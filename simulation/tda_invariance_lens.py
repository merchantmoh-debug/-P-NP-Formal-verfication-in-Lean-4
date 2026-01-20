# tda_invariance_lens.py
# ARK TDA Lens: Persistent Homology Stability Verification
# Validates that topological signatures are invariant under rotation, translation, subsampling, and noise.
# Dependencies: pip install numpy scipy ripser persim

import argparse
import json
import numpy as np
import sys
from ripser import ripser
from persim import wasserstein
from scipy.spatial.transform import Rotation as R

def load_xyz(path: str, limit: int = None) -> np.ndarray:
    """
    Accepts:
      - .npy with shape (N,3)
      - .csv or .txt with 3 columns (whitespace or comma separated)
      - .jsonl with {"x":.., "y":.., "z":..} or {"xyz": [x,y,z]}
    """
    print(f"Loading data from {path}...")
    if path.endswith(".npy"):
        X = np.load(path)
        return X[:limit] if limit else X

    pts = []
    if path.endswith(".jsonl"):
        with open(path, "r", encoding="utf-8") as f:
            for i, line in enumerate(f):
                if limit and i >= limit:
                    break
                try:
                    obj = json.loads(line)
                    if "xyz" in obj:
                        pts.append(obj["xyz"])
                    elif "x" in obj and "y" in obj and "z" in obj:
                        pts.append([obj["x"], obj["y"], obj["z"]])
                except json.JSONDecodeError:
                    continue
        return np.array(pts)

    # Fallback for CSV/TXT
    try:
        # Try loading as standard text file
        X = np.loadtxt(path, delimiter=',' if path.endswith('.csv') else None)
        if limit:
            X = X[:limit]
        if X.shape[1] < 3:
            raise ValueError("Data must have at least 3 columns (x, y, z)")
        return X[:, :3] # Take first 3 columns
    except Exception as e:
        print(f"Error loading text data: {e}")
        sys.exit(1)

def compute_ph(X: np.ndarray, maxdim: int = 1):
    """Computes persistent homology using Ripser."""
    result = ripser(X, maxdim=maxdim)
    return result['dgms']

def apply_transform(X: np.ndarray, transform_type: str, intensity: float = 1.0) -> np.ndarray:
    """Applies specific geometric or noisy transformations."""
    N = X.shape[0]
    X_new = X.copy()

    if transform_type == "rotation":
        # Random 3D rotation
        r = R.random()
        X_new = r.apply(X_new)

    elif transform_type == "translation":
        # Random translation vector scaled by intensity (relative to data scale)
        shift = np.random.randn(3) * intensity
        X_new = X_new + shift

    elif transform_type == "subsample":
        # Keep (1 - intensity) fraction of points, where intensity is drop rate
        if intensity >= 1.0 or intensity < 0: intensity = 0.5
        n_keep = int(N * (1 - intensity))
        indices = np.random.choice(N, n_keep, replace=False)
        X_new = X_new[indices]

    elif transform_type == "noise":
        # Gaussian noise
        noise = np.random.normal(0, intensity, X_new.shape)
        X_new = X_new + noise

    return X_new

def main():
    parser = argparse.ArgumentParser(description="ARK TDA Invariance Lens")
    parser.add_argument("--data", type=str, required=True, help="Path to point cloud file")
    parser.add_argument("--limit", type=int, default=None, help="Limit number of points")
    parser.add_argument("--maxdim", type=int, default=1, help="Max homology dimension")
    parser.add_argument("--hom", type=int, default=1, help="Homology dimension to test stability on")
    parser.add_argument("--trials", type=int, default=5, help="Number of trials per transform")
    args = parser.parse_args()

    # Load Data
    X = load_xyz(args.data, args.limit)
    print(f"Data loaded: {X.shape[0]} points")

    # Base PH
    print(f"Computing base Persistent Homology (Dim {args.hom})...")
    dgms_base = compute_ph(X, maxdim=args.maxdim)
    dgm_base = dgms_base[args.hom]

    # Define Transforms
    # Intensity scales: translation/noise relative to data bounds?
    # For simplicity, we use fixed small values or relative to std dev.
    scale = np.std(X) if X.shape[0] > 0 else 1.0
    transforms = {
        "rotation": 1.0, # Intensity doesn't matter for pure rotation
        "translation": scale * 0.1, # Shift by 10% of scale
        "noise": scale * 0.01, # 1% noise
        "subsample": 0.2 # Drop 20%
    }

    print("\n--- INVARIANCE TEST RESULTS ---")
    print(f"{'TRANSFORM':<15} | {'WASSERSTEIN DIST (Mean)':<25} | {'STATUS'}")
    print("-" * 55)

    results = {}

    for name, param in transforms.items():
        dists = []
        for _ in range(args.trials):
            X_trans = apply_transform(X, name, intensity=param)

            # Compute PH of transformed
            dgms_trans = compute_ph(X_trans, maxdim=args.maxdim)
            dgm_trans = dgms_trans[args.hom]

            # Compute Wasserstein distance
            # If diagram is empty, distance is infinity technically, or 0 if both empty
            if len(dgm_base) == 0 and len(dgm_trans) == 0:
                d = 0.0
            elif len(dgm_base) == 0 or len(dgm_trans) == 0:
                 # Penalty for total collapse or spontaneous generation
                d = 999.0
            else:
                d = wasserstein(dgm_base, dgm_trans)
            dists.append(d)

        mean_dist = np.mean(dists)
        results[name] = mean_dist

        # Determine Status
        # "Invariant" if distance is small relative to feature scale.
        # This is a heuristic.
        status = "STABLE" if mean_dist < (scale * 0.5) else "UNSTABLE"
        print(f"{name:<15} | {mean_dist:.5f}                   | {status}")

    print("-" * 55)
    print("Interpretation:")
    print("Low Wasserstein distance implies the topological signature persists across transformations.")
    print("Stability under rotation/translation confirms geometric invariance.")
    print("Stability under noise/subsampling confirms robustness.")

if __name__ == "__main__":
    main()
