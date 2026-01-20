# generate_test_cloud.py
# Generates a synthetic point cloud for TDA verification.
# Shape: Torus (has non-trivial H1)

import numpy as np
import argparse

def generate_torus(n_points=2000, R=1.0, r=0.3, noise_level=0.01):
    """
    Generates points on a torus with major radius R and minor radius r.
    """
    theta = np.random.uniform(0, 2*np.pi, n_points)
    phi = np.random.uniform(0, 2*np.pi, n_points)

    x = (R + r * np.cos(phi)) * np.cos(theta)
    y = (R + r * np.cos(phi)) * np.sin(theta)
    z = r * np.sin(phi)

    points = np.stack([x, y, z], axis=1)

    # Add noise
    noise = np.random.normal(0, noise_level, points.shape)
    points += noise

    return points

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=str, default="test_cloud.npy", help="Output filename")
    parser.add_argument("--points", type=int, default=2000, help="Number of points")
    args = parser.parse_args()

    print(f"Generating torus point cloud with {args.points} points...")
    data = generate_torus(n_points=args.points)

    np.save(args.out, data)
    print(f"Saved to {args.out}")

if __name__ == "__main__":
    main()
