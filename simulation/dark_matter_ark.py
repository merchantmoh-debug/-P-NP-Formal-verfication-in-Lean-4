"""
ARK SIMULATION MODULE: COSMIC PHASE TRANSITIONS
-----------------------------------------------
This module implements the ARK (Ascended Reasoning Kernel) simulation logic for
cosmic structures, calculating the isomorphic relationship between matter density,
topological stability (spectral gap), and computational complexity classes.

Authorized by: Mohamad Al-Zawahreh
Identity: ARK ASCENDANCE v64.0
Optimization: BOLT (Speed + Structure) | PALETTE (Visual Fidelity)
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Union, List, Optional
import time
import sys

# PALETTE: Visual Telemetry System
class Colors:
    USE_COLORS = sys.stdout.isatty()

    HEADER = '\033[95m' if USE_COLORS else ''
    BLUE = '\033[94m' if USE_COLORS else ''
    CYAN = '\033[96m' if USE_COLORS else ''
    GREEN = '\033[92m' if USE_COLORS else ''
    YELLOW = '\033[93m' if USE_COLORS else ''
    RED = '\033[91m' if USE_COLORS else ''
    ENDC = '\033[0m' if USE_COLORS else ''
    BOLD = '\033[1m' if USE_COLORS else ''

class CosmicSimulator:
    """
    A high-fidelity simulator for cosmic structure phase transitions.

    Encapsulates the physics constants and calculation logic for determining
    whether a galaxy resides in a 'Frozen' (Gas/Dark) or 'Collapsed' (Star) phase,
    which maps isomorphically to the P vs NP computational boundary.
    """

    # Universal Constants (ARK Physics)
    SOLAR_MASS_KG: float = 1.989e30
    KPC_METERS: float = 3.086e19

    # Simulation Constants
    G_APPROX: float = 4.3e-6
    CRITICAL_DENSITY_FACTOR: float = 1.0e7
    ARK_THRESHOLD: float = 0.85

    @staticmethod
    def calculate_spectral_gap(mass_solar: Union[float, np.ndarray], radius_kpc: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        """
        Calculates the ARK Scalar (Spectral Gap) for a given cosmic structure.

        BOLT OPTIMIZATION: Fully vectorized for O(1) array processing.
        """
        vol_kpc = (4.0 / 3.0) * np.pi * (radius_kpc ** 3)
        density = mass_solar / vol_kpc
        ark_scalar = np.exp(-1.0 * (density / CosmicSimulator.CRITICAL_DENSITY_FACTOR))
        return ark_scalar

    @staticmethod
    def calculate_escape_velocity(mass_solar: Union[float, np.ndarray], radius_kpc: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        """
        Calculates the Newtonian escape velocity.
        """
        return np.sqrt(2 * CosmicSimulator.G_APPROX * mass_solar / radius_kpc)

    @classmethod
    def simulate_galaxy(cls, name: str, mass: float, velocity_dispersion: float, radius: float, is_dark_matter: bool) -> float:
        """
        Runs a full simulation on a target galaxy and logs telemetry.
        DEPRECATED: Use simulate_batch for high-performance ARK operations.
        """
        return cls.simulate_batch([name], np.array([mass]), np.array([radius]))[0]

    @classmethod
    def simulate_batch(cls, names: List[str], masses: np.ndarray, radii: np.ndarray) -> np.ndarray:
        """
        BOLT OPTIMIZATION: Batch processing for cosmic structures.
        Processes N galaxies in a single vectorized pass (War Speed Execution).
        """
        # Vectorized Physics Checks
        # BOLT: Removed unused escape_vels calculation to save FLOPs
        gaps = cls.calculate_spectral_gap(masses, radii)

        return gaps

def print_progress_bar(iteration, total, prefix='', suffix='', decimals=1, length=50, fill='█'):
    """
    PALETTE ENHANCEMENT: ASCII Progress Bar
    """
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filled_length = int(length * iteration // total)
    bar = fill * filled_length + '-' * (length - filled_length)
    sys.stdout.write(f'\r{Colors.CYAN}{prefix} |{bar}| {percent}% {suffix}{Colors.ENDC}')
    sys.stdout.flush()
    if iteration == total:
        print()

def main():
    """
    Main execution entry point.
    Runs simulations and generates Palette visualization.
    """
    print(f"{Colors.BOLD}ARK ASCENDANCE v64.0 - SIMULATION PROTOCOL INITIALIZED{Colors.ENDC}")
    print(f"Threshold: {CosmicSimulator.ARK_THRESHOLD}")

    # Simulation Data Setup
    # 1: Milky Way (Standard Spiral)
    # 2: J0613+52 (Dark Matter Galaxy)
    # 3+: Synthetic Data for Bolt Verification

    names = ["Milky Way", "J0613+52"]
    masses = np.array([1e12, 2.0e9])
    radii = np.array([30.0, 15.0])

    # BOLT: Add synthetic data to demonstrate batch performance
    synthetic_count = 100
    names.extend([f"Synth-{i}" for i in range(synthetic_count)])
    masses = np.concatenate([masses, np.random.uniform(1e8, 1e13, synthetic_count)])
    radii = np.concatenate([radii, np.random.uniform(5, 50, synthetic_count)])

    print(f"\n{Colors.HEADER}--- EXECUTING BATCH SIMULATION ({len(names)} Objects) ---{Colors.ENDC}")

    start_time = time.time()

    # BOLT: Removed artificial sleep for War Speed Execution
    # PALETTE: Progress bar is now just a state indicator since calc is instant
    print_progress_bar(0, len(names), prefix='Scanning Sector:', suffix='Initializing', length=40)

    # BOLT: The actual heavy lifting (Instantaneous via NumPy)
    gaps = CosmicSimulator.simulate_batch(names, masses, radii)

    print_progress_bar(len(names), len(names), prefix='Scanning Sector:', suffix='Complete', length=40)

    execution_time = time.time() - start_time
    print(f"\n{Colors.GREEN}✓ Batch Processing Complete in {execution_time:.6f}s{Colors.ENDC}")

    # PALETTE: Formatted Telemetry Table (Top Results)
    print(f"\n{Colors.HEADER}{'OBJECT NAME':<20} | {'MASS (Sol)':<12} | {'RADIUS (kpc)':<12} | {'GAP':<10} | {'STATUS'}{Colors.ENDC}")
    print("-" * 80)

    for i in range(min(5, len(names))): # Show first 5
        status = f"{Colors.CYAN}FROZEN{Colors.ENDC}" if gaps[i] > CosmicSimulator.ARK_THRESHOLD else f"{Colors.YELLOW}COLLAPSED{Colors.ENDC}"
        print(f"{names[i]:<20} | {masses[i]:.2e}     | {radii[i]:<12.1f} | {gaps[i]:.5f}    | {status}")

    # PALETTE: Glossary Section
    print(f"\n{Colors.BOLD}--- ARK PHYSICS GLOSSARY ---{Colors.ENDC}")
    print(f"{Colors.CYAN}FROZEN:{Colors.ENDC}    Stable state (Dark Matter/Gas). High Spectral Gap. Cannot collapse.")
    print(f"{Colors.YELLOW}COLLAPSED:{Colors.ENDC} Unstable state (Stars/Black Holes). Low Spectral Gap. Gravitational collapse active.")

    # PALETTE: Generate Visualization
    print(f"\n{Colors.HEADER}--- GENERATING VISUALIZATION ---{Colors.ENDC}")

    try:
        # Plot only the main candidates + a few synthetic
        plot_indices = [0, 1] + list(range(2, 12)) # First 2 + next 10
        plot_names = [names[i] for i in plot_indices]
        plot_gaps = [gaps[i] for i in plot_indices]

        colors = ['blue' if n == "Milky Way" else 'black' if n == "J0613+52" else 'gray' for n in plot_names]

        y_pos = np.arange(len(plot_names))

        plt.figure(figsize=(12, 6))
        bars = plt.bar(y_pos, plot_gaps, align='center', alpha=0.7, color=colors)
        plt.xticks(y_pos, plot_names, rotation=45, ha='right')
        plt.ylabel('Spectral Gap Magnitude')
        plt.title('ARK Verification: Spectral Gap Analysis')
        plt.tight_layout()

        # Add Threshold Line
        plt.axhline(y=CosmicSimulator.ARK_THRESHOLD, color='r', linestyle='--', label=f'Obstruction Limit ({CosmicSimulator.ARK_THRESHOLD})')

        plt.legend()
        plt.savefig('ark_verification_plot.png')
        print(f"{Colors.GREEN}✓ Plot saved to 'ark_verification_plot.png'{Colors.ENDC}")

    except Exception as e:
        print(f"{Colors.RED}❌ Visualization Failed: {e}{Colors.ENDC}")

if __name__ == "__main__":
    main()
