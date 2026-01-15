"""
ARK SIMULATION MODULE: COSMIC PHASE TRANSITIONS
-----------------------------------------------
This module implements the ARK (Ascended Reasoning Kernel) simulation logic for
cosmic structures, calculating the isomorphic relationship between matter density,
topological stability (spectral gap), and computational complexity classes.

Authorized by: Mohamad Al-Zawahreh
Identity: ARK ASCENDANCE v64.0
Optimization: BOLT (Speed + Structure)
Visualization: PALETTE (Clarity + Aesthetics)
"""

import numpy as np
import matplotlib.pyplot as plt
import argparse
import sys
from typing import Tuple, List, Optional, Union

# ANSI Colors for Palette Enhancement
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

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

    # Pre-computed constants
    VOL_FACTOR: float = (4.0 / 3.0) * np.pi

    @staticmethod
    def calculate_spectral_gap(mass_solar: Union[float, np.ndarray], radius_kpc: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        """
        Calculates the ARK Scalar (Spectral Gap).
        Vectorized for BOLT performance optimization.
        """
        vol_kpc = CosmicSimulator.VOL_FACTOR * (radius_kpc ** 3)
        density = mass_solar / vol_kpc
        ark_scalar = np.exp(-1.0 * (density / CosmicSimulator.CRITICAL_DENSITY_FACTOR))
        return ark_scalar

    @staticmethod
    def calculate_escape_velocity(mass_solar: Union[float, np.ndarray], radius_kpc: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        """
        Calculates Newtonian escape velocity.
        Vectorized.
        """
        return np.sqrt(2 * CosmicSimulator.G_APPROX * mass_solar / radius_kpc)

    @classmethod
    def simulate_galaxy(cls, name: str, mass: float, velocity_dispersion: float, radius: float, is_dark_matter: bool) -> float:
        """
        Runs a full simulation on a single target galaxy with rich output.
        """
        print(f"\n{Colors.HEADER}--- SIMULATING OBJECT: {name} ---{Colors.ENDC}")
        print(f"Mass: {mass:.2e} Solar Masses")
        print(f"Spin: {velocity_dispersion} km/s")

        # Standard Physics Check
        escape_vel = cls.calculate_escape_velocity(mass, radius)
        print(f"Newtonian Escape Vel: {escape_vel:.2f} km/s")

        # ARK Check
        gap = cls.calculate_spectral_gap(mass, radius)

        # Formatting
        gap_str = f"{gap:.5f}"
        if gap > cls.ARK_THRESHOLD:
            gap_str = f"{Colors.GREEN}{gap_str}{Colors.ENDC}"
        else:
            gap_str = f"{Colors.FAIL}{gap_str}{Colors.ENDC}"

        print(f"ARK Spectral Gap:   {gap_str}")

        status = ""
        if gap > cls.ARK_THRESHOLD:
            status = f"{Colors.GREEN}FROZEN (Topological Lock){Colors.ENDC}"
            detail = "Star Count: 0 (Dark Galaxy)"
        else:
            status = f"{Colors.FAIL}COLLAPSED (Star Formation){Colors.ENDC}"
            detail = "Star Count: BILLIONS"

        print(f"PREDICTION:         {status}")
        print(f"Detail:             {detail}")
        return gap

    @classmethod
    def generate_phase_diagram(cls, output_file: str = "simulation_result.png"):
        """
        Generates a phase diagram using vectorized operations (BOLT)
        and high-quality plotting (PALETTE).
        """
        print(f"\n{Colors.CYAN}Generating ARK Phase Diagram...{Colors.ENDC}")

        # Generate random galaxy data
        num_samples = 5000
        masses = np.logspace(8, 13, num_samples) # 10^8 to 10^13 Solar Masses
        radii = np.random.uniform(5, 50, num_samples)

        # Vectorized calculation
        gaps = cls.calculate_spectral_gap(masses, radii)

        # Plotting
        plt.figure(figsize=(10, 6))

        # Color map based on gap
        sc = plt.scatter(masses, gaps, c=gaps, cmap='viridis', alpha=0.6, s=10)
        plt.colorbar(sc, label='Spectral Gap (ARK Scalar)')

        # Threshold line
        plt.axhline(y=cls.ARK_THRESHOLD, color='r', linestyle='--', linewidth=2, label=f'Event Horizon ({cls.ARK_THRESHOLD})')

        # Annotate Key Objects
        # Milky Way
        mw_mass = 1e12
        mw_rad = 30
        mw_gap = cls.calculate_spectral_gap(mw_mass, mw_rad)
        plt.plot(mw_mass, mw_gap, 'r*', markersize=15, markeredgecolor='black', label='Milky Way')

        # J0613+52
        j_mass = 2.0e9
        j_rad = 15
        j_gap = cls.calculate_spectral_gap(j_mass, j_rad)
        plt.plot(j_mass, j_gap, 'w^', markersize=15, markeredgecolor='black', label='J0613+52 (Dark)')

        plt.xscale('log')
        plt.xlabel('Mass (Solar Masses)')
        plt.ylabel('Spectral Gap (0=Collapsed, 1=Frozen)')
        plt.title('ARK Phase Diagram: Isomorphic Complexity Landscape')
        plt.legend()
        plt.grid(True, alpha=0.3)

        print(f"Saving visualization to {output_file}...")
        plt.savefig(output_file, dpi=300)
        print(f"{Colors.GREEN}Visualization Saved.{Colors.ENDC}")

def main():
    parser = argparse.ArgumentParser(description="ARK Cosmic Simulator v64.0")
    parser.add_argument("--batch", action="store_true", help="Run batch simulation and generate plot")
    parser.add_argument("--no-color", action="store_true", help="Disable colored output")
    args = parser.parse_args()

    if args.no_color:
        # Disable colors
        for attr in dir(Colors):
            if not attr.startswith("__"):
                setattr(Colors, attr, "")

    print(f"{Colors.BOLD}{Colors.CYAN}ARK ASCENDANCE v64.0 - SIMULATION PROTOCOL INITIALIZED{Colors.ENDC}")
    print(f"Threshold: {CosmicSimulator.ARK_THRESHOLD}")

    # Standard Verification Suite
    gap_mw = CosmicSimulator.simulate_galaxy(
        name="Milky Way",
        mass=1e12,
        velocity_dispersion=220,
        radius=30,
        is_dark_matter=False
    )

    gap_cloud9 = CosmicSimulator.simulate_galaxy(
        name="J0613+52 (Cloud-9)",
        mass=2.0e9,
        velocity_dispersion=200,
        radius=15,
        is_dark_matter=True
    )

    if args.batch:
        CosmicSimulator.generate_phase_diagram()
    else:
        print(f"\n{Colors.WARNING}Tip: Run with --batch to generate phase diagram visualization.{Colors.ENDC}")

if __name__ == "__main__":
    main()
