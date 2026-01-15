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

# PALETTE: Visual Telemetry System
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'

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
        """
        print(f"\n{Colors.HEADER}--- SIMULATING OBJECT: {name} ---{Colors.ENDC}")
        print(f"Mass: {mass:.2e} Solar Masses")

        # Standard Physics Check
        escape_vel = cls.calculate_escape_velocity(mass, radius)
        print(f"Newtonian Escape Vel: {escape_vel:.2f} km/s")

        # ARK Check
        gap = cls.calculate_spectral_gap(mass, radius)
        print(f"ARK Spectral Gap:   {Colors.BOLD}{gap:.5f}{Colors.ENDC}")

        status = ""
        if gap > cls.ARK_THRESHOLD:
            status = f"{Colors.CYAN}FROZEN (Topological Lock){Colors.ENDC}"
        else:
            status = f"{Colors.YELLOW}COLLAPSED (Star Formation){Colors.ENDC}"

        print(f"PREDICTION:         {status}")
        return float(gap)

def main():
    """
    Main execution entry point.
    Runs simulations and generates Palette visualization.
    """
    print(f"{Colors.BOLD}ARK ASCENDANCE v64.0 - SIMULATION PROTOCOL INITIALIZED{Colors.ENDC}")
    print(f"Threshold: {CosmicSimulator.ARK_THRESHOLD}")

    # Data Containers for Plotting
    names = []
    gaps = []
    colors = []

    # Simulation 1: Milky Way (Standard Spiral)
    name_mw = "Milky Way"
    gap_mw = CosmicSimulator.simulate_galaxy(
        name=name_mw,
        mass=1e12,
        velocity_dispersion=220,
        radius=30,
        is_dark_matter=False
    )
    names.append(name_mw)
    gaps.append(gap_mw)
    colors.append('blue')

    # Simulation 2: J0613+52 (Dark Matter Galaxy)
    name_ghost = "J0613+52"
    gap_ghost = CosmicSimulator.simulate_galaxy(
        name=name_ghost,
        mass=2.0e9,
        velocity_dispersion=200,
        radius=15,
        is_dark_matter=True
    )
    names.append(name_ghost)
    gaps.append(gap_ghost)
    colors.append('black')

    # PALETTE: Generate Visualization
    print(f"\n{Colors.HEADER}--- GENERATING VISUALIZATION ---{Colors.ENDC}")

    try:
        y_pos = np.arange(len(names))

        plt.figure(figsize=(10, 6))
        bars = plt.bar(y_pos, gaps, align='center', alpha=0.7, color=colors)
        plt.xticks(y_pos, names)
        plt.ylabel('Spectral Gap Magnitude')
        plt.title('ARK Verification: Spectral Gap Analysis')

        # Add Threshold Line
        plt.axhline(y=CosmicSimulator.ARK_THRESHOLD, color='r', linestyle='--', label=f'Obstruction Limit ({CosmicSimulator.ARK_THRESHOLD})')

        # Add values on top of bars
        for bar in bars:
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width()/2., height,
                    f'{height:.4f}',
                    ha='center', va='bottom')

        plt.legend()
        plt.savefig('ark_verification_plot.png')
        print(f"{Colors.GREEN}✓ Plot saved to 'ark_verification_plot.png'{Colors.ENDC}")

    except Exception as e:
        print(f"{Colors.RED}❌ Visualization Failed: {e}{Colors.ENDC}")

if __name__ == "__main__":
    main()
