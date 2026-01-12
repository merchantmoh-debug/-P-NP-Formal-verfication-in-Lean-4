"""
ARK SIMULATION MODULE: COSMIC PHASE TRANSITIONS
-----------------------------------------------
This module implements the ARK (Ascended Reasoning Kernel) simulation logic for
cosmic structures, calculating the isomorphic relationship between matter density,
topological stability (spectral gap), and computational complexity classes.

Authorized by: Mohamad Al-Zawahreh
Identity: ARK ASCENDANCE v64.0
Optimization: BOLT (Speed + Structure)
"""

import numpy as np
from typing import Tuple, List, Optional

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

    # Simulation Constants (Dimensionless or specific unit system)
    # G_approx: Gravitational constant in simulation units (km^2 * kpc / (M_sol * s^2) approx)
    G_APPROX: float = 4.3e-6

    # Critical Density Factor for Spectral Gap calculation
    CRITICAL_DENSITY_FACTOR: float = 1.0e7

    # Phase Transition Threshold (The Event Horizon of Complexity)
    ARK_THRESHOLD: float = 0.85

    @staticmethod
    def calculate_spectral_gap(mass_solar: float, radius_kpc: float) -> float:
        """
        Calculates the ARK Scalar (Spectral Gap) for a given cosmic structure.

        The Spectral Gap represents the energy cost to excite the system from its ground state.
        In the ARK isomorphism:
        - Large Gap (> 0.85) -> Frozen/Stable -> Polynomial Time (P)
        - Small Gap (< 0.85) -> Collapsed/Chaotic -> Non-Polynomial Difficulty (NP)

        Args:
            mass_solar (float): Mass in Solar Masses.
            radius_kpc (float): Radius in Kiloparsecs.

        Returns:
            float: The dimensionless ARK Scalar (0 < s <= 1).
        """
        # Volume in Kpc^3
        # Optimization: Pre-compute 4/3 * pi if called frequently, but here clarity reigns.
        vol_kpc: float = (4.0 / 3.0) * np.pi * (radius_kpc ** 3)

        # Density in Solar Masses / Kpc^3
        density: float = mass_solar / vol_kpc

        # The Isomorphic Mapping Function: exp(-density / critical)
        ark_scalar: float = np.exp(-1.0 * (density / CosmicSimulator.CRITICAL_DENSITY_FACTOR))

        return ark_scalar

    @staticmethod
    def calculate_escape_velocity(mass_solar: float, radius_kpc: float) -> float:
        """
        Calculates the Newtonian escape velocity.

        Args:
            mass_solar (float): Mass in Solar Masses.
            radius_kpc (float): Radius in Kiloparsecs.

        Returns:
            float: Escape velocity in km/s.
        """
        return np.sqrt(2 * CosmicSimulator.G_APPROX * mass_solar / radius_kpc)

    @classmethod
    def simulate_galaxy(cls, name: str, mass: float, velocity_dispersion: float, radius: float, is_dark_matter: bool) -> float:
        """
        Runs a full simulation on a target galaxy.

        Args:
            name (str): Name of the galaxy/structure.
            mass (float): Mass in Solar Masses.
            velocity_dispersion (float): Velocity dispersion (km/s) - tracked but not currently used in gap calc.
            radius (float): Radius in Kpc.
            is_dark_matter (bool): Flag for dark matter candidates.

        Returns:
            float: The calculated Spectral Gap.
        """
        print(f"\n--- SIMULATING OBJECT: {name} ---")
        print(f"Mass: {mass:.2e} Solar Masses")

        # Standard Physics Check
        escape_vel = cls.calculate_escape_velocity(mass, radius)
        print(f"Newtonian Escape Vel: {escape_vel:.2f} km/s")

        # ARK Check
        gap = cls.calculate_spectral_gap(mass, radius)
        print(f"ARK Spectral Gap: {gap:.5f}")

        status = ""
        if gap > cls.ARK_THRESHOLD:
            status = "FROZEN (Topological Lock)"
        else:
            status = "COLLAPSED (Star Formation)"

        print(f"PREDICTION: {status}")
        return gap

def main():
    """
    Main execution entry point.
    Runs the standard ARK test suite for Milky Way and J0613+52.
    """
    print("ARK ASCENDANCE v64.0 - SIMULATION PROTOCOL INITIALIZED")
    print(f"Threshold: {CosmicSimulator.ARK_THRESHOLD}")

    # Simulation 1: Milky Way (Standard Spiral)
    # Expected: Collapsed (Gap < 0.85)
    _ = CosmicSimulator.simulate_galaxy(
        name="Milky Way",
        mass=1e12,
        velocity_dispersion=220,
        radius=30,
        is_dark_matter=False
    )

    # Simulation 2: J0613+52 (Dark Matter Galaxy / "Cloud-9")
    # Expected: Frozen (Gap > 0.85)
    _ = CosmicSimulator.simulate_galaxy(
        name="J0613+52 (Cloud-9)",
        mass=2.0e9,
        velocity_dispersion=200,
        radius=15,
        is_dark_matter=True
    )

if __name__ == "__main__":
    main()
