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
from dataclasses import dataclass
from typing import List, Tuple

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
    UNDERLINE = '\033[4m'

@dataclass
class Galaxy:
    name: str
    mass_solar: float
    radius_kpc: float
    velocity_dispersion: float
    is_dark_matter: bool

class CosmicSimulator:
    """
    A high-fidelity simulator for cosmic structure phase transitions.
    """

    # Universal Constants (ARK Physics)
    SOLAR_MASS_KG: float = 1.989e30
    KPC_METERS: float = 3.086e19

    # Simulation Constants
    G_APPROX: float = 4.3e-6
    CRITICAL_DENSITY_FACTOR: float = 1.0e7
    ARK_THRESHOLD: float = 0.85

    @staticmethod
    def calculate_spectral_gap(mass_solar: np.ndarray, radius_kpc: np.ndarray) -> np.ndarray:
        """
        Calculates the ARK Scalar (Spectral Gap) for cosmic structures.
        BOLT OPTIMIZATION: Vectorized O(1) array processing.
        """
        vol_kpc = (4.0 / 3.0) * np.pi * (radius_kpc ** 3)
        density = mass_solar / vol_kpc
        # Avoid division by zero if radius is 0 (theoretical check)
        density = np.nan_to_num(density)
        ark_scalar = np.exp(-1.0 * (density / CosmicSimulator.CRITICAL_DENSITY_FACTOR))
        return ark_scalar

    @staticmethod
    def calculate_escape_velocity(mass_solar: np.ndarray, radius_kpc: np.ndarray) -> np.ndarray:
        """
        Calculates Newtonian escape velocity.
        """
        return np.sqrt(2 * CosmicSimulator.G_APPROX * mass_solar / radius_kpc)

    @classmethod
    def run_batch_simulation(cls, galaxies: List[Galaxy]):
        """
        BOLT: Process all galaxies in a single vectorized pass.
        PALETTE: Generate Phase Diagram and Rich Terminal Output.
        """
        print(f"{Colors.HEADER}{Colors.BOLD}=== ARK ASCENDANCE v64.0: COSMIC BATCH SIMULATION ==={Colors.ENDC}\n")

        # 1. Vectorize Data
        names = [g.name for g in galaxies]
        masses = np.array([g.mass_solar for g in galaxies])
        radii = np.array([g.radius_kpc for g in galaxies])
        velocities = np.array([g.velocity_dispersion for g in galaxies])

        # 2. Compute Physics (Vectorized)
        gaps = cls.calculate_spectral_gap(masses, radii)
        escape_vels = cls.calculate_escape_velocity(masses, radii)

        # 3. Report Telemetry
        print(f"{Colors.UNDERLINE}{'GALAXY NAME':<20} | {'MASS (M☉)':<10} | {'GAP (Ψ)':<8} | {'NEWTONIAN':<12} | {'ARK STATUS'}{Colors.ENDC}")

        for i, name in enumerate(names):
            gap = gaps[i]
            esc_vel = escape_vels[i]
            vel = velocities[i]

            # Newtonian Check
            is_stable_newton = vel <= esc_vel
            newton_status = f"{Colors.GREEN}STABLE{Colors.ENDC}" if is_stable_newton else f"{Colors.RED}UNSTABLE{Colors.ENDC}"

            # ARK Check
            is_frozen = gap > cls.ARK_THRESHOLD
            status_color = Colors.CYAN if is_frozen else Colors.YELLOW
            status_text = "FROZEN (Lock)" if is_frozen else "COLLAPSED (Star)"

            print(f"{Colors.BOLD}{name:<20}{Colors.ENDC} | {masses[i]:.1e}  | {status_color}{gap:.5f}{Colors.ENDC}  | {newton_status:<20} | {status_color}{status_text}{Colors.ENDC}")

        # 4. Generate Visualization
        cls.plot_phase_diagram(galaxies, masses, radii, gaps)

    @classmethod
    def plot_phase_diagram(cls, galaxies: List[Galaxy], masses: np.ndarray, radii: np.ndarray, gaps: np.ndarray):
        """
        PALETTE: Generates a Phase Diagram showing the topological landscape.
        """
        print(f"\n{Colors.HEADER}--- GENERATING PHASE DIAGRAM ---{Colors.ENDC}")

        try:
            plt.figure(figsize=(12, 8))
            ax = plt.gca()
            ax.set_facecolor('#1a1a2e') # Cosmic Dark Blue

            # Create a meshgrid for the background gradient
            r_range = np.linspace(1, max(radii) * 1.5, 200)
            m_range = np.linspace(min(masses) * 0.5, max(masses) * 1.5, 200)
            R, M = np.meshgrid(r_range, m_range)

            # Calculate Gap for the entire field
            # Re-implement logic inline for meshgrid to avoid reshaping issues if using static method strictly
            vol = (4.0 / 3.0) * np.pi * (R ** 3)
            dens = M / vol
            Z = np.exp(-1.0 * (dens / cls.CRITICAL_DENSITY_FACTOR))

            # Plot Contour (The ARK Threshold)
            contour = plt.contourf(R, M, Z, levels=50, cmap='magma', alpha=0.8)
            plt.colorbar(contour, label='ARK Spectral Gap (Ψ)')

            # Draw Threshold Line
            plt.contour(R, M, Z, levels=[cls.ARK_THRESHOLD], colors='cyan', linewidths=2, linestyles='dashed')

            # Plot Galaxies
            for i, g in enumerate(galaxies):
                color = 'cyan' if gaps[i] > cls.ARK_THRESHOLD else 'yellow'
                marker = 'D' if g.is_dark_matter else 'o'
                plt.scatter(g.radius_kpc, g.mass_solar, c=color, s=150, edgecolor='white', marker=marker, label=g.name if i < 10 else "")
                plt.text(g.radius_kpc, g.mass_solar, f"  {g.name}", color='white', fontsize=9, fontweight='bold')

            plt.xscale('log')
            plt.yscale('log')
            plt.xlabel('Radius (kpc) [Log Scale]', color='white')
            plt.ylabel('Mass (Solar Masses) [Log Scale]', color='white')
            plt.title(f'ARK Cosmic Phase Diagram\nHomological Obstruction at Ψ > {cls.ARK_THRESHOLD}', color='white')
            plt.grid(True, which="both", ls="-", alpha=0.2, color='white')

            # Custom Legend
            from matplotlib.lines import Line2D
            custom_lines = [Line2D([0], [0], color='cyan', lw=2, linestyle='--'),
                            Line2D([0], [0], marker='o', color='w', markerfacecolor='yellow', markersize=10),
                            Line2D([0], [0], marker='D', color='w', markerfacecolor='cyan', markersize=10)]
            plt.legend(custom_lines, ['ARK Threshold', 'Collapsed (Star Forming)', 'Frozen (Dark Matter)'], loc='upper right')

            # Fix axes colors
            ax.tick_params(axis='x', colors='white')
            ax.tick_params(axis='y', colors='white')
            for spine in ax.spines.values():
                spine.set_edgecolor('white')

            plt.tight_layout()
            output_path = 'ark_phase_diagram.png'
            plt.savefig(output_path, dpi=300, facecolor='#16213e')
            print(f"{Colors.GREEN}✓ Phase Diagram saved to '{output_path}'{Colors.ENDC}")

        except Exception as e:
            print(f"{Colors.RED}❌ Visualization Failed: {e}{Colors.ENDC}")

def main():
    # DATA INJECTION
    dataset = [
        Galaxy("Milky Way", 1e12, 30.0, 220, False),
        Galaxy("Andromeda", 1.5e12, 32.0, 260, False),
        Galaxy("Triangulum", 5e10, 18.0, 100, False),
        Galaxy("LMC", 1e10, 5.0, 80, False),
        Galaxy("J0613+52 (Cloud-9)", 2.0e9, 15.0, 200, True), # The Witness
        Galaxy("Dragonfly 44", 1e9, 10.0, 30, True),
        Galaxy("Segue 1", 6e5, 0.03, 10, True) # Ultra-faint dwarf
    ]

    CosmicSimulator.run_batch_simulation(dataset)

if __name__ == "__main__":
    main()
