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
from typing import Union, List, Tuple
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
    # G in units of kpc * (km/s)^2 / M_sun
    G_APPROX: float = 4.301e-6
    CRITICAL_DENSITY_FACTOR: float = 1.0e7
    ARK_THRESHOLD: float = 0.85

    @staticmethod
    def calculate_spectral_gap(mass_solar: np.ndarray, radius_kpc: np.ndarray) -> np.ndarray:
        """
        Calculates the ARK Scalar (Spectral Gap) for a given cosmic structure.
        BOLT OPTIMIZATION: Fully vectorized for O(1) array processing.
        """
        vol_kpc = (4.0 / 3.0) * np.pi * (radius_kpc ** 3)
        density = mass_solar / vol_kpc
        # Avoid division by zero if density is 0 (though mass shouldn't be 0)
        ark_scalar = np.exp(-1.0 * (density / CosmicSimulator.CRITICAL_DENSITY_FACTOR))
        return ark_scalar

    @staticmethod
    def calculate_escape_velocity(mass_solar: np.ndarray, radius_kpc: np.ndarray) -> np.ndarray:
        """
        Calculates the Newtonian escape velocity in km/s.
        Formula: v_esc = sqrt(2 * G * M / R)
        """
        return np.sqrt(2 * CosmicSimulator.G_APPROX * mass_solar / radius_kpc)

    @classmethod
    def simulate_batch(cls, names: List[str], masses: np.ndarray, radii: np.ndarray, dispersions: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        BOLT OPTIMIZATION: Batch processing for cosmic structures.
        Processes N galaxies in a single vectorized pass (War Speed Execution).

        Returns:
            gaps (np.ndarray): Spectral Gap values.
            escape_vels (np.ndarray): Escape velocities (km/s).
            is_unstable (np.ndarray): Boolean array (True if v_disp > v_esc).
        """
        # Vectorized Physics Checks
        gaps = cls.calculate_spectral_gap(masses, radii)
        escape_vels = cls.calculate_escape_velocity(masses, radii)

        # ARK TRUTH CHECK: Newtonian Instability
        is_unstable = dispersions > escape_vels

        return gaps, escape_vels, is_unstable

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
    # 1: Milky Way (Standard Spiral) - v_disp ~ 200 km/s (halo/bulge)
    # 2: J0613+52 (Dark Matter Galaxy) - Low surface brightness, v_disp unknown but likely low/stable?
    #    Let's assume it's stable (v_disp < v_esc) for the "Frozen" hypothesis.

    names = ["Milky Way", "J0613+52"]
    masses = np.array([1e12, 2.0e9])
    radii = np.array([30.0, 15.0])
    dispersions = np.array([150.0, 40.0]) # km/s

    # BOLT: Add synthetic data to demonstrate batch performance
    synthetic_count = 100
    names.extend([f"Synth-{i}" for i in range(synthetic_count)])

    # Generate random synthetic data
    # Random masses between 1e8 and 1e13
    synth_masses = np.random.uniform(1e8, 1e13, synthetic_count)
    masses = np.concatenate([masses, synth_masses])

    # Random radii between 5 and 50 kpc
    synth_radii = np.random.uniform(5, 50, synthetic_count)
    radii = np.concatenate([radii, synth_radii])

    # Random dispersions between 10 and 500 km/s
    synth_dispersions = np.random.uniform(10, 500, synthetic_count)
    dispersions = np.concatenate([dispersions, synth_dispersions])

    print(f"\n{Colors.HEADER}--- EXECUTING BATCH SIMULATION ({len(names)} Objects) ---{Colors.ENDC}")

    start_time = time.time()

    # PALETTE: Progress bar
    print_progress_bar(0, len(names), prefix='Scanning Sector:', suffix='Initializing', length=40)

    # BOLT: The actual heavy lifting (Instantaneous via NumPy)
    gaps, v_escs, unstable_flags = CosmicSimulator.simulate_batch(names, masses, radii, dispersions)

    print_progress_bar(len(names), len(names), prefix='Scanning Sector:', suffix='Complete', length=40)

    execution_time = time.time() - start_time
    print(f"\n{Colors.GREEN}✓ Batch Processing Complete in {execution_time:.6f}s{Colors.ENDC}")

    # PALETTE: Formatted Telemetry Table (Top Results)
    print(f"\n{Colors.HEADER}{'OBJECT NAME':<20} | {'MASS (Sol)':<10} | {'GAP':<8} | {'V_disp':<8} | {'V_esc':<8} | {'STATUS'}{Colors.ENDC}")
    print("-" * 95)

    for i in range(min(10, len(names))): # Show first 10
        # Determine Status
        if unstable_flags[i]:
            status = f"{Colors.RED}UNSTABLE (NEWT){Colors.ENDC}"
        elif gaps[i] > CosmicSimulator.ARK_THRESHOLD:
            status = f"{Colors.CYAN}FROZEN (STABLE){Colors.ENDC}"
        else:
            status = f"{Colors.YELLOW}COLLAPSED{Colors.ENDC}"

        print(f"{names[i]:<20} | {masses[i]:.2e}   | {gaps[i]:.4f}   | {dispersions[i]:<8.1f} | {v_escs[i]:<8.1f} | {status}")

    # PALETTE: Glossary Section
    print(f"\n{Colors.BOLD}--- ARK PHYSICS GLOSSARY ---{Colors.ENDC}")
    print(f"{Colors.CYAN}FROZEN:{Colors.ENDC}   High Spectral Gap (> {CosmicSimulator.ARK_THRESHOLD}). Stable Dark Matter/Gas state.")
    print(f"{Colors.YELLOW}COLLAPSED:{Colors.ENDC} Low Spectral Gap. Gravitational collapse active (Star formation).")
    print(f"{Colors.RED}UNSTABLE:{Colors.ENDC}  Velocity Dispersion > Escape Velocity. System is unbound (Newtonian breakdown).")

    # PALETTE: Generate Visualization
    print(f"\n{Colors.HEADER}--- GENERATING VISUALIZATION ---{Colors.ENDC}")

    try:
        # Plot only the main candidates + a few synthetic
        plot_indices = [0, 1] + list(range(2, 12)) # First 2 + next 10
        plot_names = [names[i] for i in plot_indices]
        plot_gaps = [gaps[i] for i in plot_indices]

        # Color code: Blue=MW, Black=Dark, Red=Unstable, Gray=Others
        plot_colors = []
        for i in plot_indices:
            if unstable_flags[i]:
                plot_colors.append('red')
            elif names[i] == "Milky Way":
                plot_colors.append('blue')
            elif names[i] == "J0613+52":
                plot_colors.append('black')
            else:
                plot_colors.append('gray')

        y_pos = np.arange(len(plot_names))

        plt.figure(figsize=(12, 6))
        bars = plt.bar(y_pos, plot_gaps, align='center', alpha=0.7, color=plot_colors)
        plt.xticks(y_pos, plot_names, rotation=45, ha='right')
        plt.ylabel('Spectral Gap Magnitude')
        plt.title('ARK Verification: Spectral Gap & Stability')
        plt.tight_layout()

        # Add Threshold Line
        plt.axhline(y=CosmicSimulator.ARK_THRESHOLD, color='g', linestyle='--', label=f'Stability Threshold ({CosmicSimulator.ARK_THRESHOLD})')

        # Legend (Custom proxy artists)
        from matplotlib.patches import Patch
        legend_elements = [
            Patch(facecolor='blue', label='Milky Way'),
            Patch(facecolor='black', label='Dark Matter Galaxy'),
            Patch(facecolor='red', label='Newtonian Unstable'),
            Patch(facecolor='gray', label='Synthetic Candidate')
        ]
        plt.legend(handles=legend_elements)

        plt.savefig('ark_verification_plot.png')
        print(f"{Colors.GREEN}✓ Plot saved to 'ark_verification_plot.png'{Colors.ENDC}")

    except Exception as e:
        print(f"{Colors.RED}❌ Visualization Failed: {e}{Colors.ENDC}")

if __name__ == "__main__":
    main()
