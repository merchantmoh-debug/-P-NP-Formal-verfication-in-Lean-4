import numpy as np

def calculate_spectral_gap(mass_solar, radius_kpc):
    vol_kpc = (4/3) * np.pi * (radius_kpc ** 3)
    density = mass_solar / vol_kpc
    critical_density_factor = 1e7
    ark_scalar = np.exp(-1.0 * (density / critical_density_factor))
    return ark_scalar

def simulate_galaxy(name, mass, velocity, radius, is_dark_matter_candidate):
    print(f"\n--- SIMULATING OBJECT: {name} ---")
    print(f"Mass: {mass:.2e} Solar Masses")
    # Standard Physics Check
    G_approx = 4.3e-6
    escape_vel = np.sqrt(2 * G_approx * mass / radius)
    print(f"Newtonian Escape Vel: {escape_vel:.2f} km/s")

    # ARK Check
    gap = calculate_spectral_gap(mass, radius)
    print(f"ARK Spectral Gap: {gap:.5f}")

    ARK_THRESHOLD = 0.85
    status = ""
    if gap > ARK_THRESHOLD:
        status = "FROZEN (Topological Lock)"
    else:
        status = "COLLAPSED (Star Formation)"
    print(f"PREDICTION: {status}")
    return gap

gap_mw = simulate_galaxy("Milky Way", 1e12, 220, 30, False)
gap_ghost = simulate_galaxy("J0613+52 (Cloud-9)", 2.0e9, 200, 15, True)
