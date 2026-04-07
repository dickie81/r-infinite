"""
Sensitivity analysis: which cascade parameter set best fits DESI DR2?
Tests multiple combinations of H0 and Omega_m.
"""

import numpy as np
from scipy import integrate

c_km_s = 299792.458
pi = np.pi

# DESI DR2 data
desi_data = [
    (0.295, "DV", 7.930, 0.150),
    (0.510, "DM", 13.650, 0.200),
    (0.510, "DH", 20.890, 0.490),
    (0.706, "DM", 16.970, 0.240),
    (0.706, "DH", 20.270, 0.470),
    (0.934, "DM", 21.790, 0.240),
    (0.934, "DH", 17.730, 0.300),
    (1.321, "DM", 27.680, 0.500),
    (1.321, "DH", 13.850, 0.340),
    (1.484, "DM", 30.420, 0.660),
    (1.484, "DH", 13.240, 0.450),
    (2.330, "DM", 39.200, 0.560),
    (2.330, "DH", 8.540, 0.140),
]

N_eff = 3.044
factor_nu = 1.0 + (7.0 / 8.0) * (4.0 / 11.0) ** (4.0 / 3.0) * N_eff


def compute_chi2(H0, Omega_m, Omega_b, Omega_r, Omega_Lambda):
    """Compute chi2 against DESI DR2 for a given parameter set."""
    h = H0 / 100.0
    omega_m = Omega_m * h**2
    omega_b = Omega_b * h**2
    omega_r = Omega_r * h**2
    Omega_gamma = Omega_r / factor_nu
    omega_gamma = Omega_gamma * h**2

    def H(z):
        return H0 * np.sqrt(
            Omega_r * (1 + z)**4 + Omega_m * (1 + z)**3 + Omega_Lambda
        )

    def D_M(z):
        result, _ = integrate.quad(lambda zp: c_km_s / H(zp), 0, z)
        return result

    def D_H(z):
        return c_km_s / H(z)

    def D_V(z):
        dm = D_M(z)
        dh = D_H(z)
        return (z * dh * dm**2) ** (1.0 / 3.0)

    # Sound horizon (numerical)
    b1 = 0.313 * omega_m**(-0.419) * (1 + 0.607 * omega_m**0.674)
    b2 = 0.238 * omega_m**0.223
    z_drag = (1291.0 * omega_m**0.251 / (1 + 0.659 * omega_m**0.828)
              * (1 + b1 * omega_b**b2))

    R_coeff = 3.0 * omega_b / (4.0 * omega_gamma)

    def integrand(z_prime):
        R = R_coeff / (1.0 + z_prime)
        c_s = 1.0 / np.sqrt(3.0 * (1.0 + R))
        return c_s * c_km_s / H(z_prime)

    r_d, _ = integrate.quad(integrand, z_drag, np.inf)

    # Also E&H98 fitting formula
    r_d_fit = 147.60 * (omega_m / 0.1432)**(-0.255) * (omega_b / 0.02237)**(-0.127)

    # Compute chi2
    chi2 = 0.0
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            pred = D_V(z) / r_d
        elif typ == "DM":
            pred = D_M(z) / r_d
        elif typ == "DH":
            pred = D_H(z) / r_d
        chi2 += ((pred - obs) / sig) ** 2

    # Also with fitting formula r_d
    chi2_fit = 0.0
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            pred = D_V(z) / r_d_fit
        elif typ == "DM":
            pred = D_M(z) / r_d_fit
        elif typ == "DH":
            pred = D_H(z) / r_d_fit
        chi2_fit += ((pred - obs) / sig) ** 2

    # Acoustic scale
    D_M_star = D_M(1089.0)
    ell_A = pi * D_M_star / r_d
    ell_A_fit = pi * D_M_star / r_d_fit

    return {
        'r_d_num': r_d, 'r_d_fit': r_d_fit, 'z_drag': z_drag,
        'chi2_num': chi2, 'chi2_fit': chi2_fit,
        'ell_A_num': ell_A, 'ell_A_fit': ell_A_fit,
    }


# === Test parameter sets ===
print("=" * 90)
print("PARAMETER SET COMPARISON")
print("=" * 90)

sets = [
    ("Planck LCDM",
     67.4, 0.315, 0.0493, 9.15e-5, 1 - 0.315 - 9.15e-5),
    ("Old cascade (Bott Omega_m)",
     70.65, 0.31150, 1/(2*pi**2), 1/(4*pi**7), (pi-1)/pi),
    ("Updated: H0=71.05, Omega_m=1/pi",
     71.05, 1/pi, 1/(2*pi**2), 1/(4*pi**7), (pi-1)/pi),
    ("Updated H0, Bott Omega_m",
     71.05, 0.31150, 1/(2*pi**2), 1/(4*pi**7), 1 - 0.31150 - 1/(4*pi**7)),
    ("Old H0, leading Omega_m=1/pi",
     70.65, 1/pi, 1/(2*pi**2), 1/(4*pi**7), (pi-1)/pi),
    ("H0=70.65, Bott Omega_m (original)",
     70.65, 0.31150, 1/(2*pi**2), 1/(4*pi**7), 1 - 0.31150 - 1/(4*pi**7)),
]

print(f"{'Set':<35s}  {'H0':>6s}  {'Om':>7s}  {'r_d_n':>6s}  "
      f"{'r_d_f':>6s}  {'chi2_n':>7s}  {'chi2_f':>7s}  "
      f"{'chi2/n_n':>8s}  {'chi2/n_f':>8s}  {'ell_A_n':>7s}  {'ell_A_f':>7s}")
print("-" * 120)

for name, H0, Om, Ob, Or, OL in sets:
    res = compute_chi2(H0, Om, Ob, Or, OL)
    n = 13
    print(f"{name:<35s}  {H0:6.2f}  {Om:7.5f}  {res['r_d_num']:6.1f}  "
          f"{res['r_d_fit']:6.1f}  {res['chi2_num']:7.2f}  {res['chi2_fit']:7.2f}  "
          f"{res['chi2_num']/n:8.3f}  {res['chi2_fit']/n:8.3f}  "
          f"{res['ell_A_num']:7.1f}  {res['ell_A_fit']:7.1f}")

# === Detailed comparison of the best cascade set vs Planck ===
print()
print("=" * 90)
print("DETAILED: OLD CASCADE (BOTT) vs PLANCK vs UPDATED CASCADE")
print("=" * 90)

# Recompute with detailed pulls for the three main contenders
for name, H0, Om, Ob, Or, OL in [sets[0], sets[1], sets[2]]:
    h = H0 / 100.0
    omega_m = Om * h**2
    omega_b = Ob * h**2
    omega_r = Or * h**2
    Omega_gamma = Or / factor_nu
    omega_gamma = Omega_gamma * h**2

    def make_H(H0_l, Or_l, Om_l, OL_l):
        def H(z):
            return H0_l * np.sqrt(Or_l*(1+z)**4 + Om_l*(1+z)**3 + OL_l)
        return H

    Hfn = make_H(H0, Or, Om, OL)

    def D_M_fn(z):
        result, _ = integrate.quad(lambda zp: c_km_s / Hfn(zp), 0, z)
        return result

    def D_H_fn(z):
        return c_km_s / Hfn(z)

    def D_V_fn(z):
        dm = D_M_fn(z)
        dh = D_H_fn(z)
        return (z * dh * dm**2) ** (1.0 / 3.0)

    b1 = 0.313 * omega_m**(-0.419) * (1 + 0.607 * omega_m**0.674)
    b2 = 0.238 * omega_m**0.223
    z_drag = (1291.0 * omega_m**0.251 / (1 + 0.659 * omega_m**0.828)
              * (1 + b1 * omega_b**b2))
    R_coeff = 3.0 * omega_b / (4.0 * omega_gamma)

    def integrand_fn(z_prime):
        R = R_coeff / (1.0 + z_prime)
        c_s = 1.0 / np.sqrt(3.0 * (1.0 + R))
        return c_s * c_km_s / Hfn(z_prime)

    r_d, _ = integrate.quad(integrand_fn, z_drag, np.inf)

    # Use Planck's known r_d for Planck
    if "Planck" in name:
        r_d = 147.60

    print(f"\n--- {name} (H0={H0}, Om={Om:.5f}, r_d={r_d:.1f} Mpc) ---")
    print(f"{'z':>6s}  {'Type':>4s}  {'DESI':>8s}  {'Pred':>8s}  {'Pull':>8s}")

    chi2 = 0
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            pred = D_V_fn(z) / r_d
        elif typ == "DM":
            pred = D_M_fn(z) / r_d
        elif typ == "DH":
            pred = D_H_fn(z) / r_d
        pull = (pred - obs) / sig
        chi2 += pull**2
        print(f"{z:6.3f}  {typ:>4s}  {obs:8.3f}  {pred:8.3f}  {pull:+7.2f}σ")
    print(f"chi2 = {chi2:.2f}, chi2/n = {chi2/13:.3f}")
