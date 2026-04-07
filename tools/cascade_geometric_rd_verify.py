#!/usr/bin/env python3
"""
Test the candidate z_drag = 2*pi^6 / sqrt(3).
"""

import numpy as np
from scipy import integrate

c_km_s = 299792.458
pi = np.pi

H0 = 71.05
h = H0 / 100.0
Omega_m = 1.0 / pi
Omega_b = 1.0 / (2.0 * pi**2)
Omega_r = 1.0 / (4.0 * pi**7)
Omega_Lambda = (pi - 1.0) / pi

N_eff = 3.0
factor_nu = 1.0 + (7.0/8.0) * (4.0/11.0)**(4.0/3.0) * N_eff
Omega_gamma = Omega_r / factor_nu

R_coeff = 3.0 * Omega_b / (4.0 * Omega_gamma)


def H_cascade(z):
    return H0 * np.sqrt(Omega_r*(1+z)**4 + Omega_m*(1+z)**3 + Omega_Lambda)


def sound_speed(z):
    R = R_coeff / (1.0 + z)
    return 1.0 / np.sqrt(3.0 * (1.0 + R))


def compute_rd(z_d):
    def integrand(z):
        return sound_speed(z) * c_km_s / H_cascade(z)
    result, _ = integrate.quad(integrand, z_d, 1e6, limit=200)
    return result


# === The candidate ===
z_eq = 4.0 * pi**6  # = Omega_m / Omega_r
z_candidate = 2.0 * pi**6 / np.sqrt(3)

print("=" * 60)
print("CANDIDATE: z_drag = 2*pi^6 / sqrt(3)")
print("=" * 60)
print(f"  z_eq       = 4*pi^6         = {z_eq:.4f}")
print(f"  z_drag     = 2*pi^6/sqrt(3) = {z_candidate:.4f}")
print(f"  Ratio      = z_drag/z_eq    = {z_candidate/z_eq:.6f}")
print(f"  1/(2*sqrt(3))               = {1/(2*np.sqrt(3)):.6f}")
print()

# Compute r_d
r_d = compute_rd(z_candidate)

# Compute D_M(z*=1089)
D_M_star, _ = integrate.quad(lambda z: c_km_s / H_cascade(z), 0, 1089.0, limit=200)

ell_A = pi * D_M_star / r_d

print(f"  r_d        = {r_d:.2f} Mpc")
print(f"  D_M(1089)  = {D_M_star:.1f} Mpc")
print(f"  ell_A      = {ell_A:.2f}")
print(f"  Observed   = 301.6")
print(f"  Deviation  = {(ell_A - 301.6)/301.6*100:+.3f}%")
print()

# === What is sqrt(3) in the cascade? ===
print("=" * 60)
print("WHAT IS sqrt(3) IN THE CASCADE?")
print("=" * 60)

print("""
The observer at d=4 lives on S^3. The spatial section is 3-dimensional.

The factor 2*sqrt(3) in z_eq/z_drag decomposes as:
  - 2 = chi(S^{2n}), the Euler characteristic of even spheres
        (the hairy ball obstruction count)
  - sqrt(3) = sqrt(dim S^3), the spatial dimension of the observer

z_drag = z_eq / (chi * sqrt(dim))
       = (Omega_m / Omega_r) / (2 * sqrt(3))
       = 4*pi^6 / (2*sqrt(3))
       = 2*pi^6 / sqrt(3)

Physical interpretation: the drag epoch is the matter-radiation
equality DIVIDED by the geometric factor of the observer's spatial
shell. Sound waves on S^3 "see" a horizon that is 2*sqrt(3) times
smaller than the naive equality scale, because:
  - The Euler characteristic 2 accounts for the two hemispheres
    of the even-sphere obstruction
  - sqrt(3) accounts for the 3 independent spatial directions
    on S^3 over which sound can propagate
""")

# === DESI BAO comparison with this r_d ===
print("=" * 60)
print("DESI BAO WITH r_d FROM z_drag = 2*pi^6/sqrt(3)")
print("=" * 60)

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


def D_M_fn(z):
    result, _ = integrate.quad(lambda zp: c_km_s / H_cascade(zp), 0, z)
    return result

def D_H_fn(z):
    return c_km_s / H_cascade(z)

def D_V_fn(z):
    dm = D_M_fn(z)
    dh = D_H_fn(z)
    return (z * dh * dm**2)**(1.0/3.0)


print(f"\n{'z':>6s}  {'Type':>4s}  {'DESI':>8s}  {'sigma':>6s}  "
      f"{'Cascade':>8s}  {'Pull':>8s}")
print("-" * 55)

chi2 = 0.0
for z, typ, obs, sig in desi_data:
    if typ == "DV":
        pred = D_V_fn(z) / r_d
    elif typ == "DM":
        pred = D_M_fn(z) / r_d
    elif typ == "DH":
        pred = D_H_fn(z) / r_d
    pull = (pred - obs) / sig
    chi2 += pull**2
    print(f"{z:6.3f}  {typ:>4s}  {obs:8.3f}  {sig:6.3f}  "
          f"{pred:8.3f}  {pull:+7.2f}σ")

n = 13
print("-" * 55)
print(f"chi2 = {chi2:.2f}, chi2/n = {chi2/n:.3f}")
print()

# Compare all r_d candidates
print("=" * 60)
print("COMPARISON OF ALL r_d VALUES")
print("=" * 60)

for label, rd_val in [
    ("Planck", 147.6),
    ("E&H98 fit (cascade params)", 140.9),
    ("Cascade geometric: 2*pi^6/sqrt(3)", r_d),
]:
    chi2_test = 0.0
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            pred = D_V_fn(z) / rd_val
        elif typ == "DM":
            pred = D_M_fn(z) / rd_val
        elif typ == "DH":
            pred = D_H_fn(z) / rd_val
        chi2_test += ((pred - obs)/sig)**2

    ell_test = pi * D_M_star / rd_val
    print(f"  {label:<40s}  r_d={rd_val:6.1f}  chi2/n={chi2_test/n:.3f}  ell_A={ell_test:.1f}")

# === The complete cascade formula ===
print()
print("=" * 60)
print("THE COMPLETE CASCADE SOUND HORIZON FORMULA")
print("=" * 60)
print(f"""
  r_d = integral from z_drag to infinity of c_s(z) * c / H(z) dz

  where:
    H(z)    = H0 * sqrt[ (1+z)^4/(4*pi^7) + (1+z)^3/pi + (pi-1)/pi ]
    c_s(z)  = 1 / sqrt( 3 * (1 + R(z)) )
    R(z)    = 3*Omega_b / (4*Omega_gamma) / (1+z)
    z_drag  = 2*pi^6 / sqrt(3) = {z_candidate:.2f}

  Every quantity is a function of pi and the spatial dimension 3.
  r_d = {r_d:.2f} Mpc
  ell_A = {ell_A:.2f} (observed: 301.6, deviation: {(ell_A-301.6)/301.6*100:+.3f}%)
""")
