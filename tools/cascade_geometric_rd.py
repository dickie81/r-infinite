#!/usr/bin/env python3
"""
Compute the cascade's own sound horizon from pure geometry.

No semiclassics. No Boltzmann solver. No E&H98 fitting formula.

The cascade provides:
  - H(z) from the Friedmann equation (all coefficients are pi)
  - c_s from Omega_b / Omega_gamma (both cascade-derived)
  - Integration limits from the cascade's geometric transitions

The "drag epoch" is identified with the cascade's own geometric
transition: the gauge boundary crossing at d=11/12, where the
radiation content (originating at the gauge boundary) decouples
from the baryon content (on the observer's S^3 shell).
"""

import numpy as np
from scipy import integrate

c_km_s = 299792.458  # km/s
pi = np.pi

# === Cascade parameters (all functions of pi) ===
H0 = 71.05  # km/s/Mpc
h = H0 / 100.0
Omega_m = 1.0 / pi
Omega_b = 1.0 / (2.0 * pi**2)
Omega_r = 1.0 / (4.0 * pi**7)
Omega_Lambda = (pi - 1.0) / pi

# === Cascade-derived neutrino/photon split ===
# The cascade derives 3 generations (Part IVa, Bott + d1=19 phase transition).
# Each generation contributes one neutrino species.
# The cascade derives QM (Part II), so Fermi-Dirac vs Bose-Einstein statistics follow.
# N_eff = 3 (cascade: exactly 3 generations; the 0.044 correction is a QFT loop effect)
N_eff_cascade = 3.0

# The factor (4/11)^(4/3) comes from entropy conservation during e+e- annihilation.
# In cascade terms: the electron is a cascade fermion at d=21; its annihilation
# transfers entropy to photons. The counting:
#   Before: g*_s = 2 (photon) + 7/8 * 4 (e+e-) = 11/2
#   After:  g*_s = 2 (photon)
#   T_nu/T_gamma = (4/11)^(1/3)
# The factors 2, 7/8, 4 are cascade-derived:
#   2 = chi(S^{2n}) from the hairy ball theorem (polarisation states)
#   7/8 = Fermi-Dirac integral / Bose-Einstein integral (cascade QM)
#   4 = electron + positron, 2 spin states each (cascade SM)
factor_nu = 1.0 + (7.0/8.0) * (4.0/11.0)**(4.0/3.0) * N_eff_cascade
Omega_gamma = Omega_r / factor_nu
Omega_nu = Omega_r - Omega_gamma

print("=" * 70)
print("CASCADE GEOMETRIC SOUND HORIZON")
print("=" * 70)
print(f"Omega_r      = 1/(4*pi^7)    = {Omega_r:.6e}")
print(f"Omega_gamma  = Omega_r/{factor_nu:.3f}  = {Omega_gamma:.6e}")
print(f"Omega_b      = 1/(2*pi^2)    = {Omega_b:.5f}")
print(f"Omega_m      = 1/pi          = {Omega_m:.5f}")
print(f"Omega_Lambda = (pi-1)/pi     = {Omega_Lambda:.5f}")
print(f"N_eff        = {N_eff_cascade:.0f} (cascade: 3 generations)")
print()


def H_cascade(z):
    """Cascade Friedmann equation. Every coefficient is pi."""
    return H0 * np.sqrt(
        Omega_r * (1+z)**4
        + Omega_m * (1+z)**3
        + Omega_Lambda
    )


def sound_speed(z):
    """
    Sound speed in the baryon-photon fluid.
    c_s = 1/sqrt(3(1+R)) where R = 3*rho_b / (4*rho_gamma)

    In cascade units:
    R = 3*Omega_b / (4*Omega_gamma) * 1/(1+z)
      = 3/(2*pi^2) / (4*Omega_gamma) * 1/(1+z)
    """
    R = 3.0 * Omega_b / (4.0 * Omega_gamma) / (1.0 + z)
    return 1.0 / np.sqrt(3.0 * (1.0 + R))


# === The cascade's geometric drag epoch ===
#
# In standard cosmology, z_drag ~ 1060 is where baryons decouple from photons
# (Thomson scattering becomes inefficient after hydrogen recombination).
#
# In the cascade, we seek a GEOMETRIC definition. Several candidates:

print("=" * 70)
print("CASCADE GEOMETRIC TRANSITIONS")
print("=" * 70)

# The cascade lapse function
def N_lapse(d):
    """Cascade lapse N(d) = sqrt(pi) * Gamma((d+1)/2) / Gamma((d+2)/2)"""
    from scipy.special import gamma
    return np.sqrt(pi) * gamma((d+1)/2.0) / gamma((d+2)/2.0)

print("\nCascade lapse N(d) and distinguished dimensions:")
for d in [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 19]:
    print(f"  N({d:2d}) = {N_lapse(d):.5f}")

print(f"\n  Self-dual radius 1/sqrt(2) = {1/np.sqrt(2):.5f}")
print(f"  Crossing between d=12 (N={N_lapse(12):.5f}) and d=13 (N={N_lapse(13):.5f})")

# The matter-radiation equality from cascade geometry
z_eq_cascade = Omega_m / Omega_r  # = 4*pi^6
print(f"\nMatter-radiation equality:")
print(f"  z_eq = Omega_m/Omega_r = 4*pi^6 = {z_eq_cascade:.1f}")

# Candidate 1: z_eq itself as the geometric transition
# In many analytic approximations, z_drag ~ z_eq is a reasonable first estimate

# Candidate 2: The baryon-photon equality R=1
# R(z) = 3*Omega_b / (4*Omega_gamma) / (1+z)
# R = 1 when z+1 = 3*Omega_b / (4*Omega_gamma)
R_coeff = 3.0 * Omega_b / (4.0 * Omega_gamma)
z_R1 = R_coeff - 1.0
print(f"\nBaryon-photon momentum equality R=1:")
print(f"  R_coeff = 3*Omega_b/(4*Omega_gamma) = {R_coeff:.2f}")
print(f"  z(R=1) = {z_R1:.1f}")
print(f"  c_s at R=1 = 1/sqrt(6) = {1/np.sqrt(6):.5f}")

# Candidate 3: The cascade's natural transition scale
# The radiation density Omega_r = 1/(4*pi^7) involves 7 geometric steps.
# The baryon fraction Omega_b = 1/(2*pi^2) involves the observer's boundary.
# Their ratio encodes the geometric distance between the observer and the gauge boundary.
# Decoupling happens when the baryon content "catches up" to radiation:
# rho_b(z) = rho_gamma(z) at z+1 = Omega_b/Omega_gamma = Omega_b * factor_nu / Omega_r
z_b_gamma = Omega_b / Omega_gamma - 1.0
print(f"\nBaryon-photon energy equality:")
print(f"  z(rho_b = rho_gamma) = {z_b_gamma:.1f}")

# Candidate 4: Geometric mean of cascade transitions
# sqrt(z_eq * z_R1) or other combinations
z_geometric_mean = np.sqrt(z_eq_cascade * z_R1)
print(f"\nGeometric mean sqrt(z_eq * z_R1) = {z_geometric_mean:.1f}")

# Candidate 5: The cascade's own "recombination" scale
# The hydrogen binding energy is 13.6 eV. T_CMB = 2.730 K = 2.35e-4 eV.
# Recombination at T ~ 0.3 eV, so z_rec ~ 0.3/2.35e-4 ~ 1275.
# But this uses atomic physics, which is semiclassical.
# The cascade alternative: the Bott period structure.
# The cascade's Bott period is 8. The descent from d=12 to d=4 spans one Bott period.
# The "recombination" might correspond to the point where the observer's Bott
# sector (complex, d mod 8 = 4) separates from the gauge Bott sector (complex, d mod 8 = 4).
# At d=12: d mod 8 = 4 (same Bott class as observer).
# The transition is the Bott mirror itself.


print("\n" + "=" * 70)
print("SOUND HORIZON COMPUTATION")
print("=" * 70)

def compute_rd(z_upper, label):
    """Compute r_d = integral from z_upper to infinity of c_s/H dz, in Mpc."""
    def integrand(z):
        return sound_speed(z) * c_km_s / H_cascade(z)

    # Integrate from z_upper to a large z (radiation dominated, integrand -> 0)
    result, err = integrate.quad(integrand, z_upper, 1e6,
                                  limit=200)

    # Also compute the integral split into segments for insight
    if z_upper < z_eq_cascade:
        rd_early, _ = integrate.quad(integrand, z_eq_cascade, 1e6, limit=200)
        rd_late, _ = integrate.quad(integrand, z_upper, z_eq_cascade, limit=200)
    else:
        rd_early = result
        rd_late = 0.0

    return result, rd_early, rd_late


# Test all candidates
candidates = [
    ("z_eq = 4*pi^6 (matter-rad equality)", z_eq_cascade),
    ("z(R=1) (baryon-photon momentum eq)", z_R1),
    ("z(rho_b=rho_gamma) (energy equality)", z_b_gamma),
    ("sqrt(z_eq * z_R1) (geometric mean)", z_geometric_mean),
    ("z_drag = 1060 (standard, for reference)", 1060.0),
    ("z_drag = 1029 (E&H98 with cascade params)", 1029.0),
]

print(f"\n{'Candidate':<45s}  {'z_d':>7s}  {'r_d':>8s}  {'ell_A':>7s}  {'Dev':>7s}")
print("-" * 85)

# Compute D_M(z*=1089) once
D_M_star, _ = integrate.quad(lambda z: c_km_s / H_cascade(z), 0, 1089.0, limit=200)

for label, z_d in candidates:
    rd, rd_e, rd_l = compute_rd(z_d, label)
    ell_A = pi * D_M_star / rd
    dev = (ell_A - 301.6) / 301.6 * 100
    print(f"{label:<45s}  {z_d:7.1f}  {rd:7.1f}  {ell_A:7.1f}  {dev:+6.2f}%")


# === Deep dive: the cascade's purely geometric candidate ===
print("\n" + "=" * 70)
print("THE CASCADE'S GEOMETRIC SOUND HORIZON")
print("=" * 70)

# The matter-radiation equality z_eq = 4*pi^6 is the most purely cascade quantity.
# It's determined entirely by Omega_m/Omega_r = (1/pi)/(1/(4*pi^7)) = 4*pi^6.
# Both are cascade-derived functions of pi.

rd_eq, _, _ = compute_rd(z_eq_cascade, "z_eq")
ell_A_eq = pi * D_M_star / rd_eq

print(f"\nUsing z_drag = z_eq = 4*pi^6 = {z_eq_cascade:.1f}:")
print(f"  r_d = {rd_eq:.2f} Mpc")
print(f"  ell_A = pi * D_M(1089) / r_d = {ell_A_eq:.1f}")
print(f"  Planck observed ell_A = 301.6")
print(f"  Deviation = {(ell_A_eq - 301.6)/301.6*100:+.2f}%")

# The R=1 point
rd_R1, _, _ = compute_rd(z_R1, "R=1")
ell_A_R1 = pi * D_M_star / rd_R1

print(f"\nUsing z_drag = z(R=1) = {z_R1:.1f}:")
print(f"  r_d = {rd_R1:.2f} Mpc")
print(f"  ell_A = {ell_A_R1:.1f}")
print(f"  Deviation = {(ell_A_R1 - 301.6)/301.6*100:+.2f}%")

# What z_drag gives ell_A = 301.6 exactly?
print("\n" + "=" * 70)
print("INVERSE PROBLEM: WHAT z_drag GIVES ell_A = 301.6?")
print("=" * 70)

from scipy.optimize import brentq

def ell_A_residual(z_d):
    rd, _, _ = compute_rd(z_d, "")
    return pi * D_M_star / rd - 301.6

z_exact = brentq(ell_A_residual, 500, 5000)
rd_exact, _, _ = compute_rd(z_exact, "")
print(f"  z_drag that gives ell_A = 301.6: {z_exact:.1f}")
print(f"  Corresponding r_d = {rd_exact:.2f} Mpc")
print(f"  For comparison: z_eq = 4*pi^6 = {z_eq_cascade:.1f}")
print(f"  Ratio z_exact/z_eq = {z_exact/z_eq_cascade:.4f}")

# Check if the required z_drag has a cascade interpretation
print(f"\n  Is z_exact a cascade number?")
print(f"  z_exact / pi^6 = {z_exact / pi**6:.4f}")
print(f"  z_exact / (4*pi^6) = {z_exact / (4*pi**6):.4f}")
print(f"  z_exact / (3*pi^6) = {z_exact / (3*pi**6):.4f}")
print(f"  z_exact / (2*pi^6) = {z_exact / (2*pi**6):.4f}")
print(f"  z_exact / pi^5 = {z_exact / pi**5:.4f}")
print(f"  z_exact / (pi^6/2) = {z_exact / (pi**6/2):.4f}")

# What about z_drag = R_coeff * z_eq^{1/2}? Or some other combination?
print(f"\n  Cascade combinations near z_exact = {z_exact:.1f}:")
combos = [
    ("4*pi^6 (z_eq)", 4*pi**6),
    ("3*pi^6", 3*pi**6),
    ("pi^6", pi**6),
    ("2*pi^6", 2*pi**6),
    ("4*pi^6 / (1+1/pi)", 4*pi**6 / (1+1/pi)),
    ("4*pi^6 * Omega_Lambda", 4*pi**6 * Omega_Lambda),
    ("4*pi^6 * N(4)/N(5)", 4*pi**6 * N_lapse(4)/N_lapse(5)),
    ("4*pi^6 / (1+Omega_b)", 4*pi**6 / (1+Omega_b)),
    ("4*pi^6 * pi/(pi+1)", 4*pi**6 * pi/(pi+1)),
    ("2*pi^5 * (2*pi-1)", 2*pi**5 * (2*pi-1)),
    ("Omega_m / (Omega_r*(1+R_eq))", Omega_m/(Omega_r*(1+R_coeff))),
    ("pi^6 * (2*pi+1)/pi", pi**6 * (2*pi+1)/pi),
]

for label, val in sorted(combos, key=lambda x: abs(x[1] - z_exact)):
    dev = (val - z_exact) / z_exact * 100
    print(f"    {label:<35s} = {val:8.1f}  (dev {dev:+.2f}%)")

# === DESI comparison with geometric r_d ===
print("\n" + "=" * 70)
print("DESI BAO WITH CASCADE GEOMETRIC r_d")
print("=" * 70)

# Use the best geometric candidate
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


for label, rd_test in [
    ("E&H98 fit (r_d=140.9)", 140.9),
    ("z_eq geometric (r_d=%.1f)" % rd_eq, rd_eq),
    ("z(R=1) geometric (r_d=%.1f)" % rd_R1, rd_R1),
    ("Exact match (r_d=%.1f)" % rd_exact, rd_exact),
]:
    chi2 = 0.0
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            pred = D_V_fn(z) / rd_test
        elif typ == "DM":
            pred = D_M_fn(z) / rd_test
        elif typ == "DH":
            pred = D_H_fn(z) / rd_test
        chi2 += ((pred - obs) / sig)**2

    print(f"  {label:<40s}  chi2/13 = {chi2/13:.3f}")
