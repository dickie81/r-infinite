"""
Recompute the DESI DR2 BAO comparison with updated cascade parameters.

Old parameters: H0 = 70.65, Omega_m = 0.31150, r_d = 142.3 Mpc
New parameters: H0 = 71.05, Omega_m = 1/pi, Omega_b = 1/(2*pi^2), Omega_r = 1/(4*pi^7)

All cascade density fractions are functions of pi alone.
"""

import numpy as np
from scipy import integrate

# === Constants ===
c_km_s = 299792.458  # speed of light in km/s
pi = np.pi

# === Updated cascade parameters ===
H0 = 71.05  # km/s/Mpc
h = H0 / 100.0
Omega_m = 1.0 / pi                     # 0.31831
Omega_b = 1.0 / (2.0 * pi**2)          # 0.05066
Omega_r = 1.0 / (4.0 * pi**7)          # 8.277e-5
Omega_Lambda = (pi - 1.0) / pi         # 0.68169
Omega_DM = Omega_m - Omega_b           # 0.26765

# Physical densities
omega_m = Omega_m * h**2
omega_b = Omega_b * h**2
omega_r = Omega_r * h**2
omega_cb = omega_m  # CDM + baryons

print("=" * 60)
print("CASCADE PARAMETERS (updated)")
print("=" * 60)
print(f"H0           = {H0:.2f} km/s/Mpc")
print(f"h            = {h:.4f}")
print(f"Omega_m      = 1/pi = {Omega_m:.5f}")
print(f"Omega_b      = 1/(2*pi^2) = {Omega_b:.5f}")
print(f"Omega_DM     = (2*pi-1)/(2*pi^2) = {Omega_DM:.5f}")
print(f"Omega_r      = 1/(4*pi^7) = {Omega_r:.6e}")
print(f"Omega_Lambda = (pi-1)/pi = {Omega_Lambda:.5f}")
print(f"omega_m      = {omega_m:.5f}")
print(f"omega_b      = {omega_b:.5f}")
print(f"omega_r      = {omega_r:.6e}")
print(f"Sum          = {Omega_m + Omega_r + Omega_Lambda:.6f}")
print()


# === Hubble parameter ===
def H(z):
    """Hubble parameter H(z) in km/s/Mpc."""
    return H0 * np.sqrt(
        Omega_r * (1 + z)**4
        + Omega_m * (1 + z)**3
        + Omega_Lambda
    )


# === Comoving distance D_M(z) ===
def D_M(z):
    """Comoving distance in Mpc (flat universe)."""
    result, _ = integrate.quad(lambda zp: c_km_s / H(zp), 0, z)
    return result


# === Hubble distance D_H(z) ===
def D_H(z):
    """Hubble distance c/H(z) in Mpc."""
    return c_km_s / H(z)


# === Volume-averaged distance D_V(z) ===
def D_V(z):
    """Volume-averaged distance in Mpc."""
    dm = D_M(z)
    dh = D_H(z)
    return (z * dh * dm**2) ** (1.0 / 3.0)


# === Sound horizon computation ===
def compute_sound_horizon():
    """
    Compute the sound horizon r_d at the drag epoch.
    Uses the Eisenstein & Hu 1998 fitting formula for z_drag,
    then integrates the sound speed numerically.
    """
    # Baryon-to-photon ratio
    # Omega_gamma from T_CMB: rho_gamma = (pi^2/15) * T^4
    # But we can get it from Omega_r assuming N_eff = 3.044:
    # Omega_gamma = Omega_r / (1 + 7/8 * (4/11)^(4/3) * N_eff)
    N_eff = 3.044
    factor = 1.0 + (7.0 / 8.0) * (4.0 / 11.0) ** (4.0 / 3.0) * N_eff
    Omega_gamma = Omega_r / factor
    omega_gamma = Omega_gamma * h**2

    # Eisenstein & Hu 1998 fitting formula for z_drag
    b1 = 0.313 * omega_m**(-0.419) * (1 + 0.607 * omega_m**0.674)
    b2 = 0.238 * omega_m**0.223
    z_drag = (1291.0 * omega_m**0.251 / (1 + 0.659 * omega_m**0.828)
              * (1 + b1 * omega_b**b2))

    print(f"z_drag (E&H98) = {z_drag:.1f}")

    # Sound speed: c_s = c / sqrt(3(1 + R))
    # where R = 3*omega_b / (4*omega_gamma) * a = 3*omega_b / (4*omega_gamma) / (1+z)
    R_coeff = 3.0 * omega_b / (4.0 * omega_gamma)

    def integrand(z_prime):
        R = R_coeff / (1.0 + z_prime)
        c_s = 1.0 / np.sqrt(3.0 * (1.0 + R))  # in units of c
        return c_s * c_km_s / H(z_prime)

    r_d, _ = integrate.quad(integrand, z_drag, np.inf)
    return r_d, z_drag


# Also compute using the simpler Eisenstein & Hu fitting formula for r_d directly
def rd_EH98_fit():
    """Eisenstein & Hu 1998 fitting formula for r_d (approximate)."""
    return 147.60 * (omega_m / 0.1432)**(-0.255) * (omega_b / 0.02237)**(-0.127)


# === Compute sound horizon ===
print("=" * 60)
print("SOUND HORIZON")
print("=" * 60)

r_d_numerical, z_d = compute_sound_horizon()
r_d_fit = rd_EH98_fit()

print(f"r_d (numerical)  = {r_d_numerical:.2f} Mpc")
print(f"r_d (E&H98 fit)  = {r_d_fit:.2f} Mpc")
print(f"Planck r_d       = 147.60 Mpc")
print(f"Old cascade r_d  = 142.30 Mpc")
print()

# Use the numerical value
r_d = r_d_numerical

# === DESI DR2 BAO data ===
# (z_eff, type, observed_value, sigma)
# Types: "DV" = D_V/r_d, "DM" = D_M/r_d, "DH" = D_H/r_d
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

# === Old cascade predictions (from Part V table) ===
old_cascade = [
    (0.295, "DV", 7.949),
    (0.510, "DM", 13.323),
    (0.510, "DH", 22.471),
    (0.706, "DM", 17.475),
    (0.706, "DH", 19.945),
    (0.934, "DM", 21.723),
    (0.934, "DH", 17.385),
    (1.321, "DM", 27.749),
    (1.321, "DH", 13.929),
    (1.484, "DM", 29.922),
    (1.484, "DH", 12.758),
    (2.330, "DM", 38.748),
    (2.330, "DH", 8.540),
]


# === Compute predictions ===
print("=" * 60)
print("DESI DR2 BAO COMPARISON")
print("=" * 60)
print(f"{'z':>6s}  {'Type':>4s}  {'DESI':>8s}  {'sigma':>6s}  "
      f"{'Old cas':>8s}  {'New cas':>8s}  {'Pull_old':>9s}  {'Pull_new':>9s}")
print("-" * 75)

chi2_old = 0.0
chi2_new = 0.0

for i, (z, typ, obs, sig) in enumerate(desi_data):
    # Compute new cascade prediction
    if typ == "DV":
        pred_new = D_V(z) / r_d
    elif typ == "DM":
        pred_new = D_M(z) / r_d
    elif typ == "DH":
        pred_new = D_H(z) / r_d

    pred_old = old_cascade[i][2]

    pull_old = (pred_old - obs) / sig
    pull_new = (pred_new - obs) / sig

    chi2_old += pull_old**2
    chi2_new += pull_new**2

    print(f"{z:6.3f}  {typ:>4s}  {obs:8.3f}  {sig:6.3f}  "
          f"{pred_old:8.3f}  {pred_new:8.3f}  {pull_old:+8.2f}σ  {pull_new:+8.2f}σ")

n = len(desi_data)
print("-" * 75)
print(f"{'χ² total':>40s}  {chi2_old:8.2f}  {chi2_new:8.2f}")
print(f"{'χ²/n (n=13)':>40s}  {chi2_old/n:8.3f}  {chi2_new/n:8.3f}")
print()

# === Planck LCDM comparison ===
# Planck parameters for reference
print("=" * 60)
print("PLANCK LCDM COMPARISON")
print("=" * 60)

H0_planck = 67.4
h_planck = H0_planck / 100.0
Omega_m_planck = 0.315
Omega_b_planck = 0.0493
Omega_r_planck = 9.15e-5  # from Planck
Omega_Lambda_planck = 1.0 - Omega_m_planck - Omega_r_planck
r_d_planck = 147.60  # Mpc


def H_planck_fn(z):
    return H0_planck * np.sqrt(
        Omega_r_planck * (1 + z)**4
        + Omega_m_planck * (1 + z)**3
        + Omega_Lambda_planck
    )


def D_M_planck(z):
    result, _ = integrate.quad(lambda zp: c_km_s / H_planck_fn(zp), 0, z)
    return result


def D_H_planck(z):
    return c_km_s / H_planck_fn(z)


def D_V_planck(z):
    dm = D_M_planck(z)
    dh = D_H_planck(z)
    return (z * dh * dm**2) ** (1.0 / 3.0)


print(f"{'z':>6s}  {'Type':>4s}  {'DESI':>8s}  {'sigma':>6s}  "
      f"{'Planck':>8s}  {'Pull':>9s}")
print("-" * 50)

chi2_planck = 0.0
for z, typ, obs, sig in desi_data:
    if typ == "DV":
        pred = D_V_planck(z) / r_d_planck
    elif typ == "DM":
        pred = D_M_planck(z) / r_d_planck
    elif typ == "DH":
        pred = D_H_planck(z) / r_d_planck

    pull = (pred - obs) / sig
    chi2_planck += pull**2
    print(f"{z:6.3f}  {typ:>4s}  {obs:8.3f}  {sig:6.3f}  "
          f"{pred:8.3f}  {pull:+8.2f}σ")

print("-" * 50)
print(f"{'χ² total':>30s}  {chi2_planck:8.2f}")
print(f"{'χ²/n (n=13)':>30s}  {chi2_planck/n:8.3f}")
print()

# === Summary ===
print("=" * 60)
print("SUMMARY")
print("=" * 60)
print(f"{'Model':<25s}  {'χ²':>8s}  {'χ²/n':>8s}  {'r_d (Mpc)':>10s}")
print("-" * 55)
print(f"{'Planck LCDM':<25s}  {chi2_planck:8.2f}  {chi2_planck/n:8.3f}  {r_d_planck:10.1f}")
print(f"{'Cascade (old params)':<25s}  {chi2_old:8.2f}  {chi2_old/n:8.3f}  {'142.3':>10s}")
print(f"{'Cascade (updated)':<25s}  {chi2_new:8.2f}  {chi2_new/n:8.3f}  {r_d:10.1f}")
print()

# === Acoustic scale ===
print("=" * 60)
print("ACOUSTIC SCALE (ell_A)")
print("=" * 60)
# ell_A = pi * D_M(z*) / r_d where z* ~ 1089 (last scattering)
z_star = 1089.0
D_M_star = D_M(z_star)
ell_A = pi * D_M_star / r_d
print(f"D_M(z*={z_star:.0f}) = {D_M_star:.1f} Mpc")
print(f"r_d              = {r_d:.2f} Mpc")
print(f"ell_A = pi * D_M / r_d = {ell_A:.1f}")
print(f"Planck observed  = 301.6")
print(f"Old cascade      = 297.6")
print(f"Deviation         = {(ell_A - 301.6) / 301.6 * 100:+.2f}%")
print()

# === w_apparent from ruler mismatch ===
print("=" * 60)
print("APPARENT w FROM RULER MISMATCH")
print("=" * 60)
# When Planck's r_d is imposed on cascade distances, the apparent w shifts
# The effect is approximately: w_apparent ~ -1 + (2/3) * ln(r_d_cascade / r_d_planck)
# More precisely, we can estimate from the D_M scaling
ratio = r_d / r_d_planck
# In a wCDM model, D_M scales roughly as (1+z)^(3(1+w)/2) at low z
# The mismatch in r_d shifts the inferred w
# Using the approximate relation from the paper
w_apparent = -1.0 + 2.0/3.0 * np.log(r_d / r_d_planck) / np.log(1.5)
print(f"r_d(cascade) / r_d(Planck) = {ratio:.4f}")
print(f"Approximate w_apparent     ~ {w_apparent:.3f}")
print(f"DESI BAO+CMB observed      = -0.76 ± 0.11")
