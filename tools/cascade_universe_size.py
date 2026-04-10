#!/usr/bin/env python3
"""
The size of the universe according to the cascade.

Key questions:
  1. How big is the observable universe?
  2. How big is the TOTAL universe (S^3)?
  3. What fraction can we see?
  4. What fraction of the CMB are we seeing?

The cascade gives:
  - S^3 topology (closed, finite)
  - H_0 = 71.05, Omega_m = 1/pi, Omega_Lambda = (pi-1)/pi
  - Omega_k ~ 0 (curvature radius >> Hubble radius)
  - De Sitter horizon area A_dS = 12*pi/Lambda ~ 10^120 Planck areas
"""

import numpy as np
from scipy import integrate

c_km_s = 299792.458  # km/s
pi = np.pi
Mpc_to_Gly = 0.003262  # 1 Mpc = 0.003262 Gly

# === Cascade parameters ===
H0 = 71.05  # km/s/Mpc
Omega_m = 1.0 / pi
Omega_r = 1.0 / (4.0 * pi**7)
Omega_Lambda = (pi - 1.0) / pi

# Derived
R_Hubble = c_km_s / H0  # Hubble radius in Mpc
R_Hubble_Gly = R_Hubble * Mpc_to_Gly


def E(z):
    """E(z) = H(z)/H_0"""
    return np.sqrt(Omega_r*(1+z)**4 + Omega_m*(1+z)**3 + Omega_Lambda)


def comoving_distance(z_max):
    """Comoving distance to redshift z_max, in Mpc."""
    result, _ = integrate.quad(lambda z: c_km_s / (H0 * E(z)), 0, z_max, limit=500)
    return result


def lookback_time(z_max):
    """Lookback time to redshift z_max, in Gyr."""
    H0_per_Gyr = H0 / 977.8  # H0 in 1/Gyr
    result, _ = integrate.quad(lambda z: 1.0 / ((1+z) * H0_per_Gyr * E(z)), 0, z_max, limit=500)
    return result


print("=" * 75)
print("THE SIZE OF THE UNIVERSE ACCORDING TO THE CASCADE")
print("=" * 75)

# ===================================================================
# PART 1: The Observable Universe
# ===================================================================
print("\n" + "=" * 75)
print("PART 1: THE OBSERVABLE UNIVERSE")
print("=" * 75)

# Hubble radius
print(f"\n  Hubble radius c/H_0:")
print(f"    = {R_Hubble:.0f} Mpc = {R_Hubble_Gly:.2f} Gly")

# Age of the universe
t_age = lookback_time(1e6)  # integrate to very high z
print(f"\n  Age of the universe:")
print(f"    = {t_age:.2f} Gyr")

# Comoving distance to the CMB (z = 1089)
d_CMB = comoving_distance(1089)
d_CMB_Gly = d_CMB * Mpc_to_Gly
print(f"\n  Comoving distance to CMB (z = 1089):")
print(f"    = {d_CMB:.0f} Mpc = {d_CMB_Gly:.2f} Gly")

# Particle horizon (comoving distance to z -> infinity)
d_horizon = comoving_distance(1e6)
d_horizon_Gly = d_horizon * Mpc_to_Gly
print(f"\n  Particle horizon (z -> infinity):")
print(f"    = {d_horizon:.0f} Mpc = {d_horizon_Gly:.2f} Gly")

# Physical radius of the observable universe TODAY
# (comoving distance * scale factor = comoving distance since a_0 = 1)
print(f"\n  Physical radius of observable universe today:")
print(f"    = {d_horizon:.0f} Mpc = {d_horizon_Gly:.2f} Gly")
print(f"    = {d_horizon_Gly * 1e9:.2e} light-years")

# Diameter
print(f"\n  Diameter of observable universe:")
print(f"    = {2*d_horizon_Gly:.2f} Gly = {2*d_horizon_Gly*1e9:.2e} light-years")

# The event horizon (maximum distance light emitted NOW can ever reach)
# In a Lambda-dominated universe, this is finite:
# d_event = integral from 0 to infinity of c*dt/a = c/H_0 * integral_0^inf dz/((1+z)^2 * E(z))
# Wait, that's not right. Event horizon is from now to future infinity:
# d_event = c * integral_{t_0}^{inf} dt/a(t) = c/H_0 * integral_0^inf da/(a^2 * H(a)/H_0)
# For a Lambda-dominated universe, d_event = c/H_0 * 1/sqrt(Omega_Lambda)

d_event_approx = c_km_s / (H0 * np.sqrt(Omega_Lambda))
# More precise: integrate
def event_horizon_integrand(z):
    return c_km_s / (H0 * (1+z)**2 * E(z))
d_event, _ = integrate.quad(event_horizon_integrand, 0, 1e6, limit=500)

print(f"\n  Cosmic event horizon (comoving distance light can reach):")
print(f"    = {d_event:.0f} Mpc = {d_event * Mpc_to_Gly:.2f} Gly")


# ===================================================================
# PART 2: THE TOTAL S^3 UNIVERSE
# ===================================================================
print("\n" + "=" * 75)
print("PART 2: THE TOTAL SIZE OF THE S^3")
print("=" * 75)

print("""
The cascade predicts S^3 topology (closed, finite universe).
Part V: "curvature radius far exceeding the Hubble radius"

The cascade does NOT give a precise Omega_k at leading order.
It gives Omega_k = 0 (flat) as the leading prediction, with S^3
topology from the B^4 boundary structure.

Key cascade relation (Part II=III):
  De Sitter horizon area A_dS = 12*pi/Lambda ~ 10^120 Planck areas
  This is the cascade hierarchy inverted: Omega_7/Omega_217 ~ 10^121

The de Sitter radius r_dS = sqrt(3/Lambda) is the NATURAL scale of
the S^3 in the cascade: it's where the cosmological horizon sits.
""")

# The de Sitter radius
# Lambda in natural units: Lambda = I * M_Pl^4 / M_Pl^2 = I * M_Pl^2
# In terms of H_0: Lambda = 3 * H_0^2 * Omega_Lambda / c^2
# de Sitter radius: r_dS = c / (H_0 * sqrt(Omega_Lambda))
r_dS = c_km_s / (H0 * np.sqrt(Omega_Lambda))
r_dS_Gly = r_dS * Mpc_to_Gly

print(f"  De Sitter radius r_dS = c/(H_0 * sqrt(Omega_Lambda)):")
print(f"    = {r_dS:.0f} Mpc = {r_dS_Gly:.2f} Gly")
print(f"    = {r_dS / R_Hubble:.3f} Hubble radii")

# The de Sitter radius is the COSMOLOGICAL HORIZON in a Lambda-dominated universe.
# Beyond this distance, objects recede faster than light.
# In the cascade, this is the natural boundary of "our" part of S^3.

# But the TOTAL S^3 could be much larger. With Omega_k:
print(f"\n  S^3 curvature radius for different Omega_k:")
print(f"  {'Omega_k':>10s}  {'R_curv (Mpc)':>14s}  {'R_curv (Gly)':>14s}  {'Circumf (Gly)':>14s}  {'R/R_Hubble':>12s}")
print(f"  {'-'*70}")

for Ok in [-0.05, -0.02, -0.01, -0.005, -0.002, -0.001, -0.0001]:
    R_curv = c_km_s / (H0 * np.sqrt(abs(Ok)))
    R_curv_Gly = R_curv * Mpc_to_Gly
    circumf = 2 * pi * R_curv_Gly
    print(f"  {Ok:+10.4f}  {R_curv:14.0f}  {R_curv_Gly:14.1f}  {circumf:14.1f}  {R_curv/R_Hubble:12.1f}")

# The cascade's 213-step descent as a natural scale
print(f"\n  Natural cascade scale: 213 descent steps")
n_steps = 213  # d=217 to d=4
# If R_curv = n_steps * R_Hubble:
R_cas_213 = n_steps * R_Hubble
Ok_213 = -(R_Hubble / R_cas_213)**2
print(f"  If R_curv = {n_steps} * R_Hubble:")
print(f"    R_curv = {R_cas_213:.0f} Mpc = {R_cas_213 * Mpc_to_Gly:.0f} Gly")
print(f"    Omega_k = -1/{n_steps}^2 = {Ok_213:.6f}")
print(f"    Circumference = {2*pi*R_cas_213*Mpc_to_Gly:.0f} Gly")

# What about R_curv = exp(cascade potential at d=217)?
# Phi(217) = sum of p(d) from d=5 to d=217
from scipy.special import digamma
Phi_217 = sum(0.5*digamma((d+1)/2) - 0.5*np.log(pi) for d in range(5, 218))
print(f"\n  Cascade potential Phi(217) = {Phi_217:.2f}")
print(f"  exp(Phi(217)) = {np.exp(Phi_217):.2e}")

# The cascade hierarchy: Omega_7/Omega_217
Omega_7 = pi**4 / 3
from scipy.special import gamma as Gamma
Omega_217 = 2 * pi**(218/2) / Gamma(218/2)
hierarchy = Omega_7 / Omega_217
print(f"\n  Cascade hierarchy Omega_7/Omega_217 = {hierarchy:.2e}")
print(f"  sqrt(hierarchy) = {np.sqrt(hierarchy):.2e}")

# If R_curv = sqrt(hierarchy) * l_Planck:
# l_Planck ~ 1.616e-35 m ~ 5.24e-58 Mpc
l_Pl_Mpc = 1.616e-35 / 3.086e22  # meters to Mpc
R_hierarchy = np.sqrt(hierarchy) * l_Pl_Mpc
print(f"\n  If R_curv = sqrt(Omega_7/Omega_217) * l_Planck:")
print(f"    R_curv = {R_hierarchy:.2e} Mpc = {R_hierarchy * Mpc_to_Gly:.2e} Gly")
print(f"    This is {R_hierarchy / R_Hubble:.2e} Hubble radii")
print(f"    Observable fraction ~ (R_Hubble/R_curv)^3 = {(R_Hubble/R_hierarchy)**3:.2e}")

# ===================================================================
# PART 3: WHAT FRACTION DO WE SEE?
# ===================================================================
print("\n" + "=" * 75)
print("PART 3: WHAT FRACTION OF THE UNIVERSE DO WE SEE?")
print("=" * 75)

def visible_fraction_S3(chi_obs, R_curv):
    """Fraction of S^3 volume within comoving distance chi_obs.

    On S^3 with radius R:
    - The total volume is 2*pi^2*R^3
    - Volume within comoving distance chi is:
      V(chi) = pi*R^3 * (2*theta - sin(2*theta))
      where theta = chi/R (angle on S^3, in [0, pi])
    """
    theta = chi_obs / R_curv
    if theta >= pi:
        return 1.0  # see the whole thing
    V_obs = pi * R_curv**3 * (2*theta - np.sin(2*theta))
    V_total = 2 * pi**2 * R_curv**3
    return V_obs / V_total


print(f"\n  Observable radius (particle horizon): {d_horizon:.0f} Mpc = {d_horizon_Gly:.2f} Gly")
print(f"  CMB distance: {d_CMB:.0f} Mpc = {d_CMB_Gly:.2f} Gly")

print(f"\n  Fraction of S^3 volume observable, for different curvature radii:")
print(f"  {'R_curv (Gly)':>14s}  {'Circumf (Gly)':>14s}  {'Vol_obs/Vol_tot':>16s}  {'CMB frac':>10s}  {'Omega_k':>10s}")
print(f"  {'-'*75}")

for Ok in [-0.05, -0.02, -0.01, -0.005, -0.002, -0.001, -0.0001, -0.00001]:
    R = c_km_s / (H0 * np.sqrt(abs(Ok)))
    R_Gly = R * Mpc_to_Gly
    circumf = 2 * pi * R_Gly
    frac_obs = visible_fraction_S3(d_horizon, R)
    frac_cmb = visible_fraction_S3(d_CMB, R)
    print(f"  {R_Gly:14.1f}  {circumf:14.1f}  {frac_obs:16.6f}  {frac_cmb:10.6f}  {Ok:+10.5f}")

# The cascade's natural candidate: 213 steps
R_213 = n_steps * R_Hubble
frac_obs_213 = visible_fraction_S3(d_horizon, R_213)
frac_cmb_213 = visible_fraction_S3(d_CMB, R_213)
print(f"\n  CASCADE CANDIDATE: R_curv = 213 * R_Hubble = {R_213*Mpc_to_Gly:.0f} Gly")
print(f"    Circumference = {2*pi*R_213*Mpc_to_Gly:.0f} Gly")
print(f"    Vol observable / Vol total = {frac_obs_213:.6f} = 1/{1/frac_obs_213:.0f}")
print(f"    CMB fraction = {frac_cmb_213:.6f} = 1/{1/frac_cmb_213:.0f}")


# ===================================================================
# PART 4: THE CMB LAST SCATTERING SURFACE
# ===================================================================
print("\n" + "=" * 75)
print("PART 4: THE CMB LAST SCATTERING SURFACE")
print("=" * 75)

# The CMB is light from z = 1089, emitted when the universe was ~380,000 years old
t_CMB = lookback_time(1089)
t_at_CMB = t_age - t_CMB

print(f"\n  Redshift of last scattering: z = 1089")
print(f"  Lookback time to CMB: {t_CMB:.2f} Gyr")
print(f"  Age at last scattering: {t_at_CMB*1e6:.0f} kyr ({t_at_CMB:.6f} Gyr)")
print(f"  Scale factor at CMB: a = 1/{1+1089:.0f} = {1.0/1090:.6f}")

# The PHYSICAL size of the last scattering surface
# At z=1089, the physical distance is d_CMB / (1+z)
d_CMB_physical_at_emission = d_CMB / 1090.0
print(f"\n  Comoving distance to CMB: {d_CMB:.0f} Mpc = {d_CMB_Gly:.2f} Gly")
print(f"  Physical distance at emission: {d_CMB_physical_at_emission:.1f} Mpc = {d_CMB_physical_at_emission*Mpc_to_Gly*1e3:.1f} Mly")

# The angular diameter distance to the CMB
d_A_CMB = d_CMB / (1 + 1089)
print(f"\n  Angular diameter distance to CMB: {d_A_CMB:.2f} Mpc = {d_A_CMB * Mpc_to_Gly * 1e3:.1f} Mly")

# The PHYSICAL radius of the last scattering surface TODAY
# (expanded by factor of 1090 since emission)
print(f"\n  Physical radius of last scattering surface TODAY:")
print(f"    = comoving distance = {d_CMB:.0f} Mpc = {d_CMB_Gly:.2f} Gly")

# On S^3: the CMB is a 2-sphere (S^2) at comoving distance d_CMB
# Its angular radius on S^3 is theta = d_CMB / R_curv
# Its physical radius (2-sphere) at emission was: R_curv * sin(theta) / (1+z)
print(f"\n  On S^3 (closed topology):")
print(f"  The CMB is a 2-sphere embedded in S^3.")
print(f"  Its angular size on S^3 depends on curvature:")
print(f"\n  {'R_curv (Gly)':>14s}  {'theta (rad)':>12s}  {'theta/pi':>10s}  {'Interpretation':>30s}")
print(f"  {'-'*75}")

for Ok in [-0.05, -0.01, -0.005, -0.001, -0.0001]:
    R = c_km_s / (H0 * np.sqrt(abs(Ok)))
    R_Gly = R * Mpc_to_Gly
    theta = d_CMB / R  # angle in radians
    note = ""
    if theta > pi:
        note = "See EVERYTHING (CMB wraps around)"
    elif theta > pi/2:
        note = "See >half of S^3!"
    elif theta > pi/4:
        note = "See >1/8 of S^3"
    else:
        note = f"Small cap: {theta/pi:.4f} of great circle"
    print(f"  {R_Gly:14.1f}  {theta:12.4f}  {theta/pi:10.4f}  {note:>30s}")


# ===================================================================
# PART 5: THE CASCADE'S OWN GEOMETRY
# ===================================================================
print("\n" + "=" * 75)
print("PART 5: THE CASCADE'S GEOMETRIC INTERPRETATION")
print("=" * 75)

print(f"""
In the cascade:
  - The observer sits on S^3 = boundary of B^4 at d=5
  - The de Sitter horizon area A_dS = 12*pi/Lambda ~ 10^120 Planck areas
  - Part II=III: "The cosmological constant does not describe vacuum energy;
    it describes the inverse area of the boundary the observer inhabits."

The de Sitter radius is the cascade's natural horizon:
  r_dS = c / (H_0 * sqrt(Omega_Lambda)) = {r_dS:.0f} Mpc = {r_dS_Gly:.1f} Gly

Beyond r_dS, the expansion exceeds c. Objects beyond the de Sitter
horizon are CAUSALLY DISCONNECTED from us in the future.

Key cascade distances:
  Hubble radius:       {R_Hubble_Gly:.2f} Gly
  De Sitter radius:    {r_dS_Gly:.2f} Gly
  CMB distance:        {d_CMB_Gly:.2f} Gly
  Particle horizon:    {d_horizon_Gly:.2f} Gly
  Event horizon:       {d_event * Mpc_to_Gly:.2f} Gly

The particle horizon ({d_horizon_Gly:.1f} Gly) is the maximum distance from
which light has EVER reached us. The CMB at {d_CMB_Gly:.1f} Gly is nearly
as far as this — we're seeing {d_CMB/d_horizon*100:.1f}% of the way to the
particle horizon when we look at the CMB.

The event horizon ({d_event * Mpc_to_Gly:.1f} Gly) is the maximum distance
light emitted NOW can ever reach. It's SMALLER than the particle horizon
because Lambda-dominated expansion is accelerating.
""")

# The key ratio: particle horizon / de Sitter radius
ratio = d_horizon / r_dS
print(f"  Particle horizon / de Sitter radius = {ratio:.3f}")
print(f"  CMB distance / de Sitter radius = {d_CMB / r_dS:.3f}")
print()

# ===================================================================
# PART 6: SYNTHESIS
# ===================================================================
print("=" * 75)
print("SYNTHESIS: THE CASCADE'S UNIVERSE")
print("=" * 75)

print(f"""
WHAT THE CASCADE TELLS US:

1. TOPOLOGY: S^3 (closed, finite, no boundary)
   - Like the surface of a 4-dimensional sphere
   - Go far enough in any direction and you return to where you started

2. OBSERVABLE UNIVERSE:
   - Radius: {d_horizon_Gly:.1f} Gly (particle horizon)
   - Diameter: {2*d_horizon_Gly:.1f} Gly
   - The CMB comes from {d_CMB_Gly:.1f} Gly away ({d_CMB/d_horizon*100:.1f}% to the horizon)

3. TOTAL SIZE OF S^3:
   The cascade says Omega_k ~ 0 (leading order), meaning the curvature
   radius R >> {R_Hubble_Gly:.1f} Gly. How much larger is model-dependent:

   If R = 213 * R_Hubble (cascade descent steps):
     Circumference = {2*pi*n_steps*R_Hubble_Gly:.0f} Gly
     We see 1/{1/frac_obs_213:.0f} of the total volume
     The CMB shows us 1/{1/frac_cmb_213:.0f} of the total S^3

   If R = 1/sqrt(Lambda) * l_Planck (de Sitter scale from cascade hierarchy):
     R ~ 10^60 Hubble radii
     The observable universe is ~ 10^-180 of the total
     We see an incomprehensibly tiny fraction

4. WHAT FRACTION OF THE CMB ARE WE SEEING?
   We see ALL of the CMB that is causally accessible to us.
   The CMB is a 2-sphere at comoving distance {d_CMB_Gly:.1f} Gly.

   On FLAT space: this 2-sphere surrounds us completely — we see it
   in every direction. It's the full sky (4*pi steradians).

   On S^3: the same is true, but the 2-sphere we see is a small
   fraction of the TOTAL last-scattering surface. Light from the
   rest of S^3 at z=1089 hasn't reached us yet (and in a Lambda-
   dominated universe, most of it NEVER will).

   For R = 213 * R_Hubble:
     The CMB 2-sphere subtends angle {d_CMB/R_213:.4f} rad = {d_CMB/R_213*180/pi:.2f} deg on S^3
     We see {frac_cmb_213*100:.4f}% of the total last-scattering surface

5. THE CASCADE'S DEEPEST STATEMENT:
   "The cosmological constant does not describe vacuum energy;
    it describes the inverse area of the boundary the observer inhabits."
   (Part IVb)

   A_dS = 12*pi/Lambda ~ 10^120 Planck areas
   This IS the cascade hierarchy Omega_7/Omega_217.
   The universe's size and the cosmological constant are two readings
   of the same geometric fact.
""")
