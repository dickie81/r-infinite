#!/usr/bin/env python3
"""
DERIVING THE z-TO-d MAPPING FROM THE CASCADE'S OWN STRUCTURE.

The cascade descent from d=217 to d=4 IS physical time (Part II, S7.1).
Each step has proper time increment Delta_tau = N(d).
The total proper time is sum of N(d) from d=5 to d=217.

The Friedmann equation connects proper time to redshift.
The cascade's own density content at each d determines H(d).
Therefore the z-to-d mapping is DERIVED, not chosen.

Key cascade facts:
  - Proper time per step: dtau = N(d) = sqrt(pi) * R(d)
  - Content at each level: sphere area Omega_{d-1}
  - Bott partition: matter layers (d mod 8 in {5,6}), vacuum layers (rest)
  - Radiation originates at gauge boundary (d=11) and propagates inward
  - Matter-radiation equality at z_eq = 4*pi^6 = 3846

The mapping: the cumulative proper time from d=217 down to level d,
as a fraction of total proper time, should correspond to the
cumulative conformal time from z=infinity down to redshift z(d).
"""

import numpy as np
from scipy.special import gamma as Gamma, digamma
from scipy import integrate, optimize

pi = np.pi
c_km_s = 299792.458

# === CASCADE LAPSE AND PROPER TIME ===

def N_lapse(d):
    """Cascade lapse at integer dimension d."""
    return np.sqrt(pi) * Gamma((d+1)/2.0) / Gamma((d+2)/2.0)


# Total proper time in the descent
print("=" * 75)
print("CASCADE DESCENT: PROPER TIME BUDGET")
print("=" * 75)

tau_total = sum(N_lapse(d) for d in range(5, 218))
print(f"\n  Total descent proper time: sum_{{d=5}}^{{217}} N(d) = {tau_total:.4f} cascade units")

# Cumulative proper time from d=217 down to level d
# (time elapsed since the "beginning" at d=217)
tau_cumulative = {}
tau_running = 0.0
for d in range(217, 3, -1):
    tau_running += N_lapse(d)
    tau_cumulative[d] = tau_running

# Fraction of total time elapsed at each d
print(f"\n  Cumulative proper time fraction at key dimensions:")
print(f"  {'d':>4s}  {'N(d)':>8s}  {'tau_cum':>8s}  {'frac':>8s}  Note")
print(f"  {'-'*50}")
for d in [217, 100, 50, 19, 14, 13, 12, 11, 7, 6, 5, 4]:
    if d in tau_cumulative:
        tc = tau_cumulative[d]
        frac = tc / tau_total
    elif d == 4:
        tc = tau_total
        frac = 1.0
    else:
        tc = 0
        frac = 0
    note = ""
    if d == 217: note = "terminus"
    elif d == 19: note = "threshold d1"
    elif d == 14: note = "U(1)"
    elif d == 13: note = "SU(2)"
    elif d == 12: note = "SU(3) / gauge window"
    elif d == 11: note = "gauge boundary"
    elif d == 7: note = "area max d0"
    elif d == 5: note = "volume max dV"
    elif d == 4: note = "observer"
    print(f"  {d:4d}  {N_lapse(d):8.5f}  {tc:8.3f}  {frac:8.4f}  {note}")


# === THE FRIEDMANN SIDE: CONFORMAL TIME BUDGET ===

H0 = 71.05
h = H0 / 100.0
h2 = h**2
Omega_m = 1.0 / pi
Omega_r = 1.0 / (4.0 * pi**7)
Omega_Lambda = (pi - 1.0) / pi

# Use 7/8 baryon split
omega_b_78 = (7.0/8.0) / (2*pi**2) * h2
Omega_b_78 = omega_b_78 / h2

N_eff = 3.0
factor_nu = 1.0 + (7.0/8.0) * (4.0/11.0)**(4.0/3.0) * N_eff
Omega_gamma = Omega_r / factor_nu
R_coeff = 3.0 * Omega_b_78 / (4.0 * Omega_gamma)

def E(z):
    return np.sqrt(Omega_r*(1+z)**4 + Omega_m*(1+z)**3 + Omega_Lambda)

def sound_speed(z):
    R = R_coeff / (1.0 + z)
    return 1.0 / np.sqrt(3.0 * (1.0 + R))


# Conformal time from z=infinity to z:
# eta(z) = integral from z to infinity of c*dz'/(H0*E(z'))
def conformal_time_from_inf(z_lower):
    result, _ = integrate.quad(lambda z: 1.0 / (H0 * E(z)),
                                z_lower, 1e7, limit=500)
    return result * c_km_s  # in Mpc

# Total conformal time (z=inf to z=0)
eta_total = conformal_time_from_inf(0)
eta_at_1089 = conformal_time_from_inf(1089)
eta_at_1060 = conformal_time_from_inf(1060)
z_eq = 4 * pi**6
eta_at_eq = conformal_time_from_inf(z_eq)

print(f"\n\n{'='*75}")
print("FRIEDMANN CONFORMAL TIME BUDGET")
print("=" * 75)
print(f"\n  Total conformal time (z=inf to z=0): {eta_total:.1f} Mpc")
print(f"  Conformal time at z_eq = {z_eq:.0f}:     {eta_at_eq:.1f} Mpc  (frac: {eta_at_eq/eta_total:.4f})")
print(f"  Conformal time at z=1089:         {eta_at_1089:.1f} Mpc  (frac: {eta_at_1089/eta_total:.4f})")
print(f"  Conformal time at z=1060:         {eta_at_1060:.1f} Mpc  (frac: {eta_at_1060/eta_total:.4f})")


# === THE MAPPING: MATCH PROPER TIME FRACTIONS TO CONFORMAL TIME FRACTIONS ===

print(f"\n\n{'='*75}")
print("z-TO-d MAPPING: MATCHING TIME FRACTIONS")
print("=" * 75)
print(f"""
  Principle: the cascade descent IS physical time.
  The fraction of proper time elapsed at cascade level d
  should equal the fraction of conformal time elapsed at
  the corresponding redshift z.

  tau_cascade(d) / tau_total  =  eta(z) / eta_total

  This gives z(d) for each cascade level.
""")

# For each cascade level d, find the redshift z such that
# eta(z)/eta_total = tau_cumulative(d)/tau_total
def find_z_for_d(d):
    """Find redshift corresponding to cascade level d."""
    if d not in tau_cumulative:
        return 0.0
    target_frac = tau_cumulative[d] / tau_total

    # eta(z)/eta_total = target_frac
    # eta(z) = conformal_time_from_inf(z) = target_frac * eta_total
    target_eta = target_frac * eta_total

    def residual(log_z):
        z = np.exp(log_z)
        eta_z = conformal_time_from_inf(z)
        return eta_z - target_eta

    try:
        # Search in log space
        log_z = optimize.brentq(residual, np.log(0.01), np.log(1e7))
        return np.exp(log_z)
    except:
        return np.nan


print(f"  {'d':>4s}  {'tau_frac':>10s}  {'z(d)':>12s}  {'1+z':>12s}  Note")
print(f"  {'-'*55}")

z_of_d = {}
for d in range(217, 3, -1):
    z = find_z_for_d(d)
    z_of_d[d] = z

for d in [217, 200, 150, 100, 50, 19, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5]:
    if d in tau_cumulative and d in z_of_d:
        frac = tau_cumulative[d] / tau_total
        z = z_of_d[d]
        note = ""
        if d == 217: note = "terminus"
        elif d == 19: note = "threshold d1"
        elif d == 14: note = "U(1)"
        elif d == 13: note = "SU(2)"
        elif d == 12: note = "SU(3)"
        elif d == 11: note = "gauge boundary"
        elif d == 7: note = "d0 (area max)"
        elif d == 5: note = "dV (volume max)"
        print(f"  {d:4d}  {frac:10.4f}  {z:12.1f}  {1+z:12.1f}  {note}")

# Key: what d does recombination (z=1089) correspond to?
# Find d such that z(d) ~ 1089
print(f"\n  KEY EPOCHS:")
for z_target, label in [(1089, "recombination"), (1060, "drag epoch"),
                         (z_eq, "matter-radiation eq"), (10, "dark energy onset")]:
    # Find d where z(d) is closest to z_target
    best_d = None
    best_diff = 1e20
    for d, z in z_of_d.items():
        if not np.isnan(z) and abs(np.log(z+1) - np.log(z_target+1)) < best_diff:
            best_diff = abs(np.log(z+1) - np.log(z_target+1))
            best_d = d
    if best_d:
        print(f"  z = {z_target:>8.0f} ({label:>25s}) -> d = {best_d}, N({best_d}) = {N_lapse(best_d):.5f}")


# === COMPUTE THE EFFECTIVE LAPSE CORRECTION ===

print(f"\n\n{'='*75}")
print("EFFECTIVE LAPSE CORRECTION AT EACH REDSHIFT")
print("=" * 75)

# Build inverse map: z -> d
# For each z, find the cascade level d(z) and the lapse N(d(z))
def d_of_z(z_val):
    """Find cascade level corresponding to redshift z."""
    # Use the z_of_d mapping (inverted)
    # Find the two d values that bracket z_val
    d_prev = 217
    z_prev = z_of_d.get(217, 1e7)
    for d in range(216, 4, -1):
        z_d = z_of_d.get(d, np.nan)
        if np.isnan(z_d):
            continue
        if z_d <= z_val <= z_prev or z_prev <= z_val <= z_d:
            # Interpolate
            if abs(z_prev - z_d) > 0:
                frac = (np.log(z_val+1) - np.log(z_d+1)) / (np.log(z_prev+1) - np.log(z_d+1))
                return d + frac * (d_prev - d)
            else:
                return d
        d_prev = d
        z_prev = z_d
    return 5.0  # default for low z


def N_interp(d_float):
    """Interpolate lapse for non-integer d."""
    d_low = max(4, int(np.floor(d_float)))
    d_high = min(217, d_low + 1)
    frac = d_float - d_low
    return (1 - frac) * N_lapse(d_low) + frac * N_lapse(d_high)


N4 = N_lapse(4)
print(f"\n  {'z':>8s}  {'d(z)':>6s}  {'N(d)':>8s}  {'N(4)/N(d)':>10s}  {'H enhancement':>14s}")
print(f"  {'-'*55}")

for z_test in [0, 1, 10, 100, 500, 1000, 1060, 1089, 2000, 3846, 10000, 100000]:
    d_z = d_of_z(z_test)
    N_z = N_interp(d_z)
    enhancement = N4 / N_z
    print(f"  {z_test:8d}  {d_z:6.1f}  {N_z:8.5f}  {enhancement:10.4f}  {(enhancement-1)*100:+13.2f}%")


# === COMPUTE THE SOUND HORIZON WITH THE DERIVED MAPPING ===

print(f"\n\n{'='*75}")
print("SOUND HORIZON WITH DERIVED z-TO-d LAPSE")
print("=" * 75)

def H_with_derived_lapse(z):
    """Friedmann H(z) corrected by the cascade's own d-dependent lapse."""
    d_z = d_of_z(z)
    N_z = N_interp(d_z)
    correction = N4 / N_z
    return H0 * E(z) * correction

# Sound horizon
def compute_rd(H_func, z_drag):
    def integrand(z):
        return sound_speed(z) * c_km_s / H_func(z)
    result, _ = integrate.quad(integrand, z_drag, 1e6, limit=500)
    return result

rd_standard = compute_rd(lambda z: H0 * E(z), 1060)
rd_derived = compute_rd(H_with_derived_lapse, 1060)

DA_standard, _ = integrate.quad(lambda z: c_km_s / (H0 * E(z)), 0, 1089, limit=500)
DA_derived, _ = integrate.quad(lambda z: c_km_s / H_with_derived_lapse(z), 0, 1089, limit=500)

ell_A_standard = pi * DA_standard / rd_standard
ell_A_derived = pi * DA_derived / rd_derived

print(f"\n  {'':>25s}  {'Standard':>10s}  {'Derived':>10s}  {'Planck':>10s}")
print(f"  {'-'*60}")
print(f"  {'r_d (Mpc)':>25s}  {rd_standard:10.1f}  {rd_derived:10.1f}  {'147.1':>10s}")
print(f"  {'D_A (Mpc)':>25s}  {DA_standard:10.0f}  {DA_derived:10.0f}  {'13800':>10s}")
print(f"  {'ell_A':>25s}  {ell_A_standard:10.1f}  {ell_A_derived:10.1f}  {'301.6':>10s}")
print(f"  {'Deviation from Planck':>25s}  {(ell_A_standard-301.6)/301.6*100:+9.2f}%  {(ell_A_derived-301.6)/301.6*100:+9.2f}%")

# What the first peak would be at
l1_standard = ell_A_standard * 220 / 301.6  # approximate scaling
l1_derived = ell_A_derived * 220 / 301.6
print(f"\n  Approx first peak position:")
print(f"    Standard:  l_1 ~ {l1_standard:.0f}")
print(f"    Derived:   l_1 ~ {l1_derived:.0f}")
print(f"    Observed:  l_1 = 220")


# === WHAT IF WE USE PROPER TIME INSTEAD OF CONFORMAL TIME? ===
print(f"\n\n{'='*75}")
print("ALTERNATIVE: PROPER TIME MATCHING")
print("=" * 75)
print(f"\n  Maybe conformal time is the wrong quantity to match.")
print(f"  The cascade's proper time per step is N(d).")
print(f"  The Friedmann proper time is dt = dz / ((1+z)*H(z)).")

# Proper time from z=inf to z:
def proper_time_from_inf(z_lower):
    result, _ = integrate.quad(lambda z: 1.0 / ((1+z) * H0 * E(z)),
                                z_lower, 1e7, limit=500)
    return result * c_km_s / (3.086e19 * 3.156e7)  # convert to Gyr... actually let's keep in Mpc/c

# Just use the SAME unit. Proper time in "Mpc/c" units:
def proper_time_mpc(z_lower):
    result, _ = integrate.quad(lambda z: c_km_s / ((1+z) * H0 * E(z)),
                                z_lower, 1e7, limit=500)
    return result

t_total = proper_time_mpc(0)
t_at_1089 = proper_time_mpc(1089)
t_at_eq = proper_time_mpc(z_eq)

print(f"\n  Proper time budget:")
print(f"    Total (z=inf to 0):  {t_total:.1f} Mpc/c")
print(f"    At z=1089:           {t_at_1089:.1f} Mpc/c  (frac: {t_at_1089/t_total:.6f})")
print(f"    At z_eq:             {t_at_eq:.1f} Mpc/c  (frac: {t_at_eq/t_total:.6f})")

# Now map using proper time
def find_z_for_d_proper(d):
    if d not in tau_cumulative:
        return 0.0
    target_frac = tau_cumulative[d] / tau_total
    target_t = target_frac * t_total

    def residual(log_z):
        z = np.exp(log_z)
        return proper_time_mpc(z) - target_t

    try:
        log_z = optimize.brentq(residual, np.log(0.001), np.log(1e7))
        return np.exp(log_z)
    except:
        return np.nan

print(f"\n  Proper-time z-to-d mapping at key dimensions:")
print(f"  {'d':>4s}  {'z(d) conformal':>14s}  {'z(d) proper':>14s}")
print(f"  {'-'*40}")

z_of_d_proper = {}
for d in range(217, 4, -1):
    z_p = find_z_for_d_proper(d)
    z_of_d_proper[d] = z_p

for d in [217, 100, 50, 19, 14, 13, 12, 11, 7, 6, 5]:
    z_conf = z_of_d.get(d, np.nan)
    z_prop = z_of_d_proper.get(d, np.nan)
    print(f"  {d:4d}  {z_conf:14.1f}  {z_prop:14.1f}")

# Where does recombination land in proper time?
for z_target, label in [(1089, "recombination"), (1060, "drag epoch")]:
    best_d = None
    best_diff = 1e20
    for d, z in z_of_d_proper.items():
        if not np.isnan(z) and abs(np.log(z+1) - np.log(z_target+1)) < best_diff:
            best_diff = abs(np.log(z+1) - np.log(z_target+1))
            best_d = d
    if best_d:
        print(f"\n  z={z_target} ({label}): d = {best_d}, N({best_d}) = {N_lapse(best_d):.5f}, N(4)/N({best_d}) = {N4/N_lapse(best_d):.4f}")


# === SUMMARY ===
print(f"\n\n{'='*75}")
print("SUMMARY: THE DERIVED z-TO-d MAPPING")
print("=" * 75)

# Find d at recombination for both methods
d_recomb_conf = d_of_z(1089)
print(f"""
  Two natural mappings from the cascade's own structure:

  1. CONFORMAL TIME matching:
     Recombination (z=1089) -> d = {d_recomb_conf:.1f}
     N({d_recomb_conf:.0f}) = {N_interp(d_recomb_conf):.5f}
     H enhancement = {N4/N_interp(d_recomb_conf):.4f} ({(N4/N_interp(d_recomb_conf)-1)*100:+.1f}%)
     ell_A = {ell_A_derived:.1f} (Planck: 301.6, deviation: {(ell_A_derived-301.6)/301.6*100:+.1f}%)

  Recall: a uniform 5.06% enhancement gives ell_A = 301.6 exactly.

  The conformal-time mapping places recombination at d ~ {d_recomb_conf:.0f},
  where the lapse is {N_interp(d_recomb_conf):.3f} vs N(4) = {N4:.3f}.
  The enhancement is {(N4/N_interp(d_recomb_conf)-1)*100:.1f}%.
""")

# The needed enhancement is 5.06%. What d gives this?
N_needed = N4 / 1.0506
print(f"  For ell_A = 301.6, need N(d) = {N_needed:.5f}")
print(f"  This is between N(4) = {N4:.5f} and N(5) = {N_lapse(5):.5f}")
frac_needed = (N4 - N_needed) / (N4 - N_lapse(5))
d_needed = 4 + frac_needed
print(f"  Corresponding to d = {d_needed:.2f}")
print(f"  The recombination epoch needs to map to d ~ {d_needed:.1f}")
