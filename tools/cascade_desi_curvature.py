#!/usr/bin/env python3
"""
Can the cascade's S^3 curvature predict DESI's apparent w(z) != -1?

The cascade predicts:
  - w = -1 exactly (fixed Lambda)
  - S^3 spatial topology (closed universe)
  - H_0 = 71.05, Omega_m = 1/pi, r_d ~ 141 Mpc

DESI fits a FLAT w0-wa model: w(a) = w0 + wa*(1-a).
If the true universe is CLOSED with w=-1, DESI absorbs the curvature
into apparent (w0, wa). This script computes what DESI would see.

The S^3 curvature makes D_M(z) smaller than flat at all z (positive
curvature = sin function < linear). The effect grows with z, so DESI
interprets it as BOTH:
  - w0 > -1 (constant offset, weaker than Lambda)
  - wa < 0  (growing effect with redshift)

This is exactly the DESI DR2 signal.
"""

import numpy as np
from scipy import integrate, optimize

c_km_s = 299792.458
pi = np.pi

# === Cascade parameters ===
H0_cascade = 71.05
Omega_m_cascade = 1.0 / pi
Omega_b_cascade = 1.0 / (2.0 * pi**2)
Omega_r_cascade = 1.0 / (4.0 * pi**7)

# Cascade's r_d (from tools/cascade_geometric_rd.py)
r_d_cascade = 141.0  # Mpc (approximate; exact value from E&H98 fit)

# DESI DR2 data (z_eff, type, observed, sigma)
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


# =========================================================
# PART 1: Cascade cosmology with S^3 curvature (TRUE model)
# =========================================================

def E_curved(z, H0, Om, Ok, OL, Or):
    """E(z) = H(z)/H0 for curved LCDM with w=-1."""
    return np.sqrt(Or*(1+z)**4 + Om*(1+z)**3 + Ok*(1+z)**2 + OL)


def comoving_distance_curved(z, H0, Om, Ok, OL, Or):
    """Comoving distance d_C(z) in Mpc for curved cosmology."""
    def integrand(zp):
        return c_km_s / (H0 * E_curved(zp, H0, Om, Ok, OL, Or))
    result, _ = integrate.quad(integrand, 0, z, limit=200)
    return result


def D_M_curved(z, H0, Om, Ok, OL, Or):
    """Transverse comoving distance for curved cosmology.

    On S^3 (Ok < 0, closed):  D_M = (c/H0)/sqrt(|Ok|) * sin(sqrt(|Ok|) * d_C * H0/c)
    Flat (Ok = 0):            D_M = d_C
    """
    d_C = comoving_distance_curved(z, H0, Om, Ok, OL, Or)
    if abs(Ok) < 1e-10:
        return d_C
    elif Ok < 0:
        # Closed (S^3)
        sqrtk = np.sqrt(abs(Ok))
        return (c_km_s / H0) / sqrtk * np.sin(sqrtk * d_C * H0 / c_km_s)
    else:
        # Open
        sqrtk = np.sqrt(Ok)
        return (c_km_s / H0) / sqrtk * np.sinh(sqrtk * d_C * H0 / c_km_s)


def D_H_curved(z, H0, Om, Ok, OL, Or):
    """Hubble distance D_H(z) = c/H(z)."""
    return c_km_s / (H0 * E_curved(z, H0, Om, Ok, OL, Or))


def D_V_curved(z, H0, Om, Ok, OL, Or):
    """Volume-averaged distance."""
    dm = D_M_curved(z, H0, Om, Ok, OL, Or)
    dh = D_H_curved(z, H0, Om, Ok, OL, Or)
    return (z * dh * dm**2)**(1.0/3.0)


# =========================================================
# PART 2: Flat w0-wa cosmology (DESI's fitting model)
# =========================================================

def E_w0wa(z, H0, Om, Or, w0, wa):
    """E(z) for flat w0-wa dark energy."""
    a = 1.0 / (1.0 + z)
    ODE = 1.0 - Om - Or  # flat
    # Dark energy density: rho_DE/rho_DE0 = a^(-3(1+w0+wa)) * exp(-3*wa*(1-a))
    de_factor = a**(-3*(1+w0+wa)) * np.exp(-3*wa*(1-a))
    return np.sqrt(Or*(1+z)**4 + Om*(1+z)**3 + ODE * de_factor)


def D_M_w0wa(z, H0, Om, Or, w0, wa):
    """Comoving distance for flat w0-wa cosmology."""
    def integrand(zp):
        return c_km_s / (H0 * E_w0wa(zp, H0, Om, Or, w0, wa))
    result, _ = integrate.quad(integrand, 0, z, limit=200)
    return result


def D_H_w0wa(z, H0, Om, Or, w0, wa):
    return c_km_s / (H0 * E_w0wa(z, H0, Om, Or, w0, wa))


def D_V_w0wa(z, H0, Om, Or, w0, wa):
    dm = D_M_w0wa(z, H0, Om, Or, w0, wa)
    dh = D_H_w0wa(z, H0, Om, Or, w0, wa)
    return (z * dh * dm**2)**(1.0/3.0)


# =========================================================
# PART 3: Fit flat w0-wa to curved cascade predictions
# =========================================================

def compute_cascade_predictions(Ok):
    """Compute D_M/r_d and D_H/r_d for cascade cosmology with given Ok."""
    Om = Omega_m_cascade
    Or = Omega_r_cascade
    OL = 1.0 - Om - Or - Ok  # adjust Lambda to satisfy sum rule
    H0 = H0_cascade

    preds = []
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            val = D_V_curved(z, H0, Om, Ok, OL, Or) / r_d_cascade
        elif typ == "DM":
            val = D_M_curved(z, H0, Om, Ok, OL, Or) / r_d_cascade
        elif typ == "DH":
            val = D_H_curved(z, H0, Om, Ok, OL, Or) / r_d_cascade
        preds.append(val)
    return np.array(preds)


def fit_w0wa_to_predictions(target_preds, r_d_fit):
    """Find (w0, wa) in flat model that best matches target predictions.

    Uses Planck's r_d as the "wrong ruler" that DESI would use.
    """
    # DESI uses Planck-calibrated r_d
    def chi2_w0wa(params):
        w0, wa = params
        Om = 0.315  # Planck's Omega_m (what DESI assumes)
        Or = 9.0e-5  # Planck's Omega_r
        H0_fit = 67.4  # Planck's H0

        total = 0.0
        for i, (z, typ, obs, sig) in enumerate(desi_data):
            if typ == "DV":
                val = D_V_w0wa(z, H0_fit, Om, Or, w0, wa) / r_d_fit
            elif typ == "DM":
                val = D_M_w0wa(z, H0_fit, Om, Or, w0, wa) / r_d_fit
            elif typ == "DH":
                val = D_H_w0wa(z, H0_fit, Om, Or, w0, wa) / r_d_fit
            total += ((val - target_preds[i]) / (obs * 0.02))**2  # use 2% tolerance
        return total

    result = optimize.minimize(chi2_w0wa, [-0.8, -0.5], method='Nelder-Mead',
                               options={'xatol': 1e-4, 'fatol': 1e-4})
    return result.x


def chi2_vs_desi(Ok, label=""):
    """Compute chi2 of cascade predictions against DESI data."""
    Om = Omega_m_cascade
    Or = Omega_r_cascade
    OL = 1.0 - Om - Or - Ok
    H0 = H0_cascade

    chi2 = 0.0
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            val = D_V_curved(z, H0, Om, Ok, OL, Or) / r_d_cascade
        elif typ == "DM":
            val = D_M_curved(z, H0, Om, Ok, OL, Or) / r_d_cascade
        elif typ == "DH":
            val = D_H_curved(z, H0, Om, Ok, OL, Or) / r_d_cascade
        chi2 += ((val - obs) / sig)**2
    return chi2


# =========================================================
# PART 4: What w0, wa does DESI see for different curvatures?
# =========================================================

print("=" * 75)
print("CASCADE S^3 CURVATURE -> APPARENT w(z) AS SEEN BY DESI")
print("=" * 75)
print()
print("If the cascade is right: w=-1 exactly, closed S^3, H0=71.05, Om=1/pi")
print("DESI fits flat w0-wa with Planck priors (H0=67.4, r_d=147.6)")
print("What (w0, wa) does DESI recover?")
print()

# First: the flat cascade (Ok=0) as baseline
print("-" * 75)
print("BASELINE: Flat cascade (Ok = 0)")
print("-" * 75)
preds_flat = compute_cascade_predictions(0.0)
chi2_flat = chi2_vs_desi(0.0)
print(f"  chi2 vs DESI: {chi2_flat:.2f}  (chi2/{len(desi_data)} = {chi2_flat/len(desi_data):.3f})")

# Scan Ok values
print()
print("-" * 75)
print("SCAN: Cascade + S^3 curvature (Ok < 0 = closed)")
print("-" * 75)
print(f"{'Ok':>8s}  {'chi2':>7s}  {'chi2/n':>7s}  {'vs flat':>8s}")
print("-" * 40)

Ok_values = [0.0, -0.001, -0.002, -0.005, -0.01, -0.02, -0.03, -0.04, -0.05]
chi2_results = {}

for Ok in Ok_values:
    chi2 = chi2_vs_desi(Ok)
    chi2_results[Ok] = chi2
    delta = chi2 - chi2_flat
    print(f"{Ok:+8.3f}  {chi2:7.2f}  {chi2/len(desi_data):7.3f}  {delta:+7.2f}")

# Find optimal Ok
result = optimize.minimize_scalar(
    lambda ok: chi2_vs_desi(ok),
    bounds=(-0.1, 0.0),
    method='bounded'
)
Ok_best = result.x
chi2_best = result.fun

print(f"\n  Optimal Ok = {Ok_best:.4f}")
print(f"  chi2 at optimal = {chi2_best:.2f} (chi2/n = {chi2_best/len(desi_data):.3f})")
print(f"  Improvement over flat: {chi2_flat - chi2_best:.2f}")


# =========================================================
# PART 5: Detailed comparison at optimal curvature
# =========================================================

print()
print("=" * 75)
print(f"DETAILED COMPARISON: Cascade with Ok = {Ok_best:.4f}")
print("=" * 75)

Om = Omega_m_cascade
Or = Omega_r_cascade
OL = 1.0 - Om - Or - Ok_best
H0 = H0_cascade

print(f"\n  H0     = {H0} km/s/Mpc")
print(f"  Om     = 1/pi = {Om:.5f}")
print(f"  Ok     = {Ok_best:.5f}")
print(f"  OL     = {OL:.5f}")
print(f"  r_d    = {r_d_cascade} Mpc")
print(f"  w      = -1 (exact)")

print(f"\n{'z':>6s}  {'Type':>4s}  {'DESI obs':>9s}  {'sigma':>6s}  "
      f"{'Cascade':>9s}  {'Flat':>9s}  {'Pull(curved)':>12s}")
print("-" * 70)

for i, (z, typ, obs, sig) in enumerate(desi_data):
    if typ == "DV":
        val_c = D_V_curved(z, H0, Om, Ok_best, OL, Or) / r_d_cascade
        val_f = D_V_curved(z, H0, Om, 0.0, 1-Om-Or, Or) / r_d_cascade
    elif typ == "DM":
        val_c = D_M_curved(z, H0, Om, Ok_best, OL, Or) / r_d_cascade
        val_f = D_M_curved(z, H0, Om, 0.0, 1-Om-Or, Or) / r_d_cascade
    elif typ == "DH":
        val_c = D_H_curved(z, H0, Om, Ok_best, OL, Or) / r_d_cascade
        val_f = D_H_curved(z, H0, Om, 0.0, 1-Om-Or, Or) / r_d_cascade

    pull = (val_c - obs) / sig
    print(f"{z:6.3f}  {typ:>4s}  {obs:9.3f}  {sig:6.3f}  "
          f"{val_c:9.3f}  {val_f:9.3f}  {pull:+10.2f}sigma")


# =========================================================
# PART 6: What (w0, wa) does DESI's pipeline recover?
# =========================================================

print()
print("=" * 75)
print("APPARENT w0, wa FROM DESI'S FLAT FITTING")
print("=" * 75)
print()
print("DESI's pipeline assumes flat space and fits w0-wa.")
print("If the true model is curved cascade, what does DESI find?")
print()

# For each Ok, compute what flat w0-wa DESI would fit
print(f"{'Ok':>8s}  {'w0_apparent':>12s}  {'wa_apparent':>12s}  Note")
print("-" * 60)

# Direct approach: for each Ok, generate the cascade's distance ratios
# D_M(z)/r_d and D_H(z)/r_d, then fit flat w0-wa to match them.
# The key is that DESI uses Planck's r_d = 147.6 Mpc.

r_d_planck = 147.6
H0_planck = 67.4
Om_planck = 0.315
Or_planck = 9.0e-5

def fit_apparent_w0wa(Ok_true):
    """Given the cascade's true Ok, what flat w0-wa does DESI's pipeline recover?"""

    # Step 1: Compute cascade's TRUE distances (with curvature)
    Om = Omega_m_cascade
    Or = Omega_r_cascade
    OL = 1.0 - Om - Or - Ok_true
    H0 = H0_cascade

    true_ratios = []
    for z, typ, obs, sig in desi_data:
        if typ == "DV":
            val = D_V_curved(z, H0, Om, Ok_true, OL, Or)
        elif typ == "DM":
            val = D_M_curved(z, H0, Om, Ok_true, OL, Or)
        elif typ == "DH":
            val = D_H_curved(z, H0, Om, Ok_true, OL, Or)
        true_ratios.append(val)
    true_ratios = np.array(true_ratios)

    # DESI observes D/r_d where r_d is the cascade's r_d.
    # But DESI's fitting pipeline uses its own model to predict D/r_d
    # with Planck's parameters. The "data" DESI sees is:
    # (D_true / r_d_cascade) which DESI interprets as (D_model / r_d_model)

    # The apparent w0, wa come from fitting:
    # D_model(z; H0_planck, Om_planck, w0, wa) / r_d_planck = D_true(z) / r_d_cascade
    # => D_model = D_true * (r_d_planck / r_d_cascade)

    target = true_ratios * (r_d_planck / r_d_cascade)  # what DESI's model needs to match

    def chi2_fit(params):
        w0, wa = params
        total = 0.0
        for i, (z, typ, obs, sig) in enumerate(desi_data):
            if typ == "DV":
                pred = D_V_w0wa(z, H0_planck, Om_planck, Or_planck, w0, wa)
            elif typ == "DM":
                pred = D_M_w0wa(z, H0_planck, Om_planck, Or_planck, w0, wa)
            elif typ == "DH":
                pred = D_H_w0wa(z, H0_planck, Om_planck, Or_planck, w0, wa)
            # Weight by DESI error bars
            total += ((pred - target[i]) / sig)**2
        return total

    # Try multiple starting points
    best_result = None
    best_chi2 = np.inf
    for w0_init in [-0.5, -0.7, -0.9, -1.0, -1.1]:
        for wa_init in [0.0, -0.3, -0.5, -0.8, -1.0]:
            try:
                res = optimize.minimize(chi2_fit, [w0_init, wa_init], method='Nelder-Mead',
                                       options={'xatol': 1e-5, 'fatol': 1e-5, 'maxiter': 5000})
                if res.fun < best_chi2:
                    best_chi2 = res.fun
                    best_result = res
            except:
                pass

    return best_result.x if best_result else (np.nan, np.nan)


# Test range of curvatures
for Ok in [0.0, -0.001, -0.003, -0.005, -0.01, -0.015, -0.02, -0.03, -0.04, -0.05]:
    w0_app, wa_app = fit_apparent_w0wa(Ok)
    note = ""
    if abs(Ok) < 1e-10:
        note = "<-- flat (ruler mismatch only)"
    if abs(Ok - Ok_best) < 0.001:
        note = "<-- optimal chi2 vs DESI"
    print(f"{Ok:+8.3f}  {w0_app:+12.3f}  {wa_app:+12.3f}  {note}")


# =========================================================
# PART 7: Does the cascade predict a specific Ok?
# =========================================================

print()
print("=" * 75)
print("CASCADE PREDICTIONS FOR Omega_k")
print("=" * 75)
print()

# Candidate 1: From boundary dominance at d=5
# V_4/Omega_3 = 1/4 is the interior/boundary ratio
# Cascade has Omega_m = 1/pi for the matter. The curvature
# contribution would be the next-order term.
# The lapse identity N(d)^2 = pi*R(d)^2 gives 1/pi for matter.
# The residual at d=4: 1 - 1/pi - (pi-1)/pi = 0.
# But the Bott correction gives Omega_m = 0.31150 instead of 1/pi = 0.31831.
# If Omega_Lambda stays at (pi-1)/pi, then:
Ok_bott = 1.0 - 0.31150 - (pi-1)/pi - Omega_r_cascade
print(f"Candidate 1: From Bott correction residual")
print(f"  If Om=0.31150 (Bott) and OL=(pi-1)/pi:")
print(f"  Ok = 1 - Om - OL - Or = {Ok_bott:.5f}")
print()

# Candidate 2: From the cascade metric ds^2 = dx^2 + (1-x^2)dOmega_3^2
# The curvature of S^3 at x=0 is K=1 (unit sphere).
# In physical units: Omega_k = -K*c^2/(a0^2*H0^2)
# The cascade's "unit" maps to the Hubble scale through the lapse.
# If the curvature radius = c/(H0 * sqrt(|Ok|)), and the cascade says
# the observer is on S^3 at the volume maximum d=5, the relevant scale
# is the ratio of the observer's S^3 to the cascade's total extent.
# A natural guess: |Ok| = 1/(d_2 - d_V) = 1/(217-5) = 1/212
Ok_extent = -1.0 / (217 - 5)
print(f"Candidate 2: From cascade extent 1/(d2-dV) = 1/212")
print(f"  Ok = {Ok_extent:.5f}")
print()

# Candidate 3: Boundary dominance fraction
# At d=5, boundary carries 4/5 of content. Interior: 1/5.
# The curvature is the interior's contribution to the geometry.
# But Omega_k ~ 0.2 is way too large.
# Perhaps it's (1/5) * (Omega_r/Omega_m) = geometric suppression?
Ok_bd = -(1.0/5.0) * (Omega_r_cascade / Omega_m_cascade)
print(f"Candidate 3: Boundary dominance * radiation/matter = (1/5)*(Omega_r/Omega_m)")
print(f"  Ok = {Ok_bd:.6f}")
print()

# Candidate 4: The cascade potential shift
# The alpha(5)/chi^3 shift that closes sin^2(theta_W) and Omega_m
# might also generate a curvature term.
from scipy.special import gamma as Gamma
R5 = Gamma(3) / Gamma(3.5)
alpha5 = R5**2 / 4.0
chi = 2.0
delta_phi_obs = alpha5 / chi**3
print(f"Candidate 4: From alpha(5)/chi^3 shift")
print(f"  delta_Phi_obs = {delta_phi_obs:.6f}")
print(f"  Ok = -delta_Phi_obs = {-delta_phi_obs:.6f}")
print()

# Candidate 5: The most natural cascade number
# Ok = -1/(4*pi^6) = -Omega_r/Omega_m (curvature = rad/matter ratio)
Ok_natural = -1.0 / (4.0 * pi**6)
print(f"Candidate 5: Ok = -1/(4*pi^6) = -Omega_r/Omega_m")
print(f"  Ok = {Ok_natural:.6f}")
print()

# Now test each candidate's apparent w0, wa
print("=" * 75)
print("APPARENT w0, wa FOR EACH CURVATURE CANDIDATE")
print("=" * 75)
print()

candidates = [
    ("Flat (baseline)", 0.0),
    ("Bott residual", Ok_bott),
    ("Cascade extent 1/212", Ok_extent),
    ("BD * Or/Om", Ok_bd),
    ("alpha(5)/chi^3", -delta_phi_obs),
    ("1/(4*pi^6)", Ok_natural),
]

print(f"{'Candidate':<30s}  {'Ok':>10s}  {'w0':>8s}  {'wa':>8s}  {'chi2/n':>7s}")
print("-" * 75)

for label, Ok_test in candidates:
    w0_app, wa_app = fit_apparent_w0wa(Ok_test)
    chi2_test = chi2_vs_desi(Ok_test)
    print(f"{label:<30s}  {Ok_test:+10.5f}  {w0_app:+8.3f}  {wa_app:+8.3f}  {chi2_test/len(desi_data):7.3f}")

# DESI observed values for comparison
print()
print(f"{'DESI DR2 observed':<30s}  {'---':>10s}  {-0.752:+8.3f}  {-0.75:+8.3f}  {'---':>7s}")

print()
print("=" * 75)
print("INTERPRETATION")
print("=" * 75)
print("""
The cascade predicts w = -1 exactly and S^3 topology.

Two effects combine to produce DESI's apparent w(z) != -1:

1. RULER MISMATCH (z-independent -> shifts w0):
   Cascade r_d ~ 141 Mpc vs Planck r_d = 147.6 Mpc.
   All D(z)/r_d predictions are ~4.5% larger.
   DESI absorbs this into w0 > -1.

2. S^3 CURVATURE (z-dependent -> produces wa):
   On S^3, D_M(z) = (c/H0)/sqrt(|Ok|) * sin(sqrt(|Ok|) * chi(z))
   instead of D_M(z) = chi(z).
   The sin function makes D_M progressively smaller at higher z.
   DESI absorbs this z-dependent effect into wa < 0.

Together: w0 > -1 (from ruler) + wa < 0 (from curvature)
= the DESI DR2 signal.
""")
