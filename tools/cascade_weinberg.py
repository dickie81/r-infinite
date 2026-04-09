#!/usr/bin/env python3
"""
Compute the Weinberg angle from the cascade's own descent mechanism,
without borrowing standard RG running.

The cascade gives bare gauge couplings at the gauge window {12, 13, 14}:
    SU(3) at d=12 (Weyl,  phase +1, mod 8 = 4)
    SU(2) at d=13 (Dirac, phase  i, mod 8 = 5)  ← hairy ball obstruction
    U(1)  at d=14 (Weyl,  phase -1, mod 8 = 6)

Each descends to the observer at d=4 via:
    α_obs(d) = α(d) × exp(Φ(d→4)) × (Bott modification)

where α(d) = N(d)²/(4π), Φ(d→4) = Σ_{d'=5}^{d} p(d'), and the Bott
modification depends on whether the descent path crosses Dirac layers
(d mod 8 = 5) where the topological obstruction (2√π)^{-1} applies.

We test several scenarios for the Bott modification.
"""

import math
from math import pi, sqrt, exp, log, gamma

def digamma(x):
    """Digamma function using recurrence + asymptotic series."""
    result = 0.0
    while x < 6:
        result -= 1.0 / x
        x += 1
    # Asymptotic expansion
    result += log(x) - 1.0/(2*x)
    inv_x2 = 1.0 / (x * x)
    result -= inv_x2 * (1.0/12 - inv_x2 * (1.0/120 - inv_x2 * (1.0/252)))
    return result

# ───────────────────────────────────────────────────────────────────────
# Cascade primitives
# ───────────────────────────────────────────────────────────────────────

def R(d):
    """R(d) = Γ((d+1)/2) / Γ((d+2)/2)"""
    return gamma((d + 1) / 2) / gamma((d + 2) / 2)

def N(d):
    """Lapse function N(d) = √π · R(d)"""
    return sqrt(pi) * R(d)

def alpha_bare(d):
    """Bare gauge coupling at layer d: α(d) = N(d)² / (4π)"""
    return N(d)**2 / (4 * pi)

def p(d):
    """Sphere-area decay rate at layer d."""
    return -0.5 * log(pi) + 0.5 * digamma((d + 1) / 2)

def Phi(d_gauge, d_obs=4):
    """Cascade potential from observer to gauge layer."""
    return sum(p(d) for d in range(d_obs + 1, d_gauge + 1))

def is_dirac_layer(d):
    """Dirac layer: d mod 8 == 5 (complex Dirac spinor in Cl(1,d-1))."""
    return d % 8 == 5

def n_dirac_crossed(d_start, d_end=4):
    """Number of Dirac layers in [d_end+1, d_start]."""
    return sum(1 for d in range(d_end + 1, d_start + 1) if is_dirac_layer(d))

# ───────────────────────────────────────────────────────────────────────
# Display the cascade primitives
# ───────────────────────────────────────────────────────────────────────

print("=" * 72)
print("CASCADE GAUGE COUPLINGS — BARE VALUES AT THE GAUGE WINDOW")
print("=" * 72)
print(f"\n{'Layer':<8}{'N(d)':<14}{'α(d)':<14}{'1/α(d)':<14}{'Bott':<10}{'phase':<8}")
print("-" * 68)

for d, name, bott in [(12, 'SU(3)', 'Weyl'), (13, 'SU(2)', 'Dirac'), (14, 'U(1) ', 'Weyl')]:
    Nd = N(d)
    a = alpha_bare(d)
    phase_idx = (d - 4) % 4
    phase = ['+1', 'i', '-1', '-i'][phase_idx]
    print(f"{d} {name:<6}{Nd:<14.6f}{a:<14.6f}{1/a:<14.4f}{bott:<10}{phase:<8}")

# ───────────────────────────────────────────────────────────────────────
# Cascade descent factors
# ───────────────────────────────────────────────────────────────────────

print(f"\n\n{'Layer':<8}{'Φ(d→4)':<14}{'exp(Φ)':<14}{'Dirac crossed':<16}")
print("-" * 52)
for d in [12, 13, 14]:
    phi = Phi(d)
    nd = n_dirac_crossed(d)
    crossed = [d for d in range(5, d + 1) if is_dirac_layer(d)]
    print(f"d={d:<6}{phi:<14.6f}{exp(phi):<14.6f}{str(crossed):<16}")

# ───────────────────────────────────────────────────────────────────────
# Scenarios for Bott modification
# ───────────────────────────────────────────────────────────────────────

print("\n\n" + "=" * 72)
print("SCENARIOS FOR sin²θ_W FROM CASCADE DESCENT")
print("=" * 72)

# sin²θ_W = (3/5)α₁_GUT / ((3/5)α₁_GUT + α₂)
# At GUT with α₁ = α₂: sin²θ_W = (3/5)/(3/5+1) = 3/8 ✓
GUT_NORM = 3.0 / 5.0
TOPO_FACTOR = 1.0 / (2 * sqrt(pi))  # 1/(2√π) ≈ 0.2821

# Bare couplings at the gauge window
a_3 = alpha_bare(12)  # SU(3)
a_2 = alpha_bare(13)  # SU(2)
a_1 = alpha_bare(14)  # U(1)

# Cascade descent factors
desc_3 = exp(Phi(12))
desc_2 = exp(Phi(13))
desc_1 = exp(Phi(14))


def weinberg(a1_obs, a2_obs):
    """sin²θ_W = (5/3)α₁ / ((5/3)α₁ + α₂)"""
    return (GUT_NORM * a1_obs) / (GUT_NORM * a1_obs + a2_obs)


def report(label, a1_obs, a2_obs, a3_obs):
    sw2 = weinberg(a1_obs, a2_obs)
    print(f"\n{label}")
    print(f"  α_3 = {a3_obs:.6f}  (1/α = {1/a3_obs:.4f})")
    print(f"  α_2 = {a2_obs:.6f}  (1/α = {1/a2_obs:.4f})")
    print(f"  α_1 = {a1_obs:.6f}  (1/α = {1/a1_obs:.4f})")
    print(f"  sin²θ_W = {sw2:.6f}  (observed: 0.2312, deviation: {(sw2-0.2312)/0.2312*100:+.2f}%)")


# Scenario 1: No Bott modification (just cascade descent)
print("\n--- Scenario 1: Pure cascade descent (leading order) ---")
report("Just exp(Φ):",
       a_1 * desc_1,
       a_2 * desc_2,
       a_3 * desc_3)

# Scenario 2: 1/(2√π) per Dirac layer crossed
print("\n--- Scenario 2: Topological factor (2√π)⁻¹ per Dirac layer crossed ---")
nd_3 = n_dirac_crossed(12)  # 1: just d=5
nd_2 = n_dirac_crossed(13)  # 2: d=5, d=13
nd_1 = n_dirac_crossed(14)  # 2: d=5, d=13
print(f"Dirac counts: SU(3)={nd_3}, SU(2)={nd_2}, U(1)={nd_1}")
report("With (2√π)^(-n_D):",
       a_1 * desc_1 * TOPO_FACTOR**nd_1,
       a_2 * desc_2 * TOPO_FACTOR**nd_2,
       a_3 * desc_3 * TOPO_FACTOR**nd_3)

# Scenario 3: 1/(2√π) only at the OWN layer if it's a Dirac layer
# (SU(2) at d=13 is the only one whose own layer is Dirac)
print("\n--- Scenario 3: Own-layer obstruction only ---")
own_3 = TOPO_FACTOR if is_dirac_layer(12) else 1.0
own_2 = TOPO_FACTOR if is_dirac_layer(13) else 1.0
own_1 = TOPO_FACTOR if is_dirac_layer(14) else 1.0
print(f"Own-layer obstructions: SU(3)={own_3:.4f}, SU(2)={own_2:.4f}, U(1)={own_1:.4f}")
report("With own-layer (2√π)^(-1) where Dirac:",
       a_1 * desc_1 * own_1,
       a_2 * desc_2 * own_2,
       a_3 * desc_3 * own_3)

# Scenario 4: 1/2 (chirality only, no quarter-turn) at SU(2) layer
print("\n--- Scenario 4: SU(2) gets only the chirality factor (1/2) ---")
report("SU(2) × 1/2:",
       a_1 * desc_1,
       a_2 * desc_2 * 0.5,
       a_3 * desc_3)

# Scenario 5: Test the inverted formula — SU(2) AMPLIFIED at Dirac layer
# (gauge coupling sees the obstruction as a 1/g² enhancement, since
#  it's the inverse coupling that runs)
print("\n--- Scenario 5: Inverse coupling enhancement at Dirac layer ---")
# 1/α grows by 2√π at the Dirac layer
report("1/α_2 × 2√π enhancement:",
       a_1 * desc_1,
       1.0 / (1.0/(a_2 * desc_2) * 2 * sqrt(pi)),
       a_3 * desc_3)

# Scenario 6: Multi-step Dirac obstruction (full crossing)
print("\n--- Scenario 6: 1/α_2 × (2√π)^n_D where n_D counts Dirac layers ---")
print("    (matching the fermion mass formula structure)")
report("Inverse couplings enhanced by (2√π)^n_D:",
       1.0 / (1.0/(a_1 * desc_1) * (2 * sqrt(pi))**nd_1),
       1.0 / (1.0/(a_2 * desc_2) * (2 * sqrt(pi))**nd_2),
       1.0 / (1.0/(a_3 * desc_3) * (2 * sqrt(pi))**nd_3))

# Scenario 7: Majorana-gap projection
# Between the gauge window {12,13,14} and the spacetime window {4,5,6}
# lie 5 Majorana layers d=7,8,9,10,11. A complex propagator passing
# through a real layer gets projected onto the real subspace.
# The projection of e^{iθ} onto reals is cos(θ).
# At each Majorana layer, the propagator acquires a phase i^k.
# The cumulative effect differs for couplings starting at different layers.

print("\n--- Scenario 7: Majorana-gap phase projection ---")
print("Each gauge coupling accumulates phase i^(d-d_obs) per descent step.")
print("At Majorana layers (d=7..11), the complex propagator must project")
print("onto a real spinor structure. The projection factor is |cos(phase)|.")
print()

def majorana_factor(d_start, d_obs=4):
    """Cumulative phase projection through Majorana layers in [7,11]."""
    factor = 1.0
    for d in range(d_obs + 1, d_start + 1):
        if 7 <= d <= 11:  # Majorana layer
            phase = (d - d_obs) * pi / 2  # accumulated phase at this layer
            proj = abs(math.cos(phase))
            factor *= max(proj, 1e-12)  # avoid log(0)
    return factor

mf_3 = majorana_factor(12)
mf_2 = majorana_factor(13)
mf_1 = majorana_factor(14)
print(f"Majorana projections: SU(3)={mf_3:.4f}, SU(2)={mf_2:.4f}, U(1)={mf_1:.4f}")

# (this will be zero for any gauge coupling whose phase is purely imaginary
#  at any Majorana step, so we need a smoother model)

# Smoother: use the propagator's "real component fraction" at each step
def smooth_majorana_factor(d_start, d_obs=4):
    """Average |Re(e^{iφ})| over the Majorana gap, weighted by N(d)."""
    weights = []
    for d in range(d_obs + 1, d_start + 1):
        if 7 <= d <= 11:
            phase = (d - d_obs) * pi / 2
            # The fraction of amplitude that survives = (1 + |cos(phase)|)/2
            # This is the fraction of the spinor that aligns with the real layer
            survival = (1.0 + abs(math.cos(phase))) / 2.0
            weights.append(survival)
    if not weights:
        return 1.0
    prod = 1.0
    for w in weights:
        prod *= w
    return prod

smf_3 = smooth_majorana_factor(12)
smf_2 = smooth_majorana_factor(13)
smf_1 = smooth_majorana_factor(14)
print(f"\nSmoother survival: SU(3)={smf_3:.4f}, SU(2)={smf_2:.4f}, U(1)={smf_1:.4f}")

report("With smooth Majorana survival factors:",
       a_1 * desc_1 * smf_1,
       a_2 * desc_2 * smf_2,
       a_3 * desc_3 * smf_3)


# Scenario 7b: U(1) at d=14 must cross the Dirac layer at d=13 during descent.
# SU(2) sits AT d=13 (its own layer; the "obstruction" IS the symmetry breaking,
# not an additional propagator factor). So only U(1) sees the topological factor.
print("\n--- Scenario 7b: U(1) crosses Dirac at d=13, SU(2) sits at it ---")
print("Only U(1) gets the (2√π)^(-1) topological factor.")
report("U(1) × 1/(2√π), SU(2) unmodified:",
       a_1 * desc_1 * TOPO_FACTOR,
       a_2 * desc_2,
       a_3 * desc_3)

# What factor on α_1 alone gives sin²θ_W = 0.2312?
# (3/5) α_1 X / ((3/5) α_1 X + α_2) = 0.2312
# (3/5) α_1 X (1 - 0.2312) = 0.2312 α_2
# X = 0.2312 α_2 / ((3/5) α_1 × 0.7688)
X_needed = 0.2312 * (a_2 * desc_2) / ((3/5) * (a_1 * desc_1) * 0.7688)
print(f"\nFactor on α_1 needed for sin²θ_W = 0.2312: X = {X_needed:.6f}")
print(f"  1/X = {1/X_needed:.6f}")
print(f"  Compare: 1/(2√π) = {1/(2*sqrt(pi)):.6f}")
print(f"  Compare: 1/π     = {1/pi:.6f}")
print(f"  Compare: 1/e     = {1/math.e:.6f}")
print(f"  Compare: 2/π     = {2/pi:.6f}")
print(f"  Compare: 1/√(2π) = {1/sqrt(2*pi):.6f}")

# Scenario 8: Maybe sin²θ_W comes from the cascade DIRECTLY without descent
# i.e., the Weinberg angle is a property of the gauge window itself
print("\n--- Scenario 8: Weinberg angle from bare cascade quantities ---")
print("Try various cascade ratios that could give sin²θ_W ≈ 0.2312")
print()

# Bare couplings, GUT formula
sw2_bare = (GUT_NORM * a_1) / (GUT_NORM * a_1 + a_2)
print(f"  Bare with (3/5)α(14)/(...+α(13)): {sw2_bare:.6f}")

# N(14)²/(N(13)²+N(14)²) with no normalization
sw2_n = N(14)**2 / (N(13)**2 + N(14)**2)
print(f"  N(14)²/(N(13)²+N(14)²): {sw2_n:.6f}")

# (3/5)N(14)²/((3/5)N(14)²+N(13)²)
sw2_n_gut = (3/5)*N(14)**2 / ((3/5)*N(14)**2 + N(13)**2)
print(f"  (3/5)N(14)²/(...+N(13)²): {sw2_n_gut:.6f}")

# 3/13 (number of generators / SU(2) layer)
print(f"  3/13 (heuristic): {3/13:.6f}")

# 1/(1 + N(13)/N(14))
sw2_lapse = 1.0 / (1.0 + N(13)**2/N(14)**2)
print(f"  1/(1+(N13/N14)²): {sw2_lapse:.6f}")


# ───────────────────────────────────────────────────────────────────────
# Direct GUT-scale check (no descent at all)
# ───────────────────────────────────────────────────────────────────────

print("\n\n" + "=" * 72)
print("GUT-SCALE CHECK (couplings at the gauge window directly)")
print("=" * 72)
print("\nAt the gauge window with no descent, the SU(5) formula gives:")
print("  sin²θ_W^GUT = 3/8 = 0.375 (if all couplings equal)")
print()
sw2_gut = weinberg(a_1, a_2)
print(f"With cascade's unequal bare couplings:")
print(f"  α_1 = {a_1:.6f}, α_2 = {a_2:.6f}")
print(f"  sin²θ_W^GUT(cascade) = {sw2_gut:.6f}")

# ───────────────────────────────────────────────────────────────────────
# Inverted descent: maybe 1/α descends, not α
# ───────────────────────────────────────────────────────────────────────

print("\n\n" + "=" * 72)
print("INVERTED DESCENT: 1/α grows additively")
print("=" * 72)
print("\nIn standard RG, 1/α(μ) - 1/α(M) = (b/2π) ln(M/μ)")
print("If the cascade replaces (b/2π)ln(M/μ) with the cascade potential Φ,")
print("then 1/α_obs = 1/α_GUT + Φ × (something gauge-dependent)")
print()

# Try: 1/α_obs - 1/α_GUT = Φ(d→4) (the cascade potential traversed)
print("Test: 1/α_obs = 1/α(d) + Φ(d→4)  (additive in cascade potential)")
inv_3 = 1/a_3 + Phi(12)
inv_2 = 1/a_2 + Phi(13)
inv_1 = 1/a_1 + Phi(14)
print(f"  1/α_3 = {inv_3:.4f}  (observed at M_Z: ~8.5)")
print(f"  1/α_2 = {inv_2:.4f}  (observed at M_Z: ~29.6)")
print(f"  1/α_1 = {inv_1:.4f}  (observed at M_Z: ~59)")
sw2 = (GUT_NORM/inv_1) / ((GUT_NORM/inv_1) + (1/inv_2))
print(f"  sin²θ_W = {sw2:.6f}")
