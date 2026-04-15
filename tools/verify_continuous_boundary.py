#!/usr/bin/env python3
"""
High-precision verification of Part 0's cascade invariant under
various boundary-labeling conventions.

Tests the conjecture (from conversation) that I_P0 / I_cont = 4 exactly,
where I_cont uses the continuous boundary crossings of p(d).

Also diagnoses an apparent numerical error in Part 0 at p(20).
"""

import mpmath

mpmath.mp.dps = 50


def p(d):
    """Decay rate p(d) = (1/2) psi((d+1)/2) - (1/2) ln(pi)."""
    x = (mpmath.mpf(d) + 1) / 2
    return (mpmath.digamma(x) - mpmath.log(mpmath.pi)) / 2


def Omega(d):
    """Sphere area: Omega_d = 2 * pi^((d+1)/2) / Gamma((d+1)/2)."""
    x = (mpmath.mpf(d) + 1) / 2
    return 2 * mpmath.power(mpmath.pi, x) / mpmath.gamma(x)


def V(d):
    """Ball volume: V_d = pi^(d/2) / Gamma(d/2 + 1)."""
    return mpmath.power(mpmath.pi, mpmath.mpf(d) / 2) / mpmath.gamma(mpmath.mpf(d) / 2 + 1)


# Threshold constants
c0 = mpmath.mpf(0)
c1 = mpmath.log(mpmath.pi) / 2           # (1/2) ln pi
c2 = mpmath.sqrt(mpmath.pi)              # sqrt pi

print("=" * 72)
print("Part 0 cascade invariant: high-precision boundary analysis")
print("=" * 72)

# ============================================================================
# SECTION 1: Check Part 0's discrete verification of p(19), p(20), p(217), p(218)
# ============================================================================
print("\n[1] PART 0 DISCRETE VERIFICATION CHECK")
print("-" * 72)
print(f"Formula: p(d) = (1/2) psi((d+1)/2) - (1/2) ln(pi)")
print(f"Thresholds: c1 = {mpmath.nstr(c1, 10)}, c2 = {mpmath.nstr(c2, 10)}")
print()
print(f"  Part 0 claims: p(19) = 0.5535")
print(f"  Computed:       p(19) = {mpmath.nstr(p(19), 10)}")
print()
print(f"  Part 0 claims: p(20) = 0.6013")
print(f"  Computed:       p(20) = {mpmath.nstr(p(20), 10)}")
print(f"  ** DISCREPANCY: Part 0's p(20) value appears incorrect. **")
print(f"  ** Correct p(20) ≈ 0.5791, not 0.6013.                   **")
print()
print(f"  Part 0 claims: p(217) = 1.77101")
print(f"  Computed:       p(217) = {mpmath.nstr(p(217), 10)}")
print()
print(f"  Part 0 claims: p(218) = 1.77331")
print(f"  Computed:       p(218) = {mpmath.nstr(p(218), 10)}")

# ============================================================================
# SECTION 2: Continuous boundary crossings via high-precision root finding
# ============================================================================
print("\n[2] CONTINUOUS BOUNDARY CROSSINGS (50 decimal places)")
print("-" * 72)

d0_star = mpmath.findroot(lambda d: p(d) - c0, mpmath.mpf("6.27"))
d1_star = mpmath.findroot(lambda d: p(d) - c1, mpmath.mpf("19.7"))
d2_star = mpmath.findroot(lambda d: p(d) - c2, mpmath.mpf("217.6"))

print(f"  d_0* = {mpmath.nstr(d0_star, 20)}  between integers (6, 7)")
print(f"         frac={mpmath.nstr(d0_star - 6, 10)}; nearer-integer = 6")
print()
print(f"  d_1* = {mpmath.nstr(d1_star, 20)}  between integers (19, 20)")
print(f"         frac={mpmath.nstr(d1_star - 19, 10)}; nearer-integer = 20")
print()
print(f"  d_2* = {mpmath.nstr(d2_star, 20)}  between integers (217, 218)")
print(f"         frac={mpmath.nstr(d2_star - 217, 10)}; nearer-integer = 218")

# Verify
print(f"\n  Residuals p(d*) - target (should be ~10^-50):")
print(f"    p(d_0*) - 0  = {mpmath.nstr(p(d0_star) - c0, 5)}")
print(f"    p(d_1*) - c1 = {mpmath.nstr(p(d1_star) - c1, 5)}")
print(f"    p(d_2*) - c2 = {mpmath.nstr(p(d2_star) - c2, 5)}")

# ============================================================================
# SECTION 3: Sphere areas at integer labels and continuous crossings
# ============================================================================
print("\n[3] SPHERE AREAS")
print("-" * 72)

Omega_5 = Omega(5)
Omega_6 = Omega(6)
Omega_7 = Omega(7)
Omega_d0 = Omega(d0_star)

print(f"  Omega_5   = pi^3       = {mpmath.nstr(Omega_5, 15)}")
print(f"  Omega_6   = 16*pi^3/15 = {mpmath.nstr(Omega_6, 15)}")
print(f"  Omega_d0* (= max)      = {mpmath.nstr(Omega_d0, 15)}")
print(f"  Omega_7   = pi^4/3     = {mpmath.nstr(Omega_7, 15)}")

Omega_19 = Omega(19)
Omega_20 = Omega(20)
Omega_d1 = Omega(d1_star)
print(f"\n  Omega_19                = {mpmath.nstr(Omega_19, 15)}")
print(f"  Omega_d1*               = {mpmath.nstr(Omega_d1, 15)}")
print(f"  Omega_20                = {mpmath.nstr(Omega_20, 15)}")

Omega_217 = Omega(217)
Omega_218 = Omega(218)
Omega_d2 = Omega(d2_star)
print(f"\n  Omega_217               = {mpmath.nstr(Omega_217, 15)}")
print(f"  Omega_d2*               = {mpmath.nstr(Omega_d2, 15)}")
print(f"  Omega_218               = {mpmath.nstr(Omega_218, 15)}")

# ============================================================================
# SECTION 4: Invariants under different boundary conventions
# ============================================================================
print("\n[4] INVARIANTS UNDER DIFFERENT BOUNDARY CONVENTIONS")
print("-" * 72)

def invariant(o_d0, o_d1, o_d2):
    return (Omega_5 / o_d0) ** 2 * o_d1 * o_d2

# (A) Part 0 mixed convention: (7, 19, 217) -- ceiling at d0, floor at d1, d2
I_P0 = invariant(Omega_7, Omega_19, Omega_217)

# (B) Uniform floor: (6, 19, 217) -- floor of each continuous crossing
I_floor = invariant(Omega_6, Omega_19, Omega_217)

# (C) Uniform ceiling: (7, 20, 218)
I_ceil = invariant(Omega_7, Omega_20, Omega_218)

# (D) Nearest integer: (6, 20, 218) -- d_0*=6.26→6, d_1*=19.73→20, d_2*=217.63→218
I_near = invariant(Omega_6, Omega_20, Omega_218)

# (E) Farther integer: (7, 19, 217) = Part 0's choice! (See section 6)
I_far = invariant(Omega_7, Omega_19, Omega_217)

# (F) Continuous crossings
I_cont = invariant(Omega_d0, Omega_d1, Omega_d2)

# (G) Geometric mean of each pair
Omega_g0 = mpmath.sqrt(Omega_6 * Omega_7)
Omega_g1 = mpmath.sqrt(Omega_19 * Omega_20)
Omega_g2 = mpmath.sqrt(Omega_217 * Omega_218)
I_geom = invariant(Omega_g0, Omega_g1, Omega_g2)

# (H) Arithmetic mean of each pair
Omega_a0 = (Omega_6 + Omega_7) / 2
Omega_a1 = (Omega_19 + Omega_20) / 2
Omega_a2 = (Omega_217 + Omega_218) / 2
I_arith = invariant(Omega_a0, Omega_a1, Omega_a2)

print(f"  (A) Part 0 mixed (7, 19, 217)    : {mpmath.nstr(I_P0,   15)}")
print(f"  (B) Uniform floor (6, 19, 217)   : {mpmath.nstr(I_floor, 15)}")
print(f"  (C) Uniform ceiling (7, 20, 218) : {mpmath.nstr(I_ceil,  15)}")
print(f"  (D) Nearest integer (6, 20, 218) : {mpmath.nstr(I_near,  15)}")
print(f"  (E) Farther integer (7, 19, 217) : {mpmath.nstr(I_far,   15)}  ← same as (A)")
print(f"  (F) Continuous crossings          : {mpmath.nstr(I_cont,  15)}")
print(f"  (G) Geometric mean of each pair   : {mpmath.nstr(I_geom,  15)}")
print(f"  (H) Arithmetic mean of each pair  : {mpmath.nstr(I_arith, 15)}")

obs = mpmath.mpf("1.10e-120")
obs_err = mpmath.mpf("0.02e-120")
print(f"\n  Observed rho_Lambda/M_Pl,red^4   : (1.10 ± 0.02) × 10^-120")

# ============================================================================
# SECTION 5: Deviations from observation
# ============================================================================
print("\n[5] DEVIATIONS FROM OBSERVATION")
print("-" * 72)
print(f"  {'Convention':<35} {'Value':<25} {'Dev%':<10}")

for name, I in [
    ("(A) Part 0 mixed (7,19,217)", I_P0),
    ("(B) Uniform floor (6,19,217)", I_floor),
    ("(C) Uniform ceiling (7,20,218)", I_ceil),
    ("(D) Nearest (6,20,218)", I_near),
    ("(F) Continuous crossings", I_cont),
    ("(G) Geometric mean", I_geom),
    ("(H) Arithmetic mean", I_arith),
]:
    dev = (I - obs) / obs * 100
    print(f"  {name:<35} {mpmath.nstr(I, 10):<25} {mpmath.nstr(dev, 6):<10}")

# ============================================================================
# SECTION 6: The central question - is I_P0 / I_cont = 4?
# ============================================================================
print("\n[6] I_P0 / I_cont RATIO: is it 4?")
print("-" * 72)

ratio_cont = I_P0 / I_cont
ratio_floor = I_floor / I_cont
ratio_geom = I_P0 / I_geom
ratio_arith = I_P0 / I_arith

print(f"  I_P0 / I_cont   = {mpmath.nstr(ratio_cont, 15)}")
print(f"  I_P0 / I_geom   = {mpmath.nstr(ratio_geom, 15)}")
print(f"  I_P0 / I_arith  = {mpmath.nstr(ratio_arith, 15)}")
print(f"  I_floor / I_cont = {mpmath.nstr(ratio_floor, 15)}")

print(f"\n  Candidate structural constants near 4.78:")
print(f"    4              = {mpmath.nstr(mpmath.mpf(4), 10)}")
print(f"    pi             = {mpmath.nstr(mpmath.pi, 10)}")
print(f"    3*pi/2         = {mpmath.nstr(3*mpmath.pi/2, 10)}")
print(f"    15/pi          = {mpmath.nstr(15/mpmath.pi, 10)}")
print(f"    pi^2/2         = {mpmath.nstr(mpmath.pi**2/2, 10)}  (= V_4)")
print(f"    2*pi - 1.5     = {mpmath.nstr(2*mpmath.pi - mpmath.mpf('1.5'), 10)}")
print(f"    e^(3/2)        = {mpmath.nstr(mpmath.exp(mpmath.mpf('1.5')), 10)}")
print(f"    5              = 5")
print(f"    actual ratio   = {mpmath.nstr(ratio_cont, 10)}")

# ============================================================================
# SECTION 7: Part 0's convention is "farther integer"
# ============================================================================
print("\n[7] WHAT IS PART 0'S IMPLICIT CONVENTION?")
print("-" * 72)
print(f"  Continuous crossings and Part 0's choices:")
print(f"  d_0* = {mpmath.nstr(d0_star, 8)}  -> Part 0 picks 7")
print(f"    |7 - d_0*| = {mpmath.nstr(mpmath.mpf(7) - d0_star, 6)}")
print(f"    |6 - d_0*| = {mpmath.nstr(d0_star - 6, 6)}")
print(f"    Part 0 picks the FARTHER integer (7).")
print()
print(f"  d_1* = {mpmath.nstr(d1_star, 8)}  -> Part 0 picks 19")
print(f"    |20 - d_1*| = {mpmath.nstr(mpmath.mpf(20) - d1_star, 6)}")
print(f"    |19 - d_1*| = {mpmath.nstr(d1_star - 19, 6)}")
print(f"    Part 0 picks the FARTHER integer (19).")
print()
print(f"  d_2* = {mpmath.nstr(d2_star, 8)}  -> Part 0 picks 217")
print(f"    |218 - d_2*| = {mpmath.nstr(mpmath.mpf(218) - d2_star, 6)}")
print(f"    |217 - d_2*| = {mpmath.nstr(d2_star - 217, 6)}")
print(f"    Part 0 picks the FARTHER integer (217).")
print()
print(f"  CONCLUSION: Part 0's implicit rule is 'farther integer of each pair'.")
print(f"  This is a consistent rule, not a mixed convention as I earlier claimed.")

# ============================================================================
# SECTION 8: Variational (argmax) characterization
# ============================================================================
print("\n[8] ARGMAX OVER ALL 8 INTEGER LABELINGS")
print("-" * 72)
print("  The 'farther integer' rule is equivalent to 'maximize I over labelings'.")
print("  Enumerating all 2^3 = 8 possible (d_0, d_1, d_2) assignments:")
print()
print(f"  {'rank':>4}  {'(d0, d1, d2)':>15}  {'I':>24}  {'dev from obs %':>15}")
print("  " + "-" * 65)

all_combinations = []
for d0 in [6, 7]:
    for d1 in [19, 20]:
        for d2 in [217, 218]:
            I_label = (Omega_5 / Omega(d0)) ** 2 * Omega(d1) * Omega(d2)
            dev = (I_label - obs) / obs * 100
            all_combinations.append((I_label, d0, d1, d2, dev))

# Sort descending by I value
all_combinations.sort(key=lambda x: -x[0])

for rank, (I_label, d0, d1, d2, dev) in enumerate(all_combinations, start=1):
    marker = "  <-- Part 0 (argmax)" if (d0, d1, d2) == (7, 19, 217) else ""
    print(f"  {rank:>4}  ({d0:>3}, {d1:>3}, {d2:>3})"
          f"  {mpmath.nstr(I_label, 15):>24}"
          f"  {mpmath.nstr(dev, 6):>14}%{marker}")

print()
argmax_labels = (all_combinations[0][1], all_combinations[0][2], all_combinations[0][3])
print(f"  Argmax over labelings: {argmax_labels}")
print(f"  Part 0's choice:        (7, 19, 217)")
print(f"  Agreement: {argmax_labels == (7, 19, 217)}")
print()
print("  The 0.1% match with observation is the statement that the supremum of")
print("  the cascade invariant over integer labelings coincides with the observed")
print("  rho_Lambda/M_Pl_red^4, to within the observational 1-sigma uncertainty.")

# ============================================================================
# SECTION 9: Summary
# ============================================================================
print("\n[9] SUMMARY")
print("-" * 72)
print("  * Part 0 has a numerical error in the discrete verification at d=20:")
print(f"    Claimed p(20) = 0.6013; correct p(20) = {mpmath.nstr(p(20), 10)}.")
print()
print("  * The continuous crossings lie at d_0* = 6.2569, d_1* = 19.7308,")
print("    d_2* = 217.6267 - each straddled by an integer pair.")
print()
print("  * Part 0's integer labeling (7, 19, 217) is the uniform 'farther")
print("    integer of each pair' rule, equivalently the ARGMAX of the")
print("    cascade invariant over all 8 possible integer labelings.")
print()
print("  * The 0.1% match with observation is the statement that the supremum")
print("    of I over boundary labelings coincides with rho_Lambda/M_Pl_red^4.")
print()
print("  * Deviations of alternative conventions from observation:")
print(f"    - Part 0 argmax (7, 19, 217)      : {mpmath.nstr(((I_P0 - obs)/obs*100), 5)}%")
print(f"    - Uniform floor (6, 19, 217)      : {mpmath.nstr(((I_floor - obs)/obs*100), 5)}%")
print(f"    - Nearest integer (6, 20, 218)    : {mpmath.nstr(((I_near - obs)/obs*100), 5)}%")
print(f"    - Continuous crossings            : {mpmath.nstr(((I_cont - obs)/obs*100), 5)}%")
print(f"    - Geometric mean                  : {mpmath.nstr(((I_geom - obs)/obs*100), 5)}%")
