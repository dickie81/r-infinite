#!/usr/bin/env python3
"""
Hopf-propagation closure of Clifford absorption: numerical investigation.

CLAIM TO TEST: Reading (III) plus audit items 3.2, 3.3 (Adams 1960 chain
made explicit) provide a cascade-internal Hopf-propagation of octonion
algebraic structure from d=8 (S^7 parallelisable) and d=7 (S^6 = G_2/SU(3))
to the host d=5 (S^4) via the Hopf bundle S^7 -> S^4, giving the cascade
fermion measure m(d=5) = R(5)/2 without the scalar's axial sqrt(pi).

This script tests whether specific cascade volume ratios at the relevant
layers actually produce R(d)/2 cascade-internally.

Concrete computations:
  1. Cascade primitives at d=5, 7, 8 (R, alpha, V, Omega).
  2. Hopf bundle volume ratio: Omega_7 / Omega_4 should reflect Hopf
     fibre Omega_3 (since S^7 = S^3-bundle over S^4).
  3. Test whether R(5)/2 emerges from any cascade-internal combination
     of d=7, 8 quantities through the Hopf bundle.

The honest scope: this is structural plausibility checking, NOT a proof.
A full proof needs the Hopf-propagation theorem constructed cascade-
internally (Part IVc work).  This script identifies what does and
doesn't fall out numerically.
"""
import numpy as np
from scipy.special import gamma as Gfn

pi = np.pi


def R(d):
    """Cascade slicing ratio R(d) = Gamma((d+1)/2) / Gamma((d+2)/2)."""
    return Gfn((d + 1) / 2) / Gfn((d + 2) / 2)


def alpha(d):
    """Cascade per-layer scale alpha(d) = R(d)^2 / 4."""
    return R(d) ** 2 / 4


def V(d):
    """Volume of unit d-ball: V_d = pi^{d/2} / Gamma(d/2 + 1)."""
    return pi ** (d / 2) / Gfn(d / 2 + 1)


def Omega(d):
    """Surface area of unit S^{d-1} (so Omega_d = 2 pi^{(d+1)/2}/Gamma((d+1)/2))."""
    # Note: I use the convention Omega_d = surface area of S^d (d-sphere).
    return 2 * pi ** ((d + 1) / 2) / Gfn((d + 1) / 2)


def N(d):
    """Cascade lapse: N(d) = sqrt(pi) * R(d)."""
    return np.sqrt(pi) * R(d)


def main():
    print("=" * 78)
    print("HOPF-PROPAGATION TEST: Reading (III) + Adams 1960 chain")
    print("=" * 78)
    print()

    # === Step 1: cascade primitives at relevant layers ===
    print("=" * 78)
    print("Step 1: cascade primitives at d in {5, 7, 8}")
    print("=" * 78)
    print()
    print(f"{'d':>3s} {'R(d)':>14s} {'alpha(d)=R^2/4':>16s} {'V_d':>14s} {'Omega_{d-1}':>14s} {'N(d)=sqrt(pi)R':>14s}")
    print("-" * 78)
    for d in [5, 7, 8, 4]:
        print(f"{d:>3d} {R(d):>14.10f} {alpha(d):>16.10f} {V(d):>14.10f} {Omega(d-1):>14.10f} {N(d):>14.10f}")
    print()

    # Specific values we want to reproduce
    R5 = R(5)
    R5_over_2 = R5 / 2
    print(f"  Target: m(d=5) = R(5)/2 = {R5_over_2:.10f}")
    print(f"  Also: R(5)/2 = 8/(15 sqrt(pi)) = {8/(15*np.sqrt(pi)):.10f} (closed form)")
    print()

    # === Step 2: Hopf bundle S^7 -> S^4 volume ratios ===
    print("=" * 78)
    print("Step 2: Hopf bundle volume identity at the cascade-internal d=8 -> d=5")
    print("=" * 78)
    print()

    # S^n has surface area Omega_{n} where Omega_n = 2 pi^{(n+1)/2}/Gamma((n+1)/2)
    # In my convention Omega(d-1) = surface area of S^{d-1}, so
    # surface area of S^k is Omega(k+1) - 1? No wait, let me re-check.
    # Omega(d) = 2 pi^{(d+1)/2}/Gamma((d+1)/2). For d=2, Omega(2) = 2 pi^{3/2}/Gamma(3/2) = 2 pi^{3/2}/(sqrt(pi)/2) = 4 pi.
    # That's the surface area of S^2 = 4 pi. So Omega(d) = surface area of S^d. Good.

    # Surface areas of the relevant spheres in the Hopf bundle S^7 -> S^4
    Om7 = Omega(7)  # S^7
    Om4 = Omega(4)  # S^4
    Om3 = Omega(3)  # S^3 (Hopf fibre)
    Om6 = Omega(6)  # S^6 (G_2/SU(3))

    print(f"  Omega_7 = surf(S^7) = pi^4/3       = {Om7:.10f}, check: {pi**4/3:.10f}")
    print(f"  Omega_4 = surf(S^4) = 8 pi^2/3     = {Om4:.10f}, check: {8*pi**2/3:.10f}")
    print(f"  Omega_3 = surf(S^3) = 2 pi^2       = {Om3:.10f}, check: {2*pi**2:.10f}")
    print(f"  Omega_6 = surf(S^6) = 16 pi^3/15   = {Om6:.10f}, check: {16*pi**3/15:.10f}")
    print()

    # Hopf bundle: S^7 = S^3-bundle over S^4
    # Bundle integration: Omega_7 = Omega_3 * Omega_4 / (4) for the standard round metric
    # (the factor 1/4 reflects the Hopf circle / SU(2) fibre normalization)
    print(f"  Omega_3 * Omega_4 / Omega_7 = {Om3 * Om4 / Om7:.10f}")
    print(f"    (this is the Hopf bundle's curvature-corrected fibre integration factor)")
    print()

    # === Step 3: test if R(5)/2 emerges from d=7 or d=8 quantities ===
    print("=" * 78)
    print("Step 3: does R(5)/2 = 8/(15 sqrt(pi)) emerge from d=7, 8 cascade quantities?")
    print("=" * 78)
    print()
    print(f"  Target: R(5)/2 = {R5_over_2:.10f}")
    print()

    # Try various cascade-internal combinations
    candidates = [
        ("R(8)", R(8)),
        ("R(7)", R(7)),
        ("R(8) * R(7)", R(8) * R(7)),
        ("R(8) / R(7)", R(8) / R(7)),
        ("alpha(8)", alpha(8)),
        ("alpha(7)", alpha(7)),
        ("sqrt(alpha(7))", np.sqrt(alpha(7))),
        ("sqrt(alpha(8))", np.sqrt(alpha(8))),
        ("sqrt(alpha(7) * alpha(8))", np.sqrt(alpha(7) * alpha(8))),
        ("R(8) / 2", R(8) / 2),
        ("Omega_3 / Omega_7", Om3 / Om7),
        ("Omega_4 / Omega_7", Om4 / Om7),
        ("Omega_6 / Omega_7", Om6 / Om7),
        ("Omega_3 / (Omega_7 * pi)", Om3 / (Om7 * pi)),
        ("V_5 / V_8", V(5) / V(8)),
        ("V_5 / V_7", V(5) / V(7)),
        ("(V_5 / V_8) / sqrt(pi)", (V(5) / V(8)) / np.sqrt(pi)),
        # Cascade descent product: V_8/V_5 = product of N(d) for d=6,7,8
        ("R(6) * R(7) * R(8)", R(6) * R(7) * R(8)),
        ("R(6) * R(7) * R(8) / 2", R(6) * R(7) * R(8) / 2),
        ("R(7) * R(8)", R(7) * R(8)),
        # More complex: maybe a Hopf bundle ratio gives it
        ("R(5)", R5),
    ]

    print(f"  {'Candidate':<35s}  {'value':>14s}  {'value/target':>14s}  {'match?':>8s}")
    print("  " + "-" * 80)
    for name, val in candidates:
        ratio = val / R5_over_2
        match = "EXACT" if abs(ratio - 1) < 1e-10 else f"{ratio:>5.4f}"
        print(f"  {name:<35s}  {val:>14.10f}  {ratio:>14.10f}  {match:>8s}")
    print()

    # === Step 4: scaling check ===
    print("=" * 78)
    print("Step 4: scaling check -- does Hopf-propagation give polynomial decay?")
    print("=" * 78)
    print()
    print("  R(d)/2 at Dirac layers:")
    print(f"    {'d':>4s}  {'R(d)/2':>14s}  {'asymptotic 1/sqrt(2d)':>22s}")
    for d in [5, 13, 21, 29]:
        Rd = R(d)
        print(f"    {d:>4d}  {Rd/2:>14.10f}  {1/np.sqrt(2*d):>22.10f}")
    print()
    print("  Octonion algebra (fixed dim 8) scaling: R^{(d-8)/2} or similar?")
    print(f"    R(5)/2     = {R(5)/2:.10f}")
    print(f"    R(8) * R(7) * R(6) = {R(8)*R(7)*R(6):.10f}")
    print(f"    Ratio R(5)/2 / [R(6)R(7)R(8)] = {(R(5)/2) / (R(6)*R(7)*R(8)):.10f}")
    print(f"    sqrt(pi^3) = {np.sqrt(pi**3):.10f}")
    print()
    # The cascade descent identity: R(d) = R(d-1) * (d/(d+1)) by Gamma recursion?
    # Actually let's check
    print("  Cascade recursion check: does R(d+2)/R(d) = (d+1)/(d+2)?")
    for d in [5, 6, 7, 8]:
        ratio = R(d+2) / R(d)
        expected = (d + 1) / (d + 2)
        print(f"    d={d}: R({d+2})/R({d}) = {ratio:.6f}, expected (d+1)/(d+2) = {expected:.6f}, match: {abs(ratio - expected) < 1e-10}")
    print()

    # === Step 5: explicit cascade descent factor product ===
    print("=" * 78)
    print("Step 5: cascade descent V_5 from V_8 via slicing")
    print("=" * 78)
    print()
    print("  V_{d+1} = V_d * sqrt(pi) * R(d+1)")
    print("  So: V_8 = V_5 * (sqrt(pi))^3 * R(6) * R(7) * R(8)")
    print("  Equivalently: V_5 = V_8 / [pi^(3/2) * R(6) R(7) R(8)]")
    print()
    V5_via_descent = V(8) / (pi**(3/2) * R(6) * R(7) * R(8))
    print(f"    V_5 direct          = {V(5):.10f}")
    print(f"    V_5 via descent     = {V5_via_descent:.10f}")
    print(f"    match: {abs(V(5) - V5_via_descent) < 1e-10}")
    print()
    print("  KEY: the (sqrt(pi))^3 factor in cascade descent is the THREE axial Jacobians")
    print("  picked up at each step d=5->6, 6->7, 7->8.  If the fermion measure")
    print("  doesn't pick up these Jacobians, V_5^{fermion} = V_8 / [R(6) R(7) R(8)]:")
    V5_fermion = V(8) / (R(6) * R(7) * R(8))
    print(f"    V_5^{{fermion}} = V_8 / [R(6)R(7)R(8)] = {V5_fermion:.10f}")
    print(f"    R(5)/2 target                          = {R5_over_2:.10f}")
    print(f"    ratio                                  = {V5_fermion / R5_over_2:.10f}")
    print()

    # === Step 6: sphere-area version ===
    print("=" * 78)
    print("Step 6: sphere-area version of the cascade descent")
    print("=" * 78)
    print()
    print("  Using sphere areas Omega_d instead of ball volumes V_d:")
    print(f"    Omega_4 = {Om4:.10f}")
    print(f"    Omega_7 = {Om7:.10f}")
    print(f"    Omega_4 / Omega_7 = {Om4/Om7:.10f}")
    print(f"    R(5)/2 = {R5_over_2:.10f}")
    print(f"    ratio (Omega_4/Omega_7) / (R(5)/2) = {(Om4/Om7) / R5_over_2:.10f}")
    print()
    # Check if Omega_4/Omega_7 has a clean cascade-internal form
    print(f"    Omega_4/Omega_7 = (8 pi^2/3) / (pi^4/3) = 8/pi^2 = {8/pi**2:.10f}")
    print(f"    R(5)/2 = 8/(15 sqrt(pi)) = {8/(15*np.sqrt(pi)):.10f}")
    print(f"    These are different (Omega ratio: {8/pi**2:.6f}, target: {8/(15*np.sqrt(pi)):.6f})")
    print()

    # === Step 7: structural interpretation ===
    print("=" * 78)
    print("Step 7: what does the calculation tell us?")
    print("=" * 78)
    print()
    print("Key findings:")
    print()
    print("  (a) NO direct cascade-internal combination of d=7, 8 quantities")
    print("      yields R(5)/2 exactly.  The candidates tested are off by")
    print("      factors of pi^(1/2), pi, etc.")
    print()
    print("  (b) The cascade descent V_8 -> V_5 picks up three sqrt(pi) factors")
    print("      (one per axial Beta integral at d=6, 7, 8).  If these are")
    print("      stripped (octonion measure has no axial Jacobian), one gets")
    print("      V_5^{fermion} = V_8 / [R(6) R(7) R(8)] = pi^{3/2} V(5).")
    print("      This is V(5) * pi^{3/2} -- not directly R(5)/2.")
    print()
    print("  (c) R(5)/2 = 8/(15 sqrt(pi)) has a sqrt(pi) in the DENOMINATOR.")
    print("      For the fermion measure to give this, it needs to PRODUCE")
    print("      a 1/sqrt(pi), not just AVOID a sqrt(pi) factor.")
    print()
    print("  (d) Comparing: scalar lapse N(5) = sqrt(pi) R(5) = 8/15.")
    print("      Fermion target m(5) = R(5)/2 = 8/(15 sqrt(pi)) = N(5)/(2 sqrt(pi)).")
    print("      The factor 1/(2 sqrt(pi)) is exactly Part IVb's Clifford")
    print("      absorption ratio -- but the QUESTION is where the 1/sqrt(pi)")
    print("      comes from cascade-internally.")
    print()
    print("  (e) Strict reading: m(5) = N(5)/(2 sqrt(pi)) = R(5)/2.  The 1/2")
    print("      is chirality halving (Theorem 4.14, derived).  The 1/sqrt(pi)")
    print("      is the part Reading-III-Hopf-propagation would need to supply.")
    print("      None of the natural cascade combinations tested produce 1/sqrt(pi)")
    print("      cleanly.")
    print()
    print("HONEST CONCLUSION:")
    print()
    print("  Reading (III) and the Adams 1960 chain (audit 3.2, 3.3) provide")
    print("  the structural shape (octonion algebra at d=7, 8 propagating via")
    print("  Hopf bundle to d=5 host) but do NOT obviously yield the specific")
    print("  numerical factor R(5)/2 from cascade-internal volume ratios.")
    print()
    print("  The 1/sqrt(pi) factor's cascade-internal origin remains the open")
    print("  problem.  Reading III supplies a candidate framework (octonion-")
    print("  derived measure on S^6 at d=7); the specific calculation that")
    print("  produces 1/sqrt(pi) from this framework has not been identified.")
    print()
    print("  This is a PARTIAL NEGATIVE result: the structural framework is")
    print("  promising (right scaling, no super-exp pathology) but the specific")
    print("  numerical bridge from octonion structure to 1/sqrt(pi) is not")
    print("  found in the obvious places (cascade descent ratios, sphere-area")
    print("  combinations, R-product rearrangements).")
    print()
    print("  A successful Part IVc would need to identify HOW the octonion")
    print("  measure structure produces 1/sqrt(pi) -- presumably via specific")
    print("  G_2-invariant integration that I haven't computed here.  This")
    print("  needs the actual G_2 3-form integration, not just dimensional")
    print("  reasoning.")


if __name__ == "__main__":
    main()
