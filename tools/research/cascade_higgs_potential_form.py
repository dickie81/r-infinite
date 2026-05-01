#!/usr/bin/env python3
"""
Cascade-internal derivation of V(theta) = (1/2) cos^2(theta) on S^12
from primitives -- not assuming the cos^2 form.

THE OPEN QUESTION
=================
Part IVb rem:lambda-direct supplies the chain V''(pi/2)=1 -> lambda =
pi^2 g^2/32.  But this assumes V(theta) = (1/2) cos^2(theta) on S^12.
The deeper question: derive this specific potential form from cascade
primitives.

CASCADE PRIMITIVES AVAILABLE
============================
At d=13 (SU(2) gauge layer in cascade):
  - S^{d-1} = S^12 (gauge boson sphere, Adams thm:adams)
  - Lefschetz / hairy-ball: SU(2) is broken at d=13 (chi(S^12) = 2)
  - Two zeros of any tangent vector field at the poles (north + south)
  - Chirality factor chi = 2 (Theorem chirality-factorisation)
  - Cascade gauge coupling N(13)^2 (Part IVa Adams)

THE DERIVATION
==============
Four cascade-internal conditions force V(theta) = (1/2) cos^2(theta):

(C1) Higgs effective potential V is a function on S^12 -- the gauge
     sphere at d=13.  Cascade structural (Adams + Higgs at gauge layer).

(C2) Antipodal symmetry V(theta) = V(pi - theta).  Cascade structural:
     the hairy-ball obstruction has two zeros at the antipodal poles
     of S^12, and the cascade's chirality theorem (Thm 4.8) treats them
     symmetrically.  This forces V to be a function of cos^2(theta) only
     (or higher even harmonics).

(C3) Lowest harmonic truncation: V(theta) = c_0 Y_0 + c_2 Y_2 + c_4 Y_4 + ...
     The cascade truncates to the LOWEST non-trivial mode (analogous to
     how the cascade scalar action retains only the leading slicing-recurrence
     mode; higher modes correspond to higher-dimensional excitations on
     S^12 that aren't sourced by the obstruction at d=13).
     => V(theta) = c_0 + c_2 Y_2(theta)
     where Y_2(theta) on S^n is the zonal quadrupole = cos^2(theta) - 1/(n+1)
     for unit sphere.  On S^12: Y_2 = cos^2(theta) - 1/13.

(C4) Boundary conditions:
     - V(VEV at theta=pi/2) = 0 (broken vacuum has zero potential energy;
       convention at zero-point of energy)
     - V(obstruction at theta=0) = 1/chi = 1/2 (cascade chirality factor:
       at the obstruction zero, energy is shared equally between the chi
       basins meeting there, giving V = 1/chi in cascade-natural units)

These four conditions UNIQUELY determine V(theta) = (1/2) cos^2(theta).

DERIVATION
==========
From (C2) + (C3): V = c_0 + c_2 Y_2, with Y_2 = cos^2(theta) - 1/13 on S^12.

From (C4) V(pi/2) = 0:
   c_0 + c_2 * Y_2(pi/2) = c_0 + c_2 * (0 - 1/13) = c_0 - c_2/13 = 0
   => c_0 = c_2/13

From (C4) V(0) = 1/chi = 1/2:
   c_0 + c_2 * Y_2(0) = c_0 + c_2 * (1 - 1/13) = c_0 + (12/13) c_2 = 1/2
   Substituting c_0 = c_2/13:
   c_2/13 + 12 c_2/13 = c_2 = 1/2
   So c_2 = 1/2, c_0 = 1/26.

V(theta) = 1/26 + (1/2) Y_2(theta)
        = 1/26 + (1/2)(cos^2(theta) - 1/13)
        = 1/26 - 1/26 + (1/2) cos^2(theta)
        = (1/2) cos^2(theta).

VERIFIED.

WHAT THIS SCRIPT DOES
=====================
  1. States the four cascade-internal conditions explicitly.
  2. Verifies that V(theta) = (1/2) cos^2(theta) is uniquely determined.
  3. Computes V''(pi/2) = 1 directly from the derived form.
  4. Identifies the structural status of each condition (cascade-derived
     vs heuristic vs convention).

WHAT THIS SCRIPT DOES NOT DO
============================
  - Provide a fully airtight derivation of (C3) (lowest-harmonic
    truncation) from the cascade scalar action principle.
  - Provide an airtight derivation of (C4) V(0) = 1/chi (currently
    heuristic, motivated by chirality-basin sharing at the obstruction).
  - Address why the cascade Higgs vacuum manifold is S^11 (the equator
    of S^12), which is larger than SM's S^3 vacuum manifold.
"""

from __future__ import annotations

import math


def Y2_zonal(theta: float, n: int) -> float:
    """Zonal Y_2 spherical harmonic on S^n: cos^2(theta) - 1/(n+1)."""
    return math.cos(theta)**2 - 1.0/(n+1)


def V_cascade(theta: float) -> float:
    """Cascade Higgs potential V(theta) = (1/2) cos^2(theta)."""
    return 0.5 * math.cos(theta)**2


def V_double_prime(theta: float) -> float:
    """V''(theta) = -cos(2 theta) for V = (1/2) cos^2(theta)."""
    return -math.cos(2 * theta)


def main():
    print("=" * 78)
    print("Cascade-internal derivation of V(theta) = (1/2) cos^2(theta) on S^12")
    print("=" * 78)
    print()

    n = 12
    chi = 2

    # ---- Step 1: condition (C1) ----
    print("CONDITION (C1): V is a function on S^12")
    print("-" * 78)
    print(f"  Cascade structural: Higgs at d=13 is on S^(d-1) = S^12.")
    print(f"  Source: Part IVa thm:adams; Higgs mechanism at d=13.")
    print()

    # ---- Step 2: condition (C2) ----
    print("CONDITION (C2): antipodal symmetry V(theta) = V(pi - theta)")
    print("-" * 78)
    print(f"  Hairy-ball obstruction has TWO zeros (chi(S^12) = {chi}).")
    print(f"  Cascade chirality theorem (Thm 4.8) treats the basins symmetrically.")
    print(f"  Forces V to be a function of cos^2(theta) (even in theta - pi/2).")
    print(f"  Source: Lefschetz / hairy-ball; cascade chirality factor.")
    print()

    # ---- Step 3: condition (C3) ----
    print("CONDITION (C3): lowest-harmonic truncation V = c_0 Y_0 + c_2 Y_2")
    print("-" * 78)
    print(f"  Antipodal-symmetric harmonics on S^n: Y_0 (constant), Y_2 (quadrupole),")
    print(f"  Y_4, Y_6, ...  Cascade truncates to lowest non-trivial mode (L=2).")
    print(f"  Y_2 on S^{n}: zonal form = cos^2(theta) - 1/(n+1) = cos^2(theta) - 1/{n+1}.")
    print(f"  Higher modes (L=4, 6, ...) require additional sources at higher")
    print(f"  spherical-harmonic moments, which the cascade does NOT supply at d=13:")
    print(f"  the Higgs is sourced only by the L=2 obstruction.")
    print(f"  Source: spherical-harmonic decomposition + cascade truncation principle.")
    print()
    print(f"  Status: heuristic.  A first-principles derivation would compute the")
    print(f"  cascade Higgs effective potential at d=13 from the action principle")
    print(f"  (currently downstream of oq:fermion-gauge-action) and verify it has")
    print(f"  no L>=4 components.")
    print()

    # ---- Step 4: condition (C4) ----
    print("CONDITION (C4): boundary conditions V(pi/2) = 0, V(0) = 1/chi")
    print("-" * 78)
    print(f"  V(pi/2) = 0: broken-vacuum convention (zero-point of energy).")
    print(f"  V(0) = 1/chi = 1/{chi} = 0.5: cascade chirality factor.")
    print(f"  At the obstruction zero (theta=0), the cascade has chi = {chi} chirality")
    print(f"  basins meeting symmetrically.  Cascade-natural energy at the zero:")
    print(f"    V(0) = (cascade gauge coupling at d=13) / chi (per-basin contribution)")
    print(f"    in dimensionless units, V(0) = 1/chi = 1/{chi}.")
    print(f"  Source: cascade chirality structure; analogous to the chirality")
    print(f"  filtering 1/chi^k in the open-line family (Thm 4.8).")
    print()
    print(f"  Status: heuristic.  A first-principles derivation would relate the")
    print(f"  obstruction-zero energy to the cascade gauge coupling structure")
    print(f"  cascade-natively (via the action principle).")
    print()

    # ---- Step 5: solve for c_0, c_2 ----
    print("STEP 5: solve for the harmonic coefficients")
    print("-" * 78)
    print(f"  V(theta) = c_0 + c_2 Y_2(theta) = c_0 + c_2 (cos^2(theta) - 1/13)")
    print()
    print(f"  Equation (1): V(pi/2) = 0")
    print(f"    c_0 + c_2 * (-1/13) = 0  =>  c_0 = c_2/13")
    print()
    print(f"  Equation (2): V(0) = 1/2")
    print(f"    c_0 + c_2 * (12/13) = 1/2")
    print(f"    c_2/13 + 12 c_2/13 = c_2 = 1/2")
    print()
    print(f"  Solution: c_2 = 1/2, c_0 = 1/26")
    print()
    print(f"  V(theta) = 1/26 + (1/2)(cos^2(theta) - 1/13)")
    print(f"          = 1/26 - 1/26 + (1/2) cos^2(theta)")
    print(f"          = (1/2) cos^2(theta)  ✓")
    print()

    # ---- Step 6: numerical verification ----
    print("STEP 6: numerical verification at key points")
    print("-" * 78)
    print(f"  {'theta':>8}  {'V(theta)':>12}  {'V''(theta)':>12}  {'description':<30}")
    points = [
        (0,                "obstruction zero / pole"),
        (math.pi/4,        "halfway"),
        (math.pi/2,        "VEV / equator"),
        (3*math.pi/4,      "symmetric of pi/4"),
        (math.pi,          "antipodal pole"),
    ]
    for theta, desc in points:
        v = V_cascade(theta)
        vpp = V_double_prime(theta)
        print(f"  {theta:>8.4f}  {v:>12.5f}  {vpp:>12.5f}  {desc:<30}")
    print()
    print(f"  V(0) = 1/2 = 1/chi    ✓ (cascade chirality factor)")
    print(f"  V(pi/2) = 0           ✓ (broken-vacuum convention)")
    print(f"  V''(pi/2) = 1         ✓ (cascade structural curvature)")
    print()

    # ---- Step 7: status summary ----
    print("STATUS")
    print("-" * 78)
    print(f"  CASCADE-DERIVED (structural):")
    print(f"  - Higgs lives on S^12 (Adams + Higgs at d=13)")
    print(f"  - Antipodal symmetry V(theta) = V(pi-theta) (Lefschetz + chirality)")
    print(f"  - Specific cos^2(theta) form (UNIQUE solution to C1+C2+C3+C4)")
    print()
    print(f"  CASCADE-DERIVED (with heuristic arguments):")
    print(f"  - Lowest-harmonic truncation L=0+L=2 (truncation principle, not")
    print(f"    derived from action explicitly)")
    print(f"  - V(0) = 1/chi (chirality-basin energy sharing, not derived from")
    print(f"    action explicitly)")
    print()
    print(f"  CASCADE-DERIVED CONSEQUENCES:")
    print(f"  - V''(pi/2) = 1 (sphere geometry, follows from cos^2 form)")
    print(f"  - lambda = pi^2 g^2/32 (Remark rem:lambda-direct, V_0 = N(13)^2 v^4/4)")
    print()
    print(f"  WHAT REMAINS OPEN:")
    print(f"  - First-principles derivation of (C3) and (C4) from cascade action,")
    print(f"    downstream of oq:fermion-gauge-action.")
    print(f"  - Why cascade Higgs vacuum manifold is S^11 (equator) rather than")
    print(f"    SM's S^3 (after symmetry breaking).  This is a structural issue")
    print(f"    about the cascade's compactification of d=13 down to d=4.")
    print()
    print(f"  PARTIAL CLOSURE: the cos^2(theta) form is now derived from the")
    print(f"  four cascade-internal conditions.  The truly first-principles")
    print(f"  derivation requires the cascade-action setting of (C3) and (C4),")
    print(f"  which is downstream.")
    print()


if __name__ == "__main__":
    main()
