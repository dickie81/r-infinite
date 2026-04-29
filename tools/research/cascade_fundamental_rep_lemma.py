#!/usr/bin/env python3
"""
Research note: the cascade-internal forcing of the FUNDAMENTAL
representation at each gauge-window layer.

CLAIM (UNIFIED LEMMA)
---------------------
At each gauge-window layer d in {12, 13, 14}, the cascade space's
Bott-structured carrier IS the underlying vector space of the gauge
group's fundamental representation.  Matter content at that layer
embeds naturally into this carrier; therefore matter transforms in the
fundamental rep.

CONTEXT
-------
The cascade derives gauge groups SU(3) x SU(2) x U(1) at d in
{12, 13, 14} from Adams' theorem (Part IVa Theorem thm:adams) and
Bott periodicity.  It does NOT explicitly derive that matter takes
the FUNDAMENTAL representation at each layer (vs. adjoint, symmetric,
higher tensor, etc.).  The verifier
`tools/verifiers/cascade_path_tensor_product.py` flags this as open
in its docstring:

    "Cascade-internal derivation that each particle takes the SPECIFIC
    representation it does (fundamental vs. adjoint vs. higher-symmetric).
    The cascade derives the GAUGE GROUPS at distinguished layers but
    the specific representations are imported from SM observation."

This script splits the unified claim by layer and reports:

  d=12 (SU(3)): CLOSED structurally.  H^3 = R^12 forces N_c = 3.
                Already implicit in Part IVa rem:su3-d7-algebra
                line 519: "Fundamental representation dimension
                (N_c=3) at d=12 via Adams' theorem."
                This script makes the argument explicit.

  d=14 (U(1)):  PARTIALLY CLOSED.  C^7 = R^14 via J (PR #105) forces
                fundamental rep DIMENSION = 1.  CHARGE SPECTRUM open:
                J's eigenvalues are +/- 1, but SM hypercharges are
                fractional {-1, -1/2, -1/3, +1/6, +2/3, +1}.

  d=13 (SU(2)): OPEN.  R^13 has no clean Bott complex/quaternionic
                decomposition.  The 2-complex-dim Weyl piece of the
                d=13 Dirac spinor is the natural fundamental-rep
                carrier, but the chirality split (L doublet vs R
                singlet) requires a separate derivation.

CONNECTION TO CLAUDE.MD
-----------------------
This research note narrows the matter-rep / hypercharge gap recorded
in CLAUDE.md (PR #105).  It splits the gap into:
  - rep DIMENSION (fundamental vs adjoint etc.): CLOSED at d=12,
    CLOSED at d=14, OPEN at d=13.
  - rep WEIGHT (specific Y values): OPEN at d=14, partial at d=13
    (depends on doublet structure).

The script's final report could be folded back into a CLAUDE.md
sub-bullet if the user wants to record the narrowing.
"""

from __future__ import annotations

import math
import sys

import numpy as np
from scipy.special import gammaln


# ---------------------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------------------

def radon_hurwitz(n: int) -> int:
    """Radon--Hurwitz number rho(n) for Adams' theorem."""
    a, m = 0, n
    while m % 2 == 0:
        a += 1
        m //= 2
    q, r = divmod(a, 4)
    return 8 * q + 2**r


def R_cascade(d: int) -> float:
    return float(np.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0)))


def alpha_cascade(d: int) -> float:
    return R_cascade(d) ** 2 / 4.0


def build_J(n: int) -> np.ndarray:
    """Block-diagonal J on R^{2n}: 2x2 blocks [[0,-1],[1,0]]."""
    J = np.zeros((2 * n, 2 * n))
    for k in range(n):
        J[2 * k, 2 * k + 1] = -1.0
        J[2 * k + 1, 2 * k] = +1.0
    return J


# ---------------------------------------------------------------------------
# d=12 case: H^3 = R^12 forces N_c = 3
# ---------------------------------------------------------------------------

def d12_quaternionic_carrier() -> None:
    print("-" * 78)
    print("d=12 (SU(3)): H^3 = R^12 forces N_c = 3")
    print("-" * 78)
    print()
    print("Cascade ingredients (all in Part IVa, no new content):")
    print("  - Cascade space at d=12: V_{12} = R^12.")
    print("  - Bott periodicity: Cl(1,d-1) at d=4 is M_2(C) tensor M_2(R)")
    print("    (Part IVa Section 2.1, Lounesto Lorentzian (1,d-1) table");
    print("    line 119); d=12 = d=4 + one Bott period 8.")
    print("  - Quaternionic decomposition R^12 = H^3 (three quaternionic")
    print("    dimensions, equivalently 3 copies of R^4 = H).")
    print("  - Adams' theorem on S^11: rho(12) - 1 = 3 nowhere-zero")
    print("    tangent fields (Part IVa Theorem thm:adams).")
    print("  - These 3 fields are the right-multiplications by quaternion")
    print("    units {i, j, k} on H^3 (Part IVa rem:su3-d7-algebra line")
    print("    528-532; verifier cascade_d7_su3_bs_closure.py Step 1).")
    print()
    print("Numerical sanity:")
    rho12 = radon_hurwitz(12)
    print(f"  rho(12) = {rho12};  rho(12) - 1 = {rho12 - 1}  (matches 3 = N_c)")
    print(f"  R^12 dimension = 12 = 4 * 3 = dim(H) * N_c  (quaternionic")
    print(f"    decomposition consistent)")
    print()
    print("Forcing argument:")
    print("  (1) The cascade space at d=12 IS R^12 (slicing recurrence,")
    print("      Part 0 cascade tower).")
    print("  (2) R^12 has the natural quaternionic decomposition R^12 = H^3")
    print("      via the Bott class inherited from d=4.")
    print("  (3) The Adams' fields (3 nowhere-zero tangent fields on S^11)")
    print("      act as quaternionic right-multiplications -- they ARE the")
    print("      cascade structure at d=12, not auxiliary.")
    print("  (4) The 'three' of H^3 = the dimension of SU(3)'s fundamental")
    print("      rep (the 3 in '3 of SU(3)').")
    print("  (5) Matter at d=12 lives in the cascade space; the cascade")
    print("      space is H^3; matter therefore transforms in the 3 of SU(3).")
    print()
    print("Status: CLOSED structurally.  This is the implicit content of")
    print("Part IVa rem:su3-d7-algebra line 519:")
    print("  'Fundamental representation dimension (N_c=3) at d=12 via")
    print("   Adams' theorem.'")
    print("The argument above makes the lemma explicit; it does not add")
    print("new cascade content.")
    print()


# ---------------------------------------------------------------------------
# d=14 case: C^7 = R^14 via J forces dim-1 fundamental rep
# ---------------------------------------------------------------------------

def d14_complex_carrier() -> None:
    print("-" * 78)
    print("d=14 (U(1)): C^7 = R^14 via J forces dim-1 fundamental rep")
    print("-" * 78)
    print()
    print("Cascade ingredients (PR #105 result, plus Part II/IVa):")
    print("  - Cascade space at d=14: V_{14} = R^14.")
    print("  - Cascade complex structure J (Part II thm:complex):")
    print("    J^2 = -Id, block-diagonal on R^14 = R^{2*7}.")
    print("  - R^14 = C^7 via J (seven complex dimensions).")
    print("  - Adams' theorem on S^13: rho(14) - 1 = 1.  PR #105 closure:")
    print("    J|_{S^13} IS the Adams field (up to scale), since")
    print("    <Jx, x> = 0 and |Jx| = 1.")
    print("  - U(1) acts on C^7 by exp(theta J).")
    print()
    print("Numerical sanity:")
    rho14 = radon_hurwitz(14)
    n = 7
    J = build_J(n)
    JJ = J @ J
    print(f"  rho(14) = {rho14};  rho(14) - 1 = {rho14 - 1}  (matches 1 = dim U(1))")
    print(f"  R^14 dimension = 14 = 2 * 7 = dim(C) * 7  (J-complex decomposition)")
    print(f"  ||J^2 + I||_F = {np.linalg.norm(JJ + np.eye(2*n)):.2e}  (J^2 = -Id)")
    print()

    # Verify J's eigenvalues are exactly +/- i
    eigvals = np.linalg.eigvals(J)
    plus_i = np.sum(np.isclose(eigvals.imag, +1.0) & np.isclose(eigvals.real, 0.0))
    minus_i = np.sum(np.isclose(eigvals.imag, -1.0) & np.isclose(eigvals.real, 0.0))
    print(f"  J spectrum on R^14: {plus_i} eigenvalues +i, {minus_i} eigenvalues -i")
    print(f"  (each with multiplicity n = 7 = dim_C C^7)")
    print()
    print("Forcing argument:")
    print("  (1) The cascade space at d=14 is R^14.")
    print("  (2) The cascade complex structure J (forced by precession,")
    print("      Part II) gives R^14 = C^7.")
    print("  (3) Adams' uniqueness on S^13 (rho-1 = 1) + PR #105: the U(1)")
    print("      generated by J|_{S^13} is THE U(1) at d=14.")
    print("  (4) U(1) acts on each complex direction of C^7 with charges")
    print("      +/- 1 (J's eigenvalues).  The fundamental rep of U(1)")
    print("      is 1-dimensional.")
    print("  (5) Matter at d=14 embeds in C^7 = 7 copies of the 1-dim")
    print("      fundamental rep of U(1).  DIM = 1 is FORCED.")
    print()
    print("Status: PARTIALLY CLOSED.")
    print("  - DIMENSION of fundamental rep (1) FORCED by Bott + J + Adams.")
    print("  - SPECIFIC CHARGES SM Y in {-1, -1/2, -1/3, +1/6, +2/3, +1}")
    print("    NOT FORCED by this argument (J's eigenvalues are +/- 1,")
    print("    not fractional).  PR #105 finding (B): the SM Y-spectrum")
    print("    requires a separate derivation (anomaly cancellation,")
    print("    embedding into a rep that picks specific Y values, etc.).")
    print()


# ---------------------------------------------------------------------------
# d=13 case: SU(2) doublet structure -- OPEN
# ---------------------------------------------------------------------------

def d13_su2_open() -> None:
    print("-" * 78)
    print("d=13 (SU(2)): doublet structure NOT cleanly forced (OPEN)")
    print("-" * 78)
    print()
    print("Cascade ingredients:")
    print("  - Cascade space at d=13: V_{13} = R^13.")
    print("  - R^13 is odd-real-dimensional; no clean Bott decomposition")
    print("    of the WHOLE space (no R^13 = C^? structure since 13 is odd).")
    print("  - Spinor type at d=13 (Part IVa Section 2.1, Lounesto data):")
    print("    Cl(1,12) = M_4(C) gives complex Dirac spinor of dim 4")
    print("    (4 complex components).")
    print("  - Adams' theorem at d=13: rho(13) - 1 = 0  (no nowhere-zero")
    print("    tangent field on S^12; hairy-ball obstruction).")
    print("  - SU(2) at d=13 is broken (Part IVa thm:breaking, Lefschetz")
    print("    obstruction).")
    print()
    print("Numerical sanity:")
    rho13 = radon_hurwitz(13)
    print(f"  rho(13) = {rho13};  rho(13) - 1 = {rho13 - 1}  (no cascade")
    print(f"    nowhere-zero tangent field; hairy ball forces SU(2) breaking)")
    print(f"  R^13 dimension = 13 = prime, no clean complex/quaternionic")
    print(f"    decomposition (gcd(13, 2) = {math.gcd(13, 2)},")
    print(f"    gcd(13, 4) = {math.gcd(13, 4)}).")
    print(f"  Dirac spinor at d=13: 4 complex components (Weyl + anti-Weyl,")
    print(f"    each 2 complex).  SU(2)'s fundamental rep is 2-complex-dim.")
    print()
    print("Forcing argument (incomplete):")
    print("  (1) The 4-complex-dim Dirac spinor at d=13 decomposes by")
    print("      chirality as Weyl + anti-Weyl, each 2-complex-dim.")
    print("  (2) A 2-complex-dim Weyl is the natural carrier of SU(2)'s")
    print("      fundamental rep (since SU(2) ~= Spin(3), fundamental")
    print("      action on C^2).")
    print("  (3) IF SU(2) at d=13 couples to ONE chirality only (the L-Weyl")
    print("      piece of the Dirac), then L is doublet and R is singlet")
    print("      automatically.  This matches the SM parity-violating")
    print("      SU(2)_L pattern.")
    print()
    print("The gap:")
    print("  Step (3) is not derived in Part IVa.  Part IVa Section 2.3")
    print("  line 263-269 explicitly says the chirality structure of each")
    print("  gauge boson's coupling is 'distinct from the Clifford")
    print("  classification' and 'determined separately by the symmetry")
    print("  breaking of Section 3 and the fermion generation structure")
    print("  of Section 4.'  Reading those sections (Section 3:")
    print("  symmetry-breaking pattern theorem; Section 4: generation")
    print("  count from d_1 = 19) does NOT show an explicit derivation")
    print("  of why SU(2) couples only to L.")
    print()
    print("What would close it:")
    print("  A cascade-internal argument that the d=13 hairy-ball forced")
    print("  zero on S^12 selects ONE chirality of the surrounding")
    print("  Weyl-Dirac-Weyl Bott structure -- e.g., that the index")
    print("  (Poincare-Hopf, +1 at the zero) couples to the L-Weyl piece")
    print("  of the d=13 Dirac, leaving the R-Weyl piece SU(2)-singlet.")
    print("  This would tie the parity violation to the hairy-ball")
    print("  obstruction's chirality structure.")
    print()
    print("Status: OPEN.  Doublet DIMENSION suggested by Bott-Weyl projection")
    print("but not forced; chirality SPLIT (L doublet vs R singlet) requires")
    print("separate derivation tying SU(2) coupling to the d=13 hairy-ball")
    print("obstruction's chirality structure.")
    print()


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

def summary() -> None:
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print()
    print("Unified lemma: 'matter at distinguished cascade layer transforms")
    print("in the fundamental rep of the gauge group'")
    print()
    print("  d=12 (SU(3)):  CLOSED structurally.")
    print("                 Mechanism: R^12 = H^3 (Bott class from d=4).")
    print("                 Already implicit in Part IVa rem:su3-d7-algebra")
    print("                 line 519.")
    print()
    print("  d=14 (U(1)):   PARTIALLY CLOSED.")
    print("                 Mechanism: R^14 = C^7 via J (PR #105).")
    print("                 Forced: fundamental rep DIM = 1.")
    print("                 Open: specific charge values (SM Y spectrum).")
    print()
    print("  d=13 (SU(2)):  OPEN.")
    print("                 Bott Weyl-Dirac-Weyl structure suggests 2-complex-dim")
    print("                 doublet from Dirac chirality decomposition;")
    print("                 chirality SPLIT (L doublet vs R singlet) not")
    print("                 derived in Part IVa.")
    print()
    print("Documentation impact: this narrows the matter-rep gap recorded")
    print("in CLAUDE.md (PR #105 commit 1cdf897).  Specifically:")
    print("  - Rep DIMENSION (fundamental vs adjoint) is now closed at")
    print("    d=12 and d=14 explicitly; only d=13 doublet structure")
    print("    remains structurally open.")
    print("  - Rep WEIGHT (specific Y values) remains open at d=14.")
    print()
    print("Recommended next step (option 3 of investigation):")
    print("  Attempt the d=13 closure: connect the hairy-ball obstruction")
    print("  on S^12 to a chirality selection that picks the L-Weyl piece")
    print("  of the d=13 Dirac spinor as the SU(2) doublet, leaving R-Weyl")
    print("  as singlet.  See companion script (or extension of this one)")
    print("  for an attempt.")


def main() -> int:
    print("=" * 78)
    print("CASCADE FUNDAMENTAL-REP LEMMA: status of the rep-choice claim")
    print("at each gauge-window layer")
    print("=" * 78)
    print()

    d12_quaternionic_carrier()
    d14_complex_carrier()
    d13_su2_open()
    summary()
    return 0


if __name__ == "__main__":
    sys.exit(main())
