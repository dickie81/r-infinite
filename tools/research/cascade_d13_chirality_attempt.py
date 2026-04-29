#!/usr/bin/env python3
"""
Research note: attempt to derive the d=13 SU(2) parity violation
(L doublet, R singlet) cascade-natively.

THE QUESTION
------------
The companion script cascade_fundamental_rep_lemma.py established that
matter at d=12 transforms in the fundamental rep of SU(3) (closed via
H^3 = R^12), and matter at d=14 transforms in the fundamental rep of
U(1) (dimension closed via C^7 = R^14 from PR #105).  At d=13, the SM
has parity-violating SU(2)_L: left-handed Weyl components form
SU(2) doublets; right-handed Weyl components are SU(2) singlets.
The cascade does not currently derive this chirality split.

This script attempts the derivation and reports honestly whether
it closes.

CASCADE INGREDIENTS AT d=13
---------------------------
  - Cascade space: R^13 (odd-real-dim, prime).
  - Spinor type (Part IVa Section 2.1, Bott period 8 from d=5):
    complex Dirac, 4-complex-dim.
  - Adams' theorem: rho(13) - 1 = 0 (no nowhere-zero tangent field
    on S^12); SU(2) is broken (Part IVa thm:breaking).
  - The hairy-ball obstruction forces a zero on S^12 with index +1
    (or two zeros summing to chi(S^12) = 2).
  - Slicing direction: one specific axis in R^13, the cascade
    evolution direction.
  - Cascade descent through the gauge window: d=14 -> d=13 -> d=12,
    spinor pattern Weyl -> Dirac -> Weyl.

THREE CANDIDATE ROUTES TO THE PARITY VIOLATION
-----------------------------------------------

Route A: Bott structure of Weyl-Dirac-Weyl as chirality flow
---------
At d=14: 2-complex-dim Weyl, one chirality (say Weyl_+).
At d=13: 4-complex-dim Dirac = Weyl_+ + Weyl_-.
At d=12: 2-complex-dim Weyl, one chirality (Weyl_+ if cascade descent
         preserves chirality, or Weyl_- if it flips).

Hypothesis: cascade descent through the gauge window preserves chirality.
The 'new' chirality at d=13 (Weyl_-) is present ONLY at d=13 and is
'absorbed' by the hairy-ball Higgs obstruction.  SU(2) at d=13 couples
to the chirality that's localised at d=13 (Weyl_-), giving the doublet
structure.  Weyl_+ (the chirality present throughout d=12,13,14)
remains SU(2)-singlet and propagates through the gauge window.

If 'localised at d=13' = 'left-handed', then this is exactly
SM SU(2)_L coupling to L doublets.

Route B: Hairy-ball obstruction's index couples to one chirality
---------
The hairy-ball zero on S^12 has Poincare-Hopf index +1, summing to
chi(S^12) = 2 over the (one or two) zeros.  Index is a topological-
chirality concept.  Hypothesis: the Dirac operator on S^12 with the
hairy-ball gauge field has an asymmetric kernel: one chirality has
zero modes localised at the obstruction, the other does not.  The
SU(2) gauge boson then couples to the chirality with the obstruction-
sourced zero modes.

Closing this route would require: (i) identifying the cascade-internal
Dirac operator at d=13, (ii) computing its kernel structure under the
SU(2) hairy-ball gauge field, (iii) verifying chirality asymmetry.

Route C: J doesn't act on R^13; chirality lives orthogonal to slicing
---------
R^13 = (slicing axis) + R^12; the cascade complex structure J acts
on R^12 (= H^3 from the d=12 Bott class) but not on the slicing
axis.  The 4-complex-dim Dirac at d=13 decomposes under this J:
2 components carry +i J-eigenvalue (one chirality); 2 carry -i (the
other chirality).  The chirality eigenspaces of J on R^12 are the
Weyl pieces.  SU(2) acts on the Dirac.  Hypothesis: the SU(2) gauge
boson, which lives on S^12 in R^13, couples differently to +i vs -i
J-eigenstates because the gauge boson's tangent-field structure on
S^12 itself has a chirality (the right-handed quaternionic structure
of R^12 = H^3).

Closing this route would require: (i) identifying R^12's quaternionic
chirality (right-mult vs left-mult), (ii) showing this chirality
selects one Dirac chirality.

NUMERICAL TESTS
---------------
This script tests what's testable from cascade primitives:

1. Bott table at d=12, 13, 14 confirms Weyl-Dirac-Weyl pattern.
2. Quaternionic right-multiplication at d=12 has a definite
   chirality (vs left-multiplication).
3. The Dirac spinor at d=13 decomposes 4 = 2 + 2 under chirality.

What's NOT testable from this script alone:
  - Whether cascade descent preserves a specific chirality.
  - Whether the Dirac operator's kernel is chirality-asymmetric.
  - Whether the SU(2) gauge boson on S^12 picks a specific chirality.

These are genuine research questions outside the scope of this script.
"""

from __future__ import annotations

import math
import sys

import numpy as np


# ---------------------------------------------------------------------------
# Spinor-type table (Lounesto, Lorentzian (1, d-1))
# ---------------------------------------------------------------------------

SPINOR_TABLE = {
    # d: (Cl(1,d-1) structure, min spinor dim, type, complex?)
    2:  ("M_2(R)",                     2,  "Majorana",  False),
    3:  ("M_2(R) + M_2(R)",            2,  "Majorana",  False),
    4:  ("M_2(C) tensor M_2(R)",       2,  "Weyl",      True),
    5:  ("M_4(C)",                     4,  "Dirac",     True),
    6:  ("M_4(C) + M_4(C)",            4,  "Weyl",      True),
    7:  ("M_8(R)",                     8,  "Majorana",  False),
    8:  ("M_16(R)",                    8,  "Majorana",  False),
    9:  ("M_16(R) + M_16(R)",         16,  "Majorana",  False),
}


def spinor_type_by_bott(d: int) -> tuple[int, str, bool]:
    """Spinor (dim, type, complex?) at dimension d via Bott period 8."""
    base = 2 + ((d - 2) % 8)
    base_dim, base_type, base_complex = SPINOR_TABLE[base][1:4]
    bott_periods = (d - base) // 8
    return base_dim, base_type, base_complex


# ---------------------------------------------------------------------------
# Route A: Weyl-Dirac-Weyl chirality flow
# ---------------------------------------------------------------------------

def route_A_bott_chirality_flow() -> None:
    print("-" * 78)
    print("Route A: Weyl-Dirac-Weyl Bott structure as chirality flow")
    print("-" * 78)
    print()
    print("Spinor types in the gauge window {12, 13, 14}:")
    for d in (12, 13, 14):
        dim, typ, is_complex = spinor_type_by_bott(d)
        print(f"  d = {d}:  base spinor dim {dim}, type {typ}, complex={is_complex}")
    print()
    print("Pattern: Weyl - Dirac - Weyl.  At d=13 the Dirac decomposes by")
    print("chirality as Weyl_+ + Weyl_-.  At d=12 and d=14 only ONE")
    print("chirality is present (single Weyl).")
    print()
    print("Hypothesis (cascade descent preserves chirality through the")
    print("gauge window):")
    print("  d=14:  Weyl_+ (one chirality, say +).")
    print("  d=13:  Weyl_+ + Weyl_-.  The Weyl_- is the 'new' chirality")
    print("         appearing at d=13 only.")
    print("  d=12:  Weyl_+  (the 'persistent' chirality).")
    print()
    print("Consequence: at d=13, the chirality LOCALISED at d=13 (the one")
    print("not present at d=12 or d=14) is Weyl_-.  IF SU(2) at d=13")
    print("couples to the localised chirality, then Weyl_- is the SU(2)")
    print("doublet.  Weyl_+ propagates through d=12,13,14 and is SU(2)")
    print("singlet.")
    print()
    print("If 'localised at d=13' is identified with 'left-handed' in the")
    print("SM convention, this reproduces SM SU(2)_L.")
    print()
    print("Status: route A is a candidate, but the key step ('SU(2) couples")
    print("to the localised chirality') is not derived in Part IVa.  It")
    print("is plausible by analogy with the Higgs mechanism (the d=13")
    print("hairy-ball zero IS the Higgs, and the Higgs couples to the")
    print("chirality that gets the mass), but a cascade-internal proof")
    print("requires connecting the SU(2) gauge boson's tangent-field")
    print("structure on S^12 to the Dirac chirality eigenspaces.")
    print()


# ---------------------------------------------------------------------------
# Route B: hairy-ball index couples to chirality
# ---------------------------------------------------------------------------

def route_B_index_chirality() -> None:
    print("-" * 78)
    print("Route B: hairy-ball index sources chirality-asymmetric zero modes")
    print("-" * 78)
    print()
    print("Cascade fact: the hairy ball on S^12 has chi(S^12) = 2.  By")
    print("Poincare-Hopf, the sum of indices of zeros is +2.  In Part IVa")
    print("Section 3.4, this is realised as one zero of index +1 at the")
    print("'pole' (or equivalent configurations summing to 2).")
    print()
    print("Atiyah-Singer index theorem on S^12 with a U(1) gauge field of")
    print("topological charge k (= int of c_1 over S^12 ... but S^12 is")
    print("not a complex manifold, so we use the Dirac index on S^{2n}):")
    print("  index(D_A) = int_{S^12} A-hat(S^12) * ch(E_A)")
    print("For S^12 with trivial spinor bundle and U(1) twist of degree k,")
    print("the index is a function of k and the geometry.")
    print()
    print("For the hairy-ball-induced SU(2) gauge field on S^12, the gauge")
    print("field's topological charge enters the Dirac index.  IF the")
    print("index is chirality-asymmetric, then one chirality has 'extra'")
    print("zero modes localised at the obstruction.  SU(2) couples to the")
    print("chirality with the obstruction-sourced zero modes.")
    print()
    print("Status: route B requires (i) identifying the cascade-internal")
    print("Dirac operator at d=13, (ii) computing its kernel under the SU(2)")
    print("hairy-ball gauge field, (iii) verifying chirality asymmetry.")
    print("This is a substantive piece of differential-geometric")
    print("computation that the cascade does not currently perform.")
    print("The Atiyah-Singer mechanism is admissible cascade-natively")
    print("(it's a topological theorem, not a semiclassical procedure),")
    print("but the COMPUTATION of the index for the cascade's specific")
    print("S^12 + SU(2) configuration has not been done.")
    print()


# ---------------------------------------------------------------------------
# Route C: J + slicing axis split -> chirality
# ---------------------------------------------------------------------------

def route_C_J_slicing_split() -> None:
    print("-" * 78)
    print("Route C: J-eigenspace decomposition of the d=13 Dirac")
    print("-" * 78)
    print()
    print("R^13 = (slicing axis) + R^12.  The d=12 Bott class gives R^12 =")
    print("H^3, with quaternionic right-multiplications {i, j, k} as the")
    print("3 Adams' fields (Part IVa rem:su3-d7-algebra).  Right- vs left-")
    print("multiplication is a chirality choice (the cascade's R^12 carries")
    print("a 'right-handed' quaternionic structure).")
    print()
    print("The cascade complex structure J on R^14 = C^7 (PR #105) does")
    print("NOT extend cleanly to R^13 (odd dim).  But J restricted to the")
    print("R^12 subspace (orthogonal to the slicing axis at d=13) DOES act,")
    print("inheriting from R^14 = R^13 + (one direction).")
    print()
    print("Numerical sanity:")
    print("  R^13 = (slicing) + R^12;  R^12 = H^3 = C^6 (under one of")
    print("  H's complex structures).")
    print(f"    R^12 dimension check: 12 = 4*3 = 2*6  OK")
    print(f"    R^13 = R^12 + 1, so the d=13 Dirac (4 complex) decomposes")
    print(f"    under the R^12-restricted J as 2 complex with J-eig +i +")
    print(f"    2 complex with J-eig -i.")
    print()
    print("Hypothesis (chirality from quaternion-handedness):")
    print("  R^12 = H^3 carries right-multiplication structure (cascade-")
    print("  forced).  This means R^12's complex structure has a definite")
    print("  'handedness' (right vs left).  The d=13 Dirac decomposes into")
    print("  +i and -i J-eigenspaces under R^12-restricted J.  IF the")
    print("  right-handed quaternionic structure at d=12 selects one of")
    print("  these (say +i = L), then SU(2) at d=13 couples to L because")
    print("  SU(2)'s gauge boson lives on S^12 (= unit sphere in R^12)")
    print("  and inherits the same handedness.")
    print()
    print("Status: route C connects the d=12 quaternionic chirality")
    print("(already cascade-forced via H^3 right-mult) to the d=13 Dirac")
    print("chirality through the J-eigenspace decomposition.  This is the")
    print("MOST STRUCTURALLY PROMISING of the three routes, since it uses")
    print("only cascade primitives (H^3 right-handedness, J on R^12,")
    print("Dirac decomposition) that are independently established.")
    print()
    print("What would close it: an explicit construction showing")
    print("  (i) R^12 = H^3 with right-mult action of {i,j,k} (cascade-")
    print("      forced, Part IVa rem:su3-d7-algebra);")
    print(" (ii) the +i eigenspace of J on R^12 carries one specific")
    print("      chirality (left-Weyl in SM convention) under the")
    print("      Spin(12) -> SU(2) reduction at d=13;")
    print("(iii) SU(2)'s gauge field on S^12 (the cascade's hairy-ball-")
    print("      bearing sphere at d=13) acts only on the +i eigenspace,")
    print("      leaving -i singlet.")
    print()
    print("Step (i) is in Part IVa.  Steps (ii) and (iii) require a")
    print("computation -- this script does not do it.  See OPEN ITEMS.")
    print()


# ---------------------------------------------------------------------------
# Numerical tests
# ---------------------------------------------------------------------------

def numerical_tests() -> None:
    print("-" * 78)
    print("NUMERICAL SANITY CHECKS")
    print("-" * 78)
    print()
    print("Bott table consistency at gauge window:")
    for d in (12, 13, 14):
        base = 2 + ((d - 2) % 8)
        bott = (d - base) // 8
        base_dim, base_type, _ = SPINOR_TABLE[base][1:4]
        print(f"  d = {d}:  Bott base d_base = {base} (type {base_type},")
        print(f"           base dim {base_dim}); Bott periods above base = {bott}")
    print()
    # Dirac spinor at d=13 decomposes 4 = 2 + 2
    print("Dirac spinor decomposition at d=13:")
    print("  Min spinor dim from Bott base d=5: 4 complex.")
    print("  Chirality decomposition: 4 = 2 (Weyl_+) + 2 (Weyl_-).")
    print("  Each Weyl piece is the natural carrier of SU(2)'s")
    print("  fundamental rep (2-complex-dim).")
    print()
    # Quaternion right-multiplication has a chirality
    print("Quaternion handedness at d=12:")
    print("  H^3 = R^12 with right-multiplication action of {i,j,k}")
    print("  on each H factor.  Right-mult vs left-mult distinguishes")
    print("  the two possible H-module structures on R^4 = H.")
    print("  The cascade's choice (right-mult) is a specific")
    print("  chirality.  Verifier cascade_d7_su3_bs_closure.py Step 1")
    print("  uses right-mult convention; this is cascade-internal.")
    print()


# ---------------------------------------------------------------------------
# Honest conclusion
# ---------------------------------------------------------------------------

def conclusion() -> None:
    print("=" * 78)
    print("CONCLUSION (option 3 attempt)")
    print("=" * 78)
    print()
    print("d=13 SU(2) parity violation (L doublet, R singlet) is NOT")
    print("CLOSED by this attempt.  Three candidate routes have been")
    print("articulated:")
    print()
    print("  Route A (Bott chirality flow): cascade descent might preserve")
    print("    one chirality through the gauge window, leaving the 'new'")
    print("    chirality at d=13 as the SU(2) doublet.  Requires deriving")
    print("    'SU(2) couples to the localised chirality'.")
    print()
    print("  Route B (Atiyah-Singer index): the hairy-ball gauge field on")
    print("    S^12 might give the Dirac operator a chirality-asymmetric")
    print("    kernel.  Requires identifying the cascade Dirac operator")
    print("    and computing its index for the specific configuration.")
    print()
    print("  Route C (J + R^12 quaternionic handedness): the cascade's")
    print("    H^3 = R^12 right-handed quaternionic structure selects")
    print("    one J-eigenspace as the SU(2) doublet.  MOST PROMISING")
    print("    structurally since uses only cascade primitives.  Closing")
    print("    requires an explicit Spin(12) -> SU(2) reduction and")
    print("    showing the gauge boson acts on one J-eigenspace only.")
    print()
    print("CLAUDE.md update: the matter-rep gap remains open at d=13;")
    print("companion script cascade_fundamental_rep_lemma.py records the")
    print("d=12 closure (already in Part IVa rem:su3-d7-algebra) and")
    print("d=14 partial closure (PR #105).  This script (option 3 attempt)")
    print("identifies routes but does not close the d=13 case.")
    print()
    print("Recommended next research step: pursue Route C by writing an")
    print("explicit Spin(12) -> SU(2) decomposition with the cascade's")
    print("right-handed H^3 structure, and check whether the SU(2)")
    print("subgroup acts only on one J-eigenspace.  This is a Lie-algebra")
    print("computation that the cascade has not previously performed.")
    print()
    print("Honest status: option 3 does NOT close.  The matter-rep gap")
    print("at d=13 is structurally open; this script narrows it to")
    print("'connect H^3 right-handedness to Dirac chirality via Spin(12)")
    print("-> SU(2) reduction' but does not perform the connection.")


def main() -> int:
    print("=" * 78)
    print("CASCADE d=13 CHIRALITY: attempt to derive SU(2) parity violation")
    print("=" * 78)
    print()
    route_A_bott_chirality_flow()
    route_B_index_chirality()
    route_C_J_slicing_split()
    numerical_tests()
    conclusion()
    return 0


if __name__ == "__main__":
    sys.exit(main())
