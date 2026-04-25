#!/usr/bin/env python3
"""
Investigation: does Bott-shift transport quaternionic structure from d=4
to give SU(2) at d=13?

CLAIM TO TEST.  At the close of cascade-non-abelian-wilson-test.md, the
most concrete cascade-internal candidate for supplying missing Lie-algebra
components was: "Bott-shift transport from Hurwitz layer to gauge layer."
For SU(2) at d=13: quaternions at d=4 (Hurwitz) Bott-shifted to d=13
should give 3 = dim(su(2)) generators.

This script tests:
  1. Bott-shift arithmetic: does d=13 cleanly arise as a Bott-image of d=4?
  2. Whether Bott periodicity (K-theoretic) supplies Lie-algebra components.
  3. The actual cascade-internal generator count at d=13.

RESULT: NEGATIVE.

Three reasons:
  (a) Bott arithmetic mismatch: d=13 - d=4 = 9, not 8.  d=12 IS the
      Bott image of d=4 (8 layers up), but cascade puts SU(3) at d=12,
      not SU(2).  d=13 is one layer past the Bott image.

  (b) Bott periodicity is K-theoretic (cohomological).  It says topological
      invariants repeat every 8 layers, which is what predicts ρ(d) values.
      It does NOT supply additional Lie-algebra-valued component functions
      that aren't already accounted for by Adams.

  (c) The cascade's structure at d=13 supplies at most rank-2 Abelian
      content (J + 1 Adams vector field), not the 3-dim non-Abelian
      su(2).  At d=12, even with 3 Adams vector fields, these may form
      a 3-dim Lie algebra (e.g., su(2) from quaternionic structure)
      but NOT the 8-dim su(3) that SU(3) requires.

Net: the cascade cannot supply the missing Lie-algebra components from
Bott-shift transport.  The gauge group identifications in Part IVa may
themselves be overclaiming relative to what the cascade strictly derives.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def main():
    print("=" * 78)
    print("INVESTIGATION: Bott-shift transport for SU(2) at d=13")
    print("=" * 78)
    print()

    # === Step 1: Bott arithmetic ===
    print("=" * 78)
    print("Step 1: Bott-shift arithmetic")
    print("=" * 78)
    print()
    print("Hurwitz dimensions: {1, 2, 4, 8} (parallelisable spheres).")
    print("Bott period: 8.")
    print()
    print("Bott images of d=4 (quaternion layer): d=4, 12, 20, 28, ...")
    print()
    print("Cascade gauge layer assignments (Part IVa):")
    print("  d=12: SU(3)  -- coincides with Bott image of d=4 (quaternions)")
    print("  d=13: SU(2)  -- one layer PAST the Bott image; NOT a Bott image of d=4")
    print("  d=14: U(1)   -- two layers past")
    print()
    print("Mismatch:")
    print("  - d=12 is Bott image of d=4, but cascade puts SU(3) (related to")
    print("    OCTONIONS, not quaternions) there.")
    print("  - d=13 is not a Bott image of any Hurwitz dimension.")
    print()
    print("If Bott-shift transported Hurwitz structure cleanly:")
    print("  - d=12 should carry quaternionic structure -> SU(2)/Sp(1) (3-dim).")
    print("  - But cascade claims SU(3) (8-dim) at d=12.")
    print("  - Where do the extra 5 generators come from?  Not from Bott shift.")
    print()
    print("Conversely:")
    print("  - d=13 is not Bott image of any Hurwitz layer.  No quaternionic")
    print("    structure to transport.")
    print()
    print("VERDICT: Bott-shift transport doesn't cleanly map cascade gauge")
    print("layers to Hurwitz division algebras.  The arithmetic doesn't work.")
    print()

    # === Step 2: K-theory vs Lie algebra ===
    print("=" * 78)
    print("Step 2: Bott periodicity is K-theoretic, not Lie-algebra-supplying")
    print("=" * 78)
    print()
    print("Bott periodicity statement: KO^{n+8}(X) = KO^n(X) for any space X.")
    print("This is a cohomological / K-theoretic fact about topological")
    print("invariants.  It predicts:")
    print("  - The structure of K-theory groups repeats every 8 dimensions.")
    print("  - The number of non-vanishing tangent vector fields rho(d) is")
    print("    determined by this periodicity (Adams' theorem).")
    print()
    print("It does NOT predict:")
    print("  - Lie-algebra-valued connection components A^a(d) on cascade paths.")
    print("  - Additional generators beyond rho(d) - 1 at gauge layers.")
    print("  - Non-Abelian structure constants that the cascade hasn't separately")
    print("    derived.")
    print()
    print("So Bott periodicity, even if cleanly applicable, would NOT supply")
    print("additional Lie-algebra components.  The cascade's existing rho(d)")
    print("count already exhausts what Bott periodicity provides.")
    print()
    print("VERDICT: Even if Bott arithmetic worked, the mechanism is wrong --")
    print("Bott periodicity doesn't add Lie components, just predicts vector")
    print("field counts that Adams already specifies.")
    print()

    # === Step 3: actual cascade-internal generators at d=13 ===
    print("=" * 78)
    print("Step 3: cascade-internal generator count at d=13 (sharply)")
    print("=" * 78)
    print()
    print("At d=13, cascade provides:")
    print("  - J (cascade complex structure from Theorem complex of Part II):")
    print("    1 generator, the U(1) action on the state space's complex")
    print("    structure.  Acts on R^{state-space-dim} via multiplication by i.")
    print()
    print("  - Adams vector field at d=13: 1 vector field on S^{12}, from")
    print("    Adams' theorem.  Acts on the boundary sphere as a tangent")
    print("    vector field.")
    print()
    print("Are J and the Adams vector field INDEPENDENT generators?")
    print()
    print("  - J acts on the state space's complex structure (intrinsic to the")
    print("    state vector).")
    print("  - Adams vector field acts on the sphere's tangent bundle (extrinsic")
    print("    to the state vector, intrinsic to the boundary geometry).")
    print()
    print("  These are different actions, but their LIE BRACKET structure is")
    print("  not specified by the cascade.  If they commute, they generate")
    print("  U(1) x U(1) = T^2 (2-dim Abelian).  If not, they generate some")
    print("  3-dim Lie algebra (which could be su(2), so(3), or non-semisimple).")
    print()
    print("Either way, cascade gives at most 2 generators at d=13.")
    print("SU(2) needs 3 generators.  Missing at least 1.")
    print()
    print("VERDICT: Even with the most generous reading (J and Adams independent")
    print("and forming a 3-dim Lie algebra under their non-trivial brackets),")
    print("the cascade gives at most 2 + their bracket = 3 generators.")
    print("Whether this 3-dim algebra is actually su(2) is undetermined --")
    print("the cascade doesn't specify the Lie bracket structure cascade-")
    print("internally.")
    print()

    # === Step 4: implications for d=12 (SU(3)) ===
    print("=" * 78)
    print("Step 4: implications for the SU(3) claim at d=12")
    print("=" * 78)
    print()
    print("At d=12, cascade provides:")
    print("  - J: 1 generator.")
    print("  - 3 Adams vector fields on S^{11}: 3 generators.")
    print("  Total: at most 4 generators.")
    print()
    print("SU(3) requires 8 generators.  Missing 4.")
    print()
    print("Even if the 3 Adams vector fields form a 3-dim non-Abelian Lie")
    print("algebra (e.g., su(2) from quaternionic structure on H^3 x S^11),")
    print("the cascade's d=12 algebra is at most 4-dim (J + su(2)) = u(2).")
    print()
    print("u(2) is NOT su(3).  They have different ranks (u(2) has rank 2,")
    print("same as su(3), but different dimension: u(2) is 4-dim, su(3) is")
    print("8-dim).")
    print()
    print("So the cascade's claim 'SU(3) at d=12' is plausibly overclaiming:")
    print("the natural cascade-internal Lie algebra at d=12 is u(2), not")
    print("su(3).  The 5 additional generators of su(3) (or 4 if we allow")
    print("J already in u(2)) are NOT cascade-internal.")
    print()
    print("This conflicts with Part IVa's interpretation but is consistent")
    print("with the non-Abelian Wilson finding that the cascade doesn't")
    print("supply enough Lie-algebra components for the full SM gauge group.")
    print()

    # === Step 5: structural conclusion ===
    print("=" * 78)
    print("Step 5: structural conclusion")
    print("=" * 78)
    print()
    print("Three layers of negative result:")
    print()
    print("  (a) Bott-shift arithmetic does not cleanly map Hurwitz dimensions")
    print("      to cascade gauge layers.  The proposed mechanism (d=4 quaternion")
    print("      -> d=13 SU(2) via Bott shift) doesn't even arithmetically work.")
    print()
    print("  (b) Bott periodicity is K-theoretic; it does not supply Lie-algebra")
    print("      components.  Even if (a) worked arithmetically, the mechanism")
    print("      would be wrong.")
    print()
    print("  (c) The cascade's own gauge group identifications (SU(3) at d=12,")
    print("      SU(2) at d=13) may themselves overclaim relative to what the")
    print("      cascade strictly derives.  The cascade-internal Lie algebra at")
    print("      d=12 is at most u(2) (4-dim), not su(3) (8-dim).  At d=13,")
    print("      cascade gives at most a 3-dim algebra of unspecified Lie")
    print("      structure, not necessarily su(2).")
    print()
    print("CONSEQUENCE FOR THE PROGRAM.")
    print()
    print("The non-Abelian gauge dynamics gap is not just unfilled by Bott")
    print("transport -- it is structurally outside what the cascade can deliver.")
    print("Furthermore, the existing gauge group identifications in Part IVa")
    print("rely on more than what the cascade strictly forces.")
    print()
    print("Concretely:")
    print("  - Cascade derives ENERGIES of gauge layers (Adams gives rho(d)-1).")
    print("  - Cascade derives BROKEN/UNBROKEN status (hairy ball at even spheres).")
    print("  - Cascade does NOT derive the SPECIFIC GROUP STRUCTURE; SM is")
    print("    used to identify the broken/unbroken structures with SU(N) groups.")
    print()
    print("For full austerity compliance (Prelude 2.2), Part IVa's gauge group")
    print("derivations should be qualified:")
    print("  - 'The cascade derives 3 colours at d=12, 1 at d=13, 0 at d=14,")
    print("    with broken/unbroken status from hairy ball; the identification")
    print("    with SU(3) x SU(2) x U(1) is the SM-consistent fit, not strictly")
    print("    cascade-forced.'")
    print()
    print("This is a meaningful narrowing of the cascade's claim.  The")
    print("framework still derives substantial SM structure (number of colors,")
    print("gauge layer placement, broken/unbroken pattern), but the specific")
    print("SU(N) groups are SM-imported, not cascade-derived.")
    print()
    print("Tier implication: Tier 1 'Gauge group SU(3) x SU(2) x U(1)' should")
    print("arguably be split:")
    print("  - Tier 1: 'Three gauge layers with multiplicities 3, 1, 0 at")
    print("    d=12, 13, 14 from Adams + Bott' -- forced.")
    print("  - Tier 2-3: 'Identification as SU(3) x SU(2) x U(1)' -- SM-")
    print("    consistent, not cascade-forced beyond the multiplicities.")


if __name__ == "__main__":
    main()
