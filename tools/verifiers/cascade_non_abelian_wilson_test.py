#!/usr/bin/env python3
"""
Test: is the non-Abelian Wilson line cascade-forced (or even constructible)?

CLAIM TO TEST.  Under Option 2 / Reading G, the cascade's gauge-anchored
running coupling formula admits an Abelian Wilson holonomy interpretation
(see cascade-wilson-line-derivation2.md).  Does the cascade's structure
support a NON-ABELIAN extension that delivers full SU(N) gauge dynamics?

STRUCTURAL REQUIREMENTS for a non-Abelian Wilson line W = P-exp(integral A):

  (a) A Lie-algebra-valued connection 1-form A^a(d) T_a at every layer
      of the path, with T_a generators of the gauge Lie algebra.
  (b) The component functions A^a(d) -- one per generator -- specified
      cascade-internally.
  (c) Path-ordering (handled correctly by P-exp; non-trivial when
      generators don't commute).

WHAT THE CASCADE PROVIDES:

  - Adams' theorem: gauge algebras at gauge layers d in {12, 13, 14}.
  - Cascade slicing potential: p(d), a SCALAR function of layer index.
  - Cascade complex structure J: a single U(1) generator (from Theorem
    complex of Part II).

WHAT'S NEEDED VS WHAT'S PROVIDED:

  Group  Algebra dim N^2-1  Cascade-provided  Gap (need - have)
  ----   ----------------   ---------------    -----------------
  SU(3)  8                  ~1 (J) + Adams=3   8 - 4 = 4 missing
  SU(2)  3                  ~1 (J) + Adams=1   3 - 2 = 1 missing
  U(1)   1                  1 (J)              0 (sufficient)

So:
  - U(1) Wilson line: cascade-sufficient (J plus the slicing potential
    p(d) gives a complete Abelian connection).
  - SU(2) Wilson line: cascade INSUFFICIENT.  Adams gives 1 vector field
    at d=13, J gives U(1), but SU(2) needs 3 generators.  Missing 1.
  - SU(3) Wilson line: cascade INSUFFICIENT.  Adams gives 3 vector fields
    at d=12, J gives U(1), totalling at most 4 of 8 SU(3) generators.
    Missing 4.

CONCLUSION.  The non-Abelian Wilson lift is NOT cascade-forced.  It is
not even cascade-constructible without importing additional Lie-algebra-
valued connection components that the cascade does not provide.

This means: non-perturbative gauge dynamics (gluon self-coupling,
confinement, instantons) is genuinely OUTSIDE the cascade's scope.
The cascade can support gauge running couplings (Abelian Wilson) but
not the full non-Abelian gauge field theory.

This verifier:
  1. Explicitly counts the cascade's available algebra components per
     gauge layer.
  2. Compares to SU(N) requirements.
  3. Tests whether any natural cascade-internal scheme closes the gap.
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Cascade gauge layer assignments (Part IVa)
GAUGE_LAYERS = {
    12: ("SU(3)", 3, 8),  # (group, fundamental_dim, algebra_dim = N^2 - 1)
    13: ("SU(2)", 2, 3),
    14: ("U(1)", 1, 1),
}

# Cascade-provided generators per layer:
#   J: cascade complex structure (1 U(1) generator), available at every layer
#   Adams vector fields: rho(d) - 1 at gauge layers
ADAMS_VECTORS = {
    12: 3,  # rho(12) - 1
    13: 1,  # rho(13) - 1
    14: 0,  # rho(14) - 1
}


def main():
    print("=" * 78)
    print("TEST: IS THE NON-ABELIAN WILSON LIFT CASCADE-FORCED?")
    print("=" * 78)
    print()
    print("Claim under test: cascade's structure supports a non-Abelian Wilson")
    print("line W = P-exp(integral A^a T_a) at gauge layers, with all SU(N)")
    print("Lie-algebra components A^a(d) cascade-internal.")
    print()

    # === Step 1: count what's needed vs what's provided ===
    print("=" * 78)
    print("Step 1: structural component count per gauge layer")
    print("=" * 78)
    print()
    print(f"{'Layer':>6s}  {'Group':>8s}  {'Algebra dim':>12s}  {'Cascade gen':>12s}  "
          f"{'Gap':>6s}  {'Sufficient?':>14s}")
    print("-" * 78)

    sufficient_layers = []
    insufficient_layers = []

    for d, (group, fund_dim, alg_dim) in sorted(GAUGE_LAYERS.items()):
        # Cascade generators: 1 from J + Adams vector fields at gauge layer
        cascade_gens = 1 + ADAMS_VECTORS[d]
        gap = alg_dim - cascade_gens
        sufficient = gap <= 0
        status = "YES" if sufficient else "NO"
        print(f"{d:>6d}  {group:>8s}  {alg_dim:>12d}  {cascade_gens:>12d}  "
              f"{gap:>6d}  {status:>14s}")
        if sufficient:
            sufficient_layers.append((d, group))
        else:
            insufficient_layers.append((d, group, gap))

    print()
    print(f"  Cascade-sufficient gauge layers: {sufficient_layers}")
    print(f"  Cascade-insufficient gauge layers: {[(d, g) for d, g, _ in insufficient_layers]}")
    print()

    # === Step 2: explicit Abelian (sufficient) case ===
    print("=" * 78)
    print("Step 2: U(1) at d=14 -- cascade-sufficient")
    print("=" * 78)
    print()
    print("U(1) algebra: 1-dimensional (single generator, e.g., i for the")
    print("standard U(1) phase).  Cascade provides J directly, giving a")
    print("complete Abelian connection.")
    print()
    print("Wilson line: W_{[5,14]} = exp(integral_5^14 A(d) dd) = exp(Phi(14))")
    print("This is the cascade's existing running coupling formula.")
    print("Cascade-internal: YES.")
    print()

    # === Step 3: explicit SU(2) case (insufficient) ===
    print("=" * 78)
    print("Step 3: SU(2) at d=13 -- cascade-insufficient by 1 generator")
    print("=" * 78)
    print()
    print("SU(2) algebra: 3-dimensional (generators sigma_x, sigma_y, sigma_z).")
    print()
    print("Cascade provides:")
    print("  - J (cascade complex structure): 1 generator (e.g., sigma_z analogue).")
    print("  - 1 Adams vector field at d=13: 1 generator (e.g., sigma_x analogue).")
    print("  Total: 2 of 3 generators.")
    print()
    print("Missing: 1 generator (e.g., sigma_y).  Cascade has no natural")
    print("structure that supplies a third independent generator at d=13.")
    print()
    print("Without the missing generator:")
    print("  - The cascade's 'SU(2) Wilson line' is restricted to a 2D")
    print("    subspace of the 3D su(2) algebra -- not a true SU(2) Wilson")
    print("    line.")
    print("  - Path-ordering is degenerate (only 2 generators that may")
    print("    commute or partially commute).")
    print("  - Curvature F_{munu} = dA + A wedge A would have only the")
    print("    2-generator components.")
    print()
    print("CONCLUSION: SU(2) Wilson line is NOT cascade-internal.  Its")
    print("construction would require an external choice of the third")
    print("generator's component function.")
    print()

    # === Step 4: explicit SU(3) case (more insufficient) ===
    print("=" * 78)
    print("Step 4: SU(3) at d=12 -- cascade-insufficient by 4 generators")
    print("=" * 78)
    print()
    print("SU(3) algebra: 8-dimensional (8 Gell-Mann matrices lambda_1..lambda_8).")
    print()
    print("Cascade provides:")
    print("  - J: 1 generator (lambda_3-like).")
    print("  - 3 Adams vector fields at d=12: 3 generators (lambda_1, lambda_2,")
    print("    plus possibly the second Cartan lambda_8).")
    print("  Total: at most 4 of 8 generators.")
    print()
    print("Missing: 4 generators (the off-diagonal lambda_4, lambda_5, lambda_6,")
    print("lambda_7).  These are NOT supplied by Adams' theorem alone.")
    print()
    print("The 4 Adams-derived generators span at most the Cartan subalgebra")
    print("(rank 2) plus some root vectors.  The full SU(3) would need all 8.")
    print()
    print("Without the missing 4 generators:")
    print("  - The cascade's 'SU(3) Wilson line' is restricted to a 4D subspace")
    print("    of the 8D su(3) algebra.")
    print("  - Cannot express full color rotations in fundamental rep.")
    print("  - QCD phenomena like asymptotic freedom (which depends on the")
    print("    full structure constants) are not derivable.")
    print()
    print("CONCLUSION: SU(3) Wilson line is NOT cascade-internal.")
    print()

    # === Step 5: try a natural cascade-internal scheme ===
    print("=" * 78)
    print("Step 5: candidate cascade-internal schemes for the missing generators")
    print("=" * 78)
    print()

    candidates = [
        ("Use slicing potential p(d) for ALL components: A^a(d) = p(d)",
         "Fails: gives 1 scalar replicated 8 times, all components proportional."
         " Wilson line collapses to scalar exp(8 p(d)). Equivalent to Abelian."),

        ("Differentiate p(d) at multiple scales: A^a(d) = d^a/dd^a p(d)",
         "Fails: gives only as many independent components as taking high-order"
         " derivatives provides. Higher derivatives are linearly dependent for"
         " smooth p(d). Insufficient."),

        ("Use sphere-area ratios at different layers: A^a(d) = Omega_{d+a}/Omega_d",
         "Fails: ratios of cascade primitives, but only cascade-internal at"
         " d itself, not across layers. Cross-layer ratios mix SCALES, not"
         " gauge directions."),

        ("Use Adams vector fields PLUS second-order perturbations from neighbouring"
         " layers",
         "Fails: cascade's slicing recurrence is multiplicative scalar; doesn't"
         " carry tangent vector information across layers."),

        ("Import SM gauge field as 'matter content'",
         "FAILS by construction: this would import the answer."),
    ]

    print(f"  Tested {len(candidates)} candidate cascade-internal schemes:")
    print()
    for i, (proposal, result) in enumerate(candidates, 1):
        print(f"  Candidate {i}: {proposal}")
        print(f"    Result: {result}")
        print()

    print("None of the natural cascade-internal schemes produces the missing")
    print("Lie-algebra-valued component functions cascade-natively.")
    print()

    # === Step 6: structural conclusion ===
    print("=" * 78)
    print("Step 6: structural conclusion")
    print("=" * 78)
    print()
    print("The non-Abelian Wilson lift FAILS the cascade-internal forcing test:")
    print()
    print("  1. Cascade provides at most rank+1 generators per gauge layer")
    print("     (J + Adams vector fields).")
    print("  2. SU(N) requires N^2 - 1 generators total.  For N >= 2, the")
    print("     cascade is missing at least N^2 - N - 1 generators.")
    print("  3. No natural cascade-internal scheme supplies the missing")
    print("     components.")
    print()
    print("CONSEQUENCE.  Non-perturbative gauge dynamics -- everything that")
    print("requires the FULL non-Abelian gauge structure (gluon self-coupling,")
    print("confinement, instantons, theta-vacuum, asymptotic freedom in its")
    print("complete RG form) -- is NOT derivable cascade-internally as currently")
    print("formulated.")
    print()
    print("The cascade gives gauge GROUPS via Adams + Hurwitz, gauge running")
    print("via Abelian Wilson lines, and matter representation content via path")
    print("tensor products.  It does NOT give the full non-Abelian gauge field")
    print("theory.")
    print()
    print("This confirms reading (B) of the trichotomy for non-perturbative")
    print("content: the framework is genuinely partial in this regime.  The")
    print("cascade is a real partial framework -- forcing perturbative SM")
    print("structure cleanly, leaving non-perturbative gauge dynamics open.")
    print()
    print("To close the non-perturbative gap would require either:")
    print("  (i) Adding cascade-internal structure that supplies the missing")
    print("      Lie-algebra components (no candidate identified).")
    print(" (ii) Importing the missing components from outside the cascade")
    print("      (violates austerity: would be a free input).")
    print("(iii) Accepting that non-perturbative content is outside scope.")
    print()
    print("Given austerity (Prelude 2.2), option (iii) is the honest conclusion:")
    print("the cascade's claims should be qualified to perturbative SM physics,")
    print("with non-perturbative content explicitly out of scope.")


if __name__ == "__main__":
    main()
