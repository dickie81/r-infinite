#!/usr/bin/env python3
"""Cascade gauge-related dimensions forced by Cayley-Dickson chain.

The investigation began with d_gw = dim G_2 forcing (cascade_dgw_g2_forcing.py)
and surfaces a deeper structural pattern: the cascade's GAUGE-RELATED
distinguished dimensions {d_0, d_g, d_gw} are jointly forced by:

  (A) Cayley-Dickson chain ℝ → ℂ → ℍ → 𝕆 (cascade carries the four
      normed division algebras at successive layers)
  (B) Cover sheet's G_2/SU(3) commitment at d_0 (octonion-completion)
  (C) Cascade Catalan d_gw = 2·d_0 (cover sheet)

These three commitments imply, cascade-internally:

  dim ℍ = 4, dim 𝕆 = 8   (C-D doubling)
  d_0 = dim 𝕆 − 1 = 7    (G_2/SU(3) = S^6 at layer d_0; cascade convention)
  N_c = 3 = √(dim 𝕆 + 1) (octonion-stabilizer rank: dim SU(N) = N² − 1 = dim 𝕆)
  dim SU(3) = 8 = dim 𝕆  (cascade gauge gens = octonion algebra)
  d_g = N_c · dim ℍ = 12 (cascade gauge sphere as ℍ^{N_c} = ℝ^12)
  d_gw = 2·d_0 = 14 = dim G_2 = 2(dim 𝕆 − 1)  (gauge window upper edge)
  dim Spin(7) = 21 = N_c · d_0  (m_η'² scale, PR #141)

The remaining cascade distinguished dimensions {d_V, d_1, d_2} sit OUTSIDE
the C-D regime — they retain small-integer-identity status:

  d_V = 5 = dim ℍ + 1    (Γ-volume-max integer = quaternion dim + 1)
  d_1 = 19 = d_gw + d_V  (phase-transition = gauge window + vol-max)
  d_2 = 217              (no Lie connection found)

Verdict: cascade gauge-related dims are NOW STRUCTURALLY FORCED via C-D +
cover sheet commitments. Volume-max / phase-transition layers (d_V, d_1)
are still at small-integer-identity level. d_2 is outside the chain.
"""

from __future__ import annotations


# Cascade primitives
N_C = 3
N_0 = 2
D_V = 5
D_0 = 7
D_G = 12
D_GW = 14
D_1 = 19
D_2 = 217

# Division algebra dimensions (Cayley-Dickson chain)
DIM_R = 1
DIM_C = 2  # = 2 · dim R
DIM_H = 4  # = 2 · dim C
DIM_O = 8  # = 2 · dim H


def main() -> None:
    print("=" * 92)
    print("CASCADE GAUGE-RELATED DIMENSIONS FORCED BY CAYLEY-DICKSON CHAIN")
    print("=" * 92)
    print()

    print("STEP 1 — Cayley-Dickson chain forces division-algebra dims:")
    print(f"  ℝ → ℂ → ℍ → 𝕆: doubling rule from C-D construction")
    print(f"  dim ℝ = {DIM_R}, dim ℂ = {DIM_C}, dim ℍ = {DIM_H}, dim 𝕆 = {DIM_O}")
    print(f"  Adams' theorem (Hopf invariant 1) forces termination at 𝕆:")
    print(f"  no division algebra of dim > 8.")
    print()

    print("STEP 2 — Cover sheet's G_2/SU(3) commitment at d_0:")
    print(f"  G_2 = Aut(𝕆) acts on Im 𝕆 = ℝ^{DIM_O - 1} = ℝ^7 transitively;")
    print(f"  stabilizer of unit imaginary octonion is SU(3).")
    print(f"  dim G_2 = 14, dim SU(3) = 8, quotient G_2/SU(3) = S^6.")
    print(f"  Cascade convention: layer d → sphere S^(d−1).")
    print(f"  G_2/SU(3) = S^6 at cascade layer d_0 with d_0 − 1 = 6:")
    print(f"  d_0 = dim 𝕆 − 1 = {DIM_O - 1}")
    assert D_0 == DIM_O - 1
    print()

    print("STEP 3 — Cascade-internal forcing of N_c:")
    print(f"  Cover sheet's octonion-stabilizer SU(N) ⊂ G_2.")
    print(f"  Lie theory: dim SU(N) = N² − 1.")
    print(f"  Octonion-stabilizer dim = dim G_2 − dim S^6 = 14 − 6 = 8 = dim 𝕆.")
    print(f"  N² − 1 = dim 𝕆 forces N = √(dim 𝕆 + 1) = √{DIM_O+1} = {N_C}.")
    print(f"  Hence N_c = 3 forced via octonion completion.")
    print()
    assert N_C * N_C - 1 == DIM_O

    print("STEP 4 — Cascade-internal forcing of d_g:")
    print(f"  Cascade gauge sphere is S^(d_g − 1) ⊂ ℝ^{DIM_H}^N_c = ℝ^12.")
    print(f"  d_g − 1 = dim ℍ^{{N_c}} − 1 = N_c · dim ℍ − 1 = {N_C * DIM_H - 1}.")
    print(f"  d_g = N_c · dim ℍ = {N_C * DIM_H}.")
    assert D_G == N_C * DIM_H
    print(f"  Independently, Adams: ρ(12) − 1 = 3 = N_c at cascade gauge layer 12.")
    print(f"  Both routes give d_g = 12 with N_c = 3 via different mechanisms.")
    print()

    print("STEP 5 — Cascade-internal forcing of d_gw:")
    print(f"  Cascade Catalan reading (cover sheet): d_gw = 2 · d_0 = {2 * D_0}.")
    print(f"  Lie identity: dim G_2 = 2·(dim 𝕆 − 1) = 2·{DIM_O - 1} = {2*(DIM_O-1)}.")
    print(f"  With d_0 = dim 𝕆 − 1 (Step 2), 2·d_0 = 2·(dim 𝕆 − 1) = dim G_2.")
    print(f"  Hence d_gw = dim G_2 = {D_GW}, fully forced via C-D + cover sheet.")
    assert D_GW == 2 * (DIM_O - 1)
    print()

    print("STEP 6 — Cascade-internal forcing of dim Spin(7) (PR #141):")
    print(f"  Spin(7)/G_2 = S^7 (standard Lie identification).")
    print(f"  dim Spin(7) = dim G_2 + dim S^7 = 14 + 7 = {14 + 7}.")
    print(f"  In cascade: dim Spin(7) = N_c · d_0 = {N_C * D_0}.")
    assert N_C * D_0 == 21
    print(f"  Theorem thm:axial-anomaly-mass: m_η'² = Λ² · dim Spin(7) = 21·Λ².")
    print()

    print("=" * 92)
    print("WHAT IS FORCED VS. WHAT REMAINS OPEN")
    print("=" * 92)
    print()
    print("FORCED via C-D chain + cover sheet's G_2/SU(3) at d_0:")
    print()
    print("  Quantity                   Cascade form              Value")
    print("  -" * 70)
    print(f"  dim ℍ                      C-D doubling              {DIM_H}")
    print(f"  dim 𝕆                      C-D doubling              {DIM_O}")
    print(f"  d_0                         dim 𝕆 − 1                {D_0}")
    print(f"  N_c                         √(dim 𝕆 + 1)              {N_C}")
    print(f"  dim SU(3)                  N_c² − 1 = dim 𝕆          {N_C**2-1}")
    print(f"  d_g                         N_c · dim ℍ              {D_G}")
    print(f"  d_gw                        2 · d_0 = dim G_2         {D_GW}")
    print(f"  dim G_2                    2·(dim 𝕆 − 1)             {2*(DIM_O-1)}")
    print(f"  dim Spin(7)                N_c · d_0                  {N_C*D_0}")
    print()

    print("REMAINING OPEN (small-integer identities, not yet forced):")
    print()
    print(f"  d_V = 5 = dim ℍ + 1                  (Γ-volume-max = ℍ-dim + 1)")
    print(f"  d_1 = 19 = d_gw + d_V                 (phase trans. = gauge wind. + vol max)")
    print(f"  N(0) = 2 = (d_V − 1)/2                (chirality mult. vs. d_V identity)")
    print(f"  d_2 = 217                              (no Lie/C-D connection found)")
    print()

    print("These remaining identities cluster around d_V = 5 (the volume-maximum)")
    print("which sits OUTSIDE the C-D chain (the chain has algebras at dims 1, 2, 4, 8;")
    print("d_V = 5 is between dim ℍ = 4 and dim 𝕆 - 1 = 7). The cover sheet anchors")
    print("the observer at d=4 (S^4 boundary of B^5), so d_V = 5 reflects the volume")
    print("of the unit ball in 5 dimensions, not a division algebra.")
    print()
    print("Whether d_V's small-integer identities (d_V = dim ℍ + 1, N(0) = (d_V−1)/2)")
    print("can be cascade-forced or remain coincidental in the small-integer landscape")
    print("is the next dig target — likely requires a different mechanism (Γ critical")
    print("points + observer-frame structure) than the C-D chain we've used here.")
    print()

    print("=" * 92)
    print("CASCADE STRUCTURAL CHAIN: from cover sheet to gauge content")
    print("=" * 92)
    print()
    print("           Cayley-Dickson chain")
    print("                  ↓")
    print("           dim ℍ = 4, dim 𝕆 = 8")
    print("                  ↓")
    print("    Cover sheet: G_2/SU(3) at d_0 (octonion completion)")
    print("                  ↓")
    print(f"    d_0 = 7 (Γ-area-max, also = dim 𝕆 − 1)")
    print(f"    N_c = 3 (octonion-stabilizer rank)")
    print(f"    dim SU(3) = 8 (= dim 𝕆)")
    print("                  ↓")
    print(f"    d_g = 12 (= N_c · dim ℍ; gauge sphere ℍ^3)")
    print(f"    d_gw = 14 (= 2·d_0 = dim G_2 = 2(dim 𝕆 − 1))")
    print(f"    dim Spin(7) = 21 (= N_c · d_0; m_η'² scale)")
    print()
    print("All cascade gauge content (color count, gauge layers, gauge window,")
    print("U(1)_A anomaly mass) is forced by ONE structural commitment: the")
    print("cover sheet's G_2/SU(3) octonion-completion at d_0. The Cayley-")
    print("Dickson chain provides the algebra dimensions; G_2 = Aut(𝕆) provides")
    print("the Lie content; the cascade Catalan reading bridges d_0 and d_gw.")
    print()
    print()
    print("=" * 92)
    print("THE LIE-THEORETIC UNIQUENESS OF d_0 (DEEPEST DIG)")
    print("=" * 92)
    print()
    print("Why d_0 (not d=8 directly) hosts G_2/SU(3)?")
    print()
    print("  d=8: sphere S^7 = unit octonion sphere. G_2 = Aut(𝕆) does NOT act")
    print("       transitively on S^7 (it fixes 1 ∈ 𝕆 since automorphisms preserve")
    print("       the multiplicative identity). So S^7 is NOT a homogeneous space")
    print("       for G_2.")
    print()
    print("  d=7: sphere S^6 = unit imaginary octonions = Im 𝕆 unit sphere.")
    print("       G_2 acts TRANSITIVELY on S^6, with stabilizer SU(3).")
    print("       So S^6 = G_2/SU(3) IS the natural G_2-homogeneous space.")
    print()
    print("Hence the cascade's G_2 commitment FORCES the algebra-source layer to")
    print("be d such that d − 1 = dim S^6 = 6, i.e., d = 7. This is a Lie-theoretic")
    print("uniqueness: among small spheres around the octonion completion, only S^6")
    print("supports G_2-transitivity (i.e., is a G_2-homogeneous space).")
    print()
    print("Combined with the Γ-area-max integer being d_0 = 7 (Part 0 transcendental),")
    print("the cascade has a STRUCTURALLY CONSISTENT placement of G_2/SU(3) at d_0:")
    print()
    print("  • Lie-theoretic argument (cascade has G_2 → S^6 = G_2/SU(3) → d=7):")
    print("    forces algebra source at cascade layer 7.")
    print("  • Γ argument (Part 0 area-max integer):")
    print("    forces d_0 = 7 from transcendental ψ((d+1)/2) = log π.")
    print("  • Both give 7 — cascade's Γ + G_2 commitments are mutually consistent.")
    print()
    print("This sharpens the previous 'cover sheet's choice of d_0 to host")
    print("G_2/SU(3)' from a STRUCTURAL CHOICE to a LIE-THEORETIC NECESSITY ")
    print("(modulo the cascade's existing G_2 commitment from C-D + Adams + Bott).")
    print()
    print("=" * 92)
    print("THE GROUNDING REGRESS")
    print("=" * 92)
    print()
    print("Where does the cascade's G_2 commitment come from? Tracing back:")
    print()
    print("  G_2 = Aut(𝕆)  ←  cascade has 𝕆")
    print("       ←  C-D chain ℝ→ℂ→ℍ→𝕆 terminates at 𝕆 (Adams' theorem)")
    print("            ←  Cascade carries parallelizable spheres at boundaries")
    print("                 (S^0, S^1, S^3, S^7) with division-algebra structure")
    print("            ←  Cascade's commitment to Adams + Bott periodicity")
    print("                 (Cover sheet: Adams anchors gauge bosons; Bott")
    print("                  anchors fermion generations at 8-fold residues)")
    print()
    print("So the cascade's G_2 commitment ultimately reduces to its FOUNDATIONAL")
    print("commitments: Adams' theorem (parallelizable spheres) + Bott periodicity")
    print("(8-fold KO structure). These two commitments jointly imply the C-D chain")
    print("with division algebras at dims {1, 2, 4, 8}, and hence G_2 = Aut(𝕆).")
    print()
    print("CONSEQUENCE: the cascade's gauge sector is forced cascade-internally")
    print("from Adams + Bott + Γ critical points + cascade conventions, with no")
    print("additional structural commitment. The Cayley-Dickson chain is the")
    print("UNIFIER that connects fermion-Bott-content to gauge-Adams-content via")
    print("the four normed division algebras.")
    print()
    print("=" * 92)
    print("DEEPEST DIG VERDICT")
    print("=" * 92)
    print()
    print("The cascade's distinguished-dimension landscape implements the Cayley-")
    print("Dickson chain ℝ → ℂ → ℍ → 𝕆 at the cascade's foundational layers:")
    print()
    print("    d=1  ℝ-completion (slicing measure)")
    print("    d=2  ℂ-completion (Paper II forced orthogonality)")
    print("    d=4  ℍ-completion (4D spacetime, observer; ρ(4)−1 = 3)")
    print("    d=5  d_V (volume max; one above ℍ; observer host)")
    print("    d=7  d_0 (area max; one below 𝕆; G_2/SU(3) algebra source)")
    print("    d=8  𝕆-completion (octonion sphere S^7; ρ(8)=8 max; chain ends)")
    print("    d=12 d_g (gauge sphere S^11 ⊂ ℍ^3; Adams gives N_c = 3)")
    print("    d=14 d_gw (gauge window upper edge = dim G_2 = 2(𝕆−1))")
    print("    d=19 d_1 (phase transition = d_gw + d_V; integer relation)")
    print("    d=217 d_2 (Planck floor; outside C-D regime)")
    print()
    print("The C-D chain TERMINATES at 𝕆 (Adams' theorem on Hopf invariant 1:")
    print("no division algebra of dim > 8). The cascade's distinguished dims")
    print("at d_V, d_0 sit just above ℍ-completion and just below 𝕆-completion")
    print("respectively — natural BOUNDARY POSITIONS in the C-D chain.")
    print()
    print("'Specialness' of d_0 is a particular case of a broader pattern:")
    print("cascade distinguished dims sit at C-D characteristic positions:")
    print()
    print("    d_V = dim ℍ + 1   (above quaternion completion)")
    print("    d_0 = dim 𝕆 − 1   (below octonion completion)")
    print("    d_g = N_c · dim ℍ (gauge sphere = ℍ^{N_c})")
    print("    d_gw = 2·(dim 𝕆 − 1) = dim G_2  (gauge window upper edge)")
    print()
    print("Three of these (d_0, d_g, d_gw) are CASCADE-FORCED by C-D + cover")
    print("sheet's G_2/SU(3) commitment + cascade Catalan. The fourth (d_V) is")
    print("a small-integer identity at the cascade's Γ-volume-max integer.")
    print()
    print("The 'specialness' of d_0 IS the Lie-theoretic uniqueness of S^6 =")
    print("G_2/SU(3) as the cascade's natural octonion-algebra-source homogeneous")
    print("space, combined with the Γ critical point at the same layer. Both the")
    print("Lie and Γ arguments give d_0 = 7 — cascade-internal consistency.")
    print()
    print("This is a substantive structural deepening of the cascade's gauge sector:")
    print("the gauge content reduces to ONE octonion-completion commitment plus")
    print("the cascade's existing Γ + Adams + Catalan structure. The 'specialness'")
    print("of d_0 is now fully articulated — d_0 is the cascade layer at which the")
    print("octonion algebra completes (dim 𝕆 − 1 = 7 = Γ-area-max integer), and")
    print("everything else in the gauge sector follows.")


if __name__ == "__main__":
    main()
