/-
# Round 621: Proposition 3′ at `L = 230/100` on the Halász–Montgomery window `[3944/10000, 4780/10000]·L`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

The curve `gU` of `SieveTypeIIU232.lean` (round 609) with the Type II bound of `SieveTypeIIHM.typeII_gen_hm` (the
better of orthogonality and Halász–Montgomery for each bin): every piece of the window condition `WindowOKHM` holds by
orthogonality at its corners except the top piece `[5/6, 11/12]` for `m ≤ 1`, which holds by the Halász–Montgomery
branch at its corners (`windowPieceHM_const_split`: `windowPieceHM_affine_split` for the step `(101/50)(1 − σ)` of
`gU`).

The file imports `SieveTypeIIU232.lean` (for `gU`, `counts_U` and the tactic `corners`) and `SieveTypeIIHM.lean`.
-/
import SieveTypeIIU232
import SieveTypeIIHM

namespace SieveTypeIIU230

open DirichletCharacter SieveTypeIIGen SieveCurveGlue SieveTypeIIU232 SieveTypeIIHM

set_option hygiene false in
/-- The corner cases of `windowPieceHM_const_split`: two values of `β`, two of `m`, two of `w`, each by `norm_num`. -/
macro "cornersHM" : tactic =>
  `(tactic| (intro β m w hb hm hw
             rcases hb with rfl | rfl <;> rcases hm with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num))

/-- **The window's exponents** at `L = 230/100` on `[3944/10000, 4780/10000]·L`, with the Halász–Montgomery branch on
the top piece. -/
theorem window_230 : WindowOKHM gU (230 / 100) (3944 / 10000 * (230 / 100)) (4780 / 10000 * (230 / 100))
    (1 / 1000) (1 / 1000) :=
  windowOKHM_of_piece <| windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_one (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 1152508841 / 537682000) (lo := 2801 / 4801) (hi := 115239 / 192040)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 576252821 / 265642000) (lo := 115239 / 192040) (hi := 59219 / 96020)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 384167481 / 174962000) (lo := 59219 / 96020) (hi := 121637 / 192040)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 288124811 / 129622000) (lo := 121637 / 192040) (hi := 31209 / 48010)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 230499209 / 102418000) (lo := 31209 / 48010) (hi := 25607 / 38408)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 192082141 / 84282000) (lo := 25607 / 38408) (hi := 65617 / 96020)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 1152489647 / 499294000) (lo := 65617 / 96020) (hi := 134433 / 192040)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 72030403 / 30806000) (lo := 134433 / 192040) (hi := 17204 / 24005)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 384161083 / 162166000) (lo := 17204 / 24005) (hi := 140831 / 192040)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 4801 / 2000) (lo := 140831 / 192040) (hi := 3 / 4)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 4801 / 2000) (lo := 3 / 4) (hi := 91 / 120)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 80017 / 34000) (lo := 91 / 120) (hi := 23 / 30)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 60013 / 26000) (lo := 23 / 30) (hi := 31 / 40)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 240053 / 106000) (lo := 31 / 40) (hi := 47 / 60)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 40009 / 18000) (lo := 47 / 60) (hi := 19 / 24)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 48011 / 22000) (lo := 19 / 24) (hi := 4 / 5)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 30007 / 14000) (lo := 4 / 5) (hi := 97 / 120)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 80019 / 38000) (lo := 97 / 120) (hi := 49 / 60)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 120029 / 58000) (lo := 49 / 60) (hi := 33 / 40)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 240059 / 118000) (lo := 33 / 40) (hi := 5 / 6)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_const_split (A := 101 / 50) (lo := 5 / 6) (hi := 11 / 12)
      (by norm_num) (by cornersHM) (by cornersHM) (by cornersHM)

open scoped ContDiff in
/-- **Proposition 3′ at `L = 230/100` on `[3944/10000, 4780/10000]·L`, for the curve `gU`**, with no hypothesis:
`typeII_gen_hm` for `f0` smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀`, `e₁ > 0` (`he₁`) and `0 < η ≤ 10⁻⁵`
(`hη`, `hη1`). -/
theorem typeII_230 {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (3944 / 10000 * (230 / 100) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (4780 / 10000 * (230 / 100) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (230 / 100 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ ((230 / 100 : ℝ) - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen_hm gU_le_one gU_half counts_U window_230 hf0 hsupp K₀ he₁ hη hη1

end SieveTypeIIU230

#print axioms SieveTypeIIU230.window_230
#print axioms SieveTypeIIU230.typeII_230
