/-
# Round 609: the unconditional curve at `L = 232/100`: Ingham's and Huxley's staircases, `101/50` above `5/6`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_232`). Proposition 3′ (`SieveTypeIIGen.typeII_gen`) at `L = 232/100` on the window
`[4045/10000, 4825/10000]·L` for the curve `gU`: the trivial count below `b₀ = 1 − 1/A_U`, `A_U = 12/5 + 1/2000`
(`b₀ = 2801 / 4801`), the ten Ingham steps of `LinnikStairs` from `b₀` to `3/4`, its ten Huxley steps from `3/4` to
`5/6`,
and `101/50` from `5/6` on. No hypothesis: every piece is a theorem of the stack.

* `gU`, `gU_le_one`, `gU_half`: the curve's exponent `A(σ)(1 − σ)`, at most `1`, and `1` at `σ = 1/2`.
* `counts_U`: `CurveCounts gU`, glued from the pieces by `SieveCurveGlue.rangeCounts_glue`.
* `window_U`: `WindowOK gU L m₁ m₂`, glued by `SieveCurveGlue.windowPiece_glue` from pieces checked at their corners
  (`windowPiece_const`, `windowPiece_one`; the tactic `corners` runs the cases and `norm_num`).
* `typeII_232`: `typeII_gen` at `gU`.

The file imports `SieveCurveGlue.lean`, `LinnikStairs.lean` and `LinnikStep.lean`.
-/
import SieveCurveGlue
import LinnikStairs
import LinnikStep

open Complex Real Finset

noncomputable section

namespace SieveTypeIIU232

open DirichletCharacter SieveTypeIIGen SieveCurveGlue

set_option hygiene false in
/-- The corner cases of `windowPiece_const` and `windowPiece_one`: the two values of `β`, the three of `m` where the
side condition holds, the two of `w`, each closed by `norm_num` (a corner with `m = m₂ ≤ 1` is closed at `h`). -/
macro "corners" : tactic =>
  `(tactic| (intro β m w hb hm hw
             rcases hb with rfl | rfl <;> rcases hm with ⟨rfl, h⟩ | ⟨rfl, h, h'⟩ | ⟨rfl, h⟩ <;>
               rcases hw with rfl | rfl <;> (try norm_num at h) <;> norm_num ))

/-- The curve: `1` below `b₀`, then the twenty steps of `LinnikStairs` (each `A(1 − σ)` with the step's constant `A`),
and `(101/50)(1 − σ)` from `5/6` on. -/
def gU (σ : ℝ) : ℝ :=
  if σ < 2801 / 4801 then 1 else
  if σ < 115239 / 192040 then (1152508841 / 537682000) * (1 - σ) else
  if σ < 59219 / 96020 then (576252821 / 265642000) * (1 - σ) else
  if σ < 121637 / 192040 then (384167481 / 174962000) * (1 - σ) else
  if σ < 31209 / 48010 then (288124811 / 129622000) * (1 - σ) else
  if σ < 25607 / 38408 then (230499209 / 102418000) * (1 - σ) else
  if σ < 65617 / 96020 then (192082141 / 84282000) * (1 - σ) else
  if σ < 134433 / 192040 then (1152489647 / 499294000) * (1 - σ) else
  if σ < 17204 / 24005 then (72030403 / 30806000) * (1 - σ) else
  if σ < 140831 / 192040 then (384161083 / 162166000) * (1 - σ) else
  if σ < 3 / 4 then (4801 / 2000) * (1 - σ) else
  if σ < 91 / 120 then (4801 / 2000) * (1 - σ) else
  if σ < 23 / 30 then (80017 / 34000) * (1 - σ) else
  if σ < 31 / 40 then (60013 / 26000) * (1 - σ) else
  if σ < 47 / 60 then (240053 / 106000) * (1 - σ) else
  if σ < 19 / 24 then (40009 / 18000) * (1 - σ) else
  if σ < 4 / 5 then (48011 / 22000) * (1 - σ) else
  if σ < 97 / 120 then (30007 / 14000) * (1 - σ) else
  if σ < 49 / 60 then (80019 / 38000) * (1 - σ) else
  if σ < 33 / 40 then (120029 / 58000) * (1 - σ) else
  if σ < 5 / 6 then (240059 / 118000) * (1 - σ) else
  (101 / 50) * (1 - σ)

lemma gU_le_one (σ : ℝ) : gU σ ≤ 1 := by
  unfold gU
  by_cases h0 : σ < 2801 / 4801
  · simp only [h0, ite_true, le_refl]
  simp only [h0, ite_false]
  by_cases h1 : σ < 115239 / 192040
  · simp only [h1, ite_true]; linarith
  simp only [h1, ite_false]
  by_cases h2 : σ < 59219 / 96020
  · simp only [h2, ite_true]; linarith
  simp only [h2, ite_false]
  by_cases h3 : σ < 121637 / 192040
  · simp only [h3, ite_true]; linarith
  simp only [h3, ite_false]
  by_cases h4 : σ < 31209 / 48010
  · simp only [h4, ite_true]; linarith
  simp only [h4, ite_false]
  by_cases h5 : σ < 25607 / 38408
  · simp only [h5, ite_true]; linarith
  simp only [h5, ite_false]
  by_cases h6 : σ < 65617 / 96020
  · simp only [h6, ite_true]; linarith
  simp only [h6, ite_false]
  by_cases h7 : σ < 134433 / 192040
  · simp only [h7, ite_true]; linarith
  simp only [h7, ite_false]
  by_cases h8 : σ < 17204 / 24005
  · simp only [h8, ite_true]; linarith
  simp only [h8, ite_false]
  by_cases h9 : σ < 140831 / 192040
  · simp only [h9, ite_true]; linarith
  simp only [h9, ite_false]
  by_cases h10 : σ < 3 / 4
  · simp only [h10, ite_true]; linarith
  simp only [h10, ite_false]
  by_cases h11 : σ < 91 / 120
  · simp only [h11, ite_true]; linarith
  simp only [h11, ite_false]
  by_cases h12 : σ < 23 / 30
  · simp only [h12, ite_true]; linarith
  simp only [h12, ite_false]
  by_cases h13 : σ < 31 / 40
  · simp only [h13, ite_true]; linarith
  simp only [h13, ite_false]
  by_cases h14 : σ < 47 / 60
  · simp only [h14, ite_true]; linarith
  simp only [h14, ite_false]
  by_cases h15 : σ < 19 / 24
  · simp only [h15, ite_true]; linarith
  simp only [h15, ite_false]
  by_cases h16 : σ < 4 / 5
  · simp only [h16, ite_true]; linarith
  simp only [h16, ite_false]
  by_cases h17 : σ < 97 / 120
  · simp only [h17, ite_true]; linarith
  simp only [h17, ite_false]
  by_cases h18 : σ < 49 / 60
  · simp only [h18, ite_true]; linarith
  simp only [h18, ite_false]
  by_cases h19 : σ < 33 / 40
  · simp only [h19, ite_true]; linarith
  simp only [h19, ite_false]
  by_cases h20 : σ < 5 / 6
  · simp only [h20, ite_true]; linarith
  simp only [h20, ite_false]
  linarith

lemma gU_half : gU (1 / 2) = 1 := by unfold gU; norm_num

open scoped Classical in
/-- **The counts of the curve** (`CurveCounts gU`): the trivial count, the twenty steps and `charDensity_step`,
glued. -/
theorem counts_U : CurveCounts gU :=
  curveCounts_of_range <| rangeCounts_glue (rangeCounts_trivial _ _) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in0) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in1) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in2) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in3) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in4) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in5) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in6) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in7) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in8) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_in9) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx0) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx1) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx2) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx3) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx4) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx5) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx6) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx7) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx8) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs.charDensity_hx9) <|
    rangeCounts_of_density LinnikStep.charDensity_step

/-- **The window's exponents** at `L = 232/100` on `[4045/10000, 4825/10000]·L`: every piece at its corners. -/
theorem window_U : WindowOK gU (232 / 100) (4045 / 10000 * (232 / 100)) (4825 / 10000 * (232 / 100)) :=
  windowOK_of_piece <| windowPiece_glue (windowPiece_one (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 1152508841 / 537682000) (lo := 2801 / 4801) (hi := 115239 / 192040)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 576252821 / 265642000) (lo := 115239 / 192040) (hi := 59219 / 96020)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 384167481 / 174962000) (lo := 59219 / 96020) (hi := 121637 / 192040)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 288124811 / 129622000) (lo := 121637 / 192040) (hi := 31209 / 48010)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 230499209 / 102418000) (lo := 31209 / 48010) (hi := 25607 / 38408)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 192082141 / 84282000) (lo := 25607 / 38408) (hi := 65617 / 96020)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 1152489647 / 499294000) (lo := 65617 / 96020) (hi := 134433 / 192040)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 72030403 / 30806000) (lo := 134433 / 192040) (hi := 17204 / 24005)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 384161083 / 162166000) (lo := 17204 / 24005) (hi := 140831 / 192040)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 4801 / 2000) (lo := 140831 / 192040) (hi := 3 / 4)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 4801 / 2000) (lo := 3 / 4) (hi := 91 / 120)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 80017 / 34000) (lo := 91 / 120) (hi := 23 / 30)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 60013 / 26000) (lo := 23 / 30) (hi := 31 / 40)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 240053 / 106000) (lo := 31 / 40) (hi := 47 / 60)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 40009 / 18000) (lo := 47 / 60) (hi := 19 / 24)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 48011 / 22000) (lo := 19 / 24) (hi := 4 / 5)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 30007 / 14000) (lo := 4 / 5) (hi := 97 / 120)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 80019 / 38000) (lo := 97 / 120) (hi := 49 / 60)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 120029 / 58000) (lo := 49 / 60) (hi := 33 / 40)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 240059 / 118000) (lo := 33 / 40) (hi := 5 / 6)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_const (A := 101 / 50) (lo := 5 / 6) (hi := 11 / 12)
      (by norm_num) (by norm_num) (by corners) (by corners)

open scoped ContDiff in
/-- **Proposition 3′ at `L = 232/100` on `[4045/10000, 4825/10000]·L`, for the curve `gU`**: `typeII_gen`. -/
theorem typeII_232 {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (4045 / 10000 * (232 / 100) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (4825 / 10000 * (232 / 100) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (232 / 100 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ ((232 / 100 : ℝ) - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen gU_le_one gU_half counts_U window_U hf0 hsupp K₀ he₁ hη hη1

end SieveTypeIIU232

#print axioms SieveTypeIIU232.counts_U
#print axioms SieveTypeIIU232.window_U
#print axioms SieveTypeIIU232.typeII_232
