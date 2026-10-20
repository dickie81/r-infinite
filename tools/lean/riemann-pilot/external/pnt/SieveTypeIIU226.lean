/-
# Round 614: the Weyl-conditional curve `g7` at `L = 226/100`: its window and Proposition 3′ there

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_226`). Under `LinnikCGL.CGLDensity` and `LinnikWeyl.PYWeyl`, Proposition 3′
(`SieveTypeIIGen.typeII_gen`) at `L = 226/100` on the window `[4075/10000, 4835/10000]·L` for round 612's curve
`SieveTypeIIU227.g7` (the trivial count below `4/7`, the sixty steps of `LinnikStairs7`, `7/3 + 1/2000` on
`[5/7, 16/21]`), whose counts are `SieveTypeIIU227.counts_7`.

* `window_6`: `WindowOK g7 L m₁ m₂` at `L = 226/100`, glued by `SieveCurveGlue.windowPiece_glue` from the 62 pieces
  checked at their corners (`windowPiece_const`, `windowPiece_one`; round 612's tactic `corners`).
* `typeII_226`: `typeII_gen` at `g7`, under `CGLDensity` and `PYWeyl`.

The file imports `SieveTypeIIU227.lean`.
-/
import SieveTypeIIU227

open Complex Real Finset

noncomputable section

namespace SieveTypeIIU226

open DirichletCharacter SieveTypeIIGen SieveCurveGlue SieveTypeIIU227

/-- **The window's exponents** at `L = 226/100` on `[4075/10000, 4835/10000]·L`: every piece of `g7` at its corners. -/
theorem window_6 : WindowOK g7 (226 / 100) (4075 / 10000 * (226 / 100)) (4835 / 10000 * (226 / 100)) :=
  windowOK_of_piece <| windowPiece_glue (windowPiece_one (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 840199 / 398000) (lo := 4 / 7) (hi := 81 / 140)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 140033 / 66000) (lo := 81 / 140) (hi := 41 / 70)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 840197 / 394000) (lo := 41 / 70) (hi := 83 / 140)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 30007 / 14000) (lo := 83 / 140) (hi := 3 / 5)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 56013 / 26000) (lo := 3 / 5) (hi := 17 / 28)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 420097 / 194000) (lo := 17 / 28) (hi := 43 / 70)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 840193 / 386000) (lo := 43 / 70) (hi := 87 / 140)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 547 / 250) (lo := 87 / 140) (hi := 22 / 35)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 840191 / 382000) (lo := 22 / 35) (hi := 89 / 140)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 84019 / 38000) (lo := 89 / 140) (hi := 9 / 14)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 40009 / 18000) (lo := 9 / 14) (hi := 13 / 20)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 210047 / 94000) (lo := 13 / 20) (hi := 23 / 35)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 840187 / 374000) (lo := 23 / 35) (hi := 93 / 140)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 140031 / 62000) (lo := 93 / 140) (hi := 47 / 70)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 168037 / 74000) (lo := 47 / 70) (hi := 19 / 28)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 105023 / 46000) (lo := 19 / 28) (hi := 24 / 35)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 280061 / 122000) (lo := 24 / 35) (hi := 97 / 140)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 60013 / 26000) (lo := 97 / 140) (hi := 7 / 10)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 840181 / 362000) (lo := 7 / 10) (hi := 99 / 140)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 14003 / 6000) (lo := 99 / 140) (hi := 5 / 7)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 14003 / 6000) (lo := 5 / 7) (hi := 16 / 21)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 14003 / 6000) (lo := 16 / 21) (hi := 643 / 840)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 560121 / 242000) (lo := 643 / 840) (hi := 323 / 420)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 280061 / 122000) (lo := 323 / 420) (hi := 649 / 840)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 560123 / 246000) (lo := 649 / 840) (hi := 163 / 210)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 140031 / 62000) (lo := 163 / 210) (hi := 131 / 168)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 4481 / 2000) (lo := 131 / 168) (hi := 47 / 60)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 40009 / 18000) (lo := 47 / 60) (hi := 661 / 840)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 560127 / 254000) (lo := 661 / 840) (hi := 83 / 105)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 547 / 250) (lo := 83 / 105) (hi := 667 / 840)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 560129 / 258000) (lo := 667 / 840) (hi := 67 / 84)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 56013 / 26000) (lo := 67 / 84) (hi := 673 / 840)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 560131 / 262000) (lo := 673 / 840) (hi := 169 / 210)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 140033 / 66000) (lo := 169 / 210) (hi := 97 / 120)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 80019 / 38000) (lo := 97 / 120) (hi := 341 / 420)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 280067 / 134000) (lo := 341 / 420) (hi := 137 / 168)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 112027 / 54000) (lo := 137 / 168) (hi := 86 / 105)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 70017 / 34000) (lo := 86 / 105) (hi := 691 / 840)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 560137 / 274000) (lo := 691 / 840) (hi := 347 / 420)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 280069 / 138000) (lo := 347 / 420) (hi := 697 / 840)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 560139 / 278000) (lo := 697 / 840) (hi := 5 / 6)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 50159 / 25000) (lo := 5 / 6) (hi := 67 / 80)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 480121 / 242000) (lo := 67 / 80) (hi := 101 / 120)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 240061 / 122000) (lo := 101 / 120) (hi := 203 / 240)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 160041 / 82000) (lo := 203 / 240) (hi := 17 / 20)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 120031 / 62000) (lo := 17 / 20) (hi := 41 / 48)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 3841 / 2000) (lo := 41 / 48) (hi := 103 / 120)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 80021 / 42000) (lo := 103 / 120) (hi := 69 / 80)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 480127 / 254000) (lo := 69 / 80) (hi := 13 / 15)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 3751 / 2000) (lo := 13 / 15) (hi := 209 / 240)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 160043 / 86000) (lo := 209 / 240) (hi := 7 / 8)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 48013 / 26000) (lo := 7 / 8) (hi := 211 / 240)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 480131 / 262000) (lo := 211 / 240) (hi := 53 / 60)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 40011 / 22000) (lo := 53 / 60) (hi := 71 / 80)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 480133 / 266000) (lo := 71 / 80) (hi := 107 / 120)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 240067 / 134000) (lo := 107 / 120) (hi := 43 / 48)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 32009 / 18000) (lo := 43 / 48) (hi := 9 / 10)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 60017 / 34000) (lo := 9 / 10) (hi := 217 / 240)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 480137 / 274000) (lo := 217 / 240) (hi := 109 / 120)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_glue (windowPiece_const (A := 80023 / 46000) (lo := 109 / 120) (hi := 73 / 80)
      (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPiece_const (A := 480139 / 278000) (lo := 73 / 80) (hi := 11 / 12)
      (by norm_num) (by norm_num) (by corners) (by corners)

open scoped ContDiff in
/-- **Proposition 3′ at `L = 226/100` on `[4075/10000, 4835/10000]·L`, for the curve `g7`**, under `CGLDensity` and
`PYWeyl`: `typeII_gen`. -/
theorem typeII_226 (hCGL : LinnikCGL.CGLDensity) (hPY : LinnikWeyl.PYWeyl) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (4075 / 10000 * (226 / 100) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (4835 / 10000 * (226 / 100) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (226 / 100 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ ((226 / 100 : ℝ) - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen g7_le_one g7_half (counts_7 hCGL hPY) window_6 hf0 hsupp K₀ he₁ hη hη1

end SieveTypeIIU226

#print axioms SieveTypeIIU226.window_6
#print axioms SieveTypeIIU226.typeII_226
