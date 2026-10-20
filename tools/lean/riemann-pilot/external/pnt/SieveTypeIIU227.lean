/-
# Round 612: the Weyl-conditional curve at `L = 227/100`: Ingham's and Huxley's staircases, Huxley's curve above `5/6`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_227`). Under `LinnikCGL.CGLDensity` and `LinnikWeyl.PYWeyl`, Proposition 3′
(`SieveTypeIIGen.typeII_gen`) at `L = 227/100` on the window `[4048/10000, 4858/10000]·L` for the curve `g7`: the
trivial
count below `4/7`, the twenty Ingham steps of `LinnikStairs7` from `4/7` to `5/7`, `7/3 + 1/2000` on `[5/7, 16/21]`
(`CGLDensity`), its twenty Huxley steps from `16/21` to `5/6`, and its twenty steps under the pointwise bound from `5/6`
to `11/12`, the last extended to `1`.

* `g7`, `g7_le_one`, `g7_half`: the curve's exponent `A(σ)(1 − σ)`, at most `1`, and `1` at `σ = 1/2`.
* `rangeCounts_cgl`: `CGLDensity` at `ε = 1/8400` gives the counts of `(7/3 + 1/2000)(1 − σ)` on `[5/7, 16/21]`.
* `counts_7`: `CurveCounts g7`, glued from the pieces by `SieveCurveGlue.rangeCounts_glue`, under `CGLDensity` and
  `PYWeyl`.
* `window_7`: `WindowOK g7 L m₁ m₂`, glued by `SieveCurveGlue.windowPiece_glue` from pieces checked at their corners
  (`windowPiece_const`, `windowPiece_one`; the tactic `corners` runs the cases and `norm_num`).
* `typeII_227`: `typeII_gen` at `g7`, under `CGLDensity` and `PYWeyl`.

The file imports `SieveCurveGlue.lean`, `LinnikStairs7.lean` and `LinnikCGL.lean`.
-/
import SieveCurveGlue
import LinnikStairs7
import LinnikCGL

open Complex Real Finset

noncomputable section

namespace SieveTypeIIU227

open DirichletCharacter SieveTypeIIGen SieveCurveGlue

set_option hygiene false in
/-- The corner cases of `windowPiece_const` and `windowPiece_one`: the two values of `β`, the three of `m` where the
side condition holds, the two of `w`, each closed by `norm_num` (a corner whose side condition is false, `m = m₂` with
`m₂ ≤ 1` or `m = m₁` with `1 ≤ m₁`, is closed at `h`). -/
macro "corners" : tactic =>
  `(tactic| (intro β m w hb hm hw
             rcases hb with rfl | rfl <;> rcases hm with ⟨rfl, h⟩ | ⟨rfl, h, h'⟩ | ⟨rfl, h⟩ <;>
               rcases hw with rfl | rfl <;> (try norm_num at h) <;> norm_num ))

/-- The curve: `1` below `4/7`, then the sixty steps of `LinnikStairs7` and `7/3 + 1/2000` on `[5/7, 16/21]` (each
`A(1 − σ)` with the piece's constant `A`), the last step's constant from `73 / 80` on. -/
def g7 (σ : ℝ) : ℝ :=
  if σ < 4 / 7 then 1 else
  if σ < 81 / 140 then (840199 / 398000) * (1 - σ) else
  if σ < 41 / 70 then (140033 / 66000) * (1 - σ) else
  if σ < 83 / 140 then (840197 / 394000) * (1 - σ) else
  if σ < 3 / 5 then (30007 / 14000) * (1 - σ) else
  if σ < 17 / 28 then (56013 / 26000) * (1 - σ) else
  if σ < 43 / 70 then (420097 / 194000) * (1 - σ) else
  if σ < 87 / 140 then (840193 / 386000) * (1 - σ) else
  if σ < 22 / 35 then (547 / 250) * (1 - σ) else
  if σ < 89 / 140 then (840191 / 382000) * (1 - σ) else
  if σ < 9 / 14 then (84019 / 38000) * (1 - σ) else
  if σ < 13 / 20 then (40009 / 18000) * (1 - σ) else
  if σ < 23 / 35 then (210047 / 94000) * (1 - σ) else
  if σ < 93 / 140 then (840187 / 374000) * (1 - σ) else
  if σ < 47 / 70 then (140031 / 62000) * (1 - σ) else
  if σ < 19 / 28 then (168037 / 74000) * (1 - σ) else
  if σ < 24 / 35 then (105023 / 46000) * (1 - σ) else
  if σ < 97 / 140 then (280061 / 122000) * (1 - σ) else
  if σ < 7 / 10 then (60013 / 26000) * (1 - σ) else
  if σ < 99 / 140 then (840181 / 362000) * (1 - σ) else
  if σ < 5 / 7 then (14003 / 6000) * (1 - σ) else
  if σ < 16 / 21 then (14003 / 6000) * (1 - σ) else
  if σ < 643 / 840 then (14003 / 6000) * (1 - σ) else
  if σ < 323 / 420 then (560121 / 242000) * (1 - σ) else
  if σ < 649 / 840 then (280061 / 122000) * (1 - σ) else
  if σ < 163 / 210 then (560123 / 246000) * (1 - σ) else
  if σ < 131 / 168 then (140031 / 62000) * (1 - σ) else
  if σ < 47 / 60 then (4481 / 2000) * (1 - σ) else
  if σ < 661 / 840 then (40009 / 18000) * (1 - σ) else
  if σ < 83 / 105 then (560127 / 254000) * (1 - σ) else
  if σ < 667 / 840 then (547 / 250) * (1 - σ) else
  if σ < 67 / 84 then (560129 / 258000) * (1 - σ) else
  if σ < 673 / 840 then (56013 / 26000) * (1 - σ) else
  if σ < 169 / 210 then (560131 / 262000) * (1 - σ) else
  if σ < 97 / 120 then (140033 / 66000) * (1 - σ) else
  if σ < 341 / 420 then (80019 / 38000) * (1 - σ) else
  if σ < 137 / 168 then (280067 / 134000) * (1 - σ) else
  if σ < 86 / 105 then (112027 / 54000) * (1 - σ) else
  if σ < 691 / 840 then (70017 / 34000) * (1 - σ) else
  if σ < 347 / 420 then (560137 / 274000) * (1 - σ) else
  if σ < 697 / 840 then (280069 / 138000) * (1 - σ) else
  if σ < 5 / 6 then (560139 / 278000) * (1 - σ) else
  if σ < 67 / 80 then (50159 / 25000) * (1 - σ) else
  if σ < 101 / 120 then (480121 / 242000) * (1 - σ) else
  if σ < 203 / 240 then (240061 / 122000) * (1 - σ) else
  if σ < 17 / 20 then (160041 / 82000) * (1 - σ) else
  if σ < 41 / 48 then (120031 / 62000) * (1 - σ) else
  if σ < 103 / 120 then (3841 / 2000) * (1 - σ) else
  if σ < 69 / 80 then (80021 / 42000) * (1 - σ) else
  if σ < 13 / 15 then (480127 / 254000) * (1 - σ) else
  if σ < 209 / 240 then (3751 / 2000) * (1 - σ) else
  if σ < 7 / 8 then (160043 / 86000) * (1 - σ) else
  if σ < 211 / 240 then (48013 / 26000) * (1 - σ) else
  if σ < 53 / 60 then (480131 / 262000) * (1 - σ) else
  if σ < 71 / 80 then (40011 / 22000) * (1 - σ) else
  if σ < 107 / 120 then (480133 / 266000) * (1 - σ) else
  if σ < 43 / 48 then (240067 / 134000) * (1 - σ) else
  if σ < 9 / 10 then (32009 / 18000) * (1 - σ) else
  if σ < 217 / 240 then (60017 / 34000) * (1 - σ) else
  if σ < 109 / 120 then (480137 / 274000) * (1 - σ) else
  if σ < 73 / 80 then (80023 / 46000) * (1 - σ) else
  (480139 / 278000) * (1 - σ)

lemma g7_le_one (σ : ℝ) : g7 σ ≤ 1 := by
  unfold g7
  by_cases h0 : σ < 4 / 7
  · simp only [h0, ite_true, le_refl]
  simp only [h0, ite_false]
  by_cases h1 : σ < 81 / 140
  · simp only [h1, ite_true]; linarith only [not_lt.1 h0]
  simp only [h1, ite_false]
  clear h0
  by_cases h2 : σ < 41 / 70
  · simp only [h2, ite_true]; linarith only [not_lt.1 h1]
  simp only [h2, ite_false]
  clear h1
  by_cases h3 : σ < 83 / 140
  · simp only [h3, ite_true]; linarith only [not_lt.1 h2]
  simp only [h3, ite_false]
  clear h2
  by_cases h4 : σ < 3 / 5
  · simp only [h4, ite_true]; linarith only [not_lt.1 h3]
  simp only [h4, ite_false]
  clear h3
  by_cases h5 : σ < 17 / 28
  · simp only [h5, ite_true]; linarith only [not_lt.1 h4]
  simp only [h5, ite_false]
  clear h4
  by_cases h6 : σ < 43 / 70
  · simp only [h6, ite_true]; linarith only [not_lt.1 h5]
  simp only [h6, ite_false]
  clear h5
  by_cases h7 : σ < 87 / 140
  · simp only [h7, ite_true]; linarith only [not_lt.1 h6]
  simp only [h7, ite_false]
  clear h6
  by_cases h8 : σ < 22 / 35
  · simp only [h8, ite_true]; linarith only [not_lt.1 h7]
  simp only [h8, ite_false]
  clear h7
  by_cases h9 : σ < 89 / 140
  · simp only [h9, ite_true]; linarith only [not_lt.1 h8]
  simp only [h9, ite_false]
  clear h8
  by_cases h10 : σ < 9 / 14
  · simp only [h10, ite_true]; linarith only [not_lt.1 h9]
  simp only [h10, ite_false]
  clear h9
  by_cases h11 : σ < 13 / 20
  · simp only [h11, ite_true]; linarith only [not_lt.1 h10]
  simp only [h11, ite_false]
  clear h10
  by_cases h12 : σ < 23 / 35
  · simp only [h12, ite_true]; linarith only [not_lt.1 h11]
  simp only [h12, ite_false]
  clear h11
  by_cases h13 : σ < 93 / 140
  · simp only [h13, ite_true]; linarith only [not_lt.1 h12]
  simp only [h13, ite_false]
  clear h12
  by_cases h14 : σ < 47 / 70
  · simp only [h14, ite_true]; linarith only [not_lt.1 h13]
  simp only [h14, ite_false]
  clear h13
  by_cases h15 : σ < 19 / 28
  · simp only [h15, ite_true]; linarith only [not_lt.1 h14]
  simp only [h15, ite_false]
  clear h14
  by_cases h16 : σ < 24 / 35
  · simp only [h16, ite_true]; linarith only [not_lt.1 h15]
  simp only [h16, ite_false]
  clear h15
  by_cases h17 : σ < 97 / 140
  · simp only [h17, ite_true]; linarith only [not_lt.1 h16]
  simp only [h17, ite_false]
  clear h16
  by_cases h18 : σ < 7 / 10
  · simp only [h18, ite_true]; linarith only [not_lt.1 h17]
  simp only [h18, ite_false]
  clear h17
  by_cases h19 : σ < 99 / 140
  · simp only [h19, ite_true]; linarith only [not_lt.1 h18]
  simp only [h19, ite_false]
  clear h18
  by_cases h20 : σ < 5 / 7
  · simp only [h20, ite_true]; linarith only [not_lt.1 h19]
  simp only [h20, ite_false]
  clear h19
  by_cases h21 : σ < 16 / 21
  · simp only [h21, ite_true]; linarith only [not_lt.1 h20]
  simp only [h21, ite_false]
  clear h20
  by_cases h22 : σ < 643 / 840
  · simp only [h22, ite_true]; linarith only [not_lt.1 h21]
  simp only [h22, ite_false]
  clear h21
  by_cases h23 : σ < 323 / 420
  · simp only [h23, ite_true]; linarith only [not_lt.1 h22]
  simp only [h23, ite_false]
  clear h22
  by_cases h24 : σ < 649 / 840
  · simp only [h24, ite_true]; linarith only [not_lt.1 h23]
  simp only [h24, ite_false]
  clear h23
  by_cases h25 : σ < 163 / 210
  · simp only [h25, ite_true]; linarith only [not_lt.1 h24]
  simp only [h25, ite_false]
  clear h24
  by_cases h26 : σ < 131 / 168
  · simp only [h26, ite_true]; linarith only [not_lt.1 h25]
  simp only [h26, ite_false]
  clear h25
  by_cases h27 : σ < 47 / 60
  · simp only [h27, ite_true]; linarith only [not_lt.1 h26]
  simp only [h27, ite_false]
  clear h26
  by_cases h28 : σ < 661 / 840
  · simp only [h28, ite_true]; linarith only [not_lt.1 h27]
  simp only [h28, ite_false]
  clear h27
  by_cases h29 : σ < 83 / 105
  · simp only [h29, ite_true]; linarith only [not_lt.1 h28]
  simp only [h29, ite_false]
  clear h28
  by_cases h30 : σ < 667 / 840
  · simp only [h30, ite_true]; linarith only [not_lt.1 h29]
  simp only [h30, ite_false]
  clear h29
  by_cases h31 : σ < 67 / 84
  · simp only [h31, ite_true]; linarith only [not_lt.1 h30]
  simp only [h31, ite_false]
  clear h30
  by_cases h32 : σ < 673 / 840
  · simp only [h32, ite_true]; linarith only [not_lt.1 h31]
  simp only [h32, ite_false]
  clear h31
  by_cases h33 : σ < 169 / 210
  · simp only [h33, ite_true]; linarith only [not_lt.1 h32]
  simp only [h33, ite_false]
  clear h32
  by_cases h34 : σ < 97 / 120
  · simp only [h34, ite_true]; linarith only [not_lt.1 h33]
  simp only [h34, ite_false]
  clear h33
  by_cases h35 : σ < 341 / 420
  · simp only [h35, ite_true]; linarith only [not_lt.1 h34]
  simp only [h35, ite_false]
  clear h34
  by_cases h36 : σ < 137 / 168
  · simp only [h36, ite_true]; linarith only [not_lt.1 h35]
  simp only [h36, ite_false]
  clear h35
  by_cases h37 : σ < 86 / 105
  · simp only [h37, ite_true]; linarith only [not_lt.1 h36]
  simp only [h37, ite_false]
  clear h36
  by_cases h38 : σ < 691 / 840
  · simp only [h38, ite_true]; linarith only [not_lt.1 h37]
  simp only [h38, ite_false]
  clear h37
  by_cases h39 : σ < 347 / 420
  · simp only [h39, ite_true]; linarith only [not_lt.1 h38]
  simp only [h39, ite_false]
  clear h38
  by_cases h40 : σ < 697 / 840
  · simp only [h40, ite_true]; linarith only [not_lt.1 h39]
  simp only [h40, ite_false]
  clear h39
  by_cases h41 : σ < 5 / 6
  · simp only [h41, ite_true]; linarith only [not_lt.1 h40]
  simp only [h41, ite_false]
  clear h40
  by_cases h42 : σ < 67 / 80
  · simp only [h42, ite_true]; linarith only [not_lt.1 h41]
  simp only [h42, ite_false]
  clear h41
  by_cases h43 : σ < 101 / 120
  · simp only [h43, ite_true]; linarith only [not_lt.1 h42]
  simp only [h43, ite_false]
  clear h42
  by_cases h44 : σ < 203 / 240
  · simp only [h44, ite_true]; linarith only [not_lt.1 h43]
  simp only [h44, ite_false]
  clear h43
  by_cases h45 : σ < 17 / 20
  · simp only [h45, ite_true]; linarith only [not_lt.1 h44]
  simp only [h45, ite_false]
  clear h44
  by_cases h46 : σ < 41 / 48
  · simp only [h46, ite_true]; linarith only [not_lt.1 h45]
  simp only [h46, ite_false]
  clear h45
  by_cases h47 : σ < 103 / 120
  · simp only [h47, ite_true]; linarith only [not_lt.1 h46]
  simp only [h47, ite_false]
  clear h46
  by_cases h48 : σ < 69 / 80
  · simp only [h48, ite_true]; linarith only [not_lt.1 h47]
  simp only [h48, ite_false]
  clear h47
  by_cases h49 : σ < 13 / 15
  · simp only [h49, ite_true]; linarith only [not_lt.1 h48]
  simp only [h49, ite_false]
  clear h48
  by_cases h50 : σ < 209 / 240
  · simp only [h50, ite_true]; linarith only [not_lt.1 h49]
  simp only [h50, ite_false]
  clear h49
  by_cases h51 : σ < 7 / 8
  · simp only [h51, ite_true]; linarith only [not_lt.1 h50]
  simp only [h51, ite_false]
  clear h50
  by_cases h52 : σ < 211 / 240
  · simp only [h52, ite_true]; linarith only [not_lt.1 h51]
  simp only [h52, ite_false]
  clear h51
  by_cases h53 : σ < 53 / 60
  · simp only [h53, ite_true]; linarith only [not_lt.1 h52]
  simp only [h53, ite_false]
  clear h52
  by_cases h54 : σ < 71 / 80
  · simp only [h54, ite_true]; linarith only [not_lt.1 h53]
  simp only [h54, ite_false]
  clear h53
  by_cases h55 : σ < 107 / 120
  · simp only [h55, ite_true]; linarith only [not_lt.1 h54]
  simp only [h55, ite_false]
  clear h54
  by_cases h56 : σ < 43 / 48
  · simp only [h56, ite_true]; linarith only [not_lt.1 h55]
  simp only [h56, ite_false]
  clear h55
  by_cases h57 : σ < 9 / 10
  · simp only [h57, ite_true]; linarith only [not_lt.1 h56]
  simp only [h57, ite_false]
  clear h56
  by_cases h58 : σ < 217 / 240
  · simp only [h58, ite_true]; linarith only [not_lt.1 h57]
  simp only [h58, ite_false]
  clear h57
  by_cases h59 : σ < 109 / 120
  · simp only [h59, ite_true]; linarith only [not_lt.1 h58]
  simp only [h59, ite_false]
  clear h58
  by_cases h60 : σ < 73 / 80
  · simp only [h60, ite_true]; linarith only [not_lt.1 h59]
  simp only [h60, ite_false]
  clear h59
  linarith only [not_lt.1 h60]

lemma g7_half : g7 (1 / 2) = 1 := by unfold g7; norm_num

open scoped Classical in
/-- **`CGLDensity` on `[5/7, 16/21]` as counts of the curve**: at `ε = 1/8400`,
`(7/3)(1 − σ) + 1/8400 ≤ (7/3 + 1/2000)(1 − σ)` for `σ ≤ 16/21`, and `1 ≤ (1 + log qT)^{10}`. -/
theorem rangeCounts_cgl (hCGL : LinnikCGL.CGLDensity) :
    RangeCounts (fun σ => 14003 / 6000 * (1 - σ)) (5 / 7) (16 / 21) := by
  obtain ⟨C₂, hC₂⟩ := hCGL (1 / 8400) (by norm_num)
  refine ⟨max 0 C₂, le_max_left _ _, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by linarith)
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith)
  have hc := hC₂ q σ T hσ hσ1 hT
  have hX : ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) ≤ ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hX0 : 0 ≤ ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) := Real.rpow_nonneg (by linarith) _
  calc _ ≤ C₂ * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) := hc
    _ ≤ max 0 C₂ * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + 1 / 8400) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hX0
    _ ≤ max 0 C₂ * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * 1 := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hX (le_max_left _ _)
    _ ≤ max 0 C₂ * ((q : ℝ) * T) ^ (14003 / 6000 * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr

open scoped Classical in
/-- **The counts of the curve** (`CurveCounts g7`) under `CGLDensity` and `PYWeyl`: the trivial count, the sixty steps,
`rangeCounts_cgl` and `charDensity_hy_top`, glued. -/
theorem counts_7 (hCGL : LinnikCGL.CGLDensity) (hPY : LinnikWeyl.PYWeyl) : CurveCounts g7 :=
  curveCounts_of_range <| rangeCounts_glue (rangeCounts_trivial _ _) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_0) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_1) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_2) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_3) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_4) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_5) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_6) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_7) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_8) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_9) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_10) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_11) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_12) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_13) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_14) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_15) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_16) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_17) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_18) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_in7_19) <|
    rangeCounts_glue (rangeCounts_cgl hCGL) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_0) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_1) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_2) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_3) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_4) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_5) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_6) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_7) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_8) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_9) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_10) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_11) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_12) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_13) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_14) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_15) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_16) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_17) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_18) <|
    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_hx7_19) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_0 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_1 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_2 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_3 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_4 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_5 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_6 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_7 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_8 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_9 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_10 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_11 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_12 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_13 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_14 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_15 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_16 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_17 hPY)) <|
    rangeCounts_glue (rangeCounts_of_density (LinnikStairs7.charDensity_hy_18 hPY)) <|
    rangeCounts_of_density (LinnikStairs7.charDensity_hy_top hPY)

/-- **The window's exponents** at `L = 227/100` on `[4048/10000, 4858/10000]·L`: every piece at its corners. -/
theorem window_7 : WindowOK g7 (227 / 100) (4048 / 10000 * (227 / 100)) (4858 / 10000 * (227 / 100)) :=
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
/-- **Proposition 3′ at `L = 227/100` on `[4048/10000, 4858/10000]·L`, for the curve `g7`**, under `CGLDensity` and
`PYWeyl`: `typeII_gen`. -/
theorem typeII_227 (hCGL : LinnikCGL.CGLDensity) (hPY : LinnikWeyl.PYWeyl) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (4048 / 10000 * (227 / 100) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (4858 / 10000 * (227 / 100) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (227 / 100 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ ((227 / 100 : ℝ) - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen g7_le_one g7_half (counts_7 hCGL hPY) window_7 hf0 hsupp K₀ he₁ hη hη1

end SieveTypeIIU227

#print axioms SieveTypeIIU227.counts_7
#print axioms SieveTypeIIU227.window_7
#print axioms SieveTypeIIU227.typeII_227
