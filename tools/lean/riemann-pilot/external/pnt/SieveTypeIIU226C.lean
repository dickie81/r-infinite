/-
# Round 622: the curve `g7` without Petrow–Young's bound, `g7c`, at `L = 226/100`: its Halász–Montgomery window and
Proposition 3′ there under Chen–Gupta–Li's estimate alone

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_226c`). Under `LinnikCGL.CGLDensity` alone, Proposition 3′ with the Halász–Montgomery bound
per bin (`SieveTypeIIHM.typeII_gen_hm`, round 621) at `L = 226/100` on round 614's window `[4075/10000, 4835/10000]·L`
for the curve `g7c`: round 612's `g7` below `5/6` (the trivial count below `4/7`, twenty Ingham steps, `7/3 + 1/2000`
on `[5/7, 16/21]`, twenty Huxley steps) and `(101/50)(1 − σ)` from `5/6` on (`LinnikStep.charDensity_step`, as round
609's `gU`), in place of `g7`'s twenty Petrow–Young steps.

* `g7c`, `g7c_le_one`, `g7c_half`; `counts_7c`: `CurveCounts g7c` under `CGLDensity`, glued as `counts_7` up to `5/6`
  and from `charDensity_step` above it.
* `window_226c`: `WindowOKHM g7c L m₁ m₂ (1/1000) (1/1000)` at `L = 226/100` on round 614's window: the 42 pieces
  below `5/6` by orthogonality at their corners (round 612's tactic `corners`; round 614's `window_6` has the same
  pieces there), the top piece `[5/6, 11/12]` by `windowPieceHM_const_split` at its 24 corners (`cornersHM`).
* `typeII_226c`: `typeII_gen_hm` at `g7c`, under `CGLDensity`.

The file imports `SieveTypeIIU227.lean` (for `rangeCounts_cgl`, `LinnikStairs7` and `corners`), `LinnikStep.lean` and
`SieveTypeIIHM.lean`.
-/
import SieveTypeIIU227
import LinnikStep
import SieveTypeIIHM

open Complex Real Finset

noncomputable section

namespace SieveTypeIIU226C

open DirichletCharacter SieveTypeIIGen SieveCurveGlue SieveTypeIIU227 SieveTypeIIHM

set_option hygiene false in
/-- The corner cases of `windowPieceHM_const_split`: two values of `β`, two of `m`, two of `w`, each by `norm_num`. -/
macro "cornersHM" : tactic =>
  `(tactic| (intro β m w hb hm hw
             rcases hb with rfl | rfl <;> rcases hm with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num))

/-- The curve: `g7` below `5/6` (`1` below `4/7`, then forty-one steps `A(1 − σ)`), and `(101/50)(1 − σ)` from `5/6`
on. -/
def g7c (σ : ℝ) : ℝ :=
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
  (101 / 50) * (1 - σ)

/-- `g7c ≤ 1`: on each step `A(1 − σ) ≤ A(1 − lo) ≤ 1`, and `(101/50)(1 − σ) ≤ 101/300` from `5/6` on. -/
lemma g7c_le_one (σ : ℝ) : g7c σ ≤ 1 := by
  unfold g7c
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
  linarith only [not_lt.1 h41]

lemma g7c_half : g7c (1 / 2) = 1 := by unfold g7c; norm_num

/-- **The counts of the curve** (`CurveCounts g7c`) under `CGLDensity` (`hCGL`): the trivial count, the twenty Ingham
steps, `7/3 + 1/2000` on `[5/7, 16/21]` and the twenty Huxley steps of `counts_7` up to `5/6`, and
`LinnikStep.charDensity_step` from `5/6` on. -/
theorem counts_7c (hCGL : LinnikCGL.CGLDensity) : CurveCounts g7c :=
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
    rangeCounts_of_density LinnikStep.charDensity_step

/-- **The window's exponents** at `L = 226/100` on `[4075/10000, 4835/10000]·L`, with the Halász–Montgomery branch on
the top piece. -/
theorem window_226c : WindowOKHM g7c (226 / 100) (4075 / 10000 * (226 / 100)) (4835 / 10000 * (226 / 100))
    (1 / 1000) (1 / 1000) :=
  windowOKHM_of_piece <| windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_one (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 840199 / 398000) (lo := 4 / 7) (hi := 81 / 140)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 140033 / 66000) (lo := 81 / 140) (hi := 41 / 70)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 840197 / 394000) (lo := 41 / 70) (hi := 83 / 140)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 30007 / 14000) (lo := 83 / 140) (hi := 3 / 5)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 56013 / 26000) (lo := 3 / 5) (hi := 17 / 28)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 420097 / 194000) (lo := 17 / 28) (hi := 43 / 70)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 840193 / 386000) (lo := 43 / 70) (hi := 87 / 140)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 547 / 250) (lo := 87 / 140) (hi := 22 / 35)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 840191 / 382000) (lo := 22 / 35) (hi := 89 / 140)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 84019 / 38000) (lo := 89 / 140) (hi := 9 / 14)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 40009 / 18000) (lo := 9 / 14) (hi := 13 / 20)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 210047 / 94000) (lo := 13 / 20) (hi := 23 / 35)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 840187 / 374000) (lo := 23 / 35) (hi := 93 / 140)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 140031 / 62000) (lo := 93 / 140) (hi := 47 / 70)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 168037 / 74000) (lo := 47 / 70) (hi := 19 / 28)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 105023 / 46000) (lo := 19 / 28) (hi := 24 / 35)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 280061 / 122000) (lo := 24 / 35) (hi := 97 / 140)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 60013 / 26000) (lo := 97 / 140) (hi := 7 / 10)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 840181 / 362000) (lo := 7 / 10) (hi := 99 / 140)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 14003 / 6000) (lo := 99 / 140) (hi := 5 / 7)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 14003 / 6000) (lo := 5 / 7) (hi := 16 / 21)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 14003 / 6000) (lo := 16 / 21) (hi := 643 / 840)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 560121 / 242000) (lo := 643 / 840) (hi := 323 / 420)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 280061 / 122000) (lo := 323 / 420) (hi := 649 / 840)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 560123 / 246000) (lo := 649 / 840) (hi := 163 / 210)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 140031 / 62000) (lo := 163 / 210) (hi := 131 / 168)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 4481 / 2000) (lo := 131 / 168) (hi := 47 / 60)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 40009 / 18000) (lo := 47 / 60) (hi := 661 / 840)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 560127 / 254000) (lo := 661 / 840) (hi := 83 / 105)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 547 / 250) (lo := 83 / 105) (hi := 667 / 840)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 560129 / 258000) (lo := 667 / 840) (hi := 67 / 84)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 56013 / 26000) (lo := 67 / 84) (hi := 673 / 840)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 560131 / 262000) (lo := 673 / 840) (hi := 169 / 210)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 140033 / 66000) (lo := 169 / 210) (hi := 97 / 120)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 80019 / 38000) (lo := 97 / 120) (hi := 341 / 420)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 280067 / 134000) (lo := 341 / 420) (hi := 137 / 168)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 112027 / 54000) (lo := 137 / 168) (hi := 86 / 105)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 70017 / 34000) (lo := 86 / 105) (hi := 691 / 840)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 560137 / 274000) (lo := 691 / 840) (hi := 347 / 420)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 280069 / 138000) (lo := 347 / 420) (hi := 697 / 840)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_glue (windowPieceHM_of_piece <|
      windowPiece_const (A := 560139 / 278000) (lo := 697 / 840) (hi := 5 / 6)
        (by norm_num) (by norm_num) (by corners) (by corners)) <|
    windowPieceHM_const_split (A := 101 / 50) (lo := 5 / 6) (hi := 11 / 12)
      (by norm_num) (by cornersHM) (by cornersHM) (by cornersHM)

open scoped ContDiff in
/-- **Proposition 3′ at `L = 226/100` on `[4075/10000, 4835/10000]·L`, for the curve `g7c`**, under `CGLDensity`
(`hCGL`) alone: `typeII_gen_hm` for `f0` smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀`, `e₁ > 0` (`he₁`) and
`0 < η ≤ 10⁻⁵` (`hη`, `hη1`). -/
theorem typeII_226c (hCGL : LinnikCGL.CGLDensity) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
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
  typeII_gen_hm g7c_le_one g7c_half (counts_7c hCGL) window_226c hf0 hsupp K₀ he₁ hη hη1

end SieveTypeIIU226C

#print axioms SieveTypeIIU226C.counts_7c
#print axioms SieveTypeIIU226C.window_226c
#print axioms SieveTypeIIU226C.typeII_226c
