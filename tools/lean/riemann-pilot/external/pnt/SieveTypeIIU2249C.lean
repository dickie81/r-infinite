/-
# Round 710: Proposition 3′ at `L = 2249/1000` on the Halász–Montgomery window `[41249/100000, 48104/100000]·L`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

The curve `g7c` of `SieveTypeIIU226C.lean` (round 622: round 612's `g7` below `5/6`, `(101/50)(1 − σ)` from `5/6` on)
with the Type II bound of `SieveTypeIIHM.typeII_gen_hm` (round 621), as round 625's `SieveTypeIIU225C.lean` at
`L = 9/4`: every piece of the window condition `WindowOKHM` holds by orthogonality at its corners except the top
piece `[5/6, 11/12]` for `m ≤ 1`, which holds by the Halász–Montgomery branch at its corners
(`windowPieceHM_const_split`). The window's ends are written over `100000`.

* `window_2249c`: `WindowOKHM g7c L m₁ m₂ (1/1000) (1/1000)` at `L = 2249/1000` on `[41249/100000, 48104/100000]·L`.
* `typeII_2249c`: `typeII_gen_hm` at `g7c`, under `CGLDensity` (`hCGL`).

The file imports `SieveTypeIIU226C.lean` (for `g7c`, `counts_7c` and, through `SieveTypeIIU227.lean`, the tactic
`corners`) and `SieveTypeIIHM.lean`.
-/
import SieveTypeIIU226C
import SieveTypeIIHM

namespace SieveTypeIIU2249C

open DirichletCharacter SieveTypeIIGen SieveCurveGlue SieveTypeIIU227 SieveTypeIIU226C SieveTypeIIHM

set_option hygiene false in
/-- The corner cases of `windowPieceHM_const_split`: two values of `β`, two of `m`, two of `w`, each by `norm_num`. -/
macro "cornersHM" : tactic =>
  `(tactic| (intro β m w hb hm hw
             rcases hb with rfl | rfl <;> rcases hm with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num))

/-- **The window's exponents** at `L = 2249/1000` on `[41249/100000, 48104/100000]·L`, with the Halász–Montgomery
branch on the top piece. -/
theorem window_2249c : WindowOKHM g7c (2249 / 1000) (41249 / 100000 * (2249 / 1000)) (48104 / 100000 * (2249 / 1000))
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
/-- **Proposition 3′ at `L = 2249/1000` on `[41249/100000, 48104/100000]·L`, for the curve `g7c`**, under
`CGLDensity` (`hCGL`): `typeII_gen_hm` for `f0` smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀`, `e₁ > 0`
(`he₁`) and `0 < η ≤ 10⁻⁵` (`hη`, `hη1`). -/
theorem typeII_2249c (hCGL : LinnikCGL.CGLDensity) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (41249 / 100000 * (2249 / 1000) : ℝ) ≤ P →
      (P : ℝ) ≤ (q : ℝ) ^ (48104 / 100000 * (2249 / 1000) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (2249 / 1000 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ ((2249 / 1000 : ℝ) - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen_hm g7c_le_one g7c_half (counts_7c hCGL) window_2249c hf0 hsupp K₀ he₁ hη hη1

end SieveTypeIIU2249C

#print axioms SieveTypeIIU2249C.window_2249c
#print axioms SieveTypeIIU2249C.typeII_2249c
