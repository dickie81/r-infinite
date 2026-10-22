/-
# Round 636: Linnik's exponents `9/4` and `226/100` from Chen–Gupta–Li's large-values estimate

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`linnik_225c_lv`): if `LinnikCGLLV.CGLLargeValues` holds, there is `K` such that for every `q ≥ 1`
and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{9/4}`. Plain statement (`linnik_226c_lv`):
the same with `p ≤ K·q^{226/100}`.

`Linnik225C.linnik_225c` and `Linnik226C.linnik_226c` take `LinnikCGL.CGLDensity` as their hypothesis and use it once,
through `SieveTypeIIU227.rangeCounts_cgl`: the counts `C(qT)^{(14003/6000)(1−σ)}(1 + log qT)^{10}` on `[5/7, 16/21]`.
Here those counts come from `LinnikCGLStep.charDensity_cgl` instead, and the two theorems are re-assembled with their
own windows, grids and certificates.

* `rangeCounts_lv`: `charDensity_cgl` as `RangeCounts`.
* `counts_7c_lv`: `SieveTypeIIU226C.counts_7c`'s glue with `rangeCounts_lv` in place of `rangeCounts_cgl`.
* `typeII225c_lv`, `typeII226c_lv`: `typeII_gen_hm` at `g7c` on the windows `window_225c` and `window_226c`.
* `linnik_225c_lv`, `linnik_226c_lv`: `SieveMain.linnik_route_lt` with round 625's certificate, and
  `SieveMain.linnik_route` with round 614's.

The file imports `Linnik225C.lean`, `Linnik226C.lean` and `LinnikCGLStep.lean`.
-/
import Linnik225C
import Linnik226C
import LinnikCGLStep

open Complex Real Finset

noncomputable section

namespace LinnikCGLLinnik

open DirichletCharacter SieveTypeIIGen SieveCurveGlue SieveTypeIIU227 SieveTypeIIHM SieveTypeIIU226C SieveCert
  SieveRoute SieveQ

/-- **The counts on `[5/7, 16/21]` from the large values**: `LinnikCGLStep.charDensity_cgl` as `RangeCounts`, with
`7/3 + 1/2000 = 14003/6000`. -/
theorem rangeCounts_lv (h : LinnikCGLLV.CGLLargeValues) :
    RangeCounts (fun σ => 14003 / 6000 * (1 - σ)) (5 / 7) (16 / 21) := by
  have h1 := rangeCounts_of_density (LinnikCGLStep.charDensity_cgl h)
  have e : (7 / 3 + 1 / 2000 : ℝ) = 14003 / 6000 := by norm_num
  rw [e] at h1
  exact h1

/-- **The counts of the curve `g7c` from the large values**: `SieveTypeIIU226C.counts_7c`'s glue, with
`rangeCounts_lv` in place of `rangeCounts_cgl`. -/
theorem counts_7c_lv (h : LinnikCGLLV.CGLLargeValues) : CurveCounts g7c :=
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
    rangeCounts_glue (rangeCounts_lv h) <|
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

/-- **`typeII_gen_hm` at `g7c` on `window_225c`, from the large values**, as `TypeIIAt` at `Linnik225C.route225C`. -/
theorem typeII225c_lv (h : LinnikCGLLV.CGLLargeValues) : @TypeIIAt Linnik225C.route225C := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact typeII_gen_hm g7c_le_one g7c_half (counts_7c_lv h) SieveTypeIIU225C.window_225c hf0 hsupp K₀ he₁ hη hη1

/-- **`typeII_gen_hm` at `g7c` on `window_226c`, from the large values**, as `TypeIIAt` at `Linnik226.route226`. -/
theorem typeII226c_lv (h : LinnikCGLLV.CGLLargeValues) : @TypeIIAt Linnik226.route226 := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact typeII_gen_hm g7c_le_one g7c_half (counts_7c_lv h) window_226c hf0 hsupp K₀ he₁ hη hη1

/-- **Linnik's theorem with exponent `9/4`, from Chen–Gupta–Li's large-values estimate** (`h`). There is `K` such
that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{9/4}`. -/
theorem linnik_225c_lv (h : LinnikCGLLV.CGLLargeValues) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  @SieveMain.linnik_route_lt Linnik225C.route225C Linnik225C.routeOK225C grid225C gridOK225C Linnik225C.fits225C
    (typeII225c_lv h) total_lt_225C

/-- **Linnik's theorem with exponent `226/100`, from Chen–Gupta–Li's large-values estimate** (`h`). There is `K` such
that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{226/100}`. -/
theorem linnik_226c_lv (h : LinnikCGLLV.CGLLargeValues) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  @SieveMain.linnik_route Linnik226.route226 Linnik226.routeOK226 grid226 gridOK226 Linnik226.fits226
    (typeII226c_lv h) total_le_226

end LinnikCGLLinnik

#print axioms LinnikCGLLinnik.rangeCounts_lv
#print axioms LinnikCGLLinnik.counts_7c_lv
#print axioms LinnikCGLLinnik.linnik_225c_lv
#print axioms LinnikCGLLinnik.linnik_226c_lv
