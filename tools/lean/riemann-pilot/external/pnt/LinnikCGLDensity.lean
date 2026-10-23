/-
# Round 702: Chen–Gupta–Li's density estimate on `[5/7, 16/21]` for every `ε` (`LinnikCGL.CGLDensity`)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 607 displayed Chen–Gupta–Li's zero-density estimate on `[5/7, 16/21]` as the hypothesis `LinnikCGL.CGLDensity`.
Rounds 636–637's step (`LinnikCGLStep`) gives the count at the exponent `(7/3 + 1/2000)(1 − σ)` from their Proposition
3.1, which round 700 proved (`LinnikCGLHB101.prop31`). Round 702 makes the step's internal `ε` a field of its
parameters (`LinnikCGLStep.ParC.e`). This file takes it to `0`, proves `CGLDensity`, and so gives
`Linnik225C.linnik_225c` and `Linnik226C.linnik_226c` with no hypothesis.

The stack's form.
* `parCGLe e` is `parCGL`'s parameters at the internal `ε = e`: `a = 7/9 + 2e`, `λ = 7/6 + 9e/2`, `A_i = 7/3 + 25e`
  and `A = 7/3 + 26e`. For `0 < e ≤ 1/100000` they are `Good`: the exponent conditions are linear in `σ` with
  coefficients linear in `e`, and `nlinarith` closes them with `e(σ − 5/7) ≥ 0` and `e(16/21 − σ) ≥ 0`.
* At `e = min(1/100000, ε/16)`, `26e(1 − σ) ≤ ε/2` on `[5/7, 16/21]`, and Mathlib's `Real.log_le_rpow_div` gives
  `(log qT)^{10} ≤ (20/ε)^{10}(qT)^{ε/2}`.

Plain statements, with `q ≥ 1` where `[NeZero q]`.
* `parCGLe`, `parCGLe_good`: the parameters above; for `0 < e ≤ 1/100000` they are `Good`.
* `charDensity_e`: for `0 < e ≤ 1/100000` there is `C ≥ 0` such that, for `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at
  most `C(qT)^{(7/3+26e)(1−σ)}(log qT)^{10}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`,
  `|Im s| ≤ T`.
* `log_pow_ten_le`: for `x ≥ 1` and `ε > 0`, `(log x)^{10} ≤ (20/ε)^{10}x^{ε/2}`.
* `cglDensity`: round 607's `CGLDensity`: for every `ε > 0` there is `C` such that, for `q ≥ 1`, `5/7 ≤ σ ≤ 16/21`
  and `T ≥ 2`, at most `C(qT)^{(7/3)(1−σ)+ε}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`,
  `|Im s| ≤ T`.
* `linnik_225c`, `linnik_226c`: `Linnik225C.linnik_225c` and `Linnik226C.linnik_226c` at `cglDensity`: there is `K`
  such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{9/4}`; and
  likewise with `p ≤ Kq^{226/100}`.

The file imports `LinnikCGLHB101.lean`.
-/

import LinnikCGLHB101

open Real

noncomputable section

namespace LinnikCGLDensity

open LinnikCGLStep

/-- The step's parameters at the internal `ε = e`: `parCGL`'s, with `a = 7/9 + 2e`, `λ = 7/6 + 9e/2`,
`A_i = 7/3 + 25e` and `A = 7/3 + 26e`. -/
def parCGLe (e : ℝ) : ParC where
  M := 1556
  a := 7 / 9 + 2 * e
  lam := 7 / 6 + 9 / 2 * e
  lo := 5 / 7
  hi := 16 / 21
  Ai := 7 / 3 + 25 * e
  A := 7 / 3 + 26 * e
  e := e

/-- For `0 < e ≤ 1/100000`, `parCGLe e` is `Good`. -/
theorem parCGLe_good {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 100000) : (parCGLe e).Good where
  he := he
  he1 := he1
  hM := by simp [parCGLe]
  ha := by simp only [parCGLe]; linarith
  hat := by simp only [parCGLe]; push_cast; linarith
  hlam1 := by simp only [parCGLe]; linarith
  hlam2 := by simp only [parCGLe]; linarith
  hlam3 := by simp only [parCGLe]; linarith
  hlo := by simp only [parCGLe]; norm_num
  hhi := by simp only [parCGLe]; norm_num
  hc := by
    intro σ h1 h2
    simp only [parCGLe] at *
    have p1 := mul_nonneg he.le (sub_nonneg.2 h1)
    have p2 := mul_nonneg he.le (sub_nonneg.2 h2)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parCGLe] at *
    have p1 := mul_nonneg he.le (sub_nonneg.2 h1)
    have p2 := mul_nonneg he.le (sub_nonneg.2 h2)
    nlinarith
  h4 := by
    intro σ h2
    simp only [parCGLe] at *
    push_cast
    have p2 := mul_nonneg he.le (sub_nonneg.2 h2)
    nlinarith
  hA := by simp only [parCGLe]; linarith
  hA10 := by simp only [parCGLe]; linarith

open scoped Classical in
/-- **The density count at the internal `ε = e`**: for `0 < e ≤ 1/100000` there is `C ≥ 0` such that, for `q ≥ 1`,
`5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most `C(qT)^{(7/3+26e)(1−σ)}(log qT)^{10}` characters mod `q` have an `L`-function
with a zero in `Re s ≥ σ`, `|Im s| ≤ T` (rounds 636–637's `charDensity_cglGen` at round 700's `prop31`). -/
theorem charDensity_e {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 100000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 7 ≤ σ → σ ≤ 16 / 21 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((7 / 3 + 26 * e) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_cglGen LinnikCGLHB101.prop31 (parCGLe e) (parCGLe_good he he1)

/-- For `x ≥ 1` and `ε > 0`, `(log x)^{10} ≤ (20/ε)^{10}x^{ε/2}`. -/
lemma log_pow_ten_le {x ε : ℝ} (hx1 : 1 ≤ x) (hε : 0 < ε) :
    Real.log x ^ (10 : ℝ) ≤ (20 / ε) ^ (10 : ℝ) * x ^ (ε / 2) := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ x ^ (ε / 20) / (ε / 20) := Real.log_le_rpow_div hx0.le (by positivity)
  calc Real.log x ^ (10 : ℝ) ≤ (x ^ (ε / 20) / (ε / 20)) ^ (10 : ℝ) :=
        Real.rpow_le_rpow hlog0 hlog (by norm_num)
    _ = (20 / ε) ^ (10 : ℝ) * x ^ (ε / 2) := by
        rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0.le, inv_div,
          mul_comm]
        congr 2
        ring

open scoped Classical in
/-- **Chen–Gupta–Li's density estimate on `[5/7, 16/21]`**, round 607's `LinnikCGL.CGLDensity`: for every `ε > 0`
there is `C` such that, for `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most `C(qT)^{(7/3)(1−σ)+ε}` characters mod `q`
have an `L`-function with a zero in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem cglDensity : LinnikCGL.CGLDensity := by
  intro ε hε
  have he : 0 < min (1 / 100000 : ℝ) (ε / 16) := lt_min (by norm_num) (by positivity)
  have he1 : min (1 / 100000 : ℝ) (ε / 16) ≤ 1 / 100000 := min_le_left _ _
  have heε : min (1 / 100000 : ℝ) (ε / 16) ≤ ε / 16 := min_le_right _ _
  obtain ⟨C, hC, hcount⟩ := charDensity_e he he1
  refine ⟨C * (20 / ε) ^ (10 : ℝ), ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hx1 : 1 ≤ (q : ℝ) * T := by nlinarith
  have hx0 : 0 < (q : ℝ) * T := by linarith
  have hlog := log_pow_ten_le hx1 hε
  have hexp : (7 / 3 + 26 * min (1 / 100000 : ℝ) (ε / 16)) * (1 - σ) + ε / 2 ≤ 7 / 3 * (1 - σ) + ε := by
    have h1σ : 1 - σ ≤ 2 / 7 := by linarith
    have h0σ : 0 ≤ 1 - σ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1σ he.le, mul_le_mul_of_nonneg_right heε h0σ]
  have h20 : 0 ≤ (20 / ε) ^ (10 : ℝ) := by positivity
  calc _ ≤ C * ((q : ℝ) * T) ^ ((7 / 3 + 26 * min (1 / 100000 : ℝ) (ε / 16)) * (1 - σ)) *
          Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hcount q σ T hσ hσ1 hT
    _ ≤ C * ((q : ℝ) * T) ^ ((7 / 3 + 26 * min (1 / 100000 : ℝ) (ε / 16)) * (1 - σ)) *
          ((20 / ε) ^ (10 : ℝ) * ((q : ℝ) * T) ^ (ε / 2)) := by gcongr
    _ = C * (20 / ε) ^ (10 : ℝ) * (((q : ℝ) * T) ^ ((7 / 3 + 26 * min (1 / 100000 : ℝ) (ε / 16)) * (1 - σ)) *
          ((q : ℝ) * T) ^ (ε / 2)) := by ring
    _ = C * (20 / ε) ^ (10 : ℝ) * ((q : ℝ) * T) ^ ((7 / 3 + 26 * min (1 / 100000 : ℝ) (ε / 16)) * (1 - σ) +
          ε / 2) := by rw [← Real.rpow_add hx0]
    _ ≤ C * (20 / ε) ^ (10 : ℝ) * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + ε) := by
        gcongr

/-! ### Round 622's and round 625's theorems with no hypothesis -/

/-- **Linnik's theorem with exponent `9/4`**, `Linnik225C.linnik_225c` at `cglDensity`: there is `K` such that for
every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{9/4}`. -/
theorem linnik_225c : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  Linnik225C.linnik_225c cglDensity

/-- **Linnik's theorem with exponent `226/100`**, `Linnik226C.linnik_226c` at `cglDensity`: there is `K` such that
for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{226/100}`. -/
theorem linnik_226c : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  Linnik226C.linnik_226c cglDensity

end LinnikCGLDensity

#print axioms LinnikCGLDensity.parCGLe_good
#print axioms LinnikCGLDensity.charDensity_e
#print axioms LinnikCGLDensity.cglDensity
#print axioms LinnikCGLDensity.linnik_225c
#print axioms LinnikCGLDensity.linnik_226c
