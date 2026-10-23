/-
# Round 700: Heath-Brown's Theorem 10.1 with characters, and Linnik's exponents `9/4` and `226/100` (stage M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 699's `sig_bound` bounds round 694's `σ(N)` by `((M_BB₁)² + 2M_BA₁)B(N)`, with the factors depending on `q`,
`T`, `δ` and a divisor bound `D`. This file bounds the factors by powers of one quantity, `W = 3C_δ(4Q)^δ/δ` with
`C_δ` round 525's divisor constant and `Q = q(1 + 2T)`, and proves round 670's displayed hypothesis `CGLT101`
(Heath-Brown's Theorem 10.1 with characters, the stage M5 of the CGL plan). With round 693's `cgls3_t101`,
`prop31_t101`, `linnik_225c_t101` and `linnik_226c_t101` it gives, with no hypothesis, Chen–Gupta–Li's Propositions
11.1 and 3.1 at one point per character, rounds 636–637's count of characters with a zero at the exponent
`(7/3 + 1/2000)(1 − σ)` on `[5/7, 16/21]` (`LinnikCGLStep.charDensity_cgl`) and Linnik's theorem with the exponents
`9/4` and `226/100`. `CGLDensity` itself, the count at `(7/3)(1 − σ) + ε` for every `ε > 0`, is not proved here.

The stack's form.
* For `0 < δ ≤ 1`: `d(q)`, `Q^δ` and `J + 1` (with `J = ⌊log₂⌊4Q⌋⌋`, through `2^J ≤ 4Q` and Mathlib's
  `Real.log_le_rpow_div`) are at most `W`; `d(m) ≤ 68W⁵` for `1 ≤ m ≤ L = 4(1 + U₀)Q^{1+δ}`, through round 525's
  `card_divisors_le` and `L^δ ≤ 68W⁴`; so `A₁ ≤ C(1 + 2c_K²)W⁶`, `B₁ ≤ 136C(πC_0)²W¹²` and `M_B ≤ 5826240W¹³` at
  `D = 68W⁵`, and the factor of round 699 is at most `κW⁵⁰`.
* `W⁵⁰ = (3C_δ/δ)⁵⁰(4Q)^{50δ}`; at `δ = min(ε, 1)/50`, `(4Q)^{50δ} ≤ 12(qTN)^ε` for `T, N ≥ 1`, and `B(N)` is at most
  twice `RN + R² + R^{5/4}(qT)^{1/2}`.
* `CGLT101` holds with `Q₀ = 0`: its double sum is round 694's with the weights `c_n`, and positivity with
  `|c_n| ≤ B ≤ B(2M)^{1/2}n^{−1/2}` on `(M, 2M]` bounds it by `2MB²σ(M)`.

Plain statements, with `q ≥ 1` where `[NeZero q]`, `R` the number of points and `Q = q(1 + 2T)`.
* `Wf`, `one_le_four_Q`, `one_le_rpow_fourQ`, `Cdiv_le_W`, `one_le_W`: `W = 3C_δ(4Q)^δ/δ`; for `T ≥ 0`, `4Q ≥ 1` and,
  for `δ > 0`, `(4Q)^δ ≥ 1`; and for `T ≥ 0` and `0 < δ ≤ 1`, `C_δ(4Q)^δ ≤ W` and `W ≥ 1`.
* `dq_le_W`, `Qd_le_W`, `J_le_W`, `dm_le_W`: for `T ≥ 0` and `0 < δ ≤ 1`, `d(q) ≤ W`, `Q^δ ≤ W`, `J + 1 ≤ W`, and
  `d(m) ≤ 68W⁵` for `m ≤ L`.
* `A1_le`, `B1_le`, `U0_le`, `MB_le`, `factor_le`: for `T ≥ 0`, `0 < δ ≤ 1` and `C ≥ 0`, with `D = 68W⁵`:
  `A₁ ≤ C(1 + 2c_K²)W⁶`, `B₁ ≤ 136C(πC_0)²W¹²`, `U₀ ≤ 16W²`, `M_B ≤ 5826240W¹³`, and
  `(M_BB₁)² + 2M_BA₁ ≤ κW⁵⁰` with `κ = (5826240·136C(πC_0)²)² + 2·5826240·C(1 + 2c_K²)`.
* `sqrt_three_le_two`, `Bd_le_qT`: `3^{1/2} ≤ 2`; and for `T ≥ 1` and `N, R ≥ 0`,
  `B(N) ≤ 2(RN + R² + R^{5/4}(qT)^{1/2})`.
* `sig_le_eps`: for `ε > 0` there is `C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`, `N ≥ 1`, points with `|t_r| ≤ T` and the
  points with the same character `1`-separated, `σ(N) ≤ C(qTN)^ε(RN + R² + R^{5/4}(qT)^{1/2})`.
* `cglt101`: round 670's `CGLT101`.
* `cgls3`, `prop31`: round 639's `CGLS3` and round 637's `CGLProp31` (their Propositions 11.1 and 3.1 at one point
  per character).
* `char_density`: there is `C ≥ 0` such that, for `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most
  `C(qT)^{(7/3+1/2000)(1−σ)}(log qT)^{10}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`,
  `|Im s| ≤ T`.
* `linnik_225`, `linnik_226`: there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
  `p ≡ a (mod q)` with `p ≤ Kq^{9/4}`; and likewise with `p ≤ Kq^{226/100}`.

The file imports `LinnikCGLHBIter.lean` and `LinnikCGLP81.lean`.
-/

import LinnikCGLHBIter
import LinnikCGLP81

open Complex Set Real Filter Topology MeasureTheory
open scoped ComplexConjugate Classical

noncomputable section

namespace LinnikCGLHB101

open LinnikCGLMat LinnikCGLReflect LinnikCGLPair LinnikCGLHBPos LinnikCGLHBLen LinnikCGLHBRefl LinnikCGLHBIter
  LinnikCGLT101 LinnikPower

/-! ### The factors as powers of `W = 3C_δ(4Q)^δ/δ` -/

/-- `W = 3C_δ(4Q)^δ/δ`, with `C_δ` round 525's divisor constant and `Q = q(1 + 2T)`. -/
def Wf (δ : ℝ) (q : ℕ) (T : ℝ) : ℝ := 3 * Cdiv δ * (4 * Qq q T) ^ δ / δ

section W

variable {δ : ℝ} {q : ℕ} [NeZero q] {T : ℝ}

lemma one_le_four_Q (hT : 0 ≤ T) : 1 ≤ 4 * Qq q T := by
  have := one_le_Qq (q := q) hT
  linarith

lemma one_le_rpow_fourQ (hT : 0 ≤ T) (hδ : 0 < δ) : 1 ≤ (4 * Qq q T) ^ δ :=
  Real.one_le_rpow (one_le_four_Q hT) hδ.le

/-- For `q ≥ 1`, `T ≥ 0` and `0 < δ ≤ 1`, `C_δ(4Q)^δ ≤ W`. -/
lemma Cdiv_le_W (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Cdiv δ * (4 * Qq q T) ^ δ ≤ Wf δ q T := by
  have hC := one_le_Cdiv hδ hδ1
  have hr := one_le_rpow_fourQ (q := q) hT hδ
  have h3 : (1 : ℝ) ≤ 3 / δ := by rw [le_div_iff₀ hδ]; linarith
  unfold Wf
  calc Cdiv δ * (4 * Qq q T) ^ δ = Cdiv δ * (4 * Qq q T) ^ δ * 1 := (mul_one _).symm
    _ ≤ Cdiv δ * (4 * Qq q T) ^ δ * (3 / δ) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 3 * Cdiv δ * (4 * Qq q T) ^ δ / δ := by ring

lemma one_le_W (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 ≤ Wf δ q T := by
  have hC := one_le_Cdiv hδ hδ1
  have hr := one_le_rpow_fourQ (q := q) hT hδ
  exact le_trans (one_le_mul_of_one_le_of_one_le hC hr) (Cdiv_le_W hT hδ hδ1)

/-- For `q ≥ 1`, `T ≥ 0` and `0 < δ ≤ 1`, `d(q) ≤ W`. -/
lemma dq_le_W (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (q.divisors.card : ℝ) ≤ Wf δ q T := by
  have h1 := card_divisors_le hδ hδ1 q
  have hq : (q : ℝ) ≤ 4 * Qq q T := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    unfold Qq
    nlinarith
  have h2 : (q : ℝ) ^ δ ≤ (4 * Qq q T) ^ δ := Real.rpow_le_rpow (Nat.cast_nonneg q) hq hδ.le
  have hC := one_le_Cdiv hδ hδ1
  calc (q.divisors.card : ℝ) ≤ Cdiv δ * (q : ℝ) ^ δ := h1
    _ ≤ Cdiv δ * (4 * Qq q T) ^ δ := mul_le_mul_of_nonneg_left h2 (by linarith)
    _ ≤ Wf δ q T := Cdiv_le_W hT hδ hδ1

/-- For `q ≥ 1`, `T ≥ 0` and `0 < δ ≤ 1`, `Q^δ ≤ W`. -/
lemma Qd_le_W (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Qq q T ^ δ ≤ Wf δ q T := by
  have hQ := one_le_Qq (q := q) hT
  have h2 : Qq q T ^ δ ≤ (4 * Qq q T) ^ δ := Real.rpow_le_rpow (by linarith) (by linarith) hδ.le
  have hC := one_le_Cdiv hδ hδ1
  have hr : 0 ≤ (4 * Qq q T) ^ δ := by positivity
  calc Qq q T ^ δ ≤ (4 * Qq q T) ^ δ := h2
    _ = 1 * (4 * Qq q T) ^ δ := (one_mul _).symm
    _ ≤ Cdiv δ * (4 * Qq q T) ^ δ := mul_le_mul_of_nonneg_right hC hr
    _ ≤ Wf δ q T := Cdiv_le_W hT hδ hδ1

/-- For `q ≥ 1`, `T ≥ 0` and `0 < δ ≤ 1`, `J + 1 ≤ W` with `J = ⌊log₂⌊4Q⌋⌋`: `2^J ≤ 4Q` and `log(4Q) ≤ (4Q)^δ/δ`. -/
lemma J_le_W (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (Jm q T : ℝ) + 1 ≤ Wf δ q T := by
  have h4 := one_le_four_Q (q := q) hT
  have hn : ⌊4 * Qq q T⌋₊ ≠ 0 := (Nat.floor_pos.2 h4).ne'
  have h2J : ((2 : ℝ) ^ Jm q T) ≤ 4 * Qq q T := by
    have h := Nat.pow_log_le_self 2 hn
    have h' : ((2 ^ Jm q T : ℕ) : ℝ) ≤ (⌊4 * Qq q T⌋₊ : ℝ) := by exact_mod_cast h
    have hf : (⌊4 * Qq q T⌋₊ : ℝ) ≤ 4 * Qq q T := Nat.floor_le (by linarith)
    push_cast at h'
    linarith
  have hlog : (Jm q T : ℝ) * Real.log 2 ≤ (4 * Qq q T) ^ δ / δ := by
    rw [← Real.log_pow]
    exact (Real.log_le_log (by positivity) h2J).trans (Real.log_le_rpow_div (by linarith) hδ)
  have hl2 := Real.log_two_gt_d9
  have hr := one_le_rpow_fourQ (q := q) hT hδ
  have hrd : 1 ≤ (4 * Qq q T) ^ δ / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hJ : (Jm q T : ℝ) ≤ 2 * ((4 * Qq q T) ^ δ / δ) := by
    have hJ0 : (0 : ℝ) ≤ Jm q T := Nat.cast_nonneg _
    nlinarith
  have hC := one_le_Cdiv hδ hδ1
  unfold Wf
  have e : 3 * Cdiv δ * (4 * Qq q T) ^ δ / δ = 3 * Cdiv δ * ((4 * Qq q T) ^ δ / δ) := by ring
  rw [e]
  nlinarith

/-- For `q ≥ 1`, `T ≥ 0`, `0 < δ ≤ 1` and `m ≤ L`, `d(m) ≤ 68W⁵`. -/
lemma dm_le_W (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {m : ℕ} (hm : (m : ℝ) ≤ Lm q T δ) :
    (m.divisors.card : ℝ) ≤ 68 * Wf δ q T ^ 5 := by
  have hW := one_le_W (q := q) hT hδ hδ1
  have hdW := dq_le_W (q := q) hT hδ hδ1
  have hQW := Qd_le_W (q := q) hT hδ hδ1
  have hQ := one_le_Qq (q := q) hT
  have hC := one_le_Cdiv hδ hδ1
  have hCW : Cdiv δ ≤ Wf δ q T := by
    have hr := one_le_rpow_fourQ (q := q) hT hδ
    calc Cdiv δ = Cdiv δ * 1 := (mul_one _).symm
      _ ≤ Cdiv δ * (4 * Qq q T) ^ δ := mul_le_mul_of_nonneg_left hr (by linarith)
      _ ≤ Wf δ q T := Cdiv_le_W hT hδ hδ1
  have hU : U0 q ≤ 16 * Wf δ q T ^ 2 := by
    unfold U0
    have : (q.divisors.card : ℝ) ^ 2 ≤ Wf δ q T ^ 2 := pow_le_pow_left₀ (by positivity) hdW 2
    nlinarith
  have hU0 : 0 ≤ U0 q := by unfold U0; positivity
  -- `L^δ ≤ 68W⁴`
  have hL1 : (4 * (1 + U0 q)) ^ δ ≤ 4 * (1 + U0 q) := by
    have h1 : 1 ≤ 4 * (1 + U0 q) := by linarith
    calc (4 * (1 + U0 q)) ^ δ ≤ (4 * (1 + U0 q)) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hδ1
      _ = 4 * (1 + U0 q) := Real.rpow_one _
  have hL2 : (Qq q T ^ (1 + δ)) ^ δ ≤ Wf δ q T ^ 2 := by
    have hQd1 : 1 ≤ Qq q T ^ δ := Real.one_le_rpow hQ hδ.le
    have e : (Qq q T ^ (1 + δ)) ^ δ = (Qq q T ^ δ) ^ (1 + δ) := by
      rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith), mul_comm]
    rw [e]
    calc (Qq q T ^ δ) ^ (1 + δ) ≤ (Qq q T ^ δ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQd1 (by linarith)
      _ = (Qq q T ^ δ) ^ 2 := Real.rpow_two _
      _ ≤ Wf δ q T ^ 2 := pow_le_pow_left₀ (by positivity) hQW 2
  have hLd : Lm q T δ ^ δ ≤ 68 * Wf δ q T ^ 4 := by
    unfold Lm
    rw [Real.mul_rpow (by positivity) (by positivity)]
    calc (4 * (1 + U0 q)) ^ δ * (Qq q T ^ (1 + δ)) ^ δ ≤ (4 * (1 + U0 q)) * Wf δ q T ^ 2 :=
          mul_le_mul hL1 hL2 (by positivity) (by positivity)
      _ ≤ (4 * (1 + 16 * Wf δ q T ^ 2)) * Wf δ q T ^ 2 := by gcongr
      _ ≤ 68 * Wf δ q T ^ 4 := by nlinarith [pow_le_pow_left₀ zero_le_one hW 2]
  have h1 := card_divisors_le hδ hδ1 m
  have h2 : (m : ℝ) ^ δ ≤ Lm q T δ ^ δ := Real.rpow_le_rpow (Nat.cast_nonneg m) hm hδ.le
  calc (m.divisors.card : ℝ) ≤ Cdiv δ * (m : ℝ) ^ δ := h1
    _ ≤ Cdiv δ * (68 * Wf δ q T ^ 4) := mul_le_mul_of_nonneg_left (h2.trans hLd) (by linarith)
    _ ≤ Wf δ q T * (68 * Wf δ q T ^ 4) := mul_le_mul_of_nonneg_right hCW (by positivity)
    _ = 68 * Wf δ q T ^ 5 := by ring

end W

/-! ### The factors of the iteration in powers of `W` -/

section Factors

variable {δ C : ℝ} {K : ℕ} {q : ℕ} [NeZero q] {T : ℝ}

/-- For `q ≥ 1`, `T ≥ 0`, `0 < δ ≤ 1` and `C ≥ 0`, `A₁ ≤ C(1 + 2c_K²)W⁶`. -/
lemma A1_le (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) :
    A1 C K q ≤ C * (1 + 2 * ctail K ^ 2) * Wf δ q T ^ 6 := by
  have hW := one_le_W (q := q) hT hδ hδ1
  have hd := dq_le_W (q := q) hT hδ hδ1
  have hd6 : (q.divisors.card : ℝ) ^ 6 ≤ Wf δ q T ^ 6 := pow_le_pow_left₀ (by positivity) hd 6
  have hW6 : 1 ≤ Wf δ q T ^ 6 := one_le_pow₀ hW
  have hct := ctail_nonneg K
  unfold A1
  calc C * (1 + 2 * ctail K ^ 2 * (q.divisors.card : ℝ) ^ 6)
      ≤ C * (Wf δ q T ^ 6 + 2 * ctail K ^ 2 * Wf δ q T ^ 6) := by gcongr
    _ = C * (1 + 2 * ctail K ^ 2) * Wf δ q T ^ 6 := by ring

/-- For `q ≥ 1`, `T ≥ 0`, `0 < δ ≤ 1`, `C ≥ 0` and `D = 68W⁵`, `B₁ ≤ 136C(πC_0)²W¹²`. -/
lemma B1_le (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) :
    LinnikCGLHBIter.B1 C (68 * Wf δ q T ^ 5) q T ≤ 136 * C * (Real.pi * CGK 0) ^ 2 * Wf δ q T ^ 12 := by
  have hW := one_le_W (q := q) hT hδ hδ1
  have hd := dq_le_W (q := q) hT hδ hδ1
  have hJ := J_le_W (q := q) hT hδ hδ1
  have hC0 := CGK_pos 0
  have hQ0W : Q0 q ≤ Real.pi * CGK 0 * Wf δ q T ^ 3 := (Q0_le (NeZero.ne q)).trans (by gcongr)
  have hQ00 := Q0_nonneg q
  unfold LinnikCGLHBIter.B1
  calc 2 * C * Q0 q ^ 2 * (68 * Wf δ q T ^ 5) * ((Jm q T : ℝ) + 1)
      ≤ 2 * C * (Real.pi * CGK 0 * Wf δ q T ^ 3) ^ 2 * (68 * Wf δ q T ^ 5) * Wf δ q T := by gcongr
    _ = 136 * C * (Real.pi * CGK 0) ^ 2 * Wf δ q T ^ 12 := by ring

lemma U0_le (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : U0 q ≤ 16 * Wf δ q T ^ 2 := by
  have hW := one_le_W (q := q) hT hδ hδ1
  have hd := dq_le_W (q := q) hT hδ hδ1
  have : (q.divisors.card : ℝ) ^ 2 ≤ Wf δ q T ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
  unfold U0
  nlinarith

/-- For `q ≥ 1`, `T ≥ 0`, `0 < δ ≤ 1` and `D = 68W⁵`, `M_B ≤ 5826240W¹³`. -/
lemma MB_le (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MB (68 * Wf δ q T ^ 5) q T δ ≤ 5826240 * Wf δ q T ^ 13 := by
  have hW := one_le_W (q := q) hT hδ hδ1
  have hd := dq_le_W (q := q) hT hδ hδ1
  have hQW := Qd_le_W (q := q) hT hδ hδ1
  have hU := U0_le (q := q) hT hδ hδ1
  have hU0 : 0 ≤ U0 q := by unfold U0; positivity
  have h1 : 2 * Qq q T ^ δ + 2 * U0 q + 1 ≤ 35 * Wf δ q T ^ 2 := by
    nlinarith [pow_le_pow_left₀ zero_le_one hW 2]
  have hQd : 0 ≤ Qq q T ^ δ := by have := one_le_Qq (q := q) hT; positivity
  unfold MB
  calc 36 * (q.divisors.card : ℝ) * (68 * Wf δ q T ^ 5) ^ 2 * (2 * Qq q T ^ δ + 2 * U0 q + 1)
      ≤ 36 * Wf δ q T * (68 * Wf δ q T ^ 5) ^ 2 * (35 * Wf δ q T ^ 2) := by gcongr
    _ = 5826240 * Wf δ q T ^ 13 := by ring

/-- **The factors**: for `q ≥ 1`, `T ≥ 0`, `0 < δ ≤ 1`, `C ≥ 0` and `D = 68W⁵`, `(M_BB₁)² + 2M_BA₁ ≤ κW⁵⁰` with
`κ = (5826240·136C(πC_0)²)² + 2·5826240·C(1 + 2c_K²)`. -/
lemma factor_le (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) :
    (MB (68 * Wf δ q T ^ 5) q T δ * LinnikCGLHBIter.B1 C (68 * Wf δ q T ^ 5) q T) ^ 2 +
        2 * (MB (68 * Wf δ q T ^ 5) q T δ * A1 C K q) ≤
      ((5826240 * (136 * C * (Real.pi * CGK 0) ^ 2)) ^ 2 + 2 * (5826240 * (C * (1 + 2 * ctail K ^ 2)))) *
        Wf δ q T ^ 50 := by
  have hW := one_le_W (q := q) hT hδ hδ1
  have hM := MB_le (q := q) hT hδ hδ1
  have hB := B1_le (q := q) hT hδ hδ1 hC
  have hA := A1_le (K := K) (q := q) hT hδ hδ1 hC
  have hct := ctail_nonneg K
  have hC0 := CGK_pos 0
  have hM0 : 0 ≤ MB (68 * Wf δ q T ^ 5) q T δ := by
    unfold MB U0
    have := one_le_Qq (q := q) hT
    positivity
  have hB0 : 0 ≤ LinnikCGLHBIter.B1 C (68 * Wf δ q T ^ 5) q T := by
    unfold LinnikCGLHBIter.B1
    positivity
  have hA0 : 0 ≤ A1 C K q := by
    unfold A1
    positivity
  have h1 : (MB (68 * Wf δ q T ^ 5) q T δ * LinnikCGLHBIter.B1 C (68 * Wf δ q T ^ 5) q T) ^ 2 ≤
      (5826240 * (136 * C * (Real.pi * CGK 0) ^ 2)) ^ 2 * Wf δ q T ^ 50 := by
    calc (MB (68 * Wf δ q T ^ 5) q T δ * LinnikCGLHBIter.B1 C (68 * Wf δ q T ^ 5) q T) ^ 2
        ≤ (5826240 * Wf δ q T ^ 13 * (136 * C * (Real.pi * CGK 0) ^ 2 * Wf δ q T ^ 12)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hM0 hB0) (mul_le_mul hM hB hB0 (by positivity)) 2
      _ = (5826240 * (136 * C * (Real.pi * CGK 0) ^ 2)) ^ 2 * Wf δ q T ^ 50 := by ring
  have h2 : 2 * (MB (68 * Wf δ q T ^ 5) q T δ * A1 C K q) ≤
      2 * (5826240 * (C * (1 + 2 * ctail K ^ 2))) * Wf δ q T ^ 50 := by
    have h3 : MB (68 * Wf δ q T ^ 5) q T δ * A1 C K q ≤
        5826240 * Wf δ q T ^ 13 * (C * (1 + 2 * ctail K ^ 2) * Wf δ q T ^ 6) :=
      mul_le_mul hM hA hA0 (by positivity)
    have hW19 : Wf δ q T ^ 19 ≤ Wf δ q T ^ 50 := pow_le_pow_right₀ hW (by norm_num)
    calc 2 * (MB (68 * Wf δ q T ^ 5) q T δ * A1 C K q)
        ≤ 2 * (5826240 * Wf δ q T ^ 13 * (C * (1 + 2 * ctail K ^ 2) * Wf δ q T ^ 6)) := by linarith
      _ = 2 * (5826240 * (C * (1 + 2 * ctail K ^ 2))) * Wf δ q T ^ 19 := by ring
      _ ≤ 2 * (5826240 * (C * (1 + 2 * ctail K ^ 2))) * Wf δ q T ^ 50 :=
          mul_le_mul_of_nonneg_left hW19 (by positivity)
  linarith

end Factors

/-! ### The bound with `(qTN)^ε`, and Theorem 10.1 -/

/-- `3^{1/2} ≤ 2`. -/
lemma sqrt_three_le_two : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  calc (3 : ℝ) ^ (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 2 := h4

/-- For `q ≥ 1`, `T ≥ 1`, `N ≥ 0` and `R ≥ 0`, `B(N) ≤ 2(RN + R² + R^{5/4}(qT)^{1/2})`. -/
lemma Bd_le_qT {q : ℕ} [NeZero q] {T N R : ℝ} (hT : 1 ≤ T) (hN : 0 ≤ N) (hR : 0 ≤ R) :
    Bd R (Qq q T) N ≤ 2 * (R * N + R ^ 2 + R ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ : 0 ≤ Qq q T := zero_le_one.trans (one_le_Qq (q := q) (by linarith))
  have hQ3 : Qq q T ≤ 3 * ((q : ℝ) * T) := by
    unfold Qq
    nlinarith
  have hy : Qq q T ^ (1 / 2 : ℝ) ≤ 2 * ((q : ℝ) * T) ^ (1 / 2 : ℝ) := by
    calc Qq q T ^ (1 / 2 : ℝ) ≤ (3 * ((q : ℝ) * T)) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hQ hQ3 (by norm_num)
      _ = (3 : ℝ) ^ (1 / 2 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * ((q : ℝ) * T) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right sqrt_three_le_two (by positivity)
  have h1 : R ^ (5 / 4 : ℝ) * Qq q T ^ (1 / 2 : ℝ) ≤ R ^ (5 / 4 : ℝ) * (2 * ((q : ℝ) * T) ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hy (by positivity)
  have h2 : 0 ≤ R ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) := by positivity
  unfold Bd
  nlinarith [mul_nonneg hR hN, sq_nonneg R]

/-- **The double sums with characters**: for `ε > 0` there is `C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`, `N ≥ 1`,
points with `|t_r| ≤ T` and the points with the same character `1`-separated,
`σ(N) ≤ C(qTN)^ε(RN + R² + R^{5/4}(qT)^{1/2})`. -/
theorem sig_le_eps {ε : ℝ} (hε : 0 < ε) : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (P : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T N : ℝ}, 1 ≤ T → 1 ≤ N → (∀ i ∈ P, |t i| ≤ T) →
    (∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) →
    sig P χ t N ≤ C' * ((q : ℝ) * T * N) ^ ε *
      ((P.card : ℝ) * N + (P.card : ℝ) ^ 2 + (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ)) := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set δ := ε' / 50 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  obtain ⟨C, hC, hbound⟩ := sig_bound hδ
  set K := ⌈1 / δ⌉₊ with hK
  set κ := (5826240 * (136 * C * (Real.pi * CGK 0) ^ 2)) ^ 2 + 2 * (5826240 * (C * (1 + 2 * ctail K ^ 2)))
    with hκ
  have hct := ctail_nonneg K
  have hC0 := CGK_pos 0
  have hκ0 : 0 ≤ κ := by positivity
  have hCd := one_le_Cdiv hδ hδ1
  refine ⟨κ * (3 * Cdiv δ / δ) ^ 50 * 12 * 2, by positivity, ?_⟩
  intro q _ ι P χ t T N hT hN ht hsep
  have hT0 : 0 ≤ T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hR0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hD : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Lm q T δ → (m.divisors.card : ℝ) ≤ 68 * Wf δ q T ^ 5 :=
    fun m _ hm => dm_le_W hT0 hδ hδ1 hm
  have h1 := hbound q P χ t hT ht hsep (by have := one_le_W (q := q) hT0 hδ hδ1; positivity) hD N
    (by linarith)
  have h2 := factor_le (K := K) (q := q) hT0 hδ hδ1 hC
  have hBd0 : 0 ≤ Bd P.card (Qq q T) N := by
    unfold Bd
    have := one_le_Qq (q := q) hT0
    positivity
  have hBd := Bd_le_qT (q := q) hT (by linarith) hR0 (N := N)
  -- `W⁵⁰ ≤ 12(3C_δ/δ)⁵⁰(qTN)^ε`
  have h4Q := one_le_four_Q (q := q) hT0
  have hW50 : Wf δ q T ^ 50 = (3 * Cdiv δ / δ) ^ 50 * (4 * Qq q T) ^ ε' := by
    unfold Wf
    rw [show 3 * Cdiv δ * (4 * Qq q T) ^ δ / δ = 3 * Cdiv δ / δ * (4 * Qq q T) ^ δ by ring, mul_pow,
      ← Real.rpow_natCast ((4 * Qq q T) ^ δ) 50, ← Real.rpow_mul (by linarith)]
    congr 2
    rw [hδdef]
    push_cast
    ring
  have hqTN : 1 ≤ (q : ℝ) * T * N := by
    have h1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT
    exact one_le_mul_of_one_le_of_one_le h1 hN
  have h4 : 4 * Qq q T ≤ 12 * ((q : ℝ) * T * N) := by
    have h5 : (q : ℝ) * T ≤ (q : ℝ) * T * N := le_mul_of_one_le_right (by positivity) hN
    unfold Qq
    nlinarith
  have hQe : (4 * Qq q T) ^ ε' ≤ 12 * ((q : ℝ) * T * N) ^ ε := by
    calc (4 * Qq q T) ^ ε' ≤ (12 * ((q : ℝ) * T * N)) ^ ε' := Real.rpow_le_rpow (by linarith) h4 hε'0.le
      _ = (12 : ℝ) ^ ε' * ((q : ℝ) * T * N) ^ ε' := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 12 * ((q : ℝ) * T * N) ^ ε := by
          have h6 : (12 : ℝ) ^ ε' ≤ 12 := by
            calc (12 : ℝ) ^ ε' ≤ (12 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε'1
              _ = 12 := Real.rpow_one _
          have h7 : ((q : ℝ) * T * N) ^ ε' ≤ ((q : ℝ) * T * N) ^ ε :=
            Real.rpow_le_rpow_of_exponent_le hqTN hε'ε
          exact mul_le_mul h6 h7 (by positivity) (by norm_num)
  have hW : Wf δ q T ^ 50 ≤ (3 * Cdiv δ / δ) ^ 50 * (12 * ((q : ℝ) * T * N) ^ ε) := by
    rw [hW50]
    exact mul_le_mul_of_nonneg_left hQe (by positivity)
  have hX0 : 0 ≤ κ * ((3 * Cdiv δ / δ) ^ 50 * (12 * ((q : ℝ) * T * N) ^ ε)) := by
    have h1 : 0 ≤ (3 * Cdiv δ / δ) ^ 50 := pow_nonneg (by positivity) 50
    have h2 : 0 ≤ ((q : ℝ) * T * N) ^ ε := Real.rpow_nonneg (by linarith) ε
    exact mul_nonneg hκ0 (mul_nonneg h1 (mul_nonneg (by norm_num) h2))
  calc sig P χ t N
      ≤ ((MB (68 * Wf δ q T ^ 5) q T δ * LinnikCGLHBIter.B1 C (68 * Wf δ q T ^ 5) q T) ^ 2 +
          2 * (MB (68 * Wf δ q T ^ 5) q T δ * A1 C ⌈1 / δ⌉₊ q)) * Bd P.card (Qq q T) N := h1
    _ ≤ (κ * Wf δ q T ^ 50) * Bd P.card (Qq q T) N := mul_le_mul_of_nonneg_right h2 hBd0
    _ ≤ (κ * ((3 * Cdiv δ / δ) ^ 50 * (12 * ((q : ℝ) * T * N) ^ ε))) *
          (2 * ((P.card : ℝ) * N + (P.card : ℝ) ^ 2 + (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hW hκ0) hBd hBd0 hX0
    _ = κ * (3 * Cdiv δ / δ) ^ 50 * 12 * 2 * ((q : ℝ) * T * N) ^ ε *
          ((P.card : ℝ) * N + (P.card : ℝ) ^ 2 + (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ)) := by
        ring

/-- **Heath-Brown's Theorem 10.1 with characters** (round 670's `CGLT101`), with `Q₀ = 0`: positivity with
`|c_n| ≤ B ≤ B(2M)^{1/2}n^{−1/2}` on `(M, 2M]` bounds the double sum by `2MB²σ(M)`. -/
theorem cglt101 : CGLT101 := by
  intro ε hε
  obtain ⟨C', hC', hfin⟩ := sig_le_eps hε
  refine ⟨2 * C', 0, ?_⟩
  intro q _ ι P χ t T M B c _ hT hM _ ht hsep hc
  have hM0 : 0 ≤ M := by linarith
  have hn₀ : ⌊M⌋₊ + 1 ∈ dyad M := by
    rw [mem_dyad hM0]
    refine ⟨by push_cast; exact Nat.lt_floor_add_one M, ?_⟩
    have := Nat.floor_le hM0
    push_cast
    linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hc _ hn₀)
  -- the left side is round 694's double sum with the weights `c`
  have e : ∑ i ∈ P, ∑ j ∈ P,
      ‖∑ n ∈ dyad M, c n * χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I)‖ ^ 2 =
        dsum P (famA χ t) (dyad M) c := by
    unfold dsum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := by
      have h := ((mem_dyad hM0).1 hn).1
      exact_mod_cast lt_of_le_of_lt hM0 h
    have h := famA_mul_conj χ t i j hn0
    calc c n * χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I)
        = c n * (χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I)) := by ring
      _ = c n * (famA χ t i n * conj (famA χ t j n)) := by rw [h]
      _ = c n * famA χ t i n * conj (famA χ t j n) := by ring
  -- positivity
  have hb : ∀ n ∈ dyad M, ‖c n‖ ≤ B * (2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := fun n hn => by
    obtain ⟨h1, h2⟩ := (mem_dyad hM0).1 hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt hM0 h1
    have h3 : (2 * M) ^ (-(1 / 2 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hn0 h2 (by norm_num)
    have h4 : (2 * M) ^ (1 / 2 : ℝ) * (2 * M) ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      simp
    have h5 : 1 ≤ (2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
      calc (1 : ℝ) = (2 * M) ^ (1 / 2 : ℝ) * (2 * M) ^ (-(1 / 2 : ℝ)) := h4.symm
        _ ≤ (2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc ‖c n‖ ≤ B := hc n hn
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * ((2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h5 hB0
      _ = B * (2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
  have hle := dsum_le P (famA χ t) (le_refl (dyad M)) hb (fun n _ => by positivity)
  -- the right side is `2MB²σ(M)`
  have hr2 : ((2 * M) ^ (1 / 2 : ℝ)) ^ 2 = 2 * M := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have e2 : dsum P (famA χ t) (dyad M)
      (fun n => ((B * (2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = 2 * M * B ^ 2 * sig P χ t M := by
    have e3 : (fun n : ℕ => ((B * (2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
        fun n => ((B * (2 * M) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * wh n := by
      funext n
      unfold wh
      rw [← Complex.ofReal_mul]
    rw [e3, dsum_const_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, hr2]
    unfold sig
    ring
  have hσ := hfin q P χ t hT hM ht hsep
  rw [e]
  calc dsum P (famA χ t) (dyad M) c
      ≤ dsum P (famA χ t) (dyad M) (fun n => ((B * (2 * M) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := hle
    _ = 2 * M * B ^ 2 * sig P χ t M := e2
    _ ≤ 2 * M * B ^ 2 * (C' * ((q : ℝ) * T * M) ^ ε *
          ((P.card : ℝ) * M + (P.card : ℝ) ^ 2 + (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hσ (by positivity)
    _ = 2 * C' * ((q : ℝ) * T * M) ^ ε * ((P.card : ℝ) * M ^ 2 + (P.card : ℝ) ^ 2 * M +
          (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) * B ^ 2 := by ring

/-! ### The density count and Linnik's theorem -/

/-- **Their Proposition 11.1, at one point per character, with no hypothesis**: round 693's `cgls3_t101` at
`cglt101`. -/
theorem cgls3 : LinnikCGLS23.CGLS3 := LinnikCGLP81.cgls3_t101 cglt101

/-- **Their Proposition 3.1, at one point per character, with no hypothesis**: round 693's `prop31_t101` at
`cglt101`. -/
theorem prop31 : LinnikCGLLV.CGLProp31 := LinnikCGLP81.prop31_t101 cglt101

/-- **The density count with no hypothesis**: there is `C ≥ 0` such that, for `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and
`T ≥ 2`, at most `C(qT)^{(7/3+1/2000)(1−σ)}(log qT)^{10}` characters mod `q` have an `L`-function with a zero in
`Re s ≥ σ`, `|Im s| ≤ T` (rounds 636–637's `charDensity_cgl` at `prop31`). -/
theorem char_density : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 7 ≤ σ → σ ≤ 16 / 21 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ ((7 / 3 + 1 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  LinnikCGLStep.charDensity_cgl prop31

/-- **Linnik's theorem with exponent `9/4`**: there is `K` such that for every `q ≥ 1` and every `a` prime to `q`
there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{9/4}` (round 693's `linnik_225c_t101` at `cglt101`). -/
theorem linnik_225 : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLP81.linnik_225c_t101 cglt101

/-- **Linnik's theorem with exponent `226/100`**: there is `K` such that for every `q ≥ 1` and every `a` prime to `q`
there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{226/100}` (round 693's `linnik_226c_t101` at `cglt101`). -/
theorem linnik_226 : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLP81.linnik_226c_t101 cglt101

end LinnikCGLHB101

#print axioms LinnikCGLHB101.sig_le_eps
#print axioms LinnikCGLHB101.cglt101
#print axioms LinnikCGLHB101.cgls3
#print axioms LinnikCGLHB101.prop31
#print axioms LinnikCGLHB101.char_density
#print axioms LinnikCGLHB101.linnik_225
#print axioms LinnikCGLHB101.linnik_226
