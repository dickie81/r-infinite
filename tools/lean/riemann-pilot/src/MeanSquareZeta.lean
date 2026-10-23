import Mathlib
import DirMean

/-! # The mean square of ζ on Re s ≥ 2/3 (round 401)

The Euler–Maclaurin formula approximates `ζ(σ+it)` by `Σ_{n≤N} n^{−σ−it}` with error at most
`N^{1−σ}/|t| + N^{−σ}/2 + (σ + |t|)N^{−σ}/σ` for `σ > 0` and `|t| ≥ 2`. It follows from PNT+'s Euler–Maclaurin formula
(`ZetaBounds`); here it is displayed as `EMApprox`, and `external/zeta23/ShellSixth.lean` proves it from zeta23's
copy. With `N = 2^J ≥ M^{3/2}` terms the error is bounded on `2 ≤ |t| ≤ M` for `σ ≥ 2/3`, and the dyadic mean value
theorem (`DirMean.mean_value`) bounds the partial sum.

* **`mean_square_partial`**: `∫_a^b |Σ_{n≤2^J} n^{−σ−it}|² dt ≤ (J+1)²(b − a + 8(J+1)·2^{2J/3})` for `σ ≥ 2/3`.
* **`mean_square_zeta_le`**: given `EMApprox`, for `σ ≥ 2/3`, `[a, b]` with `2 ≤ |t| ≤ M` on it and `Q = 2^{2J/3} ≥ M`,
  `∫_a^b |ζ(σ+it)|² dt ≤ 2(J+1)²(b − a + 8(J+1)Q) + 2Q + 36(b − a)`. With `Q ≤ 2M` this is `≪ M (log M)³`.

The exponent `2/3` is where this method's two requirements meet: the remainder needs `N ≥ M^{1/σ}`, and the mean value
theorem's off-diagonal term `N^{2−2σ}` must stay below `M`; together they force `σ ≥ 2/3`.
-/

open Real Complex MeasureTheory Set Finset

noncomputable section

namespace MeanSquareZeta

open DirMean

/-- **The Euler–Maclaurin approximation of `ζ` by its partial sums**, displayed: for `σ > 0`, `|t| ≥ 2` and
`N ≥ 1`, `|ζ(σ+it) − Σ_{n≤N} n^{−σ−it}| ≤ N^{1−σ}/|t| + N^{−σ}/2 + (σ + |t|)N^{−σ}/σ`. -/
def EMApprox : Prop :=
  ∀ {σ t : ℝ}, 0 < σ → 2 ≤ |t| → ∀ {N : ℕ}, 1 ≤ N →
    ‖riemannZeta (σ + t * I) - ∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-((σ : ℂ) + t * I))‖
      ≤ (N : ℝ) ^ (1 - σ) / |t| + (N : ℝ) ^ (-σ) / 2 + (σ + |t|) * (N : ℝ) ^ (-σ) / σ

/-- `n^{−(σ+it)} = n^{−σ} e^{−it log n}`. -/
lemma natCast_cpow_eq {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + t * I))
      = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(I * ((t * Real.log n : ℝ) : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn0, Real.rpow_def_of_pos hnr]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnr.le]
  rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `Σ_{0<n≤2^J} f(n) = f(1) + Σ_{j<J} Σ_{2^j<n≤2^{j+1}} f(n)`. -/
lemma sum_Ioc_two_pow {M : Type*} [AddCommMonoid M] (f : ℕ → M) (J : ℕ) :
    ∑ n ∈ Ioc 0 (2 ^ J), f n = f 1 + ∑ j ∈ range J, ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n := by
  induction J with
  | zero =>
    rw [pow_zero, Finset.range_zero, Finset.sum_empty, add_zero,
      show (1 : ℕ) = 0 + 1 from rfl, Nat.Ioc_succ_singleton, Finset.sum_singleton]
  | succ J ih =>
    rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le (2 ^ J))
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)), ih, Finset.sum_range_succ, add_assoc]

/-- The dyadic block bound: for `P = 2^j` with `j ≤ J` and `σ ≥ 2/3`,
`(b − a + 8P(1 + log P))·P·(P^{−σ})² ≤ (b − a) + 8(J + 1)(2^J)^{2/3}`. -/
lemma block_bound {σ : ℝ} (hσ : 2 / 3 ≤ σ) {j J : ℕ} (hj : j ≤ J) {a b : ℝ} (hab : a ≤ b) :
    (b - a + 8 * (2 ^ j : ℕ) * (1 + Real.log (2 ^ j : ℕ))) * ((2 ^ j : ℕ) * (((2 ^ j : ℕ) : ℝ) ^ (-σ)) ^ 2)
      ≤ (b - a) + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) := by
  set P : ℝ := ((2 ^ j : ℕ) : ℝ) with hP
  have hP1 : 1 ≤ P := by rw [hP]; exact_mod_cast Nat.one_le_two_pow
  have hP0 : 0 < P := by linarith
  have hsq : P * (P ^ (-σ)) ^ 2 = P ^ (1 - 2 * σ) := by
    rw [← Real.rpow_natCast (P ^ (-σ)) 2, ← Real.rpow_mul hP0.le]
    rw [show (1 : ℝ) - 2 * σ = 1 + (-σ * ((2 : ℕ) : ℝ)) by push_cast; ring,
      Real.rpow_add hP0, Real.rpow_one]
  have hsq2 : P * P ^ (1 - 2 * σ) = P ^ (2 - 2 * σ) := by
    rw [show (2 : ℝ) - 2 * σ = 1 + (1 - 2 * σ) by ring, Real.rpow_add hP0, Real.rpow_one]
  rw [hsq]
  have h1 : P ^ (1 - 2 * σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
  have h2 : P ^ (2 - 2 * σ) ≤ P ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hPJ : P ≤ (2 : ℝ) ^ J := by
    rw [hP]; push_cast; exact pow_le_pow_right₀ (by norm_num) hj
  have h3 : P ^ ((2 : ℝ) / 3) ≤ ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hP0.le hPJ (by norm_num)
  have hlog : Real.log P ≤ J := by
    rw [hP]; push_cast
    rw [Real.log_pow]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    calc (j : ℝ) * Real.log 2 ≤ j * 1 := by gcongr
      _ = j := mul_one _
      _ ≤ J := by exact_mod_cast hj
  have hlog0 : 0 ≤ Real.log P := Real.log_nonneg hP1
  have hQ0 : 0 ≤ ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) := by positivity
  have hba : 0 ≤ b - a := by linarith
  have hpos1 : 0 ≤ P ^ (1 - 2 * σ) := by positivity
  calc (b - a + 8 * P * (1 + Real.log P)) * P ^ (1 - 2 * σ)
      = (b - a) * P ^ (1 - 2 * σ) + 8 * (1 + Real.log P) * (P * P ^ (1 - 2 * σ)) := by ring
    _ = (b - a) * P ^ (1 - 2 * σ) + 8 * (1 + Real.log P) * P ^ (2 - 2 * σ) := by rw [hsq2]
    _ ≤ (b - a) * 1 + 8 * (1 + J) * ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) := by
        have e1 : (b - a) * P ^ (1 - 2 * σ) ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left h1 hba
        have e2 : 8 * (1 + Real.log P) * P ^ (2 - 2 * σ) ≤ 8 * (1 + J) * ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) :=
          mul_le_mul (by linarith) (h2.trans h3) (by positivity) (by positivity)
        linarith
    _ = (b - a) + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) := by ring

/-- **The mean square of `Σ_{n≤2^J} n^{−σ−it}`** for `σ ≥ 2/3`, from the dyadic mean value theorem
(`DirMean.mean_value`) and Cauchy–Schwarz over the `J + 1` blocks. -/
theorem mean_square_partial {σ : ℝ} (hσ : 2 / 3 ≤ σ) (J : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖∑ n ∈ Ioc (0 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2
      ≤ (J + 1) ^ 2 * (b - a + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3)) := by
  set c : ℕ → ℂ := fun n => (((n : ℝ) ^ (-σ) : ℝ) : ℂ) with hc
  set Bk : ℕ → ℝ → ℂ := fun j t => dp (Finset.Ioc (2 ^ j) (2 ^ (j + 1))) c t with hBk
  set Q : ℝ := ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) with hQ
  have hD : ∀ t : ℝ, ∑ n ∈ Ioc (0 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + t * I))
      = 1 + ∑ j ∈ range J, Bk j t := by
    intro t
    rw [sum_Ioc_two_pow]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hBk, dp]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := by
        have h1 := (Finset.mem_Ioc.1 hn).1
        have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      rw [natCast_cpow_eq hn1]
  have hcs : ∀ t : ℝ, ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2
      ≤ (J + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2) := by
    intro t
    have hle : ‖1 + ∑ j ∈ range J, Bk j t‖ ≤ 1 + ∑ j ∈ range J, ‖Bk j t‖ :=
      (norm_add_le _ _).trans (by rw [norm_one]; gcongr; exact norm_sum_le _ _)
    have hcs0 := sq_sum_le_card_mul_sum_sq (s := range (J + 1))
      (f := fun i => if i = 0 then (1 : ℝ) else ‖Bk (i - 1) t‖)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hcs0
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, card_range, one_pow] at hcs0
    push_cast at hcs0
    calc ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2 ≤ (1 + ∑ j ∈ range J, ‖Bk j t‖) ^ 2 := by
          gcongr
      _ ≤ (J + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2) := by
          rw [add_comm (1 : ℝ) (∑ j ∈ range J, ‖Bk j t‖),
            add_comm (1 : ℝ) (∑ j ∈ range J, ‖Bk j t‖ ^ 2)]
          exact hcs0
  have hcontB : ∀ j, Continuous (Bk j) := fun j => continuous_dp _ _
  have hfun : (fun t : ℝ => ‖∑ n ∈ Ioc (0 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2)
      = fun t => ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2 := funext fun t => by rw [hD]
  rw [hfun]
  have hint1 : IntervalIntegrable (fun t => ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2) volume a b :=
    (by fun_prop : Continuous fun t => ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2).intervalIntegrable _ _
  have hintB : ∀ j ∈ range J, IntervalIntegrable (fun t => ‖Bk j t‖ ^ 2) volume a b :=
    fun j _ => ((hcontB j).norm.pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun t => ((J : ℝ) + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2)) volume a b :=
    (continuous_const.mul (continuous_const.add (continuous_finsetSum _
      fun j _ => (hcontB j).norm.pow 2))).intervalIntegrable _ _
  calc ∫ t in a..b, ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2
      ≤ ∫ t in a..b, ((J : ℝ) + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2) :=
        intervalIntegral.integral_mono_on hab hint1 hint2 fun t _ => hcs t
    _ = ((J : ℝ) + 1) * ((b - a) + ∑ j ∈ range J, ∫ t in a..b, ‖Bk j t‖ ^ 2) := by
        have hsum_int : IntervalIntegrable (fun t => ∑ j ∈ range J, ‖Bk j t‖ ^ 2) volume a b :=
          (continuous_finsetSum _ fun j _ => (hcontB j).norm.pow 2).intervalIntegrable _ _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          intervalIntegrable_const hsum_int,
          intervalIntegral.integral_finsetSum hintB, intervalIntegral.integral_const, smul_eq_mul,
          mul_one]
    _ ≤ ((J : ℝ) + 1) * ((b - a) + ∑ j ∈ range J, ((b - a) + 8 * (J + 1) * Q)) := by
        gcongr with j hj
        have hjJ : j ≤ J := (Finset.mem_range.1 hj).le
        have hP : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        have hS : Finset.Ioc (2 ^ j) (2 ^ (j + 1)) ⊆ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
          rw [pow_succ, mul_comm]
        have hmv := mean_value hP hS c hab
        refine hmv.trans ?_
        refine le_trans ?_ (block_bound hσ hjJ hab)
        have hsum : ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ‖c n‖ ^ 2
            ≤ ((2 ^ j : ℕ) : ℝ) * ((((2 ^ j : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by
          have hcard : (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).card = 2 ^ j := by
            rw [Nat.card_Ioc, pow_succ]; omega
          calc ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ‖c n‖ ^ 2
              ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ((((2 ^ j : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by
                refine Finset.sum_le_sum fun n hn => ?_
                have hn' := (Finset.mem_Ioc.1 hn).1
                have hPr : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
                have hnr : ((2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.le
                have hle : (n : ℝ) ^ (-σ) ≤ ((2 ^ j : ℕ) : ℝ) ^ (-σ) :=
                  Real.rpow_le_rpow_of_nonpos hPr hnr (by linarith)
                have hn0 : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
                have hnorm : ‖c n‖ = (n : ℝ) ^ (-σ) := by
                  simp only [hc, Complex.norm_real, Real.norm_eq_abs]
                  exact abs_of_nonneg hn0
                rw [hnorm]
                exact pow_le_pow_left₀ hn0 hle 2
            _ = ((2 ^ j : ℕ) : ℝ) * ((((2 ^ j : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by
                rw [Finset.sum_const, hcard, nsmul_eq_mul]
        have hL0 : 0 ≤ b - a + 8 * (2 ^ j : ℕ) * (1 + Real.log (2 ^ j : ℕ)) := by
          have : 0 ≤ Real.log ((2 ^ j : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hP)
          have : 0 ≤ b - a := by linarith
          positivity
        push_cast at hsum hL0 ⊢
        exact mul_le_mul_of_nonneg_left hsum hL0
    _ = ((J : ℝ) + 1) * ((b - a) + J * ((b - a) + 8 * (J + 1) * Q)) := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
    _ ≤ (J + 1) ^ 2 * (b - a + 8 * (J + 1) * Q) := by
        have hQ0 : 0 ≤ Q := by positivity
        have hba : 0 ≤ b - a := by linarith
        have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
        nlinarith [mul_nonneg hJ hQ0, mul_nonneg (mul_nonneg hJ hJ) hQ0]

/-- `∫_a^b t^{−2} dt ≤ ½` on an interval with `|t| ≥ 2`. -/
lemma integral_inv_sq_le {a b : ℝ} (hab : a ≤ b) (hside : 2 ≤ a ∨ b ≤ -2) :
    ∫ t in a..b, (t ^ 2)⁻¹ ≤ 1 / 2 := by
  have hne : ∀ t ∈ uIcc a b, t ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    rcases hside with h | h
    · linarith [ht.1]
    · linarith [ht.2]
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((t ^ 2)⁻¹) t := by
    intro t ht
    have h := (hasDerivAt_inv (hne t ht)).neg
    rw [neg_neg] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (uIcc a b) :=
    (continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne t ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  rcases hside with h | h
  · have hb : 2 ≤ b := h.trans hab
    have h1 : a⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : 0 ≤ b⁻¹ := inv_nonneg.2 (by linarith)
    linarith
  · have ha : a ≤ -2 := hab.trans h
    have h1 : a⁻¹ < 0 := inv_lt_zero.2 (by linarith)
    have h2 : -b⁻¹ ≤ 1 / 2 := by
      have : b⁻¹ ≥ -(1 / 2) := by
        rw [ge_iff_le, le_inv_of_neg (by norm_num) (by linarith)]
        linarith
      linarith
    linarith

/-- **The mean square of `ζ` on a vertical segment**, from the Euler–Maclaurin approximation with
`N = 2^J ≥ M^{3/2}` terms: for `σ ≥ 2/3` and `[a, b]` with `2 ≤ |t| ≤ M`,
`∫_a^b |ζ(σ+it)|² ≤ 2(J+1)²(b − a + 8(J+1)Q) + 2Q + 36(b − a)`, where `Q = (2^J)^{2/3} ≥ M`. -/
theorem mean_square_zeta_le (hEM : EMApprox) {σ M a b : ℝ} {J : ℕ} (hσ : 2 / 3 ≤ σ)
    (hM : 2 ≤ M) (hQ : M ≤ ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3)) (hab : a ≤ b) (hside : 2 ≤ a ∨ b ≤ -2)
    (hbd : ∀ t ∈ Icc a b, |t| ≤ M) :
    ∫ t in a..b, ‖riemannZeta (σ + t * I)‖ ^ 2
      ≤ 2 * ((J + 1) ^ 2 * (b - a + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3)))
        + 2 * ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) + 36 * (b - a) := by
  set Q : ℝ := ((2 : ℝ) ^ J) ^ ((2 : ℝ) / 3) with hQdef
  set N : ℕ := 2 ^ J with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNr : (N : ℝ) = (2 : ℝ) ^ J := by rw [hN]; push_cast; ring
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hσ0 : 0 < σ := by linarith
  have habs : ∀ t ∈ Icc a b, 2 ≤ |t| := by
    intro t ht
    rcases hside with h | h
    · rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    · rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]
  set D : ℝ → ℂ := fun t => ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((σ : ℂ) + t * I)) with hDdef
  -- pointwise bound on the Euler–Maclaurin error
  have hN13 : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = Q := by
    rw [hQdef, ← hNr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hNσ : (N : ℝ) ^ (-σ) ≤ 1 / M := by
    have h1 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-((2 : ℝ) / 3)) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
    have h2 : (N : ℝ) ^ (-((2 : ℝ) / 3)) = Q⁻¹ := by
      rw [Real.rpow_neg (by positivity), hQdef, ← hNr]
    rw [h2] at h1
    refine h1.trans ?_
    rw [one_div]
    exact inv_anti₀ (by linarith) hQ
  have hE : ∀ t ∈ Icc a b, ‖riemannZeta (σ + t * I) - D t‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / |t| + 3 := by
    intro t ht
    have h2t := habs t ht
    have hMt := hbd t ht
    have hem := hEM hσ0 h2t hN1
    have ht0 : 0 < |t| := by linarith
    have hM0 : 0 < M := by linarith
    have hA : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
    have hB : (N : ℝ) ^ (-σ) / 2 ≤ 1 := by
      have : 1 / M ≤ 1 / 2 := by gcongr
      linarith
    have hC : (σ + |t|) * (N : ℝ) ^ (-σ) / σ ≤ 2 := by
      have hNσ0 : 0 ≤ (N : ℝ) ^ (-σ) := by positivity
      calc (σ + |t|) * (N : ℝ) ^ (-σ) / σ ≤ (σ + M) * (1 / M) / σ := by gcongr
        _ = 1 / M + 1 / σ := by field_simp
        _ ≤ 1 / 2 + 3 / 2 := by
            have e1 : 1 / M ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
            have e2 : 1 / σ ≤ 3 / 2 := by rw [div_le_div_iff₀ hσ0 (by norm_num)]; linarith
            linarith
        _ = 2 := by norm_num
    calc ‖riemannZeta (σ + t * I) - D t‖ ≤ _ := hem
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / |t| + 1 + 2 := by
          gcongr
      _ = _ := by ring
  have hne : ∀ t ∈ Icc a b, (σ : ℂ) + t * I ≠ 1 := by
    intro t ht h
    have := congrArg Complex.im h
    simp at this
    have := habs t ht
    rw [‹t = 0›, abs_zero] at this
    norm_num at this
  have hzcont : ContinuousOn (fun t : ℝ => ‖riemannZeta (σ + t * I)‖ ^ 2) (Icc a b) := by
    intro t ht
    have hin : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
    have h1 : ContinuousAt (fun t : ℝ => riemannZeta (σ + t * I)) t :=
      ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I)
        (differentiableAt_riemannZeta (hne t ht)).continuousAt hin.continuousAt
    exact (h1.norm.pow 2).continuousWithinAt
  have hDc : Continuous D := by
    simp only [hDdef]
    refine continuous_finsetSum _ fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Ioc.1 hn).1
      exact_mod_cast (show n ≠ 0 by omega)
    exact (by fun_prop : Continuous fun t : ℝ => -((σ : ℂ) + t * I)).const_cpow (Or.inl hn0)
  have hDcont : Continuous fun t => ‖D t‖ ^ 2 := hDc.norm.pow 2
  have hne0 : ∀ t ∈ Icc a b, t ≠ 0 := by
    intro t ht h; have := habs t ht; rw [h, abs_zero] at this; norm_num at this
  have hmajcont : ContinuousOn (fun t : ℝ => 2 * ‖D t‖ ^ 2 + (4 * Q * (t ^ 2)⁻¹ + 36)) (Icc a b) :=
    (continuous_const.mul hDcont).continuousOn.add
      ((continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne0 t ht))).add
        continuousOn_const)
  have hpt : ∀ t ∈ Icc a b,
      ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ 2 * ‖D t‖ ^ 2 + (4 * Q * (t ^ 2)⁻¹ + 36) := by
    intro t ht
    have h1 : ‖riemannZeta (σ + t * I)‖ ≤ ‖D t‖ + ‖riemannZeta (σ + t * I) - D t‖ := by
      have := norm_add_le (D t) (riemannZeta (σ + t * I) - D t)
      rwa [add_sub_cancel] at this
    have h2 := hE t ht
    have ht0 : 0 < |t| := by linarith [habs t ht]
    have hX : ((N : ℝ) ^ ((1 : ℝ) / 3) / |t|) ^ 2 = Q * (t ^ 2)⁻¹ := by
      rw [div_pow, hN13, sq_abs, div_eq_mul_inv]
    have hE0 : 0 ≤ ‖riemannZeta (σ + t * I) - D t‖ := norm_nonneg _
    have hY0 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 3) / |t| := by positivity
    calc ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ (‖D t‖ + ‖riemannZeta (σ + t * I) - D t‖) ^ 2 := by
          gcongr
      _ ≤ 2 * ‖D t‖ ^ 2 + 2 * ‖riemannZeta (σ + t * I) - D t‖ ^ 2 := by
          nlinarith [sq_nonneg (‖D t‖ - ‖riemannZeta (σ + t * I) - D t‖)]
      _ ≤ 2 * ‖D t‖ ^ 2 + 2 * ((N : ℝ) ^ ((1 : ℝ) / 3) / |t| + 3) ^ 2 := by gcongr
      _ ≤ 2 * ‖D t‖ ^ 2 + 2 * (2 * ((N : ℝ) ^ ((1 : ℝ) / 3) / |t|) ^ 2 + 18) := by
          nlinarith [sq_nonneg ((N : ℝ) ^ ((1 : ℝ) / 3) / |t| - 3)]
      _ = 2 * ‖D t‖ ^ 2 + (4 * Q * (t ^ 2)⁻¹ + 36) := by rw [hX]; ring
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint_maj : IntervalIntegrable (fun t : ℝ => 2 * ‖D t‖ ^ 2 + (4 * Q * (t ^ 2)⁻¹ + 36)) volume a b :=
    (hIcc ▸ hmajcont).intervalIntegrable
  have hint_z : IntervalIntegrable (fun t : ℝ => ‖riemannZeta (σ + t * I)‖ ^ 2) volume a b :=
    (hIcc ▸ hzcont).intervalIntegrable
  have hinvint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a b :=
    (hIcc ▸ ((continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne0 t ht))).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hab hint_z hint_maj hpt
  have hsplit : ∫ t in a..b, 2 * ‖D t‖ ^ 2 + (4 * Q * (t ^ 2)⁻¹ + 36)
      = 2 * (∫ t in a..b, ‖D t‖ ^ 2) + 4 * Q * (∫ t in a..b, (t ^ 2)⁻¹) + 36 * (b - a) := by
    have e1 : ∫ t in a..b, 2 * ‖D t‖ ^ 2 + (4 * Q * (t ^ 2)⁻¹ + 36)
        = (∫ t in a..b, 2 * ‖D t‖ ^ 2) + ∫ t in a..b, (4 * Q * (t ^ 2)⁻¹ + 36) :=
      intervalIntegral.integral_add ((hDcont.intervalIntegrable a b).const_mul 2)
        ((hinvint.const_mul (4 * Q)).add intervalIntegrable_const)
    have e2 : ∫ t in a..b, (4 * Q * (t ^ 2)⁻¹ + 36)
        = (∫ t in a..b, 4 * Q * (t ^ 2)⁻¹) + ∫ _ in a..b, (36 : ℝ) :=
      intervalIntegral.integral_add (hinvint.const_mul (4 * Q)) intervalIntegrable_const
    have e3 : ∫ t in a..b, 2 * ‖D t‖ ^ 2 = 2 * ∫ t in a..b, ‖D t‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    have e4 : ∫ t in a..b, 4 * Q * (t ^ 2)⁻¹ = 4 * Q * ∫ t in a..b, (t ^ 2)⁻¹ :=
      intervalIntegral.integral_const_mul _ _
    have e5 : ∫ _ in a..b, (36 : ℝ) = (b - a) * 36 := by simp
    rw [e1, e2, e3, e4, e5]
    ring
  have hDint : ∫ t in a..b, ‖D t‖ ^ 2
      ≤ (J + 1) ^ 2 * (b - a + 8 * (J + 1) * Q) := by
    have := mean_square_partial hσ J hab
    simpa [hDdef, hN] using this
  have hinv := integral_inv_sq_le hab hside
  have hQ0 : 0 ≤ Q := by positivity
  rw [hsplit] at hmono
  have h4 : 4 * Q * (∫ t in a..b, (t ^ 2)⁻¹) ≤ 4 * Q * (1 / 2) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  linarith [hmono, hDint, h4]

end MeanSquareZeta

#print axioms MeanSquareZeta.natCast_cpow_eq
#print axioms MeanSquareZeta.sum_Ioc_two_pow
#print axioms MeanSquareZeta.block_bound
#print axioms MeanSquareZeta.mean_square_partial
#print axioms MeanSquareZeta.integral_inv_sq_le
#print axioms MeanSquareZeta.mean_square_zeta_le
