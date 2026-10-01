import Mathlib
import DHNumerics
import DHLogBounds
import DHTrigBounds

/-! # the constants of the archimedean bound at `(a, ω) = (12/5, 169/2)` (round 261, certificate stage 3)

`log 5`, `log π`, `log √(9/16 + ω²/4) = ½ log(14285/8)`, `log(2aω) = log(2028/5)`, `e^{−3a} = e^{−36/5}`,
`‖g‖² = 12/5 + sin(2028/5)/169`. -/

open Real Finset

namespace PsiOmega.Num

/-- `log(1 + 1/a)` bounds for real `a > 0` (the same series). -/
theorem log_one_add_inv_bounds' {a : ℝ} (ha : 0 < a) (K : ℕ) :
    ∑ k ∈ range K, 2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1)
        ≤ Real.log (1 + a⁻¹) ∧
      Real.log (1 + a⁻¹)
        ≤ ∑ k ∈ range K, 2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1)
          + 2 * (1 / (2 * a + 1)) ^ (2 * K + 1) / (1 - (1 / (2 * a + 1)) ^ 2) := by
  have hs := Real.hasSum_log_one_add_inv ha
  set q : ℝ := 1 / (2 * a + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  have hterm : ∀ k : ℕ, 0 ≤ 2 * (1 / (2 * (k : ℝ) + 1)) * q ^ (2 * k + 1) := fun k => by positivity
  refine ⟨sum_le_hasSum (range K) (fun i _ => hterm i) hs, ?_⟩
  have hsum := hs.summable
  have key := hsum.sum_add_tsum_nat_add K
  rw [hs.tsum_eq] at key
  rw [← key]
  gcongr
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun i : ℕ => 2 * q ^ (2 * K + 1) * (q ^ 2) ^ i)
      (2 * q ^ (2 * K + 1) * (1 - q ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hq2).mul_left _
  have hshift : HasSum (fun i : ℕ => 2 * (1 / (2 * ((i + K : ℕ) : ℝ) + 1)) * q ^ (2 * (i + K) + 1))
      (∑' i : ℕ, 2 * (1 / (2 * ((i + K : ℕ) : ℝ) + 1)) * q ^ (2 * (i + K) + 1)) :=
    ((summable_nat_add_iff K).2 hsum).hasSum
  rw [div_eq_mul_inv]
  refine hasSum_le (fun i => ?_) hshift hg
  have h1 : 1 / (2 * ((i + K : ℕ) : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg (i + K) : (0 : ℝ) ≤ (i + K : ℕ))]
  have h2 : q ^ (2 * (i + K) + 1) = q ^ (2 * K + 1) * (q ^ 2) ^ i := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [h2]
  have hp : 0 ≤ q ^ (2 * K + 1) * (q ^ 2) ^ i := by positivity
  calc 2 * (1 / (2 * ((i + K : ℕ) : ℝ) + 1)) * (q ^ (2 * K + 1) * (q ^ 2) ^ i)
      ≤ 2 * 1 * (q ^ (2 * K + 1) * (q ^ 2) ^ i) := by gcongr
    _ = 2 * q ^ (2 * K + 1) * (q ^ 2) ^ i := by ring

/-! ## `log π` -/

theorem log_pi_bounds : (11447296 : ℝ) / 10 ^ 7 < Real.log π ∧ Real.log π < (11447301 : ℝ) / 10 ^ 7 := by
  have h3 := log_bound_3
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  -- log 3.141592 = log 3 + log(1 + 1/a₁), a₁ = 3/0.141592 = 375000/17699
  have e1 : Real.log (3.141592 : ℝ) = Real.log 3 + Real.log (1 + (375000 / 17699 : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log (3.141593 : ℝ) = Real.log 3 + Real.log (1 + (3000000 / 141593 : ℝ)⁻¹) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l1 : Real.log (3.141592 : ℝ) < Real.log π := Real.log_lt_log (by norm_num) hpi1
  have l2 : Real.log π < Real.log (3.141593 : ℝ) := Real.log_lt_log Real.pi_pos hpi2
  rw [e1] at l1; rw [e2] at l2
  have b1 := log_one_add_inv_bounds' (a := 375000 / 17699) (by norm_num) 3
  have b2 := log_one_add_inv_bounds' (a := 3000000 / 141593) (by norm_num) 3
  set y₁ := Real.log (1 + (375000 / 17699 : ℝ)⁻¹) with hy₁
  set y₂ := Real.log (1 + (3000000 / 141593 : ℝ)⁻¹) with hy₂
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at b1 b2
  norm_num at b1 b2
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, h3.1, h3.2]

/-! ## `log √(9/16 + ω²/4) = ½ log(14285/8)`, `14285 = 5 · 2857`, `2857 = 2856 (1 + 1/2856)`, `2856 = 8·3·7·17` -/

theorem log_2857_bounds : (79575273 : ℝ) / 10 ^ 7 < Real.log 2857 ∧ Real.log 2857 < (79575275 : ℝ) / 10 ^ 7 := by
  have h2 := log_bound_2; have h3 := log_bound_3; have h7 := log_bound_7; have h17 := log_bound_17
  have e : Real.log (2857 : ℝ) = 3 * Real.log 2 + Real.log 3 + Real.log 7 + Real.log 17
      + Real.log (1 + ((2856 : ℕ) : ℝ)⁻¹) := by
    have : (2857 : ℝ) = 2 ^ 3 * 3 * 7 * 17 * (1 + ((2856 : ℕ) : ℝ)⁻¹) := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [e]
  have b := log_one_add_inv_bounds (m := 2856) (by norm_num) 1
  set y := Real.log (1 + ((2856 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at b
  norm_num at b
  constructor <;> linarith [b.1, b.2, h2.1, h2.2, h3.1, h3.2, h7.1, h7.2, h17.1, h17.2]

/-- `log √(9/16 + ω²/4) = ½(log 5 + log 2857 − 3 log 2)`. -/
theorem log_sqrt_z_eq :
    Real.log (Real.sqrt (9 / 16 + (169 / 2 : ℝ) ^ 2 / 4))
      = (Real.log 5 + Real.log 2857 - 3 * Real.log 2) / 2 := by
  have : (9 / 16 + (169 / 2 : ℝ) ^ 2 / 4) = 5 * 2857 / 2 ^ 3 := by norm_num
  rw [this, Real.log_sqrt (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast; ring

theorem log_sqrt_z_bounds :
    (37437617 : ℝ) / 10 ^ 7 < Real.log (Real.sqrt (9 / 16 + (169 / 2 : ℝ) ^ 2 / 4)) ∧
      Real.log (Real.sqrt (9 / 16 + (169 / 2 : ℝ) ^ 2 / 4)) < (37437620 : ℝ) / 10 ^ 7 := by
  rw [log_sqrt_z_eq]
  have h2 := log_bound_2; have h5 := log_bound_5; have h := log_2857_bounds
  constructor <;> linarith [h2.1, h2.2, h5.1, h5.2, h.1, h.2]

/-! ## `log(2aω) = log(2028/5)`, `2028 = 4·3·13²` -/

theorem log_two_a_omega_bounds :
    (60053 : ℝ) / 10 ^ 4 < Real.log (2028 / 5 : ℝ) ∧ Real.log (2028 / 5 : ℝ) < (60054 : ℝ) / 10 ^ 4 := by
  have h2 := log_bound_2; have h3 := log_bound_3; have h5 := log_bound_5; have h13 := log_bound_13
  have e : Real.log (2028 / 5 : ℝ) = 2 * Real.log 2 + Real.log 3 + 2 * Real.log 13 - Real.log 5 := by
    have : (2028 / 5 : ℝ) = 2 ^ 2 * 3 * 13 ^ 2 / 5 := by norm_num
    rw [this, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [e]
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, h5.1, h5.2, h13.1, h13.2]

/-! ## `e^{−36/5}` and `1 − e^{−48/5}` -/

theorem exp_neg_one_pow_bounds (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (0.3678794412 : ℝ) ^ n := by
  rw [show (-(n : ℝ)) = (n : ℕ) • (-1 : ℝ) by simp, Real.exp_nsmul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_d9.le n

theorem exp_neg_three_a_le : Real.exp (-(3 * (12 / 5 : ℝ))) ≤ (0.3678794412 : ℝ) ^ 7 := by
  calc Real.exp (-(3 * (12 / 5 : ℝ))) ≤ Real.exp (-((7 : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.2; norm_num
    _ ≤ _ := exp_neg_one_pow_bounds 7

theorem one_sub_exp_neg_four_a_ge : (9998 : ℝ) / 10 ^ 4 ≤ 1 - Real.exp (-(4 * (12 / 5 : ℝ))) := by
  have : Real.exp (-(4 * (12 / 5 : ℝ))) ≤ (0.3678794412 : ℝ) ^ 9 := by
    calc Real.exp (-(4 * (12 / 5 : ℝ))) ≤ Real.exp (-((9 : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.2; norm_num
      _ ≤ _ := exp_neg_one_pow_bounds 9
  nlinarith [this]

/-! ## `‖g‖² = 12/5 + sin(2028/5)/169` -/

theorem normSq_packet_bounds :
    (2398056 : ℝ) / 10 ^ 6 < 12 / 5 + Real.sin (2028 / 5) / (2 * (169 / 2 : ℝ)) ∧
      12 / 5 + Real.sin (2028 / 5) / (2 * (169 / 2 : ℝ)) < (2398058 : ℝ) / 10 ^ 6 := by
  have h := twoOmegaA_sin
  constructor <;> nlinarith [h.1, h.2]

end PsiOmega.Num

#print axioms PsiOmega.Num.log_pi_bounds
#print axioms PsiOmega.Num.log_sqrt_z_bounds
#print axioms PsiOmega.Num.log_two_a_omega_bounds
#print axioms PsiOmega.Num.exp_neg_three_a_le
#print axioms PsiOmega.Num.one_sub_exp_neg_four_a_ge
#print axioms PsiOmega.Num.normSq_packet_bounds
