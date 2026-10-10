/-
# Layer II helpers from round 211

Round 211's growth bound `growth_sum` (`6/7 ≤ a`, with `weighted_block` and `big_block`) was superseded
by `ExpSum10.growth_weak` (`4/5 ≤ a`) and `VinoFam.growth_sharp` (`2/3 < a`), and removed in round 218.
The pieces that later files use remain: `cpow_phase` (`n^{−σ−it}` as a phase times `n^{−σ}`), `exp_pow'`,
`dyadic` (splitting `(N₀, X]` into dyadic blocks) and `small_part` (the trivial bound for `n ≤ e^Λ`).
-/
import ExpSum6

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder VinoRec

/-- `n^{−s} = n^{−σ}·n^{−it}`. -/
lemma cpow_phase (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    1 / (n : ℂ) ^ ((σ : ℂ) + t * I) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * phaseF t n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [one_div, ← Complex.cpow_neg, neg_add, Complex.cpow_add _ _ hn0]
  congr 1
  · rw [Complex.ofReal_cpow hnr.le]; push_cast; ring_nf
  · unfold phaseF ee
    rw [Complex.cpow_def_of_ne_zero hn0]
    congr 1
    have hl : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log hnr.le]; push_cast; rfl
    rw [hl]
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

lemma exp_pow' (ν : ℝ) (k : ℕ) : Real.exp (ν / 20) ^ k = Real.exp (k * ν / 20) := by
  rw [← Real.exp_nat_mul]; ring_nf

set_option maxHeartbeats 800000 in
/-- **Dyadic decomposition.** -/
theorem dyadic (f : ℕ → ℂ) (N0 X : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ N N', N0 ≤ N → N ≤ N' → N' ≤ 2 * N → N' ≤ X → ‖∑ n ∈ Ioc N N', f n‖ ≤ B) :
    ∀ j : ℕ, ∀ Y, Y ≤ X → Y ≤ 2 ^ j * N0 → ‖∑ n ∈ Ioc N0 Y, f n‖ ≤ j * B := by
  intro j
  induction j with
  | zero =>
    intro Y _ hY
    rw [Finset.Ioc_eq_empty_of_le (by simpa using hY)]
    simp
  | succ j ih =>
    intro Y hYX hY
    rcases le_or_gt Y (2 ^ j * N0) with h | h
    · have := ih Y hYX h
      push_cast
      nlinarith
    · have hN0j : N0 ≤ 2 ^ j * N0 := Nat.le_mul_of_pos_left _ (by positivity)
      rw [← Finset.sum_Ioc_consecutive f hN0j h.le]
      have h1 := ih (2 ^ j * N0) (by omega) le_rfl
      have h2 := hB (2 ^ j * N0) Y hN0j h.le (by rw [pow_succ] at hY; linarith) hYX
      push_cast
      calc _ ≤ ‖∑ n ∈ Ioc N0 (2 ^ j * N0), f n‖ + ‖∑ n ∈ Ioc (2 ^ j * N0) Y, f n‖ := norm_add_le _ _
        _ ≤ j * B + B := add_le_add h1 h2
        _ = (j + 1) * B := by ring

/-- **The initial segment**, bounded trivially. -/
theorem small_part {σ δ Λ t : ℝ} (Y : ℕ) (hY : (Y : ℝ) ≤ 2 * Real.exp Λ) (hΛ : 0 ≤ Λ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 1 - δ ≤ σ) :
    ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 2 * Real.exp (Λ * δ) * (2 + Λ) := by
  have hE : (2 * Real.exp Λ) ^ δ ≤ 2 * Real.exp (Λ * δ) := by
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    have : (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hterm : ∀ n ∈ Ioc 0 Y, ‖1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤
      2 * Real.exp (Λ * δ) * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Ioc.mp hn).1
    have hnY : n ≤ Y := (mem_Ioc.mp hn).2
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    rw [cpow_phase n hn1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
    have hph : ‖phaseF t n‖ ≤ 1 := norm_phaseF t n
    have h1 : (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hnr (by linarith)
    have h2 : (n : ℝ) ^ (δ - 1) = (n : ℝ) ^ δ * (1 / (n : ℝ)) := by
      rw [Real.rpow_sub hn0, Real.rpow_one]; ring
    have h3 : (n : ℝ) ^ δ ≤ (2 * Real.exp Λ) ^ δ :=
      Real.rpow_le_rpow hn0.le (le_trans (by exact_mod_cast hnY) hY) hδ0
    have hpow0 : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hn0.le _
    calc (n : ℝ) ^ (-σ) * ‖phaseF t n‖ ≤ (n : ℝ) ^ (-σ) * 1 :=
          mul_le_mul_of_nonneg_left hph hpow0
      _ ≤ (n : ℝ) ^ δ * (1 / (n : ℝ)) := by rw [mul_one, ← h2]; exact h1
      _ ≤ 2 * Real.exp (Λ * δ) * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (h3.trans hE) (by positivity)
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases Nat.eq_zero_or_pos Y with h0 | hpos
  · subst h0; simp; linarith
  have hharm : ∑ n ∈ Ioc 0 Y, 1 / (n : ℝ) = (harmonic Y : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast
    rw [show Icc 1 Y = Ioc 0 Y by ext n; simp [mem_Icc, mem_Ioc]; omega]
    simp [one_div]
  rw [hharm]
  refine (harmonic_le_one_add_log Y).trans ?_
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hpos
  have := Real.log_le_log hYr hY
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have := Real.log_two_lt_d9
  linarith

end ExpSum
