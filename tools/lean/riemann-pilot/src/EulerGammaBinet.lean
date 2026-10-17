import Mathlib
import BinetProof

/-! # Euler's constant to seven digits, from Binet's formula (round 406)

`φ(s) = 1/(1 − e^{−s}) − 1/s − 1/2 = Σ_{n≥1} 2s/(s² + 4π²n²)` (`PilotDigamma.hasSum_phiB`) lies between
`s/12 − s³/720` and `s/12`, by `ζ(2) = π²/6` and `ζ(4) = π⁴/90`. Through `ψ(x) = log x − 1/(2x) −
∫_0^∞ e^{−xs}φ(s) ds` (`PilotDigamma.digamma_eq_lap`) at `x = 16`, where `ψ(16) = H₁₅ − γ` and
`log 16 = 4 log 2`, this pins `0.57721566 < γ < 0.57721580`.
-/

open Real Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

namespace Electron

open PilotDigamma

theorem hasSum_inv_succ_sq : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

theorem hasSum_inv_succ_four : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 4) (π ^ 4 / 90) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  simpa using h

/-- `φ(s) ≤ s/12`. -/
theorem phiB_le {s : ℝ} (hs : 0 < s) : phiB s ≤ s / 12 := by
  have h := hasSum_phiB hs
  have hz := hasSum_inv_succ_sq.mul_left (s / (2 * π ^ 2))
  have hle : ∀ n : ℕ, 2 * s / (s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2)
      ≤ s / (2 * π ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hc : (0 : ℝ) < (2 * π * ((n : ℝ) + 1)) ^ 2 := by positivity
    have key : 2 * s / (s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2) ≤ 2 * s / (2 * π * ((n : ℝ) + 1)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hc (by nlinarith)
    calc _ ≤ _ := key
      _ = s / (2 * π ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
        field_simp
  calc phiB s ≤ s / (2 * π ^ 2) * (π ^ 2 / 6) := hasSum_le hle h hz
    _ = s / 12 := by field_simp; ring

/-- `s/12 − s³/720 ≤ φ(s)`. -/
theorem le_phiB {s : ℝ} (hs : 0 < s) : s / 12 - s ^ 3 / 720 ≤ phiB s := by
  have h := hasSum_phiB hs
  have hz := (hasSum_inv_succ_sq.mul_left (s / (2 * π ^ 2))).sub
    (hasSum_inv_succ_four.mul_left (s ^ 3 / (8 * π ^ 4)))
  have hle : ∀ n : ℕ, s / (2 * π ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)
      - s ^ 3 / (8 * π ^ 4) * (1 / ((n : ℝ) + 1) ^ 4)
      ≤ 2 * s / (s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set C : ℝ := (2 * π * ((n : ℝ) + 1)) ^ 2 with hC
    have hC0 : 0 < C := by positivity
    have e1 : s / (2 * π ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) = 2 * s / C := by
      rw [hC]; field_simp
    have e2 : s ^ 3 / (8 * π ^ 4) * (1 / ((n : ℝ) + 1) ^ 4) = 2 * s ^ 3 / C ^ 2 := by
      rw [hC]; field_simp; ring
    rw [e1, e2]
    have e3 : 2 * s / (s ^ 2 + C) - (2 * s / C - 2 * s ^ 3 / C ^ 2)
        = 2 * s ^ 5 / (C ^ 2 * (s ^ 2 + C)) := by
      field_simp
      ring
    have : 0 ≤ 2 * s ^ 5 / (C ^ 2 * (s ^ 2 + C)) := by positivity
    linarith
  calc s / 12 - s ^ 3 / 720
      = s / (2 * π ^ 2) * (π ^ 2 / 6) - s ^ 3 / (8 * π ^ 4) * (π ^ 4 / 90) := by
        field_simp; ring
    _ ≤ phiB s := hasSum_le hle hz h

theorem integrableOn_exp_mul_phiB {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s => Real.exp (-(x * s)) * phiB s) (Ioi 0) := by
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(x * s))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hx
  refine Integrable.mono' (he.mul_const (1 / 2)) ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.mul
      continuousOn_phiB).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s (hs : 0 < s) => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_phiB_le hs) (Real.exp_pos _).le

theorem integrableOn_pow_mul_exp {x : ℝ} (hx : 0 < x) (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(x * s))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := x)
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) one_pos hx
  refine h.congr_fun (fun s (hs : 0 < s) => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]

theorem integral_pow_mul_exp {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(x * s)) = (1 / x) ^ (k + 1) * (k.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := x) (by positivity) hx
  have hG : Real.Gamma ((k : ℝ) + 1) = k.factorial := Real.Gamma_nat_eq_factorial k
  rw [hG, add_sub_cancel_right] at h
  rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) => ?_)
  simp only [Real.rpow_natCast]

/-- The real Laplace integral `L(x) = ∫_0^∞ e^{−xs}φ(s) ds`. -/
def lapR (x : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), Real.exp (-(x * s)) * phiB s

theorem lap_ofReal (x : ℝ) : lap (x : ℂ) = (lapR x : ℂ) := by
  rw [lap, lapR, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  push_cast
  ring_nf

theorem lapR_le {x : ℝ} (hx : 0 < x) : lapR x ≤ 1 / (12 * x ^ 2) := by
  have hm := setIntegral_mono_on (integrableOn_exp_mul_phiB hx)
    ((integrableOn_pow_mul_exp hx 1).mul_const (1 / 12)) measurableSet_Ioi
    (fun s (hs : 0 < s) => by
      have := phiB_le hs
      have he := (Real.exp_pos (-(x * s))).le
      calc Real.exp (-(x * s)) * phiB s ≤ Real.exp (-(x * s)) * (s / 12) :=
            mul_le_mul_of_nonneg_left this he
        _ = s ^ 1 * Real.exp (-(x * s)) * (1 / 12) := by ring)
  rw [integral_mul_const, integral_pow_mul_exp hx 1] at hm
  calc lapR x ≤ _ := hm
    _ = 1 / (12 * x ^ 2) := by
      norm_num

theorem le_lapR {x : ℝ} (hx : 0 < x) : 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) ≤ lapR x := by
  have hi : IntegrableOn (fun s : ℝ => s ^ 1 * Real.exp (-(x * s)) * (1 / 12)
      - s ^ 3 * Real.exp (-(x * s)) * (1 / 720)) (Ioi 0) :=
    ((integrableOn_pow_mul_exp hx 1).mul_const _).sub ((integrableOn_pow_mul_exp hx 3).mul_const _)
  have hm := setIntegral_mono_on hi (integrableOn_exp_mul_phiB hx) measurableSet_Ioi
    (fun s (hs : 0 < s) => by
      have := le_phiB hs
      have he := (Real.exp_pos (-(x * s))).le
      calc s ^ 1 * Real.exp (-(x * s)) * (1 / 12) - s ^ 3 * Real.exp (-(x * s)) * (1 / 720)
          = Real.exp (-(x * s)) * (s / 12 - s ^ 3 / 720) := by ring
        _ ≤ Real.exp (-(x * s)) * phiB s := mul_le_mul_of_nonneg_left this he)
  rw [integral_sub ((integrableOn_pow_mul_exp hx 1).mul_const _)
    ((integrableOn_pow_mul_exp hx 3).mul_const _), integral_mul_const, integral_mul_const,
    integral_pow_mul_exp hx 1, integral_pow_mul_exp hx 3] at hm
  calc 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)
      = (1 / x) ^ (1 + 1) * ((Nat.factorial 1 : ℕ) : ℝ) * (1 / 12)
        - (1 / x) ^ (3 + 1) * ((Nat.factorial 3 : ℕ) : ℝ) * (1 / 720) := by
        simp only [Nat.factorial]; push_cast; field_simp; ring
    _ ≤ lapR x := hm

theorem harmonic_fifteen : (harmonic 15 : ℝ) = 1195757 / 360360 := by
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `γ = H₁₅ − 4 log 2 + 1/32 + L(16)`. -/
theorem eulerMascheroni_eq :
    Real.eulerMascheroniConstant = (harmonic 15 : ℝ) - 4 * Real.log 2 + 1 / 32 + lapR 16 := by
  have h1 := Complex.digamma_nat_add_one 15
  have h2 := digamma_eq_lap (z := (16 : ℂ)) (by norm_num)
  have e16 : ((15 : ℕ) : ℂ) + 1 = (16 : ℂ) := by norm_num
  rw [e16, h2, show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num, lap_ofReal,
    ← Complex.ofReal_log (by norm_num)] at h1
  have h3 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have h4 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.div_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_im, Complex.ratCast_re] at h4
  norm_num at h4
  rw [h3] at h4
  linarith [harmonic_fifteen]

/-- **Euler's constant to seven digits**: `0.57721566 < γ < 0.57721580`. -/
theorem eulerMascheroni_bounds :
    (0.57721566 : ℝ) < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < 0.57721580 := by
  rw [eulerMascheroni_eq, harmonic_fifteen]
  have hu := lapR_le (x := 16) (by norm_num)
  have hl := le_lapR (x := 16) (by norm_num)
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  constructor <;> norm_num at hu hl ⊢ <;> linarith

end Electron

#print axioms Electron.eulerMascheroni_bounds
