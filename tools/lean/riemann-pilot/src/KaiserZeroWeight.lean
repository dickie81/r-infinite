import Mathlib
import KaiserPoissonK
import WeilAssemble

/-! # The zero weight on the line `Im t = −1` (round 164, part 2)

For `τ = σ + is` a zero ordinate (`|s| < ½`) and `x ∈ ℝ`, put
`V_τ(x) = P_{1+s}(x − σ) + P_{1−s}(x + σ)`. Then `π V_τ(x) = Im 2t₀/(t₀² − τ²)` with `t₀ = x − i`, so by
Hadamard (`hasSum_logDeriv_Xi`) `Σ_τ V_τ(x) = Im(Ξ′/Ξ)(x − i)/π`, and on `Re s = 3/2`
(`logDeriv_Xi_eq`) this is `≤ (C + ½ log(|x| + 2))/π`. Every zero counts, on the line or off it.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

open Pilot1ca Pilot1bt

/-- `Re ψ(z) ≤ log|z| + 4` for `Re z ≥ 1/4`. -/
theorem digamma_re_le {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    (Complex.digamma z).re ≤ Real.log ‖z‖ + 4 := by
  have hz0 : 0 < z.re := by linarith
  rw [PilotDigamma.digamma_eq_lap hz0, sub_re, sub_re, Complex.log_re]
  have hinv : ‖1 / (2 * z)‖ ≤ 2 := by
    have hnz : 1 / 4 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, div_le_iff₀ (by positivity)]; linarith
  have hlap : ‖PilotDigamma.lap z‖ ≤ 2 := by
    refine (PilotDigamma.norm_lap_le hz0).trans ?_
    rw [div_le_iff₀ (by positivity)]; linarith
  have a1 := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hinv)
  have a2 := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hlap)
  linarith

/-- `Σ Λ(n)/n^{3/2}`. -/
def kLam : ℝ := ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖

theorem norm_LSeries_vonMangoldt_le (x : ℝ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 + I * x)‖ ≤ kLam := by
  have h1 : 1 < (3 / 2 + I * (x : ℂ)).re := by simp; norm_num
  have hs := summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt h1)
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  unfold kLam
  congr 1; funext n
  simp only [LSeries.norm_term_eq]
  congr 3; simp

/-- **`Im(Ξ′/Ξ)(x − i) ≤ 3 + kLam + ½ log(|x| + 2)`.** -/
theorem im_logDeriv_Xi_le (x : ℝ) :
    (logDeriv Xi ((x : ℂ) - I)).im ≤ 5 + kLam + Real.log (|x| + 2) / 2 := by
  have hs : (1 / 2 + I * ((x : ℂ) - I)) = 3 / 2 + I * x := by ring_nf; rw [I_sq]; ring
  have hre : 1 < (1 / 2 + I * ((x : ℂ) - I)).re := by rw [hs]; simp; norm_num
  rw [logDeriv_Xi_eq hre, hs]
  set s : ℂ := 3 / 2 + I * x
  have hsre : s.re = 3 / 2 := by simp [s]
  have hsim : s.im = x := by simp [s]
  simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  simp only [add_re, sub_re, Complex.div_ofNat_re]
  -- `Re(1/s) ≤ 1`, `Re(1/(s − 1)) ≤ 2`
  have hn1 : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by
      have := Complex.re_le_norm s; rw [hsre] at this; linarith)]
    have := Complex.re_le_norm s; rw [hsre] at this; linarith
  have hn2 : ‖1 / (s - 1)‖ ≤ 2 := by
    have : 1 / 2 ≤ ‖s - 1‖ := by
      have := Complex.re_le_norm (s - 1); rw [sub_re, hsre, one_re] at this; linarith
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have r1 := (Complex.re_le_norm _).trans hn1
  have r2 := (Complex.re_le_norm _).trans hn2
  have hlogpi : 0 ≤ (Real.log π : ℂ).re / 2 := by
    rw [ofReal_re]; have := Real.log_nonneg (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ π); positivity
  -- `Re ψ(s/2) ≤ log|s/2| + 4 ≤ log(|x| + 2) + 4`
  have hz : 1 / 4 ≤ (s / 2).re := by simp [hsre]; norm_num
  have hpsi := digamma_re_le hz
  have hnorm : ‖s / 2‖ ≤ |x| + 2 := by
    rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    rw [this]; linarith [abs_nonneg x]
  have hpos : 0 < ‖s / 2‖ := lt_of_lt_of_le (by norm_num) (hz.trans (Complex.re_le_norm _))
  have hlog : Real.log ‖s / 2‖ ≤ Real.log (|x| + 2) := Real.log_le_log hpos hnorm
  have hL := (Complex.re_le_norm _).trans (norm_LSeries_vonMangoldt_le x)
  have hLneg := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans (norm_LSeries_vonMangoldt_le x))
  linarith

/-- The Poisson pair of a zero ordinate: `V_τ(x) = P_{1+s}(x − σ) + P_{1−s}(x + σ)`. -/
def Vz (τ : ℂ) (x : ℝ) : ℝ := pk (1 + τ.im) (x - τ.re) + pk (1 - τ.im) (x + τ.re)

theorem Vz_nonneg {τ : ℂ} (hτ : |τ.im| < 1 / 2) (x : ℝ) : 0 ≤ Vz τ x := by
  have := abs_lt.1 hτ
  exact add_nonneg (pk_nonneg (by linarith) _) (pk_nonneg (by linarith) _)

theorem im_inv_line (a b : ℝ) (hb : 0 < b) :
    (1 / ((a : ℂ) - b * I)).im = π * pk b a := by
  have hn : Complex.normSq ((a : ℂ) - b * I) = a ^ 2 + b ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [one_div, Complex.inv_im, hn]
  simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one, zero_sub, neg_neg]
  unfold pk
  have : 0 < a ^ 2 + b ^ 2 := by positivity
  field_simp; ring

/-- **`Im 2t₀/(t₀² − τ²) = π V_τ(x)`** at `t₀ = x − i`. -/
theorem im_pair (x : ℝ) {τ : ℂ} (hτ : |τ.im| < 1 / 2) :
    (2 * ((x : ℂ) - I) / (((x : ℂ) - I) ^ 2 - τ ^ 2)).im = π * Vz τ x := by
  have hs := abs_lt.1 hτ
  set σ := τ.re; set s := τ.im
  have hτe : τ = σ + s * I := (Complex.re_add_im τ).symm
  have h1 : (x : ℂ) - I - τ = ((x - σ : ℝ) : ℂ) - ((1 + s : ℝ) : ℂ) * I := by rw [hτe]; push_cast; ring
  have h2 : (x : ℂ) - I + τ = ((x + σ : ℝ) : ℂ) - ((1 - s : ℝ) : ℂ) * I := by rw [hτe]; push_cast; ring
  have n1 : (x : ℂ) - I - τ ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [h1] at this; simp at this; linarith
  have n2 : (x : ℂ) - I + τ ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [h2] at this; simp at this; linarith
  have e : 2 * ((x : ℂ) - I) / (((x : ℂ) - I) ^ 2 - τ ^ 2) = 1 / ((x : ℂ) - I - τ) + 1 / ((x : ℂ) - I + τ) := by
    have : ((x : ℂ) - I) ^ 2 - τ ^ 2 = ((x : ℂ) - I - τ) * ((x : ℂ) - I + τ) := by ring
    rw [this]; field_simp; ring
  rw [e, add_im, h1, h2, im_inv_line _ _ (by linarith), im_inv_line _ _ (by linarith), Vz]
  ring

/-- **The zero weight**: `Σ_τ V_τ(x) = Im(Ξ′/Ξ)(x − i)/π`, over the zeros of `Ξ(√w)` with multiplicity. -/
theorem hasSum_Vz (x : ℝ) :
    HasSum (fun i : ZeroIdx (sqF Xi) => Vz (tau i) x) ((logDeriv Xi ((x : ℂ) - I)).im / π) := by
  have H := Complex.hasSum_im (hasSum_logDeriv_Xi (Xi_line_ne_zero x))
  have e : ∀ i : ZeroIdx (sqF Xi), (2 * ((x : ℂ) - I) / (((x : ℂ) - I) ^ 2 - i.1)).im = π * Vz (tau i) x := by
    intro i; rw [← tau_sq i]; exact im_pair x (tau_im i)
  simp_rw [e] at H
  have := H.div_const π
  simp_rw [mul_div_cancel_left₀ _ pi_ne_zero] at this
  exact this

theorem tsum_Vz_le (x : ℝ) :
    ∑' i : ZeroIdx (sqF Xi), Vz (tau i) x ≤ (5 + kLam + Real.log (|x| + 2) / 2) / π := by
  rw [(hasSum_Vz x).tsum_eq]
  exact div_le_div_of_nonneg_right (im_logDeriv_Xi_le x) pi_pos.le

end Kaiser

#print axioms Kaiser.tsum_Vz_le
#print axioms Kaiser.hasSum_Vz
