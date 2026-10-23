import Mathlib
import KaiserKernel
import StripShift

/-! # The Kaiser trial's Fourier side, and Paley–Wiener by contour shift (round 163, part 2)

`kH L η α z = z²(z² − α) · cos(β√(z² − L²)) · sinc(πηz)⁸` with `β = 2π(L − 4η)`.

* `norm_kH_le`: exponential type `2πL` with `1/(1 + (Re z)²)` decay on every horizontal line.
* `kh_eq_zero`: its inverse Fourier transform `h = 𝓕⁻ H` vanishes for `|ξ| > L`. The proof shifts the
  contour to `Im = T` with `strip_shift` (round 156) and lets `T → ∞`.
-/

open Complex Filter Topology MeasureTheory Real
open scoped FourierTransform

noncomputable section

namespace Kaiser

/-- The Kaiser trial's Fourier side. -/
def kH (L η α : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 * (z ^ 2 - α) * kK (2 * π * (L - 4 * η)) L z * sincE (π * η * z) ^ 8

theorem differentiable_kH (L η α : ℝ) : Differentiable ℂ (kH L η α) := by
  unfold kH
  have h1 := differentiable_kK (2 * π * (L - 4 * η)) L
  have h2 : Differentiable ℂ fun z : ℂ => sincE (π * η * z) :=
    differentiable_sincE.comp (by fun_prop)
  fun_prop

theorem kH_neg (L η α : ℝ) (z : ℂ) : kH L η α (-z) = kH L η α z := by
  have hK : kK (2 * π * (L - 4 * η)) L (-z) = kK (2 * π * (L - 4 * η)) L z := by
    simp [kK]
  have hS : sincE (π * η * -z) ^ 8 = sincE (π * η * z) ^ 8 := by
    simp only [sincE, mul_neg, neg_sq]
  simp only [kH, hK, hS, neg_sq]

/-- The polynomial–sinc envelope: `r²(r² + A)(1 + r²) ≤ (1 + A)(1/q)⁶(1 + qr)⁸` for `0 < q ≤ 1`. -/
theorem envelope {r q A : ℝ} (hr : 0 ≤ r) (hq : 0 < q) (hq1 : q ≤ 1) (hA : 0 ≤ A) :
    r ^ 2 * (r ^ 2 + A) * (1 + r ^ 2) ≤ (1 + A) * (1 / q) ^ 6 * (1 + q * r) ^ 8 := by
  have h1 : r ^ 2 * (r ^ 2 + A) ≤ (1 + A) * (1 + r ^ 2) ^ 2 := by nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  have h2 : (1 + r ^ 2) ^ 3 ≤ (1 + r) ^ 6 := by
    have : 1 + r ^ 2 ≤ (1 + r) ^ 2 := by nlinarith
    calc (1 + r ^ 2) ^ 3 ≤ ((1 + r) ^ 2) ^ 3 := by gcongr
      _ = (1 + r) ^ 6 := by ring
  have h3 : 1 + r ≤ (1 / q) * (1 + q * r) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hq]; nlinarith
  have h4 : (1 + r) ^ 6 ≤ (1 / q) ^ 6 * (1 + q * r) ^ 6 := by
    rw [← mul_pow]; gcongr
  have h5 : (1 + q * r) ^ 6 ≤ (1 + q * r) ^ 8 :=
    pow_le_pow_right₀ (by nlinarith) (by norm_num)
  calc r ^ 2 * (r ^ 2 + A) * (1 + r ^ 2) ≤ (1 + A) * (1 + r ^ 2) ^ 2 * (1 + r ^ 2) := by gcongr
    _ = (1 + A) * (1 + r ^ 2) ^ 3 := by ring
    _ ≤ (1 + A) * ((1 / q) ^ 6 * (1 + q * r) ^ 6) := by gcongr; linarith
    _ ≤ (1 + A) * ((1 / q) ^ 6 * (1 + q * r) ^ 8) := by gcongr
    _ = (1 + A) * (1 / q) ^ 6 * (1 + q * r) ^ 8 := by ring

/-- The growth constant. -/
def kA (L η α : ℝ) : ℝ := 6 ^ 8 * (1 + |α|) * (1 / (π * η)) ^ 6 * Real.exp (2 * π * (L - 4 * η) * L)

/-- The common core of the growth bounds: with `β = 2π(L − 4η)`, `q = πη` and `r = ‖z‖`,
`‖H(z)‖ ≤ r²(r² + |α|)·e^{β(|Im z| + L)}·(6e^{q|Im z|}/(1 + qr))⁸`. -/
theorem norm_kH_core {L η α : ℝ} (hη : 0 < η) (hL : 4 * η ≤ L) (z : ℂ) :
    ‖kH L η α z‖ ≤ ‖z‖ ^ 2 * (‖z‖ ^ 2 + |α|) * Real.exp (2 * π * (L - 4 * η) * (|z.im| + L)) *
      (6 * Real.exp (π * η * |z.im|) / (1 + π * η * ‖z‖)) ^ 8 := by
  set β := 2 * π * (L - 4 * η)
  set q := π * η
  have hq : 0 < q := by positivity
  have hβ : 0 ≤ β := by have := pi_pos; positivity
  have hL0 : 0 ≤ L := by linarith
  set r := ‖z‖
  have hK := norm_kK_le hβ hL0 z
  have hS := norm_sincE_le (π * η * z)
  have hcast : (π * η * z : ℂ) = ((π * η : ℝ) : ℂ) * z := by push_cast; ring
  have hSim : |(π * η * z : ℂ).im| = q * |z.im| := by
    rw [hcast, Complex.im_ofReal_mul, abs_mul, abs_of_pos hq]
  have hSn : ‖(π * η * z : ℂ)‖ = q * r := by
    rw [hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  rw [hSim, hSn] at hS
  have hpoly : ‖z ^ 2 - (α : ℂ)‖ ≤ r ^ 2 + |α| := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  unfold kH
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  gcongr

/-- `e^{β(|Im z| + L)}·e^{8q|Im z|} = e^{βL}·e^{2πL|Im z|}`. -/
theorem kH_exp_eq (L η y : ℝ) :
    Real.exp (2 * π * (L - 4 * η) * (y + L)) * Real.exp (π * η * y) ^ 8
      = Real.exp (2 * π * (L - 4 * η) * L) * Real.exp (2 * π * L * y) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring

/-- **Exponential type `2πL`**: `‖H(z)‖ ≤ A · e^{2πL|Im z|} / (1 + (Re z)²)`. -/
theorem norm_kH_le {L η α : ℝ} (hη : 0 < η) (hη1 : π * η ≤ 1) (hL : 4 * η ≤ L) (z : ℂ) :
    ‖kH L η α z‖ ≤ kA L η α * Real.exp (2 * π * L * |z.im|) / (1 + z.re ^ 2) := by
  set β := 2 * π * (L - 4 * η)
  set q := π * η
  have hq : 0 < q := by positivity
  have hβ : 0 ≤ β := by have := pi_pos; positivity
  have hL0 : 0 ≤ L := by linarith
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have hre : z.re ^ 2 ≤ r ^ 2 := by
    have := Complex.abs_re_le_norm z
    nlinarith [abs_nonneg z.re, sq_abs z.re]
  have hden : 0 < 1 + q * r := by positivity
  -- assemble
  have hmain : ‖kH L η α z‖ ≤ r ^ 2 * (r ^ 2 + |α|) * Real.exp (β * (|z.im| + L)) *
      (6 * Real.exp (q * |z.im|) / (1 + q * r)) ^ 8 :=
    norm_kH_core hη hL z
  have hexp : Real.exp (β * (|z.im| + L)) * Real.exp (q * |z.im|) ^ 8
      = Real.exp (β * L) * Real.exp (2 * π * L * |z.im|) :=
    kH_exp_eq L η |z.im|
  have henv := envelope hr hq hη1 (abs_nonneg α)
  rw [le_div_iff₀ (by positivity)]
  calc ‖kH L η α z‖ * (1 + z.re ^ 2)
      ≤ r ^ 2 * (r ^ 2 + |α|) * Real.exp (β * (|z.im| + L)) *
          (6 * Real.exp (q * |z.im|) / (1 + q * r)) ^ 8 * (1 + r ^ 2) := by
        gcongr
    _ = 6 ^ 8 * (r ^ 2 * (r ^ 2 + |α|) * (1 + r ^ 2)) / (1 + q * r) ^ 8 *
          (Real.exp (β * (|z.im| + L)) * Real.exp (q * |z.im|) ^ 8) := by
        rw [div_pow, mul_pow]; field_simp
    _ ≤ 6 ^ 8 * ((1 + |α|) * (1 / q) ^ 6 * (1 + q * r) ^ 8) / (1 + q * r) ^ 8 *
          (Real.exp (β * (|z.im| + L)) * Real.exp (q * |z.im|) ^ 8) := by
        gcongr
    _ = kA L η α * Real.exp (2 * π * L * |z.im|) := by
        rw [hexp, kA]; simp only [β, q]; field_simp

/-- On the real line, `‖H(x)‖ ≤ A/(1 + x²)`. -/
theorem norm_kH_real_le {L η α : ℝ} (hη : 0 < η) (hη1 : π * η ≤ 1) (hL : 4 * η ≤ L) (x : ℝ) :
    ‖kH L η α x‖ ≤ kA L η α / (1 + x ^ 2) := by
  have := norm_kH_le hη hη1 hL (x : ℂ) (α := α)
  simpa using this

theorem kA_nonneg (L η α : ℝ) : 0 ≤ kA L η α := by unfold kA; positivity

theorem continuous_kH_real (L η α : ℝ) : Continuous fun x : ℝ => kH L η α x :=
  (differentiable_kH L η α).continuous.comp continuous_ofReal

theorem integrable_kH_real {L η α : ℝ} (hη : 0 < η) (hη1 : π * η ≤ 1) (hL : 4 * η ≤ L) :
    Integrable fun x : ℝ => kH L η α x := by
  refine ((integrable_inv_one_add_sq).const_mul (kA L η α)).mono'
    (continuous_kH_real L η α).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have := norm_kH_real_le hη hη1 hL x (α := α)
  simpa [div_eq_mul_inv] using this

/-! ## Paley–Wiener by contour shift -/

/-- **Paley–Wiener.** `𝓕⁻ H` vanishes beyond `L`. -/
theorem kh_eq_zero {L η α : ℝ} (hη : 0 < η) (hη1 : π * η ≤ 1) (hL : 4 * η ≤ L) {ξ : ℝ}
    (hξ : L < ξ) : 𝓕⁻ (fun x : ℝ => kH L η α x) ξ = 0 := by
  have hL0 : 0 ≤ L := by linarith
  have hξ0 : 0 < ξ := by linarith
  set A := kA L η α
  set F : ℂ → ℂ := fun t => Complex.exp (2 * π * ξ * t * I) * kH L η α t
  have hF : 𝓕⁻ (fun x : ℝ => kH L η α x) ξ = ∫ r : ℝ, F (r + (0 : ℝ) * I) := by
    rw [fourierInv_eq']
    congr 1; funext v
    simp only [F, smul_eq_mul, ofReal_zero, zero_mul, add_zero,
      RCLike.inner_apply, conj_trivial]
    congr 2; push_cast; ring
  have hd : Differentiable ℂ F := by
    have := differentiable_kH L η α
    simp only [F]; fun_prop
  -- the bound on the strip `0 ≤ Im ≤ T`
  have hbound : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ PilotWeil.strip 0 T,
      ‖F t‖ ≤ A * Real.exp (2 * π * L * T) / (1 + t.re ^ 2) := by
    intro T hT t ht
    obtain ⟨h0, hT'⟩ := ht
    have he : ‖Complex.exp (2 * π * ξ * t * I)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have : (2 * π * ξ * t * I : ℂ).re = -(2 * π * ξ * t.im) := by
        simp [mul_re, mul_im]
      rw [this, Real.exp_le_one_iff]
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * π * ξ) h0]
    have hk := norm_kH_le hη hη1 hL t (α := α)
    have hab : |t.im| ≤ T := by rw [abs_of_nonneg h0]; exact hT'
    have hexp : Real.exp (2 * π * L * |t.im|) ≤ Real.exp (2 * π * L * T) := by
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_left hab (by positivity : (0:ℝ) ≤ 2 * π * L)]
    simp only [F, norm_mul]
    calc ‖Complex.exp (2 * π * ξ * t * I)‖ * ‖kH L η α t‖ ≤ 1 * (A * Real.exp (2 * π * L * |t.im|) /
          (1 + t.re ^ 2)) := by gcongr
      _ ≤ A * Real.exp (2 * π * L * T) / (1 + t.re ^ 2) := by
          rw [one_mul]; gcongr; exact kA_nonneg L η α
  -- shift to height `T`
  have hshift : ∀ T : ℝ, 0 ≤ T → ‖∫ r : ℝ, F (r + (0 : ℝ) * I)‖ ≤
      A * π * Real.exp (-(2 * π * (ξ - L) * T)) := by
    intro T hT
    rw [PilotWeil.strip_shift hT hd.differentiableOn (hbound T hT)]
    have hpt : ∀ r : ℝ, ‖F (r + T * I)‖ ≤ A * Real.exp (-(2 * π * (ξ - L) * T)) * (1 + r ^ 2)⁻¹ := by
      intro r
      have he : ‖Complex.exp (2 * π * ξ * ((r : ℂ) + T * I) * I)‖ = Real.exp (-(2 * π * ξ * T)) := by
        rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]
      have hk := norm_kH_le hη hη1 hL ((r : ℂ) + T * I) (α := α)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add,
        add_re, mul_re, sub_self, add_zero, abs_of_nonneg hT] at hk
      simp only [F, norm_mul, he]
      calc Real.exp (-(2 * π * ξ * T)) * ‖kH L η α (↑r + ↑T * I)‖
          ≤ Real.exp (-(2 * π * ξ * T)) * (A * Real.exp (2 * π * L * T) / (1 + r ^ 2)) := by gcongr
        _ = A * Real.exp (-(2 * π * (ξ - L) * T)) * (1 + r ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          have : Real.exp (-(2 * π * ξ * T)) * Real.exp (2 * π * L * T) = Real.exp (-(2 * π * (ξ - L) * T)) := by
            rw [← Real.exp_add]; ring_nf
          rw [← this]; ring
    calc ‖∫ r : ℝ, F (r + T * I)‖ ≤ ∫ r : ℝ, A * Real.exp (-(2 * π * (ξ - L) * T)) * (1 + r ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le ((integrable_inv_one_add_sq).const_mul _)
            (Eventually.of_forall hpt)
      _ = A * π * Real.exp (-(2 * π * (ξ - L) * T)) := by
          rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring
  -- let `T → ∞`
  have hlim : Tendsto (fun T : ℝ => A * π * Real.exp (-(2 * π * (ξ - L) * T))) atTop (𝓝 0) := by
    have hc : 0 < 2 * π * (ξ - L) := by have := pi_pos; nlinarith
    have : Tendsto (fun T : ℝ => -(2 * π * (ξ - L) * T)) atTop atBot := by
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul (A * π)
  rw [hF]
  apply norm_le_zero_iff.1
  exact ge_of_tendsto hlim ((eventually_ge_atTop 0).mono fun T hT => hshift T hT)

end Kaiser

#print axioms Kaiser.norm_kH_le
#print axioms Kaiser.integrable_kH_real
#print axioms Kaiser.kh_eq_zero
