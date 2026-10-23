import Mathlib
import StripShift

/-! # The Poisson kernel of the half-plane (round 164, part 1)

`P_y(x) = y/(π(x² + y²))` has `∫ P_y(x) e^{ixw} dx = e^{−y|w|}` (Fourier inversion of `e^{−y|w|}`).
So for `F(t) = ∫_0^∞ ψ(w) e^{itw} dw` and `s > −1`,
`F(σ + is) = ∫ P_{1+s}(x) F(σ + x − i) dx`, and `‖F(σ + is)‖² ≤ ∫ P_{1+s}(x) ‖F(σ + x − i)‖² dx`.
-/

open Complex Filter Topology MeasureTheory Real Set
open scoped FourierTransform

noncomputable section

namespace Kaiser

/-- `e^{−y|w|}`. -/
def ey (y : ℝ) (w : ℝ) : ℂ := (Real.exp (-(y * |w|)) : ℂ)

theorem continuous_ey (y : ℝ) : Continuous (ey y) := by unfold ey; fun_prop

theorem integrable_ey {y : ℝ} (hy : 0 < y) : Integrable (ey y) :=
  (PilotWeil.integrable_exp_neg_abs hy).ofReal

theorem fourier_ey {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    𝓕 (ey y) ξ = ((2 * y / (y ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  set f : ℝ → ℂ := fun v => Complex.exp (↑(-2 * π * v * ξ) * I) * ey y v
  set A : ℂ := (y : ℂ) - 2 * π * ξ * I
  set B : ℂ := -(y : ℂ) - 2 * π * ξ * I
  have hA : 0 < A.re := by simp [A]; exact hy
  have hB : B.re < 0 := by simp [B]; exact hy
  have e1 : ∀ v ∈ Iic (0 : ℝ), f v = Complex.exp (A * v) := by
    intro v hv
    have : |v| = -v := abs_of_nonpos hv
    simp only [f, ey, this, A, Complex.ofReal_exp]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : ∀ v ∈ Ioi (0 : ℝ), f v = Complex.exp (B * v) := by
    intro v hv
    have : |v| = v := abs_of_pos hv
    simp only [f, ey, this, B, Complex.ofReal_exp]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have i1 : IntegrableOn f (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hA 0).congr_fun (fun v hv => (e1 v hv).symm) measurableSet_Iic
  have i2 : IntegrableOn f (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hB 0).congr_fun (fun v hv => (e2 v hv).symm) measurableSet_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi i1 i2, setIntegral_congr_fun measurableSet_Iic e1,
    setIntegral_congr_fun measurableSet_Ioi e2, integral_exp_mul_complex_Iic hA,
    integral_exp_mul_complex_Ioi hB]
  have hA0 : A ≠ 0 := fun h => by rw [h, zero_re] at hA; exact lt_irrefl _ hA
  have hB0 : B ≠ 0 := fun h => by rw [h, zero_re] at hB; exact lt_irrefl _ hB
  have hd : ((y ^ 2 + (2 * π * ξ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < y ^ 2 + (2 * π * ξ) ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hAB : A * B = -((y ^ 2 + (2 * π * ξ) ^ 2 : ℝ) : ℂ) := by
    simp only [A, B]; push_cast; ring_nf; rw [I_sq]; ring
  have hBA : B - A = -(2 * y : ℂ) := by simp only [A, B]; ring
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (1 : ℂ) / A + -1 / B = (B - A) / (A * B) by field_simp; ring, hAB, hBA]
  push_cast; field_simp

theorem integrable_fourier_ey {y : ℝ} (hy : 0 < y) : Integrable (𝓕 (ey y)) := by
  have hc : (2 * π / y) ≠ 0 := by have := pi_pos; positivity
  have hi := ((integrable_inv_one_add_sq.comp_mul_left' hc).const_mul (2 / y)).ofReal (𝕜 := ℂ)
  refine hi.congr (ae_of_all _ fun ξ => ?_)
  have e : 2 / y * (1 + (2 * π / y * ξ) ^ 2)⁻¹ = 2 * y / (y ^ 2 + (2 * π * ξ) ^ 2) := by
    have : 0 < y ^ 2 + (2 * π * ξ) ^ 2 := by positivity
    field_simp
  show ((2 / y * (1 + (2 * π / y * ξ) ^ 2)⁻¹ : ℝ) : ℂ) = 𝓕 (ey y) ξ
  rw [fourier_ey hy ξ, e]

/-- The Poisson kernel `P_y(x) = y/(π(x² + y²))`. -/
def pk (y x : ℝ) : ℝ := y / (π * (x ^ 2 + y ^ 2))

theorem continuous_pk {y : ℝ} (hy : 0 < y) : Continuous (pk y) := by
  unfold pk
  exact continuous_const.div (by fun_prop) fun x => (mul_pos pi_pos (by positivity)).ne'

theorem pk_nonneg {y : ℝ} (hy : 0 ≤ y) (x : ℝ) : 0 ≤ pk y x := by
  unfold pk; have := pi_pos; positivity

/-- **`∫ P_y(x) e^{ixw} dx = e^{−y|w|}`.** -/
theorem integral_pk_exp {y : ℝ} (hy : 0 < y) (w : ℝ) :
    ∫ x : ℝ, (pk y x : ℂ) * Complex.exp (I * x * w) = ey y w := by
  have hinv := congrFun (Continuous.fourierInv_fourier_eq (continuous_ey y) (integrable_ey hy)
    (integrable_fourier_ey hy)) w
  rw [fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  simp only [smul_eq_mul, fourier_ey hy] at hinv
  set g : ℝ → ℂ := fun x => Complex.exp (↑(x * w) * I) * ((2 * y / (y ^ 2 + x ^ 2) : ℝ) : ℂ)
  have hg : ∀ ξ : ℝ, Complex.exp (↑(-2 * π * ξ * -w) * I) * ((2 * y / (y ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ)
      = g (2 * π * ξ) := by
    intro ξ; simp only [g]; congr 3; ring_nf
  simp_rw [hg] at hinv
  rw [Measure.integral_comp_mul_left g (2 * π)] at hinv
  have hpi : 0 < 2 * π := by have := pi_pos; positivity
  rw [abs_of_pos (inv_pos.2 hpi)] at hinv
  rw [← hinv, Complex.real_smul, ← integral_const_mul]
  congr 1; funext x
  simp only [g, pk]
  have : 0 < y ^ 2 + x ^ 2 := by positivity
  push_cast
  rw [show (↑x * ↑w * I : ℂ) = I * ↑x * ↑w by ring]
  field_simp
  ring

theorem integral_pk {y : ℝ} (hy : 0 < y) : ∫ x : ℝ, pk y x = 1 := by
  have h := integral_pk_exp hy 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one, ey, abs_zero, neg_zero,
    Real.exp_zero, ofReal_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem integrable_pk {y : ℝ} (hy : 0 < y) : Integrable (pk y) := by
  by_contra h
  have := integral_pk hy
  rw [integral_undef h] at this; norm_num at this

/-! ## The Poisson representation -/

/-- `F(t) = ∫_0^∞ ψ(w) e^{itw} dw`. -/
def Fl (ψ : ℝ → ℂ) (t : ℂ) : ℂ := ∫ w in Ioi (0 : ℝ), ψ w * Complex.exp (I * t * w)

section Rep

variable {ψ : ℝ → ℂ} (hm : AEStronglyMeasurable ψ (volume.restrict (Ioi 0)))
  (hi : IntegrableOn (fun w => ‖ψ w‖ * Real.exp w) (Ioi 0))
include hm hi

omit hm hi in
theorem norm_Fl_line_le (x : ℝ) :
    ‖Fl ψ (x - I)‖ ≤ ∫ w in Ioi (0 : ℝ), ‖ψ w‖ * Real.exp w := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
  rw [norm_mul, Complex.norm_exp]; congr 2; simp

theorem continuous_Fl_line : Continuous fun x : ℝ => Fl ψ (x - I) := by
  refine continuous_of_dominated (bound := fun w => ‖ψ w‖ * Real.exp w)
    (fun x => hm.mul (Continuous.aestronglyMeasurable
      (by fun_prop : Continuous fun w : ℝ => Complex.exp (I * ((x : ℂ) - I) * w))))
    (fun x => ae_of_all _ fun w => ?_) hi
    (ae_of_all _ fun w => by fun_prop)
  rw [norm_mul, Complex.norm_exp]; apply le_of_eq; congr 2; simp

/-- **The Poisson representation**: `F(σ + is) = ∫ P_{1+s}(x) F(σ + x − i) dx` for `s > −1`. -/
theorem Fl_poisson {σ s : ℝ} (hs : -1 < s) :
    Fl ψ (σ + s * I) = ∫ x : ℝ, (pk (1 + s) x : ℂ) * Fl ψ (σ + x - I) := by
  have hy : 0 < 1 + s := by linarith
  set F : ℝ → ℝ → ℂ := fun x w => (pk (1 + s) x : ℂ) * (ψ w * Complex.exp (I * ((σ : ℂ) + x - I) * w))
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    have hprod := ((integrable_pk hy).mul_prod (hi : Integrable (fun w => ‖ψ w‖ * Real.exp w) (volume.restrict (Ioi (0 : ℝ)))))
    refine hprod.mono' ?_ (ae_of_all _ fun z => ?_)
    · have m1 : AEStronglyMeasurable (fun z : ℝ × ℝ => ψ z.2) (volume.prod (volume.restrict (Ioi 0))) :=
        hm.comp_snd
      have m2 : AEStronglyMeasurable (fun z : ℝ × ℝ => Complex.exp (I * ((σ : ℂ) + z.1 - I) * z.2))
          (volume.prod (volume.restrict (Ioi 0))) := Continuous.aestronglyMeasurable (by fun_prop)
      have m0 : AEStronglyMeasurable (fun z : ℝ × ℝ => (pk (1 + s) z.1 : ℂ))
          (volume.prod (volume.restrict (Ioi 0))) :=
        (Complex.continuous_ofReal.comp ((continuous_pk hy).comp continuous_fst)).aestronglyMeasurable
      exact m0.mul (m1.mul m2)
    · simp only [Function.uncurry, F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pk_nonneg hy.le _), Complex.norm_exp]
      apply le_of_eq; congr 2; simp
  have hswap := integral_integral_swap hF
  simp only [F] at hswap
  unfold Fl
  simp_rw [← integral_const_mul]
  rw [hswap]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw0 : 0 ≤ w := le_of_lt hw
  have e : ∀ x : ℝ, (pk (1 + s) x : ℂ) * (ψ w * Complex.exp (I * ((σ : ℂ) + x - I) * w)) =
      (ψ w * Complex.exp (I * σ * w) * Complex.exp (w : ℂ)) * ((pk (1 + s) x : ℂ) * Complex.exp (I * x * w)) := by
    intro x
    rw [show I * ((σ : ℂ) + x - I) * w = I * σ * w + w + I * x * w by ring_nf; rw [I_sq]; ring,
      Complex.exp_add, Complex.exp_add]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_pk_exp hy, ey, abs_of_nonneg hw0, Complex.ofReal_exp]
  simp only [mul_assoc]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2; push_cast; ring_nf; rw [I_sq]; ring

omit hm hi in
/-- **Cauchy–Schwarz against `P`**: `‖∫ P F‖² ≤ ∫ P ‖F‖²` for bounded measurable `F`. -/
theorem norm_sq_pk_le {y : ℝ} (hy : 0 < y) {F : ℝ → ℂ} (hFm : AEStronglyMeasurable F volume)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    ‖∫ x : ℝ, (pk y x : ℂ) * F x‖ ^ 2 ≤ ∫ x : ℝ, pk y x * ‖F x‖ ^ 2 := by
  have hP := integrable_pk hy
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have i1 : Integrable fun x => pk y x * ‖F x‖ :=
    (hP.mul_const B).mono' (hP.aestronglyMeasurable.mul hFm.norm)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pk_nonneg hy.le x) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hB x) (pk_nonneg hy.le x))
  have i2 : Integrable fun x => pk y x * ‖F x‖ ^ 2 :=
    (hP.mul_const (B ^ 2)).mono' (hP.aestronglyMeasurable.mul (hFm.norm.pow 2))
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pk_nonneg hy.le x) (by positivity))]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hB x) 2) (pk_nonneg hy.le x))
  set A := ∫ x, pk y x * ‖F x‖
  have h1 : ‖∫ x : ℝ, (pk y x : ℂ) * F x‖ ≤ A := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pk_nonneg hy.le x)]
  have hA0 : 0 ≤ A := integral_nonneg fun x => mul_nonneg (pk_nonneg hy.le x) (norm_nonneg _)
  -- `0 ≤ ∫ P (‖F‖ − A)² = ∫ P‖F‖² − A²`
  have h2 : 0 ≤ ∫ x, pk y x * (‖F x‖ - A) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (pk_nonneg hy.le x) (sq_nonneg _)
  have e : ∫ x, pk y x * (‖F x‖ - A) ^ 2 = (∫ x, pk y x * ‖F x‖ ^ 2) - 2 * A * A + A ^ 2 * ∫ x, pk y x := by
    have : (fun x => pk y x * (‖F x‖ - A) ^ 2) =
        fun x => pk y x * ‖F x‖ ^ 2 - 2 * A * (pk y x * ‖F x‖) + A ^ 2 * pk y x := by
      funext x; ring
    have j1 : Integrable fun x => pk y x * ‖F x‖ ^ 2 - 2 * A * (pk y x * ‖F x‖) := i2.sub (i1.const_mul _)
    have j2 : Integrable fun x => A ^ 2 * pk y x := hP.const_mul _
    rw [this, integral_add j1 j2, integral_sub i2 (i1.const_mul _), integral_const_mul, integral_const_mul]
  rw [e, integral_pk hy] at h2
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2]

/-- **The Poisson majorant**: `‖F(σ + is)‖² ≤ ∫ P_{1+s}(x − σ) ‖F(x − i)‖² dx` for `s > −1`. -/
theorem Fl_sq_le {σ s : ℝ} (hs : -1 < s) :
    ‖Fl ψ (σ + s * I)‖ ^ 2 ≤ ∫ x : ℝ, pk (1 + s) (x - σ) * ‖Fl ψ (x - I)‖ ^ 2 := by
  have hy : 0 < 1 + s := by linarith
  rw [Fl_poisson hm hi hs]
  have hc : Continuous fun x : ℝ => Fl ψ ((σ : ℂ) + x - I) := by
    have := (continuous_Fl_line hm hi).comp (continuous_const.add continuous_id : Continuous fun x : ℝ => σ + x)
    refine this.congr fun x => ?_
    simp only [Function.comp_apply, Pi.add_apply]; congr 1; push_cast; ring
  refine (norm_sq_pk_le hy hc.aestronglyMeasurable (B := ∫ w in Ioi (0 : ℝ), ‖ψ w‖ * Real.exp w)
    (fun x => ?_)).trans (le_of_eq ?_)
  · have := norm_Fl_line_le (ψ := ψ) (σ + x); push_cast at this; ring_nf at this ⊢; exact this
  · have := integral_add_right_eq_self (μ := volume)
      (fun x : ℝ => pk (1 + s) (x - σ) * ‖Fl ψ (x - I)‖ ^ 2) σ
    rw [← this]; congr 1; funext x
    simp only [add_sub_cancel_right]; congr 3; push_cast; ring_nf

end Rep

end Kaiser

#print axioms Kaiser.integral_pk_exp
#print axioms Kaiser.Fl_sq_le
