import Mathlib
import KaiserZeroWeight

/-! # A regularised Plancherel inequality (round 164, part 3)

For `Ψ ∈ L¹ ∩ L²(ℝ)` and `F(x) = ∫ Ψ(w) e^{ixw} dw`:
`∫ ‖F(x)‖² e^{−bx²} dx ≤ 2π ∫ ‖Ψ‖²` for every `b > 0`.
Expand `‖F‖²` as a double integral, integrate the Gaussian first (`fourierIntegral_gaussian`),
and apply Schur's test to the kernel `k(u) = √(π/b) e^{−u²/4b}`, whose integral is `2π`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

/-- `F(x) = ∫ Ψ(w) e^{ixw} dw`. -/
def FT (Ψ : ℝ → ℂ) (x : ℝ) : ℂ := ∫ w, Ψ w * Complex.exp (I * x * w)

/-- The Gaussian kernel `k(u) = √(π/b) e^{−u²/(4b)}`. -/
def gk (b u : ℝ) : ℝ := Real.sqrt (π / b) * Real.exp (-(u ^ 2 / (4 * b)))

theorem gk_nonneg (b u : ℝ) : 0 ≤ gk b u := by unfold gk; positivity

theorem integrable_gk {b : ℝ} (hb : 0 < b) : Integrable (gk b) := by
  have := (integrable_exp_neg_mul_sq (b := 1 / (4 * b)) (by positivity)).const_mul (Real.sqrt (π / b))
  refine this.congr (ae_of_all _ fun u => ?_)
  simp only [gk]; congr 2; ring

theorem integral_gk {b : ℝ} (hb : 0 < b) : ∫ u, gk b u = 2 * π := by
  have e : (fun u => gk b u) = fun u => Real.sqrt (π / b) * Real.exp (-(1 / (4 * b)) * u ^ 2) := by
    funext u; simp only [gk]; congr 2; ring
  rw [e, integral_const_mul, integral_gaussian, ← Real.sqrt_mul (by positivity)]
  have : π / b * (π / (1 / (4 * b))) = (2 * π) ^ 2 := by field_simp; ring
  rw [this, Real.sqrt_sq (by positivity)]

/-- The Gaussian's Fourier transform, as used here. -/
theorem integral_gauss_exp {b : ℝ} (hb : 0 < b) (u : ℝ) :
    ∫ x : ℝ, Complex.exp (I * x * u) * (Real.exp (-(b * x ^ 2)) : ℂ) = gk b u := by
  have h := fourierIntegral_gaussian (b := (b : ℂ)) (by simpa using hb) (u : ℂ)
  have e1 : ∀ x : ℝ, Complex.exp (I * x * u) * (Real.exp (-(b * x ^ 2)) : ℂ) =
      Complex.exp (I * u * x) * Complex.exp (-(b : ℂ) * x ^ 2) := by
    intro x; rw [Complex.ofReal_exp]; push_cast; ring_nf
  simp_rw [e1, h]
  have e2 : ((π : ℂ) / b) ^ (1 / 2 : ℂ) = (Real.sqrt (π / b) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf
  rw [e2, gk]; push_cast
  congr 2; ring

section Planch

variable {Ψ : ℝ → ℂ} (h1 : Integrable Ψ) (h2 : Integrable fun w => ‖Ψ w‖ ^ 2)
include h1

omit h1 in
theorem normsq_FT (x : ℝ) :
    ‖FT Ψ x‖ ^ 2 = (∫ z : ℝ × ℝ, Ψ z.1 * (starRingEnd ℂ) (Ψ z.2) * Complex.exp (I * x * (z.1 - z.2))).re := by
  have hc : (starRingEnd ℂ) (FT Ψ x) = ∫ w, (starRingEnd ℂ) (Ψ w) * Complex.exp (-(I * x * w)) := by
    rw [FT, ← integral_conj]; congr 1; funext w
    rw [map_mul, ← Complex.exp_conj]; congr 2; simp [Complex.conj_ofReal]
  have hm : FT Ψ x * (starRingEnd ℂ) (FT Ψ x) =
      ∫ z : ℝ × ℝ, Ψ z.1 * (starRingEnd ℂ) (Ψ z.2) * Complex.exp (I * x * (z.1 - z.2)) := by
    rw [hc, FT, ← integral_prod_mul]
    congr 1; funext z
    rw [show I * x * (z.1 - z.2 : ℂ) = I * x * z.1 + -(I * x * z.2) by ring, Complex.exp_add]
    ring
  rw [← hm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

omit h1 in
theorem gk_symm (b u v : ℝ) : gk b (u - v) = gk b (v - u) := by
  unfold gk; congr 3; ring

include h2 in
/-- **Schur's test**: `∫∫ ‖Ψ(w)‖‖Ψ(w′)‖ k(w − w′) ≤ 2π ∫ ‖Ψ‖²`. -/
theorem schur_gk {b : ℝ} (hb : 0 < b) :
    ∫ z : ℝ × ℝ, ‖Ψ z.1‖ * ‖Ψ z.2‖ * gk b (z.1 - z.2) ∂(volume.prod volume) ≤ 2 * π * ∫ w, ‖Ψ w‖ ^ 2 := by
  set f : ℝ → ℝ := fun w => ‖Ψ w‖ ^ 2
  have iA : Integrable (fun p : ℝ × ℝ => f p.2 * gk b (p.1 - p.2)) (volume.prod volume) :=
    h2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (integrable_gk hb)
  have iB : Integrable (fun p : ℝ × ℝ => f p.1 * gk b (p.1 - p.2)) (volume.prod volume) := by
    have := iA.swap
    refine this.congr (ae_of_all _ fun p => ?_)
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]; rw [gk_symm b p.2 p.1]
  have hA : ∫ p : ℝ × ℝ, f p.2 * gk b (p.1 - p.2) ∂(volume.prod volume) = 2 * π * ∫ w, f w := by
    rw [integral_prod_symm _ iA]
    simp_rw [integral_const_mul, integral_sub_right_eq_self (fun u => gk b u), integral_gk hb]
    rw [integral_mul_const, mul_comm]
  have hB : ∫ p : ℝ × ℝ, f p.1 * gk b (p.1 - p.2) ∂(volume.prod volume) = 2 * π * ∫ w, f w := by
    rw [← hA, ← integral_prod_swap]
    congr 1; funext p; simp only [Prod.fst_swap, Prod.snd_swap]; rw [gk_symm b p.2 p.1]
  have hle : ∀ p : ℝ × ℝ, ‖Ψ p.1‖ * ‖Ψ p.2‖ * gk b (p.1 - p.2) ≤
      (1 / 2) * (f p.1 * gk b (p.1 - p.2)) + (1 / 2) * (f p.2 * gk b (p.1 - p.2)) := by
    intro p
    have := gk_nonneg b (p.1 - p.2)
    have h := two_mul_le_add_sq ‖Ψ p.1‖ ‖Ψ p.2‖
    simp only [f]; nlinarith
  have iC : Integrable (fun p : ℝ × ℝ => (1 / 2) * (f p.1 * gk b (p.1 - p.2)) + (1 / 2) * (f p.2 * gk b (p.1 - p.2)))
      (volume.prod volume) := (iB.const_mul _).add (iA.const_mul _)
  have iD : Integrable (fun p : ℝ × ℝ => ‖Ψ p.1‖ * ‖Ψ p.2‖ * gk b (p.1 - p.2)) (volume.prod volume) := by
    refine iC.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((h1.norm.aestronglyMeasurable.comp_fst.mul h1.norm.aestronglyMeasurable.comp_snd).mul
        ((integrable_gk hb).aestronglyMeasurable.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub volume volume)))
    · rw [Real.norm_of_nonneg (by have := gk_nonneg b (p.1 - p.2); positivity)]; exact hle p
  calc _ ≤ ∫ p : ℝ × ℝ, ((1 / 2) * (f p.1 * gk b (p.1 - p.2)) + (1 / 2) * (f p.2 * gk b (p.1 - p.2)))
          ∂(volume.prod volume) :=
        integral_mono iD iC hle
    _ = 2 * π * ∫ w, f w := by
        rw [integral_add (iB.const_mul _) (iA.const_mul _), integral_const_mul, integral_const_mul, hA, hB]
        ring

include h2 in
/-- **Regularised Plancherel**: `∫ ‖F(x)‖² e^{−bx²} dx ≤ 2π ∫ ‖Ψ‖²`. -/
theorem FT_gauss_le {b : ℝ} (hb : 0 < b) :
    ∫ x, ‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2)) ≤ 2 * π * ∫ w, ‖Ψ w‖ ^ 2 := by
  set Φ : ℝ → ℝ × ℝ → ℂ := fun x z => (Real.exp (-(b * x ^ 2)) : ℂ) *
    (Ψ z.1 * (starRingEnd ℂ) (Ψ z.2) * Complex.exp (I * x * (z.1 - z.2)))
  have hΦ : Integrable (Function.uncurry Φ) (volume.prod (volume.prod volume)) := by
    have hd := (integrable_exp_neg_mul_sq hb).mul_prod (h1.norm.mul_prod h1.norm)
    refine hd.mono' ?_ (ae_of_all _ fun p => ?_)
    · have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Ψ p.2.1) (volume.prod (volume.prod volume)) :=
        h1.aestronglyMeasurable.comp_fst.comp_snd
      have m2 : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => (starRingEnd ℂ) (Ψ p.2.2))
          (volume.prod (volume.prod volume)) :=
        (Complex.continuous_conj.comp_aestronglyMeasurable h1.aestronglyMeasurable).comp_snd.comp_snd
      have m0 : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => (Real.exp (-(b * p.1 ^ 2)) : ℂ))
          (volume.prod (volume.prod volume)) := Continuous.aestronglyMeasurable (by fun_prop)
      have m3 : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Complex.exp (I * p.1 * (p.2.1 - p.2.2)))
          (volume.prod (volume.prod volume)) := Continuous.aestronglyMeasurable (by fun_prop)
      exact m0.mul ((m1.mul m2).mul m3)
    · simp only [Function.uncurry, Φ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_conj, Complex.norm_exp]
      apply le_of_eq
      have : (I * (p.1 : ℂ) * ((p.2.1 : ℂ) - p.2.2)).re = 0 := by simp
      rw [this, Real.exp_zero, mul_one, neg_mul]
  -- `‖F(x)‖² e^{−bx²} = Re ∫ Φ(x, ·)`
  have e1 : ∀ x : ℝ, ‖FT Ψ x‖ ^ 2 * Real.exp (-(b * x ^ 2)) = (∫ z, Φ x z).re := by
    intro x
    rw [normsq_FT, integral_const_mul, re_ofReal_mul, mul_comm]
  simp_rw [e1]
  rw [Measure.volume_eq_prod]
  have h3 := integral_re (hΦ.integral_prod_left)
  simp only [RCLike.re_to_complex, Function.uncurry_apply_pair] at h3
  rw [h3, integral_integral_swap hΦ]
  -- the Gaussian integral in `x`
  have e2 : ∀ z : ℝ × ℝ, ∫ x, Φ x z = Ψ z.1 * (starRingEnd ℂ) (Ψ z.2) * gk b (z.1 - z.2) := by
    intro z
    have : ∀ x : ℝ, Φ x z = Ψ z.1 * (starRingEnd ℂ) (Ψ z.2) *
        (Complex.exp (I * x * ((z.1 - z.2 : ℝ) : ℂ)) * (Real.exp (-(b * x ^ 2)) : ℂ)) := by
      intro x; simp only [Φ]; push_cast; ring
    simp_rw [this]; rw [integral_const_mul, integral_gauss_exp hb]
  simp_rw [e2]
  refine (Complex.re_le_norm _).trans ((norm_integral_le_integral_norm _).trans ?_)
  refine le_trans (le_of_eq ?_) (schur_gk h1 h2 hb)
  congr 1; funext z
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (gk_nonneg _ _)]

end Planch

end Kaiser

#print axioms Kaiser.FT_gauss_le
