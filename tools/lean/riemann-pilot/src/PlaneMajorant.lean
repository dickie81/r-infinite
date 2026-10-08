import Mathlib

/-! # A radial majorant with compactly supported Fourier transform (round 301)

S4 of round 291's plan, part 1. The companion paper's proof of its Proposition 4.5 starts by bounding
the sum over `0 < N(u) ≤ H` by a smoothed sum `Σ_u Φ(u/√H)·|A_u|²`, with a weight `Φ ≥ 0` that is
`≥ 1` on the unit disc and whose Fourier transform has compact support, so that the dual sum after
Poisson summation is finite. This file constructs such a `Φ` on `ℂ`.

* **The bump** `η(z) = s(1 − 64|z|²)` (`etaR`, `eta`), for Mathlib's smooth transition `s`: smooth,
  real, nonnegative, radial, even, supported in `|z| ≤ 1/8`, with `∫η > 0` (`integral_etaR_pos`).
* **`𝓕η` is real** (`fourier_eta_im`), since `η` is real and even, and **`Re 𝓕η(ξ) ≥ (∫η)/2` for
  `|ξ| ≤ 1`** (`fourier_eta_re_ge`): on the support of `η`, `|⟨v, ξ⟩| ≤ 1/8`, so
  `cos(2π⟨v, ξ⟩) ≥ 1 − π²/32 ≥ 1/2`.
* **The majorant** `Φ = c·𝓕(η ⋆ η)` with `c = 4/(∫η)²` (`Phi`). By Mathlib's convolution theorem,
  `Φ(ξ) = c·(𝓕η(ξ))²` (`Phi_apply`). So `Φ` is real (`Phi_im`), `Φ ≥ 0` (`Phi_re_nonneg`), and
  **`Φ ≥ 1` on the unit disc** (`one_le_Phi_re`).
* **`𝓕Φ(x) = c·(η ⋆ η)(−x)`** by Fourier inversion (`fourier_Phi`), so **`𝓕Φ` vanishes outside a
  disc** (`exists_fourier_Phi_eq_zero`).
* **Radial**: `Φ(uξ) = Φ(ξ)` and `𝓕Φ(ux) = 𝓕Φ(x)` for `|u| = 1` (`Phi_rot`, `fourier_Phi_rot`), by
  Mathlib's `fourier_comp_linearIsometry` for rotations.
-/

open Complex MeasureTheory
open scoped FourierTransform ComplexConjugate RealInnerProductSpace ContDiff SchwartzMap Convolution

noncomputable section

namespace Majorant

/-- The radial bump `η(z) = s(1 − 64|z|²)`, supported in `|z| ≤ 1/8`. -/
def etaR (z : ℂ) : ℝ := Real.smoothTransition (1 - 64 * ‖z‖ ^ 2)

def etaF (z : ℂ) : ℂ := (etaR z : ℂ)

theorem etaR_contDiff : ContDiff ℝ ∞ etaR :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem etaF_contDiff : ContDiff ℝ ∞ etaF :=
  ofRealCLM.contDiff.comp etaR_contDiff

theorem etaR_eq_zero {z : ℂ} (hz : 1 / 8 < ‖z‖) : etaR z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : (1 / 8 : ℝ) ^ 2 < ‖z‖ ^ 2 := by gcongr
  nlinarith

theorem etaF_support : HasCompactSupport etaF := by
  refine HasCompactSupport.intro (isCompact_closedBall 0 (1 / 8)) fun z hz => ?_
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  simp [etaF, etaR_eq_zero hz]

theorem etaR_nonneg (z : ℂ) : 0 ≤ etaR z := Real.smoothTransition.nonneg _

theorem etaR_neg (z : ℂ) : etaR (-z) = etaR z := by simp [etaR]

theorem etaR_rot (u z : ℂ) (hu : ‖u‖ = 1) : etaR (u * z) = etaR z := by
  simp [etaR, hu]

/-- `η` as a Schwartz function. -/
def eta : 𝓢(ℂ, ℂ) := etaF_support.toSchwartzMap etaF_contDiff

theorem eta_apply (z : ℂ) : eta z = (etaR z : ℂ) := rfl

theorem etaR_integrable : Integrable etaR := by
  have h : Integrable (fun z => ‖eta z‖) := eta.integrable.norm
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp [eta_apply, Complex.norm_real, abs_of_nonneg (etaR_nonneg z)]

theorem integral_etaR_pos : 0 < ∫ z, etaR z := by
  have hc : Continuous etaR := etaR_contDiff.continuous
  have hs : HasCompactSupport etaR := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 (1 / 8)) fun z hz => ?_
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact etaR_eq_zero hz
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs etaR_nonneg (x := 0) ?_
  simp [etaR, Real.smoothTransition.one_of_one_le]

theorem conj_fourierChar_neg (a : ℝ) : conj ((𝐞 (-a) : Circle) : ℂ) = (𝐞 a : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-- `𝓕η` is real: `η` is real and even. -/
theorem fourier_eta_im (ξ : ℂ) : (𝓕 (eta : ℂ → ℂ) ξ).im = 0 := by
  have hconj : conj (𝓕 (eta : ℂ → ℂ) ξ) = 𝓕 (eta : ℂ → ℂ) ξ := by
    rw [Real.fourier_eq, ← integral_conj]
    have h : ∀ x : ℂ, conj (𝐞 (-⟪x, ξ⟫) • eta x) = (fun v : ℂ => 𝐞 (-⟪v, ξ⟫) • eta v) (-x) := by
      intro x
      simp only [Circle.smul_def, smul_eq_mul, map_mul, eta_apply, Complex.conj_ofReal, etaR_neg,
        inner_neg_left, neg_neg, conj_fourierChar_neg]
    simp_rw [h]
    exact integral_neg_eq_self (fun v : ℂ => 𝐞 (-⟪v, ξ⟫) • eta v) volume
  have := congrArg Complex.im hconj
  rw [Complex.conj_im] at this
  linarith

/-- `Re(e(−⟨v, ξ⟩)·η(v)) = η(v)·cos(2π⟨v, ξ⟩)`. -/
theorem re_integrand (v ξ : ℂ) :
    (𝐞 (-⟪v, ξ⟫) • eta v).re = etaR v * Real.cos (2 * Real.pi * ⟪v, ξ⟫) := by
  rw [Circle.smul_def, smul_eq_mul, eta_apply, Real.fourierChar_apply, Complex.re_mul_ofReal,
    exp_ofReal_mul_I_re, mul_comm]
  congr 1
  rw [show 2 * Real.pi * -⟪v, ξ⟫ = -(2 * Real.pi * ⟪v, ξ⟫) by ring, Real.cos_neg]

/-- **On the unit disc `𝓕η` is at least half its value at `0`**: `Re 𝓕η(ξ) ≥ (∫η)/2` for `|ξ| ≤ 1`. -/
theorem fourier_eta_re_ge (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1) : (∫ z, etaR z) / 2 ≤ (𝓕 (eta : ℂ → ℂ) ξ).re := by
  have hint : Integrable (fun v : ℂ => 𝐞 (-⟪v, ξ⟫) • eta v) :=
    (Real.fourierIntegral_convergent_iff ξ).2 eta.integrable
  have e := integral_re hint
  simp only [RCLike.re_to_complex] at e
  rw [Real.fourier_eq, ← e, ← integral_div]
  refine integral_mono (etaR_integrable.div_const 2) hint.re fun v => ?_
  simp only
  rw [re_integrand]
  by_cases hv : ‖v‖ ≤ 1 / 8
  · have hin : |⟪v, ξ⟫| ≤ 1 / 8 := by
      calc |⟪v, ξ⟫| ≤ ‖v‖ * ‖ξ‖ := abs_real_inner_le_norm v ξ
        _ ≤ 1 / 8 * 1 := by gcongr
        _ = 1 / 8 := by ring
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * ⟪v, ξ⟫)
    have hsq : (2 * Real.pi * ⟪v, ξ⟫) ^ 2 ≤ (2 * 3.15 * (1 / 8)) ^ 2 := by
      have hab := abs_le.1 hin
      have h0 : 0 < Real.pi := Real.pi_pos
      apply sq_le_sq' <;> nlinarith [hab.1, hab.2]
    have hc : 1 / 2 ≤ Real.cos (2 * Real.pi * ⟪v, ξ⟫) := by nlinarith
    nlinarith [etaR_nonneg v]
  · rw [etaR_eq_zero (lt_of_not_ge hv)]; simp

/-- `ψ = η ⋆ η`. -/
def psi : 𝓢(ℂ, ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) eta eta

/-- The normalizing constant `c = 4/(∫η)²`. -/
def cPhi : ℝ := 4 / (∫ z, etaR z) ^ 2

/-- **The majorant** `Φ = c·𝓕ψ`. -/
def Phi : 𝓢(ℂ, ℂ) := (cPhi : ℂ) • 𝓕 psi

theorem Phi_apply (ξ : ℂ) : Phi ξ = (cPhi : ℂ) * (𝓕 (eta : ℂ → ℂ) ξ) ^ 2 := by
  rw [Phi, smul_apply, psi, SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, smul_eq_mul, ContinuousLinearMap.mul_apply', sq,
    SchwartzMap.fourier_coe]

theorem fourier_eta_eq_re (ξ : ℂ) : 𝓕 (eta : ℂ → ℂ) ξ = ((𝓕 (eta : ℂ → ℂ) ξ).re : ℂ) :=
  Complex.ext (by simp) (by simp [fourier_eta_im])

/-- `Φ` is real: `Φ(ξ) = c·(Re 𝓕η(ξ))²`. -/
theorem Phi_eq_real (ξ : ℂ) : Phi ξ = ((cPhi * ((𝓕 (eta : ℂ → ℂ) ξ).re) ^ 2 : ℝ) : ℂ) := by
  rw [Phi_apply]; nth_rewrite 1 [fourier_eta_eq_re]; push_cast; ring

theorem cPhi_pos : 0 < cPhi := by have := integral_etaR_pos; unfold cPhi; positivity

theorem Phi_im (ξ : ℂ) : (Phi ξ).im = 0 := by rw [Phi_eq_real, Complex.ofReal_im]

theorem Phi_re_nonneg (ξ : ℂ) : 0 ≤ (Phi ξ).re := by
  rw [Phi_eq_real, Complex.ofReal_re]; have := cPhi_pos; positivity

/-- **`Φ ≥ 1` on the unit disc.** -/
theorem one_le_Phi_re (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1) : 1 ≤ (Phi ξ).re := by
  rw [Phi_eq_real, Complex.ofReal_re]
  have hI := integral_etaR_pos
  have h := fourier_eta_re_ge ξ hξ
  have hsq : ((∫ z, etaR z) / 2) ^ 2 ≤ ((𝓕 (eta : ℂ → ℂ) ξ).re) ^ 2 := by
    gcongr
  calc (1 : ℝ) = cPhi * ((∫ z, etaR z) / 2) ^ 2 := by unfold cPhi; field_simp; norm_num
    _ ≤ cPhi * ((𝓕 (eta : ℂ → ℂ) ξ).re) ^ 2 := by gcongr; exact cPhi_pos.le

/-- **`𝓕Φ(x) = c·ψ(−x)`**: Fourier inversion. -/
theorem fourier_Phi (x : ℂ) : 𝓕 (Phi : ℂ → ℂ) x = (cPhi : ℂ) * psi (-x) := by
  have h1 : 𝓕⁻ (𝓕 psi) = psi := FourierPair.fourierInv_fourier_eq psi
  have h2 : psi (-x) = 𝓕 (𝓕 psi) x := by
    conv_lhs => rw [← h1]
    rw [SchwartzMap.fourierInv_apply_eq]
    simp
  rw [h2, ← SchwartzMap.fourier_coe, Phi, FourierTransform.fourier_smul, smul_apply,
    smul_eq_mul]

theorem psi_support : HasCompactSupport (psi : ℂ → ℂ) := by
  have h : (psi : ℂ → ℂ) = (eta : ℂ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (eta : ℂ → ℂ) := by
    funext x; exact SchwartzMap.convolution_apply _ eta eta x
  rw [h]
  exact etaF_support.convolution _ etaF_support

/-- **`𝓕Φ` has compact support.** -/
theorem exists_fourier_Phi_eq_zero : ∃ R : ℝ, 0 < R ∧ ∀ x : ℂ, R ≤ ‖x‖ → 𝓕 (Phi : ℂ → ℂ) x = 0 := by
  obtain ⟨R, hR⟩ := psi_support.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0 + 1, by positivity, fun x hx => ?_⟩
  rw [fourier_Phi]
  have : -x ∉ tsupport (psi : ℂ → ℂ) := by
    intro hmem
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg] at this
    have := le_max_left R 0
    linarith
  rw [image_eq_zero_of_notMem_tsupport this, mul_zero]

theorem eta_comp_rotation (u : Circle) : (eta : ℂ → ℂ) ∘ rotation u = eta := by
  funext z
  simp only [Function.comp_apply, rotation_apply, eta_apply, etaR_rot _ _ (Circle.norm_coe u)]

/-- `𝓕η` is radial. -/
theorem fourier_eta_rot (u : Circle) (ξ : ℂ) :
    𝓕 (eta : ℂ → ℂ) ((u : ℂ) * ξ) = 𝓕 (eta : ℂ → ℂ) ξ := by
  have h := Real.fourier_comp_linearIsometry (rotation u) (eta : ℂ → ℂ) ξ
  rw [eta_comp_rotation, rotation_apply] at h
  exact h.symm

/-- **`Φ` is radial.** -/
theorem Phi_rot (u : Circle) (ξ : ℂ) : Phi ((u : ℂ) * ξ) = Phi ξ := by
  rw [Phi_apply, Phi_apply, fourier_eta_rot]

/-- **`𝓕Φ` is radial.** -/
theorem fourier_Phi_rot (u : Circle) (x : ℂ) :
    𝓕 (Phi : ℂ → ℂ) ((u : ℂ) * x) = 𝓕 (Phi : ℂ → ℂ) x := by
  have hc : (Phi : ℂ → ℂ) ∘ rotation u = Phi := by
    funext z; simp only [Function.comp_apply, rotation_apply, Phi_rot]
  have h := Real.fourier_comp_linearIsometry (rotation u) (Phi : ℂ → ℂ) x
  rw [hc, rotation_apply] at h
  exact h.symm

end Majorant

end

#print axioms Majorant.integral_etaR_pos
#print axioms Majorant.fourier_eta_im
#print axioms Majorant.fourier_eta_re_ge
#print axioms Majorant.Phi_apply
#print axioms Majorant.Phi_im
#print axioms Majorant.Phi_re_nonneg
#print axioms Majorant.one_le_Phi_re
#print axioms Majorant.fourier_Phi
#print axioms Majorant.exists_fourier_Phi_eq_zero
#print axioms Majorant.Phi_rot
#print axioms Majorant.fourier_Phi_rot
