import Mathlib
import Mollify
import DigammaGauss

/-! # The archimedean term at a general digamma shift (round 226)

Weil's form for an L-function with gamma factor `Γ_ℝ(s + δ)` has archimedean term
`(1/2π)∫ĝ(r)² Re ψ(q + ir/2) dr` with `q = (1 + 2δ)/4`: `q = ¼` for `ζ` and for even characters,
`q = ¾` for odd characters. This file proves, for every `q ≥ ¼` and every probe `g`,

  `(1/2π)∫ĝ(r)² Re ψ(q + ir/2) dr = Re ψ(q)‖g‖² + ∫_0^∞ [f(0) − f(u)] K_q(u) du`   (`arch_termQ`),

`f = autocorr g`, `K_q(u) = e^{(1−2q)u}/sinh u = 2Σ_m e^{−(2m+2q)u}`. This is the kernel `K_{z0}` of
`frontier/dh/dh_gram.py`. The proof is ExplicitBridge.lean's (round 126) with `¼` replaced by `q`:
Gauss's digamma integral (`PilotDigamma.digamma_sub_eq_integral`), Tonelli, and `t = 2u`.
ExplicitBridge.lean now takes its B1 and B2 as the instance `q = ¼`.

Integrability for `q ≥ ¼` comes from the probe's own condition at `q = ¼`: `K_q = K_{1/4}·e^{(½−2q)u}`
and the second factor is at most `1` on `u > 0`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

variable {a q : ℝ} {g : ℝ → ℝ}

/-- `q + ir/2`. -/
def zQ (q r : ℝ) : ℂ := q + Complex.I * r / 2

/-- `Re ψ(q + ir/2)`. -/
def psiReQ (q r : ℝ) : ℝ := (Complex.digamma (zQ q r)).re

/-- The kernel `e^{−qt}/(1 − e^{−t})`. -/
def kkQ (q t : ℝ) : ℝ := Real.exp (-(q * t)) / (1 - Real.exp (-t))

/-- The archimedean kernel `K_q(u) = e^{(1−2q)u}/sinh u`. -/
def archKer (q u : ℝ) : ℝ := Real.exp ((1 - 2 * q) * u) / Real.sinh u

/-- `[f(0) − f(u)] K_q(u)`. -/
def archIntegrandQ (q : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (autocorr g 0 - autocorr g u) * archKer q u

/-- `∫_0^∞ [f(0) − f(u)] K_q(u) du`. -/
def archEQ (q : ℝ) (g : ℝ → ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), archIntegrandQ q g u

/-! ## B1. The digamma difference as a positive-kernel integral -/

theorem kkQ_nonneg (q : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ kkQ q t := by
  unfold kkQ
  have : Real.exp (-t) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  exact div_nonneg (Real.exp_pos _).le (by linarith)

theorem measurable_kkQ (q : ℝ) : Measurable (kkQ q) := by unfold kkQ; fun_prop

theorem kkQ_re (q r t : ℝ) :
    ((cexp (-(zQ q 0 * t)) - cexp (-(zQ q r * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ)).re
      = kkQ q t * (1 - Real.cos (r * (t / 2))) := by
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.exp_re, Complex.exp_re]
  unfold kkQ zQ
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  rw [show r * 2 / 4 * t = r * (t / 2) by ring]
  ring

/-- **B1**: `Re ψ(q + ir/2) − Re ψ(q) = ∫_0^∞ k_q(t)(1 − cos(rt/2)) dt`, integrably, for `q > 0`. -/
theorem psiReQ_sub (hq : 0 < q) (r : ℝ) :
    IntegrableOn (fun t => kkQ q t * (1 - Real.cos (r * (t / 2)))) (Ioi 0) ∧
      psiReQ q r - psiReQ q 0 = ∫ t in Ioi (0 : ℝ), kkQ q t * (1 - Real.cos (r * (t / 2))) := by
  have hz : ∀ s : ℝ, 0 < (zQ q s).re := fun s => by unfold zQ; simpa using hq
  obtain ⟨hI, hE⟩ := PilotDigamma.digamma_sub_eq_integral (hz r) (hz 0)
  have hI' := hI.re
  simp only [RCLike.re_to_complex, PilotDigamma.gaussK, kkQ_re] at hI'
  refine ⟨hI', ?_⟩
  unfold psiReQ
  have h2 := integral_re hI
  simp only [RCLike.re_to_complex, PilotDigamma.gaussK, kkQ_re] at h2
  rw [← Complex.sub_re, hE, h2]
  rfl

/-- The Lévy–Khintchine exponent is nonnegative: `Re ψ(q) ≤ Re ψ(q + ir/2)`. -/
theorem psiReQ_ge (hq : 0 < q) (r : ℝ) : psiReQ q 0 ≤ psiReQ q r := by
  obtain ⟨-, he⟩ := psiReQ_sub hq r
  have : 0 ≤ ∫ t in Ioi (0 : ℝ), kkQ q t * (1 - Real.cos (r * (t / 2))) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (kkQ_nonneg q ht) (by linarith [Real.cos_le_one (r * (t / 2))])
  linarith

/-! ## B2. The archimedean term, by Tonelli and `t = 2u` -/

/-- `2k_q(2u) = K_q(u)`. -/
theorem two_kkQ (q : ℝ) {u : ℝ} (hu : 0 < u) : 2 * kkQ q (2 * u) = archKer q u := by
  unfold kkQ archKer
  rw [Real.sinh_eq]
  have e1 : Real.exp (-(q * (2 * u))) = Real.exp ((1 - 2 * q) * u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (-u) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-u) := Real.exp_pos _
  have h4 : 1 - Real.exp (-u) * Real.exp (-u) ≠ 0 := by nlinarith
  have h5 : (Real.exp u - Real.exp (-u)) / 2 ≠ 0 := by
    have : Real.exp (-u) < Real.exp u := Real.exp_lt_exp.2 (by linarith)
    intro h; linarith
  rw [e1, e2, mul_div_assoc', div_eq_div_iff h4 h5]
  linear_combination (Real.exp ((1 - 2 * q) * u)) * h2

/-- The `t`-integrand after the `r`-integral: `k_q(t)(f(0) − f(t/2))`. -/
def phiAQ (q : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := kkQ q t * (autocorr g 0 - autocorr g (t / 2))

theorem phiAQ_two_mul (q : ℝ) (g : ℝ → ℝ) {u : ℝ} (hu : 0 < u) :
    2 * phiAQ q g (2 * u) = archIntegrandQ q g u := by
  unfold phiAQ archIntegrandQ
  rw [← two_kkQ q hu, show 2 * u / 2 = u by ring]; ring

/-- At `q = ¼` the integrand is ExplicitBridge's `archIntegrand`. -/
theorem archIntegrandQ_quarter : archIntegrandQ (1 / 4) = archIntegrand := by
  funext g u
  unfold archIntegrandQ archKer archIntegrand
  congr 3; ring

theorem archEQ_quarter : archEQ (1 / 4) = archE := by
  funext g; unfold archEQ archE; rw [archIntegrandQ_quarter]

/-- **Integrability for `q ≥ ¼`**, from the probe's condition at `q = ¼`. -/
theorem archIntegrandQ_integrable (hp : Probe a g) (hq : 1 / 4 ≤ q) :
    IntegrableOn (archIntegrandQ q g) (Ioi 0) := by
  have hb : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), ‖Real.exp ((1 / 2 - 2 * q) * u)‖ ≤ 1 := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hu)
  refine (hp.arch.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop)) hb).congr
    (Eventually.of_forall fun u => ?_)
  simp only [archIntegrand, archIntegrandQ, archKer]
  rw [mul_assoc, div_mul_eq_mul_div, ← Real.exp_add]
  congr 3; ring

theorem phiAQ_integrable (hp : Probe a g) (hq : 1 / 4 ≤ q) : IntegrableOn (phiAQ q g) (Ioi 0) := by
  have h : IntegrableOn (fun u => phiAQ q g (2 * u)) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((archIntegrandQ_integrable hp hq).div_const 2) (fun u hu => ?_)
      measurableSet_Ioi
    rw [← phiAQ_two_mul q g hu]; ring
  simpa using (integrableOn_Ioi_comp_mul_left_iff (phiAQ q g) 0 (by norm_num : (0 : ℝ) < 2)).1 h

theorem phiAQ_integral (q : ℝ) (g : ℝ → ℝ) : ∫ t in Ioi (0 : ℝ), phiAQ q g t = archEQ q g := by
  have e := integral_comp_mul_left_Ioi (phiAQ q g) 0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at e
  have e2 : ∫ x in Ioi (0 : ℝ), phiAQ q g (2 * x)
      = (∫ u in Ioi (0 : ℝ), archIntegrandQ q g u) / 2 := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [← phiAQ_two_mul q g hu]; ring
  rw [archEQ]
  linarith

/-- **B2**: `∫ ĝ(r)² (Re ψ(q + ir/2) − Re ψ(q)) dr = 2π·E_q(g)`, integrably, for `q ≥ ¼`. -/
theorem hsq_psiQ_sub (hp : Probe a g) (ha : 0 < a) (hq : 1 / 4 ≤ q) :
    Integrable (fun r => hsq g a r * (psiReQ q r - psiReQ q 0)) ∧
      ∫ r, hsq g a r * (psiReQ q r - psiReQ q 0) = 2 * π * archEQ q g := by
  have hq0 : 0 < q := by linarith
  set ν := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ × ℝ → ℝ := fun p => hsq g a p.1 * (kkQ q p.2 * (1 - Real.cos (p.1 * (p.2 / 2))))
    with hFd
  have hFm : AEStronglyMeasurable F (volume.prod ν) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((continuous_hsq hp.toE).measurable.comp measurable_fst).mul
      (((measurable_kkQ q).comp measurable_snd).mul ?_)
    exact (Continuous.measurable (by fun_prop))
  have e : ∀ t, (fun r => F (r, t))
      = fun r => kkQ q t * (hsq g a r - hsq g a r * Real.cos (r * (t / 2))) := by
    intro t; funext r; simp only [hFd]; ring
  have hinner : ∀ t, ∫ r, F (r, t) = 2 * π * phiAQ q g t := by
    intro t
    rw [e, integral_const_mul, integral_sub (integrable_hsq hp.toE ha)
      (integrable_hsq_cos hp.toE ha _), integral_hsq hp.toE ha, integral_hsq_cos hp.toE ha,
      ← autocorr_zero, phiAQ]
    ring
  have hFint : ∀ t, Integrable (fun r => F (r, t)) := by
    intro t
    rw [e]; exact ((integrable_hsq hp.toE ha).sub (integrable_hsq_cos hp.toE ha _)).const_mul _
  have hFnn : ∀ r, ∀ t, 0 < t → 0 ≤ F (r, t) := fun r t ht =>
    mul_nonneg (hsq_nonneg r)
      (mul_nonneg (kkQ_nonneg q ht) (by linarith [Real.cos_le_one (r * (t / 2))]))
  have hF : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall hFint, ?_⟩
    refine ((phiAQ_integrable hp hq).const_mul (2 * π)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    show 2 * π * phiAQ q g t = ∫ r, ‖F (r, t)‖
    rw [← hinner t]
    congr 1; funext r
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn r t ht)]
  have hG : ∀ r, ∫ t, F (r, t) ∂ν = hsq g a r * (psiReQ q r - psiReQ q 0) := by
    intro r
    simp only [hFd, ν]
    rw [integral_const_mul, (psiReQ_sub hq0 r).2]
  have hGi := hF.integral_prod_left
  simp only [hG] at hGi
  refine ⟨hGi, ?_⟩
  calc ∫ r, hsq g a r * (psiReQ q r - psiReQ q 0) = ∫ r, ∫ t, F (r, t) ∂ν := by simp only [hG]
    _ = ∫ t, (∫ r, F (r, t)) ∂ν := integral_integral_swap (f := fun r t => F (r, t)) hF
    _ = ∫ t in Ioi (0 : ℝ), 2 * π * phiAQ q g t := by simp only [hinner, ν]
    _ = 2 * π * archEQ q g := by rw [integral_const_mul, phiAQ_integral q g]

theorem integrable_hsq_psiQ (hp : Probe a g) (ha : 0 < a) (hq : 1 / 4 ≤ q) :
    Integrable (fun r => hsq g a r * psiReQ q r) := by
  obtain ⟨hi, -⟩ := hsq_psiQ_sub hp ha hq
  refine (hi.add ((integrable_hsq hp.toE ha).const_mul (psiReQ q 0))).congr
    (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply]; ring

/-- **The archimedean term at shift `q ≥ ¼`**:
`(1/2π)∫ ĝ² Re ψ(q + ir/2) = Re ψ(q)‖g‖² + ∫_0^∞ [f(0) − f(u)] e^{(1−2q)u}/sinh u du`. -/
theorem arch_termQ (hp : Probe a g) (ha : 0 < a) (hq : 1 / 4 ≤ q) :
    1 / (2 * π) * ∫ r, hsq g a r * psiReQ q r = psiReQ q 0 * normSq g + archEQ q g := by
  obtain ⟨hi, he⟩ := hsq_psiQ_sub hp ha hq
  have e : (fun r => hsq g a r * psiReQ q r)
      = fun r => hsq g a r * (psiReQ q r - psiReQ q 0) + psiReQ q 0 * hsq g a r := by
    funext r; ring
  rw [e, integral_add hi ((integrable_hsq hp.toE ha).const_mul _), he, integral_const_mul,
    integral_hsq hp.toE ha]
  field_simp
  ring

theorem psiReQ_zero (q : ℝ) : psiReQ q 0 = (Complex.digamma q).re := by unfold psiReQ zQ; simp

end Pilot1ca

#print axioms Pilot1ca.psiReQ_sub
#print axioms Pilot1ca.psiReQ_ge
#print axioms Pilot1ca.archIntegrandQ_integrable
#print axioms Pilot1ca.hsq_psiQ_sub
#print axioms Pilot1ca.arch_termQ
