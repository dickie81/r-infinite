import Mathlib
import DHExplicit
import ArchShift

/-! # Weil's form for the Davenport–Heilbronn function in u-space (round 258)

Round 257's explicit formula is stated for the scaled function `Ξ₃(t) = Ξ_dh(3t)`, so its probe
form `QDH a g = weilRHSDH (hsq g a)` is Weil's form of the scaled probe. This file undoes the scaling
on the test-function side: with `h(z) = ĝ(3z)²` (a strip test function at width 1 exactly when `ĝ²`
is one at width 3) the right-hand side collapses, by `g_{h(3·)}(u) = ⅓ g_h(u/3)` (`gh_comp_three`),
`Re ψ(3/4 + 3ir/2) = ψ_{3/4}(3r)` (`psiRe3_eq`) and round 226's `arch_termQ` at `q = ¾`, to the
u-space form

  `Q_dh(g) = (Re ψ(¾) + log(5/π))‖g‖² + ∫_0^∞ [f(0) − f(u)] e^{−u/2}/sinh u du − 2 Σ c(n) n^{−1/2} f(log n)`

(`QDHu`, `f = autocorr g`; `weilRHSDH_scaled`). This is `QCu` of round 226 with `N = 5`, the odd
shift `q = ¾`, and `c(n)` in place of `Λ(n)χ(n)`: the form `frontier/dh/dh_gram.py` and `cert.py`
evaluate in ball arithmetic (round 165). **`QDHu_hasSum`**: `Q_dh(g) = Σ_u 2ĝ(3τ_u)²` over the zeros
`½ ± 3iτ_u` of `dh`; `QDHu_nonneg_of_DHRH`; **`exists_offline_dh_of_neg_u`**: `Q_dh(g) < 0` for one
probe whose `ĝ(3·)²` is a strip test function gives a zero of `dh` with `Re s > 0`, `Re s ≠ ½`.

For even, nonnegative profiles non-increasing on `[0, a]` the strip test at width 3 is automatic
(`striptest_antitone3`, from `norm_ghatC_le_of_antitone` with `cosh(3a)` and the bound
`‖ĝ(z)‖ ≤ e^{a|Im z|}∫|g|`, `norm_ghatC_le_exp_im`), so **`exists_offline_dh_of_neg_antitone`** and
**`exists_offline_dh_of_neg_box`** (`Q_dh(box a) < 0` for one `a > 0`) need no strip hypothesis.
A kernel-checked off-line zero of `dh` is now one verified real inequality away: `QDHu g < 0` for an
explicit `g`, whose ingredients are the finitely many `c(n)` with `log n ≤ 2a` (`f(log n) = 0`
beyond the support of the autocorrelation), `Re ψ(¾)`, and the elementary integral `E_{3/4}(g)`.
-/

open Real Complex DirichletCharacter Filter Topology MeasureTheory Set

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

variable {a : ℝ} {g : ℝ → ℝ}

/-! ## Scaling identities -/

/-- `g_{h(3·)}(u) = ⅓ g_h(u/3)`. -/
theorem gh_comp_three (hR : ℝ → ℝ) (u : ℝ) :
    gh (fun r => hR (3 * r)) u = 1 / 3 * gh hR (u / 3) := by
  unfold gh
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun v : ℝ => hR v * Real.cos (v * (u / 3))) 3
  simp only [smul_eq_mul] at h
  have e : (fun r : ℝ => hR (3 * r) * Real.cos (r * u))
      = fun r => hR (3 * r) * Real.cos (3 * r * (u / 3)) := by
    funext r; congr 2; ring
  rw [e, h, abs_of_pos (by norm_num : (0 : ℝ) < 3⁻¹)]
  ring

theorem psiRe3_eq (r : ℝ) : psiRe3 r = psiReQ (3 / 4) (3 * r) := by
  unfold psiRe3 psiReQ zC3 zQ; congr 2; push_cast; ring

theorem integral_hsq_psiRe3 (g : ℝ → ℝ) (a : ℝ) :
    ∫ r, hsq g a (3 * r) * psiRe3 r = 1 / 3 * ∫ v, hsq g a v * psiReQ (3 / 4) v := by
  simp_rw [psiRe3_eq]
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun v : ℝ => hsq g a v * psiReQ (3 / 4) v) 3
  simp only [smul_eq_mul] at h
  rw [h, abs_of_pos (by norm_num : (0 : ℝ) < 3⁻¹)]
  ring

/-! ## Weil's form for `dh` in u-space -/

/-- **Weil's form for `dh` in u-space**: `Q_dh(g) = (Re ψ(¾) + log(5/π))‖g‖² + E_{3/4}(g)
− 2 Σ c(n) n^{−1/2} f(log n)`, `f = autocorr g`, `E_{3/4}(g) = ∫_0^∞ [f(0) − f(u)] e^{−u/2}/sinh u du`.
No zero of `dh` enters. -/
def QDHu (g : ℝ → ℝ) : ℝ :=
  ((Complex.digamma (3 / 4 : ℂ)).re + Real.log 5 - Real.log π) * normSq g + archEQ (3 / 4) g
    - 2 * ∑' n : ℕ, fDH n / Real.sqrt n * autocorr g (Real.log n)

/-- The scaled right-hand side at `h = ĝ(3·)²` is the u-space form of `g`. -/
theorem weilRHSDH_scaled (hp : Probe a g) (ha : 0 < a) :
    weilRHSDH (fun r => hsq g a (3 * r)) = QDHu g := by
  unfold weilRHSDH QDHu
  simp_rw [gh_comp_three]
  rw [integral_hsq_psiRe3]
  have harch := arch_termQ hp ha (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)
  rw [psiReQ_zero, show ((3 / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) by push_cast; ring] at harch
  simp only [gh_hsq hp.toE ha, autocorr_zero, zero_div]
  have hlog : ∀ n : ℕ, 3 * Real.log n / 3 = Real.log n := fun n => by ring
  simp_rw [hlog]
  have hsum : ∑' n : ℕ, fDH n / Real.sqrt n * (1 / 3 * autocorr g (Real.log n))
      = 1 / 3 * ∑' n : ℕ, fDH n / Real.sqrt n * autocorr g (Real.log n) := by
    rw [← tsum_mul_left]; exact tsum_congr fun n => by ring
  rw [hsum]
  linear_combination harch

/-- **The explicit formula for a probe, unscaled**: `Q_dh(g) = Σ_u 2ĝ(3τ_u)²`, where `½ ± 3iτ_u`
are the zeros of `dh` with `Re s > 0`. -/
theorem QDHu_hasSum (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a (3 * z) ^ 2) K) :
    HasSum (fun i : ZeroIdx (sqF XiDH3) => 2 * ghatC g a (3 * tau3 i) ^ 2) (QDHu g : ℂ) := by
  have heven : ∀ t : ℂ, ghatC g a (3 * -t) ^ 2 = ghatC g a (3 * t) ^ 2 := fun t => by
    rw [mul_neg]; exact even_ghat_sq hp.even a (3 * t)
  have hreal : ∀ r : ℝ, ghatC g a (3 * (r : ℂ)) ^ 2 = ((hsq g a (3 * r) : ℝ) : ℂ) := fun r => by
    rw [show (3 : ℂ) * (r : ℂ) = ((3 * r : ℝ) : ℂ) by push_cast; ring]
    exact hsq_ofReal hp ha.le (3 * r)
  have h := weil_XiDH3 hK heven hreal
  rwa [weilRHSDH_scaled hp ha] at h

/-- **`DHRH ⟹ Q_dh ≥ 0`**. -/
theorem QDHu_nonneg_of_DHRH (hRH : DHRH) (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a (3 * z) ^ 2) K) : 0 ≤ QDHu g := by
  have h := (QDHu_hasSum hp ha hK).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, ofReal_re] at h
  refine h.nonneg fun i => ?_
  have hi := tau3_real_of_DHRH hRH i
  have e : (3 : ℂ) * tau3 i = ((3 * (tau3 i).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
  rw [e, hsq_ofReal hp ha.le]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (by norm_num) (hsq_nonneg _)

/-- **A negative u-space Weil form certifies an off-line zero of `dh`.** -/
theorem exists_offline_dh_of_neg_u (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a (3 * z) ^ 2) K) (hneg : QDHu g < 0) :
    ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 := by
  by_contra hcon
  push Not at hcon
  exact absurd (QDHu_nonneg_of_DHRH (fun s hs h0 => hcon s hs h0) hp ha hK) (not_le.2 hneg)

/-! ## The strip test at width 3 for monotone profiles -/

/-- `‖ĝ(z)‖ ≤ e^{a|Im z|}∫|g|`. -/
theorem norm_ghatC_le_exp_im (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a) (z : ℂ) :
    ‖ghatC g a z‖ ≤ Real.exp (a * |z.im|) * ∫ u in (-a)..a, |g u| := by
  unfold ghatC
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Eventually.of_forall fun u hu => ?_) (hg.abs.const_mul (Real.exp (a * |z.im|)))).trans_eq
    (intervalIntegral.integral_const_mul _ _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.2
  have e : (Complex.I * z * u).re = -(z.im * u) := by simp [Complex.mul_re]
  rw [e]
  have h1 : |u| ≤ a := abs_le.2 ⟨hu.1.le, hu.2⟩
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ |z.im| * a := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = a * |z.im| := mul_comm _ _

/-- **`ĝ(3z)²` is a strip test function** for every even, nonnegative profile non-increasing on
`[0, a]`: the width-3 form of `striptest_antitone`. -/
theorem striptest_antitone3 (ha : 0 < a) (hev : ∀ u, g (-u) = g u)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u)
    (hint : IntervalIntegrable g volume (-a) a) :
    ∃ K, StripTest (fun z => ghatC g a (3 * z) ^ 2) K := by
  have hg0 : 0 ≤ g 0 := hnn 0 ⟨le_rfl, ha.le⟩
  refine ⟨(Real.exp (3 * a) * ∫ u in (-a)..a, |g u|) ^ 2
      + (2 * g 0 * Real.cosh (3 * a) / 3) ^ 2,
    striptest_sq ((ghatC_differentiable hint).comp (differentiable_id.const_mul 3))
      fun t ht => ?_⟩
  have h3im : (3 * t).im = 3 * t.im := by simp
  have htim : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h3 : |(3 * t).im| ≤ 3 := by
    rw [h3im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
  refine sq_strip_bound ?_ ?_
  · refine (norm_ghatC_le_exp_im ha.le hint _).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _)
    linarith [mul_le_mul_of_nonneg_left h3 ha.le]
  · rcases eq_or_ne t 0 with rfl | ht0
    · simp; positivity
    have h3t : (3 : ℂ) * t ≠ 0 := mul_ne_zero (by norm_num) ht0
    have hb := norm_ghatC_le_of_antitone ha hev hmono hnn h3t
    have hn3 : ‖(3 : ℂ) * t‖ = 3 * ‖t‖ := by rw [norm_mul]; norm_num
    rw [hn3] at hb
    have hc : Real.cosh (a * |(3 * t).im|) ≤ Real.cosh (3 * a) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg ha.le (abs_nonneg _)),
        abs_of_pos (by linarith : (0 : ℝ) < 3 * a)]
      linarith [mul_le_mul_of_nonneg_left h3 ha.le]
    have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
    calc ‖t‖ * ‖ghatC g a (3 * t)‖
        ≤ ‖t‖ * (2 * g 0 * Real.cosh (a * |(3 * t).im|) / (3 * ‖t‖)) :=
          mul_le_mul_of_nonneg_left hb htn.le
      _ = 2 * g 0 * Real.cosh (a * |(3 * t).im|) / 3 := by field_simp
      _ ≤ 2 * g 0 * Real.cosh (3 * a) / 3 := by gcongr

/-- **The certificate for monotone probes**: no strip hypothesis. -/
theorem exists_offline_dh_of_neg_antitone (ha : 0 < a) (hp : Probe a g)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u) (hneg : QDHu g < 0) :
    ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 := by
  obtain ⟨K, hK⟩ := striptest_antitone3 ha hp.even hmono hnn hp.intervalIntegrable
  exact exists_offline_dh_of_neg_u hp ha hK hneg

theorem box_antitone' (a : ℝ) : AntitoneOn (box a) (Icc 0 a) := fun x hx y hy _ => by
  have h1 : |x| ≤ a := by rw [abs_of_nonneg hx.1]; exact hx.2
  have h2 : |y| ≤ a := by rw [abs_of_nonneg hy.1]; exact hy.2
  rw [box_apply, box_apply]; simp [h1, h2]

theorem box_nonneg' (a : ℝ) : ∀ u ∈ Icc (0 : ℝ) a, 0 ≤ box a u := fun u _ => by
  rw [box_apply]; split_ifs <;> positivity

/-- **The certificate for the box**: `Q_dh(box a) < 0` for one `a > 0` gives an off-line zero. -/
theorem exists_offline_dh_of_neg_box (ha : 0 < a) (hneg : QDHu (box a) < 0) :
    ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 :=
  exists_offline_dh_of_neg_antitone ha (box_probe a) (box_antitone' a) (box_nonneg' a) hneg

end PsiOmega

#print axioms PsiOmega.gh_comp_three
#print axioms PsiOmega.integral_hsq_psiRe3
#print axioms PsiOmega.weilRHSDH_scaled
#print axioms PsiOmega.QDHu_hasSum
#print axioms PsiOmega.QDHu_nonneg_of_DHRH
#print axioms PsiOmega.exists_offline_dh_of_neg_u
#print axioms PsiOmega.norm_ghatC_le_exp_im
#print axioms PsiOmega.striptest_antitone3
#print axioms PsiOmega.exists_offline_dh_of_neg_antitone
#print axioms PsiOmega.exists_offline_dh_of_neg_box
