import Mathlib
import ZetaInputs

/-! # The exterior identity over the zeros of `ζ`, for every probe (round 157)

Round 4's exterior identity (`exterior_identity_probe`) takes Weil's explicit formula for
`h = ĝ²χ` as a named input, with `χ` the smooth even band cut built from the complex normal
distribution function `Φ`. Here `h` is shown to be a strip test function for every even probe
`g ∈ L¹[−a, a]`, so round 156's `weilExplicit_zeta` supplies the input:

* `differentiable_Phi`: `Φ` is entire (differentiation under the integral).
* `Phi_add_neg`: `Φ(w) + Φ(−w) = 1` (the shifted complex Gaussian integral).
* `chi_strip`: `‖χ(t)‖(1 + (Re t)²)` is bounded on `|Im t| ≤ 1`; away from the band `χ` has Gaussian
  decay, and near it `χ` is continuous on a compact set.
* `exterior_identity_probe_zeta`: the exterior identity summed over the nontrivial zeros of `ζ`,
  with no named input (the integrability conditions on the real values stay as hypotheses).

Classical analysis only: no bearing on RH.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## `Φ` is entire -/

theorem gauss_exp_le {z : ℂ} {R u : ℝ} (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (-(z - u) ^ 2 / 2)‖ ≤ Real.exp (R ^ 2) * Real.exp (-(1 / 4) * u ^ 2) := by
  rw [Complex.norm_exp, re_gauss, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := Complex.abs_im_le_norm z
  have h2 := Complex.abs_re_le_norm z
  have hi : z.im ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  have hr : z.re ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg z.re, sq_abs z.re]
  nlinarith [sq_nonneg (u - 2 * z.re)]

theorem differentiable_Phi : Differentiable ℂ Phi := by
  intro z0
  set R := ‖z0‖ + 1
  set bound : ℝ → ℝ := fun u => Real.exp (R ^ 2) *
    (R * Real.exp (-(1 / 4) * u ^ 2) + u * Real.exp (-(1 / 4) * u ^ 2))
  have hbi : Integrable bound (volume.restrict (Ioi 0)) :=
    ((((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul R).add
      (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4))).const_mul _).restrict
  have hball : ∀ z ∈ Metric.ball z0 1, ‖z‖ ≤ R := fun z hz => by
    have := norm_le_norm_add_norm_sub' z z0
    rw [Metric.mem_ball, dist_eq_norm] at hz
    simp only [R]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (x₀ := z0) (s := Metric.ball z0 1)
    (F := fun z (u : ℝ) => Complex.exp (-(z - u) ^ 2 / 2))
    (F' := fun z (u : ℝ) => -(z - u) * Complex.exp (-(z - u) ^ 2 / 2))
    (bound := bound) (Metric.ball_mem_nhds z0 one_pos)
    (Eventually.of_forall fun z => (by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (-(z - u) ^ 2 / 2)).aestronglyMeasurable)
    ?_ ((by fun_prop : Continuous fun u : ℝ =>
      -(z0 - u) * Complex.exp (-(z0 - u) ^ 2 / 2)).aestronglyMeasurable) ?_ hbi ?_
  · have hP : Phi = fun z => ((1 / Real.sqrt (2 * π) : ℝ) : ℂ) *
        ∫ u in Ioi (0 : ℝ), Complex.exp (-(z - u) ^ 2 / 2) := by
      funext z; rfl
    rw [hP]
    exact (key.2.differentiableAt).const_mul _
  · refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (Real.exp (R ^ 2))).restrict
      ((by fun_prop : Continuous fun u : ℝ => Complex.exp (-(z0 - u) ^ 2 / 2)).aestronglyMeasurable)
      (Eventually.of_forall fun u => gauss_exp_le (by simp [R]))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu z hz => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hzR := hball z hz
    rw [norm_mul, norm_neg]
    have h1 : ‖z - u‖ ≤ R + u := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]; linarith
    have h2 := gauss_exp_le (u := u) hzR
    calc ‖z - u‖ * ‖Complex.exp (-(z - u) ^ 2 / 2)‖
        ≤ (R + u) * (Real.exp (R ^ 2) * Real.exp (-(1 / 4) * u ^ 2)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = bound u := by simp only [bound]; ring
  · refine Eventually.of_forall fun u z _ => ?_
    have h := ((((hasDerivAt_id z).sub_const (u : ℂ)).mul
      ((hasDerivAt_id z).sub_const (u : ℂ))).neg.div_const 2).cexp
    convert h using 1
    · funext x; simp only [id, sq, Pi.mul_apply, Pi.neg_apply]
    · simp only [id, sq, Pi.mul_apply, Pi.neg_apply]; ring

/-! ## `Φ(w) + Φ(−w) = 1` -/

theorem Phi_add_neg (w : ℂ) : Phi w + Phi (-w) = 1 := by
  set f : ℝ → ℂ := fun v => Complex.exp (-(w - v) ^ 2 / 2)
  have hshift : ∀ x : ℝ,
      f (x + w.re) = Complex.exp (-(1 / 2 : ℂ) * (x + ((-w.im : ℝ) : ℂ) * I) ^ 2) := by
    intro x
    simp only [f]
    congr 1
    have hw : w - ((x + w.re : ℝ) : ℂ) = -((x : ℂ) + ((-w.im : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hw]; ring
  have hint' := GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I (b := 1 / 2)
    (by norm_num) (-w.im)
  have hint : Integrable f := by
    have := hint'.comp_sub_right w.re
    refine this.congr (Eventually.of_forall fun x => ?_)
    have h := hshift (x - w.re)
    simp only [sub_add_cancel] at h
    rw [h]
  have hval : ∫ v, f v = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
    rw [← integral_add_right_eq_self (μ := volume) f w.re]
    simp_rw [hshift]
    rw [GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I (b := 1 / 2) (by norm_num) (-w.im)]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    field_simp
  have hneg : ∫ u in Ioi (0 : ℝ), Complex.exp (-(-w - u) ^ 2 / 2) = ∫ v in Iic (0 : ℝ), f v := by
    have h := integral_comp_neg_Ioi 0 f
    rw [neg_zero] at h
    rw [← h]
    congr 1; funext u; simp only [f]; push_cast; ring_nf
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn
  unfold Phi
  rw [hneg, ← mul_add, show (∫ u in Ioi (0 : ℝ), Complex.exp (-(w - u) ^ 2 / 2))
    = ∫ v in Ioi (0 : ℝ), f v from rfl, add_comm, hsplit, hval]
  have : Real.sqrt (2 * π) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  push_cast
  field_simp

/-! ## `χ` on the strip -/

theorem differentiable_chi (T T' Δ : ℝ) : Differentiable ℂ (chi T T' Δ) := by
  have hP := differentiable_Phi
  unfold chi
  fun_prop

/-- Gaussian decay of `Φ` on the left, with the imaginary part controlled. -/
theorem norm_Phi_left {w : ℂ} {x Δ : ℝ} (hx : 0 ≤ x) (hre : w.re ≤ -x) (hΔ : 0 < Δ)
    (him : |w.im| ≤ 1 / Δ) :
    ‖Phi w‖ ≤ Real.exp (1 / (2 * Δ ^ 2)) * Real.exp (-(x ^ 2 / 2)) / 2 := by
  refine (norm_Phi_le (by linarith)).trans ?_
  rw [← Real.exp_add]
  apply div_le_div_of_nonneg_right (Real.exp_le_exp.2 _) (by norm_num)
  have h1 : w.im ^ 2 ≤ 1 / Δ ^ 2 := by
    have := sq_le_sq' (abs_le.1 him).1 (abs_le.1 him).2
    rw [div_pow, one_pow] at this; exact this
  have h2 : x ^ 2 ≤ w.re ^ 2 := by nlinarith
  have e : 1 / (2 * Δ ^ 2) = (1 / Δ ^ 2) / 2 := by field_simp
  rw [e]; linarith

/-- Right of the band: `‖χ(t)‖ ≤ 2e^{1/(2Δ²)}e^{−x²/2}`, `x = (Re t − T′)/Δ`. -/
theorem norm_chi_right {T T' Δ : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T') (hΔ : 0 < Δ) {t : ℂ}
    (ht : |t.im| ≤ 1) (hr : T' ≤ t.re) :
    ‖chi T T' Δ t‖ ≤ 2 * Real.exp (1 / (2 * Δ ^ 2)) * Real.exp (-(((t.re - T') / Δ) ^ 2 / 2)) := by
  set x := (t.re - T') / Δ
  have hx : 0 ≤ x := div_nonneg (by linarith) hΔ.le
  have e : chi T T' Δ t = Phi (-((t - T') / Δ)) - Phi (-((t - T) / Δ))
      + Phi ((-t - T) / Δ) - Phi ((-t - T') / Δ) := by
    unfold chi
    have h1 := Phi_add_neg ((t - T) / Δ)
    have h2 := Phi_add_neg ((t - T') / Δ)
    linear_combination h1 - h2
  have hre : ∀ c : ℝ, (((t - c) / Δ : ℂ)).re = (t.re - c) / Δ := fun c => by
    rw [Complex.div_ofReal_re]; simp
  have hre' : ∀ c : ℝ, (((-t - c) / Δ : ℂ)).re = (-t.re - c) / Δ := fun c => by
    rw [Complex.div_ofReal_re]; simp
  have him : ∀ c : ℝ, |(((t - c) / Δ : ℂ)).im| ≤ 1 / Δ := fun c => by
    rw [Complex.div_ofReal_im]; simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [abs_div, abs_of_pos hΔ]; exact div_le_div_of_nonneg_right ht hΔ.le
  have him' : ∀ c : ℝ, |(((-t - c) / Δ : ℂ)).im| ≤ 1 / Δ := fun c => by
    rw [Complex.div_ofReal_im]; simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, sub_zero]
    rw [abs_div, abs_of_pos hΔ, abs_neg]; exact div_le_div_of_nonneg_right ht hΔ.le
  have le1 : ‖Phi (-((t - T') / Δ))‖ ≤ Real.exp (1 / (2 * Δ ^ 2)) * Real.exp (-(x ^ 2 / 2)) / 2 :=
    norm_Phi_left hx (by rw [Complex.neg_re, hre]) hΔ (by rw [Complex.neg_im, abs_neg]; exact him T')
  have le2 : ‖Phi (-((t - T) / Δ))‖ ≤ Real.exp (1 / (2 * Δ ^ 2)) * Real.exp (-(x ^ 2 / 2)) / 2 :=
    norm_Phi_left hx (by
      rw [Complex.neg_re, hre]; simp only [x]
      rw [← neg_div, ← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hΔ.le) hΔ
      (by rw [Complex.neg_im, abs_neg]; exact him T)
  have le3 : ‖Phi ((-t - T) / Δ)‖ ≤ Real.exp (1 / (2 * Δ ^ 2)) * Real.exp (-(x ^ 2 / 2)) / 2 :=
    norm_Phi_left hx (by
      rw [hre']; simp only [x]
      rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hΔ.le) hΔ (him' T)
  have le4 : ‖Phi ((-t - T') / Δ)‖ ≤ Real.exp (1 / (2 * Δ ^ 2)) * Real.exp (-(x ^ 2 / 2)) / 2 :=
    norm_Phi_left hx (by
      rw [hre']; simp only [x]
      rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith) hΔ.le) hΔ (him' T')
  rw [e]
  calc _ ≤ ‖Phi (-((t - T') / Δ))‖ + ‖Phi (-((t - T) / Δ))‖ + ‖Phi ((-t - T) / Δ)‖
        + ‖Phi ((-t - T') / Δ)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

/-- **`χ` in the strip class**: `‖χ(t)‖(1 + (Re t)²) ≤ M` on `|Im t| ≤ 1`. -/
theorem chi_strip {T T' Δ : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T') (hΔ : 0 < Δ) :
    ∃ M, ∀ t ∈ PilotWeil.strip (-1) 1, ‖chi T T' Δ t‖ * (1 + t.re ^ 2) ≤ M := by
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) (T' + 1)).exists_bound_of_continuousOn
    (differentiable_chi T T' Δ).continuous.continuousOn
  set E := Real.exp (1 / (2 * Δ ^ 2))
  set M1 := 2 * E * (1 + 2 * T' ^ 2 + 4 * Δ ^ 2)
  -- the right-of-band bound, times the weight
  have hR : ∀ t : ℂ, |t.im| ≤ 1 → T' ≤ t.re → ‖chi T T' Δ t‖ * (1 + t.re ^ 2) ≤ M1 := by
    intro t ht hr
    set x := (t.re - T') / Δ
    have hb := norm_chi_right hT hTT' hΔ ht hr
    have htx : t.re = Δ * x + T' := by simp only [x]; field_simp; ring
    have hw : 1 + t.re ^ 2 ≤ 1 + 2 * T' ^ 2 + 2 * Δ ^ 2 * x ^ 2 := by
      rw [htx]; nlinarith [sq_nonneg (Δ * x - T')]
    have hy : x ^ 2 / 2 * Real.exp (-(x ^ 2 / 2)) ≤ 1 := by
      have h1 := Real.add_one_le_exp (x ^ 2 / 2)
      have h2 : Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-(x ^ 2 / 2)), Real.exp_pos (x ^ 2 / 2)]
    have he1 : Real.exp (-(x ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
    have hE : 0 < E := Real.exp_pos _
    calc ‖chi T T' Δ t‖ * (1 + t.re ^ 2)
        ≤ 2 * E * Real.exp (-(x ^ 2 / 2)) * (1 + 2 * T' ^ 2 + 2 * Δ ^ 2 * x ^ 2) :=
          mul_le_mul hb hw (by positivity) (by positivity)
      _ = 2 * E * ((1 + 2 * T' ^ 2) * Real.exp (-(x ^ 2 / 2))
            + 4 * Δ ^ 2 * (x ^ 2 / 2 * Real.exp (-(x ^ 2 / 2)))) := by ring
      _ ≤ 2 * E * ((1 + 2 * T' ^ 2) * 1 + 4 * Δ ^ 2 * 1) := by
          gcongr
      _ = M1 := by simp only [M1]; ring
  refine ⟨max (M0 * (1 + T' ^ 2)) M1, fun t ht => ?_⟩
  have hti : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  rcases le_or_gt T' t.re with hr | hr
  · exact (hR t hti hr).trans (le_max_right _ _)
  rcases le_or_gt T' (-t.re) with hl | hl
  · have hm := hR (-t) (by simpa using hti) (by simpa using hl)
    rw [chi_even] at hm
    simp only [Complex.neg_re, neg_sq] at hm
    exact hm.trans (le_max_right _ _)
  · have hre : |t.re| ≤ T' := abs_le.2 ⟨by linarith, hr.le⟩
    have hball : t ∈ Metric.closedBall (0 : ℂ) (T' + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im t).trans (by linarith)
    have h1 := hM0 t hball
    have h2 : 1 + t.re ^ 2 ≤ 1 + T' ^ 2 := by nlinarith [abs_nonneg t.re, sq_abs t.re]
    have hM0' : 0 ≤ M0 := (norm_nonneg _).trans h1
    exact (mul_le_mul h1 h2 (by positivity) hM0').trans (le_max_left _ _)

/-! ## The exterior identity over the zeros of `ζ` -/

theorem Phi_real (x : ℝ) : (Phi x).im = 0 := by
  have e : Phi x = ((1 / Real.sqrt (2 * π) * ∫ u in Ioi (0 : ℝ), Real.exp (-(x - u) ^ 2 / 2) : ℝ) : ℂ) := by
    unfold Phi
    rw [Complex.ofReal_mul, ← integral_complex_ofReal]
    congr 2; funext u; push_cast; rfl
  rw [e, Complex.ofReal_im]

theorem chi_real (T T' Δ r : ℝ) : (chi T T' Δ r).im = 0 := by
  unfold chi
  have e : ∀ c : ℝ, ((r : ℂ) - c) / Δ = (((r - c) / Δ : ℝ) : ℂ) := fun c => by push_cast; rfl
  have e' : ∀ c : ℝ, (-(r : ℂ) - c) / Δ = (((-r - c) / Δ : ℝ) : ℂ) := fun c => by push_cast; rfl
  rw [e, e, e', e']
  simp only [Complex.sub_im, Complex.add_im, Phi_real]; ring

/-- The real values of `ĝ²χ` on `ℝ`. -/
def hRchi (g : ℝ → ℝ) (a T T' Δ r : ℝ) : ℝ := (ghatC g a r ^ 2 * chi T T' Δ r).re

theorem striptest_ghat_chi {g : ℝ → ℝ} {a T T' Δ : ℝ} (ha : 0 ≤ a)
    (hint : IntervalIntegrable g volume (-a) a) (hT : 0 ≤ T) (hTT' : T ≤ T') (hΔ : 0 < Δ) :
    ∃ K, StripTest (fun z => ghatC g a z ^ 2 * chi T T' Δ z) K := by
  obtain ⟨M, hM⟩ := chi_strip hT hTT' hΔ
  set τ0 := Real.exp a * ∫ u in (-a)..a, |g u|
  refine ⟨τ0 ^ 2 * M, ((ghatC_differentiable hint).pow 2).mul (differentiable_chi T T' Δ)
    |>.differentiableOn, fun t ht => ?_⟩
  have h0 : ‖ghatC g a t‖ ≤ τ0 := norm_ghatC_strip_le ha hint (abs_le.2 ⟨ht.1, ht.2⟩)
  have hw : 0 < 1 + t.re ^ 2 := by positivity
  rw [le_div_iff₀ hw, norm_mul, norm_pow, mul_assoc]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h0 2) (hM t ht) (by positivity)
    (by have := norm_nonneg (ghatC g a t); positivity)

/-- **1ca(iv) over the zeros of `ζ`, for every even probe, with no named input.** The zeros' sum
`Σ_ρ ĝ(t_ρ)²χ(t_ρ)` is the smooth count's integral plus `E_arch` plus the pole term less the prime
shells. The three integrability conditions on the real values `hR` are the identity's own
regularity hypotheses. -/
theorem exterior_identity_probe_zeta {g : ℝ → ℝ} {a T T' Δ : ℝ} (ha : 0 ≤ a)
    (hg : ∀ u, g (-u) = g u) (hint : IntervalIntegrable g volume (-a) a)
    (hT : 0 ≤ T) (hTT' : T ≤ T') (hΔ : 0 < Δ)
    (hi0 : IntegrableOn (hRchi g a T T' Δ) (Set.Ioi 0))
    (hi1 : IntegrableOn (fun r => hRchi g a T T' Δ r * Real.log (r / (2 * π))) (Set.Ioi 0))
    (hi2 : IntegrableOn (fun r => hRchi g a T T' Δ r * (psiRe r - Real.log (r / 2))) (Set.Ioi 0)) :
    HasSum (fun p => ghatC g a ((zetaZeroFamily p - 1 / 2) / Complex.I) ^ 2
        * chi T T' Δ ((zetaZeroFamily p - 1 / 2) / Complex.I))
      (((1 / π * (∫ r in Set.Ioi (0 : ℝ), hRchi g a T T' Δ r * Real.log (r / (2 * π)))
          + Earch (hRchi g a T T' Δ)
          - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
            * fchi (hRchi g a T T' Δ) (Real.log n) : ℝ) : ℂ)
        + 2 * ghatC g a (Complex.I / 2) ^ 2 * chi T T' Δ (Complex.I / 2)) := by
  obtain ⟨K, hK⟩ := striptest_ghat_chi ha hint hT hTT' hΔ
  have hEF : WeilExplicit zetaZeroFamily (fun z => ghatC g a z ^ 2 * chi T T' Δ z) (hRchi g a T T' Δ) :=
    weilExplicit_zeta hK (fun t => by simp only [chi_even, ghatC_even hg]) (fun r => by
      have him : (ghatC g a r ^ 2 * chi T T' Δ r).im = 0 := by
        have h1 := ghatC_im_eq_zero hg hint r
        have h2 := chi_real T T' Δ r
        simp [sq, Complex.mul_im, h1, h2]
      exact Complex.ext (by simp [hRchi]) (by simp [him]))
  exact exterior_identity_probe hg hEF hi0 hi1 hi2

end Pilot1ca

#print axioms Pilot1ca.differentiable_Phi
#print axioms Pilot1ca.Phi_add_neg
#print axioms Pilot1ca.chi_strip
#print axioms Pilot1ca.striptest_ghat_chi
#print axioms Pilot1ca.exterior_identity_probe_zeta
