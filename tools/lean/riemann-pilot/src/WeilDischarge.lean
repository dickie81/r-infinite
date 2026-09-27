import Mathlib
import WeilAssemble
import PhiLadder

/-! # Discharging `WeilExplicit` for the pilot's test functions (round 156, part 5)

`weilExplicit_Xi` proves `WeilExplicit` over the zeros of `Ξ` for every test function in the strip
class (`StripTest`). Here the pilot's test functions are shown to be in the class:
`ĝ(Φ_b)²`, the twins' `ĝ(T_l)²`, the rung-2 combinations, and `1/(z² + 4)`. The decay corollaries
`lam_decay`, `lamO_decay` and `lam2_decay` then hold with **no named input at all**.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open PilotWeil

/-! ## The strip class for squares -/

theorem striptest_sq {G : ℂ → ℂ} (hd : Differentiable ℂ G) {K : ℝ}
    (hK : ∀ t ∈ PilotWeil.strip (-1) 1, ‖G t‖ ^ 2 * (1 + t.re ^ 2) ≤ K) :
    StripTest (fun z => G z ^ 2) K := by
  refine ⟨Differentiable.differentiableOn (hd.pow 2), fun t ht => ?_⟩
  rw [norm_pow, le_div_iff₀ (by positivity)]
  exact hK t ht

/-- `‖ĝ(z)‖ ≤ e^{a}∫|g|` on `|Im z| ≤ 1`. -/
theorem norm_ghatC_strip_le {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hg : IntervalIntegrable g volume (-a) a) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖ghatC g a z‖ ≤ Real.exp a * ∫ u in (-a)..a, |g u| := by
  unfold ghatC
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Eventually.of_forall fun u hu => ?_) (hg.abs.const_mul (Real.exp a))).trans_eq
    (intervalIntegral.integral_const_mul _ _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.2
  have e : (Complex.I * z * u).re = -(z.im * u) := by simp [Complex.mul_re]
  rw [e]
  have h1 : |u| ≤ a := abs_le.2 ⟨hu.1.le, hu.2⟩
  have h2 := neg_abs_le (z.im * u)
  rw [abs_mul] at h2
  nlinarith [abs_nonneg u, abs_nonneg z.im]

theorem norm_cexp_strip_le {z : ℂ} (hz : |z.im| ≤ 1) {b : ℝ} (hb : 0 ≤ b) :
    ‖Complex.exp (Complex.I * z * b)‖ ≤ Real.exp b ∧ ‖Complex.exp (-(Complex.I * z * b))‖ ≤ Real.exp b := by
  have e1 : (Complex.I * z * b).re = -(z.im * b) := by simp [Complex.mul_re]
  have h2 := neg_abs_le (z.im * b)
  have h3 := le_abs_self (z.im * b)
  rw [abs_mul, abs_of_nonneg hb] at h2 h3
  constructor
  · rw [Complex.norm_exp, e1]; apply Real.exp_le_exp.2; nlinarith
  · rw [Complex.norm_exp, Complex.neg_re, e1]; apply Real.exp_le_exp.2; nlinarith

/-- **`ĝ(Φ_b)` on the strip**: `‖ĝ(z)‖²(1 + (Re z)²) ≤ K`. -/
theorem ghat_PhiA_strip {b : ℝ} (hb : 0 < b) : ∃ K, ∀ t ∈ PilotWeil.strip (-1) 1,
    ‖ghatC (PhiA b) b t‖ ^ 2 * (1 + t.re ^ 2) ≤ K := by
  have hR : IntervalIntegrable RPhi volume (-b) b := continuous_RPhi.intervalIntegrable _ _
  have hR1 : IntervalIntegrable RPhi1 volume (-b) b := continuous_RPhi1.intervalIntegrable _ _
  set τ0 := Real.exp b * ∫ u in (-b)..b, |RPhi u|
  set τ1 := 2 * |RPhi b| * Real.exp b + Real.exp b * ∫ u in (-b)..b, |RPhi1 u|
  refine ⟨τ0 ^ 2 + τ1 ^ 2, fun t ht => ?_⟩
  have hz : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  rw [ghatC_PhiA hb.le]
  have h0 : ‖ghatC RPhi b t‖ ≤ τ0 := norm_ghatC_strip_le hb.le hR hz
  have h1 : ‖t‖ * ‖ghatC RPhi b t‖ ≤ τ1 := by
    have hi := ibp_window b t
    have hn : ‖t‖ * ‖ghatC RPhi b t‖ = ‖Complex.I * t * ghatC RPhi b t‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    rw [hn, hi]
    obtain ⟨e1, e2⟩ := norm_cexp_strip_le hz hb.le
    have hg1 := norm_ghatC_strip_le hb.le hR1 hz
    calc _ ≤ ‖(RPhi b : ℂ) * (Complex.exp (Complex.I * t * b) - Complex.exp (-(Complex.I * t * b)))‖
          + ‖ghatC RPhi1 b t‖ := norm_sub_le _ _
      _ ≤ |RPhi b| * (Real.exp b + Real.exp b) + Real.exp b * ∫ u in (-b)..b, |RPhi1 u| := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add e1 e2)
      _ = τ1 := by simp only [τ1]; ring
  have hx : t.re ^ 2 ≤ ‖t‖ ^ 2 := by
    have := Complex.abs_re_le_norm t
    nlinarith [abs_nonneg t.re, sq_abs t.re]
  have hg0 := norm_nonneg (ghatC RPhi b t)
  have hτ0 : 0 ≤ τ0 := le_trans hg0 h0
  nlinarith [mul_le_mul h0 h0 hg0 hτ0, mul_self_nonneg (‖t‖ * ‖ghatC RPhi b t‖),
    mul_le_mul h1 h1 (by positivity) (le_trans (by positivity) h1)]

/-- **`ĝ(Φ_b)²` is in the strip class.** -/
theorem striptest_PhiA {b : ℝ} (hb : 0 < b) : ∃ K, StripTest (fun z => ghatC (PhiA b) b z ^ 2) K := by
  obtain ⟨K, hK⟩ := ghat_PhiA_strip hb
  exact ⟨K, striptest_sq (ghatC_differentiable (probe_PhiA hb.le).intervalIntegrable) hK⟩

/-- `1/(z² + 4)` is in the strip class. -/
theorem striptest_four : StripTest (fun z : ℂ => 1 / (z ^ 2 + 4)) 1 := by
  have hre : ∀ t ∈ PilotWeil.strip (-1) 1, 1 + t.re ^ 2 ≤ (t ^ 2 + 4).re := fun t ht => by
    have : t.im ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    simp [sq, Complex.mul_re]; nlinarith
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have hne : t ^ 2 + 4 ≠ 0 := fun h0 => by
      have := hre t ht; rw [h0, Complex.zero_re] at this; nlinarith [sq_nonneg t.re]
    exact (DifferentiableAt.div (c := fun _ : ℂ => (1 : ℂ)) (d := fun z : ℂ => z ^ 2 + 4)
      (differentiableAt_const _) (by fun_prop) hne).differentiableWithinAt
  · have h1 := hre t ht
    have h2 := (Complex.re_le_norm (t ^ 2 + 4))
    rw [norm_div, norm_one, div_le_div_iff₀ (by linarith [sq_nonneg t.re]) (by positivity)]
    linarith

theorem even_ghat_sq {g : ℝ → ℝ} (hg : ∀ u, g (-u) = g u) (a : ℝ) (t : ℂ) :
    ghatC g a (-t) ^ 2 = ghatC g a t ^ 2 := by rw [ghatC_even hg]

/-- **`Σ‖1/(t_ρ² + 4)‖ < ∞`** over the zeros of `Ξ`. -/
theorem summable_four_Xi :
    Summable fun p : Bool × ZeroIdx (sqF Xi) => ‖1 / (((rhoXi p - 1 / 2) / Complex.I) ^ 2 + 4)‖ := by
  have H := weilExplicit_Xi striptest_four (hR := fun r => 1 / (r ^ 2 + 4))
    (fun t => by simp) (fun r => by push_cast; rfl)
  exact summable_norm_iff.2 H.2.summable

/-- The explicit formula for `ĝ(Φ_b)²`, `b > 0`, over the zeros of `Ξ`. -/
theorem weilExplicit_PhiA {b : ℝ} (hb : 0 < b) :
    WeilExplicit rhoXi (fun z => ghatC (PhiA b) b z ^ 2) (hsq (PhiA b) b) := by
  obtain ⟨K, hK⟩ := striptest_PhiA hb
  exact weilExplicit_Xi hK (fun t => even_ghat_sq (probe_PhiA hb.le).even b t)
    (hsq_ofReal (probe_PhiA hb.le) hb.le)

/-- **Round 133's decay of the ground energy, unconditional**: `λ₁(a) ≤ K e^{−Ba}` for every `B`,
with no named input. -/
theorem lam_decay_uncond (B : ℝ) : ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lam a ≤ K * Real.exp (-B * a) :=
  lam_decay Xi_rhoXi (fun p => (im_rhoXi p).le) summable_four_Xi
    (fun a ha => weilExplicit_PhiA (by linarith)) B

/-! ## Twins and rung-2 combinations -/

theorem striptest_mul_sq {G m : ℂ → ℂ} (hdG : Differentiable ℂ G) (hdm : Differentiable ℂ m)
    {K M : ℝ} (hK : ∀ t ∈ PilotWeil.strip (-1) 1, ‖G t‖ ^ 2 * (1 + t.re ^ 2) ≤ K)
    (hm : ∀ t ∈ PilotWeil.strip (-1) 1, ‖m t‖ ≤ M) :
    StripTest (fun z => (m z * G z) ^ 2) (M ^ 2 * K) := by
  refine striptest_sq (hdm.mul hdG) fun t ht => ?_
  have hM : 0 ≤ M := (norm_nonneg _).trans (hm t ht)
  simp only [Pi.mul_apply]
  rw [norm_mul, mul_pow, mul_assoc]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hm t ht) 2) (hK t ht) (by positivity) (by positivity)

theorem norm_two_cos_strip {l : ℝ} (hl : 0 ≤ l) {t : ℂ} (ht : t ∈ PilotWeil.strip (-1) 1) :
    ‖2 * Complex.cos (l * t)‖ ≤ 2 * Real.exp l := by
  refine (norm_two_cos_le _).trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 _) (by norm_num)
  have e : ((l : ℂ) * t).im = l * t.im := by simp [Complex.mul_im]
  rw [e, abs_mul, abs_of_nonneg hl]
  have : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  nlinarith

/-- The explicit formula for the twins' `ĝ(T_l)²`, over the zeros of `Ξ`. -/
theorem weilExplicit_twin {b l : ℝ} (hb : 0 < b) (hl : 0 ≤ l) :
    WeilExplicit rhoXi (fun z => ghatC (twin (PhiA b) l) (l + b) z ^ 2) (hsq (twin (PhiA b) l) (l + b)) := by
  have hp := probe_PhiA hb.le
  have hpt := twin_probe hp hl
  obtain ⟨K, hK⟩ := ghat_PhiA_strip hb
  have hT := striptest_mul_sq (G := ghatC (PhiA b) b) (m := fun z => 2 * Complex.cos (l * z))
    (ghatC_differentiable hp.intervalIntegrable) (by fun_prop) hK (fun t ht => norm_two_cos_strip hl ht)
  have e : (fun z => ghatC (twin (PhiA b) l) (l + b) z ^ 2)
      = fun z => (2 * Complex.cos (l * z) * ghatC (PhiA b) b z) ^ 2 := by
    funext z; rw [ghatC_twin hb hp hl]
  rw [e]
  refine weilExplicit_Xi hT (fun t => ?_) (fun r => ?_)
  · have := even_ghat_sq hpt.even (l + b) t
    rw [ghatC_twin hb hp hl, ghatC_twin hb hp hl] at this
    exact this
  · have := hsq_ofReal hpt (by linarith) r
    rw [ghatC_twin hb hp hl] at this
    exact this

/-- The explicit formula for the rung-2 combinations `pT_{a/4} + qT_{3a/4}`, over the zeros of `Ξ`. -/
theorem weilExplicit_combo {a : ℝ} (ha : 1 ≤ a) (p q : ℝ) :
    WeilExplicit rhoXi
      (fun z => ghatC (fun t => p * twin (PhiA (a / 8)) (a / 4) t
        + q * twin (PhiA (a / 8)) (3 * a / 4) t) a z ^ 2)
      (hsq (fun t => p * twin (PhiA (a / 8)) (a / 4) t + q * twin (PhiA (a / 8)) (3 * a / 4) t) a) := by
  have hb : 0 < a / 8 := by positivity
  have hp := probe_PhiA hb.le
  have hl : (0 : ℝ) ≤ a / 4 := by positivity
  have hm : (0 : ℝ) ≤ 3 * a / 4 := by positivity
  have hpl := twin_probe hp hl
  have hpm := twin_probe hp hm
  have hpv : Probe a (fun t => p * twin (PhiA (a / 8)) (a / 4) t + q * twin (PhiA (a / 8)) (3 * a / 4) t) :=
    (probe_add_sub (probe_smul (hpl.mono (by linarith)) p) (probe_smul (hpm.mono (by linarith)) q)).1
  have e : ∀ t : ℂ, ghatC (fun t => p * twin (PhiA (a / 8)) (a / 4) t
        + q * twin (PhiA (a / 8)) (3 * a / 4) t) a t
      = (p * (2 * Complex.cos (↑(a / 4) * t)) + q * (2 * Complex.cos (↑(3 * a / 4) * t)))
        * ghatC (PhiA (a / 8)) (a / 8) t := by
    intro t
    rw [show (fun t => p * twin (PhiA (a / 8)) (a / 4) t + q * twin (PhiA (a / 8)) (3 * a / 4) t)
      = (fun t => p * twin (PhiA (a / 8)) (a / 4) t) + (fun t => q * twin (PhiA (a / 8)) (3 * a / 4) t)
        from rfl,
      ghatC_add (hpl.memL2.const_mul p) (hpm.memL2.const_mul q), ghatC_smul, ghatC_smul,
      ghatC_window (by linarith) (by linarith) hpl.supp,
      ghatC_window (by linarith) (by linarith) hpm.supp, ghatC_twin hb hp hl, ghatC_twin hb hp hm]
    ring
  obtain ⟨K, hK⟩ := ghat_PhiA_strip hb
  have hT := striptest_mul_sq (G := ghatC (PhiA (a / 8)) (a / 8))
    (m := fun z => (p : ℂ) * (2 * Complex.cos (↑(a / 4) * z)) + q * (2 * Complex.cos (↑(3 * a / 4) * z)))
    (M := |p| * (2 * Real.exp (a / 4)) + |q| * (2 * Real.exp (3 * a / 4)))
    (ghatC_differentiable hp.intervalIntegrable) (by fun_prop) hK (fun t ht => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_two_cos_strip hl ht) (abs_nonneg _)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_two_cos_strip hm ht) (abs_nonneg _))
  have hfun : (fun z => ghatC (fun t => p * twin (PhiA (a / 8)) (a / 4) t
        + q * twin (PhiA (a / 8)) (3 * a / 4) t) a z ^ 2)
      = fun z => (((p : ℂ) * (2 * Complex.cos (↑(a / 4) * z)) + q * (2 * Complex.cos (↑(3 * a / 4) * z)))
          * ghatC (PhiA (a / 8)) (a / 8) z) ^ 2 := by
    funext z; rw [e]
  rw [hfun]
  refine weilExplicit_Xi hT (fun t => ?_) (fun r => ?_)
  · have := even_ghat_sq (g := fun t => p * twin (PhiA (a / 8)) (a / 4) t
      + q * twin (PhiA (a / 8)) (3 * a / 4) t) hpv.even a t
    rw [e, e] at this
    exact this
  · have := hsq_ofReal hpv (by linarith) r
    rw [e] at this
    exact this

/-- **Rung 1 (round 153), unconditional**: `λ_odd(a) ≤ K e^{−Ba}` for every `B`. -/
theorem lamO_decay_uncond (B : ℝ) : ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lamO a ≤ K * Real.exp (-B * a) :=
  lamO_decay Xi_rhoXi (fun p => (im_rhoXi p).le) summable_four_Xi
    (fun (b : ℝ) (hb : 0 < b) => weilExplicit_PhiA hb)
    (fun (b l : ℝ) (hb : 0 < b) (hl : 0 ≤ l) => weilExplicit_twin hb hl) B

/-- **Rung 2 (round 153), unconditional**: every `s` with `λ₂(a) ≥ s` has `s ≤ K e^{−Ba}`. -/
theorem lam2_decay_uncond (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → ∀ s, Lam2Ge a s → s ≤ K * Real.exp (-B * a) :=
  lam2_decay Xi_rhoXi (fun p => (im_rhoXi p).le) summable_four_Xi
    (fun (a : ℝ) (ha : 1 ≤ a) (p q : ℝ) => weilExplicit_combo ha p q) B

end Pilot1ca

#print axioms Pilot1ca.weilExplicit_PhiA
#print axioms Pilot1ca.weilExplicit_twin
#print axioms Pilot1ca.weilExplicit_combo
#print axioms Pilot1ca.lam_decay_uncond
#print axioms Pilot1ca.lamO_decay_uncond
#print axioms Pilot1ca.lam2_decay_uncond
