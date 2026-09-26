import Mathlib
import GapCriterion

/-! # Weil's form commutes with `∂²` (round 48, Theorem B, formal)

For `C²` functions `f, k` supported in `[−a, a]` (with `f, f'` vanishing outside):

* `xcorr_deriv2`: `xcorr(f'', k)(u) = xcorr(f, k'')(u)` for every shift `u`, by two integrations by parts;
* `bil0_deriv2`: hence `B₀(f'', k) = B₀(f, k'')` for the pole-free bilinear form (constant, archimedean and
  prime terms are all functionals of the cross-correlation);
* `poleR_deriv2`: `poleR(f'') = ¼·poleR(f)`, because `(e^{−u/2})'' = ¼e^{−u/2}`, i.e. `(i/2)² = −¼` is real;
* `bilQ_deriv2`: the full bilinear form of `Q` satisfies `B(f'', k) = B(f, k'')`.

Theorem C itself (flat ⇒ degenerate) is proved in `H²` generality in TheoremC.lean, where the smooth
form `simple_not_flat` is derived as a corollary.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-- `f` is `C²` with derivatives `f₁, f₂`, and `f, f₁, f₂` vanish outside `[−r, r]`. -/
structure C2Supp (r : ℝ) (f f₁ f₂ : ℝ → ℝ) : Prop where
  d1 : ∀ x, HasDerivAt f (f₁ x) x
  d2 : ∀ x, HasDerivAt f₁ (f₂ x) x
  cont2 : Continuous f₂
  supp : ∀ x, r < |x| → f x = 0
  supp1 : ∀ x, r < |x| → f₁ x = 0
  supp2 : ∀ x, r < |x| → f₂ x = 0

/-- `g` is `C²` with derivatives `g₁, g₂` (no support condition). -/
structure C2Fun (g g₁ g₂ : ℝ → ℝ) : Prop where
  d1 : ∀ x, HasDerivAt g (g₁ x) x
  d2 : ∀ x, HasDerivAt g₁ (g₂ x) x
  cont2 : Continuous g₂

theorem C2Supp.toC2Fun {r : ℝ} {f f₁ f₂ : ℝ → ℝ} (h : C2Supp r f f₁ f₂) : C2Fun f f₁ f₂ :=
  ⟨h.d1, h.d2, h.cont2⟩

theorem C2Fun.cont1 {g g₁ g₂ : ℝ → ℝ} (h : C2Fun g g₁ g₂) : Continuous g₁ :=
  continuous_iff_continuousAt.2 fun x => (h.d2 x).continuousAt

/-- **Integration by parts twice on an interval**, boundary values of `u, u₁` zero. -/
theorem ibp2_interval {α β : ℝ} {u u₁ u₂ v v₁ v₂ : ℝ → ℝ} (hu : C2Fun u u₁ u₂) (hv : C2Fun v v₁ v₂)
    (hα : u α = 0) (hβ : u β = 0) (hα1 : u₁ α = 0) (hβ1 : u₁ β = 0) :
    (∫ x in α..β, u₂ x * v x) = ∫ x in α..β, u x * v₂ x := by
  have I1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
    (fun x _ => hv.d1 x) (fun x _ => hu.d2 x)
    (hv.cont1.intervalIntegrable _ _) (hu.cont2.intervalIntegrable _ _)
  have I2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
    (fun x _ => hv.d2 x) (fun x _ => hu.d1 x)
    (hv.cont2.intervalIntegrable _ _) (hu.cont1.intervalIntegrable _ _)
  rw [hα1, hβ1, mul_zero, mul_zero, sub_zero, zero_sub] at I1
  rw [hα, hβ, mul_zero, mul_zero, sub_zero, zero_sub] at I2
  have e1 : (∫ x in α..β, u₂ x * v x) = ∫ x in α..β, v x * u₂ x := by
    congr 1; funext x; ring
  have e2 : (∫ x in α..β, u x * v₂ x) = ∫ x in α..β, v₂ x * u x := by
    congr 1; funext x; ring
  rw [e1, e2, I1, I2, neg_neg]

/-- Integral over the line equals the integral over any interval containing `[−r, r]` strictly. -/
theorem integral_line_eq {r R : ℝ} (hR : r < R) {F : ℝ → ℝ} (hF : ∀ x, r < |x| → F x = 0) :
    (∫ x, F x) = ∫ x in (-R)..R, F x := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  rw [Function.mem_support] at hx
  have : |x| ≤ r := by
    by_contra h'
    exact hx (hF x (lt_of_not_ge h'))
  exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- **Integration by parts twice on the line**, for `F` compactly supported. -/
theorem ibp2_line {r : ℝ} {F F₁ F₂ G G₁ G₂ : ℝ → ℝ} (hF : C2Supp r F F₁ F₂) (hG : C2Fun G G₁ G₂) :
    (∫ x, F₂ x * G x) = ∫ x, F x * G₂ x := by
  have hr : r < |r| + 1 := by linarith [le_abs_self r]
  have hout : r < |(|r| + 1)| := by rw [abs_of_pos (by positivity)]; exact hr
  have hout' : r < |-(|r| + 1)| := by rw [abs_neg]; exact hout
  rw [integral_line_eq hr (fun x hx => by rw [hF.supp2 x hx, zero_mul]),
    integral_line_eq hr (fun x hx => by rw [hF.supp x hx, zero_mul])]
  exact ibp2_interval hF.toC2Fun hG (hF.supp _ hout') (hF.supp _ hout) (hF.supp1 _ hout')
    (hF.supp1 _ hout)

theorem C2Supp.shift {r : ℝ} {f f₁ f₂ : ℝ → ℝ} (h : C2Supp r f f₁ f₂) (u : ℝ) :
    C2Supp (r + |u|) (fun x => f (x + u)) (fun x => f₁ (x + u)) (fun x => f₂ (x + u)) := by
  have far : ∀ x, r + |u| < |x| → r < |x + u| := by
    intro x hx
    have := abs_sub (x + u) u
    rw [add_sub_cancel_right] at this
    linarith
  exact ⟨fun x => (h.d1 (x + u)).comp_add_const x u, fun x => (h.d2 (x + u)).comp_add_const x u,
    h.cont2.comp (continuous_id.add continuous_const), fun x hx => h.supp _ (far x hx),
    fun x hx => h.supp1 _ (far x hx), fun x hx => h.supp2 _ (far x hx)⟩

theorem C2Fun.shift {g g₁ g₂ : ℝ → ℝ} (h : C2Fun g g₁ g₂) (u : ℝ) :
    C2Fun (fun x => g (x + u)) (fun x => g₁ (x + u)) (fun x => g₂ (x + u)) :=
  ⟨fun x => (h.d1 (x + u)).comp_add_const x u, fun x => (h.d2 (x + u)).comp_add_const x u,
    h.cont2.comp (continuous_id.add continuous_const)⟩

/-- **`xcorr(f'', k) = xcorr(f, k'')`** at every shift. -/
theorem xcorr_deriv2 {a : ℝ} {f f₁ f₂ k k₁ k₂ : ℝ → ℝ} (hf : C2Supp a f f₁ f₂)
    (hk : C2Supp a k k₁ k₂) (u : ℝ) : xcorr f₂ k u = xcorr f k₂ u := by
  unfold xcorr
  have h1 : (∫ t, f₂ t * k (t + u)) = ∫ t, f t * k₂ (t + u) :=
    ibp2_line hf (hk.toC2Fun.shift u)
  have h2 : (∫ t, k t * f₂ (t + u)) = ∫ t, k₂ t * f (t + u) := by
    have := ibp2_line (hf.shift u) hk.toC2Fun
    calc (∫ t, k t * f₂ (t + u)) = ∫ t, f₂ (t + u) * k t := by congr 1; funext t; ring
      _ = ∫ t, f (t + u) * k₂ t := this
      _ = ∫ t, k₂ t * f (t + u) := by congr 1; funext t; ring
  rw [h1, h2]

/-- **The pole-free bilinear form commutes with `∂²`.** -/
theorem bil0_deriv2 {a : ℝ} {f f₁ f₂ k k₁ k₂ : ℝ → ℝ} (hf : C2Supp a f f₁ f₂)
    (hk : C2Supp a k k₁ k₂) : bil0 a f₂ k = bil0 a f k₂ := by
  unfold bil0 archX primeX
  simp only [xcorr_deriv2 hf hk]

/-- **`poleR(f'') = ¼·poleR(f)`**: `(e^{−u/2})'' = ¼·e^{−u/2}`. -/
theorem poleR_deriv2 {a : ℝ} (ha : 0 ≤ a) {f f₁ f₂ : ℝ → ℝ} (hf : C2Supp a f f₁ f₂) :
    poleR f₂ a = (1 / 4) * poleR f a := by
  have hE : C2Fun (fun u => Real.exp (-(u / 2))) (fun u => -(1 / 2) * Real.exp (-(u / 2)))
      (fun u => (1 / 4) * Real.exp (-(u / 2))) := by
    have h : ∀ x : ℝ, HasDerivAt (fun u : ℝ => -(u / 2)) (-(1 / 2)) x := by
      intro x
      have := (hasDerivAt_id x).const_mul (-(1 / 2) : ℝ)
      convert this using 1
      · funext u; simp only [id]; ring
      · ring
    refine ⟨fun x => ?_, fun x => ?_, by fun_prop⟩
    · convert (h x).exp using 1; ring
    · convert ((h x).exp.const_mul (-(1 / 2))) using 1; ring
  have hL : ∀ g : ℝ → ℝ, (∀ x, a < |x| → g x = 0) →
      poleR g a = ∫ x, g x * Real.exp (-(x / 2)) := fun g hg => poleR_eq_integral ha hg
  rw [hL f₂ hf.supp2, hL f hf.supp, ibp2_line hf hE, ← integral_const_mul]
  congr 1; funext x; ring

/-- **The full bilinear form of `Q` commutes with `∂²`**: `B(f'', k) = B(f, k'')`. -/
theorem bilQ_deriv2 {a : ℝ} (ha : 0 ≤ a) {f f₁ f₂ k k₁ k₂ : ℝ → ℝ} (hf : C2Supp a f f₁ f₂)
    (hk : C2Supp a k k₁ k₂) :
    bil0 a f₂ k + 2 * poleR f₂ a * poleR k a = bil0 a f k₂ + 2 * poleR f a * poleR k₂ a := by
  rw [bil0_deriv2 hf hk, poleR_deriv2 ha hf, poleR_deriv2 ha hk]; ring

/-! ## Flat ground states force a second ground state (round 48, Theorem C, smooth form) -/

theorem weilQ0_eq_bil0 {a : ℝ} {f : ℝ → ℝ} (hf : Probe a f) : weilQ0 a f = bil0 a f f := by
  have e := weilQ0_add_smul hf hf 1
  have e2 : (fun t => f t + 1 * f t) = fun t => (2 : ℝ) * f t := by funext t; ring
  rw [e2, weilQ0_smul] at e
  linarith

theorem normSq_eq_xcorr {f : ℝ → ℝ} (hf : MemLp f 2 volume) : normSq f = xcorr f f 0 := by
  have e := normSq_add_smul hf hf 1
  have e2 : (fun t => f t + 1 * f t) = fun t => (2 : ℝ) * f t := by funext t; ring
  rw [e2, normSq_smul] at e
  linarith

end Pilot1ca

#print axioms Pilot1ca.xcorr_deriv2
#print axioms Pilot1ca.bil0_deriv2
#print axioms Pilot1ca.poleR_deriv2
#print axioms Pilot1ca.bilQ_deriv2
