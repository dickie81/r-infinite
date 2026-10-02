import Mathlib
import T1bt
import Exterior

/-! # §11 roadmap, item 1: the target stated, and the reduction to RH proved

**(i) The objects, prime side only.** `weilQ a g` is Theorem 1bn(i)'s true form
`Q(g) = 2ĝ(i/2)² + (ψ(¼) − log π)‖g‖² + ∫₀^∞ [f(0) − f(u)] e^{u/2}/sinh u du − 2Σ Λ(n)n^{−1/2} f(log n)`
(`f` the autocorrelation) on real even probes supported in `[−a, a]`, `δ = 2a`: no zero of `ζ`
enters. `IsGroundState a g` is its normalised minimiser. Riemann's `Ξ(t) = ξ(½ + it)` is built from
Mathlib's `completedRiemannZeta₀`. Item 1's (a) is `HypD` (Hypothesis D of Theorem 1bu(ii): below
`T_D` the zero multisets of `ĝ₁` and `Ξ` coincide, as analytic orders) and (b) is `RealRooted`.

**(ii) The reductions, proved.**
* `zeros_on_line_below`: D at one support plus real-rootedness there puts every nontrivial zero of
  `riemannZeta` with `|t_ρ| < T_D` on the critical line (item 5's finite advance). Only the
  inclusion "every zero of `Ξ` below `T_D` is a zero of `ĝ₁`" is used.
* `rh_of_realRooted_limit`: real-rooted entire functions whose rescalings converge locally uniformly
  to `Ξ` give Mathlib's `RiemannHypothesis` (item 6's step). The Hurwitz lemma it needs is
  proved here from the maximum modulus principle, on any open set and for any closed target set
  (`hurwitz_closed_on`); `hurwitz_closed` and `hurwitz_real` are its special cases.
* `rh_of_ground_states`: the same for ground states, with `ĝ` proved entire. -/

open Real Filter Topology MeasureTheory Complex

noncomputable section

namespace Pilot1ca

open Pilot1bt

/-! ## (i) The prime-side objects -/

/-- The autocorrelation `f(u) = ∫ g(t) g(t + u) dt` (`= g ⋆ g̃` for even `g`). -/
def autocorr (g : ℝ → ℝ) (u : ℝ) : ℝ := ∫ t, g t * g (t + u)

/-- `‖g‖² = ∫ g²`. -/
def normSq (g : ℝ → ℝ) : ℝ := ∫ t, g t ^ 2

/-- `ĝ(i/2) = ∫_{−a}^{a} g(u) e^{−u/2} du`, real for real `g`. -/
def poleR (g : ℝ → ℝ) (a : ℝ) : ℝ := ∫ u in (-a)..a, g u * Real.exp (-(u / 2))

/-- The archimedean integrand `[f(0) − f(u)] e^{u/2}/sinh u`. -/
def archIntegrand (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  (autocorr g 0 - autocorr g u) * (Real.exp (u / 2) / Real.sinh u)

/-- **Weil's true form at half-support `a`** (Theorem 1bn(i), Suzuki's (2.11)): the pole term, the
constant `ψ(¼) − log π`, the archimedean integral and the prime sum. No zero of `ζ` enters. -/
def weilQ (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  2 * poleR g a ^ 2 + ((Complex.digamma (1 / 4)).re - Real.log π) * normSq g
    + (∫ u in Set.Ioi (0 : ℝ), archIntegrand g u)
    - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr g (Real.log n)

/-- Admissible probes at half-support `a`: real, even, supported in `[−a, a]`, square-integrable,
with the archimedean integral convergent (so that `weilQ` is the form, not a Bochner default). -/
structure Probe (a : ℝ) (g : ℝ → ℝ) : Prop where
  even : ∀ u, g (-u) = g u
  supp : ∀ u, a < |u| → g u = 0
  memL2 : MemLp g 2 volume
  arch : IntegrableOn (archIntegrand g) (Set.Ioi 0)

/-- **The ground state at support `δ = 2a`**: a normalised admissible probe minimising `Q`. -/
def IsGroundState (a : ℝ) (g : ℝ → ℝ) : Prop :=
  Probe a g ∧ normSq g = 1 ∧ ∀ h, Probe a h → normSq h = 1 → weilQ a g ≤ weilQ a h

theorem ghatC_I_div_two (g : ℝ → ℝ) (a : ℝ) : ghatC g a (I / 2) = (poleR g a : ℂ) := by
  unfold ghatC poleR
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro u _
  have e : I * (I / 2) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) := by
    push_cast
    linear_combination (u / 2 : ℂ) * I_mul_I
  simp only
  rw [e, ← ofReal_exp]
  push_cast
  ring

/-! ### Riemann's `ξ` and `Ξ` -/

/-- Riemann's `ξ(s) = ½s(s − 1)π^{−s/2}Γ(s/2)ζ(s)`, entire: `(s(s − 1)Λ₀(s) + 1)/2`. -/
def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- Riemann's `Ξ(t) = ξ(½ + it)`. -/
def Xi (t : ℂ) : ℂ := xi (1 / 2 + I * t)

theorem differentiable_xi : Differentiable ℂ xi := by
  have h := differentiable_completedZeta₀
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul h).add_const 1).div_const 2

theorem differentiable_Xi : Differentiable ℂ Xi :=
  differentiable_xi.comp ((differentiable_const _).add ((differentiable_const _).mul differentiable_id))

theorem xi_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have h1' : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  rw [completedRiemannZeta_eq, xi]
  field_simp
  ring

/-- A nontrivial zero of `ζ` is a zero of `ξ`. -/
theorem xi_eq_zero_of_nontrivial {s : ℂ} (hs : IsNontrivialZero s) : xi s = 0 := by
  obtain ⟨hre0, hre1⟩ := hs.mem_strip
  have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hre0; exact lt_irrefl _ hre0
  have h1 : s ≠ 1 := fun h => by rw [h, one_re] at hre1; exact lt_irrefl _ hre1
  have hz := hs.1
  rw [riemannZeta_def_of_ne_zero h0, div_eq_zero_iff] at hz
  rcases hz with hz | hz
  · rw [xi_eq h0 h1, hz]; ring
  · exact absurd hz (Gammaℝ_ne_zero_of_re_pos hre0)

theorem Xi_at_ordinate (s : ℂ) : Xi ((s - 1 / 2) / I) = xi s := by
  unfold Xi
  congr 1
  field_simp
  ring

/-- `ξ(2) = π/6 ≠ 0`, so `Ξ` is not identically zero. -/
theorem xi_two_ne_zero : xi 2 ≠ 0 := by
  rw [xi_eq two_ne_zero (by norm_num)]
  have hG : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hz := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
  rw [riemannZeta_two] at hz
  intro h
  have hΛ : completedRiemannZeta 2 = 0 := by
    have : (2 : ℂ) * (2 - 1) * completedRiemannZeta 2 = 0 := by
      have := congrArg (· * 2) h; simpa using this
    norm_num at this; exact this
  rw [hΛ, zero_div] at hz
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  exact (div_ne_zero (pow_ne_zero 2 hπ) (by norm_num : (6 : ℂ) ≠ 0)) hz

/-! ### Item 1's (a) and (b) as propositions -/

/-- **Hypothesis D at support `2a` below `T_D`** (Theorem 1bu(ii), item 1(a), item 5): the zero
multisets of `ĝ` and `Ξ` coincide in the disc `|z| < T_D` (equal analytic orders at every point). -/
def HypD (a : ℝ) (g : ℝ → ℝ) (TD : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ < TD → analyticOrderAt (ghatC g a) z = analyticOrderAt Xi z

/-- **Real-rootedness** (item 1(b), item 6): every zero of `ĝ` is real. -/
def RealRooted (a : ℝ) (g : ℝ → ℝ) : Prop := ∀ z : ℂ, ghatC g a z = 0 → z.im = 0

/-! ## (ii) The reductions -/

theorem re_eq_half_of_Xi_real {s : ℂ} (h : ((s - 1 / 2) / I).im = 0) : s.re = 1 / 2 := by
  have e : (s - 1 / 2) / I = -I * (s - 1 / 2) := by field_simp; rw [I_sq]; ring
  rw [e] at h
  simp at h
  linarith

/-- **The finite advance (item 5), proved**: if every zero of `Ξ` in `|z| < T` is a zero of `F`
(the direction of D that matters) and `F`'s zeros there are real, every nontrivial zero `ρ` of
`riemannZeta` with `|t_ρ| < T`, `t_ρ = (ρ − ½)/i`, has `Re ρ = ½`. -/
theorem zeros_on_line_below {F : ℂ → ℂ} {T : ℝ}
    (hD : ∀ z : ℂ, ‖z‖ < T → analyticOrderAt Xi z ≠ 0 → analyticOrderAt F z ≠ 0)
    (hRR : ∀ z : ℂ, ‖z‖ < T → F z = 0 → z.im = 0) :
    ∀ s, IsNontrivialZero s → ‖(s - 1 / 2) / I‖ < T → s.re = 1 / 2 := by
  intro s hs hT
  set t := (s - 1 / 2) / I
  have hXi : Xi t = 0 := by rw [Xi_at_ordinate]; exact xi_eq_zero_of_nontrivial hs
  have hord : analyticOrderAt Xi t ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨differentiable_Xi.analyticAt t, hXi⟩
  have hF := (analyticOrderAt_ne_zero.1 (hD t hT hord)).2
  exact re_eq_half_of_Xi_real (hRR t hT hF)

/-- **Item 1 at one support, as the roadmap states it**: a ground state satisfying D below `T_D` and
real-rooted puts every zeta zero with `|t_ρ| < T_D` on the line. -/
theorem finite_advance {a TD : ℝ} {g : ℝ → ℝ} (_hg : IsGroundState a g) (hD : HypD a g TD)
    (hRR : RealRooted a g) :
    ∀ s, IsNontrivialZero s → ‖(s - 1 / 2) / I‖ < TD → s.re = 1 / 2 :=
  zeros_on_line_below (fun z hz h => by rw [hD z hz]; exact h) (fun z _ h => hRR z h)

/-- **Hurwitz for a closed set, on an open set `U`.** -/
theorem hurwitz_closed_on {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ n, Differentiable ℂ (F n)) (hf : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hnz : ∃ w, f w ≠ 0) {S : Set ℂ} (hS : IsClosed S) (hzeros : ∀ n z, F n z = 0 → z ∈ S) :
    ∀ z₀ ∈ U, f z₀ = 0 → z₀ ∈ S := by
  intro z₀ hU0 hz₀
  by_contra hS0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hS.isOpen_compl.inter hU) z₀ ⟨hS0, hU0⟩
  have hiso : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
    rcases (hf.analyticAt z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hnz
      have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z₀) (h.mono fun z hz => by simp [hz])
      exact hw (by simpa using hall (Set.mem_univ w))
    · exact h
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hiso)
  set r := min (ε / 2) (ρ / 2) with hr_def
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hne : (Metric.sphere z₀ r).Nonempty := ⟨z₀ + r, by simp [abs_of_pos hr]⟩
  obtain ⟨w, hwS, hwmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn hne
    (hf.continuous.norm.continuousOn)
  have hfS : ∀ z ∈ Metric.sphere z₀ r, f z ≠ 0 := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    apply hεf (by rw [dist_eq_norm, hz]; exact hrε)
    intro h; rw [h, sub_self, norm_zero] at hz; exact hr.ne hz
  set m := ‖f w‖ with hm_def
  have hm : 0 < m := norm_pos_iff.2 (hfS w hwS)
  have hsub : Metric.closedBall z₀ r ⊆ U := fun z hz =>
    (hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hrρ)).2
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hsub
    (isCompact_closedBall z₀ r)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif (m / 2) (by linarith)).exists
  have hnoz : ∀ z ∈ Metric.closedBall z₀ r, F n z ≠ 0 := by
    intro z hz h
    have hzS := hzeros n z h
    exact (hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hrρ)).1 hzS
  have hbound : ∀ z ∈ frontier (Metric.ball z₀ r), ‖(F n z)⁻¹‖ ≤ (m / 2)⁻¹ := by
    intro z hz
    rw [frontier_ball z₀ hr.ne'] at hz
    have h1 := hn z (Metric.sphere_subset_closedBall hz)
    have h2 : m ≤ ‖f z‖ := hwmin hz
    rw [dist_eq_norm] at h1
    have h3 : m / 2 ≤ ‖F n z‖ := by
      have := norm_sub_norm_le (f z) (F n z)
      linarith
    rw [norm_inv]
    exact inv_anti₀ (by linarith) h3
  have hdiff : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (Metric.ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact ((hF n).differentiableOn).inv hnoz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff hbound
    (subset_closure (Metric.mem_ball_self hr))
  have hz0 := hn z₀ (Metric.mem_closedBall_self hr.le)
  rw [hz₀, dist_eq_norm, zero_sub, norm_neg] at hz0
  have hFz0 : F n z₀ ≠ 0 := hnoz z₀ (Metric.mem_closedBall_self hr.le)
  rw [norm_inv] at hmax
  have hpos : 0 < ‖F n z₀‖ := norm_pos_iff.2 hFz0
  have := (inv_le_inv₀ hpos (by linarith)).1 hmax
  linarith

/-- **Hurwitz for a closed set.** If entire `F n → f` locally uniformly, `f ≢ 0`, and every zero of
every `F n` lies in the closed set `S`, then every zero of `f` lies in `S`. -/
theorem hurwitz_closed {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (hf : Differentiable ℂ f) (hconv : TendstoLocallyUniformly F f atTop)
    (hnz : ∃ w, f w ≠ 0) {S : Set ℂ} (hS : IsClosed S) (hzeros : ∀ n z, F n z = 0 → z ∈ S) :
    ∀ z₀, f z₀ = 0 → z₀ ∈ S := fun z₀ hz₀ =>
  hurwitz_closed_on isOpen_univ hF hf ((tendstoLocallyUniformlyOn_univ).2 hconv) hnz hS hzeros z₀
    (Set.mem_univ _) hz₀

/-- **A Hurwitz-type lemma**: if entire `F n → f` locally uniformly, `f ≢ 0`, and every `F n` has
only real zeros, then `f` has only real zeros (`hurwitz_closed` with `S = ℝ`). -/
theorem hurwitz_real {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (hf : Differentiable ℂ f) (hconv : TendstoLocallyUniformly F f atTop)
    (hnz : ∃ w, f w ≠ 0) (hreal : ∀ n z, F n z = 0 → z.im = 0) :
    ∀ z₀, f z₀ = 0 → z₀.im = 0 :=
  hurwitz_closed (S := {z | z.im = 0}) hF hf hconv hnz
    (isClosed_eq continuous_im continuous_const) hreal

/-- **Item 6's step, proved**: real-rooted entire functions `F n` with nonzero scalars `c n` such
that `c n · F n → Ξ` locally uniformly give **Mathlib's `RiemannHypothesis`**. -/
theorem rh_of_realRooted_limit {F : ℕ → ℂ → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (hreal : ∀ n z, F n z = 0 → z.im = 0) {c : ℕ → ℂ} (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformly (fun n z => c n * F n z) Xi atTop) : RiemannHypothesis := by
  have hXi : ∀ z, Xi z = 0 → z.im = 0 :=
    hurwitz_real (fun n => (differentiable_const _).mul (hF n)) differentiable_Xi hconv
      ⟨(2 - 1 / 2) / I, by rw [Xi_at_ordinate]; exact xi_two_ne_zero⟩
      (fun n z h => hreal n z ((mul_eq_zero.1 h).resolve_left (hc n)))
  intro s hz htriv _
  have hs : IsNontrivialZero s := ⟨hz, htriv⟩
  apply re_eq_half_of_Xi_real
  apply hXi
  rw [Xi_at_ordinate]
  exact xi_eq_zero_of_nontrivial hs

/-! ### `ĝ` is entire -/

theorem ghatC_differentiable {g : ℝ → ℝ} {a : ℝ} (hg : IntervalIntegrable g volume (-a) a) :
    Differentiable ℂ (ghatC g a) := by
  intro z₀
  have hgm : AEStronglyMeasurable (fun u => ((g u : ℝ) : ℂ)) (volume.restrict (Set.uIoc (-a) a)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.def'.aestronglyMeasurable)
  set B := |a| * Real.exp ((‖z₀‖ + 1) * |a|) with hB
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -a) (b := a) (x₀ := z₀) (s := Metric.ball z₀ 1)
    (F := fun z u => ((g u : ℝ) : ℂ) * Complex.exp (I * z * u))
    (F' := fun z u => ((g u : ℝ) : ℂ) * (I * u * Complex.exp (I * z * u)))
    (bound := fun u => |g u| * B) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => hgm.mul (by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (I * z * u)).aestronglyMeasurable)
    ?_ (hgm.mul (by fun_prop : Continuous fun u : ℝ =>
      I * u * Complex.exp (I * z₀ * u)).aestronglyMeasurable)
    ?_ (hg.abs.mul_const B) ?_
  · exact (key.2).differentiableAt
  · -- integrability at `z₀`: bounded continuous factor times integrable `g`
    have hc : ContinuousOn (fun u : ℝ => Complex.exp (I * z₀ * u)) (Set.uIcc (-a) a) :=
      (by fun_prop : Continuous fun u : ℝ => Complex.exp (I * z₀ * u)).continuousOn
    have hgC : IntervalIntegrable (fun u => ((g u : ℝ) : ℂ)) volume (-a) a :=
      ⟨hg.1.ofReal, hg.2.ofReal⟩
    exact hgC.mul_continuousOn hc
  · refine Eventually.of_forall fun u hu z hz => ?_
    have hua : |u| ≤ |a| := by
      have h1 := le_abs_self a
      have h2 := neg_abs_le a
      rcases Set.mem_uIoc.1 hu with h | h
      · exact abs_le.2 ⟨by linarith [h.1], by linarith [h.2]⟩
      · exact abs_le.2 ⟨by linarith [h.1], by linarith [h.2]⟩
    have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    rw [norm_mul, norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (I * z * u).re ≤ (‖z₀‖ + 1) * |a| := by
      have e : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [mul_re]
      rw [e]
      have := abs_im_le_norm z
      calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
        _ = |z.im| * |u| := abs_mul _ _
        _ ≤ (‖z₀‖ + 1) * |a| := mul_le_mul (by linarith) hua (abs_nonneg _) (by positivity)
    calc |g u| * (|u| * Real.exp (I * z * u).re)
        ≤ |g u| * (|a| * Real.exp ((‖z₀‖ + 1) * |a|)) := by
          gcongr
      _ = |g u| * B := rfl
  · refine Eventually.of_forall fun u _ z _ => ?_
    have h := ((((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)).cexp).const_mul
      ((g u : ℝ) : ℂ)
    refine h.congr_deriv ?_
    simp only [id]
    ring

/-- **The roadmap's endpoint, as a theorem**: ground states `g n` at supports `2a n` that are
real-rooted, with nonzero scalars `c n` making `c n · ĝ_n → Ξ` locally uniformly (what 1bu(ii)
derives from D with `ε(δ) → 0`), give **Mathlib's `RiemannHypothesis`**. -/
theorem rh_of_ground_states {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n)) {c : ℕ → ℂ} (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformly (fun n z => c n * ghatC (g n) (a n) z) Xi atTop) :
    RiemannHypothesis :=
  rh_of_realRooted_limit (fun n => ghatC_differentiable (hint n)) (fun n => hRR n) hc hconv

end Pilot1ca

#print axioms Pilot1ca.ghatC_I_div_two
#print axioms Pilot1ca.differentiable_Xi
#print axioms Pilot1ca.xi_eq_zero_of_nontrivial
#print axioms Pilot1ca.xi_two_ne_zero
#print axioms Pilot1ca.zeros_on_line_below
#print axioms Pilot1ca.finite_advance
#print axioms Pilot1ca.hurwitz_closed_on
#print axioms Pilot1ca.hurwitz_real
#print axioms Pilot1ca.rh_of_realRooted_limit
#print axioms Pilot1ca.ghatC_differentiable
#print axioms Pilot1ca.rh_of_ground_states
