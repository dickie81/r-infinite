import Mathlib
import WeilCriterion
import Zeta

/-! # Discharging the remaining classical inputs over the zeros of `ζ` (round 157)

* `hadamard_zeta`: **Hadamard's identity** `Σ_ρ 1/(ρ(1 − ρ)) = 2 + γ − log 4π`, summed over the
  nontrivial zeros of `ζ` with multiplicity. Proof: the logarithmic derivative of Hadamard's product
  (`hasSum_logDeriv_Xi`) at `t = −i/2`, where `Ξ(−i/2) = ξ(1) = ½`, gives
  `Σ_u 1/(u + ¼) = ξ′(1)/ξ(1) = Λ₀(1)`, and Mathlib's `completedRiemannZeta₀_one` evaluates `Λ₀(1)`.
* `pole_free_form_negative_zeta_explicit`: **Theorem 1bt(i)** with Hadamard's identity and the
  explicit formula discharged. The one input left is the first zero's height, `γ₁ ≥ 14`.
* `pinned_zeta`: `Unconditional.lean`'s pinning theorem with the explicit formula (`hQ`), the
  strip (`hstrip`), and the tail summability (`hS`) discharged. Left: verified RH to height `H`
  (numeric), and monotonicity of the probe (a hypothesis on `g`, observed for ground states).

Classical analysis only: no bearing on RH.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## Hadamard's identity over the zeros of `ζ` -/

theorem hasSum_bool_prod {X : Type*} {g : X → ℂ} {s : ℂ} (hg : HasSum g s) :
    HasSum (fun p : Bool × X => g p.2) (s + s) := by
  have h := HasSum.sum (f := fun q : X ⊕ X => g (Sum.elim id id q)) hg hg
  have e := ((Equiv.boolProdEquivSum X).hasSum_iff (f := fun q : X ⊕ X => g (Sum.elim id id q))
    (a := s + s)).2 h
  refine e.congr_fun fun p => ?_
  rcases p with ⟨b, x⟩
  cases b <;> rfl

theorem Xi_neg_half : Xi (-(I / 2)) = 1 / 2 := by
  have e : (1 / 2 + I * -(I / 2) : ℂ) = 1 := by
    ring_nf; rw [I_sq]; norm_num
  unfold Xi xi; rw [e]; simp

theorem hasDerivAt_xi_one : HasDerivAt xi (completedRiemannZeta₀ 1 / 2) 1 := by
  have hΛ := (differentiable_completedZeta₀ 1).hasDerivAt
  have h := ((((hasDerivAt_id (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)).mul hΛ).add_const
    1).div_const 2
  have e : xi = fun s => (id s * (id s - 1) * completedRiemannZeta₀ s + 1) / 2 := by
    funext s; rfl
  rw [e]
  convert h using 1
  simp

/-- `Ξ′/Ξ(−i/2) = i·ξ′(1)/ξ(1) = i·Λ₀(1)`. -/
theorem logDeriv_Xi_neg_half : logDeriv Xi (-(I / 2)) = I * completedRiemannZeta₀ 1 := by
  have hg : HasDerivAt (fun z : ℂ => 1 / 2 + I * z) I (-(I / 2)) := by
    simpa using ((hasDerivAt_id (-(I / 2))).const_mul I).const_add (1 / 2)
  have hx : HasDerivAt xi (completedRiemannZeta₀ 1 / 2) ((fun z : ℂ => 1 / 2 + I * z) (-(I / 2))) := by
    have e : (fun z : ℂ => 1 / 2 + I * z) (-(I / 2)) = 1 := by
      simp only; ring_nf; rw [I_sq]; norm_num
    rw [e]; exact hasDerivAt_xi_one
  have hX : HasDerivAt Xi (completedRiemannZeta₀ 1 / 2 * I) (-(I / 2)) := HasDerivAt.comp (h₂ := xi) (h := fun z : ℂ => 1 / 2 + I * z) (-(I / 2)) hx hg
  rw [logDeriv_apply, hX.deriv, Xi_neg_half]
  ring

/-- `Σ_u 1/(u + ¼) = Λ₀(1)` over the zeros `u` of `Ξ(√w)`. -/
theorem hasSum_inv_quarter :
    HasSum (fun i : ZeroIdx (sqF Xi) => 1 / (i.1 + 1 / 4)) (completedRiemannZeta₀ 1) := by
  have h := hasSum_logDeriv_Xi (t := -(I / 2)) (by rw [Xi_neg_half]; norm_num)
  rw [logDeriv_Xi_neg_half] at h
  have e : ∀ i : ZeroIdx (sqF Xi), 2 * -(I / 2) / ((-(I / 2)) ^ 2 - i.1) = I * (1 / (i.1 + 1 / 4)) := by
    intro i
    have h2 : (-(I / 2)) ^ 2 - i.1 = -(i.1 + 1 / 4) := by ring_nf; rw [I_sq]; ring
    rw [h2, show 2 * -(I / 2) = -I by ring, neg_div_neg_eq, mul_one_div]
  simp_rw [e] at h
  exact (hasSum_mul_left_iff I_ne_zero).1 h

theorem rhoXi_mul_one_sub (p : Bool × ZeroIdx (sqF Xi)) :
    rhoXi p * (1 - rhoXi p) = p.2.1 + 1 / 4 := by
  unfold rhoXi
  split_ifs
  · rw [← tau_sq p.2]; ring_nf; rw [I_sq]; ring
  · rw [← tau_sq p.2]; ring_nf; rw [I_sq]; ring

/-- **Hadamard's identity, proved**: `Σ_ρ 1/(ρ(1 − ρ)) = 2 + γ − log 4π` over the nontrivial zeros
of `ζ` with multiplicity. -/
theorem hadamard_zeta :
    HasSum (fun p => 1 / (zetaZeroFamily p * (1 - zetaZeroFamily p)))
      ((2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) : ℂ) := by
  have h2 := hasSum_bool_prod hasSum_inv_quarter
  have hval : completedRiemannZeta₀ 1 + completedRiemannZeta₀ 1
      = ((2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) : ℂ) := by
    rw [completedRiemannZeta₀_one]
    have hl : Complex.log (4 * (π : ℂ)) = ((Real.log (4 * π) : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
    rw [hl]; push_cast; ring
  rw [hval] at h2
  have hX : HasSum (fun p : Bool × ZeroIdx (sqF Xi) => 1 / (rhoXi p * (1 - rhoXi p)))
      ((2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) : ℂ) :=
    h2.congr_fun fun p => by rw [rhoXi_mul_one_sub]
  have := (zetaEquiv.hasSum_iff (f := fun p => 1 / (rhoXi p * (1 - rhoXi p)))).2 hX
  simpa [Function.comp_def, rhoXi_zetaEquiv] using this

/-! ## Theorem 1bt(i) with the explicit formula and Hadamard's identity discharged -/

/-- The right-hand side of Weil's explicit formula (`WeilExplicit`). -/
def weilRHS (h : ℂ → ℂ) (hR : ℝ → ℝ) : ℂ :=
  h (I / 2) + h (-(I / 2))
    + ((-(gh hR 0 * Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe r)
      - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n) : ℝ) : ℂ)

theorem WeilExplicit.hasSum_rhs {ι : Type*} {ρ : ι → ℂ} {h : ℂ → ℂ} {hR : ℝ → ℝ}
    (H : WeilExplicit ρ h hR) : HasSum (fun i => h ((ρ i - 1 / 2) / I)) (weilRHS h hR) := H.2

/-- The real values of the witness' squared transform on `ℝ`. -/
def hRbt (a r : ℝ) : ℝ := (ghat a r).re ^ 2

theorem ghat_eq_ghatC (a : ℝ) : ghat a = ghatC (fun u => Real.cosh (u / 2)) a := rfl

theorem V_nonneg (a : ℝ) : 0 ≤ V a := by
  unfold V; linarith [Real.one_le_cosh (a / 2)]

/-- **`ĝ_a²` is a strip test function** (the 1bt witness `cosh(u/2)` on `[−a, a]`). -/
theorem striptest_ghat_bt {a : ℝ} (ha : 0 ≤ a) : ∃ K, StripTest (fun z => ghat a z ^ 2) K := by
  have hint : IntervalIntegrable (fun u : ℝ => Real.cosh (u / 2)) volume (-a) a :=
    (by fun_prop : Continuous fun u : ℝ => Real.cosh (u / 2)).intervalIntegrable _ _
  obtain ⟨K, hK⟩ := ghat_strip_of_inv ha (B := V a * Real.exp a)
    (mul_nonneg (V_nonneg a) (Real.exp_pos a).le) hint fun t ht ht0 => by
      rw [← ghat_eq_ghatC]
      refine (ghat_bound a ha t ht0).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (V_nonneg a)) (norm_nonneg _))
      exact mul_le_of_le_one_right ha (abs_le.2 ⟨ht.1, ht.2⟩)
  exact ⟨K, striptest_sq (ghatC_differentiable hint) hK⟩

theorem weilExplicit_ghat_bt {a : ℝ} (ha : 0 ≤ a) :
    WeilExplicit zetaZeroFamily (fun z => ghat a z ^ 2) (hRbt a) := by
  obtain ⟨K, hK⟩ := striptest_ghat_bt ha
  have hev : ∀ u : ℝ, Real.cosh (-u / 2) = Real.cosh (u / 2) := fun u => by
    rw [neg_div, Real.cosh_neg]
  have hint : IntervalIntegrable (fun u : ℝ => Real.cosh (u / 2)) volume (-a) a :=
    (by fun_prop : Continuous fun u : ℝ => Real.cosh (u / 2)).intervalIntegrable _ _
  refine weilExplicit_zeta hK (fun t => ?_) (fun r => ?_)
  · simp only [ghat_eq_ghatC]; rw [ghatC_even (fun u => hev u)]
  · have him := ghatC_im_eq_zero (fun u => hev u) hint r
    rw [← ghat_eq_ghatC] at him
    have e : ghat a r = ((ghat a r).re : ℂ) := Complex.ext (by simp) (by simp [him])
    unfold hRbt; rw [e]; push_cast; simp

/-- **Theorem 1bt(i) over the zeros of `ζ`, with Hadamard's identity and Weil's explicit formula
discharged.** The value of Weil's form on the witness is the explicit formula's prime side
`W = weilRHS`; it satisfies `‖W‖ < 2(a + sinh a)²`, so the pole-free form is negative. One named
input remains: the first zero's height `γ₁ ≥ 14`. -/
theorem pole_free_form_negative_zeta_explicit
    (h_height : ∀ p, 14 ≤ |(zetaZeroFamily p).im|) (a : ℝ) (ha : 1 / 5 ≤ a) :
    ‖weilRHS (fun z => ghat a z ^ 2) (hRbt a)‖ < 2 * (a + Real.sinh a) ^ 2 ∧
      (weilRHS (fun z => ghat a z ^ 2) (hRbt a) - 2 * ghat a (I / 2) ^ 2).re < 0 :=
  pole_free_form_negative_zeta h_height hadamard_zeta a ha _
    (weilExplicit_ghat_bt (by linarith)).hasSum_rhs

/-! ## The pinning theorem with the explicit formula, strip and tail discharged -/

theorem summable_four_zeta :
    Summable fun p => ‖1 / (((zetaZeroFamily p - 1 / 2) / I) ^ 2 + 4)‖ := by
  have := (zetaEquiv.summable_iff (f := fun p => ‖1 / (((rhoXi p - 1 / 2) / I) ^ 2 + 4)‖)).2
    summable_four_Xi
  simpa [Function.comp_def, rhoXi_zetaEquiv] using this

theorem im_ordinate_zeta (p : Σ w : NontrivialZero, Fin (zeroMult w)) :
    |((zetaZeroFamily p - 1 / 2) / I).im| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := p.1.2.mem_strip
  have e : ((zetaZeroFamily p - 1 / 2) / I).im = 1 / 2 - (zetaZeroFamily p).re := by
    simp [Complex.div_I]
  rw [e, abs_le]; change 0 < (zetaZeroFamily p).re at h0
  change (zetaZeroFamily p).re < 1 at h1
  constructor <;> linarith

/-- The tail sum `Σ_{|Re t| > H} (Re t)⁻²` over the zeros of `ζ` converges, for `H ≥ 1`. -/
theorem summable_tail_zeta {H : ℝ} (hH : 1 ≤ H) :
    Summable fun p => if H < |((zetaZeroFamily p - 1 / 2) / I).re|
      then 1 / ((zetaZeroFamily p - 1 / 2) / I).re ^ 2 else 0 := by
  refine Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) (fun p => ?_)
    (summable_four_zeta.mul_left 6)
  split_ifs with h
  · set t := (zetaZeroFamily p - 1 / 2) / I
    have him := im_ordinate_zeta p
    have hre : 1 ≤ t.re ^ 2 := by nlinarith [abs_nonneg t.re, sq_abs t.re]
    have him2 : t.im ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg t.im, sq_abs t.im]
    have hlow : t.re ^ 2 - t.im ^ 2 + 4 ≤ ‖t ^ 2 + 4‖ := by
      have := Complex.re_le_norm (t ^ 2 + 4)
      simp [sq, Complex.mul_re] at this ⊢; linarith
    have hup : ‖t ^ 2 + 4‖ ≤ 6 * t.re ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
      simp; nlinarith
    have hpos : 0 < ‖t ^ 2 + 4‖ := by linarith
    rw [norm_div, norm_one, ← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) hpos]
    linarith
  · positivity

/-- **The pinning theorem over the zeros of `ζ`.** For an even, nonnegative probe non-increasing on
`[0, a]`, with `Q = weilQ a g` and `S` the zero-tail sum above height `H ≥ 1`: `ĝ` has a zero within
`√(Q + B²S)/m` of every zero verified on the line below `H` near which `|ĝ′| ≥ m`,
`B = 2g(0)cosh(a/2)`. The explicit formula, the strip and the tail's convergence are proved; the
remaining hypotheses are RH verified to height `H` (`hRH`, numeric) and the probe's monotonicity. -/
theorem pinned_zeta {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hp : Probe a g)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u) {H : ℝ} (hH : 1 ≤ H)
    (hRH : ∀ p, |((zetaZeroFamily p - 1 / 2) / I).re| ≤ H → ((zetaZeroFamily p - 1 / 2) / I).im = 0)
    (j : Σ w : NontrivialZero, Fin (zeroMult w)) (hj : |((zetaZeroFamily j - 1 / 2) / I).re| ≤ H)
    {m r : ℝ} (hm : 0 < m)
    (hr : Real.sqrt (weilQ a g + (2 * g 0 * Real.cosh (a / 2)) ^ 2 *
      (∑' p, if H < |((zetaZeroFamily p - 1 / 2) / I).re|
        then 1 / ((zetaZeroFamily p - 1 / 2) / I).re ^ 2 else 0)) / m ≤ r)
    (hc : ContinuousOn (fun x : ℝ => (ghatC g a x).re)
      (Icc (((zetaZeroFamily j - 1 / 2) / I).re - r) (((zetaZeroFamily j - 1 / 2) / I).re + r)))
    (hd : DifferentiableOn ℝ (fun x : ℝ => (ghatC g a x).re)
      (Ioo (((zetaZeroFamily j - 1 / 2) / I).re - r) (((zetaZeroFamily j - 1 / 2) / I).re + r)))
    (hslope : (∀ x ∈ Ioo (((zetaZeroFamily j - 1 / 2) / I).re - r)
        (((zetaZeroFamily j - 1 / 2) / I).re + r), m ≤ deriv (fun x : ℝ => (ghatC g a x).re) x) ∨
      (∀ x ∈ Ioo (((zetaZeroFamily j - 1 / 2) / I).re - r)
        (((zetaZeroFamily j - 1 / 2) / I).re + r), deriv (fun x : ℝ => (ghatC g a x).re) x ≤ -m)) :
    ∃ x ∈ Icc (((zetaZeroFamily j - 1 / 2) / I).re - Real.sqrt (weilQ a g + (2 * g 0 * Real.cosh (a / 2)) ^ 2 *
        (∑' p, if H < |((zetaZeroFamily p - 1 / 2) / I).re|
          then 1 / ((zetaZeroFamily p - 1 / 2) / I).re ^ 2 else 0)) / m)
      (((zetaZeroFamily j - 1 / 2) / I).re + Real.sqrt (weilQ a g + (2 * g 0 * Real.cosh (a / 2)) ^ 2 *
        (∑' p, if H < |((zetaZeroFamily p - 1 / 2) / I).re|
          then 1 / ((zetaZeroFamily p - 1 / 2) / I).re ^ 2 else 0)) / m), (ghatC g a x).re = 0 := by
  have hQ := weilQ_eq_zero_sum hp ha (weilExplicit_antitone_zeta ha hp hmono hnn)
  exact pinned_unconditional ha hp.even hmono hnn hp.intervalIntegrable (by linarith)
    hQ.summable hQ.tsum_eq.symm hRH (fun p => im_ordinate_zeta p) (summable_tail_zeta hH) le_rfl
    j hj hm hr hc hd hslope

end Pilot1ca

#print axioms Pilot1ca.hadamard_zeta
#print axioms Pilot1ca.weilExplicit_ghat_bt
#print axioms Pilot1ca.pole_free_form_negative_zeta_explicit
#print axioms Pilot1ca.summable_tail_zeta
#print axioms Pilot1ca.pinned_zeta
