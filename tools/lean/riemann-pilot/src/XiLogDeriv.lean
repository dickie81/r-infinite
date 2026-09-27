import Mathlib
import XiBounds

/-! # The logarithmic derivative of `Ξ` (round 156, part 2)

* **`Xi_zero_im`.** Every zero of `Ξ` has `|Im t| < ½` (`ζ ≠ 0` on `Re s ≥ 1`, and `ξ(1 − s) = ξ(s)`).
* **`hasSum_logDeriv_Xi`.** Off the zeros, `Ξ′/Ξ(t) = Σ_u 2t/(t² − u)` over the zero family of
  `F(w) = Ξ(√w)` (with multiplicity): the logarithmic derivative of Hadamard's product (round 20),
  by Mathlib's `logDeriv_tprod_eq_tsum` and locally uniform convergence.
-/

open Real Filter Topology Complex Set

noncomputable section

namespace Pilot1ca

/-- `ξ(s) ≠ 0` for `Re s ≥ 1`. -/
theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1]; simp [xi]
  have h0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  rw [xi_eq h0 h1]
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    rw [riemannZeta_def_of_ne_zero h0, h, zero_div] at hz
    exact hz rfl
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 hs1) hΛ) two_ne_zero

/-- **The zeros of `Ξ` lie in `|Im t| < ½`.** -/
theorem Xi_zero_im {t : ℂ} (ht : Xi t = 0) : |t.im| < 1 / 2 := by
  have hre : (1 / 2 + I * t).re = 1 / 2 - t.im := by simp; ring
  rw [abs_lt]
  constructor
  · by_contra h; push Not at h
    exact xi_ne_zero_of_one_le_re (by rw [hre]; linarith) ht
  · by_contra h; push Not at h
    have h1 : 1 ≤ (1 - (1 / 2 + I * t)).re := by simp; linarith
    apply xi_ne_zero_of_one_le_re h1
    rw [xi_one_sub]; exact ht

/-- The zeros `u` of `F(w) = Ξ(√w)` are nonzero. -/
theorem ZeroIdx_ne_zero (i : ZeroIdx (sqF Xi)) : i.1 ≠ 0 := by
  intro h
  have hz : sqF Xi i.1 = 0 := (ordN_ne_zero_iff (sqF_differentiable differentiable_Xi Xi_even)
    (by rw [sqF_zero]; exact Xi_zero_ne_zero) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))
  rw [h, sqF_zero] at hz
  exact Xi_zero_ne_zero hz

/-- **The logarithmic derivative of Hadamard's product**: off the zeros,
`Ξ′(t)/Ξ(t) = Σ_u 2t/(t² − u)` over the zeros `u` of `Ξ(√w)`, with multiplicity. -/
theorem hasSum_logDeriv_Xi {t : ℂ} (ht : Xi t ≠ 0) :
    HasSum (fun i : ZeroIdx (sqF Xi) => 2 * t / (t ^ 2 - i.1)) (logDeriv Xi t) := by
  have H := hadamardW_Xi xiGrowth Xi_zero_ne_zero
  set w : ZeroIdx (sqF Xi) → ℂ := fun i => i.1⁻¹
  have hw : Summable fun i => ‖w i‖ := H.summ
  set f : ZeroIdx (sqF Xi) → ℂ → ℂ := fun i z => 1 + -(z ^ 2 * w i)
  have hprod : ∀ z, HasProd (fun i => f i z) (Xi z / Xi 0) := fun z => by
    have := H.prod z; simpa [f, sub_eq_add_neg] using this
  have hX0 := Xi_zero_ne_zero
  -- no factor vanishes at `t`
  have hf : ∀ i, f i t ≠ 0 := by
    intro i h0
    have := (hprod t).unique (hasProd_zero_of_exists_eq_zero ⟨i, h0⟩)
    exact ht (by rw [div_eq_zero_iff] at this; tauto)
  set R := ‖t‖ + 1
  set s : Set ℂ := Metric.ball 0 R
  have hs : IsOpen s := Metric.isOpen_ball
  have hts : t ∈ s := by simp [s, R]
  have hd : ∀ i, DifferentiableOn ℂ (f i) s := fun i =>
    Differentiable.differentiableOn (by simp only [f]; fun_prop)
  have htend : MultipliableLocallyUniformlyOn f s := by
    refine Summable.multipliableLocallyUniformlyOn_one_add (f := fun i z => -(z ^ 2 * w i))
      (u := fun i => R ^ 2 * ‖w i‖) hs (hw.mul_left _) (Eventually.of_forall fun i z hz => ?_)
      (fun i => Continuous.continuousOn (by fun_prop))
    rw [norm_neg, norm_mul, norm_pow]
    have : ‖z‖ ≤ R := le_of_lt (by simpa [s] using hz)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) this 2) (norm_nonneg _)
  -- the termwise logarithmic derivatives
  have hlog : ∀ i, logDeriv (f i) t = 2 * t / (t ^ 2 - i.1) := by
    intro i
    have hu := ZeroIdx_ne_zero i
    have hfi := hf i
    simp only [f, w] at hfi
    have hd' : HasDerivAt (f i) (-(2 * t * w i)) t := by
      have := ((hasDerivAt_pow 2 t).mul_const (w i)).neg.const_add 1
      simpa [f] using this
    rw [logDeriv_apply, hd'.deriv]
    have ht2 : t ^ 2 - i.1 ≠ 0 := by
      intro h0
      apply hfi
      rw [show t ^ 2 = i.1 by linear_combination h0]
      field_simp; ring
    rw [div_eq_div_iff hfi ht2]
    simp only [w]
    field_simp
    ring
  have hm : Summable fun i => logDeriv (f i) t := by
    simp_rw [hlog]
    have hw0 := hw.tendsto_cofinite_zero
    have hev : ∀ᶠ i in cofinite, ‖w i‖ ≤ 1 / (2 * (‖t‖ ^ 2 + 1)) :=
      (Metric.tendsto_nhds.1 (by simpa using hw0) (1 / (2 * (‖t‖ ^ 2 + 1)))
        (by positivity)).mono fun i hi => by
        simpa using hi.le
    refine Summable.of_norm_bounded_eventually (hw.mul_left (4 * ‖t‖)) ?_
    filter_upwards [hev] with i hi
    have hu := ZeroIdx_ne_zero i
    have hwi : ‖w i‖ = ‖i.1‖⁻¹ := by simp [w]
    have hpos : 0 < ‖i.1‖ := norm_pos_iff.2 hu
    have hi' : ‖i.1‖⁻¹ ≤ (2 * (‖t‖ ^ 2 + 1))⁻¹ := by rw [← hwi]; simpa [one_div] using hi
    have hbig : 2 * (‖t‖ ^ 2 + 1) ≤ ‖i.1‖ := (inv_le_inv₀ hpos (by positivity)).1 hi'
    have hden : ‖i.1‖ / 2 ≤ ‖t ^ 2 - i.1‖ := by
      have := norm_sub_norm_le i.1 (t ^ 2)
      rw [norm_sub_rev, norm_pow] at this
      nlinarith [sq_nonneg ‖t‖]
    rw [norm_div, norm_mul, Complex.norm_two, hwi]
    calc 2 * ‖t‖ / ‖t ^ 2 - i.1‖ ≤ 2 * ‖t‖ / (‖i.1‖ / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 4 * ‖t‖ * ‖i.1‖⁻¹ := by field_simp; ring
  have hnez : ∏' i, f i t ≠ 0 := by rw [(hprod t).tprod_eq]; exact div_ne_zero ht hX0
  have key := logDeriv_tprod_eq_tsum hs hts hf hd hm htend hnez
  have hfun : (fun z => ∏' i, f i z) = fun z => Xi z * (Xi 0)⁻¹ := by
    funext z; rw [(hprod z).tprod_eq, div_eq_mul_inv]
  rw [hfun, logDeriv_mul_const t _ (inv_ne_zero hX0)] at key
  rw [key]
  simp_rw [← hlog]
  exact hm.hasSum


/-! ## `Ξ′/Ξ` on `Re s > 1` -/

theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = -(Real.log π : ℂ) / 2 + Complex.digamma (s / 2) / 2 := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hs2 : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := fun m h => by
    have := congrArg Complex.re h
    simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs2
  have hdG : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ hs2
  have hdiv : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hneg : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
    simpa using (hasDerivAt_id s).neg.div_const 2
  have hpow := hneg.const_cpow (c := (π : ℂ)) (Or.inl hπ)
  have hpow0 : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have e : Gammaℝ = fun z => (π : ℂ) ^ (-z / 2) * (Complex.Gamma ∘ fun z : ℂ => z / 2) z := by
    funext z; rfl
  rw [e, logDeriv_fun_mul s hpow0 hG hpow.differentiableAt (hdG.comp s hdiv.differentiableAt),
    logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z / 2) hdG hdiv.differentiableAt, hdiv.deriv, ← Complex.digamma_def, logDeriv_apply,
    hpow.deriv, ← Complex.ofReal_log Real.pi_pos.le]
  field_simp

/-- `ξ′/ξ = 1/s + 1/(s − 1) + Γℝ′/Γℝ + ζ′/ζ` on `Re s > 1`. -/
theorem logDeriv_xi {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s = 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; linarith
  set U : Set ℂ := {z | 1 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set P : ℂ → ℂ := fun z => z * (z - 1) * Gammaℝ z * riemannZeta z * (1 / 2)
  have hEq : ∀ z ∈ U, xi z = P z := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz'; linarith
    have hz1 : z ≠ 1 := fun h => by rw [h, one_re] at hz'; linarith
    have hGz : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    simp only [P]
    rw [xi_eq hz0 hz1, riemannZeta_def_of_ne_zero hz0]
    field_simp
  have hev : xi =ᶠ[𝓝 s] P := Filter.eventuallyEq_of_mem (hU.mem_nhds hs) hEq
  have hlog : logDeriv xi s = logDeriv P s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hEq s hs]
  rw [hlog]
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hdG : DifferentiableAt ℂ Gammaℝ s := by
    have hs2 : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := fun m h => by
      have := congrArg Complex.re h
      simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    exact (((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (π : ℂ)) (Or.inl hπ)).differentiableAt.mul
      ((Complex.differentiableAt_Gamma _ hs2).comp s ((hasDerivAt_id s).div_const 2).differentiableAt)
  have hdz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  simp only [P]
  rw [logDeriv_mul_const s _ (by norm_num : (1 / 2 : ℂ) ≠ 0),
    logDeriv_fun_mul (f := fun z => z * (z - 1) * Gammaℝ z) (g := riemannZeta) s
      (mul_ne_zero (mul_ne_zero hs0 hs1') hG) hz
      (((differentiableAt_id.mul (differentiableAt_id.sub_const 1))).mul hdG) hdz,
    logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1)) (g := Gammaℝ) s (mul_ne_zero hs0 hs1') hG
      (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hdG,
    logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hs0 hs1' differentiableAt_id
      (differentiableAt_id.sub_const 1)]
  have h1 : logDeriv (fun z : ℂ => z) s = 1 / s := logDeriv_id' s
  have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply]
    have := ((hasDerivAt_id s).sub_const 1).deriv
    simp only [id] at this
    rw [this]
  rw [h1, h2]

/-- **`Ξ′/Ξ` on the line `Re s > 1`**: with `s = ½ + it`,
`Ξ′(t)/Ξ(t) = i(1/s + 1/(s − 1) − (log π)/2 + ψ(s/2)/2 − Σ Λ(n)n^{−s})`. -/
theorem logDeriv_Xi_eq {t : ℂ} (ht : 1 < (1 / 2 + I * t).re) :
    logDeriv Xi t = I * (1 / (1 / 2 + I * t) + 1 / (1 / 2 + I * t - 1) - (Real.log π : ℂ) / 2
      + Complex.digamma ((1 / 2 + I * t) / 2) / 2
      - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + I * t)) := by
  set s := 1 / 2 + I * t
  have hg : HasDerivAt (fun z : ℂ => 1 / 2 + I * z) I t := by
    simpa using ((hasDerivAt_id t).const_mul I).const_add (1 / 2)
  have hdx : DifferentiableAt ℂ xi s := differentiable_xi s
  have e : Xi = xi ∘ fun z : ℂ => 1 / 2 + I * z := by funext z; rfl
  rw [e, logDeriv_comp (f := xi) (g := fun z : ℂ => 1 / 2 + I * z) hdx hg.differentiableAt, hg.deriv, logDeriv_xi ht,
    logDeriv_Gammaℝ (by linarith)]
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div ht
  rw [logDeriv_apply riemannZeta s]
  rw [show deriv riemannZeta s / riemannZeta s = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s by
    rw [hL]; ring]
  ring

end Pilot1ca

#print axioms Pilot1ca.Xi_zero_im
#print axioms Pilot1ca.hasSum_logDeriv_Xi
#print axioms Pilot1ca.logDeriv_Xi_eq
