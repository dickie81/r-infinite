import Mathlib
import PsiOmega
import PrimeRaces

/-!
# S0 of the round-277 plan: the smoothed Möbius sums of `ζ · L(·, χ₋₃)` and a zero-free half-plane

Let `r(n) = Σ_{d ∣ n} χ₋₃(d)`, so that `Σ r(n) n^{−s} = ζ(s) L(s, χ₋₃)` on `Re s > 1`
(`LSeries_rK`), and let `μ_K = μ ⍟ (χ₋₃ μ)`, whose L-series is the reciprocal there
(`LSeries_muK_mul`). Suppose that for every smooth `W` compactly supported in `(0, ∞)` and every
`ε > 0`, `Σ_n μ_K(n) W(n/D) = O(D^{θ+ε})` as `D → ∞` (`SmoothBound θ`). Then `ζ(s) ≠ 0` and
`L(s, χ₋₃) ≠ 0` on `Re s > θ` (`ne_zero_of_smoothBound`).

The proof. For such a `W`, the Mellin transform `G(w) = ∫_0^∞ S_W(D) D^{−w−1} dD` of the smoothed
sum is holomorphic on `Re w > θ + ε` (Mathlib's `mellin_differentiableAt_of_isBigO_rpow`), and on
`Re w > 1` it equals `L(μ_K, w) · W̃(w)`, where `W̃` is the Mellin transform of `W`
(`mellin_smoothSum`). So `G(w) · (w − 1)ζ(w) · L(w, χ₋₃) = (w − 1) W̃(w)` on all of `Re w > θ + ε`,
by the identity theorem. At a zero `ρ ≠ 1` this forces `W̃(ρ) = 0` for every `W`, and the fundamental
lemma of the calculus of variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) would
then make `x^{ρ−1}` vanish almost everywhere on `(0, ∞)`, which it does not.

No positivity is used: the hypothesis bounds the sums on both sides. The hypothesis is displayed,
not derived; it is the socket for stages S1–S6 of the round-277 plan.
-/

open Complex Filter Topology MeasureTheory Set Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius ContDiff

namespace HalfPlaneS0

open PsiOmega DirichletCharacter

/-- `r(n) = Σ_{d ∣ n} χ₋₃(d)`: the coefficients of `ζ(s) L(s, χ₋₃)`. -/
noncomputable def rK : ℕ → ℂ := 1 ⍟ ↗chi3

/-- `μ_K = μ ⍟ (χ₋₃ μ)`. -/
noncomputable def muK : ℕ → ℂ := ↗μ ⍟ (↗chi3 * ↗μ)

theorem muK_zero : muK 0 = 0 := LSeries.convolution_map_zero _ _

theorem LSeries_rK {s : ℂ} (hs : 1 < s.re) : L rK s = riemannZeta s * LFunction chi3 s := by
  rw [rK, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
    (LSeriesSummable_of_one_lt_re chi3 hs), LSeries_one_eq_riemannZeta hs,
    LFunction_eq_LSeries chi3 hs]

theorem LSeriesSummable_muK {s : ℂ} (hs : 1 < s.re) : LSeriesSummable muK s :=
  (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).convolution
    (DirichletCharacter.LSeriesSummable_mul chi3
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs))

/-- `L(μ_K, s) · ζ(s) L(s, χ₋₃) = 1` on `Re s > 1`. -/
theorem LSeries_muK_mul {s : ℂ} (hs : 1 < s.re) :
    L muK s * (riemannZeta s * LFunction chi3 s) = 1 := by
  have hμ := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  rw [muK, LSeries_convolution' hμ (DirichletCharacter.LSeriesSummable_mul chi3 hμ),
    ← LSeries_one_eq_riemannZeta hs, LFunction_eq_LSeries chi3 hs]
  have h1 := LSeries_one_mul_Lseries_moebius hs
  have h2 := DirichletCharacter.LSeries.mul_mu_eq_one chi3 hs
  calc _ = (L 1 s * L ↗μ s) * (L ↗chi3 s * L (↗chi3 * ↗μ) s) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

/-- `L(r, s) · L(μ_K, s) = 1` on `Re s > 1`: `μ_K` is the Dirichlet inverse of `r` there. -/
theorem LSeries_rK_mul_muK {s : ℂ} (hs : 1 < s.re) : L rK s * L muK s = 1 := by
  rw [LSeries_rK hs, mul_comm]; exact LSeries_muK_mul hs

/-- A weight of the hypothesis: smooth, with compact support inside `(0, ∞)`. -/
structure Weight (W : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ W
  compact : HasCompactSupport W
  pos : tsupport W ⊆ Ioi 0

/-- The smoothed Möbius sum `Σ_n μ_K(n) W(n/D)`. -/
noncomputable def smoothSum (W : ℝ → ℝ) (D : ℝ) : ℂ := ∑' n : ℕ, muK n * (W (n / D) : ℂ)

/-- The S0 hypothesis at exponent `θ`: for every weight `W` and every `ε > 0`,
`Σ_n μ_K(n) W(n/D) = O(D^{θ+ε})` as `D → ∞`. -/
def SmoothBound (θ : ℝ) : Prop :=
  ∀ W : ℝ → ℝ, Weight W → ∀ ε : ℝ, 0 < ε → smoothSum W =O[atTop] fun D => D ^ (θ + ε)

/-- The norm of a Mellin integrand under the dilation `t ↦ a t`. -/
theorem integral_norm_comp_mul (z : ℂ) {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) :
    ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (z - 1) • f (a * t)‖ =
      a ^ (-z.re) * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (z - 1) • f t‖ := by
  set h : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (z - 1) • f u‖
  have hcancel : a ^ (1 - z.re) * a ^ (z.re - 1) = 1 := by
    rw [← Real.rpow_add ha, show 1 - z.re + (z.re - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  have hpt : EqOn (fun t : ℝ => ‖(t : ℂ) ^ (z - 1) • f (a * t)‖)
      (fun t => a ^ (1 - z.re) * h (a * t)) (Ioi 0) := fun t ht => by
    have ht : (0 : ℝ) < t := ht
    simp only [h, norm_smul, norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos (mul_pos ha ht), sub_re, one_re,
      Real.mul_rpow ha.le ht.le]
    rw [← mul_assoc, ← mul_assoc, hcancel, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi h 0 ha, mul_zero, smul_eq_mul, ← mul_assoc,
    show a ^ (1 - z.re) * a⁻¹ = a ^ (-z.re) by
      rw [Real.rpow_sub ha, Real.rpow_one, Real.rpow_neg ha.le]
      field_simp]

namespace Weight

variable {W : ℝ → ℝ} (hW : Weight W)
include hW

theorem continuous : Continuous W := hW.smooth.continuous

/-- `W` vanishes beyond some `R ≥ 0`. -/
theorem exists_vanish_right : ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < x → W x = 0 := by
  obtain ⟨R, hR⟩ := hW.compact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => image_eq_zero_of_notMem_tsupport fun hxs => ?_⟩
  have h := hR hxs
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  linarith [le_abs_self x, le_max_left R 0]

theorem eventually_zero_atTop : (fun t => (W t : ℂ)) =ᶠ[atTop] 0 := by
  obtain ⟨R, -, hR⟩ := hW.exists_vanish_right
  filter_upwards [eventually_gt_atTop R] with x hx
  simp [hR x hx]

theorem eventually_zero_nhds : (fun t => (W t : ℂ)) =ᶠ[𝓝 0] 0 := by
  have h : W =ᶠ[𝓝 0] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp fun h => lt_irrefl (0 : ℝ) (hW.pos h)
  filter_upwards [h] with x hx
  simp [hx]

theorem locallyIntegrableOn : LocallyIntegrableOn (fun t => (W t : ℂ)) (Ioi 0) :=
  ((continuous_ofReal.comp hW.continuous).locallyIntegrable).locallyIntegrableOn _

theorem mellinConvergent (z : ℂ) : MellinConvergent (fun t => (W t : ℂ)) z :=
  mellinConvergent_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1) hW.locallyIntegrableOn
    (hW.eventually_zero_atTop.trans_isBigO (isBigO_zero _ _)) (by linarith)
    ((hW.eventually_zero_nhds.filter_mono nhdsWithin_le_nhds).trans_isBigO (isBigO_zero _ _))
    (by linarith)

/-- The Mellin transform of a weight is entire. -/
theorem differentiable_mellin : Differentiable ℂ (mellin fun t => (W t : ℂ)) := fun z =>
  mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1) hW.locallyIntegrableOn
    (hW.eventually_zero_atTop.trans_isBigO (isBigO_zero _ _)) (by linarith)
    ((hW.eventually_zero_nhds.filter_mono nhdsWithin_le_nhds).trans_isBigO (isBigO_zero _ _))
    (by linarith)

omit hW in
/-- On `0 < D < b` the smoothed sum is a finite sum. -/
theorem smoothSum_eq_sum {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x, R < x → W x = 0) {b D : ℝ}
    (hD : 0 < D) (hDb : D ≤ b) {N : ℕ} (hN : R * b < N) :
    smoothSum W D = ∑ n ∈ Finset.range N, muK n * (W (n / D) : ℂ) := by
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hRD : R * D ≤ R * b := mul_le_mul_of_nonneg_left hDb hR0
  have hnD : R < n / D := by
    rw [lt_div_iff₀ hD]
    exact lt_of_le_of_lt hRD (lt_of_lt_of_le hN (by exact_mod_cast hn))
  rw [hR _ hnD, ofReal_zero, mul_zero]

/-- The smoothed sum vanishes for small `D > 0`. -/
theorem smoothSum_eventually_zero : smoothSum W =ᶠ[𝓝[>] 0] 0 := by
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  have hpos : (0 : ℝ) < 1 / (R + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with D hD
  rw [Pi.zero_apply, smoothSum_eq_sum hR0 hR hD.1 le_rfl (N := 1) ?_]
  · simp [muK_zero]
  · have h1 : D * (R + 1) < 1 := by
      have := hD.2
      rwa [lt_div_iff₀ (by positivity : (0 : ℝ) < R + 1)] at this
    push_cast
    nlinarith [hD.1]

theorem continuousOn_smoothSum : ContinuousOn (smoothSum W) (Ioi 0) := by
  intro D0 hD0
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  obtain ⟨N, hN⟩ := exists_nat_gt (R * (D0 + 1))
  have hcont : ContinuousOn (fun D : ℝ => ∑ n ∈ Finset.range N, muK n * (W (n / D) : ℂ))
      (Ioi 0) := by
    refine continuousOn_finsetSum _ fun n _ => continuousOn_const.mul ?_
    exact continuous_ofReal.comp_continuousOn (hW.continuous.comp_continuousOn
      (continuousOn_const.div continuousOn_id fun x hx => ne_of_gt hx))
  have hnhds : Ioo 0 (D0 + 1) ∈ 𝓝 D0 := Ioo_mem_nhds hD0 (by linarith)
  have hat : ContinuousAt (smoothSum W) D0 :=
    ((hcont D0 hD0).continuousAt (Ioi_mem_nhds hD0)).congr
      (Filter.eventuallyEq_of_mem hnhds fun D hD =>
        (smoothSum_eq_sum hR0 hR hD.1 hD.2.le hN).symm)
  exact hat.continuousWithinAt

theorem locallyIntegrableOn_smoothSum : LocallyIntegrableOn (smoothSum W) (Ioi 0) :=
  hW.continuousOn_smoothSum.locallyIntegrableOn measurableSet_Ioi

/-- Under the bound at exponent `θ + ε`, the Mellin transform of the smoothed sum, read at `−w`, is
holomorphic on `Re w > θ + ε`. -/
theorem differentiableAt_mellin_smoothSum {θ ε : ℝ}
    (hb : smoothSum W =O[atTop] fun D => D ^ (θ + ε)) {w : ℂ} (hw : θ + ε < w.re) :
    DifferentiableAt ℂ (fun z => mellin (smoothSum W) (-z)) w := by
  have h := mellin_differentiableAt_of_isBigO_rpow (f := smoothSum W) (s := -w)
    (a := -(θ + ε)) (b := -w.re - 1) hW.locallyIntegrableOn_smoothSum
    (by simpa only [neg_neg] using hb) (by rw [neg_re]; linarith)
    (hW.smoothSum_eventually_zero.trans_isBigO (isBigO_zero _ _)) (by rw [neg_re]; linarith)
  exact h.comp w differentiableAt_id.neg

/-- On `Re z > 1`, the Mellin transform of the smoothed sum, read at `−z`, is `L(μ_K, z) · W̃(z)`. -/
theorem mellin_smoothSum {z : ℂ} (hz : 1 < z.re) :
    mellin (smoothSum W) (-z) = L muK z * mellin (fun t => (W t : ℂ)) z := by
  rw [← mellin_comp_inv]
  set F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (z - 1) • (muK n * (W (n * t) : ℂ)) with hF
  have hS : ∀ t : ℝ, (t : ℂ) ^ (z - 1) • smoothSum W t⁻¹ = ∑' n, F n t := fun t => by
    simp only [smoothSum, div_inv_eq_mul, hF, smul_eq_mul, tsum_mul_left]
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hF, muK_zero, zero_mul, smul_zero]; exact integrable_zero _ _ _
    · have hc : MellinConvergent (fun t => (W (n * t) : ℂ)) z :=
        (MellinConvergent.comp_mul_left (by exact_mod_cast hn)).mpr (hW.mellinConvergent z)
      have := hc.const_mul (muK n)
      refine this.congr (Eventually.of_forall fun t => ?_)
      simp only [hF, smul_eq_mul]; ring
  set I : ℝ := ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (z - 1) • (W t : ℂ)‖
  have hnorm : ∀ n, ∫ t in Ioi 0, ‖F n t‖ = ‖LSeries.term muK z n‖ * I := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, muK_zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have e1 : ∀ t : ℝ, ‖F n t‖ = ‖muK n‖ * ‖(t : ℂ) ^ (z - 1) • (W (n * t) : ℂ)‖ := fun t => by
        simp only [hF, smul_eq_mul, norm_mul]; ring
      simp_rw [e1]
      rw [integral_const_mul, integral_norm_comp_mul z hn' (fun t => (W t : ℂ)),
        Real.rpow_neg hn'.le]
      simp only [LSeries.norm_term_eq, hn.ne', ↓reduceIte]
      ring
  have hsumm : Summable fun n => ∫ t in Ioi 0, ‖F n t‖ :=
    ((LSeriesSummable_muK hz).norm.mul_right I).congr fun n => (hnorm n).symm
  have hHS := hasSum_integral_of_summable_integral_norm hint hsumm
  have hterm : ∀ n, ∫ t in Ioi 0, F n t = LSeries.term muK z n * mellin (fun t => (W t : ℂ)) z :=
    fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, muK_zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have e1 : ∀ t : ℝ, F n t = muK n * ((t : ℂ) ^ (z - 1) • (W (n * t) : ℂ)) := fun t => by
        simp only [hF, smul_eq_mul]; ring
      have hm := mellin_comp_mul_left (fun t => (W t : ℂ)) z hn'
      simp_rw [e1]
      rw [integral_const_mul, ← mellin, hm, LSeries.term_of_ne_zero hn.ne', smul_eq_mul,
        ofReal_natCast, cpow_neg, div_eq_mul_inv]
      ring
  calc mellin (fun t => smoothSum W t⁻¹) z = ∫ t in Ioi 0, ∑' n, F n t := by
        simp only [mellin, hS]
    _ = ∑' n, ∫ t in Ioi 0, F n t := hHS.tsum_eq.symm
    _ = L muK z * mellin (fun t => (W t : ℂ)) z := by
        simp_rw [hterm]; rw [tsum_mul_right]; rfl

end Weight

/-- **S0.** Suppose that for every smooth `W` compactly supported in `(0, ∞)` and every `ε > 0`,
`Σ_n μ_K(n) W(n/D) = O(D^{θ+ε})`. Then `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > θ`. -/
theorem ne_zero_of_smoothBound {θ : ℝ} (h : SmoothBound θ) {s : ℂ} (hs : θ < s.re) :
    riemannZeta s ≠ 0 ∧ LFunction chi3 s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; exact ⟨riemannZeta_one_ne_zero, LFunction_apply_one_ne_zero chi3_ne_one⟩
  suffices key : riemannZeta s * LFunction chi3 s ≠ 0 from
    ⟨fun h0 => key (by rw [h0, zero_mul]), fun h0 => key (by rw [h0, mul_zero])⟩
  intro h0
  -- every weight's Mellin transform vanishes at `s`
  have hvan : ∀ W : ℝ → ℝ, Weight W → mellin (fun t => (W t : ℂ)) s = 0 := by
    intro W hW
    set ε : ℝ := (s.re - θ) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hb := h W hW ε hε0
    set U : Set ℂ := {w | θ + ε < w.re} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
    have hUc : IsPreconnected U := (convex_halfSpace_re_gt (θ + ε)).isPreconnected
    set G : ℂ → ℂ := fun w => mellin (smoothSum W) (-w) * (Zr w * LFunction chi3 w) with hG
    set H : ℂ → ℂ := fun w => (w - 1) * mellin (fun t => (W t : ℂ)) w with hH
    have hGd : DifferentiableOn ℂ G U := fun w hw =>
      ((hW.differentiableAt_mellin_smoothSum hb hw).mul
        (differentiable_Zr.differentiableAt.mul
          (differentiable_LFunction chi3_ne_one).differentiableAt)).differentiableWithinAt
    have hHd : DifferentiableOn ℂ H U :=
      ((differentiable_id.sub_const 1).mul hW.differentiable_mellin).differentiableOn
    have hagree : ∀ w : ℂ, 1 < w.re → G w = H w := fun w hw => by
      have hw1 : w ≠ 1 := fun h1 => by rw [h1, one_re] at hw; exact lt_irrefl _ hw
      have hL := LSeries_muK_mul hw
      simp only [hG, hH, hW.mellin_smoothSum hw, Zr_of_ne hw1]
      linear_combination (w - 1) * mellin (fun t => (W t : ℂ)) w * hL
    set w0 : ℂ := ((max 1 (θ + ε) + 1 : ℝ) : ℂ) with hw0
    have hw0U : w0 ∈ U := by
      simp only [hU, hw0, mem_ofPred_eq, ofReal_re]; linarith [le_max_right 1 (θ + ε)]
    have hw0r : 1 < w0.re := by
      simp only [hw0, ofReal_re]; linarith [le_max_left 1 (θ + ε)]
    have hev : G =ᶠ[𝓝 w0] H := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hw0r] with w hw
      exact hagree w hw
    have heq := (hGd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
      (hHd.analyticOnNhd hUo) hUc hw0U hev
    have hsU : s ∈ U := by simp only [hU, mem_ofPred_eq]; rw [hε]; linarith
    have hGs := heq hsU
    simp only [hG, hH, Zr_of_ne hs1] at hGs
    have h00 : (s - 1) * mellin (fun t => (W t : ℂ)) s = 0 := by
      rw [← hGs]; linear_combination mellin (smoothSum W) (-s) * (s - 1) * h0
    exact (mul_eq_zero.mp h00).resolve_left (sub_ne_zero.mpr hs1)
  -- the fundamental lemma: `x^{s-1}` would vanish almost everywhere on `(0, ∞)`
  have hloc : LocallyIntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioi 0) volume := by
    refine ContinuousOn.locallyIntegrableOn (fun x hx => ?_) measurableSet_Ioi
    exact (continuousAt_ofReal_cpow_const x (s - 1) (Or.inr (ne_of_gt hx))).continuousWithinAt
  have hae := (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hloc fun g hg hgc hgs => by
      have hw := hvan g ⟨hg, hgc, hgs⟩
      rw [mellin] at hw
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun hxs => hx (hgs hxs), zero_smul]]
      rw [← hw]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [real_smul, smul_eq_mul, mul_comm]
  have hnull : volume (Ioi (0 : ℝ)) = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun x hx => ?_) hae
    simp only [mem_ofPred_eq, not_imp]
    refine ⟨hx, fun h1 => ?_⟩
    rw [cpow_eq_zero_iff] at h1
    exact (ne_of_gt (mem_Ioi.mp hx)) (ofReal_eq_zero.mp h1.1)
  simp [Real.volume_Ioi] at hnull

end HalfPlaneS0

#print axioms HalfPlaneS0.LSeries_rK
#print axioms HalfPlaneS0.LSeries_muK_mul
#print axioms HalfPlaneS0.LSeries_rK_mul_muK
#print axioms HalfPlaneS0.Weight.differentiable_mellin
#print axioms HalfPlaneS0.Weight.differentiableAt_mellin_smoothSum
#print axioms HalfPlaneS0.Weight.mellin_smoothSum
#print axioms HalfPlaneS0.ne_zero_of_smoothBound
