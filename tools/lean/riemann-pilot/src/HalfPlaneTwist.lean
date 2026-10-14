import HalfPlaneS0

/-!
# Round 475: S0 for twisted Möbius sums

Step 2 of round 471's plan for the real characters, "S0 for the twisted coefficients". Round 278's S0 goes from
bounds on the smoothed sums of `μ_K` to `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0`. This file does the same for the twist
`χ(n)μ_K(n)` by a Dirichlet character `χ`.

* `ne_zero_of_smoothSumOf`: let `c(0) = 0`, `L(c, s)` absolutely convergent on `Re s > 1`, and `F` entire with
  `L(c, s)F(s) = 1` there. If `Σ_n c(n)W(n/D) = O(D^{θ+ε})` for every weight `W` and every `ε > 0`, then
  `F(s) ≠ 0` on `Re s > θ`. This is round 278's argument: the Mellin transform of the smoothed sum, read at
  `−s`, times `F` is `W̃` on `Re s > 1`, hence on `Re s > θ + ε` by the identity theorem, and a zero of `F`
  there would be a zero of every `W̃`. The lemmas of round 278's `Weight` namespace are restated here for a
  general `c` (`smoothSumOf`, `mellin_smoothSumOf`, `differentiableAt_mellin_smoothSumOf`).
* `ne_zero_of_twistBound`: for `3 ∣ N` and `χ` mod `N` with `χ ≠ 1` and `χχ₋₃ ≠ 1` (`mulChi3`), the bound
  for `c(n) = χ(n)μ_K(n)` (`muKTw`) gives `L(s, χ) ≠ 0` and `L(s, χχ₋₃) ≠ 0` on `Re s > θ`. Here
  `χμ_K = (χμ) ⍟ (χχ₋₃μ)` (`muKTw_eq`, from Mathlib's `mul_convolution_distrib`), so
  `L(χμ_K, s)·L(s, χ)L(s, χχ₋₃) = 1` on `Re s > 1` (`LSeries_muKTw_mul`), and `F = L(·, χ)L(·, χχ₋₃)` is
  entire (Mathlib's `differentiable_LFunction`).
-/

open Complex Filter Topology MeasureTheory Set Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius ContDiff

namespace HalfPlaneS0

open PsiOmega DirichletCharacter

/-- The smoothed sum `Σ_n c(n) W(n/D)` of a sequence `c`. -/
noncomputable def smoothSumOf (c : ℕ → ℂ) (W : ℝ → ℝ) (D : ℝ) : ℂ := ∑' n : ℕ, c n * (W (n / D) : ℂ)

namespace Weight

variable {W : ℝ → ℝ} (hW : Weight W)
include hW

omit hW in
/-- On `0 < D ≤ b` the smoothed sum is a finite sum. -/
theorem smoothSumOf_eq_sum (c : ℕ → ℂ) {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x, R < x → W x = 0) {b D : ℝ}
    (hD : 0 < D) (hDb : D ≤ b) {N : ℕ} (hN : R * b < N) :
    smoothSumOf c W D = ∑ n ∈ Finset.range N, c n * (W (n / D) : ℂ) := by
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hRD : R * D ≤ R * b := mul_le_mul_of_nonneg_left hDb hR0
  have hnD : R < n / D := by
    rw [lt_div_iff₀ hD]
    exact lt_of_le_of_lt hRD (lt_of_lt_of_le hN (by exact_mod_cast hn))
  rw [hR _ hnD, ofReal_zero, mul_zero]

/-- The smoothed sum vanishes for small `D > 0` when `c(0) = 0`. -/
theorem smoothSumOf_eventually_zero {c : ℕ → ℂ} (hc0 : c 0 = 0) : smoothSumOf c W =ᶠ[𝓝[>] 0] 0 := by
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  have hpos : (0 : ℝ) < 1 / (R + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with D hD
  rw [Pi.zero_apply, smoothSumOf_eq_sum c hR0 hR hD.1 le_rfl (N := 1) ?_]
  · simp [hc0]
  · have h1 : D * (R + 1) < 1 := by
      have := hD.2
      rwa [lt_div_iff₀ (by positivity : (0 : ℝ) < R + 1)] at this
    push_cast
    nlinarith [hD.1]

theorem continuousOn_smoothSumOf (c : ℕ → ℂ) : ContinuousOn (smoothSumOf c W) (Ioi 0) := by
  intro D0 hD0
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  obtain ⟨N, hN⟩ := exists_nat_gt (R * (D0 + 1))
  have hcont : ContinuousOn (fun D : ℝ => ∑ n ∈ Finset.range N, c n * (W (n / D) : ℂ))
      (Ioi 0) := by
    refine continuousOn_finsetSum _ fun n _ => continuousOn_const.mul ?_
    exact continuous_ofReal.comp_continuousOn (hW.continuous.comp_continuousOn
      (continuousOn_const.div continuousOn_id fun x hx => ne_of_gt hx))
  have hnhds : Ioo 0 (D0 + 1) ∈ 𝓝 D0 := Ioo_mem_nhds hD0 (by linarith)
  have hat : ContinuousAt (smoothSumOf c W) D0 :=
    ((hcont D0 hD0).continuousAt (Ioi_mem_nhds hD0)).congr
      (Filter.eventuallyEq_of_mem hnhds fun D hD =>
        (smoothSumOf_eq_sum c hR0 hR hD.1 hD.2.le hN).symm)
  exact hat.continuousWithinAt

/-- Under the bound at exponent `θ + ε`, the Mellin transform of the smoothed sum, read at `−w`, is
holomorphic on `Re w > θ + ε`. -/
theorem differentiableAt_mellin_smoothSumOf {c : ℕ → ℂ} (hc0 : c 0 = 0) {θ ε : ℝ}
    (hb : smoothSumOf c W =O[atTop] fun D => D ^ (θ + ε)) {w : ℂ} (hw : θ + ε < w.re) :
    DifferentiableAt ℂ (fun z => mellin (smoothSumOf c W) (-z)) w := by
  have h := mellin_differentiableAt_of_isBigO_rpow (f := smoothSumOf c W) (s := -w)
    (a := -(θ + ε)) (b := -w.re - 1)
    ((hW.continuousOn_smoothSumOf c).locallyIntegrableOn measurableSet_Ioi)
    (by simpa only [neg_neg] using hb) (by rw [neg_re]; linarith)
    ((hW.smoothSumOf_eventually_zero hc0).trans_isBigO (isBigO_zero _ _)) (by rw [neg_re]; linarith)
  exact h.comp w differentiableAt_id.neg

/-- Where `L(c, z)` converges absolutely, the Mellin transform of the smoothed sum, read at
`−z`, is `L(c, z) · W̃(z)`. -/
theorem mellin_smoothSumOf {c : ℕ → ℂ} (hc0 : c 0 = 0) {z : ℂ} (hcS : LSeriesSummable c z) :
    mellin (smoothSumOf c W) (-z) = L c z * mellin (fun t => (W t : ℂ)) z := by
  rw [← mellin_comp_inv]
  set F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (z - 1) • (c n * (W (n * t) : ℂ)) with hF
  have hS : ∀ t : ℝ, (t : ℂ) ^ (z - 1) • smoothSumOf c W t⁻¹ = ∑' n, F n t := fun t => by
    simp only [smoothSumOf, div_inv_eq_mul, hF, smul_eq_mul, tsum_mul_left]
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hF, hc0, zero_mul, smul_zero]; exact integrable_zero _ _ _
    · have hc : MellinConvergent (fun t => (W (n * t) : ℂ)) z :=
        (MellinConvergent.comp_mul_left (by exact_mod_cast hn)).mpr (hW.mellinConvergent z)
      have := hc.const_mul (c n)
      refine this.congr (Eventually.of_forall fun t => ?_)
      simp only [hF, smul_eq_mul]; ring
  set I : ℝ := ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (z - 1) • (W t : ℂ)‖
  have hnorm : ∀ n, ∫ t in Ioi 0, ‖F n t‖ = ‖LSeries.term c z n‖ * I := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, hc0]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have e1 : ∀ t : ℝ, ‖F n t‖ = ‖c n‖ * ‖(t : ℂ) ^ (z - 1) • (W (n * t) : ℂ)‖ := fun t => by
        simp only [hF, smul_eq_mul, norm_mul]; ring
      simp_rw [e1]
      rw [integral_const_mul, integral_norm_comp_mul z hn' (fun t => (W t : ℂ)),
        Real.rpow_neg hn'.le]
      simp only [LSeries.norm_term_eq, hn.ne', ↓reduceIte]
      ring
  have hsumm : Summable fun n => ∫ t in Ioi 0, ‖F n t‖ :=
    (hcS.norm.mul_right I).congr fun n => (hnorm n).symm
  have hHS := hasSum_integral_of_summable_integral_norm hint hsumm
  have hterm : ∀ n, ∫ t in Ioi 0, F n t = LSeries.term c z n * mellin (fun t => (W t : ℂ)) z :=
    fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, hc0]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have e1 : ∀ t : ℝ, F n t = c n * ((t : ℂ) ^ (z - 1) • (W (n * t) : ℂ)) := fun t => by
        simp only [hF, smul_eq_mul]; ring
      have hm := mellin_comp_mul_left (fun t => (W t : ℂ)) z hn'
      simp_rw [e1]
      rw [integral_const_mul, ← mellin, hm, LSeries.term_of_ne_zero hn.ne', smul_eq_mul,
        ofReal_natCast, cpow_neg, div_eq_mul_inv]
      ring
  calc mellin (fun t => smoothSumOf c W t⁻¹) z = ∫ t in Ioi 0, ∑' n, F n t := by
        simp only [mellin, hS]
    _ = ∑' n, ∫ t in Ioi 0, F n t := hHS.tsum_eq.symm
    _ = L c z * mellin (fun t => (W t : ℂ)) z := by
        simp_rw [hterm]; rw [tsum_mul_right]; rfl

end Weight

/-- **S0 for a sequence with an entire inverse.** Let `c(0) = 0`, `L(c, s)` absolutely convergent on
`Re s > 1`, and `F` entire with `L(c, s)F(s) = 1` there. If `Σ_n c(n)W(n/D) = O(D^{θ+ε})` for every weight
`W` and every `ε > 0`, then `F(s) ≠ 0` on `Re s > θ`. -/
theorem ne_zero_of_smoothSumOf {c : ℕ → ℂ} (hc0 : c 0 = 0)
    (hcS : ∀ s : ℂ, 1 < s.re → LSeriesSummable c s) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hLF : ∀ s : ℂ, 1 < s.re → L c s * F s = 1) {θ : ℝ}
    (h : ∀ W : ℝ → ℝ, Weight W → ∀ ε : ℝ, 0 < ε → smoothSumOf c W =O[atTop] fun D => D ^ (θ + ε))
    {s : ℂ} (hs : θ < s.re) : F s ≠ 0 := by
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
    set G : ℂ → ℂ := fun w => mellin (smoothSumOf c W) (-w) * F w with hG
    set H : ℂ → ℂ := fun w => mellin (fun t => (W t : ℂ)) w with hH
    have hGd : DifferentiableOn ℂ G U := fun w hw =>
      ((hW.differentiableAt_mellin_smoothSumOf hc0 hb hw).mul
        hF.differentiableAt).differentiableWithinAt
    have hHd : DifferentiableOn ℂ H U := hW.differentiable_mellin.differentiableOn
    have hagree : ∀ w : ℂ, 1 < w.re → G w = H w := fun w hw => by
      simp only [hG, hH, hW.mellin_smoothSumOf hc0 (hcS w hw)]
      linear_combination mellin (fun t => (W t : ℂ)) w * hLF w hw
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
    simp only [hG, hH, h0, mul_zero] at hGs
    exact hGs.symm
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

/-! ### The twist by a Dirichlet character -/

section Twist

variable {N : ℕ} [NeZero N]

/-- `χ·χ₋₃` at a level divisible by `3`. -/
noncomputable def mulChi3 (h3 : 3 ∣ N) (χ : DirichletCharacter ℂ N) : DirichletCharacter ℂ N :=
  χ * chi3.changeLevel h3

theorem mulChi3_apply (h3 : 3 ∣ N) (χ : DirichletCharacter ℂ N) (n : ℕ) :
    mulChi3 h3 χ n = χ n * chi3 n := by
  rw [mulChi3, MulChar.mul_apply]
  by_cases hn : IsUnit (n : ZMod N)
  · congr 1
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd chi3 h3 hn.unit
    rw [IsUnit.unit_spec] at h
    rw [h, ZMod.cast_natCast h3]
  · rw [χ.map_nonunit hn, zero_mul, zero_mul]

/-- The twist `n ↦ χ(n)μ_K(n)` of round 278's `μ_K`. -/
noncomputable def muKTw (χ : DirichletCharacter ℂ N) : ℕ → ℂ := fun n ↦ χ n * muK n

omit [NeZero N] in
theorem muKTw_zero (χ : DirichletCharacter ℂ N) : muKTw χ 0 = 0 := by
  simp [muKTw, muK_zero]

/-- `χ·μ_K = (χμ) ⍟ (χχ₋₃μ)`. -/
theorem muKTw_eq (h3 : 3 ∣ N) (χ : DirichletCharacter ℂ N) :
    muKTw χ = (↗χ * ↗μ) ⍟ (↗(mulChi3 h3 χ) * ↗μ) := by
  have e : ↗(mulChi3 h3 χ) * ↗μ = ↗χ * (↗chi3 * ↗μ) := by
    ext n
    simp only [Pi.mul_apply, mulChi3_apply]
    ring
  rw [e, mul_convolution_distrib]
  rfl

omit [NeZero N] in
theorem LSeriesSummable_muKTw (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (muKTw χ) s :=
  LSeriesSummable_mul χ (LSeriesSummable_muK hs)

/-- `L(χμ_K, s) · L(s, χ) L(s, χχ₋₃) = 1` on `Re s > 1`. -/
theorem LSeries_muKTw_mul (h3 : 3 ∣ N) (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L (muKTw χ) s * (LFunction χ s * LFunction (mulChi3 h3 χ) s) = 1 := by
  have hμ := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  rw [muKTw_eq h3, LSeries_convolution' (LSeriesSummable_mul χ hμ) (LSeriesSummable_mul _ hμ),
    LFunction_eq_LSeries χ hs, LFunction_eq_LSeries _ hs]
  have h1 := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have h2 := DirichletCharacter.LSeries.mul_mu_eq_one (mulChi3 h3 χ) hs
  calc _ = (L ↗χ s * L (↗χ * ↗μ) s) * (L ↗(mulChi3 h3 χ) s * L (↗(mulChi3 h3 χ) * ↗μ) s) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

/-- **S0 for the twist by `χ`.** Let `3 ∣ N`, `χ` a Dirichlet character mod `N` with `χ ≠ 1` and
`χχ₋₃ ≠ 1`. If `Σ_n χ(n)μ_K(n)W(n/D) = O(D^{θ+ε})` for every weight `W` and every `ε > 0`, then
`L(s, χ) ≠ 0` and `L(s, χχ₋₃) ≠ 0` on `Re s > θ`. -/
theorem ne_zero_of_twistBound (h3 : 3 ∣ N) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχ3 : mulChi3 h3 χ ≠ 1) {θ : ℝ}
    (h : ∀ W : ℝ → ℝ, Weight W → ∀ ε : ℝ, 0 < ε →
      smoothSumOf (muKTw χ) W =O[atTop] fun D => D ^ (θ + ε))
    {s : ℂ} (hs : θ < s.re) : LFunction χ s ≠ 0 ∧ LFunction (mulChi3 h3 χ) s ≠ 0 := by
  have hne := ne_zero_of_smoothSumOf (muKTw_zero χ) (fun s hs ↦ LSeriesSummable_muKTw χ hs)
    ((differentiable_LFunction hχ).mul (differentiable_LFunction hχ3))
    (fun s hs ↦ LSeries_muKTw_mul h3 χ hs) h hs
  exact ⟨fun h0 ↦ hne (by simp [h0]), fun h0 ↦ hne (by simp [h0])⟩

end Twist

end HalfPlaneS0

#print axioms HalfPlaneS0.Weight.mellin_smoothSumOf
#print axioms HalfPlaneS0.Weight.differentiableAt_mellin_smoothSumOf
#print axioms HalfPlaneS0.ne_zero_of_smoothSumOf
#print axioms HalfPlaneS0.mulChi3_apply
#print axioms HalfPlaneS0.muKTw_eq
#print axioms HalfPlaneS0.LSeries_muKTw_mul
#print axioms HalfPlaneS0.ne_zero_of_twistBound
