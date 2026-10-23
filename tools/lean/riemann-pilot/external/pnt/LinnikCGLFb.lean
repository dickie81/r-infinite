/-
# Round 663: their `f_b = ψR̃(·, −b)²` for §11, with a `ψ` that is `1` on the centres (the CGL plan's stage M3, the
`S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their §11: "To bound S₃,₄, we define f_b(v) = ψ(v)|R̃_{M₂}(v,−b)|² for (b,q) = 1, where ψ(v) is a smooth bump
function supported on v ≍ 1 and such that ψ(1) > 0." (text layer lines 5655–5657; spaces restored, the tilde,
subscripts and exponent transcribed). Round 662 records why the stack takes a different `ψ`: round 662's reduction
(`Qb_le_gJ`) compares `S₃,₄` with `J(f⃗)` term by term, which needs `f_{−b} ≥ R̃(·, b)²` at the centres, all in
`[−3, 3]` on the stack's block. Here `ψ` is Mathlib's smooth bump with radii `3` and `4`: it is `1` on `[−3, 3]`, `0`
off `(−4, 4)`, and `ψ(1) = 1`.

This file proves the properties of `f_b` that round 662's `CGLP81` and `S34_le_Jint` ask for, apart from the decay of
`f̂_b`, which is the next step.
* Smoothness. `R̃_{M₂}(·, a)²` is the convolution of `1_{[1/2,2]}|R(·, a)|²`, bounded and measurable, with the smooth
  compactly supported kernel `x ↦ Lψ̃₀(Lx/(2X))`, `L = NM₂/q` (round 658's `Rt_sq`), so it is smooth (Mathlib's
  `HasCompactSupport.contDiff_convolution_right`).
* The lower bound. For `T ≥ 1` and points `|t_i| ≤ T`, `|R(u′, 1)| ≥ |R|/2` when `|u′ − 1| ≤ 1/(2T)`: there
  `|t_i log u′| ≤ 1`, so each `Re u′^{it_i} = cos(t_i log u′) ≥ 1/2`. Their `ψ̃₀` is `1` on `[−1, 1]`, so with
  `δ = min(2X/L, 1/(2T))`, `f_{−1}(1) = R̃(1, 1)² ≥ 2δ·L|R|²/4 = min(2X, L/(2T))|R|²/2`. Their version of this step:
  "f_{q−1}(1) = ψ(1) ∫ (NM₂/q) ψ̃((NM₂/q)(1−u′)) |R(u′,1)|² du′ ⪆ (NM₂/(qT)) |W|²" (lines 5804–5812; spaces restored,
  the integral, tildes, large parentheses, fractions, subscripts and exponents transcribed).
* A largest value. A continuous nonnegative `f_b`, `0` beyond `A`, attains `sup_{b,u}f_b(u)` (`exists_max`).

Plain statements, with `q ≥ 1`, `L = NM₂/q` and `X` for their `(qT)^ϵ`.
* `psiW`: `0 ≤ ψ ≤ 1`, `ψ = 1` on `[−3, 3]`, `ψ = 0` for `|x| ≥ 4`, `ψ` smooth.
* `contDiff_Rt_sq`: for `L, X > 0`, `u ↦ R̃_{M₂}(u, a)²` is smooth.
* `fb_nonneg`, `fb_eq_zero`, `Rt_sq_le_fb`, `contDiff_fb`: `f_b ≥ 0`; `f_b(u) = 0` for `|u| > 4`;
  `R̃(c, b)² ≤ f_{−b}(c)` for `|c| ≤ 3`; and, for `L, X > 0`, `f_b` is smooth.
* `norm_Rf_one_ge`, `fb_one_ge`: for `T ≥ 1` and points `|t_i| ≤ T`, `|R(u′, 1)| ≥ |R|/2` for `|u′ − 1| ≤ 1/(2T)`,
  and, for `L, X > 0`, `f_{−1}(1) ≥ min(2X, L/(2T))|R|²/2`.
* `exists_max`: a family of continuous nonnegative functions on `ℝ`, indexed by the units and `0` beyond `A`, has a
  largest value `f_{b₀}(u₀)`.
* `S34_le_fb`: for `L = 2^kN/q > 0` and `X > 0`, round 662's `S₃,₄ ≤ 4(k + 1)Σ_{j≤k}Jint(f, …)` holds for this `f`.

* `psiWide`, `psiW`, `psiW_nonneg`, `psiW_le_one`, `psiW_eq_one`, `psiW_eq_zero`, `contDiff_psiW`: their `ψ`.
* `kerL`, `hasCompactSupport_kerL`, `contDiff_kerL`, `Rt_sq_eq_conv`, `contDiff_Rt_sq`: `R̃²` as a convolution.
* `fb`, `fb_nonneg`, `fb_eq_zero`, `Rt_sq_le_fb`, `contDiff_fb`: their `f_b`.
* `norm_Rf_one_ge`, `fb_one_ge`: the lower bound.
* `exists_max`, `S34_le_fb`: a largest value, and round 662's reduction for this `f`.

The file imports `LinnikCGLJ.lean`.
-/

import LinnikCGLJ

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLFb

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt LinnikCGLP72
  LinnikCGLMom LinnikCGLMom4 LinnikCGLCS LinnikCGLJ

/-! ### Their `ψ`, `1` on the centres -/

/-- Their `ψ`: a smooth bump, `1` on `[−3, 3]` and `0` off `(−4, 4)`. -/
def psiWide : ContDiffBump (0 : ℝ) := ⟨3, 4, by norm_num, by norm_num⟩

/-- Their `ψ` as a function. -/
def psiW (x : ℝ) : ℝ := psiWide x

lemma psiW_nonneg (x : ℝ) : 0 ≤ psiW x := psiWide.nonneg

lemma psiW_le_one (x : ℝ) : psiW x ≤ 1 := psiWide.le_one

lemma psiW_eq_one {x : ℝ} (hx : |x| ≤ 3) : psiW x = 1 :=
  psiWide.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

lemma psiW_eq_zero {x : ℝ} (hx : 4 ≤ |x|) : psiW x = 0 :=
  psiWide.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx)

lemma contDiff_psiW : ContDiff ℝ ∞ psiW := psiWide.contDiff

/-! ### `R̃²` as a convolution -/

/-- The kernel of `R̃²`: `x ↦ Lψ̃₀(Lx/(2X))`. -/
def kerL (L X : ℝ) (x : ℝ) : ℝ := L * psi0 (L * x / (2 * X))

lemma hasCompactSupport_kerL {L X : ℝ} (hL : 0 < L) (hX : 0 < X) : HasCompactSupport (kerL L X) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(4 * X / L)) (b := 4 * X / L)) fun x hx => ?_
  have hx' : 4 * X / L < |x| := by
    by_contra h
    push Not at h
    exact hx (abs_le.mp h)
  unfold kerL psi0
  rw [psiBump.zero_of_le_dist, mul_zero]
  rw [Real.dist_eq, sub_zero, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * X),
    le_div_iff₀ (by positivity)]
  have : 4 * X < L * |x| := by rw [div_lt_iff₀ hL] at hx'; linarith [mul_comm |x| L]
  have hr : psiBump.rOut = 2 := rfl
  rw [hr]
  linarith

lemma contDiff_kerL (L X : ℝ) : ContDiff ℝ ∞ (kerL L X) := by
  unfold kerL psi0
  exact contDiff_const.mul (psiBump.contDiff.comp ((contDiff_const.mul contDiff_id).div_const _))

/-- `R̃_{M₂}(u, a)² = ((1_{[1/2,2]}|R(·, a)|²) ⋆ kerL)(u)` for `L ≥ 0`. -/
lemma Rt_sq_eq_conv {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hL : 0 ≤ N * M₂ / q) (u : ℝ) (a : ZMod q) :
    Rt N R χ t X M₂ u a ^ 2 = convolution ((Icc (1 / 2 : ℝ) 2).indicator fun u' => ‖Rf R χ t u' a‖ ^ 2)
      (kerL (N * M₂ / q) X) (ContinuousLinearMap.lsmul ℝ ℝ) volume u := by
  rw [Rt_sq R χ t hL, convolution_def, ← integral_indicator measurableSet_Icc]
  congr 1
  funext u'
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Set.indicator, kerL]
  split_ifs <;> ring

/-- `u ↦ R̃_{M₂}(u, a)²` is smooth for `L, X > 0`. -/
lemma contDiff_Rt_sq {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hL : 0 < N * M₂ / q) (hX : 0 < X) (a : ZMod q) :
    ContDiff ℝ ∞ fun u => Rt N R χ t X M₂ u a ^ 2 := by
  have e : (fun u => Rt N R χ t X M₂ u a ^ 2) = convolution ((Icc (1 / 2 : ℝ) 2).indicator
      fun u' => ‖Rf R χ t u' a‖ ^ 2) (kerL (N * M₂ / q) X) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    funext fun u => Rt_sq_eq_conv R χ t hL.le u a
  rw [e]
  have hint : IntegrableOn (fun u' => ‖Rf R χ t u' a‖ ^ 2) (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le ((measurable_Rf R χ t a).norm.pow_const 2) (C := (R.card : ℝ) ^ 2) fun u hu => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hu.1]) a) 2
  have hloc : LocallyIntegrable ((Icc (1 / 2 : ℝ) 2).indicator fun u' => ‖Rf R χ t u' a‖ ^ 2) volume :=
    (hint.integrable_indicator measurableSet_Icc).locallyIntegrable
  exact HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤)
    (hasCompactSupport_kerL hL hX) hloc (contDiff_kerL _ _)

/-! ### Their `f_b` -/

/-- **Their `f_b`**, with the stack's `ψ`: `f_b(u) = ψ(u)R̃_{M₂}(u, −b)²`. -/
def fb {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ : ℝ) (b : (ZMod q)ˣ) (u : ℝ) : ℝ :=
  psiW u * Rt N R χ t X M₂ u ((-b : (ZMod q)ˣ) : ZMod q) ^ 2

section fb

variable {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
  {X M₂ : ℝ}

lemma fb_nonneg (b : (ZMod q)ˣ) (u : ℝ) : 0 ≤ fb N R χ t X M₂ b u :=
  mul_nonneg (psiW_nonneg u) (sq_nonneg _)

lemma fb_eq_zero (b : (ZMod q)ˣ) {u : ℝ} (hu : 4 < |u|) : fb N R χ t X M₂ b u = 0 := by
  unfold fb
  rw [psiW_eq_zero hu.le, zero_mul]

lemma Rt_sq_le_fb (b : (ZMod q)ˣ) {c : ℝ} (hc : |c| ≤ 3) :
    Rt N R χ t X M₂ c (b : ZMod q) ^ 2 ≤ fb N R χ t X M₂ (-b) c := by
  unfold fb
  rw [psiW_eq_one hc, one_mul, neg_neg]

lemma contDiff_fb (hL : 0 < N * M₂ / q) (hX : 0 < X) (b : (ZMod q)ˣ) : ContDiff ℝ ∞ (fb N R χ t X M₂ b) :=
  contDiff_psiW.mul (contDiff_Rt_sq R χ t hL hX _)

end fb

/-! ### The lower bound of `f` -/

/-- `|R(u′, 1)| ≥ |R|/2` for `|u′ − 1| ≤ 1/(2T)`, `T ≥ 1` and points `|t_i| ≤ T`: there `|t_i log u′| ≤ 1`, and
`Re u′^{it_i} = cos(t_i log u′) ≥ 1/2`. -/
lemma norm_Rf_one_ge {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {T : ℝ} (hT : 1 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T) {u : ℝ} (hu : |u - 1| ≤ 1 / (2 * T)) :
    (R.card : ℝ) / 2 ≤ ‖Rf R χ t u 1‖ := by
  have hT0 : 0 < T := by linarith
  have hu' := abs_le.mp hu
  have hhalf : 1 / (2 * T) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hu0 : 1 / 2 ≤ u := by linarith [hu'.1]
  have hupos : 0 < u := by linarith
  -- `|log u| ≤ 1/T`
  have hlog : |Real.log u| ≤ 1 / T := by
    rw [abs_le]
    constructor
    · have h1 := Real.one_sub_inv_le_log_of_pos hupos
      have h2 : -(1 / T) ≤ 1 - u⁻¹ := by
        rw [show 1 - u⁻¹ = (u - 1) / u by field_simp, le_div_iff₀ hupos]
        have : -(1 / T) * u ≤ -(1 / T) * (1 / 2) :=
          mul_le_mul_of_nonpos_left hu0 (by have := one_div_pos.2 hT0; linarith)
        have h3 : -(1 / T) * (1 / 2) = -(1 / (2 * T)) := by field_simp
        linarith [hu'.1]
      linarith
    · have h1 := Real.log_le_sub_one_of_pos hupos
      have h2 : 1 / (2 * T) ≤ 1 / T := by
        rw [div_le_div_iff₀ (by positivity) hT0]; linarith
      linarith [hu'.2]
  -- each term has real part at least `1/2`
  have hre : ∀ i ∈ R, (1 : ℝ) / 2 ≤ ((u : ℂ) ^ ((t i : ℂ) * I) * χ i 1).re := by
    intro i hi
    have hχ : χ i 1 = 1 := map_one _
    have hc : (u : ℂ) ^ ((t i : ℂ) * I) = Complex.exp (((t i * Real.log u : ℝ) : ℂ) * I) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hupos.ne'), ← Complex.ofReal_log hupos.le]
      congr 1
      push_cast
      ring
    rw [hχ, mul_one, hc, Complex.exp_ofReal_mul_I_re]
    have hθ : |t i * Real.log u| ≤ 1 := by
      rw [abs_mul]
      calc |t i| * |Real.log u| ≤ T * (1 / T) :=
            mul_le_mul (ht i hi) hlog (abs_nonneg _) (by linarith)
        _ = 1 := by field_simp
    have hcos := Real.one_sub_sq_div_two_le_cos (x := t i * Real.log u)
    have hsq : (t i * Real.log u) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (t i * Real.log u)]
    linarith
  calc (R.card : ℝ) / 2 = ∑ _i ∈ R, (1 : ℝ) / 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ R, ((u : ℂ) ^ ((t i : ℂ) * I) * χ i 1).re := Finset.sum_le_sum hre
    _ = (Rf R χ t u 1).re := by unfold Rf; rw [Complex.re_sum]
    _ ≤ ‖Rf R χ t u 1‖ := Complex.re_le_norm _

/-- **The lower bound of `f`**: for `L, X > 0`, `T ≥ 1` and points `|t_i| ≤ T`,
`f_{−1}(1) = R̃(1, 1)² ≥ min(2X, L/(2T))|R|²/2`. -/
lemma fb_one_ge {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X M₂ T : ℝ} (hL : 0 < N * M₂ / q) (hX : 0 < X) (hT : 1 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T) :
    min (2 * X) (N * M₂ / q / (2 * T)) * (R.card : ℝ) ^ 2 / 2 ≤ fb N R χ t X M₂ (-1) 1 := by
  set L := N * M₂ / q with hLdef
  have hT0 : 0 < T := by linarith
  set δ := min (2 * X / L) (1 / (2 * T)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδT : δ ≤ 1 / (2 * T) := min_le_right _ _
  have hδX : δ ≤ 2 * X / L := min_le_left _ _
  have hδh : δ ≤ 1 / 2 := hδT.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hfb : fb N R χ t X M₂ (-1) 1 = Rt N R χ t X M₂ 1 (1 : ZMod q) ^ 2 := by
    unfold fb
    rw [psiW_eq_one (by norm_num), one_mul, neg_neg, Units.val_one]
  rw [hfb, Rt_sq R χ t hL.le]
  set F : ℝ → ℝ := fun u' => L * psi0 (L * (1 - u') / (2 * X)) * ‖Rf R χ t u' (1 : ZMod q)‖ ^ 2 with hF
  have hF0 : ∀ u', 0 ≤ F u' := fun u' => by have := psi0_nonneg (L * (1 - u') / (2 * X)); positivity
  have hFm : Measurable F := by
    refine (measurable_const.mul (continuous_psi0.measurable.comp (by fun_prop))).mul ?_
    exact (measurable_Rf R χ t _).norm.pow_const 2
  have hFint : IntegrableOn F (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le hFm (C := L * 1 * (R.card : ℝ) ^ 2) fun u hu => ?_
    rw [abs_of_nonneg (hF0 u)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (psi0_le_one _) hL.le)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hu.1]) _) 2) (sq_nonneg _) (by positivity)
  have hsub : Icc (1 - δ) (1 + δ) ⊆ Icc (1 / 2 : ℝ) 2 := Icc_subset_Icc (by linarith) (by linarith)
  have hwin : ∀ u' ∈ Icc (1 - δ) (1 + δ), L * ((R.card : ℝ) ^ 2 / 4) ≤ F u' := by
    intro u' hu'
    have hd : |u' - 1| ≤ δ := abs_le.mpr ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    have hp : psi0 (L * (1 - u') / (2 * X)) = 1 := by
      refine psi0_eq_one ?_
      rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * X), div_le_one (by positivity),
        abs_sub_comm]
      have := hd.trans hδX
      rwa [le_div_iff₀ hL, mul_comm] at this
    have hR := norm_Rf_one_ge R χ t hT ht (hd.trans hδT)
    have hR2 : (R.card : ℝ) ^ 2 / 4 ≤ ‖Rf R χ t u' (1 : ZMod q)‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ (R.card : ℝ) / 2 := by positivity
      have := pow_le_pow_left₀ h0 hR 2
      calc (R.card : ℝ) ^ 2 / 4 = ((R.card : ℝ) / 2) ^ 2 := by ring
        _ ≤ ‖Rf R χ t u' (1 : ZMod q)‖ ^ 2 := this
    simp only [hF, hp, mul_one]
    exact mul_le_mul_of_nonneg_left hR2 hL.le
  calc min (2 * X) (L / (2 * T)) * (R.card : ℝ) ^ 2 / 2
      = (2 * δ) * (L * ((R.card : ℝ) ^ 2 / 4)) := by
        have e : min (2 * X) (L / (2 * T)) = δ * L := by
          rw [hδ, min_mul_of_nonneg _ _ hL.le]
          congr 1
          · field_simp
          · field_simp
        rw [e]; ring
    _ = ∫ _ in Icc (1 - δ) (1 + δ), L * ((R.card : ℝ) ^ 2 / 4) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring
    _ ≤ ∫ u' in Icc (1 - δ) (1 + δ), F u' :=
        setIntegral_mono_on continuous_const.integrableOn_Icc (hFint.mono_set hsub) measurableSet_Icc hwin
    _ ≤ ∫ u' in Icc (1 / 2 : ℝ) 2, F u' :=
        setIntegral_mono_set hFint (Eventually.of_forall fun u' => hF0 u') hsub.eventuallyLE

/-! ### A largest value -/

/-- A family of continuous nonnegative functions, indexed by the units of `ℤ/qℤ` and `0` beyond `A`, has a largest
value: some `f_{b₀}(u₀) ≥ f_b(u)` for every `b` and `u`. -/
lemma exists_max {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfc : ∀ b, Continuous (f b))
    (hf0 : ∀ b u, 0 ≤ f b u) {A : ℝ} (hfA : ∀ b u, A < |u| → f b u = 0) :
    ∃ b₀ u₀, ∀ b u, f b u ≤ f b₀ u₀ := by
  have hA : ∀ b, ∃ u₀, ∀ u, f b u ≤ f b u₀ := by
    intro b
    by_cases hA0 : 0 ≤ A
    · obtain ⟨u₀, -, hmax⟩ := (isCompact_Icc (a := -A) (b := A)).exists_isMaxOn
        (nonempty_Icc.2 (by linarith)) (hfc b).continuousOn
      refine ⟨u₀, fun u => ?_⟩
      by_cases hu : u ∈ Icc (-A) A
      · exact hmax hu
      · have : A < |u| := by
          by_contra h
          push Not at h
          exact hu (abs_le.mp h)
        rw [hfA b u this]
        exact hf0 b u₀
    · refine ⟨0, fun u => ?_⟩
      have h1 : A < |u| := lt_of_lt_of_le (by linarith) (abs_nonneg u)
      have h2 : A < |(0 : ℝ)| := by rw [abs_zero]; linarith
      rw [hfA b u h1, hfA b 0 h2]
  choose u₀ hu₀ using hA
  obtain ⟨b₀, -, hb₀⟩ := Finset.exists_max_image Finset.univ (fun b => f b (u₀ b)) Finset.univ_nonempty
  exact ⟨b₀, u₀ b₀, fun b u => (hu₀ b u).trans (hb₀ b (Finset.mem_univ b))⟩

/-! ### Round 662's reduction for this `f` -/

/-- **`S₃,₄` against their `J` for this `f`**: for `L = 2^kN/q > 0` and `X > 0`,
`S₃,₄ ≤ 4(k + 1)Σ_{j≤k}Jint(f, 2^j − 1/2, 2^k − 1/2, 2^k − 1/2, 2)` on the block `k`. -/
theorem S34_le_fb {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X : ℝ} {M k : ℕ} (hL : 0 < N * 2 ^ k / q) (hX : 0 < X) :
    S34 R χ t (X := X) (M₂ := 2 ^ k) (blk M k) (N := N) ≤ 4 * (k + 1) * ∑ j ∈ Finset.range (k + 1),
      Jint (fb N R χ t X (2 ^ k)) (2 ^ j - 1 / 2) (2 ^ k - 1 / 2) (2 ^ k - 1 / 2) 2 :=
  S34_le_Jint R χ t hL.le (fun b u => fb_nonneg R χ t b u) (fun b => (contDiff_fb R χ t hL hX b).continuous)
    (A := 4) (fun b _u hu => fb_eq_zero R χ t b hu) (fun b _c hc => Rt_sq_le_fb R χ t b hc)

end LinnikCGLFb

#print axioms LinnikCGLFb.contDiff_fb
#print axioms LinnikCGLFb.fb_one_ge
#print axioms LinnikCGLFb.exists_max
#print axioms LinnikCGLFb.S34_le_fb
