/-
# Round 656: their `R̃` and the inner integral of Proposition 7.2 (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

This file supplies the Cauchy–Schwarz step of Chen–Gupta–Li's proof of Proposition 7.2.

Their bump and their `R̃`. "Let ψ̃₀(x) be a non-negative smooth bump supported on [−2,2] such that ψ̃₀(x) = 1 for |x| ≤
1, ‖ψ̃₀^{(j)}‖_∞ ≪_j 1 and ψ̃(x) = ψ̃₀(x/(2(qT)^ϵ))" (their (7.4), text layer lines 2236–2243; spaces restored, the
tildes, subscripts, superscripts, the norm, the large parentheses and the fraction transcribed), and "R̃_{M₂}(u,a) :=
(∫_{u′∈[1/2,2]} (NM₂/q) ψ̃((NM₂/q)(u−u′)) |R(u′,a)|² du′)^{1/2}" (their (7.5), lines 2246–2257; spaces restored, the
tildes, the integral and its range, the large parentheses, the fractions, the exponents and the subscripts transcribed).
`psi0` is Mathlib's smooth bump with radii 1 and 2 (`ContDiffBump`); this file uses four of its properties: it is
continuous, nonnegative, at most 1, and 1 on `[−1, 1]`. `Rt` is their `R̃_{M₂}` with `X` for their `(qT)^ϵ`.

The step. "Using Cauchy-Schwarz and noting that |R(1/v₂,b⁻¹)| = |R(v₂,b)|, the inner v₂ integral is bounded by"
(lines 2382–2383; spaces restored, the subscripts and the exponent transcribed). The display that follows (lines
2384–2422) ends with `≤ (q/(NM₂)) R̃_{M₂}((m₁v₁+m₃)/(−m₂v₁), b₁⁻¹b₂) R̃_{M₂}((m₁v₁+m₃)/(−m₂), b₂)` (transcribed).
The identity it notes follows, by taking norms, from "From the definition of R(v,a), it follows that (see (7.2))
R(1/v,a⁻¹) = R(v,a)" (lines 2330–2335; spaces restored, the large parentheses, the fraction and the exponent
transcribed). In the PDF the right side carries a conjugation bar, a drawn rule that the text layer drops: on page 25
pdfminer finds a rule at y = 346.1, above the row at y = 333, spanning x = 323.4–358.9, exactly the extent of the
characters `R(v,a)`. `Rf_inv` is that identity, with the bar, for `v > 0` and a unit.

The window. Round 655's `Vr` keeps `|m₁v₁ + m₂v₂ + m₃| ≤ Xq/N` and `v₂/v₁ ∈ [1/2, 2]`. For `|m₂| ≥ M₂ > 0` the first
condition puts `v₂` within `δ = Xq/(NM₂)` of `c = −(m₁v₁ + m₃)/m₂`, so `(NM₂/q)δ = X`. With `u′ = v₂/v₁` the window
becomes `|u′ − c/v₁| ≤ δ/v₁ ≤ 2δ`, on which `ψ̃ = 1`; the stack uses the `2` in their `2(qT)^ϵ` here.

The constant. The substitution `u′ = v₂/v₁` gives `dv₂ = v₁du′`, so the first factor carries `√v₁ ≤ √2`, which the
stack rounds up to `2`. Their display has no constant there. Their next line is "We therefore obtain
|I′_{m₁,m₂,m₃}| ≪_ϵ (N²/(q²M₂)) Ĩ_{m₁,−m₂,m₃} + O_ϵ((qT)^{−200})" (lines 2423–2428; spaces restored, the tilde,
the subscripts, the exponents and the fraction transcribed), stated with `≪_ϵ`, which absorbs it.

Plain statements, with `L = NM₂/q`, `X > 0` and `q ≥ 1`.
* `Rf_inv`: `R(1/v, b⁻¹) = conj(R(v, b))` for `v > 0` and a unit `b`; `norm_Rf_inv` takes norms.
* `local_le_Rt_sq`: for `L > 0` and `Lδ ≤ 2X`, `L∫_{[1/2,2], |u−c|≤δ}|R(u, a)|² ≤ R̃(c, a)²`.
* `ratio_le_Rt_sq`: for `v₁ > 0` and `L(δ/v₁) ≤ 2X`,
  `L∫_{[1/2,2], |v₂−c|≤δ, v₂/v₁∈[1/2,2]}|R(v₂/v₁, a)|² ≤ v₁R̃(c/v₁, a)²`.
* `cs_Icc`: Cauchy–Schwarz on `[1/2, 2]` for nonnegative bounded measurable functions.
* `inner_le`: for `v₁ ∈ [1/2, 2]`, `L > 0` and `Lδ ≤ X`,
  `L∫_{[1/2,2], |v₂−c|≤δ, v₂/v₁∈[1/2,2]}|R(v₂/v₁, a)||R(1/v₂, b⁻¹)| ≤ 2R̃(c/v₁, a)R̃(c, b)`.
* `Vr_inner_le`: for `N > 0`, `|m₂| ≥ M₂ > 0` and `v₁ ∈ [1/2, 2]`, with `c = −(m₁v₁ + m₃)/m₂`,
  `L∫_{[1/2,2]}Vr(v₁, v₂) dv₂ ≤ 2Σ_{b₁,b₂}(b₁m₁ + b₂m₂ + m₃, q)|R(v₁, b₁)|R̃(c/v₁, b₂b₁⁻¹)R̃(c, b₂)`, where `(n, q)`
  is the gcd of `q` and the least nonnegative representative of `n`.

* `psiBump`, `psi0`, `Rt`, `Rt_nonneg`: their `ψ̃₀` and `R̃`.
* `Rf_inv`, `norm_Rf_inv`: the conjugation identity.
* `integrableOn_Icc_of_le`, `local_le_Rt_sq`, `ratio_le_Rt_sq`: the local second moments.
* `cs_Icc`, `inner_le`, `Vr_inner_le`: the Cauchy–Schwarz step.

The next round integrates `Vr_inner_le` over `v₁` against round 655's `prop71r`.

The file imports `LinnikCGLSym.lean`.
-/

import LinnikCGLSym

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLRt

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact
  LinnikCGLRam LinnikCGLP71 LinnikCGLSym

/-! ### Their `ψ̃₀` and `R̃` -/

/-- Their `ψ̃₀`: a smooth bump, `1` on `[−1, 1]` and `0` off `(−2, 2)`. -/
def psiBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- Their `ψ̃₀` as a function. -/
def psi0 (x : ℝ) : ℝ := psiBump x

lemma psi0_nonneg (x : ℝ) : 0 ≤ psi0 x := psiBump.nonneg

lemma psi0_le_one (x : ℝ) : psi0 x ≤ 1 := psiBump.le_one

lemma psi0_eq_one {x : ℝ} (hx : |x| ≤ 1) : psi0 x = 1 :=
  psiBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

lemma continuous_psi0 : Continuous psi0 := psiBump.continuous

/-- **Their (7.5)**, with `X` for their `(qT)^ϵ` and `ψ̃(x) = ψ̃₀(x/(2X))`:
`R̃_{M₂}(u, a) = (∫_{[1/2,2]}(NM₂/q)ψ̃((NM₂/q)(u − u′))|R(u′, a)|² du′)^{1/2}`. -/
def Rt {ι : Type*} {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (X M₂ u : ℝ)
    (a : ZMod q) : ℝ :=
  Real.sqrt (∫ u' in Icc (1 / 2 : ℝ) 2, N * M₂ / q * psi0 (N * M₂ / q * (u - u') / (2 * X)) * ‖Rf R χ t u' a‖ ^ 2)

lemma Rt_nonneg {ι : Type*} {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ u : ℝ) (a : ZMod q) : 0 ≤ Rt N R χ t X M₂ u a := Real.sqrt_nonneg _

/-! ### `|R(1/v, b⁻¹)| = |R(v, b)|` -/

/-- `R(1/v, b⁻¹) = conj(R(v, b))` for `v > 0` and a unit `b`. -/
lemma Rf_inv {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {v : ℝ}
    (hv : 0 < v) (b : (ZMod q)ˣ) :
    Rf R χ t (1 / v) ((b⁻¹ : (ZMod q)ˣ) : ZMod q) = conj (Rf R χ t v (b : ZMod q)) := by
  unfold Rf
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← star_unit (χ i) b, cpow_eq_exp (one_div_pos.2 hv), cpow_eq_exp hv, ← Complex.exp_conj]
  congr 2
  rw [one_div, Real.log_inv]
  simp [Complex.conj_ofReal]

lemma norm_Rf_inv {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {v : ℝ} (hv : 0 < v) (b : (ZMod q)ˣ) :
    ‖Rf R χ t (1 / v) ((b⁻¹ : (ZMod q)ˣ) : ZMod q)‖ = ‖Rf R χ t v (b : ZMod q)‖ := by
  rw [Rf_inv R χ t hv b, RCLike.norm_conj]

/-! ### The local second moment against `R̃` -/

/-- A bounded measurable function on `[1/2, 2]` is integrable there. -/
lemma integrableOn_Icc_of_le {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |f x| ≤ C) : IntegrableOn f (Icc (1 / 2 : ℝ) 2) :=
  Integrable.mono' (integrableOn_const (C := C) (by simp)) hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]; exact hC x hx))

/-- **`R̃` controls the local second moment**: for `L = NM₂/q > 0` and `Lδ ≤ 2X`,
`L∫_{[1/2,2], |u−c|≤δ}|R(u, a)|² ≤ R̃_{M₂}(c, a)²`. -/
lemma local_le_Rt_sq {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hX : 0 < X) (hL : 0 < N * M₂ / q) {c δ : ℝ} (hδ : N * M₂ / q * δ ≤ 2 * X) (a : ZMod q) :
    N * M₂ / q * ∫ u in Icc (1 / 2 : ℝ) 2, (if |u - c| ≤ δ then ‖Rf R χ t u a‖ ^ 2 else 0) ≤
      Rt N R χ t X M₂ c a ^ 2 := by
  set L := N * M₂ / q with hLdef
  have hR2 : ∀ u ∈ Icc (1 / 2 : ℝ) 2, ‖Rf R χ t u a‖ ^ 2 ≤ (R.card : ℝ) ^ 2 := fun u hu =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hu.1]) a) 2
  have hmR : Measurable fun u : ℝ => ‖Rf R χ t u a‖ ^ 2 := ((measurable_Rf R χ t a).norm).pow_const 2
  have hint : IntegrableOn (fun u => L * psi0 (L * (c - u) / (2 * X)) * ‖Rf R χ t u a‖ ^ 2)
      (Icc (1 / 2 : ℝ) 2) := by
    refine integrableOn_Icc_of_le ((measurable_const.mul (continuous_psi0.measurable.comp (by fun_prop))).mul hmR)
      (C := L * (R.card : ℝ) ^ 2) fun u hu => ?_
    rw [abs_of_nonneg (by have := psi0_nonneg (L * (c - u) / (2 * X)); positivity)]
    calc L * psi0 (L * (c - u) / (2 * X)) * ‖Rf R χ t u a‖ ^ 2 ≤ L * 1 * (R.card : ℝ) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (psi0_le_one _) hL.le) (hR2 u hu) (by positivity)
            (by positivity)
      _ = L * (R.card : ℝ) ^ 2 := by ring
  have hsq : Rt N R χ t X M₂ c a ^ 2 =
      ∫ u in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (c - u) / (2 * X)) * ‖Rf R χ t u a‖ ^ 2 :=
    Real.sq_sqrt (setIntegral_nonneg measurableSet_Icc fun u _ => by
      have := psi0_nonneg (L * (c - u) / (2 * X)); positivity)
  rw [hsq, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => ?_) hint
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_))
  · show 0 ≤ L * (if |u - c| ≤ δ then ‖Rf R χ t u a‖ ^ 2 else 0)
    split_ifs <;> positivity
  · show L * (if |u - c| ≤ δ then ‖Rf R χ t u a‖ ^ 2 else 0) ≤ L * psi0 (L * (c - u) / (2 * X)) * ‖Rf R χ t u a‖ ^ 2
    split_ifs with h
    · have h1 : psi0 (L * (c - u) / (2 * X)) = 1 := by
        refine psi0_eq_one ?_
        rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * X), div_le_one (by positivity),
          abs_sub_comm]
        calc L * |u - c| ≤ L * δ := mul_le_mul_of_nonneg_left h hL.le
          _ ≤ 2 * X := hδ
      rw [h1, mul_one]
    · have := psi0_nonneg (L * (c - u) / (2 * X)); simp only [mul_zero]; positivity

/-- **The ratio factor**: for `v₁ > 0` and `L(δ/v₁) ≤ 2X`,
`L∫_{[1/2,2], |v₂−c|≤δ, v₂/v₁∈[1/2,2]}|R(v₂/v₁, a)|² ≤ v₁R̃_{M₂}(c/v₁, a)²`. -/
lemma ratio_le_Rt_sq {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hX : 0 < X) (hL : 0 < N * M₂ / q) {v₁ c δ : ℝ} (hv₁ : 0 < v₁)
    (hδ : N * M₂ / q * (δ / v₁) ≤ 2 * X) (a : ZMod q) :
    N * M₂ / q * ∫ v₂ in Icc (1 / 2 : ℝ) 2,
      (if |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then ‖Rf R χ t (v₂ / v₁) a‖ ^ 2 else 0) ≤
      v₁ * Rt N R χ t X M₂ (c / v₁) a ^ 2 := by
  set L := N * M₂ / q with hLdef
  set F : ℝ → ℝ := fun u =>
    if |u - c / v₁| ≤ δ / v₁ ∧ u ∈ Icc (1 / 2 : ℝ) 2 then ‖Rf R χ t u a‖ ^ 2 else 0 with hF
  have hmR : Measurable fun u : ℝ => ‖Rf R χ t u a‖ ^ 2 := ((measurable_Rf R χ t a).norm).pow_const 2
  have hF0 : ∀ u, 0 ≤ F u := fun u => by simp only [hF]; split_ifs <;> positivity
  have hFm : Measurable F := by
    have h1 : MeasurableSet {u : ℝ | |u - c / v₁| ≤ δ / v₁} := measurableSet_le (by fun_prop) measurable_const
    have hS : MeasurableSet {u : ℝ | |u - c / v₁| ≤ δ / v₁ ∧ u ∈ Icc (1 / 2 : ℝ) 2} := h1.inter measurableSet_Icc
    exact Measurable.ite hS hmR measurable_const
  have hFi : Integrable F := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Icc (1 / 2 : ℝ) 2) ?_ fun u hu => ?_
    · refine integrableOn_Icc_of_le hFm (C := (R.card : ℝ) ^ 2) fun u hu => ?_
      rw [abs_of_nonneg (hF0 u)]
      simp only [hF]; split_ifs
      · exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hu.1]) a) 2
      · positivity
    · simp only [hF]; split_ifs with h
      · exact absurd h.2 hu
      · rfl
  have hG : ∀ v₂, (if |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then ‖Rf R χ t (v₂ / v₁) a‖ ^ 2 else 0) =
      F (v₂ / v₁) := by
    intro v₂
    have e : |v₂ / v₁ - c / v₁| ≤ δ / v₁ ↔ |v₂ - c| ≤ δ := by
      rw [← sub_div, abs_div, abs_of_pos hv₁, div_le_div_iff_of_pos_right hv₁]
    simp only [hF, e]
  have hle : ∫ v₂ in Icc (1 / 2 : ℝ) 2, F (v₂ / v₁) ≤ ∫ v₂, F (v₂ / v₁) :=
    setIntegral_le_integral (hFi.comp_div hv₁.ne') (Filter.Eventually.of_forall fun v₂ => hF0 _)
  have hsub : ∫ v₂, F (v₂ / v₁) = v₁ * ∫ u in Icc (1 / 2 : ℝ) 2, (if |u - c / v₁| ≤ δ / v₁ then
      ‖Rf R χ t u a‖ ^ 2 else 0) := by
    rw [Measure.integral_comp_div, abs_of_pos hv₁, smul_eq_mul]
    congr 1
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm.trans
      (setIntegral_congr_fun measurableSet_Icc fun u hu => ?_)
    · simp only [hF]; split_ifs with h
      · exact absurd h.2 hu
      · rfl
    · simp only [hF, hu, and_true]
  have hloc := local_le_Rt_sq R χ t hX hL (c := c / v₁) (δ := δ / v₁) hδ a
  simp only [hG]
  calc L * ∫ v₂ in Icc (1 / 2 : ℝ) 2, F (v₂ / v₁) ≤ L * ∫ v₂, F (v₂ / v₁) :=
        mul_le_mul_of_nonneg_left hle hL.le
    _ = v₁ * (L * ∫ u in Icc (1 / 2 : ℝ) 2, (if |u - c / v₁| ≤ δ / v₁ then ‖Rf R χ t u a‖ ^ 2 else 0)) := by
        rw [hsub]; ring
    _ ≤ v₁ * Rt N R χ t X M₂ (c / v₁) a ^ 2 := mul_le_mul_of_nonneg_left hloc hv₁.le

/-- **Cauchy–Schwarz on `[1/2, 2]`** for nonnegative bounded measurable functions. -/
lemma cs_Icc {f g : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x ∈ Icc (1 / 2 : ℝ) 2, f x ≤ Cf) (hgb : ∀ x ∈ Icc (1 / 2 : ℝ) 2, g x ≤ Cg) :
    ∫ x in Icc (1 / 2 : ℝ) 2, f x * g x ≤
      Real.sqrt (∫ x in Icc (1 / 2 : ℝ) 2, f x ^ 2) * Real.sqrt (∫ x in Icc (1 / 2 : ℝ) 2, g x ^ 2) := by
  have : IsFiniteMeasure (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hf2 : MemLp f (ENNReal.ofReal 2) (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    MemLp.of_bound hfm.aestronglyMeasurable Cf ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hfb x hx))
  have hg2 : MemLp g (ENNReal.ofReal 2) (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    MemLp.of_bound hgm.aestronglyMeasurable Cg ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgb x hx))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hf2 hg2
  simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using h

/-- **The inner `v₂` integral by Cauchy–Schwarz**: for `v₁ ∈ [1/2, 2]`, `L = NM₂/q > 0` and `Lδ ≤ X`,
`L∫_{[1/2,2], |v₂−c|≤δ, v₂/v₁∈[1/2,2]}|R(v₂/v₁, a)||R(1/v₂, b⁻¹)| ≤ 2R̃_{M₂}(c/v₁, a)R̃_{M₂}(c, b)`. -/
lemma inner_le {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X M₂ : ℝ} (hX : 0 < X) (hL : 0 < N * M₂ / q) {v₁ c δ : ℝ} (hv₁ : v₁ ∈ Icc (1 / 2 : ℝ) 2)
    (hδ : N * M₂ / q * δ ≤ X) (a : ZMod q) (b : (ZMod q)ˣ) :
    N * M₂ / q * ∫ v₂ in Icc (1 / 2 : ℝ) 2, (if |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then
      ‖Rf R χ t (v₂ / v₁) a‖ * ‖Rf R χ t (1 / v₂) ((b⁻¹ : (ZMod q)ˣ) : ZMod q)‖ else 0) ≤
      2 * (Rt N R χ t X M₂ (c / v₁) a * Rt N R χ t X M₂ c (b : ZMod q)) := by
  set L := N * M₂ / q with hLdef
  have hv0 : 0 < v₁ := by linarith [hv₁.1]
  set f : ℝ → ℝ := fun v₂ => if |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then ‖Rf R χ t (v₂ / v₁) a‖ else 0
    with hf
  set g : ℝ → ℝ := fun v₂ => if |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then
    ‖Rf R χ t (1 / v₂) ((b⁻¹ : (ZMod q)ˣ) : ZMod q)‖ else 0 with hg
  have hS : MeasurableSet {v₂ : ℝ | |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2} := by
    have h1 : MeasurableSet {v₂ : ℝ | |v₂ - c| ≤ δ} := measurableSet_le (by fun_prop) measurable_const
    have h2 : MeasurableSet {v₂ : ℝ | v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2} :=
      (measurable_id.div_const v₁) measurableSet_Icc
    exact h1.inter h2
  have hfm : Measurable f :=
    Measurable.ite hS ((measurable_Rf R χ t a).comp (measurable_id.div_const v₁)).norm measurable_const
  have hgm : Measurable g :=
    Measurable.ite hS ((measurable_Rf R χ t _).comp (measurable_const.div measurable_id)).norm measurable_const
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; split_ifs <;> positivity
  have hg0 : ∀ x, 0 ≤ g x := fun x => by simp only [hg]; split_ifs <;> positivity
  have hfb : ∀ x ∈ Icc (1 / 2 : ℝ) 2, f x ≤ R.card := fun x hx => by
    simp only [hf]; split_ifs with h
    · exact norm_Rf_le R χ t (div_pos (by linarith [hx.1]) hv0) a
    · positivity
  have hgb : ∀ x ∈ Icc (1 / 2 : ℝ) 2, g x ≤ R.card := fun x hx => by
    simp only [hg]; split_ifs with h
    · exact norm_Rf_le R χ t (one_div_pos.2 (by linarith [hx.1])) _
    · positivity
  have hfg : ∀ v₂, (if |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then
      ‖Rf R χ t (v₂ / v₁) a‖ * ‖Rf R χ t (1 / v₂) ((b⁻¹ : (ZMod q)ˣ) : ZMod q)‖ else 0) = f v₂ * g v₂ := by
    intro v₂; simp only [hf, hg]; split_ifs <;> simp
  have hcs := cs_Icc hf0 hg0 hfm hgm hfb hgb
  have hA : L * ∫ x in Icc (1 / 2 : ℝ) 2, f x ^ 2 ≤ v₁ * Rt N R χ t X M₂ (c / v₁) a ^ 2 := by
    have hδv : L * (δ / v₁) ≤ 2 * X := by
      rcases le_or_gt δ 0 with h0 | h0
      · have : L * (δ / v₁) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hL.le (div_nonpos_of_nonpos_of_nonneg h0 hv0.le)
        linarith
      · have h1 : δ / v₁ ≤ 2 * δ := by rw [div_le_iff₀ hv0]; nlinarith [hv₁.1]
        nlinarith [mul_le_mul_of_nonneg_left h1 hL.le]
    have h := ratio_le_Rt_sq R χ t hX hL (c := c) (δ := δ) hv0 hδv a
    refine le_trans (le_of_eq ?_) h
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    simp only [hf]; split_ifs <;> simp
  have hB : L * ∫ x in Icc (1 / 2 : ℝ) 2, g x ^ 2 ≤ Rt N R χ t X M₂ c (b : ZMod q) ^ 2 := by
    have h := local_le_Rt_sq R χ t hX hL (c := c) (δ := δ) (by linarith) (b : ZMod q)
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hL.le) h
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun x hx => ?_
    · exact integrableOn_Icc_of_le (hgm.pow_const 2) (C := (R.card : ℝ) ^ 2) fun x hx => by
        rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (hg0 x) (hgb x hx) 2
    · refine integrableOn_Icc_of_le ?_ (C := (R.card : ℝ) ^ 2) fun x hx => ?_
      · exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
          (((measurable_Rf R χ t _).norm).pow_const 2) measurable_const
      · split_ifs
        · rw [abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hx.1]) _) 2
        · simp
    · have hx0 : 0 < x := by linarith [hx.1]
      simp only [hg]; split_ifs with h1 h2 h2
      · rw [norm_Rf_inv R χ t hx0 b]
      · exact absurd h1.1 h2
      · rw [zero_pow two_ne_zero]; positivity
      · simp
  have hsA : 0 ≤ ∫ x in Icc (1 / 2 : ℝ) 2, f x ^ 2 := setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
  have hsB : 0 ≤ ∫ x in Icc (1 / 2 : ℝ) 2, g x ^ 2 := setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
  have hR1 := Rt_nonneg N R χ t X M₂ (c / v₁) a
  have hR2 := Rt_nonneg N R χ t X M₂ c (b : ZMod q)
  simp only [hfg]
  calc L * ∫ x in Icc (1 / 2 : ℝ) 2, f x * g x
      ≤ L * (Real.sqrt (∫ x in Icc (1 / 2 : ℝ) 2, f x ^ 2) * Real.sqrt (∫ x in Icc (1 / 2 : ℝ) 2, g x ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hL.le
    _ = Real.sqrt (L * ∫ x in Icc (1 / 2 : ℝ) 2, f x ^ 2) * Real.sqrt (L * ∫ x in Icc (1 / 2 : ℝ) 2, g x ^ 2) := by
        rw [Real.sqrt_mul hL.le, Real.sqrt_mul hL.le]
        have := Real.mul_self_sqrt hL.le
        linear_combination (-(Real.sqrt (∫ x in Icc (1 / 2 : ℝ) 2, f x ^ 2) *
          Real.sqrt (∫ x in Icc (1 / 2 : ℝ) 2, g x ^ 2))) * this
    _ ≤ Real.sqrt (v₁ * Rt N R χ t X M₂ (c / v₁) a ^ 2) * Real.sqrt (Rt N R χ t X M₂ c (b : ZMod q) ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt v₁ * (Rt N R χ t X M₂ (c / v₁) a * Rt N R χ t X M₂ c (b : ZMod q)) := by
        rw [Real.sqrt_mul hv0.le, Real.sqrt_sq hR1, Real.sqrt_sq hR2]; ring
    _ ≤ 2 * (Rt N R χ t X M₂ (c / v₁) a * Rt N R χ t X M₂ c (b : ZMod q)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith [hv₁.2])

/-- **The inner integral of their Proposition 7.2**: for `N > 0`, `X > 0`, `|m₂| ≥ M₂ > 0`, `v₁ ∈ [1/2, 2]` and
`c = −(m₁v₁ + m₃)/m₂`, with `V` round 655's `Vr`, `(NM₂/q)∫_{[1/2,2]}V(v₁, v₂) dv₂ ≤
2Σ_{b₁,b₂}(b₁m₁ + b₂m₂ + m₃, q)|R(v₁, b₁)|R̃(c/v₁, b₂b₁⁻¹)R̃(c, b₂)`. -/
lemma Vr_inner_le {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) {X M₂ : ℝ} (hX : 0 < X) (hM₂ : 0 < M₂)
    (hm₂ : M₂ ≤ |(m₂ : ℝ)|) {v₁ : ℝ} (hv₁ : v₁ ∈ Icc (1 / 2 : ℝ) 2) :
    N * M₂ / q * ∫ v₂ in Icc (1 / 2 : ℝ) 2, Vr N R χ t m₁ m₂ m₃ X v₁ v₂ ≤
      2 * ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ,
        (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ) *
          (‖Rf R χ t v₁ b₁‖ * (Rt N R χ t X M₂ (-(m₁ * v₁ + m₃) / m₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) *
            Rt N R χ t X M₂ (-(m₁ * v₁ + m₃) / m₂) (b₂ : ZMod q))) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hL : 0 < N * M₂ / q := by positivity
  have hv0 : 0 < v₁ := by linarith [hv₁.1]
  have hm0 : (m₂ : ℝ) ≠ 0 := fun h => by rw [h, abs_zero] at hm₂; linarith
  set c : ℝ := -(m₁ * v₁ + m₃) / m₂ with hc
  set δ : ℝ := X * q / (N * M₂) with hδdef
  have hLδ : N * M₂ / q * δ ≤ X := le_of_eq (by rw [hδdef]; field_simp)
  set G : (ZMod q)ˣ → (ZMod q)ˣ → ℝ → ℝ := fun b₁ b₂ v₂ =>
    if |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then
      ‖Rf R χ t (v₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q)‖ * ‖Rf R χ t (1 / v₂) ((b₂⁻¹ : (ZMod q)ˣ) : ZMod q)‖
    else 0 with hG
  set w : (ZMod q)ˣ → (ZMod q)ˣ → ℝ := fun b₁ b₂ =>
    (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ) *
      ‖Rf R χ t v₁ b₁‖ with hw
  have hw0 : ∀ b₁ b₂, 0 ≤ w b₁ b₂ := fun b₁ b₂ => by simp only [hw]; positivity
  have hG0 : ∀ b₁ b₂ v₂, 0 ≤ G b₁ b₂ v₂ := fun b₁ b₂ v₂ => by simp only [hG]; split_ifs <;> positivity
  have hS : MeasurableSet {v₂ : ℝ | |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2} := by
    have h1 : MeasurableSet {v₂ : ℝ | |v₂ - c| ≤ δ} := measurableSet_le (by fun_prop) measurable_const
    have h2 : MeasurableSet {v₂ : ℝ | v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2} :=
      (measurable_id.div_const v₁) measurableSet_Icc
    exact h1.inter h2
  have hGi : ∀ b₁ b₂, IntegrableOn (G b₁ b₂) (Icc (1 / 2 : ℝ) 2) := by
    intro b₁ b₂
    refine integrableOn_Icc_of_le (C := (R.card : ℝ) ^ 2) (Measurable.ite hS
      ((((measurable_Rf R χ t _).comp (measurable_id.div_const v₁)).norm).mul
        ((measurable_Rf R χ t _).comp (measurable_const.div measurable_id)).norm) measurable_const) fun x hx => ?_
    rw [abs_of_nonneg (hG0 b₁ b₂ x)]
    simp only [hG]; split_ifs
    · rw [sq]
      exact mul_le_mul (norm_Rf_le R χ t (div_pos (by linarith [hx.1]) hv0) _)
        (norm_Rf_le R χ t (one_div_pos.2 (by linarith [hx.1])) _) (norm_nonneg _) (Nat.cast_nonneg _)
    · positivity
  have hpt : ∀ v₂ ∈ Icc (1 / 2 : ℝ) 2,
      Vr N R χ t m₁ m₂ m₃ X v₁ v₂ ≤ ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, w b₁ b₂ * G b₁ b₂ v₂ := by
    intro v₂ _
    unfold Vr
    split_ifs with h
    · have hS' : |v₂ - c| ≤ δ ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 := by
        refine ⟨?_, h.2⟩
        have e : v₂ - c = (m₁ * v₁ + m₂ * v₂ + m₃) / m₂ := by rw [hc]; field_simp; ring
        rw [e, abs_div, hδdef, div_le_iff₀ (abs_pos.2 hm0)]
        calc |(m₁ : ℝ) * v₁ + m₂ * v₂ + m₃| ≤ X * q / N := h.1
          _ = X * q / (N * M₂) * M₂ := by field_simp
          _ ≤ X * q / (N * M₂) * |(m₂ : ℝ)| := mul_le_mul_of_nonneg_left hm₂ (by positivity)
      unfold Wm
      refine le_of_eq (Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_)
      simp only [hw, hG, hS'.1, hS'.2, and_self, ite_true]
      ring
    · exact Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ => mul_nonneg (hw0 b₁ b₂) (hG0 b₁ b₂ v₂)
  have hsum_int : IntegrableOn (fun v₂ => ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, w b₁ b₂ * G b₁ b₂ v₂)
      (Icc (1 / 2 : ℝ) 2) :=
    integrable_finsetSum _ fun b₁ _ => integrable_finsetSum _ fun b₂ _ => (hGi b₁ b₂).const_mul _
  have hV0 : ∀ v₂, 0 ≤ Vr N R χ t m₁ m₂ m₃ X v₁ v₂ := fun v₂ => by
    unfold Vr; split_ifs
    · exact Wm_nonneg R χ t m₁ m₂ m₃ v₁ v₂
    · exact le_rfl
  have hint : ∫ v₂ in Icc (1 / 2 : ℝ) 2, Vr N R χ t m₁ m₂ m₃ X v₁ v₂ ≤
      ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, w b₁ b₂ * ∫ v₂ in Icc (1 / 2 : ℝ) 2, G b₁ b₂ v₂ := by
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall hV0) hsum_int
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hpt))).trans (le_of_eq ?_)
    rw [integral_finsetSum _ fun b₁ _ => integrable_finsetSum _ fun b₂ _ => (hGi b₁ b₂).const_mul _]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [integral_finsetSum _ fun b₂ _ => (hGi b₁ b₂).const_mul _]
    exact Finset.sum_congr rfl fun b₂ _ => integral_const_mul _ _
  calc N * M₂ / q * ∫ v₂ in Icc (1 / 2 : ℝ) 2, Vr N R χ t m₁ m₂ m₃ X v₁ v₂
      ≤ N * M₂ / q * ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, w b₁ b₂ * ∫ v₂ in Icc (1 / 2 : ℝ) 2, G b₁ b₂ v₂ :=
        mul_le_mul_of_nonneg_left hint hL.le
    _ = ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, w b₁ b₂ * (N * M₂ / q * ∫ v₂ in Icc (1 / 2 : ℝ) 2, G b₁ b₂ v₂) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b₂ _ => by ring
    _ ≤ ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ, w b₁ b₂ *
          (2 * (Rt N R χ t X M₂ (c / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) * Rt N R χ t X M₂ c (b₂ : ZMod q))) :=
        Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
          mul_le_mul_of_nonneg_left (inner_le R χ t hX hL hv₁ hLδ _ b₂) (hw0 b₁ b₂)
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b₂ _ => ?_
        simp only [hw]
        ring

end LinnikCGLRt

#print axioms LinnikCGLRt.Rf_inv
#print axioms LinnikCGLRt.local_le_Rt_sq
#print axioms LinnikCGLRt.ratio_le_Rt_sq
#print axioms LinnikCGLRt.cs_Icc
#print axioms LinnikCGLRt.inner_le
#print axioms LinnikCGLRt.Vr_inner_le
