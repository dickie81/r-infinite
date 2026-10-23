/-
# Round 658: their Lemma 9.1, the second moments of `R` and `R̃` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

This file proves Chen–Gupta–Li's Lemma 9.1 at one point per character, where both parts are identities.

Their statement. "Let W be a finite set of pairs (t,χ), where |t| ≤ T and for (t,χ) ≠ (t′,χ′) either χ ≠ χ′ or
|t−t′| ≥ (qT)^ϵ. For any M₂ > 0, we have ∫_{v≍1} Σ_{a mod q, (a,q)=1} |R(v,a)|² dv ≪_ϵ ϕ(q)|W| and
∫_{v≍1} Σ_{a mod q, (a,q)=1} |R̃_{M₂}(v,a)|² dv ⪅ ϕ(q)|W|." (text layer lines 4355–4368; spaces restored, the
integrals, sums and their ranges, the tilde, exponents and subscripts transcribed). Their proof expands the square
against a smooth majorant: "The final equality follows from the orthogonality of characters." (line 4458), and then
"Finally, the terms with t₁ = t₂ contribute ≪ ϕ(q)|W| to the sum." (line 4467, spaces restored, the subscripts
transcribed).

At one point per character. The stack's points have distinct characters (`Set.InjOn χ R`), so the cross terms vanish
exactly and no majorant is needed: `Σ_{a unit}|R(v, a)|² = φ(q)|R|` for every `v > 0` (`sum_norm_Rf_sq`), and its
integral over `[1/2, 2]` is `(3/2)φ(q)|R|` (`lemma91`). For `R̃` the stack integrates over all of `ℝ` rather than
`v ≍ 1`: by Fubini, `∫_ℝR̃_{M₂}(v, a)² dv = 2X∫ψ̃₀·∫_{[1/2,2]}|R(u′, a)|² du′` (`integral_Rt_sq`), with `X` for their
`(qT)^ϵ`, so `∫_ℝΣ_aR̃_{M₂}(v, a)² dv = 2X∫ψ̃₀·(3/2)φ(q)|R|` (`lemma91_Rt`). Since `0 ≤ ψ̃₀ ≤ 1` vanishes off
`(−2, 2)`, `2X∫ψ̃₀ ≤ 8X`, the factor their `⪅` absorbs.

Plain statements, with `q ≥ 1`, `χ` injective on `R` and `L = NM₂/q`.
* `sum_units_eq`, `sum_units_mul_star`: `Σ_{a unit}χ(a)conj(ψ(a)) = φ(q)[χ = ψ]` for Dirichlet characters mod `q`.
* `sum_norm_Rf_sq`: `Σ_{a unit}|R(v, a)|² = φ(q)|R|` for `v > 0`.
* `lemma91`: `∫_{[1/2,2]}Σ_{a unit}|R(v, a)|² dv = (3/2)φ(q)|R|`.
* `integral_kernel`: `∫_ℝLψ̃₀(L(v − u′)/(2X)) dv = 2X∫ψ̃₀` for `L, X > 0`.
* `integral_Rt_sq`: for `L, X > 0`, `v ↦ R̃_{M₂}(v, a)²` is integrable on `ℝ`, with the integral above.
* `lemma91_Rt`: `∫_ℝΣ_{a unit}R̃_{M₂}(v, a)² dv = 2X∫ψ̃₀·(3/2)φ(q)|R|` for `L, X > 0`.

* `sum_units_eq`, `sum_units_mul_star`: orthogonality over the units.
* `norm_cpow_I`, `sum_norm_Rf_sq`, `lemma91`: the part for `R`.
* `integral_kernel`, `psi0_eq_zero`, `Rt_sq`, `integral_Rt_sq`, `lemma91_Rt`: the part for `R̃`.

The next step is their Lemma 9.2, the fourth moments against the energy `E(W)`.

The file imports `LinnikCGLP72.lean`.
-/

import LinnikCGLP72

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLMom

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt LinnikCGLP72

/-! ### Orthogonality over the units -/

/-- A sum over the units of a function vanishing off them is the sum over `ℤ/qℤ`. -/
lemma sum_units_eq {q : ℕ} [NeZero q] (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0) :
    ∑ a : (ZMod q)ˣ, g a = ∑ x : ZMod q, g x :=
  Fintype.sum_of_injective (fun a : (ZMod q)ˣ => (a : ZMod q)) Units.val_injective _ _
    (fun x hx => hg x fun h => hx ⟨h.unit, rfl⟩) fun _ => rfl

/-- **Orthogonality over the units**: `Σ_{a unit}χ(a)conj(ψ(a)) = φ(q)[χ = ψ]`. -/
lemma sum_units_mul_star {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    ∑ a : (ZMod q)ˣ, χ a * star (ψ a) = if χ = ψ then (q.totient : ℂ) else 0 := by
  rw [sum_units_eq (fun x => χ x * star (ψ x)) fun x hx => by simp [MulChar.map_nonunit χ hx]]
  have e : ∑ x : ZMod q, χ x * star (ψ x) = ∑ a ∈ Finset.range q, χ a * star (ψ a) := by
    symm
    exact Finset.sum_nbij' (fun a => (a : ZMod q)) ZMod.val (fun _ _ => Finset.mem_univ _)
      (fun x _ => Finset.mem_range.2 (ZMod.val_lt x)) (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha))
      (fun x _ => ZMod.natCast_zmod_val x) (fun _ _ => rfl)
  rw [e]
  split_ifs with h
  · subst h; exact sum_range_mul_star_self χ
  · exact sum_range_mul_star_eq_zero h

/-! ### Their Lemma 9.1 for `R` -/

lemma norm_cpow_I {v : ℝ} (hv : 0 < v) (τ : ℝ) : ‖(v : ℂ) ^ ((τ : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]; simp

/-- **Their Lemma 9.1 for `R`, exact at one point per character**: for `v > 0`,
`Σ_{a unit}|R(v, a)|² = φ(q)|R|`. -/
lemma sum_norm_Rf_sq {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) (t : ι → ℝ) {v : ℝ} (hv : 0 < v) :
    ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 2 = q.totient * R.card := by
  have hC : ∑ a : (ZMod q)ˣ, ((‖Rf R χ t v a‖ ^ 2 : ℝ) : ℂ) = (q.totient : ℂ) * R.card := by
    have h1 : ∀ a : (ZMod q)ˣ, ((‖Rf R χ t v a‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ R, ∑ j ∈ R, (v : ℂ) ^ ((t i : ℂ) * I) * conj ((v : ℂ) ^ ((t j : ℂ) * I)) *
          (χ i a * star (χ j a)) := by
      intro a
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      unfold Rf
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Complex.star_def]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ i ∈ R, ∑ a : (ZMod q)ˣ, ∑ j ∈ R, (v : ℂ) ^ ((t i : ℂ) * I) * conj ((v : ℂ) ^ ((t j : ℂ) * I)) *
        (χ i a * star (χ j a)) = q.totient := by
      intro i hi
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_units_mul_star]
      rw [Finset.sum_eq_single i]
      · split_ifs with h
        · rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_cpow_I hv]; simp
        · exact absurd rfl h
      · intro j hj hji
        have hne : ¬(χ i = χ j) := fun h => hji (hinj hj hi h.symm)
        simp [hne]
      · intro h; exact absurd hi h
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact_mod_cast hC

/-- **Their Lemma 9.1 for `R`**: `∫_{[1/2,2]}Σ_{a unit}|R(v, a)|² dv = (3/2)φ(q)|R|`. -/
theorem lemma91 {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) (t : ι → ℝ) :
    ∫ v in Icc (1 / 2 : ℝ) 2, ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 2 = 3 / 2 * (q.totient * R.card) := by
  have h : ∫ v in Icc (1 / 2 : ℝ) 2, ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 2 =
      ∫ _ in Icc (1 / 2 : ℝ) 2, (q.totient : ℝ) * R.card :=
    setIntegral_congr_fun measurableSet_Icc fun v hv => sum_norm_Rf_sq R hinj t (by linarith [hv.1] : 0 < v)
  rw [h, setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
  ring

/-! ### Their Lemma 9.1 for `R̃` -/

/-- The kernel of `R̃` integrates to `2X∫ψ̃₀`: `∫_ℝ Lψ̃₀(L(v − u′)/(2X)) dv = 2X∫ψ̃₀` for `L, X > 0`. -/
lemma integral_kernel {L X : ℝ} (hL : 0 < L) (hX : 0 < X) (u' : ℝ) :
    ∫ v, L * psi0 (L * (v - u') / (2 * X)) = 2 * X * ∫ x, psi0 x := by
  rw [integral_const_mul]
  have e : (fun v => psi0 (L * (v - u') / (2 * X))) = fun v => (fun w => psi0 (L / (2 * X) * w)) (v - u') := by
    funext v; congr 1; ring
  rw [e, integral_sub_right_eq_self (fun w => psi0 (L / (2 * X) * w)) u', Measure.integral_comp_mul_left]
  have : (0 : ℝ) < L / (2 * X) := by positivity
  rw [abs_of_pos (inv_pos.2 this), smul_eq_mul, inv_div]
  field_simp

lemma psi0_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : psi0 x = 0 :=
  psiBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx)

/-- `R̃_{M₂}(v, a)² = ∫_{[1/2,2]}Lψ̃₀(L(v − u′)/(2X))|R(u′, a)|² du′` for `L ≥ 0`. -/
lemma Rt_sq {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hL : 0 ≤ N * M₂ / q) (v : ℝ) (a : ZMod q) :
    Rt N R χ t X M₂ v a ^ 2 =
      ∫ u' in Icc (1 / 2 : ℝ) 2, N * M₂ / q * psi0 (N * M₂ / q * (v - u') / (2 * X)) * ‖Rf R χ t u' a‖ ^ 2 :=
  Real.sq_sqrt (setIntegral_nonneg measurableSet_Icc fun u' _ => by
    have := psi0_nonneg (N * M₂ / q * (v - u') / (2 * X)); positivity)

/-- **Fubini for `R̃²`**: for `L, X > 0`, `v ↦ R̃_{M₂}(v, a)²` is integrable on `ℝ` and
`∫_ℝR̃_{M₂}(v, a)² dv = 2X∫ψ̃₀·∫_{[1/2,2]}|R(u′, a)|² du′`. -/
lemma integral_Rt_sq {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hX : 0 < X) (hL : 0 < N * M₂ / q) (a : ZMod q) :
    Integrable (fun v => Rt N R χ t X M₂ v a ^ 2) ∧
      ∫ v, Rt N R χ t X M₂ v a ^ 2 = 2 * X * (∫ x, psi0 x) * ∫ u' in Icc (1 / 2 : ℝ) 2, ‖Rf R χ t u' a‖ ^ 2 := by
  set L := N * M₂ / q with hLdef
  set g : ℝ → ℝ := (Icc (1 / 2 : ℝ) 2).indicator fun u => ‖Rf R χ t u a‖ ^ 2 with hg
  set F : ℝ × ℝ → ℝ := fun p => L * psi0 (L * (p.1 - p.2) / (2 * X)) * g p.2 with hF
  have hmR : Measurable fun u : ℝ => ‖Rf R χ t u a‖ ^ 2 := ((measurable_Rf R χ t a).norm).pow_const 2
  have hgm : Measurable g := hmR.indicator measurableSet_Icc
  have hg0 : ∀ u, 0 ≤ g u := fun u => by
    simp only [hg, Set.indicator]; split_ifs <;> positivity
  have hgb : ∀ u, g u ≤ (R.card : ℝ) ^ 2 * (Icc (1 / 2 : ℝ) 2).indicator 1 u := fun u => by
    simp only [hg, Set.indicator]; split_ifs with h
    · simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [h.1]) a) 2
    · simp
  set A := 1 / 2 - 4 * X / L with hA
  set B := 2 + 4 * X / L with hB
  have hFm : Measurable F :=
    (measurable_const.mul (continuous_psi0.measurable.comp (by fun_prop))).mul (hgm.comp measurable_snd)
  have hFint : Integrable F (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => L * (R.card : ℝ) ^ 2 *
        ((Icc A B).indicator (fun _ => (1 : ℝ)) p.1 * (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.2))
        (volume.prod volume) := by
      refine Integrable.const_mul ?_ _
      exact Integrable.mul_prod ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
        ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
    refine hdom.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hp0 := psi0_nonneg (L * (p.1 - p.2) / (2 * X))
    have hI0 : 0 ≤ L * (R.card : ℝ) ^ 2 *
        ((Icc A B).indicator (fun _ => (1 : ℝ)) p.1 * (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.2) :=
      mul_nonneg (by positivity) (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hL.le hp0) (hg0 _))]
    by_cases h2 : p.2 ∈ Icc (1 / 2 : ℝ) 2
    · by_cases h1 : |p.1 - p.2| < 4 * X / L
      · have hp1 : p.1 ∈ Icc A B := by
          refine ⟨?_, ?_⟩ <;> linarith [(abs_lt.1 h1).1, (abs_lt.1 h1).2, h2.1, h2.2, hA, hB]
        rw [Set.indicator_of_mem hp1, Set.indicator_of_mem h2, mul_one, mul_one]
        have := hgb p.2
        rw [Set.indicator_of_mem h2, Pi.one_apply, mul_one] at this
        calc L * psi0 (L * (p.1 - p.2) / (2 * X)) * g p.2 ≤ L * 1 * (R.card : ℝ) ^ 2 :=
              mul_le_mul (mul_le_mul_of_nonneg_left (psi0_le_one _) hL.le) this (hg0 _) (by positivity)
          _ = L * (R.card : ℝ) ^ 2 := by ring
      · have hz : psi0 (L * (p.1 - p.2) / (2 * X)) = 0 := by
          refine psi0_eq_zero ?_
          rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * X), le_div_iff₀
            (by positivity)]
          push Not at h1
          calc 2 * (2 * X) = L * (4 * X / L) := by field_simp; ring
            _ ≤ L * |p.1 - p.2| := mul_le_mul_of_nonneg_left h1 hL.le
        rw [hz, mul_zero, zero_mul]
        exact hI0
    · have : g p.2 = 0 := by simp only [hg]; exact Set.indicator_of_notMem h2 _
      rw [this, mul_zero]
      exact hI0
  have hinner : ∀ v, ∫ u', F (v, u') = Rt N R χ t X M₂ v a ^ 2 := by
    intro v
    rw [Rt_sq R χ t hL.le v a, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
    simp only [hF, hg, Set.indicator]
    split_ifs <;> simp [hLdef]
  have hint1 : Integrable (fun v => Rt N R χ t X M₂ v a ^ 2) := by
    have := hFint.integral_prod_left
    simpa only [hinner] using this
  refine ⟨hint1, ?_⟩
  have hswap := integral_integral_swap (f := fun v u' => F (v, u')) hFint
  have hright : ∀ u', ∫ v, F (v, u') = 2 * X * (∫ x, psi0 x) * g u' := by
    intro u'
    simp only [hF]
    rw [integral_mul_const, integral_kernel hL hX u']
  simp only [hinner, hright] at hswap
  rw [hswap, integral_const_mul, hg, integral_indicator measurableSet_Icc]

/-- **Their Lemma 9.1 for `R̃`, exact at one point per character**: for `L = NM₂/q > 0` and `X > 0`,
`∫_ℝΣ_{a unit}R̃_{M₂}(v, a)² dv = 2X∫ψ̃₀·(3/2)φ(q)|R|`. -/
theorem lemma91_Rt {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) (t : ι → ℝ) {X M₂ : ℝ} (hX : 0 < X) (hL : 0 < N * M₂ / q) :
    ∫ v, ∑ a : (ZMod q)ˣ, Rt N R χ t X M₂ v a ^ 2 = 2 * X * (∫ x, psi0 x) * (3 / 2 * (q.totient * R.card)) := by
  rw [integral_finsetSum (s := Finset.univ) (f := fun (a : (ZMod q)ˣ) v => Rt N R χ t X M₂ v (a : ZMod q) ^ 2)
    fun a _ => (integral_Rt_sq R χ t hX hL (a : ZMod q)).1]
  simp_rw [fun a : (ZMod q)ˣ => (integral_Rt_sq R χ t hX hL (a : ZMod q)).2]
  rw [← Finset.mul_sum, ← lemma91 R hinj t,
    integral_finsetSum (s := Finset.univ) (f := fun (a : (ZMod q)ˣ) v => ‖Rf R χ t v (a : ZMod q)‖ ^ 2)]
  intro a _
  refine integrableOn_Icc_of_le (((measurable_Rf R χ t _).norm).pow_const 2) (C := (R.card : ℝ) ^ 2)
    fun x hx => ?_
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hx.1]) _) 2

end LinnikCGLMom

#print axioms LinnikCGLMom.sum_units_mul_star
#print axioms LinnikCGLMom.sum_norm_Rf_sq
#print axioms LinnikCGLMom.lemma91
#print axioms LinnikCGLMom.integral_kernel
#print axioms LinnikCGLMom.integral_Rt_sq
#print axioms LinnikCGLMom.lemma91_Rt
