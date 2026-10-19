/-
# Round 600: separation of smooth comparisons by Fourier inversion over `ℝ^J` (milestone M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. Mathlib's `𝓕` is `ξ ↦ ∫ e^{−2πixξ}f(x) dx`. Let the `g_j`, for `j` in a finite type, be continuous
and integrable with integrable `𝓕g_j`.

* `inv_eq`: `g(u) = ∫ 𝓕g(ξ)e^{2πiξu} dξ`, Fourier inversion at a point (Mathlib's `Continuous.fourierInv_fourier_eq`).
* `prod_eq_integral`, `integrable_prod_fourier`: `∏_j g_j(u_j) = ∫_{ℝ^J} ∏_j 𝓕g_j(ξ_j)e^{2πiξ_ju_j} dξ`, with an
  integrable integrand (Mathlib's `integral_fintype_prod_volume_eq_prod` and `Integrable.fintype_prod`).
* `sum_sep`: for a finite sum, `Σ_{i∈N} w_i ∏_j g_j(ℓ_j(i)) = ∫_{ℝ^J} (∏_j 𝓕g_j(ξ_j))·Σ_{i∈N} w_i e^{2πiΣ_j ξ_jℓ_j(i)} dξ`.
* `sep_bound`: let `F_x(ξ)` be continuous in `ξ` for each `x` of a finite set `s`, with `Σ_x |F_x(ξ)| ≤ B₁` on the box
  `|ξ_j| ≤ T₀` and `Σ_x |F_x(ξ)| ≤ B₂` everywhere, `B₁, B₂ ≥ 0`, and let the `h_j` be integrable. Then
  `Σ_x |∫ ∏_j h_j(ξ_j)F_x(ξ) dξ| ≤ B₁ ∏_j ‖h_j‖₁ + B₂ Σ_j (∫_{|t|>T₀} |h_j(t)| dt) ∏_{i≠j} ‖h_i‖₁`.

This is the separation of `frontier/linnik/SIEVE-ROUTE.md` §13's M4 (§10's Lemma 4′). With the `g_j` the cut-off of
`SieveSmooth`, a family's comparisons become an integral over the heights `ξ`; on the box M3 bounds the integrand, and
outside it the trivial bound and the tails of the `𝓕g_j`. The file imports only Mathlib.
-/
import Mathlib

open MeasureTheory Real Complex FourierTransform Finset

namespace SieveSep

/-! ### Fourier inversion in one variable and in `J` variables -/

/-- Fourier inversion at a point, for `g` continuous and integrable with integrable `𝓕 g`. -/
theorem inv_eq {g : ℝ → ℂ} (hc : Continuous g) (hi : Integrable g) (hf : Integrable (𝓕 g)) (u : ℝ) :
    g u = ∫ ξ : ℝ, 𝓕 g ξ * Complex.exp (2 * π * I * ξ * u) := by
  have hinv := Continuous.fourierInv_fourier_eq hc hi hf
  rw [← congrFun hinv u, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

variable {ι : Type*} [Fintype ι]

/-- **Fourier inversion of a product**: `∏_j g_j(u_j) = ∫_{ℝ^J} ∏_j 𝓕g_j(ξ_j)e^{2πiξ_ju_j} dξ`. -/
theorem prod_eq_integral {g : ι → ℝ → ℂ} (hc : ∀ j, Continuous (g j)) (hi : ∀ j, Integrable (g j))
    (hf : ∀ j, Integrable (𝓕 (g j))) (u : ι → ℝ) :
    ∏ j, g j (u j) = ∫ ξ : ι → ℝ, ∏ j, (𝓕 (g j) (ξ j) * Complex.exp (2 * π * I * ξ j * u j)) := by
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun j (t : ℝ) => 𝓕 (g j) t * Complex.exp (2 * π * I * t * u j))]
  exact Finset.prod_congr rfl fun j _ => inv_eq (hc j) (hi j) (hf j) (u j)

/-- The integrand of `prod_eq_integral` is integrable. -/
theorem integrable_prod_fourier {g : ι → ℝ → ℂ} (hf : ∀ j, Integrable (𝓕 (g j))) (u : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => ∏ j, (𝓕 (g j) (ξ j) * Complex.exp (2 * π * I * ξ j * u j))) := by
  refine Integrable.fintype_prod (f := fun j (t : ℝ) => 𝓕 (g j) t * Complex.exp (2 * π * I * t * u j))
    fun j => ?_
  refine (hf j).mul_bdd (c := 1) (Continuous.cexp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Complex.norm_exp]
  simp

/-- **Separation of a finite sum.** `Σ_{i∈N} w_i ∏_j g_j(ℓ_j(i))` is the integral over `ℝ^J` of
`∏_j 𝓕g_j(ξ_j)` times `Σ_{i∈N} w_i e^{2πi Σ_j ξ_jℓ_j(i)}`. -/
theorem sum_sep {X : Type*} (N : Finset X) (w : X → ℂ) (ℓ : ι → X → ℝ) {g : ι → ℝ → ℂ}
    (hc : ∀ j, Continuous (g j)) (hi : ∀ j, Integrable (g j)) (hf : ∀ j, Integrable (𝓕 (g j))) :
    ∑ i ∈ N, w i * ∏ j, g j (ℓ j i) =
      ∫ ξ : ι → ℝ, (∏ j, 𝓕 (g j) (ξ j)) *
        ∑ i ∈ N, w i * Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * ℓ j i) := by
  have h1 : ∀ i ∈ N, w i * ∏ j, g j (ℓ j i) =
      ∫ ξ : ι → ℝ, w i * ∏ j, (𝓕 (g j) (ξ j) * Complex.exp (2 * π * I * ξ j * ℓ j i)) := by
    intro i _
    rw [prod_eq_integral hc hi hf (fun j => ℓ j i), integral_const_mul]
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum]
    have : ∀ j, 2 * ↑π * I * ↑(ξ j) * ↑(ℓ j i) = 2 * ↑π * I * (↑(ξ j) * ↑(ℓ j i)) := fun j => by ring
    simp only [this]
    ring
  · intro i _
    exact (integrable_prod_fourier hf (fun j => ℓ j i)).const_mul (w i)

/-- **The bound after separation.** Let `F_x(ξ)` be continuous in `ξ` for each `x` of a finite set `s`, with
`Σ_x ‖F_x(ξ)‖ ≤ B₁` on the box `|ξ_j| ≤ T₀` and `≤ B₂` everywhere. Then
`Σ_x ‖∫ ∏_j h_j(ξ_j) F_x(ξ) dξ‖ ≤ B₁ ∏_j ‖h_j‖₁ + B₂ Σ_j (∫_{|t|>T₀} ‖h_j‖) ∏_{i≠j} ‖h_i‖₁`. -/
theorem sep_bound {X : Type*} [DecidableEq ι] (s : Finset X) (F : X → (ι → ℝ) → ℂ) (hF : ∀ x, Continuous (F x))
    {h : ι → ℝ → ℂ} (hh : ∀ j, Integrable (h j)) {T₀ B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hB₁ : ∀ ξ : ι → ℝ, (∀ j, |ξ j| ≤ T₀) → ∑ x ∈ s, ‖F x ξ‖ ≤ B₁)
    (hB₂ : ∀ ξ : ι → ℝ, ∑ x ∈ s, ‖F x ξ‖ ≤ B₂) :
    ∑ x ∈ s, ‖∫ ξ : ι → ℝ, (∏ j, h j (ξ j)) * F x ξ‖ ≤
      B₁ * (∏ j, ∫ t, ‖h j t‖) +
        B₂ * ∑ j, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖h j t‖) t) *
          ∏ i ∈ Finset.univ.erase j, ∫ t, ‖h i t‖ := by
  -- the weight `∏_j ‖h_j(ξ_j)‖` and its integrability
  set H : (ι → ℝ) → ℝ := fun ξ => ∏ j, ‖h j (ξ j)‖ with hHdef
  have hHi : Integrable H := Integrable.fintype_prod (f := fun j t => ‖h j t‖) fun j => (hh j).norm
  -- the tail weights
  set E : ι → (ι → ℝ) → ℝ := fun j ξ =>
    ∏ i, (if i = j then Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖h i t‖) (ξ i) else ‖h i (ξ i)‖) with hEdef
  have hEi : ∀ j, Integrable (E j) := by
    intro j
    refine Integrable.fintype_prod
      (f := fun i t => if i = j then Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖h i t‖) t else ‖h i t‖)
      fun i => ?_
    split_ifs
    · exact (hh i).norm.indicator (measurableSet_lt measurable_const measurable_norm)
    · exact (hh i).norm
  have hEint : ∀ j, ∫ ξ, E j ξ = (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖h j t‖) t) *
      ∏ i ∈ Finset.univ.erase j, ∫ t, ‖h i t‖ := by
    intro j
    rw [hEdef, integral_fintype_prod_volume_eq_prod
      (f := fun i t => if i = j then Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖h i t‖) t else ‖h i t‖),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [ite_true]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [Finset.ne_of_mem_erase hi]
  have hHint : ∫ ξ, H ξ = ∏ j, ∫ t, ‖h j t‖ := by
    rw [hHdef, integral_fintype_prod_volume_eq_prod (f := fun j t => ‖h j t‖)]
  -- pointwise: `H(ξ) Σ_x ‖F_x(ξ)‖ ≤ B₁H(ξ) + B₂ Σ_j E_j(ξ)`
  have hpt : ∀ ξ : ι → ℝ, H ξ * ∑ x ∈ s, ‖F x ξ‖ ≤ B₁ * H ξ + B₂ * ∑ j, E j ξ := by
    intro ξ
    have hH0 : 0 ≤ H ξ := Finset.prod_nonneg fun j _ => norm_nonneg _
    by_cases hbox : ∀ j, |ξ j| ≤ T₀
    · have hE0 : 0 ≤ ∑ j, E j ξ := Finset.sum_nonneg fun j _ => Finset.prod_nonneg fun i _ => by
        split_ifs
        · exact Set.indicator_nonneg (fun t _ => norm_nonneg _) _
        · exact norm_nonneg _
      calc H ξ * ∑ x ∈ s, ‖F x ξ‖ ≤ H ξ * B₁ := mul_le_mul_of_nonneg_left (hB₁ ξ hbox) hH0
        _ ≤ B₁ * H ξ + B₂ * ∑ j, E j ξ := by nlinarith [mul_nonneg hB₂0 hE0]
    · push Not at hbox
      obtain ⟨j₀, hj₀⟩ := hbox
      have hEj : E j₀ ξ = H ξ := by
        rw [hEdef, hHdef]
        refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs with hij
        · subst hij
          rw [Set.indicator_of_mem (show ξ i ∈ {t : ℝ | T₀ < |t|} from hj₀)]
        · rfl
      have hEle : E j₀ ξ ≤ ∑ j, E j ξ :=
        Finset.single_le_sum (f := fun j => E j ξ) (fun j _ => Finset.prod_nonneg fun i _ => by
          split_ifs
          · exact Set.indicator_nonneg (fun t _ => norm_nonneg _) _
          · exact norm_nonneg _) (Finset.mem_univ j₀)
      calc H ξ * ∑ x ∈ s, ‖F x ξ‖ ≤ H ξ * B₂ := mul_le_mul_of_nonneg_left (hB₂ ξ) hH0
        _ = B₂ * E j₀ ξ := by rw [hEj]; ring
        _ ≤ B₂ * ∑ j, E j ξ := mul_le_mul_of_nonneg_left hEle hB₂0
        _ ≤ B₁ * H ξ + B₂ * ∑ j, E j ξ := by nlinarith [mul_nonneg hB₁0 hH0]
  -- integrate
  have hFb : ∀ x ∈ s, ∀ ξ, ‖F x ξ‖ ≤ B₂ := fun x hx ξ =>
    le_trans (Finset.single_le_sum (f := fun x => ‖F x ξ‖) (fun _ _ => norm_nonneg _) hx) (hB₂ ξ)
  have hint : ∀ x ∈ s, Integrable (fun ξ => H ξ * ‖F x ξ‖) := fun x hx =>
    hHi.mul_bdd (c := B₂) (hF x).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs, abs_norm]; exact hFb x hx ξ)
  have hnorm : ∀ x, ∀ ξ : ι → ℝ, ‖(∏ j, h j (ξ j)) * F x ξ‖ = H ξ * ‖F x ξ‖ := fun x ξ => by
    rw [norm_mul, norm_prod]
  have hEsum : Integrable (fun ξ => ∑ j, E j ξ) := integrable_finsetSum _ fun j _ => hEi j
  calc ∑ x ∈ s, ‖∫ ξ : ι → ℝ, (∏ j, h j (ξ j)) * F x ξ‖
      ≤ ∑ x ∈ s, ∫ ξ : ι → ℝ, H ξ * ‖F x ξ‖ := Finset.sum_le_sum fun x _ => by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => hnorm x ξ)
    _ = ∫ ξ : ι → ℝ, H ξ * ∑ x ∈ s, ‖F x ξ‖ := by
        rw [← integral_finsetSum _ hint]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only [Finset.mul_sum]
    _ ≤ ∫ ξ : ι → ℝ, (B₁ * H ξ + B₂ * ∑ j, E j ξ) := by
        refine integral_mono ?_ ((hHi.const_mul B₁).add (hEsum.const_mul B₂)) hpt
        have := integrable_finsetSum s hint
        refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
        simp only [Finset.mul_sum]
    _ = B₁ * (∏ j, ∫ t, ‖h j t‖) +
        B₂ * ∑ j, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖h j t‖) t) *
          ∏ i ∈ Finset.univ.erase j, ∫ t, ‖h i t‖ := by
        rw [integral_add (hHi.const_mul B₁) (hEsum.const_mul B₂), integral_const_mul, integral_const_mul,
          integral_finsetSum _ fun j _ => hEi j, hHint]
        congr 2
        exact Finset.sum_congr rfl fun j _ => hEint j

end SieveSep
