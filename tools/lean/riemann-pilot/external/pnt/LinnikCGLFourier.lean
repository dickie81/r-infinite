/-
# Round 645: Chen–Gupta–Li's Lemma 4.3 (1), the decay of `ĥ_t` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

The `S₃` side of Chen–Gupta–Li's argument starts from the Poisson expansion of the Gram entries in residue classes
(their Lemmas 4.4 and 4.5), whose terms carry the Fourier transform of `h_t(u) = w(u)²u^{it}`. This file proves the
decay of that transform, their Lemma 4.3 (1): "For any integer j ≥ 0, ĥ_t(ξ) ≪_j (1 + |t|)^j/|ξ|^j" (spaces restored,
the hat, the subscripts and the exponents transcribed). They say of its proof: "The proof (cf. [5, Lemma 4.3]) relies on
the properties of the function w(u) and repeated applications of integration by parts." Here `w` is round 638's `wCGL`
and `h_t` is round 640's `Wt t`. Mathlib's `𝓕f(ξ) = ∫ e^{−2πixξ}f(x) dx` is their `ĥ(ξ)`.

Plain statement (`lemma43`). For every `K` there is `C_K ≥ 0` (`CF K`) such that for all real `τ` and `ξ`,
`(2π|ξ|)^K|ĥ_τ(ξ)| ≤ C_K(1 + |τ|)^K`.

The proof makes the integrations by parts explicit. The `k`-th derivative of `h_τ` is
`F_k(u) = u^{iτ}Σ_{j≤k}(iτ)^j c_{k,j}(u)`, with coefficients that do not depend on `τ`: `c_{0,0} = w²`,
`c_{k+1,0} = c′_{k,0}` and `c_{k+1,j+1} = c′_{k,j+1} + c_{k,j}/u`. Each `c_{k,j}` is smooth and vanishes for `u ≤ 1`
and `u ≥ 2`. So `|F_K(u)| ≤ Σ_j|τ|^j|c_{K,j}(u)|` and `C_K = Σ_{j≤K}∫|c_{K,j}|`.

* `Off12`, `cf`, `off12_deriv`, `contDiff_mul_inv`, `cf_props`, `cf_eq_zero_of_lt`, `integrable_cf`: the coefficients.
  A smooth function vanishing for `u ≤ 1` and `u ≥ 2` has a derivative vanishing there too: it is locally `0` on the
  open parts, and the zero set of the continuous derivative is closed.
* `F`, `F_zero`, `F_eq_zero`, `sum_cf_succ`, `hasDerivAt_F`: `F_0 = h_τ` and `F_k′ = F_{k+1}`, by the product rule
  with `(u^{iτ})′ = iτu^{iτ}u⁻¹` on `[1, 2]`, and because `F_k` is locally `0` near every `u < 1` and every `u > 2`.
* `fourier_F_succ`, `fourier_F`: `𝓕F_K(ξ) = (2πiξ)^K·ĥ_τ(ξ)` (Mathlib's `Real.fourier_deriv`, `K` times).
* `norm_F_le`, `CF`, `lemma43`: `|𝓕F_K(ξ)| ≤ ∫|F_K| ≤ C_K(1 + |τ|)^K`.

The file imports `LinnikCGLS2.lean`.
-/

import LinnikCGLS2

open Complex Set Real Filter Topology MeasureTheory FourierTransform
open scoped ContDiff

noncomputable section

namespace LinnikCGLFourier

open LinnikCGLMat LinnikCGLMellin

/-! ### The coefficient functions -/

/-- Vanishing for `u ≤ 1` and for `u ≥ 2`. -/
def Off12 (f : ℝ → ℝ) : Prop := ∀ u, (u ≤ 1 ∨ 2 ≤ u) → f u = 0

/-- The coefficients `c_{k,j}`: `c_{0,0} = w²`, `c_{0,j} = 0` for `j ≥ 1`, `c_{k+1,0} = c′_{k,0}` and
`c_{k+1,j+1} = c′_{k,j+1} + c_{k,j}/u`. -/
def cf : ℕ → ℕ → ℝ → ℝ
  | 0, 0 => wsq
  | 0, _ + 1 => fun _ => 0
  | k + 1, 0 => deriv (cf k 0)
  | k + 1, j + 1 => fun u => deriv (cf k (j + 1)) u + cf k j u * u⁻¹

/-- A smooth function vanishing for `u ≤ 1` and `u ≥ 2` has a derivative vanishing there too: on the open parts it
is locally `0`, and the zero set of the continuous derivative is closed. -/
lemma off12_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (h0 : Off12 f) : Off12 (deriv f) := by
  have hc : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hopen : ∀ u, (u < 1 ∨ 2 < u) → deriv f u = 0 := by
    intro u hu
    have hev : f =ᶠ[𝓝 u] fun _ => 0 := by
      rcases hu with hu | hu
      · filter_upwards [Iio_mem_nhds hu] with x hx using h0 x (Or.inl (le_of_lt hx))
      · filter_upwards [Ioi_mem_nhds hu] with x hx using h0 x (Or.inr (le_of_lt hx))
    rw [hev.deriv_eq]; simp
  have hclosed : IsClosed {u | deriv f u = 0} := isClosed_eq hc continuous_const
  intro u hu
  rcases hu with hu | hu
  · have hsub : Iio (1 : ℝ) ⊆ {u | deriv f u = 0} := fun x hx => hopen x (Or.inl hx)
    have := hclosed.closure_subset_iff.2 hsub
    rw [closure_Iio] at this
    exact this hu
  · have hsub : Ioi (2 : ℝ) ⊆ {u | deriv f u = 0} := fun x hx => hopen x (Or.inr hx)
    have := hclosed.closure_subset_iff.2 hsub
    rw [closure_Ioi] at this
    exact this hu

/-- `f(u)/u` is smooth when `f` is smooth and vanishes for `u ≤ 1`. -/
lemma contDiff_mul_inv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (h0 : Off12 f) :
    ContDiff ℝ ∞ (fun u => f u * u⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge u 1 with hu | hu
  · have hev : (fun u => f u * u⁻¹) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu] with x hx
      rw [h0 x (Or.inl (le_of_lt hx)), zero_mul]
    exact (contDiffAt_const).congr_of_eventuallyEq hev
  · have hu0 : u ≠ 0 := by linarith
    exact hf.contDiffAt.mul (contDiffAt_inv ℝ hu0)

/-- Each `c_{k,j}` is smooth and vanishes for `u ≤ 1` and `u ≥ 2`. -/
lemma cf_props : ∀ k j, ContDiff ℝ ∞ (cf k j) ∧ Off12 (cf k j)
  | 0, 0 => ⟨contDiff_wsq, fun _ hu => wsq_eq_zero hu⟩
  | 0, _ + 1 => ⟨contDiff_const, fun _ _ => rfl⟩
  | k + 1, 0 => by
      obtain ⟨h1, h2⟩ := cf_props k 0
      exact ⟨(contDiff_infty_iff_deriv.1 h1).2, off12_deriv h1 h2⟩
  | k + 1, j + 1 => by
      obtain ⟨h1, h2⟩ := cf_props k (j + 1)
      obtain ⟨h3, h4⟩ := cf_props k j
      refine ⟨(contDiff_infty_iff_deriv.1 h1).2.add (contDiff_mul_inv h3 h4), fun u hu => ?_⟩
      show deriv (cf k (j + 1)) u + cf k j u * u⁻¹ = 0
      rw [off12_deriv h1 h2 u hu, h4 u hu]; ring

lemma cf_contDiff (k j : ℕ) : ContDiff ℝ ∞ (cf k j) := (cf_props k j).1

lemma cf_off12 (k j : ℕ) : Off12 (cf k j) := (cf_props k j).2

/-- `c_{k,j} = 0` for `j > k`. -/
lemma cf_eq_zero_of_lt : ∀ k j, k < j → cf k j = fun _ => 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | k + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j + 1, h => by
      have h1 := cf_eq_zero_of_lt k (j + 1) (by omega)
      have h2 := cf_eq_zero_of_lt k j (by omega)
      funext u
      show deriv (cf k (j + 1)) u + cf k j u * u⁻¹ = 0
      rw [h1, h2]; simp

lemma continuous_cf (k j : ℕ) : Continuous (cf k j) := (cf_contDiff k j).continuous

lemma integrable_cf (k j : ℕ) : Integrable (cf k j) := by
  refine (continuous_cf k j).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun u hu => ?_
  apply cf_off12 k j
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with hu | hu
  · exact Or.inl hu.le
  · exact Or.inr hu.le

/-! ### The derivatives of `h_τ(u) = u^{iτ}w(u)²` -/

/-- `F_k(u) = u^{iτ}Σ_{j≤k}(iτ)^j c_{k,j}(u)`, the `k`-th derivative of `h_τ` (`hasDerivAt_F`, `F_zero`). -/
def F (τ : ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ ((τ : ℂ) * I) * ∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * (cf k j u : ℂ)

lemma F_zero (τ : ℝ) : F τ 0 = Wt τ := by
  funext u
  simp [F, Wt, Wc, cf]

lemma F_eq_zero (τ : ℝ) (k : ℕ) {u : ℝ} (hu : u ≤ 1 ∨ 2 ≤ u) : F τ k u = 0 := by
  unfold F
  rw [Finset.sum_eq_zero fun j _ => by rw [cf_off12 k j u hu]; simp, mul_zero]

/-- The sum identity behind the recursion: `Σ_{j≤k+1}(iτ)^j c_{k+1,j} = Σ_{j≤k}(iτ)^j c′_{k,j} +
iτu⁻¹Σ_{j≤k}(iτ)^j c_{k,j}`. -/
lemma sum_cf_succ (τ : ℝ) (k : ℕ) (u : ℝ) :
    ∑ j ∈ Finset.range (k + 2), (I * τ) ^ j * (cf (k + 1) j u : ℂ) =
      ∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * ((deriv (cf k j) u : ℝ) : ℂ) +
        I * τ * (u : ℂ)⁻¹ * ∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * (cf k j u : ℂ) := by
  rw [Finset.sum_range_succ']
  have h1 : ∀ j ∈ Finset.range (k + 1), (I * τ) ^ (j + 1) * (cf (k + 1) (j + 1) u : ℂ) =
      (I * τ) ^ (j + 1) * ((deriv (cf k (j + 1)) u : ℝ) : ℂ) + I * τ * (u : ℂ)⁻¹ * ((I * τ) ^ j * (cf k j u : ℂ)) := by
    intro j _
    show (I * τ) ^ (j + 1) * ((deriv (cf k (j + 1)) u + cf k j u * u⁻¹ : ℝ) : ℂ) = _
    push_cast; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : (I * τ) ^ 0 * (cf (k + 1) 0 u : ℂ) = (I * τ) ^ 0 * ((deriv (cf k 0) u : ℝ) : ℂ) := rfl
  rw [h2]
  have h3 : ∑ j ∈ Finset.range (k + 1), (I * τ) ^ (j + 1) * ((deriv (cf k (j + 1)) u : ℝ) : ℂ) +
      (I * τ) ^ 0 * ((deriv (cf k 0) u : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * ((deriv (cf k j) u : ℝ) : ℂ) := by
    have h4 := Finset.sum_range_succ' (fun j => (I * τ) ^ j * ((deriv (cf k j) u : ℝ) : ℂ)) (k + 1)
    have h5 : deriv (cf k (k + 1)) u = 0 := by rw [cf_eq_zero_of_lt k (k + 1) (by omega)]; simp
    rw [Finset.sum_range_succ, h5] at h4
    simp only [Complex.ofReal_zero, mul_zero, add_zero] at h4
    rw [h4]
  rw [← h3]; ring

/-- **`F_k′ = F_{k+1}`**: at `u ∈ [1, 2]` by the product rule and `sum_cf_succ`, and elsewhere because `F_k` is locally
`0` near every `u < 1` and every `u > 2` and the closure points are handled by `F_{k+1} = 0` there. -/
lemma hasDerivAt_F (τ : ℝ) (k : ℕ) (u : ℝ) : HasDerivAt (F τ k) (F τ (k + 1) u) u := by
  rcases lt_or_ge u 1 with hu | hu
  · have hev : F τ k =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu] with x hx using F_eq_zero τ k (Or.inl (le_of_lt hx))
    rw [F_eq_zero τ (k + 1) (Or.inl hu.le)]
    exact (hasDerivAt_const u (0 : ℂ)).congr_of_eventuallyEq hev
  rcases lt_or_ge 2 u with hu2 | hu2
  · have hev : F τ k =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hu2] with x hx using F_eq_zero τ k (Or.inr (le_of_lt hx))
    rw [F_eq_zero τ (k + 1) (Or.inr hu2.le)]
    exact (hasDerivAt_const u (0 : ℂ)).congr_of_eventuallyEq hev
  have hu0 : (0 : ℝ) < u := by linarith
  have hslit : ((u : ℝ) : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.2 hu0
  have hpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ ((τ : ℂ) * I))
      ((τ : ℂ) * I * (u : ℂ) ^ ((τ : ℂ) * I - 1)) u :=
    (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.comp_ofReal
  have hsum : HasDerivAt (fun y : ℝ => ∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * (cf k j y : ℂ))
      (∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * ((deriv (cf k j) u : ℝ) : ℂ)) u := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    have hd : HasDerivAt (cf k j) (deriv (cf k j) u) u :=
      ((cf_contDiff k j).differentiable (by simp) u).hasDerivAt
    exact hd.ofReal_comp.const_mul _
  have h : HasDerivAt (F τ k) ((τ : ℂ) * I * (u : ℂ) ^ ((τ : ℂ) * I - 1) *
      ∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * (cf k j u : ℂ) + (u : ℂ) ^ ((τ : ℂ) * I) *
      ∑ j ∈ Finset.range (k + 1), (I * τ) ^ j * ((deriv (cf k j) u : ℝ) : ℂ)) u := hpow.mul hsum
  have hcp : (u : ℂ) ^ ((τ : ℂ) * I - 1) = (u : ℂ) ^ ((τ : ℂ) * I) * (u : ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ (by exact_mod_cast hu0.ne'), Complex.cpow_one, div_eq_mul_inv]
  refine h.congr_deriv ?_
  unfold F
  rw [sum_cf_succ, hcp]
  ring

lemma deriv_F (τ : ℝ) (k : ℕ) : deriv (F τ k) = F τ (k + 1) := funext fun u => (hasDerivAt_F τ k u).deriv

lemma continuous_F (τ : ℝ) (k : ℕ) : Continuous (F τ k) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_F τ k u).continuousAt

lemma integrable_F (τ : ℝ) (k : ℕ) : Integrable (F τ k) := by
  refine (continuous_F τ k).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun u hu => ?_
  apply F_eq_zero τ k
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with hu | hu
  · exact Or.inl hu.le
  · exact Or.inr hu.le

/-- `𝓕F_{k+1}(ξ) = 2πiξ·𝓕F_k(ξ)` (Mathlib's `Real.fourier_deriv`). -/
lemma fourier_F_succ (τ : ℝ) (k : ℕ) (ξ : ℝ) : 𝓕 (F τ (k + 1)) ξ = (2 * π * I * ξ) • 𝓕 (F τ k) ξ := by
  have h := Real.fourier_deriv (integrable_F τ k) (fun u => (hasDerivAt_F τ k u).differentiableAt)
    (by rw [deriv_F]; exact integrable_F τ (k + 1))
  rw [deriv_F] at h
  exact congrFun h ξ

lemma fourier_F (τ : ℝ) (K : ℕ) (ξ : ℝ) : 𝓕 (F τ K) ξ = (2 * π * I * ξ) ^ K * 𝓕 (Wt τ) ξ := by
  induction K with
  | zero => rw [F_zero]; simp
  | succ K ih => rw [fourier_F_succ, ih, smul_eq_mul, pow_succ]; ring

/-- `|F_K(u)| ≤ Σ_{j≤K}|τ|^j|c_{K,j}(u)|`, since `|u^{iτ}| = 1` for `u > 0` and `F_K` vanishes for `u ≤ 1`. -/
lemma norm_F_le (τ : ℝ) (K : ℕ) (u : ℝ) :
    ‖F τ K u‖ ≤ ∑ j ∈ Finset.range (K + 1), |τ| ^ j * |cf K j u| := by
  rcases le_or_gt u 1 with hu | hu
  · rw [F_eq_zero τ K (Or.inl hu), norm_zero]
    exact Finset.sum_nonneg fun j _ => by positivity
  have hu0 : (0 : ℝ) < u := by linarith
  unfold F
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have hre : ((τ : ℂ) * I).re = 0 := by simp
  rw [hre, Real.rpow_zero, one_mul]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs]

/-- The constant `C_K = Σ_{j≤K}∫|c_{K,j}|` of Lemma 4.3 (1). -/
def CF (K : ℕ) : ℝ := ∑ j ∈ Finset.range (K + 1), ∫ u, |cf K j u|

lemma CF_nonneg (K : ℕ) : 0 ≤ CF K := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => abs_nonneg _

/-- **Chen–Gupta–Li's Lemma 4.3 (1)**: for `h_τ(u) = w(u)²u^{iτ}` and every `K`,
`(2π|ξ|)^K|ĥ_τ(ξ)| ≤ C_K(1 + |τ|)^K` with `C_K` independent of `τ` and `ξ`. -/
theorem lemma43 (τ : ℝ) (K : ℕ) (ξ : ℝ) :
    (2 * π * |ξ|) ^ K * ‖𝓕 (Wt τ) ξ‖ ≤ CF K * (1 + |τ|) ^ K := by
  have h1 : (2 * π * |ξ|) ^ K * ‖𝓕 (Wt τ) ξ‖ = ‖𝓕 (F τ K) ξ‖ := by
    rw [fourier_F, norm_mul, norm_pow]
    congr 1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Complex.norm_two,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [h1]
  have h2 : ‖𝓕 (F τ K) ξ‖ ≤ ∫ u, ‖F τ K u‖ := VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  refine h2.trans ?_
  have hint : ∀ j ∈ Finset.range (K + 1), Integrable fun u => |τ| ^ j * |cf K j u| :=
    fun j _ => ((integrable_cf K j).abs).const_mul _
  calc ∫ u, ‖F τ K u‖ ≤ ∫ u, ∑ j ∈ Finset.range (K + 1), |τ| ^ j * |cf K j u| :=
        integral_mono (integrable_F τ K).norm (integrable_finsetSum _ hint) (norm_F_le τ K)
    _ = ∑ j ∈ Finset.range (K + 1), |τ| ^ j * ∫ u, |cf K j u| := by
        rw [integral_finsetSum _ hint]
        exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1), (1 + |τ|) ^ K * ∫ u, |cf K j u| := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have h0 : 0 ≤ ∫ u, |cf K j u| := integral_nonneg fun u => abs_nonneg _
        have h3 : |τ| ^ j ≤ (1 + |τ|) ^ K :=
          (pow_le_pow_left₀ (abs_nonneg τ) (by linarith [abs_nonneg τ]) j).trans
            (pow_le_pow_right₀ (by linarith [abs_nonneg τ]) hj')
        exact mul_le_mul_of_nonneg_right h3 h0
    _ = CF K * (1 + |τ|) ^ K := by rw [← Finset.mul_sum, CF, mul_comm]

end LinnikCGLFourier

#print axioms LinnikCGLFourier.hasDerivAt_F
#print axioms LinnikCGLFourier.fourier_F
#print axioms LinnikCGLFourier.lemma43
