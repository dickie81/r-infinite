/-
# Round 692: their smoothing `f̃_b` in their induction, and `Λ` against `F` (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li prove their Proposition 8.1 from their Lemma 8.2: "We wish to show that for any ϵ > 0 there is a
C(ϵ) > 0 such that" (lines 2521–2522; spaces restored) their (8.1) holds, "via downward induction on ϵ" (line 2543;
spaces restored). For the step they need of `f̃_b(u) = ∫_ℝTψ(T(u − u′))f_b(u′) du′` (lines 2517–2520, transcribed):
"The compact support conditions |u| ≪ 1 for f_b(u) and |x| ≪ 1 for ψ(x) ensure that the modified function f̃_b(u)
maintains the same support restriction |u| ≪ 1. Moreover, the Fourier transform of f̃_b also satisfies the desired
decay." (lines 2566–2568; spaces restored, the subscripts and the tildes transcribed), and "Since f̃_b is a smoothed
version of f_b, we have the L¹ and L² norm comparisons:" (line 2590; likewise, the exponents transcribed)
`∫f̃_b ≪ ∫f_b` and `∫f̃_b² ≪ ∫f_b²` (lines 2590–2595, transcribed). This file proves those four properties for round
685's `ftil`, and bounds `Λ = φ(q)f_{b₀}(u₀)` against `F = Σ_b∫f_b`, the hypothesis of round 691's `lemma82_form`.

The stack's form.
* `f̃_b = k_T ⋆ f_b` with `k_T(t) = Tψ̃₀(Tt)` (round 656's `psi0`), smooth, `0` off `[−2/T, 2/T]`, with `∫k_T = ∫ψ̃₀`.
* The support: for `T ≥ 1`, `f̃_b` is `0` for `|u| > |A| + 2` (round 686's `ftil_eq_zero`).
* The decay: `𝓕f̃_b = 𝓕k_T·f̂_b` (Mathlib's `Real.fourier_mul_convolution_eq`) and `|𝓕k_T| ≤ ∫k_T`, so `f̃` keeps
  the premise with `(∫ψ̃₀)D` in place of `D` and the same `Λ`.
* `L¹`: `∫f̃_b = (∫ψ̃₀)∫f_b` (Mathlib's `integral_convolution`). `L²`: `f̃_b(x)² ≤ (∫ψ̃₀)(k_T ⋆ f_b²)(x)` by
  Cauchy–Schwarz against `k_T` (round 643's `integral_sq_le`), and `∫(k_T ⋆ f_b²) = (∫ψ̃₀)∫f_b²`.
* `Λ` against `F`: Fourier inversion gives `f_b(u) ≤ ∫|f̂_b| ≤ 2XF + 2πDT⁴ΛX^{−2}`, from `|f̂_b| ≤ F` on `[−X, X]` and
  the premise at `j = 4` off it. At `Λ = φ(q)f_{b₀}(u₀)` and `X = 4π·max(D, 1)T²φ(q)`, the second term is at most
  `f_{b₀}(u₀)/2`.

Plain statements, with `q ≥ 1` (`[NeZero q]`) where a sum over `b` occurs, `f̂_b` the Fourier transform of `u ↦ f_b(u)`
(round 680's `fC`), `F = Σ_b∫f_b` and "the premise at `j`" the decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for every `ξ ≠ 0`.
* `hasCompactSupport_kT`, `contDiff_kT`, `integrable_kT`, `integral_kT`: for `T > 0`, `k_T` is smooth, `0` off
  `[−2/T, 2/T]` and integrable, with `∫k_T = ∫ψ̃₀`.
* `contDiff_ftil`, `integral_ftil`: for `T > 0` and integrable `f_b`, `f̃_b` is smooth and `∫f̃_b = (∫ψ̃₀)∫f_b`.
* `ftil_vanish`: for `f_b` that are `0` for `|u| > A` and `T ≥ 1`, `f̃_b` is `0` for `|u| > |A| + 2`.
* `fC_ftil_eq`, `norm_fourier_ftil_le`: `f̃_b`, cast to `ℂ`, is the convolution of the casts; and for `T > 0` and
  integrable `f_b`, `|𝓕f̃_b(ξ)| ≤ (∫ψ̃₀)|f̂_b(ξ)|`.
* `decay_ftil`: for `T > 0` and integrable `f_b`, if `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` then
  `Σ_b|𝓕f̃_b(ξ)| ≤ (∫ψ̃₀)D(T/|ξ|)^jΛ`.
* `integral_ftil_sq_le`: for `T > 0` and continuous `f_b ≥ 0` with `f_b²` integrable, `∫f̃_b² ≤ (∫ψ̃₀)²∫f_b²`.
* `norm_le_integral_norm_fourier`: for continuous integrable `g : ℝ → ℂ` with `ĝ` integrable, `|g(u)| ≤ ∫|ĝ|`.
* `f_le_of_decay`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `D, Λ ≥ 0`, `X ≥ 1` and the premise at `j = 4`,
  `f_b(u) ≤ 2XF + 2πDT⁴ΛX^{−2}` for every `b` and `u`.
* `Lam_le`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, a point `(b₀, u₀)` and the premise at `j = 4`
  with `Λ = φ(q)f_{b₀}(u₀)`, `φ(q)f_{b₀}(u₀) ≤ 16π·max(D, 1)(qT)²F`.

The file imports `LinnikCGLForm.lean`.
-/

import LinnikCGLForm

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate Convolution

noncomputable section

namespace LinnikCGLFtilP

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLJ LinnikCGLG LinnikCGLFtil LinnikCGLJtil LinnikCGLFrob
  LinnikCGLPhi LinnikCGLCov

/-! ### The kernel `k_T(t) = Tψ̃₀(Tt)` -/

/-- For `T > 0`, `t ↦ Tψ̃₀(Tt)` vanishes off `[−2/T, 2/T]`. -/
lemma hasCompactSupport_kT {T : ℝ} (hT : 0 < T) : HasCompactSupport (fun t : ℝ => T * psi0 (T * t)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 / T)) (b := 2 / T)) fun t ht => ?_
  have h2 : 2 ≤ |T * t| := by
    rw [abs_mul, abs_of_pos hT]
    by_contra hc
    push Not at hc
    exact ht (abs_le.mp ((lt_div_iff₀' hT).mpr hc).le)
  rw [psi0_eq_zero h2, mul_zero]

/-- `t ↦ Tψ̃₀(Tt)` is smooth. -/
lemma contDiff_kT (T : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => T * psi0 (T * t)) :=
  contDiff_const.mul (contDiff_psi0.comp (contDiff_const.mul contDiff_id))

/-- For `T > 0`, `t ↦ Tψ̃₀(Tt)` is integrable. -/
lemma integrable_kT {T : ℝ} (hT : 0 < T) : Integrable (fun t : ℝ => T * psi0 (T * t)) :=
  (contDiff_kT T).continuous.integrable_of_hasCompactSupport (hasCompactSupport_kT hT)

/-- For `T > 0`, `∫Tψ̃₀(Tt) dt = ∫ψ̃₀`. -/
lemma integral_kT {T : ℝ} (hT : 0 < T) : ∫ t, T * psi0 (T * t) = ∫ t, psi0 t := by
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun t => psi0 t) T, abs_of_pos (inv_pos.2 hT),
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]

/-! ### `f̃_b` -/

/-- For `T > 0` and integrable `f_b`, `f̃_b` is smooth. -/
lemma contDiff_ftil {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 < T) (b : (ZMod q)ˣ)
    (hfi : Integrable (f b)) : ContDiff ℝ ∞ (ftil f T b) :=
  (hasCompactSupport_kT hT).contDiff_convolution_left (L := ContinuousLinearMap.mul ℝ ℝ) (contDiff_kT T)
    hfi.locallyIntegrable

/-- For `f_b` that are `0` for `|u| > A` and `T ≥ 1`, `f̃_b` is `0` for `|u| > |A| + 2`. -/
lemma ftil_vanish {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {T : ℝ}
    (hT : 1 ≤ T) (b : (ZMod q)ˣ) (u : ℝ) (hu : |A| + 2 < |u|) : ftil f T b u = 0 := by
  have hT0 : 0 < T := by linarith
  refine ftil_eq_zero hA hT0 b (lt_of_le_of_lt ?_ hu)
  have : 2 / T ≤ 2 := by rw [div_le_iff₀ hT0]; linarith
  linarith

/-- For `T > 0` and integrable `f_b`, `∫f̃_b = (∫ψ̃₀)∫f_b`. -/
lemma integral_ftil {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 < T) (b : (ZMod q)ˣ)
    (hfi : Integrable (f b)) : ∫ u, ftil f T b u = (∫ t, psi0 t) * ∫ u, f b u := by
  unfold ftil
  rw [integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (integrable_kT hT) hfi, integral_kT hT]
  rfl

/-- `f̃_b`, cast to `ℂ`, is the convolution of the casts. -/
lemma fC_ftil_eq {q : ℕ} (f : (ZMod q)ˣ → ℝ → ℝ) (T : ℝ) (b : (ZMod q)ˣ) :
    fC (ftil f T) b =
      (fun t : ℝ => ((T * psi0 (T * t) : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] fC f b := by
  ext x
  rw [convolution_def]
  simp only [fC, ftil_apply, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  congr 1
  ext t
  push_cast
  ring

/-- **The convolution theorem for `f̃_b`**: for `T > 0` and integrable `f_b`, `|𝓕f̃_b(ξ)| ≤ (∫ψ̃₀)|f̂_b(ξ)|`. -/
lemma norm_fourier_ftil_le {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 < T) (b : (ZMod q)ˣ)
    (hfi : Integrable (f b)) (ξ : ℝ) : ‖𝓕 (fC (ftil f T) b) ξ‖ ≤ (∫ t, psi0 t) * ‖𝓕 (fC f b) ξ‖ := by
  have hk : Integrable (fun t : ℝ => ((T * psi0 (T * t) : ℝ) : ℂ)) := (integrable_kT hT).ofReal
  have hfC : Integrable (fC f b) := hfi.ofReal
  rw [fC_ftil_eq, Real.fourier_mul_convolution_eq hk hfC ξ, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖𝓕 (fun t : ℝ => ((T * psi0 (T * t) : ℝ) : ℂ)) ξ‖ ≤ ∫ t, ‖((T * psi0 (T * t) : ℝ) : ℂ)‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ = ∫ t, T * psi0 (T * t) := by
        congr 1
        ext t
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hT.le (psi0_nonneg _))]
    _ = ∫ t, psi0 t := integral_kT hT

/-- **The decay premise for `f̃`**: for `q ≥ 1`, `T > 0` and integrable `f_b`, if `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` then
`Σ_b|𝓕f̃_b(ξ)| ≤ (∫ψ̃₀)D(T/|ξ|)^jΛ`. -/
lemma decay_ftil {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hfi : ∀ b, Integrable (f b))
    {D Λ ξ : ℝ} {j : ℕ} (h : ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ j * Λ) :
    ∑ b, ‖𝓕 (fC (ftil f T) b) ξ‖ ≤ (∫ t, psi0 t) * D * (T / |ξ|) ^ j * Λ := by
  calc ∑ b, ‖𝓕 (fC (ftil f T) b) ξ‖ ≤ ∑ b, (∫ t, psi0 t) * ‖𝓕 (fC f b) ξ‖ :=
        Finset.sum_le_sum fun b _ => norm_fourier_ftil_le hT b (hfi b) ξ
    _ = (∫ t, psi0 t) * ∑ b, ‖𝓕 (fC f b) ξ‖ := by rw [Finset.mul_sum]
    _ ≤ (∫ t, psi0 t) * (D * (T / |ξ|) ^ j * Λ) := mul_le_mul_of_nonneg_left h (integral_nonneg psi0_nonneg)
    _ = (∫ t, psi0 t) * D * (T / |ξ|) ^ j * Λ := by ring

/-- **`L²` against `f̃_b`**: for `T > 0` and continuous `f_b ≥ 0` with `f_b²` integrable,
`∫f̃_b² ≤ (∫ψ̃₀)²∫f_b²`. -/
lemma integral_ftil_sq_le {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : ∀ b u, 0 ≤ f b u)
    (b : (ZMod q)ˣ) (hfc : Continuous (f b)) (hfi2 : Integrable fun u => f b u ^ 2) :
    ∫ u, ftil f T b u ^ 2 ≤ (∫ t, psi0 t) ^ 2 * ∫ u, f b u ^ 2 := by
  set k : ℝ → ℝ := fun t => T * psi0 (T * t) with hk
  have hk0 : ∀ t, 0 ≤ k t := fun t => mul_nonneg hT.le (psi0_nonneg _)
  have hki : Integrable k := integrable_kT hT
  have hkc : Continuous k := (contDiff_kT T).continuous
  have hks : HasCompactSupport k := hasCompactSupport_kT hT
  -- pointwise, by Cauchy–Schwarz against `k`: `f̃_b(x)² ≤ (∫ψ̃₀)·(k ⋆ f_b²)(x)`
  have hpt : ∀ x, ftil f T b x ^ 2 ≤ (∫ t, psi0 t) * ∫ t, k t * f b (x - t) ^ 2 := by
    intro x
    have hc1 : Continuous fun t => f b (x - t) := hfc.comp (continuous_const.sub continuous_id)
    have i2 : Integrable fun t => k t * f b (x - t) :=
      (hkc.mul hc1).integrable_of_hasCompactSupport (hks.mul_right)
    have i3 : Integrable fun t => k t * f b (x - t) ^ 2 :=
      (hkc.mul (hc1.pow 2)).integrable_of_hasCompactSupport (hks.mul_right)
    have h := integral_sq_le hk0 (fun t => hf b (x - t)) hki i2 i3
    rw [ftil_apply, ← integral_kT hT]
    exact h
  -- integrated: `∫(k ⋆ f_b²) = (∫k)(∫f_b²)`
  have hconv : ∫ x, (∫ t, k t * f b (x - t) ^ 2) = (∫ t, k t) * ∫ u, f b u ^ 2 := by
    have h := integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hki hfi2
    simpa [convolution_def] using h
  have hint : Integrable fun x => (∫ t, psi0 t) * ∫ t, k t * f b (x - t) ^ 2 := by
    have h := hki.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hfi2
    refine (h.const_mul (∫ t, psi0 t)).congr (Eventually.of_forall fun x => ?_)
    simp [convolution_def]
  calc ∫ u, ftil f T b u ^ 2 ≤ ∫ x, (∫ t, psi0 t) * ∫ t, k t * f b (x - t) ^ 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _) hint (Eventually.of_forall hpt)
    _ = (∫ t, psi0 t) * ((∫ t, k t) * ∫ u, f b u ^ 2) := by rw [integral_const_mul, hconv]
    _ = (∫ t, psi0 t) ^ 2 * ∫ u, f b u ^ 2 := by rw [hk, integral_kT hT]; ring

/-! ### `Λ` against `F`, by Fourier inversion -/

/-- **Fourier inversion, as a bound**: for continuous integrable `g : ℝ → ℂ` with `ĝ` integrable,
`|g(u)| ≤ ∫|ĝ|`. -/
lemma norm_le_integral_norm_fourier {g : ℝ → ℂ} (hc : Continuous g) (hi : Integrable g) (hfi : Integrable (𝓕 g))
    (u : ℝ) : ‖g u‖ ≤ ∫ ξ, ‖𝓕 g ξ‖ := by
  have h := congrFun (hc.fourierInv_fourier_eq hi hfi) u
  rw [← h, Real.fourierInv_eq_fourier_neg]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- **A pointwise bound from the decay**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `D, Λ ≥ 0`,
`X ≥ 1` and `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)⁴Λ` for every `ξ ≠ 0`, `f_b(u) ≤ 2XF + 2πDT⁴ΛX^{−2}` for every `b` and `u`,
with `F = Σ_b∫f_b`. -/
lemma f_le_of_decay {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    (hf : ∀ b u, 0 ≤ f b u) {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {T D Λ X : ℝ} (hD : 0 ≤ D)
    (hΛ : 0 ≤ Λ) (hX : 1 ≤ X) (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ 4 * Λ)
    (b : (ZMod q)ˣ) (u : ℝ) :
    f b u ≤ 2 * X * (∑ b, ∫ u, f b u) + 2 * π * D * T ^ 4 * Λ * (X ^ 2)⁻¹ := by
  set F : ℝ := ∑ b, ∫ u, f b u with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun b _ => integral_nonneg (hf b)
  set C : ℝ := D * T ^ 4 * Λ with hC
  have hC0 : 0 ≤ C := by positivity
  have hnorm : ∀ v, ‖fC f b v‖ = f b v := fun v => by
    rw [fC, Complex.norm_real, Real.norm_of_nonneg (hf b v)]
  -- `|f̂_b| ≤ F` everywhere and `≤ C|ξ|^{−4}` for `ξ ≠ 0`
  have hF1 : ∀ ξ, ‖𝓕 (fC f b) ξ‖ ≤ F := by
    intro ξ
    calc ‖𝓕 (fC f b) ξ‖ ≤ ∫ v, ‖fC f b v‖ := VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      _ = ∫ v, f b v := by simp_rw [hnorm]
      _ ≤ F := Finset.single_le_sum (f := fun b => ∫ v, f b v) (fun b _ => integral_nonneg (hf b))
          (Finset.mem_univ b)
  have hF2 : ∀ ξ, ξ ≠ 0 → ‖𝓕 (fC f b) ξ‖ ≤ C * (|ξ| ^ 4)⁻¹ := by
    intro ξ hξ
    have h1 := le_trans (Finset.single_le_sum (fun b _ => norm_nonneg (𝓕 (fC f b) ξ)) (Finset.mem_univ b))
      (hdec ξ hξ)
    calc ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ 4 * Λ := h1
      _ = C * (|ξ| ^ 4)⁻¹ := by rw [hC, div_pow]; ring
  -- `|f̂_b(ξ)| ≤ 2(F + C)(1 + ξ²)⁻¹`, so `f̂_b` is integrable
  have hmaj : ∀ ξ, ‖𝓕 (fC f b) ξ‖ ≤ 2 * (F + C) * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    by_cases h1 : |ξ| ≤ 1
    · have hs : ξ ^ 2 ≤ 1 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
      have : 1 ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
      calc ‖𝓕 (fC f b) ξ‖ ≤ F := hF1 ξ
        _ ≤ F * (2 * (1 + ξ ^ 2)⁻¹) := le_mul_of_one_le_right hF0 this
        _ ≤ 2 * (F + C) * (1 + ξ ^ 2)⁻¹ := by
            have : 0 ≤ C * (2 * (1 + ξ ^ 2)⁻¹) := by positivity
            nlinarith
    · push Not at h1
      have hξ0 : ξ ≠ 0 := by intro h; rw [h, abs_zero] at h1; linarith
      have hs : 1 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
      have h4 : (|ξ| ^ 4)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
        have e : |ξ| ^ 4 = (ξ ^ 2) ^ 2 := by rw [← sq_abs ξ]; ring
        rw [e]
        calc ((ξ ^ 2) ^ 2)⁻¹ ≤ ((1 + ξ ^ 2) / 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
          _ = 2 * (1 + ξ ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
      calc ‖𝓕 (fC f b) ξ‖ ≤ C * (|ξ| ^ 4)⁻¹ := hF2 ξ hξ0
        _ ≤ C * (2 * (1 + ξ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h4 hC0
        _ ≤ 2 * (F + C) * (1 + ξ ^ 2)⁻¹ := by
            have : 0 ≤ F * (2 * (1 + ξ ^ 2)⁻¹) := by positivity
            nlinarith
  have hfi : Integrable (𝓕 (fC f b)) :=
    (integrable_inv_one_add_sq.const_mul (2 * (F + C))).mono' (continuous_fourier_fC hfs hA b).aestronglyMeasurable
      (Eventually.of_forall hmaj)
  -- Fourier inversion
  have hcont : Continuous (fC f b) := Complex.continuous_ofReal.comp (hfs b).continuous
  have hinv := norm_le_integral_norm_fourier hcont (integrable_fC hfs hA b) hfi u
  rw [hnorm] at hinv
  -- the split at `|ξ| = X`
  have hsplit := integral_add_compl (measurableSet_Icc (a := -X) (b := X)) hfi.norm
  have hin : ∫ ξ in Icc (-X) X, ‖𝓕 (fC f b) ξ‖ ≤ 2 * X * F := by
    calc ∫ ξ in Icc (-X) X, ‖𝓕 (fC f b) ξ‖ ≤ ∫ _ξ in Icc (-X) X, F :=
          setIntegral_mono_on hfi.norm.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
            fun ξ _ => hF1 ξ
      _ = 2 * X * F := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]; ring
  have hout : ∫ ξ in (Icc (-X) X)ᶜ, ‖𝓕 (fC f b) ξ‖ ≤ 2 * π * C * (X ^ 2)⁻¹ := by
    have hpt : ∀ ξ ∈ (Icc (-X) X)ᶜ, ‖𝓕 (fC f b) ξ‖ ≤ 2 * C * (X ^ 2)⁻¹ * (1 + ξ ^ 2)⁻¹ := by
      intro ξ hξ
      have hXξ : X < |ξ| := by
        by_contra h
        exact hξ (abs_le.mp (not_lt.mp h))
      have hξ0 : ξ ≠ 0 := by intro h; rw [h, abs_zero] at hXξ; linarith
      have hs : 1 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
      have hkey : (|ξ| ^ 4)⁻¹ ≤ (X ^ 2)⁻¹ * (2 * (1 + ξ ^ 2)⁻¹) := by
        have e : (|ξ| ^ 4)⁻¹ = (|ξ| ^ 2)⁻¹ * (ξ ^ 2)⁻¹ := by
          rw [← sq_abs ξ, ← mul_inv, ← pow_add]
        rw [e]
        refine mul_le_mul (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hXξ.le _)) ?_
          (by positivity) (by positivity)
        calc (ξ ^ 2)⁻¹ ≤ ((1 + ξ ^ 2) / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
          _ = 2 * (1 + ξ ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
      calc ‖𝓕 (fC f b) ξ‖ ≤ C * (|ξ| ^ 4)⁻¹ := hF2 ξ hξ0
        _ ≤ C * ((X ^ 2)⁻¹ * (2 * (1 + ξ ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left hkey hC0
        _ = 2 * C * (X ^ 2)⁻¹ * (1 + ξ ^ 2)⁻¹ := by ring
    have hm : Integrable fun ξ : ℝ => 2 * C * (X ^ 2)⁻¹ * (1 + ξ ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul _
    calc ∫ ξ in (Icc (-X) X)ᶜ, ‖𝓕 (fC f b) ξ‖ ≤ ∫ ξ in (Icc (-X) X)ᶜ, 2 * C * (X ^ 2)⁻¹ * (1 + ξ ^ 2)⁻¹ :=
          setIntegral_mono_on hfi.norm.integrableOn hm.integrableOn measurableSet_Icc.compl hpt
      _ ≤ ∫ ξ, 2 * C * (X ^ 2)⁻¹ * (1 + ξ ^ 2)⁻¹ :=
          setIntegral_le_integral hm (Eventually.of_forall fun ξ => by positivity)
      _ = 2 * π * C * (X ^ 2)⁻¹ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring
  calc f b u ≤ ∫ ξ, ‖𝓕 (fC f b) ξ‖ := hinv
    _ = (∫ ξ in Icc (-X) X, ‖𝓕 (fC f b) ξ‖) + ∫ ξ in (Icc (-X) X)ᶜ, ‖𝓕 (fC f b) ξ‖ := hsplit.symm
    _ ≤ 2 * X * F + 2 * π * C * (X ^ 2)⁻¹ := add_le_add hin hout
    _ = 2 * X * F + 2 * π * D * T ^ 4 * Λ * (X ^ 2)⁻¹ := by rw [hC]; ring

/-- **`Λ` against `F`**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `T ≥ 1`, a point `(b₀, u₀)` and the
decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)⁴φ(q)f_{b₀}(u₀)` for every `ξ ≠ 0`, `φ(q)f_{b₀}(u₀) ≤ 16π·max(D, 1)(qT)²F`, with
`F = Σ_b∫f_b`. -/
lemma Lam_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    (hf : ∀ b u, 0 ≤ f b u) {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {T D : ℝ} (hT : 1 ≤ T)
    (b₀ : (ZMod q)ˣ) (u₀ : ℝ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ 4 * ((q.totient : ℝ) * f b₀ u₀)) :
    (q.totient : ℝ) * f b₀ u₀ ≤ 16 * π * max D 1 * ((q : ℝ) * T) ^ 2 * ∑ b, ∫ u, f b u := by
  set D' : ℝ := max D 1 with hD'
  have hD'1 : 1 ≤ D' := le_max_right _ _
  set φ : ℝ := ((q.totient : ℕ) : ℝ) with hφ
  have hφ1 : 1 ≤ φ := by
    rw [hφ]; exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφq : φ ≤ q := by rw [hφ]; exact_mod_cast Nat.totient_le q
  set y : ℝ := f b₀ u₀ with hy
  have hy0 : 0 ≤ y := hf b₀ u₀
  set F : ℝ := ∑ b, ∫ u, f b u with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun b _ => integral_nonneg (hf b)
  have hT0 : 0 < T := by linarith
  have hdec' : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D' * (T / |ξ|) ^ 4 * (φ * y) := fun ξ hξ =>
    (hdec ξ hξ).trans (by gcongr; exact le_max_left _ _)
  set X : ℝ := 4 * π * D' * T ^ 2 * φ with hX
  have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
  have hX1 : 1 ≤ X := by
    rw [hX]
    have h1 : (1 : ℝ) ≤ 4 * π := by nlinarith [Real.pi_gt_three]
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ 4 * π * D' * T ^ 2 * φ := by gcongr
  have h := f_le_of_decay hfs hf hA (by linarith) (by positivity) hX1 hdec' b₀ u₀
  rw [← hy, ← hF] at h
  -- the coefficient of `y` is at most `1/2`
  have hcoef : 2 * π * D' * T ^ 4 * (φ * y) * (X ^ 2)⁻¹ ≤ y / 2 := by
    have hXp : 0 < X := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have e : X ^ 2 = 16 * π ^ 2 * D' ^ 2 * T ^ 4 * φ ^ 2 := by rw [hX]; ring
    rw [e]
    have hπ : 0 < π := Real.pi_pos
    have h8 : 2 ≤ 8 * π * D' * φ := by
      have : (2 : ℝ) ≤ 8 * π := by nlinarith [Real.pi_gt_three]
      calc (2 : ℝ) = 2 * 1 * 1 := by ring
        _ ≤ 8 * π * D' * φ := by gcongr
    have e2 : y / 2 * (16 * π ^ 2 * D' ^ 2 * T ^ 4 * φ ^ 2) =
        (2 * π * D' * T ^ 4 * (φ * y)) * (8 * π * D' * φ) / 2 := by ring
    rw [e2]
    have h0 : 0 ≤ 2 * π * D' * T ^ 4 * (φ * y) := by positivity
    nlinarith
  have hy4 : y ≤ 4 * X * F := by linarith
  calc φ * y ≤ φ * (4 * X * F) := mul_le_mul_of_nonneg_left hy4 (by linarith)
    _ = 16 * π * D' * T ^ 2 * (φ * φ) * F := by rw [hX]; ring
    _ ≤ 16 * π * D' * T ^ 2 * ((q : ℝ) * q) * F := by gcongr
    _ = 16 * π * D' * ((q : ℝ) * T) ^ 2 * F := by ring

end LinnikCGLFtilP

#print axioms LinnikCGLFtilP.contDiff_ftil
#print axioms LinnikCGLFtilP.integral_ftil
#print axioms LinnikCGLFtilP.decay_ftil
#print axioms LinnikCGLFtilP.integral_ftil_sq_le
#print axioms LinnikCGLFtilP.Lam_le
