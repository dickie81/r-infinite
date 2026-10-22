/-
# Round 668: local averages of finite exponential sums, toward their Lemmas 10.4 and 10.8 (the CGL plan's stage M3, the
`S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their §10 twice bounds a finite exponential sum at a point by its average near the point. Lemma 10.4, from
Guth–Maynard: "|D_N(t,χ)| ⪅ ∫_{|u−t|⪅1} |D_N(u,χ)| du + O((qT)^{−100})." (text layer lines 4680–4683; spaces restored;
the integral, subscripts and exponent transcribed). Lemma 10.8: "|R(v,a)| ≪_{ϵ,C} T ∫_{|v′−v|≤T^ϵ/T} |R(v′,a)| dv′ +
O(T^{−100})." (lines 5012–5015; spaces normalized; the integral, subscripts and exponents transcribed), proved with "a
smooth bump which is 1 on [−1,1]" and "by the Fourier inversion formula" (lines 5016–5017; spaces restored).

This file proves the common form without a window. For `F(x) = Σ_{k∈s}c_ke^{iλ_kx}` with every `|λ_k − Λ| ≤ H` and
`k = ψ̂₀` the Fourier transform of round 656's bump `ψ̃₀` (`kloc`), Fourier inversion gives
`∫k(ξ)e^{2πiξμ} dξ = ψ̃₀(μ) = 1` for `|μ| ≤ 1`, and so `F(x) = ∫k(ξ)e^{−2πiξΛ/H}F(x + 2πξ/H) dξ`. Hence
`|F(x)| ≤ ∫|k(ξ)||F(x + 2πξ/H)| dξ`, and, since `|F|² = F·F̄` and `|F|³ = |F·F·F̄|` are again finite exponential
sums, with frequencies in `[−2H, 2H]` and `[Λ − 3H, Λ + 3H]`, `|F(x)|² ≤ ∫|k(ξ)||F(x + πξ/H)|² dξ` and
`|F(x)|³ ≤ ∫|k(ξ)||F(x + 2πξ/(3H))|³ dξ`. The weight `|k|` is integrable and does not depend on `F`; the windows of
their two lemmas come from its decay, `(2π|ξ|)^j|k(ξ)| ≤ D_j` (round 659's `fourier_psiC_decay`).

Plain statements, with `F = esum s c λ`.
* `integrable_kloc`, `kloc_inv`, `kloc_inv_one`: `k` is integrable, `∫e^{2πiξμ}k(ξ) dξ = ψ̃₀(μ)`, and this is `1` for
  `|μ| ≤ 1`.
* `esum_eq_integral`, `norm_esum_le_integral`: for `H > 0` and every `|λ_k − Λ| ≤ H`,
  `F(x) = ∫k(ξ)e^{−2πiξΛ/H}F(x + 2πξ/H) dξ` and `|F(x)| ≤ ∫|k(ξ)||F(x + 2πξ/H)| dξ`.
* `norm_sq_esum_le`, `norm_cube_esum_le`: under the same hypotheses, `|F(x)|² ≤ ∫|k(ξ)||F(x + πξ/H)|² dξ` and
  `|F(x)|³ ≤ ∫|k(ξ)||F(x + 2πξ/(3H))|³ dξ`.

* `integrable_psiC`, `kloc`, `continuous_kloc`, `integrable_kloc`, `kloc_inv`, `kloc_inv_one`: the kernel.
* `esum`, `continuous_esum`, `norm_esum_le`, `esum_mul`, `conj_esum`: finite exponential sums.
* `esum_eq_integral`, `integrable_loc`, `norm_esum_le_integral`, `norm_sq_esum_le`, `norm_cube_esum_le`: the local
  averages.

The file imports `LinnikCGL112.lean`.
-/

import LinnikCGL112

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLLoc

open LinnikCGLRt LinnikCGLMom4

/-! ### The kernel `k = ψ̂₀` -/

lemma integrable_psiC : Integrable psiC :=
  contDiff_psiC.continuous.integrable_of_hasCompactSupport hasCompactSupport_psiC

/-- The kernel `k = 𝓕ψ̃₀`. -/
def kloc (ξ : ℝ) : ℂ := 𝓕 psiC ξ

lemma continuous_kloc : Continuous kloc :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ integrable_psiC

/-- `k` is integrable: `(1 + ξ²)|k(ξ)| ≤ ∫ψ̃₀ + D₂/(4π²)`. -/
lemma integrable_kloc : Integrable kloc := by
  set N₀ := ∫ x, psi0 x with hN₀
  set N₂ := Dpsi 2 with hN₂
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (N₀ + N₂ / (4 * π ^ 2)))
    continuous_kloc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have h0 : ‖kloc ξ‖ ≤ N₀ := norm_fourier_psiC_le ξ
  have h2 : (2 * π * |ξ|) ^ 2 * ‖kloc ξ‖ ≤ N₂ := fourier_psiC_decay 2 ξ
  have hsq : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * ξ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hsq] at h2
  have hF := norm_nonneg (kloc ξ)
  have hpi : 0 < 4 * π ^ 2 := by positivity
  have h2' : ξ ^ 2 * ‖kloc ξ‖ ≤ N₂ / (4 * π ^ 2) := by rw [le_div_iff₀ hpi]; nlinarith
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith

/-- **Fourier inversion for `ψ̃₀`**: `∫e^{2πiξμ}k(ξ) dξ = ψ̃₀(μ)`. -/
lemma kloc_inv (μ : ℝ) : ∫ ξ, cexp (↑(2 * π * ξ * μ) * I) * kloc ξ = psiC μ := by
  have hinv := Continuous.fourierInv_fourier_eq contDiff_psiC.continuous integrable_psiC integrable_kloc
  rw [← congrFun hinv μ, Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, kloc, RCLike.inner_apply, conj_trivial]
  congr 3
  push_cast
  ring

lemma kloc_inv_one {μ : ℝ} (hμ : |μ| ≤ 1) : ∫ ξ, cexp (↑(2 * π * ξ * μ) * I) * kloc ξ = 1 := by
  rw [kloc_inv, psiC, psi0_eq_one hμ, Complex.ofReal_one]

/-! ### Finite exponential sums -/

/-- A finite exponential sum `F(x) = Σ_{k∈s}c_ke^{iλ_kx}`. -/
def esum {κ : Type*} (s : Finset κ) (c : κ → ℂ) (lam : κ → ℝ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, c k * cexp (↑(lam k * x) * I)

section esum

variable {κ : Type*} (s : Finset κ) (c : κ → ℂ) (lam : κ → ℝ)

lemma continuous_esum : Continuous (esum s c lam) := by
  unfold esum
  fun_prop

lemma norm_esum_le (x : ℝ) : ‖esum s c lam x‖ ≤ ∑ k ∈ s, ‖c k‖ := by
  unfold esum
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The product of two exponential sums is the exponential sum over the pairs. -/
lemma esum_mul {κ' : Type*} (s' : Finset κ') (c' : κ' → ℂ) (lam' : κ' → ℝ) (x : ℝ) :
    esum s c lam x * esum s' c' lam' x =
      esum (s ×ˢ s') (fun p => c p.1 * c' p.2) (fun p => lam p.1 + lam' p.2) x := by
  unfold esum
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have e : cexp (↑(lam k * x) * I) * cexp (↑(lam' l * x) * I) = cexp (↑((lam k + lam' l) * x) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc c k * cexp (↑(lam k * x) * I) * (c' l * cexp (↑(lam' l * x) * I))
      = c k * c' l * (cexp (↑(lam k * x) * I) * cexp (↑(lam' l * x) * I)) := by ring
    _ = c k * c' l * cexp (↑((lam k + lam' l) * x) * I) := by rw [e]

/-- The conjugate of an exponential sum. -/
lemma conj_esum (x : ℝ) : conj (esum s c lam x) = esum s (fun k => conj (c k)) (fun k => -lam k) x := by
  unfold esum
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

end esum

/-! ### Local averages -/

section loc

variable {κ : Type*} (s : Finset κ) (c : κ → ℂ) (lam : κ → ℝ)

/-- The integrand of the local average is integrable. -/
lemma integrable_loc (H x : ℝ) : Integrable fun ξ => ‖kloc ξ‖ * ‖esum s c lam (x + 2 * π * ξ / H)‖ := by
  refine (integrable_kloc.norm.mul_const (∑ k ∈ s, ‖c k‖)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (continuous_kloc.norm.mul ((continuous_esum s c lam).comp (by fun_prop)).norm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_esum_le s c lam _) (norm_nonneg _)

/-- **The local average, as an identity**: for `H > 0` and every `|λ_k − Λ| ≤ H`,
`F(x) = ∫k(ξ)e^{−2πiξΛ/H}F(x + 2πξ/H) dξ`. -/
theorem esum_eq_integral {Λ H : ℝ} (hH : 0 < H) (hlam : ∀ k ∈ s, |lam k - Λ| ≤ H) (x : ℝ) :
    esum s c lam x =
      ∫ ξ, kloc ξ * cexp (↑(-(2 * π * ξ * Λ / H)) * I) * esum s c lam (x + 2 * π * ξ / H) := by
  have hint : ∀ k ∈ s, Integrable fun ξ =>
      kloc ξ * cexp (↑(-(2 * π * ξ * Λ / H)) * I) * (c k * cexp (↑(lam k * (x + 2 * π * ξ / H)) * I)) := by
    intro k _
    refine (integrable_kloc.norm.mul_const ‖c k‖).mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · have h1 : Continuous fun ξ : ℝ => cexp (↑(-(2 * π * ξ * Λ / H)) * I) := by fun_prop
      have h2 : Continuous fun ξ : ℝ => cexp (↑(lam k * (x + 2 * π * ξ / H)) * I) := by fun_prop
      exact ((continuous_kloc.mul h1).mul (continuous_const.mul h2)).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one,
        mul_one]
  have e1 : ∀ ξ, kloc ξ * cexp (↑(-(2 * π * ξ * Λ / H)) * I) * esum s c lam (x + 2 * π * ξ / H) =
      ∑ k ∈ s, kloc ξ * cexp (↑(-(2 * π * ξ * Λ / H)) * I) *
        (c k * cexp (↑(lam k * (x + 2 * π * ξ / H)) * I)) := fun ξ => by
    unfold esum
    rw [Finset.mul_sum]
  simp_rw [e1]
  rw [integral_finsetSum _ hint]
  unfold esum
  refine Finset.sum_congr rfl fun k hk => ?_
  have hμ : |(lam k - Λ) / H| ≤ 1 := by
    rw [abs_div, abs_of_pos hH, div_le_one hH]
    exact hlam k hk
  have h1 := kloc_inv_one hμ
  have e2 : ∀ ξ : ℝ, c k * cexp (↑(lam k * x) * I) * (cexp (↑(2 * π * ξ * ((lam k - Λ) / H)) * I) * kloc ξ) =
      kloc ξ * cexp (↑(-(2 * π * ξ * Λ / H)) * I) * (c k * cexp (↑(lam k * (x + 2 * π * ξ / H)) * I)) := by
    intro ξ
    have e : cexp (↑(lam k * x) * I) * cexp (↑(2 * π * ξ * ((lam k - Λ) / H)) * I) =
        cexp (↑(-(2 * π * ξ * Λ / H)) * I) * cexp (↑(lam k * (x + 2 * π * ξ / H)) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc c k * cexp (↑(lam k * x) * I) * (cexp (↑(2 * π * ξ * ((lam k - Λ) / H)) * I) * kloc ξ)
        = c k * (cexp (↑(lam k * x) * I) * cexp (↑(2 * π * ξ * ((lam k - Λ) / H)) * I)) * kloc ξ := by ring
      _ = c k * (cexp (↑(-(2 * π * ξ * Λ / H)) * I) * cexp (↑(lam k * (x + 2 * π * ξ / H)) * I)) * kloc ξ := by
          rw [e]
      _ = kloc ξ * cexp (↑(-(2 * π * ξ * Λ / H)) * I) * (c k * cexp (↑(lam k * (x + 2 * π * ξ / H)) * I)) := by
          ring
  calc c k * cexp (↑(lam k * x) * I)
      = c k * cexp (↑(lam k * x) * I) * ∫ ξ, cexp (↑(2 * π * ξ * ((lam k - Λ) / H)) * I) * kloc ξ := by
        rw [h1, mul_one]
    _ = ∫ ξ, c k * cexp (↑(lam k * x) * I) * (cexp (↑(2 * π * ξ * ((lam k - Λ) / H)) * I) * kloc ξ) :=
        (integral_const_mul _ _).symm
    _ = _ := integral_congr_ae (Eventually.of_forall e2)

/-- **The local average**: for `H > 0` and every `|λ_k − Λ| ≤ H`, `|F(x)| ≤ ∫|k(ξ)||F(x + 2πξ/H)| dξ`. -/
theorem norm_esum_le_integral {Λ H : ℝ} (hH : 0 < H) (hlam : ∀ k ∈ s, |lam k - Λ| ≤ H) (x : ℝ) :
    ‖esum s c lam x‖ ≤ ∫ ξ, ‖kloc ξ‖ * ‖esum s c lam (x + 2 * π * ξ / H)‖ := by
  rw [esum_eq_integral s c lam hH hlam x]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext ξ
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The local average of `|F|²`**: for `H > 0` and every `|λ_k − Λ| ≤ H`,
`|F(x)|² ≤ ∫|k(ξ)||F(x + πξ/H)|² dξ`, since `F·F̄` has its frequencies in `[−2H, 2H]`. -/
theorem norm_sq_esum_le {Λ H : ℝ} (hH : 0 < H) (hlam : ∀ k ∈ s, |lam k - Λ| ≤ H) (x : ℝ) :
    ‖esum s c lam x‖ ^ 2 ≤ ∫ ξ, ‖kloc ξ‖ * ‖esum s c lam (x + π * ξ / H)‖ ^ 2 := by
  set G := esum (s ×ˢ s) (fun p => c p.1 * conj (c p.2)) (fun p => lam p.1 + -lam p.2) with hG
  have hGx : ∀ y, ‖esum s c lam y‖ ^ 2 = ‖G y‖ := fun y => by
    rw [hG, ← esum_mul s c lam s (fun k => conj (c k)) (fun k => -lam k) y, ← conj_esum, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hlam2 : ∀ p ∈ s ×ˢ s, |(lam p.1 + -lam p.2) - 0| ≤ 2 * H := by
    intro p hp
    rw [Finset.mem_product] at hp
    have h1 := abs_le.mp (hlam p.1 hp.1)
    have h2 := abs_le.mp (hlam p.2 hp.2)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have h := norm_esum_le_integral (s ×ˢ s) (fun p => c p.1 * conj (c p.2)) (fun p => lam p.1 + -lam p.2)
    (by linarith : (0 : ℝ) < 2 * H) hlam2 x
  rw [hGx x]
  refine h.trans (le_of_eq ?_)
  congr 1
  funext ξ
  rw [hGx, show x + 2 * π * ξ / (2 * H) = x + π * ξ / H by field_simp]

/-- **The local average of `|F|³`**: for `H > 0` and every `|λ_k − Λ| ≤ H`,
`|F(x)|³ ≤ ∫|k(ξ)||F(x + 2πξ/(3H))|³ dξ`, since `F·F·F̄` has its frequencies in `[Λ − 3H, Λ + 3H]`. -/
theorem norm_cube_esum_le {Λ H : ℝ} (hH : 0 < H) (hlam : ∀ k ∈ s, |lam k - Λ| ≤ H) (x : ℝ) :
    ‖esum s c lam x‖ ^ 3 ≤ ∫ ξ, ‖kloc ξ‖ * ‖esum s c lam (x + 2 * π * ξ / (3 * H))‖ ^ 3 := by
  set G := esum ((s ×ˢ s) ×ˢ s) (fun p => c p.1.1 * c p.1.2 * conj (c p.2))
    (fun p => lam p.1.1 + lam p.1.2 + -lam p.2) with hG
  have hGx : ∀ y, ‖esum s c lam y‖ ^ 3 = ‖G y‖ := fun y => by
    have e1 := esum_mul s c lam s c lam y
    have e2 := esum_mul (s ×ˢ s) (fun p => c p.1 * c p.2) (fun p => lam p.1 + lam p.2) s
      (fun k => conj (c k)) (fun k => -lam k) y
    rw [hG, ← e2, ← e1, ← conj_esum, norm_mul, norm_mul, Complex.norm_conj]
    ring
  have hlam3 : ∀ p ∈ (s ×ˢ s) ×ˢ s, |(lam p.1.1 + lam p.1.2 + -lam p.2) - Λ| ≤ 3 * H := by
    intro p hp
    simp only [Finset.mem_product] at hp
    have h1 := abs_le.mp (hlam p.1.1 hp.1.1)
    have h2 := abs_le.mp (hlam p.1.2 hp.1.2)
    have h3 := abs_le.mp (hlam p.2 hp.2)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have h := norm_esum_le_integral ((s ×ˢ s) ×ˢ s) (fun p => c p.1.1 * c p.1.2 * conj (c p.2))
    (fun p => lam p.1.1 + lam p.1.2 + -lam p.2) (by linarith : (0 : ℝ) < 3 * H) hlam3 x
  rw [hGx x]
  refine h.trans (le_of_eq ?_)
  congr 1
  funext ξ
  rw [hGx]

end loc

end LinnikCGLLoc

#print axioms LinnikCGLLoc.kloc_inv
#print axioms LinnikCGLLoc.esum_eq_integral
#print axioms LinnikCGLLoc.norm_esum_le_integral
#print axioms LinnikCGLLoc.norm_sq_esum_le
#print axioms LinnikCGLLoc.norm_cube_esum_le
