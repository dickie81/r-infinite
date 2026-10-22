/-
# Round 659: their Lemma 9.2, the fourth moments of `R` and `R̃` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

This file proves Chen–Gupta–Li's Lemma 9.2 at one point per character, with explicit constants.

Their energy. "For a finite set W of pairs (t,χ), we define its energy E(W) as E(W) := #{(t₁,χ₁),(t₂,χ₂),(t₃,χ₃),
(t₄,χ₄) ∈ W : |t₁+t₂−t₃−t₄| ≤ 1, χ₁χ₂ = χ₃χ₄}." (their footnote 5, text layer lines 2487–2488; spaces restored, the
footnote mark dropped, the subscripts transcribed). `energy` is that count over `R⁴`; at one point per character
`i ↦ (t_i, χ_i)` is injective on `R`, so it is their `E(W)` for `W = {(t_i, χ_i) : i ∈ R}`.

Their statement. "Let W be a finite set of pairs (t,χ), where |t| ≤ T and for (t,χ) ≠ (t′,χ′) either χ ≠ χ′ or
|t−t′| ≥ (qT)^ϵ. For any M₂ > 0, we have ∫_{v≍1} Σ_{a mod q, (a,q)=1} |R(v,a)|⁴ dv ⪅ ϕ(q)E(W) and
∫_{v≍1} Σ_{a mod q, (a,q)=1} |R̃_{M₂}(v,a)|⁴ dv ⪅_ϵ ϕ(q)E(W)." (lines 4470–4482; spaces restored, the integrals,
sums and their ranges, the tilde, exponents and subscripts transcribed).

Their proof for `R`. After the change of variables `v = e^τ` (line 4537), "Let ψ(τ) be a smooth bump function supported
on |τ| ≪ 1 such that ψ(τ/(qT)^ϵ) majorizes the range of integration." (lines 4556–4557; spaces restored, the exponent
transcribed), then orthogonality, and "Due to the rapid decay of ψ̂, the summation can be restricted to
|t₁+t₂−t₃−t₄| ≤ 1, incurring an error of O_ϵ((qT)^{−100}). The proof is then completed by observing that the
remaining terms contribute ⪅ ϕ(q)E(W)." (lines 4609–4612; spaces restored, the hat, subscripts and exponents
transcribed).

An observation about their write-up. In the display of lines 4558–4584 the majorized integral carries the Jacobian
`e^τ` (`… |Σ e^{itτ}χ(a)|⁴ e^τ dτ`, line 4571), and the identity that follows, `= Σ … ∫ ψ(τ/(qT)^ϵ)
e^{iτ(t₁+t₂−t₃−t₄)} … dτ`, has no `e^τ`. The PDF agrees: on page 39 pdfminer finds two exponentials in the row at
y = 201 (superscripts `itτ` and `τ` in the row at y = 207) and one in the row at y = 154 (superscript
`iτ(t1+t2−t3−t4)` at y = 159). Kept, `e^τ` grows like `e^{(qT)^ϵ}` on the majorant's support. The repair costs a
factor `2`: bound `e^τ ≤ 2` on the original range `|τ| ≤ log 2` before majorizing, as `lemma92` does.

The stack's form.
* `sum_norm_Rf_four` is exact for any characters: `Σ_{a unit}|R(e^τ, a)|⁴ = φ(q)Σ_{i,j,k,l}[χ_iχ_j = χ_kχ_l]
  e^{iτ(t_i + t_j − t_k − t_l)}`, by orthogonality over the units (round 658's `sum_units_mul_star` for `χ_iχ_j` and
  `χ_kχ_l`).
* The majorant is round 656's bump: `ψ̃₀(τ/X) = 1` for `|τ| ≤ X`, which contains `|τ| ≤ log 2` when `X ≥ 1`;
  `∫_ℝψ̃₀(τ/X)e^{iτΔ} dτ = Xψ̂₀(−XΔ/(2π))` (`integral_psi_exp`). The terms with `|Δ| ≤ 1` are counted by the energy
  with weight `X∫ψ̃₀`, and the others are at most `XD_K/X^K` each, with `D_K = ∫|ψ̃₀^{(K)}|` (round 588's integration
  by parts). With `X` for their `(qT)^ϵ` and `K` large, the second term is their `O_ϵ((qT)^{−100})`.
* For `R̃` the stack does not use their window. Weighted Cauchy–Schwarz gives
  `R̃_{M₂}(v, a)⁴ ≤ (∫k)(∫k|R|⁴)` with `k(u′) = Lψ̃₀(L(v − u′)/(2X))` on `[1/2, 2]` and `∫k ≤ 2X∫ψ̃₀`
  (`Rt_four_le`), and Fubini (`integral_conv`, round 658's argument for any bounded measurable `g`) integrates over
  all `v ∈ ℝ`.

Plain statements, with `q ≥ 1`, `L = NM₂/q` and `E` the energy.
* `lemma92`: for `X ≥ 1` and `K ∈ ℕ`, `∫_{[1/2,2]}Σ_{a unit}|R(v, a)|⁴ dv ≤ 2φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`.
* `integral_conv`: for `L, X > 0` and `g` measurable with `|g| ≤ C` on `[1/2, 2]`,
  `∫_ℝ∫_{[1/2,2]}Lψ̃₀(L(v − u′)/(2X))g(u′) du′ dv = 2X∫ψ̃₀·∫_{[1/2,2]}g`, the inner integral integrable in `v`.
* `Rt_four_le`: `R̃_{M₂}(v, a)⁴ ≤ 2X∫ψ̃₀·∫_{[1/2,2]}Lψ̃₀(L(v − u′)/(2X))|R(u′, a)|⁴ du′` for `L, X > 0`.
* `lemma92_Rt`: for `L > 0`, `X ≥ 1` and `K ∈ ℕ`,
  `∫_ℝΣ_{a unit}R̃_{M₂}(v, a)⁴ dv ≤ (2X∫ψ̃₀)²·2φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`.

* `energy`, `energy_eq_sum`: the energy.
* `Rf_exp`, `conj_exp_I`, `sum_norm_Rf_four`: the fourth power over the units.
* `psiC`, `contDiff_psiC`, `hasCompactSupport_psiC`, `integrable_iteratedDeriv_psiC`, `Dpsi`, `Dpsi_nonneg`,
  `fourier_psiC_decay`, `norm_fourier_psiC_le`, `integral_psi_exp`, `integrable_psi_exp`, `norm_term_le`: the Fourier
  side.
* `lemma92`: the part for `R`.
* `integral_conv`, `Rt_four_le`, `lemma92_Rt`: the part for `R̃`.

The next step is their Proposition 10.2, the energy bound, from Heath-Brown's Theorem 10.1 as a displayed hypothesis.

The file imports `LinnikCGLMom.lean`.
-/

import LinnikCGLMom

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLMom4

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt LinnikCGLP72
  LinnikCGLMom

/-! ### The energy -/

open scoped Classical in
/-- **Their energy `E(W)`** at one point per character: the number of `(i, j, k, l) ∈ R⁴` with
`|t_i + t_j − t_k − t_l| ≤ 1` and `χ_iχ_j = χ_kχ_l`. -/
def energy {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) : ℕ :=
  ((R ×ˢ R ×ˢ R ×ˢ R).filter fun p : ι × ι × ι × ι =>
    |t p.1 + t p.2.1 - t p.2.2.1 - t p.2.2.2| ≤ 1 ∧ χ p.1 * χ p.2.1 = χ p.2.2.1 * χ p.2.2.2).card

open scoped Classical in
lemma energy_eq_sum {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) :
    (energy R χ t : ℝ) = ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R,
      (if |t i + t j - t k - t l| ≤ 1 ∧ χ i * χ j = χ k * χ l then (1 : ℝ) else 0) := by
  unfold energy
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_product]

/-! ### The fourth power of `R` at `v = e^τ` -/

/-- `R(e^τ, a) = Σ_{i∈R}e^{iτt_i}χ_i(a)`. -/
lemma Rf_exp {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (τ : ℝ)
    (a : ZMod q) : Rf R χ t (Real.exp τ) a = ∑ i ∈ R, Complex.exp (((τ * t i : ℝ) : ℂ) * I) * χ i a := by
  unfold Rf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cpow_eq_exp (Real.exp_pos τ), Real.log_exp]

lemma conj_exp_I (x : ℝ) : conj (Complex.exp ((x : ℂ) * I)) = Complex.exp (((-x : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring_nf

open scoped Classical in
/-- **The fourth moment over the units at `v = e^τ`, exact at one point per character**:
`Σ_{a unit}|R(e^τ, a)|⁴ = φ(q)Σ_{i,j,k,l∈R}[χ_iχ_j = χ_kχ_l]e^{iτ(t_i + t_j − t_k − t_l)}`. -/
lemma sum_norm_Rf_four {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (τ : ℝ) :
    ((∑ a : (ZMod q)ˣ, ‖Rf R χ t (Real.exp τ) a‖ ^ 4 : ℝ) : ℂ) = (q.totient : ℂ) *
      ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R, (if χ i * χ j = χ k * χ l then
        Complex.exp (((τ * (t i + t j - t k - t l) : ℝ) : ℂ) * I) else 0) := by
  set e : ι → ℂ := fun i => Complex.exp (((τ * t i : ℝ) : ℂ) * I) with he
  have h1 : ∀ a : (ZMod q)ˣ, ((‖Rf R χ t (Real.exp τ) a‖ ^ 4 : ℝ) : ℂ) =
      ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R, (e i * e j * conj (e k) * conj (e l)) *
        ((χ i * χ j) a * star ((χ k * χ l) a)) := by
    intro a
    set z := Rf R χ t (Real.exp τ) a with hz
    have hz4 : ((‖z‖ ^ 4 : ℝ) : ℂ) = (z * z) * (conj z * conj z) := by
      have : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
      rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring]
      push_cast at this ⊢
      rw [this]; ring
    rw [hz4, hz, Rf_exp, map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, MulChar.mul_apply, star_mul', Complex.star_def, he]
    ring
  rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun a _ => h1 a)]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.mul_sum, sum_units_mul_star]
  split_ifs with h
  · simp only [he, conj_exp_I, ← Complex.exp_add]
    rw [mul_comm]; congr 2; push_cast; ring
  · simp

/-! ### The Fourier transform of `ψ̃₀` -/

/-- `ψ̃₀` as a complex function. -/
def psiC (x : ℝ) : ℂ := (psi0 x : ℂ)

lemma contDiff_psiC : ContDiff ℝ ∞ psiC :=
  Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ fun x => psiBump x from psiBump.contDiff)

lemma hasCompactSupport_psiC : HasCompactSupport psiC :=
  (show HasCompactSupport fun x => psiBump x from psiBump.hasCompactSupport).comp_left Complex.ofReal_zero

lemma integrable_iteratedDeriv_psiC (n : ℕ) : Integrable (iteratedDeriv n psiC) := by
  have hcs : HasCompactSupport (iteratedDeriv n psiC) := by
    have h := hasCompactSupport_psiC.iteratedFDeriv (𝕜 := ℝ) n
    have e : iteratedDeriv n psiC =
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ => L fun _ => 1) ∘ iteratedFDeriv ℝ n psiC := by
      funext x; simp [iteratedDeriv_eq_iteratedFDeriv]
    rw [e]; exact h.comp_left (by simp)
  exact (contDiff_psiC.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport hcs

/-- The constants of the decay: `D_K = ∫|ψ̃₀^{(K)}|`. -/
def Dpsi (K : ℕ) : ℝ := ∫ x, ‖iteratedDeriv K psiC x‖

lemma Dpsi_nonneg (K : ℕ) : 0 ≤ Dpsi K := integral_nonneg fun _ => norm_nonneg _

/-- `(2π|ξ|)^K|ψ̂₀(ξ)| ≤ D_K`, by round 588's integration by parts. -/
lemma fourier_psiC_decay (K : ℕ) (ξ : ℝ) : (2 * π * |ξ|) ^ K * ‖𝓕 psiC ξ‖ ≤ Dpsi K :=
  SieveSmooth.pow_mul_norm_fourier_le (contDiff_psiC.of_le (by exact_mod_cast le_top))
    (fun n _ => integrable_iteratedDeriv_psiC n) ξ

/-- `|ψ̂₀(ξ)| ≤ ∫ψ̃₀`. -/
lemma norm_fourier_psiC_le (ξ : ℝ) : ‖𝓕 psiC ξ‖ ≤ ∫ x, psi0 x := by
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans (le_of_eq ?_)
  congr 1; funext x; simp [psiC, abs_of_nonneg (psi0_nonneg x)]

/-- `∫_ℝψ̃₀(τ/X)e^{iτΔ} dτ = Xψ̂₀(−XΔ/(2π))` for `X > 0`. -/
lemma integral_psi_exp {X : ℝ} (hX : 0 < X) (Δ : ℝ) :
    ∫ τ : ℝ, (psi0 (τ / X) : ℂ) * Complex.exp (((τ * Δ : ℝ) : ℂ) * I) = (X : ℂ) * 𝓕 psiC (-(X * Δ) / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e1 : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * (-(X * Δ) / (2 * π))) * I) • psiC v =
      (fun w : ℝ => (psi0 (w / X) : ℂ) * Complex.exp (((w * Δ : ℝ) : ℂ) * I)) (v * X) := by
    intro v
    simp only [psiC, smul_eq_mul]
    rw [mul_div_cancel_right₀ v hX.ne', mul_comm]
    congr 3
    field_simp
  have h := Measure.integral_comp_mul_right
    (fun w : ℝ => (psi0 (w / X) : ℂ) * Complex.exp (((w * Δ : ℝ) : ℂ) * I)) X
  rw [integral_congr_ae (Filter.Eventually.of_forall e1), h, abs_of_pos (inv_pos.2 hX), Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hX.ne', Complex.ofReal_one, one_mul]

/-- `τ ↦ ψ̃₀(τ/X)e^{iτΔ}` is integrable for `X > 0`. -/
lemma integrable_psi_exp {X : ℝ} (hX : 0 < X) (Δ : ℝ) :
    Integrable fun τ : ℝ => (psi0 (τ / X) : ℂ) * Complex.exp (((τ * Δ : ℝ) : ℂ) * I) := by
  refine Continuous.integrable_of_hasCompactSupport (by
    exact (Complex.continuous_ofReal.comp (continuous_psi0.comp (continuous_id.div_const X))).mul (by fun_prop)) ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * X)) (b := 2 * X)) fun τ hτ => ?_
  rw [psi0_eq_zero, Complex.ofReal_zero, zero_mul]
  rw [abs_div, abs_of_pos hX, le_div_iff₀ hX]
  by_contra hc
  exact hτ ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩

/-- One term of the fourth moment: `|[χ-condition]Xψ̂₀(−XΔ/(2π))| ≤ [|Δ| ≤ 1, χ-condition]X∫ψ̃₀ + XD_K/X^K`
for `X ≥ 1`. -/
lemma norm_term_le {X : ℝ} (hX : 1 ≤ X) (K : ℕ) (Δ : ℝ) (c : Prop) [Decidable c] :
    ‖(if c then (X : ℂ) * 𝓕 psiC (-(X * Δ) / (2 * π)) else 0)‖ ≤
      (if |Δ| ≤ 1 ∧ c then X * ∫ x, psi0 x else 0) + X * (Dpsi K / X ^ K) := by
  have hX0 : 0 < X := by linarith
  have hD := Dpsi_nonneg K
  have hI : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hXK : 0 ≤ X * (Dpsi K / X ^ K) := by positivity
  by_cases hc : c
  · rw [ite_eq_left hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    by_cases hΔ : |Δ| ≤ 1
    · rw [ite_eq_left ⟨hΔ, hc⟩]
      have := norm_fourier_psiC_le (-(X * Δ) / (2 * π))
      nlinarith
    · rw [ite_eq_right fun h => hΔ h.1, zero_add]
      refine mul_le_mul_of_nonneg_left ?_ hX0.le
      have hdec := fourier_psiC_decay K (-(X * Δ) / (2 * π))
      have hξ : 2 * π * |-(X * Δ) / (2 * π)| = X * |Δ| := by
        rw [abs_div, abs_neg, abs_mul, abs_of_pos hX0, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        field_simp
      rw [hξ] at hdec
      have hXΔ : X ≤ X * |Δ| := by nlinarith [not_le.1 hΔ]
      have hpow : X ^ K ≤ (X * |Δ|) ^ K := pow_le_pow_left₀ hX0.le hXΔ K
      rw [le_div_iff₀ (by positivity)]
      calc ‖𝓕 psiC (-(X * Δ) / (2 * π))‖ * X ^ K ≤ ‖𝓕 psiC (-(X * Δ) / (2 * π))‖ * (X * |Δ|) ^ K :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = (X * |Δ|) ^ K * ‖𝓕 psiC (-(X * Δ) / (2 * π))‖ := mul_comm _ _
        _ ≤ Dpsi K := hdec
  · rw [ite_eq_right hc, norm_zero, ite_eq_right fun h => hc h.2, zero_add]
    exact hXK

/-! ### Their Lemma 9.2 for `R` -/

open scoped Classical in
/-- **Their Lemma 9.2 for `R`, at one point per character**: for `X ≥ 1` and `K ∈ ℕ`,
`∫_{[1/2,2]}Σ_{a unit}|R(v, a)|⁴ dv ≤ 2φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`, with `E` the energy. -/
theorem lemma92 {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X : ℝ} (hX : 1 ≤ X) (K : ℕ) :
    ∫ v in Icc (1 / 2 : ℝ) 2, ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 4 ≤
      2 * q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) := by
  have hX0 : 0 < X := by linarith
  set G : ℝ → ℝ := fun v => ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 4 with hG
  set H : ℝ → ℝ := fun τ => psi0 (τ / X) * G (Real.exp τ) with hH
  have hG0 : ∀ v, 0 ≤ G v := fun v => Finset.sum_nonneg fun a _ => by positivity
  have hGm : Measurable G := Finset.measurable_sum _ fun a _ => ((measurable_Rf R χ t _).norm).pow_const 4
  have hGc : Continuous fun τ => G (Real.exp τ) := by
    simp only [hG, Rf_exp]
    exact continuous_finsetSum _ fun a _ => ((continuous_finsetSum _ fun i _ => by fun_prop).norm).pow 4
  have hHc : Continuous H := (continuous_psi0.comp (continuous_id.div_const X)).mul hGc
  have hHcs : HasCompactSupport H := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * X)) (b := 2 * X)) fun τ hτ => ?_
    simp only [hH]
    rw [psi0_eq_zero, zero_mul]
    rw [abs_div, abs_of_pos hX0, le_div_iff₀ hX0]
    by_contra hc
    exact hτ ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
  have hHi : Integrable H := hHc.integrable_of_hasCompactSupport hHcs
  have hH0 : ∀ τ, 0 ≤ H τ := fun τ => mul_nonneg (psi0_nonneg _) (hG0 _)
  -- the majorant `ψ̃₀(log v/X)`, which is `1` on `[1/2, 2]`
  have hstep1 : ∫ v in Icc (1 / 2 : ℝ) 2, G v ≤ 2 * ∫ τ, H τ := by
    rw [← integral_comp_log_Ioi_zero H]
    have hint : IntegrableOn (fun v : ℝ => v⁻¹ • H (Real.log v)) (Ioi 0) :=
      (integrableOn_comp_log_Ioi_zero H).2 hHi
    have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun v hv => show (0 : ℝ) < v by linarith [hv.1]
    have hpt : ∀ v ∈ Icc (1 / 2 : ℝ) 2, G v ≤ 2 * (v⁻¹ • H (Real.log v)) := by
      intro v hv
      have hv0 : 0 < v := by linarith [hv.1]
      have hlog : |Real.log v / X| ≤ 1 := by
        rw [abs_div, abs_of_pos hX0, div_le_one hX0]
        have h1 : |Real.log v| ≤ Real.log 2 := by
          rw [abs_le]; constructor
          · have := Real.log_le_log (by norm_num) hv.1
            rw [one_div, Real.log_inv] at this; linarith
          · exact Real.log_le_log hv0 hv.2
        linarith [Real.log_two_lt_d9]
      simp only [hH, smul_eq_mul, Real.exp_log hv0, psi0_eq_one hlog, one_mul]
      have h2 : 1 ≤ 2 * v⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hv0]; linarith [hv.2]
      calc G v = 1 * G v := (one_mul _).symm
        _ ≤ 2 * v⁻¹ * G v := mul_le_mul_of_nonneg_right h2 (hG0 v)
        _ = 2 * (v⁻¹ * G v) := by ring
    have hGint : IntegrableOn G (Icc (1 / 2 : ℝ) 2) := by
      refine integrableOn_Icc_of_le hGm (C := Fintype.card (ZMod q)ˣ * (R.card : ℝ) ^ 4) fun v hv => ?_
      rw [abs_of_nonneg (hG0 v)]
      calc G v ≤ ∑ _a : (ZMod q)ˣ, (R.card : ℝ) ^ 4 :=
            Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _)
              (norm_Rf_le R χ t (by linarith [hv.1]) _) 4
        _ = Fintype.card (ZMod q)ˣ * (R.card : ℝ) ^ 4 := by simp
    calc ∫ v in Icc (1 / 2 : ℝ) 2, G v ≤ ∫ v in Icc (1 / 2 : ℝ) 2, 2 * (v⁻¹ • H (Real.log v)) :=
          setIntegral_mono_on hGint ((hint.mono_set hsub).const_mul 2) measurableSet_Icc hpt
      _ = 2 * ∫ v in Icc (1 / 2 : ℝ) 2, v⁻¹ • H (Real.log v) := integral_const_mul _ _
      _ ≤ 2 * ∫ v in Ioi 0, v⁻¹ • H (Real.log v) := by
          refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub))
            (by norm_num)
          exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv =>
            smul_nonneg (inv_nonneg.2 (le_of_lt hv)) (hH0 _))
  -- the Fourier side
  have hC : ((∫ τ, H τ : ℝ) : ℂ) = (q.totient : ℂ) * ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R,
      (if χ i * χ j = χ k * χ l then (X : ℂ) * 𝓕 psiC (-(X * (t i + t j - t k - t l)) / (2 * π)) else 0) := by
    rw [← integral_complex_ofReal]
    have e1 : ∀ τ, ((H τ : ℝ) : ℂ) = (q.totient : ℂ) * ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R,
        (if χ i * χ j = χ k * χ l then
          (psi0 (τ / X) : ℂ) * Complex.exp (((τ * (t i + t j - t k - t l) : ℝ) : ℂ) * I) else 0) := by
      intro τ
      simp only [hH, hG]
      rw [Complex.ofReal_mul, sum_norm_Rf_four, mul_left_comm]
      congr 1
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [e1]
    rw [integral_const_mul]
    congr 1
    have hint4 : ∀ i j k l, Integrable fun τ : ℝ => (if χ i * χ j = χ k * χ l then
        (psi0 (τ / X) : ℂ) * Complex.exp (((τ * (t i + t j - t k - t l) : ℝ) : ℂ) * I) else 0) := by
      intro i j k l
      split_ifs
      · exact integrable_psi_exp hX0 _
      · exact integrable_zero _ _ _
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hint4 i j k l]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hint4 i j k l]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint4 i j k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => hint4 i j k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [integral_psi_exp hX0]
    · simp
  have hstep2 : ∫ τ, H τ ≤ q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) := by
    have hnn : 0 ≤ ∫ τ, H τ := integral_nonneg hH0
    have hn : ∫ τ, H τ = ‖((∫ τ, H τ : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [hn, hC, norm_mul, Complex.norm_natCast]
    have hsum : ‖∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R,
        (if χ i * χ j = χ k * χ l then (X : ℂ) * 𝓕 psiC (-(X * (t i + t j - t k - t l)) / (2 * π)) else 0)‖ ≤
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R, ((if |t i + t j - t k - t l| ≤ 1 ∧ χ i * χ j = χ k * χ l then
          X * ∫ x, psi0 x else 0) + X * (Dpsi K / X ^ K)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      exact norm_term_le hX K _ _
    have hcount : ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R, ((if |t i + t j - t k - t l| ≤ 1 ∧ χ i * χ j = χ k * χ l then
          X * ∫ x, psi0 x else 0) + X * (Dpsi K / X ^ K)) =
        X * (∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * (X * (Dpsi K / X ^ K)) := by
      rw [energy_eq_sum]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, mul_ite, mul_one,
        mul_zero]
      ring
    calc (q.totient : ℝ) * ‖∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R, (if χ i * χ j = χ k * χ l then
          (X : ℂ) * 𝓕 psiC (-(X * (t i + t j - t k - t l)) / (2 * π)) else 0)‖
        ≤ q.totient * (X * (∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * (X * (Dpsi K / X ^ K))) :=
          mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq hcount)) (Nat.cast_nonneg _)
      _ = q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) := by ring
  calc ∫ v in Icc (1 / 2 : ℝ) 2, G v ≤ 2 * ∫ τ, H τ := hstep1
    _ ≤ 2 * (q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) :=
        mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    _ = 2 * q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) := by ring

/-! ### Their Lemma 9.2 for `R̃` -/

/-- **Fubini for the kernel of `R̃`**: for `L, X > 0` and `g` measurable with `|g| ≤ C` on `[1/2, 2]`,
`v ↦ ∫_{[1/2,2]}Lψ̃₀(L(v − u′)/(2X))g(u′) du′` is integrable on `ℝ`, with integral `2X∫ψ̃₀·∫_{[1/2,2]}g`. -/
lemma integral_conv {L X : ℝ} (hL : 0 < L) (hX : 0 < X) {g : ℝ → ℝ} (hgm : Measurable g) {C : ℝ}
    (hgb : ∀ u ∈ Icc (1 / 2 : ℝ) 2, |g u| ≤ C) :
    Integrable (fun v => ∫ u' in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (v - u') / (2 * X)) * g u') ∧
      ∫ v, ∫ u' in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (v - u') / (2 * X)) * g u' =
        2 * X * (∫ x, psi0 x) * ∫ u' in Icc (1 / 2 : ℝ) 2, g u' := by
  set g' : ℝ → ℝ := (Icc (1 / 2 : ℝ) 2).indicator g with hg'
  set F : ℝ × ℝ → ℝ := fun p => L * psi0 (L * (p.1 - p.2) / (2 * X)) * g' p.2 with hF
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgb 1 ⟨by norm_num, by norm_num⟩)
  have hg'm : Measurable g' := hgm.indicator measurableSet_Icc
  set A := 1 / 2 - 4 * X / L with hA
  set B := 2 + 4 * X / L with hB
  have hFm : Measurable F :=
    (measurable_const.mul (continuous_psi0.measurable.comp (by fun_prop))).mul (hg'm.comp measurable_snd)
  have hFint : Integrable F (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => L * C *
        ((Icc A B).indicator (fun _ => (1 : ℝ)) p.1 * (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.2))
        (volume.prod volume) := by
      refine Integrable.const_mul ?_ _
      exact Integrable.mul_prod ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
        ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
    refine hdom.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hp0 := psi0_nonneg (L * (p.1 - p.2) / (2 * X))
    have hI0 : 0 ≤ L * C *
        ((Icc A B).indicator (fun _ => (1 : ℝ)) p.1 * (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.2) :=
      mul_nonneg (by positivity) (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
    rw [Real.norm_eq_abs, show F p = L * psi0 (L * (p.1 - p.2) / (2 * X)) * g' p.2 from rfl, abs_mul, abs_mul,
      abs_of_pos hL, abs_of_nonneg hp0]
    by_cases h2 : p.2 ∈ Icc (1 / 2 : ℝ) 2
    · by_cases h1 : |p.1 - p.2| < 4 * X / L
      · have hp1 : p.1 ∈ Icc A B := by
          refine ⟨?_, ?_⟩ <;> linarith [(abs_lt.1 h1).1, (abs_lt.1 h1).2, h2.1, h2.2, hA, hB]
        rw [Set.indicator_of_mem hp1, Set.indicator_of_mem h2, mul_one, mul_one]
        have hgp : |g' p.2| ≤ C := by rw [hg', Set.indicator_of_mem h2]; exact hgb _ h2
        calc L * psi0 (L * (p.1 - p.2) / (2 * X)) * |g' p.2| ≤ L * 1 * C :=
              mul_le_mul (mul_le_mul_of_nonneg_left (psi0_le_one _) hL.le) hgp (abs_nonneg _) (by positivity)
          _ = L * C := by ring
      · have hz : psi0 (L * (p.1 - p.2) / (2 * X)) = 0 := by
          refine psi0_eq_zero ?_
          rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * X), le_div_iff₀
            (by positivity)]
          push Not at h1
          calc 2 * (2 * X) = L * (4 * X / L) := by field_simp; ring
            _ ≤ L * |p.1 - p.2| := mul_le_mul_of_nonneg_left h1 hL.le
        rw [hz, mul_zero, zero_mul]
        exact hI0
    · have : g' p.2 = 0 := by rw [hg']; exact Set.indicator_of_notMem h2 _
      rw [this, abs_zero, mul_zero]
      exact hI0
  have hinner : ∀ v, ∫ u', F (v, u') = ∫ u' in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (v - u') / (2 * X)) * g u' := by
    intro v
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
    simp only [hF, hg', Set.indicator]
    split_ifs <;> simp
  have hint1 : Integrable fun v => ∫ u' in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (v - u') / (2 * X)) * g u' := by
    have := hFint.integral_prod_left
    simpa only [hinner] using this
  refine ⟨hint1, ?_⟩
  have hswap := integral_integral_swap (f := fun v u' => F (v, u')) hFint
  have hright : ∀ u', ∫ v, F (v, u') = 2 * X * (∫ x, psi0 x) * g' u' := by
    intro u'
    simp only [hF]
    rw [integral_mul_const, integral_kernel hL hX u']
  simp only [hinner, hright] at hswap
  rw [hswap, integral_const_mul, hg', integral_indicator measurableSet_Icc]

/-- **Weighted Cauchy–Schwarz for `R̃`**: for `L = NM₂/q > 0` and `X > 0`,
`R̃_{M₂}(v, a)⁴ ≤ 2X∫ψ̃₀·∫_{[1/2,2]}Lψ̃₀(L(v − u′)/(2X))|R(u′, a)|⁴ du′`. -/
lemma Rt_four_le {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hX : 0 < X) (hL : 0 < N * M₂ / q) (v : ℝ) (a : ZMod q) :
    Rt N R χ t X M₂ v a ^ 4 ≤ 2 * X * (∫ x, psi0 x) *
      ∫ u' in Icc (1 / 2 : ℝ) 2, N * M₂ / q * psi0 (N * M₂ / q * (v - u') / (2 * X)) * ‖Rf R χ t u' a‖ ^ 4 := by
  set L := N * M₂ / q with hLdef
  set k : ℝ → ℝ := fun u' => L * psi0 (L * (v - u') / (2 * X)) with hk
  have hk0 : ∀ u', 0 ≤ k u' := fun u' => mul_nonneg hL.le (psi0_nonneg _)
  have hkm : Measurable k := measurable_const.mul (continuous_psi0.measurable.comp (by fun_prop))
  have hkb : ∀ u', k u' ≤ L := fun u' => mul_le_of_le_one_right hL.le (psi0_le_one _)
  have hmR : Measurable fun u : ℝ => ‖Rf R χ t u a‖ := (measurable_Rf R χ t a).norm
  have hRb : ∀ u ∈ Icc (1 / 2 : ℝ) 2, ‖Rf R χ t u a‖ ≤ R.card := fun u hu =>
    norm_Rf_le R χ t (by linarith [hu.1]) a
  have hcs := cs_Icc (f := fun u' => Real.sqrt (k u')) (g := fun u' => Real.sqrt (k u') * ‖Rf R χ t u' a‖ ^ 2)
    (fun _ => Real.sqrt_nonneg _) (fun _ => mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    hkm.sqrt (hkm.sqrt.mul (hmR.pow_const 2)) (Cf := Real.sqrt L) (Cg := Real.sqrt L * (R.card : ℝ) ^ 2)
    (fun u _ => Real.sqrt_le_sqrt (hkb u))
    (fun u hu => mul_le_mul (Real.sqrt_le_sqrt (hkb u)) (pow_le_pow_left₀ (norm_nonneg _) (hRb u hu) 2)
      (by positivity) (Real.sqrt_nonneg _))
  have e1 : ∀ u', Real.sqrt (k u') * (Real.sqrt (k u') * ‖Rf R χ t u' a‖ ^ 2) = k u' * ‖Rf R χ t u' a‖ ^ 2 :=
    fun u' => by rw [← mul_assoc, Real.mul_self_sqrt (hk0 u')]
  have e2 : ∀ u', Real.sqrt (k u') ^ 2 = k u' := fun u' => Real.sq_sqrt (hk0 u')
  have e3 : ∀ u', (Real.sqrt (k u') * ‖Rf R χ t u' a‖ ^ 2) ^ 2 = k u' * ‖Rf R χ t u' a‖ ^ 4 := fun u' => by
    rw [mul_pow, Real.sq_sqrt (hk0 u')]; ring
  simp only [e1, e2, e3] at hcs
  have hsq : Rt N R χ t X M₂ v a ^ 2 = ∫ u' in Icc (1 / 2 : ℝ) 2, k u' * ‖Rf R χ t u' a‖ ^ 2 :=
    Rt_sq R χ t hL.le v a
  have hA0 : 0 ≤ ∫ u' in Icc (1 / 2 : ℝ) 2, k u' := setIntegral_nonneg measurableSet_Icc fun u' _ => hk0 u'
  have hB0 : 0 ≤ ∫ u' in Icc (1 / 2 : ℝ) 2, k u' * ‖Rf R χ t u' a‖ ^ 4 :=
    setIntegral_nonneg measurableSet_Icc fun u' _ => mul_nonneg (hk0 u') (by positivity)
  have hkint : Integrable k := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_const.mul (continuous_psi0.comp (by fun_prop)))
      (HasCompactSupport.intro (isCompact_Icc (a := v - 4 * X / L) (b := v + 4 * X / L)) fun u' hu' => ?_)
    show L * psi0 (L * (v - u') / (2 * X)) = 0
    rw [psi0_eq_zero, mul_zero]
    rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * X), le_div_iff₀ (by positivity)]
    have h4 : 4 * X / L ≤ |v - u'| := by
      by_contra hc
      push Not at hc
      exact hu' ⟨by linarith [(abs_lt.1 hc).2], by linarith [(abs_lt.1 hc).1]⟩
    calc 2 * (2 * X) = L * (4 * X / L) := by field_simp; ring
      _ ≤ L * |v - u'| := mul_le_mul_of_nonneg_left h4 hL.le
  have hAle : ∫ u' in Icc (1 / 2 : ℝ) 2, k u' ≤ 2 * X * ∫ x, psi0 x := by
    have hfull : ∫ u', k u' = 2 * X * ∫ x, psi0 x := by
      have e : (fun u' => k u') = fun u' => (fun w => L * psi0 (L * (w - 0) / (2 * X))) (v - u') := by
        funext u'; simp only [hk, sub_zero]
      rw [e, integral_sub_left_eq_self (fun w => L * psi0 (L * (w - 0) / (2 * X))) volume v, integral_kernel hL hX 0]
    rw [← hfull]
    exact setIntegral_le_integral hkint (Filter.Eventually.of_forall hk0)
  calc Rt N R χ t X M₂ v a ^ 4 = (Rt N R χ t X M₂ v a ^ 2) ^ 2 := by ring
    _ = (∫ u' in Icc (1 / 2 : ℝ) 2, k u' * ‖Rf R χ t u' a‖ ^ 2) ^ 2 := by rw [hsq]
    _ ≤ (Real.sqrt (∫ u' in Icc (1 / 2 : ℝ) 2, k u') *
          Real.sqrt (∫ u' in Icc (1 / 2 : ℝ) 2, k u' * ‖Rf R χ t u' a‖ ^ 4)) ^ 2 :=
        pow_le_pow_left₀ (setIntegral_nonneg measurableSet_Icc fun u' _ => mul_nonneg (hk0 u') (by positivity))
          hcs 2
    _ = (∫ u' in Icc (1 / 2 : ℝ) 2, k u') * ∫ u' in Icc (1 / 2 : ℝ) 2, k u' * ‖Rf R χ t u' a‖ ^ 4 := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ ≤ 2 * X * (∫ x, psi0 x) * ∫ u' in Icc (1 / 2 : ℝ) 2, k u' * ‖Rf R χ t u' a‖ ^ 4 :=
        mul_le_mul_of_nonneg_right hAle hB0

open scoped Classical in
/-- **Their Lemma 9.2 for `R̃`, at one point per character**: for `L = NM₂/q > 0`, `X ≥ 1` and `K ∈ ℕ`,
`∫_ℝΣ_{a unit}R̃_{M₂}(v, a)⁴ dv ≤ (2X∫ψ̃₀)²·2φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`. -/
theorem lemma92_Rt {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X M₂ : ℝ} (hX : 1 ≤ X) (hL : 0 < N * M₂ / q) (K : ℕ) :
    ∫ v, ∑ a : (ZMod q)ˣ, Rt N R χ t X M₂ v a ^ 4 ≤ (2 * X * ∫ x, psi0 x) ^ 2 *
      (2 * q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) := by
  have hX0 : 0 < X := by linarith
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  set L := N * M₂ / q with hLdef
  have hconv : ∀ a : ZMod q, Integrable (fun v => ∫ u' in Icc (1 / 2 : ℝ) 2,
      L * psi0 (L * (v - u') / (2 * X)) * ‖Rf R χ t u' a‖ ^ 4) ∧
      ∫ v, ∫ u' in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (v - u') / (2 * X)) * ‖Rf R χ t u' a‖ ^ 4 =
        2 * X * (∫ x, psi0 x) * ∫ u' in Icc (1 / 2 : ℝ) 2, ‖Rf R χ t u' a‖ ^ 4 := fun a =>
    integral_conv hL hX0 (((measurable_Rf R χ t a).norm).pow_const 4) (C := (R.card : ℝ) ^ 4) fun u hu => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hu.1]) a) 4
  have hint : ∀ a : ZMod q, Integrable fun v => Rt N R χ t X M₂ v a ^ 4 := fun a =>
    ((hconv a).1.const_mul (2 * X * ∫ x, psi0 x)).mono' (((measurable_Rt N R χ t X M₂ a).pow_const 4)
      |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := Rt_nonneg N R χ t X M₂ v a; positivity)]
        exact Rt_four_le R χ t hX0 hL v a)
  have hone : ∀ a : ZMod q, ∫ v, Rt N R χ t X M₂ v a ^ 4 ≤
      (2 * X * ∫ x, psi0 x) ^ 2 * ∫ u' in Icc (1 / 2 : ℝ) 2, ‖Rf R χ t u' a‖ ^ 4 := by
    intro a
    calc ∫ v, Rt N R χ t X M₂ v a ^ 4 ≤ ∫ v, 2 * X * (∫ x, psi0 x) *
          ∫ u' in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (v - u') / (2 * X)) * ‖Rf R χ t u' a‖ ^ 4 :=
          integral_mono (hint a) ((hconv a).1.const_mul _) fun v => Rt_four_le R χ t hX0 hL v a
      _ = (2 * X * ∫ x, psi0 x) ^ 2 * ∫ u' in Icc (1 / 2 : ℝ) 2, ‖Rf R χ t u' a‖ ^ 4 := by
          rw [integral_const_mul, (hconv a).2]; ring
  have hRint : ∀ a : (ZMod q)ˣ, IntegrableOn (fun u => ‖Rf R χ t u (a : ZMod q)‖ ^ 4) (Icc (1 / 2 : ℝ) 2) :=
    fun a => integrableOn_Icc_of_le (((measurable_Rf R χ t _).norm).pow_const 4) (C := (R.card : ℝ) ^ 4)
      fun x hx => by
        rw [abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hx.1]) _) 4
  rw [integral_finsetSum (s := Finset.univ) (f := fun (a : (ZMod q)ˣ) v => Rt N R χ t X M₂ v (a : ZMod q) ^ 4)
    fun a _ => hint a]
  calc ∑ a : (ZMod q)ˣ, ∫ v, Rt N R χ t X M₂ v a ^ 4
      ≤ ∑ a : (ZMod q)ˣ, (2 * X * ∫ x, psi0 x) ^ 2 * ∫ u' in Icc (1 / 2 : ℝ) 2, ‖Rf R χ t u' a‖ ^ 4 :=
        Finset.sum_le_sum fun a _ => hone a
    _ = (2 * X * ∫ x, psi0 x) ^ 2 * ∫ u' in Icc (1 / 2 : ℝ) 2, ∑ a : (ZMod q)ˣ, ‖Rf R χ t u' a‖ ^ 4 := by
        rw [← Finset.mul_sum, integral_finsetSum (s := Finset.univ)
          (f := fun (a : (ZMod q)ˣ) u => ‖Rf R χ t u (a : ZMod q)‖ ^ 4) fun a _ => hRint a]
    _ ≤ (2 * X * ∫ x, psi0 x) ^ 2 *
          (2 * q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) :=
        mul_le_mul_of_nonneg_left (lemma92 R χ t hX K) (by positivity)

end LinnikCGLMom4

#print axioms LinnikCGLMom4.energy_eq_sum
#print axioms LinnikCGLMom4.sum_norm_Rf_four
#print axioms LinnikCGLMom4.fourier_psiC_decay
#print axioms LinnikCGLMom4.integral_psi_exp
#print axioms LinnikCGLMom4.lemma92
#print axioms LinnikCGLMom4.integral_conv
#print axioms LinnikCGLMom4.Rt_four_le
#print axioms LinnikCGLMom4.lemma92_Rt
