/-
# Round 687: the terms `|n| > N₀` of their `Σ_II` and the range `|ξ| > X` of `ĝ_a`, by the decay premise (the CGL
plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li discard large frequencies by the decay of `f̂_b`: their `Σ_b|f̂_b(ξ)| = O((qT)^{−200})` unless `|ξ| ⪅ T`
(lines 3480–3481, transcribed), so "we can restrict the sum over n to the range |n| ⪅ qT/M₂ at the cost of a negligible
error." (lines 3481–3482; spaces restored, the subscript transcribed and their footnote mark omitted). This file bounds,
with explicit constants, the two ranges that rounds 683 and 686 leave out: the terms `|n| > N₀` of round 683's `B_II`,
and the range `|ξ| > X` of `ĝ_a`. Their proof splits at `|ξ| = (qT)²` and discards `|ξ| > (qT)²` by the decay of
`Σ_b|f̂_b|` (lines 2781–2794): "Thus, the contribution from the region |ξ| > (qT)² is negligible and our analysis can
focus on the range |ξ| ≤ (qT)²." (lines 2795–2796; spaces restored, the exponents transcribed). The stack's `X` is
their `(qT)²`; round 683's count carries the factor `(1 + q|X|)^δ`, which grows with `X`, so round 683 integrates over
`|ξ| ≤ X` only.

The stack's form.
* The hypothesis `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`, with `D, Λ ≥ 0`, follows from the decay premise of round
  662's `CGLP81` at one exponent `j` when `T ≥ 0` and `f_b ≥ 0`, with `D` the larger of `D_j` and `0` and
  `Λ = φ(q)f_{b₀}(u₀)`.
* The terms `|n| > N₀`: for `|τ| ≤ L|n|/(2q)`, `|n/q + τ/L| ≥ |n|/(2q)`, so the premise bounds `Φ(n, τ)`
  (`norm_Phi_le_decay`); for larger `|τ|`, `|ψ̂₀(−τ)| ≤ C_K(1 + |τ|)^{−K}` and `|Φ(n, τ)| ≤ PF` (`norm_Phi_le_PF`). The
  sum over `n` uses `Σ_{n∈W, n≠0}n^{−2} ≤ 12π`, from round 685's lattice sum (`sum_inv_sq_le`).
* The range `|ξ| > X`: round 680's formula for `ĝ_a` with the premise gives `|ĝ_a(ξ)| ≤ G₁|ξ|^{−j}`, and
  `∫(1 + ξ²)⁻¹ dξ = π` (Mathlib's `integral_univ_inv_one_add_sq`).
* Their negligible errors are kept as explicit bounds, with the factors `N₀^{−(2j−2)}`, `N₀^{−(K−4)}` and
  `X^{−(2j−2)}`; the choice of `N₀`, `X`, `j` and `K` is left to the assembly of their Lemma 8.2.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `ψ̂₀` round 659's `𝓕 psiC`, `C_K` round 684's `CK`, `Φ(n, τ)` round 683's
`Phi`, `ĝ_a` the Fourier transform of round 680's `ga`, `I₀ = ∫|ψ̂₀(−τ)| dτ`, `P = Σ_{m₂∈P2 M₂}m₂`, `F = Σ_b∫f_b`,
`G₁ = #P1·#P2·(2M₂/M₁)·q#P3·D(2M₁T/M₂)^jΛ` (with `#P1 = #(P1 M₁)`, `#P2 = #(P2 M₂)`, `#P3 = #(P3 L)`), and "the
premise" the decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for every `ξ ≠ 0`.
* `sum_inv_sq_le`: `Σ_{n∈W, n≠0}n^{−2} ≤ 12π` for every finite set `W` of integers.
* `sum_inv_pow_tail_le`: for `N₀ > 0` and `s ≥ 2`, `Σ_{n∈W, |n|>N₀}|n|^{−s} ≤ 12πN₀^{−(s−2)}` for every finite set
  `W` of integers.
* `norm_Phi_le_PF`: for `f_b ≥ 0`, `|Φ(n, τ)| ≤ PF`.
* `norm_Phi_le_decay`: for `M₂ > 0`, `L > 0`, `T, D, Λ ≥ 0`, the premise, `n ≠ 0` and `|τ| ≤ L|n|/(2q)`,
  `|Φ(n, τ)| ≤ PD(2qT/(M₂|n|))^jΛ`.
* `integrable_Phi`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `τ ↦ |ψ̂₀(−τ)||Φ(n, τ)|²` is integrable.
* `integral_Phi_term_le`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `M₂ > 0`, `L > 0`, `T, D, Λ ≥ 0`, `K ≥ 2`,
  the premise and `n ≠ 0`,
  `∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ ≤ I₀(PDΛ)²(2qT/M₂)^{2j}|n|^{−2j} + πC_K(PF)²(2q/L)^{K−2}|n|^{−(K−2)}`.
* `sum_integral_Phi_tail_le`: for smooth `f_b ≥ 0` that are `0` for `|u| > A`, `M₂ > 0`, `L > 0`, `N₀ > 0`,
  `T, D, Λ ≥ 0`, `j ≥ 1`, `K ≥ 4` and the premise, `Σ_{n∈W, |n|>N₀}∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ ≤
  12π(I₀(PDΛ)²(2qT/M₂)^{2j}N₀^{−(2j−2)} + πC_K(PF)²(2q/L)^{K−2}N₀^{−(K−4)})` for every finite set `W` of integers.
* `gJw_le`: round 662's `gJw` is at most `q`.
* `norm_fourier_ga_le_decay`: for smooth `f_b` that are `0` for `|u| > A`, `M₁, M₂ > 0`, `T, D, Λ ≥ 0`, the premise and
  `ξ ≠ 0`, `|ĝ_a(ξ)| ≤ G₁|ξ|^{−j}`.
* `setIntegral_ga_tail_le`: for smooth `f_b` that are `0` for `|u| > A`, `M₁, M₂ > 0`, `X ≥ 1`, `T, D, Λ ≥ 0`, `j ≥ 1`
  and the premise, `∫_{|ξ|>X}Σ_a|ĝ_a(ξ)|² dξ ≤ 2πφ(q)G₁²X^{−(2j−2)}`.

The file imports `LinnikCGLJtil.lean`.
-/

import LinnikCGLJtil

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLTail

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov LinnikCGLSig2 LinnikCGLFtil
  LinnikCGLLoc LinnikCGLJtil

/-! ### Sums of `|n|^{−s}` -/

/-- `Σ_{n∈W, n≠0}n^{−2} ≤ 12π` for every finite set `W` of integers. -/
lemma sum_inv_sq_le (W : Finset ℤ) : ∑ n ∈ W.filter (· ≠ 0), ((n : ℝ) ^ 2)⁻¹ ≤ 12 * π := by
  have h := sum_lor_lattice_le one_pos 0 (W.filter (· ≠ 0))
  have hle : ∀ n ∈ W.filter (· ≠ 0), ((n : ℝ) ^ 2)⁻¹ ≤ 2 * lor 1 (1 * n + 0) := by
    intro n hn
    have hn0 : n ≠ 0 := (Finset.mem_filter.1 hn).2
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_abs (n : ℝ)]
    simp only [lor, one_pow, one_mul, add_zero]
    calc ((n : ℝ) ^ 2)⁻¹ ≤ ((1 + (n : ℝ) ^ 2) / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
      _ = 2 * (1 + (n : ℝ) ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  calc ∑ n ∈ W.filter (· ≠ 0), ((n : ℝ) ^ 2)⁻¹ ≤ ∑ n ∈ W.filter (· ≠ 0), 2 * lor 1 (1 * n + 0) :=
        Finset.sum_le_sum hle
    _ = 2 * ∑ n ∈ W.filter (· ≠ 0), lor 1 (1 * n + 0) := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * π + 4 * π / 1) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 12 * π := by ring

/-- For `N₀ > 0` and `s ≥ 2`, `Σ_{n∈W, |n|>N₀}|n|^{−s} ≤ 12πN₀^{−(s−2)}` for every finite set `W` of integers. -/
lemma sum_inv_pow_tail_le {N₀ : ℝ} (hN₀ : 0 < N₀) {s : ℕ} (hs : 2 ≤ s) (W : Finset ℤ) :
    ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|), (|(n : ℝ)| ^ s)⁻¹ ≤ 12 * π * (N₀ ^ (s - 2))⁻¹ := by
  have hterm : ∀ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|),
      (|(n : ℝ)| ^ s)⁻¹ ≤ (N₀ ^ (s - 2))⁻¹ * ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    have h := (Finset.mem_filter.1 hn).2
    have hpos : 0 < |(n : ℝ)| := hN₀.trans h
    have e : |(n : ℝ)| ^ s = |(n : ℝ)| ^ (s - 2) * (n : ℝ) ^ 2 := by
      rw [← sq_abs (n : ℝ), ← pow_add, Nat.sub_add_cancel hs]
    rw [e, mul_inv]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (pow_le_pow_left₀ hN₀.le h.le _)) (by positivity)
  have hsub : W.filter (fun n : ℤ => N₀ < |(n : ℝ)|) ⊆ W.filter (· ≠ 0) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, fun h0 => ?_⟩
    rw [h0, Int.cast_zero, abs_zero] at hn
    linarith [hn.2]
  calc _ ≤ ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|), (N₀ ^ (s - 2))⁻¹ * ((n : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (N₀ ^ (s - 2))⁻¹ * ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (N₀ ^ (s - 2))⁻¹ * ∑ n ∈ W.filter (· ≠ 0), ((n : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity)
          (by positivity)
    _ ≤ (N₀ ^ (s - 2))⁻¹ * (12 * π) := mul_le_mul_of_nonneg_left (sum_inv_sq_le W) (by positivity)
    _ = _ := by ring

/-! ### `Φ(n, τ)` by the decay premise -/

/-- For `f_b ≥ 0`, `|Φ(n, τ)| ≤ PF` with `P = Σ_{m₂∈P2 M₂}m₂` and `F = Σ_b∫f_b`. -/
lemma norm_Phi_le_PF {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) (M₂ L : ℝ) (n : ℤ)
    (τ : ℝ) : ‖Phi f M₂ L n τ‖ ≤ (∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * ∑ b, ∫ u, f b u := by
  refine (norm_Phi_le hf M₂ L n τ).trans (le_of_eq ?_)
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₂ hm₂ => Finset.sum_congr rfl fun b _ => ?_
  have := (mem_P2 m₂).1 hm₂
  rw [abs_of_pos (by linarith [this.1, this.2])]

/-- **`Φ(n, τ)` by the decay premise**: for `q ≥ 1`, `M₂ > 0`, `L > 0`, `T, D, Λ ≥ 0`, the decay
`Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`, `n ≠ 0` and `|τ| ≤ L|n|/(2q)`, `|Φ(n, τ)| ≤ PD(2qT/(M₂|n|))^jΛ`, with
`P = Σ_{m₂∈P2 M₂}m₂`. -/
lemma norm_Phi_le_decay {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} {M₂ L T D Λ : ℝ} {j : ℕ} (hM₂ : 0 < M₂)
    (hL : 0 < L) (hT : 0 ≤ T) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ j * Λ) {n : ℤ} (hn : n ≠ 0) {τ : ℝ}
    (hτ : |τ| ≤ L * |(n : ℝ)| / (2 * q)) :
    ‖Phi f M₂ L n τ‖ ≤ (∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * (D * (2 * q * T / (M₂ * |(n : ℝ)|)) ^ j * Λ) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  -- the argument of `f̂_b` is at least `M₂|n|/(2q)` in size
  have hlow : ∀ m₂ ∈ P2 M₂, M₂ * |(n : ℝ)| / (2 * q) ≤ |(m₂ : ℝ) * (n / q + τ / L)| := by
    intro m₂ hm₂
    have h2 := (mem_P2 m₂).1 hm₂
    have hp : (0 : ℝ) < m₂ := by linarith [h2.1]
    have h1 : |(n : ℝ) / q| - |τ / L| ≤ |(n : ℝ) / q + τ / L| := by
      have := abs_add_le ((n : ℝ) / q + τ / L) (-(τ / L))
      rw [add_neg_cancel_right, abs_neg] at this
      linarith
    have h3 : |τ / L| ≤ |(n : ℝ)| / (2 * q) := by
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
      calc |τ| ≤ L * |(n : ℝ)| / (2 * q) := hτ
        _ = |(n : ℝ)| / (2 * q) * L := by ring
    have h4 : |(n : ℝ) / q| = |(n : ℝ)| / q := by rw [abs_div, abs_of_pos hq]
    have h5 : |(n : ℝ)| / (2 * q) ≤ |(n : ℝ) / q + τ / L| := by
      have : |(n : ℝ)| / q = 2 * (|(n : ℝ)| / (2 * q)) := by field_simp
      linarith
    rw [abs_mul, abs_of_pos hp]
    calc M₂ * |(n : ℝ)| / (2 * q) = M₂ * (|(n : ℝ)| / (2 * q)) := by ring
      _ ≤ m₂ * |(n : ℝ) / q + τ / L| :=
          mul_le_mul h2.1.le h5 (by positivity) hp.le
  have hpos : 0 < M₂ * |(n : ℝ)| / (2 * q) := by positivity
  have e2 : 2 * q * T / (M₂ * |(n : ℝ)|) = T / (M₂ * |(n : ℝ)| / (2 * q)) := by field_simp
  unfold Phi
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b : (ZMod q)ˣ, ‖∑ m₂ ∈ P2 M₂, ((m₂ : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * (n / q + τ / L)) *
        ZMod.stdAddChar (-((n : ZMod q) * ((b : ZMod q) * (m₂ : ZMod q))))‖
      ≤ ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) * ‖𝓕 (fC f b) ((m₂ : ℝ) * (n / q + τ / L))‖ := by
        refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₂ hm₂ => ?_)
        have h2 := (mem_P2 m₂).1 hm₂
        rw [norm_mul, norm_stdAddChar, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith [h2.1, h2.2])]
    _ = ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) * ∑ b : (ZMod q)ˣ, ‖𝓕 (fC f b) ((m₂ : ℝ) * (n / q + τ / L))‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m₂ _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) * (D * (2 * q * T / (M₂ * |(n : ℝ)|)) ^ j * Λ) := by
        refine Finset.sum_le_sum fun m₂ hm₂ => mul_le_mul_of_nonneg_left ?_ (by
          have := (mem_P2 m₂).1 hm₂; linarith [this.1, this.2])
        have hl := hlow m₂ hm₂
        have hne : (m₂ : ℝ) * (n / q + τ / L) ≠ 0 := by
          intro h; rw [h, abs_zero] at hl; linarith
        refine (hdec _ hne).trans ?_
        rw [e2]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_left hT hpos hl) _) hD) hΛ
    _ = _ := by rw [Finset.sum_mul]

/-- For smooth `f_b ≥ 0` that are `0` for `|u| > A`, `τ ↦ |ψ̂₀(−τ)||Φ(n, τ)|²` is integrable. -/
lemma integrable_Phi {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) (M₂ L : ℝ) (n : ℤ) :
    Integrable fun τ => ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 :=
  integrable_norm_fourier_psiC_neg.mul_bdd (c := ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * ∑ b, ∫ u, f b u) ^ 2)
    ((continuous_Phi hfs hA M₂ L n).norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun τ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_Phi_le_PF hf M₂ L n τ) 2)

/-- **One term `n ≠ 0`**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `M₂ > 0`, `L > 0`,
`T, D, Λ ≥ 0`, `K ≥ 2` and the decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`,
`∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ ≤ I₀(PDΛ)²(2qT/M₂)^{2j}|n|^{−2j} + πC_K(PF)²(2q/L)^{K−2}|n|^{−(K−2)}`, with
`I₀ = ∫|ψ̂₀(−τ)| dτ`, `P = Σ_{m₂∈P2 M₂}m₂` and `F = Σ_b∫f_b`. -/
lemma integral_Phi_term_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) {M₂ L T D Λ : ℝ} {j K : ℕ} (hM₂ : 0 < M₂)
    (hL : 0 < L) (hT : 0 ≤ T) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ) (hK : 2 ≤ K)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ j * Λ) {n : ℤ} (hn : n ≠ 0) :
    ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 ≤
      (∫ τ, ‖𝓕 psiC (-τ)‖) * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * D * Λ) ^ 2 * (2 * q * T / M₂) ^ (2 * j) *
          (|(n : ℝ)| ^ (2 * j))⁻¹ +
        π * CK K * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * ∑ b, ∫ u, f b u) ^ 2 * (2 * q / L) ^ (K - 2) *
          (|(n : ℝ)| ^ (K - 2))⁻¹ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hn0 : 0 < |(n : ℝ)| := by linarith
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  set P : ℝ := ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) with hP
  set F : ℝ := ∑ b, ∫ u, f b u with hF
  set R : ℝ := L * |(n : ℝ)| / (2 * q) with hR
  have hR0 : 0 < R := by positivity
  set Bd : ℝ := P * (D * (2 * q * T / (M₂ * |(n : ℝ)|)) ^ j * Λ) with hBd
  set c : ℝ := CK K * (P * F) ^ 2 * ((1 + R) ^ (K - 2))⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 ≤ ‖𝓕 psiC (-τ)‖ * Bd ^ 2 + c * (1 + τ ^ 2)⁻¹ := by
    intro τ
    have hw := norm_nonneg (𝓕 psiC (-τ))
    by_cases hτ : |τ| ≤ R
    · have h1 := norm_Phi_le_decay (f := f) hM₂ hL hT hD hΛ hdec hn hτ
      have h2 : ‖Phi f M₂ L n τ‖ ^ 2 ≤ Bd ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : 0 ≤ c * (1 + τ ^ 2)⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hw]
    · have hτ' : R < |τ| := not_le.mp hτ
      have h1 := norm_Phi_le_PF hf M₂ L n τ
      have h2 : ‖Phi f M₂ L n τ‖ ^ 2 ≤ (P * F) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hk := norm_fourier_psiC_le_CK K (-τ)
      rw [abs_neg] at hk
      have hbig : (1 + R) ^ (K - 2) * (1 + τ ^ 2) ≤ (1 + |τ|) ^ K := by
        have e : (1 + |τ|) ^ K = (1 + |τ|) ^ (K - 2) * (1 + |τ|) ^ 2 := by
          rw [← pow_add, Nat.sub_add_cancel hK]
        rw [e]
        refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _) ?_ (by positivity) (by positivity)
        nlinarith [abs_nonneg τ, sq_abs τ]
      have hw' : ‖𝓕 psiC (-τ)‖ ≤ CK K * ((1 + R) ^ (K - 2))⁻¹ * (1 + τ ^ 2)⁻¹ := by
        have hpos : 0 < (1 + R) ^ (K - 2) * (1 + τ ^ 2) := by positivity
        rw [mul_assoc, ← mul_inv, le_mul_inv_iff₀ hpos]
        calc ‖𝓕 psiC (-τ)‖ * ((1 + R) ^ (K - 2) * (1 + τ ^ 2)) ≤ ‖𝓕 psiC (-τ)‖ * (1 + |τ|) ^ K :=
              mul_le_mul_of_nonneg_left hbig hw
          _ = (1 + |τ|) ^ K * ‖𝓕 psiC (-τ)‖ := by ring
          _ ≤ CK K := hk
      have h3 : 0 ≤ ‖𝓕 psiC (-τ)‖ * Bd ^ 2 := by positivity
      calc ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 ≤ CK K * ((1 + R) ^ (K - 2))⁻¹ * (1 + τ ^ 2)⁻¹ * (P * F) ^ 2 :=
            mul_le_mul hw' h2 (sq_nonneg _) (by positivity)
        _ = c * (1 + τ ^ 2)⁻¹ := by rw [hc]; ring
        _ ≤ _ := by linarith
  have hRi : Integrable fun τ : ℝ => ‖𝓕 psiC (-τ)‖ * Bd ^ 2 + c * (1 + τ ^ 2)⁻¹ :=
    (integrable_norm_fourier_psiC_neg.mul_const (Bd ^ 2)).add (integrable_inv_one_add_sq.const_mul c)
  have hint := integral_mono (integrable_Phi hfs hA hf M₂ L n) hRi hpt
  rw [integral_add (integrable_norm_fourier_psiC_neg.mul_const _) (integrable_inv_one_add_sq.const_mul _),
    integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq] at hint
  have hRle : ((1 + R) ^ (K - 2))⁻¹ ≤ (2 * q / L) ^ (K - 2) * (|(n : ℝ)| ^ (K - 2))⁻¹ := by
    have e : (2 * q / L) ^ (K - 2) * (|(n : ℝ)| ^ (K - 2))⁻¹ = (R ^ (K - 2))⁻¹ := by
      rw [← inv_pow, ← mul_pow, ← inv_pow, hR]
      congr 1
      field_simp
    rw [e]
    exact inv_anti₀ (pow_pos hR0 _) (pow_le_pow_left₀ hR0.le (by linarith) _)
  refine hint.trans (add_le_add (le_of_eq ?_) ?_)
  · have hpow : ∀ x : ℝ, x ^ (2 * j) = (x ^ j) ^ 2 := fun x => by rw [← pow_mul, mul_comm]
    rw [hBd, hpow, hpow]
    ring
  · calc c * π = π * CK K * (P * F) ^ 2 * ((1 + R) ^ (K - 2))⁻¹ := by rw [hc]; ring
      _ ≤ π * CK K * (P * F) ^ 2 * ((2 * q / L) ^ (K - 2) * (|(n : ℝ)| ^ (K - 2))⁻¹) :=
          mul_le_mul_of_nonneg_left hRle (by positivity)
      _ = _ := by ring

/-- **The terms `|n| > N₀`**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A`, `M₂ > 0`, `L > 0`, `N₀ > 0`,
`T, D, Λ ≥ 0`, `j ≥ 1`, `K ≥ 4` and the decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`,
`Σ_{n∈W, |n|>N₀}∫|ψ̂₀(−τ)||Φ(n, τ)|² dτ ≤ 12π(I₀(PDΛ)²(2qT/M₂)^{2j}N₀^{−(2j−2)} + πC_K(PF)²(2q/L)^{K−2}N₀^{−(K−4)})`
for every finite set `W` of integers, with `I₀ = ∫|ψ̂₀(−τ)| dτ`, `P = Σ_{m₂∈P2 M₂}m₂` and `F = Σ_b∫f_b`. -/
theorem sum_integral_Phi_tail_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) (hf : ∀ b u, 0 ≤ f b u) {M₂ L N₀ T D Λ : ℝ} {j K : ℕ}
    (hM₂ : 0 < M₂) (hL : 0 < L) (hN₀ : 0 < N₀) (hT : 0 ≤ T) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ) (hj : 1 ≤ j) (hK : 4 ≤ K)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ j * Λ) (W : Finset ℤ) :
    ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|), ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2 ≤
      12 * π * ((∫ τ, ‖𝓕 psiC (-τ)‖) * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * D * Λ) ^ 2 * (2 * q * T / M₂) ^ (2 * j) *
          (N₀ ^ (2 * j - 2))⁻¹ +
        π * CK K * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * ∑ b, ∫ u, f b u) ^ 2 * (2 * q / L) ^ (K - 2) *
          (N₀ ^ (K - 4))⁻¹) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hCK : 0 ≤ CK K := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (norm_fourier_psiC_le_CK K 0)
  have hI0 : 0 ≤ ∫ τ, ‖𝓕 psiC (-τ)‖ := integral_nonneg fun τ => norm_nonneg _
  set a : ℝ := (∫ τ, ‖𝓕 psiC (-τ)‖) * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * D * Λ) ^ 2 * (2 * q * T / M₂) ^ (2 * j)
    with ha
  set c : ℝ := π * CK K * ((∑ m₂ ∈ P2 M₂, (m₂ : ℝ)) * ∑ b, ∫ u, f b u) ^ 2 * (2 * q / L) ^ (K - 2) with hc
  have ha0 : 0 ≤ a := by positivity
  have hc0 : 0 ≤ c := by positivity
  have e : K - 2 - 2 = K - 4 := by omega
  calc ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|), ∫ τ, ‖𝓕 psiC (-τ)‖ * ‖Phi f M₂ L n τ‖ ^ 2
      ≤ ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|),
          (a * (|(n : ℝ)| ^ (2 * j))⁻¹ + c * (|(n : ℝ)| ^ (K - 2))⁻¹) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have h := (Finset.mem_filter.1 hn).2
        have hn0 : n ≠ 0 := by
          rintro rfl
          rw [Int.cast_zero, abs_zero] at h
          linarith
        exact integral_Phi_term_le hfs hA hf hM₂ hL hT hD hΛ (by omega) hdec hn0
    _ = a * ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|), (|(n : ℝ)| ^ (2 * j))⁻¹ +
        c * ∑ n ∈ W.filter (fun n : ℤ => N₀ < |(n : ℝ)|), (|(n : ℝ)| ^ (K - 2))⁻¹ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * (12 * π * (N₀ ^ (2 * j - 2))⁻¹) + c * (12 * π * (N₀ ^ (K - 2 - 2))⁻¹) :=
        add_le_add (mul_le_mul_of_nonneg_left (sum_inv_pow_tail_le hN₀ (by omega) W) ha0)
          (mul_le_mul_of_nonneg_left (sum_inv_pow_tail_le hN₀ (by omega) W) hc0)
    _ = _ := by rw [e]; ring

/-! ### The range `|ξ| > X` of `ĝ_a` -/

/-- Their gcd `(am₁ + bm₂ + m₃, q)` is at most `q`. -/
lemma gJw_le {q : ℕ} [NeZero q] (a b : (ZMod q)ˣ) (m : ℤ × ℤ × ℤ) : gJw a b m ≤ q := by
  unfold gJw; exact_mod_cast Nat.gcd_le_right _ (Nat.pos_of_ne_zero (NeZero.ne q))

/-- **`ĝ_a` by the decay premise**: for `q ≥ 1`, smooth `f_b` that are `0` for `|u| > A`, `M₁, M₂ > 0`,
`T, D, Λ ≥ 0`, the decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`, and `ξ ≠ 0`,
`|ĝ_a(ξ)| ≤ G₁|ξ|^{−j}` with `G₁ = #P1·#P2·(2M₂/M₁)·q#P3·D(2M₁T/M₂)^jΛ`. -/
lemma norm_fourier_ga_le_decay {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L T D Λ : ℝ} {j : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hT : 0 ≤ T) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ j * Λ) (a : (ZMod q)ˣ) {ξ : ℝ}
    (hξ : ξ ≠ 0) :
    ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ≤
      (P1 M₁).card * (P2 M₂).card * (2 * M₂ / M₁) * (q * (P3 L).card) * (D * (2 * M₁ * T / M₂) ^ j * Λ) *
        (|ξ| ^ j)⁻¹ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hξ0 : 0 < |ξ| := abs_pos.mpr hξ
  set Q : ℝ := q * (P3 L).card with hQ
  -- the sum over `m₃`
  have hS : ∀ (b : (ZMod q)ˣ) (m₁ m₂ : ℤ), ‖∑ m₃ ∈ P3 L, ((psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) : ℝ) : ℂ) *
      Complex.exp (2 * π * I * ((m₃ : ℝ) * ξ / (m₁ : ℝ)))‖ ≤ Q := by
    intro b m₁ m₂
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m₃ ∈ P3 L, ‖((psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) : ℝ) : ℂ) *
          Complex.exp (2 * π * I * ((m₃ : ℝ) * ξ / (m₁ : ℝ)))‖ ≤ ∑ _m₃ ∈ P3 L, (q : ℝ) := by
          refine Finset.sum_le_sum fun m₃ _ => ?_
          have he : (2 * π * I * ((m₃ : ℝ) * ξ / (m₁ : ℝ)) : ℂ) =
              ((2 * π * ((m₃ : ℝ) * ξ / (m₁ : ℝ)) : ℝ) : ℂ) * I := by push_cast; ring
          rw [norm_mul, he, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (psi0_nonneg _) (gJw_nonneg _ _ _))]
          calc psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) ≤ 1 * q :=
                mul_le_mul (psi0_le_one _) (gJw_le a b _) (gJw_nonneg _ _ _) zero_le_one
            _ = q := one_mul _
      _ = Q := by rw [Finset.sum_const, nsmul_eq_mul, hQ]; ring
  -- the decay of `f̂_b`
  have hF : ∀ m₁ ∈ P1 M₁, ∀ m₂ ∈ P2 M₂, ∑ b : (ZMod q)ˣ, ‖𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ ≤
      D * (2 * M₁ * T / M₂) ^ j * Λ * (|ξ| ^ j)⁻¹ := by
    intro m₁ hm₁ m₂ hm₂
    have h1 := (mem_P1 m₁).1 hm₁
    have h2 := (mem_P2 m₂).1 hm₂
    have hp2 : (0 : ℝ) < m₂ := by linarith [h2.1]
    have hm1 : 0 < |(m₁ : ℝ)| := by linarith [h1.1]
    have hlow : M₂ * |ξ| / (2 * M₁) ≤ |(m₂ : ℝ) * ξ / m₁| := by
      rw [abs_div, abs_mul, abs_of_pos hp2, div_le_div_iff₀ (by positivity) hm1]
      have := mul_le_mul h2.1.le h1.2 hm1.le hp2.le
      nlinarith [hξ0]
    have hpos : 0 < M₂ * |ξ| / (2 * M₁) := by positivity
    have hne : (m₂ : ℝ) * ξ / m₁ ≠ 0 := by
      intro h; rw [h, abs_zero] at hlow; linarith
    refine (hdec _ hne).trans ?_
    have e : D * (2 * M₁ * T / M₂) ^ j * Λ * (|ξ| ^ j)⁻¹ = D * (T / (M₂ * |ξ| / (2 * M₁))) ^ j * Λ := by
      rw [← inv_pow, mul_assoc D, mul_comm _ Λ, mul_assoc D, mul_assoc Λ, ← mul_pow,
        show 2 * M₁ * T / M₂ * |ξ|⁻¹ = T / (M₂ * |ξ| / (2 * M₁)) by field_simp]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left hT hpos hlow) _) hD) hΛ
  rw [fourier_ga hfs hA hM₁ a ξ]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b : (ZMod q)ˣ, ‖∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) *
        𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁) * ∑ m₃ ∈ P3 L, ((psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) : ℝ) : ℂ) *
          Complex.exp (2 * π * I * ((m₃ : ℝ) * ξ / (m₁ : ℝ)))‖
      ≤ ∑ b : (ZMod q)ˣ, ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, 2 * M₂ / M₁ * Q * ‖𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ := by
        refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₁ hm₁ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₂ hm₂ => ?_))
        have h1 := (mem_P1 m₁).1 hm₁
        have h2 := (mem_P2 m₂).1 hm₂
        have hp2 : (0 : ℝ) < m₂ := by linarith [h2.1]
        have hm1 : 0 < |(m₁ : ℝ)| := by linarith [h1.1]
        have hc : (m₂ : ℝ) / |(m₁ : ℝ)| ≤ 2 * M₂ / M₁ := by
          rw [div_le_div_iff₀ hm1 hM₁]
          nlinarith [h1.1, h2.2]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        calc (m₂ : ℝ) / |(m₁ : ℝ)| * ‖𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ * ‖∑ m₃ ∈ P3 L,
              ((psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) : ℝ) : ℂ) * Complex.exp (2 * π * I * ((m₃ : ℝ) * ξ / (m₁ : ℝ)))‖
            ≤ 2 * M₂ / M₁ * ‖𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ * Q :=
              mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) (hS b m₁ m₂) (norm_nonneg _)
                (by positivity)
          _ = 2 * M₂ / M₁ * Q * ‖𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ := by ring
    _ = ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, 2 * M₂ / M₁ * Q * ∑ b : (ZMod q)ˣ, ‖𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m₂ _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, 2 * M₂ / M₁ * Q * (D * (2 * M₁ * T / M₂) ^ j * Λ * (|ξ| ^ j)⁻¹) :=
        Finset.sum_le_sum fun m₁ hm₁ => Finset.sum_le_sum fun m₂ hm₂ =>
          mul_le_mul_of_nonneg_left (hF m₁ hm₁ m₂ hm₂) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring

/-- **The range `|ξ| > X`**: for `q ≥ 1`, smooth `f_b` that are `0` for `|u| > A`, `M₁, M₂ > 0`, `X ≥ 1`,
`T, D, Λ ≥ 0`, `j ≥ 1` and the decay `Σ_b|f̂_b(ξ)| ≤ D(T/|ξ|)^jΛ` for `ξ ≠ 0`,
`∫_{|ξ|>X}Σ_a|ĝ_a(ξ)|² dξ ≤ 2πφ(q)G₁²X^{−(2j−2)}`, with `G₁ = #P1·#P2·(2M₂/M₁)·q#P3·D(2M₁T/M₂)^jΛ`. -/
theorem setIntegral_ga_tail_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L X T D Λ : ℝ} {j : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hX : 1 ≤ X) (hT : 0 ≤ T) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ) (hj : 1 ≤ j)
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D * (T / |ξ|) ^ j * Λ) :
    ∫ ξ in (Icc (-X) X)ᶜ, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 ≤
      2 * π * q.totient * ((P1 M₁).card * (P2 M₂).card * (2 * M₂ / M₁) * (q * (P3 L).card) *
        (D * (2 * M₁ * T / M₂) ^ j * Λ)) ^ 2 * (X ^ (2 * j - 2))⁻¹ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set G₁ : ℝ := (P1 M₁).card * (P2 M₂).card * (2 * M₂ / M₁) * (q * (P3 L).card) * (D * (2 * M₁ * T / M₂) ^ j * Λ)
    with hG₁
  have hG₁0 : 0 ≤ G₁ := by positivity
  set c : ℝ := q.totient * G₁ ^ 2 * (X ^ (2 * j - 2))⁻¹ * 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ ξ ∈ (Icc (-X) X)ᶜ, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 ≤
      c * (1 + ξ ^ 2)⁻¹ := by
    intro ξ hξ
    have hXξ : X < |ξ| := by
      by_contra h
      exact hξ (abs_le.mp (not_lt.mp h))
    have hξ0 : 0 < |ξ| := by linarith
    have hne : ξ ≠ 0 := abs_pos.mp hξ0
    have hone : ∀ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 ≤ (G₁ * (|ξ| ^ j)⁻¹) ^ 2 :=
      fun a => pow_le_pow_left₀ (norm_nonneg _) (norm_fourier_ga_le_decay hfs hA hM₁ hM₂ hT hD hΛ hdec a hne) 2
    have hsq : 1 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
    have hkey : (|ξ| ^ j)⁻¹ ^ 2 ≤ (X ^ (2 * j - 2))⁻¹ * (2 * (1 + ξ ^ 2)⁻¹) := by
      have e : (|ξ| ^ j)⁻¹ ^ 2 = (|ξ| ^ (2 * j - 2))⁻¹ * (ξ ^ 2)⁻¹ := by
        rw [← sq_abs ξ, ← mul_inv, ← pow_add, inv_pow, ← pow_mul, Nat.sub_add_cancel (by omega), mul_comm]
      rw [e]
      refine mul_le_mul (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hXξ.le _)) ?_
        (by positivity) (by positivity)
      calc (ξ ^ 2)⁻¹ ≤ ((1 + ξ ^ 2) / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
        _ = 2 * (1 + ξ ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    calc ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2
        ≤ ∑ _a : (ZMod q)ˣ, (G₁ * (|ξ| ^ j)⁻¹) ^ 2 := Finset.sum_le_sum fun a _ => hone a
      _ = q.totient * G₁ ^ 2 * (|ξ| ^ j)⁻¹ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]; ring
      _ ≤ q.totient * G₁ ^ 2 * ((X ^ (2 * j - 2))⁻¹ * (2 * (1 + ξ ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = c * (1 + ξ ^ 2)⁻¹ := by rw [hc]; ring
  have hmaj : Integrable fun ξ : ℝ => c * (1 + ξ ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul c
  calc ∫ ξ in (Icc (-X) X)ᶜ, ∑ a : (ZMod q)ˣ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2
      ≤ ∫ ξ in (Icc (-X) X)ᶜ, c * (1 + ξ ^ 2)⁻¹ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => Finset.sum_nonneg fun a _ => sq_nonneg _)
          hmaj.integrableOn ((ae_restrict_iff' measurableSet_Icc.compl).2 (Eventually.of_forall hpt))
    _ ≤ ∫ ξ, c * (1 + ξ ^ 2)⁻¹ :=
        setIntegral_le_integral hmaj (Eventually.of_forall fun ξ => by positivity)
    _ = c * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
    _ = _ := by rw [hc]; ring

end LinnikCGLTail

#print axioms LinnikCGLTail.sum_inv_pow_tail_le
#print axioms LinnikCGLTail.norm_Phi_le_decay
#print axioms LinnikCGLTail.integral_Phi_term_le
#print axioms LinnikCGLTail.sum_integral_Phi_tail_le
#print axioms LinnikCGLTail.norm_fourier_ga_le_decay
#print axioms LinnikCGLTail.setIntegral_ga_tail_le
