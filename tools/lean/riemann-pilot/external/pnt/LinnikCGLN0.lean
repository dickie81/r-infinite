/-
# Round 682: the term `n = 0` of `ĝ_a`, their `I` (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li bound the terms of `ĝ_a` with `q | n` in "8.2.5. The contribution of I. By the definition of
ĝ_{a,2}(ξ), we see that" (line 4235; spaces restored, the hat and subscripts transcribed), "It follows from the
Cauchy-Schwarz inequality and the positivity of f_b that" (line 4284; spaces restored, the subscript transcribed) and
"Since M₁, M₂, M₃ ≤ M, we conclude that" (line 4325; spaces restored, the subscripts transcribed), then (8.13). This
file bounds the term `n = 0` of round 682's `LinnikCGLNsum.fourier_ga_split`, which corresponds to their term `ℓ = 0`
in (8.4) (lines 2868–2891).

The stack's form.
* Their region `|ξ| ≤ (qT)^ηM₁/M₃` is not used: `|ψ̂₀(−Lξ/m₁)| ≤ B₄L_{L/(2M₁)}(ξ)²` for `|m₁| ≤ 2M₁` (round 681's
  `norm_fourier_psiC_le_lor`) and `∫L_c(ξ) dξ = π/c` (round 673's `integral_lor`) bound the integral over all `ξ`.
* Their `sup_ξ|f̂_b(ξ)| ≤ ∫f_b` for `f_b ≥ 0` is `norm_fourier_fC_le`, and their `Σ_{d mod q}(d, q)/q ⪅ 1` is
  `|c_q(0)| ≤ Σ_{h∈ℤ/qℤ}(h, q)` (round 681's `norm_cqg_le`).

Plain statements, with `q ≥ 1` (`[NeZero q]`), `L_c(r) = (1 + c²r²)⁻¹` (round 673's `lor`), `B₄` round 681's `B4`,
`(h, q)` round 681's `gw`, and `F(m₁, n)` and `tg` round 682's `LinnikCGLNsum.Fb` and `LinnikCGLNsum.tg`.
* `norm_fourier_fC_le`: for `f_b ≥ 0`, `|f̂_b(η)| ≤ ∫f_b`.
* `norm_Fb_le_int`: for `f_b ≥ 0`, `M₁ > 0` and `m₁ ∈ P1 M₁`, `|F(m₁, n)| ≤ #P2·(2M₂/M₁)Σ_b∫f_b`.
* `norm_tg_zero_le`: for `f_b ≥ 0`, `M₁ > 0`, `L > 0` and `m₁ ∈ P1 M₁`,
  `|tg(a, m₁, 0)| ≤ (L/q)B₄L_{L/(2M₁)}(ξ)²(Σ_h(h, q))#P2·(2M₂/M₁)Σ_b∫f_b`.
* `W0`, `norm_g0_le`: with `W₀ = #P1·(L/q)B₄(Σ_h(h, q))#P2·(2M₂/M₁)Σ_b∫f_b`, for `f_b ≥ 0`, `M₁ > 0` and `L > 0`,
  `|Σ_{m₁∈P1 M₁}tg(a, m₁, 0)| ≤ W₀L_{L/(2M₁)}(ξ)²`.
* `sum_integral_g0_le`: for `f_b ≥ 0`, `M₁ > 0` and `L > 0`, `Σ_a∫|Σ_{m₁∈P1 M₁}tg(a, m₁, 0)|² dξ ≤ φ(q)W₀²·2πM₁/L`.

The file imports `LinnikCGLNsum.lean`.
-/

import LinnikCGLNsum

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLN0

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum

/-! ### `f̂_b` and `F(m₁, n)` -/

/-- For `f_b ≥ 0`, `|f̂_b(η)| ≤ ∫f_b`. -/
lemma norm_fourier_fC_le {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) (b : (ZMod q)ˣ) (η : ℝ) :
    ‖𝓕 (fC f b) η‖ ≤ ∫ u, f b u := by
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans (le_of_eq ?_)
  congr 1; funext u; simp [fC, abs_of_nonneg (hf b u)]

/-- For `q ≥ 1`, `f_b ≥ 0`, `M₁ > 0` and `m₁ ∈ P1 M₁`, `|F(m₁, n)| ≤ #P2·(2M₂/M₁)Σ_b∫f_b`. -/
lemma norm_Fb_le_int {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ : ℝ}
    (hM₁ : 0 < M₁) (ξ : ℝ) {m₁ : ℤ} (hm₁ : m₁ ∈ P1 M₁) (n : ℤ) :
    ‖Fb f M₂ ξ m₁ n‖ ≤ (P2 M₂).card * (2 * M₂ / M₁) * ∑ b : (ZMod q)ˣ, ∫ u, f b u := by
  refine (norm_Fb_le f M₂ ξ m₁ n).trans ?_
  have hm := (mem_P1 m₁).1 hm₁
  have h1 : ∀ b : (ZMod q)ˣ, ∀ m₂ ∈ P2 M₂,
      ‖(((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖ ≤ 2 * M₂ / M₁ * ∫ u, f b u := by
    intro b m₂ hm₂
    have hm2 := (mem_P2 m₂).1 hm₂
    have hpos : 0 < (m₂ : ℝ) := by linarith [hm2.1, hm2.2]
    have hM₂ : 0 < M₂ := by linarith [hm2.1, hm2.2]
    have habs : abs ((m₂ : ℝ) / |(m₁ : ℝ)|) ≤ 2 * M₂ / M₁ := by
      rw [abs_div, abs_abs, abs_of_pos hpos]
      calc (m₂ : ℝ) / |(m₁ : ℝ)| ≤ (m₂ : ℝ) / M₁ := div_le_div_of_nonneg_left hpos.le hM₁ hm.1.le
        _ ≤ 2 * M₂ / M₁ := div_le_div_of_nonneg_right hm2.2 hM₁.le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul habs (norm_fourier_fC_le hf b _) (norm_nonneg _) (by positivity)
  calc ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, ‖(((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * 𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁)‖
      ≤ ∑ b : (ZMod q)ˣ, ∑ m₂ ∈ P2 M₂, 2 * M₂ / M₁ * ∫ u, f b u :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun m₂ hm₂ => h1 b m₂ hm₂
    _ = (P2 M₂).card * (2 * M₂ / M₁) * ∑ b : (ZMod q)ˣ, ∫ u, f b u := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ### The term `n = 0` -/

/-- For `q ≥ 1`, `f_b ≥ 0`, `M₁ > 0`, `L > 0` and `m₁ ∈ P1 M₁`,
`|tg(a, m₁, 0)| ≤ (L/q)B₄L_{L/(2M₁)}(ξ)²(Σ_h(h, q))#P2·(2M₂/M₁)Σ_b∫f_b`. -/
lemma norm_tg_zero_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ L : ℝ}
    (hM₁ : 0 < M₁) (hL : 0 < L) (ξ : ℝ) (a : (ZMod q)ˣ) {m₁ : ℤ} (hm₁ : m₁ ∈ P1 M₁) :
    ‖tg f M₂ L ξ a m₁ 0‖ ≤ L / q * (B4 * lor (L / (2 * M₁)) ξ ^ 2) * (∑ h : ZMod q, gw h) *
      ((P2 M₂).card * (2 * M₂ / M₁) * ∑ b : (ZMod q)ˣ, ∫ u, f b u) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hm := (mem_P1 m₁).1 hm₁
  have hm0 : (m₁ : ℝ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hm; linarith [hm.1]
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have hB4 := B4_nonneg
  have hlor : lor 1 (L * -(ξ / m₁)) ≤ lor (L / (2 * M₁)) ξ := by
    unfold lor
    refine inv_anti₀ (by positivity) ?_
    have hm2 : (m₁ : ℝ) ^ 2 ≤ (2 * M₁) ^ 2 := by
      rw [sq_le_sq, abs_of_pos (by positivity : (0 : ℝ) < 2 * M₁)]
      exact hm.2
    have e : (L * -(ξ / m₁)) ^ 2 = (L * ξ) ^ 2 / (m₁ : ℝ) ^ 2 := by rw [mul_neg, neg_sq, mul_div_assoc', div_pow]
    have e' : (L / (2 * M₁)) ^ 2 * ξ ^ 2 = (L * ξ) ^ 2 / (2 * M₁) ^ 2 := by ring
    rw [e, e', one_pow, one_mul]
    have : (L * ξ) ^ 2 / (2 * M₁) ^ 2 ≤ (L * ξ) ^ 2 / (m₁ : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hm0))) hm2
    linarith
  have h1 : ‖𝓕 psiC (L * -(ξ / m₁))‖ ≤ B4 * lor (L / (2 * M₁)) ξ ^ 2 := by
    refine (norm_fourier_psiC_le_lor _).trans ?_
    have h0 : 0 ≤ lor 1 (L * -(ξ / m₁)) := (lor_pos' _ _).le
    gcongr
  have h2 := norm_cqg_le (q := q) 0
  have h3 := norm_Fb_le_int hf (M₂ := M₂) hM₁ ξ hm₁ 0
  unfold tg
  simp only [Int.cast_zero, zero_div, zero_sub, zero_mul, mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  gcongr

/-- `W₀ = #P1·(L/q)B₄(Σ_h(h, q))#P2·(2M₂/M₁)Σ_b∫f_b`. -/
def W0 {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₁ M₂ L : ℝ) : ℝ :=
  (P1 M₁).card * (L / q) * B4 * (∑ h : ZMod q, gw h) * ((P2 M₂).card * (2 * M₂ / M₁) * ∑ b : (ZMod q)ˣ, ∫ u, f b u)

/-- **The term `n = 0`, pointwise**: for `q ≥ 1`, `f_b ≥ 0`, `M₁ > 0` and `L > 0`,
`|Σ_{m₁∈P1 M₁}tg(a, m₁, 0)| ≤ W₀L_{L/(2M₁)}(ξ)²`. -/
lemma norm_g0_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ L : ℝ}
    (hM₁ : 0 < M₁) (hL : 0 < L) (ξ : ℝ) (a : (ZMod q)ˣ) :
    ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ≤ W0 f M₁ M₂ L * lor (L / (2 * M₁)) ξ ^ 2 := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun m₁ hm₁ => norm_tg_zero_le hf hM₁ hL ξ a hm₁).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, W0]
  ring

/-- **Their `I`, the term `n = 0`**: for `q ≥ 1`, `f_b ≥ 0`, `M₁ > 0` and `L > 0`,
`Σ_a∫|Σ_{m₁∈P1 M₁}tg(a, m₁, 0)|² dξ ≤ φ(q)W₀²·2πM₁/L`. -/
theorem sum_integral_g0_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ L : ℝ}
    (hM₁ : 0 < M₁) (hL : 0 < L) :
    ∑ a : (ZMod q)ˣ, ∫ ξ, ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 ≤
      q.totient * W0 f M₁ M₂ L ^ 2 * (2 * π * M₁ / L) := by
  have hc : 0 < L / (2 * M₁) := by positivity
  have hint : Integrable fun ξ : ℝ => lor (L / (2 * M₁)) ξ := by
    refine (integrable_lor hc 0).congr (Eventually.of_forall fun ξ => ?_)
    simp only [zero_sub, lor_neg]
  have hval : ∫ ξ, lor (L / (2 * M₁)) ξ = 2 * π * M₁ / L := by
    have h := integral_lor hc 0
    simp only [zero_sub, lor_neg] at h
    rw [h, div_div_eq_mul_div]
    ring
  have hone : ∀ a : (ZMod q)ˣ, ∫ ξ, ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 ≤
      W0 f M₁ M₂ L ^ 2 * (2 * π * M₁ / L) := by
    intro a
    rw [← hval, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => sq_nonneg _) (hint.const_mul _)
      (Eventually.of_forall fun ξ => ?_)
    have h1 := norm_g0_le (M₂ := M₂) hf hM₁ hL ξ a
    have hl0 : 0 ≤ lor (L / (2 * M₁)) ξ := (lor_pos' _ _).le
    have hl1 : lor (L / (2 * M₁)) ξ ^ 4 ≤ lor (L / (2 * M₁)) ξ :=
      pow_le_of_le_one hl0 (lor_le_one _ _) (by norm_num)
    calc ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2 ≤ (W0 f M₁ M₂ L * lor (L / (2 * M₁)) ξ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = W0 f M₁ M₂ L ^ 2 * lor (L / (2 * M₁)) ξ ^ 4 := by ring
      _ ≤ W0 f M₁ M₂ L ^ 2 * lor (L / (2 * M₁)) ξ := mul_le_mul_of_nonneg_left hl1 (sq_nonneg _)
  calc ∑ a : (ZMod q)ˣ, ∫ ξ, ‖∑ m₁ ∈ P1 M₁, tg f M₂ L ξ a m₁ 0‖ ^ 2
      ≤ ∑ a : (ZMod q)ˣ, W0 f M₁ M₂ L ^ 2 * (2 * π * M₁ / L) := Finset.sum_le_sum fun a _ => hone a
    _ = q.totient * W0 f M₁ M₂ L ^ 2 * (2 * π * M₁ / L) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
        ring

end LinnikCGLN0

#print axioms LinnikCGLN0.norm_fourier_fC_le
#print axioms LinnikCGLN0.norm_Fb_le_int
#print axioms LinnikCGLN0.norm_tg_zero_le
#print axioms LinnikCGLN0.norm_g0_le
#print axioms LinnikCGLN0.sum_integral_g0_le
