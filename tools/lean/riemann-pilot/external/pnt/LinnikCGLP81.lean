/-
# Round 693: their Proposition 8.1, by their downward induction (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li prove their Proposition 8.1 from their Lemma 8.2: "We prove the statement via downward induction on
ϵ. The base case ϵ = 100 holds trivially. For the inductive step, we assume (8.1) holds with parameter 3ϵ/2 and aim
to establish it for ϵ." (lines 2543–2545; spaces restored). This file runs that induction on round 691's form of
their Lemma 8.2 and proves round 662's displayed hypothesis `CGLP81`, so the stack's Linnik theorems with the
exponents `9/4` and `226/100` (`linnik_225c_t101`, `linnik_226c_t101`) take Heath-Brown's Theorem 10.1 (`CGLT101`) as
their only hypothesis.

The stack's form.
* The induction runs on `P81 ε`, their (8.1) with an abstract `Λ`: the premise `Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jΛ` with
  `0 ≤ Λ ≤ G(qT)²F`. By round 692, `f̃` keeps it with `(∫ψ̃₀)D_j` and `G/∫ψ̃₀`. `CGLP81`'s `Λ = φ(q)f_{b₀}(u₀)` is a
  value of `f`, not of `f̃`.
* The base case is `ε = 5` (theirs is `ϵ = 100`). For `M₁ < 1/2` or `M₂ < 1/2`, `Jint = 0` (round 689's
  `Jint_eq_zero`). Otherwise, by Cauchy–Schwarz over the pairs `(b, m)`, `(·, q) ≤ q` (round 687's `gJw_le`) and the
  change of variables `u ↦ (m₁u + m₃)/m₂`, `Jint ≤ 4φ(q)²q²(#setJ)²M₂∫Σ_bf_b²`; and `#setJ ≤ 100(2|κ| + 6)M³` for
  `1/2 ≤ M₁, M₂ ≤ M` and `0 ≤ M₃ ≤ M`.
* The step from `3ε/2` to `ε`: round 691's `lemma82_form` at `θ = ε/8`; the induction hypothesis at `f̃`, with the
  support `|A| + 2`, `κ′ = 4|A| + 2`, `G/∫ψ̃₀` and `(∫ψ̃₀)D_j`; `√𝔖√J̃ ≤ (λ𝔖 + J̃/λ)/2` at `λ = φ(q)M²(qT)^{3ε/4}`; and
  `q ≤ φ(q)d(q)` (round 689) with `d(q) ≤ C_δq^δ` (round 525's `card_divisors_le`) at `δ = min(ε/8, 1)`. The powers
  of `qT` are `ε/8 + ε/8 + 3ε/4 = ε`.
* `CGLP81` at `Λ = φ(q)f_{b₀}(u₀)`, which round 692's `Lam_le` bounds by `16π·max(D₄, 1)(qT)²F`, with `Q₀ = 0` and
  `M ≤ (qT)^ϖ ≤ qT`.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `F = Σ_b∫f_b`, `𝔖 = ∫Σ_bf_b²`, `S = setJ(M₁, M₂, M₃, κ)` and `f̃_b`
round 685's `ftil`.
* `P81 ε` (a definition): for every `A`, `κ`, `G` and `D : ℕ → ℝ` there is `C ≥ 0` such that, for `T ≥ 1`, `M ≤ qT`,
  smooth `f_b ≥ 0` that are `0` for `|u| > A`, `0 ≤ Λ ≤ G(qT)²F`, the premise for every `j` and every `ξ ≠ 0`,
  `0 < M₁ ≤ M`, `0 < M₂ ≤ M` and `0 ≤ M₃ ≤ M`, `Jint ≤ C(qT)^ε(φ(q)M⁶F² + φ(q)²M⁴𝔖)`.
* `P81_mono`: for `ε₁ ≤ ε₂`, `P81 ε₁` gives `P81 ε₂`.
* `integrable_comp_affine`, `integral_sq_affine`: for continuous `g` that is `0` for `|u| > A`, `c ≠ 0` and `e > 0`,
  `u ↦ g((cu + d)/e)` is integrable; and for `c ≠ 0` and `e > 0`, `∫g((cu + d)/e)² du = (e/|c|)∫g²`.
* `card_Icc_ceil_abs_le`, `card_setJ_le`: `#[−⌈x⌉, ⌈x⌉] ≤ 2|x| + 3`, and
  `#S ≤ (4|M₁| + 3)(4|M₂| + 3)(2|κM₃| + 3)`.
* `Jint_le_trivial`: for smooth `f_b` that are `0` for `|u| > A` and `M₁, M₂ ≥ 1/2`, `Jint ≤ 4φ(q)²q²(#S)²M₂𝔖`.
* `P81_base`: `P81 5`.
* `sqrt_mul_sqrt_le`, `step_combine`, `integral_psi0_pos`, `integral_sum_ftil_sq_le`: AM-GM for square roots, the
  step's count in real variables, `∫ψ̃₀ > 0`, and `∫Σ_bf̃_b² ≤ (∫ψ̃₀)²𝔖` (each docstring lists its hypotheses).
* `P81_step`, `P81_pow`, `P81_all`: for `ε > 0`, `P81(3ε/2)` gives `P81 ε`; `P81(5(2/3)ⁿ)` for every `n`; and
  `P81 ε` for every `ε > 0`.
* `cglp81`: `CGLP81`.
* `cgls3_t101`, `prop31_t101`, `linnik_225c_t101`, `linnik_226c_t101`: from `CGLT101`, their Propositions 11.1 and
  3.1 at one point per character (`CGLS3`, `CGLProp31`), and Linnik's theorem with the exponents `9/4` and `226/100`:
  there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
  `p ≤ Kq^{9/4}`, respectively `p ≤ Kq^{226/100}`.

The file imports `LinnikCGLFtilP.lean`.
-/

import LinnikCGLFtilP

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLP81

open LinnikCGLRt LinnikCGLMom LinnikCGLJ LinnikCGLG LinnikCGLFtil LinnikCGLJtil LinnikCGLTail LinnikCGLConst
  LinnikCGLForm LinnikCGLFtilP LinnikCGLCov

/-! ### The statement -/

/-- **Their (8.1) at the exponent `ε`, with an abstract `Λ`**: for every support bound `A`, constant `κ`, `G` and
decay constants `D j` there is `C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`, `M ≤ qT`, smooth `f_b ≥ 0` that are `0` for
`|u| > A`, `0 ≤ Λ ≤ G(qT)²F` and `Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jΛ` for every `j` and every `ξ ≠ 0`, every
`0 < M₁ ≤ M`, `0 < M₂ ≤ M` and `0 ≤ M₃ ≤ M` has `Jint ≤ C(qT)^ε(φ(q)M⁶F² + φ(q)²M⁴∫Σ_bf_b²)`, with `F = Σ_b∫f_b`. -/
def P81 (ε : ℝ) : Prop :=
  ∀ (A κ G : ℝ) (D : ℕ → ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) [NeZero q] (T M Λ : ℝ) (f : (ZMod q)ˣ → ℝ → ℝ), 1 ≤ T → M ≤ q * T →
      (∀ b, ContDiff ℝ ∞ (f b)) → (∀ b u, 0 ≤ f b u) → (∀ b u, A < |u| → f b u = 0) → 0 ≤ Λ →
      Λ ≤ G * ((q : ℝ) * T) ^ 2 * ∑ b, ∫ u, f b u →
      (∀ (j : ℕ) (ξ : ℝ), ξ ≠ 0 → ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D j * (T / |ξ|) ^ j * Λ) →
      ∀ M₁ M₂ M₃ : ℝ, 0 < M₁ → M₁ ≤ M → 0 < M₂ → M₂ ≤ M → 0 ≤ M₃ → M₃ ≤ M →
        Jint f M₁ M₂ M₃ κ ≤ C * ((q : ℝ) * T) ^ ε * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 +
          (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2)

/-- **`P81` is monotone in `ε`**: for `ε₁ ≤ ε₂`, `P81 ε₁` gives `P81 ε₂`. -/
lemma P81_mono {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) (h1 : P81 ε₁) : P81 ε₂ := by
  intro A κ G D
  obtain ⟨C, hC, hb⟩ := h1 A κ G D
  refine ⟨C, hC, ?_⟩
  intro q _ T M Λ f hT hMQ hfs hf hA hΛ hΛF hdec M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  refine (hb q T M Λ f hT hMQ hfs hf hA hΛ hΛF hdec M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M).trans ?_
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ1 : (1 : ℝ) ≤ q * T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hS : 0 ≤ ∫ u, ∑ b, f b u ^ 2 := integral_nonneg fun u => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hX : 0 ≤ (q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 + (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2 :=
    by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 h) hC) hX

/-! ### The base case -/

/-- For continuous `g` that is `0` for `|u| > A`, `c ≠ 0` and `e > 0`, `u ↦ g((cu + d)/e)` is integrable. -/
lemma integrable_comp_affine {g : ℝ → ℝ} (hg : Continuous g) {A : ℝ} (h0 : ∀ u, A < |u| → g u = 0) {c d e : ℝ}
    (hc : c ≠ 0) (he : 0 < e) : Integrable (fun u => g ((c * u + d) / e)) := by
  refine integrable_of_vanish (hg.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _))
    (A := (|A| * e + |d|) / |c|) fun u hu => h0 _ ?_
  rw [div_lt_iff₀ (abs_pos.mpr hc)] at hu
  have t1 : |c * u| - |d| ≤ |c * u + d| := by
    have := abs_sub_abs_le_abs_sub (c * u) (-d)
    rwa [abs_neg, sub_neg_eq_add] at this
  rw [abs_mul] at t1
  rw [abs_div, abs_of_pos he, lt_div_iff₀ he]
  have : |A| * e < |c * u + d| := by nlinarith [abs_nonneg u, abs_nonneg c]
  linarith [le_abs_self A, mul_le_mul_of_nonneg_right (le_abs_self A) he.le]

/-- `∫g((cu + d)/e)² du = (e/|c|)∫g²` for `c ≠ 0` and `e > 0`. -/
lemma integral_sq_affine (g : ℝ → ℝ) {c d e : ℝ} (hc : c ≠ 0) (he : 0 < e) :
    ∫ u, g ((c * u + d) / e) ^ 2 = e / |c| * ∫ v, g v ^ 2 := by
  have h1 : (fun u => g ((c * u + d) / e) ^ 2) = fun u => (fun v => g (c / e * v) ^ 2) (u + d / c) := by
    ext u
    congr 2
    field_simp
  rw [h1, integral_add_right_eq_self (fun v => g (c / e * v) ^ 2) (d / c),
    Measure.integral_comp_mul_left (fun v => g v ^ 2) (c / e), smul_eq_mul, inv_div, abs_div, abs_of_pos he]

/-- For every real `x`, the integers in `[−⌈x⌉, ⌈x⌉]` number at most `2|x| + 3`. -/
lemma card_Icc_ceil_abs_le (x : ℝ) : ((Finset.Icc (-⌈x⌉) ⌈x⌉).card : ℝ) ≤ 2 * |x| + 3 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact card_Icc_ceil_le hx
  · have h0 : ⌈x⌉ ≤ 0 := Int.ceil_le.mpr (by push_cast; linarith)
    have hsub : Finset.Icc (-⌈x⌉) ⌈x⌉ ⊆ {0} := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_singleton]
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    have h1 : ((Finset.Icc (-⌈x⌉) ⌈x⌉).card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith [abs_nonneg x]

/-- `#setJ(M₁, M₂, M₃, κ) ≤ (4|M₁| + 3)(4|M₂| + 3)(2|κM₃| + 3)`. -/
lemma card_setJ_le (M₁ M₂ M₃ κ : ℝ) :
    ((setJ M₁ M₂ M₃ κ).card : ℝ) ≤ (4 * |M₁| + 3) * (4 * |M₂| + 3) * (2 * |κ * M₃| + 3) := by
  unfold setJ
  have h := Finset.card_filter_le ((Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉) ×ˢ (Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉) ×ˢ
      (Finset.Icc (-⌈κ * M₃⌉) ⌈κ * M₃⌉)) fun m =>
    M₁ < |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ M₂ < (m.2.1 : ℝ) ∧ (m.2.1 : ℝ) ≤ 2 * M₂ ∧ |(m.2.2 : ℝ)| ≤ κ * M₃
  rw [Finset.card_product, Finset.card_product] at h
  have h' : ((Finset.filter (fun m : ℤ × ℤ × ℤ => M₁ < |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ M₂ < (m.2.1 : ℝ) ∧
      (m.2.1 : ℝ) ≤ 2 * M₂ ∧ |(m.2.2 : ℝ)| ≤ κ * M₃) ((Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉) ×ˢ
        (Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉) ×ˢ (Finset.Icc (-⌈κ * M₃⌉) ⌈κ * M₃⌉))).card : ℝ) ≤
      ((Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉).card : ℝ) * ((Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉).card : ℝ) *
        ((Finset.Icc (-⌈κ * M₃⌉) ⌈κ * M₃⌉).card : ℝ) := by
    rw [mul_assoc]; exact_mod_cast h
  have c1 := card_Icc_ceil_abs_le (2 * M₁)
  have c2 := card_Icc_ceil_abs_le (2 * M₂)
  have c3 := card_Icc_ceil_abs_le (κ * M₃)
  rw [abs_mul, abs_two] at c1 c2
  refine h'.trans ?_
  have p1 : (0 : ℝ) ≤ ((Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉).card : ℝ) := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ ((Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉).card : ℝ) := Nat.cast_nonneg _
  have p3 : (0 : ℝ) ≤ ((Finset.Icc (-⌈κ * M₃⌉) ⌈κ * M₃⌉).card : ℝ) := Nat.cast_nonneg _
  calc ((Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉).card : ℝ) * ((Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉).card : ℝ) *
        ((Finset.Icc (-⌈κ * M₃⌉) ⌈κ * M₃⌉).card : ℝ)
      ≤ (2 * (2 * |M₁|) + 3) * (2 * (2 * |M₂|) + 3) * (2 * |κ * M₃| + 3) := by gcongr
    _ = (4 * |M₁| + 3) * (4 * |M₂| + 3) * (2 * |κ * M₃| + 3) := by ring

/-- **The trivial bound**: for `q ≥ 1`, smooth `f_b` that are `0` for `|u| > A`, `M₁, M₂ ≥ 1/2` and every `M₃`
and `κ`, `Jint(f, M₁, M₂, M₃, κ) ≤ 4φ(q)²q²(#setJ)²M₂∫Σ_bf_b²`. -/
theorem Jint_le_trivial {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ M₃ κ : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) :
    Jint f M₁ M₂ M₃ κ ≤ 4 * (q.totient : ℝ) ^ 2 * (q : ℝ) ^ 2 * ((setJ M₁ M₂ M₃ κ).card : ℝ) ^ 2 * M₂ *
      ∫ u, ∑ b, f b u ^ 2 := by
  set S := setJ M₁ M₂ M₃ κ with hS
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hcard : ((Finset.univ : Finset (ZMod q)ˣ).card : ℝ) = q.totient := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient]
  -- each `m ∈ S` has `m₁ ≠ 0`, `m₂ > 0` and `m₂/|m₁| ≤ 4M₂`
  have hm : ∀ m ∈ S, (m.1 : ℝ) ≠ 0 ∧ 0 < (m.2.1 : ℝ) ∧ (m.2.1 : ℝ) / |(m.1 : ℝ)| ≤ 4 * M₂ := by
    intro m hmS
    obtain ⟨h1, -, h3, h4, -⟩ := (mem_setJ m).1 hmS
    have hm1 : 1 / 2 < |(m.1 : ℝ)| := by linarith
    refine ⟨fun h => by rw [h, abs_zero] at hm1; linarith, by linarith, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- the terms are integrable
  have hint : ∀ b, ∀ m ∈ S, Integrable fun u => f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 := fun b m hmS =>
    integrable_comp_affine (g := fun v => f b v ^ 2) ((hfs b).continuous.pow 2)
      (fun u hu => by show f b u ^ 2 = 0; rw [hA b u hu]; ring) (hm m hmS).1 (hm m hmS).2.1
  -- pointwise, by Cauchy–Schwarz over the pairs `(b, m)` and `(·, q) ≤ q`
  have hpt : ∀ u, ∑ a : (ZMod q)ˣ, gJ f S a u ^ 2 ≤
      (q.totient : ℝ) * ((q.totient : ℝ) * S.card * q ^ 2) *
        ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 := by
    intro u
    have e2 : ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 =
        ∑ p ∈ (Finset.univ : Finset (ZMod q)ˣ) ×ˢ S, f p.1 ((p.2.1 * u + p.2.2.2) / p.2.2.1) ^ 2 := by
      rw [Finset.sum_product]
    have hone : ∀ a : (ZMod q)ˣ, gJ f S a u ^ 2 ≤
        (q.totient : ℝ) * S.card * q ^ 2 * ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 := by
      intro a
      have e1 : gJ f S a u = ∑ p ∈ (Finset.univ : Finset (ZMod q)ˣ) ×ˢ S,
          f p.1 ((p.2.1 * u + p.2.2.2) / p.2.2.1) * gJw a p.1 p.2 := by
        unfold gJ
        rw [Finset.sum_product]
      rw [e1, e2]
      calc (∑ p ∈ (Finset.univ : Finset (ZMod q)ˣ) ×ˢ S, f p.1 ((p.2.1 * u + p.2.2.2) / p.2.2.1) * gJw a p.1 p.2) ^ 2
          ≤ (((Finset.univ : Finset (ZMod q)ˣ) ×ˢ S).card : ℝ) * ∑ p ∈ (Finset.univ : Finset (ZMod q)ˣ) ×ˢ S,
              (f p.1 ((p.2.1 * u + p.2.2.2) / p.2.2.1) * gJw a p.1 p.2) ^ 2 := sq_sum_le_card_mul_sum_sq
        _ ≤ (((Finset.univ : Finset (ZMod q)ˣ) ×ˢ S).card : ℝ) * ∑ p ∈ (Finset.univ : Finset (ZMod q)ˣ) ×ˢ S,
              f p.1 ((p.2.1 * u + p.2.2.2) / p.2.2.1) ^ 2 * (q : ℝ) ^ 2 := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) (Nat.cast_nonneg _)
            have hw := gJw_le a p.1 p.2
            have hw0 := gJw_nonneg a p.1 p.2
            rw [mul_pow]
            gcongr
        _ = (q.totient : ℝ) * S.card * q ^ 2 * ∑ p ∈ (Finset.univ : Finset (ZMod q)ˣ) ×ˢ S,
              f p.1 ((p.2.1 * u + p.2.2.2) / p.2.2.1) ^ 2 := by
            rw [Finset.card_product, Nat.cast_mul, hcard, ← Finset.sum_mul]
            ring
    calc ∑ a : (ZMod q)ˣ, gJ f S a u ^ 2
        ≤ ∑ _a : (ZMod q)ˣ, (q.totient : ℝ) * S.card * q ^ 2 * ∑ b : (ZMod q)ˣ, ∑ m ∈ S,
            f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 := Finset.sum_le_sum fun a _ => hone a
      _ = (q.totient : ℝ) * ((q.totient : ℝ) * S.card * q ^ 2) *
            ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
          ring
  -- integrated, with the change of variables
  have hsum_int : Integrable fun u => ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 :=
    integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun m hmS => hint b m hmS
  have hval : ∫ u, ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 ≤
      S.card * (4 * M₂) * ∫ u, ∑ b, f b u ^ 2 := by
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun m hmS => hint b m hmS]
    have hb : ∀ b : (ZMod q)ˣ, ∫ u, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 ≤
        S.card * (4 * M₂) * ∫ u, f b u ^ 2 := by
      intro b
      rw [integral_finsetSum _ fun m hmS => hint b m hmS]
      have hb0 : 0 ≤ ∫ u, f b u ^ 2 := integral_nonneg fun u => sq_nonneg _
      calc ∑ m ∈ S, ∫ u, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2
          = ∑ m ∈ S, (m.2.1 : ℝ) / |(m.1 : ℝ)| * ∫ v, f b v ^ 2 :=
            Finset.sum_congr rfl fun m hmS => integral_sq_affine (f b) (hm m hmS).1 (hm m hmS).2.1
        _ ≤ ∑ _m ∈ S, 4 * M₂ * ∫ v, f b v ^ 2 :=
            Finset.sum_le_sum fun m hmS => mul_le_mul_of_nonneg_right (hm m hmS).2.2 hb0
        _ = S.card * (4 * M₂) * ∫ u, f b u ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hcont : ∀ b : (ZMod q)ˣ, Integrable fun u => f b u ^ 2 := fun b =>
      integrable_of_vanish (g := fun v => f b v ^ 2) ((hfs b).continuous.pow 2)
        (fun u hu => by show f b u ^ 2 = 0; rw [hA b u hu]; ring)
    rw [integral_finsetSum _ fun b _ => hcont b, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hb b
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  calc Jint f M₁ M₂ M₃ κ = ∫ u, ∑ a : (ZMod q)ˣ, gJ f S a u ^ 2 := rfl
    _ ≤ ∫ u, (q.totient : ℝ) * ((q.totient : ℝ) * S.card * q ^ 2) *
          ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => Finset.sum_nonneg fun a _ => sq_nonneg _)
          (hsum_int.const_mul _) (Eventually.of_forall hpt)
    _ = (q.totient : ℝ) * ((q.totient : ℝ) * S.card * q ^ 2) *
          ∫ u, ∑ b : (ZMod q)ˣ, ∑ m ∈ S, f b ((m.1 * u + m.2.2) / m.2.1) ^ 2 :=
        integral_const_mul _ _
    _ ≤ (q.totient : ℝ) * ((q.totient : ℝ) * S.card * q ^ 2) * (S.card * (4 * M₂) * ∫ u, ∑ b, f b u ^ 2) :=
        mul_le_mul_of_nonneg_left hval (by positivity)
    _ = 4 * (q.totient : ℝ) ^ 2 * (q : ℝ) ^ 2 * (S.card : ℝ) ^ 2 * M₂ * ∫ u, ∑ b, f b u ^ 2 := by ring

/-- **The base case**: `P81 5`, with `C = 4(100(2|κ| + 6))²`. -/
theorem P81_base : P81 5 := by
  intro A κ G D
  refine ⟨4 * (100 * (2 * |κ| + 6)) ^ 2, by positivity, ?_⟩
  intro q _ T M Λ f hT hMQ hfs hf hA hΛ hΛF hdec M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hT0 : 0 < T := by linarith
  have hQ1 : (1 : ℝ) ≤ q * T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hS0 : 0 ≤ ∫ u, ∑ b, f b u ^ 2 := integral_nonneg fun u => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hX0 : 0 ≤ (q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 := by positivity
  have h5 : ((q : ℝ) * T) ^ (5 : ℝ) = ((q : ℝ) * T) ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h5]
  by_cases hsmall : M₁ < 1 / 2 ∨ M₂ < 1 / 2
  · rw [Jint_eq_zero f M₃ κ hsmall]
    positivity
  push Not at hsmall
  obtain ⟨hM₁', hM₂'⟩ := hsmall
  have hM : 1 / 2 ≤ M := hM₁'.trans hM₁M
  have hM0 : 0 ≤ M := by linarith
  have hκ0 : 0 ≤ |κ| := abs_nonneg κ
  -- the count: `#setJ ≤ 100(2|κ| + 6)M³`
  have hcard : ((setJ M₁ M₂ M₃ κ).card : ℝ) ≤ 100 * (2 * |κ| + 6) * M ^ 3 := by
    have h := card_setJ_le M₁ M₂ M₃ κ
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ M₁), abs_of_nonneg (by linarith : (0 : ℝ) ≤ M₂), abs_mul,
      abs_of_nonneg hM₃] at h
    have h1 : 4 * M₁ + 3 ≤ 10 * M := by linarith
    have h2 : 4 * M₂ + 3 ≤ 10 * M := by linarith
    have h3 : 2 * (|κ| * M₃) + 3 ≤ (2 * |κ| + 6) * M := by nlinarith
    calc ((setJ M₁ M₂ M₃ κ).card : ℝ) ≤ (4 * M₁ + 3) * (4 * M₂ + 3) * (2 * (|κ| * M₃) + 3) := h
      _ ≤ (10 * M) * (10 * M) * ((2 * |κ| + 6) * M) := by
          have a1 : 0 ≤ 4 * M₁ + 3 := by linarith
          have a2 : 0 ≤ 4 * M₂ + 3 := by linarith
          have a3 : 0 ≤ 2 * (|κ| * M₃) + 3 := by positivity
          have a4 : 0 ≤ 10 * M := by linarith
          exact mul_le_mul (mul_le_mul h1 h2 a2 a4) h3 a3 (by positivity)
      _ = 100 * (2 * |κ| + 6) * M ^ 3 := by ring
  have hJ := Jint_le_trivial (q := q) hfs hA hM₁' hM₂' (M₃ := M₃) (κ := κ)
  have hqQ : (q : ℝ) ≤ q * T := le_mul_of_one_le_right (by linarith) hT
  have hq2 : (q : ℝ) ^ 2 ≤ ((q : ℝ) * T) ^ 2 := pow_le_pow_left₀ (by linarith) hqQ 2
  have hM3 : M ^ 3 ≤ ((q : ℝ) * T) ^ 3 := pow_le_pow_left₀ hM0 hMQ 3
  have hc0 : 0 ≤ 100 * (2 * |κ| + 6) := by positivity
  have hcard0 : (0 : ℝ) ≤ (setJ M₁ M₂ M₃ κ).card := Nat.cast_nonneg _
  calc Jint f M₁ M₂ M₃ κ ≤ 4 * (q.totient : ℝ) ^ 2 * (q : ℝ) ^ 2 * ((setJ M₁ M₂ M₃ κ).card : ℝ) ^ 2 * M₂ *
        ∫ u, ∑ b, f b u ^ 2 := hJ
    _ ≤ 4 * (q.totient : ℝ) ^ 2 * (q : ℝ) ^ 2 * (100 * (2 * |κ| + 6) * M ^ 3) ^ 2 * M * ∫ u, ∑ b, f b u ^ 2 := by
        gcongr
    _ = 4 * (100 * (2 * |κ| + 6)) ^ 2 * ((q : ℝ) ^ 2 * M ^ 3) * ((q.totient : ℝ) ^ 2 * M ^ 4 *
          ∫ u, ∑ b, f b u ^ 2) := by ring
    _ ≤ 4 * (100 * (2 * |κ| + 6)) ^ 2 * (((q : ℝ) * T) ^ 2 * ((q : ℝ) * T) ^ 3) * ((q.totient : ℝ) ^ 2 * M ^ 4 *
          ∫ u, ∑ b, f b u ^ 2) := by gcongr
    _ = 4 * (100 * (2 * |κ| + 6)) ^ 2 * ((q : ℝ) * T) ^ 5 * ((q.totient : ℝ) ^ 2 * M ^ 4 *
          ∫ u, ∑ b, f b u ^ 2) := by ring
    _ ≤ 4 * (100 * (2 * |κ| + 6)) ^ 2 * ((q : ℝ) * T) ^ 5 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 +
          (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2) := by gcongr; linarith

/-! ### The step -/

/-- **AM-GM for square roots**: for `a, b ≥ 0` and `l > 0`, `√a√b ≤ (la + b/l)/2`. -/
lemma sqrt_mul_sqrt_le {a b l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < l) : √a * √b ≤ (l * a + b / l) / 2 := by
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  have key : 0 ≤ (l * √a - √b) ^ 2 := sq_nonneg _
  have h1 : 2 * l * (√a * √b) ≤ l ^ 2 * a + b := by nlinarith
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_nonneg]
  have e : l * a + b / l - √a * √b * 2 = (l ^ 2 * a + b - 2 * l * (√a * √b)) / l := by
    field_simp
  rw [e]
  exact div_nonneg (by linarith) hl.le

/-- **The count of the step**, in real variables: from `J ≤ C₁Q_a(P + qM²√𝔖√J̃)`, `J̃ ≤ C₂Q_b²I²(P + W)` with
`W = φ²M⁴𝔖`, `q ≤ dφ`, `d ≤ C_dQ_a`, `Q_a, Q_b ≥ 1`, `φ, M > 0` and `C₁, C₂, q, d, 𝔖, J̃, P ≥ 0`,
`J ≤ (C₁ + C₁C_d(1 + C₂I²)/2)Q_aQ_aQ_b(P + W)`. -/
lemma step_combine {J C₁ C₂ I Cd Qa Qb q φ d M S Jt P W : ℝ}
    (hJ : J ≤ C₁ * Qa * (P + q * M ^ 2 * √S * √Jt)) (hJt : Jt ≤ C₂ * Qb ^ 2 * (I ^ 2 * (P + W)))
    (hW : W = φ ^ 2 * M ^ 4 * S) (hqd : q ≤ d * φ) (hd : d ≤ Cd * Qa) (hQa : 1 ≤ Qa) (hQb : 1 ≤ Qb)
    (hφ : 0 < φ) (hM : 0 < M) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hq : 0 ≤ q) (hd0 : 0 ≤ d)
    (hS : 0 ≤ S) (hJt0 : 0 ≤ Jt) (hP : 0 ≤ P) :
    J ≤ (C₁ + C₁ * Cd * (1 + C₂ * I ^ 2) / 2) * (Qa * Qa * Qb) * (P + W) := by
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hI2 : 0 ≤ I ^ 2 := sq_nonneg I
  set l : ℝ := φ * M ^ 2 * Qb with hl
  have hl0 : 0 < l := by positivity
  have hAM := sqrt_mul_sqrt_le hS hJt0 hl0
  -- the two halves
  have t1 : q * M ^ 2 * (l * S) ≤ d * Qb * W := by
    rw [hl, hW]
    have : q * M ^ 2 * (φ * M ^ 2 * Qb * S) = q * (φ * M ^ 4 * Qb * S) := by ring
    rw [this]
    calc q * (φ * M ^ 4 * Qb * S) ≤ (d * φ) * (φ * M ^ 4 * Qb * S) :=
          mul_le_mul_of_nonneg_right hqd (by positivity)
      _ = d * Qb * (φ ^ 2 * M ^ 4 * S) := by ring
  have t2 : q * M ^ 2 * (Jt / l) ≤ d * Qb * (C₂ * I ^ 2 * (P + W)) := by
    have e : q * M ^ 2 * (Jt / l) = q * Jt / (φ * Qb) := by
      rw [hl]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    calc q * Jt ≤ (d * φ) * (C₂ * Qb ^ 2 * (I ^ 2 * (P + W))) :=
          mul_le_mul hqd hJt hJt0 (by positivity)
      _ = d * Qb * (C₂ * I ^ 2 * (P + W)) * (φ * Qb) := by ring
  have hmid : q * M ^ 2 * √S * √Jt ≤ d * Qb * ((1 + C₂ * I ^ 2) * (P + W)) / 2 := by
    calc q * M ^ 2 * √S * √Jt = q * M ^ 2 * (√S * √Jt) := by ring
      _ ≤ q * M ^ 2 * ((l * S + Jt / l) / 2) := mul_le_mul_of_nonneg_left hAM (by positivity)
      _ = (q * M ^ 2 * (l * S) + q * M ^ 2 * (Jt / l)) / 2 := by ring
      _ ≤ (d * Qb * W + d * Qb * (C₂ * I ^ 2 * (P + W))) / 2 := by gcongr
      _ ≤ d * Qb * ((1 + C₂ * I ^ 2) * (P + W)) / 2 := by
          have : d * Qb * W ≤ d * Qb * (P + W) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          nlinarith
  have hQ : Qa ≤ Qa * Qa * Qb := by
    have : 1 ≤ Qa * Qb := one_le_mul_of_one_le_of_one_le hQa hQb
    nlinarith
  have hdQ : d * Qb ≤ Cd * (Qa * Qb) := by
    calc d * Qb ≤ Cd * Qa * Qb := mul_le_mul_of_nonneg_right hd (by linarith)
      _ = Cd * (Qa * Qb) := by ring
  calc J ≤ C₁ * Qa * (P + q * M ^ 2 * √S * √Jt) := hJ
    _ ≤ C₁ * Qa * (P + d * Qb * ((1 + C₂ * I ^ 2) * (P + W)) / 2) := by gcongr
    _ ≤ C₁ * Qa * ((P + W) + Cd * (Qa * Qb) * ((1 + C₂ * I ^ 2) * (P + W)) / 2) := by
        gcongr
        · linarith
    _ = C₁ * Qa * (P + W) + C₁ * Cd * (1 + C₂ * I ^ 2) / 2 * (Qa * Qa * Qb) * (P + W) := by ring
    _ ≤ C₁ * (Qa * Qa * Qb) * (P + W) + C₁ * Cd * (1 + C₂ * I ^ 2) / 2 * (Qa * Qa * Qb) * (P + W) := by
        gcongr
    _ = (C₁ + C₁ * Cd * (1 + C₂ * I ^ 2) / 2) * (Qa * Qa * Qb) * (P + W) := by ring

/-- `∫ψ̃₀ > 0`. -/
lemma integral_psi0_pos : 0 < ∫ t, psi0 t := psiBump.integral_pos

/-- **The `L²` comparison for the sums**: for `q ≥ 1`, smooth `f_b ≥ 0` that are `0` for `|u| > A` and `T ≥ 1`,
`∫Σ_bf̃_b² ≤ (∫ψ̃₀)²∫Σ_bf_b²`. -/
lemma integral_sum_ftil_sq_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    (hf : ∀ b u, 0 ≤ f b u) {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {T : ℝ} (hT : 1 ≤ T) :
    ∫ u, ∑ b, ftil f T b u ^ 2 ≤ (∫ t, psi0 t) ^ 2 * ∫ u, ∑ b, f b u ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hfi : ∀ b, Integrable (f b) := fun b => integrable_of_vanish (hfs b).continuous (hA b)
  have hi1 : ∀ b, Integrable fun u => ftil f T b u ^ 2 := fun b =>
    integrable_of_vanish (g := fun u => ftil f T b u ^ 2) ((contDiff_ftil hT0 b (hfi b)).continuous.pow 2)
      (A := |A| + 2) (fun u hu => by show ftil f T b u ^ 2 = 0; rw [ftil_vanish hA hT b u hu]; ring)
  have hi2 : ∀ b, Integrable fun u => f b u ^ 2 := fun b =>
    integrable_of_vanish (g := fun u => f b u ^ 2) ((hfs b).continuous.pow 2)
      (fun u hu => by show f b u ^ 2 = 0; rw [hA b u hu]; ring)
  rw [integral_finsetSum _ fun b _ => hi1 b, integral_finsetSum _ fun b _ => hi2 b, Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => integral_ftil_sq_le hT0 hf b (hfs b).continuous (hi2 b)

/-- **The step**: for `ε > 0`, `P81 (3ε/2)` gives `P81 ε`. -/
theorem P81_step {ε : ℝ} (hε : 0 < ε) (h : P81 (3 * ε / 2)) : P81 ε := by
  intro A κ G D
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ t, psi0 t := ⟨_, rfl⟩
  have hI : 0 < I := by rw [hIdef]; exact integral_psi0_pos
  obtain ⟨C₁, hC₁, h82⟩ := lemma82_form (θ := ε / 8) (by positivity) κ G D
  obtain ⟨C₂, hC₂, hind⟩ := h (|A| + 2) (4 * |A| + 2) (G / I) (fun j => I * D j)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (ε / 8) 1 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
  have hδε : δ ≤ ε / 8 := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨Cd, hCddef⟩ : ∃ Cd : ℝ, Cd = LinnikPower.Cdiv δ := ⟨_, rfl⟩
  have hCd : 1 ≤ Cd := by rw [hCddef]; exact LinnikPower.one_le_Cdiv hδ hδ1
  refine ⟨C₁ + C₁ * Cd * (1 + C₂ * I ^ 2) / 2, by positivity, ?_⟩
  intro q _ T M Λ f hT hMQ hfs hf hA hΛ hΛF hdec M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hT0 : 0 < T := by linarith
  have hQ1 : (1 : ℝ) ≤ q * T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hQ0 : (0 : ℝ) < q * T := by linarith
  have hS0 : 0 ≤ ∫ u, ∑ b, f b u ^ 2 := integral_nonneg fun u => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hφ1 : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  by_cases hsmall : M₁ < 1 / 2 ∨ M₂ < 1 / 2
  · rw [Jint_eq_zero f M₃ κ hsmall]
    positivity
  push Not at hsmall
  have hM : 1 / 2 ≤ M := hsmall.1.trans hM₁M
  have hM0 : 0 < M := by linarith
  -- their Lemma 8.2 at `θ = ε/8`
  have h1 := h82 q T M A Λ f hT hMQ hfs hf hA hΛ hΛF hdec M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  -- the induction hypothesis at `f̃`
  have hfi : ∀ b, Integrable (f b) := fun b => integrable_of_vanish (hfs b).continuous (hA b)
  have hF' : ∑ b, ∫ u, ftil f T b u = I * ∑ b, ∫ u, f b u := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [integral_ftil hT0 b (hfi b), hIdef]
  have hΛF' : Λ ≤ G / I * ((q : ℝ) * T) ^ 2 * ∑ b, ∫ u, ftil f T b u := by
    rw [hF']
    have e : G / I * ((q : ℝ) * T) ^ 2 * (I * ∑ b, ∫ u, f b u) = G * ((q : ℝ) * T) ^ 2 * ∑ b, ∫ u, f b u := by
      field_simp
    rw [e]
    exact hΛF
  have hdec' : ∀ (j : ℕ) (ξ : ℝ), ξ ≠ 0 →
      ∑ b, ‖𝓕 (fC (ftil f T) b) ξ‖ ≤ (fun j => I * D j) j * (T / |ξ|) ^ j * Λ := fun j ξ hξ => by
    have h' := decay_ftil hT0 hfi (hdec j ξ hξ)
    rw [← hIdef] at h'
    exact h'
  have hJt := hind q T M Λ (ftil f T) hT hMQ (fun b => contDiff_ftil hT0 b (hfi b)) (ftil_nonneg hT0.le hf)
    (fun b u hu => ftil_vanish hA hT b u hu) hΛ hΛF' hdec' M₂ M₂ M₂ hM₂ hM₂M hM₂ hM₂M hM₂.le hM₂M
  have hS' := integral_sum_ftil_sq_le hfs hf hA hT
  rw [← hIdef] at hS'
  rw [hF'] at hJt
  -- the powers of `qT`
  obtain ⟨Qa, hQadef⟩ : ∃ Qa : ℝ, Qa = ((q : ℝ) * T) ^ (ε / 8) := ⟨_, rfl⟩
  obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = ((q : ℝ) * T) ^ (3 * ε / 4) := ⟨_, rfl⟩
  have hQa : 1 ≤ Qa := by rw [hQadef]; exact Real.one_le_rpow hQ1 (by positivity)
  have hQb : 1 ≤ Qb := by rw [hQbdef]; exact Real.one_le_rpow hQ1 (by positivity)
  have hQb2 : ((q : ℝ) * T) ^ (3 * ε / 2) = Qb ^ 2 := by
    rw [hQbdef, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    push_cast
    ring
  have hQe : Qa * Qa * Qb = ((q : ℝ) * T) ^ ε := by
    rw [hQadef, hQbdef, ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    congr 1
    ring
  -- the bound for `f̃`, in the form of `step_combine`
  have hJt2 : Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2) ≤ C₂ * Qb ^ 2 * (I ^ 2 *
      ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 + (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2)) := by
    refine hJt.trans ?_
    rw [hQb2]
    have hφ0 : (0 : ℝ) ≤ q.totient := by linarith
    have e : (q.totient : ℝ) * M ^ 6 * (I * ∑ b, ∫ u, f b u) ^ 2 =
        I ^ 2 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2) := by ring
    rw [e]
    have h2 : (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, ftil f T b u ^ 2 ≤
        I ^ 2 * ((q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2) := by
      calc (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, ftil f T b u ^ 2
          ≤ (q.totient : ℝ) ^ 2 * M ^ 4 * (I ^ 2 * ∫ u, ∑ b, f b u ^ 2) :=
            mul_le_mul_of_nonneg_left hS' (by positivity)
        _ = I ^ 2 * ((q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2) := by ring
    have hC₂Qb : 0 ≤ C₂ * Qb ^ 2 := by positivity
    calc C₂ * Qb ^ 2 * (I ^ 2 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2) +
          (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, ftil f T b u ^ 2)
        ≤ C₂ * Qb ^ 2 * (I ^ 2 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2) +
          I ^ 2 * ((q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2)) := by gcongr
      _ = C₂ * Qb ^ 2 * (I ^ 2 * ((q.totient : ℝ) * M ^ 6 * (∑ b, ∫ u, f b u) ^ 2 +
          (q.totient : ℝ) ^ 2 * M ^ 4 * ∫ u, ∑ b, f b u ^ 2)) := by ring
  -- the divisor bound
  have hqd : (q : ℝ) ≤ (q.divisors.card : ℝ) * q.totient := by
    have h := le_totient_mul_card_divisors q
    rw [mul_comm] at h
    exact_mod_cast h
  have hd : (q.divisors.card : ℝ) ≤ Cd * Qa := by
    have h := LinnikPower.card_divisors_le hδ hδ1 q
    rw [← hCddef] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    rw [hQadef]
    calc (q : ℝ) ^ δ ≤ ((q : ℝ) * T) ^ δ :=
          Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_right (by linarith) hT) hδ.le
      _ ≤ ((q : ℝ) * T) ^ (ε / 8) := Real.rpow_le_rpow_of_exponent_le hQ1 hδε
  have hJt0 : 0 ≤ Jint (ftil f T) M₂ M₂ M₂ (4 * |A| + 2) :=
    integral_nonneg fun u => Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [← hQadef] at h1
  have hfin := step_combine h1 hJt2 rfl hqd hd hQa hQb (by linarith) hM0 hC₁ hC₂ (by linarith)
    (Nat.cast_nonneg _) hS0 hJt0 (by positivity)
  rw [hQe] at hfin
  exact hfin

/-! ### Their induction, and their Proposition 8.1 -/

/-- **The induction**: `P81(5(2/3)ⁿ)` for every `n`. -/
theorem P81_pow (n : ℕ) : P81 (5 * (2 / 3) ^ n) := by
  induction n with
  | zero => simpa using P81_base
  | succ n ih =>
    refine P81_step (by positivity) ?_
    have e : 3 * (5 * (2 / 3 : ℝ) ^ (n + 1)) / 2 = 5 * (2 / 3) ^ n := by rw [pow_succ]; ring
    rw [e]
    exact ih

/-- **Their (8.1) for every `ε > 0`**, with an abstract `Λ`. -/
theorem P81_all {ε : ℝ} (hε : 0 < ε) : P81 ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 5 by positivity) (show (2 / 3 : ℝ) < 1 by norm_num)
  refine P81_mono ?_ (P81_pow n)
  have : 5 * (2 / 3 : ℝ) ^ n < ε := by linarith [mul_lt_mul_of_pos_left hn (show (0 : ℝ) < 5 by norm_num)]
  exact this.le

/-- **Their Proposition 8.1** (round 662's displayed hypothesis `CGLP81`), proved: `Λ = φ(q)f_{b₀}(u₀)` satisfies
`Λ ≤ 16π·max(D₄, 1)(qT)²F` (round 692's `Lam_le`), so `P81_all` applies, with `Q₀ = 0`. -/
theorem cglp81 : CGLP81 := by
  intro ϖ hϖ hϖ1 A κ D ε hε
  obtain ⟨C, hC, hP⟩ := P81_all hε A κ (16 * π * max (D 4) 1) D
  refine ⟨C, 0, ?_⟩
  intro q _ T M f b₀ u₀ _ hT hM hMϖ hfs hf hA hdec M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ1 : (1 : ℝ) ≤ q * T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hdecΛ : ∀ (j : ℕ) (ξ : ℝ), ξ ≠ 0 →
      ∑ b, ‖𝓕 (fC f b) ξ‖ ≤ D j * (T / |ξ|) ^ j * ((q.totient : ℝ) * f b₀ u₀) := fun j ξ hξ => by
    have h := hdec j ξ hξ
    calc ∑ b, ‖𝓕 (fC f b) ξ‖ = ∑ b, ‖𝓕 (fun u : ℝ => (f b u : ℂ)) ξ‖ := rfl
      _ ≤ D j * (T / |ξ|) ^ j * q.totient * f b₀ u₀ := h
      _ = D j * (T / |ξ|) ^ j * ((q.totient : ℝ) * f b₀ u₀) := by ring
  have hΛ0 : 0 ≤ (q.totient : ℝ) * f b₀ u₀ := mul_nonneg (Nat.cast_nonneg _) (hf b₀ u₀)
  have hΛF := Lam_le hfs hf hA hT b₀ u₀ (hdecΛ 4)
  have hMQ : M ≤ q * T := by
    refine hMϖ.trans ?_
    calc ((q : ℝ) * T) ^ ϖ ≤ ((q : ℝ) * T) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 hϖ1.le
      _ = q * T := Real.rpow_one _
  have h := hP q T M ((q.totient : ℝ) * f b₀ u₀) f hT hMQ hfs hf hA hΛ0 hΛF hdecΛ M₁ M₂ M₃ hM₁ hM₁M.le hM₂
    hM₂M.le hM₃.le hM₃M.le
  have hfi : ∀ b, Integrable (f b) := fun b => integrable_of_vanish (hfs b).continuous (hA b)
  have e : ∑ b, ∫ u, f b u = ∫ u, ∑ b, f b u := (integral_finsetSum _ fun b _ => hfi b).symm
  rw [e] at h
  exact h

/-- **Their Proposition 11.1 from Heath-Brown's Theorem 10.1 alone**: round 678's `cgls3` with `cglp81`. -/
theorem cgls3_t101 (hT : LinnikCGLT101.CGLT101) : LinnikCGLS23.CGLS3 := LinnikCGLS3.cgls3 cglp81 hT

/-- **Their Proposition 3.1, at one point per character, from Heath-Brown's Theorem 10.1 alone**: round 678's
`prop31_pt` with `cglp81`. -/
theorem prop31_t101 (hT : LinnikCGLT101.CGLT101) : LinnikCGLLV.CGLProp31 := LinnikCGLS3.prop31_pt cglp81 hT

/-- **Linnik's theorem with exponent `9/4` from Heath-Brown's Theorem 10.1 alone**: round 678's `linnik_225c_pt`
with `cglp81`. -/
theorem linnik_225c_t101 (hT : LinnikCGLT101.CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLS3.linnik_225c_pt cglp81 hT

/-- **Linnik's theorem with exponent `226/100` from Heath-Brown's Theorem 10.1 alone**: round 678's
`linnik_226c_pt` with `cglp81`. -/
theorem linnik_226c_t101 (hT : LinnikCGLT101.CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLS3.linnik_226c_pt cglp81 hT

end LinnikCGLP81

#print axioms LinnikCGLP81.P81_base
#print axioms LinnikCGLP81.P81_step
#print axioms LinnikCGLP81.P81_all
#print axioms LinnikCGLP81.cglp81
#print axioms LinnikCGLP81.prop31_t101
#print axioms LinnikCGLP81.linnik_225c_t101
#print axioms LinnikCGLP81.linnik_226c_t101
