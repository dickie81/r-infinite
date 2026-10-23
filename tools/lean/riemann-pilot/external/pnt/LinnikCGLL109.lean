/-
# Round 674: their Lemma 10.9, the small-gcd terms (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Lemma 10.9 (Small GCD terms): "We have Σ_{n₁,n₂∼N, (n₁n₂,q)=1, (n₁,n₂)≤D} |R(n₁/n₂, n₁n₂^{−1})|³ ⪅_ϵ
(DqT + N²)|W|^{1/2}E(W)^{1/2}." (text layer lines 5070–5082; spaces restored; the sum, fraction, large bars, which the
text layer encodes as four form feeds each, large parentheses, subscripts and exponents transcribed). Their proof
splits the sum by `d = (n₁, n₂)` and the residue `a`, bounds each class with Lemma 10.8 and the separation of the
fractions (round 673), sums over `d`, and ends: "We may bound the third moment by Cauchy-Schwarz and Lemmas 9.1 and
9.2," (line 5265) with the bound "⪅_ϵ q|W|^{1/2}E(W)^{1/2}" (line 5285; spaces restored, the subscript and exponents
transcribed).

The stack's form.
* Their sum runs over the pairs with `(n₁n₂, q) = 1`. `R₂(n₁, n₂) = 0` for the others (`R2_eq_zero`), so the stack
  sums over all pairs `n₁, n₂ ∼ N` with `(n₁, n₂) ≤ D` (`pairs`); on the pairs prime to `q`, round 669's `R₂` is their
  `R(n₁/n₂, n₁n₂⁻¹)`.
* The classes. A pair prime to `q` has `d = (n₁, n₂)` in `[1, D]` and the unit `a = n₁n₂⁻¹`, and
  `R₂(n₁, n₂) = F_a(log(n₁/n₂))` with `F_a(y) = Σ_iχ_i(a)e^{it_iy}` (`R2_eq_esum`), a finite exponential sum with
  frequencies `|t_i| ≤ T`. In one class the points `log(n₁/n₂)` are `qd²/(8N²)`-separated (round 673's `log_sep`)
  and at most `1` in absolute value (`abs_log_div_le_one`), so round 673's `sum_cube_le` bounds the class by
  `C_k(3T + 32πN²/(qd²))∫ψ̃₀(y/X)|F_a(y)|³ dy` plus its tail, where their coefficient is `T + N²/(d²q)`.
* The sum over `d`: `Σ_{1≤d≤D}(3T + 32πN²/(qd²)) ≤ 3DT + 64πN²/q`, by Mathlib's `sum_Ioo_inv_sq_le`.
* The third moment. Their Cauchy–Schwarz with Lemmas 9.1 and 9.2 is `sum_cube_moment_le`: `|F|³ ≤ (l|F|² + |F|⁴/l)/2`
  for every `l > 0`, round 658's second moment `Σ_{a unit}|F_a(y)|² = φ(q)|R|`, exact at one point per character, and
  the fourth moment `∫ψ̃₀(y/X)Σ_{a unit}|F_a(y)|⁴ dy ≤ φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)` (`integral_sum_four_le`, whose
  proof copies the second step of round 659's `lemma92`). The weight `ψ̃₀(y/X)` stands for their `|v| ≍ 1`.
* Then `φ(q) ≤ q` turns `(3DT + 64πN²/q)φ(q)` into `3DqT + 64πN²`. Their `⪅_ϵ` absorbs `C_k`, `X`, `∫ψ̃₀`, the term
  `|R|⁴D_K/X^K` and the tail; the stack keeps them, with `X ≥ 4` and `K ≥ 2` free.

Plain statements, with `q ≥ 1`, `k`, `C_k`, `D_K` and `ψ̃₀` as in round 673, `E` round 659's `energy`, `n ∼ N` round
670's `dyad`, and `F_a(y) = Σ_iχ_i(a)e^{it_iy}`, round 668's `esum`.
* `Rf_exp_eq_esum`: `R(e^y, a) = F_a(y)`.
* `abs_log_div_le_one`: for `N > 0` and `n₁, n₂ ∼ N`, `|log(n₁/n₂)| ≤ 1`.
* `integrable_psi0_mul`: `y ↦ ψ̃₀(y/X)G(y)` is integrable for `X > 0` and `G` continuous.
* `le_sqrt_of_forall`: for `a, b ≥ 0`, if `s ≤ (la + b/l)/2` for every `l > 0`, then `s ≤ √(ab)`.
* `integral_sum_four_le`: for `X ≥ 1` and `K ∈ ℕ`, `∫ψ̃₀(τ/X)Σ_{a unit}|R(e^τ, a)|⁴ dτ ≤ φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`.
* `sum_cube_moment_le`: for `χ` injective on `R`, `X ≥ 1` and `K ∈ ℕ`,
  `Σ_{a unit}∫ψ̃₀(y/X)|F_a(y)|³ dy ≤ φ(q)X√(|R|∫ψ̃₀·(∫ψ̃₀·E + |R|⁴D_K/X^K))`.
* `R2_eq_zero`, `R2_eq_esum`: `R₂(n₁, n₂) = 0` unless `n₁` and `n₂` are units modulo `q`; and for `n₁, n₂ > 0` with
  `n₂` a unit modulo `q`, `R₂(n₁, n₂) = F_a(log(n₁/n₂))` with `a = n₁n₂⁻¹`.
* `pairs`: the pairs `n₁, n₂ ∼ N` with `(n₁, n₂) ≤ D`.
* `lemma109`: for `χ` injective on `R`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0`, `X ≥ 4`, `D ∈ ℕ` and `K ≥ 2`,
  `Σ_{(n₁,n₂)∈P}|R₂(n₁, n₂)|³ ≤ C_k(3DqT + 64πN²)X√(|R|∫ψ̃₀·(∫ψ̃₀·E + |R|⁴D_K/X^K)) + |P||R|³·2πD_K(2π)^{−K}Z^{2−K}`,
  with `P` the pairs and `Z = 3T(X − 1)/(2π)`.

The file imports `LinnikCGLSep.lean`.
-/

import LinnikCGLSep

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLL109

open LinnikCGLL105 LinnikCGLRFact LinnikCGLLoc LinnikCGLMom4 LinnikCGLRt LinnikCGLSep LinnikCGLT101

/-! ### `R` as a finite exponential sum -/

/-- `R(e^y, a) = Σ_iχ_i(a)e^{it_iy}`, round 668's `esum`. -/
lemma Rf_exp_eq_esum {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (a : ZMod q)
    (y : ℝ) : Rf R χ t (Real.exp y) a = esum R (fun i => χ i a) t y := by
  rw [Rf_exp]
  unfold esum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm y (t i)]
  exact mul_comm _ _

/-- For `N > 0` and `n₁, n₂ ∼ N`, `|log(n₁/n₂)| ≤ 1`. -/
lemma abs_log_div_le_one {N : ℝ} (hN : 0 < N) {n₁ n₂ : ℕ} (h₁ : n₁ ∈ dyad N) (h₂ : n₂ ∈ dyad N) :
    |Real.log ((n₁ : ℝ) / n₂)| ≤ 1 := by
  rw [mem_dyad hN.le] at h₁ h₂
  have p₁ : (0 : ℝ) < n₁ := hN.trans h₁.1
  have p₂ : (0 : ℝ) < n₂ := hN.trans h₂.1
  have hlt : (n₁ : ℝ) / n₂ < 2 := by rw [div_lt_iff₀ p₂]; linarith [h₁.2, h₂.1]
  have hgt : 1 / 2 < (n₁ : ℝ) / n₂ := by rw [lt_div_iff₀ p₂]; linarith [h₁.1, h₂.2]
  rw [abs_le]
  constructor
  · have := Real.log_lt_log (by norm_num) hgt
    rw [one_div, Real.log_inv] at this
    linarith [Real.log_two_lt_d9]
  · have := Real.log_lt_log (div_pos p₁ p₂) hlt
    linarith [Real.log_two_lt_d9]

/-- `y ↦ ψ̃₀(y/X)G(y)` is integrable for `X > 0` and `G` continuous. -/
lemma integrable_psi0_mul {X : ℝ} (hX : 0 < X) {G : ℝ → ℝ} (hG : Continuous G) :
    Integrable fun y => psi0 (y / X) * G y := by
  have hc : Continuous fun y => psi0 (y / X) * G y := (continuous_psi0.comp (continuous_id.div_const X)).mul hG
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * X)) (b := 2 * X)) fun y hy => ?_
  show psi0 (y / X) * G y = 0
  rw [LinnikCGLMom.psi0_eq_zero, zero_mul]
  rw [abs_div, abs_of_pos hX, le_div_iff₀ hX]
  by_contra hc
  exact hy ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩

/-- **The arithmetic–geometric mean step**: if `s ≤ (la + b/l)/2` for every `l > 0`, with `a, b ≥ 0`, then
`s ≤ √(ab)`. -/
lemma le_sqrt_of_forall {s a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ l : ℝ, 0 < l → s ≤ (l * a + b / l) / 2) :
    s ≤ √(a * b) := by
  rcases ha.lt_or_eq with ha0 | ha0
  · rcases hb.lt_or_eq with hb0 | hb0
    · obtain ⟨u, hu⟩ : ∃ u, u = √a := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v, v = √b := ⟨_, rfl⟩
      have hu0 : 0 < u := by rw [hu]; exact Real.sqrt_pos.2 ha0
      have hv0 : 0 < v := by rw [hv]; exact Real.sqrt_pos.2 hb0
      have hau : a = u ^ 2 := by rw [hu, Real.sq_sqrt ha]
      have hbv : b = v ^ 2 := by rw [hv, Real.sq_sqrt hb]
      rw [Real.sqrt_mul ha, ← hu, ← hv]
      have := h (v / u) (div_pos hv0 hu0)
      rw [hau, hbv] at this
      calc s ≤ (v / u * u ^ 2 + v ^ 2 / (v / u)) / 2 := this
        _ = u * v := by field_simp; ring
    · rw [← hb0, mul_zero, Real.sqrt_zero]
      by_contra hs
      push Not at hs
      have := h (s / a) (div_pos hs ha0)
      rw [← hb0, zero_div, add_zero, div_mul_cancel₀ s ha0.ne'] at this
      linarith
  · rw [← ha0, zero_mul, Real.sqrt_zero]
    by_contra hs
    push Not at hs
    have hl : 0 < b / s + 1 := by positivity
    have := h _ hl
    rw [← ha0, mul_zero, zero_add] at this
    have hlt : b / (b / s + 1) < s := by
      rw [div_lt_iff₀ hl, mul_add, mul_div_cancel₀ b hs.ne', mul_one]
      linarith
    linarith

/-! ### The moments over the units -/

section moments

variable {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

open scoped Classical in
/-- **The weighted fourth moment** (round 659's `lemma92`, its second step): for `X ≥ 1` and `K ∈ ℕ`,
`∫ψ̃₀(τ/X)Σ_{a unit}|R(e^τ, a)|⁴ dτ ≤ φ(q)X(∫ψ̃₀·E + |R|⁴D_K/X^K)`. -/
theorem integral_sum_four_le {X : ℝ} (hX : 1 ≤ X) (K : ℕ) :
    ∫ τ, psi0 (τ / X) * ∑ a : (ZMod q)ˣ, ‖Rf R χ t (Real.exp τ) a‖ ^ 4 ≤
      q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun v => ∑ a : (ZMod q)ˣ, ‖Rf R χ t v a‖ ^ 4 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, H = fun τ => psi0 (τ / X) * G (Real.exp τ) := ⟨_, rfl⟩
  have hgoal : (∫ τ, psi0 (τ / X) * ∑ a : (ZMod q)ˣ, ‖Rf R χ t (Real.exp τ) a‖ ^ 4) = ∫ τ, H τ := by
    rw [hH, hG]
  rw [hgoal]
  have hG0 : ∀ v, 0 ≤ G v := fun v => by rw [hG]; exact Finset.sum_nonneg fun a _ => by positivity
  have hH0 : ∀ τ, 0 ≤ H τ := fun τ => by rw [hH]; exact mul_nonneg (psi0_nonneg _) (hG0 _)
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

/-- **The weighted third moment over the units**: at one point per character, for `X ≥ 1` and `K ∈ ℕ`,
`Σ_{a unit}∫ψ̃₀(y/X)|F_a(y)|³ dy ≤ φ(q)X√(|R|∫ψ̃₀·(∫ψ̃₀·E + |R|⁴D_K/X^K))`, with `F_a = Σ_iχ_i(a)e^{it_iy}`. It is
Cauchy–Schwarz between the second moment, `φ(q)|R|X∫ψ̃₀` exactly (round 658's `sum_norm_Rf_sq`), and the fourth
(`integral_sum_four_le`), in the form `|F|³ ≤ (l|F|² + |F|⁴/l)/2` for every `l > 0`. -/
theorem sum_cube_moment_le (hinj : Set.InjOn χ R) {X : ℝ} (hX : 1 ≤ X) (K : ℕ) :
    ∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 3 ≤
      q.totient * X *
        √(R.card * (∫ x, psi0 x) * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) := by
  have hX0 : 0 < X := by linarith
  have hc : ∀ u : (ZMod q)ˣ, Continuous (esum R (fun i => χ i u) t) := fun u => continuous_esum R _ t
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hE0 : (0 : ℝ) ≤ energy R χ t := Nat.cast_nonneg _
  have hD0 := Dpsi_nonneg K
  have hi : ∀ (u : (ZMod q)ˣ) (k : ℕ), Integrable fun y => psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ k :=
    fun u k => integrable_psi0_mul hX0 ((hc u).norm.pow k)
  -- the second moment, exactly
  have hS2 : ∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 2 =
      q.totient * R.card * (X * ∫ x, psi0 x) := by
    have hsw : ∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 2 =
        ∫ y, ∑ u : (ZMod q)ˣ, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 2 :=
      (integral_finsetSum _ fun u _ => hi u 2).symm
    rw [hsw]
    have e : ∀ y, ∑ u : (ZMod q)ˣ, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 2 =
        psi0 (y / X) * (q.totient * R.card) := by
      intro y
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [← Rf_exp_eq_esum]
      exact LinnikCGLMom.sum_norm_Rf_sq R hinj t (Real.exp_pos y)
    simp_rw [e]
    rw [integral_mul_const, Measure.integral_comp_div psi0 X, abs_of_pos hX0, smul_eq_mul]
    ring
  -- the fourth moment
  have hS4 : ∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 4 ≤
      q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) := by
    have hsw : ∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 4 =
        ∫ y, ∑ u : (ZMod q)ˣ, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 4 :=
      (integral_finsetSum _ fun u _ => hi u 4).symm
    rw [hsw]
    have e : ∀ y, ∑ u : (ZMod q)ˣ, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 4 =
        psi0 (y / X) * ∑ a : (ZMod q)ˣ, ‖Rf R χ t (Real.exp y) a‖ ^ 4 := by
      intro y
      rw [← Finset.mul_sum]
      simp_rw [Rf_exp_eq_esum]
    simp_rw [e]
    exact integral_sum_four_le R χ t hX K
  -- every `l > 0`
  have hl : ∀ l : ℝ, 0 < l → ∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 3 ≤
      (l * (q.totient * R.card * (X * ∫ x, psi0 x)) +
        q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) / l) / 2 := by
    intro l hl
    have hpt : ∀ (u : (ZMod q)ˣ) y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 3 ≤
        l / 2 * (psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 2) +
          1 / (2 * l) * (psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 4) := by
      intro u y
      have hp := psi0_nonneg (y / X)
      obtain ⟨z, hz⟩ : ∃ z, z = ‖esum R (fun i => χ i u) t y‖ := ⟨_, rfl⟩
      rw [← hz]
      have e : l / 2 * (psi0 (y / X) * z ^ 2) + 1 / (2 * l) * (psi0 (y / X) * z ^ 4) - psi0 (y / X) * z ^ 3 =
          psi0 (y / X) * (z ^ 2 * (l - z) ^ 2 / (2 * l)) := by
        field_simp
        ring
      have : 0 ≤ psi0 (y / X) * (z ^ 2 * (l - z) ^ 2 / (2 * l)) := by positivity
      linarith
    calc ∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 3
        ≤ ∑ u : (ZMod q)ˣ, ∫ y, (l / 2 * (psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 2) +
            1 / (2 * l) * (psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 4)) :=
          Finset.sum_le_sum fun u _ => integral_mono (hi u 3)
            (((hi u 2).const_mul _).add ((hi u 4).const_mul _)) (hpt u)
      _ = l / 2 * (∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 2) +
            1 / (2 * l) * (∑ u : (ZMod q)ˣ, ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i u) t y‖ ^ 4) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [integral_add ((hi u 2).const_mul _) ((hi u 4).const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ l / 2 * (q.totient * R.card * (X * ∫ x, psi0 x)) +
            1 / (2 * l) * (q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) := by
          rw [hS2]
          have : (0 : ℝ) ≤ 1 / (2 * l) := by positivity
          have := mul_le_mul_of_nonneg_left hS4 this
          linarith
      _ = (l * (q.totient * R.card * (X * ∫ x, psi0 x)) +
            q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) / l) / 2 := by
          field_simp
  have ha : (0 : ℝ) ≤ q.totient * R.card * (X * ∫ x, psi0 x) := by positivity
  have hb : (0 : ℝ) ≤ q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K) := by
    positivity
  refine (le_sqrt_of_forall ha hb hl).trans (le_of_eq ?_)
  have e : q.totient * R.card * (X * ∫ x, psi0 x) *
      (q.totient * X * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) =
      (q.totient * X) ^ 2 *
        (R.card * (∫ x, psi0 x) * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) := by ring
  rw [e, Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (by positivity)]

end moments

/-! ### Their Lemma 10.9 -/

section lemma109

variable {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

omit [NeZero q] in
/-- `R₂(n₁, n₂) = 0` unless `n₁` and `n₂` are units modulo `q`. -/
lemma R2_eq_zero {n₁ n₂ : ℕ} (h : ¬(IsUnit (n₁ : ZMod q) ∧ IsUnit (n₂ : ZMod q))) : R2 R χ t n₁ n₂ = 0 := by
  unfold R2
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases not_and_or.mp h with h1 | h2
  · rw [MulChar.map_nonunit _ h1, zero_mul, zero_mul]
  · rw [MulChar.map_nonunit _ h2, map_zero, mul_zero, zero_mul]

/-- For `n₁, n₂ > 0` with `n₂` a unit modulo `q`, `R₂(n₁, n₂) = F_a(log(n₁/n₂))` with `a = n₁n₂⁻¹` and
`F_a(y) = Σ_iχ_i(a)e^{it_iy}`. -/
lemma R2_eq_esum {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) (hu : IsUnit (n₂ : ZMod q)) :
    R2 R χ t n₁ n₂ = esum R (fun i => χ i ((n₁ : ZMod q) * (n₂ : ZMod q)⁻¹)) t (Real.log ((n₁ : ℝ) / n₂)) := by
  have hp : (0 : ℝ) < (n₁ : ℝ) / n₂ := div_pos (Nat.cast_pos.mpr h₁) (Nat.cast_pos.mpr h₂)
  rw [R2_eq_Rf R χ t h₁ h₂ hu, ← Rf_exp_eq_esum, Real.exp_log hp]

omit [NeZero q] in
/-- The pairs `n₁, n₂ ∼ N` with `(n₁, n₂) ≤ D`. -/
def pairs (N : ℝ) (D : ℕ) : Finset (ℕ × ℕ) := (dyad N ×ˢ dyad N).filter fun p => Nat.gcd p.1 p.2 ≤ D

/-- **Their Lemma 10.9 (small gcd terms), at one point per character**: for `q ≥ 1`, `χ` injective on `R`, `T ≥ 1`,
points `|t_i| ≤ T`, `N > 0`, `X ≥ 4`, `D ∈ ℕ` and `K ≥ 2`, `Σ_{n₁,n₂∼N, (n₁,n₂)≤D}|R₂(n₁, n₂)|³ ≤
C_k(3DqT + 64πN²)X√(|R|∫ψ̃₀·(∫ψ̃₀·E + |R|⁴D_K/X^K)) + |P|·|R|³·2πD_K(2π)^{−K}Z^{2−K}`, with `P` the pairs and
`Z = 3T(X − 1)/(2π)`. The pairs prime to `q` are split by their gcd `d` and their residue `a = n₁n₂⁻¹`; on each
class `R₂(n₁, n₂) = F_a(log(n₁/n₂))` (`R2_eq_esum`), the points are `qd²/(8N²)`-separated (round 673's `log_sep`),
and round 673's `sum_cube_le` applies; `Σ_d(3T + 32πN²/(qd²)) ≤ 3DT + 64πN²/q`, and `sum_cube_moment_le` bounds
the sum over `a`. -/
theorem lemma109 (hinj : Set.InjOn χ R) {T N X : ℝ} (hT : 1 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T) (hN : 0 < N)
    (hX : 4 ≤ X) (D : ℕ) {K : ℕ} (hK : 2 ≤ K) :
    ∑ p ∈ pairs N D, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤
      Ck * (3 * D * q * T + 64 * π * N ^ 2) * X *
          √(R.card * (∫ x, psi0 x) * ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) +
        (pairs N D).card * (R.card : ℝ) ^ 3 *
          (2 * π * (Dpsi K / (2 * π) ^ K / (3 * T * (X - 1) / (2 * π)) ^ (K - 2))) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = √(R.card * (∫ x, psi0 x) *
      ((∫ x, psi0 x) * energy R χ t + (R.card : ℝ) ^ 4 * Dpsi K / X ^ K)) := ⟨_, rfl⟩
  rw [← hQ]
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ℝ, τ' = 2 * π * (Dpsi K / (2 * π) ^ K / (3 * T * (X - 1) / (2 * π)) ^ (K - 2)) :=
    ⟨_, rfl⟩
  rw [← hτ']
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hτ'0 : 0 ≤ τ' := by
    rw [hτ']
    have := Dpsi_nonneg K
    have : 0 < 3 * T * (X - 1) / (2 * π) := by
      have : 0 < X - 1 := by linarith
      positivity
    positivity
  obtain ⟨A, hA⟩ : ∃ A : Finset (ZMod q), A = Finset.univ.image fun u : (ZMod q)ˣ => (u : ZMod q) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Finset (ℕ × ℕ),
      U = (pairs N D).filter fun p => IsUnit (p.1 : ZMod q) ∧ IsUnit (p.2 : ZMod q) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ × ℕ → ℕ × ZMod q,
      g = fun p => (Nat.gcd p.1 p.2, (p.1 : ZMod q) * (p.2 : ZMod q)⁻¹) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ZMod q → ℝ, W = fun a => ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i a) t y‖ ^ 3 :=
    ⟨_, rfl⟩
  have hW0 : ∀ a, 0 ≤ W a := fun a => by
    rw [hW]; exact integral_nonneg fun y => mul_nonneg (psi0_nonneg _) (by positivity)
  -- membership
  have hmemU : ∀ p ∈ U, p.1 ∈ dyad N ∧ p.2 ∈ dyad N ∧ Nat.gcd p.1 p.2 ≤ D ∧ IsUnit (p.1 : ZMod q) ∧
      IsUnit (p.2 : ZMod q) := by
    intro p hp
    simp only [hU, pairs, Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨hp.1.1.1, hp.1.1.2, hp.1.2, hp.2.1, hp.2.2⟩
  have hposd : ∀ n ∈ dyad N, 0 < n := fun n hn => by
    have := ((mem_dyad hN.le).mp hn).1
    exact_mod_cast hN.trans this
  -- the pairs not prime to `q` contribute nothing
  have h1 : ∑ p ∈ pairs N D, ‖R2 R χ t p.1 p.2‖ ^ 3 = ∑ p ∈ U, ‖R2 R χ t p.1 p.2‖ ^ 3 := by
    rw [hU, Finset.sum_filter_of_ne]
    intro p _ hp
    by_contra hnu
    exact hp (by rw [R2_eq_zero R χ t hnu, norm_zero]; norm_num)
  -- the classes
  have hmaps : ∀ p ∈ U, g p ∈ Finset.Ioo 0 (D + 1) ×ˢ A := by
    intro p hp
    obtain ⟨h₁, -, hD, hu₁, hu₂⟩ := hmemU p hp
    simp only [hg, hA, Finset.mem_product, Finset.mem_Ioo, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨Nat.gcd_pos_of_pos_left _ (hposd _ h₁), Nat.lt_succ_of_le hD⟩, hu₁.unit * hu₂.unit⁻¹, ?_⟩
    rw [Units.val_mul, ← ZMod.inv_coe_unit, IsUnit.unit_spec, IsUnit.unit_spec]
  have hclass : ∀ d ∈ Finset.Ioo 0 (D + 1), ∀ a ∈ A,
      ∑ p ∈ U with g p = (d, a), ‖R2 R χ t p.1 p.2‖ ^ 3 ≤
        Ck * (3 * T + 32 * π * N ^ 2 / (q * (d : ℝ) ^ 2)) * W a +
          ((U.filter fun p => g p = (d, a)).card : ℝ) * (R.card : ℝ) ^ 3 * τ' := by
    intro d hd a _
    have hd0 : 0 < d := (Finset.mem_Ioo.mp hd).1
    obtain ⟨P, hP⟩ : ∃ P : Finset (ℕ × ℕ), P = U.filter fun p => g p = (d, a) := ⟨_, rfl⟩
    rw [← hP]
    have hmem : ∀ p ∈ P, p.1 ∈ dyad N ∧ p.2 ∈ dyad N ∧ Nat.gcd p.1 p.2 = d ∧ IsUnit (p.1 : ZMod q) ∧
        IsUnit (p.2 : ZMod q) ∧ (p.1 : ZMod q) * (p.2 : ZMod q)⁻¹ = a := by
      intro p hp
      rw [hP, Finset.mem_filter] at hp
      obtain ⟨h₁, h₂, -, hu₁, hu₂⟩ := hmemU p hp.1
      have h := hp.2
      simp only [hg, Prod.mk.injEq] at h
      exact ⟨h₁, h₂, h.1, hu₁, hu₂, h.2⟩
    have hR2 : ∑ p ∈ P, ‖R2 R χ t p.1 p.2‖ ^ 3 =
        ∑ p ∈ P, ‖esum R (fun i => χ i a) t (Real.log ((p.1 : ℝ) / p.2))‖ ^ 3 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨h₁, h₂, -, -, hu₂, hres⟩ := hmem p hp
      rw [R2_eq_esum R χ t (hposd _ h₁) (hposd _ h₂) hu₂, hres]
    rw [hR2]
    have hδ : (0 : ℝ) < q * (d : ℝ) ^ 2 / (8 * N ^ 2) := by
      have : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
      positivity
    have hx : ∀ p ∈ P, |Real.log ((p.1 : ℝ) / p.2)| ≤ 1 := fun p hp =>
      abs_log_div_le_one hN (hmem p hp).1 (hmem p hp).2.1
    have hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' →
        q * (d : ℝ) ^ 2 / (8 * N ^ 2) ≤ |Real.log ((p.1 : ℝ) / p.2) - Real.log ((p'.1 : ℝ) / p'.2)| := by
      intro p hp p' hp' hne
      obtain ⟨h₁, h₂, hgd, hu₁, hu₂, hres⟩ := hmem p hp
      obtain ⟨h₁', h₂', hgd', -, hv₂, hres'⟩ := hmem p' hp'
      have := log_sep (q := q) hN h₁ h₂ h₁' h₂' (by rw [hgd, hgd']) hu₁ hu₂ hv₂ (by rw [hres, hres']) (by
        intro h; exact hne (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)))
      rwa [hgd] at this
    have key := sum_cube_le R (fun i => χ i a) t hT ht hX hδ P (fun p => Real.log ((p.1 : ℝ) / p.2)) hx hsep hK
    rw [← hτ'] at key
    have hB : ∑ i ∈ R, ‖χ i a‖ ≤ R.card := by
      calc ∑ i ∈ R, ‖χ i a‖ ≤ ∑ _i ∈ R, (1 : ℝ) := Finset.sum_le_sum fun i _ => DirichletCharacter.norm_le_one _ _
        _ = R.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hB3 : (∑ i ∈ R, ‖χ i a‖) ^ 3 ≤ (R.card : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _) hB 3
    have hcoef : 4 * π / (q * (d : ℝ) ^ 2 / (8 * N ^ 2)) = 32 * π * N ^ 2 / (q * (d : ℝ) ^ 2) := by
      have : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
      field_simp
      ring
    rw [hcoef] at key
    have hWa : W a = ∫ y, psi0 (y / X) * ‖esum R (fun i => χ i a) t y‖ ^ 3 := by rw [hW]
    rw [hWa]
    have hP0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hB3 hP0
    have := mul_le_mul_of_nonneg_right this hτ'0
    linarith
  -- the sum over `d`
  have hcd : ∑ d ∈ Finset.Ioo 0 (D + 1), Ck * (3 * T + 32 * π * N ^ 2 / (q * (d : ℝ) ^ 2)) ≤
      Ck * (3 * D * T + 64 * π * N ^ 2 / q) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ Ck_nonneg
    have e : ∀ d : ℕ, 3 * T + 32 * π * N ^ 2 / (q * (d : ℝ) ^ 2) =
        3 * T + 32 * π * N ^ 2 / q * ((d : ℝ) ^ 2)⁻¹ := fun d => by
      ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioo, ← Finset.mul_sum, nsmul_eq_mul]
    have hs : ∑ i ∈ Finset.Ioo 0 (D + 1), ((i : ℝ) ^ 2)⁻¹ ≤ 2 := by
      have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (D + 1)
      norm_num at h
      exact h
    have hc0 : (0 : ℝ) ≤ 32 * π * N ^ 2 / q := by positivity
    have := mul_le_mul_of_nonneg_left hs hc0
    have hD : ((D + 1 - 0 - 1 : ℕ) : ℝ) = D := by simp
    rw [hD]
    have h64 : (D : ℝ) * (3 * T) + 32 * π * N ^ 2 / q * ∑ i ∈ Finset.Ioo 0 (D + 1), ((i : ℝ) ^ 2)⁻¹ ≤
        (D : ℝ) * (3 * T) + 32 * π * N ^ 2 / q * 2 := add_le_add (le_refl _) this
    have e64 : (D : ℝ) * (3 * T) + 32 * π * N ^ 2 / q * 2 = 3 * D * T + 64 * π * N ^ 2 / q := by ring
    exact h64.trans (le_of_eq e64)
  -- the sum over the classes
  have hcardU : ∑ d ∈ Finset.Ioo 0 (D + 1), ∑ a ∈ A, ((U.filter fun p => g p = (d, a)).card : ℝ) = U.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.Ioo 0 (D + 1) ×ˢ A) fun p hp => hmaps p hp,
      Nat.cast_sum, Finset.sum_product]
  have hsumW : ∑ a ∈ A, W a ≤ q.totient * X * Q := by
    rw [hA, Finset.sum_image fun u _ v _ h => Units.ext h, hQ, hW]
    exact sum_cube_moment_le R χ t hinj hX1 K
  have hsW0 : 0 ≤ ∑ a ∈ A, W a := Finset.sum_nonneg fun a _ => hW0 a
  have hUc : (U.card : ℝ) ≤ (pairs N D).card := by
    rw [hU]; exact_mod_cast Finset.card_filter_le _ _
  have htot : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  calc ∑ p ∈ pairs N D, ‖R2 R χ t p.1 p.2‖ ^ 3 = ∑ p ∈ U, ‖R2 R χ t p.1 p.2‖ ^ 3 := h1
    _ = ∑ j ∈ Finset.Ioo 0 (D + 1) ×ˢ A, ∑ p ∈ U with g p = j, ‖R2 R χ t p.1 p.2‖ ^ 3 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ d ∈ Finset.Ioo 0 (D + 1), ∑ a ∈ A, ∑ p ∈ U with g p = (d, a), ‖R2 R χ t p.1 p.2‖ ^ 3 :=
        Finset.sum_product _ _ _
    _ ≤ ∑ d ∈ Finset.Ioo 0 (D + 1), ∑ a ∈ A, (Ck * (3 * T + 32 * π * N ^ 2 / (q * (d : ℝ) ^ 2)) * W a +
          ((U.filter fun p => g p = (d, a)).card : ℝ) * (R.card : ℝ) ^ 3 * τ') :=
        Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun a ha => hclass d hd a ha
    _ = (∑ d ∈ Finset.Ioo 0 (D + 1), Ck * (3 * T + 32 * π * N ^ 2 / (q * (d : ℝ) ^ 2))) * ∑ a ∈ A, W a +
          (∑ d ∈ Finset.Ioo 0 (D + 1), ∑ a ∈ A, ((U.filter fun p => g p = (d, a)).card : ℝ)) *
            (R.card : ℝ) ^ 3 * τ' := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    _ ≤ Ck * (3 * D * T + 64 * π * N ^ 2 / q) * (q.totient * X * Q) + (pairs N D).card * (R.card : ℝ) ^ 3 * τ' := by
        rw [hcardU]
        have hR3 : (0 : ℝ) ≤ (R.card : ℝ) ^ 3 * τ' := by positivity
        have h2 : (U.card : ℝ) * (R.card : ℝ) ^ 3 * τ' ≤ (pairs N D).card * (R.card : ℝ) ^ 3 * τ' := by
          rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hUc hR3
        have hC0 : 0 ≤ Ck * (3 * D * T + 64 * π * N ^ 2 / q) := by
          have := Ck_nonneg; positivity
        have h3 := mul_le_mul hcd hsumW hsW0 hC0
        linarith
    _ ≤ Ck * (3 * D * q * T + 64 * π * N ^ 2) * X * Q + (pairs N D).card * (R.card : ℝ) ^ 3 * τ' := by
        have hk : Ck * (3 * D * T + 64 * π * N ^ 2 / q) * (q.totient * X * Q) ≤
            Ck * (3 * D * T + 64 * π * N ^ 2 / q) * (q * X * Q) := by
          have hC0 : 0 ≤ Ck * (3 * D * T + 64 * π * N ^ 2 / q) := by
            have := Ck_nonneg; positivity
          refine mul_le_mul_of_nonneg_left ?_ hC0
          have : 0 ≤ X * Q := by positivity
          nlinarith
        have he : Ck * (3 * D * T + 64 * π * N ^ 2 / q) * (q * X * Q) =
            Ck * (3 * D * q * T + 64 * π * N ^ 2) * X * Q := by
          field_simp
        linarith

end lemma109

end LinnikCGLL109

#print axioms LinnikCGLL109.integral_sum_four_le
#print axioms LinnikCGLL109.sum_cube_moment_le
#print axioms LinnikCGLL109.lemma109
