/-
# Round 697: the reflection of the principal Gram entries (the CGL plan's stage M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 641's `LinnikCGLReflect.reflect_gram` and round 642's `LinnikCGLPair.norm_gram_le` reflect the Gram entries
`G(i, k)` with `χ_i ≠ χ_k`. Heath-Brown's bound sums over every pair. For `χ_i = χ_k` the integrand of round 640's
`perron_gram` is `G₁(s) = L(s, χ₀)H(s + iτ)N^s`, with `χ₀` the principal character mod `q`, and `L(s, χ₀)` has a pole
at `s = 1`. This file reflects those entries through the pole and keeps its residue term. The dual sum runs over `χ₀`
itself, as in Jutila's Lemma 1 for the principal character at `|t| ≥ h²` (Acta Arith. 32 (1977); README round 694).

The stack's form.
* The functional equation `L(s, χ) = Φ(s)L(1 − s, χ⁻¹)E(s)` of round 641 holds for every `χ`, the principal one
  included, at `Re s < 1` and `s ≠ 0` (`LFunction_reflected0`): round 526's proof, with Mathlib's conditions `s ≠ 0`
  and `s ≠ 1` in place of `ψ ≠ 1`.
* `L(s, χ₀) = ζ(s)E₀(s)` with `E₀(s) = ∏_{p∣q}(1 − p^{−s})` (Mathlib's `LFunction_changeLevel` from the character
  mod `1`), and `|ζ(σ + it)| ≤ 2 + 2|t|/σ` for `0 < σ ≤ 2` and `|t| ≥ 2` (PNT+'s `Zeta0EqZeta` at `N = 1` and
  `ZetaBnd_aux1`).
* The shift from `Re s = 2` to `Re s = 1/2` crosses the pole: round 524's `LinnikGamma.verticalIntegral_sub_eq`,
  translated to `s = 1`, with the residue `R = E₀(1)H(1 + iτ)N` (Mathlib's `isBigO_riemannZeta_sub_one_div`).
* The rest is `G₁ − Mn` (round 641's `Mn`), holomorphic on `Re s < 1`: at `s = 0`, where `L(1 − s, χ₀)` has a pole,
  this form needs no value of it. It moves to `Re s = −K` (round 641's `shift_of_bound`), where it is round 641's
  `Tl`.

Plain statements, with `q ≥ 1` (`[NeZero q]`), `χ₀` the principal character mod `q`, `N > 0`, `τ` real, and `G₁`,
`Mn`, `Tl` round 641's integrands at `χ₀`.
* `LFunction_eq_reflect0`, `LFunction_reflected0`: for a primitive `ψ` mod `f ≥ 1` with `f ∣ q`, `Re s < 1` and
  `s ≠ 0`, round 526's identity; and for every `χ` mod `q`, `L(s, χ) = Φ(s)L(1 − s, χ⁻¹)E(s)` at `Re s < 1`, `s ≠ 0`.
* `LFunction_one_eq`, `norm_E0_le`, `norm_E0_one_le`: for `s ≠ 1`, `L(s, χ₀) = ζ(s)E₀(s)`; `|E₀(s)| ≤ 2^{ω(q)}` for
  `Re s ≥ 0`; and `|E₀(1)| ≤ 1`.
* `norm_zeta_le_strip`, `norm_L1_le_strip`, `norm_L1_le_right`: for `0 < σ ≤ 2` and `|t| ≥ 2`,
  `|ζ(σ + it)| ≤ 2 + 2|t|/σ` and `|L(σ + it, χ₀)| ≤ 2^{ω(q)}(2 + 2|t|/σ)`; and for `σ ≥ 1/2` and `|t| ≥ 2`,
  `|L(σ + it, χ₀)| ≤ 2^{ω(q)}(2 + 4|t| + |ζ(3/2)|)`.
* `G1_one_far`, `Rt0_bound`: `|G₁(x + iy)| ≤ M(1 + |y + τ|)^{−2}` on `1/2 ≤ x ≤ 2`, `|y| ≥ 2`; and, for `K ≥ 1`,
  `|(G₁ − Mn)(x + iy)| ≤ M(1 + |y + τ|)^{−2}` on `−K ≤ x ≤ 1/2`.
* `shift_pole`: `∫_{(2)}G₁ − ∫_{(1/2)}G₁ = 2πR`, with `R = E₀(1)H(1 + iτ)N`, the integrals over `v` with `s = σ + iv`.
* `reflect_gram0`: for `Z ≥ 0` and `K ≥ 1`, `∫_{(2)}G₁ = 2πR + ∫_{(1/2)}Mn + ∫_{(−K)}Tl`.
* `gram_reflect0`, `norm_gram_le0`: for `χ_i = χ_k`, `τ = t_i − t_k`, `Z ≥ 0` and `K ≥ 1`,
  `G(i, k) = N^{iτ}(R + (2π)⁻¹(∫_{(1/2)}Mn + ∫_{(−K)}Tl))`; and for `Z, K ≥ 1`,
  `|G(i, k)| ≤ N|H(1 + iτ)| + (2π)⁻¹(N^{1/2}Q₀(q)∫|H(1/2 + iu)||D(u)| du + T_K)`, with
  `D(u) = Σ_{m≤Z}χ₀(m)m^{−1/2+i(u−τ)}` and `T_K` the bound of round 642's `norm_integral_Tl_le`.

The file imports `LinnikCGLPair.lean`, `LinnikAFE.lean` and `HalfPlaneLindelof.lean`.
-/

import LinnikCGLPair
import LinnikAFE
import HalfPlaneLindelof

open Complex Set Real Filter Topology MeasureTheory Asymptotics

noncomputable section

namespace LinnikCGLRefl0

open LinnikCGLMat LinnikCGLMellin LinnikCGLReflect LinnikCGLPair DirichletCharacter LinnikReflect

/-! ### The functional equation at `s ≠ 0` -/

/-- **Round 526's functional equation at `s ≠ 0`**: for a primitive `ψ` mod `f ≥ 1` (the trivial one included),
`f ∣ q` with `q ≥ 1`, `Re s < 1` and `s ≠ 0`,
`L(s, ψ) = f^{1/2−s}ε(ψ)·(γ_{ψ⁻¹}(1 − s)/γ_ψ(s))·eulerQ(s)⁻¹·L(1 − s, χ⁻¹)`, with `χ` the character mod `q` that `ψ`
induces. -/
theorem LFunction_eq_reflect0 {f q : ℕ} [NeZero f] [NeZero q] (hfq : f ∣ q) {ψ : DirichletCharacter ℂ f}
    (hprim : ψ.IsPrimitive) {s : ℂ} (hs : s.re < 1) (hs0 : s ≠ 0) :
    LFunction ψ s = (f : ℂ) ^ (1 / 2 - s) * rootNumber ψ * gr ψ s * (eulerQ ψ q s)⁻¹ *
      LFunction (changeLevel hfq ψ)⁻¹ (1 - s) := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have h1s : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have h1s1 : 1 - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  rw [LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0)]
  have hFE := IsPrimitive.completedLFunction_one_sub hprim (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  have hγ : gammaFactor ψ⁻¹ (1 - s) ≠ 0 := by
    rcases ψ⁻¹.even_or_odd with h | h
    · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hL1 : completedLFunction ψ⁻¹ (1 - s) = LFunction ψ⁻¹ (1 - s) * gammaFactor ψ⁻¹ (1 - s) := by
    rw [LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inl h1s), div_mul_cancel₀ _ hγ]
  have hcl : changeLevel hfq ψ⁻¹ = (changeLevel hfq ψ)⁻¹ := map_inv _ ψ
  have hL2 := LFunction_changeLevel hfq ψ⁻¹ (s := 1 - s) (Or.inr h1s1)
  rw [hcl] at hL2
  have hE : eulerQ ψ q s = ∏ p ∈ q.primeFactors, (1 - ψ⁻¹ p * (p : ℂ) ^ (-(1 - s))) := rfl
  have hE0 := eulerQ_ne_zero ψ q hs
  have hL3 : LFunction ψ⁻¹ (1 - s) = (eulerQ ψ q s)⁻¹ * LFunction (changeLevel hfq ψ)⁻¹ (1 - s) := by
    rw [hL2, ← hE, mul_comm (LFunction ψ⁻¹ (1 - s)), ← mul_assoc, inv_mul_cancel₀ hE0, one_mul]
  rw [hL1, hL3]
  have hexp : (f : ℂ) ^ (1 - s - 1 / 2) = (f : ℂ) ^ (1 / 2 - s) := by ring_nf
  rw [hexp]
  unfold gr
  ring

/-- **The reflected `L`-function at `s ≠ 0`**: for every `χ` mod `q ≥ 1`, the principal one included, `Re s < 1` and
`s ≠ 0`, `L(s, χ) = Φ(s)L(1 − s, χ⁻¹)E(s)`, with `Φ` and `E` those of the primitive character of `χ`. -/
lemma LFunction_reflected0 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re < 1) (hs0 : s ≠ 0) :
    LFunction χ s = Phi χ.primitiveCharacter q s * LFunction χ⁻¹ (1 - s) * Eu χ.primitiveCharacter q s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (s := s) (Or.inr hs1)
  rw [changeLevel_primitiveCharacter] at h
  rw [h, LFunction_eq_reflect0 χ.conductor_dvd_level χ.primitiveCharacter_isPrimitive hs hs0,
    changeLevel_primitiveCharacter]
  unfold Phi Eu
  ring

/-! ### `L(s, χ₀)` through `ζ` -/

/-- `E₀(s) = ∏_{p∣q}(1 − p^{−s})`. -/
def E0 (q : ℕ) (s : ℂ) : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))

/-- For `q ≥ 1` and `s ≠ 1`, `L(s, χ₀) = ζ(s)E₀(s)`. -/
lemma LFunction_one_eq {q : ℕ} [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    LFunction (1 : DirichletCharacter ℂ q) s = riemannZeta s * E0 q s := by
  have h := LFunction_changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1) (s := s) (Or.inr hs)
  rw [changeLevel_one, LFunction_modOne_eq] at h
  rw [h, E0]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

lemma differentiable_E0 (q : ℕ) : Differentiable ℂ (E0 q) := by
  intro s
  unfold E0
  refine DifferentiableAt.fun_finsetProd fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl hp0))

/-- `|E₀(s)| ≤ 2^{ω(q)}` for `Re s ≥ 0`. -/
lemma norm_E0_le (q : ℕ) {s : ℂ} (hs : 0 ≤ s.re) : ‖E0 q s‖ ≤ 2 ^ q.primeFactors.card := by
  unfold E0
  rw [norm_prod]
  refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p hp => ?_).trans (by rw [Finset.prod_const])
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h1 : (p : ℝ) ^ (-s).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpp.one_lt.le) (by simp; linarith)
  calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ = 1 + (p : ℝ) ^ (-s).re := by rw [norm_one, Complex.norm_natCast_cpow_of_pos hpp.pos]
    _ ≤ 2 := by linarith

/-- `|E₀(1)| ≤ 1`. -/
lemma norm_E0_one_le (q : ℕ) : ‖E0 q 1‖ ≤ 1 := by
  unfold E0
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have e : (1 : ℂ) - (p : ℂ) ^ (-(1 : ℂ)) = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.cpow_neg_one]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by have := inv_lt_one_of_one_lt₀ hp1; linarith)]
  have : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  linarith

/-! ### Bounds on vertical lines -/

/-- **`ζ` on `0 < σ ≤ 2`, `|t| ≥ 2`**: `|ζ(σ + it)| ≤ 2 + 2|t|/σ` (PNT+'s `Zeta0EqZeta` at `N = 1` and
`ZetaBnd_aux1`). -/
lemma norm_zeta_le_strip {σ t : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖riemannZeta (σ + t * I)‖ ≤ 2 + 2 * |t| / σ := by
  have hint := ZetaBnd_aux1 1 le_rfl ⟨hσ, hσ2⟩ ht
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hsim] at this
    simp at this
    rw [this] at ht
    norm_num at ht
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith
  rw [← Zeta0EqZeta (N := 1) one_pos (by rw [hsre]; exact hσ) hs1]
  unfold riemannZeta0
  have hsum : ∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ) ^ s) = 1 := by
    simp [Finset.sum_range_succ, Complex.zero_cpow hs0]
  have h1s : 2 ≤ ‖1 - s‖ := by
    calc (2 : ℝ) ≤ |t| := ht
      _ = |(1 - s).im| := by simp [hsim]
      _ ≤ ‖1 - s‖ := Complex.abs_im_le_norm _
  have hfr : ‖(-((1 : ℕ) : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ 1 / 2 := by
    rw [Nat.cast_one, Complex.one_cpow, norm_div, norm_neg, norm_one]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hhalf : ‖(-((1 : ℕ) : ℂ) ^ (-s)) / 2‖ = 1 / 2 := by
    rw [Nat.cast_one, Complex.one_cpow, norm_div, norm_neg, norm_one, Complex.norm_two]
  have hint' : ‖s * ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ 2 * |t| / σ := by
    have e : 2 * |t| * ((1 : ℕ) : ℝ) ^ (-σ) / σ = 2 * |t| / σ := by rw [Nat.cast_one, Real.one_rpow, mul_one]
    rw [← e]
    exact hint
  calc ‖(∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ) ^ s)) + (-((1 : ℕ) : ℂ) ^ (1 - s)) / (1 - s) +
        (-((1 : ℕ) : ℂ) ^ (-s)) / 2 + s * ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ‖∑ n ∈ Finset.range (1 + 1), 1 / ((n : ℂ) ^ s)‖ + ‖(-((1 : ℕ) : ℂ) ^ (1 - s)) / (1 - s)‖ +
        ‖(-((1 : ℕ) : ℂ) ^ (-s)) / 2‖ + ‖s * ∫ x in Ioi ((1 : ℕ) : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := by
        exact norm_add₄_le
    _ ≤ 1 + 1 / 2 + 1 / 2 + 2 * |t| / σ := by
        rw [hsum, norm_one, hhalf]
        linarith
    _ = 2 + 2 * |t| / σ := by ring

/-- For `q ≥ 1`, `0 < σ ≤ 2` and `|t| ≥ 2`, `|L(σ + it, χ₀)| ≤ 2^{ω(q)}(2 + 2|t|/σ)`. -/
lemma norm_L1_le_strip {q : ℕ} [NeZero q] {σ t : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)‖ ≤ 2 ^ q.primeFactors.card * (2 + 2 * |t| / σ) := by
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    rw [this] at ht
    norm_num at ht
  rw [LFunction_one_eq hs1, norm_mul, mul_comm]
  exact mul_le_mul (norm_E0_le q (by simp; linarith)) (norm_zeta_le_strip hσ hσ2 ht) (norm_nonneg _)
    (by positivity)

/-- For `q ≥ 1`, `σ ≥ 1/2` and `|t| ≥ 2`, `|L(σ + it, χ₀)| ≤ 2^{ω(q)}(2 + 4|t| + |ζ(3/2)|)`. -/
lemma norm_L1_le_right {q : ℕ} [NeZero q] {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (ht : 2 ≤ |t|) :
    ‖LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)‖ ≤
      2 ^ q.primeFactors.card * (2 + 4 * |t| + ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖) := by
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    rw [this] at ht
    norm_num at ht
  have hz : ‖riemannZeta (σ + t * I)‖ ≤ 2 + 4 * |t| + ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ := by
    rcases le_or_gt σ 2 with h2 | h2
    · have h := norm_zeta_le_strip (by linarith) h2 ht
      have : 2 * |t| / σ ≤ 4 * |t| := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [abs_nonneg t]
      linarith [norm_nonneg (riemannZeta ((3 / 2 : ℝ) : ℂ))]
    · have h := HalfPlaneLindelof.norm_zeta_le_three_halves (s := σ + t * I) (by simp; linarith)
      linarith [abs_nonneg t]
  rw [LFunction_one_eq hs1, norm_mul, mul_comm]
  exact mul_le_mul (norm_E0_le q (by simp; linarith)) hz (norm_nonneg _) (by positivity)

/-- For `M ≥ 0`, a bound `M(1 + |y + τ|)^{−2}` for `|y| ≥ 2`, with continuity on the rectangle `[a, b] × [−2, 2]`,
gives one for every `y`. -/
lemma bound_of_far {G : ℂ → ℂ} {a b M τ : ℝ} (hM : 0 ≤ M)
    (hc : ContinuousOn (fun p : ℝ × ℝ => G (p.1 + p.2 * I)) (Icc a b ×ˢ Icc (-2) 2))
    (hfar : ∀ x ∈ Icc a b, ∀ y : ℝ, 2 ≤ |y| → ‖G (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x ∈ Icc a b, ∀ y : ℝ, ‖G (x + y * I)‖ ≤ M' * ((1 + |y + τ|) ^ 2)⁻¹ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨M + |C| * (3 + |τ|) ^ 2, by positivity, fun x hx y => ?_⟩
  have hpos : 0 < (1 + |y + τ|) ^ 2 := by positivity
  rcases le_or_gt 2 |y| with hy | hy
  · refine (hfar x hx y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hmem : (x, y) ∈ Icc a b ×ˢ Icc (-2 : ℝ) 2 := ⟨hx, abs_le.1 hy.le⟩
    have h1 := hC (x, y) hmem
    have hyt : 1 + |y + τ| ≤ 3 + |τ| := by
      have := abs_add_le y τ
      linarith
    have h2 : (1 + |y + τ|) ^ 2 ≤ (3 + |τ|) ^ 2 := pow_le_pow_left₀ (by positivity) hyt 2
    calc ‖G (x + y * I)‖ ≤ |C| := h1.trans (le_abs_self C)
      _ = |C| * (3 + |τ|) ^ 2 * ((3 + |τ|) ^ 2)⁻¹ := by field_simp
      _ ≤ |C| * (3 + |τ|) ^ 2 * ((1 + |y + τ|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hpos h2) (by positivity)
      _ ≤ (M + |C| * (3 + |τ|) ^ 2) * ((1 + |y + τ|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (by positivity)

/-- Continuity on a rectangle from differentiability at its points. -/
lemma continuousOn_rect {G : ℂ → ℂ} {a b : ℝ} (h : ∀ x ∈ Icc a b, ∀ y ∈ Icc (-2 : ℝ) 2,
    DifferentiableAt ℂ G (x + y * I)) :
    ContinuousOn (fun p : ℝ × ℝ => G (p.1 + p.2 * I)) (Icc a b ×ˢ Icc (-2) 2) := by
  intro p hp
  have hinner : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) p := by fun_prop
  exact (ContinuousAt.comp (g := G) (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
    (h p.1 hp.1 p.2 hp.2).continuousAt hinner).continuousWithinAt

variable {q : ℕ} [NeZero q]

lemma differentiableAt_G1_one (τ : ℝ) {N : ℝ} (hN : 0 < N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (G1 (1 : DirichletCharacter ℂ q) τ N) s :=
  ((differentiableAt_LFunction _ s (Or.inl hs)).mul (differentiableAt_H_shift τ s)).mul
    (differentiable_cpow_const hN s)

/-- **`G₁` at `χ₀` on `1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2`**: for `q ≥ 1` and `N > 0`, `|G₁(x + iy)| ≤ M(1 + |y + τ|)^{−2}`.
-/
lemma G1_one_far (τ : ℝ) {N : ℝ} (hN : 0 < N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (1 / 2 : ℝ) 2, ∀ y : ℝ, 2 ≤ |y| →
      ‖G1 (1 : DirichletCharacter ℂ q) τ N (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := H_shift_bound 0 (S := 2) (by norm_num)
  refine ⟨2 ^ q.primeFactors.card * 4 * (1 + |τ|) * B * (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)), by positivity,
    fun x hx y hy => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hL := norm_L1_le_strip (q := q) (by linarith : (0 : ℝ) < x) hx2 hy
  have hL' : ‖LFunction (1 : DirichletCharacter ℂ q) (x + y * I)‖ ≤
      2 ^ q.primeFactors.card * (4 * ((1 + |τ|) * (1 + |y + τ|))) := by
    refine hL.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h1 : 2 * |y| / x ≤ 4 * |y| := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg y]
    have h2 := one_add_abs_le y τ
    nlinarith [abs_nonneg y]
  have hHb := hB x y τ (by rw [abs_of_pos (by linarith)]; linarith)
  have hNb : ‖(N : ℂ) ^ ((x : ℂ) + y * I)‖ ≤ N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
    have : ((x : ℂ) + y * I).re = x := by simp
    rw [this]
    exact rpow_le_add_ends hN hx1 hx2
  have hu : 0 < 1 + |y + τ| := by positivity
  unfold G1
  rw [norm_mul, norm_mul]
  calc ‖LFunction (1 : DirichletCharacter ℂ q) (x + y * I)‖ * ‖H (x + y * I + τ * I)‖ *
        ‖(N : ℂ) ^ ((x : ℂ) + y * I)‖
      ≤ (2 ^ q.primeFactors.card * (4 * ((1 + |τ|) * (1 + |y + τ|)))) * (B * ((1 + |y + τ|) ^ (0 + 3))⁻¹) *
          (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)) := by gcongr
    _ = 2 ^ q.primeFactors.card * 4 * (1 + |τ|) * B * (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)) *
          ((1 + |y + τ|) * ((1 + |y + τ|) ^ 3)⁻¹) := by ring
    _ = 2 ^ q.primeFactors.card * 4 * (1 + |τ|) * B * (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)) *
          ((1 + |y + τ|) ^ 2)⁻¹ := by
        congr 1
        field_simp

/-! ### Across the pole -/

/-- **The shift across the pole**: for `q ≥ 1` and `N > 0`, at `χ₀`, `∫_{(2)}G₁ − ∫_{(1/2)}G₁ = 2πR` with
`R = E₀(1)H(1 + iτ)N`, the integrals over `v` with `s = σ + iv`. -/
theorem shift_pole (τ : ℝ) {N : ℝ} (hN : 0 < N) :
    (∫ v : ℝ, G1 (1 : DirichletCharacter ℂ q) τ N ((2 : ℝ) + v * I)) -
      ∫ v : ℝ, G1 (1 : DirichletCharacter ℂ q) τ N ((1 / 2 : ℝ) + v * I) =
      2 * π * (E0 q 1 * H (1 + τ * I) * N) := by
  set R : ℂ := E0 q 1 * H (1 + τ * I) * N with hR
  set G : ℂ → ℂ := fun w => G1 (1 : DirichletCharacter ℂ q) τ N (w + 1) with hG
  obtain ⟨M, hM0, hM⟩ := G1_one_far (q := q) τ hN
  -- holomorphy off the pole
  have hdiff : ∀ w : ℂ, w ≠ 0 → DifferentiableAt ℂ G w := fun w hw =>
    (differentiableAt_G1_one τ hN (fun h => hw (by linear_combination h))).comp w
      (differentiableAt_id.add_const 1)
  have hhol : HolomorphicOn G ((Icc (-1 / 2 : ℝ) 1 ×ℂ univ) \ {0}) := fun w hw =>
    (hdiff w hw.2).differentiableWithinAt
  -- the polar part
  set g : ℂ → ℂ := fun s => E0 q s * H (s + τ * I) * (N : ℂ) ^ s with hg
  have hgd : Differentiable ℂ g := fun s =>
    ((differentiable_E0 q s).mul (differentiableAt_H_shift τ s)).mul (differentiable_cpow_const hN s)
  have hg1 : g 1 = R := by
    simp only [hg, hR, Complex.cpow_one]
  have hO : (G - fun w => R / (w - 0)) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
    have ht : Tendsto (fun w : ℂ => w + 1) (𝓝[≠] 0) (𝓝 1) := by
      have : Tendsto (fun w : ℂ => w + 1) (𝓝 0) (𝓝 (0 + 1)) := (continuous_id.add continuous_const).tendsto 0
      rw [zero_add] at this
      exact this.mono_left nhdsWithin_le_nhds
    have ha : (fun w : ℂ => riemannZeta (w + 1) - 1 / w) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) := by
      have h := (isBigO_riemannZeta_sub_one_div (F := ℂ)).comp_tendsto ht
      refine h.congr_left fun w => ?_
      simp only [Function.comp, add_sub_cancel_right]
    have hb : (fun w : ℂ => g (w + 1)) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) :=
      ((hgd 1).continuousAt.tendsto.comp ht).isBigO_one ℂ
    have hc : (fun w : ℂ => (g (w + 1) - g 1) / w) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) := by
      have hd := (hasDerivAt_iff_tendsto_slope_zero.1 (hgd 1).hasDerivAt).isBigO_one ℂ
      refine hd.congr_left fun w => ?_
      rw [smul_eq_mul, add_comm 1 w, div_eq_inv_mul]
    have hab : (fun w : ℂ => (riemannZeta (w + 1) - 1 / w) * g (w + 1)) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) := by
      simpa using ha.mul hb
    have hsum := hab.add hc
    refine (hsum.congr' ?_ (Eventually.of_forall fun _ => by simp)).trans (isBigO_refl _ _)
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := Set.mem_compl_singleton_iff.1 hw
    have hw1 : w + 1 ≠ 1 := fun h => hw0 (by linear_combination h)
    simp only [Pi.sub_apply, hG, G1, LFunction_one_eq hw1, sub_zero]
    rw [← hg1]
    simp only [hg]
    field_simp
    ring
  -- integrability on the two lines and decay
  have hfarG : ∀ x ∈ Icc (-1 / 2 : ℝ) 1, ∀ y : ℝ, 2 ≤ |y| → ‖G (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹ := by
    intro x hx y hy
    have e : (x : ℂ) + y * I + 1 = ((x + 1 : ℝ) : ℂ) + y * I := by push_cast; ring
    simp only [hG]
    rw [e]
    exact hM (x + 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩ y hy
  have hline : ∀ x : ℝ, x ∈ Icc (-1 / 2 : ℝ) 1 → x ≠ 0 → Integrable fun t : ℝ => G (x + t * I) := by
    intro x hx hx0
    have hd : ∀ y : ℝ, DifferentiableAt ℂ G (x + y * I) := fun y => hdiff _ (by
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hx0 this)
    have hc : ContinuousOn (fun p : ℝ × ℝ => G (p.1 + p.2 * I)) (Icc x x ×ˢ Icc (-2) 2) :=
      continuousOn_rect fun x' hx' y _ => by rw [show x' = x by linarith [hx'.1, hx'.2]]; exact hd y
    obtain ⟨M', hM'0, hM'⟩ := bound_of_far hM0 hc fun x' hx' y hy => by
      rw [show x' = x by linarith [hx'.1, hx'.2]]
      exact hfarG x hx y hy
    exact integrable_of_bound (continuous_line hd) (hM' x ⟨le_rfl, le_rfl⟩)
  have hint1 := hline 1 ⟨by norm_num, le_rfl⟩ (by norm_num)
  have hint2 := hline (-1 / 2) ⟨le_rfl, by norm_num⟩ (by norm_num)
  have hdec : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc (-1 / 2 : ℝ) 1, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η := by
    intro η hη
    refine ⟨max 2 (|τ| + M / η + 1), fun x hx y hy => (hfarG x hx y (le_trans (le_max_left _ _) hy)).trans ?_⟩
    have hy' : |τ| + M / η + 1 ≤ |y| := le_trans (le_max_right _ _) hy
    have h0 : |y| ≤ |y + τ| + |τ| := by
      calc |y| = |(y + τ) + (-τ)| := by ring_nf
        _ ≤ |y + τ| + |-τ| := abs_add_le _ _
        _ = |y + τ| + |τ| := by rw [abs_neg]
    have h1 : M / η + 1 ≤ 1 + |y + τ| := by linarith
    have h2 : 1 + |y + τ| ≤ (1 + |y + τ|) ^ 2 := by nlinarith [abs_nonneg (y + τ)]
    have hpos : 0 < (1 + |y + τ|) ^ 2 := by positivity
    rw [mul_inv_le_iff₀ hpos]
    have h3 : M = η * (M / η) := by field_simp
    have h4 : 0 ≤ M / η := div_nonneg hM0 hη.le
    nlinarith
  have key := LinnikGamma.verticalIntegral_sub_eq (G := G) (σ' := -1 / 2) (σ := 1) (by norm_num) (by norm_num)
    R hhol hO hint1 hint2 hdec
  unfold VerticalIntegral at key
  have e1 : (fun t : ℝ => G ((1 : ℝ) + t * I)) =
      fun v : ℝ => G1 (1 : DirichletCharacter ℂ q) τ N ((2 : ℝ) + v * I) := by
    funext v
    simp only [hG]
    congr 1
    push_cast
    ring
  have e2 : (fun t : ℝ => G ((-1 / 2 : ℝ) + t * I)) =
      fun v : ℝ => G1 (1 : DirichletCharacter ℂ q) τ N ((1 / 2 : ℝ) + v * I) := by
    funext v
    simp only [hG]
    congr 1
    push_cast
    ring
  rw [e1, e2, smul_eq_mul, smul_eq_mul, ← mul_sub] at key
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have := mul_left_cancel₀ hI (key.trans (by ring : 2 * ↑π * I * R = I * (2 * π * R)))
  exact this

/-! ### The rest, from `Re s = 1/2` to `Re s = −K` -/

/-- The rest at `χ₀`, `G₁ − Mn`. -/
def Rt0 (τ N : ℝ) (Z : ℕ) (s : ℂ) : ℂ :=
  G1 (1 : DirichletCharacter ℂ q) τ N s - Mn (1 : DirichletCharacter ℂ q) τ N Z s

/-- For `q ≥ 1`, `Re s < 1` and `s ≠ 0`, the rest is `Cf(s)(L(1 − s, χ₀) − Σ_{m≤Z}χ₀(m)m^{s−1})`. -/
lemma Rt0_eq (τ N : ℝ) (Z : ℕ) {s : ℂ} (hs : s.re < 1) (hs0 : s ≠ 0) :
    Rt0 (q := q) τ N Z s = LinnikCGLReflect.Cf (1 : DirichletCharacter ℂ q) τ N s *
      (LFunction (1 : DirichletCharacter ℂ q)⁻¹ (1 - s) - dualS (1 : DirichletCharacter ℂ q)⁻¹ Z s) := by
  unfold Rt0 G1 Mn LinnikCGLReflect.Cf
  rw [LFunction_reflected0 (1 : DirichletCharacter ℂ q) hs hs0]
  ring

lemma differentiableAt_Rt0 (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (Rt0 (q := q) τ N Z) s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  exact (differentiableAt_G1_one τ hN hs1).sub (differentiableAt_Mn _ τ hN Z hs)

/-- **The rest on `−K ≤ Re s ≤ 1/2`**: for `q ≥ 1`, `N > 0` and `K ≥ 1`, `|Rt₀(x + iy)| ≤ M(1 + |y + τ|)^{−2}`. -/
lemma Rt0_bound (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-(K : ℝ)) (1 / 2), ∀ y : ℝ,
      ‖Rt0 (q := q) τ N Z (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹ := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  obtain ⟨C, hC0, hC⟩ := LinnikCGLReflect.Cf_bound (1 : DirichletCharacter ℂ q) τ hN hK
  set Lc : ℝ := 2 ^ q.primeFactors.card * (6 + ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖) + Z with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  refine bound_of_far (G := Rt0 (q := q) τ N Z) (M := C * Lc * (1 + |τ|) ^ (K + 2)) (by positivity)
    (continuousOn_rect fun x hx y _ => differentiableAt_Rt0 τ hN Z (by simp; linarith [hx.2]))
    fun x hx y hy => ?_
  obtain ⟨hx1, hx2⟩ := hx
  set s : ℂ := x + y * I with hs
  have hsre : s.re = x := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hs] at this
    rw [this] at hy
    norm_num at hy
  rw [Rt0_eq τ N Z (by rw [hsre]; linarith) hs0, norm_mul]
  have h1s : (1 : ℂ) - s = ((1 - x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hLb : ‖LFunction (1 : DirichletCharacter ℂ q)⁻¹ (1 - s)‖ ≤
      2 ^ q.primeFactors.card * (2 + 4 * |y| + ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖) := by
    rw [inv_one, h1s]
    have h := norm_L1_le_right (q := q) (σ := 1 - x) (t := -y) (by linarith) (by rw [abs_neg]; exact hy)
    rwa [abs_neg] at h
  have hSb := norm_dualS_le (1 : DirichletCharacter ℂ q)⁻¹ Z (s := s) (by rw [hsre]; linarith)
  have hy1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hfac : ‖LFunction (1 : DirichletCharacter ℂ q)⁻¹ (1 - s) - dualS (1 : DirichletCharacter ℂ q)⁻¹ Z s‖ ≤
      Lc * (1 + |y|) := by
    refine (norm_sub_le _ _).trans ?_
    have hz0 : 0 ≤ ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ := norm_nonneg _
    have hA : 2 + 4 * |y| + ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ ≤
        (6 + ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖) * (1 + |y|) := by nlinarith [abs_nonneg y]
    have hB : (Z : ℝ) ≤ Z * (1 + |y|) := le_mul_of_one_le_right (Nat.cast_nonneg Z) hy1
    calc ‖LFunction (1 : DirichletCharacter ℂ q)⁻¹ (1 - s)‖ + ‖dualS (1 : DirichletCharacter ℂ q)⁻¹ Z s‖
        ≤ 2 ^ q.primeFactors.card * ((6 + ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖) * (1 + |y|)) + Z * (1 + |y|) :=
          add_le_add (hLb.trans (mul_le_mul_of_nonneg_left hA (by positivity))) (hSb.trans hB)
      _ = Lc * (1 + |y|) := by rw [hLc]; ring
  have hCb := hC x ⟨hx1, hx2⟩ y
  have hu1 : (1 : ℝ) ≤ 1 + |y + τ| := by linarith [abs_nonneg (y + τ)]
  have hyτ := one_add_abs_le y τ
  have hpow : (1 + |y|) ^ (K + 2) ≤ ((1 + |τ|) * (1 + |y + τ|)) ^ (K + 2) := pow_le_pow_left₀ (by positivity) hyτ _
  calc ‖LinnikCGLReflect.Cf (1 : DirichletCharacter ℂ q) τ N s‖ *
        ‖LFunction (1 : DirichletCharacter ℂ q)⁻¹ (1 - s) - dualS (1 : DirichletCharacter ℂ q)⁻¹ Z s‖
      ≤ (C * (1 + |y|) ^ (K + 1) * ((1 + |y + τ|) ^ (K + 5))⁻¹) * (Lc * (1 + |y|)) :=
        mul_le_mul hCb hfac (norm_nonneg _) (by positivity)
    _ = C * Lc * (1 + |y|) ^ (K + 2) * ((1 + |y + τ|) ^ (K + 5))⁻¹ := by ring
    _ ≤ C * Lc * ((1 + |τ|) * (1 + |y + τ|)) ^ (K + 2) * ((1 + |y + τ|) ^ (K + 5))⁻¹ := by gcongr
    _ = C * Lc * (1 + |τ|) ^ (K + 2) * ((1 + |y + τ|) ^ (K + 2) * ((1 + |y + τ|) ^ (K + 5))⁻¹) := by
        rw [mul_pow]; ring
    _ = C * Lc * (1 + |τ|) ^ (K + 2) * ((1 + |y + τ|) ^ 3)⁻¹ := by
        have hx : (1 + |y + τ|) ^ (K + 5) = (1 + |y + τ|) ^ (K + 2) * (1 + |y + τ|) ^ 3 := by rw [← pow_add]
        have hne : (1 + |y + τ|) ^ (K + 2) ≠ 0 := by positivity
        rw [hx, mul_inv, ← mul_assoc ((1 + |y + τ|) ^ (K + 2)), mul_inv_cancel₀ hne, one_mul]
    _ ≤ C * Lc * (1 + |τ|) ^ (K + 2) * ((1 + |y + τ|) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ hu1 (by norm_num : 2 ≤ 3)))
          (by positivity)

/-! ### The reflection at `χ₀` -/

/-- **The principal reflection**: at `χ₀`, for `q ≥ 1`, `N > 0`, `Z ≥ 0` and `K ≥ 1`,
`∫_{(2)}G₁ = 2πR + ∫_{(1/2)}Mn + ∫_{(−K)}Tl` with `R = E₀(1)H(1 + iτ)N`, the integrals over `v` with `s = σ + iv`. -/
theorem reflect_gram0 (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∫ v : ℝ, G1 (1 : DirichletCharacter ℂ q) τ N ((2 : ℝ) + v * I) =
      2 * π * (E0 q 1 * H (1 + τ * I) * N) +
        ((∫ v : ℝ, Mn (1 : DirichletCharacter ℂ q) τ N Z ((1 / 2 : ℝ) + v * I)) +
          ∫ v : ℝ, Tl (1 : DirichletCharacter ℂ q) τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I)) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 := shift_pole (q := q) τ hN
  obtain ⟨M₂, hM₂, hb₂⟩ := Rt0_bound (q := q) τ hN Z hK
  obtain ⟨M₃, hM₃, hb₃⟩ := Mn_bound (1 : DirichletCharacter ℂ q) τ hN Z hK
  have hhalf : (1 / 2 : ℝ) ∈ Icc (-(K : ℝ)) (1 / 2) := ⟨by linarith, le_rfl⟩
  have hre : ∀ v : ℝ, (((1 / 2 : ℝ) : ℂ) + v * I).re < 1 := fun v => by simp; norm_num
  have hRt_int : Integrable fun v : ℝ => Rt0 (q := q) τ N Z ((1 / 2 : ℝ) + v * I) :=
    integrable_of_bound (continuous_line fun v => differentiableAt_Rt0 τ hN Z (hre v)) (hb₂ _ hhalf)
  have hMn_int : Integrable fun v : ℝ => Mn (1 : DirichletCharacter ℂ q) τ N Z ((1 / 2 : ℝ) + v * I) :=
    integrable_of_bound (continuous_line fun v => differentiableAt_Mn _ τ hN Z (hre v)) (hb₃ _ hhalf)
  have h2 : ∫ v : ℝ, G1 (1 : DirichletCharacter ℂ q) τ N ((1 / 2 : ℝ) + v * I) =
      (∫ v : ℝ, Mn (1 : DirichletCharacter ℂ q) τ N Z ((1 / 2 : ℝ) + v * I)) +
        ∫ v : ℝ, Rt0 (q := q) τ N Z ((1 / 2 : ℝ) + v * I) := by
    rw [← integral_add hMn_int hRt_int]
    exact integral_congr_ae (Eventually.of_forall fun v => by unfold Rt0; ring)
  have h3 : ∫ v : ℝ, Rt0 (q := q) τ N Z ((1 / 2 : ℝ) + v * I) =
      ∫ v : ℝ, Rt0 (q := q) τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I) :=
    shift_of_bound (G := Rt0 (q := q) τ N Z) (σ' := -(K : ℝ)) (σ := 1 / 2) (by linarith) hM₂
      (fun z _ hz2 => differentiableAt_Rt0 τ hN Z (by linarith)) hb₂
  have h4 : ∫ v : ℝ, Rt0 (q := q) τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I) =
      ∫ v : ℝ, Tl (1 : DirichletCharacter ℂ q) τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I) := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have hre' : (((-(K : ℝ) : ℝ) : ℂ) + v * I).re = -(K : ℝ) := by simp
    have hs0 : ((-(K : ℝ) : ℝ) : ℂ) + v * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      rw [hre'] at this
      simp at this
      linarith
    show Rt0 τ N Z _ = _
    rw [Rt0_eq τ N Z (by rw [hre']; linarith) hs0, LFunction_sub_dualS _ Z (by rw [hre']; linarith)]
    rfl
  rw [← h4, ← h3, ← h2]
  linear_combination h1

/-- **The principal Gram entries reflected**: for `q ≥ 1`, `χ_i = χ_k`, `N > 0`, `Z ≥ 0` and `K ≥ 1`, with
`τ = t_i − t_k`, `G(i, k) = N^{iτ}(R + (2π)⁻¹(∫_{(1/2)}Mn + ∫_{(−K)}Tl))` at `χ₀`, with `R = E₀(1)H(1 + iτ)N`. -/
theorem gram_reflect0 {ι : Type*} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {i k : ι}
    (hik : χ i = χ k) (Z : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    gramP N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) *
      (E0 q 1 * H (1 + ((t i - t k : ℝ) : ℂ) * I) * N + (1 / (2 * π) : ℂ) *
        ((∫ v : ℝ, Mn (1 : DirichletCharacter ℂ q) (t i - t k) N Z ((1 / 2 : ℝ) + v * I)) +
          ∫ v : ℝ, Tl (1 : DirichletCharacter ℂ q) (t i - t k) N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I))) := by
  have h1 : χ i * (χ k)⁻¹ = 1 := by rw [hik, mul_inv_cancel]
  rw [perron_gram hN (σ := 2) (by norm_num) χ t i k, h1]
  have h := reflect_gram0 (q := q) (t i - t k) hN Z hK
  have e : (∫ v : ℝ, LFunction (1 : DirichletCharacter ℂ q) ((2 : ℝ) + v * I) *
      H ((2 : ℝ) + v * I + ((t i - t k : ℝ) : ℂ) * I) * (N : ℂ) ^ (((2 : ℝ) : ℂ) + v * I)) =
      ∫ v : ℝ, G1 (1 : DirichletCharacter ℂ q) (t i - t k) N ((2 : ℝ) + v * I) := rfl
  rw [e, h]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  congr 1
  field_simp

/-- **A principal Gram entry, bounded through its reflection**: for `q ≥ 1`, `χ_i = χ_k`, `N > 0` and `Z, K ≥ 1`,
with `τ = t_i − t_k`, `|G(i, k)| ≤ N|H(1 + iτ)| + (2π)⁻¹(N^{1/2}Q₀(q)∫|H(1/2 + iu)||D(u)| du + T_K)`, where
`D(u) = Σ_{m≤Z}χ₀(m)m^{−1/2+i(u−τ)}` and `T_K` is the bound of round 642's `norm_integral_Tl_le`. -/
theorem norm_gram_le0 {ι : Type*} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {i k : ι}
    (hik : χ i = χ k) {Z K : ℕ} (hZ : 1 ≤ Z) (hK : 1 ≤ K) :
    ‖gramP N χ t i k‖ ≤ N * ‖H (1 + ((t i - t k : ℝ) : ℂ) * I)‖ + (2 * Real.pi)⁻¹ * (N ^ (1 / 2 : ℝ) * Q0 q *
        (∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ *
          ‖dualS (1 : DirichletCharacter ℂ q)⁻¹ Z ((1 / 2 : ℝ) + (u - ((t i - t k : ℝ) : ℂ)) * I)‖) +
      2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N * Z) ^ (-(K : ℝ)) * (1 + |t i - t k|) ^ (K + 1) * IK K) := by
  rw [gram_reflect0 hN χ t hik Z hK, norm_mul]
  have h1 : ‖(N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]; simp
  have h2 : ‖(1 / (2 * π) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    have e : (1 / (2 * π) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  have hR : ‖E0 q 1 * H (1 + ((t i - t k : ℝ) : ℂ) * I) * (N : ℂ)‖ ≤ N * ‖H (1 + ((t i - t k : ℝ) : ℂ) * I)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hN.le]
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (norm_E0_one_le q)
      (norm_nonneg (H (1 + ((t i - t k : ℝ) : ℂ) * I)))) hN.le
    linarith
  rw [h1, one_mul]
  refine (norm_add_le _ _).trans (add_le_add hR ?_)
  rw [norm_mul, h2]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
  · exact norm_integral_Mn_le (1 : DirichletCharacter ℂ q) (t i - t k) hN Z
  · exact norm_integral_Tl_le (1 : DirichletCharacter ℂ q) (t i - t k) hN hZ hK

end LinnikCGLRefl0

#print axioms LinnikCGLRefl0.LFunction_reflected0
#print axioms LinnikCGLRefl0.norm_zeta_le_strip
#print axioms LinnikCGLRefl0.shift_pole
#print axioms LinnikCGLRefl0.reflect_gram0
#print axioms LinnikCGLRefl0.norm_gram_le0
