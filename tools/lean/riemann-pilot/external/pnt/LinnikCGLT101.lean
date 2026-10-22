/-
# Round 670: their Theorem 10.1 (Heath-Brown) displayed, and their Lemma 10.6 (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Theorem 10.1: "Let T be a set of pairs (t,χ), where χ is a primitive character modulo q and t is a real number
with |t| ≤ T such that for (t,χ) ≠ (t′,χ′) either χ ≠ χ′ or |t−t′| ≥ 1. Then Σ_{(t₁,χ₁),(t₂,χ₂)∈T} |Σ_{n∼N}
c_nχ₁(n)χ̄₂(n)n^{i(t₁−t₂)}|² ⪅ (|T|N² + |T|²N + |T|^{5/4}(qT)^{1/2}N) max_{n∼N} |c_n|²." (text layer lines 4618–4635;
spaces restored; the sums, large bars, subscripts and exponents transcribed; the first `T` is their calligraphic set).
The bar over `χ₂`, which the text layer drops, is a rule at y = 438.6 spanning x = 220.3–227.7 over the `χ` at x =
220.3–227.7 in the row y = 429.5 on PDF page 40 (pdfminer; `scratchpad/r670/probe/p40_all.txt`). Their notation: "we
write A ⪅ B to indicate that for any ϵ > 0, there exists a constant C(ϵ) > 0, depending only on ϵ, such that A ≤
C(ϵ)(qT)^ϵ B for all sufficiently large qT." (lines 279–281; spaces restored, the exponent transcribed), and "A ∼ B
signifies the stronger condition B < A ≤ 2B" (lines 278–279; spaces restored).

`CGLT101` displays it, not proved here (the plan's stage M5), with its implicit constants explicit: for every
`ε > 0` there are `C` and `Q₀` such that, for `qT ≥ Q₀`, `T, M ≥ 1`, points `(t_i, χ_i)` with `χ_i` primitive modulo
`q`, `|t_i| ≤ T` and `χ_i ≠ χ_j` or `|t_i − t_j| ≥ 1` for `i ≠ j`, and `|c_n| ≤ B` on `M < n ≤ 2M`,
`Σ_{i,j}|Σ_{M<n≤2M}c_nχ_i(n)χ̄_j(n)n^{i(t_i−t_j)}|² ≤ C(qTM)^ε(|P|M² + |P|²M + |P|^{5/4}(qT)^{1/2}M)B²`. Their
theorem implies it: `(qT)^ε ≤ (qTM)^ε` for `M ≥ 1`, and the hypotheses `T, M ≥ 1` only restrict it. The factor
`(qTM)^ε` keeps the displayed form safe for `M` beyond `qT`; round 672's `group_le` applies it at a modulus `q₁ ∣ q`
and a height `T′`, where `M` can exceed `q₁T′`. It costs nothing for `M ≤ qT`, where it is at most `(qT)^{2ε}`.

Their Lemma 10.6: "For any M ≥ 1, we have Σ_{n₁,n₂∼M, (n₁n₂,q)=1} |R(n₁/n₂, n₁n₂^{−1})|² ⪅ |W|M² + |W|²M +
|W|^{5/4}(qT)^{1/2}M." (lines 4767–4778; spaces restored; the sum, fraction, large bars, large parentheses, subscripts
and exponents transcribed), by expanding the square and "Applying Theorem 10.1" (line 4813). With round 669's `R₂`,
the expansion is exact: `Σ_{n₁,n₂}|R₂(n₁, n₂)|² = Σ_{i,j}|Σ_nχ_i(n)χ̄_j(n)n^{i(t_i−t_j)}|²` (`sum_sq_R2_eq`). At one
point per character the separation holds because the characters differ.

Plain statements, with `n ∼ M` the naturals `M < n ≤ 2M` (`dyad`).
* `mem_dyad`: for `M ≥ 0`, `n ∈ dyad M ↔ M < n ≤ 2M`.
* `sum_sq_R2_eq`: `Σ_{n₁,n₂∼M}|R₂(n₁, n₂)|² = Σ_{i,j∈R}|Σ_{n∼M}χ_i(n)χ̄_j(n)n^{i(t_i−t_j)}|²`.
* `lemma106`: from `CGLT101`, for every `ε > 0` there are `C` and `Q₀` such that, for `qT ≥ Q₀`, `T, M ≥ 1`, `χ`
  injective on `R` with primitive values and `|t_i| ≤ T`,
  `Σ_{n₁,n₂∼M}|R₂(n₁, n₂)|² ≤ C(qTM)^ε(|R|M² + |R|²M + |R|^{5/4}(qT)^{1/2}M)`.

* `dyad`, `mem_dyad`, `CGLT101`: the hypothesis.
* `sum_sq_R2_eq`, `lemma106`: their Lemma 10.6.

The file imports `LinnikCGLL105.lean`.
-/

import LinnikCGLL105

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLT101

open LinnikCGLL105

/-! ### The hypothesis -/

/-- `n ∼ M`: the naturals `M < n ≤ 2M`. -/
def dyad (M : ℝ) : Finset ℕ := Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊

lemma mem_dyad {M : ℝ} (hM : 0 ≤ M) {n : ℕ} : n ∈ dyad M ↔ M < n ∧ (n : ℝ) ≤ 2 * M := by
  unfold dyad
  rw [Finset.mem_Ioc, Nat.floor_lt hM, Nat.le_floor_iff (by positivity)]

/-- **Their Theorem 10.1 (Heath-Brown), as a displayed hypothesis** (not proved here): for every `ε > 0` there are `C`
and `Q₀` such that, for `qT ≥ Q₀`, `T, M ≥ 1`, points with primitive characters modulo `q`, `|t_i| ≤ T` and
`χ_i ≠ χ_j` or `|t_i − t_j| ≥ 1` for `i ≠ j`, and `|c_n| ≤ B` on `n ∼ M`,
`Σ_{i,j}|Σ_{n∼M}c_nχ_i(n)χ̄_j(n)n^{i(t_i−t_j)}|² ≤ C(qTM)^ε(|P|M² + |P|²M + |P|^{5/4}(qT)^{1/2}M)B²`. -/
def CGLT101 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C Q₀ : ℝ, ∀ (q : ℕ) [NeZero q] {ι : Type} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (T M B : ℝ) (c : ℕ → ℂ),
    Q₀ ≤ (q : ℝ) * T → 1 ≤ T → 1 ≤ M → (∀ i ∈ P, (χ i).IsPrimitive) → (∀ i ∈ P, |t i| ≤ T) →
    (∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) → (∀ n ∈ dyad M, ‖c n‖ ≤ B) →
    ∑ i ∈ P, ∑ j ∈ P, ‖∑ n ∈ dyad M, c n * χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I)‖ ^ 2 ≤
      C * ((q : ℝ) * T * M) ^ ε * ((P.card : ℝ) * M ^ 2 + (P.card : ℝ) ^ 2 * M +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) * B ^ 2

/-! ### Their Lemma 10.6 -/

section R2

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- **The square of `R₂`, expanded**: `Σ_{n₁,n₂∈S}|R₂(n₁, n₂)|² = Σ_{i,j}|Σ_{n∈S}χ_i(n)χ̄_j(n)n^{i(t_i−t_j)}|²` for `S`
of positive integers. -/
theorem sum_sq_R2_eq (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 2 =
      ∑ i ∈ R, ∑ j ∈ R, ‖∑ n ∈ S, χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I)‖ ^ 2 := by
  -- `a_i(n) = χ_i(n)e^{it_i log n}`
  set a : ι → ℕ → ℂ := fun i n => χ i n * cexp (↑(t i * Real.log n) * I) with ha
  have ec : ∀ x : ℝ, conj (cexp (↑x * I)) = cexp (↑(-x) * I) := fun x => by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  have ee : ∀ x y : ℝ, cexp (↑x * I) * cexp (↑y * I) = cexp (↑(x + y) * I) := fun x y => by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hR2 : ∀ n₁ n₂, R2 R χ t n₁ n₂ = ∑ i ∈ R, a i n₁ * conj (a i n₂) := fun n₁ n₂ => by
    unfold R2
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha, map_mul, ec]
    have e2 : cexp (↑(t i * (Real.log n₁ - Real.log n₂)) * I) =
        cexp (↑(t i * Real.log n₁) * I) * cexp (↑(-(t i * Real.log n₂)) * I) := by
      rw [ee]
      congr 3
      ring
    rw [e2]
    ring
  have hpow : ∀ i j, ∀ n ∈ S, χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I) =
      a i n * conj (a j n) := by
    intro i j n hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    simp only [ha, map_mul, ec]
    have e3 : cexp (↑(Real.log n) * (↑(t i - t j) * I)) =
        cexp (↑(t i * Real.log n) * I) * cexp (↑(-(t j * Real.log n)) * I) := by
      rw [ee]
      congr 1
      push_cast
      ring
    rw [e3]
    ring
  -- `|z|² = z·z̄`, expanded on both sides
  have hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * conj z := fun z => by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  have hL : ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 2 =
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖∑ i ∈ R, a i n₁ * conj (a i n₂)‖ ^ 2 := by
    simp only [hR2]
  have hRt : ∑ i ∈ R, ∑ j ∈ R, ‖∑ n ∈ S, χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I)‖ ^ 2 =
      ∑ i ∈ R, ∑ j ∈ R, ‖∑ n ∈ S, a i n * conj (a j n)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (hpow i j)]
  rw [hL, hRt]
  apply Complex.ofReal_injective
  push_cast
  simp only [hsq, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  -- both sides are `Σ_{n₁,n₂}Σ_{i,j}a_i(n₁)ā_i(n₂)ā_j(n₁)a_j(n₂)`, in different orders
  simp_rw [Finset.sum_comm (s := R) (t := S)]
  refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end R2

/-- **Their Lemma 10.6, at one point per character**: from `CGLT101`, for every `ε > 0` there are `C` and `Q₀` such
that, for `qT ≥ Q₀`, `T, M ≥ 1`, `χ` injective on `R` with primitive values and `|t_i| ≤ T`,
`Σ_{n₁,n₂∼M}|R₂(n₁, n₂)|² ≤ C(qTM)^ε(|R|M² + |R|²M + |R|^{5/4}(qT)^{1/2}M)`. -/
theorem lemma106 (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) :
    ∃ C Q₀ : ℝ, ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
      (T M : ℝ), Q₀ ≤ (q : ℝ) * T → 1 ≤ T → 1 ≤ M → (∀ i ∈ R, (χ i).IsPrimitive) → Set.InjOn χ R →
      (∀ i ∈ R, |t i| ≤ T) →
      ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖R2 R χ t n₁ n₂‖ ^ 2 ≤
        C * ((q : ℝ) * T * M) ^ ε * ((R.card : ℝ) * M ^ 2 + (R.card : ℝ) ^ 2 * M +
          (R.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) := by
  obtain ⟨C, Q₀, hCQ⟩ := hT ε hε
  refine ⟨C, Q₀, ?_⟩
  intro q hq0 ι R χ t T M hQ hT1 hM hprim hinj ht
  have hpos : ∀ n ∈ dyad M, 0 < n := fun n hn => by
    have := ((mem_dyad (by linarith)).mp hn).1
    exact_mod_cast (by linarith : (0 : ℝ) < n)
  have hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j| := fun i hi j hj hij =>
    Or.inl fun h => hij (hinj hi hj h)
  have h := hCQ q R χ t T M 1 (fun _ => 1) hQ hT1 hM hprim ht hsep (fun n _ => by simp)
  rw [sum_sq_R2_eq R χ t (dyad M) hpos]
  simp only [one_mul, one_pow, mul_one] at h
  exact h

end LinnikCGLT101

#print axioms LinnikCGLT101.sum_sq_R2_eq
#print axioms LinnikCGLT101.lemma106
