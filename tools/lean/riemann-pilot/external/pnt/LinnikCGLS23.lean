/-
# Round 639: the off-diagonal of the cubic trace as Chen–Gupta–Li's `S₂ + S₃` (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 638's hypothesis `LinnikCGLMat.CGLThird` bounds `X`, the cubic trace of the points' Gram matrix `G` without its
diagonal. This file splits it into two hypotheses, one for each of the paper's Propositions 6.1 and 11.1.

Plain statement (`X3_eq`). With `E` the off-diagonal part of `G` and `μ` its constant diagonal,
`X = 3μ‖E‖_F² + tr(E³)`, where `‖E‖_F² = Σ_{i≠k}|G(i, k)|²` (`frobOff`) and `tr(E³)` is the real part of
`Σ G(i, j)G(j, k)G(k, i)` over the triples of distinct points (`tri3`): a triple that is not all equal either has
exactly two equal points, `G(i, i)G(i, k)G(k, i) = μ|G(i, k)|²` in each of three positions, or has none.

Plain statement (`CGLS2`, a hypothesis). For every `ε > 0` there is `C ≥ 0` such that, under the conditions of
`CGLThird`, `‖E‖_F² ≤ C(qTN)^ε·qT|R|N^{2−2σ}`.

Plain statement (`CGLS3`, a hypothesis). For every `ε > 0` there is `C ≥ 0` such that, under the same conditions,
`S₃ = X − 3μ₀‖E‖_F² ≤ C(qTN)^ε((qT)²|R|^{3/2} + qT|R|N^{3−2σ} + qT|R|²N^{3/2−σ} + (qT)^{9/8}|R|^{29/16}N^{3/2−σ})`,
with `μ₀ = (φ(q)/q)N∫w²` (`mu0`, the integral over `[1, 2]`, outside which `w` vanishes).

Plain statement (`third_of_s23`). The two imply `CGLThird`, since `X = 3μ₀‖E‖_F² + S₃` and `0 ≤ μ₀ ≤ N`; so
`linnik_225c_s23` and `linnik_226c_s23` give Linnik's exponents `9/4` and `226/100` from them.

Why their paper implies the two. Round 638's header shows that at one point per character `Z′ = S₁ = 0`, so that
`X = S₂ + S₃` (their (5.2)). Their proof of Proposition 6.1 concludes
"S₂ = 3ϕ(q)N³ĥ₀(0)/q³ Σ_{m₁,m₂≠0} Σ_{(t₁,χ₁)≠(t₂,χ₂)} Σ_{a₁,a₂ mod q, (a₁a₂,q)=1} χ₁χ̄₂(a₁)χ₂χ̄₁(a₂)e_q(a₁m₁ + a₂m₂)
· ĥ_{t₁−t₂}(Nm₁/q)ĥ_{t₂−t₁}(Nm₂/q) + O_ϵ((qT)^{−10})", where the error term is their bound for "the terms with
t₁ ≠ t₃", among the triples with `χ₁ = χ₃` that orthogonality leaves, and one point per character excludes those
terms. The sum factors as `F(1, 2)F(2, 1)`, with
`F(1, 2) = Σ_{m≠0} Σ_a χ₁χ̄₂(a)e_q(am)ĥ_{t₁−t₂}(Nm/q)`. This is the whole of the right side of their (6.1),
"q/N Σ_{n∈ℤ} h_t(n/N)χ(n) = Σ_{a mod q} χ(a) Σ_{m∈ℤ} e_q(am)ĥ_t(Nm/q)", at `t = t₁ − t₂` and `χ = χ₁χ̄₂`, since its
term `m = 0` vanishes for `χ₁ ≠ χ₂`; and with `h_t(u) = w(u)²u^{it}`,
`Σ_n h_{t₁−t₂}(n/N)χ₁χ̄₂(n) = N^{−i(t₁−t₂)}G(1, 2)`.
So `F(1, 2)F(2, 1) = (q/N)²|G(1, 2)|²`, `S₂ = 3μ₀‖E‖_F²` with `μ₀ = φ(q)Nĥ₀(0)/q`, `ĥ₀(0) = ∫w²`, and
`S₃ = X − 3μ₀‖E‖_F²`. Their Proposition 6.1, "S₂ ⪅_ϵ qT|W|N^{3−2σ}", gives `CGLS2`, since `μ₀ ≥ (3/5)(φ(q)/q)N`
(`w = 1` on `[6/5, 9/5]`) and `q/φ(q) ≪_δ q^δ` for every `δ > 0`. Their Proposition 11.1, for
`(qT)^{2/3}/2 ≤ N ≤ qT`, "S₃ ⪅ (qT)²|W|^{3/2} + qT|W|N^{3−2σ} + qT|W|²N^{3/2−σ} + (qT)^{9/8}|W|^{29/16}N^{3/2−σ}", gives
`CGLS3`. Both hold for bounded `qT` too: there `‖E‖_F²` and `|S₃|` are bounded, both vanish when `R` is empty, and
for `R` not empty the right sides are at least a positive constant, since `N ≥ 1/2`.

* `gramP_swap`: `G(k, i) = conj G(i, k)`.
* `split_triple`: a not-all-equal triple has two equal points in one of three positions, or none.
* `X3_eq`: `X = 3μ‖E‖_F² + tr(E³)`.
* `mu0_nonneg`, `mu0_le`: `0 ≤ μ₀ ≤ N`.
* `third_of_s23`: `CGLS2` and `CGLS3` imply `CGLThird`, with the constant `3C₂ + C₃`.

The file imports `LinnikCGLMat.lean`.
-/

import LinnikCGLMat

open Complex Real Finset

noncomputable section

namespace LinnikCGLS23

open DirichletCharacter LinnikCGLMat

/-- The Gram matrix is Hermitian: `G(k, i) = conj G(i, k)`. -/
lemma gramP_swap {ι : Type*} {q : ℕ} (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) :
    gramP N χ t k i = star (gramP N χ t i k) := by
  unfold gramP
  rw [star_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [star_mul', star_star, mul_comm]

/-- **The off-diagonal mass** `‖E‖_F² = Σ_{i≠k}|G(i, k)|²`. -/
def frobOff {ι : Type*} [DecidableEq ι] {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) : ℝ :=
  ∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else ‖gramP N χ t i k‖ ^ 2

/-- **The triples of distinct points**: `tr(E³) = Re Σ G(i, j)G(j, k)G(k, i)` over `i, j, k` pairwise distinct. -/
def tri3 {ι : Type*} [DecidableEq ι] {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) : ℝ :=
  (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
    if i ≠ j ∧ j ≠ k ∧ k ≠ i then gramP N χ t i j * gramP N χ t j k * gramP N χ t k i else 0).re

lemma frobOff_nonneg {ι : Type*} [DecidableEq ι] {q : ℕ} (N : ℝ) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) : 0 ≤ frobOff N R χ t :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The not-all-equal triples: two equal points in one of three positions, or three distinct points. -/
lemma split_triple {ι : Type*} [DecidableEq ι] (P : ι → ι → ι → ℂ) (i j k : ι) :
    (if i = j ∧ j = k then (0 : ℂ) else P i j k) =
      (if i = j ∧ j ≠ k then P i j k else 0) + (if j = k ∧ k ≠ i then P i j k else 0) +
      (if k = i ∧ i ≠ j then P i j k else 0) + (if i ≠ j ∧ j ≠ k ∧ k ≠ i then P i j k else 0) := by
  by_cases h1 : i = j <;> by_cases h2 : j = k <;> by_cases h3 : k = i <;> simp_all

/-- **The cubic trace's off-diagonal**: `X = 3μ‖E‖_F² + tr(E³)`. -/
theorem X3_eq {ι : Type*} [DecidableEq ι] {q : ℕ} {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) :
    X3 N R χ t = 3 * muP q N * frobOff N R χ t + tri3 N R χ t := by
  have hdiag : ∀ i, gramP N χ t i i = (muP q N : ℂ) := gramP_diag hN χ t
  have hsq : ∀ i k, gramP N χ t i k * gramP N χ t k i = ((‖gramP N χ t i k‖ ^ 2 : ℝ) : ℂ) := by
    intro i k
    rw [gramP_swap N χ t i k, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold X3 tri3
  set G := gramP N χ t with hG
  set μ := muP q N with hμ
  set c : ι → ι → ℂ := fun i k => (μ : ℂ) * ((‖G i k‖ ^ 2 : ℝ) : ℂ) with hc
  have hF : (μ : ℂ) * ((frobOff N R χ t : ℝ) : ℂ) = ∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else c i k := by
    unfold frobOff
    rw [Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp [hc, hG]
  -- the pattern `i = j ≠ k`: the sum over `j` collapses to `j = i`
  have s1 : ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if i = j ∧ j ≠ k then G i j * G j k * G k i else 0) =
      ∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else c i k := by
    refine sum_congr rfl fun i hi => ?_
    rw [sum_eq_single i]
    · refine sum_congr rfl fun k _ => ?_
      by_cases hk : i = k
      · simp [hk]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hk⟩), ite_eq_right_of_eq_false _ _ (eq_false hk), hdiag,
          mul_assoc, hsq]
    · intro j _ hji
      exact sum_eq_zero fun k _ => ite_eq_right_of_eq_false _ _ (eq_false fun h => hji h.1.symm)
    · intro h; exact absurd hi h
  -- the pattern `j = k ≠ i`: the sum over `k` collapses to `k = j`
  have s2 : ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if j = k ∧ k ≠ i then G i j * G j k * G k i else 0) =
      ∑ i ∈ R, ∑ j ∈ R, if i = j then 0 else c i j := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
    rw [sum_eq_single j]
    · by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, Ne.symm hij⟩), ite_eq_right_of_eq_false _ _ (eq_false hij),
          hdiag, hc]
        dsimp only
        rw [← hsq i j]
        ring
    · intro k _ hkj
      exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hkj h.1.symm)
    · intro h; exact absurd hj h
  -- the pattern `k = i ≠ j`: the sum over `k` collapses to `k = i`
  have s3 : ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if k = i ∧ i ≠ j then G i j * G j k * G k i else 0) =
      ∑ i ∈ R, ∑ j ∈ R, if i = j then 0 else c i j := by
    refine sum_congr rfl fun i hi => sum_congr rfl fun j _ => ?_
    rw [sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hij⟩), ite_eq_right_of_eq_false _ _ (eq_false hij), hdiag,
          hc]
        dsimp only
        rw [← hsq i j]
        ring
    · intro k _ hki
      exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hki h.1)
    · intro h; exact absurd hi h
  have hsum : (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, if i = j ∧ j = k then (0 : ℂ) else G i j * G j k * G k i) =
      3 * ((μ : ℂ) * ((frobOff N R χ t : ℝ) : ℂ)) +
      ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if i ≠ j ∧ j ≠ k ∧ k ≠ i then G i j * G j k * G k i else 0) := by
    have e : (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, if i = j ∧ j = k then (0 : ℂ) else G i j * G j k * G k i) =
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if i = j ∧ j ≠ k then G i j * G j k * G k i else 0) +
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if j = k ∧ k ≠ i then G i j * G j k * G k i else 0) +
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if k = i ∧ i ≠ j then G i j * G j k * G k i else 0) +
        ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if i ≠ j ∧ j ≠ k ∧ k ≠ i then G i j * G j k * G k i else 0) := by
      simp only [← sum_add_distrib]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
        split_triple (fun i j k => G i j * G j k * G k i) i j k
    rw [e, s1, s2, s3, hF]
    ring
  rw [hsum, Complex.add_re]
  have e3 : (3 * ((μ : ℂ) * ((frobOff N R χ t : ℝ) : ℂ))).re = 3 * μ * frobOff N R χ t := by
    rw [show (3 : ℂ) * ((μ : ℂ) * ((frobOff N R χ t : ℝ) : ℂ)) = ((3 * μ * frobOff N R χ t : ℝ) : ℂ) by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [e3]

/-! ### The two hypotheses -/

/-- `μ₀ = (φ(q)/q)N∫w²`, the integral over `[1, 2]`: the term `m = 0` of the diagonal's Poisson expansion. -/
def mu0 (q : ℕ) (N : ℝ) : ℝ := (q.totient : ℝ) / q * N * ∫ u in (1 : ℝ)..2, wCGL u ^ 2

lemma integral_w_sq_nonneg : 0 ≤ ∫ u in (1 : ℝ)..2, wCGL u ^ 2 :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => by positivity

lemma integral_w_sq_le_one : ∫ u in (1 : ℝ)..2, wCGL u ^ 2 ≤ 1 := by
  have hc : Continuous fun u => wCGL u ^ 2 := (wBump.continuous).pow 2
  calc ∫ u in (1 : ℝ)..2, wCGL u ^ 2 ≤ ∫ _u in (1 : ℝ)..2, (1 : ℝ) := by
        refine intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
          intervalIntegrable_const fun u _ => ?_
        have h0 := wCGL_nonneg u
        have h1 := wCGL_le_one u
        nlinarith
    _ = 1 := by norm_num

lemma mu0_nonneg (q : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ mu0 q N := by
  unfold mu0
  have := integral_w_sq_nonneg
  positivity

lemma mu0_le (q : ℕ) [NeZero q] {N : ℝ} (hN : 0 ≤ N) : mu0 q N ≤ N := by
  unfold mu0
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hφ : (q.totient : ℝ) / q ≤ 1 := by
    rw [div_le_one hq]; exact_mod_cast Nat.totient_le q
  have hφ0 : 0 ≤ (q.totient : ℝ) / q := by positivity
  have hI0 := integral_w_sq_nonneg
  have hI1 := integral_w_sq_le_one
  calc (q.totient : ℝ) / q * N * ∫ u in (1 : ℝ)..2, wCGL u ^ 2 ≤ 1 * N * 1 := by gcongr
    _ = N := by ring

/-- **Chen–Gupta–Li's `S₃` at one point per character**: `X − 3μ₀‖E‖_F²`. -/
def S3 {ι : Type*} [DecidableEq ι] (q : ℕ) (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) : ℝ :=
  X3 N R χ t - 3 * mu0 q N * frobOff N R χ t

/-- **The `S₂` hypothesis** (their Proposition 6.1 at one point per character, divided by `3μ₀`): for every
`ε > 0` there is `C ≥ 0` such that, under the conditions of `CGLThird`, `‖E‖_F² ≤ C(qTN)^ε·qT|R|N^{2−2σ}`. -/
def CGLS2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} [DecidableEq ι] (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    Set.InjOn χ R → (∀ i ∈ R, (χ i).IsPrimitive) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N → N ≤ (q : ℝ) * T →
    (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) → (∀ n, ‖b n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
    (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    frobOff N R χ t ≤ C * ((q : ℝ) * T * N) ^ ε * ((q : ℝ) * T * R.card * N ^ (2 - 2 * σ))

/-- **The `S₃` hypothesis** (their Proposition 11.1 at one point per character): for every `ε > 0` there is `C ≥ 0`
such that, under the conditions of `CGLThird`,
`S₃ ≤ C(qTN)^ε((qT)²|R|^{3/2} + qT|R|N^{3−2σ} + qT|R|²N^{3/2−σ} + (qT)^{9/8}|R|^{29/16}N^{3/2−σ})`. -/
def CGLS3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} [DecidableEq ι] (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    Set.InjOn χ R → (∀ i ∈ R, (χ i).IsPrimitive) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N → N ≤ (q : ℝ) * T →
    (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) → (∀ n, ‖b n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
    (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    S3 q N R χ t ≤ C * ((q : ℝ) * T * N) ^ ε * (((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) +
      (q : ℝ) * T * R.card * N ^ (3 - 2 * σ) + (q : ℝ) * T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) +
      ((q : ℝ) * T) ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ))

/-- **`CGLThird` from the two hypotheses**: `X = 3μ₀‖E‖_F² + S₃` with `0 ≤ μ₀ ≤ N`, and `qT|R|N^{3−2σ}` is one of
`S₃`'s terms. -/
theorem third_of_s23 (h2 : CGLS2) (h3 : CGLS3) : CGLThird := by
  intro ε hε
  obtain ⟨C₂, hC₂0, hC₂⟩ := h2 ε hε
  obtain ⟨C₃, hC₃0, hC₃⟩ := h3 ε hε
  refine ⟨3 * C₂ + C₃, by positivity, ?_⟩
  intro q _ ι _ R χ t T N σ S b hinj hprim hT hσ1 hσ2 hN hNq hS hb ht hbig
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hN0 : 0 < N := by
    have : (1 : ℝ) ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    linarith
  have hF := hC₂ q R χ t T N σ S b hinj hprim hT hσ1 hσ2 hN hNq hS hb ht hbig
  have h3' := hC₃ q R χ t T N σ S b hinj hprim hT hσ1 hσ2 hN hNq hS hb ht hbig
  have hF0 := frobOff_nonneg N R χ t
  have hm0 := mu0_nonneg q hN0.le
  have hm1 := mu0_le q hN0.le
  set E := ((q : ℝ) * T * N) ^ ε with hE
  have hE0 : 0 ≤ E := by positivity
  set A := ((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) with hA
  set B := (q : ℝ) * T * R.card * N ^ (3 - 2 * σ) with hB
  set Cc := (q : ℝ) * T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) with hCc
  set D := ((q : ℝ) * T) ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) with hD
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hCc0 : 0 ≤ Cc := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hN3 : 0 ≤ N ^ 3 := by positivity
  have hNB : N * ((q : ℝ) * T * R.card * N ^ (2 - 2 * σ)) = B := by
    rw [hB, show (3 - 2 * σ) = 1 + (2 - 2 * σ) by ring, Real.rpow_add hN0, Real.rpow_one]; ring
  have hS2 : 3 * mu0 q N * frobOff N R χ t ≤ 3 * C₂ * E * B := by
    calc 3 * mu0 q N * frobOff N R χ t ≤ 3 * N * (C₂ * E * ((q : ℝ) * T * R.card * N ^ (2 - 2 * σ))) := by
          gcongr
      _ = 3 * C₂ * E * (N * ((q : ℝ) * T * R.card * N ^ (2 - 2 * σ))) := by ring
      _ = 3 * C₂ * E * B := by rw [hNB]
  have hX : X3 N R χ t = 3 * mu0 q N * frobOff N R χ t + S3 q N R χ t := by unfold S3; ring
  rw [hX]
  calc 3 * mu0 q N * frobOff N R χ t + S3 q N R χ t ≤ 3 * C₂ * E * B + C₃ * E * (A + B + Cc + D) :=
        add_le_add hS2 h3'
    _ ≤ (3 * C₂ + C₃) * E * (N ^ 3 + A + B + Cc + D) := by
        have h1 : 3 * C₂ * E * B ≤ 3 * C₂ * E * (N ^ 3 + A + B + Cc + D) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h2 : C₃ * E * (A + B + Cc + D) ≤ C₃ * E * (N ^ 3 + A + B + Cc + D) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        nlinarith

/-- **Linnik's theorem with exponent `9/4` from the `S₂` and `S₃` hypotheses.** -/
theorem linnik_225c_s23 (h2 : CGLS2) (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  linnik_225c_third (third_of_s23 h2 h3)

/-- **Linnik's theorem with exponent `226/100` from the `S₂` and `S₃` hypotheses.** -/
theorem linnik_226c_s23 (h2 : CGLS2) (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  linnik_226c_third (third_of_s23 h2 h3)

end LinnikCGLS23

#print axioms LinnikCGLS23.X3_eq
#print axioms LinnikCGLS23.mu0_le
#print axioms LinnikCGLS23.third_of_s23
#print axioms LinnikCGLS23.linnik_225c_s23
#print axioms LinnikCGLS23.linnik_226c_s23
