/-
# Round 638: Chen–Gupta–Li's Proposition 3.1 from a bound on the cubic trace (the CGL plan's stage M3, first step)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`CGLThird`, a hypothesis). For points `(t_i, χ_i)`, `i ∈ R`, with distinct primitive characters
`χ_i` mod `q`, let `G(i, j) = Σ_n A_{i,n}conj(A_{j,n})` with `A_{i,n} = w(n/N)χ_i(n)n^{it_i}` over the integers
`⌈N⌉ ≤ n ≤ ⌊2N⌋`, `w` the weight below, and let `X = Re Σ G(i, j)G(j, k)G(k, i)` over the triples of `R` that are not
all equal (`X3`). The hypothesis: for every `ε > 0` there is `C ≥ 0` such that, under the conditions of
`LinnikCGLLV.CGLProp31` and `N ≤ qT`,
`X ≤ C(qTN)^ε(N³ + (qT)²|R|^{3/2} + qT|R|N^{3−2σ} + qT|R|²N^{3/2−σ} + (qT)^{9/8}|R|^{29/16}N^{3/2−σ})`.

Why their paper implies it. Their matrix (4.1), `M_{(t,χ),n} = w(n/N)χ(n)n^{it}` for `n ∼ N`, is `A` up to a zero
column, so `MM*` is `G`. The proof of their Lemma 4.5 writes `tr((MM∗)³)`, which is `Σ G(i, j)G(j, k)G(k, i)` over
all triples, as `Z + Z′ + Σ_{m⃗∈Z³\{0}} I_m⃗`. Here `Z`, "the term coming from (t₁,χ₁) = (t₂,χ₂) = (t₃,χ₃)", is
`|R|μ³` by their Lemma 4.4. Of `Z′` they write "Since Σ_{a mod q} χ(a) = 0 unless χ = χ₀, we have that
χ₁ = χ₂ = χ₃". At one point per character that makes the three points equal, which `Z′`'s triples exclude, so `Z′ = 0`
and `X = Σ_{m⃗≠0} I_m⃗ = S₁ + S₂ + S₃` (their (5.2)). The proof of their Proposition 5.1 restricts `S₁` to
`χ₁ = χ₂ = χ₃` in the same way, so `S₁ = 0`. Their §11.2 combines their Propositions 5.1, 6.1 and 11.1 (the last
stated for `(qT)^{2/3}/2 ≤ N ≤ qT`) as
`N³ + S₁ + S₂ + S₃ ⪅_ϵ N³ + (qT)²|W|^{3/2} + qT|W|N^{3−2σ} + qT|W|²N^{3/2−σ} + (qT)^{9/8}|W|^{29/16}N^{3/2−σ}`, where
(their §1.1) `A ⪅ B` means that for any `ϵ > 0`, `A ≤ C(ϵ)(qT)^ϵB` for all sufficiently large `qT`. That is the
hypothesis for large `qT`, since `(qT)^ϵ ≤ 2^ϵ(qTN)^ϵ` for `N ≥ 1/2`. For bounded `qT`, `|R| ≤ q ≤ qT` and
`|X| ≤ |R|³(N + 1)³` are bounded while `N³ ≥ 1/8`.

Plain statement (`prop31_of_third`). The hypothesis implies `LinnikCGLLV.CGLProp31`, so `linnik_225c_third` and
`linnik_226c_third` give Linnik's exponents `9/4` and `226/100` from it.

* `wCGL`: Mathlib's `ContDiffBump` at `3/2` with radii `3/10` and `1/2`: smooth, `0` outside `(1, 2)` and `1` on
  `[6/5, 9/5]`, as their §3 asks of `w`, with values in `[0, 1]`.
* `refined_moment_points`: round 537's `LinnikMoment.refined_moment_cube` for the matrix `A`, whose Gram matrix has
  the constant diagonal `μ = Σ w(n/N)²` over the columns prime to `q`. It bounds `Σ_{i∈R}|D(i)|²` directly, so it does
  the work of their Lemmas 4.1 and 4.2 together.
* `prop46`: their Proposition 4.6 for the points, in a cubed form. With the coefficients `b_n1_S(n)`, for which
  `w(n/N) = 1`, either `|R|N^{2σ} ≤ 648N²` or `(|R|N^{2σ})³ ≤ (216N)³X`.
* `mvt_case`, `polylog_le`: for `N ≥ max(qT, 10)`, the mean value theorem at one point per character
  (`LinnikPoints.large_values_points`) gives `|R|N^{2σ} ≤ 36N²(11 + 8 log N)(2 + log²(2N))`, at most
  `36(11 + 24/ε)(2 + 36/ε²)N^{2+ε}` for `0 < ε ≤ 1`.
* `le_of_cube_le`, `dom4`, `dom5`, `alg112`: their §11.2's algebra. The terms `qT|R|²N^{3/2−σ}` and
  `(qT)^{9/8}|R|^{29/16}N^{3/2−σ}` give `|R|` at most `qTN^{9/2−7σ}` and `(qT)^{18/19}N^{(72−112σ)/19}`, each up to a
  constant factor. Each of these is at most `(qT)^{1/2}N^{3−4σ}` for `N ≥ (qT)^{5/6}` and `(qT)^{4/3}N^{2−4σ}` for
  `N ≤ (qT)^{5/6}` (`dom4`, `dom5`), with equality at `σ = 7/10`, `N = (qT)^{5/6}`.
* `prop31_of_third`: `prop46` and `alg112` for `N ≤ qT`, `mvt_case` for `N ≥ max(qT, 10)`, and at most `q < 10`
  characters for `qT < N < 10`.

The file imports `LinnikCGLLinnik.lean`, `LinnikMoment.lean` and `LinnikPoints.lean`.
-/

import LinnikCGLLinnik
import LinnikMoment
import LinnikPoints

open Complex Real Finset

noncomputable section

namespace LinnikCGLMat

open DirichletCharacter LinnikMoment Matrix

/-! ### The weight -/

/-- The bump of the weight: centre `3/2`, radii `3/10` and `1/2`. -/
def wBump : ContDiffBump (3 / 2 : ℝ) := ⟨3 / 10, 1 / 2, by norm_num, by norm_num⟩

/-- **The weight** of Chen–Gupta–Li's §3: smooth, `1` on `[6/5, 9/5]`, `0` outside `(1, 2)`, in `[0, 1]`. -/
def wCGL (u : ℝ) : ℝ := wBump u

lemma wCGL_nonneg (u : ℝ) : 0 ≤ wCGL u := wBump.nonneg

lemma wCGL_le_one (u : ℝ) : wCGL u ≤ 1 := wBump.le_one

lemma wCGL_one {u : ℝ} (h1 : 6 / 5 ≤ u) (h2 : u ≤ 9 / 5) : wCGL u = 1 := by
  refine wBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  simp only [wBump]
  constructor <;> linarith

lemma wCGL_zero {u : ℝ} (h : u ≤ 1 ∨ 2 ≤ u) : wCGL u = 0 := by
  refine wBump.zero_of_le_dist ?_
  rw [Real.dist_eq]
  simp only [wBump]
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma wCGL_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wCGL := wBump.contDiff

/-! ### The matrix -/

/-- The columns: the integers `⌈N⌉ ≤ n ≤ ⌊2N⌋`. -/
def colsP (N : ℝ) : Finset ℕ := Icc ⌈N⌉₊ ⌊2 * N⌋₊

/-- The entries `A_{i,n} = w(n/N)χ_i(n)n^{it_i}`. -/
def entP {ι : Type*} {q : ℕ} (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i : ι) (n : ℕ) : ℂ :=
  (wCGL (n / N) : ℂ) * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)

/-- The Gram matrix `G(i, j) = Σ_n A_{i,n}conj(A_{j,n})`. -/
def gramP {ι : Type*} {q : ℕ} (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i j : ι) : ℂ :=
  ∑ n ∈ colsP N, entP N χ t i n * star (entP N χ t j n)

/-- **The off-diagonal of the cubic trace**: `X = Re Σ G(i, j)G(j, k)G(k, i)` over the triples of `R` that are not
all equal. -/
def X3 {ι : Type*} [DecidableEq ι] {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) :
    ℝ :=
  (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
    if i = j ∧ j = k then 0 else gramP N χ t i j * gramP N χ t j k * gramP N χ t k i).re

/-- The diagonal `μ = Σ w(n/N)²` over the columns prime to `q`. -/
def muP (q : ℕ) (N : ℝ) : ℝ := ∑ n ∈ (colsP N).filter (fun n : ℕ => n.Coprime q), wCGL (n / N) ^ 2

lemma colsP_pos {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n ∈ colsP N) : 0 < n := by
  have h1 : ⌈N⌉₊ ≤ n := (mem_Icc.1 hn).1
  have h2 : 0 < ⌈N⌉₊ := Nat.ceil_pos.2 hN
  omega

lemma norm_cpow_I {n : ℕ} (hn : 0 < n) (x : ℝ) : ‖(n : ℂ) ^ ((x : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- The Gram matrix has the constant diagonal `μ`. -/
lemma gramP_diag {ι : Type*} {q : ℕ} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i : ι) :
    gramP N χ t i i = (muP q N : ℂ) := by
  classical
  unfold gramP muP
  rw [Complex.ofReal_sum, sum_filter]
  refine sum_congr rfl fun n hn => ?_
  have hn0 := colsP_pos hN hn
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold entP
  rw [norm_mul, norm_mul, norm_cpow_I hn0, mul_one, Complex.norm_real, Real.norm_of_nonneg (wCGL_nonneg _)]
  split_ifs with hc
  · obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n q).2 hc
    have h1 : ‖χ i n‖ = 1 := by rw [← hu]; exact DirichletCharacter.unit_norm_eq_one (χ i) u
    rw [h1, mul_one]
  · rw [MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h))]; simp

/-- **The moment inequality for the points** (`LinnikMoment.refined_moment_cube` for the matrix `A`): with
`D(i) = Σ_n A_{i,n}b_n` and `β = Σ_n |b_n|²` over the columns, if `Σ_{i∈R}|D(i)|² ≥ μβ`, then
`(Σ_{i∈R}|D(i)|² − μβ)³ ≤ β³X`. -/
theorem refined_moment_points {ι : Type*} [DecidableEq ι] {q : ℕ} {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (b : ℕ → ℂ)
    (hge : muP q N * (∑ n ∈ colsP N, ‖b n‖ ^ 2) ≤ ∑ i ∈ R, ‖∑ n ∈ colsP N, entP N χ t i n * b n‖ ^ 2) :
    (∑ i ∈ R, ‖∑ n ∈ colsP N, entP N χ t i n * b n‖ ^ 2 - muP q N * (∑ n ∈ colsP N, ‖b n‖ ^ 2)) ^ 3 ≤
      (∑ n ∈ colsP N, ‖b n‖ ^ 2) ^ 3 * X3 N R χ t := by
  classical
  set μ := muP q N with hμ
  set cols := colsP N with hcols
  have hdiag : ∀ i, gramP N χ t i i = (μ : ℂ) := gramP_diag hN χ t
  let A : Matrix R cols ℂ := fun i n => entP N χ t i.1 n.1
  let b' : cols → ℂ := fun n => b n.1
  have hl : nsq (A *ᵥ b') = ∑ i ∈ R, ‖∑ n ∈ cols, entP N χ t i n * b n‖ ^ 2 := by
    simp only [nsq, Matrix.mulVec, dotProduct, A, b']
    rw [← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_coe_sort cols (fun n => entP N χ t i n * b n)]
  have hb : nsq b' = ∑ n ∈ cols, ‖b n‖ ^ 2 := by
    simp only [nsq, b']
    exact Finset.sum_coe_sort cols (fun n => ‖b n‖ ^ 2)
  have hG : ∀ i j : R, (A * Aᴴ) i j = gramP N χ t i.1 j.1 := by
    intro i j
    simp only [A, gramP]
    exact Finset.sum_coe_sort cols (fun n => entP N χ t i n * star (entP N χ t j n))
  have ht : (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace =
      ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, gramP N χ t i j * gramP N χ t j k * gramP N χ t k i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.sum_mul]
    rw [← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_coe_sort R]
  have htr1 : (A * Aᴴ).trace.re = Fintype.card R * μ := by
    simp only [Matrix.trace, Matrix.diag, hG, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [Complex.mul_re]
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun _ _ => by positivity
  have key := refined_moment_cube A b' μ hμ0 htr1 (by rw [hl, hb]; exact hge)
  rw [hl, hb, ht, sum_triples_split R, Complex.add_re] at key
  simp only [hdiag, Fintype.card_coe] at key
  have hdiag3 : (∑ a ∈ R, (μ : ℂ) * (μ : ℂ) * (μ : ℂ)).re = R.card * μ ^ 3 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have e : (R.card : ℂ) * ((μ : ℂ) * (μ : ℂ) * (μ : ℂ)) = ((R.card * μ ^ 3 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  rw [hdiag3] at key
  unfold X3
  linarith

/-! ### Their Proposition 4.6 -/

/-- There are at most `N + 1` columns. -/
lemma card_colsP_le {N : ℝ} (hN : 0 ≤ N) : ((colsP N).card : ℝ) ≤ N + 1 := by
  unfold colsP
  rw [Nat.card_Icc]
  have h1 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
  have h2 : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
  rcases le_or_gt (⌊2 * N⌋₊ + 1) ⌈N⌉₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h]; push_cast; linarith
  · rw [Nat.cast_sub h.le]; push_cast; linarith

/-- **Their Proposition 4.6 for the points**, cubed: for `N ≥ 1/2`, `S ⊆ [6N/5, 9N/5]`, `|b_n| ≤ 1` and
`|Σ_{n∈S} b_nχ_i(n)n^{it_i}| ≥ N^σ/6` on `R`, either `|R|N^{2σ} ≤ 648N²` or `(|R|N^{2σ})³ ≤ (216N)³X`. -/
theorem prop46 {ι : Type*} [DecidableEq ι] {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {N σ : ℝ} (hN : 1 / 2 ≤ N) {S : Finset ℕ} (hS : ∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1)
    (hbig : ∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) :
    (R.card : ℝ) * (N ^ σ) ^ 2 ≤ 648 * N ^ 2 ∨
      ((R.card : ℝ) * (N ^ σ) ^ 2) ^ 3 ≤ (216 * N) ^ 3 * X3 N R χ t := by
  classical
  have hN0 : 0 < N := by linarith
  set b' : ℕ → ℂ := fun n => if n ∈ S then b n else 0 with hb'
  have hSc : S ⊆ colsP N := by
    intro n hn
    obtain ⟨h1, h2⟩ := hS n hn
    rw [colsP, mem_Icc]
    exact ⟨Nat.ceil_le.2 (by linarith), Nat.le_floor (by linarith)⟩
  have hD : ∀ i, ∑ n ∈ colsP N, entP N χ t i n * b' n =
      ∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) := by
    intro i
    rw [← sum_subset hSc (fun n _ hn => by simp [hb', hn])]
    refine sum_congr rfl fun n hn => ?_
    obtain ⟨h1, h2⟩ := hS n hn
    have hw : wCGL (n / N) = 1 :=
      wCGL_one (by rw [le_div_iff₀ hN0]; linarith) (by rw [div_le_iff₀ hN0]; linarith)
    simp only [entP, hb', hn, ↓reduceIte, hw, Complex.ofReal_one, one_mul]
    ring
  set V := ∑ i ∈ R, ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ ^ 2 with hV
  set β := ∑ n ∈ colsP N, ‖b' n‖ ^ 2 with hβ
  set μ := muP q N with hμ
  set u := N ^ σ with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hN0 σ
  have hcard := card_colsP_le hN0.le
  have hβ0 : 0 ≤ β := sum_nonneg fun _ _ => by positivity
  have hβ1 : β ≤ 3 * N := by
    calc β ≤ ∑ _n ∈ colsP N, (1 : ℝ) := by
          refine sum_le_sum fun n _ => ?_
          have : ‖b' n‖ ≤ 1 := by simp only [hb']; split_ifs; exacts [hb n, by simp]
          nlinarith [norm_nonneg (b' n)]
      _ = (colsP N).card := by simp
      _ ≤ 3 * N := by linarith
  have hμ0 : 0 ≤ μ := sum_nonneg fun _ _ => by positivity
  have hμ1 : μ ≤ 3 * N := by
    calc μ ≤ ∑ _n ∈ (colsP N).filter (fun n : ℕ => n.Coprime q), (1 : ℝ) := by
          refine sum_le_sum fun n _ => ?_
          have h1 := wCGL_le_one (n / N)
          have h0 := wCGL_nonneg (n / N)
          nlinarith
      _ = ((colsP N).filter (fun n : ℕ => n.Coprime q)).card := by simp
      _ ≤ (colsP N).card := by exact_mod_cast card_filter_le _ _
      _ ≤ 3 * N := by linarith
  have hV1 : (R.card : ℝ) * (u / 6) ^ 2 ≤ V := by
    calc (R.card : ℝ) * (u / 6) ^ 2 = ∑ _i ∈ R, (u / 6) ^ 2 := by simp
      _ ≤ V := sum_le_sum fun i hi => pow_le_pow_left₀ (by positivity) (hbig i hi) 2
  have hVD : ∑ i ∈ R, ‖∑ n ∈ colsP N, entP N χ t i n * b' n‖ ^ 2 = V := by
    simp only [hV, hD]
  by_cases hc : V ≤ 2 * (μ * β)
  · left
    have h1 : μ * β ≤ (3 * N) * (3 * N) := mul_le_mul hμ1 hβ1 hβ0 (by linarith)
    nlinarith
  · right
    push Not at hc
    have hge : μ * β ≤ V := by nlinarith [mul_nonneg hμ0 hβ0]
    have key := refined_moment_points hN0 R χ t b' (by rw [hVD]; exact hge)
    rw [hVD] at key
    have hpos : 0 < V - μ * β := by nlinarith [mul_nonneg hμ0 hβ0]
    have hX : 0 < X3 N R χ t := by
      have h1 : 0 < (V - μ * β) ^ 3 := by positivity
      have h2 : 0 < β ^ 3 * X3 N R χ t := lt_of_lt_of_le h1 key
      by_contra hneg
      push Not at hneg
      nlinarith [pow_nonneg hβ0 3]
    have h1 : (R.card : ℝ) * u ^ 2 / 72 ≤ V - μ * β := by nlinarith [mul_nonneg hμ0 hβ0]
    have h2 : ((R.card : ℝ) * u ^ 2 / 72) ^ 3 ≤ (V - μ * β) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    have h3 : β ^ 3 * X3 N R χ t ≤ (3 * N) ^ 3 * X3 N R χ t :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hβ0 hβ1 3) hX.le
    have h4 := h2.trans (key.trans h3)
    have e : ((R.card : ℝ) * u ^ 2) ^ 3 = 72 ^ 3 * ((R.card : ℝ) * u ^ 2 / 72) ^ 3 := by ring
    rw [e]
    calc 72 ^ 3 * ((R.card : ℝ) * u ^ 2 / 72) ^ 3 ≤ 72 ^ 3 * ((3 * N) ^ 3 * X3 N R χ t) := by gcongr
      _ = (216 * N) ^ 3 * X3 N R χ t := by ring

/-! ### The mean value theorem for `N ≥ qT` -/

/-- `n^{ix} = e^{−i(−x)log n}` for `n ≥ 1`, the form of `DirMean.dp`. -/
lemma natCast_cpow_I {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (n : ℂ) ^ ((x : ℂ) * I) = Complex.exp (-(I * (((-x) * Real.log n : ℝ) : ℂ))) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hn.ne')]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  push_cast; ring

/-- **The mean value theorem at one point per character** (`LinnikPoints.large_values_points`), for `N ≥ 10` and
`qT ≤ N`: `|R|N^{2σ} ≤ 36N²(11 + 8 log N)(2 + log²(2N))`. -/
theorem mvt_case {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (hinj : Set.InjOn χ R) {T N σ : ℝ} (hT : 1 ≤ T) (hqT : (q : ℝ) * T ≤ N) (hN : 10 ≤ N) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1)
    (ht : ∀ i ∈ R, |t i| ≤ T)
    (hbig : ∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) :
    (R.card : ℝ) * (N ^ σ) ^ 2 ≤ 36 * N ^ 2 * ((11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2)) := by
  classical
  have hN0 : 0 < N := by linarith
  set P := ⌊N⌋₊ with hP
  have hP1 : (P : ℝ) ≤ N := Nat.floor_le hN0.le
  have hP2 : N - 1 < (P : ℝ) := Nat.sub_one_lt_floor N
  have hP0 : (1 : ℝ) ≤ P := by linarith
  have hSP : S ⊆ Ioc P (2 * P) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hS n hn
    rw [mem_Ioc]
    constructor
    · exact_mod_cast (show (P : ℝ) < n by linarith)
    · exact_mod_cast (show (n : ℝ) ≤ 2 * P by linarith)
  have hmv := LinnikPoints.large_values_points hSP b q (lo := -T - 1 / 2) (hi := T + 1 / 2) (by linarith) R χ
    (fun i => -t i) (fun i hi => by have := abs_le.1 (ht i hi); constructor <;> linarith)
    (fun i hi j hj hij hχ => absurd (hinj hi hj hχ) hij)
  have hdp : ∀ i, DirMean.dp S (fun j => b j * χ i j) (-t i) =
      ∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) := by
    intro i
    unfold DirMean.dp
    refine sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := by
      have := (hS n hn).1
      exact_mod_cast (show (0 : ℝ) < n by linarith)
    rw [natCast_cpow_I hn0]
  simp only [hdp] at hmv
  -- the left side
  set u := N ^ σ with hu
  have hV1 : (R.card : ℝ) * (u / 6) ^ 2 ≤ ∑ i ∈ R, ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ ^ 2 := by
    calc (R.card : ℝ) * (u / 6) ^ 2 = ∑ _i ∈ R, (u / 6) ^ 2 := by simp
      _ ≤ _ := sum_le_sum fun i hi => pow_le_pow_left₀ (by positivity) (hbig i hi) 2
  -- the right side
  have hS1 : ∑ j ∈ S, ‖b j‖ ^ 2 ≤ N := by
    calc ∑ j ∈ S, ‖b j‖ ^ 2 ≤ ∑ _j ∈ S, (1 : ℝ) := sum_le_sum fun j _ => by
          nlinarith [hb j, norm_nonneg (b j)]
      _ = S.card := by simp
      _ ≤ (Ioc P (2 * P)).card := by exact_mod_cast card_le_card hSP
      _ = P := by rw [Nat.card_Ioc]; push_cast [show 2 * P - P = P by omega]; ring
      _ ≤ N := hP1
  have hlP : Real.log P ≤ Real.log N := Real.log_le_log (by linarith) hP1
  have hlP0 : 0 ≤ Real.log P := Real.log_nonneg hP0
  have hl2P : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (2 * P) ≤ Real.log (2 * N) := Real.log_le_log (by linarith) (by linarith)
  have hq : (q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) ≤ 3 * N := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hL : ((q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) ≤
      N * (11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2) := by
    have h1 : 8 * (P : ℝ) * (1 + Real.log P) ≤ 8 * N * (1 + Real.log N) := by
      have : (P : ℝ) * (1 + Real.log P) ≤ N * (1 + Real.log N) :=
        mul_le_mul hP1 (by linarith) (by linarith) hN0.le
      linarith
    have h2 : Real.log (2 * P) ^ 2 ≤ Real.log (2 * N) ^ 2 := pow_le_pow_left₀ hl2P hl2 2
    calc ((q : ℝ) * (T + 1 / 2 - (-T - 1 / 2)) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2)
        ≤ (3 * N + 8 * N * (1 + Real.log N)) * (2 + Real.log (2 * N) ^ 2) := by
          gcongr
          · nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ N by linarith)]
      _ = N * (11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2) := by ring
  have hpos : 0 ≤ N * (11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by linarith)
    positivity
  have hmain : (R.card : ℝ) * (u / 6) ^ 2 ≤ N * (11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2) * N := by
    refine hV1.trans (hmv.trans ?_)
    exact mul_le_mul hL hS1 (sum_nonneg fun _ _ => by positivity) hpos
  nlinarith

/-- `(11 + 8 log N)(2 + log²(2N)) ≤ (11 + 24/ε)(2 + 36/ε²)N^ε` for `N ≥ 1` and `0 < ε ≤ 1`. -/
lemma polylog_le {N ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2) ≤ (11 + 24 / ε) * (2 + 36 / ε ^ 2) * N ^ ε := by
  have hN0 : 0 < N := by linarith
  set e := ε / 3 with he
  have he0 : 0 < e := by positivity
  have h1 : Real.log N ≤ N ^ e / e := Real.log_le_rpow_div hN0.le he0
  have h2 : Real.log (2 * N) ≤ (2 * N) ^ e / e := Real.log_le_rpow_div (by positivity) he0
  have hl1 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hl2 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hNe : 1 ≤ N ^ e := Real.one_le_rpow hN he0.le
  have h2e : (2 * N) ^ e ≤ 2 * N ^ e := by
    rw [Real.mul_rpow (by norm_num) hN0.le]
    gcongr
    calc (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hA : 11 + 8 * Real.log N ≤ (11 + 24 / ε) * N ^ e := by
    have e3 : 8 * (N ^ e / e) = 24 / ε * N ^ e := by rw [he]; field_simp; ring
    have : 8 * Real.log N ≤ 24 / ε * N ^ e := by rw [← e3]; linarith
    have h24 : 0 ≤ 24 / ε := by positivity
    nlinarith
  have hB : Real.log (2 * N) ≤ 6 / ε * N ^ e := by
    calc Real.log (2 * N) ≤ (2 * N) ^ e / e := h2
      _ ≤ 2 * N ^ e / e := by gcongr
      _ = 6 / ε * N ^ e := by rw [he]; field_simp; ring
  have hB2 : 2 + Real.log (2 * N) ^ 2 ≤ (2 + 36 / ε ^ 2) * (N ^ e) ^ 2 := by
    have h3 : Real.log (2 * N) ^ 2 ≤ (6 / ε * N ^ e) ^ 2 := pow_le_pow_left₀ hl2 hB 2
    have h4 : (6 / ε * N ^ e) ^ 2 = 36 / ε ^ 2 * (N ^ e) ^ 2 := by field_simp; ring
    have h5 : 1 ≤ (N ^ e) ^ 2 := one_le_pow₀ hNe
    nlinarith
  have hNε : (N ^ e) * (N ^ e) ^ 2 = N ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    rw [he]; push_cast; ring_nf
  calc (11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2)
      ≤ ((11 + 24 / ε) * N ^ e) * ((2 + 36 / ε ^ 2) * (N ^ e) ^ 2) := by
        gcongr
    _ = (11 + 24 / ε) * (2 + 36 / ε ^ 2) * ((N ^ e) * (N ^ e) ^ 2) := by ring
    _ = (11 + 24 / ε) * (2 + 36 / ε ^ 2) * N ^ ε := by rw [hNε]

/-! ### Their §11.2's algebra -/

/-- `r ≤ A^{1/(3−p)}` from `r³ ≤ Ar^p`, for `r, A ≥ 0` and `p < 3`. -/
lemma le_of_cube_le {r A p : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) (hp : p < 3) (h : r ^ 3 ≤ A * r ^ p) :
    r ≤ A ^ (1 / (3 - p)) := by
  have h' : r ^ (3 : ℝ) ≤ A * r ^ p := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact h
  rcases eq_or_lt_of_le hr with h0 | h0
  · rw [← h0]; exact Real.rpow_nonneg hA _
  · have h1 : r ^ (3 - p) ≤ A := by
      rw [Real.rpow_sub h0, div_le_iff₀ (Real.rpow_pos_of_pos h0 p)]
      exact h'
    have h3 : 0 < 3 - p := by linarith
    calc r = (r ^ (3 - p)) ^ (1 / (3 - p)) := by
          rw [← Real.rpow_mul hr, mul_one_div_cancel h3.ne', Real.rpow_one]
      _ ≤ A ^ (1 / (3 - p)) := Real.rpow_le_rpow (Real.rpow_nonneg hr _) h1 (by positivity)

/-- `QN^{9/2−7σ} ≤ Q^{1/2}N^{3−4σ} + Q^{4/3}N^{2−4σ}` for `Q ≥ 1`, `N > 0` and `7/10 ≤ σ ≤ 4/5`: the first term
bounds it for `N ≥ Q^{5/6}`, the second for `N ≤ Q^{5/6}`. -/
lemma dom4 {Q N σ : ℝ} (hQ : 1 ≤ Q) (hN : 0 < N) (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 4 / 5) :
    Q * N ^ (9 / 2 - 7 * σ) ≤ Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by
  have hQ0 : 0 < Q := by linarith
  have hA : 0 ≤ Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by positivity
  have hB : 0 ≤ Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by positivity
  rcases le_total (Q ^ (5 / 6 : ℝ)) N with h | h
  · have hN1 : 1 ≤ N := le_trans (Real.one_le_rpow hQ (by norm_num)) h
    have h1 : Q ^ (1 / 2 : ℝ) ≤ N ^ (3 * σ - 3 / 2) := by
      calc Q ^ (1 / 2 : ℝ) = (Q ^ (5 / 6 : ℝ)) ^ (3 / 5 : ℝ) := by rw [← Real.rpow_mul hQ0.le]; norm_num
        _ ≤ N ^ (3 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) h (by norm_num)
        _ ≤ N ^ (3 * σ - 3 / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have e1 : Q = Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
    have e2 : N ^ (3 * σ - 3 / 2) * N ^ (9 / 2 - 7 * σ) = N ^ (3 - 4 * σ) := by
      rw [← Real.rpow_add hN]; ring_nf
    calc Q * N ^ (9 / 2 - 7 * σ) = Q ^ (1 / 2 : ℝ) * (Q ^ (1 / 2 : ℝ) * N ^ (9 / 2 - 7 * σ)) := by
          rw [← mul_assoc, ← e1]
      _ ≤ Q ^ (1 / 2 : ℝ) * (N ^ (3 * σ - 3 / 2) * N ^ (9 / 2 - 7 * σ)) := by gcongr
      _ = Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by rw [e2]
      _ ≤ _ := le_add_of_nonneg_right hB
  · have h1 : N ^ (5 / 2 - 3 * σ) ≤ Q ^ (1 / 3 : ℝ) := by
      calc N ^ (5 / 2 - 3 * σ) ≤ (Q ^ (5 / 6 : ℝ)) ^ (5 / 2 - 3 * σ) :=
            Real.rpow_le_rpow hN.le h (by linarith)
        _ = Q ^ (5 / 6 * (5 / 2 - 3 * σ)) := by rw [← Real.rpow_mul hQ0.le]
        _ ≤ Q ^ (1 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ (by nlinarith)
    have e1 : Q ^ (4 / 3 : ℝ) = Q * Q ^ (1 / 3 : ℝ) := by
      rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hQ0, Real.rpow_one]
    have e2 : N ^ (5 / 2 - 3 * σ) * N ^ (2 - 4 * σ) = N ^ (9 / 2 - 7 * σ) := by
      rw [← Real.rpow_add hN]; ring_nf
    calc Q * N ^ (9 / 2 - 7 * σ) = Q * (N ^ (5 / 2 - 3 * σ) * N ^ (2 - 4 * σ)) := by rw [e2]
      _ ≤ Q * (Q ^ (1 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by gcongr
      _ = Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by rw [e1]; ring
      _ ≤ _ := le_add_of_nonneg_left hA

/-- `Q^{18/19}N^{(72−112σ)/19} ≤ Q^{1/2}N^{3−4σ} + Q^{4/3}N^{2−4σ}` for `Q ≥ 1`, `N > 0` and `7/10 ≤ σ ≤ 4/5`, split
at `N = Q^{5/6}` as `dom4`. -/
lemma dom5 {Q N σ : ℝ} (hQ : 1 ≤ Q) (hN : 0 < N) (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 4 / 5) :
    Q ^ (18 / 19 : ℝ) * N ^ ((72 - 112 * σ) / 19) ≤
      Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by
  have hQ0 : 0 < Q := by linarith
  have hA : 0 ≤ Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by positivity
  have hB : 0 ≤ Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by positivity
  rcases le_total (Q ^ (5 / 6 : ℝ)) N with h | h
  · have hN1 : 1 ≤ N := le_trans (Real.one_le_rpow hQ (by norm_num)) h
    have h1 : Q ^ (17 / 38 : ℝ) ≤ N ^ ((36 * σ - 15) / 19) := by
      calc Q ^ (17 / 38 : ℝ) = (Q ^ (5 / 6 : ℝ)) ^ (51 / 95 : ℝ) := by rw [← Real.rpow_mul hQ0.le]; norm_num
        _ ≤ N ^ (51 / 95 : ℝ) := Real.rpow_le_rpow (by positivity) h (by norm_num)
        _ ≤ N ^ ((36 * σ - 15) / 19) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have e1 : Q ^ (18 / 19 : ℝ) = Q ^ (1 / 2 : ℝ) * Q ^ (17 / 38 : ℝ) := by
      rw [← Real.rpow_add hQ0]; norm_num
    have e2 : N ^ ((36 * σ - 15) / 19) * N ^ ((72 - 112 * σ) / 19) = N ^ (3 - 4 * σ) := by
      rw [← Real.rpow_add hN]; ring_nf
    calc Q ^ (18 / 19 : ℝ) * N ^ ((72 - 112 * σ) / 19)
        = Q ^ (1 / 2 : ℝ) * (Q ^ (17 / 38 : ℝ) * N ^ ((72 - 112 * σ) / 19)) := by rw [e1]; ring
      _ ≤ Q ^ (1 / 2 : ℝ) * (N ^ ((36 * σ - 15) / 19) * N ^ ((72 - 112 * σ) / 19)) := by gcongr
      _ = Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by rw [e2]
      _ ≤ _ := le_add_of_nonneg_right hB
  · have h1 : N ^ ((34 - 36 * σ) / 19) ≤ Q ^ (22 / 57 : ℝ) := by
      calc N ^ ((34 - 36 * σ) / 19) ≤ (Q ^ (5 / 6 : ℝ)) ^ ((34 - 36 * σ) / 19) :=
            Real.rpow_le_rpow hN.le h (by linarith)
        _ = Q ^ (5 / 6 * ((34 - 36 * σ) / 19)) := by rw [← Real.rpow_mul hQ0.le]
        _ ≤ Q ^ (22 / 57 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ (by nlinarith)
    have e1 : Q ^ (4 / 3 : ℝ) = Q ^ (18 / 19 : ℝ) * Q ^ (22 / 57 : ℝ) := by
      rw [← Real.rpow_add hQ0]; norm_num
    have e2 : N ^ ((34 - 36 * σ) / 19) * N ^ (2 - 4 * σ) = N ^ ((72 - 112 * σ) / 19) := by
      rw [← Real.rpow_add hN]; ring_nf
    calc Q ^ (18 / 19 : ℝ) * N ^ ((72 - 112 * σ) / 19)
        = Q ^ (18 / 19 : ℝ) * (N ^ ((34 - 36 * σ) / 19) * N ^ (2 - 4 * σ)) := by rw [e2]
      _ ≤ Q ^ (18 / 19 : ℝ) * (Q ^ (22 / 57 : ℝ) * N ^ (2 - 4 * σ)) := by gcongr
      _ = Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by rw [e1]; ring
      _ ≤ _ := le_add_of_nonneg_left hA

/-- **Their §11.2's algebra.** For `Q ≥ 1`, `N > 0`, `7/10 ≤ σ ≤ 4/5`, `K ≥ 1`, `r ≥ 0` and real `X`: if
`rN^{2σ} ≤ 648N²` or `(rN^{2σ})³ ≤ (216N)³X` (the two cases of `prop46`), and
`X ≤ K(N³ + Q²r^{3/2} + QrN^{3−2σ} + Qr²N^{3/2−σ} + Q^{9/8}r^{29/16}N^{3/2−σ})`, then
`r ≤ 5·216³K(N^{2−2σ} + Q^{1/2}N^{3−4σ} + Q^{4/3}N^{2−4σ})`. -/
theorem alg112 {r N Q σ K X : ℝ} (hr : 0 ≤ r) (hN : 0 < N) (hQ : 1 ≤ Q) (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 4 / 5)
    (hK : 1 ≤ K) (h46 : r * (N ^ σ) ^ 2 ≤ 648 * N ^ 2 ∨ (r * (N ^ σ) ^ 2) ^ 3 ≤ (216 * N) ^ 3 * X)
    (hX : X ≤ K * (N ^ 3 + Q ^ 2 * r ^ (3 / 2 : ℝ) + Q * r * N ^ (3 - 2 * σ) + Q * r ^ 2 * N ^ (3 / 2 - σ) +
      Q ^ (9 / 8 : ℝ) * r ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ))) :
    r ≤ 5 * 216 ^ 3 * K * (N ^ (2 - 2 * σ) + Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
      Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hM1 : (1 : ℝ) ≤ 5 * 216 ^ 3 * K := by nlinarith
  have hM0 : (0 : ℝ) ≤ 5 * 216 ^ 3 * K := by linarith
  have hb1 : 0 ≤ N ^ (2 - 2 * σ) := by positivity
  have hb2 : 0 ≤ Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by positivity
  have hb3 : 0 ≤ Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by positivity
  have hu : 0 < N ^ σ := Real.rpow_pos_of_pos hN σ
  have hMe : ∀ e : ℝ, e ≤ 1 → (5 * 216 ^ 3 * K) ^ e ≤ 5 * 216 ^ 3 * K := fun e he => by
    calc (5 * 216 ^ 3 * K) ^ e ≤ (5 * 216 ^ 3 * K) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 he
      _ = 5 * 216 ^ 3 * K := Real.rpow_one _
  rcases h46 with h | h
  · have e : N ^ (2 - 2 * σ) = N ^ 2 / (N ^ σ) ^ 2 := by
      rw [LinnikCGLLV.npow_div_rpow_pow hN 2 2 σ]; norm_num
    have h1 : r ≤ 648 * N ^ (2 - 2 * σ) := by
      rw [e, mul_div_assoc', le_div_iff₀ (by positivity)]; exact h
    have h648 : (648 : ℝ) ≤ 5 * 216 ^ 3 * K := by linarith
    calc r ≤ 648 * N ^ (2 - 2 * σ) := h1
      _ ≤ 5 * 216 ^ 3 * K * N ^ (2 - 2 * σ) := mul_le_mul_of_nonneg_right h648 hb1
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hM0
  · have e6 : N ^ (3 - 6 * σ) = N ^ 3 / (N ^ σ) ^ 6 := by
      rw [LinnikCGLLV.npow_div_rpow_pow hN 3 6 σ]; norm_num
    have hr3 : r ^ 3 ≤ 216 ^ 3 * N ^ (3 - 6 * σ) * X := by
      have h' : r ^ 3 * (N ^ σ) ^ 6 ≤ 216 ^ 3 * N ^ 3 * X := by
        calc r ^ 3 * (N ^ σ) ^ 6 = (r * (N ^ σ) ^ 2) ^ 3 := by ring
          _ ≤ (216 * N) ^ 3 * X := h
          _ = 216 ^ 3 * N ^ 3 * X := by ring
      have e : 216 ^ 3 * N ^ (3 - 6 * σ) * X = 216 ^ 3 * N ^ 3 * X / (N ^ σ) ^ 6 := by rw [e6]; ring
      rw [e, le_div_iff₀ (by positivity)]
      exact h'
    have a1 : N ^ (3 - 6 * σ) * N ^ 3 = N ^ (6 - 6 * σ) := by
      rw [← Real.rpow_natCast N 3, ← Real.rpow_add hN]; congr 1; push_cast; ring
    have a2 : N ^ (3 - 6 * σ) * N ^ (3 - 2 * σ) = N ^ (6 - 8 * σ) := by rw [← Real.rpow_add hN]; ring_nf
    have a3 : N ^ (3 - 6 * σ) * N ^ (3 / 2 - σ) = N ^ (9 / 2 - 7 * σ) := by rw [← Real.rpow_add hN]; ring_nf
    have hsum : r ^ 3 ≤ 216 ^ 3 * K * (N ^ (6 - 6 * σ) + Q ^ 2 * N ^ (3 - 6 * σ) * r ^ (3 / 2 : ℝ) +
        Q * N ^ (6 - 8 * σ) * r + Q * N ^ (9 / 2 - 7 * σ) * r ^ 2 +
        Q ^ (9 / 8 : ℝ) * N ^ (9 / 2 - 7 * σ) * r ^ (29 / 16 : ℝ)) := by
      calc r ^ 3 ≤ 216 ^ 3 * N ^ (3 - 6 * σ) * X := hr3
        _ ≤ 216 ^ 3 * N ^ (3 - 6 * σ) * (K * (N ^ 3 + Q ^ 2 * r ^ (3 / 2 : ℝ) + Q * r * N ^ (3 - 2 * σ) +
            Q * r ^ 2 * N ^ (3 / 2 - σ) + Q ^ (9 / 8 : ℝ) * r ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ))) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
        _ = _ := by rw [← a1, ← a2, ← a3]; ring
    have hcases : r ^ 3 ≤ 5 * 216 ^ 3 * K * N ^ (6 - 6 * σ) ∨
        r ^ 3 ≤ 5 * 216 ^ 3 * K * (Q ^ 2 * N ^ (3 - 6 * σ)) * r ^ (3 / 2 : ℝ) ∨
        r ^ 3 ≤ 5 * 216 ^ 3 * K * (Q * N ^ (6 - 8 * σ)) * r ^ (1 : ℝ) ∨
        r ^ 3 ≤ 5 * 216 ^ 3 * K * (Q * N ^ (9 / 2 - 7 * σ)) * r ^ (2 : ℝ) ∨
        r ^ 3 ≤ 5 * 216 ^ 3 * K * (Q ^ (9 / 8 : ℝ) * N ^ (9 / 2 - 7 * σ)) * r ^ (29 / 16 : ℝ) := by
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3, c4, c5⟩ := hc
      rw [Real.rpow_one] at c3
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at c4
      linarith
    have hB := add_nonneg (add_nonneg hb1 hb2) hb3
    rcases hcases with c | c | c | c | c
    · -- `r ≤ M N^{2−2σ}`
      have e : N ^ (6 - 6 * σ) = (N ^ (2 - 2 * σ)) ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; push_cast; ring_nf
      have hMM : 5 * 216 ^ 3 * K ≤ (5 * 216 ^ 3 * K) ^ 3 := le_self_pow₀ hM1 (by norm_num)
      have h1 : r ^ 3 ≤ (5 * 216 ^ 3 * K * N ^ (2 - 2 * σ)) ^ 3 := by
        rw [e] at c
        calc r ^ 3 ≤ 5 * 216 ^ 3 * K * (N ^ (2 - 2 * σ)) ^ 3 := c
          _ ≤ (5 * 216 ^ 3 * K) ^ 3 * (N ^ (2 - 2 * σ)) ^ 3 :=
              mul_le_mul_of_nonneg_right hMM (by positivity)
          _ = (5 * 216 ^ 3 * K * N ^ (2 - 2 * σ)) ^ 3 := by ring
      have h2 : r ≤ 5 * 216 ^ 3 * K * N ^ (2 - 2 * σ) :=
        (pow_le_pow_iff_left₀ hr (by positivity) (by norm_num)).1 h1
      calc r ≤ 5 * 216 ^ 3 * K * N ^ (2 - 2 * σ) := h2
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hM0
    · -- `r ≤ (MQ²N^{3−6σ})^{2/3}`
      have h1 := le_of_cube_le hr (by positivity) (by norm_num) c
      have e : (1 : ℝ) / (3 - 3 / 2) = 2 / 3 := by norm_num
      rw [e, Real.mul_rpow hM0 (by positivity : (0 : ℝ) ≤ Q ^ 2 * N ^ (3 - 6 * σ)),
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ Q ^ 2) (by positivity : (0 : ℝ) ≤ N ^ (3 - 6 * σ))] at h1
      have e2 : (Q ^ 2) ^ (2 / 3 : ℝ) = Q ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_natCast Q 2, ← Real.rpow_mul hQ0.le]; norm_num
      have e3 : (N ^ (3 - 6 * σ)) ^ (2 / 3 : ℝ) = N ^ (2 - 4 * σ) := by
        rw [← Real.rpow_mul hN.le]; ring_nf
      rw [e2, e3] at h1
      calc r ≤ (5 * 216 ^ 3 * K) ^ (2 / 3 : ℝ) * (Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := h1
        _ ≤ 5 * 216 ^ 3 * K * (Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) :=
            mul_le_mul_of_nonneg_right (hMe _ (by norm_num)) hb3
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hM0
    · -- `r ≤ (MQN^{6−8σ})^{1/2}`
      have h1 := le_of_cube_le hr (by positivity) (by norm_num) c
      have e : (1 : ℝ) / (3 - 1) = 1 / 2 := by norm_num
      rw [e, Real.mul_rpow hM0 (by positivity : (0 : ℝ) ≤ Q * N ^ (6 - 8 * σ)),
        Real.mul_rpow hQ0.le (by positivity : (0 : ℝ) ≤ N ^ (6 - 8 * σ))] at h1
      have e3 : (N ^ (6 - 8 * σ)) ^ (1 / 2 : ℝ) = N ^ (3 - 4 * σ) := by
        rw [← Real.rpow_mul hN.le]; ring_nf
      rw [e3] at h1
      calc r ≤ (5 * 216 ^ 3 * K) ^ (1 / 2 : ℝ) * (Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ)) := h1
        _ ≤ 5 * 216 ^ 3 * K * (Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ)) :=
            mul_le_mul_of_nonneg_right (hMe _ (by norm_num)) hb2
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hM0
    · -- `r ≤ MQN^{9/2−7σ}`
      have h1 := le_of_cube_le hr (by positivity) (by norm_num) c
      have e : (1 : ℝ) / (3 - 2) = 1 := by norm_num
      rw [e, Real.rpow_one] at h1
      have h2 := dom4 hQ hN hσ1 hσ2
      calc r ≤ 5 * 216 ^ 3 * K * (Q * N ^ (9 / 2 - 7 * σ)) := h1
        _ ≤ 5 * 216 ^ 3 * K * (Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) :=
            mul_le_mul_of_nonneg_left h2 hM0
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hM0
    · -- `r ≤ (MQ^{9/8}N^{9/2−7σ})^{16/19}`
      have h1 := le_of_cube_le hr (by positivity) (by norm_num) c
      have e : (1 : ℝ) / (3 - 29 / 16) = 16 / 19 := by norm_num
      rw [e, Real.mul_rpow hM0 (by positivity : (0 : ℝ) ≤ Q ^ (9 / 8 : ℝ) * N ^ (9 / 2 - 7 * σ)),
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ Q ^ (9 / 8 : ℝ))
          (by positivity : (0 : ℝ) ≤ N ^ (9 / 2 - 7 * σ))] at h1
      have e2 : (Q ^ (9 / 8 : ℝ)) ^ (16 / 19 : ℝ) = Q ^ (18 / 19 : ℝ) := by
        rw [← Real.rpow_mul hQ0.le]; norm_num
      have e3 : (N ^ (9 / 2 - 7 * σ)) ^ (16 / 19 : ℝ) = N ^ ((72 - 112 * σ) / 19) := by
        rw [← Real.rpow_mul hN.le]; ring_nf
      rw [e2, e3] at h1
      have h2 := dom5 hQ hN hσ1 hσ2
      calc r ≤ (5 * 216 ^ 3 * K) ^ (16 / 19 : ℝ) * (Q ^ (18 / 19 : ℝ) * N ^ ((72 - 112 * σ) / 19)) := h1
        _ ≤ 5 * 216 ^ 3 * K * (Q ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + Q ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) :=
            mul_le_mul (hMe _ (by norm_num)) h2 (by positivity) hM0
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hM0

/-! ### The hypothesis, and Proposition 3.1 from it -/

/-- **Chen–Gupta–Li's bound on the off-diagonal of the cubic trace** (a hypothesis): for every `ε > 0` there is
`C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`, `7/10 ≤ σ ≤ 4/5`, a real `N` with `(qT)^{2/3}/2 ≤ N ≤ qT`,
`S ⊆ [6N/5, 9N/5]`, `|b_n| ≤ 1` and distinct primitive characters `χ_i` mod `q` (`i ∈ R`) with
`|Σ_{n∈S} b_nχ_i(n)n^{it_i}| ≥ N^σ/6` at points `|t_i| ≤ T`,
`X ≤ C(qTN)^ε(N³ + (qT)²|R|^{3/2} + qT|R|N^{3−2σ} + qT|R|²N^{3/2−σ} + (qT)^{9/8}|R|^{29/16}N^{3/2−σ})`. -/
def CGLThird : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} [DecidableEq ι] (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    Set.InjOn χ R → (∀ i ∈ R, (χ i).IsPrimitive) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N → N ≤ (q : ℝ) * T →
    (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) → (∀ n, ‖b n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
    (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    X3 N R χ t ≤ C * ((q : ℝ) * T * N) ^ ε * (N ^ 3 + ((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) +
      (q : ℝ) * T * R.card * N ^ (3 - 2 * σ) + (q : ℝ) * T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) +
      ((q : ℝ) * T) ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ))

/-- **Proposition 3.1 from the bound on the cubic trace**: `CGLThird` implies `LinnikCGLLV.CGLProp31`. For `N ≤ qT`,
`prop46` and `alg112` with `K = max(C(qTN)^{ε₁}, 1)`, `ε₁ = min(ε, 1)`; for `N ≥ max(qT, 10)`, the mean value
theorem (`mvt_case`, `polylog_le`); for `qT < N < 10`, at most `q < 10` characters. -/
theorem prop31_of_third (h : CGLThird) : LinnikCGLLV.CGLProp31 := by
  intro ε hε
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := h ε₁ hε₁0
  obtain ⟨Cm, hCm⟩ : ∃ x : ℝ, x = (11 + 24 / ε₁) * (2 + 36 / ε₁ ^ 2) := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  obtain ⟨Ctot, hCtot⟩ : ∃ x : ℝ, x = 10 * 216 ^ 3 * max C 1 + 36 * Cm + 20 := ⟨_, rfl⟩
  have hC1 : 1 ≤ max C 1 := le_max_right _ _
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; linarith
  refine ⟨2 ^ ε * Ctot, mul_nonneg (by positivity) hCtot0, ?_⟩
  intro q _ ι R χ t T N σ S b hinj hprim hT hσ1 hσ2 hN hS hb ht hbig
  classical
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hN12 : 1 / 2 ≤ N := by
    have : (1 : ℝ) ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have hb1 : 0 ≤ N ^ (2 - 2 * σ) := by positivity
  have hb2 : 0 ≤ ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by positivity
  have hb3 : 0 ≤ ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by positivity
  have hP : 0 < (q : ℝ) * T * N := by positivity
  have hP2 : 1 ≤ 2 * ((q : ℝ) * T * N) := by nlinarith
  set E := 2 ^ ε * ((q : ℝ) * T * N) ^ ε with hE
  have hE1 : 1 ≤ E := by
    rw [hE, ← Real.mul_rpow (by norm_num) hP.le]; exact Real.one_le_rpow hP2 hε.le
  have hpow1 : ((q : ℝ) * T * N) ^ ε₁ ≤ E := by
    rcases le_total 1 ((q : ℝ) * T * N) with h1 | h1
    · calc ((q : ℝ) * T * N) ^ ε₁ ≤ ((q : ℝ) * T * N) ^ ε := Real.rpow_le_rpow_of_exponent_le h1 hε₁ε
        _ ≤ E := le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (by norm_num) hε.le)
    · calc ((q : ℝ) * T * N) ^ ε₁ ≤ 1 := Real.rpow_le_one hP.le h1 hε₁0.le
        _ ≤ E := hE1
  -- the final form
  have hfin : ∀ c : ℝ, 0 ≤ c → c ≤ Ctot → c * E * (N ^ (2 - 2 * σ) +
      ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) ≤
      2 ^ ε * Ctot * ((q : ℝ) * T * N) ^ ε * (N ^ (2 - 2 * σ) +
      ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
    intro c hc0 hc
    have hB0 : 0 ≤ N ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
        ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by positivity
    have hE0 : 0 ≤ E := by linarith
    calc c * E * _ ≤ Ctot * E * _ := by gcongr
      _ = _ := by rw [hE]; ring
  rcases le_or_gt N ((q : ℝ) * T) with hNq | hNq
  · -- `N ≤ qT`: the cubic trace
    have hX := hC q R χ t T N σ S b hinj hprim hT hσ1 hσ2 hN hNq hS hb ht hbig
    have h46 := prop46 R χ t hN12 hS hb hbig
    set K := max (C * ((q : ℝ) * T * N) ^ ε₁) 1 with hK
    have hK1 : 1 ≤ K := le_max_right _ _
    have hXK : X3 N R χ t ≤ K * (N ^ 3 + ((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) +
        (q : ℝ) * T * R.card * N ^ (3 - 2 * σ) + (q : ℝ) * T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) +
        ((q : ℝ) * T) ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ)) :=
      hX.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hr := alg112 (Nat.cast_nonneg R.card) hN0 hQ1 hσ1 hσ2 hK1 h46 hXK
    have hKE : K ≤ max C 1 * E := by
      rw [hK]
      apply max_le
      · exact mul_le_mul (le_max_left _ _) hpow1 (by positivity) (by positivity)
      · calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ max C 1 * E := mul_le_mul hC1 hE1 zero_le_one (by positivity)
    calc (R.card : ℝ) ≤ 5 * 216 ^ 3 * K * (N ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := hr
      _ ≤ 5 * 216 ^ 3 * max C 1 * E * (N ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
          rw [mul_assoc (5 * 216 ^ 3) (max C 1) E]
          gcongr
      _ ≤ _ := hfin _ (by positivity) (by rw [hCtot]; linarith)
  · rcases le_or_gt 10 N with hN10 | hN10
    · -- `N ≥ max(qT, 10)`: the mean value theorem
      have hm := mvt_case R χ t hinj hT hNq.le hN10 hS hb ht hbig
      have hpl := polylog_le (by linarith : (1 : ℝ) ≤ N) hε₁0 hε₁1
      rw [← hCm] at hpl
      have e : N ^ (2 - 2 * σ) = N ^ 2 / (N ^ σ) ^ 2 := by
        rw [LinnikCGLLV.npow_div_rpow_pow hN0 2 2 σ]; norm_num
      have h1 : (R.card : ℝ) ≤ 36 * Cm * N ^ ε₁ * N ^ (2 - 2 * σ) := by
        rw [e, show 36 * Cm * N ^ ε₁ * (N ^ 2 / (N ^ σ) ^ 2) = 36 * Cm * N ^ ε₁ * N ^ 2 / (N ^ σ) ^ 2 by ring,
          le_div_iff₀ (by positivity)]
        calc (R.card : ℝ) * (N ^ σ) ^ 2
            ≤ 36 * N ^ 2 * ((11 + 8 * Real.log N) * (2 + Real.log (2 * N) ^ 2)) := hm
          _ ≤ 36 * N ^ 2 * (Cm * N ^ ε₁) := by gcongr
          _ = 36 * Cm * N ^ ε₁ * N ^ 2 := by ring
      have h2 : N ^ ε₁ ≤ E :=
        le_trans (Real.rpow_le_rpow hN0.le (le_mul_of_one_le_left hN0.le hQ1) hε₁0.le) hpow1
      calc (R.card : ℝ) ≤ 36 * Cm * N ^ ε₁ * N ^ (2 - 2 * σ) := h1
        _ ≤ 36 * Cm * E * (N ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
            ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
            gcongr
            linarith
        _ ≤ _ := hfin _ (by positivity) (by rw [hCtot]; linarith)
    · -- `qT < N < 10`: at most `q < 10` characters
      have hRq : (R.card : ℝ) ≤ q := by
        have h1 := LinnikDensity.card_chars_le (R.image χ)
        rwa [Finset.card_image_of_injOn hinj] at h1
      have hN1 : 1 ≤ N := by linarith
      have hNB : 1 ≤ N ^ (2 - 2 * σ) := Real.one_le_rpow hN1 (by linarith)
      have hqqT : (q : ℝ) ≤ (q : ℝ) * T := le_mul_of_one_le_right (Nat.cast_nonneg q) hT
      have hq10 : (q : ℝ) ≤ 10 := by linarith
      have hEB : 1 ≤ E * (N ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) :=
        one_le_mul_of_one_le_of_one_le hE1 (by linarith)
      calc (R.card : ℝ) ≤ 20 * E * (N ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
            ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by rw [mul_assoc]; linarith
        _ ≤ _ := hfin _ (by norm_num) (by rw [hCtot]; linarith)

/-- **Linnik's theorem with exponent `9/4` from the bound on the cubic trace** (`h`). -/
theorem linnik_225c_third (h : CGLThird) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLLinnik.linnik_225c_lv (prop31_of_third h)

/-- **Linnik's theorem with exponent `226/100` from the bound on the cubic trace** (`h`). -/
theorem linnik_226c_third (h : CGLThird) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLLinnik.linnik_226c_lv (prop31_of_third h)

end LinnikCGLMat

#print axioms LinnikCGLMat.refined_moment_points
#print axioms LinnikCGLMat.prop46
#print axioms LinnikCGLMat.mvt_case
#print axioms LinnikCGLMat.polylog_le
#print axioms LinnikCGLMat.alg112
#print axioms LinnikCGLMat.prop31_of_third
#print axioms LinnikCGLMat.linnik_225c_third
#print axioms LinnikCGLMat.linnik_226c_third
