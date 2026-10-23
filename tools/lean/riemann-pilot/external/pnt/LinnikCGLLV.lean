/-
# Rounds 636–637: Chen–Gupta–Li's Proposition 3.1 as a hypothesis, and the large-values counts it gives (the CGL
plan's stages M1 and M2)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`CGLProp31`, a hypothesis). Chen, Gupta and Li's Proposition 3.1 (arXiv:2507.08296v2) at one point per
character, for a sum over `[6N/5, 9N/5]`: for every `ε > 0` there is `C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`,
`7/10 ≤ σ ≤ 4/5`, a real `N ≥ (qT)^{2/3}/2`, `S ⊆ [6N/5, 9N/5]` and `|b_n| ≤ 1`, at most
`C(qTN)^ε(N^{2−2σ} + (qT)^{1/2}N^{3−4σ} + (qT)^{4/3}N^{2−4σ})` distinct primitive characters `χ` mod `q` have
`|Σ_{n∈S} b_nχ(n)n^{it_χ}| ≥ N^σ/6` at a point `|t_χ| ≤ T`. Their proposition bounds `S_N = Σ_n w(n/N)b_nχ(n)n^{it}`,
with the smooth `w` of their §3 (supported on `[1, 2]`, `1` on `[6/5, 9/5]`), for a set of pairs `(t, χ)` whose
members with the same `χ` are `(qT)^ε` apart, by `⪅_ε`: a factor `C(ϵ)(qT)^ϵ` for every `ϵ > 0` and all sufficiently
large `qT` (their §1.1). The coefficients `b_n1_S(n)` make their `S_N` this sum; distinct characters are such a set;
`(qT)^ϵ ≤ 2^ϵ(qTN)^ϵ` since `N ≥ 1/2`; and for `qT` below any bound the count is at most `q`, while `(qTN)^ε ≥ 2^{−ε}`
and `N^{2−2σ} ≥ 1/2`. So their proposition implies the hypothesis.

Plain statement (`lv_range`). Under the hypothesis, for `0 < ε ≤ 1` there is `C ≥ 0` such that, for `q ≥ 1`,
`T ≥ 1`, `N ≥ (qT)^{2/3}`, `N^{7/10} ≤ V ≤ N^{4/5}` and `|a_n| ≤ 1`, at most `C(qTN)^ε B(q, T, N, V)` distinct
primitive characters `χ` mod `q` have `|Σ_{N<n≤2N} a_nχ(n)n^{it_χ}| ≥ V` at a point `|t_χ| ≤ T`, where
`B(q, T, N, V) = N²V⁻² + (qT)^{1/2}N³V⁻⁴ + (qT)^{4/3}N²V⁻⁴` (`p31B`). This is the reduction of their Theorem 1.1 to
Proposition 3.1 on the range of `V` where the proposition applies (their §3). The rest of that proof, the mean value
theorem and Huxley's estimate outside the range and the subdivision in `T`, is not needed by the step
(`LinnikCGLStep`), which uses the count only at `V = N^σ/Z` with `5/7 ≤ σ ≤ 16/21`.

Plain statement (`cgl_all`). Under the hypothesis, the count of `lv_range` holds for any characters mod `q`, primitive
or not, with a factor `C′q^ε` for the divisors of `q`.

Plain statement (`cgl_shift`). Under the hypothesis, characters with `|Σ_{N<n≤2N} a_nχ(n)n^{−(δ_χ+iγ_χ)}| ≥ V`,
`0 ≤ δ_χ ≤ 1/16`, `|γ_χ| ≤ T`, number at most `K·C′q^ε(qTN)^ε B(q, T, N, V/2)` for every `K ≥ 1` with
`2N·16^{−K} ≤ V/4`, when `N^{7/10} ≤ V/2 ≤ N^{4/5}`.

* `lv_range`: with `V = N^σ`, `D_N` is the sum of its parts over `(N, 6N/5)`, `[6N/5, 9N/5]` and `(9N/5, 2N]`, one
  of which is at least `V/3` at each point; the hypothesis at `11N/15`, `N` and `19N/15` counts each part's points,
  and `(cN)^x ≤ 2N^x` for `11/15 ≤ c ≤ 19/15` and `|x| ≤ 2` (`rpow_le_two`, `piece_bound`).
* `cgl_all`: a character `χ` with conductor `d` factors through a character `χ₀` mod `d`, which is primitive and
  determines `χ`; `χ(n) = χ₀(n)` for `n` prime to `q` and `χ(n) = 0` otherwise, so the sum is `χ₀`'s with the
  coefficients `a_n 1_{(n,q)=1}`; `lv_range` at each `d ∣ q`, and `d(q) ≤ C(ε)q^ε` (`card_divisors_le`).
* `taylor_pick`: `n^{−δ} = N^{−δ}e^{−δ log(n/N)}` with `0 ≤ log(n/N) ≤ 1`, and `e^{−δx}` is its Taylor polynomial of
  degree `K − 1` within `2·16^{−K}` (`Real.exp_bound`); if every `Σ a_n log(n/N)^k χ(n)n^{−iγ}`, `k < K`, were below
  `V/2`, the sum would be at most `(V/2)e^{1/16} + V/4 < V`.
* `cgl_shift`: `taylor_pick` for each character, and `cgl_all` for each `k < K`.

Round 636 had their Theorem 1.1's second bound as the hypothesis (`CGLLargeValues`, with the bound `cglB`); round 637
replaces it with Proposition 3.1 (README round 637).

The file imports `LinnikPower.lean`.
-/

import LinnikPower

open Complex Real Finset

noncomputable section

namespace LinnikCGLLV

open DirichletCharacter LinnikPower

variable {q : ℕ}

/-! ### The hypothesis -/

/-- The bound of Chen–Gupta–Li's Proposition 3.1 at `V = N^σ`: `N²V⁻² + (qT)^{1/2}N³V⁻⁴ + (qT)^{4/3}N²V⁻⁴`. -/
def p31B (q : ℕ) (T : ℝ) (N : ℕ) (V : ℝ) : ℝ :=
  (N : ℝ) ^ 2 / V ^ 2 + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (N : ℝ) ^ 3 / V ^ 4 +
    ((q : ℝ) * T) ^ (4 / 3 : ℝ) * (N : ℝ) ^ 2 / V ^ 4

/-- **Chen–Gupta–Li's Proposition 3.1, one point per character** (as a hypothesis): for every `ε > 0` there is
`C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`, `7/10 ≤ σ ≤ 4/5`, a real `N ≥ (qT)^{2/3}/2`, `S ⊆ [6N/5, 9N/5]`,
`|b_n| ≤ 1` and distinct primitive characters `χ_i` mod `q` (`i ∈ R`) with `|Σ_{n∈S} b_nχ_i(n)n^{it_i}| ≥ N^σ/6` at
points `|t_i| ≤ T`, `|R| ≤ C(qTN)^ε(N^{2−2σ} + (qT)^{1/2}N^{3−4σ} + (qT)^{4/3}N^{2−4σ})`. -/
def CGLProp31 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
    Set.InjOn χ R → (∀ i ∈ R, (χ i).IsPrimitive) → 1 ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N → (∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) →
    (∀ n, ‖b n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
    (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
    (R.card : ℝ) ≤ C * ((q : ℝ) * T * N) ^ ε *
      (N ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
        ((q : ℝ) * T) ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ))

lemma p31B_nonneg (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (V : ℝ) : 0 ≤ p31B q T N V := by
  unfold p31B; positivity

/-- `p31B` is monotone in the modulus. -/
lemma p31B_mono {d q : ℕ} (hdq : (d : ℝ) ≤ q) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (V : ℝ) :
    p31B d T N V ≤ p31B q T N V := by
  unfold p31B
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdT : (d : ℝ) * T ≤ q * T := mul_le_mul_of_nonneg_right hdq hT
  have h1 : ((d : ℝ) * T) ^ (1 / 2 : ℝ) ≤ ((q : ℝ) * T) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hdT (by norm_num)
  have h2 : ((d : ℝ) * T) ^ (4 / 3 : ℝ) ≤ ((q : ℝ) * T) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hdT (by norm_num)
  gcongr

/-! ### Proposition 3.1's range of `V` -/

/-- `N^k/(N^σ)^p = N^{k−pσ}` for `N > 0`. -/
lemma rpow_div_rpow_pow {N : ℝ} (hN : 0 < N) (k σ : ℝ) (p : ℕ) : N ^ k / (N ^ σ) ^ p = N ^ (k - p * σ) := by
  rw [← Real.rpow_natCast (N ^ σ), ← Real.rpow_mul hN.le, ← Real.rpow_sub hN, mul_comm σ]

/-- `N^k/(N^σ)^p = N^{k−pσ}` for `N > 0` and a natural `k`. -/
lemma npow_div_rpow_pow {N : ℝ} (hN : 0 < N) (k p : ℕ) (σ : ℝ) : N ^ k / (N ^ σ) ^ p = N ^ ((k : ℝ) - p * σ) := by
  rw [← rpow_div_rpow_pow hN, Real.rpow_natCast]

/-- `c^x ≤ 2` for `11/15 ≤ c ≤ 19/15` and `−2 ≤ x ≤ 2`. -/
lemma rpow_le_two {c x : ℝ} (hc1 : 11 / 15 ≤ c) (hc2 : c ≤ 19 / 15) (hx1 : -2 ≤ x) (hx2 : x ≤ 2) : c ^ x ≤ 2 := by
  have hc0 : 0 < c := by linarith
  rcases le_total 1 c with h1 | h1
  · calc c ^ x ≤ c ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hx2
      _ = c ^ 2 := Real.rpow_two c
      _ ≤ (19 / 15) ^ 2 := pow_le_pow_left₀ hc0.le hc2 2
      _ ≤ 2 := by norm_num
  · calc c ^ x ≤ c ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hc0 h1 hx1
      _ = (c ^ 2)⁻¹ := by rw [Real.rpow_neg hc0.le, Real.rpow_two]
      _ ≤ ((11 / 15 : ℝ) ^ 2)⁻¹ := by gcongr
      _ ≤ 2 := by norm_num

/-- `(cN)^x ≤ 2N^x` for `N ≥ 0`, `11/15 ≤ c ≤ 19/15` and `−2 ≤ x ≤ 2`. -/
lemma rpow_mul_le_two {c N x : ℝ} (hN : 0 ≤ N) (hc1 : 11 / 15 ≤ c) (hc2 : c ≤ 19 / 15) (hx1 : -2 ≤ x)
    (hx2 : x ≤ 2) : (c * N) ^ x ≤ 2 * N ^ x := by
  rw [Real.mul_rpow (by linarith) hN]
  exact mul_le_mul_of_nonneg_right (rpow_le_two hc1 hc2 hx1 hx2) (Real.rpow_nonneg hN x)

/-- **Proposition 3.1's bound at `cN` by its bound at `N`**: for `C, x, N ≥ 0`, `0 ≤ ε ≤ 1`, `11/15 ≤ c ≤ 19/15`
and `7/10 ≤ σ ≤ 4/5`, `C(xcN)^ε B_σ(cN) ≤ 4C(xN)^ε B_σ(N)`, where
`B_σ(N) = N^{2−2σ} + x^{1/2}N^{3−4σ} + x^{4/3}N^{2−4σ}`. -/
lemma piece_bound {C ε c N x σ : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : 0 ≤ x) (hN : 0 ≤ N)
    (hc1 : 11 / 15 ≤ c) (hc2 : c ≤ 19 / 15) (hσ1 : 7 / 10 ≤ σ) (hσ2 : σ ≤ 4 / 5) :
    C * (x * (c * N)) ^ ε * ((c * N) ^ (2 - 2 * σ) + x ^ (1 / 2 : ℝ) * (c * N) ^ (3 - 4 * σ) +
      x ^ (4 / 3 : ℝ) * (c * N) ^ (2 - 4 * σ)) ≤
    4 * C * (x * N) ^ ε * (N ^ (2 - 2 * σ) + x ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
      x ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
  have hA : (x * (c * N)) ^ ε ≤ 2 * (x * N) ^ ε := by
    have h1 : x * (c * N) ≤ 2 * (x * N) := by nlinarith [mul_nonneg hx hN]
    calc (x * (c * N)) ^ ε ≤ (2 * (x * N)) ^ ε := Real.rpow_le_rpow (by positivity) h1 hε
      _ = 2 ^ ε * (x * N) ^ ε := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (x * N) ^ ε := by
          gcongr
          calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
            _ = 2 := Real.rpow_one 2
  have h1 := rpow_mul_le_two hN hc1 hc2 (x := 2 - 2 * σ) (by linarith) (by linarith)
  have h2 := rpow_mul_le_two hN hc1 hc2 (x := 3 - 4 * σ) (by linarith) (by linarith)
  have h3 := rpow_mul_le_two hN hc1 hc2 (x := 2 - 4 * σ) (by linarith) (by linarith)
  have e1 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx _
  have e2 : 0 ≤ x ^ (4 / 3 : ℝ) := Real.rpow_nonneg hx _
  have hB : (c * N) ^ (2 - 2 * σ) + x ^ (1 / 2 : ℝ) * (c * N) ^ (3 - 4 * σ) + x ^ (4 / 3 : ℝ) * (c * N) ^ (2 - 4 * σ) ≤
      2 * (N ^ (2 - 2 * σ) + x ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + x ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 e1, mul_le_mul_of_nonneg_left h3 e2]
  have hc0 : 0 ≤ c * N := by nlinarith
  calc C * (x * (c * N)) ^ ε * ((c * N) ^ (2 - 2 * σ) + x ^ (1 / 2 : ℝ) * (c * N) ^ (3 - 4 * σ) +
        x ^ (4 / 3 : ℝ) * (c * N) ^ (2 - 4 * σ))
      ≤ C * (2 * (x * N) ^ ε) * (2 * (N ^ (2 - 2 * σ) + x ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          x ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ))) := by
        gcongr
    _ = 4 * C * (x * N) ^ ε * (N ^ (2 - 2 * σ) + x ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) +
          x ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ)) := by ring

open scoped Classical in
/-- **The large values of `D_N` on Proposition 3.1's range** (their §3, at one point per character): under
`CGLProp31`, for `0 < ε ≤ 1` there is `C ≥ 0` such that, for `q ≥ 1`, `T ≥ 1`, `N ≥ (qT)^{2/3}`,
`N^{7/10} ≤ V ≤ N^{4/5}`, `|a_n| ≤ 1` and distinct primitive characters `χ_i` mod `q` (`i ∈ R`) with
`|Σ_{N<n≤2N} a_nχ_i(n)n^{it_i}| ≥ V` at points `|t_i| ≤ T`, `|R| ≤ C(qTN)^ε p31B(q, T, N, V)`. -/
theorem lv_range (h : CGLProp31) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T : ℝ) (N : ℕ) (V : ℝ) (a : ℕ → ℂ), Set.InjOn χ R → (∀ i ∈ R, (χ i).IsPrimitive) → 1 ≤ T →
      ((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ N → (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
      (R.card : ℝ) ≤ C * ((q : ℝ) * T * N) ^ ε * p31B q T N V := by
  obtain ⟨C, hC0, hC⟩ := h ε hε
  refine ⟨12 * C, by positivity, ?_⟩
  intro q _ ι R χ t T N V a hinj hprim hT hN hV1 hV2 ha ht hbig
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hN1r : (1 : ℝ) ≤ N := (Real.one_le_rpow hqT1 (by norm_num)).trans hN
  have hN1 : 1 ≤ N := by exact_mod_cast hN1r
  have hNr : (0 : ℝ) < N := by linarith
  have hV0 : 0 < V := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr _) hV1
  -- `V = N^σ` with `7/10 ≤ σ ≤ 4/5`
  obtain ⟨σ, hσ1, hσ2, hNσ⟩ : ∃ σ : ℝ, 7 / 10 ≤ σ ∧ σ ≤ 4 / 5 ∧ (N : ℝ) ^ σ = V := by
    rcases Nat.lt_or_ge 1 N with h2 | h2
    · have hb : (1 : ℝ) < N := by exact_mod_cast h2
      exact ⟨Real.logb N V, (Real.le_logb_iff_rpow_le hb hV0).2 hV1, (Real.logb_le_iff_le_rpow hb hV0).2 hV2,
        Real.rpow_logb hNr hb.ne' hV0⟩
    · have hN' : N = 1 := le_antisymm h2 hN1
      subst hN'
      refine ⟨7 / 10, le_refl _, by norm_num, ?_⟩
      simp only [Nat.cast_one, Real.one_rpow] at hV1 hV2 ⊢
      linarith
  have hσ0 : 0 ≤ σ := by linarith
  -- the three parts
  obtain ⟨A1, hA1⟩ : ∃ A : Finset ℕ, A = (Ioc N (2 * N)).filter fun n : ℕ => (n : ℝ) < 6 / 5 * N := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : Finset ℕ,
      A = (Ioc N (2 * N)).filter fun n : ℕ => 6 / 5 * (N : ℝ) ≤ n ∧ (n : ℝ) ≤ 9 / 5 * N := ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A : Finset ℕ, A = (Ioc N (2 * N)).filter fun n : ℕ => 9 / 5 * (N : ℝ) < n := ⟨_, rfl⟩
  have hdecomp : ∀ i, ∑ n ∈ Ioc N (2 * N), a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) =
      ∑ n ∈ A1, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) + ∑ n ∈ A2, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) +
        ∑ n ∈ A3, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) := by
    intro i
    rw [hA1, hA2, hA3, sum_filter, sum_filter, sum_filter, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases h1 : (n : ℝ) < 6 / 5 * N
    · have h2 : ¬ (6 / 5 * (N : ℝ) ≤ n ∧ (n : ℝ) ≤ 9 / 5 * N) := fun h => by linarith [h.1]
      have h3 : ¬ (9 / 5 * (N : ℝ) < n) := fun h => by linarith
      simp only [h1, h2, h3, ↓reduceIte, add_zero]
    · by_cases h3 : 9 / 5 * (N : ℝ) < n
      · have h2 : ¬ (6 / 5 * (N : ℝ) ≤ n ∧ (n : ℝ) ≤ 9 / 5 * N) := fun h => by linarith [h.2]
        simp only [h1, h2, h3, ↓reduceIte, zero_add]
      · have h2 : 6 / 5 * (N : ℝ) ≤ n ∧ (n : ℝ) ≤ 9 / 5 * N := ⟨by linarith, by linarith⟩
        simp only [h1, h2, h3, and_self, ↓reduceIte, add_zero, zero_add]
  -- the points of each part
  obtain ⟨R1, hR1⟩ : ∃ R' : Finset ι,
      R' = R.filter fun i => V / 3 ≤ ‖∑ n ∈ A1, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R' : Finset ι,
      R' = R.filter fun i => V / 3 ≤ ‖∑ n ∈ A2, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ := ⟨_, rfl⟩
  obtain ⟨R3, hR3⟩ : ∃ R' : Finset ι,
      R' = R.filter fun i => V / 3 ≤ ‖∑ n ∈ A3, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ := ⟨_, rfl⟩
  have hcover : R ⊆ R1 ∪ R2 ∪ R3 := by
    intro i hi
    by_contra hno
    simp only [mem_union, hR1, hR2, hR3, mem_filter, hi, true_and, not_or, not_le] at hno
    obtain ⟨⟨h1, h2⟩, h3⟩ := hno
    have h4 := hbig i hi
    rw [hdecomp i] at h4
    have h5 : ‖∑ n ∈ A1, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) + ∑ n ∈ A2, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) +
        ∑ n ∈ A3, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ ≤ ‖∑ n ∈ A1, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ +
        ‖∑ n ∈ A2, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ + ‖∑ n ∈ A3, a n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ :=
      norm_add₃_le
    linarith
  have hcard : (R.card : ℝ) ≤ R1.card + R2.card + R3.card := by
    have h1 := card_le_card hcover
    have h2 := card_union_le (R1 ∪ R2) R3
    have h3 := card_union_le R1 R2
    have : R.card ≤ R1.card + R2.card + R3.card := by omega
    exact_mod_cast this
  have hsub : ∀ R' : Finset ι, R' ⊆ R → Set.InjOn χ R' ∧ (∀ i ∈ R', (χ i).IsPrimitive) ∧ ∀ i ∈ R', |t i| ≤ T :=
    fun R' h' => ⟨hinj.mono (coe_subset.2 h'), fun i hi => hprim i (h' hi), fun i hi => ht i (h' hi)⟩
  have hN0 : (0 : ℝ) ≤ N := hNr.le
  have hx0 : (0 : ℝ) ≤ (q : ℝ) * T := by linarith
  -- each part by the hypothesis at `cN`
  have hthr : ∀ (c : ℝ), 0 ≤ c → c ≤ 19 / 15 → (c * N) ^ σ / 6 ≤ V / 3 := by
    intro c hc0 hc
    have h1 : (c * N) ^ σ ≤ 2 * (N : ℝ) ^ σ := by
      rcases le_total (11 / 15) c with h | h
      · exact rpow_mul_le_two hN0 h hc (by linarith) (by linarith)
      · calc (c * N) ^ σ ≤ (11 / 15 * N) ^ σ := Real.rpow_le_rpow (by positivity) (by nlinarith) hσ0
          _ ≤ 2 * (N : ℝ) ^ σ := rpow_mul_le_two hN0 le_rfl (by norm_num) (by linarith) (by linarith)
    rw [← hNσ]; linarith
  have hk1 : (R1.card : ℝ) ≤ 4 * C * ((q : ℝ) * T * N) ^ ε * ((N : ℝ) ^ (2 - 2 * σ) +
      ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) + ((q : ℝ) * T) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ)) := by
    obtain ⟨hi1, hi2, hi3⟩ := hsub R1 (by rw [hR1]; exact filter_subset _ _)
    have hc := hC q R1 χ t T (11 / 15 * (N : ℝ)) σ A1 a hi1 hi2 hT hσ1 hσ2 (by linarith)
      (fun n hn => by
        rw [hA1, mem_filter, mem_Ioc] at hn
        have h1 : (N : ℝ) < n := by exact_mod_cast hn.1.1
        exact ⟨by linarith, by linarith [hn.2]⟩) ha hi3
      (fun i hi => by
        rw [hR1, mem_filter] at hi
        exact (hthr _ (by norm_num) (by norm_num)).trans hi.2)
    exact hc.trans (piece_bound (c := 11 / 15) (N := (N : ℝ)) (x := (q : ℝ) * T) hC0 hε.le hε1 hx0 hN0
      (by norm_num) (by norm_num) hσ1 hσ2)
  have hk2 : (R2.card : ℝ) ≤ 4 * C * ((q : ℝ) * T * N) ^ ε * ((N : ℝ) ^ (2 - 2 * σ) +
      ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) + ((q : ℝ) * T) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ)) := by
    obtain ⟨hi1, hi2, hi3⟩ := hsub R2 (by rw [hR2]; exact filter_subset _ _)
    have hc := hC q R2 χ t T (1 * (N : ℝ)) σ A2 a hi1 hi2 hT hσ1 hσ2 (by linarith)
      (fun n hn => by
        rw [hA2, mem_filter] at hn
        exact ⟨by linarith [hn.2.1], by linarith [hn.2.2]⟩) ha hi3
      (fun i hi => by
        rw [hR2, mem_filter] at hi
        exact (hthr _ (by norm_num) (by norm_num)).trans hi.2)
    exact hc.trans (piece_bound (c := 1) (N := (N : ℝ)) (x := (q : ℝ) * T) hC0 hε.le hε1 hx0 hN0
      (by norm_num) (by norm_num) hσ1 hσ2)
  have hk3 : (R3.card : ℝ) ≤ 4 * C * ((q : ℝ) * T * N) ^ ε * ((N : ℝ) ^ (2 - 2 * σ) +
      ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) + ((q : ℝ) * T) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ)) := by
    obtain ⟨hi1, hi2, hi3⟩ := hsub R3 (by rw [hR3]; exact filter_subset _ _)
    have hc := hC q R3 χ t T (19 / 15 * (N : ℝ)) σ A3 a hi1 hi2 hT hσ1 hσ2 (by linarith)
      (fun n hn => by
        rw [hA3, mem_filter, mem_Ioc] at hn
        have h2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.1.2
        exact ⟨by linarith [hn.2], by linarith⟩) ha hi3
      (fun i hi => by
        rw [hR3, mem_filter] at hi
        exact (hthr _ (by norm_num) (by norm_num)).trans hi.2)
    exact hc.trans (piece_bound (c := 19 / 15) (N := (N : ℝ)) (x := (q : ℝ) * T) hC0 hε.le hε1 hx0 hN0
      (by norm_num) (by norm_num) hσ1 hσ2)
  -- the bound in terms of `V = N^σ`
  have hB : (N : ℝ) ^ (2 - 2 * σ) + ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
      ((q : ℝ) * T) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ) = p31B q T N V := by
    have e1 : (N : ℝ) ^ (2 - 2 * σ) = (N : ℝ) ^ 2 / V ^ 2 := by
      rw [← hNσ, npow_div_rpow_pow hNr 2 2 σ]; norm_num
    have e2 : (N : ℝ) ^ (3 - 4 * σ) = (N : ℝ) ^ 3 / V ^ 4 := by
      rw [← hNσ, npow_div_rpow_pow hNr 3 4 σ]; norm_num
    have e3 : (N : ℝ) ^ (2 - 4 * σ) = (N : ℝ) ^ 2 / V ^ 4 := by
      rw [← hNσ, npow_div_rpow_pow hNr 2 4 σ]; norm_num
    rw [e1, e2, e3]; unfold p31B; ring
  rw [← hB]
  linarith

/-! ### All characters mod `q` -/

/-- A character `χ = changeLevel χ₀` takes `χ₀`'s value at `n` prime to `q` and `0` elsewhere. -/
lemma changeLevel_natCast {d : ℕ} (hd : d ∣ q) (χ₀ : DirichletCharacter ℂ d) (n : ℕ) :
    changeLevel hd χ₀ n = if n.Coprime q then χ₀ n else 0 := by
  split_ifs with hc
  · have h := changeLevel_eq_cast_of_dvd' χ₀ hd (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hc)
    simpa using h
  · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

open scoped Classical in
/-- **Proposition 3.1's count over all characters mod `q`**: under `CGLProp31`, for `0 < ε ≤ 1` there is `C ≥ 0`
such that for `q ≥ 1`, `T ≥ 1`, `N ≥ (qT)^{2/3}`, `N^{7/10} ≤ V ≤ N^{4/5}` and `|a_n| ≤ 1`, characters `χ ∈ R` mod `q`
with `|Σ_{N<n≤2N} a_nχ(n)n^{it_χ}| ≥ V`, `|t_χ| ≤ T`, number at most `Cq^ε(qTN)^ε p31B(q, T, N, V)`. -/
theorem cgl_all (h : CGLProp31) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)) (t : DirichletCharacter ℂ q → ℝ)
      (T : ℝ) (N : ℕ) (V : ℝ) (a : ℕ → ℂ), 1 ≤ T → ((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ N →
      (N : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (N : ℝ) ^ (4 / 5 : ℝ) → (∀ n, ‖a n‖ ≤ 1) → (∀ χ ∈ R, |t χ| ≤ T) →
      (∀ χ ∈ R, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ ((t χ : ℂ) * I)‖) →
      (R.card : ℝ) ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N V := by
  obtain ⟨C, hC0, hC⟩ := lv_range h hε hε1
  have hCd := one_le_Cdiv hε hε1
  refine ⟨Cdiv ε * C, by positivity, ?_⟩
  intro q _ R t T N V a hT hN hV1 hV2 ha ht hbig
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set B : ℝ := C * ((q : ℝ) * T * N) ^ ε * p31B q T N V with hB
  have hB0 : 0 ≤ B := by have := p31B_nonneg q hT0 N V; positivity
  -- the characters of each conductor
  have hsub : R ⊆ q.divisors.biUnion fun d => R.filter fun χ => χ.conductor = d := by
    intro χ hχ
    exact mem_biUnion.2 ⟨χ.conductor, Nat.mem_divisors.2 ⟨χ.conductor_dvd_level, NeZero.ne q⟩,
      mem_filter.2 ⟨hχ, rfl⟩⟩
  have hd : ∀ d ∈ q.divisors, ((R.filter fun χ => χ.conductor = d).card : ℝ) ≤ B := by
    intro d hdq
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hdq).ne'
    have : NeZero d := ⟨hd0⟩
    have hdvd : d ∣ q := Nat.dvd_of_mem_divisors hdq
    have hdq' : (d : ℝ) ≤ q := by exact_mod_cast Nat.divisor_le hdq
    set Rd := R.filter fun χ => χ.conductor = d with hRd
    have hft : ∀ χ ∈ Rd, χ.FactorsThrough d := by
      intro χ hχ
      rw [← (mem_filter.1 hχ).2]
      exact χ.factorsThrough_conductor
    set g : DirichletCharacter ℂ q → DirichletCharacter ℂ d :=
      fun χ => if hχ : χ.FactorsThrough d then hχ.χ₀ else 1 with hgdef
    have hg : ∀ χ ∈ Rd, χ = changeLevel hdvd (g χ) := by
      intro χ hχ
      have h1 := (hft χ hχ).eq_changeLevel
      simp only [hgdef, hft χ hχ, ↓reduceDIte]
      exact h1
    have hinj : Set.InjOn g Rd := by
      intro χ₁ h₁ χ₂ h₂ he
      rw [hg χ₁ h₁, hg χ₂ h₂, he]
    have hprim : ∀ χ ∈ Rd, (g χ).IsPrimitive := by
      intro χ hχ
      have h1 : χ.conductor ≤ (g χ).conductor := by
        have := conductor_le_conductor_mem_conductorSet (χ := χ) (hft χ hχ)
        simpa only [hgdef, hft χ hχ, ↓reduceDIte, FactorsThrough.χ₀] using this
      have h2 : (g χ).conductor ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (conductor_dvd_level _)
      rw [isPrimitive_def]
      have h3 := (mem_filter.1 hχ).2
      omega
    set a' : ℕ → ℂ := fun n => if n.Coprime q then a n else 0 with ha'def
    have ha' : ∀ n, ‖a' n‖ ≤ 1 := by
      intro n; simp only [ha'def]; split_ifs
      · exact ha n
      · simp
    have hval : ∀ χ ∈ Rd, ∀ n : ℕ, a' n * g χ n = a n * χ n := by
      intro χ hχ n
      have e : χ (n : ZMod q) = changeLevel hdvd (g χ) n := congrArg (fun ψ => ψ (n : ZMod q)) (hg χ hχ)
      rw [e, changeLevel_natCast hdvd]
      simp only [ha'def]
      split_ifs <;> simp
    have hNd : ((d : ℝ) * T) ^ (2 / 3 : ℝ) ≤ N :=
      (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hdq' hT0) (by norm_num)).trans hN
    have hbig' : ∀ χ ∈ Rd, V ≤ ‖∑ n ∈ Ioc N (2 * N), a' n * g χ n * (n : ℂ) ^ ((t χ : ℂ) * I)‖ := by
      intro χ hχ
      have e : ∑ n ∈ Ioc N (2 * N), a' n * g χ n * (n : ℂ) ^ ((t χ : ℂ) * I) =
          ∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ ((t χ : ℂ) * I) :=
        sum_congr rfl fun n _ => by rw [hval χ hχ n]
      rw [e]; exact hbig χ (mem_filter.1 hχ).1
    have hcount := hC d Rd g t T N V a' hinj hprim hT hNd hV1 hV2 ha' (fun χ hχ => ht χ (mem_filter.1 hχ).1) hbig'
    refine hcount.trans ?_
    rw [hB]
    have hpow : ((d : ℝ) * T * N) ^ ε ≤ ((q : ℝ) * T * N) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by gcongr) hε.le
    have hm := p31B_mono hdq' hT0 N V
    have h0 : 0 ≤ p31B d T N V := p31B_nonneg d hT0 N V
    gcongr
  have hdiv : (q.divisors.card : ℝ) ≤ Cdiv ε * (q : ℝ) ^ ε := card_divisors_le hε hε1 q
  calc (R.card : ℝ) ≤ ((q.divisors.biUnion fun d => R.filter fun χ => χ.conductor = d).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ d ∈ q.divisors, ((R.filter fun χ => χ.conductor = d).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _d ∈ q.divisors, B := sum_le_sum hd
    _ = (q.divisors.card : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Cdiv ε * (q : ℝ) ^ ε * B := mul_le_mul_of_nonneg_right hdiv hB0
    _ = Cdiv ε * C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N V := by rw [hB]; ring

/-! ### Points off the line -/

/-- `n^{−δ} = N^{−δ}e^{−δ log(n/N)}` for `n, N > 0`. -/
lemma rpow_neg_split {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (δ : ℝ) :
    (n : ℝ) ^ (-δ) = (N : ℝ) ^ (-δ) * Real.exp (-δ * Real.log ((n : ℝ) / N)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hn', Real.rpow_def_of_pos hN', ← Real.exp_add, Real.log_div hn'.ne' hN'.ne']
  congr 1; ring

/-- `n^{−(δ+iγ)} = n^{−δ}n^{i(−γ)}` for `n ≥ 1`. -/
lemma cpow_shift {n : ℕ} (hn : n ≠ 0) (δ γ : ℝ) :
    (n : ℂ) ^ (-((δ : ℂ) + γ * I)) = (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * (n : ℂ) ^ (((-γ : ℝ) : ℂ) * I) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.2 hn)]
  congr 1; ring

/-- **One character off the line.** For `N ≥ 1`, `|a_n| ≤ 1`, `0 ≤ δ ≤ 1/16`, `V > 0` and `K ≥ 1` with
`2N·16^{−K} ≤ V/4`, if `|Σ_{N<n≤2N} a_nχ(n)n^{−(δ+iγ)}| ≥ V` then
`|Σ_{N<n≤2N} a_n log(n/N)^k χ(n)n^{−iγ}| ≥ V/2` for some `k < K`. -/
theorem taylor_pick {N : ℕ} (hN : 1 ≤ N) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) {δ γ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 16) {V : ℝ} (hV : 0 < V) {K : ℕ} (hK : 1 ≤ K)
    (htail : 2 * (N : ℝ) * (1 / 16) ^ K ≤ V / 4) (χ : DirichletCharacter ℂ q)
    (hbig : V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ : ℂ) + γ * I))‖) :
    ∃ k < K, V / 2 ≤ ‖∑ n ∈ Ioc N (2 * N), (a n * ((Real.log ((n : ℝ) / N) ^ k : ℝ) : ℂ)) * χ n *
      (n : ℂ) ^ (((-γ : ℝ) : ℂ) * I)‖ := by
  classical
  by_contra hcon
  push Not at hcon
  set S := Ioc N (2 * N) with hS
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set x : ℕ → ℝ := fun n => Real.log ((n : ℝ) / N) with hxdef
  have hx : ∀ n ∈ S, 0 ≤ x n ∧ x n ≤ 1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hn
    have hn1 : (N : ℝ) < n := by exact_mod_cast h1
    have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast h2
    have hnpos : (0 : ℝ) < n := by linarith
    constructor
    · exact Real.log_nonneg (by rw [le_div_iff₀ hNpos]; linarith)
    · calc x n ≤ Real.log 2 := Real.log_le_log (div_pos hnpos hNpos) (by rw [div_le_iff₀ hNpos]; linarith)
        _ ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn => by have := (mem_Ioc.1 hn).1; omega
  set u : ℕ → ℂ := fun n => a n * χ n * (n : ℂ) ^ (((-γ : ℝ) : ℂ) * I) with hudef
  have hu : ∀ n ∈ S, ‖u n‖ ≤ 1 := by
    intro n hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero (hS0 n hn)
    have h1 : ‖(n : ℂ) ^ (((-γ : ℝ) : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hnpos]; simp
    simp only [hudef, norm_mul, h1, mul_one]
    calc ‖a n‖ * ‖χ n‖ ≤ 1 * 1 := mul_le_mul (ha n) (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
          zero_le_one
      _ = 1 := one_mul 1
  -- the factor `N^{−δ}`, at most `1`
  set c : ℝ := (N : ℝ) ^ (-δ) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
  -- the Taylor polynomial and its remainder
  set P : ℕ → ℝ := fun n => ∑ k ∈ range K, (-δ * x n) ^ k / k.factorial with hPdef
  set r : ℕ → ℝ := fun n => Real.exp (-δ * x n) - P n with hrdef
  have hr : ∀ n ∈ S, |r n| ≤ 2 * (1 / 16) ^ K := by
    intro n hn
    have hxn := hx n hn
    have hy : |-δ * x n| ≤ 1 / 16 := by
      rw [abs_le]; constructor <;> nlinarith
    have hy1 : |-δ * x n| ≤ 1 := by linarith
    have hb := Real.exp_bound hy1 (n := K) (by omega)
    have hK' : ((K.succ : ℕ) : ℝ) / ((K.factorial : ℕ) * K) ≤ 2 := by
      have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hf : (1 : ℝ) ≤ (K.factorial : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero K)
      rw [div_le_iff₀ (by positivity)]
      push_cast
      nlinarith
    calc |r n| ≤ |-δ * x n| ^ K * ((K.succ : ℕ) / ((K.factorial : ℕ) * K : ℝ)) := by
          simpa [hrdef, hPdef] using hb
      _ ≤ (1 / 16) ^ K * 2 := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy K) hK' (by positivity) (by positivity)
      _ = 2 * (1 / 16) ^ K := by ring
  -- the sum, rewritten
  have hsplit : ∀ n ∈ S, a n * χ n * (n : ℂ) ^ (-((δ : ℂ) + γ * I)) =
      (c : ℂ) * (((P n : ℝ) : ℂ) * u n + ((r n : ℝ) : ℂ) * u n) := by
    intro n hn
    rw [cpow_shift (hS0 n hn), rpow_neg_split (Nat.pos_of_ne_zero (hS0 n hn)) (by omega : 0 < N)]
    have he : Real.exp (-δ * Real.log ((n : ℝ) / N)) = P n + r n := by simp [hrdef, hxdef]
    rw [he]; simp only [hudef, hcdef]; push_cast; ring
  have hsum : ∑ n ∈ S, a n * χ n * (n : ℂ) ^ (-((δ : ℂ) + γ * I)) =
      (c : ℂ) * (∑ k ∈ range K, (((-δ) ^ k / k.factorial : ℝ) : ℂ) *
        ∑ n ∈ S, (a n * ((Real.log ((n : ℝ) / N) ^ k : ℝ) : ℂ)) * χ n * (n : ℂ) ^ (((-γ : ℝ) : ℂ) * I) +
        ∑ n ∈ S, ((r n : ℝ) : ℂ) * u n) := by
    have hP : ∀ n, ((P n : ℝ) : ℂ) * u n = ∑ k ∈ range K, (((-δ) ^ k / k.factorial : ℝ) : ℂ) *
        ((a n * ((Real.log ((n : ℝ) / N) ^ k : ℝ) : ℂ)) * χ n * (n : ℂ) ^ (((-γ : ℝ) : ℂ) * I)) := by
      intro n
      simp only [hPdef, hudef, hxdef]
      push_cast
      rw [sum_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_pow]; ring
    rw [sum_congr rfl hsplit, ← mul_sum, sum_add_distrib, sum_congr rfl fun n _ => hP n, sum_comm]
    congr 2
    exact sum_congr rfl fun k _ => by rw [mul_sum]
  -- the bounds
  have hD : ∀ k ∈ range K, ‖(((-δ) ^ k / k.factorial : ℝ) : ℂ) *
      ∑ n ∈ S, (a n * ((Real.log ((n : ℝ) / N) ^ k : ℝ) : ℂ)) * χ n * (n : ℂ) ^ (((-γ : ℝ) : ℂ) * I)‖ ≤
      δ ^ k / k.factorial * (V / 2) := by
    intro k hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_of_nonneg hδ0,
      Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (hcon k (mem_range.1 hk)).le (by positivity)
  have hexp : ∑ k ∈ range K, δ ^ k / k.factorial ≤ 9 / 8 := by
    have h1 := Real.sum_le_exp_of_nonneg hδ0 K
    have h2 := Real.exp_bound' hδ0 (by linarith) (n := 1) (by norm_num)
    simp at h2
    linarith
  have hT1 : ‖∑ k ∈ range K, (((-δ) ^ k / k.factorial : ℝ) : ℂ) *
      ∑ n ∈ S, (a n * ((Real.log ((n : ℝ) / N) ^ k : ℝ) : ℂ)) * χ n * (n : ℂ) ^ (((-γ : ℝ) : ℂ) * I)‖ ≤
      9 / 8 * (V / 2) := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum hD).trans ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right hexp (by positivity)
  have hcardS : (S.card : ℝ) = N := by
    rw [hS, Nat.card_Ioc]; push_cast [show 2 * N - N = N by omega]; ring
  have hT2 : ‖∑ n ∈ S, ((r n : ℝ) : ℂ) * u n‖ ≤ V / 4 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ S, ‖((r n : ℝ) : ℂ) * u n‖ ≤ ∑ _n ∈ S, 2 * (1 / 16 : ℝ) ^ K := by
          refine sum_le_sum fun n hn => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |r n| * ‖u n‖ ≤ (2 * (1 / 16) ^ K) * 1 :=
                mul_le_mul (hr n hn) (hu n hn) (norm_nonneg _) (by positivity)
            _ = 2 * (1 / 16) ^ K := mul_one _
      _ = S.card * (2 * (1 / 16) ^ K) := by rw [sum_const, nsmul_eq_mul]
      _ = 2 * (N : ℝ) * (1 / 16) ^ K := by rw [hcardS]; ring
      _ ≤ V / 4 := htail
  have hfinal : ‖∑ n ∈ S, a n * χ n * (n : ℂ) ^ (-((δ : ℂ) + γ * I))‖ ≤ 13 / 16 * V := by
    rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc c * ‖_ + _‖ ≤ 1 * (9 / 8 * (V / 2) + V / 4) :=
          mul_le_mul hc1 ((norm_add_le _ _).trans (add_le_add hT1 hT2)) (norm_nonneg _) zero_le_one
      _ = 13 / 16 * V := by ring
  linarith

open scoped Classical in
/-- **Proposition 3.1's count off the line**: under `CGLProp31`, for `0 < ε ≤ 1` there is `C ≥ 0` such that for
`q ≥ 1`, `T ≥ 1`, `N ≥ (qT)^{2/3}`, `N^{7/10} ≤ V/2 ≤ N^{4/5}`, `|a_n| ≤ 1` and `K ≥ 1` with `2N·16^{−K} ≤ V/4`,
characters `χ ∈ R` mod `q` with `|Σ_{N<n≤2N} a_nχ(n)n^{−(δ_χ+iγ_χ)}| ≥ V`, `0 ≤ δ_χ ≤ 1/16` and `|γ_χ| ≤ T`, number at
most `K·Cq^ε(qTN)^ε p31B(q, T, N, V/2)`. -/
theorem cgl_shift (h : CGLProp31) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)) (δ γ : DirichletCharacter ℂ q → ℝ)
      (T : ℝ) (N : ℕ) (V : ℝ) (a : ℕ → ℂ) (K : ℕ), 1 ≤ T → ((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ N →
      (N : ℝ) ^ (7 / 10 : ℝ) ≤ V / 2 → V / 2 ≤ (N : ℝ) ^ (4 / 5 : ℝ) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ 1 / 16) → (∀ χ ∈ R, |γ χ| ≤ T) → 1 ≤ K →
      2 * (N : ℝ) * (1 / 16) ^ K ≤ V / 4 →
      (∀ χ ∈ R, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ χ : ℂ) + γ χ * I))‖) →
      (R.card : ℝ) ≤ K * (C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N (V / 2)) := by
  obtain ⟨C, hC0, hC⟩ := cgl_all h hε hε1
  refine ⟨C, hC0, ?_⟩
  intro q _ R δ γ T N V a K hT hN hV1 hV2 ha hδ hγ hK htail hbig
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
    exact_mod_cast h1.trans hN
  have hV : 0 < V := by
    have h1 : (0 : ℝ) < (N : ℝ) ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hN1) _
    linarith
  set D : ℕ → DirichletCharacter ℂ q → ℂ := fun k χ =>
    ∑ n ∈ Ioc N (2 * N), (a n * ((Real.log ((n : ℝ) / N) ^ k : ℝ) : ℂ)) * χ n * (n : ℂ) ^ (((-γ χ : ℝ) : ℂ) * I)
    with hDdef
  have hpick : ∀ χ ∈ R, ∃ k < K, V / 2 ≤ ‖D k χ‖ := by
    intro χ hχ
    exact taylor_pick hN1 ha (hδ χ hχ).1 (hδ χ hχ).2 hV hK htail χ (hbig χ hχ)
  have hsub : R ⊆ (range K).biUnion fun k => R.filter fun χ => V / 2 ≤ ‖D k χ‖ := by
    intro χ hχ
    obtain ⟨k, hk, hkV⟩ := hpick χ hχ
    exact mem_biUnion.2 ⟨k, mem_range.2 hk, mem_filter.2 ⟨hχ, hkV⟩⟩
  have hk : ∀ k ∈ range K, ((R.filter fun χ => V / 2 ≤ ‖D k χ‖).card : ℝ) ≤
      C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N (V / 2) := by
    intro k _
    set ak : ℕ → ℂ := fun n => if n ∈ Ioc N (2 * N) then a n * ((Real.log ((n : ℝ) / N) ^ k : ℝ) : ℂ) else 0
      with hakdef
    have hak : ∀ n, ‖ak n‖ ≤ 1 := by
      intro n
      simp only [hakdef]
      split_ifs with hn
      · obtain ⟨h1, h2⟩ := mem_Ioc.1 hn
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
        have hn1 : (N : ℝ) < n := by exact_mod_cast h1
        have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast h2
        have hl0 : 0 ≤ Real.log ((n : ℝ) / N) := Real.log_nonneg (by rw [le_div_iff₀ hNpos]; linarith)
        have hl1 : Real.log ((n : ℝ) / N) ≤ 1 :=
          calc Real.log ((n : ℝ) / N) ≤ Real.log 2 :=
                Real.log_le_log (div_pos (by linarith) hNpos) (by rw [div_le_iff₀ hNpos]; linarith)
            _ ≤ 1 := by have := Real.log_two_lt_d9; linarith
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg hl0]
        calc ‖a n‖ * Real.log ((n : ℝ) / N) ^ k ≤ 1 * 1 :=
              mul_le_mul (ha n) (pow_le_one₀ hl0 hl1) (by positivity) zero_le_one
          _ = 1 := one_mul 1
      · simp
    have hbig' : ∀ χ ∈ R.filter fun χ => V / 2 ≤ ‖D k χ‖,
        V / 2 ≤ ‖∑ n ∈ Ioc N (2 * N), ak n * χ n * (n : ℂ) ^ (((-γ χ : ℝ) : ℂ) * I)‖ := by
      intro χ hχ
      have e : ∑ n ∈ Ioc N (2 * N), ak n * χ n * (n : ℂ) ^ (((-γ χ : ℝ) : ℂ) * I) = D k χ :=
        sum_congr rfl fun n hn => by simp only [hakdef, hn, ↓reduceIte]
      rw [e]; exact (mem_filter.1 hχ).2
    exact hC q (R.filter fun χ => V / 2 ≤ ‖D k χ‖) (fun χ => -γ χ) T N (V / 2) ak hT hN hV1 hV2 hak
      (fun χ hχ => by rw [abs_neg]; exact hγ χ (mem_filter.1 hχ).1) hbig'
  calc (R.card : ℝ) ≤ (((range K).biUnion fun k => R.filter fun χ => V / 2 ≤ ‖D k χ‖).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, ((R.filter fun χ => V / 2 ≤ ‖D k χ‖).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _k ∈ range K, C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N (V / 2) := sum_le_sum hk
    _ = K * (C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N (V / 2)) := by
        rw [sum_const, card_range, nsmul_eq_mul]

end LinnikCGLLV

#print axioms LinnikCGLLV.lv_range
#print axioms LinnikCGLLV.cgl_all
#print axioms LinnikCGLLV.taylor_pick
#print axioms LinnikCGLLV.cgl_shift
