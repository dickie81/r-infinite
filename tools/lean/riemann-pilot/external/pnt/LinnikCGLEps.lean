/-
# Round 677: their Lemmas 10.9 and 10.10 with their `⪅`, and their Proposition 10.2 (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Proposition 10.2: "Let D_N(t, χ) = Σ_{N<n≤2N} a_nχ(n)n^{it}, where χ is a primitive character modulo q and
|a_n| ≤ 1. Suppose that W is a finite set of pairs (t, χ), where |t| ≤ T and for (t, χ) ≠ (t′, χ′) either χ ≠ χ′ or
|t − t′| ≥ (qT)^ϵ. Assume that |D_N(t, χ)| ≥ N^σ/6 for all (t, χ) ∈ W and (qT)^{2/3}/2 ≤ N ≤ qT. Assume that either
|W| ≥ (qT)^{2/3} or that E(W)^{1/8}N ≥ (qT)^{1/2}|W|^{5/8}. Then we have E(W) ⪅_ϵ |W|N^{4−4σ} +
|W|^{21/8}(qT)^{1/4}N^{1−2σ} + |W|³N^{1−2σ}." (text layer lines 4637–4656.)

Their proof: "First, we use Lemma 10.5 to obtain E(W) ⪅ N^{−2σ} Σ_{n₁,n₂∼N, (n₁n₂,q)=1} |R(n₁/n₂, n₁n₂^{−1})|³."
(lines 5500–5512); "By splitting the sum based on whether (n₁, n₂) ≤ D nor not and applying (10.3) and Lemma 10.10,
we find E(W) ⪅ N^{−2σ}(N|W|³ + N(qT)^{1/4}|W|^{21/8} + E(W)^{1/2}|W|^{1/2}N²). so that E(W) ⪅ |W|N^{4−4σ} +
|W|^{21/8}(qT)^{1/4}N^{1−2σ} + |W|³N^{1−2σ}, as required." (lines 5513–5518.) Their (10.3) is their Lemma 10.9,
"⪅_ϵ (DqT + N²)|W|^{1/2}E(W)^{1/2}." (line 5082), at "D = N²/(qT)" (line 5300): "⪅ N²|W|^{1/2}E(W)^{1/2}."
(line 5314). In all of these, spaces are restored and the sums, fractions, large bars, large parentheses, subscripts
and exponents transcribed; "nor" is as printed (the PDF's page 47 has it).

The stack's form.
* One point per character. The stack's points have distinct characters (`Set.InjOn χ R`), which suffices for
  `CGLDensity`, a count of characters (`frontier/linnik/CGL-LEAN.md`, "One point per character"); their spacing
  hypothesis then holds.
* Their `a_n`. The stack sums `b_nχ_i(n)n^{it_i}` over a set `S ⊆ (N, 2N]` with `|b_n| ≤ 1`: their `D_N` with
  `a_n = b_n` on `S` and `a_n = 0` off it.
* Their `⪅`. Each result carries a constant for each `ε`: `C max(1, N)^ε` in `lemma109_eps`, `C(2qTN)^ε` in
  `lemma1010_eps` and `C(qTN)^ε` in `prop102`. For `N ≤ qT` the last is at most `C(qT)^{2ε}`. The stack does not use
  `N ≤ qT`.
* Their (10.3). `lemma109_eps` is their Lemma 10.9 at `DqT ≤ N²`, with the term `N|R|³`, which bounds round 674's
  term `|R|⁴D_K/X^K` (`eps_absorb`) and its tail (`eps_tail`). Their (10.3) does not have this term. Their Lemma
  10.10's bound has it, so their Proposition 10.2's bound is the same.
* `lemma1010_eps` is round 676's `lemma1010_case` with `d(q) ≤ C_δq^δ` (round 525's `card_divisors_le`) and
  `|R| ≤ φ(q) ≤ q` (`card_le_totient`) for `G`, `1 + log max(1, N) ≤ (1 + 1/δ)max(1, N)^δ` (`log_max_le`) for `L`,
  and `|{n ∼ N}| ≤ N + 1 ≤ 3N` (`card_dyad_le`) for round 675's term `|{n ∼ N}||R|³`.
* `prop102`. Round 669's `lemma105` gives `E ≤ 36(N^σ)^{−2}∫κ·Σ_{n₁,n₂∈S}|R₂(n₁, n₂)|³`; `sum_S_le` splits the
  cubes at `D = ⌊N²/(qT)⌋` into `lemma109_eps` and `lemma1010_eps` at `ε/2`. That gives `E ≤ A + B√E`, and `quad_le`
  gives `E ≤ 2A + B²`, their "so that".

Plain statements, with `q ≥ 1`, `n ∼ N` round 670's `dyad`, `R₂` round 669's, `E` round 659's `energy` and
`CGLT101` round 670's displayed hypothesis.
* `card_le_totient`, `card_dyad_le`, `sqrt_add_le`: `|R| ≤ φ(q)` for `χ` injective on `R`; `|{n ∼ N}| ≤ N + 1` for
  `N ≥ 0`; and `√(x + y) ≤ √x + √y` for `x, y ≥ 0`.
* `eps_sqrt_le`, `eps_absorb`, `eps_tail`, `eps_Z`, `card_pairs_le`, `eps_combine`: the steps of `lemma109_eps`.
* `lemma109_eps`: for every `ε > 0` there is `C ≥ 0` such that, for `χ` injective on `R`, `T ≥ 1`, points
  `|t_i| ≤ T`, `N ≥ 1/2` and `D ∈ ℕ` with `DqT ≤ N²`, `Σ_{n₁,n₂∼N, (n₁,n₂)≤D}|R₂(n₁, n₂)|³ ≤
  C max(1, N)^ε(N²√(|R|E) + N|R|³)`.
* `natlog_le`, `log_max_le`, `factor_le`: the steps of `lemma1010_eps`.
* `lemma1010_eps`: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for primitive characters injective
  on `R`, `T ≥ 1`, points `|t_i| ≤ T`, `(qT)^{2/3}/2 ≤ N`, `D = ⌊N²/(qT)⌋` and either `|R| ≥ (qT)^{2/3}` or
  `(qT)^{1/2}|R|^{5/8} ≤ E^{1/8}N`, `Σ_{n₁,n₂∼N, (n₁,n₂)>D}|R₂(n₁, n₂)|³ ≤
  C(2qTN)^ε(N|R|³ + N(qT)^{1/4}|R|^{21/8} + N²√(|R|E))`.
* `quad_le`, `sum_S_le`, `rpow_four_sub`, `sq_rpow_half`, `prop102_fin`, `prop102_sum`: the steps of `prop102`.
* `prop102`: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for primitive characters injective on
  `R`, `T ≥ 1`, points `|t_i| ≤ T`, `(qT)^{2/3}/2 ≤ N`, `S ⊆ (N, 2N]`, `|b_n| ≤ 1`, `|Σ_{n∈S}b_nχ_i(n)n^{it_i}| ≥
  N^σ/6` for `i ∈ R` and either `|R| ≥ (qT)^{2/3}` or `(qT)^{1/2}|R|^{5/8} ≤ E^{1/8}N`,
  `E ≤ C(qTN)^ε(|R|N^{4−4σ} + |R|^{21/8}(qT)^{1/4}N^{1−2σ} + |R|³N^{1−2σ})`.

The file imports `LinnikCGLCase.lean`.
-/

import LinnikCGLCase

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLEps

open LinnikCGLL105 LinnikCGLMom4 LinnikCGLRt LinnikCGLT101 LinnikCGLL109 LinnikCGLL1010 LinnikCGLCase

/-! ### Counting -/

/-- `|R| ≤ φ(q)` at one point per character: there are `φ(q)` Dirichlet characters modulo `q` (Mathlib's
`card_eq_totient_of_hasEnoughRootsOfUnity`). -/
lemma card_le_totient {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) : R.card ≤ q.totient := by
  classical
  have h1 : R.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card :=
    Finset.card_le_card_of_injOn χ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q] at h1
  exact h1

/-- `|{n ∼ N}| ≤ N + 1` for `N ≥ 0`. -/
lemma card_dyad_le {N : ℝ} (hN : 0 ≤ N) : ((dyad N).card : ℝ) ≤ N + 1 := by
  unfold dyad
  rw [Nat.card_Ioc]
  have h1 : (⌊N⌋₊ : ℝ) ≤ ⌊2 * N⌋₊ := by exact_mod_cast Nat.floor_le_floor (by linarith)
  have h2 : ((⌊2 * N⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) = (⌊2 * N⌋₊ : ℝ) - ⌊N⌋₊ := by
    rw [Nat.cast_sub (by exact_mod_cast h1)]
  rw [h2]
  have h3 : (⌊2 * N⌋₊ : ℝ) ≤ 2 * N := Nat.floor_le (by linarith)
  have h4 : N < (⌊N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one N
  linarith

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
lemma sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : 0 ≤ √x * √y := by positivity
  nlinarith

/-! ### Their Lemma 10.9 with `⪅` -/

/-- The square root of round 674's lemma: `√(rI(IE + r⁴D/X^K)) ≤ I√(rE) + √(ID)√(r⁵/X^K)` for `r, I, E, D ≥ 0`
and `X > 0`. -/
lemma eps_sqrt_le {r I E D X : ℝ} (K : ℕ) (hr : 0 ≤ r) (hI : 0 ≤ I) (hE : 0 ≤ E) (hD : 0 ≤ D) (hX : 0 < X) :
    √(r * I * (I * E + r ^ 4 * D / X ^ K)) ≤ I * √(r * E) + √(I * D) * √(r ^ 5 / X ^ K) := by
  have e1 : r * I * (I * E + r ^ 4 * D / X ^ K) = I ^ 2 * (r * E) + I * D * (r ^ 5 / X ^ K) := by
    field_simp
  rw [e1]
  refine (sqrt_add_le (by positivity) (by positivity)).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ I ^ 2 by positivity) (r * E),
    Real.sqrt_mul (show (0 : ℝ) ≤ I * D by positivity) (r ^ 5 / X ^ K), Real.sqrt_sq hI]

/-- The term `r⁴D/X^K` absorbed: for `K = 2m + 2`, `0 ≤ N ≤ M ≤ X^m`, `X > 0` and `r = 0` or `r ≥ 1`,
`N²X√(r⁵/X^K) ≤ Nr³`. -/
lemma eps_absorb {r N M X : ℝ} {m K : ℕ} (hK : K = 2 * m + 2) (hr : r = 0 ∨ 1 ≤ r) (hN : 0 ≤ N) (hNM : N ≤ M)
    (hX : 0 < X) (hXm : M ≤ X ^ m) : N ^ 2 * X * √(r ^ 5 / X ^ K) ≤ N * r ^ 3 := by
  have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
  have e1 : X * √(r ^ 5 / X ^ K) = √(r ^ 5) / X ^ m := by
    have e2 : r ^ 5 / X ^ K = r ^ 5 / (X ^ m) ^ 2 / X ^ 2 := by
      rw [hK, ← pow_mul, div_div, ← pow_add]
      ring_nf
    rw [e2, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hX.le, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity)]
    field_simp
  have hr5 : √(r ^ 5) ≤ r ^ 3 := by
    rw [Real.sqrt_le_left (by positivity)]
    rcases hr with h0 | h1
    · rw [h0]; norm_num
    · have : r ^ 5 ≤ r ^ 6 := pow_le_pow_right₀ h1 (by norm_num)
      calc r ^ 5 ≤ r ^ 6 := this
        _ = (r ^ 3) ^ 2 := by ring
  rw [mul_assoc, e1]
  have hXm0 : 0 < X ^ m := by positivity
  rw [mul_div_assoc', div_le_iff₀ hXm0]
  have h1 : N ^ 2 * √(r ^ 5) ≤ N ^ 2 * r ^ 3 := mul_le_mul_of_nonneg_left hr5 (by positivity)
  have h2 : N * r ^ 3 * M ≤ N * r ^ 3 * X ^ m := mul_le_mul_of_nonneg_left hXm (by positivity)
  have h3 : N * (N * r ^ 3) ≤ M * (N * r ^ 3) := mul_le_mul_of_nonneg_right hNM (by positivity)
  have e3 : N ^ 2 * r ^ 3 = N * (N * r ^ 3) := by ring
  have e4 : M * (N * r ^ 3) = N * r ^ 3 * M := by ring
  linarith

/-- The tail of round 674's lemma: for `c ≤ Z^k` with `Z^k > 0`, `N ≥ 1/2` and `ct, r ≥ 0`,
`c·r³·ct/Z^k ≤ 2ct·Nr³`. -/
lemma eps_tail {c Zk ct r N : ℝ} (hZ : 0 < Zk) (hc : c ≤ Zk) (hct : 0 ≤ ct) (hr : 0 ≤ r) (hN : 1 / 2 ≤ N) :
    c * r ^ 3 * (ct / Zk) ≤ 2 * ct * (N * r ^ 3) := by
  by_cases hc0 : c ≤ 0
  · have : c * r ^ 3 * (ct / Zk) ≤ 0 := by
      have : 0 ≤ r ^ 3 * (ct / Zk) := by positivity
      nlinarith
    have : 0 ≤ 2 * ct * (N * r ^ 3) := by
      have : 0 ≤ N := by linarith
      positivity
    linarith
  · push Not at hc0
    have h1 : c / Zk ≤ 1 := by rw [div_le_one hZ]; exact hc
    have e : c * r ^ 3 * (ct / Zk) = ct * r ^ 3 * (c / Zk) := by ring
    rw [e]
    have h2 : ct * r ^ 3 * (c / Zk) ≤ ct * r ^ 3 := mul_le_of_le_one_right (by positivity) h1
    have h3 : ct * r ^ 3 * 1 ≤ ct * r ^ 3 * (2 * N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : ct * r ^ 3 * (2 * N) = 2 * ct * (N * r ^ 3) := by ring
    linarith

/-- `7Y ≤ 3T(16Y − 1)/(2π)` and so `4M² ≤ (3T(16Y − 1)/(2π))^{2m}` for `T, Y ≥ 1`, `Y^m = M` and `m ≥ 1`. -/
lemma eps_Z {T Y M : ℝ} {m : ℕ} (hT : 1 ≤ T) (hY : 1 ≤ Y) (hYm : Y ^ m = M) (hm : 1 ≤ m) :
    4 * M ^ 2 ≤ (3 * T * (16 * Y - 1) / (2 * π)) ^ (2 * m) := by
  have hZ : 7 * Y ≤ 3 * T * (16 * Y - 1) / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have hpi : π < 3.15 := Real.pi_lt_d2
    have h1 : 3 * (16 * Y - 1) ≤ 3 * T * (16 * Y - 1) := by
      have : 0 ≤ 16 * Y - 1 := by linarith
      nlinarith
    nlinarith
  have h1 : (7 * Y) ^ (2 * m) ≤ (3 * T * (16 * Y - 1) / (2 * π)) ^ (2 * m) :=
    pow_le_pow_left₀ (by positivity) hZ _
  have h2 : (7 * Y) ^ (2 * m) = 49 ^ m * M ^ 2 := by
    calc (7 * Y) ^ (2 * m) = ((7 * Y) ^ 2) ^ m := pow_mul _ _ _
      _ = (49 * Y ^ 2) ^ m := by ring
      _ = 49 ^ m * (Y ^ m) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 m]
      _ = 49 ^ m * M ^ 2 := by rw [hYm]
  have h3 : (49 : ℝ) ≤ 49 ^ m := by
    calc (49 : ℝ) = 49 ^ 1 := (pow_one _).symm
      _ ≤ 49 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have h4 : 0 ≤ M ^ 2 := by positivity
  have h5 : 4 * M ^ 2 ≤ 49 ^ m * M ^ 2 := by nlinarith
  linarith

/-- The pairs `n₁, n₂ ∼ N` number at most `4M²` for `0 ≤ N ≤ M` and `M ≥ 1`. -/
lemma card_pairs_le {N M : ℝ} (D : ℕ) (hN : 0 ≤ N) (hNM : N ≤ M) (hM : 1 ≤ M) :
    ((pairs N D).card : ℝ) ≤ 4 * M ^ 2 := by
  have h1 : (pairs N D).card ≤ (dyad N ×ˢ dyad N).card := Finset.card_filter_le _ _
  rw [Finset.card_product] at h1
  have h2 : ((pairs N D).card : ℝ) ≤ (dyad N).card * (dyad N).card := by exact_mod_cast h1
  have h5 : ((dyad N).card : ℝ) ≤ 2 * M := (card_dyad_le hN).trans (by linarith)
  have h6 : (0 : ℝ) ≤ (dyad N).card := by positivity
  have h7 : ((dyad N).card : ℝ) * (dyad N).card ≤ (2 * M) * (2 * M) := mul_le_mul h5 h5 h6 (by linarith)
  nlinarith

/-- The assembly of `lemma109_eps`: from `S ≤ A + B`, `A ≤ C₁MεP + C₂Q` and `B ≤ C₃Q`, for `Mε ≥ 1` and
`C₁, C₂, C₃, P, Q ≥ 0`, `S ≤ (C₁ + C₂ + C₃)Mε(P + Q)`. -/
lemma eps_combine {S A B C₁ C₂ C₃ Mε P Q : ℝ} (hS : S ≤ A + B) (hA : A ≤ C₁ * Mε * P + C₂ * Q) (hB : B ≤ C₃ * Q)
    (hMε : 1 ≤ Mε) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₁ : 0 ≤ C₁) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    S ≤ (C₁ + C₂ + C₃) * Mε * (P + Q) := by
  have h1 : C₂ * Q ≤ C₂ * Mε * Q := by
    have := mul_le_mul_of_nonneg_left hMε (mul_nonneg hC₂ hQ)
    nlinarith
  have h2 : C₃ * Q ≤ C₃ * Mε * Q := by
    have := mul_le_mul_of_nonneg_left hMε (mul_nonneg hC₃ hQ)
    nlinarith
  have h3 : 0 ≤ C₁ * Mε * Q := by positivity
  have h4 : 0 ≤ (C₂ + C₃) * Mε * P := by positivity
  nlinarith

/-- **Their Lemma 10.9 with their `⪅`**: for every `ε > 0` there is `C ≥ 0` such that, for `q ≥ 1`, `χ` injective on
`R`, `T ≥ 1`, points `|t_i| ≤ T`, `N ≥ 1/2` and `D ∈ ℕ` with `DqT ≤ N²`,
`Σ_{n₁,n₂∼N, (n₁,n₂)≤D}|R₂(n₁, n₂)|³ ≤ C max(1, N)^ε(N²√(|R|E) + N|R|³)`. Round 674's `lemma109` with
`K = 2m + 2`, `m = ⌈1/ε⌉` and `X = 16max(1, N)^{1/m}`: then `X^m ≥ max(1, N)` absorbs the term `|R|⁴D_K/X^K`
into `N|R|³` (`eps_absorb`), and `Z = 3T(X − 1)/(2π) ≥ 7max(1, N)^{1/m}` makes the tail at most a constant times
`N|R|³` (`eps_Z`, `eps_tail`). -/
theorem lemma109_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T N : ℝ) (D : ℕ), Set.InjOn χ R → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) → 1 / 2 ≤ N →
      (D : ℝ) * ((q : ℝ) * T) ≤ N ^ 2 →
      ∑ p ∈ pairs N D, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤
        C * (max 1 N) ^ ε * (N ^ 2 * √((R.card : ℝ) * energy R χ t) + N * (R.card : ℝ) ^ 3) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈1 / ε⌉₊ := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [hm]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hδε : 1 / (m : ℝ) ≤ ε := by
    have h1 : 1 / ε ≤ m := hm ▸ Nat.le_ceil _
    rw [div_le_iff₀ hm0]
    rw [div_le_iff₀ hε] at h1
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 * m + 2 := ⟨_, rfl⟩
  have hK2 : 2 ≤ K := by omega
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ x, psi0 x := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hI]; exact integral_nonneg psi0_nonneg
  have hD0 : 0 ≤ Dpsi K := Dpsi_nonneg K
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 3 + 64 * π := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨ct, hct⟩ : ∃ ct : ℝ, ct = 2 * π * (Dpsi K / (2 * π) ^ K) := ⟨_, rfl⟩
  have hct0 : 0 ≤ ct := by rw [hct]; positivity
  have hCk := Ck_nonneg
  refine ⟨Ck * c₀ * 16 * I + Ck * c₀ * √(I * Dpsi K) + 2 * ct, by positivity, ?_⟩
  intro q _ ι R χ t T N D hinj hT ht hN hDN
  have hN0 : 0 < N := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max 1 N := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : 1 ≤ M := hM ▸ le_max_left _ _
  have hNM : N ≤ M := hM ▸ le_max_right _ _
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = M ^ (1 / (m : ℝ)) := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [hY]; exact Real.one_le_rpow hM1 (by positivity)
  have hYm : Y ^ m = M := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have : 1 / (m : ℝ) * m = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hYε : Y ≤ M ^ ε := by rw [hY]; exact Real.rpow_le_rpow_of_exponent_le hM1 hδε
  have hMε1 : 1 ≤ M ^ ε := Real.one_le_rpow hM1 hε.le
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 16 * Y := ⟨_, rfl⟩
  have hX4 : 4 ≤ X := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have hXm : M ≤ X ^ m := by
    rw [hX, mul_pow, hYm]
    have : (1 : ℝ) ≤ 16 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have h := lemma109 R χ t hinj hT ht hN0 hX4 D hK2
  rw [← hI] at h
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (R.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (energy R χ t : ℝ) := ⟨_, rfl⟩
  rw [← hr, ← hE] at h ⊢
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hr1 : r = 0 ∨ 1 ≤ r := by
    rw [hr]
    rcases Nat.eq_zero_or_pos R.card with h0 | h0
    · left; exact_mod_cast h0
    · right; exact_mod_cast h0
  -- the coefficient
  have hs1 : 3 * (D : ℝ) * q * T + 64 * π * N ^ 2 ≤ c₀ * N ^ 2 := by
    have e : 3 * (D : ℝ) * q * T = 3 * ((D : ℝ) * ((q : ℝ) * T)) := by ring
    rw [e, hc₀]
    linarith
  have hs2 := eps_sqrt_le K hr0 hI0 hE0 hD0 hX0
  have hs3 := eps_absorb hK hr1 hN0.le hNM hX0 hXm
  -- the tail
  have hZK : 4 * M ^ 2 ≤ (3 * T * (X - 1) / (2 * π)) ^ (K - 2) := by
    have e : K - 2 = 2 * m := by omega
    rw [e, hX]
    exact eps_Z hT hY1 hYm hm1
  have hZ0 : 0 < (3 * T * (X - 1) / (2 * π)) ^ (K - 2) := by
    have : 0 < 3 * T * (X - 1) / (2 * π) := by
      have : 0 < X - 1 := by linarith
      positivity
    positivity
  have hcard := card_pairs_le D hN0.le hNM hM1
  have hs4 : ((pairs N D).card : ℝ) * r ^ 3 *
      (2 * π * (Dpsi K / (2 * π) ^ K / (3 * T * (X - 1) / (2 * π)) ^ (K - 2))) ≤ 2 * ct * (N * r ^ 3) := by
    have e : 2 * π * (Dpsi K / (2 * π) ^ K / (3 * T * (X - 1) / (2 * π)) ^ (K - 2)) =
        ct / (3 * T * (X - 1) / (2 * π)) ^ (K - 2) := by
      rw [hct]; field_simp
    rw [e]
    exact eps_tail hZ0 (hcard.trans hZK) hct0 hr0 hN
  -- the main term
  have hmain : Ck * (3 * (D : ℝ) * q * T + 64 * π * N ^ 2) * X *
      √(r * I * (I * E + r ^ 4 * Dpsi K / X ^ K)) ≤
      Ck * c₀ * 16 * I * M ^ ε * (N ^ 2 * √(r * E)) + Ck * c₀ * √(I * Dpsi K) * (N * r ^ 3) := by
    have h1 : Ck * (3 * (D : ℝ) * q * T + 64 * π * N ^ 2) * X ≤ Ck * (c₀ * N ^ 2) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 hCk) hX0.le
    have h2 := mul_le_mul h1 hs2 (Real.sqrt_nonneg _) (by positivity)
    have h3 : Ck * (c₀ * N ^ 2) * X * (I * √(r * E)) ≤ Ck * c₀ * 16 * I * M ^ ε * (N ^ 2 * √(r * E)) := by
      have e : Ck * (c₀ * N ^ 2) * X * (I * √(r * E)) = Ck * c₀ * 16 * I * Y * (N ^ 2 * √(r * E)) := by
        rw [hX]; ring
      rw [e]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hYε (by positivity)
    have h4 : Ck * (c₀ * N ^ 2) * X * (√(I * Dpsi K) * √(r ^ 5 / X ^ K)) ≤
        Ck * c₀ * √(I * Dpsi K) * (N * r ^ 3) := by
      have e : Ck * (c₀ * N ^ 2) * X * (√(I * Dpsi K) * √(r ^ 5 / X ^ K)) =
          Ck * c₀ * √(I * Dpsi K) * (N ^ 2 * X * √(r ^ 5 / X ^ K)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hs3 (by positivity)
    have e5 : Ck * (c₀ * N ^ 2) * X * (I * √(r * E) + √(I * Dpsi K) * √(r ^ 5 / X ^ K)) =
        Ck * (c₀ * N ^ 2) * X * (I * √(r * E)) + Ck * (c₀ * N ^ 2) * X * (√(I * Dpsi K) * √(r ^ 5 / X ^ K)) := by
      ring
    linarith
  exact eps_combine h hmain hs4 hMε1 (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity)

/-! ### Their Lemma 10.10 with `⪅` -/

/-- `⌊log₂n⌋ + 1 ≤ (2/(δ log 2) + 1)q^δ` for `n ≤ q²`, `q ≥ 1` and `δ > 0`, from `log q ≤ q^δ/δ`. -/
lemma natlog_le {q n : ℕ} (hq : 1 ≤ q) (hn : n ≤ q ^ 2) {δ : ℝ} (hδ : 0 < δ) :
    (Nat.log 2 n : ℝ) + 1 ≤ (2 / (δ * Real.log 2) + 1) * (q : ℝ) ^ δ := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqδ : 1 ≤ (q : ℝ) ^ δ := Real.one_le_rpow hq1 hδ.le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ 2 * Real.log q := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, Nat.log_zero_right, Nat.cast_zero, zero_mul]
      exact mul_nonneg (by norm_num) (Real.log_nonneg hq1)
    · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 h0.ne'
      have h2 : ((2 : ℕ) ^ Nat.log 2 n : ℝ) ≤ ((q ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1.trans hn
      push_cast at h2
      have h3 := Real.log_le_log (by positivity) h2
      rw [Real.log_pow, Real.log_pow] at h3
      push_cast at h3
      linarith
  have hlq : Real.log q ≤ (q : ℝ) ^ δ / δ := Real.log_le_rpow_div (by positivity) hδ
  have h4 : (Nat.log 2 n : ℝ) ≤ 2 / (δ * Real.log 2) * (q : ℝ) ^ δ := by
    rw [← le_div_iff₀ hl2] at hlog
    calc (Nat.log 2 n : ℝ) ≤ 2 * Real.log q / Real.log 2 := hlog
      _ ≤ 2 * ((q : ℝ) ^ δ / δ) / Real.log 2 := by gcongr
      _ = 2 / (δ * Real.log 2) * (q : ℝ) ^ δ := by field_simp
  nlinarith

/-- `1 + log max(1, N) ≤ (1 + 1/δ)max(1, N)^δ` for `δ > 0`. -/
lemma log_max_le (N : ℝ) {δ : ℝ} (hδ : 0 < δ) : 1 + Real.log (max 1 N) ≤ (1 + 1 / δ) * (max 1 N) ^ δ := by
  have hM1 : 1 ≤ max 1 N := le_max_left _ _
  have h1 : Real.log (max 1 N) ≤ (max 1 N) ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ
  have h2 : 1 ≤ (max 1 N) ^ δ := Real.one_le_rpow hM1 hδ.le
  have e : (1 + 1 / δ) * (max 1 N) ^ δ = (max 1 N) ^ δ + (max 1 N) ^ δ / δ := by field_simp
  rw [e]
  linarith

/-- The factors of `lemma1010_case` against `(2qTN)^ε`: for `q, T ≥ 1`, `N ≥ 1/2` and `0 ≤ 4δ ≤ ε`,
`q^δ·q^δ·(qTN)^δ·max(1, N)^δ ≤ (2qTN)^ε`. -/
lemma factor_le {q T N δ ε : ℝ} (hq : 1 ≤ q) (hT : 1 ≤ T) (hN : 1 / 2 ≤ N) (hδ : 0 ≤ δ) (hδε : 4 * δ ≤ ε) :
    q ^ δ * q ^ δ * (q * T * N) ^ δ * (max 1 N) ^ δ ≤ (2 * q * T * N) ^ ε := by
  have hB : 1 ≤ 2 * q * T * N := by
    have : 1 ≤ q * T := one_le_mul_of_one_le_of_one_le hq hT
    nlinarith
  have hqB : q ≤ 2 * q * T * N := by
    have : q * 1 ≤ q * (2 * T * N) := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    nlinarith
  have hqTN : q * T * N ≤ 2 * q * T * N := by
    have hN0 : 0 ≤ N := by linarith
    have : 0 ≤ q * T * N := by positivity
    linarith
  have hMB : max 1 N ≤ 2 * q * T * N := by
    have hqT : 1 ≤ q * T := one_le_mul_of_one_le_of_one_le hq hT
    have h2N : 2 * N ≤ 2 * q * T * N := by
      have : 2 * N * 1 ≤ 2 * N * (q * T) := mul_le_mul_of_nonneg_left hqT (by linarith)
      nlinarith
    exact max_le (by linarith) (by linarith)
  have h0 : 0 ≤ q * T * N := by
    have : 0 ≤ N := by linarith
    have : 0 ≤ q * T := by nlinarith
    positivity
  calc q ^ δ * q ^ δ * (q * T * N) ^ δ * (max 1 N) ^ δ
      ≤ (2 * q * T * N) ^ δ * (2 * q * T * N) ^ δ * (2 * q * T * N) ^ δ * (2 * q * T * N) ^ δ := by
        gcongr
    _ = (2 * q * T * N) ^ (4 * δ) := by
        rw [show (4 : ℝ) * δ = δ + δ + δ + δ by ring, Real.rpow_add (by linarith), Real.rpow_add (by linarith),
          Real.rpow_add (by linarith)]
    _ ≤ (2 * q * T * N) ^ ε := Real.rpow_le_rpow_of_exponent_le hB hδε

/-- **Their Lemma 10.10 with their `⪅`**: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for `q ≥ 1`,
primitive characters injective on `R`, `T ≥ 1`, points `|t_i| ≤ T`, `(qT)^{2/3}/2 ≤ N`, `D = ⌊N²/(qT)⌋` and either
`|R| ≥ (qT)^{2/3}` or `(qT)^{1/2}|R|^{5/8} ≤ E^{1/8}N`, `Σ_{n₁,n₂∼N, (n₁,n₂)>D}|R₂(n₁, n₂)|³ ≤
C(2qTN)^ε(N|R|³ + N(qT)^{1/4}|R|^{21/8} + N²√(|R|E))`. Round 676's `lemma1010_case` at `δ = min(ε/4, 1)`, with
the divisor bound `d(q) ≤ C_δq^δ` (round 525's `card_divisors_le`), `|R| ≤ φ(q) ≤ q` (`card_le_totient`) for the
logarithm `⌊log₂|R|²⌋ + 1`, and `1 + log max(1, N) ≤ (1 + 1/δ)max(1, N)^δ`. -/
theorem lemma1010_eps (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T N : ℝ), 1 ≤ T → (∀ i ∈ R, (χ i).IsPrimitive) → Set.InjOn χ R → (∀ i ∈ R, |t i| ≤ T) →
      ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N →
      (((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ R.card ∨
        ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (R.card : ℝ) ^ (5 / 8 : ℝ) ≤ (energy R χ t : ℝ) ^ (1 / 8 : ℝ) * N) →
      ∑ p ∈ pairsGt N ⌊N ^ 2 / ((q : ℝ) * T)⌋₊, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤
        C * (2 * (q : ℝ) * T * N) ^ ε *
          (N * (R.card : ℝ) ^ 3 + N * ((q : ℝ) * T) ^ (1 / 4 : ℝ) * (R.card : ℝ) ^ (21 / 8 : ℝ) +
            N ^ 2 * √((R.card : ℝ) * energy R χ t)) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 4) 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_right _ _
  have hδε : 4 * δ ≤ ε := by have := hδ ▸ min_le_left (ε / 4) 1; linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := lemma1010_case hT hδ0
  obtain ⟨cG, hcG⟩ : ∃ cG : ℝ, cG = LinnikPower.Cdiv δ * (2 / (δ * Real.log 2) + 1) := ⟨_, rfl⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCd : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ0 hδ1
  have hcG0 : 0 ≤ cG := by rw [hcG]; positivity
  refine ⟨8 * C₁ * cG * (1 + 1 / δ) + 3, by positivity, ?_⟩
  intro q _ ι R χ t T N hT1 hprim hinj ht hN halt
  have h := hC₁ q R χ t T N hT1 hprim hinj ht hN halt
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT1
  have hN2 : 1 / 2 ≤ N := by
    have : 1 ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  -- the divisor factor
  have hG : (q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1) ≤ cG * ((q : ℝ) ^ δ * (q : ℝ) ^ δ) := by
    have h1 := LinnikPower.card_divisors_le hδ0 hδ1 q
    have hRq : R.card ^ 2 ≤ q ^ 2 := by
      have := card_le_totient R hinj
      exact Nat.pow_le_pow_left (this.trans (Nat.totient_le q)) 2
    have h2 := natlog_le (Nat.one_le_iff_ne_zero.2 (NeZero.ne q)) hRq hδ0
    have h3 : (0 : ℝ) ≤ (Nat.log 2 (R.card ^ 2) : ℝ) + 1 := by positivity
    rw [hcG]
    calc (q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)
        ≤ (LinnikPower.Cdiv δ * (q : ℝ) ^ δ) * ((2 / (δ * Real.log 2) + 1) * (q : ℝ) ^ δ) :=
          mul_le_mul h1 h2 h3 (by positivity)
      _ = LinnikPower.Cdiv δ * (2 / (δ * Real.log 2) + 1) * ((q : ℝ) ^ δ * (q : ℝ) ^ δ) := by ring
  have hL := log_max_le N hδ0
  have hfac := factor_le hq1 hT1 hN2 hδ0.le hδε
  -- the sum
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = N * (R.card : ℝ) ^ 3 + N * ((q : ℝ) * T) ^ (1 / 4 : ℝ) * (R.card : ℝ) ^ (21 / 8 : ℝ) +
      N ^ 2 * √((R.card : ℝ) * energy R χ t) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hsq : (energy R χ t : ℝ) ^ (1 / 2 : ℝ) * (R.card : ℝ) ^ (1 / 2 : ℝ) * N ^ 2 =
      N ^ 2 * √((R.card : ℝ) * energy R χ t) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    ring
  rw [hsq, ← hW] at h
  have hB1 : 1 ≤ (2 * (q : ℝ) * T * N) ^ ε := by
    have : 1 ≤ 2 * (q : ℝ) * T * N := by nlinarith
    exact Real.one_le_rpow this hε.le
  have hdyad : ((dyad N).card : ℝ) * (R.card : ℝ) ^ 3 ≤ 3 * (2 * (q : ℝ) * T * N) ^ ε * W := by
    have h1 := card_dyad_le hN0.le
    have h2 : ((dyad N).card : ℝ) * (R.card : ℝ) ^ 3 ≤ 3 * (N * (R.card : ℝ) ^ 3) := by
      have : ((dyad N).card : ℝ) ≤ 3 * N := by linarith
      have h4 : (0 : ℝ) ≤ (R.card : ℝ) ^ 3 := by positivity
      nlinarith
    have h3 : N * (R.card : ℝ) ^ 3 ≤ W := by
      rw [hW]
      have : 0 ≤ N * ((q : ℝ) * T) ^ (1 / 4 : ℝ) * (R.card : ℝ) ^ (21 / 8 : ℝ) +
          N ^ 2 * √((R.card : ℝ) * energy R χ t) := by
        positivity
      linarith
    have h5 : 3 * W ≤ 3 * (2 * (q : ℝ) * T * N) ^ ε * W := by nlinarith
    linarith
  have hmain : 8 * C₁ * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) * ((q : ℝ) * T * N) ^ δ *
      (1 + Real.log (max 1 N)) * W ≤ 8 * C₁ * cG * (1 + 1 / δ) * (2 * (q : ℝ) * T * N) ^ ε * W := by
    have hΛ : 0 ≤ ((q : ℝ) * T * N) ^ δ := by positivity
    calc 8 * C₁ * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) * ((q : ℝ) * T * N) ^ δ *
          (1 + Real.log (max 1 N)) * W
        ≤ 8 * C₁ * (cG * ((q : ℝ) ^ δ * (q : ℝ) ^ δ)) * ((q : ℝ) * T * N) ^ δ *
            ((1 + 1 / δ) * (max 1 N) ^ δ) * W := by
          gcongr
          have : 0 ≤ Real.log (max 1 N) := Real.log_nonneg (le_max_left 1 N)
          linarith
      _ = 8 * C₁ * cG * (1 + 1 / δ) * ((q : ℝ) ^ δ * (q : ℝ) ^ δ * ((q : ℝ) * T * N) ^ δ * (max 1 N) ^ δ) * W := by
          ring
      _ ≤ 8 * C₁ * cG * (1 + 1 / δ) * (2 * (q : ℝ) * T * N) ^ ε * W := by gcongr
  have e : (8 * C₁ * cG * (1 + 1 / δ) + 3) * (2 * (q : ℝ) * T * N) ^ ε * W =
      8 * C₁ * cG * (1 + 1 / δ) * (2 * (q : ℝ) * T * N) ^ ε * W + 3 * (2 * (q : ℝ) * T * N) ^ ε * W := by ring
  rw [← hW, e]
  linarith

/-! ### Their Proposition 10.2 -/

/-- **The quadratic step**: for `E ≥ 0`, `E ≤ A + B√E` gives `E ≤ 2A + B²`, since `2B√E ≤ E + B²`. -/
lemma quad_le {E A B : ℝ} (hE : 0 ≤ E) (h : E ≤ A + B * √E) : E ≤ 2 * A + B ^ 2 := by
  have h1 : (√E) ^ 2 = E := Real.sq_sqrt hE
  have h2 : 0 ≤ (√E - B) ^ 2 := sq_nonneg _
  nlinarith

/-- The cubes over `S × S`, for `S ⊆ {n ∼ N}`, split at the gcd `D`: their Lemmas 10.9 and 10.10 cover the two
parts. -/
lemma sum_S_le {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {N : ℝ} (hN : 0 < N)
    {S : Finset ℕ} (hS : ∀ n ∈ S, N < n ∧ (n : ℝ) ≤ 2 * N) (D : ℕ) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 3 ≤
      ∑ p ∈ pairs N D, ‖R2 R χ t p.1 p.2‖ ^ 3 + ∑ p ∈ pairsGt N D, ‖R2 R χ t p.1 p.2‖ ^ 3 := by
  classical
  rw [← Finset.sum_product' S S fun n₁ n₂ => ‖R2 R χ t n₁ n₂‖ ^ 3]
  have hsub : S ×ˢ S ⊆ dyad N ×ˢ dyad N := by
    intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨(mem_dyad hN.le).mpr (hS _ hp.1), (mem_dyad hN.le).mpr (hS _ hp.2)⟩
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun p : ℕ × ℕ => ‖R2 R χ t p.1 p.2‖ ^ 3)
    fun _ _ _ => by positivity
  have h2 : ∑ p ∈ dyad N ×ˢ dyad N, ‖R2 R χ t p.1 p.2‖ ^ 3 =
      ∑ p ∈ pairs N D, ‖R2 R χ t p.1 p.2‖ ^ 3 + ∑ p ∈ pairsGt N D, ‖R2 R χ t p.1 p.2‖ ^ 3 := by
    rw [← Finset.sum_filter_add_sum_filter_not (dyad N ×ˢ dyad N) (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 ≤ D)]
    have e : (dyad N ×ˢ dyad N).filter (fun p : ℕ × ℕ => ¬Nat.gcd p.1 p.2 ≤ D) = pairsGt N D := by
      unfold pairsGt
      exact Finset.filter_congr fun p _ => not_le
    rw [e]
    rfl
  exact h1.trans (le_of_eq h2)

/-- `N^{4−4σ} = (N²/(N^σ)²)²` and `N^{1−2σ} = N/(N^σ)²` for `N > 0`. -/
lemma rpow_four_sub {N σ : ℝ} (hN : 0 < N) :
    N ^ (4 - 4 * σ) = (N ^ 2 / (N ^ σ) ^ 2) ^ 2 ∧ N ^ (1 - 2 * σ) = N / (N ^ σ) ^ 2 := by
  have h4 : N ^ (4 * σ) = (N ^ σ) ^ 4 := by
    rw [mul_comm, Real.rpow_mul hN.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : N ^ (2 * σ) = (N ^ σ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hN.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hNσ : 0 < N ^ σ := Real.rpow_pos_of_pos hN σ
  constructor
  · rw [Real.rpow_sub hN, h4, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  · rw [Real.rpow_sub hN, h2, Real.rpow_one]

/-- `((2x)^{ε/2})² = 2^εx^ε` for `x ≥ 0`; at `x = qTN`, `Λ² = 2^ε(qTN)^ε` for `Λ = (2qTN)^{ε/2}`. -/
lemma sq_rpow_half {x ε : ℝ} (hx : 0 ≤ x) : ((2 * x) ^ (ε / 2)) ^ 2 = 2 ^ ε * x ^ ε := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx]
  congr 2 <;> push_cast <;> ring

/-- The last step of their Proposition 10.2: from `E ≤ A + B√E` in the stack's variables to their form, for
`E, r, Q4, N, u, c₁, C₃ ≥ 0` and `Λ ≥ 1`. -/
lemma prop102_fin {E r Q4 N u c₁ C₃ Λ : ℝ} (hE : 0 ≤ E) (hr : 0 ≤ r) (hQ4 : 0 ≤ Q4) (hN : 0 ≤ N) (hu : 0 ≤ u)
    (hc₁ : 0 ≤ c₁) (hC₃ : 0 ≤ C₃) (hΛ : 1 ≤ Λ)
    (h : E ≤ c₁ * u * C₃ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ)) + c₁ * u * C₃ * Λ * N ^ 2 * √r * √E) :
    E ≤ (2 * c₁ * C₃ + c₁ ^ 2 * C₃ ^ 2) * Λ ^ 2 *
      (r * (N ^ 2 * u) ^ 2 + r ^ (21 / 8 : ℝ) * Q4 * (N * u) + r ^ 3 * (N * u)) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hq := quad_le hE h
  have hsr : (√r) ^ 2 = r := Real.sq_sqrt hr
  have e3 : (c₁ * u * C₃ * Λ * N ^ 2 * √r) ^ 2 = c₁ ^ 2 * C₃ ^ 2 * Λ ^ 2 * (r * (N ^ 2 * u) ^ 2) := by
    calc (c₁ * u * C₃ * Λ * N ^ 2 * √r) ^ 2 = c₁ ^ 2 * C₃ ^ 2 * Λ ^ 2 * ((√r) ^ 2 * (N ^ 2 * u) ^ 2) := by ring
      _ = _ := by rw [hsr]
  rw [e3] at hq
  have hΛΛ : Λ ≤ Λ ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hΛ0 hΛ
  have hX0 : 0 ≤ c₁ * C₃ * (r ^ 3 * (N * u) + r ^ (21 / 8 : ℝ) * Q4 * (N * u)) := by positivity
  have h5 := mul_le_mul_of_nonneg_right hΛΛ hX0
  have h6 : 0 ≤ c₁ * C₃ * Λ ^ 2 * (r * (N ^ 2 * u) ^ 2) := by positivity
  have h7 : 0 ≤ c₁ ^ 2 * C₃ ^ 2 * Λ ^ 2 * (r ^ (21 / 8 : ℝ) * Q4 * (N * u) + r ^ 3 * (N * u)) := by positivity
  have e4 : (2 * c₁ * C₃ + c₁ ^ 2 * C₃ ^ 2) * Λ ^ 2 *
      (r * (N ^ 2 * u) ^ 2 + r ^ (21 / 8 : ℝ) * Q4 * (N * u) + r ^ 3 * (N * u)) =
        2 * (Λ ^ 2 * (c₁ * C₃ * (r ^ 3 * (N * u) + r ^ (21 / 8 : ℝ) * Q4 * (N * u)))) +
          2 * (c₁ * C₃ * Λ ^ 2 * (r * (N ^ 2 * u) ^ 2)) + c₁ ^ 2 * C₃ ^ 2 * Λ ^ 2 * (r * (N ^ 2 * u) ^ 2) +
          c₁ ^ 2 * C₃ ^ 2 * Λ ^ 2 * (r ^ (21 / 8 : ℝ) * Q4 * (N * u) + r ^ 3 * (N * u)) := by ring
  have e5 : c₁ * u * C₃ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ)) =
      Λ * (c₁ * C₃ * (r ^ 3 * (N * u) + r ^ (21 / 8 : ℝ) * Q4 * (N * u))) := by ring
  rw [e4]
  rw [e5] at hq
  linarith

/-- The cubes over `S × S` by the bounds of their Lemmas 10.9 and 10.10 at `ε/2`, in the stack's variables: from
`s ≤ s₁ + s₂` and the two bounds, for `M ≤ Λ` (in the use, `M = max(1, N)^{ε/2}`), `C₁, N, r, Q4, Λ ≥ 0` and
`C₃ = C₁ + C₂`. -/
lemma prop102_sum {s s₁ s₂ C₁ C₂ C₃ M Λ N r E Q4 : ℝ} (hsplit : s ≤ s₁ + s₂)
    (hs1 : s₁ ≤ C₁ * M * (N ^ 2 * (√r * √E) + N * r ^ 3))
    (hs2 : s₂ ≤ C₂ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ) + N ^ 2 * (√r * √E)))
    (hC₁ : 0 ≤ C₁) (hMΛ : M ≤ Λ) (hN : 0 ≤ N) (hr : 0 ≤ r) (hQ4 : 0 ≤ Q4) (hΛ : 0 ≤ Λ) (hC₃ : C₃ = C₁ + C₂) :
    s ≤ C₃ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ)) + C₃ * Λ * N ^ 2 * √r * √E := by
  have h1 : C₁ * M * (N ^ 2 * (√r * √E) + N * r ^ 3) ≤ C₁ * Λ * (N ^ 2 * (√r * √E) + N * r ^ 3) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMΛ hC₁) (by positivity)
  have h2 : 0 ≤ C₁ * Λ * (N * Q4 * r ^ (21 / 8 : ℝ)) := by positivity
  have e : C₃ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ)) + C₃ * Λ * N ^ 2 * √r * √E =
      C₁ * Λ * (N ^ 2 * (√r * √E) + N * r ^ 3) + C₁ * Λ * (N * Q4 * r ^ (21 / 8 : ℝ)) +
        C₂ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ) + N ^ 2 * (√r * √E)) := by
    rw [hC₃]; ring
  rw [e]
  linarith

/-- **Their Proposition 10.2, at one point per character**: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such
that, for `q ≥ 1`, primitive characters injective on `R`, `T ≥ 1`, points `|t_i| ≤ T`, `(qT)^{2/3}/2 ≤ N`,
`S ⊆ (N, 2N]`, `|b_n| ≤ 1`, `|Σ_{n∈S}b_nχ_i(n)n^{it_i}| ≥ N^σ/6` for `i ∈ R`, and either `|R| ≥ (qT)^{2/3}` or
`(qT)^{1/2}|R|^{5/8} ≤ E^{1/8}N`, `E ≤ C(qTN)^ε(|R|N^{4−4σ} + |R|^{21/8}(qT)^{1/4}N^{1−2σ} + |R|³N^{1−2σ})`.
Round 669's `lemma105` bounds `E` by the cubes over `S × S`; `sum_S_le` splits them at `D = ⌊N²/(qT)⌋` into
`lemma109_eps` and `lemma1010_eps` at `ε/2`; and `E ≤ A + B√E` gives `E ≤ 2A + B²` (`quad_le`). -/
theorem prop102 (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T N σ : ℝ) (S : Finset ℕ) (b : ℕ → ℂ),
      Set.InjOn χ R → (∀ i ∈ R, (χ i).IsPrimitive) → 1 ≤ T → (∀ i ∈ R, |t i| ≤ T) →
      ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N → (∀ n ∈ S, N < n ∧ (n : ℝ) ≤ 2 * N) → (∀ n, ‖b n‖ ≤ 1) →
      (∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) →
      (((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ R.card ∨
        ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (R.card : ℝ) ^ (5 / 8 : ℝ) ≤ (energy R χ t : ℝ) ^ (1 / 8 : ℝ) * N) →
      (energy R χ t : ℝ) ≤ C * ((q : ℝ) * T * N) ^ ε *
        ((R.card : ℝ) * N ^ (4 - 4 * σ) + (R.card : ℝ) ^ (21 / 8 : ℝ) * ((q : ℝ) * T) ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) +
          (R.card : ℝ) ^ 3 * N ^ (1 - 2 * σ)) := by
  obtain ⟨C₁, hC₁0, h109⟩ := lemma109_eps (half_pos hε)
  obtain ⟨C₂, hC₂0, h1010⟩ := lemma1010_eps hT (half_pos hε)
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 36 * ∫ ξ, kmaj ξ := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; exact mul_nonneg (by norm_num) (integral_nonneg kmaj_nonneg)
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = C₁ + C₂ := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  refine ⟨(2 * c₁ * C₃ + c₁ ^ 2 * C₃ ^ 2) * 2 ^ ε, by positivity, ?_⟩
  intro q _ ι R χ t T N σ S b hinj hprim hT1 ht hN hS hb hbig halt
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT1
  have hN2 : 1 / 2 ≤ N := by
    have : 1 ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  -- the energy by the cubes
  have h105 := lemma105 hinj t hN0 (fun n hn => ⟨(hS n hn).1.le, (hS n hn).2⟩) hb hbig
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = ⌊N ^ 2 / ((q : ℝ) * T)⌋₊ := ⟨_, rfl⟩
  have hDqT : (D : ℝ) * ((q : ℝ) * T) ≤ N ^ 2 := by
    have : (D : ℝ) ≤ N ^ 2 / ((q : ℝ) * T) := by rw [hD]; exact Nat.floor_le (by positivity)
    rwa [le_div_iff₀ (by positivity)] at this
  have hsplit := sum_S_le R χ t hN0 hS D
  have hs1 := h109 q R χ t T N D hinj hT1 ht hN2 hDqT
  have hs2 := h1010 q R χ t T N hT1 hprim hinj ht hN halt
  rw [← hD] at hs2
  -- `max(1, N)^{ε/2} ≤ (2qTN)^{ε/2}`
  have hqTN : N ≤ (q : ℝ) * T * N := by
    have := mul_le_mul_of_nonneg_right hQ1 hN0.le
    linarith
  have hB1 : 1 ≤ 2 * (q : ℝ) * T * N := by linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (2 * (q : ℝ) * T * N) ^ (ε / 2) := ⟨_, rfl⟩
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact Real.one_le_rpow hB1 (by positivity)
  have hMΛ : (max 1 N) ^ (ε / 2) ≤ Λ := by
    rw [hΛ]
    exact Real.rpow_le_rpow (by positivity) (max_le hB1 (by linarith)) (by positivity)
  rw [← hΛ] at hs2
  -- the stack's variables
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (energy R χ t : ℝ) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (R.card : ℝ) := ⟨_, rfl⟩
  rw [← hE, ← hr] at hs1 hs2
  rw [← hE] at h105
  rw [← hE, ← hr]
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  obtain ⟨Q4, hQ4⟩ : ∃ Q4 : ℝ, Q4 = ((q : ℝ) * T) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hQ4] at hs2
  rw [← hQ4]
  have hQ40 : 0 ≤ Q4 := by rw [hQ4]; positivity
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / (N ^ σ) ^ 2 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hsq : √(r * E) = √r * √E := Real.sqrt_mul hr0 E
  rw [hsq] at hs1 hs2
  -- the cubes, then `E ≤ A + B√E`
  have hsum := prop102_sum hsplit hs1 hs2 hC₁0 hMΛ hN0.le hr0 hQ40 (by linarith) hC₃
  have e1 : 36 / (N ^ σ) ^ 2 * (∫ ξ, kmaj ξ) = c₁ * u := by rw [hc₁, hu]; ring
  rw [e1] at h105
  have h2 := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ c₁ * u)
  have hEAB : E ≤ c₁ * u * C₃ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ)) +
      c₁ * u * C₃ * Λ * N ^ 2 * √r * √E := by
    have e2 : c₁ * u * (C₃ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ)) + C₃ * Λ * N ^ 2 * √r * √E) =
        c₁ * u * C₃ * Λ * (N * r ^ 3 + N * Q4 * r ^ (21 / 8 : ℝ)) + c₁ * u * C₃ * Λ * N ^ 2 * √r * √E := by ring
    linarith
  have hfin := prop102_fin hE0 hr0 hQ40 hN0.le hu0 hc₁0 hC₃0 hΛ1 hEAB
  -- back to their form
  obtain ⟨h44, h12⟩ := rpow_four_sub (σ := σ) hN0
  have hΛ2 : Λ ^ 2 = 2 ^ ε * ((q : ℝ) * T * N) ^ ε := by
    rw [hΛ, show 2 * (q : ℝ) * T * N = 2 * ((q : ℝ) * T * N) by ring]
    exact sq_rpow_half (by positivity)
  refine hfin.trans (le_of_eq ?_)
  rw [h44, h12, hΛ2, hu]
  ring

end LinnikCGLEps

#print axioms LinnikCGLEps.card_le_totient
#print axioms LinnikCGLEps.lemma109_eps
#print axioms LinnikCGLEps.lemma1010_eps
#print axioms LinnikCGLEps.prop102
