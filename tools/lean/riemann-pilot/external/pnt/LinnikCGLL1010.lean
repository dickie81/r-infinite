/-
# Round 675: their Lemma 10.10, the large-gcd terms, before their case analysis (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Lemma 10.10 (Large GCD terms): "Let D = N²/(qT) and N ≥ (qT)^{2/3}/2. Assume that either |W| ≥ (qT)^{2/3} or that
E(W)^{1/8}N ≥ (qT)^{1/2}|W|^{5/8}. Then we have Σ_{n₁,n₂∼N, (n₁n₂,q)=1, (n₁,n₂)≥D} |R(n₁/n₂, n₁n₂^{−1})|³ ⪅ N|W|³ +
N(qT)^{1/4}|W|^{21/8} + E(W)^{1/2}|W|^{1/2}N²." (text layer lines 5315–5336; spaces restored; the sum, fraction, large
bars, which the text layer encodes as four form feeds each, large parentheses, subscripts and exponents transcribed).
Their proof writes `n₁ = n′₁d`, `n₂ = n′₂d`; "By the Cauchy-Schwarz inequality, we have" (lines 5339–5340) the cubes
over `n′₁, n′₂ ∼ N/d` bounded by the fourth and second moments; "Applying Lemmas 10.6 and 10.7 yields" (line 5387) a
bound for each `d`; and "By summing over d ≥ D and using Cauchy-Schwarz, we arrive at" (line 5415; spaces restored)
the product `(|W|N²/D + |W|²N + |W|^{5/4}(qT)^{1/2}N)^{1/2}(E(W)N²/D + |W|⁴N + E(W)^{3/4}|W|(qT)^{1/2}N)^{1/2}` up to
`⪅` (lines 5416–5435, transcribed). Their case analysis, (10.4) and (10.5) (lines 5436–5499), follows; this file stops
before it.

The stack's form.
* `lemma106'`: round 670's `lemma106` assumes `Q₀ ≤ qT`. At `T′ = max(1, Q₀)T`, which makes `qT′ ≥ Q₀`, its bound
  holds for every `q ≥ 1` and `T ≥ 1`, with the constant `max(C, 0)max(1, Q₀)^ε max(1, Q₀)^{1/2}`, as round 672
  did for `lemma107`.
* Their `n′ = n/d`: for `d, m₁, m₂ > 0`, `|R₂(dm₁, dm₂)| ≤ |R₂(m₁, m₂)|` (`norm_R2_mul_le`), with equality when `d` is
  a unit modulo `q`, and `R₂(dm₁, dm₂) = 0` otherwise. So the pairs `n₁, n₂ ∼ N` with gcd `d > 0` contribute at most
  `Σ_{m₁,m₂∼N/d}|R₂(m₁, m₂)|^k` (`sum_gcd_eq_le`), their inner sum.
* For `d ≤ N`, Cauchy–Schwarz (`sum_cube_le_sqrt`) and `lemma106'` and round 672's `lemma107` at `M = N/d ≥ 1`, with
  `(qTN/d)^ε ≤ (qTN)^ε`, bound the pairs with gcd `d`. The sum over `d` uses Cauchy–Schwarz (Mathlib's
  `Real.sum_sqrt_mul_sqrt_le`), `Σ_{D<d≤N}d^{−2} ≤ 2/(D + 1)` (Mathlib's `sum_Ioo_inv_sq_le`, `sum_inv_sq_le`) and
  `Σ_{D<d≤N}d^{−1} ≤ 1 + log max(1, N)` (Mathlib's `harmonic_le_one_add_log`, `sum_inv_le`); their `⪅` absorbs the
  logarithm and the divisor factor `d(q)(⌊log₂|R|²⌋ + 1)` of `lemma107`.
* For `d > N` their Lemmas 10.6 and 10.7, each stated "For any M ≥ 1, we have" (lines 4767 and 4814; spaces
  restored), do not apply, since `N/d < 1`. A pair `n₁, n₂ ∼ N` with gcd `d > N` is `(d, d)` (`eq_of_dvd_of_lt`), and
  `|R₂| ≤ |R|` (`norm_R2_le`), so these pairs contribute at most `|{n ∼ N}||R|³`, a term of the size of their `N|W|³`.
* The stack sums over `(n₁, n₂) > D`, so that with round 674's `(n₁, n₂) ≤ D` the two cover every pair; their `N²/D`
  becomes `2N²/(D + 1)`. Their hypotheses on `D`, `N`, `|W|` and `E(W)` enter only their case analysis, which is
  not formalized here.

Plain statements, with `q ≥ 1`, `n ∼ N` round 670's `dyad`, `R₂` round 669's, `E` round 659's `energy`,
`G = d(q)(⌊log₂|R|²⌋ + 1)` and `L = 1 + log max(1, N)`.
* `lemma106'`: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for primitive characters injective on
  `R`, `T, M ≥ 1` and points `|t_i| ≤ T`, `Σ_{n₁,n₂∼M}|R₂(n₁, n₂)|² ≤ C(qTM)^ε(|R|M² + |R|²M + |R|^{5/4}(qT)^{1/2}M)`.
* `norm_R2_le`, `norm_R2_mul_le`: `|R₂(n₁, n₂)| ≤ |R|`; and `|R₂(dm₁, dm₂)| ≤ |R₂(m₁, m₂)|` for `d, m₁, m₂ > 0`.
* `sum_gcd_eq_le`: for `N > 0`, `d > 0` and `k ∈ ℕ`, `Σ_{n₁,n₂∼N, (n₁,n₂)=d}|R₂(n₁, n₂)|^k ≤
  Σ_{m₁,m₂∼N/d}|R₂(m₁, m₂)|^k`.
* `sum_cube_le_sqrt`: for `f ≥ 0` on a finite set, `Σf³ ≤ √(Σf⁴)√(Σf²)`.
* `sum_inv_le`, `sum_inv_sq_le`: `Σ_{D<d≤N}d^{−1} ≤ 1 + log max(1, N)` and `Σ_{D<d≤N}d^{−2} ≤ 2/(D + 1)`.
* `pairsGt`, `eq_of_dvd_of_lt`: the pairs `n₁, n₂ ∼ N` with `(n₁, n₂) > D`; and for `N > 0`, `n ∼ N` and a divisor
  `g > N` of `n`, `n = g`.
* `lemma1010`: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for primitive characters injective on
  `R`, `T ≥ 1`, points `|t_i| ≤ T`, `N > 0` and `D ∈ ℕ`, `Σ_{n₁,n₂∼N, (n₁,n₂)>D}|R₂(n₁, n₂)|³ ≤ CG(qTN)^ε√(ab) +
  |{n ∼ N}||R|³` with `a = |R|N²·2/(D + 1) + (|R|² + |R|^{5/4}(qT)^{1/2})NL` and
  `b = E·N²·2/(D + 1) + (|R|⁴ + E^{3/4}|R|(qT)^{1/2})NL`.

The file imports `LinnikCGLL109.lean`.
-/

import LinnikCGLL109

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLL1010

open LinnikCGLL105 LinnikCGLMom4 LinnikCGLT101 LinnikCGLL107 LinnikCGLL109

/-! ### Their Lemma 10.6 without a threshold -/

/-- **Their Lemma 10.6 without a lower bound on `qT`**: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that,
for `q ≥ 1`, primitive characters injective on `R`, `T, M ≥ 1` and points `|t_i| ≤ T`,
`Σ_{n₁,n₂∼M}|R₂(n₁, n₂)|² ≤ C(qTM)^ε(|R|M² + |R|²M + |R|^{5/4}(qT)^{1/2}M)`. Round 670's `lemma106` at
`T′ = max(1, Q₀)T`, which makes `qT′ ≥ Q₀`. -/
theorem lemma106' (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T M : ℝ), 1 ≤ T → 1 ≤ M → (∀ i ∈ R, (χ i).IsPrimitive) → Set.InjOn χ R →
      (∀ i ∈ R, |t i| ≤ T) →
      ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖R2 R χ t n₁ n₂‖ ^ 2 ≤
        C * ((q : ℝ) * T * M) ^ ε * ((R.card : ℝ) * M ^ 2 + (R.card : ℝ) ^ 2 * M +
          (R.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) := by
  obtain ⟨C, Q₀, hCQ⟩ := lemma106 hT hε
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : ℝ, Q₁ = max 1 Q₀ := ⟨_, rfl⟩
  have hQ₁1 : 1 ≤ Q₁ := hQ₁ ▸ le_max_left _ _
  have hQ₀ : Q₀ ≤ Q₁ := hQ₁ ▸ le_max_right _ _
  refine ⟨max C 0 * Q₁ ^ ε * Q₁ ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro q _ ι R χ t T M hT1 hM hprim hinj ht
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT1
  have hQT : Q₀ ≤ (q : ℝ) * (Q₁ * T) := by
    have := mul_le_mul_of_nonneg_left hqT1 (by linarith : (0 : ℝ) ≤ Q₁)
    calc Q₀ ≤ Q₁ := hQ₀
      _ = Q₁ * 1 := (mul_one _).symm
      _ ≤ Q₁ * ((q : ℝ) * T) := this
      _ = (q : ℝ) * (Q₁ * T) := by ring
  have hT' : 1 ≤ Q₁ * T := one_le_mul_of_one_le_of_one_le hQ₁1 hT1
  have ht' : ∀ i ∈ R, |t i| ≤ Q₁ * T := fun i hi =>
    (ht i hi).trans (le_mul_of_one_le_left (by linarith) hQ₁1)
  have h := hCQ q R χ t (Q₁ * T) M hQT hT' hM hprim hinj ht'
  have hqT : 0 ≤ (q : ℝ) * T := by positivity
  have e1 : ((q : ℝ) * (Q₁ * T) * M) ^ ε = Q₁ ^ ε * ((q : ℝ) * T * M) ^ ε := by
    rw [show (q : ℝ) * (Q₁ * T) * M = Q₁ * ((q : ℝ) * T * M) by ring, Real.mul_rpow (by linarith) (by positivity)]
  have e2 : ((q : ℝ) * (Q₁ * T)) ^ (1 / 2 : ℝ) = Q₁ ^ (1 / 2 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) := by
    rw [show (q : ℝ) * (Q₁ * T) = Q₁ * ((q : ℝ) * T) by ring, Real.mul_rpow (by linarith) hqT]
  rw [e1, e2] at h
  have hA : 0 ≤ (R.card : ℝ) * M ^ 2 + (R.card : ℝ) ^ 2 * M := by positivity
  have hs1 : 1 ≤ Q₁ ^ (1 / 2 : ℝ) := Real.one_le_rpow hQ₁1 (by norm_num)
  calc ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖R2 R χ t n₁ n₂‖ ^ 2
      ≤ C * (Q₁ ^ ε * ((q : ℝ) * T * M) ^ ε) * ((R.card : ℝ) * M ^ 2 + (R.card : ℝ) ^ 2 * M +
          (R.card : ℝ) ^ (5 / 4 : ℝ) * (Q₁ ^ (1 / 2 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ)) * M) := h
    _ ≤ max C 0 * (Q₁ ^ ε * ((q : ℝ) * T * M) ^ ε) * (Q₁ ^ (1 / 2 : ℝ) * ((R.card : ℝ) * M ^ 2 +
          (R.card : ℝ) ^ 2 * M + (R.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) ?_ (by positivity)
          (by positivity)
        have hB : 0 ≤ (R.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hs1 hA]
    _ = max C 0 * Q₁ ^ ε * Q₁ ^ (1 / 2 : ℝ) * ((q : ℝ) * T * M) ^ ε * ((R.card : ℝ) * M ^ 2 +
          (R.card : ℝ) ^ 2 * M + (R.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) := by ring

/-! ### `R₂` at multiples, and the pairs with one gcd -/

section mult

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- `|R₂(n₁, n₂)| ≤ |R|`. -/
lemma norm_R2_le (n₁ n₂ : ℕ) : ‖R2 R χ t n₁ n₂‖ ≤ R.card := by
  unfold R2
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ R, ‖χ i n₁ * conj (χ i n₂) * cexp (↑(t i * (Real.log n₁ - Real.log n₂)) * I)‖
      ≤ ∑ _i ∈ R, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_conj]
        calc ‖χ i n₁‖ * ‖χ i n₂‖ ≤ 1 * 1 :=
              mul_le_mul (DirichletCharacter.norm_le_one _ _) (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1
    _ = R.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- For `d, m₁, m₂ > 0`, `|R₂(dm₁, dm₂)| ≤ |R₂(m₁, m₂)|`: the two are equal for `d` a unit modulo `q`, and the first
is `0` otherwise. -/
lemma norm_R2_mul_le {d m₁ m₂ : ℕ} (hd : 0 < d) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    ‖R2 R χ t (d * m₁) (d * m₂)‖ ≤ ‖R2 R χ t m₁ m₂‖ := by
  by_cases hu : IsUnit (d : ZMod q)
  · refine le_of_eq (congrArg norm ?_)
    unfold R2
    refine Finset.sum_congr rfl fun i _ => ?_
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have h1' : (0 : ℝ) < m₁ := by exact_mod_cast h₁
    have h2' : (0 : ℝ) < m₂ := by exact_mod_cast h₂
    have hl : Real.log ((d * m₁ : ℕ) : ℝ) - Real.log ((d * m₂ : ℕ) : ℝ) = Real.log m₁ - Real.log m₂ := by
      push_cast
      rw [Real.log_mul hd'.ne' h1'.ne', Real.log_mul hd'.ne' h2'.ne']
      ring
    have hn : ‖χ i (d : ZMod q)‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one (χ i) hu.unit
      rwa [IsUnit.unit_spec] at this
    have hdd : χ i (d : ZMod q) * conj (χ i (d : ZMod q)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num
    have hχ : χ i ((d * m₁ : ℕ) : ZMod q) * conj (χ i ((d * m₂ : ℕ) : ZMod q)) =
        χ i (m₁ : ZMod q) * conj (χ i (m₂ : ZMod q)) := by
      push_cast
      rw [map_mul, map_mul, map_mul]
      calc χ i (d : ZMod q) * χ i (m₁ : ZMod q) * (conj (χ i (d : ZMod q)) * conj (χ i (m₂ : ZMod q)))
          = (χ i (d : ZMod q) * conj (χ i (d : ZMod q))) * (χ i (m₁ : ZMod q) * conj (χ i (m₂ : ZMod q))) := by
            ring
        _ = χ i (m₁ : ZMod q) * conj (χ i (m₂ : ZMod q)) := by rw [hdd, one_mul]
    rw [hχ, hl]
  · have h0 : R2 R χ t (d * m₁) (d * m₂) = 0 := by
      refine R2_eq_zero R χ t fun h => hu ?_
      have h1 : IsUnit ((d : ZMod q) * (m₁ : ZMod q)) := by
        have := h.1
        push_cast at this
        exact this
      exact isUnit_of_mul_isUnit_left h1
    rw [h0, norm_zero]
    exact norm_nonneg _

/-- **The pairs with one gcd**: for `N > 0`, `d > 0` and `k ∈ ℕ`,
`Σ_{n₁,n₂∼N, (n₁,n₂)=d}|R₂(n₁, n₂)|^k ≤ Σ_{m₁,m₂∼N/d}|R₂(m₁, m₂)|^k`, through `(n₁, n₂) ↦ (n₁/d, n₂/d)`. -/
lemma sum_gcd_eq_le {N : ℝ} (hN : 0 < N) {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ∑ p ∈ (dyad N ×ˢ dyad N).filter (fun p => Nat.gcd p.1 p.2 = d), ‖R2 R χ t p.1 p.2‖ ^ k ≤
      ∑ p ∈ dyad (N / d) ×ˢ dyad (N / d), ‖R2 R χ t p.1 p.2‖ ^ k := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Finset (ℕ × ℕ), F = (dyad N ×ˢ dyad N).filter (fun p => Nat.gcd p.1 p.2 = d) :=
    ⟨_, rfl⟩
  rw [← hF]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmem : ∀ p ∈ F, p.1 ∈ dyad N ∧ p.2 ∈ dyad N ∧ d ∣ p.1 ∧ d ∣ p.2 := by
    intro p hp
    rw [hF, Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2 ▸ Nat.gcd_dvd_left _ _, hp.2 ▸ Nat.gcd_dvd_right _ _⟩
  have hdiv : ∀ n ∈ dyad N, d ∣ n → n / d ∈ dyad (N / d) := by
    intro n hn hdn
    rw [mem_dyad hN.le] at hn
    rw [mem_dyad (by positivity)]
    have e : ((n / d : ℕ) : ℝ) = (n : ℝ) / d := Nat.cast_div hdn hd'.ne'
    rw [e]
    constructor
    · exact div_lt_div_of_pos_right hn.1 hd'
    · rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hn.2 hd'.le
  have hpos : ∀ n ∈ dyad N, d ∣ n → 0 < n / d := by
    intro n hn hdn
    have h1 := hdiv n hn hdn
    rw [mem_dyad (by positivity)] at h1
    have : (0 : ℝ) < (n / d : ℕ) := (div_pos hN hd').trans h1.1
    exact_mod_cast this
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 / d, p.2 / d)) F := by
    intro p hp p' hp' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, -, h1, h2⟩ := hmem p hp
    obtain ⟨-, -, h1', h2'⟩ := hmem p' hp'
    refine Prod.ext ?_ ?_
    · rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h1', h.1]
    · rw [← Nat.mul_div_cancel' h2, ← Nat.mul_div_cancel' h2', h.2]
  have hsub : F.image (fun p : ℕ × ℕ => (p.1 / d, p.2 / d)) ⊆ dyad (N / d) ×ˢ dyad (N / d) := by
    intro p' hp'
    rw [Finset.mem_image] at hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    obtain ⟨h₁, h₂, h1, h2⟩ := hmem p hp
    exact Finset.mem_product.mpr ⟨hdiv _ h₁ h1, hdiv _ h₂ h2⟩
  calc ∑ p ∈ F, ‖R2 R χ t p.1 p.2‖ ^ k ≤ ∑ p ∈ F, ‖R2 R χ t (p.1 / d) (p.2 / d)‖ ^ k := by
        refine Finset.sum_le_sum fun p hp => pow_le_pow_left₀ (norm_nonneg _) ?_ k
        obtain ⟨h₁, h₂, h1, h2⟩ := hmem p hp
        have e1 : p.1 = d * (p.1 / d) := (Nat.mul_div_cancel' h1).symm
        have e2 : p.2 = d * (p.2 / d) := (Nat.mul_div_cancel' h2).symm
        obtain ⟨a, ha⟩ : ∃ a, a = p.1 / d := ⟨_, rfl⟩
        obtain ⟨b, hb⟩ : ∃ b, b = p.2 / d := ⟨_, rfl⟩
        rw [← ha] at e1 ⊢
        rw [← hb] at e2 ⊢
        have ha0 : 0 < a := ha ▸ hpos _ h₁ h1
        have hb0 : 0 < b := hb ▸ hpos _ h₂ h2
        rw [e1, e2]
        exact norm_R2_mul_le R χ t hd ha0 hb0
    _ = ∑ p' ∈ F.image (fun p : ℕ × ℕ => (p.1 / d, p.2 / d)), ‖R2 R χ t p'.1 p'.2‖ ^ k :=
        (Finset.sum_image (f := fun p' : ℕ × ℕ => ‖R2 R χ t p'.1 p'.2‖ ^ k) hinj).symm
    _ ≤ ∑ p ∈ dyad (N / d) ×ˢ dyad (N / d), ‖R2 R χ t p.1 p.2‖ ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

end mult

/-! ### Two sums -/

/-- `Σ|f|³ ≤ √(Σ|f|⁴)√(Σ|f|²)` over a finite set, by Cauchy–Schwarz. -/
lemma sum_cube_le_sqrt {κ : Type*} (s : Finset κ) (f : κ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 3 ≤ √(∑ i ∈ s, f i ^ 4) * √(∑ i ∈ s, f i ^ 2) := by
  have h := Real.sum_sqrt_mul_sqrt_le s (f := fun i => f i ^ 4) (g := fun i => f i ^ 2) (fun i => by positivity)
    (fun i => by positivity)
  calc ∑ i ∈ s, f i ^ 3 = ∑ i ∈ s, √(f i ^ 4) * √(f i ^ 2) := Finset.sum_congr rfl fun i _ => by
        rw [show f i ^ 4 = (f i ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.sqrt_sq (hf i)]
        ring
    _ ≤ √(∑ i ∈ s, f i ^ 4) * √(∑ i ∈ s, f i ^ 2) := h

/-- `Σ_{D<d≤N}d⁻¹ ≤ 1 + log max(1, N)`, from Mathlib's `harmonic_le_one_add_log`. -/
lemma sum_inv_le (N : ℝ) (D : ℕ) : ∑ d ∈ Finset.Ioc D ⌊N⌋₊, ((d : ℝ))⁻¹ ≤ 1 + Real.log (max 1 N) := by
  have h1 : ∑ d ∈ Finset.Ioc D ⌊N⌋₊, ((d : ℝ))⁻¹ ≤ ∑ d ∈ Finset.Icc 1 ⌊N⌋₊, ((d : ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ => by positivity
    intro d hd
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hd ⊢
    omega
  have h2 : ∑ d ∈ Finset.Icc 1 ⌊N⌋₊, ((d : ℝ))⁻¹ = ((harmonic ⌊N⌋₊ : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  have h3 := harmonic_le_one_add_log ⌊N⌋₊
  have h4 : Real.log (⌊N⌋₊ : ℝ) ≤ Real.log (max 1 N) := by
    rcases Nat.eq_zero_or_pos ⌊N⌋₊ with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (le_max_left _ _)
    · have hN1 : 1 ≤ N := Nat.floor_pos.mp h
      exact Real.log_le_log (by exact_mod_cast h) ((Nat.floor_le (by linarith)).trans (le_max_right _ _))
  linarith

/-- `Σ_{D<d≤N}d^{−2} ≤ 2/(D + 1)`, from Mathlib's `sum_Ioo_inv_sq_le`. -/
lemma sum_inv_sq_le (N : ℝ) (D : ℕ) : ∑ d ∈ Finset.Ioc D ⌊N⌋₊, ((d : ℝ) ^ 2)⁻¹ ≤ 2 / (D + 1) := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) D (⌊N⌋₊ + 1)
  have e : Finset.Ioc D ⌊N⌋₊ = Finset.Ioo D (⌊N⌋₊ + 1) := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Ioo]
    omega
  rw [e]
  exact h

/-! ### Their Lemma 10.10 -/

/-- The pairs `n₁, n₂ ∼ N` with `(n₁, n₂) > D`. -/
def pairsGt (N : ℝ) (D : ℕ) : Finset (ℕ × ℕ) := (dyad N ×ˢ dyad N).filter fun p => D < Nat.gcd p.1 p.2

/-- For `N > 0`, `n ∼ N` and a divisor `g > N` of `n`, `n = g`. -/
lemma eq_of_dvd_of_lt {N : ℝ} (hN : 0 < N) {n g : ℕ} (hn : n ∈ dyad N) (hg : g ∣ n) (hgN : N < g) : n = g := by
  obtain ⟨a, ha⟩ := hg
  rw [mem_dyad hN.le] at hn
  have hn0 : (0 : ℝ) < n := hN.trans hn.1
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, mul_zero] at ha
      rw [ha, Nat.cast_zero] at hn0
      exact absurd hn0 (lt_irrefl 0)
    · exact h
  by_contra hne
  have ha2 : 2 ≤ a := by
    rcases Nat.lt_or_ge a 2 with h | h
    · exact absurd (by rw [ha, show a = 1 by omega, mul_one]) hne
    · exact h
  have h2 : (2 : ℝ) * g ≤ n := by
    rw [ha]
    push_cast
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha2
    nlinarith [(by positivity : (0 : ℝ) ≤ g)]
  linarith [hn.2]

/-- **Their Lemma 10.10 (large gcd terms), at one point per character, before their case analysis**: from
`CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for `q ≥ 1`, primitive characters injective on `R`, `T ≥ 1`,
points `|t_i| ≤ T`, `N > 0` and `D ∈ ℕ`, `Σ_{n₁,n₂∼N, (n₁,n₂)>D}|R₂(n₁, n₂)|³ ≤ CG(qTN)^ε√(ab) + |{n ∼ N}||R|³`, with
`G = d(q)(⌊log₂|R|²⌋ + 1)`, `L = 1 + log max(1, N)`, `a = |R|N²·2/(D + 1) + (|R|² + |R|^{5/4}(qT)^{1/2})NL` and
`b = E·N²·2/(D + 1) + (|R|⁴ + E^{3/4}|R|(qT)^{1/2})NL`. -/
theorem lemma1010 (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T N : ℝ) (D : ℕ), 1 ≤ T → 0 < N → (∀ i ∈ R, (χ i).IsPrimitive) → Set.InjOn χ R →
      (∀ i ∈ R, |t i| ≤ T) →
      ∑ p ∈ pairsGt N D, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤
        C * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) * ((q : ℝ) * T * N) ^ ε *
          √(((R.card : ℝ) * N ^ 2 * (2 / (D + 1)) +
              ((R.card : ℝ) ^ 2 + (R.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ)) * N *
                (1 + Real.log (max 1 N))) *
            ((energy R χ t : ℝ) * N ^ 2 * (2 / (D + 1)) +
              ((R.card : ℝ) ^ 4 + (energy R χ t : ℝ) ^ (3 / 4 : ℝ) * R.card * ((q : ℝ) * T) ^ (1 / 2 : ℝ)) * N *
                (1 + Real.log (max 1 N)))) +
        (dyad N).card * (R.card : ℝ) ^ 3 := by
  obtain ⟨C₆, hC₆0, h6⟩ := lemma106' hT hε
  obtain ⟨C₇, hC₇0, h7⟩ := lemma107 hT hε
  refine ⟨√(C₆ * C₇), Real.sqrt_nonneg _, ?_⟩
  intro q _ ι R χ t T N D hT1 hN hprim hinj ht
  classical
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + Real.log (max 1 N) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = ((q : ℝ) * T * N) ^ ε := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (energy R χ t : ℝ) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (R.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ((q : ℝ) * T) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hG, ← hL, ← hΛ, ← hE, ← hr, ← hs]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = r * N ^ 2 * (2 / (D + 1)) + (r ^ 2 + r ^ (5 / 4 : ℝ) * s) * N * L := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = E * N ^ 2 * (2 / (D + 1)) + (r ^ 4 + E ^ (3 / 4 : ℝ) * r * s) * N * L :=
    ⟨_, rfl⟩
  rw [← ha, ← hb]
  -- signs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hL1 : 1 ≤ L := by rw [hL]; have := Real.log_nonneg (le_max_left 1 N); linarith
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  -- the diagonal: `(n₁, n₂) > N`
  obtain ⟨S₂, hS₂⟩ : ∃ S₂ : Finset (ℕ × ℕ), S₂ = (pairsGt N D).filter fun p => ¬Nat.gcd p.1 p.2 ≤ ⌊N⌋₊ :=
    ⟨_, rfl⟩
  have hdiag : ∑ p ∈ S₂, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤ (dyad N).card * r ^ 3 := by
    have hS₂mem : ∀ p ∈ S₂, p.1 ∈ dyad N ∧ p.1 = p.2 := by
      intro p hp
      rw [hS₂, Finset.mem_filter, pairsGt, Finset.mem_filter, Finset.mem_product] at hp
      have hgN : N < (Nat.gcd p.1 p.2 : ℝ) := by
        have h1 : ⌊N⌋₊ + 1 ≤ Nat.gcd p.1 p.2 := by omega
        have h2 : N < (⌊N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one N
        have h3 : ((⌊N⌋₊ + 1 : ℕ) : ℝ) ≤ (Nat.gcd p.1 p.2 : ℝ) := by exact_mod_cast h1
        push_cast at h3
        linarith
      have e1 := eq_of_dvd_of_lt hN hp.1.1.1 (Nat.gcd_dvd_left _ _) hgN
      have e2 := eq_of_dvd_of_lt hN hp.1.1.2 (Nat.gcd_dvd_right _ _) hgN
      exact ⟨hp.1.1.1, e1.trans e2.symm⟩
    have hcard : S₂.card ≤ (dyad N).card := by
      refine Finset.card_le_card_of_injOn (fun p => p.1) (fun p hp => (hS₂mem p hp).1) ?_
      intro p hp p' hp' h
      have h' : p.1 = p'.1 := h
      exact Prod.ext h' (by rw [← (hS₂mem p hp).2, ← (hS₂mem p' hp').2, h'])
    calc ∑ p ∈ S₂, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤ S₂.card • r ^ 3 :=
          Finset.sum_le_card_nsmul _ _ _ fun p _ => by
            rw [hr]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_R2_le R χ t _ _) 3
      _ = S₂.card * r ^ 3 := nsmul_eq_mul _ _
      _ ≤ (dyad N).card * r ^ 3 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  -- the pairs with `D < (n₁, n₂) ≤ N`
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset (ℕ × ℕ), S₁ = (pairsGt N D).filter fun p => Nat.gcd p.1 p.2 ≤ ⌊N⌋₊ :=
    ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ → ℝ, A' = fun (d : ℕ) => C₆ * Λ * (r * N ^ 2 * ((d : ℝ) ^ 2)⁻¹ +
      (r ^ 2 + r ^ (5 / 4 : ℝ) * s) * N * ((d : ℝ))⁻¹) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℕ → ℝ, B' = fun (d : ℕ) => C₇ * G ^ 2 * Λ * (E * N ^ 2 * ((d : ℝ) ^ 2)⁻¹ +
      (r ^ 4 + E ^ (3 / 4 : ℝ) * r * s) * N * ((d : ℝ))⁻¹) := ⟨_, rfl⟩
  have hA'0 : ∀ d, 0 ≤ A' d := fun d => by rw [hA']; positivity
  have hB'0 : ∀ d, 0 ≤ B' d := fun d => by rw [hB']; positivity
  have hmaps : ∀ p ∈ S₁, Nat.gcd p.1 p.2 ∈ Finset.Ioc D ⌊N⌋₊ := by
    intro p hp
    rw [hS₁, Finset.mem_filter, pairsGt, Finset.mem_filter] at hp
    exact Finset.mem_Ioc.mpr ⟨hp.1.2, hp.2⟩
  have hfib : ∀ d ∈ Finset.Ioc D ⌊N⌋₊,
      ∑ p ∈ S₁ with Nat.gcd p.1 p.2 = d, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤ √(B' d) * √(A' d) := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hd0 : 0 < d := by omega
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
    have hdN : (d : ℝ) ≤ N := by
      have : (d : ℝ) ≤ (⌊N⌋₊ : ℝ) := by exact_mod_cast hd.2
      exact this.trans (Nat.floor_le hN.le)
    have hM : 1 ≤ N / d := by rw [le_div_iff₀ hd']; linarith
    -- the fiber lies in the pairs with gcd `d`
    have hsub : S₁.filter (fun p => Nat.gcd p.1 p.2 = d) ⊆
        (dyad N ×ˢ dyad N).filter (fun p => Nat.gcd p.1 p.2 = d) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      rw [hS₁, Finset.mem_filter, pairsGt, Finset.mem_filter] at hp
      exact ⟨hp.1.1.1, hp.2⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun p => ‖R2 R χ t p.1 p.2‖ ^ 3)
      fun _ _ _ => by positivity
    have h2 := sum_gcd_eq_le R χ t hN hd0 3
    have h3 := sum_cube_le_sqrt (dyad (N / d) ×ˢ dyad (N / d)) (fun p => ‖R2 R χ t p.1 p.2‖) fun _ => norm_nonneg _
    -- the moments at `M = N/d`
    have h6' := h6 q R χ t T (N / d) hT1 hM hprim hinj ht
    have h7' := (h7 q R χ t T (N / d) hT1 hM ht)
    rw [← Finset.sum_product' (dyad (N / d)) (dyad (N / d)) fun n₁ n₂ => ‖R2 R χ t n₁ n₂‖ ^ 2] at h6'
    rw [← Finset.sum_product' (dyad (N / d)) (dyad (N / d)) fun n₁ n₂ => ‖R2 R χ t n₁ n₂‖ ^ 4] at h7'
    rw [← hE, ← hr, ← hG] at h7'
    rw [← hr] at h6'
    rw [← hs] at h6' h7'
    have hΛd : ((q : ℝ) * T * (N / d)) ^ ε ≤ Λ := by
      rw [hΛ]
      refine Real.rpow_le_rpow (by positivity) ?_ hε.le
      have hNd : N / d ≤ N := div_le_self hN.le (by exact_mod_cast hd0)
      have : 0 ≤ (q : ℝ) * T := by positivity
      exact mul_le_mul_of_nonneg_left hNd this
    have hA6 : C₆ * ((q : ℝ) * T * (N / d)) ^ ε * (r * (N / d) ^ 2 + r ^ 2 * (N / d) + r ^ (5 / 4 : ℝ) * s * (N / d))
        ≤ A' d := by
      rw [hA']
      have e : r * (N / d) ^ 2 + r ^ 2 * (N / d) + r ^ (5 / 4 : ℝ) * s * (N / d) =
          r * N ^ 2 * ((d : ℝ) ^ 2)⁻¹ + (r ^ 2 + r ^ (5 / 4 : ℝ) * s) * N * ((d : ℝ))⁻¹ := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ r * N ^ 2 * ((d : ℝ) ^ 2)⁻¹ + (r ^ 2 + r ^ (5 / 4 : ℝ) * s) * N * ((d : ℝ))⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛd hC₆0) this
    have hB7 : C₇ * G ^ 2 * ((q : ℝ) * T * (N / d)) ^ ε *
        (E * (N / d) ^ 2 + r ^ 4 * (N / d) + E ^ (3 / 4 : ℝ) * r * s * (N / d)) ≤ B' d := by
      rw [hB']
      have e : E * (N / d) ^ 2 + r ^ 4 * (N / d) + E ^ (3 / 4 : ℝ) * r * s * (N / d) =
          E * N ^ 2 * ((d : ℝ) ^ 2)⁻¹ + (r ^ 4 + E ^ (3 / 4 : ℝ) * r * s) * N * ((d : ℝ))⁻¹ := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ E * N ^ 2 * ((d : ℝ) ^ 2)⁻¹ + (r ^ 4 + E ^ (3 / 4 : ℝ) * r * s) * N * ((d : ℝ))⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛd (by positivity)) this
    calc ∑ p ∈ S₁ with Nat.gcd p.1 p.2 = d, ‖R2 R χ t p.1 p.2‖ ^ 3
        ≤ ∑ p ∈ (dyad N ×ˢ dyad N).filter (fun p => Nat.gcd p.1 p.2 = d), ‖R2 R χ t p.1 p.2‖ ^ 3 := h1
      _ ≤ ∑ p ∈ dyad (N / d) ×ˢ dyad (N / d), ‖R2 R χ t p.1 p.2‖ ^ 3 := h2
      _ ≤ √(∑ p ∈ dyad (N / d) ×ˢ dyad (N / d), ‖R2 R χ t p.1 p.2‖ ^ 4) *
            √(∑ p ∈ dyad (N / d) ×ˢ dyad (N / d), ‖R2 R χ t p.1 p.2‖ ^ 2) := h3
      _ ≤ √(B' d) * √(A' d) := by
          gcongr
          · exact h7'.trans hB7
          · exact h6'.trans hA6
  -- the sum over `d`
  have hsumA : ∑ d ∈ Finset.Ioc D ⌊N⌋₊, A' d ≤ C₆ * Λ * a := by
    rw [hA', ha]
    simp only
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := sum_inv_sq_le N D
    have h2 := sum_inv_le N D
    rw [← hL] at h2
    have hc : 0 ≤ C₆ * Λ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hc
    have hx : 0 ≤ r * N ^ 2 := by positivity
    have hy : 0 ≤ (r ^ 2 + r ^ (5 / 4 : ℝ) * s) * N := by positivity
    have := mul_le_mul_of_nonneg_left h1 hx
    have := mul_le_mul_of_nonneg_left h2 hy
    linarith
  have hsumB : ∑ d ∈ Finset.Ioc D ⌊N⌋₊, B' d ≤ C₇ * G ^ 2 * Λ * b := by
    rw [hB', hb]
    simp only
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := sum_inv_sq_le N D
    have h2 := sum_inv_le N D
    rw [← hL] at h2
    have hc : 0 ≤ C₇ * G ^ 2 * Λ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hc
    have hx : 0 ≤ E * N ^ 2 := by positivity
    have hy : 0 ≤ (r ^ 4 + E ^ (3 / 4 : ℝ) * r * s) * N := by positivity
    have := mul_le_mul_of_nonneg_left h1 hx
    have := mul_le_mul_of_nonneg_left h2 hy
    linarith
  have hmain : ∑ p ∈ S₁, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤ √(C₆ * C₇) * G * Λ * √(a * b) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ d ∈ Finset.Ioc D ⌊N⌋₊, ∑ p ∈ S₁ with Nat.gcd p.1 p.2 = d, ‖R2 R χ t p.1 p.2‖ ^ 3
        ≤ ∑ d ∈ Finset.Ioc D ⌊N⌋₊, √(B' d) * √(A' d) := Finset.sum_le_sum hfib
      _ ≤ √(∑ d ∈ Finset.Ioc D ⌊N⌋₊, B' d) * √(∑ d ∈ Finset.Ioc D ⌊N⌋₊, A' d) :=
          Real.sum_sqrt_mul_sqrt_le _ hB'0 hA'0
      _ ≤ √(C₇ * G ^ 2 * Λ * b) * √(C₆ * Λ * a) := by
          gcongr
      _ = √(C₆ * C₇) * G * Λ * √(a * b) := by
          rw [← Real.sqrt_mul (by positivity)]
          have e : C₇ * G ^ 2 * Λ * b * (C₆ * Λ * a) = C₆ * C₇ * ((G * Λ) ^ 2 * (a * b)) := by ring
          rw [e, Real.sqrt_mul (show (0 : ℝ) ≤ C₆ * C₇ by positivity),
            Real.sqrt_mul (show (0 : ℝ) ≤ (G * Λ) ^ 2 by positivity), Real.sqrt_sq (show (0 : ℝ) ≤ G * Λ by positivity)]
          ring
  -- the two parts
  have hsplit : ∑ p ∈ pairsGt N D, ‖R2 R χ t p.1 p.2‖ ^ 3 =
      ∑ p ∈ S₁, ‖R2 R χ t p.1 p.2‖ ^ 3 + ∑ p ∈ S₂, ‖R2 R χ t p.1 p.2‖ ^ 3 := by
    rw [hS₁, hS₂, Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  linarith

end LinnikCGLL1010

#print axioms LinnikCGLL1010.lemma106'
#print axioms LinnikCGLL1010.sum_gcd_eq_le
#print axioms LinnikCGLL1010.lemma1010
