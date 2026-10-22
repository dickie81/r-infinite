/-
# Round 676: their Lemma 10.10 with its case analysis, and their Remark 10.3 (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their case analysis in Lemma 10.10 (round 675 quotes the statement): "Since N ≥ (qT)^{1/2} and D = N²/(qT), we have
|W|^{5/4}(qT)^{1/2}N ≫ |W|qT = |W|N²/D." (text layer line 5436; spaces restored, the exponents transcribed); "We split
into cases based on whether |W| > (qT)^{2/3} or not." (line 5440; spaces restored, the exponent transcribed). The first
case uses "N|W|⁴ ≫ |W|³qT ≥ E(W)qT," (line 5445; spaces restored, the exponents transcribed) and ends with their
(10.4), `⪅ N|W|³`; the second ends with their (10.5), after "Notice that, in this case, our assumption gives
E(W)^{1/8}N ≥ (qT)^{1/2}|W|^{5/8}." (line 5483; spaces restored, the exponents transcribed).

Their Remark 10.3: "Suppose that |W| < (qT)^{2/3} and E(W)^{1/8}N < (qT)^{1/2}|W|^{5/8}. Then (qT)²|W|^{3/2} >
qTN|W|^{1/2}E(W)^{1/2}." (lines 4666–4667; spaces restored, the exponents transcribed), by a chain whose "first
strict inequality follows from the lower bound N ≥ (qT)^{2/3} in the present range" (lines 4673–4674; spaces
restored, the exponent transcribed), where the range of their Proposition 10.2 is "(qT)^{2/3}/2 ≤ N ≤ qT" (line
4646; spaces restored, the exponent transcribed).

The stack's form.
* The energy. `sq_le_energy`: `|R|² ≤ E`, from the quadruples `(i, j, i, j)`. `energy_le_cube`: `E ≤ |R|³` at one
  point per character, since `χ_iχ_j = χ_kχ_l` determines `χ_l` and so `l`; their case analysis uses this as
  `|W|³qT ≥ E(W)qT`.
* The case analysis is an inequality between real numbers. With `r = u⁸`, `E = v⁸` and `qT = z¹²` (`exists_pow_eq`,
  `pow_rpow_eq`) every power in it is a natural power of `u`, `v` and `z`, and it becomes the polynomial inequality
  `case_poly`, proved in two cases: `z ≤ u` (`case_one`, their `|W| ≥ (qT)^{2/3}`) and `u < z` with their assumption
  `z⁶u⁵ ≤ vN` (`case_two`, their `|W| < (qT)^{2/3}`). The stack uses `N ≥ (qT)^{1/2}/2`, which `N ≥ (qT)^{2/3}/2`
  and `qT ≥ 1` give, where they write `N ≥ (qT)^{1/2}` under `≫`. `case_le` is the result in real powers.
* `remark103` is the stack's form of their Remark 10.3. Their remark holds as stated, strictly and with the constant
  `1`, for every `N > 0`: with `E ≤ |W|³` (`energy_le_cube`; the fourth point is unique, lines 4716–4718), their
  second assumption gives `E^{1/2} = E^{1/8}E^{3/8} < (qT)^{1/2}|W|^{7/4}N^{−1}`, so
  `qTN|W|^{1/2}E^{1/2} < (qT)^{3/2}|W|^{9/4}`, and their first gives `(qT)^{3/2}|W|^{9/4} < (qT)²|W|^{3/2}`. The slip
  is in their chain: its step `(qT)³|W|³N^{−3} < qT|W|³` (line 4669) needs `N³ > (qT)²`, which fails for
  `(qT)^{2/3}/2 ≤ N ≤ (qT)^{2/3}`. The stack reads that step as their "first strict inequality", since the chain's
  first step follows from their second assumption (lines 4667–4668). `remark103` does not assume `E ≤ |W|³`: with
  `N ≥ (qT)^{2/3}/2` it gives `qTN|W|^{1/2}E^{1/2} ≤ 8(qT)²|W|^{3/2}`, and the `8` is attained, at `|W| = (qT)^{2/3}`,
  `N = (qT)^{2/3}/2` and `E = 256(qT)²`. The constant does not affect their use of it, which is up to `⪅`.
* `lemma1010_case`: their Lemma 10.10 with their hypotheses, from round 675's `lemma1010` and `case_le`, with
  `D = ⌊N²/(qT)⌋`.

Plain statements, with `q ≥ 1`, `n ∼ N` round 670's `dyad`, `R₂` round 669's, `E` round 659's `energy`,
`G = d(q)(⌊log₂|R|²⌋ + 1)` and `L = 1 + log max(1, N)`.
* `sq_le_energy`, `energy_le_cube`: `|R|² ≤ E`; and `E ≤ |R|³` for `χ` injective on `R`.
* `pow_rpow_eq`, `exists_pow_eq`: `(u^m)^x = u^k` for `u ≥ 0` and `mx = k`; and every `r ≥ 0` is `u^m` for some
  `u ≥ 0`, for `m ≥ 1`.
* `sq_add_sq_le`, `z6_le`, `case_a`, `case_one`, `case_two`, `case_poly`: the polynomial inequalities.
* `case_le`: for `r = 0` or `r ≥ 1`, `0 ≤ E ≤ r³`, `Q ≥ 1`, `Q^{2/3}/2 ≤ N`, `L ≥ 1`, `N²/Q < D + 1` and either
  `r ≥ Q^{2/3}` or `Q^{1/2}r^{5/8} ≤ E^{1/8}N`, their factors `a = rN²·2/(D + 1) + (r² + r^{5/4}Q^{1/2})NL` and
  `b = EN²·2/(D + 1) + (r⁴ + E^{3/4}rQ^{1/2})NL` have `√(ab) ≤ 8L(Nr³ + NQ^{1/4}r^{21/8} + E^{1/2}r^{1/2}N²)`.
* `remark103`: for `r, E ≥ 0`, `Q ≥ 1`, `N ≥ Q^{2/3}/2`, `r ≤ Q^{2/3}` and `E^{1/8}N ≤ Q^{1/2}r^{5/8}`,
  `QNr^{1/2}E^{1/2} ≤ 8Q²r^{3/2}`.
* `lemma1010_case`: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for primitive characters injective
  on `R`, `T ≥ 1`, points `|t_i| ≤ T`, `(qT)^{2/3}/2 ≤ N`, `D = ⌊N²/(qT)⌋` and either `|R| ≥ (qT)^{2/3}` or
  `(qT)^{1/2}|R|^{5/8} ≤ E^{1/8}N`, `Σ_{n₁,n₂∼N, (n₁,n₂)>D}|R₂(n₁, n₂)|³ ≤
  8CGL(qTN)^ε(N|R|³ + N(qT)^{1/4}|R|^{21/8} + E^{1/2}|R|^{1/2}N²) + |{n ∼ N}||R|³`.

The file imports `LinnikCGLL1010.lean`.
-/

import LinnikCGLL1010

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLCase

open LinnikCGLL105 LinnikCGLMom4 LinnikCGLT101 LinnikCGLL107 LinnikCGLL1010

/-! ### The energy between `|R|²` and `|R|³` -/

section energy

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- `|R|² ≤ E`: the quadruples `(i, j, i, j)`. -/
lemma sq_le_energy : (R.card : ℝ) ^ 2 ≤ energy R χ t := by
  classical
  have h : (R ×ˢ R).card ≤ energy R χ t := by
    unfold energy
    refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2, p.1, p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_product] at hp
      have e : t p.1 + t p.2 - t p.1 - t p.2 = 0 := by ring
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1, hp.2, hp.1, hp.2⟩, by rw [e, abs_zero]; norm_num, trivial⟩
    · intro p _ p' _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1
  rw [Finset.card_product] at h
  have : ((R.card * R.card : ℕ) : ℝ) ≤ energy R χ t := by exact_mod_cast h
  push_cast at this
  nlinarith

/-- `E ≤ |R|³` at one point per character: in a quadruple of the energy, `χ_l` is determined by `χ_i`, `χ_j` and
`χ_k`, and so is `l`. -/
lemma energy_le_cube (hinj : Set.InjOn χ R) : (energy R χ t : ℝ) ≤ (R.card : ℝ) ^ 3 := by
  classical
  have h : energy R χ t ≤ (R ×ˢ R ×ˢ R).card := by
    unfold energy
    refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2.1, p.2.2.1)) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
      simp only [Finset.mem_coe, Finset.mem_product]
      exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩
    · intro p hp p' hp' h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hl : χ p.2.2.2 = χ p'.2.2.2 := by
        have e := hp.2.2
        have e' := hp'.2.2
        rw [h1, h2, h3] at e
        rw [e] at e'
        exact mul_left_cancel e'
      have hl' := hinj hp.1.2.2.2 hp'.1.2.2.2 hl
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 hl'))
  rw [Finset.card_product, Finset.card_product] at h
  have : (energy R χ t : ℝ) ≤ ((R.card * (R.card * R.card) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this
  nlinarith

end energy

/-! ### Their case analysis -/

/-- `(u^m)^x = u^k` for `u ≥ 0` and `mx = k`. -/
lemma pow_rpow_eq {u : ℝ} (hu : 0 ≤ u) (m k : ℕ) {x : ℝ} (h : (m : ℝ) * x = k) : (u ^ m) ^ x = u ^ k := by
  rw [← Real.rpow_natCast u m, ← Real.rpow_mul hu, h, Real.rpow_natCast]

/-- For `m ≠ 0`, a nonnegative real is the `m`-th power of its `m`-th root. -/
lemma exists_pow_eq {r : ℝ} (hr : 0 ≤ r) (m : ℕ) (hm : m ≠ 0) : ∃ u : ℝ, 0 ≤ u ∧ r = u ^ m := by
  refine ⟨r ^ (1 / (m : ℝ)), by positivity, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  have : (1 / (m : ℝ)) * m = 1 := by field_simp
  rw [this, Real.rpow_one]

/-- `y² + w² ≤ (x + y + w)²` for `x, y, w ≥ 0`. -/
lemma sq_add_sq_le {x y w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) : y ^ 2 + w ^ 2 ≤ (x + y + w) ^ 2 := by
  nlinarith [mul_nonneg hx hy, mul_nonneg hx hw, mul_nonneg hy hw, sq_nonneg x]

/-- `z⁶ ≤ 2u²N` for `u, z ≥ 1` and `N ≥ z⁸/2`. -/
lemma z6_le {u z N : ℝ} (hu1 : 1 ≤ u) (hz : 1 ≤ z) (hN : z ^ 8 / 2 ≤ N) : z ^ 6 ≤ 2 * u ^ 2 * N := by
  have h8 : 0 ≤ z ^ 8 / 2 := by positivity
  have hN0 : 0 ≤ N := by linarith
  have h1 : z ^ 6 ≤ z ^ 8 := pow_le_pow_right₀ hz (by norm_num)
  have h2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
  have h3 : N ≤ u ^ 2 * N := le_mul_of_one_le_left hN0 h2
  linarith

/-- Their first factor, `a ≤ 5L(u¹⁶ + u¹⁰z⁶)N`, with `r = u⁸`, `qT = z¹²` and `p = 2/(D + 1)`, for `u, z, L ≥ 1`,
`N ≥ z⁸/2` and `N²p ≤ 2z¹²`. -/
lemma case_a {u z N L p : ℝ} (hu1 : 1 ≤ u) (hz : 1 ≤ z) (hN : z ^ 8 / 2 ≤ N) (hL : 1 ≤ L)
    (hNp : N ^ 2 * p ≤ 2 * z ^ 12) :
    u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L ≤ 5 * L * ((u ^ 16 + u ^ 10 * z ^ 6) * N) := by
  have h8 : 0 ≤ z ^ 8 / 2 := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hz6 := z6_le hu1 hz hN
  have h1 : u ^ 8 * (N ^ 2 * p) ≤ u ^ 8 * (2 * z ^ 12) := mul_le_mul_of_nonneg_left hNp (by positivity)
  have h2 : u ^ 8 * z ^ 6 * z ^ 6 ≤ u ^ 8 * z ^ 6 * (2 * u ^ 2 * N) := mul_le_mul_of_nonneg_left hz6 (by positivity)
  have h3 : 0 ≤ u ^ 16 * N := by positivity
  have h4 : (u ^ 16 + u ^ 10 * z ^ 6) * N ≤ L * ((u ^ 16 + u ^ 10 * z ^ 6) * N) :=
    le_mul_of_one_le_left (by positivity) hL
  linarith

/-- **Their (10.4)**, as a polynomial inequality: the case `z ≤ u`, `|W| ≥ (qT)^{2/3}`, for `u, z, L ≥ 1`,
`0 ≤ v ≤ u³`, `N ≥ z⁸/2`, `p ≥ 0` and `N²p ≤ 2z¹²`. -/
lemma case_one {u v z N L p : ℝ} (hu1 : 1 ≤ u) (hv0 : 0 ≤ v) (hvu : v ≤ u ^ 3) (hz : 1 ≤ z)
    (hN : z ^ 8 / 2 ≤ N) (hL : 1 ≤ L) (hp0 : 0 ≤ p) (hNp : N ^ 2 * p ≤ 2 * z ^ 12) (hzu : z ≤ u) :
    (u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L) *
      (v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L) ≤ (8 * L * (N * u ^ 24)) ^ 2 := by
  have h8 : 0 ≤ z ^ 8 / 2 := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hv6 : v ^ 6 ≤ u ^ 18 := by
    have := pow_le_pow_left₀ hv0 hvu 6
    rwa [← pow_mul] at this
  have hv8 : v ^ 8 ≤ u ^ 24 := by
    have := pow_le_pow_left₀ hv0 hvu 8
    rwa [← pow_mul] at this
  have hz6u : z ^ 6 ≤ u ^ 6 := pow_le_pow_left₀ hz0 hzu 6
  have hA := case_a hu1 hz hN hL hNp
  have ha' : u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L ≤ 10 * L * (u ^ 16 * N) := by
    have h1 : u ^ 10 * z ^ 6 ≤ u ^ 10 * u ^ 6 := mul_le_mul_of_nonneg_left hz6u (by positivity)
    have h2 : u ^ 10 * z ^ 6 * N ≤ u ^ 10 * u ^ 6 * N := mul_le_mul_of_nonneg_right h1 hN0
    have h3 : L * (u ^ 10 * z ^ 6 * N) ≤ L * (u ^ 10 * u ^ 6 * N) := mul_le_mul_of_nonneg_left h2 hL0
    linarith
  have hz12 : z ^ 12 ≤ 2 * u ^ 8 * N := by
    have h1 : z ^ 12 ≤ z ^ 16 := pow_le_pow_right₀ hz (by norm_num)
    have h2 : z ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ hz0 hzu 8
    have h3 : z ^ 8 * z ^ 8 ≤ u ^ 8 * z ^ 8 := mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : u ^ 8 * z ^ 8 ≤ u ^ 8 * (2 * N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hb' : v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L ≤ 6 * L * (u ^ 32 * N) := by
    have h1 : v ^ 8 * (N ^ 2 * p) ≤ v ^ 8 * (2 * z ^ 12) := mul_le_mul_of_nonneg_left hNp (by positivity)
    have h2 : v ^ 8 * z ^ 12 ≤ u ^ 24 * z ^ 12 := mul_le_mul_of_nonneg_right hv8 (by positivity)
    have h3 : u ^ 24 * z ^ 12 ≤ u ^ 24 * (2 * u ^ 8 * N) := mul_le_mul_of_nonneg_left hz12 (by positivity)
    have h4 : v ^ 6 * u ^ 8 * z ^ 6 ≤ u ^ 18 * u ^ 8 * u ^ 6 := by
      have := mul_le_mul hv6 (le_refl (u ^ 8)) (by positivity) (by positivity)
      exact mul_le_mul this hz6u (by positivity) (by positivity)
    have h5 : v ^ 6 * u ^ 8 * z ^ 6 * N ≤ u ^ 18 * u ^ 8 * u ^ 6 * N := mul_le_mul_of_nonneg_right h4 hN0
    have h6 : L * (v ^ 6 * u ^ 8 * z ^ 6 * N) ≤ L * (u ^ 18 * u ^ 8 * u ^ 6 * N) :=
      mul_le_mul_of_nonneg_left h5 hL0
    have h7 : u ^ 32 * N ≤ L * (u ^ 32 * N) := le_mul_of_one_le_left (by positivity) hL
    linarith
  have hb0 : 0 ≤ v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L := by positivity
  have e1 : (10 * L * (u ^ 16 * N)) * (6 * L * (u ^ 32 * N)) = 60 * (L ^ 2 * u ^ 48 * N ^ 2) := by ring
  have e2 : (8 * L * (N * u ^ 24)) ^ 2 = 64 * (L ^ 2 * u ^ 48 * N ^ 2) := by ring
  have h0 : 0 ≤ L ^ 2 * u ^ 48 * N ^ 2 := by positivity
  calc (u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L) *
        (v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L)
      ≤ (10 * L * (u ^ 16 * N)) * (6 * L * (u ^ 32 * N)) := mul_le_mul ha' hb' hb0 (by positivity)
    _ ≤ (8 * L * (N * u ^ 24)) ^ 2 := by rw [e1, e2]; linarith

/-- **Their (10.5)**, as a polynomial inequality: the case `u < z` under `z⁶u⁵ ≤ vN`, their
`E(W)^{1/8}N ≥ (qT)^{1/2}|W|^{5/8}`, for `u, z, L ≥ 1`, `0 ≤ v ≤ u³`, `N ≥ z⁸/2`, `p ≥ 0` and `N²p ≤ 2z¹²`. -/
lemma case_two {u v z N L p : ℝ} (hu1 : 1 ≤ u) (hv0 : 0 ≤ v) (hvu : v ≤ u ^ 3) (hz : 1 ≤ z)
    (hN : z ^ 8 / 2 ≤ N) (hL : 1 ≤ L) (hp0 : 0 ≤ p) (hNp : N ^ 2 * p ≤ 2 * z ^ 12) (hzu : u < z)
    (halt : z ^ 6 * u ^ 5 ≤ v * N) :
    (u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L) *
      (v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L) ≤
      64 * L ^ 2 * ((N * z ^ 3 * u ^ 21) ^ 2 + (v ^ 4 * u ^ 4 * N ^ 2) ^ 2) := by
  have h8 : 0 ≤ z ^ 8 / 2 := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hv2 : v ^ 2 ≤ u ^ 6 := by
    have := pow_le_pow_left₀ hv0 hvu 2
    rwa [← pow_mul] at this
  have hz6 := z6_le hu1 hz hN
  have hu6z : u ^ 6 ≤ z ^ 6 := pow_le_pow_left₀ hu0 hzu.le 6
  have hA := case_a hu1 hz hN hL hNp
  have ha' : u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L ≤ 10 * L * (u ^ 10 * z ^ 6 * N) := by
    have h1 : u ^ 10 * u ^ 6 ≤ u ^ 10 * z ^ 6 := mul_le_mul_of_nonneg_left hu6z (by positivity)
    have h2 : u ^ 10 * u ^ 6 * N ≤ u ^ 10 * z ^ 6 * N := mul_le_mul_of_nonneg_right h1 hN0
    have h3 : L * (u ^ 10 * u ^ 6 * N) ≤ L * (u ^ 10 * z ^ 6 * N) := mul_le_mul_of_nonneg_left h2 hL0
    linarith
  have hb' : v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L ≤
      5 * L * ((u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N) := by
    have h1 : v ^ 8 * (N ^ 2 * p) ≤ v ^ 8 * (2 * z ^ 12) := mul_le_mul_of_nonneg_left hNp (by positivity)
    have h2 : v ^ 6 * z ^ 6 * (v ^ 2 * z ^ 6) ≤ v ^ 6 * z ^ 6 * (u ^ 6 * (2 * u ^ 2 * N)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul hv2 hz6 (by positivity) (by positivity)
    have h3 : 0 ≤ u ^ 32 * N := by positivity
    have h4 : (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N ≤ L * ((u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N) :=
      le_mul_of_one_le_left (by positivity) hL
    linarith
  have hkey : v ^ 6 * u ^ 18 * z ^ 12 * N ^ 2 ≤ v ^ 8 * u ^ 8 * N ^ 4 := by
    have h1 : (z ^ 6 * u ^ 5) ^ 2 ≤ (v * N) ^ 2 := pow_le_pow_left₀ (by positivity) halt 2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ v ^ 6 * u ^ 8 * N ^ 2)
    have e1 : v ^ 6 * u ^ 8 * N ^ 2 * (z ^ 6 * u ^ 5) ^ 2 = v ^ 6 * u ^ 18 * z ^ 12 * N ^ 2 := by ring
    have e2 : v ^ 6 * u ^ 8 * N ^ 2 * (v * N) ^ 2 = v ^ 8 * u ^ 8 * N ^ 4 := by ring
    rw [e1, e2] at h2
    exact h2
  have hb0 : 0 ≤ v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L := by positivity
  have e1 : (10 * L * (u ^ 10 * z ^ 6 * N)) * (5 * L * ((u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N)) =
      50 * (L ^ 2 * (N ^ 2 * z ^ 6 * u ^ 42)) + 50 * (L ^ 2 * (v ^ 6 * u ^ 18 * z ^ 12 * N ^ 2)) := by ring
  have e2 : 64 * L ^ 2 * ((N * z ^ 3 * u ^ 21) ^ 2 + (v ^ 4 * u ^ 4 * N ^ 2) ^ 2) =
      64 * (L ^ 2 * (N ^ 2 * z ^ 6 * u ^ 42)) + 64 * (L ^ 2 * (v ^ 8 * u ^ 8 * N ^ 4)) := by ring
  have h1 : 0 ≤ L ^ 2 * (N ^ 2 * z ^ 6 * u ^ 42) := by positivity
  have h2 : 0 ≤ L ^ 2 * (v ^ 6 * u ^ 18 * z ^ 12 * N ^ 2) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ L ^ 2)
  calc (u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L) *
        (v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L)
      ≤ (10 * L * (u ^ 10 * z ^ 6 * N)) * (5 * L * ((u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N)) :=
        mul_le_mul ha' hb' hb0 (by positivity)
    _ ≤ 64 * L ^ 2 * ((N * z ^ 3 * u ^ 21) ^ 2 + (v ^ 4 * u ^ 4 * N ^ 2) ^ 2) := by rw [e1, e2]; linarith

/-- **Their case analysis, as a polynomial inequality**: with `r = u⁸`, `E = v⁸`, `qT = z¹²` and `p = 2/(D + 1)`,
for `u = 0` or `u ≥ 1`, `0 ≤ v ≤ u³`, `z, L ≥ 1`, `N ≥ z⁸/2`, `p ≥ 0`, `N²p ≤ 2z¹²` and either `z ≤ u` or
`z⁶u⁵ ≤ vN`. -/
lemma case_poly {u v z N L p : ℝ} (hu : u = 0 ∨ 1 ≤ u) (hv0 : 0 ≤ v) (hvu : v ≤ u ^ 3) (hz : 1 ≤ z)
    (hN : z ^ 8 / 2 ≤ N) (hL : 1 ≤ L) (hp0 : 0 ≤ p) (hNp : N ^ 2 * p ≤ 2 * z ^ 12)
    (halt : z ≤ u ∨ z ^ 6 * u ^ 5 ≤ v * N) :
    (u ^ 8 * N ^ 2 * p + (u ^ 16 + u ^ 10 * z ^ 6) * N * L) *
      (v ^ 8 * N ^ 2 * p + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L) ≤
      (8 * L * (N * u ^ 24 + N * z ^ 3 * u ^ 21 + v ^ 4 * u ^ 4 * N ^ 2)) ^ 2 := by
  have h8 : 0 ≤ z ^ 8 / 2 := by positivity
  have hN0 : 0 ≤ N := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hz0 : 0 ≤ z := by linarith
  rcases hu with rfl | hu1
  · have hv : v = 0 := le_antisymm (by rw [zero_pow (by norm_num)] at hvu; exact hvu) hv0
    subst hv
    simp
  have hu0 : 0 ≤ u := by linarith
  have hx : 0 ≤ N * u ^ 24 := by positivity
  have hy : 0 ≤ N * z ^ 3 * u ^ 21 := by positivity
  have hw : 0 ≤ v ^ 4 * u ^ 4 * N ^ 2 := by positivity
  rcases le_or_gt z u with hzu | hzu
  · refine (case_one hu1 hv0 hvu hz hN hL hp0 hNp hzu).trans (pow_le_pow_left₀ (by positivity) ?_ 2)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have halt2 : z ^ 6 * u ^ 5 ≤ v * N := by
      rcases halt with h | h
      · exact absurd h (not_le.mpr hzu)
      · exact h
    refine (case_two hu1 hv0 hvu hz hN hL hp0 hNp hzu halt2).trans ?_
    have e : (8 * L * (N * u ^ 24 + N * z ^ 3 * u ^ 21 + v ^ 4 * u ^ 4 * N ^ 2)) ^ 2 =
        64 * L ^ 2 * ((N * u ^ 24 + N * z ^ 3 * u ^ 21 + v ^ 4 * u ^ 4 * N ^ 2) ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (sq_add_sq_le hx hy hw) (by positivity)

/-- **Their case analysis (10.4)–(10.5)**: for `r = 0` or `r ≥ 1`, `0 ≤ E ≤ r³`, `Q ≥ 1`, `Q^{2/3}/2 ≤ N`, `L ≥ 1`,
`N²/Q < D + 1` and either `r ≥ Q^{2/3}` or `Q^{1/2}r^{5/8} ≤ E^{1/8}N`, the product of their two factors
`a = rN²·2/(D + 1) + (r² + r^{5/4}Q^{1/2})NL` and `b = EN²·2/(D + 1) + (r⁴ + E^{3/4}rQ^{1/2})NL` has
`√(ab) ≤ 8L(Nr³ + NQ^{1/4}r^{21/8} + E^{1/2}r^{1/2}N²)`. -/
theorem case_le {r E Q N L : ℝ} {D : ℕ} (hr : r = 0 ∨ 1 ≤ r) (hE0 : 0 ≤ E) (hEr : E ≤ r ^ 3) (hQ : 1 ≤ Q)
    (hN : Q ^ (2 / 3 : ℝ) / 2 ≤ N) (hL : 1 ≤ L) (hD : N ^ 2 / Q < D + 1)
    (halt : Q ^ (2 / 3 : ℝ) ≤ r ∨ Q ^ (1 / 2 : ℝ) * r ^ (5 / 8 : ℝ) ≤ E ^ (1 / 8 : ℝ) * N) :
    √((r * N ^ 2 * (2 / (D + 1)) + (r ^ 2 + r ^ (5 / 4 : ℝ) * Q ^ (1 / 2 : ℝ)) * N * L) *
      (E * N ^ 2 * (2 / (D + 1)) + (r ^ 4 + E ^ (3 / 4 : ℝ) * r * Q ^ (1 / 2 : ℝ)) * N * L)) ≤
      8 * L * (N * r ^ 3 + N * Q ^ (1 / 4 : ℝ) * r ^ (21 / 8 : ℝ) + E ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) * N ^ 2) := by
  have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
  obtain ⟨u, hu0, rfl⟩ := exists_pow_eq hr0 8 (by norm_num)
  obtain ⟨v, hv0, rfl⟩ := exists_pow_eq hE0 8 (by norm_num)
  obtain ⟨z, hz0, rfl⟩ := exists_pow_eq (by linarith : (0 : ℝ) ≤ Q) 12 (by norm_num)
  rw [pow_rpow_eq (x := 5 / 4) hu0 8 10 (by norm_num), pow_rpow_eq (x := 1 / 2) hz0 12 6 (by norm_num),
    pow_rpow_eq (x := 3 / 4) hv0 8 6 (by norm_num), pow_rpow_eq (x := 1 / 4) hz0 12 3 (by norm_num),
    pow_rpow_eq (x := 21 / 8) hu0 8 21 (by norm_num), pow_rpow_eq (x := 1 / 2) hv0 8 4 (by norm_num),
    pow_rpow_eq (x := 1 / 2) hu0 8 4 (by norm_num)]
  rw [pow_rpow_eq (x := 2 / 3) hz0 12 8 (by norm_num)] at hN
  rw [pow_rpow_eq (x := 2 / 3) hz0 12 8 (by norm_num), pow_rpow_eq (x := 1 / 2) hz0 12 6 (by norm_num),
    pow_rpow_eq (x := 5 / 8) hu0 8 5 (by norm_num), pow_rpow_eq (x := 1 / 8) hv0 8 1 (by norm_num), pow_one] at halt
  have hu : u = 0 ∨ 1 ≤ u := by
    rcases hr with h | h
    · left; exact pow_eq_zero_iff (by norm_num) |>.mp h
    · right
      by_contra hc
      push Not at hc
      have : u ^ 8 < 1 := pow_lt_one₀ hu0 hc (by norm_num)
      linarith
  have hvu : v ≤ u ^ 3 := by
    have : v ^ 8 ≤ (u ^ 3) ^ 8 := by rw [← pow_mul]; exact hEr.trans (le_of_eq (by ring))
    exact (pow_le_pow_iff_left₀ hv0 (by positivity) (by norm_num)).mp this
  have hz : 1 ≤ z := by
    by_contra hc
    push Not at hc
    have : z ^ 12 < 1 := pow_lt_one₀ hz0 hc (by norm_num)
    linarith
  have halt' : z ≤ u ∨ z ^ 6 * u ^ 5 ≤ v * N := by
    rcases halt with h | h
    · left; exact (pow_le_pow_iff_left₀ hz0 hu0 (by norm_num)).mp h
    · right; exact h
  have hp0 : (0 : ℝ) ≤ 2 / (D + 1) := by positivity
  have hNp : N ^ 2 * (2 / (D + 1)) ≤ 2 * z ^ 12 := by
    have hQ0 : (0 : ℝ) < z ^ 12 := by linarith
    rw [div_lt_iff₀ hQ0] at hD
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hpoly := case_poly hu hv0 hvu hz hN hL hp0 hNp halt'
  have hY : 0 ≤ 8 * L * (N * u ^ 24 + N * z ^ 3 * u ^ 21 + v ^ 4 * u ^ 4 * N ^ 2) := by
    have h8 : 0 ≤ z ^ 8 / 2 := by positivity
    have : 0 ≤ N := by linarith
    have : 0 ≤ L := by linarith
    positivity
  have e1 : (u ^ 8) ^ 2 = u ^ 16 := by ring
  have e2 : (u ^ 8) ^ 4 = u ^ 32 := by ring
  have e3 : (u ^ 8) ^ 3 = u ^ 24 := by ring
  rw [e1, e2, e3]
  calc √((u ^ 8 * N ^ 2 * (2 / (D + 1)) + (u ^ 16 + u ^ 10 * z ^ 6) * N * L) *
        (v ^ 8 * N ^ 2 * (2 / (D + 1)) + (u ^ 32 + v ^ 6 * u ^ 8 * z ^ 6) * N * L))
      ≤ √((8 * L * (N * u ^ 24 + N * z ^ 3 * u ^ 21 + v ^ 4 * u ^ 4 * N ^ 2)) ^ 2) := Real.sqrt_le_sqrt hpoly
    _ = 8 * L * (N * u ^ 24 + N * z ^ 3 * u ^ 21 + v ^ 4 * u ^ 4 * N ^ 2) := Real.sqrt_sq hY

/-! ### Their Remark 10.3 -/

/-- **Their Remark 10.3, in the stack's form**: for `r ≥ 0`, `E ≥ 0`, `Q ≥ 1`, `N ≥ Q^{2/3}/2`, `r ≤ Q^{2/3}` and
`E^{1/8}N ≤ Q^{1/2}r^{5/8}`, `QNr^{1/2}E^{1/2} ≤ 8Q²r^{3/2}`. Their remark has the constant `1` and uses `E ≤ r³`,
which this form does not assume. -/
theorem remark103 {r E Q N : ℝ} (hr0 : 0 ≤ r) (hE0 : 0 ≤ E) (hQ : 1 ≤ Q) (hN : Q ^ (2 / 3 : ℝ) / 2 ≤ N)
    (hrQ : r ≤ Q ^ (2 / 3 : ℝ)) (hEN : E ^ (1 / 8 : ℝ) * N ≤ Q ^ (1 / 2 : ℝ) * r ^ (5 / 8 : ℝ)) :
    Q * N * r ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) ≤ 8 * Q ^ 2 * r ^ (3 / 2 : ℝ) := by
  obtain ⟨u, hu0, rfl⟩ := exists_pow_eq hr0 8 (by norm_num)
  obtain ⟨v, hv0, rfl⟩ := exists_pow_eq hE0 8 (by norm_num)
  obtain ⟨z, hz0, rfl⟩ := exists_pow_eq (by linarith : (0 : ℝ) ≤ Q) 12 (by norm_num)
  rw [pow_rpow_eq (x := 1 / 2) hu0 8 4 (by norm_num), pow_rpow_eq (x := 1 / 2) hv0 8 4 (by norm_num),
    pow_rpow_eq (x := 3 / 2) hu0 8 12 (by norm_num)]
  rw [pow_rpow_eq (x := 2 / 3) hz0 12 8 (by norm_num)] at hN hrQ
  rw [pow_rpow_eq (x := 1 / 8) hv0 8 1 (by norm_num), pow_one, pow_rpow_eq (x := 1 / 2) hz0 12 6 (by norm_num),
    pow_rpow_eq (x := 5 / 8) hu0 8 5 (by norm_num)] at hEN
  have hz : 1 ≤ z := by
    by_contra hc
    push Not at hc
    have : z ^ 12 < 1 := pow_lt_one₀ hz0 hc (by norm_num)
    linarith
  have huz : u ≤ z := (pow_le_pow_iff_left₀ hu0 hz0 (by norm_num)).mp hrQ
  have hN0 : 0 < N := by
    have : 0 < z ^ 8 / 2 := by positivity
    linarith
  -- `N⁴v⁴ ≤ z²⁴u²⁰` and `z²⁴ ≤ 8N³`
  have h1 : (v * N) ^ 4 ≤ (z ^ 6 * u ^ 5) ^ 4 := pow_le_pow_left₀ (by positivity) hEN 4
  have h2 : (z ^ 8) ^ 3 ≤ (2 * N) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h3 : u ^ 12 ≤ z ^ 12 := pow_le_pow_left₀ hu0 huz 12
  -- multiply out: `z¹²N⁴u⁴v⁴ ≤ z³⁶u²⁴ ≤ 8z²⁴u¹²N³`
  have h4 : z ^ 12 * u ^ 4 * ((v * N) ^ 4) ≤ z ^ 12 * u ^ 4 * ((z ^ 6 * u ^ 5) ^ 4) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : z ^ 36 * u ^ 12 * u ^ 12 ≤ z ^ 36 * u ^ 12 * z ^ 12 := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : z ^ 24 * u ^ 12 * (z ^ 8) ^ 3 ≤ z ^ 24 * u ^ 12 * (2 * N) ^ 3 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hfin : z ^ 12 * N * u ^ 4 * v ^ 4 * N ^ 3 ≤ 8 * (z ^ 12) ^ 2 * u ^ 12 * N ^ 3 := by nlinarith
  have hN3 : 0 < N ^ 3 := by positivity
  exact le_of_mul_le_mul_right hfin hN3

/-! ### Their Lemma 10.10 -/

/-- **Their Lemma 10.10 (large gcd terms), at one point per character**: from `CGLT101`, for every `ε > 0` there is
`C ≥ 0` such that, for `q ≥ 1`, primitive characters injective on `R`, `T ≥ 1`, points `|t_i| ≤ T`,
`(qT)^{2/3}/2 ≤ N`, `D = ⌊N²/(qT)⌋` and either `|R| ≥ (qT)^{2/3}` or `(qT)^{1/2}|R|^{5/8} ≤ E^{1/8}N`,
`Σ_{n₁,n₂∼N, (n₁,n₂)>D}|R₂(n₁, n₂)|³ ≤ 8CGL(qTN)^ε(N|R|³ + N(qT)^{1/4}|R|^{21/8} + E^{1/2}|R|^{1/2}N²) + |{n ∼ N}||R|³`,
with `G = d(q)(⌊log₂|R|²⌋ + 1)` and `L = 1 + log max(1, N)`: round 675's `lemma1010` and `case_le`. -/
theorem lemma1010_case (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T N : ℝ), 1 ≤ T → (∀ i ∈ R, (χ i).IsPrimitive) → Set.InjOn χ R → (∀ i ∈ R, |t i| ≤ T) →
      ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N →
      (((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ R.card ∨
        ((q : ℝ) * T) ^ (1 / 2 : ℝ) * (R.card : ℝ) ^ (5 / 8 : ℝ) ≤ (energy R χ t : ℝ) ^ (1 / 8 : ℝ) * N) →
      ∑ p ∈ pairsGt N ⌊N ^ 2 / ((q : ℝ) * T)⌋₊, ‖R2 R χ t p.1 p.2‖ ^ 3 ≤
        8 * C * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) * ((q : ℝ) * T * N) ^ ε *
            (1 + Real.log (max 1 N)) *
            (N * (R.card : ℝ) ^ 3 + N * ((q : ℝ) * T) ^ (1 / 4 : ℝ) * (R.card : ℝ) ^ (21 / 8 : ℝ) +
              (energy R χ t : ℝ) ^ (1 / 2 : ℝ) * (R.card : ℝ) ^ (1 / 2 : ℝ) * N ^ 2) +
          (dyad N).card * (R.card : ℝ) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := lemma1010 hT hε
  refine ⟨C, hC0, ?_⟩
  intro q _ ι R χ t T N hT1 hprim hinj ht hN halt
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT1
  have hN0 : 0 < N := by
    have : 0 < ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 := by positivity
    linarith
  have h := hC q R χ t T N ⌊N ^ 2 / ((q : ℝ) * T)⌋₊ hT1 hN0 hprim hinj ht
  have hr : (R.card : ℝ) = 0 ∨ 1 ≤ (R.card : ℝ) := by
    rcases Nat.eq_zero_or_pos R.card with h0 | h0
    · left; exact_mod_cast h0
    · right; exact_mod_cast h0
  have hL : 1 ≤ 1 + Real.log (max 1 N) := by have := Real.log_nonneg (le_max_left 1 N); linarith
  have hD : N ^ 2 / ((q : ℝ) * T) < (⌊N ^ 2 / ((q : ℝ) * T)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcase := case_le hr (Nat.cast_nonneg _) (energy_le_cube R χ t hinj) hQ hN hL hD halt
  have hG0 : 0 ≤ (q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1) := by positivity
  have hΛ0 : 0 ≤ ((q : ℝ) * T * N) ^ ε := by positivity
  have hk := mul_le_mul_of_nonneg_left hcase
    (by positivity : 0 ≤ C * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) * ((q : ℝ) * T * N) ^ ε)
  have e : C * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) * ((q : ℝ) * T * N) ^ ε *
      (8 * (1 + Real.log (max 1 N)) *
        (N * (R.card : ℝ) ^ 3 + N * ((q : ℝ) * T) ^ (1 / 4 : ℝ) * (R.card : ℝ) ^ (21 / 8 : ℝ) +
          (energy R χ t : ℝ) ^ (1 / 2 : ℝ) * (R.card : ℝ) ^ (1 / 2 : ℝ) * N ^ 2)) =
      8 * C * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) * ((q : ℝ) * T * N) ^ ε *
          (1 + Real.log (max 1 N)) *
          (N * (R.card : ℝ) ^ 3 + N * ((q : ℝ) * T) ^ (1 / 4 : ℝ) * (R.card : ℝ) ^ (21 / 8 : ℝ) +
            (energy R χ t : ℝ) ^ (1 / 2 : ℝ) * (R.card : ℝ) ^ (1 / 2 : ℝ) * N ^ 2) := by ring
  rw [e] at hk
  linarith

end LinnikCGLCase

#print axioms LinnikCGLCase.energy_le_cube
#print axioms LinnikCGLCase.case_le
#print axioms LinnikCGLCase.remark103
#print axioms LinnikCGLCase.lemma1010_case
