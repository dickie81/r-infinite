/-
# Round 607: a step of Huxley's bound with parameters, `7/3 + 1/2000` on `[16/21, 5/6]` (the second goal's input D3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`charDensity_hux73`). There is `C ≥ 0` such that for every `q ≥ 1`, `16/21 ≤ σ ≤ 5/6` and `T ≥ 2`,
at most `C(qT)^{(7/3+1/2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`.

This is round 589's step (`LinnikStep`) with its numbers as parameters. A `Par` holds the largest power `M`, the power
trick's target `Q^a`, the exponent `lam` of the powers' lengths, the range `[lo, hi]` of `σ`, the inner exponent `Ai`
and the exponent `A`. `Par.Good` lists what the step needs of them at the internal `ε = 1/100000` (`εs`): `M ≥ 1`,
`0 < a` and `a + ε ≤ M/2000`, the bounds on `lam`, `3/4 ≤ lo`, `hi ≤ 11/12`, `0 ≤ A ≤ 16`, and four exponent
inequalities on `[lo, hi]`, one for each term of `block_bin_hux`, one for the integral class and one for the number
of dyadic blocks. At `parHux73` (`a = 7/9 + 2ε`, `m ≤ 1556`, `lam = 7/6 + 9ε/2`, `Ai = 7/3 + 25ε`), up to powers of
`Q^ε`, for `16/21 ≤ σ ≤ 5/6`:
* the first term carries `Λ^{2−2σ}`, and `Λ ≤ Q^{7/6}`, so it is at most `Q^{(7/3)(1−σ)}`;
* the second carries `Λ^{4−6σ}Q ≤ Q^{(7/9)(4−6σ)+1}`, since `Λ ≥ Q^{7/9}` and `4 − 6σ < 0`, and
  `(7/3)(1 − σ) − ((7/9)(4 − 6σ) + 1) = 7σ/3 − 16/9`, which is `0` at `σ = 16/21`; the power trick's target
  `Q^{7/9+3ε}` closes the gap;
* the integral class carries `Q^{(201/100)(1/2−σ)+1/500+1}`, as in round 589.
At `parStep` the step is round 589's again, on `5/6 ≤ σ ≤ 11/12`.

* `choose_m_gen`, `term1_gen`, `Gm_le_gen`, `Gm3_gen`, `final2_gen`, `term2_gen`: round 589's lemmas with `M`, `a`,
  `lam` and `Ai` as arguments.
* `class1_gen`, `class2_bound_gen`: the polynomial class and the integral class.
* `eventually_gen`, `absorb_K_gen`, `count_gen_at`, `count_gen`: the range `[lo, hi]` for all large `Q`, and below.
* `charDensity_gen`: for parameters with `Good`, the density estimate with exponent `A` on `[lo, hi]`.
* `charDensity_hux73` (`parHux73`) and `charDensity_step'` (`parStep`), the latter `LinnikStep.charDensity_step`
  below `11/12`.

The file imports `LinnikTwelve.lean`.
-/
import LinnikTwelve

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

set_option exponentiation.threshold 3000

namespace LinnikHuxStep

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag LinnikHuxley LinnikReflect LinnikTwelve

variable {q : ℕ}

/-! ### The parameters -/

/-- The internal `ε`. -/
def εs : ℝ := 1 / 100000

/-- The parameters of a step of Huxley's bound: the largest power `M`, the power trick's target `Q^a`, the exponent
`lam` of the powers' lengths, the range `[lo, hi]` of `σ`, the inner exponent `Ai` and the exponent `A`. -/
structure Par where
  M : ℕ
  a : ℝ
  lam : ℝ
  lo : ℝ
  hi : ℝ
  Ai : ℝ
  A : ℝ

/-- What a step needs of its parameters, at the internal `ε = 1/100000`. -/
structure Par.Good (P : Par) : Prop where
  hM : 1 ≤ P.M
  ha : 0 < P.a
  hat : P.a + εs ≤ (P.M : ℝ) / 2000
  hlam1 : 201 / 200 + εs ≤ P.lam
  hlam2 : 3 * (P.a + εs) / 2 ≤ P.lam
  hlam3 : P.lam ≤ 2
  hlo : 3 / 4 ≤ P.lo
  hhi : P.hi ≤ 11 / 12
  h1 : ∀ σ, P.lo ≤ σ → σ ≤ P.hi → P.lam * (2 - 2 * σ + εs) + εs / 12 ≤ P.Ai * (1 - σ)
  h2 : ∀ σ, P.lo ≤ σ → σ ≤ P.hi →
    (P.a + εs) * (4 - 6 * σ + 3 * εs) + (εs / 4 + (1 + 3 / 2 * εs) + εs / 4) ≤ P.Ai * (1 - σ)
  h3 : ∀ σ, P.lo ≤ σ → σ ≤ P.hi → 201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + εs) ≤ P.A * (1 - σ)
  h4 : ∀ σ, σ ≤ P.hi → εs / (24 * P.M) + P.Ai * (1 - σ) ≤ P.A * (1 - σ)
  hA : 0 ≤ P.A
  hA16 : P.A ≤ 16

theorem εs_pos : 0 < εs := by unfold εs; norm_num

/-! ### The power of a block -/

/-- **The power of a block**: for `Q > 1`, `x ≥ Q^{1/2000}` and `0 < a ≤ M/2000` some `m` with `Q^a ≤ x^m` has
`1 ≤ m ≤ M` and `x^m ≤ max(x², Q^{3a/2})`; the proof takes the least such `m`. -/
lemma choose_m_gen (M : ℕ) {Q a x : ℝ} (hQ : 1 < Q) (ha : 0 < a) (ha1 : a ≤ (M : ℝ) / 2000)
    (hx : Q ^ (1 / 2000 : ℝ) ≤ x) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧ Q ^ a ≤ x ^ m ∧ x ^ m ≤ max (x ^ 2) (Q ^ (3 * a / 2)) := by
  classical
  have hQ0 : 0 < Q := by linarith
  have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hQ.le (by norm_num)) hx
  have hM : Q ^ a ≤ x ^ M := by
    calc Q ^ a ≤ Q ^ ((M : ℝ) / 2000) := Real.rpow_le_rpow_of_exponent_le hQ.le ha1
      _ = (Q ^ (1 / 2000 : ℝ)) ^ M := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; congr 1; ring
      _ ≤ x ^ M := pow_le_pow_left₀ (by positivity) hx M
  have hex : ∃ m : ℕ, Q ^ a ≤ x ^ m := ⟨M, hM⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex hM, Nat.find_spec hex, ?_⟩
  · by_contra h0
    have hm0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hm0, pow_zero] at this
    exact absurd this (not_le.2 (Real.one_lt_rpow hQ ha))
  · set m := Nat.find hex with hm
    rcases le_or_gt m 2 with h2 | h3
    · exact le_max_of_le_left (pow_le_pow_right₀ hx1 h2)
    · refine le_max_of_le_right ?_
      have h1 : x ^ (m - 1) < Q ^ a := not_le.1 (Nat.find_min hex (by omega : m - 1 < m))
      have h2 : x ^ 2 ≤ x ^ (m - 1) := pow_le_pow_right₀ hx1 (by omega)
      have e1 : (x ^ m) ^ 2 = (x ^ (m - 1)) ^ 2 * x ^ 2 := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
      have e2 : (Q ^ (3 * a / 2)) ^ 2 = (Q ^ a) ^ 2 * Q ^ a := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_natCast (Q ^ a), ← Real.rpow_mul hQ0.le,
          ← Real.rpow_add hQ0]
        congr 1; push_cast; ring
      have h3 : (x ^ m) ^ 2 ≤ (Q ^ (3 * a / 2)) ^ 2 := by
        rw [e1, e2]
        have hxm0 : 0 ≤ x ^ (m - 1) := by positivity
        exact mul_le_mul (pow_le_pow_left₀ hxm0 h1.le 2) (h2.trans h1.le) (by positivity) (by positivity)
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h3

/-! ### One block and one bin as a power of `Q` -/

/-- The constant of `term1_gen`. -/
def B1g (M : ℕ) (ε : ℝ) : ℝ := 16 * 2 ^ M * (4 * Cdiv (ε / (4 * M)) ^ 4) ^ M

/-- The constant of `term2_gen`. -/
def B2g (M : ℕ) (ε : ℝ) : ℝ :=
  2 ^ (2 * M + 6) * (40 * (24 * InghamDensity.KG * CG) ^ 2) * (4 * Cdiv (ε / (4 * M)) ^ 4) ^ (3 * M)

lemma B1g_nonneg (M : ℕ) (ε : ℝ) : 0 ≤ B1g M ε := by unfold B1g; positivity

lemma B2g_nonneg (M : ℕ) (ε : ℝ) : 0 ≤ B2g M ε := by unfold B2g; positivity

/-- `G_m ≥ 0`, for `0 < ε_d ≤ 1`. -/
lemma Gm_nonneg {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) (P m : ℕ) (σ : ℝ) : 0 ≤ Gm εd P m σ := by
  have hCd := one_le_Cdiv hεd hεd1
  unfold Gm
  have h1 : 0 ≤ Cdiv εd ^ (4 * m) := pow_nonneg (by linarith) _
  positivity

/-- `G_m(σ_b) ≤ (4C⁴)^M Λ^{1−2σ+ε}` for `M ≥ 1`, `0 < ε ≤ 1`, `P ≥ 1`, `m ≤ M`, `σ ≤ σ_b` and `σ ≤ 1`, with
`C = C(ε/(4M))`. -/
lemma Gm_le_gen {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {σ σb : ℝ} (hσ1 : σ ≤ 1)
    (hσb : σ ≤ σb) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ M) :
    Gm (ε / (4 * M)) P m σb ≤ (4 * Cdiv (ε / (4 * M)) ^ 4) ^ M * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 - 2 * σ + ε) := by
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hεd : 0 < ε / (4 * M) := by positivity
  have hεd1 : ε / (4 * M) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  set A : ℝ := 4 * Cdiv (ε / (4 * M)) ^ 4 with hA
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hmε : 4 * (m : ℝ) * (ε / (4 * M)) ≤ ε := by
    rw [show 4 * (m : ℝ) * (ε / (4 * M)) = ε * ((m : ℝ) / M) by field_simp]
    have : (m : ℝ) / M ≤ 1 := by rw [div_le_one (by positivity)]; exact hm'
    nlinarith
  refine (Gm_le hεd hεd1 hP m hσ1 hσb).trans ?_
  rw [← hA, ← hΛdef]
  exact mul_le_mul (pow_le_pow_right₀ hA1 hm) (Real.rpow_le_rpow_of_exponent_le hΛ1 (by linarith))
    (by positivity) (by positivity)

/-- **The first term**: for `M ≥ 1`, `0 < ε ≤ 1`, `Q ≥ 1`, `P ≥ 1` and `K ≥ 1`, with `Λ = (2P)^m ≤ Q^{lam}`, `m ≤ M`,
`4K ≤ Q^{ε/(24M)}`, `σ ≤ σ_b`, `σ ≤ 1` and `lam(2 − 2σ + ε) + ε/12 ≤ Ai(1 − σ)`:
`2c₀⁻¹G_m(σ_b)Λ(4K)^{2m} ≤ B1g(M, ε)Q^{Ai(1−σ)}`. -/
lemma term1_gen {M : ℕ} (hM : 1 ≤ M) {ε lam Ai : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {σ σb Q : ℝ} (hσ1 : σ ≤ 1)
    (hσb : σ ≤ σb) (hQ1 : 1 ≤ Q) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ M)
    (hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ lam) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : 4 * K ≤ Q ^ (ε / (24 * M))) (hexp : lam * (2 - 2 * σ + ε) + ε / 12 ≤ Ai * (1 - σ)) :
    2 * (8 * 2 ^ m) * Gm (ε / (4 * M)) P m σb * ((2 * P : ℕ) : ℝ) ^ m / ((1 / (4 * K)) ^ m) ^ 2
      ≤ B1g M ε * Q ^ (Ai * (1 - σ)) := by
  unfold B1g
  have hQ0 : 0 < Q := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  set A : ℝ := 4 * Cdiv (ε / (4 * M)) ^ 4 with hA
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hGm := Gm_le_gen hM hε hε1 hσ1 hσb hP hm
  rw [← hA, ← hΛdef] at hGm
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (m * 2) ≤ Q ^ (ε / 12) := by
    calc (4 * K) ^ (m * 2) ≤ (Q ^ (ε / (24 * M))) ^ (m * 2) := pow_le_pow_left₀ hK0.le hK _
      _ = Q ^ (ε / (24 * M) * (m * 2 : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ Q ^ (ε / 12) := by
          refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
          have hm' : (m : ℝ) ≤ M := by exact_mod_cast hm
          push_cast
          rw [show ε / (24 * M) * (m * 2) = ε / 12 * ((m : ℝ) / M) by field_simp; ring]
          have : (m : ℝ) / M ≤ 1 := by rw [div_le_one (by positivity)]; exact hm'
          nlinarith
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hm
  have hpow : Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (2 - 2 * σ + ε) := by
    conv_lhs => rw [show Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0]; ring_nf
  have hΛQ : Λ ^ (2 - 2 * σ + ε) ≤ Q ^ (lam * (2 - 2 * σ + ε)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow hΛ0.le hΛ (by linarith)
  have hMr' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hG0 : 0 ≤ Gm (ε / (4 * M)) P m σb :=
    Gm_nonneg (by positivity) (by rw [div_le_one (by positivity)]; nlinarith) P m σb
  calc 2 * (8 * 2 ^ m) * Gm (ε / (4 * M)) P m σb * Λ / ((1 / (4 * K)) ^ m) ^ 2
      = 2 * (8 * 2 ^ m) * Gm (ε / (4 * M)) P m σb * Λ * (4 * K) ^ (m * 2) := by
        rw [one_div, inv_pow, inv_pow, div_inv_eq_mul, ← pow_mul]
    _ ≤ 2 * (8 * 2 ^ M) * (A ^ M * Λ ^ (1 - 2 * σ + ε)) * Λ * Q ^ (ε / 12) := by gcongr
    _ = 16 * 2 ^ M * A ^ M * (Λ ^ (1 - 2 * σ + ε) * Λ) * Q ^ (ε / 12) := by ring
    _ = 16 * 2 ^ M * A ^ M * Λ ^ (2 - 2 * σ + ε) * Q ^ (ε / 12) := by rw [hpow]
    _ ≤ 16 * 2 ^ M * A ^ M * Q ^ (lam * (2 - 2 * σ + ε)) * Q ^ (ε / 12) := by gcongr
    _ = 16 * 2 ^ M * A ^ M * Q ^ (lam * (2 - 2 * σ + ε) + ε / 12) := by
        rw [mul_assoc _ (Q ^ _), ← Real.rpow_add hQ0]
    _ ≤ 16 * 2 ^ M * A ^ M * Q ^ (Ai * (1 - σ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 hexp) (by positivity)

/-- `G_m(σ_b)³ ≤ (4C⁴)^{3M}Λ^{3−6σ+3ε}` for `M ≥ 1`, `0 < ε ≤ 1`, `P ≥ 1`, `m ≤ M`, `σ ≤ σ_b` and `σ ≤ 1` (`Gm_le_gen`
cubed). -/
lemma Gm3_gen {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {σ σb : ℝ} (hσ1 : σ ≤ 1) (hσb : σ ≤ σb)
    {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ M) :
    Gm (ε / (4 * M)) P m σb ^ 3 ≤
      (4 * Cdiv (ε / (4 * M)) ^ 4) ^ (3 * M) * (((2 * P : ℕ) : ℝ) ^ m) ^ (3 - 6 * σ + 3 * ε) := by
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  set A : ℝ := 4 * Cdiv (ε / (4 * M)) ^ 4 with hA
  have hGm := Gm_le_gen hM hε hε1 hσ1 hσb hP hm
  rw [← hA, ← hΛdef] at hGm
  have hMr' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hG0 : 0 ≤ Gm (ε / (4 * M)) P m σb :=
    Gm_nonneg (by positivity) (by rw [div_le_one (by positivity)]; nlinarith) P m σb
  calc Gm (ε / (4 * M)) P m σb ^ 3 ≤ (A ^ M * Λ ^ (1 - 2 * σ + ε)) ^ 3 := pow_le_pow_left₀ hG0 hGm 3
    _ = A ^ (3 * M) * Λ ^ (3 - 6 * σ + 3 * ε) := by
        rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (Λ ^ (1 - 2 * σ + ε)), ← Real.rpow_mul hΛ0.le]
        rw [mul_comm M 3]; congr 2; push_cast; ring

/-- The product of the five bounds of the second term as a power of `Q`, for `Q ≥ 1`, `Λ > 0`, `C, A ≥ 0`,
`Λ^{4−6σ+3ε} ≤ Q^{aT(4−6σ+3ε)}` and the exponent condition `hexp`. -/
lemma final2_gen {M : ℕ} {Q Λ A C ε σ aT Ai : ℝ} (hQ1 : 1 ≤ Q) (hΛ0 : 0 < Λ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hΛQ : Λ ^ (4 - 6 * σ + 3 * ε) ≤ Q ^ (aT * (4 - 6 * σ + 3 * ε)))
    (hexp : aT * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) ≤ Ai * (1 - σ)) :
    2 ^ (2 * M + 6) * Q ^ (ε / 4) * (A ^ (3 * M) * Λ ^ (3 - 6 * σ + 3 * ε)) * (C * Λ * Q ^ (1 + 3 / 2 * ε)) *
        Q ^ (ε / 4) ≤ 2 ^ (2 * M + 6) * C * A ^ (3 * M) * Q ^ (Ai * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hΛpow : Λ ^ (3 - 6 * σ + 3 * ε) * Λ = Λ ^ (4 - 6 * σ + 3 * ε) := by
    conv_lhs => rw [show Λ ^ (3 - 6 * σ + 3 * ε) * Λ = Λ ^ (3 - 6 * σ + 3 * ε) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0]; ring_nf
  have eQ : Q ^ (ε / 4) * Q ^ (1 + 3 / 2 * ε) * Q ^ (ε / 4) = Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
  have hD : 0 ≤ 2 ^ (2 * M + 6) * C * A ^ (3 * M) := by positivity
  have hQe : 0 ≤ Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by positivity
  calc 2 ^ (2 * M + 6) * Q ^ (ε / 4) * (A ^ (3 * M) * Λ ^ (3 - 6 * σ + 3 * ε)) * (C * Λ * Q ^ (1 + 3 / 2 * ε)) *
        Q ^ (ε / 4)
      = (2 ^ (2 * M + 6) * C * A ^ (3 * M)) * (Λ ^ (3 - 6 * σ + 3 * ε) * Λ) *
          (Q ^ (ε / 4) * Q ^ (1 + 3 / 2 * ε) * Q ^ (ε / 4)) := by ring
    _ = (2 ^ (2 * M + 6) * C * A ^ (3 * M)) * Λ ^ (4 - 6 * σ + 3 * ε) *
          Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by rw [hΛpow, eQ]
    _ ≤ (2 ^ (2 * M + 6) * C * A ^ (3 * M)) * Q ^ (aT * (4 - 6 * σ + 3 * ε)) *
          Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛQ hD) hQe
    _ = (2 ^ (2 * M + 6) * C * A ^ (3 * M)) *
          Q ^ (aT * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4)) := by
        rw [mul_assoc, ← Real.rpow_add hQ0]
    _ ≤ 2 ^ (2 * M + 6) * C * A ^ (3 * M) * Q ^ (Ai * (1 - σ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 hexp) hD

/-- **The second term**: for `M ≥ 1`, `0 < ε ≤ 1/200`, `σ ≤ σ_b`, `σ ≤ 1`, `Q ≥ 1`, `T ≥ 0`, `q(T + 2) ≤ Q`, `P ≥ 1` and
`K ≥ 1`, with `Λ = (2P)^m ≥ Q^{aT}`, `m ≤ M`, `4K ≤ Q^{ε/(24M)}`, the far tail cut off and the sizes of `A1_sq_le`,
`c₀⁻²4^{ω(q)}G_m(σ_b)³hxA²(4K)^{6m} ≤ B2g(M, ε)Q^{Ai(1−σ)}` when `4 − 6σ + 3ε ≤ 0` and
`aT(4 − 6σ + 3ε) + ε/4 + (1 + 3ε/2) + ε/4 ≤ Ai(1 − σ)`. -/
lemma term2_gen [NeZero q] {M : ℕ} (hM : 1 ≤ M) {ε aT Ai : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {σ σb Q T τ : ℝ}
    (hσ1 : σ ≤ 1) (hσb : σ ≤ σb) (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ M) (hΛlo : Q ^ aT ≤ ((2 * P : ℕ) : ℝ) ^ m)
    (hneg : 4 - 6 * σ + 3 * ε ≤ 0)
    (hexp : aT * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) ≤ Ai * (1 - σ))
    {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ Q ^ (ε / (24 * M)))
    {X J : ℕ} (hX1 : 1 ≤ X) (hXQ : (X : ℝ) ≤ Q ^ (25 : ℝ)) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (ε / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (ε / 8)) (hL : LSmax X ≤ Q ^ (ε / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8)) (hEQ : EQ q ≤ Q ^ (ε / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (ε / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / (4 * M)) P m σb ^ 3 *
        hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) ((2 * P) ^ m : ℕ) X J ^ 2 / ((1 / (4 * K)) ^ m) ^ 6
      ≤ B2g M ε * Q ^ (Ai * (1 - σ)) := by
  unfold B2g
  have hQ0 : 0 < Q := by linarith
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ ((2 * P : ℕ) : ℝ) ^ m := one_le_pow₀ h2P
  have hΛ0 : 0 < ((2 * P : ℕ) : ℝ) ^ m := by linarith
  have hN : ((((2 * P) ^ m : ℕ)) : ℝ) = ((2 * P : ℕ) : ℝ) ^ m := by push_cast; ring
  rw [hN]
  have hεd : 0 < ε / (4 * M) := by positivity
  have hεd1 : ε / (4 * M) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hCd := one_le_Cdiv hεd hεd1
  have hA0 : 0 ≤ 4 * Cdiv (ε / (4 * M)) ^ 4 := by positivity
  have hKG := InghamDensity.KG_pos
  have hCG := CG_pos
  have hC0 : 0 ≤ 40 * (24 * InghamDensity.KG * CG) ^ 2 := by positivity
  have hH := hxA_sq_le (q := q) (τ := τ) (Λ := ((2 * P : ℕ) : ℝ) ^ m) hε hε1 hQ1 hT hqT hΛ0.le hX1 hXQ
    hτ1 hτQ hJ hL hB hEQ hfar
  have hG3 := Gm3_gen hM hε (by linarith) hσ1 hσb hP hm
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (m * 6) ≤ Q ^ (ε / 4) := by
    calc (4 * K) ^ (m * 6) ≤ (Q ^ (ε / (24 * M))) ^ (m * 6) := pow_le_pow_left₀ hK0.le hK _
      _ = Q ^ (ε / (24 * M) * (m * 6 : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ Q ^ (ε / 4) := by
          refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
          have hm' : (m : ℝ) ≤ M := by exact_mod_cast hm
          push_cast
          rw [show ε / (24 * M) * (m * 6) = ε / 4 * ((m : ℝ) / M) by field_simp; ring]
          have : (m : ℝ) / M ≤ 1 := by rw [div_le_one (by positivity)]; exact hm'
          nlinarith
  have h8 : (8 * (2 : ℝ) ^ m) ^ 2 ≤ 2 ^ (2 * M + 6) := by
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hm
    calc (8 * (2 : ℝ) ^ m) ^ 2 ≤ (8 * 2 ^ M) ^ 2 := by gcongr
      _ = 2 ^ (2 * M + 6) := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_mul]; ring_nf
  have hPs2 : (q.primeFactors.powerset.card : ℝ) ^ 2 ≤ Q ^ (ε / 4) := by
    calc (q.primeFactors.powerset.card : ℝ) ^ 2 ≤ (Q ^ (ε / 8)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hPs 2
      _ = Q ^ (ε / 4) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; ring_nf
  have hΛQ : (((2 * P : ℕ) : ℝ) ^ m) ^ (4 - 6 * σ + 3 * ε) ≤ Q ^ (aT * (4 - 6 * σ + 3 * ε)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hΛlo hneg
  have hG0 : 0 ≤ Gm (ε / (4 * M)) P m σb ^ 3 := pow_nonneg (Gm_nonneg hεd hεd1 P m σb) 3
  have hprod := prod5_le (by positivity) (by positivity) hG0 (sq_nonneg _) (by positivity) h8 hPs2 hG3 hH h4K
  have hfin := final2_gen (M := M) (A := 4 * Cdiv (ε / (4 * M)) ^ 4) hQ1 hΛ0 hC0 hA0 hΛQ hexp
  have e1 : (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / (4 * M)) P m σb ^ 3 *
      hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) (((2 * P : ℕ) : ℝ) ^ m) X J ^ 2 / ((1 / (4 * K)) ^ m) ^ 6 =
      (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / (4 * M)) P m σb ^ 3 *
      hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) (((2 * P : ℕ) : ℝ) ^ m) X J ^ 2 * (4 * K) ^ (m * 6) := by
    rw [one_div, inv_pow, inv_pow, div_inv_eq_mul, ← pow_mul]
  rw [e1]
  exact hprod.trans hfin

/-! ### The polynomial class and the integral class -/

/-- **The polynomial class with Huxley's estimate on `[lo, hi]`.** Let the parameters have `Good`, `lo ≤ σ ≤ hi`,
`T ≥ 0`, `Q > 1` with `q(T + 2) ≤ Q`, `X, N ≥ 1`, and the large-sieve range `X_l`, `J` and `τ` with the size conditions
its hypotheses list (`hK` … `hfar`). Characters with one point `β_χ + iγ_χ` each, `σ ≤ β_χ < 1`, `|γ_χ| ≤ T`, and
`|P_χ(β_χ + iγ_χ)| ≥ ¼` number at most `(⌊50/ε⌋ + 1)K(B₁ + B₂)Q^{Ai(1−σ)}`, `K = ⌊log₂ N⌋ + 1`, `ε = εs`, for
`Q^{1/2000} ≤ 2X` and `(2XN)² ≤ Q^{201/200+ε}`: some dyadic block is at least `1/(4K)`; bins of width `ε/200` in `β`; in
each block and bin a power `m ≤ M` with `(2P)^m ≥ Q^{a+ε}` (`choose_m_gen`), at most `Q^{lam}` long, and `block_bin_hux`
with `term1_gen` and `term2_gen`. -/
theorem class1_gen [NeZero q] (Pa : Par) (G : Pa.Good)
    {σ T Q : ℝ} (hσ : Pa.lo ≤ σ) (hσ1 : σ ≤ Pa.hi) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXQ : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (εs / (24 * Pa.M)))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + εs))
    {Xl J : ℕ} {τ : ℝ} (hXl1 : 1 ≤ Xl) (hXlQ : (Xl : ℝ) ≤ Q ^ (25 : ℝ))
    (hXl : Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Xl)
    (hτd : ∀ n, n ≤ Xl → (n.divisors.card : ℝ) ≤ τ) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (εs / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (εs / 8)) (hL : LSmax Xl ≤ Q ^ (εs / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (εs / 8)) (hEQ : EQ q ≤ Q ^ (εs / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (εs / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1)
    {Y : ℝ} (hY : 0 < Y) (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ < 1) (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T)
    (hbig : ∀ χ ∈ Rs, 1 / 4 ≤ ‖Pvχ χ X N Y (β χ) (γ χ)‖) :
    (Rs.card : ℝ) ≤ ((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * ((B1g Pa.M εs + B2g Pa.M εs) *
      Q ^ (Pa.Ai * (1 - σ))) := by
  classical
  have hε := εs_pos
  have hε1 : εs ≤ 1 / 100000 := le_refl _
  have hQ0 : 0 < Q := by linarith
  have hlo := G.hlo
  have hhi := G.hhi
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set nb := ⌊50 / εs⌋₊ + 1 with hnb
  set Bb := (B1g Pa.M εs + B2g Pa.M εs) * Q ^ (Pa.Ai * (1 - σ)) with hBb
  -- some block of each character is at least `V`
  have hlarge : ∀ χ ∈ Rs, ∃ k ∈ range K, V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ := by
    intro χ hχ
    by_contra hcon
    push Not at hcon
    have h1 := hbig χ hχ
    rw [Pvχ_eq_blocks χ X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkχ χ X N Y k (β χ) (γ χ)‖ < ∑ _k ∈ range K, V :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * V = 1 / 4 := by rw [hV]; field_simp
    linarith [(norm_sum_le (range K) fun k => Fkχ χ X N Y k (β χ) (γ χ)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → ℕ → Finset (DirichletCharacter ℂ q) := fun k j =>
    Rs.filter fun χ => V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ ∧ ⌊200 / εs * (β χ - σ)⌋₊ = j with hCkdef
  have hsub : Rs ⊆ (range K).biUnion fun k => (range nb).biUnion fun j => Ck k j := by
    intro χ hχ
    obtain ⟨k, hk, hbigk⟩ := hlarge χ hχ
    have h1 := hβ χ hχ
    have hj : ⌊200 / εs * (β χ - σ)⌋₊ < nb := by
      have hle : 200 / εs * (β χ - σ) ≤ 50 / εs := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]; linarith
      exact Nat.lt_succ_of_le (Nat.floor_le_floor hle)
    exact mem_biUnion.2 ⟨k, hk, mem_biUnion.2 ⟨_, mem_range.2 hj, mem_filter.2 ⟨hχ, hbigk, rfl⟩⟩⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqQ : (q : ℝ) ≤ Q := (le_mul_of_one_le_right hq0 (by linarith : (1 : ℝ) ≤ T + 2)).trans hqT
  have hq2T : (q : ℝ) * (1 + 2 * T) ≤ 2 * Q := by
    have : (q : ℝ) * (1 + 2 * T) ≤ q * (2 * (T + 2)) := mul_le_mul_of_nonneg_left (by linarith) hq0
    linarith
  have hCk : ∀ k ∈ range K, ∀ j ∈ range nb, ((Ck k j).card : ℝ) ≤ Bb := by
    intro k hk j _
    set P := 2 ^ k * X with hPdef
    have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ X * N := by
      rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le (mem_range.1 hk) hN)
    have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
    have hSsub : (Ioc X (X * N)).filter (fun j => blk X j = k) ⊆ Ioc P (2 * P) := block_sub hX
    have h2Px : Q ^ (1 / 2000 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
      have : (2 * (X : ℝ)) ≤ ((2 * P : ℕ) : ℝ) := by
        have h := (by omega : 2 * X ≤ 2 * P)
        have h' : ((2 * X : ℕ) : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h' ⊢; linarith
      linarith
    obtain ⟨m, hm1, hmM, hΛlo, hΛhi⟩ :=
      choose_m_gen Pa.M hQ1 (by linarith [G.ha] : (0 : ℝ) < Pa.a + εs) G.hat h2Px
    have hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ Pa.lam := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ Q ^ (201 / 200 + εs) := hXN
          _ ≤ Q ^ Pa.lam := Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam1
      · exact Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam2
    have hΛ2 : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ 2 := by
      calc ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ Pa.lam := hΛ
        _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam3
        _ = Q ^ 2 := by norm_num
    set σb : ℝ := σ + j * (εs / 200) with hσb
    have hσσb : σ ≤ σb := by
      have : (0 : ℝ) ≤ (j : ℝ) * (εs / 200) := by positivity
      rw [hσb]; linarith
    have hbin : ∀ χ ∈ Ck k j, σb ≤ β χ ∧ β χ ≤ σb + εs / 200 := by
      intro χ hχ
      obtain ⟨hχR, -, hbj⟩ := mem_filter.1 hχ
      have h0 : 0 ≤ 200 / εs * (β χ - σ) := by
        have h5 := (hβ χ hχR).1
        have h6 : 0 ≤ β χ - σ := by linarith
        positivity
      have h1 : ((⌊200 / εs * (β χ - σ)⌋₊ : ℕ) : ℝ) ≤ 200 / εs * (β χ - σ) := Nat.floor_le h0
      have h2 : 200 / εs * (β χ - σ) < ((⌊200 / εs * (β χ - σ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hbj] at h1 h2
      constructor
      · have h3 : (j : ℝ) * (εs / 200) ≤ β χ - σ := by
          calc (j : ℝ) * (εs / 200) ≤ (200 / εs * (β χ - σ)) * (εs / 200) := by gcongr
            _ = β χ - σ := by field_simp
        rw [hσb]; linarith
      · have h3 : β χ - σ ≤ ((j : ℝ) + 1) * (εs / 200) := by
          have h4 : 200 / εs * (β χ - σ) ≤ (j : ℝ) + 1 := h2.le
          calc β χ - σ = (200 / εs * (β χ - σ)) * (εs / 200) := by field_simp
            _ ≤ ((j : ℝ) + 1) * (εs / 200) := by gcongr
        rw [hσb]; linarith
    have hXD : (((2 * P) ^ m : ℕ) : ℝ) * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J ≤ Xl := by
      have e : (((2 * P) ^ m : ℕ) : ℝ) = ((2 * P : ℕ) : ℝ) ^ m := by push_cast; ring
      rw [e]
      have h1 : 2 * ((q : ℝ) * (1 + 2 * T)) * q + 1 ≤ 4 * Q ^ 2 + 1 := by
        have h1' : (q : ℝ) * (1 + 2 * T) * q ≤ 2 * Q * Q := mul_le_mul hq2T hqQ hq0 (by linarith)
        have hsq : Q ^ 2 = Q * Q := sq Q
        linarith
      have h0 : 0 ≤ 2 * ((q : ℝ) * (1 + 2 * T)) * q + 1 := by positivity
      calc ((2 * P : ℕ) : ℝ) ^ m * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J
          ≤ Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J := by gcongr
        _ ≤ Xl := hXl
    have hMr : (1 : ℝ) ≤ Pa.M := by exact_mod_cast G.hM
    have hcount := block_bin_hux (q := q) (R := Ck k j) hP hSsub (c := b1 X Y) (fun i _ => norm_b1_le X hY i) hm1
      (σb := σb) (η := εs / 200) (by linarith) (by linarith) β γ hbin hT
      (fun χ hχ => hγ χ (mem_filter.1 hχ).1) hV0
      (fun χ hχ => by rw [← Fkχ_eq_pv]; exact (mem_filter.1 hχ).2.1) (εd := εs / (4 * Pa.M)) (by positivity)
      (by rw [div_le_one (by positivity)]; linarith) J hXl1 hXD hτd
    have ht1 := term1_gen G.hM hε (by linarith) (by linarith) hσσb hQ1.le hP hmM hΛ hK1 hK
      (G.h1 σ hσ hσ1)
    have ht2 := term2_gen (q := q) G.hM hε (by linarith) (by linarith) hσσb hQ1.le hT hqT hP hmM hΛlo
      (by linarith) (G.h2 σ hσ hσ1) hK1 hK hXl1 hXlQ hτ1 hτQ hJ hL hB hEQ hPs hfar
    refine hcount.trans ?_
    rw [hBb, add_mul]
    exact add_le_add ht1 ht2
  calc (Rs.card : ℝ) ≤ ((range K).biUnion fun k => (range nb).biUnion fun j => Ck k j).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, (((range nb).biUnion fun j => Ck k j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range nb, ((Ck k j).card : ℝ) := by
        gcongr with k hk; exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range nb, Bb := by
        gcongr with k hk j hj; exact hCk k hk j hj
    _ = (nb : ℝ) * (K : ℝ) * Bb := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- **The integral class as a power of `Q`**: for `ε > 0`, `C₄ ≥ 0`, `Q ≥ 1` and `T ≥ 0`, with `Y = Q^{201/400}`,
`X ≤ Q^{1/2000}`, `q(T + 2) ≤ Q` and `δ = 1/4`, `27A⁴X⁴M₂ ≤ 27(4KG)⁴C₄Q^{A(1−σ)}` when
`(201/100)(1/2 − σ) + 1/500 + 1 + ε ≤ A(1 − σ)`. -/
lemma class2_bound_gen {ε C₄ A : ℝ} (hε : 0 < ε) (hC₄ : 0 ≤ C₄) {σ T Q : ℝ}
    (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) {X : ℕ} (hXQ : (X : ℝ) ≤ Q ^ (1 / 2000 : ℝ))
    (hexp : 201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + ε) ≤ A * (1 - σ)) :
    27 * (KG * (Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (A * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hY : ((Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = Q ^ (201 / 100 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ Q ^ (1 / 500 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (Q ^ (1 / 2000 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXQ 4
      _ = Q ^ (1 / 500 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
  have hM : ((q : ℝ) * (T + 2)) ^ (1 + ε) ≤ Q ^ (1 + ε) := Real.rpow_le_rpow (by positivity) hqT (by linarith)
  calc 27 * (KG * (Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 *
        (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      = 27 * (4 * KG) ^ 4 * C₄ * (((Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 *
          ((q : ℝ) * (T + 2)) ^ (1 + ε)) := by ring
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * (Q ^ (201 / 100 * (1 / 2 - σ)) * Q ^ (1 / 500 : ℝ) * Q ^ (1 + ε)) := by
        rw [hY]; gcongr
    _ = 27 * (4 * KG) ^ 4 * C₄ * Q ^ (201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + ε)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (A * (1 - σ)) := by
        gcongr

/-! ### Large `Q` -/

/-- For `M_p ≥ 1`, `ε > 0` and `M ≥ 1`, the conditions on `Q` used by a step hold for all large `Q` (`ev_log_pow`); as
`LinnikStep.eventually_step`, with `4K ≤ Q^{ε/(24M)}`. -/
lemma eventually_gen (Mp : ℕ) (hMp : 1 ≤ Mp) {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM : 1 ≤ M) :
    ∀ᶠ Q : ℝ in atTop, (8 : ℝ) ^ 2000 ≤ Q ∧ 4 * (1 + 2 * Real.log Q) ≤ Q ^ (ε / (24 * Mp)) ∧
      (2 * (23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)))) ^ 2 ≤ Q ^ (201 / 200 + ε) ∧
      23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)) ≤ Q ∧ Cdiv (ε / 200) ≤ Q ^ (ε / 8) ∧
      16 * (2 * Real.log (4 * M * Q) + 1) + 2 ≤ Q ^ (ε / 8) ∧ (8 * M * Q) ^ 16 ≤ Q ^ 20 ∧
      8 * Real.exp 1 * 25 * 627 * 50 * (1 + Real.log Q) ^ 4 ≤ Q ^ (ε / 8) ∧
      2 * Real.log (4 * Q) + 1 ≤ Q ^ (ε / 8) ∧ CEQ ε ≤ Q ^ (ε / 16) ∧ Cdiv (ε / 16) ≤ Q ^ (ε / 16) := by
  have hlM : 0 ≤ Real.log (4 * M) := Real.log_nonneg (by linarith)
  have hMp' : (0 : ℝ) < Mp := by exact_mod_cast hMp
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 2000), ev_log_pow 8 (ε / (24 * Mp)) 1 (by positivity),
    ev_log_pow ((4623 / 200) ^ 2) ε 2 hε, ev_log_pow (4623 / 400) (199 / 400) 1 (by norm_num),
    ev_log_pow (Cdiv (ε / 200)) (ε / 8) 0 (by positivity),
    ev_log_pow (32 * Real.log (4 * M) + 50) (ε / 8) 1 (by positivity),
    ev_log_pow ((8 * M) ^ 16) 4 0 (by norm_num),
    ev_log_pow (8 * Real.exp 1 * 25 * 627 * 50) (ε / 8) 4 (by positivity),
    ev_log_pow (2 * Real.log 4 + 3) (ε / 8) 1 (by positivity),
    ev_log_pow (CEQ ε) (ε / 16) 0 (by positivity), ev_log_pow (Cdiv (ε / 16)) (ε / 16) 0 (by positivity)]
    with Q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have hQ1 : 1 ≤ Q := le_trans (by norm_num) h1
  have hQ0 : 0 < Q := by linarith
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlog : Real.log (Q ^ (201 / 400 : ℝ)) = 201 / 400 * Real.log Q := Real.log_rpow hQ0 _
  simp only [pow_zero, mul_one, pow_one] at h2 h4 h5 h6 h7 h9 h10 h11
  refine ⟨h1, ?_, ?_, ?_, h5, ?_, ?_, h8, ?_, h10, h11⟩
  · linarith
  · have hQY : (Q ^ (201 / 400 : ℝ)) ^ 2 = Q ^ (201 / 200 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
    calc (2 * (23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)))) ^ 2
        = (4623 / 200) ^ 2 * Real.log Q ^ 2 * (Q ^ (201 / 400 : ℝ)) ^ 2 := by rw [hlog]; ring
      _ ≤ (4623 / 200) ^ 2 * (1 + Real.log Q) ^ 2 * Q ^ (201 / 200 : ℝ) := by
          rw [hQY]; gcongr; linarith
      _ ≤ Q ^ ε * Q ^ (201 / 200 : ℝ) := by gcongr
      _ = Q ^ (201 / 200 + ε) := by rw [← Real.rpow_add hQ0]; ring_nf
  · calc 23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)) =
          4623 / 400 * Real.log Q * Q ^ (201 / 400 : ℝ) := by rw [hlog]; ring
      _ ≤ 4623 / 400 * (1 + Real.log Q) * Q ^ (201 / 400 : ℝ) := by gcongr; linarith
      _ ≤ Q ^ (199 / 400 : ℝ) * Q ^ (201 / 400 : ℝ) := by gcongr
      _ = Q := by rw [← Real.rpow_add hQ0]; norm_num
  · have e : Real.log (4 * M * Q) = Real.log (4 * M) + Real.log Q := Real.log_mul (by positivity) hQ0.ne'
    rw [e]
    nlinarith
  · have e4 : Q ^ (4 : ℝ) = Q ^ 4 := by norm_num
    rw [e4] at h7
    calc (8 * M * Q) ^ 16 = (8 * M) ^ 16 * Q ^ 16 := by ring
      _ ≤ Q ^ 4 * Q ^ 16 := by gcongr
      _ = Q ^ 20 := by ring
  · have e : Real.log (4 * Q) = Real.log 4 + Real.log Q := Real.log_mul (by norm_num) hQ0.ne'
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [e]
    nlinarith

/-- The number `K ≤ Q^{ε/(24M)}/4` of dyadic blocks absorbed into the exponent, for `Q ≥ 1` and `n_b, B, K ≥ 0`, when
`ε/(24M) + Ai(1 − σ) ≤ A(1 − σ)`. -/
lemma absorb_K_gen {Mp : ℕ} {ε σ Q nb B K c Ai A : ℝ} (hQ1 : 1 ≤ Q)
    (hnb : 0 ≤ nb) (hB : 0 ≤ B) (hK0 : 0 ≤ K) (hK : 4 * K ≤ Q ^ (ε / (24 * Mp)))
    (hexp : ε / (24 * Mp) + Ai * (1 - σ) ≤ A * (1 - σ))
    (hc : c ≤ nb * K * (B * Q ^ (Ai * (1 - σ)))) :
    c ≤ nb * B * Q ^ (A * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKle : K ≤ Q ^ (ε / (24 * Mp)) := by have := Real.rpow_nonneg hQ0.le (ε / (24 * Mp)); linarith
  have hE1 : Q ^ (ε / (24 * Mp)) * Q ^ (Ai * (1 - σ)) ≤ Q ^ (A * (1 - σ)) := by
    rw [← Real.rpow_add hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hP0 : 0 ≤ Q ^ (Ai * (1 - σ)) := by positivity
  calc c ≤ nb * K * (B * Q ^ (Ai * (1 - σ))) := hc
    _ ≤ nb * Q ^ (ε / (24 * Mp)) * (B * Q ^ (Ai * (1 - σ))) := by gcongr
    _ = nb * B * (Q ^ (ε / (24 * Mp)) * Q ^ (Ai * (1 - σ))) := by ring
    _ ≤ nb * B * Q ^ (A * (1 - σ)) := by gcongr

open scoped Classical in
/-- **The range `[lo, hi]` at one large `Q`.** Let the parameters have `Good`, let the fourth moment hold with a
constant `C₄ ≥ 0` (`h4`), and let `lo ≤ σ ≤ hi`, `T ≥ 0` and `Q > 1` with `q(T + 2) ≤ Q`. With the detector's `X, N, Y`
(`X, N ≥ 1`, `Y ≥ 8`, `22Y log Y ≤ XN`, `Y = Q^{201/400}`, `Q^{1/2000} ≤ 2X`, `X ≤ Q^{1/2000}`), the large-sieve range
`X_l`, `J` and `τ` of `class1_gen`, at most `(⌊50/ε⌋ + 1)(B₁ + B₂)Q^E + 27(4KG)⁴C₄Q^E` characters `χ ≠ 1` mod `q` have a
zero in `Re s ≥ σ`, `|Im s| ≤ T`, `E = A(1 − σ)`, `ε = εs`: `LinnikDetect.dichotomy`, `class1_gen`, `class2_count_small`
and `class2_bound_gen`. -/
theorem count_gen_at [NeZero q] (Pa : Par) (G : Pa.Good) {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + εs))
    {σ T Q : ℝ} (hσ : Pa.lo ≤ σ) (hσ1 : σ ≤ Pa.hi) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hY8 : 8 ≤ Y) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hYQ : Y = Q ^ (201 / 400 : ℝ)) (hXU : (X : ℝ) ≤ Q ^ (1 / 2000 : ℝ)) (hXU2 : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (εs / (24 * Pa.M)))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + εs))
    {Xl J : ℕ} {τ : ℝ} (hXl1 : 1 ≤ Xl) (hXlQ : (Xl : ℝ) ≤ Q ^ (25 : ℝ))
    (hXl : Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Xl)
    (hτd : ∀ n, n ≤ Xl → (n.divisors.card : ℝ) ≤ τ) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (εs / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (εs / 8)) (hL : LSmax Xl ≤ Q ^ (εs / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (εs / 8)) (hEQ : EQ q ≤ Q ^ (εs / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (εs / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ (((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * (B1g Pa.M εs + B2g Pa.M εs) + 27 * (4 * KG) ^ 4 * C₄) *
        Q ^ (Pa.A * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hε := εs_pos
  have hε1 : εs ≤ 1 / 100000 := le_refl _
  have hlo := G.hlo
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset (DirichletCharacter ℂ q), Z = univ.filter fun χ : DirichletCharacter ℂ q =>
      χ ≠ 1 ∧ ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := ⟨_, rfl⟩
  rw [← hZ]
  have hch : ∀ χ ∈ Z, ∃ s : ℂ, χ ≠ 1 ∧ σ ≤ s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
    intro χ hχ
    rw [hZ] at hχ
    obtain ⟨hχ1, s, hs1, hs2, hs3⟩ := (mem_filter.1 hχ).2
    refine ⟨s, hχ1, hs1, ?_, hs2, hs3⟩
    by_contra hge
    push Not at hge
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hge hs3
  choose! s0 hs0 using hch
  have hz0 : ∀ χ ∈ Z, LFunction χ (((s0 χ).re : ℂ) + (s0 χ).im * I) = 0 := fun χ hχ => by
    rw [Complex.re_add_im]; exact (hs0 χ hχ).2.2.2.2
  have hdich : ∀ χ ∈ Z, 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖
      ∨ 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := by
    intro χ hχ
    obtain ⟨hχ1, h1, h2, _, _⟩ := hs0 χ hχ
    exact dichotomy hχ1 hX hN hY8 hM (by linarith) h2 (hz0 χ hχ)
  obtain ⟨Z1, hZ1⟩ : ∃ Z1 : Finset (DirichletCharacter ℂ q),
      Z1 = Z.filter fun χ => 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖ := ⟨_, rfl⟩
  obtain ⟨Z2, hZ2⟩ : ∃ Z2 : Finset (DirichletCharacter ℂ q),
      Z2 = Z.filter fun χ => 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := ⟨_, rfl⟩
  have hcover : Z ⊆ Z1 ∪ Z2 := by
    intro χ hχ
    rcases hdich χ hχ with h | h
    · exact mem_union_left _ (hZ1 ▸ mem_filter.2 ⟨hχ, h⟩)
    · exact mem_union_right _ (hZ2 ▸ mem_filter.2 ⟨hχ, h⟩)
  have hm1 : ∀ χ ∈ Z1, χ ∈ Z ∧ 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖ := fun χ hχ => by
    rw [hZ1] at hχ; exact mem_filter.1 hχ
  have hm2 : ∀ χ ∈ Z2, χ ∈ Z ∧ 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := fun χ hχ => by
    rw [hZ2] at hχ; exact mem_filter.1 hχ
  have hc1 := class1_gen Pa G hσ hσ1 hT hQ1 hqT hX hN hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hB hEQ
    hPs hfar (by linarith : (0 : ℝ) < Y) Z1 (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => ⟨(hs0 χ (hm1 χ hχ).1).2.1, (hs0 χ (hm1 χ hχ).1).2.2.1⟩)
    (fun χ hχ => (hs0 χ (hm1 χ hχ).1).2.2.2.1)
    (fun χ hχ => (hm1 χ hχ).2)
  have hc2 := class2_count_small hε.le (by linarith) hC₄0 h4 hX (δ := 1 / 4) (by norm_num)
    (by linarith : 1 / 2 + 1 / 4 ≤ σ) hT (by linarith : (1 : ℝ) ≤ Y) Z2
    (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => by
      obtain ⟨hχ1, h1, h2, h3, _⟩ := hs0 χ (hm2 χ hχ).1
      exact ⟨hχ1, h1, h2, h3, hz0 χ (hm2 χ hχ).1, (hm2 χ hχ).2⟩)
  have hb2 := class2_bound_gen (q := q) (σ := σ) (A := Pa.A) hε hC₄0 hQ1.le hT hqT (X := X) hXU
    (G.h3 σ hσ hσ1)
  rw [hYQ] at hc2
  have hI := absorb_K_gen (Mp := Pa.M) (A := Pa.A) hQ1.le (by positivity)
    (add_nonneg (B1g_nonneg Pa.M εs) (B2g_nonneg Pa.M εs)) (Nat.cast_nonneg _) hK (G.h4 σ hσ1) hc1
  have hII : (Z2.card : ℝ) ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (Pa.A * (1 - σ)) := hc2.trans hb2
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card := by exact_mod_cast card_union_le Z1 Z2
    _ ≤ ((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * (B1g Pa.M εs + B2g Pa.M εs) * Q ^ (Pa.A * (1 - σ)) +
          27 * (4 * KG) ^ 4 * C₄ * Q ^ (Pa.A * (1 - σ)) := add_le_add hI hII
    _ = (((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * (B1g Pa.M εs + B2g Pa.M εs) + 27 * (4 * KG) ^ 4 * C₄) *
          Q ^ (Pa.A * (1 - σ)) := by ring

/-- For `Q > 0`, `Y = Q^{201/400}` for the detector at `U = Q^{1/2000}`, `c = 502`. -/
lemma Yw_gen {Q : ℝ} (hQ0 : 0 < Q) : Yw 502 (Q ^ (1 / 2000 : ℝ)) = Q ^ (201 / 400 : ℝ) := by
  unfold Yw; rw [← Real.rpow_mul hQ0.le]; norm_num

open scoped Classical in
/-- **The range `[lo, hi]`.** For parameters with `Good`, there is `C ≥ 0` such that for every `q ≥ 1`, `lo ≤ σ ≤ hi`
and `T ≥ 2` at most `C Q^{A(1−σ)}`, `Q = q(T + 6)`, characters `χ ≠ 1` mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. For `Q ≥ Q₀` (`eventually_gen`), `count_gen_at` at the detector `X = ⌊Q^{1/2000}⌋`, `Y = Q^{201/400}` and
the large-sieve range of `sieve_range`; below `Q₀` at most `q ≤ Q₀` characters are counted. -/
theorem count_gen (Pa : Par) (G : Pa.Good) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), Pa.lo ≤ σ → σ ≤ Pa.hi → 2 ≤ T →
      ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ C * ((q : ℝ) * (T + 6)) ^ (Pa.A * (1 - σ)) := by
  have hε := εs_pos
  have hε1 : εs ≤ 1 / 100000 := le_refl _
  have hε200 : εs ≤ 1 / 200 := by linarith
  obtain ⟨C₄', hC₄'⟩ := LinnikFourth.fourth_moment hε (by linarith : εs ≤ 1)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = max C₄' 0 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := hC₄ ▸ le_max_right _ _
  have h4all : ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) →
      ∀ T' : ℝ, 0 ≤ T' → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + εs) := by
    intro q _ R hR T' hT' t ht
    refine (hC₄' q R hR T' hT' t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₄ ▸ le_max_left _ _) (by positivity)
  have hM1 : (1 : ℝ) ≤ max zeta98 1 := le_max_right _ _
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (eventually_gen Pa.M G.hM hε hM1)
  have hKG := KG_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ,
      B = ((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * (B1g Pa.M εs + B2g Pa.M εs) + 27 * (4 * KG) ^ 4 * C₄ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; have := B1g_nonneg Pa.M εs; have := B2g_nonneg Pa.M εs; positivity
  refine ⟨max Q₀ 0 + B, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hlo := G.hlo
  have hhi := G.hhi
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) * (T + 6) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ8 : 8 ≤ Q := by
    rw [hQ]
    calc (8 : ℝ) = 1 * 8 := by norm_num
      _ ≤ (q : ℝ) * (T + 6) := mul_le_mul hq1 (by linarith) (by norm_num) (by positivity)
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Pa.A * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg G.hA (by linarith)
  have hQE : 1 ≤ Q ^ E := Real.one_le_rpow hQ1 hE0
  rcases lt_or_ge Q Q₀ with hsmall | hlarge
  · have hBQ : 0 ≤ B * Q ^ E := by positivity
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ max Q₀ 0 := hsmall.le.trans (le_max_left _ _)
      _ ≤ max Q₀ 0 * Q ^ E := le_mul_of_one_le_right (le_max_right _ _) hQE
      _ ≤ (max Q₀ 0 + B) * Q ^ E := by rw [add_mul]; linarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hQ₀ Q hlarge
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Q ^ (1 / 2000 : ℝ) := ⟨_, rfl⟩
  have hU8 : 8 ≤ U := by
    rw [hU]
    calc (8 : ℝ) = ((8 : ℝ) ^ 2000) ^ (1 / 2000 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ Q ^ (1 / 2000 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hYQ : Yw 502 U = Q ^ (201 / 400 : ℝ) := by rw [hU]; exact Yw_gen hQ0
  have hX : 1 ≤ Xw U := Xw_one hU8
  have hN : 1 ≤ Nw 502 U := Nw_one
  have hY8 : 8 ≤ Yw 502 U := le_trans hU8 (Yw_ge (by norm_num) hU8)
  have hM : 22 * Yw 502 U * Real.log (Yw 502 U) ≤ ((Xw U * Nw 502 U : ℕ) : ℝ) := XN_ge hU8
  have hXNle : ((Xw U * Nw 502 U : ℕ) : ℝ) ≤ 23 * Yw 502 U * Real.log (Yw 502 U) := XN_le (by norm_num) hU8
  have hXU : (Xw U : ℝ) ≤ Q ^ (1 / 2000 : ℝ) := hU ▸ Xw_le hU8
  have hXU2 : Q ^ (1 / 2000 : ℝ) ≤ 2 * (Xw U : ℝ) := by have := Xw_half hU8; rw [← hU]; linarith
  have hXr : (1 : ℝ) ≤ Xw U := by exact_mod_cast hX
  have hNQ : (Nw 502 U : ℝ) ≤ Q := by
    have h1 : (Nw 502 U : ℝ) ≤ ((Xw U * Nw 502 U : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    rw [hYQ] at hXNle
    linarith
  have hK : 4 * ((Nat.log 2 (Nw 502 U) + 1 : ℕ) : ℝ) ≤ Q ^ (εs / (24 * Pa.M)) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNQ) (by norm_num)).trans h2
  have hXN : (2 * ((Xw U * Nw 502 U : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + εs) := by
    refine le_trans ?_ h3
    rw [← hYQ]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hqT : (q : ℝ) * (T + 2) ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  have h1' : (8 : ℝ) ^ 25 ≤ Q := le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) h1
  obtain ⟨Xl, J, τ, hXl1, hXlQ, hXl, hτd, hτ1, hτQ, hJ, hL, hfar⟩ :=
    sieve_range (q := q) hε hε200 (by linarith : (0 : ℝ) ≤ T) h1' hqT h5 h6 h7 h8
  have hBk := bkt_le_Q (q := q) (ε := εs) (by linarith : (0 : ℝ) ≤ T) hqT h9
  have hEQ := EQ_le_Q (q := q) hε hQ1 hqQ h10
  have hPs := powerset_le_Q (q := q) hε hε200 hQ1 hqQ h11
  have hcount := count_gen_at (q := q) Pa G hC₄0 (h4all q) (σ := σ) (T := T) (Q := Q) hσ hσ1 (by linarith)
    (by linarith) hqT hX hN hY8 hM hYQ hXU hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hBk hEQ hPs hfar
  rw [← hE, ← hB] at hcount
  calc _ ≤ B * Q ^ E := hcount
    _ ≤ (max Q₀ 0 + B) * Q ^ E := by
        have : 0 ≤ max Q₀ 0 * Q ^ E := by positivity
        rw [add_mul]; linarith

open scoped Classical in
/-- **A density estimate over the characters mod `q` with exponent `A` on `[lo, hi]`**: for parameters with `Good`,
there is `C ≥ 0` such that for every `q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2` at most `C(qT)^{A(1−σ)}(log qT)^{10}` characters
mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`: `count_gen` measured at `Q = q(T + 6) ≤ 4qT`, plus the
trivial character. -/
theorem charDensity_gen (Pa : Par) (G : Pa.Good) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), Pa.lo ≤ σ → σ ≤ Pa.hi → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (Pa.A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  obtain ⟨CT, hCT0, hCT⟩ := count_gen Pa G
  refine ⟨2 ^ 10 + 256 * 2 ^ 10 * CT, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hlo := G.hlo
  have hhi := G.hhi
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((q : ℝ) * T) := ⟨_, rfl⟩
  rw [← hℓdef]
  have hℓ : 1 / 2 ≤ ℓ := hℓdef ▸ half_le_log hqT
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Pa.A * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg G.hA (by linarith)
  have hE4 : E ≤ 4 := by
    rw [hE]
    have h1 : 1 - σ ≤ 1 / 4 := by linarith
    have h2 := G.hA16
    nlinarith [G.hA]
  have hpowE : 0 ≤ ((q : ℝ) * T) ^ E := by positivity
  have hpowE1 : 1 ≤ ((q : ℝ) * T) ^ E := Real.one_le_rpow (by linarith) hE0
  have e10 : ℓ ^ (10 : ℝ) = ℓ ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e10]
  have h2ℓ : 1 ≤ 2 ^ 10 * ℓ ^ 10 := by
    have h1 : 1 ≤ (2 * ℓ) ^ 10 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) ≤ (2 * ℓ) ^ 10 := h1
      _ = 2 ^ 10 * ℓ ^ 10 := by ring
  have hℓ10 : 0 ≤ ℓ ^ 10 := by positivity
  have hsub : (univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
      ⊆ insert 1 (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) := by
    intro χ hχ
    rw [mem_insert]
    by_cases h1 : χ = 1
    · exact Or.inl h1
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, h1, (mem_filter.1 hχ).2⟩)
  have hcard := (card_le_card hsub).trans (card_insert_le _ _)
  have hF : ((univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) + 1 := by exact_mod_cast hcard
  have h1 : 1 ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := one_le_mul_of_one_le_of_one_le hpowE1 h2ℓ
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 256 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by positivity) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (4 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 256 * ((q : ℝ) * T) ^ E := by norm_num
  have hZ := hCT q σ T hσ hσ1 hT
  rw [← hE] at hZ
  have hstep : CT * ((q : ℝ) * (T + 6)) ^ E ≤ 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by
    calc CT * ((q : ℝ) * (T + 6)) ^ E ≤ CT * (256 * ((q : ℝ) * T) ^ E) := by gcongr
      _ = 256 * CT * ((q : ℝ) * T) ^ E * 1 := by ring
      _ ≤ 256 * CT * ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) :=
          mul_le_mul_of_nonneg_left h2ℓ (by positivity)
      _ = 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
  calc _ ≤ _ := hF
    _ ≤ CT * ((q : ℝ) * (T + 6)) ^ E + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
    _ ≤ (2 ^ 10 + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith

/-! ### Two steps -/

/-- The parameters of round 589's step: `101/50` on `[5/6, 11/12]` (`LinnikStep.charDensity_step`). -/
def parStep : Par where
  M := 1334
  a := 2 / 3
  lam := 201 / 200 + 3 / 2 * εs
  lo := 5 / 6
  hi := 11 / 12
  Ai := 2019 / 1000
  A := 101 / 50

theorem parStep_good : parStep.Good where
  hM := by simp [parStep]
  ha := by simp [parStep]
  hat := by simp only [parStep, εs]; norm_num
  hlam1 := by simp only [parStep, εs]; norm_num
  hlam2 := by simp only [parStep, εs]; norm_num
  hlam3 := by simp only [parStep, εs]; norm_num
  hlo := by simp only [parStep]; norm_num
  hhi := by simp only [parStep]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parStep, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parStep, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parStep, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parStep, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parStep]; norm_num
  hA16 := by simp only [parStep]; norm_num

/-- The parameters of the step `7/3 + 1/2000` on `[16/21, 5/6]`: the power trick's target `Q^{7/9+3ε}`, powers
`m ≤ 1556`, and the inner exponent `7/3 + 25ε`. -/
def parHux73 : Par where
  M := 1556
  a := 7 / 9 + 2 * εs
  lam := 7 / 6 + 9 / 2 * εs
  lo := 16 / 21
  hi := 5 / 6
  Ai := 7 / 3 + 25 * εs
  A := 7 / 3 + 1 / 2000

theorem parHux73_good : parHux73.Good where
  hM := by simp [parHux73]
  ha := by simp only [parHux73, εs]; norm_num
  hat := by simp only [parHux73, εs]; norm_num
  hlam1 := by simp only [parHux73, εs]; norm_num
  hlam2 := by simp only [parHux73, εs]; norm_num
  hlam3 := by simp only [parHux73, εs]; norm_num
  hlo := by simp only [parHux73]; norm_num
  hhi := by simp only [parHux73]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHux73, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHux73, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHux73, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHux73, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHux73]; norm_num
  hA16 := by simp only [parHux73]; norm_num

open scoped Classical in
/-- **The step `7/3 + 1/2000` on `[16/21, 5/6]`**: there is `C ≥ 0` such that for every `q ≥ 1`, `16/21 ≤ σ ≤ 5/6`
and `T ≥ 2` at most `C(qT)^{(7/3+1/2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hux73 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 16 / 21 ≤ σ → σ ≤ 5 / 6 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((7 / 3 + 1 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHux73 parHux73_good

open scoped Classical in
/-- **Round 589's step from the parameters**: there is `C ≥ 0` such that for every `q ≥ 1`, `5/6 ≤ σ ≤ 11/12` and
`T ≥ 2` at most `C(qT)^{(101/50)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. This is `LinnikStep.charDensity_step` below `11/12`. -/
theorem charDensity_step' :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 6 ≤ σ → σ ≤ 11 / 12 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (101 / 50 * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parStep parStep_good

end LinnikHuxStep

#print axioms LinnikHuxStep.charDensity_hux73
#print axioms LinnikHuxStep.charDensity_step'
