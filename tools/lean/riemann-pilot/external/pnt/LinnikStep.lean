/-
# Round 589: a step of Huxley's bound, exponent `101/50` on `5/6 ≤ σ ≤ 11/12`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`charDensity_step`). There is `C ≥ 0` such that for every `q ≥ 1`, `5/6 ≤ σ ≤ 1` and `T ≥ 2`, at
most `C(qT)^{(101/50)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.

The proof is round 527's argument on `3/4 ≤ σ ≤ 11/12` (`LinnikTwelve.count_twelve_fifths`) with three parameters
changed: the detector's `X = ⌊Q^{1/2000}⌋` and `Y = Q^{201/400}` (round 518's `Xw`, `Yw`, `Nw` at `U = Q^{1/2000}`,
`c = 502`) in place of `⌊Q^{1/25}⌋` and `Q^{3/5}`, and the power trick's target `Q^{2/3+ε}` in place of `Q^{4/5+ε}`.
The power `m` is then at most `1334` in place of `22`. Up to powers of `Q^ε`, for `5/6 ≤ σ ≤ 11/12`:
* the first term of `block_bin_hux` carries `Λ^{2−2σ}`, and `Λ ≤ max((2XN)², Q^{3(2/3)/2}) ≤ Q^{201/200}`, so it is
  at most `Q^{(201/100)(1−σ)}`;
* the second carries `Λ^{4−6σ}Q ≤ Q^{(2/3)(4−6σ)+1}`, since `Λ ≥ Q^{2/3}` and `4 − 6σ < 0`, and
  `(101/50)(1 − σ) − ((2/3)(4 − 6σ) + 1) = (297σ − 247)/150 ≥ 1/300`;
* the integral class carries `Y^{4(1/2−σ)}X⁴Q = Q^{(201/100)(1/2−σ)+1/500+1}`, below `Q^{(101/50)(1−σ)}` by
  `Q^{13/1000−σ/100}`.
The internal `ε` is fixed at `1/100000`. Huxley's curve `3/(3σ − 1)` equals `2` at `σ = 5/6`.

* `choose_m_step`: the least `m` with `Q^a ≤ x^m`, for `x ≥ Q^{1/2000}` and `0 < a ≤ 667/1000`, has `m ≤ 1334`.
* `term1_step`, `exp2_step`, `Gm3_step`, `final2_step`, `term2_step`: the two terms of `block_bin_hux`, each at most a
  constant times `Q^{(2019/1000)(1−σ)}`.
* `class1_step`, `class2_bound_step`: the polynomial class and the integral class.
* `eventually_step`, `absorb_K_step`, `count_step_at`, `count_step`: the range `5/6 ≤ σ ≤ 11/12` for all large `Q`,
  and below.
* `charDensity_step`: the density estimate on `5/6 ≤ σ ≤ 1`, in the form of `Linnik.CharDensity` on that range.
-/

import LinnikTwelve

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

set_option exponentiation.threshold 3000

namespace LinnikStep

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag LinnikHuxley LinnikReflect LinnikTwelve

variable {q : ℕ}

/-! ### The power of a block -/

/-- **The power of a block**: for `x ≥ Q^{1/2000}` and `0 < a ≤ 667/1000` the least `m` with `Q^a ≤ x^m` has
`1 ≤ m ≤ 1334` and `x^m ≤ max(x², Q^{3a/2})` (`LinnikHuxley.choose_m` with `1/2000` in place of `1/25`). -/
lemma choose_m_step {Q a x : ℝ} (hQ : 1 < Q) (ha : 0 < a) (ha1 : a ≤ 667 / 1000) (hx : Q ^ (1 / 2000 : ℝ) ≤ x) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 1334 ∧ Q ^ a ≤ x ^ m ∧ x ^ m ≤ max (x ^ 2) (Q ^ (3 * a / 2)) := by
  classical
  have hQ0 : 0 < Q := by linarith
  have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hQ.le (by norm_num)) hx
  have hM : Q ^ a ≤ x ^ 1334 := by
    calc Q ^ a ≤ Q ^ (667 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ.le ha1
      _ = (Q ^ (1 / 2000 : ℝ)) ^ (1334 : ℕ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
      _ ≤ x ^ 1334 := pow_le_pow_left₀ (by positivity) hx 1334
  have hex : ∃ m : ℕ, Q ^ a ≤ x ^ m := ⟨1334, hM⟩
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

/-! ### One block and one bin as a power of `Q` in the range `5/6 ≤ σ ≤ 11/12` -/

/-- The constant of `term1_step`. -/
def B1s (ε : ℝ) : ℝ := 16 * 2 ^ 1334 * (4 * Cdiv (ε / 5336) ^ 4) ^ 1334

/-- The constant of `term2_step`. -/
def B2s (ε : ℝ) : ℝ := 2 ^ 2674 * (40 * (24 * InghamDensity.KG * CG) ^ 2) * (4 * Cdiv (ε / 5336) ^ 4) ^ 4002

lemma B1s_nonneg (ε : ℝ) : 0 ≤ B1s ε := by unfold B1s; positivity

lemma B2s_nonneg (ε : ℝ) : 0 ≤ B2s ε := by unfold B2s; positivity

/-- **The first term**: with `Λ = (2P)^m ≤ Q^{201/200+3ε/2}`, `m ≤ 1334`, `4K ≤ Q^{ε/32016}`, `σ ≤ σ_b` and
`σ ≤ 11/12`, `2c₀⁻¹G_m(σ_b)Λ(4K)^{2m} ≤ B1s(ε)Q^{(2019/1000)(1−σ)}`, `B1s(ε) = 16·2^{1334}(4C⁴)^{1334}`,
`c₀ = 2^{−m}/8`, `C = C(ε/5336)` the constant of the divisor bound (`LinnikTwelve.term1_le` with these sizes). -/
lemma term1_step {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100000) {σ σb Q : ℝ} (hσ11 : σ ≤ 11 / 12)
    (hσb : σ ≤ σb) (hQ1 : 1 ≤ Q) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 1334)
    (hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (201 / 200 + 3 / 2 * ε)) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : 4 * K ≤ Q ^ (ε / 32016)) :
    2 * (8 * 2 ^ m) * Gm (ε / 5336) P m σb * ((2 * P : ℕ) : ℝ) ^ m / ((1 / (4 * K)) ^ m) ^ 2
      ≤ B1s ε * Q ^ (2019 / 1000 * (1 - σ)) := by
  unfold B1s
  have hQ0 : 0 < Q := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hεd : 0 < ε / 5336 := by positivity
  have hεd1 : ε / 5336 ≤ 1 := by linarith
  set A : ℝ := 4 * Cdiv (ε / 5336) ^ 4 with hA
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 1334 := by exact_mod_cast hm
  have hGm : Gm (ε / 5336) P m σb ≤ A ^ 1334 * Λ ^ (1 - 2 * σ + ε) := by
    refine (Gm_le hεd hεd1 hP m (by linarith) hσb).trans ?_
    rw [← hA, ← hΛdef]
    exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
      (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (m * 2) ≤ Q ^ (ε / 12) := by
    calc (4 * K) ^ (m * 2) ≤ (Q ^ (ε / 32016)) ^ (m * 2) := pow_le_pow_left₀ hK0.le hK _
      _ = Q ^ (ε / 32016 * (m * 2 : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ Q ^ (ε / 12) := Real.rpow_le_rpow_of_exponent_le hQ1 (by push_cast; nlinarith)
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ 1334 := pow_le_pow_right₀ (by norm_num) hm
  have hpow : Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (2 - 2 * σ + ε) := by
    conv_lhs => rw [show Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0]; ring_nf
  have hΛQ : Λ ^ (2 - 2 * σ + ε) ≤ Q ^ ((201 / 200 + 3 / 2 * ε) * (2 - 2 * σ + ε)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow hΛ0.le hΛ (by linarith)
  have hexp : (201 / 200 + 3 / 2 * ε) * (2 - 2 * σ + ε) + ε / 12 ≤ 2019 / 1000 * (1 - σ) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hσ11) (by linarith : (0 : ℝ) ≤ 9 / 1000 - 3 * ε),
      mul_nonneg hε.le (sub_nonneg.2 hε1)]
  have hG0 : 0 ≤ Gm (ε / 5336) P m σb := by unfold Gm; positivity
  calc 2 * (8 * 2 ^ m) * Gm (ε / 5336) P m σb * Λ / ((1 / (4 * K)) ^ m) ^ 2
      = 2 * (8 * 2 ^ m) * Gm (ε / 5336) P m σb * Λ * (4 * K) ^ (m * 2) := by
        rw [one_div, inv_pow, inv_pow, div_inv_eq_mul, ← pow_mul]
    _ ≤ 2 * (8 * 2 ^ 1334) * (A ^ 1334 * Λ ^ (1 - 2 * σ + ε)) * Λ * Q ^ (ε / 12) := by gcongr
    _ = 16 * 2 ^ 1334 * A ^ 1334 * (Λ ^ (1 - 2 * σ + ε) * Λ) * Q ^ (ε / 12) := by ring
    _ = 16 * 2 ^ 1334 * A ^ 1334 * Λ ^ (2 - 2 * σ + ε) * Q ^ (ε / 12) := by rw [hpow]
    _ ≤ 16 * 2 ^ 1334 * A ^ 1334 * Q ^ ((201 / 200 + 3 / 2 * ε) * (2 - 2 * σ + ε)) * Q ^ (ε / 12) := by gcongr
    _ = 16 * 2 ^ 1334 * A ^ 1334 * Q ^ ((201 / 200 + 3 / 2 * ε) * (2 - 2 * σ + ε) + ε / 12) := by
        rw [mul_assoc _ (Q ^ _), ← Real.rpow_add hQ0]
    _ ≤ 16 * 2 ^ 1334 * A ^ 1334 * Q ^ (2019 / 1000 * (1 - σ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 hexp) (by positivity)

/-- The exponent of the second term: `(2/3 + ε)(4 − 6σ + 3ε) + 1 + 2ε ≤ (2019/1000)(1 − σ)` for `σ ≥ 5/6` and
`0 < ε ≤ 1/100000`; the difference is `(1981/1000)(σ − 5/6) + 19/6000 − ε(8 − 6σ) − 3ε²`. -/
lemma exp2_step {ε σ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100000) (hσ : 5 / 6 ≤ σ) :
    (2 / 3 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) ≤ 2019 / 1000 * (1 - σ) := by
  have key : 2019 / 1000 * (1 - σ) - ((2 / 3 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4)) =
      1981 / 1000 * (σ - 5 / 6) + 19 / 6000 - ε * (8 - 6 * σ) - 3 * ε ^ 2 := by ring
  nlinarith [mul_nonneg hε.le (sub_nonneg.2 hσ), mul_nonneg hε.le (sub_nonneg.2 hε1)]

/-- `G_m(σ_b)³ ≤ (4C⁴)^{4002}Λ^{3−6σ+3ε}` for `m ≤ 1334`, `σ ≤ σ_b`, `σ ≤ 1` (`Gm_le` cubed). -/
lemma Gm3_step {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100000) {σ σb : ℝ} (hσ1 : σ ≤ 1) (hσb : σ ≤ σb) {P m : ℕ}
    (hP : 1 ≤ P) (hm : m ≤ 1334) :
    Gm (ε / 5336) P m σb ^ 3 ≤ (4 * Cdiv (ε / 5336) ^ 4) ^ 4002 * (((2 * P : ℕ) : ℝ) ^ m) ^ (3 - 6 * σ + 3 * ε) := by
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hεd : 0 < ε / 5336 := by positivity
  have hεd1 : ε / 5336 ≤ 1 := by linarith
  set A : ℝ := 4 * Cdiv (ε / 5336) ^ 4 with hA
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 1334 := by exact_mod_cast hm
  have hGm : Gm (ε / 5336) P m σb ≤ A ^ 1334 * Λ ^ (1 - 2 * σ + ε) := by
    refine (Gm_le hεd hεd1 hP m hσ1 hσb).trans ?_
    rw [← hA, ← hΛdef]
    exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
      (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)
  have hG0 : 0 ≤ Gm (ε / 5336) P m σb := by unfold Gm; positivity
  calc Gm (ε / 5336) P m σb ^ 3 ≤ (A ^ 1334 * Λ ^ (1 - 2 * σ + ε)) ^ 3 := pow_le_pow_left₀ hG0 hGm 3
    _ = A ^ 4002 * Λ ^ (3 - 6 * σ + 3 * ε) := by
        rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (Λ ^ (1 - 2 * σ + ε)), ← Real.rpow_mul hΛ0.le]
        congr 2; push_cast; ring

/-- The product of the five bounds of the second term as a power of `Q`. -/
lemma final2_step {Q Λ A C ε σ : ℝ} (hQ1 : 1 ≤ Q) (hΛ0 : 0 < Λ) (hC : 0 ≤ C)
    (hΛQ : Λ ^ (4 - 6 * σ + 3 * ε) ≤ Q ^ ((2 / 3 + ε) * (4 - 6 * σ + 3 * ε)))
    (hexp : (2 / 3 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) ≤ 2019 / 1000 * (1 - σ)) :
    2 ^ 2674 * Q ^ (ε / 4) * (A ^ 4002 * Λ ^ (3 - 6 * σ + 3 * ε)) * (C * Λ * Q ^ (1 + 3 / 2 * ε)) * Q ^ (ε / 4) ≤
      2 ^ 2674 * C * A ^ 4002 * Q ^ (2019 / 1000 * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hΛpow : Λ ^ (3 - 6 * σ + 3 * ε) * Λ = Λ ^ (4 - 6 * σ + 3 * ε) := by
    conv_lhs => rw [show Λ ^ (3 - 6 * σ + 3 * ε) * Λ = Λ ^ (3 - 6 * σ + 3 * ε) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0]; ring_nf
  have eQ : Q ^ (ε / 4) * Q ^ (1 + 3 / 2 * ε) * Q ^ (ε / 4) = Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
  have hD : 0 ≤ 2 ^ 2674 * C * A ^ 4002 := by positivity
  have hQe : 0 ≤ Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by positivity
  calc 2 ^ 2674 * Q ^ (ε / 4) * (A ^ 4002 * Λ ^ (3 - 6 * σ + 3 * ε)) * (C * Λ * Q ^ (1 + 3 / 2 * ε)) * Q ^ (ε / 4)
      = (2 ^ 2674 * C * A ^ 4002) * (Λ ^ (3 - 6 * σ + 3 * ε) * Λ) *
          (Q ^ (ε / 4) * Q ^ (1 + 3 / 2 * ε) * Q ^ (ε / 4)) := by ring
    _ = (2 ^ 2674 * C * A ^ 4002) * Λ ^ (4 - 6 * σ + 3 * ε) * Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by
        rw [hΛpow, eQ]
    _ ≤ (2 ^ 2674 * C * A ^ 4002) * Q ^ ((2 / 3 + ε) * (4 - 6 * σ + 3 * ε)) *
          Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛQ hD) hQe
    _ = (2 ^ 2674 * C * A ^ 4002) *
          Q ^ ((2 / 3 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4)) := by
        rw [mul_assoc, ← Real.rpow_add hQ0]
    _ ≤ 2 ^ 2674 * C * A ^ 4002 * Q ^ (2019 / 1000 * (1 - σ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 hexp) hD

/-- **The second term**: with `Λ = (2P)^m ≥ Q^{2/3+ε}`, `m ≤ 1334`, `4K ≤ Q^{ε/32016}`, the far tail cut off and the
sizes of `A1_sq_le`, `c₀⁻²4^{ω(q)}G_m(σ_b)³hxA²(4K)^{6m} ≤ B2s(ε)Q^{(2019/1000)(1−σ)}`,
`B2s(ε) = 2^{2674}·40(24·KG·CG)²(4C⁴)^{4002}`,
for `5/6 ≤ σ ≤ σ_b`, `σ ≤ 11/12`: `G_m³ ≤ (4C⁴)^{4002}Λ^{3−6σ+3ε}` (`Gm3_step`), `hxA² ≤ 4A₁²` (`hxA_sq_le`), and
`Λ^{4−6σ+3ε} ≤ Q^{(2/3+ε)(4−6σ+3ε)}` because `4 − 6σ + 3ε < 0`; the exponents are compared in `exp2_step`. -/
lemma term2_step [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100000) {σ σb Q T τ : ℝ} (hσ : 5 / 6 ≤ σ)
    (hσ11 : σ ≤ 11 / 12) (hσb : σ ≤ σb) (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 1334) (hΛlo : Q ^ (2 / 3 + ε) ≤ ((2 * P : ℕ) : ℝ) ^ m)
    {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ Q ^ (ε / 32016))
    {X J : ℕ} (hX1 : 1 ≤ X) (hXQ : (X : ℝ) ≤ Q ^ (25 : ℝ)) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (ε / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (ε / 8)) (hL : LSmax X ≤ Q ^ (ε / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8)) (hEQ : EQ q ≤ Q ^ (ε / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (ε / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / 5336) P m σb ^ 3 *
        hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) ((2 * P) ^ m : ℕ) X J ^ 2 / ((1 / (4 * K)) ^ m) ^ 6
      ≤ B2s ε * Q ^ (2019 / 1000 * (1 - σ)) := by
  unfold B2s
  have hQ0 : 0 < Q := by linarith
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ ((2 * P : ℕ) : ℝ) ^ m := one_le_pow₀ h2P
  have hΛ0 : 0 < ((2 * P : ℕ) : ℝ) ^ m := by linarith
  have hN : ((((2 * P) ^ m : ℕ)) : ℝ) = ((2 * P : ℕ) : ℝ) ^ m := by push_cast; ring
  rw [hN]
  have hεd : 0 < ε / 5336 := by positivity
  have hCd := one_le_Cdiv hεd (by linarith)
  have hA0 : 0 ≤ 4 * Cdiv (ε / 5336) ^ 4 := by positivity
  have hKG := InghamDensity.KG_pos
  have hCG := CG_pos
  have hC0 : 0 ≤ 40 * (24 * InghamDensity.KG * CG) ^ 2 := by positivity
  have hH := hxA_sq_le (q := q) (τ := τ) (Λ := ((2 * P : ℕ) : ℝ) ^ m) hε (by linarith) hQ1 hT hqT hΛ0.le hX1 hXQ
    hτ1 hτQ hJ hL hB hEQ hfar
  have hG3 := Gm3_step hε hε1 (σ := σ) (by linarith) hσb hP hm
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (m * 6) ≤ Q ^ (ε / 4) := by
    calc (4 * K) ^ (m * 6) ≤ (Q ^ (ε / 32016)) ^ (m * 6) := pow_le_pow_left₀ hK0.le hK _
      _ = Q ^ (ε / 32016 * (m * 6 : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ Q ^ (ε / 4) := Real.rpow_le_rpow_of_exponent_le hQ1 (by
          have hm' : (m : ℝ) ≤ 1334 := by exact_mod_cast hm
          push_cast; nlinarith)
  have h8 : (8 * (2 : ℝ) ^ m) ^ 2 ≤ 2 ^ 2674 := by
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ 1334 := pow_le_pow_right₀ (by norm_num) hm
    calc (8 * (2 : ℝ) ^ m) ^ 2 ≤ (8 * 2 ^ 1334) ^ 2 := by gcongr
      _ = 2 ^ 2674 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_mul]
  have hPs2 : (q.primeFactors.powerset.card : ℝ) ^ 2 ≤ Q ^ (ε / 4) := by
    calc (q.primeFactors.powerset.card : ℝ) ^ 2 ≤ (Q ^ (ε / 8)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hPs 2
      _ = Q ^ (ε / 4) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; ring_nf
  have hΛQ : (((2 * P : ℕ) : ℝ) ^ m) ^ (4 - 6 * σ + 3 * ε) ≤ Q ^ ((2 / 3 + ε) * (4 - 6 * σ + 3 * ε)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hΛlo (by linarith)
  have hexp := exp2_step hε hε1 hσ
  have hG0 : 0 ≤ Gm (ε / 5336) P m σb ^ 3 := by unfold Gm; positivity
  have hprod := prod5_le (by positivity) (by positivity) hG0 (sq_nonneg _) (by positivity) h8 hPs2 hG3 hH h4K
  have hfin := final2_step (A := 4 * Cdiv (ε / 5336) ^ 4) hQ1 hΛ0 hC0 hΛQ hexp
  have e1 : (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / 5336) P m σb ^ 3 *
      hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) (((2 * P : ℕ) : ℝ) ^ m) X J ^ 2 / ((1 / (4 * K)) ^ m) ^ 6 =
      (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / 5336) P m σb ^ 3 *
      hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) (((2 * P : ℕ) : ℝ) ^ m) X J ^ 2 * (4 * K) ^ (m * 6) := by
    rw [one_div, inv_pow, inv_pow, div_inv_eq_mul, ← pow_mul]
  rw [e1]
  exact hprod.trans hfin

/-! ### The polynomial class and the integral class in the range `5/6 ≤ σ ≤ 11/12` -/

/-- **The polynomial class with Huxley's estimate on `5/6 ≤ σ ≤ 11/12`.** Characters with one point `β_χ + iγ_χ`
each, `σ ≤ β_χ < 1`, `|γ_χ| ≤ T`, and `|P_χ(β_χ + iγ_χ)| ≥ ¼` number at most
`(⌊50/ε⌋ + 1)K(B₁ + B₂)Q^{(2019/1000)(1−σ)}`, `K = ⌊log₂ N⌋ + 1`, for `Q^{1/2000} ≤ 2X` and
`(2XN)² ≤ Q^{201/200+ε}` (`LinnikTwelve.class1_twelve` with these sizes): some dyadic block is at least `1/(4K)`;
bins of width `ε/200` in `β`; in each block and bin the least power `m` with `(2P)^m ≥ Q^{2/3+ε}`
(`choose_m_step`), at most `Q^{201/200+3ε/2}` long, and `block_bin_hux` with `term1_step` and `term2_step`. -/
theorem class1_step [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100000)
    {σ T Q : ℝ} (hσ : 5 / 6 ≤ σ) (hσ1 : σ ≤ 11 / 12) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXQ : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 32016))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + ε))
    {Xl J : ℕ} {τ : ℝ} (hXl1 : 1 ≤ Xl) (hXlQ : (Xl : ℝ) ≤ Q ^ (25 : ℝ))
    (hXl : Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Xl)
    (hτd : ∀ n, n ≤ Xl → (n.divisors.card : ℝ) ≤ τ) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (ε / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (ε / 8)) (hL : LSmax Xl ≤ Q ^ (ε / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8)) (hEQ : EQ q ≤ Q ^ (ε / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (ε / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1)
    {Y : ℝ} (hY : 0 < Y) (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ < 1) (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T)
    (hbig : ∀ χ ∈ Rs, 1 / 4 ≤ ‖Pvχ χ X N Y (β χ) (γ χ)‖) :
    (Rs.card : ℝ) ≤ ((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * ((B1s ε + B2s ε) *
      Q ^ (2019 / 1000 * (1 - σ))) := by
  classical
  have hQ0 : 0 < Q := by linarith
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set nb := ⌊50 / ε⌋₊ + 1 with hnb
  set Bb := (B1s ε + B2s ε) * Q ^ (2019 / 1000 * (1 - σ)) with hBb
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
    Rs.filter fun χ => V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ ∧ ⌊200 / ε * (β χ - σ)⌋₊ = j with hCkdef
  have hsub : Rs ⊆ (range K).biUnion fun k => (range nb).biUnion fun j => Ck k j := by
    intro χ hχ
    obtain ⟨k, hk, hbigk⟩ := hlarge χ hχ
    have h1 := hβ χ hχ
    have hj : ⌊200 / ε * (β χ - σ)⌋₊ < nb := by
      have hle : 200 / ε * (β χ - σ) ≤ 50 / ε := by
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
      choose_m_step hQ1 (by positivity : (0 : ℝ) < 2 / 3 + ε) (by linarith) h2Px
    have hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (201 / 200 + 3 / 2 * ε) := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ Q ^ (201 / 200 + ε) := hXN
          _ ≤ Q ^ (201 / 200 + 3 / 2 * ε) := Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith)
    have hΛ2 : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ 2 := by
      calc ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (201 / 200 + 3 / 2 * ε) := hΛ
        _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith)
        _ = Q ^ 2 := by norm_num
    set σb : ℝ := σ + j * (ε / 200) with hσb
    have hσσb : σ ≤ σb := by
      have : (0 : ℝ) ≤ (j : ℝ) * (ε / 200) := by positivity
      rw [hσb]; linarith
    have hbin : ∀ χ ∈ Ck k j, σb ≤ β χ ∧ β χ ≤ σb + ε / 200 := by
      intro χ hχ
      obtain ⟨hχR, -, hbj⟩ := mem_filter.1 hχ
      have h0 : 0 ≤ 200 / ε * (β χ - σ) := by
        have h5 := (hβ χ hχR).1
        have h6 : 0 ≤ β χ - σ := by linarith
        positivity
      have h1 : ((⌊200 / ε * (β χ - σ)⌋₊ : ℕ) : ℝ) ≤ 200 / ε * (β χ - σ) := Nat.floor_le h0
      have h2 : 200 / ε * (β χ - σ) < ((⌊200 / ε * (β χ - σ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hbj] at h1 h2
      constructor
      · have h3 : (j : ℝ) * (ε / 200) ≤ β χ - σ := by
          calc (j : ℝ) * (ε / 200) ≤ (200 / ε * (β χ - σ)) * (ε / 200) := by gcongr
            _ = β χ - σ := by field_simp
        rw [hσb]; linarith
      · have h3 : β χ - σ ≤ ((j : ℝ) + 1) * (ε / 200) := by
          have h4 : 200 / ε * (β χ - σ) ≤ (j : ℝ) + 1 := h2.le
          calc β χ - σ = (200 / ε * (β χ - σ)) * (ε / 200) := by field_simp
            _ ≤ ((j : ℝ) + 1) * (ε / 200) := by gcongr
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
    have hcount := block_bin_hux (q := q) (R := Ck k j) hP hSsub (c := b1 X Y) (fun i _ => norm_b1_le X hY i) hm1
      (σb := σb) (η := ε / 200) (by linarith) (by linarith) β γ hbin hT (fun χ hχ => hγ χ (mem_filter.1 hχ).1) hV0
      (fun χ hχ => by rw [← Fkχ_eq_pv]; exact (mem_filter.1 hχ).2.1) (εd := ε / 5336) (by positivity)
      (by linarith) J hXl1 hXD hτd
    have ht1 := term1_step hε hε1 hσ1 hσσb hQ1.le hP hmM hΛ hK1 hK
    have ht2 := term2_step (q := q) hε hε1 hσ hσ1 hσσb hQ1.le hT hqT hP hmM hΛlo hK1
      hK hXl1 hXlQ hτ1 hτQ hJ hL hB hEQ hPs hfar
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

/-- **The integral class as a power of `Q`**: with `Y = Q^{201/400}`, `X ≤ Q^{1/2000}`, `q(T + 2) ≤ Q` and `δ = 1/4`,
`27A⁴X⁴M₂ ≤ 27(4KG)⁴C₄Q^{(101/50)(1−σ)}` for `σ ≤ 1`: the exponent `(201/100)(1/2 − σ) + 1/500 + 1 + ε` falls short of
`(101/50)(1 − σ)` by `13/1000 − σ/100 − ε ≥ 3/1000 − ε`. -/
lemma class2_bound_step {ε C₄ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100000) (hC₄ : 0 ≤ C₄) {σ T Q : ℝ} (hσ1 : σ ≤ 1)
    (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) {X : ℕ} (hXQ : (X : ℝ) ≤ Q ^ (1 / 2000 : ℝ)) :
    27 * (KG * (Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (101 / 50 * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hY : ((Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = Q ^ (201 / 100 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ Q ^ (1 / 500 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (Q ^ (1 / 2000 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXQ 4
      _ = Q ^ (1 / 500 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
  have hM : ((q : ℝ) * (T + 2)) ^ (1 + ε) ≤ Q ^ (1 + ε) := Real.rpow_le_rpow (by positivity) hqT (by linarith)
  have hexp : 201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + ε) ≤ 101 / 50 * (1 - σ) := by linarith
  calc 27 * (KG * (Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 *
        (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      = 27 * (4 * KG) ^ 4 * C₄ * (((Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 *
          ((q : ℝ) * (T + 2)) ^ (1 + ε)) := by ring
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * (Q ^ (201 / 100 * (1 / 2 - σ)) * Q ^ (1 / 500 : ℝ) * Q ^ (1 + ε)) := by
        rw [hY]; gcongr
    _ = 27 * (4 * KG) ^ 4 * C₄ * Q ^ (201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + ε)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (101 / 50 * (1 - σ)) := by
        gcongr

/-! ### Large `Q` -/

/-- The conditions on `Q` used in the range `5/6 ≤ σ ≤ 11/12` hold for all large `Q` (`ev_log_pow`); as
`LinnikTwelve.eventually_twelve`, with `Q^{1/2000} ≥ 8`, `Y = Q^{201/400}` and `4K ≤ Q^{ε/32016}`. -/
lemma eventually_step {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM : 1 ≤ M) :
    ∀ᶠ Q : ℝ in atTop, (8 : ℝ) ^ 2000 ≤ Q ∧ 4 * (1 + 2 * Real.log Q) ≤ Q ^ (ε / 32016) ∧
      (2 * (23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)))) ^ 2 ≤ Q ^ (201 / 200 + ε) ∧
      23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)) ≤ Q ∧ Cdiv (ε / 200) ≤ Q ^ (ε / 8) ∧
      16 * (2 * Real.log (4 * M * Q) + 1) + 2 ≤ Q ^ (ε / 8) ∧ (8 * M * Q) ^ 16 ≤ Q ^ 20 ∧
      8 * Real.exp 1 * 25 * 627 * 50 * (1 + Real.log Q) ^ 4 ≤ Q ^ (ε / 8) ∧
      2 * Real.log (4 * Q) + 1 ≤ Q ^ (ε / 8) ∧ CEQ ε ≤ Q ^ (ε / 16) ∧ Cdiv (ε / 16) ≤ Q ^ (ε / 16) := by
  have hlM : 0 ≤ Real.log (4 * M) := Real.log_nonneg (by linarith)
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 2000), ev_log_pow 8 (ε / 32016) 1 (by positivity),
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

/-- The number `K ≤ Q^{ε/32016}/4` of dyadic blocks absorbed into the exponent:
`ε/32016 + (2019/1000)(1 − σ) ≤ (101/50)(1 − σ)` for `σ ≤ 11/12`. -/
lemma absorb_K_step {ε σ Q nb B K c : ℝ} (hε1 : ε ≤ 1 / 100000) (hσ1 : σ ≤ 11 / 12) (hQ1 : 1 ≤ Q)
    (hnb : 0 ≤ nb) (hB : 0 ≤ B) (hK0 : 0 ≤ K) (hK : 4 * K ≤ Q ^ (ε / 32016))
    (hc : c ≤ nb * K * (B * Q ^ (2019 / 1000 * (1 - σ)))) :
    c ≤ nb * B * Q ^ (101 / 50 * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKle : K ≤ Q ^ (ε / 32016) := by have := Real.rpow_nonneg hQ0.le (ε / 32016); linarith
  have hE1 : Q ^ (ε / 32016) * Q ^ (2019 / 1000 * (1 - σ)) ≤ Q ^ (101 / 50 * (1 - σ)) := by
    rw [← Real.rpow_add hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hP0 : 0 ≤ Q ^ (2019 / 1000 * (1 - σ)) := by positivity
  calc c ≤ nb * K * (B * Q ^ (2019 / 1000 * (1 - σ))) := hc
    _ ≤ nb * Q ^ (ε / 32016) * (B * Q ^ (2019 / 1000 * (1 - σ))) := by gcongr
    _ = nb * B * (Q ^ (ε / 32016) * Q ^ (2019 / 1000 * (1 - σ))) := by ring
    _ ≤ nb * B * Q ^ (101 / 50 * (1 - σ)) := by gcongr

open scoped Classical in
/-- **The range `5/6 ≤ σ ≤ 11/12` at one large `Q`.** With the detector's `X, N, Y` (`22Y log Y ≤ XN`,
`Y = Q^{201/400}`, `Q^{1/2000} ≤ 2X`, `X ≤ Q^{1/2000}`), the large-sieve range `X_l`, `J` and `τ` of `class1_step`, at
most `(⌊50/ε⌋ + 1)(B₁ + B₂)Q^E + 27(4KG)⁴C₄Q^E` characters `χ ≠ 1` mod `q` have a zero in `Re s ≥ σ`, `|Im s| ≤ T`,
`E = (101/50)(1 − σ)`: `LinnikDetect.dichotomy`, `class1_step`, `class2_count_small` and `class2_bound_step`. -/
theorem count_step_at [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100000) {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {σ T Q : ℝ} (hσ : 5 / 6 ≤ σ) (hσ1 : σ ≤ 11 / 12) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hY8 : 8 ≤ Y) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hYQ : Y = Q ^ (201 / 400 : ℝ)) (hXU : (X : ℝ) ≤ Q ^ (1 / 2000 : ℝ)) (hXU2 : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 32016))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + ε))
    {Xl J : ℕ} {τ : ℝ} (hXl1 : 1 ≤ Xl) (hXlQ : (Xl : ℝ) ≤ Q ^ (25 : ℝ))
    (hXl : Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Xl)
    (hτd : ∀ n, n ≤ Xl → (n.divisors.card : ℝ) ≤ τ) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (ε / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (ε / 8)) (hL : LSmax Xl ≤ Q ^ (ε / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8)) (hEQ : EQ q ≤ Q ^ (ε / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (ε / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ (((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1s ε + B2s ε) + 27 * (4 * KG) ^ 4 * C₄) *
        Q ^ (101 / 50 * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
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
  have hc1 := class1_step hε hε1 hσ hσ1 hT hQ1 hqT hX hN hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hB hEQ
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
  have hb2 := class2_bound_step (q := q) (σ := σ) hε hε1 hC₄0 (by linarith) hQ1.le hT hqT (X := X) hXU
  rw [hYQ] at hc2
  have hI := absorb_K_step hε1 hσ1 hQ1.le (by positivity) (add_nonneg (B1s_nonneg ε) (B2s_nonneg ε))
    (Nat.cast_nonneg _) hK hc1
  have hII : (Z2.card : ℝ) ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (101 / 50 * (1 - σ)) := hc2.trans hb2
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card := by exact_mod_cast card_union_le Z1 Z2
    _ ≤ ((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1s ε + B2s ε) * Q ^ (101 / 50 * (1 - σ)) +
          27 * (4 * KG) ^ 4 * C₄ * Q ^ (101 / 50 * (1 - σ)) := add_le_add hI hII
    _ = (((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1s ε + B2s ε) + 27 * (4 * KG) ^ 4 * C₄) *
          Q ^ (101 / 50 * (1 - σ)) := by ring

/-- `Y = Q^{201/400}` for the detector at `U = Q^{1/2000}`, `c = 502`. -/
lemma Yw_step {Q : ℝ} (hQ0 : 0 < Q) : Yw 502 (Q ^ (1 / 2000 : ℝ)) = Q ^ (201 / 400 : ℝ) := by
  unfold Yw; rw [← Real.rpow_mul hQ0.le]; norm_num

open scoped Classical in
/-- **The range `5/6 ≤ σ ≤ 11/12`.** There is `C ≥ 0` such that for every `q ≥ 1`, `5/6 ≤ σ ≤ 11/12` and `T ≥ 2` at
most `C Q^{(101/50)(1−σ)}`, `Q = q(T + 6)`, characters `χ ≠ 1` mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. At `ε = 1/100000`: for `Q ≥ Q₀` (`eventually_step`), `count_step_at` at the detector
`X = ⌊Q^{1/2000}⌋`, `Y = Q^{201/400}` and the large-sieve range of `sieve_range`; below `Q₀` at most `q ≤ Q₀`
characters are counted (`LinnikTwelve.count_twelve_fifths` with these sizes). -/
theorem count_step :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 6 ≤ σ → σ ≤ 11 / 12 → 2 ≤ T →
      ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ C * ((q : ℝ) * (T + 6)) ^ (101 / 50 * (1 - σ)) := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / 100000 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; norm_num
  have hε1 : ε ≤ 1 / 100000 := hεdef.le
  have hε200 : ε ≤ 1 / 200 := by linarith
  obtain ⟨C₄', hC₄'⟩ := LinnikFourth.fourth_moment hε (by linarith : ε ≤ 1)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = max C₄' 0 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := hC₄ ▸ le_max_right _ _
  have h4all : ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) →
      ∀ T' : ℝ, 0 ≤ T' → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε) := by
    intro q _ R hR T' hT' t ht
    refine (hC₄' q R hR T' hT' t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₄ ▸ le_max_left _ _) (by positivity)
  have hM1 : (1 : ℝ) ≤ max zeta98 1 := le_max_right _ _
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (eventually_step hε hM1)
  have hKG := KG_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1s ε + B2s ε) + 27 * (4 * KG) ^ 4 * C₄ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; have := B1s_nonneg ε; have := B2s_nonneg ε; positivity
  refine ⟨max Q₀ 0 + B, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) * (T + 6) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ8 : 8 ≤ Q := by
    rw [hQ]
    calc (8 : ℝ) = 1 * 8 := by norm_num
      _ ≤ (q : ℝ) * (T + 6) := mul_le_mul hq1 (by linarith) (by norm_num) (by positivity)
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 101 / 50 * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (by norm_num) (by linarith)
  have hQE : 1 ≤ Q ^ E := Real.one_le_rpow hQ1 hE0
  rcases lt_or_ge Q Q₀ with hsmall | hlarge
  · -- below `Q₀`: at most `q ≤ Q < Q₀` characters
    have hBQ : 0 ≤ B * Q ^ E := by positivity
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ max Q₀ 0 := hsmall.le.trans (le_max_left _ _)
      _ ≤ max Q₀ 0 * Q ^ E := le_mul_of_one_le_right (le_max_right _ _) hQE
      _ ≤ (max Q₀ 0 + B) * Q ^ E := by rw [add_mul]; linarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hQ₀ Q hlarge
  -- the detector at `U = Q^{1/2000}`, `c = 502`
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Q ^ (1 / 2000 : ℝ) := ⟨_, rfl⟩
  have hU8 : 8 ≤ U := by
    rw [hU]
    calc (8 : ℝ) = ((8 : ℝ) ^ 2000) ^ (1 / 2000 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ Q ^ (1 / 2000 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hYQ : Yw 502 U = Q ^ (201 / 400 : ℝ) := by rw [hU]; exact Yw_step hQ0
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
  have hK : 4 * ((Nat.log 2 (Nw 502 U) + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 32016) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNQ) (by norm_num)).trans h2
  have hXN : (2 * ((Xw U * Nw 502 U : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + ε) := by
    refine le_trans ?_ h3
    rw [← hYQ]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hqT : (q : ℝ) * (T + 2) ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  have h1' : (8 : ℝ) ^ 25 ≤ Q := le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) h1
  -- the large-sieve range and the sizes of `bkt`, `EQ` and `2^{ω(q)}`
  obtain ⟨Xl, J, τ, hXl1, hXlQ, hXl, hτd, hτ1, hτQ, hJ, hL, hfar⟩ :=
    sieve_range (q := q) hε hε200 (by linarith : (0 : ℝ) ≤ T) h1' hqT h5 h6 h7 h8
  have hBk := bkt_le_Q (q := q) (ε := ε) (by linarith : (0 : ℝ) ≤ T) hqT h9
  have hEQ := EQ_le_Q (q := q) hε hQ1 hqQ h10
  have hPs := powerset_le_Q (q := q) hε hε200 hQ1 hqQ h11
  have hcount := count_step_at (q := q) (σ := σ) (T := T) (Q := Q) hε hε1 hC₄0 (h4all q) hσ hσ1 (by linarith)
    (by linarith) hqT hX hN hY8 hM hYQ hXU hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hBk hEQ hPs hfar
  rw [← hE, ← hB] at hcount
  calc _ ≤ B * Q ^ E := hcount
    _ ≤ (max Q₀ 0 + B) * Q ^ E := by
        have : 0 ≤ max Q₀ 0 * Q ^ E := by positivity
        rw [add_mul]; linarith

/-! ### Density over the characters -/

open scoped Classical in
/-- **A density estimate over the characters mod `q` with exponent `101/50` on `5/6 ≤ σ ≤ 1`**: there is `C ≥ 0`
such that for every `q ≥ 1`, `5/6 ≤ σ ≤ 1` and `T ≥ 2` at most `C(qT)^{(101/50)(1−σ)}(log qT)^{10}` characters mod
`q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`, the form of `Linnik.CharDensity` on this range. Up to
`11/12`, `count_step` measured at `Q = q(T + 6) ≤ 4qT`, plus the trivial character; above `11/12` no character
`χ ≠ 1` has a zero (`LinnikLindelof.LFunction_ne_zero`). -/
theorem charDensity_step :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 6 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (101 / 50 * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  obtain ⟨CT, hCT0, hCT⟩ := count_step
  refine ⟨2 ^ 10 + 256 * 2 ^ 10 * CT, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((q : ℝ) * T) := ⟨_, rfl⟩
  rw [← hℓdef]
  have hℓ : 1 / 2 ≤ ℓ := hℓdef ▸ half_le_log hqT
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 101 / 50 * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (by norm_num) (by linarith)
  have hE4 : E ≤ 4 := by rw [hE]; linarith
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
  have hrest : 0 ≤ 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by positivity
  rcases lt_or_ge (11 / 12) σ with hbig | hle
  · -- above `11/12`: no character `χ ≠ 1` has a zero
    have hZ : (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro χ - ⟨hχ1, s, hs, -, hz⟩
      exact LinnikLindelof.LFunction_ne_zero hχ1 (by linarith) hz
    rw [hZ, card_empty, Nat.cast_zero, zero_add] at hF
    calc _ ≤ (1 : ℝ) := hF
      _ ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := h1
      _ ≤ (2 ^ 10 + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith
  -- `Q = q(T + 6) ≤ 4qT`
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 256 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by positivity) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (4 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 256 * ((q : ℝ) * T) ^ E := by norm_num
  have hZ := hCT q σ T hσ hle hT
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

end LinnikStep

#print axioms LinnikStep.choose_m_step
#print axioms LinnikStep.term1_step
#print axioms LinnikStep.term2_step
#print axioms LinnikStep.class1_step
#print axioms LinnikStep.class2_bound_step
#print axioms LinnikStep.count_step_at
#print axioms LinnikStep.count_step
#print axioms LinnikStep.charDensity_step
