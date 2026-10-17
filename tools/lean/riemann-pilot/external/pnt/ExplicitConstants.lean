/-
# Round 484: explicit constants for Littlewood's bounds and the least quadratic nonresidue

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every quadratic Dirichlet character `χ ≠ 1` mod `N`:
`|ψ(x, χ)| ≤ (2·10¹¹/e⁵) log(N + 2)·x^{11/12+η}` for every `x > 1` and `η > 0`, with `e = min(η, 1/24)`
(`psiChi_le_explicit`; round 509: for every Dirichlet character `χ ≠ 1` mod `N`); `|L′/L(σ, χ)| ≤ 10²¹ log log(N + 16)` for `1 ≤ σ ≤ 2` (`logDeriv_le_explicit`,
`norm_logDeriv_one_le_explicit`); `|log |L(1, χ)|| ≤ log log log(N + 16) + 2·10²¹`, so
`e^{−2·10²¹}/log log(N + 16) ≤ |L(1, χ)| ≤ e^{2·10²¹} log log(N + 16)` (`norm_LFunction_one_ge_explicit`,
`norm_LFunction_one_le_explicit`). For every `A > 12`, with `e = min(1/12 − 1/A, 1/24)` and
`K = 4(2·10¹¹/e⁵ + 11)`: `χ` has, for `ε = ±1`, a prime `p ∤ N` with `χ(p) = ε` and
`p ≤ (101 + K^A)(log(N + 2))^A` (`exists_prime_eq_explicit`), at `A = 13` below `10²⁹⁸(log(N + 2))¹³`
(`exists_prime_eq_13`); and every odd prime `p` has a quadratic nonresidue `n ≤ (101 + K^A)2^A(log p)^A`
(`exists_nonsquare_le_explicit`), at `A = 13` below `10³⁰⁴(log p)¹³` (`exists_nonsquare_le_13`), so below
`10³⁰⁴(13/δ)¹³p^δ` for every `δ > 0` (`exists_nonsquare_le_rpow_explicit`). No hypothesis.

* `zeta32_le`, `logDerivZeta32_le`: `ζ(3/2) ≤ 3` and `−ζ′/ζ(3/2) ≤ 3(log 4 + 4)`, by round 480's partial summation
  (`Littlewood.norm_LSeries_le_of_sum_le`) with `⌊t⌋ ≤ t` and with Mathlib's `Chebyshev.psi_le_const_mul_self`.
* `Kld_le`: the constant `LogDerivDisc.Kld (11/12) (11/12 + e/4)` (`ChiUniform.Kld` before round 513) is at most
  `23000/e³` for `0 < e ≤ 1/24`: `16r²/(r − r′)³ ≤ 16(28/(3e))³`, and `(R²/R′ − R′) log(R/R′) ≥ (3e/28)²` from
  `log y ≥ 1 − 1/y`.
* `KM_le`: the constant of `ExplicitSmooth.mellin_ν₀_le_geom` on the line `11/12 + e/4` is at most `6750`.
* `psiChi_le_explicit`: `ChiPNT.sum_le_uniform_of` (`ChiUniform.sum_le_uniform_of` before round 513) with `ν₀`,
  then `ChiUniform.psiChi_le_uniform_of`, with `log(2 + 36ζ(3/2)/11) ≤ 3` and `−ζ′/ζ(3/2) ≤ 17`.
* The rest: the `_of` theorems of `Littlewood` and `LeastNonresidue` with these constants.
-/
import ExplicitSmooth
import LeastNonresidue

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransform8) "𝓜" => mellin

namespace ExplicitConstants

open ChiUniform Littlewood LeastNonresidue ExplicitSmooth ChiPNT LogDerivDisc

/-! ### `ζ(3/2)` and `−ζ′/ζ(3/2)` -/

/-- A term of an L-series with real coefficients at a real point is real. -/
lemma term_ofReal (a : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n ↦ (a n : ℂ)) σ n = ((if n = 0 then 0 else a n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rw [LSeries.term_def]
  split_ifs with hn
  · simp
  · rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

/-- For nonnegative real coefficients, `Σ ‖term‖ = ‖L(f, σ)‖`. -/
lemma tsum_norm_term_eq {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (σ : ℝ) :
    ∑' n, ‖LSeries.term (fun n ↦ (a n : ℂ)) σ n‖ = ‖LSeries (fun n ↦ (a n : ℂ)) σ‖ := by
  set t : ℕ → ℝ := fun n ↦ if n = 0 then 0 else a n / (n : ℝ) ^ σ with htdef
  have ht : ∀ n, 0 ≤ t n := fun n ↦ by
    simp only [htdef]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (ha n) (by positivity)
  have hterm : ∀ n, LSeries.term (fun n ↦ (a n : ℂ)) σ n = (t n : ℂ) := term_ofReal a σ
  have h1 : ∑' n, ‖LSeries.term (fun n ↦ (a n : ℂ)) σ n‖ = ∑' n, t n := by
    refine tsum_congr fun n ↦ ?_
    rw [hterm, Complex.norm_of_nonneg (ht n)]
  rw [h1, LSeries, tsum_congr hterm, ← Complex.ofReal_tsum,
    Complex.norm_of_nonneg (tsum_nonneg ht)]

/-- The partial sums of a sequence bounded by `1` are at most `t`. -/
lemma norm_sum_le_of_norm_le_one {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1) (t : ℝ) (ht : 1 ≤ t) :
    ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, g k‖ ≤ 1 * t ^ (1 : ℝ) := by
  rw [Real.rpow_one, one_mul]
  calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, g k‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖g k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ hg k
    _ = ⌊t⌋₊ := by simp
    _ ≤ t := Nat.floor_le (by linarith)

/-- **`ζ(3/2) ≤ 3`**, by partial summation. -/
lemma zeta32_le : zeta32 ≤ 3 := by
  have e : zeta32 = ∑' n, ‖LSeries.term (fun n ↦ ((1 : ℝ) : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖ := by
    simp [zeta32]
  rw [e, tsum_norm_term_eq (fun _ ↦ zero_le_one)]
  have hS : LSeriesSummable (fun n ↦ ((1 : ℝ) : ℂ)) ((3 / 2 : ℝ) : ℂ) := by
    simpa using summable_one_32
  have h := norm_LSeries_le_of_sum_le zero_le_one (by norm_num : (1 : ℝ) < 3 / 2) hS
    (norm_sum_le_of_norm_le_one (fun n ↦ by simp))
  norm_num at h ⊢
  linarith

/-- **`−ζ′/ζ(3/2) ≤ 3(log 4 + 4)`**, by partial summation with Chebyshev's `ψ(t) ≤ (log 4 + 4)t`. -/
lemma logDerivZeta32_le : logDerivZeta32 ≤ 3 * (Real.log 4 + 4) := by
  have e : logDerivZeta32 = ∑' n, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
      ((3 / 2 : ℝ) : ℂ) n‖ := rfl
  rw [e, tsum_norm_term_eq (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg)]
  have hS : LSeriesSummable (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hb : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)‖ ≤
      (Real.log 4 + 4) * t ^ (1 : ℝ) := by
    intro t ht
    rw [Real.rpow_one, ← Complex.ofReal_sum, Complex.norm_of_nonneg
      (Finset.sum_nonneg fun k _ ↦ ArithmeticFunction.vonMangoldt_nonneg)]
    have h := Chebyshev.psi_le_const_mul_self (x := t) (by linarith)
    have e2 : Chebyshev.psi t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k := rfl
    rw [← e2]
    exact h
  have h := norm_LSeries_le_of_sum_le zero_le_one (by norm_num : (1 : ℝ) < 3 / 2) hS hb
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  calc _ ≤ 3 / 2 * (Real.log 4 + 4) / (3 / 2 - 1) := h
    _ = 3 * (Real.log 4 + 4) := by ring

lemma log_four_lt : Real.log 4 < 1.3863 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_lt_d9
  rw [h]
  linarith

lemma logDerivZeta32_le' : logDerivZeta32 ≤ 17 := by
  have h := logDerivZeta32_le
  have h4 := log_four_lt
  linarith

lemma log_zeta32_le : Real.log (2 + 36 * zeta32 / 11) ≤ 3 := by
  have hz := zeta32_le
  have hz0 : 0 ≤ zeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  rw [Real.log_le_iff_le_exp (by positivity)]
  have he := Real.exp_one_gt_d9
  have e3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
    calc (2.7182818283 : ℝ) ^ 3 = 2.7182818283 * 2.7182818283 * 2.7182818283 := by ring
      _ ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by gcongr
  rw [e3]
  nlinarith

/-! ### The constants at `θ = 11/12` -/

/-- **`Kld (11/12) (11/12 + e/4) ≤ 23000/e³`** for `0 < e ≤ 1/24`. -/
lemma Kld_le {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 24) :
    Kld (11 / 12) (11 / 12 + e / 4) ≤ 23000 / e ^ 3 := by
  have hr' : (3 / 2 - (11 / 12 + e / 4)) / (3 / 2 - 11 / 12) = 1 - 3 * e / 7 := by
    field_simp
    ring
  simp only [Kld]
  rw [hr', show (1 - 3 * e / 7) + (1 - (1 - 3 * e / 7)) / 4 = 1 - 9 * e / 28 by ring,
    show (1 - 3 * e / 7) + (1 - (1 - 3 * e / 7)) / 2 = 1 - 3 * e / 14 by ring,
    show (1 - 3 * e / 7) + 3 * (1 - (1 - 3 * e / 7)) / 4 = 1 - 3 * e / 28 by ring,
    show (1 - 9 * e / 28) - (1 - 3 * e / 7) = 3 * e / 28 by ring,
    show (3 : ℝ) / 2 - 11 / 12 = 7 / 12 by norm_num]
  set R : ℝ := 1 - 3 * e / 28 with hRdef
  set R' : ℝ := 1 - 3 * e / 14 with hR'def
  have hR'0 : 0 < R' := by rw [hR'def]; linarith
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hR1 : R ≤ 1 := by rw [hRdef]; linarith
  have hRR' : R - R' = 3 * e / 28 := by rw [hRdef, hR'def]; ring
  have hq : 0 < 3 * e / 28 := by positivity
  -- the second term
  have hA2den : (3 * e / 28) * (3 * e / 28) ≤ (R ^ 2 / R' - R') * Real.log (R / R') := by
    have h1 : 3 * e / 28 ≤ R ^ 2 / R' - R' := by
      rw [le_sub_iff_add_le, le_div_iff₀ hR'0]
      nlinarith
    have h2 : 3 * e / 28 ≤ Real.log (R / R') := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hR0 hR'0)
      rw [inv_div] at h
      have h3 : 1 - R' / R = (R - R') / R := by field_simp
      have h4 : R - R' ≤ (R - R') / R := by
        rw [le_div_iff₀ hR0]
        nlinarith
      linarith
    exact mul_le_mul h1 h2 hq.le (by linarith)
  have hA2 : 1 / ((R ^ 2 / R' - R') * Real.log (R / R')) ≤ 784 / 9 / e ^ 3 := by
    have hpos : 0 < (3 * e / 28) * (3 * e / 28) := by positivity
    calc 1 / ((R ^ 2 / R' - R') * Real.log (R / R')) ≤ 1 / ((3 * e / 28) * (3 * e / 28)) :=
          one_div_le_one_div_of_le hpos hA2den
      _ = 784 / 9 / e ^ 2 := by field_simp; ring
      _ ≤ 784 / 9 / e ^ 3 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith [pow_pos he0 2]
  -- the first term
  have hA1 : 16 * (1 - 9 * e / 28) ^ 2 / (3 * e / 28) ^ 3 ≤ 351232 / 27 / e ^ 3 := by
    have h1 : (1 - 9 * e / 28) ^ 2 ≤ 1 := by
      have : 0 ≤ 1 - 9 * e / 28 := by linarith
      nlinarith
    calc 16 * (1 - 9 * e / 28) ^ 2 / (3 * e / 28) ^ 3 ≤ 16 * 1 / (3 * e / 28) ^ 3 := by gcongr
      _ = 351232 / 27 / e ^ 3 := by field_simp; ring
  calc (16 * (1 - 9 * e / 28) ^ 2 / (3 * e / 28) ^ 3 +
        1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) / (7 / 12)
      ≤ (351232 / 27 / e ^ 3 + 784 / 9 / e ^ 3) / (7 / 12) := by gcongr
    _ = (351232 / 27 + 784 / 9) * (12 / 7) / e ^ 3 := by ring
    _ ≤ 23000 / e ^ 3 := by gcongr; norm_num

/-- **The Mellin constant of `ν₀` on the line `θ′ = 11/12 + e/4`** is at most `6750`, for `0 < e ≤ 1/24`. -/
lemma KM_le {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 24) :
    25 ^ (1 - e / 4) * 54 ^ (e / 4) * ((11 / 12 + e / 4) / 2) ^ (-(1 + e / 4)) ≤ 6750 := by
  have h1 : (25 : ℝ) ^ (1 - e / 4) ≤ 25 := by
    calc (25 : ℝ) ^ (1 - e / 4) ≤ 25 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 25 := Real.rpow_one 25
  have h2 : (54 : ℝ) ^ (e / 4) ≤ 54 := by
    calc (54 : ℝ) ^ (e / 4) ≤ 54 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 54 := Real.rpow_one 54
  set b : ℝ := (11 / 12 + e / 4) / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hb1 : b ≤ 1 := by rw [hbdef]; linarith
  have hb : 11 / 24 ≤ b := by rw [hbdef]; linarith
  have h3 : b ^ (-(1 + e / 4)) ≤ 5 := by
    calc b ^ (-(1 + e / 4)) ≤ b ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 (by linarith)
      _ = 1 / b ^ 2 := by
          rw [Real.rpow_neg hb0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            one_div]
      _ ≤ 5 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have h0a : 0 ≤ (25 : ℝ) ^ (1 - e / 4) := by positivity
  have h0b : 0 ≤ (54 : ℝ) ^ (e / 4) := by positivity
  have h0c : 0 ≤ b ^ (-(1 + e / 4)) := by positivity
  calc (25 : ℝ) ^ (1 - e / 4) * 54 ^ (e / 4) * b ^ (-(1 + e / 4)) ≤ 25 * 54 * 5 := by
        apply mul_le_mul (mul_le_mul h1 h2 h0b (by norm_num)) h3 h0c (by norm_num)
    _ = 6750 := by norm_num

lemma eta0_eq (η : ℝ) : eta0 (11 / 12) η = min η (1 / 24) := by
  simp only [eta0]
  norm_num

/-! ### `ψ(x, χ)` with an explicit constant -/

/-- **`ψ(x, χ)` uniformly in the modulus, with an explicit constant.** For every `η > 0`, with
`e = min(η, 1/24)`: `|ψ(x, χ)| ≤ (2·10¹¹/e⁵) log(N + 2)·x^{11/12+η}` for every Dirichlet
character `χ ≠ 1` mod `N` and every `x > 1`. -/
theorem psiChi_le_explicit {η : ℝ} (hη : 0 < η) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ x : ℝ, 1 < x → ‖psiChi χ x‖ ≤
        2 * 10 ^ 11 / (min η (1 / 24)) ^ 5 * Real.log (N + 2) * x ^ (11 / 12 + η) := by
  have he : eta0 (11 / 12) η = min η (1 / 24) := eta0_eq η
  set e : ℝ := eta0 (11 / 12) η with hedef
  rw [← he]
  have he0 : 0 < e := by rw [he]; exact lt_min hη (by norm_num)
  have he1 : e ≤ 1 / 24 := by rw [he]; exact min_le_right _ _
  set KM : ℝ := 25 ^ (1 - e / 4) * 54 ^ (e / 4) * ((11 / 12 + e / 4) / 2) ^ (-(1 + e / 4))
    with hKMdef
  have hKM0 : 0 ≤ KM := by positivity
  have hKM := mellin_ν₀_le_geom (κ := e / 4) (by positivity) (by linarith) (σ := 11 / 12 + e / 4)
    (by positivity) (by linarith)
  set K : ℝ := Kld (11 / 12) (11 / 12 + e / 4) with hKdef
  have hK0 : 0 < K := (logDeriv_le_uniform_of (θ := 11 / 12) (θ' := 11 / 12 + e / 4) (by norm_num)
    (by linarith) (by linarith)).1
  have hC₁ : 0 ≤ KM * (16 / e) * (K + 1) := by positivity
  have hC₂ : 0 ≤ KM * (16 / e) * (K * 4 ^ (e / 8) / (e / 8)) + 4 * (2 + 4 / e) := by positivity
  have hpsi := psiChi_le_uniform_of hC₁ hC₂ (sum_le_uniform_of (θ := 11 / 12) (by norm_num)
    (by norm_num) hη contDiff_ν₀ (fun x _ ↦ ν₀_nonneg x) support_ν₀ mass_ν₀ hKM0 hKM)
  intro N _ χ hχ x hx
  refine (hpsi N χ hχ x hx).trans ?_
  have hlog : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hxp : 0 ≤ x ^ (11 / 12 + η) := by positivity
  apply mul_le_mul_of_nonneg_right _ hxp
  apply mul_le_mul_of_nonneg_right _ hlog
  -- the constant
  set u : ℝ := 1 / e with hudef
  have hu : 24 ≤ u := by rw [hudef, le_div_iff₀ he0]; linarith
  have hu1 : 1 ≤ u := by linarith
  have hKu : K ≤ 23000 * u ^ 3 := by
    have := Kld_le he0 he1
    rw [hudef, div_pow, one_pow, ← div_eq_mul_one_div]
    exact this
  have hKM6 : KM ≤ 6750 := KM_le he0 he1
  have h4 : (4 : ℝ) ^ (e / 8) ≤ 4 := by
    calc (4 : ℝ) ^ (e / 8) ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have h16 : 16 / e = 16 * u := by rw [hudef]; ring
  have h8 : 1 / (e / 8) = 8 * u := by rw [hudef]; field_simp
  have h4e : 4 / e = 4 * u := by rw [hudef]; ring
  have he5 : 2 * 10 ^ 11 / e ^ 5 = 2 * 10 ^ 11 * u ^ 5 := by rw [hudef]; field_simp
  rw [h16, h4e, he5, div_eq_mul_one_div (K * 4 ^ (e / 8)), h8]
  have hc' := log_zeta32_le
  have hΛ := logDerivZeta32_le'
  have hz0 : 0 ≤ zeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hc'0 : 0 ≤ Real.log (2 + 36 * zeta32 / 11) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 36 * zeta32 / 11 by positivity])
  have hΛ0 : 0 ≤ logDerivZeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
  have hu4 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hu5 : u ^ 4 ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
  have hu15 : u ≤ u ^ 5 := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
  have h4e0 : 0 ≤ (4 : ℝ) ^ (e / 8) := by positivity
  -- `C₁ ≤ 6750·16·23001·u⁴`
  have hC₁le : KM * (16 * u) * (K + 1) ≤ 6750 * 16 * 23001 * u ^ 4 := by
    have h1 : K + 1 ≤ 23001 * u ^ 3 := by linarith
    calc KM * (16 * u) * (K + 1) ≤ 6750 * (16 * u) * (23001 * u ^ 3) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hKM6 (by positivity)) h1 (by positivity)
            (by positivity)
      _ = 6750 * 16 * 23001 * u ^ 4 := by ring
  -- `C₂ ≤ 6750·16·23000·4·8·u⁵ + 8 + 16u`
  have hC₂le : KM * (16 * u) * (K * 4 ^ (e / 8) * (8 * u)) + 4 * (2 + 4 * u) ≤
      6750 * 16 * 23000 * 4 * 8 * u ^ 5 + 8 + 16 * u := by
    have h1 : K * 4 ^ (e / 8) ≤ 23000 * u ^ 3 * 4 :=
      mul_le_mul hKu h4 h4e0 (by positivity)
    have h2 : K * 4 ^ (e / 8) * (8 * u) ≤ 23000 * u ^ 3 * 4 * (8 * u) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : KM * (16 * u) * (K * 4 ^ (e / 8) * (8 * u)) ≤
        6750 * (16 * u) * (23000 * u ^ 3 * 4 * (8 * u)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hKM6 (by positivity)) h2 (by positivity) (by positivity)
    have e1 : 6750 * (16 * u) * (23000 * u ^ 3 * 4 * (8 * u)) = 6750 * 16 * 23000 * 4 * 8 * u ^ 5 := by
      ring
    linarith
  have hsum : 1 + Real.log (2 + 36 * zeta32 / 11) + logDerivZeta32 ≤ 21 := by linarith
  have hsum0 : 0 ≤ 1 + Real.log (2 + 36 * zeta32 / 11) + logDerivZeta32 := by linarith
  calc KM * (16 * u) * (K + 1) * (1 + Real.log (2 + 36 * zeta32 / 11) + logDerivZeta32) +
        (KM * (16 * u) * (K * 4 ^ (e / 8) * (8 * u)) + 4 * (2 + 4 * u))
      ≤ 6750 * 16 * 23001 * u ^ 4 * 21 + (6750 * 16 * 23000 * 4 * 8 * u ^ 5 + 8 + 16 * u) := by
        apply add_le_add _ hC₂le
        exact mul_le_mul hC₁le hsum hsum0 (by positivity)
    _ ≤ 2 * 10 ^ 11 * u ^ 5 := by nlinarith

/-! ### Littlewood's bounds with explicit constants -/

lemma min_24 : min (1 / 24 : ℝ) (1 / 24) = 1 / 24 := min_self _

/-- **`|L′/L(σ, χ)| ≤ 10²¹ log log(N + 16)` on `(1, 2]`.** -/
theorem logDeriv_le_explicit :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        ‖deriv (DirichletCharacter.LFunction χ) σ / DirichletCharacter.LFunction χ σ‖ ≤
          10 ^ 21 * Real.log (Real.log (N + 16)) := by
  have hψ := psiChi_le_explicit (η := 1 / 24) (by norm_num)
  rw [min_24] at hψ
  have hC : (0 : ℝ) ≤ 2 * 10 ^ 11 / (1 / 24) ^ 5 := by positivity
  have hb := logDeriv_le_loglog_of hC fun N _ χ _ hχ ↦ hψ N χ hχ
  intro N _ χ hq hχ σ hσ1 hσ2
  refine (hb N χ hq hχ σ hσ1 hσ2).trans ?_
  have hℓ : 0 ≤ Real.log (Real.log (N + 16)) := by linarith [one_lt_loglog N]
  apply mul_le_mul_of_nonneg_right _ hℓ
  have h4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h0 : 0 ≤ Real.log 4 + 4 + 2 * 10 ^ 11 / (1 / 24 : ℝ) ^ 5 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  calc 48 * (Real.log 4 + 4 + 2 * 10 ^ 11 / (1 / 24) ^ 5) * Real.exp 1
      ≤ 48 * (2 + 4 + 2 * 10 ^ 11 / (1 / 24) ^ 5) * 3 := by
        apply mul_le_mul (by linarith) he.le he0.le (by positivity)
    _ ≤ 10 ^ 21 := by norm_num

/-- **Littlewood's bound with an explicit constant**:
`|log |L(1, χ)|| ≤ log log log(N + 16) + 2·10²¹`. -/
theorem abs_log_norm_LFunction_one_le_explicit :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      |Real.log ‖DirichletCharacter.LFunction χ 1‖| ≤
        Real.log (Real.log (Real.log (N + 16))) + 2 * 10 ^ 21 := by
  intro N _ χ hq hχ
  refine (abs_log_norm_LFunction_one_le_of logDeriv_le_explicit N χ hq hχ).trans ?_
  have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  linarith

/-- **`|L(1, χ)| ≤ e^{2·10²¹} log log(N + 16)`** for every quadratic `χ ≠ 1` mod `N`. -/
theorem norm_LFunction_one_le_explicit :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ 1‖ ≤ Real.exp (2 * 10 ^ 21) * Real.log (Real.log (N + 16)) :=
  norm_LFunction_one_le_of abs_log_norm_LFunction_one_le_explicit

/-- **`|L(1, χ)| ≥ e^{−2·10²¹}/log log(N + 16)`** for every quadratic `χ ≠ 1` mod `N`. -/
theorem norm_LFunction_one_ge_explicit :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      Real.exp (-(2 * 10 ^ 21)) / Real.log (Real.log (N + 16)) ≤
        ‖DirichletCharacter.LFunction χ 1‖ :=
  norm_LFunction_one_ge_of abs_log_norm_LFunction_one_le_explicit

/-- **`|L′/L(1, χ)| ≤ 10²¹ log log(N + 16)`** for every quadratic `χ ≠ 1` mod `N`. -/
theorem norm_logDeriv_one_le_explicit :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        10 ^ 21 * Real.log (Real.log (N + 16)) :=
  norm_logDeriv_one_le_of logDeriv_le_explicit

/-! ### The least primes with `χ(p) = ±1` and the least quadratic nonresidue, with explicit constants -/

/-- **The least primes with `χ(p) = ±1`, with an explicit constant, for every `A > 12`.** With
`e = min(1/12 − 1/A, 1/24)` and `K = 4(2·10¹¹/e⁵ + 11)`, every quadratic Dirichlet character `χ ≠ 1` mod `q`
has, for `ε = 1` and for `ε = −1`, a prime `p ∤ q` with `χ(p) = ε` and `p ≤ (101 + K^A)(log(q + 2))^A`. -/
theorem exists_prime_eq_explicit {A : ℝ} (hA : 12 < A) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsQuadratic → χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) →
        ∃ p : ℕ, p.Prime ∧ ¬ p ∣ q ∧ χ p = ε ∧
          (p : ℝ) ≤ (101 + (4 * (2 * 10 ^ 11 / (min (1 / 12 - 1 / A) (1 / 24)) ^ 5 + 11)) ^ A) *
            Real.log (q + 2) ^ A := by
  have hA0 : 0 < A := by linarith
  have hiA : 1 / A < 1 / 12 := by
    rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  have hψ := psiChi_le_explicit (η := 1 / 12 - 1 / A) (by linarith)
  have hm : 0 < min (1 / 12 - 1 / A) (1 / 24 : ℝ) := lt_min (by linarith) (by norm_num)
  have hK : 0 < 4 * (2 * 10 ^ 11 / (min (1 / 12 - 1 / A) (1 / 24 : ℝ)) ^ 5 + 11) := by positivity
  exact exists_prime_eq_of hA0 hK fun q _ χ _ hχ ↦ rpow_le_of_forall_eq_of hA hψ q χ hχ

set_option exponentiation.threshold 400 in
/-- **The least primes with `χ(p) = ±1`, at `A = 13`**: every quadratic Dirichlet character `χ ≠ 1` mod `q`
has, for `ε = ±1`, a prime `p ∤ q` with `χ(p) = ε` and `p ≤ 10²⁹⁸(log(q + 2))¹³`. -/
theorem exists_prime_eq_13 :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsQuadratic → χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) →
        ∃ p : ℕ, p.Prime ∧ ¬ p ∣ q ∧ χ p = ε ∧ (p : ℝ) ≤ 10 ^ 298 * Real.log (q + 2) ^ 13 := by
  intro q _ χ hq hχ ε hε
  obtain ⟨p, hp, hpq, hχp, hple⟩ := exists_prime_eq_explicit (A := 13) (by norm_num) q χ hq hχ hε
  refine ⟨p, hp, hpq, hχp, hple.trans ?_⟩
  have hm : min (1 / 12 - 1 / 13 : ℝ) (1 / 24) = 1 / 156 := by norm_num
  rw [hm]
  have hlog : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have e13 : (13 : ℝ) = ((13 : ℕ) : ℝ) := by norm_num
  rw [e13, Real.rpow_natCast, Real.rpow_natCast]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  norm_num

/-- **The least quadratic nonresidue, with an explicit constant, for every `A > 12`.** With
`e = min(1/12 − 1/A, 1/24)` and `K = 4(2·10¹¹/e⁵ + 11)`, every odd prime `p` has a quadratic nonresidue
`n ≤ (101 + K^A)2^A (log p)^A`. -/
theorem exists_nonsquare_le_explicit {A : ℝ} (hA : 12 < A) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ n : ℕ, 0 < n ∧
      (n : ℝ) ≤ (101 + (4 * (2 * 10 ^ 11 / (min (1 / 12 - 1 / A) (1 / 24)) ^ 5 + 11)) ^ A) *
        2 ^ A * Real.log p ^ A ∧ ¬ IsSquare (n : ZMod p) := by
  have hA0 : 0 < A := by linarith
  have hiA : 1 / A < 1 / 12 := by
    rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  have hm : 0 < min (1 / 12 - 1 / A) (1 / 24 : ℝ) := lt_min (by linarith) (by norm_num)
  exact exists_nonsquare_le_of hA0 (by positivity) (exists_prime_eq_explicit hA)

set_option exponentiation.threshold 400 in
/-- **`n(p) ≤ 10³⁰⁴ (log p)¹³`** for every odd prime `p`. -/
theorem exists_nonsquare_le_13 :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 10 ^ 304 * Real.log p ^ 13 ∧ ¬ IsSquare (n : ZMod p) := by
  intro p hp hp2
  obtain ⟨n, hn0, hnle, hns⟩ := exists_nonsquare_le_explicit (A := 13) (by norm_num) p hp hp2
  refine ⟨n, hn0, hnle.trans ?_, hns⟩
  have hm : min (1 / 12 - 1 / 13 : ℝ) (1 / 24) = 1 / 156 := by norm_num
  rw [hm]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have e13 : (13 : ℝ) = ((13 : ℕ) : ℝ) := by norm_num
  rw [e13, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  norm_num

/-- **`n(p) ≤ 10³⁰⁴(13/δ)¹³p^δ`** for every odd prime `p` and every `δ > 0`. -/
theorem exists_nonsquare_le_rpow_explicit {δ : ℝ} (hδ : 0 < δ) :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 10 ^ 304 * (13 / δ) ^ 13 * (p : ℝ) ^ δ ∧ ¬ IsSquare (n : ZMod p) := by
  have h13 : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 10 ^ 304 * Real.log p ^ (13 : ℝ) ∧ ¬ IsSquare (n : ZMod p) := by
    intro p hp hp2
    obtain ⟨n, hn0, hnle, hns⟩ := exists_nonsquare_le_13 p hp hp2
    refine ⟨n, hn0, ?_, hns⟩
    rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hnle
  intro p hp hp2
  obtain ⟨n, hn0, hnle, hns⟩ := exists_nonsquare_le_rpow_of (by positivity) h13 hδ p hp hp2
  refine ⟨n, hn0, ?_, hns⟩
  rwa [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hnle

end ExplicitConstants
