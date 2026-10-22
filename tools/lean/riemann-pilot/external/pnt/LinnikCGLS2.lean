/-
# Round 644: `CGLS2` (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 639 split round 638's hypothesis on the cubic trace into two displayed hypotheses, `CGLS2` (the off-diagonal
mass of the Gram matrix, Chen–Gupta–Li's Proposition 6.1 at one point per character) and `CGLS3` (their
Proposition 11.1). This file proves `CGLS2` (`cgls2`), from round 643's explicit bound `LinnikCGLFrob.frobOff_le`, by
choosing its parameters and bounding each factor by a power of `qT`. Linnik's exponents `9/4` and `226/100` then
follow from `CGLS3` alone (`linnik_225c_s3`, `linnik_226c_s3`).

Plain statement (`cgls2`). For every `ε > 0` there is `C ≥ 0` such that, for `χ` injective on `R`, `T ≥ 1`,
`7/10 ≤ σ ≤ 4/5`, `(qT)^{2/3}/2 ≤ N ≤ qT`, `S ⊆ [6N/5, 9N/5]`, `|b_n| ≤ 1`, `|t_i| ≤ T` and
`|Σ_{n∈S}b_nχ_i(n)n^{it_i}| ≥ N^σ/6` for every `i ∈ R`, `‖E‖_F² ≤ C(qTN)^ε·qT|R|N^{2−2σ}`.

Plain statement (`s2_main`). For `N > 5/6` and `0 < δ ≤ 1/16`, `‖E‖_F² ≤ (C₁(δ) + C₂(δ))(qT)^{1+16δ}|R|N^{2−2σ}`.
The parameters: `P = qT`, `u = P^δ`, `N′ = ⌊9N/5⌋`, `Z = ⌊3Pu/N⌋ + 1`, `K = ⌈4/δ⌉` and `τ = C_δ(N′Z)^δ`.

The paper's own count: "S₂ ⪅_ε (|W|N^{2−2σ}/M)(N²M² + qTNM) ⪅_ε qT|W|N^{3−2σ}, since NM ⪅_ε qT" (the end of their
proof of Proposition 6.1, spaces restored and the fraction written on one line). Here `NZ` plays their `NM`, and
`‖E‖_F²` carries one power of `N` less than `S₂ = 3μ₀‖E‖_F²`.

* `AL`, `natLog_le_two_log`, `LSX_le`: round 526's large-sieve factor is at most `A(δ)(q(2T + 1) + X)X^δ`, from
  `log x ≤ x^{δ/4}/(δ/4)` (Mathlib's `Real.log_le_rpow_div`).
* `HZ_le`: `H_Z ≤ Z^δ/δ` (`SquarefreeCount.sum_rpow_neg_le`).
* `two_pow_omega_le`, `EQh_le`, `Q0_le`: `2^{ω(q)} ≤ C_δq^δ` (round 526's `card_powerset_le_divisors` and the stack's
  divisor bound `card_divisors_le`), `EQh(q) ≤ 4^{ω(q)}`, and so `Q₀(q) ≤ π·CGK(0)·(2^{ω(q)})³`.
* `card_mul_sq_le`, `card_le`: `|R|V² ≤ L(N′)Σ|b_n|²` (round 643's `ls_points` for the large polynomial itself), and
  so `|R| ≪_δ PuN^{1−2σ}`.
* `pv_point_eq`, `rpow_le_of_le_mul`: the large polynomial as round 526's `pv`, and `x^δ ≤ c(P^δ)²` for
  `x ≤ cP^{1+δ}`.
* `Bmax_le`: round 642's tail bound is `≪_δ u³P^{−3}`, since `NZ ≥ 3Pu ≥ q(1 + 2T)u` and `u^K ≥ P⁴`.
* `Kd`, `C1`, `C2`, `main_term_le`, `tail_le`, `s2_main`: the two terms of `frobOff_le` as powers of `P`.
* `char_eq_of_le_two`, `frobOff_eq_zero_of_le_two`, `q_le_two`: for `N ≤ 5/6` (where `S` may contain `1`, outside
  the large sieve's support `[2, X]`), `q ≤ 2`, there is one character mod `q` (`φ(q) = 1`), and `‖E‖_F² = 0`.
* `cgls2`: `s2_main` at `δ = min(ε, 1)/16`, with `(qT)^{min(ε,1)} ≤ (6/5)^ε(qTN)^ε`.
* `linnik_225c_s3`, `linnik_226c_s3`: round 639's `linnik_225c_s23` and `linnik_226c_s23` with `cgls2`.

The file imports `LinnikCGLFrob.lean`.
-/

import LinnikCGLFrob

open Complex Set Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikCGLS2

open LinnikCGLMat LinnikCGLS23 LinnikCGLMellin LinnikCGLReflect LinnikCGLPair LinnikCGLFrob DirichletCharacter
  LinnikReflect LinnikPower

/-! ### Sizes -/

/-- The constant `A(δ) = e(8 + 32/δ)(2 + 64/δ²)(1 + 8/δ)` of `LSX_le`. -/
def AL (δ : ℝ) : ℝ := Real.exp 1 * ((8 + 32 / δ) * (2 + 64 / δ ^ 2)) * (1 + 8 / δ)

lemma AL_pos {δ : ℝ} (hδ : 0 < δ) : 0 < AL δ := by unfold AL; positivity

/-- `log₂ X ≤ 2 log X` for `X ≥ 1`. -/
lemma natLog_le_two_log {X : ℕ} (hX : 1 ≤ X) : (Nat.log 2 X : ℝ) ≤ 2 * Real.log X := by
  have h1 : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ) ^ Nat.log 2 X) ≤ X := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 X) ≤ Real.log X := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 := Real.log_two_gt_d9
  have h5 : (0 : ℝ) ≤ Nat.log 2 X := Nat.cast_nonneg _
  nlinarith

/-- **The large-sieve factor as a power**: `L(X) ≤ A(δ)(q(2T + 1) + X)X^δ` for `X ≥ 1`, `T ≥ 0` and `0 < δ ≤ 1`,
from `log x ≤ x^{δ/4}/(δ/4)` (Mathlib's `Real.log_le_rpow_div`). -/
lemma LSX_le (q : ℕ) {T : ℝ} (hT : 0 ≤ T) {X : ℕ} (hX : 1 ≤ X) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    LSX q T X ≤ AL δ * ((q : ℝ) * (2 * T + 1) + X) * (X : ℝ) ^ δ := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  set e := δ / 4 with he
  have he0 : 0 < e := by positivity
  set y := (X : ℝ) ^ e with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hX1 he0.le
  have hl : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hl2 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have h1 : Real.log X ≤ y / e := Real.log_le_rpow_div hX0.le he0
  have h2 : Real.log (2 * X) ≤ (2 * X : ℝ) ^ e / e := Real.log_le_rpow_div (by positivity) he0
  have h2e : (2 * X : ℝ) ^ e ≤ 2 * y := by
    rw [Real.mul_rpow (by norm_num) hX0.le]
    gcongr
    calc (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hye : y / e = 4 / δ * y := by rw [he]; field_simp
  -- the three factors
  have hA : 8 + 8 * Real.log X ≤ (8 + 32 / δ) * y := by
    have : 8 * Real.log X ≤ 32 / δ * y := by
      have h8 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 8)
      rw [hye, show 8 * (4 / δ * y) = 32 / δ * y by ring] at h8; exact h8
    nlinarith
  have hB : 2 + Real.log (2 * X) ^ 2 ≤ (2 + 64 / δ ^ 2) * y ^ 2 := by
    have hb1 : Real.log (2 * X) ≤ 8 / δ * y := by
      calc Real.log (2 * X) ≤ (2 * X : ℝ) ^ e / e := h2
        _ ≤ 2 * y / e := by gcongr
        _ = 8 / δ * y := by rw [he]; field_simp; ring
    have hb2 : Real.log (2 * X) ^ 2 ≤ (8 / δ * y) ^ 2 := pow_le_pow_left₀ hl2 hb1 2
    have hb3 : (8 / δ * y) ^ 2 = 64 / δ ^ 2 * y ^ 2 := by field_simp; ring
    have hb4 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
    nlinarith
  have hC : (Nat.log 2 X : ℝ) + 1 ≤ (1 + 8 / δ) * y := by
    have hc1 := natLog_le_two_log hX
    have : 2 * Real.log X ≤ 8 / δ * y := by
      have h8 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
      rw [hye, show 2 * (4 / δ * y) = 8 / δ * y by ring] at h8; exact h8
    nlinarith
  have hQ : (q : ℝ) * (2 * T + 1) + 8 * X * (1 + Real.log X) ≤ ((q : ℝ) * (2 * T + 1) + X) * (8 + 8 * Real.log X) := by
    have : 0 ≤ (q : ℝ) * (2 * T + 1) := by positivity
    nlinarith
  have hyδ : y ^ 4 = (X : ℝ) ^ δ := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; congr 1; rw [he]; push_cast; ring
  unfold LSX
  have hQX : 0 ≤ (q : ℝ) * (2 * T + 1) + X := by positivity
  have hp1 : 0 ≤ 8 + 8 * Real.log X := by positivity
  have hp2 : 0 ≤ 2 + Real.log (2 * X) ^ 2 := by positivity
  calc Real.exp 1 * (((q : ℝ) * (2 * T + 1) + 8 * X * (1 + Real.log X)) * (2 + Real.log (2 * X) ^ 2)) *
        ((Nat.log 2 X : ℝ) + 1)
      ≤ Real.exp 1 * ((((q : ℝ) * (2 * T + 1) + X) * (8 + 8 * Real.log X)) * (2 + Real.log (2 * X) ^ 2)) *
        ((Nat.log 2 X : ℝ) + 1) := by gcongr
    _ ≤ Real.exp 1 * ((((q : ℝ) * (2 * T + 1) + X) * ((8 + 32 / δ) * y)) * ((2 + 64 / δ ^ 2) * y ^ 2)) *
        ((1 + 8 / δ) * y) := by gcongr
    _ = AL δ * ((q : ℝ) * (2 * T + 1) + X) * y ^ 4 := by unfold AL; ring
    _ = AL δ * ((q : ℝ) * (2 * T + 1) + X) * (X : ℝ) ^ δ := by rw [hyδ]

/-- `H_Z ≤ Z^δ/δ` for `0 < δ < 1` (`SquarefreeCount.sum_rpow_neg_le` at `β = 1 − δ`, and `1/m ≤ m^{δ−1}`). -/
lemma HZ_le (Z : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : HZ Z ≤ (Z : ℝ) ^ δ / δ := by
  have h := SquarefreeCount.sum_rpow_neg_le (β := 1 - δ) (by linarith) (by linarith) Z
  rw [show 1 - (1 - δ) = δ by ring] at h
  have hI : Finset.Icc 1 Z = Finset.Ioc 0 Z := by ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  unfold HZ
  rw [hI]
  refine le_trans (Finset.sum_le_sum fun m hm => ?_) h
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ioc.1 hm).1
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

/-- `2^{ω(q)} ≤ C_δq^δ` (round 526's `card_powerset_le_divisors` and the stack's divisor bound). -/
lemma two_pow_omega_le (q : ℕ) [NeZero q] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ q.primeFactors.card ≤ Cdiv δ * (q : ℝ) ^ δ := by
  have h1 := LinnikTwelve.card_powerset_le_divisors q
  rw [Finset.card_powerset] at h1
  push_cast at h1
  exact h1.trans (card_divisors_le hδ hδ1 q)

/-- `EQh(q) ≤ 4^{ω(q)}`: each factor `(1 − p^{−1/2})⁻¹` is at most `4`. -/
lemma EQh_le (q : ℕ) : EQh q ≤ ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
  have e : ((2 : ℝ) ^ q.primeFactors.card) ^ 2 = ∏ _p ∈ q.primeFactors, (4 : ℝ) := by
    rw [Finset.prod_const, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]
  unfold EQh
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    exact inv_nonneg.2 (by linarith)
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    set y := (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hy
    have hy0 : 0 < y := by positivity
    have hy2 : y ^ 2 = 1 / 2 := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hy3 : y ≤ 3 / 4 := by nlinarith
    have h2 : 1 / 4 ≤ 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith

/-- `Q₀(q) ≤ π·CGK(0)·(2^{ω(q)})³`. -/
lemma Q0_le (q : ℕ) : Q0 q ≤ Real.pi * CGK 0 * ((2 : ℝ) ^ q.primeFactors.card) ^ 3 := by
  unfold Q0
  have h := EQh_le q
  have hC := CGK_pos 0
  calc 2 ^ q.primeFactors.card * (Real.pi * CGK 0) * EQh q
      ≤ 2 ^ q.primeFactors.card * (Real.pi * CGK 0) * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by gcongr
    _ = Real.pi * CGK 0 * ((2 : ℝ) ^ q.primeFactors.card) ^ 3 := by ring

/-! ### The number of large values, and one character -/

/-- **The number of large values**: `|R|V² ≤ L(N′)Σ|b_n|²` (`ls_points` for `F` itself). -/
lemma card_mul_sq_le {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) {t : ι → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ht : ∀ i ∈ R, |t i| ≤ T) {S : Finset ℕ} {N' : ℕ} (hS : S ⊆ Finset.Icc 2 N') (b : ℕ → ℂ) {V : ℝ}
    (hV : 0 ≤ V) (hbig : ∀ i ∈ R, V ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖) :
    (R.card : ℝ) * V ^ 2 ≤ LSX q T N' * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  calc (R.card : ℝ) * V ^ 2 = ∑ _i ∈ R, V ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ R, ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ ^ 2 :=
        Finset.sum_le_sum fun i hi => pow_le_pow_left₀ hV (hbig i hi) 2
    _ ≤ LSX q T N' * ∑ n ∈ S, ‖b n‖ ^ 2 := ls_points hinj hT ht hS b

/-- For `q ≤ 2` there is one character mod `q`: `(ℤ/q)ˣ` has `φ(q) = 1` element. -/
lemma char_eq_of_le_two {q : ℕ} [NeZero q] (hq : q ≤ 2) (χ ψ : DirichletCharacter ℂ q) : χ = ψ := by
  have hcard : Fintype.card (ZMod q)ˣ ≤ 1 := by
    rw [ZMod.card_units_eq_totient]
    have hq0 : q ≠ 0 := NeZero.ne q
    interval_cases q <;> simp
  have hsub : Subsingleton (ZMod q)ˣ := Fintype.card_le_one_iff_subsingleton.1 hcard
  refine MulChar.ext fun a => ?_
  rw [Subsingleton.elim a 1, Units.val_one, MulChar.map_one, MulChar.map_one]

/-- With one character and `χ` injective on `R`, `‖E‖_F² = 0`. -/
lemma frobOff_eq_zero_of_le_two {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] (hq : q ≤ 2) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (N : ℝ) (t : ι → ℝ) : frobOff N R χ t = 0 := by
  unfold frobOff
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k hk => ?_
  have : i = k := hinj (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hk) (char_eq_of_le_two hq _ _)
  simp [this]

/-! ### `CGLS2` -/

/-- The large polynomial at a point, as round 526's `pv`. -/
lemma pv_point_eq {q : ℕ} (S : Finset ℕ) (b : ℕ → ℂ) (ψ : DirichletCharacter ℂ q) (x : ℝ) :
    pv S b ψ (((0 : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * I) = ∑ n ∈ S, b n * ψ n * (n : ℂ) ^ ((x : ℂ) * I) := by
  unfold pv
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 2
  push_cast; ring

/-- `x^δ ≤ c(P^δ)²` when `0 ≤ x ≤ c·P·P^δ`, `c, P ≥ 1` and `0 ≤ δ ≤ 1`. -/
lemma rpow_le_of_le_mul {x c P δ : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) (hP : 1 ≤ P) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : x ≤ c * (P * P ^ δ)) : x ^ δ ≤ c * (P ^ δ) ^ 2 := by
  have hP0 : 0 < P := by linarith
  have hu1 : 1 ≤ P ^ δ := Real.one_le_rpow hP hδ0
  have h1 : c ^ δ ≤ c := by
    calc c ^ δ ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hδ1
      _ = c := Real.rpow_one c
  have h2 : (P ^ δ) ^ δ ≤ P ^ δ := by
    calc (P ^ δ) ^ δ ≤ (P ^ δ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 hδ1
      _ = P ^ δ := Real.rpow_one _
  calc x ^ δ ≤ (c * (P * P ^ δ)) ^ δ := Real.rpow_le_rpow hx h hδ0
    _ = c ^ δ * (P ^ δ * (P ^ δ) ^ δ) := by
        rw [Real.mul_rpow (by linarith) (by positivity), Real.mul_rpow hP0.le (by positivity)]
    _ ≤ c * (P ^ δ * P ^ δ) := by
        have : 0 ≤ (P ^ δ) ^ δ := by positivity
        have : 0 ≤ c ^ δ := by positivity
        gcongr
    _ = c * (P ^ δ) ^ 2 := by ring

/-- `K(δ) = ⌈4/δ⌉`. -/
def Kd (δ : ℝ) : ℕ := ⌈4 / δ⌉₊

/-- The constant of the main term. -/
def C1 (δ : ℝ) : ℝ :=
  (Real.pi * CGK 0) ^ 2 * Cdiv δ ^ 7 * IH ^ 2 * AL δ * (36 * 11 * (36 / 5) * (36 / 5) * (9 / 5) * 5 / δ)

/-- The constant of the tails. -/
def C2 (δ : ℝ) : ℝ :=
  AL δ * (Real.pi * CGK (Kd δ) * IK (Kd δ)) ^ 2 * Cdiv δ ^ 6 * (5 * 2 * (9 / 5) * 36 * 4 * 9 * (6 / 5))

lemma C1_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ C1 δ := by
  have := CGK_pos 0; have := AL_pos hδ; have : 0 < Cdiv δ := by linarith [one_le_Cdiv hδ hδ1]
  unfold C1; positivity

lemma C2_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ C2 δ := by
  have := AL_pos hδ; have : 0 < Cdiv δ := by linarith [one_le_Cdiv hδ hδ1]
  unfold C2; positivity

/-- **The tail bound as a power of `P`**: with `P = qT`, `u = P^δ`, `NZ ≥ 3Pu`, `δK ≥ 4` and `T ≥ 1`,
`B ≤ 2(C_δu)³·π·CGK(K)·I_K·3P·P^{−4}`. -/
lemma Bmax_le {q : ℕ} [NeZero q] {N T P u δ : ℝ} {Z K : ℕ} (hT : 1 ≤ T) (hN0 : 0 < N) (hP : P = (q : ℝ) * T)
    (hu : u = P ^ δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hZ1 : 1 ≤ Z) (hNZ : 3 * P * u ≤ N * Z) (hδK : 4 ≤ δ * K) :
    Bmax q N T Z K ≤ 2 * (Cdiv δ * u) ^ 3 * (Real.pi * CGK K * IK K) * (3 * P * (P ^ 4)⁻¹) := by
  have hT0 : 0 ≤ T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hP1 : 1 ≤ P := by rw [hP]; exact one_le_mul_of_one_le_of_one_le hq1 hT
  have hP0 : 0 < P := by linarith
  have hqP : (q : ℝ) ≤ P := by rw [hP]; exact le_mul_of_one_le_right (by positivity) hT
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_rpow hP1 hδ0.le
  have hu0 : 0 < u := by linarith
  have hCd0 : 0 < Cdiv δ := by linarith [one_le_Cdiv hδ0 hδ1]
  have hqδ : (q : ℝ) ^ δ ≤ u := by rw [hu]; exact Real.rpow_le_rpow (by linarith) hqP hδ0.le
  have hω : (2 : ℝ) ^ q.primeFactors.card ≤ Cdiv δ * u :=
    (two_pow_omega_le q hδ0 hδ1).trans (mul_le_mul_of_nonneg_left hqδ hCd0.le)
  have h2ω : (2 : ℝ) ^ (q.primeFactors.card + 1) * EQh q ≤ 2 * (Cdiv δ * u) ^ 3 := by
    have hE := EQh_le q
    rw [pow_succ]
    calc (2 : ℝ) ^ q.primeFactors.card * 2 * EQh q
        ≤ 2 ^ q.primeFactors.card * 2 * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by gcongr
      _ = 2 * ((2 : ℝ) ^ q.primeFactors.card) ^ 3 := by ring
      _ ≤ 2 * (Cdiv δ * u) ^ 3 := by gcongr
  have hcore : (q : ℝ) ^ ((K : ℝ) + 1 / 2) * (N * Z) ^ (-(K : ℝ)) * (1 + 2 * T) ^ (K + 1) ≤
      3 * P * (P ^ 4)⁻¹ := by
    have hZ0 : (0 : ℝ) < Z := by exact_mod_cast hZ1
    have hNZ0 : 0 < N * Z := mul_pos hN0 hZ0
    have e1 : (q : ℝ) ^ ((K : ℝ) + 1 / 2) = (q : ℝ) ^ K * (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_add hq0, Real.rpow_natCast]
    have e2 : (N * Z) ^ (-(K : ℝ)) = ((N * Z) ^ K)⁻¹ := by
      rw [Real.rpow_neg hNZ0.le, Real.rpow_natCast]
    have e3 : (q : ℝ) ^ K * (q : ℝ) ^ (1 / 2 : ℝ) * ((N * Z) ^ K)⁻¹ * (1 + 2 * T) ^ (K + 1) =
        ((q : ℝ) * (1 + 2 * T) / (N * Z)) ^ K * ((q : ℝ) ^ (1 / 2 : ℝ) * (1 + 2 * T)) := by
      rw [div_pow, mul_pow (q : ℝ) (1 + 2 * T) K, pow_succ, div_eq_mul_inv]; ring
    rw [e1, e2, e3]
    have hq3 : (q : ℝ) * (1 + 2 * T) ≤ 3 * P := by
      have e : (q : ℝ) * (1 + 2 * T) = q + 2 * P := by rw [hP]; ring
      rw [e]; linarith
    have hr : (q : ℝ) * (1 + 2 * T) / (N * Z) ≤ u⁻¹ := by
      rw [div_le_iff₀ hNZ0]
      calc (q : ℝ) * (1 + 2 * T) ≤ 3 * P := hq3
        _ = u⁻¹ * (3 * P * u) := by field_simp
        _ ≤ u⁻¹ * (N * Z) := by gcongr
    have huK : P ^ 4 ≤ u ^ K := by
      rw [hu, ← Real.rpow_natCast (P ^ δ), ← Real.rpow_mul hP0.le, ← Real.rpow_natCast P 4]
      exact Real.rpow_le_rpow_of_exponent_le hP1 (by rw [Nat.cast_ofNat]; exact hδK)
    have hrK : ((q : ℝ) * (1 + 2 * T) / (N * Z)) ^ K ≤ (P ^ 4)⁻¹ := by
      calc ((q : ℝ) * (1 + 2 * T) / (N * Z)) ^ K ≤ (u⁻¹) ^ K := pow_le_pow_left₀ (by positivity) hr K
        _ = (u ^ K)⁻¹ := inv_pow u K
        _ ≤ (P ^ 4)⁻¹ := inv_anti₀ (by positivity) huK
    have hq2 : (q : ℝ) ^ (1 / 2 : ℝ) * (1 + 2 * T) ≤ 3 * P := by
      have h1 : (q : ℝ) ^ (1 / 2 : ℝ) ≤ q := by
        calc (q : ℝ) ^ (1 / 2 : ℝ) ≤ (q : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
          _ = q := Real.rpow_one _
      calc (q : ℝ) ^ (1 / 2 : ℝ) * (1 + 2 * T) ≤ q * (1 + 2 * T) := mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ 3 * P := hq3
    calc ((q : ℝ) * (1 + 2 * T) / (N * Z)) ^ K * ((q : ℝ) ^ (1 / 2 : ℝ) * (1 + 2 * T)) ≤
          (P ^ 4)⁻¹ * (3 * P) := mul_le_mul hrK hq2 (by positivity) (by positivity)
      _ = 3 * P * (P ^ 4)⁻¹ := by ring
  have e : Bmax q N T Z K = ((2 : ℝ) ^ (q.primeFactors.card + 1) * EQh q) * (Real.pi * CGK K * IK K) *
      ((q : ℝ) ^ ((K : ℝ) + 1 / 2) * (N * Z) ^ (-(K : ℝ)) * (1 + 2 * T) ^ (K + 1)) := by unfold Bmax; ring
  rw [e]
  have := CGK_pos K; have := IK_nonneg K; have := EQh_pos q
  gcongr

/-- **The number of large values as a power of `P`**: under the hypotheses of `CGLS2` with `N > 5/6`, and with
`P = qT`, `u = P^δ` and `N′ ≤ 2P`, `|R| ≤ A(δ)·5P·2u·(9/5)N·36N^{−2σ}` (`card_mul_sq_le` and `LSX_le`). -/
lemma card_le {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι} {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) {t : ι → ℝ} {T N σ P u δ : ℝ} (hT : 1 ≤ T) (hN0 : 0 < N) (hP : P = (q : ℝ) * T)
    (hu : u = P ^ δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : ∀ i ∈ R, |t i| ≤ T) {S : Finset ℕ} {N' : ℕ}
    (hS : S ⊆ Finset.Icc 2 N') (hN'1 : 1 ≤ N') (hN'P : (N' : ℝ) ≤ 2 * P) {b : ℕ → ℂ}
    (hSb : ∑ n ∈ S, ‖b n‖ ^ 2 ≤ 9 / 5 * N)
    (hbig : ∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) :
    (R.card : ℝ) ≤ AL δ * (5 * P) * (2 * u) * (9 / 5 * N) * (36 * ((N ^ σ) ^ 2)⁻¹) := by
  have hT0 : 0 ≤ T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hP1 : 1 ≤ P := by rw [hP]; exact one_le_mul_of_one_le_of_one_le hq1 hT
  have hP0 : 0 < P := by linarith
  have hqP : (q : ℝ) ≤ P := by rw [hP]; exact le_mul_of_one_le_right (by positivity) hT
  have hu0 : 0 < u := by rw [hu]; positivity
  have hAL := AL_pos hδ0
  have hb0 : 0 ≤ ∑ n ∈ S, ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbig' : ∀ i ∈ R, N ^ σ / 6 ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ := fun i hi => by
    rw [pv_point_eq]; exact hbig i hi
  have h1 := card_mul_sq_le hinj hT0 ht hS b (by positivity) hbig'
  have h2 : LSX q T N' ≤ AL δ * (5 * P) * (2 * u) := by
    refine (LSX_le q hT0 hN'1 hδ0 hδ1).trans ?_
    have h3 : (q : ℝ) * (2 * T + 1) + N' ≤ 5 * P := by
      have e : (q : ℝ) * (2 * T + 1) = 2 * P + q := by rw [hP]; ring
      rw [e]; linarith
    have h4 : (N' : ℝ) ^ δ ≤ 2 * u := by
      calc (N' : ℝ) ^ δ ≤ (2 * P) ^ δ := Real.rpow_le_rpow (by positivity) hN'P hδ0.le
        _ = 2 ^ δ * u := by rw [Real.mul_rpow (by norm_num) hP0.le, hu]
        _ ≤ 2 * u := by
            have : (2 : ℝ) ^ δ ≤ 2 := by
              calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
                _ = 2 := Real.rpow_one 2
            gcongr
    have : 0 ≤ (N' : ℝ) ^ δ := by positivity
    gcongr
  have h5 : (R.card : ℝ) * (N ^ σ / 6) ^ 2 ≤ AL δ * (5 * P) * (2 * u) * (9 / 5 * N) := by
    have := LSX_nonneg q hT0 N'
    exact h1.trans (mul_le_mul h2 hSb hb0 (by positivity))
  have hV2 : ((N ^ σ / 6) ^ 2)⁻¹ = 36 * ((N ^ σ) ^ 2)⁻¹ := by field_simp; ring
  rw [← hV2, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h5

/-- **The main term as a power of `P`**: from the sizes of its factors,
`N·Q·I_H²·R·V^{−2}·L·τ·S·H ≤ C₁(δ)·P·u^{16}·R·N^{2−2σ}`. -/
lemma main_term_le {N P u δ σ V Q LS τ Sb Hz Rc : ℝ} (hN0 : 0 < N) (hP0 : 0 < P) (hu1 : 1 ≤ u) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hR0 : 0 ≤ Rc) (hQ : Q ≤ (Real.pi * CGK 0) ^ 2 * (Cdiv δ * u) ^ 6)
    (hLS0 : 0 ≤ LS) (hLS : LS ≤ AL δ * (11 * (P * u)) * (36 / 5 * u ^ 2)) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ Cdiv δ * (36 / 5 * u ^ 2)) (hSb0 : 0 ≤ Sb) (hSb : Sb ≤ 9 / 5 * N) (hHz0 : 0 ≤ Hz)
    (hHz : Hz ≤ 5 * u ^ 2 / δ) (hV2 : (V ^ 2)⁻¹ = 36 * ((N ^ σ) ^ 2)⁻¹) :
    N * Q * IH ^ 2 * (Rc * ((V ^ 2)⁻¹ * (LS * (τ * (Sb * Hz))))) ≤ C1 δ * (P * u ^ 16) * (Rc * N ^ (2 - 2 * σ)) := by
  have hu0 : 0 < u := by linarith
  have hIH := IH_nonneg
  have hAL := AL_pos hδ0
  have hCd0 : 0 < Cdiv δ := by linarith [one_le_Cdiv hδ0 hδ1]
  have hNN : N * N * ((N ^ σ) ^ 2)⁻¹ = N ^ (2 - 2 * σ) := by
    have e1 : (N ^ σ) ^ 2 = N ^ (2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [e1, Real.rpow_sub hN0, Real.rpow_two, div_eq_mul_inv, sq]
  have hV20 : 0 ≤ (V ^ 2)⁻¹ := by positivity
  calc N * Q * IH ^ 2 * (Rc * ((V ^ 2)⁻¹ * (LS * (τ * (Sb * Hz)))))
      ≤ N * ((Real.pi * CGK 0) ^ 2 * (Cdiv δ * u) ^ 6) * IH ^ 2 * (Rc * ((V ^ 2)⁻¹ *
          ((AL δ * (11 * (P * u)) * (36 / 5 * u ^ 2)) * ((Cdiv δ * (36 / 5 * u ^ 2)) *
            ((9 / 5 * N) * (5 * u ^ 2 / δ)))))) := by
        gcongr
    _ = C1 δ * P * (Rc * (N * N * ((N ^ σ) ^ 2)⁻¹)) * u ^ 13 := by rw [hV2]; unfold C1; ring
    _ = C1 δ * P * (Rc * N ^ (2 - 2 * σ)) * u ^ 13 := by rw [hNN]
    _ ≤ C1 δ * P * (Rc * N ^ (2 - 2 * σ)) * u ^ 16 := by
        have := C1_nonneg hδ0 hδ1
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu1 (by norm_num)) (by positivity)
    _ = C1 δ * (P * u ^ 16) * (Rc * N ^ (2 - 2 * σ)) := by ring

/-- **The tails as a power of `P`**: from the bounds of `|R|` and of `B`, `|R|²B² ≤ C₂(δ)·P·u^{16}·|R|·N^{2−2σ}`
for `N > 5/6`. -/
lemma tail_le {N P u δ σ Rc B : ℝ} {K : ℕ} (hN56 : 5 / 6 < N) (hP1 : 1 ≤ P) (hu1 : 1 ≤ u) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hR0 : 0 ≤ Rc) (hRb : Rc ≤ AL δ * (5 * P) * (2 * u) * (9 / 5 * N) * (36 * ((N ^ σ) ^ 2)⁻¹))
    (hB0 : 0 ≤ B) (hB : B ≤ 2 * (Cdiv δ * u) ^ 3 * (Real.pi * CGK K * IK K) * (3 * P * (P ^ 4)⁻¹))
    (hK : K = Kd δ) :
    Rc ^ 2 * B ^ 2 ≤ C2 δ * (P * u ^ 16) * (Rc * N ^ (2 - 2 * σ)) := by
  have hN0 : 0 < N := by linarith
  have hP0 : 0 < P := by linarith
  have hu0 : 0 < u := by linarith
  have hAL := AL_pos hδ0
  have hCd0 : 0 < Cdiv δ := by linarith [one_le_Cdiv hδ0 hδ1]
  have hK0 := CGK_pos K
  have hIK := IK_nonneg K
  have hNN : N * N * ((N ^ σ) ^ 2)⁻¹ = N ^ (2 - 2 * σ) := by
    have e1 : (N ^ σ) ^ 2 = N ^ (2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [e1, Real.rpow_sub hN0, Real.rpow_two, div_eq_mul_inv, sq]
  have hB2 := pow_le_pow_left₀ hB0 hB 2
  have hPp : P ^ 3 * ((P ^ 4)⁻¹) ^ 2 ≤ P := by
    have e : P ^ 3 * ((P ^ 4)⁻¹) ^ 2 = (P ^ 5)⁻¹ := by field_simp
    rw [e]
    exact (inv_le_one_of_one_le₀ (one_le_pow₀ hP1)).trans hP1
  have hN1 : N * ((N ^ σ) ^ 2)⁻¹ ≤ 6 / 5 * N ^ (2 - 2 * σ) := by
    rw [← hNN]
    have h0 : 0 ≤ N * ((N ^ σ) ^ 2)⁻¹ := by positivity
    calc N * ((N ^ σ) ^ 2)⁻¹ = 1 * (N * ((N ^ σ) ^ 2)⁻¹) := by ring
      _ ≤ (6 / 5 * N) * (N * ((N ^ σ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_right (by linarith) h0
      _ = 6 / 5 * (N * N * ((N ^ σ) ^ 2)⁻¹) := by ring
  have hu7 : u ^ 7 ≤ u ^ 16 := pow_le_pow_right₀ hu1 (by norm_num)
  calc Rc ^ 2 * B ^ 2 = Rc * (Rc * B ^ 2) := by ring
    _ ≤ Rc * ((AL δ * (5 * P) * (2 * u) * (9 / 5 * N) * (36 * ((N ^ σ) ^ 2)⁻¹)) *
          (2 * (Cdiv δ * u) ^ 3 * (Real.pi * CGK K * IK K) * (3 * P * (P ^ 4)⁻¹)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hRb hB2 (sq_nonneg _) ?_) hR0
        positivity
    _ = AL δ * (Real.pi * CGK K * IK K) ^ 2 * Cdiv δ ^ 6 * (5 * 2 * (9 / 5) * 36 * 4 * 9) *
          (P ^ 3 * ((P ^ 4)⁻¹) ^ 2) * u ^ 7 * (Rc * (N * ((N ^ σ) ^ 2)⁻¹)) := by ring
    _ ≤ AL δ * (Real.pi * CGK K * IK K) ^ 2 * Cdiv δ ^ 6 * (5 * 2 * (9 / 5) * 36 * 4 * 9) *
          P * u ^ 16 * (Rc * (6 / 5 * N ^ (2 - 2 * σ))) := by
        gcongr
    _ = C2 δ * (P * u ^ 16) * (Rc * N ^ (2 - 2 * σ)) := by unfold C2; rw [← hK]; ring

/-- **The main case of `CGLS2`**, `N > 5/6`: with `P = qT`, `Z = ⌊3P^{1+δ}/N⌋ + 1` and `K = ⌈4/δ⌉`,
`‖E‖_F² ≤ (C₁(δ) + C₂(δ))P^{1+16δ}|R|N^{2−2σ}` for `0 < δ ≤ 1/16` (`frobOff_le` and the sizes). -/
theorem s2_main {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι} {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) {t : ι → ℝ} {T N σ : ℝ} (hT : 1 ≤ T) (hN56 : 5 / 6 < N) (hNP : N ≤ (q : ℝ) * T)
    {S : Finset ℕ} (hS : ∀ n ∈ S, 6 / 5 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 9 / 5 * N) {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1)
    (ht : ∀ i ∈ R, |t i| ≤ T) (hbig : ∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) :
    frobOff N R χ t ≤
      (C1 δ + C2 δ) * (((q : ℝ) * T) * ((q : ℝ) * T) ^ (16 * δ)) * (R.card * N ^ (2 - 2 * σ)) := by
  classical
  have hN0 : 0 < N := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hδ1' : δ ≤ 1 := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hCd0 : 0 < Cdiv δ := by linarith [one_le_Cdiv hδ0 hδ1']
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (q : ℝ) * T := ⟨_, rfl⟩
  rw [← hP] at hNP ⊢
  have hP1 : 1 ≤ P := by rw [hP]; exact one_le_mul_of_one_le_of_one_le hq1 hT
  have hP0 : 0 < P := by linarith
  have hqP : (q : ℝ) ≤ P := by rw [hP]; exact le_mul_of_one_le_right (by positivity) hT
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = P ^ δ := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_rpow hP1 hδ0.le
  have hu0 : 0 < u := by linarith
  have hu16 : u ^ 16 = P ^ (16 * δ) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; congr 1; push_cast; ring
  rw [← hu16]
  -- the support of the large polynomial
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, N' = ⌊9 / 5 * N⌋₊ := ⟨_, rfl⟩
  have hN'r : (N' : ℝ) ≤ 9 / 5 * N := by rw [hN']; exact Nat.floor_le (by positivity)
  have hN'1 : 1 ≤ N' := by rw [hN']; exact Nat.le_floor (by push_cast; linarith)
  have hN'P : (N' : ℝ) ≤ 2 * P := by linarith
  have hS' : S ⊆ Finset.Icc 2 N' := by
    intro n hn
    obtain ⟨h1, h2⟩ := hS n hn
    have hn1 : (1 : ℝ) < n := by linarith
    have hn2 : 2 ≤ n := by
      have : 1 < n := by exact_mod_cast hn1
      omega
    exact Finset.mem_Icc.2 ⟨hn2, by rw [hN']; exact Nat.le_floor h2⟩
  have hSb : ∑ n ∈ S, ‖b n‖ ^ 2 ≤ 9 / 5 * N := by
    calc ∑ n ∈ S, ‖b n‖ ^ 2 ≤ ∑ _n ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => by nlinarith [hb n, norm_nonneg (b n)]
      _ = S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ N' := by
          have h1 := Finset.card_le_card hS'
          rw [Nat.card_Icc] at h1
          have : S.card ≤ N' := by omega
          exact_mod_cast this
      _ ≤ 9 / 5 * N := hN'r
  -- `Z`, `K` and `τ`
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, Z = ⌊3 * P * u / N⌋₊ + 1 := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; omega
  have hZlo : 3 * P * u / N ≤ Z := by
    rw [hZ]; push_cast; exact (Nat.lt_floor_add_one _).le
  have hZhi : (Z : ℝ) ≤ 3 * P * u / N + 1 := by
    rw [hZ]; push_cast; gcongr; exact Nat.floor_le (by positivity)
  have hNZ : 3 * P * u ≤ N * Z := by
    have := mul_le_mul_of_nonneg_left hZlo hN0.le
    rwa [mul_div_cancel₀ _ hN0.ne'] at this
  have hPu : P ≤ P * u := le_mul_of_one_le_right hP0.le hu1
  have hZ5 : (Z : ℝ) ≤ 5 * (P * u) := by
    have h1 : 3 * P * u / N ≤ 18 / 5 * (P * u) := by
      rw [div_le_iff₀ hN0]
      have := mul_pos hP0 hu0
      nlinarith [mul_pos this (sub_pos.2 hN56)]
    linarith
  have hX : ((N' * Z : ℕ) : ℝ) ≤ 36 / 5 * (P * u) := by
    push_cast
    have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg _
    calc (N' : ℝ) * Z ≤ 9 / 5 * N * (3 * P * u / N + 1) := mul_le_mul hN'r hZhi hZ0 (by positivity)
      _ = 27 / 5 * (P * u) + 9 / 5 * N := by field_simp; ring
      _ ≤ 36 / 5 * (P * u) := by linarith
  have hX1 : 1 ≤ N' * Z := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = Kd δ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact Nat.ceil_pos.2 (by positivity)
  have hδK : 4 ≤ δ * K := by
    have h1 := Nat.le_ceil (4 / δ)
    rw [div_le_iff₀ hδ0] at h1
    rw [hK, Kd]; linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = Cdiv δ * ((N' * Z : ℕ) : ℝ) ^ δ := ⟨_, rfl⟩
  have hτ : ∀ k, k ≤ N' * Z → (k.divisors.card : ℝ) ≤ τ := by
    intro k hk
    refine (card_divisors_le hδ0 hδ1' k).trans ?_
    have hk' : (k : ℝ) ≤ ((N' * Z : ℕ) : ℝ) := by exact_mod_cast hk
    rw [hτdef]
    gcongr
  -- `frobOff_le`
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = N ^ σ / 6 := ⟨_, rfl⟩
  have hV0 : 0 < V := by rw [hV]; positivity
  have hbigV : ∀ i ∈ R, V ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖ := fun i hi => by
    rw [hV]; exact hbig i hi
  have h := frobOff_le hinj hT0 hN0 ht hS' b hV0 hbigV hZ1 hK1 hτ
  -- the sizes
  have hqδ : (q : ℝ) ^ δ ≤ u := by rw [hu]; exact Real.rpow_le_rpow (by linarith) hqP hδ0.le
  have hω : (2 : ℝ) ^ q.primeFactors.card ≤ Cdiv δ * u :=
    (two_pow_omega_le q hδ0 hδ1').trans (mul_le_mul_of_nonneg_left hqδ hCd0.le)
  have hQ0b : Q0 q ^ 2 ≤ (Real.pi * CGK 0) ^ 2 * (Cdiv δ * u) ^ 6 := by
    have h1 := Q0_le q
    have h2 : Real.pi * CGK 0 * ((2 : ℝ) ^ q.primeFactors.card) ^ 3 ≤ Real.pi * CGK 0 * (Cdiv δ * u) ^ 3 := by
      have := CGK_pos 0; gcongr
    calc Q0 q ^ 2 ≤ (Real.pi * CGK 0 * (Cdiv δ * u) ^ 3) ^ 2 := pow_le_pow_left₀ (Q0_nonneg q) (h1.trans h2) 2
      _ = (Real.pi * CGK 0) ^ 2 * (Cdiv δ * u) ^ 6 := by ring
  have hXδ : ((N' * Z : ℕ) : ℝ) ^ δ ≤ 36 / 5 * u ^ 2 := by
    have := rpow_le_of_le_mul (c := 36 / 5) (Nat.cast_nonneg _) (by norm_num) hP1 hδ0.le hδ1' (by rw [← hu]; exact hX)
    rwa [← hu] at this
  have hτb : τ ≤ Cdiv δ * (36 / 5 * u ^ 2) := by rw [hτdef]; gcongr
  have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
  have hLSXb : LSX q T (N' * Z) ≤ AL δ * (11 * (P * u)) * (36 / 5 * u ^ 2) := by
    refine (LSX_le q hT0 hX1 hδ0 hδ1').trans ?_
    have hAL := AL_pos hδ0
    have h1 : (q : ℝ) * (2 * T + 1) + ((N' * Z : ℕ) : ℝ) ≤ 11 * (P * u) := by
      have e : (q : ℝ) * (2 * T + 1) = 2 * P + q := by rw [hP]; ring
      rw [e]; linarith
    gcongr
  have hHZb : HZ Z ≤ 5 * u ^ 2 / δ := by
    refine (HZ_le Z hδ0 (by linarith)).trans ?_
    have hZδ : (Z : ℝ) ^ δ ≤ 5 * u ^ 2 := by
      have := rpow_le_of_le_mul (c := 5) (Nat.cast_nonneg _) (by norm_num) hP1 hδ0.le hδ1' (by rw [← hu]; exact hZ5)
      rwa [← hu] at this
    gcongr
  have hHZ0 : 0 ≤ HZ Z := Finset.sum_nonneg fun m _ => by positivity
  have hV2 : (V ^ 2)⁻¹ = 36 * ((N ^ σ) ^ 2)⁻¹ := by rw [hV]; field_simp; ring
  have hmain := main_term_le hN0 hP0 hu1 hδ0 hδ1' (Nat.cast_nonneg R.card) hQ0b
    (LSX_nonneg q hT0 (N' * Z)) hLSXb hτ0 hτb (Finset.sum_nonneg fun _ _ => sq_nonneg _) hSb hHZ0 hHZb hV2
  have hRb := card_le hinj hT hN0 hP hu hδ0 hδ1' ht hS' hN'1 hN'P hSb hbig
  have hBb := Bmax_le hT hN0 hP hu hδ0 hδ1' hZ1 hNZ hδK
  have htail := tail_le hN56 hP1 hu1 hδ0 hδ1' (Nat.cast_nonneg R.card) hRb (Bmax_nonneg q hN0.le hT0 Z K) hBb hK
  calc frobOff N R χ t ≤ N * Q0 q ^ 2 * IH ^ 2 * (R.card * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) *
        (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z))))) + (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 := h
    _ ≤ C1 δ * (P * u ^ 16) * (R.card * N ^ (2 - 2 * σ)) + C2 δ * (P * u ^ 16) * (R.card * N ^ (2 - 2 * σ)) :=
        add_le_add hmain htail
    _ = (C1 δ + C2 δ) * (P * u ^ 16) * (R.card * N ^ (2 - 2 * σ)) := by ring

/-- For `N ≤ 5/6`, `(qT)^{2/3}/2 ≤ N` and `T ≥ 1` force `q ≤ 2`: otherwise `(qT)² ≥ 9 > (5/3)³`. -/
lemma q_le_two {q : ℕ} {T N : ℝ} (hT : 1 ≤ T) (hN1 : ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N) (hN : N ≤ 5 / 6) :
    q ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ q := by omega
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast h3
  have hP : (3 : ℝ) ≤ q * T := by nlinarith
  have hP0 : (0 : ℝ) ≤ q * T := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((q : ℝ) * T) ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a ≤ 5 / 3 := by rw [ha]; linarith
  have ha3 : a ^ 3 = ((q : ℝ) * T) ^ 2 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hP0, show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = 2 by norm_num,
      Real.rpow_two]
  have h1 : a ^ 3 ≤ (5 / 3) ^ 3 := pow_le_pow_left₀ ha0 ha1 3
  nlinarith

/-- **`CGLS2` holds**: Chen–Gupta–Li's Proposition 6.1 at one point per character, in round 639's form. For
`N > 5/6` it is `s2_main` at `δ = min(ε, 1)/16`, with `(qT)^{min(ε,1)} ≤ (6/5)^ε(qTN)^ε`; for `N ≤ 5/6`, `q ≤ 2`
(`q_le_two`), there is one character, and `‖E‖_F² = 0`. -/
theorem cgls2 : CGLS2 := by
  intro ε hε
  have hη0 : 0 < min ε 1 := lt_min hε one_pos
  have hηε : min ε 1 ≤ ε := min_le_left _ _
  have hδ0 : 0 < min ε 1 / 16 := by positivity
  have hδ1 : min ε 1 / 16 ≤ 1 / 16 := by have := min_le_right ε 1; linarith
  have hC1 := C1_nonneg hδ0 (by linarith)
  have hC2 := C2_nonneg hδ0 (by linarith)
  refine ⟨(C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (6 / 5) ^ ε, by positivity, ?_⟩
  intro q _ ι _ R χ t T N σ S b hinj _ hT _ _ hN1 hN2 hS hb ht hbig
  have hT0 : 0 ≤ T := by linarith
  have hN0 : 0 ≤ N := le_trans (by positivity) hN1
  rcases le_or_gt N (5 / 6) with hN56 | hN56
  · rw [frobOff_eq_zero_of_le_two (q_le_two hT hN1 hN56) hinj N t]
    positivity
  · have h := s2_main hinj hT hN56 hN2 hS hb ht hbig hδ0 hδ1
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    have hP1 : (1 : ℝ) ≤ q * T := one_le_mul_of_one_le_of_one_le hq1 hT
    have hPN : (q : ℝ) * T ≤ 6 / 5 * ((q : ℝ) * T * N) := by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ q * T) (by linarith : (0 : ℝ) ≤ 6 / 5 * N - 1)
      nlinarith
    have hpow : ((q : ℝ) * T) ^ (16 * (min ε 1 / 16)) ≤ (6 / 5) ^ ε * ((q : ℝ) * T * N) ^ ε := by
      rw [show 16 * (min ε 1 / 16) = min ε 1 by ring]
      calc ((q : ℝ) * T) ^ min ε 1 ≤ ((q : ℝ) * T) ^ ε := Real.rpow_le_rpow_of_exponent_le hP1 hηε
        _ ≤ (6 / 5 * ((q : ℝ) * T * N)) ^ ε := Real.rpow_le_rpow (by linarith) hPN hε.le
        _ = (6 / 5) ^ ε * ((q : ℝ) * T * N) ^ ε := Real.mul_rpow (by norm_num) (by positivity)
    calc frobOff N R χ t ≤ (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) *
          (((q : ℝ) * T) * ((q : ℝ) * T) ^ (16 * (min ε 1 / 16))) * (R.card * N ^ (2 - 2 * σ)) := h
      _ ≤ (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) *
          (((q : ℝ) * T) * ((6 / 5) ^ ε * ((q : ℝ) * T * N) ^ ε)) * (R.card * N ^ (2 - 2 * σ)) := by
          gcongr
      _ = (C1 (min ε 1 / 16) + C2 (min ε 1 / 16)) * (6 / 5) ^ ε * ((q : ℝ) * T * N) ^ ε *
          ((q : ℝ) * T * R.card * N ^ (2 - 2 * σ)) := by ring

/-- **Linnik's theorem with exponent `9/4` from the `S₃` hypothesis alone**: round 639's `linnik_225c_s23` with
`cgls2`. -/
theorem linnik_225c_s3 (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  linnik_225c_s23 cgls2 h3

/-- **Linnik's theorem with exponent `226/100` from the `S₃` hypothesis alone**: round 639's `linnik_226c_s23` with
`cgls2`. -/
theorem linnik_226c_s3 (h3 : CGLS3) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  linnik_226c_s23 cgls2 h3

end LinnikCGLS2

#print axioms LinnikCGLS2.LSX_le
#print axioms LinnikCGLS2.HZ_le
#print axioms LinnikCGLS2.Q0_le
#print axioms LinnikCGLS2.card_mul_sq_le
#print axioms LinnikCGLS2.frobOff_eq_zero_of_le_two
#print axioms LinnikCGLS2.Bmax_le
#print axioms LinnikCGLS2.card_le
#print axioms LinnikCGLS2.main_term_le
#print axioms LinnikCGLS2.tail_le
#print axioms LinnikCGLS2.s2_main
#print axioms LinnikCGLS2.cgls2
#print axioms LinnikCGLS2.linnik_225c_s3
#print axioms LinnikCGLS2.linnik_226c_s3
