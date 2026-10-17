/-
# Round 527, part 2: one block and one bin as a power of `Q` on `3/4 ≤ σ ≤ 11/12`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`term1_le`, `term2_le`). Take part 1's `block_bin_hux` at `η = ε/200`, `ε_d = ε/88` and `V = 1/(4K)`,
with `Λ = (2P)^m`, `Q^{4/5+ε} ≤ Λ ≤ Q^{6/5+3ε/2}`, `m ≤ 22`, `4K ≤ Q^{ε/528}`, `3/4 ≤ σ ≤ σ_b` and `σ ≤ 11/12`. If
`q(T + 2) ≤ Q`, the far tail is cut off, `X ≤ Q^{25}`, `τ ≤ Q^{ε/4}`, and `J + 2`, `L(X)`, `bkt(q(1 + 2T)) + 1`,
`EQ(q)` and `2^{ω(q)}` are each at most `Q^{ε/8}`, then each of the two terms is at most a constant (depending on `ε`)
times `Q^{(12/5+53ε)(1−σ)}`. Up to the powers of `Q^ε`, the first term carries `Λ^{2−2σ} ≤ Q^{(6/5)(2−2σ)}`, which is
`Q^{(12/5)(1−σ)}`; the second carries `Λ^{4−6σ}Q ≤ Q^{(4/5)(4−6σ)+1}` (the exponent `4 − 6σ` is negative), which falls
short of `Q^{(12/5)(1−σ)}` by `Q^{(12σ−9)/5}`, and `(12σ − 9)/5 ≥ 0` exactly when `σ ≥ 3/4`.

* `card_powerset_le_divisors`: `2^{ω(q)} ≤ d(q)`.
* `bkt_le_log`, `LSmax_le_log`, `ev_log_pow`: the logarithmic sizes, and `c(1 + log Q)^k ≤ Q^θ` for all large `Q`.
* `hxA_le_two`, `A1_sq_le`, `hxA_sq_le`: with the far tail cut off, `hxA ≤ 2A₁` and `hxA² ≤ 40(24·KG·CG)²ΛQ^{1+3ε/2}`.
* `term1_le`, `exp2_le`, `Gm3_le`, `term2_le`: the two terms of `block_bin_hux` as powers of `Q`.
-/

import LinnikTwelveBins

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikTwelve

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag LinnikHuxley LinnikReflect

variable {q : ℕ}

/-! ### Sizes -/

/-- `2^{ω(q)} ≤ d(q)`: the products of the sets of primes of `q` are distinct divisors of `q`. -/
lemma card_powerset_le_divisors (q : ℕ) [NeZero q] :
    (q.primeFactors.powerset.card : ℝ) ≤ q.divisors.card := by
  have h : q.primeFactors.powerset.card ≤ q.divisors.card := by
    refine card_le_card_of_injOn (fun T => ∏ p ∈ T, p) ?_ ?_
    · intro T hT
      have hT' := mem_powerset.1 (Finset.mem_coe.1 hT)
      rw [Finset.mem_coe, Nat.mem_divisors]
      exact ⟨(Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p) hT').trans (Nat.prod_primeFactors_dvd q),
        NeZero.ne q⟩
    · intro T hT T' hT' h
      have h1 : ∀ p ∈ T, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors (mem_powerset.1 (Finset.mem_coe.1 hT) hp)
      have h2 : ∀ p ∈ T', p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors (mem_powerset.1 (Finset.mem_coe.1 hT') hp)
      have h3 := congrArg Nat.primeFactors h
      simp only at h3
      rwa [Nat.primeFactors_prod h1, Nat.primeFactors_prod h2] at h3
  exact_mod_cast h

/-- `L(X) ≥ 1` for `X ≥ 1`. -/
lemma one_le_LSmax {X : ℕ} (hX : 1 ≤ X) : 1 ≤ LSmax X := by
  unfold LSmax
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have h1 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have f1 : 1 ≤ Real.exp 1 * 8 := by linarith
  have f2 : 1 ≤ 1 + Real.log X := by linarith
  have f3 : 1 ≤ 2 + Real.log (2 * X) ^ 2 := by nlinarith [sq_nonneg (Real.log (2 * X))]
  have f4 : (1 : ℝ) ≤ Nat.log 2 X + 1 := by have : (0 : ℝ) ≤ Nat.log 2 X := Nat.cast_nonneg _; linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le f1 f2) f3) f4

/-- `bkt x ≤ 2 log(2x)` for `x ≥ 1`. -/
lemma bkt_le_log {x : ℝ} (hx : 1 ≤ x) : (bkt x : ℝ) ≤ 2 * Real.log (2 * x) := by
  have h := (bkt_spec hx).2
  have h1 : (bkt x : ℝ) * Real.log 2 ≤ Real.log (2 * x) := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h
  have h2 := Real.log_two_gt_d9
  have h3 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have h4 : (0 : ℝ) ≤ bkt x := Nat.cast_nonneg _
  nlinarith

/-- `L(X) ≤ 8e·25·627·50(1 + log Q)⁴` for `1 ≤ X ≤ Q^{25}`. -/
lemma LSmax_le_log {X : ℕ} {Q : ℝ} (hX : 1 ≤ X) (hQ1 : 1 ≤ Q) (hXQ : (X : ℝ) ≤ Q ^ (25 : ℝ)) :
    LSmax X ≤ 8 * Real.exp 1 * 25 * 627 * 50 * (1 + Real.log Q) ^ 4 := by
  unfold LSmax
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlX : Real.log X ≤ 25 * Real.log Q := by
    calc Real.log X ≤ Real.log (Q ^ (25 : ℝ)) := Real.log_le_log (by linarith) hXQ
      _ = 25 * Real.log Q := Real.log_rpow (by linarith) _
  have hlX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have h2X : Real.log (2 * X) ≤ 1 + 25 * Real.log Q := by
    rw [Real.log_mul (by norm_num) (by linarith)]; have := Real.log_two_lt_d9; linarith
  have h2X0 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hNl : (Nat.log 2 X : ℝ) ≤ 50 * Real.log Q := by
    have h1 : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
    have h2 : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log X := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
    have := Real.log_two_gt_d9
    have : (0 : ℝ) ≤ Nat.log 2 X := Nat.cast_nonneg _
    nlinarith
  set l := 1 + Real.log Q with hl
  have hl1 : 1 ≤ l := by linarith
  have f1 : 1 + Real.log X ≤ 25 * l := by linarith
  have f2 : 2 + Real.log (2 * X) ^ 2 ≤ 627 * l ^ 2 := by
    have : Real.log (2 * X) ≤ 25 * l := by linarith
    nlinarith
  have f3 : (Nat.log 2 X : ℝ) + 1 ≤ 50 * l := by linarith
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have g1 : 0 ≤ 1 + Real.log X := by linarith
  have g2 : 0 ≤ 2 + Real.log (2 * X) ^ 2 := by positivity
  have g3 : (0 : ℝ) ≤ Nat.log 2 X + 1 := by positivity
  calc Real.exp 1 * 8 * (1 + Real.log X) * (2 + Real.log (2 * X) ^ 2) * (Nat.log 2 X + 1)
      ≤ Real.exp 1 * 8 * (25 * l) * (627 * l ^ 2) * (50 * l) := by gcongr
    _ = 8 * Real.exp 1 * 25 * 627 * 50 * l ^ 4 := by ring

/-- `c(1 + log Q)^k ≤ Q^θ` for all large `Q` (`log Q ≤ Q^θ′/θ′`, `Real.log_le_rpow_div`). -/
lemma ev_log_pow (c θ : ℝ) (k : ℕ) (hθ : 0 < θ) : ∀ᶠ Q : ℝ in atTop, c * (1 + Real.log Q) ^ k ≤ Q ^ θ := by
  set θ' := θ / (2 * k + 2) with hθ'
  have hθ'0 : 0 < θ' := by positivity
  have hev := (tendsto_rpow_atTop (by positivity : 0 < θ / 2)).eventually_ge_atTop (|c| * (1 + 1 / θ') ^ k)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hev] with Q hQ1 hQc
  have hQ0 : 0 < Q := by linarith
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hl : Real.log Q ≤ Q ^ θ' / θ' := Real.log_le_rpow_div hQ0.le hθ'0
  have hQθ' : 1 ≤ Q ^ θ' := Real.one_le_rpow hQ1 hθ'0.le
  have h1 : 1 + Real.log Q ≤ (1 + 1 / θ') * Q ^ θ' := by
    have e : (1 + 1 / θ') * Q ^ θ' = Q ^ θ' + Q ^ θ' / θ' := by field_simp
    rw [e]; linarith
  have h2 : (1 + Real.log Q) ^ k ≤ (1 + 1 / θ') ^ k * Q ^ (k * θ') := by
    calc (1 + Real.log Q) ^ k ≤ ((1 + 1 / θ') * Q ^ θ') ^ k := pow_le_pow_left₀ (by linarith) h1 k
      _ = (1 + 1 / θ') ^ k * (Q ^ θ') ^ k := mul_pow _ _ _
      _ = (1 + 1 / θ') ^ k * Q ^ (k * θ') := by
          rw [← Real.rpow_natCast (Q ^ θ'), ← Real.rpow_mul hQ0.le, mul_comm θ']
  have hkθ : (k : ℝ) * θ' ≤ θ / 2 := by
    rw [hθ', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h3 : Q ^ ((k : ℝ) * θ') ≤ Q ^ (θ / 2) := Real.rpow_le_rpow_of_exponent_le hQ1 hkθ
  have hpos : 0 ≤ (1 + Real.log Q) ^ k := by positivity
  calc c * (1 + Real.log Q) ^ k ≤ |c| * (1 + Real.log Q) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self c) hpos
    _ ≤ |c| * ((1 + 1 / θ') ^ k * Q ^ (θ / 2)) := by
        gcongr; exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = (|c| * (1 + 1 / θ') ^ k) * Q ^ (θ / 2) := by ring
    _ ≤ Q ^ (θ / 2) * Q ^ (θ / 2) := by gcongr
    _ = Q ^ θ := by rw [← Real.rpow_add hQ0]; ring_nf

/-! ### The off-diagonal factor of one block -/

/-- **The far tail cut off**: if `q^{1/4}(2q(1 + 2T))^{3/4}2^{−J/16}ζ(9/8) ≤ 1`, the second summand of `hxA` is at most
its first, so `hxA ≤ 2A₁`. -/
lemma hxA_le_two [NeZero q] {τ η T U N : ℝ} (hτ : 1 ≤ τ) (hη : 0 ≤ η) (hT : 0 ≤ T) (hU : 0 ≤ U) (hN : 0 ≤ N)
    {X J : ℕ} (hX : 1 ≤ X)
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    hxA q τ η T U N X J ≤ 2 * ((12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η) *
      (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ η *
        Real.sqrt (τ * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T))))))) := by
  unfold hxA
  set K₀ := 12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η with hK₀
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK₀0 : 0 ≤ K₀ := by
    have := InghamDensity.KG_pos; have := CG_pos; have := EQ_pos q; rw [hK₀]; positivity
  have hB0 : (0 : ℝ) ≤ bkt (q * (1 + 2 * T)) + 1 := by positivity
  set W := τ * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T))) with hW
  have hL1 := one_le_LSmax hX
  have hqT : (0 : ℝ) ≤ q * (1 + 2 * T) := by positivity
  have hτL : 1 ≤ τ * LSmax X := one_le_mul_of_one_le_of_one_le hτ hL1
  have hW1 : q * N ≤ W := by
    rw [hW]
    have h1 : (q : ℝ) * N ≤ 4 * N * (q * (1 + 2 * T)) := by
      have h := mul_nonneg (mul_nonneg hq0 hN) (by linarith : (0 : ℝ) ≤ 3 + 8 * T)
      have e : 4 * N * ((q : ℝ) * (1 + 2 * T)) = q * N + (q * N) * (3 + 8 * T) := by ring
      rw [e]; linarith
    have h2 : 4 * N * (q * (1 + 2 * T)) ≤ U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T)) := by
      have : 0 ≤ U * q * (2 * T + 1) := by positivity
      linarith
    have h3 : 0 ≤ U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T)) := by positivity
    calc (q : ℝ) * N ≤ U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T)) := h1.trans h2
      _ = 1 * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T))) := (one_mul _).symm
      _ ≤ τ * LSmax X * (U * q * (2 * T + 1) + 4 * N * (q * (1 + 2 * T))) := by gcongr
  have hX1 : (1 : ℝ) ≤ (X : ℝ) ^ η := Real.one_le_rpow (by exact_mod_cast hX) hη
  have hJ1 : (1 : ℝ) ≤ J + 2 := by have : (0 : ℝ) ≤ J := Nat.cast_nonneg J; linarith
  have hsq : Real.sqrt (q * N) ≤ (J + 2) * ((X : ℝ) ^ η * Real.sqrt W) := by
    have h1 : Real.sqrt (q * N) ≤ Real.sqrt W := Real.sqrt_le_sqrt hW1
    have h2 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
    calc Real.sqrt (q * N) ≤ 1 * (1 * Real.sqrt W) := by rw [one_mul, one_mul]; exact h1
      _ ≤ (J + 2) * ((X : ℝ) ^ η * Real.sqrt W) := by gcongr
  have hfar0 : 0 ≤ (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
      ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98 := by have := zeta98_nonneg; positivity
  have h2nd : K₀ * (bkt (q * (1 + 2 * T)) + 1) * ((q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
      ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) * Real.sqrt (q * N) ≤
      K₀ * (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ η * Real.sqrt W)) := by
    calc K₀ * (bkt (q * (1 + 2 * T)) + 1) * ((q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
          ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98) * Real.sqrt (q * N)
        ≤ K₀ * (bkt (q * (1 + 2 * T)) + 1) * 1 * Real.sqrt (q * N) := by gcongr
      _ = K₀ * (bkt (q * (1 + 2 * T)) + 1) * Real.sqrt (q * N) := by ring
      _ ≤ K₀ * (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ η * Real.sqrt W)) := by gcongr
  linarith

/-- **The first summand of the off-diagonal factor, squared**: with `q(T + 2) ≤ Q`, `X ≤ Q^{25}`, `τ ≤ Q^{ε/4}`, and
`J + 2`, `L(X)`, `bkt(q(1 + 2T)) + 1` and `EQ(q)` each at most `Q^{ε/8}`, `A₁² ≤ 10(24·KG·CG)²ΛQ^{1+3ε/2}` at
`η = ε/200`, `U = N = Λ`. -/
lemma A1_sq_le [NeZero q] {ε τ T Λ Q : ℝ} {X J : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hQ1 : 1 ≤ Q) (hT : 0 ≤ T)
    (hqT : (q : ℝ) * (T + 2) ≤ Q) (hΛ : 0 ≤ Λ) (hX1 : 1 ≤ X) (hXQ : (X : ℝ) ≤ Q ^ (25 : ℝ))
    (hτ0 : 0 ≤ τ) (hτQ : τ ≤ Q ^ (ε / 4)) (hJ : (J : ℝ) + 2 ≤ Q ^ (ε / 8)) (hL : LSmax X ≤ Q ^ (ε / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8)) (hEQ : EQ q ≤ Q ^ (ε / 8)) :
    ((12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * (ε / 200)) * (q * (1 + 2 * T)) ^ (ε / 200)) *
      (bkt (q * (1 + 2 * T)) + 1) * ((J + 2) * ((X : ℝ) ^ (ε / 200) *
        Real.sqrt (τ * LSmax X * (Λ * q * (2 * T + 1) + 4 * Λ * (q * (1 + 2 * T))))))) ^ 2
      ≤ 10 * (24 * InghamDensity.KG * CG) ^ 2 * Λ * Q ^ (1 + 3 / 2 * ε) := by
  have hQ0 : 0 < Q := by linarith
  set η := ε / 200 with hη
  have hη0 : 0 ≤ η := by positivity
  have hη1 : η ≤ 1 := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqQ : (q : ℝ) ≤ Q := (le_mul_of_one_le_right hq0' (by linarith : (1 : ℝ) ≤ T + 2)).trans hqT
  have hq2T : (q : ℝ) * (1 + 2 * T) ≤ 2 * Q := by
    have : (q : ℝ) * (1 + 2 * T) ≤ q * (2 * (T + 2)) := mul_le_mul_of_nonneg_left (by linarith) hq0'
    linarith
  have hq2T0 : 0 ≤ (q : ℝ) * (1 + 2 * T) := by positivity
  have hKG := InghamDensity.KG_pos
  have hCG := CG_pos
  have hEQ0 := EQ_pos q
  have hqη : (q : ℝ) ^ (2 * η) ≤ Q ^ (2 * η) := Real.rpow_le_rpow (by positivity) hqQ (by positivity)
  have hq2η : ((q : ℝ) * (1 + 2 * T)) ^ η ≤ 2 * Q ^ η := by
    calc ((q : ℝ) * (1 + 2 * T)) ^ η ≤ (2 * Q) ^ η := Real.rpow_le_rpow hq2T0 hq2T hη0
      _ = 2 ^ η * Q ^ η := Real.mul_rpow (by norm_num) hQ0.le
      _ ≤ 2 ^ (1 : ℝ) * Q ^ η :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1) (by positivity)
      _ = 2 * Q ^ η := by rw [Real.rpow_one]
  have hK₀ : 12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η ≤
      24 * InghamDensity.KG * CG * Q ^ (ε / 8 + 3 * η) := by
    calc 12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η
        ≤ 12 * InghamDensity.KG * CG * Q ^ (ε / 8) * Q ^ (2 * η) * (2 * Q ^ η) := by gcongr
      _ = 24 * InghamDensity.KG * CG * (Q ^ (ε / 8) * Q ^ (2 * η) * Q ^ η) := by ring
      _ = 24 * InghamDensity.KG * CG * Q ^ (ε / 8 + 3 * η) := by
          rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; ring_nf
  have hXη : (X : ℝ) ^ η ≤ Q ^ (25 * η) := by
    calc (X : ℝ) ^ η ≤ (Q ^ (25 : ℝ)) ^ η := Real.rpow_le_rpow (Nat.cast_nonneg _) hXQ hη0
      _ = Q ^ (25 * η) := by rw [← Real.rpow_mul hQ0.le]
  set W := τ * LSmax X * (Λ * q * (2 * T + 1) + 4 * Λ * (q * (1 + 2 * T))) with hW
  have hL0 : 0 ≤ LSmax X := LSmax_nonneg X
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hWle : W ≤ 10 * Λ * Q ^ (1 + 3 / 8 * ε) := by
    have e : W = 5 * τ * LSmax X * (Λ * (q * (1 + 2 * T))) := by rw [hW]; ring
    rw [e]
    calc 5 * τ * LSmax X * (Λ * (q * (1 + 2 * T))) ≤ 5 * Q ^ (ε / 4) * Q ^ (ε / 8) * (Λ * (2 * Q)) := by
          gcongr
      _ = 10 * Λ * (Q ^ (ε / 4) * Q ^ (ε / 8) * Q) := by ring
      _ = 10 * Λ * Q ^ (1 + 3 / 8 * ε) := by
          rw [← Real.rpow_add hQ0, ← Real.rpow_add_one hQ0.ne']; ring_nf
  set K₀ := 12 * InghamDensity.KG * CG * EQ q * (q : ℝ) ^ (2 * η) * (q * (1 + 2 * T)) ^ η with hK₀def
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀def]; positivity
  set B := (bkt (q * (1 + 2 * T)) : ℝ) + 1 with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hJ0 : (0 : ℝ) ≤ J + 2 := by positivity
  have hXη0 : 0 ≤ (X : ℝ) ^ η := by positivity
  have hprod : K₀ * B * (J + 2) * (X : ℝ) ^ η ≤
      24 * InghamDensity.KG * CG * Q ^ (ε / 8 + 3 * η) * Q ^ (ε / 8) * Q ^ (ε / 8) * Q ^ (25 * η) := by
    gcongr
  have hsq : (K₀ * B * ((J + 2) * ((X : ℝ) ^ η * Real.sqrt W))) ^ 2 = (K₀ * B * (J + 2) * (X : ℝ) ^ η) ^ 2 * W := by
    rw [show K₀ * B * ((J + 2) * ((X : ℝ) ^ η * Real.sqrt W)) = (K₀ * B * (J + 2) * (X : ℝ) ^ η) * Real.sqrt W by
      ring, mul_pow, Real.sq_sqrt hW0]
  rw [hsq]
  have hP0 : 0 ≤ K₀ * B * (J + 2) * (X : ℝ) ^ η := by positivity
  calc (K₀ * B * (J + 2) * (X : ℝ) ^ η) ^ 2 * W
      ≤ (24 * InghamDensity.KG * CG * Q ^ (ε / 8 + 3 * η) * Q ^ (ε / 8) * Q ^ (ε / 8) * Q ^ (25 * η)) ^ 2 *
          (10 * Λ * Q ^ (1 + 3 / 8 * ε)) := by
        gcongr
    _ = 10 * (24 * InghamDensity.KG * CG) ^ 2 * Λ *
          ((Q ^ (ε / 8 + 3 * η) * Q ^ (ε / 8) * Q ^ (ε / 8) * Q ^ (25 * η)) ^ 2 * Q ^ (1 + 3 / 8 * ε)) := by ring
    _ = 10 * (24 * InghamDensity.KG * CG) ^ 2 * Λ * Q ^ (1 + 9 / 8 * ε + 56 * η) := by
        congr 1
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0, ← Real.rpow_add hQ0, ← Real.rpow_natCast,
          ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0]
        congr 1; push_cast; ring
    _ ≤ 10 * (24 * InghamDensity.KG * CG) ^ 2 * Λ * Q ^ (1 + 3 / 2 * ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)) (by positivity)

/-! ### One block and one bin as a power of `Q` in the range `3/4 ≤ σ ≤ 11/12` -/

/-- **The first term**: with `Λ = (2P)^m ≤ Q^{6/5+3ε/2}`, `m ≤ 22`, `4K ≤ Q^{ε/528}`, `σ ≤ σ_b` and
`σ ≤ 11/12`, `2c₀⁻¹G_m(σ_b)Λ(4K)^{2m} ≤ 16·2^{22}(4C⁴)^{22}Q^{(12/5+53ε)(1−σ)}`, `c₀ = 2^{−m}/8`, `C = C(ε/88)` the
constant of the divisor bound (no lower bound on `σ` is used). -/
lemma term1_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {σ σb Q : ℝ} (hσ11 : σ ≤ 11 / 12)
    (hσb : σ ≤ σb) (hQ1 : 1 ≤ Q) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 22)
    (hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (6 / 5 + 3 / 2 * ε)) {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ Q ^ (ε / 528)) :
    2 * (8 * 2 ^ m) * Gm (ε / 88) P m σb * ((2 * P : ℕ) : ℝ) ^ m / ((1 / (4 * K)) ^ m) ^ 2
      ≤ 16 * 2 ^ 22 * (4 * Cdiv (ε / 88) ^ 4) ^ 22 * Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hεd : 0 < ε / 88 := by positivity
  have hεd1 : ε / 88 ≤ 1 := by linarith
  set A : ℝ := 4 * Cdiv (ε / 88) ^ 4 with hA
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
  have hGm : Gm (ε / 88) P m σb ≤ A ^ 22 * Λ ^ (1 - 2 * σ + ε) := by
    refine (Gm_le hεd hεd1 hP m (by linarith) hσb).trans ?_
    rw [← hA, ← hΛdef]
    exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
      (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (m * 2) ≤ Q ^ (ε / 12) := by
    calc (4 * K) ^ (m * 2) ≤ (Q ^ (ε / 528)) ^ (m * 2) := pow_le_pow_left₀ hK0.le hK _
      _ = Q ^ (ε / 528 * (m * 2 : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ Q ^ (ε / 12) := Real.rpow_le_rpow_of_exponent_le hQ1 (by push_cast; nlinarith)
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ 22 := pow_le_pow_right₀ (by norm_num) hm
  have hpow : Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (2 - 2 * σ + ε) := by
    conv_lhs => rw [show Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0]; ring_nf
  have hΛQ : Λ ^ (2 - 2 * σ + ε) ≤ Q ^ ((6 / 5 + 3 / 2 * ε) * (2 - 2 * σ + ε)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow hΛ0.le hΛ (by linarith)
  have hexp : (6 / 5 + 3 / 2 * ε) * (2 - 2 * σ + ε) + ε / 12 ≤ (12 / 5 + 53 * ε) * (1 - σ) := by
    nlinarith [mul_nonneg hε.le (sub_nonneg.2 hσ11), mul_nonneg hε.le (sub_nonneg.2 hε1)]
  have hG0 : 0 ≤ Gm (ε / 88) P m σb := by unfold Gm; positivity
  calc 2 * (8 * 2 ^ m) * Gm (ε / 88) P m σb * Λ / ((1 / (4 * K)) ^ m) ^ 2
      = 2 * (8 * 2 ^ m) * Gm (ε / 88) P m σb * Λ * (4 * K) ^ (m * 2) := by
        rw [one_div, inv_pow, inv_pow, div_inv_eq_mul, ← pow_mul]
    _ ≤ 2 * (8 * 2 ^ 22) * (A ^ 22 * Λ ^ (1 - 2 * σ + ε)) * Λ * Q ^ (ε / 12) := by gcongr
    _ = 16 * 2 ^ 22 * A ^ 22 * (Λ ^ (1 - 2 * σ + ε) * Λ) * Q ^ (ε / 12) := by ring
    _ = 16 * 2 ^ 22 * A ^ 22 * Λ ^ (2 - 2 * σ + ε) * Q ^ (ε / 12) := by rw [hpow]
    _ ≤ 16 * 2 ^ 22 * A ^ 22 * Q ^ ((6 / 5 + 3 / 2 * ε) * (2 - 2 * σ + ε)) * Q ^ (ε / 12) := by gcongr
    _ = 16 * 2 ^ 22 * A ^ 22 * Q ^ ((6 / 5 + 3 / 2 * ε) * (2 - 2 * σ + ε) + ε / 12) := by
        rw [mul_assoc _ (Q ^ _), ← Real.rpow_add hQ0]
    _ ≤ 16 * 2 ^ 22 * A ^ 22 * Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 hexp) (by positivity)

/-- The exponent of the second term: `(4/5 + ε)(4 − 6σ + 3ε) + 1 + 2ε ≤ (12/5 + 53ε)(1 − σ)` for `3/4 ≤ σ ≤ 11/12` and
`0 < ε ≤ 1/200`; the difference is `(12σ − 9)/5 + 47ε(11/12 − σ) + 3ε(1/200 − ε) + 901ε/600`. -/
lemma exp2_le {ε σ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hσ : 3 / 4 ≤ σ) (hσ11 : σ ≤ 11 / 12) :
    (4 / 5 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) ≤ (12 / 5 + 53 * ε) * (1 - σ) := by
  have key : (12 / 5 + 53 * ε) * (1 - σ) - ((4 / 5 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4)) =
      (12 * σ - 9) / 5 + 47 * (ε * (11 / 12 - σ)) + 3 * (ε * (1 / 200 - ε)) + 901 / 600 * ε := by ring
  have h1 : 0 ≤ ε * (11 / 12 - σ) := mul_nonneg hε.le (by linarith)
  have h2 : 0 ≤ ε * (1 / 200 - ε) := mul_nonneg hε.le (by linarith)
  have h3 : 0 ≤ (12 * σ - 9) / 5 + 47 * (ε * (11 / 12 - σ)) + 3 * (ε * (1 / 200 - ε)) + 901 / 600 * ε := by
    have : 0 ≤ (12 * σ - 9) / 5 := by linarith
    positivity
  linarith

/-- `G_m(σ_b)³ ≤ (4C⁴)^{66}Λ^{3−6σ+3ε}` for `m ≤ 22`, `σ ≤ σ_b`, `σ ≤ 1` (`Gm_le` cubed). -/
lemma Gm3_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {σ σb : ℝ} (hσ1 : σ ≤ 1) (hσb : σ ≤ σb) {P m : ℕ}
    (hP : 1 ≤ P) (hm : m ≤ 22) :
    Gm (ε / 88) P m σb ^ 3 ≤ (4 * Cdiv (ε / 88) ^ 4) ^ 66 * (((2 * P : ℕ) : ℝ) ^ m) ^ (3 - 6 * σ + 3 * ε) := by
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hεd : 0 < ε / 88 := by positivity
  have hεd1 : ε / 88 ≤ 1 := by linarith
  set A : ℝ := 4 * Cdiv (ε / 88) ^ 4 with hA
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
  have hGm : Gm (ε / 88) P m σb ≤ A ^ 22 * Λ ^ (1 - 2 * σ + ε) := by
    refine (Gm_le hεd hεd1 hP m hσ1 hσb).trans ?_
    rw [← hA, ← hΛdef]
    exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
      (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)
  have hG0 : 0 ≤ Gm (ε / 88) P m σb := by unfold Gm; positivity
  calc Gm (ε / 88) P m σb ^ 3 ≤ (A ^ 22 * Λ ^ (1 - 2 * σ + ε)) ^ 3 := pow_le_pow_left₀ hG0 hGm 3
    _ = A ^ 66 * Λ ^ (3 - 6 * σ + 3 * ε) := by
        rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (Λ ^ (1 - 2 * σ + ε)), ← Real.rpow_mul hΛ0.le]
        congr 2; push_cast; ring

/-- `hxA² ≤ 40(24·KG·CG)²ΛQ^{1+3ε/2}` at `η = ε/200`, `U = N = Λ`, with the far tail cut off (`hxA_le_two`) and the
sizes of `A1_sq_le`. -/
lemma hxA_sq_le [NeZero q] {ε τ T Λ Q : ℝ} {X J : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hQ1 : 1 ≤ Q) (hT : 0 ≤ T)
    (hqT : (q : ℝ) * (T + 2) ≤ Q) (hΛ : 0 ≤ Λ) (hX1 : 1 ≤ X) (hXQ : (X : ℝ) ≤ Q ^ (25 : ℝ))
    (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (ε / 4)) (hJ : (J : ℝ) + 2 ≤ Q ^ (ε / 8)) (hL : LSmax X ≤ Q ^ (ε / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8)) (hEQ : EQ q ≤ Q ^ (ε / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    hxA q τ (ε / 200) T Λ Λ X J ^ 2 ≤ 40 * (24 * InghamDensity.KG * CG) ^ 2 * Λ * Q ^ (1 + 3 / 2 * ε) := by
  have hx := hxA_le_two (q := q) (τ := τ) (η := ε / 200) (U := Λ) (N := Λ) hτ1 (by positivity) hT hΛ hΛ hX1 hfar
  have hA1sq := A1_sq_le (q := q) (τ := τ) (Λ := Λ) hε hε1 hQ1 hT hqT hΛ hX1 hXQ (by linarith) hτQ hJ hL hB hEQ
  have hx0 : 0 ≤ hxA q τ (ε / 200) T Λ Λ X J := hxA_nonneg q hT X J
  have h2 := pow_le_pow_left₀ hx0 hx 2
  rw [mul_pow] at h2
  linarith

/-- Five bounds multiplied. -/
lemma prod5_le {a p g x k a' p' g' x' k' : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (hg : 0 ≤ g) (hx : 0 ≤ x) (hk : 0 ≤ k)
    (h1 : a ≤ a') (h2 : p ≤ p') (h3 : g ≤ g') (h4 : x ≤ x') (h5 : k ≤ k') :
    a * p * g * x * k ≤ a' * p' * g' * x' * k' := by
  have ha' : 0 ≤ a' := ha.trans h1
  have hp' : 0 ≤ p' := hp.trans h2
  have hg' : 0 ≤ g' := hg.trans h3
  have hx' : 0 ≤ x' := hx.trans h4
  exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h1 h2 hp ha') h3 hg (mul_nonneg ha' hp')) h4 hx
    (mul_nonneg (mul_nonneg ha' hp') hg')) h5 hk (mul_nonneg (mul_nonneg (mul_nonneg ha' hp') hg') hx')

/-- The product of the five bounds of the second term as a power of `Q`. -/
lemma final2_le {Q Λ A C ε σ : ℝ} (hQ1 : 1 ≤ Q) (hΛ0 : 0 < Λ) (hC : 0 ≤ C)
    (hΛQ : Λ ^ (4 - 6 * σ + 3 * ε) ≤ Q ^ ((4 / 5 + ε) * (4 - 6 * σ + 3 * ε)))
    (hexp : (4 / 5 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) ≤ (12 / 5 + 53 * ε) * (1 - σ)) :
    2 ^ 50 * Q ^ (ε / 4) * (A ^ 66 * Λ ^ (3 - 6 * σ + 3 * ε)) * (C * Λ * Q ^ (1 + 3 / 2 * ε)) * Q ^ (ε / 4) ≤
      2 ^ 50 * C * A ^ 66 * Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hΛpow : Λ ^ (3 - 6 * σ + 3 * ε) * Λ = Λ ^ (4 - 6 * σ + 3 * ε) := by
    conv_lhs => rw [show Λ ^ (3 - 6 * σ + 3 * ε) * Λ = Λ ^ (3 - 6 * σ + 3 * ε) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0]; ring_nf
  have eQ : Q ^ (ε / 4) * Q ^ (1 + 3 / 2 * ε) * Q ^ (ε / 4) = Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
  have hD : 0 ≤ 2 ^ 50 * C * A ^ 66 := by positivity
  have hQe : 0 ≤ Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by positivity
  calc 2 ^ 50 * Q ^ (ε / 4) * (A ^ 66 * Λ ^ (3 - 6 * σ + 3 * ε)) * (C * Λ * Q ^ (1 + 3 / 2 * ε)) * Q ^ (ε / 4)
      = (2 ^ 50 * C * A ^ 66) * (Λ ^ (3 - 6 * σ + 3 * ε) * Λ) *
          (Q ^ (ε / 4) * Q ^ (1 + 3 / 2 * ε) * Q ^ (ε / 4)) := by ring
    _ = (2 ^ 50 * C * A ^ 66) * Λ ^ (4 - 6 * σ + 3 * ε) * Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) := by
        rw [hΛpow, eQ]
    _ ≤ (2 ^ 50 * C * A ^ 66) * Q ^ ((4 / 5 + ε) * (4 - 6 * σ + 3 * ε)) *
          Q ^ (ε / 4 + (1 + 3 / 2 * ε) + ε / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΛQ hD) hQe
    _ = (2 ^ 50 * C * A ^ 66) * Q ^ ((4 / 5 + ε) * (4 - 6 * σ + 3 * ε) + (ε / 4 + (1 + 3 / 2 * ε) + ε / 4)) := by
        rw [mul_assoc, ← Real.rpow_add hQ0]
    _ ≤ 2 ^ 50 * C * A ^ 66 * Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1 hexp) hD

/-- **The second term**: with `Λ = (2P)^m ≥ Q^{4/5+ε}`, `m ≤ 22`, `4K ≤ Q^{ε/528}`, the far tail cut off and the sizes
of `A1_sq_le`, `c₀⁻²4^{ω(q)}G_m(σ_b)³hxA²(4K)^{6m} ≤ 2^{50}·40(24·KG·CG)²(4C⁴)^{66}Q^{(12/5+53ε)(1−σ)}` for
`3/4 ≤ σ ≤ σ_b`, `σ ≤ 11/12`: `G_m³ ≤ (4C⁴)^{66}Λ^{3−6σ+3ε}` (`Gm3_le`), `hxA² ≤ 4A₁²` (`hxA_sq_le`), and
`Λ^{4−6σ+3ε} ≤ Q^{(4/5+ε)(4−6σ+3ε)}` because `4 − 6σ + 3ε < 0`; the exponents are compared in `exp2_le`. -/
lemma term2_le [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {σ σb Q T τ : ℝ} (hσ : 3 / 4 ≤ σ)
    (hσ11 : σ ≤ 11 / 12) (hσb : σ ≤ σb) (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 22) (hΛlo : Q ^ (4 / 5 + ε) ≤ ((2 * P : ℕ) : ℝ) ^ m)
    {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ Q ^ (ε / 528))
    {X J : ℕ} (hX1 : 1 ≤ X) (hXQ : (X : ℝ) ≤ Q ^ (25 : ℝ)) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (ε / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (ε / 8)) (hL : LSmax X ≤ Q ^ (ε / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8)) (hEQ : EQ q ≤ Q ^ (ε / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (ε / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / 88) P m σb ^ 3 *
        hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) ((2 * P) ^ m : ℕ) X J ^ 2 / ((1 / (4 * K)) ^ m) ^ 6
      ≤ 2 ^ 50 * (40 * (24 * InghamDensity.KG * CG) ^ 2) * (4 * Cdiv (ε / 88) ^ 4) ^ 66 *
        Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ ((2 * P : ℕ) : ℝ) ^ m := one_le_pow₀ h2P
  have hΛ0 : 0 < ((2 * P : ℕ) : ℝ) ^ m := by linarith
  have hN : ((((2 * P) ^ m : ℕ)) : ℝ) = ((2 * P : ℕ) : ℝ) ^ m := by push_cast; ring
  rw [hN]
  have hεd : 0 < ε / 88 := by positivity
  have hCd := one_le_Cdiv hεd (by linarith)
  have hA0 : 0 ≤ 4 * Cdiv (ε / 88) ^ 4 := by positivity
  have hKG := InghamDensity.KG_pos
  have hCG := CG_pos
  have hC0 : 0 ≤ 40 * (24 * InghamDensity.KG * CG) ^ 2 := by positivity
  have hH := hxA_sq_le (q := q) (τ := τ) (Λ := ((2 * P : ℕ) : ℝ) ^ m) hε hε1 hQ1 hT hqT hΛ0.le hX1 hXQ hτ1 hτQ hJ hL
    hB hEQ hfar
  have hG3 := Gm3_le hε hε1 (σ := σ) (by linarith) hσb hP hm
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (m * 6) ≤ Q ^ (ε / 4) := by
    calc (4 * K) ^ (m * 6) ≤ (Q ^ (ε / 528)) ^ (m * 6) := pow_le_pow_left₀ hK0.le hK _
      _ = Q ^ (ε / 528 * (m * 6 : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ Q ^ (ε / 4) := Real.rpow_le_rpow_of_exponent_le hQ1 (by
          have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
          push_cast; nlinarith)
  have h8 : (8 * (2 : ℝ) ^ m) ^ 2 ≤ 2 ^ 50 := by
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ 22 := pow_le_pow_right₀ (by norm_num) hm
    calc (8 * (2 : ℝ) ^ m) ^ 2 ≤ (8 * 2 ^ 22) ^ 2 := by gcongr
      _ = 2 ^ 50 := by norm_num
  have hPs2 : (q.primeFactors.powerset.card : ℝ) ^ 2 ≤ Q ^ (ε / 4) := by
    calc (q.primeFactors.powerset.card : ℝ) ^ 2 ≤ (Q ^ (ε / 8)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hPs 2
      _ = Q ^ (ε / 4) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; ring_nf
  have hΛQ : (((2 * P : ℕ) : ℝ) ^ m) ^ (4 - 6 * σ + 3 * ε) ≤ Q ^ ((4 / 5 + ε) * (4 - 6 * σ + 3 * ε)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hΛlo (by linarith)
  have hexp := exp2_le hε hε1 hσ hσ11
  have hG0 : 0 ≤ Gm (ε / 88) P m σb ^ 3 := by unfold Gm; positivity
  have hprod := prod5_le (by positivity) (by positivity) hG0 (sq_nonneg _) (by positivity) h8 hPs2 hG3 hH h4K
  have hfin := final2_le (A := 4 * Cdiv (ε / 88) ^ 4) hQ1 hΛ0 hC0 hΛQ hexp
  have e1 : (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / 88) P m σb ^ 3 *
      hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) (((2 * P : ℕ) : ℝ) ^ m) X J ^ 2 / ((1 / (4 * K)) ^ m) ^ 6 =
      (8 * 2 ^ m) ^ 2 * (q.primeFactors.powerset.card : ℝ) ^ 2 * Gm (ε / 88) P m σb ^ 3 *
      hxA q τ (ε / 200) T (((2 * P : ℕ) : ℝ) ^ m) (((2 * P : ℕ) : ℝ) ^ m) X J ^ 2 * (4 * K) ^ (m * 6) := by
    rw [one_div, inv_pow, inv_pow, div_inv_eq_mul, ← pow_mul]
  rw [e1]
  refine hprod.trans (hfin.trans (le_of_eq ?_))
  ring

end LinnikTwelve

#print axioms LinnikTwelve.card_powerset_le_divisors
#print axioms LinnikTwelve.LSmax_le_log
#print axioms LinnikTwelve.hxA_le_two
#print axioms LinnikTwelve.A1_sq_le
#print axioms LinnikTwelve.term1_le
#print axioms LinnikTwelve.term2_le
