/-
# Round 527, part 3: the power trick on `3/4 ≤ σ ≤ 11/12` with round 526's estimate, and Linnik's exponent `12/5 + η`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `0 < ε ≤ 1/200`, `CharDensity (12/5 + 54ε) 10 C` holds with some `C ≥ 0`
(`charDensity_twelve_fifths`): for every `q ≥ 1`, `½ ≤ σ ≤ 1` and `T ≥ 2`, at most
`C(qT)^{(12/5+54ε)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. With
round 520's `linnik_of_charDensity`, for every `η > 0` every reduced class mod `q` has a prime `p ≤ K q^{12/5+η}`
(`linnik_twelve_fifths`), with no hypothesis. Round 525 had `87/35 + η`. On `7/12 ≤ σ ≤ 3/4` the count is round
524's Ingham argument at `c = 1/10` (part 1's `count_middle_c10`); on `3/4 ≤ σ ≤ 11/12` it is round 525's detector and
power trick, with round 526's large-values estimate (part 1's `block_bin_hux`) in place of round 525's
Halász–Montgomery count (`LinnikHuxley.power_count`). Ingham's exponent `3/(2 − σ)` equals `12/5` at `σ = 3/4`.

* `class1_twelve`: the polynomial class for `Q^{1/25} ≤ 2X` and `(2XN)² ≤ Q^{6/5+ε}`: some dyadic block is at least
  `1/(4K)`; in bins of width `ε/200` in `β` and in each block, the least `m` with `(2P)^m ≥ Q^{4/5+ε}` (`choose_m`),
  then part 1's `block_bin_hux` with part 2's `term1_le` and `term2_le`.
* `class2_bound_twelve`: round 525's integral class (`class2_count_small`) at `Y = Q^{3/5}`, `X ≤ Q^{1/25}` and
  `δ = 1/4` has at most `27(4KG)⁴C₄Q^{(12/5)(1−σ)}` members.
* `far_cut`, `sieve_range`, `EQ_le_Q`, `powerset_le_Q`, `bkt_le_Q`: at `J = 16⌈log₂(4MQ)⌉`, `M = max(ζ(9/8), 1)`,
  `X_l = ⌈Q²(4Q² + 1)2^J⌉` and `τ = C(ε/200)X_l^{ε/200}` the far tail is cut off, `X_l ≤ Q^{25}`, `τ ≤ Q^{ε/4}`, and
  `J + 2`, `L(X_l)`, `EQ(q)`, `2^{ω(q)}` and `bkt(q(1 + 2T)) + 1` are each at most `Q^{ε/8}`, for all large `Q`
  (`eventually_twelve`).
* `count_twelve_at`, `count_twelve_fifths`: `LinnikDetect.dichotomy` at `X = ⌊Q^{1/25}⌋`, `Y = Q^{3/5}` (round 518's
  `Xw`, `Yw`, `Nw` at `U = Q^{1/25}`, `c = 7`), `Q = q(T + 6)`, for all large `Q`; below that at most `q` characters.
* `charDensity_twelve_fifths`: below `7/12` the trivial count; on `[7/12, 3/4]` `count_middle_c10`; on `[3/4, 11/12]`
  `count_twelve_fifths`; above `11/12` no character `χ ≠ 1` has a zero (`LinnikLindelof.LFunction_ne_zero`).
* `linnik_twelve_fifths`: `linnik_of_charDensity` at `ε = min(η, 1)/216`.
-/

import LinnikTwelveSizes

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikTwelve

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag LinnikHuxley LinnikReflect

variable {q : ℕ}

/-! ### The polynomial class in the range `3/4 ≤ σ ≤ 11/12` -/

/-- The constant of `term1_le`. -/
def B1 (ε : ℝ) : ℝ := 16 * 2 ^ 22 * (4 * Cdiv (ε / 88) ^ 4) ^ 22

/-- The constant of `term2_le`. -/
def B2 (ε : ℝ) : ℝ := 2 ^ 50 * (40 * (24 * InghamDensity.KG * CG) ^ 2) * (4 * Cdiv (ε / 88) ^ 4) ^ 66

lemma B1_nonneg (ε : ℝ) : 0 ≤ B1 ε := by unfold B1; positivity

lemma B2_nonneg (ε : ℝ) : 0 ≤ B2 ε := by unfold B2; positivity

/-- **The polynomial class with Huxley's estimate.** Characters with one point `β_χ + iγ_χ` each, `σ ≤ β_χ < 1`,
`|γ_χ| ≤ T`, and `|P_χ(β_χ + iγ_χ)| ≥ ¼` number at most `(⌊50/ε⌋ + 1)K(B₁ + B₂)Q^{(12/5+53ε)(1−σ)}`,
`K = ⌊log₂ N⌋ + 1`, for `3/4 ≤ σ ≤ 11/12`: some dyadic block is at least `1/(4K)` (`Pvχ_eq_blocks`); bins of width
`ε/200` in `β`; in each block and bin the least power `m` with `(2P)^m ≥ Q^{4/5+ε}` (`choose_m`), at most
`Q^{6/5+3ε/2}` long, and `block_bin_hux` with `term1_le` and `term2_le`. -/
theorem class1_twelve [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200)
    {σ T Q : ℝ} (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 11 / 12) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXQ : Q ^ (1 / 25 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 528))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (6 / 5 + ε))
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
    (Rs.card : ℝ) ≤ ((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * ((B1 ε + B2 ε) *
      Q ^ ((12 / 5 + 53 * ε) * (1 - σ))) := by
  classical
  have hQ0 : 0 < Q := by linarith
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set nb := ⌊50 / ε⌋₊ + 1 with hnb
  set Bb := (B1 ε + B2 ε) * Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) with hBb
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
    have h2Px : Q ^ (1 / 25 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
      have : (2 * (X : ℝ)) ≤ ((2 * P : ℕ) : ℝ) := by
        have h := (by omega : 2 * X ≤ 2 * P)
        have h' : ((2 * X : ℕ) : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h' ⊢; linarith
      linarith
    obtain ⟨m, hm1, hm22, hΛlo, hΛhi⟩ :=
      choose_m hQ1 (by positivity : (0 : ℝ) < 4 / 5 + ε) (by linarith) h2Px
    have hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (6 / 5 + 3 / 2 * ε) := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ Q ^ (6 / 5 + ε) := hXN
          _ ≤ Q ^ (6 / 5 + 3 / 2 * ε) := Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith)
      · rw [show 3 * (4 / 5 + ε) / 2 = 6 / 5 + 3 / 2 * ε by ring]
    have hΛ2 : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ 2 := by
      calc ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (6 / 5 + 3 / 2 * ε) := hΛ
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
      have e : (j : ℝ) * (ε / 200) = ε / 200 * j := by ring
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
      have h1 : 2 * ((q : ℝ) * (1 + 2 * T)) * q + 1 ≤ 4 * Q ^ 2 + 1 := by nlinarith
      have h0 : 0 ≤ 2 * ((q : ℝ) * (1 + 2 * T)) * q + 1 := by positivity
      calc ((2 * P : ℕ) : ℝ) ^ m * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J
          ≤ Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J := by gcongr
        _ ≤ Xl := hXl
    have hcount := block_bin_hux (q := q) (R := Ck k j) hP hSsub (c := b1 X Y) (fun i _ => norm_b1_le X hY i) hm1
      (σb := σb) (η := ε / 200) (by linarith) (by linarith) β γ hbin hT (fun χ hχ => hγ χ (mem_filter.1 hχ).1) hV0
      (fun χ hχ => by rw [← Fkχ_eq_pv]; exact (mem_filter.1 hχ).2.1) (εd := ε / 88) (by positivity)
      (by linarith) J hXl1 hXD hτd
    have ht1 := term1_le hε hε1 hσ1 hσσb hQ1.le hP hm22 hΛ hK1 hK
    have ht2 := term2_le (q := q) hε hε1 hσ hσ1 hσσb hQ1.le hT hqT hP hm22 hΛlo hK1
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

/-- **The integral class as a power of `Q`**: with `Y = Q^{3/5}`, `X ≤ Q^{1/25}`, `q(T + 2) ≤ Q` and `δ = 1/4`,
`27A⁴X⁴M₂ ≤ 27(4KG)⁴C₄Q^{(12/5)(1−σ)}`: the exponent `59/25 − (12/5)σ + ε` falls short of `(12/5)(1 − σ)` by
`1/25 − ε ≥ 0`. -/
lemma class2_bound_twelve {ε C₄ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hC₄ : 0 ≤ C₄) {σ T Q : ℝ}
    (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) {X : ℕ} (hXQ : (X : ℝ) ≤ Q ^ (1 / 25 : ℝ)) :
    27 * (KG * (Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (12 / 5 * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hY : ((Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = Q ^ (12 / 5 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ Q ^ (4 / 25 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (Q ^ (1 / 25 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXQ 4
      _ = Q ^ (4 / 25 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
  have hM : ((q : ℝ) * (T + 2)) ^ (1 + ε) ≤ Q ^ (1 + ε) := Real.rpow_le_rpow (by positivity) hqT (by linarith)
  have hexp : 12 / 5 * (1 / 2 - σ) + 4 / 25 + (1 + ε) ≤ 12 / 5 * (1 - σ) := by linarith
  calc 27 * (KG * (Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      = 27 * (4 * KG) ^ 4 * C₄ * (((Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 *
          ((q : ℝ) * (T + 2)) ^ (1 + ε)) := by ring
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * (Q ^ (12 / 5 * (1 / 2 - σ)) * Q ^ (4 / 25 : ℝ) * Q ^ (1 + ε)) := by
        rw [hY]; gcongr
    _ = 27 * (4 * KG) ^ 4 * C₄ * Q ^ (12 / 5 * (1 / 2 - σ) + 4 / 25 + (1 + ε)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (12 / 5 * (1 - σ)) := by
        gcongr

/-! ### The cut of the far tail and the large-sieve range -/

/-- `W ≤ 2^L ≤ 2W` and `L ≤ 2 log W + 1` for `L = ⌈log₂ W⌉`, `W ≥ 1`. -/
lemma two_pow_ceil_logb {W : ℝ} (hW : 1 ≤ W) :
    W ≤ (2 : ℝ) ^ ⌈Real.logb 2 W⌉₊ ∧ (2 : ℝ) ^ ⌈Real.logb 2 W⌉₊ ≤ 2 * W ∧
      (⌈Real.logb 2 W⌉₊ : ℝ) ≤ 2 * Real.log W + 1 := by
  have hW0 : 0 < W := by linarith
  have hl0 : 0 ≤ Real.logb 2 W := Real.logb_nonneg (by norm_num) hW
  have hc1 : Real.logb 2 W ≤ ⌈Real.logb 2 W⌉₊ := Nat.le_ceil _
  have hc2 : (⌈Real.logb 2 W⌉₊ : ℝ) < Real.logb 2 W + 1 := Nat.ceil_lt_add_one hl0
  have e : (2 : ℝ) ^ Real.logb 2 W = W := Real.rpow_logb (by norm_num) (by norm_num) hW0
  refine ⟨?_, ?_, ?_⟩
  · calc W = (2 : ℝ) ^ Real.logb 2 W := e.symm
      _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 W⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
      _ = (2 : ℝ) ^ ⌈Real.logb 2 W⌉₊ := Real.rpow_natCast _ _
  · calc (2 : ℝ) ^ ⌈Real.logb 2 W⌉₊ = (2 : ℝ) ^ ((⌈Real.logb 2 W⌉₊ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (Real.logb 2 W + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc2.le
      _ = 2 * W := by rw [Real.rpow_add (by norm_num), e, Real.rpow_one]; ring
  · have hl : Real.logb 2 W ≤ 2 * Real.log W := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have := Real.log_two_gt_d9
      have : 0 ≤ Real.log W := Real.log_nonneg hW
      nlinarith
    linarith

/-- `(2^{16L})^{−1/16} = 2^{−L}`. -/
lemma two_pow_sixteen_rpow (L : ℕ) : (((2 ^ (16 * L) : ℕ) : ℝ)) ^ (-(1 / 16 : ℝ)) = ((2 : ℝ) ^ L)⁻¹ := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_neg (by norm_num)]
  congr 1; push_cast; ring

/-- **The far tail is cut off** at `J = 16⌈log₂(4MQ)⌉`, `M = max(ζ(9/8), 1)`, for `q(T + 2) ≤ Q`, `Q ≥ 1`:
`q^{1/4}(2q(1 + 2T))^{3/4}2^{−J/16}ζ(9/8) ≤ 4QM·2^{−J/16} ≤ 1`, since `2^{J/16} ≥ 4MQ`. -/
lemma far_cut [NeZero q] {T Q : ℝ} (hT : 0 ≤ T) (hQ1 : 1 ≤ Q) (hqT : (q : ℝ) * (T + 2) ≤ Q) :
    (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) *
      ((2 ^ (16 * ⌈Real.logb 2 (4 * max zeta98 1 * Q)⌉₊) : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) * zeta98 ≤ 1 := by
  set M := max zeta98 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hζM : zeta98 ≤ M := le_max_left _ _
  have hζ0 := zeta98_nonneg
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hx : (q : ℝ) ≤ 2 * (q * (1 + 2 * T)) := by nlinarith
  have hx4 : 2 * ((q : ℝ) * (1 + 2 * T)) ≤ 4 * Q := by
    have : (q : ℝ) * (1 + 2 * T) ≤ q * (2 * (T + 2)) := mul_le_mul_of_nonneg_left (by linarith) hq0
    linarith
  have hx0 : 0 ≤ 2 * ((q : ℝ) * (1 + 2 * T)) := by positivity
  have hpow : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) ≤ 4 * Q := by
    calc (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ)
        ≤ (2 * (q * (1 + 2 * T))) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) := by
          gcongr
      _ = 2 * (q * (1 + 2 * T)) := by
          rw [← Real.rpow_add' hx0 (by norm_num)]; norm_num
      _ ≤ 4 * Q := hx4
  have hW : 1 ≤ 4 * M * Q := by nlinarith
  obtain ⟨hL1, -, -⟩ := two_pow_ceil_logb hW
  rw [two_pow_sixteen_rpow]
  have h2L : 0 < (2 : ℝ) ^ ⌈Real.logb 2 (4 * M * Q)⌉₊ := by positivity
  have hpow0 : 0 ≤ (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) := by positivity
  calc (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 : ℝ) ^ ⌈Real.logb 2 (4 * M * Q)⌉₊)⁻¹ *
        zeta98 ≤ 4 * Q * ((2 : ℝ) ^ ⌈Real.logb 2 (4 * M * Q)⌉₊)⁻¹ * M := by gcongr
    _ = 4 * M * Q / (2 : ℝ) ^ ⌈Real.logb 2 (4 * M * Q)⌉₊ := by ring
    _ ≤ 1 := by rw [div_le_one h2L]; exact hL1

/-! ### Large `Q` -/

/-- The constant of `EQ(q) ≤ C q^{ε/16}` (`prod_inv_one_sub_le` at `θ = 3/16`). -/
def CEQ (ε : ℝ) : ℝ :=
  ((1 - (2 : ℝ) ^ (-(3 / 16 : ℝ)))⁻¹) ^ ⌈max ((2 : ℝ) ^ (1 / (3 / 16 : ℝ))) ((2 : ℝ) ^ (1 / (ε / 16)))⌉₊

/-- The conditions on `Q` used in the range `3/4 ≤ σ ≤ 11/12` hold for all large `Q` (`ev_log_pow`). -/
lemma eventually_twelve {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM : 1 ≤ M) :
    ∀ᶠ Q : ℝ in atTop, (8 : ℝ) ^ 25 ≤ Q ∧ 4 * (1 + 2 * Real.log Q) ≤ Q ^ (ε / 528) ∧
      (2 * (23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)))) ^ 2 ≤ Q ^ (6 / 5 + ε) ∧
      23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)) ≤ Q ∧ Cdiv (ε / 200) ≤ Q ^ (ε / 8) ∧
      16 * (2 * Real.log (4 * M * Q) + 1) + 2 ≤ Q ^ (ε / 8) ∧ (8 * M * Q) ^ 16 ≤ Q ^ 20 ∧
      8 * Real.exp 1 * 25 * 627 * 50 * (1 + Real.log Q) ^ 4 ≤ Q ^ (ε / 8) ∧
      2 * Real.log (4 * Q) + 1 ≤ Q ^ (ε / 8) ∧ CEQ ε ≤ Q ^ (ε / 16) ∧ Cdiv (ε / 16) ≤ Q ^ (ε / 16) := by
  have hlM : 0 ≤ Real.log (4 * M) := Real.log_nonneg (by linarith)
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 25), ev_log_pow 8 (ε / 528) 1 (by positivity),
    ev_log_pow ((138 / 5) ^ 2) ε 2 hε, ev_log_pow (69 / 5) (2 / 5) 1 (by norm_num),
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
  have hlog : Real.log (Q ^ (3 / 5 : ℝ)) = 3 / 5 * Real.log Q := Real.log_rpow hQ0 _
  simp only [pow_zero, mul_one, pow_one] at h2 h4 h5 h6 h7 h9 h10 h11
  refine ⟨h1, ?_, ?_, ?_, h5, ?_, ?_, h8, ?_, h10, h11⟩
  · linarith
  · have hQ35 : (Q ^ (3 / 5 : ℝ)) ^ 2 = Q ^ (6 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
    calc (2 * (23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)))) ^ 2
        = (138 / 5) ^ 2 * Real.log Q ^ 2 * (Q ^ (3 / 5 : ℝ)) ^ 2 := by rw [hlog]; ring
      _ ≤ (138 / 5) ^ 2 * (1 + Real.log Q) ^ 2 * Q ^ (6 / 5 : ℝ) := by
          rw [hQ35]; gcongr; linarith
      _ ≤ Q ^ ε * Q ^ (6 / 5 : ℝ) := by gcongr
      _ = Q ^ (6 / 5 + ε) := by rw [← Real.rpow_add hQ0]; ring_nf
  · calc 23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)) = 69 / 5 * Real.log Q * Q ^ (3 / 5 : ℝ) := by
          rw [hlog]; ring
      _ ≤ 69 / 5 * (1 + Real.log Q) * Q ^ (3 / 5 : ℝ) := by gcongr; linarith
      _ ≤ Q ^ (2 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by gcongr
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

/-- `ε/528 + (12/5 + 53ε)(1 − σ) ≤ (12/5 + 54ε)(1 − σ)` for `σ ≤ 11/12`. -/
lemma exp_absorb {ε σ : ℝ} (hε : 0 < ε) (hσ1 : σ ≤ 11 / 12) :
    ε / 528 + (12 / 5 + 53 * ε) * (1 - σ) ≤ (12 / 5 + 54 * ε) * (1 - σ) := by
  have h : 0 ≤ ε * (1 - σ - 1 / 528) := mul_nonneg hε.le (by linarith)
  have e : (12 / 5 + 54 * ε) * (1 - σ) - (ε / 528 + (12 / 5 + 53 * ε) * (1 - σ)) = ε * (1 - σ - 1 / 528) := by
    ring
  linarith

/-- `(12/5)(1 − σ) ≤ (12/5 + 54ε)(1 − σ)` for `σ ≤ 1`. -/
lemma exp_twelve_le {ε σ : ℝ} (hε : 0 < ε) (hσ1 : σ ≤ 1) :
    12 / 5 * (1 - σ) ≤ (12 / 5 + 54 * ε) * (1 - σ) := by
  have h0 : 0 ≤ 1 - σ := by linarith
  have h : 0 ≤ 54 * ε * (1 - σ) := by positivity
  have e : (12 / 5 + 54 * ε) * (1 - σ) - 12 / 5 * (1 - σ) = 54 * ε * (1 - σ) := by ring
  linarith

/-- The number `K ≤ Q^{ε/528}/4` of dyadic blocks absorbed into the exponent. -/
lemma absorb_K {ε σ Q nb B K c : ℝ} (hε : 0 < ε) (hσ1 : σ ≤ 11 / 12) (hQ1 : 1 ≤ Q) (hnb : 0 ≤ nb) (hB : 0 ≤ B)
    (hK0 : 0 ≤ K) (hK : 4 * K ≤ Q ^ (ε / 528)) (hc : c ≤ nb * K * (B * Q ^ ((12 / 5 + 53 * ε) * (1 - σ)))) :
    c ≤ nb * B * Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKle : K ≤ Q ^ (ε / 528) := by have := Real.rpow_nonneg hQ0.le (ε / 528); linarith
  have hE1 : Q ^ (ε / 528) * Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) ≤ Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) := by
    rw [← Real.rpow_add hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (exp_absorb hε hσ1)
  have hP0 : 0 ≤ Q ^ ((12 / 5 + 53 * ε) * (1 - σ)) := by positivity
  calc c ≤ nb * K * (B * Q ^ ((12 / 5 + 53 * ε) * (1 - σ))) := hc
    _ ≤ nb * Q ^ (ε / 528) * (B * Q ^ ((12 / 5 + 53 * ε) * (1 - σ))) := by gcongr
    _ = nb * B * (Q ^ (ε / 528) * Q ^ ((12 / 5 + 53 * ε) * (1 - σ))) := by ring
    _ ≤ nb * B * Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) := by gcongr

open scoped Classical in
/-- **The range `3/4 ≤ σ ≤ 11/12` at one large `Q`.** With the detector's `X, N, Y` (`22Y log Y ≤ XN`, `Y = Q^{3/5}`,
`Q^{1/25} ≤ 2X`, `X ≤ Q^{1/25}`), the large-sieve range `X_l`, `J` and `τ` of `class1_twelve`, at most
`(⌊50/ε⌋ + 1)(B₁ + B₂)Q^E + 27(4KG)⁴C₄Q^E` characters `χ ≠ 1` mod `q` have a zero in `Re s ≥ σ`, `|Im s| ≤ T`,
`E = (12/5 + 54ε)(1 − σ)`: `LinnikDetect.dichotomy`, `class1_twelve`, `class2_count_small` and `class2_bound_twelve`. -/
theorem count_twelve_at [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {σ T Q : ℝ} (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 11 / 12) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hY8 : 8 ≤ Y) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hYQ : Y = Q ^ (3 / 5 : ℝ)) (hXU : (X : ℝ) ≤ Q ^ (1 / 25 : ℝ)) (hXU2 : Q ^ (1 / 25 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 528))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (6 / 5 + ε))
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
      ≤ (((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1 ε + B2 ε) + 27 * (4 * KG) ^ 4 * C₄) *
        Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) := by
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
  have hc1 := class1_twelve hε hε1 hσ hσ1 hT hQ1 hqT hX hN hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hB hEQ
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
  have hb2 := class2_bound_twelve (q := q) (σ := σ) hε hε1 hC₄0 hQ1.le hT hqT (X := X) hXU
  rw [hYQ] at hc2
  have hI := absorb_K hε hσ1 hQ1.le (by positivity) (add_nonneg (B1_nonneg ε) (B2_nonneg ε)) (Nat.cast_nonneg _) hK hc1
  have hII : (Z2.card : ℝ) ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) :=
    (hc2.trans hb2).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1.le (exp_twelve_le hε (by linarith))) (by positivity))
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card := by exact_mod_cast card_union_le Z1 Z2
    _ ≤ ((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1 ε + B2 ε) * Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) +
          27 * (4 * KG) ^ 4 * C₄ * Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) := add_le_add hI hII
    _ = (((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1 ε + B2 ε) + 27 * (4 * KG) ^ 4 * C₄) *
          Q ^ ((12 / 5 + 54 * ε) * (1 - σ)) := by ring

/-! ### The sizes at one large `Q` -/

/-- `EQ(q) ≤ Q^{ε/8}` from `EQ(q) ≤ C q^{ε/16}` (`prod_inv_one_sub_le`) and `C ≤ Q^{ε/16}`. -/
lemma EQ_le_Q [NeZero q] {ε Q : ℝ} (hε : 0 < ε) (hQ1 : 1 ≤ Q) (hqQ : (q : ℝ) ≤ Q) (h10 : CEQ ε ≤ Q ^ (ε / 16)) :
    EQ q ≤ Q ^ (ε / 8) := by
  have hQ0 : 0 < Q := by linarith
  have h := prod_inv_one_sub_le (ε := ε / 16) (θ := 3 / 16) (by positivity) (by norm_num) (NeZero.ne q)
  have e : EQ q = ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(3 / 16 : ℝ)))⁻¹ := rfl
  rw [e]
  refine h.trans ?_
  have hc : ((1 - (2 : ℝ) ^ (-(3 / 16 : ℝ)))⁻¹) ^ ⌈max ((2 : ℝ) ^ (1 / (3 / 16 : ℝ))) ((2 : ℝ) ^ (1 / (ε / 16)))⌉₊ =
      CEQ ε := rfl
  rw [hc]
  have hC0 : 0 ≤ CEQ ε := by
    unfold CEQ
    have : (2 : ℝ) ^ (-(3 / 16 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have : 0 < 1 - (2 : ℝ) ^ (-(3 / 16 : ℝ)) := by linarith
    positivity
  calc CEQ ε * (q : ℝ) ^ (ε / 16) ≤ Q ^ (ε / 16) * Q ^ (ε / 16) :=
        mul_le_mul h10 (Real.rpow_le_rpow (Nat.cast_nonneg q) hqQ (by positivity)) (by positivity) (by positivity)
    _ = Q ^ (ε / 8) := by rw [← Real.rpow_add hQ0]; ring_nf

/-- `2^{ω(q)} ≤ Q^{ε/8}` from `2^{ω(q)} ≤ d(q) ≤ C(ε/16)q^{ε/16}` and `C(ε/16) ≤ Q^{ε/16}`. -/
lemma powerset_le_Q [NeZero q] {ε Q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hQ1 : 1 ≤ Q) (hqQ : (q : ℝ) ≤ Q)
    (h11 : Cdiv (ε / 16) ≤ Q ^ (ε / 16)) : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (ε / 8) := by
  have hQ0 : 0 < Q := by linarith
  refine (card_powerset_le_divisors q).trans ((card_divisors_le (ε := ε / 16) (by positivity) (by linarith) q).trans ?_)
  calc Cdiv (ε / 16) * (q : ℝ) ^ (ε / 16) ≤ Q ^ (ε / 16) * Q ^ (ε / 16) :=
        mul_le_mul h11 (Real.rpow_le_rpow (Nat.cast_nonneg q) hqQ (by positivity)) (by positivity) (by positivity)
    _ = Q ^ (ε / 8) := by rw [← Real.rpow_add hQ0]; ring_nf

/-- `bkt(q(1 + 2T)) + 1 ≤ 2 log(4Q) + 1 ≤ Q^{ε/8}` (`bkt_le_log`). -/
lemma bkt_le_Q [NeZero q] {ε T Q : ℝ} (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q)
    (h9 : 2 * Real.log (4 * Q) + 1 ≤ Q ^ (ε / 8)) : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (ε / 8) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hx1 : (1 : ℝ) ≤ q * (1 + 2 * T) := by nlinarith
  have h := bkt_le_log hx1
  have hx2 : 2 * ((q : ℝ) * (1 + 2 * T)) ≤ 4 * Q := by
    have : (q : ℝ) * (1 + 2 * T) ≤ q * (2 * (T + 2)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hl : Real.log (2 * (q * (1 + 2 * T))) ≤ Real.log (4 * Q) := Real.log_le_log (by positivity) hx2
  linarith

/-- **The large-sieve range** at one large `Q`: `J = 16⌈log₂(4MQ)⌉`, `X_l = ⌈Q²(4Q² + 1)2^J⌉` and
`τ = C(ε/200)X_l^{ε/200}` satisfy the size conditions of `class1_twelve`, and the far tail is cut off (`far_cut`). -/
lemma sieve_range [NeZero q] {ε T Q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hT : 0 ≤ T) (hQ : (8 : ℝ) ^ 25 ≤ Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q) (h5 : Cdiv (ε / 200) ≤ Q ^ (ε / 8))
    (h6 : 16 * (2 * Real.log (4 * max zeta98 1 * Q) + 1) + 2 ≤ Q ^ (ε / 8))
    (h7 : (8 * max zeta98 1 * Q) ^ 16 ≤ Q ^ 20)
    (h8 : 8 * Real.exp 1 * 25 * 627 * 50 * (1 + Real.log Q) ^ 4 ≤ Q ^ (ε / 8)) :
    ∃ (Xl J : ℕ) (τ : ℝ), 1 ≤ Xl ∧ (Xl : ℝ) ≤ Q ^ (25 : ℝ) ∧ Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Xl ∧
      (∀ n, n ≤ Xl → (n.divisors.card : ℝ) ≤ τ) ∧ 1 ≤ τ ∧ τ ≤ Q ^ (ε / 4) ∧ (J : ℝ) + 2 ≤ Q ^ (ε / 8) ∧
      LSmax Xl ≤ Q ^ (ε / 8) ∧
      (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
        zeta98 ≤ 1 := by
  have hQ1 : 1 ≤ Q := le_trans (by norm_num) hQ
  have hQ0 : 0 < Q := by linarith
  have hM1 : (1 : ℝ) ≤ max zeta98 1 := le_max_right _ _
  have hW : 1 ≤ 4 * max zeta98 1 * Q := by nlinarith
  obtain ⟨-, hL2, hL3⟩ := two_pow_ceil_logb hW
  have h2J : (2 : ℝ) ^ (16 * ⌈Real.logb 2 (4 * max zeta98 1 * Q)⌉₊) ≤ Q ^ 20 := by
    calc (2 : ℝ) ^ (16 * ⌈Real.logb 2 (4 * max zeta98 1 * Q)⌉₊)
        = ((2 : ℝ) ^ ⌈Real.logb 2 (4 * max zeta98 1 * Q)⌉₊) ^ 16 := by rw [mul_comm, pow_mul]
      _ ≤ (2 * (4 * max zeta98 1 * Q)) ^ 16 := pow_le_pow_left₀ (by positivity) hL2 16
      _ = (8 * max zeta98 1 * Q) ^ 16 := by ring
      _ ≤ Q ^ 20 := h7
  set J := 16 * ⌈Real.logb 2 (4 * max zeta98 1 * Q)⌉₊ with hJdef
  set A := Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J with hA
  have hA0 : 0 < A := by positivity
  have hXl : A ≤ ⌈A⌉₊ := Nat.le_ceil A
  have hXl1 : 1 ≤ ⌈A⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hA0).ne'
  have hXlQ : (⌈A⌉₊ : ℝ) ≤ Q ^ (25 : ℝ) := by
    have h1 : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0.le
    have hQ2 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ1
    have h2 : A ≤ 5 * Q ^ 24 := by
      rw [hA]
      calc Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Q ^ 2 * (5 * Q ^ 2) * Q ^ 20 := by gcongr; linarith
        _ = 5 * Q ^ 24 := by ring
    have h3 : (1 : ℝ) ≤ Q ^ 24 := one_le_pow₀ hQ1
    have h4 : 6 * Q ^ 24 ≤ Q ^ 25 := by
      have : (6 : ℝ) ≤ Q := le_trans (by norm_num) hQ
      calc 6 * Q ^ 24 ≤ Q * Q ^ 24 := by gcongr
        _ = Q ^ 25 := by ring
    rw [show (25 : ℝ) = ((25 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    linarith
  have hεd : 0 < ε / 200 := by positivity
  have hCd1 := one_le_Cdiv hεd (by linarith)
  refine ⟨⌈A⌉₊, J, Cdiv (ε / 200) * ((⌈A⌉₊ : ℕ) : ℝ) ^ (ε / 200), hXl1, hXlQ, hXl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    refine (card_divisors_le (ε := ε / 200) hεd (by linarith) n).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hεd.le)
      (by positivity)
  · exact one_le_mul_of_one_le_of_one_le hCd1 (Real.one_le_rpow (by exact_mod_cast hXl1) hεd.le)
  · calc Cdiv (ε / 200) * ((⌈A⌉₊ : ℕ) : ℝ) ^ (ε / 200) ≤ Q ^ (ε / 8) * (Q ^ (25 : ℝ)) ^ (ε / 200) :=
          mul_le_mul h5 (Real.rpow_le_rpow (Nat.cast_nonneg _) hXlQ hεd.le) (by positivity) (by positivity)
      _ = Q ^ (ε / 4) := by rw [← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0]; ring_nf
  · have : (J : ℝ) ≤ 16 * (2 * Real.log (4 * max zeta98 1 * Q) + 1) := by rw [hJdef]; push_cast; linarith
    linarith
  · exact (LSmax_le_log hXl1 hQ1 hXlQ).trans h8
  · exact far_cut hT hQ1 hqT

open scoped Classical in
/-- **The range `3/4 ≤ σ ≤ 11/12`.** For every `0 < ε ≤ 1/200` there is `C ≥ 0` such that for every `q ≥ 1`,
`3/4 ≤ σ ≤ 11/12` and `T ≥ 2` at most `C Q^{(12/5+54ε)(1−σ)}`, `Q = q(T + 6)`, characters `χ ≠ 1` mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. For `Q ≥ Q₀` (`eventually_twelve`), `count_twelve_at` at round 525's detector
(`X = ⌊Q^{1/25}⌋`, `Y = Q^{3/5}`) and the large-sieve range of `sieve_range`; below `Q₀` at most `q ≤ Q₀` characters
are counted. -/
theorem count_twelve_fifths {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 3 / 4 ≤ σ → σ ≤ 11 / 12 → 2 ≤ T →
      ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ C * ((q : ℝ) * (T + 6)) ^ ((12 / 5 + 54 * ε) * (1 - σ)) := by
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
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (eventually_twelve hε hM1)
  have hKG := KG_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((⌊50 / ε⌋₊ + 1 : ℕ) : ℝ) * (B1 ε + B2 ε) + 27 * (4 * KG) ^ 4 * C₄ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; have := B1_nonneg ε; have := B2_nonneg ε; positivity
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
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (12 / 5 + 54 * ε) * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (by positivity) (by linarith)
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
  -- the detector at `U = Q^{1/25}` (as in `count_huxley`)
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Q ^ (1 / 25 : ℝ) := ⟨_, rfl⟩
  have hU8 : 8 ≤ U := by
    rw [hU]
    calc (8 : ℝ) = ((8 : ℝ) ^ 25) ^ (1 / 25 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ Q ^ (1 / 25 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hYQ : Yw 7 U = Q ^ (3 / 5 : ℝ) := by rw [hU]; exact Yw_seven hQ0
  have hX : 1 ≤ Xw U := Xw_one hU8
  have hN : 1 ≤ Nw 7 U := Nw_one
  have hY8 : 8 ≤ Yw 7 U := le_trans hU8 (Yw_ge (by norm_num) hU8)
  have hM : 22 * Yw 7 U * Real.log (Yw 7 U) ≤ ((Xw U * Nw 7 U : ℕ) : ℝ) := XN_ge hU8
  have hXNle : ((Xw U * Nw 7 U : ℕ) : ℝ) ≤ 23 * Yw 7 U * Real.log (Yw 7 U) := XN_le (by norm_num) hU8
  have hXU : (Xw U : ℝ) ≤ Q ^ (1 / 25 : ℝ) := hU ▸ Xw_le hU8
  have hXU2 : Q ^ (1 / 25 : ℝ) ≤ 2 * (Xw U : ℝ) := by have := Xw_half hU8; rw [← hU]; linarith
  have hXr : (1 : ℝ) ≤ Xw U := by exact_mod_cast hX
  have hNQ : (Nw 7 U : ℝ) ≤ Q := by
    have h1 : (Nw 7 U : ℝ) ≤ ((Xw U * Nw 7 U : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    rw [hYQ] at hXNle
    linarith
  have hK : 4 * ((Nat.log 2 (Nw 7 U) + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 528) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNQ) (by norm_num)).trans h2
  have hXN : (2 * ((Xw U * Nw 7 U : ℕ) : ℝ)) ^ 2 ≤ Q ^ (6 / 5 + ε) := by
    refine le_trans ?_ h3
    rw [← hYQ]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hqT : (q : ℝ) * (T + 2) ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  -- the large-sieve range and the sizes of `bkt`, `EQ` and `2^{ω(q)}`
  obtain ⟨Xl, J, τ, hXl1, hXlQ, hXl, hτd, hτ1, hτQ, hJ, hL, hfar⟩ :=
    sieve_range (q := q) hε hε1 (by linarith : (0 : ℝ) ≤ T) h1 hqT h5 h6 h7 h8
  have hBk := bkt_le_Q (q := q) (ε := ε) (by linarith : (0 : ℝ) ≤ T) hqT h9
  have hEQ := EQ_le_Q (q := q) hε hQ1 hqQ h10
  have hPs := powerset_le_Q (q := q) hε hε1 hQ1 hqQ h11
  have hcount := count_twelve_at (q := q) (σ := σ) (T := T) (Q := Q) hε hε1 hC₄0 (h4all q) hσ hσ1 (by linarith)
    (by linarith) hqT hX hN hY8 hM hYQ hXU hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hBk hEQ hPs hfar
  rw [← hE, ← hB] at hcount
  calc _ ≤ B * Q ^ E := hcount
    _ ≤ (max Q₀ 0 + B) * Q ^ E := by
        have : 0 ≤ max Q₀ 0 * Q ^ E := by positivity
        rw [add_mul]; linarith

/-! ### Density over the characters -/

/-- The constant of `charDensity_twelve_fifths`. -/
def CDT (C₄ CT : ℝ) : ℝ :=
  2 ^ 10 + 256 * 3 ^ 10 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (1 / 12)) + (KG / (1 / 12)) ^ 2 * C₄))
    + 256 * 2 ^ 10 * CT

open scoped Classical in
/-- **A density estimate over the characters mod `q` with exponent `12/5`**: for every `0 < ε ≤ 1/200` there is
`C ≥ 0` with `CharDensity (12/5 + 54ε) 10 C`. Below `σ = 7/12`, where `(12/5)(1 − σ) ≥ 1`, at most `q ≤ qT`
characters are counted; between `7/12` and `3/4`, Ingham's method at `c = 1/10` (`count_middle_c10`); between `3/4`
and `11/12`, the power trick and the large-values estimate of round 526 (`count_twelve_fifths`); above `11/12` no
character `χ ≠ 1` has a zero (`LinnikLindelof.LFunction_ne_zero`). Both counted ranges are measured at
`Q = q(T + 6) ≤ 4qT`. -/
theorem charDensity_twelve_fifths {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ C : ℝ, 0 ≤ C ∧ CharDensity (12 / 5 + 54 * ε) 10 C := by
  obtain ⟨C₄', hC₄'⟩ := LinnikFourth.fourth_moment hε (by linarith : ε ≤ 1)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = max C₄' 0 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := hC₄ ▸ le_max_right _ _
  have h4all : ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) →
      ∀ T' : ℝ, 0 ≤ T' → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε) := by
    intro q _ R hR T' hT' t ht
    refine (hC₄' q R hR T' hT' t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₄ ▸ le_max_left _ _) (by positivity)
  obtain ⟨CT, hCT0, hCT⟩ := count_twelve_fifths hε hε1
  have hKG := KG_pos
  have hCDT0 : 0 ≤ CDT C₄ CT := by unfold CDT; positivity
  refine ⟨CDT C₄ CT, hCDT0, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((q : ℝ) * T) := ⟨_, rfl⟩
  rw [← hℓdef]
  have hℓ : 1 / 2 ≤ ℓ := hℓdef ▸ half_le_log hqT
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (12 / 5 + 54 * ε) * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (by positivity) (by linarith)
  have hE4 : E ≤ 4 := by rw [hE]; nlinarith
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
  obtain ⟨Mc, hMc⟩ : ∃ x : ℝ, x = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (1 / 12)) + (KG / (1 / 12)) ^ 2 * C₄) :=
    ⟨_, rfl⟩
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hCDTe : CDT C₄ CT = 2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CT := by rw [hMc]; rfl
  rw [hCDTe]
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
  have hrest : 0 ≤ (256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by positivity
  rcases lt_or_ge σ (7 / 12) with hsmall | hmid
  · -- below `7/12`: at most `q ≤ qT ≤ (qT)^E` characters
    have hE1 : 1 ≤ E := by rw [hE]; nlinarith
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ (q : ℝ) * T := by nlinarith
      _ = ((q : ℝ) * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((q : ℝ) * T) ^ E := Real.rpow_le_rpow_of_exponent_le (by linarith) hE1
      _ ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := le_mul_of_one_le_right hpowE h2ℓ
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith
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
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith
  -- `Q = q(T + 6) ≤ 4qT`
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 256 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by linarith) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (4 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 256 * ((q : ℝ) * T) ^ E := by norm_num
  have hQE0 : 0 ≤ ((q : ℝ) * (T + 6)) ^ E := by positivity
  rcases lt_or_ge σ (3 / 4) with hlow | hhux
  · -- between `7/12` and `3/4`: Ingham's method at `c = 1/10`
    have hZ := count_middle_c10 hε (by linarith) hC₄0 (h4all q) hmid hlow.le hT
    rw [← hMc] at hZ
    have hL0 : 2 ≤ Real.log ((q : ℝ) * (T + 6)) := log_ge_two hQ8
    have hLQ : Real.log ((q : ℝ) * (T + 6)) ≤ 3 * ℓ := by
      have h2 : Real.log ((q : ℝ) * (T + 6)) ≤ Real.log (4 * ((q : ℝ) * T)) := Real.log_le_log (by linarith) hQ4
      rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < q * T).ne'] at h2
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have h5 : Real.log 2 ≤ ℓ := hℓdef ▸ Real.log_le_log (by norm_num) hqT
      rw [← hℓdef] at h2
      linarith
    have hL10 : Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ 3 ^ 10 * ℓ ^ 10 := by
      calc Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ (3 * ℓ) ^ 10 := by gcongr
        _ = 3 ^ 10 * ℓ ^ 10 := by ring
    have hQE' : ((q : ℝ) * (T + 6)) ^ ((12 / 5 + 4 * ε) * (1 - σ)) ≤ ((q : ℝ) * (T + 6)) ^ E :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hE]; nlinarith)
    have hlog0 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by positivity
    have hstep : Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((12 / 5 + 4 * ε) * (1 - σ)) ≤
        Mc * (3 ^ 10 * ℓ ^ 10) * (256 * ((q : ℝ) * T) ^ E) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL10 hMc0) (hQE'.trans hQE) (by positivity) (by positivity)
    have hCT : 0 ≤ 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by positivity
    calc _ ≤ _ := hF
      _ ≤ Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((12 / 5 + 4 * ε) * (1 - σ)) +
            ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
      _ ≤ Mc * (3 ^ 10 * ℓ ^ 10) * (256 * ((q : ℝ) * T) ^ E) + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := by
          linarith
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith
  · -- between `3/4` and `11/12`: the power trick and the large-values estimate of round 526
    have hZ := hCT q σ T hhux hle hT
    rw [← hE] at hZ
    have hstep : CT * ((q : ℝ) * (T + 6)) ^ E ≤ 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by
      calc CT * ((q : ℝ) * (T + 6)) ^ E ≤ CT * (256 * ((q : ℝ) * T) ^ E) := by gcongr
        _ = 256 * CT * ((q : ℝ) * T) ^ E * 1 := by ring
        _ ≤ 256 * CT * ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) :=
            mul_le_mul_of_nonneg_left h2ℓ (by positivity)
        _ = 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
    have hM : 0 ≤ 256 * 3 ^ 10 * Mc * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by positivity
    calc _ ≤ _ := hF
      _ ≤ CT * ((q : ℝ) * (T + 6)) ^ E + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith

/-! ### Linnik's exponent `12/5 + η` -/

/-- **Linnik's theorem with exponent `12/5 + η`, with no hypothesis.** For every `η > 0` there is `K` such that for
every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{12/5 + η}`: round 520's
`linnik_of_charDensity` fed `charDensity_twelve_fifths` at `ε = min(η, 1)/216`. -/
theorem linnik_twelve_fifths {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (12 / 5 + η) := by
  have hmin : 0 < min η 1 := lt_min hη one_pos
  have hε0 : 0 < min η 1 / 216 := by positivity
  have hε1 : min η 1 / 216 ≤ 1 / 200 := by have := min_le_right η 1; linarith
  obtain ⟨C, hC0, hD⟩ := charDensity_twelve_fifths hε0 hε1
  obtain ⟨K, hK⟩ := linnik_of_charDensity (by nlinarith : (2 : ℝ) ≤ 12 / 5 + 54 * (min η 1 / 216))
    (by norm_num) hC0 hD (half_pos hη)
  refine ⟨max K 0, fun q _ a ha => ?_⟩
  obtain ⟨p, hp, hpa, hpK⟩ := hK q a ha
  refine ⟨p, hp, hpa, hpK.trans ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hexp : 12 / 5 + 54 * (min η 1 / 216) + η / 2 ≤ 12 / 5 + η := by
    have := min_le_left η 1; linarith
  calc K * (q : ℝ) ^ (12 / 5 + 54 * (min η 1 / 216) + η / 2)
      ≤ max K 0 * (q : ℝ) ^ (12 / 5 + 54 * (min η 1 / 216) + η / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * (q : ℝ) ^ (12 / 5 + η) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hexp) (le_max_right _ _)

end LinnikTwelve

#print axioms LinnikTwelve.class1_twelve
#print axioms LinnikTwelve.class2_bound_twelve
#print axioms LinnikTwelve.far_cut
#print axioms LinnikTwelve.eventually_twelve
#print axioms LinnikTwelve.count_twelve_at
#print axioms LinnikTwelve.sieve_range
#print axioms LinnikTwelve.count_twelve_fifths
#print axioms LinnikTwelve.charDensity_twelve_fifths
#print axioms LinnikTwelve.linnik_twelve_fifths
