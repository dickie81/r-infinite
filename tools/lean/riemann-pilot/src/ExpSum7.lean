/-
# Layer II, step (G2d): growth of the Dirichlet polynomial (round 211)

Plain statement (`growth_sum`). Fix `6/7 ≤ a ≤ 1`. There is an absolute `B` such that, whenever
`log|t| ≥ 1`, `σ ≥ 1 − (log|t|)^{−a}` and `X ≤ |t|^{5/4}`,
  `|Σ_{1≤n≤X} n^{−σ−it}| ≤ B·log|t|`.

Proof. Write `L = log|t|` and `Λ = 128·L^{1−a/6}`.
* Terms with `n ≤ e^Λ` are bounded trivially (`small_part`). Since `n^{1−σ} ≤ e^{Λ L^{−a}} ≤ e^{128}`
  (this is where `a ≥ 6/7` enters: `1 − a/6 − a ≤ 0`), they contribute `O(1 + Λ) = O(L)`.
* The rest splits into at most `3L` dyadic blocks (`dyadic`). On a block `(N, 2N]` with
  `log N ≥ Λ`, the choice `r = ⌈2L/log N⌉` meets every hypothesis of `block_saving` (round 210),
  and Abel summation with weights `n^{−σ}` gives at most `2^{27}` (`big_block`).
-/
import ExpSum6

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder VinoRec

/-- `n^{−s} = n^{−σ}·n^{−it}`. -/
lemma cpow_phase (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    1 / (n : ℂ) ^ ((σ : ℂ) + t * I) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * phaseF t n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [one_div, ← Complex.cpow_neg, neg_add, Complex.cpow_add _ _ hn0]
  congr 1
  · rw [Complex.ofReal_cpow hnr.le]; push_cast; ring_nf
  · unfold phaseF ee
    rw [Complex.cpow_def_of_ne_zero hn0]
    congr 1
    have hl : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log hnr.le]; push_cast; rfl
    rw [hl]
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

/-- **A weighted block.** -/
theorem weighted_block {t σ u : ℝ} {N N' K ℓ r : ℕ} (hr : 2 ≤ r) (hK : K = 5 * r + 5)
    (hℓ : ℓ = K + 2 * K ^ 2 * K) (hu : 2 ≤ u) (hN : (N : ℝ) = u ^ 20)
    (hN1 : N ≤ N') (hN2 : N' ≤ 2 * N) (hℓu : (ℓ : ℝ) ≤ u ^ 4)
    (ht1 : u ^ (5 * r + 3) ≤ |t|) (ht2 : |t| ≤ u ^ (10 * r))
    (hσ0 : 0 ≤ σ) (hσ : 20 * (ℓ : ℝ) ^ 2 * (1 - σ) ≤ 1) :
    ‖∑ n ∈ Ioc N N', 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 2 ^ 27 := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hNr : (0 : ℝ) < N := by rw [hN]; positivity
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; subst hK; nlinarith
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  rw [sum_congr rfl (fun n hn => cpow_phase n (by have := (mem_Ioc.mp hn).1; omega) σ t)]
  set B : ℝ := 2 ^ 27 * N / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) with hB
  have hrpos : 0 < u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := Real.rpow_pos_of_pos hu0 _
  have hab := abel_bound (fun n => phaseF t n) (fun n => (n : ℝ) ^ (-σ)) N N' B
    (by rw [hB]; positivity)
    (fun m hm1 hm2 => block_saving hr hK hℓ hu hN hm1 (by omega) hℓu ht1 ht2)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (fun n hn1 _ => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < n by omega))
      (by push_cast; linarith) (by linarith))
  refine hab.trans ?_
  have h1 : ((N + 1 : ℕ) : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hNr (by push_cast; linarith) (by linarith)
  have h2 : (N : ℝ) ^ (-σ) * N ≤ u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by
    have e : (N : ℝ) ^ (-σ) * N = u ^ (20 * (1 - σ)) := by
      calc (N : ℝ) ^ (-σ) * N = (N : ℝ) ^ (-σ) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ (-σ + 1) := (Real.rpow_add hNr _ _).symm
        _ = (u ^ 20 : ℝ) ^ (-σ + 1) := by rw [hN]
        _ = u ^ (20 * (1 - σ)) := by
            rw [← Real.rpow_natCast u 20, ← Real.rpow_mul hu0.le]; push_cast; ring_nf
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le hu1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  calc ((N + 1 : ℕ) : ℝ) ^ (-σ) * B ≤ (N : ℝ) ^ (-σ) * B := mul_le_mul_of_nonneg_right h1 hB0
    _ = 2 ^ 27 * ((N : ℝ) ^ (-σ) * N) / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by rw [hB]; ring
    _ ≤ 2 ^ 27 * u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by gcongr
    _ = 2 ^ 27 := by field_simp

lemma exp_pow' (ν : ℝ) (k : ℕ) : Real.exp (ν / 20) ^ k = Real.exp (k * ν / 20) := by
  rw [← Real.exp_nat_mul]; ring_nf

set_option maxHeartbeats 800000 in
/-- **A block far from the origin.** -/
theorem big_block {a t σ : ℝ} {N N' : ℕ} (ha1 : 6 / 7 ≤ a) (ha2 : a ≤ 1)
    (hL : 1 ≤ Real.log |t|) (hσ : 1 - Real.log |t| ^ (-a) ≤ σ)
    (hΛ : 128 * Real.log |t| ^ (1 - a / 6) ≤ Real.log N)
    (hN5 : Real.log N ≤ 5 / 4 * Real.log |t|) (hN1 : N ≤ N') (hN2 : N' ≤ 2 * N) :
    ‖∑ n ∈ Ioc N N', 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 2 ^ 27 := by
  set L := Real.log |t| with hLdef
  set ν := Real.log N with hνdef
  have hL0 : 0 < L := by linarith
  have hP1 : 1 ≤ L ^ (1 - a / 6) := Real.one_le_rpow hL (by linarith)
  have hν128 : 128 ≤ ν := by nlinarith
  have hν0 : 0 < ν := by linarith
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [hνdef, h, Nat.cast_zero, Real.log_zero] at hν128; linarith
    · exact h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNexp : (N : ℝ) = Real.exp ν := (Real.exp_log hNr).symm
  have htpos : 0 < |t| := by
    rcases (abs_nonneg t).lt_or_eq with h | h
    · exact h
    · rw [hLdef, ← h, Real.log_zero] at hL; linarith
  have htexp : |t| = Real.exp L := (Real.exp_log htpos).symm
  set q := L / ν with hq
  have hq45 : 4 / 5 ≤ q := by rw [hq, le_div_iff₀ hν0]; linarith
  have hqL : q ≤ L / 128 := by rw [hq]; exact div_le_div_of_nonneg_left hL0.le (by norm_num) hν128
  set r := ⌈2 * q⌉₊ with hrdef
  have hr1 : 2 * q ≤ r := Nat.le_ceil _
  have hr2 : (r : ℝ) < 2 * q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hr : 2 ≤ r := by
    have : (1 : ℝ) < r := by linarith
    exact_mod_cast this
  set K := 5 * r + 5 with hKdef
  set ℓ := K + 2 * K ^ 2 * K with hℓdef
  set u := Real.exp (ν / 20) with hudef
  have hu : 2 ≤ u := by
    have h2 := Real.log_two_lt_d9
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ u := Real.exp_le_exp.mpr (by linarith)
  have hN : (N : ℝ) = u ^ 20 := by rw [hudef, exp_pow', hNexp]; congr 1; push_cast; ring
  have ht2 : |t| ≤ u ^ (10 * r) := by
    rw [hudef, exp_pow', htexp, Real.exp_le_exp]
    have hqν : q * ν = L := by rw [hq]; field_simp
    have : 2 * L ≤ r * ν := by
      have := mul_le_mul_of_nonneg_right hr1 hν0.le
      nlinarith
    push_cast; linarith
  have ht1 : u ^ (5 * r + 3) ≤ |t| := by
    rw [hudef, exp_pow', htexp, Real.exp_le_exp]
    have hqν : q * ν = L := by rw [hq]; field_simp
    have : r * ν < 2 * L + ν := by
      have := mul_lt_mul_of_pos_right hr2 hν0
      nlinarith
    push_cast; nlinarith
  -- the size of `ℓ`
  have hKq : (K : ℝ) ≤ 45 / 2 * q := by rw [hKdef]; push_cast; linarith
  have hK0 : (1 : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hℓq : (ℓ : ℝ) ≤ 2 ^ 16 * q ^ 3 := by
    have e : (ℓ : ℝ) = K + 2 * (K : ℝ) ^ 3 := by rw [hℓdef]; push_cast; ring
    have h3 : (K : ℝ) ^ 3 ≤ (45 / 2 * q) ^ 3 := pow_le_pow_left₀ (by linarith) hKq 3
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 3 := by
      have := pow_le_pow_right₀ hK0 (show 1 ≤ 3 by norm_num); simpa using this
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hq3 : (0 : ℝ) ≤ q ^ 3 := by positivity
    have e2 : (45 / 2 * q) ^ 3 = 91125 / 8 * q ^ 3 := by ring
    rw [e]; linarith
  have hℓu : (ℓ : ℝ) ≤ u ^ 4 := by
    have hε : (5 : ℝ) / 6 ≤ 1 - a / 6 := by linarith
    have hlogL : Real.log L ≤ L ^ (1 - a / 6) / (1 - a / 6) :=
      Real.log_le_rpow_div hL0.le (by linarith)
    have hlogL' : Real.log L ≤ 6 / 5 * L ^ (1 - a / 6) := by
      refine hlogL.trans ?_
      rw [div_le_iff₀ (by linarith)]
      have hP0 : 0 ≤ L ^ (1 - a / 6) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hε hP0]
    have hL3 : L ^ 3 ≤ u ^ 4 := by
      rw [hudef, exp_pow', ← Real.exp_log (pow_pos hL0 3), Real.exp_le_exp, Real.log_pow]
      push_cast; linarith
    have hq3 : 2 ^ 16 * q ^ 3 ≤ L ^ 3 := by
      have hq0 : 0 ≤ q := by linarith
      have := pow_le_pow_left₀ hq0 hqL 3
      have e : (L / 128) ^ 3 = L ^ 3 / 2 ^ 21 := by ring
      rw [e] at this
      have : (0 : ℝ) ≤ L ^ 3 := by positivity
      linarith
    linarith
  -- the saving beats the loss `N^{1−σ}`
  have hσ0 : 0 ≤ σ := by
    have : L ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
    linarith
  have hsave : 20 * (ℓ : ℝ) ^ 2 * (1 - σ) ≤ 1 := by
    rcases le_or_gt (1 - σ) 0 with h | h
    · have : 0 ≤ 20 * (ℓ : ℝ) ^ 2 := by positivity
      nlinarith
    have hδ : 1 - σ ≤ L ^ (-a) := by linarith
    have hP6 : (L ^ (1 - a / 6)) ^ 6 = L ^ (6 - a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
    have hL6 : L ^ 6 * L ^ (-a) = L ^ (6 - a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hL0]; ring_nf
    have hν6 : 2 ^ 42 * L ^ (6 - a) ≤ ν ^ 6 := by
      have := pow_le_pow_left₀ (by positivity) hΛ 6
      rw [mul_pow, hP6] at this; linarith
    have hq6 : q ^ 6 * L ^ (-a) ≤ 1 / 2 ^ 42 := by
      rw [hq, div_pow, div_mul_eq_mul_div, hL6, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hℓ2 : 20 * (ℓ : ℝ) ^ 2 ≤ 2 ^ 37 * q ^ 6 := by
      have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
      have := pow_le_pow_left₀ hℓ0 hℓq 2
      nlinarith
    have hLa : 0 ≤ L ^ (-a) := Real.rpow_nonneg hL0.le _
    calc 20 * (ℓ : ℝ) ^ 2 * (1 - σ) ≤ 2 ^ 37 * q ^ 6 * L ^ (-a) :=
          mul_le_mul hℓ2 hδ h.le (by positivity)
      _ = 2 ^ 37 * (q ^ 6 * L ^ (-a)) := by ring
      _ ≤ 2 ^ 37 * (1 / 2 ^ 42) := by gcongr
      _ ≤ 1 := by norm_num
  exact weighted_block hr rfl rfl hu hN hN1 hN2 hℓu ht1 ht2 hσ0 hsave

/-- **Dyadic decomposition.** -/
theorem dyadic (f : ℕ → ℂ) (N0 X : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ N N', N0 ≤ N → N ≤ N' → N' ≤ 2 * N → N' ≤ X → ‖∑ n ∈ Ioc N N', f n‖ ≤ B) :
    ∀ j : ℕ, ∀ Y, Y ≤ X → Y ≤ 2 ^ j * N0 → ‖∑ n ∈ Ioc N0 Y, f n‖ ≤ j * B := by
  intro j
  induction j with
  | zero =>
    intro Y _ hY
    rw [Finset.Ioc_eq_empty_of_le (by simpa using hY)]
    simp
  | succ j ih =>
    intro Y hYX hY
    rcases le_or_gt Y (2 ^ j * N0) with h | h
    · have := ih Y hYX h
      push_cast
      nlinarith
    · have hN0j : N0 ≤ 2 ^ j * N0 := Nat.le_mul_of_pos_left _ (by positivity)
      rw [← Finset.sum_Ioc_consecutive f hN0j h.le]
      have h1 := ih (2 ^ j * N0) (by omega) le_rfl
      have h2 := hB (2 ^ j * N0) Y hN0j h.le (by rw [pow_succ] at hY; linarith) hYX
      push_cast
      calc _ ≤ ‖∑ n ∈ Ioc N0 (2 ^ j * N0), f n‖ + ‖∑ n ∈ Ioc (2 ^ j * N0) Y, f n‖ := norm_add_le _ _
        _ ≤ j * B + B := add_le_add h1 h2
        _ = (j + 1) * B := by ring

/-- **The initial segment**, bounded trivially. -/
theorem small_part {σ δ Λ t : ℝ} (Y : ℕ) (hY : (Y : ℝ) ≤ 2 * Real.exp Λ) (hΛ : 0 ≤ Λ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 1 - δ ≤ σ) :
    ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 2 * Real.exp (Λ * δ) * (2 + Λ) := by
  have hE : (2 * Real.exp Λ) ^ δ ≤ 2 * Real.exp (Λ * δ) := by
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    have : (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hterm : ∀ n ∈ Ioc 0 Y, ‖1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤
      2 * Real.exp (Λ * δ) * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Ioc.mp hn).1
    have hnY : n ≤ Y := (mem_Ioc.mp hn).2
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    rw [cpow_phase n hn1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
    have hph : ‖phaseF t n‖ ≤ 1 := norm_phaseF t n
    have h1 : (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hnr (by linarith)
    have h2 : (n : ℝ) ^ (δ - 1) = (n : ℝ) ^ δ * (1 / (n : ℝ)) := by
      rw [Real.rpow_sub hn0, Real.rpow_one]; ring
    have h3 : (n : ℝ) ^ δ ≤ (2 * Real.exp Λ) ^ δ :=
      Real.rpow_le_rpow hn0.le (le_trans (by exact_mod_cast hnY) hY) hδ0
    have hpow0 : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hn0.le _
    calc (n : ℝ) ^ (-σ) * ‖phaseF t n‖ ≤ (n : ℝ) ^ (-σ) * 1 :=
          mul_le_mul_of_nonneg_left hph hpow0
      _ ≤ (n : ℝ) ^ δ * (1 / (n : ℝ)) := by rw [mul_one, ← h2]; exact h1
      _ ≤ 2 * Real.exp (Λ * δ) * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (h3.trans hE) (by positivity)
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases Nat.eq_zero_or_pos Y with h0 | hpos
  · subst h0; simp; linarith
  have hharm : ∑ n ∈ Ioc 0 Y, 1 / (n : ℝ) = (harmonic Y : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast
    rw [show Icc 1 Y = Ioc 0 Y by ext n; simp [mem_Icc, mem_Ioc]; omega]
    simp [one_div]
  rw [hharm]
  refine (harmonic_le_one_add_log Y).trans ?_
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hpos
  have := Real.log_le_log hYr hY
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have := Real.log_two_lt_d9
  linarith

/-- **Step (G2d): growth of the Dirichlet polynomial.** -/
theorem growth_sum {a : ℝ} (ha1 : 6 / 7 ≤ a) (ha2 : a ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ t σ : ℝ, 1 ≤ Real.log |t| → 1 - Real.log |t| ^ (-a) ≤ σ →
      ∀ X : ℕ, (X : ℝ) ≤ |t| ^ ((5 : ℝ) / 4) →
        ‖∑ n ∈ Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ B * Real.log |t| := by
  refine ⟨260 * Real.exp 128 + 3 * 2 ^ 27, by positivity, ?_⟩
  intro t σ hL hσ X hX
  set L := Real.log |t| with hLdef
  have hL0 : 0 < L := by linarith
  have htpos : 0 < |t| := by
    rcases (abs_nonneg t).lt_or_eq with h | h
    · exact h
    · rw [hLdef, ← h, Real.log_zero] at hL; linarith
  set δ := L ^ (-a) with hδdef
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hL0.le _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  set Λ := 128 * L ^ (1 - a / 6) with hΛdef
  have hP1 : 1 ≤ L ^ (1 - a / 6) := Real.one_le_rpow hL (by linarith)
  have hPL : L ^ (1 - a / 6) ≤ L := by
    calc L ^ (1 - a / 6) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      _ = L := Real.rpow_one L
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛδ : Λ * δ ≤ 128 := by
    have e : Λ * δ = 128 * L ^ (1 - a / 6 + -a) := by
      rw [hΛdef, hδdef, Real.rpow_add hL0]; ring
    rw [e]
    have : L ^ (1 - a / 6 + -a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
    linarith
  set N0 := ⌈Real.exp Λ⌉₊ with hN0def
  have hN0ge : Real.exp Λ ≤ N0 := Nat.le_ceil _
  have hN0lt : (N0 : ℝ) < Real.exp Λ + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hN0le : (N0 : ℝ) ≤ 2 * Real.exp Λ := by
    have := Real.one_le_exp hΛ0; linarith
  have hN01 : 1 ≤ N0 := by
    have : (1 : ℝ) ≤ N0 := le_trans (Real.one_le_exp hΛ0) hN0ge
    exact_mod_cast this
  set Y := min X N0 with hYdef
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) (min_le_left X N0)]
  -- the initial segment
  have hsmall : ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 260 * Real.exp 128 * L := by
    have hYle : (Y : ℝ) ≤ 2 * Real.exp Λ := by
      have : (Y : ℝ) ≤ N0 := by exact_mod_cast min_le_right X N0
      linarith
    refine (small_part Y hYle hΛ0 hδ0 hδ1 (by linarith)).trans ?_
    have h1 : Real.exp (Λ * δ) ≤ Real.exp 128 := Real.exp_le_exp.mpr hΛδ
    have h2 : 2 + Λ ≤ 130 * L := by nlinarith
    have h128 : 0 < Real.exp 128 := Real.exp_pos _
    calc 2 * Real.exp (Λ * δ) * (2 + Λ) ≤ 2 * Real.exp 128 * (130 * L) := by gcongr
      _ = 260 * Real.exp 128 * L := by ring
  -- the dyadic part
  have hbig : ‖∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ 3 * 2 ^ 27 * L := by
    rcases le_or_gt X N0 with hXN | hXN
    · have : Y = X := min_eq_left hXN
      rw [this, Finset.Ioc_self, Finset.sum_empty, norm_zero]; positivity
    have hY : Y = N0 := min_eq_right hXN.le
    rw [hY]
    have hX0 : X ≠ 0 := by omega
    have hXr : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX0
    have hlogX : Real.log X ≤ 5 / 4 * L := by
      have := Real.log_le_log hXr hX
      rwa [Real.log_rpow htpos] at this
    have hblocks := dyadic (fun n => 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)) N0 X (2 ^ 27) (by positivity)
      (fun N N' hN0N hNN' hN'2 hN'X => by
        have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
        refine big_block ha1 ha2 hL hσ ?_ ?_ hNN' hN'2
        · have := Real.log_le_log (Real.exp_pos _) (hN0ge.trans (show (N0 : ℝ) ≤ N by exact_mod_cast hN0N))
          rwa [Real.log_exp] at this
        · have hNX : (N : ℝ) ≤ X := by exact_mod_cast (hNN'.trans hN'X)
          exact (Real.log_le_log hNr hNX).trans hlogX)
      (Nat.log 2 X + 1) X le_rfl (by
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
        calc X ≤ 2 ^ (Nat.log 2 X + 1) := this.le
          _ ≤ 2 ^ (Nat.log 2 X + 1) * N0 := Nat.le_mul_of_pos_right _ hN01)
    refine hblocks.trans ?_
    have hlog2 : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log X := by
      have h := Nat.pow_log_le_self 2 hX0
      have h' : ((2 ^ Nat.log 2 X : ℕ) : ℝ) ≤ X := by exact_mod_cast h
      have := Real.log_le_log (by positivity) h'
      rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
    have hl2 := Real.log_two_gt_d9
    have hj : (Nat.log 2 X : ℝ) ≤ 2 * L := by
      have : (Nat.log 2 X : ℝ) * 0.6931471803 ≤ 5 / 4 * L := by
        have : (Nat.log 2 X : ℝ) * 0.6931471803 ≤ (Nat.log 2 X : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
        linarith
      nlinarith
    push_cast
    nlinarith
  calc ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I) +
        ∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖
      ≤ ‖∑ n ∈ Ioc 0 Y, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ +
          ‖∑ n ∈ Ioc Y X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * I)‖ := norm_add_le _ _
    _ ≤ 260 * Real.exp 128 * L + 3 * 2 ^ 27 * L := add_le_add hsmall hbig
    _ = (260 * Real.exp 128 + 3 * 2 ^ 27) * L := by ring

end ExpSum
