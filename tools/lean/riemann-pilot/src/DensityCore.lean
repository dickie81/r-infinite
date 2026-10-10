import Mathlib
import DirMean
import DivSq
import ZeroLocal

/-! # Zero density, the counting core (round 235)

The detecting polynomial of a zero `ρ = β + iγ` is `D(ρ) = Σ_{X<j≤XN} a_j j^{−ρ}`, with the
coefficients `a_j = Σ_{m|j, m≤X, j/m≤N} μ(m)` of `M_X(s)·Σ_{n≤N} n^{−s}`, `M_X = Σ_{m≤X} μ(m)m^{−s}`.

`card_detect_le`: if every zero `τ` of `Ξ` in a set `Z` has `|Re τ| ≤ 2U`, `β ≥ σ` and
`|D(ρ)| ≥ ½` (for its zero `ρ = β + iγ` of `ζ` with `β = ½ + |Im τ|`), then
`|Z| ≤ 800 K³(1 + log 2XN)⁶ Kloc(2U + 1)·(U X^{1−2σ} + (XN)^{2−2σ})`, `K = ⌊log₂ N⌋ + 1`.

The steps: one representative zero for each unit window of `|γ|`, split by parity, so the
representatives are 1-separated (`ZeroLocal` bounds each window's multiplicity); the dyadic blocks
`(2^k X, 2^{k+1} X]` of `D`, one of which carries `|D_k(ρ)| ≥ 1/(2K)`; large values off the line
(`DirMean.large_values_off'`) on each block; the divisor bound `Σ d(j)² ≤ M(1 + log M)³`.
-/

open Real Finset

noncomputable section

namespace ShortWeil

open Pilot1ca Pilot1bt DirMean

/-! ## The coefficients -/

/-- `a_j = Σ_{m | j, m ≤ X, j/m ≤ N} μ(m)`. -/
def mollC (X N : ℕ) (j : ℕ) : ℂ :=
  ∑ m ∈ j.divisors, if m ≤ X ∧ j / m ≤ N then ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0

theorem norm_mollC_le (X N j : ℕ) : ‖mollC X N j‖ ≤ (j.divisors.card : ℝ) := by
  unfold mollC
  refine (norm_sum_le _ _).trans ?_
  rw [card_eq_sum_ones, Nat.cast_sum]
  refine sum_le_sum fun m _ => ?_
  split_ifs
  · rw [Complex.norm_intCast]; push_cast
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- **The coefficient mass of a block**: `Σ_{j∈(P,2P]} |a_j|² j^{−2σ} ≤ 2P^{1−2σ}(1 + log 2P)³`. -/
theorem block_mass_le {X N P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Ioc P (2 * P)) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ∑ j ∈ S, ‖mollC X N j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2
      ≤ 2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * P)) ^ 3 := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h1 : ∀ j ∈ S, ‖mollC X N j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2
      ≤ ((j.divisors.card : ℕ) : ℝ) ^ 2 * ((P : ℝ) ^ (-σ)) ^ 2 := by
    intro j hj
    obtain ⟨hj1, _⟩ := mem_Ioc.1 (hS hj)
    have hPj : (P : ℝ) ≤ j := by exact_mod_cast hj1.le
    have hjs : (j : ℝ) ^ (-σ) ≤ (P : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hP0 hPj (by linarith)
    gcongr
    · exact norm_mollC_le X N j
  have h2 : ∑ j ∈ S, ((j.divisors.card : ℕ) : ℝ) ^ 2 ≤ ∑ j ∈ Ioc 0 (2 * P), ((j.divisors.card : ℕ) : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (fun j hj => by
      obtain ⟨h1, h2⟩ := mem_Ioc.1 (hS hj); exact mem_Ioc.2 ⟨by omega, h2⟩) fun _ _ _ => by positivity
  have h3 := DivSq.sum_card_divisors_sq_le (2 * P)
  push_cast at h3
  have hpow : ((P : ℝ) ^ (-σ)) ^ 2 * (2 * P) = 2 * (P : ℝ) ^ (1 - 2 * σ) := by
    rw [show (1 : ℝ) - 2 * σ = 1 + (-σ * 2) by ring, Real.rpow_add hP0, Real.rpow_one,
      ← Real.rpow_natCast ((P : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hP0.le]
    push_cast; ring
  calc ∑ j ∈ S, ‖mollC X N j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ j ∈ S, ((j.divisors.card : ℕ) : ℝ) ^ 2 * ((P : ℝ) ^ (-σ)) ^ 2 := sum_le_sum h1
    _ = (∑ j ∈ S, ((j.divisors.card : ℕ) : ℝ) ^ 2) * ((P : ℝ) ^ (-σ)) ^ 2 := by rw [sum_mul]
    _ ≤ (2 * P * (1 + Real.log (2 * P)) ^ 3) * ((P : ℝ) ^ (-σ)) ^ 2 := by gcongr; exact h2.trans h3
    _ = 2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * P)) ^ 3 := by rw [← hpow]; ring

/-! ## The dyadic blocks -/

/-- The block of `j > X`: `k` with `2^k X < j ≤ 2^{k+1} X`. -/
def blk (X j : ℕ) : ℕ := Nat.log 2 ((j - 1) / X)

theorem blk_mem {X j : ℕ} (hX : 1 ≤ X) (hj : X < j) :
    j ∈ Ioc (2 ^ blk X j * X) (2 * (2 ^ blk X j * X)) := by
  have hq : (j - 1) / X ≠ 0 := by
    rw [Ne, Nat.div_eq_zero_iff]; omega
  have h1 := Nat.pow_log_le_self 2 hq
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((j - 1) / X)
  unfold blk
  set k := Nat.log 2 ((j - 1) / X)
  rw [Nat.le_div_iff_mul_le (by omega)] at h1
  rw [Nat.div_lt_iff_lt_mul (by omega)] at h2
  rw [pow_succ, show 2 ^ k * 2 * X = 2 * (2 ^ k * X) by ring] at h2
  exact mem_Ioc.2 ⟨by omega, by omega⟩

theorem blk_lt {X N j : ℕ} (hX : 1 ≤ X) (hj : j ∈ Ioc X (X * N)) : blk X j < Nat.log 2 N + 1 := by
  obtain ⟨h1, h2⟩ := mem_Ioc.1 hj
  have hq : (j - 1) / X < N := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : j - 1 < X * N := by omega
    linarith [mul_comm X N]
  unfold blk
  exact Nat.lt_succ_of_le (Nat.log_mono_right hq.le)

theorem pow_blk_le {N k : ℕ} (hk : k < Nat.log 2 N + 1) (hN : 1 ≤ N) : 2 ^ k ≤ N :=
  Nat.pow_le_of_le_log (by omega) (by omega)

/-- `D = Σ_k D_k` over the blocks. -/
theorem dp_blocks (X N : ℕ) (hX : 1 ≤ X) (c : ℕ → ℂ) (t : ℝ) :
    dp (Ioc X (X * N)) c t
      = ∑ k ∈ range (Nat.log 2 N + 1), dp ((Ioc X (X * N)).filter (fun j => blk X j = k)) c t := by
  unfold dp
  exact (sum_fiberwise_of_maps_to (fun j hj => mem_range.2 (blk_lt hX hj)) _).symm

theorem block_sub {X N k : ℕ} (hX : 1 ≤ X) :
    (Ioc X (X * N)).filter (fun j => blk X j = k) ⊆ Ioc (2 ^ k * X) (2 * (2 ^ k * X)) := by
  intro j hj
  obtain ⟨hj1, hjk⟩ := mem_filter.1 hj
  rw [← hjk]
  exact blk_mem hX (mem_Ioc.1 hj1).1

/-! ## One block -/

/-- The detecting polynomial `D(β + iγ) = Σ_{X<j≤XN} a_j j^{−β−iγ}`. -/
def DPval (X N : ℕ) (β γ : ℝ) : ℂ :=
  dp (Ioc X (X * N)) (fun j => mollC X N j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) γ

/-- Its `k`-th dyadic block. -/
def Fk (X N k : ℕ) (β γ : ℝ) : ℂ :=
  dp ((Ioc X (X * N)).filter (fun j => blk X j = k)) (fun j => mollC X N j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) γ

theorem DPval_eq (X N : ℕ) (hX : 1 ≤ X) (β γ : ℝ) :
    DPval X N β γ = ∑ k ∈ range (Nat.log 2 N + 1), Fk X N k β γ :=
  dp_blocks X N hX _ γ

/-- **One block**: `c₀²·#{large values} ≤ 32e(1 + log 2XN)⁶(U X^{1−2σ} + (XN)^{2−2σ})`. -/
theorem block_count {σ U : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hU : 2 ≤ U) {X N k : ℕ} (hX : 1 ≤ X)
    (hN : 1 ≤ N) (hk : k < Nat.log 2 N + 1) {ι : Type*} (Rs : Finset ι) (x β : ι → ℝ)
    (hsep : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |x r - x s|) (hx : ∀ r ∈ Rs, |x r| ≤ 2 * U)
    (hβ : ∀ r ∈ Rs, σ ≤ β r ∧ β r ≤ σ + 1 / 2) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hbig : ∀ r ∈ Rs, c₀ ≤ ‖Fk X N k (β r) (x r)‖) :
    (Rs.card : ℝ) * c₀ ^ 2 ≤ 32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
  set P := 2 ^ k * X with hPdef
  have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hPN : P ≤ X * N := by
    rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le hk hN)
  have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hXN0 : (0 : ℝ) < (X : ℝ) * N := by positivity
  have hPNr : (P : ℝ) ≤ X * N := by exact_mod_cast hPN
  have hXPr : (X : ℝ) ≤ P := by exact_mod_cast hXP
  set ℓ := Real.log (2 * X * N) with hℓ
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by nlinarith [mul_le_mul hXr hNr zero_le_one (by linarith)])
  have hlP : Real.log P ≤ ℓ := Real.log_le_log hP0 (by nlinarith)
  have hl2P : Real.log (2 * P) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hlP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
  have hl2P0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by nlinarith [(by exact_mod_cast hP : (1 : ℝ) ≤ P)])
  -- large values on the block
  have hLV := large_values_off' hP (block_sub (N := N) (k := k) hX) (mollC X N) (σ := σ)
    (lo := -2 * U - 1) (hi := 2 * U + 1) (by linarith) Rs x β hsep
    (fun r hr => by have := abs_le.1 (hx r hr); constructor <;> linarith) hβ
  have hmass := block_mass_le (X := X) (N := N) hP (block_sub (N := N) (k := k) hX) (by linarith : 0 ≤ σ)
  have hlow : (Rs.card : ℝ) * c₀ ^ 2 ≤ ∑ r ∈ Rs, ‖Fk X N k (β r) (x r)‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun r hr => pow_le_pow_left₀ hc₀.le (hbig r hr) 2
  have hL : (2 * U + 1 - (-2 * U - 1) + 8 * P * (1 + Real.log P)) ≤ 8 * (U + P) * (1 + ℓ) := by
    nlinarith
  have hL2 : 2 + Real.log (2 * P) ^ 2 ≤ 2 * (1 + ℓ) ^ 2 := by nlinarith
  have hsplit : (P : ℝ) ^ (1 - 2 * σ) * (U + P) ≤ U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ) := by
    have h1 : (P : ℝ) ^ (1 - 2 * σ) ≤ (X : ℝ) ^ (1 - 2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hX0 hXPr (by linarith)
    have h2 : (P : ℝ) ^ (1 - 2 * σ) * P = (P : ℝ) ^ (2 - 2 * σ) := by
      rw [show (2 : ℝ) - 2 * σ = (1 - 2 * σ) + 1 by ring, Real.rpow_add hP0, Real.rpow_one]
    have h3 : (P : ℝ) ^ (2 - 2 * σ) ≤ ((X : ℝ) * N) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow hP0.le hPNr (by linarith)
    have hU0 : 0 ≤ U := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hU0]
  have hmass0 : 0 ≤ ∑ j ∈ (Ioc X (X * N)).filter (fun j => blk X j = k),
      ‖mollC X N j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := sum_nonneg fun _ _ => by positivity
  have hPs : 0 ≤ (P : ℝ) ^ (1 - 2 * σ) := by positivity
  calc (Rs.card : ℝ) * c₀ ^ 2 ≤ ∑ r ∈ Rs, ‖Fk X N k (β r) (x r)‖ ^ 2 := hlow
    _ ≤ Real.exp 1 * ((2 * U + 1 - (-2 * U - 1) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2))
          * ∑ j ∈ (Ioc X (X * N)).filter (fun j => blk X j = k),
              ‖mollC X N j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := hLV
    _ ≤ Real.exp 1 * ((8 * (U + P) * (1 + ℓ)) * (2 * (1 + ℓ) ^ 2))
          * (2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * P)) ^ 3) := by
        gcongr
    _ ≤ Real.exp 1 * ((8 * (U + P) * (1 + ℓ)) * (2 * (1 + ℓ) ^ 2))
          * (2 * (P : ℝ) ^ (1 - 2 * σ) * (1 + ℓ) ^ 3) := by gcongr
    _ = 32 * Real.exp 1 * (1 + ℓ) ^ 6 * ((P : ℝ) ^ (1 - 2 * σ) * (U + P)) := by ring
    _ ≤ 32 * Real.exp 1 * (1 + ℓ) ^ 6 * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
        gcongr

/-! ## The zeros and the count -/

/-- `β = ½ + |Im τ|`: of the two zeros `½ ± iτ` of `ζ`, the one with `β ≥ ½`. -/
def βs (i : ZeroIdx (sqF Xi)) : ℝ := 1 / 2 + |(tau i).im|

/-- Its ordinate `γ = ±Re τ`. -/
def γs (i : ZeroIdx (sqF Xi)) : ℝ := if (tau i).im ≤ 0 then (tau i).re else -(tau i).re

theorem abs_γs (i : ZeroIdx (sqF Xi)) : |γs i| = |(tau i).re| := by
  unfold γs; split_ifs <;> simp [abs_neg]

theorem βs_lt_one (i : ZeroIdx (sqF Xi)) : βs i < 1 := by
  have := tau_im i; unfold βs; linarith

/-- One parity class of unit windows: 1-separated representatives, one dyadic block each. -/
theorem class_count {σ U : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hU : 2 ≤ U) {X N : ℕ} (hX : 1 ≤ X)
    (hN : 1 ≤ N) (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi))
    (hC : ∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n)
    (hwin : ∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1)
    (hdet : ∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧ σ ≤ βs (rep n)
      ∧ 1 / 2 ≤ ‖DPval X N (βs (rep n)) (γs (rep n))‖) :
    (C.card : ℝ) ≤ 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 * (32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))) := by
  classical
  set K := Nat.log 2 N + 1 with hK
  set B := 32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) with hB
  have hK0 : (0 : ℝ) < K := by positivity
  set xs : ℕ → ℝ := fun n => γs (rep n)
  set bs : ℕ → ℝ := fun n => βs (rep n)
  have hsep : ∀ n ∈ C, ∀ m ∈ C, n ≠ m → 1 ≤ |xs n - xs m| := by
    intro n hn m hm hnm
    have h1 := hwin n hn
    have h2 := hwin m hm
    have e1 : |xs n| = |(tau (rep n)).re| := abs_γs _
    have e2 : |xs m| = |(tau (rep m)).re| := abs_γs _
    refine le_trans ?_ (abs_abs_sub_abs_le_abs_sub (xs n) (xs m))
    rw [e1, e2]
    rcases hC n hn m hm hnm with h | h
    · have : ((n + 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast h
      push_cast at this
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : ((m + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast h
      push_cast at this
      rw [abs_of_nonneg (by linarith)]; linarith
  have hx : ∀ n ∈ C, |xs n| ≤ 2 * U := fun n hn => by
    simp only [xs]; rw [abs_γs]; exact (hdet n hn).1
  have hβ : ∀ n ∈ C, σ ≤ bs n ∧ bs n ≤ σ + 1 / 2 := fun n hn =>
    ⟨(hdet n hn).2.1, by have := βs_lt_one (rep n); simp only [bs]; linarith⟩
  -- a large block for each representative
  have hlarge : ∀ n ∈ C, ∃ k ∈ range K, 1 / (2 * K) ≤ ‖Fk X N k (bs n) (xs n)‖ := by
    intro n hn
    by_contra hcon
    push Not at hcon
    have h1 := (hdet n hn).2.2
    rw [DPval_eq X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fk X N k (bs n) (xs n)‖ < ∑ _k ∈ range K, 1 / (2 * (K : ℝ)) :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * (1 / (2 * K)) = 1 / 2 := by field_simp
    have := (norm_sum_le _ _).trans h2.le
    linarith [(norm_sum_le (range K) fun k => Fk X N k (bs n) (xs n)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → Finset ℕ := fun k => C.filter fun n => 1 / (2 * (K : ℝ)) ≤ ‖Fk X N k (bs n) (xs n)‖
  have hsub : C ⊆ (range K).biUnion Ck := by
    intro n hn
    obtain ⟨k, hk, hbig⟩ := hlarge n hn
    exact mem_biUnion.2 ⟨k, hk, mem_filter.2 ⟨hn, hbig⟩⟩
  have hCk : ∀ k ∈ range K, ((Ck k).card : ℝ) ≤ 4 * (K : ℝ) ^ 2 * B := by
    intro k hk
    have hc0 : (0 : ℝ) < 1 / (2 * K) := by positivity
    have h := block_count hσ hσ1 hU hX hN (mem_range.1 hk) (Ck k) xs bs
      (fun n hn m hm hnm => hsep n (mem_filter.1 hn).1 m (mem_filter.1 hm).1 hnm)
      (fun n hn => hx n (mem_filter.1 hn).1) (fun n hn => hβ n (mem_filter.1 hn).1) hc0
      (fun n hn => (mem_filter.1 hn).2)
    rw [div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity)] at h
    calc ((Ck k).card : ℝ) ≤ B * (2 * K) ^ 2 := h
      _ = 4 * (K : ℝ) ^ 2 * B := by ring
  calc (C.card : ℝ) ≤ ((range K).biUnion Ck).card := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, ((Ck k).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _k ∈ range K, 4 * (K : ℝ) ^ 2 * B := sum_le_sum hCk
    _ = 4 * (K : ℝ) ^ 3 * B := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem Kloc_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Kloc x := by
  unfold Kloc
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x + 2)
  have := kLam_nonneg
  positivity

/-- **The count**: `|Z| ≤ 800K³(1 + log 2XN)⁶ Kloc(2U + 1)(U X^{1−2σ} + (XN)^{2−2σ})`. -/
theorem card_detect_le {σ U : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hU : 2 ≤ U) {X N : ℕ} (hX : 1 ≤ X)
    (hN : 1 ≤ N) (Z : Finset (ZeroIdx (sqF Xi)))
    (hZ : ∀ i ∈ Z, |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i ∧ 1 / 2 ≤ ‖DPval X N (βs i) (γs i)‖) :
    (Z.card : ℝ) ≤ 800 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 * (1 + Real.log (2 * X * N)) ^ 6
      * Kloc (2 * U + 1) * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
  classical
  set K := Nat.log 2 N + 1 with hK
  set B := 32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
      * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) with hB
  have hB0 : 0 ≤ B := by positivity
  have hKl : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  rcases Z.eq_empty_or_nonempty with hZe | ⟨i0, hi0⟩
  · rw [hZe, card_empty, Nat.cast_zero]; positivity
  have : Nonempty (ZeroIdx (sqF Xi)) := ⟨i0⟩
  set nn : ZeroIdx (sqF Xi) → ℕ := fun i => ⌊|(tau i).re|⌋₊ with hnn
  set NI := Z.image nn with hNI
  -- `|Z| ≤ |NI|·Kloc`
  have hfib : ∀ n ∈ NI, ((Z.filter fun i => nn i = n).card : ℝ) ≤ Kloc (2 * U + 1) := by
    intro n hn
    obtain ⟨i1, hi1, rfl⟩ := mem_image.1 hn
    have hn0 : (0 : ℝ) ≤ nn i1 := Nat.cast_nonneg _
    have hnU : (nn i1 : ℝ) ≤ 2 * U + 1 :=
      (Nat.floor_le (abs_nonneg _)).trans (by linarith [(hZ i1 hi1).1])
    refine (card_local_le hn0 _ fun i hi => ?_).trans (Kloc_mono hn0 hnU)
    obtain ⟨_, hik⟩ := mem_filter.1 hi
    have h1 := Nat.floor_le (abs_nonneg (tau i).re)
    have h2 := Nat.lt_floor_add_one |(tau i).re|
    simp only [hnn] at hik
    rw [hik] at h1 h2
    rw [abs_le]; constructor <;> linarith
  have hZN : (Z.card : ℝ) ≤ NI.card * Kloc (2 * U + 1) := by
    rw [card_eq_sum_card_image nn Z]
    push_cast
    calc ∑ n ∈ NI, ((Z.filter fun i => nn i = n).card : ℝ) ≤ ∑ _n ∈ NI, Kloc (2 * U + 1) :=
          sum_le_sum hfib
      _ = NI.card * Kloc (2 * U + 1) := by rw [sum_const, nsmul_eq_mul]
  -- representatives
  have hrep : ∀ n ∈ NI, ∃ i ∈ Z, nn i = n := fun n hn => by
    obtain ⟨i, hi, h⟩ := mem_image.1 hn; exact ⟨i, hi, h⟩
  choose! rep hrepZ hrepn using hrep
  have hwin : ∀ n ∈ NI, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1 := by
    intro n hn
    have h := hrepn n hn
    have h1 := Nat.floor_le (abs_nonneg (tau (rep n)).re)
    have h2 := Nat.lt_floor_add_one |(tau (rep n)).re|
    simp only [hnn] at h
    rw [h] at h1 h2
    exact ⟨h1, h2⟩
  have hdet : ∀ n ∈ NI, |(tau (rep n)).re| ≤ 2 * U ∧ σ ≤ βs (rep n)
      ∧ 1 / 2 ≤ ‖DPval X N (βs (rep n)) (γs (rep n))‖ := fun n hn =>
    hZ _ (hrepZ n hn)
  -- the two parity classes
  have hclass : ∀ p : ℕ, ((NI.filter fun n => n % 2 = p).card : ℝ) ≤ 4 * (K : ℝ) ^ 3 * B := by
    intro p
    exact class_count hσ hσ1 hU hX hN _ rep
      (fun n hn m hm hnm => by
        have := (mem_filter.1 hn).2; have := (mem_filter.1 hm).2; omega)
      (fun n hn => hwin n (mem_filter.1 hn).1) (fun n hn => hdet n (mem_filter.1 hn).1)
  have hsplit : (NI.card : ℝ) ≤ (NI.filter fun n => n % 2 = 0).card + (NI.filter fun n => n % 2 = 1).card := by
    have h := card_filter_add_card_filter_not (s := NI) (fun n => n % 2 = 0)
    have e : NI.filter (fun n => ¬ n % 2 = 0) = NI.filter (fun n => n % 2 = 1) :=
      filter_congr fun n _ => by omega
    rw [e] at h
    exact_mod_cast h.symm.le
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  calc (Z.card : ℝ) ≤ NI.card * Kloc (2 * U + 1) := hZN
    _ ≤ (4 * (K : ℝ) ^ 3 * B + 4 * (K : ℝ) ^ 3 * B) * Kloc (2 * U + 1) := by
        gcongr; exact hsplit.trans (add_le_add (hclass 0) (hclass 1))
    _ = 256 * Real.exp 1 * (K : ℝ) ^ 3 * (1 + Real.log (2 * X * N)) ^ 6 * Kloc (2 * U + 1)
          * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by rw [hB]; ring
    _ ≤ 800 * (K : ℝ) ^ 3 * (1 + Real.log (2 * X * N)) ^ 6 * Kloc (2 * U + 1)
          * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
        have h0 : 0 ≤ (K : ℝ) ^ 3 * (1 + Real.log (2 * X * N)) ^ 6 * Kloc (2 * U + 1)
            * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ)) := by
          have : 0 ≤ 1 + Real.log (2 * X * N) := by
            have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
            have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
            have := Real.log_nonneg (by nlinarith [mul_le_mul hXr hNr zero_le_one (by linarith)] :
              (1 : ℝ) ≤ 2 * X * N)
            linarith
          positivity
        nlinarith

end ShortWeil

#print axioms ShortWeil.block_mass_le
#print axioms ShortWeil.dp_blocks
#print axioms ShortWeil.block_count
#print axioms ShortWeil.class_count
#print axioms ShortWeil.card_detect_le
