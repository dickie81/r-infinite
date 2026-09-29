/-
# Layer II, step (G2c): the per-block saving with explicit parameters (round 210)

Plain statement (`block_saving`). Write `N = u^20` with `u ≥ 2`, and take
* `M = ⌊u^8⌋` (so `M ≈ N^{2/5}`),
* `r ≥ 2`, `K = 5r + 5`, `m = 2K²` Karatsuba steps, `ℓ = K + mK = K(2K² + 1)`,
* `ℓ ≤ u⁴` (i.e. `ℓ⁵ ≤ N`) and `u^{5r+3} ≤ |t| ≤ u^{10r}`.
Then for every partial block `N ≤ N' ≤ 2N`,
  `|Σ_{N<n≤N'} n^{−it}| ≤ 2^{27}·N·u^{−1/ℓ²} = 2^{27}·N^{1 − 1/(20ℓ²)}`.

Every constant is explicit. The VMVT constant `C_m ≤ (8(K+2))^{20K⁵}` (rounds 207/209) is
absorbed because its `(2ℓ²)`-th root is at most `2^{25}` (`const_bound`), and `η_m ≤ 1/8`
(round 209) keeps the loss `M^{2η} ≤ u²` below the saving `W ≤ 2^{5r+8}/u⁴` (`wsave_le`).
-/
import ExpSum5
import VinoConst2

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder VinoRec

lemma floor_facts {u : ℝ} (hu : 2 ≤ u) :
    1 ≤ ⌊u ^ 8⌋₊ ∧ (⌊u ^ 8⌋₊ : ℝ) ≤ u ^ 8 ∧ u ^ 8 ≤ 2 * (⌊u ^ 8⌋₊ : ℝ) := by
  have h8 : (1 : ℝ) ≤ u ^ 8 := one_le_pow₀ (by linarith)
  have h1 : 1 ≤ ⌊u ^ 8⌋₊ := Nat.le_floor (by exact_mod_cast h8)
  refine ⟨h1, Nat.floor_le (by positivity), ?_⟩
  have := Nat.lt_floor_add_one (u ^ 8)
  have h1' : (1 : ℝ) ≤ ⌊u ^ 8⌋₊ := by exact_mod_cast h1
  linarith

lemma eight_K_le (K : ℕ) : 8 * ((K : ℝ) + 2) ≤ 2 ^ (K + 4) := by
  have h : ((K + 2 : ℕ) : ℝ) ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast add_two_le_two_pow K
  push_cast at h
  calc 8 * ((K : ℝ) + 2) ≤ 8 * 2 ^ (K + 1) := by linarith
    _ = 2 ^ (K + 4) := by ring

/-- **The constants are absorbed.** `C²·3^K·ℓ^{2K}·2^{5r+8} ≤ 2^{50ℓ²}`. -/
theorem const_bound {K r : ℕ} (hK : 2 ≤ K) (hrK : r ≤ K) :
    (Cvm K (2 * K ^ 2)) ^ 2 * 3 ^ K * ((K + 2 * K ^ 2 * K : ℕ) : ℝ) ^ (2 * K) *
        2 ^ (5 * r + 8) ≤ (2 : ℝ) ^ (50 * (K + 2 * K ^ 2 * K) ^ 2) := by
  set ℓ := K + 2 * K ^ 2 * K with hℓ
  have hC := Cvm_le hK (2 * K ^ 2)
  have hC0 : 0 ≤ Cvm K (2 * K ^ 2) := (zero_lt_one.trans_le (Cvm_ge_one hK _)).le
  have hg := gexp_two_sq hK
  have h1 : (Cvm K (2 * K ^ 2)) ^ 2 ≤ (2 : ℝ) ^ ((K + 4) * (20 * K ^ 5) * 2) := by
    calc _ ≤ ((8 * ((K : ℝ) + 2)) ^ gexp K (2 * K ^ 2)) ^ 2 := pow_le_pow_left₀ hC0 hC 2
      _ ≤ (((2 : ℝ) ^ (K + 4)) ^ gexp K (2 * K ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) (eight_K_le K) _) 2
      _ ≤ (((2 : ℝ) ^ (K + 4)) ^ (20 * K ^ 5)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hg) 2
      _ = _ := by rw [← pow_mul, ← pow_mul]; ring_nf
  have h2 : (3 : ℝ) ^ K ≤ 2 ^ (2 * K) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h3 : ((ℓ : ℕ) : ℝ) ^ (2 * K) ≤ 2 ^ (ℓ * (2 * K)) := by
    have hl : ((ℓ : ℕ) : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc ((ℓ : ℕ) : ℝ) ^ (2 * K) ≤ ((2 : ℝ) ^ ℓ) ^ (2 * K) := pow_le_pow_left₀ (by positivity) hl _
      _ = _ := by rw [← pow_mul]
  have hE : (K + 4) * (20 * K ^ 5) * 2 + 2 * K + ℓ * (2 * K) + (5 * r + 8) ≤ 50 * ℓ ^ 2 := by
    rw [hℓ]
    have h56 : K ^ 5 ≤ K ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h14 : K ≤ K ^ 4 := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h24 : K ^ 2 ≤ K ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1K : 1 ≤ K ^ 4 := Nat.one_le_pow _ _ (by omega)
    ring_nf
    nlinarith
  calc (Cvm K (2 * K ^ 2)) ^ 2 * 3 ^ K * ((ℓ : ℕ) : ℝ) ^ (2 * K) * 2 ^ (5 * r + 8)
      ≤ (2 : ℝ) ^ ((K + 4) * (20 * K ^ 5) * 2) * 2 ^ (2 * K) * 2 ^ (ℓ * (2 * K)) *
          2 ^ (5 * r + 8) := by gcongr
    _ = (2 : ℝ) ^ ((K + 4) * (20 * K ^ 5) * 2 + 2 * K + ℓ * (2 * K) + (5 * r + 8)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hE

/-- **The saving factor with these parameters.** `W ≤ 2^{5r+8}/u⁴`. -/
theorem wsave_le {t u : ℝ} {N M ℓ r : ℕ} (hu : 2 ≤ u) (hr : 2 ≤ r) (hℓ1 : 1 ≤ ℓ)
    (hN : (N : ℝ) = u ^ 20) (hMle : (M : ℝ) ≤ u ^ 8) (hMge : u ^ 8 ≤ 2 * M)
    (hℓu : (ℓ : ℝ) ≤ u ^ 4) (ht1 : u ^ (5 * r + 3) ≤ |t|) :
    0 ≤ Wsave t N M ℓ r ∧ Wsave t N M ℓ r ≤ 2 ^ (5 * r + 8) / u ^ 4 := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have h256 : (256 : ℝ) ≤ u ^ 8 := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu 8
  have hM0 : (0 : ℝ) < M := by linarith
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hMr : u ^ (8 * r) ≤ 2 ^ r * (M : ℝ) ^ r := by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hMge r
  have hM2r : u ^ (16 * r) ≤ 4 ^ r * (M : ℝ) ^ (2 * r) := by
    have := pow_le_pow_left₀ (by positivity) hMr 2
    calc u ^ (16 * r) = (u ^ (8 * r)) ^ 2 := by rw [← pow_mul]; ring_nf
      _ ≤ (2 ^ r * (M : ℝ) ^ r) ^ 2 := this
      _ = 4 ^ r * (M : ℝ) ^ (2 * r) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
          ring_nf
  have hy1 : (1 : ℝ) ≤ ℓ * (M : ℝ) ^ r := by
    have : (1 : ℝ) ≤ (M : ℝ) ^ r := one_le_pow₀ (by linarith)
    nlinarith
  have hy : (ℓ : ℝ) * (M : ℝ) ^ r ≤ u ^ (8 * r + 4) := by
    calc (ℓ : ℝ) * (M : ℝ) ^ r ≤ u ^ 4 * (u ^ 8) ^ r :=
          mul_le_mul hℓu (pow_le_pow_left₀ hM0.le hMle r) (by positivity) (by positivity)
      _ = u ^ (8 * r + 4) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hlog : 1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r) ≤ (8 * r + 5) * u := by
    have h1 := Real.log_le_log (by linarith) hy
    rw [Real.log_pow] at h1
    have h2 := Real.log_le_sub_one_of_pos hu0
    have hr0 : (0 : ℝ) ≤ ((8 * r + 4 : ℕ) : ℝ) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hr0
    push_cast at h1 h3
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r) := by
    have := Real.log_nonneg hy1; linarith
  have htpos : 0 < |t| := lt_of_lt_of_le (by positivity) ht1
  -- the first term
  have hT1 : 1 / ((ℓ : ℝ) * (M : ℝ) ^ r) ≤ 2 ^ r / u ^ 4 := by
    rw [div_le_div_iff₀ (by linarith) (by positivity), one_mul]
    have h4 : u ^ 4 ≤ u ^ (8 * r) := pow_le_pow_right₀ hu1 (by omega)
    have : (M : ℝ) ^ r ≤ ℓ * (M : ℝ) ^ r := le_mul_of_one_le_left (by positivity) hℓr
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) r]
  -- the second term
  set A : ℝ := 2 * Real.pi * r * (8 * r + 5) * 2 ^ r with hA
  have hA0 : 0 ≤ A := by positivity
  have hT2 : 2 * Real.pi * r * (2 * (N : ℝ)) ^ r * (1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r)) /
      (|t| * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * r)) ≤ 2 * Real.pi * r * (8 * r + 5) * 8 ^ r / u ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (2 * (N : ℝ)) ^ r = 2 ^ r * u ^ (20 * r) := by rw [hN, mul_pow, ← pow_mul]
    rw [e1]
    have hℓ2 : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := one_le_pow₀ hℓr
    calc 2 * Real.pi * r * (2 ^ r * u ^ (20 * r)) * (1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r)) * u ^ 4
        ≤ 2 * Real.pi * r * (2 ^ r * u ^ (20 * r)) * ((8 * r + 5) * u) * u ^ 4 := by gcongr
      _ = A * u ^ (20 * r + 5) := by rw [hA]; ring
      _ ≤ A * u ^ (21 * r + 3) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu1 (by omega)) hA0
      _ = A * (u ^ (5 * r + 3) * u ^ (16 * r)) := by rw [← pow_add]; ring_nf
      _ ≤ A * (|t| * (4 ^ r * (M : ℝ) ^ (2 * r))) := by gcongr
      _ = 2 * Real.pi * r * (8 * r + 5) * 8 ^ r * (|t| * 1 * (M : ℝ) ^ (2 * r)) := by
          rw [hA, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]; ring
      _ ≤ 2 * Real.pi * r * (8 * r + 5) * 8 ^ r * (|t| * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * r)) := by
          gcongr
  -- the constant
  have hconst : 2 ^ r + 2 * Real.pi * r * (8 * r + 5) * 8 ^ r ≤ (2 : ℝ) ^ (5 * r + 8) := by
    have hrr : ((r : ℕ) : ℝ) ^ 2 ≤ 4 ^ r := by
      have : r < 2 ^ r := Nat.lt_two_pow_self
      have h' : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast this.le
      calc ((r : ℕ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ r) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
        _ = 4 ^ r := by rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hπ := Real.pi_lt_d2
    have h13 : (r : ℝ) * (8 * r + 5) ≤ 13 * 4 ^ r := by nlinarith
    have h32 : (4 : ℝ) ^ r * 8 ^ r = 32 ^ r := by rw [← mul_pow]; norm_num
    have e : (2 : ℝ) ^ (5 * r + 8) = 256 * 32 ^ r := by
      rw [pow_add, pow_mul]; norm_num; ring
    have h2r : (2 : ℝ) ^ r ≤ 32 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
    have h8 : (0 : ℝ) ≤ 8 ^ r := by positivity
    have hin : 2 * Real.pi * (r * (8 * r + 5)) ≤ 2 * 3.15 * (13 * 4 ^ r) := by
      have : (0 : ℝ) ≤ r * (8 * r + 5) := by positivity
      nlinarith [Real.pi_pos]
    have hmain : 2 * Real.pi * r * (8 * r + 5) * 8 ^ r ≤ 2 * 3.15 * (13 * 4 ^ r) * 8 ^ r := by
      calc 2 * Real.pi * r * (8 * r + 5) * 8 ^ r = (2 * Real.pi * (r * (8 * r + 5))) * 8 ^ r := by
            ring
        _ ≤ 2 * 3.15 * (13 * 4 ^ r) * 8 ^ r := mul_le_mul_of_nonneg_right hin h8
    have hA : 2 * 3.15 * (13 * 4 ^ r) * 8 ^ r = (81.9 : ℝ) * 32 ^ r := by rw [← h32]; ring
    have h32p : (0 : ℝ) ≤ 32 ^ r := by positivity
    rw [e]; linarith
  refine ⟨?_, ?_⟩
  · unfold Wsave
    exact add_nonneg (by positivity) (div_nonneg (mul_nonneg (by positivity) hlog0) (by positivity))
  · unfold Wsave
    calc _ ≤ 2 ^ r / u ^ 4 + 2 * Real.pi * r * (8 * r + 5) * 8 ^ r / u ^ 4 := add_le_add hT1 hT2
      _ = (2 ^ r + 2 * Real.pi * r * (8 * r + 5) * 8 ^ r) / u ^ 4 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)

/-- **The per-`n` saving.** `Φ ≤ 2^{25}/u^{1/ℓ²}`. -/
theorem phi_le {t u : ℝ} {N M K ℓ r : ℕ} {C η : ℝ} (hu : 2 ≤ u) (hℓ1 : 1 ≤ ℓ)
    (hη : η ≤ 1 / 8) (hM1 : 1 ≤ M) (hMle : (M : ℝ) ≤ u ^ 8)
    (hW0 : 0 ≤ Wsave t N M ℓ r) (hW : Wsave t N M ℓ r ≤ 2 ^ (5 * r + 8) / u ^ 4)
    (hQ : C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * 2 ^ (5 * r + 8) ≤ (2 : ℝ) ^ (50 * ℓ ^ 2)) :
    Phi t C η N M K ℓ r ≤ 2 ^ 25 / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMη : (M : ℝ) ^ (2 * η) ≤ u ^ 2 := by
    calc (M : ℝ) ^ (2 * η) ≤ (M : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le hMr (by linarith)
      _ ≤ (u ^ 8) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hMle (by norm_num)
      _ = u ^ 2 := by
          rw [← Real.rpow_natCast u 8, ← Real.rpow_mul hu0.le]; norm_num
  set P : ℝ := C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) with hP
  have hP0 : 0 ≤ P := by positivity
  have hbase : P * (M : ℝ) ^ (2 * η) * Wsave t N M ℓ r ≤ (2 : ℝ) ^ (50 * ℓ ^ 2) / u ^ 2 := by
    calc P * (M : ℝ) ^ (2 * η) * Wsave t N M ℓ r
        = P * ((M : ℝ) ^ (2 * η) * Wsave t N M ℓ r) := by ring
      _ ≤ P * (u ^ 2 * (2 ^ (5 * r + 8) / u ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hMη hW hW0 (by positivity)) hP0
      _ = P * 2 ^ (5 * r + 8) / u ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hQ (by positivity)
  have hb0 : 0 ≤ P * (M : ℝ) ^ (2 * η) * Wsave t N M ℓ r :=
    mul_nonneg (by positivity) hW0
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  unfold Phi
  rw [← hP]
  set e : ℝ := (((2 * ℓ ^ 2 : ℕ) : ℝ))⁻¹ with he
  calc (P * (M : ℝ) ^ (2 * η) * Wsave t N M ℓ r) ^ e
      ≤ ((2 : ℝ) ^ (50 * ℓ ^ 2) / u ^ 2) ^ e :=
        Real.rpow_le_rpow hb0 hbase (by positivity)
    _ = 2 ^ 25 / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by
        rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast (2 : ℝ),
          ← Real.rpow_natCast u 2, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hu0.le]
        have e1 : ((50 * ℓ ^ 2 : ℕ) : ℝ) * e = 25 := by
          rw [he]; push_cast; field_simp; ring
        have e2 : ((2 : ℕ) : ℝ) * e = 1 / (ℓ : ℝ) ^ 2 := by
          rw [he]; push_cast; field_simp
        rw [e1, e2]; norm_num

/-- **Step (G2c), the per-block saving.** -/
theorem block_saving {t u : ℝ} {N N' K ℓ r : ℕ} (hr : 2 ≤ r) (hK : K = 5 * r + 5)
    (hℓ : ℓ = K + 2 * K ^ 2 * K) (hu : 2 ≤ u) (hN : (N : ℝ) = u ^ 20)
    (hN1 : N ≤ N') (hN2 : N' ≤ 2 * N) (hℓu : (ℓ : ℝ) ≤ u ^ 4)
    (ht1 : u ^ (5 * r + 3) ≤ |t|) (ht2 : |t| ≤ u ^ (10 * r)) :
    ‖∑ n ∈ Ioc N N', phaseF t n‖ ≤ 2 ^ 27 * N / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have htpos : 0 < |t| := lt_of_lt_of_le (by positivity) ht1
  have ht : t ≠ 0 := abs_pos.mp htpos
  have hK2 : 2 ≤ K := by omega
  have hrK : r ≤ K := by omega
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; omega
  obtain ⟨hM1, hMle, hMge⟩ := floor_facts hu
  set M := ⌊u ^ 8⌋₊ with hMdef
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hu4 : (16 : ℝ) ≤ u ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have hM2 : (M : ℝ) ^ 2 ≤ u ^ 16 := by
    calc (M : ℝ) ^ 2 ≤ (u ^ 8) ^ 2 := pow_le_pow_left₀ hM0 hMle 2
      _ = u ^ 16 := by rw [← pow_mul]
  have hMN : 2 * M ^ 2 ≤ N := by
    have : (2 * M ^ 2 : ℝ) ≤ N := by
      rw [hN]
      calc (2 * (M : ℝ) ^ 2) ≤ 2 * u ^ 16 := by linarith
        _ ≤ u ^ 4 * u ^ 16 := by nlinarith [pow_pos hu0 16]
        _ = u ^ 20 := by rw [← pow_add]
    exact_mod_cast this
  -- VMVT at `m = 2K²`
  obtain ⟨hC, hJall⟩ := vmvt_explicit hK2 (2 * K ^ 2)
  have hJ := hJall M hM1
  have hℓeq : K + 2 * K ^ 2 * K = ℓ := hℓ.symm
  rw [hℓeq] at hJ
  have hJ' : (J ℓ K M : ℝ) ≤ Cvm K (2 * K ^ 2) *
      (M : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + eta K (2 * K ^ 2)) := by
    convert hJ using 3
    simp only [expo, hℓeq]
  -- the good coordinate
  have hgood : |t| * ℓ * (M : ℝ) ^ r ≤ Real.pi * r * (N : ℝ) ^ r := by
    have hMr : (M : ℝ) ^ r ≤ u ^ (8 * r) := by
      rw [pow_mul]; exact pow_le_pow_left₀ hM0 hMle r
    have h1 : |t| * ℓ * (M : ℝ) ^ r ≤ u ^ (10 * r) * u ^ 4 * u ^ (8 * r) := by gcongr
    have h2 : u ^ (10 * r) * u ^ 4 * u ^ (8 * r) ≤ (N : ℝ) ^ r := by
      rw [hN, ← pow_mul, ← pow_add, ← pow_add]
      exact pow_le_pow_right₀ hu1 (by omega)
    have h3 : (N : ℝ) ^ r ≤ Real.pi * r * (N : ℝ) ^ r := by
      have : (1 : ℝ) ≤ Real.pi * r := by
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr
        nlinarith [Real.pi_gt_three]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ N by positivity) r]
    linarith
  have hbb := block_bound_partial ht hC hM1 hℓ1 (by omega : 1 ≤ r) hrK hMN hN1 hN2 hJ' hgood
  -- the three terms
  obtain ⟨hW0, hW⟩ := wsave_le (t := t) (N := N) hu hr hℓ1 hN hMle hMge hℓu ht1
  have hQ := const_bound hK2 hrK
  rw [hℓeq] at hQ
  have hPhi := phi_le (t := t) (N := N) (K := K) hu hℓ1 (eta_two_sq (k := K) (by omega)) hM1 hMle
    hW0 hW hQ
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hTay : 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) ≤ 2 := by
    have hq : (M : ℝ) ^ 2 / N ≤ 1 / u ^ 4 := by
      rw [div_le_div_iff₀ hNpos (by positivity), hN]
      calc (M : ℝ) ^ 2 * u ^ 4 ≤ u ^ 16 * u ^ 4 := by gcongr
        _ = 1 * u ^ 20 := by rw [← pow_add]; ring
    have hq' : ((M : ℝ) ^ 2 / N) ^ (K + 1) ≤ (1 / u ^ 4) ^ (K + 1) :=
      pow_le_pow_left₀ (by positivity) hq _
    have hkey : |t| * N * (1 / u ^ 4) ^ (K + 1) ≤ 1 := by
      rw [hN, one_div_pow, ← pow_mul, mul_one_div, div_le_one (by positivity)]
      calc |t| * u ^ 20 ≤ u ^ (10 * r) * u ^ 20 := by gcongr
        _ = u ^ (10 * r + 20) := by rw [← pow_add]
        _ ≤ u ^ (4 * (K + 1)) := pow_le_pow_right₀ hu1 (by omega)
    have : |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) ≤ |t| * N * (1 / u ^ 4) ^ (K + 1) :=
      mul_le_mul_of_nonneg_left hq' (by positivity)
    linarith
  -- assemble
  have hr1 : u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) ≤ u := by
    have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    have : (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ hℓr
    calc u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 this
      _ = u := Real.rpow_one u
  have hrpos : 0 < u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := Real.rpow_pos_of_pos hu0 _
  have hsmall : 2 + 2 * u ^ 16 ≤ (2 ^ 27 - 2 ^ 25) * N / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by
    rw [le_div_iff₀ hrpos, hN]
    have h1 : 1 ≤ u ^ 16 := one_le_pow₀ hu1
    have h2 : (2 + 2 * u ^ 16) * u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) ≤ 4 * u ^ 16 * u := by
      have : 2 + 2 * u ^ 16 ≤ 4 * u ^ 16 := by linarith
      exact mul_le_mul this hr1 hrpos.le (by positivity)
    have h3 : 4 * u ^ 16 * u ≤ (2 ^ 27 - 2 ^ 25) * u ^ 20 := by
      have : u ^ 16 * u ≤ u ^ 20 := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hu1 (by norm_num)
      nlinarith [pow_pos hu0 20]
    linarith
  calc ‖∑ n ∈ Ioc N N', phaseF t n‖
      ≤ N * Phi t (Cvm K (2 * K ^ 2)) (eta K (2 * K ^ 2)) N M K ℓ r +
          2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) + 2 * (M : ℝ) ^ 2 := hbb
    _ ≤ N * (2 ^ 25 / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2)) + 2 + 2 * u ^ 16 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hPhi hNpos.le) hTay) (by linarith)
    _ ≤ N * (2 ^ 25 / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2)) +
          (2 ^ 27 - 2 ^ 25) * N / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by linarith
    _ = 2 ^ 27 * N / u ^ ((1 : ℝ) / (ℓ : ℝ) ^ 2) := by ring

end ExpSum
