/-
# Sharpening, step S1b: explicit parameters for many good coordinates (round 213)

Plain statement (`block_saving_multi`). Write `N = u^20` (`u ≥ 2`), `M = ⌊u⁸⌋` and
`u^R ≤ |t| ≤ u^{R+1}`, with `R + 21 ≤ 4K` and `K ≤ ℓ ≤ u⁴`. Let `G` be any set of coordinates
`j` with `R + 5 ≤ 12j` and `24j + 6 ≤ 5R`, and suppose VMVT holds at `(ℓ, K)` with
`η ≤ 1/32` and `C²·3^K·ℓ^{2K}·2^{K(5K+8)} ≤ 2^{2Q₀ℓ²}`. Then for every partial block
  `|Σ_{N<n≤N'} n^{−it}| ≤ 2^{Q₀+2}·N·u^{−s}`,   `s = (#G·R/6 − 1/2)/(2ℓ²)`.

Each `j ∈ G` saves `u^{−(R−4j−1)} ≤ u^{−R/6}` (`wsave_le_j`). `window` supplies a `G` with
`R² ≤ 50·#G·R − 150`, so `s ≥ R²/(600ℓ²)`: the saving now grows like `K²/ℓ²`, not `1/ℓ²`.
-/
import ExpSum8

open Finset Complex

namespace VinoRec

/-- `η_{2K²} ≤ 1/32` for `K ≥ 10`. -/
theorem eta_two_sq32 {k : ℕ} (hk : 10 ≤ k) : eta k (2 * k ^ 2) ≤ 1 / 32 := by
  have hk2 : 2 ≤ k := by omega
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hsplit : 2 * k ^ 2 = k * k + k * k := by ring
  rw [hsplit]
  have hg := eta_geo hk2 (k * k)
  have hle := eta_le hk2 (k * k)
  have hr0 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hexp : (1 - 1 / (k : ℝ)) ^ (k * k) ≤ Real.exp (-(k : ℝ)) := by
    have h1 : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / (k : ℝ))) := by
      have := Real.add_one_le_exp (-(1 / (k : ℝ))); linarith
    calc (1 - 1 / (k : ℝ)) ^ (k * k) ≤ (Real.exp (-(1 / (k : ℝ)))) ^ (k * k) :=
          pow_le_pow_left₀ hr0 h1 _
      _ = Real.exp (-(k : ℝ)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have hek : 16 * (k : ℝ) * ((k : ℝ) + 1) ≤ Real.exp k := by
    have h3 : 1 + (k : ℝ) + (k : ℝ) ^ 2 / 2 + (k : ℝ) ^ 3 / 6 + (k : ℝ) ^ 4 / 24
        + (k : ℝ) ^ 5 / 120 + (k : ℝ) ^ 6 / 720 ≤ Real.exp k := by
      have := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ k) 7
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
      norm_num [Nat.factorial] at this
      linarith
    have hk7 : 0 ≤ (k : ℝ) - 10 := by linarith
    nlinarith [mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 5),
      mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 4),
      mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 3),
      mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2),
      mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  have hekinv : Real.exp (-(k : ℝ)) * (16 * (k : ℝ) * ((k : ℝ) + 1)) ≤ 1 := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]; linarith
  have hη0 := eta_nonneg hk2 (k * k)
  calc eta k (k * k + k * k) ≤ (1 - 1 / (k : ℝ)) ^ (k * k) * eta k (k * k) := hg
    _ ≤ Real.exp (-(k : ℝ)) * ((k : ℝ) * ((k : ℝ) + 1) / 2) :=
        mul_le_mul hexp hle hη0 (Real.exp_pos _).le
    _ = (Real.exp (-(k : ℝ)) * (16 * (k : ℝ) * ((k : ℝ) + 1))) / 32 := by ring
    _ ≤ 1 / 32 := by linarith

end VinoRec

namespace ExpSum

open Vinogradov VinoHolder VinoRec

/-- The weak-VMVT constant absorbs the many-coordinate constants. -/
theorem const_bound2 {K : ℕ} (hK : 2 ≤ K) :
    (Cvm K (2 * K ^ 2)) ^ 2 * 3 ^ K * ((K + 2 * K ^ 2 * K : ℕ) : ℝ) ^ (2 * K) *
        2 ^ (K * (5 * K + 8)) ≤ (2 : ℝ) ^ (2 * 25 * (K + 2 * K ^ 2 * K) ^ 2) := by
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
  have hE : (K + 4) * (20 * K ^ 5) * 2 + 2 * K + ℓ * (2 * K) + K * (5 * K + 8) ≤
      2 * 25 * ℓ ^ 2 := by
    rw [hℓ]
    have h56 : K ^ 5 ≤ K ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h14 : K ≤ K ^ 4 := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h24 : K ^ 2 ≤ K ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1K : 1 ≤ K ^ 4 := Nat.one_le_pow _ _ (by omega)
    ring_nf
    nlinarith
  calc (Cvm K (2 * K ^ 2)) ^ 2 * 3 ^ K * ((ℓ : ℕ) : ℝ) ^ (2 * K) * 2 ^ (K * (5 * K + 8))
      ≤ (2 : ℝ) ^ ((K + 4) * (20 * K ^ 5) * 2) * 2 ^ (2 * K) * 2 ^ (ℓ * (2 * K)) *
          2 ^ (K * (5 * K + 8)) := by gcongr
    _ = (2 : ℝ) ^ ((K + 4) * (20 * K ^ 5) * 2 + 2 * K + ℓ * (2 * K) + K * (5 * K + 8)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hE

/-- **The saving factor of one coordinate in the window.** -/
theorem wsave_le_j {t u : ℝ} {N M ℓ R jj : ℕ} (hu : 2 ≤ u) (hjj : 1 ≤ jj) (hℓ1 : 1 ≤ ℓ)
    (hN : (N : ℝ) = u ^ 20) (hMle : (M : ℝ) ≤ u ^ 8) (hMge : u ^ 8 ≤ 2 * M)
    (hℓu : (ℓ : ℝ) ≤ u ^ 4) (ht1 : u ^ R ≤ |t|) (hw1 : R + 5 ≤ 12 * jj)
    (hw2 : 24 * jj + 6 ≤ 5 * R) :
    Wsave t N M ℓ jj ≤ 2 ^ (5 * jj + 8) / u ^ (R - 4 * jj - 1) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have h256 : (256 : ℝ) ≤ u ^ 8 := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu 8
  have hM0 : (0 : ℝ) < M := by linarith
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  set e := R - 4 * jj - 1 with he
  have he8 : e ≤ 8 * jj := by omega
  have heR : e + 4 * jj + 1 = R := by omega
  have hMr : u ^ (8 * jj) ≤ 2 ^ jj * (M : ℝ) ^ jj := by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hMge jj
  have hM2r : u ^ (16 * jj) ≤ 4 ^ jj * (M : ℝ) ^ (2 * jj) := by
    have := pow_le_pow_left₀ (by positivity) hMr 2
    calc u ^ (16 * jj) = (u ^ (8 * jj)) ^ 2 := by rw [← pow_mul]; ring_nf
      _ ≤ (2 ^ jj * (M : ℝ) ^ jj) ^ 2 := this
      _ = 4 ^ jj * (M : ℝ) ^ (2 * jj) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
          ring_nf
  have hy1 : (1 : ℝ) ≤ ℓ * (M : ℝ) ^ jj := by
    have : (1 : ℝ) ≤ (M : ℝ) ^ jj := one_le_pow₀ (by linarith)
    nlinarith
  have hy : (ℓ : ℝ) * (M : ℝ) ^ jj ≤ u ^ (8 * jj + 4) := by
    calc (ℓ : ℝ) * (M : ℝ) ^ jj ≤ u ^ 4 * (u ^ 8) ^ jj :=
          mul_le_mul hℓu (pow_le_pow_left₀ hM0.le hMle jj) (by positivity) (by positivity)
      _ = u ^ (8 * jj + 4) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hlog : 1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ jj) ≤ (8 * jj + 5) * u := by
    have h1 := Real.log_le_log (by linarith) hy
    rw [Real.log_pow] at h1
    have h2 := Real.log_le_sub_one_of_pos hu0
    have hr0 : (0 : ℝ) ≤ ((8 * jj + 4 : ℕ) : ℝ) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hr0
    push_cast at h1 h3
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ jj) := by
    have := Real.log_nonneg hy1; linarith
  have htpos : 0 < |t| := lt_of_lt_of_le (by positivity) ht1
  have hue : u ^ e ≤ u ^ (8 * jj) := pow_le_pow_right₀ hu1 he8
  -- the first term
  have hT1 : 1 / ((ℓ : ℝ) * (M : ℝ) ^ jj) ≤ 2 ^ jj / u ^ e := by
    rw [div_le_div_iff₀ (by linarith) (by positivity), one_mul]
    have : (M : ℝ) ^ jj ≤ ℓ * (M : ℝ) ^ jj := le_mul_of_one_le_left (by positivity) hℓr
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) jj]
  -- the second term
  set A : ℝ := 2 * Real.pi * jj * (8 * jj + 5) * 2 ^ jj with hA
  have hA0 : 0 ≤ A := by positivity
  have hT2 : 2 * Real.pi * jj * (2 * (N : ℝ)) ^ jj * (1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ jj)) /
      (|t| * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * jj)) ≤
        2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj / u ^ e := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (2 * (N : ℝ)) ^ jj = 2 ^ jj * u ^ (20 * jj) := by rw [hN, mul_pow, ← pow_mul]
    rw [e1]
    have hℓ2 : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := one_le_pow₀ hℓr
    calc 2 * Real.pi * jj * (2 ^ jj * u ^ (20 * jj)) * (1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ jj)) *
          u ^ e
        ≤ 2 * Real.pi * jj * (2 ^ jj * u ^ (20 * jj)) * ((8 * jj + 5) * u) * u ^ e := by gcongr
      _ = A * u ^ (R + 16 * jj) := by
          rw [hA, ← heR]; ring
      _ = A * (u ^ R * u ^ (16 * jj)) := by rw [← pow_add]
      _ ≤ A * (|t| * (4 ^ jj * (M : ℝ) ^ (2 * jj))) := by gcongr
      _ = 2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj * (|t| * 1 * (M : ℝ) ^ (2 * jj)) := by
          rw [hA, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]; ring
      _ ≤ 2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj * (|t| * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * jj)) := by
          gcongr
  -- the constant
  have hconst : 2 ^ jj + 2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj ≤ (2 : ℝ) ^ (5 * jj + 8) := by
    have hrr : ((jj : ℕ) : ℝ) ^ 2 ≤ 4 ^ jj := by
      have : jj < 2 ^ jj := Nat.lt_two_pow_self
      have h' : (jj : ℝ) ≤ 2 ^ jj := by exact_mod_cast this.le
      calc ((jj : ℕ) : ℝ) ^ 2 ≤ ((2 : ℝ) ^ jj) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
        _ = 4 ^ jj := by rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    have hr1 : (1 : ℝ) ≤ jj := by exact_mod_cast hjj
    have h13 : (jj : ℝ) * (8 * jj + 5) ≤ 13 * 4 ^ jj := by nlinarith
    have h32 : (4 : ℝ) ^ jj * 8 ^ jj = 32 ^ jj := by rw [← mul_pow]; norm_num
    have e : (2 : ℝ) ^ (5 * jj + 8) = 256 * 32 ^ jj := by
      rw [pow_add, pow_mul]; norm_num; ring
    have h2r : (2 : ℝ) ^ jj ≤ 32 ^ jj := pow_le_pow_left₀ (by norm_num) (by norm_num) jj
    have h8 : (0 : ℝ) ≤ 8 ^ jj := by positivity
    have hin : 2 * Real.pi * (jj * (8 * jj + 5)) ≤ 2 * 3.15 * (13 * 4 ^ jj) := by
      have : (0 : ℝ) ≤ jj * (8 * jj + 5) := by positivity
      nlinarith [Real.pi_pos, Real.pi_lt_d2]
    have hmain : 2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj ≤ 2 * 3.15 * (13 * 4 ^ jj) * 8 ^ jj := by
      calc 2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj = (2 * Real.pi * (jj * (8 * jj + 5))) * 8 ^ jj := by
            ring
        _ ≤ 2 * 3.15 * (13 * 4 ^ jj) * 8 ^ jj := mul_le_mul_of_nonneg_right hin h8
    have hA' : 2 * 3.15 * (13 * 4 ^ jj) * 8 ^ jj = (81.9 : ℝ) * 32 ^ jj := by rw [← h32]; ring
    have h32p : (0 : ℝ) ≤ 32 ^ jj := by positivity
    rw [e]; linarith
  unfold Wsave
  calc _ ≤ 2 ^ jj / u ^ e + 2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj / u ^ e := add_le_add hT1 hT2
    _ = (2 ^ jj + 2 * Real.pi * jj * (8 * jj + 5) * 8 ^ jj) / u ^ e := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)

/-- **A window of good coordinates.** -/
theorem window {R K : ℕ} (hR : 16 ≤ R) (hKR : R + 21 ≤ 4 * K) :
    ∃ G : Finset (Fin K), (∀ j ∈ G, R + 5 ≤ 12 * (j.val + 1) ∧ 24 * (j.val + 1) + 6 ≤ 5 * R) ∧
      1 ≤ G.card ∧ (R : ℝ) ^ 2 ≤ 50 * G.card * R - 150 := by
  set j1 := (R + 16) / 12 with hj1
  set j3 := (5 * R - 6) / 24 with hj3
  set G : Finset (Fin K) := univ.filter (fun j => j1 ≤ j.val + 1 ∧ j.val + 1 ≤ j3) with hG
  have hj1pos : 1 ≤ j1 := by omega
  have hj3K : j3 ≤ K := by omega
  have himg : G.image (fun j => j.val + 1) = Icc j1 j3 := by
    ext n
    simp only [hG, mem_image, mem_filter, mem_univ, true_and, mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · rintro ⟨h1, h2⟩
      exact ⟨⟨n - 1, by omega⟩, by simp only; omega, by simp only; omega⟩
  have hcard : G.card = j3 + 1 - j1 := by
    rw [← Nat.card_Icc, ← himg, card_image_of_injective]
    intro a b h; exact Fin.ext (by simpa using h)
  refine ⟨G, ?_, ?_, ?_⟩
  · intro j hj
    simp only [hG, mem_filter, mem_univ, true_and] at hj
    omega
  · rw [hcard]; omega
  · rw [hcard]
    have hRr : (16 : ℝ) ≤ R := by exact_mod_cast hR
    rcases le_or_gt R 20 with h20 | h21
    · have hc : 1 ≤ j3 + 1 - j1 := by omega
      have hcr : (1 : ℝ) ≤ ((j3 + 1 - j1 : ℕ) : ℝ) := by exact_mod_cast hc
      have hR20 : (R : ℝ) ≤ 20 := by exact_mod_cast h20
      nlinarith
    · have hc : 3 * R ≤ 24 * (j3 + 1 - j1) + 37 := by omega
      have hcr : 3 * (R : ℝ) ≤ 24 * ((j3 + 1 - j1 : ℕ) : ℝ) + 37 := by exact_mod_cast hc
      have hR21 : (21 : ℝ) ≤ R := by exact_mod_cast h21
      nlinarith

set_option maxHeartbeats 1600000 in
/-- **Step S1b, the per-block saving with a window of good coordinates.** -/
theorem block_saving_multi {t u C η : ℝ} {N N' K ℓ R Q0 : ℕ} (G : Finset (Fin K))
    (hu : 2 ≤ u) (hN : (N : ℝ) = u ^ 20) (hN1 : N ≤ N') (hN2 : N' ≤ 2 * N)
    (hK1 : 1 ≤ K) (hKℓ : K ≤ ℓ) (hℓu : (ℓ : ℝ) ≤ u ^ 4)
    (ht1 : u ^ R ≤ |t|) (ht2 : |t| ≤ u ^ (R + 1)) (hKR : R + 21 ≤ 4 * K)
    (hG : ∀ j ∈ G, R + 5 ≤ 12 * (j.val + 1) ∧ 24 * (j.val + 1) + 6 ≤ 5 * R)
    (hC : 0 < C) (hη : η ≤ 1 / 32)
    (hJ : ∀ P : ℕ, 1 ≤ P →
      (J ℓ K P : ℝ) ≤ C * (P : ℝ) ^ (2 * (ℓ : ℝ) - (K : ℝ) * ((K : ℝ) + 1) / 2 + η))
    (hQ : C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) * 2 ^ (K * (5 * K + 8)) ≤
      (2 : ℝ) ^ (2 * Q0 * ℓ ^ 2)) :
    ‖∑ n ∈ Ioc N N', phaseF t n‖ ≤
      2 ^ (Q0 + 2) * N / u ^ (((G.card : ℝ) * R / 6 - 1 / 2) / (2 * (ℓ : ℝ) ^ 2)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have htpos : 0 < |t| := lt_of_lt_of_le (by positivity) ht1
  have ht : t ≠ 0 := abs_pos.mp htpos
  have hℓ1 : 1 ≤ ℓ := le_trans hK1 hKℓ
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  obtain ⟨hM1, hMle, hMge⟩ := floor_facts hu
  set M := ⌊u ^ 8⌋₊ with hMdef
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
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
  -- good coordinates
  have hgood : ∀ j ∈ G, |t| * ℓ * (M : ℝ) ^ (j.val + 1) ≤
      Real.pi * (j.val + 1 : ℕ) * (N : ℝ) ^ (j.val + 1) := by
    intro j hj
    obtain ⟨hw1, _⟩ := hG j hj
    set jj := j.val + 1
    have hMj : (M : ℝ) ^ jj ≤ u ^ (8 * jj) := by
      rw [pow_mul]; exact pow_le_pow_left₀ hM0 hMle jj
    have h1 : |t| * ℓ * (M : ℝ) ^ jj ≤ u ^ (R + 1) * u ^ 4 * u ^ (8 * jj) := by gcongr
    have h2 : u ^ (R + 1) * u ^ 4 * u ^ (8 * jj) ≤ (N : ℝ) ^ jj := by
      rw [hN, ← pow_mul, ← pow_add, ← pow_add]
      exact pow_le_pow_right₀ hu1 (by omega)
    have h3 : (N : ℝ) ^ jj ≤ Real.pi * (jj : ℕ) * (N : ℝ) ^ jj := by
      have : (1 : ℝ) ≤ Real.pi * (jj : ℕ) := by
        have : (1 : ℝ) ≤ (jj : ℕ) := by exact_mod_cast (show 1 ≤ jj by omega)
        nlinarith [Real.pi_gt_three]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ N by positivity) jj]
    linarith
  have hbb := block_bound_multi ht hC hM1 hℓ1 G hMN hN1 hN2 (hJ M hM1) hgood
  -- the saving product
  have hGK : G.card ≤ K := by
    calc G.card ≤ (univ : Finset (Fin K)).card := card_le_univ G
      _ = K := by simp
  set s0 : ℝ := (R : ℝ) / 6 with hs0
  have hWG : WG t N M K ℓ G ≤ 2 ^ (K * (5 * K + 8)) / u ^ ((G.card : ℝ) * s0) := by
    have hper : ∀ j ∈ G, Wsave t N M ℓ (j.val + 1) ≤ 2 ^ (5 * K + 8) / u ^ s0 := by
      intro j hj
      obtain ⟨hw1, hw2⟩ := hG j hj
      refine (wsave_le_j hu (by omega) hℓ1 hN hMle hMge hℓu ht1 hw1 hw2).trans ?_
      have hjK : j.val + 1 ≤ K := j.isLt
      apply div_le_div₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
        (Real.rpow_pos_of_pos hu0 _)
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hu1
      have : 6 * (R - 4 * (j.val + 1) - 1) ≥ R := by omega
      have h' : (6 : ℝ) * ((R - 4 * (j.val + 1) - 1 : ℕ) : ℝ) ≥ R := by exact_mod_cast this
      rw [hs0]; linarith
    calc WG t N M K ℓ G ≤ ∏ _j ∈ G, (2 : ℝ) ^ (5 * K + 8) / u ^ s0 :=
          Finset.prod_le_prod₀ (fun j _ => wsave_nonneg t N hM1 hℓ1 _) hper
      _ = ((2 : ℝ) ^ (5 * K + 8)) ^ G.card / (u ^ s0) ^ G.card := by
          rw [prod_const, div_pow]
      _ ≤ 2 ^ (K * (5 * K + 8)) / u ^ ((G.card : ℝ) * s0) := by
          have e1 : (u ^ s0) ^ G.card = u ^ ((G.card : ℝ) * s0) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; ring_nf
          rw [e1]
          apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hu0.le _)
          rw [← pow_mul]
          exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
  -- `M^{2η} ≤ u^{1/2}`
  have hMη : (M : ℝ) ^ (2 * η) ≤ u ^ ((1 : ℝ) / 2) := by
    calc (M : ℝ) ^ (2 * η) ≤ (M : ℝ) ^ ((1 : ℝ) / 16) :=
          Real.rpow_le_rpow_of_exponent_le hMr (by linarith)
      _ ≤ (u ^ 8) ^ ((1 : ℝ) / 16) := Real.rpow_le_rpow hM0 hMle (by norm_num)
      _ = u ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast u 8, ← Real.rpow_mul hu0.le]; norm_num
  -- `Φ_G ≤ 2^{Q₀}·u^{−s}`
  set sv : ℝ := ((G.card : ℝ) * R / 6 - 1 / 2) / (2 * (ℓ : ℝ) ^ 2) with hsv
  have hPhi : PhiG t C η N M K ℓ G ≤ 2 ^ Q0 / u ^ sv := by
    set P : ℝ := C ^ 2 * 3 ^ K * (ℓ : ℝ) ^ (2 * K) with hP
    have hP0 : 0 ≤ P := by positivity
    have hWG0 := WG_nonneg t N hM1 hℓ1 G
    have hbase : P * (M : ℝ) ^ (2 * η) * WG t N M K ℓ G ≤
        (2 : ℝ) ^ (2 * Q0 * ℓ ^ 2) * u ^ ((1 : ℝ) / 2 - (G.card : ℝ) * s0) := by
      calc P * (M : ℝ) ^ (2 * η) * WG t N M K ℓ G
          ≤ P * u ^ ((1 : ℝ) / 2) * (2 ^ (K * (5 * K + 8)) / u ^ ((G.card : ℝ) * s0)) := by
            gcongr
        _ = (P * 2 ^ (K * (5 * K + 8))) *
              (u ^ ((1 : ℝ) / 2) / u ^ ((G.card : ℝ) * s0)) := by ring
        _ = (P * 2 ^ (K * (5 * K + 8))) * u ^ ((1 : ℝ) / 2 - (G.card : ℝ) * s0) := by
            rw [Real.rpow_sub hu0]
        _ ≤ _ := mul_le_mul_of_nonneg_right hQ (Real.rpow_nonneg hu0.le _)
    have hb0 : 0 ≤ P * (M : ℝ) ^ (2 * η) * WG t N M K ℓ G := by positivity
    unfold PhiG
    rw [← hP]
    have hℓpos : (0 : ℝ) < ℓ := by linarith
    calc (P * (M : ℝ) ^ (2 * η) * WG t N M K ℓ G) ^ (((2 * ℓ ^ 2 : ℕ) : ℝ))⁻¹
        ≤ ((2 : ℝ) ^ (2 * Q0 * ℓ ^ 2) * u ^ ((1 : ℝ) / 2 - (G.card : ℝ) * s0)) ^
            (((2 * ℓ ^ 2 : ℕ) : ℝ))⁻¹ := Real.rpow_le_rpow hb0 hbase (by positivity)
      _ = 2 ^ Q0 / u ^ sv := by
          rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hu0.le _),
            ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul hu0.le]
          have e1 : ((2 * Q0 * ℓ ^ 2 : ℕ) : ℝ) * (((2 * ℓ ^ 2 : ℕ) : ℝ))⁻¹ = Q0 := by
            push_cast; field_simp
          have e2 : ((1 : ℝ) / 2 - (G.card : ℝ) * s0) * (((2 * ℓ ^ 2 : ℕ) : ℝ))⁻¹ = -sv := by
            rw [hsv, hs0]; push_cast; field_simp; ring
          rw [e1, e2, Real.rpow_neg hu0.le, Real.rpow_natCast]
          ring
  -- the other terms
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
      calc |t| * u ^ 20 ≤ u ^ (R + 1) * u ^ 20 := by gcongr
        _ = u ^ (R + 21) := by rw [← pow_add]
        _ ≤ u ^ (4 * (K + 1)) := pow_le_pow_right₀ hu1 (by omega)
    have : |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) ≤ |t| * N * (1 / u ^ 4) ^ (K + 1) :=
      mul_le_mul_of_nonneg_left hq' (by positivity)
    linarith
  have hsv1 : sv ≤ 1 := by
    rw [hsv, div_le_one (by positivity)]
    have hGr : (G.card : ℝ) ≤ K := by exact_mod_cast hGK
    have hRr : (R : ℝ) ≤ 4 * K := by
      have : R ≤ 4 * K := by omega
      exact_mod_cast this
    have hKl : (K : ℝ) ≤ ℓ := by exact_mod_cast hKℓ
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have hG0 : (0 : ℝ) ≤ G.card := by positivity
    have : (G.card : ℝ) * R ≤ K * (4 * K) := mul_le_mul hGr hRr (by positivity) hK0
    nlinarith
  have hrpos : 0 < u ^ sv := Real.rpow_pos_of_pos hu0 _
  have hr1 : u ^ sv ≤ u := by
    calc u ^ sv ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 hsv1
      _ = u := Real.rpow_one u
  have hsmall : 2 + 2 * u ^ 16 ≤ (2 ^ (Q0 + 2) - 2 ^ Q0) * N / u ^ sv := by
    rw [le_div_iff₀ hrpos, hN]
    have h1 : 1 ≤ u ^ 16 := one_le_pow₀ hu1
    have h2 : (2 + 2 * u ^ 16) * u ^ sv ≤ 4 * u ^ 16 * u := by
      have : 2 + 2 * u ^ 16 ≤ 4 * u ^ 16 := by linarith
      exact mul_le_mul this hr1 hrpos.le (by positivity)
    have hQ1 : (3 : ℝ) ≤ 2 ^ (Q0 + 2) - 2 ^ Q0 := by
      have : (2 : ℝ) ^ (Q0 + 2) = 4 * 2 ^ Q0 := by rw [pow_add]; ring
      rw [this]; have := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := Q0); linarith
    have h3 : 4 * u ^ 16 * u ≤ (2 ^ (Q0 + 2) - 2 ^ Q0) * u ^ 20 := by
      have : u ^ 16 * u ≤ u ^ 20 := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hu1 (by norm_num)
      have hu3 : (8 : ℝ) ≤ u ^ 3 := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
      have e : u ^ 20 = u ^ 3 * (u ^ 16 * u) := by ring
      have hp : 0 ≤ u ^ 16 * u := by positivity
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hu3 hp, mul_le_mul_of_nonneg_right hQ1 (mul_nonneg (by linarith : (0:ℝ) ≤ u ^ 3) hp)]
    linarith
  calc ‖∑ n ∈ Ioc N N', phaseF t n‖
      ≤ N * PhiG t C η N M K ℓ G + 2 * |t| * N * ((M : ℝ) ^ 2 / N) ^ (K + 1) +
          2 * (M : ℝ) ^ 2 := hbb
    _ ≤ N * (2 ^ Q0 / u ^ sv) + 2 + 2 * u ^ 16 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hPhi hNpos.le) hTay) (by linarith)
    _ ≤ N * (2 ^ Q0 / u ^ sv) + (2 ^ (Q0 + 2) - 2 ^ Q0) * N / u ^ sv := by linarith
    _ = 2 ^ (Q0 + 2) * N / u ^ sv := by ring

end ExpSum
