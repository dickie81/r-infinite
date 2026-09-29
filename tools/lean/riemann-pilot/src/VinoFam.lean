/-
# Sharpening, step S2c: the sharp family and growth for every `a > 2/3` (round 214)

Plain statements.
* `sharpFamily ε` (`0 < ε ≤ 1/2`): VMVT from round 214 (`vmvt2`) at `m = K(⌊log₂(16K²)⌋ + 1)`
  steps is a `VMVTFamily` with `ℓ = K(m+1) ≤ (6 + 3/ε)·K^{2+ε}`, `η ≤ 1/32` and constant
  exponent `Q₀ = 300`.
* `growth_sharp`: for every `2/3 < a ≤ 1`, the Dirichlet-polynomial growth bound of round 211
  holds at exponent `a` (take `ε = (3a−2)/2` in `growth_gen`).
-/
import VinoRec2
import ExpSum10

open Finset

namespace VinoFam

open Vinogradov VinoRec VinoRec2 ExpSum

/-- The number of steps. -/
def mf (K : ℕ) : ℕ := K * (Nat.log 2 (16 * K ^ 2) + 1)

/-- The family's `ℓ`. -/
def ℓf (K : ℕ) : ℕ := K + mf K * K

lemma half_pow {K : ℕ} (hK : 2 ≤ K) : (1 - 1 / (K : ℝ)) ^ K ≤ 1 / 2 := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h0 : 0 ≤ 1 - 1 / (K : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h1 : 1 - 1 / (K : ℝ) ≤ Real.exp (-(1 / (K : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (K : ℝ))); linarith
  calc (1 - 1 / (K : ℝ)) ^ K ≤ (Real.exp (-(1 / (K : ℝ)))) ^ K := pow_le_pow_left₀ h0 h1 _
    _ = Real.exp (-1) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    _ ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]
        apply inv_anti₀ (by norm_num)
        have := Real.add_one_le_exp (1 : ℝ); linarith

lemma eta_small2 {K : ℕ} (hK : 2 ≤ K) : eta2 K (mf K) ≤ 1 / 32 := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  set L := Nat.log 2 (16 * K ^ 2) with hL
  have h0 : 0 ≤ 1 - 1 / (K : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hpow : (1 - 1 / (K : ℝ)) ^ (mf K) ≤ (1 / 2) ^ (L + 1) := by
    rw [mf, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg h0 _) (half_pow hK) _
  have h2 : (16 * (K : ℝ) ^ 2) < 2 ^ (L + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (16 * K ^ 2)
    exact_mod_cast this
  have hhalf : ((1 : ℝ) / 2) ^ (L + 1) ≤ 1 / (16 * (K : ℝ) ^ 2) := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hc : 0 ≤ (K : ℝ) * ((K : ℝ) - 1) / 2 := by nlinarith
  unfold eta2
  calc (1 - 1 / (K : ℝ)) ^ (mf K) * ((K : ℝ) * ((K : ℝ) - 1) / 2)
      ≤ 1 / (16 * (K : ℝ) ^ 2) * ((K : ℝ) * ((K : ℝ) - 1) / 2) :=
        mul_le_mul_of_nonneg_right (hpow.trans hhalf) hc
    _ ≤ 1 / 32 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

lemma ℓf_le {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 2 ≤ K) :
    (ℓf K : ℝ) ≤ (6 + 3 / ε) * (K : ℝ) ^ (2 + ε) := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  set L := Nat.log 2 (16 * K ^ 2) with hL
  -- `L ≤ 4 + 3 log K`
  have hLlog : (L : ℝ) ≤ 4 + 3 * Real.log K := by
    have h := Nat.pow_log_le_self 2 (show 16 * K ^ 2 ≠ 0 by positivity)
    have h' : ((2 ^ L : ℕ) : ℝ) ≤ ((16 * K ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    have hl := Real.log_le_log (by positivity) h'
    push_cast at hl
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
    have hl2 := Real.log_two_gt_d9
    have hl16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    rw [hl16] at hl
    push_cast at hl
    have : (L : ℝ) * Real.log 2 ≤ 4 * Real.log 2 + 2 * Real.log K := by linarith
    have hL2 : (L : ℝ) ≤ 4 + 2 * Real.log K / Real.log 2 := by
      rw [← sub_nonneg]
      have : 4 + 2 * Real.log K / Real.log 2 - (L : ℝ) =
          (4 * Real.log 2 + 2 * Real.log K - (L : ℝ) * Real.log 2) / Real.log 2 := by
        field_simp
      rw [this]; apply div_nonneg <;> linarith
    have : 2 * Real.log K / Real.log 2 ≤ 3 * Real.log K := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hlogK : Real.log K ≤ (K : ℝ) ^ ε / ε := Real.log_le_rpow_div hK0.le hε
  have hKε : 1 ≤ (K : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hL2 : (L : ℝ) + 2 ≤ (6 + 3 / ε) * (K : ℝ) ^ ε := by
    have : 3 * Real.log K ≤ 3 / ε * (K : ℝ) ^ ε := by
      have := mul_le_mul_of_nonneg_left hlogK (show (0 : ℝ) ≤ 3 by norm_num)
      calc 3 * Real.log K ≤ 3 * ((K : ℝ) ^ ε / ε) := this
        _ = 3 / ε * (K : ℝ) ^ ε := by ring
    have : 6 ≤ 6 * (K : ℝ) ^ ε := by linarith
    nlinarith
  have hℓ : (ℓf K : ℝ) ≤ (K : ℝ) ^ 2 * ((L : ℝ) + 2) := by
    unfold ℓf mf; push_cast; nlinarith
  calc (ℓf K : ℝ) ≤ (K : ℝ) ^ 2 * ((L : ℝ) + 2) := hℓ
    _ ≤ (K : ℝ) ^ 2 * ((6 + 3 / ε) * (K : ℝ) ^ ε) := by gcongr
    _ = (6 + 3 / ε) * (K : ℝ) ^ (2 + ε) := by
        rw [Real.rpow_add hK0, Real.rpow_two]; ring

set_option maxHeartbeats 1600000 in
/-- The weak-VMVT constant absorbs the block-bound constants, for any `m ≥ K`. -/
lemma const_bound_m {K m : ℕ} (hK : 10 ≤ K) (hmK : K ≤ m) :
    (Cv2 K m) ^ 2 * 3 ^ K * ((K + m * K : ℕ) : ℝ) ^ (2 * K) * 2 ^ (K * (5 * K + 8)) ≤
      (2 : ℝ) ^ (2 * 300 * (K + m * K) ^ 2) := by
  have hK2 : 2 ≤ K := by omega
  set ℓ := K + m * K with hℓ
  have hC := Cv2_le hK2 m
  have hC0 : 0 ≤ Cv2 K m := (zero_lt_one.trans_le (Cv2_ge_one hK2 m)).le
  set g := 40 * K ^ 2 * (m + 1) + gexp K m with hg
  have h1 : (Cv2 K m) ^ 2 ≤ (2 : ℝ) ^ ((K + 4) * g * 2) := by
    calc _ ≤ ((8 * ((K : ℝ) + 2)) ^ g) ^ 2 := pow_le_pow_left₀ hC0 hC 2
      _ ≤ (((2 : ℝ) ^ (K + 4)) ^ g) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) (eight_K_le K) _) 2
      _ = _ := by rw [← pow_mul, ← pow_mul]; ring_nf
  have h2 : (3 : ℝ) ^ K ≤ 2 ^ (2 * K) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h3 : ((ℓ : ℕ) : ℝ) ^ (2 * K) ≤ 2 ^ (ℓ * (2 * K)) := by
    have hl : ((ℓ : ℕ) : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc ((ℓ : ℕ) : ℝ) ^ (2 * K) ≤ ((2 : ℝ) ^ ℓ) ^ (2 * K) := pow_le_pow_left₀ (by positivity) hl _
      _ = _ := by rw [← pow_mul]
  have hE : (K + 4) * g * 2 + 2 * K + ℓ * (2 * K) + K * (5 * K + 8) ≤ 2 * 300 * ℓ ^ 2 := by
    rw [hg, gexp_closed, hℓ]
    have a1 : K ^ 3 * m ≤ K ^ 2 * m ^ 2 := by
      have := Nat.mul_le_mul_left (K ^ 2 * m) hmK; nlinarith
    have a2 : K ^ 3 ≤ K ^ 2 * m := by
      have := Nat.mul_le_mul_left (K ^ 2) hmK; nlinarith
    have a3 : K * m ^ 2 ≤ K ^ 2 * m ^ 2 := by
      have : 1 ≤ K := by omega
      nlinarith [Nat.mul_le_mul_right (m ^ 2) this]
    have a4 : K * m ≤ K ^ 2 * m := by
      have : 1 ≤ K := by omega
      nlinarith [Nat.mul_le_mul_right (K * m) this]
    have a5 : K ≤ K ^ 2 := by nlinarith
    have a6 : m ≤ K * m := by nlinarith
    have a7 : K ^ 2 ≤ K ^ 2 * m := by nlinarith
    ring_nf
    nlinarith
  calc (Cv2 K m) ^ 2 * 3 ^ K * ((ℓ : ℕ) : ℝ) ^ (2 * K) * 2 ^ (K * (5 * K + 8))
      ≤ (2 : ℝ) ^ ((K + 4) * g * 2) * 2 ^ (2 * K) * 2 ^ (ℓ * (2 * K)) *
          2 ^ (K * (5 * K + 8)) := by gcongr
    _ = (2 : ℝ) ^ ((K + 4) * g * 2 + 2 * K + ℓ * (2 * K) + K * (5 * K + 8)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hE

lemma const_bound3 {K : ℕ} (hK : 10 ≤ K) :
    (Cv2 K (mf K)) ^ 2 * 3 ^ K * ((ℓf K : ℕ) : ℝ) ^ (2 * K) * 2 ^ (K * (5 * K + 8)) ≤
      (2 : ℝ) ^ (2 * 300 * ℓf K ^ 2) :=
  const_bound_m hK (Nat.le_mul_of_pos_right _ (by omega))

/-- **The sharp VMVT family.** -/
theorem sharpFamily {ε : ℝ} (hε : 0 < ε) : VMVTFamily 10 300 (2 + ε) (6 + 3 / ε) ℓf := by
  intro K hK
  have hK2 : 2 ≤ K := by omega
  refine ⟨by unfold ℓf; omega, ℓf_le hε hK2, Cv2 K (mf K), eta2 K (mf K),
    (vmvt2 hK2 (mf K)).1, eta_small2 hK2, ?_, const_bound3 hK⟩
  intro P hP
  have h := (vmvt2 hK2 (mf K)).2 P hP
  convert h using 3
  all_goals first | rfl | (unfold VinoRec2.expo2 ℓf; push_cast; ring)

/-- **Growth for every `a > 2/3`.** -/
theorem growth_sharp {a : ℝ} (ha1 : 2 / 3 < a) (ha2 : a ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ t σ : ℝ, 1 ≤ Real.log |t| → 1 - Real.log |t| ^ (-a) ≤ σ →
      ∀ X : ℕ, (X : ℝ) ≤ |t| ^ ((5 : ℝ) / 4) →
        ‖∑ n ∈ Ioc 0 X, 1 / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ ≤ B * Real.log |t| := by
  set ε := (3 * a - 2) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hB0 : 1 ≤ 6 + 3 / ε := by have : 0 ≤ 3 / ε := by positivity
                                 linarith
  refine growth_gen (sharpFamily hε) le_rfl (by linarith) hB0 ?_ ha2
  rw [div_le_iff₀ (by linarith), hεdef]
  nlinarith

end VinoFam
