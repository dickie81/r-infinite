/-
# Explicit VMVT parameters for layer II (round 209)

Plain statements, for `K ≥ 7` and `m = 2K²` (so `ℓ = K(2K²+1)` variables):
* `eta_geo`: after `K²` steps the excess exponent `η` contracts by `1 − 1/K` per step (used by
  `ExpSum9.eta_two_sq32`, `η_{2K²} ≤ 1/32` for `K ≥ 10`).
* `gexp_closed`: `g(m) = K + 3K·m(m+1) + (K² + 3K + 2)·m`.
* `gexp_two_sq`: `g(2K²) ≤ 20K⁵`. With `Cvm_le`, `C_{2K²} ≤ (8(K+2))^{20K⁵}`.
-/
import VinoConst

open Finset

namespace VinoRec

lemma eta_contract {k : ℕ} (hk : 2 ≤ k) (m : ℕ) (hm : k * k ≤ m) :
    eta k (m + 1) ≤ (1 - 1 / (k : ℝ)) * eta k m := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [eta]
  apply max_le le_rfl
  have hmr : ((k * k : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  push_cast at hmr
  have hlin : (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ 2 * (((k + m * k : ℕ) : ℝ) + 1) / k := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    push_cast
    nlinarith
  have hr0 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have := mul_nonneg hr0 (eta_nonneg hk m)
  linarith

lemma eta_geo {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    eta k (k * k + j) ≤ (1 - 1 / (k : ℝ)) ^ j * eta k (k * k) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  induction j with
  | zero => simp
  | succ j ih =>
    calc eta k (k * k + (j + 1)) = eta k (k * k + j + 1) := by rw [add_assoc]
      _ ≤ (1 - 1 / (k : ℝ)) * eta k (k * k + j) := eta_contract hk _ (Nat.le_add_right _ _)
      _ ≤ (1 - 1 / (k : ℝ)) * ((1 - 1 / (k : ℝ)) ^ j * eta k (k * k)) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ = (1 - 1 / (k : ℝ)) ^ (j + 1) * eta k (k * k) := by ring

lemma gexp_closed (k m : ℕ) : gexp k m = k + 3 * k * m * (m + 1) + (k ^ 2 + 3 * k + 2) * m := by
  induction m with
  | zero => simp [gexp]
  | succ m ih => rw [gexp, ih]; ring

theorem gexp_two_sq {k : ℕ} (hk : 2 ≤ k) : gexp k (2 * k ^ 2) ≤ 20 * k ^ 5 := by
  rw [gexp_closed]
  have h2 : 2 ≤ k := hk
  have hk4 : k ^ 4 * 2 ≤ k ^ 5 := by rw [pow_succ]; exact Nat.mul_le_mul_left _ h2
  have hk3 : k ^ 3 * 4 ≤ k ^ 5 := by
    have : 4 ≤ k ^ 2 := by simpa using Nat.pow_le_pow_left h2 2
    calc k ^ 3 * 4 ≤ k ^ 3 * k ^ 2 := Nat.mul_le_mul_left _ this
      _ = k ^ 5 := by ring
  have hk2' : k ^ 2 * 8 ≤ k ^ 5 := by
    have : 8 ≤ k ^ 3 := by simpa using Nat.pow_le_pow_left h2 3
    calc k ^ 2 * 8 ≤ k ^ 2 * k ^ 3 := Nat.mul_le_mul_left _ this
      _ = k ^ 5 := by ring
  have hk1 : k * 16 ≤ k ^ 5 := by
    have : 16 ≤ k ^ 4 := by simpa using Nat.pow_le_pow_left h2 4
    calc k * 16 ≤ k * k ^ 4 := Nat.mul_le_mul_left _ this
      _ = k ^ 5 := by ring
  nlinarith

end VinoRec
