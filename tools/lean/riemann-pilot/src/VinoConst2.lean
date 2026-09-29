/-
# Explicit VMVT parameters for layer II (round 209)

Plain statements, for `K ≥ 7` and `m = 2K²` (so `ℓ = K(2K²+1)` variables):
* `eta_two_sq`: the excess exponent satisfies `η_{2K²} ≤ 1/8`. After `K²` steps `η` contracts
  by `1 − 1/K` per step, and `(1 − 1/K)^{K²} ≤ e^{−K}`.
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

/-- **`η_{2K²} ≤ 1/8` for `K ≥ 7`.** -/
theorem eta_two_sq {k : ℕ} (hk : 7 ≤ k) : eta k (2 * k ^ 2) ≤ 1 / 8 := by
  have hk2 : 2 ≤ k := by omega
  have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hsplit : 2 * k ^ 2 = k * k + k * k := by ring
  rw [hsplit]
  have hg := eta_geo hk2 (k * k)
  have hle := eta_le hk2 (k * k)
  have hr0 : 0 ≤ 1 - 1 / (k : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  -- `(1 − 1/k)^{k²} ≤ e^{−k}`
  have hexp : (1 - 1 / (k : ℝ)) ^ (k * k) ≤ Real.exp (-(k : ℝ)) := by
    have h1 : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / (k : ℝ))) := by
      have := Real.add_one_le_exp (-(1 / (k : ℝ))); linarith
    calc (1 - 1 / (k : ℝ)) ^ (k * k) ≤ (Real.exp (-(1 / (k : ℝ)))) ^ (k * k) :=
          pow_le_pow_left₀ hr0 h1 _
      _ = Real.exp (-(k : ℝ)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  -- `4k(k+1) ≤ e^k` for `k ≥ 7`
  have hek : 4 * (k : ℝ) * ((k : ℝ) + 1) ≤ Real.exp k := by
    -- `e^k ≥ Σ_{j<6} k^j/j!`
    have h3 : 1 + (k : ℝ) + (k : ℝ) ^ 2 / 2 + (k : ℝ) ^ 3 / 6 + (k : ℝ) ^ 4 / 24
        + (k : ℝ) ^ 5 / 120 ≤ Real.exp k := by
      have := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ k) 6
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
      norm_num [Nat.factorial] at this
      linarith
    have hk7 : 0 ≤ (k : ℝ) - 7 := by linarith
    nlinarith [mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 4),
      mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 3),
      mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2),
      mul_nonneg hk7 (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  have hpos : 0 < Real.exp (-(k : ℝ)) := Real.exp_pos _
  have hekinv : Real.exp (-(k : ℝ)) * (4 * (k : ℝ) * ((k : ℝ) + 1)) ≤ 1 := by
    rw [Real.exp_neg]
    rw [inv_mul_le_iff₀ (Real.exp_pos _)]; linarith
  have hη0 := eta_nonneg hk2 (k * k)
  calc eta k (k * k + k * k) ≤ (1 - 1 / (k : ℝ)) ^ (k * k) * eta k (k * k) := hg
    _ ≤ Real.exp (-(k : ℝ)) * ((k : ℝ) * ((k : ℝ) + 1) / 2) :=
        mul_le_mul hexp hle hη0 (Real.exp_pos _).le
    _ = (Real.exp (-(k : ℝ)) * (4 * (k : ℝ) * ((k : ℝ) + 1))) / 8 := by ring
    _ ≤ 1 / 8 := by linarith

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
