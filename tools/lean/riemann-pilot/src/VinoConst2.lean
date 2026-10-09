/-
# Explicit VMVT parameters for layer II (round 209)

Plain statements, for `K ≥ 7` and `m = 2K²` (so `ℓ = K(2K²+1)` variables):
* `eta_geo` (in `VinoRec.lean` since round 334, where `eta_small` uses it): after `K²` steps the
  excess exponent `η` contracts by `1 − 1/K` per step (used by `ExpSum9.eta_two_sq32`,
  `η_{2K²} ≤ 1/32` for `K ≥ 10`).
* `gexp_closed`: `g(m) = K + 3K·m(m+1) + (K² + 3K + 2)·m`.
* `gexp_two_sq`: `g(2K²) ≤ 20K⁵`. With `Cvm_le`, `C_{2K²} ≤ (8(K+2))^{20K⁵}`.
-/
import VinoConst

open Finset

namespace VinoRec

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
