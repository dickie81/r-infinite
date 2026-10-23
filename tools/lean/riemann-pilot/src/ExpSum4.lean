/-
# Layer II helpers from round 206

Round 206's one-coordinate block bound (`Bn_bound`, `block_bound`) fed only round 210's chain, which
`ExpSum8`–`ExpSum10` superseded; both were removed in round 218. What later files use remains:
`oneD_three`, `prod_three_L` and the saving `Wsave`.
-/
import ExpSum3

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

lemma oneD_three (α : ℝ) (L : ℕ) (hL : 1 ≤ L) :
    ∑ z ∈ Icc (-(L : ℤ)) L, ‖inner α z L‖ ≤ 3 * (L : ℝ) ^ 2 := by
  refine (oneD_trivial α L L).trans ?_
  have : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith

lemma prod_three_L (K M ℓ : ℕ) :
    ∏ j : Fin K, (3 * ((Lbox K M ℓ j : ℕ) : ℝ) ^ 2) =
      3 ^ K * (ℓ : ℝ) ^ (2 * K) * (M : ℝ) ^ (K * (K + 1)) := by
  simp only [Lbox, Nat.cast_mul, Nat.cast_pow, mul_pow, Finset.prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hs : ∑ j : Fin K, (j.val + 1) * 2 = K * (K + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (i + 1) * 2), ← Finset.sum_mul,
      Finset.sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one, add_mul,
      Finset.sum_range_id_mul_two]
    rcases K with _ | K
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  rw [hs]; ring

/-- The explicit saving factor of the good coordinate. -/
noncomputable def Wsave (t : ℝ) (N M ℓ r : ℕ) : ℝ :=
  1 / ((ℓ : ℝ) * (M : ℝ) ^ r) +
    2 * Real.pi * r * (2 * (N : ℝ)) ^ r * (1 + Real.log ((ℓ : ℝ) * (M : ℝ) ^ r)) /
      (|t| * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * r))

end ExpSum
