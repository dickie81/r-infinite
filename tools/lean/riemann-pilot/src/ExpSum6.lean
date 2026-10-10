/-
# Layer II helpers from round 210

Round 210's explicit per-block saving (`block_saving`, with `const_bound`, `wsave_le`, `phi_le`) was
superseded by the many-coordinate bounds of `ExpSum8`–`ExpSum10` (round 213) and removed in round 218.
Two elementary facts that later files use remain: `floor_facts` (`M = ⌊u⁸⌋`) and `eight_K_le`.
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

end ExpSum
