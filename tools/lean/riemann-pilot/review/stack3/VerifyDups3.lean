import KubotaThetaProof
import EisensteinPrepared
import EisensteinSquarefreeRows
import EisensteinThetaRows
import EisensteinQuadSupplement
import EisensteinCompletedSums
import EisensteinSupplement
import EisensteinRowTwist
import EisensteinThetaAssembly
import EisensteinThetaMeanSquare
import EisensteinCubeReduction
import EisensteinDualMeanSquare
import HalfPlaneMeanSquare
import MellinRowDep
import KubotaPhi
import KubotaConstTerm

/-! Stack review 3, third batch (the Eisenstein reader's candidates). -/

open Complex
open scoped NumberField

namespace Eis

-- EisensteinSquarefreeRows:36 and EisensteinThetaRows:250 from EisensteinQuadSupplement:482 (no coprimality).
example : type_of% @sym6_sq_eq_pow_eight := by
  intro I hI m
  calc sym6 m I ^ 2 = sym6 m I * sym6 m I := sq _
    _ = sym6 m I ^ 7 * sym6 m I := by rw [sym6_pow_seven]
    _ = sym6 m I ^ 8 := by ring
example : type_of% @sym6_pow_nine := by
  intro I hI m; rw [show (9 : ℕ) = 7 + 2 from rfl, pow_add, sym6_pow_seven]; ring

-- EisensteinCompletedSums' coprime-6 block from EisensteinPrepared's coprime-3 block.
example : type_of% @exists_primary_gen := by
  intro I hI; exact exists_primary_gen3 (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hI)
example : type_of% @pgen_spec6 := by
  intro I hI; exact pgen_spec3 (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hI)
example : type_of% @ne_bot_of_coprime6 := by
  intro I hI; exact ne_bot_of_coprime3 (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hI)
example : type_of% @pgen_mul6 := by
  intro I J hI hJ
  exact pgen_mul3 (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hI)
    (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hJ)

-- EisensteinSupplement:231 is EisensteinQuadSupplement:244 at `m = 9`.
example : type_of% @absNorm_congr_nine := by
  intro b b' h
  have := absNorm_congr 9 (b := b) (b' := b') (by exact_mod_cast h)
  exact_mod_cast this

-- EisensteinSupplement:192 is EisensteinQuadSupplement:216 at `I = span {b}`.
example : type_of% @absNorm_span_eq_prod := by
  intro b hb; exact absNorm_eq_prod_nf (by rwa [Ne, Ideal.span_singleton_eq_bot])

-- EisensteinQuadSupplement:494 against Mathlib's `dvd_of_mul_right_dvd`.
example : type_of% @dvd_of_dvd_mul_left' := by
  intros; exact dvd_of_mul_right_dvd ‹_›

-- EisensteinPrepared:934 against Mathlib's `Real.rpow_pow_comm`.
example : type_of% @pow_rpow_comm := by
  intro a ha n x; exact (Real.rpow_pow_comm ha.le x n).symm

-- EisensteinRowTwist:174 against Mathlib's `normalizedFactors_pow` and `Multiset.count_nsmul` (no `I ≠ ⊥`).
example : type_of% @count_nf_pow := by
  intro P I hI n; rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]

-- EisensteinThetaAssembly:78 against Mathlib's `Ideal.mem_normalizedFactors_iff`.
example : type_of% @mem_nf_of_dvd := by
  intro I Q hI hQ h
  exact (Ideal.mem_normalizedFactors_iff hI).2 ⟨Ideal.isPrime_of_prime hQ, Ideal.le_of_dvd h⟩

-- HalfPlaneMeanSquare:558 is EisensteinThetaMeanSquare:28 at `ι = 𝓞 K`.
example : type_of% @norm_sum_sq_le := by
  intro T A; exact norm_sum_sq_le_card T A

-- EisensteinThetaMeanSquare:33 is KubotaPhi:43's equality, weakened.
example : type_of% @card_units_le := card_units_O.le

-- EisensteinDualMeanSquare:45's instance covers KubotaConstTerm:346.
example : type_of% @finite_quot_three_mul := by
  intro c hc
  have : NeZero (3 * c) := ⟨three_mul_ne_zero hc⟩
  exact finite_quot_of_neZero

-- EisensteinSquarefreeRows:108 is EisensteinPrepared:68 at `s = 2`.
example : type_of% @sum_idealsLe_inv_sq_le := by
  intro x
  have h := sum_idealsLe_rpow_le (s := 2) (by norm_num) x
  have e : (2 : ℝ) * (2 * kappa + 5) / (1 - (2 : ℝ) ^ (1 - (2 : ℝ))) = 4 * (2 * kappa + 5) := by
    rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]; ring
  rw [e] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun I _ => ?_)) h
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, one_div]

end Eis

-- MellinRowDep:469 is EisensteinCubeReduction:125 at `c = 1`.
example : type_of% @MellinSep.norm_sum_mul_sq_le := by
  intro ι s w hw x
  simpa using Eis.norm_sum_sq_le_weighted s (fun _ => 1) x w hw (fun _ _ => by simp)
