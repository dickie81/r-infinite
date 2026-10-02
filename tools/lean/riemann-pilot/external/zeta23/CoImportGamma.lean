import DetectEM
import Zeta23.GammaFacts.Complete

/-! # The pnt layer and zeta23's Gamma facts co-import (round 248)

`DetectEM` and `Zeta23.GammaFacts.Complete` load together; the Vinogradov block saving is stated as a `Prop`.
-/

open Real Complex

noncomputable section

namespace CoImportGamma

example : Zeta23.GammaFacts := Zeta23.gammaFacts

/-- `1 + 2μ ≤ 2 + μ²` for every real `μ`: the factor of `large_values_amgm` never exceeds `large_values`'. -/
theorem amgm_factor_le (μ : ℝ) : 1 + 2 * μ ≤ 2 + μ ^ 2 := by nlinarith [sq_nonneg (μ - 1)]

/-- The Vinogradov–Korobov power saving on a dyadic block, uniformly in the block length
(`|Σ_{M<n≤N} n^{−it}| ≤ C·M^{1 − c(log M/log|t|)²}` for `M ≤ |t|^{5/4}`); the stack proves only its
thin-strip consequences (`ExpSum.big_block_gen`, `growth_gen`). -/
def VinoBlockSaving : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (t : ℝ) (M N : ℕ), 2 ≤ M → M ≤ N → N ≤ 2 * M → Real.exp 1 ≤ |t| →
    (M : ℝ) ≤ |t| ^ ((5 : ℝ) / 4) →
    ‖∑ n ∈ Finset.Ioc M N, (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖
      ≤ C * (M : ℝ) ^ (1 - c * (Real.log M / Real.log |t|) ^ 2)

end CoImportGamma

#print axioms CoImportGamma.amgm_factor_le
