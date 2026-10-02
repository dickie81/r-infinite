/-
# Rung 3 of the wander ladder, reduced to its analytic input (round 192)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement.
* `rung3_of_region`: suppose ζ has no zeros in the region `σ ≥ 1 − A/(log|t|)^{n₁}`, and ζ'/ζ is
  at most `C·(log|t|)^{n₂}` there. Then
  `ψ(x) − x = O(x·exp(−c·(log x)^{1/(1+n₁)}))`.
* De la Vallée Poussin is `n₁ = 1` (exponent 1/2, rung 2). The Korobov–Vinogradov region
  `σ ≥ 1 − c/((log t)^{2/3}(log log t)^{1/3})` contains `σ ≥ 1 − A/(log t)^{n₁}` for every
  `n₁ > 2/3`. So KV gives every exponent below 3/5 (`rung3_exponent`). That is rung 3,
  up to the `(log log x)^{−1/5}` factor.
* What is NOT proved here: the KV zero-free region and log-derivative bound themselves
  (`KVInput`). They rest on Vinogradov's mean value theorem for exponential sums, which is not
  formalised in Lean as far as I know.
-/
import PrimeNumberTheoremAnd.StrongPNT

open Filter Asymptotics Real

namespace Rung3

/-- The analytic input of rung 3: a zero-free region of width `(log t)^{−n₁}` with a
log-derivative bound `(log t)^{n₂}` inside it. -/
def KVInput (n₁ n₂ : ℝ) : Prop := ZetaZeroFreeGenProp n₁ ∧ LogDerivZetaBndUnifGenProp n₁ n₂

/-- **Rung 3, reduced.** A zero-free region of width `(log t)^{−n₁}` (with the log-derivative
bound) gives drift `O(x·exp(−c (log x)^{1/(1+n₁)}))`. -/
theorem rung3_of_region {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : KVInput n₁ n₂) :
    ∃ c > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁)))) :=
  GenStrengthPNT (LogDerivZetaBoundedAndHoloGen h.2 (LogDerivZetaHolcLargeTGen h.1 hn₁)) hn₁ hn₂

/-- The exponent: for `n₁ ∈ (2/3, 1)` (the Korobov–Vinogradov range) the exponent `1/(1+n₁)`
lies strictly between de la Vallée Poussin's `1/2` and `3/5`. -/
theorem rung3_exponent {n₁ : ℝ} (h1 : 2 / 3 < n₁) (h2 : n₁ < 1) :
    (1 : ℝ) / 2 < 1 / (1 + n₁) ∧ 1 / (1 + n₁) < 3 / 5 := by
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  · rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith

end Rung3

#print axioms Rung3.rung3_of_region
#print axioms Rung3.rung3_exponent
