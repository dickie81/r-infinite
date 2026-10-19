import Mathlib

open Real

namespace SieveDyadic

/-- `ψ₁(t) = g(2t − 1)`, with `g` Mathlib's `Real.smoothTransition`: `0` for `t ≤ 1/2`, `1` for `t ≥ 1`. -/
noncomputable def psi1 (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

/-- The dyadic bump `f0(t) = ψ₁(t) − ψ₁(t/2)`. -/
noncomputable def bump (t : ℝ) : ℝ := psi1 t - psi1 (t / 2)

theorem psi1_zero {t : ℝ} (ht : t ≤ 1 / 2) : psi1 t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem psi1_one {t : ℝ} (ht : 1 ≤ t) : psi1 t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem psi1_mono : Monotone psi1 := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)

theorem contDiff_bump {n : ℕ∞} : ContDiff ℝ n bump := by
  unfold bump psi1
  exact (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).sub
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_id.div_const 2)).sub contDiff_const))

theorem bump_support : Function.support bump ⊆ Set.Icc (1 / 2) 2 := by
  intro t ht
  rw [Function.mem_support] at ht
  constructor
  · by_contra h
    push Not at h
    exact ht (by rw [bump, psi1_zero h.le, psi1_zero (by linarith)]; ring)
  · by_contra h
    push Not at h
    exact ht (by rw [bump, psi1_one (by linarith), psi1_one (by linarith)]; ring)

theorem bump_nonneg (t : ℝ) : 0 ≤ bump t := by
  unfold bump
  rcases le_or_gt t 0 with h | h
  · rw [psi1_zero (by linarith), psi1_zero (by linarith)]; norm_num
  · have := psi1_mono (show t / 2 ≤ t by linarith)
    linarith

theorem bump_le_one (t : ℝ) : bump t ≤ 1 := by
  unfold bump psi1
  have h1 := Real.smoothTransition.le_one (2 * t - 1)
  have h2 := Real.smoothTransition.nonneg (2 * (t / 2) - 1)
  linarith

/-- **The dyadic partition of unity.** For `1 ≤ t ≤ 2^M`, `Σ_{k ≤ M} f0(t/2^k) = 1`. -/
theorem sum_bump {t : ℝ} {M : ℕ} (h1 : 1 ≤ t) (hM : t ≤ 2 ^ M) :
    ∑ k ∈ Finset.range (M + 1), bump (t / 2 ^ k) = 1 := by
  have htel : ∀ N : ℕ, ∑ k ∈ Finset.range N, bump (t / 2 ^ k) = psi1 t - psi1 (t / 2 ^ N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, bump, pow_succ, div_div]
      ring
  rw [htel, psi1_one h1, psi1_zero]
  · ring
  · rw [div_le_iff₀ (by positivity), pow_succ]
    linarith

end SieveDyadic
