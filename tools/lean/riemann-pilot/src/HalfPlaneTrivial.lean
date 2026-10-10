import HalfPlaneS0

/-! # The trivial range of S0's hypothesis (round 280)

`SmoothBound θ` (round 278) holds for every `θ ≥ 1` (`smoothBound_of_one_le`). So the hypothesis of
`ne_zero_of_smoothBound` and of round 279's joins is satisfiable, and those theorems are not vacuous
as statements. The proof is Rankin's trick: for `1 ≤ n ≤ X`, `|μ_K(n)| ≤ X^σ|μ_K(n)|n^{−σ}`
(`norm_le_rpow_mul_norm_term`), and `Σ_n |μ_K(n)|n^{−σ}` converges for `σ = 1 + ε`
(`LSeriesSummable_muK`). A weight bounded by `M` and vanishing beyond `R` then gives
`|Σ_n μ_K(n)W(n/D)| ≤ M((R + 1)D)^{1+ε}Σ_n |μ_K(n)|n^{−1−ε}`.

At `θ = 1` the conclusion of S0 is the classical `ζ(s)L(s, χ₋₃) ≠ 0` on `Re s > 1`; nothing below
`Re s = 1` is claimed. Every `θ < 1` is open in the stack: that is the target of S1–S6.
-/

open Complex Filter Topology Asymptotics
open scoped LSeries.notation

namespace HalfPlaneS0

/-- Rankin's trick for one term: for `1 ≤ n ≤ X` and `σ ≥ 0`, `‖a n‖ ≤ X^σ‖a n / n^σ‖`. -/
theorem norm_le_rpow_mul_norm_term (a : ℕ → ℂ) {σ X : ℝ} (hσ : 0 ≤ σ) {n : ℕ} (hn : n ≠ 0)
    (hnX : (n : ℝ) ≤ X) : ‖a n‖ ≤ X ^ σ * ‖LSeries.term a σ n‖ := by
  rw [LSeries.norm_term_eq]
  simp only [hn, ↓reduceIte, ofReal_re]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h1 : (n : ℝ) ^ σ ≤ X ^ σ := Real.rpow_le_rpow hn0.le hnX hσ
  rw [← mul_div_assoc, le_div_iff₀ (Real.rpow_pos_of_pos hn0 σ)]
  calc ‖a n‖ * (n : ℝ) ^ σ ≤ ‖a n‖ * X ^ σ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = X ^ σ * ‖a n‖ := mul_comm _ _

/-- **The trivial range of the hypothesis**: `SmoothBound θ` holds for every `θ ≥ 1`. -/
theorem smoothBound_of_one_le {θ : ℝ} (hθ : 1 ≤ θ) : SmoothBound θ := by
  intro W hW ε hε
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  obtain ⟨M, hM⟩ := hW.compact.exists_bound_of_continuous hW.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set σ : ℝ := 1 + ε with hσdef
  have hσ1 : 1 < ((σ : ℂ)).re := by rw [ofReal_re]; linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hsum : Summable fun n => ‖LSeries.term muK σ n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_muK hσ1)
  set S := ∑' n, ‖LSeries.term muK σ n‖ with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have key : ∀ D : ℝ, 1 ≤ D → ‖smoothSum W D‖ ≤ M * ((R + 1) * D) ^ σ * S := by
    intro D hD
    have hD0 : 0 < D := by linarith
    set C := M * ((R + 1) * D) ^ σ
    have hC0 : 0 ≤ C := mul_nonneg hM0 (Real.rpow_nonneg (by positivity) _)
    refine tsum_of_norm_bounded (g := fun n => C * ‖LSeries.term muK σ n‖)
      (hsum.hasSum.mul_left C) fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [muK_zero]
    by_cases hW0 : W (n / D) = 0
    · simp [hW0]; positivity
    have hnD : (n : ℝ) / D ≤ R := by
      by_contra hc; exact hW0 (hR _ (not_le.1 hc))
    have hnX : (n : ℝ) ≤ (R + 1) * D := by
      rw [div_le_iff₀ hD0] at hnD; nlinarith
    have hr := norm_le_rpow_mul_norm_term muK hσ0 hn hnX
    rw [norm_mul, Complex.norm_real]
    calc ‖muK n‖ * ‖W (n / D)‖ ≤ ‖muK n‖ * M := mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ ≤ (((R + 1) * D) ^ σ * ‖LSeries.term muK σ n‖) * M := mul_le_mul_of_nonneg_right hr hM0
      _ = C * ‖LSeries.term muK σ n‖ := by simp only [C]; ring
  refine IsBigO.of_bound (M * (R + 1) ^ σ * S) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
  have hD0 : 0 < D := by linarith
  have e : ((R + 1) * D) ^ σ = (R + 1) ^ σ * D ^ σ :=
    Real.mul_rpow (by linarith) hD0.le
  have hDσ : D ^ σ ≤ ‖D ^ (θ + ε)‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hD0.le _)]
    exact Real.rpow_le_rpow_of_exponent_le hD (by rw [hσdef]; linarith)
  calc ‖smoothSum W D‖ ≤ M * ((R + 1) * D) ^ σ * S := key D hD
    _ = M * (R + 1) ^ σ * S * D ^ σ := by rw [e]; ring
    _ ≤ M * (R + 1) ^ σ * S * ‖D ^ (θ + ε)‖ := by
        apply mul_le_mul_of_nonneg_left hDσ
        exact mul_nonneg (mul_nonneg hM0 (Real.rpow_nonneg (by linarith) _)) hS0

end HalfPlaneS0

#print axioms HalfPlaneS0.norm_le_rpow_mul_norm_term
#print axioms HalfPlaneS0.smoothBound_of_one_le
