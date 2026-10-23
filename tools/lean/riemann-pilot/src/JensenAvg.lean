import Mathlib

/-! # Jensen's formula with an averaged majorant (round 401)

Mathlib's `AnalyticOnNhd.sum_divisor_le` bounds the number of zeros of `f` in the closed disc of radius `r` by
`log(M/|f(c)|)/log(R/r)`, where `M ≥ 1` bounds `|f|` on the circle of radius `R`. Here the pointwise bound is replaced
by the mean square on the circle, which is what a mean-square bound for `ζ` controls (`ZetaDiscs`).

* **`log_le_half_log_add`**: `log x ≤ ½ log λ + x²/(2λ)` for `x ≥ 0` and `λ ≥ 1`.
* **`sum_divisor_mul_log_le`**: for `f` analytic on the closed disc of radius `R` about `c` with `f(c) ≠ 0`, and for
  `0 < r < R` and `λ ≥ 1`, `n(r)·log(R/r) ≤ ½ log λ + (1/2λ)·avg_{|z−c|=R} |f(z)|² − log |f(c)|`, where `n(r)` counts
  the zeros in the closed disc of radius `r` with multiplicity (Mathlib's `divisor`).
-/

open Real Complex Metric Set Filter MeromorphicOn MeasureTheory
open scoped Topology

noncomputable section

namespace JensenAvg

/-- `log x ≤ ½ log λ + x²/(2λ)` for `x ≥ 0` and `λ ≥ 1` (Lean's `log 0 = 0` included). -/
lemma log_le_half_log_add {x lam : ℝ} (hx : 0 ≤ x) (hlam : 1 ≤ lam) :
    Real.log x ≤ Real.log lam / 2 + x ^ 2 / (2 * lam) := by
  have hlam0 : 0 < lam := by linarith
  rcases hx.eq_or_lt with rfl | hx
  · have := Real.log_nonneg hlam
    simp only [Real.log_zero]
    positivity
  · have h1 : Real.log (x ^ 2 / lam) ≤ x ^ 2 / lam - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hlam0.ne', Real.log_pow] at h1
    have e : x ^ 2 / (2 * lam) = (x ^ 2 / lam) / 2 := by field_simp
    rw [e]
    push_cast at h1
    linarith

/-- **Jensen's formula with an averaged majorant.** If `f` is analytic on the closed disc of radius `R`
about `c` and `f c ≠ 0`, then for `0 < r < R` and `λ ≥ 1` the zeros of `f` in the closed disc of radius `r`,
counted with multiplicity, satisfy `n(r) log(R/r) ≤ ½ log λ + (1/2λ)·avg_{|z−c|=R} |f|² − log |f(c)|`.
(Mathlib's `AnalyticOnNhd.sum_divisor_le` is the same argument with a bound `M ≥ 1` for `|f|` on the circle in
place of the averaged majorant.) -/
theorem sum_divisor_mul_log_le {f : ℂ → ℂ} {c : ℂ} {r R lam : ℝ} (hr : 0 < r) (hrR : r < R)
    (hlam : 1 ≤ lam) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    (∑ᶠ u, (divisor f (closedBall c r) u : ℝ)) * Real.log (R / r)
      ≤ Real.log lam / 2 + circleAverage (fun z => ‖f z‖ ^ 2) c R / (2 * lam) - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  have habsR : |R| = R := abs_of_pos hR
  have habsr : |r| = r := abs_of_pos hr
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [habsR]
  have jensen := hf'.circleAverage_log_norm hR.ne' hfc
  have hcont : ContinuousOn f (sphere c |R|) :=
    (hf'.continuousOn).mono sphere_subset_closedBall
  have hlogint : CircleIntegrable (fun z => Real.log ‖f z‖) c R :=
    (hf'.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hsqint : CircleIntegrable (fun z => ‖f z‖ ^ 2) c R :=
    ContinuousOn.circleIntegrable' (hcont.norm.pow 2)
  have hmajint : CircleIntegrable (fun z => Real.log lam / 2 + ‖f z‖ ^ 2 / (2 * lam)) c R :=
    ContinuousOn.circleIntegrable' (continuousOn_const.add ((hcont.norm.pow 2).div_const _))
  have hbound : circleAverage (fun z => Real.log ‖f z‖) c R
      ≤ Real.log lam / 2 + circleAverage (fun z => ‖f z‖ ^ 2) c R / (2 * lam) := by
    calc circleAverage (fun z => Real.log ‖f z‖) c R
        ≤ circleAverage (fun z => Real.log lam / 2 + ‖f z‖ ^ 2 / (2 * lam)) c R :=
          circleAverage_mono hlogint hmajint fun z _ => log_le_half_log_add (norm_nonneg _) hlam
      _ = Real.log lam / 2 + circleAverage (fun z => ‖f z‖ ^ 2) c R / (2 * lam) := by
          have hq : CircleIntegrable (fun z => ‖f z‖ ^ 2 / (2 * lam)) c R :=
            ContinuousOn.circleIntegrable' ((hcont.norm.pow 2).div_const _)
          rw [circleAverage_fun_add (f₁ := fun _ => Real.log lam / 2)
            (f₂ := fun z => ‖f z‖ ^ 2 / (2 * lam)) (circleIntegrable_const _ c R) hq,
            circleAverage_const]
          congr 1
          have e : (fun z => ‖f z‖ ^ 2 / (2 * lam)) = fun z => (2 * lam)⁻¹ • (‖f z‖ ^ 2) := by
            funext z; rw [smul_eq_mul]; ring
          rw [e, circleAverage_fun_smul, smul_eq_mul]
          ring
  have hfinr := (divisor f (closedBall c |r|)).finiteSupport (isCompact_closedBall c |r|)
  have hfinR := (divisor f (closedBall c |R|)).finiteSupport (isCompact_closedBall c |R|)
  have key : ∑ᶠ u, (divisor f (closedBall c |r|) u : ℝ) * Real.log (R / r)
      ≤ ∑ᶠ u, (divisor f (closedBall c |R|) u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_le_finsum ?_ ?_ fun u ↦ ?_
    · exact hfinr.subset fun _ _ ↦ (by simp_all)
    · exact hfinR.subset fun _ _ ↦ (by simp_all)
    · by_cases h1 : u ∈ closedBall c |R|
      · by_cases h2 : u ∈ closedBall c |r|
        · have hsub : closedBall c |r| ⊆ closedBall c |R| :=
            closedBall_subset_closedBall (by rw [habsr, habsR]; exact hrR.le)
          simp only [(hf'.mono hsub), h2, AnalyticOnNhd.divisor_apply, hf', h1]
          by_cases! h3 : u = c
          · rw [h3, (hf' c (by simp)).analyticOrderAt_eq_zero.mpr hfc]
            simp
          have hcu : 0 < ‖c - u‖ := by
            rw [norm_pos_iff, sub_ne_zero]; exact fun h => h3 h.symm
          have hle : ‖c - u‖ ≤ r := by
            rw [mem_closedBall, dist_eq_norm, habsr, ← norm_neg, neg_sub] at h2; exact h2
          have hlog : Real.log (R / r) ≤ Real.log (R * ‖c - u‖⁻¹) := by
            rw [← div_eq_mul_inv]
            exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hR.le hcu hle)
          have hord : (0 : ℝ) ≤ (((analyticOrderAt f u).map (↑)).untop₀ : ℤ) := by
            have := hf'.divisor_nonneg u
            simp only [AnalyticOnNhd.divisor_apply hf' h1] at this
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_left hlog hord
        · simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
            Int.cast_zero, zero_mul]
          refine mul_nonneg (mod_cast hf'.divisor_nonneg u) ?_
          have hu : |r| < ‖c - u‖ := by
            rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub, not_le] at h2; exact h2
          have hu' : ‖c - u‖ ≤ |R| := by
            rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub] at h1; exact h1
          rw [habsr] at hu; rw [habsR] at hu'
          have hpos : 0 < ‖c - u‖ := hr.trans hu
          apply Real.log_nonneg
          rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
          exact hu'
      · have : u ∉ closedBall c |r| := fun h => h1
          (closedBall_subset_closedBall (by rw [habsr, habsR]; exact hrR.le) h)
        simp [h1, this]
  rw [show closedBall c r = closedBall c |r| by rw [habsr],
    finsum_mul' _ _ (hfinr.subset fun u hu => by simpa using hu)]
  have hj : ∑ᶠ u, (divisor f (closedBall c |R|) u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
      = circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
    rw [jensen]; ring
  linarith [key, hj ▸ key]

end JensenAvg

#print axioms JensenAvg.log_le_half_log_add
#print axioms JensenAvg.sum_divisor_mul_log_le
