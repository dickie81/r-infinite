import Mathlib
import LandauLaplace

/-! # Landau's theorem for Dirichlet series with nonnegative coefficients (round 221)

Landau's theorem for Laplace transforms (`LandauLaplace.landau`), applied to the counting measure on
`ℕ` with `φ(n) = log n`, is the classical theorem for Dirichlet series: **an L-series with
nonnegative coefficients is singular at the real point of its abscissa of convergence.**

* `LSeries_landau`: if `L(a, s)` converges for every real `σ > σ₀`, and near `σ₀` it agrees on
  `Re s > σ₀` with a function holomorphic on a disc around `σ₀`, it converges at some `σ < σ₀`.
* `LSeries_not_holomorphic_at_abscissa`: equivalently, if the abscissa of absolute convergence is a
  real number `x`, no function holomorphic on a disc around `x` agrees with `L(a, s)` on `Re s > x`.

Mathlib has only `ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn` (an entire
continuation is positive on the reals), which does not give convergence. The statements here use only
Mathlib's `LSeries` API and `LandauLaplace.lean`, in Mathlib style, so they can be upstreamed.
-/

open Complex MeasureTheory Filter Topology Set Metric LSeries

noncomputable section

namespace LandauLaplace

variable {a : ℕ → ℝ}

/-- The coefficients with `a 0` replaced by `0`, matching `LSeries.term`. -/
def coefL (a : ℕ → ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else a n

theorem ofReal_coefL_mul (a : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    (coefL a n : ℂ) * cexp (-s * (Real.log n : ℂ)) = term (fun n => (a n : ℂ)) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coefL]
  · simp only [coefL, hn, ↓reduceIte]
    rw [term_of_ne_zero hn, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hn), div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    rw [← Complex.natCast_log]; ring

theorem hyp_coefL (ha : ∀ n, 0 ≤ a n) : Hyp Measure.count (coefL a) (fun n => Real.log n) where
  A_nonneg := Eventually.of_forall fun n => by unfold coefL; split_ifs <;> [exact le_rfl; exact ha n]
  ph_nonneg := Eventually.of_forall fun n => Real.log_natCast_nonneg n
  A_meas := measurable_from_nat.aestronglyMeasurable
  ph_meas := measurable_from_nat.aestronglyMeasurable

theorem conv_iff (σ : ℝ) :
    Conv Measure.count (coefL a) (fun n => Real.log n) σ ↔
      LSeriesSummable (fun n => (a n : ℂ)) σ := by
  unfold Conv LSeriesSummable
  rw [integrable_count_iff, ← summable_norm_iff (f := term (fun n => (a n : ℂ)) σ)]
  refine summable_congr fun n => ?_
  rw [← ofReal_coefL_mul, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, Complex.norm_real]

theorem lap_eq_LSeries {s : ℂ} (hs : LSeriesSummable (fun n => (a n : ℂ)) s.re) :
    lap Measure.count (coefL a) (fun n => Real.log n) s = LSeries (fun n => (a n : ℂ)) s := by
  have hint : Integrable (fun n : ℕ => (coefL a n : ℂ) * cexp (-s * (Real.log n : ℂ))) Measure.count := by
    rw [integrable_count_iff]
    have h := (summable_norm_iff.2 hs)
    refine h.congr fun n => ?_
    rw [← ofReal_coefL_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    congr 2
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  unfold lap LSeries
  rw [integral_countable hint]
  refine tsum_congr fun n => ?_
  rw [Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul, ofReal_coefL_mul]

/-- **Landau's theorem for L-series with nonnegative coefficients.** -/
theorem LSeries_landau (ha : ∀ n, 0 ≤ a n) {σ₀ : ℝ}
    (hconv : ∀ σ : ℝ, σ₀ < σ → LSeriesSummable (fun n => (a n : ℂ)) σ) {η : ℝ} (hη : 0 < η)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball (σ₀ : ℂ) η))
    (hFL : ∀ s ∈ ball (σ₀ : ℂ) η, σ₀ < s.re → F s = LSeries (fun n => (a n : ℂ)) s) :
    ∃ σ < σ₀, LSeriesSummable (fun n => (a n : ℂ)) σ := by
  obtain ⟨σ, hσ, hc⟩ := landau (hyp_coefL ha) (fun σ hσ => (conv_iff σ).2 (hconv σ hσ)) hη hF
    fun s hs hsr => by rw [hFL s hs hsr, lap_eq_LSeries (hconv _ hsr)]
  exact ⟨σ, hσ, (conv_iff σ).1 hc⟩

/-- **An L-series with nonnegative coefficients is singular at the real point of its abscissa.** -/
theorem LSeries_not_holomorphic_at_abscissa (ha : ∀ n, 0 ≤ a n) {x : ℝ}
    (hx : abscissaOfAbsConv (fun n => (a n : ℂ)) = x) :
    ¬ ∃ η > 0, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (x : ℂ) η) ∧
      ∀ s ∈ ball (x : ℂ) η, x < s.re → F s = LSeries (fun n => (a n : ℂ)) s := by
  rintro ⟨η, hη, F, hF, hFL⟩
  obtain ⟨σ, hσ, hs⟩ := LSeries_landau ha (fun σ hσ => LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (by rw [hx]; exact_mod_cast hσ)) hη hF hFL
  have := hs.abscissaOfAbsConv_le
  rw [hx] at this
  exact absurd (by exact_mod_cast this : x ≤ σ) (not_le.2 hσ)

end LandauLaplace

#print axioms LandauLaplace.LSeries_landau
#print axioms LandauLaplace.LSeries_not_holomorphic_at_abscissa
