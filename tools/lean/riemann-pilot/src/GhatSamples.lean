import ZeroSwap

/-! # The Fourier coefficients of a probe are samples of `ĝ` (round 247)

`cf a g n = ĝ(−2πn/4a)/(4a)`, so Parseval on `[−2a, 2a]` is the sampled Plancherel identity `Σ_n |ĝ(πn/2a)|² = 4a‖g‖²`.
-/

open Real Complex MeasureTheory

noncomputable section

namespace GhatSamples

open Pilot1ca

theorem cf_eq_ghatC {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0) (n : ℤ) :
    cf a g n = (1 / (4 * a) : ℂ) * ghatC g a (((-(2 * π * n / (4 * a))) : ℝ) : ℂ) := by
  have hs : ∀ u, a < |u| → Complex.exp (-(2 * π * I * n * u / (4 * a))) * ((g u : ℝ) : ℂ) = 0 :=
    fun u hu => by rw [hsupp u hu]; simp
  unfold cf
  rw [integral_eq_of_supp hs (by linarith) (by linarith), ghatC_eq_integral ha hsupp]
  congr 1
  congr 1; funext u; rw [mul_comm]; congr 2; push_cast; ring

/-- **Sampled Plancherel**: `Σ_n ‖ĝ(−2πn/4a)‖² = 4a‖g‖²` for a probe. -/
theorem hasSum_ghat_samples {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) :
    HasSum (fun n : ℤ => ‖ghatC g a (((-(2 * π * n / (4 * a))) : ℝ) : ℂ)‖ ^ 2) (4 * a * normSq g) := by
  have h := hasSum_cf_sq ha (by linarith : a < 2 * a) hp.memL2 hp.supp
  have hn : ‖(1 / (4 * a) : ℂ)‖ = 1 / (4 * a) := by
    rw [show (1 / (4 * a) : ℂ) = ((1 / (4 * a) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [cf_eq_ghatC ha hp.supp, norm_mul, mul_pow, hn] at h
  have h2 := h.mul_left ((4 * a) ^ 2)
  have ha4 : (4 * a) ≠ 0 := by positivity
  convert h2 using 1
  · funext n; field_simp
  · field_simp

end GhatSamples

#print axioms GhatSamples.cf_eq_ghatC
#print axioms GhatSamples.hasSum_ghat_samples
