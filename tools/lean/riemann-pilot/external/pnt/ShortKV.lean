import KaiserKV
import ShortPrimes

/-! # Primes in short intervals: the Korobov–Vinogradov input (round 235)

`ShortWeil.short_primes_of_density` needs a zero-free region of width `(log T)^{−α}` with `α < 1`.
The Korobov–Vinogradov region has width `A/f(T)`, `f(T) = (log T)^{2/3}(log log T)^{1/3} ≤ 2(log T)^{3/4}`
(`fKV_le`), so `α = 3/4` (`zeroFreeXi_KV`).
-/

open Real Filter Topology

noncomputable section

namespace ShortKV

open ShortWeil KaiserKV Pilot1ca Pilot1bt

theorem four_rpow_third_le : (4 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
  have e : ((2 : ℝ) ^ (3 : ℕ)) ^ (((3 : ℕ) : ℝ)⁻¹) = 2 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h3 : ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  calc (4 : ℝ) ^ ((1 : ℝ) / 3) ≤ ((2 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 2 := by rw [h3, e]

/-- `f(T) ≤ 2(log T)^{3/4}`. -/
theorem fKV_le' {T : ℝ} (hT : Real.exp 3 ≤ T) : fKV T ≤ 2 * Real.log T ^ ((3 : ℝ) / 4) := by
  set u := Real.log T with hu
  have hu3 : 3 ≤ u := three_le_log hT
  have hu0 : 0 < u := by linarith
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have h1 : Real.log u ≤ 4 * u ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div hu0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith [show u ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * u ^ ((1 : ℝ) / 4) by ring]
  have h2 : Real.log u ^ ((1 : ℝ) / 3) ≤ 2 * u ^ ((1 : ℝ) / 12) := by
    calc Real.log u ^ ((1 : ℝ) / 3) ≤ (4 * u ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hlu h1 (by norm_num)
      _ = 4 ^ ((1 : ℝ) / 3) * u ^ ((1 : ℝ) / 12) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hu0.le]; norm_num
      _ ≤ 2 * u ^ ((1 : ℝ) / 12) :=
          mul_le_mul_of_nonneg_right four_rpow_third_le (by positivity)
  unfold fKV
  rw [← hu]
  calc u ^ ((2 : ℝ) / 3) * Real.log u ^ ((1 : ℝ) / 3) ≤ u ^ ((2 : ℝ) / 3) * (2 * u ^ ((1 : ℝ) / 12)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * (u ^ ((2 : ℝ) / 3) * u ^ ((1 : ℝ) / 12)) := by ring
    _ = 2 * u ^ ((3 : ℝ) / 4) := by rw [← Real.rpow_add hu0]; norm_num

/-- **The Korobov–Vinogradov region as `ZeroFreeXi (3/4)`.** -/
theorem zeroFreeXi_KV : ZeroFreeXi (3 / 4) := by
  obtain ⟨A, hA, -, h⟩ := abs_im_tau_le
  refine ⟨A / 2, Real.exp 3, by positivity, fun T hT i hi => ?_⟩
  have h1 := h T hT i hi
  have hf := fKV_pos hT
  have hle := fKV_le' hT
  have h2 : A / 2 / Real.log T ^ ((3 : ℝ) / 4) ≤ A / fKV T := by
    rw [div_div]; exact div_le_div_of_nonneg_left hA.le hf hle
  linarith

/-- **Primes in short intervals from a density bound**, the zero-free region supplied. -/
theorem short_primes_KV_of_density {A B : ℝ} (hA : 0 < A) (hden : DensityXi A B) {θ : ℝ}
    (h1 : 1 / 2 < θ) (h2 : 1 - 1 / A < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ :=
  short_primes_of_density hA (by norm_num) hden zeroFreeXi_KV h1 h2

end ShortKV

#print axioms ShortKV.zeroFreeXi_KV
#print axioms ShortKV.short_primes_KV_of_density
