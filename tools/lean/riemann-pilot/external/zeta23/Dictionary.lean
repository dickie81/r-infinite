import SlogZeta
import ToneHyperbola
import ExplicitBridge
import GroundState

/-! # The zeta23 ↔ pilot dictionary (round 248)

`Zeta23.mu τ = (psiRe τ − log π)/(2π)`, `weilConst = 2π·mu 0`, `sigmaW a r = 2π(mu r + PX (e^{2a}) r)`, `ToneHyperbola.stirl q γ = π·N₀(qγ)/q`, and Stirling for the tone phase.
-/

open Real

namespace Dictionary

/-! ### B1. ToneHyperbola's leading Stirling phase is T1ca's main term `N₀`, rescaled. -/
theorem stirl_eq_N0 {q γ : ℝ} (hq : 0 < q) (hγ : 0 < γ) :
    ToneHyperbola.stirl q γ = π * Pilot1ca.N0 (q * γ) / q := by
  unfold ToneHyperbola.stirl Pilot1ca.N0
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hq' : q ≠ 0 := hq.ne'
  have h1 : Real.log (q * γ / (2 * π * Real.exp 1)) = Real.log (q * γ / (2 * π)) - 1 := by
    rw [← div_div, Real.log_div (by positivity) he, Real.log_exp]
  rw [h1]
  field_simp

/-! ### B2. zeta23's density `μ` is the pilot's archimedean symbol: `2πμ = ψ_Re − log π`. -/
theorem mu_eq_psiRe (τ : ℝ) : Zeta23.mu τ = (Pilot1ca.psiRe τ - Real.log π) / (2 * π) := by
  unfold Zeta23.mu Pilot1ca.psiRe Pilot1ca.zB
  ring

theorem weilConst_eq_two_pi_mu_zero : Pilot1ca.weilConst = 2 * π * Zeta23.mu 0 := by
  rw [mu_eq_psiRe]
  unfold Pilot1ca.weilConst Pilot1ca.psiRe Pilot1ca.zB
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  field_simp

/-! ### B3. The pilot's Weil symbol is zeta23's `2π(μ + P_X)` at `X = e^{2a}`. -/
theorem sigmaW_eq (a r : ℝ) :
    Pilot1ca.sigmaW a r = 2 * π * (Zeta23.mu r + Zeta23.PX (Real.exp (2 * a)) r) := by
  have hset : Finset.range (Pilot1ca.primeCut a) =
      insert 0 (Finset.Ioc 0 ⌊Real.exp (2 * a)⌋₊) := by
    ext n
    simp only [Pilot1ca.primeCut, Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  unfold Pilot1ca.sigmaW Zeta23.PX
  rw [hset, Finset.sum_insert (by simp), mu_eq_psiRe]
  simp only [ArithmeticFunction.map_zero, zero_div, zero_mul, zero_add]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### B4. The true `θ'(γ) = π μ(γ)` is ToneHyperbola's idealised phase derivative up to `O(γ⁻²)`
(zeta23's Stirling, the "Stirling error term" that ToneHyperbola's header lists as not formalised). -/
theorem tone_theta_stirling : ∃ C : ℝ, ∀ γ : ℝ, 1 ≤ γ → ∃ d : ℝ,
    HasDerivAt (ToneHyperbola.stirl 1) d γ ∧ |π * Zeta23.mu γ - d| ≤ C / γ ^ 2 := by
  obtain ⟨Cs, hCs⟩ := Zeta23.gammaFacts.stirling
  refine ⟨π * |Cs|, fun γ hγ => ⟨_, ToneHyperbola.stirling_deriv one_pos (by linarith), ?_⟩⟩
  have hγ0 : 0 < γ := by linarith
  have h := hCs γ (by rw [abs_of_pos hγ0]; exact hγ)
  rw [abs_of_pos hγ0] at h
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have e : π * Zeta23.mu γ - Real.log (1 * γ / (2 * π)) / 2 =
      π * (Zeta23.mu γ - 1 / (2 * π) * Real.log (γ / (2 * π))) := by
    rw [one_mul]; field_simp
  rw [e, abs_mul, abs_of_pos Real.pi_pos]
  have h2 : Cs / γ ^ 2 ≤ |Cs| / γ ^ 2 :=
    div_le_div_of_nonneg_right (le_abs_self Cs) (by positivity)
  calc π * |Zeta23.mu γ - 1 / (2 * π) * Real.log (γ / (2 * π))| ≤ π * (|Cs| / γ ^ 2) :=
        mul_le_mul_of_nonneg_left (h.trans h2) Real.pi_pos.le
    _ = π * |Cs| / γ ^ 2 := by ring

end Dictionary

#print axioms Dictionary.stirl_eq_N0
#print axioms Dictionary.mu_eq_psiRe
#print axioms Dictionary.weilConst_eq_two_pi_mu_zero
#print axioms Dictionary.sigmaW_eq
#print axioms Dictionary.tone_theta_stirling
