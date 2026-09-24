import Mathlib
import StripConv

/-! # RH from `L²` closeness to Riemann's kernel

Riemann's formula `Φ̂ = Ξ/2` on all of `ℂ` (RiemannKernel.lean) discharges `KernelApprox` for `φ_n = Φ`
whenever `a_n → ∞` (`kernelApprox_RPhi`), so `rh_of_close_RPhi` derives RH from the `L²` closeness
hypothesis alone. -/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace Pilot1ca

/-- **`KernelApprox` holds for Riemann's kernel**, for any supports `a_n → ∞`. -/
theorem kernelApprox_RPhi {a : ℕ → ℝ} (hlim : Tendsto a atTop atTop) :
    KernelApprox a fun _ => RPhi := by
  refine ⟨fun _ => memLp_RPhi, 1 / 2, by norm_num, ?_⟩
  have hsub : stripSet ⊆ closedStrip 1 := fun z hz => by
    simp only [stripSet, Set.mem_ofPred_eq] at hz
    simp only [closedStrip, Set.mem_ofPred_eq]; linarith
  have h := (tendstoUniformlyOn_ghatC_RPhi 1 hlim).mono hsub
  have h2 : TendstoUniformlyOn (fun n z => ghatC RPhi (a n) z) (fun z => 1 / 2 * Xi z) atTop stripSet :=
    h.congr_right fun z _ => by rw [RPhiHat_eq]; ring
  exact h2.tendstoLocallyUniformlyOn

/-- **RH from `L²` closeness to Riemann's kernel**, with no unproved input other than the closeness:
if `a_n → ∞` and `√(2a_n) e^{b a_n} ‖σ_n·topGS(a_n) − Φ‖ → 0` for every `b < ½` (some signs and
scalings `σ_n ≠ 0`), the Riemann hypothesis holds. -/
theorem rh_of_close_RPhi {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hlim : Tendsto a atTop atTop)
    {σ : ℕ → ℝ} (hσ : ∀ n, σ n ≠ 0)
    (hclose : ∀ b < 1 / 2, Tendsto (fun n => Real.sqrt (2 * a n) * Real.exp (a n * b)
      * Real.sqrt (normSq fun t => σ n * topGS (a n) t - RPhi t)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  rh_of_close_top ha (kernelApprox_RPhi hlim) hσ hclose

end Pilot1ca

#print axioms Pilot1ca.kernelApprox_RPhi
#print axioms Pilot1ca.rh_of_close_RPhi
