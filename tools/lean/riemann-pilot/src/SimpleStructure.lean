import Mathlib
import SimpleCover

/-! # The structure of a degenerate ground space

Round 48. The zero-swap of round 43 is an operation *on the ground space*. If `g` is in the ground
space and `ĝ(w) = 0` with `σ = w²` non-real, then both real parts of the Green solution
`h = (∂² + σ)⁻¹ g` (compactly supported, ĥ = −ĝ/(z² − σ), SwapRealize.lean) are again in the ground
space (`green_mem_groundSpace`). Iterating this, and using that `Q` commutes with `∂²` (the Weil
functional is a distribution applied to `f ⋆ k̃`, and `(i/2)² = −¼` is real), gives the structure
theorem of README round 48: the ground space is simple iff no ground state is `H²`-flat at the edges.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

section Green

variable {g : ℝ → ℝ} {a : ℝ} {w : ℂ}

/-- The swapped pair of a ground-space element lies in the ground space. -/
theorem swap_pair_mem (ha : 0 < a) (hg : g ∈ groundSpace a) (hw : ghatC g a w = 0)
    (hσ : (w ^ 2).im ≠ 0) : uSw g a w ∈ groundSpace a ∧ vSw g a w ∈ groundSpace a := by
  have hp : Probe a g := hg.1
  have hw0 : w ≠ 0 := by rintro rfl; apply hσ; simp
  have hac := swap_autocorr hp ha hw hw0 hσ
  have hac' : ∀ s, autocorr (vSw g a w) s + autocorr (uSw g a w) s = autocorr g s :=
    fun s => by rw [add_comm]; exact hac s
  have hu : Probe a (uSw g a w) := ⟨uSw_even hp hw, uSw_supp hp hw, memLp_uSw hp hw,
    arch_dom (memLp_uSw hp hw) (memLp_vSw hp hw) hac hp.arch⟩
  have hv : Probe a (vSw g a w) := ⟨vSw_even hp hw, vSw_supp hp hw, memLp_vSw hp hw,
    arch_dom (memLp_vSw hp hw) (memLp_uSw hp hw) hac' hp.arch⟩
  have hB : ∀ z : ℂ, z ^ 2 ≠ w ^ 2 → ghatC (uSw g a w) a z + Complex.I * ghatC (vSw g a w) a z
      = ghatC g a z * ((z ^ 2 - (starRingEnd ℂ) (w ^ 2)) / (z ^ 2 - w ^ 2)) :=
    fun z hz => swap_hat hp ha.le hw hw0 z hz
  exact split_mem_groundSpace hg hu hv hac (poleR_swap hσ hB)

/-- **Swap closure.** If `g` is in the ground space and `ĝ(w) = 0` with `w²` non-real, the real and
imaginary parts of the Green solution `h = (∂² + w²)⁻¹ g` are in the ground space. -/
theorem green_mem_groundSpace (ha : 0 < a) (hg : g ∈ groundSpace a) (hw : ghatC g a w = 0)
    (hσ : (w ^ 2).im ≠ 0) :
    (fun x => (hSw g a w x).re) ∈ groundSpace a ∧ (fun x => (hSw g a w x).im) ∈ groundSpace a := by
  obtain ⟨hu, hv⟩ := swap_pair_mem ha hg hw hσ
  set s := (w ^ 2).im
  have hc : ∀ x, ((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x
      = ((2 * s * (hSw g a w x).im : ℝ) : ℂ) + ((-2 * s * (hSw g a w x).re : ℝ) : ℂ) * Complex.I := by
    intro x
    have e1 : ((starRingEnd ℂ) (w ^ 2) - w ^ 2).re = 0 := by
      simp only [Complex.sub_re, Complex.conj_re, sub_self]
    have e2 : ((starRingEnd ℂ) (w ^ 2) - w ^ 2).im = -2 * s := by
      simp only [Complex.sub_im, Complex.conj_im, s]; ring
    apply Complex.ext
    · rw [Complex.mul_re, e1, e2]; simp
    · rw [Complex.mul_im, e1, e2]; simp
  have hre : (fun x => (hSw g a w x).re) = fun x => (-(2 * s)⁻¹) * vSw g a w x := by
    funext x
    have : vSw g a w x = -2 * s * (hSw g a w x).re := by
      rw [vSw_eq]; simp only; rw [hc x]; simp
    rw [this]; field_simp
  have him : (fun x => (hSw g a w x).im) = fun x => (2 * s)⁻¹ * (uSw g a w x + (-1) * g x) := by
    funext x
    have : uSw g a w x = g x + 2 * s * (hSw g a w x).im := by
      rw [uSw_eq]; simp only; rw [hc x]; simp
    rw [this]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hre]; exact groundSpace_fun hv _
  · rw [him]
    have := (groundSpace a).add_mem hu ((groundSpace a).smul_mem (-1) hg)
    exact groundSpace_fun (by convert this using 1) _

/-- The Green solution is not zero when `g` is not: its transform is `−ĝ/(z² − w²)`. -/
theorem hSw_hat' (hg : Probe a g) (ha : 0 ≤ a) (hw : ghatC g a w = 0) (hw0 : w ≠ 0) {z : ℂ}
    (hz : z ^ 2 ≠ w ^ 2) :
    (∫ x in (-a)..a, hSw g a w x * Complex.exp (Complex.I * z * x))
      = -(ghatC g a z / (z ^ 2 - w ^ 2)) :=
  hSw_hat hg.memL2 hg.even ha hw hw0 hz

end Green

end Pilot1ca

#print axioms Pilot1ca.swap_pair_mem
#print axioms Pilot1ca.green_mem_groundSpace
