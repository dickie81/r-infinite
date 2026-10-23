import Mathlib
import BohrSphere
import DHLocateFour

/-! # A zero pair off the sphere (round 392)

Round 391 (`BohrSphere.lean`) identifies the critical line with the unit sphere of the normalised Bohr lift:
`v_F(s)` lies on the unit sphere of `ℂ^F` exactly when `Re s = ½`, strictly inside exactly when `Re s > ½`
(`norm_vF_lt_one_iff`, added in this round) and strictly outside exactly when `Re s < ½` (`one_lt_norm_vF_iff`).
None of this involves ζ: `v_F` is a map of the `s`-plane. So nothing in it can place the zeros of a function on
the sphere, and this file shows it on the Davenport–Heilbronn function `dh`, whose completion satisfies the
same reflection `Λ(1 − s) = Λ(s)` (`dh_functional_equation`, round 253).

* **`dh_zero_pair_off_sphere`**: the zero `ρ` located in round 267 (`0.7985 < Re ρ < 0.8185`, the first box of
  round 270's `dh_zeros_located_four_box`) and its mirror image `1 − ρ` (`dh_zero_symm`) are both zeros of `dh`. In every dimension `v_F(ρ)` lies strictly inside
  the unit ball and `v_F(1 − ρ)` strictly outside it, and as `N → ∞` over the primes below `N` the radius of
  `ρ` tends to `0` and that of `1 − ρ` to `∞`. Neither ever lies on the sphere.

So "every point inside the ball lies on its surface" is false in this frame, at a zero of a function with the
functional-equation symmetry, and an argument whose premises hold for `dh` as well as for ζ cannot place the
zeros of ζ on the line.
-/

open Filter Topology

namespace PsiOmega

open BohrSphere

/-- **A zero pair of the Davenport–Heilbronn function off the unit sphere.** -/
theorem dh_zero_pair_off_sphere :
    (∀ s, dhLam chi5 (1 - s) = dhLam chi5 s) ∧
    ∃ ρ : ℂ, dh ρ = 0 ∧ dh (1 - ρ) = 0 ∧ 1597 / 2000 < ρ.re ∧ ρ.re < 1637 / 2000 ∧
      (∀ F : Finset Nat.Primes, F.Nonempty → ‖vF F ρ‖ < 1 ∧ 1 < ‖vF F (1 - ρ)‖) ∧
      Tendsto (fun N => ‖vF (primesLT N) ρ‖) atTop (𝓝 0) ∧
      Tendsto (fun N => ‖vF (primesLT N) (1 - ρ)‖) atTop atTop := by
  obtain ⟨⟨ρ, h0, h1, h2, -, -⟩, -⟩ := Locate.dh_zeros_located_four_box
  have hre : 1 / 2 < ρ.re := by linarith
  have hm : dh (1 - ρ) = 0 := (dh_zero_symm (by linarith) (by linarith)).2 h0
  have hmre : (1 - ρ).re < 1 / 2 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact ⟨dh_functional_equation, ρ, h0, hm, h1, h2,
    fun F hF => ⟨(norm_vF_lt_one_iff hF).2 hre, (one_lt_norm_vF_iff hF).2 hmre⟩,
    tendsto_norm_vF_of_half_lt hre, tendsto_norm_vF_of_lt_half hmre⟩

end PsiOmega

#print axioms PsiOmega.dh_zero_pair_off_sphere
