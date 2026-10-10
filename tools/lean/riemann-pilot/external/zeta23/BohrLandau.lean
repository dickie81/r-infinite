import Mathlib
import ShellDensity
import BohrLandauCore

/-! # Bohr and Landau's theorem in the pilot's zero family (round 402)

`src/BohrLandauCore.lean` proves the proportion statement for every `w > 0` from one input, a lower bound `c·T log T`
for the number of pairs up to height `T`. This file supplies it on zeta23's side of the layer boundary
(`ShellDensity.NX_zero_ge`, from zeta23's Riemann–von Mangoldt formula).

* **`tendsto_NX_div_pos`**: for every `w > 0`, `NX w T / NX 0 T → 0`: the proportion of zero pairs up to height `T`
  with `β ≥ ½ + w` tends to `0`.
* **`tendsto_outside_div_pos`**: the same in Bohr-shell form: for every nonempty finite set `F` of primes, the
  proportion of pairs up to height `T` whose Bohr vectors lie outside the shell of half-width `w` tends to `0`.

This extends round 400's `w > ¼` and round 401's `w > 1/6` to every `w > 0` (Bohr and Landau, 1914). A proportion
statement, for any `w`, allows a set of off-shell zeros of smaller order than the set of all zeros, so it does not bear
on RH.
-/

open Real Filter Topology Complex

noncomputable section

namespace BohrLandau

open ShortWeil Pilot1ca Pilot1bt ShellCount

/-- **For every `w > 0`, the proportion of zero pairs up to height `T` with `|β − ½| ≥ w` tends to `0`.** -/
theorem tendsto_NX_div_pos {w : ℝ} (hw : 0 < w) :
    Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0) := by
  refine BohrLandauCore.tendsto_NX_div_of_lower (c := 1 / (8 * π)) (by positivity) ?_ hw
  filter_upwards [ShellDensity.NX_zero_ge] with T hT
  calc 1 / (8 * π) * (T * Real.log T) = T * Real.log T / (8 * π) := by ring
    _ ≤ NX 0 T := hT

/-- **The same in sphere form**: for every `w > 0` and every nonempty finite set `F` of primes, the proportion of
pairs up to height `T` whose Bohr vectors lie outside the shell of half-width `w` tends to `0`. -/
theorem tendsto_outside_div_pos {w : ℝ} (hw : 0 < w) {F : Finset Nat.Primes} (hF : F.Nonempty) :
    Tendsto (fun T => (Set.ncard {i : ZeroIdx (sqF Xi) |
        |(tau i).re| ≤ T ∧ ‖BohrSphere.vF F (rhoS i)‖ ≤ ‖BohrSphere.vF F ((1 / 2 + w : ℝ) : ℂ)‖} : ℝ) /
      Set.ncard {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T}) atTop (𝓝 0) := by
  refine (tendsto_NX_div_pos hw).congr fun T => ?_
  rw [NX_eq_ncard_outside hF, NX_zero_eq]

end BohrLandau

#print axioms BohrLandau.tendsto_NX_div_pos
#print axioms BohrLandau.tendsto_outside_div_pos
