import Mathlib
import Zeta23.FromPNTPlus.ZetaBounds
import ShellDensity
import ShellSixthCore

/-! # For every w > 1/6, almost every zero lies within w of the critical line (round 401)

`src/ShellSixthCore.lean` proves the proportion statement from two inputs: the Euler–Maclaurin approximation
(`MeanSquareZeta.EMApprox`) and a lower bound `c·T log T` for the number of pairs up to height `T`. This file supplies
both on zeta23's side of the layer boundary.

* **`emApprox_zeta23`**: `EMApprox`, from zeta23's copy of PNT+'s `ZetaBounds` (`Zeta0EqZeta`, `ZetaBnd_aux1b`).
* **`tendsto_NX_div_sixth`**: for every `w > 1/6`, `NX w T / NX 0 T → 0`, with `ShellDensity.NX_zero_ge` as the
  lower bound.
* **`tendsto_outside_div_sixth`**: the same in Bohr-shell form: for every nonempty finite set `F` of primes, the
  proportion of pairs up to height `T` whose Bohr vectors lie outside the shell of half-width `w` tends to `0`.

This extends round 400's `w > ¼` (`ShellDensity.tendsto_NX_div_quarter`) to `w > 1/6`. Not proved: `w ≤ 1/6` (Bohr and
Landau proved every `w > 0`). A proportion statement, for any `w`, allows a set of off-shell zeros of smaller order than
the set of all zeros, so it does not bear on RH.
-/

open Real Filter Topology Complex Finset

noncomputable section

namespace ShellSixth

open ShortWeil Pilot1ca Pilot1bt ShellCount

/-- **The Euler–Maclaurin approximation of `ζ` by its partial sums** (`MeanSquareZeta.EMApprox`), from zeta23's
copy of PNT+'s `ZetaBounds`. -/
theorem emApprox_zeta23 : MeanSquareZeta.EMApprox := by
  intro σ t hσ0 ht N hN
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.im h; rw [hsim] at this; simp at this
    rw [this] at ht; norm_num at ht
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  have hEM := Zeta0EqZeta (N := N) (by omega) (by rw [hsre]; exact hσ0) hs1
  unfold riemannZeta0 at hEM
  set I0 := ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hI0
  have hsum : ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s = ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s) := by
    rw [Finset.sum_range_succ', Nat.cast_zero, Complex.zero_cpow hs0, div_zero, add_zero]
    have hmap : Ioc 0 N = (Finset.range N).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext n; simp only [mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact ⟨n - 1, by omega, by omega⟩
      · rintro ⟨m, hm, rfl⟩; omega
    rw [hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Function.Embedding.coeFn_mk]
    rw [Complex.cpow_neg, one_div]
  rw [hsum] at hEM
  have hZ : riemannZeta s - ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)
      = -(N : ℂ) ^ (1 - s) / (1 - s) + -(N : ℂ) ^ (-s) / 2 + s * I0 := by
    rw [← hEM]; ring
  rw [hZ]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ‖-(N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ (N : ℝ) ^ (1 - σ) / |t| := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega)]
    have : (1 - s).re = 1 - σ := by simp [hsre]
    rw [this]
    apply div_le_div_of_nonneg_left (by positivity) (by linarith)
    have := Complex.abs_im_le_norm (1 - s)
    simpa [hsim] using this
  have h2 : ‖-(N : ℂ) ^ (-s) / 2‖ = (N : ℝ) ^ (-σ) / 2 := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega)]; simp [hsre]
  have h3 : ‖s * I0‖ ≤ (σ + |t|) * (N : ℝ) ^ (-σ) / σ := by
    have hI := ZetaBnd_aux1b N hN (σ := σ) (t := t) hσ0
    have hsn : ‖s‖ ≤ σ + |t| := by
      rw [hs]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      simp [Complex.norm_real, abs_of_pos hσ0]
    rw [norm_mul, mul_div_assoc]
    exact mul_le_mul hsn (by rw [hI0, hs]; exact hI) (norm_nonneg _) (by positivity)
  have hA := norm_add_le (-(N : ℂ) ^ (1 - s) / (1 - s) + -(N : ℂ) ^ (-s) / 2) (s * I0)
  have hB := norm_add_le (-(N : ℂ) ^ (1 - s) / (1 - s)) (-(N : ℂ) ^ (-s) / 2)
  linarith [hA, hB, h1, h2, h3]

/-- **For every `w > 1/6`, the proportion of zero pairs up to height `T` with `|β − ½| ≥ w` tends to `0`.** -/
theorem tendsto_NX_div_sixth {w : ℝ} (hw : 1 / 6 < w) :
    Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0) := by
  refine ShellSixthCore.tendsto_NX_div_of_EMApprox emApprox_zeta23 (c := 1 / (8 * π))
    (by positivity) ?_ hw
  filter_upwards [ShellDensity.NX_zero_ge] with T hT
  calc 1 / (8 * π) * (T * Real.log T) = T * Real.log T / (8 * π) := by ring
    _ ≤ NX 0 T := hT

/-- **The same in sphere form**: for every `w > 1/6` and every nonempty finite set `F` of primes, the proportion
of pairs up to height `T` whose Bohr vectors lie outside the shell of half-width `w` tends to `0`. -/
theorem tendsto_outside_div_sixth {w : ℝ} (hw : 1 / 6 < w) {F : Finset Nat.Primes} (hF : F.Nonempty) :
    Tendsto (fun T => (Set.ncard {i : ZeroIdx (sqF Xi) |
        |(tau i).re| ≤ T ∧ ‖BohrSphere.vF F (rhoS i)‖ ≤ ‖BohrSphere.vF F ((1 / 2 + w : ℝ) : ℂ)‖} : ℝ) /
      Set.ncard {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T}) atTop (𝓝 0) := by
  refine (tendsto_NX_div_sixth hw).congr fun T => ?_
  rw [NX_eq_ncard_outside hF, NX_zero_eq]

end ShellSixth

#print axioms ShellSixth.emApprox_zeta23
#print axioms ShellSixth.tendsto_NX_div_sixth
#print axioms ShellSixth.tendsto_outside_div_sixth
