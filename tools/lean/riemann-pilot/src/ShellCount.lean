import Mathlib
import BohrSphere
import ShortPrimes
import DensityCore

/-! # Zero density as counts outside shells around the Bohr sphere (round 400)

Round 391's Bohr lift puts a zero `ρ` on the unit sphere of `ℂ^F` exactly when `Re ρ = ½`, and the radius is
strictly decreasing in `Re ρ`. So the zeros counted by `NX w T` (`|γ| ≤ T`, `β ≥ ½ + w`, one per pair `ρ`, `1 − ρ`)
are exactly the pairs whose Bohr vectors lie outside the open shell between the radii at `½ + w` and `½ − w`.

* **`le_im_iff_outside`**, **`le_im_iff_outside_refl`**: the pair `i` is counted by `NX w T` if and only if its zero
  `ρ` with `β ≥ ½` (`rhoS i`) has radius at most the radius at `½ + w`, if and only if the reflection `1 − ρ̄` of `ρ`
  in the line has radius at least the radius at `½ − w`, for every nonempty finite set `F` of primes. The radius
  depends only on the real part (`norm_vF_eq_of_re_eq`), so `1 − ρ̄` has the radius of the pair's other zero `1 − ρ`.
* **`NX_eq_ncard_outside`**: `NX w T` is the number of pairs up to height `T` outside that shell.
* **`ncard_outside_le`**: a density estimate `DensityXi A B` bounds that number by `C T^{A(½−w)}(log T)^B`.
* **`tendsto_outside_div`**: if moreover `A(½ − w) < 1` and the total number of pairs up to height `T` is at least
  `cT` for large `T`, the proportion of pairs outside the shell tends to `0`.

Not proved: that proportion for every `w > 0` (the theorem of Bohr and Landau); with the stack's
`A = 4(1+δ)` the condition `A(½ − w) < 1` holds only for `w > ¼` (`external/zeta23/ShellDensity.lean`).
-/

open Real Filter Topology Complex BohrSphere

noncomputable section

namespace ShellCount

open ShortWeil Pilot1ca Pilot1bt

/-- The zero of the pair `i` with `β ≥ ½`: `βs i + i·γs i`. -/
def rhoS (i : ZeroIdx (sqF Xi)) : ℂ := (βs i : ℂ) + (γs i : ℝ) * I

lemma rhoS_re (i : ZeroIdx (sqF Xi)) : (rhoS i).re = 1 / 2 + |(tau i).im| := by
  simp [rhoS, βs]

/-- The radius is strictly decreasing in `Re s`, as an equivalence. -/
lemma norm_vF_le_iff {F : Finset Nat.Primes} (hF : F.Nonempty) (s s' : ℂ) :
    ‖vF F s‖ ≤ ‖vF F s'‖ ↔ s'.re ≤ s.re := by
  constructor
  · intro h
    by_contra hc
    exact absurd h (not_le.2 (norm_vF_lt_norm_vF hF (lt_of_not_ge hc)))
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (norm_vF_lt_norm_vF hF h).le
    · exact (norm_vF_eq_of_re_eq F h.symm).le

/-- **The pair `i` lies outside the shell of half-width `w`**: `w ≤ |Im τ|` if and only if its zero with `β ≥ ½`
has radius at most the radius at `½ + w`. -/
theorem le_im_iff_outside {F : Finset Nat.Primes} (hF : F.Nonempty) (i : ZeroIdx (sqF Xi)) (w : ℝ) :
    w ≤ |(tau i).im| ↔ ‖vF F (rhoS i)‖ ≤ ‖vF F ((1 / 2 + w : ℝ) : ℂ)‖ := by
  rw [norm_vF_le_iff hF, rhoS_re, ofReal_re]
  constructor <;> intro h <;> linarith

/-- The same through the reflection `1 − ρ̄` of `ρ = rhoS i` in the line: its radius is at least the radius at `½ − w`. -/
theorem le_im_iff_outside_refl {F : Finset Nat.Primes} (hF : F.Nonempty) (i : ZeroIdx (sqF Xi)) (w : ℝ) :
    w ≤ |(tau i).im| ↔ ‖vF F ((1 / 2 - w : ℝ) : ℂ)‖ ≤ ‖vF F (lineRefl (rhoS i))‖ := by
  rw [norm_vF_le_iff hF]
  have e : (lineRefl (rhoS i)).re = 1 - (rhoS i).re := by simp [lineRefl]
  rw [e, rhoS_re, ofReal_re]
  constructor <;> intro h <;> linarith

/-- **`NX w T` counts the pairs up to height `T` outside the shell.** -/
theorem NX_eq_ncard_outside {F : Finset Nat.Primes} (hF : F.Nonempty) (w T : ℝ) :
    NX w T = Set.ncard {i : ZeroIdx (sqF Xi) |
      |(tau i).re| ≤ T ∧ ‖vF F (rhoS i)‖ ≤ ‖vF F ((1 / 2 + w : ℝ) : ℂ)‖} := by
  unfold NX
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, le_im_iff_outside hF]

/-- `NX 0 T` counts all pairs up to height `T`. -/
theorem NX_zero_eq (T : ℝ) : NX 0 T = Set.ncard {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T} := by
  unfold NX
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, abs_nonneg, and_true]

/-- No pair has `|Im τ| ≥ ½`: every zero has `β < 1`. -/
theorem NX_eq_zero {w : ℝ} (hw : 1 / 2 ≤ w) (T : ℝ) : NX w T = 0 := by
  unfold NX
  have : {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T ∧ w ≤ |(tau i).im|} = ∅ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _
    have h := βs_lt_one i
    unfold βs at h
    linarith
  rw [this, Set.ncard_empty]

/-- **A density estimate bounds the number of pairs outside the shell.** -/
theorem ncard_outside_le {A B : ℝ} (h : DensityXi A B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Finset Nat.Primes, F.Nonempty → ∀ T : ℝ, 2 ≤ T → ∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 →
      (Set.ncard {i : ZeroIdx (sqF Xi) |
        |(tau i).re| ≤ T ∧ ‖vF F (rhoS i)‖ ≤ ‖vF F ((1 / 2 + w : ℝ) : ℂ)‖} : ℝ)
        ≤ C * T ^ (A * (1 / 2 - w)) * Real.log T ^ B := by
  obtain ⟨C, hC, hD⟩ := h
  exact ⟨C, hC, fun F hF T hT w hw0 hw1 => by rw [← NX_eq_ncard_outside hF]; exact hD T hT w hw0 hw1⟩

/-- **The proportion of pairs outside the shell tends to `0`**, given a density estimate with `A(½ − w) < 1` and
a total count of at least `cT`. -/
theorem tendsto_NX_div {A B : ℝ} (h : DensityXi A B) {w : ℝ} (hw0 : 0 ≤ w) (hw : A * (1 / 2 - w) < 1)
    (hN : ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop, c * T ≤ NX 0 T) :
    Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0) := by
  rcases le_or_gt (1 / 2) w with hw1 | hw1
  · simp only [NX_eq_zero hw1, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  obtain ⟨C, hC, hD⟩ := h
  obtain ⟨c, hc, hcT⟩ := hN
  set a := 1 - A * (1 / 2 - w) with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hlim : Tendsto (fun T : ℝ => C / c * (Real.log T ^ B / T ^ a)) atTop (𝓝 0) := by
    have := (isLittleO_log_rpow_rpow_atTop B ha0).tendsto_div_nhds_zero
    simpa using this.const_mul (C / c)
  refine squeeze_zero' (Eventually.of_forall fun T => by positivity) ?_ hlim
  filter_upwards [hcT, eventually_ge_atTop (2 : ℝ)] with T hT hT2
  have hT0 : 0 < T := by linarith
  have hNpos : 0 < (NX 0 T : ℝ) := lt_of_lt_of_le (by positivity) hT
  have hb := hD T hT2 w hw0 hw1.le
  rw [div_le_iff₀ hNpos]
  calc (NX w T : ℝ) ≤ C * T ^ (A * (1 / 2 - w)) * Real.log T ^ B := hb
    _ = C / c * (Real.log T ^ B / T ^ a) * (c * T) := by
        have hTa : T ^ (A * (1 / 2 - w)) = T ^ (1 : ℝ) / T ^ a := by
          rw [← Real.rpow_sub hT0, ha]; ring_nf
        rw [hTa, Real.rpow_one]
        field_simp
    _ ≤ C / c * (Real.log T ^ B / T ^ a) * NX 0 T := by
        have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        gcongr

/-- **The same in sphere form**: for every nonempty finite set `F` of primes, the proportion of pairs up to height
`T` whose Bohr vectors lie outside the shell between the radii at `½ + w` and `½ − w` tends to `0`. -/
theorem tendsto_outside_div {A B : ℝ} (h : DensityXi A B) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : A * (1 / 2 - w) < 1) (hN : ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop, c * T ≤ NX 0 T)
    {F : Finset Nat.Primes} (hF : F.Nonempty) :
    Tendsto (fun T => (Set.ncard {i : ZeroIdx (sqF Xi) |
        |(tau i).re| ≤ T ∧ ‖vF F (rhoS i)‖ ≤ ‖vF F ((1 / 2 + w : ℝ) : ℂ)‖} : ℝ) /
      Set.ncard {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T}) atTop (𝓝 0) := by
  have h' := tendsto_NX_div h hw0 hw hN
  refine h'.congr fun T => ?_
  rw [NX_eq_ncard_outside hF, NX_zero_eq]

end ShellCount

#print axioms ShellCount.rhoS_re
#print axioms ShellCount.norm_vF_le_iff
#print axioms ShellCount.le_im_iff_outside
#print axioms ShellCount.le_im_iff_outside_refl
#print axioms ShellCount.NX_eq_ncard_outside
#print axioms ShellCount.NX_zero_eq
#print axioms ShellCount.NX_eq_zero
#print axioms ShellCount.ncard_outside_le
#print axioms ShellCount.tendsto_NX_div
#print axioms ShellCount.tendsto_outside_div
