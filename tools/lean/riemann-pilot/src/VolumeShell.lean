import Mathlib

/-! # At the limit all the volume is at the surface, and points carry no volume (round 393)

The owner wrote: "At the limit all the volume is at the surface of the infinite unit ball". That is a theorem,
proved here for the Euclidean unit ball of `ℝⁿ` with Lebesgue measure, together with the two facts that decide
what it can say about the zeros of ζ.

* **The volume** (**`volume_ball_fraction`** and **`tendsto_inner_fraction`**): the ball of radius `r ∈ (0, 1]`
  holds the fraction `rⁿ` of the volume of the unit ball, so for every `ε ∈ (0, 1)` the inner ball of radius
  `1 − ε` holds the fraction `(1 − ε)ⁿ`, which tends to `0` as `n → ∞`.
* **The inner ball is never empty** (**`zero_mem_inner_ball`**): it contains the centre in every dimension. Its
  volume tends to `0`; the set does not.
* **Points carry no volume** (**`volume_countable_eq_zero`**): in every positive dimension every countable set has
  volume `0`, wherever it lies, inside the inner ball or on the surface alike.

So the volume statement holds whatever the positions of countably many points, and it cannot place any of them.
The zeros of ζ are countable (they are isolated, ζ being meromorphic and not identically zero), and so are their
images under round 391's map `s ↦ v_F(s)` into `ℂ^F`, the Euclidean space of real dimension `2|F|`. Round 392's
`dh_zero_pair_off_sphere` holds alongside `tendsto_inner_fraction`: a zero of a function with ζ's reflection
symmetry is inside the ball in every dimension, with radius tending to `0`, while the volume concentrates at the
surface.
-/

open MeasureTheory Metric Filter Topology

namespace VolumeShell

/-- The ball of radius `r ∈ (0, 1]` holds the fraction `r^n` of the volume of the unit ball of `ℝⁿ`. -/
theorem volume_ball_fraction (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal /
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal = r ^ n := by
  rw [Measure.addHaar_ball_of_pos volume (0 : EuclideanSpace ℝ (Fin n)) hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hpos : 0 < (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  field_simp

/-- **At the limit all the volume is at the surface.** For every `ε ∈ (0, 1)` the ball of radius
`1 − ε` holds the fraction `(1 − ε)^n → 0` of the volume of the unit ball. -/
theorem tendsto_inner_fraction {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Tendsto (fun n : ℕ => (volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 - ε))).toReal /
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) atTop (𝓝 0) := by
  simp_rw [volume_ball_fraction _ (sub_pos.2 h1)]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- The inner ball is never empty: it contains the centre, in every dimension. -/
theorem zero_mem_inner_ball (n : ℕ) {ε : ℝ} (h1 : ε < 1) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (1 - ε) :=
  mem_ball_self (by linarith)

/-- **Points carry no volume.** In every positive dimension every countable set, wherever it lies, has
volume `0`, so a statement about where the volume is says nothing about a countable set. -/
theorem volume_countable_eq_zero (n : ℕ) {S : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hS : S.Countable) : volume S = 0 :=
  hS.measure_zero volume

end VolumeShell

#print axioms VolumeShell.volume_ball_fraction
#print axioms VolumeShell.tendsto_inner_fraction
#print axioms VolumeShell.zero_mem_inner_ball
#print axioms VolumeShell.volume_countable_eq_zero
