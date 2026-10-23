/-
# The ball tower from counting integer points (round 185)

Plain statement.
* `intLattice n` is the set of points of `ℝⁿ` with whole-number coordinates (`mem_intLattice`).
  Its covolume (the volume of one unit cell) is `1` (`covolume_intLattice`).
* `latticeCount n R` counts the whole-number points `v` with `√(v₁² + … + vₙ²) ≤ R`: the lattice
  ball of radius `R`.
* **The counting route (`count_div_pow_tendsto_ballVol`):** `latticeCount n R / Rⁿ → ballVol n` as
  `R → ∞`, where `ballVol n = √π ^ n / Γ(n/2 + 1)` (BallTower.lean). Only whole numbers go in; the
  Gamma function comes out.
* Consequently the counted volume is largest in dimension 5 (`counted_volume_max_five`).

The counting asymptotic is Mathlib's `ZLattice.covolume.tendsto_card_le_div` (lattice points in a
dilated region, via box-integral Riemann sums), and the unit-ball volume is Mathlib's
`MeasureTheory.volume_sum_rpow_le` (via Gaussian integrals). This file specialises both to `ℤⁿ` and
the round ball, and checks every hypothesis (bounded, measurable, null boundary, covolume 1).
-/
import BallTower

open Real Filter Topology Metric MeasureTheory Submodule

namespace BallTower

variable (n : ℕ)

/-- The whole-number lattice `ℤⁿ ⊂ ℝⁿ`. -/
noncomputable abbrev intLattice : Submodule ℤ (Fin n → ℝ) :=
  span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

/-- Its points are exactly the vectors with whole-number coordinates. -/
theorem mem_intLattice (x : Fin n → ℝ) : x ∈ intLattice n ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = x i := by
  unfold intLattice
  rw [Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

theorem covolume_intLattice : ZLattice.covolume (intLattice n) = 1 := by
  rw [ZLattice.covolume_eq_det (intLattice n) ((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ)]
  have : Matrix.of ((↑) ∘ ((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Module.Basis.restrictScalars_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one, abs_one]

/-- The Euclidean length `√(Σ xᵢ²)`, written the way Mathlib's volume formula writes it. -/
noncomputable def eLen (x : Fin n → ℝ) : ℝ := (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

lemma eLen_nonneg (x : Fin n → ℝ) : 0 ≤ eLen n x := Real.rpow_nonneg (by positivity) _

lemma eLen_smul (x : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) : eLen n (r • x) = r * eLen n x := by
  unfold eLen
  have h1 : ∀ i, |(r • x) i| ^ (2 : ℝ) = r ^ (2 : ℝ) * |x i| ^ (2 : ℝ) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr, Real.mul_rpow hr (abs_nonneg _)]
  simp_rw [h1, ← Finset.mul_sum]
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hr]
  norm_num

lemma continuous_eLen : Continuous (eLen n) := by
  unfold eLen
  refine Continuous.rpow_const ?_ (fun _ => Or.inr (by norm_num))
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).abs).rpow_const (fun _ => Or.inr (by norm_num))

lemma abs_le_eLen (x : Fin n → ℝ) (i : Fin n) : |x i| ≤ eLen n x := by
  unfold eLen
  have hle : |x i| ^ (2 : ℝ) ≤ ∑ j, |x j| ^ (2 : ℝ) :=
    Finset.single_le_sum (f := fun j => |x j| ^ (2 : ℝ)) (fun j _ => by positivity) (Finset.mem_univ i)
  calc |x i| = (|x i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul (abs_nonneg _)]; norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hle (by norm_num)

/-- The number of whole-number points in the ball of radius `R`. -/
noncomputable def latticeCount (R : ℝ) : ℕ :=
  Nat.card ({x : Fin n → ℝ | eLen n x ≤ R} ∩ (intLattice n : Set (Fin n → ℝ)) : Set (Fin n → ℝ))

section
variable [NeZero n]

private lemma volume_unit : volume {x : Fin n → ℝ | eLen n x ≤ 1} = ENNReal.ofReal (ballVol n) := by
  have := MeasureTheory.volume_sum_rpow_le (Fin n) (p := 2) (by norm_num) 1
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul] at this
  unfold eLen
  rw [this]
  congr 1
  unfold ballVol
  have hG : Real.Gamma (1 / 2 + 1) = √π / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  rw [hG, show (2 : ℝ) * (√π / 2) = √π by ring]

private lemma volume_unit_lt : volume {x : Fin n → ℝ | eLen n x < 1} = ENNReal.ofReal (ballVol n) := by
  have := MeasureTheory.volume_sum_rpow_lt (Fin n) (p := 2) (by norm_num) 1
  have h2 := MeasureTheory.volume_sum_rpow_le (Fin n) (p := 2) (by norm_num) 1
  unfold eLen
  rw [this, ← h2]
  have := volume_unit n
  unfold eLen at this
  exact this

private lemma frontier_null : volume (frontier {x : Fin n → ℝ | eLen n x ≤ 1}) = 0 := by
  have hclosed : IsClosed {x : Fin n → ℝ | eLen n x ≤ 1} :=
    isClosed_le (continuous_eLen n) continuous_const
  have hopen : IsOpen {x : Fin n → ℝ | eLen n x < 1} :=
    isOpen_lt (continuous_eLen n) continuous_const
  have hsub : frontier {x : Fin n → ℝ | eLen n x ≤ 1} ⊆
      {x | eLen n x ≤ 1} \ {x | eLen n x < 1} := by
    rw [frontier, hclosed.closure_eq]
    exact Set.sdiff_subset_sdiff_right
      (hopen.subset_interior_iff.mpr (fun x (hx : eLen n x < 1) => le_of_lt hx))
  refine measure_mono_null hsub ?_
  have hBA : {x : Fin n → ℝ | eLen n x < 1} ⊆ {x : Fin n → ℝ | eLen n x ≤ 1} :=
    fun x (hx : eLen n x < 1) => le_of_lt hx
  rw [measure_sdiff hBA hopen.measurableSet.nullMeasurableSet
    (by rw [volume_unit_lt]; exact ENNReal.ofReal_ne_top), volume_unit, volume_unit_lt, tsub_self]

omit [NeZero n] in
private lemma bounded_unit : Bornology.IsBounded {x : Fin n → ℝ | eLen n x ≤ 1} := by
  refine (isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  exact (abs_le_eLen n x i).trans hx

/-- **Counting integer points gives the ball tower.** `#{v ∈ ℤⁿ : ‖v‖ⁿ ≤ c} / c → ballVol n`. -/
theorem count_div_tendsto_ballVol :
    Tendsto (fun c : ℝ => (Nat.card (↥(({x : Fin n → ℝ | x ∈ Set.univ ∧ eLen n x ^ n ≤ c} :
      Set (Fin n → ℝ)) ∩ (intLattice n : Set (Fin n → ℝ)))) : ℝ) / c) atTop (𝓝 (ballVol n)) := by
  have hn : n ≠ 0 := NeZero.ne n
  have hset : {x : Fin n → ℝ | x ∈ Set.univ ∧ eLen n x ^ n ≤ 1} = {x | eLen n x ≤ 1} := by
    ext x
    simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq]
    exact pow_le_one_iff_of_nonneg (eLen_nonneg n x) hn
  have key := ZLattice.covolume.tendsto_card_le_div (intLattice n) (X := Set.univ)
    (F := fun x => eLen n x ^ n) (fun _ _ _ _ => Set.mem_univ _)
    (fun x r hr => by simp only [eLen_smul n x hr, mul_pow, Fintype.card_fin])
    (by rw [hset]; exact bounded_unit n)
    (by rw [hset]; exact measurableSet_le (continuous_eLen n).measurable measurable_const)
    (by rw [hset]; exact frontier_null n)
  rw [hset, covolume_intLattice, div_one, measureReal_def, volume_unit,
    ENNReal.toReal_ofReal (ballVol_pos n).le] at key
  exact key

/-- **Same statement by radius:** `latticeCount n R / Rⁿ → √π^n / Γ(n/2+1)` as `R → ∞`. -/
theorem count_div_pow_tendsto_ballVol :
    Tendsto (fun R : ℝ => (latticeCount n R : ℝ) / R ^ n) atTop (𝓝 (ballVol n)) := by
  have hn : n ≠ 0 := NeZero.ne n
  refine ((count_div_tendsto_ballVol n).comp (tendsto_pow_atTop hn)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  have hset : ({x : Fin n → ℝ | x ∈ Set.univ ∧ eLen n x ^ n ≤ R ^ n} : Set (Fin n → ℝ)) =
      {x | eLen n x ≤ R} := by
    ext x
    simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq]
    exact pow_le_pow_iff_left₀ (eLen_nonneg n x) hR hn
  simp only [Function.comp_apply, latticeCount, hset]

end

/-- The counted volume (the limit of `latticeCount n R / Rⁿ`) is largest in dimension 5. -/
theorem counted_volume_max_five (m : ℕ) [NeZero m] (hm : m ≠ 5) :
    ∃ Vm V5 : ℝ, Tendsto (fun R : ℝ => (latticeCount m R : ℝ) / R ^ m) atTop (𝓝 Vm) ∧
      Tendsto (fun R : ℝ => (latticeCount 5 R : ℝ) / R ^ 5) atTop (𝓝 V5) ∧ Vm < V5 :=
  ⟨ballVol m, ballVol 5, count_div_pow_tendsto_ballVol m, count_div_pow_tendsto_ballVol 5,
    ballVol_lt_five m hm⟩

end BallTower
