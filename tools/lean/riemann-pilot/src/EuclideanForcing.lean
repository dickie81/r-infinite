import Mathlib
import BohrSphere

/-! # The forcing of the Euclidean unit ball (round 394)

The owner asked for the forcing of the Euclidean infinite unit ball in Lean. The forcer proved here is
self-duality: the Euclidean ball is the only set equal to its own polar, and among the `ℓ^p` balls the
polarity is Hölder conjugation, which is how round 391's reflection `s ↦ 1 − s̄` in the critical line acts on
the Bohr thresholds. Volume is not the forcer: round 393's concentration at the surface holds for the unit
ball of every norm, the cube included.

* **Self-polar uniqueness** (`innerPolar`, a definition; **`innerPolar_closedBall`**,
  **`eq_closedBall_of_innerPolar_eq`** and **`innerPolar_eq_self_iff`**): in any real inner product space, of
  any dimension, the closed unit ball is its own polar `{y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}`, and it is the only set,
  convex or not, with this property. **`ell2_innerPolar_eq_self_iff`** states it for `ℓ²(ℕ)`, the
  infinite-dimensional Euclidean space.
* **Hölder duality** (`lpBall`, a definition; **`innerPolar_lpBall`** and **`lpBall_two`**, with
  `inner_eq_sum`, `abs_sign_mul_rpow` and `sign_mul_rpow_mul`): in `ℝ^ι` with its Euclidean inner product, for
  conjugate exponents `p` and `q` the polar of the `ℓ^p` unit ball is the `ℓ^q` unit ball, and the `ℓ²` ball is
  the Euclidean closed unit ball.
* **Among the `ℓ^p` balls only `p = 2` is self-dual** (**`lpBall_eq_lpBall_two_iff`** and
  **`innerPolar_lpBall_eq_self_iff`**, with `twoPt`, `sum_twoPt` and `two_mul_rpow_le_one_iff`): in every
  dimension at least two, for `p > 0`, the `ℓ^p` ball is its own polar if and only if `p = 2`.
* **The link to the critical line** (**`innerPolar_lpBall_critExp`** and
  **`innerPolar_lpBall_critExp_eq_self_iff`**): for `0 < σ < 1` the polar of the threshold ball `ℓ^{1/σ}` of `s`
  (`z(s) ∈ ℓ^q` iff `q > 1/σ`, round 391) is the threshold ball `ℓ^{1/(1−σ)}` of the mirror image `1 − s̄`, by
  round 391's `holderConjugate_critExp`; and, for `σ > 0`, the threshold ball is its own polar, hence the
  Euclidean ball, exactly when `σ = ½`.
* **Volume is not the forcer** (**`addHaar_ball_fraction`** and **`tendsto_inner_fraction_cube`**): in every
  finite-dimensional real normed space with an additive Haar measure the ball of radius `r` holds the fraction
  `r^dim` of the unit ball, so the volume concentrates at the surface for every norm; for the sup norm, whose
  unit ball is the cube, the inner fraction `(1 − ε)ⁿ` tends to `0` exactly as for the Euclidean ball.

What this file does not prove: anything about the zeros of ζ. The Euclidean ball is forced as the self-dual
ball, and round 391 already places the critical line on its sphere; the zeros stay where rounds 391 to 393
left them, with RH equivalent to their lying on the sphere (`riemannHypothesis_iff_mem_sphere`).
-/

open Metric Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace EuclideanForcing

/-! ## Part A: the Euclidean ball is the only self-polar set -/

section Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The polar of a set: the points whose inner product with every point of the set is at most `1`. -/
def innerPolar (K : Set E) : Set E := {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}

/-- The closed unit ball is its own polar. -/
theorem innerPolar_closedBall : innerPolar (closedBall (0 : E) 1) = closedBall 0 1 := by
  ext y
  simp only [innerPolar, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  constructor
  · intro h
    by_cases hy : y = 0
    · simp [hy]
    · have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
      have h1 := h (‖y‖⁻¹ • y) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
      have e : ‖y‖⁻¹ * ‖y‖ ^ 2 = ‖y‖ := by field_simp
      linarith
  · intro hy x hx
    calc ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      _ ≤ 1 := by nlinarith [norm_nonneg x, norm_nonneg y]

/-- **Uniqueness.** A set equal to its own polar is the closed unit ball. -/
theorem eq_closedBall_of_innerPolar_eq {K : Set E} (h : innerPolar K = K) : K = closedBall 0 1 := by
  have sub : K ⊆ closedBall 0 1 := by
    intro x hx
    have hx' : x ∈ innerPolar K := h.symm ▸ hx
    have h1 := hx' x hx
    rw [real_inner_self_eq_norm_sq] at h1
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg x]
  refine Set.Subset.antisymm sub fun y hy => ?_
  rw [← h]
  intro x hx
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 (sub hx)
  have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 hy
  calc ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    _ ≤ 1 := by nlinarith [norm_nonneg x, norm_nonneg y]

/-- **The Euclidean ball is forced by self-duality**: in any real inner product space, of any
dimension, the closed unit ball is the one and only set equal to its own polar. -/
theorem innerPolar_eq_self_iff (K : Set E) : innerPolar K = K ↔ K = closedBall 0 1 :=
  ⟨eq_closedBall_of_innerPolar_eq, fun h => by rw [h]; exact innerPolar_closedBall⟩

end Polar

/-- **The infinite-dimensional case**: in `ℓ²(ℕ)` the closed unit ball is the only self-polar set. -/
theorem ell2_innerPolar_eq_self_iff (K : Set (lp (fun _ : ℕ => ℝ) 2)) :
    innerPolar K = K ↔ K = closedBall 0 1 :=
  innerPolar_eq_self_iff K

/-! ## Part B: the `ℓ^p` balls, Hölder duality, and the exponent `2` -/

section LpBall

variable {ι : Type*} [Fintype ι]

/-- The unit ball of the `ℓ^p` norm, as a subset of `ℝ^ι` with its Euclidean inner product. -/
def lpBall (p : ℝ) : Set (EuclideanSpace ℝ ι) := {x | ∑ i, |x i| ^ p ≤ 1}

lemma inner_eq_sum (x y : EuclideanSpace ℝ ι) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-- The `ℓ²` ball is the Euclidean closed unit ball. -/
theorem lpBall_two : (lpBall 2 : Set (EuclideanSpace ℝ ι)) = closedBall 0 1 := by
  ext x
  simp only [lpBall, Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  have h : ∑ i, |x i| ^ (2 : ℝ) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_two, sq_abs]
  rw [h, pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

lemma abs_sign_mul_rpow (t : ℝ) {q : ℝ} (hq : 1 < q) :
    |(SignType.sign t : ℝ)| * |t| ^ (q - 1) = |t| ^ (q - 1) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.zero_rpow (by linarith : q - 1 ≠ 0)]
  · rcases lt_or_gt_of_ne ht with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]

lemma sign_mul_rpow_mul (t : ℝ) {q : ℝ} (hq : 1 < q) :
    (SignType.sign t : ℝ) * |t| ^ (q - 1) * t = |t| ^ q := by
  rw [mul_assoc, mul_comm (|t| ^ (q - 1)) t, ← mul_assoc, sign_mul_self]
  rcases eq_or_ne t 0 with rfl | ht
  · simp [Real.zero_rpow (by linarith : q ≠ 0)]
  · have hpos : 0 < |t| := abs_pos.2 ht
    rw [Real.rpow_sub_one hpos.ne' q]
    field_simp

/-- **Hölder duality.** For conjugate exponents the polar of the `ℓ^p` ball is the `ℓ^q` ball. -/
theorem innerPolar_lpBall {p q : ℝ} (hpq : p.HolderConjugate q) :
    innerPolar (lpBall p : Set (EuclideanSpace ℝ ι)) = lpBall q := by
  have hp := hpq.pos
  have hq1 : 1 < q := hpq.symm.lt
  have hconj : (q - 1) * p = q := by
    have e := hpq.inv_add_inv_eq_one
    have hq0 := hpq.symm.pos
    field_simp at e
    nlinarith
  ext y
  constructor
  · intro hy
    simp only [lpBall, Set.mem_ofPred_eq]
    set S := ∑ i, |y i| ^ q with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
    rcases hS0.lt_or_eq with hSpos | hS
    swap
    · rw [← hS]; exact zero_le_one
    set c := S ^ (1 / p) with hc
    have hcpos : 0 < c := Real.rpow_pos_of_pos hSpos _
    let x : EuclideanSpace ℝ ι :=
      WithLp.toLp 2 fun i => (SignType.sign (y i) : ℝ) * |y i| ^ (q - 1) / c
    have hxi : ∀ i, |x i| = |y i| ^ (q - 1) / c := by
      intro i
      show |(SignType.sign (y i) : ℝ) * |y i| ^ (q - 1) / c| = _
      rw [abs_div, abs_mul, abs_of_pos hcpos, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        abs_sign_mul_rpow _ hq1]
    have hxp : ∑ i, |x i| ^ p = 1 := by
      simp_rw [hxi]
      have : ∀ i, (|y i| ^ (q - 1) / c) ^ p = |y i| ^ q / S := by
        intro i
        rw [Real.div_rpow (Real.rpow_nonneg (abs_nonneg _) _) hcpos.le,
          ← Real.rpow_mul (abs_nonneg _), hconj, hc, ← Real.rpow_mul hSpos.le,
          one_div_mul_cancel hp.ne', Real.rpow_one]
      simp_rw [this, ← Finset.sum_div, ← hSdef, div_self hSpos.ne']
    have hxy : ⟪x, y⟫ = S ^ (1 / q) := by
      rw [inner_eq_sum]
      have : ∀ i, x i * y i = |y i| ^ q / c := by
        intro i
        show (SignType.sign (y i) : ℝ) * |y i| ^ (q - 1) / c * y i = _
        rw [div_mul_eq_mul_div, sign_mul_rpow_mul _ hq1]
      simp_rw [this, ← Finset.sum_div, ← hSdef, hc]
      have e1 : 1 / q = 1 - 1 / p := by
        have e := hpq.inv_add_inv_eq_one
        rw [one_div, one_div]
        linarith
      rw [e1, Real.rpow_sub hSpos, Real.rpow_one]
    have h1 := hy x (by simp only [lpBall, Set.mem_ofPred_eq]; rw [hxp])
    rw [hxy] at h1
    by_contra hgt
    have := Real.one_lt_rpow (lt_of_not_ge hgt) (one_div_pos.2 hpq.symm.pos)
    linarith
  · intro hy x hx
    simp only [lpBall, Set.mem_ofPred_eq] at hx hy
    rw [inner_eq_sum]
    calc ∑ i, x i * y i
        ≤ (∑ i, |x i| ^ p) ^ (1 / p) * (∑ i, |y i| ^ q) ^ (1 / q) :=
          Real.inner_le_Lp_mul_Lq Finset.univ _ _ hpq
      _ ≤ 1 * 1 := mul_le_mul
          (Real.rpow_le_one (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) hx
            (one_div_pos.2 hp).le)
          (Real.rpow_le_one (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) hy
            (one_div_pos.2 hpq.symm.pos).le)
          (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _)
          zero_le_one
      _ = 1 := one_mul 1

/-- **The reflection in the critical line acts as the polarity.** For `0 < σ < 1` the polar of the
threshold ball `ℓ^{1/σ}` of `s` (round 391: `z(s) ∈ ℓ^q` iff `q > 1/σ`) is the threshold ball
`ℓ^{1/(1−σ)}` of its mirror image `1 − s̄`. -/
theorem innerPolar_lpBall_critExp {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    innerPolar (lpBall (1 / σ) : Set (EuclideanSpace ℝ ι)) = lpBall (1 / (1 - σ)) :=
  innerPolar_lpBall (BohrSphere.holderConjugate_critExp h0 h1)

section TwoPoint

variable [DecidableEq ι]

/-- The vector with the value `c` at `i` and at `j`, and `0` elsewhere. -/
def twoPt (i j : ι) (c : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun k => if k = i ∨ k = j then c else 0

lemma sum_twoPt {i j : ι} (hij : i ≠ j) {c r : ℝ} (hc : 0 ≤ c) (hr : 0 < r) :
    ∑ k, |twoPt i j c k| ^ r = 2 * c ^ r := by
  rw [Fintype.sum_eq_add i j hij]
  · simp [twoPt, abs_of_nonneg hc]
    ring
  · intro k ⟨hki, hkj⟩
    simp [twoPt, hki, hkj, Real.zero_rpow hr.ne']

lemma two_mul_rpow_le_one_iff (a : ℝ) : 2 * (2 : ℝ) ^ a ≤ 1 ↔ a ≤ -1 := by
  rw [show (2 : ℝ) * 2 ^ a = 2 ^ (1 + a) by rw [Real.rpow_add two_pos, Real.rpow_one]]
  conv_lhs => rw [show (1 : ℝ) = 2 ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
  rw [Real.rpow_le_rpow_left_iff one_lt_two]
  constructor <;> intro h <;> linarith

/-- In at least two dimensions the `ℓ^p` ball is the Euclidean ball only for `p = 2`. -/
theorem lpBall_eq_lpBall_two_iff {i j : ι} (hij : i ≠ j) {p : ℝ} (hp : 0 < p) :
    (lpBall p : Set (EuclideanSpace ℝ ι)) = lpBall 2 ↔ p = 2 := by
  constructor
  · intro h
    have hle : p ≤ 2 := by
      have hc : (0 : ℝ) ≤ 2 ^ (-1 / p) := Real.rpow_nonneg zero_le_two _
      have hmem : twoPt i j ((2 : ℝ) ^ (-1 / p)) ∈ (lpBall p : Set (EuclideanSpace ℝ ι)) := by
        simp only [lpBall, Set.mem_ofPred_eq]
        rw [sum_twoPt hij hc hp, ← Real.rpow_mul zero_le_two, div_mul_cancel₀ _ hp.ne',
          two_mul_rpow_le_one_iff]
      rw [h] at hmem
      simp only [lpBall, Set.mem_ofPred_eq] at hmem
      rw [sum_twoPt hij hc two_pos, ← Real.rpow_mul zero_le_two, two_mul_rpow_le_one_iff] at hmem
      have h2 : 1 ≤ 2 / p := by
        have : -1 / p * 2 = -(2 / p) := by ring
        linarith
      rwa [le_div_iff₀ hp, one_mul] at h2
    have hge : 2 ≤ p := by
      have hc : (0 : ℝ) ≤ 2 ^ (-1 / 2 : ℝ) := Real.rpow_nonneg zero_le_two _
      have hmem : twoPt i j ((2 : ℝ) ^ (-1 / 2 : ℝ)) ∈ (lpBall 2 : Set (EuclideanSpace ℝ ι)) := by
        simp only [lpBall, Set.mem_ofPred_eq]
        rw [sum_twoPt hij hc two_pos, ← Real.rpow_mul zero_le_two, two_mul_rpow_le_one_iff]
        norm_num
      rw [← h] at hmem
      simp only [lpBall, Set.mem_ofPred_eq] at hmem
      rw [sum_twoPt hij hc hp, ← Real.rpow_mul zero_le_two, two_mul_rpow_le_one_iff] at hmem
      linarith
    linarith
  · rintro rfl
    rfl

/-- **Among the `ℓ^p` balls, self-duality forces `p = 2`**, in every dimension at least two. -/
theorem innerPolar_lpBall_eq_self_iff {i j : ι} (hij : i ≠ j) {p : ℝ} (hp : 0 < p) :
    innerPolar (lpBall p : Set (EuclideanSpace ℝ ι)) = lpBall p ↔ p = 2 := by
  rw [innerPolar_eq_self_iff, ← lpBall_two, lpBall_eq_lpBall_two_iff hij hp]

/-- **The threshold ball is its own polar, hence Euclidean, exactly on the line.** -/
theorem innerPolar_lpBall_critExp_eq_self_iff {i j : ι} (hij : i ≠ j) {σ : ℝ} (h0 : 0 < σ) :
    innerPolar (lpBall (1 / σ) : Set (EuclideanSpace ℝ ι)) = lpBall (1 / σ) ↔ σ = 1 / 2 := by
  rw [innerPolar_lpBall_eq_self_iff hij (by positivity)]
  constructor
  · intro h
    field_simp at h
    linarith
  · rintro rfl
    norm_num

end TwoPoint

end LpBall

/-! ## Part C: volume concentration does not single out the Euclidean ball -/

/-- In every finite-dimensional real normed space with an additive Haar measure, the ball of radius
`r` holds the fraction `r^dim` of the unit ball. -/
theorem addHaar_ball_fraction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] (μ : Measure F)
    [μ.IsAddHaarMeasure] {r : ℝ} (hr : 0 < r) :
    (μ (ball (0 : F) r)).toReal / (μ (ball (0 : F) 1)).toReal = r ^ Module.finrank ℝ F := by
  rw [Measure.addHaar_ball_of_pos μ (0 : F) hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  have hpos : 0 < (μ (ball (0 : F) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ _ one_pos).ne' measure_ball_lt_top.ne
  field_simp

/-- **The cube concentrates at its surface too.** For the sup norm on `ℝⁿ`, whose unit ball is the
cube `(−1, 1)ⁿ`, the ball of radius `1 − ε` holds the fraction `(1 − ε)ⁿ → 0` of the volume. -/
theorem tendsto_inner_fraction_cube {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Tendsto (fun n : ℕ => (volume (ball (0 : Fin n → ℝ) (1 - ε))).toReal /
      (volume (ball (0 : Fin n → ℝ) 1)).toReal) atTop (𝓝 0) := by
  simp_rw [addHaar_ball_fraction volume (sub_pos.2 h1), Module.finrank_fin_fun]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

end EuclideanForcing

#print axioms EuclideanForcing.innerPolar_closedBall
#print axioms EuclideanForcing.eq_closedBall_of_innerPolar_eq
#print axioms EuclideanForcing.innerPolar_eq_self_iff
#print axioms EuclideanForcing.ell2_innerPolar_eq_self_iff
#print axioms EuclideanForcing.inner_eq_sum
#print axioms EuclideanForcing.lpBall_two
#print axioms EuclideanForcing.abs_sign_mul_rpow
#print axioms EuclideanForcing.sign_mul_rpow_mul
#print axioms EuclideanForcing.innerPolar_lpBall
#print axioms EuclideanForcing.innerPolar_lpBall_critExp
#print axioms EuclideanForcing.sum_twoPt
#print axioms EuclideanForcing.two_mul_rpow_le_one_iff
#print axioms EuclideanForcing.lpBall_eq_lpBall_two_iff
#print axioms EuclideanForcing.innerPolar_lpBall_eq_self_iff
#print axioms EuclideanForcing.innerPolar_lpBall_critExp_eq_self_iff
#print axioms EuclideanForcing.addHaar_ball_fraction
#print axioms EuclideanForcing.tendsto_inner_fraction_cube
