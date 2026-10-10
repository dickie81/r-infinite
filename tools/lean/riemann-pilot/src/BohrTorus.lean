import Mathlib
import Orthogonality
import Vinogradov

/-! # The Bohr torus: Vinogradov's orthogonality on the lift of a vertical line (round 399)

The owner asked for the joins of the 27 files that round 398 did not survey (the Vinogradov and exponential-sum
strand, the teeth, the angular family, the wander bound) with the geometric strand of rounds 391–398. Round 395
proved Parseval along a vertical line for prime polynomials (`Orthogonality.tendsto_mean_sq_norm_primePoly`), and
`Vinogradov` proves orthogonality on the torus (`integral_torus`, `count_eq_integral`). This file joins them through
the Bohr lift. README round 399 records the rest of the survey: the teeth already join the ball tower through
`AngularResidue` (round 243), and the Korobov–Vinogradov region gives a shell at each height
(`external/pnt/BohrKV.lean`).

* **The logarithms of distinct primes are linearly independent over `ℤ`** (**`eq_zero_of_sum_log`**, with
  `factorization_prod_pow`): unique factorisation.
* **The lift of the line runs on the torus** (`lineAngle`, a definition; **`bohr_line`**): with
  `θ_p(t) = −t log p/2π`, the Bohr coordinate of `σ + it` is `p^{−(σ+it)} = p^{−σ}·e(θ_p(t))`. Every point
  `(p^{−σ} e(α_p))_p` of that torus has squared norm `A_F(σ) = Σ_p p^{−2σ}` (**`sum_norm_sq_torus`**), the
  numerator of round 391's `‖v_F(s)‖² = A_F(Re s)/c_F`.
* **Character means along the line** (**`tendsto_mean_character`**, with `ee_lineAngle`): for every `k ∈ ℤ^F` the
  mean of `e(k·θ(t))` over `[0, T]` tends to `∫ e(k·α) dα` over the torus, which is `1` if `k = 0` and `0`
  otherwise. By linearity the same holds for every trigonometric polynomial on the torus
  (**`tendsto_mean_trigSum`**). These are the limits in Weyl's criterion; the passage from them to equidistribution
  for every continuous function is not proved here.
* **The moments along the line are the torus moments** (`torusPoly`, a definition; **`tendsto_mean_moment`**, with
  `primePoly_eq_torusPoly`, `torusPoly_pow` and `norm_pow_expand`): for every `σ`, weights `a` and `ℓ`, the mean of
  `|Σ_{p∈F} a_p p^{−(σ+it)}|^{2ℓ}` over `[0, T]` tends to `∫ |Σ_{p∈F} a_p p^{−σ} e(α_p)|^{2ℓ} dα` over the torus.
  At `ℓ = 1` round 395 computed the same limit as `Σ_p |a_p|² p^{−2σ}`.
* **The moments are a Vinogradov count** (**`integral_moment_eq_count`**, **`tendsto_mean_moment_count`**,
  **`tendsto_mean_moment_rearrangements`**): at `a = 1`, `σ = 0`, `Vinogradov.count_eq_integral` makes the
  limiting mean of `|Σ_{p∈F} p^{−it}|^{2ℓ}` the number of pairs of `ℓ`-tuples of primes of `F` that are
  rearrangements of each other.
* **Rigid at every `ℓ`, against rigid up to the dimension** (**`prod_eq_iff_map_eq`**, **`agree_not_rigid`**):
  `∏_i p_{x_i} = ∏_i p_{y_i}` if and only if the tuples are rearrangements of each other, for every `ℓ`.
  Vinogradov's additive system `Σ_i x_i^j = Σ_i y_i^j` (`1 ≤ j ≤ k`) has this property for `s ≤ k`
  (`Vinogradov.agree_iff`) and not at `s = 3`, `k = 2`: `(1, 5, 6)` and `(2, 3, 7)`.

Not proved: anything about the zeros of ζ. The moments are those of finite prime sums; ζ does not enter.
-/

open Complex Filter Topology MeasureTheory Finset
open scoped ComplexConjugate

namespace BohrTorus

open Vinogradov

/-- The `j`-th prime of `F`, in the order of `F.equivFin`. -/
noncomputable def prP (F : Finset Nat.Primes) (j : Fin F.card) : Nat.Primes := (F.equivFin.symm j : F)

/-- The same prime as a natural number. -/
noncomputable def pr (F : Finset Nat.Primes) (j : Fin F.card) : ℕ := (prP F j : ℕ)

lemma pr_prime (F : Finset Nat.Primes) (j : Fin F.card) : (pr F j).Prime := (prP F j).prop

lemma pr_injective (F : Finset Nat.Primes) : Function.Injective (pr F) := by
  intro i j h
  apply F.equivFin.symm.injective
  exact Subtype.ext (Nat.Primes.coe_nat_injective h)

/-- Reindexing a sum over `F` by `Fin F.card`. -/
lemma sum_prP {M : Type*} [AddCommMonoid M] (F : Finset Nat.Primes) (g : Nat.Primes → M) :
    ∑ j, g (prP F j) = ∑ p ∈ F, g p := by
  rw [← Finset.sum_coe_sort F g]
  exact Equiv.sum_comp F.equivFin.symm (fun p : F => g p)

/-- The exponent of `p_{j₀}` in `∏_j p_j^{a_j}` is `a_{j₀}`. -/
lemma factorization_prod_pow {K : ℕ} (P : Fin K → ℕ) (hP : ∀ j, (P j).Prime)
    (hinj : Function.Injective P) (a : Fin K → ℕ) (j₀ : Fin K) :
    (∏ j, P j ^ a j).factorization (P j₀) = a j₀ := by
  rw [Nat.factorization_prod (fun j _ => pow_ne_zero _ (hP j).ne_zero), Finsupp.finsetSum_apply]
  simp_rw [Nat.factorization_pow, (hP _).factorization]
  simp [Finsupp.single_apply, hinj.eq_iff]

/-- **The logarithms of distinct primes are linearly independent over `ℤ`** (unique factorisation). -/
theorem eq_zero_of_sum_log {K : ℕ} (P : Fin K → ℕ) (hP : ∀ j, (P j).Prime)
    (hinj : Function.Injective P) (k : Fin K → ℤ) (h : ∑ j, (k j : ℝ) * Real.log (P j) = 0) :
    k = 0 := by
  set A := ∏ j, P j ^ (k j).toNat with hAdef
  set B := ∏ j, P j ^ (-k j).toNat with hBdef
  have hA0 : 0 < A := Finset.prod_pos fun j _ => pow_pos (hP j).pos _
  have hB0 : 0 < B := Finset.prod_pos fun j _ => pow_pos (hP j).pos _
  have hlogP : ∀ (a : Fin K → ℕ), Real.log ((∏ j, P j ^ a j : ℕ) : ℝ) = ∑ j, (a j : ℝ) * Real.log (P j) := by
    intro a
    rw [Nat.cast_prod, Real.log_prod (fun j _ => by
      have := (hP j).pos
      positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hk : ∀ j, (k j : ℝ) = ((k j).toNat : ℝ) - ((-k j).toNat : ℝ) := by
    intro j
    have := Int.toNat_sub_toNat_neg (k j)
    exact_mod_cast this.symm
  have hlog : Real.log A = Real.log B := by
    rw [hAdef, hBdef, hlogP, hlogP]
    have h' := h
    simp_rw [hk, sub_mul] at h'
    rw [Finset.sum_sub_distrib] at h'
    linarith
  have hAB : A = B := by
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (by exact_mod_cast hA0))
      (Set.mem_Ioi.2 (by exact_mod_cast hB0)) hlog
    exact_mod_cast this
  funext j
  have h1 := factorization_prod_pow P hP hinj (fun j => (k j).toNat) j
  have h2 := factorization_prod_pow P hP hinj (fun j => (-k j).toNat) j
  rw [← hBdef, ← hAB, hAdef, h1] at h2
  simp only [Pi.zero_apply]
  omega

/-! ## The Bohr line on the torus: character means -/

/-- The angles of the lift of the vertical line: `θ_j(t) = −t log p_j / 2π`. -/
noncomputable def lineAngle (F : Finset Nat.Primes) (t : ℝ) (j : Fin F.card) : ℝ :=
  -(t * Real.log (pr F j)) / (2 * Real.pi)

lemma continuous_lineAngle (F : Finset Nat.Primes) (j : Fin F.card) :
    Continuous fun t => lineAngle F t j := by
  unfold lineAngle; fun_prop

lemma ee_lineAngle (F : Finset Nat.Primes) (k : Fin F.card → ℤ) (t : ℝ) :
    ee (∑ j, (k j : ℝ) * lineAngle F t j) =
      exp (((-∑ j, (k j : ℝ) * Real.log (pr F j) : ℝ) : ℂ) * t * I) := by
  have e : ∑ j, (k j : ℝ) * lineAngle F t j =
      -(t / (2 * Real.pi)) * ∑ j, (k j : ℝ) * Real.log (pr F j) := by
    unfold lineAngle
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  unfold ee
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **The character means along the Bohr line.** For every frequency vector `k ∈ ℤ^F`, the mean of the character
`e(k·θ(t))` over `[0, T]` tends to its integral over the torus: `1` if `k = 0`, else `0`. -/
theorem tendsto_mean_character (F : Finset Nat.Primes) (k : Fin F.card → ℤ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, ee (∑ j, (k j : ℝ) * lineAngle F t j))
      atTop (𝓝 (∫ α, ee (∑ j, (k j : ℝ) * α j) ∂torus F.card)) := by
  rw [integral_torus]
  simp_rw [ee_lineAngle]
  split_ifs with hk
  · subst hk
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, neg_zero, ofReal_zero,
      exp_zero, intervalIntegral.integral_const, sub_zero, real_smul, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp
  · set μ := -∑ j, (k j : ℝ) * Real.log (pr F j) with hμdef
    have hμ : μ ≠ 0 := by
      intro h0
      exact hk (eq_zero_of_sum_log (pr F) (pr_prime F) (pr_injective F) k (by linarith [h0]))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      ((tendsto_const_nhds (x := 2 / |μ|)).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [norm_mul, norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hT, id, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (Orthogonality.norm_integral_exp_mul_I_le hμ T) (inv_nonneg.2 hT.le)

/-! ## The torus polynomial and the lift of the line -/

/-- The torus polynomial `Σ_{p∈F} a_p p^{−σ} e(α_p)`. -/
noncomputable def torusPoly (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ : ℝ) (α : Fin F.card → ℝ) :
    ℂ :=
  ∑ j, a (prP F j) * (((pr F j : ℝ) ^ (-σ) : ℝ) : ℂ) * ee (α j)

lemma ee_lineAngle_one (F : Finset Nat.Primes) (t : ℝ) (j : Fin F.card) :
    ee (lineAngle F t j) = exp ((-Real.log (pr F j) : ℝ) * t * I) := by
  unfold ee lineAngle
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **The Bohr lift of the line `Re s = σ` runs on the torus**: `p_j^{−(σ+it)} = p_j^{−σ}·e(θ_j(t))`. -/
theorem bohr_line (F : Finset Nat.Primes) (σ t : ℝ) (j : Fin F.card) :
    BohrSphere.bohr ((σ : ℂ) + t * I) (prP F j) = (((pr F j : ℝ) ^ (-σ) : ℝ) : ℂ) * ee (lineAngle F t j) := by
  rw [BohrSphere.bohr, Orthogonality.natCast_cpow_line, ee_lineAngle_one]
  rfl

/-- The prime polynomial on the line is the torus polynomial at the angles of the line. -/
theorem primePoly_eq_torusPoly (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ t : ℝ) :
    Orthogonality.primePoly F a σ t = torusPoly F a σ (lineAngle F t) := by
  unfold Orthogonality.primePoly torusPoly
  rw [← sum_prP F (fun p => a p * ((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * I)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := bohr_line F σ t j
  rw [BohrSphere.bohr] at h
  rw [h, mul_assoc]

/-- **Every point of the torus has the same norm**: `Σ_j |p_j^{−σ} e(α_j)|² = A_F(σ)`. -/
theorem sum_norm_sq_torus (F : Finset Nat.Primes) (σ : ℝ) (α : Fin F.card → ℝ) :
    ∑ j, ‖(((pr F j : ℝ) ^ (-σ) : ℝ) : ℂ) * ee (α j)‖ ^ 2 = BohrSphere.bohrSqSum F σ := by
  unfold BohrSphere.bohrSqSum
  rw [← sum_prP F (fun p => ((p : ℕ) : ℝ) ^ (-(2 * σ)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp : (0 : ℝ) ≤ (pr F j : ℝ) := Nat.cast_nonneg _
  rw [norm_mul, norm_ee, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp _),
    ← Real.rpow_natCast, ← Real.rpow_mul hp]
  congr 1
  push_cast
  ring

/-! ## Means of trigonometric sums along the line -/

/-- **For every trigonometric polynomial on the torus, the mean along the Bohr line tends to the integral
over the torus.** -/
theorem tendsto_mean_trigSum (F : Finset Nat.Primes) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (k : ι → Fin F.card → ℤ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..T, ∑ i ∈ s, c i * ee (∑ j, (k i j : ℝ) * lineAngle F t j)) atTop
      (𝓝 (∫ α, ∑ i ∈ s, c i * ee (∑ j, (k i j : ℝ) * α j) ∂torus F.card)) := by
  have hcont : ∀ i, Continuous fun t => ee (∑ j, (k i j : ℝ) * lineAngle F t j) := fun i =>
    continuous_ee.comp (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_lineAngle F j))
  have e1 : (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..T, ∑ i ∈ s, c i * ee (∑ j, (k i j : ℝ) * lineAngle F t j)) =
      fun T : ℝ => ∑ i ∈ s, c i * ((T : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..T, ee (∑ j, (k i j : ℝ) * lineAngle F t j)) := by
    funext T
    have hint : ∀ i ∈ s, IntervalIntegrable
        (fun t => c i * ee (∑ j, (k i j : ℝ) * lineAngle F t j)) volume 0 T :=
      fun i _ => (continuous_const.mul (hcont i)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  have e2 : ∫ α, ∑ i ∈ s, c i * ee (∑ j, (k i j : ℝ) * α j) ∂torus F.card =
      ∑ i ∈ s, c i * ∫ α, ee (∑ j, (k i j : ℝ) * α j) ∂torus F.card := by
    rw [integral_finsetSum _ fun i _ => (integrable_ee _ (by fun_prop)).const_mul _]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e1, e2]
  exact tendsto_finsetSum _ fun i _ => (tendsto_mean_character F (k i)).const_mul (c i)

/-! ## The moments -/

/-- The multiplicity vector of an `ℓ`-tuple of indices: `#{i : x_i = j}`. -/
def multVec {K ℓ : ℕ} (x : Fin ℓ → Fin K) (j : Fin K) : ℤ := ((univ.filter fun i => x i = j).card : ℤ)

/-- The weight of an `ℓ`-tuple: `∏_i a_{p_{x_i}} p_{x_i}^{−σ}`. -/
noncomputable def tupleWeight (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ : ℝ) {ℓ : ℕ}
    (x : Fin ℓ → Fin F.card) : ℂ :=
  ∏ i, a (prP F (x i)) * (((pr F (x i) : ℝ) ^ (-σ) : ℝ) : ℂ)

lemma sum_comp_eq_multVec {K ℓ : ℕ} (x : Fin ℓ → Fin K) (α : Fin K → ℝ) :
    ∑ i, α (x i) = ∑ j, (multVec x j : ℝ) * α j := by
  rw [← Finset.sum_fiberwise univ x (fun i => α (x i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const,
    nsmul_eq_mul, multVec]
  push_cast
  ring

/-- `P(α)^ℓ = Σ_x w_x e(m(x)·α)`, with `w = tupleWeight` and `m = multVec`. -/
lemma torusPoly_pow (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ : ℝ) (ℓ : ℕ) (α : Fin F.card → ℝ) :
    torusPoly F a σ α ^ ℓ = ∑ x : Fin ℓ → Fin F.card, tupleWeight F a σ x * ee (∑ j, (multVec x j : ℝ) * α j) := by
  have h1 : torusPoly F a σ α ^ ℓ = ∏ _i : Fin ℓ, torusPoly F a σ α := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, torusPoly, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib, ← ee_sum, sum_comp_eq_multVec]
  rfl

/-- `|P(α)|^{2ℓ} = Σ_{x,y} w_x w̄_y e((m(x) − m(y))·α)`, with `w = tupleWeight` and `m = multVec`. -/
lemma norm_pow_expand (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ : ℝ) (ℓ : ℕ) (α : Fin F.card → ℝ) :
    ((‖torusPoly F a σ α‖ ^ (2 * ℓ) : ℝ) : ℂ) =
      ∑ q ∈ (univ : Finset (Fin ℓ → Fin F.card)) ×ˢ (univ : Finset (Fin ℓ → Fin F.card)),
        tupleWeight F a σ q.1 * conj (tupleWeight F a σ q.2) * ee (∑ j, ((multVec q.1 j - multVec q.2 j : ℤ) : ℝ) * α j) := by
  rw [show ‖torusPoly F a σ α‖ ^ (2 * ℓ) = ‖torusPoly F a σ α ^ ℓ‖ ^ 2 by
    rw [norm_pow, ← pow_mul, mul_comm], ofReal_pow, ← mul_conj', torusPoly_pow, map_sum,
    Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul, conj_ee]
  have e : ee (∑ j, (multVec x j : ℝ) * α j) * ee (-∑ j, (multVec y j : ℝ) * α j) =
      ee (∑ j, ((multVec x j - multVec y j : ℤ) : ℝ) * α j) := by
    rw [← ee_add]
    congr 1
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [← e]
  ring

/-- **The moments along the line are the torus moments.** For every `σ`, weights `a` and `ℓ`, the mean of
`|Σ_{p∈F} a_p p^{−(σ+it)}|^{2ℓ}` over `[0, T]` tends to `∫_{𝕋^F} |Σ_{p∈F} a_p p^{−σ} e(α_p)|^{2ℓ} dα`. -/
theorem tendsto_mean_moment (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ : ℝ) (ℓ : ℕ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖Orthogonality.primePoly F a σ t‖ ^ (2 * ℓ)) atTop
      (𝓝 (∫ α, ‖torusPoly F a σ α‖ ^ (2 * ℓ) ∂torus F.card)) := by
  have h := tendsto_mean_trigSum F ((univ : Finset (Fin ℓ → Fin F.card)) ×ˢ (univ : Finset (Fin ℓ → Fin F.card)))
    (fun q => tupleWeight F a σ q.1 * conj (tupleWeight F a σ q.2)) (fun q j => multVec q.1 j - multVec q.2 j)
  have hL : (fun T : ℝ => ((T⁻¹ * ∫ t in (0 : ℝ)..T, ‖Orthogonality.primePoly F a σ t‖ ^ (2 * ℓ) : ℝ) : ℂ)) =
      fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
        ∑ q ∈ (univ : Finset (Fin ℓ → Fin F.card)) ×ˢ (univ : Finset (Fin ℓ → Fin F.card)), tupleWeight F a σ q.1 * conj (tupleWeight F a σ q.2) *
          ee (∑ j, ((multVec q.1 j - multVec q.2 j : ℤ) : ℝ) * lineAngle F t j) := by
    funext T
    rw [ofReal_mul, ← intervalIntegral.integral_ofReal, ofReal_inv]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [primePoly_eq_torusPoly, norm_pow_expand]
  have hR : (((∫ α, ‖torusPoly F a σ α‖ ^ (2 * ℓ) ∂torus F.card) : ℝ) : ℂ) =
      ∫ α, ∑ q ∈ (univ : Finset (Fin ℓ → Fin F.card)) ×ˢ (univ : Finset (Fin ℓ → Fin F.card)), tupleWeight F a σ q.1 * conj (tupleWeight F a σ q.2) *
          ee (∑ j, ((multVec q.1 j - multVec q.2 j : ℤ) : ℝ) * α j) ∂torus F.card := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun α => norm_pow_expand F a σ ℓ α)
  have hC : Tendsto (fun T : ℝ => ((T⁻¹ * ∫ t in (0 : ℝ)..T,
      ‖Orthogonality.primePoly F a σ t‖ ^ (2 * ℓ) : ℝ) : ℂ)) atTop
      (𝓝 (((∫ α, ‖torusPoly F a σ α‖ ^ (2 * ℓ) ∂torus F.card) : ℝ) : ℂ)) := by
    rw [hL, hR]
    exact h
  have := (Complex.continuous_re.tendsto _).comp hC
  simpa [Function.comp_def] using this

/-! ## The count: Vinogradov's orthogonality for the multiplicative system -/

/-- With `a = 1` and `σ = 0`, `P(α)^ℓ` is Vinogradov's generating function `E` of the multiplicity vectors. -/
lemma torusPoly_one_zero_pow (F : Finset Nat.Primes) (ℓ : ℕ) (α : Fin F.card → ℝ) :
    torusPoly F 1 0 α ^ ℓ = E (univ : Finset (Fin ℓ → Fin F.card)) multVec α := by
  rw [torusPoly_pow, E]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [tupleWeight]

/-- **The torus moment of the unweighted prime sum is a Vinogradov count** (`count_eq_integral`):
`∫ |Σ_{p∈F} e(α_p)|^{2ℓ} dα = #{(x, y) : m(x) = m(y)}`, with `m = multVec`. -/
theorem integral_moment_eq_count (F : Finset Nat.Primes) (ℓ : ℕ) :
    ∫ α, ‖torusPoly F 1 0 α‖ ^ (2 * ℓ) ∂torus F.card =
      ((((univ : Finset (Fin ℓ → Fin F.card)) ×ˢ (univ : Finset (Fin ℓ → Fin F.card))).filter
        fun q => multVec q.1 = multVec q.2).card : ℝ) := by
  convert (count_eq_integral (univ : Finset (Fin ℓ → Fin F.card)) multVec).symm using 1
  refine integral_congr_ae (Eventually.of_forall fun α => ?_)
  simp only
  rw [← torusPoly_one_zero_pow, norm_pow, ← pow_mul, mul_comm ℓ 2]

/-- **The limiting means of `|Σ_{p∈F} p^{−it}|^{2ℓ}` are the count.** -/
theorem tendsto_mean_moment_count (F : Finset Nat.Primes) (ℓ : ℕ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖Orthogonality.primePoly F 1 0 t‖ ^ (2 * ℓ)) atTop
      (𝓝 ((((univ : Finset (Fin ℓ → Fin F.card)) ×ˢ (univ : Finset (Fin ℓ → Fin F.card))).filter
        fun q => multVec q.1 = multVec q.2).card : ℝ)) := by
  rw [← integral_moment_eq_count]
  exact tendsto_mean_moment F 1 0 ℓ

/-! ## Rigidity at every `ℓ`, against rigidity up to the dimension -/

/-- `∏_i p_{x_i} = ∏_j p_j^{#{i : x_i = j}}`. -/
lemma prod_pr_eq (F : Finset Nat.Primes) {ℓ : ℕ} (x : Fin ℓ → Fin F.card) :
    ∏ i, pr F (x i) = ∏ j, pr F j ^ (univ.filter fun i => x i = j).card := by
  rw [← Finset.prod_fiberwise univ x (fun i => pr F (x i))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]

/-- Equal multiplicity vectors, equal products: unique factorisation. -/
theorem multVec_eq_iff_prod_eq (F : Finset Nat.Primes) {ℓ : ℕ} (x y : Fin ℓ → Fin F.card) :
    multVec x = multVec y ↔ ∏ i, pr F (x i) = ∏ i, pr F (y i) := by
  rw [prod_pr_eq, prod_pr_eq]
  constructor
  · intro h
    refine Finset.prod_congr rfl fun j _ => ?_
    have := congrFun h j
    simp only [multVec, Nat.cast_inj] at this
    rw [this]
  · intro h
    funext j
    have h1 := factorization_prod_pow (pr F) (pr_prime F) (pr_injective F)
      (fun j => (univ.filter fun i => x i = j).card) j
    have h2 := factorization_prod_pow (pr F) (pr_prime F) (pr_injective F)
      (fun j => (univ.filter fun i => y i = j).card) j
    rw [h] at h1
    simp only [multVec]
    exact_mod_cast h1.symm.trans h2

lemma count_map_eq_card {K ℓ : ℕ} (z : Fin ℓ → Fin K) (j : Fin K) :
    Multiset.count j (univ.val.map z) = (univ.filter fun i => z i = j).card := by
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun i _ => eq_comm

/-- Equal multiplicity vectors, rearrangements of each other. -/
theorem multVec_eq_iff_map_eq {K ℓ : ℕ} (x y : Fin ℓ → Fin K) :
    multVec x = multVec y ↔ univ.val.map x = univ.val.map y := by
  rw [Multiset.ext]
  simp_rw [count_map_eq_card]
  constructor
  · intro h j
    have := congrFun h j
    simpa [multVec] using this
  · intro h
    funext j
    simp [multVec, h j]

/-- **The multiplicative system is rigid at every `ℓ`**: `∏_i p_{x_i} = ∏_i p_{y_i}` if and only if `x` and `y`
are rearrangements of each other. Compare `Vinogradov.agree_iff`, which needs `s ≤ k`. -/
theorem prod_eq_iff_map_eq (F : Finset Nat.Primes) {ℓ : ℕ} (x y : Fin ℓ → Fin F.card) :
    ∏ i, pr F (x i) = ∏ i, pr F (y i) ↔ univ.val.map x = univ.val.map y :=
  (multVec_eq_iff_prod_eq F x y).symm.trans (multVec_eq_iff_map_eq x y)

/-- **The additive system is not rigid beyond its dimension**: `(1, 5, 6)` and `(2, 3, 7)` agree in the sums of
first and second powers (`12` and `62`) and are not rearrangements of each other (their products are `30` and
`42`). So `agree_iff` fails at `s = 3`, `k = 2`. -/
theorem agree_not_rigid : ∃ x y : Fin 3 → ℕ, Agree 2 x y ∧ univ.val.map x ≠ univ.val.map y := by
  refine ⟨![1, 5, 6], ![2, 3, 7], ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨h1, h2⟩ := hj
    interval_cases j <;> simp [Fin.sum_univ_three]
  · intro h
    have := congrArg Multiset.prod h
    rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod] at this
    simp [Fin.prod_univ_three] at this

/-- **The limiting means of `|Σ_{p∈F} p^{−it}|^{2ℓ}` count the pairs of rearrangements.** -/
theorem tendsto_mean_moment_rearrangements (F : Finset Nat.Primes) (ℓ : ℕ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖Orthogonality.primePoly F 1 0 t‖ ^ (2 * ℓ)) atTop
      (𝓝 ((((univ : Finset (Fin ℓ → Fin F.card)) ×ˢ (univ : Finset (Fin ℓ → Fin F.card))).filter
        fun q => univ.val.map q.1 = univ.val.map q.2).card : ℝ)) := by
  convert tendsto_mean_moment_count F ℓ using 4
  exact Finset.filter_congr fun q _ => (multVec_eq_iff_map_eq q.1 q.2).symm

end BohrTorus

#print axioms BohrTorus.pr_prime
#print axioms BohrTorus.pr_injective
#print axioms BohrTorus.sum_prP
#print axioms BohrTorus.factorization_prod_pow
#print axioms BohrTorus.eq_zero_of_sum_log
#print axioms BohrTorus.continuous_lineAngle
#print axioms BohrTorus.ee_lineAngle
#print axioms BohrTorus.tendsto_mean_character
#print axioms BohrTorus.ee_lineAngle_one
#print axioms BohrTorus.bohr_line
#print axioms BohrTorus.primePoly_eq_torusPoly
#print axioms BohrTorus.sum_norm_sq_torus
#print axioms BohrTorus.tendsto_mean_trigSum
#print axioms BohrTorus.sum_comp_eq_multVec
#print axioms BohrTorus.torusPoly_pow
#print axioms BohrTorus.norm_pow_expand
#print axioms BohrTorus.tendsto_mean_moment
#print axioms BohrTorus.torusPoly_one_zero_pow
#print axioms BohrTorus.integral_moment_eq_count
#print axioms BohrTorus.tendsto_mean_moment_count
#print axioms BohrTorus.prod_pr_eq
#print axioms BohrTorus.multVec_eq_iff_prod_eq
#print axioms BohrTorus.count_map_eq_card
#print axioms BohrTorus.multVec_eq_iff_map_eq
#print axioms BohrTorus.prod_eq_iff_map_eq
#print axioms BohrTorus.agree_not_rigid
#print axioms BohrTorus.tendsto_mean_moment_rearrangements
