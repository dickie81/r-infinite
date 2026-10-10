import Mathlib
import BohrSphere

/-! # Orthogonality forces the Euclidean structure (round 395)

The owner wrote: "Orthogonality forces it". This file proves it in two forms, and what it says about round 391's
Bohr ball.

* **Parseval: distinct frequencies are orthogonal** (`trig` and `freqGapBound`, definitions;
  **`tendsto_mean_sq_norm_trig`**, with `integral_exp_mul_I`, `norm_integral_exp_mul_I_le`, `continuous_trig`,
  `sq_norm_trig`, `integral_sq_norm_trig`, `norm_integral_sub_le` and `abs_integral_sub_le`): for distinct real
  frequencies `λ_j` and complex coefficients `c_j`, the mean of `|Σ_j c_j e^{iλ_j t}|²` over `[0, T]` tends to
  `Σ_j |c_j|²`. The integral differs from `T·Σ_j |c_j|²` by at most `Σ_{j≠k} 2|c_j||c_k|/|λ_j − λ_k|`, uniformly
  in `T`.
* **The prime polynomial on a vertical line** (`primePoly`, a definition; **`tendsto_mean_sq_norm_primePoly`**
  and **`tendsto_mean_sq_norm_primeSum`**, with `natCast_cpow_line`, `primePoly_eq_trig` and `injOn_neg_log`):
  distinct primes have distinct frequencies `log p`, so the mean square of `Σ_{p∈F} a_p p^{−(σ+it)}` along the
  line `Re s = σ` tends to `Σ_{p∈F} |a_p|² p^{−2σ}`, the squared Euclidean norm of the weighted Bohr vector. With
  `a_p = 1`, divided by `c_F`, it tends to `‖v_F(s)‖²`: the radius of round 391 is the root mean square of the
  prime sum along the vertical line through `s`.
* **Pythagoras forces `p = 2`** (`lpGauge`, a definition; **`pythagoras_lpGauge_iff`**, with `lpGauge_two` and
  `pythagoras_two`): in dimension at least two, the `ℓ^p` gauge `(Σ|x_i|^p)^{1/p}` satisfies Pythagoras for every
  orthogonal pair if and only if `p = 2`.

What this file does not prove: anything about the zeros of ζ. Parseval holds for every choice of coefficients,
the Davenport–Heilbronn function's as well as ζ's. Mean-value theorems of this kind are what the classical
density theorems and the positive proportions of zeros on the line are built from; they have not given RH.
-/

open Complex Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace Orthogonality

/-! ## Part B: orthogonality of distinct frequencies (Parseval for trigonometric polynomials) -/

/-- `∫₀ᵀ e^{iμt} dt`: `T` when `μ = 0`, `(e^{iμT} − 1)/(iμ)` otherwise. -/
lemma integral_exp_mul_I (μ T : ℝ) :
    ∫ t in (0 : ℝ)..T, exp (μ * t * I) =
      if μ = 0 then (T : ℂ) else (exp (μ * T * I) - 1) / (μ * I) := by
  split_ifs with h
  · simp [h]
  · have hc : (μ : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 h) I_ne_zero
    have e : ∀ t : ℝ, exp ((μ : ℂ) * t * I) = exp ((μ * I) * t) := fun t => by ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    simp only [ofReal_zero, mul_zero, exp_zero]

/-- For `μ ≠ 0`, `‖∫₀ᵀ e^{iμt} dt‖ ≤ 2/|μ|`, uniformly in `T`. -/
lemma norm_integral_exp_mul_I_le {μ : ℝ} (h : μ ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, exp (μ * t * I)‖ ≤ 2 / |μ| := by
  rw [integral_exp_mul_I]
  simp only [h, ↓reduceIte]
  rw [norm_div, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have habs : 0 < |μ| := abs_pos.2 h
  refine div_le_div_of_nonneg_right ?_ habs.le
  calc ‖exp (μ * T * I) - 1‖ ≤ ‖exp (μ * T * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [show (μ : ℂ) * T * I = ((μ * T : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
        norm_one]
      norm_num

variable {ι : Type*} (s : Finset ι) (c : ι → ℂ) (lam : ι → ℝ)

/-- The trigonometric polynomial `Σ_{j∈s} c_j e^{iλ_j t}`. -/
noncomputable def trig (t : ℝ) : ℂ := ∑ j ∈ s, c j * exp (lam j * t * I)

lemma continuous_trig : Continuous (trig s c lam) := by
  unfold trig
  fun_prop

/-- `|Σ c_j e^{iλ_j t}|² = Σ_j Σ_k c_j c̄_k e^{i(λ_j − λ_k)t}`. -/
lemma sq_norm_trig (t : ℝ) :
    ((‖trig s c lam t‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * exp ((lam j - lam k) * t * I) := by
  rw [ofReal_pow, ← mul_conj', trig, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← exp_conj]
  have e : conj ((lam k : ℂ) * t * I) = -((lam k : ℂ) * t * I) := by
    simp [conj_ofReal]
  rw [e]
  have e2 : ((lam j - lam k : ℝ) : ℂ) * t * I = (lam j : ℂ) * t * I + -((lam k : ℂ) * t * I) := by
    push_cast; ring
  rw [show ((lam j : ℂ) - lam k) * t * I = ((lam j - lam k : ℝ) : ℂ) * t * I by push_cast; ring, e2,
    exp_add]
  ring

/-- `∫₀ᵀ |trig|²`, expanded over pairs of frequencies. -/
lemma integral_sq_norm_trig (T : ℝ) :
    ((∫ t in (0 : ℝ)..T, ‖trig s c lam t‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * ∫ t in (0 : ℝ)..T, exp ((lam j - lam k) * t * I) := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [sq_norm_trig]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro k _
      exact (by fun_prop : Continuous fun t : ℝ =>
        c j * conj (c k) * exp (((lam j : ℂ) - lam k) * t * I)).intervalIntegrable _ _
  · intro j _
    exact (by fun_prop : Continuous fun t : ℝ =>
      ∑ k ∈ s, c j * conj (c k) * exp (((lam j : ℂ) - lam k) * t * I)).intervalIntegrable _ _

variable [DecidableEq ι]

/-- The off-diagonal constant `2/|λ_j − λ_k|` (`0` on the diagonal). -/
noncomputable def freqGapBound (lam : ι → ℝ) (j k : ι) : ℝ := if j = k then 0 else 2 / |lam j - lam k|

lemma norm_integral_sub_le (hlam : Set.InjOn lam s) {j k : ι} (hj : j ∈ s) (hk : k ∈ s) (T : ℝ) :
    ‖(∫ t in (0 : ℝ)..T, exp (((lam j : ℂ) - lam k) * t * I)) - (if j = k then (T : ℂ) else 0)‖
      ≤ freqGapBound lam j k := by
  unfold freqGapBound
  split_ifs with hjk
  · subst hjk
    simp
  · have hne : lam j - lam k ≠ 0 := sub_ne_zero.2 fun h => hjk (hlam hj hk h)
    rw [sub_zero, show ((lam j : ℂ) - lam k) = ((lam j - lam k : ℝ) : ℂ) by push_cast; ring]
    exact norm_integral_exp_mul_I_le hne T

/-- **The deviation of `∫₀ᵀ |trig|²` from `T·Σ|c_j|²` is bounded uniformly in `T`.** -/
lemma abs_integral_sub_le (hlam : Set.InjOn lam s) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖trig s c lam t‖ ^ 2) - T * ∑ j ∈ s, ‖c j‖ ^ 2| ≤
      ∑ j ∈ s, ∑ k ∈ s, ‖c j‖ * ‖c k‖ * freqGapBound lam j k := by
  have hdiag : ((T * ∑ j ∈ s, ‖c j‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * (if j = k then (T : ℂ) else 0) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte]
      rw [mul_conj']
      ring
    · intro k _ hkj
      simp [Ne.symm hkj]
    · intro hj'
      exact absurd hj hj'
  have key : (((∫ t in (0 : ℝ)..T, ‖trig s c lam t‖ ^ 2) - T * ∑ j ∈ s, ‖c j‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) *
        ((∫ t in (0 : ℝ)..T, exp (((lam j : ℂ) - lam k) * t * I)) - (if j = k then (T : ℂ) else 0)) := by
    rw [ofReal_sub, integral_sq_norm_trig, hdiag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hn := congrArg norm key
  rw [norm_real, Real.norm_eq_abs] at hn
  rw [hn]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_))
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left (norm_integral_sub_le s lam hlam hj hk T) (by positivity)

/-- **Parseval for trigonometric polynomials: distinct frequencies are orthogonal.** The mean of
`|Σ_j c_j e^{iλ_j t}|²` over `[0, T]` tends to `Σ_j |c_j|²`. -/
theorem tendsto_mean_sq_norm_trig (hlam : Set.InjOn lam s) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖trig s c lam t‖ ^ 2) atTop
      (𝓝 (∑ j ∈ s, ‖c j‖ ^ 2)) := by
  set B := ∑ j ∈ s, ∑ k ∈ s, ‖c j‖ * ‖c k‖ * freqGapBound lam j k
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    ((tendsto_const_nhds (x := B)).div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [Real.norm_eq_abs]
  have e : T⁻¹ * (∫ t in (0 : ℝ)..T, ‖trig s c lam t‖ ^ 2) - ∑ j ∈ s, ‖c j‖ ^ 2 =
      T⁻¹ * ((∫ t in (0 : ℝ)..T, ‖trig s c lam t‖ ^ 2) - T * ∑ j ∈ s, ‖c j‖ ^ 2) := by
    field_simp
  rw [e, abs_mul, abs_inv, abs_of_pos hT, id, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (abs_integral_sub_le s c lam hlam T) (inv_nonneg.2 hT.le)

/-! ## Part C: the prime polynomial on a vertical line -/

/-- The prime polynomial `Σ_{p∈F} a_p p^{−(σ+it)}`. -/
noncomputable def primePoly (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ t : ℝ) : ℂ :=
  ∑ p ∈ F, a p * ((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * I))

lemma natCast_cpow_line (p : Nat.Primes) (σ t : ℝ) :
    ((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * I)) =
      ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * exp ((-Real.log (p : ℕ) : ℝ) * t * I) := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 p.prop.ne_zero
  have hpr : (0 : ℝ) < (p : ℕ) := Nat.cast_pos.2 p.prop.pos
  rw [cpow_def_of_ne_zero hp, Real.rpow_def_of_pos hpr, ofReal_exp, ← exp_add, ← natCast_log]
  congr 1
  push_cast
  ring

lemma primePoly_eq_trig (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ t : ℝ) :
    primePoly F a σ t =
      trig F (fun p => a p * ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)) (fun p => -Real.log (p : ℕ)) t := by
  unfold primePoly trig
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [natCast_cpow_line]
  ring

/-- Distinct primes have distinct frequencies `log p`. -/
lemma injOn_neg_log (F : Finset Nat.Primes) :
    Set.InjOn (fun p : Nat.Primes => -Real.log (p : ℕ)) F := by
  intro p _ q _ h
  simp only [neg_inj] at h
  have hpq := Real.log_injOn_pos (Set.mem_Ioi.2 (Nat.cast_pos.2 p.prop.pos))
    (Set.mem_Ioi.2 (Nat.cast_pos.2 q.prop.pos)) h
  exact Nat.Primes.coe_nat_injective (by exact_mod_cast hpq)

/-- **The mean square of a prime polynomial along the vertical line `Re s = σ` is the squared
Euclidean norm of its weighted Bohr vector** `(a_p p^{−σ})_{p∈F}`. -/
theorem tendsto_mean_sq_norm_primePoly (F : Finset Nat.Primes) (a : Nat.Primes → ℂ) (σ : ℝ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖primePoly F a σ t‖ ^ 2) atTop
      (𝓝 (∑ p ∈ F, ‖a p‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ)))) := by
  simp_rw [primePoly_eq_trig]
  convert tendsto_mean_sq_norm_trig F _ _ (injOn_neg_log F) using 2
  refine Finset.sum_congr rfl fun p _ => ?_
  have hpr : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpr _), mul_pow,
    ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-σ)), ← Real.rpow_mul hpr]
  congr 2
  push_cast
  ring

/-- **The radius of round 391 is the root mean square of the prime sum.** For every `s`, the mean
square of `Σ_{p∈F} p^{−(Re s + it)}` along the vertical line through `s`, divided by `c_F`, tends to
`‖v_F(s)‖²`. -/
theorem tendsto_mean_sq_norm_primeSum (F : Finset Nat.Primes) (s : ℂ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖primePoly F 1 s.re t‖ ^ 2 / BohrSphere.cF F)
      atTop (𝓝 (‖BohrSphere.vF F s‖ ^ 2)) := by
  rw [BohrSphere.norm_vF_sq]
  have h := (tendsto_mean_sq_norm_primePoly F 1 s.re).div_const (BohrSphere.cF F)
  convert h using 2 with T
  · rw [intervalIntegral.integral_div, mul_div_assoc]
  · simp [BohrSphere.bohrSqSum]

/-! ## Part A: Pythagoras forces `p = 2` -/

section Pythagoras

variable {κ : Type*} [Fintype κ]

/-- The `ℓ^p` gauge `(Σ|x_i|^p)^{1/p}` on `ℝ^κ`. -/
noncomputable def lpGauge (p : ℝ) (x : EuclideanSpace ℝ κ) : ℝ := (∑ i, |x i| ^ p) ^ (1 / p)

theorem lpGauge_two (x : EuclideanSpace ℝ κ) : lpGauge 2 x = ‖x‖ := by
  rw [lpGauge, EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.rpow_two, Real.norm_eq_abs]

/-- In the Euclidean norm, orthogonal vectors satisfy Pythagoras. -/
theorem pythagoras_two {x y : EuclideanSpace ℝ κ} (h : inner ℝ x y = 0) :
    lpGauge 2 (x + y) ^ 2 = lpGauge 2 x ^ 2 + lpGauge 2 y ^ 2 := by
  simp only [lpGauge_two, sq]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_real h

/-- **Orthogonality forces `p = 2`.** In dimension at least two, the `ℓ^p` gauge satisfies
Pythagoras for every orthogonal pair if and only if `p = 2`. -/
theorem pythagoras_lpGauge_iff [DecidableEq κ] {i j : κ} (hij : i ≠ j) {p : ℝ} (hp : 0 < p) :
    (∀ x y : EuclideanSpace ℝ κ, inner ℝ x y = 0 →
      lpGauge p (x + y) ^ 2 = lpGauge p x ^ 2 + lpGauge p y ^ 2) ↔ p = 2 := by
  constructor
  · intro h
    have horth : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) = 0 := by
      rw [EuclideanSpace.inner_single_left]
      simp [hij]
    have ek : ∀ k : κ, lpGauge p (EuclideanSpace.single k (1 : ℝ)) = 1 := by
      intro k
      rw [lpGauge, Fintype.sum_eq_single k]
      · simp
      · intro m hm
        simp [hm, Real.zero_rpow hp.ne']
    have eij : lpGauge p (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ)) =
        2 ^ (1 / p) := by
      rw [lpGauge, Fintype.sum_eq_add i j hij]
      · simp [hij, Ne.symm hij]
        norm_num
      · intro m ⟨hmi, hmj⟩
        simp [hmi, hmj, Real.zero_rpow hp.ne']
    have h1 := h _ _ horth
    rw [ek, ek, eij, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two] at h1
    norm_num at h1
    have h2 : p⁻¹ * 2 = 1 := by
      have hl := congrArg Real.log h1
      rw [Real.log_rpow two_pos] at hl
      have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      exact mul_right_cancel₀ hlog (hl.trans (one_mul _).symm)
    field_simp at h2
    linarith
  · rintro rfl x y hxy
    exact pythagoras_two hxy

end Pythagoras

end Orthogonality

#print axioms Orthogonality.integral_exp_mul_I
#print axioms Orthogonality.norm_integral_exp_mul_I_le
#print axioms Orthogonality.continuous_trig
#print axioms Orthogonality.sq_norm_trig
#print axioms Orthogonality.integral_sq_norm_trig
#print axioms Orthogonality.norm_integral_sub_le
#print axioms Orthogonality.abs_integral_sub_le
#print axioms Orthogonality.tendsto_mean_sq_norm_trig
#print axioms Orthogonality.natCast_cpow_line
#print axioms Orthogonality.primePoly_eq_trig
#print axioms Orthogonality.injOn_neg_log
#print axioms Orthogonality.tendsto_mean_sq_norm_primePoly
#print axioms Orthogonality.tendsto_mean_sq_norm_primeSum
#print axioms Orthogonality.lpGauge_two
#print axioms Orthogonality.pythagoras_two
#print axioms Orthogonality.pythagoras_lpGauge_iff
