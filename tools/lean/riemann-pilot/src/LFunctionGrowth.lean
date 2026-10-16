import Mathlib
import RealDirichlet

/-! # The growth of `L(s, χ)` for every `χ ≠ 1`, and the reflection of `Λ*` for every primitive `χ` (round 509)

Moved unchanged from the dh layer so that the pnt layer, which imports no dh module, can use them:
* from DHHadamard.lean (round 254): the partial sums of `χ ≠ 1` are bounded by its modulus
  (`norm_sum_cC_le`), `L(s, χ) = s∫_1^∞ S(x)x^{−s−1}dx` on `Re s > 0` from Mathlib's `LSeries_eq_mul_integral`
  (`LFunction_eq_IχC`), hence `‖L(s, χ)‖ ≤ (N + 1)‖s‖/Re s` (`norm_LFunction_leC`), and the reflection
  `Λ*(1 − s, χ) = ε_χ Λ*(s, χ⁻¹)` for primitive `χ` (`LamG_one_sub'`);
* from DavenportHeilbronn.lean (round 253): `χ⁻¹` is primitive when `χ` is (`isPrimitive_inv`).

Round 224's `norm_LFunction_le` (RealDirichlet.lean) is the growth bound for quadratic `χ`; its integral
representation is for the L-series of `Re χ`. Round 509 uses `norm_LFunction_leC` in its place in the pnt layer's
ChiPNT.lean and ChiUniform.lean, and `LamG_one_sub'` for the band of every `L(s, χ)` (HalfPlaneJoinsChar.lean).
-/

open Real Complex DirichletCharacter Filter Topology MeasureTheory Set Asymptotics

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-! ## Complex partial sums -/

/-- `χ(n)` as a sequence on `ℕ`. -/
def cC (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := χ n

omit [NeZero N] in
theorem norm_cC_le (n : ℕ) : ‖cC χ n‖ ≤ 1 := norm_le_one χ _

omit [NeZero N] in
theorem sum_range_shiftC (g : ℕ → ℂ) (hper : ∀ k, g (k + N) = g k) (m : ℕ) :
    ∑ k ∈ Finset.range N, g (m + k) = ∑ k ∈ Finset.range N, g k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ' (fun k => g (m + k)) N
    have h2 := Finset.sum_range_succ (fun k => g (m + k)) N
    have e : ∑ k ∈ Finset.range N, g (m + 1 + k) = ∑ k ∈ Finset.range N, g (m + (k + 1)) :=
      Finset.sum_congr rfl fun k _ => by congr 1; ring
    have hN : g (m + N) = g (m + 0) := by rw [add_zero, hper]
    linear_combination e - h1 + h2 + hN

theorem sum_range_modC (g : ℕ → ℂ) (hper : ∀ k, g (k + N) = g k)
    (h0 : ∑ k ∈ Finset.range N, g k = 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, g k = ∑ k ∈ Finset.range (n % N), g k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n N with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_comm N m, Finset.sum_range_add, sum_range_shiftC g hper, h0, add_zero,
        Nat.add_mod_right]
      exact ih m (by have := NeZero.pos N; omega)

/-- **The partial sums of a nontrivial `χ` are bounded by its modulus.** -/
theorem norm_sum_cC_le (hχ1 : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ Finset.range n, cC χ k‖ ≤ N := by
  have hper : ∀ k, cC χ (k + N) = cC χ k := fun k => by simp [cC]
  have h0 : ∑ k ∈ Finset.range N, cC χ k = 0 :=
    (sum_range_eq_univ (fun a => χ a)).trans (MulChar.sum_eq_zero_of_ne_one hχ1)
  rw [sum_range_modC _ hper h0]
  calc ‖∑ k ∈ Finset.range (n % N), cC χ k‖ ≤ ∑ k ∈ Finset.range (n % N), ‖cC χ k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n % N), (1 : ℝ) := Finset.sum_le_sum fun k _ => norm_cC_le k
    _ = (n % N : ℕ) := by simp
    _ ≤ N := by exact_mod_cast (Nat.mod_lt n (NeZero.pos N)).le

omit [NeZero N] in
theorem sum_Icc_eqC (g : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, g k = ∑ k ∈ Finset.range (n + 1), g k - g 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (n + 1)]; ring

/-- The summatory function `S(x) = Σ_{n ≤ x} χ(n)`. -/
def summC (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, cC χ k

theorem norm_summC_le (hχ1 : χ ≠ 1) (x : ℝ) : ‖summC χ x‖ ≤ N + 1 := by
  unfold summC
  rw [sum_Icc_eqC]
  refine (norm_sub_le _ _).trans ?_
  linarith [norm_sum_cC_le hχ1 (⌊x⌋₊ + 1), norm_cC_le (χ := χ) 0]

omit [NeZero N] in
theorem measurable_summC : Measurable (summC χ) :=
  (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cC χ k)).comp Nat.measurable_floor

/-! ## `L(s, χ)` on `Re s > 0` by partial summation, complex coefficients -/

/-- `I(s) = ∫_1^∞ S(x)x^{−s−1}dx`. -/
def IχC (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), summC χ x * (x : ℂ) ^ (-(s + 1))

omit [NeZero N] in
theorem IχC_eq_mellin (s : ℂ) :
    IχC χ s = mellin (fun x : ℝ => (Ioi (1 : ℝ)).indicator (summC χ) x) (-s) := by
  unfold IχC mellin
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator (s := Ioi 0) measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases h1 : x ∈ Ioi (1 : ℝ)
  · have h0 : x ∈ Ioi (0 : ℝ) := show (0 : ℝ) < x from lt_trans one_pos h1
    simp only [indicator_of_mem h1, indicator_of_mem h0, smul_eq_mul]
    rw [mul_comm]; congr 2; ring
  · simp only [indicator_of_notMem h1]
    by_cases h0 : x ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem h0, indicator_of_notMem h1]
    · simp [indicator_of_notMem h0]

theorem IχC_differentiableAt (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (IχC χ) s := by
  set g : ℝ → ℂ := fun x => (Ioi (1 : ℝ)).indicator (summC χ) x
  have hgm : Measurable g := measurable_summC.indicator measurableSet_Ioi
  have hgb : ∀ x, ‖g x‖ ≤ N + 1 := fun x => by
    by_cases h : x ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem h]
      exact norm_summC_le hχ1 x
    · simp only [g, indicator_of_notMem h, norm_zero]; positivity
  have hloc : LocallyIntegrableOn g (Ioi 0) :=
    ((locallyIntegrable_const ((N + 1 : ℝ) : ℂ)).mono hgm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]; exact hgb x)).locallyIntegrableOn _
  have htop : g =O[atTop] (· ^ (-(0 : ℝ))) :=
    Asymptotics.IsBigO.of_bound (N + 1) (Eventually.of_forall fun x => by
      simpa [Real.rpow_zero] using hgb x)
  have hbot : g =O[𝓝[>] 0] (· ^ (-((-s).re - 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have : x ∉ Ioi (1 : ℝ) := fun h => by linarith [hx.2, show 1 < x from h]
    simp [g, indicator_of_notMem this]
  have hd : DifferentiableAt ℂ (mellin g) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by simp; linarith) hbot (by linarith)
  have e : IχC χ = fun s => mellin g (-s) := funext IχC_eq_mellin
  rw [e]
  exact hd.comp s differentiableAt_id.neg

/-- **`L(s, χ) = s·∫_1^∞ S(x)x^{−s−1}dx` for `Re s > 0`**, for every `χ ≠ 1`. -/
theorem LFunction_eq_IχC (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * IχC χ s := by
  set U : Set ℂ := {s | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hL : DifferentiableOn ℂ (LFunction χ) U := (differentiable_LFunction hχ1).differentiableOn
  have hR : DifferentiableOn ℂ (fun s => s * IχC χ s) U := fun z hz =>
    (differentiableAt_id.mul (IχC_differentiableAt hχ1 hz)).differentiableWithinAt
  refine eqOn_convex hUo (convex_halfSpace_re_gt 0) hL hR (z0 := 2)
    (show (0 : ℝ) < (2 : ℂ).re by norm_num) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  have hS : LSeriesSummable (cC χ) z :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_cC_le n) hz
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cC χ k) =O[atTop] fun n => (n : ℝ) ^ (0 : ℝ) :=
    Asymptotics.IsBigO.of_bound (N + 1) (Eventually.of_forall fun n => by
      rw [Real.rpow_zero, norm_one, mul_one]
      have := norm_summC_le hχ1 n
      simpa [summC] using this)
  have h := LSeries_eq_mul_integral (cC χ) le_rfl (by linarith) hS hO
  rw [LFunction_eq_LSeries χ hz]
  exact h

/-- **`‖L(s, χ)‖ ≤ (N + 1)‖s‖/Re s`** on `Re s > 0`, for every `χ ≠ 1`. -/
theorem norm_LFunction_leC (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ (N + 1) * ‖s‖ / s.re := by
  rw [LFunction_eq_IχC hχ1 hs, norm_mul]
  suffices hI : ‖IχC χ s‖ ≤ (N + 1) * (1 / s.re) by
    calc ‖s‖ * ‖IχC χ s‖ ≤ ‖s‖ * ((N + 1) * (1 / s.re)) := by gcongr
      _ = _ := by ring
  rw [← integral_rpow_Ioi_one' hs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  have hx0 : 0 < x := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have : (-(s + 1)).re = -s.re - 1 := by simp; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (norm_summC_le hχ1 x) (by positivity)

/-! ## The reflection -/

omit [NeZero N] in
/-- `χ⁻¹` is primitive when `χ` is. -/
theorem isPrimitive_inv (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  unfold IsPrimitive at *; rw [conductor_inv]; exact hprim

/-- **`Λ*(1 − s, χ) = ε_χ Λ*(s, χ⁻¹)`** for primitive `χ`. -/
theorem LamG_one_sub' (hprim : χ.IsPrimitive) (s : ℂ) :
    LamG χ (1 - s) = rootNumber χ * LamG χ⁻¹ s := by
  unfold LamG
  rw [hprim.completedLFunction_one_sub]
  have e : (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) = (N : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ natCast_ne_zero']; congr 1; ring
  linear_combination (rootNumber χ * completedLFunction χ⁻¹ s) * e

end PsiOmega

#print axioms PsiOmega.norm_sum_cC_le
#print axioms PsiOmega.LFunction_eq_IχC
#print axioms PsiOmega.norm_LFunction_leC
#print axioms PsiOmega.LamG_one_sub'
