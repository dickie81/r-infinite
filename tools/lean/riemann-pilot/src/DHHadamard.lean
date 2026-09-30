import Mathlib
import DavenportHeilbronn

/-! # Davenport–Heilbronn in Lean, stage 2: the Hadamard product of `Ξ_{DH}` (round 254)

Round 225's growth chain for `Ξ_χ` (`norm_LamG_le → norm_XiC_le → hadamard_XiC`, RealDirichlet.lean
and WeilChi.lean) takes `χ` real: its integral representation `LFunction_eq_Iχ` is for the L-series of
`Re χ`, and the reflection to `Re s < ½` uses `χ⁻¹ = χ`. Here the chain is rebuilt for every primitive
`χ ≠ 1`:

* complex partial sums, `‖Σ_{k<n} χ(k)‖ ≤ N` (`norm_sum_cC_le`) and `‖S(x)‖ ≤ N + 1`;
* `L(s, χ) = s∫_1^∞ S(x)x^{−s−1}dx` on `Re s > 0` from Mathlib's `LSeries_eq_mul_integral`
  (`LFunction_eq_IχC`), hence `‖L(s, χ)‖ ≤ (N + 1)‖s‖/Re s` (`norm_LFunction_leC`);
* `‖Λ*(w)‖ ≤ n^{3n}` on `Re w ≥ ½` (`norm_LamG_leC`), the reflection `Λ*(1 − s, χ) = ε_χ Λ*(s, χ⁻¹)`
  (`LamG_one_sub'`), and the order bound `‖Ξ_χ(t)‖ ≤ K_χ e^{36‖t‖^{3/2}}` for every primitive `χ`
  (`norm_XiC_le'`), which, unlike round 225's, needs no `L(½, χ) ≠ 0`;
* for the Davenport–Heilbronn combination (DavenportHeilbronn.lean): `‖Ξ_{DH}(t)‖ ≤ K e^{36‖t‖^{3/2}}`
  (`norm_XiDH_le`), `Ξ_{DH}(0) = 2(1 + ε_{χ⁻¹}) Λ*(½, χ)` (`XiDH_zero_eq`), and **the Hadamard
  product** `HadamardW (XiDH χ)` from `hadamardW_even`, under `ε_χ ≠ −1` and `L(½, χ) ≠ 0`
  (`hadamard_XiDH`).

For `χ₅` the first input is round 253's `rootNumber_chi5_ne_neg_one`; the second is the named input
`DHHalf : L(½, χ₅) ≠ 0`, and `hadamard_dh : DHHalf → HadamardW (XiDH chi5) …` gives the zeros of the
Davenport–Heilbronn `Ξ` as the indexed family `ZeroIdx (sqF (XiDH chi5))` with multiplicities,
summable inverses, and the product formula. What remains for the certificate chain is the explicit
formula (the prime side of `−dh′/dh`) and the certificate arithmetic; see the README, round 254.
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

/-! ## `‖Λ*(w)‖ ≤ n^{3n}` on `Re w ≥ ½`, for every `χ ≠ 1` -/

theorem norm_LamG_leC (hχ1 : χ ≠ 1) {w : ℂ} (hw : 1 / 2 ≤ w.re) {n : ℕ}
    (hn : ‖w‖ + 3 ≤ n) (hnN : (N : ℝ) + 1 ≤ n) (hn4 : 4 ≤ n) :
    ‖LamG χ w‖ ≤ (n : ℝ) ^ (3 * n) := by
  have hre := Complex.re_le_norm w
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  rw [LamG, completed_eq_mul (by linarith), norm_mul, norm_mul]
  have hc : ‖(N : ℂ) ^ (w / 2)‖ ≤ (n : ℝ) ^ n := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    have e : (w / 2).re = w.re / 2 := by simp
    rw [e]
    calc (N : ℝ) ^ (w.re / 2) ≤ (N : ℝ) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ (n : ℝ) ^ (n : ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
      _ = (n : ℝ) ^ n := Real.rpow_natCast _ _
  have hΓ : ‖gammaFactor χ w‖ ≤ 4 * (n : ℝ) ^ n := by
    obtain ⟨δ, hδ1, hδ⟩ := gammaFactor_shift χ
    have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
    have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
    rw [hδ]
    refine (norm_Gammaℝ_le' (by simp; linarith)).trans ?_
    have e : (w + δ).re = w.re + δ := by simp
    rw [e]
    refine (rGamma_le' (n := n) (by linarith) (by linarith)).trans ?_
    have : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    linarith
  have hL : ‖LFunction χ w‖ ≤ 2 * (n : ℝ) ^ 2 := by
    refine (norm_LFunction_leC hχ1 (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : ((N : ℝ) + 1) * ‖w‖ ≤ n * n := mul_le_mul hnN (by linarith) (norm_nonneg _) (by linarith)
    nlinarith
  have hpow : 8 * (n : ℝ) ^ (2 * n + 2) ≤ (n : ℝ) ^ (3 * n) := by
    have h8 : (8 : ℝ) ≤ (n : ℝ) ^ (n - 2) := by
      calc (8 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        _ ≤ (n : ℝ) ^ (n - 2) := pow_le_pow_right₀ (by linarith) (by omega)
    calc 8 * (n : ℝ) ^ (2 * n + 2) ≤ (n : ℝ) ^ (n - 2) * (n : ℝ) ^ (2 * n + 2) :=
          mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = (n : ℝ) ^ (3 * n) := by rw [← pow_add]; congr 1; omega
  calc ‖(N : ℂ) ^ (w / 2)‖ * (‖gammaFactor χ w‖ * ‖LFunction χ w‖)
      ≤ (n : ℝ) ^ n * (4 * (n : ℝ) ^ n * (2 * (n : ℝ) ^ 2)) := by gcongr
    _ = 8 * (n : ℝ) ^ (2 * n + 2) := by ring
    _ ≤ _ := hpow

/-! ## Reflection and the growth of `Ξ_χ`, `Ξ_{DH}` -/

/-- **`Λ*(1 − s, χ) = ε_χ Λ*(s, χ⁻¹)`** for primitive `χ`. -/
theorem LamG_one_sub' (hprim : χ.IsPrimitive) (s : ℂ) :
    LamG χ (1 - s) = rootNumber χ * LamG χ⁻¹ s := by
  unfold LamG
  rw [hprim.completedLFunction_one_sub]
  have e : (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) = (N : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ natCast_ne_zero']; congr 1; ring
  linear_combination (rootNumber χ * completedLFunction χ⁻¹ s) * e

/-- `n^{3n} ≤ exp(12 n√n)`. -/
theorem pow_three_mul_le_exp {n : ℕ} (hn0 : (0 : ℝ) < n) :
    (n : ℝ) ^ (3 * n) ≤ Real.exp (12 * ((n : ℝ) * Real.sqrt n)) := by
  calc (n : ℝ) ^ (3 * n) = Real.exp ((3 * n : ℝ) * Real.log n) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hn0]; push_cast; ring_nf
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        have hl := log_le_two_sqrt hn0
        nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- **The order of `Ξ_χ` for every primitive `χ ≠ 1`**: `‖Ξ_χ(t)‖ ≤ K_χ exp(36‖t‖^{3/2})`, with the
functional equation reflecting `Re(½ + it) < ½` to `χ⁻¹`. -/
theorem norm_XiC_le' (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℂ) :
    ‖XiC χ t‖ ≤ KC χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  set x := ‖t‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg t
  set M : ℝ := (N : ℝ) + 5
  have hM : 0 ≤ M := by positivity
  set n : ℕ := ⌈x⌉₊ + N + 4
  have hnx : (n : ℝ) ≤ x + M := by
    have := Nat.ceil_lt_add_one hx0; simp only [n, M]; push_cast; linarith
  have hxn : x + N + 4 ≤ (n : ℝ) := by
    have := Nat.le_ceil x; simp only [n]; push_cast; linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn4 : 4 ≤ n := by simp only [n]; omega
  have hn1 : ‖1 / 2 + I * t‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
  have hn2 : ‖1 / 2 + I * -t‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
  -- `‖Ξ_χ(t)‖ ≤ (‖ε‖ + 1) n^{3n}` in both cases
  have hmain : ‖XiC χ t‖ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) := by
    rcases le_total (1 / 2) (1 / 2 + I * t).re with h | h
    · have hL := norm_LamG_leC hχ1 h (n := n) (by linarith) (by linarith) hn4
      have hp : (0 : ℝ) ≤ (n : ℝ) ^ (3 * n) := by positivity
      calc ‖XiC χ t‖ = ‖LamG χ (1 / 2 + I * t)‖ := rfl
        _ ≤ (n : ℝ) ^ (3 * n) := hL
        _ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) := by nlinarith [norm_nonneg (rootNumber χ)]
    · have hre : 1 / 2 ≤ (1 / 2 + I * -t).re := by
        simp only [add_re, mul_re, I_re, I_im, neg_re, neg_im] at h ⊢; norm_num at h ⊢; linarith
      have hL := norm_LamG_leC (inv_ne_one.2 hχ1) hre (n := n) (by linarith) (by linarith) hn4
      have e : LamG χ (1 / 2 + I * t) = rootNumber χ * LamG χ⁻¹ (1 / 2 + I * -t) := by
        rw [← LamG_one_sub' hprim]; congr 1; ring
      calc ‖XiC χ t‖ = ‖rootNumber χ * LamG χ⁻¹ (1 / 2 + I * -t)‖ := by rw [XiC, e]
        _ = ‖rootNumber χ‖ * ‖LamG χ⁻¹ (1 / 2 + I * -t)‖ := norm_mul _ _
        _ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) :=
            mul_le_mul (by linarith) hL (norm_nonneg _) (by positivity)
  have hns : (n : ℝ) * Real.sqrt n ≤ 3 * (x * Real.sqrt x) + 3 * (M * Real.sqrt M) :=
    le_trans (mul_le_mul hnx (Real.sqrt_le_sqrt hnx) (Real.sqrt_nonneg _) (by linarith))
      (shift_sqrt hx0 hM)
  have hx32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx0 (by norm_num), Real.rpow_one]
  rw [hx32]
  have hKC : (‖rootNumber χ‖ + 1) * Real.exp (36 * (M * Real.sqrt M)) ≤ KC χ := by
    unfold KC; simp only [M]; linarith
  calc ‖XiC χ t‖ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) := hmain
    _ ≤ (‖rootNumber χ‖ + 1) * Real.exp (12 * ((n : ℝ) * Real.sqrt n)) := by
        gcongr; exact pow_three_mul_le_exp hn0
    _ ≤ (‖rootNumber χ‖ + 1) * Real.exp (12 * (3 * (x * Real.sqrt x) + 3 * (M * Real.sqrt M))) := by
        gcongr
    _ = ((‖rootNumber χ‖ + 1) * Real.exp (36 * (M * Real.sqrt M))) * Real.exp (36 * (x * Real.sqrt x)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ KC χ * Real.exp (36 * (x * Real.sqrt x)) := by gcongr

/-- The growth constant of `Ξ_{DH}`. -/
def KDH (χ : DirichletCharacter ℂ N) : ℝ :=
  ‖1 + rootNumber χ⁻¹‖ * KC χ + ‖1 + rootNumber χ‖ * KC χ⁻¹ + 1

theorem one_le_KDH : 1 ≤ KDH χ := by
  unfold KDH
  have h1 := one_le_KC (χ := χ)
  have h2 := one_le_KC (χ := χ⁻¹)
  nlinarith [norm_nonneg (1 + rootNumber χ⁻¹), norm_nonneg (1 + rootNumber χ)]

/-- **The order of `Ξ_{DH}`**: `‖Ξ_{DH}(t)‖ ≤ K exp(36‖t‖^{3/2})`. -/
theorem norm_XiDH_le (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℂ) :
    ‖XiDH χ t‖ ≤ KDH χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  have h1 := norm_XiC_le' hχ1 hprim t
  have h2 := norm_XiC_le' (inv_ne_one.2 hχ1) (isPrimitive_inv χ hprim) t
  have he : 0 < Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := Real.exp_pos _
  calc ‖XiDH χ t‖ = ‖(1 + rootNumber χ⁻¹) * XiC χ t + (1 + rootNumber χ) * XiC χ⁻¹ t‖ := rfl
    _ ≤ ‖1 + rootNumber χ⁻¹‖ * ‖XiC χ t‖ + ‖1 + rootNumber χ‖ * ‖XiC χ⁻¹ t‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ ‖1 + rootNumber χ⁻¹‖ * (KC χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)))
        + ‖1 + rootNumber χ‖ * (KC χ⁻¹ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ))) := by gcongr
    _ ≤ KDH χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by unfold KDH; nlinarith

/-! ## `Ξ_{DH}(0) ≠ 0` and the Hadamard product -/

/-- `Ξ_{DH}(0) = 2(1 + ε_{χ⁻¹}) Λ*(½, χ)`. -/
theorem XiDH_zero_eq (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) :
    XiDH χ 0 = 2 * (1 + rootNumber χ⁻¹) * LamG χ (1 / 2) := by
  have heps := rootNumber_mul_rootNumber_inv χ hχ1 hprim
  have hFE := LamG_one_sub' (isPrimitive_inv χ hprim) (1 / 2)
  rw [inv_inv, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hFE
  show (1 + rootNumber χ⁻¹) * LamG χ (1 / 2 + I * 0) + (1 + rootNumber χ) * LamG χ⁻¹ (1 / 2 + I * 0) = _
  rw [mul_zero, add_zero, hFE]
  linear_combination (LamG χ (1 / 2)) * heps

theorem one_add_rootNumber_inv_ne_zero (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive)
    (h : 1 + rootNumber χ ≠ 0) : 1 + rootNumber χ⁻¹ ≠ 0 := by
  have heps := rootNumber_mul_rootNumber_inv χ hχ1 hprim
  intro h0
  apply h
  linear_combination rootNumber χ * h0 - heps

/-- **`Ξ_{DH}(0) ≠ 0`** when `ε_χ ≠ −1` and `L(½, χ) ≠ 0`. -/
theorem XiDH_zero_ne (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    (hhalf : LFunction χ (1 / 2) ≠ 0) : XiDH χ 0 ≠ 0 := by
  rw [XiDH_zero_eq hχ1 hprim]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (one_add_rootNumber_inv_ne_zero hχ1 hprim h1))
    (LamG_ne_zero (by norm_num) hhalf)

/-- **The Hadamard product of `Ξ_{DH}`**: its zeros, with multiplicity, have summable inverses and
`Ξ_{DH}(t)/Ξ_{DH}(0) = Π (1 − t²/u)` over the zeros `u` of `t ↦ Ξ_{DH}(√t)`. -/
theorem hadamard_XiDH (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    (hhalf : LFunction χ (1 / 2) ≠ 0) :
    HadamardW (XiDH χ) (fun i : ZeroIdx (sqF (XiDH χ)) => i.1⁻¹) :=
  hadamardW_even (differentiable_XiDH χ hχ1) (XiDH_even χ hχ1 hprim) (XiDH_zero_ne hχ1 hprim h1 hhalf)
    one_le_KDH (by norm_num) (by norm_num) (by norm_num) (norm_XiDH_le hχ1 hprim)

/-! ## The Davenport–Heilbronn function -/

/-- **The one named input of stage 2**: `L(½, χ₅) ≠ 0` (numerically `L(½, χ₅) ≈ 0.763748 + 0.216965i`, `|L(½, χ₅)| ≈ 0.793968`, by Hurwitz zeta in mpmath, not proved here). -/
def DHHalf : Prop := LFunction chi5 (1 / 2) ≠ 0

theorem norm_XiDH_chi5_le (t : ℂ) : ‖XiDH chi5 t‖ ≤ KDH chi5 * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) :=
  norm_XiDH_le chi5_ne_one chi5_isPrimitive t

theorem XiDH_chi5_zero_ne (h : DHHalf) : XiDH chi5 0 ≠ 0 :=
  XiDH_zero_ne chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero h

/-- **The Hadamard product of the Davenport–Heilbronn `Ξ`**, given `L(½, χ₅) ≠ 0`. -/
theorem hadamard_dh (h : DHHalf) :
    HadamardW (XiDH chi5) (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) :=
  hadamard_XiDH chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero h

end PsiOmega

#print axioms PsiOmega.norm_sum_cC_le
#print axioms PsiOmega.LFunction_eq_IχC
#print axioms PsiOmega.norm_LFunction_leC
#print axioms PsiOmega.norm_LamG_leC
#print axioms PsiOmega.LamG_one_sub'
#print axioms PsiOmega.norm_XiC_le'
#print axioms PsiOmega.norm_XiDH_le
#print axioms PsiOmega.XiDH_zero_eq
#print axioms PsiOmega.XiDH_zero_ne
#print axioms PsiOmega.hadamard_XiDH
#print axioms PsiOmega.norm_XiDH_chi5_le
#print axioms PsiOmega.hadamard_dh
