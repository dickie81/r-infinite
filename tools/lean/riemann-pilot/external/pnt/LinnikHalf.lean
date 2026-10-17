/-
# Round 521, part 4: the partial-summation bound for `L(½ + it, χ)` and Linnik's exponent `4 + η`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every Dirichlet character `χ ≠ 1` mod `q ≥ 1` and every real `t`,
`|L(½ + it, χ)| ≤ 11(q(|t| + 2))^{1/2}` (`norm_LFunction_half_le`). So `CritBoundχ (1/2)` holds (`critBoundχ_half`),
part 3 gives `CharDensity 4 10 C`, and every reduced class modulo every `q ≥ 1` has a prime `p ≤ K q^{4+η}` for every
`η > 0` (`linnik_four`), with no hypothesis. Round 520's `linnik_twelve` had the exponent `12 + η`.

* `Jf`, `LSeries_eq_Jf`, `Jf_differentiableAt`: for `f` with `|f(n)|` and `|Σ_{k≤n} f(k)|` bounded,
  `L(f, z) = z∫_1^∞ (Σ_{k≤t} f(k))t^{−z−1} dt` on `Re z > 1` (Mathlib's `LSeries_eq_mul_integral`), and the integral is
  holomorphic on `Re z > 0` (a Mellin transform, as in round 254's `PsiOmega.IχC_differentiableAt`).
* `norm_Jf_le`: if the partial sums are at most `B` and vanish up to `M ≥ 1`, the integral is at most
  `B M^{−Re z}/Re z`.
* `LFunction_split`: `L(s, χ) = Σ_{n≤M} χ(n)n^{−s} + s J_M(s)` on `Re s > 0`, with `J_M` the integral of the tail
  `χ(n)1_{n>M}` (`cT`, whose partial sums are at most `2(q + 1)` by round 254's `PsiOmega.norm_summC_le`): the identity
  on `Re s > 1` (`LSeries_cT`) continues by `LandauLaplace.eqOn_convex`.
* `norm_LFunction_half_le`: the split at `M = ⌈q(|t| + 2)⌉`, with `Σ_{n≤M} n^{−1/2} ≤ 2√M` (`sum_rpow_neg_half_le`) and
  `|s J_M(s)| ≤ 4(q + 1)|s|M^{−1/2}`.
-/
import LinnikDensity
import LFunctionGrowth

open Complex Real Filter Topology MeasureTheory Asymptotics

noncomputable section

namespace LinnikDensity

open DirichletCharacter Finset PsiOmega LandauLaplace

/-! ### Partial summation for a sequence with bounded partial sums -/

/-- `J_f(z) = ∫_1^∞ (Σ_{k ≤ t} f(k)) t^{−z−1} dt`. -/
def Jf (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(z + 1))

theorem Jf_eq_mellin (f : ℕ → ℂ) (z : ℂ) :
    Jf f z = mellin (fun x : ℝ => (Set.Ioi (1 : ℝ)).indicator (fun t => ∑ k ∈ Icc 1 ⌊t⌋₊, f k) x) (-z) := by
  unfold Jf mellin
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator (s := Set.Ioi 0) measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases h1 : x ∈ Set.Ioi (1 : ℝ)
  · have h0 : x ∈ Set.Ioi (0 : ℝ) := show (0 : ℝ) < x from lt_trans one_pos h1
    simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h0, smul_eq_mul]
    rw [mul_comm]; congr 2; ring
  · simp only [Set.indicator_of_notMem h1]
    by_cases h0 : x ∈ Set.Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem h0, Set.indicator_of_notMem h1]
    · simp [Set.indicator_of_notMem h0]

/-- `J_f` is holomorphic on `Re z > 0` when the partial sums of `f` are bounded. -/
theorem Jf_differentiableAt (f : ℕ → ℂ) {B : ℝ} (hB : ∀ n, ‖∑ k ∈ Icc 1 n, f k‖ ≤ B) {z : ℂ}
    (hz : 0 < z.re) : DifferentiableAt ℂ (Jf f) z := by
  set g : ℝ → ℂ := fun x => (Set.Ioi (1 : ℝ)).indicator (fun t => ∑ k ∈ Icc 1 ⌊t⌋₊, f k) x with hg
  have hSm : Measurable fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, f k :=
    (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, f k)).comp Nat.measurable_floor
  have hgm : Measurable g := hSm.indicator measurableSet_Ioi
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hgb : ∀ x, ‖g x‖ ≤ B := fun x => by
    by_cases h : x ∈ Set.Ioi (1 : ℝ)
    · simp only [hg, Set.indicator_of_mem h]; exact hB _
    · simp only [hg, Set.indicator_of_notMem h, norm_zero]; exact hB0
  have hloc : LocallyIntegrableOn g (Set.Ioi 0) :=
    ((locallyIntegrable_const ((B : ℝ) : ℂ)).mono hgm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg hB0]; exact hgb x)).locallyIntegrableOn _
  have htop : g =O[atTop] (· ^ (-(0 : ℝ))) :=
    IsBigO.of_bound B (Eventually.of_forall fun x => by
      simpa [Real.rpow_zero] using hgb x)
  have hbot : g =O[𝓝[>] 0] (· ^ (-((-z).re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have : x ∉ Set.Ioi (1 : ℝ) := fun h => by linarith [hx.2, show 1 < x from h]
    simp [hg, Set.indicator_of_notMem this]
  have hd : DifferentiableAt ℂ (mellin g) (-z) :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by simp; linarith) hbot (by linarith)
  have e : Jf f = fun z => mellin g (-z) := funext fun z => Jf_eq_mellin f z
  rw [e]
  exact hd.comp z differentiableAt_id.neg

/-- **`L(f, z) = z J_f(z)` on `Re z > 1`** for bounded `f` with bounded partial sums (Mathlib's
`LSeries_eq_mul_integral`). -/
theorem LSeries_eq_Jf (f : ℕ → ℂ) {B B' : ℝ} (hB : ∀ n, ‖∑ k ∈ Icc 1 n, f k‖ ≤ B) (hf : ∀ n, ‖f n‖ ≤ B')
    {z : ℂ} (hz : 1 < z.re) : LSeries f z = z * Jf f z := by
  have hS : LSeriesSummable f z := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hz
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ (0 : ℝ) :=
    IsBigO.of_bound B (Eventually.of_forall fun n => by
      rw [Real.rpow_zero, norm_one, mul_one]; exact hB n)
  exact LSeries_eq_mul_integral f le_rfl (by linarith) hS hO

/-- **The tail integral**: if the partial sums of `f` are bounded by `B` and vanish up to `M ≥ 1`, then
`|J_f(z)| ≤ B M^{−Re z}/Re z` on `Re z > 0`. -/
theorem norm_Jf_le (f : ℕ → ℂ) {B : ℝ} (hB : ∀ n, ‖∑ k ∈ Icc 1 n, f k‖ ≤ B) {M : ℕ} (hM : 1 ≤ M)
    (h0 : ∀ n, n ≤ M → ∑ k ∈ Icc 1 n, f k = 0) {z : ℂ} (hz : 0 < z.re) :
    ‖Jf f z‖ ≤ B * ((M : ℝ) ^ (-z.re) / z.re) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set σ := z.re with hσ
  have hint : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Set.Ioi (M : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)
  have hval : ∫ t in Set.Ioi (M : ℝ), t ^ (-σ - 1) = (M : ℝ) ^ (-σ) / σ := by
    rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith), show -σ - 1 + 1 = -σ by ring, neg_div_neg_eq]
  set h : ℝ → ℝ := (Set.Ioi (M : ℝ)).indicator (fun t => B * t ^ (-σ - 1)) with hh
  have hint2 : IntegrableOn (fun t : ℝ => B * t ^ (-σ - 1)) (Set.Ioi (M : ℝ)) := hint.const_mul B
  have hhint : IntegrableOn h (Set.Ioi 1) := (hint2.integrable_indicator measurableSet_Ioi).integrableOn
  have hbound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ‖(∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(z + 1))‖ ≤ h t := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) => ?_)
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(z + 1)).re = -σ - 1 := by simp [hσ]; ring
    rw [hre]
    by_cases htM : (M : ℝ) < t
    · rw [hh, Set.indicator_of_mem (show t ∈ Set.Ioi (M : ℝ) from htM)]
      exact mul_le_mul_of_nonneg_right (hB _) (by positivity)
    · push Not at htM
      rw [h0 _ (Nat.floor_le_of_le htM), norm_zero, zero_mul, hh,
        Set.indicator_of_notMem (by simpa using htM)]
  calc ‖Jf f z‖ ≤ ∫ t in Set.Ioi (1 : ℝ), h t := norm_integral_le_of_norm_le hhint hbound
    _ = ∫ t in Set.Ioi (M : ℝ), B * t ^ (-σ - 1) := by
        rw [hh, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.inter_eq_left.2 (Set.Ioi_subset_Ioi hM1)]
    _ = B * ((M : ℝ) ^ (-σ) / σ) := by rw [integral_const_mul, hval]

/-! ### The split of `L(s, χ)` at `M` -/

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

omit [NeZero N] in
/-- The tail `χ(n)·1_{n > M}`. -/
def cT (χ : DirichletCharacter ℂ N) (M n : ℕ) : ℂ := if M < n then χ n else 0

omit [NeZero N] in
theorem sum_cT (χ : DirichletCharacter ℂ N) (M n : ℕ) :
    ∑ k ∈ Icc 1 n, cT χ M k = ∑ k ∈ Icc 1 n, cC χ k - ∑ k ∈ Icc 1 (min n M), cC χ k := by
  have h1 : ∑ k ∈ Icc 1 n, cC χ k = ∑ k ∈ Icc 1 n, (cT χ M k + if k ≤ M then cC χ k else 0) := by
    refine sum_congr rfl fun k _ => ?_
    unfold cT cC
    by_cases h : M < k
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  have h2 : (Icc 1 n).filter (fun k => k ≤ M) = Icc 1 (min n M) := by
    ext k; simp only [mem_filter, mem_Icc, le_min_iff]; tauto
  rw [h1, sum_add_distrib, ← sum_filter, h2]
  ring

theorem norm_sum_cT_le (hχ1 : χ ≠ 1) (M n : ℕ) : ‖∑ k ∈ Icc 1 n, cT χ M k‖ ≤ 2 * (N + 1) := by
  rw [sum_cT]
  have h1 := norm_summC_le hχ1 (n : ℝ)
  have h2 := norm_summC_le hχ1 ((min n M : ℕ) : ℝ)
  simp only [summC, Nat.floor_natCast] at h1 h2
  calc _ ≤ ‖∑ k ∈ Icc 1 n, cC χ k‖ + ‖∑ k ∈ Icc 1 (min n M), cC χ k‖ := norm_sub_le _ _
    _ ≤ (N + 1) + (N + 1) := add_le_add h1 h2
    _ = 2 * (N + 1) := by ring

omit [NeZero N] in
theorem sum_cT_eq_zero (χ : DirichletCharacter ℂ N) {M n : ℕ} (h : n ≤ M) :
    ∑ k ∈ Icc 1 n, cT χ M k = 0 := by
  rw [sum_cT, min_eq_left h, sub_self]

/-- `L(cT, z) = L(z, χ) − Σ_{n ≤ M} χ(n)n^{−z}` on `Re z > 1`. -/
theorem LSeries_cT (χ : DirichletCharacter ℂ N) (M : ℕ) {z : ℂ} (hz : 1 < z.re) :
    LSeries (cT χ M) z = LFunction χ z - ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-z) := by
  have hs : LSeriesSummable (fun n : ℕ => χ n) z :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_le_one χ _) hz
  set b : ℕ → ℂ := fun n => if n ∈ Icc 1 M then LSeries.term (fun n : ℕ => χ n) z n else 0 with hb
  have hbsum : ∑' n, b n = ∑ n ∈ Icc 1 M, LSeries.term (fun n : ℕ => χ n) z n := by
    rw [tsum_eq_sum (s := Icc 1 M) (fun n hn => by simp only [hb]; exact ite_eq_right hn)]
    exact sum_congr rfl fun n hn => by simp only [hb]; exact ite_eq_left hn
  have hbs : Summable b :=
    summable_of_ne_finset_zero (s := Icc 1 M) (fun n hn => by simp only [hb]; exact ite_eq_right hn)
  have hterm : ∀ n, LSeries.term (cT χ M) z n = LSeries.term (fun n : ℕ => χ n) z n - b n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : b 0 = 0 := by simp only [hb]; exact ite_eq_right (by simp)
      rw [LSeries.term_zero, LSeries.term_zero, h0, sub_zero]
    · by_cases hnM : M < n
      · have hnot : n ∉ Icc 1 M := fun h => by have := (mem_Icc.1 h).2; omega
        have h0 : b n = 0 := by simp only [hb]; exact ite_eq_right hnot
        rw [h0, sub_zero, LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
        simp only [cT, ite_eq_left hnM]
      · have hin : n ∈ Icc 1 M := mem_Icc.2 ⟨hn, by omega⟩
        have h0 : b n = LSeries.term (fun n : ℕ => χ n) z n := by simp only [hb]; exact ite_eq_left hin
        rw [h0, sub_self, LSeries.term_of_ne_zero hn.ne']
        simp only [cT, ite_eq_right hnM, zero_div]
  rw [LFunction_eq_LSeries χ hz]
  unfold LSeries
  rw [tsum_congr hterm, Summable.tsum_sub hs hbs, hbsum]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [LSeries.term_of_ne_zero (by have := (mem_Icc.1 hn).1; omega), div_eq_mul_inv, ← cpow_neg]

/-- **The split at `M`**: `L(s, χ) = Σ_{n ≤ M} χ(n)n^{−s} + s J_M(s)` on `Re s > 0`, for `χ ≠ 1`, with
`J_M = J_f` at the tail `f = χ·1_{n > M}`. -/
theorem LFunction_split (hχ1 : χ ≠ 1) (M : ℕ) {z : ℂ} (hz : 0 < z.re) :
    LFunction χ z = ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-z) + z * Jf (cT χ M) z := by
  set U : Set ℂ := {s | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (fun s => LFunction χ s - ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)) U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (LFunction χ) w := differentiable_LFunction hχ1 w
    have h2 : DifferentiableAt ℂ (fun s => ∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)) w := by
      refine DifferentiableAt.fun_sum fun n hn => ?_
      have hn0 : (n : ℂ) ≠ 0 := by
        have := (mem_Icc.1 hn).1; exact_mod_cast (show n ≠ 0 by omega)
      exact (differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _
    exact (h1.sub h2).differentiableWithinAt
  have hG : DifferentiableOn ℂ (fun s => s * Jf (cT χ M) s) U := fun w hw =>
    (differentiableAt_id.mul (Jf_differentiableAt (cT χ M) (norm_sum_cT_le hχ1 M) hw)).differentiableWithinAt
  have heq := eqOn_convex hUo (convex_halfSpace_re_gt 0) hF hG (z0 := 2)
    (show (0 : ℝ) < (2 : ℂ).re by norm_num) (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
      have hcT : ∀ n, ‖cT χ M n‖ ≤ 1 := fun n => by
        unfold cT; split_ifs
        · exact norm_le_one χ _
        · simp
      rw [← LSeries_cT χ M hw]
      exact LSeries_eq_Jf (cT χ M) (norm_sum_cT_le hχ1 M) hcT hw) (show z ∈ U from hz)
  simp only at heq
  rw [← heq]
  ring

/-! ### The partial-summation bound and Linnik's exponent `4 + η` -/

/-- `Σ_{1 ≤ n ≤ M} n^{−1/2} ≤ 2√M`. -/
theorem sum_rpow_neg_half_le (M : ℕ) : ∑ n ∈ Icc 1 M, (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    have hb : 0 < Real.sqrt ((M : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have ha0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
    have ha2 : Real.sqrt M ^ 2 = M := Real.sq_sqrt (Nat.cast_nonneg M)
    have hb2 : Real.sqrt ((M : ℝ) + 1) ^ 2 = M + 1 := Real.sq_sqrt (by positivity)
    have hr : ((M : ℝ) + 1) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt ((M : ℝ) + 1) := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    rw [hr]
    have key : 2 * Real.sqrt M + 1 / Real.sqrt ((M : ℝ) + 1) ≤ 2 * Real.sqrt ((M : ℝ) + 1) := by
      rw [← sub_nonneg]
      have e : 2 * Real.sqrt ((M : ℝ) + 1) - (2 * Real.sqrt M + 1 / Real.sqrt ((M : ℝ) + 1))
          = (Real.sqrt ((M : ℝ) + 1) - Real.sqrt M) ^ 2 / Real.sqrt ((M : ℝ) + 1) := by
        field_simp
        nlinarith [ha2, hb2]
      rw [e]; positivity
    linarith

/-- **The partial-summation bound** `|L(½ + it, χ)| ≤ 11 (N(|t| + 2))^{1/2}` for every `χ ≠ 1` modulo `N`: the split at
`M = ⌈N(|t| + 2)⌉`, with `|Σ_{n ≤ M} χ(n)n^{−s}| ≤ 2√M` and `|s J_M(s)| ≤ 4(N + 1)|s| M^{−1/2}`. -/
theorem norm_LFunction_half_le (hχ1 : χ ≠ 1) (t : ℝ) :
    ‖LFunction χ (1 / 2 + t * I)‖ ≤ 11 * ((N : ℝ) * (|t| + 2)) ^ (1 / 2 : ℝ) := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  set x := (N : ℝ) * (|t| + 2) with hx
  have hx2 : 2 ≤ x := by nlinarith [abs_nonneg t]
  have hxpos : 0 < x := by linarith
  set M := ⌈x⌉₊ with hM
  have hxM : x ≤ M := Nat.le_ceil x
  have hMx : (M : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  rw [LFunction_split hχ1 M (by rw [hsre]; norm_num)]
  have hfin : ‖∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)‖ ≤ 2 * Real.sqrt M := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n hn => ?_).trans (sum_rpow_neg_half_le M))
    have hn0 : 0 < n := by have := (mem_Icc.1 hn).1; omega
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0]
    have hre : (-s).re = -(1 / 2) := by simp [hsre]
    rw [hre]
    calc ‖χ n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          gcongr; exact norm_le_one χ _
      _ = _ := one_mul _
  have htail := norm_Jf_le (cT χ M) (norm_sum_cT_le hχ1 M) hM1 (fun n hn => sum_cT_eq_zero χ hn)
    (z := s) (by rw [hsre]; norm_num)
  rw [hsre] at htail
  have hsnorm : ‖s‖ ≤ |t| + 2 := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = 1 / 2 + |t| := by rw [hsre, hsim]; norm_num
      _ ≤ |t| + 2 := by linarith
  have hMs : Real.sqrt M ≤ 3 / 2 * x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h1 : Real.sqrt M ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (2 * x) = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    have h3 : Real.sqrt 2 ≤ 3 / 2 := by
      calc Real.sqrt 2 ≤ Real.sqrt ((3 / 2) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
        _ = 3 / 2 := Real.sqrt_sq (by norm_num)
    have h4 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    nlinarith
  have hMr : (M : ℝ) ^ (-(1 / 2 : ℝ)) ≤ x ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hxpos hxM (by norm_num)
  have hxx : x * x ^ (-(1 / 2 : ℝ)) = x ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add hxpos (1 : ℝ) (-(1 / 2 : ℝ))
    rw [Real.rpow_one] at h
    rw [← h]; norm_num
  have hJ0 : 0 ≤ ‖Jf (cT χ M) s‖ := norm_nonneg _
  have hxr : 0 ≤ x ^ (-(1 / 2 : ℝ)) := by positivity
  have hNN : 2 * ((N : ℝ) + 1) ≤ 2 * (2 * N) := by linarith
  calc ‖∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s) + s * Jf (cT χ M) s‖
      ≤ ‖∑ n ∈ Icc 1 M, χ n * (n : ℂ) ^ (-s)‖ + ‖s‖ * ‖Jf (cT χ M) s‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 2 * Real.sqrt M + (|t| + 2) * (2 * (N + 1) * ((M : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2))) := by
        gcongr
    _ ≤ 2 * (3 / 2 * x ^ (1 / 2 : ℝ)) + (|t| + 2) * (2 * (2 * N) * (x ^ (-(1 / 2 : ℝ)) / (1 / 2))) := by
        gcongr
    _ = 3 * x ^ (1 / 2 : ℝ) + 8 * (x * x ^ (-(1 / 2 : ℝ))) := by rw [hx]; ring
    _ = 11 * x ^ (1 / 2 : ℝ) := by rw [hxx]; ring

/-- `CritBoundχ (1/2)`, with constant `11`. -/
theorem critBoundχ_half : CritBoundχ (1 / 2) :=
  ⟨11, fun _ _ _ hχ t => norm_LFunction_half_le hχ t⟩

/-- **Linnik's theorem with exponent `4 + η`**: `linnik_of_critBound` at the partial-summation bound `critBoundχ_half`
(`CharDensity 4 10 C`). For every `η > 0` there is `K` such that every reduced class modulo every `q ≥ 1` has a
prime `p ≤ K q^{4+η}`. -/
theorem linnik_four {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (4 + η) := by
  obtain ⟨K, hK⟩ := linnik_of_critBound (c := 1 / 2) (by norm_num) (by norm_num) critBoundχ_half hη
  refine ⟨K, fun q _ a ha => ?_⟩
  obtain ⟨p, hp1, hp2, hp3⟩ := hK q a ha
  have e : (2 : ℝ) + 4 * (1 / 2) + η = 4 + η := by ring
  exact ⟨p, hp1, hp2, by rwa [e] at hp3⟩

end LinnikDensity

#print axioms LinnikDensity.LFunction_split
#print axioms LinnikDensity.norm_LFunction_half_le
#print axioms LinnikDensity.critBoundχ_half
#print axioms LinnikDensity.linnik_four
