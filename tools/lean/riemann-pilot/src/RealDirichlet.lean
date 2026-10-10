import Mathlib
import DirichletOmega
import XiBounds

/-! # Real primitive Dirichlet characters: a zero, and a positivity criterion (round 224)

Round 223's `χ₄` argument, for every primitive real (quadratic) Dirichlet character `χ ≠ 1` of any
modulus `N` and either parity.

**Partial sums.** `|Σ_{k < n} χ(k)| ≤ N` (`abs_sum_cR_le`), since the sum over a period vanishes.
Partial summation then gives `L(s, χ) = s∫_1^∞ S(x)x^{−s−1}dx` on `Re s > 0` (`LFunction_eq_Iχ`), so
* `‖L(s, χ)‖ ≤ (N + 1)‖s‖/Re s` (`norm_LFunction_le`);
* `|L(σ, χ) − 1| ≤ (N + 2)/(σ − 1)` for `σ > 1` (`abs_LFunction_sub_one_le`);
* if every partial sum is `≥ 0`, `L(σ, χ) ≥ 1 − 2^{−σ} > 0` on `(0, ∞)` (`LFunction_real_ge`): no
  real zero, in particular no Siegel zero.

**A zero** (`exists_zero_of_primitive`). With `Λ*(s) = N^{s/2}Λ(s, χ)`, Mathlib's functional
equation gives `Λ*(1 − s) = εΛ*(s)` (`LamG_one_sub`). `f(z) = Λ*(½ + iz)Λ*(½ − iz)` is even and entire of
order `≤ 3/2` in `z` (`norm_fG_le`). If `L(s, χ)` had no zero with `½ ≤ Re ρ < 1`, `f` would have no
zeros, hence be constant by Hadamard (`hadamardW_even`); but `‖Λ*(σ)‖ ≥ k!/(2π^{k+1})` along
`σ = 2k + 2 − δ` (`norm_LamG_ge`). If `L(½, χ) = 0` the zero is `½` itself.

**Consequences.**
* `psiChi_omega_of_primitive`: `ψ(x, χ) = Ω±(x^θ)` for every `θ < ½`, given only that `L(σ, χ)` has no
  real zero in `(θ, 1)`.
* `psiChi_omega_of_sums_nonneg`: unconditionally, when the partial sums of `χ` are nonnegative.
* `hadamard_fG`: the genus-0 Hadamard product of `f` when `L(½, χ) ≠ 0`.

No bearing on RH. -/

open Real Complex MeasureTheory Filter Topology Set ArithmeticFunction

noncomputable section

namespace PsiOmega

open LandauLaplace DirichletCharacter Pilot1ca Pilot1bt

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **A nontrivial character of prime level is primitive** (round 335; `chi3_isPrimitive` in
`PrimeRaces.lean`, `WeilTwinGeneral.chi7_isPrimitive` and `chi5_isPrimitive` in `external/dh/` are its
cases). -/
theorem isPrimitive_of_prime_level {p : ℕ} (hp : p.Prime) {χ : DirichletCharacter ℂ p} (h : χ ≠ 1) :
    χ.IsPrimitive :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  (hp.eq_one_or_self_of_dvd _ (conductor_dvd_level χ)).resolve_left
    fun h1 => h (eq_one_iff_conductor_eq_one.2 h1)

/-! ## Partial sums -/

/-- `Re χ(n)`. -/
def cR (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ := (χ n).re

omit [NeZero N] in
theorem cR_ofReal (hq : χ.IsQuadratic) (n : ℕ) : (cR χ n : ℂ) = χ n := by
  rcases hq (n : ZMod N) with h | h | h <;> simp [cR, h]

omit [NeZero N] in
theorem isReal_of_isQuadratic (hq : χ.IsQuadratic) : IsReal χ := cR_ofReal hq

omit [NeZero N] in
theorem abs_cR_le (n : ℕ) : |cR χ n| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_le_one χ _)

omit [NeZero N] in
theorem sum_range_shift (g : ℕ → ℝ) (hper : ∀ k, g (k + N) = g k) (m : ℕ) :
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
    linarith

theorem sum_range_mod (g : ℕ → ℝ) (hper : ∀ k, g (k + N) = g k)
    (h0 : ∑ k ∈ Finset.range N, g k = 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, g k = ∑ k ∈ Finset.range (n % N), g k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n N with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_comm N m, Finset.sum_range_add, sum_range_shift g hper, h0, add_zero,
        Nat.add_mod_right]
      exact ih m (by have := NeZero.pos N; omega)

theorem sum_range_eq_univ (f : ZMod N → ℂ) :
    ∑ k ∈ Finset.range N, f k = ∑ a, f a := by
  refine Finset.sum_nbij' (fun k => (k : ZMod N)) (fun a => a.val) (fun _ _ => Finset.mem_univ _)
    (fun a _ => Finset.mem_range.2 (ZMod.val_lt a)) (fun k hk => ZMod.val_cast_of_lt
      (Finset.mem_range.1 hk)) (fun a _ => ZMod.natCast_zmod_val a) (fun _ _ => rfl)

/-- **The partial sums of a nontrivial `χ` are bounded by its modulus.** -/
theorem abs_sum_cR_le (hχ1 : χ ≠ 1) (n : ℕ) : |∑ k ∈ Finset.range n, cR χ k| ≤ N := by
  have hper : ∀ k, cR χ (k + N) = cR χ k := fun k => by simp [cR]
  have h0 : ∑ k ∈ Finset.range N, cR χ k = 0 := by
    have := congrArg Complex.re ((sum_range_eq_univ (fun a => χ a)).trans
      (MulChar.sum_eq_zero_of_ne_one hχ1))
    simpa [cR, Complex.re_sum] using this
  rw [sum_range_mod _ hper h0]
  calc |∑ k ∈ Finset.range (n % N), cR χ k| ≤ ∑ k ∈ Finset.range (n % N), |cR χ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n % N), (1 : ℝ) := Finset.sum_le_sum fun k _ => abs_cR_le k
    _ = (n % N : ℕ) := by simp
    _ ≤ N := by exact_mod_cast (Nat.mod_lt n (NeZero.pos N)).le

omit [NeZero N] in
theorem sum_Icc_eq (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, g k = ∑ k ∈ Finset.range (n + 1), g k - g 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (n + 1)]; ring

theorem abs_summ_cR_le (hχ1 : χ ≠ 1) (x : ℝ) : |summ (cR χ) x| ≤ N + 1 := by
  unfold summ
  rw [sum_Icc_eq]
  refine (abs_sub _ _).trans ?_
  linarith [abs_sum_cR_le hχ1 (⌊x⌋₊ + 1), abs_cR_le (χ := χ) 0]

omit [NeZero N] in
theorem summ_cR_eq_one {x : ℝ} (h1 : 1 ≤ x) (h2 : x < 2) : summ (cR χ) x = 1 := by
  unfold summ
  have : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]; norm_num; exact ⟨h1, h2⟩
  rw [this]; simp [cR]

omit [NeZero N] in
theorem summ_cR_zero {x : ℝ} (h : x < 1) : summ (cR χ) x = 0 := by
  unfold summ; rw [Nat.floor_eq_zero.2 h]; simp

theorem linBound_cR (hχ1 : χ ≠ 1) : LinBound (cR χ) (N + 1) := fun x hx => by
  rcases lt_or_ge x 1 with h | h
  · rw [summ_cR_zero h, abs_zero]; positivity
  · exact (abs_summ_cR_le hχ1 x).trans (le_mul_of_one_le_right (by positivity) h)

/-! ## `L(s, χ)` on `Re s > 0` by partial summation -/

/-- `I(s) = ∫_1^∞ S(x)x^{−s−1}dx`. -/
def Iχ (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (summ (cR χ) x : ℂ) * (x : ℂ) ^ (-(s + 1))

omit [NeZero N] in
theorem Iχ_eq_mellin (s : ℂ) :
    Iχ χ s = mellin (fun x : ℝ => (Ioi (1 : ℝ)).indicator (fun x => (summ (cR χ) x : ℂ)) x) (-s) := by
  unfold Iχ mellin
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

theorem Iχ_differentiableAt (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Iχ χ) s := by
  set g : ℝ → ℂ := fun x => (Ioi (1 : ℝ)).indicator (fun x => (summ (cR χ) x : ℂ)) x
  have hgm : Measurable g :=
    (Complex.continuous_ofReal.measurable.comp (measurable_summ _)).indicator measurableSet_Ioi
  have hgb : ∀ x, ‖g x‖ ≤ N + 1 := fun x => by
    by_cases h : x ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs]
      exact abs_summ_cR_le hχ1 x
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
  have e : Iχ χ = fun s => mellin g (-s) := funext Iχ_eq_mellin
  rw [e]
  exact hd.comp s differentiableAt_id.neg

omit [NeZero N] in
theorem LSeriesSummable_cR (hq : χ.IsQuadratic) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (cR χ n : ℂ)) s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => by
    rw [cR_ofReal hq, sub_self, Real.rpow_zero, mul_one]; exact norm_le_one χ _⟩

/-- **`L(s, χ) = s·∫_1^∞ S(x)x^{−s−1}dx` for `Re s > 0`.** -/
theorem LFunction_eq_Iχ (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * Iχ χ s := by
  set U : Set ℂ := {s | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hL : DifferentiableOn ℂ (LFunction χ) U := (differentiable_LFunction hχ1).differentiableOn
  have hR : DifferentiableOn ℂ (fun s => s * Iχ χ s) U := fun z hz =>
    (differentiableAt_id.mul (Iχ_differentiableAt hχ1 hz)).differentiableWithinAt
  refine eqOn_convex hUo (convex_halfSpace_re_gt 0) hL hR (z0 := 2)
    (show (0 : ℝ) < (2 : ℂ).re by norm_num) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; linarith
  have h := integral_summ (linBound_cR hχ1) hz (LSeriesSummable_cR hq hz)
  rw [show (fun n => (cR χ n : ℂ)) = fun n : ℕ => χ n from funext (cR_ofReal hq)] at h
  rw [LFunction_eq_LSeries χ hz]
  unfold Iχ; rw [h]; field_simp

theorem integral_rpow_Ioi_one' {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) = 1 / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, show -σ - 1 + 1 = -σ by ring]
  field_simp

/-- **`‖L(s, χ)‖ ≤ (N + 1)‖s‖/Re s`** on `Re s > 0`. -/
theorem norm_LFunction_le (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ (N + 1) * ‖s‖ / s.re := by
  rw [LFunction_eq_Iχ hχ1 hq hs, norm_mul]
  suffices hI : ‖Iχ χ s‖ ≤ (N + 1) * (1 / s.re) by
    calc ‖s‖ * ‖Iχ χ s‖ ≤ ‖s‖ * ((N + 1) * (1 / s.re)) := by gcongr
      _ = _ := by ring
  rw [← integral_rpow_Ioi_one' hs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  have hx0 : 0 < x := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have : (-(s + 1)).re = -s.re - 1 := by simp; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (abs_summ_cR_le hχ1 x) (by positivity)

omit [NeZero N] in
/-- The real integrand, for real `σ`. -/
theorem Iχ_real (σ : ℝ) :
    Iχ χ σ = ((∫ x in Ioi (1 : ℝ), summ (cR χ) x * x ^ (-σ - 1) : ℝ) : ℂ) := by
  unfold Iχ
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => ?_
  push_cast
  rw [Complex.ofReal_cpow (by linarith)]; congr 2; push_cast; ring

theorem integrableOn_summ_cR (hχ1 : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x => summ (cR χ) x * x ^ (-σ - 1)) (Ioi 1) := by
  refine ((integrableOn_Ioi_rpow_of_lt (show -σ - 1 < -1 by linarith) one_pos).const_mul
    ((N : ℝ) + 1)).mono'
    ((measurable_summ _).mul (by fun_prop)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_))
  have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_right (abs_summ_cR_le hχ1 x) hp

/-- **`|L(σ, χ) − 1| ≤ (N + 2)/(σ − 1)`** for real `σ > 1`: `|S(x) − 1| ≤ (N + 2)(x − 1)`. -/
theorem abs_LFunction_sub_one_le (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) {σ : ℝ} (hσ : 1 < σ) :
    ‖LFunction χ σ - 1‖ ≤ (N + 2) / (σ - 1) := by
  have hσ0 : 0 < σ := by linarith
  rw [LFunction_eq_Iχ hχ1 hq (by simpa using hσ0), Iχ_real, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (-σ - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hi0 : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  -- `σ∫S x^{−σ−1} − 1 = σ∫(S − 1)x^{−σ−1}`
  have e1 : σ * (∫ x in Ioi (1 : ℝ), summ (cR χ) x * x ^ (-σ - 1)) - 1
      = σ * ∫ x in Ioi (1 : ℝ), (summ (cR χ) x - 1) * x ^ (-σ - 1) := by
    rw [show (fun x : ℝ => (summ (cR χ) x - 1) * x ^ (-σ - 1))
        = fun x => summ (cR χ) x * x ^ (-σ - 1) - x ^ (-σ - 1) by funext x; ring,
      integral_sub (integrableOn_summ_cR hχ1 hσ0) hi1, integral_rpow_Ioi_one' hσ0]
    field_simp
  rw [e1, abs_mul, abs_of_pos hσ0]
  -- `∫(x − 1)x^{−σ−1} = 1/(σ − 1) − 1/σ`
  have hb : ∫ x in Ioi (1 : ℝ), (N + 2) * (x ^ (-σ) - x ^ (-σ - 1))
      = (N + 2) * (1 / (σ - 1) - 1 / σ) := by
    rw [integral_const_mul, integral_sub hi0 hi1, integral_rpow_Ioi_one' hσ0,
      integral_Ioi_rpow_of_lt (show -σ < -1 by linarith) one_pos, Real.one_rpow]
    have h1 : σ - 1 ≠ 0 := by linarith
    have h2 : -σ + 1 ≠ 0 := by linarith
    field_simp; ring
  have hle : |∫ x in Ioi (1 : ℝ), (summ (cR χ) x - 1) * x ^ (-σ - 1)|
      ≤ ∫ x in Ioi (1 : ℝ), (N + 2) * (x ^ (-σ) - x ^ (-σ - 1)) := by
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on ?_ ((hi0.sub hi1).const_mul _)
      measurableSet_Ioi fun x (hx : 1 < x) => ?_)
    · exact IntegrableOn.congr_fun (((integrableOn_summ_cR hχ1 hσ0).sub hi1).abs)
        (fun x _ => by simp only [Pi.sub_apply, sub_mul, one_mul]) measurableSet_Ioi
    have hx0 : 0 < x := by linarith
    have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
    have ex : x ^ (-σ) - x ^ (-σ - 1) = (x - 1) * x ^ (-σ - 1) := by
      have e : x ^ (-σ) = x ^ (-σ - 1) * x := by
        rw [← Real.rpow_add_one hx0.ne']; ring_nf
      rw [e]; ring
    rw [ex, abs_mul, abs_of_nonneg hp, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hp
    rcases lt_or_ge x 2 with h2 | h2
    · rw [summ_cR_eq_one hx.le h2, sub_self, abs_zero]; nlinarith
    · have := abs_summ_cR_le hχ1 x
      have : |summ (cR χ) x - 1| ≤ N + 2 := by
        refine (abs_sub _ _).trans ?_; simp; linarith
      nlinarith
  calc σ * |∫ x in Ioi (1 : ℝ), (summ (cR χ) x - 1) * x ^ (-σ - 1)|
      ≤ σ * ((N + 2) * (1 / (σ - 1) - 1 / σ)) := by rw [← hb]; gcongr
    _ = (N + 2) / (σ - 1) := by
        have : σ - 1 ≠ 0 := by linarith
        field_simp; ring

/-! ## Positivity from nonnegative partial sums -/

/-- **Nonnegative partial sums force `L(σ, χ) ≥ 1 − 2^{−σ} > 0` on `(0, ∞)`.** -/
theorem LFunction_real_ge (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) (hS : ∀ x, 0 ≤ summ (cR χ) x)
    {σ : ℝ} (hσ : 0 < σ) : 1 - (2 : ℝ) ^ (-σ) ≤ (LFunction χ σ).re := by
  rw [LFunction_eq_Iχ hχ1 hq (by simpa using hσ), Iχ_real, ← Complex.ofReal_mul, ofReal_re]
  have hlow : ∫ x in Ioo (1 : ℝ) 2, x ^ (-σ - 1) ≤ ∫ x in Ioi (1 : ℝ), summ (cR χ) x * x ^ (-σ - 1) := by
    calc ∫ x in Ioo (1 : ℝ) 2, x ^ (-σ - 1) = ∫ x in Ioo (1 : ℝ) 2, summ (cR χ) x * x ^ (-σ - 1) :=
          setIntegral_congr_fun measurableSet_Ioo fun x hx => by
            simp only [summ_cR_eq_one hx.1.le hx.2, one_mul]
      _ ≤ _ := setIntegral_mono_set (integrableOn_summ_cR hχ1 hσ) ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun x (hx : 1 < x) =>
              mul_nonneg (hS x) (Real.rpow_nonneg (by linarith) _)))
            (Eventually.of_forall Ioo_subset_Ioi_self)
  have hval : ∫ x in Ioo (1 : ℝ) 2, x ^ (-σ - 1) = (1 - (2 : ℝ) ^ (-σ)) / σ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      integral_rpow (Or.inr ⟨by linarith, by norm_num [Set.mem_uIcc]⟩)]
    rw [show -σ - 1 + 1 = -σ by ring, Real.one_rpow]
    field_simp; ring
  rw [hval] at hlow
  have := mul_le_mul_of_nonneg_left hlow hσ.le
  rwa [mul_div_cancel₀ _ hσ.ne'] at this

theorem LFunction_ne_zero_of_sums_nonneg (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic)
    (hS : ∀ x, 0 ≤ summ (cR χ) x) {σ : ℝ} (hσ : 0 < σ) : LFunction χ σ ≠ 0 := fun h => by
  have := LFunction_real_ge hχ1 hq hS hσ
  rw [h, zero_re] at this
  have : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

/-! ## The completed function and its growth -/

omit [NeZero N] in
theorem gammaFactor_shift (χ : DirichletCharacter ℂ N) :
    ∃ δ : ℕ, δ ≤ 1 ∧ ∀ s, gammaFactor χ s = Gammaℝ (s + δ) := by
  rcases χ.even_or_odd with h | h
  · exact ⟨0, by norm_num, fun s => by rw [h.gammaFactor_def]; simp⟩
  · exact ⟨1, le_rfl, fun s => by rw [h.gammaFactor_def]; simp⟩

omit [NeZero N] in
theorem gammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  obtain ⟨δ, -, hδ⟩ := gammaFactor_shift χ
  rw [hδ]; exact Gammaℝ_ne_zero_of_re_pos (by simp; positivity)

theorem completed_eq_mul {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = gammaFactor χ s * LFunction χ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl _ hs
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
  field_simp [gammaFactor_ne_zero hs]

/-- `Λ*(s) = N^{s/2}Λ(s, χ)`. -/
def LamG (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := (N : ℂ) ^ (s / 2) * completedLFunction χ s

theorem natCast_ne_zero' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)

theorem differentiable_LamG (hχ1 : χ ≠ 1) : Differentiable ℂ (LamG χ) :=
  ((differentiable_id.div_const 2).const_cpow (Or.inl natCast_ne_zero')).mul
    (differentiable_completedLFunction hχ1)

/-- **`Λ*(1 − s) = εΛ*(s)`** for primitive real `χ`. -/
theorem LamG_one_sub (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive) (s : ℂ) :
    LamG χ (1 - s) = rootNumber χ * LamG χ s := by
  unfold LamG
  rw [hprim.completedLFunction_one_sub, hq.inv]
  have e : (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) = (N : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ natCast_ne_zero']; congr 1; ring
  linear_combination (rootNumber χ * completedLFunction χ s) * e

omit [NeZero N] in
theorem norm_cGamma_le' {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq
    (setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

omit [NeZero N] in
theorem rGamma_le' {x : ℝ} (hx : 1 / 4 ≤ x) {n : ℕ} (hn : x + 2 ≤ n + 1) :
    Real.Gamma x ≤ 4 * n.factorial := by
  have hx0 : 0 < x := by linarith
  have h2 : Real.Gamma (x + 2) = (x + 1) * x * Real.Gamma x := by
    rw [show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
      Real.Gamma_add_one hx0.ne']; ring
  have hmono : Real.Gamma (x + 2) ≤ Real.Gamma (n + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ≤ x + 2 by linarith)
      (show (2 : ℝ) ≤ n + 1 by linarith) hn
  rw [Real.Gamma_nat_eq_factorial] at hmono
  have hG := Real.Gamma_pos_of_pos hx0
  have hxx : 1 / 4 ≤ (x + 1) * x := by nlinarith
  nlinarith

omit [NeZero N] in
theorem norm_Gammaℝ_le' {w : ℂ} (hw : 0 < w.re) : ‖Gammaℝ w‖ ≤ Real.Gamma (w.re / 2) := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : π ^ (-w / 2).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by simp; linarith)
  have h2 := norm_cGamma_le' (w := w / 2) (by simp; linarith)
  have e : (w / 2).re = w.re / 2 := by simp
  rw [e] at h2
  calc π ^ (-w / 2).re * ‖Complex.Gamma (w / 2)‖ ≤ 1 * Real.Gamma (w.re / 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **`‖Λ*(w)‖ ≤ n^{3n}`** on `Re w ≥ ½`, for `n ≥ ‖w‖ + 3`, `n ≥ N + 1`, `n ≥ 4`. -/
theorem norm_LamG_le (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) {w : ℂ} (hw : 1 / 2 ≤ w.re) {n : ℕ}
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
    refine (norm_LFunction_le hχ1 hq (by linarith)).trans ?_
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

omit [NeZero N] in
/-- `(x + M)√(x + M) ≤ 3x√x + 3M√M` for `x, M ≥ 0`. -/
theorem shift_sqrt {x M : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M) :
    (x + M) * Real.sqrt (x + M) ≤ 3 * (x * Real.sqrt x) + 3 * (M * Real.sqrt M) := by
  have key : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → v ≤ u → (u + v) * Real.sqrt (u + v) ≤ 3 * (u * Real.sqrt u) := by
    intro u v hu hv hvu
    have h : Real.sqrt (u + v) ≤ 3 / 2 * Real.sqrt u := by
      rw [show 3 / 2 * Real.sqrt u = Real.sqrt ((3 / 2) ^ 2 * u) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have := mul_le_mul (show u + v ≤ 2 * u by linarith) h (Real.sqrt_nonneg _) (by linarith)
    linarith
  rcases le_total M x with h | h
  · have := key x M hx hM h; nlinarith [mul_nonneg hM (Real.sqrt_nonneg M)]
  · have := key M x hM hx h; rw [add_comm] at this; nlinarith [mul_nonneg hx (Real.sqrt_nonneg x)]

/-! ## The zero -/

/-- `f(z) = Λ*(½ + iz)Λ*(½ − iz)`. -/
def fG (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ := LamG χ (1 / 2 + I * z) * LamG χ (1 / 2 - I * z)

theorem fG_even (z : ℂ) : fG χ (-z) = fG χ z := by
  unfold fG; rw [mul_comm]; congr 2 <;> ring

theorem fG_eq (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive) (z : ℂ) :
    fG χ z = rootNumber χ * LamG χ (1 / 2 + I * z) ^ 2 := by
  unfold fG
  rw [show 1 / 2 - I * z = 1 - (1 / 2 + I * z) by ring, LamG_one_sub hq hprim]; ring

theorem differentiable_fG (hχ1 : χ ≠ 1) : Differentiable ℂ (fG χ) :=
  ((differentiable_LamG hχ1).comp ((differentiable_const _).add (differentiable_const _ |>.mul
    differentiable_id))).mul
  ((differentiable_LamG hχ1).comp ((differentiable_const _).sub (differentiable_const _ |>.mul
    differentiable_id)))

/-- **The order of `f`**: `‖f(z)‖ ≤ (‖ε‖ + 1)e^{36M√M}·exp(36‖z‖^{3/2})`, `M = N + 5`. -/
theorem norm_fG_le (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive) (z : ℂ) :
    ‖fG χ z‖ ≤ (‖rootNumber χ‖ + 1) * Real.exp (36 * (((N : ℝ) + 5) * Real.sqrt ((N : ℝ) + 5)))
      * Real.exp (36 * ‖z‖ ^ (3 / 2 : ℝ)) := by
  set x := ‖z‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg z
  set M : ℝ := (N : ℝ) + 5
  have hM : 0 ≤ M := by positivity
  obtain ⟨w, hw, hwn, hfw⟩ : ∃ w : ℂ, 1 / 2 ≤ w.re ∧ ‖w‖ ≤ 1 / 2 + x ∧
      fG χ z = rootNumber χ * LamG χ w ^ 2 := by
    have hn1 : ‖1 / 2 + I * z‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
    have hn2 : ‖1 / 2 + I * -z‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
    rcases le_total (1 / 2) (1 / 2 + I * z).re with h | h
    · exact ⟨_, h, hn1, fG_eq hq hprim z⟩
    · refine ⟨1 / 2 + I * -z, ?_, hn2, by rw [← fG_eq hq hprim, fG_even]⟩
      simp only [add_re, mul_re, I_re, I_im, neg_re, neg_im] at h ⊢; norm_num at h ⊢; linarith
  set n : ℕ := ⌈x⌉₊ + N + 4
  have hnx : (n : ℝ) ≤ x + M := by
    have := Nat.ceil_lt_add_one hx0; simp only [n, M]; push_cast; linarith
  have hxn : x + N + 4 ≤ (n : ℝ) := by
    have := Nat.le_ceil x; simp only [n]; push_cast; linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hL := norm_LamG_le hχ1 hq hw (n := n) (by linarith) (by linarith) (by simp only [n]; omega)
  have hL2 : ‖LamG χ w‖ ^ 2 ≤ Real.exp (12 * ((n : ℝ) * Real.sqrt n)) := by
    calc ‖LamG χ w‖ ^ 2 ≤ ((n : ℝ) ^ (3 * n)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hL 2
      _ = Real.exp ((6 * n : ℝ) * Real.log n) := by
          rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hn0]; push_cast; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          have hl := log_le_two_sqrt hn0
          nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hns : (n : ℝ) * Real.sqrt n ≤ 3 * (x * Real.sqrt x) + 3 * (M * Real.sqrt M) :=
    le_trans (mul_le_mul hnx (Real.sqrt_le_sqrt hnx) (Real.sqrt_nonneg _) (by linarith))
      (shift_sqrt hx0 hM)
  have hx32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx0 (by norm_num), Real.rpow_one]
  rw [hx32, hfw, norm_mul, norm_pow]
  calc ‖rootNumber χ‖ * ‖LamG χ w‖ ^ 2
      ≤ (‖rootNumber χ‖ + 1) * Real.exp (12 * ((n : ℝ) * Real.sqrt n)) :=
        mul_le_mul (by linarith) hL2 (by positivity) (by positivity)
    _ ≤ (‖rootNumber χ‖ + 1) * Real.exp (12 * (3 * (x * Real.sqrt x) + 3 * (M * Real.sqrt M))) := by
        gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **`‖Λ*(2k + 2 − δ)‖ ≥ k!/(2π^{k+1})`** once `L(σ) ≥ ½` there (`k ≥ N + 2`). -/
theorem norm_LamG_ge (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) {δ : ℕ} (hδ1 : δ ≤ 1)
    (hδ : ∀ s, gammaFactor χ s = Gammaℝ (s + δ)) {k : ℕ} (hk : N + 2 ≤ k) :
    k.factorial / (2 * π ^ (k + 1)) ≤ ‖LamG χ ((2 * k + 2 - δ : ℝ) : ℂ)‖ := by
  set σ : ℝ := 2 * k + 2 - δ
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hk' : (N : ℝ) + 2 ≤ k := by exact_mod_cast hk
  have hσ1 : 2 * N + 5 ≤ σ := by simp only [σ]; linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  unfold LamG
  rw [completed_eq_mul (by simp; linarith), norm_mul, norm_mul, hδ]
  have hc : 1 ≤ ‖(N : ℂ) ^ ((σ : ℂ) / 2)‖ := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.one_le_rpow hN1 (by simp; linarith)
  have hΓ : ‖Gammaℝ ((σ : ℂ) + δ)‖ = k.factorial / π ^ (k + 1) := by
    have e0 : (σ : ℂ) + δ = 2 * ((k : ℕ) : ℂ) + 2 := by simp only [σ]; push_cast; ring
    rw [e0, Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have e1 : (2 * ((k : ℕ) : ℂ) + 2) / 2 = ((k : ℕ) : ℂ) + 1 := by ring
    have e2 : (-(2 * ((k : ℕ) : ℂ) + 2) / 2).re = -((k + 1 : ℕ) : ℝ) := by simp; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.norm_natCast, Real.rpow_neg Real.pi_pos.le,
      Real.rpow_natCast]
    field_simp
  have hL : 1 / 2 ≤ ‖LFunction χ σ‖ := by
    have h := abs_LFunction_sub_one_le hχ1 hq (σ := σ) (by linarith)
    have h2 : ((N : ℝ) + 2) / (σ - 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have := norm_sub_norm_le (1 : ℂ) (LFunction χ σ)
    rw [norm_one, norm_sub_rev] at this
    linarith
  rw [hΓ]
  have hp : 0 < π ^ (k + 1) := by positivity
  calc (k.factorial : ℝ) / (2 * π ^ (k + 1)) = 1 * ((k.factorial : ℝ) / π ^ (k + 1) * (1 / 2)) := by
        field_simp
    _ ≤ _ := by gcongr

/-- **Every primitive real Dirichlet character `χ ≠ 1` has an L-function zero with
`½ ≤ Re ρ < 1`.** -/
theorem exists_zero_of_primitive (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    ∃ ρ : ℂ, LFunction χ ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
  by_contra hno
  push Not at hno
  have hlt : ∀ ρ, LFunction χ ρ = 0 → ρ.re < 1 / 2 := fun ρ h => by
    by_contra h'; push Not at h'
    have h1 : ρ.re < 1 := by
      by_contra h''; exact LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (not_lt.1 h'') h
    exact absurd h1 (not_lt.2 (hno ρ h h'))
  have hLam : ∀ w, LamG χ w ≠ 0 := by
    intro w hw
    have hw' : LamG χ (1 - w) = 0 := by rw [LamG_one_sub hq hprim, hw, mul_zero]
    have key : ∀ v, LamG χ v = 0 → 1 / 2 ≤ v.re → False := fun v hv hre => by
      unfold LamG at hv
      rw [completed_eq_mul (by linarith)] at hv
      rcases mul_eq_zero.1 hv with h | h
      · rw [cpow_eq_zero_iff] at h; exact natCast_ne_zero' h.1
      · rcases mul_eq_zero.1 h with h | h
        · exact gammaFactor_ne_zero (by linarith) h
        · linarith [hlt v h]
    rcases le_total (1 / 2) w.re with h | h
    · exact key w hw h
    · exact key (1 - w) hw' (by simp; linarith)
  have hfne : ∀ z, fG χ z ≠ 0 := fun z => mul_ne_zero (hLam _) (hLam _)
  have hf0 := hfne 0
  have hε : rootNumber χ ≠ 0 := fun h => by
    have := fG_eq hq hprim 0; rw [h, zero_mul] at this; exact hf0 this
  have H := hadamardW_even (differentiable_fG hχ1) fG_even hf0 (A := 36) (β := 3 / 2)
    (C := (‖rootNumber χ‖ + 1) * Real.exp (36 * (((N : ℝ) + 5) * Real.sqrt ((N : ℝ) + 5))))
    (by nlinarith [norm_nonneg (rootNumber χ), Real.one_le_exp (show (0 : ℝ) ≤ 36 * (((N : ℝ) + 5) *
      Real.sqrt ((N : ℝ) + 5)) by positivity)])
    (by norm_num) (by norm_num) (by norm_num) (norm_fG_le hχ1 hq hprim)
  have : IsEmpty (ZeroIdx (sqF (fG χ))) := ⟨fun i => by
    have h := (ordN_ne_zero_iff (sqF_differentiable (differentiable_fG hχ1) fG_even)
      (by rw [sqF_zero]; exact hf0) i.1).1 (Nat.pos_iff_ne_zero.1 (Fin.pos i.2))
    exact hfne _ h⟩
  have hconst : ∀ z, fG χ z = fG χ 0 := fun z => by
    have := (H.prod z).unique hasProd_empty
    rwa [div_eq_one_iff_eq hf0] at this
  -- `‖Λ*(σ)‖² = ‖f(0)‖/‖ε‖` on the reals
  set K := ‖fG χ 0‖ / ‖rootNumber χ‖
  have hK0 : 0 ≤ K := by positivity
  have hreal : ∀ σ : ℝ, ‖LamG χ σ‖ ≤ K + 1 := fun σ => by
    have hz : fG χ (-I * ((σ : ℂ) - 1 / 2)) = rootNumber χ * LamG χ σ ^ 2 := by
      rw [fG_eq hq hprim]; congr 2
      rw [show I * (-I * ((σ : ℂ) - 1 / 2)) = -(I * I) * ((σ : ℂ) - 1 / 2) by ring, I_mul_I]
      ring_nf
    rw [hconst] at hz
    have hn : ‖LamG χ σ‖ ^ 2 = K := by
      simp only [K]; rw [hz, norm_mul, norm_pow]
      field_simp [norm_ne_zero_iff.2 hε]
    nlinarith [norm_nonneg (LamG χ σ)]
  -- but `k!/π^{k+1}` is unbounded
  obtain ⟨δ, hδ1, hδ⟩ := gammaFactor_shift χ
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop π
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * π * (K + 2)) by positivity))).and
    (eventually_ge_atTop (N + 2))
  obtain ⟨k, hk1, hk2⟩ := hev.exists
  have hge := norm_LamG_ge hχ1 hq hδ1 hδ hk2
  have hle := hreal (2 * k + 2 - δ)
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hπ := Real.pi_pos
  -- `π^k/k! < 1/(2π(K + 2))` gives `k!/(2π^{k+1}) > K + 2`
  have : K + 2 < k.factorial / (2 * π ^ (k + 1)) := by
    rw [lt_div_iff₀ (by positivity), pow_succ]
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at hk1
    nlinarith
  linarith

/-! ## The Hadamard product -/

theorem LamG_ne_zero {s : ℂ} (hs : 0 < s.re) (hL : LFunction χ s ≠ 0) : LamG χ s ≠ 0 := by
  unfold LamG; rw [completed_eq_mul hs]
  exact mul_ne_zero (by rw [Ne, cpow_eq_zero_iff]; exact fun h => natCast_ne_zero' h.1)
    (mul_ne_zero (gammaFactor_ne_zero hs) hL)

/-- **Hadamard's product for `Λ*(½ + iz)Λ*(½ − iz)`** (genus 0 in `z²`), for primitive real `χ`
with `L(½, χ) ≠ 0`: `f(z) = f(0)Π(1 − z²/u)` over the zeros `u` of `f(√w)`. -/
theorem hadamard_fG (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (h0 : LFunction χ (1 / 2) ≠ 0) :
    HadamardW (fG χ) (fun i : ZeroIdx (sqF (fG χ)) => i.1⁻¹) := by
  have hL : LamG χ (1 / 2) ≠ 0 := LamG_ne_zero (by norm_num) h0
  have hf0 : fG χ 0 ≠ 0 := by
    unfold fG; simp only [mul_zero, add_zero, sub_zero]; exact mul_ne_zero hL hL
  exact hadamardW_even (differentiable_fG hχ1) fG_even hf0 (A := 36) (β := 3 / 2)
    (C := (‖rootNumber χ‖ + 1) * Real.exp (36 * (((N : ℝ) + 5) * Real.sqrt ((N : ℝ) + 5))))
    (by nlinarith [norm_nonneg (rootNumber χ), Real.one_le_exp (show (0 : ℝ) ≤ 36 * (((N : ℝ) + 5) *
      Real.sqrt ((N : ℝ) + 5)) by positivity)])
    (by norm_num) (by norm_num) (by norm_num) (norm_fG_le hχ1 hq hprim)

/-! ## Ω± for `ψ(x, χ)` -/

/-- **For every primitive real `χ ≠ 1` and `0 < θ < ½`**, if `L(σ, χ)` has no real zero in
`(θ, 1)`, then `ψ(x, χ) = Ω±(x^θ)`. -/
theorem psiChi_omega_of_primitive (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (hS : ∀ σ : ℝ, θ < σ → σ < 1 → LFunction χ σ ≠ 0)
    (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < summ (fχ χ) x) ∧ (∃ x, X < x ∧ summ (fχ χ) x < -(c * x ^ θ)) := by
  obtain ⟨ρ, hρ, hre, -⟩ := exists_zero_of_primitive hχ1 hq hprim
  exact psiChi_omega hχ1 (isReal_of_isQuadratic hq) hρ hθ (by linarith) hS c X

/-- **Unconditionally**, if moreover the partial sums of `χ` are nonnegative. -/
theorem psiChi_omega_of_sums_nonneg (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hsum : ∀ x, 0 ≤ summ (cR χ) x) {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < summ (fχ χ) x) ∧ (∃ x, X < x ∧ summ (fχ χ) x < -(c * x ^ θ)) :=
  psiChi_omega_of_primitive hχ1 hq hprim hθ hθ2
    (fun σ hσ _ => LFunction_ne_zero_of_sums_nonneg hχ1 hq hsum (by linarith)) c X

end PsiOmega

#print axioms PsiOmega.LFunction_eq_Iχ
#print axioms PsiOmega.abs_LFunction_sub_one_le
#print axioms PsiOmega.LFunction_real_ge
#print axioms PsiOmega.exists_zero_of_primitive
#print axioms PsiOmega.psiChi_omega_of_primitive
#print axioms PsiOmega.psiChi_omega_of_sums_nonneg
#print axioms PsiOmega.hadamard_fG
#print axioms PsiOmega.isPrimitive_of_prime_level
