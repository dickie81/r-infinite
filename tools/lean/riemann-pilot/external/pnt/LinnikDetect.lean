/-
# Round 521, part 2: zero detection for `L(s, χ)`, `χ ≠ 1`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `χ ≠ 1` be a Dirichlet character mod `q` and `ρ = β + iγ` a zero of `L(·, χ)` with `½ < β < 1`.
For `X, N ≥ 1`, `Y ≥ 8` and `XN ≥ 22Y log Y`, the polynomial `P_χ(ρ) = Σ_{X<j≤XN} b_jχ(j)j^{−ρ}`,
`b_j = a_j e^{−j/Y}` with `a_j = Σ_{d | j, d ≤ X} μ(d)` (`Pvχ`; round 518's `InghamDensity.b1`), and the integral
`I_χ(ρ) = (1/2π)∫ G_χ(½ − β + iv) dv` (`Ivχ`) satisfy `|P_χ(ρ)| ≥ ¼` or `|I_χ(ρ)| ≥ ¼` (`dichotomy`). Here
`G_χ(w) = M_X(ρ + w, χ)·(L(ρ + w, χ)/w)·Γ(w + 1)·Y^w` (`Gχ`), with the mollifier `M_X(s, χ) = Σ_{m≤X} μ(m)χ(m)m^{−s}`
(`mollχ`). This is round 518's detection for `ζ` twisted by `χ`; since `L(·, χ)` has no pole, the pole class of round
518's `trichotomy` does not occur.

* `LSeries_aXχ`: `M_X(s, χ)L(s, χ) = Σ_n a_nχ(n)n^{−s}` on `Re s > 1` (`aXχ_eq_conv`: the coefficients are the
  convolution of `μχ·1_{≤X}` with `χ`).
* `Gχ_eq_LSeries`, `Gχ_eq_left`: on `Re(ρ + w) > 1`, `G_χ(w) = L(aχ, ρ + w)Γ(w)Y^w`; for `w ≠ 0`,
  `G_χ(w) = M_X(ρ + w, χ)L(ρ + w, χ)Γ(w + 1)Y^w/w`.
* `Gχ_strip_bound`, `Gχ_decay`: `|G_χ(w)|(1 + |Im w|)³` is bounded on `½ − β ≤ Re w ≤ 2` (round 520's
  `Linnik.LFunction_growth` and round 518's `InghamDensity.norm_Gamma_le'`).
* `detect_identityχ`: `Σ_n a_nχ(n)n^{−ρ}e^{−n/Y} = (1/2π)∫ G_χ(½ − β + iv) dv`: round 520's `Linnik.perron_exp` gives
  the integral on `Re w = 2`, and the line moves to `Re w = ½ − β` (`SmoothPerron.verticalIntegral_shift`); `G_χ` is
  holomorphic on `Re w > −1`, since `L(ρ + w, χ)/w` (Mathlib's `dslope`) is entire at the zero `ρ`.
* `dichotomy`: the series is `e^{−1/Y} + P_χ(ρ) + (the terms beyond XN)` (`a_1 = 1`, `a_n = 0` for `2 ≤ n ≤ X`),
  with `e^{−1/Y} ≥ 7/8` and the terms beyond `XN` at most `1/16` (`tailχ_le`).
-/
import LinnikChar

open Complex Set Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikDetect

open InghamDensity Linnik DirichletCharacter

variable {q : ℕ} [NeZero q]

/-! ### The coefficients of `M_X(s, χ)L(s, χ)` -/

/-- `μ(n)χ(n)` cut at `X`. -/
def muXχ (χ : DirichletCharacter ℂ q) (X n : ℕ) : ℂ := χ n * muX X n

/-- `χ(n)a_n`, `a_n = Σ_{d | n, d ≤ X} μ(d)`: the coefficients of `M_X(s, χ)L(s, χ)`. -/
def aXχ (χ : DirichletCharacter ℂ q) (X n : ℕ) : ℂ := χ n * aX X n

/-- `M_X(s, χ) = Σ_{m ≤ X} μ(m)χ(m)m^{−s}`. -/
def mollχ (χ : DirichletCharacter ℂ q) (X : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 X, ((ArithmeticFunction.moebius m : ℤ) : ℂ) * χ m * (m : ℂ) ^ (-s)

omit [NeZero q] in
theorem aXχ_eq_conv (χ : DirichletCharacter ℂ q) (X : ℕ) :
    aXχ χ X = LSeries.convolution (muXχ χ X) (fun n => χ n) := by
  funext n
  rw [LSeries.convolution_def]
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b => muXχ χ X a * χ b)]
  simp only [aXχ, aX, muXχ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  have hχ : χ (d : ZMod q) * χ ((n / d : ℕ) : ZMod q) = χ (n : ZMod q) := by
    rw [← map_mul, ← Nat.cast_mul, hdn]
  by_cases h : d ≤ X
  · simp only [muX, h, ↓reduceIte]; rw [← hχ]; ring
  · simp only [muX, h, ↓reduceIte]; ring

omit [NeZero q] in
theorem muXχ_summable (χ : DirichletCharacter ℂ q) (X : ℕ) (s : ℂ) : LSeriesSummable (muXχ χ X) s := by
  refine summable_of_ne_finset_zero (s := Finset.Ioc 0 X) fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero hpos.ne', muXχ, muX,
      ite_eq_right fun h => hn (Finset.mem_Ioc.2 ⟨hpos, h⟩), mul_zero, zero_div]

omit [NeZero q] in
theorem LSeries_muXχ (χ : DirichletCharacter ℂ q) (X : ℕ) (s : ℂ) : LSeries (muXχ χ X) s = mollχ χ X s := by
  rw [LSeries, tsum_eq_sum (s := Finset.Ioc 0 X) fun n hn => ?_]
  · unfold mollχ
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h0, hX⟩ := Finset.mem_Ioc.1 hn
    rw [LSeries.term_of_ne_zero (by omega), muXχ, muX, ite_eq_left hX, Complex.cpow_neg, div_eq_mul_inv]
    ring
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero hpos.ne', muXχ, muX,
        ite_eq_right fun h => hn (Finset.mem_Ioc.2 ⟨hpos, h⟩), mul_zero, zero_div]

/-- `Σ χ(n)a_n n^{−s} = M_X(s, χ)L(s, χ)` on `Re s > 1`. -/
theorem LSeries_aXχ (χ : DirichletCharacter ℂ q) (X : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (aXχ χ X) s = mollχ χ X s * LFunction χ s := by
  rw [aXχ_eq_conv, LSeries_convolution' (muXχ_summable χ X s) (LSeriesSummable_of_one_lt_re χ hs),
    LSeries_muXχ, LFunction_eq_LSeries χ hs]

omit [NeZero q] in
theorem LSeriesSummable_aXχ (χ : DirichletCharacter ℂ q) (X : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (aXχ χ X) s := by
  rw [aXχ_eq_conv]; exact (muXχ_summable χ X s).convolution (LSeriesSummable_of_one_lt_re χ hs)

omit [NeZero q] in
theorem aXχ_zero (χ : DirichletCharacter ℂ q) (X : ℕ) : aXχ χ X 0 = 0 := by simp [aXχ, aX_zero]

omit [NeZero q] in
theorem aXχ_one (χ : DirichletCharacter ℂ q) {X : ℕ} (hX : 1 ≤ X) : aXχ χ X 1 = 1 := by
  simp [aXχ, aX_one hX]

omit [NeZero q] in
theorem aXχ_eq_zero (χ : DirichletCharacter ℂ q) {X n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ X) : aXχ χ X n = 0 := by
  simp [aXχ, aX_eq_zero h2 hn]

omit [NeZero q] in
theorem norm_aXχ_le (χ : DirichletCharacter ℂ q) (X n : ℕ) : ‖aXχ χ X n‖ ≤ (n.divisors.card : ℝ) := by
  rw [aXχ, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one χ _)).trans (norm_aX_le X n)

omit [NeZero q] in
theorem differentiable_mollχ (χ : DirichletCharacter ℂ q) (X : ℕ) : Differentiable ℂ (mollχ χ X) := by
  have e : mollχ χ X = fun s => ∑ m ∈ Finset.Ioc 0 X,
      ((ArithmeticFunction.moebius m : ℤ) : ℂ) * χ m * (m : ℂ) ^ (-s) := rfl
  rw [e]
  refine Differentiable.fun_sum fun m hm => ?_
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (Finset.mem_Ioc.1 hm).1; omega)
  exact (differentiable_id.neg.const_cpow (Or.inl hm0)).const_mul _

omit [NeZero q] in
/-- `|M_X(s, χ)| ≤ X` for `Re s ≥ 0`. -/
theorem norm_mollχ_le_X (χ : DirichletCharacter ℂ q) (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖mollχ χ X s‖ ≤ X := by
  unfold mollχ
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ Finset.Ioc 0 X,
      ‖((ArithmeticFunction.moebius m : ℤ) : ℂ) * χ m * (m : ℂ) ^ (-s)‖ ≤ 1 := by
    intro m hm
    have hm0 : 0 < m := (Finset.mem_Ioc.1 hm).1
    rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hm0]
    have hμ : (|((ArithmeticFunction.moebius m : ℤ) : ℝ)|) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hχ := norm_le_one χ (m : ZMod q)
    have h1 : (m : ℝ) ^ (-s).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm0) (by simp; linarith)
    calc |((ArithmeticFunction.moebius m : ℤ) : ℝ)| * ‖χ m‖ * (m : ℝ) ^ (-s).re ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by norm_num
  refine (Finset.sum_le_sum hterm).trans ?_
  simp

/-! ### The integrand -/

/-- **The integrand** `M_X(ρ + w, χ)·(L(ρ + w, χ)/w)·Γ(w + 1)·Y^w`: at a zero `ρ` of `L(·, χ)`, `χ ≠ 1`, the quotient
`L(ρ + w, χ)/w` (Mathlib's `dslope` at `0`) is entire, and `Γ(w + 1)` is holomorphic on `Re w > −1`. -/
def Gχ (χ : DirichletCharacter ℂ q) (X : ℕ) (Y : ℝ) (ρ w : ℂ) : ℂ :=
  mollχ χ X (ρ + w) * dslope (fun z => LFunction χ (ρ + z)) 0 w * Complex.Gamma (w + 1) * (Y : ℂ) ^ w

theorem differentiable_dslopeχ {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (ρ : ℂ) :
    Differentiable ℂ (dslope (fun z => LFunction χ (ρ + z)) 0) := by
  have hd : Differentiable ℂ (fun z => LFunction χ (ρ + z)) := (differentiable_LFunction hχ).comp (by fun_prop)
  have h := (Complex.differentiableOn_dslope (s := univ) (c := 0) Filter.univ_mem).2 hd.differentiableOn
  exact fun w => h.differentiableAt Filter.univ_mem

theorem differentiableAt_Gχ {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (X : ℕ) {Y : ℝ} (hY : 0 < Y) (ρ : ℂ)
    {w : ℂ} (hw : -1 < w.re) : DifferentiableAt ℂ (Gχ χ X Y ρ) w := by
  have h1 : DifferentiableAt ℂ (fun w => mollχ χ X (ρ + w)) w :=
    (differentiable_mollχ χ X).differentiableAt.comp w (by fun_prop)
  have h3 : DifferentiableAt ℂ (fun w => Complex.Gamma (w + 1)) w := by
    refine DifferentiableAt.comp (g := Complex.Gamma) w (Complex.differentiableAt_Gamma _ fun m h => ?_)
      (by fun_prop)
    have := congrArg Complex.re h
    simp only [add_re, one_re, neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h4 : DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 hY.ne'))
  exact ((h1.mul (differentiable_dslopeχ hχ ρ w)).mul h3).mul h4

/-- `L(ρ + w, χ)/w` for `w ≠ 0`, at a zero `ρ` of `L(·, χ)`. -/
theorem dslope_eqχ {χ : DirichletCharacter ℂ q} {ρ : ℂ} (hρ : LFunction χ ρ = 0) {w : ℂ} (hw : w ≠ 0) :
    dslope (fun z => LFunction χ (ρ + z)) 0 w = LFunction χ (ρ + w) / w := by
  rw [dslope_of_ne _ hw, slope_def_field]
  simp [hρ]

/-- **On `Re(ρ + w) > 1`** the integrand is `L(χa, ρ + w)·Γ(w)·Y^w`. -/
theorem Gχ_eq_LSeries {χ : DirichletCharacter ℂ q} (X : ℕ) (Y : ℝ) {ρ : ℂ} (hρ : LFunction χ ρ = 0) {w : ℂ}
    (hw : w ≠ 0) (hre : 1 < (ρ + w).re) :
    Gχ χ X Y ρ w = LSeries (aXχ χ X) (ρ + w) * Complex.Gamma w * (Y : ℂ) ^ w := by
  rw [Gχ, dslope_eqχ hρ hw, LSeries_aXχ χ X hre, Complex.Gamma_add_one w hw]
  field_simp

/-- **On the line `Re w = ½ − Re ρ`**: `G(w) = M_X(ρ + w, χ) L(ρ + w, χ) Γ(w + 1)/w · Y^w`. -/
theorem Gχ_eq_left {χ : DirichletCharacter ℂ q} (X : ℕ) (Y : ℝ) {ρ : ℂ} (hρ : LFunction χ ρ = 0) {w : ℂ}
    (hw : w ≠ 0) :
    Gχ χ X Y ρ w = mollχ χ X (ρ + w) * LFunction χ (ρ + w) * (Complex.Gamma (w + 1) / w) * (Y : ℂ) ^ w := by
  rw [Gχ, dslope_eqχ hρ hw]
  ring

/-! ### Bounds on the strip -/

/-- **`|G(w)|(1 + |Im w|)³` is bounded on the strip `½ − Re ρ ≤ Re w ≤ 2`.** -/
theorem Gχ_strip_bound {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (X : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {ρ : ℂ}
    (hρ : LFunction χ ρ = 0) (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) :
    ∃ C : ℝ, ∀ w : ℂ, 1 / 2 - ρ.re ≤ w.re → w.re ≤ 2 → ‖Gχ χ X Y ρ w‖ * (1 + |w.im|) ^ 3 ≤ C := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_dslopeχ hχ ρ).continuous.continuousOn
  set D := max C₁ (3 * (q + 1) * (|ρ.im| + 2)) with hD
  have hD0 : 0 ≤ D := le_max_of_le_right (by positivity)
  refine ⟨X * D * KG * Y ^ (2 : ℝ), fun w hw1 hw2 => ?_⟩
  have h1 : 1 ≤ (1 + |w.im|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg w.im])
  have hDw : ‖dslope (fun z => LFunction χ (ρ + z)) 0 w‖ ≤ D * (1 + |w.im|) ^ 2 := by
    rcases le_or_gt ‖w‖ 1 with hw | hw
    · calc ‖dslope (fun z => LFunction χ (ρ + z)) 0 w‖ ≤ C₁ :=
            hC₁ w (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw)
        _ ≤ D := le_max_left _ _
        _ ≤ D * (1 + |w.im|) ^ 2 := le_mul_of_one_le_right hD0 h1
    · have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
      rw [dslope_eqχ hρ hw0, norm_div]
      have hz := LFunction_growth hχ (s := ρ + w) (by simp; linarith) (by simp; linarith)
      have him : |(ρ + w).im| ≤ |ρ.im| + |w.im| := by simp only [add_im]; exact abs_add_le _ _
      have hq0 : (0 : ℝ) ≤ 3 * (q + 1) := by positivity
      calc ‖LFunction χ (ρ + w)‖ / ‖w‖ ≤ ‖LFunction χ (ρ + w)‖ := div_le_self (norm_nonneg _) hw.le
        _ ≤ 3 * (q + 1) * (|(ρ + w).im| + 2) := hz
        _ ≤ 3 * (q + 1) * ((|ρ.im| + 2) * (1 + |w.im|)) := by
            gcongr
            nlinarith [abs_nonneg ρ.im, abs_nonneg w.im]
        _ = 3 * (q + 1) * (|ρ.im| + 2) * (1 + |w.im|) := by ring
        _ ≤ D * (1 + |w.im|) ^ 2 := by
            have h2 : 1 + |w.im| ≤ (1 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im]
            calc 3 * (q + 1) * (|ρ.im| + 2) * (1 + |w.im|) ≤ D * (1 + |w.im|) :=
                  mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
              _ ≤ D * (1 + |w.im|) ^ 2 := mul_le_mul_of_nonneg_left h2 hD0
  have hm := norm_mollχ_le_X χ X (s := ρ + w) (by simp; linarith)
  have hG := norm_Gamma_le' (z := w + 1) (by simp; linarith) (by simp; linarith)
  have hGim : (w + 1).im = w.im := by simp
  rw [hGim] at hG
  have hYw : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hY hw2
  unfold Gχ
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖mollχ χ X (ρ + w)‖ * ‖dslope (fun z => LFunction χ (ρ + z)) 0 w‖ * ‖Complex.Gamma (w + 1)‖
        * ‖(Y : ℂ) ^ w‖ * (1 + |w.im|) ^ 3
      ≤ X * (D * (1 + |w.im|) ^ 2) * ‖Complex.Gamma (w + 1)‖ * Y ^ (2 : ℝ) * (1 + |w.im|) ^ 3 := by
        gcongr
    _ = X * D * Y ^ (2 : ℝ) * (‖Complex.Gamma (w + 1)‖ * (1 + |w.im|) ^ 5) := by ring
    _ ≤ X * D * Y ^ (2 : ℝ) * KG := by gcongr
    _ = X * D * KG * Y ^ (2 : ℝ) := by ring

theorem continuous_Gχ_line {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (X : ℕ) {Y : ℝ} (hY : 0 < Y) (ρ : ℂ)
    {σ : ℝ} (hσ : -1 < σ) : Continuous fun t : ℝ => Gχ χ X Y ρ (σ + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ContinuousAt.comp (g := Gχ χ X Y ρ) (f := fun t : ℝ => (σ : ℂ) + t * I)
    (differentiableAt_Gχ hχ X hY ρ (by simpa using hσ)).continuousAt (by fun_prop)

theorem Gχ_line_integrable {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (X : ℕ) {Y : ℝ} (hY : 0 < Y) {ρ : ℂ}
    {C : ℝ} (hC : ∀ w : ℂ, 1 / 2 - ρ.re ≤ w.re → w.re ≤ 2 → ‖Gχ χ X Y ρ w‖ * (1 + |w.im|) ^ 3 ≤ C)
    (hρ2 : ρ.re < 1) {σ : ℝ} (hσ1 : 1 / 2 - ρ.re ≤ σ) (hσ2 : σ ≤ 2) :
    Integrable fun t : ℝ => Gχ χ X Y ρ (σ + t * I) := by
  refine integrable_of_le_sq (continuous_Gχ_line hχ X hY ρ (by linarith)) (K := C) fun t => ?_
  have h := hC (σ + t * I) (by simpa using hσ1) (by simpa using hσ2)
  have him : ((σ : ℂ) + t * I).im = t := by simp
  rw [him] at h
  have h23 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 3 := pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
  calc ‖Gχ χ X Y ρ (σ + t * I)‖ * (1 + |t|) ^ 2 ≤ ‖Gχ χ X Y ρ (σ + t * I)‖ * (1 + |t|) ^ 3 := by gcongr
    _ ≤ C := h

theorem Gχ_decay {χ : DirichletCharacter ℂ q} (X : ℕ) {Y : ℝ} {ρ : ℂ} {C : ℝ}
    (hC : ∀ w : ℂ, 1 / 2 - ρ.re ≤ w.re → w.re ≤ 2 → ‖Gχ χ X Y ρ w‖ * (1 + |w.im|) ^ 3 ≤ C) :
    ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc (1 / 2 - ρ.re) 2, ∀ y : ℝ, T₀ ≤ |y| → ‖Gχ χ X Y ρ (x + y * I)‖ ≤ η := by
  intro η hη
  refine ⟨C / η, fun x hx y hy => ?_⟩
  have hb := hC (x + y * I) (by simpa using hx.1) (by simpa using hx.2)
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [him] at hb
  have hpos : 0 < 1 + |y| := by positivity
  have h3 : 1 + |y| ≤ (1 + |y|) ^ 3 := le_self_pow₀ (by linarith [abs_nonneg y]) (by norm_num)
  have hCη : C ≤ η * |y| := by rwa [div_le_iff₀ hη, mul_comm] at hy
  have hG0 := norm_nonneg (Gχ χ X Y ρ (x + y * I))
  have : ‖Gχ χ X Y ρ (x + y * I)‖ * (1 + |y|) ≤ η * (1 + |y|) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hG0]
  exact le_of_mul_le_mul_right this hpos

/-! ### The identity at a zero -/

/-- The `n`-th term of the identity: `χ(n)a_n n^{−ρ}e^{−n/Y}`. -/
def cnχ (χ : DirichletCharacter ℂ q) (X : ℕ) (Y : ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  aXχ χ X n * (n : ℂ) ^ (-ρ) * (Real.exp (-((n : ℝ) / Y)) : ℂ)

omit [NeZero q] in
theorem term_shift (χ : DirichletCharacter ℂ q) (X : ℕ) (ρ w : ℂ) :
    LSeries.term (fun n => aXχ χ X n * (n : ℂ) ^ (-ρ)) w = LSeries.term (aXχ χ X) (ρ + w) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hn', Complex.cpow_neg]
    field_simp

/-- **The identity at a zero.** For `χ ≠ 1` and a zero `ρ` of `L(·, χ)` with `½ < Re ρ < 1`, `X ≥ 0` and `Y ≥ 1`:
`Σ_n χ(n)a_n n^{−ρ}e^{−n/Y} = (1/2π) ∫ G(½ − Re ρ + iv) dv`. Perron's formula for `e^{−n/Y}` (`Linnik.perron_exp`)
gives the integral on `Re w = 2`; the zero of `L(·, χ)` at `ρ` cancels the pole of `Γ(w)` at `w = 0`, so the line
moves to `Re(ρ + w) = ½` with no residue. -/
theorem detect_identityχ {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (X : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {ρ : ℂ}
    (hρ : LFunction χ ρ = 0) (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) :
    ∑' n : ℕ, cnχ χ X Y ρ n = (1 / (2 * π) : ℂ) * ∫ v : ℝ, Gχ χ X Y ρ (((1 / 2 - ρ.re : ℝ) : ℂ) + v * I) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨C, hC⟩ := Gχ_strip_bound hχ X hY hρ hρ1 hρ2
  set a : ℕ → ℂ := fun n => aXχ χ X n * (n : ℂ) ^ (-ρ) with ha
  have ha0 : a 0 = 0 := by simp [ha, aXχ_zero]
  have hsum2 : LSeriesSummable a ((2 : ℝ) : ℂ) := by
    have h := LSeriesSummable_aXχ χ X (s := ρ + ((2 : ℝ) : ℂ)) (by simp; linarith)
    show LSeriesSummable (fun n => aXχ χ X n * (n : ℂ) ^ (-ρ)) ((2 : ℝ) : ℂ)
    unfold LSeriesSummable at h ⊢
    rw [term_shift χ X ρ ((2 : ℝ) : ℂ)]
    exact h
  have hp := perron_exp ha0 (c := 2) (by norm_num) (by norm_num) hY0 hsum2
  have hleft : ∑' n : ℕ, cnχ χ X Y ρ n = ∑' n : ℕ, a n * (Real.exp (-((n : ℝ) / Y)) : ℂ) := rfl
  rw [hleft, hp]
  have hright : ∀ t : ℝ, LSeries a ((2 : ℝ) + t * I) * Complex.Gamma ((2 : ℝ) + t * I) * (Y : ℂ) ^ ((2 : ℝ) + t * I)
      = Gχ χ X Y ρ (((2 : ℝ) : ℂ) + t * I) := by
    intro t
    have hw0 : ((2 : ℝ) : ℂ) + t * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have hL : LSeries a ((2 : ℝ) + t * I) = LSeries (aXχ χ X) (ρ + ((2 : ℝ) + t * I)) := by
      show LSeries (fun n => aXχ χ X n * (n : ℂ) ^ (-ρ)) _ = _
      unfold LSeries; rw [term_shift χ X ρ]
    rw [hL, Gχ_eq_LSeries X Y hρ hw0 (by simp; linarith)]
  simp_rw [hright]
  have hhol : HolomorphicOn (Gχ χ X Y ρ) (Icc (1 / 2 - ρ.re) 2 ×ℂ univ) := by
    intro w hw
    rw [mem_reProdIm] at hw
    exact (differentiableAt_Gχ hχ X hY0 ρ (by linarith [hw.1.1])).differentiableWithinAt
  have hshift := SmoothPerron.verticalIntegral_shift (G := Gχ χ X Y ρ) (σ' := 1 / 2 - ρ.re) (σ := 2)
    (by linarith) hhol (Gχ_line_integrable hχ X hY0 hC hρ2 (by linarith) le_rfl)
    (Gχ_line_integrable hχ X hY0 hC hρ2 le_rfl (by linarith)) (Gχ_decay X hC)
  simp only [VerticalIntegral] at hshift
  congr 1
  exact smul_right_injective ℂ I_ne_zero hshift

/-! ### The pieces and the dichotomy -/

/-- The detecting polynomial `P_χ(β + iγ) = Σ_{X<j≤XN} b_jχ(j)j^{−β−iγ}`, `b_j = a_j e^{−j/Y}`
(`InghamDensity.b1`). -/
def Pvχ (χ : DirichletCharacter ℂ q) (X N : ℕ) (Y β γ : ℝ) : ℂ :=
  DirMean.dp (Finset.Ioc X (X * N)) (fun j => b1 X Y j * χ j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) γ

/-- The right side of the identity. -/
def Ivχ (χ : DirichletCharacter ℂ q) (X : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ v : ℝ, Gχ χ X Y ρ (((1 / 2 - ρ.re : ℝ) : ℂ) + v * I)

omit [NeZero q] in
theorem cnχ_zero (χ : DirichletCharacter ℂ q) (X : ℕ) (Y : ℝ) (ρ : ℂ) : cnχ χ X Y ρ 0 = 0 := by
  simp [cnχ, aXχ_zero]

omit [NeZero q] in
theorem cnχ_one (χ : DirichletCharacter ℂ q) {X : ℕ} (hX : 1 ≤ X) (Y : ℝ) (ρ : ℂ) :
    cnχ χ X Y ρ 1 = (Real.exp (-(1 / Y)) : ℂ) := by
  simp [cnχ, aXχ_one χ hX]

omit [NeZero q] in
theorem cnχ_eq_zero (χ : DirichletCharacter ℂ q) {X n : ℕ} (h2 : 2 ≤ n) (hn : n ≤ X) (Y : ℝ) (ρ : ℂ) :
    cnχ χ X Y ρ n = 0 := by
  simp [cnχ, aXχ_eq_zero χ h2 hn]

omit [NeZero q] in
/-- `|c_n| ≤ n e^{−n/Y}` for `Re ρ ≥ 0`. -/
theorem norm_cnχ_le (χ : DirichletCharacter ℂ q) (X : ℕ) (Y : ℝ) {ρ : ℂ} (hρ : 0 ≤ ρ.re) (n : ℕ) :
    ‖cnχ χ X Y ρ n‖ ≤ n * Real.exp (-((n : ℝ) / Y)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cnχ_zero]
  unfold cnχ
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_natCast_cpow_of_pos hn]
  have h1 : (n : ℝ) ^ (-ρ).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp; linarith)
  have h2 : ‖aXχ χ X n‖ ≤ n := (norm_aXχ_le χ X n).trans (by exact_mod_cast Nat.card_divisors_le_self n)
  calc ‖aXχ χ X n‖ * (n : ℝ) ^ (-ρ).re * Real.exp (-((n : ℝ) / Y))
      ≤ n * 1 * Real.exp (-((n : ℝ) / Y)) := by gcongr
    _ = n * Real.exp (-((n : ℝ) / Y)) := by ring

omit [NeZero q] in
theorem summable_cnχ (χ : DirichletCharacter ℂ q) (X : ℕ) {Y : ℝ} (hY : 0 < Y) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    Summable (cnχ χ X Y ρ) := by
  have hr : 0 < 1 / Y := by positivity
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  refine Summable.of_norm_bounded h1 fun n => ?_
  refine (norm_cnχ_le χ X Y hρ n).trans (le_of_eq ?_)
  have e : -(1 / Y) * (n : ℝ) = -((n : ℝ) / Y) := by ring
  rw [pow_one, e]

omit [NeZero q] in
/-- `Σ_{X<n≤XN} c_n = P_χ(β + iγ)`. -/
theorem sum_cnχ_eq (χ : DirichletCharacter ℂ q) (X N : ℕ) (Y β γ : ℝ) :
    ∑ n ∈ Finset.Ioc X (X * N), cnχ χ X Y ((β : ℂ) + γ * I) n = Pvχ χ X N Y β γ := by
  unfold Pvχ DirMean.dp
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < n := by have := (Finset.mem_Ioc.1 hn).1; omega
  rw [cnχ, ShortWeil.natCast_cpow_neg n hn0 β γ]
  simp only [b1, aXχ]
  push_cast
  ring

omit [NeZero q] in
/-- **The split**: `Σ' c_n = c₁ + Σ_{X<n≤M} c_n + Σ'_{n>M} c_n` for `1 ≤ X ≤ M`. -/
theorem tsum_cnχ_split (χ : DirichletCharacter ℂ q) {X M : ℕ} (hX : 1 ≤ X) (hXM : X ≤ M) {Y : ℝ} (hY : 0 < Y)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ∑' n, cnχ χ X Y ρ n = cnχ χ X Y ρ 1 + ∑ n ∈ Finset.Ioc X M, cnχ χ X Y ρ n
      + ∑' n : ℕ, if M < n then cnχ χ X Y ρ n else 0 := by
  have hs := summable_cnχ χ X hY hρ
  set f := cnχ χ X Y ρ with hf
  have hpt : ∀ n, f n = ((if n = 1 then f 1 else 0) + (if n ∈ Finset.Ioc X M then f n else 0))
      + (if M < n then f n else 0) := by
    intro n
    rcases Nat.lt_or_ge M n with h | h
    · have h1 : n ≠ 1 := by omega
      have h2 : n ∉ Finset.Ioc X M := fun hm => by have := (Finset.mem_Ioc.1 hm).2; omega
      simp [h1, h2, h]
    · have h3 : ¬ M < n := by omega
      rcases Nat.lt_or_ge X n with hXn | hXn
      · have h1 : n ≠ 1 := by omega
        have h2 : n ∈ Finset.Ioc X M := Finset.mem_Ioc.2 ⟨hXn, h⟩
        simp [h1, h2, h3]
      · have h2 : n ∉ Finset.Ioc X M := fun hm => by have := (Finset.mem_Ioc.1 hm).1; omega
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · interval_cases n
          · simp [hf, cnχ_zero]
          · simp [h2, h3]
        · have h1 : n ≠ 1 := by omega
          simp [h1, h2, h3, hf, cnχ_eq_zero χ hn2 hXn]
  have hs1 : Summable fun n : ℕ => if n = 1 then f 1 else 0 :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by simp at hn; simp [hn]
  have hs2 : Summable fun n : ℕ => if n ∈ Finset.Ioc X M then f n else 0 :=
    summable_of_ne_finset_zero (s := Finset.Ioc X M) fun n hn => by simp [hn]
  have hs3 : Summable fun n : ℕ => if M < n then f n else 0 := by
    refine Summable.of_norm_bounded hs.norm fun n => ?_
    split_ifs <;> simp
  calc ∑' n, f n = ∑' n, (((if n = 1 then f 1 else 0) + (if n ∈ Finset.Ioc X M then f n else 0))
        + (if M < n then f n else 0)) := tsum_congr hpt
    _ = (∑' n : ℕ, if n = 1 then f 1 else 0) + (∑' n : ℕ, if n ∈ Finset.Ioc X M then f n else 0)
        + ∑' n : ℕ, if M < n then f n else 0 := by
        rw [Summable.tsum_add (hs1.add hs2) hs3, Summable.tsum_add hs1 hs2]
    _ = f 1 + ∑ n ∈ Finset.Ioc X M, f n + ∑' n : ℕ, if M < n then f n else 0 := by
        congr 2
        · exact tsum_ite_eq 1 (fun _ : ℕ => f 1)
        · rw [tsum_eq_sum (s := Finset.Ioc X M) fun n hn => by simp [hn]]
          exact Finset.sum_congr rfl fun n hn => by simp [hn]

omit [NeZero q] in
/-- **The tail beyond `M ≥ 22 Y log Y`** is at most `1/16`, for `Y ≥ 8`: `n e^{−n/Y} ≤ 48Y³e^{−M/(2Y)}/n²` for
`n > M`, and `e^{−M/(2Y)} ≤ Y^{−11}`. -/
theorem tailχ_le (χ : DirichletCharacter ℂ q) (X : ℕ) {Y : ℝ} (hY : 8 ≤ Y) {ρ : ℂ} (hρ : 0 ≤ ρ.re) {M : ℕ}
    (hM : 22 * Y * Real.log Y ≤ M) :
    ‖∑' n : ℕ, if M < n then cnχ χ X Y ρ n else 0‖ ≤ 1 / 16 := by
  have hY0 : 0 < Y := by linarith
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hexp : Real.exp ((M : ℝ) / (2 * Y)) ≥ Y ^ 11 := by
    have h1 : 11 * Real.log Y ≤ (M : ℝ) / (2 * Y) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    calc Y ^ 11 = Real.exp (((11 : ℕ) : ℝ) * Real.log Y) := by
          rw [Real.exp_nat_mul, Real.exp_log hY0]
      _ ≤ Real.exp ((M : ℝ) / (2 * Y)) := Real.exp_le_exp.2 (by push_cast; linarith)
  set K : ℝ := 48 * Y ^ 3 * Real.exp (-((M : ℝ) / (2 * Y))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ n : ℕ, ‖if M < n then cnχ χ X Y ρ n else 0‖ ≤ K * (1 / (n : ℝ) ^ 2) := by
    intro n
    split_ifs with hn
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn0 : (0 : ℝ) < n := by linarith
      have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn.le
      refine (norm_cnχ_le χ X Y hρ n).trans ?_
      have hy : 0 ≤ (n : ℝ) / (2 * Y) := by positivity
      have h3 := pow_mul_exp_neg_le 3 hy
      have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [hf] at h3
      have hsplit : Real.exp (-((n : ℝ) / Y))
          = Real.exp (-((n : ℝ) / (2 * Y))) * Real.exp (-((n : ℝ) / (2 * Y))) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring
      have hmono : Real.exp (-((n : ℝ) / (2 * Y))) ≤ Real.exp (-((M : ℝ) / (2 * Y))) :=
        Real.exp_le_exp.2 (by
          have : (M : ℝ) / (2 * Y) ≤ (n : ℝ) / (2 * Y) := by gcongr
          linarith)
      have e3 : (n : ℝ) * (n : ℝ) ^ 2 = 8 * Y ^ 3 * ((n : ℝ) / (2 * Y)) ^ 3 := by
        field_simp; ring
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      rw [mul_one_div, le_div_iff₀ hn2]
      calc (n : ℝ) * Real.exp (-((n : ℝ) / Y)) * (n : ℝ) ^ 2
          = 8 * Y ^ 3 * (((n : ℝ) / (2 * Y)) ^ 3 * Real.exp (-((n : ℝ) / (2 * Y))))
            * Real.exp (-((n : ℝ) / (2 * Y))) := by rw [hsplit]; nlinarith [e3]
        _ ≤ 8 * Y ^ 3 * 6 * Real.exp (-((M : ℝ) / (2 * Y))) := by gcongr
        _ = K := by rw [hK]; ring
    · rw [norm_zero]; positivity
  have hsum : HasSum (fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) (K * (π ^ 2 / 6)) :=
    hasSum_zeta_two.mul_left K
  refine (tsum_of_norm_bounded hsum hpt).trans ?_
  have hpi : π ^ 2 / 6 ≤ 2 := by have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
  have hY11 : 0 < Y ^ 11 := by positivity
  have hKle : K ≤ 48 * Y ^ 3 / Y ^ 11 := by
    rw [hK, Real.exp_neg, ← div_eq_mul_inv]
    gcongr
  have hfin : 2 * (48 * Y ^ 3 / Y ^ 11) ≤ 1 / 16 := by
    rw [mul_div_assoc', div_le_div_iff₀ hY11 (by norm_num)]
    have hY8 : (8 : ℝ) ^ 8 ≤ Y ^ 8 := by gcongr
    have e : Y ^ 11 = Y ^ 8 * Y ^ 3 := by ring
    rw [e]
    have hY3 : 0 ≤ Y ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hY8 hY3]
  calc K * (π ^ 2 / 6) ≤ K * 2 := by gcongr
    _ = 2 * K := by ring
    _ ≤ 2 * (48 * Y ^ 3 / Y ^ 11) := by gcongr
    _ ≤ 1 / 16 := hfin

/-- **The dichotomy at a zero.** Let `χ ≠ 1`, `ρ = β + iγ` a zero of `L(·, χ)` with `½ < β < 1`, `8 ≤ Y`, `1 ≤ X`
and `22 Y log Y ≤ XN`. Then `|P_χ(ρ)| ≥ ¼` or `|I_χ(ρ)| ≥ ¼`: the identity is `e^{−1/Y} + P_χ(ρ) + T = I_χ(ρ)` with
`e^{−1/Y} ≥ 7/8` and `|T| ≤ 1/16`. -/
theorem dichotomy {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) {Y : ℝ}
    (hY : 8 ≤ Y) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ)) {β γ : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1)
    (hz : LFunction χ ((β : ℂ) + γ * I) = 0) :
    1 / 4 ≤ ‖Pvχ χ X N Y β γ‖ ∨ 1 / 4 ≤ ‖Ivχ χ X Y ((β : ℂ) + γ * I)‖ := by
  set ρ : ℂ := (β : ℂ) + γ * I with hρdef
  have hY0 : 0 < Y := by linarith
  have hρre : ρ.re = β := by simp [hρdef]
  have hXM : X ≤ X * N := Nat.le_mul_of_pos_right X hN
  have hid := detect_identityχ hχ X (Y := Y) (by linarith) hz (by rw [hρre]; exact hβ1)
    (by rw [hρre]; exact hβ2)
  have hsplit := tsum_cnχ_split χ hX hXM hY0 (ρ := ρ) (by rw [hρre]; linarith)
  have hsum := sum_cnχ_eq χ X N Y β γ
  rw [← hρdef] at hsum
  set T := ∑' n : ℕ, if X * N < n then cnχ χ X Y ρ n else 0 with hT
  set P := Pvχ χ X N Y β γ
  set II := Ivχ χ X Y ρ with hII
  have heq : cnχ χ X Y ρ 1 + P + T = II := by
    rw [← hsum, ← hsplit]; exact hid
  have hT16 : ‖T‖ ≤ 1 / 16 := tailχ_le χ X hY (by rw [hρre]; linarith) hM
  have hc1 : (7 / 8 : ℝ) ≤ ‖cnχ χ X Y ρ 1‖ := by
    rw [cnχ_one χ hX, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := Real.add_one_le_exp (-(1 / Y))
    have : 1 / Y ≤ 1 / 8 := by gcongr
    linarith
  have hle : ‖cnχ χ X Y ρ 1‖ ≤ ‖P‖ + ‖T‖ + ‖II‖ := by
    have e : cnχ χ X Y ρ 1 = II - P - T := by rw [← heq]; ring
    rw [e]
    calc ‖II - P - T‖ ≤ ‖II‖ + ‖P‖ + ‖T‖ := by
          refine (norm_sub_le _ _).trans ?_
          have h1 := norm_sub_le II P
          linarith
      _ = ‖P‖ + ‖T‖ + ‖II‖ := by ring
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  linarith

end LinnikDetect

#print axioms LinnikDetect.LSeries_aXχ
#print axioms LinnikDetect.detect_identityχ
#print axioms LinnikDetect.dichotomy
