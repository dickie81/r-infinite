import KubotaDirSplit

/-! # θ's coefficients at `xp²` and `xp` (round 454)

S5f-13 of round 360's plan, part 5. Round 453 proved the relations among round 428's Dirichlet series at a
primary prime `p ∤ x`; its next step planned their consequences for θ's coefficients `ρ` (round 431's `rhoM`),
through round 450's residue principle and round 449's cube relation. This round proves them, with `N = N(p)`,
`X = N(p)^{−s}`, `t = (3/p)₃` and round 452's Gauss sums `γ_j(x)`:

* **The completed series at `xp^e`** (`dirL_mul_pow`, **`dirL_p5`** and **`dirL_p3`**): with the factors
  `(|p|^e)^{s−1}` from `|δ₃xp^e| = |δ₃x|·|p|^e`, for `Re s > 2`, `Λ_{xp⁵} = (|p|³)^{s−1}(1 + N³X³)·Λ_{xp²}`
  and `Λ_{xp³} = (|p|³)^{s−1}(1 + N³X³)·Λ_x − t·γ_1(x)·X·(|p|²)^{s−1}·Λ_{xp}`.
* **The coefficients at `4/3`** (`coef_four_thirds_cube` and `coef_four_thirds_sq`):
  `(|p|³)^{1/3}(1 + N³N^{−4})` is `|p| + |p|⁻¹`, and `N^{−4/3}(|p|²)^{1/3}` is `|p|⁻²`.
* **θ's coefficients** (**`rhoM_mul_sq`**, **`rhoM_mul_prime`** and **`rhoM_mul_prime_eq`**): `ρ(xp²) = 0`,
  `t·γ_1(x)·ρ(xp) = |p|·ρ(x)`, and `ρ(xp) = t²·γ_2(x)·ρ(x)/|p|`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-! ### The completed series at `xp^e` -/

/-- **`Λ_{xp^e}(s) = Q_x(s)·(|p|^e)^{s−1}·D_{δ₃xp^e}(s)`**, with `Q_x(s) = (2π/Γ(s))(2π|δ₃x|/9)^{s−1}`. -/
theorem dirL_mul_pow (x p : 𝓞 K) (e : ℕ) (s : ℂ) :
    dirL (x * p ^ e) s = 2 * Real.pi / Complex.Gamma s *
      ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) * ((‖σO p‖ ^ e : ℝ) : ℂ) ^ (s - 1) *
        dirD (δ3 * (x * p ^ e)) s := by
  have h : (2 * Real.pi * ‖σO (δ3 * (x * p ^ e)) / 9‖ : ℝ) =
      (2 * Real.pi * ‖σO (δ3 * x) / 9‖) * ‖σO p‖ ^ e := by
    rw [show δ3 * (x * p ^ e) = δ3 * x * p ^ e by ring, map_mul, map_pow, mul_div_right_comm, norm_mul,
      norm_pow]
    ring
  rw [dirL_eq, h, Complex.ofReal_mul (2 * Real.pi * ‖σO (δ3 * x) / 9‖) (‖σO p‖ ^ e),
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  ring

/-- **`Λ_{xp⁵} = (|p|³)^{s−1}(1 + N(p)^{3−3s})·Λ_{xp²}`** for a primary prime `p ∤ x` and `Re s > 2`. -/
theorem dirL_p5 {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) {s : ℂ}
    (hs : 2 < s.re) :
    dirL (x * p ^ 5) s = ((‖σO p‖ ^ 3 : ℝ) : ℂ) ^ (s - 1) *
      (1 + (absNorm (span {p}) : ℂ) ^ 3 * ((absNorm (span {p}) : ℂ) ^ (-s)) ^ 3) *
        dirL (x * p ^ 2) s := by
  rw [dirL_mul_pow, dirL_mul_pow, dirD_p5 hp hpp hpx hs,
    show ‖σO p‖ ^ 5 = ‖σO p‖ ^ 3 * ‖σO p‖ ^ 2 by ring, Complex.ofReal_mul (‖σO p‖ ^ 3) (‖σO p‖ ^ 2),
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  ring

/-- **`Λ_{xp³} = (|p|³)^{s−1}(1 + N(p)^{3−3s})·Λ_x − (3/p)₃·γ_1(x)·N(p)^{−s}·(|p|²)^{s−1}·Λ_{xp}`** for a
primary prime `p ∤ x` and `Re s > 2`. -/
theorem dirL_p3 {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) {s : ℂ}
    (hs : 2 < s.re) :
    dirL (x * p ^ 3) s = ((‖σO p‖ ^ 3 : ℝ) : ℂ) ^ (s - 1) *
      (1 + (absNorm (span {p}) : ℂ) ^ 3 * ((absNorm (span {p}) : ℂ) ^ (-s)) ^ 3) * dirL x s -
        σO (cub 3 (span {p})) * gaussP x p 1 * (absNorm (span {p}) : ℂ) ^ (-s) *
          ((‖σO p‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) * dirL (x * p) s := by
  have L1 : dirL (x * p) s = 2 * Real.pi / Complex.Gamma s *
      ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) * ((‖σO p‖ : ℝ) : ℂ) ^ (s - 1) *
        dirD (δ3 * (x * p)) s := by
    have := dirL_mul_pow x p 1 s
    simp only [pow_one] at this
    exact this
  rw [dirL_mul_pow, dirL_eq x s, L1, dirD_p3 hp hpp hpx hs,
    show ‖σO p‖ ^ 3 = ‖σO p‖ ^ 2 * ‖σO p‖ by ring, Complex.ofReal_mul (‖σO p‖ ^ 2) ‖σO p‖,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  ring

/-! ### θ's coefficients at `xp²` and `xp` -/

/-- **The coefficient of `Λ_x` and `Λ_{xp²}` at `4/3`**:
`(|p|³)^{1/3}(1 + N(p)³·(N(p)^{−4/3})³) = |p| + |p|⁻¹`, as `N(p) = |p|²`. -/
theorem coef_four_thirds_cube {p : 𝓞 K} (hp0 : p ≠ 0) :
    ((‖σO p‖ ^ 3 : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 1) *
      (1 + (absNorm (span {p}) : ℂ) ^ 3 * ((absNorm (span {p}) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3) =
        ((‖σO p‖ : ℝ) : ℂ) + ((‖σO p‖ : ℝ) : ℂ)⁻¹ := by
  set q := ‖σO p‖ with hq
  have hq0 : 0 < q := norm_pos_iff.2 (σO_ne_zero hp0)
  have hNq : (absNorm (span {p}) : ℂ) = ((q ^ 2 : ℝ) : ℂ) := by
    rw [hq, ← Complex.normSq_eq_norm_sq, normSq_σO, Complex.ofReal_natCast]
  have h13 : (4 / 3 : ℂ) - 1 = ((1 / 3 : ℝ) : ℂ) := by push_cast; norm_num
  have h43 : -(4 / 3 : ℂ) = ((-4 / 3 : ℝ) : ℂ) := by push_cast; ring
  have hA : ((q ^ 3 : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 1) = (q : ℂ) := by
    rw [h13, ← Complex.ofReal_cpow (by positivity), show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast hq0.le (by norm_num)]
  have hB : ((absNorm (span {p}) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3 = (((q ^ 2) ^ 4 : ℝ) : ℂ)⁻¹ := by
    rw [hNq, h43, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_pow, ← Complex.ofReal_inv]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show (-4 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  rw [hA, hB, hNq]
  push_cast
  field_simp

/-- **The coefficient of `Λ_{xp}` at `4/3`**: `N(p)^{−4/3}·(|p|²)^{1/3} = |p|⁻²`. -/
theorem coef_four_thirds_sq {p : 𝓞 K} (hp0 : p ≠ 0) :
    (absNorm (span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) * ((‖σO p‖ ^ 2 : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 1) =
      ((‖σO p‖ : ℝ) : ℂ)⁻¹ ^ 2 := by
  set q := ‖σO p‖ with hq
  have hq0 : 0 < q := norm_pos_iff.2 (σO_ne_zero hp0)
  have hNq : (absNorm (span {p}) : ℂ) = ((q ^ 2 : ℝ) : ℂ) := by
    rw [hq, ← Complex.normSq_eq_norm_sq, normSq_σO, Complex.ofReal_natCast]
  have h13 : (4 / 3 : ℂ) - 1 = ((1 / 3 : ℝ) : ℂ) := by push_cast; norm_num
  have h43 : -(4 / 3 : ℂ) = ((-4 / 3 : ℝ) : ℂ) := by push_cast; ring
  rw [hNq, h43, h13, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity),
    ← Complex.ofReal_mul, ← Real.rpow_add (by positivity), show (-4 / 3 : ℝ) + 1 / 3 = -1 by norm_num,
    Real.rpow_neg_one, ← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow]

/-- **`ρ(xp²) = 0`** for a primary prime `p ∤ x`: round 450's `sum_rhoM_eq_zero` applied to `dirL_p5` gives
`ρ(xp⁵) = (|p| + |p|⁻¹)·ρ(xp²)` at `s = 4/3`, and round 449's `rhoM_cube` gives `ρ(xp⁵) = |p|·ρ(xp²)`. -/
theorem rhoM_mul_sq {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    {x : 𝓞 K} (hpx : ¬ p ∣ x) : rhoM (x * p ^ 2) r Y hY = 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hpx (dvd_zero p)
  have hp0 := hp.ne_zero
  have hq0 : 0 < ‖σO p‖ := norm_pos_iff.2 (σO_ne_zero hp0)
  have hq' : ((‖σO p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hN0 : (absNorm (span {p}) : ℂ) ≠ 0 := absNorm_span_ne_zero hp0
  set xs : Fin 2 → 𝓞 K := ![x * p ^ 5, x * p ^ 2] with hxs_def
  set a : Fin 2 → ℂ → ℂ := ![fun _ => 1, fun s => -(((‖σO p‖ ^ 3 : ℝ) : ℂ) ^ (s - 1) *
    (1 + (absNorm (span {p}) : ℂ) ^ 3 * ((absNorm (span {p}) : ℂ) ^ (-s)) ^ 3))] with ha_def
  have hxs : ∀ i, xs i ≠ 0 := by
    intro i
    fin_cases i
    · exact mul_ne_zero hx0 (pow_ne_zero 5 hp0)
    · exact mul_ne_zero hx0 (pow_ne_zero 2 hp0)
  have ha : ∀ i, Differentiable ℂ (a i) := by
    intro i
    fin_cases i
    · exact differentiable_const 1
    · have h1 : Differentiable ℂ fun s : ℂ => ((‖σO p‖ ^ 3 : ℝ) : ℂ) ^ (s - 1) :=
        (differentiable_id.sub_const 1).const_cpow (Or.inl (by exact_mod_cast (pow_pos hq0 3).ne'))
      have h2 : Differentiable ℂ fun s : ℂ => (absNorm (span {p}) : ℂ) ^ (-s) :=
        differentiable_id.neg.const_cpow (Or.inl hN0)
      exact (h1.mul ((differentiable_const _).add ((differentiable_const _).mul (h2.pow 3)))).neg
  have hrel : ∀ s : ℂ, 2 < s.re → ∑ i, a i s * dirL (xs i) s = 0 := by
    intro s hs
    simp only [Fin.sum_univ_two, ha_def, hxs_def, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [dirL_p5 hp hpp hpx hs]
    ring
  have key := sum_rhoM_eq_zero hr hY xs hxs a ha hrel
  simp only [Fin.sum_univ_two, ha_def, hxs_def, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  rw [coef_four_thirds_cube hp0] at key
  have hcube := rhoM_cube hr hY hp hpp (mul_ne_zero hx0 (pow_ne_zero 2 hp0))
  rw [show p ^ 3 * (x * p ^ 2) = x * p ^ 5 by ring] at hcube
  rw [hcube] at key
  have h : ((‖σO p‖ : ℝ) : ℂ)⁻¹ * rhoM (x * p ^ 2) r Y hY = 0 := by linear_combination -key
  exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hq')

/-- **`(3/p)₃·γ_1(x)·ρ(xp) = |p|·ρ(x)`** for a primary prime `p ∤ x`: round 450's `sum_rhoM_eq_zero` applied
to `dirL_p3` gives `ρ(xp³) = (|p| + |p|⁻¹)·ρ(x) − (3/p)₃·γ_1(x)·|p|⁻²·ρ(xp)` at `s = 4/3`, and round 449's
`rhoM_cube` gives `ρ(xp³) = |p|·ρ(x)`. -/
theorem rhoM_mul_prime {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p)
    (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) :
    σO (cub 3 (span {p})) * gaussP x p 1 * rhoM (x * p) r Y hY = (‖σO p‖ : ℂ) * rhoM x r Y hY := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hpx (dvd_zero p)
  have hp0 := hp.ne_zero
  have hq0 : 0 < ‖σO p‖ := norm_pos_iff.2 (σO_ne_zero hp0)
  have hq' : ((‖σO p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hN0 : (absNorm (span {p}) : ℂ) ≠ 0 := absNorm_span_ne_zero hp0
  set t := σO (cub 3 (span {p})) with ht_def
  set γ := gaussP x p 1 with hγ_def
  set xs : Fin 3 → 𝓞 K := ![x * p ^ 3, x, x * p] with hxs_def
  set a : Fin 3 → ℂ → ℂ := ![fun _ => 1, fun s => -(((‖σO p‖ ^ 3 : ℝ) : ℂ) ^ (s - 1) *
    (1 + (absNorm (span {p}) : ℂ) ^ 3 * ((absNorm (span {p}) : ℂ) ^ (-s)) ^ 3)),
    fun s => t * γ * (absNorm (span {p}) : ℂ) ^ (-s) * ((‖σO p‖ ^ 2 : ℝ) : ℂ) ^ (s - 1)] with ha_def
  have hxs : ∀ i, xs i ≠ 0 := by
    intro i
    fin_cases i
    · exact mul_ne_zero hx0 (pow_ne_zero 3 hp0)
    · exact hx0
    · exact mul_ne_zero hx0 hp0
  have hc : ∀ n : ℕ, Differentiable ℂ fun s : ℂ => ((‖σO p‖ ^ n : ℝ) : ℂ) ^ (s - 1) := fun n =>
    (differentiable_id.sub_const 1).const_cpow (Or.inl (by exact_mod_cast (pow_pos hq0 n).ne'))
  have h2 : Differentiable ℂ fun s : ℂ => (absNorm (span {p}) : ℂ) ^ (-s) :=
    differentiable_id.neg.const_cpow (Or.inl hN0)
  have ha : ∀ i, Differentiable ℂ (a i) := by
    intro i
    fin_cases i
    · exact differentiable_const 1
    · exact ((hc 3).mul ((differentiable_const _).add ((differentiable_const _).mul (h2.pow 3)))).neg
    · exact ((differentiable_const _).mul h2).mul (hc 2)
  have hrel : ∀ s : ℂ, 2 < s.re → ∑ i, a i s * dirL (xs i) s = 0 := by
    intro s hs
    simp only [Fin.sum_univ_three, ha_def, hxs_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [dirL_p3 hp hpp hpx hs]
    ring
  have key := sum_rhoM_eq_zero hr hY xs hxs a ha hrel
  simp only [Fin.sum_univ_three, ha_def, hxs_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at key
  rw [coef_four_thirds_cube hp0, mul_assoc (t * γ), coef_four_thirds_sq hp0] at key
  have hcube := rhoM_cube hr hY hp hpp hx0
  rw [show p ^ 3 * x = x * p ^ 3 by ring] at hcube
  rw [hcube] at key
  have h1 : ((‖σO p‖ : ℝ) : ℂ)⁻¹ * (((‖σO p‖ : ℝ) : ℂ)⁻¹ * (t * γ * rhoM (x * p) r Y hY) -
      rhoM x r Y hY) = 0 := by linear_combination key
  have h2 := (mul_eq_zero.1 h1).resolve_left (inv_ne_zero hq')
  have h3 := congrArg (fun z => ((‖σO p‖ : ℝ) : ℂ) * z) h2
  simp only [mul_sub, ← mul_assoc, mul_inv_cancel₀ hq', one_mul, mul_zero] at h3
  linear_combination h3

/-- **`ρ(xp) = (3/p)₃²·γ_2(x)·ρ(x)/|p|`** for a primary prime `p ∤ x`, from `rhoM_mul_prime`,
`γ_1(x)·γ_2(x) = N(p) = |p|²` (round 453's `gaussP_one_mul_two`) and `(3/p)₃³ = 1`. -/
theorem rhoM_mul_prime_eq {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p)
    (hpp : Primary p) {x : 𝓞 K} (hpx : ¬ p ∣ x) :
    rhoM (x * p) r Y hY = σO (cub 3 (span {p})) ^ 2 * gaussP x p 2 * rhoM x r Y hY / (‖σO p‖ : ℂ) := by
  have hp0 := hp.ne_zero
  have hq0 : 0 < ‖σO p‖ := norm_pos_iff.2 (σO_ne_zero hp0)
  have hq' : ((‖σO p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have h3 := rhoM_mul_prime hr hY hp hpp hpx
  have ht := cub_three_pow_three hpp
  have hγ : gaussP x p 1 * gaussP x p 2 = ((‖σO p‖ : ℝ) : ℂ) ^ 2 := by
    rw [gaussP_one_mul_two hp hpp hpx, ← Complex.ofReal_natCast, ← normSq_σO, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow]
  rw [eq_div_iff hq']
  apply mul_left_cancel₀ hq'
  linear_combination σO (cub 3 (span {p})) ^ 2 * gaussP x p 2 * h3 -
    gaussP x p 1 * gaussP x p 2 * rhoM (x * p) r Y hY * ht - rhoM (x * p) r Y hY * hγ

end Eis

end

#print axioms Eis.dirL_mul_pow
#print axioms Eis.dirL_p5
#print axioms Eis.dirL_p3
#print axioms Eis.coef_four_thirds_cube
#print axioms Eis.coef_four_thirds_sq
#print axioms Eis.rhoM_mul_sq
#print axioms Eis.rhoM_mul_prime
#print axioms Eis.rhoM_mul_prime_eq
