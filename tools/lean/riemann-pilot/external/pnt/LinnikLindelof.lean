/-
# Round 522, part 2: a Lindelöf bound for `L(s, χ)` on `Re s > 11/12`, uniformly in the modulus

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `σ₀ > 11/12` and `ε > 0` there is `C` such that for every modulus `q ≥ 1`, every Dirichlet
character `χ ≠ 1` mod `q`, every `σ ≥ σ₀` and every real `t`, `|L(σ + it, χ)| ≤ C((q + 2)(|t| + 4))^ε` and
`1/|L(σ + it, χ)| ≤ C((q + 2)(|t| + 4))^ε` (`lindelof`): round 470's `HalfPlaneLindelof.zeta_bound_of_zeroFree` for
`L(s, χ)`, from round 495's half-plane `Eis.LFunction_ne_zero_of_re_gt`, with `C` independent of `q` and `χ` and no
lower bound on `|t|` (`L(s, χ)` has no pole for `χ ≠ 1`).

* `norm_LFunction_le_zeta32`, `inv_norm_LFunction_le_zeta32`: `|L(s, χ)|` and `1/|L(s, χ)|` are at most `ζ(3/2)` on
  `Re s ≥ 3/2`.
* `logDeriv_le`: round 520's `Linnik.logDeriv_LFunction_le` at `θ = 11/12`: `|L′/L(σ + it, χ)| ≤
  KL(11/12, a)·log((q + 2)(|t| + 4))` for `σ ≥ a > 11/12`.
* `logDeriv_le_interp`: that bound interpolated against `|L′/L| ≤ max(−ζ′/ζ(3/2), 1)` on `Re s = 3/2`
  (`ChiUniform.logDeriv_LFunction_right`) by `HalfPlaneLindelof.norm_le_interp` on the rectangle
  `[a, 3/2] × [t − W, t + W]`, with `W` linear in `log((q + 2)(|t| + 4))`.
* `lindelof`: the mean value inequality for `log|L(u + it, χ)|` on `[σ, 3/2]`.
-/
import LinnikHalf
import Subconvexity

open Complex Real Filter Topology Set

noncomputable section

namespace LinnikLindelof

open DirichletCharacter LogDerivDisc ChiUniform

variable {q : ℕ} [NeZero q]

/-! ### A Lindelöf bound for `L(s, χ)` on `Re s > 11/12`, uniformly in the modulus -/

/-- `L(s, χ) ≠ 0` on `Re s > 11/12` for `χ ≠ 1` (round 495's half-plane). -/
theorem LFunction_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : 11 / 12 < s.re) :
    LFunction χ s ≠ 0 :=
  Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)

/-- `‖L(s, χ)‖ ≤ ζ(3/2)` on `Re s ≥ 3/2`. -/
theorem norm_LFunction_le_zeta32 (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖LFunction χ s‖ ≤ zeta32 := by
  rw [LFunction_eq_LSeries χ (by linarith)]
  have hχs : LSeriesSummable (fun n ↦ χ n) ((3 / 2 : ℝ) : ℂ) :=
    ZMod.LSeriesSummable_of_one_lt_re (fun n ↦ χ n) (by norm_num)
  refine (SmoothPerron.norm_LSeries_le_of_le_re hχs hs).trans
    (tsum_norm_term_le (fun n ↦ ?_) summable_one_32)
  rw [norm_one]
  exact DirichletCharacter.norm_le_one _ _

/-- `‖L(s, χ)‖⁻¹ ≤ ζ(3/2)` on `Re s ≥ 3/2`, from `1/L(s, χ) = Σ χ(n)μ(n)n^{−s}`. -/
theorem inv_norm_LFunction_le_zeta32 (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖LFunction χ s‖⁻¹ ≤ zeta32 := by
  have hs1 : 1 < s.re := by linarith
  have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs1
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
  rw [← norm_inv, inv_eq_of_mul_eq_one_right hm]
  have hμ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) ((3 / 2 : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by norm_num))
  refine (SmoothPerron.norm_LSeries_le_of_le_re hμ hs).trans
    (tsum_norm_term_le (fun n ↦ ?_) summable_one_32)
  rw [norm_mul, norm_one]
  refine (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans ?_
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- `L′/L(σ + it, χ)` for `σ ≥ a > 11/12`: round 520's `Linnik.logDeriv_LFunction_le` at `θ = 11/12`, whose disc
lies in the half-plane. -/
theorem logDeriv_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {a σ t : ℝ} (ha : 11 / 12 < a)
    (ha32 : a < 3 / 2) (hσ : a ≤ σ) :
    ‖deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)‖ ≤
      Linnik.KL (11 / 12) a * (Real.log (q + 2) + Real.log (|t| + 4)) := by
  refine Linnik.logDeriv_LFunction_le hχ (by norm_num) ha ha32 hσ (fun s hs ↦ LFunction_ne_zero hχ ?_)
  rw [Metric.mem_ball, Complex.dist_eq] at hs
  have h1 := Complex.abs_re_le_norm (s - ctr t)
  rw [Complex.sub_re, ctr_re] at h1
  have h2 := neg_abs_le (s.re - 3 / 2)
  linarith

/-- The bound on `Re s ≥ 3/2` used for the interpolation. -/
def Bχ : ℝ := max logDerivZeta32 1

lemma one_le_Bχ : 1 ≤ Bχ := le_max_right _ _

/-- `log((q + 2)(|t| + 4))`, split. -/
def L0 (q : ℕ) (t : ℝ) : ℝ := Real.log (q + 2) + Real.log (|t| + 4)

lemma L0_nonneg (q : ℕ) (t : ℝ) : 0 ≤ L0 q t := by
  unfold L0
  have h1 : 0 ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
  have h2 : 0 ≤ Real.log (|t| + 4) := Real.log_nonneg (by linarith [abs_nonneg t])
  linarith

/-- The half-height of the interpolation rectangle. -/
def Wχ (a : ℝ) (q : ℕ) (t : ℝ) : ℝ := Bχ + Linnik.KL (11 / 12) a * L0 q t + Linnik.KL (11 / 12) a + 1

/-- The bound on the whole interpolation rectangle. -/
def Aχ (a : ℝ) (q : ℕ) (t : ℝ) : ℝ := Bχ + Linnik.KL (11 / 12) a * (L0 q t + Wχ a q t)

/-- **The interpolated bound on `L′/L`.** For `χ ≠ 1`, `11/12 < a < 3/2` and `u ∈ [a, 3/2]`,
`|L′/L(u + it, χ)| ≤ e^{9/4 − u²}A^{(3/2−u)/(3/2−a)}B^{(u−a)/(3/2−a)}`, with `A = Aχ a q t` linear in
`log((q + 2)(|t| + 4))` and `B = Bχ` absolute: `HalfPlaneLindelof.norm_le_interp` on the rectangle
`[a, 3/2] × [t − W, t + W]`, `W = Wχ a q t`. -/
theorem logDeriv_le_interp {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {a u t : ℝ} (ha : 11 / 12 < a)
    (ha32 : a < 3 / 2) (hu : u ∈ Icc a (3 / 2)) :
    ‖deriv (LFunction χ) (u + t * I) / LFunction χ (u + t * I)‖ ≤
      Real.exp ((3 / 2) ^ 2 - u ^ 2) * Aχ a q t ^ ((3 / 2 - u) / (3 / 2 - a)) *
        Bχ ^ ((u - a) / (3 / 2 - a)) := by
  set KL := Linnik.KL (11 / 12) a with hKL
  have hK0 : 0 < KL := Linnik.KL_pos ha ha32
  have hB1 := one_le_Bχ
  have hL0 := L0_nonneg q t
  set W := Wχ a q t with hW
  have hWdef : W = Bχ + KL * L0 q t + KL + 1 := rfl
  have hW1 : 1 ≤ W := by rw [hWdef]; nlinarith
  set A := Aχ a q t with hA
  have hAdef : A = Bχ + KL * (L0 q t + W) := rfl
  have hBA : Bχ ≤ A := by rw [hAdef]; nlinarith
  set R : Set ℂ := Icc a (3 / 2) ×ℂ Icc (t - W) (t + W) with hR
  have hre : ∀ z ∈ R, a ≤ z.re := fun z hz => hz.1.1
  have hF : DifferentiableOn ℂ (fun z => deriv (LFunction χ) z / LFunction χ z) R := by
    intro z hz
    have hz0 : LFunction χ z ≠ 0 := LFunction_ne_zero hχ (by linarith [hre z hz])
    have hdL : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ
    exact (((hdL.analyticAt z).deriv.differentiableAt).div (hdL z) hz0).differentiableWithinAt
  have hall : ∀ z ∈ R, ‖deriv (LFunction χ) z / LFunction χ z‖ ≤ A := by
    intro z hz
    have hzi : z.im ∈ Icc (t - W) (t + W) := hz.2
    have h := logDeriv_le hχ (t := z.im) ha ha32 (hre z hz)
    rw [Complex.re_add_im] at h
    refine h.trans ?_
    have him : |z.im| + 4 ≤ (|t| + 4) * (1 + W) := by
      have h1 : |z.im| ≤ |t| + W := by
        rw [abs_le]; constructor <;> linarith [hzi.1, hzi.2, neg_abs_le t, le_abs_self t]
      nlinarith [abs_nonneg t]
    have hlog : Real.log (|z.im| + 4) ≤ Real.log (|t| + 4) + W := by
      have h1 : Real.log (|z.im| + 4) ≤ Real.log ((|t| + 4) * (1 + W)) :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) him
      rw [Real.log_mul (by linarith [abs_nonneg t]) (by linarith)] at h1
      have h2 : Real.log (1 + W) ≤ W := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + W by linarith); linarith
      linarith
    rw [hAdef]
    unfold L0
    nlinarith
  have hright : ∀ y ∈ Icc (t - W) (t + W),
      ‖deriv (LFunction χ) (((3 / 2 : ℝ) : ℂ) + y * I) / LFunction χ (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ Bχ :=
    fun y _ => (logDeriv_LFunction_right χ (by simp)).trans (le_max_left _ _)
  have hWlog : Real.log (A / Bχ) ≤ W ^ 2 := by
    have hApos : 0 < A / Bχ := div_pos (by linarith) (by linarith)
    have h1 : Real.log (A / Bχ) ≤ A / Bχ - 1 := Real.log_le_sub_one_of_pos hApos
    have h2 : A / Bχ ≤ A := div_le_self (by linarith) hB1
    have h3 : A ≤ W ^ 2 := by
      rw [hAdef]
      have e : W ^ 2 - (Bχ + KL * (L0 q t + W)) = (W - 1) * (Bχ + KL * L0 q t) + W := by
        rw [hWdef]; ring
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ W - 1)
        (by nlinarith : (0 : ℝ) ≤ Bχ + KL * L0 q t)]
    linarith
  exact HalfPlaneLindelof.norm_le_interp (by linarith) ha32 (by linarith) (by linarith) hBA hF hall
    hright hWlog hu

/-- `y^κ ≤ δy + Y` for all `y ≥ 0`, when `0 ≤ κ < 1` and `δ > 0`. -/
theorem rpow_le_mul_add {κ δ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1) (hδ : 0 < δ) :
    ∃ Y : ℝ, 0 ≤ Y ∧ ∀ y : ℝ, 0 ≤ y → y ^ κ ≤ δ * y + Y := by
  obtain ⟨Y, hY0, hY⟩ := HalfPlaneLindelof.rpow_le_mul_self hκ hδ
  refine ⟨Y + 1, by linarith, fun y hy => ?_⟩
  rcases le_or_gt Y y with h | h
  · have := hY y h; nlinarith
  · rcases le_or_gt y 1 with h1 | h1
    · have : y ^ κ ≤ 1 := Real.rpow_le_one hy h1 hκ0
      nlinarith
    · have : y ^ κ ≤ y := by
        calc y ^ κ ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le hκ.le
          _ = y := Real.rpow_one y
      nlinarith

/-- **A Lindelöf bound for `L(s, χ)`, uniformly in the modulus.** For `σ₀ > 11/12` and `ε > 0` there is `C` such
that for every modulus `q ≥ 1`, every Dirichlet character `χ ≠ 1` mod `q`, every `σ ≥ σ₀` and every real `t`,
`|L(σ + it, χ)| ≤ C((q + 2)(|t| + 4))^ε` and `1/|L(σ + it, χ)| ≤ C((q + 2)(|t| + 4))^ε`: the mean value inequality
for `log|L(u + it, χ)|` on `[σ, 3/2]`, with the interpolated bound `e^{9/4}A^κB`, `κ < 1`. -/
theorem lindelof {σ₀ ε : ℝ} (hσ₀ : 11 / 12 < σ₀) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ t : ℝ, σ₀ ≤ σ →
      ‖LFunction χ (σ + t * I)‖ ≤ C * (((q : ℝ) + 2) * (|t| + 4)) ^ ε ∧
        ‖LFunction χ (σ + t * I)‖⁻¹ ≤ C * (((q : ℝ) + 2) * (|t| + 4)) ^ ε := by
  set σ₁ : ℝ := min σ₀ (5 / 4) with hσ₁
  have hθσ₁ : 11 / 12 < σ₁ := lt_min hσ₀ (by norm_num)
  have hσ₁σ₀ : σ₁ ≤ σ₀ := min_le_left _ _
  have hσ₁54 : σ₁ ≤ 5 / 4 := min_le_right _ _
  set a : ℝ := (11 / 12 + σ₁) / 2 with ha
  have hθa : 11 / 12 < a := by linarith
  have haσ₁ : a < σ₁ := by linarith
  have ha32 : a < 3 / 2 := by linarith
  set KL := Linnik.KL (11 / 12) a with hKL
  have hK0 : 0 < KL := Linnik.KL_pos hθa ha32
  have hB1 := one_le_Bχ
  set κ : ℝ := (3 / 2 - σ₁) / (3 / 2 - a) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by linarith)
  have hκ1 : κ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set K : ℝ := Real.exp ((3 / 2) ^ 2) * Bχ * (3 / 2) with hK
  have hK0' : 0 < K := by positivity
  set c₁ : ℝ := KL * (1 + KL) with hc₁
  set c₂ : ℝ := Bχ + KL * (Bχ + KL + 1) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hAc : ∀ (q : ℕ) (t : ℝ), Aχ a q t = c₁ * L0 q t + c₂ := fun q t => by
    simp only [Aχ, Wχ, hc₁, hc₂, hKL]; ring
  set δ : ℝ := ε / (K * c₁ + 1) with hδ
  have hKc : 0 < K * c₁ + 1 := by positivity
  have hδ0 : 0 < δ := div_pos hε hKc
  have hKδ : K * δ * c₁ ≤ ε := by
    rw [hδ, show K * (ε / (K * c₁ + 1)) * c₁ = ε * (K * c₁ / (K * c₁ + 1)) by ring]
    have : K * c₁ / (K * c₁ + 1) ≤ 1 := (div_le_one hKc).2 (by linarith)
    exact mul_le_of_le_one_right hε.le this
  obtain ⟨Y, hY0, hY⟩ := rpow_le_mul_add hκ0 hκ1 hδ0
  have hz0 := zeta32_nonneg
  set M : ℝ := Real.log zeta32 + K * (δ * c₂ + Y) with hM
  refine ⟨max (Real.exp M) zeta32 + 1, by positivity, fun q _ χ hχ σ t hσ => ?_⟩
  set P : ℝ := ((q : ℝ) + 2) * (|t| + 4) with hP
  have hP1 : 1 ≤ P := by
    have := Nat.cast_nonneg (α := ℝ) q
    nlinarith [abs_nonneg t]
  have hPε : 1 ≤ P ^ ε := Real.one_le_rpow hP1 hε.le
  have hL0P : L0 q t = Real.log P := by
    rw [hP, Real.log_mul (by have := Nat.cast_nonneg (α := ℝ) q; linarith) (by linarith [abs_nonneg t])]
    rfl
  set C := max (Real.exp M) zeta32 + 1 with hC
  have hCZ : zeta32 ≤ C := by rw [hC]; linarith [le_max_right (Real.exp M) zeta32]
  have hCM : Real.exp M ≤ C := by rw [hC]; linarith [le_max_left (Real.exp M) zeta32]
  have hC0 : 0 ≤ C := by positivity
  by_cases h32 : 3 / 2 ≤ σ
  · have hre : 3 / 2 ≤ ((σ : ℂ) + t * I).re := by simpa using h32
    constructor
    · calc ‖LFunction χ (σ + t * I)‖ ≤ zeta32 := norm_LFunction_le_zeta32 χ hre
        _ ≤ C := hCZ
        _ ≤ C * P ^ ε := le_mul_of_one_le_right hC0 hPε
    · calc ‖LFunction χ (σ + t * I)‖⁻¹ ≤ zeta32 := inv_norm_LFunction_le_zeta32 χ hre
        _ ≤ C := hCZ
        _ ≤ C * P ^ ε := le_mul_of_one_le_right hC0 hPε
  · push Not at h32
    have hσa : a < σ := by linarith
    set A : ℝ := Aχ a q t with hA
    have hA1 : 1 ≤ A := by
      rw [hA, hAc]; have := L0_nonneg q t; nlinarith
    -- the interpolated bound at every `u ∈ [σ, 3/2]`
    have hbound : ∀ u ∈ Icc σ (3 / 2),
        ‖deriv (LFunction χ) (u + t * I) / LFunction χ (u + t * I)‖ ≤ Real.exp ((3 / 2) ^ 2) * A ^ κ * Bχ := by
      intro u hu
      have hua : u ∈ Icc a (3 / 2) := ⟨by linarith [hu.1], hu.2⟩
      have h := logDeriv_le_interp hχ (t := t) hθa ha32 hua
      refine h.trans ?_
      have e1 : Real.exp ((3 / 2) ^ 2 - u ^ 2) ≤ Real.exp ((3 / 2) ^ 2) :=
        Real.exp_le_exp.2 (by linarith [sq_nonneg u])
      have e2 : A ^ ((3 / 2 - u) / (3 / 2 - a)) ≤ A ^ κ := by
        apply Real.rpow_le_rpow_of_exponent_le hA1
        rw [hκ]
        exact div_le_div_of_nonneg_right (by linarith [hu.1]) (by linarith)
      have e3 : Bχ ^ ((u - a) / (3 / 2 - a)) ≤ Bχ := by
        calc Bχ ^ ((u - a) / (3 / 2 - a)) ≤ Bχ ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hB1 ((div_le_one (by linarith)).2 (by linarith [hu.2]))
          _ = Bχ := Real.rpow_one Bχ
      have p1 : 0 ≤ A ^ ((3 / 2 - u) / (3 / 2 - a)) := Real.rpow_nonneg (by linarith) _
      have p2 : 0 ≤ Bχ ^ ((u - a) / (3 / 2 - a)) := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul (mul_le_mul e1 e2 p1 (Real.exp_pos _).le) e3 p2
        (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _))
    -- the mean value inequality for `log|L(u + it, χ)|` on `[σ, 3/2]`
    set g : ℝ → ℝ := fun u => Real.log ‖LFunction χ (u + t * I)‖ with hg
    have hderiv : ∀ u ∈ Icc σ (3 / 2), HasDerivWithinAt g
        ((deriv (LFunction χ) (u + t * I) / LFunction χ (u + t * I)).re) (Icc σ (3 / 2)) u := by
      intro u hu
      have hz : LFunction χ ((u : ℂ) + t * I) ≠ 0 := LFunction_ne_zero hχ (by simp; linarith [hu.1])
      have hd : HasDerivAt (fun x : ℂ => LFunction χ (x + t * I)) (deriv (LFunction χ) (u + t * I)) u :=
        ((differentiable_LFunction hχ _).hasDerivAt).comp_add_const _ _
      exact (HalfPlaneLindelof.hasDerivAt_log_norm hd.comp_ofReal hz).hasDerivWithinAt
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
      (fun u hu => (Complex.abs_re_le_norm _).trans (hbound u hu)) (convex_Icc σ (3 / 2))
      (left_mem_Icc.2 h32.le) (right_mem_Icc.2 h32.le)
    -- the endpoint `u = 3/2`
    have hre32 : 3 / 2 ≤ (((3 / 2 : ℝ) : ℂ) + t * I).re := by simp
    have hz32 : 0 < ‖LFunction χ (((3 / 2 : ℝ) : ℂ) + t * I)‖ :=
      norm_pos_iff.2 (LFunction_ne_zero hχ (by simp; norm_num))
    have hg32 : |g (3 / 2)| ≤ Real.log zeta32 := by
      have u1 := norm_LFunction_le_zeta32 χ hre32
      have u2 := inv_norm_LFunction_le_zeta32 χ hre32
      rw [abs_le]
      constructor
      · have := Real.log_le_log (inv_pos.2 hz32) u2
        rw [Real.log_inv] at this
        simp only [hg]
        linarith
      · exact Real.log_le_log hz32 u1
    -- the size of the interpolated bound
    have hAκ : A ^ κ ≤ δ * (c₁ * L0 q t + c₂) + Y :=
      calc A ^ κ ≤ δ * A + Y := hY A (by linarith)
        _ = δ * (c₁ * L0 q t + c₂) + Y := by rw [hA, hAc]
    have hAκ0 : 0 ≤ A ^ κ := Real.rpow_nonneg (by linarith) _
    have hL0 := L0_nonneg q t
    have hL : |g σ| ≤ M + ε * L0 q t := by
      have h1 : |g σ| ≤ |g (3 / 2)| + |g (3 / 2) - g σ| := by
        have := abs_sub (g (3 / 2)) (g (3 / 2) - g σ)
        rwa [sub_sub_cancel] at this
      have h2 : |g (3 / 2) - g σ| ≤ K * A ^ κ := by
        have hm := hmvt
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 - σ)] at hm
        have hE : 0 ≤ Real.exp ((3 / 2) ^ 2) * A ^ κ * Bχ :=
          mul_nonneg (mul_nonneg (Real.exp_pos _).le hAκ0) (by linarith)
        have h4 : Real.exp ((3 / 2) ^ 2) * A ^ κ * Bχ * (3 / 2 - σ) ≤
            Real.exp ((3 / 2) ^ 2) * A ^ κ * Bχ * (3 / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hE
        have h5 : Real.exp ((3 / 2) ^ 2) * A ^ κ * Bχ * (3 / 2) = K * A ^ κ := by rw [hK]; ring
        linarith
      have h3 : K * A ^ κ ≤ K * (δ * c₂ + Y) + ε * L0 q t := by
        have h4 := mul_le_mul_of_nonneg_left hAκ hK0'.le
        have h5 : K * δ * c₁ * L0 q t ≤ ε * L0 q t := mul_le_mul_of_nonneg_right hKδ hL0
        have h6 : K * (δ * (c₁ * L0 q t + c₂) + Y) = K * (δ * c₂ + Y) + K * δ * c₁ * L0 q t := by ring
        linarith
      rw [hM]
      linarith
    have hzσ : 0 < ‖LFunction χ (σ + t * I)‖ := norm_pos_iff.2 (LFunction_ne_zero hχ (by simp; linarith))
    have hpow : P ^ ε = Real.exp (ε * L0 q t) := by
      rw [Real.rpow_def_of_pos (by linarith), hL0P, mul_comm]
    have hgσ : g σ = Real.log ‖LFunction χ (σ + t * I)‖ := rfl
    rw [hgσ] at hL
    constructor
    · calc ‖LFunction χ (σ + t * I)‖ = Real.exp (Real.log ‖LFunction χ (σ + t * I)‖) :=
            (Real.exp_log hzσ).symm
        _ ≤ Real.exp (M + ε * L0 q t) := Real.exp_le_exp.2 (le_of_abs_le hL)
        _ = Real.exp M * P ^ ε := by rw [Real.exp_add, hpow]
        _ ≤ C * P ^ ε := by gcongr
    · calc ‖LFunction χ (σ + t * I)‖⁻¹ = Real.exp (-Real.log ‖LFunction χ (σ + t * I)‖) := by
            rw [Real.exp_neg, Real.exp_log hzσ]
        _ ≤ Real.exp (M + ε * L0 q t) := Real.exp_le_exp.2 (by
            linarith [neg_abs_le (Real.log ‖LFunction χ (σ + t * I)‖),
              neg_le_abs (Real.log ‖LFunction χ (σ + t * I)‖)])
        _ = Real.exp M * P ^ ε := by rw [Real.exp_add, hpow]
        _ ≤ C * P ^ ε := by gcongr

end LinnikLindelof

#print axioms LinnikLindelof.norm_LFunction_le_zeta32
#print axioms LinnikLindelof.inv_norm_LFunction_le_zeta32
#print axioms LinnikLindelof.logDeriv_le_interp
#print axioms LinnikLindelof.lindelof
