/-
# Round 480: Littlewood's bounds for `L(1, χ)` at the real characters

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. There is `C` with `|log|L(1, χ)|| ≤ log log log(N + 16) + C` for every quadratic Dirichlet
character `χ ≠ 1` mod `N` (`abs_log_norm_LFunction_one_le`). So `|L(1, χ)| ≤ C′ log log(N + 16)`
(`norm_LFunction_one_le`) and `|L(1, χ)| ≥ c/log log(N + 16)` (`norm_LFunction_one_ge`). No hypothesis.

* `norm_LSeries_le_of_sum_le`: partial summation. If `|Σ_{1 ≤ k ≤ t} f(k)| ≤ Kt^α` for `t ≥ 1`, with
  `0 ≤ α < σ`, and `L(f, σ)` converges absolutely, then `|L(f, σ)| ≤ σK/(σ − α)` (Mathlib's
  `LSeries_eq_mul_integral`).
* `logDeriv_le_loglog`: `|L′/L(σ, χ)| ≤ M log log(N + 16)` for `1 < σ ≤ 2`. The partial sums of `χΛ` are at most
  `ψ(t) ≤ (log 4 + 4)t` (Mathlib's `Chebyshev.psi_le_const_mul_self`) and, by `ChiUniform.psiChi_le_uniform`,
  at most `C₁ log(N + 2)·t^{23/24}`. With `D = log 4 + 4 + C₁` and `l = 1/log log(N + 16)`, interpolating the two
  gives `D(log(N + 16))^l·t^{1−l/24} = eD·t^{1−l/24}`, and partial summation gives `48eD log log(N + 16)`.
* `norm_LFunction_le_real`: `|L(σ, χ)|` and `1/|L(σ, χ)| = |L(χμ, σ)|` are at most `σ/(σ − 1)` for `σ > 1`.
* `abs_log_norm_LFunction_one_le`: the mean value theorem for `log|L(σ, χ)|` on `[1, 1 + 1/log log(N + 16)]`,
  whose derivative is `Re L′/L(σ, χ)` (round 470's `HalfPlaneLindelof.hasDerivAt_log_norm`); `L(σ, χ) ≠ 0` for
  `σ ≥ 1` by round 477's half-plane.
-/
import ChiUniform

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

namespace Littlewood

open ChiPNT

/-! ### Partial summation for an L-series -/

/-- **Partial summation for an L-series.** If the partial sums of `f` are at most `K t^α` for `t ≥ 1`,
with `0 ≤ α < σ`, and `L(f, σ)` converges absolutely, then `|L(f, σ)| ≤ σK/(σ − α)`. -/
theorem norm_LSeries_le_of_sum_le {f : ℕ → ℂ} {α σ K : ℝ} (hα : 0 ≤ α) (hασ : α < σ)
    (hS : LSeriesSummable f σ)
    (hb : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤ K * t ^ α) :
    ‖LSeries f σ‖ ≤ σ * K / (σ - α) := by
  have hσ : 0 < σ := by linarith
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hb 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at this
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ α := by
    refine IsBigO.of_bound K ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := hb n (by exact_mod_cast hn)
    rw [Nat.floor_natCast] at h
    rwa [Real.norm_of_nonneg (by positivity)]
  rw [LSeries_eq_mul_integral f hα (by simpa using hασ) hS hO, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hσ.le, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hσ.le
  have hint : IntegrableOn (fun t : ℝ ↦ K * t ^ (α - σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul K
  calc ‖∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-((σ : ℂ) + 1))‖
      ≤ ∫ t in Ioi (1 : ℝ), K * t ^ (α - σ - 1) := by
        refine norm_integral_le_of_norm_le hint ?_
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht ↦ ?_)
        have ht1 : 1 < t := ht
        have ht0 : 0 < t := by linarith
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-((σ : ℂ) + 1)).re = -(σ + 1) := by simp
        rw [hre]
        calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ * t ^ (-(σ + 1)) ≤ K * t ^ α * t ^ (-(σ + 1)) :=
              mul_le_mul_of_nonneg_right (hb t ht1.le) (by positivity)
          _ = K * t ^ (α - σ - 1) := by
              rw [mul_assoc, ← Real.rpow_add ht0]
              congr 2
              ring
    _ = K / (σ - α) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
        have h1 : α - σ - 1 + 1 = -(σ - α) := by ring
        have h2 : σ - α ≠ 0 := by linarith
        rw [h1]
        field_simp

/-! ### The log-derivative on `(1, 2]`, uniformly in the modulus -/

/-- `|ψ(x, χ)| ≤ ψ(x) ≤ (log 4 + 4)x` for `x ≥ 0` (Mathlib's `Chebyshev.psi_le_const_mul_self`). -/
lemma norm_psiChi_le {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 ≤ x) :
    ‖psiChi χ x‖ ≤ (Real.log 4 + 4) * x := by
  refine le_trans ?_ (Chebyshev.psi_le_const_mul_self hx)
  rw [psiChi, Chebyshev.psi_eq_sum_Icc]
  calc ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
        refine Finset.sum_le_sum fun n _ ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (DirichletCharacter.norm_le_one _ _)
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (Nat.zero_le 1))
          fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg

/-- `a ≤ b₁^{1−l}·b₂^l` when `0 ≤ a ≤ b₁`, `a ≤ b₂` and `0 ≤ l ≤ 1`. -/
lemma le_rpow_mul_rpow {a b₁ b₂ l : ℝ} (ha : 0 ≤ a) (h1 : a ≤ b₁) (h2 : a ≤ b₂) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) : a ≤ b₁ ^ (1 - l) * b₂ ^ l := by
  calc a = a ^ (1 - l) * a ^ l := by
        rw [← Real.rpow_add' ha (by norm_num), sub_add_cancel, Real.rpow_one]
    _ ≤ b₁ ^ (1 - l) * b₂ ^ l :=
        mul_le_mul (Real.rpow_le_rpow ha h1 (by linarith)) (Real.rpow_le_rpow ha h2 hl0)
          (Real.rpow_nonneg ha _) (Real.rpow_nonneg (ha.trans h1) _)

/-- `e < log(N + 16)`, so `log log(N + 16) > 1`. -/
lemma exp_one_lt_log (N : ℕ) : Real.exp 1 < Real.log (N + 16) := by
  have h1 : Real.log 16 ≤ Real.log (N + 16) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  have := Real.exp_one_lt_d9
  linarith

lemma one_lt_loglog (N : ℕ) : 1 < Real.log (Real.log (N + 16)) := by
  have h := exp_one_lt_log N
  rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos 1])]
  exact h

/-- **The log-derivative on `(1, 2]`, uniformly in the modulus.** There is `M` with
`|L′/L(σ, χ)| ≤ M log log(N + 16)` for every quadratic Dirichlet character `χ ≠ 1` mod `N` and every
`1 < σ ≤ 2`. -/
theorem logDeriv_le_loglog :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        ‖deriv (DirichletCharacter.LFunction χ) σ / DirichletCharacter.LFunction χ σ‖ ≤
          M * Real.log (Real.log (N + 16)) := by
  obtain ⟨C₁, hC₁, hψ⟩ := ChiUniform.psiChi_le_uniform (η := 1 / 24) (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set D : ℝ := Real.log 4 + 4 + C₁ with hDdef
  have hD : 0 < D := by linarith
  refine ⟨48 * D * Real.exp 1, by positivity, fun N _ χ hq hχ σ hσ1 hσ2 ↦ ?_⟩
  set L : ℝ := Real.log (N + 16) with hLdef
  have hL : Real.exp 1 < L := exp_one_lt_log N
  have hL0 : 0 < L := by linarith [Real.exp_pos 1]
  set ℓ : ℝ := Real.log L with hℓdef
  have hℓ : 1 < ℓ := one_lt_loglog N
  have hℓ0 : ℓ ≠ 0 := by linarith
  set l : ℝ := 1 / ℓ with hldef
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hldef, div_le_one (by linarith)]; linarith
  set α : ℝ := 1 - l / 24 with hαdef
  have hlog2 : 0 ≤ Real.log (N + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hlogL : Real.log (N + 2) ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hLl : L ^ l = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hL0, ← hℓdef, hldef]
    congr 1
    field_simp
  -- the interpolated bound on the partial sums
  have hb : ∀ t : ℝ, 1 ≤ t → ‖psiChi χ t‖ ≤ D * Real.exp 1 * t ^ α := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have h1 : ‖psiChi χ t‖ ≤ D * t :=
      (norm_psiChi_le χ ht0.le).trans (mul_le_mul_of_nonneg_right (by linarith) ht0.le)
    have h2 : ‖psiChi χ t‖ ≤ D * L * t ^ (23 / 24 : ℝ) := by
      rcases eq_or_lt_of_le ht with h | ht1
      · have h0 : psiChi χ t = 0 := by
          rw [← h]
          simp [psiChi]
        rw [h0, norm_zero]
        positivity
      · have h := hψ N χ hq hχ t ht1
        have e : (11 / 12 + 1 / 24 : ℝ) = 23 / 24 := by norm_num
        rw [e] at h
        refine h.trans ?_
        have ht' : 0 ≤ t ^ (23 / 24 : ℝ) := by positivity
        have hC₁D : C₁ ≤ D := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul hC₁D hlogL hlog2 hD.le) ht'
    have h3 := le_rpow_mul_rpow (norm_nonneg _) h1 h2 hl0.le hl1
    calc ‖psiChi χ t‖ ≤ (D * t) ^ (1 - l) * (D * L * t ^ (23 / 24 : ℝ)) ^ l := h3
      _ = (D ^ (1 - l) * D ^ l) * L ^ l * (t ^ (1 - l) * t ^ (23 / 24 * l)) := by
          rw [Real.mul_rpow hD.le ht0.le, Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow hD.le hL0.le, ← Real.rpow_mul ht0.le]
          ring
      _ = D * Real.exp 1 * t ^ α := by
          rw [← Real.rpow_add hD, sub_add_cancel, Real.rpow_one, hLl, ← Real.rpow_add ht0]
          congr 2
          rw [hαdef]
          ring
  -- the L-series bound
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ1
  rw [← norm_neg, ← LSeries_twist_vonMangoldt_eq_LFunction χ hs]
  have hS : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hα0 : 0 ≤ α := by rw [hαdef]; linarith
  have hασ : α < σ := by rw [hαdef]; linarith
  have hσα : l / 24 ≤ σ - α := by rw [hαdef]; linarith
  calc ‖LSeries (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ‖
      ≤ σ * (D * Real.exp 1) / (σ - α) := norm_LSeries_le_of_sum_le hα0 hασ hS hb
    _ ≤ 2 * (D * Real.exp 1) / (l / 24) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hσ2 (by positivity))
          (by positivity) hσα
    _ = 48 * D * Real.exp 1 * ℓ := by
        rw [hldef]
        field_simp
        ring

/-! ### `L(σ, χ)` near `1` -/

/-- `|L(σ, χ)| ≤ σ/(σ − 1)` and `1/|L(σ, χ)| ≤ σ/(σ − 1)` for `σ > 1`, from the partial sums of `χ` and
of `χμ`, each at most `t` in absolute value. -/
lemma norm_LFunction_le_real {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ‖DirichletCharacter.LFunction χ σ‖ ≤ σ / (σ - 1) ∧
      ‖DirichletCharacter.LFunction χ σ‖⁻¹ ≤ σ / (σ - 1) := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hcount : ∀ g : ℕ → ℂ, (∀ n, ‖g n‖ ≤ 1) → ∀ t : ℝ, 1 ≤ t →
      ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, g k‖ ≤ 1 * t ^ (1 : ℝ) := by
    intro g hg t ht
    rw [Real.rpow_one, one_mul]
    calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, g k‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖g k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ hg k
      _ = ⌊t⌋₊ := by simp
      _ ≤ t := Nat.floor_le (by linarith)
  have hd : σ * 1 / (σ - 1) = σ / (σ - 1) := by ring
  constructor
  · rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← hd]
    exact norm_LSeries_le_of_sum_le zero_le_one hσ
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)
      (hcount _ fun n ↦ DirichletCharacter.norm_le_one _ _)
  · have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← norm_inv, inv_eq_of_mul_eq_one_right hm,
      ← hd]
    have hμ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) σ :=
      DirichletCharacter.LSeriesSummable_mul χ
        (ArithmeticFunction.LSeriesSummable_moebius_iff.2 hs)
    refine norm_LSeries_le_of_sum_le zero_le_one hσ hμ (hcount _ fun n ↦ ?_)
    show ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans ?_
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-! ### Littlewood's bounds for `L(1, χ)` -/

/-- **Littlewood's bounds for `L(1, χ)`**: there is `C` with
`|log |L(1, χ)|| ≤ log log log(N + 16) + C` for every quadratic Dirichlet character `χ ≠ 1` mod `N`. -/
theorem abs_log_norm_LFunction_one_le :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      |Real.log ‖DirichletCharacter.LFunction χ 1‖| ≤ Real.log (Real.log (Real.log (N + 16))) + C := by
  obtain ⟨M, hM, hlog⟩ := logDeriv_le_loglog
  refine ⟨M + Real.log 2, fun N _ χ hq hχ ↦ ?_⟩
  set ℓ : ℝ := Real.log (Real.log (N + 16)) with hℓdef
  have hℓ : 1 < ℓ := one_lt_loglog N
  have hℓ0 : ℓ ≠ 0 := by linarith
  set σ₂ : ℝ := 1 + 1 / ℓ with hσ₂def
  have hiℓ : 0 < 1 / ℓ := by positivity
  have hiℓ1 : 1 / ℓ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hσ₂1 : 1 < σ₂ := by linarith
  have hσ₂2 : σ₂ ≤ 2 := by linarith
  have hF := DirichletCharacter.differentiable_LFunction hχ
  have hzf : ∀ u : ℝ, 1 ≤ u → DirichletCharacter.LFunction χ u ≠ 0 := fun u hu ↦
    Eis.RealChar.LFunction_ne_zero_of_isQuadratic hq (by simp; linarith) (Or.inl hχ)
  set φ : ℝ → ℝ := fun u ↦ Real.log ‖DirichletCharacter.LFunction χ u‖ with hφdef
  have hcont : ContinuousOn φ (Icc 1 σ₂) :=
    ((hF.continuous.comp continuous_ofReal).norm.continuousOn).log
      fun u hu ↦ norm_ne_zero_iff.2 (hzf u hu.1)
  have hderiv : ∀ u ∈ Ioo 1 σ₂, HasDerivAt φ
      ((deriv (DirichletCharacter.LFunction χ) u / DirichletCharacter.LFunction χ u).re) u :=
    fun u hu ↦ HalfPlaneLindelof.hasDerivAt_log_norm ((hF u).hasDerivAt.comp_ofReal) (hzf u hu.1.le)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope φ _ hσ₂1 hcont hderiv
  -- the mean value step
  have hdiff : |φ σ₂ - φ 1| ≤ M := by
    have h1 : φ σ₂ - φ 1 = (deriv (DirichletCharacter.LFunction χ) c /
        DirichletCharacter.LFunction χ c).re * (σ₂ - 1) := by
      rw [hslope]
      have : σ₂ - 1 ≠ 0 := by linarith
      field_simp
    have h2 := hlog N χ hq hχ c hc.1 (by linarith [hc.2])
    rw [h1, abs_mul, abs_of_pos (by linarith : 0 < σ₂ - 1)]
    have h3 : σ₂ - 1 = 1 / ℓ := by rw [hσ₂def]; ring
    calc |(deriv (DirichletCharacter.LFunction χ) c / DirichletCharacter.LFunction χ c).re| *
          (σ₂ - 1) ≤ M * ℓ * (1 / ℓ) := by
          rw [h3]
          exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans h2) hiℓ.le
      _ = M := by field_simp
  -- the value at `σ₂`
  obtain ⟨hup, hlow⟩ := norm_LFunction_le_real χ hσ₂1
  have hpos : 0 < ‖DirichletCharacter.LFunction χ σ₂‖ := norm_pos_iff.2 (hzf σ₂ hσ₂1.le)
  have hval : σ₂ / (σ₂ - 1) = ℓ + 1 := by
    rw [hσ₂def]
    field_simp
    ring
  have hle : Real.log (σ₂ / (σ₂ - 1)) ≤ Real.log 2 + Real.log ℓ := by
    rw [hval, ← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hφσ₂ : |φ σ₂| ≤ Real.log 2 + Real.log ℓ := by
    rw [abs_le]
    constructor
    · have h := Real.log_le_log (inv_pos.2 hpos) hlow
      rw [Real.log_inv] at h
      show -(Real.log 2 + Real.log ℓ) ≤ Real.log ‖DirichletCharacter.LFunction χ σ₂‖
      linarith
    · have h := Real.log_le_log hpos hup
      show Real.log ‖DirichletCharacter.LFunction χ σ₂‖ ≤ Real.log 2 + Real.log ℓ
      linarith
  have hφ1 : φ 1 = Real.log ‖DirichletCharacter.LFunction χ 1‖ := by
    simp only [hφdef, Complex.ofReal_one]
  rw [← hφ1]
  obtain ⟨d1, d2⟩ := abs_le.1 hdiff
  obtain ⟨e1, e2⟩ := abs_le.1 hφσ₂
  rw [abs_le]
  constructor <;> linarith

/-- **`L(1, χ) ≪ log log q`**: there is `C > 0` with `|L(1, χ)| ≤ C log log(N + 16)` for every quadratic
Dirichlet character `χ ≠ 1` mod `N`. -/
theorem norm_LFunction_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ 1‖ ≤ C * Real.log (Real.log (N + 16)) := by
  obtain ⟨C, hC⟩ := abs_log_norm_LFunction_one_le
  refine ⟨Real.exp C, Real.exp_pos C, fun N _ χ hq hχ ↦ ?_⟩
  have hpos : 0 < ‖DirichletCharacter.LFunction χ 1‖ :=
    norm_pos_iff.2 (Eis.RealChar.LFunction_ne_zero_of_isQuadratic hq (by norm_num) (Or.inl hχ))
  have hℓ : 0 < Real.log (Real.log (N + 16)) := by linarith [one_lt_loglog N]
  have h1 := (abs_le.1 (hC N χ hq hχ)).2
  calc ‖DirichletCharacter.LFunction χ 1‖
      = Real.exp (Real.log ‖DirichletCharacter.LFunction χ 1‖) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (Real.log (Real.log (Real.log (N + 16))) + C) := Real.exp_le_exp.2 h1
    _ = Real.exp C * Real.log (Real.log (N + 16)) := by
        rw [Real.exp_add, Real.exp_log hℓ]
        ring

/-- **`L(1, χ) ≫ 1/log log q`**: there is `c > 0` with `|L(1, χ)| ≥ c/log log(N + 16)` for every quadratic
Dirichlet character `χ ≠ 1` mod `N`. -/
theorem norm_LFunction_one_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      c / Real.log (Real.log (N + 16)) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  obtain ⟨C, hC⟩ := abs_log_norm_LFunction_one_le
  refine ⟨Real.exp (-C), Real.exp_pos _, fun N _ χ hq hχ ↦ ?_⟩
  have hpos : 0 < ‖DirichletCharacter.LFunction χ 1‖ :=
    norm_pos_iff.2 (Eis.RealChar.LFunction_ne_zero_of_isQuadratic hq (by norm_num) (Or.inl hχ))
  have hℓ : 0 < Real.log (Real.log (N + 16)) := by linarith [one_lt_loglog N]
  have h1 := (abs_le.1 (hC N χ hq hχ)).1
  calc Real.exp (-C) / Real.log (Real.log (N + 16))
      = Real.exp (-(Real.log (Real.log (Real.log (N + 16))) + C)) := by
        rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hℓ]
        field_simp
    _ ≤ Real.exp (Real.log ‖DirichletCharacter.LFunction χ 1‖) := Real.exp_le_exp.2 h1
    _ = ‖DirichletCharacter.LFunction χ 1‖ := Real.exp_log hpos

end Littlewood
