/-
# Round 480: bounds for the real Dirichlet L-functions, uniform in the modulus

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `η > 0` there is `C` with `|ψ(x, χ)| ≤ C log(N + 2)·x^{11/12+η}` for every quadratic
Dirichlet character `χ ≠ 1` mod `N` and every `x > 1` (`psiChi_le_uniform`). No hypothesis. *(Round 509: for every
Dirichlet character `χ ≠ 1` mod `N`, with round 254's `PsiOmega.norm_LFunction_leC` and round 495's half-plane
`Eis.LFunction_ne_zero_of_re_gt`; the same for `psiChi_le_uniform_of`.)*

* `psiChi_le_uniform`: `ChiPNT.sum_le_uniform` at `F = L(·, χ)`, with `c = 18(N + 1)/11` from round 224's
  `PsiOmega.norm_LFunction_le`, `A = ζ(3/2)` (`zeta32`) and `C₀ = −ζ′/ζ(3/2)` (`logDerivZeta32`), and round 477's
  half-plane `Re s > 11/12`. *(Round 509: round 254's `PsiOmega.norm_LFunction_leC` and round 495's half-plane, for
  every `χ ≠ 1`.)* *(Round 511: `norm_LFunction_le` is removed; `norm_LFunction_leC` replaces it.)*
* `psiChi_le_uniform_of` (round 484): `psiChi_le_uniform` from given constants `C₁`, `C₂` of `sum_le_uniform`.

History. Round 480 also proved here round 478's two bounds for an entire `F` with their constants kept:
`logDeriv_le_uniform` (`|F′/F(σ + it)| ≤ K(log(2 + 2cA) + log(|t| + 4)) + C₀` for `σ ≥ θ'`) and `sum_le_uniform`
(`|Σ_{n ≤ X} f(n)| ≤ (C₁(log(2 + 2cA) + C₀) + C₂)X^{θ+η}` for `X > 1`); round 484 added their constants as
formulas (`Kld`, `logDeriv_le_uniform_of`, `eta0`, `sum_le_uniform_of`, `integral_one_add_abs_rpow`). Round 513
(STRUCTURAL-REVIEW §9.3, U3) moved `Kld` and the two log-derivative bounds to `LogDerivDisc.lean` and the rest to
`ChiPNT.lean`, where round 478's bounds without constants are now their corollaries; their namespaces are
`LogDerivDisc` and `ChiPNT`.
-/
import ChiPNT

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

namespace ChiUniform

open SmoothPerron LogDerivDisc ChiPNT

/-! ### Real characters, uniformly in the modulus -/

/-- `ζ(3/2) = Σ_{n≥1} n^{−3/2}`, as the sum of the norms of the terms. -/
noncomputable def zeta32 : ℝ := ∑' n : ℕ, ‖LSeries.term (fun _ ↦ (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖

/-- `−ζ′/ζ(3/2) = Σ Λ(n)n^{−3/2}`, as the sum of the norms of the terms. -/
noncomputable def logDerivZeta32 : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖

/-- Termwise comparison of `Σ |f(n)|n^{−σ}`. -/
lemma tsum_norm_term_le {f g : ℕ → ℂ} (hfg : ∀ n, ‖f n‖ ≤ ‖g n‖) {σ : ℝ}
    (hg : LSeriesSummable g σ) :
    ∑' n, ‖LSeries.term f σ n‖ ≤ ∑' n, ‖LSeries.term g σ n‖ := by
  have hle : ∀ n, ‖LSeries.term f σ n‖ ≤ ‖LSeries.term g σ n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · exact le_rfl
    · gcongr
      exact hfg n
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hg.norm) hg.norm

lemma summable_one_32 : LSeriesSummable (fun _ ↦ (1 : ℂ)) ((3 / 2 : ℝ) : ℂ) := by
  have := (LSeriesSummable_one_iff (s := ((3 / 2 : ℝ) : ℂ))).2 (by norm_num)
  exact this

/-- **`ψ(x, χ)` uniformly in the modulus, from the constants of `sum_le_uniform`.** If `C₁, C₂ ≥ 0` satisfy
the conclusion of `sum_le_uniform` at `θ = 11/12`, then
`|ψ(x, χ)| ≤ (C₁(1 + log(2 + 36ζ(3/2)/11) − ζ′/ζ(3/2)) + C₂) log(N + 2)·x^{11/12+η}` for every
Dirichlet character `χ ≠ 1` mod `N` and every `x > 1`. -/
theorem psiChi_le_uniform_of {η C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hb : ∀ {F : ℂ → ℂ}, Differentiable ℂ F → (∀ s : ℂ, 11 / 12 < s.re → F s ≠ 0) →
      ∀ {c A C₀ : ℝ}, 0 ≤ c → 0 ≤ A →
      (∀ s : ℂ, 11 / 12 ≤ s.re → s.re ≤ 3 → ‖F s‖ ≤ c * (|s.im| + 2)) →
      (∀ t : ℝ, ‖F (ctr t)‖⁻¹ ≤ A) →
      (∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv F s / F s‖ ≤ C₀) →
      ∀ {f : ℕ → ℂ}, f 0 = 0 → (∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n) →
      (∀ s : ℂ, 1 < s.re → LSeries f s = -(deriv F s / F s)) →
      ∀ X : ℝ, 1 < X → ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ ≤
        (C₁ * (Real.log (2 + 2 * c * A) + C₀) + C₂) * X ^ (11 / 12 + η)) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ x : ℝ, 1 < x → ‖psiChi χ x‖ ≤
        (C₁ * (1 + Real.log (2 + 36 * zeta32 / 11) + logDerivZeta32) + C₂) * Real.log (N + 2) *
          x ^ (11 / 12 + η) := by
  have hA₀ : 0 ≤ zeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hΛ₀ : 0 ≤ logDerivZeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  set c' : ℝ := Real.log (2 + 36 * zeta32 / 11) with hc'def
  have hc' : 0 ≤ c' := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 36 * zeta32 / 11 by positivity])
  intro N _ χ hχ x hx
  have hF := DirichletCharacter.differentiable_LFunction hχ
  have hzf : ∀ s : ℂ, 11 / 12 < s.re → DirichletCharacter.LFunction χ s ≠ 0 :=
    fun _ hs ↦ Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)
  set c : ℝ := 18 * (N + 1) / 11 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hgrowth : ∀ s : ℂ, 11 / 12 ≤ s.re → s.re ≤ 3 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ c * (|s.im| + 2) := by
    intro s hs1 hs3
    have hre : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ 3 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 3 + |s.im| := by rw [abs_of_pos hre]; linarith
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ (N + 1) * ‖s‖ / s.re :=
          PsiOmega.norm_LFunction_leC hχ hre
      _ ≤ (N + 1) * (3 + |s.im|) / (11 / 12) := by
          gcongr
      _ ≤ c * (|s.im| + 2) := by
          rw [hcdef]
          have : 0 ≤ (N : ℝ) + 1 := by positivity
          have : 0 ≤ |s.im| := abs_nonneg _
          rw [div_le_iff₀ (by norm_num)]
          have := mul_nonneg (by positivity : (0 : ℝ) ≤ N + 1) (abs_nonneg s.im)
          linarith
  have hlow : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ctr t)‖⁻¹ ≤ zeta32 := by
    intro t
    have hs : 1 < (ctr t).re := by rw [ctr_re]; norm_num
    have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hm]
    have hμ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) ((3 / 2 : ℝ) : ℂ) :=
      DirichletCharacter.LSeriesSummable_mul χ
        (ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by norm_num))
    refine (norm_LSeries_le_of_le_re hμ (s := ctr t) (by rw [ctr_re])).trans
      (tsum_norm_term_le (fun n ↦ ?_) summable_one_32)
    rw [norm_mul, norm_one]
    refine (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans ?_
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s‖ ≤ logDerivZeta32 := by
    intro s hs
    rw [← norm_neg, ← LSeries_twist_vonMangoldt_eq_LFunction χ (by linarith)]
    have hΛ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((3 / 2 : ℝ) : ℂ) :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num)
    refine (norm_LSeries_le_of_le_re hΛ hs).trans (tsum_norm_term_le (fun n ↦ ?_)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)))
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hfΛ : ∀ n : ℕ,
      ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one _ _)
  have hmain := hb hF hzf hc0 hA₀ hgrowth hlow hright (by simp) hfΛ
    (fun s hs ↦ LSeries_twist_vonMangoldt_eq_LFunction χ hs) x hx
  -- the constant
  have hN2 : (3 : ℝ) ≤ N + 2 := by
    have := NeZero.ne N
    have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    linarith
  have hlogN : 1 ≤ Real.log (N + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL : Real.log (2 + 2 * c * zeta32) ≤ Real.log (N + 2) + c' := by
    rw [hc'def, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [hcdef]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hxp : 0 ≤ x ^ (11 / 12 + η) := Real.rpow_nonneg (by linarith) _
  calc ‖psiChi χ x‖ ≤ (C₁ * (Real.log (2 + 2 * c * zeta32) + logDerivZeta32) + C₂) *
        x ^ (11 / 12 + η) := hmain
    _ ≤ (C₁ * (Real.log (N + 2) + c' + logDerivZeta32) + C₂) * x ^ (11 / 12 + η) := by
        gcongr
    _ ≤ ((C₁ * (1 + c' + logDerivZeta32) + C₂) * Real.log (N + 2)) * x ^ (11 / 12 + η) := by
        apply mul_le_mul_of_nonneg_right _ hxp
        have h1 : C₁ * c' ≤ C₁ * c' * Real.log (N + 2) := le_mul_of_one_le_right (by positivity) hlogN
        have h2 : C₁ * logDerivZeta32 ≤ C₁ * logDerivZeta32 * Real.log (N + 2) :=
          le_mul_of_one_le_right (by positivity) hlogN
        have h3 : C₂ ≤ C₂ * Real.log (N + 2) := le_mul_of_one_le_right hC₂ hlogN
        linarith
    _ = (C₁ * (1 + c' + logDerivZeta32) + C₂) * Real.log (N + 2) * x ^ (11 / 12 + η) := by ring

/-- **`ψ(x, χ)` uniformly in the modulus.** For every `η > 0` there is `C` with
`|ψ(x, χ)| ≤ C log(N + 2)·x^{11/12+η}` for every Dirichlet character `χ ≠ 1` mod `N` and
every `x > 1`. -/
theorem psiChi_le_uniform {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ x : ℝ, 1 < x → ‖psiChi χ x‖ ≤ C * Real.log (N + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := sum_le_uniform (θ := 11 / 12) (by norm_num) (by norm_num) hη
  have hA₀ : 0 ≤ zeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hΛ₀ : 0 ≤ logDerivZeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hc' : 0 ≤ Real.log (2 + 36 * zeta32 / 11) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 36 * zeta32 / 11 by positivity])
  exact ⟨_, by positivity, psiChi_le_uniform_of hC₁ hC₂ hb⟩

end ChiUniform
