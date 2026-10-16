import ChiUniform
import DHHadamard
import DirichletCharHalfPlane

/-! # Stack review 3, door D1 (STRUCTURAL-REVIEW.md §9.2): `ψ(x, χ)` uniformly in the modulus, every `χ ≠ 1`

Not compiled by any build script. Compile it as `DoorAP.lean` (10 s at round 508's head; the printed axiom list is
`[propext, Classical.choice, Quot.sound]`). The body of `ChiUniform.psiChi_le_uniform_of` is copied with two
substitutions: `Eis.LFunction_ne_zero_of_re_gt` for `Eis.RealChar.LFunction_ne_zero_of_isQuadratic`, and
`PsiOmega.norm_LFunction_leC` for `PsiOmega.norm_LFunction_le`.
-/

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

namespace ChiUniformAll

open SmoothPerron HalfPlanePNT ChiPNT ChiUniform

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
    refine (norm_LSeries_le hμ t).trans (tsum_norm_term_le (fun n ↦ ?_) summable_one_32)
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


/-- **`ψ(x, χ)` uniformly in the modulus, for every Dirichlet character `χ ≠ 1`.** -/
theorem psiChi_le_uniform {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ x : ℝ, 1 < x → ‖psiChi χ x‖ ≤ C * Real.log (N + 2) * x ^ (11 / 12 + η) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := sum_le_uniform (θ := 11 / 12) (by norm_num) (by norm_num) hη
  have hA₀ : 0 ≤ zeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hΛ₀ : 0 ≤ logDerivZeta32 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hc' : 0 ≤ Real.log (2 + 36 * zeta32 / 11) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 36 * zeta32 / 11 by positivity])
  exact ⟨_, by positivity, psiChi_le_uniform_of hC₁ hC₂ hb⟩

end ChiUniformAll

#print axioms ChiUniformAll.psiChi_le_uniform
