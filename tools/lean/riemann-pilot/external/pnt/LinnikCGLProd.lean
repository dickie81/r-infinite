/-
# Round 651: a product of three `ĥ`s as an integral over `(v₁, v₂)` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li's proof of Proposition 7.1 opens: "Expanding the definition of ĥ as an integral and interchanging the
order of summation and integration, one finds" `I′_{m⃗}` as an integral over `(u₁, u₂, u₃)`. Then, since "a key
observation is that the arguments of the R functions above are restricted to a two-dimensional subvariety defined by
z₁z₂z₃ = 1", "we make the change of variables v₁ = u₁/u₃, v₂ = u₂/u₃, b₁ = a₁a₃⁻¹, b₂ = a₂a₃⁻¹", with
"du₁du₂du₃ = u₃²dv₁dv₂du₃" (text layer lines 2067–2068 and 2125–2163; spaces restored, the hat, fractions, exponents
and subscripts transcribed). Their (7.3) integrates over `u₃` first, against `w(v₁u₃)²w(v₂u₃)²w(u₃)²u₃²`. This file
proves the analytic part of that computation for one triple of points: a product of three `ĥ`s whose `τ`s sum to `0`
is an integral over `(v₁, v₂)` of `v₁^{iτ₁}v₂^{iτ₂}` times the inner integral of their (7.3).

Plain statement (`hhat_prod`). For `τ₁ + τ₂ + τ₃ = 0` and real `ξ₁, ξ₂, ξ₃`,
`ĥ_{τ₁}(ξ₁)ĥ_{τ₂}(ξ₂)ĥ_{τ₃}(ξ₃) = ∫∫v₁^{iτ₁}v₂^{iτ₂}J(v₁, v₂, v₁ξ₁ + v₂ξ₂ + ξ₃) dv₂ dv₁`, with
`J(v₁, v₂, λ) = ∫e^{−2πiλu}u²w(v₁u)²w(v₂u)²w(u)² du` and `h_τ(u) = w(u)²u^{iτ}`.

The proof. With `f_ℓ(u) = e^{−2πiuξ_ℓ}h_{τ_ℓ}(u)`, `ĥ₁ĥ₂ĥ₃ = ∫f₃(u₃)(∫f₁)(∫f₂) du₃`. For `u₃ > 0` the substitutions
`u₁ = v₁u₃`, `u₂ = v₂u₃` give `(∫f₁)(∫f₂) = u₃²∫∫f₁(v₁u₃)f₂(v₂u₃)`; for `u₃ ≤ 0`, `f₃(u₃) = 0`. The integrand
`Φ(u₃, v₁, v₂) = u₃²f₁(v₁u₃)f₂(v₂u₃)f₃(u₃)` is continuous and vanishes outside `[1, 2] × [1/2, 2] × [1/2, 2]`, so
Fubini puts the integral over `u₃` inside. Where `Φ ≠ 0`, `u₃, v₁, v₂ > 0` and
`(v₁u₃)^{iτ₁}(v₂u₃)^{iτ₂}u₃^{iτ₃} = v₁^{iτ₁}v₂^{iτ₂}`, since `τ₁ + τ₂ + τ₃ = 0`.

* `ee`, `ee_add`, `continuous_ee`, `norm_ee`, `fourier_eq`, `Wt_apply`, `one_lt_of_wCGL_ne`, `gv`, `Jk`: the phase
  `e^{−2πix}`, Mathlib's Fourier transform as `∫e^{−2πiuξ}f(u) du`, and the kernel.
* `Phi`, `integral_scale`, `prod_eq_iter`: the substitution (Mathlib's `Measure.integral_comp_mul_right`).
* `Phi_ne_zero`, `continuous_Phi3`, `integrable_Phi3`, `integrable_Phi2`, `iter_swap`: Fubini (Mathlib's
  `integral_integral_swap` and `Integrable.integral_prod_left`).
* `Phi_eq`, `hhat_prod`: the phases, and the formula.

The file imports `LinnikCGLTrunc.lean`.
-/

import LinnikCGLTrunc

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLProd

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson

/-! ### The phase, the weight and the kernel -/

/-- `e(−x) = e^{−2πix}`, the phase of Mathlib's Fourier transform on `ℝ`. -/
def ee (x : ℝ) : ℂ := Complex.exp (((-2 * π * x : ℝ) : ℂ) * I)

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee; exact Complex.norm_exp_ofReal_mul_I _

lemma fourier_eq (f : ℝ → ℂ) (ξ : ℝ) : 𝓕 f ξ = ∫ u : ℝ, ee (u * ξ) * f u := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [ee, smul_eq_mul]
  congr 1; congr 1; push_cast; ring

lemma Wt_apply (τ u : ℝ) : Wt τ u = (u : ℂ) ^ ((τ : ℂ) * I) * ((wCGL u ^ 2 : ℝ) : ℂ) := by
  unfold Wt Wc wsq; rw [smul_eq_mul]

lemma one_lt_of_wCGL_ne {x : ℝ} (hx : wCGL x ≠ 0) : 1 < x ∧ x < 2 := by
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  exact hx (wCGL_zero hc)

/-- The weight of their (7.3): `g_v(u) = u²w(v₁u)²w(v₂u)²w(u)²`. -/
def gv (v₁ v₂ u : ℝ) : ℝ := u ^ 2 * wCGL (v₁ * u) ^ 2 * wCGL (v₂ * u) ^ 2 * wCGL u ^ 2

/-- **The kernel of their (7.3)**: `J(v₁, v₂, λ) = ∫e(−λu)g_v(u) du`. -/
def Jk (v₁ v₂ lam : ℝ) : ℂ := ∫ u : ℝ, ee (u * lam) * (gv v₁ v₂ u : ℂ)

/-! ### The substitution `u₁ = v₁u₃`, `u₂ = v₂u₃` -/

/-- The integrand after the substitution: `Φ(u₃, v₁, v₂) = u₃²f₁(v₁u₃)f₂(v₂u₃)f₃(u₃)` with `f_ℓ(u) = e(−uξ_ℓ)h_{τ_ℓ}(u)`
and `h_τ(u) = w(u)²u^{iτ}`. -/
def Phi (τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ : ℝ) : ℂ :=
  ((u₃ ^ 2 : ℝ) : ℂ) * (ee (v₁ * u₃ * ξ₁) * Wt τ₁ (v₁ * u₃) * (ee (v₂ * u₃ * ξ₂) * Wt τ₂ (v₂ * u₃)) *
    (ee (u₃ * ξ₃) * Wt τ₃ u₃))

lemma integral_scale (g : ℝ → ℂ) {c : ℝ} (hc : 0 < c) : ∫ y, g y = (c : ℂ) * ∫ x, g (x * c) := by
  rw [Measure.integral_comp_mul_right g c, abs_of_pos (inv_pos.2 hc), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne', Complex.ofReal_one, one_mul]

/-- **The substitution**: `ĥ_{τ₁}(ξ₁)ĥ_{τ₂}(ξ₂)ĥ_{τ₃}(ξ₃) = ∫∫∫Φ(u₃, v₁, v₂) dv₂ dv₁ du₃`. -/
lemma prod_eq_iter (τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ : ℝ) :
    𝓕 (Wt τ₁) ξ₁ * 𝓕 (Wt τ₂) ξ₂ * 𝓕 (Wt τ₃) ξ₃ =
      ∫ u₃ : ℝ, ∫ v₁ : ℝ, ∫ v₂ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ := by
  rw [fourier_eq (Wt τ₃), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u₃ => ?_)
  dsimp only
  by_cases hu : 0 < u₃
  · have hs1 : ∫ u : ℝ, ee (u * ξ₁) * Wt τ₁ u = (u₃ : ℂ) * ∫ x : ℝ, ee (x * u₃ * ξ₁) * Wt τ₁ (x * u₃) :=
      integral_scale (fun u => ee (u * ξ₁) * Wt τ₁ u) hu
    have hs2 : ∫ u : ℝ, ee (u * ξ₂) * Wt τ₂ u = (u₃ : ℂ) * ∫ x : ℝ, ee (x * u₃ * ξ₂) * Wt τ₂ (x * u₃) :=
      integral_scale (fun u => ee (u * ξ₂) * Wt τ₂ u) hu
    rw [fourier_eq, fourier_eq, hs1, hs2]
    have e1 : ∀ v₁ v₂ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ =
        (((u₃ ^ 2 : ℝ) : ℂ) * (ee (u₃ * ξ₃) * Wt τ₃ u₃) * (ee (v₁ * u₃ * ξ₁) * Wt τ₁ (v₁ * u₃))) *
          (ee (v₂ * u₃ * ξ₂) * Wt τ₂ (v₂ * u₃)) := by
      intro v₁ v₂; unfold Phi; ring
    have hinner : ∀ v₁ : ℝ, ∫ v₂ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ =
        (((u₃ ^ 2 : ℝ) : ℂ) * (ee (u₃ * ξ₃) * Wt τ₃ u₃) * (ee (v₁ * u₃ * ξ₁) * Wt τ₁ (v₁ * u₃))) *
          ∫ x : ℝ, ee (x * u₃ * ξ₂) * Wt τ₂ (x * u₃) := by
      intro v₁
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun v₂ => e1 v₁ v₂)
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const, integral_const_mul]
    push_cast
    ring
  · have h3 : Wt τ₃ u₃ = 0 := Wt_vanish τ₃ u₃ fun h => hu (by linarith [h.1])
    simp [Phi, h3]

/-! ### Fubini -/

lemma Phi_ne_zero {τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ : ℝ} (h : Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ ≠ 0) :
    u₃ ∈ Icc (1 : ℝ) 2 ∧ v₁ ∈ Icc (1 / 2 : ℝ) 2 ∧ v₂ ∈ Icc (1 / 2 : ℝ) 2 := by
  have hw : ∀ (τ x : ℝ), Wt τ x ≠ 0 → x ∈ Icc (1 : ℝ) 2 := fun τ x hx => by
    by_contra hc; exact hx (Wt_vanish τ x hc)
  have h3 : Wt τ₃ u₃ ≠ 0 := fun h0 => h (by simp [Phi, h0])
  have h1 : Wt τ₁ (v₁ * u₃) ≠ 0 := fun h0 => h (by simp [Phi, h0])
  have h2 : Wt τ₂ (v₂ * u₃) ≠ 0 := fun h0 => h (by simp [Phi, h0])
  obtain ⟨hu1, hu2⟩ := hw _ _ h3
  obtain ⟨ha1, ha2⟩ := hw _ _ h1
  obtain ⟨hb1, hb2⟩ := hw _ _ h2
  have hv₁ : 0 < v₁ := by
    by_contra hc; rw [not_lt] at hc; nlinarith
  have hv₂ : 0 < v₂ := by
    by_contra hc; rw [not_lt] at hc; nlinarith
  refine ⟨⟨hu1, hu2⟩, ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

lemma continuous_Phi3 (τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ : ℝ) :
    Continuous fun p : (ℝ × ℝ) × ℝ => Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ p.1.1 p.1.2 p.2 := by
  unfold Phi
  have h1 := continuous_Wt τ₁
  have h2 := continuous_Wt τ₂
  have h3 := continuous_Wt τ₃
  have he := continuous_ee
  fun_prop

lemma integrable_Phi3 (τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ : ℝ) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ p.1.1 p.1.2 p.2)
      ((volume.prod volume).prod volume) := by
  refine (continuous_Phi3 τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (((isCompact_Icc (a := (1 : ℝ)) (b := 2)).prod
    (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2))).prod (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2))) fun p hp => ?_
  by_contra h
  obtain ⟨hu, hv₁, hv₂⟩ := Phi_ne_zero h
  exact hp ⟨⟨hu, hv₁⟩, hv₂⟩

lemma integrable_Phi2 (τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ v₁ : ℝ) :
    Integrable (fun p : ℝ × ℝ => Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ p.1 v₁ p.2) (volume.prod volume) := by
  have hc : Continuous fun p : ℝ × ℝ => Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ p.1 v₁ p.2 :=
    (continuous_Phi3 τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃).comp (by fun_prop : Continuous fun p : ℝ × ℝ => ((p.1, v₁), p.2))
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro ((isCompact_Icc (a := (1 : ℝ)) (b := 2)).prod
    (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2))) fun p hp => ?_
  by_contra h
  obtain ⟨hu, -, hv₂⟩ := Phi_ne_zero h
  exact hp ⟨hu, hv₂⟩

/-- **Fubini**: `∫∫∫Φ dv₂ dv₁ du₃ = ∫∫∫Φ du₃ dv₂ dv₁`. -/
lemma iter_swap (τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ : ℝ) :
    ∫ u₃ : ℝ, ∫ v₁ : ℝ, ∫ v₂ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ =
      ∫ v₁ : ℝ, ∫ v₂ : ℝ, ∫ u₃ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ := by
  have h1 : Integrable (Function.uncurry fun u₃ v₁ => ∫ v₂ : ℝ, Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂)
      (volume.prod volume) :=
    (integrable_Phi3 τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃).integral_prod_left
  rw [integral_integral_swap h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v₁ => ?_)
  exact integral_integral_swap (integrable_Phi2 τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ v₁)

/-! ### The phases -/

/-- **The phases** for `τ₁ + τ₂ + τ₃ = 0`: `Φ(u₃, v₁, v₂) = v₁^{iτ₁}v₂^{iτ₂}e(−u₃(v₁ξ₁ + v₂ξ₂ + ξ₃))g_v(u₃)`. -/
lemma Phi_eq {τ₁ τ₂ τ₃ : ℝ} (hτ : τ₁ + τ₂ + τ₃ = 0) (ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ : ℝ) :
    Phi τ₁ τ₂ τ₃ ξ₁ ξ₂ ξ₃ u₃ v₁ v₂ = (v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) *
      (ee (u₃ * (v₁ * ξ₁ + v₂ * ξ₂ + ξ₃)) * (gv v₁ v₂ u₃ : ℂ)) := by
  by_cases h : wCGL (v₁ * u₃) = 0 ∨ wCGL (v₂ * u₃) = 0 ∨ wCGL u₃ = 0
  · rcases h with h | h | h <;> simp [Phi, gv, Wt_apply, h]
  rw [not_or, not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hu1, -⟩ := one_lt_of_wCGL_ne h3
  obtain ⟨ha1, -⟩ := one_lt_of_wCGL_ne h1
  obtain ⟨hb1, -⟩ := one_lt_of_wCGL_ne h2
  have hu : 0 < u₃ := by linarith
  have hv₁ : 0 < v₁ := by by_contra hc; rw [not_lt] at hc; nlinarith
  have hv₂ : 0 < v₂ := by by_contra hc; rw [not_lt] at hc; nlinarith
  have hu0 : (u₃ : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hc1 : ((v₁ * u₃ : ℝ) : ℂ) ^ ((τ₁ : ℂ) * I) = (v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (u₃ : ℂ) ^ ((τ₁ : ℂ) * I) := by
    rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg hv₁.le hu.le _
  have hc2 : ((v₂ * u₃ : ℝ) : ℂ) ^ ((τ₂ : ℂ) * I) = (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) * (u₃ : ℂ) ^ ((τ₂ : ℂ) * I) := by
    rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg hv₂.le hu.le _
  have hph : (u₃ : ℂ) ^ ((τ₁ : ℂ) * I) * (u₃ : ℂ) ^ ((τ₂ : ℂ) * I) * (u₃ : ℂ) ^ ((τ₃ : ℂ) * I) = 1 := by
    rw [← Complex.cpow_add _ _ hu0, ← Complex.cpow_add _ _ hu0,
      show (τ₁ : ℂ) * I + (τ₂ : ℂ) * I + (τ₃ : ℂ) * I = ((τ₁ + τ₂ + τ₃ : ℝ) : ℂ) * I by push_cast; ring, hτ]
    simp
  have hee : ee (v₁ * u₃ * ξ₁) * ee (v₂ * u₃ * ξ₂) * ee (u₃ * ξ₃) = ee (u₃ * (v₁ * ξ₁ + v₂ * ξ₂ + ξ₃)) := by
    rw [← ee_add, ← ee_add]; congr 1; ring
  unfold Phi gv
  rw [Wt_apply, Wt_apply, Wt_apply, hc1, hc2]
  push_cast
  linear_combination ((v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) * (u₃ : ℂ) ^ 2 *
      (wCGL (v₁ * u₃) : ℂ) ^ 2 * (wCGL (v₂ * u₃) : ℂ) ^ 2 * (wCGL u₃ : ℂ) ^ 2 *
      (ee (v₁ * u₃ * ξ₁) * ee (v₂ * u₃ * ξ₂) * ee (u₃ * ξ₃))) * hph +
    ((v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) * (u₃ : ℂ) ^ 2 *
      (wCGL (v₁ * u₃) : ℂ) ^ 2 * (wCGL (v₂ * u₃) : ℂ) ^ 2 * (wCGL u₃ : ℂ) ^ 2) * hee

/-- **A product of three `ĥ`s** (the change of variables of their proof of Proposition 7.1): for
`τ₁ + τ₂ + τ₃ = 0`, `ĥ_{τ₁}(ξ₁)ĥ_{τ₂}(ξ₂)ĥ_{τ₃}(ξ₃) = ∫∫v₁^{iτ₁}v₂^{iτ₂}J(v₁, v₂, v₁ξ₁ + v₂ξ₂ + ξ₃) dv₂ dv₁`. -/
theorem hhat_prod {τ₁ τ₂ τ₃ : ℝ} (hτ : τ₁ + τ₂ + τ₃ = 0) (ξ₁ ξ₂ ξ₃ : ℝ) :
    𝓕 (Wt τ₁) ξ₁ * 𝓕 (Wt τ₂) ξ₂ * 𝓕 (Wt τ₃) ξ₃ =
      ∫ v₁ : ℝ, ∫ v₂ : ℝ, (v₁ : ℂ) ^ ((τ₁ : ℂ) * I) * (v₂ : ℂ) ^ ((τ₂ : ℂ) * I) *
        Jk v₁ v₂ (v₁ * ξ₁ + v₂ * ξ₂ + ξ₃) := by
  rw [prod_eq_iter, iter_swap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v₁ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun v₂ => ?_)
  simp only [Phi_eq hτ]
  rw [integral_const_mul]
  rfl

end LinnikCGLProd

#print axioms LinnikCGLProd.prod_eq_iter
#print axioms LinnikCGLProd.iter_swap
#print axioms LinnikCGLProd.Phi_eq
#print axioms LinnikCGLProd.hhat_prod
