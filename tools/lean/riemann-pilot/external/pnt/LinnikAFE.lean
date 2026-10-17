/-
# Round 524, part 1: the approximate functional equation for `L(s, χ)²`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For a primitive character `χ ≠ 1` modulo `N` and `0 ≤ Re s ≤ 1`,
`Λ(s, χ)² = J(s, χ) + ε(χ)²N^{1−2s}J(1 − s, χ⁻¹)` with `J(s, χ) = (1/2πi)∫_{(2)} Λ(s + w, χ)²N^w e^{w²} dw/w` (`afe`).
For every character `χ`, every `c ≥ 0` and real `t`, `v`, the Archimedean factor `γ_χ` (Mathlib's `gammaFactor`)
satisfies `|γ_χ(½ + it + c + iv)| ≤ e^{KR(c)}(1 + |t|)^{c/2}(1 + |v|)^{c/2+1/4}e^{π|v|/4}|γ_χ(½ + it)|`
(`norm_gammaFactor_ratio_le`). Both are inputs of the fourth moment in `LinnikFourth.lean`.

* `log_norm_Gamma_seg`, `log_norm_Gamma_le`, `log_norm_Gamma_ge`: `log|Γ(x + it)|` against `log|Γ(½ + it)|`, by the
  mean value theorem along the horizontal segment, with `log|z| − 4 ≤ Re ψ(z) ≤ log|z| + 4` on `Re z ≥ ¼`
  (`digamma_re_ge` here, and round 164's `Kaiser.digamma_re_le`).
* `log_norm_Gamma_half_sub`: two ordinates on `Re z = ½`, from `|Γ(½ + it)|² = π/cosh(πt)`.
* `log_norm_Gamma_ratio`, `norm_Gamma_ratio_le`, `norm_gammaFactor_ratio_le`: the ratio bound, for even and odd `χ`.
* `verticalIntegral_sub_eq`: moving a vertical integral across a simple pole at `0` costs `2πi` times the residue
  (PNT+'s `ResidueTheoremOnRectangleWithSimplePole'` on the rectangles, and round 472's limits).
* `norm_completed_le`: `|Λ(z, χ)| ≤ 16(N + 1)N^{5/2}(3 + |Im z|)` on `−2 ≤ Re z ≤ 3` for primitive `χ ≠ 1` (round
  254's `PsiOmega.norm_LFunction_leC` right of `Re z = ½`, Mathlib's functional equation and `|ε(χ)| = 1` left of it).
* `afe`: `verticalIntegral_sub_eq` for `w ↦ Λ(s + w, χ)²N^w e^{w²}/w` between `Re w = 2` and `Re w = −2`, where Mathlib's
  functional equation turns the left integral into `ε(χ)²N^{1−2s}J(1 − s, χ⁻¹)`.
-/
import LinnikSubconvex

open Complex Real Set MeasureTheory

noncomputable section

namespace LinnikGamma

/-- `Re ψ(z) ≥ log|z| − 4` for `Re z ≥ 1/4` (the lower half of `Kaiser.digamma_re_le`, from Binet's formula). -/
theorem digamma_re_ge {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    Real.log ‖z‖ - 4 ≤ (Complex.digamma z).re := by
  have hz0 : 0 < z.re := by linarith
  rw [PilotDigamma.digamma_eq_lap hz0, sub_re, sub_re, Complex.log_re]
  have hinv : ‖1 / (2 * z)‖ ≤ 2 := by
    have hnz : 1 / 4 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, div_le_iff₀ (by positivity)]; linarith
  have hlap : ‖PilotDigamma.lap z‖ ≤ 2 := by
    refine (PilotDigamma.norm_lap_le hz0).trans ?_
    rw [div_le_iff₀ (by positivity)]; linarith
  have a1 := le_of_abs_le ((Complex.abs_re_le_norm _).trans hinv)
  have a2 := le_of_abs_le ((Complex.abs_re_le_norm _).trans hlap)
  linarith

lemma norm_add_mul_I_pos {x : ℝ} (hx : 0 < x) (t : ℝ) : 0 < ‖(x : ℂ) + t * I‖ := by
  rw [norm_pos_iff]
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma norm_add_mul_I_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (t : ℝ) :
    ‖(x : ℂ) + t * I‖ ≤ ‖(y : ℂ) + t * I‖ := by
  rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I]
  apply Real.sqrt_le_sqrt
  nlinarith

/-- **`log|Γ|` along a horizontal segment, both ways**: for `1/4 ≤ a ≤ b`,
`(b − a)(log|a + it| − 4) ≤ log|Γ(b + it)| − log|Γ(a + it)| ≤ (b − a)(log|b + it| + 4)`, by the mean value theorem
for `x ↦ log|Γ(x + it)|`, whose derivative `Re ψ(x + it)` lies between `log|x + it| ∓ 4`. -/
theorem log_norm_Gamma_seg {a b : ℝ} (ha : 1 / 4 ≤ a) (hab : a ≤ b) (t : ℝ) :
    (b - a) * (Real.log ‖(a : ℂ) + t * I‖ - 4) ≤
        Real.log ‖Complex.Gamma (b + t * I)‖ - Real.log ‖Complex.Gamma (a + t * I)‖ ∧
      Real.log ‖Complex.Gamma (b + t * I)‖ - Real.log ‖Complex.Gamma (a + t * I)‖ ≤
        (b - a) * (Real.log ‖(b : ℂ) + t * I‖ + 4) := by
  set g : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma (x + t * I)‖ with hg
  have hne : ∀ x : ℝ, 0 < x → Complex.Gamma (x + t * I) ≠ 0 := fun x hx =>
    Complex.Gamma_ne_zero_of_re_pos (by simpa using hx)
  have hpole : ∀ x : ℝ, 0 < x → ∀ m : ℕ, (x : ℂ) + t * I ≠ -m := by
    intro x hx m h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt g (Complex.digamma (x + t * I)).re x := by
    intro x hx
    have hd : HasDerivAt (fun z : ℂ => Complex.Gamma (z + t * I)) (deriv Complex.Gamma (x + t * I)) x :=
      ((Complex.differentiableAt_Gamma _ (hpole x hx)).hasDerivAt).comp_add_const _ _
    have := HalfPlaneLindelof.hasDerivAt_log_norm hd.comp_ofReal (hne x hx)
    convert this using 2
    rw [Complex.digamma_def, logDeriv_apply]
  have hpos : ∀ x ∈ Icc a b, 0 < x := fun x hx => by linarith [hx.1]
  have hcont : ContinuousOn g (Icc a b) := fun x hx =>
    (hderiv x (hpos x hx)).continuousAt.continuousWithinAt
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  have hdiff : DifferentiableOn ℝ g (interior (Icc a b)) := by
    rw [hint]
    exact fun x hx => (hderiv x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  have hre : ∀ x ∈ Ioo a b, 1 / 4 ≤ ((x : ℂ) + t * I).re := fun x hx => by simp; linarith [hx.1]
  have hup : ∀ x ∈ interior (Icc a b), deriv g x ≤ Real.log ‖(b : ℂ) + t * I‖ + 4 := by
    rw [hint]
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(hderiv x hx0).deriv]
    refine (Kaiser.digamma_re_le (hre x hx)).trans ?_
    have := Real.log_le_log (norm_add_mul_I_pos hx0 t) (norm_add_mul_I_mono hx0.le hx.2.le t)
    linarith
  have hlo : ∀ x ∈ interior (Icc a b), Real.log ‖(a : ℂ) + t * I‖ - 4 ≤ deriv g x := by
    rw [hint]
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(hderiv x hx0).deriv]
    refine le_trans ?_ (digamma_re_ge (hre x hx))
    have := Real.log_le_log (norm_add_mul_I_pos (by linarith) t) (norm_add_mul_I_mono (by linarith) hx.1.le t)
    linarith
  have h1 := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont hdiff hlo a (left_mem_Icc.2 hab) b
    (right_mem_Icc.2 hab) hab
  have h2 := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hcont hdiff hup a (left_mem_Icc.2 hab) b
    (right_mem_Icc.2 hab) hab
  simp only [hg] at h1 h2
  constructor
  · linarith
  · linarith

/-- `(1 + |t|)/5 ≤ |x + it|` for `x ≥ 1/4`. -/
lemma one_add_abs_le_norm {x : ℝ} (hx : 1 / 4 ≤ x) (t : ℝ) : (1 + |t|) / 5 ≤ ‖(x : ℂ) + t * I‖ := by
  have h1 : |t| ≤ ‖(x : ℂ) + t * I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + t * I); simpa using this
  have h2 : x ≤ ‖(x : ℂ) + t * I‖ := by
    have := Complex.re_le_norm ((x : ℂ) + t * I); simpa using this
  rcases le_total (1 / 4) |t| with h | h <;> linarith

/-- `|x + it| ≤ max(1, x)(1 + |t|)` for `x ≥ 0`. -/
lemma norm_le_max_mul {x : ℝ} (hx : 0 ≤ x) (t : ℝ) : ‖(x : ℂ) + t * I‖ ≤ max 1 x * (1 + |t|) := by
  have h := norm_add_le (x : ℂ) (t * I)
  have e1 : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx]
  have e2 : ‖(t : ℂ) * I‖ = |t| := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [e1, e2] at h
  have hm1 : 1 ≤ max 1 x := le_max_left _ _
  have hmx : x ≤ max 1 x := le_max_right _ _
  nlinarith [abs_nonneg t]

/-- **Upper bound for `log|Γ|`**: `log|Γ(x + it)| ≤ log|Γ(1/2 + it)| + (x − 1/2)log(1 + |t|) + |x − 1/2|·log(5e⁴max(1, x))`
for `x ≥ 1/4`. -/
theorem log_norm_Gamma_le {x : ℝ} (hx : 1 / 4 ≤ x) (t : ℝ) :
    Real.log ‖Complex.Gamma (x + t * I)‖ ≤ Real.log ‖Complex.Gamma (1 / 2 + t * I)‖ +
      (x - 1 / 2) * Real.log (1 + |t|) + |x - 1 / 2| * Real.log (5 * Real.exp 4 * max 1 x) := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have ht1 : 0 < 1 + |t| := by positivity
  have hl1 : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hM : 1 ≤ max 1 x := le_max_left _ _
  have hl5 : Real.log 5 + 4 ≤ Real.log (5 * Real.exp 4 * max 1 x) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hM]
  rcases le_total (1 / 2) x with h | h
  · have hs := (log_norm_Gamma_seg (a := 1 / 2) (b := x) (by norm_num) h t).2
    rw [hhalf] at hs
    have hn := norm_le_max_mul (by linarith : (0 : ℝ) ≤ x) t
    have hpos := norm_add_mul_I_pos (by linarith : (0 : ℝ) < x) t
    have hlog : Real.log ‖(x : ℂ) + t * I‖ ≤ Real.log (max 1 x) + Real.log (1 + |t|) := by
      rw [← Real.log_mul (by positivity) ht1.ne']
      exact Real.log_le_log hpos hn
    have habs : |x - 1 / 2| = x - 1 / 2 := abs_of_nonneg (by linarith)
    rw [habs]
    have hl5' : Real.log (max 1 x) + 4 ≤ Real.log (5 * Real.exp 4 * max 1 x) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_exp]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)]
    have hx0 : 0 ≤ x - 1 / 2 := by linarith
    nlinarith
  · have hs := (log_norm_Gamma_seg (a := x) (b := 1 / 2) hx h t).1
    rw [hhalf] at hs
    have hn := one_add_abs_le_norm hx t
    have hlog : Real.log (1 + |t|) - Real.log 5 ≤ Real.log ‖(x : ℂ) + t * I‖ := by
      rw [← Real.log_div ht1.ne' (by norm_num)]
      exact Real.log_le_log (by positivity) hn
    have habs : |x - 1 / 2| = 1 / 2 - x := by rw [abs_of_nonpos (by linarith)]; ring
    rw [habs]
    have hx0 : 0 ≤ 1 / 2 - x := by linarith
    nlinarith

/-- **Lower bound for `log|Γ|`**: `log|Γ(1/2 + it)| + (x − 1/2)log(1 + |t|) − |x − 1/2|·log(5e⁴) ≤ log|Γ(x + it)|`
for `x ≥ 1/4`. -/
theorem log_norm_Gamma_ge {x : ℝ} (hx : 1 / 4 ≤ x) (t : ℝ) :
    Real.log ‖Complex.Gamma (1 / 2 + t * I)‖ + (x - 1 / 2) * Real.log (1 + |t|) -
      |x - 1 / 2| * Real.log (5 * Real.exp 4) ≤ Real.log ‖Complex.Gamma (x + t * I)‖ := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have ht1 : 0 < 1 + |t| := by positivity
  have hl5 : Real.log (5 * Real.exp 4) = Real.log 5 + 4 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  have hl50 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  rcases le_total (1 / 2) x with h | h
  · have hs := (log_norm_Gamma_seg (a := 1 / 2) (b := x) (by norm_num) h t).1
    rw [hhalf] at hs
    have hn := one_add_abs_le_norm (x := 1 / 2) (by norm_num) t
    rw [hhalf] at hn
    have hlog : Real.log (1 + |t|) - Real.log 5 ≤ Real.log ‖(1 / 2 : ℂ) + t * I‖ := by
      rw [← Real.log_div ht1.ne' (by norm_num)]
      exact Real.log_le_log (by positivity) hn
    have habs : |x - 1 / 2| = x - 1 / 2 := abs_of_nonneg (by linarith)
    rw [habs, hl5]
    have hx0 : 0 ≤ x - 1 / 2 := by linarith
    nlinarith
  · have hs := (log_norm_Gamma_seg (a := x) (b := 1 / 2) hx h t).2
    rw [hhalf] at hs
    have hn : ‖(1 / 2 : ℂ) + t * I‖ ≤ 1 + |t| := by
      have := norm_le_max_mul (x := 1 / 2) (by norm_num) t
      rw [hhalf, max_eq_left (by norm_num), one_mul] at this
      exact this
    have hpos : 0 < ‖(1 / 2 : ℂ) + t * I‖ := by
      have := norm_add_mul_I_pos (x := 1 / 2) (by norm_num) t; rwa [hhalf] at this
    have hlog : Real.log ‖(1 / 2 : ℂ) + t * I‖ ≤ Real.log (1 + |t|) := Real.log_le_log hpos hn
    have habs : |x - 1 / 2| = 1 / 2 - x := by rw [abs_of_nonpos (by linarith)]; ring
    rw [habs, hl5]
    have hx0 : 0 ≤ 1 / 2 - x := by linarith
    nlinarith

/-- `log|Γ(1/2 + iy₁)| − log|Γ(1/2 + iy₀)| ≤ π|y₁ − y₀|/2 + log 2/2`, from `|Γ(1/2 + it)|² = π/cosh(πt)`. -/
theorem log_norm_Gamma_half_sub (y₀ y₁ : ℝ) :
    Real.log ‖Complex.Gamma (1 / 2 + y₁ * I)‖ - Real.log ‖Complex.Gamma (1 / 2 + y₀ * I)‖ ≤
      Real.pi * |y₁ - y₀| / 2 + Real.log 2 / 2 := by
  have hsq : ∀ y : ℝ, Real.log ‖Complex.Gamma (1 / 2 + y * I)‖ =
      (Real.log Real.pi - Real.log (Real.cosh (Real.pi * y))) / 2 := by
    intro y
    have h := Subconvexity.norm_Gamma_half_sq y
    have hpos : 0 < ‖Complex.Gamma (1 / 2 + y * I)‖ := by
      rw [norm_pos_iff]
      exact Complex.Gamma_ne_zero_of_re_pos (by simp)
    have h2 := congrArg Real.log h
    rw [Real.log_pow, Real.log_div Real.pi_pos.ne' (Real.cosh_pos _).ne'] at h2
    push_cast at h2
    linarith
  rw [hsq, hsq]
  have hup : ∀ z : ℝ, Real.log (Real.cosh z) ≤ |z| := by
    intro z
    rw [Real.log_le_iff_le_exp (Real.cosh_pos _), Real.cosh_eq]
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]
      have : Real.exp (-z) ≤ Real.exp z := Real.exp_le_exp.2 (by linarith)
      linarith
    · rw [abs_of_nonpos h]
      have : Real.exp z ≤ Real.exp (-z) := Real.exp_le_exp.2 (by linarith)
      linarith
  have hlo : ∀ z : ℝ, |z| - Real.log 2 ≤ Real.log (Real.cosh z) := by
    intro z
    have h := InghamDensity.exp_abs_le_two_cosh z
    have h2 : |z| ≤ Real.log (2 * Real.cosh z) := by
      rw [Real.le_log_iff_exp_le (by positivity)]; exact h
    rw [Real.log_mul (by norm_num) (Real.cosh_pos _).ne'] at h2
    linarith
  have h1 := hup (Real.pi * y₀)
  have h2 := hlo (Real.pi * y₁)
  have h3 : |Real.pi * y₀| - |Real.pi * y₁| ≤ Real.pi * |y₁ - y₀| := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    have := abs_sub_abs_le_abs_sub y₀ y₁
    rw [abs_sub_comm] at this
    nlinarith [Real.pi_pos]
  linarith

/-- `log(1 + |y + u|) ≤ log(1 + |y|) + log(1 + |u|)`. -/
lemma log_one_add_abs_add_le (y u : ℝ) :
    Real.log (1 + |y + u|) ≤ Real.log (1 + |y|) + Real.log (1 + |u|) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have := abs_add_le y u
  nlinarith [abs_nonneg y, abs_nonneg u]

/-- The constant of `log_norm_Gamma_ratio`. -/
def KR (c : ℝ) : ℝ :=
  (c / 2 + 1 / 4) * Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c / 2)) + 1 / 4 * Real.log (5 * Real.exp 4) +
    Real.log 2 / 2

/-- **The ratio of two values of `Γ`**: for `1/4 ≤ x₀ ≤ 3/4` and `c ≥ 0`,
`log|Γ(x₀ + c/2 + i(y₀ + v/2))| − log|Γ(x₀ + iy₀)| ≤ (c/2)log(1 + |y₀|) + (c/2 + 1/4)log(1 + |v|) + π|v|/4 + KR(c)`. -/
theorem log_norm_Gamma_ratio {x₀ c y₀ v : ℝ} (hx₀ : 1 / 4 ≤ x₀) (hx₀' : x₀ ≤ 3 / 4) (hc : 0 ≤ c) :
    Real.log ‖Complex.Gamma ((x₀ + c / 2 : ℝ) + (y₀ + v / 2 : ℝ) * I)‖ -
        Real.log ‖Complex.Gamma (x₀ + y₀ * I)‖ ≤
      c / 2 * Real.log (1 + |y₀|) + (c / 2 + 1 / 4) * Real.log (1 + |v|) + Real.pi * |v| / 4 + KR c := by
  have hA := log_norm_Gamma_le (x := x₀ + c / 2) (by linarith) (y₀ + v / 2)
  have hB := log_norm_Gamma_ge (x := x₀) hx₀ y₀
  have hH := log_norm_Gamma_half_sub y₀ (y₀ + v / 2)
  have hv2 : |y₀ + v / 2 - y₀| = |v| / 2 := by
    rw [show y₀ + v / 2 - y₀ = v / 2 by ring, abs_div, abs_two]
  rw [hv2] at hH
  set ℓ₀ := Real.log (1 + |y₀|) with hℓ₀
  set ℓ₁ := Real.log (1 + |y₀ + v / 2|) with hℓ₁
  set lv := Real.log (1 + |v|) with hlv
  have hlv0 : 0 ≤ lv := Real.log_nonneg (by linarith [abs_nonneg v])
  have hhalf : Real.log (1 + |v / 2|) ≤ lv := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith [abs_nonneg v]
  have h1 : ℓ₁ ≤ ℓ₀ + lv := by
    have := log_one_add_abs_add_le y₀ (v / 2); rw [← hℓ₀, ← hℓ₁] at this; linarith
  have h2 : ℓ₀ ≤ ℓ₁ + lv := by
    have := log_one_add_abs_add_le (y₀ + v / 2) (-(v / 2))
    rw [show y₀ + v / 2 + -(v / 2) = y₀ by ring, abs_neg, ← hℓ₀, ← hℓ₁] at this; linarith
  have hd : |ℓ₁ - ℓ₀| ≤ lv := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hx0abs : |x₀ - 1 / 2| ≤ 1 / 4 := abs_le.2 ⟨by linarith, by linarith⟩
  have hx1abs : |x₀ + c / 2 - 1 / 2| ≤ c / 2 + 1 / 4 := abs_le.2 ⟨by linarith, by linarith⟩
  have hmid : (x₀ - 1 / 2) * (ℓ₁ - ℓ₀) ≤ 1 / 4 * lv := by
    calc (x₀ - 1 / 2) * (ℓ₁ - ℓ₀) ≤ |(x₀ - 1 / 2) * (ℓ₁ - ℓ₀)| := le_abs_self _
      _ = |x₀ - 1 / 2| * |ℓ₁ - ℓ₀| := abs_mul _ _
      _ ≤ 1 / 4 * lv := mul_le_mul hx0abs hd (abs_nonneg _) (by norm_num)
  have hl1 : 0 ≤ ℓ₀ := Real.log_nonneg (by linarith [abs_nonneg y₀])
  have hM : max 1 (x₀ + c / 2) ≤ max 1 (3 / 4 + c / 2) := max_le_max le_rfl (by linarith)
  have hLpos : 0 ≤ Real.log (5 * Real.exp 4 * max 1 (x₀ + c / 2)) := by
    apply Real.log_nonneg
    have : 1 ≤ max 1 (x₀ + c / 2) := le_max_left _ _
    have : 1 ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
    nlinarith
  have hLmono : Real.log (5 * Real.exp 4 * max 1 (x₀ + c / 2)) ≤
      Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c / 2)) := by
    apply Real.log_le_log (by positivity)
    gcongr
  have hL5 : 0 ≤ Real.log (5 * Real.exp 4) := by
    apply Real.log_nonneg
    have : 1 ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
    nlinarith
  have hlast1 : |x₀ + c / 2 - 1 / 2| * Real.log (5 * Real.exp 4 * max 1 (x₀ + c / 2)) ≤
      (c / 2 + 1 / 4) * Real.log (5 * Real.exp 4 * max 1 (3 / 4 + c / 2)) :=
    mul_le_mul hx1abs hLmono hLpos (by linarith)
  have hlast0 : |x₀ - 1 / 2| * Real.log (5 * Real.exp 4) ≤ 1 / 4 * Real.log (5 * Real.exp 4) :=
    mul_le_mul_of_nonneg_right hx0abs hL5
  have hc1 : c / 2 * ℓ₁ ≤ c / 2 * (ℓ₀ + lv) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have e : (x₀ + c / 2 - 1 / 2) * ℓ₁ - (x₀ - 1 / 2) * ℓ₀ = c / 2 * ℓ₁ + (x₀ - 1 / 2) * (ℓ₁ - ℓ₀) := by ring
  unfold KR
  push_cast at hA hH ⊢
  linarith

/-- **The ratio of two values of `Γ`**, exponentiated. -/
theorem norm_Gamma_ratio_le {x₀ c y₀ v : ℝ} (hx₀ : 1 / 4 ≤ x₀) (hx₀' : x₀ ≤ 3 / 4) (hc : 0 ≤ c) :
    ‖Complex.Gamma ((x₀ + c / 2 : ℝ) + (y₀ + v / 2 : ℝ) * I)‖ ≤
      Real.exp (KR c) * (1 + |y₀|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
        ‖Complex.Gamma (x₀ + y₀ * I)‖ := by
  have h := log_norm_Gamma_ratio (y₀ := y₀) (v := v) hx₀ hx₀' hc
  have hp1 : 0 < ‖Complex.Gamma ((x₀ + c / 2 : ℝ) + (y₀ + v / 2 : ℝ) * I)‖ := by
    rw [norm_pos_iff]; exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hp0 : 0 < ‖Complex.Gamma (x₀ + y₀ * I)‖ := by
    rw [norm_pos_iff]; exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hy : 0 < 1 + |y₀| := by positivity
  have hv : 0 < 1 + |v| := by positivity
  rw [← Real.exp_log hp1]
  have e : Real.exp (KR c) * (1 + |y₀|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) *
      Real.exp (Real.pi * |v| / 4) * ‖Complex.Gamma (x₀ + y₀ * I)‖ =
      Real.exp (KR c + c / 2 * Real.log (1 + |y₀|) + (c / 2 + 1 / 4) * Real.log (1 + |v|) +
        Real.pi * |v| / 4 + Real.log ‖Complex.Gamma (x₀ + y₀ * I)‖) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hp0,
      Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hv]
    ring_nf
  rw [e]
  apply Real.exp_le_exp.2
  linarith

/-- **The ratio of two values of the Archimedean factor**: for every Dirichlet character `χ`, `c ≥ 0` and real
`t`, `v`, `|γ_χ(1/2 + it + c + iv)| ≤ e^{KR(c)}(1 + |t|)^{c/2}(1 + |v|)^{c/2+1/4}e^{π|v|/4}|γ_χ(1/2 + it)|`. -/
theorem norm_gammaFactor_ratio_le {N : ℕ} (χ : DirichletCharacter ℂ N) {c : ℝ} (hc : 0 ≤ c) (t v : ℝ) :
    ‖DirichletCharacter.gammaFactor χ (1 / 2 + t * I + (c + v * I))‖ ≤
      Real.exp (KR c) * (1 + |t|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
        ‖DirichletCharacter.gammaFactor χ (1 / 2 + t * I)‖ := by
  -- the common step, for `a = 0` (even) and `a = 1` (odd)
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ‖Complex.Gammaℝ (1 / 2 + t * I + (c + v * I) + a)‖ ≤
        Real.exp (KR c) * (1 + |t|) ^ (c / 2) * (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
          ‖Complex.Gammaℝ (1 / 2 + t * I + a)‖ := by
    intro a ha0 ha1
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have e1 : (1 / 2 + t * I + (c + v * I) + a) / 2 =
        (((1 / 4 + a / 2) + c / 2 : ℝ) : ℂ) + ((t / 2 + v / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    have e0 : (1 / 2 + t * I + a) / 2 = (((1 / 4 + a / 2) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e1, e0]
    have hG := norm_Gamma_ratio_le (x₀ := 1 / 4 + a / 2) (c := c) (y₀ := t / 2) (v := v)
      (by linarith) (by linarith) hc
    have hre1 : (-(1 / 2 + t * I + (c + v * I) + a) / 2 : ℂ).re = -(1 / 2 + c + a) / 2 := by
      simp
    have hre0 : (-(1 / 2 + t * I + a) / 2 : ℂ).re = -(1 / 2 + a) / 2 := by
      simp
    rw [hre1, hre0]
    have hπ : Real.pi ^ (-(1 / 2 + c + a) / 2) ≤ Real.pi ^ (-(1 / 2 + a) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
    have ht : (1 + |t / 2|) ^ (c / 2) ≤ (1 + |t|) ^ (c / 2) := by
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      rw [abs_div, abs_two]; linarith [abs_nonneg t]
    have hpos : 0 ≤ Real.exp (KR c) * (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) := by
      positivity
    have hg0 : 0 ≤ ‖Complex.Gamma ((((1 / 4 + a / 2) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := norm_nonneg _
    calc Real.pi ^ (-(1 / 2 + c + a) / 2) *
          ‖Complex.Gamma ((((1 / 4 + a / 2) + c / 2 : ℝ) : ℂ) + ((t / 2 + v / 2 : ℝ) : ℂ) * I)‖
        ≤ Real.pi ^ (-(1 / 2 + a) / 2) * (Real.exp (KR c) * (1 + |t / 2|) ^ (c / 2) *
            (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
              ‖Complex.Gamma ((((1 / 4 + a / 2) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) :=
          mul_le_mul hπ hG (norm_nonneg _) (by positivity)
      _ ≤ Real.pi ^ (-(1 / 2 + a) / 2) * (Real.exp (KR c) * (1 + |t|) ^ (c / 2) *
            (1 + |v|) ^ (c / 2 + 1 / 4) * Real.exp (Real.pi * |v| / 4) *
              ‖Complex.Gamma ((((1 / 4 + a / 2) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) := by
          gcongr
      _ = _ := by ring
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, h.gammaFactor_def]
    have := key 0 le_rfl zero_le_one
    simpa using this
  · rw [h.gammaFactor_def, h.gammaFactor_def]
    have := key 1 zero_le_one le_rfl
    simpa using this

open MeasureTheory Filter Topology in
/-- **Moving the line of integration across a simple pole at `0`.** If `G` is holomorphic on the closed strip
`σ' ≤ Re w ≤ σ`, `σ' < 0 < σ`, except at `0`, where `G(w) − R/w` stays bounded, is integrable on both lines and
tends to `0` uniformly on the strip as `|Im w| → ∞`, then `∫_{(σ)} G − ∫_{(σ')} G = 2πiR` (PNT+'s
`ResidueTheoremOnRectangleWithSimplePole'` on the rectangles, and round 472's limits). -/
theorem verticalIntegral_sub_eq {G : ℂ → ℂ} {σ' σ : ℝ} (hσ' : σ' < 0) (hσ : 0 < σ) (R : ℂ)
    (hG : HolomorphicOn G ((Icc σ' σ ×ℂ univ) \ {0}))
    (hR : (G - fun w ↦ R / (w - 0)) =O[𝓝[≠] 0] (1 : ℂ → ℂ))
    (hint : Integrable fun t : ℝ ↦ G (σ + t * I)) (hint' : Integrable fun t : ℝ ↦ G (σ' + t * I))
    (hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc σ' σ, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η) :
    VerticalIntegral G σ - VerticalIntegral G σ' = 2 * π * I * R := by
  have hσσ : σ' ≤ σ := by linarith
  have hrect : ∀ T : ℝ, 0 < T → RectangleIntegral G (σ' - I * T) (σ + I * T) = 2 * π * I * R := by
    intro T hT
    have hz : (↑σ' - I * ↑T : ℂ).re ≤ (↑σ + I * ↑T : ℂ).re := by simp; linarith
    have hzi : (↑σ' - I * ↑T : ℂ).im ≤ (↑σ + I * ↑T : ℂ).im := by simp; linarith
    have hnhds : Rectangle (↑σ' - I * ↑T) (↑σ + I * ↑T) ∈ 𝓝 (0 : ℂ) := by
      rw [rectangle_mem_nhds_iff]
      simp only [mem_reProdIm, zero_re, zero_im]
      constructor
      · simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, sub_zero, mul_zero,
          add_re, add_zero]
        rw [Set.uIoo_of_le hσσ]
        exact ⟨hσ', hσ⟩
      · simp only [sub_im, ofReal_im, mul_im, I_re, ofReal_re, I_im, zero_mul, zero_add, one_mul,
          zero_sub, add_im]
        rw [Set.uIoo_of_le (by linarith)]
        exact ⟨by linarith, hT⟩
    have hhol : HolomorphicOn G (Rectangle (↑σ' - I * ↑T) (↑σ + I * ↑T) \ {0}) := by
      refine hG.mono fun z hz ↦ ⟨?_, hz.2⟩
      have h1 := hz.1
      rw [Rectangle, mem_reProdIm] at h1
      rw [mem_reProdIm]
      refine ⟨?_, mem_univ _⟩
      have h2 := h1.1
      simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, sub_zero,
        mul_zero, add_re, add_zero] at h2
      rwa [uIcc_of_le hσσ] at h2
    have h := ResidueTheoremOnRectangleWithSimplePole' hz hzi hnhds hhol hR
    rw [RectangleIntegral'] at h
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      simp [this, I_ne_zero]
    rw [smul_eq_mul, div_mul_eq_mul_div, one_mul, div_eq_iff h2pi] at h
    rw [h]; ring
  have hdiff : ∀ T : ℝ, 0 < T → VerticalIntegral G σ - VerticalIntegral G σ' - 2 * π * I * R =
      UpperUIntegral G σ' σ T - LowerUIntegral G σ' σ T := by
    intro T hT
    have h := DiffVertRect_eq_UpperLowerUs (f := G) (σ := σ') (σ' := σ) (T := T) hint' hint
    rw [hrect T hT] at h
    exact h
  have habs : Tendsto (fun T : ℝ ↦ |T|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp tendsto_id
  have habs' : Tendsto (fun T : ℝ ↦ |-T|) atTop atTop := by
    simpa only [abs_neg] using habs
  have hU : Tendsto (fun T ↦ UpperUIntegral G σ' σ T) atTop (𝓝 0) := by
    have := ((SmoothPerron.tendsto_HIntegral hσσ hdecay habs).add
      ((SmoothPerron.tendsto_integral_Ici hint).const_smul I)).sub
      ((SmoothPerron.tendsto_integral_Ici hint').const_smul I)
    simpa [UpperUIntegral] using this
  have hL : Tendsto (fun T ↦ LowerUIntegral G σ' σ T) atTop (𝓝 0) := by
    have := ((SmoothPerron.tendsto_HIntegral hσσ hdecay habs').sub
      ((SmoothPerron.tendsto_integral_Iic_neg hint).const_smul I)).add
      ((SmoothPerron.tendsto_integral_Iic_neg hint').const_smul I)
    simpa [LowerUIntegral] using this
  have hlim := hU.sub hL
  rw [sub_zero] at hlim
  have hconst : Tendsto (fun T ↦ UpperUIntegral G σ' σ T - LowerUIntegral G σ' σ T) atTop
      (𝓝 (VerticalIntegral G σ - VerticalIntegral G σ' - 2 * π * I * R)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact hdiff T hT
  have := tendsto_nhds_unique hconst hlim
  linear_combination this

/-! ### The approximate functional equation -/

open DirichletCharacter

/-- `Γ(x) ≤ 8` for `1/4 ≤ x ≤ 2`: `Γ(x + 1) ≤ 2` by the convexity of `Γ` between `1` and `3`. -/
lemma real_Gamma_le_eight {x : ℝ} (h1 : 1 / 4 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 8 := by
  have hx0 : 0 < x := by linarith
  have hy : Real.Gamma (x + 1) ≤ 2 := by
    have hc := Real.convexOn_Gamma.2 (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (3 : ℝ) ∈ Ioi 0)
      (by linarith : 0 ≤ (2 - x) / 2) (by linarith : 0 ≤ x / 2) (by ring)
    have h13 : ((2 - x) / 2) • (1 : ℝ) + (x / 2) • (3 : ℝ) = x + 1 := by simp only [smul_eq_mul]; ring
    rw [h13] at hc
    have hG3 : Real.Gamma 3 = 2 := by
      rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
    rw [Real.Gamma_one, hG3, smul_eq_mul, smul_eq_mul] at hc
    nlinarith
  have hrec : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx0.ne'
  have hGpos := Real.Gamma_pos_of_pos hx0
  nlinarith

/-- `|γ_χ(z)| ≤ 8` on `1/2 ≤ Re z ≤ 3`. -/
lemma norm_gammaFactor_le {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 3) :
    ‖gammaFactor χ z‖ ≤ 8 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact (PsiOmega.norm_Gammaℝ_le' (by linarith)).trans (real_Gamma_le_eight (by linarith) (by linarith))
  · rw [h.gammaFactor_def]
    have hre : (z + 1).re = z.re + 1 := by simp
    refine (PsiOmega.norm_Gammaℝ_le' (by rw [hre]; linarith)).trans ?_
    rw [hre]
    exact real_Gamma_le_eight (by linarith) (by linarith)

lemma gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ} (h : 0 < z.re) :
    gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with hp | hp
  · rw [hp.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos h
  · rw [hp.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- `Λ(z, χ) = L(z, χ)γ_χ(z)` on `Re z > 0`. -/
lemma completed_eq_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {z : ℂ} (h : 0 < z.re) :
    completedLFunction χ z = LFunction χ z * gammaFactor χ z := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  rw [LFunction_eq_completed_div_gammaFactor χ z (Or.inl hz0)]
  field_simp [gammaFactor_ne_zero χ h]

/-- `|Λ(z, χ)| ≤ 16(N + 1)(3 + |Im z|)` on `1/2 ≤ Re z ≤ 3`, for `χ ≠ 1` (round 254's
`PsiOmega.norm_LFunction_leC`). -/
lemma norm_completed_right {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {z : ℂ}
    (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 3) :
    ‖completedLFunction χ z‖ ≤ 16 * ((N : ℝ) + 1) * (3 + |z.im|) := by
  rw [completed_eq_mul χ (by linarith), norm_mul]
  have hLb := PsiOmega.norm_LFunction_leC hχ (by linarith : 0 < z.re)
  have hn : ‖z‖ ≤ 3 + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg (by linarith : 0 ≤ z.re)] at this; linarith
  have hN0 : (0 : ℝ) ≤ N + 1 := by positivity
  have hLb' : ‖LFunction χ z‖ ≤ 2 * ((N : ℝ) + 1) * (3 + |z.im|) := by
    refine hLb.trans ?_
    rw [div_le_iff₀ (by linarith)]
    calc ((N : ℝ) + 1) * ‖z‖ ≤ ((N : ℝ) + 1) * (3 + |z.im|) := by gcongr
      _ ≤ ((N : ℝ) + 1) * (3 + |z.im|) * (2 * z.re) := by
          have : 0 ≤ ((N : ℝ) + 1) * (3 + |z.im|) := by positivity
          nlinarith
      _ = 2 * ((N : ℝ) + 1) * (3 + |z.im|) * z.re := by ring
  calc ‖LFunction χ z‖ * ‖gammaFactor χ z‖ ≤ (2 * ((N : ℝ) + 1) * (3 + |z.im|)) * 8 :=
        mul_le_mul hLb' (norm_gammaFactor_le χ h1 h2) (norm_nonneg _) (by positivity)
    _ = 16 * ((N : ℝ) + 1) * (3 + |z.im|) := by ring

/-- **`Λ(z, χ)` in the strip `−2 ≤ Re z ≤ 3`**, for primitive `χ ≠ 1` mod `N`: at most
`16(N + 1)N^{5/2}(3 + |Im z|)`; left of `1/2` by Mathlib's functional equation and `|ε(χ)| = 1`. -/
lemma norm_completed_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {z : ℂ} (h1 : -2 ≤ z.re) (h2 : z.re ≤ 3) :
    ‖completedLFunction χ z‖ ≤ 16 * ((N : ℝ) + 1) * (N : ℝ) ^ (5 / 2 : ℝ) * (3 + |z.im|) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hN52 : 1 ≤ (N : ℝ) ^ (5 / 2 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  rcases le_total (1 / 2) z.re with h | h
  · have hR := norm_completed_right hχ h h2
    have h0 : 0 ≤ 16 * ((N : ℝ) + 1) * (3 + |z.im|) := by positivity
    calc _ ≤ 16 * ((N : ℝ) + 1) * (3 + |z.im|) := hR
      _ ≤ 16 * ((N : ℝ) + 1) * (3 + |z.im|) * (N : ℝ) ^ (5 / 2 : ℝ) := le_mul_of_one_le_right h0 hN52
      _ = _ := by ring
  · have hinv : χ⁻¹.IsPrimitive := by
      unfold DirichletCharacter.IsPrimitive at hprim ⊢
      rw [conductor_inv]; exact hprim
    have hχinv : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ
    have hFE := hprim.completedLFunction_one_sub (1 - z)
    rw [sub_sub_cancel] at hFE
    have hre : (1 - z).re = 1 - z.re := by simp
    have him : (1 - z).im = -z.im := by simp
    have hR := norm_completed_right hχinv (z := 1 - z) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him, abs_neg] at hR
    rw [hFE, norm_mul, norm_mul, LinnikFE.norm_rootNumber hprim, mul_one]
    have hNs : ‖(N : ℂ) ^ (1 - z - 1 / 2)‖ = (N : ℝ) ^ (1 / 2 - z.re) := by
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      congr 1; simp; ring
    rw [hNs]
    have hNb : (N : ℝ) ^ (1 / 2 - z.re) ≤ (N : ℝ) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc (N : ℝ) ^ (1 / 2 - z.re) * ‖completedLFunction χ⁻¹ (1 - z)‖
        ≤ (N : ℝ) ^ (5 / 2 : ℝ) * (16 * ((N : ℝ) + 1) * (3 + |z.im|)) :=
          mul_le_mul hNb hR (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- `(a + u)²e^{−u²} ≤ 4(a² + 1)/u` for `u ≥ 1`. -/
lemma sq_mul_exp_neg_sq_le {a u : ℝ} (hu : 1 ≤ u) :
    (a + u) ^ 2 * Real.exp (-u ^ 2) ≤ 4 * (a ^ 2 + 1) / u := by
  have hu0 : 0 < u := by linarith
  have he := Real.quadratic_le_exp_of_nonneg (sq_nonneg u)
  have hexp : 0 < Real.exp (u ^ 2) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexp hu0]
  have h1 : (a + u) ^ 2 ≤ 2 * a ^ 2 + 2 * u ^ 2 := by nlinarith [sq_nonneg (a - u)]
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hu3 : u ≤ u ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hu0.le, sq_nonneg (u ^ 2), sq_nonneg a]

/-- `(a + |y|)²e^{−y²} ≤ (2a² + 2)e^{−y²/2}`. -/
lemma sq_mul_exp_neg_sq_le' (a y : ℝ) :
    (a + |y|) ^ 2 * Real.exp (-y ^ 2) ≤ (2 * a ^ 2 + 2) * Real.exp (-y ^ 2 / 2) := by
  have h1 : (a + |y|) ^ 2 ≤ 2 * a ^ 2 + 2 * y ^ 2 := by
    nlinarith [sq_nonneg (a - |y|), sq_abs y]
  have h2 : y ^ 2 * Real.exp (-y ^ 2 / 2) ≤ 1 := by
    have he := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 2 / 2)
    have hpos := Real.exp_pos (y ^ 2 / 2)
    rw [show -y ^ 2 / 2 = -(y ^ 2 / 2) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
    nlinarith [sq_nonneg (y ^ 2 - 2)]
  have e : Real.exp (-y ^ 2) = Real.exp (-y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hp := Real.exp_pos (-y ^ 2 / 2)
  rw [e]
  have hle : Real.exp (-y ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg y])
  set E := Real.exp (-y ^ 2 / 2) with hE
  have hEE : E * E ≤ E := by nlinarith
  calc (a + |y|) ^ 2 * (E * E) ≤ (2 * a ^ 2 + 2 * y ^ 2) * (E * E) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 * a ^ 2 * (E * E) + 2 * ((y ^ 2 * E) * E) := by ring
    _ ≤ 2 * a ^ 2 * E + 2 * (1 * E) := by
        gcongr
    _ = (2 * a ^ 2 + 2) * E := by ring

/-- The integrand of the approximate functional equation: `Λ(s + w, χ)² N^w e^{w²}/w`. -/
def afeG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s w : ℂ) : ℂ :=
  completedLFunction χ (s + w) ^ 2 * (N : ℂ) ^ w * Complex.exp (w ^ 2) / w

/-- `J(s, χ) = (1/2πi)∫_{(2)} Λ(s + w, χ)² N^w e^{w²} dw/w`. -/
def afeJ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := VerticalIntegral' (afeG χ s) 2

lemma differentiable_afeF {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    Differentiable ℂ fun w : ℂ => completedLFunction χ (s + w) ^ 2 * (N : ℂ) ^ w * Complex.exp (w ^ 2) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h1 : Differentiable ℂ fun w : ℂ => completedLFunction χ (s + w) :=
    (differentiable_completedLFunction hχ).comp (differentiable_const s |>.add differentiable_id)
  have h2 : Differentiable ℂ fun w : ℂ => (N : ℂ) ^ w := fun w => (differentiableAt_id.const_cpow (Or.inl hN0))
  exact ((h1.pow 2).mul h2).mul (Complex.differentiable_exp.comp (differentiable_id.pow 2))

/-- The bound on `afeG` in the strip `|Re w| ≤ 2`, for `0 ≤ Re s ≤ 1`. -/
lemma norm_afeG_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) {x y : ℝ} (hx1 : -2 ≤ x) (hx2 : x ≤ 2) (hw : (x : ℂ) + y * I ≠ 0) :
    ‖afeG χ s (x + y * I)‖ ≤ (16 * ((N : ℝ) + 1) * (N : ℝ) ^ (5 / 2 : ℝ)) ^ 2 * (N : ℝ) ^ (2 : ℝ) *
      Real.exp 4 * ((3 + |s.im| + |y|) ^ 2 * Real.exp (-y ^ 2)) / ‖(x : ℂ) + y * I‖ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hre : (s + (x + y * I)).re = s.re + x := by simp
  have him : (s + (x + y * I)).im = s.im + y := by simp
  have hL := norm_completed_le hprim hχ (z := s + (x + y * I)) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [him] at hL
  have him' : |s.im + y| ≤ |s.im| + |y| := abs_add_le _ _
  have hL' : ‖completedLFunction χ (s + (x + y * I))‖ ≤
      16 * ((N : ℝ) + 1) * (N : ℝ) ^ (5 / 2 : ℝ) * (3 + |s.im| + |y|) := by
    refine hL.trans ?_
    have : 0 ≤ 16 * ((N : ℝ) + 1) * (N : ℝ) ^ (5 / 2 : ℝ) := by positivity
    nlinarith
  have hNw : ‖(N : ℂ) ^ ((x : ℂ) + y * I)‖ ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hx2
  have hexp : ‖Complex.exp (((x : ℂ) + y * I) ^ 2)‖ ≤ Real.exp 4 * Real.exp (-y ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (((x : ℂ) + y * I) ^ 2).re = x ^ 2 - y ^ 2 := by simp [sq]
    rw [this]; nlinarith
  unfold afeG
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  have hwpos : 0 < ‖(x : ℂ) + y * I‖ := norm_pos_iff.2 hw
  rw [div_le_div_iff_of_pos_right hwpos]
  have hA : 0 ≤ 16 * ((N : ℝ) + 1) * (N : ℝ) ^ (5 / 2 : ℝ) * (3 + |s.im| + |y|) := by positivity
  calc ‖completedLFunction χ (s + (x + y * I))‖ ^ 2 * ‖(N : ℂ) ^ ((x : ℂ) + y * I)‖ *
        ‖Complex.exp (((x : ℂ) + y * I) ^ 2)‖
      ≤ (16 * ((N : ℝ) + 1) * (N : ℝ) ^ (5 / 2 : ℝ) * (3 + |s.im| + |y|)) ^ 2 * (N : ℝ) ^ (2 : ℝ) *
          (Real.exp 4 * Real.exp (-y ^ 2)) := by gcongr
    _ = _ := by ring

open Filter Topology in
/-- **The approximate functional equation for `L(s, χ)²`.** For primitive `χ ≠ 1` mod `N` and `0 ≤ Re s ≤ 1`,
`Λ(s, χ)² = J(s, χ) + ε(χ)²N^{1−2s}J(1 − s, χ⁻¹)`, with `J(s, χ) = (1/2πi)∫_{(2)} Λ(s + w, χ)²N^w e^{w²} dw/w`:
`verticalIntegral_sub_eq` across the pole at `w = 0`, and Mathlib's functional equation on `Re w = −2`. -/
theorem afe {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    completedLFunction χ s ^ 2 = afeJ χ s + rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s) * afeJ χ⁻¹ (1 - s) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hinv : χ⁻¹.IsPrimitive := by
    unfold DirichletCharacter.IsPrimitive at hprim ⊢
    rw [conductor_inv]; exact hprim
  have hχinv : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ
  set G := afeG χ s with hG
  set F : ℂ → ℂ := fun w => completedLFunction χ (s + w) ^ 2 * (N : ℂ) ^ w * Complex.exp (w ^ 2) with hF
  have hFd := differentiable_afeF hχ s
  have hGF : ∀ w, G w = F w / w := fun w => rfl
  -- the constants of the strip bound
  set B := (16 * ((N : ℝ) + 1) * (N : ℝ) ^ (5 / 2 : ℝ)) ^ 2 * (N : ℝ) ^ (2 : ℝ) * Real.exp 4 with hB
  have hB0 : 0 ≤ B := by positivity
  set a := 3 + |s.im| with ha
  -- holomorphy off `0`
  have hhol : HolomorphicOn G ((Icc (-2) 2 ×ℂ univ) \ {0}) := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    exact ((hFd w).div differentiableAt_id hw0).differentiableWithinAt
  -- the residue
  have hres : (G - fun w ↦ completedLFunction χ s ^ 2 / (w - 0)) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
    have hF0 : F 0 = completedLFunction χ s ^ 2 := by simp [hF]
    have hslope := (hFd 0).hasDerivAt.tendsto_slope_zero
    have hb : (fun w => slope F 0 w) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
      have h1 : Tendsto (fun w => slope F 0 w) (𝓝[≠] 0) (𝓝 (deriv F 0)) := by
        have := (hFd 0).hasDerivAt.tendsto_slope
        exact this
      exact h1.isBigO_one ℂ
    refine hb.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Pi.sub_apply, hGF, slope_def_field, sub_zero, hF0]
    rw [sub_div]
  -- integrability on the two lines
  have hline : ∀ x : ℝ, (x = 2 ∨ x = -2) → Integrable fun t : ℝ => G (x + t * I) := by
    intro x hx
    have hx1 : -2 ≤ x := by rcases hx with h | h <;> linarith
    have hx2 : x ≤ 2 := by rcases hx with h | h <;> linarith
    have hxn : ∀ t : ℝ, (x : ℂ) + t * I ≠ 0 := fun t h => by
      have := congrArg Complex.re h; simp at this; rcases hx with h' | h' <;> linarith
    have hcont : Continuous fun t : ℝ => G (x + t * I) := by
      have hc1 : Continuous fun t : ℝ => (x : ℂ) + t * I := by fun_prop
      exact (hFd.continuous.comp hc1).div hc1 hxn
    refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (B * (2 * a ^ 2 + 2) / 2)) hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have h := norm_afeG_le hprim hχ hs0 hs1 hx1 hx2 (hxn t) (y := t)
    have hn2 : 2 ≤ ‖(x : ℂ) + t * I‖ := by
      have h0 := Complex.abs_re_le_norm ((x : ℂ) + t * I)
      have hre : ((x : ℂ) + t * I).re = x := by simp
      rw [hre] at h0
      have hax : |x| = 2 := by rcases hx with h' | h' <;> rw [h'] <;> norm_num
      linarith
    have h2 := sq_mul_exp_neg_sq_le' a t
    have hnum : 0 ≤ (a + |t|) ^ 2 * Real.exp (-t ^ 2) := by positivity
    calc ‖G (x + t * I)‖ ≤ B * ((a + |t|) ^ 2 * Real.exp (-t ^ 2)) / ‖(x : ℂ) + t * I‖ := by
          simpa [hG, hB, ha, add_assoc] using h
      _ ≤ B * ((a + |t|) ^ 2 * Real.exp (-t ^ 2)) / 2 := by
          gcongr
      _ ≤ B * ((2 * a ^ 2 + 2) * Real.exp (-t ^ 2 / 2)) / 2 := by gcongr
      _ = B * (2 * a ^ 2 + 2) / 2 * Real.exp (-(1 / 2) * t ^ 2) := by ring_nf
  -- uniform decay
  have hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc (-2 : ℝ) 2, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η := by
    intro η hη
    refine ⟨max 1 (B * 4 * (a ^ 2 + 1) / η), fun x hx y hy => ?_⟩
    have hy1 : 1 ≤ |y| := (le_max_left _ _).trans hy
    have hyB : B * 4 * (a ^ 2 + 1) / η ≤ |y| := (le_max_right _ _).trans hy
    have hyn : (x : ℂ) + y * I ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; rw [this] at hy1; simp at hy1; linarith
    have h := norm_afeG_le hprim hχ hs0 hs1 hx.1 hx.2 hyn
    have hn : |y| ≤ ‖(x : ℂ) + y * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + y * I); simpa using this
    have hk := sq_mul_exp_neg_sq_le (a := a) hy1
    rw [sq_abs] at hk
    have hpos : 0 < |y| := by linarith
    calc ‖G (x + y * I)‖ ≤ B * ((a + |y|) ^ 2 * Real.exp (-y ^ 2)) / ‖(x : ℂ) + y * I‖ := by
          simpa [hG, hB, ha, add_assoc] using h
      _ ≤ B * ((a + |y|) ^ 2 * Real.exp (-y ^ 2)) / 1 := by
          gcongr; linarith
      _ ≤ B * (4 * (a ^ 2 + 1) / |y|) := by rw [div_one]; gcongr
      _ = B * 4 * (a ^ 2 + 1) / |y| := by ring
      _ ≤ η := by
          rw [div_le_iff₀ hpos]
          rw [div_le_iff₀ hη] at hyB
          linarith
  have hsub := verticalIntegral_sub_eq (G := G) (σ' := -2) (σ := 2) (by norm_num) (by norm_num) _ hhol hres
    (hline 2 (Or.inl rfl)) (by simpa using hline (-2) (Or.inr rfl)) hdecay
  -- the left line through the functional equation
  set G' := afeG χ⁻¹ (1 - s) with hG'
  have hrefl : ∀ u : ℂ, u ≠ 0 → G (-u) = -(rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s)) * G' u := by
    intro u hu
    have hFE := hprim.completedLFunction_one_sub (1 - s + u)
    rw [show 1 - (1 - s + u) = s + -u by ring] at hFE
    simp only [hG, hG', afeG]
    rw [hFE]
    have hcp : ((N : ℂ) ^ (1 - s + u - 1 / 2)) ^ 2 * (N : ℂ) ^ (-u) = (N : ℂ) ^ (1 - 2 * s) * (N : ℂ) ^ u := by
      rw [sq, ← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]
      congr 1; ring
    have hnu : (-u : ℂ) ≠ 0 := neg_ne_zero.2 hu
    rw [neg_sq]
    calc ((N : ℂ) ^ (1 - s + u - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ (1 - s + u)) ^ 2 *
          (N : ℂ) ^ (-u) * Complex.exp (u ^ 2) / -u
        = (((N : ℂ) ^ (1 - s + u - 1 / 2)) ^ 2 * (N : ℂ) ^ (-u)) *
            (rootNumber χ ^ 2 * completedLFunction χ⁻¹ (1 - s + u) ^ 2 * Complex.exp (u ^ 2)) / -u := by ring
      _ = ((N : ℂ) ^ (1 - 2 * s) * (N : ℂ) ^ u) *
            (rootNumber χ ^ 2 * completedLFunction χ⁻¹ (1 - s + u) ^ 2 * Complex.exp (u ^ 2)) / -u := by
          rw [hcp]
      _ = _ := by field_simp
  have hleft : VerticalIntegral G (-2) = -(rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s)) * VerticalIntegral G' 2 := by
    simp only [VerticalIntegral]
    have h1 : ∫ t : ℝ, G ((-2 : ℝ) + t * I) = ∫ t : ℝ, G ((-2 : ℝ) + (-t) * I) := by
      rw [← integral_neg_eq_self]; simp only [ofReal_neg]
    rw [h1]
    have h2 : ∀ t : ℝ, G ((-2 : ℝ) + (-t) * I) =
        -(rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s)) * G' ((2 : ℝ) + t * I) := by
      intro t
      have hu : ((2 : ℝ) : ℂ) + t * I ≠ 0 := fun h => by
        have := congrArg Complex.re h; norm_num at this
      rw [← hrefl _ hu]
      congr 1; push_cast; ring
    simp_rw [h2]
    rw [integral_const_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hleft, hG, hG'] at hsub
  unfold afeJ VerticalIntegral'
  simp only [smul_eq_mul]
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    simp [this, I_ne_zero]
  have hsum : VerticalIntegral (afeG χ s) 2 + rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s) *
      VerticalIntegral (afeG χ⁻¹ (1 - s)) 2 = 2 * π * I * completedLFunction χ s ^ 2 := by
    linear_combination hsub
  calc completedLFunction χ s ^ 2 = 1 / (2 * π * I) * (2 * π * I * completedLFunction χ s ^ 2) := by
        field_simp
    _ = 1 / (2 * π * I) * (VerticalIntegral (afeG χ s) 2 + rootNumber χ ^ 2 * (N : ℂ) ^ (1 - 2 * s) *
          VerticalIntegral (afeG χ⁻¹ (1 - s)) 2) := by rw [hsum]
    _ = _ := by ring

end LinnikGamma

#print axioms LinnikGamma.norm_gammaFactor_ratio_le
#print axioms LinnikGamma.verticalIntegral_sub_eq
#print axioms LinnikGamma.afe
