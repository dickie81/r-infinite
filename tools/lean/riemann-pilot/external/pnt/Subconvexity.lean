/-
# Round 517: subconvexity from a zero-free half-plane

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If `ζ(s) ≠ 0` on `Re s > θ`, with `1/2 ≤ θ < 1`, then for `1 − θ ≤ σ ≤ θ` and every `ε > 0`,
`|ζ(σ + it)| ≤ C|t|^{(θ − σ)/2 + ε}` for `|t| ≥ 2` (`zeta_strip_of_zeroFree`); on the critical line,
`CrossCriteria.ZetaCritBound ((2θ − 1)/4 + ε)` (`zetaCritBound_of_zeroFree`). With no hypothesis at `θ = 11/12`,
from round 466's half-plane: `|ζ(σ + it)| = O(|t|^{(11/12 − σ)/2 + ε})` on `1/12 ≤ σ ≤ 11/12`
(`zeta_strip_eleven_twelfths`) and `|ζ(1/2 + it)| = O(|t|^{5/24 + ε})` (`zetaCritBound_five_24`), so
`CrossCriteria.ConvexityBound` holds (`convexityBound`). At round 469's `Θ`: `ZetaCritBound ((2Θ − 1)/4 + ε)`
(`zetaCritBound_Theta`). At `θ = 1/2`: RH implies `CrossCriteria.Lindelof` (`lindelof_of_RH`).

* `norm_le_interp_strip`: Hadamard's three lines (Mathlib's `norm_le_interp_of_mem_verticalClosedStrip'`) for
  `f(z)exp((z − it₀)²)`: polynomial bounds `A(1 + |t|)^α` and `B(1 + |t|)^β` on the two edges of a strip give
  the interpolated exponent at height `t₀`.
* `norm_Gamma_le_half`: `|Γ(σ + it)| ≤ |Γ(1/2 + it)|(e⁴|σ + it|)^{σ − 1/2}` for `σ ≥ 1/2`, by the mean value
  inequality for `log|Γ(x + it)|`, whose derivative `Re ψ(x + it)` is at most `log|x + it| + 4`
  (`Kaiser.digamma_re_le`, from Binet's formula).
* `norm_Gamma_half_sq`: `|Γ(1/2 + it)|² = π/cosh(πt)`.
* `norm_Gamma_mul_le_of`, `norm_Gamma_mul_cos_le`: `|Γ(s)w| ≤ 3(e⁴|s|)^{σ − 1/2}` on `Re s = σ ≥ 1/2` for every
  `w` with `|w| ≤ e^{π|Im s|/2}`, such as `cos(πs/2)`.
* `norm_zeta_one_sub_le`: `|ζ(1 − s)| ≤ 6(e⁴|s|)^{σ − 1/2}|ζ(s)|` for `1/2 ≤ σ < 1` (Mathlib's
  `riemannZeta_one_sub`).
* `zeta_strip_of_zeroFree`: round 470's Lindelöf bound on `Re s = θ + δ`, carried to `Re s = 1 − θ − δ` by
  `norm_zeta_one_sub_le`, interpolated by `norm_le_interp_strip`, with `ζ`'s polynomial growth in the strip
  (`HalfPlanePNT.norm_riemannZeta_le_of_re_pos`).
-/
import HalfPlaneLindelof
import CrossCriteria

open Complex Set Filter Topology

namespace Subconvexity

/-- `(1 + |y|)^a e^{−(y − t₀)²} ≤ (1 + |t₀|)^a e^{a²/4}` for `a ≥ 0`. -/
theorem rpow_mul_gauss_le {a : ℝ} (ha : 0 ≤ a) (y t₀ : ℝ) :
    (1 + |y|) ^ a * Real.exp (-(y - t₀) ^ 2) ≤ (1 + |t₀|) ^ a * Real.exp (a ^ 2 / 4) := by
  have h1 : 1 + |y| ≤ (1 + |t₀|) * (1 + |y - t₀|) := by
    have := abs_sub_abs_le_abs_sub y t₀
    nlinarith [abs_nonneg t₀, abs_nonneg (y - t₀), mul_nonneg (abs_nonneg t₀) (abs_nonneg (y - t₀))]
  have h2 : (1 + |y|) ^ a ≤ (1 + |t₀|) ^ a * (1 + |y - t₀|) ^ a := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h1 ha
  have h3 : (1 + |y - t₀|) ^ a ≤ Real.exp (a * |y - t₀|) := by
    calc (1 + |y - t₀|) ^ a ≤ (Real.exp |y - t₀|) ^ a :=
          Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp |y - t₀|]) ha
      _ = Real.exp (a * |y - t₀|) := by rw [← Real.exp_mul, mul_comm]
  have h4 : Real.exp (a * |y - t₀|) * Real.exp (-(y - t₀) ^ 2) ≤ Real.exp (a ^ 2 / 4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (y - t₀) ^ 2 = |y - t₀| ^ 2 := (sq_abs _).symm
    nlinarith [sq_nonneg (|y - t₀| - a / 2)]
  calc (1 + |y|) ^ a * Real.exp (-(y - t₀) ^ 2)
      ≤ (1 + |t₀|) ^ a * (1 + |y - t₀|) ^ a * Real.exp (-(y - t₀) ^ 2) := by gcongr
    _ ≤ (1 + |t₀|) ^ a * (Real.exp (a * |y - t₀|) * Real.exp (-(y - t₀) ^ 2)) := by
        rw [mul_assoc]; gcongr
    _ ≤ (1 + |t₀|) ^ a * Real.exp (a ^ 2 / 4) := by gcongr

/-- The modulus of the Gaussian weight: `|exp((z − it₀)²)| = exp(x² − (y − t₀)²)` for `z = x + iy`. -/
theorem norm_exp_gauss (z : ℂ) (t₀ : ℝ) :
    ‖Complex.exp ((z - t₀ * I) ^ 2)‖ = Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [sq, Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **Convexity in a strip with interpolated exponents.** If `f` is holomorphic on the closed strip
`l ≤ Re z ≤ u`, polynomially bounded there, and `|f(l + it)| ≤ A(1 + |t|)^α`, `|f(u + it)| ≤ B(1 + |t|)^β`
with `α, β ≥ 0`, then on `Re z = σ`, with `λ = (σ − l)/(u − l)`,
`|f(σ + it₀)| ≤ (Ae^{l² + α²/4})^{1−λ}(Be^{u² + β²/4})^λ(1 + |t₀|)^{(1−λ)α + λβ}`: Hadamard's three lines
(Mathlib's `norm_le_interp_of_mem_verticalClosedStrip'`) for `f(z)exp((z − it₀)²)`. -/
theorem norm_le_interp_strip {f : ℂ → ℂ} {l u A B α β K N : ℝ} (hlu : l < u) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hf : DifferentiableOn ℂ f (re ⁻¹' Icc l u))
    (hl : ∀ t : ℝ, ‖f (l + t * I)‖ ≤ A * (1 + |t|) ^ α)
    (hu : ∀ t : ℝ, ‖f (u + t * I)‖ ≤ B * (1 + |t|) ^ β)
    (hgr : ∀ z : ℂ, z.re ∈ Icc l u → ‖f z‖ ≤ K * (1 + |z.im|) ^ N)
    {σ : ℝ} (hσ : σ ∈ Icc l u) (t₀ : ℝ) :
    ‖f (σ + t₀ * I)‖ ≤ (A * Real.exp (l ^ 2 + α ^ 2 / 4)) ^ (1 - (σ - l) / (u - l)) *
      (B * Real.exp (u ^ 2 + β ^ 2 / 4)) ^ ((σ - l) / (u - l)) *
      (1 + |t₀|) ^ ((1 - (σ - l) / (u - l)) * α + (σ - l) / (u - l) * β) := by
  set g : ℂ → ℂ := fun z => f z * Complex.exp ((z - t₀ * I) ^ 2) with hg
  have hgn : ∀ z, ‖g z‖ = ‖f z‖ * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) := fun z => by
    rw [hg, norm_mul, norm_exp_gauss]
  have hA : 0 ≤ A := by
    have := hl 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hB : 0 ≤ B := by
    have := hu 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hK : 0 ≤ K := by
    have := hgr (l : ℂ) (by simp [hlu.le])
    simp only [Complex.ofReal_im, abs_zero, add_zero, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hre : ∀ z : ℂ, z = (z.re : ℂ) + (z.im : ℂ) * I := fun z => (Complex.re_add_im z).symm
  -- the bounds on the two edges
  have ha : ∀ z ∈ re ⁻¹' {l}, ‖g z‖ ≤
      A * Real.exp (l ^ 2 + α ^ 2 / 4) * (1 + |t₀|) ^ α := by
    intro z hz
    have hzre : z.re = l := hz
    have e1 := hl z.im
    rw [← hzre, ← hre z] at e1
    have e2 := rpow_mul_gauss_le hα z.im t₀
    rw [hgn, hzre]
    calc ‖f z‖ * Real.exp (l ^ 2 - (z.im - t₀) ^ 2)
        ≤ A * (1 + |z.im|) ^ α * Real.exp (l ^ 2 - (z.im - t₀) ^ 2) := by gcongr
      _ = A * Real.exp (l ^ 2) * ((1 + |z.im|) ^ α * Real.exp (-(z.im - t₀) ^ 2)) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ A * Real.exp (l ^ 2) * ((1 + |t₀|) ^ α * Real.exp (α ^ 2 / 4)) := by gcongr
      _ = A * Real.exp (l ^ 2 + α ^ 2 / 4) * (1 + |t₀|) ^ α := by rw [Real.exp_add]; ring
  have hb : ∀ z ∈ re ⁻¹' {u}, ‖g z‖ ≤
      B * Real.exp (u ^ 2 + β ^ 2 / 4) * (1 + |t₀|) ^ β := by
    intro z hz
    have hzre : z.re = u := hz
    have e1 := hu z.im
    rw [← hzre, ← hre z] at e1
    have e2 := rpow_mul_gauss_le hβ z.im t₀
    rw [hgn, hzre]
    calc ‖f z‖ * Real.exp (u ^ 2 - (z.im - t₀) ^ 2)
        ≤ B * (1 + |z.im|) ^ β * Real.exp (u ^ 2 - (z.im - t₀) ^ 2) := by gcongr
      _ = B * Real.exp (u ^ 2) * ((1 + |z.im|) ^ β * Real.exp (-(z.im - t₀) ^ 2)) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ B * Real.exp (u ^ 2) * ((1 + |t₀|) ^ β * Real.exp (β ^ 2 / 4)) := by gcongr
      _ = B * Real.exp (u ^ 2 + β ^ 2 / 4) * (1 + |t₀|) ^ β := by rw [Real.exp_add]; ring
  -- `g` is bounded on the closed strip
  have hbdd : BddAbove ((norm ∘ g) '' HadamardThreeLines.verticalClosedStrip l u) := by
    refine ⟨K * Real.exp ((|l| + |u|) ^ 2) * ((1 + |t₀|) ^ N * Real.exp (N ^ 2 / 4)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z.re ∈ Icc l u := hz
    have hx : z.re ^ 2 ≤ (|l| + |u|) ^ 2 := by
      have h1 : |z.re| ≤ |l| + |u| := by
        rw [abs_le]
        constructor <;> linarith [hz'.1, hz'.2, neg_abs_le l, le_abs_self u, abs_nonneg l,
          abs_nonneg u]
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have e2 := rpow_mul_gauss_le hN z.im t₀
    show ‖g z‖ ≤ _
    rw [hgn]
    calc ‖f z‖ * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2)
        ≤ K * (1 + |z.im|) ^ N * Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) := by
          gcongr; exact hgr z hz'
      _ = K * Real.exp (z.re ^ 2) * ((1 + |z.im|) ^ N * Real.exp (-(z.im - t₀) ^ 2)) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ K * Real.exp ((|l| + |u|) ^ 2) * ((1 + |t₀|) ^ N * Real.exp (N ^ 2 / 4)) := by gcongr
  -- `g` is holomorphic on the open strip and continuous on its closure
  have hd : DiffContOnCl ℂ g (HadamardThreeLines.verticalStrip l u) := by
    have hcl : closure (HadamardThreeLines.verticalStrip l u) = re ⁻¹' Icc l u := by
      rw [HadamardThreeLines.verticalStrip, closure_preimage_re, closure_Ioo hlu.ne]
    apply DifferentiableOn.diffContOnCl
    rw [hcl]
    exact hf.mul (Differentiable.differentiableOn (by fun_prop))
  have hmem : (σ : ℂ) + t₀ * I ∈ HadamardThreeLines.verticalClosedStrip l u := by
    show ((σ : ℂ) + t₀ * I).re ∈ Icc l u
    simpa using hσ
  have key := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hmem hd hbdd ha hb
  have hσre : ((σ : ℂ) + t₀ * I).re = σ := by simp
  have hσim : ((σ : ℂ) + t₀ * I).im = t₀ := by simp
  rw [hσre] at key
  -- `|f| ≤ |g|` at `σ + it₀`
  have hfg : ‖f (σ + t₀ * I)‖ ≤ ‖g (σ + t₀ * I)‖ := by
    rw [hgn, hσre, hσim, sub_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
    exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (sq_nonneg σ))
  refine hfg.trans (key.trans (le_of_eq ?_))
  have hT : 0 < 1 + |t₀| := by positivity
  have hA' : 0 ≤ A * Real.exp (l ^ 2 + α ^ 2 / 4) := mul_nonneg hA (Real.exp_pos _).le
  have hB' : 0 ≤ B * Real.exp (u ^ 2 + β ^ 2 / 4) := mul_nonneg hB (Real.exp_pos _).le
  rw [Real.mul_rpow hA' (Real.rpow_nonneg hT.le _), Real.mul_rpow hB' (Real.rpow_nonneg hT.le _),
    ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, Real.rpow_add hT]
  ring_nf

/-- **`Γ` along a horizontal segment**: `|Γ(σ + it)| ≤ |Γ(1/2 + it)|(e⁴|σ + it|)^{σ − 1/2}` for `σ ≥ 1/2`, by
the mean value inequality for `x ↦ log|Γ(x + it)|`, whose derivative `Re ψ(x + it)` is at most
`log|x + it| + 4` (`Kaiser.digamma_re_le`, from Binet's formula). -/
theorem norm_Gamma_le_half {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖Complex.Gamma (σ + t * I)‖ ≤
      ‖Complex.Gamma (1 / 2 + t * I)‖ * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by
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
  have hpos : ∀ x ∈ Icc (1 / 2 : ℝ) σ, 0 < x := fun x hx => by linarith [hx.1]
  have hcont : ContinuousOn g (Icc (1 / 2) σ) := fun x hx =>
    (hderiv x (hpos x hx)).continuousAt.continuousWithinAt
  have hint : interior (Icc (1 / 2 : ℝ) σ) = Ioo (1 / 2) σ := interior_Icc
  have hdiff : DifferentiableOn ℝ g (interior (Icc (1 / 2) σ)) := by
    rw [hint]
    exact fun x hx => (hderiv x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  have hnσ : 0 < ‖(σ : ℂ) + t * I‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hbound : ∀ x ∈ interior (Icc (1 / 2 : ℝ) σ), deriv g x ≤ Real.log ‖(σ : ℂ) + t * I‖ + 4 := by
    rw [hint]
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [(hderiv x hx0).deriv]
    have hre : 1 / 4 ≤ ((x : ℂ) + t * I).re := by simp; linarith [hx.1]
    refine (Kaiser.digamma_re_le hre).trans ?_
    have hnx : 0 < ‖(x : ℂ) + t * I‖ := by
      rw [norm_pos_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hle : ‖(x : ℂ) + t * I‖ ≤ ‖(σ : ℂ) + t * I‖ := by
      rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I]
      apply Real.sqrt_le_sqrt
      nlinarith [hx.1, hx.2]
    linarith [Real.log_le_log hnx hle]
  have hmvt := (convex_Icc (1 / 2 : ℝ) σ).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound (1 / 2)
    (left_mem_Icc.2 hσ) σ (right_mem_Icc.2 hσ) hσ
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  simp only [hg, hhalf] at hmvt
  have hG : 0 < ‖Complex.Gamma (σ + t * I)‖ := norm_pos_iff.2 (hne σ (by linarith))
  have hG2 : 0 < ‖Complex.Gamma (1 / 2 + t * I)‖ := by
    have := hne (1 / 2) (by norm_num)
    rw [hhalf] at this
    exact norm_pos_iff.2 this
  have hE : 0 < Real.exp 4 * ‖(σ : ℂ) + t * I‖ := mul_pos (Real.exp_pos 4) hnσ
  rw [Real.rpow_def_of_pos hE, Real.log_mul (Real.exp_pos 4).ne' hnσ.ne', Real.log_exp,
    ← Real.exp_log hG, ← Real.exp_log hG2, ← Real.exp_add]
  apply Real.exp_le_exp.2
  linarith

/-- **`|Γ(1/2 + it)|² = π/cosh(πt)`**, from `Γ(s)Γ(1 − s) = π/sin(πs)` and `Γ(s̄) = conj Γ(s)`. -/
theorem norm_Gamma_half_sq (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have h1 := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + t * I)
  have h2 : 1 - (1 / 2 + t * I) = (starRingEnd ℂ) (1 / 2 + t * I) := by
    apply Complex.ext <;> norm_num
  have h3 : Complex.sin (Real.pi * (1 / 2 + t * I)) = (Real.cosh (Real.pi * t) : ℂ) := by
    have e : (Real.pi : ℂ) * (1 / 2 + t * I) = Real.pi / 2 + ((Real.pi * t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
      Complex.ofReal_cosh]
    ring
  rw [h2, Complex.Gamma_conj, Complex.mul_conj, h3, Complex.normSq_eq_norm_sq] at h1
  have h4 : ((‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) =
      ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h4

/-- `|cos z| ≤ e^{|Im z|}`. -/
theorem norm_cos_le_exp (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have e1 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have h3 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  calc ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ / 2
      ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by gcongr; exact norm_add_le _ _
    _ ≤ Real.exp |z.im| := by rw [e1, e2]; linarith

/-- **`Γ` times a factor of size at most `e^{π|t|/2}`**: for `σ ≥ 1/2` and `|w| ≤ e^{π|t|/2}`,
`|Γ(σ + it)w| ≤ 3(e⁴|σ + it|)^{σ − 1/2}`, from `norm_Gamma_le_half` and `|Γ(1/2 + it)|² = π/cosh(πt)`. -/
theorem norm_Gamma_mul_le_of {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) {w : ℂ}
    (hc : ‖w‖ ≤ Real.exp (Real.pi * |t| / 2)) :
    ‖Complex.Gamma (σ + t * I) * w‖ ≤ 3 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by
  have hR : 0 ≤ (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := Real.rpow_nonneg (by positivity) _
  -- `|Γ(1/2 + it)| |w| ≤ 3`
  have hcosh : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]; linarith [Real.exp_pos (-(Real.pi * t))]
    · rw [abs_of_nonpos ht]
      have : -(Real.pi * t) = Real.pi * -t := by ring
      rw [this]; linarith [Real.exp_pos (Real.pi * t)]
  have hsq : ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
    rw [norm_Gamma_half_sq]
    have hch : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
    rw [div_le_iff₀ hch]
    have he : Real.exp (Real.pi * |t|) * Real.exp (-(Real.pi * |t|)) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 := mul_le_mul_of_nonneg_left hcosh
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)))
    have h6 : 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 2) = Real.pi := by
      rw [show 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 2)
        = Real.pi * (Real.exp (Real.pi * |t|) * Real.exp (-(Real.pi * |t|))) by ring, he, mul_one]
    linarith
  have hprod : ‖Complex.Gamma (1 / 2 + t * I)‖ * ‖w‖ ≤ 3 := by
    have h0 : 0 ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * ‖w‖ := by positivity
    have hsq2 : (‖Complex.Gamma (1 / 2 + t * I)‖ * ‖w‖) ^ 2 ≤ 9 := by
      have hc2 : ‖w‖ ^ 2 ≤ Real.exp (Real.pi * |t|) := by
        have : Real.exp (Real.pi * |t| / 2) ^ 2 = Real.exp (Real.pi * |t|) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [← this]
        exact pow_le_pow_left₀ (norm_nonneg _) hc 2
      have he : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
        rw [← Real.exp_add]; simp
      calc (‖Complex.Gamma (1 / 2 + t * I)‖ * ‖w‖) ^ 2
          = ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) := by
            gcongr
        _ = 2 * Real.pi := by rw [mul_assoc, he, mul_one]
        _ ≤ 9 := by linarith [Real.pi_lt_d2]
    nlinarith
  rw [norm_mul]
  calc ‖Complex.Gamma (σ + t * I)‖ * ‖w‖
      ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) * ‖w‖ := by
        gcongr; exact norm_Gamma_le_half hσ t
    _ = (‖Complex.Gamma (1 / 2 + t * I)‖ * ‖w‖) * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by
        ring
    _ ≤ 3 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by gcongr

/-- **The factor of the functional equation on a vertical line**:
`|Γ(σ + it)cos(π(σ + it)/2)| ≤ 3(e⁴|σ + it|)^{σ − 1/2}` for `σ ≥ 1/2`. -/
theorem norm_Gamma_mul_cos_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖Complex.Gamma (σ + t * I) * Complex.cos (Real.pi * (σ + t * I) / 2)‖ ≤
      3 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := by
  refine norm_Gamma_mul_le_of hσ t ((norm_cos_le_exp _).trans (le_of_eq ?_))
  congr 1
  have : ((Real.pi : ℂ) * (σ + t * I) / 2).im = Real.pi * t / 2 := by simp
  rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/-- **The left line from the right one**: for `1/2 ≤ σ < 1`,
`|ζ(1 − σ − it)| ≤ 6(e⁴|σ + it|)^{σ − 1/2}|ζ(σ + it)|` (Mathlib's functional equation `riemannZeta_one_sub`,
with `|(2π)^{−s}| ≤ 1`). -/
theorem norm_zeta_one_sub_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (t : ℝ) :
    ‖riemannZeta (1 - (σ + t * I))‖ ≤
      6 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) * ‖riemannZeta (σ + t * I)‖ := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hpole : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith
  rw [riemannZeta_one_sub hpole hs1]
  have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ ≤ 1 := by
    have e : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, hsre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hR : 0 ≤ (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) := Real.rpow_nonneg (by positivity) _
  calc ‖2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2) * riemannZeta s‖
      = 2 * ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ * ‖Complex.Gamma s * Complex.cos (Real.pi * s / 2)‖ *
          ‖riemannZeta s‖ := by
        rw [show (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2) *
          riemannZeta s = 2 * (2 * (Real.pi : ℂ)) ^ (-s) * (Complex.Gamma s * Complex.cos (Real.pi * s / 2)) *
          riemannZeta s by ring]
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_two]
    _ ≤ 2 * 1 * (3 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2)) * ‖riemannZeta s‖ := by
        gcongr
        exact norm_Gamma_mul_cos_le hσ t
    _ = 6 * (Real.exp 4 * ‖(σ : ℂ) + t * I‖) ^ (σ - 1 / 2) * ‖riemannZeta s‖ := by ring

/-- **Subconvexity from a zero-free half-plane.** If `ζ(s) ≠ 0` on `Re s > θ`, `1/2 ≤ θ < 1`, then for
`1 − θ ≤ σ ≤ θ` and `ε > 0` there is `C` with `|ζ(σ + it)| ≤ C|t|^{(θ − σ)/2 + ε}` for `|t| ≥ 2`. The proof takes
round 470's Lindelöf bound on `Re s = θ'`, `θ' = θ + δ`, carries it to `Re s = 1 − θ'` with the exponent
`θ' − 1/2` by the functional equation, and interpolates between the two lines. -/
theorem zeta_strip_of_zeroFree {θ σ ε : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ1 : 1 - θ ≤ σ) (hσ2 : σ ≤ θ)
    (hε : 0 < ε) (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ((θ - σ) / 2 + ε) := by
  -- the two lines `Re s = l` and `Re s = u`
  obtain ⟨δ, hδ0, hδε, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ (1 - θ) / 2 :=
    ⟨min ε ((1 - θ) / 2), lt_min hε (by linarith), min_le_left _ _, min_le_right _ _⟩
  set u : ℝ := θ + δ with hu
  set l : ℝ := 1 - u with hl
  have hu1 : u < 1 := by linarith
  have hl0 : 0 < l := by linarith
  have hlu : l < u := by linarith
  have hε' : 0 < ε / 2 := by positivity
  -- round 470 on `Re s ≥ u`
  obtain ⟨T, C₀, hL⟩ := HalfPlaneLindelof.zeta_bound_of_zeroFree (by linarith) hθ1
    (by linarith : θ < u) hε' hzf
  -- polynomial growth in the strip `l ≤ Re s ≤ u`
  set K : ℝ := 1 / 2 + 1 / (1 - u) + 1 / l with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ 1 / (1 - u) := one_div_nonneg.2 (by linarith)
    have h2 : 0 ≤ 1 / l := one_div_nonneg.2 hl0.le
    linarith
  have hgr : ∀ z : ℂ, z.re ∈ Icc l u → ‖riemannZeta z‖ ≤ K * (1 + |z.im|) ^ (1 : ℝ) := by
    intro z hz
    rw [Real.rpow_one]
    have hz0 : 0 < z.re := hl0.trans_le hz.1
    have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at hz; linarith [hz.2]
    refine (HalfPlanePNT.norm_riemannZeta_le_of_re_pos hz0 hz1).trans ?_
    have h1 : 1 / ‖1 - z‖ ≤ 1 / (1 - u) := by
      have hre : 1 - u ≤ ‖1 - z‖ := by
        have := Complex.re_le_norm (1 - z)
        rw [Complex.sub_re, Complex.one_re] at this
        linarith [hz.2]
      exact one_div_le_one_div_of_le (by linarith) hre
    have h2 : ‖z‖ / z.re ≤ (1 + |z.im|) / l := by
      have hn : ‖z‖ ≤ 1 + |z.im| := by
        have := Complex.norm_le_abs_re_add_abs_im z
        rw [abs_of_pos hz0] at this
        linarith [hz.2]
      calc ‖z‖ / z.re ≤ (1 + |z.im|) / z.re := by gcongr
        _ ≤ (1 + |z.im|) / l := by gcongr; exact hz.1
    have hy : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    have hc : 0 ≤ 1 / (1 - u) := one_div_nonneg.2 (by linarith)
    calc 1 / 2 + 1 / ‖1 - z‖ + ‖z‖ / z.re ≤ 1 / 2 + 1 / (1 - u) + (1 + |z.im|) / l := by linarith
      _ ≤ (1 / 2 + 1 / (1 - u)) * (1 + |z.im|) + (1 + |z.im|) / l := by
          have := mul_le_mul_of_nonneg_left hy (by linarith : (0 : ℝ) ≤ 1 / 2 + 1 / (1 - u))
          linarith
      _ = K * (1 + |z.im|) := by rw [hK]; ring
  -- the right line: `|ζ(u + it)| ≤ B(1 + |t|)^{ε/2}`
  set B : ℝ := max (max C₀ 0) (K * (1 + |T|)) with hB
  have hB0 : 0 ≤ B := (le_max_right C₀ 0).trans (le_max_left _ _)
  have hright : ∀ t : ℝ, ‖riemannZeta (u + t * I)‖ ≤ B * (1 + |t|) ^ (ε / 2) := by
    intro t
    have hT1 : (1 : ℝ) ≤ (1 + |t|) ^ (ε / 2) :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) hε'.le
    rcases le_or_gt T |t| with ht | ht
    · have h := (hL u t le_rfl ht).1
      calc ‖riemannZeta (u + t * I)‖ ≤ C₀ * |t| ^ (ε / 2) := h
        _ ≤ max C₀ 0 * |t| ^ (ε / 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
        _ ≤ max C₀ 0 * (1 + |t|) ^ (ε / 2) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hε'.le)
              (le_max_right _ _)
        _ ≤ B * (1 + |t|) ^ (ε / 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    · have hre : ((u : ℂ) + t * I).re ∈ Icc l u := by
        rw [show ((u : ℂ) + t * I).re = u by simp]
        exact ⟨hlu.le, le_rfl⟩
      have h := hgr _ hre
      have him : ((u : ℂ) + t * I).im = t := by simp
      rw [him, Real.rpow_one] at h
      calc ‖riemannZeta (u + t * I)‖ ≤ K * (1 + |t|) := h
        _ ≤ K * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self T]) hK0
        _ ≤ B := le_max_right _ _
        _ ≤ B * (1 + |t|) ^ (ε / 2) := le_mul_of_one_le_right hB0 hT1
  -- the left line: `|ζ(l + it)| ≤ A(1 + |t|)^{u − 1/2 + ε/2}`
  set A : ℝ := 6 * Real.exp (4 * (u - 1 / 2)) * B with hA
  have hleft : ∀ t : ℝ, ‖riemannZeta (l + t * I)‖ ≤ A * (1 + |t|) ^ (u - 1 / 2 + ε / 2) := by
    intro t
    have e : (l : ℂ) + t * I = 1 - ((u : ℂ) + (-t : ℝ) * I) := by rw [hl]; push_cast; ring
    rw [e]
    refine (norm_zeta_one_sub_le (by linarith) hu1 (-t)).trans ?_
    have hn : ‖(u : ℂ) + (-t : ℝ) * I‖ ≤ 1 + |t| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < u)]
      linarith
    have hpow : (Real.exp 4 * ‖(u : ℂ) + (-t : ℝ) * I‖) ^ (u - 1 / 2) ≤
        Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2) := by
      calc (Real.exp 4 * ‖(u : ℂ) + (-t : ℝ) * I‖) ^ (u - 1 / 2)
          ≤ (Real.exp 4 * (1 + |t|)) ^ (u - 1 / 2) :=
            Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hn (Real.exp_pos 4).le)
              (by linarith)
        _ = Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2) := by
            rw [Real.mul_rpow (Real.exp_pos 4).le (by positivity), ← Real.exp_mul]
    have hr := hright (-t)
    rw [abs_neg] at hr
    calc 6 * (Real.exp 4 * ‖(u : ℂ) + (-t : ℝ) * I‖) ^ (u - 1 / 2) * ‖riemannZeta (u + (-t : ℝ) * I)‖
        ≤ 6 * (Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2)) * (B * (1 + |t|) ^ (ε / 2)) := by
          gcongr
      _ = A * ((1 + |t|) ^ (u - 1 / 2) * (1 + |t|) ^ (ε / 2)) := by rw [hA]; ring
      _ = A * (1 + |t|) ^ (u - 1 / 2 + ε / 2) := by
          rw [← Real.rpow_add (by positivity)]
  -- interpolate
  have hdiff : DifferentiableOn ℂ riemannZeta (re ⁻¹' Icc l u) := fun z hz =>
    (differentiableAt_riemannZeta (fun h => by
      have : z.re ∈ Icc l u := hz
      rw [h, Complex.one_re] at this
      linarith [this.2])).differentiableWithinAt
  have hσ : σ ∈ Icc l u := ⟨by linarith, by linarith⟩
  set D : ℝ := (A * Real.exp (l ^ 2 + (u - 1 / 2 + ε / 2) ^ 2 / 4)) ^ (1 - (σ - l) / (u - l)) *
      (B * Real.exp (u ^ 2 + (ε / 2) ^ 2 / 4)) ^ ((σ - l) / (u - l)) with hD
  have hD0 : 0 ≤ D := by
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hexp : (1 - (σ - l) / (u - l)) * (u - 1 / 2 + ε / 2) + (σ - l) / (u - l) * (ε / 2) =
      (u - σ) / 2 + ε / 2 := by
    have hul : u - l ≠ 0 := by linarith
    have hl' : l = 1 - u := hl
    field_simp
    rw [hl']
    ring
  have he : 0 ≤ (θ - σ) / 2 + ε := by linarith
  refine ⟨D * 2 ^ ((θ - σ) / 2 + ε), fun t ht => ?_⟩
  have key := norm_le_interp_strip hlu (by linarith) hε'.le zero_le_one hdiff hleft hright hgr hσ t
  rw [hexp] at key
  have ht1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc ‖riemannZeta (σ + t * I)‖ ≤ D * (1 + |t|) ^ ((u - σ) / 2 + ε / 2) := key
    _ ≤ D * (1 + |t|) ^ ((θ - σ) / 2 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hD0
    _ ≤ D * (2 * |t|) ^ ((θ - σ) / 2 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) he) hD0
    _ = D * 2 ^ ((θ - σ) / 2 + ε) * |t| ^ ((θ - σ) / 2 + ε) := by
        rw [Real.mul_rpow (by norm_num) (abs_nonneg t)]; ring

/-- **On the strip `1/12 ≤ σ ≤ 11/12`, with no hypothesis**: `|ζ(σ + it)| = O(|t|^{(11/12 − σ)/2 + ε})`, from
round 466's half-plane. -/
theorem zeta_strip_eleven_twelfths {σ ε : ℝ} (hσ1 : 1 / 12 ≤ σ) (hσ2 : σ ≤ 11 / 12) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ ((11 / 12 - σ) / 2 + ε) :=
  zeta_strip_of_zeroFree (by norm_num) (by norm_num) (by linarith) hσ2 hε
    (fun _ hs => (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1)

/-- **On the critical line**: if `ζ(s) ≠ 0` on `Re s > θ`, `1/2 ≤ θ < 1`, then
`CrossCriteria.ZetaCritBound ((2θ − 1)/4 + ε)` for every `ε > 0`. -/
theorem zetaCritBound_of_zeroFree {θ ε : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    CrossCriteria.ZetaCritBound ((2 * θ - 1) / 4 + ε) := by
  obtain ⟨C, hC⟩ := zeta_strip_of_zeroFree (σ := 1 / 2) hθ hθ1 (by linarith) hθ hε hzf
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  have e : (θ - 1 / 2) / 2 + ε = (2 * θ - 1) / 4 + ε := by ring
  have hc : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rwa [e, hc] at h

/-- `ZetaCritBound` is monotone in the exponent. -/
theorem zetaCritBound_mono {c c' : ℝ} (hcc : c ≤ c') (h : CrossCriteria.ZetaCritBound c) :
    CrossCriteria.ZetaCritBound c' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun t ht => (hC t ht).trans ?_⟩
  have h1 : (1 : ℝ) ≤ |t| := by linarith
  calc C * |t| ^ c ≤ max C 0 * |t| ^ c :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ max C 0 * |t| ^ c' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hcc) (le_max_right _ _)

/-- **Subconvexity on the critical line, with no hypothesis**: `|ζ(1/2 + it)| = O(|t|^{5/24 + ε})`, from
round 466's half-plane `Re s > 11/12`. -/
theorem zetaCritBound_five_24 {ε : ℝ} (hε : 0 < ε) : CrossCriteria.ZetaCritBound (5 / 24 + ε) := by
  have h := zetaCritBound_of_zeroFree (θ := 11 / 12) (by norm_num) (by norm_num) hε
    (fun _ hs => (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1)
  have e : (2 * (11 / 12 : ℝ) - 1) / 4 + ε = 5 / 24 + ε := by ring
  rwa [e] at h

/-- **The convexity bound**, `CrossCriteria.ConvexityBound`: `5/24 + ε ≤ 1/4 + ε`. -/
theorem convexityBound : CrossCriteria.ConvexityBound := fun _ hε =>
  zetaCritBound_mono (by linarith) (zetaCritBound_five_24 hε)

/-- At round 469's `Θ`, the supremum of the real parts of the nontrivial zeros:
`ZetaCritBound ((2Θ − 1)/4 + ε)`. -/
theorem zetaCritBound_Theta {ε : ℝ} (hε : 0 < ε) :
    CrossCriteria.ZetaCritBound ((2 * PsiExponent.Theta - 1) / 4 + ε) :=
  zetaCritBound_of_zeroFree PsiExponent.half_le_Theta (by linarith [PsiExponent.Theta_le]) hε
    (fun _ hs => PsiExponent.zeta_ne_zero_of_Theta_lt hs)

/-- **RH implies Lindelöf**: the case `θ = 1/2`. -/
theorem lindelof_of_RH (hRH : RiemannHypothesis) : CrossCriteria.Lindelof := by
  intro ε hε
  have hzf : ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
    intro s hs h0
    rcases le_or_gt 1 s.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1 h0
    · have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
        rintro ⟨n, rfl⟩
        have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
        rw [this] at hs
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hs1 : s ≠ 1 := by
        rintro rfl
        simp at h1
      have := hRH s h0 htriv hs1
      linarith
  have h := zetaCritBound_of_zeroFree (θ := 1 / 2) le_rfl (by norm_num) hε hzf
  have e : (2 * (1 / 2 : ℝ) - 1) / 4 + ε = ε := by ring
  rwa [e] at h

end Subconvexity

#print axioms Subconvexity.norm_le_interp_strip
#print axioms Subconvexity.norm_Gamma_le_half
#print axioms Subconvexity.norm_Gamma_half_sq
#print axioms Subconvexity.norm_Gamma_mul_le_of
#print axioms Subconvexity.norm_Gamma_mul_cos_le
#print axioms Subconvexity.norm_zeta_one_sub_le
#print axioms Subconvexity.zeta_strip_of_zeroFree
#print axioms Subconvexity.zeta_strip_eleven_twelfths
#print axioms Subconvexity.zetaCritBound_of_zeroFree
#print axioms Subconvexity.zetaCritBound_five_24
#print axioms Subconvexity.convexityBound
#print axioms Subconvexity.zetaCritBound_Theta
#print axioms Subconvexity.lindelof_of_RH
