import Mathlib

/-! # Gaussians and Gaussian chirps in the plane (round 296)

The Gaussian `e^{-πa|z|²}` on `ℂ` as a Schwartz function, Gaussian chirps `e^{2πi q(z)}e^{-πa|z|²}`,
and the Fourier transform of the chirps with a quadratic phase `q(z) = Re(wz²)`. They feed round 297's
evaluation of the quadratic Gauss sums of `ℤ[ω]` by Poisson summation (the companion paper's
Appendix A.1). Mathlib has the one-variable Gaussian Fourier transform (`fourier_gaussian_pi`) but no
Gaussian as a Schwartz function.

* **The Gaussian is Schwartz** (`gaussR`, `gaussC`). `norm_iteratedFDeriv_gauss_le`:
  `‖Dⁿ e^{-πa|z|²}‖ ≤ n!·e^{-πa|z|²}·(2(1 + πa)(1 + |z|)²)ⁿ`, from Mathlib's Faà di Bruno bound
  (`norm_iteratedFDeriv_comp_le`) with `‖Dⁱ|z|²‖ ≤ 2ⁱ(1 + |z|)²` (`norm_iteratedFDeriv_normSq_le`,
  through the bilinear bound for the inner product). The decay `(1 + t)ᵐe^{-bt²} ≤ C`
  (`one_add_pow_mul_exp_le`) uses `xᴺ/N! ≤ eˣ`.
* **Chirps** (`chirp`, `chirp_apply`): `e^{2πi q(z)}·e^{-πa|z|²}` for a real phase `q` of temperate
  growth, through Mathlib's `smulLeftCLM` and `Complex.hasTemperateGrowth_exp_mul_I`.
* **Product Gaussians** (`fourier_prod_gauss`):
  `𝓕[e^{-πb₁x²}e^{-πb₂y²}](ξ) = b₁^{-1/2}e^{-πξ₁²/b₁}·b₂^{-1/2}e^{-πξ₂²/b₂}` for `Re b₁, Re b₂ > 0`,
  through `ℂ ≃ ℝ × ℝ` and Fubini.
* **`fourier_chirp`**: for `F(z) = e^{2πi Re(wz²)}e^{-πη|z|²}`,
  `𝓕F(ξ) = (η² + 4|w|²)^{-1/2}·exp(-π(η|ξ|² + 2i Re(wξ²))/(η² + 4|w|²))`. The rotation
  `r = e^{-i·arg(w)/2}` makes `r²w = |w|` (`rot_sq_mul`), so `F(ru)` is the product Gaussian with
  `b = η ∓ 2i|w|` (`chirp_rot`), and Mathlib's `fourier_comp_linearIsometry` moves the rotation to the
  frequency; `b^{1/2}·b̄^{1/2} = |b|` (`cpow_half_mul_conj`).
-/

open Complex Real Nat MeasureTheory
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

noncomputable section

namespace PlaneGaussian

/-- `‖Dʲ id (z)‖ ≤ 1 + ‖z‖`: it is `‖z‖`, at most `1`, then `0`. -/
theorem norm_iteratedFDeriv_id_le (j : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ j (id : ℂ → ℂ) z‖ ≤ 1 + ‖z‖ := by
  rcases j with _ | _ | j
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [norm_iteratedFDeriv_one, fderiv_id]
    exact ContinuousLinearMap.norm_id_le.trans (by linarith [norm_nonneg z])
  · rw [← norm_iteratedFDeriv_fderiv]
    have h : fderiv ℝ (id : ℂ → ℂ) = fun _ => ContinuousLinearMap.id ℝ ℂ :=
      funext fun _ => fderiv_id
    rw [h, iteratedFDeriv_succ_const]
    simp only [Pi.zero_apply, norm_zero]
    positivity

/-- `‖Dⁱ(‖z‖²)‖ ≤ 2ⁱ(1 + ‖z‖)²`. -/
theorem norm_iteratedFDeriv_normSq_le (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i (fun z : ℂ => ‖z‖ ^ 2) z‖ ≤ 2 ^ i * (1 + ‖z‖) ^ 2 := by
  have h : (fun z : ℂ => ‖z‖ ^ 2) = fun z => innerSL ℝ (id z) (id z) := by
    funext z; simp
  rw [h]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one (innerSL ℝ)
    contDiff_id contDiff_id z (n := i) (N := ⊤) le_top (norm_innerSL_le ℝ)).trans ?_
  calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j id z‖ *
        ‖iteratedFDeriv ℝ (i - j) id z‖
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (1 + ‖z‖) * (1 + ‖z‖) := by
        gcongr with j hj
        · exact norm_iteratedFDeriv_id_le j z
        · exact norm_iteratedFDeriv_id_le (i - j) z
    _ = 2 ^ i * (1 + ‖z‖) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        rw [this]; ring

/-- `(1 + t)ᵐ e^{-bt²}` is bounded on `t ≥ 0`. -/
theorem one_add_pow_mul_exp_le (m : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ m * Real.exp (-b * t ^ 2) ≤ C := by
  refine ⟨2 ^ m * max 1 (m ! / b ^ m), fun t ht => ?_⟩
  have hexp : Real.exp (-b * t ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  rcases le_or_gt t 1 with h1 | h1
  · calc (1 + t) ^ m * Real.exp (-b * t ^ 2) ≤ 2 ^ m * 1 := by
          gcongr
          · linarith
    _ ≤ 2 ^ m * max 1 (m ! / b ^ m) := by gcongr; exact le_max_left _ _
  · have ht0 : 0 < t := by linarith
    have hpow : (b * t ^ 2) ^ m / m ! ≤ Real.exp (b * t ^ 2) :=
      Real.pow_div_factorial_le_exp (b * t ^ 2) (by positivity) m
    have hfac : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    have hE : Real.exp (-b * t ^ 2) * (b * t ^ 2) ^ m ≤ m ! := by
      rw [neg_mul, Real.exp_neg]
      rw [div_le_iff₀ hfac] at hpow
      have hpos := Real.exp_pos (b * t ^ 2)
      rw [inv_mul_le_iff₀ hpos]
      linarith
    have h2 : (1 + t) ^ m ≤ 2 ^ m * t ^ m := by
      rw [← mul_pow]; gcongr; linarith
    have htm : 1 ≤ t ^ m := one_le_pow₀ h1.le
    calc (1 + t) ^ m * Real.exp (-b * t ^ 2) ≤ 2 ^ m * t ^ m * Real.exp (-b * t ^ 2) := by
          gcongr
      _ ≤ 2 ^ m * (t ^ m * t ^ m) * Real.exp (-b * t ^ 2) := by
          gcongr
          nlinarith
      _ = 2 ^ m * (Real.exp (-b * t ^ 2) * (b * t ^ 2) ^ m) / b ^ m := by
          field_simp
          ring
      _ ≤ 2 ^ m * m ! / b ^ m := by gcongr
      _ ≤ 2 ^ m * max 1 (m ! / b ^ m) := by
          rw [mul_div_assoc]; gcongr; exact le_max_right _ _

/-- Derivative bound for the Gaussian: `‖Dⁿ exp(-πa‖z‖²)‖ ≤ n!·exp(-πa‖z‖²)·(2(1 + πa)(1 + ‖z‖)²)ⁿ`. -/
theorem norm_iteratedFDeriv_gauss_le {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n (fun z : ℂ => Real.exp (-(π * a) * ‖z‖ ^ 2)) z‖ ≤
      n ! * Real.exp (-(π * a) * ‖z‖ ^ 2) * (2 * (1 + π * a) * (1 + ‖z‖) ^ 2) ^ n := by
  have hf : ContDiff ℝ ⊤ (fun z : ℂ => -(π * a) * ‖z‖ ^ 2) := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hcomp : (fun z : ℂ => Real.exp (-(π * a) * ‖z‖ ^ 2)) =
      Real.exp ∘ (fun z : ℂ => -(π * a) * ‖z‖ ^ 2) := rfl
  rw [hcomp]
  refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hf le_top z (fun i _ => ?_)
    (fun i hi1 _ => ?_)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · have hsmul : (fun z : ℂ => -(π * a) * ‖z‖ ^ 2) = (-(π * a)) • (fun z : ℂ => ‖z‖ ^ 2) := by
      funext z; simp [smul_eq_mul]
    rw [hsmul, iteratedFDeriv_const_smul_apply (contDiff_norm_sq ℝ).contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : 0 < π * a)]
    have hi : i ≠ 0 := by omega
    have h1 : 1 ≤ 1 + π * a := by linarith [mul_pos Real.pi_pos ha]
    have h2 : 1 ≤ (1 + ‖z‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg z])
    calc π * a * ‖iteratedFDeriv ℝ i (fun z : ℂ => ‖z‖ ^ 2) z‖
        ≤ π * a * (2 ^ i * (1 + ‖z‖) ^ 2) := by
          gcongr; exact norm_iteratedFDeriv_normSq_le i z
      _ ≤ (1 + π * a) * (2 ^ i * (1 + ‖z‖) ^ 2) := by gcongr; linarith
      _ ≤ (1 + π * a) ^ i * (2 ^ i * ((1 + ‖z‖) ^ 2) ^ i) := by
          gcongr
          · exact le_self_pow₀ h1 hi
          · exact le_self_pow₀ h2 hi
      _ = (2 * (1 + π * a) * (1 + ‖z‖) ^ 2) ^ i := by rw [mul_pow, mul_pow]; ring

theorem gauss_decay {a : ℝ} (ha : 0 < a) (k n : ℕ) : ∃ C, ∀ z : ℂ,
    ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun z : ℂ => Real.exp (-(π * a) * ‖z‖ ^ 2)) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := one_add_pow_mul_exp_le (k + 2 * n) (by positivity : 0 < π * a)
  refine ⟨n ! * (2 * (1 + π * a)) ^ n * C, fun z => ?_⟩
  have h1 := norm_iteratedFDeriv_gauss_le ha n z
  have h2 := hC ‖z‖ (norm_nonneg z)
  calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun z : ℂ => Real.exp (-(π * a) * ‖z‖ ^ 2)) z‖
      ≤ (1 + ‖z‖) ^ k *
          (n ! * Real.exp (-(π * a) * ‖z‖ ^ 2) * (2 * (1 + π * a) * (1 + ‖z‖) ^ 2) ^ n) := by
        gcongr; linarith [norm_nonneg z]
    _ = n ! * (2 * (1 + π * a)) ^ n *
          ((1 + ‖z‖) ^ (k + 2 * n) * Real.exp (-(π * a) * ‖z‖ ^ 2)) := by
        rw [mul_pow (2 * (1 + π * a)) ((1 + ‖z‖) ^ 2) n, ← pow_mul, pow_add]; ring
    _ ≤ n ! * (2 * (1 + π * a)) ^ n * C := by gcongr

/-- The Gaussian `z ↦ exp(-πa‖z‖²)` as a Schwartz function on `ℂ`. -/
def gaussR (a : ℝ) (ha : 0 < a) : SchwartzMap ℂ ℝ where
  toFun z := Real.exp (-(π * a) * ‖z‖ ^ 2)
  smooth' := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  decay' k n := gauss_decay ha k n

/-- The Gaussian with complex values. -/
def gaussC (a : ℝ) (ha : 0 < a) : SchwartzMap ℂ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM (gaussR a ha)

theorem gaussC_apply (a : ℝ) (ha : 0 < a) (z : ℂ) :
    gaussC a ha z = (Real.exp (-(π * a) * ‖z‖ ^ 2) : ℂ) := rfl

/-- **A Gaussian chirp** `z ↦ e^{2πi q(z)}·exp(-πa‖z‖²)`, for a real phase `q`. -/
def chirp (q : ℂ → ℝ) (a : ℝ) (ha : 0 < a) : SchwartzMap ℂ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z => Complex.exp (↑(2 * π * q z) * I)) (gaussC a ha)

theorem chirp_apply {q : ℂ → ℝ} (hq : q.HasTemperateGrowth) (a : ℝ) (ha : 0 < a) (z : ℂ) :
    chirp q a ha z =
      Complex.exp (↑(2 * π * q z) * I) * (Real.exp (-(π * a) * ‖z‖ ^ 2) : ℂ) := by
  have ht : (fun z => Complex.exp (↑(2 * π * q z) * I)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const (2 * π)).mul hq)
  rw [chirp, SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul, gaussC_apply]

/-- **The Fourier transform of a product of one-variable Gaussians** in the coordinates of `ℂ`:
`𝓕[e^{-πb₁x²}e^{-πb₂y²}](ξ) = b₁^{-1/2}e^{-πξ₁²/b₁}·b₂^{-1/2}e^{-πξ₂²/b₂}`. -/
theorem fourier_prod_gauss {b₁ b₂ : ℂ} (h₁ : 0 < b₁.re) (h₂ : 0 < b₂.re) (ξ : ℂ) :
    𝓕 (fun u : ℂ => cexp (-π * b₁ * u.re ^ 2) * cexp (-π * b₂ * u.im ^ 2)) ξ =
      (1 / b₁ ^ (1 / 2 : ℂ) * cexp (-π / b₁ * ξ.re ^ 2)) *
        (1 / b₂ ^ (1 / 2 : ℂ) * cexp (-π / b₂ * ξ.im ^ 2)) := by
  have g1 := congrFun (fourier_gaussian_pi h₁) ξ.re
  have g2 := congrFun (fourier_gaussian_pi h₂) ξ.im
  rw [Real.fourier_real_eq] at g1 g2
  rw [← g1, ← g2, Real.fourier_eq]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding]
  rw [Measure.volume_eq_prod, ← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hin : ⟪measurableEquivRealProd.symm p, ξ⟫ = p.1 * ξ.re + p.2 * ξ.im := by
    rw [measurableEquivRealProd_symm_apply, Complex.inner]
    simp; ring
  have he : 𝐞 (-(p.1 * ξ.re + p.2 * ξ.im)) = 𝐞 (-(p.1 * ξ.re)) * 𝐞 (-(p.2 * ξ.im)) := by
    rw [← AddChar.map_add_eq_mul, neg_add]
  dsimp only
  rw [hin, he, measurableEquivRealProd_symm_apply]
  simp only [Circle.smul_def, smul_eq_mul, Circle.coe_mul]
  ring

/-- The phase `z ↦ Re(w z²)` has temperate growth. -/
theorem quadPhase_temperate (w : ℂ) : (fun z : ℂ => (w * z ^ 2).re).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_re.comp
    ((Function.HasTemperateGrowth.const w).mul (Function.HasTemperateGrowth.id'.pow 2))

/-- The rotation `r = e^{-i·arg(w)/2}`, with `r²w = |w|`. -/
def rot (w : ℂ) : Circle := Circle.exp (-(arg w) / 2)

theorem rot_sq_mul (w : ℂ) : ((rot w : ℂ)) ^ 2 * w = (‖w‖ : ℂ) := by
  have hw := norm_mul_exp_arg_mul_I w
  rw [rot, Circle.coe_exp]
  calc cexp (↑(-arg w / 2) * I) ^ 2 * w
      = cexp (↑(-arg w / 2) * I) ^ 2 * (‖w‖ * cexp (↑(arg w) * I)) := by rw [hw]
    _ = ‖w‖ * (cexp (↑(-arg w / 2) * I) ^ 2 * cexp (↑(arg w) * I)) := by ring
    _ = ‖w‖ := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        have : (((2 : ℕ) : ℂ) * (↑(-arg w / 2) * I) + ↑(arg w) * I) = 0 := by push_cast; ring
        rw [this, Complex.exp_zero, mul_one]

/-- The product Gaussian `e^{-πb₁x²}e^{-πb₂y²}`, `u = x + iy`. -/
def pgauss (b₁ b₂ : ℂ) (u : ℂ) : ℂ := cexp (-π * b₁ * u.re ^ 2) * cexp (-π * b₂ * u.im ^ 2)

/-- `chirp(r·u)` is the product Gaussian with `b = η ∓ 2i|w|`. -/
theorem chirp_rot (w : ℂ) (η : ℝ) (hη : 0 < η) (u : ℂ) :
    chirp (fun z => (w * z ^ 2).re) η hη ((rot w : ℂ) * u) =
      pgauss (η - 2 * ‖w‖ * I) (η + 2 * ‖w‖ * I) u := by
  rw [chirp_apply (quadPhase_temperate w)]
  have h1 : (w * ((rot w : ℂ) * u) ^ 2).re = ‖w‖ * (u.re ^ 2 - u.im ^ 2) := by
    rw [mul_pow, ← mul_assoc, mul_comm w, rot_sq_mul]
    simp [sq]
  have h2 : ‖(rot w : ℂ) * u‖ = ‖u‖ := by simp
  have hn : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h1, h2, hn, Complex.ofReal_exp, ← Complex.exp_add, pgauss, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem chirp_eq_comp (w : ℂ) (η : ℝ) (hη : 0 < η) :
    (chirp (fun z => (w * z ^ 2).re) η hη : ℂ → ℂ) =
      pgauss (η - 2 * ‖w‖ * I) (η + 2 * ‖w‖ * I) ∘ rotation (rot w)⁻¹ := by
  funext z
  simp only [Function.comp_apply, rotation_apply]
  rw [← chirp_rot w η hη]
  congr 1
  rw [← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul]

/-- `𝓕(chirp)(ξ) = 𝓕(product Gaussian)(r⁻¹ξ)`. -/
theorem fourier_chirp_rot (w : ℂ) (η : ℝ) (hη : 0 < η) (ξ : ℂ) :
    𝓕 (chirp (fun z => (w * z ^ 2).re) η hη : ℂ → ℂ) ξ =
      𝓕 (pgauss (η - 2 * ‖w‖ * I) (η + 2 * ‖w‖ * I)) (((rot w)⁻¹ : Circle) * ξ) := by
  rw [chirp_eq_comp, Real.fourier_comp_linearIsometry, rotation_apply]

/-- `b^{1/2}·(b̄)^{1/2} = |b|` for `Re b > 0`. -/
theorem cpow_half_mul_conj {b : ℂ} (hb : 0 < b.re) :
    b ^ (1 / 2 : ℂ) * (conj b) ^ (1 / 2 : ℂ) = (‖b‖ : ℂ) := by
  have harg : b.arg ≠ π := by
    intro h; rw [arg_eq_pi_iff] at h; linarith [h.1]
  have hc := cpow_conj b (1 / 2) harg
  have hc2 : conj (2 : ℂ) = 2 := by apply Complex.ext <;> simp
  have h12 : conj (1 / 2 : ℂ) = 1 / 2 := by simp [hc2]
  rw [h12] at hc
  rw [hc, conj_mul']
  have h' : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h', norm_cpow_real, Complex.norm_conj, ← Complex.ofReal_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg b)]
  norm_num

/-- `|w|·(r⁻¹)² = w`. -/
theorem norm_mul_rot_inv_sq (w : ℂ) :
    (‖w‖ : ℂ) * ((((rot w)⁻¹ : Circle) : ℂ)) ^ 2 = w := by
  rw [← rot_sq_mul w]
  have h : ((rot w : ℂ)) * (((rot w)⁻¹ : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  linear_combination w * ((rot w : ℂ) * (((rot w)⁻¹ : Circle) : ℂ) + 1) * h

/-- **The Fourier transform of a Gaussian chirp**: for `F(z) = e^{2πi Re(wz²)} e^{-πη|z|²}`,
`𝓕F(ξ) = (η² + 4|w|²)^{-1/2}·exp(-π(η|ξ|² + 2i Re(wξ²))/(η² + 4|w|²))`. -/
theorem fourier_chirp (w : ℂ) (η : ℝ) (hη : 0 < η) (ξ : ℂ) :
    𝓕 (chirp (fun z => (w * z ^ 2).re) η hη : ℂ → ℂ) ξ =
      ((Real.sqrt (η ^ 2 + 4 * ‖w‖ ^ 2) : ℝ) : ℂ)⁻¹ *
        cexp (-(π : ℂ) * (((η * ‖ξ‖ ^ 2 : ℝ) : ℂ) + 2 * I * (((w * ξ ^ 2).re : ℝ) : ℂ)) /
          ((η ^ 2 + 4 * ‖w‖ ^ 2 : ℝ) : ℂ)) := by
  set A : ℝ := ‖w‖ with hA
  have h₁ : 0 < ((η : ℂ) - 2 * A * I).re := by simp [hη]
  have h₂ : 0 < ((η : ℂ) + 2 * A * I).re := by simp [hη]
  rw [fourier_chirp_rot]
  have hp : pgauss ((η : ℂ) - 2 * ‖w‖ * I) ((η : ℂ) + 2 * ‖w‖ * I) =
      fun u => cexp (-π * ((η : ℂ) - 2 * A * I) * u.re ^ 2) *
        cexp (-π * ((η : ℂ) + 2 * A * I) * u.im ^ 2) := rfl
  rw [hp, fourier_prod_gauss h₁ h₂]
  set ξ' : ℂ := (((rot w)⁻¹ : Circle) : ℂ) * ξ with hξ'
  have hnorm : ξ'.re ^ 2 + ξ'.im ^ 2 = ‖ξ‖ ^ 2 := by
    have : ‖ξ'‖ = ‖ξ‖ := by simp [hξ']
    rw [← this, Complex.sq_norm, Complex.normSq_apply]; ring
  have hre : A * (ξ'.re ^ 2 - ξ'.im ^ 2) = (w * ξ ^ 2).re := by
    have h2 : ξ' ^ 2 = ((((rot w)⁻¹ : Circle) : ℂ)) ^ 2 * ξ ^ 2 := by rw [hξ', mul_pow]
    have h3 : (A : ℂ) * ξ' ^ 2 = w * ξ ^ 2 := by
      rw [h2, ← mul_assoc, hA, norm_mul_rot_inv_sq]
    have h4 := congrArg Complex.re h3
    rw [Complex.re_ofReal_mul] at h4
    rw [← h4]; simp [sq]
  have hc2 : conj (2 : ℂ) = 2 := by apply Complex.ext <;> simp
  have hconj : conj ((η : ℂ) - 2 * A * I) = (η : ℂ) + 2 * A * I := by
    simp [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, hc2]
  have hsq : ((η : ℂ) - 2 * A * I) ^ (1 / 2 : ℂ) * ((η : ℂ) + 2 * A * I) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (η ^ 2 + 4 * A ^ 2) : ℝ) : ℂ) := by
    rw [← hconj, cpow_half_mul_conj h₁]
    congr 1
    rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
    congr 1; simp; ring
  have hD : ((η : ℂ) - 2 * A * I) * ((η : ℂ) + 2 * A * I) = ((η ^ 2 + 4 * A ^ 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hD0 : ((η ^ 2 + 4 * A ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (η ^ 2 + 4 * A ^ 2 : ℝ) ≠ 0)
  have hb₁ : ((η : ℂ) - 2 * A * I) ≠ 0 := by
    intro h; rw [h] at h₁; simp at h₁
  have hb₂ : ((η : ℂ) + 2 * A * I) ≠ 0 := by
    intro h; rw [h] at h₂; simp at h₂
  rw [← hnorm, ← hre]
  calc (1 / ((η : ℂ) - 2 * A * I) ^ (1 / 2 : ℂ) *
          cexp (-π / ((η : ℂ) - 2 * A * I) * (ξ'.re : ℂ) ^ 2)) *
        (1 / ((η : ℂ) + 2 * A * I) ^ (1 / 2 : ℂ) *
          cexp (-π / ((η : ℂ) + 2 * A * I) * (ξ'.im : ℂ) ^ 2))
      = (((η : ℂ) - 2 * A * I) ^ (1 / 2 : ℂ) * ((η : ℂ) + 2 * A * I) ^ (1 / 2 : ℂ))⁻¹ *
          cexp (-π / ((η : ℂ) - 2 * A * I) * (ξ'.re : ℂ) ^ 2 +
            -π / ((η : ℂ) + 2 * A * I) * (ξ'.im : ℂ) ^ 2) := by
        rw [Complex.exp_add, mul_inv]; ring
    _ = _ := by
        rw [hsq]
        congr 2
        rw [eq_div_iff hD0, ← hD]
        field_simp
        push_cast
        ring

end PlaneGaussian

end

#print axioms PlaneGaussian.norm_iteratedFDeriv_normSq_le
#print axioms PlaneGaussian.one_add_pow_mul_exp_le
#print axioms PlaneGaussian.norm_iteratedFDeriv_gauss_le
#print axioms PlaneGaussian.gaussC_apply
#print axioms PlaneGaussian.chirp_apply
#print axioms PlaneGaussian.fourier_prod_gauss
#print axioms PlaneGaussian.chirp_rot
#print axioms PlaneGaussian.cpow_half_mul_conj
#print axioms PlaneGaussian.fourier_chirp
