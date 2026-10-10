import KubotaStrip

/-! # The contour shift and the transformed weight `V^♯` (round 376)

S5f-5 of round 360's plan, part 2. The companion paper writes: "`Together with the rapid decay of
$\widehat V_*$ on vertical lines, these bounds justify moving the $s$-contour in
\eqref{eq:theta-mellin-inversion} to $\Rea s<0$.`" After the functional equation: "`The rapid decay of
$\widehat V_*$, together with Stirling's formula, allows us to shift each kernel contour to $\Rea t=0$.`" and
"`This gives the weight $V_*^\sharp$ defined in \eqref{eq:theta-weight}, evaluated at
$\NK(\ell)X/\NK(c)^2$.`" This file proves these steps for round 374's `𝒥(s)`, with the bounds of round 375.

* **The Mellin transform of a smooth weight** (`mellin_eq_interval`, `mellin_ibp`, `mellin_iter`,
  `norm_mellin_le_bound`, **`mellin_decay`**, with `deriv_eq_zero_out` and `iteratedDeriv_eq_zero_out`): for `W`
  smooth and vanishing outside `[α, β] ⊂ (0, ∞)`, `Ŵ(z) = (−1)^k(∏_{j<k}(z + j))^{−1}(W^{(k)})^(z + k)`. In a
  vertical strip `|Ŵ(z)| ≤ CN(1 + |Im z|)^{−k}` if `|W^{(i)}| ≤ N` for `i ≤ k`, with `C` depending only on
  `α`, `β`, the strip and `k`.
* **The weight `V_*(y) = √y·W(y)`** (`mellin_Vstar`, `mellin_Vstar_decay`, `mellinConvergent_of_support`,
  `differentiable_mellin_of_support`, **`Vstar_mellinInv`**, with `Vstar_eq_zero_out`, `continuous_Vstar`,
  `isBigO_of_eventually_eq_zero` and `integrable_inv_one_add_abs_sq`): `V̂_*(z) = Ŵ(z + 1/2)`, entire and
  decaying in strips, and Mellin inversion `V_*(y) = (1/2π)∫V̂_*(σ + iu)y^{−σ−iu} du`.
* **Contour shifts between vertical lines** (**`vertical_shift`**): round 156's `PilotWeil.strip_shift'`, turned
  by `t ↦ it`.
* **The transformed weight** (`kernG` and `Vsharp`, definitions; `differentiableOn_kernG`, `kernG_bound` and
  **`kernG_shift`**, with `norm_ofReal_cpow_le` and `inv_one_add_sq_le_rpow`): the kernel
  `V̂_*(s − 1/2)·gRatio(s)·Y^{s−1/2}` and `V^♯(Y) = (1/2π)∫V̂_*(iu)gRatio(1/2 + iu)Y^{iu} du`. The paper's
  `V_*^♯(x)` is `V^♯((2π)⁴x/27)`. The kernel's integral along any line `Re s = σ` with `−5/2 ≤ σ ≤ 1/2` is
  `2πV^♯(Y)`.
* **The dual side** (`Fq`, a definition; **`Fq_dual_line`**, with `cpow_combine`, `ofReal_cpow_eq_exp`,
  `ofReal_eq_exp` and `dual_term_kern`): for `Re s < −3/2`, `V̂_*(s − 1/2)𝒥(s)Z^{s−1/2}/(Γ(s + 1/3)Γ(s + 2/3))` is
  the sum over the cusp terms and the cusp coefficients `m` of `d(m)φ(m)N(c)x_m^{−2}` times the kernel at
  `Y = x_m²Z/(4N(c)²)`, where `x_m = 4π|m|/9`.
* **The Voronoi-type identity** (**`voronoi_FE`**, with `integral_tsum_of_dom` and `AY_eq`): under the
  hypotheses of round 374's `mellin_FE`, the integral of `V̂_*(s − 1/2)𝒥(s)Z^{s−1/2}/(Γ(s + 1/3)Γ(s + 2/3))` along
  `Re s = 2` is the sum over the cusp terms and the coefficients `m` of `d(m)φ(m)N(c)x_m^{−2}·2πV^♯(x_m²Z/(4N(c)²))`.
  This holds for every smooth weight supported in `[α, β] ⊂ (0, ∞)` whose first `14` derivatives are bounded.
* **For the twisted `θ̄`** (**`twisted_theta_voronoi`**): the identity with the data of round 373's
  `twisted_theta_dbar`, chosen before the weight.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics
open scoped Topology ContDiff ComplexConjugate

noncomputable section

namespace Eis

/-- The derivative of a function vanishing outside `[α, β]` vanishes outside `[α, β]`. -/
theorem deriv_eq_zero_out {W : ℝ → ℂ} {α β : ℝ} (hW : ∀ y, y < α ∨ β < y → W y = 0) :
    ∀ y, y < α ∨ β < y → deriv W y = 0 := by
  intro y hy
  have h : W =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    rcases hy with hy | hy
    · filter_upwards [Iio_mem_nhds hy] with x hx using hW x (Or.inl hx)
    · filter_upwards [Ioi_mem_nhds hy] with x hx using hW x (Or.inr hx)
  rw [h.deriv_eq]; simp

theorem iteratedDeriv_eq_zero_out {W : ℝ → ℂ} {α β : ℝ} (hW : ∀ y, y < α ∨ β < y → W y = 0) (k : ℕ) :
    ∀ y, y < α ∨ β < y → iteratedDeriv k W y = 0 := by
  induction k generalizing W with
  | zero => simpa using hW
  | succ k ih =>
    rw [iteratedDeriv_succ']
    exact ih (deriv_eq_zero_out hW)

/-- For a function vanishing outside `[α, β] ⊂ (0, ∞)`, the Mellin integral is an integral over
`[α/2, 2β]`. -/
theorem mellin_eq_interval {f : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hf : ∀ y, y < α ∨ β < y → f y = 0) (z : ℂ) :
    mellin f z = ∫ y in (α / 2)..(2 * β), (y : ℂ) ^ (z - 1) * f y := by
  unfold mellin
  rw [intervalIntegral.integral_of_le (by linarith)]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ α / 2)))]
  · rfl
  · intro y hy
    have : y ≤ α / 2 ∨ 2 * β < y := by
      rcases le_or_gt y (α / 2) with h | h
      · exact Or.inl h
      · right; by_contra h'; exact hy.2 ⟨h, not_lt.1 h'⟩
    have hfy : f y = 0 := hf y (by rcases this with h | h; left; linarith; right; linarith)
    simp [hfy]

/-- **One integration by parts**: `∫_0^∞ f(y)y^{z−1} dy = −z^{−1}∫_0^∞ f′(y)y^z dy` for a `C¹` function
vanishing outside `[α, β] ⊂ (0, ∞)` and `z ≠ 0`. -/
theorem mellin_ibp {f : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hf : ∀ y, y < α ∨ β < y → f y = 0) (hd : Differentiable ℝ f) (hc : Continuous (deriv f))
    {z : ℂ} (hz : z ≠ 0) : mellin f z = -(z⁻¹ * mellin (deriv f) (z + 1)) := by
  rw [mellin_eq_interval hα hαβ hf, mellin_eq_interval hα hαβ (deriv_eq_zero_out hf)]
  have hpos : ∀ y ∈ uIcc (α / 2) (2 * β), 0 < y := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    linarith [hy.1]
  have hv : ∀ y ∈ uIcc (α / 2) (2 * β), HasDerivAt (fun y : ℝ => (y : ℂ) ^ ((z - 1) + 1) / ((z - 1) + 1))
      ((y : ℂ) ^ (z - 1)) y := fun y hy =>
    hasDerivAt_ofReal_cpow_const' (hpos y hy).ne' (by intro h; apply hz; linear_combination h)
  have hcont : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (z - 1)) (uIcc (α / 2) (2 * β)) := fun y hy =>
    (continuousAt_ofReal_cpow_const y (z - 1) (Or.inr (hpos y hy).ne')).continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun y _ => (hd y).hasDerivAt) hv
    (hc.intervalIntegrable _ _) (hcont.intervalIntegrable)
  have h1 : f (2 * β) = 0 := hf _ (Or.inr (by linarith))
  have h2 : f (α / 2) = 0 := hf _ (Or.inl (by linarith))
  rw [h1, h2, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  simp only [sub_add_cancel] at hibp
  rw [show (∫ y in (α / 2)..(2 * β), (y : ℂ) ^ (z - 1) * f y) =
      ∫ y in (α / 2)..(2 * β), f y * (y : ℂ) ^ (z - 1) from
      intervalIntegral.integral_congr fun y _ => mul_comm _ _, hibp]
  rw [show (∫ y in (α / 2)..(2 * β), deriv f y * ((y : ℂ) ^ z / z)) =
      z⁻¹ * ∫ y in (α / 2)..(2 * β), (y : ℂ) ^ (z + 1 - 1) * deriv f y by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [add_sub_cancel_right]
    field_simp]

/-- **Repeated integration by parts**: `Ŵ(z) = (−1)^k(∏_{j<k}(z + j))^{−1}·(W^{(k)})^(z + k)`. -/
theorem mellin_iter {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ) :
    ∀ (W : ℝ → ℂ), (∀ y, y < α ∨ β < y → W y = 0) → ContDiff ℝ ∞ W →
    ∀ z : ℂ, (∀ j < k, z + j ≠ 0) →
      mellin W z = (-1) ^ k * (∏ j ∈ Finset.range k, (z + j))⁻¹ * mellin (iteratedDeriv k W) (z + k) := by
  induction k with
  | zero => intro W _ _ z _; simp
  | succ k ih =>
    intro W hW hs z hz
    obtain ⟨hd, hs'⟩ := contDiff_infty_iff_deriv.1 hs
    have hz0 : z ≠ 0 := by simpa using hz 0 (Nat.succ_pos k)
    rw [mellin_ibp hα hαβ hW hd hs'.continuous hz0,
      ih (deriv W) (deriv_eq_zero_out hW) hs' (z + 1) fun j hj => by
        have := hz (j + 1) (by omega); push_cast at this
        intro h; apply this; linear_combination h]
    rw [← iteratedDeriv_succ', Finset.prod_range_succ']
    have hP : (∏ j ∈ Finset.range k, (z + 1 + (j : ℂ))) = ∏ j ∈ Finset.range k, (z + ((j + 1 : ℕ) : ℂ)) :=
      Finset.prod_congr rfl fun j _ => by push_cast; ring
    rw [hP, show z + 1 + (k : ℂ) = z + ((k + 1 : ℕ) : ℂ) by push_cast; ring]
    simp only [Nat.cast_zero, add_zero, mul_inv, pow_succ]
    ring

/-- `|Ŵ(z)| ≤ N∫_{α/2}^{2β}(y^{a−1} + y^{b−1}) dy` for `a ≤ Re z ≤ b`, if `|W| ≤ N`. -/
theorem norm_mellin_le_bound {g : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hg : ∀ y, y < α ∨ β < y → g y = 0) {N : ℝ} (hN : ∀ y, ‖g y‖ ≤ N) {a b : ℝ} {z : ℂ}
    (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖mellin g z‖ ≤ N * ∫ y in (α / 2)..(2 * β), (y ^ (a - 1) + y ^ (b - 1)) := by
  rw [mellin_eq_interval hα hαβ hg, ← intervalIntegral.integral_const_mul]
  have hab : α / 2 ≤ 2 * β := by linarith
  have hpos : ∀ y ∈ Icc (α / 2) (2 * β), 0 < y := fun y hy => by linarith [hy.1]
  refine intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall fun y hy => ?_) ?_
  · have hy0 : 0 < y := by linarith [hy.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (z - 1).re = z.re - 1 := by simp
    rw [hre]
    have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN y)
    have hpow : y ^ (z.re - 1) ≤ y ^ (a - 1) + y ^ (b - 1) := by
      rcases le_or_gt y 1 with h | h
      · have := Real.rpow_le_rpow_of_exponent_ge hy0 h (by linarith : a - 1 ≤ z.re - 1)
        linarith [Real.rpow_nonneg hy0.le (b - 1)]
      · have := Real.rpow_le_rpow_of_exponent_le h.le (by linarith : z.re - 1 ≤ b - 1)
        linarith [Real.rpow_nonneg hy0.le (a - 1)]
    calc y ^ (z.re - 1) * ‖g y‖ ≤ (y ^ (a - 1) + y ^ (b - 1)) * N :=
          mul_le_mul hpow (hN y) (norm_nonneg _) (by positivity)
      _ = N * (y ^ (a - 1) + y ^ (b - 1)) := by ring
  · refine (ContinuousOn.intervalIntegrable ?_).const_mul N
    rw [uIcc_of_le hab]
    exact (ContinuousOn.rpow_const continuousOn_id (fun y hy => Or.inl (hpos y hy).ne')).add
      (ContinuousOn.rpow_const continuousOn_id (fun y hy => Or.inl (hpos y hy).ne'))

/-- **Decay of the Mellin transform** of a smooth weight supported in `[α, β] ⊂ (0, ∞)` in a vertical strip:
`|Ŵ(z)| ≤ CN(1 + |Im z|)^{−k}` if `|W^{(i)}| ≤ N` for `i ≤ k`, with `C` depending only on `α, β, a, b, k`. -/
theorem mellin_decay {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (W : ℝ → ℂ), (∀ y, y < α ∨ β < y → W y = 0) → ContDiff ℝ ∞ W →
      ∀ N : ℝ, (∀ i ≤ k, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖mellin W z‖ ≤ C * N / (1 + |z.im|) ^ k := by
  set I₀ := ∫ y in (α / 2)..(2 * β), (y ^ (a - 1) + y ^ (b - 1)) with hI₀
  set I₁ := ∫ y in (α / 2)..(2 * β), (y ^ (a + k - 1) + y ^ (b + k - 1)) with hI₁
  have hab : α / 2 ≤ 2 * β := by linarith
  have hnn : ∀ c d : ℝ, 0 ≤ ∫ y in (α / 2)..(2 * β), (y ^ c + y ^ d) := fun c d =>
    intervalIntegral.integral_nonneg hab fun y hy => by
      have : 0 < y := by linarith [hy.1]
      positivity
  refine ⟨2 ^ k * (I₀ + I₁), by have := hnn (a - 1) (b - 1); have := hnn (a + k - 1) (b + k - 1); positivity,
    fun W hW hs N hN z ha hb => ?_⟩
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0)
  have hI₀0 : 0 ≤ I₀ := hnn _ _
  have hI₁0 : 0 ≤ I₁ := hnn _ _
  have hden : 0 < (1 + |z.im|) ^ k := by positivity
  rw [le_div_iff₀ hden]
  rcases lt_or_ge |z.im| 1 with him | him
  · have h0 := norm_mellin_le_bound hα hαβ hW (fun y => by simpa using hN 0 (Nat.zero_le _) y) ha hb
    have h2 : (1 + |z.im|) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    calc ‖mellin W z‖ * (1 + |z.im|) ^ k ≤ (N * I₀) * 2 ^ k := by gcongr
      _ ≤ 2 ^ k * (I₀ + I₁) * N := by
          have h3 : 0 ≤ 2 ^ k * I₁ * N := mul_nonneg (mul_nonneg (by positivity) hI₁0) hN0
          linarith [show N * I₀ * 2 ^ k = 2 ^ k * I₀ * N by ring,
            show 2 ^ k * (I₀ + I₁) * N = 2 ^ k * I₀ * N + 2 ^ k * I₁ * N by ring]
  · have hzj : ∀ j < k, z + j ≠ 0 := fun j _ h => by
      have := congrArg Complex.im h
      simp at this
      rw [this, abs_zero] at him
      linarith
    rw [mellin_iter hα hαβ k W hW hs z hzj]
    have hk := norm_mellin_le_bound hα hαβ (iteratedDeriv_eq_zero_out hW k) (hN k le_rfl)
      (a := a + k) (b := b + k) (z := z + k) (by simp; linarith) (by simp; linarith)
    have hprod : ((1 + |z.im|) / 2) ^ k ≤ ‖∏ j ∈ Finset.range k, (z + j)‖ := by
      rw [norm_prod]
      calc ((1 + |z.im|) / 2) ^ k = ∏ _j ∈ Finset.range k, ((1 + |z.im|) / 2) := by
            rw [Finset.prod_const, Finset.card_range]
        _ ≤ ∏ j ∈ Finset.range k, ‖z + j‖ := by
            refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
            have := Complex.abs_im_le_norm (z + j)
            simp at this
            linarith
    have hP0 : 0 < ‖∏ j ∈ Finset.range k, (z + j)‖ := lt_of_lt_of_le (by positivity) hprod
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv]
    have e : (1 + |z.im|) ^ k = 2 ^ k * ((1 + |z.im|) / 2) ^ k := by
      rw [div_pow]; field_simp
    rw [e]
    calc ‖∏ j ∈ Finset.range k, (z + j)‖⁻¹ * ‖mellin (iteratedDeriv k W) (z + k)‖ *
          (2 ^ k * ((1 + |z.im|) / 2) ^ k)
        ≤ ‖∏ j ∈ Finset.range k, (z + j)‖⁻¹ * (N * I₁) * (2 ^ k * ‖∏ j ∈ Finset.range k, (z + j)‖) := by
          gcongr
      _ = 2 ^ k * I₁ * N := by field_simp
      _ ≤ 2 ^ k * (I₀ + I₁) * N := by
          gcongr
          linarith

theorem isBigO_of_eventually_eq_zero {f : ℝ → ℂ} {g : ℝ → ℝ} {l : Filter ℝ} (h : ∀ᶠ x in l, f x = 0) :
    f =O[l] g :=
  (isBigO_zero g l).congr' (h.mono fun _ hx => hx.symm) EventuallyEq.rfl

/-- A continuous function vanishing outside `[α, β] ⊂ (0, ∞)` has a Mellin transform converging
everywhere. -/
theorem mellinConvergent_of_support {f : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hf : ∀ y, y < α ∨ β < y → f y = 0) (hc : Continuous f) (z : ℂ) : MellinConvergent f z := by
  unfold MellinConvergent
  refine IntegrableOn.of_forall_sdiff_eq_zero (s := Icc (α / 2) (2 * β)) ?_ measurableSet_Ioi ?_
  · refine ContinuousOn.integrableOn_Icc fun y hy => ?_
    have hy0 : 0 < y := by linarith [hy.1]
    exact ((continuousAt_ofReal_cpow_const y (z - 1) (Or.inr hy0.ne')).smul
      hc.continuousAt).continuousWithinAt
  · intro y hy
    have hy' : y < α ∨ β < y := by
      rcases lt_or_ge y (α / 2) with h | h
      · exact Or.inl (by linarith)
      · right; by_contra h'; exact hy.2 ⟨h, by linarith [not_lt.1 h']⟩
    simp [hf y hy']

/-- ... and an entire Mellin transform. -/
theorem differentiable_mellin_of_support {f : ℝ → ℂ} {α β : ℝ} (hα : 0 < α)
    (hf : ∀ y, y < α ∨ β < y → f y = 0) (hc : Continuous f) : Differentiable ℂ (mellin f) := by
  intro s
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hc.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by linarith)
  · exact isBigO_of_eventually_eq_zero ((eventually_gt_atTop β).mono fun y hy => hf y (Or.inr hy))
  · refine isBigO_of_eventually_eq_zero ?_
    filter_upwards [Ioo_mem_nhdsGT hα] with y hy using hf y (Or.inl hy.2)

theorem Vstar_eq_zero_out {W : ℝ → ℂ} {α β : ℝ} (hW : ∀ y, y < α ∨ β < y → W y = 0) :
    ∀ y, y < α ∨ β < y → Vstar W y = 0 := fun y hy => by simp [Vstar, hW y hy]

theorem continuous_Vstar {W : ℝ → ℂ} (hc : Continuous W) : Continuous (Vstar W) :=
  (Complex.continuous_ofReal.comp Real.continuous_sqrt).mul hc

/-- `V̂_*(z) = Ŵ(z + 1/2)`, for `V_*(y) = √y·W(y)`. -/
theorem mellin_Vstar (W : ℝ → ℂ) (z : ℂ) : mellin (Vstar W) z = mellin W (z + 1 / 2) := by
  rw [← mellin_cpow_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  simp only [Vstar, smul_eq_mul]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy0.le]
  push_cast
  ring

/-- **Decay of `V̂_*`** in a vertical strip, with a constant depending only on `α, β, a, b, k`. -/
theorem mellin_Vstar_decay {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (W : ℝ → ℂ), (∀ y, y < α ∨ β < y → W y = 0) → ContDiff ℝ ∞ W →
      ∀ N : ℝ, (∀ i ≤ k, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖mellin (Vstar W) z‖ ≤ C * N / (1 + |z.im|) ^ k := by
  obtain ⟨C, hC, h⟩ := mellin_decay hα hαβ k (a + 1 / 2) (b + 1 / 2)
  refine ⟨C, hC, fun W hW hs N hN z ha hb => ?_⟩
  rw [mellin_Vstar]
  have := h W hW hs N hN (z + 1 / 2) (by simp; linarith) (by simp; linarith)
  simpa using this

theorem integrable_inv_one_add_abs_sq :
    Integrable fun u : ℝ => ((1 + |u|) ^ 2)⁻¹ := by
  refine integrable_inv_one_add_sq.mono' (by fun_prop) (Eventually.of_forall fun u => ?_)
  have h1 : 0 < 1 + u ^ 2 := by positivity
  have h2 : 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_anti₀ h1 h2

/-- **Mellin inversion for `V_*`**: `V_*(y) = (1/2π)∫ V̂_*(σ + iu)y^{−σ−iu} du`. -/
theorem Vstar_mellinInv {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hW : ∀ y, y < α ∨ β < y → W y = 0) (hs : ContDiff ℝ ∞ W) {N : ℝ}
    (hN : ∀ i ≤ 2, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    mellinInv σ (mellin (Vstar W)) y = Vstar W y := by
  have hc : Continuous (Vstar W) := continuous_Vstar hs.continuous
  refine mellinInv_mellin_eq σ (Vstar W) hy
    (mellinConvergent_of_support hα hαβ (Vstar_eq_zero_out hW) hc σ) ?_ hc.continuousAt
  obtain ⟨C, hC, hdec⟩ := mellin_Vstar_decay hα hαβ 2 σ σ
  have hd := differentiable_mellin_of_support hα (Vstar_eq_zero_out hW) hc
  refine ((integrable_inv_one_add_abs_sq).const_mul (C * N)).mono'
    ((hd.continuous.comp (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  have := hdec W hW hs N hN ((σ : ℂ) + u * I) (by simp) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add] at this
  simpa [div_eq_mul_inv] using this

/-- **Contour shift between vertical lines**, for `G` holomorphic on the closed strip with
`|G(s)| ≤ K(1 + |Im s|)^{−3/2}` there: round 156's `PilotWeil.strip_shift'`, turned by `t ↦ it`. -/
theorem vertical_shift {G : ℂ → ℂ} {a b K : ℝ} (hab : a ≤ b)
    (hd : DifferentiableOn ℂ G (re ⁻¹' Icc a b))
    (hbd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖G s‖ ≤ K * (1 + |s.im|) ^ (-(3 / 2 : ℝ))) :
    ∫ u : ℝ, G (a + u * I) = ∫ u : ℝ, G (b + u * I) := by
  have hmaps : ∀ t ∈ PilotWeil.strip (-b) (-a), I * t ∈ re ⁻¹' Icc a b := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    show a ≤ (I * t).re ∧ (I * t).re ≤ b
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
    constructor <;> linarith
  have h := PilotWeil.strip_shift' (f := fun t => G (I * t)) (a := -b) (b := -a) (K := K)
    (by linarith) (fun t ht => (hd (I * t) (hmaps t ht)).comp t
      ((differentiableAt_id.const_mul I).differentiableWithinAt) fun x hx => hmaps x hx)
    (fun t ht => by
      have := hbd (I * t) (hmaps t ht).1 (hmaps t ht).2
      simpa using this)
  have e : ∀ c r : ℝ, I * ((r : ℂ) + ((-c : ℝ) : ℂ) * I) = (c : ℂ) + (r : ℂ) * I := by
    intro c r; apply Complex.ext <;> simp
  simp only [e] at h
  exact h.symm

/-- The kernel of the transformed weight: `V̂_*(s − 1/2)·gRatio(s)·Y^{s−1/2}`. -/
def kernG (W : ℝ → ℂ) (Y : ℝ) (s : ℂ) : ℂ :=
  mellin (Vstar W) (s - 1 / 2) * gRatio s * (Y : ℂ) ^ (s - 1 / 2)

/-- **The transformed weight** `V^♯(Y) = (1/2π)∫ V̂_*(iu)·gRatio(1/2 + iu)·Y^{iu} du`. The paper's `V_*^♯(x)`
of its (6.6) is `V^♯((2π)⁴x/27)`. -/
def Vsharp (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ u : ℝ, kernG W Y (((1 / 2 : ℝ) : ℂ) + u * I)

theorem norm_ofReal_cpow_le {Y : ℝ} (hY : 0 < Y) {z : ℂ} {e₁ e₂ : ℝ} (h1 : e₁ ≤ z.re)
    (h2 : z.re ≤ e₂) : ‖(Y : ℂ) ^ z‖ ≤ Y ^ e₁ + Y ^ e₂ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  rcases le_or_gt Y 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hY h h1
    linarith [Real.rpow_nonneg hY.le e₂]
  · have := Real.rpow_le_rpow_of_exponent_le h.le h2
    linarith [Real.rpow_nonneg hY.le e₁]

theorem differentiableOn_kernG {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α)
    (hW : ∀ y, y < α ∨ β < y → W y = 0) (hc : Continuous W) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (kernG W Y) {s | s.re < 4 / 3} := by
  have hm := differentiable_mellin_of_support hα (Vstar_eq_zero_out hW) (continuous_Vstar hc)
  intro s hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => mellin (Vstar W) (s - 1 / 2)) s :=
    (hm _).comp s (differentiableAt_id.sub_const _)
  have h3 : DifferentiableAt ℂ (fun s : ℂ => (Y : ℂ) ^ (s - 1 / 2)) s :=
    (differentiableAt_id.sub_const _).const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hY.ne'))
  exact ((h1.differentiableWithinAt.mul (differentiableOn_gRatio s hs)).mul
    h3.differentiableWithinAt)

/-- **The kernel in the strip** `−5/2 ≤ Re s ≤ 1/2`: at most `CNY^{Re s − 1/2}(1 + |Im s|)^{−2}`. -/
theorem kernG_bound {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ C, 0 ≤ C ∧ ∀ (W : ℝ → ℂ), (∀ y, y < α ∨ β < y → W y = 0) → ContDiff ℝ ∞ W →
      ∀ N : ℝ, (∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
      ∀ Y : ℝ, 0 < Y → ∀ s : ℂ, -5 / 2 ≤ s.re → s.re ≤ 1 / 2 →
        ‖kernG W Y s‖ ≤ C * N * Y ^ (s.re - 1 / 2) / (1 + |s.im|) ^ 2 := by
  obtain ⟨Cv, hCv, hv⟩ := mellin_Vstar_decay hα hαβ 14 (-3) 0
  obtain ⟨Cg, hg⟩ := exists_gRatio_strip 3
  have hCg : 0 ≤ Cg := by
    have := (norm_nonneg _).trans (hg (1 / 2 : ℂ) (by norm_num) (by norm_num))
    simpa using this
  refine ⟨Cv * Cg, mul_nonneg hCv hCg, fun W hW hs N hN Y hY s h1 h2 => ?_⟩
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by norm_num) 0)
  have hk := hv W hW hs N hN (s - 1 / 2) (by simp; linarith) (by simp; linarith)
  have hgs := hg s (by push_cast; linarith) h2
  have hy : ‖(Y : ℂ) ^ (s - 1 / 2)‖ = Y ^ (s.re - 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]; simp
  have him : (s - 1 / 2).im = s.im := by simp
  rw [him] at hk
  have hpos : 0 < 1 + |s.im| := by positivity
  unfold kernG
  rw [norm_mul, norm_mul]
  have e12 : (1 + |s.im|) ^ (4 * 3) / (1 + |s.im|) ^ 14 = ((1 + |s.im|) ^ 2)⁻¹ := by
    rw [div_eq_iff (by positivity)]; field_simp
  rw [hy]
  calc ‖mellin (Vstar W) (s - 1 / 2)‖ * ‖gRatio s‖ * Y ^ (s.re - 1 / 2)
      ≤ (Cv * N / (1 + |s.im|) ^ 14) * (Cg * (1 + |s.im|) ^ (4 * 3)) * Y ^ (s.re - 1 / 2) := by
        gcongr
    _ = Cv * Cg * N * Y ^ (s.re - 1 / 2) * ((1 + |s.im|) ^ (4 * 3) / (1 + |s.im|) ^ 14) := by
        ring
    _ = Cv * Cg * N * Y ^ (s.re - 1 / 2) / (1 + |s.im|) ^ 2 := by
        rw [e12]; exact (div_eq_mul_inv _ _).symm

theorem inv_one_add_sq_le_rpow {x : ℝ} (hx : 0 ≤ x) : ((1 + x) ^ 2)⁻¹ ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have h1 : (1 : ℝ) ≤ 1 + x := by linarith
  rw [Real.rpow_neg (by linarith), show ((1 + x) ^ 2) = (1 + x) ^ (2 : ℝ) by norm_cast]
  exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))

/-- **The kernel's contour shift**: for `−5/2 ≤ σ ≤ 1/2`, the integral of the kernel along `Re s = σ` is
`2πV^♯(Y)`. -/
theorem kernG_shift {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) {W : ℝ → ℂ}
    (hW : ∀ y, y < α ∨ β < y → W y = 0) (hs : ContDiff ℝ ∞ W) {N : ℝ}
    (hN : ∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) {Y : ℝ} (hY : 0 < Y) {σ : ℝ}
    (hσ1 : -5 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2) :
    ∫ u : ℝ, kernG W Y (σ + u * I) = 2 * Real.pi * Vsharp W Y := by
  obtain ⟨C, hC, hb⟩ := kernG_bound hα hαβ
  have hshift := vertical_shift (G := kernG W Y) (a := σ) (b := 1 / 2)
    (K := C * N * (Y ^ (-3 : ℝ) + 1)) hσ2
    ((differentiableOn_kernG hα hW hs.continuous hY).mono fun s hs' => by
      show s.re < 4 / 3; linarith [hs'.2])
    (fun s h1 h2 => by
      have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by norm_num) 0)
      have := hb W hW hs N hN Y hY s (by linarith) h2
      have hYe : Y ^ (s.re - 1 / 2) ≤ Y ^ (-3 : ℝ) + 1 := by
        rcases le_or_gt Y 1 with h | h
        · have := Real.rpow_le_rpow_of_exponent_ge hY h (by linarith : -3 ≤ s.re - 1 / 2)
          linarith
        · have := Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith : s.re - 1 / 2 ≤ 0)
          linarith [Real.rpow_nonneg hY.le (-3 : ℝ)]
      calc ‖kernG W Y s‖ ≤ C * N * Y ^ (s.re - 1 / 2) / (1 + |s.im|) ^ 2 := this
        _ = C * N * Y ^ (s.re - 1 / 2) * ((1 + |s.im|) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ C * N * (Y ^ (-3 : ℝ) + 1) * (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
          gcongr
          exact inv_one_add_sq_le_rpow (abs_nonneg _))
  rw [hshift, Vsharp, ← mul_assoc,
    mul_one_div_cancel (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_pos.ne')), one_mul]

theorem ofReal_cpow_eq_exp {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (p : ℂ) ^ z = Complex.exp ((Real.log p : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hp.ne'), ← Complex.ofReal_log hp.le]

theorem ofReal_eq_exp {p : ℝ} (hp : 0 < p) : (p : ℂ) = Complex.exp (Real.log p : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hp]

/-- `N^{2−2s}·2^{1−2s}x^{2s−3}·Z^{s−1/2} = Nx^{−2}·(x²Z/(4N²))^{s−1/2}`. -/
theorem cpow_combine {Nc x Z : ℝ} (hN : 0 < Nc) (hx : 0 < x) (hZ : 0 < Z) (s : ℂ) :
    (Nc : ℂ) ^ (2 - 2 * s) * ((2 : ℂ) ^ (2 * (1 - s) - 1) * (x : ℂ) ^ (-(2 * (1 - s) + 1))) *
      (Z : ℂ) ^ (s - 1 / 2) =
      ((Nc * (x ^ 2)⁻¹ : ℝ) : ℂ) * (((x ^ 2 / (4 * Nc ^ 2) * Z : ℝ)) : ℂ) ^ (s - 1 / 2) := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2, ofReal_cpow_eq_exp hN, ofReal_cpow_eq_exp (by norm_num : (0 : ℝ) < 2),
    ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hZ, ofReal_cpow_eq_exp (by positivity),
    ofReal_eq_exp (by positivity : 0 < Nc * (x ^ 2)⁻¹), ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have l1 : Real.log (Nc * (x ^ 2)⁻¹) = Real.log Nc - 2 * Real.log x := by
    rw [Real.log_mul hN.ne' (by positivity), Real.log_inv, Real.log_pow]; push_cast; ring
  have l2 : Real.log (x ^ 2 / (4 * Nc ^ 2) * Z) =
      2 * Real.log x - 2 * Real.log 2 - 2 * Real.log Nc + Real.log Z := by
    rw [Real.log_mul (by positivity) hZ.ne', Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [l1, l2]
  push_cast
  ring

/-- One dual term: `V̂_*(s − 1/2)·N^{2−2s}·d·φ·2^{1−2s}Γ(4/3 − s)Γ(5/3 − s)x^{2s−3}·Z^{s−1/2}/(Γ(s + 1/3)Γ(s + 2/3))`
is `d·φ·Nx^{−2}` times the kernel at `Y = x²Z/(4N²)`. -/
theorem dual_term_kern (W : ℝ → ℂ) {Nc Z : ℝ} (hN : 0 < Nc) (hZ : 0 < Z) (d φ : ℂ) (x : ℝ) (hx : 0 ≤ x)
    {s : ℂ} (hs : s.re < 1) :
    (mellin (Vstar W) (s - 1 / 2) * (Gamma (s + 1 / 3))⁻¹ * (Gamma (s + 2 / 3))⁻¹ *
        (Z : ℂ) ^ (s - 1 / 2)) *
      ((Nc : ℂ) ^ (2 - 2 * s) * (d * φ * (2 ^ (2 * (1 - s) - 1) * Gamma ((1 - s) + 1 / 3) *
        Gamma ((1 - s) + 2 / 3) * (x : ℂ) ^ (-(2 * (1 - s) + 1))))) =
      d * φ * ((Nc * (x ^ 2)⁻¹ : ℝ) : ℂ) * kernG W (x ^ 2 / (4 * Nc ^ 2) * Z) s := by
  rcases hx.lt_or_eq with hx | hx
  · rw [show (1 - s) + 1 / 3 = 4 / 3 - s by ring, show (1 - s) + 2 / 3 = 5 / 3 - s by ring]
    have hc := cpow_combine hN hx hZ s
    unfold kernG gRatio
    linear_combination (d * φ * mellin (Vstar W) (s - 1 / 2) * Gamma (4 / 3 - s) * Gamma (5 / 3 - s) *
      (Gamma (s + 1 / 3))⁻¹ * (Gamma (s + 2 / 3))⁻¹) * hc
  · subst hx
    have hne : (-(2 * (1 - s) + 1)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [Complex.ofReal_zero, Complex.zero_cpow hne]
    simp

/-- A sum of continuous functions dominated by `c_m g(u)`, with `Σ c_m < ∞` and `g ≤ 1` integrable, is
integrable, and its integral is the sum of the integrals. -/
theorem integral_tsum_of_dom {T : 𝓞 K → ℝ → ℂ} {c : 𝓞 K → ℝ} {g : ℝ → ℝ} (hT : ∀ m, Continuous (T m))
    (hc0 : ∀ m, 0 ≤ c m) (hc : Summable c) (hg : Integrable g) (hg1 : ∀ u, g u ≤ 1)
    (hdom : ∀ m u, ‖T m u‖ ≤ c m * g u) :
    Integrable (fun u => ∑' m, T m u) ∧ ∫ u, ∑' m, T m u = ∑' m, ∫ u, T m u := by
  have hint : ∀ m, Integrable (T m) := fun m =>
    (hg.const_mul (c m)).mono' (hT m).aestronglyMeasurable (Eventually.of_forall fun u => hdom m u)
  have hsum : Summable fun m => ∫ u, ‖T m u‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun u => norm_nonneg _)
      (fun m => ?_) (hc.mul_right (∫ u, g u))
    calc ∫ u, ‖T m u‖ ≤ ∫ u, c m * g u :=
          integral_mono (hint m).norm (hg.const_mul (c m)) fun u => hdom m u
      _ = c m * ∫ u, g u := integral_const_mul _ _
  have hcont : Continuous fun u => ∑' m, T m u :=
    continuous_tsum hT hc fun m u => (hdom m u).trans (by
      calc c m * g u ≤ c m * 1 := mul_le_mul_of_nonneg_left (hg1 u) (hc0 m)
        _ = c m := mul_one _)
  refine ⟨(hg.const_mul (∑' m, c m)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_), (hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq.symm⟩
  calc ‖∑' m, T m u‖ ≤ ∑' m, ‖T m u‖ := norm_tsum_le_tsum_norm
        (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hdom m u) (hc.mul_right (g u)))
    _ ≤ ∑' m, c m * g u := Summable.tsum_le_tsum (fun m => hdom m u)
        (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hdom m u) (hc.mul_right (g u)))
        (hc.mul_right (g u))
    _ = (∑' m, c m) * g u := tsum_mul_right

/-- `𝒥(s)/(Γ(s + 1/3)Γ(s + 2/3))`, for `𝒥(s) = ∫_0^∞ G(v)v^{2s−1} dv`. -/
def Fq (a φa : 𝓞 K → ℂ) (s : ℂ) : ℂ :=
  mellin (dSer a φa) (2 * s) * (Gamma (s + 1 / 3))⁻¹ * (Gamma (s + 2 / 3))⁻¹

/-- **The dual side, pointwise**: for `Re s < −3/2`, `V̂_*(s − 1/2)·𝒥(s)/(Γ(s + 1/3)Γ(s + 2/3))·Z^{s−1/2}` is the
sum over the cusp terms and the cusp coefficients `m` of `d(m)φ(m)N(c)x_m^{−2}` times the kernel at
`Y = x_m²Z/(4N(c)²)`, `x_m = 4π|m|/9`. -/
theorem Fq_dual_line {ι κ : Type*} (S : Finset ι) (T : Finset κ) {Ka Ca Cc : ℝ}
    {a φa φc : 𝓞 K → ℂ} (ha : ThetaSupp Ka a) (hφa : ∀ m, ‖φa m‖ ≤ Ca * ‖σO m‖)
    (hφc : ∀ m, ‖φc m‖ ≤ Cc * ‖σO m‖) (α : ι → ℂ) (β : κ → ℂ) (γ : ι → κ → ℂ)
    (dd : ι → κ → 𝓞 K → ℂ) (cc : ι → κ → 𝓞 K) (Kd : ι → κ → ℝ)
    (hdd : ∀ i ∈ S, ∀ k ∈ T, ThetaSupp (Kd i k) (dd i k) ∧ σO (cc i k) ≠ 0)
    (hid : ∀ v : ℝ, 0 < v → dSer a φa v = ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k *
      (-(σO (cc i k) ^ 2 * (v : ℂ) ^ 2)⁻¹ *
        dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹)))
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) {s : ℂ} (hs : s.re < -3 / 2) :
    mellin (Vstar W) (s - 1 / 2) * Fq a φa s * (Z : ℂ) ^ (s - 1 / 2) =
      ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k * (-(σO (cc i k) ^ 2)⁻¹ *
        ∑' m : 𝓞 K, dd i k m * φc m *
          ((Complex.normSq (σO (cc i k)) * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
          kernG W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Complex.normSq (σO (cc i k)) ^ 2) * Z) s)) := by
  obtain ⟨-, -, hFE⟩ := mellin_FE S T ha hφa hφc α β γ dd cc Kd hdd hid
  set c := mellin (Vstar W) (s - 1 / 2) * (Gamma (s + 1 / 3))⁻¹ * (Gamma (s + 2 / 3))⁻¹ *
    (Z : ℂ) ^ (s - 1 / 2) with hc
  have e1 : mellin (Vstar W) (s - 1 / 2) * Fq a φa s * (Z : ℂ) ^ (s - 1 / 2) =
      c * mellin (dSer a φa) (2 * s) := by
    unfold Fq; rw [hc]; ring
  rw [e1, hFE s hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hd, hcne⟩ := hdd i hi k hk
  have hNpos : 0 < Complex.normSq (σO (cc i k)) := Complex.normSq_pos.2 hcne
  have hm := mellin_dSer hd hφc (w := 1 - s) (by simp; linarith)
  rw [show mellin (dSer (dd i k) φc) (2 - 2 * s) = mellin (dSer (dd i k) φc) (2 * (1 - s)) by ring_nf, hm]
  have hsum : (∑' m : 𝓞 K, dd i k m * φc m *
      ((Complex.normSq (σO (cc i k)) * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
      kernG W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Complex.normSq (σO (cc i k)) ^ 2) * Z) s) =
      c * (((Complex.normSq (σO (cc i k)) : ℝ) : ℂ) ^ (2 - 2 * s) * ∑' m : 𝓞 K, dd i k m * φc m *
        (2 ^ (2 * (1 - s) - 1) * Gamma ((1 - s) + 1 / 3) * Gamma ((1 - s) + 2 / 3) *
          (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * (1 - s) + 1)))) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [hc]
    exact (dual_term_kern W hNpos hZ (dd i k m) (φc m) _ (by positivity) (by linarith)).symm
  rw [hsum]
  ring

theorem AY_eq {Nc x Z : ℝ} (hN : 0 < Nc) (hx : 0 < x) (hZ : 0 < Z) :
    Nc * (x ^ 2)⁻¹ * (x ^ 2 / (4 * Nc ^ 2) * Z) ^ (-3 : ℝ) =
      64 * Nc ^ 7 * (Z ^ 3)⁻¹ * x ^ (-(2 * (7 / 2 : ℝ) + 1)) := by
  rw [show -(2 * (7 / 2 : ℝ) + 1) = -((8 : ℕ) : ℝ) by norm_num, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_neg hx.le, Real.rpow_natCast, Real.rpow_natCast]
  field_simp
  ring

/-- **The Voronoi-type identity** (the paper's contour shift, its functional equation on the new line,
and the kernel shift that defines `V^♯`): under the hypotheses of round 374's `mellin_FE`, for a smooth
weight `W` supported in `[α₀, β₀] ⊂ (0, ∞)` whose first `14` derivatives are at most `N`, and `Z > 0`,
`∫ V̂_*(s − 1/2)·(𝒥(s)/(Γ(s + 1/3)Γ(s + 2/3)))·Z^{s−1/2} du` along `Re s = 2` equals the sum over the cusp
terms and the cusp coefficients `m` of `d(m)φ(m)N(c)x_m^{−2}·2πV^♯(x_m²Z/(4N(c)²))`, `x_m = 4π|m|/9`. -/
theorem voronoi_FE {ι κ : Type*} (S : Finset ι) (T : Finset κ) {Ka Ca Cc : ℝ}
    {a φa φc : 𝓞 K → ℂ} (ha : ThetaSupp Ka a) (hφa : ∀ m, ‖φa m‖ ≤ Ca * ‖σO m‖)
    (hφc : ∀ m, ‖φc m‖ ≤ Cc * ‖σO m‖) (α : ι → ℂ) (β : κ → ℂ) (γ : ι → κ → ℂ)
    (dd : ι → κ → 𝓞 K → ℂ) (cc : ι → κ → 𝓞 K) (Kd : ι → κ → ℝ)
    (hdd : ∀ i ∈ S, ∀ k ∈ T, ThetaSupp (Kd i k) (dd i k) ∧ σO (cc i k) ≠ 0)
    (hid : ∀ v : ℝ, 0 < v → dSer a φa v = ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k *
      (-(σO (cc i k) ^ 2 * (v : ℂ) ^ 2)⁻¹ *
        dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹)))
    {W : ℝ → ℂ} {α₀ β₀ : ℝ} (hα₀ : 0 < α₀) (hαβ₀ : α₀ ≤ β₀)
    (hW : ∀ y, y < α₀ ∨ β₀ < y → W y = 0) (hs : ContDiff ℝ ∞ W) {N : ℝ}
    (hN : ∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) {Z : ℝ} (hZ : 0 < Z) :
    ∫ u : ℝ, mellin (Vstar W) (((2 : ℝ) : ℂ) + u * I - 1 / 2) * Fq a φa (((2 : ℝ) : ℂ) + u * I) *
        (Z : ℂ) ^ (((2 : ℝ) : ℂ) + u * I - 1 / 2) =
      ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k * (-(σO (cc i k) ^ 2)⁻¹ *
        ∑' m : 𝓞 K, dd i k m * φc m *
          ((Complex.normSq (σO (cc i k)) * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
          (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
            (4 * Complex.normSq (σO (cc i k)) ^ 2) * Z)))) := by
  obtain ⟨-, hdiff, -⟩ := mellin_FE S T ha hφa hφc α β γ dd cc Kd hdd hid
  obtain ⟨CF, hCF⟩ := poly_bound_FE S T ha hφa hφc α β γ dd cc Kd hdd hid
  obtain ⟨Cv, hCv, hv⟩ := mellin_Vstar_decay hα₀ hαβ₀ 14 (-3) (3 / 2)
  obtain ⟨Ck, hCk, hkern⟩ := kernG_bound hα₀ hαβ₀
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by norm_num) 0)
  have hCF0 : 0 ≤ CF := by
    have := (norm_nonneg _).trans (hCF 0 (by norm_num) (by norm_num))
    simpa using this
  set G : ℂ → ℂ := fun s => mellin (Vstar W) (s - 1 / 2) * Fq a φa s * (Z : ℂ) ^ (s - 1 / 2) with hG
  have hmV := differentiable_mellin_of_support hα₀ (Vstar_eq_zero_out hW) (continuous_Vstar hs.continuous)
  have hGd : Differentiable ℂ G := fun s =>
    (((hmV _).comp s (differentiableAt_id.sub_const _)).mul
      (((hdiff.comp (differentiable_id.const_mul 2) s).mul
        ((Complex.differentiable_one_div_Gamma _).comp s (differentiableAt_id.add_const _))).mul
        ((Complex.differentiable_one_div_Gamma _).comp s (differentiableAt_id.add_const _)))).mul
      ((differentiableAt_id.sub_const _).const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hZ.ne')))
  have hGb : ∀ s : ℂ, -5 / 2 ≤ s.re → s.re ≤ 2 →
      ‖G s‖ ≤ Cv * N * CF * (Z ^ (-3 : ℝ) + Z ^ (3 / 2 : ℝ)) * (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
    intro s h1 h2
    have hV := hv W hW hs N hN (s - 1 / 2) (by simp; linarith) (by simp; linarith)
    have hF : ‖Fq a φa s‖ ≤ CF * (1 + |s.im|) ^ 12 := hCF s h1 h2
    have hZs := norm_ofReal_cpow_le hZ (z := s - 1 / 2) (e₁ := -3) (e₂ := 3 / 2) (by simp; linarith)
      (by simp; linarith)
    have him : (s - 1 / 2).im = s.im := by simp
    rw [him] at hV
    simp only [hG]
    rw [norm_mul, norm_mul]
    have hpos : 0 < 1 + |s.im| := by positivity
    calc ‖mellin (Vstar W) (s - 1 / 2)‖ * ‖Fq a φa s‖ * ‖(Z : ℂ) ^ (s - 1 / 2)‖
        ≤ (Cv * N / (1 + |s.im|) ^ 14) * (CF * (1 + |s.im|) ^ 12) *
            (Z ^ (-3 : ℝ) + Z ^ (3 / 2 : ℝ)) := by gcongr
      _ = Cv * N * CF * (Z ^ (-3 : ℝ) + Z ^ (3 / 2 : ℝ)) * ((1 + |s.im|) ^ 2)⁻¹ := by
          field_simp
      _ ≤ _ := by gcongr; exact inv_one_add_sq_le_rpow (abs_nonneg _)
  have hshift := vertical_shift (G := G) (a := -5 / 2) (b := 2) (by norm_num) hGd.differentiableOn hGb
  show ∫ u : ℝ, G (((2 : ℝ) : ℂ) + u * I) = _
  rw [← hshift]
  have hline : ∀ u : ℝ, ((((-5 / 2 : ℝ) : ℂ) + u * I)).re < -3 / 2 := fun u => by simp; norm_num
  have hpt := fun u : ℝ => Fq_dual_line S T ha hφa hφc α β γ dd cc Kd hdd hid W hZ
    (s := ((-5 / 2 : ℝ) : ℂ) + u * I) (hline u)
  refine (integral_congr_ae (Eventually.of_forall hpt)).trans ?_
  have hinner : ∀ i ∈ S, ∀ k ∈ T,
      Integrable (fun u : ℝ => ∑' m : 𝓞 K, dd i k m * φc m *
        ((Complex.normSq (σO (cc i k)) * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
        kernG W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Complex.normSq (σO (cc i k)) ^ 2) * Z)
          (((-5 / 2 : ℝ) : ℂ) + u * I)) ∧
      ∫ u : ℝ, (∑' m : 𝓞 K, dd i k m * φc m *
        ((Complex.normSq (σO (cc i k)) * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
        kernG W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Complex.normSq (σO (cc i k)) ^ 2) * Z)
          (((-5 / 2 : ℝ) : ℂ) + u * I)) =
      ∑' m : 𝓞 K, dd i k m * φc m *
        ((Complex.normSq (σO (cc i k)) * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
        (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
          (4 * Complex.normSq (σO (cc i k)) ^ 2) * Z)) := by
    intro i hi k hk
    obtain ⟨hd, hcne⟩ := hdd i hi k hk
    set Nc := Complex.normSq (σO (cc i k)) with hNc
    have hNpos : 0 < Nc := Complex.normSq_pos.2 hcne
    have hx0 : ∀ m : 𝓞 K, 0 ≤ 4 * Real.pi * ‖σO m‖ / 9 := fun m => by positivity
    have hg1 : ∀ u : ℝ, ((1 + |u|) ^ 2)⁻¹ ≤ 1 := fun u =>
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [abs_nonneg u]))
    have hline' : ∀ u : ℝ, (((-5 / 2 : ℝ) : ℂ) + u * I) ∈ {s : ℂ | s.re < 4 / 3} := fun u => by
      show (((-5 / 2 : ℝ) : ℂ) + u * I).re < 4 / 3
      simp; norm_num
    obtain ⟨hI, hE⟩ := integral_tsum_of_dom
      (T := fun m u => dd i k m * φc m * ((Nc * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
        kernG W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Nc ^ 2) * Z) (((-5 / 2 : ℝ) : ℂ) + u * I))
      (c := fun m => Ck * N * (64 * Nc ^ 7 * (Z ^ 3)⁻¹) *
        (‖dd i k m‖ * ‖φc m‖ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * (7 / 2 : ℝ) + 1))))
      (g := fun u => ((1 + |u|) ^ 2)⁻¹)
      (fun m => by
        rcases (hx0 m).lt_or_eq with hxm | hxm
        · exact continuous_const.mul ((differentiableOn_kernG hα₀ hW hs.continuous
            (by positivity)).continuousOn.comp_continuous (by fun_prop) hline')
        · simp only [← hxm]; simpa using continuous_const)
      (fun m => mul_nonneg (mul_nonneg (mul_nonneg hCk hN0) (by positivity)) (by positivity))
      ((summable_dSer_abs hd hφc (σ := 7 / 2) (by norm_num)).mul_left (Ck * N * (64 * Nc ^ 7 * (Z ^ 3)⁻¹)))
      integrable_inv_one_add_abs_sq hg1
      (fun m u => by
        rcases (hx0 m).lt_or_eq with hxm | hxm
        · have hY : 0 < (4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Nc ^ 2) * Z := by positivity
          have hkb := hkern W hW hs N hN _ hY (((-5 / 2 : ℝ) : ℂ) + u * I) (by simp) (by simp; norm_num)
          have hre : (((-5 / 2 : ℝ) : ℂ) + u * I).re - 1 / 2 = -3 := by simp; norm_num
          have him : (((-5 / 2 : ℝ) : ℂ) + u * I).im = u := by simp
          rw [hre, him] at hkb
          have hA : 0 ≤ Nc * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ := by positivity
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA]
          have hAY := AY_eq hNpos hxm hZ
          calc ‖dd i k m‖ * ‖φc m‖ * (Nc * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹) *
                ‖kernG W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Nc ^ 2) * Z) (((-5 / 2 : ℝ) : ℂ) + u * I)‖
              ≤ ‖dd i k m‖ * ‖φc m‖ * (Nc * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹) *
                  (Ck * N * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Nc ^ 2) * Z) ^ (-3 : ℝ) /
                    (1 + |u|) ^ 2) := by gcongr
            _ = Ck * N * (‖dd i k m‖ * ‖φc m‖) * (Nc * ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ *
                  ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 / (4 * Nc ^ 2) * Z) ^ (-3 : ℝ)) * ((1 + |u|) ^ 2)⁻¹ := by
                ring
            _ = _ := by rw [hAY]; ring
        · simp only [← hxm]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, mul_zero,
            Complex.ofReal_zero, zero_mul, norm_zero]
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCk hN0) (by positivity))
            (by positivity)) (by positivity))
    refine ⟨hI, ?_⟩
    rw [hE]
    refine tsum_congr fun m => ?_
    rw [integral_const_mul]
    rcases (hx0 m).lt_or_eq with hxm | hxm
    · rw [kernG_shift hα₀ hαβ₀ hW hs hN (by positivity) (by norm_num) (by norm_num)]
    · simp only [← hxm]; simp
  rw [integral_finsetSum S (fun i hi => ?_)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, integral_finsetSum T (fun k hk => ?_)]
    · congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [integral_const_mul, integral_const_mul, integral_const_mul, (hinner i hi k hk).2]
    · exact (((hinner i hi k hk).1.const_mul _).const_mul _).const_mul _
  · exact (integrable_finsetSum T fun k hk =>
      (((hinner i hi k hk).1.const_mul _).const_mul _).const_mul _).const_mul _

open Classical in
/-- **The Voronoi-type identity for the twisted `θ̄`**: with the data of round 373's `twisted_theta_dbar`,
chosen once, for every smooth weight `W` supported in `[α₀, β₀] ⊂ (0, ∞)` whose first `14` derivatives
are at most `N`, and every `Z > 0`, the integral along `Re s = 2` of `V̂_*(s − 1/2)`, `𝒥(s)/(Γ(s + 1/3)Γ(s + 2/3))`
and `Z^{s−1/2}` is the sum over the groups `(h₀, A)` and the cusp coefficients `m` of the transformed
weight `V^♯` at `x_m²Z/(4N(c)²)`. -/
theorem twisted_theta_voronoi {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (hφ0 : φ₀ 0 = 0) (Ps : Finset Pr) (hPs : ∀ P ∈ Ps, L ∉ P.1)
    (j : Pr → ℕ) :
    ∃ (D : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K) (C₀ : (𝓞 K ⧸ span {L}) → Finset Pr → ℂ)
      (dH : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K → ℂ) (y : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K),
      (∀ h₀, ∀ A ∈ Ps.powerset, D h₀ A ≠ 0 ∧ D h₀ A ∣ L ∧ ‖C₀ h₀ A‖ = 1 ∧ ThetaSupp Kc (dH h₀ A)) ∧
      ∀ (W : ℝ → ℂ) (α₀ β₀ : ℝ), 0 < α₀ → α₀ ≤ β₀ → (∀ y, y < α₀ ∨ β₀ < y → W y = 0) →
        ContDiff ℝ ∞ W → ∀ N : ℝ, (∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
        ∀ Z : ℝ, 0 < Z →
        ∫ u : ℝ, mellin (Vstar W) (((2 : ℝ) : ℂ) + u * I - 1 / 2) *
            Fq (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)))
              (fun m => 2 * Real.pi * I * conj (σO m) / 9) (((2 : ℝ) : ℂ) + u * I) *
            (Z : ℂ) ^ (((2 : ℝ) : ℂ) + u * I - 1 / 2) =
          ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
            ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
              (C₀ h₀ A * (-(σO (D h₀ A * ∏ P ∈ A, πP P) ^ 2)⁻¹ *
                ∑' m : 𝓞 K, conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
                    (∏ P : A, Bloc P.1.1 (j P.1) m) * (2 * Real.pi * I * σO m / 9) *
                  ((Complex.normSq (σO (D h₀ A * ∏ P ∈ A, πP P)) *
                    ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
                  (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
                    (4 * Complex.normSq (σO (D h₀ A * ∏ P ∈ A, πP P)) ^ 2) * Z)))) := by
  obtain ⟨D, C₀, dH, y, hDATA, hid⟩ := twisted_theta_dbar hd hL φ₀ hφ hφ0 Ps hPs j
  obtain ⟨B₀, hB₀⟩ := exists_bound_of_periodic L hL φ₀ hφ
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  have hF : ∀ x, ‖φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x‖ ≤ B₀ := by
    intro x
    rw [norm_mul, norm_prod]
    exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun P _ => norm_chiPow_le _ _ _))).trans (hB₀ x)
  have ha := thetaSupp_twisted hd.1 hB₀0 hF
  have hcne : ∀ (h₀ : 𝓞 K ⧸ span {L}), ∀ A ∈ Ps.powerset, σO (D h₀ A * ∏ P ∈ A, πP P) ≠ 0 := by
    intro h₀ A hA
    have hD := (hDATA h₀ A hA).1
    have hprod : (∏ P ∈ A, πP P) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P _ => ne_zero_of_maximal (πP P)
    have hc : D h₀ A * ∏ P ∈ A, πP P ≠ 0 := mul_ne_zero hD hprod
    exact fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  have := finite_quot L hL
  let _ : Fintype (𝓞 K ⧸ span {L}) := Fintype.ofFinite _
  refine ⟨D, C₀, dH, y, hDATA, fun W α₀ β₀ hα₀ hαβ₀ hW hs N hN Z hZ => ?_⟩
  rw [voronoi_FE Finset.univ Ps.powerset ha (fun m => norm_phiInf_le m)
    (fun m => norm_phiCusp_le m) (fun h₀ => fCoef L φ₀ (repQ L h₀))
    (fun A => ∏ P ∈ Ps \ A, locCoef P (j P) 0) C₀
    (fun h₀ A m => conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
      ∏ P : A, Bloc P.1.1 (j P.1) m)
    (fun h₀ A => D h₀ A * ∏ P ∈ A, πP P) (fun _ A => (∏ P : A, Real.sqrt (absNorm P.1.1)) * Kc)
    (fun h₀ _ A hA => ⟨thetaSupp_cuspCoef (hDATA h₀ A hA).2.2.2 _ _ A j, hcne h₀ A hA⟩)
    (fun v hv => by rw [← finsum_eq_sum_of_fintype]; exact hid v hv) hα₀ hαβ₀ hW hs hN hZ,
    finsum_eq_sum_of_fintype]

end Eis

end

#print axioms Eis.deriv_eq_zero_out
#print axioms Eis.iteratedDeriv_eq_zero_out
#print axioms Eis.mellin_eq_interval
#print axioms Eis.mellin_ibp
#print axioms Eis.mellin_iter
#print axioms Eis.norm_mellin_le_bound
#print axioms Eis.mellin_decay
#print axioms Eis.isBigO_of_eventually_eq_zero
#print axioms Eis.mellinConvergent_of_support
#print axioms Eis.differentiable_mellin_of_support
#print axioms Eis.Vstar_eq_zero_out
#print axioms Eis.continuous_Vstar
#print axioms Eis.mellin_Vstar
#print axioms Eis.mellin_Vstar_decay
#print axioms Eis.integrable_inv_one_add_abs_sq
#print axioms Eis.Vstar_mellinInv
#print axioms Eis.vertical_shift
#print axioms Eis.norm_ofReal_cpow_le
#print axioms Eis.differentiableOn_kernG
#print axioms Eis.kernG_bound
#print axioms Eis.inv_one_add_sq_le_rpow
#print axioms Eis.kernG_shift
#print axioms Eis.ofReal_cpow_eq_exp
#print axioms Eis.ofReal_eq_exp
#print axioms Eis.cpow_combine
#print axioms Eis.dual_term_kern
#print axioms Eis.integral_tsum_of_dom
#print axioms Eis.Fq_dual_line
#print axioms Eis.AY_eq
#print axioms Eis.voronoi_FE
#print axioms Eis.twisted_theta_voronoi
