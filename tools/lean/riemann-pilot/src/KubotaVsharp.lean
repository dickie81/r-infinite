import KubotaContour

/-! # The decay of the transformed weight `V^♯` (round 377)

S5f-5 of round 360's plan, part 3, which completes S5f-5. The companion paper writes: "`It remains to bound
the transformed weight.`" It continues: "`We may therefore shift the kernel contour to $\Rea t=-1/4$ for
$0<x\le1$, obtaining the factor $x^{1/4}$, and to $\Rea t=A$ for $x\ge1$, obtaining $x^{-A}$.`" and "`Each
application of $x\partial_x$ introduces a factor $-t$.`" This file proves the bound in the form the display
`Eis.ThetaRows` (round 341) uses: `h(w) = V^♯(κe^w)` is smooth, and `|h^{(i)}(w)| ≤ C_wN(1 + e^w)^{−1}` for
`i ≤ 2`, where `N` bounds the first `16` derivatives of the weight and `C_w` depends only on its support and
`κ`.

* **Fourier-type integrals** (`fourierG`, a definition; `hasDerivAt_fourierG`, `iteratedDeriv_fourierG`,
  `contDiff_fourierG` and `norm_fourierG_le`, with `norm_cexp_I_mul`): if every `|u|^nF(u)` is integrable,
  `g_0(w) = ∫F(u)e^{iuw} du` is smooth with `g_0^{(n)}(w) = ∫(iu)^nF(u)e^{iuw} du`.
* **Bounded derivatives** (`exists_deriv_bounds`): a smooth function vanishing outside `[α, β]` has bounded
  derivatives of every order.
* **The profile of `V^♯`** (`vsF`, a definition; `Vsharp_eq_fourierG`, `continuous_vsF`, `norm_vsF`, `vsF_dom`
  and `integrable_vsF_moments`, with `cpow_mul_exp` and `half_line_sub`): `V^♯(κe^w)` is `g_0(w)` for the profile
  `(1/2π)V̂_*(iu)gRatio(1/2 + iu)κ^{iu}`, of modulus `(1/2π)|V̂_*(iu)|`.
* **The decay** (**`Vsharp_decay`**, with `kernG_bound_gen`, `fourierG_eq_line` and `pow_mul_ratio_le`):
  `h(w) = V^♯(κe^w)` is smooth, with `|h^{(i)}(w)| ≤ C_wN(1 + e^w)^{−1}` for `i ≤ 2`.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics
open scoped Topology ContDiff ComplexConjugate

noncomputable section

namespace Eis

/-- A smooth function vanishing outside `[α, β]` has bounded derivatives of every order. -/
theorem exists_deriv_bounds {W : ℝ → ℂ} {α β : ℝ} (hW : ∀ y, y < α ∨ β < y → W y = 0)
    (hs : ContDiff ℝ ∞ W) (k : ℕ) : ∃ N : ℝ, ∀ i ≤ k, ∀ y, ‖iteratedDeriv i W y‖ ≤ N := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedDeriv i W y‖ ≤ C := by
    intro i
    have hc : Continuous (iteratedDeriv i W) := hs.continuous_iteratedDeriv i (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0, fun y => ?_⟩
    by_cases hy : y ∈ Icc α β
    · exact (hC y hy).trans (le_max_left _ _)
    · have : y < α ∨ β < y := by
        rcases not_and_or.1 hy with h | h
        · exact Or.inl (not_le.1 h)
        · exact Or.inr (not_le.1 h)
      rw [iteratedDeriv_eq_zero_out hW i y this, norm_zero]
      exact le_max_right _ _
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (k + 1), max (C i) 0, fun i hi y => ?_⟩
  calc ‖iteratedDeriv i W y‖ ≤ max (C i) 0 := (hC i y).trans (le_max_left _ _)
    _ ≤ ∑ i ∈ Finset.range (k + 1), max (C i) 0 :=
        Finset.single_le_sum (f := fun i => max (C i) 0) (fun _ _ => le_max_right _ _)
          (Finset.mem_range.2 (by omega))

/-- The Fourier-type integrals `g_n(w) = ∫ (iu)^n F(u)e^{iuw} du`. -/
def fourierG (F : ℝ → ℂ) (n : ℕ) (w : ℝ) : ℂ :=
  ∫ u : ℝ, (I * u) ^ n * F u * Complex.exp (I * u * w)

theorem norm_cexp_I_mul (u w : ℝ) : ‖Complex.exp (I * u * w)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- `g_n′ = g_{n+1}`, when every `|u|^nF(u)` is integrable. -/
theorem hasDerivAt_fourierG {F : ℝ → ℂ} (hc : Continuous F)
    (hF : ∀ n : ℕ, Integrable fun u : ℝ => |u| ^ n * ‖F u‖) (n : ℕ) (w : ℝ) :
    HasDerivAt (fourierG F n) (fourierG F (n + 1) w) w := by
  have hmeas : ∀ (m : ℕ) (x : ℝ), AEStronglyMeasurable
      (fun u : ℝ => (I * u) ^ m * F u * Complex.exp (I * u * x)) := fun m x =>
    (((continuous_const.mul Complex.continuous_ofReal).pow m).mul hc |>.mul
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
        continuous_const))).aestronglyMeasurable
  have hnorm : ∀ (m : ℕ) (x u : ℝ), ‖(I * u) ^ m * F u * Complex.exp (I * u * x)‖ = |u| ^ m * ‖F u‖ := by
    intro m x u
    rw [norm_mul, norm_mul, norm_pow, norm_cexp_I_mul, mul_one, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := w) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x => hmeas n x)
    ((hF n).mono' (hmeas n w) (Eventually.of_forall fun u => (hnorm n w u).le))
    (F' := fun x u => (I * u) ^ (n + 1) * F u * Complex.exp (I * u * x)) (hmeas (n + 1) w)
    (Eventually.of_forall fun u x _ => (hnorm (n + 1) x u).le) (hF (n + 1))
    (Eventually.of_forall fun u x _ => by
      have h1 : HasDerivAt (fun y : ℝ => I * u * (y : ℂ)) (I * u * 1) x :=
        ((hasDerivAt_id x).ofReal_comp).const_mul (I * u)
      have h2 := (h1.cexp).const_mul ((I * u) ^ n * F u)
      convert h2 using 1
      ring)
  exact h.2

theorem iteratedDeriv_fourierG {F : ℝ → ℂ} (hc : Continuous F)
    (hF : ∀ n : ℕ, Integrable fun u : ℝ => |u| ^ n * ‖F u‖) (n : ℕ) :
    iteratedDeriv n (fourierG F 0) = fourierG F n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun w => (hasDerivAt_fourierG hc hF n w).deriv

theorem contDiff_fourierG {F : ℝ → ℂ} (hc : Continuous F)
    (hF : ∀ n : ℕ, Integrable fun u : ℝ => |u| ^ n * ‖F u‖) : ContDiff ℝ ∞ (fourierG F 0) :=
  contDiff_of_differentiable_iteratedDeriv fun m _ => by
    rw [iteratedDeriv_fourierG hc hF m]
    exact fun w => (hasDerivAt_fourierG hc hF m w).differentiableAt

theorem norm_fourierG_le {F : ℝ → ℂ} (hF : ∀ n : ℕ, Integrable fun u : ℝ => |u| ^ n * ‖F u‖)
    (n : ℕ) (w : ℝ) :
    ‖fourierG F n w‖ ≤ ∫ u : ℝ, |u| ^ n * ‖F u‖ := by
  unfold fourierG
  refine norm_integral_le_of_norm_le (hF n) (Eventually.of_forall fun u => le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_pow, norm_cexp_I_mul, mul_one, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-- The kernel bound with `k` derivatives: `|kernel| ≤ CNY^{Re s − 1/2}(1 + |Im s|)^{12−k}` for
`−5/2 ≤ Re s ≤ 1/2`. -/
theorem kernG_bound_gen {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (W : ℝ → ℂ), (∀ y, y < α ∨ β < y → W y = 0) → ContDiff ℝ ∞ W →
      ∀ N : ℝ, (∀ i ≤ k, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
      ∀ Y : ℝ, 0 < Y → ∀ s : ℂ, -5 / 2 ≤ s.re → s.re ≤ 1 / 2 →
        ‖kernG W Y s‖ ≤ C * N * Y ^ (s.re - 1 / 2) * (1 + |s.im|) ^ 12 / (1 + |s.im|) ^ k := by
  obtain ⟨Cv, hCv, hv⟩ := mellin_Vstar_decay hα hαβ k (-3) 0
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
  unfold kernG
  rw [norm_mul, norm_mul, hy]
  calc ‖mellin (Vstar W) (s - 1 / 2)‖ * ‖gRatio s‖ * Y ^ (s.re - 1 / 2)
      ≤ (Cv * N / (1 + |s.im|) ^ k) * (Cg * (1 + |s.im|) ^ (4 * 3)) * Y ^ (s.re - 1 / 2) := by
        gcongr
    _ = _ := by ring

theorem cpow_mul_exp {κ : ℝ} (hκ : 0 < κ) (w : ℝ) (z : ℂ) :
    (((κ * Real.exp w : ℝ)) : ℂ) ^ z = (κ : ℂ) ^ z * Complex.exp (w * z) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hκ.le (Real.exp_pos w).le,
    ofReal_cpow_eq_exp (Real.exp_pos w), Real.log_exp]

/-- The Fourier profile of `w ↦ V^♯(κe^w)`. -/
def vsF (W : ℝ → ℂ) (κ : ℝ) (u : ℝ) : ℂ :=
  1 / (2 * Real.pi) * (mellin (Vstar W) ((((1 / 2 : ℝ) : ℂ) + u * I) - 1 / 2) *
    gRatio (((1 / 2 : ℝ) : ℂ) + u * I) * (κ : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + u * I) - 1 / 2))

theorem half_line_sub (u : ℝ) : (((1 / 2 : ℝ) : ℂ) + u * I) - 1 / 2 = u * I := by push_cast; ring

theorem Vsharp_eq_fourierG (W : ℝ → ℂ) {κ : ℝ} (hκ : 0 < κ) (w : ℝ) :
    Vsharp W (κ * Real.exp w) = fourierG (vsF W κ) 0 w := by
  unfold Vsharp fourierG kernG vsF
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [half_line_sub]
  rw [cpow_mul_exp hκ]
  have : Complex.exp (w * (u * I)) = Complex.exp (I * u * w) := by congr 1; ring
  rw [this]
  ring

theorem continuous_vsF {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hW : ∀ y, y < α ∨ β < y → W y = 0)
    (hc : Continuous W) {κ : ℝ} (hκ : 0 < κ) : Continuous (vsF W κ) := by
  have hm := differentiable_mellin_of_support hα (Vstar_eq_zero_out hW) (continuous_Vstar hc)
  have hl : Continuous fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + u * I := by fun_prop
  have hg : Continuous fun u : ℝ => gRatio (((1 / 2 : ℝ) : ℂ) + u * I) :=
    differentiableOn_gRatio.continuousOn.comp_continuous hl fun u => by
      show (((1 / 2 : ℝ) : ℂ) + u * I).re < 4 / 3; simp; norm_num
  unfold vsF
  exact continuous_const.mul (((hm.continuous.comp (hl.sub continuous_const)).mul hg).mul
    ((hl.sub continuous_const).const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hκ.ne'))))

theorem norm_vsF (W : ℝ → ℂ) {κ : ℝ} (hκ : 0 < κ) (u : ℝ) :
    ‖vsF W κ u‖ = 1 / (2 * Real.pi) * ‖mellin (Vstar W) (u * I)‖ := by
  unfold vsF
  rw [half_line_sub, norm_mul, norm_mul, norm_mul, norm_gRatio_half (by simp),
    Complex.norm_cpow_eq_rpow_re_of_pos hκ]
  have h2 : ‖(1 : ℂ) / (2 * Real.pi)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [h2]
  simp

/-- The profile decays: `|u|^n|vsF(u)| ≤ C((1 + |u|)²)^{−1}`, from `n + 2` derivatives of `W`. -/
theorem vsF_dom {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (W : ℝ → ℂ), (∀ y, y < α ∨ β < y → W y = 0) → ContDiff ℝ ∞ W →
      ∀ N : ℝ, (∀ i ≤ n + 2, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) → ∀ κ : ℝ, 0 < κ → ∀ u : ℝ,
        |u| ^ n * ‖vsF W κ u‖ ≤ C * N * ((1 + |u|) ^ 2)⁻¹ := by
  obtain ⟨C, hC, hv⟩ := mellin_Vstar_decay hα hαβ (n + 2) 0 0
  refine ⟨1 / (2 * Real.pi) * C, by positivity, fun W hW hs N hN κ hκ u => ?_⟩
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by omega) 0)
  have hd := hv W hW hs N hN ((u : ℂ) * I) (by simp) (by simp)
  have him : ((u : ℂ) * I).im = u := by simp
  rw [him] at hd
  rw [norm_vsF W hκ]
  have hpos : 0 < 1 + |u| := by positivity
  have hu : |u| ^ n ≤ (1 + |u|) ^ n := pow_le_pow_left₀ (abs_nonneg u) (by linarith) n
  calc |u| ^ n * (1 / (2 * Real.pi) * ‖mellin (Vstar W) (u * I)‖)
      ≤ (1 + |u|) ^ n * (1 / (2 * Real.pi) * (C * N / (1 + |u|) ^ (n + 2))) := by gcongr
    _ = 1 / (2 * Real.pi) * C * N * ((1 + |u|) ^ 2)⁻¹ := by
        rw [pow_add]; field_simp

theorem integrable_vsF_moments {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hW : ∀ y, y < α ∨ β < y → W y = 0) (hs : ContDiff ℝ ∞ W) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    Integrable fun u : ℝ => |u| ^ n * ‖vsF W κ u‖ := by
  obtain ⟨C, hC, hdom⟩ := vsF_dom hα hαβ n
  obtain ⟨N, hN⟩ := exists_deriv_bounds hW hs (n + 2)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by omega) 0)
  refine (integrable_inv_one_add_abs_sq.const_mul (C * N)).mono'
    ((continuous_abs.pow n).mul (continuous_vsF hα hW hs.continuous hκ).norm).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact hdom W hW hs N hN κ hκ u

/-- `g_n(w)` as `(1/2π)` times the integral of `(s − 1/2)^n` times the kernel at `κe^w`, along `Re s = 1/2`. -/
theorem fourierG_eq_line (W : ℝ → ℂ) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (w : ℝ) :
    fourierG (vsF W κ) n w = 1 / (2 * Real.pi) * ∫ u : ℝ,
      ((((1 / 2 : ℝ) : ℂ) + u * I) - 1 / 2) ^ n * kernG W (κ * Real.exp w) (((1 / 2 : ℝ) : ℂ) + u * I) := by
  unfold fourierG vsF kernG
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [half_line_sub]
  rw [cpow_mul_exp hκ]
  have : Complex.exp (w * (u * I)) = Complex.exp (I * u * w) := by congr 1; ring
  rw [this]
  ring

theorem pow_mul_ratio_le {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≤ 2) :
    (1 + x) ^ n * (1 + x) ^ 12 / (1 + x) ^ 16 ≤ ((1 + x) ^ 2)⁻¹ := by
  have h1 : (1 : ℝ) ≤ 1 + x := by linarith
  have hp : 0 < 1 + x := by linarith
  calc (1 + x) ^ n * (1 + x) ^ 12 / (1 + x) ^ 16 ≤ (1 + x) ^ 2 * (1 + x) ^ 12 / (1 + x) ^ 16 := by
        gcongr
    _ = ((1 + x) ^ 2)⁻¹ := by field_simp

/-- **The decay of `V^♯`** (the paper's (A.20), in the form `ThetaRows` uses): for `κ > 0` and a smooth weight
`W` supported in `[α, β] ⊂ (0, ∞)` whose first `16` derivatives are at most `N`, `h(w) = V^♯(κe^w)` is smooth,
and `|h^{(i)}(w)| ≤ C_wN(1 + e^w)^{−1}` for `i ≤ 2`, with `C_w` depending only on `α`, `β` and `κ`. -/
theorem Vsharp_decay {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) {κ : ℝ} (hκ : 0 < κ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ y, y < α ∨ β < y → W y = 0) →
      ∀ N : ℝ, (∀ i ≤ 16, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
      ContDiff ℝ ∞ (fun w => Vsharp W (κ * Real.exp w)) ∧
      ∀ i ≤ 2, ∀ w, ‖iteratedDeriv i (fun w => Vsharp W (κ * Real.exp w)) w‖ ≤
        Cw * N * (1 + Real.exp w) ^ (-(1 : ℝ)) := by
  obtain ⟨C4, hC4, hv4⟩ := mellin_Vstar_decay hα hαβ 4 0 0
  obtain ⟨C16, hC16, hk16⟩ := kernG_bound_gen hα hαβ 16
  set I₂ : ℝ := ∫ u : ℝ, ((1 + |u|) ^ 2)⁻¹ with hI₂
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun u => by positivity
  set A : ℝ := 1 / (2 * Real.pi) * C4 * I₂ with hA
  set B : ℝ := 1 / (2 * Real.pi) * C16 * κ⁻¹ * I₂ with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨2 * (A + B), by positivity, fun W hs hW N hN => ?_⟩
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by norm_num) 0)
  have hc := continuous_vsF hα hW hs.continuous hκ
  have hF := integrable_vsF_moments hα hαβ hW hs hκ
  have heq : (fun w => Vsharp W (κ * Real.exp w)) = fourierG (vsF W κ) 0 :=
    funext fun w => Vsharp_eq_fourierG W hκ w
  refine ⟨heq ▸ contDiff_fourierG hc hF, fun i hi w => ?_⟩
  rw [heq, iteratedDeriv_fourierG hc hF i]
  -- the bound from the line `Re s = 1/2`
  have hleft : ‖fourierG (vsF W κ) i w‖ ≤ A * N := by
    refine (norm_fourierG_le hF i w).trans ?_
    have hdom : ∀ u : ℝ, |u| ^ i * ‖vsF W κ u‖ ≤ 1 / (2 * Real.pi) * C4 * N * ((1 + |u|) ^ 2)⁻¹ := by
      intro u
      have hd := hv4 W hW hs N (fun j hj => hN j (by omega)) ((u : ℂ) * I) (by simp) (by simp)
      have him : ((u : ℂ) * I).im = u := by simp
      rw [him] at hd
      rw [norm_vsF W hκ]
      have hpos : 0 < 1 + |u| := by positivity
      have hu : |u| ^ i ≤ (1 + |u|) ^ 2 :=
        (pow_le_pow_left₀ (abs_nonneg u) (by linarith) i).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg u]) hi)
      calc |u| ^ i * (1 / (2 * Real.pi) * ‖mellin (Vstar W) (u * I)‖)
          ≤ (1 + |u|) ^ 2 * (1 / (2 * Real.pi) * (C4 * N / (1 + |u|) ^ 4)) := by gcongr
        _ = 1 / (2 * Real.pi) * C4 * N * ((1 + |u|) ^ 2)⁻¹ := by field_simp
    calc ∫ u : ℝ, |u| ^ i * ‖vsF W κ u‖ ≤ ∫ u : ℝ, 1 / (2 * Real.pi) * C4 * N * ((1 + |u|) ^ 2)⁻¹ :=
          integral_mono (hF i) (integrable_inv_one_add_abs_sq.const_mul _) hdom
      _ = A * N := by rw [integral_const_mul, hA, hI₂]; ring
  -- the bound from the line `Re s = −1/2`
  have hright : ‖fourierG (vsF W κ) i w‖ ≤ B * N * Real.exp (-w) := by
    set Y := κ * Real.exp w with hY
    have hY0 : 0 < Y := by positivity
    set G : ℂ → ℂ := fun s => (s - 1 / 2) ^ i * kernG W Y s with hG
    have hGd : DifferentiableOn ℂ G (re ⁻¹' Icc (-1 / 2) (1 / 2)) :=
      (((differentiable_id.sub_const _).pow i).differentiableOn.mul
        (differentiableOn_kernG hα hW hs.continuous hY0)).mono fun s hs' => by
          show s.re < 4 / 3; linarith [hs'.2]
    have hsub : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 1 / 2 → ‖s - 1 / 2‖ ≤ 1 + |s.im| := by
      intro s h1 h2
      have := Complex.norm_le_abs_re_add_abs_im (s - 1 / 2)
      have e1 : |(s - 1 / 2).re| ≤ 1 := by simp; rw [abs_le]; constructor <;> linarith
      have e2 : (s - 1 / 2).im = s.im := by simp
      rw [e2] at this
      linarith
    have hGb : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 1 / 2 →
        ‖G s‖ ≤ C16 * N * (Y ^ (-1 : ℝ) + 1) * (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
      intro s h1 h2
      have hk := hk16 W hW hs N hN Y hY0 s (by linarith) h2
      have hYe : Y ^ (s.re - 1 / 2) ≤ Y ^ (-1 : ℝ) + 1 := by
        rcases le_or_gt Y 1 with h | h
        · have := Real.rpow_le_rpow_of_exponent_ge hY0 h (by linarith : -1 ≤ s.re - 1 / 2)
          linarith
        · have := Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith : s.re - 1 / 2 ≤ 0)
          linarith [Real.rpow_nonneg hY0.le (-1 : ℝ)]
      simp only [hG]
      rw [norm_mul, norm_pow]
      have hx : 0 ≤ |s.im| := abs_nonneg _
      calc ‖s - 1 / 2‖ ^ i * ‖kernG W Y s‖
          ≤ (1 + |s.im|) ^ i * (C16 * N * Y ^ (s.re - 1 / 2) * (1 + |s.im|) ^ 12 / (1 + |s.im|) ^ 16) := by
            gcongr; exact hsub s h1 h2
        _ = C16 * N * Y ^ (s.re - 1 / 2) * ((1 + |s.im|) ^ i * (1 + |s.im|) ^ 12 / (1 + |s.im|) ^ 16) := by
            ring
        _ ≤ C16 * N * (Y ^ (-1 : ℝ) + 1) * ((1 + |s.im|) ^ 2)⁻¹ := by
            gcongr
            exact pow_mul_ratio_le hx hi
        _ ≤ _ := by gcongr; exact inv_one_add_sq_le_rpow hx
    have hshift := vertical_shift (G := G) (a := -1 / 2) (b := 1 / 2) (by norm_num) hGd hGb
    rw [fourierG_eq_line W hκ i w, ← hY]
    change ‖1 / (2 * Real.pi) * ∫ u : ℝ, G (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤ _
    rw [← hshift]
    have hline : ∀ u : ℝ, ‖G (((-1 / 2 : ℝ) : ℂ) + u * I)‖ ≤ C16 * N * Y ^ (-1 : ℝ) * ((1 + |u|) ^ 2)⁻¹ := by
      intro u
      have hk := hk16 W hW hs N hN Y hY0 (((-1 / 2 : ℝ) : ℂ) + u * I) (by simp; norm_num) (by simp; norm_num)
      have hre : (((-1 / 2 : ℝ) : ℂ) + u * I).re - 1 / 2 = -1 := by simp; norm_num
      have him : (((-1 / 2 : ℝ) : ℂ) + u * I).im = u := by simp
      rw [hre, him] at hk
      have hs1 := hsub (((-1 / 2 : ℝ) : ℂ) + u * I) (by simp) (by simp; norm_num)
      rw [him] at hs1
      simp only [hG]
      rw [norm_mul, norm_pow]
      calc ‖(((-1 / 2 : ℝ) : ℂ) + u * I) - 1 / 2‖ ^ i * ‖kernG W Y (((-1 / 2 : ℝ) : ℂ) + u * I)‖
          ≤ (1 + |u|) ^ i * (C16 * N * Y ^ (-1 : ℝ) * (1 + |u|) ^ 12 / (1 + |u|) ^ 16) := by gcongr
        _ = C16 * N * Y ^ (-1 : ℝ) * ((1 + |u|) ^ i * (1 + |u|) ^ 12 / (1 + |u|) ^ 16) := by ring
        _ ≤ _ := by
            gcongr
            exact pow_mul_ratio_le (abs_nonneg u) hi
    have hYm : Y ^ (-1 : ℝ) = κ⁻¹ * Real.exp (-w) := by
      rw [Real.rpow_neg_one, hY, mul_inv, Real.exp_neg]
    rw [norm_mul]
    have h2π : ‖(1 : ℂ) / (2 * Real.pi)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [h2π]
    calc 1 / (2 * Real.pi) * ‖∫ u : ℝ, G (((-1 / 2 : ℝ) : ℂ) + u * I)‖
        ≤ 1 / (2 * Real.pi) * ∫ u : ℝ, C16 * N * Y ^ (-1 : ℝ) * ((1 + |u|) ^ 2)⁻¹ := by
          gcongr
          exact norm_integral_le_of_norm_le (integrable_inv_one_add_abs_sq.const_mul _)
            (Eventually.of_forall hline)
      _ = B * N * Real.exp (-w) := by rw [integral_const_mul, hYm, hB, hI₂]; ring
  -- combine
  rw [Real.rpow_neg_one]
  have hpos : 0 < 1 + Real.exp w := by positivity
  rcases le_or_gt w 0 with hw | hw
  · have h1 : 1 + Real.exp w ≤ 2 := by linarith [Real.exp_le_one_iff.2 hw]
    calc ‖fourierG (vsF W κ) i w‖ ≤ A * N := hleft
      _ ≤ 2 * (A + B) * N * (1 + Real.exp w)⁻¹ := by
          rw [show 2 * (A + B) * N * (1 + Real.exp w)⁻¹ = (A + B) * N * (2 / (1 + Real.exp w)) by ring]
          have : 1 ≤ 2 / (1 + Real.exp w) := by rw [le_div_iff₀ hpos]; linarith
          nlinarith [mul_nonneg hB0 hN0, mul_nonneg hA0 hN0]
  · have h1 : 1 + Real.exp w ≤ 2 * Real.exp w := by linarith [Real.one_lt_exp_iff.2 hw]
    calc ‖fourierG (vsF W κ) i w‖ ≤ B * N * Real.exp (-w) := hright
      _ ≤ 2 * (A + B) * N * (1 + Real.exp w)⁻¹ := by
          have he : Real.exp (-w) ≤ 2 * (1 + Real.exp w)⁻¹ := by
            rw [Real.exp_neg, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos w) hpos]
            linarith
          calc B * N * Real.exp (-w) ≤ B * N * (2 * (1 + Real.exp w)⁻¹) := by
                gcongr
            _ = 2 * B * N * (1 + Real.exp w)⁻¹ := by ring
            _ ≤ 2 * (A + B) * N * (1 + Real.exp w)⁻¹ := by
                gcongr
                linarith

end Eis

end

#print axioms Eis.exists_deriv_bounds
#print axioms Eis.norm_cexp_I_mul
#print axioms Eis.hasDerivAt_fourierG
#print axioms Eis.iteratedDeriv_fourierG
#print axioms Eis.contDiff_fourierG
#print axioms Eis.norm_fourierG_le
#print axioms Eis.kernG_bound_gen
#print axioms Eis.cpow_mul_exp
#print axioms Eis.half_line_sub
#print axioms Eis.Vsharp_eq_fourierG
#print axioms Eis.continuous_vsF
#print axioms Eis.norm_vsF
#print axioms Eis.vsF_dom
#print axioms Eis.integrable_vsF_moments
#print axioms Eis.fourierG_eq_line
#print axioms Eis.pow_mul_ratio_le
#print axioms Eis.Vsharp_decay
