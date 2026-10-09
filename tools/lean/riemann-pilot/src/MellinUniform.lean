import MellinSeparation
import EisensteinMeanSquareDual

/-! # Separating variables uniformly in the weight (round 317)

S5c-1 in round 316's plan. Round 302's Mellin separation takes its constants from the Mellin
coefficient of the given weight `W₀`. The companion paper's Lemma B.2 bounds the same quantities by
`‖𝒦_r‖_{C^{2m+4}}`, uniformly in the kernel, and its transfer estimate (Proposition 5.4, displayed in
round 315 as `TransferEstimate`) chooses its constant before the weight. This file makes the constants
depend on the weight only through a bound on its derivatives.

* **The Mellin coefficient, explicitly** (`expSchwartz`, `mellin_expSchwartz`): `W(y) = ∫ 𝓕h(t)·y^{2πit}
  dt` for `y > 0` with `h(v) = W(e^v)`. **Its decay** (`norm_fourier_expSchwartz_le`):
  `|𝓕h(t)|(1+|t|)^q ≤ coeffConst(α, β, q)·N` when the first `q` derivatives of `W` are bounded by `N`.
  The proof uses `|2πt|^q|𝓕h(t)| = |𝓕(h^{(q)})(t)| ≤ ∫|h^{(q)}|` (Mathlib's `Real.fourier_iteratedDeriv`)
  and `|h^{(q)}| ≤ q!·N·max(1, β)^q` on `[log α, log β]` (Faà di Bruno, Mathlib's
  `norm_iteratedFDeriv_comp_le`). Hence `∫|𝓕h(t)|(1+|t|)^k dt ≤ π·coeffConst(α, β, k+2)·N`
  (`integral_fourier_expSchwartz_le`).
* **Dilated weights** (`dilated_meanSquare_unif`): round 302's `dilated_meanSquare` with constant
  `K·N_W²` for a bound `N_W` on the first `2J+2` derivatives of `W₀`. Its input, the same bound with the
  coefficient as data (`dilated_meanSquare_of_coeff`), is in `MellinSeparation.lean` since round 332.
* **The bilinear form with the dual kernel** (`bilinear_dual_bound_unif`): round 306's two-family
  `bilinear_dual_bound₂` with constant `K·N_W²`. Its input, the same bound from the two dilated bounds
  on `Re s = σ` (`bilinear_dual_bound_of_dilated`), is in `MellinSeparation.lean` since round 332.
* **The weight `x^{−1/2}W(x)`** (`W0c`, `W0c_unif`): smooth, with its first `q` derivatives bounded by
  `C·N`, `C` depending only on `[α, β]` and `q` (Leibniz with a fixed bump, `iteratedDeriv_mul_fixed_le`).
-/

open Complex MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace ContDiff SchwartzMap Nat ComplexConjugate

noncomputable section

namespace MellinSep

/-! ### The Mellin coefficient of a compactly supported weight, explicitly -/

/-- `v ↦ W(e^v)` has compact support in `[log α, log β]` when `W` vanishes outside `[α, β]`. -/
theorem expComp_eq_zero {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α)
    (hs : ∀ x, x < α ∨ β < x → W x = 0) {v : ℝ} (hv : v < Real.log α ∨ Real.log β < v)
    (hβ : 0 < β) : W (Real.exp v) = 0 := by
  apply hs
  rcases hv with hv | hv
  · left
    have := Real.exp_lt_exp.2 hv
    rwa [Real.exp_log hα] at this
  · right
    have := Real.exp_lt_exp.2 hv
    rwa [Real.exp_log hβ] at this

theorem expComp_hasCompactSupport {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hs : ∀ x, x < α ∨ β < x → W x = 0) :
    HasCompactSupport (fun v => W (Real.exp v)) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  refine HasCompactSupport.intro (isCompact_Icc (a := Real.log α) (b := Real.log β))
    fun v hv => ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hv
  exact expComp_eq_zero hα hs hv hβ

/-- The `q`-th derivative of `v ↦ W(e^v)` is at most `q!·N·D^q` where `e^v ≤ D`, `D ≥ 1`, if the first
`q` derivatives of `W` are bounded by `N` (Faà di Bruno, Mathlib's `norm_iteratedFDeriv_comp_le`). -/
theorem norm_iteratedDeriv_expComp_le {W : ℝ → ℂ} (hW : ContDiff ℝ ∞ W) {q : ℕ} {N : ℝ}
    (hN : ∀ j ≤ q, ∀ y, ‖iteratedDeriv j W y‖ ≤ N) {D : ℝ} (hD : 1 ≤ D) {v : ℝ}
    (hv : Real.exp v ≤ D) :
    ‖iteratedDeriv q (fun v => W (Real.exp v)) v‖ ≤ q ! * N * D ^ q := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine norm_iteratedFDeriv_comp_le (g := W) (f := Real.exp) hW Real.contDiff_exp
    (nat_le_infty q) v (fun j hj => ?_) (fun j hj1 hj2 => ?_)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hN j hj _
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos v)]
    calc Real.exp v ≤ D := hv
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ j := pow_le_pow_right₀ hD hj1

/-- The derivatives of `v ↦ W(e^v)` vanish outside `[log α, log β]`. -/
theorem iteratedDeriv_expComp_eq_zero {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hs : ∀ x, x < α ∨ β < x → W x = 0) (q : ℕ) {v : ℝ}
    (hv : v < Real.log α ∨ Real.log β < v) :
    iteratedDeriv q (fun v => W (Real.exp v)) v = 0 := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hev : (fun v => W (Real.exp v)) =ᶠ[nhds v] fun _ => (0 : ℂ) := by
    rcases hv with hv | hv
    · exact Filter.eventuallyEq_of_mem (Iio_mem_nhds hv) fun w hw =>
        expComp_eq_zero hα hs (Or.inl hw) hβ
    · exact Filter.eventuallyEq_of_mem (Ioi_mem_nhds hv) fun w hw =>
        expComp_eq_zero hα hs (Or.inr hw) hβ
  rw [iteratedDeriv_eq_iteratedFDeriv, (hev.iteratedFDeriv ℝ q).eq_of_nhds,
    iteratedFDeriv_fun_zero]
  rfl

/-- `∫ |(W ∘ exp)^{(q)}| ≤ (log β − log α)·q!·N·max(1, β)^q`. -/
theorem integral_norm_iteratedDeriv_expComp_le {W : ℝ → ℂ} (hW : ContDiff ℝ ∞ W) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hs : ∀ x, x < α ∨ β < x → W x = 0) {q : ℕ} {N : ℝ}
    (hN : ∀ j ≤ q, ∀ y, ‖iteratedDeriv j W y‖ ≤ N) :
    ∫ v, ‖iteratedDeriv q (fun v => W (Real.exp v)) v‖ ≤
      (Real.log β - Real.log α) * (q ! * N * (max 1 β) ^ q) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hD : 1 ≤ max 1 β := le_max_left _ _
  have hlog : Real.log α ≤ Real.log β := Real.log_le_log hα hαβ
  set B := q ! * N * (max 1 β) ^ q with hB
  have hzero : ∀ v ∉ Icc (Real.log α) (Real.log β),
      ‖iteratedDeriv q (fun v => W (Real.exp v)) v‖ = 0 := by
    intro v hv
    simp only [Set.mem_Icc, not_and_or, not_le] at hv
    rw [iteratedDeriv_expComp_eq_zero hα hαβ hs q hv, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hle : ∀ v ∈ Icc (Real.log α) (Real.log β),
      ‖iteratedDeriv q (fun v => W (Real.exp v)) v‖ ≤ B := by
    intro v hv
    refine norm_iteratedDeriv_expComp_le hW hN hD ?_
    calc Real.exp v ≤ Real.exp (Real.log β) := Real.exp_le_exp.2 hv.2
      _ = β := Real.exp_log hβ
      _ ≤ max 1 β := le_max_right _ _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hle _ ⟨le_rfl, hlog⟩)
  calc ∫ v in Icc (Real.log α) (Real.log β), ‖iteratedDeriv q (fun v => W (Real.exp v)) v‖
      ≤ ∫ _v in Icc (Real.log α) (Real.log β), B := by
        refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Icc hle
        refine Continuous.integrableOn_Icc ?_
        exact ((hW.comp Real.contDiff_exp).continuous_iteratedDeriv q (nat_le_infty q)).norm
    _ = (Real.log β - Real.log α) * B := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]

/-- The Schwartz function `v ↦ W(e^v)`. -/
def expSchwartz (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hs : ∀ x, x < α ∨ β < x → W x = 0) : 𝓢(ℝ, ℂ) :=
  (expComp_hasCompactSupport hα hαβ hs).toSchwartzMap (hW.comp Real.contDiff_exp)

theorem expSchwartz_apply (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hs : ∀ x, x < α ∨ β < x → W x = 0) (v : ℝ) :
    expSchwartz W hW hα hαβ hs v = W (Real.exp v) := rfl

/-- **The Mellin representation with its coefficient named**: `W(y) = ∫ 𝓕h(t)·y^{2πit} dt` for `y > 0`,
`h(v) = W(e^v)`. -/
theorem mellin_expSchwartz (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hs : ∀ x, x < α ∨ β < x → W x = 0) (y : ℝ) (hy : 0 < y) :
    W y = ∫ t : ℝ, (𝓕 (expSchwartz W hW hα hαβ hs)) t *
      ((y : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
  have e := log_fourier_inversion (expSchwartz W hW hα hαβ hs) y hy
  have e2 : expSchwartz W hW hα hαβ hs (Real.log y) = W y := by
    rw [expSchwartz_apply, Real.exp_log hy]
  rw [← e2, e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  rw [SchwartzMap.fourier_coe]

/-- **The Mellin coefficient decays at the rate of the derivative bounds**:
`|𝓕h(t)|·(1+|t|)^q ≤ 2^q(log β − log α)(1 + q!·max(1,β)^q/(2π)^q)·N` if the first `q` derivatives of
`W` are bounded by `N`. -/
theorem norm_fourier_expSchwartz_le (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hs : ∀ x, x < α ∨ β < x → W x = 0) {q : ℕ} {N : ℝ}
    (hN : ∀ j ≤ q, ∀ y, ‖iteratedDeriv j W y‖ ≤ N) (t : ℝ) :
    ‖(𝓕 (expSchwartz W hW hα hαβ hs)) t‖ * (1 + |t|) ^ q ≤
      2 ^ q * ((Real.log β - Real.log α) *
        (1 + q ! * (max 1 β) ^ q / (2 * Real.pi) ^ q)) * N := by
  set h := expSchwartz W hW hα hαβ hs with hhdef
  set f : ℝ → ℂ := fun v => W (Real.exp v) with hf
  have hfc : ContDiff ℝ ∞ f := hW.comp Real.contDiff_exp
  have hfs : HasCompactSupport f := expComp_hasCompactSupport hα hαβ hs
  have hlog : Real.log α ≤ Real.log β := Real.log_le_log hα hαβ
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0)
  have hcoe : (𝓕 h) t = 𝓕 f t := by rw [SchwartzMap.fourier_coe]; rfl
  -- the derivatives of `f` are integrable
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n f) := by
    intro n
    refine (hfc.continuous_iteratedDeriv n (nat_le_infty n)).integrable_of_hasCompactSupport ?_
    have : iteratedDeriv n f = (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ =>
        L (fun _ => 1)) ∘ iteratedFDeriv ℝ n f := by
      funext x; simp [iteratedDeriv_eq_iteratedFDeriv]
    rw [this]
    exact (hfs.iteratedFDeriv n).comp_left (by simp)
  -- `|𝓕f(t)| ≤ ∫|f|` and `|2πt|^q·|𝓕f(t)| ≤ ∫|f^{(q)}|`
  have h0 : ‖𝓕 f t‖ ≤ (Real.log β - Real.log α) * N := by
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
    have := integral_norm_iteratedDeriv_expComp_le hW hα hαβ hs (q := 0)
      (fun j hj y => hN j (le_trans hj (Nat.zero_le _)) y)
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul,
      mul_one] at this
    exact this
  have hq : ‖(2 * Real.pi * t : ℝ)‖ ^ q * ‖𝓕 f t‖ ≤
      (Real.log β - Real.log α) * (q ! * N * (max 1 β) ^ q) := by
    have e := congrFun (Real.fourier_iteratedDeriv (N := (q : ℕ∞))
      (hfc.of_le (by exact_mod_cast le_top)) (fun n _ => hint n) le_rfl) t
    have hn : ‖𝓕 (iteratedDeriv q f) t‖ ≤ ∫ v, ‖iteratedDeriv q f v‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    rw [e, norm_smul, norm_pow] at hn
    have h2 : ‖(2 * ↑Real.pi * I * (t : ℂ))‖ = ‖(2 * Real.pi * t : ℝ)‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_mul, abs_two]
      ring
    rw [h2] at hn
    exact hn.trans (integral_norm_iteratedDeriv_expComp_le hW hα hαβ hs hN)
  rw [hcoe]
  -- combine: `(1+|t|)^q ≤ 2^q(1 + |t|^q)`
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpow : (1 + |t|) ^ q ≤ 2 ^ q * (1 + |t| ^ q) := by
    rcases le_total |t| 1 with ht | ht
    · calc (1 + |t|) ^ q ≤ (2 : ℝ) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
        _ ≤ 2 ^ q * (1 + |t| ^ q) := by
            have : 0 ≤ |t| ^ q := by positivity
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) q]
    · calc (1 + |t|) ^ q ≤ (2 * |t|) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
        _ = 2 ^ q * |t| ^ q := mul_pow _ _ _
        _ ≤ 2 ^ q * (1 + |t| ^ q) := by
            have : 0 ≤ (2 : ℝ) ^ q := by positivity
            nlinarith
  have htq : |t| ^ q * ‖𝓕 f t‖ ≤
      (Real.log β - Real.log α) * (q ! * N * (max 1 β) ^ q) / (2 * Real.pi) ^ q := by
    rw [le_div_iff₀ (by positivity)]
    have e1 : ‖(2 * Real.pi * t : ℝ)‖ ^ q = (2 * Real.pi) ^ q * |t| ^ q := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpi, mul_pow]
    rw [e1] at hq
    linarith
  have hL0 : 0 ≤ Real.log β - Real.log α := by linarith
  calc ‖𝓕 f t‖ * (1 + |t|) ^ q ≤ ‖𝓕 f t‖ * (2 ^ q * (1 + |t| ^ q)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = 2 ^ q * (‖𝓕 f t‖ + |t| ^ q * ‖𝓕 f t‖) := by ring
    _ ≤ 2 ^ q * ((Real.log β - Real.log α) * N +
          (Real.log β - Real.log α) * (q ! * N * (max 1 β) ^ q) / (2 * Real.pi) ^ q) := by
        gcongr
    _ = _ := by field_simp

/-- A decay bound `|c(t)|(1+|t|)^{k+2} ≤ B` gives `∫|c(t)|(1+|t|)^k dt ≤ πB`. -/
theorem integral_norm_mul_le_pi (c : 𝓢(ℝ, ℂ)) {k : ℕ} {B : ℝ}
    (hB : ∀ t, ‖c t‖ * (1 + |t|) ^ (k + 2) ≤ B) :
    ∫ t, ‖c t‖ * (1 + |t|) ^ k ≤ B * Real.pi := by
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0)
  have hpt : ∀ t, ‖c t‖ * (1 + |t|) ^ k ≤ B * (1 + t ^ 2)⁻¹ := by
    intro t
    have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have h2 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have h3 := hB t
    rw [le_mul_inv_iff₀ h1]
    calc ‖c t‖ * (1 + |t|) ^ k * (1 + t ^ 2) ≤ ‖c t‖ * (1 + |t|) ^ k * (1 + |t|) ^ 2 := by
          gcongr
      _ = ‖c t‖ * (1 + |t|) ^ (k + 2) := by ring
      _ ≤ B := h3
  calc ∫ t, ‖c t‖ * (1 + |t|) ^ k ≤ ∫ t, B * (1 + t ^ 2)⁻¹ :=
        integral_mono (integrable_norm_mul_one_add_pow c k) (integrable_inv_one_add_sq.const_mul B)
          hpt
    _ = B * Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- The constant `2^q(log β − log α)(1 + q!·max(1,β)^q/(2π)^q)` of `norm_fourier_expSchwartz_le`. -/
def coeffConst (α β : ℝ) (q : ℕ) : ℝ :=
  2 ^ q * ((Real.log β - Real.log α) * (1 + q ! * (max 1 β) ^ q / (2 * Real.pi) ^ q))

theorem coeffConst_nonneg {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (q : ℕ) :
    0 ≤ coeffConst α β q := by
  unfold coeffConst
  have : Real.log α ≤ Real.log β := Real.log_le_log hα hαβ
  have h2 : 0 ≤ Real.log β - Real.log α := by linarith
  positivity

/-- **The Mellin coefficient's weighted `L¹` norm is linear in the derivative bound**:
`∫|𝓕h(t)|(1+|t|)^k dt ≤ π·coeffConst(α, β, k+2)·N` if the first `k+2` derivatives of `W` are bounded
by `N`. -/
theorem integral_fourier_expSchwartz_le (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hs : ∀ x, x < α ∨ β < x → W x = 0) {k : ℕ} {N : ℝ}
    (hN : ∀ j ≤ k + 2, ∀ y, ‖iteratedDeriv j W y‖ ≤ N) :
    ∫ t, ‖(𝓕 (expSchwartz W hW hα hαβ hs)) t‖ * (1 + |t|) ^ k ≤
      coeffConst α β (k + 2) * N * Real.pi :=
  integral_norm_mul_le_pi _ fun t => norm_fourier_expSchwartz_le W hW hα hαβ hs hN t

/-! ### Dilated weights with a given Mellin coefficient -/

/-- **Mean square of dilated weights, uniformly in the weight**: the constant of round 302's
`dilated_meanSquare` is `K·N_W²` for a bound `N_W` on the first `2J+2` derivatives of `W₀`, with `K`
depending only on `[α, β]`, `V`, `[ρ₀, ρ₁]`, `A` and `J`. -/
theorem dilated_meanSquare_unif {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (V : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Ioi 0) {ρ0 ρ1 : ℝ}
    (hρ0 : 0 < ρ0) (hV1 : ∀ y, α / ρ1 ≤ y → y ≤ β / ρ0 → V y = 1) (A : ℝ) (J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W0 : ℝ → ℂ), ContDiff ℝ ∞ W0 → (∀ y, y < α ∨ β < y → W0 y = 0) →
      ∀ NW : ℝ, (∀ j ≤ 2 * J + 2, ∀ y, ‖iteratedDeriv j W0 y‖ ≤ NW) →
      ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, ρ0 ≤ ρ r ∧ ρ r ≤ ρ1) → ∀ s : ℂ, |s.re| ≤ A →
      ∑ r ∈ T, ‖∑ n ∈ C, a r n * (W0 (ρ r * x n) * (x n : ℂ) ^ s)‖ ^ 2 ≤
        K * NW ^ 2 * M * (1 + ‖s‖) ^ (2 * J) := by
  obtain ⟨Ctf, hCtf0, hD⟩ := dilated_meanSquare_of_coeff V hV hVc hVp hρ0 hV1 A J
  set c0 := coeffConst α β 2 * Real.pi with hc0
  set c1 := coeffConst α β (2 * J + 2) * Real.pi with hc1
  have hc00 : 0 ≤ c0 := mul_nonneg (coeffConst_nonneg hα hαβ 2) Real.pi_pos.le
  have hc10 : 0 ≤ c1 := mul_nonneg (coeffConst_nonneg hα hαβ _) Real.pi_pos.le
  refine ⟨c0 * (Ctf ^ 2 * 64 ^ J * c1), by positivity,
    fun W0 hW0 hW0s NW hNW => fun T C a x hx M hM hyp ρ hρ s hs => ?_⟩
  set c := 𝓕 (expSchwartz W0 hW0 hα hαβ hW0s) with hcdef
  have hrep := mellin_expSchwartz W0 hW0 hα hαβ hW0s
  have hNW0 : 0 ≤ NW := (norm_nonneg _).trans (hNW 0 (Nat.zero_le _) 0)
  have hI0 : ∫ t, ‖c t‖ ≤ c0 * NW := by
    have h := integral_fourier_expSchwartz_le W0 hW0 hα hαβ hW0s (k := 0)
      (fun j hj y => hNW j (by omega) y)
    simp only [pow_zero, mul_one] at h
    calc ∫ t, ‖c t‖ ≤ coeffConst α β (0 + 2) * NW * Real.pi := h
      _ = c0 * NW := by rw [hc0]; ring
  have hI1 : ∫ t, ‖c t‖ * (1 + |t|) ^ (2 * J) ≤ c1 * NW := by
    have h := integral_fourier_expSchwartz_le W0 hW0 hα hαβ hW0s (k := 2 * J) hNW
    calc ∫ t, ‖c t‖ * (1 + |t|) ^ (2 * J) ≤ coeffConst α β (2 * J + 2) * NW * Real.pi := h
      _ = c1 * NW := by rw [hc1]; ring
  have hmain := hD W0 hW0s c hrep T C a x hx M hM hyp ρ hρ s hs
  refine hmain.trans ?_
  have hA0 : 0 ≤ ∫ t, ‖c t‖ := integral_nonneg fun t => norm_nonneg _
  have hA1 : 0 ≤ ∫ t, ‖c t‖ * (1 + |t|) ^ (2 * J) := integral_nonneg fun t => by positivity
  calc (∫ t, ‖c t‖) * (Ctf ^ 2 * 64 ^ J * ∫ t, ‖c t‖ * (1 + |t|) ^ (2 * J)) * M *
        (1 + ‖s‖) ^ (2 * J)
      ≤ (c0 * NW) * (Ctf ^ 2 * 64 ^ J * (c1 * NW)) * M * (1 + ‖s‖) ^ (2 * J) := by gcongr
    _ = c0 * (Ctf ^ 2 * 64 ^ J * c1) * NW ^ 2 * M * (1 + ‖s‖) ^ (2 * J) := by ring

/-- **The bilinear form with the dual kernel, uniformly in the weight**: round 306's
`bilinear_dual_bound₂` with constant `K·N_W²`, for a bound `N_W` on the first `2J+2` derivatives of
`W₀`, with `K` depending only on `[α, β]`, `V`, `[ρ₀, ρ₁]`, `J`, `G` and `σ`. It plays the role of the
companion paper's Lemma B.2, whose bound `√(M₁M₂)·sup_r‖𝒦_r‖_{C^{2m+4}}` is likewise uniform in the
kernels, for kernels of this shape. -/
theorem bilinear_dual_bound_unif {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (V : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (hVp : tsupport V ⊆ Ioi 0) {ρ0 ρ1 : ℝ}
    (hρ0 : 0 < ρ0) (hV1 : ∀ y, α / ρ1 ≤ y → y ≤ β / ρ0 → V y = 1) (J : ℕ)
    (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ n : ℕ, ∃ C, ∀ ρ, ‖iteratedFDeriv ℝ n G ρ‖ ≤ C)
    {R : ℝ} (hR : ∀ ρ, R ≤ ρ → G ρ = 0) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W0 : ℝ → ℂ), ContDiff ℝ ∞ W0 → (∀ y, y < α ∨ β < y → W0 y = 0) →
      ∀ NW : ℝ, (∀ j ≤ 2 * J + 2, ∀ y, ‖iteratedDeriv j W0 y‖ ≤ NW) →
      ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a b : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, b r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, ρ0 ≤ ρ r ∧ ρ r ≤ ρ1) →
      ∀ w : ι → ℂ, (∀ r ∈ T, ‖w r‖ ≤ 1) → ∀ (Ar : ι → ℝ) (Amin : ℝ), 0 < Amin →
      (∀ r ∈ T, Amin ≤ Ar r) →
      ‖∑ r ∈ T, w r * ∑ n1 ∈ C, ∑ n2 ∈ C, a r n1 * conj (b r n2) *
          (W0 (ρ r * x n1) * conj (W0 (ρ r * x n2)) *
            G (Real.sqrt (Ar r / (x n1 * x n2))))‖ ≤ K * NW ^ 2 * Amin ^ (-σ) * M := by
  obtain ⟨Kd, hKd0, hKd⟩ := dilated_meanSquare_unif hα hαβ V hV hVc hVp hρ0 hV1 σ J
  obtain ⟨Kg, hKg0, hKg⟩ := bilinear_dual_bound_of_dilated J G hG hGb hR hσ
  refine ⟨Kg * Kd, mul_nonneg hKg0 hKd0, fun W0 hW0 hW0s NW hNW =>
    fun T C a b x hx M hM hyp hypb ρ hρ w hw Ar Amin hAmin hAr => ?_⟩
  have hs : ∀ s : ℂ, s.re = σ → |s.re| ≤ σ := fun s hs => by rw [hs, abs_of_pos hσ]
  have h := hKg W0 T C a b x hx ρ (Kd * NW ^ 2 * M)
    (fun s hsr => hKd W0 hW0 hW0s NW hNW T C a x hx M hM hyp ρ hρ s (hs s hsr))
    (fun s hsr => hKd W0 hW0 hW0s NW hNW T C b x hx M hM hypb ρ hρ s (hs s hsr))
    w hw Ar Amin hAmin hAr
  calc _ ≤ Kg * (Kd * NW ^ 2 * M) * Amin ^ (-σ) := h
    _ = Kg * Kd * NW ^ 2 * Amin ^ (-σ) * M := by ring

/-- **Leibniz with a fixed factor**: for a fixed smooth compactly supported `ψ` there is `C` with
`‖(Wψ)^{(j)}‖ ≤ C·N` for `j ≤ q`, whenever the first `q` derivatives of `W` are bounded by `N`. -/
theorem iteratedDeriv_mul_fixed_le (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (q : ℕ) :
    ∃ Cψ : ℝ, 0 ≤ Cψ ∧ ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → ∀ N : ℝ,
      (∀ j ≤ q, ∀ y, ‖iteratedDeriv j W y‖ ≤ N) →
      ∀ j ≤ q, ∀ y, ‖iteratedDeriv j (fun x => W x * ψ x) y‖ ≤ Cψ * N := by
  obtain ⟨Kψ, hKψ0, hKψ⟩ := hψc.exists_bound_iteratedFDeriv hψ q
  refine ⟨2 ^ q * Kψ, by positivity, fun W hW N hN j hj y => ?_⟩
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0)
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_mul_le hW hψ y (nat_le_infty j)).trans ?_
  calc ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ * ‖iteratedFDeriv ℝ (j - i) ψ y‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * N * Kψ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 : ‖iteratedFDeriv ℝ i W y‖ ≤ N := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hN i (hi'.trans hj) y
        have h2 : ‖iteratedFDeriv ℝ (j - i) ψ y‖ ≤ Kψ := hKψ (j - i) (by omega) y
        gcongr
    _ = (2 : ℝ) ^ j * N * Kψ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ q * Kψ * N := by
        have : (2 : ℝ) ^ j ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hj
        have : 0 ≤ N * Kψ := mul_nonneg hN0 hKψ0
        nlinarith

/-- The weight `W₀(x) = x^{−1/2}W(x)` of the companion paper's kernels, for complex `W`. -/
def W0c (W : ℝ → ℂ) (x : ℝ) : ℂ := W x / ((Real.sqrt x : ℝ) : ℂ)

theorem W0c_eq_zero {W : ℝ → ℂ} {α β : ℝ} (hW : ∀ x, x < α ∨ β < x → W x = 0) {x : ℝ}
    (hx : x < α ∨ β < x) : W0c W x = 0 := by
  unfold W0c; rw [hW x hx, zero_div]

/-- **The weight `x^{−1/2}W(x)`, uniformly**: for `0 < α ≤ β` there is `C` such that every smooth `W`
vanishing outside `[α, β]` with its first `q` derivatives bounded by `N` gives a smooth `W₀`,
vanishing outside `[α, β]`, with its first `q` derivatives bounded by `C·N`. -/
theorem W0c_unif {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ x, x < α ∨ β < x → W x = 0) →
      ∀ N : ℝ, (∀ j ≤ q, ∀ y, ‖iteratedDeriv j W y‖ ≤ N) →
      ContDiff ℝ ∞ (W0c W) ∧ ∀ j ≤ q, ∀ y, ‖iteratedDeriv j (W0c W) y‖ ≤ C * N := by
  obtain ⟨V, hV, hVc, hVp, -, hV1⟩ := Eis.exists_bump hα hαβ
  set ψ : ℝ → ℂ := fun x => V x * (x : ℂ) ^ (-(1 / 2 : ℂ)) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := testFun_contDiff V hV hVp _
  have hψc : HasCompactSupport ψ := hVc.mul_right
  obtain ⟨C, hC0, hC⟩ := iteratedDeriv_mul_fixed_le ψ hψ hψc q
  refine ⟨C, hC0, fun W hW hWs N hN => ?_⟩
  have heq : W0c W = fun x => W x * ψ x := by
    funext x
    unfold W0c
    by_cases hx : x < α ∨ β < x
    · rw [hWs x hx]; simp
    · push Not at hx
      have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
      have hVx : V x = 1 := hV1 x (by linarith) hx.2
      have hsq : ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
      simp only [hψdef, hVx, one_mul]
      rw [div_eq_mul_inv, hsq, Complex.cpow_neg]
  rw [heq]
  exact ⟨hW.mul hψ, hC W hW N hN⟩

end MellinSep

end

#print axioms MellinSep.expComp_eq_zero
#print axioms MellinSep.expComp_hasCompactSupport
#print axioms MellinSep.norm_iteratedDeriv_expComp_le
#print axioms MellinSep.iteratedDeriv_expComp_eq_zero
#print axioms MellinSep.integral_norm_iteratedDeriv_expComp_le
#print axioms MellinSep.expSchwartz_apply
#print axioms MellinSep.mellin_expSchwartz
#print axioms MellinSep.norm_fourier_expSchwartz_le
#print axioms MellinSep.integral_norm_mul_le_pi
#print axioms MellinSep.coeffConst_nonneg
#print axioms MellinSep.integral_fourier_expSchwartz_le
#print axioms MellinSep.dilated_meanSquare_unif
#print axioms MellinSep.bilinear_dual_bound_unif
#print axioms MellinSep.iteratedDeriv_mul_fixed_le
#print axioms MellinSep.W0c_eq_zero
#print axioms MellinSep.W0c_unif
