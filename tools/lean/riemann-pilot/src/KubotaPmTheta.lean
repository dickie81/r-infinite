import KubotaPmPair
import KubotaMellin

/-! # The pairing of `P_m(ψ)` with θ (round 431)

S5f-10 of round 360's plan, part 14 (S5f-10f, fourth part). Round 430's next step planned
`⟨P_m(ψ), θ⟩ = ρ(m)·J_ψ(4/3)` with `ρ(m)` independent of `ψ`, for `m = δ₃x ≠ 0`. This round proves it, for
`r > 0`, `Y > 0`, `a = 4π|m|/9`, and `ψ` measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`:

* **`J_ψ` is entire** (`jKer`, a definition; **`jPsi_eq_mellin`** and **`differentiable_jPsi`**, with
  `bkK_le_one`, `measurable_bkK`, `zpow_neg_two_le`, `bkK_isBigO_bot`, `measurable_jKer_integrand`,
  `norm_jKer_integrand_le`, `norm_jKer_le` and `continuousOn_jKer`): `J_ψ(s) = ½·M[G](s − 1)` with
  `G(t) = ∫_0^∞ conj ψ(v)·v^{−2}·e^{−av(t + 1/t)/2} dv` (Fubini), and `|G(t)| ≤ C·e^{−aα(t + 1/t)/2}` for
  `t > 0`, so Mathlib's `mellin_differentiableAt_of_isBigO_rpow_exp` applies at every point.
* **Two profiles** (`besC` and `aPm`, definitions; **`aPm_eq`**, **`differentiableOn_aPm`**, **`tendsto_aPm`**
  and **`inner_pmSer_thetaL_cross`**):
  `A_ψ(s) = ⟨P_m(ψ), ũ_s⟩ − I_m·M_ψ(2 − s) + ⟨P_m(ψ), E(1[Y ≤ v ≤ H]v^s)⟩` with `H = Y + β + 1/α` is
  `(2π/Γ(s))(2π|m|/9)^{s−1}·D_m(s)·J_ψ(s)` for `Re s > 2` with `Im ĥ(s) ≠ 0` (round 430's
  `inner_pmSer_uL_bessel`), is holomorphic on round 427's `U`, and `iε·A_ψ(4/3 + iε) → ⟨P_m(ψ), θ⟩` as
  `ε → 0⁺`. So `A_{ψ₁}J_{ψ₂} − A_{ψ₂}J_{ψ₁}` vanishes on `U` (the identity theorem), and
  `⟨P_m(ψ₁), θ⟩·J_{ψ₂}(4/3) = ⟨P_m(ψ₂), θ⟩·J_{ψ₁}(4/3)`.
* **`ρ(m)`** (`ind12` and `rhoM`, definitions; **`jPsi_ind12_ne_zero`** and **`inner_pmSer_thetaL`**, with
  `bkR_pos`, `measurable_ind12`, `norm_ind12_le`, `ind12_eq_zero` and `memLp_pmSer_ind12`):
  `J_{1_{[1, 2]}}(4/3) = ∫_1^2 v^{−2}K_{1/3}(av) dv > 0`, and with
  `ρ(m) = ⟨P_m(1_{[1, 2]}), θ⟩/J_{1_{[1, 2]}}(4/3)`, `⟨P_m(ψ), θ⟩ = ρ(m)·J_ψ(4/3)`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### `J_ψ` is entire -/

theorem bkK_le_one {x : ℝ} (hx : 0 ≤ x) {t : ℝ} (ht : 0 < t) : bkK x t ≤ 1 := by
  have h := bkK_anti hx ht
  have h0 : bkK 0 t = 1 := by unfold bkK; simp
  linarith

theorem measurable_bkK : Measurable fun p : ℝ × ℝ => bkK p.1 p.2 := by
  unfold bkK
  fun_prop

theorem zpow_neg_two_le {α v : ℝ} (hα : 0 < α) (hv : α ≤ v) : v ^ (-2 : ℤ) ≤ α ^ (-2 : ℤ) := by
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by
    rw [zpow_neg]
    norm_cast
  rw [e, e]
  exact inv_anti₀ (pow_pos hα 2) (pow_le_pow_left₀ hα.le hv 2)

/-- `bkK x t = O(t^{−b})` as `t → 0⁺`, for `x > 0` and every `b` (round 361's `bkK_le_bot`). -/
theorem bkK_isBigO_bot {x : ℝ} (hx : 0 < x) (b : ℝ) :
    (fun t => bkK x t) =O[𝓝[>] 0] fun t : ℝ => t ^ (-b) := by
  have hx2 : 0 < x / 2 := by positivity
  have h1 := (isLittleO_exp_neg_mul_rpow_atTop hx2 b).comp_tendsto tendsto_inv_nhdsGT_zero
  have h2 : ((fun x : ℝ => x ^ b) ∘ fun t : ℝ => t⁻¹) =ᶠ[𝓝[>] 0] fun t => t ^ (-b) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_apply]
    rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]
  refine IsBigO.trans ?_ (h1.isBigO.congr' EventuallyEq.rfl h2)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Real.norm_of_nonneg (bkK_pos x t).le, one_mul, Function.comp_apply,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  exact bkK_le_bot hx ht

/-- The kernel of `J_ψ`: `G(t) = ∫_0^∞ conj ψ(v)·v^{−2}·e^{−av(t + 1/t)/2} dv`. -/
def jKer (a : ℝ) (ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ v in Ioi 0, conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * (bkK (a * v) t : ℂ))

theorem measurable_jKer_integrand {ψ : ℝ → ℂ} (hψ : Measurable ψ) (a t : ℝ) :
    Measurable fun v : ℝ => conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * (bkK (a * v) t : ℂ)) := by
  have hb : Measurable fun v : ℝ => bkK (a * v) t := by
    unfold bkK
    fun_prop
  have hz : Measurable fun v : ℝ => ((v ^ (-2 : ℤ) : ℝ) : ℂ) := by fun_prop
  exact (Complex.continuous_conj.measurable.comp hψ).mul (hz.mul (Complex.measurable_ofReal.comp hb))

theorem norm_jKer_integrand_le {ψ : ℝ → ℂ} {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a) (v : ℝ) {t : ℝ}
    (ht : 0 < t) :
    ‖conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * (bkK (a * v) t : ℂ))‖ ≤
      (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) v * bkK (a * α) t := by
  by_cases hv : v ∈ Icc α β
  · have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
    rw [indicator_of_mem hv, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (bkK_pos _ _).le]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have h1 := zpow_neg_two_le hα hv.1
    have h2 : bkK (a * v) t ≤ bkK (a * α) t := bkK_anti (mul_le_mul_of_nonneg_left hv.1 ha) ht
    calc ‖ψ v‖ * (v ^ (-2 : ℤ) * bkK (a * v) t) ≤ M * (α ^ (-2 : ℤ) * bkK (a * α) t) :=
          mul_le_mul (hM v) (mul_le_mul h1 h2 (bkK_pos _ _).le (by positivity))
            (mul_nonneg (by positivity) (bkK_pos _ _).le) hM0
      _ = M * α ^ (-2 : ℤ) * bkK (a * α) t := by ring
  · rw [indicator_of_notMem hv, hψ0 v hv, map_zero, zero_mul, norm_zero, zero_mul]

theorem norm_jKer_le {ψ : ℝ → ℂ} {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    ‖jKer a ψ t‖ ≤ M * α ^ (-2 : ℤ) * bkK (a * α) t * volume.real (Icc α β) := by
  have hsub : Icc α β ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hα hv.1
  unfold jKer
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    (fun v hv => by rw [hψ0 v hv.2, map_zero, zero_mul])]
  refine norm_setIntegral_le_of_norm_le_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    fun v hv => ?_
  have := norm_jKer_integrand_le hM hψ0 hα ha v ht
  rwa [indicator_of_mem hv] at this

theorem continuousOn_jKer {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {a : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (jKer a ψ) (Ioi 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  unfold jKer
  refine continuousOn_of_dominated
    (bound := fun v => (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) v) ?_ ?_ ?_ ?_
  · intro t _
    exact (measurable_jKer_integrand hψ a t).aestronglyMeasurable
  · intro t ht
    refine Eventually.of_forall fun v => (norm_jKer_integrand_le hM hψ0 hα ha v ht).trans ?_
    have h0 : 0 ≤ (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) v :=
      indicator_nonneg (fun _ _ => by positivity) v
    calc (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) v * bkK (a * α) t
        ≤ (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) v * 1 :=
          mul_le_mul_of_nonneg_left (bkK_le_one (by positivity) ht) h0
      _ = (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) v := mul_one _
  · rw [integrable_indicator_iff measurableSet_Icc]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Icc]
    exact (measure_mono inter_subset_left).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      |>.ne
  · refine Eventually.of_forall fun v => ?_
    exact continuousOn_const.mul (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (bkK_continuousOn (a * v))))

/-- **`J_ψ` as a Mellin transform**: `J_ψ(s) = ½·M[G](s − 1)` with `G = jKer a ψ` (Fubini). -/
theorem jPsi_eq_mellin {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {a : ℝ} (ha : 0 < a) (s : ℂ) :
    jPsi a ψ s = (1 / 2 : ℂ) * mellin (jKer a ψ) (s - 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set f : ℝ → ℝ → ℂ := fun v t => (1 / 2 : ℂ) * (((t : ℝ) : ℂ) ^ (s - 1 - 1) *
      (conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * (bkK (a * v) t : ℂ)))) with hf
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg1 : Integrable (fun v => (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) v)
        (volume.restrict (Ioi (0 : ℝ))) := by
      rw [integrable_indicator_iff measurableSet_Icc]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_Icc]
      exact (measure_mono inter_subset_left).trans_lt
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) |>.ne
    have hg2 : Integrable (fun t : ℝ => t ^ (s.re - 1 - 1) * bkK (a * α) t)
        (volume.restrict (Ioi (0 : ℝ))) := integrableOn_bkR (mul_pos ha hα) (s.re - 1)
    have hm : Measurable (Function.uncurry f) := by
      have hb : Measurable fun p : ℝ × ℝ => bkK (a * p.1) p.2 :=
        measurable_bkK.comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
      have hz : Measurable fun p : ℝ × ℝ => ((p.1 ^ (-2 : ℤ) : ℝ) : ℂ) := by fun_prop
      exact measurable_const.mul (((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul
        ((Complex.continuous_conj.measurable.comp (hψ.comp measurable_fst)).mul
          (hz.mul (Complex.measurable_ofReal.comp hb))))
    refine (hg1.mul_prod hg2).mono' hm.aestronglyMeasurable ?_
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    refine Eventually.of_forall fun p hp => ?_
    have ht : (0 : ℝ) < p.2 := hp.2
    simp only [hf, Function.uncurry_def]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    have hre : (s - 1 - 1).re = s.re - 1 - 1 := by simp
    rw [hre]
    have h1 := norm_jKer_integrand_le hM hψ0 hα ha.le p.1 ht
    have h0 : 0 ≤ (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) p.1 :=
      indicator_nonneg (fun _ _ => by positivity) _
    have hp2 : 0 ≤ p.2 ^ (s.re - 1 - 1) := Real.rpow_nonneg ht.le _
    calc ‖(1 / 2 : ℂ)‖ * (p.2 ^ (s.re - 1 - 1) *
          ‖conj (ψ p.1) * (((p.1 ^ (-2 : ℤ) : ℝ) : ℂ) * (bkK (a * p.1) p.2 : ℂ))‖)
        ≤ 1 * (p.2 ^ (s.re - 1 - 1) *
          ((Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) p.1 * bkK (a * α) p.2)) := by
          refine mul_le_mul (by norm_num) (mul_le_mul_of_nonneg_left h1 hp2) (by positivity)
            (by norm_num)
      _ = (Icc α β).indicator (fun _ => M * α ^ (-2 : ℤ)) p.1 *
          (p.2 ^ (s.re - 1 - 1) * bkK (a * α) p.2) := by ring
  have e1 : jPsi a ψ s = ∫ v in Ioi 0, ∫ t in Ioi 0, f v t := by
    unfold jPsi
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [hf]
    rw [integral_const_mul]
    have e : ∀ t : ℝ, ((t : ℝ) : ℂ) ^ (s - 1 - 1) *
        (conj (ψ v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * (bkK (a * v) t : ℂ))) =
        (conj (ψ v) * ((v ^ (-2 : ℤ) : ℝ) : ℂ)) * (((t : ℝ) : ℂ) ^ (s - 1 - 1) • (bkK (a * v) t : ℂ)) :=
      fun t => by rw [smul_eq_mul]; ring
    simp_rw [e]
    rw [integral_const_mul]
    unfold besselK mellin
    ring
  rw [e1, integral_integral_swap hint]
  unfold mellin jKer
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [hf]
  rw [integral_const_mul, integral_const_mul, smul_eq_mul]

/-- **`J_ψ` is entire**, for `a > 0` and `ψ` measurable and bounded, vanishing outside `[α, β]` with
`α > 0`: `G` decays like `e^{−aαt/2}` at `∞` and faster than every power at `0`, so Mathlib's
`mellin_differentiableAt_of_isBigO_rpow_exp` applies at every point. -/
theorem differentiable_jPsi {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) {a : ℝ} (ha : 0 < a) :
    Differentiable ℂ (jPsi a ψ) := by
  intro s
  have e : jPsi a ψ = fun s => (1 / 2 : ℂ) * mellin (jKer a ψ) (s - 1) :=
    funext (jPsi_eq_mellin hψ hM hψ0 hα ha)
  rw [e]
  refine DifferentiableAt.const_mul ?_ _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hx : 0 < a * α := mul_pos ha hα
  have hx2 : 0 < a * α / 2 := by positivity
  set C := M * α ^ (-2 : ℤ) * volume.real (Icc α β) with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg hM0 (by positivity)) measureReal_nonneg
  have hbd : ∀ t, 0 < t → ‖jKer a ψ t‖ ≤ C * bkK (a * α) t := fun t ht => by
    have := norm_jKer_le hM hψ0 hα ha.le ht
    rw [hCdef]
    linarith
  have hd : DifferentiableAt ℂ (mellin (jKer a ψ)) (s - 1) := by
    refine mellin_differentiableAt_of_isBigO_rpow_exp hx2
      ((continuousOn_jKer hψ hM hψ0 hα ha.le).locallyIntegrableOn measurableSet_Ioi) ?_ ?_
      (b := (s - 1).re - 1) (by linarith)
    · refine IsBigO.of_bound C ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (hbd t ht).trans (mul_le_mul_of_nonneg_left (bkK_le_top hx ht) hC0)
    · have h1 : jKer a ψ =O[𝓝[>] 0] fun t => bkK (a * α) t := by
        refine IsBigO.of_bound C ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [Real.norm_of_nonneg (bkK_pos _ _).le]
        exact hbd t ht
      exact h1.trans (bkK_isBigO_bot hx _)
  have hcomp : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := differentiableAt_id.sub_const 1
  exact DifferentiableAt.comp (g := mellin (jKer a ψ)) s hd hcomp

/-! ### The ratio of two profiles -/

/-- The Bessel factor `(2π/Γ(s))(2π|m|/9)^{s−1}·D_m(s)` of round 430's `inner_pmSer_uL_bessel`. -/
def besC (x : 𝓞 K) (s : ℂ) : ℂ :=
  2 * Real.pi / Gamma s * ((2 * Real.pi * ‖σO (δ3 * x) / 9‖ : ℝ) : ℂ) ^ (s - 1) *
    (∑' c : 𝓞 K, cuspSm (δ3 * x) c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s))

/-- `A_ψ(s) = ⟨y, ũ_s⟩ − I_m·M_ψ(2 − s) + ⟨y, E(1[Y ≤ v ≤ H]v^s)⟩` for `R = 2cosh r − 2`. For `y = P_m(ψ)` and
`H = Y + β + 1/α` it is the Bessel term of round 430's `inner_pmSer_uL_bessel` where that theorem applies
(`aPm_eq`). -/
def aPm (x : 𝓞 K) (r Y : ℝ) (hY : 0 < Y) {H : ℝ} (hYH : Y ≤ H) (ψ : ℝ → ℂ) (y : Lp ℂ 2 (muR rhoG))
    (s : ℂ) : ℂ :=
  inner ℂ y (uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY s) -
    (∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z))) * mellinPsi ψ (2 - s) + inner ℂ y (bandL hY hYH s)

/-- `A_ψ(s) = (2π/Γ(s))(2π|m|/9)^{s−1}·D_m(s)·J_ψ(s)` for `Re s > 2` with `Im ĥ(s) ≠ 0`. -/
theorem aPm_eq {x : 𝓞 K} (hx : x ≠ 0) {r Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ} (hs : 2 < s.re)
    (him : (hhat (2 * Real.cosh r - 2) s).im ≠ 0) :
    aPm x r Y hY (le_band hα hαβ) ψ (hψ2.toLp (pmSer (δ3 * x) ψ)) s =
      besC x s * jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ s := by
  unfold aPm besC
  rw [inner_pmSer_uL_bessel hx (cosh_sub_nonneg r) hY hψ hψ2 hM hψ0 hα hαβ hs him]
  ring

/-- `A_ψ` is holomorphic on round 427's `U = {Re s > 1, 0 < Im s < π/r}`. -/
theorem differentiableOn_aPm (x : 𝓞 K) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {H : ℝ} (hYH : Y ≤ H)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (y : Lp ℂ 2 (muR rhoG)) :
    DifferentiableOn ℂ (aPm x r Y hY hYH ψ y) (domU r) := by
  have hMd := differentiable_mellinPsi hψ hM hψ0 hα
  unfold aPm
  intro s hs
  have him : (hhat (2 * Real.cosh r - 2) s).im ≠ 0 :=
    (im_hhat_pos hr hs.1 hs.2.1 ((lt_div_iff₀ hr).1 hs.2.2)).ne'
  have h1 := differentiableAt_inner_uL hr.le hY y him
  have hc : DifferentiableAt ℂ (fun s : ℂ => 2 - s) s := (differentiableAt_const 2).sub differentiableAt_id
  have h2 : DifferentiableAt ℂ (fun s => mellinPsi ψ (2 - s)) s :=
    DifferentiableAt.comp (g := mellinPsi ψ) s (hMd (2 - s)) hc
  have h3 := differentiable_inner_bandL y hY hYH s
  exact ((h1.sub (h2.const_mul _)).add h3).differentiableWithinAt

/-- **The residue of `A_ψ`**: `iε·A_ψ(4/3 + iε) → ⟨y, θ⟩` as `ε → 0⁺` (round 425's `tendsto_uL_thetaL`). -/
theorem tendsto_aPm (x : 𝓞 K) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {H : ℝ} (hYH : Y ≤ H)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (y : Lp ℂ 2 (muR rhoG)) :
    Tendsto (fun ε : ℝ => (I * ε) * aPm x r Y hY hYH ψ y (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (inner ℂ y (thetaL r Y hY))) := by
  have hMd := differentiable_mellinPsi hψ hM hψ0 hα
  have hγ : Tendsto (fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε) (𝓝[>] 0) (𝓝 ((4 / 3 : ℝ) : ℂ)) := by
    have hc : Continuous fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε := by fun_prop
    have := hc.tendsto 0
    simp only [ofReal_zero, mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hI : Tendsto (fun ε : ℝ => I * (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => I * (ε : ℂ) := by fun_prop
    have := hc.tendsto 0
    simp only [ofReal_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun ε : ℝ => (I * ε) *
      inner ℂ y (uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY (((4 / 3 : ℝ) : ℂ) + I * ε)))
      (𝓝[>] 0) (𝓝 (inner ℂ y (thetaL r Y hY))) := by
    have h := ((innerSL ℂ y).continuous.tendsto _).comp (tendsto_uL_thetaL hr hY)
    refine h.congr fun ε => ?_
    simp only [Function.comp, innerSL_apply_apply, inner_smul_right]
  have hc2 : Tendsto (fun ε : ℝ => 2 - (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (2 - ((4 / 3 : ℝ) : ℂ))) := tendsto_const_nhds.sub hγ
  have h2 : Tendsto (fun ε : ℝ => mellinPsi ψ (2 - (((4 / 3 : ℝ) : ℂ) + I * ε))) (𝓝[>] 0)
      (𝓝 (mellinPsi ψ (2 - ((4 / 3 : ℝ) : ℂ)))) :=
    (hMd _).continuousAt.tendsto.comp hc2
  have h3 : Tendsto (fun ε : ℝ => inner ℂ y (bandL hY hYH (((4 / 3 : ℝ) : ℂ) + I * ε))) (𝓝[>] 0)
      (𝓝 (inner ℂ y (bandL hY hYH ((4 / 3 : ℝ) : ℂ)))) :=
    (differentiable_inner_bandL y hY hYH _).continuousAt.tendsto.comp hγ
  have hc0 : Tendsto (fun _ : ℝ => (∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)))) (𝓝[>] 0)
      (𝓝 (∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)))) := tendsto_const_nhds
  have h := (hL.sub (hI.mul (hc0.mul h2))).add (hI.mul h3)
  simp only [zero_mul, sub_zero, add_zero] at h
  refine h.congr fun ε => ?_
  unfold aPm
  ring

/-- **Two profiles**: for `m = δ₃x ≠ 0`, `r > 0`, `Y > 0`, and profiles `ψ₁`, `ψ₂` measurable and
bounded, vanishing outside `[α_i, β_i]` with `0 < α_i ≤ β_i`,
`⟨P_m(ψ₁), θ⟩·J_{ψ₂}(4/3) = ⟨P_m(ψ₂), θ⟩·J_{ψ₁}(4/3)`: `A_{ψ₁}J_{ψ₂} − A_{ψ₂}J_{ψ₁}` vanishes for
`Re s > 2` (`aPm_eq`), hence on `U` (the identity theorem), and its residue at `4/3` is the difference. -/
theorem inner_pmSer_thetaL_cross {x : 𝓞 K} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y)
    {ψ₁ ψ₂ : ℝ → ℂ} (hψ₁ : Measurable ψ₁) (hψ₂ : Measurable ψ₂)
    (h₁ : MemLp (pmSer (δ3 * x) ψ₁) 2 (muR rhoG)) (h₂ : MemLp (pmSer (δ3 * x) ψ₂) 2 (muR rhoG))
    {M₁ α₁ β₁ M₂ α₂ β₂ : ℝ} (hM₁ : ∀ v, ‖ψ₁ v‖ ≤ M₁) (hM₂ : ∀ v, ‖ψ₂ v‖ ≤ M₂)
    (h0₁ : ∀ v, v ∉ Icc α₁ β₁ → ψ₁ v = 0) (h0₂ : ∀ v, v ∉ Icc α₂ β₂ → ψ₂ v = 0)
    (hα₁ : 0 < α₁) (hαβ₁ : α₁ ≤ β₁) (hα₂ : 0 < α₂) (hαβ₂ : α₂ ≤ β₂) :
    inner ℂ (h₁.toLp (pmSer (δ3 * x) ψ₁)) (thetaL r Y hY) *
        jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ₂ (4 / 3) =
      inner ℂ (h₂.toLp (pmSer (δ3 * x) ψ₂)) (thetaL r Y hY) *
        jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ₁ (4 / 3) := by
  have hξ : σO (δ3 * x) / 9 ≠ 0 :=
    div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num)
  have ha : 0 < 4 * Real.pi * ‖σO (δ3 * x) / 9‖ := by
    have := norm_pos_iff.2 hξ
    positivity
  obtain ⟨A₁, hA₁⟩ : ∃ f : ℂ → ℂ,
      f = aPm x r Y hY (le_band hα₁ hαβ₁) ψ₁ (h₁.toLp (pmSer (δ3 * x) ψ₁)) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ f : ℂ → ℂ,
      f = aPm x r Y hY (le_band hα₂ hαβ₂) ψ₂ (h₂.toLp (pmSer (δ3 * x) ψ₂)) := ⟨_, rfl⟩
  obtain ⟨J₁, hJ₁⟩ : ∃ f : ℂ → ℂ, f = jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ₁ := ⟨_, rfl⟩
  obtain ⟨J₂, hJ₂⟩ : ∃ f : ℂ → ℂ, f = jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ₂ := ⟨_, rfl⟩
  rw [← hJ₁, ← hJ₂]
  have hJ₁d : Differentiable ℂ J₁ := by rw [hJ₁]; exact differentiable_jPsi hψ₁ hM₁ h0₁ hα₁ ha
  have hJ₂d : Differentiable ℂ J₂ := by rw [hJ₂]; exact differentiable_jPsi hψ₂ hM₂ h0₂ hα₂ ha
  have hA₁d : DifferentiableOn ℂ A₁ (domU r) := by
    rw [hA₁]; exact differentiableOn_aPm x hr hY _ hψ₁ hM₁ h0₁ hα₁ _
  have hA₂d : DifferentiableOn ℂ A₂ (domU r) := by
    rw [hA₂]; exact differentiableOn_aPm x hr hY _ hψ₂ hM₂ h0₂ hα₂ _
  set F : ℂ → ℂ := fun s => A₁ s * J₂ s - A₂ s * J₁ s with hF
  have hFd : DifferentiableOn ℂ F (domU r) :=
    (hA₁d.mul hJ₂d.differentiableOn).sub (hA₂d.mul hJ₁d.differentiableOn)
  -- `F = 0` where `Re s > 2`
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.pi / (2 * r) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; positivity
  have htr : t < Real.pi / r := by
    rw [htdef, div_lt_div_iff₀ (by positivity) hr]
    nlinarith [Real.pi_pos]
  set z0 : ℂ := 3 + I * (t : ℂ) with hz0def
  have hz0re : z0.re = 3 := by simp [z0]
  have hz0im : z0.im = t := by simp [z0]
  have hz0 : z0 ∈ domU r := by
    refine ⟨?_, ?_, ?_⟩
    · show 1 < z0.re
      rw [hz0re]
      norm_num
    · show 0 < z0.im
      rw [hz0im]
      exact ht0
    · show z0.im < Real.pi / r
      rw [hz0im]
      exact htr
  have hfg : F =ᶠ[𝓝 z0] fun _ => 0 := by
    have hO : IsOpen (domU r ∩ {s | 2 < s.re}) :=
      (isOpen_domU r).inter (isOpen_lt continuous_const continuous_re)
    have hmem : z0 ∈ domU r ∩ {s | 2 < s.re} := ⟨hz0, by show 2 < z0.re; rw [hz0re]; norm_num⟩
    filter_upwards [hO.mem_nhds hmem] with s hs
    have him : (hhat (2 * Real.cosh r - 2) s).im ≠ 0 :=
      (im_hhat_pos hr hs.1.1 hs.1.2.1 ((lt_div_iff₀ hr).1 hs.1.2.2)).ne'
    simp only [hF]
    rw [hA₁, hA₂, hJ₁, hJ₂, aPm_eq hx hY hψ₁ h₁ hM₁ h0₁ hα₁ hαβ₁ hs.2 him,
      aPm_eq hx hY hψ₂ h₂ hM₂ h0₂ hα₂ hαβ₂ hs.2 him]
    ring
  have heq : EqOn F (fun _ => 0) (domU r) :=
    (hFd.analyticOnNhd (isOpen_domU r)).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_domU r).isPreconnected hz0 hfg
  -- the residue
  have hγ : Tendsto (fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε) (𝓝[>] 0) (𝓝 ((4 / 3 : ℝ) : ℂ)) := by
    have hc : Continuous fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε := by fun_prop
    have := hc.tendsto 0
    simp only [ofReal_zero, mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hγU : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ((4 / 3 : ℝ) : ℂ) + I * (ε : ℂ) ∈ domU r := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos Real.pi_pos hr)] with ε hε
    refine ⟨?_, ?_, ?_⟩
    · show 1 < (((4 / 3 : ℝ) : ℂ) + I * ε).re
      simp
      norm_num
    · show 0 < (((4 / 3 : ℝ) : ℂ) + I * ε).im
      simp [hε.1]
    · show (((4 / 3 : ℝ) : ℂ) + I * ε).im < Real.pi / r
      simp [hε.2]
  have hT₁ : Tendsto (fun ε : ℝ => (I * ε) * A₁ (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (inner ℂ (h₁.toLp (pmSer (δ3 * x) ψ₁)) (thetaL r Y hY))) := by
    rw [hA₁]; exact tendsto_aPm x hr hY _ hψ₁ hM₁ h0₁ hα₁ _
  have hT₂ : Tendsto (fun ε : ℝ => (I * ε) * A₂ (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (inner ℂ (h₂.toLp (pmSer (δ3 * x) ψ₂)) (thetaL r Y hY))) := by
    rw [hA₂]; exact tendsto_aPm x hr hY _ hψ₂ hM₂ h0₂ hα₂ _
  have hJ₁t : Tendsto (fun ε : ℝ => J₁ (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0) (𝓝 (J₁ ((4 / 3 : ℝ) : ℂ))) :=
    (hJ₁d _).continuousAt.tendsto.comp hγ
  have hJ₂t : Tendsto (fun ε : ℝ => J₂ (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0) (𝓝 (J₂ ((4 / 3 : ℝ) : ℂ))) :=
    (hJ₂d _).continuousAt.tendsto.comp hγ
  have hlim := (hT₁.mul hJ₂t).sub (hT₂.mul hJ₁t)
  have h0 : Tendsto (fun ε : ℝ => (I * ε) * A₁ (((4 / 3 : ℝ) : ℂ) + I * ε) * J₂ (((4 / 3 : ℝ) : ℂ) + I * ε) -
      (I * ε) * A₂ (((4 / 3 : ℝ) : ℂ) + I * ε) * J₁ (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hγU] with ε hε
    have := heq hε
    simp only [hF] at this
    linear_combination (-(I * (ε : ℂ))) * this
  have hfin := tendsto_nhds_unique hlim h0
  have e43 : ((4 / 3 : ℝ) : ℂ) = 4 / 3 := by push_cast; ring
  rw [e43] at hfin
  linear_combination hfin

/-! ### The coefficient `ρ(m)` -/

/-- `bkR r x > 0` for `x > 0`: its integrand is positive on `(0, ∞)`. -/
theorem bkR_pos {x : ℝ} (hx : 0 < x) (r : ℝ) : 0 < bkR r x := by
  unfold bkR
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_bkR hx r)]
  · have hs : Function.support (fun t : ℝ => t ^ (r - 1) * bkK x t) ∩ Ioi 0 = Ioi 0 := by
      ext t
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · exact fun h => h.2
      · intro ht
        exact ⟨(mul_pos (Real.rpow_pos_of_pos ht _) (bkK_pos x t)).ne', ht⟩
    rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun t ht => mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (bkK_pos x t).le

/-- The profile `1_{[1, 2]}`. -/
def ind12 : ℝ → ℂ := (Icc (1 : ℝ) 2).indicator fun _ => 1

theorem measurable_ind12 : Measurable ind12 := measurable_const.indicator measurableSet_Icc

theorem norm_ind12_le (v : ℝ) : ‖ind12 v‖ ≤ 1 := by
  unfold ind12
  by_cases h : v ∈ Icc (1 : ℝ) 2
  · rw [indicator_of_mem h, norm_one]
  · rw [indicator_of_notMem h, norm_zero]
    norm_num

theorem ind12_eq_zero {v : ℝ} (hv : v ∉ Icc (1 : ℝ) 2) : ind12 v = 0 := by
  unfold ind12
  rw [indicator_of_notMem hv]

theorem memLp_pmSer_ind12 (m : 𝓞 K) : MemLp (pmSer m ind12) 2 (muR rhoG) :=
  memLp_pmSer_Icc m measurable_ind12 norm_ind12_le (fun _ hv => ind12_eq_zero hv) one_pos

/-- **`J_{1_{[1, 2]}}(4/3) ≠ 0`** for `a > 0`: it is `∫_1^2 v^{−2}K_{1/3}(av) dv`, and `K_{1/3}` is positive
on `(0, ∞)` (round 374's `besselK_third_ofReal`, and `bkR_pos`). -/
theorem jPsi_ind12_ne_zero {a : ℝ} (ha : 0 < a) : jPsi a ind12 (4 / 3) ≠ 0 := by
  set g : ℝ → ℝ := (Icc (1 : ℝ) 2).indicator fun v => v ^ (-2 : ℤ) * (1 / 2 * bkR (1 / 3) (a * v))
    with hg
  have e : ∀ v, conj (ind12 v) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (4 / 3 - 1) (a * v)) =
      ((g v : ℝ) : ℂ) := by
    intro v
    rw [show (4 / 3 : ℂ) - 1 = 1 / 3 by norm_num, besselK_third_ofReal]
    unfold ind12
    by_cases h : v ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem h, hg, indicator_of_mem h, map_one, one_mul]
      push_cast
      ring
    · rw [indicator_of_notMem h, hg, indicator_of_notMem h, map_zero, zero_mul, ofReal_zero]
  have hint : IntegrableOn g (Ioi 0) := by
    have hc := integrableOn_Ioi_conj_mul measurable_ind12 norm_ind12_le (fun _ hv => ind12_eq_zero hv)
      one_pos (continuousOn_zpow_besselK (4 / 3 - 1) ha)
    refine hc.re.congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp only [e v, RCLike.re_to_complex, Complex.ofReal_re]
  have hg0 : ∀ v, 0 ≤ g v := fun v => by
    rw [hg]
    refine indicator_nonneg (fun v hv => ?_) v
    have hv0 : 0 < v := lt_of_lt_of_le one_pos hv.1
    have := bkR_nonneg (1 / 3) (a * v)
    positivity
  have hpos : 0 < ∫ v in Ioi 0, g v := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hg0) hint]
    have hsub : Icc (1 : ℝ) 2 ⊆ Function.support g ∩ Ioi 0 := by
      intro v hv
      have hv0 : 0 < v := lt_of_lt_of_le one_pos hv.1
      refine ⟨?_, hv0⟩
      rw [Function.mem_support, hg, indicator_of_mem hv]
      have := bkR_pos (mul_pos ha hv0) (1 / 3)
      positivity
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Icc]
    norm_num
  unfold jPsi
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v _ => e v), integral_complex_ofReal]
  exact_mod_cast hpos.ne'

/-- **`ρ(m)`**, for `m = δ₃x`: `⟨P_m(1_{[1, 2]}), θ⟩/J_{1_{[1, 2]}}(4/3)`. -/
def rhoM (x : 𝓞 K) (r Y : ℝ) (hY : 0 < Y) : ℂ :=
  inner ℂ ((memLp_pmSer_ind12 (δ3 * x)).toLp (pmSer (δ3 * x) ind12)) (thetaL r Y hY) /
    jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ind12 (4 / 3)

/-- **The pairing of θ with `P_m(ψ)`**: for `m = δ₃x ≠ 0`, `r > 0`, `Y > 0`, and `ψ` measurable and
bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, `⟨P_m(ψ), θ⟩ = ρ(m)·J_ψ(4/3)`, with
`J_ψ(4/3) = ∫_0^∞ conj ψ(v)·v^{−2}·K_{1/3}(4π|m|v/9) dv` and `ρ(m)` independent of `ψ`. -/
theorem inner_pmSer_thetaL {x : 𝓞 K} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) :
    inner ℂ (hψ2.toLp (pmSer (δ3 * x) ψ)) (thetaL r Y hY) =
      rhoM x r Y hY * jPsi (4 * Real.pi * ‖σO (δ3 * x) / 9‖) ψ (4 / 3) := by
  have hξ : σO (δ3 * x) / 9 ≠ 0 :=
    div_ne_zero (σO_ne_zero (mul_ne_zero δ3_ne_zero hx)) (by norm_num)
  have ha : 0 < 4 * Real.pi * ‖σO (δ3 * x) / 9‖ := by
    have := norm_pos_iff.2 hξ
    positivity
  have hJ0 := jPsi_ind12_ne_zero ha
  have hc := inner_pmSer_thetaL_cross hx hr hY hψ measurable_ind12 hψ2 (memLp_pmSer_ind12 (δ3 * x)) hM
    norm_ind12_le hψ0 (fun _ hv => ind12_eq_zero hv) hα hαβ one_pos one_le_two (Y := Y)
  unfold rhoM
  field_simp
  linear_combination hc

end Eis

end

#print axioms Eis.bkK_le_one
#print axioms Eis.measurable_bkK
#print axioms Eis.zpow_neg_two_le
#print axioms Eis.bkK_isBigO_bot
#print axioms Eis.measurable_jKer_integrand
#print axioms Eis.norm_jKer_integrand_le
#print axioms Eis.norm_jKer_le
#print axioms Eis.continuousOn_jKer
#print axioms Eis.jPsi_eq_mellin
#print axioms Eis.differentiable_jPsi
#print axioms Eis.aPm_eq
#print axioms Eis.differentiableOn_aPm
#print axioms Eis.tendsto_aPm
#print axioms Eis.inner_pmSer_thetaL_cross
#print axioms Eis.bkR_pos
#print axioms Eis.measurable_ind12
#print axioms Eis.norm_ind12_le
#print axioms Eis.ind12_eq_zero
#print axioms Eis.memLp_pmSer_ind12
#print axioms Eis.jPsi_ind12_ne_zero
#print axioms Eis.inner_pmSer_thetaL
