import KubotaEisTrunc

/-! # `s ↦ g_s` is holomorphic into `L²`, and the resolvent applied to it (round 424)

S5f-10 of round 360's plan, part 7 (S5f-10d). Round 423 wrote `g_s = (K − ĥ(s))(E_s − h_s)` as the
pseudo-Eisenstein series `E(G_s)` of a profile `G_s` that vanishes outside the shells
`Y/(R + 2) ≤ v < (R + 2)Y`. This round proves that `s ↦ g_s` is complex-differentiable into `L²(ν)` at every
`s`, and sets `ũ_s = −R(ĥ(s))g_s` where `Im ĥ(s) ≠ 0`.

* **A quantitative `L²` bound** (`psC`, a definition; **`lintegral_puLe_top_mul_le`** and
  **`eLpNorm_pseis_le`**, with `psC_lt_top`, `norm_le_pow_of_vanish`, `lintegral_pseis_sq_le` and
  `memLp_pseis_of_vanish`): `∫ρ_Γ F dμ ≤ Σ_q C(q⁻¹)·∫ρ dμ` when `F(g·p) ≤ C(g)` on the Siegel set for every
  `g`. So for `f` measurable, vanishing on `(0, a)` and bounded by `D`, `‖E(f)‖₂ ≤ psC(a)^{1/2}·D`, through
  round 423's growth at the cusps with `τ = 3`. The bound is linear in the supremum of the profile.
* **`G_s` as one integral** (`gWt`, `gInt` and `gDer`, definitions; **`gProf_eq_gInt`**, with `norm_gWt_le`,
  `measurable_gWt`, `gWt_eq_zero`, `snd_mem_Icc_of_mem_hball`, `rpow_le_add_of_mem_Icc`,
  `abs_log_le_of_mem_Icc`, `integrableOn_hball_of_le`, `measurable_ballInt`, `measurable_gInt`,
  `measurable_gDer`, `integrableOn_gWt`, `ballInt_gWt_eq_zero`, `snd_mem_shell` and `norm_ballInt_gWt_le`):
  `G_s(v) = ∫_{B_R(0, v)} (1[v′ < Y] − 1[v < Y])·v′^s dμ` by round 418's `bavg_cpow`. The weight vanishes on
  the ball off the shells, so the `s`-dependence sits in `v′^s` with `v′` in `[Y/(R + 2)², (R + 2)²Y]`.
* **Taylor's bound, uniform in `v`** (`shM` and `shL`, definitions; **`norm_cpow_taylor_le`** and
  **`gInt_taylor`**, with `shM_nonneg`, `shL_nonneg`, `norm_cpow_le_shM`, `abs_log_le_shL`,
  `gInt_eq_zero_of_lt`, `gDer_eq_zero_of_lt`, `norm_gInt_le` and `norm_gDer_le`):
  `|x^{s+h} − x^s − h·log x·x^s| ≤ x^σ|h log x|²` for `|h log x| ≤ 1` (Mathlib's
  `Complex.norm_exp_sub_one_sub_id_le`). So `|G_{s+h}(v) − G_s(v) − h·G′_s(v)| ≤ V_R·M_s·(|h|L)²` for every
  `v > 0` when `|h|L ≤ 1`, with `G′_s(v) = ∫_{B_R(0, v)} (1[v′ < Y] − 1[v < Y])·log v′·v′^s dμ`.
* **`s ↦ g_s` is holomorphic** (`gL` and `gL'`, definitions; **`memLp_gfun_all`** and **`hasDerivAt_gL`**,
  with `memLp_pseis_gDer`, `shell_lt_of_lt_div`, `differentiable_gL` and `continuous_gL`): `g_s` is in `L²(ν)`
  for every `s`, and `s ↦ g_s` has derivative `E(G′_s)` in `L²(ν)` at every `s`, for `R ≥ 0` and `Y > 0`.
* **The resolvent** (`uL`, a definition; **`uL_eq_eisLow`** and **`differentiableAt_uL`**, with
  `ballOp_toLp_eisLow_sub`, `cosh_sub_nonneg` and `differentiableAt_inner_uL`): `ũ_s = −R(ĥ(s))g_s` equals
  `E_s − h_s` in `L²(ν)` for `Re s > 2` with `Im ĥ(s) ≠ 0`, `R ≥ 0` and `Y > 0` (round 419's
  `resolvent_sub_apply`). For `R = 2cosh r − 2`, `s ↦ ũ_s` is complex-differentiable wherever `Im ĥ(s) ≠ 0`
  (round 418's `differentiable_hhat`, round 419's `hasDerivAt_resolvent_of_im_ne_zero`), and so is
  `s ↦ ⟨y, ũ_s⟩`.
-/

open MeasureTheory Set Filter NumberField Asymptotics
open scoped ENNReal Topology MatrixGroups

noncomputable section

namespace Eis

/-! ### A quantitative `L²` bound for pseudo-Eisenstein series -/

/-- **The integral over `Γ\H³`, bounded at every cusp**: `∫ρ_Γ F ≤ Σ_q C(q⁻¹)·∫ρ` over the cosets `q` of
`SL_2(ℤ[ω])/Γ`, when `F(g·p) ≤ C(g)` on round 385's Siegel set for every `g`. -/
theorem lintegral_puLe_top_mul_le (Γ : Subgroup SL(2, 𝓞 K)) {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F)
    {C : SL(2, 𝓞 K) → ℝ≥0∞} (hb : ∀ g : SL(2, 𝓞 K), ∀ p ∈ siegelK, F (slAct g p) ≤ C g) :
    ∫⁻ p, puLe ⊤ Γ rhoK p * F p ∂uhsMeasure ≤
      ∑' q : (⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤,
        C (q.out : SL(2, 𝓞 K))⁻¹ * ∫⁻ p, rhoK p ∂uhsMeasure := by
  have h1 : ∀ q : (⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤,
      ∫⁻ p, rhoK (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure ≤
        C (q.out : SL(2, 𝓞 K))⁻¹ * ∫⁻ p, rhoK p ∂uhsMeasure := by
    intro q
    set g : SL(2, 𝓞 K) := ((q.out : (⊤ : Subgroup SL(2, 𝓞 K))) : SL(2, 𝓞 K))
    rw [← lintegral_slAct g⁻¹ (F := fun p => rhoK (slAct g p) * F p)
      ((measurable_rhoK.comp (measurable_slAct _)).mul hF)]
    calc ∫⁻ p, rhoK (slAct g (slAct g⁻¹ p)) * F (slAct g⁻¹ p) ∂uhsMeasure
        ≤ ∫⁻ p, rhoK p * C g⁻¹ ∂uhsMeasure := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_UHS] with p hp
          rw [slAct_slAct_inv g hp]
          by_cases hK : p ∈ siegelK
          · gcongr
            exact hb g⁻¹ p hK
          · have h0 : rhoK p = 0 := by
              have := rhoK_le p
              rw [indicator_of_notMem hK] at this
              exact le_zero_iff.1 this
            simp [h0]
      _ = C g⁻¹ * ∫⁻ p, rhoK p ∂uhsMeasure := by
          rw [lintegral_mul_const _ measurable_rhoK, mul_comm]
  have hm : ∀ q : (⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤,
      AEMeasurable (fun p => rhoK (slAct (q.out : SL(2, 𝓞 K)) p) * F p) uhsMeasure :=
    fun q => ((measurable_rhoK.comp (measurable_slAct _)).mul hF).aemeasurable
  unfold puLe
  simp_rw [← ENNReal.tsum_mul_right]
  rw [lintegral_tsum hm]
  exact ENNReal.tsum_le_tsum h1

/-- The constant of the `L²` bound, for profiles vanishing below `a`:
`Σ_q (|a_{q⁻¹}| + 2a⁻³·cuspC(3))²·∫ρ dμ` over the cosets `q` of `SL_2(ℤ[ω])/Γ_1(3)`. -/
def psC (a : ℝ) : ℝ≥0∞ :=
  ∑' q : (⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Gam3.subgroupOf ⊤,
    ENNReal.ofReal (‖cuspA (q.out : SL(2, 𝓞 K))⁻¹‖ + 2 * (a ^ 3)⁻¹ * cuspC 3) ^ 2 *
      ∫⁻ p, rhoK p ∂uhsMeasure

theorem psC_lt_top (a : ℝ) : psC a < ⊤ := by
  unfold psC
  let := Fintype.ofFinite ((⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Gam3.subgroupOf ⊤)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun q _ =>
    ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) lintegral_rhoK_lt_top

/-- A profile vanishing on `(0, a)` and bounded by `D` is under the power bound `D·a⁻³·v³`. -/
theorem norm_le_pow_of_vanish {f : ℝ → ℂ} {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (h0 : ∀ v, 0 < v → v < a → f v = 0) (hf : ∀ v, 0 < v → ‖f v‖ ≤ D) {v : ℝ} (hv : 0 < v) :
    ‖f v‖ ≤ D * (a ^ 3)⁻¹ * v ^ (3 : ℝ) := by
  by_cases hva : v < a
  · rw [h0 v hv hva, norm_zero]
    positivity
  · have hav : a ≤ v := not_lt.1 hva
    have h1 : 1 ≤ (a ^ 3)⁻¹ * v ^ (3 : ℝ) := by
      rw [show v ^ (3 : ℝ) = v ^ (3 : ℕ) by norm_cast, ← div_eq_inv_mul, one_le_div (by positivity)]
      exact pow_le_pow_left₀ ha.le hav 3
    calc ‖f v‖ ≤ D := hf v hv
      _ = D * 1 := (mul_one D).symm
      _ ≤ D * ((a ^ 3)⁻¹ * v ^ (3 : ℝ)) := mul_le_mul_of_nonneg_left h1 hD
      _ = _ := by ring

/-- **A quantitative `L²` bound**: for `f` measurable, vanishing on `(0, a)` and bounded by `D ≥ 0` on
`(0, ∞)`, `∫|E(f)|² dν ≤ psC(a)·D²`. -/
theorem lintegral_pseis_sq_le {f : ℝ → ℂ} (hfm : Measurable f) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (h0 : ∀ v, 0 < v → v < a → f v = 0) (hf : ∀ v, 0 < v → ‖f v‖ ≤ D) :
    ∫⁻ p, ‖pseis f p‖ₑ ^ 2 ∂(muR rhoG) ≤ psC a * ENNReal.ofReal D ^ 2 := by
  have hm := measurable_pseis hfm
  have hC : 0 ≤ D * (a ^ 3)⁻¹ := by positivity
  have hpow : ∀ v, 0 < v → ‖f v‖ ≤ D * (a ^ 3)⁻¹ * v ^ (3 : ℝ) :=
    fun v hv => norm_le_pow_of_vanish ha hD h0 hf hv
  have hcC := cuspC_nonneg (by norm_num : (1 : ℝ) < 3)
  rw [muR, lintegral_withDensity_eq_lintegral_mul _ isPU_rhoG.1 (hm.enorm.pow_const 2)]
  refine (lintegral_puLe_top_mul_le Gam3 (hm.enorm.pow_const 2)
    (C := fun g => ENNReal.ofReal ((‖cuspA g‖ + 2 * (a ^ 3)⁻¹ * cuspC 3) * D) ^ 2)
    fun g p hp => ?_).trans (le_of_eq ?_)
  · have hv : 1 / 2 ≤ p.2 := hp.2
    have hp0 : (0 : ℝ) < p.2 := by linarith
    have h := norm_pseis_slAct_sub_le hC (by norm_num : (2 : ℝ) < 3) hpow g hv
    have h2 : p.2 ^ (2 - (3 : ℝ)) ≤ 2 := by
      rw [show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one, inv_le_comm₀ hp0 two_pos]
      linarith
    have hb : ‖pseis f (slAct g p)‖ ≤ (‖cuspA g‖ + 2 * (a ^ 3)⁻¹ * cuspC 3) * D := by
      calc ‖pseis f (slAct g p)‖ ≤ ‖cuspA g * f p.2‖ + ‖pseis f (slAct g p) - cuspA g * f p.2‖ :=
            norm_le_insert' _ _
        _ ≤ ‖cuspA g‖ * D + D * (a ^ 3)⁻¹ * (cuspC 3 * 2) := by
            rw [norm_mul]
            gcongr
            · exact hf _ hp0
            · exact h.trans (by gcongr)
        _ = _ := by ring
    change ‖pseis f (slAct g p)‖ₑ ^ 2 ≤ _
    rw [← ofReal_norm]
    gcongr
  · unfold psC
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun q => ?_
    rw [ENNReal.ofReal_mul (by positivity), mul_pow]
    ring

/-- **The `L²` norm of `E(f)`**: `‖E(f)‖₂ ≤ psC(a)^{1/2}·D` under the same hypotheses. -/
theorem eLpNorm_pseis_le {f : ℝ → ℂ} (hfm : Measurable f) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (h0 : ∀ v, 0 < v → v < a → f v = 0) (hf : ∀ v, 0 < v → ‖f v‖ ≤ D) :
    eLpNorm (pseis f) 2 (muR rhoG) ≤ psC a ^ (1 / 2 : ℝ) * ENNReal.ofReal D := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (measurable_pseis hfm).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ p, ‖pseis f p‖ₑ ^ 2 ∂(muR rhoG)) ^ (1 / 2 : ℝ)
      ≤ (psC a * ENNReal.ofReal D ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_pseis_sq_le hfm ha hD h0 hf) (by norm_num)
    _ = psC a ^ (1 / 2 : ℝ) * ENNReal.ofReal D := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

theorem memLp_pseis_of_vanish {f : ℝ → ℂ} (hfm : Measurable f) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (h0 : ∀ v, 0 < v → v < a → f v = 0) (hf : ∀ v, 0 < v → ‖f v‖ ≤ D) :
    MemLp (pseis f) 2 (muR rhoG) := by
  rw [memLp_iff]
  exact lt_of_le_of_lt (eLpNorm_pseis_le hfm ha hD h0 hf)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (psC_lt_top a).ne)
      ENNReal.ofReal_lt_top)

/-! ### `G_s` as one integral over the ball -/

/-- The weight of `G_s` on `B_R(0, v)`: `1[v′ < Y] − 1[v < Y]`. -/
def gWt (Y v : ℝ) (q : ℂ × ℝ) : ℂ := (if q.2 < Y then 1 else 0) - (if v < Y then 1 else 0)

theorem norm_gWt_le (Y v : ℝ) (q : ℂ × ℝ) : ‖gWt Y v q‖ ≤ 1 := by
  unfold gWt
  split_ifs <;> simp

theorem measurable_gWt (Y : ℝ) : Measurable fun x : ℝ × (ℂ × ℝ) => gWt Y x.1 x.2 := by
  unfold gWt
  refine Measurable.sub ?_ ?_
  · exact Measurable.ite (measurableSet_lt measurable_snd.snd measurable_const) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_const
      measurable_const

/-- **The weight vanishes on the ball off the shells**: on `B_R(0, v)`, `1[v′ < Y] = 1[v < Y]` when
`(R + 2)v < Y` or `(R + 2)Y ≤ v`. -/
theorem gWt_eq_zero {R Y v : ℝ} (hR : 0 ≤ R) (hv : 0 < v) (hva : (R + 2) * v < Y ∨ (R + 2) * Y ≤ v)
    {q : ℂ × ℝ} (hq : q ∈ hball R (0, v)) : gWt Y v q = 0 := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  have h1 := snd_le_of_mem_hball hv' hq
  have h2 := le_snd_of_mem_hball hv' hq
  unfold gWt
  rcases hva with h | h
  · have hq2 : q.2 < Y := lt_of_le_of_lt h1 h
    have hvY : v < Y := by nlinarith [mul_nonneg hR hv.le]
    simp [hq2, hvY]
  · have hq2 : ¬ q.2 < Y := by
      intro hlt
      have : (R + 2) * q.2 < (R + 2) * Y := mul_lt_mul_of_pos_left hlt (by linarith)
      linarith
    have hvY : ¬ v < Y := by
      intro hlt
      nlinarith [mul_nonneg hR (le_of_lt (lt_trans hv hlt))]
    simp [hq2, hvY]

/-- Heights on `B_R(0, v)` lie in `[v/(R + 2), (R + 2)v]`. -/
theorem snd_mem_Icc_of_mem_hball {R v : ℝ} (hR : 0 ≤ R) (hv : 0 < v) {q : ℂ × ℝ}
    (hq : q ∈ hball R (0, v)) : q.2 ∈ Icc (v / (R + 2)) ((R + 2) * v) := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  refine ⟨?_, snd_le_of_mem_hball hv' hq⟩
  rw [div_le_iff₀ (by linarith), mul_comm]
  exact le_snd_of_mem_hball hv' hq

/-- `x^σ ≤ α^σ + β^σ` on `[α, β]`, for `α > 0`. -/
theorem rpow_le_add_of_mem_Icc {α β x σ : ℝ} (hα : 0 < α) (hx : x ∈ Icc α β) :
    x ^ σ ≤ α ^ σ + β ^ σ := by
  have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
  rcases le_or_gt 0 σ with hσ | hσ
  · have := Real.rpow_le_rpow hx0.le hx.2 hσ
    linarith [Real.rpow_nonneg hα.le σ]
  · have := Real.rpow_le_rpow_of_nonpos hα hx.1 hσ.le
    linarith [Real.rpow_nonneg (hx0.le.trans hx.2) σ]

/-- `|log x| ≤ |log α| + |log β|` on `[α, β]`, for `α > 0`. -/
theorem abs_log_le_of_mem_Icc {α β x : ℝ} (hα : 0 < α) (hx : x ∈ Icc α β) :
    |Real.log x| ≤ |Real.log α| + |Real.log β| := by
  have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
  have h1 := Real.log_le_log hα hx.1
  have h2 := Real.log_le_log hx0 hx.2
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log α), le_abs_self (Real.log β), abs_nonneg (Real.log α),
    abs_nonneg (Real.log β)]

/-- Bounded measurable functions are integrable on a ball. -/
theorem integrableOn_hball_of_le {R : ℝ} (hR : 0 ≤ R) {p : ℂ × ℝ} (hp : p ∈ UHS) {F : ℂ × ℝ → ℂ}
    (hF : Measurable F) {M : ℝ} (hM : ∀ q ∈ hball R p, ‖F q‖ ≤ M) :
    IntegrableOn F (hball R p) uhsMeasure :=
  Measure.integrableOn_of_bounded (uhsMeasure_hball_lt_top_of_mem hR hp).ne hF.aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_hball R p)).2 (Eventually.of_forall hM))

/-- **Integrals over `B_R(0, v)` are measurable in `v`**, for a jointly measurable integrand (Mathlib's
`StronglyMeasurable.integral_prod_right'`). -/
theorem measurable_ballInt (R : ℝ) {Φ : ℝ × (ℂ × ℝ) → ℂ} (hΦ : Measurable Φ) :
    Measurable fun v : ℝ => ∫ q in hball R (0, v), Φ (v, q) ∂uhsMeasure := by
  set S := {x : ℝ × (ℂ × ℝ) | x.2 ∈ hball R (0, x.1)} with hSdef
  have hS : MeasurableSet S := by
    have e : S = {x | 0 < x.2.2} ∩ {x | ppi (0, x.1) x.2 ≤ R} := by
      ext x
      simp [hSdef, hball, UHS]
    have hm : Measurable fun x : ℝ × (ℂ × ℝ) => ppi (0, x.1) x.2 := by
      unfold ppi
      fun_prop
    rw [e]
    exact (measurableSet_lt measurable_const measurable_snd.snd).inter
      (measurableSet_le hm measurable_const)
  have h := ((hΦ.indicator hS).stronglyMeasurable).integral_prod_right' (ν := uhsMeasure)
  have e : (fun v : ℝ => ∫ q in hball R (0, v), Φ (v, q) ∂uhsMeasure) =
      fun v => ∫ q, S.indicator Φ (v, q) ∂uhsMeasure := by
    funext v
    rw [← integral_indicator (measurableSet_hball R _)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    dsimp only
    by_cases hq : q ∈ hball R (0, v)
    · rw [indicator_of_mem hq, indicator_of_mem (show (v, q) ∈ S from hq)]
    · rw [indicator_of_notMem hq, indicator_of_notMem (show (v, q) ∉ S from hq)]
  rw [e]
  exact h.measurable

/-- The integral form of the profile: `∫_{B_R(0, v)} w·v′^s dμ` with the weight `w = 1[v′ < Y] − 1[v < Y]`. -/
def gInt (R : ℝ) (s : ℂ) (Y v : ℝ) : ℂ :=
  ∫ q in hball R (0, v), gWt Y v q * ((q.2 : ℝ) : ℂ) ^ s ∂uhsMeasure

/-- Its derivative in `s`: `∫_{B_R(0, v)} w·log v′·v′^s dμ`. -/
def gDer (R : ℝ) (s : ℂ) (Y v : ℝ) : ℂ :=
  ∫ q in hball R (0, v), gWt Y v q * (((Real.log q.2 : ℝ) : ℂ) * ((q.2 : ℝ) : ℂ) ^ s) ∂uhsMeasure

theorem measurable_gInt (R : ℝ) (s : ℂ) (Y : ℝ) : Measurable (gInt R s Y) :=
  measurable_ballInt R (Φ := fun x => gWt Y x.1 x.2 * ((x.2.2 : ℝ) : ℂ) ^ s)
    ((measurable_gWt Y).mul (by fun_prop))

theorem measurable_gDer (R : ℝ) (s : ℂ) (Y : ℝ) : Measurable (gDer R s Y) :=
  measurable_ballInt R
    (Φ := fun x => gWt Y x.1 x.2 * (((Real.log x.2.2 : ℝ) : ℂ) * ((x.2.2 : ℝ) : ℂ) ^ s))
    ((measurable_gWt Y).mul (by fun_prop))

/-- Weighted integrals over `B_R(0, v)` of a function of the height bounded on `[v/(R + 2), (R + 2)v]`
are integrable. -/
theorem integrableOn_gWt {R : ℝ} (hR : 0 ≤ R) (Y : ℝ) {v : ℝ} (hv : 0 < v) {φ : ℝ → ℂ}
    (hφm : Measurable φ) {C : ℝ} (hφ : ∀ x ∈ Icc (v / (R + 2)) ((R + 2) * v), ‖φ x‖ ≤ C) :
    IntegrableOn (fun q : ℂ × ℝ => gWt Y v q * φ q.2) (hball R (0, v)) uhsMeasure := by
  have hm : Measurable fun q : ℂ × ℝ => gWt Y v q * φ q.2 :=
    ((measurable_gWt Y).comp (measurable_const.prodMk measurable_id)).mul (hφm.comp measurable_snd)
  refine integrableOn_hball_of_le hR (show ((0 : ℂ), v) ∈ UHS from hv) hm (M := C) fun q hq => ?_
  rw [norm_mul]
  calc ‖gWt Y v q‖ * ‖φ q.2‖ ≤ 1 * C :=
        mul_le_mul (norm_gWt_le Y v q) (hφ _ (snd_mem_Icc_of_mem_hball hR hv hq)) (norm_nonneg _)
          zero_le_one
    _ = C := one_mul C

/-- **Off the shells the weighted integrals vanish.** -/
theorem ballInt_gWt_eq_zero {R Y v : ℝ} (hR : 0 ≤ R) (hv : 0 < v)
    (hva : (R + 2) * v < Y ∨ (R + 2) * Y ≤ v) (φ : ℝ → ℂ) :
    ∫ q in hball R (0, v), gWt Y v q * φ q.2 ∂uhsMeasure = 0 := by
  have e : ∫ q in hball R (0, v), gWt Y v q * φ q.2 ∂uhsMeasure =
      ∫ q in hball R (0, v), (0 : ℂ) ∂uhsMeasure :=
    setIntegral_congr_fun (measurableSet_hball R _) fun q hq => by
      simp only [gWt_eq_zero hR hv hva hq, zero_mul]
  rw [e, integral_zero]

/-- Heights on `B_R(0, v)` for `v` in the shells, `Y ≤ (R + 2)v ≤ (R + 2)²Y`, lie in
`[Y/(R + 2)², (R + 2)²Y]`. -/
theorem snd_mem_shell {R Y v : ℝ} (hR : 0 ≤ R) (hv : 0 < v) (h1 : Y ≤ (R + 2) * v)
    (h2 : v ≤ (R + 2) * Y) {q : ℂ × ℝ} (hq : q ∈ hball R (0, v)) :
    q.2 ∈ Icc (Y / (R + 2) ^ 2) ((R + 2) ^ 2 * Y) := by
  have hR2 : 0 < R + 2 := by linarith
  obtain ⟨hl, hu⟩ := snd_mem_Icc_of_mem_hball hR hv hq
  constructor
  · refine le_trans ?_ hl
    rw [div_le_div_iff₀ (by positivity) hR2]
    nlinarith
  · calc q.2 ≤ (R + 2) * v := hu
      _ ≤ (R + 2) * ((R + 2) * Y) := mul_le_mul_of_nonneg_left h2 hR2.le
      _ = (R + 2) ^ 2 * Y := by ring

/-- **The weighted integrals are bounded by the shell**: `|∫_{B_R(0, v)} w·φ(v′) dμ| ≤ V_R·C` for every
`v > 0` when `|φ| ≤ C` on `[Y/(R + 2)², (R + 2)²Y]`. -/
theorem norm_ballInt_gWt_le {R Y : ℝ} (hR : 0 ≤ R) {φ : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ x ∈ Icc (Y / (R + 2) ^ 2) ((R + 2) ^ 2 * Y), ‖φ x‖ ≤ C) {v : ℝ} (hv : 0 < v) :
    ‖∫ q in hball R (0, v), gWt Y v q * φ q.2 ∂uhsMeasure‖ ≤
      uhsMeasure.real (hball R (0, 1)) * C := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  by_cases hs : (R + 2) * v < Y ∨ (R + 2) * Y ≤ v
  · rw [ballInt_gWt_eq_zero hR hv hs, norm_zero]
    exact mul_nonneg measureReal_nonneg hC
  · push Not at hs
    obtain ⟨h1, h2⟩ := hs
    have h := norm_setIntegral_le_of_norm_le_const (uhsMeasure_hball_lt_top_of_mem hR hv')
      (f := fun q : ℂ × ℝ => gWt Y v q * φ q.2) (C := C) fun q hq => by
        rw [norm_mul]
        calc ‖gWt Y v q‖ * ‖φ q.2‖ ≤ 1 * C :=
              mul_le_mul (norm_gWt_le Y v q) (hφ _ (snd_mem_shell hR hv h1 h2.le hq))
                (norm_nonneg _) zero_le_one
          _ = C := one_mul C
    rw [show uhsMeasure.real (hball R (0, v)) = uhsMeasure.real (hball R (0, 1)) by
      simp only [Measure.real, uhsMeasure_hball R hv']] at h
    linarith

/-- `G_s` in its integral form. -/
theorem gProf_eq_gInt {R : ℝ} (hR : 0 ≤ R) (s : ℂ) (Y : ℝ) {v : ℝ} (hv : 0 < v) :
    gProf R s Y v = gInt R s Y v := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  have hbd : ∀ x ∈ Icc (v / (R + 2)) ((R + 2) * v),
      ‖((x : ℝ) : ℂ) ^ s‖ ≤ (v / (R + 2)) ^ s.re + ((R + 2) * v) ^ s.re := by
    intro x hx
    have hα : 0 < v / (R + 2) := div_pos hv (by linarith)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hα hx.1)]
    exact rpow_le_add_of_mem_Icc hα hx
  have hI1 : IntegrableOn (fun q : ℂ × ℝ => (if q.2 < Y then (1 : ℂ) else 0) * ((q.2 : ℝ) : ℂ) ^ s)
      (hball R (0, v)) uhsMeasure := by
    refine integrableOn_hball_of_le hR hv' ?_ (M := (v / (R + 2)) ^ s.re + ((R + 2) * v) ^ s.re)
      fun q hq => ?_
    · exact (Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const
        measurable_const).mul (measurable_cpow_snd s)
    · rw [norm_mul]
      refine le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_)
        (hbd _ (snd_mem_Icc_of_mem_hball hR hv hq))
      split_ifs <;> simp
  have hI2 : IntegrableOn (fun q : ℂ × ℝ => (if v < Y then (1 : ℂ) else 0) * ((q.2 : ℝ) : ℂ) ^ s)
      (hball R (0, v)) uhsMeasure := by
    refine integrableOn_hball_of_le hR hv' (measurable_const.mul (measurable_cpow_snd s))
      (M := (v / (R + 2)) ^ s.re + ((R + 2) * v) ^ s.re) fun q hq => ?_
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_)
      (hbd _ (snd_mem_Icc_of_mem_hball hR hv hq))
    split_ifs <;> simp
  have hb : ∫ q in hball R (0, v), ((q.2 : ℝ) : ℂ) ^ s ∂uhsMeasure = hhat R s * ((v : ℝ) : ℂ) ^ s :=
    bavg_cpow R s hv'
  unfold gInt gWt
  simp_rw [sub_mul]
  rw [integral_sub hI1 hI2, integral_const_mul, hb, gProf, bTrans, bavg]
  congr 1
  · refine setIntegral_congr_fun (measurableSet_hball R _) fun q _ => ?_
    simp only [lowF]
    split_ifs <;> simp
  · simp only [lowF]
    split_ifs <;> simp

/-! ### Bounds on the shells, and Taylor's bound -/

/-- The bound for powers on the shells: `(Y/(R + 2)²)^σ + ((R + 2)²Y)^σ`. -/
def shM (R Y : ℝ) (s : ℂ) : ℝ := (Y / (R + 2) ^ 2) ^ s.re + ((R + 2) ^ 2 * Y) ^ s.re

/-- The bound for logarithms on the shells: `|log(Y/(R + 2)²)| + |log((R + 2)²Y)|`. -/
def shL (R Y : ℝ) : ℝ := |Real.log (Y / (R + 2) ^ 2)| + |Real.log ((R + 2) ^ 2 * Y)|

theorem shM_nonneg {R Y : ℝ} (hY : 0 < Y) (s : ℂ) : 0 ≤ shM R Y s := by
  unfold shM
  have h1 : 0 ≤ Y / (R + 2) ^ 2 := div_nonneg hY.le (sq_nonneg _)
  have h2 : 0 ≤ (R + 2) ^ 2 * Y := mul_nonneg (sq_nonneg _) hY.le
  exact add_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)

theorem shL_nonneg (R Y : ℝ) : 0 ≤ shL R Y := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem norm_cpow_le_shM {R Y : ℝ} (hR : 0 ≤ R) (hY : 0 < Y) {x : ℝ}
    (hx : x ∈ Icc (Y / (R + 2) ^ 2) ((R + 2) ^ 2 * Y)) (s : ℂ) : ‖((x : ℝ) : ℂ) ^ s‖ ≤ shM R Y s := by
  have hα : 0 < Y / (R + 2) ^ 2 := div_pos hY (by positivity)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hα hx.1)]
  exact rpow_le_add_of_mem_Icc hα hx

theorem abs_log_le_shL {R Y : ℝ} (hR : 0 ≤ R) (hY : 0 < Y) {x : ℝ}
    (hx : x ∈ Icc (Y / (R + 2) ^ 2) ((R + 2) ^ 2 * Y)) : |Real.log x| ≤ shL R Y :=
  abs_log_le_of_mem_Icc (div_pos hY (by positivity)) hx

/-- **Taylor's bound for `x^s`**: `|x^{s+h} − x^s − h·log x·x^s| ≤ x^σ·|h log x|²` for `x > 0` and
`|h log x| ≤ 1` (Mathlib's `Complex.norm_exp_sub_one_sub_id_le`). -/
theorem norm_cpow_taylor_le {x : ℝ} (hx : 0 < x) (s h : ℂ) (hh : ‖h * (Real.log x : ℂ)‖ ≤ 1) :
    ‖((x : ℝ) : ℂ) ^ (s + h) - ((x : ℝ) : ℂ) ^ s - h * (((Real.log x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ s)‖ ≤
      x ^ s.re * ‖h * (Real.log x : ℂ)‖ ^ 2 := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e1 : ((x : ℝ) : ℂ) ^ (s + h) = ((x : ℝ) : ℂ) ^ s * Complex.exp (h * (Real.log x : ℂ)) := by
    rw [Complex.cpow_add _ _ hx0, Complex.cpow_def_of_ne_zero hx0 h, ← Complex.ofReal_log hx.le,
      mul_comm (((Real.log x : ℝ) : ℂ)) h]
  have e2 : ((x : ℝ) : ℂ) ^ (s + h) - ((x : ℝ) : ℂ) ^ s -
      h * (((Real.log x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ s) =
      ((x : ℝ) : ℂ) ^ s * (Complex.exp (h * (Real.log x : ℂ)) - 1 - h * (Real.log x : ℂ)) := by
    rw [e1]
    ring
  rw [e2, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  exact mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le hh) (Real.rpow_nonneg hx.le _)

theorem gInt_eq_zero_of_lt {R Y v : ℝ} (hR : 0 ≤ R) (hv : 0 < v) (h : (R + 2) * v < Y) (s : ℂ) :
    gInt R s Y v = 0 :=
  ballInt_gWt_eq_zero hR hv (Or.inl h) (fun x => ((x : ℝ) : ℂ) ^ s)

theorem gDer_eq_zero_of_lt {R Y v : ℝ} (hR : 0 ≤ R) (hv : 0 < v) (h : (R + 2) * v < Y) (s : ℂ) :
    gDer R s Y v = 0 :=
  ballInt_gWt_eq_zero hR hv (Or.inl h) (fun x => ((Real.log x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ s)

/-- `|G_s(v)| ≤ V_R·M_s` for every `v > 0`. -/
theorem norm_gInt_le {R Y : ℝ} (hR : 0 ≤ R) (hY : 0 < Y) (s : ℂ) {v : ℝ} (hv : 0 < v) :
    ‖gInt R s Y v‖ ≤ uhsMeasure.real (hball R (0, 1)) * shM R Y s :=
  norm_ballInt_gWt_le hR (φ := fun x => ((x : ℝ) : ℂ) ^ s) (shM_nonneg hY s)
    (fun _ hx => norm_cpow_le_shM hR hY hx s) hv

/-- `|G′_s(v)| ≤ V_R·L·M_s` for every `v > 0`. -/
theorem norm_gDer_le {R Y : ℝ} (hR : 0 ≤ R) (hY : 0 < Y) (s : ℂ) {v : ℝ} (hv : 0 < v) :
    ‖gDer R s Y v‖ ≤ uhsMeasure.real (hball R (0, 1)) * (shL R Y * shM R Y s) :=
  norm_ballInt_gWt_le hR (φ := fun x => ((Real.log x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ s)
    (mul_nonneg (shL_nonneg R Y) (shM_nonneg hY s)) (fun x hx => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (abs_log_le_shL hR hY hx) (norm_cpow_le_shM hR hY hx s) (norm_nonneg _)
        (shL_nonneg R Y)) hv

/-- **Taylor's bound for `G_s`, uniform in `v`**: `|G_{s+h}(v) − G_s(v) − h·G′_s(v)| ≤ V_R·M_s·(|h|L)²` for
every `v > 0` when `|h|·L ≤ 1`. -/
theorem gInt_taylor {R Y : ℝ} (hR : 0 ≤ R) (hY : 0 < Y) (s : ℂ) {h : ℂ} (hh : ‖h‖ * shL R Y ≤ 1)
    {v : ℝ} (hv : 0 < v) :
    ‖gInt R (s + h) Y v - gInt R s Y v - h * gDer R s Y v‖ ≤
      uhsMeasure.real (hball R (0, 1)) * (shM R Y s * (‖h‖ * shL R Y) ^ 2) := by
  have hα : 0 < v / (R + 2) := div_pos hv (by linarith)
  have hA := integrableOn_gWt hR Y hv (φ := fun x => ((x : ℝ) : ℂ) ^ (s + h)) (by fun_prop)
    (C := (v / (R + 2)) ^ (s + h).re + ((R + 2) * v) ^ (s + h).re) fun x hx => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hα hx.1)]
      exact rpow_le_add_of_mem_Icc hα hx
  have hB := integrableOn_gWt hR Y hv (φ := fun x => ((x : ℝ) : ℂ) ^ s) (by fun_prop)
    (C := (v / (R + 2)) ^ s.re + ((R + 2) * v) ^ s.re) fun x hx => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hα hx.1)]
      exact rpow_le_add_of_mem_Icc hα hx
  have hC := (integrableOn_gWt hR Y hv (φ := fun x => ((Real.log x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ s)
    (by fun_prop) (C := (|Real.log (v / (R + 2))| + |Real.log ((R + 2) * v)|) *
      ((v / (R + 2)) ^ s.re + ((R + 2) * v) ^ s.re)) fun x hx => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hα hx.1)]
      exact mul_le_mul (abs_log_le_of_mem_Icc hα hx) (rpow_le_add_of_mem_Icc hα hx)
        (Real.rpow_nonneg (hα.le.trans hx.1) _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).const_mul h
  have e : gInt R (s + h) Y v - gInt R s Y v - h * gDer R s Y v =
      ∫ q in hball R (0, v), gWt Y v q * (((q.2 : ℝ) : ℂ) ^ (s + h) - ((q.2 : ℝ) : ℂ) ^ s -
        h * (((Real.log q.2 : ℝ) : ℂ) * ((q.2 : ℝ) : ℂ) ^ s)) ∂uhsMeasure := by
    have hAB : IntegrableOn (fun q : ℂ × ℝ => gWt Y v q * ((q.2 : ℝ) : ℂ) ^ (s + h) -
        gWt Y v q * ((q.2 : ℝ) : ℂ) ^ s) (hball R (0, v)) uhsMeasure := hA.sub hB
    unfold gInt gDer
    rw [← integral_const_mul, ← integral_sub hA hB, ← integral_sub hAB hC]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  rw [e]
  refine norm_ballInt_gWt_le hR
    (φ := fun x => ((x : ℝ) : ℂ) ^ (s + h) - ((x : ℝ) : ℂ) ^ s -
      h * (((Real.log x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ s))
    (mul_nonneg (shM_nonneg hY s) (sq_nonneg _)) (fun x hx => ?_) hv
  have hx0 : 0 < x := lt_of_lt_of_le (div_pos hY (by positivity)) hx.1
  have hl : ‖h * (Real.log x : ℂ)‖ ≤ ‖h‖ * shL R Y := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_log_le_shL hR hY hx) (norm_nonneg _)
  refine (norm_cpow_taylor_le hx0 s h (hl.trans hh)).trans ?_
  refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) hl 2) (sq_nonneg _) (shM_nonneg hY s)
  have := norm_cpow_le_shM hR hY hx s
  rwa [Complex.norm_cpow_eq_rpow_re_of_pos hx0] at this

/-! ### `s ↦ g_s` is holomorphic into `L²(ν)` -/

/-- **`g_s` is in `L²(ν)` for every `s`**, for `R ≥ 0` and `Y > 0`. -/
theorem memLp_gfun_all {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) (s : ℂ) :
    MemLp (gfun R s Y) 2 (muR rhoG) := by
  have hR2 : 0 < R + 2 := by linarith
  refine memLp_pseis_of_vanish (measurable_gProf R s Y) (a := Y / (R + 2))
    (D := uhsMeasure.real (hball R (0, 1)) * shM R Y s) (div_pos hY hR2)
    (mul_nonneg measureReal_nonneg (shM_nonneg hY s)) (fun v hv hva => ?_) (fun v hv => ?_)
  · refine gProf_eq_zero_of_lt hR s hv ?_
    rw [lt_div_iff₀ hR2] at hva
    linarith
  · rw [gProf_eq_gInt hR s Y hv]
    exact norm_gInt_le hR hY s hv

/-- The derivative `E(G′_s)` is in `L²(ν)`. -/
theorem memLp_pseis_gDer {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) (s : ℂ) :
    MemLp (pseis (gDer R s Y)) 2 (muR rhoG) := by
  have hR2 : 0 < R + 2 := by linarith
  refine memLp_pseis_of_vanish (measurable_gDer R s Y) (a := Y / (R + 2))
    (D := uhsMeasure.real (hball R (0, 1)) * (shL R Y * shM R Y s)) (div_pos hY hR2)
    (mul_nonneg measureReal_nonneg (mul_nonneg (shL_nonneg R Y) (shM_nonneg hY s)))
    (fun v hv hva => ?_) (fun v hv => norm_gDer_le hR hY s hv)
  refine gDer_eq_zero_of_lt hR hv ?_ s
  rw [lt_div_iff₀ hR2] at hva
  linarith

/-- **`g_s` in `L²(ν)`**, for `R ≥ 0` and `Y > 0`. -/
def gL (R : ℝ) (hR : 0 ≤ R) (Y : ℝ) (hY : 0 < Y) (s : ℂ) : Lp ℂ 2 (muR rhoG) :=
  (memLp_gfun_all hR hY s).toLp (gfun R s Y)

/-- **Its derivative** `E(G′_s)` in `L²(ν)`. -/
def gL' (R : ℝ) (hR : 0 ≤ R) (Y : ℝ) (hY : 0 < Y) (s : ℂ) : Lp ℂ 2 (muR rhoG) :=
  (memLp_pseis_gDer hR hY s).toLp (pseis (gDer R s Y))

/-- The profiles vanish below `Y/(R + 2)`. -/
theorem shell_lt_of_lt_div {R Y v : ℝ} (hR : 0 ≤ R) (hva : v < Y / (R + 2)) : (R + 2) * v < Y := by
  rw [lt_div_iff₀ (by linarith)] at hva
  linarith

/-- **`s ↦ g_s` is complex-differentiable into `L²(ν)`, with derivative `E(G′_s)`**, at every `s`, for
`R ≥ 0` and `Y > 0`. -/
theorem hasDerivAt_gL {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) (s₀ : ℂ) :
    HasDerivAt (gL R hR Y hY) (gL' R hR Y hY s₀) s₀ := by
  have hR2 : 0 < R + 2 := by linarith
  set a := Y / (R + 2) with ha_def
  have ha : 0 < a := div_pos hY hR2
  set L := shL R Y
  set V := uhsMeasure.real (hball R (0, 1))
  set P := (psC a ^ (1 / 2 : ℝ)).toReal
  have hL : 0 ≤ L := shL_nonneg R Y
  have hV : 0 ≤ V := measureReal_nonneg
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  have hM := shM_nonneg (R := R) hY s₀
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  set K := P * (V * (shM R Y s₀ * L ^ 2))
  have hK : 0 ≤ K := by positivity
  set ε := min (1 / (L + 1)) (c / (K + 1))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
  rw [Metric.mem_ball, dist_eq_norm] at hs
  set h := s - s₀ with hh_def
  have hs' : s = s₀ + h := by rw [hh_def]; ring
  have h1 : ‖h‖ * L ≤ 1 := by
    have : ‖h‖ ≤ 1 / (L + 1) := hs.le.trans (min_le_left _ _)
    calc ‖h‖ * L ≤ 1 / (L + 1) * L := mul_le_mul_of_nonneg_right this hL
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; linarith
  have h2 : K * ‖h‖ ≤ c := by
    have : ‖h‖ ≤ c / (K + 1) := hs.le.trans (min_le_right _ _)
    calc K * ‖h‖ ≤ K * (c / (K + 1)) := mul_le_mul_of_nonneg_left this hK
      _ ≤ c := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  -- the remainder profile
  set rem : ℝ → ℂ := fun v => gInt R s Y v - gInt R s₀ Y v - h * gDer R s₀ Y v with hrem
  have hrem_m : Measurable rem :=
    ((measurable_gInt R s Y).sub (measurable_gInt R s₀ Y)).sub
      (measurable_const.mul (measurable_gDer R s₀ Y))
  have hrem0 : ∀ v, 0 < v → v < a → rem v = 0 := fun v hv hva => by
    have hlt := shell_lt_of_lt_div hR hva
    simp only [hrem, gInt_eq_zero_of_lt hR hv hlt, gDer_eq_zero_of_lt hR hv hlt, sub_zero, mul_zero]
  have hremb : ∀ v, 0 < v → ‖rem v‖ ≤ V * (shM R Y s₀ * (‖h‖ * L) ^ 2) := fun v hv => by
    have := gInt_taylor hR hY s₀ h1 hv
    rwa [← hs'] at this
  have hD : 0 ≤ V * (shM R Y s₀ * (‖h‖ * L) ^ 2) := by positivity
  -- the power bounds for the pieces
  have hpw : ∀ (f : ℝ → ℂ) (D : ℝ), 0 ≤ D → (∀ v, 0 < v → v < a → f v = 0) →
      (∀ v, 0 < v → ‖f v‖ ≤ D) → ∀ v, 0 < v → ‖f v‖ ≤ D * (a ^ 3)⁻¹ * v ^ (3 : ℝ) :=
    fun f D hD0 h0 hb v hv => norm_le_pow_of_vanish ha hD0 h0 hb hv
  have hI : ∀ t : ℂ, ∀ v, 0 < v → ‖gInt R t Y v‖ ≤ V * shM R Y t * (a ^ 3)⁻¹ * v ^ (3 : ℝ) :=
    fun t => hpw _ _ (mul_nonneg hV (shM_nonneg hY t))
      (fun v hv hva => gInt_eq_zero_of_lt hR hv (shell_lt_of_lt_div hR hva) t)
      (fun v hv => norm_gInt_le hR hY t hv)
  have hDr : ∀ v, 0 < v → ‖h * gDer R s₀ Y v‖ ≤
      ‖h‖ * (V * (L * shM R Y s₀)) * (a ^ 3)⁻¹ * v ^ (3 : ℝ) :=
    hpw _ _ (by positivity)
      (fun v hv hva => by rw [gDer_eq_zero_of_lt hR hv (shell_lt_of_lt_div hR hva) s₀, mul_zero])
      (fun v hv => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_gDer_le hR hY s₀ hv) (norm_nonneg _))
  have hsub : ∀ v, 0 < v → ‖gInt R s Y v - gInt R s₀ Y v‖ ≤
      (V * shM R Y s * (a ^ 3)⁻¹ + V * shM R Y s₀ * (a ^ 3)⁻¹) * v ^ (3 : ℝ) := fun v hv => by
    refine (norm_sub_le _ _).trans ?_
    have := add_le_add (hI s v hv) (hI s₀ v hv)
    linarith
  -- the a.e. identity
  have hae : (fun p => gfun R s Y p - gfun R s₀ Y p - h * pseis (gDer R s₀ Y) p) =ᵐ[muR rhoG]
      pseis rem := by
    filter_upwards [ae_muR_UHS rhoG] with p hp
    rw [gfun, gfun, pseis_congr (fun v hv => gProf_eq_gInt hR s Y hv) hp,
      pseis_congr (fun v hv => gProf_eq_gInt hR s₀ Y hv) hp, ← pseis_const_mul,
      ← pseis_sub (by norm_num : (2 : ℝ) < 3) (hI s) (hI s₀) hp,
      ← pseis_sub (by norm_num : (2 : ℝ) < 3) hsub hDr hp]
  -- the norm
  have hnorm : ‖gL R hR Y hY s - gL R hR Y hY s₀ - h • gL' R hR Y hY s₀‖ ≤
      P * (V * (shM R Y s₀ * (‖h‖ * L) ^ 2)) := by
    rw [gL, gL, gL', ← MemLp.toLp_const_smul, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_toLp]
    have he : eLpNorm (gfun R s Y - gfun R s₀ Y - h • pseis (gDer R s₀ Y)) 2 (muR rhoG) =
        eLpNorm (pseis rem) 2 (muR rhoG) := eLpNorm_congr_ae hae
    rw [he]
    have hb := eLpNorm_pseis_le hrem_m ha hD hrem0 hremb
    have hfin : psC a ^ (1 / 2 : ℝ) * ENNReal.ofReal (V * (shM R Y s₀ * (‖h‖ * L) ^ 2)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (psC_lt_top a).ne)
        ENNReal.ofReal_ne_top
    refine (ENNReal.toReal_mono hfin hb).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD]
  calc ‖gL R hR Y hY s - gL R hR Y hY s₀ - (s - s₀) • gL' R hR Y hY s₀‖
      ≤ P * (V * (shM R Y s₀ * (‖h‖ * L) ^ 2)) := hnorm
    _ = K * ‖h‖ * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

theorem differentiable_gL {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) :
    Differentiable ℂ (gL R hR Y hY) :=
  fun s => (hasDerivAt_gL hR hY s).differentiableAt

theorem continuous_gL {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) : Continuous (gL R hR Y hY) :=
  (differentiable_gL hR hY).continuous

/-! ### The resolvent applied to `g_s` -/

/-- **`ũ_s = −R(ĥ(s))g_s`**, with `R(z) = (z − K)⁻¹` the resolvent of round 421's ball operator `K` for
`Γ_1(3)` and Kubota's character. -/
def uL (R : ℝ) (hR : 0 ≤ R) (Y : ℝ) (hY : 0 < Y) (s : ℂ) : Lp ℂ 2 (muR rhoG) :=
  -resolvent (ballOp isPU_rhoG isUChar_kub hR) (hhat R s) (gL R hR Y hY s)

/-- **`(K − ĥ(s))(E_s − h_s) = g_s` in `L²(ν)`**, as an identity of elements, for `Re s > 2`. -/
theorem ballOp_toLp_eisLow_sub {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 2 < s.re) :
    ballOp isPU_rhoG isUChar_kub hR ((memLp_eisLow hs hY.le).toLp (eisLow s Y)) -
      hhat R s • (memLp_eisLow hs hY.le).toLp (eisLow s Y) = gL R hR Y hY s := by
  refine Lp.ext ?_
  filter_upwards [ballOp_eisLow_sub hR hs hY.le, (memLp_gfun_all hR hY s).coeFn_toLp] with p h1 h2
  rw [h1, gL, h2]

/-- **`ũ_s = E_s − h_s`** in `L²(ν)` for `Re s > 2` with `Im ĥ(s) ≠ 0`. -/
theorem uL_eq_eisLow {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 2 < s.re)
    (him : (hhat R s).im ≠ 0) :
    uL R hR Y hY s = (memLp_eisLow hs hY.le).toLp (eisLow s Y) := by
  set K := ballOp isPU_rhoG isUChar_kub hR
  set u := (memLp_eisLow hs hY.le).toLp (eisLow s Y)
  have hz := mem_resolventSet_of_im_ne_zero (isSelfAdjoint_ballOp isPU_rhoG isUChar_kub hR) him
  have h2 : (algebraMap ℂ (Lp ℂ 2 (muR rhoG) →L[ℂ] Lp ℂ 2 (muR rhoG)) (hhat R s) - K) u =
      -gL R hR Y hY s := by
    rw [← ballOp_toLp_eisLow_sub hR hY hs, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self]
    abel
  have h3 := resolvent_sub_apply hz u
  rw [h2, map_neg] at h3
  exact h3

theorem cosh_sub_nonneg (r : ℝ) : 0 ≤ 2 * Real.cosh r - 2 := by
  linarith [Real.one_le_cosh r]

/-- **`s ↦ ũ_s` is complex-differentiable into `L²(ν)` wherever `Im ĥ(s) ≠ 0`**, for `R = 2cosh r − 2` and
`Y > 0` (round 418's `differentiable_hhat`, round 419's `hasDerivAt_resolvent_of_im_ne_zero`). -/
theorem differentiableAt_uL {r : ℝ} (hr : 0 ≤ r) {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ}
    (him : (hhat (2 * Real.cosh r - 2) s₀).im ≠ 0) :
    DifferentiableAt ℂ (uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY) s₀ := by
  set R := 2 * Real.cosh r - 2
  set K := ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r)
  have hK := isSelfAdjoint_ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r)
  have h1 : HasDerivAt (fun s => resolvent K (hhat R s))
      (deriv (hhat R) s₀ • -resolvent K (hhat R s₀) ^ 2) s₀ :=
    (hasDerivAt_resolvent_of_im_ne_zero hK him).scomp s₀
      ((differentiable_hhat hr) s₀).hasDerivAt
  have h2 := h1.clm_apply (hasDerivAt_gL (cosh_sub_nonneg r) hY s₀)
  exact h2.neg.differentiableAt

/-- **Pairings with `ũ_s` are holomorphic wherever `Im ĥ(s) ≠ 0`.** -/
theorem differentiableAt_inner_uL {r : ℝ} (hr : 0 ≤ r) {Y : ℝ} (hY : 0 < Y)
    (y : Lp ℂ 2 (muR rhoG)) {s₀ : ℂ} (him : (hhat (2 * Real.cosh r - 2) s₀).im ≠ 0) :
    DifferentiableAt ℂ (fun s => inner ℂ y (uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY s))
      s₀ :=
  ((innerSL ℂ y).differentiableAt).comp s₀ (differentiableAt_uL hr hY him)

end Eis

end

#print axioms Eis.lintegral_puLe_top_mul_le
#print axioms Eis.psC_lt_top
#print axioms Eis.norm_le_pow_of_vanish
#print axioms Eis.lintegral_pseis_sq_le
#print axioms Eis.eLpNorm_pseis_le
#print axioms Eis.memLp_pseis_of_vanish
#print axioms Eis.norm_gWt_le
#print axioms Eis.measurable_gWt
#print axioms Eis.gWt_eq_zero
#print axioms Eis.snd_mem_Icc_of_mem_hball
#print axioms Eis.rpow_le_add_of_mem_Icc
#print axioms Eis.abs_log_le_of_mem_Icc
#print axioms Eis.integrableOn_hball_of_le
#print axioms Eis.measurable_ballInt
#print axioms Eis.measurable_gInt
#print axioms Eis.measurable_gDer
#print axioms Eis.integrableOn_gWt
#print axioms Eis.ballInt_gWt_eq_zero
#print axioms Eis.snd_mem_shell
#print axioms Eis.norm_ballInt_gWt_le
#print axioms Eis.gProf_eq_gInt
#print axioms Eis.shM_nonneg
#print axioms Eis.shL_nonneg
#print axioms Eis.norm_cpow_le_shM
#print axioms Eis.abs_log_le_shL
#print axioms Eis.norm_cpow_taylor_le
#print axioms Eis.gInt_eq_zero_of_lt
#print axioms Eis.gDer_eq_zero_of_lt
#print axioms Eis.norm_gInt_le
#print axioms Eis.norm_gDer_le
#print axioms Eis.gInt_taylor
#print axioms Eis.memLp_gfun_all
#print axioms Eis.memLp_pseis_gDer
#print axioms Eis.shell_lt_of_lt_div
#print axioms Eis.hasDerivAt_gL
#print axioms Eis.differentiable_gL
#print axioms Eis.continuous_gL
#print axioms Eis.ballOp_toLp_eisLow_sub
#print axioms Eis.uL_eq_eisLow
#print axioms Eis.cosh_sub_nonneg
#print axioms Eis.differentiableAt_uL
#print axioms Eis.differentiableAt_inner_uL
