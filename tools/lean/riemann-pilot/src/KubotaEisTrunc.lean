import KubotaBallKernel
import KubotaConstTerm

/-! # The truncated Eisenstein series, and `g_s` (round 423)

S5f-10 of round 360's plan, part 6 (S5f-10c). Round 422 identified round 421's ball operator `K` with the ball
average `T_R` of round 418 on automorphic functions. This round takes `Γ_1(3)` with Kubota's character. It
builds the truncated Eisenstein series `E_s − h_s` and the function `g_s = (K − ĥ(s))(E_s − h_s)` that the
resolvent is planned to act on.

* **`Γ_1(3)` with Kubota's character** (`rhoG`, a definition, and the instances `finite_quot_three`,
  `finiteIndex_Gam3` and `finite_quot_Gam3`; `isUChar_kub` and `isPU_rhoG`): `κ` is a unitary character on
  `Γ_1(3)` (round 382's `kub_mul_Gam3`, round 387's `norm_kub`), `Γ_1(3)` has finite index in `SL_2(ℤ[ω])`,
  and `ρ_G = Σ_{q∈SL_2(ℤ[ω])/Γ_1(3)} ρ(q·)` is a partition of unity for it (round 386's `isPU_puLe_top`).
* **Pseudo-Eisenstein series** (`psTerm` and `pseis`, definitions; **`isAut_pseis`**, **`measurable_pseis`**
  and **`summable_psTerm`**, with `eisTerm_eq_psTerm`, `eis1_eq_pseis`, `psTerm_of_not_bRow`, `psTerm_add`,
  `psTerm_const_mul`, `psTerm_congr`, `pseis_congr`, `psTerm_rowMul`, `measurable_height`,
  `measurable_psTerm`, `norm_psTerm_le`, `pseis_add`, `pseis_const_mul` and `pseis_sub`):
  `E(f)(w) = Σ_{(c, d)} (c/d)₃·f(v(γw))` over the bottom rows of `Γ_1(3)`, for any `f : ℝ → ℂ`. Round 387's
  series is `E(v^s)` by definition. `E(f)` is automorphic for every `f`, measurable for measurable `f`, and
  absolutely convergent when `|f(v)| ≤ C·v^τ` on `(0, ∞)` with `τ > 2`.
* **Growth at the cusps, and `L²`** (**`norm_pseis_slAct_sub_le`**, **`lintegral_puLe_top_mul_lt_top`** and
  **`memLp_pseis`**, with `height_slAct_of_fst` and `memLp_two_of_lintegral`): under that bound,
  `|E(f)(g·w) − a_g·f(v)| ≤ C·cuspC(τ)·v^{2−τ}` for every `g ∈ SL_2(ℤ[ω])` and `v ≥ 1/2`, by round 388's
  argument for `E(v^s)`. A function bounded on the Siegel set at every cusp has a finite integral over `Γ\H³`
  for `Γ` of finite index. So `E(f)` is in `L²(ν)`, `ν = ρ_G dμ`, for `f` measurable and bounded with
  `|f(v)| ≤ C·v^τ`.
* **The ball average** (`bTrans`, a definition; **`bavg_pseis`** and **`bavg_eis1`**, with
  `le_snd_of_mem_hball`, `snd_le_of_mem_hball`, `height_le_of_mem_hball`, `bavg_snd_eq`, `psTerm_eq_of_row`
  and `bavg_psTerm`): heights on `B_R(p)` lie between `v(p)/(R + 2)` and `(R + 2)v(p)`, and for `R ≥ 0` and
  `f` measurable under that bound, `T_R E(f) = E(Bf)` with `Bf(v) = ∫_{B_R(0, v)} f(v') dμ` (Mathlib's
  `integral_tsum`). For `f = v^s`, round 418's `bavg_cpow` gives `T_R E_s = ĥ(s)·E_s` for `Re s > 2`.
* **The truncation** (`lowF`, `highF`, `eisLow` and `eisHigh`, definitions; **`eis1_eq_eisLow_add_eisHigh`**
  and **`memLp_eisLow`**, with `measurable_lowF`, `measurable_highF`, `norm_lowF_le`, `norm_lowF_le_Y`,
  `norm_highF_le`, `isAut_eisLow` and `measurable_eisLow`): `h_s = E(1[v ≥ Y]v^s)` and
  `E_s − h_s = E(1[v < Y]v^s)`, so `E_s = (E_s − h_s) + h_s` for `Re s > 2`, and `E_s − h_s` is in `L²(ν)` for
  `Re s > 2` and `Y ≥ 0`.
* **`g_s`** (`gProf` and `gfun`, definitions, and the instance `sFinite_uhsMeasure`; **`ballOp_eisLow_sub`**,
  **`gProf_eq_zero_of_lt`**, **`gProf_eq_zero_of_ge`** and **`memLp_gfun`**, with
  `uhsMeasure_hball_lt_top_of_mem`, `norm_bTrans_le_const`, `norm_bTrans_le`, `bavg_eisLow_sub`,
  `measurable_bTrans`, `measurable_gProf`, `norm_gProf_le` and `norm_gProf_le_pow`): `g_s = E(G_s)` with
  `G_s(v) = B(1[v′ < Y]v′^s)(v) − ĥ(s)·1[v < Y]v^s`. Then `(K − ĥ(s))(E_s − h_s) = g_s` in `L²(ν)` for
  `Re s > 2`, `R ≥ 0` and `Y ≥ 0` (round 422's `ballOp_toLp_ae_eq_bavg`). For `R ≥ 0` and `v > 0`,
  `G_s(v) = 0` unless `Y/(R + 2) ≤ v < (R + 2)Y`, and for `R ≥ 0` and `Y > 0`, `g_s` is in `L²(ν)` for every
  `s` with `Re s ≥ 0`.
-/

open MeasureTheory Set Filter NumberField Ideal
open scoped ENNReal ComplexConjugate MatrixGroups InnerProductSpace

noncomputable section

namespace Eis

/-! ### `Γ_1(3)` with Kubota's character -/

/-- **Kubota's character is a unitary character on `Γ_1(3)`** (round 382's `kub_mul_Gam3`, round 387's
`norm_kub`). -/
theorem isUChar_kub : IsUChar Gam3 (fun g => kub ↑g) where
  map_mul _ hg _ hh := kub_mul_Gam3 hg hh
  norm_eq g hg := norm_kub g.2 (mem_Gam3.1 hg)

instance finite_quot_three : Finite (𝓞 K ⧸ span {(3 : 𝓞 K)}) := by
  have := finite_quot_three_mul (one_ne_zero : (1 : 𝓞 K) ≠ 0)
  rwa [mul_one] at this

instance finiteIndex_Gam3 : Gam3.FiniteIndex := by
  unfold Gam3; infer_instance

/-- **`Γ_1(3)` has finite index**, as the kernel of reduction to `SL_2(ℤ[ω]/3)`. -/
instance finite_quot_Gam3 : Finite ((⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Gam3.subgroupOf ⊤) := by
  have h : (Gam3.subgroupOf ⊤).FiniteIndex := ⟨by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  infer_instance

/-- The partition of unity for `Γ_1(3)` from round 385's `rhoK` (round 386's `isPU_puLe_top`). -/
def rhoG : ℂ × ℝ → ℝ≥0∞ := puLe ⊤ Gam3 rhoK

theorem isPU_rhoG : IsPU Gam3 rhoG := isPU_puLe_top Gam3

/-! ### Pseudo-Eisenstein series -/

open Classical in
/-- The terms of a pseudo-Eisenstein series: `(c/d)₃·f(v/(|cz + d|² + |c|²v²))` on the bottom rows of
`Γ_1(3)`. -/
def psTerm (f : ℝ → ℂ) (p : ℂ × ℝ) (cd : 𝓞 K × 𝓞 K) : ℂ :=
  if BRow cd then σO (cub cd.1 (span {cd.2})) * f (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) else 0

/-- **The pseudo-Eisenstein series** of `f`: `E(f)(w) = Σ_{(c, d)} (c/d)₃·f(v(γw))` over the bottom rows
`(c, d)` of the elements `γ` of `Γ_1(3)`. Round 387's series is `E(v^s)`. -/
def pseis (f : ℝ → ℂ) (p : ℂ × ℝ) : ℂ := ∑' cd, psTerm f p cd

theorem eisTerm_eq_psTerm (s : ℂ) (p : ℂ × ℝ) (cd : 𝓞 K × 𝓞 K) :
    eisTerm s p cd = psTerm (fun v => ((v : ℝ) : ℂ) ^ s) p cd := rfl

theorem eis1_eq_pseis (s : ℂ) : eis1 s = pseis (fun v => ((v : ℝ) : ℂ) ^ s) := rfl

theorem psTerm_of_not_bRow (f : ℝ → ℂ) (p : ℂ × ℝ) {cd : 𝓞 K × 𝓞 K} (h : ¬ BRow cd) :
    psTerm f p cd = 0 := by
  unfold psTerm
  simp [h]

theorem psTerm_add (f g : ℝ → ℂ) (p : ℂ × ℝ) (cd : 𝓞 K × 𝓞 K) :
    psTerm (fun v => f v + g v) p cd = psTerm f p cd + psTerm g p cd := by
  unfold psTerm
  split_ifs <;> ring

theorem psTerm_const_mul (a : ℂ) (f : ℝ → ℂ) (p : ℂ × ℝ) (cd : 𝓞 K × 𝓞 K) :
    psTerm (fun v => a * f v) p cd = a * psTerm f p cd := by
  unfold psTerm
  split_ifs <;> ring

/-- Only the values on `(0, ∞)` matter. -/
theorem psTerm_congr {f g : ℝ → ℂ} (hfg : ∀ v, 0 < v → f v = g v) {p : ℂ × ℝ} (hp : p ∈ UHS)
    (cd : 𝓞 K × 𝓞 K) : psTerm f p cd = psTerm g p cd := by
  unfold psTerm
  split_ifs with h
  · rw [hfg _ (div_pos hp (uhsDen_pos_of_BRow h hp))]
  · rfl

theorem pseis_congr {f g : ℝ → ℂ} (hfg : ∀ v, 0 < v → f v = g v) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    pseis f p = pseis g p :=
  tsum_congr fun cd => psTerm_congr hfg hp cd

/-- **The terms along `Γ_1(3)`**: the term of `(c, d)·g⁻¹` at `g·p` is `κ(g)` times the term of `(c, d)`
at `p`. -/
theorem psTerm_rowMul {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (f : ℝ → ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS)
    (cd : 𝓞 K × 𝓞 K) : psTerm f (slAct g p) (rowMul g⁻¹ cd) = kub ↑g * psTerm f p cd := by
  unfold psTerm
  by_cases h : BRow cd
  · have h' : BRow (rowMul g⁻¹ cd) := bRow_rowMul (Gam3.inv_mem hg) h
    simp only [h, h', ↓reduceIte]
    rw [cub_rowMul (Gam3.inv_mem hg) h, kub_inv_Gam3 hg, Complex.conj_conj, height_rowMul g h' hp,
      ← rowMul_mul, inv_mul_cancel, rowMul_one]
    ring
  · have h' : ¬ BRow (rowMul g⁻¹ cd) :=
      fun h'' => h ((bRow_rowMul_iff (Gam3.inv_mem hg) cd).1 h'')
    simp only [h, h', ↓reduceIte, mul_zero]

/-- **Automorphy**: `E(f)(γ·w) = κ(γ)·E(f)(w)` for `γ ∈ Γ_1(3)`, for every `f`. -/
theorem isAut_pseis (f : ℝ → ℂ) : IsAut Gam3 (fun g => kub ↑g) (pseis f) := by
  intro g hg p hp
  unfold pseis
  calc ∑' cd, psTerm f (slAct g p) cd = ∑' cd, psTerm f (slAct g p) (rowMul g⁻¹ cd) :=
        ((rowEquiv g⁻¹).tsum_eq (psTerm f (slAct g p))).symm
    _ = ∑' cd, kub ↑g * psTerm f p cd := tsum_congr (psTerm_rowMul hg f hp)
    _ = kub ↑g * ∑' cd, psTerm f p cd := tsum_mul_left

theorem measurable_height (cd : 𝓞 K × 𝓞 K) :
    Measurable fun p : ℂ × ℝ => p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 := by
  unfold uhsDen
  fun_prop

theorem measurable_psTerm {f : ℝ → ℂ} (hf : Measurable f) (cd : 𝓞 K × 𝓞 K) :
    Measurable fun p : ℂ × ℝ => psTerm f p cd := by
  unfold psTerm
  split_ifs
  · exact measurable_const.mul (hf.comp (measurable_height cd))
  · exact measurable_const

theorem measurable_pseis {f : ℝ → ℂ} (hf : Measurable f) : Measurable (pseis f) :=
  Measurable.tsum fun cd => measurable_psTerm hf cd

open Classical in
/-- **The terms under a power bound**: `|f(v)| ≤ C·v^τ` on `(0, ∞)` bounds the term of `(c, d)` by `C` times
its height to the power `τ`. -/
theorem norm_psTerm_le {f : ℝ → ℂ} {C τ : ℝ} (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : 𝓞 K × 𝓞 K) :
    ‖psTerm f p cd‖ ≤
      C * if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ τ else 0 := by
  unfold psTerm
  split_ifs with h
  · rw [norm_mul, norm_σO_cub h.2.2 h.1, one_mul]
    exact hf _ (div_pos hp (uhsDen_pos_of_BRow h hp))
  · simp

/-- **Absolute convergence** under `|f(v)| ≤ C·v^τ` with `τ > 2`. -/
theorem summable_psTerm {f : ℝ → ℂ} {C τ : ℝ} (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) {p : ℂ × ℝ} (hp : p ∈ UHS) : Summable (psTerm f p) :=
  Summable.of_norm_bounded ((summable_height_rpow hτ hp).mul_left C) (norm_psTerm_le hf hp)

theorem pseis_add {f g : ℝ → ℂ} {C C' τ : ℝ} (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) (hg : ∀ v, 0 < v → ‖g v‖ ≤ C' * v ^ τ) {p : ℂ × ℝ}
    (hp : p ∈ UHS) : pseis (fun v => f v + g v) p = pseis f p + pseis g p := by
  unfold pseis
  rw [← (summable_psTerm hτ hf hp).tsum_add (summable_psTerm hτ hg hp)]
  exact tsum_congr fun cd => psTerm_add f g p cd


theorem pseis_const_mul (a : ℂ) (f : ℝ → ℂ) (p : ℂ × ℝ) :
    pseis (fun v => a * f v) p = a * pseis f p := by
  unfold pseis
  rw [← tsum_mul_left]
  exact tsum_congr fun cd => psTerm_const_mul a f p cd

theorem pseis_sub {f g : ℝ → ℂ} {C C' τ : ℝ} (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) (hg : ∀ v, 0 < v → ‖g v‖ ≤ C' * v ^ τ) {p : ℂ × ℝ}
    (hp : p ∈ UHS) : pseis (fun v => f v - g v) p = pseis f p - pseis g p := by
  have hg' : ∀ v, 0 < v → ‖-g v‖ ≤ C' * v ^ τ := fun v hv => by rw [norm_neg]; exact hg v hv
  have e := pseis_add hτ hf hg' hp
  simp only [← sub_eq_add_neg] at e
  rw [e, show (fun v => -g v) = fun v => (-1 : ℂ) * g v from funext fun v => by ring,
    pseis_const_mul]
  ring

/-! ### Growth at the cusps, and square-integrability -/

/-- At a row with `(c, d)·g = (0, *)` the height at `g·p` is `v`. -/
theorem height_slAct_of_fst {g : SL(2, 𝓞 K)} {cd : 𝓞 K × 𝓞 K} (h : BRow cd)
    (h0 : (rowMul g cd).1 = 0) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 = p.2 := by
  rw [height_rowMul g h hp, h0]
  obtain ⟨u, hu⟩ := isUnit_rowMul_snd h h0
  have hD : uhsDen (σO 0) (σO (u : 𝓞 K)) p.1 p.2 = 1 := by
    unfold uhsDen
    rw [map_zero, zero_mul, zero_add, normSq_σO_unit, Complex.normSq_zero, zero_mul, add_zero]
  rw [← hu, hD, div_one]

open Classical in
/-- **A pseudo-Eisenstein series at the cusp `g·∞`**: for `|f(v)| ≤ C·v^τ` on `(0, ∞)` with `C ≥ 0` and
`τ > 2`, `|E(f)(g·w) − a_g·f(v)| ≤ C·cuspC(τ)·v^{2−τ}` for every `g ∈ SL_2(ℤ[ω])` and `v ≥ 1/2`, with
`a_g = cuspA g` (round 388). -/
theorem norm_pseis_slAct_sub_le {f : ℝ → ℂ} {C τ : ℝ} (hC : 0 ≤ C) (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) (g : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hv : 1 / 2 ≤ p.2) :
    ‖pseis f (slAct g p) - cuspA g * f p.2‖ ≤ C * (cuspC τ * p.2 ^ (2 - τ)) := by
  have hp : p ∈ UHS := show 0 < p.2 by linarith
  have hgp : slAct g p ∈ UHS := slAct_mem g hp
  set F := fun cd : 𝓞 K × 𝓞 K => psTerm f (slAct g p) cd with hFdef
  have hN : Summable fun cd => ‖F cd‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_psTerm_le hf hgp)
      ((summable_height_rpow hτ hgp).mul_left C)
  have h1 : Summable fun cd => if (rowMul g cd).1 = 0 then F cd else 0 :=
    Summable.of_norm_bounded hN fun cd => by split_ifs <;> simp
  have h2 : Summable fun cd => if (rowMul g cd).1 = 0 then 0 else F cd :=
    Summable.of_norm_bounded hN fun cd => by split_ifs <;> simp
  have hsplit : pseis f (slAct g p) = ∑' cd, (if (rowMul g cd).1 = 0 then F cd else 0) +
      ∑' cd, (if (rowMul g cd).1 = 0 then 0 else F cd) := by
    rw [← h1.tsum_add h2]
    refine tsum_congr fun cd => ?_
    split_ifs <;> simp [F]
  have hA : ∑' cd, (if (rowMul g cd).1 = 0 then F cd else 0) = cuspA g * f p.2 := by
    unfold cuspA
    rw [← tsum_mul_right]
    refine tsum_congr fun cd => ?_
    by_cases h0 : (rowMul g cd).1 = 0
    · by_cases hb : BRow cd
      · simp only [h0, hb, and_self, ↓reduceIte, F, psTerm, height_slAct_of_fst hb h0 hp]
      · simp only [h0, hb, false_and, ↓reduceIte, zero_mul, F, psTerm_of_not_bRow f _ hb]
    · simp [h0]
  rw [hsplit, hA, add_sub_cancel_left]
  obtain ⟨hsum, hle⟩ := summable_height_ne hτ p.1 hv
  refine (tsum_of_norm_bounded (((rowEquiv g).hasSum_iff.2 hsum.hasSum).mul_left C)
    fun cd => ?_).trans (mul_le_mul_of_nonneg_left hle hC)
  change _ ≤ C * (if (rowMul g cd).1 = 0 then 0 else
    (p.2 / uhsDen (σO (rowMul g cd).1) (σO (rowMul g cd).2) p.1 p.2) ^ τ)
  by_cases h0 : (rowMul g cd).1 = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    refine (norm_psTerm_le hf hgp cd).trans (mul_le_mul_of_nonneg_left ?_ hC)
    split_ifs with hb
    · rw [height_rowMul g hb hp]
    · exact Real.rpow_nonneg (div_nonneg hp.le (uhsDen_nonneg _ _ _ _)) _

/-- A measurable `u` with `∫|u|² dν < ∞` is in `L²(ν)`. -/
theorem memLp_two_of_lintegral {ρ : ℂ × ℝ → ℝ≥0∞} {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (h : ∫⁻ q, ‖u q‖ₑ ^ 2 ∂(muR ρ) < ⊤) : MemLp u 2 (muR ρ) := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hum.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

/-- **Bounded on the Siegel set at every cusp, so integrable over `Γ\H³`**: for `Γ` of finite index and
`F` bounded on `g·K` for every `g ∈ SL_2(ℤ[ω])`, with `K` round 385's Siegel set,
`∫Σ_{q∈SL_2(ℤ[ω])/Γ} ρ(q·p)·F(p) dμ < ∞`. -/
theorem lintegral_puLe_top_mul_lt_top (Γ : Subgroup SL(2, 𝓞 K))
    [Finite ((⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤)] {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hb : ∀ g : SL(2, 𝓞 K), ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ p ∈ siegelK, F (slAct g p) ≤ C) :
    ∫⁻ p, puLe ⊤ Γ rhoK p * F p ∂uhsMeasure < ⊤ := by
  have h1 : ∀ q : (⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤,
      ∫⁻ p, rhoK (slAct (q.out : SL(2, 𝓞 K)) p) * F p ∂uhsMeasure < ⊤ := by
    intro q
    set g : SL(2, 𝓞 K) := ((q.out : (⊤ : Subgroup SL(2, 𝓞 K))) : SL(2, 𝓞 K))
    obtain ⟨C, hC, hCb⟩ := hb g⁻¹
    rw [← lintegral_slAct g⁻¹ (F := fun p => rhoK (slAct g p) * F p)
      ((measurable_rhoK.comp (measurable_slAct _)).mul hF)]
    calc ∫⁻ p, rhoK (slAct g (slAct g⁻¹ p)) * F (slAct g⁻¹ p) ∂uhsMeasure
        ≤ ∫⁻ p, rhoK p * C ∂uhsMeasure := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_UHS] with p hp
          rw [slAct_slAct_inv g hp]
          by_cases hK : p ∈ siegelK
          · gcongr
            exact hCb p hK
          · have h0 : rhoK p = 0 := by
              have := rhoK_le p
              rw [indicator_of_notMem hK] at this
              exact le_zero_iff.1 this
            simp [h0]
      _ = (∫⁻ p, rhoK p ∂uhsMeasure) * C := lintegral_mul_const _ measurable_rhoK
      _ < ⊤ := ENNReal.mul_lt_top lintegral_rhoK_lt_top hC.lt_top
  have hm : ∀ q : (⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤,
      AEMeasurable (fun p => rhoK (slAct (q.out : SL(2, 𝓞 K)) p) * F p) uhsMeasure :=
    fun q => ((measurable_rhoK.comp (measurable_slAct _)).mul hF).aemeasurable
  unfold puLe
  simp_rw [← ENNReal.tsum_mul_right]
  rw [lintegral_tsum hm]
  let := Fintype.ofFinite ((⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun q _ => h1 q

/-- **Pseudo-Eisenstein series in `L²(ν)`**: for `f` measurable and bounded on `(0, ∞)`, with
`|f(v)| ≤ C·v^τ` there for some `C ≥ 0` and `τ > 2`, `E(f)` is in `L²(ν)`, `ν = ρ dμ` for the partition of
unity `ρ` of `Γ_1(3)`. -/
theorem memLp_pseis {f : ℝ → ℂ} (hfm : Measurable f) {C τ D : ℝ} (hC : 0 ≤ C) (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) (hD : ∀ v, 0 < v → ‖f v‖ ≤ D) :
    MemLp (pseis f) 2 (muR rhoG) := by
  have hm := measurable_pseis hfm
  refine memLp_two_of_lintegral hm ?_
  rw [muR, lintegral_withDensity_eq_lintegral_mul _ isPU_rhoG.1 (hm.enorm.pow_const 2)]
  refine lintegral_puLe_top_mul_lt_top Gam3 (hm.enorm.pow_const 2) fun g => ?_
  refine ⟨ENNReal.ofReal (‖cuspA g‖ * D + C * (cuspC τ * (1 / 2 : ℝ) ^ (2 - τ))) ^ 2,
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top, fun p hp => ?_⟩
  have hv : 1 / 2 ≤ p.2 := hp.2
  have hp0 : (0 : ℝ) < p.2 := by linarith
  have h := norm_pseis_slAct_sub_le hC hτ hf g hv
  have h2 : p.2 ^ (2 - τ) ≤ (1 / 2 : ℝ) ^ (2 - τ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hv (by linarith)
  have hcC := cuspC_nonneg (by linarith : 1 < τ)
  have hb : ‖pseis f (slAct g p)‖ ≤ ‖cuspA g‖ * D + C * (cuspC τ * (1 / 2 : ℝ) ^ (2 - τ)) := by
    calc ‖pseis f (slAct g p)‖ ≤ ‖cuspA g * f p.2‖ + ‖pseis f (slAct g p) - cuspA g * f p.2‖ :=
          norm_le_insert' _ _
      _ ≤ ‖cuspA g‖ * D + C * (cuspC τ * (1 / 2 : ℝ) ^ (2 - τ)) := by
          rw [norm_mul]
          gcongr
          · exact hD _ hp0
          · exact h.trans (by gcongr)
  change ‖pseis f (slAct g p)‖ₑ ^ 2 ≤ _
  rw [← ofReal_norm]
  gcongr

/-! ### The ball average of a pseudo-Eisenstein series -/

/-- A point of the ball `B_R(p)` has height at least `v(p)/(R + 2)`. -/
theorem le_snd_of_mem_hball {R : ℝ} {p q : ℂ × ℝ} (hp : p ∈ UHS) (hq : q ∈ hball R p) :
    p.2 ≤ (R + 2) * q.2 := by
  obtain ⟨hq0, hle⟩ := hq
  have hp' : (0 : ℝ) < p.2 := hp
  have hq' : (0 : ℝ) < q.2 := hq0
  unfold ppi at hle
  rw [div_le_iff₀ (mul_pos hp' hq')] at hle
  refine le_of_not_gt fun hc => ?_
  nlinarith [Complex.normSq_nonneg (p.1 - q.1), mul_pos hp' (sub_pos.2 hc), mul_pos hq' hq']

/-- A point of the ball `B_R(p)` has height at most `(R + 2)·v(p)`. -/
theorem snd_le_of_mem_hball {R : ℝ} {p q : ℂ × ℝ} (hp : p ∈ UHS) (hq : q ∈ hball R p) :
    q.2 ≤ (R + 2) * p.2 := by
  obtain ⟨hq0, hle⟩ := hq
  have hp' : (0 : ℝ) < p.2 := hp
  have hq' : (0 : ℝ) < q.2 := hq0
  unfold ppi at hle
  rw [div_le_iff₀ (mul_pos hp' hq')] at hle
  refine le_of_not_gt fun hc => ?_
  nlinarith [Complex.normSq_nonneg (p.1 - q.1), mul_pos hq' (sub_pos.2 hc), mul_pos hp' hp']

/-- **Heights on a ball**: for `q ∈ B_R(p)` and a bottom row `(c, d)`, the height of `(c, d)` at `q` is at
most `R + 2` times its height at `p`. -/
theorem height_le_of_mem_hball {R : ℝ} {p q : ℂ × ℝ} (hp : p ∈ UHS) (hq : q ∈ hball R p)
    {cd : 𝓞 K × 𝓞 K} (h : BRow cd) :
    q.2 / uhsDen (σO cd.1) (σO cd.2) q.1 q.2 ≤
      (R + 2) * (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) := by
  obtain ⟨γ, -, h1, h2⟩ := exists_Gam3_of_BRow h
  have e : cd = (γ 1 0, γ 1 1) := by rw [h1, h2]
  rw [e, ← slAct_snd, ← slAct_snd]
  exact snd_le_of_mem_hball (slAct_mem γ hp) ((mem_hball_actP (det_map_σO γ.2) hp hq.1).2 hq)

/-- **A function of the height, averaged over a ball**, depends only on the height of the centre. -/
theorem bavg_snd_eq {R : ℝ} {f : ℝ → ℂ} (hf : Measurable f) {w : ℂ × ℝ} (hw : w ∈ UHS) :
    bavg R (fun q => f q.2) w = bavg R (fun q => f q.2) (0, w.2) := by
  have hw0 : ((0 : ℂ), w.2) ∈ UHS := hw
  have e : actP !![1, w.1; 0, 1] (0, w.2) = w := by
    simp only [actP, uhsAct_transl, zero_add]
  have h := bavg_comp_actP (R := R) (det_transl w.1) (f := fun q => f q.2) (hf.comp measurable_snd) hw0
  rw [e] at h
  rw [← h]
  unfold bavg
  refine setIntegral_congr_fun (measurableSet_hball R _) fun q _ => ?_
  simp only [actP, uhsAct_transl]

/-- The ball transform of a function of the height: `Bf(v) = ∫_{B_R(0, v)} f(v') dμ`. -/
def bTrans (R : ℝ) (f : ℝ → ℂ) (v : ℝ) : ℂ := bavg R (fun q => f q.2) (0, v)

/-- The term of `(c, d)` through an element `γ` of `Γ_1(3)` with bottom row `(c, d)`. -/
theorem psTerm_eq_of_row {cd : 𝓞 K × 𝓞 K} (h : BRow cd) {γ : SL(2, 𝓞 K)} (h1 : γ 1 0 = cd.1)
    (h2 : γ 1 1 = cd.2) (f : ℝ → ℂ) (q : ℂ × ℝ) :
    psTerm f q cd = σO (cub cd.1 (span {cd.2})) * f (slAct γ q).2 := by
  unfold psTerm
  simp only [h, ↓reduceIte]
  rw [slAct_snd, h1, h2]

/-- **The terms over a ball**: `∫_{B_R(p)} (term of f at (c, d)) dμ` is the term of `Bf` at `(c, d)`. -/
theorem bavg_psTerm (R : ℝ) {f : ℝ → ℂ} (hf : Measurable f) {p : ℂ × ℝ} (hp : p ∈ UHS)
    (cd : 𝓞 K × 𝓞 K) : bavg R (fun q => psTerm f q cd) p = psTerm (bTrans R f) p cd := by
  by_cases h : BRow cd
  · obtain ⟨γ, -, h1, h2⟩ := exists_Gam3_of_BRow h
    simp_rw [psTerm_eq_of_row h h1 h2]
    have hb : bavg R (fun q => f (slAct γ q).2) p = bTrans R f (slAct γ p).2 := by
      rw [bTrans, ← bavg_snd_eq hf (slAct_mem γ hp)]
      exact bavg_comp_actP (det_map_σO γ.2) (f := fun q => f q.2) (hf.comp measurable_snd) hp
    unfold bavg at hb ⊢
    rw [integral_const_mul, hb]
  · simp_rw [psTerm_of_not_bRow _ _ h]
    simp [bavg]

open Classical in
/-- **The ball average of a pseudo-Eisenstein series**: `T_R E(f) = E(Bf)` for `R ≥ 0` and `f` measurable
with `|f(v)| ≤ C·v^τ` on `(0, ∞)`, `C ≥ 0`, `τ > 2`. -/
theorem bavg_pseis {R : ℝ} (hR : 0 ≤ R) {f : ℝ → ℂ} (hfm : Measurable f) {C τ : ℝ} (hC : 0 ≤ C)
    (hτ : 2 < τ) (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    bavg R (pseis f) p = pseis (bTrans R f) p := by
  have hτ0 : 0 ≤ τ := by linarith
  set M : 𝓞 K × 𝓞 K → ℝ := fun cd =>
    C * (R + 2) ^ τ * if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ τ else 0
    with hMdef
  have hM0 : ∀ cd, 0 ≤ M cd := fun cd => by
    simp only [hMdef]
    split_ifs
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg hp.le (uhsDen_nonneg _ _ _ _)) _)
    · simp
  have hMsum : Summable M := (summable_height_rpow hτ hp).mul_left _
  have hle : ∀ cd, ∀ q ∈ hball R p, ‖psTerm f q cd‖ ≤ M cd := by
    intro cd q hq
    refine (norm_psTerm_le hf hq.1 cd).trans ?_
    simp only [hMdef, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    split_ifs with hb
    · rw [← Real.mul_rpow (by linarith) (div_nonneg hp.le (uhsDen_nonneg _ _ _ _))]
      exact Real.rpow_le_rpow (div_nonneg hq.1.le (uhsDen_nonneg _ _ _ _))
        (height_le_of_mem_hball hp hq hb) hτ0
    · simp
  have hB := uhsMeasure_hball_lt_top hR
  rw [← uhsMeasure_hball R hp] at hB
  have hfin : ∑' cd, ∫⁻ q in hball R p, ‖psTerm f q cd‖ₑ ∂uhsMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' cd, ENNReal.ofReal (M cd) * uhsMeasure (hball R p)) ?_
      (ENNReal.tsum_le_tsum fun cd => ?_)
    · rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hM0 hMsum]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.ne
    · rw [← setLIntegral_const]
      refine setLIntegral_mono measurable_const fun q hq => ?_
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hle cd q hq)
  unfold bavg pseis
  rw [integral_tsum (fun cd => (measurable_psTerm hfm cd).aestronglyMeasurable) hfin]
  exact tsum_congr fun cd => bavg_psTerm R hfm hp cd

/-- **`E_s` is an eigenfunction of the ball average**: `T_R E_s = ĥ_R(s)·E_s` for `R ≥ 0` and `Re s > 2`. -/
theorem bavg_eis1 {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 2 < s.re) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    bavg R (eis1 s) p = hhat R s * eis1 s p := by
  have hf : ∀ v, 0 < v → ‖((v : ℝ) : ℂ) ^ s‖ ≤ 1 * v ^ s.re := fun v hv => by
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv]
  rw [eis1_eq_pseis, bavg_pseis hR (by fun_prop) zero_le_one hs hf hp,
    ← pseis_const_mul]
  refine pseis_congr (fun v hv => ?_) hp
  rw [bTrans, bavg_cpow R s (show ((0 : ℂ), v) ∈ UHS from hv)]

/-! ### The truncation -/

/-- `v^s` below height `Y`. -/
def lowF (s : ℂ) (Y : ℝ) (v : ℝ) : ℂ := if v < Y then ((v : ℝ) : ℂ) ^ s else 0

/-- `v^s` at height `Y` and above. -/
def highF (s : ℂ) (Y : ℝ) (v : ℝ) : ℂ := if v < Y then 0 else ((v : ℝ) : ℂ) ^ s

/-- **The truncated series `E_s − h_s`**: the terms of height below `Y`. -/
def eisLow (s : ℂ) (Y : ℝ) : ℂ × ℝ → ℂ := pseis (lowF s Y)

/-- **The truncation `h_s`**: the terms of height `Y` or above. -/
def eisHigh (s : ℂ) (Y : ℝ) : ℂ × ℝ → ℂ := pseis (highF s Y)

theorem measurable_lowF (s : ℂ) (Y : ℝ) : Measurable (lowF s Y) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (Complex.measurable_ofReal.pow_const s) measurable_const

theorem measurable_highF (s : ℂ) (Y : ℝ) : Measurable (highF s Y) :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Complex.measurable_ofReal.pow_const s)

theorem norm_lowF_le (s : ℂ) (Y : ℝ) {v : ℝ} (hv : 0 < v) : ‖lowF s Y v‖ ≤ 1 * v ^ s.re := by
  unfold lowF
  split_ifs
  · rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv]
  · rw [norm_zero, one_mul]
    exact Real.rpow_nonneg hv.le _

theorem norm_lowF_le_Y {s : ℂ} (hs : 0 ≤ s.re) {Y : ℝ} (hY : 0 ≤ Y) {v : ℝ} (hv : 0 < v) :
    ‖lowF s Y v‖ ≤ Y ^ s.re := by
  unfold lowF
  split_ifs with h
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
    exact Real.rpow_le_rpow hv.le h.le hs
  · rw [norm_zero]
    exact Real.rpow_nonneg hY _

theorem norm_highF_le (s : ℂ) (Y : ℝ) {v : ℝ} (hv : 0 < v) : ‖highF s Y v‖ ≤ 1 * v ^ s.re := by
  unfold highF
  split_ifs
  · rw [norm_zero, one_mul]
    exact Real.rpow_nonneg hv.le _
  · rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv]

/-- **`E_s = (E_s − h_s) + h_s`** for `Re s > 2`. -/
theorem eis1_eq_eisLow_add_eisHigh {s : ℂ} (hs : 2 < s.re) (Y : ℝ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eis1 s p = eisLow s Y p + eisHigh s Y p := by
  rw [eis1_eq_pseis, eisLow, eisHigh,
    ← pseis_add hs (fun v hv => norm_lowF_le s Y hv) (fun v hv => norm_highF_le s Y hv) hp]
  refine pseis_congr (fun v _ => ?_) hp
  unfold lowF highF
  split_ifs <;> simp

/-- **`E_s − h_s` is automorphic**, for every `s`. -/
theorem isAut_eisLow (s : ℂ) (Y : ℝ) : IsAut Gam3 (fun g => kub ↑g) (eisLow s Y) :=
  isAut_pseis _

theorem measurable_eisLow (s : ℂ) (Y : ℝ) : Measurable (eisLow s Y) :=
  measurable_pseis (measurable_lowF s Y)

/-- **`E_s − h_s` is in `L²(ν)`** for `Re s > 2` and `Y ≥ 0`. -/
theorem memLp_eisLow {s : ℂ} (hs : 2 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    MemLp (eisLow s Y) 2 (muR rhoG) :=
  memLp_pseis (measurable_lowF s Y) zero_le_one hs (fun v hv => norm_lowF_le s Y hv)
    (fun v hv => norm_lowF_le_Y (by linarith) hY hv)

/-! ### The ball transform of a function of the height -/

theorem uhsMeasure_hball_lt_top_of_mem {R : ℝ} (hR : 0 ≤ R) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    uhsMeasure (hball R p) < ⊤ := by
  rw [uhsMeasure_hball R hp]
  exact uhsMeasure_hball_lt_top hR

/-- **A bounded profile has a bounded ball transform**: `|f| ≤ D` on `(0, ∞)` gives `|Bf| ≤ D·V_R` there. -/
theorem norm_bTrans_le_const {R : ℝ} (hR : 0 ≤ R) {f : ℝ → ℂ} {D : ℝ}
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ D) {v : ℝ} (hv : 0 < v) :
    ‖bTrans R f v‖ ≤ D * uhsMeasure.real (hball R (0, 1)) := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  unfold bTrans bavg
  rw [show uhsMeasure.real (hball R (0, 1)) = uhsMeasure.real (hball R (0, v)) by
    simp only [Measure.real, uhsMeasure_hball R hv']]
  exact norm_setIntegral_le_of_norm_le_const (uhsMeasure_hball_lt_top_of_mem hR hv')
    fun q hq => hf _ hq.1

/-- **A power bound passes to the ball transform**: `|f(v)| ≤ C·v^τ` on `(0, ∞)` with `C ≥ 0`, `τ ≥ 0` gives
`|Bf(v)| ≤ C(R + 2)^τ V_R·v^τ` there. -/
theorem norm_bTrans_le {R : ℝ} (hR : 0 ≤ R) {f : ℝ → ℂ} {C τ : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) {v : ℝ} (hv : 0 < v) :
    ‖bTrans R f v‖ ≤ C * (R + 2) ^ τ * uhsMeasure.real (hball R (0, 1)) * v ^ τ := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  unfold bTrans bavg
  have h := norm_setIntegral_le_of_norm_le_const (μ := uhsMeasure) (f := fun q : ℂ × ℝ => f q.2)
    (C := C * ((R + 2) * v) ^ τ) (uhsMeasure_hball_lt_top_of_mem hR hv') fun q hq => by
      refine (hf _ hq.1).trans (mul_le_mul_of_nonneg_left ?_ hC)
      exact Real.rpow_le_rpow (le_of_lt hq.1) (snd_le_of_mem_hball hv' hq) hτ
  refine h.trans (le_of_eq ?_)
  rw [show uhsMeasure.real (hball R (0, v)) = uhsMeasure.real (hball R (0, 1)) by
    simp only [Measure.real, uhsMeasure_hball R hv'],
    Real.mul_rpow (by linarith) hv.le]
  ring

/-! ### `g_s = (T_R − ĥ(s))(E_s − h_s)` -/

/-- **The profile of `g_s`**: `G_s(v) = ∫_{B_R(0, v)} 1[v' < Y]v'^s dμ − ĥ_R(s)·1[v < Y]v^s`. -/
def gProf (R : ℝ) (s : ℂ) (Y : ℝ) (v : ℝ) : ℂ := bTrans R (lowF s Y) v - hhat R s * lowF s Y v

/-- **`g_s`**, the pseudo-Eisenstein series of the profile `G_s`. -/
def gfun (R : ℝ) (s : ℂ) (Y : ℝ) : ℂ × ℝ → ℂ := pseis (gProf R s Y)

/-- **`(T_R − ĥ(s))(E_s − h_s) = g_s`** pointwise, for `R ≥ 0` and `Re s > 2`. -/
theorem bavg_eisLow_sub {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 2 < s.re) (Y : ℝ) {p : ℂ × ℝ}
    (hp : p ∈ UHS) : bavg R (eisLow s Y) p - hhat R s * eisLow s Y p = gfun R s Y p := by
  have hσ : 0 ≤ s.re := by linarith
  have h1 : ∀ v, 0 < v → ‖lowF s Y v‖ ≤ 1 * v ^ s.re := fun v hv => norm_lowF_le s Y hv
  have h2 : ∀ v, 0 < v → ‖bTrans R (lowF s Y) v‖ ≤
      1 * (R + 2) ^ s.re * uhsMeasure.real (hball R (0, 1)) * v ^ s.re :=
    fun v hv => norm_bTrans_le hR zero_le_one hσ h1 hv
  have h3 : ∀ v, 0 < v → ‖hhat R s * lowF s Y v‖ ≤ ‖hhat R s‖ * v ^ s.re := fun v hv => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((h1 v hv).trans (by rw [one_mul])) (norm_nonneg _)
  rw [eisLow, bavg_pseis hR (measurable_lowF s Y) zero_le_one hs h1 hp, ← pseis_const_mul, gfun]
  exact (pseis_sub hs h2 h3 hp).symm

/-- **`(K − ĥ(s))(E_s − h_s) = g_s` in `L²(ν)`** for `R ≥ 0`, `Re s > 2` and `Y ≥ 0`, with `K` round 421's
ball operator for `Γ_1(3)` and Kubota's character. -/
theorem ballOp_eisLow_sub {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 2 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    (⇑(ballOp isPU_rhoG isUChar_kub hR ((memLp_eisLow hs hY).toLp (eisLow s Y)) -
        hhat R s • (memLp_eisLow hs hY).toLp (eisLow s Y)) : ℂ × ℝ → ℂ) =ᵐ[muR rhoG]
      gfun R s Y := by
  have hK := ballOp_toLp_ae_eq_bavg isPU_rhoG isUChar_kub hR (isAut_eisLow s Y)
    (measurable_eisLow s Y) (memLp_eisLow hs hY)
  filter_upwards [Lp.coeFn_sub (ballOp isPU_rhoG isUChar_kub hR ((memLp_eisLow hs hY).toLp
      (eisLow s Y))) (hhat R s • (memLp_eisLow hs hY).toLp (eisLow s Y)),
    Lp.coeFn_smul (hhat R s) ((memLp_eisLow hs hY).toLp (eisLow s Y)), hK,
    (memLp_eisLow hs hY).coeFn_toLp, ae_muR_UHS rhoG] with p h1 h2 h3 h4 hp
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul, bavg_eisLow_sub hR hs Y hp]

/-- **Below the shells**, `G_s(v) = 0`: for `(R + 2)v < Y` the ball `B_R(0, v)` lies below height `Y`, where
`T_R(v^s) = ĥ(s)v^s`. -/
theorem gProf_eq_zero_of_lt {R : ℝ} (hR : 0 ≤ R) (s : ℂ) {Y v : ℝ} (hv : 0 < v)
    (hvY : (R + 2) * v < Y) : gProf R s Y v = 0 := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  have hlt : v < Y := by nlinarith
  have hb : bTrans R (lowF s Y) v = bavg R (fun q => ((q.2 : ℝ) : ℂ) ^ s) (0, v) := by
    unfold bTrans bavg
    refine setIntegral_congr_fun (measurableSet_hball R _) fun q hq => ?_
    have := snd_le_of_mem_hball hv' hq
    simp only [lowF, show q.2 < Y by linarith, ↓reduceIte]
  rw [gProf, hb, bavg_cpow R s hv']
  simp only [lowF, hlt, ↓reduceIte, sub_self]

/-- **Above the shells**, `G_s(v) = 0`: for `v ≥ (R + 2)Y` the ball `B_R(0, v)` lies at height `Y` or
above. -/
theorem gProf_eq_zero_of_ge {R : ℝ} (hR : 0 ≤ R) (s : ℂ) {Y v : ℝ} (hv : 0 < v)
    (hvY : (R + 2) * Y ≤ v) : gProf R s Y v = 0 := by
  have hv' : ((0 : ℂ), v) ∈ UHS := hv
  have hb : bTrans R (lowF s Y) v = 0 := by
    unfold bTrans bavg
    have e : ∫ q in hball R (0, v), lowF s Y q.2 ∂uhsMeasure =
        ∫ q in hball R (0, v), (0 : ℂ) ∂uhsMeasure := by
      refine setIntegral_congr_fun (measurableSet_hball R _) fun q hq => ?_
      have h1 := le_snd_of_mem_hball hv' hq
      have h2 : Y ≤ q.2 := by
        refine le_of_not_gt fun h => ?_
        have : (R + 2) * q.2 < (R + 2) * Y := mul_lt_mul_of_pos_left h (by linarith)
        linarith
      simp only [lowF, not_lt.2 h2, ↓reduceIte]
    rw [e, integral_zero]
  have hge : ¬ v < Y := by
    intro h
    have hY : 0 < Y := hv.trans h
    nlinarith
  rw [gProf, hb]
  simp only [lowF, hge, ↓reduceIte, mul_zero, sub_zero]

instance sFinite_uhsMeasure : SFinite uhsMeasure := by
  unfold uhsMeasure; infer_instance

/-- The ball transform of a measurable profile is measurable (Mathlib's
`StronglyMeasurable.integral_prod_right'`). -/
theorem measurable_bTrans (R : ℝ) {f : ℝ → ℂ} (hf : Measurable f) : Measurable (bTrans R f) := by
  have hS : MeasurableSet {x : ℝ × (ℂ × ℝ) | x.2 ∈ hball R (0, x.1)} := by
    have e : {x : ℝ × (ℂ × ℝ) | x.2 ∈ hball R (0, x.1)} =
        {x | 0 < x.2.2} ∩ {x | ppi (0, x.1) x.2 ≤ R} := by
      ext x
      simp [hball, UHS]
    have hm : Measurable fun x : ℝ × (ℂ × ℝ) => ppi (0, x.1) x.2 := by
      unfold ppi
      fun_prop
    rw [e]
    exact (measurableSet_lt measurable_const measurable_snd.snd).inter
      (measurableSet_le hm measurable_const)
  have hF : StronglyMeasurable fun x : ℝ × (ℂ × ℝ) =>
      (hball R (0, x.1)).indicator (fun q => f q.2) x.2 := by
    refine Measurable.stronglyMeasurable ?_
    have e : (fun x : ℝ × (ℂ × ℝ) => (hball R (0, x.1)).indicator (fun q => f q.2) x.2) =
        {x : ℝ × (ℂ × ℝ) | x.2 ∈ hball R (0, x.1)}.indicator (fun x => f x.2.2) := by
      funext x
      by_cases h : x.2 ∈ hball R (0, x.1)
      · rw [indicator_of_mem h, indicator_of_mem (show x ∈ {x : ℝ × (ℂ × ℝ) |
          x.2 ∈ hball R (0, x.1)} from h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ {x : ℝ × (ℂ × ℝ) |
          x.2 ∈ hball R (0, x.1)} from h)]
    rw [e]
    exact (hf.comp measurable_snd.snd).indicator hS
  have h := hF.integral_prod_right' (ν := uhsMeasure)
  have e : bTrans R f = fun v => ∫ q, (hball R (0, v)).indicator (fun q => f q.2) q ∂uhsMeasure := by
    funext v
    rw [bTrans, bavg, integral_indicator (measurableSet_hball R _)]
  rw [e]
  exact h.measurable

/-- `G_s` is measurable. -/
theorem measurable_gProf (R : ℝ) (s : ℂ) (Y : ℝ) : Measurable (gProf R s Y) :=
  (measurable_bTrans R (measurable_lowF s Y)).sub (measurable_const.mul (measurable_lowF s Y))

/-- **`G_s` is bounded**, by `(V_R + |ĥ(s)|)·Y^σ`, for `Re s ≥ 0`, `R ≥ 0` and `Y ≥ 0`. -/
theorem norm_gProf_le {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 0 ≤ s.re) {Y : ℝ} (hY : 0 ≤ Y) {v : ℝ}
    (hv : 0 < v) :
    ‖gProf R s Y v‖ ≤ (uhsMeasure.real (hball R (0, 1)) + ‖hhat R s‖) * Y ^ s.re := by
  have h1 := norm_bTrans_le_const hR (fun v hv => norm_lowF_le_Y hs hY hv) hv
  have h2 := norm_lowF_le_Y hs hY hv
  calc ‖gProf R s Y v‖ ≤ ‖bTrans R (lowF s Y) v‖ + ‖hhat R s‖ * ‖lowF s Y v‖ := by
        rw [gProf, ← norm_mul]; exact norm_sub_le _ _
    _ ≤ Y ^ s.re * uhsMeasure.real (hball R (0, 1)) + ‖hhat R s‖ * Y ^ s.re := by
        gcongr
    _ = _ := by ring

/-- **`G_s` under a power bound**: `|G_s(v)| ≤ M·((R + 2)/Y)³·v³` with `M = (V_R + |ĥ(s)|)·Y^σ`, since `G_s`
vanishes below `Y/(R + 2)`. -/
theorem norm_gProf_le_pow {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 0 ≤ s.re) {Y : ℝ} (hY : 0 < Y)
    {v : ℝ} (hv : 0 < v) :
    ‖gProf R s Y v‖ ≤
      (uhsMeasure.real (hball R (0, 1)) + ‖hhat R s‖) * Y ^ s.re * ((R + 2) / Y) ^ (3 : ℝ) *
        v ^ (3 : ℝ) := by
  set M := (uhsMeasure.real (hball R (0, 1)) + ‖hhat R s‖) * Y ^ s.re with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ uhsMeasure.real (hball R (0, 1)) := measureReal_nonneg
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hY.le _)
  by_cases hlt : (R + 2) * v < Y
  · rw [gProf_eq_zero_of_lt hR s hv hlt, norm_zero]
    positivity
  · push Not at hlt
    have h1 : 1 ≤ ((R + 2) / Y) ^ (3 : ℝ) * v ^ (3 : ℝ) := by
      rw [← Real.mul_rpow (by positivity) hv.le]
      refine Real.one_le_rpow ?_ (by norm_num)
      rw [div_mul_eq_mul_div, le_div_iff₀ hY, one_mul]
      exact hlt
    calc ‖gProf R s Y v‖ ≤ M := norm_gProf_le hR hs hY.le hv
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * (((R + 2) / Y) ^ (3 : ℝ) * v ^ (3 : ℝ)) := mul_le_mul_of_nonneg_left h1 hM0
      _ = _ := by ring

/-- **`g_s` is in `L²(ν)` for every `s` with `Re s ≥ 0`**, `R ≥ 0` and `Y > 0`. -/
theorem memLp_gfun {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 0 ≤ s.re) {Y : ℝ} (hY : 0 < Y) :
    MemLp (gfun R s Y) 2 (muR rhoG) := by
  have hV : 0 ≤ uhsMeasure.real (hball R (0, 1)) := measureReal_nonneg
  exact memLp_pseis (measurable_gProf R s Y) (by positivity) (by norm_num : (2 : ℝ) < 3)
    (fun v hv => norm_gProf_le_pow hR hs hY hv) (fun v hv => norm_gProf_le hR hs hY.le hv)

end Eis

end

#print axioms Eis.isUChar_kub
#print axioms Eis.isPU_rhoG
#print axioms Eis.eisTerm_eq_psTerm
#print axioms Eis.eis1_eq_pseis
#print axioms Eis.psTerm_of_not_bRow
#print axioms Eis.psTerm_add
#print axioms Eis.psTerm_const_mul
#print axioms Eis.psTerm_congr
#print axioms Eis.pseis_congr
#print axioms Eis.psTerm_rowMul
#print axioms Eis.isAut_pseis
#print axioms Eis.measurable_height
#print axioms Eis.measurable_psTerm
#print axioms Eis.measurable_pseis
#print axioms Eis.norm_psTerm_le
#print axioms Eis.summable_psTerm
#print axioms Eis.pseis_add
#print axioms Eis.pseis_const_mul
#print axioms Eis.pseis_sub
#print axioms Eis.height_slAct_of_fst
#print axioms Eis.norm_pseis_slAct_sub_le
#print axioms Eis.memLp_two_of_lintegral
#print axioms Eis.lintegral_puLe_top_mul_lt_top
#print axioms Eis.memLp_pseis
#print axioms Eis.le_snd_of_mem_hball
#print axioms Eis.snd_le_of_mem_hball
#print axioms Eis.height_le_of_mem_hball
#print axioms Eis.bavg_snd_eq
#print axioms Eis.psTerm_eq_of_row
#print axioms Eis.bavg_psTerm
#print axioms Eis.bavg_pseis
#print axioms Eis.bavg_eis1
#print axioms Eis.measurable_lowF
#print axioms Eis.measurable_highF
#print axioms Eis.norm_lowF_le
#print axioms Eis.norm_lowF_le_Y
#print axioms Eis.norm_highF_le
#print axioms Eis.eis1_eq_eisLow_add_eisHigh
#print axioms Eis.isAut_eisLow
#print axioms Eis.measurable_eisLow
#print axioms Eis.memLp_eisLow
#print axioms Eis.uhsMeasure_hball_lt_top_of_mem
#print axioms Eis.norm_bTrans_le_const
#print axioms Eis.norm_bTrans_le
#print axioms Eis.bavg_eisLow_sub
#print axioms Eis.ballOp_eisLow_sub
#print axioms Eis.gProf_eq_zero_of_lt
#print axioms Eis.gProf_eq_zero_of_ge
#print axioms Eis.measurable_bTrans
#print axioms Eis.measurable_gProf
#print axioms Eis.norm_gProf_le
#print axioms Eis.norm_gProf_le_pow
#print axioms Eis.memLp_gfun
