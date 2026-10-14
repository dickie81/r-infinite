import KubotaCuspZeroPhi

/-! # θ at the cusp `0` (round 442)

S5f-12 of round 360's plan, part 3. Round 441's next step planned θ̃∘S's constant term through a
pseudo-Eisenstein series at the cusp `0`. `Γ_1(3)` is normal in `SL_2(ℤ[ω])` (round 382's `gam3_normal`) and
`κ(SγS⁻¹) = κ(γ)` (round 382's `kub_conj_toSL`), so that series is `E(ψ)∘S⁻¹`, and this round moves round
433's argument by `S`. For `r > 0`, `Y > 0`, θ's representative `θ̃` (round 425's `thetaF`), and `ψ`
measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`:

* **Conjugation by `S`** (**`isAut_comp_sS`**, **`isPU_rhoG_comp`**, **`memLp_comp`** and
  **`integral_conj_sS_inv_mul`**, with `slAct_conj`, `kub_sS_conj`, `kub_sS_inv_conj`, `isAut_comp_sS_inv`,
  `lintegral_comp_eq` and `lintegral_enorm_comp_lt_top`): `u∘S` is automorphic on `Γ_1(3)` with `κ` when `u`
  is; `ρ_G∘g` is a partition of unity for `Γ_1(3)` for every `g ∈ SL_2(ℤ[ω])`; `u∘g` is in `L²(ν)` when `u` is
  and `|u|` is invariant; and `∫conj u(S⁻¹·p)·w(p) dν = ∫conj u(p)·w(S·p) dν` for `u` and `w` automorphic, by
  round 439's change of variables and independence of the partition of unity.
* **θ at `S·p`** (`thetaFS`, a definition; **`setLIntegral_sS_lt_top`** and **`integrableOn_sS`**, with
  `isAut_thetaFS`, `measurable_thetaFS` and `memLp_thetaFS`): `θ̃∘S` is automorphic and in `L²(ν)`, and an
  automorphic `u` in `L²(ν)`, moved by `S`, is integrable on `3P × [α, β]` (round 432's
  `lintegral_boxZ_lt_top`).
* **The band at `S·p`** (**`eisLow_sS_eq_band`**, with `height_sS_le` and `eisHigh_sS_eq_band`): every height
  at `S·p` is at most `1/v` (round 440's `rowMul_sS`, round 427's `height_le_inv`), so
  `E_s − h_s = E_s − E(1[Y ≤ v ≤ Y + β + 1/α]v^s)` at `S·p` for `v ≥ α`, as round 430's `eisLow_eq_band` on
  `3P × [α, β]`.
* **The pairing at the cusp `0`** (`pseisS`, a definition; **`inner_toLp_pseisS`** and
  **`inner_pseisS_uL_band`**, with `isAut_pseisS`, `memLp_pseisS` and `integrableOn_fundP3_of_lintegral`):
  `⟨E(ψ)∘S⁻¹, w⟩ = ∫_{3P×(0,∞)} conj ψ(v)·w(S·(z, v)) dz dv/v³` for `w` automorphic in `L²(ν)` (round 426's
  `integral_conj_pseis_mul`), and for `Re s > 2` with `Im ĥ(s) ≠ 0`,
  `⟨E(ψ)∘S⁻¹, ũ_s⟩ = (9√3/2)·φ₀(s)M_ψ(s) − ⟨E(ψ)∘S⁻¹, E(1[Y ≤ v ≤ H]v^s)⟩` with `H = Y + β + 1/α`, by round
  440's `constTerm_eis1_sS`.
* **θ's constant term at the cusp `0`** (**`inner_pseisS_thetaL`**, **`inner_pseisS_thetaL_unfold`** and
  **`const_thetaFS_ae`**): `⟨E(ψ)∘S⁻¹, θ⟩ = (9√3/2)·Res φ₀·M_ψ(4/3)` with `Res φ₀ = phiG(4/3)/3` (round 441's
  `tendsto_phi0C_residue`), by the identity theorem and the limit as in round 433. So
  `∫_{3P} θ̃(S·(z, v)) dz = (9√3/2)·Res φ₀·v^{2/3}` for almost every `v > 0`, the expression of θ's constant
  term at `∞` (round 433's `const_thetaF_ae`).
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Conjugation by `S` -/

/-- `g·(γ·p) = (gγg⁻¹)·(g·p)`. -/
theorem slAct_conj (g γ : SL(2, 𝓞 K)) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    slAct g (slAct γ p) = slAct (g * γ * g⁻¹) (slAct g p) := by
  rw [← slAct_mul _ _ hp, ← slAct_mul _ _ hp, inv_mul_cancel_right]

/-- **`κ` is invariant under conjugation by `S`** (round 382's `kub_conj_toSL` at `S⁻¹`). -/
theorem kub_sS_conj {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) : kub ↑(sS * γ * sS⁻¹) = kub ↑γ := by
  have h := kub_conj_toSL ModularGroup.S⁻¹ hγ
  rw [map_inv, inv_inv] at h
  exact h

/-- **`κ` is invariant under conjugation by `S⁻¹`** (round 382's `kub_conj_toSL` at `S`). -/
theorem kub_sS_inv_conj {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) : kub ↑(sS⁻¹ * γ * sS⁻¹⁻¹) = kub ↑γ := by
  rw [inv_inv]
  exact kub_conj_toSL ModularGroup.S hγ

/-- **Composing with `S` keeps automorphy**: `u∘S` is automorphic on `Γ_1(3)` with `κ` when `u` is, since
`Γ_1(3)` is normal and `κ(SγS⁻¹) = κ(γ)`. -/
theorem isAut_comp_sS {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) :
    IsAut Gam3 (fun g => kub ↑g) fun p => u (slAct sS p) := by
  intro γ hγ p hp
  show u (slAct sS (slAct γ p)) = kub ↑γ * u (slAct sS p)
  rw [slAct_conj sS γ hp, hu _ (gam3_normal.conj_mem γ hγ sS) _ (slAct_mem _ hp)]
  dsimp only
  rw [kub_sS_conj hγ]

/-- **Composing with `S⁻¹` keeps automorphy.** -/
theorem isAut_comp_sS_inv {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) :
    IsAut Gam3 (fun g => kub ↑g) fun p => u (slAct sS⁻¹ p) := by
  intro γ hγ p hp
  show u (slAct sS⁻¹ (slAct γ p)) = kub ↑γ * u (slAct sS⁻¹ p)
  rw [slAct_conj sS⁻¹ γ hp, hu _ (gam3_normal.conj_mem γ hγ sS⁻¹) _ (slAct_mem _ hp)]
  dsimp only
  rw [kub_sS_inv_conj hγ]

/-- **`ρ_G∘g` is a partition of unity for `Γ_1(3)`**, for every `g ∈ SL_2(ℤ[ω])`, since `Γ_1(3)` is
normal. -/
theorem isPU_rhoG_comp (g : SL(2, 𝓞 K)) : IsPU Gam3 fun p => rhoG (slAct g p) := by
  refine ⟨isPU_rhoG.1.comp (measurable_slAct g), fun p hp => ?_⟩
  let e : Gam3 ≃ Gam3 :=
    { toFun := fun γ => ⟨g * γ * g⁻¹, gam3_normal.conj_mem _ γ.2 g⟩
      invFun := fun γ => ⟨g⁻¹ * γ * g, by simpa using gam3_normal.conj_mem _ γ.2 g⁻¹⟩
      left_inv := fun γ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun γ => Subtype.ext (by simp [mul_assoc]) }
  rw [← isPU_rhoG.2 _ (slAct_mem g hp)]
  refine (tsum_congr fun γ => ?_).trans (e.tsum_eq fun γ' : Gam3 => rhoG (slAct γ' (slAct g p)))
  show rhoG (slAct g (slAct (γ : SL(2, 𝓞 K)) p)) = rhoG (slAct (g * γ * g⁻¹) (slAct g p))
  rw [slAct_conj g γ hp]

/-- **`∫F(g·p) dν = ∫F dν`** for `F ≥ 0` measurable and invariant under `Γ_1(3)`, and `g ∈ SL_2(ℤ[ω])`
(round 439's `lintegral_muR_slAct`, round 386's `lintegral_isPU_eq`). -/
theorem lintegral_comp_eq (g : SL(2, 𝓞 K)) {F : ℂ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, F (slAct γ p) = F p) :
    ∫⁻ p, F (slAct g p) ∂(muR rhoG) = ∫⁻ p, F p ∂(muR rhoG) := by
  have h1 := lintegral_muR_slAct g⁻¹ isPU_rhoG.1 hF
  rw [inv_inv] at h1
  rw [← h1, muR, muR, lintegral_withDensity_eq_lintegral_mul _ (isPU_rhoG_comp g⁻¹).1 hF,
    lintegral_withDensity_eq_lintegral_mul _ isPU_rhoG.1 hF]
  simp only [Pi.mul_apply]
  exact lintegral_isPU_eq (isPU_rhoG_comp g⁻¹) isPU_rhoG hF hinv

/-- **Composing with `g` keeps `L²(ν)`**, for `u` with `|u|` invariant under `Γ_1(3)`. -/
theorem memLp_comp (g : SL(2, 𝓞 K)) {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (hinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖u (slAct γ p)‖ₑ = ‖u p‖ₑ) (hu2 : MemLp u 2 (muR rhoG)) :
    MemLp (fun p => u (slAct g p)) 2 (muR rhoG) := by
  have hm : Measurable fun p => u (slAct g p) := hum.comp (measurable_slAct g)
  refine memLp_two_of_lintegral hm ?_
  have hfin : ∫⁻ q, ‖u q‖ₑ ^ 2 ∂(muR rhoG) < ⊤ := by
    have h := hu2.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hu2.aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h
  have key : ∫⁻ p, ‖u (slAct g p)‖ₑ ^ 2 ∂(muR rhoG) = ∫⁻ p, ‖u p‖ₑ ^ 2 ∂(muR rhoG) :=
    lintegral_comp_eq g (F := fun q => ‖u q‖ₑ ^ 2) (hum.enorm.pow_const 2)
      fun γ hγ p hp => by
        show ‖u (slAct γ p)‖ₑ ^ 2 = ‖u p‖ₑ ^ 2
        rw [hinv γ hγ p hp]
  rw [key]
  exact hfin

/-- **`∫|u(g·p)| dν < ∞`** for `u` in `L²(ν)` with `|u|` invariant under `Γ_1(3)` (round 432's
`isFiniteMeasure_muR_rhoG`). -/
theorem lintegral_enorm_comp_lt_top (g : SL(2, 𝓞 K)) {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (hinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, ‖u (slAct γ p)‖ₑ = ‖u p‖ₑ) (hu2 : MemLp u 2 (muR rhoG)) :
    ∫⁻ p, ‖u (slAct g p)‖ₑ ∂(muR rhoG) < ⊤ := by
  rw [lintegral_comp_eq g hum.enorm hinv]
  exact (hu2.integrable one_le_two).2

/-- **Moving `S` across**: for `u` and `w` measurable and automorphic on `Γ_1(3)` with `κ`, and
`∫|u(S⁻¹·p)·w(p)| dν < ∞`, `∫conj u(S⁻¹·p)·w(p) dν = ∫conj u(p)·w(S·p) dν` (round 439's
`integral_muR_slAct` and `integral_isPU_eq`). -/
theorem integral_conj_sS_inv_mul {u w : ℂ × ℝ → ℂ} (hum : Measurable u) (hwm : Measurable w)
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hw : IsAut Gam3 (fun g => kub ↑g) w)
    (hint : ∫⁻ p, ‖conj (u (slAct sS⁻¹ p)) * w p‖ₑ ∂(muR rhoG) < ⊤) :
    ∫ p, conj (u (slAct sS⁻¹ p)) * w p ∂(muR rhoG) =
      ∫ p, conj (u p) * w (slAct sS p) ∂(muR rhoG) := by
  set G : ℂ × ℝ → ℂ := fun p => conj (u p) * w (slAct sS p) with hG
  have hGm : Measurable G :=
    (Complex.continuous_conj.measurable.comp hum).mul (hwm.comp (measurable_slAct _))
  have hback : ∀ p ∈ UHS, G (slAct sS⁻¹ p) = conj (u (slAct sS⁻¹ p)) * w p := fun p hp => by
    simp only [hG]
    rw [slAct_slAct_inv sS hp]
  have h1 : ∫ p, G p ∂(muR fun p => rhoG (slAct sS p)) =
      ∫ p, conj (u (slAct sS⁻¹ p)) * w p ∂(muR rhoG) := by
    rw [integral_muR_slAct sS isPU_rhoG.1 (fun p hp => rhoG_lt_top hp) hGm]
    refine integral_congr_ae ?_
    filter_upwards [ae_muR_UHS rhoG] with p hp
    exact hback p hp
  have hinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, G (slAct γ p) = G p := by
    intro γ hγ p hp
    simp only [hG]
    rw [hu γ hγ p hp, slAct_conj sS γ hp, hw _ (gam3_normal.conj_mem γ hγ sS) _ (slAct_mem _ hp)]
    dsimp only
    rw [kub_sS_conj hγ, map_mul]
    linear_combination (conj (u p) * w (slAct sS p)) * kub_mul_conj_kub hγ
  have hint' : ∫⁻ p, ‖G p‖ₑ ∂(muR fun p => rhoG (slAct sS p)) < ⊤ := by
    rw [lintegral_muR_slAct sS isPU_rhoG.1 hGm.enorm]
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hint
    filter_upwards [ae_muR_UHS rhoG] with p hp
    rw [hback p hp]
  rw [← h1, integral_isPU_eq (isPU_rhoG_comp sS) isPU_rhoG hGm hinv hint']

/-! ### θ at the cusp `0` -/

/-- `θ̃∘S`: θ's representative (round 425's `thetaF`) at `S·p`. -/
def thetaFS (r Y : ℝ) (hY : 0 < Y) (p : ℂ × ℝ) : ℂ := thetaF r Y hY (slAct sS p)

theorem isAut_thetaFS (r Y : ℝ) (hY : 0 < Y) : IsAut Gam3 (fun g => kub ↑g) (thetaFS r Y hY) :=
  isAut_comp_sS (isAut_thetaF r Y hY)

theorem measurable_thetaFS (r Y : ℝ) (hY : 0 < Y) : Measurable (thetaFS r Y hY) :=
  (measurable_thetaF r Y hY).comp (measurable_slAct _)

theorem memLp_thetaFS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    MemLp (thetaFS r Y hY) 2 (muR rhoG) :=
  memLp_comp sS (measurable_thetaF r Y hY) (enorm_thetaF_slAct r Y hY) (memLp_thetaF hr hY)

/-- **An automorphic function in `L²(ν)`, moved by `S`, is integrable on `3P × [α, β]`** against `dz dv/v³`
(round 432's `lintegral_boxZ_lt_top`). -/
theorem setLIntegral_sS_lt_top {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hu2 : MemLp u 2 (muR rhoG)) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∫⁻ p in fundP3 ×ˢ Icc α β, ‖u (slAct sS p)‖ₑ ∂uhsMeasure < ⊤ := by
  have hm : Measurable fun p => u (slAct sS p) := hum.comp (measurable_slAct _)
  refine (lintegral_mono_set (fun p hp => (⟨norm_le_six_of_mem_fundP3 hp.1, hp.2.1, hp.2.2⟩ :
    p ∈ boxZ 6 α β))).trans_lt ?_
  exact lintegral_boxZ_lt_top hm (enorm_slAct_of_isAut (isAut_comp_sS hu))
    (lintegral_enorm_comp_lt_top sS hum (enorm_slAct_of_isAut hu) hu2) 6 hα β

/-- **The same, against `dz dv`.** -/
theorem integrableOn_sS {u : ℂ × ℝ → ℂ} (hum : Measurable u) (hu : IsAut Gam3 (fun g => kub ↑g) u)
    (hu2 : MemLp u 2 (muR rhoG)) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    IntegrableOn (fun p => u (slAct sS p)) (fundP3 ×ˢ Icc α β) := by
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hm : Measurable fun p => u (slAct sS p) := hum.comp (measurable_slAct _)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖u (slAct sS p)‖ₑ < ⊤
  exact (setLIntegral_volume_le hm.enorm hT hα (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (setLIntegral_sS_lt_top hum hu hu2 hα β))

/-! ### The band at `S·p` -/

/-- **Every height at `S·p` is at most `1/v`**: the term of `(c, d)` there is that of the row `(d, −c)`, and
`d ≠ 0`. -/
theorem height_sS_le {cd : 𝓞 K × 𝓞 K} (hb : BRow cd) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    (slAct sS p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct sS p).1 (slAct sS p).2 ≤ 1 / p.2 := by
  obtain ⟨c, d⟩ := cd
  rw [height_rowMul sS hb hp, rowMul_sS]
  exact height_le_inv (primary_ne_zero hb.2.2) _ p.1 hp

/-- **`h_s` at `S·p` is a band series**: `h_s(S·p) = E(1[Y ≤ v ≤ Y + β + 1/α]v^s)(S·p)` for `α ≤ v` and
`α ≤ β`. -/
theorem eisHigh_sS_eq_band (s : ℂ) {Y α β : ℝ} (hY : 0 < Y) (hα : 0 < α) (hαβ : α ≤ β) {p : ℂ × ℝ}
    (hαv : α ≤ p.2) :
    eisHigh s Y (slAct sS p) = pseis (bandF s Y (Y + β + 1 / α)) (slAct sS p) := by
  have hp : p ∈ UHS := show 0 < p.2 from lt_of_lt_of_le hα hαv
  unfold eisHigh pseis
  refine tsum_congr fun cd => ?_
  unfold psTerm
  split_ifs with hb
  · congr 1
    have hH : (slAct sS p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct sS p).1 (slAct sS p).2 ≤
        Y + β + 1 / α := by
      have h1 := height_sS_le hb hp
      have h2 : 1 / p.2 ≤ 1 / α := one_div_le_one_div_of_le hα hαv
      linarith
    unfold highF bandF
    by_cases hlt : (slAct sS p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct sS p).1 (slAct sS p).2 < Y
    · have hn : ¬ (Y ≤ (slAct sS p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct sS p).1 (slAct sS p).2 ∧
          (slAct sS p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct sS p).1 (slAct sS p).2 ≤ Y + β + 1 / α) :=
        fun h => not_le.2 hlt h.1
      simp only [hlt, hn, ↓reduceIte]
    · have hy : Y ≤ (slAct sS p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct sS p).1 (slAct sS p).2 ∧
          (slAct sS p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct sS p).1 (slAct sS p).2 ≤ Y + β + 1 / α :=
        ⟨not_lt.1 hlt, hH⟩
      simp only [hlt, hy, and_self, ↓reduceIte]
  · rfl

/-- **`E_s − h_s = E_s − E(1[Y ≤ v ≤ H]v^s)` at `S·p`**, `H = Y + β + 1/α`, for `Re s > 2`, `α ≤ v` and
`α ≤ β`. -/
theorem eisLow_sS_eq_band {s : ℂ} (hs : 2 < s.re) {Y α β : ℝ} (hY : 0 < Y) (hα : 0 < α) (hαβ : α ≤ β)
    {p : ℂ × ℝ} (hαv : α ≤ p.2) :
    eisLow s Y (slAct sS p) = eis1 s (slAct sS p) - pseis (bandF s Y (Y + β + 1 / α)) (slAct sS p) := by
  have hp : p ∈ UHS := show 0 < p.2 from lt_of_lt_of_le hα hαv
  rw [eis1_eq_eisLow_add_eisHigh hs Y (slAct_mem sS hp), eisHigh_sS_eq_band s hY hα hαβ hαv]
  ring

/-! ### The pseudo-Eisenstein series at the cusp `0` -/

/-- **`E(ψ)∘S⁻¹`, the pseudo-Eisenstein series of `ψ` at the cusp `0`.** -/
def pseisS (ψ : ℝ → ℂ) (p : ℂ × ℝ) : ℂ := pseis ψ (slAct sS⁻¹ p)

theorem isAut_pseisS (ψ : ℝ → ℂ) : IsAut Gam3 (fun g => kub ↑g) (pseisS ψ) :=
  isAut_comp_sS_inv (isAut_pseis ψ)

theorem memLp_pseisS {ψ : ℝ → ℂ} (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) :
    MemLp (pseisS ψ) 2 (muR rhoG) :=
  memLp_comp sS⁻¹ (measurable_pseis hψ) (enorm_slAct_of_isAut (isAut_pseis ψ)) hψ2

/-- `∫_{3P×(0,∞)} |ψ(v)G(z, v)| dz dv/v³ < ∞` makes `conj ψ(v)·G` integrable on `3P × (0, ∞)`. -/
theorem integrableOn_fundP3_of_lintegral {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) {G : ℂ × ℝ → ℂ} (hG : Measurable G)
    (hfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖G p‖ₑ ∂uhsMeasure < ⊤) :
    IntegrableOn (fun p => conj (ψ p.2) * G p) (Prod.fst ⁻¹' fundP3) uhsMeasure := by
  have hm : Measurable fun p : ℂ × ℝ => conj (ψ p.2) * G p :=
    (Complex.continuous_conj.measurable.comp (hψ.comp measurable_snd)).mul hG
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖conj (ψ p.2) * G p‖ₑ ∂(uhsMeasure.restrict (Prod.fst ⁻¹' fundP3)) < ⊤
  rw [← muR_rhoT3, muR, lintegral_withDensity_eq_lintegral_mul _ measurable_rhoT3 hm.enorm]
  exact (lintegral_rhoT3_ps_ne_top hM hψ0 hG hfin).lt_top

/-- **The pairing with the series at `0`, unfolded**: for `w` measurable, automorphic and in `L²(ν)`, with
`∫_{3P×(0,∞)} |ψ(v)w(S·(z, v))| dz dv/v³ < ∞`,
`⟨E(ψ)∘S⁻¹, w⟩ = ∫_{3P×(0,∞)} conj ψ(v)·w(S·(z, v)) dz dv/v³` (round 426's `integral_conj_pseis_mul`). -/
theorem inner_toLp_pseisS {ψ : ℝ → ℂ} (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG))
    {w : ℂ × ℝ → ℂ} (hw : IsAut Gam3 (fun g => kub ↑g) w) (hwm : Measurable w)
    (hw2 : MemLp w 2 (muR rhoG))
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2) * w (slAct sS p)‖ₑ ∂uhsMeasure ≠ ⊤) :
    inner ℂ ((memLp_pseisS hψ hψ2).toLp (pseisS ψ)) (hw2.toLp w) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * w (slAct sS p) ∂uhsMeasure := by
  have hS2 := memLp_pseisS hψ hψ2
  have hpm : Measurable (pseis ψ) := measurable_pseis hψ
  have hint : ∫⁻ p, ‖conj (pseis ψ (slAct sS⁻¹ p)) * w p‖ₑ ∂(muR rhoG) < ⊤ := by
    have h1 : MemLp (fun p => conj (pseisS ψ p)) 2 (muR rhoG) :=
      hS2.of_le ((Complex.continuous_conj.measurable.comp
        (hpm.comp (measurable_slAct _))).aestronglyMeasurable)
        (Eventually.of_forall fun p => by rw [Complex.norm_conj])
    exact (h1.integrable_mul hw2).2
  rw [L2.inner_def, ← integral_conj_pseis_mul hψ (isAut_comp_sS hw) (hwm.comp (measurable_slAct _)) hfin,
    ← integral_conj_sS_inv_mul hpm hwm (isAut_pseis ψ) hw hint]
  refine integral_congr_ae ?_
  filter_upwards [hS2.coeFn_toLp, hw2.coeFn_toLp] with p h1 h2
  rw [RCLike.inner_apply', h1, h2]
  rfl

/-- **The pairing of `E(ψ)∘S⁻¹` with `ũ_s` for `Re s > 2`**: for `R ≥ 0`, `Y > 0`, `ψ` measurable and
bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, and `Im ĥ(s) ≠ 0`,
`⟨E(ψ)∘S⁻¹, ũ_s⟩ = (9√3/2)·φ₀(s)M_ψ(s) − ⟨E(ψ)∘S⁻¹, E(1[Y ≤ v ≤ H]v^s)⟩` with `H = Y + β + 1/α`, from round
440's constant term at the cusp `0`. -/
theorem inner_pseisS_uL_band {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ} (hs : 2 < s.re)
    (him : (hhat R s).im ≠ 0) :
    inner ℂ ((memLp_pseisS hψ hψ2).toLp (pseisS ψ)) (uL R hR Y hY s) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * eisPhi0 s * mellinPsi ψ s -
        inner ℂ ((memLp_pseisS hψ hψ2).toLp (pseisS ψ)) (bandL hY (le_band hα hαβ) s) := by
  set H := Y + β + 1 / α
  have hT : MeasurableSet (fundP3 ×ˢ Icc α β) := measurableSet_fundP3.prod measurableSet_Icc
  have hLm : Measurable (eisLow s Y) := measurable_eisLow s Y
  have hBm : Measurable (pseis (bandF s Y H)) := measurable_pseis (measurable_bandF s Y H)
  have hEm : Measurable (eis1 s) := by
    rw [eis1_eq_pseis]
    exact measurable_pseis (Complex.measurable_ofReal.pow_const s)
  have hL2 := memLp_eisLow hs hY.le
  have hB2 := memLp_pseis_bandF s hY (le_band hα hαβ)
  have hLfin := setLIntegral_sS_lt_top hLm (isAut_eisLow s Y) hL2 hα β
  have hBfin := setLIntegral_sS_lt_top hBm (isAut_pseis _) hB2 hα β
  have hLSm : Measurable fun p => eisLow s Y (slAct sS p) := hLm.comp (measurable_slAct _)
  have hBSm : Measurable fun p => pseis (bandF s Y H) (slAct sS p) := hBm.comp (measurable_slAct _)
  have hESm : Measurable fun p => eis1 s (slAct sS p) := hEm.comp (measurable_slAct _)
  -- `E_s∘S` on `3P × [α, β]`
  have hEfin : ∫⁻ p in fundP3 ×ˢ Icc α β, ‖eis1 s (slAct sS p)‖ₑ ∂uhsMeasure < ⊤ := by
    calc ∫⁻ p in fundP3 ×ˢ Icc α β, ‖eis1 s (slAct sS p)‖ₑ ∂uhsMeasure
        ≤ ∫⁻ p in fundP3 ×ˢ Icc α β, (‖eisLow s Y (slAct sS p)‖ₑ +
            ‖pseis (bandF s Y H) (slAct sS p)‖ₑ) ∂uhsMeasure := by
          refine setLIntegral_mono (hLSm.enorm.add hBSm.enorm) fun p hp => ?_
          rw [show eis1 s (slAct sS p) = eisLow s Y (slAct sS p) + pseis (bandF s Y H) (slAct sS p) by
            rw [eisLow_sS_eq_band hs hY hα hαβ hp.2.1]; ring]
          exact enorm_add_le _ _
      _ = (∫⁻ p in fundP3 ×ˢ Icc α β, ‖eisLow s Y (slAct sS p)‖ₑ ∂uhsMeasure) +
            ∫⁻ p in fundP3 ×ˢ Icc α β, ‖pseis (bandF s Y H) (slAct sS p)‖ₑ ∂uhsMeasure :=
          lintegral_add_left hLSm.enorm _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hLfin, hBfin⟩
  have hEint : IntegrableOn (fun p => eis1 s (slAct sS p)) (fundP3 ×ˢ Icc α β) := by
    refine ⟨hESm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p in fundP3 ×ˢ Icc α β, ‖eis1 s (slAct sS p)‖ₑ < ⊤
    exact (setLIntegral_volume_le hESm.enorm hT hα (fun p hp => ⟨hp.2.1, hp.2.2⟩)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin)
  rw [uL_eq_eisLow hR hY hs him,
    inner_toLp_pseisS hψ hψ2 (isAut_eisLow s Y) hLm hL2 (lintegral_rhoT3_ps_ne_top hM hψ0 hLSm hLfin),
    bandL, inner_toLp_pseisS hψ hψ2 (isAut_pseis _) hBm hB2 (lintegral_rhoT3_ps_ne_top hM hψ0 hBSm hBfin)]
  have h1 : ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2) * eisLow s Y (slAct sS p) ∂uhsMeasure =
      ∫ p in Prod.fst ⁻¹' fundP3, (conj (ψ p.2) * eis1 s (slAct sS p) -
        conj (ψ p.2) * pseis (bandF s Y H) (slAct sS p)) ∂uhsMeasure := by
    refine setIntegral_congr_fun (measurableSet_fundP3.preimage measurable_fst) fun p _ => ?_
    by_cases hv : p.2 ∈ Icc α β
    · rw [eisLow_sS_eq_band hs hY hα hαβ hv.1]
      ring
    · simp [hψ0 _ hv]
  rw [h1, integral_sub (integrableOn_fundP3_of_lintegral hψ hM hψ0 hESm hEfin)
      (integrableOn_fundP3_of_lintegral hψ hM hψ0 hBSm hBfin),
    integral_fundP3_conj_mul_of_int hψ hM hψ0 hα hESm hEint]
  congr 1
  have hc9 : ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    exact_mod_cast this.ne'
  have e : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, eis1 s (slAct sS (z, v)) =
      ∫ v in Ioi 0, ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * eisPhi0 s *
        (conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    have hc := constTerm_eis1_sS hs hv'
    have hI : ∫ z in fundP3, eis1 s (slAct sS (z, v)) =
        ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (eisPhi0 s * ((v : ℝ) : ℂ) ^ (2 - s)) := by
      rw [← hc, ← mul_assoc, mul_inv_cancel₀ hc9, one_mul]
    rw [hI, ← cpow_neg_one_sub hv' s]
    ring
  rw [e, integral_const_mul]
  rfl

/-! ### θ at the cusp `0` -/

/-- **The pairing of θ with `E(ψ)∘S⁻¹`**: for `r > 0`, `Y > 0`, and `ψ` measurable and bounded, vanishing
outside `[α, β]` with `0 < α ≤ β`, `⟨E(ψ)∘S⁻¹, θ⟩ = (9√3/2)·Res φ₀·M_ψ(4/3)` with round 441's
`Res φ₀ = phiG(4/3)/3`, by the identity theorem and the limit as in round 433. -/
theorem inner_pseisS_thetaL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) :
    inner ℂ ((memLp_pseisS hψ hψ2).toLp (pseisS ψ)) (thetaL r Y hY) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * mellinPsi ψ (4 / 3) := by
  set R := 2 * Real.cosh r - 2 with hRdef
  set y := (memLp_pseisS hψ hψ2).toLp (pseisS ψ) with hy
  set c9 : ℂ := ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) with hc9
  have hMd := differentiable_mellinPsi hψ hM hψ0 hα
  set F : ℂ → ℂ := fun s => inner ℂ y (uL R (cosh_sub_nonneg r) Y hY s) +
    inner ℂ y (bandL hY (le_band hα hαβ) s) with hF
  set G : ℂ → ℂ := fun s => c9 * phi0C s * mellinPsi ψ s with hG
  have him : ∀ s ∈ domU r, (hhat R s).im ≠ 0 := fun s hs =>
    (im_hhat_pos hr hs.1 hs.2.1 ((lt_div_iff₀ hr).1 hs.2.2)).ne'
  have hFd : DifferentiableOn ℂ F (domU r) := fun s hs => by
    have h1 := differentiableAt_inner_uL hr.le hY y (him s hs)
    have h2 := differentiable_inner_bandL y hY (le_band hα hαβ) s
    exact (h1.add h2).differentiableWithinAt
  have hGd : DifferentiableOn ℂ G (domU r) := fun s hs => by
    have h43 : s ≠ 4 / 3 := fun h => by
      have h2 := hs.2.1
      rw [h] at h2
      norm_num at h2
    exact (((differentiableAt_phi0C hs.1 h43).const_mul c9).mul (hMd s)).differentiableWithinAt
  -- agreement where `Re s > 2`
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Real.pi / (2 * r) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxr : x < Real.pi / r := by
    rw [hxdef, div_lt_div_iff₀ (by positivity) hr]
    nlinarith [Real.pi_pos]
  set z0 : ℂ := 3 + I * (x : ℂ) with hz0def
  have hz0re : z0.re = 3 := by simp [z0]
  have hz0im : z0.im = x := by simp [z0]
  have hz0 : z0 ∈ domU r := by
    refine ⟨?_, ?_, ?_⟩
    · show 1 < z0.re
      rw [hz0re]
      norm_num
    · show 0 < z0.im
      rw [hz0im]
      exact hx0
    · show z0.im < Real.pi / r
      rw [hz0im]
      exact hxr
  have hfg : F =ᶠ[𝓝 z0] G := by
    have hO : IsOpen (domU r ∩ {s | 2 < s.re}) :=
      (isOpen_domU r).inter (isOpen_lt continuous_const continuous_re)
    have hmem : z0 ∈ domU r ∩ {s | 2 < s.re} := ⟨hz0, by show 2 < z0.re; rw [hz0re]; norm_num⟩
    filter_upwards [hO.mem_nhds hmem] with s hs
    simp only [hF, hG]
    rw [inner_pseisS_uL_band (cosh_sub_nonneg r) hY hψ hψ2 hM hψ0 hα hαβ hs.2 (him s hs.1),
      eisPhi0_eq_phi0C hs.2]
    ring
  have heq : EqOn F G (domU r) :=
    (hFd.analyticOnNhd (isOpen_domU r)).eqOn_of_preconnected_of_eventuallyEq
      (hGd.analyticOnNhd (isOpen_domU r)) (convex_domU r).isPreconnected hz0 hfg
  -- the curve `s = 4/3 + iε`
  set γ : ℝ → ℂ := fun ε => ((4 / 3 : ℝ) : ℂ) + I * ε with hγdef
  have hγU : ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ ε ∈ domU r := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos Real.pi_pos hr)] with ε hε
    refine ⟨?_, ?_, ?_⟩
    · show 1 < (γ ε).re
      simp [γ]
      norm_num
    · show 0 < (γ ε).im
      simp [γ, hε.1]
    · show (γ ε).im < Real.pi / r
      simp [γ, hε.2]
  have hγc : Tendsto γ (𝓝[>] 0) (𝓝 ((4 / 3 : ℝ) : ℂ)) := by
    have hcont : Continuous γ := by fun_prop
    have := hcont.tendsto 0
    have h0 : γ 0 = ((4 / 3 : ℝ) : ℂ) := by simp [γ]
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hI : Tendsto (fun ε : ℝ => I * (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun ε : ℝ => I * (ε : ℂ) := by fun_prop
    have := hcont.tendsto 0
    simp only [ofReal_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL0 : Tendsto (fun ε : ℝ => (I * ε) *
      inner ℂ y (uL R (cosh_sub_nonneg r) Y hY (γ ε))) (𝓝[>] 0) (𝓝 (inner ℂ y (thetaL r Y hY))) := by
    have h := ((innerSL ℂ y).continuous.tendsto _).comp (tendsto_uL_thetaL hr hY)
    refine h.congr fun ε => ?_
    simp only [Function.comp, hγdef, innerSL_apply_apply, inner_smul_right]
    rfl
  have hB : Tendsto (fun ε : ℝ => inner ℂ y (bandL hY (le_band hα hαβ) (γ ε))) (𝓝[>] 0)
      (𝓝 (inner ℂ y (bandL hY (le_band hα hαβ) ((4 / 3 : ℝ) : ℂ)))) :=
    (differentiable_inner_bandL y hY (le_band hα hαβ) _).continuousAt.tendsto.comp hγc
  have hL : Tendsto (fun ε : ℝ => (I * ε) * F (γ ε)) (𝓝[>] 0) (𝓝 (inner ℂ y (thetaL r Y hY))) := by
    have h := hL0.add (hI.mul hB)
    rw [zero_mul, add_zero] at h
    refine h.congr fun ε => ?_
    simp only [hF]
    ring
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝[≠] (4 / 3 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have e : ((4 / 3 : ℝ) : ℂ) = 4 / 3 := by push_cast; ring
      rw [← e]
      exact hγc
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro h
      have := congrArg Complex.im h
      simp [γ] at this
      exact (ne_of_gt (show (0 : ℝ) < ε from hε)) this
  have hRt : Tendsto (fun ε : ℝ => (I * ε) * G (γ ε)) (𝓝[>] 0)
      (𝓝 (c9 * (phiG (4 / 3) / 3) * mellinPsi ψ (4 / 3))) := by
    have h1' := tendsto_phi0C_residue.comp hγ
    have h2 : Tendsto (fun ε => mellinPsi ψ (γ ε)) (𝓝[>] 0) (𝓝 (mellinPsi ψ (4 / 3))) :=
      (hMd (4 / 3)).continuousAt.tendsto.comp (hγ.mono_right nhdsWithin_le_nhds)
    have h3 := (h1'.const_mul c9).mul h2
    refine h3.congr fun ε => ?_
    simp only [Function.comp, hG]
    have e : γ ε - 4 / 3 = I * ε := by
      simp only [γ]
      push_cast
      ring
    rw [e]
    ring
  have hEq : (fun ε : ℝ => (I * ε) * F (γ ε)) =ᶠ[𝓝[>] (0 : ℝ)] fun ε => (I * ε) * G (γ ε) := by
    filter_upwards [hγU] with ε hε
    rw [heq hε]
  exact tendsto_nhds_unique (hL.congr' hEq) hRt

/-- **The pairing of θ with `E(ψ)∘S⁻¹`, unfolded**: for `ψ` measurable and bounded, vanishing outside
`[α, β]` with `α > 0`, `⟨E(ψ)∘S⁻¹, θ⟩ = ∫_0^∞ v^{−3}·conj ψ(v)·∫_{3P} θ̃(S·(z, v)) dz dv`. -/
theorem inner_pseisS_thetaL_unfold {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψ2 : MemLp (pseis ψ) 2 (muR rhoG)) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M)
    (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) :
    inner ℂ ((memLp_pseisS hψ hψ2).toLp (pseisS ψ)) (thetaL r Y hY) =
      ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * ∫ z in fundP3, thetaFS r Y hY (z, v) := by
  have hθ : thetaL r Y hY = (memLp_thetaF hr hY).toLp (thetaF r Y hY) :=
    Lp.ext ((thetaL_ae_eq_thetaF hr hY).trans (memLp_thetaF hr hY).coeFn_toLp.symm)
  have hθm := measurable_thetaF r Y hY
  have hθSm : Measurable fun p => thetaF r Y hY (slAct sS p) := hθm.comp (measurable_slAct sS)
  have hfin := lintegral_rhoT3_ps_ne_top hM hψ0 hθSm
    (setLIntegral_sS_lt_top hθm (isAut_thetaF r Y hY) (memLp_thetaF hr hY) hα β)
  rw [hθ, inner_toLp_pseisS hψ hψ2 (isAut_thetaF r Y hY) hθm (memLp_thetaF hr hY) hfin,
    integral_fundP3_conj_mul_of_int hψ hM hψ0 hα hθSm
      (integrableOn_sS hθm (isAut_thetaF r Y hY) (memLp_thetaF hr hY) hα β)]
  rfl

/-- **θ's constant term at the cusp `0`**: for `r > 0` and `Y > 0`,
`∫_{3P} θ̃(S·(z, v)) dz = (9√3/2)·Res φ₀·v^{2/3}` for almost every `v > 0`, with round 441's
`Res φ₀ = phiG(4/3)/3`, the residue of `φ` (round 417). -/
theorem const_thetaFS_ae {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∫ z in fundP3, thetaFS r Y hY (z, v) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
  set C : ℂ := ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) with hC
  set a : ℝ → ℂ := fun v => ∫ z in fundP3, thetaFS r Y hY (z, v) with ha
  have hθm := measurable_thetaF r Y hY
  have hcont : ContinuousOn (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)) (Ioi 0) := fun v hv =>
    (continuousAt_ofReal_cpow_const v _ (Or.inr (show (0 : ℝ) < v from hv).ne')).continuousWithinAt
  have key := ae_eq_of_setIntegral_Icc (f := fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v)
    (g := fun v => C * ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)) ?_ ?_ ?_
  · filter_upwards [key, ae_restrict_mem measurableSet_Ioi] with v hv hv0
    have hv0' : (0 : ℝ) < v := hv0
    have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv0'.ne'
    have e3 : ((v ^ (-3 : ℤ) : ℝ) : ℂ) = ((v : ℂ) ^ 3)⁻¹ := by
      rw [Complex.ofReal_zpow, zpow_neg]
      norm_cast
    have e7 : ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) = (((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) * ((v : ℂ) ^ 3)⁻¹ := by
      rw [show (-1 - 4 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) - 3 by push_cast; ring,
        Complex.cpow_sub _ _ hvc, ← Complex.ofReal_cpow hv0'.le, div_eq_mul_inv]
      norm_cast
    rw [e3, e7] at hv
    have h3 : (v : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 hvc
    calc a v = (v : ℂ) ^ 3 * (((v : ℂ) ^ 3)⁻¹ * a v) := by field_simp
      _ = (v : ℂ) ^ 3 * (C * (((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ((v : ℂ) ^ 3)⁻¹)) := by rw [hv]
      _ = C * (((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) := by field_simp
  · intro n
    have hα : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hai : IntegrableOn a (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
      integrableOn_slice (integrableOn_sS hθm (isAut_thetaF r Y hY) (memLp_thetaF hr hY) hα _)
    refine (hai.norm.const_mul ((1 / ((n : ℝ) + 1)) ^ (-3 : ℤ))).mono' ?_ ?_
    · have hc : Measurable fun v : ℝ => ((v ^ (-3 : ℤ) : ℝ) : ℂ) := by fun_prop
      exact hc.aestronglyMeasurable.mul hai.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall fun v hv => ?_
      have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_right (zpow_neg_three_le hα hv.1) (norm_nonneg _)
  · intro n
    have hα : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsub : Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hα hv.1
    exact ((hcont.mono hsub).integrableOn_compact isCompact_Icc).const_mul C
  · intro n S hS hSI
    have hα : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hαβ : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have h1n : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        linarith
      exact ((div_le_one (by positivity)).2 h1n).trans h1n
    have hSsub : S ⊆ Ioi 0 := fun v hv => lt_of_lt_of_le hα (hSI hv).1
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℂ, ψ = S.indicator fun _ => 1 := ⟨_, rfl⟩
    have hψm : Measurable ψ := by rw [hψdef]; exact measurable_const.indicator hS
    have hψM : ∀ v, ‖ψ v‖ ≤ 1 := fun v => by
      by_cases h : v ∈ S
      · rw [hψdef, indicator_of_mem h, norm_one]
      · rw [hψdef, indicator_of_notMem h, norm_zero]
        norm_num
    have hψ0 : ∀ v, v ∉ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) → ψ v = 0 := fun v hv => by
      rw [hψdef, indicator_of_notMem fun h => hv (hSI h)]
    have hψ2 : MemLp (pseis ψ) 2 (muR rhoG) := memLp_pseis_Icc hψm hψM hψ0 hα
    have h1 := inner_pseisS_thetaL_unfold hr hY hψm hψ2 hψM hψ0 hα
    have h2 := inner_pseisS_thetaL hr hY hψm hψ2 hψM hψ0 hα hαβ
    rw [h1] at h2
    unfold mellinPsi at h2
    have e1 : ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * a v =
        ∫ v in S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := by
      calc ∫ v in Ioi 0, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * conj (ψ v) * a v
          = ∫ v in Ioi 0, S.indicator (fun v => ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v) v := by
            refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
            by_cases h : v ∈ S
            · rw [hψdef, indicator_of_mem h, indicator_of_mem h, map_one, mul_one]
            · rw [hψdef, indicator_of_notMem h, indicator_of_notMem h, map_zero, mul_zero, zero_mul]
        _ = ∫ v in Ioi 0 ∩ S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := setIntegral_indicator hS
        _ = ∫ v in S, ((v ^ (-3 : ℤ) : ℝ) : ℂ) * a v := by rw [inter_eq_right.2 hSsub]
    have e2 : ∫ v in Ioi 0, conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) =
        ∫ v in S, ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) := by
      calc ∫ v in Ioi 0, conj (ψ v) * ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)
          = ∫ v in Ioi 0, S.indicator (fun v => ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ)) v := by
            refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
            by_cases h : v ∈ S
            · rw [hψdef, indicator_of_mem h, indicator_of_mem h, map_one, one_mul]
            · rw [hψdef, indicator_of_notMem h, indicator_of_notMem h, map_zero, zero_mul]
        _ = ∫ v in Ioi 0 ∩ S, ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) := setIntegral_indicator hS
        _ = ∫ v in S, ((v : ℝ) : ℂ) ^ (-1 - 4 / 3 : ℂ) := by rw [inter_eq_right.2 hSsub]
    rw [e1, e2] at h2
    rw [h2, integral_const_mul]

end Eis

end

#print axioms Eis.slAct_conj
#print axioms Eis.kub_sS_conj
#print axioms Eis.kub_sS_inv_conj
#print axioms Eis.isAut_comp_sS
#print axioms Eis.isAut_comp_sS_inv
#print axioms Eis.isPU_rhoG_comp
#print axioms Eis.lintegral_comp_eq
#print axioms Eis.memLp_comp
#print axioms Eis.lintegral_enorm_comp_lt_top
#print axioms Eis.integral_conj_sS_inv_mul
#print axioms Eis.isAut_thetaFS
#print axioms Eis.measurable_thetaFS
#print axioms Eis.memLp_thetaFS
#print axioms Eis.setLIntegral_sS_lt_top
#print axioms Eis.integrableOn_sS
#print axioms Eis.height_sS_le
#print axioms Eis.eisHigh_sS_eq_band
#print axioms Eis.eisLow_sS_eq_band
#print axioms Eis.isAut_pseisS
#print axioms Eis.memLp_pseisS
#print axioms Eis.integrableOn_fundP3_of_lintegral
#print axioms Eis.inner_toLp_pseisS
#print axioms Eis.inner_pseisS_uL_band
#print axioms Eis.inner_pseisS_thetaL
#print axioms Eis.inner_pseisS_thetaL_unfold
#print axioms Eis.const_thetaFS_ae
