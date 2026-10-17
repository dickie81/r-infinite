import KubotaCuspTrans

/-! # The Poincaré series at the cusps `γ_±` (round 461)

S5f-15 of round 360's plan, part 2. Round 460's next step planned the Poincaré series at the cusp `γ_t`, for
the frequencies `m` in the class of round 460's `exists_cuspClass`, and its unfolding. This round proves them,
with `γ_{(c, d)}` round 426's element of `Γ_1(3)` with bottom row `(c, d)` and `ν = ρ_G dμ`:

* **The series with the character `κ_t`** (`CuspClass`, `pmTermT` and `pmSerT`, definitions;
  `kubT_mul_conj`, `pmTermT_slAct`, **`isAut_pmSerT`**, `measurable_pmTermT`,
  `measurable_pmSerT` and `norm_pmTermT`): for `m` with `ĕ(m·3x/9) = χ_t(x)` for every `x`,
  `P^{(t)}_m(ψ)(w) = Σ_{(c, d)} conj κ_t(γ_{(c, d)})·ψ(v(γ_{(c, d)}w))·ĕ(m·z(γ_{(c, d)}w)/9)` is automorphic
  with `κ_t`.
* **The series at the cusp** (`pmSerC`, a definition; `kubT_conj_inv`, **`isAut_pmSerC`**,
  `measurable_pmSerC`, `tsum_enorm_pmTermT_eq`, **`memLp_pmSerC`** and `memLp_pmSerC_Icc`):
  `Q_t = P^{(t)}_m(ψ)∘γ_t⁻¹` is automorphic with Kubota's character, and it is in `L²(ν)` under round 429's
  conditions on `ψ`, since its terms have the absolute values of the terms of `E(ψ)` at `γ_t⁻¹·w`.
* **Unfolding** (**`integral_conj_lowT_inv_mul`**, `conj_pmTermT_mul`, `conj_pmSerT_mul`,
  **`integral_conj_pmSerT_mul`** and **`inner_toLp_pmSerC`**): the change of variables by `γ_t`, with the
  partition of unity moved by `γ_t`, and round 429's unfolding with `κ_t` in place of `κ` give, for `u`
  automorphic with Kubota's character, `⟨Q_t, u⟩ = ∫_{3P×(0,∞)} conj(ψ(v)·ĕ(mz/9))·u(γ_t(z, v)) dz dv/v³`.
* **The pairing with θ** (`thSU`, a definition; `thSU_eq`, `measurable_thSU`, `isAut_thSU`,
  `thSU_ae_eq_thetaF`, `memLp_thSU`, `thetaL_eq_toLp_thSU`, `exists_bound_thS_lowT` and
  **`inner_pmSerC_thetaL`**): for `ψ` bounded and vanishing outside `[α, β]`, `α > 0`, the pairing of `Q_t`
  with θ is the same integral of θ's Fourier series at `γ_t(z, v)`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### The series with the character `κ_t` -/

/-- **The class of the frequencies at `γ_t`**: `ĕ(m·3x/9) = χ_t(x)` for every `x`. -/
def CuspClass (t m : 𝓞 K) : Prop := ∀ x : 𝓞 K, ebr (σO m * σO (3 * x) / 9) = chiT t x

/-- The term of `P^{(t)}_m(ψ)` at a bottom row `(c, d)`: `conj κ_t(γ)·ψ(v(γw))·ĕ(m·z(γw)/9)` with
`γ = γ_{(c, d)}`. -/
def pmTermT (t m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) (cd : BRowT) : ℂ :=
  conj (kubT t (gamRow cd)) * (ψ (slAct (gamRow cd) p).2 * ebr (σO m * (slAct (gamRow cd) p).1 / 9))

/-- **The Poincaré series with the character `κ_t`**:
`P^{(t)}_m(ψ)(w) = Σ_{(c, d)} conj κ_t(γ_{(c, d)})·ψ(v(γ_{(c, d)}w))· ĕ(m·z(γ_{(c, d)}w)/9)`. -/
def pmSerT (t m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) : ℂ := ∑' cd : BRowT, pmTermT t m ψ p cd

/-- `κ_t(γ)·conj κ_t(γ) = 1` on `Γ_1(3)`. -/
theorem kubT_mul_conj (t : 𝓞 K) {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) : kubT t g * conj (kubT t g) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, (isUChar_kubT t).norm_eq g hg]
  norm_num

/-- **The terms along `Γ_1(3)`**: for `m` in the class, the term of `(c, d)` at `g·w` is `κ_t(g)` times the
term of `(c, d)g` at `w`. `γ_{(c, d)}·g = T_{3x}·γ_{(c, d)g}` (round 429's `gamRow_mul_eq`), and the factor
`χ_t(x)` of `κ_t(T_{3x})` cancels `ĕ(m·3x/9)`. -/
theorem pmTermT_slAct {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) {t m : 𝓞 K} (hm : CuspClass t m) (ψ : ℝ → ℂ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : BRowT) :
    pmTermT t m ψ (slAct g p) cd = kubT t g * pmTermT t m ψ p (rowG hg cd) := by
  obtain ⟨x, hx⟩ := gamRow_mul_eq hg cd
  set e := rowG hg cd
  have hq : slAct (gamRow cd) (slAct g p) =
      ((slAct (gamRow e) p).1 + σO (3 * x), (slAct (gamRow e) p).2) := by
    rw [← slAct_mul _ _ hp, hx, slAct_mul _ _ hp, slAct_slT]
  have hχ := isUChar_kubT t
  have hT : slT (3 * x) ∈ Gam3 := slT_mem_Gam3 (dvd_mul_right 3 x)
  have hk : kubT t (gamRow cd) = chiT t x * kubT t (gamRow e) * conj (kubT t g) := by
    have h1 : gamRow cd = slT (3 * x) * gamRow e * g⁻¹ := by rw [← hx]; group
    rw [h1, hχ.map_mul _ (Gam3.mul_mem hT (gamRow_mem e)) _ (Gam3.inv_mem hg),
      hχ.map_mul _ hT _ (gamRow_mem e), kubT_slT, hχ.map_inv hg]
  unfold pmTermT
  rw [hq, hk]
  simp only
  rw [show σO m * ((slAct (gamRow e) p).1 + σO (3 * x)) / 9 =
      σO m * (slAct (gamRow e) p).1 / 9 + σO m * σO (3 * x) / 9 by ring, ebr_add, hm x, map_mul, map_mul,
    Complex.conj_conj]
  have hc := chiT_mul_conj t x
  linear_combination (kubT t g * conj (kubT t (gamRow e)) * ψ (slAct (gamRow e) p).2 *
    ebr (σO m * (slAct (gamRow e) p).1 / 9)) * hc

/-- **`P^{(t)}_m(ψ)` is automorphic with `κ_t`** for `m` in the class (round 429's `rowGEquiv`). -/
theorem isAut_pmSerT {t m : 𝓞 K} (hm : CuspClass t m) (ψ : ℝ → ℂ) : IsAut Gam3 (kubT t) (pmSerT t m ψ) := by
  intro g hg p hp
  unfold pmSerT
  simp_rw [pmTermT_slAct hg hm ψ hp]
  rw [tsum_mul_left]
  congr 1
  exact (rowGEquiv hg).tsum_eq (pmTermT t m ψ p)

/-- The terms are measurable. -/
theorem measurable_pmTermT (t m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) (cd : BRowT) :
    Measurable fun p => pmTermT t m ψ p cd := by
  unfold pmTermT
  refine measurable_const.mul ((hψ.comp (measurable_snd.comp (measurable_slAct _))).mul ?_)
  exact measurable_ebr.comp (((measurable_const.mul (measurable_fst.comp (measurable_slAct _))).div_const 9))

/-- `P^{(t)}_m(ψ)` is measurable. -/
theorem measurable_pmSerT (t m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) : Measurable (pmSerT t m ψ) :=
  Measurable.tsum fun cd => measurable_pmTermT t m hψ cd

/-- `|term of P^{(t)}_m(ψ)| = |ψ(v(γw))|`. -/
theorem norm_pmTermT (t m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) (cd : BRowT) :
    ‖pmTermT t m ψ p cd‖ = ‖ψ (slAct (gamRow cd) p).2‖ := by
  unfold pmTermT
  rw [norm_mul, norm_mul, Complex.norm_conj, (isUChar_kubT t).norm_eq _ (gamRow_mem cd), norm_ebr, one_mul,
    mul_one]

/-! ### The series at the cusp -/

/-- **The Poincaré series at the cusp `γ_t`**: `Q_t = P^{(t)}_m(ψ)∘γ_t⁻¹`. -/
def pmSerC (t m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) : ℂ := pmSerT t m ψ (slAct (lowT t)⁻¹ p)

/-- `κ_t(γ_t⁻¹·g·γ_t) = κ(g)`. -/
theorem kubT_conj_inv (t : 𝓞 K) {g : SL(2, 𝓞 K)} : kubT t ((lowT t)⁻¹ * g * lowT t) = kub ↑g := by
  unfold kubT
  rw [show lowT t * ((lowT t)⁻¹ * g * lowT t) * (lowT t)⁻¹ = g by group]

/-- **`Q_t` is automorphic with Kubota's character**, for `m` in the class (round 382's `conj_mem_Gam3`). -/
theorem isAut_pmSerC {t m : 𝓞 K} (hm : CuspClass t m) (ψ : ℝ → ℂ) :
    IsAut Gam3 (fun g => kub ↑g) (pmSerC t m ψ) := by
  intro g hg p hp
  show pmSerT t m ψ (slAct (lowT t)⁻¹ (slAct g p)) = kub ↑g * pmSerT t m ψ (slAct (lowT t)⁻¹ p)
  rw [← slAct_mul _ _ hp, show (lowT t)⁻¹ * g = ((lowT t)⁻¹ * g * lowT t) * (lowT t)⁻¹ by group,
    slAct_mul _ _ hp, isAut_pmSerT hm ψ _ (conj_mem_Gam3 hg (lowT t)) _ (slAct_mem _ hp), kubT_conj_inv]

/-- `Q_t` is measurable. -/
theorem measurable_pmSerC (t m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) : Measurable (pmSerC t m ψ) :=
  (measurable_pmSerT t m hψ).comp (measurable_slAct _)

/-- `Σ |term of P^{(t)}_m(ψ)| = Σ |term of E(ψ)|` (round 429's `tsum_enorm_pmTerm_eq`). -/
theorem tsum_enorm_pmTermT_eq (t m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) :
    ∑' cd : BRowT, ‖pmTermT t m ψ p cd‖ₑ = ∑' cd, ‖psTerm ψ p cd‖ₑ := by
  rw [← tsum_enorm_pmTerm_eq m ψ p]
  refine tsum_congr fun cd => ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_pmTermT, norm_pmTerm]

/-- **`Q_t` is in `L²(ν)`** for `ψ` measurable with `|ψ(v)| ≤ C·v^τ` (`C ≥ 0`, `τ > 2`) and `|ψ| ≤ D` on
`(0, ∞)`: at the cusp `g·∞` its terms are those of `E(|ψ|)` at the cusp `γ_t⁻¹g·∞` (round 429's
`tsum_enorm_psTerm_slAct_le`, round 423's `lintegral_puLe_top_mul_lt_top`). -/
theorem memLp_pmSerC (t m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {C τ D : ℝ} (hC : 0 ≤ C) (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖ψ v‖ ≤ C * v ^ τ) (hD : ∀ v, 0 < v → ‖ψ v‖ ≤ D) :
    MemLp (pmSerC t m ψ) 2 (muR rhoG) := by
  have hm := measurable_pmSerC t m hψ
  refine memLp_two_of_lintegral hm ?_
  rw [muR, lintegral_withDensity_eq_lintegral_mul _ isPU_rhoG.1 (hm.enorm.pow_const 2)]
  refine lintegral_puLe_top_mul_lt_top Gam3 (hm.enorm.pow_const 2) fun g => ?_
  refine ⟨((rowsZ ((lowT t)⁻¹ * g)).encard * ENNReal.ofReal D +
    ENNReal.ofReal (C * (cuspC τ * (1 / 2 : ℝ) ^ (2 - τ)))) ^ 2, ?_, fun p hp => ?_⟩
  · have hE : ((rowsZ ((lowT t)⁻¹ * g)).encard : ℝ≥0∞) ≠ ⊤ := by
      simpa using (rowsZ_finite ((lowT t)⁻¹ * g)).encard_lt_top.ne
    exact ENNReal.pow_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hE ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  · have hv : 1 / 2 ≤ p.2 := hp.2
    have hp0 : p ∈ UHS := show 0 < p.2 by linarith
    have h2 : p.2 ^ (2 - τ) ≤ (1 / 2 : ℝ) ^ (2 - τ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hv (by linarith)
    have hcC := cuspC_nonneg (by linarith : 1 < τ)
    change ‖pmSerT t m ψ (slAct (lowT t)⁻¹ (slAct g p))‖ₑ ^ 2 ≤ _
    rw [← slAct_mul _ _ hp0]
    gcongr
    calc ‖pmSerT t m ψ (slAct ((lowT t)⁻¹ * g) p)‖ₑ
        ≤ ∑' cd : BRowT, ‖pmTermT t m ψ (slAct ((lowT t)⁻¹ * g) p) cd‖ₑ := enorm_tsum_le_tsum_enorm
      _ = ∑' cd, ‖psTerm ψ (slAct ((lowT t)⁻¹ * g) p) cd‖ₑ := tsum_enorm_pmTermT_eq t m ψ _
      _ ≤ (rowsZ ((lowT t)⁻¹ * g)).encard * ENNReal.ofReal D +
            ENNReal.ofReal (C * (cuspC τ * p.2 ^ (2 - τ))) :=
          tsum_enorm_psTerm_slAct_le hC hτ hf hD _ hv
      _ ≤ _ := by gcongr

/-- `Q_t` is in `L²(ν)` for `ψ` measurable and bounded, vanishing outside `[α, β]` with `α > 0` (round 424's
`norm_le_pow_of_vanish`). -/
theorem memLp_pmSerC_Icc (t m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) :
    MemLp (pmSerC t m ψ) 2 (muR rhoG) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h0 : ∀ v, 0 < v → v < α → ψ v = 0 := fun v _ hv => hψ0 v fun h => (not_le.2 hv) h.1
  exact memLp_pmSerC t m hψ (C := M * (α ^ 3)⁻¹) (τ := 3) (D := M) (by positivity) (by norm_num)
    (fun v hv => norm_le_pow_of_vanish hα hM0 h0 (fun v _ => hM v) hv) (fun v _ => hM v)

/-! ### Unfolding -/

/-- **The change of variables by `γ_t`**: for `u` automorphic with `κ_t` and `w` automorphic with Kubota's
character, `∫conj u(γ_t⁻¹p)·w(p) dν = ∫conj u(p)·w(γ_t p) dν`, as round 442's `integral_conj_sS_inv_mul` for
`S` (round 439's `integral_muR_slAct` and `integral_isPU_eq`, round 442's `isPU_rhoG_comp`). -/
theorem integral_conj_lowT_inv_mul (t : 𝓞 K) {u w : ℂ × ℝ → ℂ} (hum : Measurable u) (hwm : Measurable w)
    (hu : IsAut Gam3 (kubT t) u) (hw : IsAut Gam3 (fun g => kub ↑g) w)
    (hint : ∫⁻ p, ‖conj (u (slAct (lowT t)⁻¹ p)) * w p‖ₑ ∂(muR rhoG) < ⊤) :
    ∫ p, conj (u (slAct (lowT t)⁻¹ p)) * w p ∂(muR rhoG) =
      ∫ p, conj (u p) * w (slAct (lowT t) p) ∂(muR rhoG) := by
  set G : ℂ × ℝ → ℂ := fun p => conj (u p) * w (slAct (lowT t) p) with hG
  have hGm : Measurable G :=
    (Complex.continuous_conj.measurable.comp hum).mul (hwm.comp (measurable_slAct _))
  have hback : ∀ p ∈ UHS, G (slAct (lowT t)⁻¹ p) = conj (u (slAct (lowT t)⁻¹ p)) * w p := fun p hp => by
    simp only [hG]
    rw [slAct_slAct_inv (lowT t) hp]
  have h1 : ∫ p, G p ∂(muR fun p => rhoG (slAct (lowT t) p)) =
      ∫ p, conj (u (slAct (lowT t)⁻¹ p)) * w p ∂(muR rhoG) := by
    rw [integral_muR_slAct (lowT t) isPU_rhoG.1 (fun p hp => rhoG_lt_top hp) hGm]
    refine integral_congr_ae ?_
    filter_upwards [ae_muR_UHS rhoG] with p hp
    exact hback p hp
  have hinv : ∀ γ ∈ Gam3, ∀ p ∈ UHS, G (slAct γ p) = G p := by
    intro γ hγ p hp
    simp only [hG]
    rw [hu γ hγ p hp, slAct_conj (lowT t) γ hp, hw _ (lowT_conj_mem t hγ) _ (slAct_mem _ hp), map_mul]
    have hk := kubT_mul_conj t hγ
    have e : kub ↑(lowT t * γ * (lowT t)⁻¹) = kubT t γ := rfl
    dsimp only
    rw [e]
    linear_combination (conj (u p) * w (slAct (lowT t) p)) * hk
  have hint' : ∫⁻ p, ‖G p‖ₑ ∂(muR fun p => rhoG (slAct (lowT t) p)) < ⊤ := by
    rw [lintegral_muR_slAct (lowT t) isPU_rhoG.1 hGm.enorm]
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hint
    filter_upwards [ae_muR_UHS rhoG] with p hp
    rw [hback p hp]
  rw [← h1, integral_isPU_eq (isPU_rhoG_comp (lowT t)) isPU_rhoG hGm hinv hint']

/-- The terms of `conj P^{(t)}_m(ψ)·u` for `u` automorphic with `κ_t`:
`conj(conj κ_t(γ)·ψ(v(γp))·ĕ(m·z(γp)/9))·u(p) = conj(ψ(v(γp))·ĕ(m·z(γp)/9))·u(γp)`. -/
theorem conj_pmTermT_mul {t : 𝓞 K} {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (kubT t) u) (m : 𝓞 K) (ψ : ℝ → ℂ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : BRowT) :
    conj (pmTermT t m ψ p cd) * u p =
      conj (ψ (slAct (gamRow cd) p).2 * ebr (σO m * (slAct (gamRow cd) p).1 / 9)) *
        u (slAct (gamRow cd) p) := by
  unfold pmTermT
  rw [hu _ (gamRow_mem cd) p hp, map_mul, Complex.conj_conj]
  ring

/-- The series of `conj P^{(t)}_m(ψ)·u`, term by term. -/
theorem conj_pmSerT_mul {t : 𝓞 K} {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (kubT t) u) (m : 𝓞 K) (ψ : ℝ → ℂ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) :
    conj (pmSerT t m ψ p) * u p = ∑' cd : BRowT,
      conj (ψ (slAct (gamRow cd) p).2 * ebr (σO m * (slAct (gamRow cd) p).1 / 9)) *
        u (slAct (gamRow cd) p) := by
  unfold pmSerT
  rw [Complex.conj_tsum, ← tsum_mul_right]
  exact tsum_congr fun cd => conj_pmTermT_mul hu m ψ hp cd

/-- **Unfolding `P^{(t)}_m(ψ)`** against `u` automorphic with `κ_t`, for `m` in the class and
`∫_{3P×(0,∞)} |ψ(v)u(z, v)| dz dv/v³ < ∞`:
`∫conj P^{(t)}_m(ψ)·u dν = ∫_{3P×(0,∞)} conj(ψ(v)·ĕ(mz/9))·u(z, v) dz dv/v³` (round 426's
`integral_unfold_family`, `integral_rhoH_eq` and `muR_rhoT3`). -/
theorem integral_conj_pmSerT_mul {t m : 𝓞 K} (hm : CuspClass t m) {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (kubT t) u) (hum : Measurable u)
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * u p‖ₑ ∂uhsMeasure ≠ ⊤) :
    ∫ p, conj (pmSerT t m ψ p) * u p ∂(muR rhoG) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) * u p ∂uhsMeasure := by
  set Φ : ℂ × ℝ → ℂ := fun p => conj (ψ p.2 * ebr (σO m * p.1 / 9)) * u p with hΦ
  have hΦm : Measurable Φ :=
    (Complex.continuous_conj.measurable.comp ((hψ.comp measurable_snd).mul
      (measurable_ebr.comp ((measurable_const.mul measurable_fst).div_const 9)))).mul hum
  have hper : ∀ x : 𝓞 K, ∀ p ∈ UHS, Φ (slAct (slT (3 * x)) p) = Φ p := by
    intro x p hp
    simp only [hΦ]
    rw [hu _ (slT_mem_Gam3 (dvd_mul_right 3 x)) p hp, kubT_slT, slAct_slT]
    simp only
    rw [show σO m * (p.1 + σO (3 * x)) / 9 = σO m * p.1 / 9 + σO m * σO (3 * x) / 9 by ring, ebr_add, hm x]
    simp only [map_mul]
    have hc := chiT_mul_conj t x
    linear_combination (conj (ψ p.2) * conj (ebr (σO m * p.1 / 9)) * u p) * hc
  have hfinH : ∫⁻ q, rhoH q * ‖Φ q‖ₑ ∂uhsMeasure ≠ ⊤ := by
    rw [lintegral_rhoH_eq hΦm.enorm fun x p hp => by rw [hper x p hp]]
    exact hfin
  have h1 : ∫ p, conj (pmSerT t m ψ p) * u p ∂(muR rhoG) =
      ∫ p, ∑' cd : BRowT, Φ (slAct (gamRow cd) p) ∂(muR rhoG) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_muR_UHS rhoG] with p hp
    exact conj_pmSerT_mul hu m ψ hp
  rw [h1, integral_unfold_family gamRow isPU_rhoG.1 measurable_rhoH (fun q _ => rfl)
    (fun q hq => lt_of_le_of_lt (isPU_rhoG.le_one hq) ENNReal.one_lt_top)
    (fun q hq => lt_of_le_of_lt (rhoH_le_one hq) ENNReal.one_lt_top) hΦm hfinH,
    integral_rhoH_eq hΦm hper hfin, muR_rhoT3]

/-- **The pairing at the cusp `γ_t`**: for `u` automorphic with Kubota's character and in `L²(ν)`,
`⟨Q_t, u⟩ = ∫_{3P×(0,∞)} conj(ψ(v)·ĕ(mz/9))·u(γ_t(z, v)) dz dv/v³`. -/
theorem inner_toLp_pmSerC {t m : 𝓞 K} (hm : CuspClass t m) {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pmSerC t m ψ) 2 (muR rhoG)) {u : ℂ × ℝ → ℂ}
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hum : Measurable u) (hu2 : MemLp u 2 (muR rhoG))
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO m * p.1 / 9)) * u (slAct (lowT t) p)‖ₑ ∂uhsMeasure ≠ ⊤) :
    inner ℂ (hψ2.toLp (pmSerC t m ψ)) (hu2.toLp u) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) * u (slAct (lowT t) p) ∂uhsMeasure := by
  have hint : ∫⁻ p, ‖conj (pmSerT t m ψ (slAct (lowT t)⁻¹ p)) * u p‖ₑ ∂(muR rhoG) < ⊤ := by
    have h1 : MemLp (fun p => conj (pmSerC t m ψ p)) 2 (muR rhoG) :=
      hψ2.of_le ((Complex.continuous_conj.measurable.comp
        (measurable_pmSerC t m hψ)).aestronglyMeasurable)
        (Eventually.of_forall fun p => by rw [Complex.norm_conj])
    exact (h1.integrable_mul hu2).2
  rw [L2.inner_def]
  have e1 : ∫ p, inner ℂ ((hψ2.toLp (pmSerC t m ψ)) p) ((hu2.toLp u) p) ∂(muR rhoG) =
      ∫ p, conj (pmSerT t m ψ (slAct (lowT t)⁻¹ p)) * u p ∂(muR rhoG) := by
    refine integral_congr_ae ?_
    filter_upwards [hψ2.coeFn_toLp, hu2.coeFn_toLp] with p h1 h2
    rw [RCLike.inner_apply', h1, h2]
    rfl
  rw [e1, integral_conj_lowT_inv_mul t (measurable_pmSerT t m hψ) hum (isAut_pmSerT hm ψ) hu hint,
    integral_conj_pmSerT_mul hm hψ (isAut_comp_lowT t hu) (hum.comp (measurable_slAct _)) hfin]

/-! ### The pairing with θ -/

open Classical in
/-- θ's Fourier series (round 436's `thS`), extended by `0` off upper half-space. -/
def thSU (r Y : ℝ) (hY : 0 < Y) : ℂ × ℝ → ℂ := UHS.piecewise (thS r Y hY) 0

/-- `thSU = thS` on upper half-space. -/
theorem thSU_eq {r Y : ℝ} {hY : 0 < Y} {p : ℂ × ℝ} (hp : p ∈ UHS) : thSU r Y hY p = thS r Y hY p := by
  classical
  unfold thSU
  exact Set.piecewise_eq_of_mem _ _ _ hp

/-- `thSU` is measurable (round 436's `continuousOn_thS`). -/
theorem measurable_thSU {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) : Measurable (thSU r Y hY) := by
  classical
  unfold thSU
  exact (continuousOn_thS hr hY).measurable_piecewise continuousOn_const measurableSet_UHS

/-- `thSU` is automorphic with Kubota's character (round 437's `isAut_thS`). -/
theorem isAut_thSU {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    IsAut Gam3 (fun g => kub ↑g) (thSU r Y hY) := by
  intro γ hγ p hp
  rw [thSU_eq (slAct_mem γ hp), thSU_eq hp]
  exact isAut_thS hr hY γ hγ p hp

/-- `thSU = θ̃` almost everywhere for `ν` (round 448's `ae_uhs_thetaF_eq_thS`). -/
theorem thSU_ae_eq_thetaF {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    thSU r Y hY =ᵐ[muR rhoG] thetaF r Y hY := by
  have h : ∀ᵐ p ∂uhsMeasure, thetaF r Y hY p = thSU r Y hY p := by
    filter_upwards [ae_uhs_thetaF_eq_thS hr hY, ae_UHS] with p h1 h2
    rw [thSU_eq h2, h1]
  filter_upwards [withDensity_absolutelyContinuous uhsMeasure rhoG h] with p hp
  exact hp.symm

/-- `thSU` is in `L²(ν)` (round 432's `memLp_thetaF`). -/
theorem memLp_thSU {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) : MemLp (thSU r Y hY) 2 (muR rhoG) :=
  (memLp_thetaF hr hY).ae_eq (thSU_ae_eq_thetaF hr hY).symm

/-- θ in `L²(ν)` is the class of `thSU` (round 425's `thetaL_ae_eq_thetaF`). -/
theorem thetaL_eq_toLp_thSU {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    thetaL r Y hY = (memLp_thSU hr hY).toLp (thSU r Y hY) := by
  refine Lp.ext ?_
  filter_upwards [thetaL_ae_eq_thetaF hr hY, thSU_ae_eq_thetaF hr hY, (memLp_thSU hr hY).coeFn_toLp]
    with p h1 h2 h3
  rw [h1, h3, h2]

/-- θ's Fourier series at `γ_t(z, v)` is bounded on `3P × [α, β]` for `α > 0`: the set lies in the compact
`{|z| ≤ 6} × [α, β]` (round 430's `norm_le_six_of_mem_fundP3`), where `(z, v) ↦ θ(γ_t(z, v))` is continuous
(round 437's `continuousOn_slAct`). -/
theorem exists_bound_thS_lowT {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (t : 𝓞 K) {α β : ℝ} (hα : 0 < α) :
    ∃ B : ℝ, ∀ p : ℂ × ℝ, p.1 ∈ fundP3 → p.2 ∈ Icc α β → ‖thSU r Y hY (slAct (lowT t) p)‖ ≤ B := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 6 ×ˢ Icc α β) :=
    (isCompact_closedBall 0 6).prod isCompact_Icc
  have hKU : Metric.closedBall (0 : ℂ) 6 ×ˢ Icc α β ⊆ UHS := fun p hp => by
    show 0 < p.2
    exact lt_of_lt_of_le hα hp.2.1
  have hc : ContinuousOn (fun p => thS r Y hY (slAct (lowT t) p)) (Metric.closedBall (0 : ℂ) 6 ×ˢ Icc α β) :=
    ((continuousOn_thS hr hY).comp (continuousOn_slAct (lowT t)) fun p hp => slAct_mem _ hp).mono hKU
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨B, fun p h1 h2 => ?_⟩
  have hpK : p ∈ Metric.closedBall (0 : ℂ) 6 ×ˢ Icc α β :=
    ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact norm_le_six_of_mem_fundP3 h1, h2⟩
  rw [thSU_eq (slAct_mem _ (hKU hpK))]
  exact hB p hpK

/-- **The pairing of `Q_t` with θ**: for `ψ` measurable and bounded, vanishing outside `[α, β]` with `α > 0`,
`⟨Q_t, θ⟩ = ∫_{3P×(0,∞)} conj(ψ(v)·ĕ(mz/9))·θ(γ_t(z, v)) dz dv/v³` with θ's Fourier series (round 430's
`lintegral_rhoT3_pm_ne_top`). -/
theorem inner_pmSerC_thetaL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {t m : 𝓞 K} (hm : CuspClass t m)
    {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0)
    (hα : 0 < α) :
    inner ℂ ((memLp_pmSerC_Icc t m hψ hM hψ0 hα).toLp (pmSerC t m ψ)) (thetaL r Y hY) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO m * p.1 / 9)) * thS r Y hY (slAct (lowT t) p)
        ∂uhsMeasure := by
  obtain ⟨B, hB⟩ := exists_bound_thS_lowT hr hY t hα (β := β)
  have hfin := lintegral_rhoT3_pm_ne_top m hM hψ0 hα (G := fun p => thSU r Y hY (slAct (lowT t) p)) hB
  rw [thetaL_eq_toLp_thSU hr hY, inner_toLp_pmSerC hm hψ _ (isAut_thSU hr hY) (measurable_thSU hr hY)
    (memLp_thSU hr hY) hfin]
  refine setIntegral_congr_ae (measurableSet_fundP3.preimage measurable_fst) ?_
  filter_upwards [ae_UHS] with p hp _
  rw [thSU_eq (slAct_mem _ hp)]

end Eis

end

#print axioms Eis.kubT_mul_conj
#print axioms Eis.pmTermT_slAct
#print axioms Eis.isAut_pmSerT
#print axioms Eis.measurable_pmTermT
#print axioms Eis.measurable_pmSerT
#print axioms Eis.norm_pmTermT
#print axioms Eis.kubT_conj_inv
#print axioms Eis.isAut_pmSerC
#print axioms Eis.measurable_pmSerC
#print axioms Eis.tsum_enorm_pmTermT_eq
#print axioms Eis.memLp_pmSerC
#print axioms Eis.memLp_pmSerC_Icc
#print axioms Eis.integral_conj_lowT_inv_mul
#print axioms Eis.conj_pmTermT_mul
#print axioms Eis.conj_pmSerT_mul
#print axioms Eis.integral_conj_pmSerT_mul
#print axioms Eis.inner_toLp_pmSerC
#print axioms Eis.thSU_eq
#print axioms Eis.measurable_thSU
#print axioms Eis.isAut_thSU
#print axioms Eis.thSU_ae_eq_thetaF
#print axioms Eis.memLp_thSU
#print axioms Eis.thetaL_eq_toLp_thSU
#print axioms Eis.exists_bound_thS_lowT
#print axioms Eis.inner_pmSerC_thetaL
