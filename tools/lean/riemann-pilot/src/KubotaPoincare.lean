import KubotaUnfoldEis
import KubotaEisFourier

/-! # Twisted pseudo-Eisenstein series (round 429)

S5f-10 of round 360's plan, part 12 (S5f-10f, second part). Round 428's next step planned the series `P_m(ψ)`,
a pseudo-Eisenstein series twisted by the character `ĕ(m·z(γw)/9)`, its automorphy, its square-integrability
and its unfolding. This round proves them, with `γ_{(c, d)}` round 426's element of `Γ_1(3)` with bottom row
`(c, d)`, `ν = ρ_G dμ` as in round 423, and frequencies `m = δ₃x`:

* **The series** (`pmTerm` and `pmSer`, definitions): `P_m(ψ)(w) = Σ_{(c, d)} (c/d)₃·ψ(v(γw))·ĕ(m·z(γw)/9)`
  with `γ = γ_{(c, d)}`.
* **Automorphy** (`rowG` and `rowGEquiv`, definitions; **`isAut_pmSer`**, with `gamRow_mul_eq`,
  `kub_mul_conj_kub`, `pmTerm_slAct`, `measurable_pmTerm`, `measurable_pmSer` and `norm_pmTerm`):
  `γ_{(c, d)}·g = T_{3t}·γ_{(c, d)g}` for `g ∈ Γ_1(3)` (round 426's `eq_slT_of_Gam3`), the translation does
  not change `ĕ(m·z/9)` (round 428's `ebr_period`), and `(c/d)₃ = κ(g)·((c, d)g)₃` (round 387's `cub_rowMul`),
  so `P_m(ψ)(g·w) = κ(g)·P_m(ψ)(w)`.
* **Square-integrability** (`rowsZ`, a definition; **`tsum_enorm_psTerm_slAct_le`**, **`memLp_pmSer`** and
  **`memLp_pmSer_Icc`**, with `rowsZ_finite` and `tsum_enorm_pmTerm_eq`): `|P_m(ψ)|` is at most the sum of the
  absolute values of the terms of `E(ψ)`. At the cusp `g·∞` the rows sent to `(0, *)` by `g` are finitely
  many, since they are sent to `(0, u)` with `u` a unit (round 388's `isUnit_rowMul_snd`), and the others are
  bounded by round 388's `tsum_height_ne_le`. So `P_m(ψ)` is in `L²(ν)` for `ψ` measurable with
  `|ψ(v)| ≤ C·v^τ`, `τ > 2`, and `ψ` bounded (round 423's `lintegral_puLe_top_mul_lt_top`), in particular for
  `ψ` bounded and vanishing outside `[α, β]`, `α > 0`.
* **Unfolding** (**`integral_conj_pmSer_mul`** and **`inner_toLp_pmSer`**, with `conj_pmTerm_mul` and
  `conj_pmSer_mul`): for `u` automorphic with Kubota's character,
  `∫conj P_m(ψ)·u dν = ∫_{3P×(0,∞)} conj(ψ(v)·ĕ(mz/9))·u(z, v) dz dv/v³` when the right side converges
  absolutely, by round 426's unfolding over the family `γ_{(c, d)}` and change of partition; in `L²(ν)` this
  is `⟨P_m(ψ), u⟩`.
-/

open MeasureTheory Set Filter NumberField Complex Ideal
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### The series -/

/-- The term of `P_m(ψ)` at a bottom row `(c, d)`: `(c/d)₃·ψ(v(γw))·ĕ(m·z(γw)/9)` with `γ = γ_{(c, d)}`. -/
def pmTerm (m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) (cd : BRowT) : ℂ :=
  σO (cub cd.1.1 (span {cd.1.2})) *
    (ψ (slAct (gamRow cd) p).2 * ebr (σO m * (slAct (gamRow cd) p).1 / 9))

/-- **The twisted pseudo-Eisenstein series** `P_m(ψ)(w) = Σ_{(c, d)} (c/d)₃·ψ(v(γw))·ĕ(m·z(γw)/9)`. -/
def pmSer (m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) : ℂ := ∑' cd : BRowT, pmTerm m ψ p cd

/-- The bottom row of `γ_{(c, d)}·g`, as an element of `BRowT`. -/
def rowG {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (cd : BRowT) : BRowT :=
  ⟨rowMul g cd.1, bRow_rowMul hg cd.2⟩

/-- `γ_{(c, d)}·g = T_{3t}·γ_{(c, d)g}` for `g ∈ Γ_1(3)`. -/
theorem gamRow_mul_eq {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (cd : BRowT) :
    ∃ t : 𝓞 K, gamRow cd * g = slT (3 * t) * gamRow (rowG hg cd) := by
  set e := rowG hg cd
  have hδ : gamRow cd * g * (gamRow e)⁻¹ ∈ Gam3 :=
    Gam3.mul_mem (Gam3.mul_mem (gamRow_mem cd) hg) (Gam3.inv_mem (gamRow_mem e))
  have h1 : rowMul g (gamRow cd 1 0, gamRow cd 1 1) = ((gamRow cd * g) 1 0, (gamRow cd * g) 1 1) :=
    rowMul_bottom _ _
  have h2 : rowMul (gamRow e)⁻¹ ((gamRow cd * g) 1 0, (gamRow cd * g) 1 1) =
      ((gamRow cd * g * (gamRow e)⁻¹) 1 0, (gamRow cd * g * (gamRow e)⁻¹) 1 1) := rowMul_bottom _ _
  have h3 : rowMul (gamRow e)⁻¹ (gamRow e 1 0, gamRow e 1 1) = (0, 1) := by
    rw [rowMul_bottom, mul_inv_cancel]
    simp
  have he : ((gamRow cd * g) 1 0, (gamRow cd * g) 1 1) = (gamRow e 1 0, gamRow e 1 1) := by
    rw [← h1, gamRow_10, gamRow_11, gamRow_10, gamRow_11]
    rfl
  rw [he, h3] at h2
  obtain ⟨t, ht⟩ := eq_slT_of_Gam3 hδ (congrArg Prod.fst h2).symm (congrArg Prod.snd h2).symm
  exact ⟨t, by rw [← ht, inv_mul_cancel_right]⟩

theorem kub_mul_conj_kub {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) : kub ↑g * conj (kub ↑g) = 1 := by
  have hn := norm_kub g.2 (mem_Gam3.1 hg)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  norm_num

/-- **The terms along `Γ_1(3)`**: the term of `(c, d)` at `g·p` is `κ(g)` times the term of `(c, d)g` at `p`,
for `m = δ₃x`. -/
theorem pmTerm_slAct {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (x : 𝓞 K) (ψ : ℝ → ℂ) {p : ℂ × ℝ}
    (hp : p ∈ UHS) (cd : BRowT) :
    pmTerm (δ3 * x) ψ (slAct g p) cd = kub ↑g * pmTerm (δ3 * x) ψ p (rowG hg cd) := by
  obtain ⟨t, ht⟩ := gamRow_mul_eq hg cd
  have hq : slAct (gamRow cd) (slAct g p) =
      ((slAct (gamRow (rowG hg cd)) p).1 + σO (3 * t), (slAct (gamRow (rowG hg cd)) p).2) := by
    rw [← slAct_mul _ _ hp, ht, slAct_mul _ _ hp, slAct_slT]
  have hc : σO (cub (rowG hg cd).1.1 (span {(rowG hg cd).1.2})) =
      σO (cub cd.1.1 (span {cd.1.2})) * conj (kub ↑g) := cub_rowMul hg cd.2
  unfold pmTerm
  rw [hq, hc]
  simp only
  have hper : ebr (σO (δ3 * x) * ((slAct (gamRow (rowG hg cd)) p).1 + σO (3 * t)) / 9) =
      ebr (σO (δ3 * x) * (slAct (gamRow (rowG hg cd)) p).1 / 9) := by
    rw [show σO (δ3 * x) * ((slAct (gamRow (rowG hg cd)) p).1 + σO (3 * t)) / 9 =
        σO (δ3 * x) * (slAct (gamRow (rowG hg cd)) p).1 / 9 + σO (δ3 * x) * σO (3 * t) / 9 by ring,
      ebr_add, ebr_period, mul_one]
  rw [hper]
  have hk := kub_mul_conj_kub hg
  linear_combination (σO (cub cd.1.1 (span {cd.1.2})) *
    (ψ (slAct (gamRow (rowG hg cd)) p).2 *
      ebr (σO (δ3 * x) * (slAct (gamRow (rowG hg cd)) p).1 / 9))) * hk.symm

/-- The bijection `(c, d) ↦ (c, d)g` of the bottom rows, for `g ∈ Γ_1(3)`. -/
def rowGEquiv {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) : BRowT ≃ BRowT :=
  (rowEquiv g).subtypeEquiv fun cd => (bRow_rowMul_iff hg cd).symm

/-- **`P_m(ψ)` is automorphic** with Kubota's character, for `m = δ₃x`. -/
theorem isAut_pmSer (x : 𝓞 K) (ψ : ℝ → ℂ) :
    IsAut Gam3 (fun g => kub ↑g) (pmSer (δ3 * x) ψ) := by
  intro g hg p hp
  unfold pmSer
  simp_rw [pmTerm_slAct hg x ψ hp]
  rw [tsum_mul_left]
  congr 1
  exact (rowGEquiv hg).tsum_eq (pmTerm (δ3 * x) ψ p)

theorem measurable_pmTerm (m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) (cd : BRowT) :
    Measurable fun p => pmTerm m ψ p cd := by
  unfold pmTerm
  refine measurable_const.mul ((hψ.comp (measurable_snd.comp (measurable_slAct _))).mul ?_)
  exact measurable_ebr.comp (((measurable_const.mul (measurable_fst.comp (measurable_slAct _))).div_const 9))

theorem measurable_pmSer (m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) : Measurable (pmSer m ψ) :=
  Measurable.tsum fun cd => measurable_pmTerm m hψ cd

/-- `|term of P_m(ψ)| = |ψ(v(γw))|`. -/
theorem norm_pmTerm (m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) (cd : BRowT) :
    ‖pmTerm m ψ p cd‖ = ‖ψ (slAct (gamRow cd) p).2‖ := by
  unfold pmTerm
  rw [norm_mul, norm_mul, norm_σO_cub cd.2.2.2 cd.2.1, norm_ebr, one_mul, mul_one]

/-! ### Square-integrability -/

/-- The bottom rows sent to `(0, *)` by `g`. -/
def rowsZ (g : SL(2, 𝓞 K)) : Set (𝓞 K × 𝓞 K) := {cd | BRow cd ∧ (rowMul g cd).1 = 0}

/-- **Finitely many bottom rows go to `(0, *)`**: they go to `(0, u)` with `u` a unit. -/
theorem rowsZ_finite (g : SL(2, 𝓞 K)) : (rowsZ g).Finite := by
  have hfin : ({(0 : 𝓞 K)} ×ˢ Set.range ((↑) : (𝓞 K)ˣ → 𝓞 K)).Finite :=
    (Set.finite_singleton _).prod (Set.finite_range _)
  refine (hfin.preimage (rowEquiv g).injective.injOn).subset fun cd hcd => ?_
  obtain ⟨hb, h0⟩ := hcd
  obtain ⟨u, hu⟩ := isUnit_rowMul_snd hb h0
  refine ⟨?_, u, hu⟩
  change (rowMul g cd).1 ∈ ({0} : Set (𝓞 K))
  rw [h0]
  rfl

open Classical in
/-- **The majorant at the cusp `g·∞`**: for `|f(v)| ≤ C·v^τ` with `C ≥ 0`, `τ > 2`, and `|f| ≤ D` on `(0, ∞)`,
`Σ_{(c, d)} |term of f at g·p| ≤ #(rowsZ g)·D + C·cuspC(τ)·v^{2−τ}` for `v ≥ 1/2`. -/
theorem tsum_enorm_psTerm_slAct_le {f : ℝ → ℂ} {C τ D : ℝ} (hC : 0 ≤ C) (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖f v‖ ≤ C * v ^ τ) (hD : ∀ v, 0 < v → ‖f v‖ ≤ D) (g : SL(2, 𝓞 K))
    {p : ℂ × ℝ} (hv : 1 / 2 ≤ p.2) :
    ∑' cd, ‖psTerm f (slAct g p) cd‖ₑ ≤
      (rowsZ g).encard * ENNReal.ofReal D + ENNReal.ofReal (C * (cuspC τ * p.2 ^ (2 - τ))) := by
  have hp : p ∈ UHS := show 0 < p.2 by linarith
  have hgp : slAct g p ∈ UHS := slAct_mem g hp
  set S := rowsZ g
  have hsplit : ∀ cd, ‖psTerm f (slAct g p) cd‖ₑ =
      S.indicator (fun cd => ‖psTerm f (slAct g p) cd‖ₑ) cd +
        Sᶜ.indicator (fun cd => ‖psTerm f (slAct g p) cd‖ₑ) cd := fun cd =>
    (congrFun (Set.indicator_self_add_compl S fun cd => ‖psTerm f (slAct g p) cd‖ₑ) cd).symm
  rw [tsum_congr hsplit, ENNReal.tsum_add]
  gcongr
  · calc ∑' cd, S.indicator (fun cd => ‖psTerm f (slAct g p) cd‖ₑ) cd
        ≤ ∑' cd, S.indicator (fun _ => ENNReal.ofReal D) cd := by
          refine ENNReal.tsum_le_tsum fun cd => ?_
          by_cases hcd : cd ∈ S
          · rw [indicator_of_mem hcd, indicator_of_mem hcd]
            obtain ⟨hb, h0⟩ := hcd
            unfold psTerm
            simp only [hb, ↓reduceIte]
            rw [height_slAct_of_fst hb h0 hp, enorm_mul, ← ofReal_norm (σO _),
              norm_σO_cub hb.2.2 hb.1, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hD _ hp)
          · rw [indicator_of_notMem hcd, indicator_of_notMem hcd]
      _ = S.encard * ENNReal.ofReal D := by
          rw [← tsum_subtype S (fun _ => ENNReal.ofReal D), ENNReal.tsum_set_const]
  · obtain hle := tsum_height_ne_le hτ p.1 hv
    calc ∑' cd, Sᶜ.indicator (fun cd => ‖psTerm f (slAct g p) cd‖ₑ) cd
        ≤ ∑' cd, ENNReal.ofReal C * (if (rowMul g cd).1 = 0 then 0 else
            ENNReal.ofReal ((p.2 / uhsDen (σO (rowMul g cd).1) (σO (rowMul g cd).2) p.1 p.2) ^ τ)) := by
          refine ENNReal.tsum_le_tsum fun cd => ?_
          by_cases hcd : cd ∈ S
          · rw [indicator_of_notMem (show cd ∉ Sᶜ from fun h => h hcd)]
            exact zero_le
          · rw [indicator_of_mem (show cd ∈ Sᶜ from hcd)]
            by_cases hb : BRow cd
            · have h0 : (rowMul g cd).1 ≠ 0 := fun h0 => hcd ⟨hb, h0⟩
              simp only [h0, ↓reduceIte]
              have h1 := norm_psTerm_le hf hgp cd
              simp only [hb, ↓reduceIte] at h1
              rw [height_rowMul g hb hp] at h1
              rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
              exact ENNReal.ofReal_le_ofReal h1
            · rw [psTerm_of_not_bRow f _ hb, enorm_zero]
              exact zero_le
      _ = ENNReal.ofReal C * ∑' e : 𝓞 K × 𝓞 K, (if e.1 = 0 then 0 else
            ENNReal.ofReal ((p.2 / uhsDen (σO e.1) (σO e.2) p.1 p.2) ^ τ)) := by
          rw [ENNReal.tsum_mul_left]
          congr 1
          exact (rowEquiv g).tsum_eq (fun e : 𝓞 K × 𝓞 K => if e.1 = 0 then 0 else
            ENNReal.ofReal ((p.2 / uhsDen (σO e.1) (σO e.2) p.1 p.2) ^ τ))
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (cuspC τ * p.2 ^ (2 - τ)) := by gcongr
      _ = ENNReal.ofReal (C * (cuspC τ * p.2 ^ (2 - τ))) := (ENNReal.ofReal_mul hC).symm

open Classical in
/-- `Σ_{(c, d)} |term of P_m(ψ)| = Σ_{(c, d)} |term of E(ψ)|`. -/
theorem tsum_enorm_pmTerm_eq (m : 𝓞 K) (ψ : ℝ → ℂ) (p : ℂ × ℝ) :
    ∑' cd : BRowT, ‖pmTerm m ψ p cd‖ₑ = ∑' cd, ‖psTerm ψ p cd‖ₑ := by
  have e1 : ∀ cd : BRowT, ‖pmTerm m ψ p cd‖ₑ = ‖psTerm ψ p cd.1‖ₑ := by
    intro cd
    rw [← ofReal_norm, ← ofReal_norm, norm_pmTerm, psTerm_eq_of_row cd.2 (gamRow_10 cd) (gamRow_11 cd),
      norm_mul, norm_σO_cub cd.2.2.2 cd.2.1, one_mul]
  have e2 : ∀ cd, ‖psTerm ψ p cd‖ₑ = {cd | BRow cd}.indicator (fun cd => ‖psTerm ψ p cd‖ₑ) cd := by
    intro cd
    by_cases hb : BRow cd
    · rw [indicator_of_mem (show cd ∈ {cd | BRow cd} from hb)]
    · rw [indicator_of_notMem (show cd ∉ {cd | BRow cd} from hb), psTerm_of_not_bRow ψ p hb, enorm_zero]
  rw [tsum_congr e1, tsum_congr e2, ← tsum_subtype]
  rfl

/-- **`P_m(ψ)` is in `L²(ν)`** for `ψ` measurable with `|ψ(v)| ≤ C·v^τ` (`C ≥ 0`, `τ > 2`) and `|ψ| ≤ D` on
`(0, ∞)`. -/
theorem memLp_pmSer (m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {C τ D : ℝ} (hC : 0 ≤ C) (hτ : 2 < τ)
    (hf : ∀ v, 0 < v → ‖ψ v‖ ≤ C * v ^ τ) (hD : ∀ v, 0 < v → ‖ψ v‖ ≤ D) :
    MemLp (pmSer m ψ) 2 (muR rhoG) := by
  have hm := measurable_pmSer m hψ
  refine memLp_two_of_lintegral hm ?_
  rw [muR, lintegral_withDensity_eq_lintegral_mul _ isPU_rhoG.1 (hm.enorm.pow_const 2)]
  refine lintegral_puLe_top_mul_lt_top Gam3 (hm.enorm.pow_const 2) fun g => ?_
  refine ⟨((rowsZ g).encard * ENNReal.ofReal D +
    ENNReal.ofReal (C * (cuspC τ * (1 / 2 : ℝ) ^ (2 - τ)))) ^ 2, ?_, fun p hp => ?_⟩
  · have hE : ((rowsZ g).encard : ℝ≥0∞) ≠ ⊤ := by
      simpa using (rowsZ_finite g).encard_lt_top.ne
    exact ENNReal.pow_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hE ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  · have hv : 1 / 2 ≤ p.2 := hp.2
    have h2 : p.2 ^ (2 - τ) ≤ (1 / 2 : ℝ) ^ (2 - τ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hv (by linarith)
    have hcC := cuspC_nonneg (by linarith : 1 < τ)
    change ‖pmSer m ψ (slAct g p)‖ₑ ^ 2 ≤ _
    gcongr
    calc ‖pmSer m ψ (slAct g p)‖ₑ ≤ ∑' cd : BRowT, ‖pmTerm m ψ (slAct g p) cd‖ₑ :=
          enorm_tsum_le_tsum_enorm
      _ = ∑' cd, ‖psTerm ψ (slAct g p) cd‖ₑ := tsum_enorm_pmTerm_eq m ψ _
      _ ≤ (rowsZ g).encard * ENNReal.ofReal D + ENNReal.ofReal (C * (cuspC τ * p.2 ^ (2 - τ))) :=
          tsum_enorm_psTerm_slAct_le hC hτ hf hD g hv
      _ ≤ _ := by gcongr

/-- `P_m(ψ)` is in `L²(ν)` for `ψ` measurable and bounded, vanishing outside `[α, β]` with `α > 0`. -/
theorem memLp_pmSer_Icc (m : 𝓞 K) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) :
    MemLp (pmSer m ψ) 2 (muR rhoG) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h0 : ∀ v, 0 < v → v < α → ψ v = 0 := fun v _ hv => hψ0 v fun h => (not_le.2 hv) h.1
  refine memLp_pmSer m hψ (C := M * (α ^ 3)⁻¹) (τ := 3) (D := M) (by positivity) (by norm_num)
    (fun v hv => norm_le_pow_of_vanish hα hM0 h0 (fun v _ => hM v) hv) (fun v _ => hM v)

/-! ### Unfolding -/

/-- The terms of `conj P_m(ψ)·u`:
`conj((c/d)₃·ψ(v(γp))·ĕ(m·z(γp)/9))·u(p) = conj(ψ(v(γp))·ĕ(m·z(γp)/9))·u(γp)` for `u` automorphic with
Kubota's character (round 387's `kub_eq_conj_cub`). -/
theorem conj_pmTerm_mul {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) (m : 𝓞 K) (ψ : ℝ → ℂ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : BRowT) :
    conj (pmTerm m ψ p cd) * u p =
      conj (ψ (slAct (gamRow cd) p).2 * ebr (σO m * (slAct (gamRow cd) p).1 / 9)) *
        u (slAct (gamRow cd) p) := by
  unfold pmTerm
  rw [hu _ (gamRow_mem cd) p hp]
  dsimp only
  rw [kub_eq_conj_cub (gamRow cd).2 (mem_Gam3.1 (gamRow_mem cd)), gamRow_10, gamRow_11, map_mul]
  ring

theorem conj_pmSer_mul {u : ℂ × ℝ → ℂ} (hu : IsAut Gam3 (fun g => kub ↑g) u) (m : 𝓞 K) (ψ : ℝ → ℂ)
    {p : ℂ × ℝ} (hp : p ∈ UHS) :
    conj (pmSer m ψ p) * u p = ∑' cd : BRowT,
      conj (ψ (slAct (gamRow cd) p).2 * ebr (σO m * (slAct (gamRow cd) p).1 / 9)) *
        u (slAct (gamRow cd) p) := by
  unfold pmSer
  rw [Complex.conj_tsum, ← tsum_mul_right]
  exact tsum_congr fun cd => conj_pmTerm_mul hu m ψ hp cd

/-- **Unfolding `P_m(ψ)` against an automorphic function**: for `m = δ₃x`, `ψ` and `u` measurable, `u`
automorphic with Kubota's character, and `∫_{3P×(0,∞)} |ψ(v)u(z, v)| dz dv/v³ < ∞`,
`∫conj P_m(ψ)·u dν = ∫_{3P×(0,∞)} conj(ψ(v)·ĕ(mz/9))·u(z, v) dz dv/v³`. -/
theorem integral_conj_pmSer_mul {x : 𝓞 K} {ψ : ℝ → ℂ} (hψ : Measurable ψ) {u : ℂ × ℝ → ℂ}
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hum : Measurable u)
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO (δ3 * x) * p.1 / 9)) * u p‖ₑ ∂uhsMeasure ≠ ⊤) :
    ∫ p, conj (pmSer (δ3 * x) ψ p) * u p ∂(muR rhoG) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO (δ3 * x) * p.1 / 9)) * u p ∂uhsMeasure := by
  set Φ : ℂ × ℝ → ℂ := fun p => conj (ψ p.2 * ebr (σO (δ3 * x) * p.1 / 9)) * u p with hΦ
  have hΦm : Measurable Φ :=
    (Complex.continuous_conj.measurable.comp ((hψ.comp measurable_snd).mul
      (measurable_ebr.comp ((measurable_const.mul measurable_fst).div_const 9)))).mul hum
  have hper : ∀ t : 𝓞 K, ∀ p ∈ UHS, Φ (slAct (slT (3 * t)) p) = Φ p := by
    intro t p hp
    simp only [hΦ]
    rw [hu _ (slT_mem_Gam3 (dvd_mul_right 3 t)) p hp]
    dsimp only
    rw [kub_slT, one_mul, slAct_slT]
    simp only
    rw [show σO (δ3 * x) * (p.1 + σO (3 * t)) / 9 =
        σO (δ3 * x) * p.1 / 9 + σO (δ3 * x) * σO (3 * t) / 9 by ring, ebr_add, ebr_period, mul_one]
  have hfinH : ∫⁻ q, rhoH q * ‖Φ q‖ₑ ∂uhsMeasure ≠ ⊤ := by
    rw [lintegral_rhoH_eq hΦm.enorm fun t p hp => by rw [hper t p hp]]
    exact hfin
  have h1 : ∫ p, conj (pmSer (δ3 * x) ψ p) * u p ∂(muR rhoG) =
      ∫ p, ∑' cd : BRowT, Φ (slAct (gamRow cd) p) ∂(muR rhoG) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_muR_UHS rhoG] with p hp
    exact conj_pmSer_mul hu _ ψ hp
  rw [h1, integral_unfold_family gamRow isPU_rhoG.1 measurable_rhoH (fun q _ => rfl)
    (fun q hq => lt_of_le_of_lt (isPU_rhoG.le_one hq) ENNReal.one_lt_top)
    (fun q hq => lt_of_le_of_lt (rhoH_le_one hq) ENNReal.one_lt_top) hΦm hfinH,
    integral_rhoH_eq hΦm hper hfin, muR_rhoT3]

/-- **The pairing in `L²(ν)`**: `⟨P_m(ψ), u⟩ = ∫_{3P×(0,∞)} conj(ψ(v)·ĕ(mz/9))·u(z, v) dz dv/v³`. -/
theorem inner_toLp_pmSer {x : 𝓞 K} {ψ : ℝ → ℂ} (hψ : Measurable ψ)
    (hψ2 : MemLp (pmSer (δ3 * x) ψ) 2 (muR rhoG)) {u : ℂ × ℝ → ℂ}
    (hu : IsAut Gam3 (fun g => kub ↑g) u) (hum : Measurable u) (hu2 : MemLp u 2 (muR rhoG))
    (hfin : ∫⁻ p, rhoT3 p * ‖conj (ψ p.2 * ebr (σO (δ3 * x) * p.1 / 9)) * u p‖ₑ ∂uhsMeasure ≠ ⊤) :
    inner ℂ (hψ2.toLp (pmSer (δ3 * x) ψ)) (hu2.toLp u) =
      ∫ p in Prod.fst ⁻¹' fundP3, conj (ψ p.2 * ebr (σO (δ3 * x) * p.1 / 9)) * u p ∂uhsMeasure := by
  rw [L2.inner_def, ← integral_conj_pmSer_mul hψ hu hum hfin]
  refine integral_congr_ae ?_
  filter_upwards [hψ2.coeFn_toLp, hu2.coeFn_toLp] with p h1 h2
  rw [RCLike.inner_apply', h1, h2]

end Eis

end

#print axioms Eis.gamRow_mul_eq
#print axioms Eis.kub_mul_conj_kub
#print axioms Eis.pmTerm_slAct
#print axioms Eis.isAut_pmSer
#print axioms Eis.measurable_pmTerm
#print axioms Eis.measurable_pmSer
#print axioms Eis.norm_pmTerm
#print axioms Eis.rowsZ_finite
#print axioms Eis.tsum_enorm_psTerm_slAct_le
#print axioms Eis.tsum_enorm_pmTerm_eq
#print axioms Eis.memLp_pmSer
#print axioms Eis.memLp_pmSer_Icc
#print axioms Eis.conj_pmTerm_mul
#print axioms Eis.conj_pmSer_mul
#print axioms Eis.integral_conj_pmSer_mul
#print axioms Eis.inner_toLp_pmSer
