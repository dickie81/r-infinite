import KubotaBallOp

/-! # The ball operator through its kernel, and on automorphic functions (round 422)

S5f-10 of round 360's plan, part 5 (S5f-10b, second half, third part). Round 421 built the self-adjoint
operator `K` on `L²(ν)`, `ν = ρ dμ`, from its form. This round identifies it pointwise: `Kf` is the kernel
integral `∫k(·, q)f(q) dν(q)`, and on a function automorphic with the character `χ` it is the ball average
`T_R` of round 418.

* **The Schur bound in its `L²` form** (**`lintegral_sq_cntB_le`**, with `sq_lintegral_cntB_le`):
  `(∫N(p, q)b(q) dν)² ≤ V_R·∫N(p, q)b(q)² dν` by Cauchy–Schwarz in `q`, so
  `∫(∫N(p, q)b(q) dν(q))² dν(p) ≤ V_R²∫b² dν`.
* **The kernel representation** (`kfun`, a definition; **`ballOp_ae_eq_kfun`**, with
  `lintegral_enorm_sq_lt_top`, `aestronglyMeasurable_kfun`, `enorm_kfun_le`, `memLp_kfun`, `inner_toLp_kfun`
  and `ballOp_eq_toLp_kfun`): `p ↦ ∫k(p, q)f(q) dν(q)` is in `L²(ν)`, its inner product with `g` is round
  421's form `B(f, g)` by Fubini (Mathlib's `integral_prod`), and so it is `Kf`.
* **Automorphic functions** (`IsAut`, a definition; **`kfun_eq_bavg`** and **`ballOp_toLp_ae_eq_bavg`**,
  with `IsPU.le_one`, `tsum_toReal_rho_inv`, `IsAut.enorm`, `lintegral_hball_enorm`, `conj_mul_self_of_uchar`
  and `lintegral_enorm_sq_lt_top_of_memLp`): for `u(γq) = χ(γ)u(q)`, `∫k(p, q)u(q) dν(q) = ∫_{B_R(p)} u dμ`
  whenever `∫N(p, q)|u(q)| dν(q) < ∞`. The proof exchanges the sum over `Γ` with the integral, moves each
  term by `γ⁻¹` (round 383's `integral_actP`), and sums `Σ_γ ρ(γ⁻¹q) = 1` (round 386's `IsPU.tsum_inv`).
  For `u` in `L²(ν)` the finiteness holds almost everywhere by the `L²` Schur bound, so `Ku = T_Ru` almost
  everywhere.
-/

open MeasureTheory Set Filter NumberField
open scoped ENNReal ComplexConjugate MatrixGroups InnerProductSpace

noncomputable section

namespace Eis

variable {Γ : Subgroup SL(2, 𝓞 K)} {χ : SL(2, 𝓞 K) → ℂ} {ρ : ℂ × ℝ → ℝ≥0∞}

/-! ### The Schur bound in its `L²` form -/

/-- **Cauchy–Schwarz in `q`**: `(∫N(p, q)b(q) dν)² ≤ V_R·∫N(p, q)b(q)² dν` for `p` in upper half-space. -/
theorem sq_lintegral_cntB_le (hρ : IsPU Γ ρ) (R : ℝ) {p : ℂ × ℝ} (hp : p ∈ UHS)
    {b : ℂ × ℝ → ℝ≥0∞} (hb : Measurable b) :
    (∫⁻ q, cntB Γ R p q * b q ∂(muR ρ)) ^ 2 ≤ VB R * ∫⁻ q, cntB Γ R p q * b q ^ 2 ∂(muR ρ) := by
  set μp := (muR ρ).withDensity (fun q => cntB Γ R p q) with hμp
  have hN := measurable_cntB_left Γ R p
  have h1 : ∫⁻ q, cntB Γ R p q * b q ∂(muR ρ) =
      ∫⁻ q, ((fun _ : ℂ × ℝ => (1 : ℝ≥0∞)) * b) q ∂μp := by
    rw [hμp, lintegral_withDensity_eq_lintegral_mul _ hN (measurable_const.mul hb)]
    refine lintegral_congr fun q => ?_
    simp only [Pi.mul_apply, one_mul]
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μp Real.HolderConjugate.two_two
    (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable hb.aemeasurable
  have h3 : ∫⁻ q, (fun _ : ℂ × ℝ => (1 : ℝ≥0∞)) q ^ (2 : ℝ) ∂μp = VB R := by
    simp only [ENNReal.one_rpow]
    rw [hμp, lintegral_withDensity_eq_lintegral_mul _ hN measurable_const]
    simp only [Pi.mul_apply, mul_one]
    exact lintegral_cntB_muR hρ R hp
  have h4 : ∫⁻ q, b q ^ (2 : ℝ) ∂μp = ∫⁻ q, cntB Γ R p q * b q ^ 2 ∂(muR ρ) := by
    simp only [ENNReal.rpow_two]
    rw [hμp, lintegral_withDensity_eq_lintegral_mul _ hN (hb.pow_const 2)]
    rfl
  rw [h1]
  calc (∫⁻ q, ((fun _ : ℂ × ℝ => (1 : ℝ≥0∞)) * b) q ∂μp) ^ 2
      ≤ ((∫⁻ q, (fun _ : ℂ × ℝ => (1 : ℝ≥0∞)) q ^ (2 : ℝ) ∂μp) ^ (1 / 2 : ℝ) *
          (∫⁻ q, b q ^ (2 : ℝ) ∂μp) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ zero_le h2 2
    _ = VB R * ∫⁻ q, cntB Γ R p q * b q ^ 2 ∂(muR ρ) := by
        rw [h3, h4, mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

/-- **The Schur bound in `L²` form**: `∫(∫N(p, q)b(q) dν(q))² dν(p) ≤ V_R²·∫b² dν`. -/
theorem lintegral_sq_cntB_le (hρ : IsPU Γ ρ) (R : ℝ) {b : ℂ × ℝ → ℝ≥0∞} (hb : Measurable b) :
    ∫⁻ p, (∫⁻ q, cntB Γ R p q * b q ∂(muR ρ)) ^ 2 ∂(muR ρ) ≤
      VB R ^ 2 * ∫⁻ q, b q ^ 2 ∂(muR ρ) := by
  have hF : Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) => cntB Γ R x.1 x.2 * b x.2 ^ 2 :=
    (measurable_cntB Γ R).mul ((hb.pow_const 2).comp measurable_snd)
  have hm : Measurable fun p => ∫⁻ q, cntB Γ R p q * b q ^ 2 ∂(muR ρ) := hF.lintegral_prod_right'
  calc ∫⁻ p, (∫⁻ q, cntB Γ R p q * b q ∂(muR ρ)) ^ 2 ∂(muR ρ)
      ≤ ∫⁻ p, VB R * ∫⁻ q, cntB Γ R p q * b q ^ 2 ∂(muR ρ) ∂(muR ρ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_muR_UHS ρ] with p hp
        exact sq_lintegral_cntB_le hρ R hp hb
    _ = VB R * ∫⁻ q, ∫⁻ p, cntB Γ R p q * b q ^ 2 ∂(muR ρ) ∂(muR ρ) := by
        rw [lintegral_const_mul _ hm, lintegral_lintegral_swap hF.aemeasurable]
    _ = VB R * ∫⁻ q, VB R * b q ^ 2 ∂(muR ρ) := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [ae_muR_UHS ρ] with q hq
        rw [lintegral_mul_const _ (measurable_cntB_right Γ R q), lintegral_cntB_muR' hρ R hq]
    _ = VB R ^ 2 * ∫⁻ q, b q ^ 2 ∂(muR ρ) := by
        rw [lintegral_const_mul _ (hb.pow_const 2), ← mul_assoc, sq]

/-! ### The kernel representation -/

theorem lintegral_enorm_sq_lt_top (f : Lp ℂ 2 (muR ρ)) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(muR ρ) < ⊤ := by
  have h := Lp.eLpNorm_lt_top f
  rw [← lintegral_enorm_sq_rpow] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

/-- `(Kf)(p) = ∫k(p, q)f(q) dν(q)`, pointwise. -/
def kfun (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) (R : ℝ) (ρ : ℂ × ℝ → ℝ≥0∞)
    (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  ∫ q, bker Γ χ R p q * f q ∂(muR ρ)

theorem aestronglyMeasurable_kfun (R : ℝ) (f : Lp ℂ 2 (muR ρ)) :
    AEStronglyMeasurable (kfun Γ χ R ρ f) (muR ρ) := by
  have h : AEStronglyMeasurable (fun x : (ℂ × ℝ) × (ℂ × ℝ) => bker Γ χ R x.1 x.2 * f x.2)
      ((muR ρ).prod (muR ρ)) :=
    ((measurable_bker Γ χ R).mul
      ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).aestronglyMeasurable
  exact h.integral_prod_right'

/-- `|(Kf)(p)| ≤ ∫N(p, q)|f(q)| dν(q)`. -/
theorem enorm_kfun_le (hχ : IsUChar Γ χ) (R : ℝ) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) :
    ‖kfun Γ χ R ρ f p‖ₑ ≤ ∫⁻ q, cntB Γ R p q * ‖f q‖ₑ ∂(muR ρ) := by
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun q => ?_)
  rw [enorm_mul]
  gcongr
  exact enorm_bker_le hχ R p q

/-- The kernel function of an `L²` element is in `L²`. -/
theorem memLp_kfun (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ} (hR : 0 ≤ R)
    (f : Lp ℂ 2 (muR ρ)) : MemLp (kfun Γ χ R ρ f) 2 (muR ρ) := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (aestronglyMeasurable_kfun R f)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  calc ∫⁻ p, ‖kfun Γ χ R ρ f p‖ₑ ^ 2 ∂(muR ρ)
      ≤ ∫⁻ p, (∫⁻ q, cntB Γ R p q * ‖f q‖ₑ ∂(muR ρ)) ^ 2 ∂(muR ρ) :=
        lintegral_mono fun p => pow_le_pow_left₀ zero_le (enorm_kfun_le hχ R f p) 2
    _ ≤ VB R ^ 2 * ∫⁻ q, ‖f q‖ₑ ^ 2 ∂(muR ρ) :=
        lintegral_sq_cntB_le hρ R (Lp.stronglyMeasurable f).measurable.enorm
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top (uhsMeasure_hball_lt_top hR))
        (lintegral_enorm_sq_lt_top f)

/-- `⟪kfun f, g⟫ = B(f, g)`, by Fubini (Mathlib's `integral_prod`). -/
theorem inner_toLp_kfun (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ} (hR : 0 ≤ R)
    (f g : Lp ℂ 2 (muR ρ)) :
    ⟪(memLp_kfun hρ hχ hR f).toLp (kfun Γ χ R ρ f), g⟫_ℂ = bform Γ χ R f g := by
  rw [L2.inner_def]
  have hae := (memLp_kfun hρ hχ hR f).coeFn_toLp
  calc ∫ p, ⟪(memLp_kfun hρ hχ hR f).toLp (kfun Γ χ R ρ f) p, g p⟫_ℂ ∂(muR ρ)
      = ∫ p, conj (kfun Γ χ R ρ f p) * g p ∂(muR ρ) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with p hp
        rw [RCLike.inner_apply', hp]
    _ = ∫ p, ∫ q, bformF Γ χ R f g (p, q) ∂(muR ρ) ∂(muR ρ) := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [kfun, bformF]
        rw [← integral_conj, ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun q => ?_)
        simp only [map_mul]
        ring
    _ = bform Γ χ R f g := (integral_prod _ (integrable_bformF hρ hχ hR f g)).symm

/-- **The kernel representation**: `K f = ∫k(·, q)f(q) dν(q)` in `L²`. -/
theorem ballOp_eq_toLp_kfun (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ} (hR : 0 ≤ R)
    (f : Lp ℂ 2 (muR ρ)) :
    ballOp hρ hχ hR f = (memLp_kfun hρ hχ hR f).toLp (kfun Γ χ R ρ f) := by
  refine ext_inner_right ℂ fun g => ?_
  rw [inner_ballOp, inner_toLp_kfun hρ hχ hR]

theorem ballOp_ae_eq_kfun (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ} (hR : 0 ≤ R)
    (f : Lp ℂ 2 (muR ρ)) : ballOp hρ hχ hR f =ᵐ[muR ρ] kfun Γ χ R ρ f := by
  rw [ballOp_eq_toLp_kfun]
  exact (memLp_kfun hρ hχ hR f).coeFn_toLp

/-! ### Automorphic functions -/

/-- `u(γq) = χ(γ)u(q)` for `γ ∈ Γ` and `q` in upper half-space. -/
def IsAut (Γ : Subgroup SL(2, 𝓞 K)) (χ : SL(2, 𝓞 K) → ℂ) (u : ℂ × ℝ → ℂ) : Prop :=
  ∀ γ ∈ Γ, ∀ q ∈ UHS, u (slAct γ q) = χ γ * u q

theorem IsPU.le_one (hρ : IsPU Γ ρ) {p : ℂ × ℝ} (hp : p ∈ UHS) : ρ p ≤ 1 := by
  calc ρ p = ρ (slAct ((1 : Γ) : SL(2, 𝓞 K)) p) := by rw [Subgroup.coe_one, slAct_one]
    _ ≤ ∑' γ : Γ, ρ (slAct γ p) := ENNReal.le_tsum (f := fun γ : Γ => ρ (slAct γ p)) 1
    _ = 1 := hρ.2 p hp

theorem tsum_toReal_rho_inv (hρ : IsPU Γ ρ) {q : ℂ × ℝ} (hq : q ∈ UHS) :
    ∑' γ : Γ, (ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q)).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq fun γ => ne_top_of_le_ne_top ENNReal.one_ne_top
    (hρ.le_one (slAct_mem _ hq)), hρ.tsum_inv hq, ENNReal.toReal_one]

theorem IsAut.enorm (hχ : IsUChar Γ χ) {u : ℂ × ℝ → ℂ} (hu : IsAut Γ χ u) {γ : SL(2, 𝓞 K)}
    (hγ : γ ∈ Γ) {q : ℂ × ℝ} (hq : q ∈ UHS) : ‖u (slAct γ q)‖ₑ = ‖u q‖ₑ := by
  rw [hu γ hγ q hq, enorm_mul, ← ofReal_norm, hχ.norm_eq γ hγ, ENNReal.ofReal_one, one_mul]

/-- **Unfolding `|u|` over the ball**: `∫_{B_R(p)}|u| dμ = ∫N(p, q)|u(q)| dν(q)`. -/
theorem lintegral_hball_enorm (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) (R : ℝ) {u : ℂ × ℝ → ℂ}
    (hu : IsAut Γ χ u) (hum : Measurable u) (p : ℂ × ℝ) :
    ∫⁻ q, (hball R p).indicator (fun q => ‖u q‖ₑ) q ∂uhsMeasure =
      ∫⁻ q, cntB Γ R p q * ‖u q‖ₑ ∂(muR ρ) := by
  have hB := measurableSet_hball R p
  have hm : Measurable fun q => cntB Γ R p q * ‖u q‖ₑ := (measurable_cntB_left Γ R p).mul hum.enorm
  rw [muR, lintegral_withDensity_eq_lintegral_mul _ hρ.1 hm]
  have e : ∀ q, (ρ * fun q => cntB Γ R p q * ‖u q‖ₑ) q =
      ρ q * ∑' γ : Γ, (hball R p).indicator 1 (slAct γ q) * ‖u q‖ₑ := by
    intro q
    simp only [Pi.mul_apply, cntB, ENNReal.tsum_mul_right]
  simp_rw [e]
  refine (lintegral_unfold hρ (Φ := fun γ q => (hball R p).indicator 1 (slAct γ q) * ‖u q‖ₑ)
    (Ψ := (hball R p).indicator fun q => ‖u q‖ₑ)
    (fun γ => ((measurable_one.indicator hB).comp (measurable_slAct _)).mul hum.enorm)
    (hum.enorm.indicator hB) (fun γ q hq => ?_)).symm
  simp only [Subgroup.coe_inv, slAct_slAct_inv _ hq]
  rw [IsAut.enorm hχ hu (Γ.inv_mem γ.2) hq]
  by_cases h : q ∈ hball R p
  · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

theorem conj_mul_self_of_uchar (hχ : IsUChar Γ χ) {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Γ) :
    χ γ * conj (χ γ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.norm_eq γ hγ]; simp

/-- **The kernel on automorphic functions**: `∫k(p, q)u(q) dν(q) = ∫_{B_R(p)} u dμ` when
`∫N(p, q)|u(q)| dν(q) < ∞`, by unfolding over `Γ`. -/
theorem kfun_eq_bavg (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) (R : ℝ) {u : ℂ × ℝ → ℂ}
    (hu : IsAut Γ χ u) (hum : Measurable u) {p : ℂ × ℝ}
    (hfin : ∫⁻ q, cntB Γ R p q * ‖u q‖ₑ ∂(muR ρ) ≠ ⊤) :
    kfun Γ χ R ρ u p = bavg R u p := by
  set B := hball R p with hBdef
  have hB : MeasurableSet B := measurableSet_hball R p
  have hind : ∀ γ : SL(2, 𝓞 K), Measurable fun q => B.indicator (1 : ℂ × ℝ → ℂ) (slAct γ q) :=
    fun γ => (measurable_one.indicator hB).comp (measurable_slAct γ)
  set F : Γ → ℂ × ℝ → ℂ := fun γ q => χ γ * B.indicator 1 (slAct γ q) * u q with hFdef
  have hFm : ∀ γ, Measurable (F γ) := fun γ => (measurable_const.mul (hind γ)).mul hum
  have hFe : ∀ γ q, ‖F γ q‖ₑ = B.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ q) * ‖u q‖ₑ := by
    intro γ q
    simp only [hFdef, enorm_mul]
    rw [← ofReal_norm, hχ.norm_eq γ γ.2, ENNReal.ofReal_one, one_mul]
    by_cases h : slAct (γ : SL(2, 𝓞 K)) q ∈ B
    · rw [indicator_of_mem h, indicator_of_mem h]; simp
    · rw [indicator_of_notMem h, indicator_of_notMem h]; simp
  have hsum : ∑' γ : Γ, ∫⁻ q, ‖F γ q‖ₑ ∂(muR ρ) ≠ ⊤ := by
    simp_rw [hFe]
    have e : ∑' γ : Γ, ∫⁻ q, B.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ q) * ‖u q‖ₑ ∂(muR ρ) =
        ∫⁻ q, ∑' γ : Γ, B.indicator (1 : ℂ × ℝ → ℝ≥0∞) (slAct γ q) * ‖u q‖ₑ ∂(muR ρ) :=
      (lintegral_tsum fun γ => (((measurable_one.indicator hB).comp
        (measurable_slAct _)).mul hum.enorm).aemeasurable).symm
    rw [e]
    simp_rw [ENNReal.tsum_mul_right]
    exact hfin
  have h1 : kfun Γ χ R ρ u p = ∑' γ : Γ, ∫ q, F γ q ∂(muR ρ) := by
    rw [← integral_tsum (fun γ => (hFm γ).aestronglyMeasurable) hsum]
    unfold kfun bker
    congr 1
    funext q
    rw [tsum_mul_right]
  have hρfin : ∀ᵐ q ∂uhsMeasure, ρ q < ⊤ := by
    filter_upwards [ae_UHS] with q hq
    exact lt_of_le_of_lt (hρ.le_one hq) ENNReal.one_lt_top
  set G : Γ → ℂ × ℝ → ℂ := fun γ q =>
    (ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q)).toReal • B.indicator u q with hGdef
  have hGm : ∀ γ, Measurable (G γ) := fun γ =>
    ((hρ.1.comp (measurable_slAct _)).ennreal_toReal).smul (hum.indicator hB)
  have h3 : ∀ γ : Γ, ∫ q, F γ q ∂(muR ρ) = ∫ q, G γ q ∂uhsMeasure := by
    intro γ
    rw [muR, integral_withDensity_eq_integral_toReal_smul hρ.1 hρfin]
    have hH : AEStronglyMeasurable (fun q => (ρ q).toReal • F γ q) uhsMeasure :=
      (hρ.1.ennreal_toReal.smul (hFm γ)).aestronglyMeasurable
    rw [← integral_actP (det_map_σO ((γ⁻¹ : Γ) : SL(2, 𝓞 K)).2) hH]
    refine integral_congr_ae ?_
    filter_upwards [ae_UHS] with q hq
    change (ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q)).toReal •
        F γ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q) = G γ q
    simp only [hGdef, hFdef]
    congr 1
    rw [Subgroup.coe_inv, slAct_slAct_inv _ hq, hu _ (Γ.inv_mem γ.2) q hq, hχ.map_inv γ.2]
    have hn := conj_mul_self_of_uchar hχ γ.2
    by_cases h : q ∈ B
    · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply]
      linear_combination u q * hn
    · rw [indicator_of_notMem h, indicator_of_notMem h]; ring
  have hsum2 : ∑' γ : Γ, ∫⁻ q, ‖G γ q‖ₑ ∂uhsMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun γ => lintegral_mono fun q =>
      (show ‖G γ q‖ₑ ≤ ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q) * ‖B.indicator u q‖ₑ from ?_))
    · have e0 : ∑' γ : Γ, ∫⁻ q, ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q) * ‖B.indicator u q‖ₑ
            ∂uhsMeasure = ∫⁻ q, ∑' γ : Γ, ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q) *
              ‖B.indicator u q‖ₑ ∂uhsMeasure :=
        (lintegral_tsum fun γ => ((hρ.1.comp (measurable_slAct _)).mul
          (hum.indicator hB).enorm).aemeasurable).symm
      rw [e0]
      simp_rw [ENNReal.tsum_mul_right]
      have e : ∫⁻ q, (∑' γ : Γ, ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q)) * ‖B.indicator u q‖ₑ
          ∂uhsMeasure = ∫⁻ q, B.indicator (fun q => ‖u q‖ₑ) q ∂uhsMeasure := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_UHS] with q hq
        rw [hρ.tsum_inv hq, one_mul, enorm_indicator_eq_indicator_enorm]
      rw [e, lintegral_hball_enorm hρ hχ R hu hum p]
      exact hfin
    · simp only [hGdef, enorm_smul]
      gcongr
      rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
  rw [h1]
  simp_rw [h3]
  rw [← integral_tsum (fun γ => (hGm γ).aestronglyMeasurable) hsum2, bavg,
    ← integral_indicator hB]
  refine integral_congr_ae ?_
  filter_upwards [ae_UHS] with q hq
  have hs : Summable fun γ : Γ => (ρ (slAct ((γ⁻¹ : Γ) : SL(2, 𝓞 K)) q)).toReal :=
    ENNReal.summable_toReal (by rw [hρ.tsum_inv hq]; exact ENNReal.one_ne_top)
  simp only [hGdef]
  rw [hs.tsum_smul_const, tsum_toReal_rho_inv hρ hq, one_smul]

/-- `∫|u|² dν < ∞` for `u` in `L²(ν)`. -/
theorem lintegral_enorm_sq_lt_top_of_memLp {u : ℂ × ℝ → ℂ} (hum : Measurable u)
    (hu2 : MemLp u 2 (muR ρ)) : ∫⁻ q, ‖u q‖ₑ ^ 2 ∂(muR ρ) < ⊤ := by
  have h := hu2
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hum.aestronglyMeasurable] at h
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

/-- **`K` is `T_R` on automorphic functions**: for `u` automorphic with `∫ρ|u|² < ∞`,
`Ku = ∫_{B_R(·)} u dμ` almost everywhere. -/
theorem ballOp_toLp_ae_eq_bavg (hρ : IsPU Γ ρ) (hχ : IsUChar Γ χ) {R : ℝ} (hR : 0 ≤ R)
    {u : ℂ × ℝ → ℂ} (hu : IsAut Γ χ u) (hum : Measurable u) (hu2 : MemLp u 2 (muR ρ)) :
    ballOp hρ hχ hR (hu2.toLp u) =ᵐ[muR ρ] bavg R u := by
  have h1 := ballOp_ae_eq_kfun hρ hχ hR (hu2.toLp u)
  have h2 : ∀ p, kfun Γ χ R ρ (hu2.toLp u) p = kfun Γ χ R ρ u p := by
    intro p
    unfold kfun
    refine integral_congr_ae ?_
    filter_upwards [hu2.coeFn_toLp] with q hq
    rw [hq]
  have hF : Measurable fun x : (ℂ × ℝ) × (ℂ × ℝ) => cntB Γ R x.1 x.2 * ‖u x.2‖ₑ :=
    (measurable_cntB Γ R).mul (hum.enorm.comp measurable_snd)
  have hm : Measurable fun p => ∫⁻ q, cntB Γ R p q * ‖u q‖ₑ ∂(muR ρ) := hF.lintegral_prod_right'
  have hfin : ∀ᵐ p ∂(muR ρ), ∫⁻ q, cntB Γ R p q * ‖u q‖ₑ ∂(muR ρ) ≠ ⊤ := by
    have hlt : ∫⁻ p, (∫⁻ q, cntB Γ R p q * ‖u q‖ₑ ∂(muR ρ)) ^ 2 ∂(muR ρ) < ⊤ :=
      lt_of_le_of_lt (lintegral_sq_cntB_le hρ R hum.enorm)
        (ENNReal.mul_lt_top (ENNReal.pow_lt_top (uhsMeasure_hball_lt_top hR))
          (lintegral_enorm_sq_lt_top_of_memLp hum hu2))
    filter_upwards [ae_lt_top' (hm.pow_const 2).aemeasurable hlt.ne] with p hp h
    rw [h, ENNReal.top_pow two_ne_zero] at hp
    exact lt_irrefl _ hp
  filter_upwards [h1, hfin] with p hp1 hp2
  rw [hp1, h2, kfun_eq_bavg hρ hχ R hu hum hp2]

end Eis

end

#print axioms Eis.sq_lintegral_cntB_le
#print axioms Eis.lintegral_sq_cntB_le
#print axioms Eis.lintegral_enorm_sq_lt_top
#print axioms Eis.aestronglyMeasurable_kfun
#print axioms Eis.enorm_kfun_le
#print axioms Eis.memLp_kfun
#print axioms Eis.inner_toLp_kfun
#print axioms Eis.ballOp_eq_toLp_kfun
#print axioms Eis.ballOp_ae_eq_kfun
#print axioms Eis.IsPU.le_one
#print axioms Eis.tsum_toReal_rho_inv
#print axioms Eis.IsAut.enorm
#print axioms Eis.lintegral_hball_enorm
#print axioms Eis.conj_mul_self_of_uchar
#print axioms Eis.kfun_eq_bavg
#print axioms Eis.lintegral_enorm_sq_lt_top_of_memLp
#print axioms Eis.ballOp_toLp_ae_eq_bavg
