import KubotaCubeCover

/-! # The traces and the cube eigenrelation (round 448)

S5f-12 of round 360's plan, part 9. Round 447's next step planned the data of round 439's `translates_eq_zero`
for `D = N(p)⁻³Σ_{q mod p³} θ̃∘M_q − N(p)⁻¹θ̃`, the constant terms of the traces, and then `D = 0` almost
everywhere and the eigenrelation at every point for θ's Fourier series `thS` (round 436). This round proves
them, for a primary prime `p`:

* **Almost every height** (`ae_Ioi_comp_mul`): a property of almost every `w > 0` holds at `cv` for almost
  every `v > 0`, for `c > 0`.
* **Slices** (`integrableOn_fundP3_of_mul`, `integrable_cubeDiff_slAct` and `integrable_cubeDiff_inv_slAct`):
  a measurable function periodic under `3ℤ[ω]` is integrable on `3P` when `z ↦ f(μz)` is (round 444's
  `lintegral_fundP3_mul`), and `D∘γ` and `D∘M_q⁻¹∘γ` are integrable along the affine images of `3P` on which
  round 446's `integral_cubeDiff_slAct` and `integral_cubeDiff_inv_slAct` compute their means.
* **The translates** (`cubeG`, `cubeC`, `cubeH` and `cubeE`, definitions, with `det_cubeG`, `cubeH_le`,
  `finite_cubeH`, `slAct_cubeE`, `kub_cubeE` and `sum_cubeC`): indexed by `Option (ℤ[ω]/p³)`, `I` with
  coefficient `−N(p)⁻¹`, the group `Γ(3p³)` and the identity, and `M_q` with coefficient `N(p)⁻³`, the group
  `Γ′(p)` and `γ ↦ M_qγM_q⁻¹` (round 447). Their combination is `D`.
* **The traces** (**`integral_trace_cube`**): at a height `v > 0` where θ̃ has its constant term at `v`, at
  `|p|^{2k−3}v` and at `|p|^{2k−3}|p|^{2j−3}v` for `j, k ≤ 3`, the trace of `D∘g⁻¹` to `Γ_1(3)` has constant
  term `0` at `v`, for each translate `g`.
* **The eigenrelation almost everywhere** (`ae_good_heights`; **`cubeDiff_ae_eq_zero`**): almost every height
  is such a height (round 433's `const_thetaF_ae`), so `D = 0` almost everywhere on upper half-space.
* **The eigenrelation at every point** (`continuousOn_actP`, `ae_uhs_thetaF_eq_thS` and
  `ae_thetaF_eq_thS_actP`; **`thS_cube_eigen`** and **`thS_cube_eigen_coord`**):
  `N(p)⁻³Σ_{q mod p³} thS((z + 3q)/p³, v/|p|³) = N(p)⁻¹·thS(z, v)` for every `z ∈ ℂ` and `v > 0`. θ̃ equals
  `thS` almost everywhere (round 437's `ae_thetaF_eq_thS`), and so do their compositions with each `M_q`
  (round 383's `measurePreserving_actP`); both sides are continuous on upper half-space (round 436's
  `continuousOn_thS`), and continuous functions equal almost everywhere on an open set are equal there
  (Mathlib's `Measure.eqOn_open_of_ae_eq`).
-/

open Ideal NumberField MeasureTheory Set
open scoped BigOperators MatrixGroups ComplexConjugate ENNReal

noncomputable section

namespace Eis

/-! ### Almost every height -/

/-- **Scaling keeps almost every height**: a property of almost every `w > 0` holds at `cv` for almost every
`v > 0`, for `c > 0`. -/
theorem ae_Ioi_comp_mul {P : ℝ → Prop} (h : ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))), P w) {c : ℝ}
    (hc : 0 < c) : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), P (c * v) := by
  rw [ae_restrict_iff' measurableSet_Ioi] at h ⊢
  have hq : Measure.QuasiMeasurePreserving (fun v : ℝ => c * v) volume volume :=
    ⟨measurable_const_mul c, by
      rw [Real.map_volume_mul_left hc.ne']
      exact Measure.smul_absolutelyContinuous⟩
  filter_upwards [hq.ae h] with v hv hv0
  exact hv (mul_pos hc hv0)

/-! ### Slices -/

/-- **Integrability on `3P` from a scaled slice**: for `f` measurable and periodic under `3ℤ[ω]`, if
`z ↦ f(μz)` is integrable on `3P` then so is `f` (round 444's `lintegral_fundP3_mul`). -/
theorem integrableOn_fundP3_of_mul {f : ℂ → ℂ} (hf : Measurable f) (hper : ∀ z u, f (z + σO (3 * u)) = f z)
    {μ : 𝓞 K} (hμ : μ ≠ 0) (h : IntegrableOn (fun z => f (σO μ * z)) fundP3) : IntegrableOn f fundP3 := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  show ∫⁻ z in fundP3, ‖f z‖ₑ < ⊤
  rw [← lintegral_fundP3_mul (G := fun z => ‖f z‖ₑ) hf.enorm (fun z u => by simp only [hper]) hμ]
  exact h.2

/-- **`D∘γ` is integrable along an affine image of `3P`**, under the hypotheses of round 446's
`integral_cubeDiff_slAct`. -/
theorem integrable_cubeDiff_slAct {r : ℝ} {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) {μ : 𝓞 K} (hμ : μ ≠ 0) (hpμ : p ^ 3 ∣ μ) (t : ℂ) {w : ℝ} (hw : 0 < w)
    (hc0 : ∫ z in fundP3, thetaF r Y hY (z, w) = thetaCT w)
    (hc : ∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * w) =
      thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * w)) :
    Integrable (fun z => cubeDiff r Y hY p (slAct γ (σO μ * z + t, w))) (volume.restrict fundP3) := by
  classical
  have hp0 := hp.ne_zero
  have hσp : σO p ≠ 0 := σO_ne_zero hp0
  have hnp : 0 < ‖σO p‖ := norm_pos_iff.2 hσp
  obtain ⟨μ₀, rfl⟩ := hpμ
  have hμ₀ : μ₀ ≠ 0 := right_ne_zero_of_mul hμ
  have := finite_quot_pow3 hp0
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  have key : ∀ q : 𝓞 K ⧸ span {p ^ 3}, Integrable (fun z => thetaF r Y hY (actP (cubeMat p (repQ (p ^ 3) q))
      (slAct γ (σO (p ^ 3 * μ₀) * z + t, w)))) (volume.restrict fundP3) := by
    intro q
    obtain ⟨γ', hγ', -, t', hact⟩ := cubeMat_slAct hp hpp hγ (repQ (p ^ 3) q)
    set k := ordP3 p (γ 0 0 + 3 * γ 1 0 * repQ (p ^ 3) q) with hk
    have hk3 : k ≤ 3 := ordP3_le _ _
    have hh : 0 < ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 := by positivity
    have e : ∀ z : ℂ, thetaF r Y hY (actP (cubeMat p (repQ (p ^ 3) q))
        (slAct γ (σO (p ^ 3 * μ₀) * z + t, w))) =
        kub ↑γ' * thetaF r Y hY (σO (p ^ (2 * k) * μ₀) * z + (σO p ^ (2 * k) / σO p ^ 3 * t + t'),
          ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * w) := by
      intro z
      rw [hact _ hw, isAut_thetaF r Y hY γ' hγ' _ (show (0 : ℝ) < _ from mul_pos hh hw)]
      congr 2
      simp only [Prod.mk.injEq, and_true, map_mul, map_pow]
      field_simp
      ring
    have hint := integral_thetaF_affine hY (mul_pos hh hw) (hc k hk3)
      (mul_ne_zero (pow_ne_zero (2 * k) hp0) hμ₀) (σO p ^ (2 * k) / σO p ^ 3 * t + t')
    simp_rw [e]
    exact (Integrable.of_integral_ne_zero
      (by rw [hint]; exact const_theta_ne_zero (mul_pos hh hw))).const_mul _
  have e0 : ∀ z : ℂ, thetaF r Y hY (slAct γ (σO (p ^ 3 * μ₀) * z + t, w)) =
      kub ↑γ * thetaF r Y hY (σO (p ^ 3 * μ₀) * z + t, w) := fun z => isAut_thetaF r Y hY γ hγ _ hw
  have hint0 := integral_thetaF_affine hY hw hc0 hμ t
  have hi0 : Integrable (fun z => thetaF r Y hY (slAct γ (σO (p ^ 3 * μ₀) * z + t, w)))
      (volume.restrict fundP3) := by
    simp_rw [e0]
    exact (Integrable.of_integral_ne_zero (by rw [hint0]; exact const_theta_ne_zero hw)).const_mul _
  unfold cubeDiff
  simp_rw [tsum_fintype]
  exact ((integrable_finsetSum _ fun q _ => key q).const_mul _).sub (hi0.const_mul _)

/-- **`D∘M_q⁻¹∘γ` is integrable along an affine image of `3P`**, under the hypotheses of round 446's
`integral_cubeDiff_inv_slAct`. -/
theorem integrable_cubeDiff_inv_slAct {r : ℝ} {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) (q : 𝓞 K) {μ : 𝓞 K} (hμ : μ ≠ 0) (hpμ : p ^ 6 ∣ μ) (t : ℂ) {w : ℝ}
    (hw : 0 < w)
    (hc0 : ∀ j ≤ 3, ∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w) =
      thetaCT (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w))
    (hc : ∀ j ≤ 3, ∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY
        (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w)) =
      thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w))) :
    Integrable (fun z => cubeDiff r Y hY p (actP (cubeMat p q)⁻¹ (slAct γ (σO μ * z + t, w))))
      (volume.restrict fundP3) := by
  have hp0 := hp.ne_zero
  have hσp : σO p ≠ 0 := σO_ne_zero hp0
  have hnp : 0 < ‖σO p‖ := norm_pos_iff.2 hσp
  obtain ⟨μ₁, rfl⟩ := hpμ
  have hμ₁ : μ₁ ≠ 0 := right_ne_zero_of_mul hμ
  obtain ⟨γ', hγ', t', hact⟩ := cubeMat_inv_slAct hp hpp hγ q
  set m := ordP3 p (γ 1 0) with hm
  have hm3 : m ≤ 3 := ordP3_le _ _
  have hh : 0 < ‖σO p‖ ^ (2 * m) / ‖σO p‖ ^ 3 := by positivity
  have e : ∀ z : ℂ, actP (cubeMat p q)⁻¹ (slAct γ (σO (p ^ 6 * μ₁) * z + t, w)) =
      slAct γ' (σO (p ^ (2 * m + 3) * μ₁) * z + (σO p ^ (2 * m) / σO p ^ 3 * t + t'),
        ‖σO p‖ ^ (2 * m) / ‖σO p‖ ^ 3 * w) := by
    intro z
    rw [hact _ hw]
    congr 1
    simp only [Prod.mk.injEq, and_true, map_mul, map_pow]
    field_simp
    ring
  simp_rw [e]
  exact integrable_cubeDiff_slAct hY hp hpp hγ' (mul_ne_zero (pow_ne_zero _ hp0) hμ₁)
    (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) μ₁) _ (mul_pos hh hw) (hc0 m hm3) (hc m hm3)

/-! ### The translates -/

/-- The translates of round 439's principle for the cube difference: `I` and the `M_q`. -/
def cubeG (p : 𝓞 K) : Option (𝓞 K ⧸ span {p ^ 3}) → Matrix (Fin 2) (Fin 2) ℂ
  | none => 1
  | some q => cubeMat p (repQ (p ^ 3) q)

/-- Their coefficients, `−N(p)⁻¹` and `N(p)⁻³`. -/
def cubeC (p : 𝓞 K) : Option (𝓞 K ⧸ span {p ^ 3}) → ℂ
  | none => -(absNorm (span {p}) : ℂ)⁻¹
  | some _ => ((absNorm (span {p}) : ℂ) ^ 3)⁻¹

/-- Their groups, `Γ(3p³)` and `Γ′(p)`. -/
def cubeH (p : 𝓞 K) : Option (𝓞 K ⧸ span {p ^ 3}) → Subgroup SL(2, 𝓞 K)
  | none => gamPrin (3 * p ^ 3)
  | some _ => gamTw p

/-- Their equivalences, the identity and `γ ↦ M_qγM_q⁻¹`. -/
def cubeE {p : 𝓞 K} (hp : p ≠ 0) : ∀ i : Option (𝓞 K ⧸ span {p ^ 3}), gamPrin (3 * p ^ 3) ≃ cubeH p i
  | none => Equiv.refl _
  | some q => cubeEquiv hp (repQ (p ^ 3) q)

/-- The translates have determinant `1`. -/
theorem det_cubeG {p : 𝓞 K} (hp : p ≠ 0) (i : Option (𝓞 K ⧸ span {p ^ 3})) : (cubeG p i).det = 1 := by
  cases i with
  | none => exact Matrix.det_one
  | some q => exact det_cubeMat hp _

/-- The groups lie in `Γ_1(3)`. -/
theorem cubeH_le (p : 𝓞 K) (i : Option (𝓞 K ⧸ span {p ^ 3})) : cubeH p i ≤ Gam3 := by
  cases i with
  | none => exact gamPrin_le_Gam3 (dvd_mul_right 3 _)
  | some q => exact gamTw_le_Gam3 p

/-- The groups have finite index in `Γ_1(3)`. -/
theorem finite_cubeH {p : 𝓞 K} (hp : p ≠ 0) (i : Option (𝓞 K ⧸ span {p ^ 3})) :
    Finite (Gam3 ⧸ (cubeH p i).subgroupOf Gam3) := by
  cases i with
  | none => exact finite_quot_gamPrin hp
  | some q => exact finite_quot_gamTw hp

/-- The equivalences intertwine the translates. -/
theorem slAct_cubeE {p : 𝓞 K} (hp : p ≠ 0) (i : Option (𝓞 K ⧸ span {p ^ 3})) (γ : gamPrin (3 * p ^ 3))
    {P : ℂ × ℝ} (hP : P ∈ UHS) :
    slAct (cubeE hp i γ : SL(2, 𝓞 K)) (actP (cubeG p i) P) = actP (cubeG p i) (slAct (γ : SL(2, 𝓞 K)) P) := by
  cases i with
  | none =>
    show slAct (γ : SL(2, 𝓞 K)) (actP 1 P) = actP 1 (slAct (γ : SL(2, 𝓞 K)) P)
    rw [actP_one, actP_one]
  | some q => exact slAct_cubeEquiv hp _ γ hP

/-- The equivalences preserve `κ`. -/
theorem kub_cubeE {p : 𝓞 K} (hp : p ≠ 0) (i : Option (𝓞 K ⧸ span {p ^ 3})) (γ : gamPrin (3 * p ^ 3)) :
    kub ↑(cubeE hp i γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K)) := by
  cases i with
  | none => rfl
  | some q => exact kub_cubeEquiv hp _ γ

/-- **The combination of the translates is the cube difference.** -/
theorem sum_cubeC {r Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} [Fintype (𝓞 K ⧸ span {p ^ 3})] (Q : ℂ × ℝ) :
    ∑ j, cubeC p j * thetaF r Y hY (actP (cubeG p j) Q) = cubeDiff r Y hY p Q := by
  rw [Fintype.sum_option]
  simp only [cubeC, cubeG, actP_one]
  rw [cubeDiff, tsum_fintype, Finset.mul_sum]
  ring

/-! ### The traces -/

/-- **The constant terms of the traces vanish** at a height `v > 0` where θ̃ has its constant term at `v`, at
`|p|^{2k−3}v` and at `|p|^{2k−3}|p|^{2j−3}v` for `j, k ≤ 3`: the trace is periodic under `3ℤ[ω]` (round 439's
`isAut_trK`), so its mean over `3P` is unchanged by `z ↦ p⁶z` (round 444's `integral_fundP3_mul`), and then
each of its terms is a mean of `D∘δ` or `D∘M_q⁻¹∘δ` along an affine image of `3P`, which vanishes (round 446).
-/
theorem integral_trace_cube {r Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    [Fintype (𝓞 K ⧸ span {p ^ 3})] (i : Option (𝓞 K ⧸ span {p ^ 3})) {v : ℝ} (hv : 0 < v)
    (h0 : ∫ z in fundP3, thetaF r Y hY (z, v) = thetaCT v)
    (h1 : ∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * v) =
      thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * v))
    (h2 : ∀ j ≤ 3, ∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY
        (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v)) =
      thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v))) :
    ∫ z in fundP3, trK (cubeH p i)
      (fun P => ∑ j, cubeC p j * thetaF r Y hY (actP (cubeG p j) (actP (cubeG p i)⁻¹ P))) (z, v) = 0 := by
  classical
  have hp0 := hp.ne_zero
  have := finite_cubeH hp0 i
  have := Fintype.ofFinite (Gam3 ⧸ (cubeH p i).subgroupOf Gam3)
  set F : ℂ × ℝ → ℂ :=
    fun P => ∑ j, cubeC p j * thetaF r Y hY (actP (cubeG p j) (actP (cubeG p i)⁻¹ P)) with hFdef
  have hFeq : ∀ P, F P = cubeDiff r Y hY p (actP (cubeG p i)⁻¹ P) := fun P => sum_cubeC hY _
  have hD : IsAut (gamPrin (3 * p ^ 3)) (fun g => kub ↑g)
      (fun P => ∑ j, cubeC p j * thetaF r Y hY (actP (cubeG p j) P)) := by
    intro γ hγ P hP
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := isAut_comp_actP (det_cubeG hp0 j) (cubeE hp0 j) (fun γ P hP => slAct_cubeE hp0 j γ hP)
      (kub_cubeE hp0 j) (F := thetaF r Y hY)
      (fun γ hγ P hP => isAut_thetaF r Y hY γ (cubeH_le p j hγ) P hP) γ hγ P hP
    simp only at hj
    rw [hj]
    ring
  have hFaut : IsAut (cubeH p i) (fun g => kub ↑g) F :=
    isAut_comp_actP_inv (det_cubeG hp0 i) (cubeE hp0 i) (fun γ P hP => slAct_cubeE hp0 i γ hP)
      (kub_cubeE hp0 i) hD
  have hFm : Measurable F := Finset.measurable_sum _ fun j _ =>
    measurable_const.mul ((measurable_thetaF r Y hY).comp ((measurable_actP _).comp (measurable_actP _)))
  have hTrm : Measurable fun z : ℂ => trK (cubeH p i) F (z, v) :=
    (measurable_trK hFm).comp (measurable_id.prodMk measurable_const)
  have hper : ∀ z u, trK (cubeH p i) F (z + σO (3 * u), v) = trK (cubeH p i) F (z, v) := by
    intro z u
    have h := isAut_trK hFaut (slT (3 * u)) (slT_mem_Gam3 (dvd_mul_right 3 u)) (z, v) hv
    simp only [slAct_slT, kub_slT, one_mul] at h
    exact h
  have hterm : ∀ δ : SL(2, 𝓞 K), δ ∈ Gam3 →
      Integrable (fun z => F (slAct δ (σO (p ^ 6) * z, v))) (volume.restrict fundP3) ∧
        ∫ z in fundP3, F (slAct δ (σO (p ^ 6) * z, v)) = 0 := by
    intro δ hδ
    simp_rw [hFeq]
    cases i with
    | none =>
      simp only [cubeG, inv_one, actP_one]
      have hi := integrable_cubeDiff_slAct hY hp hpp hδ (pow_ne_zero 6 hp0) (pow_dvd_pow p (by norm_num)) 0 hv
        h0 h1
      have hz := integral_cubeDiff_slAct hY hp hpp hδ (pow_ne_zero 6 hp0) (pow_dvd_pow p (by norm_num)) 0 hv
        h0 h1
      simp only [add_zero] at hi hz
      exact ⟨hi, hz⟩
    | some q =>
      simp only [cubeG]
      have hi := integrable_cubeDiff_inv_slAct hY hp hpp hδ (repQ (p ^ 3) q) (pow_ne_zero 6 hp0) dvd_rfl 0 hv
        h1 h2
      have hz := integral_cubeDiff_inv_slAct hY hp hpp hδ (repQ (p ^ 3) q) (pow_ne_zero 6 hp0) dvd_rfl 0 hv
        h1 h2
      simp only [add_zero] at hi hz
      exact ⟨hi, hz⟩
  have hδ : ∀ q : Gam3 ⧸ (cubeH p i).subgroupOf Gam3, (q.out : SL(2, 𝓞 K))⁻¹ ∈ Gam3 :=
    fun q => Gam3.inv_mem q.out.2
  have hscaled : ∀ z, trK (cubeH p i) F (σO (p ^ 6) * z, v) = ∑ q : Gam3 ⧸ (cubeH p i).subgroupOf Gam3,
      conj (kub ↑((q.out : SL(2, 𝓞 K))⁻¹)) * F (slAct (q.out : SL(2, 𝓞 K))⁻¹ (σO (p ^ 6) * z, v)) :=
    fun z => by rw [trK, tsum_fintype]
  have hint_s : IntegrableOn (fun z => trK (cubeH p i) F (σO (p ^ 6) * z, v)) fundP3 := by
    simp_rw [hscaled]
    exact integrable_finsetSum _ fun q _ => (hterm _ (hδ q)).1.const_mul _
  have hint : IntegrableOn (fun z => trK (cubeH p i) F (z, v)) fundP3 :=
    integrableOn_fundP3_of_mul hTrm hper (pow_ne_zero 6 hp0) hint_s
  show ∫ z in fundP3, trK (cubeH p i) F (z, v) = 0
  rw [← integral_fundP3_mul (f := fun z => trK (cubeH p i) F (z, v)) hTrm hper (pow_ne_zero 6 hp0) hint]
  simp_rw [hscaled]
  rw [integral_finsetSum _ fun q _ => (hterm _ (hδ q)).1.const_mul _]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [integral_const_mul, (hterm _ (hδ q)).2, mul_zero]

/-! ### The eigenrelation -/

/-- **Almost every height is good**: for almost every `v > 0`, θ̃ has its constant term (round 433's
`const_thetaF_ae`) at `v`, at `|p|^{2k−3}v` and at `|p|^{2k−3}|p|^{2j−3}v` for `j, k ≤ 3`. -/
theorem ae_good_heights {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : p ≠ 0) :
    ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      (∫ z in fundP3, thetaF r Y hY (z, v) = thetaCT v) ∧
      (∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * v) =
        thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * v)) ∧
      (∀ j ≤ 3, ∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY
          (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v)) =
        thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v))) := by
  have hg : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∫ z in fundP3, thetaF r Y hY (z, v) = thetaCT v :=
    const_thetaF_ae hr hY
  have hnp : 0 < ‖σO p‖ := norm_pos_iff.2 (σO_ne_zero hp)
  have hpos : ∀ k : ℕ, 0 < ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 := fun k => by positivity
  have hA : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∀ k : ℕ, k ≤ 3 →
      ∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * v) =
        thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * v) :=
    ae_all_iff.2 fun k => (ae_Ioi_comp_mul hg (hpos k)).mono fun v hv _ => hv
  have hB : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∀ j : ℕ, j ≤ 3 → ∀ k : ℕ, k ≤ 3 →
      ∫ z in fundP3, thetaF r Y hY
          (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v)) =
        thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v)) := by
    refine ae_all_iff.2 fun j => ?_
    have hj : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), ∀ k : ℕ, k ≤ 3 →
        ∫ z in fundP3, thetaF r Y hY
            (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v)) =
          thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * v)) :=
      ae_all_iff.2 fun k => (ae_Ioi_comp_mul hg (mul_pos (hpos k) (hpos j))).mono fun v hv _ => by
        rwa [mul_assoc] at hv
    exact hj.mono fun v hv _ => hv
  exact hg.and (hA.and hB)

/-- **The cube eigenrelation almost everywhere**: for a primary prime `p`,
`N(p)⁻³Σ_{q mod p³} θ̃∘M_q = N(p)⁻¹θ̃` almost everywhere on upper half-space (round 439's
`translates_eq_zero` with the translates `I` and `M_q`). -/
theorem cubeDiff_ae_eq_zero {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p)
    (hpp : Primary p) : ∀ᵐ P ∂uhsMeasure, cubeDiff r Y hY p P = 0 := by
  classical
  have hp0 := hp.ne_zero
  have := finite_quot_pow3 hp0
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  have : ∀ i, Finite (Gam3 ⧸ (cubeH p i).subgroupOf Gam3) := finite_cubeH hp0
  have h := translates_eq_zero hr hY (gamPrin_le_Gam3 (dvd_mul_right 3 _)) (cubeG p) (det_cubeG hp0)
    (cubeH p) (cubeH_le p) (cubeE hp0) (fun i γ P hP => slAct_cubeE hp0 i γ hP) (kub_cubeE hp0) (cubeC p)
    fun i => (ae_good_heights hr hY hp0).mp ((ae_restrict_mem measurableSet_Ioi).mono fun v hv hgood =>
      integral_trace_cube hY hp hpp i hv hgood.1 hgood.2.1 hgood.2.2)
  filter_upwards [h] with P hP
  rwa [sum_cubeC] at hP

/-! ### At every point, for θ's Fourier series -/

/-- A matrix of determinant `1` acts continuously on upper half-space. -/
theorem continuousOn_actP {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) : ContinuousOn (actP g) UHS := by
  intro P hP
  have hD : 0 < uhsDen (g 1 0) (g 1 1) P.1 P.2 :=
    uhsDen_pos (show (0 : ℝ) < P.2 from hP) (cd_ne_zero_of_det (det_two_eq_one g hg))
  refine ContinuousAt.continuousWithinAt ?_
  have hDc : Continuous fun q : ℂ × ℝ => uhsDen (g 1 0) (g 1 1) q.1 q.2 := by
    unfold uhsDen; fun_prop
  show ContinuousAt (fun q : ℂ × ℝ => (uhsZ (g 0 0) (g 0 1) (g 1 0) (g 1 1) q.1 q.2,
    uhsV (g 1 0) (g 1 1) q.1 q.2)) P
  refine ContinuousAt.prodMk ?_ ?_
  · unfold uhsZ
    refine ContinuousAt.div (by fun_prop) (Complex.continuous_ofReal.continuousAt.comp hDc.continuousAt) ?_
    exact_mod_cast hD.ne'
  · unfold uhsV
    exact continuousAt_snd.div hDc.continuousAt hD.ne'

/-- θ̃ agrees with its Fourier series almost everywhere for `dz dv/v³` (round 437's `ae_thetaF_eq_thS`). -/
theorem ae_uhs_thetaF_eq_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ᵐ Q ∂uhsMeasure, thetaF r Y hY Q = thS r Y hY Q :=
  (withDensity_absolutelyContinuous (volume.restrict UHS) uhsW).ae_le (ae_thetaF_eq_thS hr hY)

/-- So do their compositions with a matrix of determinant `1` (round 383's `measurePreserving_actP`). -/
theorem ae_thetaF_eq_thS_actP {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det = 1) : ∀ᵐ Q ∂uhsMeasure, thetaF r Y hY (actP g Q) = thS r Y hY (actP g Q) :=
  (measurePreserving_actP hg).quasiMeasurePreserving.ae (p := fun Q => thetaF r Y hY Q = thS r Y hY Q)
    (ae_uhs_thetaF_eq_thS hr hY)

/-- **The cube eigenrelation at every point**, for θ's Fourier series `thS` (round 436): for a primary prime
`p` and every `P` in upper half-space, `N(p)⁻³Σ_{q mod p³} thS(M_q·P) = N(p)⁻¹·thS(P)`. -/
theorem thS_cube_eigen {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p)
    (hpp : Primary p) {P : ℂ × ℝ} (hP : P ∈ UHS) :
    ((absNorm (span {p}) : ℂ) ^ 3)⁻¹ *
        ∑' q : 𝓞 K ⧸ span {p ^ 3}, thS r Y hY (actP (cubeMat p (repQ (p ^ 3) q)) P) =
      (absNorm (span {p}) : ℂ)⁻¹ * thS r Y hY P := by
  classical
  have hp0 := hp.ne_zero
  have := finite_quot_pow3 hp0
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  have hall : ∀ᵐ Q ∂uhsMeasure, ∀ q : 𝓞 K ⧸ span {p ^ 3},
      thetaF r Y hY (actP (cubeMat p (repQ (p ^ 3) q)) Q) =
        thS r Y hY (actP (cubeMat p (repQ (p ^ 3) q)) Q) :=
    Filter.eventually_all.2 fun q => ae_thetaF_eq_thS_actP hr hY (det_cubeMat hp0 _)
  have hD : ∀ᵐ Q ∂(volume.restrict UHS), ((absNorm (span {p}) : ℂ) ^ 3)⁻¹ *
      ∑ q, thS r Y hY (actP (cubeMat p (repQ (p ^ 3) q)) Q) = (absNorm (span {p}) : ℂ)⁻¹ * thS r Y hY Q := by
    refine restrict_UHS_ac.ae_le ?_
    filter_upwards [cubeDiff_ae_eq_zero hr hY hp hpp, ae_uhs_thetaF_eq_thS hr hY, hall] with Q h1 h2 h3
    rw [cubeDiff, tsum_fintype] at h1
    simp only [h2, h3] at h1
    exact sub_eq_zero.1 h1
  have hU : IsOpen UHS := isOpen_lt continuous_const continuous_snd
  have hc1 : ContinuousOn (fun Q => ((absNorm (span {p}) : ℂ) ^ 3)⁻¹ *
      ∑ q, thS r Y hY (actP (cubeMat p (repQ (p ^ 3) q)) Q)) UHS :=
    continuousOn_const.mul (continuousOn_finsetSum _ fun q _ =>
      (continuousOn_thS hr hY).comp (continuousOn_actP (det_cubeMat hp0 _))
        fun Q hQ => actP_mem (det_cubeMat hp0 _) hQ)
  have hc2 : ContinuousOn (fun Q => (absNorm (span {p}) : ℂ)⁻¹ * thS r Y hY Q) UHS :=
    continuousOn_const.mul (continuousOn_thS hr hY)
  rw [tsum_fintype]
  exact Measure.eqOn_open_of_ae_eq hD hU hc1 hc2 hP

/-- **The cube eigenrelation in coordinates**:
`N(p)⁻³Σ_{q mod p³} thS((z + 3q)/p³, v/|p|³) = N(p)⁻¹·thS(z, v)` for a primary prime `p`, `z ∈ ℂ` and `v > 0`
(round 446's `actP_cubeMat`). -/
theorem thS_cube_eigen_coord {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p)
    (hpp : Primary p) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    ((absNorm (span {p}) : ℂ) ^ 3)⁻¹ * ∑' q : 𝓞 K ⧸ span {p ^ 3},
        thS r Y hY ((z + σO (3 * repQ (p ^ 3) q)) / σO p ^ 3, v / ‖σO p‖ ^ 3) =
      (absNorm (span {p}) : ℂ)⁻¹ * thS r Y hY (z, v) := by
  have h := thS_cube_eigen hr hY hp hpp (P := (z, v)) hv
  simp only [actP_cubeMat hp.ne_zero] at h
  exact h

end Eis

end

#print axioms Eis.ae_Ioi_comp_mul
#print axioms Eis.integrableOn_fundP3_of_mul
#print axioms Eis.integrable_cubeDiff_slAct
#print axioms Eis.integrable_cubeDiff_inv_slAct
#print axioms Eis.det_cubeG
#print axioms Eis.cubeH_le
#print axioms Eis.finite_cubeH
#print axioms Eis.slAct_cubeE
#print axioms Eis.kub_cubeE
#print axioms Eis.sum_cubeC
#print axioms Eis.integral_trace_cube
#print axioms Eis.ae_good_heights
#print axioms Eis.cubeDiff_ae_eq_zero
#print axioms Eis.continuousOn_actP
#print axioms Eis.ae_uhs_thetaF_eq_thS
#print axioms Eis.ae_thetaF_eq_thS_actP
#print axioms Eis.thS_cube_eigen
#print axioms Eis.thS_cube_eigen_coord
