import KubotaGHolo

/-! # The residue θ (round 425)

S5f-10 of round 360's plan, part 8 (S5f-10e, first part). Round 424 made `s ↦ g_s` complex-differentiable into
`L²(ν)` and set `ũ_s = −R(ĥ(s))g_s`, equal to `E_s − h_s` for `Re s > 2`. This round takes the limit at
`s = 4/3` along `s = 4/3 + iε`, with `R = 2cosh r − 2` for `r > 0`.

* **The resolvent along a curve, near `0` only** (**`tendsto_resolvent_curve_ev`**): round 419's
  `tendsto_resolvent_curve` with its lower bound `c·ε ≤ Im ℓ(ε)` asked only for `ε` near `0⁺`, by changing `ℓ`
  where the bound fails.
* **`ĥ` near `4/3`** (**`deriv_hhat_im`** and **`imK_le_deriv_hhat`**, with `hasDerivAt_hhat_vert`): `ĥ′(σ)`
  is real for real `σ`, because `ĥ` is real on the real axis (round 418's `hhat_real_pos`), and
  `ĥ′(σ) ≥ K(r, σ) > 0` for `σ > 1`, because `Im ĥ(σ + iε)/ε → ĥ′(σ)` and `Im ĥ(σ + iε) ≥ ε·K(r, σ)` (round
  418's `im_hhat_ge`).
* **The residue** (`thetaL`, a definition; **`tendsto_uL_thetaL`** and **`ballOp_thetaL`**):
  `θ = −ĥ′(4/3)⁻¹·P g_{4/3}`, with `P` the orthogonal projection onto the kernel of `K − ĥ(4/3)`, is the limit
  of `(s − 4/3)·ũ_s` along `s = 4/3 + iε` as `ε → 0⁺`, and `Kθ = ĥ(4/3)·θ`.
* **An automorphic representative** (`thetaF`, a definition; **`isAut_kfun`**, **`isAut_thetaF`** and
  **`thetaL_ae_eq_thetaF`**, with `bker_slAct`): the kernel `k(p, q)` is automorphic in `p`, so every kernel
  integral `∫k(·, q)f(q) dν(q)` is automorphic. Since `ĥ(4/3) > 0`, `θ = ĥ(4/3)⁻¹·Kθ` is almost everywhere the
  automorphic function `θ̃ = ĥ(4/3)⁻¹·∫k(·, q)θ(q) dν(q)` (round 422's `ballOp_ae_eq_kfun`).
-/

open MeasureTheory Set Filter NumberField Complex
open scoped ENNReal Topology MatrixGroups

noncomputable section

namespace Eis

section Curve

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →L[ℂ] E}

/-- **Along a curve, with the lower bound near `0` only**: round 419's `tendsto_resolvent_curve` with
`c·ε ≤ Im ℓ(ε)` for `ε` near `0⁺`. -/
theorem tendsto_resolvent_curve_ev (hA : IsSelfAdjoint A) {l d c : ℝ} (hd : 0 < d) (hc : 0 < c)
    {ℓ : ℝ → ℂ} (hℓ : Tendsto (fun ε : ℝ => (ℓ ε - ((l : ℂ) + I * (ε * d))) / ε) (𝓝[>] 0) (𝓝 0))
    (him : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * ε ≤ (ℓ ε).im) {x : ℝ → E} {x₀ : E}
    (hx : Tendsto x (𝓝[>] 0) (𝓝 x₀)) :
    Tendsto (fun ε : ℝ => (I * ε) • resolvent A (ℓ ε) (x ε)) (𝓝[>] 0)
      (𝓝 ((d⁻¹ : ℂ) • (kerAt A l).starProjection x₀)) := by
  classical
  set ℓ' : ℝ → ℂ := fun ε => if c * ε ≤ (ℓ ε).im then ℓ ε else (l : ℂ) + I * (ε * c) with hℓ'
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ℓ' ε = ℓ ε := him.mono fun ε h => by simp [hℓ', h]
  have hℓ'1 : Tendsto (fun ε : ℝ => (ℓ' ε - ((l : ℂ) + I * (ε * d))) / ε) (𝓝[>] 0) (𝓝 0) :=
    hℓ.congr' (heq.mono fun ε h => by simp only [h])
  have him' : ∀ ε : ℝ, 0 < ε → c * ε ≤ (ℓ' ε).im := by
    intro ε _
    by_cases h : c * ε ≤ (ℓ ε).im
    · simp only [hℓ', h, ↓reduceIte]
    · simp only [hℓ', h, ↓reduceIte, add_im, ofReal_im, mul_im, I_re, I_im, zero_mul, one_mul,
        zero_add, mul_re, ofReal_re, sub_zero]
      linarith
  exact (tendsto_resolvent_curve hA hd hc hℓ'1 him' hx).congr' (heq.mono fun ε h => by simp only [h])

end Curve

/-! ### `ĥ` near the real axis -/

/-- **`ĥ′(σ)` is real**, for `σ` real: `ĥ` is real on the real axis (round 418's `hhat_real_pos`). -/
theorem deriv_hhat_im {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    (deriv (hhat (2 * Real.cosh r - 2)) σ).im = 0 := by
  set f := hhat (2 * Real.cosh r - 2)
  have hd : HasDerivAt f (deriv f σ) σ := ((differentiable_hhat hr.le) σ).hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => f y) (deriv f σ) σ := hd.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => ((f y).re : ℂ)) ((deriv f σ).re : ℂ) σ :=
    hd.real_of_complex.ofReal_comp
  have e : (fun y : ℝ => f y) = fun y : ℝ => ((f y).re : ℂ) :=
    funext fun y => Complex.ext (by simp) (by rw [ofReal_im]; exact (hhat_real_pos hr y).1)
  rw [e] at h1
  have := h1.unique h2
  rw [this, ofReal_im]

/-- The curve `ε ↦ ĥ(σ + iε)` has derivative `i·ĥ′(σ)` at `ε = 0`. -/
theorem hasDerivAt_hhat_vert {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    HasDerivAt (fun ε : ℝ => hhat (2 * Real.cosh r - 2) ((σ : ℂ) + I * ε))
      (I * deriv (hhat (2 * Real.cosh r - 2)) σ) 0 := by
  set f := hhat (2 * Real.cosh r - 2)
  have hγ : HasDerivAt (fun ε : ℝ => (σ : ℂ) + I * ε) I 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul I).const_add (σ : ℂ)
    simpa using this
  have hf : HasDerivAt f (deriv f σ) ((σ : ℂ) + I * ((0 : ℝ) : ℂ)) := by
    rw [ofReal_zero, mul_zero, add_zero]
    exact ((differentiable_hhat hr.le) σ).hasDerivAt
  have := hf.comp (0 : ℝ) hγ
  rw [mul_comm] at this
  exact this

/-- **`ĥ′(σ) ≥ K(r, σ) > 0`** for `σ > 1`, from round 418's lower bound `Im ĥ(σ + iε) ≥ ε·K(r, σ)`. -/
theorem imK_le_deriv_hhat {r : ℝ} (hr : 0 < r) {σ : ℝ} (hσ : 1 < σ) :
    imK r σ ≤ (deriv (hhat (2 * Real.cosh r - 2)) σ).re := by
  set f := hhat (2 * Real.cosh r - 2)
  have h := (hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_hhat_vert hr σ)).mono_left
    (nhdsWithin_mono _ (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun x hx => (mem_Ioi.1 hx).ne'))
  have hIm := (Complex.continuous_im.tendsto _).comp h
  have e1 : (I * deriv f σ).im = (deriv f σ).re := by simp
  rw [e1] at hIm
  refine ge_of_tendsto hIm ?_
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * r ≤ Real.pi / 2 := by
    have : Iio (Real.pi / 2 / r) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
    filter_upwards [nhdsWithin_le_nhds this] with ε hε
    rw [mem_Iio, lt_div_iff₀ hr] at hε
    exact hε.le
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : (0 : ℝ) < ε := hε0
  have hs : ((σ : ℂ) + I * ε).re = σ ∧ ((σ : ℂ) + I * ε).im = ε := by simp
  have hb := im_hhat_ge hr (s := (σ : ℂ) + I * ε) (by rw [hs.1]; exact hσ) (by rw [hs.2]; exact hε0'.le)
    (by rw [hs.2]; exact hε)
  rw [hs.1, hs.2] at hb
  have h0 : (hhat (2 * Real.cosh r - 2) ((σ : ℂ) + I * ((0 : ℝ) : ℂ))).im = 0 := by
    rw [ofReal_zero, mul_zero, add_zero]
    exact (hhat_real_pos hr σ).1
  simp only [Function.comp_apply, zero_add, Complex.smul_im, smul_eq_mul, Complex.sub_im]
  rw [h0, sub_zero]
  rw [inv_mul_eq_div, le_div_iff₀ hε0', mul_comm]
  exact hb

/-! ### The residue θ -/

/-- **The residue θ**, for `R = 2cosh r − 2`: `−ĥ′(4/3)⁻¹·P g_{4/3}`, with `P` the orthogonal projection onto
the kernel of `K − ĥ(4/3)`. -/
def thetaL (r Y : ℝ) (hY : 0 < Y) : Lp ℂ 2 (muR rhoG) :=
  -(((deriv (hhat (2 * Real.cosh r - 2)) ((4 / 3 : ℝ) : ℂ)).re : ℂ))⁻¹ •
    (kerAt (ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r))
      (hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ)).re).starProjection
      (gL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY ((4 / 3 : ℝ) : ℂ))

/-- **θ is the residue of `ũ_s` at `s = 4/3`**, along `s = 4/3 + iε`: `(s − 4/3)·ũ_s → θ` as `ε → 0⁺`, for
`r > 0` and `Y > 0`. -/
theorem tendsto_uL_thetaL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun ε : ℝ => (I * ε) •
        uL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY (((4 / 3 : ℝ) : ℂ) + I * ε))
      (𝓝[>] 0) (𝓝 (thetaL r Y hY)) := by
  have hK := isSelfAdjoint_ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r)
  have hσ : (1 : ℝ) < 4 / 3 := by norm_num
  have hc : 0 < imK r (4 / 3) := imK_pos hr hσ
  have hd : 0 < (deriv (hhat (2 * Real.cosh r - 2)) ((4 / 3 : ℝ) : ℂ)).re :=
    lt_of_lt_of_le hc (imK_le_deriv_hhat hr hσ)
  have hD : deriv (hhat (2 * Real.cosh r - 2)) ((4 / 3 : ℝ) : ℂ) =
      (((deriv (hhat (2 * Real.cosh r - 2)) ((4 / 3 : ℝ) : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by rw [ofReal_im]; exact deriv_hhat_im hr (4 / 3))
  have hl : hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ) =
      (((hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by rw [ofReal_im]; exact (hhat_real_pos hr (4 / 3)).1)
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_hhat_vert hr (4 / 3))).mono_left
    (nhdsWithin_mono _ (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun x hx => (mem_Ioi.1 hx).ne'))
  have hℓ : Tendsto (fun ε : ℝ => (hhat (2 * Real.cosh r - 2) (((4 / 3 : ℝ) : ℂ) + I * ε) -
      ((((hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ)).re : ℝ) : ℂ) +
        I * (ε * (deriv (hhat (2 * Real.cosh r - 2)) ((4 / 3 : ℝ) : ℂ)).re))) / ε)
      (𝓝[>] 0) (𝓝 0) := by
    have h2 := hslope.sub_const (I * deriv (hhat (2 * Real.cosh r - 2)) ((4 / 3 : ℝ) : ℂ))
    rw [sub_self] at h2
    refine h2.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    simp only [zero_add, ofReal_zero, mul_zero, add_zero]
    rw [Complex.real_smul, ofReal_inv]
    generalize hA : hhat (2 * Real.cosh r - 2) (((4 / 3 : ℝ) : ℂ) + I * ε) = A
    generalize hB : hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ) = B at hl
    generalize hC : deriv (hhat (2 * Real.cosh r - 2)) ((4 / 3 : ℝ) : ℂ) = C at hD
    rw [← hl, ← hD]
    field_simp
    ring
  have him : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      imK r (4 / 3) * ε ≤ (hhat (2 * Real.cosh r - 2) (((4 / 3 : ℝ) : ℂ) + I * (ε : ℂ))).im := by
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε * r ≤ Real.pi / 2 := by
      have : Iio (Real.pi / 2 / r) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
      filter_upwards [nhdsWithin_le_nhds this] with ε hε
      rw [mem_Iio, lt_div_iff₀ hr] at hε
      exact hε.le
    filter_upwards [hev, self_mem_nhdsWithin] with ε hε hε0
    have hε0' : (0 : ℝ) < ε := hε0
    have hs : (((4 / 3 : ℝ) : ℂ) + I * ε).re = 4 / 3 ∧ (((4 / 3 : ℝ) : ℂ) + I * ε).im = ε := by
      simp
    have hb := im_hhat_ge hr (s := ((4 / 3 : ℝ) : ℂ) + I * ε) (by rw [hs.1]; exact hσ)
      (by rw [hs.2]; exact hε0'.le) (by rw [hs.2]; exact hε)
    rw [hs.1, hs.2] at hb
    linarith
  have hx : Tendsto (fun ε : ℝ => gL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY
      (((4 / 3 : ℝ) : ℂ) + I * ε)) (𝓝[>] 0)
      (𝓝 (gL (2 * Real.cosh r - 2) (cosh_sub_nonneg r) Y hY ((4 / 3 : ℝ) : ℂ))) := by
    have hc0 : Continuous fun ε : ℝ => ((4 / 3 : ℝ) : ℂ) + I * ε := by fun_prop
    have h0 := ((continuous_gL (cosh_sub_nonneg r) hY).comp hc0).tendsto 0
    simp only [Function.comp_apply, ofReal_zero, mul_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h := (tendsto_resolvent_curve_ev hK hd hc hℓ him hx).neg
  refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_) |>.trans (le_of_eq ?_)
  · rw [uL, smul_neg]
  · rw [thetaL, neg_smul]

/-- **θ is an eigenfunction of the ball operator**, with eigenvalue `ĥ(4/3)`. -/
theorem ballOp_thetaL {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r) (thetaL r Y hY) =
      hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ) • thetaL r Y hY := by
  set K := ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r)
  set l := (hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ)).re
  have hl : hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ) = (l : ℂ) :=
    Complex.ext rfl (by rw [ofReal_im]; exact (hhat_real_pos hr (4 / 3)).1)
  have hmem : thetaL r Y hY ∈ kerAt K l :=
    Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _)
  have h0 := LinearMap.mem_ker.1 hmem
  rw [ContinuousLinearMap.coe_coe, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
    one_apply_eq_self, sub_eq_zero] at h0
  rw [hl]
  exact h0

/-! ### An automorphic representative -/

section Kernel

variable {Γ : Subgroup SL(2, 𝓞 K)} {χ : SL(2, 𝓞 K) → ℂ}

/-- **The kernel is automorphic in its first variable**: `k(g·p, q) = χ(g)·k(p, q)` for `g ∈ Γ`. -/
theorem bker_slAct (hχ : IsUChar Γ χ) (R : ℝ) {g : SL(2, 𝓞 K)} (hg : g ∈ Γ) {p q : ℂ × ℝ}
    (hp : p ∈ UHS) (hq : q ∈ UHS) : bker Γ χ R (slAct g p) q = χ g * bker Γ χ R p q := by
  unfold bker
  rw [← (Equiv.mulLeft (⟨g, hg⟩ : Γ)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  rw [hχ.map_mul g hg γ γ.2, mul_assoc, slAct_mul _ _ hq]
  have hiff : slAct g (slAct γ q) ∈ hball R (slAct g p) ↔ slAct γ q ∈ hball R p :=
    mem_hball_actP (det_map_σO g.2) hp (slAct_mem (γ : SL(2, 𝓞 K)) hq)
  by_cases h : slAct γ q ∈ hball R p
  · rw [indicator_of_mem h, indicator_of_mem (hiff.2 h)]
    rfl
  · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h (hiff.1 h')]

/-- **Kernel integrals are automorphic**: `∫k(·, q)f(q) dν(q)` satisfies `u(γp) = χ(γ)u(p)` for every `f`. -/
theorem isAut_kfun (hχ : IsUChar Γ χ) (R : ℝ) (ρ : ℂ × ℝ → ℝ≥0∞) (f : ℂ × ℝ → ℂ) :
    IsAut Γ χ (kfun Γ χ R ρ f) := by
  intro g hg p hp
  unfold kfun
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_muR_UHS ρ] with q hq
  rw [bker_slAct hχ R hg hp hq, mul_assoc]

end Kernel

/-- **An automorphic representative of θ**: `ĥ(4/3)⁻¹` times the kernel integral of θ. -/
def thetaF (r Y : ℝ) (hY : 0 < Y) : ℂ × ℝ → ℂ :=
  (hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ))⁻¹ •
    kfun Gam3 (fun g => kub ↑g) (2 * Real.cosh r - 2) rhoG (thetaL r Y hY)

/-- `θ̃(γw) = κ(γ)·θ̃(w)` for `γ ∈ Γ_1(3)`. -/
theorem isAut_thetaF (r Y : ℝ) (hY : 0 < Y) : IsAut Gam3 (fun g => kub ↑g) (thetaF r Y hY) := by
  intro g hg p hp
  simp only [thetaF, Pi.smul_apply, smul_eq_mul]
  rw [isAut_kfun isUChar_kub _ rhoG _ g hg p hp]
  ring

/-- **θ is its automorphic representative almost everywhere.** -/
theorem thetaL_ae_eq_thetaF {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    (thetaL r Y hY : ℂ × ℝ → ℂ) =ᵐ[muR rhoG] thetaF r Y hY := by
  set h := hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ)
  have hh : h ≠ 0 := by
    intro h0
    have := (hhat_real_pos hr (4 / 3)).2
    rw [show hhat (2 * Real.cosh r - 2) ((4 / 3 : ℝ) : ℂ) = h from rfl, h0, zero_re] at this
    exact lt_irrefl _ this
  have e : thetaL r Y hY =
      h⁻¹ • ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r) (thetaL r Y hY) := by
    rw [ballOp_thetaL hr hY, smul_smul, inv_mul_cancel₀ hh, one_smul]
  have hk := ballOp_ae_eq_kfun isPU_rhoG isUChar_kub (cosh_sub_nonneg r) (thetaL r Y hY)
  have hs := Lp.coeFn_smul h⁻¹ (ballOp isPU_rhoG isUChar_kub (cosh_sub_nonneg r) (thetaL r Y hY))
  rw [← e] at hs
  filter_upwards [hs, hk] with p h1 h2
  rw [h1, Pi.smul_apply, h2]
  rfl

end Eis

end

#print axioms Eis.tendsto_resolvent_curve_ev
#print axioms Eis.deriv_hhat_im
#print axioms Eis.hasDerivAt_hhat_vert
#print axioms Eis.imK_le_deriv_hhat
#print axioms Eis.tendsto_uL_thetaL
#print axioms Eis.ballOp_thetaL
#print axioms Eis.bker_slAct
#print axioms Eis.isAut_kfun
#print axioms Eis.isAut_thetaF
#print axioms Eis.thetaL_ae_eq_thetaF
