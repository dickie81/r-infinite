import Mathlib
import WeilIndexConverse

/-! # Every off-line quadruple gives a negative direction of `Q` (round 232)

Rounds 230 and 231 build `m` negative directions of Weil's form from `m` off-line zero quadruples, but
only when all the off-line zeros (round 230), or all those above some level (round 231), are finitely
many. Here the finiteness is gone.

* **`negDirections_offline`**: for any `m` off-line zeros of ζ in pairwise different quadruples
  `{ρ, 1 − ρ, ρ̄, 1 − ρ̄}`, some support has an `m`-dimensional space of strip-test probes on which `Q` is
  negative definite. Nothing is assumed about the other zeros.
* **`negDirections_unbounded`**: if the off-line quadruples are infinitely many (no finite set of
  quadruples holds every off-line zero), the negative index of `Q` over all supports is unbounded.

With round 229 (`finrank_le_quadruples_zeta`), the negative index of `Q` over all supports is the number
of off-line quadruples, finite or infinite. Bombieri (2000) proved the finite case for the complex form.

The proof replaces the explicit construction of round 230 by a density argument.

* **Probes** (A). Finite combinations `Σ_s c_s·twin(box 1, s)` of twin boxes at shifts `s ≥ 0`, with
  transform `m_c(z)ĝ₀(z)`, `m_c(z) = Σ_s c_s·2cos(sz)`, are strip-test probes.
* **ℓ² over the zeros** (B). The vector `(M(t_ρ))_ρ` of a probe's transform at the zero ordinates lies in
  `ℓ²`, and `Q = Re Σ_ρ M(t_ρ)²` is a bounded form there (`Bre`).
* **Targets** (C). For an off-line zero `r`, `T_r` is `i` on the zeros with `t_ρ = ±t_r` and `−i` on those
  with `t_ρ = ±t̄_r`. Then `Re Σ T_x(ρ)² ≤ −Σ x_r²` for `T_x = Σ x_r T_r`.
* **Density** (D). The twin vectors `v_s = (2cos(s t_ρ)ĝ₀(t_ρ))_ρ` span a subspace whose closure holds
  every `T_r`. A vector `a` orthogonal to all `v_s` makes `Σ_q c_q(2 + e^{λP_q} + e^{−λP_q})` constant in
  `λ`, for weights `c_q` built from `a` over the poles `±2i·t_ρ`, `±2i·t̄_ρ`. Its Laplace transform then has
  no residues (`TwinLandau.Rp_eq_zero_of_Wsum_const`), and the residue at `2i·t_r` is `ĝ₀(t_r)` times a
  sum that vanishes exactly when `⟨a, T_r⟩ = 0`.
* **The space** (E). Approximate each `T_r` within `ε` by some `v_{c_r}`. Then
  `Q(Σ x_r g_r) ≤ −Σx_r² + ε(2C + ε)·m·Σx_r² < 0`.

No bearing on RH: this counts off-line zeros when they exist; it does not say whether any exist. -/

open Real Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## A. Finite combinations of twin boxes -/

/-- The twin box at shift `s`. -/
def twinBox (s : NNReal) : ℝ → ℝ := twin (box 1) s

/-- `Σ_s c_s·twin(box 1, s)` for a finitely supported weight `c`. -/
def twinComb : (NNReal →₀ ℝ) →ₗ[ℝ] (ℝ → ℝ) := Finsupp.linearCombination ℝ twinBox

/-- The multiplier `m_c(z) = Σ_s c_s·2cos(sz)`. -/
def mulC (z : ℂ) : (NNReal →₀ ℝ) →ₗ[ℝ] ℂ :=
  Finsupp.linearCombination ℝ fun s : NNReal => 2 * Complex.cos ((s : ℝ) * z)

/-- Every shift of `c` is at most `A − 1`. -/
def Fits (c : NNReal →₀ ℝ) (A : ℝ) : Prop := ∀ s ∈ c.support, (s : ℝ) + 1 ≤ A

theorem twinComb_apply (c : NNReal →₀ ℝ) (u : ℝ) :
    twinComb c u = ∑ s ∈ c.support, c s * twinBox s u := by
  simp [twinComb, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]

theorem mulC_apply (z : ℂ) (c : NNReal →₀ ℝ) :
    mulC z c = ∑ s ∈ c.support, (c s : ℂ) * (2 * Complex.cos ((s : ℝ) * z)) := by
  simp [mulC, Finsupp.linearCombination_apply, Finsupp.sum, Complex.real_smul]

theorem twinBox_probe {s : NNReal} {A : ℝ} (h : (s : ℝ) + 1 ≤ A) : Probe A (twinBox s) :=
  (twin_probe (box_probe 1) (NNReal.coe_nonneg s)).mono h

theorem twinComb_eq (c : NNReal →₀ ℝ) :
    twinComb c = fun u => ∑ s ∈ c.support, c s * twinBox s u := funext (twinComb_apply c)

theorem twinComb_probe {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) : Probe A (twinComb c) := by
  rw [twinComb_eq]
  exact probe_finset_sum _ fun s hs => probe_smul (twinBox_probe (h s hs)) _

theorem ghatC_twinComb {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) (z : ℂ) :
    ghatC (twinComb c) A z = mulC z c * ghatC (box 1) 1 z := by
  rw [twinComb_eq, ghatC_finset_sum _ (fun s hs => probe_smul (twinBox_probe (h s hs)) _), mulC_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  rw [ghatC_smul, twinBox, ghatC_mono h1 (h s hs) (twin_probe (box_probe 1) (NNReal.coe_nonneg s)).supp,
    ghatC_twin one_pos (box_probe 1) (NNReal.coe_nonneg s)]
  ring

theorem striptest_twinComb {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) :
    ∃ K, StripTest (fun z => ghatC (twinComb c) A z ^ 2) K := by
  have hp := box_probe 1
  obtain ⟨C, hC⟩ := ghat_antitone_strip one_pos hp.even box_antitone box_nonneg hp.intervalIntegrable
  set M : ℝ := ∑ s ∈ c.support, |c s| * (2 * Real.exp s)
  have hm : ∀ t ∈ PilotWeil.strip (-1) 1, ‖mulC t c‖ ≤ M := by
    intro t ht
    rw [mulC_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_two_cos_strip (NNReal.coe_nonneg s) ht) (abs_nonneg _)
  have hd : Differentiable ℂ fun z => mulC z c := by
    have e : (fun z => mulC z c)
        = fun z => ∑ s ∈ c.support, (c s : ℂ) * (2 * Complex.cos ((s : ℝ) * z)) :=
      funext fun z => mulC_apply z c
    rw [e]; fun_prop
  have hT := striptest_mul_sq (G := ghatC (box 1) 1) (m := fun z => mulC z c)
    (ghatC_differentiable hp.intervalIntegrable) hd hC hm
  have e : (fun z => ghatC (twinComb c) A z ^ 2) = fun z => (mulC z c * ghatC (box 1) 1 z) ^ 2 :=
    funext fun z => by rw [ghatC_twinComb h z]
  exact ⟨_, e ▸ hT⟩

/-- `ĝ₀(t_ρ)`, the box transform at the ordinate of a zero. -/
def G0 (i : ZIdx) : ℂ := ghatC (box 1) 1 (tz i)

/-- **The explicit formula for a twin combination**: `Q = Σ_ρ (m_c(t_ρ)ĝ₀(t_ρ))²`. -/
theorem hasSum_twinComb {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) (hA : 0 < A) :
    HasSum (fun i : ZIdx => (mulC (tz i) c * G0 i) ^ 2) (weilQ A (twinComb c) : ℂ) := by
  obtain ⟨K, hK⟩ := striptest_twinComb h
  have := weilQ_eq_zero_sum (twinComb_probe h) hA (weilExplicit_of_strip hA (twinComb_probe h) hK)
  convert this using 2 with i
  rw [ghatC_twinComb h]; rfl


/-! ## B–E, for any family of ordinates (round 274)

Round 232's argument (§B–E below) uses only: ordinates `t_i` with `|Im t_i| < ½`, `Re t_i ≠ 0` and
finitely many below any height; `Σ‖ĝ₀(κt_i)‖² < ∞` at a scale `κ > 0`; and the explicit formula
`Q(Σ c_s twin_s) = w·Σ_i (m_c(κt_i)ĝ₀(κt_i))²` with a weight `w > 0`. `NegData` bundles them. ζ is the
instance `zetaND` (`κ = 1`, `w = 1`); the Davenport–Heilbronn form is `DHNegIndex.dhND` (`κ = 3`,
`w = 2`). Until round 273 the two were separate copies. -/

theorem cancel_two_I {a b : ℂ} (h : 2 * I * a = 2 * I * b) : a = b :=
  mul_left_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero) h

theorem norm_eq_of_indR {p P : ℂ} (h : TwinLandau.indR p P ≠ 0) : ‖P‖ = ‖p‖ := by
  by_cases h1 : P = p
  · rw [h1]
  by_cases h2 : -P = p
  · rw [← h2, norm_neg]
  simp [TwinLandau.indR, h1, h2] at h

theorem two_cos_eq (l : ℝ) (t : ℂ) :
    cexp (l * (2 * I * t)) + cexp (-(l * (2 * I * t))) = 2 * Complex.cos (((2 * l : ℝ) : ℂ) * t) := by
  rw [Complex.cos, show ((2 * l : ℝ) : ℂ) * t * I = l * (2 * I * t) by push_cast; ring,
    show -(((2 * l : ℝ) : ℂ) * t) * I = -(l * (2 * I * t)) by push_cast; ring]
  ring

theorem orb_symm {t w : ℂ} (h : Orb t w) : Orb w t := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (neg_neg _).symm)
  · exact Or.inr (Or.inr (Or.inl (Complex.conj_conj _).symm))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_neg, Complex.conj_conj, neg_neg])))


/-- **Ordinates for the negative-index argument.** -/
structure NegData where
  ι : Type
  [cnt : Countable ι]
  t : ι → ℂ
  κ : ℝ
  κ_pos : 0 < κ
  t_im : ∀ i, |(t i).im| < 1 / 2
  t_re_ne : ∀ i, (t i).re ≠ 0
  finite_t : ∀ R : ℝ, {i | ‖t i‖ ≤ R}.Finite
  summable_G0 : Summable fun i => ‖ghatC (box 1) 1 ((κ : ℂ) * t i)‖ ^ 2
  Q : ℝ → (ℝ → ℝ) → ℝ
  w : ℝ
  w_pos : 0 < w
  Good : ℝ → (ℝ → ℝ) → Prop
  hasSum : ∀ {c : NNReal →₀ ℝ} {A : ℝ}, Fits c A → 0 < A →
    HasSum (fun i => (w : ℂ) * (mulC ((κ : ℂ) * t i) c * ghatC (box 1) 1 ((κ : ℂ) * t i)) ^ 2)
      (Q A (twinComb c) : ℂ)
  good : ∀ {c : NNReal →₀ ℝ} {A : ℝ}, Fits c A → Good A (twinComb c)

attribute [instance] NegData.cnt

/-- The poles `P_i = 2i·t_i`. -/
def NegData.P (D : NegData) (i : D.ι) : ℂ := 2 * I * D.t i

/-- `ĝ₀(κt_i)`. -/
def NegData.G0 (D : NegData) (i : D.ι) : ℂ := ghatC (box 1) 1 ((D.κ : ℂ) * D.t i)

theorem NegData.summable_G0_sq (D : NegData) : Summable fun i => ‖D.G0 i‖ ^ 2 := D.summable_G0

theorem NegData.re_P (D : NegData) (i : D.ι) : (D.P i).re = -(2 * (D.t i).im) := by simp [NegData.P]

theorem NegData.abs_re_P (D : NegData) (i : D.ι) : |(D.P i).re| < 1 := by
  rw [D.re_P, abs_neg, abs_mul, abs_two]
  have := D.t_im i; linarith

theorem NegData.im_P_ne (D : NegData) (i : D.ι) : (D.P i).im ≠ 0 := by
  simp only [NegData.P, mul_im, mul_re, re_ofNat, im_ofNat, I_re, I_im]
  have := D.t_re_ne i
  intro h; apply this; linarith

theorem NegData.finite_P (D : NegData) (R : ℝ) : {i | ‖D.P i‖ ≤ R}.Finite :=
  (D.finite_t (R / 2)).subset fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    have : ‖D.P i‖ = 2 * ‖D.t i‖ := by
      simp only [NegData.P, norm_mul, Complex.norm_I, Complex.norm_two]; ring
    linarith

/-! ### B. `ℓ²` over the zeros of `Ξ₃` -/

abbrev NegData.L2 (D : NegData) := lp (fun _ : D.ι => ℂ) 2

theorem NegData.memℓp_two (D : NegData) {f : D.ι → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2) : Memℓp f 2 :=
  memℓp_gen (by simpa using hf)

theorem NegData.sq_summable (D : NegData) (a : D.L2) : Summable fun i => ‖a i‖ ^ 2 := by
  simpa using (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem NegData.summable_mul_of_sq (D : NegData) {f g : D.ι → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2)
    (hg : Summable fun i => ‖g i‖ ^ 2) : Summable fun i => ‖f i * g i‖ :=
  ((hf.add hg).div_const 2).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => by
    rw [norm_mul]; have := two_mul_le_add_sq ‖f i‖ ‖g i‖; linarith

theorem NegData.t_mem_strip (D : NegData) (i : D.ι) : D.t i ∈ PilotWeil.strip (-1) 1 := by
  have := abs_lt.1 (D.t_im i)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

def NegData.vfun (D : NegData) (s : ℝ) (i : D.ι) : ℂ := 2 * Complex.cos (s * ((D.κ : ℂ) * D.t i)) * D.G0 i

theorem NegData.vfun_eq (D : NegData) (l : ℝ) (i : D.ι) :
    D.vfun (2 * l / D.κ) i = 2 * Complex.cos (((2 * l : ℝ) : ℂ) * D.t i) * D.G0 i := by
  unfold NegData.vfun
  have hk : (D.κ : ℂ) ≠ 0 := by exact_mod_cast D.κ_pos.ne'
  rw [show (((2 * l / D.κ : ℝ) : ℂ)) * ((D.κ : ℂ) * D.t i) = ((2 * l : ℝ) : ℂ) * D.t i by
    push_cast; field_simp]

theorem NegData.norm_vfun_le (D : NegData) {s : ℝ} (hs : 0 ≤ s) (i : D.ι) :
    ‖D.vfun s i‖ ≤ 2 * Real.exp (D.κ * s) * ‖D.G0 i‖ := by
  rw [NegData.vfun, norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_two_cos_le _).trans ?_) (norm_nonneg _)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) two_pos.le
  have e : ((s : ℂ) * ((D.κ : ℂ) * D.t i)).im = s * (D.κ * (D.t i).im) := by simp
  rw [e, abs_mul, abs_of_nonneg hs, abs_mul, abs_of_pos D.κ_pos]
  have h1 := D.t_im i
  have h2 : s * (D.κ * |(D.t i).im|) ≤ s * (D.κ * 1) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) D.κ_pos.le) hs
  linarith

theorem NegData.summable_vfun_sq (D : NegData) {s : ℝ} (hs : 0 ≤ s) : Summable fun i => ‖D.vfun s i‖ ^ 2 :=
  (D.summable_G0_sq.mul_left ((2 * Real.exp (D.κ * s)) ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _) fun i => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (D.norm_vfun_le hs i) 2

def NegData.vecS (D : NegData) (s : NNReal) : D.L2 := ⟨D.vfun s, D.memℓp_two (D.summable_vfun_sq (NNReal.coe_nonneg s))⟩

def NegData.vecL (D : NegData) : (NNReal →₀ ℝ) →ₗ[ℝ] D.L2 := Finsupp.linearCombination ℝ D.vecS

theorem NegData.vecL_apply (D : NegData) (c : NNReal →₀ ℝ) (i : D.ι) : D.vecL c i = mulC ((D.κ : ℂ) * D.t i) c * D.G0 i := by
  rw [NegData.vecL, Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply, mulC_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
  show (c s : ℂ) * D.vfun s i = _
  rw [NegData.vfun]; ring

def NegData.Bre (D : NegData) (u w : D.L2) : ℝ := ⟪star u, w⟫_ℝ

theorem NegData.hasSum_Bre (D : NegData) (u w : D.L2) : HasSum (fun i => (u i * w i).re) (D.Bre u w) := by
  have := lp.hasSum_inner (𝕜 := ℝ) (star u) w
  unfold NegData.Bre
  convert this using 2 with i
  rw [lp.star_apply, Complex.inner]
  simp [mul_comm]

theorem NegData.abs_Bre_le (D : NegData) (u w : D.L2) : |D.Bre u w| ≤ ‖u‖ * ‖w‖ := by
  have := abs_real_inner_le_norm (star u) w
  rwa [norm_star] at this

theorem NegData.Bre_sub_left (D : NegData) (u v w : D.L2) : D.Bre (u - v) w = D.Bre u w - D.Bre v w := by
  unfold NegData.Bre; rw [star_sub, inner_sub_left]

theorem NegData.Bre_sub_right (D : NegData) (u v w : D.L2) : D.Bre u (v - w) = D.Bre u v - D.Bre u w := by
  unfold NegData.Bre; rw [inner_sub_right]

theorem NegData.abs_Bre_sub_le (D : NegData) (y u : D.L2) : |D.Bre y y - D.Bre u u| ≤ ‖y - u‖ * (‖y‖ + ‖u‖) := by
  have e : D.Bre y y - D.Bre u u = D.Bre (y - u) y + D.Bre u (y - u) := by
    rw [D.Bre_sub_left, D.Bre_sub_right]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h1 := D.abs_Bre_le (y - u) y
  have h2 := D.abs_Bre_le u (y - u)
  nlinarith [norm_nonneg (y - u), norm_nonneg u]

/-- **`Q` is `w` times `Bre` of the probe's vector.** -/
theorem NegData.Q_eq_Bre (D : NegData) {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) (hA : 0 < A) :
    D.Q A (twinComb c) = D.w * D.Bre (D.vecL c) (D.vecL c) := by
  have h1 := Complex.hasSum_re (D.hasSum h hA)
  rw [Complex.ofReal_re] at h1
  refine h1.unique ?_
  convert (D.hasSum_Bre (D.vecL c) (D.vecL c)).mul_left D.w using 2 with i
  rw [D.vecL_apply, ← sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, NegData.G0]; ring

/-! ### C. The targets -/

theorem NegData.P_eq (D : NegData) (q : D.ι) : D.P q = 2 * I * D.t q := rfl

theorem NegData.conj_P (D : NegData) (q : D.ι) : (starRingEnd ℂ) (D.P q) = -(2 * I * (starRingEnd ℂ) (D.t q)) := by
  rw [D.P_eq, map_mul, map_mul, Complex.conj_I, map_ofNat]; ring

def NegData.e1 (D : NegData) (r i : D.ι) : ℝ := TwinLandau.indR (D.P r) (D.P i)

def NegData.e2 (D : NegData) (r i : D.ι) : ℝ := TwinLandau.indR (D.P r) (-(starRingEnd ℂ) (D.P i))

theorem NegData.e1_eq_zero (D : NegData) {r i : D.ι} (h : ‖D.P r‖ < ‖D.P i‖) : D.e1 r i = 0 := by
  by_contra h0; have := norm_eq_of_indR h0; linarith

theorem NegData.e2_eq_zero (D : NegData) {r i : D.ι} (h : ‖D.P r‖ < ‖D.P i‖) : D.e2 r i = 0 := by
  by_contra h0; have := norm_eq_of_indR h0; rw [norm_neg, Complex.norm_conj] at this; linarith

def NegData.near (D : NegData) (r : D.ι) : Finset D.ι := (D.finite_P ‖D.P r‖).toFinset

theorem NegData.not_near (D : NegData) {r i : D.ι} (h : i ∉ D.near r) : ‖D.P r‖ < ‖D.P i‖ := by
  rw [NegData.near, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at h; exact h

def NegData.Tfun (D : NegData) (r i : D.ι) : ℂ := I * ((D.e1 r i - D.e2 r i : ℝ) : ℂ)

theorem NegData.Tfun_eq_zero (D : NegData) {r i : D.ι} (h : i ∉ D.near r) : D.Tfun r i = 0 := by
  rw [NegData.Tfun, D.e1_eq_zero (D.not_near h), D.e2_eq_zero (D.not_near h)]; simp

def NegData.Tvec (D : NegData) (r : D.ι) : D.L2 :=
  ⟨D.Tfun r, D.memℓp_two (summable_of_ne_finset_zero (s := D.near r) fun i hi => by
    rw [D.Tfun_eq_zero hi, norm_zero]; norm_num)⟩

theorem NegData.e1_self (D : NegData) {r : D.ι} : D.e1 r r = 1 := by
  have h : -D.P r ≠ D.P r := fun e => D.im_P_ne r (by
    have := congrArg Complex.im e; simp at this; linarith)
  simp [NegData.e1, TwinLandau.indR, h]

theorem NegData.e2_self (D : NegData) {r : D.ι} (hr : (D.t r).im ≠ 0) : D.e2 r r = 0 := by
  have h1 : -(starRingEnd ℂ) (D.P r) ≠ D.P r := fun e => hr (by
    have := congrArg Complex.re e; simp at this; rw [D.re_P] at this; linarith)
  have h2 : -(-(starRingEnd ℂ) (D.P r)) ≠ D.P r := fun e => D.im_P_ne r (by
    have := congrArg Complex.im e; simp at this; linarith)
  simp only [NegData.e2, TwinLandau.indR, h1, h2, ↓reduceIte]; norm_num

theorem NegData.e_other (D : NegData) {r s : D.ι} (h : ¬Orb (D.t r) (D.t s)) : D.e1 s r = 0 ∧ D.e2 s r = 0 := by
  simp only [Orb, not_or] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have c1 : D.P r ≠ D.P s := fun e => h1 (cancel_two_I (by rw [← D.P_eq, ← D.P_eq, e]))
  have c2 : -D.P r ≠ D.P s := fun e => h2 (cancel_two_I (by
    rw [D.P_eq, D.P_eq] at e; linear_combination -e))
  have c3 : -(starRingEnd ℂ) (D.P r) ≠ D.P s := fun e => h3 (by
    rw [D.conj_P, D.P_eq, neg_neg] at e
    have := cancel_two_I e
    rw [← this, Complex.conj_conj])
  have c4 : -(-(starRingEnd ℂ) (D.P r)) ≠ D.P s := fun e => h4 (by
    rw [neg_neg, D.conj_P, D.P_eq] at e
    have := cancel_two_I (a := (starRingEnd ℂ) (D.t r)) (b := -D.t s) (by linear_combination -e)
    rw [← Complex.conj_conj (D.t r), this, map_neg])
  refine ⟨?_, ?_⟩
  · simp [NegData.e1, TwinLandau.indR, c1, c2]
  · simp only [NegData.e2, TwinLandau.indR, c3, c4, ↓reduceIte]; norm_num

theorem NegData.G0_e1 (D : NegData) (r i : D.ι) : D.G0 i * (D.e1 r i : ℂ) = D.G0 r * (D.e1 r i : ℂ) := by
  by_cases h1 : D.P i = D.P r
  · rw [NegData.G0, NegData.G0, show D.t i = D.t r from cancel_two_I (by rw [← D.P_eq, ← D.P_eq, h1])]
  by_cases h2 : -D.P i = D.P r
  · rw [D.P_eq, D.P_eq] at h2
    have : D.t i = -D.t r := cancel_two_I (by linear_combination -h2)
    rw [NegData.G0, NegData.G0, this, mul_neg, ghatC_even (box_probe 1).even]
  simp [NegData.e1, TwinLandau.indR, h1, h2]

theorem NegData.G0_e2 (D : NegData) (r i : D.ι) : (starRingEnd ℂ) (D.G0 i) * (D.e2 r i : ℂ) = D.G0 r * (D.e2 r i : ℂ) := by
  have hc : (starRingEnd ℂ) (D.G0 i) = ghatC (box 1) 1 ((D.κ : ℂ) * (starRingEnd ℂ) (D.t i)) := by
    have := (ghatC_conj (box_probe 1).even zero_le_one ((D.κ : ℂ) * D.t i)).symm
    rwa [map_mul, Complex.conj_ofReal] at this
  by_cases h1 : -(starRingEnd ℂ) (D.P i) = D.P r
  · have h1' := h1
    rw [D.conj_P, D.P_eq, neg_neg] at h1'
    rw [hc, cancel_two_I h1']; rfl
  by_cases h2 : -(-(starRingEnd ℂ) (D.P i)) = D.P r
  · have h2' := h2
    rw [neg_neg, D.conj_P, D.P_eq] at h2'
    have : (starRingEnd ℂ) (D.t i) = -D.t r := cancel_two_I (by linear_combination -h2')
    rw [hc, this, mul_neg, ghatC_even (box_probe 1).even]; rfl
  have h2' : ¬(starRingEnd ℂ) (D.P i) = D.P r := by simpa using h2
  simp [NegData.e2, TwinLandau.indR, h1, h2']

/-! ### D. Density of the twin vectors -/

theorem NegData.summable_of_sq_mul (D : NegData) {f g : D.ι → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2)
    (hg : Summable fun i => ‖g i‖ ^ 2) : Summable fun i => f i * g i :=
  (D.summable_mul_of_sq hf hg).of_norm

theorem NegData.summable_conj_sq (D : NegData) (a : D.L2) : Summable fun i => ‖(starRingEnd ℂ) (a i)‖ ^ 2 := by
  simpa using D.sq_summable a

theorem NegData.summable_e (D : NegData) {r : D.ι} {f : D.ι → ℂ} {e : D.ι → ℝ} (he : ∀ i, i ∉ D.near r → e i = 0) :
    Summable fun i => f i * (e i : ℂ) :=
  summable_of_ne_finset_zero (s := D.near r) fun i hi => by rw [he i hi]; simp

theorem NegData.inner_Tvec_eq_zero (D : NegData) (a : D.L2) (ha : ∀ s : NNReal, ⟪D.vecS s, a⟫_ℝ = 0) {r : D.ι}
    (hr : (D.t r).im ≠ 0) : ⟪a, D.Tvec r⟫_ℝ = 0 := by
  classical
  set Pz : D.ι ⊕ D.ι → ℂ := Sum.elim D.P fun i => -(starRingEnd ℂ) (D.P i)
  set cz : D.ι ⊕ D.ι → ℂ :=
    Sum.elim (fun i => D.G0 i * (starRingEnd ℂ) (a i)) fun i => (starRingEnd ℂ) (D.G0 i) * a i
  have hsa := D.sq_summable a
  have hsg := D.summable_G0_sq
  have hsgc : Summable fun i => ‖(starRingEnd ℂ) (D.G0 i)‖ ^ 2 := by simpa using hsg
  have hD : TwinLandau.TwinPoles Pz cz := by
    refine ⟨Summable.sum (f := fun q => ‖cz q‖) (D.summable_mul_of_sq hsg (D.summable_conj_sq a))
      (D.summable_mul_of_sq hsgc hsa), fun q => ?_, fun q => ?_, fun R => ?_⟩
    · rcases q with i | i
      · exact D.abs_re_P i
      · simpa [Pz] using D.abs_re_P i
    · rcases q with i | i
      · exact D.im_P_ne i
      · simpa [Pz] using D.im_P_ne i
    · refine (((D.finite_P R).image Sum.inl).union ((D.finite_P R).image Sum.inr)).subset ?_
      rintro (i | i) h
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr ⟨i, by simpa [Pz] using h, rfl⟩
  set SA := ∑' i, D.G0 i * (starRingEnd ℂ) (a i)
  set SB := ∑' i, (starRingEnd ℂ) (D.G0 i) * a i
  have hSA : HasSum (fun i => D.G0 i * (starRingEnd ℂ) (a i)) SA :=
    (D.summable_of_sq_mul hsg (D.summable_conj_sq a)).hasSum
  have hSB : HasSum (fun i => (starRingEnd ℂ) (D.G0 i) * a i) SB :=
    (D.summable_of_sq_mul hsgc hsa).hasSum
  have hW : ∀ l : ℝ, 0 ≤ l → TwinLandau.Wsum Pz cz l = 2 * SA + 2 * SB := by
    intro l hl
    set s : NNReal := ⟨2 * l / D.κ, div_nonneg (by positivity) D.κ_pos.le⟩
    have hv := D.summable_vfun_sq (s := 2 * l / D.κ) (div_nonneg (by positivity) D.κ_pos.le)
    set X := ∑' i, (starRingEnd ℂ) (a i) * D.vfun (2 * l / D.κ) i
    have hX : HasSum (fun i => (starRingEnd ℂ) (a i) * D.vfun (2 * l / D.κ) i) X :=
      (D.summable_of_sq_mul (D.summable_conj_sq a) hv).hasSum
    have hXc : HasSum (fun i => a i * (starRingEnd ℂ) (D.vfun (2 * l / D.κ) i)) ((starRingEnd ℂ) X) := by
      have := hX.star
      simpa [mul_comm] using this
    have hXre : X.re = 0 := by
      have h1 := Complex.hasSum_re hX
      have h2 := lp.hasSum_inner (𝕜 := ℝ) (D.vecS s) a
      rw [ha s] at h2
      refine h1.unique ?_
      convert h2 using 2 with i
      show _ = ⟪D.vfun (2 * l / D.κ) i, a i⟫_ℝ
      rw [Complex.inner, ← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    have hin : HasSum (fun i => TwinLandau.wq Pz cz (Sum.inl i) l)
        (2 * SA + X) := by
      convert (hSA.mul_left 2).add hX using 2 with i
      simp only [TwinLandau.wq, Pz, cz, Sum.elim_inl]
      rw [add_assoc, D.P_eq, two_cos_eq, D.vfun_eq]; ring
    have hinr : HasSum (fun i => TwinLandau.wq Pz cz (Sum.inr i) l)
        (2 * SB + (starRingEnd ℂ) X) := by
      convert (hSB.mul_left 2).add hXc using 2 with i
      simp only [TwinLandau.wq, Pz, cz, Sum.elim_inr]
      rw [D.conj_P, neg_neg, add_assoc, two_cos_eq, D.vfun_eq, map_mul, map_mul, ← Complex.cos_conj,
        map_mul, Complex.conj_ofReal, map_ofNat]
      ring
    have hall := HasSum.sum (f := fun q => TwinLandau.wq Pz cz q l) hin hinr
    have hXX : X + (starRingEnd ℂ) X = 0 := by
      rw [Complex.add_conj, hXre]; simp
    rw [TwinLandau.Wsum, hall.tsum_eq]
    linear_combination hXX
  have hp0 : D.P r ≠ 0 := fun e => D.im_P_ne r (by rw [e, zero_im])
  have hR := TwinLandau.Rp_eq_zero_of_Wsum_const hD hW hp0
  set S1 := ∑' i, (starRingEnd ℂ) (a i) * (D.e1 r i : ℂ)
  set S2 := ∑' i, a i * (D.e2 r i : ℂ)
  have hne1 : ∀ i, i ∉ D.near r → D.e1 r i = 0 := fun i hi => D.e1_eq_zero (D.not_near hi)
  have hne2 : ∀ i, i ∉ D.near r → D.e2 r i = 0 := fun i hi => D.e2_eq_zero (D.not_near hi)
  have hS1 : HasSum (fun i => (starRingEnd ℂ) (a i) * (D.e1 r i : ℂ)) S1 := (D.summable_e hne1).hasSum
  have hS2 : HasSum (fun i => a i * (D.e2 r i : ℂ)) S2 := (D.summable_e hne2).hasSum
  have hRsum : HasSum (fun q => cz q * (TwinLandau.indR (D.P r) (Pz q) : ℂ))
      (D.G0 r * S1 + D.G0 r * S2) := by
    refine HasSum.sum (f := fun q => cz q * (TwinLandau.indR (D.P r) (Pz q) : ℂ)) ?_ ?_
    · convert hS1.mul_left (D.G0 r) using 2 with i
      have h := D.G0_e1 r i
      simp only [NegData.e1] at h
      simp only [Function.comp_apply, cz, Pz, Sum.elim_inl, NegData.e1]
      linear_combination (starRingEnd ℂ) (a i) * h
    · convert hS2.mul_left (D.G0 r) using 2 with i
      have h := D.G0_e2 r i
      simp only [NegData.e2] at h
      simp only [Function.comp_apply, cz, Pz, Sum.elim_inr, NegData.e2]
      linear_combination a i * h
  have hG : D.G0 r ≠ 0 := ghat_box_ne (by
    rw [show ((D.κ : ℂ) * D.t r).im = D.κ * (D.t r).im by simp]; exact mul_ne_zero D.κ_pos.ne' hr)
  have hS12 : S1 + S2 = 0 := by
    have := hRsum.tsum_eq
    rw [← TwinLandau.Rp] at this
    rw [hR] at this
    have h2 : D.G0 r * (S1 + S2) = 0 := by rw [mul_add]; exact this.symm
    exact (mul_eq_zero.1 h2).resolve_left hG
  have hT : HasSum (fun i => D.Tfun r i * (starRingEnd ℂ) (a i))
      (I * S1 - I * star S2) := by
    convert (hS1.mul_left I).sub (hS2.star.mul_left I) using 2 with i
    simp only [NegData.Tfun, star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  have h1 := Complex.hasSum_re hT
  have h2 := lp.hasSum_inner (𝕜 := ℝ) a (D.Tvec r)
  have e : ⟪a, D.Tvec r⟫_ℝ = (I * S1 - I * star S2).re := by
    refine h2.unique ?_
    convert h1 using 2 with i
    show ⟪a i, D.Tfun r i⟫_ℝ = _
    rw [Complex.inner]
  rw [e]
  have := congrArg Complex.im hS12
  simp only [add_im, zero_im] at this
  simp [Complex.mul_re]
  linarith

theorem NegData.Tvec_mem_closure (D : NegData) {r : D.ι} (hr : (D.t r).im ≠ 0) :
    D.Tvec r ∈ (LinearMap.range D.vecL).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro a ha
  refine D.inner_Tvec_eq_zero a (fun s => ?_) hr
  rw [Submodule.mem_orthogonal] at ha
  refine ha _ ⟨Finsupp.single s 1, ?_⟩
  rw [NegData.vecL, Finsupp.linearCombination_single, one_smul]

theorem NegData.exists_approx (D : NegData) {r : D.ι} (hr : (D.t r).im ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : NNReal →₀ ℝ, ‖D.vecL c - D.Tvec r‖ < ε := by
  have hm := D.Tvec_mem_closure hr
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hm
  obtain ⟨y, hy1, hy⟩ := hm ε hε
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hy1
  exact ⟨c, by rw [← dist_eq_norm, dist_comm]; exact hy⟩

/-! ### E. The negative space -/

/-- **Every off-line quadruple gives a negative direction of `Q`.** For any finite set `R` of
off-line ordinates in pairwise different quadruples, some support `a` has a space `V` of probes with
`dim V = |R|`, each satisfying `Good`, on which `Q` is negative definite. -/
theorem NegData.negDirections (D : NegData) (R : Finset D.ι)
    (hRoff : ∀ r ∈ R, (D.t r).im ≠ 0)
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (D.t s) (D.t r)) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ D.Good a v) ∧
      ∀ v ∈ V, v ≠ 0 → D.Q a v < 0 := by
  classical
  set m : ℕ := Fintype.card R
  set C : ℝ := ∑ r : R, ‖D.Tvec r.1‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set ε : ℝ := 1 / ((m : ℝ) * (2 * C + 1) + 1)
  have hden : 0 < (m : ℝ) * (2 * C + 1) + 1 := by positivity
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [div_le_one hden]; nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hεm : ε * (2 * C + ε) * m < 1 := by
    have h1 : ε * (2 * C + ε) * m ≤ ε * ((m : ℝ) * (2 * C + 1)) := by
      calc ε * (2 * C + ε) * m ≤ ε * (2 * C + 1) * m := by gcongr
        _ = ε * ((m : ℝ) * (2 * C + 1)) := by ring
    have h2 : ε * ((m : ℝ) * (2 * C + 1)) < 1 := by
      simp only [ε]; rw [div_mul_eq_mul_div, one_mul, div_lt_one hden]; linarith
    linarith
  choose c hc using fun r : R => D.exists_approx (hRoff r.1 r.2) hε
  set A : ℝ := 1 + ∑ r : R, ∑ s ∈ (c r).support, (s : ℝ)
  have hA : 0 < A := by
    have : 0 ≤ ∑ r : R, ∑ s ∈ (c r).support, (s : ℝ) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    linarith
  set cx : (R → ℝ) → NNReal →₀ ℝ := fun x => ∑ r, x r • c r
  have hfits : ∀ x, Fits (cx x) A := by
    intro x s hs
    obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hs)
    have hr' : s ∈ (c r).support := Finsupp.support_smul hr
    have h1 : (s : ℝ) ≤ ∑ s ∈ (c r).support, (s : ℝ) :=
      Finset.single_le_sum (f := fun s : NNReal => (s : ℝ)) (fun _ _ => NNReal.coe_nonneg _) hr'
    have h2 : ∑ s ∈ (c r).support, (s : ℝ) ≤ ∑ r : R, ∑ s ∈ (c r).support, (s : ℝ) :=
      Finset.single_le_sum (f := fun r : R => ∑ s ∈ (c r).support, (s : ℝ))
        (fun _ _ => Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ r)
    linarith
  have hvec : ∀ x, D.vecL (cx x) = ∑ r, x r • D.vecL (c r) := fun x => by
    simp only [cx, map_sum, map_smul]
  set Tx : (R → ℝ) → D.L2 := fun x => ∑ r, x r • D.Tvec r.1
  have hTx : ∀ x i, Tx x i = I * ((∑ r : R, x r * (D.e1 r.1 i - D.e2 r.1 i) : ℝ) : ℂ) := by
    intro x i
    have e : Tx x i = ∑ r : R, (x r : ℂ) * D.Tfun r.1 i := by
      simp only [Tx]
      rw [lp.coeFn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]; rfl
    rw [e]
    simp only [NegData.Tfun]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hval : ∀ (x : R → ℝ) (r : R), (∑ s : R, x s * (D.e1 s.1 r.1 - D.e2 s.1 r.1)) = x r := by
    intro x r
    rw [Finset.sum_eq_single r]
    · rw [D.e1_self, D.e2_self (hRoff r.1 r.2)]; ring
    · intro s _ hsr
      have hne : r.1 ≠ s.1 := fun e => hsr (Subtype.ext e.symm)
      obtain ⟨h1, h2⟩ := D.e_other (hdist s.1 s.2 r.1 r.2 (Ne.symm hne))
      rw [h1, h2]; ring
    · intro h; exact absurd (Finset.mem_univ r) h
  have hBT : ∀ x, D.Bre (Tx x) (Tx x) ≤ -∑ r, x r ^ 2 := by
    intro x
    set f : D.ι → ℝ := fun i => ∑ r : R, x r * (D.e1 r.1 i - D.e2 r.1 i)
    have hs := D.hasSum_Bre (Tx x) (Tx x)
    have e : (fun i => (Tx x i * Tx x i).re) = fun i => -(f i ^ 2) := by
      funext i; rw [hTx]; simp [f, Complex.mul_re]; ring
    rw [e] at hs
    have hs' : HasSum (fun i => f i ^ 2) (-D.Bre (Tx x) (Tx x)) := by simpa using hs.neg
    have hle : ∑ i ∈ R, f i ^ 2 ≤ -D.Bre (Tx x) (Tx x) :=
      hs'.summable.sum_le_tsum R (fun _ _ => sq_nonneg _) |>.trans_eq hs'.tsum_eq
    have hR : ∑ i ∈ R, f i ^ 2 = ∑ r : R, x r ^ 2 := by
      rw [← Finset.sum_coe_sort R]
      exact Finset.sum_congr rfl fun r _ => by simp only [f]; rw [hval]
    linarith
  have hBre : ∀ x, x ≠ 0 → D.Bre (D.vecL (cx x)) (D.vecL (cx x)) < 0 := by
    intro x hx
    set S : ℝ := ∑ r, |x r|
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hd : ‖D.vecL (cx x) - Tx x‖ ≤ ε * S := by
      rw [hvec, show (∑ r, x r • D.vecL (c r)) - Tx x = ∑ r, x r • (D.vecL (c r) - D.Tvec r.1) by
        simp only [Tx, smul_sub, Finset.sum_sub_distrib]]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_comm ε]
      exact mul_le_mul_of_nonneg_left (hc r).le (abs_nonneg _)
    have hT : ‖Tx x‖ ≤ C * S := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_comm C]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact Finset.single_le_sum (f := fun r : R => ‖D.Tvec r.1‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ r)
    have hY : ‖D.vecL (cx x)‖ ≤ C * S + ε * S := by
      have := norm_sub_norm_le (D.vecL (cx x)) (Tx x)
      linarith
    have herr := D.abs_Bre_sub_le (D.vecL (cx x)) (Tx x)
    have herr' : |D.Bre (D.vecL (cx x)) (D.vecL (cx x)) - D.Bre (Tx x) (Tx x)|
        ≤ ε * (2 * C + ε) * S ^ 2 := by
      refine herr.trans ?_
      calc ‖D.vecL (cx x) - Tx x‖ * (‖D.vecL (cx x)‖ + ‖Tx x‖)
          ≤ (ε * S) * ((C * S + ε * S) + C * S) :=
            mul_le_mul hd (by linarith) (by positivity) (by positivity)
        _ = ε * (2 * C + ε) * S ^ 2 := by ring
    have hCS : S ^ 2 ≤ m * ∑ r, x r ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun r : R => |x r|)
      simpa [sq_abs, S, m] using this
    have hpos : 0 < ∑ r, x r ^ 2 := by
      obtain ⟨r, hr⟩ := Function.ne_iff.1 hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨r, Finset.mem_univ r, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hr))⟩
    have hB := hBT x
    have h3 : ε * (2 * C + ε) * S ^ 2 ≤ ε * (2 * C + ε) * m * ∑ r, x r ^ 2 := by
      rw [mul_assoc (ε * (2 * C + ε))]
      exact mul_le_mul_of_nonneg_left hCS (by positivity)
    have h4 : ε * (2 * C + ε) * m * ∑ r, x r ^ 2 < ∑ r, x r ^ 2 := by
      nlinarith
    have := (abs_le.1 herr').2
    linarith
  let L : (R → ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
    { toFun := fun x => twinComb (cx x)
      map_add' := fun x y => by
        simp only [cx, Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
      map_smul' := fun t x => by
        simp only [cx, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul,
          RingHom.id_apply] }
  have hLQ : ∀ x, D.Q A (L x) = D.w * D.Bre (D.vecL (cx x)) (D.vecL (cx x)) := fun x =>
    D.Q_eq_Bre (hfits x) hA
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h0 : D.vecL (cx x) = 0 := by
      ext i
      rw [D.vecL_apply, NegData.G0, ← ghatC_twinComb (hfits x)]
      have : twinComb (cx x) = fun _ => 0 := hx
      rw [this, ghatC_zero_fun]; simp
    have := hBre x hx0
    rw [h0] at this
    simp [NegData.Bre] at this
  refine ⟨A, hA, LinearMap.range L, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  · rintro v ⟨x, rfl⟩
    exact ⟨twinComb_probe (hfits x), D.good (hfits x)⟩
  · rintro v ⟨x, rfl⟩ hv
    have hx : x ≠ 0 := fun h => hv (by rw [h, map_zero])
    rw [hLQ]; exact mul_neg_of_pos_of_neg D.w_pos (hBre x hx)


/-! ## ζ as an instance -/

/-- **ζ's zeros as negative-index data** (`κ = 1`, `w = 1`, the width-1 strip test). -/
def zetaND : NegData where
  ι := ZIdx
  t := tz
  κ := 1
  κ_pos := one_pos
  t_im := fun i => by
    obtain ⟨h0, h1⟩ := i.1.2.mem_strip
    have e : zetaZeroFamily i = i.1.1 := rfl
    show |((zetaZeroFamily i - 1 / 2) / I).im| < 1 / 2
    rw [im_ordinate, e, abs_lt]; constructor <;> linarith
  t_re_ne := fun i h => im_poleP_ne i (by
    rw [← two_I_ordi]; show ((2 : ℂ) * I * tz i).im = 0
    rw [show ∀ z : ℂ, ((2 : ℂ) * I * z).im = 2 * z.re from fun z => by simp, h, mul_zero])
  finite_t := fun R => (finite_poleP (2 * R)).subset fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    rw [← two_I_ordi]
    simp only [norm_mul, Complex.norm_I, Complex.norm_two]
    have : ‖ordi zetaZeroFamily i‖ = ‖tz i‖ := rfl
    linarith
  summable_G0 := by
    simp only [Complex.ofReal_one, one_mul]
    exact summable_cw.congr fun q => by rw [cw, norm_pow]
  Q := weilQ
  w := 1
  w_pos := one_pos
  Good := fun a v => ∃ K, StripTest (fun z => ghatC v a z ^ 2) K
  hasSum := fun h hA => by
    simp only [Complex.ofReal_one, one_mul]
    exact hasSum_twinComb h hA
  good := fun h => striptest_twinComb h

/-- **Every off-line quadruple gives a negative direction of Weil's form.** For any finite set `R` of
off-line zeros of ζ in pairwise different quadruples, some support `a` has a space `V` of strip-test
probes with `dim V = |R|` on which `Q` is negative definite. Nothing is assumed about the other
zeros. -/
theorem negDirections_offline (R : Finset ZIdx)
    (hRoff : ∀ r ∈ R, (zetaZeroFamily r).re ≠ 1 / 2)
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tz s) (tz r)) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 :=
  zetaND.negDirections R (fun r hr => by
    show ((zetaZeroFamily r - 1 / 2) / I).im ≠ 0
    rw [im_ordinate]; intro h; exact hRoff r hr (by linarith)) hdist

theorem exists_reps
    (hinf : ∀ F : Finset ZIdx, ∃ i, (zetaZeroFamily i).re ≠ 1 / 2 ∧ ∀ r ∈ F, ¬Orb (tz i) (tz r)) :
    ∀ m : ℕ, ∃ R : Finset ZIdx, R.card = m ∧ (∀ r ∈ R, (zetaZeroFamily r).re ≠ 1 / 2) ∧
      ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tz s) (tz r)
  | 0 => ⟨∅, rfl, by simp, by simp⟩
  | m + 1 => by
    classical
    obtain ⟨R, hcard, hoff, hd⟩ := exists_reps hinf m
    obtain ⟨i, hi, hnew⟩ := hinf R
    have hiR : i ∉ R := fun h => hnew i h (Or.inl rfl)
    refine ⟨insert i R, by rw [Finset.card_insert_of_notMem hiR, hcard], ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.1 hr with hr | hr
      · rw [hr]; exact hi
      · exact hoff r hr
    · intro r hr s hs hrs
      rcases Finset.mem_insert.1 hr with hr | hr <;> rcases Finset.mem_insert.1 hs with hs | hs
      · exact absurd (hr.trans hs.symm) hrs
      · rw [hr]; exact fun h => hnew s hs (orb_symm h)
      · rw [hs]; exact hnew r hr
      · exact hd r hr s hs hrs

/-- **Infinitely many off-line quadruples make the negative index unbounded.** If no finite set of
quadruples holds every off-line zero of ζ, then for every `m` some support has an `m`-dimensional space
of strip-test probes on which `Q` is negative definite. -/
theorem negDirections_unbounded
    (hinf : ∀ F : Finset ZIdx, ∃ i, (zetaZeroFamily i).re ≠ 1 / 2 ∧ ∀ r ∈ F, ¬Orb (tz i) (tz r))
    (m : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = m ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 := by
  obtain ⟨R, hcard, hoff, hd⟩ := exists_reps hinf m
  rw [← hcard]
  exact negDirections_offline R hoff hd

end Pilot1ca

#print axioms Pilot1ca.ghatC_twinComb
#print axioms Pilot1ca.NegData.inner_Tvec_eq_zero
#print axioms Pilot1ca.NegData.Tvec_mem_closure
#print axioms Pilot1ca.NegData.negDirections
#print axioms Pilot1ca.negDirections_offline
#print axioms Pilot1ca.negDirections_unbounded
