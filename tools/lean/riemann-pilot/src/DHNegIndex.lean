import Mathlib
import WeilIndexInfinite
import DHColumn
import DHRealAxis
import DHForm

/-! # Every off-line quadruple of `dh` gives a negative direction of `Q_dh` (round 266)

Round 232's `negDirections_offline` (WeilIndexInfinite.lean §B–E) ported to the Davenport–Heilbronn
function: for a finite set `R` of off-line zeros `τ_r` of `Ξ₃` (`(tau3 r).im ≠ 0`), pairwise in
different quadruples (`¬Orb`), there is a support `a` and an `|R|`-dimensional space `V` of probes at
support `a`, each passing the width-3 strip test, on which `Q_dh = QDHu` is negative definite
(`negDirections_offline_dh`). The dh inputs replacing the ζ datum: the pole family `P_r = 2iτ_r`
with `|Re P_r| < 1` (`tau3_im_lt`) and `Im P_r ≠ 0` (`XiDH_I_mul_ne_zero`: no zero of `Ξ_dh` on
`iℝ`), local finiteness from `hadamard_XiDH3`, `Σ‖ĝ₀(3τ_r)‖² < ∞` and the explicit formula on twin
combinations from `QDHu_hasSum` with a width-3 strip test for twin combinations
(`striptest_twinComb3`), and `Q_dh(twinComb c) = 2·Bre(v, v)` (`QDH_eq_BreD`: the weight `2` of
`QDHu_hasSum`, one index per pair `±τ`). §B–E are round 232's text with `tz ↦ tau3`,
`poleP ↦ 2i·tau3`, `weilQ ↦ QDHu`; TwinLandau's kernels are reused unchanged (the twin shifts are
reparametrised as `s = 2l/3`, `vfunD_eq`). **The payoff** (`negIndex_ge_of_located`): `n` located
off-line zeros — `‖ρ_k − c_k‖ < 1/100` with centres `c_k` right of `Re s = 1/100`, at least `1/100`
from the line and pairwise at least `2/100` from each other's quadruple images — give an
`n`-dimensional negative space of `Q_dh`, at every larger support (`negIndex_ge_mono`). Not ported:
`negDirections_above`, `negDirections_of_quadruples`, `negIndex_eq_quadruples` (rounds 230–231), whose
finiteness hypotheses fail for `dh` (infinitely many off-line zeros). -/

open Real Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace DHNegIndex

open Pilot1ca Pilot1bt PilotWeil PsiOmega

abbrev ZD := ZeroIdx (sqF XiDH3)

/-! ### (1) `Im P ≠ 0`: no zero of `Ξ₃` on the imaginary axis -/

theorem tau3_re_ne (i : ZD) : (tau3 i).re ≠ 0 := by
  intro h
  have hz := XiDH3_tau i
  have e : (3 : ℂ) * tau3 i = I * ((3 * (tau3 i).im : ℝ) : ℂ) :=
    Complex.ext (by simp [h]) (by simp)
  unfold XiDH3 at hz
  rw [e] at hz
  exact XiDH_I_mul_ne_zero _ hz

/-! ### (2) the pole family `P = 2i·τ` -/

def PD (i : ZD) : ℂ := 2 * I * tau3 i

theorem re_PD (i : ZD) : (PD i).re = -(2 * (tau3 i).im) := by simp [PD]

theorem im_PD (i : ZD) : (PD i).im = 2 * (tau3 i).re := by simp [PD]

theorem abs_re_PD (i : ZD) : |(PD i).re| < 1 := by
  rw [re_PD, abs_neg, abs_mul, abs_two]
  have := tau3_im_lt i; linarith

theorem im_PD_ne (i : ZD) : (PD i).im ≠ 0 := by
  rw [im_PD]; exact mul_ne_zero two_ne_zero (tau3_re_ne i)

/-- Local finiteness from the Hadamard product of `Ξ₃` (the column of `finite_poleP`). -/
theorem finite_PD (R : ℝ) : {i : ZD | ‖PD i‖ ≤ R}.Finite := by
  have hs : Summable fun i : ZD => ‖i.1⁻¹‖ := hadamard_XiDH3.summ
  set K : ℝ := max (R ^ 2 / 4) 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : {i : ZD | ‖i.1‖ ≤ K}.Finite := by
    have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (inv_pos.2 hK))
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq, not_lt]
    rw [norm_inv]
    have hi' : ‖i.1‖ ≤ K := hi
    have hp : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdx3_ne_zero i)
    exact inv_anti₀ hp hi'
  refine hfin.subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq] at hi ⊢
  have e1 : ‖PD i‖ = 2 * ‖tau3 i‖ := by unfold PD; rw [norm_mul, norm_mul]; simp
  have e2 : ‖i.1‖ = ‖tau3 i‖ ^ 2 := by rw [← tau3_sq, norm_pow]
  rw [e2]
  have h0 := norm_nonneg (tau3 i)
  have : ‖tau3 i‖ ^ 2 ≤ R ^ 2 / 4 := by nlinarith
  exact this.trans (le_max_left _ _)

/-! ### (3) `Σ‖ĝ₀(τ)‖² < ∞` from the dh explicit formula at the box -/

def G0D (i : ZD) : ℂ := ghatC (box 1) 1 (3 * tau3 i)

theorem summable_G0D_sq : Summable fun i : ZD => ‖G0D i‖ ^ 2 := by
  have hp := box_probe 1
  obtain ⟨C, hC⟩ := striptest_antitone3 one_pos hp.even (box_antitone' 1) (box_nonneg' 1)
    hp.intervalIntegrable
  have h := QDHu_hasSum hp one_pos hC
  have hs : Summable fun i : ZD => ‖2 * ghatC (box 1) 1 (3 * tau3 i) ^ 2‖ :=
    summable_norm_iff.2 h.summable
  refine (hs.div_const 2).congr fun i => ?_
  simp only [G0D, norm_mul, norm_pow, Complex.norm_two]; ring

theorem twinPoles_dh : TwinLandau.TwinPoles PD (fun i => G0D i ^ 2) :=
  ⟨summable_G0D_sq.congr fun i => by rw [norm_pow], abs_re_PD, im_PD_ne, finite_PD⟩

/-- The raw width-3 strip bound inside `striptest_antitone3`. -/
theorem ghat3_antitone_bound {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hev : ∀ u, g (-u) = g u)
    (hmono : AntitoneOn g (Set.Icc 0 a)) (hnn : ∀ u ∈ Set.Icc 0 a, 0 ≤ g u)
    (hint : IntervalIntegrable g volume (-a) a) :
    ∃ K, ∀ t ∈ PilotWeil.strip (-1) 1, ‖ghatC g a (3 * t)‖ ^ 2 * (1 + t.re ^ 2) ≤ K := by
  have hg0 : 0 ≤ g 0 := hnn 0 ⟨le_rfl, ha.le⟩
  refine ⟨(Real.exp (3 * a) * ∫ u in (-a)..a, |g u|) ^ 2
      + (2 * g 0 * Real.cosh (3 * a) / 3) ^ 2, fun t ht => ?_⟩
  have h3im : (3 * t).im = 3 * t.im := by simp
  have htim : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h3 : |(3 * t).im| ≤ 3 := by
    rw [h3im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
  refine sq_strip_bound (G := fun z => ghatC g a (3 * z)) ?_ ?_
  · refine (norm_ghatC_le_exp_im ha.le hint _).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _)
    linarith [mul_le_mul_of_nonneg_left h3 ha.le]
  · rcases eq_or_ne t 0 with rfl | ht0
    · simp; positivity
    have h3t : (3 : ℂ) * t ≠ 0 := mul_ne_zero (by norm_num) ht0
    have hb := norm_ghatC_le_of_antitone ha hev hmono hnn h3t
    have hn3 : ‖(3 : ℂ) * t‖ = 3 * ‖t‖ := by rw [norm_mul]; norm_num
    rw [hn3] at hb
    have hc : Real.cosh (a * |(3 * t).im|) ≤ Real.cosh (3 * a) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg ha.le (abs_nonneg _)),
        abs_of_pos (by linarith : (0 : ℝ) < 3 * a)]
      linarith [mul_le_mul_of_nonneg_left h3 ha.le]
    have htn : 0 < ‖t‖ := norm_pos_iff.2 ht0
    calc ‖t‖ * ‖ghatC g a (3 * t)‖
        ≤ ‖t‖ * (2 * g 0 * Real.cosh (a * |(3 * t).im|) / (3 * ‖t‖)) :=
          mul_le_mul_of_nonneg_left hb htn.le
      _ = 2 * g 0 * Real.cosh (a * |(3 * t).im|) / 3 := by field_simp
      _ ≤ 2 * g 0 * Real.cosh (3 * a) / 3 := by gcongr

/-- **Twin combinations pass the width-3 strip test.** -/
theorem striptest_twinComb3 {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) :
    ∃ K, StripTest (fun z => ghatC (twinComb c) A (3 * z) ^ 2) K := by
  have hp := box_probe 1
  obtain ⟨C, hC⟩ := ghat3_antitone_bound one_pos hp.even (box_antitone' 1) (box_nonneg' 1)
    hp.intervalIntegrable
  set M : ℝ := ∑ s ∈ c.support, |c s| * (2 * Real.exp (3 * s))
  have hm : ∀ t ∈ PilotWeil.strip (-1) 1, ‖mulC (3 * t) c‖ ≤ M := by
    intro t ht
    rw [mulC_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ((norm_two_cos_le _).trans ?_) (abs_nonneg _)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) two_pos.le
    have e : (((s : ℝ) : ℂ) * (3 * t)).im = s * (3 * t.im) := by simp
    rw [e, abs_mul, abs_of_nonneg (NNReal.coe_nonneg s), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    nlinarith [NNReal.coe_nonneg s, abs_nonneg t.im]
  have hd : Differentiable ℂ fun z => mulC (3 * z) c := by
    have e : (fun z => mulC (3 * z) c)
        = fun z => ∑ s ∈ c.support, (c s : ℂ) * (2 * Complex.cos ((s : ℝ) * (3 * z))) :=
      funext fun z => mulC_apply (3 * z) c
    rw [e]; fun_prop
  have hdG : Differentiable ℂ fun z => ghatC (box 1) 1 (3 * z) :=
    (ghatC_differentiable hp.intervalIntegrable).comp (differentiable_id.const_mul 3)
  have hT := striptest_mul_sq (G := fun z => ghatC (box 1) 1 (3 * z))
    (m := fun z => mulC (3 * z) c) hdG hd hC hm
  have e : (fun z => ghatC (twinComb c) A (3 * z) ^ 2)
      = fun z => (mulC (3 * z) c * ghatC (box 1) 1 (3 * z)) ^ 2 :=
    funext fun z => by rw [ghatC_twinComb h]
  exact ⟨_, e ▸ hT⟩

theorem hasSum_twinComb_dh {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) (hA : 0 < A) :
    HasSum (fun i : ZD => 2 * (mulC (3 * tau3 i) c * G0D i) ^ 2) (QDHu (twinComb c) : ℂ) := by
  obtain ⟨K, hK⟩ := striptest_twinComb3 h
  have := QDHu_hasSum (twinComb_probe h) hA hK
  convert this using 2 with i
  rw [ghatC_twinComb h]; rfl

/-! ### (5) the countable index -/

instance : Countable ZD := countable_ZeroIdx3

/-! ### (6) a located zero gives an off-line index -/

theorem ordinate3_im (ρ : ℂ) : ((ρ - 1 / 2) / (3 * I)).im = -(ρ.re - 1 / 2) / 3 := by
  have e : (ρ - 1 / 2) / (3 * I) = -I * (ρ - 1 / 2) / 3 := by
    field_simp; linear_combination (2 * ρ - 1) * I_sq
  rw [e]; simp

theorem idx_of_located {ρ c : ℂ} (hρ : dh ρ = 0) (hc : ‖ρ - c‖ < 1 / 100)
    (hre : 1 / 100 ≤ c.re) (hoff : 1 / 100 ≤ |c.re - 1 / 2|) :
    ∃ i : ZD, (tau3 i = (ρ - 1 / 2) / (3 * I) ∨ tau3 i = -((ρ - 1 / 2) / (3 * I)))
      ∧ (tau3 i).im ≠ 0 := by
  have h1 : |ρ.re - c.re| < 1 / 100 := by
    have := (Complex.abs_re_le_norm (ρ - c)).trans_lt hc; simpa using this
  have h0 : 0 < ρ.re := by have := (abs_lt.1 h1).1; linarith
  have hne : ρ.re ≠ 1 / 2 := by
    intro h; rw [h] at h1; rw [abs_sub_comm] at h1; linarith
  obtain ⟨i, hi⟩ := tau3_of_dh_zero hρ h0
  refine ⟨i, hi, ?_⟩
  have hw : ((ρ - 1 / 2) / (3 * I)).im ≠ 0 := by
    rw [ordinate3_im]; intro h; apply hne; linarith
  rcases hi with hi | hi <;> rw [hi]
  · exact hw
  · rw [neg_im]; exact neg_ne_zero.2 hw

theorem orb_neg_left {t w : ℂ} (h : Orb t w) : Orb (-t) w := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (neg_neg _)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (neg_neg _)))

theorem orb_neg_right {t w : ℂ} (h : Orb t w) : Orb t (-w) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (neg_neg _).symm)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (by rw [map_neg, neg_neg])))
  · exact Or.inr (Or.inr (Or.inl (by rw [map_neg])))

/-- The orbit of `±(ρ − ½)/3i` under `±`, conjugation is the quadruple `{ρ, 1 − ρ, ρ̄, 1 − ρ̄}`. -/
theorem quad_of_orb {ρ ρ' : ℂ} {t t' : ℂ}
    (ht : t = (ρ - 1 / 2) / (3 * I) ∨ t = -((ρ - 1 / 2) / (3 * I)))
    (ht' : t' = (ρ' - 1 / 2) / (3 * I) ∨ t' = -((ρ' - 1 / 2) / (3 * I)))
    (h : Orb t' t) :
    ρ' = ρ ∨ ρ' = 1 - ρ ∨ ρ' = conj ρ ∨ ρ' = 1 - conj ρ := by
  have hI : (3 : ℂ) * I ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
  have hc : conj ((ρ - 1 / 2) / (3 * I)) = -((conj ρ - 1 / 2) / (3 * I)) := by
    rw [map_div₀, map_sub, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat, map_ofNat,
      mul_neg, div_neg]
  have key : Orb ((ρ' - 1 / 2) / (3 * I)) ((ρ - 1 / 2) / (3 * I)) := by
    rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
    · exact h
    · simpa using orb_neg_left h
    · simpa using orb_neg_right h
    · simpa using orb_neg_left (orb_neg_right h)
  have cancel : ∀ x y : ℂ, x / (3 * I) = y / (3 * I) → x = y := fun x y e => by
    have := congrArg (· * (3 * I)) e
    simpa [div_mul_cancel₀ _ hI] using this
  rcases key with e | e | e | e
  · left; have := cancel _ _ e; linear_combination this
  · right; left
    have : ρ' - 1 / 2 = -(ρ - 1 / 2) := cancel _ _ (by rw [e, neg_div])
    linear_combination this
  · right; right; right
    rw [hc] at e
    have : ρ' - 1 / 2 = -(conj ρ - 1 / 2) := cancel _ _ (by rw [e, neg_div])
    linear_combination this
  · right; right; left
    rw [hc, neg_neg] at e
    have := cancel _ _ e
    linear_combination this


/-! ## Port of round 232 (`WeilIndexInfinite.lean` §B–E) to `dh` -/

/-! ### B. `ℓ²` over the zeros of `Ξ₃` -/

abbrev L2D := lp (fun _ : ZD => ℂ) 2

theorem memℓp_twoD {f : ZD → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2) : Memℓp f 2 :=
  memℓp_gen (by simpa using hf)

theorem sq_summableD (a : L2D) : Summable fun i => ‖a i‖ ^ 2 := by
  simpa using (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem summable_mul_of_sqD {f g : ZD → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2)
    (hg : Summable fun i => ‖g i‖ ^ 2) : Summable fun i => ‖f i * g i‖ :=
  ((hf.add hg).div_const 2).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => by
    rw [norm_mul]; have := two_mul_le_add_sq ‖f i‖ ‖g i‖; linarith

theorem tau3_mem_strip (i : ZD) : tau3 i ∈ PilotWeil.strip (-1) 1 := by
  have := abs_le.1 (tau3_im i)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

def vfunD (s : ℝ) (i : ZD) : ℂ := 2 * Complex.cos (s * (3 * tau3 i)) * G0D i

theorem vfunD_eq (l : ℝ) (i : ZD) :
    vfunD (2 * l / 3) i = 2 * Complex.cos (((2 * l : ℝ) : ℂ) * tau3 i) * G0D i := by
  unfold vfunD
  rw [show (((2 * l / 3 : ℝ) : ℂ)) * (3 * tau3 i) = ((2 * l : ℝ) : ℂ) * tau3 i by push_cast; ring]

theorem norm_vfunD_le {s : ℝ} (hs : 0 ≤ s) (i : ZD) :
    ‖vfunD s i‖ ≤ 2 * Real.exp (3 * s) * ‖G0D i‖ := by
  rw [vfunD, norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_two_cos_le _).trans ?_) (norm_nonneg _)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) two_pos.le
  have e : ((s : ℂ) * (3 * tau3 i)).im = s * (3 * (tau3 i).im) := by simp
  rw [e, abs_mul, abs_of_nonneg hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have := tau3_im i
  nlinarith [abs_nonneg (tau3 i).im]

theorem summable_vfunD_sq {s : ℝ} (hs : 0 ≤ s) : Summable fun i => ‖vfunD s i‖ ^ 2 :=
  (summable_G0D_sq.mul_left ((2 * Real.exp (3 * s)) ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _) fun i => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_vfunD_le hs i) 2

def vecSD (s : NNReal) : L2D := ⟨vfunD s, memℓp_twoD (summable_vfunD_sq (NNReal.coe_nonneg s))⟩

def vecLD : (NNReal →₀ ℝ) →ₗ[ℝ] L2D := Finsupp.linearCombination ℝ vecSD

theorem vecLD_apply (c : NNReal →₀ ℝ) (i : ZD) : vecLD c i = mulC (3 * tau3 i) c * G0D i := by
  rw [vecLD, Finsupp.linearCombination_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply, mulC_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
  show (c s : ℂ) * vfunD s i = _
  rw [vfunD]; ring

def BreD (u w : L2D) : ℝ := ⟪star u, w⟫_ℝ

theorem hasSum_BreD (u w : L2D) : HasSum (fun i => (u i * w i).re) (BreD u w) := by
  have := lp.hasSum_inner (𝕜 := ℝ) (star u) w
  unfold BreD
  convert this using 2 with i
  rw [lp.star_apply, Complex.inner]
  simp [mul_comm]

theorem abs_BreD_le (u w : L2D) : |BreD u w| ≤ ‖u‖ * ‖w‖ := by
  have := abs_real_inner_le_norm (star u) w
  rwa [norm_star] at this

theorem BreD_sub_left (u v w : L2D) : BreD (u - v) w = BreD u w - BreD v w := by
  unfold BreD; rw [star_sub, inner_sub_left]

theorem BreD_sub_right (u v w : L2D) : BreD u (v - w) = BreD u v - BreD u w := by
  unfold BreD; rw [inner_sub_right]

theorem abs_BreD_sub_le (y t : L2D) : |BreD y y - BreD t t| ≤ ‖y - t‖ * (‖y‖ + ‖t‖) := by
  have e : BreD y y - BreD t t = BreD (y - t) y + BreD t (y - t) := by
    rw [BreD_sub_left, BreD_sub_right]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_BreD_le (y - t) y
  have h2 := abs_BreD_le t (y - t)
  nlinarith [norm_nonneg (y - t), norm_nonneg t]

/-- **`Q_dh` is twice `Bre` of the probe's vector** (the weight `2` of `QDH_hasSum`). -/
theorem QDH_eq_BreD {c : NNReal →₀ ℝ} {A : ℝ} (h : Fits c A) (hA : 0 < A) :
    QDHu (twinComb c) = 2 * BreD (vecLD c) (vecLD c) := by
  have h1 := Complex.hasSum_re (hasSum_twinComb_dh h hA)
  rw [Complex.ofReal_re] at h1
  refine h1.unique ?_
  convert (hasSum_BreD (vecLD c) (vecLD c)).mul_left 2 using 2 with i
  rw [vecLD_apply, ← sq]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; ring

/-! ### C. The targets -/

theorem PD_eq (q : ZD) : PD q = 2 * I * tau3 q := rfl

theorem conj_PD (q : ZD) : (starRingEnd ℂ) (PD q) = -(2 * I * (starRingEnd ℂ) (tau3 q)) := by
  rw [PD_eq, map_mul, map_mul, Complex.conj_I, map_ofNat]; ring

def e1D (r i : ZD) : ℝ := TwinLandau.indR (PD r) (PD i)

def e2D (r i : ZD) : ℝ := TwinLandau.indR (PD r) (-(starRingEnd ℂ) (PD i))

theorem e1D_eq_zero {r i : ZD} (h : ‖PD r‖ < ‖PD i‖) : e1D r i = 0 := by
  by_contra h0; have := norm_eq_of_indR h0; linarith

theorem e2D_eq_zero {r i : ZD} (h : ‖PD r‖ < ‖PD i‖) : e2D r i = 0 := by
  by_contra h0; have := norm_eq_of_indR h0; rw [norm_neg, Complex.norm_conj] at this; linarith

def nearD (r : ZD) : Finset ZD := (finite_PD ‖PD r‖).toFinset

theorem not_nearD {r i : ZD} (h : i ∉ nearD r) : ‖PD r‖ < ‖PD i‖ := by
  rw [nearD, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at h; exact h

def TfunD (r i : ZD) : ℂ := I * ((e1D r i - e2D r i : ℝ) : ℂ)

theorem TfunD_eq_zero {r i : ZD} (h : i ∉ nearD r) : TfunD r i = 0 := by
  rw [TfunD, e1D_eq_zero (not_nearD h), e2D_eq_zero (not_nearD h)]; simp

def TvecD (r : ZD) : L2D :=
  ⟨TfunD r, memℓp_twoD (summable_of_ne_finset_zero (s := nearD r) fun i hi => by
    rw [TfunD_eq_zero hi, norm_zero]; norm_num)⟩

theorem e1D_self {r : ZD} : e1D r r = 1 := by
  have h : -PD r ≠ PD r := fun e => im_PD_ne r (by
    have := congrArg Complex.im e; simp at this; linarith)
  simp [e1D, TwinLandau.indR, h]

theorem e2D_self {r : ZD} (hr : (tau3 r).im ≠ 0) : e2D r r = 0 := by
  have h1 : -(starRingEnd ℂ) (PD r) ≠ PD r := fun e => hr (by
    have := congrArg Complex.re e; simp at this; rw [re_PD] at this; linarith)
  have h2 : -(-(starRingEnd ℂ) (PD r)) ≠ PD r := fun e => im_PD_ne r (by
    have := congrArg Complex.im e; simp at this; linarith)
  simp only [e2D, TwinLandau.indR, h1, h2, ↓reduceIte]; norm_num

theorem eD_other {r s : ZD} (h : ¬Orb (tau3 r) (tau3 s)) : e1D s r = 0 ∧ e2D s r = 0 := by
  simp only [Orb, not_or] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have c1 : PD r ≠ PD s := fun e => h1 (cancel_two_I (by rw [← PD_eq, ← PD_eq, e]))
  have c2 : -PD r ≠ PD s := fun e => h2 (cancel_two_I (by
    rw [PD_eq, PD_eq] at e; linear_combination -e))
  have c3 : -(starRingEnd ℂ) (PD r) ≠ PD s := fun e => h3 (by
    rw [conj_PD, PD_eq, neg_neg] at e
    have := cancel_two_I e
    rw [← this, Complex.conj_conj])
  have c4 : -(-(starRingEnd ℂ) (PD r)) ≠ PD s := fun e => h4 (by
    rw [neg_neg, conj_PD, PD_eq] at e
    have := cancel_two_I (a := (starRingEnd ℂ) (tau3 r)) (b := -tau3 s) (by linear_combination -e)
    rw [← Complex.conj_conj (tau3 r), this, map_neg])
  refine ⟨?_, ?_⟩
  · simp [e1D, TwinLandau.indR, c1, c2]
  · simp only [e2D, TwinLandau.indR, c3, c4, ↓reduceIte]; norm_num

theorem G0D_e1 (r i : ZD) : G0D i * (e1D r i : ℂ) = G0D r * (e1D r i : ℂ) := by
  by_cases h1 : PD i = PD r
  · rw [G0D, G0D, show tau3 i = tau3 r from cancel_two_I (by rw [← PD_eq, ← PD_eq, h1])]
  by_cases h2 : -PD i = PD r
  · rw [PD_eq, PD_eq] at h2
    have : tau3 i = -tau3 r := cancel_two_I (by linear_combination -h2)
    rw [G0D, G0D, this, mul_neg, ghatC_even (box_probe 1).even]
  simp [e1D, TwinLandau.indR, h1, h2]

theorem G0D_e2 (r i : ZD) : (starRingEnd ℂ) (G0D i) * (e2D r i : ℂ) = G0D r * (e2D r i : ℂ) := by
  have hc : (starRingEnd ℂ) (G0D i) = ghatC (box 1) 1 (3 * (starRingEnd ℂ) (tau3 i)) := by
    have := (ghatC_conj (box_probe 1).even zero_le_one (3 * tau3 i)).symm
    rwa [map_mul, map_ofNat] at this
  by_cases h1 : -(starRingEnd ℂ) (PD i) = PD r
  · have h1' := h1
    rw [conj_PD, PD_eq, neg_neg] at h1'
    rw [hc, cancel_two_I h1']; rfl
  by_cases h2 : -(-(starRingEnd ℂ) (PD i)) = PD r
  · have h2' := h2
    rw [neg_neg, conj_PD, PD_eq] at h2'
    have : (starRingEnd ℂ) (tau3 i) = -tau3 r := cancel_two_I (by linear_combination -h2')
    rw [hc, this, mul_neg, ghatC_even (box_probe 1).even]; rfl
  have h2' : ¬(starRingEnd ℂ) (PD i) = PD r := by simpa using h2
  simp [e2D, TwinLandau.indR, h1, h2']

/-! ### D. Density of the twin vectors -/

theorem summable_of_sq_mulD {f g : ZD → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2)
    (hg : Summable fun i => ‖g i‖ ^ 2) : Summable fun i => f i * g i :=
  (summable_mul_of_sqD hf hg).of_norm

theorem summable_conj_sqD (a : L2D) : Summable fun i => ‖(starRingEnd ℂ) (a i)‖ ^ 2 := by
  simpa using sq_summableD a

theorem summable_eD {r : ZD} {f : ZD → ℂ} {e : ZD → ℝ} (he : ∀ i, i ∉ nearD r → e i = 0) :
    Summable fun i => f i * (e i : ℂ) :=
  summable_of_ne_finset_zero (s := nearD r) fun i hi => by rw [he i hi]; simp

theorem inner_TvecD_eq_zero (a : L2D) (ha : ∀ s : NNReal, ⟪vecSD s, a⟫_ℝ = 0) {r : ZD}
    (hr : (tau3 r).im ≠ 0) : ⟪a, TvecD r⟫_ℝ = 0 := by
  classical
  set Pz : ZD ⊕ ZD → ℂ := Sum.elim PD fun i => -(starRingEnd ℂ) (PD i)
  set cz : ZD ⊕ ZD → ℂ :=
    Sum.elim (fun i => G0D i * (starRingEnd ℂ) (a i)) fun i => (starRingEnd ℂ) (G0D i) * a i
  have hsa := sq_summableD a
  have hsg := summable_G0D_sq
  have hsgc : Summable fun i => ‖(starRingEnd ℂ) (G0D i)‖ ^ 2 := by simpa using hsg
  have hD : TwinLandau.TwinPoles Pz cz := by
    refine ⟨Summable.sum (f := fun q => ‖cz q‖) (summable_mul_of_sqD hsg (summable_conj_sqD a))
      (summable_mul_of_sqD hsgc hsa), fun q => ?_, fun q => ?_, fun R => ?_⟩
    · rcases q with i | i
      · exact abs_re_PD i
      · simpa [Pz] using abs_re_PD i
    · rcases q with i | i
      · exact im_PD_ne i
      · simpa [Pz] using im_PD_ne i
    · refine (((finite_PD R).image Sum.inl).union ((finite_PD R).image Sum.inr)).subset ?_
      rintro (i | i) h
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr ⟨i, by simpa [Pz] using h, rfl⟩
  set SA := ∑' i, G0D i * (starRingEnd ℂ) (a i)
  set SB := ∑' i, (starRingEnd ℂ) (G0D i) * a i
  have hSA : HasSum (fun i => G0D i * (starRingEnd ℂ) (a i)) SA :=
    (summable_of_sq_mulD hsg (summable_conj_sqD a)).hasSum
  have hSB : HasSum (fun i => (starRingEnd ℂ) (G0D i) * a i) SB :=
    (summable_of_sq_mulD hsgc hsa).hasSum
  have hW : ∀ l : ℝ, 0 ≤ l → TwinLandau.Wsum Pz cz l = 2 * SA + 2 * SB := by
    intro l hl
    set s : NNReal := ⟨2 * l / 3, by positivity⟩
    have hv := summable_vfunD_sq (s := 2 * l / 3) (by positivity)
    set X := ∑' i, (starRingEnd ℂ) (a i) * vfunD (2 * l / 3) i
    have hX : HasSum (fun i => (starRingEnd ℂ) (a i) * vfunD (2 * l / 3) i) X :=
      (summable_of_sq_mulD (summable_conj_sqD a) hv).hasSum
    have hXc : HasSum (fun i => a i * (starRingEnd ℂ) (vfunD (2 * l / 3) i)) ((starRingEnd ℂ) X) := by
      have := hX.star
      simpa [mul_comm] using this
    have hXre : X.re = 0 := by
      have h1 := Complex.hasSum_re hX
      have h2 := lp.hasSum_inner (𝕜 := ℝ) (vecSD s) a
      rw [ha s] at h2
      refine h1.unique ?_
      convert h2 using 2 with i
      show _ = ⟪vfunD (2 * l / 3) i, a i⟫_ℝ
      rw [Complex.inner, ← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    have hin : HasSum (fun i => TwinLandau.wq Pz cz (Sum.inl i) l)
        (2 * SA + X) := by
      convert (hSA.mul_left 2).add hX using 2 with i
      simp only [TwinLandau.wq, Pz, cz, Sum.elim_inl]
      rw [add_assoc, PD_eq, two_cos_eq, vfunD_eq]; ring
    have hinr : HasSum (fun i => TwinLandau.wq Pz cz (Sum.inr i) l)
        (2 * SB + (starRingEnd ℂ) X) := by
      convert (hSB.mul_left 2).add hXc using 2 with i
      simp only [TwinLandau.wq, Pz, cz, Sum.elim_inr]
      rw [conj_PD, neg_neg, add_assoc, two_cos_eq, vfunD_eq, map_mul, map_mul, ← Complex.cos_conj,
        map_mul, Complex.conj_ofReal, map_ofNat]
      ring
    have hall := HasSum.sum (f := fun q => TwinLandau.wq Pz cz q l) hin hinr
    have hXX : X + (starRingEnd ℂ) X = 0 := by
      rw [Complex.add_conj, hXre]; simp
    rw [TwinLandau.Wsum, hall.tsum_eq]
    linear_combination hXX
  have hp0 : PD r ≠ 0 := fun e => im_PD_ne r (by rw [e, zero_im])
  have hR := TwinLandau.Rp_eq_zero_of_Wsum_const hD hW hp0
  set S1 := ∑' i, (starRingEnd ℂ) (a i) * (e1D r i : ℂ)
  set S2 := ∑' i, a i * (e2D r i : ℂ)
  have hne1 : ∀ i, i ∉ nearD r → e1D r i = 0 := fun i hi => e1D_eq_zero (not_nearD hi)
  have hne2 : ∀ i, i ∉ nearD r → e2D r i = 0 := fun i hi => e2D_eq_zero (not_nearD hi)
  have hS1 : HasSum (fun i => (starRingEnd ℂ) (a i) * (e1D r i : ℂ)) S1 := (summable_eD hne1).hasSum
  have hS2 : HasSum (fun i => a i * (e2D r i : ℂ)) S2 := (summable_eD hne2).hasSum
  have hRsum : HasSum (fun q => cz q * (TwinLandau.indR (PD r) (Pz q) : ℂ))
      (G0D r * S1 + G0D r * S2) := by
    refine HasSum.sum (f := fun q => cz q * (TwinLandau.indR (PD r) (Pz q) : ℂ)) ?_ ?_
    · convert hS1.mul_left (G0D r) using 2 with i
      have h := G0D_e1 r i
      simp only [e1D] at h
      simp only [Function.comp_apply, cz, Pz, Sum.elim_inl, e1D]
      linear_combination (starRingEnd ℂ) (a i) * h
    · convert hS2.mul_left (G0D r) using 2 with i
      have h := G0D_e2 r i
      simp only [e2D] at h
      simp only [Function.comp_apply, cz, Pz, Sum.elim_inr, e2D]
      linear_combination a i * h
  have hG : G0D r ≠ 0 := ghat_box_ne (by
    rw [show ((3 : ℂ) * tau3 r).im = 3 * (tau3 r).im by simp]; exact mul_ne_zero three_ne_zero hr)
  have hS12 : S1 + S2 = 0 := by
    have := hRsum.tsum_eq
    rw [← TwinLandau.Rp] at this
    rw [hR] at this
    have h2 : G0D r * (S1 + S2) = 0 := by rw [mul_add]; exact this.symm
    exact (mul_eq_zero.1 h2).resolve_left hG
  have hT : HasSum (fun i => TfunD r i * (starRingEnd ℂ) (a i))
      (I * S1 - I * star S2) := by
    convert (hS1.mul_left I).sub (hS2.star.mul_left I) using 2 with i
    simp only [TfunD, star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  have h1 := Complex.hasSum_re hT
  have h2 := lp.hasSum_inner (𝕜 := ℝ) a (TvecD r)
  have e : ⟪a, TvecD r⟫_ℝ = (I * S1 - I * star S2).re := by
    refine h2.unique ?_
    convert h1 using 2 with i
    show ⟪a i, TfunD r i⟫_ℝ = _
    rw [Complex.inner]
  rw [e]
  have := congrArg Complex.im hS12
  simp only [add_im, zero_im] at this
  simp [Complex.mul_re]
  linarith

theorem TvecD_mem_closure {r : ZD} (hr : (tau3 r).im ≠ 0) :
    TvecD r ∈ (LinearMap.range vecLD).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro a ha
  refine inner_TvecD_eq_zero a (fun s => ?_) hr
  rw [Submodule.mem_orthogonal] at ha
  refine ha _ ⟨Finsupp.single s 1, ?_⟩
  rw [vecLD, Finsupp.linearCombination_single, one_smul]

theorem exists_approxD {r : ZD} (hr : (tau3 r).im ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : NNReal →₀ ℝ, ‖vecLD c - TvecD r‖ < ε := by
  have hm := TvecD_mem_closure hr
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hm
  obtain ⟨y, hy1, hy⟩ := hm ε hε
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hy1
  exact ⟨c, by rw [← dist_eq_norm, dist_comm]; exact hy⟩

/-! ### E. The negative space -/

/-- **Every off-line quadruple of `dh` gives a negative direction of `Q_dh`** (the dh column of
`negDirections_offline`, u-space form `QDHu`, test points `3τ`, width-3 strip test). -/
theorem negDirections_offline_dh (R : Finset ZD)
    (hRoff : ∀ r ∈ R, (tau3 r).im ≠ 0)
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tau3 s) (tau3 r)) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a (3 * z) ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → QDHu v < 0 := by
  classical
  set m : ℕ := Fintype.card R
  set C : ℝ := ∑ r : R, ‖TvecD r.1‖
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
  choose c hc using fun r : R => exists_approxD (hRoff r.1 r.2) hε
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
  have hvec : ∀ x, vecLD (cx x) = ∑ r, x r • vecLD (c r) := fun x => by
    simp only [cx, map_sum, map_smul]
  set Tx : (R → ℝ) → L2D := fun x => ∑ r, x r • TvecD r.1
  have hTx : ∀ x i, Tx x i = I * ((∑ r : R, x r * (e1D r.1 i - e2D r.1 i) : ℝ) : ℂ) := by
    intro x i
    have e : Tx x i = ∑ r : R, (x r : ℂ) * TfunD r.1 i := by
      simp only [Tx]
      rw [lp.coeFn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]; rfl
    rw [e]
    simp only [TfunD]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hval : ∀ (x : R → ℝ) (r : R), (∑ s : R, x s * (e1D s.1 r.1 - e2D s.1 r.1)) = x r := by
    intro x r
    rw [Finset.sum_eq_single r]
    · rw [e1D_self, e2D_self (hRoff r.1 r.2)]; ring
    · intro s _ hsr
      have hne : r.1 ≠ s.1 := fun e => hsr (Subtype.ext e.symm)
      obtain ⟨h1, h2⟩ := eD_other (hdist s.1 s.2 r.1 r.2 (Ne.symm hne))
      rw [h1, h2]; ring
    · intro h; exact absurd (Finset.mem_univ r) h
  have hBT : ∀ x, BreD (Tx x) (Tx x) ≤ -∑ r, x r ^ 2 := by
    intro x
    set f : ZD → ℝ := fun i => ∑ r : R, x r * (e1D r.1 i - e2D r.1 i)
    have hs := hasSum_BreD (Tx x) (Tx x)
    have e : (fun i => (Tx x i * Tx x i).re) = fun i => -(f i ^ 2) := by
      funext i; rw [hTx]; simp [f, Complex.mul_re]; ring
    rw [e] at hs
    have hs' : HasSum (fun i => f i ^ 2) (-BreD (Tx x) (Tx x)) := by simpa using hs.neg
    have hle : ∑ i ∈ R, f i ^ 2 ≤ -BreD (Tx x) (Tx x) :=
      hs'.summable.sum_le_tsum R (fun _ _ => sq_nonneg _) |>.trans_eq hs'.tsum_eq
    have hR : ∑ i ∈ R, f i ^ 2 = ∑ r : R, x r ^ 2 := by
      rw [← Finset.sum_coe_sort R]
      exact Finset.sum_congr rfl fun r _ => by simp only [f]; rw [hval]
    linarith
  have hBre : ∀ x, x ≠ 0 → BreD (vecLD (cx x)) (vecLD (cx x)) < 0 := by
    intro x hx
    set S : ℝ := ∑ r, |x r|
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hd : ‖vecLD (cx x) - Tx x‖ ≤ ε * S := by
      rw [hvec, show (∑ r, x r • vecLD (c r)) - Tx x = ∑ r, x r • (vecLD (c r) - TvecD r.1) by
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
      exact Finset.single_le_sum (f := fun r : R => ‖TvecD r.1‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ r)
    have hY : ‖vecLD (cx x)‖ ≤ C * S + ε * S := by
      have := norm_sub_norm_le (vecLD (cx x)) (Tx x)
      linarith
    have herr := abs_BreD_sub_le (vecLD (cx x)) (Tx x)
    have herr' : |BreD (vecLD (cx x)) (vecLD (cx x)) - BreD (Tx x) (Tx x)|
        ≤ ε * (2 * C + ε) * S ^ 2 := by
      refine herr.trans ?_
      calc ‖vecLD (cx x) - Tx x‖ * (‖vecLD (cx x)‖ + ‖Tx x‖)
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
  have hLQ : ∀ x, QDHu (L x) = 2 * BreD (vecLD (cx x)) (vecLD (cx x)) := fun x =>
    QDH_eq_BreD (hfits x) hA
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h0 : vecLD (cx x) = 0 := by
      ext i
      rw [vecLD_apply, G0D, ← ghatC_twinComb (hfits x)]
      have : twinComb (cx x) = fun _ => 0 := hx
      rw [this, ghatC_zero_fun]; simp
    have := hBre x hx0
    rw [h0] at this
    simp [BreD] at this
  refine ⟨A, hA, LinearMap.range L, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  · rintro v ⟨x, rfl⟩
    exact ⟨twinComb_probe (hfits x), striptest_twinComb3 (hfits x)⟩
  · rintro v ⟨x, rfl⟩ hv
    have hx : x ≠ 0 := fun h => hv (by rw [h, map_zero])
    rw [hLQ]; have := hBre x hx; linarith

/-! ### F. The payoff: `n` located off-line zeros give `n` negative directions -/

theorem norm_sub_quad_le {ρ c : ℂ} (q : ℂ → ℂ)
    (hq : q = id ∨ q = (fun z => 1 - z) ∨ q = conj ∨ q = (fun z => 1 - conj z)) :
    ‖q ρ - q c‖ = ‖ρ - c‖ := by
  rcases hq with rfl | rfl | rfl | rfl
  · rfl
  · rw [show (1 - ρ) - (1 - c) = -(ρ - c) by ring, norm_neg]
  · rw [← map_sub, Complex.norm_conj]
  · rw [show (1 - conj ρ) - (1 - conj c) = -(conj (ρ - c)) by rw [map_sub]; ring, norm_neg,
      Complex.norm_conj]

/-- **`n` located off-line zeros of `dh` give an `n`-dimensional negative space of `Q_dh`.** The
centres `c k` must lie at least `1/100` from the critical line and right of `Re s = 1/100`, and every
centre must be at least `2/100` from every image of every other centre under the quadruple maps
`s ↦ s, 1 − s, s̄, 1 − s̄`. -/
theorem negIndex_ge_of_located {n : ℕ} (c : Fin n → ℂ)
    (hloc : ∀ k, ∃ ρ, dh ρ = 0 ∧ ‖ρ - c k‖ < 1 / 100)
    (hre : ∀ k, 1 / 100 ≤ (c k).re) (hoff : ∀ k, 1 / 100 ≤ |(c k).re - 1 / 2|)
    (hsep : ∀ k l, k ≠ l → 2 / 100 ≤ ‖c l - c k‖ ∧ 2 / 100 ≤ ‖c l - (1 - c k)‖
      ∧ 2 / 100 ≤ ‖c l - conj (c k)‖ ∧ 2 / 100 ≤ ‖c l - (1 - conj (c k))‖) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = n ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a (3 * z) ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → QDHu v < 0 := by
  classical
  choose ρ hρ hρc using hloc
  have hidx := fun k => idx_of_located (hρ k) (hρc k) (hre k) (hoff k)
  choose i hit himn using hidx
  -- different centres give zeros in different quadruples
  have hno : ∀ k l, k ≠ l → ¬Orb (tau3 (i l)) (tau3 (i k)) := by
    intro k l hkl hor
    have hq := quad_of_orb (hit k) (hit l) hor
    obtain ⟨s1, s2, s3, s4⟩ := hsep k l hkl
    have key : ∀ q : ℂ → ℂ, (q = id ∨ q = (fun z => 1 - z) ∨ q = conj ∨ q = (fun z => 1 - conj z)) →
        ρ l = q (ρ k) → ‖c l - q (c k)‖ < 2 / 100 := by
      intro q hq e
      have h1 := norm_sub_quad_le (ρ := ρ k) (c := c k) q hq
      calc ‖c l - q (c k)‖ = ‖(c l - ρ l) + (q (ρ k) - q (c k))‖ := by rw [e]; ring_nf
        _ ≤ ‖c l - ρ l‖ + ‖q (ρ k) - q (c k)‖ := norm_add_le _ _
        _ < 1 / 100 + 1 / 100 := by
            rw [h1, norm_sub_rev]; exact add_lt_add (hρc l) (hρc k)
        _ = 2 / 100 := by norm_num
    rcases hq with e | e | e | e
    · exact absurd (key id (Or.inl rfl) e) (not_lt.2 s1)
    · exact absurd (key (fun z => 1 - z) (Or.inr (Or.inl rfl)) e) (not_lt.2 s2)
    · exact absurd (key conj (Or.inr (Or.inr (Or.inl rfl))) e) (not_lt.2 s3)
    · exact absurd (key (fun z => 1 - conj z) (Or.inr (Or.inr (Or.inr rfl))) e) (not_lt.2 s4)
  have hinj : Function.Injective i := by
    intro k l e
    by_contra hkl
    exact hno k l hkl (by rw [e]; exact Or.inl rfl)
  set R : Finset ZD := Finset.univ.image i
  have hcard : R.card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  obtain ⟨a, ha, V, hV, hpr, hneg⟩ := negDirections_offline_dh R
    (fun r hr => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hr; exact himn k)
    (fun r hr s hs hrs => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hr
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hs
      exact hno k l (fun h => hrs (by rw [h])))
  exact ⟨a, ha, V, hV.trans hcard, hpr, hneg⟩

/-- Monotonicity: the same space works at every larger support (`QDHu` has no window). -/
theorem negIndex_ge_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {V : Submodule ℝ (ℝ → ℝ)}
    (hpr : ∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a (3 * z) ^ 2) K) :
    ∀ v ∈ V, Probe b v ∧ ∃ K, StripTest (fun z => ghatC v b (3 * z) ^ 2) K := by
  intro v hv
  refine ⟨(hpr v hv).1.mono hab, ?_⟩
  obtain ⟨K, hK⟩ := (hpr v hv).2
  have hg : ∀ z, ghatC v b z = ghatC v a z := fun z => ghatC_mono ha hab (hpr v hv).1.supp z
  exact ⟨K, by simpa only [hg] using hK⟩

end DHNegIndex

#print axioms DHNegIndex.negDirections_offline_dh
#print axioms DHNegIndex.negIndex_ge_of_located
#print axioms DHNegIndex.negIndex_ge_mono
