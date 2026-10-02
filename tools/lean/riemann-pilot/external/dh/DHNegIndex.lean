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
`QDHu_hasSum`, one index per pair `±τ`). §B–E are round 232's generic `NegData` argument
(WeilIndexInfinite.lean) at the instance `dhND` (round 274). **The payoff** (`negIndex_ge_of_located`): `n` located
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

/-! ### (3) `Σ‖ĝ₀(3τ)‖² < ∞` from the dh explicit formula at the box -/

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

/-- The orbit of `±(ρ − ½)/3i` under `±`, conjugation comes from the quadruple `{ρ, 1 − ρ, ρ̄, 1 − ρ̄}`
(one inclusion: `Orb t' t` forces `ρ'` into it). -/
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


/-! ## Round 232 at `dh`: an instance of `NegData` (round 274; until round 273, §B–E were copied here) -/

/-- **The zeros of `Ξ₃` as negative-index data** (`κ = 3`, `w = 2`, the width-3 strip test). -/
def dhND : NegData where
  ι := ZD
  t := tau3
  κ := 3
  κ_pos := by norm_num
  t_im := tau3_im_lt
  t_re_ne := tau3_re_ne
  finite_t := fun R => (finite_PD (2 * R)).subset fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    have : ‖PD i‖ = 2 * ‖tau3 i‖ := by unfold PD; rw [norm_mul, norm_mul]; simp
    linarith
  summable_G0 := by
    simp only [Complex.ofReal_ofNat]
    exact summable_G0D_sq
  Q := fun _ => QDHu
  w := 2
  w_pos := two_pos
  Good := fun a v => ∃ K, StripTest (fun z => ghatC v a (3 * z) ^ 2) K
  hasSum := fun h hA => by
    simp only [Complex.ofReal_ofNat]
    exact hasSum_twinComb_dh h hA
  good := fun h => striptest_twinComb3 h

/-- **Every off-line quadruple of `dh` gives a negative direction of `Q_dh`** (the dh column of
`negDirections_offline`, u-space form `QDHu`, test points `3τ`, width-3 strip test). -/
theorem negDirections_offline_dh (R : Finset ZD)
    (hRoff : ∀ r ∈ R, (tau3 r).im ≠ 0)
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tau3 s) (tau3 r)) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a (3 * z) ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → QDHu v < 0 :=
  dhND.negDirections R hRoff hdist

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
