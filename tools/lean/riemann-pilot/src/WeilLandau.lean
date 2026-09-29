import Mathlib
import WeilCriterion
import Zeta
import LandauLaplace

/-! # Weil's criterion for `ζ` with no finiteness hypothesis (round 220)

Round 157's `rh_of_weil_finite` needs `hfin`: only finitely many zeros off the critical line. Its
proof integrates the twin boxes' form against a weight and needs a zero of maximal `|Im t|`. This file
removes `hfin` with Landau's theorem for Laplace transforms (`LandauLaplace.lean`).

**The transform.** For the box `g₀ = box 1` and its twins `g_λ = twin g₀ λ`, the explicit formula
(`weilExplicit_twinbox_zeta`) gives `Q(λ) := Q(g_λ) = Σ_ρ ĝ₀(t_ρ)²(2 + e^{λP_ρ} + e^{−λP_ρ})`, where
`P_ρ = 2(ρ − ½) = 2i·t_ρ`. For `Re z > 1` it can be integrated term by term:
`∫_0^∞ Q(λ)e^{−zλ}dλ = F(z) := Σ_ρ ĝ₀(t_ρ)²(2/z + 1/(z − P_ρ) + 1/(z + P_ρ))` (`lap_eq_Fw`).

**The argument** (`line_of_weil_twins`). Suppose `Q(λ) ≥ 0` for every `λ ≥ 0`.
1. `F` is holomorphic off its poles `0, ±P_ρ`, which are locally finite (`Fw_differentiableAt`). No
   pole is real, because `ζ ≠ 0` on `(0, 1)`. Near every real `c > 0`, `F` is holomorphic and equals
   the transform, by the identity theorem on a thin strip. Landau's theorem then makes the integral
   converge on all of `Re z > 0` (`conv_pos`).
2. An off-line zero gives a pole `P` with `Re P > 0`. Take the pole on that horizontal line with the
   largest real part, `p`. On a thin horizontal strip to the right of `p` there is no pole, so `F`
   equals the transform, which is continuous at `p`. But `F(z) = G(z) + R/(z − p)` with `G`
   continuous at `p` and `R = N·ĝ₀(t_p)² ≠ 0` (`N ≥ 1` counts the zeros with `±P_ρ = p`;
   `ĝ₀ ≠ 0` off the real axis, `ghat_box_ne`). That is a contradiction.

**Results.**
* `rh_of_weil_twins`: `Q(twin (box 1) λ) ≥ 0` for every `λ ≥ 0` gives Mathlib's `RiemannHypothesis`.
* `rh_of_weil`: `Q ≥ 0` for every probe gives `RiemannHypothesis`.

It is an equivalence-type statement, with no bearing on RH.
-/

open Real Filter Topology Complex Set MeasureTheory Metric
open scoped Nat

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil LandauLaplace

instance : Countable ZIdx := zetaEquiv.injective.countable

/-- The pole `P_ρ = 2(ρ − ½) = 2i·t_ρ`. -/
def poleP (q : ZIdx) : ℂ := 2 * (zetaZeroFamily q - 1 / 2)

/-- The weight `ĝ₀(t_ρ)²`, `g₀ = box 1`. -/
def cw (q : ZIdx) : ℂ := ghatC (box 1) 1 (ordi zetaZeroFamily q) ^ 2

theorem two_I_ordi (q : ZIdx) : 2 * I * ordi zetaZeroFamily q = poleP q := by
  unfold ordi poleP; field_simp

theorem nontrivial_zZF (q : ZIdx) : IsNontrivialZero (zetaZeroFamily q) := q.1.2

theorem abs_re_poleP (q : ZIdx) : |(poleP q).re| < 1 := by
  have h0 := (nontrivial_zZF q).re_pos
  have h1 := (nontrivial_zZF q).re_lt_one
  have e : (poleP q).re = 2 * (zetaZeroFamily q).re - 1 := by unfold poleP; simp; ring
  rw [e, abs_lt]; constructor <;> linarith

theorem im_poleP_ne (q : ZIdx) : (poleP q).im ≠ 0 := by
  have e : (poleP q).im = 2 * (zetaZeroFamily q).im := by unfold poleP; simp
  rw [e]; exact mul_ne_zero two_ne_zero (im_zetaZeroFamily_ne q)

theorem summable_cw : Summable fun q : ZIdx => ‖cw q‖ :=
  summable_norm_iff.2 (weilQ_eq_zero_sum (box_probe 1) one_pos weilExplicit_box_zeta).summable

/-! ## The poles are locally finite -/

theorem norm_zZF_sub (q : ZIdx) : ‖zetaZeroFamily q - 1 / 2‖ = ‖tau (zetaEquiv q).2‖ := by
  rw [← rhoXi_zetaEquiv q]
  unfold rhoXi
  split_ifs <;> simp

theorem finite_poleP (R : ℝ) : {q : ZIdx | ‖poleP q‖ ≤ R}.Finite := by
  have hs : Summable fun i : ZeroIdx (sqF Xi) => ‖i.1⁻¹‖ := (hadamardW_Xi xiGrowth Xi_zero_ne_zero).summ
  set K : ℝ := max (R ^ 2 / 4) 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfin : {i : ZeroIdx (sqF Xi) | ‖i.1‖ ≤ K}.Finite := by
    have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (inv_pos.2 hK))
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun i hi => ?_
    simp only [mem_ofPred_eq, not_lt]
    rw [norm_inv]
    have hi' : ‖i.1‖ ≤ K := hi
    have hp : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdx_ne_zero i)
    exact inv_anti₀ hp hi'
  refine ((Set.finite_univ.prod hfin).preimage zetaEquiv.injective.injOn).subset fun q hq => ?_
  simp only [mem_preimage, Set.mem_prod, mem_univ, true_and, mem_ofPred_eq]
  have hq' : ‖poleP q‖ ≤ R := hq
  have e1 : ‖poleP q‖ = 2 * ‖tau (zetaEquiv q).2‖ := by
    unfold poleP; rw [norm_mul, norm_zZF_sub]; simp
  have e2 : ‖(zetaEquiv q).2.1‖ = ‖tau (zetaEquiv q).2‖ ^ 2 := by rw [← tau_sq, norm_pow]
  rw [e2]
  have h0 := norm_nonneg (tau (zetaEquiv q).2)
  have : ‖tau (zetaEquiv q).2‖ ^ 2 ≤ R ^ 2 / 4 := by nlinarith
  exact this.trans (le_max_left _ _)

/-- **Separation from the poles.** Around any point there is a disc keeping a fixed distance from
every pole `±P_ρ` other than the point itself. -/
theorem sep (z0 : ℂ) : ∃ d > 0, ∀ z ∈ ball z0 d, ∀ q : ZIdx,
    (z0 ≠ poleP q → d ≤ ‖z - poleP q‖) ∧ (z0 ≠ -poleP q → d ≤ ‖z + poleP q‖) := by
  classical
  set T := (finite_poleP (‖z0‖ + 2)).toFinset
  obtain ⟨m1, hm1, h1⟩ := exists_pos_lb T (fun q => if z0 = poleP q then 1 else ‖z0 - poleP q‖)
    fun q => by
      split_ifs with h
      · exact one_pos
      · exact norm_pos_iff.2 (sub_ne_zero.2 h)
  obtain ⟨m2, hm2, h2⟩ := exists_pos_lb T (fun q => if z0 = -poleP q then 1 else ‖z0 + poleP q‖)
    fun q => by
      split_ifs with h
      · exact one_pos
      · exact norm_pos_iff.2 (by rw [← sub_neg_eq_add]; exact sub_ne_zero.2 h)
  set d := min 1 (min m1 m2) / 2
  have hd : 0 < d := by positivity
  have hd1 : 2 * d ≤ 1 := by simp only [d]; linarith [min_le_left 1 (min m1 m2)]
  have hdm1 : 2 * d ≤ m1 := by
    simp only [d]; linarith [min_le_right 1 (min m1 m2), min_le_left m1 m2]
  have hdm2 : 2 * d ≤ m2 := by
    simp only [d]; linarith [min_le_right 1 (min m1 m2), min_le_right m1 m2]
  refine ⟨d, hd, fun z hz q => ?_⟩
  rw [mem_ball, Complex.dist_eq] at hz
  by_cases hq : q ∈ T
  · constructor
    · intro hne
      have := h1 q hq
      simp only [hne, ↓reduceIte] at this
      have t := norm_sub_le_norm_sub_add_norm_sub z0 z (poleP q)
      rw [norm_sub_rev z0 z] at t
      linarith
    · intro hne
      have := h2 q hq
      simp only [hne, ↓reduceIte] at this
      have t := norm_add_le (z0 - z) (z + poleP q)
      rw [show z0 - z + (z + poleP q) = z0 + poleP q by ring, norm_sub_rev z0 z] at t
      linarith
  · have hbig : ‖z0‖ + 2 < ‖poleP q‖ := by
      rw [Set.Finite.mem_toFinset, mem_ofPred_eq, not_le] at hq; exact hq
    constructor
    · intro _
      have := norm_sub_norm_le (poleP q) z
      rw [norm_sub_rev] at this
      have hz' : ‖z‖ ≤ ‖z0‖ + d := by
        have := norm_sub_norm_le z z0; linarith
      linarith
    · intro _
      have := norm_sub_norm_le (poleP q) (-z)
      rw [sub_neg_eq_add, add_comm, norm_neg] at this
      have hz' : ‖z‖ ≤ ‖z0‖ + d := by
        have := norm_sub_norm_le z z0; linarith
      linarith

/-! ## The kernel and its sum -/

/-- One zero's kernel `2/z + 1/(z − P) + 1/(z + P)`. -/
def hk (P z : ℂ) : ℂ := 2 / z + 1 / (z - P) + 1 / (z + P)

/-- The transform `F(z) = Σ_ρ ĝ₀(t_ρ)²(2/z + 1/(z − P_ρ) + 1/(z + P_ρ))`. -/
def Fw (z : ℂ) : ℂ := ∑' q, cw q * hk (poleP q) z

theorem norm_one_div_le {w : ℂ} {d : ℝ} (hd : 0 < d) (h : w ≠ 0 → d ≤ ‖w‖) : ‖1 / w‖ ≤ 1 / d := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp; positivity
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hd (h hw)

/-- The kernels at a fixed point are uniformly bounded over the zeros. -/
theorem hk_bound (z : ℂ) : ∃ B, ∀ q : ZIdx, ‖1 / (z - poleP q)‖ ≤ B ∧ ‖1 / (z + poleP q)‖ ≤ B := by
  obtain ⟨d, hd, h⟩ := sep z
  refine ⟨1 / d, fun q => ⟨norm_one_div_le hd fun hw => (h z (mem_ball_self hd) q).1 fun e => hw
    (by rw [e]; ring), norm_one_div_le hd fun hw => (h z (mem_ball_self hd) q).2 fun e => hw
    (by rw [e]; ring)⟩⟩

theorem summable_cw_mul {k : ZIdx → ℂ} {B : ℝ} (hk : ∀ q, ‖k q‖ ≤ B) :
    Summable fun q => cw q * k q :=
  (summable_cw.mul_right B).of_norm_bounded fun q => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hk q) (norm_nonneg _)

theorem summable_hk (z : ℂ) : Summable fun q => cw q * hk (poleP q) z := by
  obtain ⟨B, hB⟩ := hk_bound z
  refine summable_cw_mul (B := ‖2 / z‖ + B + B) fun q => ?_
  unfold hk
  exact (norm_add₃_le).trans (by linarith [(hB q).1, (hB q).2])

/-- **`F` is holomorphic off its poles.** -/
theorem Fw_differentiableAt {z0 : ℂ} (h0 : z0 ≠ 0) (hP : ∀ q, z0 ≠ poleP q ∧ z0 ≠ -poleP q) :
    DifferentiableAt ℂ Fw z0 := by
  obtain ⟨d, hd, h⟩ := sep z0
  set e := min d (‖z0‖ / 2)
  have he : 0 < e := lt_min hd (by have := norm_pos_iff.2 h0; linarith)
  have hze : ∀ z ∈ ball z0 e, e ≤ ‖z‖ := fun z hz => by
    rw [mem_ball, Complex.dist_eq] at hz
    have := norm_sub_norm_le z0 (z0 - z)
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at hz
    linarith [min_le_right d (‖z0‖ / 2)]
  have hsub : ∀ z ∈ ball z0 e, ∀ q, e ≤ ‖z - poleP q‖ ∧ e ≤ ‖z + poleP q‖ := fun z hz q => by
    have hz' : z ∈ ball z0 d := ball_subset_ball (min_le_left _ _) hz
    exact ⟨(min_le_left _ _).trans ((h z hz' q).1 (hP q).1),
      (min_le_left _ _).trans ((h z hz' q).2 (hP q).2)⟩
  have hD : DifferentiableOn ℂ Fw (ball z0 e) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun q => ‖cw q‖ * (4 / e))
      (summable_cw.mul_right _) (fun q => ?_) isOpen_ball (fun q z hz => ?_)
    · intro z hz
      have h1 : z ≠ 0 := fun e0 => by have := hze z hz; rw [e0, norm_zero] at this; linarith
      have h2 : z - poleP q ≠ 0 := fun e0 => by
        have := (hsub z hz q).1; rw [e0, norm_zero] at this; linarith
      have h3 : z + poleP q ≠ 0 := fun e0 => by
        have := (hsub z hz q).2; rw [e0, norm_zero] at this; linarith
      have hd : DifferentiableAt ℂ (fun w : ℂ => cw q * hk (poleP q) w) z := by
        unfold hk; fun_prop (disch := assumption)
      exact hd.differentiableWithinAt
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold hk
      have b1 : ‖2 / z‖ ≤ 2 / e := by
        rw [norm_div, Complex.norm_ofNat]; exact div_le_div_of_nonneg_left (by norm_num) he (hze z hz)
      have b2 := norm_one_div_le he (w := z - poleP q) fun _ => (hsub z hz q).1
      have b3 := norm_one_div_le he (w := z + poleP q) fun _ => (hsub z hz q).2
      calc _ ≤ ‖2 / z‖ + ‖1 / (z - poleP q)‖ + ‖1 / (z + poleP q)‖ := norm_add₃_le
        _ ≤ 2 / e + 1 / e + 1 / e := by linarith
        _ = 4 / e := by ring
  exact hD.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self he))

/-! ## The regular part at a pole -/

/-- The multiplicity indicator of `p` among `±P`. -/
def indR (p P : ℂ) : ℝ := (if P = p then 1 else 0) + (if -P = p then 1 else 0)

/-- The kernel with the pole at `p` removed. -/
def hkr (p P z : ℂ) : ℂ :=
  2 / z + (if P = p then 0 else 1 / (z - P)) + (if -P = p then 0 else 1 / (z + P))

theorem hk_split (p P z : ℂ) : hk P z = hkr p P z + (indR p P : ℂ) / (z - p) := by
  unfold hk hkr indR
  by_cases h1 : P = p <;> by_cases h2 : -P = p
  · subst h1
    have hP0 : P = 0 := by linear_combination (-1 / 2 : ℂ) * h2
    subst hP0
    simp only [neg_zero, ↓reduceIte]; push_cast; ring
  · subst h1; simp only [h2, ↓reduceIte]; push_cast; ring
  · have : z + P = z - p := by rw [← h2]; ring
    simp only [h1, h2, ↓reduceIte]; push_cast; rw [this]; ring
  · simp only [h1, h2, ↓reduceIte]; push_cast; ring

/-- The regular part `G_p(z) = Σ_ρ ĝ₀(t_ρ)²·(kernel with the pole at `p` removed)`. -/
def Gp (p z : ℂ) : ℂ := ∑' q, cw q * hkr p (poleP q) z

/-- The residue `R_p = Σ_ρ ĝ₀(t_ρ)²·#{±P_ρ = p}`. -/
def Rp (p : ℂ) : ℂ := ∑' q, cw q * (indR p (poleP q) : ℂ)

theorem indR_le (p P : ℂ) : indR p P ≤ 2 := by unfold indR; split_ifs <;> norm_num

theorem indR_nonneg (p P : ℂ) : 0 ≤ indR p P := by unfold indR; split_ifs <;> norm_num

theorem Fw_split (p z : ℂ) : Fw z = Gp p z + Rp p / (z - p) := by
  obtain ⟨B, hB⟩ := hk_bound z
  have hs1 : Summable fun q => cw q * hkr p (poleP q) z := by
    refine summable_cw_mul (B := ‖2 / z‖ + B + B) fun q => ?_
    unfold hkr
    refine (norm_add₃_le).trans ?_
    have b2 : ‖(if poleP q = p then 0 else 1 / (z - poleP q))‖ ≤ B := by
      split_ifs
      · simp; exact (norm_nonneg _).trans (hB q).1
      · exact (hB q).1
    have b3 : ‖(if -poleP q = p then 0 else 1 / (z + poleP q))‖ ≤ B := by
      split_ifs
      · simp; exact (norm_nonneg _).trans (hB q).1
      · exact (hB q).2
    linarith
  have hs2 : Summable fun q => cw q * (indR p (poleP q) : ℂ) :=
    summable_cw_mul (B := 2) fun q => by
      rw [Complex.norm_real, Real.norm_of_nonneg (indR_nonneg _ _)]; exact indR_le _ _
  unfold Fw Gp Rp
  simp_rw [hk_split p]
  rw [← tsum_div_const, ← hs1.tsum_add (hs2.div_const _)]
  congr 1; funext q; ring

/-- **The regular part is continuous at `p`.** -/
theorem Gp_continuousAt {p : ℂ} (hp : p ≠ 0) : ContinuousAt (Gp p) p := by
  obtain ⟨d, hd, h⟩ := sep p
  set e := min d (‖p‖ / 2)
  have he : 0 < e := lt_min hd (by have := norm_pos_iff.2 hp; linarith)
  have hze : ∀ z ∈ ball p e, e ≤ ‖z‖ := fun z hz => by
    rw [mem_ball, Complex.dist_eq] at hz
    have := norm_sub_norm_le p (p - z)
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at hz
    linarith [min_le_right d (‖p‖ / 2)]
  have hC : ContinuousOn (Gp p) (ball p e) := by
    refine continuousOn_tsum (u := fun q => ‖cw q‖ * (4 / e)) (fun q => ?_)
      (summable_cw.mul_right _) (fun q z hz => ?_)
    · intro z hz
      have hz' : z ∈ ball p d := ball_subset_ball (min_le_left _ _) hz
      have h1 : z ≠ 0 := fun e0 => by have := hze z hz; rw [e0, norm_zero] at this; linarith
      refine ContinuousAt.continuousWithinAt ?_
      unfold hkr
      split_ifs with hq1 hq2 hq2
      · fun_prop (disch := assumption)
      · have := (h z hz' q).2 (Ne.symm hq2)
        have h3 : z + poleP q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        fun_prop (disch := assumption)
      · have := (h z hz' q).1 (Ne.symm hq1)
        have h3 : z - poleP q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        fun_prop (disch := assumption)
      · have := (h z hz' q).1 (Ne.symm hq1)
        have h3 : z - poleP q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        have := (h z hz' q).2 (Ne.symm hq2)
        have h4 : z + poleP q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        fun_prop (disch := assumption)
    · have hz' : z ∈ ball p d := ball_subset_ball (min_le_left _ _) hz
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold hkr
      have b1 : ‖2 / z‖ ≤ 2 / e := by
        rw [norm_div, Complex.norm_ofNat]; exact div_le_div_of_nonneg_left (by norm_num) he (hze z hz)
      have b2 : ‖(if poleP q = p then 0 else 1 / (z - poleP q))‖ ≤ 1 / e := by
        split_ifs with hq
        · simp; positivity
        · exact norm_one_div_le he fun _ => (min_le_left _ _).trans ((h z hz' q).1 (Ne.symm hq))
      have b3 : ‖(if -poleP q = p then 0 else 1 / (z + poleP q))‖ ≤ 1 / e := by
        split_ifs with hq
        · simp; positivity
        · exact norm_one_div_le he fun _ => (min_le_left _ _).trans ((h z hz' q).2 (Ne.symm hq))
      calc _ ≤ _ := norm_add₃_le
        _ ≤ 2 / e + 1 / e + 1 / e := by linarith
        _ = 4 / e := by ring
  exact hC.continuousAt (isOpen_ball.mem_nhds (mem_ball_self he))

/-- **The residue at a pole off the imaginary axis is nonzero**: `R_p = N·ĝ₀(t_p)²`, `N ≥ 1`. -/
theorem Rp_ne_zero {p : ℂ} (hp : 0 < p.re) {q0 : ZIdx} (hq0 : poleP q0 = p ∨ -poleP q0 = p) :
    Rp p ≠ 0 := by
  classical
  set tp : ℂ := p / (2 * I)
  have hG : ∀ q, cw q * (indR p (poleP q) : ℂ) = ghatC (box 1) 1 tp ^ 2 * (indR p (poleP q) : ℂ) := by
    intro q
    unfold indR
    by_cases h1 : poleP q = p
    · have ht : ordi zetaZeroFamily q = tp := by
        simp only [tp]; rw [← h1, ← two_I_ordi]; field_simp
      unfold cw; rw [ht]
    · by_cases h2 : -poleP q = p
      · have ht : ordi zetaZeroFamily q = -tp := by
          simp only [tp]; rw [← h2, ← two_I_ordi]; field_simp
        unfold cw; rw [ht, ghatC_even (box_probe 1).even]
      · simp [h1, h2]
  unfold Rp
  simp_rw [hG]
  have hsum : Summable fun q => indR p (poleP q) := by
    refine summable_of_ne_finset_zero (s := (finite_poleP ‖p‖).toFinset) fun q hq => ?_
    rw [Set.Finite.mem_toFinset, mem_ofPred_eq, not_le] at hq
    unfold indR
    have h1 : poleP q ≠ p := fun e => by rw [e] at hq; exact lt_irrefl _ hq
    have h2 : -poleP q ≠ p := fun e => by rw [← e, norm_neg] at hq; exact lt_irrefl _ hq
    simp [h1, h2]
  rw [tsum_mul_left, ← Complex.ofReal_tsum]
  have hpos : 0 < ∑' q, indR p (poleP q) := by
    have h1 : 1 ≤ indR p (poleP q0) := by
      unfold indR
      rcases hq0 with h | h
      · simp only [h, ↓reduceIte]; split_ifs <;> norm_num
      · simp only [h, ↓reduceIte]; split_ifs <;> norm_num
    have := hsum.le_tsum q0 (fun q _ => indR_nonneg _ _)
    linarith
  refine mul_ne_zero (pow_ne_zero 2 (ghat_box_ne ?_)) (by exact_mod_cast hpos.ne')
  have e : tp.im = -p.re / 2 := by simp only [tp]; simp [Complex.div_im]; ring
  rw [e]; intro h; linarith

/-! ## The twin boxes' form as a sum of exponentials -/

/-- One zero's term `ĝ₀(t)²(2 + e^{λP} + e^{−λP})`. -/
def wq (q : ZIdx) (l : ℝ) : ℂ := cw q * (2 + cexp (l * poleP q) + cexp (-(l * poleP q)))

theorem twin_sq (l : ℝ) (t G : ℂ) :
    (2 * Complex.cos (l * t) * G) ^ 2 = G ^ 2 * (2 + cexp (l * (2 * I * t)) + cexp (-(l * (2 * I * t)))) := by
  have hu : cexp (l * (2 * I * t)) = cexp (l * t * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hv : cexp (-(l * (2 * I * t))) = cexp (-(l * t) * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have huv : cexp (l * t * I) * cexp (-(l * t) * I) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  rw [Complex.cos, hu, hv]
  linear_combination (2 * G ^ 2) * huv

/-- **The explicit formula for the twins**: `Q(twin λ) = Σ_ρ ĝ₀(t_ρ)²(2 + e^{λP_ρ} + e^{−λP_ρ})`. -/
theorem hasSum_wq {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun q => wq q l) (weilQ (l + 1) (twin (box 1) l) : ℂ) := by
  have h := weilQ_eq_zero_sum (twin_probe (box_probe 1) hl) (by linarith) (weilExplicit_twinbox_zeta hl)
  convert h using 1
  funext q
  rw [ghatC_twin one_pos (box_probe 1) hl, twin_sq, two_I_ordi]
  rfl

theorem norm_wq_le (q : ZIdx) (l : ℝ) : ‖wq q l‖ ≤ ‖cw q‖ * (4 * Real.exp |l|) := by
  unfold wq
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hr := abs_re_poleP q
  have b : ∀ s : ℝ, s = 1 ∨ s = -1 → ‖cexp (s * (l * poleP q))‖ ≤ Real.exp |l| := fun s hs => by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have e : (↑s * (↑l * poleP q)).re = s * l * (poleP q).re := by simp; ring
    rw [e]
    have := abs_le.1 hr.le
    rcases hs with rfl | rfl <;> [skip; skip] <;>
      nlinarith [abs_nonneg l, le_abs_self l, neg_abs_le l, abs_mul_abs_self l]
  have b1 := b 1 (Or.inl rfl)
  have b2 := b (-1) (Or.inr rfl)
  simp only [ofReal_one, one_mul, ofReal_neg, neg_mul] at b1 b2
  have h1 : 1 ≤ Real.exp |l| := Real.one_le_exp (abs_nonneg l)
  calc ‖2 + cexp (↑l * poleP q) + cexp (-(↑l * poleP q))‖
      ≤ ‖(2 : ℂ)‖ + ‖cexp (↑l * poleP q)‖ + ‖cexp (-(↑l * poleP q))‖ := norm_add₃_le
    _ ≤ 2 + Real.exp |l| + Real.exp |l| := by rw [Complex.norm_ofNat]; linarith
    _ ≤ 4 * Real.exp |l| := by linarith

/-- The function `λ ↦ Σ_ρ ĝ₀(t_ρ)²(2 + e^{λP_ρ} + e^{−λP_ρ})`, defined for every real `λ`. -/
def Wsum (l : ℝ) : ℂ := ∑' q, wq q l

theorem continuous_Wsum : Continuous Wsum := by
  rw [continuous_iff_continuousAt]
  intro x
  have hC : ContinuousOn Wsum (Ioo (x - 1) (x + 1)) := by
    refine continuousOn_tsum (u := fun q => ‖cw q‖ * (4 * Real.exp (|x| + 1))) (fun q => ?_)
      (summable_cw.mul_right _) (fun q l hl => ?_)
    · unfold wq; exact Continuous.continuousOn (by fun_prop)
    · refine (norm_wq_le q l).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      have : |l| ≤ |x| + 1 := by
        have h1 := abs_sub_abs_le_abs_sub l x
        have h2 : |l - x| < 1 := abs_lt.2 ⟨by linarith [hl.1], by linarith [hl.2]⟩
        linarith
      gcongr
  exact hC.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

theorem Wsum_eq {l : ℝ} (hl : 0 ≤ l) : Wsum l = (weilQ (l + 1) (twin (box 1) l) : ℂ) :=
  (hasSum_wq hl).tsum_eq

theorem norm_Wsum_le (l : ℝ) : ‖Wsum l‖ ≤ (∑' q, ‖cw q‖) * (4 * Real.exp |l|) := by
  unfold Wsum
  have hs : Summable fun q => ‖wq q l‖ :=
    (summable_cw.mul_right (4 * Real.exp |l|)).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => norm_wq_le q l)
  calc ‖∑' q, wq q l‖ ≤ ∑' q, ‖wq q l‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' q, ‖cw q‖ * (4 * Real.exp |l|) :=
        hs.tsum_le_tsum (fun q => norm_wq_le q l) (summable_cw.mul_right _)
    _ = _ := tsum_mul_right

/-! ## The Laplace transform in `λ` -/

/-- The transform's input `A(λ) = Re Σ_ρ(…)`; it equals `Q(twin λ)` for `λ ≥ 0`. -/
def Aw (l : ℝ) : ℝ := (Wsum l).re

theorem Aw_eq {l : ℝ} (hl : 0 ≤ l) : Aw l = weilQ (l + 1) (twin (box 1) l) := by
  unfold Aw; rw [Wsum_eq hl, ofReal_re]

theorem Aw_ofReal {l : ℝ} (hl : 0 ≤ l) : (Aw l : ℂ) = Wsum l := by
  rw [Aw_eq hl, Wsum_eq hl]

theorem hyp_Aw (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l)) :
    Hyp (volume.restrict (Ioi (0 : ℝ))) Aw (fun l => l) where
  A_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => by
    rw [Aw_eq hl.le]; exact hQ l hl.le)
  ph_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => hl.le)
  A_meas := (Complex.continuous_re.comp continuous_Wsum).aestronglyMeasurable
  ph_meas := continuous_id.aestronglyMeasurable

theorem conv_Aw_two : Conv (volume.restrict (Ioi (0 : ℝ))) Aw (fun l => l) 2 := by
  set S := ∑' q, ‖cw q‖
  have hi : IntegrableOn (fun l : ℝ => 4 * S * Real.exp (-1 * l)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  refine hi.mono' ((Complex.continuous_re.comp continuous_Wsum).mul (by fun_prop)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => ?_))
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : ‖Aw l‖ ≤ S * (4 * Real.exp l) := by
    have := norm_Wsum_le l
    rw [abs_of_pos hl] at this
    exact (Complex.abs_re_le_norm _).trans this
  calc ‖Aw l‖ * Real.exp (-2 * l) ≤ S * (4 * Real.exp l) * Real.exp (-2 * l) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 4 * S * Real.exp (-1 * l) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf

/-- One zero's transform: `∫_0^∞ ĝ₀²(2 + e^{λP} + e^{−λP})e^{−zλ}dλ = ĝ₀²(2/z + 1/(z − P) + 1/(z + P))`
for `Re z > 1`. -/
theorem wq_exp_eq (q : ZIdx) (z : ℂ) (l : ℝ) :
    wq q l * cexp (-z * l) = cw q * (2 * cexp (-z * l) + cexp ((poleP q - z) * l)
      + cexp ((-poleP q - z) * l)) := by
  unfold wq
  rw [show (poleP q - z) * l = l * poleP q + -z * l by ring,
    show (-poleP q - z) * l = -(l * poleP q) + -z * l by ring, Complex.exp_add, Complex.exp_add]
  ring

theorem re_lt_of_one_lt {z : ℂ} (hz : 1 < z.re) (q : ZIdx) :
    (poleP q - z).re < 0 ∧ (-poleP q - z).re < 0 ∧ (-z).re < 0 := by
  have := abs_lt.1 (abs_re_poleP q)
  simp only [sub_re, neg_re]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem integrable_wq (q : ZIdx) {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun l : ℝ => wq q l * cexp (-z * l)) (Ioi 0) := by
  obtain ⟨h1, h2, h3⟩ := re_lt_of_one_lt hz q
  simp_rw [wq_exp_eq]
  exact ((((integrableOn_exp_mul_complex_Ioi h3 0).const_mul 2).add
    (integrableOn_exp_mul_complex_Ioi h1 0)).add (integrableOn_exp_mul_complex_Ioi h2 0)).const_mul _

theorem integral_wq (q : ZIdx) {z : ℂ} (hz : 1 < z.re) :
    ∫ l in Ioi (0 : ℝ), wq q l * cexp (-z * l) = cw q * hk (poleP q) z := by
  obtain ⟨h1, h2, h3⟩ := re_lt_of_one_lt hz q
  simp_rw [wq_exp_eq]
  have i1 : IntegrableOn (fun l : ℝ => 2 * cexp (-z * l)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi h3 0).const_mul 2
  have i2 : IntegrableOn (fun l : ℝ => cexp ((poleP q - z) * l)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi h1 0
  have i3 : IntegrableOn (fun l : ℝ => cexp ((-poleP q - z) * l)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi h2 0
  have i12 : IntegrableOn (fun l : ℝ => 2 * cexp (-z * l) + cexp ((poleP q - z) * l)) (Ioi 0) :=
    i1.add i2
  rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_exp_mul_complex_Ioi h3, integral_exp_mul_complex_Ioi h1, integral_exp_mul_complex_Ioi h2]
  unfold hk
  have hP := abs_lt.1 (abs_re_poleP q)
  have hz0 : z ≠ 0 := fun e => by rw [e] at hz; simp at hz; linarith
  have hz1 : z - poleP q ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp only [sub_re, zero_re] at this; linarith [hP.1, hP.2]
  have hz2 : z + poleP q ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp only [add_re, zero_re] at this; linarith [hP.1, hP.2]
  have hz1' : poleP q - z ≠ 0 := fun e => hz1 (by rw [← neg_sub, e, neg_zero])
  have hz2' : -poleP q - z ≠ 0 := fun e => hz2 (by linear_combination -e)
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- **The transform equals `F` for `Re z > 1`.** -/
theorem lap_eq_Fw {z : ℂ} (hz : 1 < z.re) :
    lap (volume.restrict (Ioi (0 : ℝ))) Aw (fun l => l) z = Fw z := by
  unfold lap
  have e : ∫ l in Ioi (0 : ℝ), (Aw l : ℂ) * cexp (-z * l)
      = ∫ l in Ioi (0 : ℝ), ∑' q, wq q l * cexp (-z * l) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun l (hl : 0 < l) => ?_
    rw [Aw_ofReal hl.le, Wsum, tsum_mul_right]
  rw [e, ← integral_tsum_of_summable_integral_norm (fun q => integrable_wq q hz)]
  · unfold Fw; congr 1; funext q; exact integral_wq q hz
  · set K := ∫ l in Ioi (0 : ℝ), 4 * Real.exp (-(z.re - 1) * l)
    have hK : IntegrableOn (fun l : ℝ => 4 * Real.exp (-(z.re - 1) * l)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
    refine (summable_cw.mul_right K).of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _)
      fun q => ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hK.const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => ?_))
    show ‖wq q l * cexp (-z * l)‖ ≤ ‖cw q‖ * (4 * Real.exp (-(z.re - 1) * l))
    rw [norm_mul, Complex.norm_exp]
    have h1 := norm_wq_le q l
    rw [abs_of_pos hl] at h1
    have e2 : (-z * l).re = -z.re * l := by simp
    rw [e2]
    calc ‖wq q l‖ * Real.exp (-z.re * l) ≤ ‖cw q‖ * (4 * Real.exp l) * Real.exp (-z.re * l) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = ‖cw q‖ * (4 * Real.exp (-(z.re - 1) * l)) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf

theorem Fw_eventuallyEq_lap {z0 : ℂ} (hz : 1 < z0.re) :
    Fw =ᶠ[𝓝 z0] lap (volume.restrict (Ioi (0 : ℝ))) Aw (fun l => l) :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    fun _ hz => (lap_eq_Fw hz).symm

/-! ## Weil's criterion -/

/-- The poles keep a fixed distance from the real axis. -/
theorem exists_im_lb : ∃ d > 0, ∀ q : ZIdx, d ≤ |(poleP q).im| := by
  classical
  obtain ⟨m, hm, h⟩ := exists_pos_lb (finite_poleP 2).toFinset (fun q => |(poleP q).im|)
    fun q => abs_pos.2 (im_poleP_ne q)
  refine ⟨min m 1, lt_min hm one_pos, fun q => ?_⟩
  by_cases hq : q ∈ (finite_poleP 2).toFinset
  · exact (min_le_left _ _).trans (h q hq)
  · rw [Set.Finite.mem_toFinset, mem_ofPred_eq, not_le] at hq
    have := Complex.norm_le_abs_re_add_abs_im (poleP q)
    have := abs_re_poleP q
    exact (min_le_right _ _).trans (by linarith)

theorem not_pole_of_im {z : ℂ} {d : ℝ} (hd : ∀ q : ZIdx, d ≤ |(poleP q).im|) (hz : |z.im| < d)
    (q : ZIdx) : z ≠ poleP q ∧ z ≠ -poleP q := by
  constructor
  · intro e; have := hd q; rw [← e] at this; linarith
  · intro e; have := hd q; rw [← neg_neg (poleP q), ← e, neg_im, abs_neg] at this; linarith

/-- **Step 1: the transform converges on `Re z > 0`.** -/
theorem conv_pos (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l)) :
    ∀ σ, 0 < σ → Conv (volume.restrict (Ioi (0 : ℝ))) Aw (fun l => l) σ := by
  have h := hyp_Aw hQ
  obtain ⟨d, hd, hdq⟩ := exists_im_lb
  refine landau_abscissa h conv_Aw_two fun c hc habove => ?_
  set e := min (d / 2) (c / 2)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  set W : Set ℂ := {s | c < s.re} ∩ ({s | s.im < d / 2} ∩ {s | -(d / 2) < s.im})
  have hWo : IsOpen W := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hWc : Convex ℝ W := (convex_halfSpace_re_gt c).inter
    ((convex_halfSpace_im_lt (d / 2)).inter (convex_halfSpace_im_gt (-(d / 2))))
  have hFd : ∀ z : ℂ, 0 < z.re → |z.im| < d → DifferentiableAt ℂ Fw z := fun z hz hzi =>
    Fw_differentiableAt (fun e0 => by rw [e0, zero_re] at hz; exact lt_irrefl _ hz)
      (not_pole_of_im hdq hzi)
  have hLd := lap_differentiableOn h habove
  have hEq : EqOn Fw (lap (volume.restrict (Ioi (0 : ℝ))) Aw (fun l => l)) W := by
    refine eqOn_convex hWo hWc (fun z hz => (hFd z (lt_trans hc (show c < z.re from hz.1)) (abs_lt.2
      ⟨by linarith [show -(d / 2) < z.im from hz.2.2], by linarith [show z.im < d / 2 from hz.2.1]⟩)).differentiableWithinAt)
      (hLd.mono fun z hz => hz.1) (z0 := ((max c 2 + 1 : ℝ) : ℂ)) ?_ (Fw_eventuallyEq_lap ?_)
    · refine ⟨?_, ?_, ?_⟩
      · show c < ((max c 2 + 1 : ℝ) : ℂ).re; rw [ofReal_re]; linarith [le_max_left c 2]
      · show ((max c 2 + 1 : ℝ) : ℂ).im < d / 2; rw [ofReal_im]; positivity
      · show -(d / 2) < ((max c 2 + 1 : ℝ) : ℂ).im; rw [ofReal_im]; linarith
    · show 1 < ((max c 2 + 1 : ℝ) : ℂ).re; rw [ofReal_re]; linarith [le_max_right c 2]
  refine ⟨e, he, Fw, fun z hz => ?_, fun s hs hsc => hEq ⟨hsc, ?_, ?_⟩⟩
  · rw [mem_ball, Complex.dist_eq] at hz
    have h1 := Complex.abs_re_le_norm (z - c)
    have h2 := Complex.abs_im_le_norm (z - c)
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h1 h2
    refine (hFd z ?_ ?_).differentiableWithinAt
    · have := (abs_lt.1 (h1.trans_lt (hz.trans_le (min_le_right _ _)))).1; linarith
    · have := h2.trans_lt (hz.trans_le (min_le_left _ _)); linarith
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - c)
    simp only [sub_im, ofReal_im, sub_zero] at h2
    have := h2.trans_lt (hs.trans_le (min_le_left _ _)); rw [abs_lt] at this; exact this.2
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - c)
    simp only [sub_im, ofReal_im, sub_zero] at h2
    have := h2.trans_lt (hs.trans_le (min_le_left _ _)); rw [abs_lt] at this; exact this.1

/-- **Weil's criterion, twin boxes only.** If `Q(twin (box 1) λ) ≥ 0` for every `λ ≥ 0`, every
nontrivial zero of `ζ` lies on the critical line. -/
theorem line_of_weil_twins (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l)) (q0 : ZIdx) :
    (zetaZeroFamily q0).re = 1 / 2 := by
  classical
  by_contra hoff
  have h := hyp_Aw hQ
  have hconv := conv_pos hQ
  set L := lap (volume.restrict (Ioi (0 : ℝ))) Aw (fun l => l)
  have hLd : DifferentiableOn ℂ L {s | 0 < s.re} := lap_differentiableOn h hconv
  -- a pole with positive real part
  have hre0 : (poleP q0).re ≠ 0 := by
    have e : (poleP q0).re = 2 * (zetaZeroFamily q0).re - 1 := by unfold poleP; simp; ring
    rw [e]; intro h0; apply hoff; linarith
  set p : ℂ := if 0 < (poleP q0).re then poleP q0 else -poleP q0
  have hp : 0 < p.re := by
    simp only [p]; split_ifs with h1
    · exact h1
    · simp only [neg_re]; push Not at h1; exact lt_of_le_of_ne (by linarith) (by
        intro h2; exact hre0 (by linarith))
  -- the poles near `p`, and the rightmost one on the horizontal line through `p`
  set T := (finite_poleP (‖p‖ + 2)).toFinset
  set D : Finset ℂ := T.image poleP ∪ T.image (fun q => -poleP q)
  have hD : ∀ q : ZIdx, ‖poleP q‖ ≤ ‖p‖ + 2 → poleP q ∈ D ∧ -poleP q ∈ D := fun q hq => by
    have : q ∈ T := (Set.Finite.mem_toFinset _).2 hq
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ this),
      Finset.mem_union_right _ (Finset.mem_image_of_mem (fun q => -poleP q) this)⟩
  set cand := D.filter fun z => p.re ≤ z.re ∧ z.im = p.im
  have hpc : p ∈ cand := by
    have hq0 : ‖poleP q0‖ ≤ ‖p‖ + 2 := by
      simp only [p]; split_ifs <;> simp
    refine Finset.mem_filter.2 ⟨?_, le_rfl, rfl⟩
    simp only [p]; split_ifs
    · exact (hD q0 hq0).1
    · exact (hD q0 hq0).2
  obtain ⟨ps, hps, hmax⟩ := cand.exists_max_image Complex.re ⟨p, hpc⟩
  obtain ⟨hpsD, hpsre, hpsim⟩ := Finset.mem_filter.1 hps
  have hpspole : ∃ q, poleP q = ps ∨ -poleP q = ps := by
    rcases Finset.mem_union.1 hpsD with h1 | h1
    · obtain ⟨q, -, hq⟩ := Finset.mem_image.1 h1; exact ⟨q, Or.inl hq⟩
    · obtain ⟨q, -, hq⟩ := Finset.mem_image.1 h1; exact ⟨q, Or.inr hq⟩
  have hps0 : 0 < ps.re := lt_of_lt_of_le hp hpsre
  -- the pole-free strip to the right of `ps`
  obtain ⟨m, hm, hmD⟩ := exists_pos_lb D (fun z => if z.im = p.im then 1 else |z.im - p.im|)
    fun z => by split_ifs with h1
                · exact one_pos
                · exact abs_pos.2 (sub_ne_zero.2 h1)
  set δ := min m 1
  have hδ : 0 < δ := lt_min hm one_pos
  set U : Set ℂ := {s | ps.re < s.re} ∩ ({s | s.im < p.im + δ} ∩ {s | p.im - δ < s.im})
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_im_lt _).inter (convex_halfSpace_im_gt _))
  have hnopole : ∀ z ∈ U, ∀ q, z ≠ poleP q ∧ z ≠ -poleP q := by
    intro z hz q
    have key : ∀ w : ℂ, (w = poleP q ∨ w = -poleP q) → w ∉ U := by
      intro w hw hwU
      have hU1 : ps.re < w.re := hwU.1
      have hU2 : w.im < p.im + δ := hwU.2.1
      have hU3 : p.im - δ < w.im := hwU.2.2
      have hwre : |w.re| < 1 := by
        rcases hw with rfl | rfl
        · exact abs_re_poleP q
        · rw [neg_re, abs_neg]; exact abs_re_poleP q
      have hwim : |w.im - p.im| < δ := abs_lt.2 ⟨by linarith, by linarith⟩
      have hnorm : ‖poleP q‖ ≤ ‖p‖ + 2 := by
        have e : ‖poleP q‖ = ‖w‖ := by rcases hw with rfl | rfl <;> simp
        rw [e]
        have := Complex.norm_le_abs_re_add_abs_im w
        have := Complex.abs_im_le_norm p
        have : |w.im| ≤ |p.im| + δ := by
          have := abs_sub_abs_le_abs_sub w.im p.im; linarith
        linarith [min_le_right m 1]
      have hwD : w ∈ D := by rcases hw with rfl | rfl <;> [exact (hD q hnorm).1; exact (hD q hnorm).2]
      by_cases hi : w.im = p.im
      · have hwc : w ∈ cand := Finset.mem_filter.2 ⟨hwD, by linarith, hi⟩
        have := hmax w hwc
        linarith
      · have := hmD w hwD
        simp only [hi, ↓reduceIte] at this
        linarith [min_le_left m 1]
    exact ⟨fun e => key z (Or.inl e) hz, fun e => key z (Or.inr e) hz⟩
  have hFU : DifferentiableOn ℂ Fw U := fun z hz =>
    (Fw_differentiableAt (fun e0 => by
      have : ps.re < z.re := hz.1; rw [e0, zero_re] at this; linarith)
      (hnopole z hz)).differentiableWithinAt
  have hLU : DifferentiableOn ℂ L U := hLd.mono fun z hz => lt_trans hps0 (show ps.re < z.re from hz.1)
  set z0 : ℂ := (3 : ℝ) + p.im * I
  have hz0re : z0.re = 3 := by simp [z0]
  have hz0im : z0.im = p.im := by simp [z0]
  have hps1 : ps.re < 1 := by
    obtain ⟨q, hq⟩ := hpspole
    rcases hq with hq | hq
    · rw [← hq]; exact (abs_lt.1 (abs_re_poleP q)).2
    · rw [← hq, neg_re]; linarith [(abs_lt.1 (abs_re_poleP q)).1]
  have hEq : EqOn Fw L U := eqOn_convex hUo hUc hFU hLU (z0 := z0)
    ⟨show ps.re < z0.re by rw [hz0re]; linarith, show z0.im < p.im + δ by rw [hz0im]; linarith,
      show p.im - δ < z0.im by rw [hz0im]; linarith⟩
    (Fw_eventuallyEq_lap (by rw [hz0re]; norm_num))
  -- the pole test
  have hR : Rp ps = 0 := by
    refine residue_eq_zero (L := L) (G := Gp ps) one_pos
      ((hLd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hps0)).continuousAt)
      (Gp_continuousAt (fun e0 => by rw [e0, zero_re] at hps0; exact lt_irrefl _ hps0)) fun x hx _ => ?_
    have hU : ps + x ∈ U := ⟨show ps.re < (ps + x).re by simp; linarith,
      show (ps + x).im < p.im + δ by simp [hpsim]; linarith,
      show p.im - δ < (ps + x).im by simp [hpsim]; linarith⟩
    rw [← hEq hU, Fw_split ps]
  obtain ⟨q, hq⟩ := hpspole
  exact Rp_ne_zero hps0 hq hR

/-- **Weil's criterion for `ζ`, twin boxes only, no finiteness hypothesis.** -/
theorem rh_of_weil_twins (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l)) :
    RiemannHypothesis := by
  intro s hs htriv _
  exact line_of_weil_twins hQ ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

/-- **Weil's criterion for `ζ`, no finiteness hypothesis.** If `Q ≥ 0` for every probe at every
support, Mathlib's `RiemannHypothesis` holds. -/
theorem rh_of_weil (hQ : ∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ weilQ a g) :
    RiemannHypothesis :=
  rh_of_weil_twins fun l hl => hQ _ _ (by linarith) (twin_probe (box_probe 1) hl)

end Pilot1ca

#print axioms Pilot1ca.lap_eq_Fw
#print axioms Pilot1ca.conv_pos
#print axioms Pilot1ca.rh_of_weil_twins
#print axioms Pilot1ca.rh_of_weil
