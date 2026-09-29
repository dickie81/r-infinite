import Mathlib
import LandauLaplace

/-! # The Landau argument for twin forms, for any zero family (round 225)

Round 220's `WeilLandau` argument, abstracted from `ζ`. The data (`TwinData P c G Q`): a countable
family of poles `P_q` (for an L-function, `P = 2(ρ − ½)`) with `|Re P_q| < 1`, `Im P_q ≠ 0`, locally
finite; weights `c_q = G(P_q)` with `G` even, nonzero on `Re p > 0`, and `Σ‖c_q‖ < ∞`; and a real
function `Q` with `Q(λ) = Σ_q c_q(2 + e^{λP_q} + e^{−λP_q})` for `λ ≥ 0` (for an L-function, the
explicit formula for the twin boxes).

* `abs_re_le D`: `Q(λ) ≥ −C·e^{σλ}` on `λ ≥ 0` forces `|Re P_q| ≤ σ` for every `q`.
* `Q_ge D`: conversely `|Re P_q| ≤ σ` for all `q` gives `Q(λ) ≥ −4(Σ‖c_q‖)e^{σλ}`.
* `rate_iff`: the two together.

The proof is round 220's: the Laplace transform of `Q + C·e^{σλ}` is `F(z) + C/(z − σ)`,
`F = Σ_q c_q(2/z + 1/(z − P_q) + 1/(z + P_q))`; Landau's theorem continues the integral to
`Re z > σ`; the rightmost pole on a horizontal line has a nonzero residue. -/

open Real Filter Topology Complex Set MeasureTheory Metric

noncomputable section

namespace TwinLandau

open LandauLaplace

variable {ι : Type*} {P c : ι → ℂ} {G : ℂ → ℂ} {Q : ℝ → ℝ}

/-- The data of the twin-form Landau argument. -/
structure TwinData (P c : ι → ℂ) (G : ℂ → ℂ) (Q : ℝ → ℝ) : Prop where
  summ : Summable fun q => ‖c q‖
  re_lt : ∀ q, |(P q).re| < 1
  im_ne : ∀ q, (P q).im ≠ 0
  finite : ∀ R : ℝ, {q | ‖P q‖ ≤ R}.Finite
  c_eq : ∀ q, c q = G (P q)
  G_even : ∀ p, G (-p) = G p
  G_ne : ∀ p, 0 < p.re → G p ≠ 0
  hasSum : ∀ l : ℝ, 0 ≤ l → HasSum (fun q => c q * (2 + cexp (l * P q) + cexp (-(l * P q)))) (Q l)

variable (D : TwinData P c G Q)
include D

/-! ## The poles are locally finite -/

/-- **Separation from the poles.** Around any point there is a disc keeping a fixed distance from
every pole `±P_ρ` other than the point itself. -/
theorem sep (z0 : ℂ) : ∃ d > 0, ∀ z ∈ ball z0 d, ∀ q : ι,
    (z0 ≠ P q → d ≤ ‖z - P q‖) ∧ (z0 ≠ -P q → d ≤ ‖z + P q‖) := by
  classical
  set T := (D.finite (‖z0‖ + 2)).toFinset
  obtain ⟨m1, hm1, h1⟩ := exists_pos_lb T (fun q => if z0 = P q then 1 else ‖z0 - P q‖)
    fun q => by
      split_ifs with h
      · exact one_pos
      · exact norm_pos_iff.2 (sub_ne_zero.2 h)
  obtain ⟨m2, hm2, h2⟩ := exists_pos_lb T (fun q => if z0 = -P q then 1 else ‖z0 + P q‖)
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
      have t := norm_sub_le_norm_sub_add_norm_sub z0 z (P q)
      rw [norm_sub_rev z0 z] at t
      linarith
    · intro hne
      have := h2 q hq
      simp only [hne, ↓reduceIte] at this
      have t := norm_add_le (z0 - z) (z + P q)
      rw [show z0 - z + (z + P q) = z0 + P q by ring, norm_sub_rev z0 z] at t
      linarith
  · have hbig : ‖z0‖ + 2 < ‖P q‖ := by
      rw [Set.Finite.mem_toFinset, mem_ofPred_eq, not_le] at hq; exact hq
    constructor
    · intro _
      have := norm_sub_norm_le (P q) z
      rw [norm_sub_rev] at this
      have hz' : ‖z‖ ≤ ‖z0‖ + d := by
        have := norm_sub_norm_le z z0; linarith
      linarith
    · intro _
      have := norm_sub_norm_le (P q) (-z)
      rw [sub_neg_eq_add, add_comm, norm_neg] at this
      have hz' : ‖z‖ ≤ ‖z0‖ + d := by
        have := norm_sub_norm_le z z0; linarith
      linarith

/-! ## The kernel and its sum -/

/-- One zero's kernel `2/z + 1/(z − P) + 1/(z + P)`. -/
def hk (P z : ℂ) : ℂ := 2 / z + 1 / (z - P) + 1 / (z + P)

/-- The transform `F(z) = Σ_ρ ĝ₀(t_ρ)²(2/z + 1/(z − P_ρ) + 1/(z + P_ρ))`. -/
def Fw (P c : ι → ℂ) (z : ℂ) : ℂ := ∑' q, c q * hk (P q) z

omit D in
theorem norm_one_div_le {w : ℂ} {d : ℝ} (hd : 0 < d) (h : w ≠ 0 → d ≤ ‖w‖) : ‖1 / w‖ ≤ 1 / d := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp; positivity
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hd (h hw)

/-- The kernels at a fixed point are uniformly bounded over the zeros. -/
theorem hk_bound (z : ℂ) : ∃ B, ∀ q : ι, ‖1 / (z - P q)‖ ≤ B ∧ ‖1 / (z + P q)‖ ≤ B := by
  obtain ⟨d, hd, h⟩ := sep D z
  refine ⟨1 / d, fun q => ⟨norm_one_div_le hd fun hw => (h z (mem_ball_self hd) q).1 fun e => hw
    (by rw [e]; ring), norm_one_div_le hd fun hw => (h z (mem_ball_self hd) q).2 fun e => hw
    (by rw [e]; ring)⟩⟩

theorem summable_cw_mul {k : ι → ℂ} {B : ℝ} (hk : ∀ q, ‖k q‖ ≤ B) :
    Summable fun q => c q * k q :=
  (D.summ.mul_right B).of_norm_bounded fun q => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hk q) (norm_nonneg _)

theorem summable_hk (z : ℂ) : Summable fun q => c q * hk (P q) z := by
  obtain ⟨B, hB⟩ := hk_bound D z
  refine summable_cw_mul D (B := ‖2 / z‖ + B + B) fun q => ?_
  unfold hk
  exact (norm_add₃_le).trans (by linarith [(hB q).1, (hB q).2])

/-- **`F` is holomorphic off its poles.** -/
theorem Fw_differentiableAt {z0 : ℂ} (h0 : z0 ≠ 0) (hP : ∀ q, z0 ≠ P q ∧ z0 ≠ -P q) :
    DifferentiableAt ℂ (Fw P c) z0 := by
  obtain ⟨d, hd, h⟩ := sep D z0
  set e := min d (‖z0‖ / 2)
  have he : 0 < e := lt_min hd (by have := norm_pos_iff.2 h0; linarith)
  have hze : ∀ z ∈ ball z0 e, e ≤ ‖z‖ := fun z hz => by
    rw [mem_ball, Complex.dist_eq] at hz
    have := norm_sub_norm_le z0 (z0 - z)
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at hz
    linarith [min_le_right d (‖z0‖ / 2)]
  have hsub : ∀ z ∈ ball z0 e, ∀ q, e ≤ ‖z - P q‖ ∧ e ≤ ‖z + P q‖ := fun z hz q => by
    have hz' : z ∈ ball z0 d := ball_subset_ball (min_le_left _ _) hz
    exact ⟨(min_le_left _ _).trans ((h z hz' q).1 (hP q).1),
      (min_le_left _ _).trans ((h z hz' q).2 (hP q).2)⟩
  have hD : DifferentiableOn ℂ (Fw P c) (ball z0 e) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun q => ‖c q‖ * (4 / e))
      (D.summ.mul_right _) (fun q => ?_) isOpen_ball (fun q z hz => ?_)
    · intro z hz
      have h1 : z ≠ 0 := fun e0 => by have := hze z hz; rw [e0, norm_zero] at this; linarith
      have h2 : z - P q ≠ 0 := fun e0 => by
        have := (hsub z hz q).1; rw [e0, norm_zero] at this; linarith
      have h3 : z + P q ≠ 0 := fun e0 => by
        have := (hsub z hz q).2; rw [e0, norm_zero] at this; linarith
      have hd : DifferentiableAt ℂ (fun w : ℂ => c q * hk (P q) w) z := by
        unfold hk; fun_prop (disch := assumption)
      exact hd.differentiableWithinAt
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold hk
      have b1 : ‖2 / z‖ ≤ 2 / e := by
        rw [norm_div, Complex.norm_ofNat]; exact div_le_div_of_nonneg_left (by norm_num) he (hze z hz)
      have b2 := norm_one_div_le he (w := z - P q) fun _ => (hsub z hz q).1
      have b3 := norm_one_div_le he (w := z + P q) fun _ => (hsub z hz q).2
      calc _ ≤ ‖2 / z‖ + ‖1 / (z - P q)‖ + ‖1 / (z + P q)‖ := norm_add₃_le
        _ ≤ 2 / e + 1 / e + 1 / e := by linarith
        _ = 4 / e := by ring
  exact hD.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self he))

/-! ## The regular part at a pole -/

/-- The multiplicity indicator of `p` among `±P`. -/
def indR (p P : ℂ) : ℝ := (if P = p then 1 else 0) + (if -P = p then 1 else 0)

/-- The kernel with the pole at `p` removed. -/
def hkr (p P z : ℂ) : ℂ :=
  2 / z + (if P = p then 0 else 1 / (z - P)) + (if -P = p then 0 else 1 / (z + P))

omit D in
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
def Gp (P c : ι → ℂ) (p z : ℂ) : ℂ := ∑' q, c q * hkr p (P q) z

/-- The residue `R_p = Σ_ρ ĝ₀(t_ρ)²·#{±P_ρ = p}`. -/
def Rp (P c : ι → ℂ) (p : ℂ) : ℂ := ∑' q, c q * (indR p (P q) : ℂ)

omit D in
theorem indR_le (p P : ℂ) : indR p P ≤ 2 := by unfold indR; split_ifs <;> norm_num

omit D in
theorem indR_nonneg (p P : ℂ) : 0 ≤ indR p P := by unfold indR; split_ifs <;> norm_num

theorem Fw_split (p z : ℂ) : Fw P c z = Gp P c p z + Rp P c p / (z - p) := by
  obtain ⟨B, hB⟩ := hk_bound D z
  have hs1 : Summable fun q => c q * hkr p (P q) z := by
    refine summable_cw_mul D (B := ‖2 / z‖ + B + B) fun q => ?_
    unfold hkr
    refine (norm_add₃_le).trans ?_
    have b2 : ‖(if P q = p then 0 else 1 / (z - P q))‖ ≤ B := by
      split_ifs
      · simp; exact (norm_nonneg _).trans (hB q).1
      · exact (hB q).1
    have b3 : ‖(if -P q = p then 0 else 1 / (z + P q))‖ ≤ B := by
      split_ifs
      · simp; exact (norm_nonneg _).trans (hB q).1
      · exact (hB q).2
    linarith
  have hs2 : Summable fun q => c q * (indR p (P q) : ℂ) :=
    summable_cw_mul D (B := 2) fun q => by
      rw [Complex.norm_real, Real.norm_of_nonneg (indR_nonneg _ _)]; exact indR_le _ _
  unfold Fw Gp Rp
  simp_rw [hk_split p]
  rw [← tsum_div_const, ← hs1.tsum_add (hs2.div_const _)]
  congr 1; funext q; ring

/-- **The regular part is continuous at `p`.** -/
theorem Gp_continuousAt {p : ℂ} (hp : p ≠ 0) : ContinuousAt (Gp P c p) p := by
  obtain ⟨d, hd, h⟩ := sep D p
  set e := min d (‖p‖ / 2)
  have he : 0 < e := lt_min hd (by have := norm_pos_iff.2 hp; linarith)
  have hze : ∀ z ∈ ball p e, e ≤ ‖z‖ := fun z hz => by
    rw [mem_ball, Complex.dist_eq] at hz
    have := norm_sub_norm_le p (p - z)
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at hz
    linarith [min_le_right d (‖p‖ / 2)]
  have hC : ContinuousOn (Gp P c p) (ball p e) := by
    refine continuousOn_tsum (u := fun q => ‖c q‖ * (4 / e)) (fun q => ?_)
      (D.summ.mul_right _) (fun q z hz => ?_)
    · intro z hz
      have hz' : z ∈ ball p d := ball_subset_ball (min_le_left _ _) hz
      have h1 : z ≠ 0 := fun e0 => by have := hze z hz; rw [e0, norm_zero] at this; linarith
      refine ContinuousAt.continuousWithinAt ?_
      unfold hkr
      split_ifs with hq1 hq2 hq2
      · fun_prop (disch := assumption)
      · have := (h z hz' q).2 (Ne.symm hq2)
        have h3 : z + P q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        fun_prop (disch := assumption)
      · have := (h z hz' q).1 (Ne.symm hq1)
        have h3 : z - P q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        fun_prop (disch := assumption)
      · have := (h z hz' q).1 (Ne.symm hq1)
        have h3 : z - P q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        have := (h z hz' q).2 (Ne.symm hq2)
        have h4 : z + P q ≠ 0 := fun e0 => by rw [e0, norm_zero] at this; linarith
        fun_prop (disch := assumption)
    · have hz' : z ∈ ball p d := ball_subset_ball (min_le_left _ _) hz
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold hkr
      have b1 : ‖2 / z‖ ≤ 2 / e := by
        rw [norm_div, Complex.norm_ofNat]; exact div_le_div_of_nonneg_left (by norm_num) he (hze z hz)
      have b2 : ‖(if P q = p then 0 else 1 / (z - P q))‖ ≤ 1 / e := by
        split_ifs with hq
        · simp; positivity
        · exact norm_one_div_le he fun _ => (min_le_left _ _).trans ((h z hz' q).1 (Ne.symm hq))
      have b3 : ‖(if -P q = p then 0 else 1 / (z + P q))‖ ≤ 1 / e := by
        split_ifs with hq
        · simp; positivity
        · exact norm_one_div_le he fun _ => (min_le_left _ _).trans ((h z hz' q).2 (Ne.symm hq))
      calc _ ≤ _ := norm_add₃_le
        _ ≤ 2 / e + 1 / e + 1 / e := by linarith
        _ = 4 / e := by ring
  exact hC.continuousAt (isOpen_ball.mem_nhds (mem_ball_self he))

/-- **The residue at a pole off the imaginary axis is nonzero**: `R_p = N·G(p)`, `N ≥ 1`. -/
theorem Rp_ne_zero {p : ℂ} (hp : 0 < p.re) {q0 : ι} (hq0 : P q0 = p ∨ -P q0 = p) :
    Rp P c p ≠ 0 := by
  classical
  have hG : ∀ q, c q * (indR p (P q) : ℂ) = G p * (indR p (P q) : ℂ) := by
    intro q
    unfold indR
    by_cases h1 : P q = p
    · rw [D.c_eq, h1]
    · by_cases h2 : -P q = p
      · rw [D.c_eq, ← D.G_even, h2]
      · simp [h1, h2]
  unfold Rp
  simp_rw [hG]
  have hsum : Summable fun q => indR p (P q) := by
    refine summable_of_ne_finset_zero (s := (D.finite ‖p‖).toFinset) fun q hq => ?_
    rw [Set.Finite.mem_toFinset, mem_ofPred_eq, not_le] at hq
    unfold indR
    have h1 : P q ≠ p := fun e => by rw [e] at hq; exact lt_irrefl _ hq
    have h2 : -P q ≠ p := fun e => by rw [← e, norm_neg] at hq; exact lt_irrefl _ hq
    simp [h1, h2]
  rw [tsum_mul_left, ← Complex.ofReal_tsum]
  have hpos : 0 < ∑' q, indR p (P q) := by
    have h1 : 1 ≤ indR p (P q0) := by
      unfold indR
      rcases hq0 with h | h
      · simp only [h, ↓reduceIte]; split_ifs <;> norm_num
      · simp only [h, ↓reduceIte]; split_ifs <;> norm_num
    have := hsum.le_tsum q0 (fun q _ => indR_nonneg _ _)
    linarith
  exact mul_ne_zero (D.G_ne p hp) (by exact_mod_cast hpos.ne')

/-! ## The twin boxes' form as a sum of exponentials -/

/-- One zero's term `ĝ₀(t)²(2 + e^{λP} + e^{−λP})`. -/
def wq (P c : ι → ℂ) (q : ι) (l : ℝ) : ℂ := c q * (2 + cexp (l * P q) + cexp (-(l * P q)))

omit D in
theorem twin_sq (l : ℝ) (t G : ℂ) :
    (2 * Complex.cos (l * t) * G) ^ 2 = G ^ 2 * (2 + cexp (l * (2 * I * t)) + cexp (-(l * (2 * I * t)))) := by
  have hu : cexp (l * (2 * I * t)) = cexp (l * t * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hv : cexp (-(l * (2 * I * t))) = cexp (-(l * t) * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have huv : cexp (l * t * I) * cexp (-(l * t) * I) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  rw [Complex.cos, hu, hv]
  linear_combination (2 * G ^ 2) * huv

omit D in
theorem norm_wq_le_of {q : ι} {r : ℝ} (hr : |(P q).re| ≤ r) (l : ℝ) :
    ‖wq P c q l‖ ≤ ‖c q‖ * (4 * Real.exp (r * |l|)) := by
  unfold wq
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hlr : |l * (P q).re| ≤ r * |l| := by
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hr (abs_nonneg l)
  have b1 : ‖cexp (↑l * P q)‖ ≤ Real.exp (r * |l|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have e : (↑l * P q).re = l * (P q).re := by simp
    rw [e]; exact (le_abs_self _).trans hlr
  have b2 : ‖cexp (-(↑l * P q))‖ ≤ Real.exp (r * |l|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have e : (-(↑l * P q)).re = -(l * (P q).re) := by simp
    rw [e]; exact (neg_le_abs _).trans hlr
  have h1 : 1 ≤ Real.exp (r * |l|) :=
    Real.one_le_exp (mul_nonneg ((abs_nonneg _).trans hr) (abs_nonneg l))
  calc ‖2 + cexp (↑l * P q) + cexp (-(↑l * P q))‖
      ≤ ‖(2 : ℂ)‖ + ‖cexp (↑l * P q)‖ + ‖cexp (-(↑l * P q))‖ := norm_add₃_le
    _ ≤ 2 + Real.exp (r * |l|) + Real.exp (r * |l|) := by rw [Complex.norm_ofNat]; linarith
    _ ≤ 4 * Real.exp (r * |l|) := by linarith

theorem norm_wq_le (q : ι) (l : ℝ) : ‖wq P c q l‖ ≤ ‖c q‖ * (4 * Real.exp |l|) := by
  simpa using norm_wq_le_of (D.re_lt q).le l

/-- The function `λ ↦ Σ_ρ ĝ₀(t_ρ)²(2 + e^{λP_ρ} + e^{−λP_ρ})`, defined for every real `λ`. -/
def Wsum (P c : ι → ℂ) (l : ℝ) : ℂ := ∑' q, wq P c q l

theorem continuous_Wsum : Continuous (Wsum P c) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hC : ContinuousOn (Wsum P c) (Ioo (x - 1) (x + 1)) := by
    refine continuousOn_tsum (u := fun q => ‖c q‖ * (4 * Real.exp (|x| + 1))) (fun q => ?_)
      (D.summ.mul_right _) (fun q l hl => ?_)
    · unfold wq; exact Continuous.continuousOn (by fun_prop)
    · refine (norm_wq_le D q l).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      have : |l| ≤ |x| + 1 := by
        have h1 := abs_sub_abs_le_abs_sub l x
        have h2 : |l - x| < 1 := abs_lt.2 ⟨by linarith [hl.1], by linarith [hl.2]⟩
        linarith
      gcongr
  exact hC.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

theorem norm_Wsum_le_of {r : ℝ} (hr : ∀ q, |(P q).re| ≤ r) (l : ℝ) :
    ‖Wsum P c l‖ ≤ (∑' q, ‖c q‖) * (4 * Real.exp (r * |l|)) := by
  unfold Wsum
  have hs : Summable fun q => ‖wq P c q l‖ :=
    (D.summ.mul_right (4 * Real.exp (r * |l|))).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => norm_wq_le_of (hr q) l)
  calc ‖∑' q, wq P c q l‖ ≤ ∑' q, ‖wq P c q l‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' q, ‖c q‖ * (4 * Real.exp (r * |l|)) :=
        hs.tsum_le_tsum (fun q => norm_wq_le_of (hr q) l) (D.summ.mul_right _)
    _ = _ := tsum_mul_right

theorem norm_Wsum_le (l : ℝ) : ‖Wsum P c l‖ ≤ (∑' q, ‖c q‖) * (4 * Real.exp |l|) := by
  simpa using norm_Wsum_le_of D (fun q => (D.re_lt q).le) l

/-! ## The Laplace transform in `λ` -/

/-- The transform's input `A(λ) = Re Σ_ρ(…)`; it equals `Q(twin λ)` for `λ ≥ 0`. -/
def Aw (P c : ι → ℂ) (l : ℝ) : ℝ := (Wsum P c l).re

theorem Wsum_eq {l : ℝ} (hl : 0 ≤ l) : Wsum P c l = (Q l : ℂ) := (D.hasSum l hl).tsum_eq

theorem Aw_eq {l : ℝ} (hl : 0 ≤ l) : Aw P c l = Q l := by
  unfold Aw; rw [Wsum_eq D hl, ofReal_re]

theorem Aw_ofReal {l : ℝ} (hl : 0 ≤ l) : (Aw P c l : ℂ) = Wsum P c l := by
  rw [Aw_eq D hl, Wsum_eq D hl]

theorem continuous_Aw : Continuous (Aw P c) := Complex.continuous_re.comp (continuous_Wsum D)

theorem abs_Aw_le {l : ℝ} (hl : 0 ≤ l) : |Aw P c l| ≤ (∑' q, ‖c q‖) * (4 * Real.exp l) := by
  have := norm_Wsum_le D l
  rw [abs_of_nonneg hl] at this
  exact (Complex.abs_re_le_norm _).trans this

/-- The input shifted by the allowed defect: `A(λ) = Q(λ) + C·e^{σλ}`. -/
def Awc (P c : ι → ℂ) (C σ l : ℝ) : ℝ := Aw P c l + C * Real.exp (σ * l)

theorem hyp_Awc {C σ : ℝ}
    (hQ : ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Q l) :
    Hyp (volume.restrict (Ioi (0 : ℝ))) (Awc P c C σ) (fun l => l) where
  A_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => by
    unfold Awc; rw [Aw_eq D hl.le]; linarith [hQ l hl.le])
  ph_nonneg := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => hl.le)
  A_meas := ((continuous_Aw D).add (by fun_prop)).aestronglyMeasurable
  ph_meas := continuous_id.aestronglyMeasurable

theorem conv_Awc {C σ : ℝ} (hσ : 0 ≤ σ) :
    Conv (volume.restrict (Ioi (0 : ℝ))) (Awc P c C σ) (fun l => l) (σ + 2) := by
  set S := ∑' q, ‖c q‖
  have hS : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hi : IntegrableOn (fun l : ℝ => (4 * S + |C|) * Real.exp (-1 * l)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  refine hi.mono' (((continuous_Aw D).add (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => ?_))
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  unfold Awc
  have h1 := abs_Aw_le D hl.le
  have h2 : |C * Real.exp (σ * l)| = |C| * Real.exp (σ * l) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp l * Real.exp (-(σ + 2) * l) ≤ Real.exp (-1 * l) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have e2 : Real.exp (σ * l) * Real.exp (-(σ + 2) * l) ≤ Real.exp (-1 * l) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have hE := Real.exp_pos (-(σ + 2) * l)
  calc |Aw P c l + C * Real.exp (σ * l)| * Real.exp (-(σ + 2) * l)
      ≤ (S * (4 * Real.exp l) + |C| * Real.exp (σ * l)) * Real.exp (-(σ + 2) * l) := by
        refine mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans ?_) hE.le
        rw [h2]; linarith
    _ = 4 * S * (Real.exp l * Real.exp (-(σ + 2) * l))
        + |C| * (Real.exp (σ * l) * Real.exp (-(σ + 2) * l)) := by ring
    _ ≤ 4 * S * Real.exp (-1 * l) + |C| * Real.exp (-1 * l) := by
        gcongr
    _ = _ := by ring

omit D in
/-- One zero's transform: `∫_0^∞ ĝ₀²(2 + e^{λP} + e^{−λP})e^{−zλ}dλ = ĝ₀²(2/z + 1/(z − P) + 1/(z + P))`
for `Re z > 1`. -/
theorem wq_exp_eq (q : ι) (z : ℂ) (l : ℝ) :
    wq P c q l * cexp (-z * l) = c q * (2 * cexp (-z * l) + cexp ((P q - z) * l)
      + cexp ((-P q - z) * l)) := by
  unfold wq
  rw [show (P q - z) * l = l * P q + -z * l by ring,
    show (-P q - z) * l = -(l * P q) + -z * l by ring, Complex.exp_add, Complex.exp_add]
  ring

theorem re_lt_of_one_lt {z : ℂ} (hz : 1 < z.re) (q : ι) :
    (P q - z).re < 0 ∧ (-P q - z).re < 0 ∧ (-z).re < 0 := by
  have := abs_lt.1 (D.re_lt q)
  simp only [sub_re, neg_re]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem integrable_wq (q : ι) {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun l : ℝ => wq P c q l * cexp (-z * l)) (Ioi 0) := by
  obtain ⟨h1, h2, h3⟩ := re_lt_of_one_lt D hz q
  simp_rw [wq_exp_eq]
  exact ((((integrableOn_exp_mul_complex_Ioi h3 0).const_mul 2).add
    (integrableOn_exp_mul_complex_Ioi h1 0)).add (integrableOn_exp_mul_complex_Ioi h2 0)).const_mul _

theorem integral_wq (q : ι) {z : ℂ} (hz : 1 < z.re) :
    ∫ l in Ioi (0 : ℝ), wq P c q l * cexp (-z * l) = c q * hk (P q) z := by
  obtain ⟨h1, h2, h3⟩ := re_lt_of_one_lt D hz q
  simp_rw [wq_exp_eq]
  have i1 : IntegrableOn (fun l : ℝ => 2 * cexp (-z * l)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi h3 0).const_mul 2
  have i2 : IntegrableOn (fun l : ℝ => cexp ((P q - z) * l)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi h1 0
  have i3 : IntegrableOn (fun l : ℝ => cexp ((-P q - z) * l)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi h2 0
  have i12 : IntegrableOn (fun l : ℝ => 2 * cexp (-z * l) + cexp ((P q - z) * l)) (Ioi 0) :=
    i1.add i2
  rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_exp_mul_complex_Ioi h3, integral_exp_mul_complex_Ioi h1, integral_exp_mul_complex_Ioi h2]
  unfold hk
  have hP := abs_lt.1 (D.re_lt q)
  have hz0 : z ≠ 0 := fun e => by rw [e] at hz; simp at hz; linarith
  have hz1 : z - P q ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp only [sub_re, zero_re] at this; linarith [hP.1, hP.2]
  have hz2 : z + P q ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp only [add_re, zero_re] at this; linarith [hP.1, hP.2]
  have hz1' : P q - z ≠ 0 := fun e => hz1 (by rw [← neg_sub, e, neg_zero])
  have hz2' : -P q - z ≠ 0 := fun e => hz2 (by linear_combination -e)
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- **The transform equals `F` for `Re z > 1`.** -/
theorem lap_eq_Fw [Countable ι] {z : ℂ} (hz : 1 < z.re) :
    lap (volume.restrict (Ioi (0 : ℝ))) (Aw P c) (fun l => l) z = Fw P c z := by
  unfold lap
  have e : ∫ l in Ioi (0 : ℝ), (Aw P c l : ℂ) * cexp (-z * l)
      = ∫ l in Ioi (0 : ℝ), ∑' q, wq P c q l * cexp (-z * l) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun l (hl : 0 < l) => ?_
    rw [Aw_ofReal D hl.le, Wsum, tsum_mul_right]
  rw [e, ← integral_tsum_of_summable_integral_norm (fun q => integrable_wq D q hz)]
  · unfold Fw; congr 1; funext q; exact integral_wq D q hz
  · set K := ∫ l in Ioi (0 : ℝ), 4 * Real.exp (-(z.re - 1) * l)
    have hK : IntegrableOn (fun l : ℝ => 4 * Real.exp (-(z.re - 1) * l)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
    refine (D.summ.mul_right K).of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _)
      fun q => ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hK.const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => ?_))
    show ‖wq P c q l * cexp (-z * l)‖ ≤ ‖c q‖ * (4 * Real.exp (-(z.re - 1) * l))
    rw [norm_mul, Complex.norm_exp]
    have h1 := norm_wq_le D q l
    rw [abs_of_pos hl] at h1
    have e2 : (-z * l).re = -z.re * l := by simp
    rw [e2]
    calc ‖wq P c q l‖ * Real.exp (-z.re * l) ≤ ‖c q‖ * (4 * Real.exp l) * Real.exp (-z.re * l) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = ‖c q‖ * (4 * Real.exp (-(z.re - 1) * l)) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf

/-- `F` plus the transform of the defect: `F(z) + C/(z − σ)`. -/
def Fwc (P c : ι → ℂ) (C σ : ℝ) (z : ℂ) : ℂ := Fw P c z + C / (z - σ)

theorem integrableOn_Aw_exp {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun l : ℝ => (Aw P c l : ℂ) * cexp (-z * l)) (Ioi 0) := by
  set S := ∑' q, ‖c q‖
  have hi : IntegrableOn (fun l : ℝ => 4 * S * Real.exp (-(z.re - 1) * l)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  refine hi.mono' ((Complex.continuous_ofReal.comp (continuous_Aw D)).mul (by fun_prop)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l (hl : 0 < l) => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have e2 : (-z * l).re = -z.re * l := by simp
  rw [e2]
  calc |Aw P c l| * Real.exp (-z.re * l) ≤ S * (4 * Real.exp l) * Real.exp (-z.re * l) :=
        mul_le_mul_of_nonneg_right (abs_Aw_le D hl.le) (Real.exp_pos _).le
    _ = 4 * S * Real.exp (-(z.re - 1) * l) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf

/-- **The transform of `Q + C·e^{σλ}` is `F(z) + C/(z − σ)`** for `Re z > max(1, σ)`. -/
theorem lap_Awc [Countable ι] {C σ : ℝ} {z : ℂ} (hz : 1 < z.re) (hzσ : σ < z.re) :
    lap (volume.restrict (Ioi (0 : ℝ))) (Awc P c C σ) (fun l => l) z = Fwc P c C σ z := by
  have ha : ((σ : ℂ) - z).re < 0 := by simp; linarith
  have i2 : IntegrableOn (fun l : ℝ => (C : ℂ) * cexp (((σ : ℂ) - z) * l)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi ha 0).const_mul _
  have e : ∀ l : ℝ, ((Awc P c C σ l : ℝ) : ℂ) * cexp (-z * l)
      = (Aw P c l : ℂ) * cexp (-z * l) + (C : ℂ) * cexp (((σ : ℂ) - z) * l) := fun l => by
    unfold Awc
    push_cast
    rw [show ((σ : ℂ) - z) * l = σ * l + -z * l by ring, Complex.exp_add]
    ring
  unfold lap
  simp_rw [e]
  rw [integral_add (integrableOn_Aw_exp D hz) i2, integral_const_mul, integral_exp_mul_complex_Ioi ha]
  have := lap_eq_Fw D hz
  unfold lap at this
  rw [this]
  unfold Fwc
  have hz' : z - σ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hz'' : (σ : ℂ) - z ≠ 0 := fun h => hz' (by rw [← neg_sub, h, neg_zero])
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

theorem Fwc_eventuallyEq_lap [Countable ι] {C σ : ℝ} {z0 : ℂ} (hz : 1 < z0.re) (hzσ : σ < z0.re) :
    Fwc P c C σ =ᶠ[𝓝 z0] lap (volume.restrict (Ioi (0 : ℝ))) (Awc P c C σ) (fun l => l) :=
  Filter.eventually_of_mem (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds ⟨hz, hzσ⟩)
    fun _ hz => (lap_Awc D hz.1 hz.2).symm

theorem Fwc_differentiableAt {C σ : ℝ} {z0 : ℂ} (h0 : z0 ≠ 0) (hσ : z0 ≠ σ)
    (hP : ∀ q, z0 ≠ P q ∧ z0 ≠ -P q) : DifferentiableAt ℂ (Fwc P c C σ) z0 := by
  have h1 := Fw_differentiableAt D h0 hP
  have h2 : z0 - σ ≠ 0 := sub_ne_zero.2 hσ
  unfold Fwc
  exact h1.add ((differentiableAt_const _).div (differentiableAt_id.sub_const _) h2)

/-- The poles keep a fixed distance from the real axis. -/
theorem exists_im_lb : ∃ d > 0, ∀ q : ι, d ≤ |(P q).im| := by
  classical
  obtain ⟨m, hm, h⟩ := exists_pos_lb (D.finite 2).toFinset (fun q => |(P q).im|)
    fun q => abs_pos.2 (D.im_ne q)
  refine ⟨min m 1, lt_min hm one_pos, fun q => ?_⟩
  by_cases hq : q ∈ (D.finite 2).toFinset
  · exact (min_le_left _ _).trans (h q hq)
  · rw [Set.Finite.mem_toFinset, mem_ofPred_eq, not_le] at hq
    have := Complex.norm_le_abs_re_add_abs_im (P q)
    have := D.re_lt q
    exact (min_le_right _ _).trans (by linarith)

omit D in
theorem not_pole_of_im {z : ℂ} {d : ℝ} (hd : ∀ q : ι, d ≤ |(P q).im|) (hz : |z.im| < d)
    (q : ι) : z ≠ P q ∧ z ≠ -P q := by
  constructor
  · intro e; have := hd q; rw [← e] at this; linarith
  · intro e; have := hd q; rw [← neg_neg (P q), ← e, neg_im, abs_neg] at this; linarith

/-- **Step 1: the transform converges on `Re z > σ`.** -/
theorem conv_gt [Countable ι] {C σ : ℝ} (hσ : 0 ≤ σ)
    (hQ : ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Q l) :
    ∀ τ, σ < τ → Conv (volume.restrict (Ioi (0 : ℝ))) (Awc P c C σ) (fun l => l) τ := by
  have h := hyp_Awc D hQ
  obtain ⟨d, hd, hdq⟩ := exists_im_lb D
  refine landau_abscissa h (conv_Awc D hσ) fun cc hc habove => ?_
  set e := min (d / 2) ((cc - σ) / 2)
  have he : 0 < e := lt_min (by positivity) (by linarith)
  set W : Set ℂ := {s | cc < s.re} ∩ ({s | s.im < d / 2} ∩ {s | -(d / 2) < s.im})
  have hWo : IsOpen W := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hWc : Convex ℝ W := (convex_halfSpace_re_gt cc).inter
    ((convex_halfSpace_im_lt (d / 2)).inter (convex_halfSpace_im_gt (-(d / 2))))
  have hFd : ∀ z : ℂ, σ < z.re → |z.im| < d → DifferentiableAt ℂ (Fwc P c C σ) z := fun z hz hzi =>
    Fwc_differentiableAt D (fun e0 => by rw [e0, zero_re] at hz; linarith)
      (fun e0 => by rw [e0, ofReal_re] at hz; exact lt_irrefl _ hz) (not_pole_of_im hdq hzi)
  have hLd := lap_differentiableOn h habove
  set z1 : ℝ := max cc (σ + 2) + 1
  have hEq : EqOn (Fwc P c C σ) (lap (volume.restrict (Ioi (0 : ℝ))) (Awc P c C σ) (fun l => l)) W := by
    refine eqOn_convex hWo hWc (fun z hz => (hFd z (lt_trans hc (show cc < z.re from hz.1)) (abs_lt.2
      ⟨by linarith [show -(d / 2) < z.im from hz.2.2], by linarith [show z.im < d / 2 from hz.2.1]⟩)).differentiableWithinAt)
      (hLd.mono fun z hz => hz.1) (z0 := (z1 : ℂ)) ?_ (Fwc_eventuallyEq_lap D ?_ ?_)
    · refine ⟨?_, ?_, ?_⟩
      · show cc < (z1 : ℂ).re; rw [ofReal_re]; linarith [le_max_left cc (σ + 2)]
      · show (z1 : ℂ).im < d / 2; rw [ofReal_im]; positivity
      · show -(d / 2) < (z1 : ℂ).im; rw [ofReal_im]; linarith
    · show 1 < (z1 : ℂ).re; rw [ofReal_re]; linarith [le_max_right cc (σ + 2)]
    · show σ < (z1 : ℂ).re; rw [ofReal_re]; linarith [le_max_right cc (σ + 2)]
  refine ⟨e, he, Fwc P c C σ, fun z hz => ?_, fun s hs hsc => hEq ⟨hsc, ?_, ?_⟩⟩
  · rw [mem_ball, Complex.dist_eq] at hz
    have h1 := Complex.abs_re_le_norm (z - cc)
    have h2 := Complex.abs_im_le_norm (z - cc)
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h1 h2
    refine (hFd z ?_ ?_).differentiableWithinAt
    · have := (abs_lt.1 (h1.trans_lt (hz.trans_le (min_le_right _ _)))).1; linarith
    · have := h2.trans_lt (hz.trans_le (min_le_left _ _)); linarith
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - cc)
    simp only [sub_im, ofReal_im, sub_zero] at h2
    have := h2.trans_lt (hs.trans_le (min_le_left _ _)); rw [abs_lt] at this; exact this.2
  · rw [mem_ball, Complex.dist_eq] at hs
    have h2 := Complex.abs_im_le_norm (s - cc)
    simp only [sub_im, ofReal_im, sub_zero] at h2
    have := h2.trans_lt (hs.trans_le (min_le_left _ _)); rw [abs_lt] at this; exact this.1

/-- **The graded criterion.** If `Q(twin (box 1) λ) ≥ −C·e^{σλ}` for every `λ ≥ 0` (`σ ≥ 0`), every
nontrivial zero has `|2 Re ρ − 1| ≤ σ`, i.e. `|Re P_ρ| ≤ σ`. -/
theorem abs_re_le [Countable ι] {C σ : ℝ} (hσ : 0 ≤ σ)
    (hQ : ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Q l) (q0 : ι) :
    |(P q0).re| ≤ σ := by
  classical
  by_contra hoff
  push Not at hoff
  have h := hyp_Awc D hQ
  have hconv := conv_gt D hσ hQ
  set L := lap (volume.restrict (Ioi (0 : ℝ))) (Awc P c C σ) (fun l => l)
  have hLd : DifferentiableOn ℂ L {s | σ < s.re} := lap_differentiableOn h hconv
  -- a pole to the right of `σ`
  set p : ℂ := if 0 < (P q0).re then P q0 else -P q0
  have hp : σ < p.re := by
    simp only [p]; split_ifs with h1
    · rwa [abs_of_pos h1] at hoff
    · push Not at h1; rw [neg_re]; rwa [abs_of_nonpos h1] at hoff
  -- the poles near `p`, and the rightmost one on the horizontal line through `p`
  set T := (D.finite (‖p‖ + 2)).toFinset
  set DS : Finset ℂ := T.image P ∪ T.image (fun q => -P q)
  have hD : ∀ q : ι, ‖P q‖ ≤ ‖p‖ + 2 → P q ∈ DS ∧ -P q ∈ DS := fun q hq => by
    have : q ∈ T := (Set.Finite.mem_toFinset _).2 hq
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ this),
      Finset.mem_union_right _ (Finset.mem_image_of_mem (fun q => -P q) this)⟩
  set cand := DS.filter fun z => p.re ≤ z.re ∧ z.im = p.im
  have hpc : p ∈ cand := by
    have hq0 : ‖P q0‖ ≤ ‖p‖ + 2 := by
      simp only [p]; split_ifs <;> simp
    refine Finset.mem_filter.2 ⟨?_, le_rfl, rfl⟩
    simp only [p]; split_ifs
    · exact (hD q0 hq0).1
    · exact (hD q0 hq0).2
  obtain ⟨ps, hps, hmax⟩ := cand.exists_max_image Complex.re ⟨p, hpc⟩
  obtain ⟨hpsD, hpsre, hpsim⟩ := Finset.mem_filter.1 hps
  have hpspole : ∃ q, P q = ps ∨ -P q = ps := by
    rcases Finset.mem_union.1 hpsD with h1 | h1
    · obtain ⟨q, -, hq⟩ := Finset.mem_image.1 h1; exact ⟨q, Or.inl hq⟩
    · obtain ⟨q, -, hq⟩ := Finset.mem_image.1 h1; exact ⟨q, Or.inr hq⟩
  have hpsσ : σ < ps.re := lt_of_lt_of_le hp hpsre
  have hps0 : 0 < ps.re := lt_of_le_of_lt hσ hpsσ
  -- the pole-free strip to the right of `ps`
  obtain ⟨m, hm, hmD⟩ := exists_pos_lb DS (fun z => if z.im = p.im then 1 else |z.im - p.im|)
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
  have hnopole : ∀ z ∈ U, ∀ q, z ≠ P q ∧ z ≠ -P q := by
    intro z hz q
    have key : ∀ w : ℂ, (w = P q ∨ w = -P q) → w ∉ U := by
      intro w hw hwU
      have hU1 : ps.re < w.re := hwU.1
      have hU2 : w.im < p.im + δ := hwU.2.1
      have hU3 : p.im - δ < w.im := hwU.2.2
      have hwre : |w.re| < 1 := by
        rcases hw with rfl | rfl
        · exact D.re_lt q
        · rw [neg_re, abs_neg]; exact D.re_lt q
      have hwim : |w.im - p.im| < δ := abs_lt.2 ⟨by linarith, by linarith⟩
      have hnorm : ‖P q‖ ≤ ‖p‖ + 2 := by
        have e : ‖P q‖ = ‖w‖ := by rcases hw with rfl | rfl <;> simp
        rw [e]
        have := Complex.norm_le_abs_re_add_abs_im w
        have := Complex.abs_im_le_norm p
        have : |w.im| ≤ |p.im| + δ := by
          have := abs_sub_abs_le_abs_sub w.im p.im; linarith
        linarith [min_le_right m 1]
      have hwD : w ∈ DS := by rcases hw with rfl | rfl <;> [exact (hD q hnorm).1; exact (hD q hnorm).2]
      by_cases hi : w.im = p.im
      · have hwc : w ∈ cand := Finset.mem_filter.2 ⟨hwD, by linarith, hi⟩
        have := hmax w hwc
        linarith
      · have := hmD w hwD
        simp only [hi, ↓reduceIte] at this
        linarith [min_le_left m 1]
    exact ⟨fun e => key z (Or.inl e) hz, fun e => key z (Or.inr e) hz⟩
  have hFU : DifferentiableOn ℂ (Fwc P c C σ) U := fun z hz => by
    have hz1 : ps.re < z.re := hz.1
    exact (Fwc_differentiableAt D (fun e0 => by rw [e0, zero_re] at hz1; linarith)
      (fun e0 => by rw [e0, ofReal_re] at hz1; linarith) (hnopole z hz)).differentiableWithinAt
  have hLU : DifferentiableOn ℂ L U := hLd.mono fun z hz => lt_trans hpsσ (show ps.re < z.re from hz.1)
  set z0 : ℂ := ((σ + 3 : ℝ) : ℂ) + p.im * I
  have hz0re : z0.re = σ + 3 := by simp [z0]
  have hz0im : z0.im = p.im := by simp [z0]
  have hps1 : ps.re < 1 := by
    obtain ⟨q, hq⟩ := hpspole
    rcases hq with hq | hq
    · rw [← hq]; exact (abs_lt.1 (D.re_lt q)).2
    · rw [← hq, neg_re]; linarith [(abs_lt.1 (D.re_lt q)).1]
  have hEq : EqOn (Fwc P c C σ) L U := eqOn_convex hUo hUc hFU hLU (z0 := z0)
    ⟨show ps.re < z0.re by rw [hz0re]; linarith, show z0.im < p.im + δ by rw [hz0im]; linarith,
      show p.im - δ < z0.im by rw [hz0im]; linarith⟩
    (Fwc_eventuallyEq_lap D (by rw [hz0re]; linarith) (by rw [hz0re]; linarith))
  -- the pole test
  have hpsσ' : ps - σ ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  have hR : Rp P c ps = 0 := by
    refine residue_eq_zero (L := L) (G := fun z => Gp P c ps z + C / (z - σ)) one_pos
      ((hLd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpsσ)).continuousAt)
      ((Gp_continuousAt D (fun e0 => by rw [e0, zero_re] at hps0; exact lt_irrefl _ hps0)).add
        (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hpsσ')) fun x hx _ => ?_
    have hU : ps + x ∈ U := ⟨show ps.re < (ps + x).re by simp; linarith,
      show (ps + x).im < p.im + δ by simp [hpsim]; linarith,
      show p.im - δ < (ps + x).im by simp [hpsim]; linarith⟩
    rw [← hEq hU]
    unfold Fwc
    rw [Fw_split D ps]
    ring
  obtain ⟨q, hq⟩ := hpspole
  exact Rp_ne_zero D hps0 hq hR

/-- **The converse bound**: `|Re P_q| ≤ σ` for every `q` gives `Q(λ) ≥ −4(Σ‖c_q‖)e^{σλ}`. -/
theorem Q_ge {σ : ℝ} (hz : ∀ q, |(P q).re| ≤ σ) {l : ℝ} (hl : 0 ≤ l) :
    -((4 * ∑' q, ‖c q‖) * Real.exp (σ * l)) ≤ Q l := by
  rw [← Aw_eq D hl]
  have h := norm_Wsum_le_of D hz l
  rw [abs_of_nonneg hl] at h
  have := neg_abs_le (Wsum P c l).re
  have := Complex.abs_re_le_norm (Wsum P c l)
  unfold Aw
  nlinarith

/-- **The graded criterion**: for `σ ≥ 0`, `Q(λ) ≥ −C·e^{σλ}` on `λ ≥ 0` for some `C` iff
`|Re P_q| ≤ σ` for every `q`. -/
theorem rate_iff [Countable ι] {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Q l) ↔ ∀ q, |(P q).re| ≤ σ :=
  ⟨fun ⟨_, h⟩ q => abs_re_le D hσ h q, fun h => ⟨_, fun _ hl => Q_ge D h hl⟩⟩

end TwinLandau

#print axioms TwinLandau.abs_re_le
#print axioms TwinLandau.rate_iff
