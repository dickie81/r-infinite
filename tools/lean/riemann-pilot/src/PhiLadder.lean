import Mathlib
import PhiDecay
import ParityCont

/-! # Round 153: jet upper bounds on the low spectrum (rungs 1 and 2 of the ladder)

Round 133 (`lam_decay`) bounds rung 0: `λ₁(a) ≤ K e^{−Ba}` for every `B`, from the truncated null
vector `Φ_a`. This file bounds the next two rungs in the same way, with the same named input
(`WeilExplicit` for the trial functions used; `DigammaDiff` is proved, round 154) and **no RH
input**: the zero family may lie anywhere in the strip `|Im t| ≤ ½`.

The trial functions are copies of `Φ_b`, `b = a/8`, shifted to disjoint positions:
* **twins** `T_l = Φ_b(· − l) + Φ_b(· + l)` (`twin`, round 62), with `T̂_l = 2cos(lz)Φ̂_b`;
* the **antitwin** `A_l = Φ_b(· − l) − Φ_b(· + l)`, odd.

* **Rung 1** (`lamO_decay`). The parity split of the shifted copy `x = Φ_b(· − l)` and translation
  invariance give `Q(A_l) = 4Q(Φ_b) − Q(T_l) = Σ_ρ 4 sin²(l t_ρ)Φ̂_b(t_ρ)²`: the odd ground energy is
  `≤ K e^{−Ba}` for every `B`. Only the even explicit formula is used.
* **Rung 2** (`lam2_decay`). `T_{a/4}` and `T_{3a/4}` have disjoint supports, hence are orthogonal;
  on their span `Q ≤ 8e^{3a/4}N⁻¹Σ‖Φ̂_b‖²`, so every `s` with `Lam2Ge a s` (`λ₂ ≥ s` in min–max form)
  satisfies `s ≤ K e^{−Ba}`.

These are the *upper* halves of the rungs. The lower halves are RH-strength (round 152).
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace Pilot1ca

open Pilot1bt

/-! ## A. Shifts, twins and antitwins -/

/-- `ĝ` does not depend on the window once it contains the support. -/
theorem ghatC_window {g : ℝ → ℝ} {r a : ℝ} (hr : 0 < r) (hra : r ≤ a)
    (hsupp : ∀ u, r < |u| → g u = 0) (z : ℂ) : ghatC g a z = ghatC g r z := by
  rw [ghatC_eq_integral (hr.trans_le hra) (fun u hu => hsupp u (lt_of_le_of_lt hra hu)),
    ghatC_eq_integral hr hsupp]

/-- The antitwin `A_l = g₀(· − l) − g₀(· + l)`. -/
def atwin (g₀ : ℝ → ℝ) (l : ℝ) (u : ℝ) : ℝ := g₀ (u - l) - g₀ (u + l)

/-- A shifted probe is a probe of either parity. -/
theorem sprobe_shift {b a : ℝ} {g₀ : ℝ → ℝ} (hp : Probe b g₀) {c : ℝ} (h : b + |c| ≤ a) :
    SProbe a (fun t => g₀ (t + c)) := by
  refine ⟨fun u hu => hp.supp _ ?_, memLp_shift hp.memL2 c, ?_⟩
  · have := abs_sub_abs_le_abs_sub u (-c); rw [sub_neg_eq_add, abs_neg] at this; linarith
  · have e : archIntegrand (fun t => g₀ (t + c)) = archIntegrand g₀ := funext (archIntegrand_shift g₀ c)
    rw [e]; exact hp.arch

/-- **Translation invariance of Weil's form.** -/
theorem weilQg_shift {b a : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀) {c : ℝ} (h : b + |c| ≤ a) :
    weilQg a (fun t => g₀ (t + c)) = weilQ b g₀ := by
  have hs := (sprobe_shift hp h).supp
  have ha : 0 ≤ a := by linarith [abs_nonneg c]
  rw [← weilQg_even hp]
  unfold weilQg
  have hR : poleR (fun t => g₀ (t + c)) a = Real.exp (c / 2) * poleR g₀ b := by
    rw [poleR_eq_integral ha hs, poleR_eq_integral hb.le hp.supp, ← integral_const_mul]
    have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun v => Real.exp (c / 2) * (g₀ v * Real.exp (-(v / 2)))) c
    rw [← this]; congr 1; funext t
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hL : poleL (fun t => g₀ (t + c)) a = Real.exp (-(c / 2)) * poleL g₀ b := by
    rw [poleL_eq_integral ha hs, poleL_eq_integral hb.le hp.supp, ← integral_const_mul]
    have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun v => Real.exp (-(c / 2)) * (g₀ v * Real.exp (v / 2))) c
    rw [← this]; congr 1; funext t
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hA : archE (fun t => g₀ (t + c)) = archE g₀ := by
    unfold archE; congr 1; funext u; exact archIntegrand_shift g₀ c u
  have hS : primeS (fun t => g₀ (t + c)) = primeS g₀ := by
    unfold primeS; congr 1; funext n; rw [autocorr_shift]
  have hE : Real.exp (c / 2) * Real.exp (-(c / 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [hR, hL, normSq_shift, hA, hS]
  linear_combination (2 * poleR g₀ b * poleL g₀ b) * hE

theorem oprobe_atwin {b a : ℝ} {g₀ : ℝ → ℝ} (hp : Probe b g₀) {l : ℝ} (h : b + |l| ≤ a) :
    OProbe a (atwin g₀ l) := by
  have hx := sprobe_shift hp (a := a) (c := -l) (by rw [abs_neg]; exact h)
  have := (oprobe_oddPart hx).smul 2
  convert this using 1; funext t
  simp only [oddPart, atwin, sub_eq_add_neg]
  rw [show -t + -l = -(t + l) by ring, hp.even]; ring

/-- **The antitwin's energy**: `Q(A_l) = 4Q(Φ_b) − Q(T_l)`. -/
theorem weilQg_atwin {b a : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀) {l : ℝ}
    (h : b + |l| ≤ a) : weilQg a (atwin g₀ l) = 4 * weilQ b g₀ - weilQ a (twin g₀ l) := by
  have hx := sprobe_shift hp (a := a) (c := -l) (by rw [abs_neg]; exact h)
  have hpar := weilQg_parity hx
  rw [weilQg_shift hb hp (a := a) (c := -l) (by rw [abs_neg]; exact h)] at hpar
  have he : evenPart (fun t => g₀ (t + -l)) = fun t => (1 / 2 : ℝ) * twin g₀ l t := by
    funext t; simp only [evenPart, twin, sub_eq_add_neg]
    rw [show -t + -l = -(t + l) by ring, hp.even]; ring
  have ho : oddPart (fun t => g₀ (t + -l)) = fun t => (1 / 2 : ℝ) * atwin g₀ l t := by
    funext t; simp only [oddPart, atwin, sub_eq_add_neg]
    rw [show -t + -l = -(t + l) by ring, hp.even]; ring
  rw [he, ho, weilQ_smul, weilQg_smul] at hpar
  linarith

/-- Two copies with far-apart supports have pointwise zero product. -/
theorem shift_mul_zero {b : ℝ} {g₀ : ℝ → ℝ} (hsupp : ∀ u, b < |u| → g₀ u = 0) {c d : ℝ}
    (hcd : 2 * b < |c - d|) (t : ℝ) : g₀ (t + c) * g₀ (t + d) = 0 := by
  by_contra h
  have h1 : |t + c| ≤ b := by by_contra h1; exact h (by rw [hsupp _ (lt_of_not_ge h1), zero_mul])
  have h2 : |t + d| ≤ b := by by_contra h2; exact h (by rw [hsupp _ (lt_of_not_ge h2), mul_zero])
  have : |c - d| ≤ |t + c| + |t + d| := by
    have := abs_sub (t + c) (t + d); rw [show t + c - (t + d) = c - d by ring] at this; linarith
  linarith

theorem integral_shift_mul_zero {b : ℝ} {g₀ : ℝ → ℝ} (hsupp : ∀ u, b < |u| → g₀ u = 0) {c d : ℝ}
    (hcd : 2 * b < |c - d|) : (∫ t, g₀ (t + c) * g₀ (t + d)) = 0 := by
  simp [shift_mul_zero hsupp hcd]

/-- `‖T_l‖² = ‖A_l‖² = 2‖g₀‖²` when the two copies are disjoint (`l > b`). -/
theorem normSq_twin_atwin {b : ℝ} (hb : 0 ≤ b) {g₀ : ℝ → ℝ} (hp : Probe b g₀) {l : ℝ} (hl : b < l) :
    normSq (twin g₀ l) = 2 * normSq g₀ ∧ normSq (atwin g₀ l) = 2 * normSq g₀ := by
  have m1 := memLp_shift hp.memL2 (-l)
  have m2 := memLp_shift hp.memL2 l
  have hx : xcorr (fun t => g₀ (t + -l)) (fun t => g₀ (t + l)) 0 = 0 := by
    rw [xcorr_zero_eq]; exact integral_shift_mul_zero hp.supp (by
      rw [show -l - l = -(2 * l) by ring, abs_neg, abs_of_pos (by linarith)]; linarith)
  have n1 := normSq_add_smul m1 m2 1
  have n2 := normSq_add_smul m1 m2 (-1)
  rw [hx, normSq_shift, normSq_shift] at n1 n2
  constructor
  · have e : twin g₀ l = fun t => g₀ (t + -l) + 1 * g₀ (t + l) := by
      funext t; simp [twin, sub_eq_add_neg]
    rw [e, n1]; ring
  · have e : atwin g₀ l = fun t => g₀ (t + -l) + -1 * g₀ (t + l) := by
      funext t; simp [atwin, sub_eq_add_neg]
    rw [e, n2]; ring

/-- `‖e^{iw}‖ ≤ e^{|Im w|}`. -/
theorem norm_cexp_I_le (w : ℂ) : ‖Complex.exp (Complex.I * w)‖ ≤ Real.exp |w.im| := by
  rw [Complex.norm_exp]; apply Real.exp_le_exp.2
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  exact neg_le_abs _

theorem norm_cexp_negI_le (w : ℂ) : ‖Complex.exp (-(Complex.I * w))‖ ≤ Real.exp |w.im| := by
  have := norm_cexp_I_le (-w)
  rwa [show Complex.I * -w = -(Complex.I * w) by ring, Complex.neg_im, abs_neg] at this

theorem norm_two_cos_le (w : ℂ) : ‖2 * Complex.cos w‖ ≤ 2 * Real.exp |w.im| := by
  rw [Complex.cos, show 2 * ((Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2)
    = Complex.exp (Complex.I * w) + Complex.exp (-(Complex.I * w)) by ring_nf]
  calc _ ≤ ‖Complex.exp (Complex.I * w)‖ + ‖Complex.exp (-(Complex.I * w))‖ := norm_add_le _ _
    _ ≤ Real.exp |w.im| + Real.exp |w.im| := add_le_add (norm_cexp_I_le w) (norm_cexp_negI_le w)
    _ = _ := by ring

/-- `‖4 − (2cos w)²‖ = ‖2 sin w‖² ≤ 4e^{2|Im w|}`. -/
theorem norm_four_sub_cos_sq_le (w : ℂ) :
    ‖4 - (2 * Complex.cos w) ^ 2‖ ≤ 4 * Real.exp |w.im| ^ 2 := by
  have e : 4 - (2 * Complex.cos w) ^ 2 = -(Complex.exp (Complex.I * w) - Complex.exp (-(Complex.I * w))) ^ 2 := by
    have h1 : Complex.exp (Complex.I * w) * Complex.exp (-(Complex.I * w)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.cos, show w * Complex.I = Complex.I * w by ring, show -w * Complex.I = -(Complex.I * w) by ring]
    linear_combination (-4 : ℂ) * h1
  rw [e, norm_neg, norm_pow]
  have := norm_sub_le (Complex.exp (Complex.I * w)) (Complex.exp (-(Complex.I * w)))
  have h2 : ‖Complex.exp (Complex.I * w) - Complex.exp (-(Complex.I * w))‖ ≤ 2 * Real.exp |w.im| :=
    this.trans (by linarith [norm_cexp_I_le w, norm_cexp_negI_le w])
  calc _ ≤ (2 * Real.exp |w.im|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = _ := by ring

theorem im_ofReal_mul_le {l : ℝ} (hl : 0 ≤ l) {t : ℂ} (ht : |t.im| ≤ 1 / 2) :
    |((l : ℂ) * t).im| ≤ l / 2 := by
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
    abs_of_nonneg hl]
  nlinarith

/-- Disjoint twins have pointwise zero product. -/
theorem twin_mul_twin_zero {b : ℝ} {g₀ : ℝ → ℝ} (hsupp : ∀ u, b < |u| → g₀ u = 0) {l m : ℝ}
    (hl : 0 ≤ l) (hlm : l + 2 * b < m) (t : ℝ) : twin g₀ l t * twin g₀ m t = 0 := by
  have h1 := shift_mul_zero hsupp (c := -l) (d := -m) (lt_abs.2 (Or.inl (by linarith))) t
  have h2 := shift_mul_zero hsupp (c := -l) (d := m) (lt_abs.2 (Or.inr (by linarith))) t
  have h3 := shift_mul_zero hsupp (c := l) (d := -m) (lt_abs.2 (Or.inl (by linarith))) t
  have h4 := shift_mul_zero hsupp (c := l) (d := m) (lt_abs.2 (Or.inr (by linarith))) t
  simp only [twin, sub_eq_add_neg]
  rw [add_mul, mul_add, mul_add, h1, h2, h3, h4]; ring

theorem normSq_PhiA_mono' {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    normSq (PhiA r) ≤ normSq (PhiA s) := by
  unfold normSq
  refine integral_mono (probe_PhiA hr).memL2.integrable_sq
    (probe_PhiA (hr.trans hrs)).memL2.integrable_sq fun t => ?_
  by_cases h : t ∈ Icc (-r) r
  · have h' : t ∈ Icc (-s) s := ⟨by linarith [h.1], by linarith [h.2]⟩
    simp only [PhiA, indicator_of_mem h, indicator_of_mem h', le_refl]
  · simp only [PhiA, indicator_of_notMem h]
    rw [zero_pow two_ne_zero]; exact sq_nonneg _

theorem normSq_PhiA_pos {r : ℝ} (hr : 0 < r) : 0 < normSq (PhiA r) := by
  unfold normSq
  refine (integral_pos_iff_support_of_nonneg (fun t => sq_nonneg (PhiA r t))
    (probe_PhiA hr.le).memL2.integrable_sq).2 ?_
  have hsub : Ioo (-r) r ⊆ Function.support fun t => PhiA r t ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc (-r) r := Ioo_subset_Icc_self ht
    simp only [Function.mem_support, PhiA, indicator_of_mem ht']
    exact pow_ne_zero 2 (RPhi_pos t).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]; simp only [sub_neg_eq_add, ENNReal.ofReal_pos]; linarith

/-! ## B. The per-zero bound on `Φ̂_b` (round 133, at a general window) -/

theorem ghat_PhiA_sq_le {D C0 C1 : ℝ} (hD : 3 / 2 ≤ D) (hC00 : 0 ≤ C0)
    (hC0 : ∀ u, |RPhi u| ≤ C0 * Real.exp (-D * |u|))
    (hC1 : ∀ u, |RPhi1 u| ≤ C1 * Real.exp (-D * |u|))
    {t : ℂ} (ht : |t.im| ≤ 1 / 2) (hz : Xi t = 0) {b : ℝ} (hb : 0 < b) :
    ‖ghatC (PhiA b) b t‖ ^ 2 ≤ ((2 * C0 + C1 * ∫ u, Real.exp (-1 * |u|)) ^ 2
        + 4 * (C0 * ∫ u, Real.exp (-1 * |u|)) ^ 2) * Real.exp (-(D - 3 / 2) * b) ^ 2
        * ‖1 / (t ^ 2 + 4)‖ := by
  set I1 := ∫ u, Real.exp (-1 * |u|)
  set E := Real.exp (-(D - 3 / 2) * b)
  obtain ⟨b0, b1⟩ := zero_bounds ht hz hb.le
  have h0 : ‖tailT RPhi b t‖ ≤ C0 * I1 * E := by
    have := norm_tailT_le hC0 hD ht b; linarith [show C0 * E * I1 = C0 * I1 * E by ring]
  have h1 : 2 * |RPhi b| * Real.exp (b / 2) + ‖tailT RPhi1 b t‖ ≤ (2 * C0 + C1 * I1) * E := by
    have t1 := norm_tailT_le hC1 hD ht b
    have t0 := hC0 b
    rw [abs_of_pos hb] at t0
    have hb' : |RPhi b| * Real.exp (b / 2) ≤ C0 * E := by
      calc |RPhi b| * Real.exp (b / 2) ≤ C0 * Real.exp (-D * b) * Real.exp (b / 2) :=
            mul_le_mul_of_nonneg_right t0 (Real.exp_pos _).le
        _ = C0 * Real.exp (-D * b + b / 2) := by rw [mul_assoc, ← Real.exp_add]
        _ ≤ C0 * E := by
            apply mul_le_mul_of_nonneg_left _ hC00
            exact Real.exp_le_exp.2 (by nlinarith)
    nlinarith
  rw [ghatC_PhiA hb.le]
  calc _ ≤ _ := term_le ht (norm_nonneg _) (b0.trans h0) (b1.trans h1)
    _ = _ := by ring

/-! ## C. Rung 1: the antitwin -/

/-- **`Q(A_l) = Σ_ρ (4 − 4cos²(l t_ρ)) Φ̂_b(t_ρ)² ≤ 4e^{l} M S`** whenever `‖Φ̂_b(t_ρ)‖² ≤ M w_ρ`. -/
theorem weilQg_atwin_le {ι : Type*} {ρ : ι → ℂ} (hs : ∀ i, |((ρ i - 1 / 2) / Complex.I).im| ≤ 1 / 2)
    (hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖)
    {b l a : ℝ} (hb : 0 < b) (hl : 0 ≤ l) (h : b + l ≤ a)
    (hE0 : WeilExplicit ρ (fun z => ghatC (PhiA b) b z ^ 2) (hsq (PhiA b) b))
    (hEt : WeilExplicit ρ (fun z => ghatC (twin (PhiA b) l) (l + b) z ^ 2)
      (hsq (twin (PhiA b) l) (l + b)))
    {M : ℝ} (hM : ∀ i, ‖ghatC (PhiA b) b ((ρ i - 1 / 2) / Complex.I)‖ ^ 2
      ≤ M * ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖) :
    weilQg a (atwin (PhiA b) l)
      ≤ 4 * Real.exp l * M * ∑' i, ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖ := by
  have hp := probe_PhiA hb.le
  have hpt := twin_probe hp hl
  have H0 := weilQ_eq_zero_sum hp hb hE0
  have Ht := weilQ_eq_zero_sum hpt (by linarith) hEt
  have hlb : b + |l| ≤ a := by rwa [abs_of_nonneg hl]
  rw [weilQg_atwin hb hp hlb, weilQ_mono (by linarith) (by linarith) hpt]
  have H := (H0.mul_left 4).sub Ht
  rw [show (4 : ℂ) * (weilQ b (PhiA b) : ℂ) - (weilQ (l + b) (twin (PhiA b) l) : ℂ)
    = ((4 * weilQ b (PhiA b) - weilQ (l + b) (twin (PhiA b) l) : ℝ) : ℂ) by push_cast; ring] at H
  have Hre := Complex.reCLM.hasSum H
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at Hre
  refine hasSum_le (fun i => ?_) Hre (hS.hasSum.mul_left _)
  set t := (ρ i - 1 / 2) / Complex.I
  rw [ghatC_twin hb hp hl]
  have e : (4 : ℂ) * ghatC (PhiA b) b t ^ 2 - (2 * Complex.cos (↑l * t) * ghatC (PhiA b) b t) ^ 2
      = (4 - (2 * Complex.cos (↑l * t)) ^ 2) * ghatC (PhiA b) b t ^ 2 := by ring
  rw [e]
  have hexp : Real.exp |((l : ℂ) * t).im| ^ 2 ≤ Real.exp l := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by have := im_ofReal_mul_le hl (hs i); push_cast; linarith)
  have hM0 : 0 ≤ M * ‖1 / (t ^ 2 + 4)‖ := (sq_nonneg _).trans (hM i)
  calc _ ≤ ‖(4 - (2 * Complex.cos (↑l * t)) ^ 2) * ghatC (PhiA b) b t ^ 2‖ := Complex.re_le_norm _
    _ = ‖4 - (2 * Complex.cos (↑l * t)) ^ 2‖ * ‖ghatC (PhiA b) b t‖ ^ 2 := by
        rw [norm_mul, norm_pow]
    _ ≤ (4 * Real.exp |((l : ℂ) * t).im| ^ 2) * (M * ‖1 / (t ^ 2 + 4)‖) :=
        mul_le_mul (norm_four_sub_cos_sq_le _) (hM i) (sq_nonneg _) (by positivity)
    _ ≤ (4 * Real.exp l) * (M * ‖1 / (t ^ 2 + 4)‖) :=
        mul_le_mul_of_nonneg_right (by linarith) hM0
    _ = _ := by ring

/-- **Rung 1 decays faster than every exponential** (no RH input): over any family on which `Ξ`
vanishes, in the strip, with `Σ‖1/(t² + 4)‖ < ∞`, and given the explicit formula for `Φ_b` and for
its twins, `λ_odd(a) ≤ K e^{−Ba}` for `a ≥ 1`. -/
theorem lamO_decay {ι : Type*} {ρ : ι → ℂ} (hz : ∀ i, Xi ((ρ i - 1 / 2) / Complex.I) = 0)
    (hs : ∀ i, |((ρ i - 1 / 2) / Complex.I).im| ≤ 1 / 2)
    (hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖)
    (hE0 : ∀ b, 0 < b → WeilExplicit ρ (fun z => ghatC (PhiA b) b z ^ 2) (hsq (PhiA b) b))
    (hEt : ∀ b l, 0 < b → 0 ≤ l → WeilExplicit ρ (fun z => ghatC (twin (PhiA b) l) (l + b) z ^ 2)
      (hsq (twin (PhiA b) l) (l + b)))
    (B : ℝ) : ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lamO a ≤ K * Real.exp (-B * a) := by
  set D := 4 * |B| + 5
  obtain ⟨C0, hC00, hC0⟩ := RPhi_decay_gen D
  obtain ⟨C1, hC10, hC1⟩ := RPhi1_decay D
  set I1 := ∫ u, Real.exp (-1 * |u|)
  have hI1 : 0 ≤ I1 := integral_nonneg fun u => (Real.exp_pos _).le
  set S := ∑' i, ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  set N1 := normSq (PhiA (1 / 8))
  have hN1 : 0 < N1 := normSq_PhiA_pos (by norm_num)
  set K' := (2 * C0 + C1 * I1) ^ 2 + 4 * (C0 * I1) ^ 2
  have hK' : 0 ≤ K' := by positivity
  refine ⟨2 * K' * S / N1, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  have hD32 : 3 / 2 ≤ D := by have := abs_nonneg B; simp only [D]; linarith
  set b := a / 8
  have hb : 0 < b := by positivity
  set E := Real.exp (-(D - 3 / 2) * b)
  have hM := fun i => ghat_PhiA_sq_le hD32 hC00 hC0 hC1 (hs i) (hz i) hb
  have hQ := weilQg_atwin_le hs hS hb (l := a / 4) (a := a) (by positivity)
    (by simp only [b]; linarith) (hE0 b hb) (hEt b (a / 4) hb (by positivity)) hM
  set N := normSq (PhiA b)
  have hN : N1 ≤ N := normSq_PhiA_mono' (by norm_num) (by simp only [b]; linarith)
  have hNpos : 0 < N := hN1.trans_le hN
  have hnA := (normSq_twin_atwin hb.le (probe_PhiA hb.le) (show b < a / 4 by simp only [b]; linarith)).2
  set c := 1 / Real.sqrt (2 * N)
  have hc2 : c ^ 2 = 1 / (2 * N) := by rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hop := (oprobe_atwin (probe_PhiA hb.le) (a := a) (l := a / 4)
    (by rw [abs_of_pos (by positivity)]; simp only [b]; linarith)).smul c
  have hn : normSq (fun t => c * atwin (PhiA b) (a / 4) t) = 1 := by
    rw [normSq_smul, hnA, hc2]; change 1 / (2 * N) * (2 * N) = 1; field_simp
  have hl := lamO_le ha0 hop hn
  rw [weilQg_smul, hc2] at hl
  have hexp : Real.exp (a / 4) * E ^ 2 ≤ Real.exp (-B * a) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_le_exp.2
    have := le_abs_self B; simp only [D, b]; push_cast; nlinarith
  have hX : weilQg a (atwin (PhiA b) (a / 4)) ≤ 4 * K' * S * Real.exp (-B * a) := by
    calc _ ≤ 4 * Real.exp (a / 4) * (K' * E ^ 2) * S := hQ
      _ = 4 * K' * S * (Real.exp (a / 4) * E ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  calc lamO a ≤ 1 / (2 * N) * weilQg a (atwin (PhiA b) (a / 4)) := hl
    _ ≤ 1 / (2 * N) * (4 * K' * S * Real.exp (-B * a)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ 1 / (2 * N1) * (4 * K' * S * Real.exp (-B * a)) :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) (by linarith))
          (by positivity)
    _ = 2 * K' * S / N1 * Real.exp (-B * a) := by field_simp; ring

/-! ## D. Rung 2: two disjoint twins -/

/-- **`Q(pT_l + qT_m) ≤ 4(|p| + |q|)² e^{m} M S`** whenever `‖Φ̂_b(t_ρ)‖² ≤ M w_ρ`. -/
theorem weilQ_pair_le {ι : Type*} {ρ : ι → ℂ} (hs : ∀ i, |((ρ i - 1 / 2) / Complex.I).im| ≤ 1 / 2)
    (hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖)
    {b l m a : ℝ} (hb : 0 < b) (hl : 0 ≤ l) (hlm : l ≤ m) (hma : m + b ≤ a) (p q : ℝ)
    (hEv : WeilExplicit ρ
      (fun z => ghatC (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) a z ^ 2)
      (hsq (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) a))
    {M : ℝ} (hM : ∀ i, ‖ghatC (PhiA b) b ((ρ i - 1 / 2) / Complex.I)‖ ^ 2
      ≤ M * ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖) :
    weilQ a (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t)
      ≤ 4 * (|p| + |q|) ^ 2 * Real.exp m * M * ∑' i, ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖ := by
  have hp := probe_PhiA hb.le
  have hm : 0 ≤ m := hl.trans hlm
  have hpl := twin_probe hp hl
  have hpm := twin_probe hp hm
  have hpv : Probe a (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) :=
    (probe_add_sub (probe_smul (hpl.mono (by linarith)) p) (probe_smul (hpm.mono hma) q)).1
  have H := weilQ_eq_zero_sum hpv (by linarith) hEv
  have Hre := Complex.reCLM.hasSum H
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at Hre
  refine hasSum_le (fun i => ?_) Hre (hS.hasSum.mul_left _)
  set t := (ρ i - 1 / 2) / Complex.I
  set G := ghatC (PhiA b) b t
  have e : ghatC (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) a t
      = (p * (2 * Complex.cos (↑l * t)) + q * (2 * Complex.cos (↑m * t))) * G := by
    rw [show (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t)
      = (fun t => p * twin (PhiA b) l t) + (fun t => q * twin (PhiA b) m t) from rfl,
      ghatC_add (hpl.memL2.const_mul p) (hpm.memL2.const_mul q), ghatC_smul, ghatC_smul,
      ghatC_window (by linarith) (by linarith) hpl.supp,
      ghatC_window (by linarith) (by linarith) hpm.supp, ghatC_twin hb hp hl, ghatC_twin hb hp hm]
    ring
  have i1 : Real.exp |((l : ℂ) * t).im| ≤ Real.exp (m / 2) :=
    Real.exp_le_exp.2 (by have := im_ofReal_mul_le hl (hs i); linarith)
  have i2 : Real.exp |((m : ℂ) * t).im| ≤ Real.exp (m / 2) :=
    Real.exp_le_exp.2 (im_ofReal_mul_le hm (hs i))
  have hc : ‖(p : ℂ) * (2 * Complex.cos (↑l * t)) + q * (2 * Complex.cos (↑m * t))‖
      ≤ (|p| + |q|) * (2 * Real.exp (m / 2)) := by
    have c1 := norm_two_cos_le ((l : ℂ) * t)
    have c2 := norm_two_cos_le ((m : ℂ) * t)
    calc _ ≤ ‖(p : ℂ)‖ * ‖2 * Complex.cos (↑l * t)‖ + ‖(q : ℂ)‖ * ‖2 * Complex.cos (↑m * t)‖ := by
          exact (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)
      _ ≤ |p| * (2 * Real.exp (m / 2)) + |q| * (2 * Real.exp (m / 2)) := by
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr <;> linarith
      _ = _ := by ring
  have ee : Real.exp (m / 2) ^ 2 = Real.exp m := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  calc _ ≤ ‖(((p : ℂ) * (2 * Complex.cos (↑l * t)) + q * (2 * Complex.cos (↑m * t))) * G) ^ 2‖ :=
        Complex.re_le_norm _
    _ = ‖(p : ℂ) * (2 * Complex.cos (↑l * t)) + q * (2 * Complex.cos (↑m * t))‖ ^ 2 * ‖G‖ ^ 2 := by
        rw [mul_pow, norm_mul, norm_pow, norm_pow]
    _ ≤ ((|p| + |q|) * (2 * Real.exp (m / 2))) ^ 2 * (M * ‖1 / (t ^ 2 + 4)‖) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hc 2) (hM i) (sq_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow, mul_pow, ee]; ring

/-- **Rung 2 decays faster than every exponential** (no RH input): on the span of the orthonormal
twins `T_{a/4}`, `T_{3a/4}` (built from `Φ_{a/8}`), `Q ≤ K e^{−Ba}`; so every `s` with `λ₂(a) ≥ s`
in min–max form (`Lam2Ge a s`) satisfies `s ≤ K e^{−Ba}` for `a ≥ 1`. -/
theorem lam2_decay {ι : Type*} {ρ : ι → ℂ} (hz : ∀ i, Xi ((ρ i - 1 / 2) / Complex.I) = 0)
    (hs : ∀ i, |((ρ i - 1 / 2) / Complex.I).im| ≤ 1 / 2)
    (hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖)
    (hEv : ∀ a, 1 ≤ a → ∀ p q : ℝ, WeilExplicit ρ
      (fun z => ghatC (fun t => p * twin (PhiA (a / 8)) (a / 4) t
        + q * twin (PhiA (a / 8)) (3 * a / 4) t) a z ^ 2)
      (hsq (fun t => p * twin (PhiA (a / 8)) (a / 4) t + q * twin (PhiA (a / 8)) (3 * a / 4) t) a))
    (B : ℝ) : ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → ∀ s, Lam2Ge a s → s ≤ K * Real.exp (-B * a) := by
  set D := 4 * |B| + 5
  obtain ⟨C0, hC00, hC0⟩ := RPhi_decay_gen D
  obtain ⟨C1, hC10, hC1⟩ := RPhi1_decay D
  set I1 := ∫ u, Real.exp (-1 * |u|)
  have hI1 : 0 ≤ I1 := integral_nonneg fun u => (Real.exp_pos _).le
  set S := ∑' i, ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  set N1 := normSq (PhiA (1 / 8))
  have hN1 : 0 < N1 := normSq_PhiA_pos (by norm_num)
  set K' := (2 * C0 + C1 * I1) ^ 2 + 4 * (C0 * I1) ^ 2
  have hK' : 0 ≤ K' := by positivity
  refine ⟨4 * K' * S / N1, by positivity, fun a ha s Hs => ?_⟩
  have ha0 : 0 < a := by linarith
  have hD32 : 3 / 2 ≤ D := by have := abs_nonneg B; simp only [D]; linarith
  have hb : 0 < a / 8 := by positivity
  set E := Real.exp (-(D - 3 / 2) * (a / 8))
  have hM := fun i => ghat_PhiA_sq_le hD32 hC00 hC0 hC1 (hs i) (hz i) hb
  have hp := probe_PhiA hb.le
  set N := normSq (PhiA (a / 8))
  have hN : N1 ≤ N := normSq_PhiA_mono' (by norm_num) (by linarith)
  have hNpos : 0 < N := hN1.trans_le hN
  have n1 := (normSq_twin_atwin hb.le hp (show a / 8 < a / 4 by linarith)).1
  have n2 := (normSq_twin_atwin hb.le hp (show a / 8 < 3 * a / 4 by linarith)).1
  set c := 1 / Real.sqrt (2 * N)
  have hc2 : c ^ 2 = 1 / (2 * N) := by rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have pg := probe_smul ((twin_probe hp (by positivity : (0 : ℝ) ≤ a / 4)).mono
    (by linarith : a / 4 + a / 8 ≤ a)) c
  have ph := probe_smul ((twin_probe hp (by positivity : (0 : ℝ) ≤ 3 * a / 4)).mono
    (by linarith : 3 * a / 4 + a / 8 ≤ a)) c
  have ng : normSq (fun t => c * twin (PhiA (a / 8)) (a / 4) t) = 1 := by
    rw [normSq_smul, n1, hc2]; change 1 / (2 * N) * (2 * N) = 1; field_simp
  have nh : normSq (fun t => c * twin (PhiA (a / 8)) (3 * a / 4) t) = 1 := by
    rw [normSq_smul, n2, hc2]; change 1 / (2 * N) * (2 * N) = 1; field_simp
  have hx : xcorr (fun t => c * twin (PhiA (a / 8)) (a / 4) t)
      (fun t => c * twin (PhiA (a / 8)) (3 * a / 4) t) 0 = 0 := by
    rw [xcorr_zero_eq]
    have e : (fun t => c * twin (PhiA (a / 8)) (a / 4) t * (c * twin (PhiA (a / 8)) (3 * a / 4) t))
        = fun _ => (0 : ℝ) := funext fun t => by
      rw [mul_mul_mul_comm, twin_mul_twin_zero hp.supp (by positivity) (by linarith) t, mul_zero]
    rw [e, integral_zero]
  obtain ⟨α, β, hαβ, hsv⟩ := Hs _ _ pg ph ng nh hx
  have ev : (fun t => α * (c * twin (PhiA (a / 8)) (a / 4) t)
      + β * (c * twin (PhiA (a / 8)) (3 * a / 4) t))
      = fun t => (α * c) * twin (PhiA (a / 8)) (a / 4) t
        + (β * c) * twin (PhiA (a / 8)) (3 * a / 4) t := by funext t; ring
  rw [ev] at hsv
  have hQ := weilQ_pair_le hs hS hb (by positivity) (by linarith) (by linarith)
    (α * c) (β * c) (hEv a ha _ _) hM
  have hP : (|α * c| + |β * c|) ^ 2 ≤ 1 / N := by
    have h2 : (α * c) ^ 2 + (β * c) ^ 2 = 1 / (2 * N) := by
      rw [mul_pow, mul_pow, hc2, ← add_mul, hαβ, one_mul]
    have : (|α * c| + |β * c|) ^ 2 ≤ 2 * ((α * c) ^ 2 + (β * c) ^ 2) := by
      nlinarith [sq_abs (α * c), sq_abs (β * c), sq_nonneg (|α * c| - |β * c|)]
    rw [h2] at this
    calc _ ≤ 2 * (1 / (2 * N)) := this
      _ = 1 / N := by field_simp
  have hexp : Real.exp (3 * a / 4) * E ^ 2 ≤ Real.exp (-B * a) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_le_exp.2
    have := le_abs_self B; simp only [D]; push_cast; nlinarith
  set P := (|α * c| + |β * c|) ^ 2
  have hP0 : 0 ≤ P := by positivity
  calc s ≤ _ := hsv
    _ ≤ 4 * P * Real.exp (3 * a / 4) * (K' * E ^ 2) * S := hQ
    _ = (4 * K' * S) * P * (Real.exp (3 * a / 4) * E ^ 2) := by ring
    _ ≤ (4 * K' * S) * (1 / N) * Real.exp (-B * a) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP (by positivity)) hexp (by positivity)
          (by positivity)
    _ ≤ (4 * K' * S) * (1 / N1) * Real.exp (-B * a) := by
        gcongr
    _ = 4 * K' * S / N1 * Real.exp (-B * a) := by ring

end Pilot1ca

#print axioms Pilot1ca.weilQg_atwin
#print axioms Pilot1ca.lamO_decay
#print axioms Pilot1ca.lam2_decay
