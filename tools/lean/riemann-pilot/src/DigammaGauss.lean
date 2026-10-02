import Mathlib

/-! # Gauss's digamma integral, proved (round 154): discharging `DigammaDiff`

`ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt` for `Re z, Re w > 0`.

Mathlib has `ψ = Γ'/Γ`, the recurrence `ψ(s + n) = ψ(s) + Σ_{k<n} 1/(s + k)`, and the convexity of
`log Γ` on `(0, ∞)` (Bohr–Mollerup). From these:

* **A. The series** `ψ(z) − ψ(1) = Σ_k (1/(k + 1) − 1/(k + z))` for `Re z > 0`.
  On `(0, ∞)`: the real digamma is increasing (convexity), so `ψ(x + n) − ψ(y + n) → 0`, and the
  recurrence telescopes. To `Re z > 0`: both sides are holomorphic, and they agree on `(0, ∞)`, so
  the identity theorem applies.
* **B. The integral.** `1/(k + w) − 1/(k + z) = ∫_0^∞ e^{−kt}(e^{−wt} − e^{−zt}) dt`. The mean-value
  bound `|e^{−wt} − e^{−zt}| ≤ |z − w| t e^{−σt}` gives `Σ_k ∫|·| ≤ Σ_k |z − w|/(k + σ)² < ∞`, so sum
  and integral commute. The geometric series `Σ_k e^{−kt} = 1/(1 − e^{−t})` finishes.
-/

open Filter Topology MeasureTheory Set

noncomputable section

namespace PilotDigamma

theorem ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at this
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-! ## A1. The real digamma function is increasing -/

/-- The real digamma function `(log Γ)'`. -/
def rpsi (x : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) x

theorem real_ne_neg_nat {x : ℝ} (hx : 0 < x) : ∀ m : ℕ, x ≠ -(m : ℝ) := fun m h => by
  linarith [Nat.cast_nonneg (α := ℝ) m]

theorem digamma_ofReal {x : ℝ} (hx : 0 < x) : Complex.digamma x = (rpsi x : ℂ) := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := ne_neg_nat_of_re_pos (by simpa using hx)
  have hC := (Complex.differentiableAt_Gamma _ hne).hasDerivAt
  have hR := (Real.differentiableAt_Gamma (real_ne_neg_nat hx)).hasDerivAt
  have h1 := hC.comp_ofReal
  have h2 := hR.ofReal_comp
  have e : (fun y : ℝ => Complex.Gamma (y : ℂ)) = fun y => ((Real.Gamma y : ℝ) : ℂ) :=
    funext fun y => Complex.Gamma_ofReal y
  rw [e] at h1
  have hd : deriv Complex.Gamma x = ((deriv Real.Gamma x : ℝ) : ℂ) := h1.unique h2
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hl : rpsi x = deriv Real.Gamma x / Real.Gamma x := (hR.log hG.ne').deriv
  rw [Complex.digamma_def, logDeriv_apply, hd, Complex.Gamma_ofReal, hl]
  push_cast; rfl

theorem rpsi_mono : MonotoneOn rpsi (Ioi 0) :=
  Real.convexOn_log_Gamma.monotoneOn_deriv fun _ hx =>
    (Real.differentiableAt_Gamma (real_ne_neg_nat hx)).log (Real.Gamma_pos_of_pos hx).ne'

theorem rpsi_add_nat {x : ℝ} (hx : 0 < x) (K : ℕ) :
    rpsi (x + K) = rpsi x + ∑ j ∈ Finset.range K, 1 / (x + j) := by
  have h := Complex.digamma_apply_add_nat (ne_neg_nat_of_re_pos (z := (x : ℂ)) (by simpa using hx)) K
  rw [show (x : ℂ) + K = ((x + K : ℝ) : ℂ) by push_cast; ring, digamma_ofReal (by positivity),
    digamma_ofReal hx] at h
  have : ((rpsi (x + K) : ℝ) : ℂ) = ((rpsi x + ∑ j ∈ Finset.range K, 1 / (x + j) : ℝ) : ℂ) := by
    rw [h]; push_cast; simp only [one_div]
  exact_mod_cast this

theorem sum_inv_le {x : ℝ} (hx : 0 < x) (K : ℕ) : ∑ j ∈ Finset.range K, 1 / (x + j) ≤ K / x := by
  calc ∑ j ∈ Finset.range K, 1 / (x + j) ≤ ∑ _j ∈ Finset.range K, 1 / x :=
        Finset.sum_le_sum fun j _ => one_div_le_one_div_of_le hx (by linarith [Nat.cast_nonneg (α := ℝ) j])
    _ = K / x := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]

theorem tendsto_rpsi_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun n : ℕ => rpsi (x + n) - rpsi (y + n)) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (max x y)
  have key : ∀ z : ℝ, 0 < z → z ≤ K → ∀ n : ℕ, 1 ≤ n →
      rpsi n ≤ rpsi (z + n) ∧ rpsi (z + n) ≤ rpsi n + K / n := by
    intro z hz hzK n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨rpsi_mono (show (0 : ℝ) < n from hn0) (show (0 : ℝ) < z + n by linarith) (by linarith), ?_⟩
    have h1 := rpsi_mono (show (0 : ℝ) < z + n by linarith) (show (0 : ℝ) < n + K by positivity)
      (by linarith : z + n ≤ n + K)
    rw [rpsi_add_nat hn0 K] at h1
    linarith [sum_inv_le hn0 K]
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨a1, a2⟩ := key x hx (le_trans (le_max_left _ _) hK) n hn
  obtain ⟨b1, b2⟩ := key y hy (le_trans (le_max_right _ _) hK) n hn
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

/-! ## A2. The series on `(0, ∞)` -/

/-- The series term `1/(k + 1) − 1/(k + z)`. -/
def dterm (z : ℂ) (k : ℕ) : ℂ := 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)

theorem dterm_bound {z : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : δ ≤ z.re) (hR : ‖z‖ ≤ R)
    (k : ℕ) : ‖dterm z k‖ ≤ (R + 1) / δ * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : δ * ((k : ℝ) + 1) ≤ ‖(k : ℂ) + z‖ := by
    calc δ * ((k : ℝ) + 1) ≤ k + z.re := by nlinarith
      _ = ((k : ℂ) + z).re := by simp
      _ ≤ ‖(k : ℂ) + z‖ := Complex.re_le_norm _
  have hpos : 0 < δ * ((k : ℝ) + 1) := by positivity
  have hkz : (k : ℂ) + z ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have e : dterm z k = (z - 1) / (((k : ℂ) + 1) * ((k : ℂ) + z)) := by
    unfold dterm; field_simp; ring
  have n1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring
  have hz1 : ‖z - 1‖ ≤ R + 1 := (norm_sub_le _ _).trans (by simp; linarith)
  have hR0 : 0 ≤ R + 1 := by linarith [norm_nonneg z]
  rw [e, norm_div, norm_mul, n1, div_mul_div_comm, mul_one,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have : δ * ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + z‖ := by nlinarith
  calc ‖z - 1‖ * (δ * ((k : ℝ) + 1) ^ 2) ≤ (R + 1) * (δ * ((k : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hz1 (by positivity)
    _ ≤ (R + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + z‖) := mul_le_mul_of_nonneg_left this hR0

theorem summable_inv_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using this

theorem summable_dterm {z : ℂ} (hz : 0 < z.re) : Summable (dterm z) :=
  Summable.of_norm_bounded (summable_inv_sq.mul_left ((‖z‖ + 1) / min z.re 1))
    (dterm_bound (lt_min hz one_pos) (min_le_right _ _) (min_le_left _ _) le_rfl)

theorem sum_dterm {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (n : ℕ) :
    ∑ k ∈ Finset.range n, dterm z k
      = Complex.digamma z - Complex.digamma 1 - (Complex.digamma (z + n) - Complex.digamma (1 + n)) := by
  rw [Complex.digamma_apply_add_nat hz, Complex.digamma_apply_add_nat
    (ne_neg_nat_of_re_pos (by simp)) n]
  simp only [dterm, Finset.sum_sub_distrib]
  have a : ∑ k ∈ Finset.range n, 1 / ((k : ℂ) + 1) = ∑ k ∈ Finset.range n, (1 + (k : ℂ))⁻¹ :=
    Finset.sum_congr rfl fun k _ => by rw [one_div, add_comm]
  have b : ∑ k ∈ Finset.range n, 1 / ((k : ℂ) + z) = ∑ k ∈ Finset.range n, (z + (k : ℂ))⁻¹ :=
    Finset.sum_congr rfl fun k _ => by rw [one_div, add_comm]
  rw [a, b]; ring

theorem hasSum_dterm_ofReal {x : ℝ} (hx : 0 < x) :
    HasSum (dterm x) (Complex.digamma x - Complex.digamma 1) := by
  have hs := summable_dterm (z := (x : ℂ)) (by simpa using hx)
  have ht : Tendsto (fun n => ∑ k ∈ Finset.range n, dterm x k) atTop
      (𝓝 (Complex.digamma x - Complex.digamma 1)) := by
    have e : ∀ n : ℕ, ∑ k ∈ Finset.range n, dterm (x : ℂ) k
        = Complex.digamma x - Complex.digamma 1 - ((rpsi (x + n) - rpsi (1 + n) : ℝ) : ℂ) := by
      intro n
      rw [sum_dterm (ne_neg_nat_of_re_pos (by simpa using hx)) n,
        show (x : ℂ) + n = ((x + n : ℝ) : ℂ) by push_cast; ring,
        show (1 : ℂ) + n = ((1 + n : ℝ) : ℂ) by push_cast; ring,
        digamma_ofReal (x := x + n) (by positivity), digamma_ofReal (x := 1 + n) (by positivity)]
      push_cast; ring
    simp_rw [e]
    have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_rpsi_sub hx one_pos)
    rw [show 𝓝 (Complex.digamma x - Complex.digamma 1)
      = 𝓝 (Complex.digamma x - Complex.digamma 1 - ((0 : ℝ) : ℂ)) by simp]
    exact tendsto_const_nhds.sub this
  rw [← tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht]
  exact hs.hasSum

/-! ## A3. The series on `Re z > 0`, by the identity theorem -/

/-- The right half-plane. -/
def U : Set ℂ := {z | 0 < z.re}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_re

theorem differentiableOn_digamma : DifferentiableOn ℂ Complex.digamma U := by
  have hG : DifferentiableOn ℂ Complex.Gamma U := fun z hz =>
    (Complex.differentiableAt_Gamma z (ne_neg_nat_of_re_pos hz)).differentiableWithinAt
  have hG' : DifferentiableOn ℂ (deriv Complex.Gamma) U :=
    (hG.analyticOnNhd isOpen_U).deriv.differentiableOn
  intro z hz
  have h := (hG'.differentiableAt (isOpen_U.mem_nhds hz)).div
    (hG.differentiableAt (isOpen_U.mem_nhds hz)) (Complex.Gamma_ne_zero (ne_neg_nat_of_re_pos hz))
  have e : Complex.digamma = fun y => deriv Complex.Gamma y / Complex.Gamma y :=
    funext fun y => by rw [Complex.digamma_def, logDeriv_apply]
  rw [e]; exact h.differentiableWithinAt

theorem differentiableOn_S : DifferentiableOn ℂ (fun z => ∑' k, dterm z k) U := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.re := hz₀
  set δ := min (z₀.re / 2) 1
  have hδ : 0 < δ := lt_min (half_pos hz₀') one_pos
  set V := {z : ℂ | δ < z.re} ∩ Metric.ball z₀ 1
  have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hz₀V : z₀ ∈ V :=
    ⟨show δ < z₀.re by have := min_le_left (z₀.re / 2) 1; linarith, Metric.mem_ball_self one_pos⟩
  have hd : DifferentiableOn ℂ (fun z => ∑' k, dterm z k) V := by
    refine Complex.differentiableOn_tsum_of_summable_norm (F := fun k z => dterm z k)
      (summable_inv_sq.mul_left ((‖z₀‖ + 1 + 1) / δ)) (fun k z hz => ?_) hV (fun k z hz => ?_)
    · have hre : δ < z.re := hz.1
      have hkz : (k : ℂ) + z ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) k]
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun z => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) z
      exact (differentiableAt_const _).sub
        ((differentiableAt_const _).div ((differentiableAt_const _).add differentiableAt_id) hkz)
    · have hb : dist z z₀ < 1 := hz.2
      rw [dist_eq_norm] at hb
      have := norm_sub_norm_le z z₀
      exact dterm_bound hδ (min_le_right _ _) hz.1.le (by linarith) k
  exact (hd.differentiableAt (hV.mem_nhds hz₀V)).differentiableWithinAt

/-- **The digamma series**: `ψ(z) − ψ(1) = Σ_k (1/(k + 1) − 1/(k + z))` for `Re z > 0`. -/
theorem digamma_sub_one_eq {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z - Complex.digamma 1 = ∑' k, dterm z k := by
  set F : ℂ → ℂ := fun z => Complex.digamma z - Complex.digamma 1 - ∑' k, dterm z k
  have hF : AnalyticOnNhd ℂ F U :=
    ((differentiableOn_digamma.sub_const _).sub differentiableOn_S).analyticOnNhd isOpen_U
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), F w = 0 := by
    have hu : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at this
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp this
        rwa [Complex.ofReal_one] at h2
      · show _ ≠ (1 : ℂ)
        intro h
        have h' : (1 : ℝ) + 1 / ((n : ℝ) + 1) = 1 := by exact_mod_cast h
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine hu.frequently (Frequently.of_forall fun n => ?_)
    have hx : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    simp only [F]
    rw [(hasSum_dterm_ofReal hx).tsum_eq]; ring
  have := hF.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (show (1 : ℂ) ∈ U by simp [U]) hfreq hz
  simp only [F, Pi.zero_apply] at this
  linear_combination this

/-- `ψ(z) − ψ(w) = Σ_k (1/(k + w) − 1/(k + z))` for `Re z, Re w > 0`. -/
theorem hasSum_digamma_sub {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + w) - 1 / ((k : ℂ) + z))
      (Complex.digamma z - Complex.digamma w) := by
  have h := (summable_dterm hz).hasSum.sub (summable_dterm hw).hasSum
  rw [← digamma_sub_one_eq hz, ← digamma_sub_one_eq hw] at h
  convert h using 1
  · funext k; simp only [dterm]; ring
  · ring


/-! ## B1. The mean-value bound and two elementary integrals -/

theorem norm_cexp_sub_le {z w : ℂ} {σ : ℝ} (hz : σ ≤ z.re) (hw : σ ≤ w.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(w * t)) - Complex.exp (-(z * t))‖ ≤ ‖z - w‖ * (t * Real.exp (-(σ * t))) := by
  have hd : ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => Complex.exp (-(ζ * t)))
      (Complex.exp (-(ζ * t)) * -(t : ℂ)) ζ := fun ζ => by
    have h := (((hasDerivAt_id ζ).mul_const (t : ℂ)).neg).cexp
    simp only [id, one_mul] at h
    exact h
  have key := (convex_halfSpace_re_ge σ).norm_image_sub_le_of_norm_deriv_le
    (f := fun ζ : ℂ => Complex.exp (-(ζ * t))) (C := t * Real.exp (-(σ * t)))
    (fun ζ _ => (hd ζ).differentiableAt) (fun ζ hζ => by
      have hζ' : σ ≤ ζ.re := hζ
      rw [(hd ζ).deriv, norm_mul, Complex.norm_exp, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg ht]
      have e : (-(ζ * (t : ℂ))).re = -(ζ.re * t) := by simp [Complex.mul_re]
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) ht)
    (show w ∈ {c : ℂ | σ ≤ c.re} from hw) (show z ∈ {c : ℂ | σ ≤ c.re} from hz)
  rw [norm_sub_rev]
  linarith [key]

theorem integrableOn_cexp_neg {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(a * t))) (Ioi 0) := by
  have := integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0
  simpa [neg_mul] using this

theorem integral_cexp_neg {a : ℂ} (ha : 0 < a.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(a * t)) = 1 / a := by
  have := integral_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0
  simpa [neg_mul] using this

theorem integrableOn_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(c * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := c) (by norm_num) one_pos hc
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem integral_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c * t)) = 1 / c ^ 2 := by
  have e : EqOn (fun t : ℝ => t ^ ((2 : ℝ) - 1) * Real.exp (-(c * t)))
      (fun t => t * Real.exp (-(c * t))) (Ioi 0) := fun t _ => by norm_num
  rw [← setIntegral_congr_fun measurableSet_Ioi e, Real.integral_rpow_mul_exp_neg_mul_Ioi two_pos hc,
    Real.rpow_two, Real.Gamma_two, mul_one, one_div_pow]

/-! ## B2. The terms `e^{−kt}(e^{−wt} − e^{−zt})` -/

/-- `G_k(t) = e^{−(k + w)t} − e^{−(k + z)t}`. -/
def Gk (z w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-(((k : ℂ) + w) * t)) - Complex.exp (-(((k : ℂ) + z) * t))

theorem Gk_eq (z w : ℂ) (k : ℕ) (t : ℝ) :
    Gk z w k t = Complex.exp (-((k : ℂ) * t)) * (Complex.exp (-(w * t)) - Complex.exp (-(z * t))) := by
  rw [Gk, mul_sub, ← Complex.exp_add, ← Complex.exp_add]; ring_nf

theorem re_add_pos {z : ℂ} (hz : 0 < z.re) (k : ℕ) : 0 < ((k : ℂ) + z).re := by
  simp only [Complex.add_re, Complex.natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) k]

theorem integrable_Gk {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) (k : ℕ) :
    Integrable (Gk z w k) (volume.restrict (Ioi 0)) :=
  (integrableOn_cexp_neg (re_add_pos hw k)).sub (integrableOn_cexp_neg (re_add_pos hz k))

theorem integral_Gk {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) (k : ℕ) :
    ∫ t in Ioi (0 : ℝ), Gk z w k t = 1 / ((k : ℂ) + w) - 1 / ((k : ℂ) + z) := by
  unfold Gk
  rw [integral_sub (integrableOn_cexp_neg (re_add_pos hw k)) (integrableOn_cexp_neg (re_add_pos hz k)),
    integral_cexp_neg (re_add_pos hw k), integral_cexp_neg (re_add_pos hz k)]

theorem norm_Gk_le {z w : ℂ} {σ : ℝ} (hz : σ ≤ z.re) (hw : σ ≤ w.re) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Gk z w k t‖ ≤ ‖z - w‖ * (t * Real.exp (-(((k : ℝ) + σ) * t))) := by
  rw [Gk_eq, norm_mul, Complex.norm_exp]
  have e : (-((k : ℂ) * (t : ℂ))).re = -((k : ℝ) * t) := by simp [Complex.mul_re]
  rw [e]
  calc Real.exp (-((k : ℝ) * t)) * ‖Complex.exp (-(w * t)) - Complex.exp (-(z * t))‖
      ≤ Real.exp (-((k : ℝ) * t)) * (‖z - w‖ * (t * Real.exp (-(σ * t)))) :=
        mul_le_mul_of_nonneg_left (norm_cexp_sub_le hz hw ht) (Real.exp_pos _).le
    _ = ‖z - w‖ * (t * (Real.exp (-((k : ℝ) * t)) * Real.exp (-(σ * t)))) := by ring
    _ = _ := by rw [← Real.exp_add]; ring_nf

theorem summable_integral_norm_Gk {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Summable fun k => ∫ t in Ioi (0 : ℝ), ‖Gk z w k t‖ := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  set δ := min σ 1
  have hδ : 0 < δ := lt_min hσ one_pos
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_)
    (summable_inv_sq.mul_left (‖z - w‖ / δ ^ 2))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkσ : 0 < (k : ℝ) + σ := by linarith
  have h1 : ∫ t in Ioi (0 : ℝ), ‖Gk z w k t‖
      ≤ ∫ t in Ioi (0 : ℝ), ‖z - w‖ * (t * Real.exp (-(((k : ℝ) + σ) * t))) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      ((integrableOn_mul_exp_neg hkσ).const_mul _) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
      norm_Gk_le (min_le_left _ _) (min_le_right _ _) k (le_of_lt ht))
  rw [integral_const_mul, integral_mul_exp_neg hkσ] at h1
  have h2 : 1 / ((k : ℝ) + σ) ^ 2 ≤ 1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    rw [div_mul_div_comm, one_mul, ← mul_pow]
    have : δ * ((k : ℝ) + 1) ≤ (k : ℝ) + σ := by
      have := min_le_left σ 1; have := min_le_right σ 1; nlinarith
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) this 2)
  calc _ ≤ ‖z - w‖ * (1 / ((k : ℝ) + σ) ^ 2) := h1
    _ ≤ ‖z - w‖ * (1 / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖z - w‖ / δ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by ring

/-! ## B3. The geometric series and the integrand -/

/-- The integrand of Gauss's formula. -/
def gaussK (z w : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(w * t)) - Complex.exp (-(z * t))) / ((1 - Real.exp (-t) : ℝ) : ℂ)

theorem hasSum_Gk (z w : ℂ) {t : ℝ} (ht : 0 < t) : HasSum (fun k => Gk z w k t) (gaussK z w t) := by
  set ξ := Complex.exp (-(t : ℂ))
  have hξ : ‖ξ‖ < 1 := by
    rw [Complex.norm_exp]; simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have h := (hasSum_geometric_of_norm_lt_one hξ).mul_right
    (Complex.exp (-(w * t)) - Complex.exp (-(z * t)))
  convert h using 1
  · funext k
    rw [Gk_eq, ← Complex.exp_nat_mul]; congr 2; ring
  · unfold gaussK
    rw [show ((1 - Real.exp (-t) : ℝ) : ℂ) = 1 - ξ by push_cast; rfl]
    ring

theorem one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have := Real.exp_lt_one_iff.2 (by linarith : -t < 0); linarith

theorem integrableOn_gaussK {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (gaussK z w) (Ioi 0) := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  have hcont : ContinuousOn (gaussK z w) (Ioi 0) := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) fun t ht => ?_
    · exact (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).sub
        (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg))
    · exact Complex.continuous_ofReal.comp (continuous_const.sub (Real.continuous_exp.comp continuous_neg))
    · exact_mod_cast (one_sub_exp_neg_pos ht).ne'
  have hb : IntegrableOn (fun t : ℝ => ‖z - w‖ * (Real.exp (-(σ * t)) + t * Real.exp (-(σ * t))))
      (Ioi 0) := by
    have he : IntegrableOn (fun t : ℝ => Real.exp (-(σ * t))) (Ioi 0) := by
      simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hσ
    exact (he.add (integrableOn_mul_exp_neg hσ)).const_mul _
  refine hb.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht' : 0 < t := ht
  have hden := one_sub_exp_neg_pos ht'
  have hD := norm_cexp_sub_le (min_le_left z.re w.re) (min_le_right z.re w.re) ht'.le
  have hq : t ≤ (1 + t) * (1 - Real.exp (-t)) := by
    have h1 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have h2 : (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le
    nlinarith
  unfold gaussK
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hden.le, div_le_iff₀ hden]
  have hE := (Real.exp_pos (-(σ * t))).le
  have hzw := norm_nonneg (z - w)
  calc _ ≤ ‖z - w‖ * (t * Real.exp (-(σ * t))) := hD
    _ ≤ ‖z - w‖ * (((1 + t) * (1 - Real.exp (-t))) * Real.exp (-(σ * t))) := by gcongr
    _ = _ := by ring

/-! ## B4. Gauss's formula -/

/-- **Gauss's integral for the digamma function** (difference form): for `Re z, Re w > 0`, the
kernel `(e^{−wt} − e^{−zt})/(1 − e^{−t})` is integrable on `(0, ∞)` and
`ψ(z) − ψ(w) = ∫_0^∞ (e^{−wt} − e^{−zt})/(1 − e^{−t}) dt`. -/
theorem digamma_sub_eq_integral {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (gaussK z w) (Ioi 0) ∧
      Complex.digamma z - Complex.digamma w = ∫ t in Ioi (0 : ℝ), gaussK z w t := by
  refine ⟨integrableOn_gaussK hz hw, ?_⟩
  have H := hasSum_integral_of_summable_integral_norm (integrable_Gk hz hw)
    (summable_integral_norm_Gk hz hw)
  have e : (fun k => ∫ t in Ioi (0 : ℝ), Gk z w k t)
      = fun k : ℕ => 1 / ((k : ℂ) + w) - 1 / ((k : ℂ) + z) := funext (integral_Gk hz hw)
  rw [e] at H
  rw [(hasSum_digamma_sub hz hw).unique H]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => (hasSum_Gk z w ht).tsum_eq

end PilotDigamma

#print axioms PilotDigamma.digamma_ofReal
#print axioms PilotDigamma.tendsto_rpsi_sub
#print axioms PilotDigamma.digamma_sub_one_eq
#print axioms PilotDigamma.hasSum_digamma_sub
#print axioms PilotDigamma.norm_cexp_sub_le
#print axioms PilotDigamma.hasSum_Gk
#print axioms PilotDigamma.integrableOn_gaussK
#print axioms PilotDigamma.digamma_sub_eq_integral
