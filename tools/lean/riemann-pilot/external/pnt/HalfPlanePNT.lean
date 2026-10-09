/-
# Round 337: a zero-free half-plane gives a power saving in the prime number theorem

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If `ζ(s) ≠ 0` for `Re s > θ`, `θ < 1`, then `ψ(x) − x = O(x^{(1+θ)/2+ε})` for every `ε > 0`
(`psi_isBigO_of_zeroFree`). Under round 278's `SmoothBound θ` and under the completed mean square of round
326 (`Re s > 11/12`) this gives `O(x^{(1+θ)/2+ε})` and `O(x^{23/24+ε})`.

* `riemannZeta_linear_growth`: `|ζ(s)| ≤ (5/2 + 1/δ)|Im s|` for `Re s ≥ δ > 0`, `|Im s| ≥ 1`, from PNT+'s
  Euler–Maclaurin formula.
* `logDeriv_le_of_zeroFree`: under a zero-free half-plane `Re s > θ ≥ 0`, `|ζ'/ζ(σ + it)| ≤ C log|t|` on
  `σ ≥ θ'`, `|t| > 3`, for every `θ' > θ`. Left of `3/2` this is PNT+'s `FinalBound` (Borel–Carathéodory with
  the zeros divided out) on the disc of radius `3/2 − θ` around `3/2 + it`, which holds no zero, with radii
  fixed by `θ'` (`disc_point`); right of `3/2`, PNT+'s `LogDerivZetaBdd_of_Re_ge_three_halves`.
* `psi_isBigO_of_zeroFree`: `MediumPNTW.GenPNTW'` at the constant depth `1 − θ'`.

The exponent is `(1+θ)/2`, not the classical `θ`: in the contour argument the segments left of `Re s = 1`
cost `x^{θ'}/ε` (PNT+'s `I3GenBoundW`-type bounds, through `MellinOfSmooth1b`), against `εx` for the
smoothing, and the two balance at `ε = x^{−(1−θ')/2}`.
-/
import MediumPNTW
import Landau
import HalfPlaneS0
import EisensteinTransferEstimate

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

namespace HalfPlanePNT


/-- `|ζ(s)| ≤ ½ + 1/|1 − s| + |s|/Re s` for `Re s > 0`, `s ≠ 1`: PNT+'s Euler–Maclaurin formula at `N = 1`
(`Zeta0EqZeta`, `ZetaBnd_aux1b`). The proof is that of zeta23's `RvM.norm_riemannZeta_le_of_re_pos`
(`Zeta23/RvM/ZetaGrowth.lean`), whose two inputs have the same statements in PNT+; zeta23's copy cannot be
imported here (STRUCTURAL-REVIEW §2.3). -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hint := ZetaBnd_aux1b 1 le_rfl (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one, Real.one_rpow] at hint
  rw [← Zeta0EqZeta (N := 1) one_pos hσ hs]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  calc ‖(1 : ℂ) + -1 / (1 - s) + -1 / 2 + s * J‖
      = ‖(1 / 2 : ℂ) + -(1 / (1 - s)) + s * J‖ := by ring_nf
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖-(1 / (1 - s))‖ + ‖s * J‖ := norm_add₃_le
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * ‖J‖ := by
        simp [norm_neg]
    _ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * (1 / s.re) := by gcongr
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by ring

/-- `|ζ(s)| ≤ (5/2 + 1/δ)|Im s|` for `Re s ≥ δ > 0`, `|Im s| ≥ 1`. -/
theorem riemannZeta_linear_growth {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re)
    (ht : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (5 / 2 + δ⁻¹) * |s.im| := by
  have hσpos : 0 < s.re := lt_of_lt_of_le hδ hσ
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at ht
  have h := norm_riemannZeta_le_of_re_pos hσpos hs1
  have him : |s.im| ≤ ‖1 - s‖ := by
    simpa using Complex.abs_im_le_norm (1 - s)
  have h1 : 1 / ‖1 - s‖ ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h2 : ‖s‖ / s.re ≤ 1 + δ⁻¹ * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hσpos] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / δ := by gcongr
      _ = 1 + δ⁻¹ * |s.im| := by rw [div_eq_inv_mul]
  have h3 : (5 / 2 : ℝ) ≤ 5 / 2 * |s.im| := by nlinarith
  nlinarith [h, h1, h2, h3]

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- Imaginary parts on a disc of radius `≤ ρ ≤ 3/2` around a point of height `|t| > 3`. -/
lemma im_bounds {t ρ : ℝ} {w : ℂ} (ht : 3 < |t|) (hρ : 0 < ρ) (hρ32 : ρ ≤ 3 / 2) (hw : ‖w‖ ≤ 1) :
    1 ≤ |t + ρ * w.im| ∧ |t + ρ * w.im| ≤ |t| + ρ := by
  have h1 : |w.im| ≤ 1 := (Complex.abs_im_le_norm w).trans hw
  have h2 : |ρ * w.im| ≤ ρ := by
    rw [abs_mul, abs_of_pos hρ]; exact mul_le_of_le_one_right hρ.le h1
  constructor
  · have := abs_sub_abs_le_abs_sub t (-(ρ * w.im))
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  · calc |t + ρ * w.im| ≤ |t| + |ρ * w.im| := abs_add_le _ _
      _ ≤ |t| + ρ := by linarith

/-- Real parts on a disc. -/
lemma re_ge {x ρ : ℝ} (w : ℂ) (hρ : 0 ≤ ρ) : x - ρ * ‖w‖ ≤ x + ρ * w.re := by
  have h : -‖w‖ ≤ w.re := by
    have := Complex.abs_re_le_norm w; linarith [neg_abs_le w.re]
  have := mul_le_mul_of_nonneg_left h hρ
  linarith

/-- The centre `3/2 + it` and the disc of radius `ρ` around it. -/
noncomputable def ctr (t : ℝ) : ℂ := ((3 / 2 : ℝ) : ℂ) + t * I

lemma ctr_re (t : ℝ) : (ctr t).re = 3 / 2 := by simp [ctr]
lemma ctr_im (t : ℝ) : (ctr t).im = t := by simp [ctr]

lemma ctr_ne_zero (t : ℝ) : riemannZeta (ctr t) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by rw [ctr_re]; norm_num)

lemma ctr_add_re (t ρ : ℝ) (w : ℂ) : (ctr t + ρ * w).re = 3 / 2 + ρ * w.re := by
  simp [ctr_re, mul_re]

lemma ctr_add_im (t ρ : ℝ) (w : ℂ) : (ctr t + ρ * w).im = t + ρ * w.im := by
  simp [ctr_im, mul_im]

lemma ctr_pole {t ρ : ℝ} (ht : 3 < |t|) (hρ : 0 < ρ) (hρ32 : ρ ≤ 3 / 2) :
    ∀ w : ℂ, ‖w‖ < 2 → ctr t + ρ * w ≠ 1 := by
  intro w hw h
  have him := congrArg Complex.im h
  rw [ctr_add_im, one_im] at him
  have h1 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h2 : |t| = ρ * |w.im| := by
    rw [show t = -(ρ * w.im) by linarith, abs_neg, abs_mul, abs_of_pos hρ]
  have h3 : ρ * |w.im| ≤ ρ * ‖w‖ := mul_le_mul_of_nonneg_left h1 hρ.le
  have h4 : ρ * ‖w‖ < ρ * 2 := mul_lt_mul_of_pos_left hw hρ
  linarith

/-- The growth of `ζ(s₀ + ρw)/ζ(s₀)` on the disc of radius `R`. -/
lemma locF_bound {t ρ R : ℝ} (ht : 3 < |t|) (hρ : 0 < ρ) (hρ32 : ρ ≤ 3 / 2) (hR1 : R < 1)
    (hδ : 0 < 3 / 2 - ρ * R) {w : ℂ} (hw : ‖w‖ ≤ R) :
    ‖Landau.locF (ctr t) ρ w‖ ≤
      (5 / 2 + (3 / 2 - ρ * R)⁻¹) * ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ * (|t| + ρ) := by
  have hre : 3 / 2 - ρ * R ≤ (ctr t + ρ * w).re := by
    rw [ctr_add_re]
    have := re_ge (x := 3 / 2) w hρ.le
    have : ρ * ‖w‖ ≤ ρ * R := mul_le_mul_of_nonneg_left hw hρ.le
    linarith
  obtain ⟨him1, himle⟩ := im_bounds ht hρ hρ32 (hw.trans hR1.le)
  rw [← ctr_add_im] at him1 himle
  have hgrowth := riemannZeta_linear_growth hδ hre him1
  have hinv : 1 / ‖riemannZeta (ctr t)‖ ≤ ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ := by
    have := Landau.inv_norm_zeta_le (s := ctr t) (by rw [ctr_re]; norm_num)
    rwa [ctr_re] at this
  unfold Landau.locF
  rw [norm_div, div_eq_mul_one_div]
  calc ‖riemannZeta (ctr t + ρ * w)‖ * (1 / ‖riemannZeta (ctr t)‖)
      ≤ ((5 / 2 + (3 / 2 - ρ * R)⁻¹) * (|t| + ρ)) * ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ := by
        apply mul_le_mul _ hinv (by positivity) (by positivity)
        exact hgrowth.trans (mul_le_mul_of_nonneg_left himle (by positivity))
    _ = (5 / 2 + (3 / 2 - ρ * R)⁻¹) * ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ * (|t| + ρ) := by ring

/-- The logarithmic derivative of `locF` is `ρ ζ'/ζ`. -/
lemma locF_logDeriv {s₀ z : ℂ} {ρ : ℝ} (hζ0 : riemannZeta s₀ ≠ 0) (hs1 : s₀ + ρ * z ≠ 1)
    (hζz : riemannZeta (s₀ + ρ * z) ≠ 0) :
    deriv (Landau.locF s₀ ρ) z / Landau.locF s₀ ρ z =
      ρ * (deriv riemannZeta (s₀ + ρ * z) / riemannZeta (s₀ + ρ * z)) := by
  have h1 : HasDerivAt riemannZeta (deriv riemannZeta (s₀ + ρ * z)) (s₀ + ρ * z) :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => s₀ + ρ * w) (ρ : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (ρ : ℂ)).const_add s₀
  have h2 := (h1.comp z hlin).div_const (riemannZeta s₀)
  have hderiv : deriv (Landau.locF s₀ ρ) z = ρ * deriv riemannZeta (s₀ + ρ * z) / riemannZeta s₀ := by
    rw [show Landau.locF s₀ ρ = fun w => (riemannZeta ∘ fun w : ℂ => s₀ + ρ * w) w / riemannZeta s₀ by
      funext w; simp [Landau.locF], h2.deriv]
    ring
  rw [hderiv]; simp only [Landau.locF]; field_simp

/-- **The disc step.** Under a zero-free half-plane `Re s > θ ≥ 0`, with `ρ = 3/2 − θ` and radii
`0 < r' < r < R' < R < 1`: at a point `σ + it`, `|t| > 3`, with `θ < σ < 3/2` and `3/2 − σ ≤ ρ r'`,
`ρ |ζ'/ζ(σ + it)| ≤ K log B`, with `K` the constant of PNT+'s `FinalBound` and
`B = 2 + c (|t| + ρ)`. -/
lemma disc_point {θ σ t r' r R' R : ℝ} (hθ0 : 0 ≤ θ) (ht : 3 < |t|) (hσθ : θ < σ)
    (hr'0 : 0 < r') (hr'r : r' < r) (hr1 : r < 1) (hrR' : r < R') (hR'R : R' < R) (hR1 : R < 1)
    (hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ)) (hσ32 : σ < 3 / 2)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    (3 / 2 - θ) * ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤
      (16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))) *
        Real.log (2 + (5 / 2 + (3 / 2 - (3 / 2 - θ) * R)⁻¹) * ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ *
          (|t| + (3 / 2 - θ))) := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  have hρ32 : ρ ≤ 3 / 2 := by linarith
  have hδ : 0 < 3 / 2 - ρ * R := by
    have : ρ * R < ρ := mul_lt_of_lt_one_right hρ hR1
    linarith
  set c : ℝ := (5 / 2 + (3 / 2 - ρ * R)⁻¹) * ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ with hcdef
  have hc : 0 ≤ c := by positivity
  set B : ℝ := 2 + c * (|t| + ρ) with hBdef
  have hB : 1 < B := by
    have : 0 ≤ c * (|t| + ρ) := mul_nonneg hc (by positivity)
    linarith
  set f := Landau.locF (ctr t) ρ with hfdef
  have hζ0 := ctr_ne_zero t
  have hpole := ctr_pole ht hρ hρ32
  have hf0 : f 0 = 1 := by simp [hfdef, Landau.locF, hζ0]
  have hfA2 := Landau.locF_analytic hpole
  have hfA : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    apply hfA2 w
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hfin : (SetOfZeros 1 f).Finite :=
    Landau.finiteZeros_of_analytic hfA2 (by rw [hf0]; exact one_ne_zero)
  have hfb : ∀ w : ℂ, ‖w‖ ≤ R → ‖f w‖ ≤ B := by
    intro w hw
    have h := locF_bound ht hρ hρ32 hR1 hδ hw
    have : c * (|t| + ρ) ≤ B := by simp only [hBdef]; linarith
    exact h.trans this
  set z : ℂ := (((σ - 3 / 2) / ρ : ℝ) : ℂ) with hzdef
  have hsz : ctr t + ρ * z = (σ : ℂ) + t * I := by
    apply Complex.ext
    · have e : ((σ : ℂ) + t * I).re = σ := by simp
      rw [ctr_add_re, hzdef, ofReal_re, e]; field_simp; ring
    · rw [ctr_add_im, hzdef, ofReal_im]; simp
  have hznorm : ‖z‖ ≤ r' := by
    rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hρ,
      abs_of_neg (by linarith), div_le_iff₀ hρ]
    linarith
  have hζz : riemannZeta (ctr t + ρ * z) ≠ 0 := by
    rw [hsz]; apply hzf; simp; linarith
  have hfz : f z ≠ 0 := by
    simp only [hfdef, Landau.locF, div_ne_zero_iff]; exact ⟨hζz, hζ0⟩
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) r' \ SetOfZeros R' f :=
    ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hznorm, fun h => hfz h.2⟩
  have FB := FinalBound (B := B) (r' := r') (r := r) (R' := R') (R := R) hB hr'0 hr'r hr1 hrR' hR'R hR1
    hfA hf0 hfin hfb hzmem
  have hsum : ∑ q ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset,
      (analyticOrderNatAt f q : ℂ) / (z - q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    exfalso
    rw [Set.Finite.mem_toFinset] at hq
    have hzero : riemannZeta (ctr t + ρ * q) = 0 := by
      have := hq.2; simp only [hfdef, Landau.locF, div_eq_zero_iff, hζ0, or_false] at this; exact this
    apply hzf _ _ hzero
    rw [ctr_add_re]
    have h1 := re_ge (x := 3 / 2) q hρ.le
    have h2 : ρ * ‖q‖ ≤ ρ * r := mul_le_mul_of_nonneg_left hq.1 hρ.le
    have h3 : ρ * r < ρ := mul_lt_of_lt_one_right hρ hr1
    linarith
  rw [hsum, sub_zero, locF_logDeriv hζ0 (hpole z (by linarith)) hζz, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ, hsz] at FB
  exact FB

/-- **The log-derivative under a zero-free half-plane.** If `ζ(s) ≠ 0` for `Re s > θ ≥ 0`, then for every
`θ' ∈ (θ, 3/2)` there is `C` with `|ζ'/ζ(σ + it)| ≤ C log|t|` for `σ ≥ θ'`, `|t| > 3`. -/
theorem logDeriv_le_of_zeroFree {θ θ' : ℝ} (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 3 < |t| → θ' ≤ σ →
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  set r' : ℝ := (3 / 2 - θ') / ρ with hr'def
  have hr'0 : 0 < r' := div_pos (by linarith) hρ
  have hr'1 : r' < 1 := by rw [hr'def, div_lt_one hρ]; linarith
  set r : ℝ := r' + (1 - r') / 4 with hrdef
  set R' : ℝ := r' + (1 - r') / 2 with hR'def
  set R : ℝ := r' + 3 * (1 - r') / 4 with hRdef
  have hr'r : r' < r := by linarith
  have hr1 : r < 1 := by linarith
  have hrR' : r < R' := by linarith
  have hR'R : R' < R := by linarith
  have hR1 : R < 1 := by linarith
  have hR'0 : 0 < R' := by linarith
  set K : ℝ := 16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R')) with hKdef
  have hK : 0 < K := by
    have h1 : 0 < R ^ 2 / R' - R' := by
      rw [sub_pos, lt_div_iff₀ hR'0]; nlinarith
    have h2 : 0 < Real.log (R / R') := Real.log_pos (by rw [one_lt_div hR'0]; exact hR'R)
    have h3 : 0 < 16 * r ^ 2 / (r - r') ^ 3 := by
      have : 0 < r - r' := by linarith
      positivity
    have h4 : 0 < 1 / ((R ^ 2 / R' - R') * Real.log (R / R')) := by positivity
    linarith
  set c : ℝ := (5 / 2 + (3 / 2 - ρ * R)⁻¹) * ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ with hcdef
  have hδ : 0 < 3 / 2 - ρ * R := by
    have : ρ * R < ρ := mul_lt_of_lt_one_right hρ hR1
    linarith
  have hc : 0 ≤ c := by positivity
  set L : ℝ := Real.log (2 * (1 + c)) + 1 with hLdef
  have hL : 0 < L := by
    have : 0 ≤ Real.log (2 * (1 + c)) := Real.log_nonneg (by linarith)
    linarith
  obtain ⟨C₂, hC₂⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  refine ⟨max |C₂| (K / ρ * L) + 1, by positivity, fun σ t ht hσ => ?_⟩
  have hlt : 1 < Real.log |t| :=
    lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) ht.le)
  have hC1 : |C₂| ≤ max |C₂| (K / ρ * L) + 1 := by
    have := le_max_left |C₂| (K / ρ * L); linarith
  have hC2 : K / ρ * L ≤ max |C₂| (K / ρ * L) + 1 := by
    have := le_max_right |C₂| (K / ρ * L); linarith
  by_cases h32 : 3 / 2 ≤ σ
  · have h := hC₂ (σ + t * I) (by simpa using h32)
    calc ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ |C₂| := h.trans (le_abs_self _)
      _ ≤ |C₂| * Real.log |t| := le_mul_of_one_le_right (abs_nonneg _) hlt.le
      _ ≤ (max |C₂| (K / ρ * L) + 1) * Real.log |t| := by gcongr
  push Not at h32
  have hz : 3 / 2 - σ ≤ r' * (3 / 2 - θ) := by
    rw [hr'def, div_mul_cancel₀ _ hρ.ne']; linarith
  have FB := disc_point hθ0 ht (by linarith) hr'0 hr'r hr1 hrR' hR'R hR1 hz h32 hzf
  rw [← hρdef, ← hKdef, ← hcdef] at FB
  have hlogB : Real.log (2 + c * (|t| + ρ)) ≤ L * Real.log |t| := by
    have hB2 : 2 + c * (|t| + ρ) ≤ 2 * (1 + c) * |t| := by
      have : c * (|t| + ρ) ≤ c * (|t| + 2) := mul_le_mul_of_nonneg_left (by linarith) hc
      have : c * (|t| + 2) ≤ c * (2 * |t|) := mul_le_mul_of_nonneg_left (by linarith) hc
      have : 2 ≤ 2 * |t| := by linarith
      linarith
    have hBpos : 0 < 2 + c * (|t| + ρ) := by
      have : 0 ≤ c * (|t| + ρ) := mul_nonneg hc (by positivity)
      linarith
    have hl0 : 0 ≤ Real.log (2 * (1 + c)) := Real.log_nonneg (by linarith)
    calc Real.log (2 + c * (|t| + ρ)) ≤ Real.log (2 * (1 + c) * |t|) := Real.log_le_log hBpos hB2
      _ = Real.log (2 * (1 + c)) + Real.log |t| := by
          rw [Real.log_mul (by positivity) (by positivity)]
      _ ≤ Real.log (2 * (1 + c)) * Real.log |t| + Real.log |t| := by
          have := mul_le_mul_of_nonneg_left hlt.le hl0; linarith
      _ = L * Real.log |t| := by simp only [hLdef]; ring
  have hmain : ρ * ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤
      ρ * (K / ρ * L * Real.log |t|) := by
    calc ρ * ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖
        ≤ K * Real.log (2 + c * (|t| + ρ)) := FB
      _ ≤ K * (L * Real.log |t|) := mul_le_mul_of_nonneg_left hlogB hK.le
      _ = ρ * (K / ρ * L * Real.log |t|) := by field_simp
  have h1 := le_of_mul_le_mul_left hmain hρ
  calc ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ K / ρ * L * Real.log |t| := h1
    _ ≤ (max |C₂| (K / ρ * L) + 1) * Real.log |t| := by gcongr

/-- A zero-free half-plane `Re s > θ` has `θ ≥ ½`: ζ has a zero with real part at least `½`
(`PsiOmega.exists_zero_re_ge_half`). -/
theorem half_le_of_zeroFree {θ : ℝ} (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) : 1 / 2 ≤ θ := by
  by_contra h
  obtain ⟨ρ, hρ, hre⟩ := PsiOmega.exists_zero_re_ge_half
  exact hzf ρ (by linarith) hρ

section PNT

open scoped Chebyshev

open MediumPNTW

/-- `x^y / x^z = x^{y − z}` for `x > 0`. -/
lemma rpow_div_rpow' {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ y / x ^ z = x ^ (y - z) :=
  (Real.rpow_sub hx y z).symm

/-- **A zero-free half-plane gives a power saving in the prime number theorem.** If `ζ(s) ≠ 0` for
`Re s > β` with `β < 1`, then `ψ(x) − x = O(x^{(1+β)/2+ε})` for every `ε > 0`. `GenPNTW'` at the
constant depth `1 − β'`, `β' = β + min(ε, (1 − β)/2)`, with `T = x`, smoothing width `x^{−(1−β')/2}` and the
bound of `logDeriv_le_of_zeroFree`. (`β` for the abscissa: `θ` is Chebyshev's function here.) -/
theorem psi_isBigO_of_zeroFree {β : ℝ} (hβ1 : β < 1) (hzf : ∀ s : ℂ, β < s.re → ζ s ≠ 0) {ε : ℝ}
    (hε : 0 < ε) : (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ ((1 + β) / 2 + ε) := by
  have hβ := half_le_of_zeroFree hzf
  set η : ℝ := min ε ((1 - β) / 2) with hηdef
  have hη : 0 < η := lt_min hε (by linarith)
  have hηε : η ≤ ε := min_le_left _ _
  have hη1 : η ≤ (1 - β) / 2 := min_le_right _ _
  set β' : ℝ := β + η with hβ'def
  have hβ'1 : β' < 1 := by linarith
  obtain ⟨C, hC, hbnd⟩ := logDeriv_le_of_zeroFree (by linarith : (0 : ℝ) ≤ β)
    (by linarith : β < β') (by linarith : β' < 3 / 2) hzf
  set D : ℝ → ℝ := fun _ ↦ 1 - β' with hDdef
  have hD : DepthOK D := ⟨fun _ _ ↦ by simp only [hDdef]; linarith,
    fun _ _ ↦ by simp only [hDdef]; linarith, fun _ _ _ _ ↦ le_rfl⟩
  have hb : LogDerivZetaHasBoundW D 1 C := by
    intro σ t ht hσ
    rw [Real.rpow_one]
    exact hbnd σ t ht (by simpa [hDdef] using hσ)
  have holo : ∀ T : ℝ, 3 ≤ T → HolomorphicOn (fun s : ℂ ↦ ζ' s / ζ s)
      ((Icc (1 - D T) 2 ×ℂ Icc (-T) T) \ {1}) := fun T _ ↦
    LogDerivZetaHoloOn (Set.notMem_sdiff_of_mem rfl) (fun s hs ↦ hzf s (by
      have := (Complex.mem_reProdIm.mp hs.1).1.1
      simp only [hDdef] at this; linarith))
  set σ₂ : ℝ := β + η / 2 with hσ₂def
  have σ₂InIoo : σ₂ ∈ Ioo 0 1 := ⟨by linarith, by linarith⟩
  have holo2 : HolomorphicOn (fun s : ℂ ↦ ζ' s / ζ s) ((uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1}) :=
    LogDerivZetaHoloOn (Set.notMem_sdiff_of_mem rfl) (fun s hs ↦ hzf s (by
      have h := (Complex.mem_reProdIm.mp hs.1).1
      rw [uIcc_of_le (by linarith)] at h
      linarith [h.1]))
  set a : ℝ := (1 - β') / 2 with hadef
  have ha : 0 < a := by linarith
  set b : ℝ := ε / 2 with hbdef
  have hb0 : 0 < b := by linarith
  -- `log x ≤ x^b` eventually
  have hlog : ∀ᶠ x in atTop, Real.log x ≤ x ^ b := by
    have h := (isLittleO_log_rpow_atTop hb0).bound one_pos
    filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
    rw [one_mul, Real.norm_of_nonneg (Real.log_nonneg hx1.le),
      Real.norm_of_nonneg (by positivity)] at hx
    exact hx
  have key := GenPNTW' hD one_pos hC hb holo (fun x ↦ x) (fun x ↦ x ^ (-a)) (fun x ↦ x ^ (-a + b))
    tendsto_id
    (by filter_upwards [eventually_gt_atTop 0] with x hx using Real.rpow_pos_of_pos hx _)
    (tendsto_rpow_neg_atTop ha)
    σ₂InIoo holo2
    (by -- `2 < x · x^{−a}`
      have h1a : 0 < 1 - a := by linarith
      filter_upwards [(tendsto_rpow_atTop h1a).eventually_gt_atTop 2, eventually_gt_atTop 0]
        with x hx hx0
      rw [show x * x ^ (-a) = x ^ (1 - a) by
        rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]]
      exact hx)
    (Eventually.of_forall fun x ↦ by simp only [hDdef]; linarith)
    (by -- `ε log x ≤ F`
      filter_upwards [hlog, eventually_gt_atTop 0] with x hx hx0
      rw [Real.rpow_add hx0]
      exact mul_le_mul_of_nonneg_left hx (by positivity))
    (by -- `log x/(ε T) ≤ F`
      filter_upwards [hlog, eventually_gt_atTop 1] with x hx hx1
      have hx0 : 0 < x := by linarith
      have e : x ^ (-a) * x = x ^ (1 - a) := by
        rw [mul_comm, sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
      rw [e, div_le_iff₀ (by positivity), ← Real.rpow_add hx0]
      calc Real.log x ≤ x ^ b := hx
        _ ≤ x ^ (-a + b + (1 - a)) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
    (by -- `x^{−D}/ε ≤ F`
      filter_upwards [eventually_gt_atTop 1] with x hx1
      have hx0 : 0 < x := by linarith
      simp only [hDdef]
      rw [rpow_div_rpow' hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [hadef]; linarith))
    (by -- `x^{σ₂−1}/ε ≤ F`
      filter_upwards [eventually_gt_atTop 1] with x hx1
      have hx0 : 0 < x := by linarith
      rw [rpow_div_rpow' hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [hadef, hσ₂def, hβ'def]; linarith))
  refine key.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 1] with x hx1
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  rw [show x * x ^ (-a + b) = x ^ (1 + (-a + b)) by rw [Real.rpow_add hx0 1 (-a + b), Real.rpow_one]]
  exact Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [hadef, hbdef, hβ'def]; linarith)

/-- Under round 278's `SmoothBound β`, `β < 1`: `ψ(x) − x = O(x^{(1+β)/2+ε})`. -/
theorem psi_isBigO_of_smoothBound {β : ℝ} (h : HalfPlaneS0.SmoothBound β) (hβ1 : β < 1) {ε : ℝ}
    (hε : 0 < ε) : (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ ((1 + β) / 2 + ε) :=
  psi_isBigO_of_zeroFree hβ1 (fun _ hs ↦ (HalfPlaneS0.ne_zero_of_smoothBound h hs).1) hε

/-- Under the completed mean square (`Eis.CompletedMeanSquare`, the companion paper's Proposition 5.2), which
gives `ζ(s) ≠ 0` on `Re s > 11/12` (round 326): `ψ(x) − x = O(x^{23/24+ε})`. -/
theorem psi_isBigO_of_completed (hC : Eis.CompletedMeanSquare) {ε : ℝ} (hε : 0 < ε) :
    (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ ((23 : ℝ) / 24 + ε) := by
  have h := psi_isBigO_of_zeroFree (by norm_num : (11 : ℝ) / 12 < 1)
    (fun _ hs ↦ (Eis.ne_zero_of_completed hC hs).1) hε
  convert h using 3; norm_num

end PNT

end HalfPlanePNT

#print axioms HalfPlanePNT.riemannZeta_linear_growth
#print axioms HalfPlanePNT.disc_point
#print axioms HalfPlanePNT.logDeriv_le_of_zeroFree
#print axioms HalfPlanePNT.half_le_of_zeroFree
#print axioms HalfPlanePNT.psi_isBigO_of_zeroFree
#print axioms HalfPlanePNT.psi_isBigO_of_smoothBound
#print axioms HalfPlanePNT.psi_isBigO_of_completed
