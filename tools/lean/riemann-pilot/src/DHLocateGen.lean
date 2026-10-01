import DHLocateExp

/-!
# The zero-location certificate for a general centre

`DHLocateSkeleton` states its ladder, its elementary forms and its ball-uniform bounds for the one
centre `cLoc`. This file re-states the centre-dependent parts for an arbitrary centre `c` and radius
`r` (the approximant `fEM M K = DEM M + GEM M K`, its derivatives, the termwise and Cauchy bounds and
the minimum-modulus instrument are reused unchanged from the skeleton), so that a further zero needs
only numbers: the box constants of the Euler–Maclaurin error, the sup of `GEM` on a larger ball, the
termwise sum `D2sum`, and the three point values at `c`.

* `dh_zero_near_of_fEMG`: the ladder in normalised units, for any `c` with `r < Im c`.
* `norm_dh_sub_dhEM_le_ballG`: the Euler–Maclaurin error on `closedBall c r` from five rational
  bounds (`5^{-σ₀}`, `(M + j/5)^{1-σ₀-24}`) and the box product (`K = 12`).
* `norm_deriv2_fEM_ballG`: `‖DEM″ + GEM″‖ ≤ D2sum + 2C/R²` on `closedBall c r` (termwise for `DEM`,
  Cauchy on circles of radius `R` for `GEM`).
* `cCG`, `sCG`, `PReG`, `PImG`, `QDG`, `AReG`, `AImG`: the elementary forms of `fEM(c)`, `fEM′(c)`;
  `dh_zero_near_of_elementaryG`: the ladder in elementary form.
-/

open Complex Metric
open scoped Nat

noncomputable section

namespace PsiOmega

namespace Locate

/-! ## 1. Ball geometry -/

theorem box_of_memG {c z : ℂ} {ρ : ℝ} (hz : z ∈ closedBall c ρ) :
    c.re - ρ ≤ z.re ∧ z.re ≤ c.re + ρ ∧ c.im - ρ ≤ z.im ∧ z.im ≤ c.im + ρ := by
  obtain ⟨h1, h2⟩ := re_im_of_mem_closedBall hz
  rw [abs_le] at h1 h2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem ne_one_of_memG {c z : ℂ} {ρ : ℝ} (hρ : ρ < c.im) (hz : z ∈ closedBall c ρ) : z ≠ 1 := by
  intro h
  have := (box_of_memG hz).2.2.1
  rw [h, Complex.one_im] at this
  linarith

/-! ## 2. The ladder, normalised -/

/-- **The certificate for a general centre**, normalised: `‖fEM(c)‖ ≤ p₀`, `a₀ ≤ ‖fEM′(c)‖`,
`‖DEM″ + GEM″‖ ≤ m₂` and `‖dh − dhEM‖ ≤ ‖a(1)‖ e₀` on `closedBall c r`, and the margin
`2(p₀ + e₀) < a₀ r − m₂ r²`, give a zero of `dh` within `r` of `c`. -/
theorem dh_zero_near_of_fEMG {c : ℂ} {r p₀ a₀ m₂ e₀ : ℝ} {M K : ℕ} (hr : 0 < r) (hcr : r < c.im)
    (hP : ‖fEM M K c‖ ≤ p₀)
    (hA : a₀ ≤ ‖DEMk 1 M c + GEMd M K c‖)
    (hM2 : ∀ z ∈ closedBall c r, ‖DEMk 2 M z + deriv (deriv (GEM M K)) z‖ ≤ m₂)
    (hE : ∀ z ∈ closedBall c r, ‖dh z - dhEM M K z‖ ≤ ‖aDH chi5 1‖ * e₀)
    (hmargin : 2 * (p₀ + e₀) < a₀ * r - m₂ * r ^ 2) :
    ∃ ρ, dh ρ = 0 ∧ ‖ρ - c‖ < r := by
  have hA0 := norm_aDH_one_pos
  have hU : ∀ w ∈ closedBall c r, w ∈ {s : ℂ | s ≠ 1} := fun w hw => ne_one_of_memG hcr hw
  have hc1 : c ≠ 1 := ne_one_of_memG hcr (mem_closedBall_self hr.le)
  have hP' : ‖dhEM M K c‖ ≤ ‖aDH chi5 1‖ * p₀ := by
    rw [dhEM_eq, norm_mul]
    exact mul_le_mul_of_nonneg_left hP hA0.le
  have hA' : ‖aDH chi5 1‖ * a₀ ≤ ‖deriv (dhEM M K) c‖ := by
    rw [deriv_dhEM M K hc1, norm_mul]
    exact mul_le_mul_of_nonneg_left hA hA0.le
  have hM2' : ∀ z ∈ closedBall c r, ‖deriv (deriv (dhEM M K)) z‖ ≤ ‖aDH chi5 1‖ * m₂ := by
    intro z hz
    rw [deriv2_dhEM M K (ne_one_of_memG hcr hz), norm_mul]
    exact mul_le_mul_of_nonneg_left (hM2 z hz) hA0.le
  have hmargin' : 2 * (‖aDH chi5 1‖ * p₀ + ‖aDH chi5 1‖ * e₀) <
      ‖aDH chi5 1‖ * a₀ * r - ‖aDH chi5 1‖ * m₂ * r ^ 2 := by
    have h := mul_lt_mul_of_pos_left hmargin hA0
    have e1 : ‖aDH chi5 1‖ * (2 * (p₀ + e₀)) = 2 * (‖aDH chi5 1‖ * p₀ + ‖aDH chi5 1‖ * e₀) := by
      ring
    have e2 : ‖aDH chi5 1‖ * (a₀ * r - m₂ * r ^ 2) =
        ‖aDH chi5 1‖ * a₀ * r - ‖aDH chi5 1‖ * m₂ * r ^ 2 := by ring
    rw [e1, e2] at h
    exact h
  obtain ⟨z, hz, h0⟩ := exists_zero_of_bounds (f := dh) (P := dhEM M K) hr
    differentiable_dh.differentiableOn
    (fun w hw => (differentiableOn_dhEM M K).differentiableAt (isOpen_ne.mem_nhds (hU w hw)))
    (fun w hw => ((differentiableOn_dhEM M K).deriv isOpen_ne).differentiableAt
      (isOpen_ne.mem_nhds (hU w hw)))
    hP' hA' hM2' hE hmargin'
  exact ⟨z, h0, mem_ball_iff_norm.1 hz⟩

/-! ## 3. The Euler–Maclaurin error on a ball (`K = 12`) -/

/-- **The Euler–Maclaurin error on `closedBall c r`**, normalised, from rational bounds:
`5^{-σ₀} ≤ y₅`, `(M + j/5)^{1-σ₀-24} ≤ y_j`, the box product `≤ B²`, and the final numeral
inequality `hfin` (with `κ ≤ 0.28408` and `(π²/3)/(2π)²⁴ ≤ 1/(3·2²⁴·3.141592²²)`). -/
theorem norm_dh_sub_dhEM_le_ballG {c : ℂ} {r σ₀ σ₁ τ B y5 y1 y2 y3 y4 e₀ : ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hσ₀ : 0 < σ₀) (hB : 0 ≤ B) (h0 : σ₀ ≤ c.re - r) (h1 : c.re + r ≤ σ₁)
    (hT : c.im + r ≤ τ) (hcr : r < c.im)
    (hPB : ∏ i ∈ Finset.range (2 * 12), ((σ₁ + i) ^ 2 + τ ^ 2) ≤ B ^ 2)
    (h5 : (5 : ℝ) ^ (-σ₀) ≤ y5)
    (hy1 : ((M : ℝ) + 1 / 5) ^ (1 - σ₀ - 2 * 12) ≤ y1)
    (hy2 : ((M : ℝ) + 2 / 5) ^ (1 - σ₀ - 2 * 12) ≤ y2)
    (hy3 : ((M : ℝ) + 3 / 5) ^ (1 - σ₀ - 2 * 12) ≤ y3)
    (hy4 : ((M : ℝ) + 4 / 5) ^ (1 - σ₀ - 2 * 12) ≤ y4)
    (hfin : y5 * (1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22) * B / (σ₀ + 2 * 12 - 1) *
        (y1 + 28408 / 100000 * y2 + 28408 / 100000 * y3 + y4)) ≤ e₀)
    {z : ℂ} (hz : z ∈ closedBall c r) : ‖dh z - dhEM M 12 z‖ ≤ ‖aDH chi5 1‖ * e₀ := by
  obtain ⟨b1, b2, b3, b4⟩ := box_of_memG hz
  have hs0 : σ₀ ≤ z.re := by linarith
  have hs1 : z.re ≤ σ₁ := by linarith
  have hsT : |z.im| ≤ τ := by rw [abs_le]; constructor <;> linarith
  have hb := norm_dh_sub_EM_le_box (M := M) (K := 12) hM (by norm_num) hσ₀ hB hPB hs0 hs1 hsT
    (ne_one_of_memG hcr hz)
  simp only [Nat.cast_ofNat, Nat.cast_one] at hb
  rw [norm_aDH_two, norm_aDH_three, norm_aDH_four] at hb
  refine hb.trans ?_
  have hA0 : 0 ≤ ‖aDH chi5 1‖ := norm_nonneg _
  have hk0 : 0 ≤ kappa := kappa_pos.le
  have hk : kappa ≤ 28408 / 100000 := kappa_le
  have hC : Real.pi ^ 2 / 3 / (2 * Real.pi) ^ (2 * 12) ≤
      1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22) := pi_const_le
  have hC0 : 0 ≤ Real.pi ^ 2 / 3 / (2 * Real.pi) ^ (2 * 12) := by positivity
  have hd : 0 < σ₀ + 2 * 12 - 1 := by linarith
  have hX : ∀ j : ℝ, 0 ≤ j → 0 ≤ ((M : ℝ) + j / 5) ^ (1 - σ₀ - 2 * 12) := fun j hj =>
    Real.rpow_nonneg (by positivity) _
  have hX1 := hX 1 (by norm_num)
  have hX2 := hX 2 (by norm_num)
  have hX3 := hX 3 (by norm_num)
  have hX4 := hX 4 (by norm_num)
  have h50 : 0 ≤ (5 : ℝ) ^ (-σ₀) := Real.rpow_nonneg (by norm_num) _
  set C := Real.pi ^ 2 / 3 / (2 * Real.pi) ^ (2 * 12) with hCdef
  set C' := 1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22) with hC'def
  set X1 := ((M : ℝ) + 1 / 5) ^ (1 - σ₀ - 2 * 12) with hX1def
  set X2 := ((M : ℝ) + 2 / 5) ^ (1 - σ₀ - 2 * 12) with hX2def
  set X3 := ((M : ℝ) + 3 / 5) ^ (1 - σ₀ - 2 * 12) with hX3def
  set X4 := ((M : ℝ) + 4 / 5) ^ (1 - σ₀ - 2 * 12) with hX4def
  set d := σ₀ + 2 * 12 - 1 with hddef
  set A := ‖aDH chi5 1‖ with hAdef
  have e : (5 : ℝ) ^ (-σ₀) * (A * (C * B * (X1 / d)) + A * kappa * (C * B * (X2 / d)) +
      A * kappa * (C * B * (X3 / d)) + A * (C * B * (X4 / d))) =
      A * ((5 : ℝ) ^ (-σ₀) * (C * B / d * (X1 + kappa * X2 + kappa * X3 + X4))) := by ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hA0
  have hCB : C * B / d ≤ C' * B / d := by
    apply div_le_div_of_nonneg_right _ hd.le
    exact mul_le_mul_of_nonneg_right hC hB
  have hCB0 : 0 ≤ C * B / d := by positivity
  have hS : X1 + kappa * X2 + kappa * X3 + X4 ≤ y1 + 28408 / 100000 * y2 + 28408 / 100000 * y3 + y4 := by
    have t2 : kappa * X2 ≤ 28408 / 100000 * y2 := mul_le_mul hk hy2 hX2 (by norm_num)
    have t3 : kappa * X3 ≤ 28408 / 100000 * y3 := mul_le_mul hk hy3 hX3 (by norm_num)
    linarith
  have hS0 : 0 ≤ X1 + kappa * X2 + kappa * X3 + X4 := by positivity
  have hy50 : 0 ≤ y5 := h50.trans h5
  calc (5 : ℝ) ^ (-σ₀) * (C * B / d * (X1 + kappa * X2 + kappa * X3 + X4))
      ≤ y5 * (C' * B / d * (y1 + 28408 / 100000 * y2 + 28408 / 100000 * y3 + y4)) := by
        apply mul_le_mul h5 _ (by positivity) hy50
        exact mul_le_mul hCB hS hS0 (hCB0.trans hCB)
    _ = y5 * (1 / (3 * 2 ^ 24 * (3141592 / 1000000 : ℝ) ^ 22) * B / (σ₀ + 2 * 12 - 1) *
        (y1 + 28408 / 100000 * y2 + 28408 / 100000 * y3 + y4)) := by rw [hC'def, hddef]
    _ ≤ e₀ := hfin

/-! ## 4. The second derivative on a ball -/

/-- **Cauchy for `G″` at a point of `closedBall c r`**, from the termwise sup `Gsup ≤ C` on the box of
`closedBall c (r + R)`: `‖GEM″(z)‖ ≤ 2C/R²`. -/
theorem norm_deriv2_GEM_ballG (M K : ℕ) {c z : ℂ} {r R σ₀ σ₁ τ τ₀ C : ℝ} (hR : 0 < R)
    (hσ₀ : 0 ≤ σ₀) (hτ₀ : 0 < τ₀) (h0 : σ₀ ≤ c.re - (r + R)) (h1 : c.re + (r + R) ≤ σ₁)
    (hT : c.im + (r + R) ≤ τ) (hT0 : τ₀ ≤ c.im - (r + R))
    (hG : Gsup M K σ₀ σ₁ τ τ₀ ≤ C) (hz : z ∈ closedBall c r) :
    ‖deriv (deriv (GEM M K)) z‖ ≤ 2 * C / R ^ 2 := by
  have hsub : closedBall z R ⊆ closedBall c (r + R) := by
    apply closedBall_subset_closedBall'
    have := mem_closedBall.1 hz
    linarith
  have hcr : r + R < c.im := by linarith
  refine norm_deriv2_GEM_le M K hR (fun w hw => ne_one_of_memG hcr (hsub hw)) (fun w hw => ?_)
  obtain ⟨b1, b2, b3, b4⟩ := box_of_memG (hsub (sphere_subset_closedBall hw))
  have hT' : |w.im| ≤ τ := by rw [abs_le]; constructor <;> linarith
  have hT0' : τ₀ ≤ |w.im| := by rw [abs_of_pos (by linarith)]; linarith
  exact (norm_GEM_le M K hσ₀ hτ₀ (by linarith) (by linarith) hT' hT0').trans hG

/-- **The second-derivative bound on a ball**: `‖DEM″ + GEM″‖ ≤ d₂ + 2C/R²` on `closedBall c r`, from
`D2sum σd M ≤ d₂` (`σd ≤ Re c − r`) and `Gsup ≤ C` on the box of `closedBall c (r + R)`. -/
theorem norm_deriv2_fEM_ballG (M K : ℕ) {c z : ℂ} {r R σd σ₀ σ₁ τ τ₀ C d₂ : ℝ}
    (hσd : σd ≤ c.re - r) (hD : D2sum σd M ≤ d₂) (hR : 0 < R)
    (hσ₀ : 0 ≤ σ₀) (hτ₀ : 0 < τ₀) (h0 : σ₀ ≤ c.re - (r + R)) (h1 : c.re + (r + R) ≤ σ₁)
    (hT : c.im + (r + R) ≤ τ) (hT0 : τ₀ ≤ c.im - (r + R))
    (hG : Gsup M K σ₀ σ₁ τ τ₀ ≤ C) (hz : z ∈ closedBall c r) :
    ‖DEMk 2 M z + deriv (deriv (GEM M K)) z‖ ≤ d₂ + 2 * C / R ^ 2 := by
  refine (norm_add_le _ _).trans (add_le_add ((norm_DEMk_two_le M ?_).trans hD)
    (norm_deriv2_GEM_ballG M K hR hσ₀ hτ₀ h0 h1 hT hT0 hG hz))
  linarith [(box_of_memG hz).1]

/-- One term of `D2sum σ M`: `log² n · n^{-σ} ≤ c` from `log n ≤ hi`, `n^{-σ} ≤ y`, `hi² y ≤ c`. -/
theorem D2term_leG {σ : ℝ} {n : ℕ} (hn : 1 ≤ n) {hi y c : ℝ} (hl : Real.log n ≤ hi)
    (he : ex σ n ≤ y) (hc : hi ^ 2 * y ≤ c) :
    Real.log n ^ 2 * ex σ n ≤ c := by
  have h0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hx : 0 ≤ ex σ n := (Real.exp_pos _).le
  calc Real.log n ^ 2 * ex σ n ≤ hi ^ 2 * y :=
        mul_le_mul (pow_le_pow_left₀ h0 hl 2) he hx (by nlinarith)
    _ ≤ c := hc

/-! ## 5. The elementary forms at a general centre

At `c = σ + it`: `n^{-c} = e_n (C_n − i S_n)` with `e_n = exp(−σ log n)` (`ex`),
`C_n = cos(t log n)` (`cCG`), `S_n = sin(t log n)` (`sCG`) (`nps_G`). -/

/-- `cos(t log n)`, `t = Im c`. -/
def cCG (c : ℂ) (n : ℕ) : ℝ := Real.cos (c.im * Real.log n)

/-- `sin(t log n)`, `t = Im c`. -/
def sCG (c : ℂ) (n : ℕ) : ℝ := Real.sin (c.im * Real.log n)

theorem ex_oneG (σ : ℝ) : ex σ 1 = 1 := by simp [ex]

theorem cCG_one (c : ℂ) : cCG c 1 = 1 := by simp [cCG]

theorem sCG_one (c : ℂ) : sCG c 1 = 0 := by simp [sCG]

theorem nps_G (c : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (nps n c).re = ex c.re n * cCG c n ∧ (nps n c).im = -(ex c.re n * sCG c n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have e : nps n c = Complex.exp ((Real.log n : ℂ) * (-c)) := by
    rw [nps, cpow_def_of_ne_zero hn0, ← natCast_log]
  have hre : ((Real.log n : ℂ) * (-c)).re = -(c.re * Real.log n) := by
    rw [Complex.re_ofReal_mul, Complex.neg_re]; ring
  have him : ((Real.log n : ℂ) * (-c)).im = -(c.im * Real.log n) := by
    rw [Complex.im_ofReal_mul, Complex.neg_im]; ring
  rw [e, Complex.exp_re, Complex.exp_im, hre, him, Real.cos_neg, Real.sin_neg, ex, cCG, sCG]
  constructor <;> ring

/-- `Re fEM(c)`, elementary. -/
def PReG (c : ℂ) (M K : ℕ) : ℝ :=
  (∑ m ∈ Finset.range M, (ex c.re (5 * m + 1) * cCG c (5 * m + 1)
      + kappa * (ex c.re (5 * m + 2) * cCG c (5 * m + 2))
      - kappa * (ex c.re (5 * m + 3) * cCG c (5 * m + 3))
      - ex c.re (5 * m + 4) * cCG c (5 * m + 4))) +
    (ex c.re (5 * M + 1) * (cCG c (5 * M + 1) * (QEM K (M + 1 / 5) c).re
        + sCG c (5 * M + 1) * (QEM K (M + 1 / 5) c).im)
      + kappa * (ex c.re (5 * M + 2) * (cCG c (5 * M + 2) * (QEM K (M + 2 / 5) c).re
        + sCG c (5 * M + 2) * (QEM K (M + 2 / 5) c).im))
      - kappa * (ex c.re (5 * M + 3) * (cCG c (5 * M + 3) * (QEM K (M + 3 / 5) c).re
        + sCG c (5 * M + 3) * (QEM K (M + 3 / 5) c).im))
      - ex c.re (5 * M + 4) * (cCG c (5 * M + 4) * (QEM K (M + 4 / 5) c).re
        + sCG c (5 * M + 4) * (QEM K (M + 4 / 5) c).im))

/-- `Im fEM(c)`, elementary. -/
def PImG (c : ℂ) (M K : ℕ) : ℝ :=
  -(∑ m ∈ Finset.range M, (ex c.re (5 * m + 1) * sCG c (5 * m + 1)
      + kappa * (ex c.re (5 * m + 2) * sCG c (5 * m + 2))
      - kappa * (ex c.re (5 * m + 3) * sCG c (5 * m + 3))
      - ex c.re (5 * m + 4) * sCG c (5 * m + 4))) +
    (ex c.re (5 * M + 1) * (cCG c (5 * M + 1) * (QEM K (M + 1 / 5) c).im
        - sCG c (5 * M + 1) * (QEM K (M + 1 / 5) c).re)
      + kappa * (ex c.re (5 * M + 2) * (cCG c (5 * M + 2) * (QEM K (M + 2 / 5) c).im
        - sCG c (5 * M + 2) * (QEM K (M + 2 / 5) c).re))
      - kappa * (ex c.re (5 * M + 3) * (cCG c (5 * M + 3) * (QEM K (M + 3 / 5) c).im
        - sCG c (5 * M + 3) * (QEM K (M + 3 / 5) c).re))
      - ex c.re (5 * M + 4) * (cCG c (5 * M + 4) * (QEM K (M + 4 / 5) c).im
        - sCG c (5 * M + 4) * (QEM K (M + 4 / 5) c).re))

/-- The `Q`-combination of the derivative at `c`: `Q′_x(c) − log N · Q_x(c)`. -/
def QDG (c : ℂ) (K : ℕ) (x : ℝ) (N : ℕ) : ℂ := QEMd K x c - (Real.log N : ℂ) * QEM K x c

/-- `Re fEM′(c)`, elementary. -/
def AReG (c : ℂ) (M K : ℕ) : ℝ :=
  -(∑ m ∈ Finset.range M, (Real.log (5 * m + 1 : ℕ) * (ex c.re (5 * m + 1) * cCG c (5 * m + 1))
      + kappa * (Real.log (5 * m + 2 : ℕ) * (ex c.re (5 * m + 2) * cCG c (5 * m + 2)))
      - kappa * (Real.log (5 * m + 3 : ℕ) * (ex c.re (5 * m + 3) * cCG c (5 * m + 3)))
      - Real.log (5 * m + 4 : ℕ) * (ex c.re (5 * m + 4) * cCG c (5 * m + 4)))) +
    (ex c.re (5 * M + 1) * (cCG c (5 * M + 1) * (QDG c K (M + 1 / 5) (5 * M + 1)).re
        + sCG c (5 * M + 1) * (QDG c K (M + 1 / 5) (5 * M + 1)).im)
      + kappa * (ex c.re (5 * M + 2) * (cCG c (5 * M + 2) * (QDG c K (M + 2 / 5) (5 * M + 2)).re
        + sCG c (5 * M + 2) * (QDG c K (M + 2 / 5) (5 * M + 2)).im))
      - kappa * (ex c.re (5 * M + 3) * (cCG c (5 * M + 3) * (QDG c K (M + 3 / 5) (5 * M + 3)).re
        + sCG c (5 * M + 3) * (QDG c K (M + 3 / 5) (5 * M + 3)).im))
      - ex c.re (5 * M + 4) * (cCG c (5 * M + 4) * (QDG c K (M + 4 / 5) (5 * M + 4)).re
        + sCG c (5 * M + 4) * (QDG c K (M + 4 / 5) (5 * M + 4)).im))

/-- `Im fEM′(c)`, elementary. -/
def AImG (c : ℂ) (M K : ℕ) : ℝ :=
  (∑ m ∈ Finset.range M, (Real.log (5 * m + 1 : ℕ) * (ex c.re (5 * m + 1) * sCG c (5 * m + 1))
      + kappa * (Real.log (5 * m + 2 : ℕ) * (ex c.re (5 * m + 2) * sCG c (5 * m + 2)))
      - kappa * (Real.log (5 * m + 3 : ℕ) * (ex c.re (5 * m + 3) * sCG c (5 * m + 3)))
      - Real.log (5 * m + 4 : ℕ) * (ex c.re (5 * m + 4) * sCG c (5 * m + 4)))) +
    (ex c.re (5 * M + 1) * (cCG c (5 * M + 1) * (QDG c K (M + 1 / 5) (5 * M + 1)).im
        - sCG c (5 * M + 1) * (QDG c K (M + 1 / 5) (5 * M + 1)).re)
      + kappa * (ex c.re (5 * M + 2) * (cCG c (5 * M + 2) * (QDG c K (M + 2 / 5) (5 * M + 2)).im
        - sCG c (5 * M + 2) * (QDG c K (M + 2 / 5) (5 * M + 2)).re))
      - kappa * (ex c.re (5 * M + 3) * (cCG c (5 * M + 3) * (QDG c K (M + 3 / 5) (5 * M + 3)).im
        - sCG c (5 * M + 3) * (QDG c K (M + 3 / 5) (5 * M + 3)).re))
      - ex c.re (5 * M + 4) * (cCG c (5 * M + 4) * (QDG c K (M + 4 / 5) (5 * M + 4)).im
        - sCG c (5 * M + 4) * (QDG c K (M + 4 / 5) (5 * M + 4)).re))

theorem re_npsMulG (c : ℂ) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (nps n c * z).re = ex c.re n * (cCG c n * z.re + sCG c n * z.im) := by
  obtain ⟨h1, h2⟩ := nps_G c hn
  rw [Complex.mul_re, h1, h2]; ring

theorem im_npsMulG (c : ℂ) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (nps n c * z).im = ex c.re n * (cCG c n * z.im - sCG c n * z.re) := by
  obtain ⟨h1, h2⟩ := nps_G c hn
  rw [Complex.mul_im, h1, h2]; ring

theorem fEM_reG (c : ℂ) (M K : ℕ) : (fEM M K c).re = PReG c M K := by
  unfold fEM DEM GEM PReG
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul]
  rw [re_npsMulG c (by omega), re_npsMulG c (by omega), re_npsMulG c (by omega),
    re_npsMulG c (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [(nps_G c (n := 5 * m + 1) (by omega)).1, (nps_G c (n := 5 * m + 2) (by omega)).1,
    (nps_G c (n := 5 * m + 3) (by omega)).1, (nps_G c (n := 5 * m + 4) (by omega)).1]

theorem fEM_imG (c : ℂ) (M K : ℕ) : (fEM M K c).im = PImG c M K := by
  unfold fEM DEM GEM PImG
  simp only [Complex.add_im, Complex.sub_im, Complex.im_sum, Complex.im_ofReal_mul]
  rw [im_npsMulG c (by omega), im_npsMulG c (by omega), im_npsMulG c (by omega),
    im_npsMulG c (by omega)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [(nps_G c (n := 5 * m + 1) (by omega)).2, (nps_G c (n := 5 * m + 2) (by omega)).2,
    (nps_G c (n := 5 * m + 3) (by omega)).2, (nps_G c (n := 5 * m + 4) (by omega)).2]
  ring

theorem GEMd_termG (c : ℂ) (M K j : ℕ) (x : ℝ) :
    npsD 1 (5 * M + j) c * QEM K x c + nps (5 * M + j) c * QEMd K x c =
      nps (5 * M + j) c * QDG c K x (5 * M + j) := by
  rw [npsD_one, QDG]; ring

theorem fEMd_reG (c : ℂ) (M K : ℕ) : (DEMk 1 M c + GEMd M K c).re = AReG c M K := by
  unfold DEMk GEMd AReG
  rw [GEMd_termG, GEMd_termG, GEMd_termG, GEMd_termG]
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul]
  rw [re_npsMulG c (by omega), re_npsMulG c (by omega), re_npsMulG c (by omega),
    re_npsMulG c (by omega)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [npsD_one, Complex.neg_re, Complex.re_ofReal_mul, neg_mul]
  rw [(nps_G c (n := 5 * m + 1) (by omega)).1, (nps_G c (n := 5 * m + 2) (by omega)).1,
    (nps_G c (n := 5 * m + 3) (by omega)).1, (nps_G c (n := 5 * m + 4) (by omega)).1]
  ring

theorem fEMd_imG (c : ℂ) (M K : ℕ) : (DEMk 1 M c + GEMd M K c).im = AImG c M K := by
  unfold DEMk GEMd AImG
  rw [GEMd_termG, GEMd_termG, GEMd_termG, GEMd_termG]
  simp only [Complex.add_im, Complex.sub_im, Complex.im_sum, Complex.im_ofReal_mul]
  rw [im_npsMulG c (by omega), im_npsMulG c (by omega), im_npsMulG c (by omega),
    im_npsMulG c (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [npsD_one, Complex.neg_im, Complex.im_ofReal_mul, neg_mul]
  rw [(nps_G c (n := 5 * m + 1) (by omega)).2, (nps_G c (n := 5 * m + 2) (by omega)).2,
    (nps_G c (n := 5 * m + 3) (by omega)).2, (nps_G c (n := 5 * m + 4) (by omega)).2]
  ring

theorem QDG_re (c : ℂ) (K : ℕ) (x : ℝ) (N : ℕ) :
    (QDG c K x N).re = (QEMd K x c).re - Real.log N * (QEM K x c).re := by
  rw [QDG, Complex.sub_re, Complex.re_ofReal_mul]

theorem QDG_im (c : ℂ) (K : ℕ) (x : ℝ) (N : ℕ) :
    (QDG c K x N).im = (QEMd K x c).im - Real.log N * (QEM K x c).im := by
  rw [QDG, Complex.sub_im, Complex.im_ofReal_mul]

/-- **The ladder in elementary form** at a general centre: three point values at `c` (`PReG`, `PImG`,
`AReG`), the ball-uniform bounds `hM2`, `hE`, and the margin. -/
theorem dh_zero_near_of_elementaryG {c : ℂ} {r pr pi ar m₂ e₀ : ℝ} {M K : ℕ} (hr : 0 < r)
    (hcr : r < c.im) (hPr : |PReG c M K| ≤ pr) (hPi : |PImG c M K| ≤ pi)
    (hAr : ar ≤ |AReG c M K|)
    (hM2 : ∀ z ∈ closedBall c r, ‖DEMk 2 M z + deriv (deriv (GEM M K)) z‖ ≤ m₂)
    (hE : ∀ z ∈ closedBall c r, ‖dh z - dhEM M K z‖ ≤ ‖aDH chi5 1‖ * e₀)
    (hmargin : 2 * (pr + pi + e₀) < ar * r - m₂ * r ^ 2) :
    ∃ ρ, dh ρ = 0 ∧ ‖ρ - c‖ < r := by
  refine dh_zero_near_of_fEMG (p₀ := pr + pi) (a₀ := ar) hr hcr ?_ ?_ hM2 hE (by linarith)
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [fEM_reG, fEM_imG]
    linarith
  · refine hAr.trans ?_
    rw [← fEMd_reG]
    exact Complex.abs_re_le_norm _

/-! ## 6. Interval helpers -/

theorem kappaBG : (284079043840412 / 1000000000000000 : ℝ) ≤ kappa ∧
    kappa ≤ (284079043840413 / 1000000000000000 : ℝ) := by
  have h := PsiOmega.kappa_bounds
  constructor <;> linarith [h.1, h.2]

/-- `|x| ≤ t` from an enclosure. -/
theorem abs_le_of_mem {x lo hi t : ℝ} (h : lo ≤ x ∧ x ≤ hi) (h1 : -t ≤ lo) (h2 : hi ≤ t) :
    |x| ≤ t := by
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

end Locate

end PsiOmega

#print axioms PsiOmega.Locate.dh_zero_near_of_fEMG
#print axioms PsiOmega.Locate.norm_dh_sub_dhEM_le_ballG
#print axioms PsiOmega.Locate.norm_deriv2_fEM_ballG
#print axioms PsiOmega.Locate.dh_zero_near_of_elementaryG
