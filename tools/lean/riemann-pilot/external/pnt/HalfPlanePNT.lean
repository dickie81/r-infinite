/-
# Round 337: a zero-free half-plane gives a power saving in the prime number theorem

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If `ζ(s) ≠ 0` for `Re s > θ`, `θ < 1`, then `ψ(x) − x = O(x^{θ+ε})` for every `ε > 0`
(`psi_isBigO_of_zeroFree`). Under round 278's `SmoothBound θ` and under the completed mean square of round
326 (`Re s > 11/12`) this gives `O(x^{θ+ε})` and `O(x^{11/12+ε})`.

* `riemannZeta_linear_growth`: `|ζ(s)| ≤ (5/2 + 1/δ)|Im s|` for `Re s ≥ δ > 0`, `|Im s| ≥ 1`, from PNT+'s
  Euler–Maclaurin formula.
* `logDeriv_le_of_zeroFree`: under a zero-free half-plane `Re s > θ ≥ 0`, `|ζ'/ζ(σ + it)| ≤ C log|t|` on
  `σ ≥ θ'`, `|t| > 3`, for every `θ' > θ`. Left of `3/2` this is PNT+'s `FinalBound` (Borel–Carathéodory with
  the zeros divided out) on the disc of radius `3/2 − θ` around `3/2 + it`, which holds no zero, with radii
  fixed by `θ'` (`disc_point`); right of `3/2`, PNT+'s `LogDerivZetaBdd_of_Re_ge_three_halves`. *(Round 513: the
  disc step is `LogDerivDisc.logDeriv_le_Kld` at `F = ζ`, which is holomorphic on the disc of radius `2(3/2 − θ)`
  when `|t| > 3` (`differentiableOn_zeta_ball`). This file's `disc_point` for `ζ` and its helpers `ctr_pole`,
  `ctr_ne_zero` and `locF_logDeriv` are removed, and `ctr`, `re_ge` and `one_lt_log_three` moved to
  `LogDerivDisc.lean`: STRUCTURAL-REVIEW §9.3, U4.)*
* `psi_isBigO_of_zeroFree`: `MediumPNTW.GenPNTWNoEps` at the constant depth `1 − θ'`.

Round 338: the exponent is the classical `θ + ε`. Round 337 had `(1+θ)/2 + ε`: through `MediumPNTW.GenPNTW'`
the segments left of `Re s = 1` cost `x^{θ'}/ε` (PNT+'s bounds, through `MellinOfSmooth1b`) against `εx` for
the smoothing, and the two balanced at `ε = x^{−(1−θ')/2}`. Through `GenPNTWNoEps` they cost
`x^{θ'} (log x)²`, so the smoothing width can be `x^{θ'−1}`.
-/
import MediumPNTW
import Landau
import LogDerivDisc
import HalfPlaneS0
import EisensteinTransferEstimate

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

namespace HalfPlanePNT

open LogDerivDisc

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

/-- `ζ` is holomorphic on the disc of radius `2ρ ≤ 3` around `3/2 + it`, `|t| > 3`: the disc misses `1`. -/
lemma differentiableOn_zeta_ball {t ρ : ℝ} (ht : 3 < |t|) (hρ32 : ρ ≤ 3 / 2) :
    DifferentiableOn ℂ riemannZeta (Metric.ball (ctr t) (2 * ρ)) := by
  intro s hs
  refine (differentiableAt_riemannZeta fun h => ?_).differentiableWithinAt
  rw [h, Metric.mem_ball, dist_eq_norm] at hs
  have him := Complex.abs_im_le_norm (1 - ctr t)
  rw [sub_im, one_im, ctr_im, zero_sub, abs_neg] at him
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

/-- **The log-derivative under a zero-free half-plane.** If `ζ(s) ≠ 0` for `Re s > θ ≥ 0`, then for every
`θ' ∈ (θ, 3/2)` there is `C` with `|ζ'/ζ(σ + it)| ≤ C log|t|` for `σ ≥ θ'`, `|t| > 3`. -/
theorem logDeriv_le_of_zeroFree {θ θ' : ℝ} (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'32 : θ' < 3 / 2)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 3 < |t| → θ' ≤ σ →
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  set ρ : ℝ := 3 / 2 - θ with hρdef
  have hρ : 0 < ρ := by linarith
  have hρ32 : ρ ≤ 3 / 2 := by linarith
  set R : ℝ := Rld θ θ' with hRdef
  have hR1 : R < 1 := Rld_lt_one hθθ' hθ'32
  set K : ℝ := Kld θ θ' with hKdef
  have hK : 0 < K := Kld_pos hθθ' hθ'32
  have hδ : 0 < 3 / 2 - ρ * R := by
    have : ρ * R < ρ := mul_lt_of_lt_one_right hρ hR1
    linarith
  set c : ℝ := (5 / 2 + (3 / 2 - ρ * R)⁻¹) * ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ with hcdef
  have hc : 0 ≤ c := by positivity
  set L : ℝ := Real.log (2 * (1 + c)) + 1 with hLdef
  have hL : 0 < L := by
    have : 0 ≤ Real.log (2 * (1 + c)) := Real.log_nonneg (by linarith)
    linarith
  obtain ⟨C₂, hC₂⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  refine ⟨max |C₂| (K * L) + 1, by positivity, fun σ t ht hσ => ?_⟩
  have hlt : 1 < Real.log |t| :=
    lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) ht.le)
  have hC1 : |C₂| ≤ max |C₂| (K * L) + 1 := by
    have := le_max_left |C₂| (K * L); linarith
  have hC2 : K * L ≤ max |C₂| (K * L) + 1 := by
    have := le_max_right |C₂| (K * L); linarith
  by_cases h32 : 3 / 2 ≤ σ
  · have h := hC₂ (σ + t * I) (by simpa using h32)
    calc ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ |C₂| := h.trans (le_abs_self _)
      _ ≤ |C₂| * Real.log |t| := le_mul_of_one_le_right (abs_nonneg _) hlt.le
      _ ≤ (max |C₂| (K * L) + 1) * Real.log |t| := by gcongr
  push Not at h32
  have hB : 1 < 2 + c * (|t| + ρ) := by
    have : 0 ≤ c * (|t| + ρ) := mul_nonneg hc (by positivity)
    linarith
  have hfb : ∀ w : ℂ, ‖w‖ ≤ R → ‖locG riemannZeta (ctr t) ρ w‖ ≤ 2 + c * (|t| + ρ) := by
    intro w hw
    have h := locF_bound ht hρ hρ32 hR1 hδ hw
    have : c * (|t| + ρ) ≤ 2 + c * (|t| + ρ) := by linarith
    exact h.trans this
  have FB := logDeriv_le_Kld hθθ' hσ h32 (differentiableOn_zeta_ball ht hρ32) hzf hB hfb
  have hlogB : Real.log (2 + c * (|t| + ρ)) ≤ L * Real.log |t| := by
    have hB2 : 2 + c * (|t| + ρ) ≤ 2 * (1 + c) * |t| := by
      have : c * (|t| + ρ) ≤ c * (|t| + 2) := mul_le_mul_of_nonneg_left (by linarith) hc
      have : c * (|t| + 2) ≤ c * (2 * |t|) := mul_le_mul_of_nonneg_left (by linarith) hc
      have : 2 ≤ 2 * |t| := by linarith
      linarith
    have hl0 : 0 ≤ Real.log (2 * (1 + c)) := Real.log_nonneg (by linarith)
    calc Real.log (2 + c * (|t| + ρ)) ≤ Real.log (2 * (1 + c) * |t|) := Real.log_le_log (by linarith) hB2
      _ = Real.log (2 * (1 + c)) + Real.log |t| := by
          rw [Real.log_mul (by positivity) (by positivity)]
      _ ≤ Real.log (2 * (1 + c)) * Real.log |t| + Real.log |t| := by
          have := mul_le_mul_of_nonneg_left hlt.le hl0; linarith
      _ = L * Real.log |t| := by simp only [hLdef]; ring
  calc ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖
      ≤ K * Real.log (2 + c * (|t| + ρ)) := FB
    _ ≤ K * (L * Real.log |t|) := mul_le_mul_of_nonneg_left hlogB hK.le
    _ = K * L * Real.log |t| := by ring
    _ ≤ (max |C₂| (K * L) + 1) * Real.log |t| := by gcongr

/-- A zero-free half-plane `Re s > θ` has `θ ≥ ½`: ζ has a zero with real part at least `½`
(`PsiOmega.exists_zero_re_ge_half`). -/
theorem half_le_of_zeroFree {θ : ℝ} (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) : 1 / 2 ≤ θ := by
  by_contra h
  obtain ⟨ρ, hρ, hre⟩ := PsiOmega.exists_zero_re_ge_half
  exact hzf ρ (by linarith) hρ

section PNT

open scoped Chebyshev

open MediumPNTW

/-- **A zero-free half-plane gives a power saving in the prime number theorem.** If `ζ(s) ≠ 0` for
`Re s > β` with `β < 1`, then `ψ(x) − x = O(x^{β+ε})` for every `ε > 0`. `GenPNTWNoEps` at the constant depth
`1 − β'`, `β' = β + min(ε/2, (1 − β)/2)`, with `T = x`, smoothing width `x^{β'−1}` and the bound of
`logDeriv_le_of_zeroFree`. (`β` for the abscissa: `θ` is Chebyshev's function here.) -/
theorem psi_isBigO_of_zeroFree {β : ℝ} (hβ1 : β < 1) (hzf : ∀ s : ℂ, β < s.re → ζ s ≠ 0) {ε : ℝ}
    (hε : 0 < ε) : (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ (β + ε) := by
  have hβ := half_le_of_zeroFree hzf
  set η : ℝ := min (ε / 2) ((1 - β) / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η ≤ ε / 2 := min_le_left _ _
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
  set a : ℝ := 1 - β' with hadef
  have ha : 0 < a := by linarith
  set b : ℝ := ε / 4 with hbdef
  have hb0 : 0 < b := by linarith
  -- `log x ≤ x^b` eventually
  have hlog : ∀ᶠ x in atTop, Real.log x ≤ x ^ b := by
    have h := (isLittleO_log_rpow_atTop hb0).bound one_pos
    filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
    rw [one_mul, Real.norm_of_nonneg (Real.log_nonneg hx1.le),
      Real.norm_of_nonneg (by positivity)] at hx
    exact hx
  have key := GenPNTWNoEps hD one_pos hC hb holo (fun x ↦ x) (fun x ↦ x ^ (-a))
    (fun x ↦ x ^ (-a + 2 * b))
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
      filter_upwards [hlog, eventually_gt_atTop 1] with x hx hx1
      have hx0 : 0 < x := by linarith
      calc x ^ (-a) * Real.log x ≤ x ^ (-a) * x ^ b := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = x ^ (-a + b) := (Real.rpow_add hx0 _ _).symm
        _ ≤ x ^ (-a + 2 * b) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
    (by -- `log x/(ε T) ≤ F`
      filter_upwards [hlog, eventually_gt_atTop 1] with x hx hx1
      have hx0 : 0 < x := by linarith
      have e : x ^ (-a) * x = x ^ (1 - a) := by
        rw [mul_comm, sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
      rw [e, div_le_iff₀ (by positivity), ← Real.rpow_add hx0]
      calc Real.log x ≤ x ^ b := hx
        _ ≤ x ^ (-a + 2 * b + (1 - a)) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
    (by -- `x^{−D} (log T)² ≤ F`
      filter_upwards [hlog, eventually_gt_atTop 1] with x hx hx1
      have hx0 : 0 < x := by linarith
      have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
      show x ^ (-a) * Real.log x ^ ((1 : ℝ) + 1) ≤ x ^ (-a + 2 * b)
      rw [Real.rpow_add_one (Real.log_pos hx1).ne' 1, Real.rpow_one]
      calc x ^ (-a) * (Real.log x * Real.log x) ≤ x ^ (-a) * (x ^ b * x ^ b) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hx hx hl0 (by positivity)) (by positivity)
        _ = x ^ (-a + 2 * b) := by
            rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
            ring_nf)
    (by -- `x^{σ₂−1} ≤ F`
      filter_upwards [eventually_gt_atTop 1] with x hx1
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [hadef, hσ₂def, hβ'def]; linarith))
  refine key.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 1] with x hx1
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
  rw [show x * x ^ (-a + 2 * b) = x ^ (1 + (-a + 2 * b)) by
    rw [Real.rpow_add hx0 1 (-a + 2 * b), Real.rpow_one]]
  exact Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [hadef, hbdef, hβ'def]; linarith)

/-- Under round 278's `SmoothBound β`, `β < 1`: `ψ(x) − x = O(x^{β+ε})`. -/
theorem psi_isBigO_of_smoothBound {β : ℝ} (h : HalfPlaneS0.SmoothBound β) (hβ1 : β < 1) {ε : ℝ}
    (hε : 0 < ε) : (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ (β + ε) :=
  psi_isBigO_of_zeroFree hβ1 (fun _ hs ↦ (HalfPlaneS0.ne_zero_of_smoothBound h hs).1) hε

/-- Under the completed mean square (`Eis.CompletedMeanSquare`, the companion paper's Proposition 5.2), which
gives `ζ(s) ≠ 0` on `Re s > 11/12` (round 326): `ψ(x) − x = O(x^{11/12+ε})`. -/
theorem psi_isBigO_of_completed (hC : Eis.CompletedMeanSquare) {ε : ℝ} (hε : 0 < ε) :
    (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ ((11 : ℝ) / 12 + ε) :=
  psi_isBigO_of_zeroFree (by norm_num) (fun _ hs ↦ (Eis.ne_zero_of_completed hC hs).1) hε

end PNT

end HalfPlanePNT

#print axioms HalfPlanePNT.riemannZeta_linear_growth
#print axioms HalfPlanePNT.logDeriv_le_of_zeroFree
#print axioms HalfPlanePNT.half_le_of_zeroFree
#print axioms HalfPlanePNT.psi_isBigO_of_zeroFree
#print axioms HalfPlanePNT.psi_isBigO_of_smoothBound
#print axioms HalfPlanePNT.psi_isBigO_of_completed
