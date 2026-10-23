import Mathlib
import StripShift
import WeilCount

/-! # Weil's explicit formula, assembled (round 156, part 4)

The line integral `Z = ∫_ℝ h(r − i) Ξ′/Ξ(r − i) dr` is computed twice.

* **Zero side** (`zero_side`): Hadamard's `Ξ′/Ξ = Σ_u (1/(t − τ_u) + 1/(t + τ_u))`, integrated termwise
  (`Σ_u ∫|·| < ∞` by `kernel_integral_le` and `summable_Xi_zeros_rpow`), each pair giving `2πi h(τ_u)`
  (`pole_pair`).
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open PilotWeil

/-- A square root `τ` of the zero `u` of `Ξ(√w)`: a zero of `Ξ`. -/
def tau (i : ZeroIdx (sqF Xi)) : ℂ := i.1 ^ ((2 : ℂ)⁻¹)

theorem tau_sq (i : ZeroIdx (sqF Xi)) : tau i ^ 2 = i.1 := sqrt_sq' i.1

theorem Xi_tau (i : ZeroIdx (sqF Xi)) : Xi (tau i) = 0 :=
  (ordN_ne_zero_iff (sqF_differentiable differentiable_Xi Xi_even)
    (by rw [sqF_zero]; exact Xi_zero_ne_zero) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))

theorem tau_im (i : ZeroIdx (sqF Xi)) : |(tau i).im| < 1 / 2 := Xi_zero_im (Xi_tau i)

theorem norm_tau (i : ZeroIdx (sqF Xi)) : ‖tau i‖ = ‖i.1‖ ^ (2⁻¹ : ℝ) := by
  unfold tau
  rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]

instance : Countable (ZeroIdx (sqF Xi)) := by
  have hs : Summable fun i : ZeroIdx (sqF Xi) => ‖i.1⁻¹‖ :=
    (hadamardW_Xi xiGrowth Xi_zero_ne_zero).summ
  have hc := hs.countable_support
  have e : Function.support (fun i : ZeroIdx (sqF Xi) => ‖i.1⁻¹‖) = univ := by
    ext i; simp [ZeroIdx_ne_zero i]
  rw [e] at hc
  exact Set.countable_univ_iff.1 hc

theorem Xi_line_ne_zero (r : ℝ) : Xi ((r : ℂ) - I) ≠ 0 := by
  intro h
  have := Xi_zero_im h
  simp at this; norm_num at this

theorem summable_kernel_norms {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Summable fun i : ZeroIdx (sqF Xi) =>
      ∫ r : ℝ, ‖h (r - I) * (1 / ((r : ℂ) - I - tau i) + 1 / ((r : ℂ) - I + tau i))‖ := by
  refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun r => norm_nonneg _)
    (fun i => ?_) (summable_Xi_zeros_rpow.mul_left (600 * C * ∫ x, om x))
  refine (kernel_integral_le H (tau_im i).le).trans ?_
  have hK : 0 ≤ 600 * C * ∫ x, om x :=
    mul_nonneg (by linarith [H.C_nonneg]) (integral_nonneg om_nonneg)
  apply mul_le_mul_of_nonneg_left _ hK
  have hu : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdx_ne_zero i)
  have ht : 0 < ‖tau i‖ := by rw [norm_tau]; positivity
  calc (1 + ‖tau i‖) ^ (-(7 / 4 : ℝ)) ≤ ‖tau i‖ ^ (-(7 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
    _ = (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
        rw [norm_tau, ← Real.rpow_mul hu.le, ← Real.rpow_neg hu.le]; norm_num

theorem kernel_eq (i : ZeroIdx (sqF Xi)) (r : ℝ) :
    2 * ((r : ℂ) - I) / (((r : ℂ) - I) ^ 2 - i.1)
      = 1 / ((r : ℂ) - I - tau i) + 1 / ((r : ℂ) - I + tau i) := by
  have him := tau_im i
  have h1 : (r : ℂ) - I - tau i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this
    rw [abs_lt] at him; linarith
  have h2 : (r : ℂ) - I + tau i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this
    rw [abs_lt] at him; linarith
  have h3 : ((r : ℂ) - I) ^ 2 - tau i ^ 2 ≠ 0 := by
    rw [show ((r : ℂ) - I) ^ 2 - tau i ^ 2 = ((r : ℂ) - I - tau i) * ((r : ℂ) - I + tau i) by ring]
    exact mul_ne_zero h1 h2
  rw [← tau_sq i]
  field_simp
  ring

/-- **The zero side**: `∫_ℝ h(r − i)Ξ′/Ξ(r − i) dr = Σ_u 2πi h(τ_u)`. -/
theorem zero_side {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t) :
    HasSum (fun i : ZeroIdx (sqF Xi) => 2 * π * I * h (tau i))
      (∫ r : ℝ, h (r - I) * logDeriv Xi (r - I)) := by
  set F : ZeroIdx (sqF Xi) → ℝ → ℂ := fun i r =>
    h (r - I) * (1 / ((r : ℂ) - I - tau i) + 1 / ((r : ℂ) - I + tau i))
  have hint : ∀ i, Integrable (F i) := fun i =>
    integrable_kernel H (by linarith [tau_im i])
  have H1 := hasSum_integral_of_summable_integral_norm hint (summable_kernel_norms H)
  have hval : ∀ i, ∫ r, F i r = 2 * π * I * h (tau i) := fun i =>
    pole_pair H heven (by linarith [tau_im i])
  simp_rw [hval] at H1
  convert H1 using 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hs := (hasSum_logDeriv_Xi (Xi_line_ne_zero r)).mul_left (h (r - I))
  simp only [kernel_eq] at hs
  exact hs.tsum_eq.symm


/-! ## The archimedean term -/

theorem abs_log_le {y : ℝ} (hy : 1 / 4 ≤ y) : |Real.log y| ≤ 2 * Real.sqrt y + 2 := by
  have hy0 : 0 < y := by linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have h1 : Real.log y ≤ 2 * Real.sqrt y := by
    have := Real.log_le_sub_one_of_pos hs
    have e : Real.log y = 2 * Real.log (Real.sqrt y) := by
      rw [← Real.log_rpow hs, Real.rpow_two, Real.sq_sqrt hy0.le]
    linarith
  have h2 : -Real.log y ≤ 2 := by
    have : Real.log (1 / 4) ≤ Real.log y := Real.log_le_log (by norm_num) hy
    have e : Real.log (1 / 4 : ℝ) = -Real.log 4 := by rw [one_div, Real.log_inv]
    have h4 : Real.log 4 < 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      have h2' : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9; linarith
    linarith
  rw [abs_le]; constructor <;> linarith [Real.sqrt_nonneg y]

/-- **`|ψ(z)| ≤ 12√(1 + |z|)`** for `1/4 ≤ Re z`, from `ψ = log z − 1/(2z) − L(z)` (round 155). -/
theorem norm_digamma_le {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    ‖Complex.digamma z‖ ≤ 12 * Real.sqrt (1 + ‖z‖) := by
  have hz0 : 0 < z.re := by linarith
  have hnz : 1 / 4 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  rw [PilotDigamma.digamma_eq_lap hz0]
  have hlog : ‖Complex.log z‖ ≤ 2 * Real.sqrt ‖z‖ + 2 + π := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    linarith [abs_log_le hnz, Complex.abs_arg_le_pi z]
  have hinv : ‖1 / (2 * z)‖ ≤ 2 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, div_le_iff₀ (by positivity)]; linarith
  have hlap : ‖PilotDigamma.lap z‖ ≤ 2 := by
    refine (PilotDigamma.norm_lap_le hz0).trans ?_
    rw [div_le_iff₀ (by positivity)]; linarith
  have hsq : Real.sqrt ‖z‖ ≤ Real.sqrt (1 + ‖z‖) := Real.sqrt_le_sqrt (by linarith)
  have hone : 1 ≤ Real.sqrt (1 + ‖z‖) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + ‖z‖ by linarith [norm_nonneg z])
    rwa [Real.sqrt_one] at this
  calc ‖Complex.log z - 1 / (2 * z) - PilotDigamma.lap z‖
      ≤ ‖Complex.log z‖ + ‖1 / (2 * z)‖ + ‖PilotDigamma.lap z‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_sub_le (Complex.log z) (1 / (2 * z))])
    _ ≤ 2 * Real.sqrt ‖z‖ + 2 + π + 2 + 2 := by linarith
    _ ≤ 12 * Real.sqrt (1 + ‖z‖) := by nlinarith [Real.pi_lt_four]

/-- `ψ(1/4 − ir/2) = ψ(1/4 + ir/2)‾`. -/
theorem digamma_zB_neg (r : ℝ) : Complex.digamma (zB (-r)) = (starRingEnd ℂ) (Complex.digamma (zB r)) := by
  have hconj : zB (-r) = (starRingEnd ℂ) (zB r) := by
    apply Complex.ext
    · rw [Complex.conj_re, zB_re, zB_re]
    · rw [Complex.conj_im, zB_im, zB_im]; ring
  have hnp : ∀ m : ℕ, zB r ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    rw [zB_re] at this
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [hconj, PilotDigamma.digamma_conj hnp]


/-- The archimedean integrand `f(t) = h(t)ψ((½ + it)/2)` on the strip `−1 ≤ Im t ≤ 0`. -/
theorem psi_strip_bound {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {t : ℂ} (ht : t ∈ strip (-1) 0) :
    ‖h t * Complex.digamma ((1 / 2 + I * t) / 2)‖ ≤ 48 * C * (1 + |t.re|) ^ (-(3 / 2 : ℝ)) := by
  have hC := H.C_nonneg
  obtain ⟨h1, h2⟩ := ht
  set x := t.re
  set z : ℂ := (1 / 2 + I * t) / 2
  have hzre : z.re = 1 / 4 - t.im / 2 := by simp [z]; ring
  have hz : 1 / 4 ≤ z.re := by rw [hzre]; linarith
  have hnz : ‖z‖ ≤ 1 + |x| := by
    have ht' : ‖t‖ ≤ |x| + 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im t).trans ?_
      have : |t.im| ≤ 1 := abs_le.2 ⟨h1, by linarith⟩
      linarith
    have : ‖z‖ ≤ (1 / 2 + ‖t‖) / 2 := by
      simp only [z, norm_div, Complex.norm_two]
      gcongr
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul]; norm_num
    linarith [abs_nonneg x]
  have hX : 0 < 1 + |x| := by positivity
  have hpsi : ‖Complex.digamma z‖ ≤ 24 * (1 + |x|) ^ (1 / 2 : ℝ) := by
    refine (norm_digamma_le hz).trans ?_
    have : Real.sqrt (1 + ‖z‖) ≤ 2 * (1 + |x|) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc (1 + ‖z‖) ^ (1 / 2 : ℝ) ≤ (4 * (1 + |x|)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg x]) (by norm_num)
        _ = 2 * (1 + |x|) ^ (1 / 2 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) hX.le]
            congr 1
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hh : ‖h t‖ ≤ 2 * C * (1 + |x|) ^ (-(2 : ℝ)) := by
    have := H.bound t ⟨h1, by linarith⟩
    refine this.trans ?_
    rw [Real.rpow_neg hX.le, div_le_iff₀ (by positivity)]
    have hsq : (1 + |x|) ^ (2 : ℝ) ≤ 2 * (1 + x ^ 2) := by
      rw [Real.rpow_two]; nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
    have hp : 0 < (1 + |x|) ^ (2 : ℝ) := by positivity
    calc C = 2 * C * ((1 + |x|) ^ (2 : ℝ))⁻¹ * ((1 + |x|) ^ (2 : ℝ) / 2) := by field_simp
      _ ≤ 2 * C * ((1 + |x|) ^ (2 : ℝ))⁻¹ * (1 + x ^ 2) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [norm_mul]
  calc ‖h t‖ * ‖Complex.digamma z‖ ≤ (2 * C * (1 + |x|) ^ (-(2 : ℝ))) * (24 * (1 + |x|) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hh hpsi (norm_nonneg _) (by positivity)
    _ = 48 * C * ((1 + |x|) ^ (-(2 : ℝ)) * (1 + |x|) ^ (1 / 2 : ℝ)) := by ring
    _ = 48 * C * (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hX]; norm_num

theorem psi_strip_diff {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    DifferentiableOn ℂ (fun t => h t * Complex.digamma ((1 / 2 + I * t) / 2)) (strip (-1) 0) := by
  refine (H.diff.mono (strip_mono le_rfl (by norm_num))).mul ?_
  refine PilotDigamma.differentiableOn_digamma.comp (Differentiable.differentiableOn (by fun_prop))
    fun t ht => ?_
  show 0 < ((1 / 2 + I * t) / 2).re
  have := ht.2
  simp; linarith

/-- **The archimedean term on the real line**:
`∫_ℝ h(r − i)ψ((½ + i(r − i))/2) dr = ∫_ℝ h(r)ψ(¼ + ir/2) dr`. -/
theorem psi_line {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    ∫ r : ℝ, h ((r : ℂ) - I) * Complex.digamma ((1 / 2 + I * ((r : ℂ) - I)) / 2)
      = ∫ r : ℝ, h r * Complex.digamma (zB r) := by
  have := strip_shift' (by norm_num : (-1 : ℝ) ≤ 0) (psi_strip_diff H)
    (fun t ht => psi_strip_bound H ht)
  calc ∫ r : ℝ, h ((r : ℂ) - I) * Complex.digamma ((1 / 2 + I * ((r : ℂ) - I)) / 2)
      = ∫ r : ℝ, h (↑r + ↑(-1 : ℝ) * I) * Complex.digamma ((1 / 2 + I * (↑r + ↑(-1 : ℝ) * I)) / 2) := by
        congr 1; funext r; push_cast; ring_nf
    _ = ∫ r : ℝ, h (↑r + ↑(0 : ℝ) * I) * Complex.digamma ((1 / 2 + I * (↑r + ↑(0 : ℝ) * I)) / 2) := this
    _ = _ := by congr 1; funext r; push_cast; unfold zB; ring_nf

theorem integrable_psi_real {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h r * Complex.digamma (zB r) := by
  have hmem : ∀ r : ℝ, (r : ℂ) ∈ strip (-1) 0 := fun r => by
    show -1 ≤ (r : ℂ).im ∧ (r : ℂ).im ≤ 0
    simp
  have hc : Continuous fun r : ℝ => h r * Complex.digamma ((1 / 2 + I * r) / 2) :=
    (psi_strip_diff H).continuousOn.comp_continuous (by fun_prop) hmem
  have e : (fun r : ℝ => h r * Complex.digamma (zB r))
      = fun r : ℝ => h r * Complex.digamma ((1 / 2 + I * r) / 2) := by
    funext r; unfold zB; ring_nf
  rw [e]
  refine (integrable_om32.const_mul (48 * C)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have := psi_strip_bound H (hmem r)
  simpa using this

/-- **The archimedean term is real**: `∫_ℝ h(r)ψ(¼ + ir/2) dr = ∫_ℝ h_ℝ(r) Re ψ(¼ + ir/2) dr`. -/
theorem psi_real {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    ∫ r : ℝ, h r * Complex.digamma (zB r) = ((∫ r : ℝ, hR r * psiRe r : ℝ) : ℂ) := by
  have hi := integrable_psi_real H
  have hRe : ∀ r : ℝ, hR (-r) = hR r := fun r => by
    have := heven r; rw [← Complex.ofReal_neg, hreal, hreal] at this; exact_mod_cast this
  rw [← integral_re_add_im hi]
  have hre : ∀ r : ℝ, RCLike.re (h r * Complex.digamma (zB r)) = hR r * psiRe r := fun r => by
    rw [hreal]; simp [psiRe]
  have him0 : ∫ r : ℝ, RCLike.im (h r * Complex.digamma (zB r)) = 0 := by
    set g : ℝ → ℝ := fun r => RCLike.im (h r * Complex.digamma (zB r))
    have hg : ∀ r, g (-r) = -g r := fun r => by
      simp only [g]
      rw [hreal, hreal, hRe, digamma_zB_neg]
      simp
    have := integral_neg_eq_self g volume
    simp_rw [hg, integral_neg] at this
    linarith
  simp_rw [hre]
  rw [him0]
  simp


/-! ## The kernel `F = 2πg_h` and the constant term -/

theorem hR_even {h : ℂ → ℂ} (heven : ∀ t, h (-t) = h t) {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r)
    (r : ℝ) : hR (-r) = hR r := by
  have := heven r; rw [← Complex.ofReal_neg, hreal, hreal] at this; exact_mod_cast this

theorem integrable_real_line {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h r := by
  have := integrable_line H.diff H.bound (y := 0) ⟨by norm_num, by norm_num⟩
  simpa using this

/-- **`F(x) = 2πg_h(x)`** for `h` even and real on `ℝ`. -/
theorem FK_eq_gh {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) (x : ℝ) :
    FK h x = ((2 * π * gh hR x : ℝ) : ℂ) := by
  have hi : Integrable fun r : ℝ => h r * Complex.exp (-(I * r * x)) := by
    have := integrable_line (H.mul_exp x).diff (H.mul_exp x).bound (y := 0) ⟨by norm_num, by norm_num⟩
    simpa using this
  unfold FK
  rw [← integral_re_add_im hi]
  have hre : ∀ r : ℝ, RCLike.re (h r * Complex.exp (-(I * r * x))) = hR r * Real.cos (r * x) := by
    intro r; rw [hreal]
    have e : -(I * (r : ℂ) * x) = ((-(r * x) : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    show (((hR r : ℝ) : ℂ) * Complex.exp (((-(r * x) : ℝ) : ℂ) * I)).re = _
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : ∫ r : ℝ, RCLike.im (h r * Complex.exp (-(I * r * x))) = 0 := by
    set g : ℝ → ℝ := fun r => RCLike.im (h r * Complex.exp (-(I * r * x)))
    have hg : ∀ r, g (-r) = -g r := fun r => by
      simp only [g]
      rw [hreal, hreal, hR_even heven hreal]
      have e1 : -(I * ((-r : ℝ) : ℂ) * x) = ((r * x : ℝ) : ℂ) * I := by push_cast; ring
      have e2 : -(I * (r : ℂ) * x) = ((-(r * x) : ℝ) : ℂ) * I := by push_cast; ring
      rw [e1, e2]
      show (((hR r : ℝ) : ℂ) * Complex.exp (((r * x : ℝ) : ℂ) * I)).im
        = -(((hR r : ℝ) : ℂ) * Complex.exp (((-(r * x) : ℝ) : ℂ) * I)).im
      rw [Complex.im_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
        Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      ring
    have := integral_neg_eq_self g volume
    simp_rw [hg, integral_neg] at this
    linarith
  simp_rw [hre]
  rw [him]
  unfold gh
  push_cast
  field_simp
  simp only [zero_mul, add_zero, RCLike.I_to_complex]
  congr 1; congr 1; funext y; ring_nf

/-- **The constant term**: `∫_ℝ h(r − i) dr = 2πg_h(0)`. -/
theorem integral_line_const {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    ∫ r : ℝ, h ((r : ℂ) - I) = ((2 * π * gh hR 0 : ℝ) : ℂ) := by
  have := strip_shift (by norm_num : (-1 : ℝ) ≤ 0) (H.diff.mono (strip_mono le_rfl (by norm_num)))
    (fun t ht => H.bound t (strip_mono le_rfl (by norm_num) ht))
  have e1 : (fun r : ℝ => h ((r : ℂ) - I)) = fun r : ℝ => h (↑r + ↑(-1 : ℝ) * I) := by
    funext r; push_cast; ring_nf
  have e2 : (fun r : ℝ => h (↑r + ↑(0 : ℝ) * I)) = fun r : ℝ => h r := by funext r; simp
  rw [e1, this, e2, ← FK_eq_gh H heven hreal 0]
  unfold FK; simp


/-! ## The prime term -/

/-- `n^{−s} = n^{−1/2}e^{−i(r − i) log n}` on the line `s = ½ + i(r − i)`. -/
theorem term_line (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + I * ((r : ℂ) - I)) n
      = ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * Complex.exp (-(I * ((r : ℂ) - I) * (Real.log n : ℝ))) := by
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hn0.le]
  have hs : ((Real.sqrt n : ℝ) : ℂ) = Complex.exp ((Real.log n : ℝ) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Complex.ofReal_exp]; push_cast; ring_nf
  rw [Complex.ofReal_div, hs]
  simp only [div_eq_mul_inv, ← Complex.exp_neg]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; ring

theorem norm_term_line (n : ℕ) (r : ℝ) :
    ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + I * ((r : ℂ) - I)) n‖
      = ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  have e : (1 / 2 + I * ((r : ℂ) - I)).re = (3 / 2 : ℂ).re := by simp; norm_num
  rw [e]

/-- **The prime term**: `∫_ℝ h(r − i) Σ Λ(n)n^{−s} dr = 2π Σ Λ(n)n^{−1/2} g_h(log n)`. -/
theorem prime_line {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    HasSum (fun n : ℕ => ((2 * π * (ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * gh hR (Real.log n)) : ℝ) : ℂ))
      (∫ r : ℝ, h ((r : ℂ) - I)
        * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + I * ((r : ℂ) - I))) := by
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  set s : ℝ → ℂ := fun r => 1 / 2 + I * ((r : ℂ) - I)
  have hsre : ∀ r, (s r).re = 3 / 2 := fun r => by simp [s]; norm_num
  set D : ℕ → ℝ → ℂ := fun n r => h ((r : ℂ) - I) * LSeries.term f (s r) n
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hline : ∀ x : ℝ, Integrable fun r : ℝ => h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * x)) := by
    intro x
    have := integrable_line (H.mul_exp x).diff (H.mul_exp x).bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have hD : ∀ n, n ≠ 0 → D n = fun r : ℝ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * (Real.log n : ℝ)))) := by
    intro n hn; funext r; simp only [D, s, f]; rw [term_line n hn]; ring
  have hD0 : D 0 = fun _ => 0 := by funext r; simp [D, LSeries.term_zero]
  have hint : ∀ n, Integrable (D n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hD0]; exact integrable_zero _ _ _
    · rw [hD n hn]; exact (hline _).const_mul _
  have hL : Integrable fun r : ℝ => h ((r : ℂ) - I) := by
    have := integrable_line H.diff H.bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have hsum : Summable fun n => ∫ r, ‖D n r‖ := by
    have hS : Summable fun n => ‖LSeries.term f (3 / 2 : ℂ) n‖ :=
      summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
    refine (hS.mul_right (∫ r : ℝ, ‖h ((r : ℂ) - I)‖)).congr fun n => ?_
    simp only [D, s, f]
    simp_rw [norm_mul, norm_term_line]
    rw [integral_mul_const, mul_comm]
  have H1 := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ n, ∫ r, D n r = ((2 * π * (ArithmeticFunction.vonMangoldt n / Real.sqrt n
      * gh hR (Real.log n)) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hD0]; simp
    · rw [hD n hn, integral_const_mul]
      have := line_eq H hy (Real.log n)
      have e : ∫ r : ℝ, h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * (Real.log n : ℝ)))
          = FK h (Real.log n) := by
        rw [← this]; congr 1; funext r; push_cast; ring_nf
      rw [e, FK_eq_gh H heven hreal]
      push_cast; ring
  simp_rw [hval] at H1
  convert H1 using 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hs := ((ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s r) (by rw [hsre]; norm_num)).LSeriesHasSum).mul_left (h ((r : ℂ) - I))
  exact hs.tsum_eq.symm


/-! ## Assembly -/

theorem integrable_psi_line {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h ((r : ℂ) - I) * Complex.digamma ((1 / 2 + I * ((r : ℂ) - I)) / 2) := by
  have hmem : ∀ r : ℝ, ((r : ℂ) - I) ∈ strip (-1) 0 := fun r => by
    show -1 ≤ ((r : ℂ) - I).im ∧ ((r : ℂ) - I).im ≤ 0
    simp
  have hc : Continuous fun r : ℝ => h ((r : ℂ) - I) * Complex.digamma ((1 / 2 + I * ((r : ℂ) - I)) / 2) :=
    (psi_strip_diff H).continuousOn.comp_continuous (by fun_prop) hmem
  refine (integrable_om32.const_mul (48 * C)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have := psi_strip_bound H (hmem r)
  simpa using this

theorem integrable_prime_line {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h ((r : ℂ) - I)
      * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + I * ((r : ℂ) - I)) := by
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hL : Integrable fun r : ℝ => h ((r : ℂ) - I) := by
    have := integrable_line H.diff H.bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have hab : LSeries.abscissaOfAbsConv f ≤ ((5 / 4 : ℂ).re : EReal) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)).abscissaOfAbsConv_le
  have hmem : ∀ r : ℝ, (1 / 2 + I * ((r : ℂ) - I)) ∈ {s : ℂ | LSeries.abscissaOfAbsConv f < s.re} := by
    intro r
    show LSeries.abscissaOfAbsConv f < ((1 / 2 + I * ((r : ℂ) - I)).re : EReal)
    refine lt_of_le_of_lt hab ?_
    have e1 : (5 / 4 : ℂ).re = 5 / 4 := by norm_num
    have e2 : (1 / 2 + I * ((r : ℂ) - I)).re = 3 / 2 := by simp; norm_num
    rw [e1, e2]; exact_mod_cast (by norm_num : (5 / 4 : ℝ) < 3 / 2)
  have hcf : Continuous fun r : ℝ => (1 / 2 + I * ((r : ℂ) - I) : ℂ) := by fun_prop
  have hc : Continuous fun r : ℝ => LSeries f (1 / 2 + I * ((r : ℂ) - I)) :=
    continuous_iff_continuousAt.2 fun r =>
      ContinuousAt.comp (f := fun r : ℝ => (1 / 2 + I * ((r : ℂ) - I) : ℂ))
        (((LSeries_differentiableOn f).differentiableAt
          ((isOpen_re_gt_EReal _).mem_nhds (hmem r))).continuousAt) hcf.continuousAt
  have hS : Summable fun n => ‖LSeries.term f (3 / 2 : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  set M := ∑' n, ‖LSeries.term f (3 / 2 : ℂ) n‖
  have hb : ∀ r : ℝ, ‖LSeries f (1 / 2 + I * ((r : ℂ) - I))‖ ≤ M := fun r => by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · exact hS.congr fun n => (norm_term_line n r).symm
    · exact tsum_congr fun n => norm_term_line n r
  refine (hL.norm.mul_const M).mono' ((hL.aestronglyMeasurable.mul hc.aestronglyMeasurable))
    (Eventually.of_forall fun r => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _)

theorem pole_identity (r : ℝ) :
    I * (1 / (1 / 2 + I * ((r : ℂ) - I)) + 1 / (1 / 2 + I * ((r : ℂ) - I) - 1))
      = 1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2) := by
  have h1 : (r : ℂ) - I - I / 2 ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; norm_num at this
  have h2 : (r : ℂ) - I + I / 2 ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; norm_num at this
  have e1 : 1 / 2 + I * ((r : ℂ) - I) = I * ((r : ℂ) - I - I / 2) := by
    ring_nf; rw [Complex.I_sq]; ring
  have e2 : 1 / 2 + I * ((r : ℂ) - I) - 1 = I * ((r : ℂ) - I + I / 2) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [e2, e1]
  field_simp

/-- **Weil's explicit formula over the zeros of `Ξ`** (with multiplicity, each pair `±τ` once):
for `h` even, holomorphic on `|Im t| ≤ 1` with `|h(t)| ≤ C/(1 + (Re t)²)` there, and real on `ℝ`,
`Σ_u 2h(τ_u) = h(i/2) + h(−i/2) − g_h(0) log π + (1/2π)∫h Re ψ(¼ + ir/2) − 2Σ Λ(n)n^{−1/2}g_h(log n)`. -/
theorem weil_Xi {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    HasSum (fun i : ZeroIdx (sqF Xi) => 2 * h (tau i))
      (h (I / 2) + h (-(I / 2))
        + ((-(gh hR 0 * Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe r)
          - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n) : ℝ) : ℂ)) := by
  set LS : ℝ → ℂ := fun r =>
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + I * ((r : ℂ) - I))
  set PS : ℝ → ℂ := fun r => Complex.digamma ((1 / 2 + I * ((r : ℂ) - I)) / 2)
  have hZ := zero_side H heven
  -- the pointwise decomposition
  have hpt : ∀ r : ℝ, h ((r : ℂ) - I) * logDeriv Xi ((r : ℂ) - I)
      = h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2))
        + (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I)
        + I / 2 * (h ((r : ℂ) - I) * PS r)
        - I * (h ((r : ℂ) - I) * LS r) := by
    intro r
    rw [logDeriv_Xi_eq (by simp), ← pole_identity r]
    simp only [LS, PS]
    ring
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hL : Integrable fun r : ℝ => h ((r : ℂ) - I) := by
    have := integrable_line H.diff H.bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have I1 : Integrable fun r : ℝ => h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2)) :=
    integrable_kernel H (τ := I / 2) (by simp; norm_num)
  have I2 : Integrable fun r : ℝ => (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I) := hL.const_mul _
  have I3 : Integrable fun r : ℝ => I / 2 * (h ((r : ℂ) - I) * PS r) := (integrable_psi_line H).const_mul _
  have I4 : Integrable fun r : ℝ => I * (h ((r : ℂ) - I) * LS r) := (integrable_prime_line H).const_mul _
  have hsplit : ∫ r : ℝ, h ((r : ℂ) - I) * logDeriv Xi ((r : ℂ) - I)
      = (∫ r : ℝ, h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2)))
        + (∫ r : ℝ, (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I))
        + (∫ r : ℝ, I / 2 * (h ((r : ℂ) - I) * PS r))
        - ∫ r : ℝ, I * (h ((r : ℂ) - I) * LS r) := by
    simp_rw [hpt]
    have a1 : (∫ r : ℝ, (h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2))
          + (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I)
          + I / 2 * (h ((r : ℂ) - I) * PS r)
          - I * (h ((r : ℂ) - I) * LS r)))
        = (∫ r : ℝ, (h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2))
          + (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I)
          + I / 2 * (h ((r : ℂ) - I) * PS r)))
          - ∫ r : ℝ, I * (h ((r : ℂ) - I) * LS r) := integral_sub ((I1.add I2).add I3) I4
    have a2 : (∫ r : ℝ, (h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2))
          + (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I)
          + I / 2 * (h ((r : ℂ) - I) * PS r)))
        = (∫ r : ℝ, (h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2))
          + (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I)))
          + ∫ r : ℝ, I / 2 * (h ((r : ℂ) - I) * PS r) := integral_add (I1.add I2) I3
    have a3 : (∫ r : ℝ, (h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2))
          + (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I)))
        = (∫ r : ℝ, h ((r : ℂ) - I) * (1 / ((r : ℂ) - I - I / 2) + 1 / ((r : ℂ) - I + I / 2)))
          + ∫ r : ℝ, (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I) := integral_add I1 I2
    rw [a1, a2, a3]
  have v1 := pole_pair H heven (τ := I / 2) (by simp; norm_num)
  have v2 : ∫ r : ℝ, (-(I * (Real.log π : ℂ)) / 2) * h ((r : ℂ) - I)
      = (-(I * (Real.log π : ℂ)) / 2) * ((2 * π * gh hR 0 : ℝ) : ℂ) := by
    rw [integral_const_mul, integral_line_const H heven hreal]
  have v3 : ∫ r : ℝ, I / 2 * (h ((r : ℂ) - I) * PS r) = I / 2 * ((∫ r : ℝ, hR r * psiRe r : ℝ) : ℂ) := by
    rw [integral_const_mul]
    simp only [PS]
    rw [psi_line H, psi_real H heven hreal]
  have hP := prime_line H heven hreal
  have v4 : ∫ r : ℝ, I * (h ((r : ℂ) - I) * LS r)
      = I * ((2 * π * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * gh hR (Real.log n) : ℝ) : ℂ) := by
    rw [integral_const_mul]
    simp only [LS]
    rw [← hP.tsum_eq, ← Complex.ofReal_tsum, tsum_mul_left]
  rw [hsplit, v1, v2, v3, v4] at hZ
  have hZ' := hZ.mul_left ((π * I)⁻¹)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  convert hZ' using 1
  · funext i; field_simp
  · rw [heven (I / 2)]
    push_cast
    field_simp
    ring_nf


/-! ## `WeilExplicit` over the zeros of `Ξ` -/

/-- **The zero family of `Ξ`** in the `ρ` variable: `ρ = ½ + iτ` for both roots `±τ` of every zero
`u` of `Ξ(√w)`, with multiplicity. These are the nontrivial zeros of `ζ`. -/
def rhoXi : Bool × ZeroIdx (sqF Xi) → ℂ := fun p => 1 / 2 + I * (if p.1 then tau p.2 else -tau p.2)

theorem ordinate_rhoXi (p : Bool × ZeroIdx (sqF Xi)) :
    (rhoXi p - 1 / 2) / I = if p.1 then tau p.2 else -tau p.2 := by
  unfold rhoXi; field_simp; ring

theorem Xi_rhoXi (p : Bool × ZeroIdx (sqF Xi)) : Xi ((rhoXi p - 1 / 2) / I) = 0 := by
  rw [ordinate_rhoXi]; split_ifs
  · exact Xi_tau p.2
  · rw [Xi_even]; exact Xi_tau p.2

theorem im_rhoXi (p : Bool × ZeroIdx (sqF Xi)) : |((rhoXi p - 1 / 2) / I).im| < 1 / 2 := by
  rw [ordinate_rhoXi]; split_ifs
  · exact tau_im p.2
  · rw [Complex.neg_im, abs_neg]; exact tau_im p.2

/-- **Weil's explicit formula, proved** (no RH input): for `h` even, holomorphic on `|Im t| ≤ 1`
with `|h(t)| ≤ C/(1 + (Re t)²)` there, and real on `ℝ`, `WeilExplicit` holds over the zeros of
`Ξ` counted with multiplicity. -/
theorem weilExplicit_Xi {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) : WeilExplicit rhoXi h hR := by
  refine ⟨hreal, ?_⟩
  set V := h (I / 2) + h (-(I / 2))
    + ((-(gh hR 0 * Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe r)
      - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n) : ℝ) : ℂ)
  have hW := (weil_Xi H heven hreal).mul_left (1 / 2 : ℂ)
  have hg : HasSum (fun i : ZeroIdx (sqF Xi) => h (tau i)) (V / 2) := by
    convert hW using 1
    · funext i; ring
    · simp only [V]; ring
  have hsum : HasSum (Sum.elim (fun i => h (tau i)) (fun i => h (tau i))) (V / 2 + V / 2) :=
    HasSum.sum hg hg
  rw [add_halves] at hsum
  have e : (fun p : Bool × ZeroIdx (sqF Xi) => h ((rhoXi p - 1 / 2) / I))
      = (Sum.elim (fun i => h (tau i)) (fun i => h (tau i))) ∘ Equiv.boolProdEquivSum _ := by
    funext p
    rcases p with ⟨b, i⟩
    rw [ordinate_rhoXi]
    cases b <;> simp [Equiv.boolProdEquivSum, heven]
  rw [e]
  exact (Equiv.hasSum_iff _).2 hsum

end Pilot1ca

#print axioms Pilot1ca.zero_side
#print axioms Pilot1ca.psi_real
#print axioms Pilot1ca.prime_line
#print axioms Pilot1ca.weil_Xi
#print axioms Pilot1ca.weilExplicit_Xi
