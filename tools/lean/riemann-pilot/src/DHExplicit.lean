import Mathlib
import WeilChiCriterion
import DHPrime

/-! # The explicit formula for the Davenport–Heilbronn function (round 257)

**The wall of round 256** was the mismatch between the strip of the round-225 contour argument
(`|Im t| ≤ 1`, i.e. `Re s ≤ 3/2`) and the abscissa of the prime side (`Re s > 2`). It is removed by
a scaling, not by widening the strip: `Ξ₃(t) := Ξ_dh(3t)` (`XiDH3`). Its line `Im t = −1` is
`Re s = 7/2`, where `dh′/dh = −Σ c(n) n^{−s}` holds (`logDeriv_XiDH3_eq`), and its zeros satisfy
`|Im τ| ≤ ½` (`tau3_im`, from `dh_ne_zero_of_two_lt` and evenness), exactly the height the width-1
kernel bounds of round 225 need (`kernel_integral_le`, `pole_pair`, `integrable_kernel`). Every
width-1 lemma of `StripShift` and `WeilAssemble` is left unchanged: none is widened.

**The chain.** `Ξ₃` is entire, even, `Ξ₃(0) ≠ 0`, of order `≤ 3/2` with constant `216 = 36·6 ≥ 36·3^{3/2}`
(`norm_XiDH3_le`), so it has a Hadamard product (`hadamard_XiDH3`) and the zero side
`Ξ₃′/Ξ₃(t) = Σ_u 2t/(t² − u)` (`hasSum_logDeriv_XiDH3`, through the generic
`hasSum_logDeriv_of_hadamardW`, which is round 255's argument with the function abstracted). The
zero side of the formula (`zero_side3`), the archimedean term with `z₃(t) = 3/4 + 3it/2`
(`psi_line3`, `psi_real3`, `integrable_psi_line3`) and the prime line at `Re s = 7/2` with complex
coefficients, generic in the coefficient sequence (`term_lineC`, `prime_line3`,
`integrable_prime_line3`) are the round-225 lemmas re-instantiated; the archimedean and prime
files were built by agents to a stated interface and re-read and recompiled by the lead. The
coefficients `c(n)` are real (`conjFixed_cDH_chi5`: `ε′ = ε̄` and `χ₅⁻¹ = χ̄₅` make `a(n)` real, and
reality passes through the Dirichlet inverse, `logMul` and convolution), so the right-hand side is a
real number (`weilRHSDH`, with `fDH n = Re c(n) = c(n)`).

**The theorem** (`weil_XiDH3`): for `h` even, holomorphic on `|Im t| ≤ 1` with `|h| ≤ C/(1 + (Re t)²)`
there, and real on `ℝ`,
`Σ_u 2h(τ_u) = 3·[g_h(0) log(5/π) + (1/2π)∫ h(r) Re ψ(3/4 + 3ir/2) dr − 2 Σ c(n) n^{−1/2} g_h(3 log n)]`,
the sum over the zeros `±τ_u` of `Ξ₃`, i.e. over the zeros `½ ± 3iτ_u` of `Λ_{dh}`, which contain every zero of `dh`
with `Re s > 0` and, in each pair, a zero of `dh` with `Re s ≥ ½`
(`dh_zero_of_XiDH3`, `tau3_of_dh_zero`).

**Weil's form for `dh`** (`QDH a g := weilRHSDH (hsq g a)`, no zero of `dh` enters): for every probe at support `a > 0` whose `ĝ²` is a strip test function,
`Q_dh(g) = Σ_u 2ĝ(τ_u)²` (`QDH_hasSum`); under the Riemann hypothesis for `dh` (`DHRH`: every zero
with `Re s > 0` has `Re s = ½`, false by Davenport–Heilbronn) every `τ_u` is real
(`tau3_real_of_DHRH`) and `Q_dh ≥ 0` (`QDH_nonneg_of_DHRH`); hence **a probe with `Q_dh(g) < 0`
certifies an off-line zero of `dh`** (`exists_offline_dh_of_neg`). This is round 252's negative
block with its sign read off, for a function that actually has off-line zeros. Which probes make
`Q_dh` negative is a computation this file does not do.
-/

open Real Complex DirichletCharacter Filter Topology MeasureTheory Set
open scoped LSeries.notation

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## Generic: the log-derivative of a Hadamard product -/

theorem ZeroIdx_ne_zero_of {F : ℂ → ℂ} (hd : Differentiable ℂ F) (he : ∀ z, F (-z) = F z)
    (hF0 : F 0 ≠ 0) (i : ZeroIdx (sqF F)) : i.1 ≠ 0 := by
  intro h
  have hz : sqF F i.1 = 0 := (ordN_ne_zero_iff (sqF_differentiable hd he)
    (by rw [sqF_zero]; exact hF0) i.1).1 (by intro h0; exact Fin.elim0 (h0 ▸ i.2))
  rw [h, sqF_zero] at hz
  exact hF0 hz

/-- **The logarithmic derivative of a Hadamard product**: off the zeros,
`F′(t)/F(t) = Σ_u 2t/(t² − u)`. -/
theorem hasSum_logDeriv_of_hadamardW {F : ℂ → ℂ}
    (H : HadamardW F (fun i : ZeroIdx (sqF F) => i.1⁻¹)) (hF0 : F 0 ≠ 0)
    (hne : ∀ i : ZeroIdx (sqF F), i.1 ≠ 0) {t : ℂ} (ht : F t ≠ 0) :
    HasSum (fun i : ZeroIdx (sqF F) => 2 * t / (t ^ 2 - i.1)) (logDeriv F t) := by
  set w : ZeroIdx (sqF F) → ℂ := fun i => i.1⁻¹
  have hw : Summable fun i => ‖w i‖ := H.summ
  set f : ZeroIdx (sqF F) → ℂ → ℂ := fun i z => 1 + -(z ^ 2 * w i)
  have hprod : ∀ z, HasProd (fun i => f i z) (F z / F 0) := fun z => by
    have := H.prod z; simpa [f, sub_eq_add_neg] using this
  have hf : ∀ i, f i t ≠ 0 := by
    intro i h0
    have := (hprod t).unique (hasProd_zero_of_exists_eq_zero ⟨i, h0⟩)
    exact ht (by rw [div_eq_zero_iff] at this; tauto)
  set R := ‖t‖ + 1
  set s : Set ℂ := Metric.ball 0 R
  have hs : IsOpen s := Metric.isOpen_ball
  have hts : t ∈ s := by simp [s, R]
  have hd : ∀ i, DifferentiableOn ℂ (f i) s := fun i =>
    Differentiable.differentiableOn (by simp only [f]; fun_prop)
  have htend : MultipliableLocallyUniformlyOn f s := by
    refine Summable.multipliableLocallyUniformlyOn_one_add (f := fun i z => -(z ^ 2 * w i))
      (u := fun i => R ^ 2 * ‖w i‖) hs (hw.mul_left _) (Eventually.of_forall fun i z hz => ?_)
      (fun i => Continuous.continuousOn (by fun_prop))
    rw [norm_neg, norm_mul, norm_pow]
    have : ‖z‖ ≤ R := le_of_lt (by simpa [s] using hz)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) this 2) (norm_nonneg _)
  have hlog : ∀ i, logDeriv (f i) t = 2 * t / (t ^ 2 - i.1) := by
    intro i
    have hu := hne i
    have hfi := hf i
    simp only [f, w] at hfi
    have hd' : HasDerivAt (f i) (-(2 * t * w i)) t := by
      have := ((hasDerivAt_pow 2 t).mul_const (w i)).neg.const_add 1
      simpa [f] using this
    rw [logDeriv_apply, hd'.deriv]
    have ht2 : t ^ 2 - i.1 ≠ 0 := by
      intro h0
      apply hfi
      rw [show t ^ 2 = i.1 by linear_combination h0]
      field_simp; ring
    rw [div_eq_div_iff hfi ht2]
    simp only [w]
    field_simp
    ring
  have hm : Summable fun i => logDeriv (f i) t := by
    simp_rw [hlog]
    have hw0 := hw.tendsto_cofinite_zero
    have hev : ∀ᶠ i in cofinite, ‖w i‖ ≤ 1 / (2 * (‖t‖ ^ 2 + 1)) :=
      (Metric.tendsto_nhds.1 (by simpa using hw0) (1 / (2 * (‖t‖ ^ 2 + 1)))
        (by positivity)).mono fun i hi => by
        simpa using hi.le
    refine Summable.of_norm_bounded_eventually (hw.mul_left (4 * ‖t‖)) ?_
    filter_upwards [hev] with i hi
    have hu := hne i
    have hwi : ‖w i‖ = ‖i.1‖⁻¹ := by simp [w]
    have hpos : 0 < ‖i.1‖ := norm_pos_iff.2 hu
    have hi' : ‖i.1‖⁻¹ ≤ (2 * (‖t‖ ^ 2 + 1))⁻¹ := by rw [← hwi]; simpa [one_div] using hi
    have hbig : 2 * (‖t‖ ^ 2 + 1) ≤ ‖i.1‖ := (inv_le_inv₀ hpos (by positivity)).1 hi'
    have hden : ‖i.1‖ / 2 ≤ ‖t ^ 2 - i.1‖ := by
      have := norm_sub_norm_le i.1 (t ^ 2)
      rw [norm_sub_rev, norm_pow] at this
      nlinarith [sq_nonneg ‖t‖]
    rw [norm_div, norm_mul, Complex.norm_two, hwi]
    calc 2 * ‖t‖ / ‖t ^ 2 - i.1‖ ≤ 2 * ‖t‖ / (‖i.1‖ / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 4 * ‖t‖ * ‖i.1‖⁻¹ := by field_simp; ring
  have hnez : ∏' i, f i t ≠ 0 := by rw [(hprod t).tprod_eq]; exact div_ne_zero ht hF0
  have key := logDeriv_tprod_eq_tsum hs hts hf hd hm htend hnez
  have hfun : (fun z => ∏' i, f i z) = fun z => F z * (F 0)⁻¹ := by
    funext z; rw [(hprod z).tprod_eq, div_eq_mul_inv]
  rw [hfun, logDeriv_mul_const t _ (inv_ne_zero hF0)] at key
  rw [key]
  simp_rw [← hlog]
  exact hm.hasSum

/-! ## The scaled function `Ξ₃(t) = Ξ_dh(3t)` -/

/-- `Ξ₃(t) = Ξ_dh(3t)`: its zeros lie in `|Im t| ≤ ½` and its line `Im t = −1` is `Re s = 7/2`. -/
def XiDH3 (t : ℂ) : ℂ := XiDH chi5 (3 * t)

theorem differentiable_XiDH3 : Differentiable ℂ XiDH3 :=
  differentiable_XiDH_chi5.comp (differentiable_id.const_mul 3)

theorem XiDH3_even (t : ℂ) : XiDH3 (-t) = XiDH3 t := by
  unfold XiDH3; rw [mul_neg, XiDH_chi5_even]

theorem XiDH3_zero_ne : XiDH3 0 ≠ 0 := by
  unfold XiDH3; rw [mul_zero]; exact XiDH_chi5_zero_ne'

theorem three_rpow_three_halves_le : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 6 := by
  have h : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (3 / 2 : ℝ)]

theorem norm_XiDH3_le (t : ℂ) : ‖XiDH3 t‖ ≤ KDH chi5 * Real.exp (216 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  unfold XiDH3
  refine (norm_XiDH_chi5_le _).trans ?_
  have hK : 0 ≤ KDH chi5 := by linarith [one_le_KDH (χ := chi5)]
  have h3 : 36 * ‖(3 : ℂ) * t‖ ^ (3 / 2 : ℝ) ≤ 216 * ‖t‖ ^ (3 / 2 : ℝ) := by
    have hn : ‖(3 : ℂ) * t‖ = 3 * ‖t‖ := by rw [norm_mul]; norm_num
    rw [hn, Real.mul_rpow (by norm_num) (norm_nonneg _)]
    have := three_rpow_three_halves_le
    have h0 : 0 ≤ ‖t‖ ^ (3 / 2 : ℝ) := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hK

theorem hadamard_XiDH3 : HadamardW XiDH3 (fun i : ZeroIdx (sqF XiDH3) => i.1⁻¹) :=
  hadamardW_even differentiable_XiDH3 XiDH3_even XiDH3_zero_ne one_le_KDH (by norm_num)
    (by norm_num) (by norm_num) norm_XiDH3_le

theorem ZeroIdx3_ne_zero (i : ZeroIdx (sqF XiDH3)) : i.1 ≠ 0 :=
  ZeroIdx_ne_zero_of differentiable_XiDH3 XiDH3_even XiDH3_zero_ne i

theorem hasSum_logDeriv_XiDH3 {t : ℂ} (ht : XiDH3 t ≠ 0) :
    HasSum (fun i : ZeroIdx (sqF XiDH3) => 2 * t / (t ^ 2 - i.1)) (logDeriv XiDH3 t) :=
  hasSum_logDeriv_of_hadamardW hadamard_XiDH3 XiDH3_zero_ne ZeroIdx3_ne_zero ht

/-- A square root `τ` of the zero `u` of `Ξ₃(√w)`: a zero of `Ξ₃`. -/
def tau3 (i : ZeroIdx (sqF XiDH3)) : ℂ := i.1 ^ ((2 : ℂ)⁻¹)

theorem tau3_sq (i : ZeroIdx (sqF XiDH3)) : tau3 i ^ 2 = i.1 := sqrt_sq' i.1

theorem XiDH3_tau (i : ZeroIdx (sqF XiDH3)) : XiDH3 (tau3 i) = 0 :=
  (ordN_ne_zero_iff (sqF_differentiable differentiable_XiDH3 XiDH3_even)
    (by rw [sqF_zero]; exact XiDH3_zero_ne) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))

theorem norm_tau3 (i : ZeroIdx (sqF XiDH3)) : ‖tau3 i‖ = ‖i.1‖ ^ (2⁻¹ : ℝ) := by
  unfold tau3
  rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]

theorem countable_ZeroIdx3 : Countable (ZeroIdx (sqF XiDH3)) := by
  have hs : Summable fun i : ZeroIdx (sqF XiDH3) => ‖i.1⁻¹‖ := hadamard_XiDH3.summ
  have hc := hs.countable_support
  have e : Function.support (fun i : ZeroIdx (sqF XiDH3) => ‖i.1⁻¹‖) = univ := by
    ext i; simp [ZeroIdx3_ne_zero i]
  rw [e] at hc
  exact Set.countable_univ_iff.1 hc

/-- `Ξ_dh(t) ≠ 0` when `Re(½ + it) > 2`. -/
theorem XiDH_ne_zero_of_lt {t : ℂ} (ht : t.im < -(3 / 2)) : XiDH chi5 t ≠ 0 := by
  have hs : 2 < (1 / 2 + I * t).re := by simp; linarith
  have h0 : 0 < (1 / 2 + I * t).re := by linarith
  show dhLam chi5 (1 / 2 + I * t) ≠ 0
  rw [dhLam_eq chi5 chi5_odd h0]
  refine mul_ne_zero (mul_ne_zero ?_ (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))) ?_
  · rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
  · exact dh_ne_zero_of_two_lt hs

/-- **The zeros of `Ξ₃` lie in `|Im τ| ≤ ½`.** -/
theorem tau3_im (i : ZeroIdx (sqF XiDH3)) : |(tau3 i).im| ≤ 1 / 2 := by
  rw [abs_le]
  constructor
  · by_contra h
    push Not at h
    have := XiDH3_tau i
    unfold XiDH3 at this
    exact XiDH_ne_zero_of_lt (by simp; linarith) this
  · by_contra h
    push Not at h
    have := XiDH3_tau i
    rw [← XiDH3_even] at this
    unfold XiDH3 at this
    exact XiDH_ne_zero_of_lt (by simp; linarith) this

theorem XiDH3_line_ne_zero (r : ℝ) : XiDH3 ((r : ℂ) - I) ≠ 0 := by
  unfold XiDH3
  exact XiDH_ne_zero_of_lt (by simp)

/-- `Σ_i |u_i|^{−7/8} < ∞` over the zeros of `Ξ₃(√w)`. -/
theorem summable_XiDH3_zeros_rpow :
    Summable (fun i : ZeroIdx (sqF XiDH3) => (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹) := by
  have hF := sqF_differentiable differentiable_XiDH3 XiDH3_even
  have hF0 : sqF XiDH3 0 ≠ 0 := by rw [sqF_zero]; exact XiDH3_zero_ne
  have hgF : ∀ w, ‖sqF XiDH3 w‖ ≤ KDH chi5 * Real.exp (216 * ‖w‖ ^ (3 / 4 : ℝ)) := by
    intro w
    refine (norm_XiDH3_le _).trans ?_
    have hn : ‖w ^ ((2 : ℂ)⁻¹)‖ = ‖w‖ ^ (2⁻¹ : ℝ) := by
      rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    rw [hn, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hs := summable_ord_div_rpow hF hF0 one_le_KDH (by norm_num) (by norm_num)
    (by norm_num : (3 / 4 : ℝ) < 7 / 8) hgF
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun u => (hasSum_fintype _).summable, ?_⟩
  refine hs.congr fun u => ?_
  rw [tsum_fintype]
  show _ = ∑ _b : Fin (ordN (sqF XiDH3) u), (‖u‖ ^ (7 / 8 : ℝ))⁻¹
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]

/-! ## The log-derivative of `Ξ_dh` on `Re s > 2` -/

/-- `Λ_{dh}′/Λ_{dh} = ½ log 5 + Γ_ℝ′/Γ_ℝ(s + 1) − Σ c(n) n^{−s}` on `Re s > 2`. -/
theorem logDeriv_dhLam_eq {s : ℂ} (hs : 2 < s.re) :
    logDeriv (dhLam chi5) s = (Real.log 5 : ℂ) / 2 + logDeriv Gammaℝ (s + 1)
      - LSeries (cDH chi5) s := by
  set U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set Pf : ℂ → ℂ := fun z => (5 : ℂ) ^ (z / 2) * (Gammaℝ (z + 1) * dh z)
  have hEq : ∀ z ∈ U, dhLam chi5 z = Pf z := fun z hz => by
    show dhLam chi5 z = (5 : ℂ) ^ (z / 2) * (Gammaℝ (z + 1) * dhL chi5 z)
    rw [dhLam_eq chi5 chi5_odd hz]; push_cast; ring
  have hsU : s ∈ U := by show 0 < s.re; linarith
  have hev : dhLam chi5 =ᶠ[𝓝 s] Pf := Filter.eventuallyEq_of_mem (hU.mem_nhds hsU) hEq
  have hlog : logDeriv (dhLam chi5) s = logDeriv Pf s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hEq s hsU]
  rw [hlog]
  have h5 : (5 : ℂ) ≠ 0 := by norm_num
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hGs : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs1
  have hL : dh s ≠ 0 := dh_ne_zero_of_two_lt hs
  have hdG : DifferentiableAt ℂ (fun z => Gammaℝ (z + 1)) s :=
    (differentiableAt_Gammaℝ_of_re_pos hs1).comp s (differentiableAt_id.add_const 1)
  have hdL : DifferentiableAt ℂ dh s := differentiable_dh s
  have hc : HasDerivAt (fun z : ℂ => (5 : ℂ) ^ (z / 2)) ((5 : ℂ) ^ (s / 2) * Complex.log 5 * (1 / 2)) s := by
    simpa using ((hasDerivAt_id s).div_const 2).const_cpow (c := (5 : ℂ)) (Or.inl h5)
  have hc0 : (5 : ℂ) ^ (s / 2) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have e1 : deriv (fun z : ℂ => z + 1) s = 1 := ((hasDerivAt_id s).add_const 1).deriv
  have hcomp : logDeriv (fun z => Gammaℝ (z + 1)) s = logDeriv Gammaℝ (s + 1) := by
    have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := differentiableAt_id.add_const 1
    have := logDeriv_comp (f := Gammaℝ) (g := fun z : ℂ => z + 1)
      (differentiableAt_Gammaℝ_of_re_pos hs1) hg
    rw [e1, mul_one] at this
    exact this
  simp only [Pf]
  rw [logDeriv_fun_mul (f := fun z : ℂ => (5 : ℂ) ^ (z / 2))
      (g := fun z => Gammaℝ (z + 1) * dh z) s hc0 (mul_ne_zero hGs hL) hc.differentiableAt
      (hdG.mul hdL),
    logDeriv_fun_mul (f := fun z => Gammaℝ (z + 1)) (g := dh) s hGs hL hdG hdL,
    hcomp, logDeriv_dh_eq hs, logDeriv_apply, hc.deriv]
  have hlog5 : Complex.log 5 = (Real.log 5 : ℂ) := by
    rw [show (5 : ℂ) = ((5 : ℝ) : ℂ) by norm_num, Complex.ofReal_log (by norm_num)]
  rw [hlog5]
  field_simp
  ring

/-- `z₃(t) = (½ + 3it + 1)/2`, the digamma argument of the scaled function. -/
def zC3 (t : ℂ) : ℂ := (1 / 2 + I * (3 * t) + 1) / 2

/-- **`Ξ_dh′/Ξ_dh` on `Re s > 2`**: with `s = ½ + it`,
`Ξ_dh′(t)/Ξ_dh(t) = i(½ log 5 − ½ log π + ½ψ((s + 1)/2) − Σ c(n) n^{−s})`. -/
theorem logDeriv_XiDH_eq {t : ℂ} (ht : 2 < (1 / 2 + I * t).re) :
    logDeriv (XiDH chi5) t = I * ((Real.log 5 : ℂ) / 2 - (Real.log π : ℂ) / 2
      + Complex.digamma ((1 / 2 + I * t + 1) / 2) / 2 - LSeries (cDH chi5) (1 / 2 + I * t)) := by
  set s := 1 / 2 + I * t
  have hg : HasDerivAt (fun z : ℂ => 1 / 2 + I * z) I t := by
    simpa using ((hasDerivAt_id t).const_mul I).const_add (1 / 2)
  have hdx : DifferentiableAt ℂ (dhLam chi5) s := differentiable_dhLam chi5 chi5_ne_one s
  have e : XiDH chi5 = dhLam chi5 ∘ fun z : ℂ => 1 / 2 + I * z := by funext z; rfl
  have hs1 : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  rw [e, logDeriv_comp (f := dhLam chi5) (g := fun z : ℂ => 1 / 2 + I * z) hdx hg.differentiableAt,
    hg.deriv, logDeriv_dhLam_eq ht, logDeriv_Gammaℝ hs1]
  ring

/-- **`Ξ₃′/Ξ₃` on the line `Im t = −1`**, the scaled form. -/
theorem logDeriv_XiDH3_eq (r : ℝ) :
    logDeriv XiDH3 ((r : ℂ) - I) = 3 * (I * ((Real.log 5 : ℂ) / 2 - (Real.log π : ℂ) / 2
      + Complex.digamma (zC3 ((r : ℂ) - I)) / 2
      - LSeries (cDH chi5) (1 / 2 + I * (3 * ((r : ℂ) - I))))) := by
  have hg : HasDerivAt (fun z : ℂ => 3 * z) 3 ((r : ℂ) - I) := by
    simpa using (hasDerivAt_id ((r : ℂ) - I)).const_mul (3 : ℂ)
  have hdx : DifferentiableAt ℂ (XiDH chi5) (3 * ((r : ℂ) - I)) := differentiable_XiDH_chi5 _
  have e : XiDH3 = XiDH chi5 ∘ fun z : ℂ => 3 * z := by funext z; rfl
  rw [e, logDeriv_comp (f := XiDH chi5) (g := fun z : ℂ => 3 * z) hdx hg.differentiableAt, hg.deriv,
    logDeriv_XiDH_eq (by simp; norm_num)]
  unfold zC3
  ring

/-! ## The zero side -/

theorem summable_kernel_norms3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Summable fun i : ZeroIdx (sqF XiDH3) =>
      ∫ r : ℝ, ‖h (r - I) * (1 / ((r : ℂ) - I - tau3 i) + 1 / ((r : ℂ) - I + tau3 i))‖ := by
  refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun r => norm_nonneg _)
    (fun i => ?_) (summable_XiDH3_zeros_rpow.mul_left (600 * C * ∫ x, om x))
  refine (kernel_integral_le H (tau3_im i)).trans ?_
  have hK : 0 ≤ 600 * C * ∫ x, om x :=
    mul_nonneg (by linarith [H.C_nonneg]) (integral_nonneg om_nonneg)
  apply mul_le_mul_of_nonneg_left _ hK
  have hu : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdx3_ne_zero i)
  have ht : 0 < ‖tau3 i‖ := by rw [norm_tau3]; positivity
  calc (1 + ‖tau3 i‖) ^ (-(7 / 4 : ℝ)) ≤ ‖tau3 i‖ ^ (-(7 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
    _ = (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
        rw [norm_tau3, ← Real.rpow_mul hu.le, ← Real.rpow_neg hu.le]; norm_num

theorem kernel_eq3 (i : ZeroIdx (sqF XiDH3)) (r : ℝ) :
    2 * ((r : ℂ) - I) / (((r : ℂ) - I) ^ 2 - i.1)
      = 1 / ((r : ℂ) - I - tau3 i) + 1 / ((r : ℂ) - I + tau3 i) := by
  have him := abs_le.1 (tau3_im i)
  have h1 : (r : ℂ) - I - tau3 i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; linarith
  have h2 : (r : ℂ) - I + tau3 i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; linarith
  have h3 : ((r : ℂ) - I) ^ 2 - tau3 i ^ 2 ≠ 0 := by
    rw [show ((r : ℂ) - I) ^ 2 - tau3 i ^ 2 = ((r : ℂ) - I - tau3 i) * ((r : ℂ) - I + tau3 i) by ring]
    exact mul_ne_zero h1 h2
  rw [← tau3_sq i]
  field_simp
  ring

/-- **The zero side**: `∫_ℝ h(r − i)Ξ₃′/Ξ₃(r − i) dr = Σ_u 2πi h(τ_u)`. -/
theorem zero_side3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t) :
    HasSum (fun i : ZeroIdx (sqF XiDH3) => 2 * π * I * h (tau3 i))
      (∫ r : ℝ, h (r - I) * logDeriv XiDH3 (r - I)) := by
  have := countable_ZeroIdx3
  set F : ZeroIdx (sqF XiDH3) → ℝ → ℂ := fun i r =>
    h (r - I) * (1 / ((r : ℂ) - I - tau3 i) + 1 / ((r : ℂ) - I + tau3 i))
  have hlt : ∀ i : ZeroIdx (sqF XiDH3), |(tau3 i).im| < 1 := fun i =>
    (tau3_im i).trans_lt (by norm_num)
  have hint : ∀ i, Integrable (F i) := fun i => integrable_kernel H (hlt i)
  have H1 := hasSum_integral_of_summable_integral_norm hint (summable_kernel_norms3 H)
  have hval : ∀ i, ∫ r, F i r = 2 * π * I * h (tau3 i) := fun i => pole_pair H heven (hlt i)
  simp_rw [hval] at H1
  convert H1 using 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hs := (hasSum_logDeriv_XiDH3 (XiDH3_line_ne_zero r)).mul_left (h (r - I))
  simp only [kernel_eq3] at hs
  exact hs.tsum_eq.symm

/-! ## The prime-side coefficients `c(n)` are real -/

/-- A sequence fixed by complex conjugation. -/
def ConjFixed (f : ℕ → ℂ) : Prop := ∀ n, (starRingEnd ℂ) (f n) = f n

theorem ConjFixed.add {f g : ℕ → ℂ} (hf : ConjFixed f) (hg : ConjFixed g) : ConjFixed (f + g) :=
  fun n => by simp only [Pi.add_apply, map_add, hf n, hg n]

theorem conjFixed_delta : ConjFixed LSeries.delta := fun n => by
  simp only [LSeries.delta]; split_ifs <;> simp

theorem ConjFixed.logMul {f : ℕ → ℂ} (hf : ConjFixed f) : ConjFixed (LSeries.logMul f) :=
  fun n => by simp only [LSeries.logMul, map_mul, ← Complex.natCast_log, Complex.conj_ofReal, hf n]

theorem ConjFixed.convolution {f g : ℕ → ℂ} (hf : ConjFixed f) (hg : ConjFixed g) :
    ConjFixed (f ⍟ g) := fun n => by
  rw [LSeries.convolution_def]
  simp only [map_sum, map_mul]
  exact Finset.sum_congr rfl fun p _ => by rw [hf, hg]

theorem ConjFixed.dinv {u : ℕ → ℂ} (hu : ConjFixed u) : ConjFixed (DInv.dinv u) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [DInv.dinv_zero]
      · simp [DInv.dinv_one]
    · rw [DInv.dinv_of_two_le u hn, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Finset.mem_filter.1 hp
      obtain ⟨hab, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hp'.1
      have ha1 : p.1 ≠ 1 := hp'.2
      have ha0 : p.1 ≠ 0 := by rintro h; rw [h] at hab; simp at hab; omega
      have hb0 : 0 < p.2 := Nat.pos_of_ne_zero (by rintro h; rw [h] at hab; simp at hab; omega)
      have h2 : 2 ≤ p.1 := by omega
      have hlt : p.2 < n := by nlinarith
      rw [map_mul, hu, ih p.2 hlt]

theorem conjFixed_aDH_chi5 : ConjFixed (aDH chi5) := by
  intro n
  simp only [aDH, map_add, map_mul, map_one, chi5_inv_apply, rootNumber_chi5_inv_eq_conj,
    Complex.conj_conj]
  ring

theorem conjFixed_uDH_chi5 : ConjFixed (uDH chi5) := by
  intro n
  simp only [uDH]
  split_ifs
  · rw [map_div₀, conjFixed_aDH_chi5, conjFixed_aDH_chi5]
  · exact map_zero _

/-- **`c(n)` is real**: the coefficients of `−dh′/dh` are fixed by conjugation. -/
theorem conjFixed_cDH_chi5 : ConjFixed (cDH chi5) :=
  (conjFixed_delta.add conjFixed_uDH_chi5).logMul.convolution conjFixed_uDH_chi5.dinv

/-- The real prime-side coefficients `f(n) = Re c(n) = c(n)`. -/
def fDH (n : ℕ) : ℝ := (cDH chi5 n).re

theorem cDH_chi5_eq (n : ℕ) : cDH chi5 n = (fDH n : ℂ) :=
  (Complex.conj_eq_iff_re.1 (conjFixed_cDH_chi5 n)).symm

/-! ## Zeros of `Ξ₃` and zeros of `dh` -/

/-- The Riemann hypothesis for `dh`: every zero with `Re s > 0` lies on `Re s = ½`. (False in
reality — Davenport and Heilbronn's theorem — but this is the statement the criterion tests.) -/
def DHRH : Prop := ∀ s : ℂ, dh s = 0 → 0 < s.re → s.re = 1 / 2

/-- Each `τ_u` gives a zero `½ + 3iτ_u` of `Λ_{dh}`; when `Im τ_u ≤ 0` it is a zero of `dh` with
`Re s > 0`. -/
theorem dh_zero_of_XiDH3 {τ : ℂ} (hτ : XiDH3 τ = 0) (hle : τ.im ≤ 0) :
    dh (1 / 2 + I * (3 * τ)) = 0 ∧ 0 < (1 / 2 + I * (3 * τ)).re := by
  have hs : dhLam chi5 (1 / 2 + I * (3 * τ)) = 0 := hτ
  have hre : (1 / 2 + I * (3 * τ)).re = 1 / 2 - 3 * τ.im := by simp; ring
  have h0 : 0 < (1 / 2 + I * (3 * τ)).re := by rw [hre]; linarith
  exact ⟨(dh_eq_zero_iff h0).2 hs, h0⟩

/-- Under `DHRH` every `τ_u` is real. -/
theorem tau3_real_of_DHRH (hRH : DHRH) (i : ZeroIdx (sqF XiDH3)) : (tau3 i).im = 0 := by
  have hz := XiDH3_tau i
  have key : ∀ τ : ℂ, XiDH3 τ = 0 → τ.im ≤ 0 → τ.im = 0 := by
    intro τ hτ hle
    obtain ⟨hd, h0⟩ := dh_zero_of_XiDH3 hτ hle
    have := hRH _ hd h0
    have hre : (1 / 2 + I * (3 * τ)).re = 1 / 2 - 3 * τ.im := by simp; ring
    rw [hre] at this; linarith
  rcases le_or_gt (tau3 i).im 0 with h | h
  · exact key _ hz h
  · have := key (-(tau3 i)) (by rw [XiDH3_even]; exact hz) (by simp; linarith)
    simp at this; linarith

/-- Every zero of `dh` with `Re s > 0` is `½ ± 3iτ_u` for some `u`. -/
theorem tau3_of_dh_zero {s : ℂ} (hs : dh s = 0) (h0 : 0 < s.re) :
    ∃ i : ZeroIdx (sqF XiDH3), tau3 i = (s - 1 / 2) / (3 * I) ∨
      tau3 i = -((s - 1 / 2) / (3 * I)) := by
  set t := (s - 1 / 2) / (3 * I)
  have hst : 1 / 2 + I * (3 * t) = s := by simp only [t]; field_simp; ring
  have hXt : XiDH3 t = 0 := by
    show dhLam chi5 (1 / 2 + I * (3 * t)) = 0
    rw [hst]; exact (dh_eq_zero_iff h0).1 hs
  have hF := sqF_differentiable differentiable_XiDH3 XiDH3_even
  have hF0 : sqF XiDH3 0 ≠ 0 := by rw [sqF_zero]; exact XiDH3_zero_ne
  have hu : sqF XiDH3 (t ^ 2) = 0 := by rw [sqF_sq XiDH3_even]; exact hXt
  have hord : ordN (sqF XiDH3) (t ^ 2) ≠ 0 := (ordN_ne_zero_iff hF hF0 _).2 hu
  refine ⟨⟨t ^ 2, ⟨0, Nat.pos_of_ne_zero hord⟩⟩, ?_⟩
  have hsq : tau3 ⟨t ^ 2, ⟨0, Nat.pos_of_ne_zero hord⟩⟩ ^ 2 = t ^ 2 := tau3_sq _
  exact sq_eq_sq_iff_eq_or_eq_neg.1 hsq

/-! ## The archimedean term -/

/-- `Re ψ(3/4 + 3ir/2)`. -/
def psiRe3 (r : ℝ) : ℝ := (Complex.digamma (zC3 r)).re

theorem digamma_zC3_neg (r : ℝ) :
    Complex.digamma (zC3 ((-r : ℝ) : ℂ)) = (starRingEnd ℂ) (Complex.digamma (zC3 r)) := by
  have hconj : zC3 ((-r : ℝ) : ℂ) = (starRingEnd ℂ) (zC3 r) := by
    apply Complex.ext
    · rw [Complex.conj_re]; simp [zC3]
    · rw [Complex.conj_im]; simp [zC3]; ring
  have hnp : ∀ m : ℕ, zC3 r ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [zC3] at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hdiff := (Complex.differentiableAt_Gamma (zC3 r) hnp).hasDerivAt
  have hGc : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext z; simp [Complex.Gamma_conj]
  have hd := hdiff.conj_conj
  rw [hGc] at hd
  rw [hconj, Complex.digamma, logDeriv_apply, logDeriv_apply, hd.deriv, Complex.Gamma_conj,
    ← map_div₀]

theorem psi_strip_bound3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {t : ℂ}
    (ht : t ∈ PilotWeil.strip (-1) 0) :
    ‖h t * Complex.digamma (zC3 t)‖ ≤ 48 * C * (1 + |t.re|) ^ (-(3 / 2 : ℝ)) := by
  have hC := H.C_nonneg
  obtain ⟨h1, h2⟩ := ht
  set x := t.re
  set z : ℂ := zC3 t
  have hzre : z.re = 3 / 4 - 3 / 2 * t.im := by simp [z, zC3]; ring
  have hz : 1 / 4 ≤ z.re := by rw [hzre]; linarith
  have hnz : 1 + ‖z‖ ≤ 4 * (1 + |x|) := by
    have ht' : ‖t‖ ≤ |x| + 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im t).trans ?_
      have : |t.im| ≤ 1 := abs_le.2 ⟨h1, by linarith⟩
      linarith
    have : ‖z‖ ≤ (1 / 2 + 3 * ‖t‖ + 1) / 2 := by
      simp only [z, zC3, norm_div, Complex.norm_two]
      gcongr
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans ?_) (by simp)
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul]; norm_num
    linarith [abs_nonneg x]
  have hX : 0 < 1 + |x| := by positivity
  have hpsi : ‖Complex.digamma z‖ ≤ 24 * (1 + |x|) ^ (1 / 2 : ℝ) := by
    refine (norm_digamma_le hz).trans ?_
    have : Real.sqrt (1 + ‖z‖) ≤ 2 * (1 + |x|) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc (1 + ‖z‖) ^ (1 / 2 : ℝ) ≤ (4 * (1 + |x|)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hnz (by norm_num)
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
  calc ‖h t‖ * ‖Complex.digamma z‖
      ≤ (2 * C * (1 + |x|) ^ (-(2 : ℝ))) * (24 * (1 + |x|) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hh hpsi (norm_nonneg _) (by positivity)
    _ = 48 * C * ((1 + |x|) ^ (-(2 : ℝ)) * (1 + |x|) ^ (1 / 2 : ℝ)) := by ring
    _ = 48 * C * (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hX]; norm_num

theorem psi_strip_diff3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    DifferentiableOn ℂ (fun t => h t * Complex.digamma (zC3 t)) (PilotWeil.strip (-1) 0) := by
  refine (H.diff.mono (strip_mono le_rfl (by norm_num))).mul ?_
  refine PilotDigamma.differentiableOn_digamma.comp (Differentiable.differentiableOn (by
    unfold zC3; fun_prop)) fun t ht => ?_
  show 0 < (zC3 t).re
  have := ht.2
  simp [zC3]; linarith

theorem psi_line3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    ∫ r : ℝ, h ((r : ℂ) - I) * Complex.digamma (zC3 ((r : ℂ) - I))
      = ∫ r : ℝ, h r * Complex.digamma (zC3 r) := by
  have := strip_shift' (by norm_num : (-1 : ℝ) ≤ 0) (psi_strip_diff3 H)
    (fun t ht => psi_strip_bound3 H ht)
  calc ∫ r : ℝ, h ((r : ℂ) - I) * Complex.digamma (zC3 ((r : ℂ) - I))
      = ∫ r : ℝ, h (↑r + ↑(-1 : ℝ) * I) * Complex.digamma (zC3 (↑r + ↑(-1 : ℝ) * I)) := by
        congr 1; funext r; push_cast; ring_nf
    _ = ∫ r : ℝ, h (↑r + ↑(0 : ℝ) * I) * Complex.digamma (zC3 (↑r + ↑(0 : ℝ) * I)) := this
    _ = _ := by congr 1; funext r; push_cast; ring_nf

theorem integrable_psi_real3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h r * Complex.digamma (zC3 r) := by
  have hmem : ∀ r : ℝ, (r : ℂ) ∈ PilotWeil.strip (-1) 0 := fun r => by
    show -1 ≤ (r : ℂ).im ∧ (r : ℂ).im ≤ 0
    simp
  have hc : Continuous fun r : ℝ => h r * Complex.digamma (zC3 r) :=
    (psi_strip_diff3 H).continuousOn.comp_continuous (by fun_prop) hmem
  refine (integrable_om32.const_mul (48 * C)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have := psi_strip_bound3 H (hmem r)
  simpa using this

theorem psi_real3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    ∫ r : ℝ, h r * Complex.digamma (zC3 r) = ((∫ r : ℝ, hR r * psiRe3 r : ℝ) : ℂ) := by
  have hi := integrable_psi_real3 H
  rw [← integral_re_add_im hi]
  have hre : ∀ r : ℝ, RCLike.re (h r * Complex.digamma (zC3 r)) = hR r * psiRe3 r := fun r => by
    rw [hreal]; simp [psiRe3]
  have him0 : ∫ r : ℝ, RCLike.im (h r * Complex.digamma (zC3 r)) = 0 := by
    set g : ℝ → ℝ := fun r => RCLike.im (h r * Complex.digamma (zC3 r))
    have hg : ∀ r, g (-r) = -g r := fun r => by
      simp only [g]
      have e := digamma_zC3_neg r
      rw [hreal, hreal, hR_even heven hreal, e]
      simp
    have := integral_neg_eq_self g volume
    simp_rw [hg, integral_neg] at this
    linarith
  simp_rw [hre]
  rw [him0]
  simp

theorem integrable_psi_line3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Integrable fun r : ℝ => h ((r : ℂ) - I) * Complex.digamma (zC3 ((r : ℂ) - I)) := by
  have hmem : ∀ r : ℝ, ((r : ℂ) - I) ∈ PilotWeil.strip (-1) 0 := fun r => by
    show -1 ≤ ((r : ℂ) - I).im ∧ ((r : ℂ) - I).im ≤ 0
    simp
  have hc : Continuous fun r : ℝ => h ((r : ℂ) - I) * Complex.digamma (zC3 ((r : ℂ) - I)) :=
    (psi_strip_diff3 H).continuousOn.comp_continuous (by fun_prop) hmem
  refine (integrable_om32.const_mul (48 * C)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have := psi_strip_bound3 H (hmem r)
  simpa using this

/-! ## The prime term on the scaled line -/

theorem term_lineC (f : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) (r : ℝ) :
    LSeries.term f (1 / 2 + I * (3 * ((r : ℂ) - I))) n
      = f n / (Real.sqrt n : ℂ) * Complex.exp (-(I * ((r : ℂ) - I) * ((3 * Real.log n : ℝ) : ℂ))) := by
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hn0.le]
  have hs : ((Real.sqrt n : ℝ) : ℂ) = Complex.exp ((Real.log n : ℝ) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Complex.ofReal_exp]; push_cast; ring_nf
  rw [hs]
  simp only [div_eq_mul_inv, ← Complex.exp_neg]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem norm_term_lineC (f : ℕ → ℂ) (n : ℕ) (r : ℝ) :
    ‖LSeries.term f (1 / 2 + I * (3 * ((r : ℂ) - I))) n‖ = ‖LSeries.term f (7 / 2 : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  have e : (1 / 2 + I * (3 * ((r : ℂ) - I))).re = (7 / 2 : ℂ).re := by simp; norm_num
  rw [e]

/-- The prime term at the scaled line: `∫ h(r−i) Σ f(n) n^{−(7/2+3ir)} dr = 2π Σ f(n) n^{−1/2} g_h(3 log n)`. -/
theorem prime_line3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) {f : ℕ → ℂ} (hf : LSeriesSummable f (7 / 2 : ℂ)) :
    HasSum (fun n : ℕ => 2 * π * (f n / (Real.sqrt n : ℂ) * (gh hR (3 * Real.log n) : ℂ)))
      (∫ r : ℝ, h ((r : ℂ) - I) * LSeries f (1 / 2 + I * (3 * ((r : ℂ) - I)))) := by
  set s : ℝ → ℂ := fun r => 1 / 2 + I * (3 * ((r : ℂ) - I))
  have hsre : ∀ r, (s r).re = (7 / 2 : ℂ).re := fun r => by simp [s]; norm_num
  set D : ℕ → ℝ → ℂ := fun n r => h ((r : ℂ) - I) * LSeries.term f (s r) n
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hline : ∀ x : ℝ, Integrable fun r : ℝ => h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * x)) := by
    intro x
    have := integrable_line (H.mul_exp x).diff (H.mul_exp x).bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have hD : ∀ n, n ≠ 0 → D n = fun r : ℝ => (f n / (Real.sqrt n : ℂ))
      * (h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * ((3 * Real.log n : ℝ) : ℂ)))) := by
    intro n hn; funext r; simp only [D, s]; rw [term_lineC f n hn]; ring
  have hD0 : D 0 = fun _ => 0 := by funext r; simp [D, LSeries.term_zero]
  have hint : ∀ n, Integrable (D n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hD0]; exact integrable_zero _ _ _
    · rw [hD n hn]; exact (hline _).const_mul _
  have hsum : Summable fun n => ∫ r, ‖D n r‖ := by
    have hS : Summable fun n => ‖LSeries.term f (7 / 2 : ℂ) n‖ := summable_norm_iff.2 hf
    refine (hS.mul_right (∫ r : ℝ, ‖h ((r : ℂ) - I)‖)).congr fun n => ?_
    simp only [D, s]
    simp_rw [norm_mul, norm_term_lineC]
    rw [integral_mul_const, mul_comm]
  have H1 := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ n, ∫ r, D n r
      = 2 * π * (f n / (Real.sqrt n : ℂ) * (gh hR (3 * Real.log n) : ℂ)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hD0]; simp
    · rw [hD n hn, integral_const_mul]
      have := line_eq H hy (3 * Real.log n)
      have e : ∫ r : ℝ, h ((r : ℂ) - I) * Complex.exp (-(I * ((r : ℂ) - I) * ((3 * Real.log n : ℝ) : ℂ)))
          = FK h (3 * Real.log n) := by
        rw [← this]; congr 1; funext r; push_cast; ring_nf
      rw [e, FK_eq_gh H heven hreal]
      push_cast; ring
  simp_rw [hval] at H1
  convert H1 using 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hs := (((LSeriesSummable_iff_of_re_eq_re (hsre r)).2 hf).LSeriesHasSum).mul_left
    (h ((r : ℂ) - I))
  exact hs.tsum_eq.symm

theorem integrable_prime_line3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) {f : ℕ → ℂ}
    (hf : LSeriesSummable f (3 : ℂ)) :
    Integrable fun r : ℝ => h ((r : ℂ) - I) * LSeries f (1 / 2 + I * (3 * ((r : ℂ) - I))) := by
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hL : Integrable fun r : ℝ => h ((r : ℂ) - I) := by
    have := integrable_line H.diff H.bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have hab : LSeries.abscissaOfAbsConv f ≤ ((3 : ℂ).re : EReal) := hf.abscissaOfAbsConv_le
  have hmem : ∀ r : ℝ, (1 / 2 + I * (3 * ((r : ℂ) - I))) ∈
      {s : ℂ | LSeries.abscissaOfAbsConv f < s.re} := by
    intro r
    show LSeries.abscissaOfAbsConv f < ((1 / 2 + I * (3 * ((r : ℂ) - I))).re : EReal)
    refine lt_of_le_of_lt hab ?_
    have e1 : (3 : ℂ).re = 3 := by norm_num
    have e2 : (1 / 2 + I * (3 * ((r : ℂ) - I))).re = 7 / 2 := by simp; norm_num
    rw [e1, e2]; exact_mod_cast (by norm_num : (3 : ℝ) < 7 / 2)
  have hcf : Continuous fun r : ℝ => (1 / 2 + I * (3 * ((r : ℂ) - I)) : ℂ) := by fun_prop
  have hc : Continuous fun r : ℝ => LSeries f (1 / 2 + I * (3 * ((r : ℂ) - I))) :=
    continuous_iff_continuousAt.2 fun r =>
      ContinuousAt.comp (f := fun r : ℝ => (1 / 2 + I * (3 * ((r : ℂ) - I)) : ℂ))
        (((LSeries_differentiableOn f).differentiableAt
          ((isOpen_re_gt_EReal _).mem_nhds (hmem r))).continuousAt) hcf.continuousAt
  have hS : Summable fun n => ‖LSeries.term f (7 / 2 : ℂ) n‖ :=
    summable_norm_iff.2 (hf.of_re_le_re (by norm_num))
  set M := ∑' n, ‖LSeries.term f (7 / 2 : ℂ) n‖
  have hb : ∀ r : ℝ, ‖LSeries f (1 / 2 + I * (3 * ((r : ℂ) - I)))‖ ≤ M := fun r => by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · exact hS.congr fun n => (norm_term_lineC f n r).symm
    · exact tsum_congr fun n => norm_term_lineC f n r
  refine (hL.norm.mul_const M).mono' ((hL.aestronglyMeasurable.mul hc.aestronglyMeasurable))
    (Eventually.of_forall fun r => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _)

/-! ## The Davenport–Heilbronn coefficients -/

theorem LSeriesSummable_cDH_chi5_seven_halves : LSeriesSummable (cDH chi5) (7 / 2 : ℂ) :=
  LSeriesSummable_cDH_chi5 (by norm_num)

theorem LSeriesSummable_cDH_chi5_three : LSeriesSummable (cDH chi5) (3 : ℂ) :=
  LSeriesSummable_cDH_chi5 (by norm_num)

/-- The right-hand side of the explicit formula for `Ξ₃`:
`3·[g_h(0) log(5/π) + (1/2π)∫ h Re ψ(3/4 + 3ir/2) − 2 Σ c(n) n^{−1/2} g_h(3 log n)]`. -/
def weilRHSDH (hR : ℝ → ℝ) : ℝ :=
  3 * (gh hR 0 * (Real.log 5 - Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe3 r)
    - 2 * ∑' n : ℕ, fDH n / Real.sqrt n * gh hR (3 * Real.log n))

/-- **Weil's explicit formula for the Davenport–Heilbronn function** (over the zeros of
`Ξ₃(t) = Ξ_dh(3t)`, each pair `±τ` once, with multiplicity): for `h` even, holomorphic on
`|Im t| ≤ 1` with `|h(t)| ≤ C/(1 + (Re t)²)` there, and real on `ℝ`,
`Σ_u 2h(τ_u) = 3·[g_h(0) log(5/π) + (1/2π)∫h Re ψ(3/4 + 3ir/2) − 2Σ c(n)n^{−1/2}g_h(3 log n)]`. -/
theorem weil_XiDH3 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR r) :
    HasSum (fun i : ZeroIdx (sqF XiDH3) => 2 * h (tau3 i)) (weilRHSDH hR : ℂ) := by
  set LS : ℝ → ℂ := fun r => LSeries (cDH chi5) (1 / 2 + I * (3 * ((r : ℂ) - I)))
  set PS : ℝ → ℂ := fun r => Complex.digamma (zC3 ((r : ℂ) - I))
  set κ : ℂ := 3 * (I * ((Real.log 5 : ℂ) - (Real.log π : ℂ)) / 2)
  have hZ := zero_side3 H heven
  have hpt : ∀ r : ℝ, h ((r : ℂ) - I) * logDeriv XiDH3 ((r : ℂ) - I)
      = κ * h ((r : ℂ) - I) + 3 * I / 2 * (h ((r : ℂ) - I) * PS r)
        - 3 * I * (h ((r : ℂ) - I) * LS r) := by
    intro r
    rw [logDeriv_XiDH3_eq]
    simp only [LS, PS, κ]
    ring
  have hy : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hL : Integrable fun r : ℝ => h ((r : ℂ) - I) := by
    have := integrable_line H.diff H.bound hy
    refine this.congr (Eventually.of_forall fun r => ?_)
    simp only; push_cast; ring_nf
  have I2 : Integrable fun r : ℝ => κ * h ((r : ℂ) - I) := hL.const_mul _
  have I3 : Integrable fun r : ℝ => 3 * I / 2 * (h ((r : ℂ) - I) * PS r) :=
    (integrable_psi_line3 H).const_mul _
  have I4 : Integrable fun r : ℝ => 3 * I * (h ((r : ℂ) - I) * LS r) :=
    (integrable_prime_line3 H LSeriesSummable_cDH_chi5_three).const_mul _
  have hsplit : ∫ r : ℝ, h ((r : ℂ) - I) * logDeriv XiDH3 ((r : ℂ) - I)
      = (∫ r : ℝ, κ * h ((r : ℂ) - I)) + (∫ r : ℝ, 3 * I / 2 * (h ((r : ℂ) - I) * PS r))
        - ∫ r : ℝ, 3 * I * (h ((r : ℂ) - I) * LS r) := by
    simp_rw [hpt]
    have a1 : (∫ r : ℝ, (κ * h ((r : ℂ) - I) + 3 * I / 2 * (h ((r : ℂ) - I) * PS r)
          - 3 * I * (h ((r : ℂ) - I) * LS r)))
        = (∫ r : ℝ, (κ * h ((r : ℂ) - I) + 3 * I / 2 * (h ((r : ℂ) - I) * PS r)))
          - ∫ r : ℝ, 3 * I * (h ((r : ℂ) - I) * LS r) := integral_sub (I2.add I3) I4
    have a2 : (∫ r : ℝ, (κ * h ((r : ℂ) - I) + 3 * I / 2 * (h ((r : ℂ) - I) * PS r)))
        = (∫ r : ℝ, κ * h ((r : ℂ) - I)) + ∫ r : ℝ, 3 * I / 2 * (h ((r : ℂ) - I) * PS r) :=
      integral_add I2 I3
    rw [a1, a2]
  have v2 : ∫ r : ℝ, κ * h ((r : ℂ) - I) = κ * ((2 * π * gh hR 0 : ℝ) : ℂ) := by
    rw [integral_const_mul, integral_line_const H heven hreal]
  have v3 : ∫ r : ℝ, 3 * I / 2 * (h ((r : ℂ) - I) * PS r)
      = 3 * I / 2 * ((∫ r : ℝ, hR r * psiRe3 r : ℝ) : ℂ) := by
    rw [integral_const_mul]
    simp only [PS]
    rw [psi_line3 H, psi_real3 H heven hreal]
  have hP := prime_line3 H heven hreal LSeriesSummable_cDH_chi5_seven_halves
  have hterm : ∀ n : ℕ, (2 * π * (cDH chi5 n / (Real.sqrt n : ℂ) * (gh hR (3 * Real.log n) : ℂ)) : ℂ)
      = ((2 * π * (fDH n / Real.sqrt n * gh hR (3 * Real.log n)) : ℝ) : ℂ) := fun n => by
    rw [cDH_chi5_eq]; push_cast; ring
  simp_rw [hterm] at hP
  have v4 : ∫ r : ℝ, 3 * I * (h ((r : ℂ) - I) * LS r)
      = 3 * I * ((2 * π * ∑' n : ℕ, fDH n / Real.sqrt n * gh hR (3 * Real.log n) : ℝ) : ℂ) := by
    rw [integral_const_mul]
    simp only [LS]
    rw [← hP.tsum_eq, ← Complex.ofReal_tsum, tsum_mul_left]
  rw [hsplit, v2, v3, v4] at hZ
  have hZ' := hZ.mul_left ((π * I)⁻¹)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  convert hZ' using 1
  · funext i; field_simp
  · unfold weilRHSDH
    simp only [κ]
    push_cast
    field_simp

/-! ## Weil's form for `dh` -/

/-- **Weil's form for `dh`** at support `[−a, a]`: `Q_dh(g) = weilRHSDH(ĝ²)`. No zero of `dh`
enters. -/
def QDH (a : ℝ) (g : ℝ → ℝ) : ℝ := weilRHSDH (hsq g a)

/-- **The explicit formula for a probe**: `Q_dh(g) = Σ_u 2ĝ(τ_u)²`. -/
theorem QDH_hasSum {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a z ^ 2) K) :
    HasSum (fun i : ZeroIdx (sqF XiDH3) => 2 * ghatC g a (tau3 i) ^ 2) (QDH a g : ℂ) :=
  weil_XiDH3 hK (fun t => even_ghat_sq hp.even a t) (hsq_ofReal hp ha.le)

/-- **`DHRH ⟹ Q_dh ≥ 0`** for every probe whose `ĝ²` is a strip test function. -/
theorem QDH_nonneg_of_DHRH (hRH : DHRH) {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (ha : 0 < a)
    {K : ℝ} (hK : StripTest (fun z => ghatC g a z ^ 2) K) : 0 ≤ QDH a g := by
  have h := (QDH_hasSum hp ha hK).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, ofReal_re] at h
  refine h.nonneg fun i => ?_
  have hi := tau3_real_of_DHRH hRH i
  have e : tau3 i = ((tau3 i).re : ℂ) := Complex.ext (by simp) (by simp [hi])
  rw [e, hsq_ofReal hp ha.le]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (by norm_num) (hsq_nonneg _)

/-- **A negative Weil form certifies an off-line zero of `dh`.** -/
theorem exists_offline_dh_of_neg {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (ha : 0 < a) {K : ℝ}
    (hK : StripTest (fun z => ghatC g a z ^ 2) K) (hneg : QDH a g < 0) :
    ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 := by
  by_contra hcon
  push Not at hcon
  exact absurd (QDH_nonneg_of_DHRH (fun s hs h0 => hcon s hs h0) hp ha hK) (not_le.2 hneg)

end PsiOmega

#print axioms PsiOmega.hasSum_logDeriv_of_hadamardW
#print axioms PsiOmega.norm_XiDH3_le
#print axioms PsiOmega.hadamard_XiDH3
#print axioms PsiOmega.hasSum_logDeriv_XiDH3
#print axioms PsiOmega.tau3_im
#print axioms PsiOmega.summable_XiDH3_zeros_rpow
#print axioms PsiOmega.logDeriv_dhLam_eq
#print axioms PsiOmega.logDeriv_XiDH3_eq
#print axioms PsiOmega.zero_side3
#print axioms PsiOmega.conjFixed_cDH_chi5
#print axioms PsiOmega.tau3_real_of_DHRH
#print axioms PsiOmega.tau3_of_dh_zero
#print axioms PsiOmega.psi_line3
#print axioms PsiOmega.psi_real3
#print axioms PsiOmega.prime_line3
#print axioms PsiOmega.integrable_prime_line3
#print axioms PsiOmega.weil_XiDH3
#print axioms PsiOmega.QDH_hasSum
#print axioms PsiOmega.QDH_nonneg_of_DHRH
#print axioms PsiOmega.exists_offline_dh_of_neg
