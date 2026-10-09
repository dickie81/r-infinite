import Mathlib
import PsiOmega

/-! # Mertens and Liouville: one-sided bounds give zero-free half-planes (round 221)

`PsiOmega.zeta_ne_zero_of_mellin` applied to the summatory functions of `μ` and of Liouville's `λ`.

**Mertens.** `M(x) = Σ_{k ≤ x} μ(k)`, `|M(x)| ≤ x`, `L(μ, s) = 1/ζ(s)`. The transform of
`(c·x^θ − εM(x))/x` is `F(s) = c/(s − θ) − ε(s − 1)/(sZ(s))`, whose pole at a zero `ρ` of order `n` is
`h(s)/(s − ρ)ⁿ` with `h(ρ) = −ε(ρ − 1)/(ρg(ρ)) ≠ 0`.
* `zeta_ne_zero_of_mertens`: `εM(x) ≤ c·x^θ` on `(1, ∞)` (`ε ≠ 0`, `0 < θ ≤ 1`) makes `ζ ≠ 0` on
  `Re s > θ`.
* `mertens_omega`, `mertens_omega_half`: `M(x) = Ω±(x^θ)` below the real part of any zero, hence for
  every `0 < θ < ½` unconditionally.

**Liouville.** `L(x) = Σ_{k ≤ x} λ(k)`, `|L(x)| ≤ x`, and `L(λ, s)ζ(s) = ζ(2s)` (`LSeries_liouville`,
from the Euler products: `λ` is completely multiplicative with `λ(p) = −1`, and
`(1 + p^{−s})⁻¹(1 − p^{−s})⁻¹ = (1 − p^{−2s})⁻¹`). The transform is
`c/(s − θ) − εζ(2s)(s − 1)/(sZ(s))`, holomorphic on `Re s > θ ≥ ½` off the zeros; `ζ(2ρ) ≠ 0` there.
* `zeta_ne_zero_of_liouville`: `εL(x) ≤ c·x^θ` (`ε ≠ 0`, `½ ≤ θ ≤ 1`) makes `ζ ≠ 0` on `Re s > θ`.
* `rh_of_liouville_bound`: a one-sided bound `εL(x) ≤ c·√x` gives Mathlib's `RiemannHypothesis`.
* `rh_of_polya`: **Pólya's conjecture `L(x) ≤ 0` implies RH** (Pólya's conjecture is false, Haselgrove
  1958; the implication is classical).

No bearing on RH: these run from bounds on summatory functions to zeros, and no such bound is proved.
-/

open Real Complex MeasureTheory Filter Topology Set Metric ArithmeticFunction

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-- Coefficients bounded by `1` have `|S(x)| ≤ x`. -/
theorem linBound_of_abs_le_one {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) : LinBound f 1 := fun x hx => by
  unfold summ
  calc |∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k| ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := Finset.sum_le_sum fun k _ => hf k
    _ = ⌊x⌋₊ := by simp
    _ ≤ 1 * x := by rw [one_mul]; exact Nat.floor_le hx

/-- The Möbius summatory function `M(x)`. -/
abbrev fμ : ℕ → ℝ := fun n => (moebius n : ℝ)

theorem linBound_moebius : LinBound fμ 1 :=
  linBound_of_abs_le_one fun n => by
    show |((moebius n : ℤ) : ℝ)| ≤ 1; exact_mod_cast abs_moebius_le_one

theorem LSeries_moebius_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (fμ n : ℂ)) s = 1 / riemannZeta s := by
  have h := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h
  have hζ : riemannZeta s ≠ 0 := zeta_ne_zero_re_ge_one hs.le
  rw [eq_div_iff hζ, mul_comm, ← h]
  congr 1

theorem LSeriesSummable_moebius' {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (fμ n : ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    show |((moebius n : ℤ) : ℝ)| ≤ 1; exact_mod_cast abs_moebius_le_one) hs

/-- `F(s) = c/(s − θ) − ε(s − 1)/(sZ(s))`. -/
def FM (θ c ε : ℝ) (s : ℂ) : ℂ := c / (s - θ) - ε * ((s - 1) / (s * Zr s))

variable {θ c ε : ℝ}

theorem lap_eq_FM (hθ1 : θ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    lap μ1 (Aof fμ 0 θ c ε) Real.log s = FM θ c ε s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl _ hs
  have hζ : riemannZeta s ≠ 0 := zeta_ne_zero_re_ge_one hs.le
  rw [lap_Aof linBound_moebius hθ1 hs (LSeriesSummable_moebius' hs), LSeries_moebius_eq hs]
  unfold FM
  rw [Zr_of_ne hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  push_cast
  field_simp
  ring

theorem FM_differentiableAt {s : ℂ} (h1 : s ≠ θ) (h0 : s ≠ 0) (hZ : Zr s ≠ 0) :
    DifferentiableAt ℂ (FM θ c ε) s := by
  have hz : DifferentiableAt ℂ Zr s := differentiable_Zr s
  have hθ : s - θ ≠ 0 := sub_ne_zero.2 h1
  have hsz : s * Zr s ≠ 0 := mul_ne_zero h0 hZ
  unfold FM
  fun_prop (disch := assumption)

/-- A pole of the form `c/(s − θ) − ε·k(s)/(sZ(s))` at a zero of `Z`: the generic computation for
Mertens and Liouville. -/
theorem pole_of_div_Zr (hε : ε ≠ 0) {k : ℂ → ℂ} {ρ : ℂ} (hρθ : θ < ρ.re) (hθ : 0 < θ)
    (hk : ContinuousAt k ρ) (hk0 : k ρ ≠ 0) {n : ℕ} {g : ℂ → ℂ} (hn : n ≠ 0)
    (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0) (hZg : ∀ᶠ z in 𝓝 ρ, Zr z = (z - ρ) ^ n * g z) :
    PoleAt (fun s => c / (s - θ) - ε * (k s / (s * Zr s))) ρ := by
  have hρ0 : ρ ≠ 0 := fun e => by rw [e, zero_re] at hρθ; linarith
  obtain ⟨r0, hr0, hloc⟩ := local_factor hg hg0 hZg
  refine ⟨r0, hr0, fun z => c / (z - θ), fun z => -(ε * k z / (z * g z)), n, hn, ?_, ?_, ?_,
    fun x hx hxr => ?_⟩
  · have hθρ : ρ - θ ≠ 0 := fun e => by
      have := congrArg Complex.re e; simp at this; linarith
    exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) hθρ
  · exact ((continuousAt_const.mul hk).div (continuousAt_id.mul hg.continuousAt)
      (mul_ne_zero hρ0 hg0)).neg
  · exact neg_ne_zero.2 (div_ne_zero (mul_ne_zero (by exact_mod_cast hε) hk0) (mul_ne_zero hρ0 hg0))
  · obtain ⟨hZz, -, hgz0⟩ := hloc x hx hxr
    set z := ρ + (x : ℂ)
    have hu0 : z - ρ ≠ 0 := by simp only [z, add_sub_cancel_left]; exact_mod_cast hx.ne'
    have hz0 : z ≠ 0 := fun e => by
      have : (ρ + (x : ℂ)).re = ρ.re + x := by simp
      rw [show ρ + (x : ℂ) = z from rfl, e, zero_re] at this; linarith
    have hZz' : Zr z = (z - ρ) ^ n * g z := hZz.self_of_nhds
    show c / (z - θ) - ε * (k z / (z * Zr z)) = c / (z - θ) + -(ε * k z / (z * g z)) / (z - ρ) ^ n
    rw [hZz']
    have hpn : (z - ρ) ^ n ≠ 0 := pow_ne_zero _ hu0
    field_simp
    ring

/-- **A one-sided bound on Mertens' function is a zero-free half-plane.** -/
theorem zeta_ne_zero_of_mertens (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hε : ε ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ε * summ fμ x ≤ c * x ^ θ) {ρ : ℂ} (hρθ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  have h' : ∀ x : ℝ, 1 < x → ε * (summ fμ x - 0 * x) ≤ c * x ^ θ := fun x hx => by
    rw [zero_mul, sub_zero]; exact h x hx
  refine zeta_ne_zero_of_mellin (F := FM θ c ε) (R0 := 1) hθ (hyp_Aof h')
    (conv_Aof_three linBound_moebius hθ1) (fun s hs => (lap_eq_FM hθ1 hs).symm)
    (fun s hs hZ => FM_differentiableAt (fun e => by rw [e, ofReal_re] at hs; exact lt_irrefl _ hs)
      (fun e => by rw [e, zero_re] at hs; linarith) hZ)
    (fun ρ hρθ hρ1 _ n g hn hg hg0 hZg => ?_) hρθ
  have hρ1' : ρ - 1 ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  exact pole_of_div_Zr (k := fun s => s - 1) hε hρθ hθ (continuousAt_id.sub continuousAt_const)
    hρ1' hn hg hg0 hZg

/-- **`M(x) = Ω±(x^θ)`** for every zero `ρ` and every `0 < θ < Re ρ`. -/
theorem mertens_omega {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hθ : 0 < θ) (hθρ : θ < ρ.re) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < summ fμ x) ∧ (∃ x, X < x ∧ summ fμ x < -(c * x ^ θ)) := by
  have hρ1 : ρ.re < 1 := by by_contra h'; exact zeta_ne_zero_re_ge_one (not_lt.1 h') hρ
  have H := omega_of_zeroFree (κ := 0) linBound_moebius hθ (fun c ε hε h =>
    zeta_ne_zero_of_mertens (c := c) (ε := ε) hθ (by linarith) (by rcases hε with rfl | rfl <;> norm_num)
      (fun x hx => by have := h x hx; rwa [zero_mul, sub_zero] at this) hθρ hρ) c X
  simp only [zero_mul, sub_zero] at H
  exact H

/-- **`M(x) = Ω±(x^θ)` for every `0 < θ < ½`, unconditionally.** -/
theorem mertens_omega_half (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < summ fμ x) ∧ (∃ x, X < x ∧ summ fμ x < -(c * x ^ θ)) := by
  obtain ⟨ρ, hρ, hre⟩ := exists_zero_re_ge_half
  exact mertens_omega hρ hθ (by linarith) c X

/-! ## Liouville -/

/-- The Liouville summatory function `L(x)`. -/
abbrev fLi : ℕ → ℝ := fun n => (liouville n : ℝ)

theorem abs_liouville_le_one (n : ℕ) : |fLi n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fLi]
  · simp [fLi, liouville_apply hn]

theorem linBound_liouville : LinBound fLi 1 := linBound_of_abs_le_one abs_liouville_le_one

/-- `n ↦ λ(n)n^{−s}` is completely multiplicative. -/
def liouvilleSummandHom (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := (liouville n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp
  map_one' := by simp [liouville_apply_one]
  map_mul' m n := by
    have h : ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
      simpa only [Nat.cast_mul, ofReal_natCast]
        using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg (-s)
    simp only [liouville_apply_mul, Int.cast_mul, h]
    ring

/-- **`L(λ, s)·ζ(s) = ζ(2s)`** for `Re s > 1`, from the Euler products. -/
theorem LSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (fLi n : ℂ)) s * riemannZeta s = riemannZeta (2 * s) := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hsum : Summable fun n => ‖liouvilleSummandHom s n‖ := by
    refine (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    simp only [liouvilleSummandHom, riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have := abs_liouville_le_one n
    rw [show ((liouville n : ℤ) : ℂ) = ((fLi n : ℝ) : ℂ) by simp [fLi], Complex.norm_real,
      Real.norm_eq_abs]
    exact this
  have hL := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum
  have htsum : ∑' n, liouvilleSummandHom s n = LSeries (fun n => (fLi n : ℂ)) s := by
    simp only [liouvilleSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
      LSeries.term_of_ne_zero' hs0, div_eq_mul_inv, fLi]
    push_cast; rfl
  rw [htsum] at hL
  have hprime : ∀ p : Nat.Primes, liouvilleSummandHom s p = -((p : ℂ) ^ (-s)) := fun p => by
    simp only [liouvilleSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      liouville_apply p.2.ne_zero, cardFactors_apply_prime p.2]
    simp
  have hζ := riemannZeta_eulerProduct_hasProd hs
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hζ2 := riemannZeta_eulerProduct_hasProd hs2
  have hprod := hL.mul hζ
  refine hprod.unique ?_
  convert hζ2 using 1
  funext p
  rw [hprime, ← mul_inv, show -(2 * s) = ((2 : ℕ) : ℂ) * (-s) by push_cast; ring, cpow_nat_mul]
  congr 1
  ring

theorem LSeriesSummable_liouville {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n => (fLi n : ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_liouville_le_one n) hs

/-- `F(s) = c/(s − θ) − εζ(2s)(s − 1)/(sZ(s))`. -/
def FL (θ c ε : ℝ) (s : ℂ) : ℂ := c / (s - θ) - ε * (riemannZeta (2 * s) * (s - 1) / (s * Zr s))

theorem lap_eq_FL (hθ1 : θ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    lap μ1 (Aof fLi 0 θ c ε) Real.log s = FL θ c ε s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl _ hs
  have hζ : riemannZeta s ≠ 0 := zeta_ne_zero_re_ge_one hs.le
  have hL : LSeries (fun n => (fLi n : ℂ)) s = riemannZeta (2 * s) / riemannZeta s := by
    rw [eq_div_iff hζ]; exact LSeries_liouville hs
  rw [lap_Aof linBound_liouville hθ1 hs (LSeriesSummable_liouville hs), hL]
  unfold FL
  rw [Zr_of_ne hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  push_cast
  field_simp
  ring

theorem zeta_two_mul_differentiableAt {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun z => riemannZeta (2 * z)) s := by
  have h2 : 2 * s ≠ 1 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  exact (differentiableAt_riemannZeta h2).comp s (differentiableAt_id.const_mul 2)

theorem FL_differentiableAt (hθ : 1 / 2 ≤ θ) {s : ℂ} (hsθ : θ < s.re) (hZ : Zr s ≠ 0) :
    DifferentiableAt ℂ (FL θ c ε) s := by
  have h1 : s - θ ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  have h0 : s ≠ 0 := fun e => by rw [e, zero_re] at hsθ; linarith
  have hsz : s * Zr s ≠ 0 := mul_ne_zero h0 hZ
  have h2 : 2 * s ≠ 1 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  have hd : DifferentiableAt ℂ riemannZeta (2 * s) := differentiableAt_riemannZeta h2
  have hz : DifferentiableAt ℂ Zr s := differentiable_Zr s
  unfold FL
  fun_prop (disch := assumption)

/-- **A one-sided bound on Liouville's function is a zero-free half-plane** (`θ ≥ ½`). -/
theorem zeta_ne_zero_of_liouville (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hε : ε ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ε * summ fLi x ≤ c * x ^ θ) {ρ : ℂ} (hρθ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  have hθ0 : 0 < θ := by linarith
  have h' : ∀ x : ℝ, 1 < x → ε * (summ fLi x - 0 * x) ≤ c * x ^ θ := fun x hx => by
    rw [zero_mul, sub_zero]; exact h x hx
  refine zeta_ne_zero_of_mellin (F := FL θ c ε) (R0 := 1) hθ0 (hyp_Aof h')
    (conv_Aof_three linBound_liouville hθ1) (fun s hs => (lap_eq_FL hθ1 hs).symm)
    (fun s hs hZ => FL_differentiableAt hθ hs hZ) (fun ρ hρθ hρ1 _ n g hn hg hg0 hZg => ?_) hρθ
  have hρ1' : ρ - 1 ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  have h2 : riemannZeta (2 * ρ) ≠ 0 := zeta_ne_zero_re_ge_one (by simp; linarith)
  have hk : ContinuousAt (fun s => riemannZeta (2 * s) * (s - 1)) ρ :=
    ((zeta_two_mul_differentiableAt (by linarith)).continuousAt).mul
      (continuousAt_id.sub continuousAt_const)
  exact pole_of_div_Zr (k := fun s => riemannZeta (2 * s) * (s - 1)) hε hρθ hθ0 hk
    (mul_ne_zero h2 hρ1') hn hg hg0 hZg

/-- **A one-sided bound `εL(x) ≤ c√x` gives RH.** -/
theorem rh_of_liouville_bound (hε : ε ≠ 0) (h : ∀ x : ℝ, 1 < x → ε * summ fLi x ≤ c * x ^ (1 / 2 : ℝ)) :
    RiemannHypothesis :=
  rh_of_zeroFree_half fun _ hρ => zeta_ne_zero_of_liouville (le_refl _) (by norm_num) hε h hρ

/-- The hypothesis "`L(x) ≤ 0` for every `x > 1`" is refutable: `L(3/2) = λ(1) = 1`. Pólya's
conjecture starts at `x = 2` (round 238). -/
theorem polya_hyp_false : ¬ (∀ x : ℝ, 1 < x → summ fLi x ≤ 0) := by
  intro h
  have h1 := h (3 / 2) (by norm_num)
  have e : summ fLi (3 / 2) = 1 := by
    unfold summ
    have : ⌊(3 / 2 : ℝ)⌋₊ = 1 := by rw [Nat.floor_eq_iff (by norm_num)]; norm_num
    rw [this]; simp [fLi, ArithmeticFunction.liouville_apply]
  linarith

/-- **Pólya's conjecture implies RH**: if `L(x) ≤ 0` for every `x ≥ 2`, Mathlib's `RiemannHypothesis`
holds. (Pólya's conjecture is false: Haselgrove 1958; Tanaka 1980, `L(906150257) = 1`.) Until
round 238 the hypothesis was stated for every `x > 1`, which is refutable (`polya_hyp_false`), so
the theorem was vacuous; on `1 < x < 2` one has `L(x) = 1 ≤ √x`, which is what `c = 1` absorbs. -/
theorem rh_of_polya (h : ∀ x : ℝ, 2 ≤ x → summ fLi x ≤ 0) : RiemannHypothesis :=
  rh_of_liouville_bound (c := 1) (ε := 1) one_ne_zero fun x hx => by
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hr : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rcases le_or_gt 2 x with h2 | h2
    · have := h x h2; linarith
    · have e : summ fLi x = 1 := by
        unfold summ
        have : ⌊x⌋₊ = 1 := by rw [Nat.floor_eq_iff hx0]; constructor <;> push_cast <;> linarith
        rw [this]; simp [fLi, ArithmeticFunction.liouville_apply]
      rw [e]; linarith

end PsiOmega

#print axioms PsiOmega.zeta_ne_zero_of_mertens
#print axioms PsiOmega.mertens_omega_half
#print axioms PsiOmega.LSeries_liouville
#print axioms PsiOmega.zeta_ne_zero_of_liouville
#print axioms PsiOmega.rh_of_liouville_bound
#print axioms PsiOmega.polya_hyp_false
#print axioms PsiOmega.rh_of_polya
