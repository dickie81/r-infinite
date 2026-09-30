import MertensOmega
import ZetaInputs
import ShortPrimes
import KaiserNine
import ZeroLocal
import WeilLandau
import SixteenPi
import HadamardApply

/-! # Joins on the `ζ` side (round 244)

One-sided Chebyshev or Mertens bounds `ε(ψ(x) − x) ≤ c x^θ` give the twin form's exponential rate
`2θ − 1` (`weil_rate_of_psi_bound`, `weil_rate_of_mertens_bound`); one-sided upper bounds at every
`θ > ½` give RH (`rh_of_psi_upper`); `pinned_zeta` concludes a genuine zero of `ĝ`
(`pinned_zeta_zero`); the first instance of `SixteenPi.multiplier_expansion`, at `(ĝ_a, Ξ)`, with
the probe side in closed form (`multiplier_time_probe`); and **RH gives a prime in `(y, y + y^θ]` for
every `θ > ½`** (`short_primes_of_RH`), the RH endpoint of round 235's parametric theorem.
-/

open Real Complex Set Filter Topology
open Pilot1ca Pilot1bt PilotWeil

namespace ZetaJoins

/-! ### A3. Chebyshev / Mertens one-sided bounds give the twin form's exponential rate
(PsiOmega, MertensOmega → WeilLandau). -/
theorem weil_rate_of_psi_bound {θ c ε : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hε : ε ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ε * (Chebyshev.psi x - x) ≤ c * x ^ θ) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp ((2 * θ - 1) * l)) ≤
      weilQ (l + 1) (twin (box 1) l) := by
  refine (weil_twins_rate (by linarith)).2 fun s hs => ?_
  have hθ0 : 0 < θ := by linarith
  have h1 : s.re ≤ θ := by
    by_contra hc
    exact PsiOmega.zeta_ne_zero_of_psi hθ0 hθ1 hε h (not_le.1 hc) hs.1
  have h2 : (1 - s).re ≤ θ := by
    by_contra hc
    exact PsiOmega.zeta_ne_zero_of_psi hθ0 hθ1 hε h (not_le.1 hc)
      (PsiOmega.IsNontrivialZero.one_sub hs).1
  rw [Complex.sub_re, Complex.one_re] at h2
  rw [abs_le]; constructor <;> linarith

theorem weil_rate_of_mertens_bound {θ c ε : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hε : ε ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ε * PsiOmega.summ PsiOmega.fμ x ≤ c * x ^ θ) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp ((2 * θ - 1) * l)) ≤
      weilQ (l + 1) (twin (box 1) l) := by
  refine (weil_twins_rate (by linarith)).2 fun s hs => ?_
  have hθ0 : 0 < θ := by linarith
  have h1 : s.re ≤ θ := by
    by_contra hc
    exact PsiOmega.zeta_ne_zero_of_mertens hθ0 hθ1 hε h (not_le.1 hc) hs.1
  have h2 : (1 - s).re ≤ θ := by
    by_contra hc
    exact PsiOmega.zeta_ne_zero_of_mertens hθ0 hθ1 hε h (not_le.1 hc)
      (PsiOmega.IsNontrivialZero.one_sub hs).1
  rw [Complex.sub_re, Complex.one_re] at h2
  rw [abs_le]; constructor <;> linarith

/-! ### A4. One-sided upper bounds `ψ(x) − x ≤ c_θ x^θ` for every `θ > 1/2` give RH. -/
theorem rh_of_psi_upper
    (h : ∀ θ : ℝ, 1 / 2 < θ → θ ≤ 1 → ∃ c : ℝ, ∀ x : ℝ, 1 < x → Chebyshev.psi x - x ≤ c * x ^ θ) :
    RiemannHypothesis := by
  intro s hs htriv _
  have hs' : Pilot1bt.IsNontrivialZero s := ⟨hs, htriv⟩
  have key : ∀ θ, 1 / 2 < θ → θ ≤ 1 → s.re ≤ θ ∧ 1 - s.re ≤ θ := by
    intro θ hθ hθ1
    obtain ⟨c, hc⟩ := h θ hθ hθ1
    have hc' : ∀ x : ℝ, 1 < x → (1 : ℝ) * (Chebyshev.psi x - x) ≤ c * x ^ θ :=
      fun x hx => by simpa using hc x hx
    constructor
    · by_contra hlt
      exact PsiOmega.zeta_ne_zero_of_psi (by linarith) hθ1 one_ne_zero hc' (not_le.1 hlt) hs
    · by_contra hlt
      refine PsiOmega.zeta_ne_zero_of_psi (by linarith) hθ1 one_ne_zero hc' (ρ := 1 - s) ?_
        (PsiOmega.IsNontrivialZero.one_sub hs').1
      rw [Complex.sub_re, Complex.one_re]; exact not_le.1 hlt
  have hlt1 := hs'.re_lt_one
  have hpos := hs'.re_pos
  have hA : s.re ≤ 1 / 2 := by
    by_contra hgt
    have := (key ((1 / 2 + s.re) / 2) (by linarith [not_le.1 hgt]) (by linarith)).1
    linarith [not_le.1 hgt]
  have hB : 1 - s.re ≤ 1 / 2 := by
    by_contra hgt
    have := (key ((1 / 2 + (1 - s.re)) / 2) (by linarith [not_le.1 hgt]) (by linarith)).2
    linarith [not_le.1 hgt]
  linarith

/-! ### A6. Round 241's fix, applied to the ζ instance: `pinned_zeta` concludes `(ĝ x).re = 0`; `ĝ x = 0` follows. -/
theorem pinned_zeta_zero {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hp : Probe a g)
    (hmono : AntitoneOn g (Icc 0 a)) (hnn : ∀ u ∈ Icc 0 a, 0 ≤ g u) {H : ℝ} (hH : 1 ≤ H)
    (hRH : ∀ p, |((zetaZeroFamily p - 1 / 2) / I).re| ≤ H → ((zetaZeroFamily p - 1 / 2) / I).im = 0)
    (j : Σ w : NontrivialZero, Fin (zeroMult w)) (hj : |((zetaZeroFamily j - 1 / 2) / I).re| ≤ H)
    {m r : ℝ} (hm : 0 < m)
    (hr : Real.sqrt (weilQ a g + (2 * g 0 * Real.cosh (a / 2)) ^ 2 *
      (∑' p, if H < |((zetaZeroFamily p - 1 / 2) / I).re|
        then 1 / ((zetaZeroFamily p - 1 / 2) / I).re ^ 2 else 0)) / m ≤ r)
    (hc : ContinuousOn (fun x : ℝ => (ghatC g a x).re)
      (Icc (((zetaZeroFamily j - 1 / 2) / I).re - r) (((zetaZeroFamily j - 1 / 2) / I).re + r)))
    (hd : DifferentiableOn ℝ (fun x : ℝ => (ghatC g a x).re)
      (Ioo (((zetaZeroFamily j - 1 / 2) / I).re - r) (((zetaZeroFamily j - 1 / 2) / I).re + r)))
    (hslope : (∀ x ∈ Ioo (((zetaZeroFamily j - 1 / 2) / I).re - r)
        (((zetaZeroFamily j - 1 / 2) / I).re + r), m ≤ deriv (fun x : ℝ => (ghatC g a x).re) x) ∨
      (∀ x ∈ Ioo (((zetaZeroFamily j - 1 / 2) / I).re - r)
        (((zetaZeroFamily j - 1 / 2) / I).re + r), deriv (fun x : ℝ => (ghatC g a x).re) x ≤ -m)) :
    ∃ x ∈ Icc (((zetaZeroFamily j - 1 / 2) / I).re - Real.sqrt (weilQ a g + (2 * g 0 * Real.cosh (a / 2)) ^ 2 *
        (∑' p, if H < |((zetaZeroFamily p - 1 / 2) / I).re|
          then 1 / ((zetaZeroFamily p - 1 / 2) / I).re ^ 2 else 0)) / m)
      (((zetaZeroFamily j - 1 / 2) / I).re + Real.sqrt (weilQ a g + (2 * g 0 * Real.cosh (a / 2)) ^ 2 *
        (∑' p, if H < |((zetaZeroFamily p - 1 / 2) / I).re|
          then 1 / ((zetaZeroFamily p - 1 / 2) / I).re ^ 2 else 0)) / m), ghatC g a x = 0 := by
  obtain ⟨x, hx, hre⟩ := pinned_zeta ha hp hmono hnn hH hRH j hj hm hr hc hd hslope
  exact ⟨x, hx, Complex.ext (by simpa using hre)
    (by simpa using ghatC_im_eq_zero hp.even hp.intervalIntegrable x)⟩

/-! ### A7. The first instance of `SixteenPi.multiplier_expansion` (at `(ĝ_a, Ξ)`), with the probe side in
closed form by the curvature sum rule. -/
theorem multiplier_time_probe {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hg : IntervalIntegrable g MeasureTheory.volume (-a) a) (heven : ∀ u, g (-u) = g u)
    (h0 : ghatC g a 0 ≠ 0) (z : ℂ)
    (hz : ‖z‖ ^ 2 * ((∑' i : ZeroIdx (sqF (ghatC g a)), ‖i.1⁻¹‖)
      + ∑' j : ZeroIdx (sqF Xi), ‖j.1⁻¹‖) ≤ 1) :
    ‖ghatC g a z / ghatC g a 0 - Xi z / Xi 0
        * (1 + z ^ 2 * ((∑' j : ZeroIdx (sqF Xi), j.1⁻¹)
          - (((∫ u in (-a)..a, u ^ 2 * g u) / (2 * ∫ u in (-a)..a, g u) : ℝ) : ℂ)))‖
      ≤ 3 * ‖z‖ ^ 4 * ((∑' i : ZeroIdx (sqF (ghatC g a)), ‖i.1⁻¹‖)
        + ∑' j : ZeroIdx (sqF Xi), ‖j.1⁻¹‖) ^ 2 := by
  have := multiplier_expansion (hadamardW_ghat ha hg heven h0)
    (hadamardW_Xi xiGrowth Xi_zero_ne_zero) z hz
  rwa [ghat_sum_rule ha hg heven h0] at this

/-! ### A8. RH gives primes in `(y, y + y^θ]` for every `θ > 1/2`
(KaiserNine + ZeroLocal → ShortPrimes.short_primes_of_density with `A = 2`, `α = 1/2`). -/
theorem short_primes_of_RH (hRH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  have him : ∀ i : ZeroIdx (sqF Xi), (tau i).im = 0 := Kaiser.tau_im_eq_zero_of_RH hRH
  have hzf : ShortWeil.ZeroFreeXi (1 / 2) := by
    refine ⟨1 / 2, Real.exp 1, by norm_num, fun T hT i _ => ?_⟩
    rw [him i, abs_zero]
    have hlog : 1 ≤ Real.log T := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT
    have : (1 / 2 : ℝ) / Real.log T ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
      apply div_le_self (by norm_num)
      exact Real.one_le_rpow hlog (by norm_num)
    linarith
  have hden : ShortWeil.DensityXi 2 1 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hkl := ShortWeil.kLam_nonneg
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 13 / 2 * ((5 + Kaiser.kLam) / Real.log 2 + 1) := ⟨_, rfl⟩
    have hc0 : 0 ≤ c := by
      rw [hc]
      have h5 : 0 ≤ (5 + Kaiser.kLam) / Real.log 2 := div_nonneg (by linarith) hlog2.le
      linarith
    refine ⟨2 * c, by linarith, fun T hT w hw0 hw => ?_⟩
    have hT1 : 1 ≤ T := by linarith
    have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    have hKloc : ShortWeil.Kloc T ≤ c * Real.log T := by
      unfold ShortWeil.Kloc; rw [hc]
      have h1 : Real.log (T + 2) ≤ 2 * Real.log T := by
        rw [show 2 * Real.log T = Real.log (T ^ 2) by rw [Real.log_pow]; push_cast; ring]
        exact Real.log_le_log (by linarith) (by nlinarith)
      have h2 : 5 + Kaiser.kLam ≤ (5 + Kaiser.kLam) / Real.log 2 * Real.log T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left hlogT (by linarith)
      nlinarith
    have hsub : {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T ∧ w ≤ |(tau i).im|}
        ⊆ {i | |(tau i).re| ≤ T} := fun i hi => hi.1
    have hcard : ((ShortWeil.NX w T : ℕ) : ℝ) ≤ (T + 1) * ShortWeil.Kloc T := by
      refine le_trans ?_ (ShortWeil.card_re_le (by linarith))
      unfold ShortWeil.NX
      have := Set.ncard_le_ncard hsub (ShortWeil.finite_re_le T)
      rw [Set.ncard_eq_toFinset_card _ (ShortWeil.finite_re_le T)] at this
      exact_mod_cast this
    rcases eq_or_lt_of_le hw0 with hw0' | hwpos
    · subst hw0'
      norm_num
      have hprod : 0 ≤ (T - 1) * (c * Real.log T) :=
        mul_nonneg (by linarith) (mul_nonneg hc0 hlogT0)
      nlinarith [mul_le_mul_of_nonneg_left hKloc (by linarith : (0 : ℝ) ≤ T + 1), hcard]
    · have hempty : {i : ZeroIdx (sqF Xi) |
          |(tau i).re| ≤ T ∧ w ≤ |(tau i).im|} = ∅ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
        intro _; rw [him i, abs_zero]; exact hwpos
      unfold ShortWeil.NX
      rw [hempty, Set.ncard_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (by linarith)
        (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg hlogT0 _)
  exact ShortWeil.short_primes_of_density (by norm_num) (by norm_num) hden hzf hθ (by linarith)

end ZetaJoins

#print axioms ZetaJoins.weil_rate_of_psi_bound
#print axioms ZetaJoins.weil_rate_of_mertens_bound
#print axioms ZetaJoins.rh_of_psi_upper
#print axioms ZetaJoins.pinned_zeta_zero
#print axioms ZetaJoins.multiplier_time_probe
#print axioms ZetaJoins.short_primes_of_RH
