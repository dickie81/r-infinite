import Mathlib
import ExteriorZeta
import WeilLandau

/-! # RH gives `Q ≥ 0` on every probe, and Weil's criterion for `ζ` (round 157)

Round 129's `weilQ_nonneg_of_zeros_on_line` needs the explicit formula for the probe at hand, and
round 156 proves it only for strip test functions. Here the gap is closed by density:

* `ibp_C2`: for a `C²` probe vanishing near the edges, `it·ĝ(t) = −ĝ₁(t)`, so `ĝ²` is a strip test
  function (`weilExplicit_C2_zeta`).
* `lam_nonneg_of_RH`: under Mathlib's `RiemannHypothesis`, `λ₁(a) ≥ 0` at every support. If
  `λ₁ < 0`, a ground state `g` is approximated (round 55's `av3_dense`) by a `C²` probe `h` with
  `Q(h) ≤ λ₁‖h‖² + 2C(‖h − g‖² + E(h − g)) < 0`, while RH and the explicit formula give `Q(h) ≥ 0`.
* `weilQ_nonneg_of_RH`: hence `Q(g) ≥ λ₁‖g‖² ≥ 0` for every probe.
* `weil_criterion_zeta`: `Q ≥ 0` on every probe **iff** Mathlib's `RiemannHypothesis`. No named
  input, and (since round 220, `WeilLandau.rh_of_weil`) no finiteness hypothesis.

Weil's criterion is an equivalence: no bearing on RH.
-/

open Real Filter Topology Complex Set MeasureTheory

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## `C²` probes are strip test functions -/

/-- **Integration by parts on `[−a, a]`** for a `C²` function vanishing outside `[−r, r]`, `r ≤ a`. -/
theorem ibp_C2 {a r : ℝ} {h h₁ h₂ : ℝ → ℝ} (hc : C2Supp r h h₁ h₂) (hr : 0 ≤ r) (hra : r ≤ a)
    (t : ℂ) : I * t * ghatC h a t = -ghatC h₁ a t := by
  have hc1 : Continuous h₁ := continuous_iff_continuousAt.2 fun x => (hc.d2 x).continuousAt
  have hc0 : Continuous h := continuous_iff_continuousAt.2 fun x => (hc.d1 x).continuousAt
  have z1 : h a = 0 := zero_of_ge hr hc0 hc.supp a (by rw [abs_of_nonneg (by linarith)]; exact hra)
  have z2 : h (-a) = 0 :=
    zero_of_ge hr hc0 hc.supp (-a) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hra)
  rw [ibp_ghatC (fun x _ => hc.d1 x) (hc1.intervalIntegrable _ _) t, z1, z2]
  simp

/-- **`ĝ²` is a strip test function for every `C²` probe vanishing near the edges.** -/
theorem striptest_C2 {a r : ℝ} {h h₁ h₂ : ℝ → ℝ} (ha : 0 < a) (hp : Probe a h)
    (hc : C2Supp r h h₁ h₂) (hr : 0 ≤ r) (hra : r ≤ a) :
    ∃ K, StripTest (fun z => ghatC h a z ^ 2) K := by
  have hc1 : Continuous h₁ := continuous_iff_continuousAt.2 fun x => (hc.d2 x).continuousAt
  have hi1 : IntervalIntegrable h₁ volume (-a) a := hc1.intervalIntegrable _ _
  obtain ⟨K, hK⟩ := ghat_strip_of_inv ha.le (B := Real.exp a * ∫ u in (-a)..a, |h₁ u|)
    (mul_nonneg (Real.exp_pos a).le (intervalIntegral.integral_nonneg (by linarith)
      fun _ _ => abs_nonneg _)) hp.intervalIntegrable fun t ht ht0 => by
      have hn : 0 < ‖t‖ := norm_pos_iff.2 ht0
      rw [le_div_iff₀ hn]
      have e : ‖ghatC h a t‖ * ‖t‖ = ‖ghatC h₁ a t‖ := by
        rw [← norm_neg (ghatC h₁ a t), ← ibp_C2 hc hr hra t, norm_mul, norm_mul, Complex.norm_I,
          one_mul, mul_comm]
      rw [e]
      exact norm_ghatC_strip_le ha.le hi1 (abs_le.2 ⟨ht.1, ht.2⟩)
  exact ⟨K, striptest_sq (ghatC_differentiable hp.intervalIntegrable) hK⟩

/-- **The explicit formula over the zeros of `ζ` for every `C²` probe vanishing near the edges.** -/
theorem weilExplicit_C2_zeta {a r : ℝ} {h h₁ h₂ : ℝ → ℝ} (ha : 0 < a) (hp : Probe a h)
    (hc : C2Supp r h h₁ h₂) (hr : 0 ≤ r) (hra : r ≤ a) :
    WeilExplicit zetaZeroFamily (fun z => ghatC h a z ^ 2) (hsq h a) := by
  obtain ⟨K, hK⟩ := striptest_C2 ha hp hc hr hra
  exact weilExplicit_zeta hK (fun t => even_ghat_sq hp.even a t) (hsq_ofReal hp ha.le)

/-! ## RH ⇒ `Q ≥ 0` on every probe -/

theorem line_of_RH (hRH : RiemannHypothesis) (i : Σ w : NontrivialZero, Fin (zeroMult w)) :
    (zetaZeroFamily i).re = 1 / 2 := by
  have hz := i.1.2
  refine hRH _ hz.1 hz.2 fun h1 => ?_
  have h0 := hz.1
  change riemannZeta (zetaZeroFamily i) = 0 at h0
  rw [h1] at h0
  exact riemannZeta_one_ne_zero h0

theorem normSq_sub_comm (g h : ℝ → ℝ) : normSq (fun u => g u - h u) = normSq (fun u => h u - g u) := by
  unfold normSq; congr 1; funext u; ring

/-- **Under RH, the ground energy is nonnegative at every support.** -/
theorem lam_nonneg_of_RH (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a) : 0 ≤ lam a := by
  by_contra hneg
  push Not at hneg
  set L := lam a
  obtain ⟨g, hg⟩ := exists_groundState ha
  have hgq : weilQ a g = L := weilQ_eq_lam ha hg
  obtain ⟨C, hC, hCle⟩ := Qlam_le_d ha
  have hden : 0 < 2 * C - L := by linarith
  set ε := -L / (8 * (2 * C - L))
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  obtain ⟨ρ, δ, ψ, hρ0, hδ, hρ, hψ, h1, h2⟩ := av3_dense ha hg.1 ε hε
  set h := Av δ (Av δ (Av δ ψ))
  have hp : Probe a h := (probe_Av (probe_Av (probe_Av hψ hδ) hδ) hδ).mono (by linarith)
  have hc := av3_C2 hδ hψ
  have hQh : 0 ≤ weilQ a h :=
    weilQ_nonneg_of_zeros_on_line hp ha (weilExplicit_C2_zeta ha hp hc (by positivity) hρ)
      (line_of_RH hRH)
  set e : ℝ → ℝ := fun t => h t - g t
  have pe : Probe a e := (probe_add_sub hp hg.1).2
  -- `Q_λ(h) ≤ 2Q_λ(g) + 2Q_λ(h − g)`, and `Q_λ(g) = 0`
  have hadd := Qlam_add_le hg.1 pe one_pos
  have hfun : (fun u => g u + e u) = h := by funext u; simp only [e]; ring
  rw [hfun] at hadd
  have hQg : Qlam a g = 0 := by unfold Qlam; rw [hgq, hg.2.1]; ring
  have hQe : Qlam a e ≤ C * (normSq e + archE e) := hCle e pe
  have hd : normSq e + archE e ≤ 2 * ε := by linarith
  have hQh' : weilQ a h - L * normSq h ≤ 4 * C * ε := by
    have : Qlam a h ≤ 2 * (C * (normSq e + archE e)) := by
      rw [hQg] at hadd; norm_num at hadd; linarith
    unfold Qlam at this
    nlinarith
  -- `‖h‖² ≥ ½ − ε`
  have hN := normSq_add_le_t (x := h) (y := fun u => g u - h u) hp.memL2
    (hg.1.memL2.sub hp.memL2) one_pos
  have hfun2 : (fun u => h u + (g u - h u)) = g := by funext u; ring
  rw [hfun2, hg.2.1, normSq_sub_comm] at hN
  have hNe : normSq e ≤ ε := h1
  have hNh : 1 / 2 - ε ≤ normSq h := by
    have : normSq (fun u => h u - g u) ≤ ε := hNe
    norm_num at hN; linarith
  -- contradiction
  have hLN : L * normSq h ≤ L * (1 / 2 - ε) := mul_le_mul_of_nonpos_left hNh hneg.le
  have hkey : ε * (4 * C - L) ≤ -L / 4 := by
    have e1 : ε * (4 * C - L) = -L / 8 * ((4 * C - L) / (2 * C - L)) := by
      simp only [ε]; field_simp
    have e2 : (4 * C - L) / (2 * C - L) ≤ 2 := by
      rw [div_le_iff₀ hden]; linarith
    rw [e1]
    have : 0 ≤ -L / 8 := by linarith
    nlinarith
  nlinarith

/-- **RH ⇒ Weil positivity on every probe, at every support.** -/
theorem weilQ_nonneg_of_RH (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Probe a g) : 0 ≤ weilQ a g :=
  le_trans (mul_nonneg (lam_nonneg_of_RH hRH ha) (normSq_nonneg g)) (lam_mul_le hg)

/-- **Weil's criterion for `ζ`, both directions, no named input, no finiteness hypothesis.** Weil's
form is nonnegative on every probe at every support if and only if Mathlib's `RiemannHypothesis`
holds. -/
theorem weil_criterion_zeta :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ weilQ a g) ↔ RiemannHypothesis :=
  ⟨rh_of_weil, fun hRH _ _ ha hp => weilQ_nonneg_of_RH hRH ha hp⟩

end Pilot1ca

#print axioms Pilot1ca.ibp_C2
#print axioms Pilot1ca.striptest_C2
#print axioms Pilot1ca.weilExplicit_C2_zeta
#print axioms Pilot1ca.lam_nonneg_of_RH
#print axioms Pilot1ca.weilQ_nonneg_of_RH
#print axioms Pilot1ca.weil_criterion_zeta
