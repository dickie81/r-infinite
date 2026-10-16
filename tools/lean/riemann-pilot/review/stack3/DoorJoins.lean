import WeilTwinGeneral
import HalfPlaneJoinsFinal
import CrossCriteria
import MertensExponent
import LandauKV

/-! # Stack review 3: joins from the half-plane and from `Θ` into older sockets

* (J1) Every real-rooted monotone base probe has twin rate `5/6` (round 468 states the rate for `box 1` only).
* (J2) The graded Weil criterion with `Θ`: the twin form `Q(twin (box 1) λ) ≥ −C e^{σλ}` iff `2Θ − 1 ≤ σ`
  (`weil_twins_rate`'s docstring says this in prose).
* (J3) `¬RH → PsiOmegaSqrt`: half of `CrossCriteria.PsiOmegaSqrt`, from round 469's `psi_omega_Theta` and
  round 472's `rh_iff_Theta_eq_half`.
* (J4) `zeroFree_KV` with the explicit constant `A = 1/6`, from round 466's half-plane. -/

open Complex Filter
open scoped Chebyshev
open Pilot1ca Pilot1bt PilotWeil PsiOmega HalfPlaneS0 PsiExponent

namespace StackReview3

/-- **(J1)** Every real-rooted monotone base probe: `Q(twin g₀ λ) ≥ −C e^{5λ/6}`. -/
theorem realRooted_rate_eleven_twelfths {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Set.Icc 0 b)) (hnn : ∀ u ∈ Set.Icc 0 b, 0 ≤ g₀ u) (hRR : RealRooted b g₀) :
    ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (5 / 6 * l)) ≤ weilQ (l + b) (twin g₀ l) :=
  (WeilTwinGeneral.twins_rate_realRooted hb hp hmono hnn hRR (by norm_num)).2
    fun _ hs => HalfPlaneJoins.zeta_band_eleven_twelfths hs

/-- **(J2)** The exponential rate of the negative part of `ζ`'s twin form is exactly `2Θ − 1`. -/
theorem weil_twins_rate_Theta {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ weilQ (l + 1) (twin (box 1) l)) ↔
      2 * Theta - 1 ≤ σ := by
  rw [weil_twins_rate hσ]
  constructor
  · intro h
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨ρ, hρ, hre⟩ := exists_zero_re_gt (ε := ε / 2) (by positivity)
    have := (abs_le.1 (h ρ hρ)).2
    linarith
  · intro h s hs
    exact (band_of_zeroFree (fun _ hρ => zeta_ne_zero_of_Theta_lt hρ) hs).trans h

/-- **(J3)** If RH fails, `ψ(x) − x = Ω±(√x)`. -/
theorem psiOmegaSqrt_of_not_RH (h : ¬ RiemannHypothesis) : CrossCriteria.PsiOmegaSqrt := by
  have hΘ : 1 / 2 < Theta := by
    rcases half_le_Theta.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (MertensExponent.rh_iff_Theta_eq_half.2 h'.symm) h
  set ε := (Theta - 1 / 2) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hεΘ : ε < Theta := by rw [hεdef]; linarith
  have hexp : (1 / 2 : ℝ) ≤ Theta - ε := by rw [hεdef]; linarith
  refine ⟨1, one_pos, fun X => ?_⟩
  obtain ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩ := psi_omega_Theta hε hεΘ 1 (max X 1)
  have hx1' : 1 ≤ x1 := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx1)
  have hx2' : 1 ≤ x2 := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx2)
  have e1 := Real.rpow_le_rpow_of_exponent_le hx1' hexp
  have e2 := Real.rpow_le_rpow_of_exponent_le hx2' hexp
  refine ⟨⟨x1, lt_of_le_of_lt (le_max_left _ _) hx1, ?_⟩, ⟨x2, lt_of_le_of_lt (le_max_left _ _) hx2, ?_⟩⟩
  · linarith
  · linarith

/-- **(J4)** `zeroFree_KV` with `A = 1/6`: for `|t| ≥ e³` the region lies in `Re s > 11/12`. -/
theorem zeroFree_KV_explicit : ∀ σ t : ℝ, Real.exp 3 ≤ |t| →
    1 - (1 / 6) / (Real.log |t| ^ ((2 : ℝ) / 3) * Real.log (Real.log |t|) ^ ((1 : ℝ) / 3)) ≤ σ →
    riemannZeta (σ + t * I) ≠ 0 := by
  intro σ t ht hσ
  have hl3 : 3 ≤ Real.log |t| := by
    rw [← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) ht
  have hll : 1 ≤ Real.log (Real.log |t|) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have h2 : (2 : ℝ) < Real.log |t| ^ ((2 : ℝ) / 3) := by
    have h3 : (3 : ℝ) ^ ((2 : ℝ) / 3) ≤ Real.log |t| ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by norm_num) hl3 (by norm_num)
    have h8 : (2 : ℝ) < 3 ^ ((2 : ℝ) / 3) := by
      have hc : ((2 : ℝ) ^ (3 : ℝ)) < ((3 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
      exact (Real.rpow_lt_rpow_iff (by norm_num) (by positivity) (by norm_num)).1 hc
    linarith
  have h1 : 1 ≤ Real.log (Real.log |t|) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hll (by norm_num)
  have hD : 2 < Real.log |t| ^ ((2 : ℝ) / 3) * Real.log (Real.log |t|) ^ ((1 : ℝ) / 3) := by
    nlinarith
  have hq : (1 / 6) / (Real.log |t| ^ ((2 : ℝ) / 3) * Real.log (Real.log |t|) ^ ((1 : ℝ) / 3)) < 1 / 12 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  refine (Eis.ne_zero_of_re_gt_eleven_twelfths ?_).1
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
  linarith

end StackReview3

#print axioms StackReview3.realRooted_rate_eleven_twelfths
#print axioms StackReview3.weil_twins_rate_Theta
#print axioms StackReview3.psiOmegaSqrt_of_not_RH
#print axioms StackReview3.zeroFree_KV_explicit
