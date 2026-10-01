import Mathlib
import DHPacket
import DHArch
import DHTerms
import DHConstants

/-! # the certificate — `Q_dh(packet 12/5 169/2) < 0`, hence an off-line zero of `dh` (stage 4) -/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

theorem floor_exp_twoA : ⌊Real.exp (2 * (12 / 5 : ℝ))⌋₊ = 121 := by
  rw [Nat.floor_eq_iff (Real.exp_pos _).le]
  have h121 := PsiOmega.Num.log_bound_121
  have b := PsiOmega.Num.log_one_add_inv_bounds (m := 121) (by norm_num) 1
  set y := Real.log (1 + ((121 : ℕ) : ℝ)⁻¹) with hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at b
  norm_num at b
  have e122 : Real.log (122 : ℝ) = Real.log 121 + y := by
    rw [hy, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  constructor
  · have h : Real.log (121 : ℝ) ≤ 2 * (12 / 5) := by linarith [h121.2]
    have := (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 121)).1 h
    exact_mod_cast this
  · have h : 2 * (12 / 5 : ℝ) < Real.log 122 := by rw [e122]; linarith [h121.1, b.1]
    have := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 122)).1 h
    push_cast
    linarith

/-- **`Q_dh(packet 12/5 169/2) < 0`.** -/
theorem QDHu_packet_neg : QDHu (packet (12 / 5) (169 / 2)) < 0 := by
  rw [QDHu_packet_eq (by norm_num) (by norm_num), floor_exp_twoA]
  have hsum : ∑ n ∈ Finset.Icc 2 121, fDH n / Real.sqrt n
      * ((2 * (12 / 5) - Real.log n) / 2 * Real.cos (169 / 2 * Real.log n)
        + Real.sin (169 / 2 * (2 * (12 / 5) - Real.log n)) / (2 * (169 / 2)))
      = ∑ n ∈ Finset.Icc 2 121, primeTerm n := rfl
  rw [hsum]
  have hS := partial_121
  have hA := packet_arch_total_le (a := 12 / 5) (ω := 169 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hf0 := PsiOmega.Num.normSq_packet_bounds
  have hL := PsiOmega.Num.log_sqrt_z_bounds
  have hlog5 := PsiOmega.Num.log_bound_5
  have hpi := PsiOmega.Num.log_pi_bounds
  have h2aw := PsiOmega.Num.log_two_a_omega_bounds
  have hexp := PsiOmega.Num.exp_neg_three_a_le
  have hexp4 := PsiOmega.Num.one_sub_exp_neg_four_a_ge
  -- normalise the numerals appearing in `hA`
  have e1 : (2 * (169 / 2 : ℝ) * (12 / 5)) = 2028 / 5 := by norm_num
  have e2 : (2 * (12 / 5 : ℝ) * (169 / 2)) = 2028 / 5 := by norm_num
  rw [e1] at hA ⊢
  rw [e2] at hA
  set f0 : ℝ := 12 / 5 + Real.sin (2028 / 5) / (2 * (169 / 2)) with hf0def
  set L : ℝ := Real.log (Real.sqrt (9 / 16 + (169 / 2 : ℝ) ^ 2 / 4)) with hLdef
  set T : ℝ := 4 / 3 * Real.exp (-(3 * (12 / 5 : ℝ))) / (1 - Real.exp (-(4 * (12 / 5 : ℝ)))) with hTdef
  have hT : T ≤ 13 / 10000 := by
    rw [hTdef, div_le_iff₀ (by linarith)]
    nlinarith [hexp, hexp4, Real.exp_pos (-(3 * (12 / 5 : ℝ)))]
  have hTpos : 0 ≤ T := by rw [hTdef]; positivity
  have hA' : (Complex.digamma (3 / 4 : ℂ)).re * f0 + archEQ (3 / 4) (packet (12 / 5) (169 / 2))
      ≤ f0 * (L + 3 / (169 / 2)) + f0 * T + 1 / (2 * (169 / 2)) + (1 + Real.log (2028 / 5)) / (2 * (169 / 2)) := hA
  have hprod1 : f0 * (L + 3 / (169 / 2)) ≤ 2398058 / 10 ^ 6 * (37437620 / 10 ^ 7 + 3 / (169 / 2)) :=
    mul_le_mul hf0.2.le (by linarith [hL.2]) (by linarith [hL.1]) (by norm_num)
  have hprod2 : f0 * T ≤ 2398058 / 10 ^ 6 * (13 / 10000) :=
    mul_le_mul hf0.2.le hT hTpos (by norm_num)
  have hprod3 : (Real.log 5 - Real.log π) * f0 ≤ (16094380 / 10 ^ 7 - 11447296 / 10 ^ 7) * (2398058 / 10 ^ 6) :=
    mul_le_mul (by linarith [hlog5.2, hpi.1]) hf0.2.le (by linarith [hf0.1]) (by norm_num)
  have hexp' : ((Complex.digamma (3 / 4 : ℂ)).re + Real.log 5 - Real.log π) * f0
      = (Complex.digamma (3 / 4 : ℂ)).re * f0 + (Real.log 5 - Real.log π) * f0 := by ring
  rw [hexp']
  linarith [hS, hA', hprod1, hprod2, hprod3, h2aw.2]

/-- **The Davenport–Heilbronn function has a zero off the critical line** (kernel-checked). -/
theorem dh_offline_zero : ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 :=
  exists_offline_dh_of_neg_packet (by norm_num) (by norm_num) QDHu_packet_neg

end PsiOmega

#print axioms PsiOmega.floor_exp_twoA
#print axioms PsiOmega.QDHu_packet_neg
#print axioms PsiOmega.dh_offline_zero
