import Mathlib
import DHCertificate

/-! # The certificate's zero is off the cross (round 262)

Round 261's `dh_offline_zero` places a zero of `dh` in `0 < Re s`, `Re s ≠ ½`; `dh_ne_zero_of_two_lt`
(round 256) adds `Re s ≤ 2`. Here the same certificate `QDHu (packet 12/5 169/2) < 0` is read once more:
`ĝ(iy) = ∫ g(u) e^{−yu} du` is real for a real `g`, so a zero on the real axis contributes `2ĝ(3τ)² ≥ 0`
to the zero side exactly as a zero on the line does (`QDHu_packet_nonneg_of_line_or_real`). Hence the
witness is non-real (`dh_offline_nonreal_zero`), and by the zero symmetry `s ↦ 1 − s` of round 253 it may
be taken in `½ < Re s ≤ 2` (`dh_offline_zero_right`). Nothing here locates the zero. -/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-- `ĝ(iy)` is real: `∫ g(u) e^{-yu} du`. -/
theorem ghatC_I_mul_im (g : ℝ → ℝ) (a y : ℝ) : (ghatC g a (I * (y : ℂ))).im = 0 := by
  unfold ghatC
  have e : ∀ u : ℝ, ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * (I * (y : ℂ)) * u)
      = ((g u * Real.exp (-(y * u)) : ℝ) : ℂ) := by
    intro u
    have : Complex.I * (I * (y : ℂ)) * (u : ℂ) = ((-(y * u) : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [this, ← Complex.ofReal_exp]; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal]
  simp

/-- If every zero of `dh` with `Re s > 0` is on the line **or real**, the packet form is `≥ 0`. -/
theorem QDHu_packet_nonneg_of_line_or_real {a ω : ℝ} (ha : 0 < a) (hω : 0 < ω)
    (H : ∀ s : ℂ, dh s = 0 → 0 < s.re → s.re = 1 / 2 ∨ s.im = 0) : 0 ≤ QDHu (packet a ω) := by
  have h := (packet_QDHu_hasSum ha hω).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, ofReal_re] at h
  refine h.nonneg fun i => ?_
  have key : (tau3 i).im = 0 ∨ (tau3 i).re = 0 := by
    have hz := XiDH3_tau i
    have aux : ∀ τ : ℂ, XiDH3 τ = 0 → τ.im ≤ 0 → τ.im = 0 ∨ τ.re = 0 := by
      intro τ hτ hle
      obtain ⟨hd, h0⟩ := dh_zero_of_XiDH3 hτ hle
      rcases H _ hd h0 with h1 | h1
      · left
        have : (1 / 2 + I * (3 * τ)).re = 1 / 2 - 3 * τ.im := by simp; ring
        rw [this] at h1; linarith
      · right
        have : (1 / 2 + I * (3 * τ)).im = 3 * τ.re := by simp
        rw [this] at h1; linarith
    rcases le_or_gt (tau3 i).im 0 with hle | hgt
    · exact aux _ hz hle
    · have := aux (-(tau3 i)) (by rw [XiDH3_even]; exact hz) (by simp; linarith)
      simpa using this
  rcases key with hre | him
  · have e : (3 : ℂ) * tau3 i = ((3 * (tau3 i).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [hre])
    rw [e, hsq_ofReal (packet_probe ha hω.le) ha.le]
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by norm_num) (hsq_nonneg _)
  · have e : (3 : ℂ) * tau3 i = I * ((3 * (tau3 i).im : ℝ) : ℂ) :=
      Complex.ext (by simp [him]) (by simp)
    rw [e]
    have hw := ghatC_I_mul_im (packet a ω) a (3 * (tau3 i).im)
    set w := ghatC (packet a ω) a (I * ((3 * (tau3 i).im : ℝ) : ℂ))
    have : (2 * w ^ 2).re = 2 * w.re ^ 2 := by simp [sq, mul_re, hw]
    rw [this]; positivity

/-- **The certificate's zero is non-real.** -/
theorem dh_offline_nonreal_zero : ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 ∧ s.im ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have := QDHu_packet_nonneg_of_line_or_real (a := 12 / 5) (ω := 169 / 2) (by norm_num) (by norm_num)
    (fun s hs h0 => by
      by_cases h : s.re = 1 / 2
      · exact Or.inl h
      · exact Or.inr (hcon s hs h0 h))
  linarith [QDHu_packet_neg]

/-- **The free strengthening**: a non-real zero of `dh` with `½ < Re ρ ≤ 2`. -/
theorem dh_offline_zero_right : ∃ s : ℂ, dh s = 0 ∧ 1 / 2 < s.re ∧ s.re ≤ 2 ∧ s.im ≠ 0 := by
  obtain ⟨s, hs, h0, hne, him⟩ := dh_offline_nonreal_zero
  have h2 : s.re ≤ 2 := by
    by_contra h; push Not at h; exact dh_ne_zero_of_two_lt h hs
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨1 - s, (dh_zero_symm h0 (by linarith)).2 hs, ?_, ?_, ?_⟩
    · simp; linarith
    · simp; linarith
    · simpa using him
  · exact ⟨s, hs, hgt, h2, him⟩

end PsiOmega

#print axioms PsiOmega.dh_offline_nonreal_zero
#print axioms PsiOmega.dh_offline_zero_right
