import DetectEM
import Zeta23.MV.Final
import AngularFamily

/-! # The pnt layer and zeta23's mean-value module co-import (round 248)

`DetectEM` and `Zeta23.MV.Final` load together (the clash is only with the vendored `FromPNTPlus` copies that `SlogZeta` uses), so `mv_hilbert` can reach the density theorem; `large_values_amgm`; the parametric `DetectHypP`; Mathlib's `dedekindZeta` of `ℚ(i)` is `ζ·L(χ₋₄)` given `GaussIdealCount`.
-/

open Real Complex MeasureTheory Set Finset

noncomputable section

namespace CoImportMV

/-! ## (1) co-import -/

example : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C := Zeta23.MV.mv_hilbert
example {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) : ShortWeil.DensityXi (4 * (1 + δ)) 11 :=
  DetectEM.density_unconditional hδ0 hδ1

/-! ## (2) Gallagher with a weighted AM–GM -/

open DirMean in
theorem large_values_amgm {P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P))
    (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) (R : Finset ℝ)
    (hsep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 1 ≤ |x - y|)
    (hR : ∀ x ∈ R, a + 1 / 2 ≤ x ∧ x ≤ b - 1 / 2) :
    ∑ x ∈ R, ‖dp S c x‖ ^ 2
      ≤ (b - a + 8 * P * (1 + Real.log P)) * (1 + 2 * Real.log (2 * P)) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  set c' : ℕ → ℂ := fun j => c j * (-(I * (Real.log j : ℂ))) with hc'
  have hG := gallagher (fun t => hasDerivAt_dp S c t) (continuous_dp S c') R hsep hR hab
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  set μ := Real.log (2 * P) with hμ
  have hμ0 : 0 < μ := Real.log_pos (by linarith)
  have hμi : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ0.ne'
  have i1 : IntervalIntegrable (fun t => ‖dp S c t‖ ^ 2 + 2 * ‖dp S c t‖ * ‖dp S c' t‖) volume a b :=
    ((continuous_dp S c).norm.pow 2 |>.add
      ((continuous_const.mul (continuous_dp S c).norm).mul (continuous_dp S c').norm)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => (1 + μ) * ‖dp S c t‖ ^ 2) volume a b :=
    (continuous_const.mul ((continuous_dp S c).norm.pow 2)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => μ⁻¹ * ‖dp S c' t‖ ^ 2) volume a b :=
    (continuous_const.mul ((continuous_dp S c').norm.pow 2)).intervalIntegrable _ _
  have hpt : ∀ x y : ℝ, 2 * x * y ≤ μ * x ^ 2 + μ⁻¹ * y ^ 2 := by
    intro x y
    have e : (μ * x - y) ^ 2 * μ⁻¹ = μ * x ^ 2 - 2 * x * y + μ⁻¹ * y ^ 2 := by
      have : (μ * x - y) ^ 2 * μ⁻¹
          = (μ * μ⁻¹) * (μ * x ^ 2) - 2 * (μ * μ⁻¹) * x * y + μ⁻¹ * y ^ 2 := by ring
      rw [this, hμi]; ring
    have h0 : 0 ≤ (μ * x - y) ^ 2 * μ⁻¹ := mul_nonneg (sq_nonneg _) (inv_nonneg.2 hμ0.le)
    linarith
  have hle : ∫ t in a..b, (‖dp S c t‖ ^ 2 + 2 * ‖dp S c t‖ * ‖dp S c' t‖)
      ≤ (1 + μ) * (∫ t in a..b, ‖dp S c t‖ ^ 2) + μ⁻¹ * ∫ t in a..b, ‖dp S c' t‖ ^ 2 := by
    have := intervalIntegral.integral_mono_on hab i1 (i2.add i3)
      fun t _ => by have := hpt ‖dp S c t‖ ‖dp S c' t‖; nlinarith
    rwa [intervalIntegral.integral_add i2 i3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at this
  have hm := mean_value hP hS c hab
  have hm' := mean_value hP hS c' hab
  set L := b - a + 8 * P * (1 + Real.log P) with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    rw [hL]; nlinarith [sub_nonneg.2 hab]
  have hc'le : ∑ j ∈ S, ‖c' j‖ ^ 2 ≤ μ ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 (hS hj)
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hlj : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
    have hlj2 : Real.log j ≤ μ :=
      Real.log_le_log hj0 (by exact_mod_cast hj2)
    simp only [hc', norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlj, mul_pow]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlj hlj2 2) (by positivity)
  have hS0 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hμinv : 0 ≤ μ⁻¹ := inv_nonneg.2 hμ0.le
  calc ∑ x ∈ R, ‖dp S c x‖ ^ 2
      ≤ (1 + μ) * (∫ t in a..b, ‖dp S c t‖ ^ 2) + μ⁻¹ * ∫ t in a..b, ‖dp S c' t‖ ^ 2 := hG.trans hle
    _ ≤ (1 + μ) * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + μ⁻¹ * (L * ∑ j ∈ S, ‖c' j‖ ^ 2) := by
        gcongr
    _ ≤ (1 + μ) * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + μ⁻¹ * (L * (μ ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2)) := by
        gcongr
    _ = L * (1 + 2 * μ) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
        have : μ⁻¹ * (L * (μ ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2))
            = (μ * μ⁻¹) * (L * μ * ∑ j ∈ S, ‖c j‖ ^ 2) := by ring
        rw [this, hμi]; ring

/-! ## (3) missing Props, typechecked -/

/-- van der Corput's second-derivative test for `Σ n^{−it}` on a dyadic block below `|t|`:
the exponent pair `(1/2, 1/2)`. Not proved in any layer. -/
def VdC2Bound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (M N : ℕ), 1 ≤ M → M ≤ N → N ≤ 2 * M → (M : ℝ) ≤ |t| →
    ‖∑ n ∈ Finset.Ioc M N, (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ≤ C * Real.sqrt |t|

/-- The ideal count of `ℚ(i)` (as `CyclotomicField 4 ℚ`) is the pilot's radial coefficient `r₂(n)/4`. -/
def GaussIdealCount : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    (((Nat.card {I : Ideal (NumberField.RingOfIntegers (CyclotomicField 4 ℚ)) //
        Ideal.absNorm I = n} : ℕ) : ℂ) = AngularFamily.angularCoeff 0 n)

/-- The join it gives: Mathlib's Dedekind zeta of `ℚ(i)` is the pilot's radial member. -/
theorem dedekindZeta_eq_angularL (h : GaussIdealCount) {s : ℂ} (_hs : 1 < s.re) :
    NumberField.dedekindZeta (CyclotomicField 4 ℚ) s = AngularFamily.angularL 0 s := by
  unfold NumberField.dedekindZeta AngularFamily.angularL
  exact LSeries_congr (fun {n} hn => h n hn) s

theorem dedekindZeta_eq_zeta_mul_L (h : GaussIdealCount) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (CyclotomicField 4 ℚ) s
      = riemannZeta s * DirichletCharacter.LFunction AngularFamily.χ4C s := by
  rw [dedekindZeta_eq_angularL h hs, AngularFamily.member_zero_eq hs]; rfl

open Pilot1ca Pilot1bt in
/-- Detection with the exponents of `X` and `N` as functions of `σ`. -/
def DetectHypP (x ν : ℝ → ℝ) : Prop :=
  ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ σ U : ℝ, 3 / 4 ≤ σ → σ ≤ 1 → U₀ ≤ U →
    ∀ i : ZeroIdx (sqF Xi), U ≤ |(tau i).re| → |(tau i).re| ≤ 2 * U → σ ≤ ShortWeil.βs i →
      1 / 2 ≤ ‖ShortWeil.DPval ⌊U ^ x σ⌋₊ ⌊U ^ ν σ⌋₊ (ShortWeil.βs i) (ShortWeil.γs i)‖

theorem detectHypP_of {δ : ℝ} (h : ShortWeil.DetectHyp δ) :
    DetectHypP (fun σ => 2 * σ - 1) (fun σ => 3 - 2 * σ + 2 * δ) := by
  exact h

end CoImportMV

#print axioms CoImportMV.large_values_amgm
#print axioms CoImportMV.dedekindZeta_eq_angularL
#print axioms CoImportMV.dedekindZeta_eq_zeta_mul_L
#print axioms CoImportMV.detectHypP_of
