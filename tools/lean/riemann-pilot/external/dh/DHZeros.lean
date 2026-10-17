import Mathlib
import DHHadamard

/-! # `L(½, χ₅) ≠ 0` and the zero side for `Ξ_{DH}` (round 255)

Round 254's Hadamard product for the Davenport–Heilbronn `Ξ` took the named input
`DHHalf : L(½, χ₅) ≠ 0`. It is discharged here without numerics, from round 254's integral
representation: `L(½, χ) = ½∫_1^∞ S(x)x^{−3/2}dx` (`LFunction_eq_IχC` at `s = ½`), and the summatory
function of `χ₅` has real part `0, 0, 1, 1, 1` by the residue of `⌊x⌋ + 1` mod 5
(`re_sum_range_cC_chi5`), so `Re S ≥ 0` everywhere and `Re S = 1` on `[1, 4)`, where
`∫_1^4 x^{−3/2}dx = 1`. Hence **`Re L(½, χ₅) ≥ ½`** (`re_LFunction_chi5_half_ge`), `L(½, χ₅) ≠ 0`
(`LFunction_chi5_half_ne_zero`), and the Hadamard product is unconditional (`hadamard_dh'`).

The zero side of Weil's explicit formula for `Ξ_{DH}` then follows as for `Ξ_χ` (round 225): off the
zeros, `Ξ_{DH}′(t)/Ξ_{DH}(t) = Σ_u 2t/(t² − u)` (`hasSum_logDeriv_XiDH`, `hasSum_logDeriv_dh`), and
`Σ |u|^{−7/8} < ∞` (`summable_XiDH_zeros_rpow`). What remains for the explicit formula is the prime
side, the Dirichlet series of `−dh′/dh`; see the README, round 255. (Rounds 256–257, `DHPrime.lean`
and `DHExplicit.lean`: done, for the scaled `Ξ₃(t) = Ξ_dh(3t)` with its own zero side
(`hasSum_logDeriv_XiDH3`, `summable_XiDH3_zeros_rpow`); this file's zero side has no downstream use.)
-/

open Real Complex DirichletCharacter Filter Topology MeasureTheory Set

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt

/-! ## `L(½, χ₅) ≠ 0` from the integral representation -/

theorem sum_range_cC_chi5_period : ∑ k ∈ Finset.range 5, cC chi5 k = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cC, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, chi5_apply_zero, chi5_apply_one, chi5_apply_two, chi5_apply_three,
    chi5_apply_four]
  ring

theorem cC_chi5_period (k : ℕ) : cC chi5 (k + 5) = cC chi5 k := by
  simp only [cC, Nat.cast_add]; rw [ZMod.natCast_self, add_zero]

theorem sum_range_cC_chi5 (m : ℕ) :
    ∑ k ∈ Finset.range m, cC chi5 k = ∑ k ∈ Finset.range (m % 5), cC chi5 k :=
  sum_range_modC _ cC_chi5_period sum_range_cC_chi5_period m

/-- **The partial sums of `χ₅` have real part `0, 0, 1, 1, 1`** by the residue of the length. -/
theorem re_sum_range_cC_chi5 (m : ℕ) :
    (∑ k ∈ Finset.range m, cC chi5 k).re =
      if m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 then 1 else 0 := by
  rw [sum_range_cC_chi5]
  have h5 : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize m % 5 = r at h5 ⊢
  interval_cases r <;> simp [Finset.sum_range_succ, cC]

theorem summC_chi5_eq (x : ℝ) : summC chi5 x = ∑ k ∈ Finset.range (⌊x⌋₊ + 1), cC chi5 k := by
  rw [summC, sum_Icc_eqC]; simp [cC]

theorem re_summC_chi5_nonneg (x : ℝ) : 0 ≤ (summC chi5 x).re := by
  rw [summC_chi5_eq, re_sum_range_cC_chi5]; split_ifs <;> norm_num

theorem re_summC_chi5_eq_one {x : ℝ} (h1 : 1 ≤ x) (h4 : x < 4) : (summC chi5 x).re = 1 := by
  rw [summC_chi5_eq, re_sum_range_cC_chi5]
  have hlo : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hhi : ⌊x⌋₊ < 4 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast h4)
  have h : (⌊x⌋₊ + 1) % 5 = 2 ∨ (⌊x⌋₊ + 1) % 5 = 3 ∨ (⌊x⌋₊ + 1) % 5 = 4 := by omega
  split_ifs
  rfl

theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `∫_1^4 x^{−3/2} dx = 1`. -/
theorem integral_rpow_one_four : ∫ x in (1 : ℝ)..4, x ^ (-(3 / 2 : ℝ)) = 1 := by
  rw [integral_rpow (Or.inr ⟨by norm_num, by rw [Set.uIcc_of_le (by norm_num)]; norm_num⟩)]
  have h4 : (4 : ℝ) ^ (-(3 / 2 : ℝ) + 1) = 1 / 2 := by
    rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow, sqrt_four]; norm_num
  rw [h4, Real.one_rpow]; norm_num

/-- **`Re L(½, χ₅) ≥ ½`**: `L(½, χ₅) = ½∫_1^∞ S(x)x^{−3/2}dx` with `Re S ≥ 0` everywhere and
`Re S = 1` on `[1, 4)`, where `∫_1^4 x^{−3/2}dx = 1`. -/
theorem re_LFunction_chi5_half_ge : 1 / 2 ≤ (LFunction chi5 (1 / 2)).re := by
  have hrep := LFunction_eq_IχC chi5_ne_one (s := 1 / 2) (by norm_num)
  rw [hrep]
  have e1 : ((1 / 2 : ℂ) * IχC chi5 (1 / 2)).re = 1 / 2 * (IχC chi5 (1 / 2)).re := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, re_ofReal_mul]
  rw [e1]
  suffices h : 1 ≤ (IχC chi5 (1 / 2)).re by linarith
  set F : ℝ → ℂ := fun x => summC chi5 x * (x : ℂ) ^ (-((1 / 2 : ℂ) + 1)) with hF
  have hexp : ∀ x : ℝ, 0 < x →
      (x : ℂ) ^ (-((1 / 2 : ℂ) + 1)) = ((x ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
    intro x hx
    rw [Complex.ofReal_cpow hx.le]; congr 1; push_cast; ring
  have hFre : ∀ x : ℝ, 0 < x → (F x).re = (summC chi5 x).re * x ^ (-(3 / 2 : ℝ)) := by
    intro x hx
    simp only [hF, hexp x hx]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hexp_re : (-((1 / 2 : ℂ) + 1)).re = -(3 / 2 : ℝ) := by simp; norm_num
  have hint : IntegrableOn F (Ioi 1) := by
    have hmaj : IntegrableOn (fun x : ℝ => (((5 : ℕ) : ℝ) + 1) * x ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · refine measurable_summC.aestronglyMeasurable.mul ?_
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const ?_
      intro x hx
      exact Or.inl (by simpa using lt_trans one_pos (show (1 : ℝ) < x from hx))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_)
      have hx0 : 0 < x := by linarith
      simp only [hF]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hexp_re]
      exact mul_le_mul_of_nonneg_right (norm_summC_le chi5_ne_one x) (by positivity)
  have hre : (IχC chi5 (1 / 2)).re = ∫ x in Ioi (1 : ℝ), (F x).re := by
    rw [IχC]; exact (integral_re hint).symm
  rw [hre]
  set g : ℝ → ℝ := fun x => x ^ (-(3 / 2 : ℝ)) with hg
  have hG : ∀ x ∈ Ioi (1 : ℝ), (Ico (1 : ℝ) 4).indicator g x ≤ (F x).re := by
    intro x hx
    have hx1 : 1 < x := hx
    rw [hFre x (by linarith)]
    by_cases h4 : x < 4
    · have hmem : x ∈ Ico (1 : ℝ) 4 := ⟨hx1.le, h4⟩
      simp only [indicator_of_mem hmem, re_summC_chi5_eq_one hx1.le h4, one_mul, hg, le_refl]
    · have hmem : x ∉ Ico (1 : ℝ) 4 := fun h => h4 h.2
      rw [indicator_of_notMem hmem]
      exact mul_nonneg (re_summC_chi5_nonneg x) (by positivity)
  have hint_re : IntegrableOn (fun x => (F x).re) (Ioi 1) := hint.re
  have hind : IntegrableOn ((Ico (1 : ℝ) 4).indicator g) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).indicator measurableSet_Ico
  have hmono := setIntegral_mono_on hind hint_re measurableSet_Ioi hG
  have hcalc : ∫ x in Ioi (1 : ℝ), (Ico (1 : ℝ) 4).indicator g x = 1 := by
    rw [integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
      show Ico (1 : ℝ) 4 ∩ Ioi 1 = Ioo 1 4 by
        ext x; simp only [mem_inter_iff, mem_Ico, mem_Ioi, mem_Ioo]
        exact ⟨fun ⟨⟨_, h4⟩, h1⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨⟨h1.le, h4⟩, h1⟩⟩,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
    exact integral_rpow_one_four
  linarith

/-- **`L(½, χ₅) ≠ 0`**, so round 254's named input `DHHalf` holds. -/
theorem LFunction_chi5_half_ne_zero : LFunction chi5 (1 / 2) ≠ 0 := fun h => by
  have := re_LFunction_chi5_half_ge; rw [h, zero_re] at this; linarith

theorem dhHalf : DHHalf := LFunction_chi5_half_ne_zero

/-- **The Hadamard product of the Davenport–Heilbronn `Ξ`, unconditional.** -/
theorem hadamard_dh' : HadamardW (XiDH chi5) (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) :=
  hadamard_dh dhHalf

theorem XiDH_chi5_zero_ne' : XiDH chi5 0 ≠ 0 := XiDH_chi5_zero_ne dhHalf

/-! ## The zero side: the logarithmic derivative of the Hadamard product -/

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem ZeroIdxDH_ne_zero (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    (hhalf : LFunction χ (1 / 2) ≠ 0) (i : ZeroIdx (sqF (XiDH χ))) : i.1 ≠ 0 := by
  intro h
  have hz : sqF (XiDH χ) i.1 = 0 := (ordN_ne_zero_iff (sqF_differentiable (differentiable_XiDH χ hχ1)
    (XiDH_even χ hχ1 hprim)) (by rw [sqF_zero]; exact XiDH_zero_ne hχ1 hprim h1 hhalf) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))
  rw [h, sqF_zero] at hz
  exact XiDH_zero_ne hχ1 hprim h1 hhalf hz

/-- **The logarithmic derivative of Hadamard's product**: off the zeros,
`Ξ_{DH}′(t)/Ξ_{DH}(t) = Σ_u 2t/(t² − u)`. -/
theorem hasSum_logDeriv_XiDH (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    (hhalf : LFunction χ (1 / 2) ≠ 0) {t : ℂ} (ht : XiDH χ t ≠ 0) :
    HasSum (fun i : ZeroIdx (sqF (XiDH χ)) => 2 * t / (t ^ 2 - i.1)) (logDeriv (XiDH χ) t) :=
  hasSum_logDeriv_of_hadamardW (hadamard_XiDH hχ1 hprim h1 hhalf)
    (XiDH_zero_ne hχ1 hprim h1 hhalf) (ZeroIdxDH_ne_zero hχ1 hprim h1 hhalf) ht

/-- **The zero side for the Davenport–Heilbronn `Ξ`**, unconditional. -/
theorem hasSum_logDeriv_dh {t : ℂ} (ht : XiDH chi5 t ≠ 0) :
    HasSum (fun i : ZeroIdx (sqF (XiDH chi5)) => 2 * t / (t ^ 2 - i.1)) (logDeriv (XiDH chi5) t) :=
  hasSum_logDeriv_XiDH chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero dhHalf ht

/-- `Σ_i |u_i|^{−7/8} < ∞` over the zeros of `Ξ_{DH}(√w)`. -/
theorem summable_XiDH_zeros_rpow (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    (hhalf : LFunction χ (1 / 2) ≠ 0) :
    Summable (fun i : ZeroIdx (sqF (XiDH χ)) => (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹) := by
  have hF := sqF_differentiable (differentiable_XiDH χ hχ1) (XiDH_even χ hχ1 hprim)
  have hF0 : sqF (XiDH χ) 0 ≠ 0 := by rw [sqF_zero]; exact XiDH_zero_ne hχ1 hprim h1 hhalf
  have hgF : ∀ w, ‖sqF (XiDH χ) w‖ ≤ KDH χ * Real.exp (36 * ‖w‖ ^ (3 / 4 : ℝ)) := by
    intro w
    refine (norm_XiDH_le hχ1 hprim _).trans ?_
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
  show _ = ∑ _b : Fin (ordN (sqF (XiDH χ)) u), (‖u‖ ^ (7 / 8 : ℝ))⁻¹
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]

theorem summable_dh_zeros_rpow :
    Summable (fun i : ZeroIdx (sqF (XiDH chi5)) => (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹) :=
  summable_XiDH_zeros_rpow chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero dhHalf

end PsiOmega

#print axioms PsiOmega.re_sum_range_cC_chi5
#print axioms PsiOmega.integral_rpow_one_four
#print axioms PsiOmega.re_LFunction_chi5_half_ge
#print axioms PsiOmega.LFunction_chi5_half_ne_zero
#print axioms PsiOmega.hadamard_dh'
#print axioms PsiOmega.XiDH_chi5_zero_ne'
#print axioms PsiOmega.ZeroIdxDH_ne_zero
#print axioms PsiOmega.hasSum_logDeriv_XiDH
#print axioms PsiOmega.hasSum_logDeriv_dh
#print axioms PsiOmega.summable_XiDH_zeros_rpow
#print axioms PsiOmega.summable_dh_zeros_rpow
