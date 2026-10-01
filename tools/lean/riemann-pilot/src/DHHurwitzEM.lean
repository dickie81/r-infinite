import DHPrime
import HurwitzEM

/-!
# The Euler–Maclaurin approximant of the Davenport–Heilbronn function `dh`

`dh s = 5^{-s} Σ_{j=1}^{4} a(j) ζ(s, j/5)` (`dh_eq_hurwitz`, every `s`), with `a = aDH chi5`
the pilot's Dirichlet coefficients, and hence, by `HurwitzEM`, an explicit approximant with an
explicit error on `Re s > 0`, `s ≠ 1` (`norm_dh_sub_EM_le`), uniform on boxes
(`norm_dh_sub_EM_le_box`).
-/

open Complex HurwitzZeta
open scoped Nat

noncomputable section

namespace PsiOmega

theorem toAddCircle_zmod5 (j : ℕ) :
    ZMod.toAddCircle ((j : ℕ) : ZMod 5) = (((j : ℝ) / 5 : ℝ) : UnitAddCircle) := by
  simpa using ZMod.toAddCircle_natCast (N := 5) j

/-- **The bridge**: `dh s = 5^{-s} Σ_{j=1}^{4} a(j) ζ(s, j/5)`, for every `s`. -/
theorem dh_eq_hurwitz (s : ℂ) :
    dh s = (5 : ℂ) ^ (-s) *
      (aDH chi5 1 * hurwitzZeta (((1 : ℕ) : ℝ) / 5 : ℝ) s +
        aDH chi5 2 * hurwitzZeta (((2 : ℕ) : ℝ) / 5 : ℝ) s +
        aDH chi5 3 * hurwitzZeta (((3 : ℕ) : ℝ) / 5 : ℝ) s +
        aDH chi5 4 * hurwitzZeta (((4 : ℕ) : ℝ) / 5 : ℝ) s) := by
  unfold dh dhL
  simp only [DirichletCharacter.LFunction, ZMod.LFunction]
  rw [zmod5_univ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : (1 : ZMod 5) = ((1 : ℕ) : ZMod 5) := by decide
  have e2 : (2 : ZMod 5) = ((2 : ℕ) : ZMod 5) := by decide
  have e3 : (3 : ZMod 5) = ((3 : ℕ) : ZMod 5) := by decide
  have e4 : (4 : ZMod 5) = ((4 : ℕ) : ZMod 5) := by decide
  rw [e1, e2, e3, e4, toAddCircle_zmod5 1, toAddCircle_zmod5 2, toAddCircle_zmod5 3,
    toAddCircle_zmod5 4]
  have z1 : chi5 (0 : ZMod 5) = 0 := chi5_apply_zero
  have z2 : chi5⁻¹ (0 : ZMod 5) = 0 := by rw [chi5_inv_apply, chi5_apply_zero, map_zero]
  simp only [aDH, Nat.cast_ofNat, Nat.cast_one]
  rw [z1, z2]
  ring

/-- `‖5^{-s}‖ = 5^{-Re s}`. -/
theorem norm_five_cpow (s : ℂ) : ‖(5 : ℂ) ^ (-s)‖ = (5 : ℝ) ^ (-s.re) := by
  have := norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 5) (-s)
  simpa using this

/-- The Euler–Maclaurin approximant of `dh`:
`5^{-s} Σ_{j=1}^{4} a(j) · EM_{M,K}(j/5, s)`. -/
def dhEM (M K : ℕ) (s : ℂ) : ℂ :=
  (5 : ℂ) ^ (-s) *
    (aDH chi5 1 * HurwitzEM.EMmain (((1 : ℕ) : ℝ) / 5) M K s +
      aDH chi5 2 * HurwitzEM.EMmain (((2 : ℕ) : ℝ) / 5) M K s +
      aDH chi5 3 * HurwitzEM.EMmain (((3 : ℕ) : ℝ) / 5) M K s +
      aDH chi5 4 * HurwitzEM.EMmain (((4 : ℕ) : ℝ) / 5) M K s)

theorem mem_Ioc_j5 {j : ℕ} (h1 : 1 ≤ j) (h4 : j ≤ 4) : ((j : ℝ) / 5) ∈ Set.Ioc (0 : ℝ) 1 := by
  have : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have : (j : ℝ) ≤ 4 := by exact_mod_cast h4
  constructor
  · positivity
  · rw [div_le_one (by norm_num)]; linarith

/-- The four-term combination behind both bounds. -/
theorem norm_dh_sub_dhEM_le_aux {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    ‖dh s - dhEM M K s‖ ≤ (5 : ℝ) ^ (-s.re) *
      (‖aDH chi5 1‖ * ‖HurwitzEM.EMrem (((1 : ℕ) : ℝ) / 5) M K s‖ +
        ‖aDH chi5 2‖ * ‖HurwitzEM.EMrem (((2 : ℕ) : ℝ) / 5) M K s‖ +
        ‖aDH chi5 3‖ * ‖HurwitzEM.EMrem (((3 : ℕ) : ℝ) / 5) M K s‖ +
        ‖aDH chi5 4‖ * ‖HurwitzEM.EMrem (((4 : ℕ) : ℝ) / 5) M K s‖) := by
  rw [dh_eq_hurwitz, dhEM,
    HurwitzEM.hurwitzZeta_eq_EM (mem_Ioc_j5 (j := 1) le_rfl (by norm_num)) hM hK hs hs1,
    HurwitzEM.hurwitzZeta_eq_EM (mem_Ioc_j5 (j := 2) (by norm_num) (by norm_num)) hM hK hs hs1,
    HurwitzEM.hurwitzZeta_eq_EM (mem_Ioc_j5 (j := 3) (by norm_num) (by norm_num)) hM hK hs hs1,
    HurwitzEM.hurwitzZeta_eq_EM (mem_Ioc_j5 (j := 4) (by norm_num) le_rfl) hM hK hs hs1]
  set R1 := HurwitzEM.EMrem (((1 : ℕ) : ℝ) / 5) M K s
  set R2 := HurwitzEM.EMrem (((2 : ℕ) : ℝ) / 5) M K s
  set R3 := HurwitzEM.EMrem (((3 : ℕ) : ℝ) / 5) M K s
  set R4 := HurwitzEM.EMrem (((4 : ℕ) : ℝ) / 5) M K s
  have e : (5 : ℂ) ^ (-s) *
      (aDH chi5 1 * (HurwitzEM.EMmain (((1 : ℕ) : ℝ) / 5) M K s - R1) +
        aDH chi5 2 * (HurwitzEM.EMmain (((2 : ℕ) : ℝ) / 5) M K s - R2) +
        aDH chi5 3 * (HurwitzEM.EMmain (((3 : ℕ) : ℝ) / 5) M K s - R3) +
        aDH chi5 4 * (HurwitzEM.EMmain (((4 : ℕ) : ℝ) / 5) M K s - R4)) -
      (5 : ℂ) ^ (-s) *
      (aDH chi5 1 * HurwitzEM.EMmain (((1 : ℕ) : ℝ) / 5) M K s +
        aDH chi5 2 * HurwitzEM.EMmain (((2 : ℕ) : ℝ) / 5) M K s +
        aDH chi5 3 * HurwitzEM.EMmain (((3 : ℕ) : ℝ) / 5) M K s +
        aDH chi5 4 * HurwitzEM.EMmain (((4 : ℕ) : ℝ) / 5) M K s) =
      -((5 : ℂ) ^ (-s) * (aDH chi5 1 * R1 + aDH chi5 2 * R2 + aDH chi5 3 * R3 + aDH chi5 4 * R4)) := by
    ring
  rw [e, norm_neg, norm_mul, norm_five_cpow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_mul]

/-- **The Euler–Maclaurin bound for `dh`** on `Re s > 0`, `s ≠ 1`:
`‖dh s − dhEM M K s‖ ≤ 5^{-Re s} Σ_{j=1}^{4} ‖a(j)‖ · C_K ‖(s)_{2K}‖ (M + j/5)^{1−Re s−2K}/(Re s+2K−1)`. -/
theorem norm_dh_sub_EM_le {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) :
    ‖dh s - dhEM M K s‖ ≤ (5 : ℝ) ^ (-s.re) *
      (‖aDH chi5 1‖ * (HurwitzEM.CB K * ‖HurwitzEM.poch s (2 * K)‖ *
          ((M + ((1 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1))) +
        ‖aDH chi5 2‖ * (HurwitzEM.CB K * ‖HurwitzEM.poch s (2 * K)‖ *
          ((M + ((2 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1))) +
        ‖aDH chi5 3‖ * (HurwitzEM.CB K * ‖HurwitzEM.poch s (2 * K)‖ *
          ((M + ((3 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1))) +
        ‖aDH chi5 4‖ * (HurwitzEM.CB K * ‖HurwitzEM.poch s (2 * K)‖ *
          ((M + ((4 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1)))) := by
  refine (norm_dh_sub_dhEM_le_aux hM hK hs hs1).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hx : ∀ j : ℕ, 1 ≤ j → (0 : ℝ) < (j : ℝ) / 5 := fun j hj => by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    positivity
  gcongr
  · exact HurwitzEM.norm_EMrem_le (hx 1 le_rfl) hM hK hs
  · exact HurwitzEM.norm_EMrem_le (hx 2 (by norm_num)) hM hK hs
  · exact HurwitzEM.norm_EMrem_le (hx 3 (by norm_num)) hM hK hs
  · exact HurwitzEM.norm_EMrem_le (hx 4 (by norm_num)) hM hK hs

/-- **Box version**, for the minimum-modulus certificate: on `σ₀ ≤ Re s ≤ σ₁`, `|Im s| ≤ τ`,
`s ≠ 1`, `σ₀ > 0`, with `Π_{i<2K} ((σ₁+i)² + τ²) ≤ B²`,
`‖dh s − dhEM M K s‖ ≤ 5^{-σ₀} Σ_{j=1}^{4} ‖a(j)‖ · (π²/3)/(2π)^{2K} · B · (M + j/5)^{1−σ₀−2K}/(σ₀+2K−1)`. -/
theorem norm_dh_sub_EM_le_box {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K)
    {σ₀ σ₁ τ B : ℝ} (hσ₀ : 0 < σ₀) (hB : 0 ≤ B)
    (hPB : ∏ i ∈ Finset.range (2 * K), ((σ₁ + i) ^ 2 + τ ^ 2) ≤ B ^ 2)
    {s : ℂ} (hs0 : σ₀ ≤ s.re) (hs1 : s.re ≤ σ₁) (hsT : |s.im| ≤ τ) (hs : s ≠ 1) :
    ‖dh s - dhEM M K s‖ ≤ (5 : ℝ) ^ (-σ₀) *
      (‖aDH chi5 1‖ * ((Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) * B *
          ((M + ((1 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - σ₀ - 2 * K) / (σ₀ + 2 * K - 1))) +
        ‖aDH chi5 2‖ * ((Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) * B *
          ((M + ((2 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - σ₀ - 2 * K) / (σ₀ + 2 * K - 1))) +
        ‖aDH chi5 3‖ * ((Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) * B *
          ((M + ((3 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - σ₀ - 2 * K) / (σ₀ + 2 * K - 1))) +
        ‖aDH chi5 4‖ * ((Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) * B *
          ((M + ((4 : ℕ) : ℝ) / 5 : ℝ) ^ (1 - σ₀ - 2 * K) / (σ₀ + 2 * K - 1)))) := by
  have hsre : 0 < s.re := by linarith
  refine (norm_dh_sub_dhEM_le_aux hM hK hsre hs).trans ?_
  have h5 : (5 : ℝ) ^ (-s.re) ≤ (5 : ℝ) ^ (-σ₀) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hx : ∀ j : ℕ, 1 ≤ j → (0 : ℝ) < (j : ℝ) / 5 := fun j hj => by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    positivity
  apply mul_le_mul h5 _ (by positivity) (by positivity)
  gcongr
  · exact HurwitzEM.norm_EMrem_le_box (hx 1 le_rfl) hM hK hσ₀ hB hPB hs0 hs1 hsT
  · exact HurwitzEM.norm_EMrem_le_box (hx 2 (by norm_num)) hM hK hσ₀ hB hPB hs0 hs1 hsT
  · exact HurwitzEM.norm_EMrem_le_box (hx 3 (by norm_num)) hM hK hσ₀ hB hPB hs0 hs1 hsT
  · exact HurwitzEM.norm_EMrem_le_box (hx 4 (by norm_num)) hM hK hσ₀ hB hPB hs0 hs1 hsT

end PsiOmega

#print axioms PsiOmega.dh_eq_hurwitz
#print axioms PsiOmega.norm_dh_sub_EM_le
#print axioms PsiOmega.norm_dh_sub_EM_le_box
