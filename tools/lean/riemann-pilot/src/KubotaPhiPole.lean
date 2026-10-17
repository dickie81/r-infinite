import KubotaPhi

/-! # The pole of the scattering coefficient at `s = 4/3` (round 417)

S5f-9b of round 360's plan, its last part. Round 416's closed form `phiC` of round 389's `φ` continues to
`Re s > 1` with one pole there, at `s = 4/3`, whose residue is `π/(6√3)·L(1, χ₋₃)/(ζ(2)L(2, χ₋₃))`, which
is not `0`.

* **The continuation** (**`differentiableAt_phiC`**, with `nine_sqrt_ne_zero`): `phiC` is complex-differentiable
  at every `s` with `Re s > 1` and `s ≠ 4/3` (Mathlib's `differentiableAt_riemannZeta` and
  `DirichletCharacter.differentiable_LFunction`, with round 416's `phiC_den_ne_zero`).
* **The pole** (`phiG`, a definition; **`tendsto_phiC_residue`**, with `mul_phiC_eq`, `continuousAt_phiG` and
  `tendsto_mul_riemannZeta`): `(s − 4/3)·phiC(s) = phiG(s)·(s − 4/3)ζ(3s − 3)`, with `phiG` continuous at
  `4/3`, and `(s − 4/3)ζ(3s − 3) → 1/3` (Mathlib's `riemannZeta_residue_one`).
* **The residue** (**`phiRes_eq`** and **`phiRes_ne_zero`**): `phiG(4/3)/3 = π/(6√3)·L(1, χ₋₃)/(ζ(2)L(2, χ₋₃))`,
  which is not `0` (Mathlib's `DirichletCharacter.LFunction_apply_one_ne_zero`, with round 416's
  `zetaK_ne_zero`).
-/

open NumberField Filter Topology DirichletCharacter

noncomputable section

namespace Eis

/-- The factor of `(s − 4/3)·φ(s)` that is continuous at `4/3`. -/
def phiG (s : ℂ) : ℂ :=
  Real.pi / (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (s - 1)) * (2 * 3 ^ (3 - 3 * s)) *
    LFunction PsiOmega.chi3 (3 * s - 3) *
      ((1 - 3 ^ (2 - 3 * s)) * (riemannZeta (3 * s - 2) * LFunction PsiOmega.chi3 (3 * s - 2)))⁻¹

theorem mul_phiC_eq (s : ℂ) :
    (s - 4 / 3) * phiC s = phiG s * ((s - 4 / 3) * riemannZeta (3 * s - 3)) := by
  unfold phiC phiG; ring

theorem nine_sqrt_ne_zero : (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ)) ≠ 0 := by
  have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
  exact_mod_cast this.ne'

/-- **`φ` continues**: `phiC` is complex-differentiable at every `s` with `Re s > 1` and `s ≠ 4/3`. -/
theorem differentiableAt_phiC {s : ℂ} (hs : 1 < s.re) (h43 : s ≠ 4 / 3) :
    DifferentiableAt ℂ phiC s := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hw3 : 3 * s - 3 ≠ 1 := fun h => h43 (by linear_combination h / 3)
  have hw2 : 3 * s - 2 ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hL : Differentiable ℂ (LFunction PsiOmega.chi3) := differentiable_LFunction PsiOmega.chi3_ne_one
  have hlin : ∀ a b : ℂ, Differentiable ℂ fun s : ℂ => a * s - b := fun a b =>
    (differentiable_id.const_mul a).sub_const b
  have hA : DifferentiableAt ℂ (fun s : ℂ => Real.pi / (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (s - 1))) s :=
    (differentiableAt_const _).div ((differentiableAt_id.sub_const 1).const_mul _)
      (mul_ne_zero nine_sqrt_ne_zero hs1)
  have hB : DifferentiableAt ℂ (fun s : ℂ => 2 * (3 : ℂ) ^ (3 - 3 * s)) s :=
    (((differentiableAt_id.const_mul 3).const_sub 3).const_cpow (Or.inl (by norm_num))).const_mul 2
  have hZ : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (3 * s - 3) * LFunction PsiOmega.chi3 (3 * s - 3)) s :=
    ((differentiableAt_riemannZeta hw3).comp s ((hlin 3 3).differentiableAt)).mul
      ((hL _).comp s ((hlin 3 3).differentiableAt))
  have hD : DifferentiableAt ℂ (fun s : ℂ => (1 - (3 : ℂ) ^ (2 - 3 * s)) *
      (riemannZeta (3 * s - 2) * LFunction PsiOmega.chi3 (3 * s - 2))) s :=
    ((((differentiableAt_id.const_mul 3).const_sub 2).const_cpow (Or.inl (by norm_num))).const_sub 1).mul
      (((differentiableAt_riemannZeta hw2).comp s ((hlin 3 2).differentiableAt)).mul
        ((hL _).comp s ((hlin 3 2).differentiableAt)))
  exact hA.mul ((hB.mul hZ).div hD (phiC_den_ne_zero hs.le))

theorem continuousAt_phiG : ContinuousAt phiG (4 / 3) := by
  have h43 : (4 / 3 : ℂ) - 1 ≠ 0 := by norm_num
  have hw2 : 3 * (4 / 3 : ℂ) - 2 ≠ 1 := by norm_num
  have hL : Continuous (LFunction PsiOmega.chi3) := (differentiable_LFunction PsiOmega.chi3_ne_one).continuous
  have hlin : ∀ a b : ℂ, Continuous fun s : ℂ => a * s - b := fun a b =>
    (continuous_const.mul continuous_id).sub continuous_const
  have hden := phiC_den_ne_zero (s := 4 / 3) (by norm_num)
  unfold phiG
  refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_) ?_
  · exact continuousAt_const.div (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
      (mul_ne_zero nine_sqrt_ne_zero h43)
  · exact continuousAt_const.mul
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).const_cpow (Or.inl (by norm_num)))
  · exact (hL.comp (hlin 3 3)).continuousAt
  · refine ContinuousAt.inv₀ ?_ hden
    exact (continuousAt_const.sub
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).const_cpow (Or.inl (by norm_num)))).mul
      (((differentiableAt_riemannZeta hw2).continuousAt.comp (f := fun s : ℂ => 3 * s - 2)
        (hlin 3 2).continuousAt).mul (hL.comp (hlin 3 2)).continuousAt)

theorem tendsto_mul_riemannZeta :
    Tendsto (fun s : ℂ => (s - 4 / 3) * riemannZeta (3 * s - 3)) (𝓝[≠] (4 / 3)) (𝓝 (1 / 3)) := by
  have hw : Tendsto (fun s : ℂ => 3 * s - 3) (𝓝[≠] (4 / 3)) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
    swap
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      exact hs (by linear_combination h / 3)
    have hc : Continuous fun s : ℂ => 3 * s - 3 := (continuous_const.mul continuous_id).sub continuous_const
    have := hc.tendsto (4 / 3)
    rw [show 3 * (4 / 3 : ℂ) - 3 = 1 by norm_num] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (riemannZeta_residue_one.comp hw).const_mul (1 / 3 : ℂ)
  rw [mul_one] at h
  refine h.congr fun s => ?_
  simp only [Function.comp]
  ring

/-- **The pole of `φ` at `4/3`**: `(s − 4/3)·φ(s) → phiG(4/3)/3` as `s → 4/3`. -/
theorem tendsto_phiC_residue :
    Tendsto (fun s : ℂ => (s - 4 / 3) * phiC s) (𝓝[≠] (4 / 3)) (𝓝 (phiG (4 / 3) / 3)) := by
  have h := (continuousAt_phiG.tendsto.mono_left nhdsWithin_le_nhds).mul tendsto_mul_riemannZeta
  rw [show phiG (4 / 3) * (1 / 3) = phiG (4 / 3) / 3 by ring] at h
  exact h.congr fun s => (mul_phiC_eq s).symm

/-- **The residue in closed form**: `phiG(4/3)/3 = π/(6√3)·L(1, χ₋₃)/(ζ(2)L(2, χ₋₃))`. -/
theorem phiRes_eq : phiG (4 / 3) / 3 = Real.pi / (6 * Real.sqrt 3) * LFunction PsiOmega.chi3 1 /
    (riemannZeta 2 * LFunction PsiOmega.chi3 2) := by
  have e1 : (3 : ℂ) - 3 * (4 / 3) = -1 := by norm_num
  have e2 : (2 : ℂ) - 3 * (4 / 3) = -2 := by norm_num
  have e3 : 3 * (4 / 3 : ℂ) - 3 = 1 := by norm_num
  have e4 : 3 * (4 / 3 : ℂ) - 2 = 2 := by norm_num
  have c1 : (3 : ℂ) ^ (-1 : ℂ) = 1 / 3 := by rw [Complex.cpow_neg_one]; ring
  have c2 : (3 : ℂ) ^ (-2 : ℂ) = 1 / 9 := by
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; norm_num
  have hz : riemannZeta 2 * LFunction PsiOmega.chi3 2 ≠ 0 := zetaK_ne_zero (by norm_num)
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 3 := by positivity
    exact_mod_cast this.ne'
  unfold phiG
  rw [e1, e2, e3, e4, c1, c2]
  push_cast
  field_simp
  ring

/-- **The residue is not `0`**. -/
theorem phiRes_ne_zero : phiG (4 / 3) / 3 ≠ 0 := by
  rw [phiRes_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 3 := by positivity
    exact_mod_cast this.ne'
  have hL1 := LFunction_apply_one_ne_zero PsiOmega.chi3_ne_one
  have hz : riemannZeta 2 * LFunction PsiOmega.chi3 2 ≠ 0 := zetaK_ne_zero (by norm_num)
  exact div_ne_zero (mul_ne_zero (div_ne_zero hpi (mul_ne_zero (by norm_num) hs3)) hL1) hz

end Eis

end

#print axioms Eis.mul_phiC_eq
#print axioms Eis.nine_sqrt_ne_zero
#print axioms Eis.differentiableAt_phiC
#print axioms Eis.continuousAt_phiG
#print axioms Eis.tendsto_mul_riemannZeta
#print axioms Eis.tendsto_phiC_residue
#print axioms Eis.phiRes_eq
#print axioms Eis.phiRes_ne_zero
