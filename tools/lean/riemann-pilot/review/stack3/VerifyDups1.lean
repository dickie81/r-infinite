import KubotaThetaProof
import KubotaCuspPoincare
import KubotaRowsDual
import KubotaGHolo
import KubotaUnfold
import KubotaThetaPair
import KubotaPmPair
import KubotaCubeEigen
import KubotaCTPrinciple
import KubotaCoefSupp
import RealCharHalfPlane

/-! Stack review 3: each `example` restates a reader-pass duplicate (by `type_of%`, so the statement is the
stack's own) and proves it in one step from the more general lemma it is claimed to be an instance of. -/

open Complex
open scoped NumberField ComplexConjugate

namespace Eis

-- KubotaPhi:99 against Mathlib's `Ideal.span_singleton_mul_left_unit`.
example : type_of% @span_unit_mul := by
  intros; exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _

-- KubotaPhi:400 against Mathlib's `Complex.cpow_ne_zero_iff`.
example : type_of% @cpow_ne_zero_of_ne := by
  intros; exact Complex.cpow_ne_zero_iff.2 (Or.inl ‹_›)

-- KubotaLocalFactors:289 against Mathlib's `Ideal.IsPrime.mul_mem_left_iff`.
example : type_of% @mul_mem_iff_right := by
  intro P e x he; haveI := P.2.1.isPrime; exact Ideal.IsPrime.mul_mem_left_iff he

-- KubotaLocalFactors:244 against Mathlib's `MulChar.inv_apply'` and `inv_apply_eq_inv'` (no `h ≠ 0`).
example : type_of% @mulChar_inv := by
  intros; rw [← MulChar.inv_apply', MulChar.inv_apply_eq_inv']

-- KubotaLocalFactors:258 against Mathlib's `pow_eq_pow_mod`.
example : type_of% @pow_eq_pow_of_six := by
  intro u hu a b hab; rw [pow_eq_pow_mod a hu, pow_eq_pow_mod b hu, hab]

-- KubotaPhi:475 against round 477's `RealChar.one_sub_mul_cpow_ne_zero` at `p = 3`, `a = 1`.
example : type_of% @one_sub_three_cpow_ne_zero := by
  intro w hw
  have := RealChar.one_sub_mul_cpow_ne_zero Nat.prime_three (a := 1) (by simp) hw
  simpa using this

-- KubotaCharacter:411 against Mathlib's `Subgroup.Normal.conj_mem'`.
example : type_of% @conj_mem_Gam3 := by
  intro γ hγ g; exact gam3_normal.conj_mem' γ hγ g

-- KubotaCubeSum:183 against Mathlib's `PrincipalIdealRing.isMaximal_of_irreducible`.
example : type_of% @span_isMaximal_of_prime := by
  intro p hp; exact PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible

-- KubotaCubeSum:191 against Mathlib's `Prime.coprime_iff_not_dvd`.
example : type_of% @isCoprime_of_not_dvd := by
  intro p x hp h; exact ((Prime.coprime_iff_not_dvd hp).2 h).symm

-- KubotaEisenstein:152 against round 438's `IsUChar.map_inv` at `isUChar_kub`.
example : type_of% @kub_inv_Gam3 := by
  intro g hg; exact isUChar_kub.map_inv hg

-- KubotaCuspPoincare:55 and KubotaPoincare:73 against `conj_mul_self_of_uchar`.
example : type_of% @kubT_mul_conj := by
  intro t g hg; exact conj_mul_self_of_uchar (isUChar_kubT t) hg
example : type_of% @kub_mul_conj_kub := by
  intro g hg; exact conj_mul_self_of_uchar isUChar_kub hg

-- KubotaCTPrinciple:254 against `IsAut.enorm`.
example : type_of% @enorm_slAct_of_isAut := by
  intro u hu γ hγ p hp; exact IsAut.enorm isUChar_kub hu hγ hp

-- KubotaCoefSupp:266 against KubotaCuspSums:174.
example : type_of% @coprime_three_of_primary := by
  intro n hn; exact (coprime_three_absNorm hn).symm

-- KubotaRowsDual:53 against EisensteinQuadSieveNorm:246.
example : type_of% @disjoint_primeSet := by
  intro x y h; exact (primeSet_disjoint h).symm

-- KubotaEisTrunc:722 against KubotaGHolo:509.
example : type_of% @memLp_gfun := by
  intro R hR s hs Y hY; exact memLp_gfun_all hR hY s

-- KubotaUnfold:374 against KubotaEisTrunc:276 at `F = 1`.
example : type_of% @lintegral_puLe_top_lt_top := by
  intro Γ _
  have := lintegral_puLe_top_mul_lt_top Γ (F := fun _ => 1) measurable_const
    (fun _ => ⟨1, ENNReal.one_ne_top, fun _ _ => le_rfl⟩)
  simpa using this

-- KubotaThetaPair:151 against KubotaPmPair:322.
example : type_of% @uhsMeasure_fundP3_Icc_lt_top := by
  intro α β hα; exact uhsMeasure_fundP3_Icc_lt_top_of_pos (by linarith)

-- KubotaThetaEq:210 against KubotaCubeEigen:356.
example : type_of% @continuousOn_slAct := by
  intro γ; exact continuousOn_actP (det_map_σO γ.2)

end Eis
