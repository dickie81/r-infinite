import KubotaThetaProof
import KubotaCTCover
import KubotaCubeDecomp
import KubotaThetaInv
import KubotaVsharp
import EisensteinQuadSieveFinal
import BinetEnvelope
import EulerGammaBinet
import CascadeLepton
import HilbertResolvent
import BohrJoins
import ShellCount
import VolumeShell
import EuclideanForcing
import SphereDimensions
import DetectCore
import MeanSquareZeta
import HalfPlaneJoinsFinal

/-! Stack review 3, second batch: duplicates restated by `type_of%` and proved in one step from the more
general lemma; two Bohr-strand joins. -/

open Complex MeasureTheory
open scoped NumberField ComplexConjugate InnerProductSpace

namespace Eis

-- KubotaTheta:203 is more general than EisensteinCompletedSums:235.
example : type_of% @one_le_absNorm_of_coprime6 := by
  intro I h; exact one_le_absNorm_of_coprime3 (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h)

-- KubotaConstTerm:346 is KubotaTranslates:85 at `3c`.
example : type_of% @finite_quot_three_mul := by
  intro c hc; exact finite_quot _ (three_mul_ne_zero hc)

-- KubotaCTCover:43 is KubotaCusps:162.
example : type_of% @actP_one := by
  intro p; exact uhsAct_one p.1 p.2

-- KubotaMeasure:229 is KubotaCubeDecomp:51 at `b = 0`.
example : type_of% @uhsAct_diag := by
  intro a ha z v; simpa using uhsAct_upper_inv ha 0 z v

-- KubotaEisenstein:355 is KubotaEisTrunc:142 at the profile `v ↦ v^s` (`eis1_eq_pseis` is `rfl`).
example : type_of% @eis1_slAct := by
  intro g hg s p hp; rw [eis1_eq_pseis]; exact isAut_pseis _ g hg p hp

-- KubotaTranslates:381 and 384 against core's `Nat.Coprime.coprime_mul_right`/`_left`.
example : type_of% @coprime6_left := fun h => Nat.Coprime.coprime_mul_right h
example : type_of% @coprime6_right := fun h => Nat.Coprime.coprime_mul_left h

-- KubotaThetaInv:46 against Mathlib's `Subgroup.subgroupOf_self` and `subsingleton_quotient_top`.
example : type_of% @subsingleton_quot_gam3 := by
  rw [Subgroup.subgroupOf_self]; exact QuotientGroup.subsingleton_quotient_top

-- KubotaVsharp:59 against Mathlib's `Complex.norm_exp_I_mul_ofReal`.
example : type_of% @norm_cexp_I_mul := by
  intro u w; rw [mul_assoc, ← Complex.ofReal_mul]; exact Complex.norm_exp_I_mul_ofReal _

-- The nine inline proofs of `(3 : 𝓞 K) ≠ 0`.
example : (3 : 𝓞 K) ≠ 0 := by norm_num

-- EisensteinQuadSieveRecursion:380 against EisensteinFirstTransfer:833.
example : type_of% @card_fsLe_mono := by
  intro x y h; exact_mod_cast Finset.card_le_card (fsLe_mono h)

-- EisensteinQuadSieveLattice:541 against Mathlib's `Finset.prod_sub`.
example : type_of% @sum_powerset_neg_prod := by
  intro ι S a
  classical
  rw [Finset.prod_sub]
  simp

-- EisensteinQuadSieveGamma:174 against Mathlib's `Complex.I_zpow_eq_zpow_mod`.
example : type_of% @I_zpow_four_mul_add := by
  intro q k; rw [Complex.I_zpow_eq_zpow_mod, Complex.I_zpow_eq_zpow_mod k]; congr 1; omega

-- EisensteinQuadSieveErrors:36 against Mathlib's `Integrable.mul_bdd`.
example : type_of% @integrable_mul_bdd := by
  intro C g hC hg B hB; exact hC.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)

-- EisensteinQuadSieveLemma14:168 against Mathlib's `Measure.ae_ne`.
example : type_of% @ae_ne_zero_complex := Measure.ae_ne volume 0

-- EisensteinQuadSieveRecursion:545 against Mathlib's `Real.rpow_le_rpow_of_exponent_le`.
example : type_of% @rpow_le_rpow_Q := by
  intros; exact Real.rpow_le_rpow_of_exponent_le ‹_› ‹_›

-- EisensteinQuadSieveNorm:343: its hypothesis `n ≠ 0` follows from `Primary n`.
example {n : 𝓞 K} (hp : Primary n) : n ≠ 0 := by
  rintro rfl; exact Primary.not_lam_dvd hp (dvd_zero _)

-- HilbertResolvent:38 against Mathlib's `LinearMap.IsSymmetric.im_inner_apply_self`.
example : type_of% @im_inner_apply_self := by
  intros; exact LinearMap.IsSymmetric.im_inner_apply_self (IsSelfAdjoint.isSymmetric ‹_›) _

end Eis

-- BinetEnvelope:289 is EulerGammaBinet's `le_phiB` and `phiB_le` (round 406).
example : type_of% @BinetEnvelope.phiB_order_one := by
  intro s hs; exact ⟨Electron.le_phiB hs, Electron.phiB_le hs⟩

-- BinetEnvelope:362's first conjunct is EulerGammaBinet:125.
example {x : ℝ} (hx : 0 < x) : type_of% (Electron.le_lapR hx) := (BinetEnvelope.lapR_stirling2 hx).1

-- BinetEnvelope:57 is ThermalZeta:120 at a natural exponent.
example : type_of% @BinetEnvelope.summable_Zs := by
  intro m hm
  have := ThermalZeta.summable_succ_rpow (σ := (m : ℝ)) (by exact_mod_cast (show 1 < m by omega))
  simpa [Real.rpow_natCast] using this

-- DigammaGauss:290 is EulerGammaBinet:92 at `k = 1`.
example : type_of% @PilotDigamma.integral_mul_exp_neg := by
  intro c hc
  have := Electron.integral_pow_mul_exp hc 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at this
  rw [this]; ring

-- ThermalZeta:249 against Mathlib's `Complex.GammaIntegral_eq_mellin`.
example : type_of% @ThermalZeta.mellin_boltz := by
  intro s hs; rw [← Complex.GammaIntegral_eq_mellin, Complex.Gamma_eq_integral hs]

-- CascadeLepton:69 against Mathlib's `Real.Gamma_nat_add_one_add_half` at `k = 0`.
example : type_of% @Electron.Gamma_three_halves := by
  convert Real.Gamma_nat_add_one_add_half 0 using 1 <;> norm_num

-- CascadeLepton:257 against Mathlib's `Real.exp_one_pow`.
example : type_of% @Electron.exp_nat := fun n => (Real.exp_one_pow n).symm

-- BohrJoins:49 is one direction of ShellCount:40.
example : type_of% @BohrJoins.norm_vF_le_norm_vF := by
  intro F hF s s' h; exact (ShellCount.norm_vF_le_iff hF s' s).2 h

-- VolumeShell:30 is EuclideanForcing:291 at `volume` on `EuclideanSpace ℝ (Fin n)`.
example : type_of% @VolumeShell.volume_ball_fraction := by
  intro n r hr; rw [EuclideanForcing.addHaar_ball_fraction volume hr, finrank_euclideanSpace_fin]

-- SphereDimensions:35 against Mathlib's `orthonormal_subsingleton_iff`.
example : type_of% @SphereDimensions.orthonormal_singleton_of_norm := by
  intros
  exact orthonormal_subsingleton_iff.2 fun i => by simpa [Set.mem_singleton_iff.1 i.2]

namespace StackReview3

open Pilot1ca Pilot1bt ShortWeil

/-- **`EMApprox → EMBound`**: at a zero `β + iγ` with `β ≤ 2 ≤ |γ|`, `β + |γ| ≤ 2|γ|`. -/
theorem emBound_of_emApprox (h : MeanSquareZeta.EMApprox) : DetectCore.EMBound := by
  intro β γ hβ hβ2 hγ hz N hN
  have hE := h hβ hγ hN
  rw [hz, zero_sub, norm_neg] at hE
  refine hE.trans ?_
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (-β) := by positivity
  have hk : (β + |γ|) * (N : ℝ) ^ (-β) / β ≤ 2 * |γ| * (N : ℝ) ^ (-β) / β := by
    apply div_le_div_of_nonneg_right _ hβ.le
    exact mul_le_mul_of_nonneg_right (by linarith) hN0
  linarith

/-- **No pair outside the shell of half-width `w > 5/12`**: round 468's `|Im τ| ≤ 5/12`. -/
theorem NX_eq_zero_of_five_twelfths_lt {w : ℝ} (hw : 5 / 12 < w) (T : ℝ) : NX w T = 0 := by
  unfold NX
  have : {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T ∧ w ≤ |(tau i).im|} = ∅ := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _
    linarith [HalfPlaneJoins.abs_im_tau_le_five_twelfths i]
  rw [this, Set.ncard_empty]

end StackReview3

#print axioms StackReview3.emBound_of_emApprox
#print axioms StackReview3.NX_eq_zero_of_five_twelfths_lt
