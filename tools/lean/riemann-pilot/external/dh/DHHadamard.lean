import Mathlib
import DavenportHeilbronn

/-! # Davenport–Heilbronn in Lean, stage 2: the Hadamard product of `Ξ_{DH}` (round 254)

Round 225's growth chain for `Ξ_χ` (`norm_LamG_le → norm_XiC_le → hadamard_XiC`, RealDirichlet.lean
and WeilChi.lean) takes `χ` real: its integral representation `LFunction_eq_Iχ` is for the L-series of
`Re χ`, and the reflection to `Re s < ½` uses `χ⁻¹ = χ`. Here the chain is rebuilt for every primitive
`χ ≠ 1`:

* complex partial sums, `‖Σ_{k<n} χ(k)‖ ≤ N` (`norm_sum_cC_le`) and `‖S(x)‖ ≤ N + 1`;
* `L(s, χ) = s∫_1^∞ S(x)x^{−s−1}dx` on `Re s > 0` from Mathlib's `LSeries_eq_mul_integral`
  (`LFunction_eq_IχC`), hence `‖L(s, χ)‖ ≤ (N + 1)‖s‖/Re s` (`norm_LFunction_leC`);
* `‖Λ*(w)‖ ≤ n^{3n}` on `Re w ≥ ½` (`norm_LamG_leC`), the reflection `Λ*(1 − s, χ) = ε_χ Λ*(s, χ⁻¹)`
  (`LamG_one_sub'`), and the order bound `‖Ξ_χ(t)‖ ≤ K_χ e^{36‖t‖^{3/2}}` for every primitive `χ`
  (`norm_XiC_le'`), which, unlike round 225's, needs no `L(½, χ) ≠ 0`;
* for the Davenport–Heilbronn combination (DavenportHeilbronn.lean): `‖Ξ_{DH}(t)‖ ≤ K e^{36‖t‖^{3/2}}`
  (`norm_XiDH_le`), `Ξ_{DH}(0) = 2(1 + ε_{χ⁻¹}) Λ*(½, χ)` (`XiDH_zero_eq`), and **the Hadamard
  product** `HadamardW (XiDH χ)` from `hadamardW_even`, under `ε_χ ≠ −1` and `L(½, χ) ≠ 0`
  (`hadamard_XiDH`).

For `χ₅` the first input is round 253's `rootNumber_chi5_ne_neg_one`; the second is the named input
`DHHalf : L(½, χ₅) ≠ 0`, and `hadamard_dh : DHHalf → HadamardW (XiDH chi5) …` gives the zeros of the
Davenport–Heilbronn `Ξ`, squared, as the indexed family `ZeroIdx (sqF (XiDH chi5))` with multiplicities,
summable inverses, and the product formula. What remains for the certificate chain is the explicit
formula (the prime side of `−dh′/dh`) and the certificate arithmetic; see the README, round 254.
(Superseded: `DHHalf` is proved in round 255, `dhHalf` in DHZeros.lean, so `hadamard_dh'` is
unconditional; the explicit formula landed in rounds 256–257 and the certificate in round 261,
`dh_offline_zero` in DHCertificate.lean.) (Round 509: the first two items and `LamG_one_sub'` moved,
unchanged, to src/LFunctionGrowth.lean, so that the pnt layer can use them.) (Round 511: `norm_LamG_leC`
is removed: round 224's `norm_LamG_le` (RealDirichlet.lean) now holds for every `χ ≠ 1`, and
`LamG_one_sub'` moved on to RealDirichlet.lean.)
-/

open Real Complex DirichletCharacter Filter Topology MeasureTheory Set Asymptotics

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-! ## The growth of `Ξ_χ`, `Ξ_{DH}` -/

/-- `n^{3n} ≤ exp(12 n√n)`. -/
theorem pow_three_mul_le_exp {n : ℕ} (hn0 : (0 : ℝ) < n) :
    (n : ℝ) ^ (3 * n) ≤ Real.exp (12 * ((n : ℝ) * Real.sqrt n)) := by
  calc (n : ℝ) ^ (3 * n) = Real.exp ((3 * n : ℝ) * Real.log n) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hn0]; push_cast; ring_nf
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        have hl := log_le_two_sqrt hn0
        nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- **The order of `Ξ_χ` for every primitive `χ ≠ 1`**: `‖Ξ_χ(t)‖ ≤ K_χ exp(36‖t‖^{3/2})`, with the
functional equation reflecting `Re(½ + it) < ½` to `χ⁻¹`. -/
theorem norm_XiC_le' (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℂ) :
    ‖XiC χ t‖ ≤ KC χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  set x := ‖t‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg t
  set M : ℝ := (N : ℝ) + 5
  have hM : 0 ≤ M := by positivity
  set n : ℕ := ⌈x⌉₊ + N + 4
  have hnx : (n : ℝ) ≤ x + M := by
    have := Nat.ceil_lt_add_one hx0; simp only [n, M]; push_cast; linarith
  have hxn : x + N + 4 ≤ (n : ℝ) := by
    have := Nat.le_ceil x; simp only [n]; push_cast; linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn4 : 4 ≤ n := by simp only [n]; omega
  have hn1 : ‖1 / 2 + I * t‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
  have hn2 : ‖1 / 2 + I * -t‖ ≤ 1 / 2 + x := (norm_add_le _ _).trans (by simp [hx])
  -- `‖Ξ_χ(t)‖ ≤ (‖ε‖ + 1) n^{3n}` in both cases
  have hmain : ‖XiC χ t‖ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) := by
    rcases le_total (1 / 2) (1 / 2 + I * t).re with h | h
    · have hL := norm_LamG_le hχ1 h (n := n) (by linarith) (by linarith) hn4
      have hp : (0 : ℝ) ≤ (n : ℝ) ^ (3 * n) := by positivity
      calc ‖XiC χ t‖ = ‖LamG χ (1 / 2 + I * t)‖ := rfl
        _ ≤ (n : ℝ) ^ (3 * n) := hL
        _ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) := by nlinarith [norm_nonneg (rootNumber χ)]
    · have hre : 1 / 2 ≤ (1 / 2 + I * -t).re := by
        simp only [add_re, mul_re, I_re, I_im, neg_re, neg_im] at h ⊢; norm_num at h ⊢; linarith
      have hL := norm_LamG_le (inv_ne_one.2 hχ1) hre (n := n) (by linarith) (by linarith) hn4
      have e : LamG χ (1 / 2 + I * t) = rootNumber χ * LamG χ⁻¹ (1 / 2 + I * -t) := by
        rw [← LamG_one_sub' hprim]; congr 1; ring
      calc ‖XiC χ t‖ = ‖rootNumber χ * LamG χ⁻¹ (1 / 2 + I * -t)‖ := by rw [XiC, e]
        _ = ‖rootNumber χ‖ * ‖LamG χ⁻¹ (1 / 2 + I * -t)‖ := norm_mul _ _
        _ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) :=
            mul_le_mul (by linarith) hL (norm_nonneg _) (by positivity)
  have hns : (n : ℝ) * Real.sqrt n ≤ 3 * (x * Real.sqrt x) + 3 * (M * Real.sqrt M) :=
    le_trans (mul_le_mul hnx (Real.sqrt_le_sqrt hnx) (Real.sqrt_nonneg _) (by linarith))
      (shift_sqrt hx0 hM)
  have hx32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hx0 (by norm_num), Real.rpow_one]
  rw [hx32]
  have hKC : (‖rootNumber χ‖ + 1) * Real.exp (36 * (M * Real.sqrt M)) ≤ KC χ := by
    unfold KC; simp only [M]; linarith
  calc ‖XiC χ t‖ ≤ (‖rootNumber χ‖ + 1) * (n : ℝ) ^ (3 * n) := hmain
    _ ≤ (‖rootNumber χ‖ + 1) * Real.exp (12 * ((n : ℝ) * Real.sqrt n)) := by
        gcongr; exact pow_three_mul_le_exp hn0
    _ ≤ (‖rootNumber χ‖ + 1) * Real.exp (12 * (3 * (x * Real.sqrt x) + 3 * (M * Real.sqrt M))) := by
        gcongr
    _ = ((‖rootNumber χ‖ + 1) * Real.exp (36 * (M * Real.sqrt M))) * Real.exp (36 * (x * Real.sqrt x)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ KC χ * Real.exp (36 * (x * Real.sqrt x)) := by gcongr

/-- The growth constant of `Ξ_{DH}`. -/
def KDH (χ : DirichletCharacter ℂ N) : ℝ :=
  ‖1 + rootNumber χ⁻¹‖ * KC χ + ‖1 + rootNumber χ‖ * KC χ⁻¹ + 1

theorem one_le_KDH : 1 ≤ KDH χ := by
  unfold KDH
  have h1 := one_le_KC (χ := χ)
  have h2 := one_le_KC (χ := χ⁻¹)
  nlinarith [norm_nonneg (1 + rootNumber χ⁻¹), norm_nonneg (1 + rootNumber χ)]

/-- **The order of `Ξ_{DH}`**: `‖Ξ_{DH}(t)‖ ≤ K exp(36‖t‖^{3/2})`. -/
theorem norm_XiDH_le (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℂ) :
    ‖XiDH χ t‖ ≤ KDH χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  have h1 := norm_XiC_le' hχ1 hprim t
  have h2 := norm_XiC_le' (inv_ne_one.2 hχ1) (isPrimitive_inv χ hprim) t
  have he : 0 < Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := Real.exp_pos _
  calc ‖XiDH χ t‖ = ‖(1 + rootNumber χ⁻¹) * XiC χ t + (1 + rootNumber χ) * XiC χ⁻¹ t‖ := rfl
    _ ≤ ‖1 + rootNumber χ⁻¹‖ * ‖XiC χ t‖ + ‖1 + rootNumber χ‖ * ‖XiC χ⁻¹ t‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ ‖1 + rootNumber χ⁻¹‖ * (KC χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)))
        + ‖1 + rootNumber χ‖ * (KC χ⁻¹ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ))) := by gcongr
    _ ≤ KDH χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by unfold KDH; nlinarith

/-! ## `Ξ_{DH}(0) ≠ 0` and the Hadamard product -/

/-- `Ξ_{DH}(0) = 2(1 + ε_{χ⁻¹}) Λ*(½, χ)`. -/
theorem XiDH_zero_eq (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) :
    XiDH χ 0 = 2 * (1 + rootNumber χ⁻¹) * LamG χ (1 / 2) := by
  have heps := rootNumber_mul_rootNumber_inv χ hχ1 hprim
  have hFE := LamG_one_sub' (isPrimitive_inv χ hprim) (1 / 2)
  rw [inv_inv, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hFE
  show (1 + rootNumber χ⁻¹) * LamG χ (1 / 2 + I * 0) + (1 + rootNumber χ) * LamG χ⁻¹ (1 / 2 + I * 0) = _
  rw [mul_zero, add_zero, hFE]
  linear_combination (LamG χ (1 / 2)) * heps

theorem one_add_rootNumber_inv_ne_zero (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive)
    (h : 1 + rootNumber χ ≠ 0) : 1 + rootNumber χ⁻¹ ≠ 0 := by
  have heps := rootNumber_mul_rootNumber_inv χ hχ1 hprim
  intro h0
  apply h
  linear_combination rootNumber χ * h0 - heps

/-- **`Ξ_{DH}(0) ≠ 0`** when `ε_χ ≠ −1` and `L(½, χ) ≠ 0`. -/
theorem XiDH_zero_ne (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    (hhalf : LFunction χ (1 / 2) ≠ 0) : XiDH χ 0 ≠ 0 := by
  rw [XiDH_zero_eq hχ1 hprim]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (one_add_rootNumber_inv_ne_zero hχ1 hprim h1))
    (LamG_ne_zero (by norm_num) hhalf)

/-- **The Hadamard product of `Ξ_{DH}`**: the squares `u` of its zeros, with multiplicity, have summable inverses and
`Ξ_{DH}(t)/Ξ_{DH}(0) = Π (1 − t²/u)` over the zeros `u` of `t ↦ Ξ_{DH}(√t)`. -/
theorem hadamard_XiDH (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    (hhalf : LFunction χ (1 / 2) ≠ 0) :
    HadamardW (XiDH χ) (fun i : ZeroIdx (sqF (XiDH χ)) => i.1⁻¹) :=
  hadamardW_even (differentiable_XiDH χ hχ1) (XiDH_even χ hχ1 hprim) (XiDH_zero_ne hχ1 hprim h1 hhalf)
    one_le_KDH (by norm_num) (by norm_num) (by norm_num) (norm_XiDH_le hχ1 hprim)

/-! ## The Davenport–Heilbronn function -/

/-- **The one named input of stage 2**, discharged in round 255 (`dhHalf`, DHZeros.lean): `L(½, χ₅) ≠ 0` (numerically `L(½, χ₅) ≈ 0.763748 + 0.216965i`, `|L(½, χ₅)| ≈ 0.793968`, by Hurwitz zeta in mpmath, not proved here). -/
def DHHalf : Prop := LFunction chi5 (1 / 2) ≠ 0

theorem norm_XiDH_chi5_le (t : ℂ) : ‖XiDH chi5 t‖ ≤ KDH chi5 * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) :=
  norm_XiDH_le chi5_ne_one chi5_isPrimitive t

theorem XiDH_chi5_zero_ne (h : DHHalf) : XiDH chi5 0 ≠ 0 :=
  XiDH_zero_ne chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero h

/-- **The Hadamard product of the Davenport–Heilbronn `Ξ`**, given `L(½, χ₅) ≠ 0`. -/
theorem hadamard_dh (h : DHHalf) :
    HadamardW (XiDH chi5) (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) :=
  hadamard_XiDH chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero h

end PsiOmega

#print axioms PsiOmega.norm_XiC_le'
#print axioms PsiOmega.norm_XiDH_le
#print axioms PsiOmega.XiDH_zero_eq
#print axioms PsiOmega.XiDH_zero_ne
#print axioms PsiOmega.hadamard_XiDH
#print axioms PsiOmega.norm_XiDH_chi5_le
#print axioms PsiOmega.hadamard_dh
