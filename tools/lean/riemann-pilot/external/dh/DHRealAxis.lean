import Mathlib
import DHCertificate

/-! # `dh` has no zero on the positive real axis

`dh = (1 + ε′)L(s, χ₅) + (1 + ε)L(s, χ₅⁻¹)` has Dirichlet coefficients
`a(n) = a(1)·u(n mod 5)` with `u = 0, 1, κ, −κ, −1` (`aDH_chi5_eq_mul`), whose partial sums
`Σ_{k<m} a(k) = a(1)·B(m mod 5)` take the values `0, 0, 1, 1 + κ, 1` (`sum_range_aDH_chi5`,
`Bval_mod_five`), all `≥ 0`, and `= 1` on `[1, 2)`. Round 254's integral representation
`L(s, χ) = s∫_1^∞ S_χ(x)x^{−s−1}dx` (`LFunction_eq_IχC`) applied to both terms gives
`dh(s) = s∫_1^∞ A(x)x^{−s−1}dx` with `A(x) = Σ_{n ≤ x} a(n) = a(1)B(x)` (`dh_eq_integral`), so for real
`σ > 0`, `dh(σ)/a(1) = σ∫_1^∞ B(x)x^{−σ−1}dx ≥ σ∫_1^2 x^{−σ−1}dx = 1 − 2^{−σ} > 0`
(`dh_eq_integral_real`, `dh_div_a1_real_ge`). Hence `dh(σ) ≠ 0` for `σ > 0`
(`dh_ne_zero_of_real`), `Λ_{dh}(σ) ≠ 0` for every real `σ` by the functional equation
(`dhLam_real_ne_zero`), `Ξ_{dh}` has no zero on the imaginary axis (`XiDH_I_mul_ne_zero`), and the
certificate's off-line zero is off the real axis as well (`dh_offcross_zero`). On the negative real axis `dh`
does vanish: `dh(−1) = 0` (`dh_neg_one_eq_zero`), the trivial zero shared by `L(s, χ₅)` and `L(s, χ₅⁻¹)`,
both characters being odd (round 271: the title read "no zero on the real axis" before).
-/

open Real Complex DirichletCharacter MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt

/-! ## The coefficients and their partial sums -/

/-- **`a(n) = a(1)·u(n mod 5)`** for every `n`, including `n = 0, 1`. -/
theorem aDH_chi5_eq_mul (n : ℕ) : aDH chi5 n = aDH chi5 1 * ((uval (n % 5) : ℝ) : ℂ) := by
  rw [aDH_chi5_eq n, aDH_chi5_eq 1, ← chi5_re_add_kappa_im n, ← Complex.ofReal_mul]
  congr 1
  simp only [Nat.cast_one, chi5_apply_one, Complex.one_re, Complex.one_im]
  rw [← kappa_mul_one_add]
  ring

theorem aDH_chi5_zero : aDH chi5 0 = 0 := by
  rw [aDH_chi5_eq_mul]; simp [uval]

theorem aDH_chi5_period (k : ℕ) : aDH chi5 (k + 5) = aDH chi5 k := by
  rw [aDH_chi5_eq_mul, aDH_chi5_eq_mul k, Nat.add_mod_right]

theorem sum_range_aDH_chi5_period : ∑ k ∈ Finset.range 5, aDH chi5 k = 0 := by
  rw [Finset.sum_congr rfl fun k _ => aDH_chi5_eq_mul k, ← Finset.mul_sum, ← Complex.ofReal_sum]
  have h : ∑ k ∈ Finset.range 5, uval (k % 5) = 0 := by
    simp [Finset.sum_range_succ, uval]
  rw [h, Complex.ofReal_zero, mul_zero]

/-- The partial-sum pattern of the normalised coefficients: `B(r) = Σ_{k<r} u(k)`. -/
def Bval (r : ℕ) : ℝ := ∑ k ∈ Finset.range r, uval k

/-- **The partial sums of `a`**: `Σ_{k<m} a(k) = a(1)·B(m mod 5)`. -/
theorem sum_range_aDH_chi5 (m : ℕ) :
    ∑ k ∈ Finset.range m, aDH chi5 k = aDH chi5 1 * (Bval (m % 5) : ℂ) := by
  rw [sum_range_modC _ aDH_chi5_period sum_range_aDH_chi5_period m, Bval, Complex.ofReal_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk5 : k < 5 := lt_of_lt_of_le (Finset.mem_range.1 hk) (Nat.mod_lt _ (by norm_num)).le
  rw [aDH_chi5_eq_mul, Nat.mod_eq_of_lt hk5]

/-- **`B = 0, 0, 1, 1 + κ, 1`** on the residues `0, …, 4`. -/
theorem Bval_values :
    Bval 0 = 0 ∧ Bval 1 = 0 ∧ Bval 2 = 1 ∧ Bval 3 = 1 + kappa ∧ Bval 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Bval, Finset.sum_range_succ, uval]

/-- **`B(m mod 5) ∈ {0, 1, 1 + κ}`**. -/
theorem Bval_mod_five (m : ℕ) :
    Bval (m % 5) = 0 ∨ Bval (m % 5) = 1 ∨ Bval (m % 5) = 1 + kappa := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := Bval_values
  have h5 : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize m % 5 = r at h5 ⊢
  interval_cases r <;> simp [h0, h1, h2, h3, h4]

theorem Bval_mod_nonneg (m : ℕ) : 0 ≤ Bval (m % 5) := by
  rcases Bval_mod_five m with h | h | h <;> rw [h] <;> linarith [kappa_pos]

theorem Bval_mod_le (m : ℕ) : Bval (m % 5) ≤ 2 := by
  rcases Bval_mod_five m with h | h | h <;> rw [h] <;> linarith [kappa_lt]

/-! ## The summatory function -/

/-- The summatory function `A(x) = Σ_{1 ≤ n ≤ x} a(n)`. -/
def summDH (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, aDH chi5 k

/-- Its normalised real form `B(x) = A(x)/a(1)`. -/
def BDH (x : ℝ) : ℝ := Bval ((⌊x⌋₊ + 1) % 5)

theorem summDH_eq (x : ℝ) : summDH x = aDH chi5 1 * (BDH x : ℂ) := by
  rw [summDH, sum_Icc_eqC, sum_range_aDH_chi5, aDH_chi5_zero, sub_zero, BDH]

theorem summDH_eq_summC (x : ℝ) :
    summDH x = (1 + rootNumber chi5⁻¹) * summC chi5 x + (1 + rootNumber chi5) * summC chi5⁻¹ x := by
  unfold summDH summC aDH cC
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

theorem BDH_nonneg (x : ℝ) : 0 ≤ BDH x := Bval_mod_nonneg _

theorem BDH_le (x : ℝ) : BDH x ≤ 2 := Bval_mod_le _

/-- **`B = 1` on `[1, 2)`.** -/
theorem BDH_eq_one {x : ℝ} (h1 : 1 ≤ x) (h2 : x < 2) : BDH x = 1 := by
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]; norm_num; exact ⟨h1, h2⟩
  rw [BDH, hf]
  exact Bval_values.2.2.1

theorem measurable_BDH : Measurable BDH :=
  (measurable_from_nat (f := fun n : ℕ => Bval ((n + 1) % 5))).comp Nat.measurable_floor

/-! ## The integral representation -/

theorem integrableOn_summC_cpow {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => summC χ x * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hmaj : IntegrableOn (fun x : ℝ => ((N : ℝ) + 1) * x ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · refine measurable_summC.aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const ?_
    intro x hx
    exact Or.inl (by simpa using lt_trans one_pos (show (1 : ℝ) < x from hx))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_)
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have e : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (norm_summC_le hχ1 x) (by positivity)

/-- **`dh(s) = s∫_1^∞ A(x)x^{−s−1}dx` on `Re s > 0`.** -/
theorem dh_eq_integral {s : ℂ} (hs : 0 < s.re) :
    dh s = s * ∫ x in Ioi (1 : ℝ), summDH x * (x : ℂ) ^ (-(s + 1)) := by
  have h1 := integrableOn_summC_cpow chi5_ne_one hs
  have h2 := integrableOn_summC_cpow chi5_inv_ne_one hs
  have e : ∀ x : ℝ, summDH x * (x : ℂ) ^ (-(s + 1)) =
      (1 + rootNumber chi5⁻¹) * (summC chi5 x * (x : ℂ) ^ (-(s + 1)))
        + (1 + rootNumber chi5) * (summC chi5⁻¹ x * (x : ℂ) ^ (-(s + 1))) := fun x => by
    rw [summDH_eq_summC]; ring
  simp_rw [e]
  rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
  unfold dh dhL
  rw [LFunction_eq_IχC chi5_ne_one hs, LFunction_eq_IχC chi5_inv_ne_one hs]
  unfold IχC
  ring

/-- **`dh(σ) = a(1)·σ∫_1^∞ B(x)x^{−σ−1}dx`** for real `σ > 0`. -/
theorem dh_eq_integral_real {σ : ℝ} (hσ : 0 < σ) :
    dh σ = aDH chi5 1 * ((σ * ∫ x in Ioi (1 : ℝ), BDH x * x ^ (-σ - 1) : ℝ) : ℂ) := by
  rw [dh_eq_integral (by simpa using hσ)]
  have hc : ∫ x in Ioi (1 : ℝ), summDH x * (x : ℂ) ^ (-((σ : ℂ) + 1)) =
      ∫ x in Ioi (1 : ℝ), aDH chi5 1 * ((BDH x * x ^ (-σ - 1) : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun x (hx : 1 < x) => by
      have e : (x : ℂ) ^ (-((σ : ℂ) + 1)) = ((x ^ (-σ - 1) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (by linarith)]; congr 1; push_cast; ring
      rw [summDH_eq, e, Complex.ofReal_mul]; ring
  rw [hc, integral_const_mul, integral_complex_ofReal]
  push_cast
  ring

/-! ## The lower bound on the positive axis -/

theorem integrableOn_BDH_rpow {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => BDH x * x ^ (-σ - 1)) (Ioi 1) := by
  have hmaj : IntegrableOn (fun x : ℝ => 2 * x ^ (-σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine Integrable.mono' hmaj (measurable_BDH.mul (measurable_id.pow_const _)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) => ?_)
  have hp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (BDH_nonneg x), abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_right (BDH_le x) hp

/-- **`σ∫_1^∞ B(x)x^{−σ−1}dx ≥ 1 − 2^{−σ}`**: `B ≥ 0` everywhere and `B = 1` on `[1, 2)`. -/
theorem integral_BDH_ge {σ : ℝ} (hσ : 0 < σ) :
    1 - (2 : ℝ) ^ (-σ) ≤ σ * ∫ x in Ioi (1 : ℝ), BDH x * x ^ (-σ - 1) := by
  have hlow : ∫ x in Ioo (1 : ℝ) 2, x ^ (-σ - 1) ≤ ∫ x in Ioi (1 : ℝ), BDH x * x ^ (-σ - 1) := by
    calc ∫ x in Ioo (1 : ℝ) 2, x ^ (-σ - 1) = ∫ x in Ioo (1 : ℝ) 2, BDH x * x ^ (-σ - 1) :=
          setIntegral_congr_fun measurableSet_Ioo fun x hx => by
            simp only [BDH_eq_one hx.1.le hx.2, one_mul]
      _ ≤ _ := setIntegral_mono_set (integrableOn_BDH_rpow hσ)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x (hx : 1 < x) =>
              mul_nonneg (BDH_nonneg x) (Real.rpow_nonneg (by linarith) _)))
            (Eventually.of_forall Ioo_subset_Ioi_self)
  have hval : ∫ x in Ioo (1 : ℝ) 2, x ^ (-σ - 1) = (1 - (2 : ℝ) ^ (-σ)) / σ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      integral_rpow (Or.inr ⟨by linarith, by norm_num [Set.mem_uIcc]⟩)]
    rw [show -σ - 1 + 1 = -σ by ring, Real.one_rpow]
    field_simp; ring
  rw [hval] at hlow
  have := mul_le_mul_of_nonneg_left hlow hσ.le
  rwa [mul_div_cancel₀ _ hσ.ne'] at this

theorem aDH_chi5_one_ne_zero : aDH chi5 1 ≠ 0 :=
  aDH_one_ne_zero chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero

/-- **`dh(σ)/a(1)` is real** for `σ > 0`. -/
theorem dh_div_a1_real {σ : ℝ} (hσ : 0 < σ) :
    dh σ / aDH chi5 1 = ((σ * ∫ x in Ioi (1 : ℝ), BDH x * x ^ (-σ - 1) : ℝ) : ℂ) := by
  rw [dh_eq_integral_real hσ, mul_div_cancel_left₀ _ aDH_chi5_one_ne_zero]

theorem dh_div_a1_real_im {σ : ℝ} (hσ : 0 < σ) : (dh σ / aDH chi5 1).im = 0 := by
  rw [dh_div_a1_real hσ, Complex.ofReal_im]

/-- **`dh(σ)/a(1) ≥ 1 − 2^{−σ}`** for `σ > 0`. -/
theorem dh_div_a1_real_ge {σ : ℝ} (hσ : 0 < σ) : 1 - 2 ^ (-σ) ≤ (dh σ / aDH chi5 1).re := by
  rw [dh_div_a1_real hσ, Complex.ofReal_re]
  exact integral_BDH_ge hσ

/-! ## No zero of `dh` on the positive real axis, nor of `Λ_{dh}` on the real axis -/

/-- **`dh(σ) ≠ 0` for `σ > 0`.** -/
theorem dh_ne_zero_of_real {σ : ℝ} (hσ : 0 < σ) : dh (σ : ℂ) ≠ 0 := by
  rw [dh_eq_integral_real hσ]
  refine mul_ne_zero aDH_chi5_one_ne_zero (Complex.ofReal_ne_zero.2 ?_)
  have h1 := integral_BDH_ge hσ
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ne_of_gt (by linarith)

/-- **`Λ_{dh}(σ) ≠ 0` for every real `σ`**: on `σ > 0` from `dh(σ) ≠ 0`, on `σ ≤ 0` by the
functional equation at `1 − σ`. -/
theorem dhLam_real_ne_zero (σ : ℝ) : dhLam chi5 (σ : ℂ) ≠ 0 := by
  have pos : ∀ τ : ℝ, 0 < τ → dhLam chi5 (τ : ℂ) ≠ 0 := fun τ hτ h =>
    dh_ne_zero_of_real hτ ((dh_eq_zero_iff (by simpa using hτ)).2 h)
  rcases lt_or_ge 0 σ with hσ | hσ
  · exact pos σ hσ
  · have := pos (1 - σ) (by linarith)
    rwa [Complex.ofReal_sub, Complex.ofReal_one, dh_functional_equation] at this

/-- **`Ξ_{dh}` has no zero on the imaginary axis**: `Ξ_{dh}(it) = Λ_{dh}(½ − t)`. -/
theorem XiDH_I_mul_ne_zero (t : ℝ) : XiDH chi5 (Complex.I * t) ≠ 0 := by
  have e : (1 / 2 : ℂ) + I * (I * (t : ℂ)) = ((1 / 2 - t : ℝ) : ℂ) := by
    push_cast; linear_combination (t : ℂ) * I_sq
  show dhLam chi5 (1 / 2 + I * (I * t)) ≠ 0
  rw [e]
  exact dhLam_real_ne_zero _

/-- **An off-line zero of `dh` off the real axis**: the certificate's zero (`dh_offline_zero`) is
non-real because `dh` has no zero on the positive real axis. -/
theorem dh_offcross_zero : ∃ s : ℂ, dh s = 0 ∧ 0 < s.re ∧ s.re ≠ 1 / 2 ∧ s.im ≠ 0 := by
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  refine ⟨s, hs, h0, hne, fun him => ?_⟩
  have e : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hz : dh ((s.re : ℝ) : ℂ) = 0 := by rw [← e]; exact hs
  exact dh_ne_zero_of_real h0 hz

/-- `dh` vanishes at `s = −1`: the trivial zero shared by `L(s, χ₅)` and `L(s, χ₅⁻¹)` (both characters
are odd, `chi5_odd`, `chi5_inv_odd`; Mathlib's `Odd.LFunction_neg_two_mul_nat_sub_one`). -/
theorem dh_neg_one_eq_zero : dh (-1 : ℂ) = 0 := by
  have h1 := chi5_odd.LFunction_neg_two_mul_nat_sub_one 0
  have h2 := chi5_inv_odd.LFunction_neg_two_mul_nat_sub_one 0
  simp only [Nat.cast_zero, mul_zero, neg_zero, zero_sub] at h1 h2
  show dhL chi5 (-1) = 0
  unfold dhL
  rw [h1, h2]
  ring

/-- So `dh` does have a zero on the real axis; `dh_ne_zero_of_real` covers only `σ > 0`. -/
theorem exists_real_zero_dh : ∃ σ : ℝ, dh (σ : ℂ) = 0 :=
  ⟨-1, by push_cast; exact dh_neg_one_eq_zero⟩

end PsiOmega

#print axioms PsiOmega.dh_ne_zero_of_real
#print axioms PsiOmega.dhLam_real_ne_zero
#print axioms PsiOmega.XiDH_I_mul_ne_zero
#print axioms PsiOmega.dh_offcross_zero
#print axioms PsiOmega.dh_neg_one_eq_zero
#print axioms PsiOmega.exists_real_zero_dh
