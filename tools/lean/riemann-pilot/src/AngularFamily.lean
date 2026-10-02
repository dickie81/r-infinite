/-
# RH is the radial member of the ball's angular grinding family (round 189)

Plain statement.
* For each angular harmonic `k`, `angularCoeff k n` averages the direction `(z/|z|)^{4k}` over the
  teeth `z` on shell `n` of the 2D ball (divided by the 4 units). Its Dirichlet series
  `angularL k` is the `k`-th grinding channel of round 188 (Hecke's L-functions).
* The `k = 0` member (the radial channel) is exactly `ζ(s) · L(s, χ₄)` for `Re s > 1`
  (`member_zero_eq`). This uses the global tooth count (Jacobi's two-square theorem, round 187).
  `angularL0 = ζ · L(χ₄)` is its continuation to the whole plane.
* **RH is in the family** (`rh_of_member_zero`): "every zero of the `k = 0` member, apart from its
  trivial zeros at the negative integers and the pole, lies on `Re s = ½`" implies Mathlib's
  `RiemannHypothesis`. The converse also needs the same statement for `L(s, χ₄)`.

Not proved: continuation or zero statements for the members `k ≥ 1` (Hecke Grössencharacters are
not in Mathlib); only their Dirichlet series are defined here.
-/
import GlobalTeeth

open Complex GlobalTeeth
open scoped LSeries.notation

namespace AngularFamily

/-- `χ₄` as a complex Dirichlet character mod 4. -/
noncomputable def χ4C : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma χ4C_apply (n : ℕ) : χ4C n = ((ZMod.χ₄ n : ℤ) : ℂ) := by
  simp [χ4C, MulChar.ringHomComp_apply]

/-- The `k`-th angular coefficient: the average over shell `n` (per unit) of `(z/|z|)^{4k}`. -/
noncomputable def angularCoeff (k n : ℕ) : ℂ :=
  (1 / 4 : ℂ) * ∑ z ∈ shell n, ((z.re : ℂ) + z.im * I) ^ (4 * k) / (n : ℂ) ^ (2 * k)

/-- The `k`-th member of the family, as a Dirichlet series. -/
noncomputable def angularL (k : ℕ) (s : ℂ) : ℂ := LSeries (angularCoeff k) s

/-- The radial member continued to the whole plane: `ζ · L(χ₄)`. -/
noncomputable def angularL0 (s : ℂ) : ℂ := riemannZeta s * DirichletCharacter.LFunction χ4C s

/-- The radial coefficient is the divisor sum `Σ_{d ∣ n} χ₄(d)`: Jacobi's two-square theorem. -/
theorem member_zero_coeff {n : ℕ} (hn : n ≠ 0) :
    angularCoeff 0 n = ∑ d ∈ n.divisors, ((ZMod.χ₄ d : ℤ) : ℂ) := by
  have h := two_sq_count n (Nat.pos_of_ne_zero hn)
  have hR : ((R n : ℤ) : ℂ) = 4 * ((f n : ℤ) : ℂ) := by rw [h]; push_cast; ring
  simp only [angularCoeff, mul_zero, pow_zero, div_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : ((shell n).card : ℂ) = ((R n : ℤ) : ℂ) := by simp [R]
  rw [hc, hR, f]
  push_cast
  ring

lemma coeff_eq_convolution {n : ℕ} (hn : n ≠ 0) :
    angularCoeff 0 n = ((fun m : ℕ => χ4C m) ⍟ (1 : ℕ → ℂ)) n := by
  rw [member_zero_coeff hn, LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => χ4C a)]
  simp [χ4C_apply]

/-- **The radial member is `ζ · L(χ₄)`** on `Re s > 1`. -/
theorem member_zero_eq {s : ℂ} (hs : 1 < s.re) : angularL 0 s = angularL0 s := by
  have hχ := DirichletCharacter.LSeriesSummable_of_one_lt_re χ4C hs
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  unfold angularL angularL0
  rw [LSeries_congr (fun {n} hn => coeff_eq_convolution hn) s, LSeries_convolution' hχ h1,
    DirichletCharacter.LFunction_eq_LSeries χ4C hs, LSeries_one_eq_riemannZeta hs, mul_comm]

/-- `ζ` does not vanish at the negative odd integers (functional equation at `s = 2n + 2`). -/
theorem zeta_neg_odd_ne_zero (n : ℕ) : riemannZeta (-(2 * n + 1)) ≠ 0 := by
  set s : ℂ := 2 * n + 2
  have hs : ∀ m : ℕ, s ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp [s] at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs1 : s ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp [s] at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have e : (1 : ℂ) - s = -(2 * n + 1) := by simp [s]; ring
  rw [← e, riemannZeta_one_sub hs hs1]
  have hre : 1 < s.re := by simp [s]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_)
    (riemannZeta_ne_zero_of_one_lt_re hre)
  · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; have := congrArg Complex.re h; simp [s] at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])).mpr (by
        exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact Complex.Gamma_ne_zero hs
  · have : (Real.pi : ℂ) * s / 2 = ((n + 1 : ℕ) : ℂ) * (Real.pi : ℂ) := by simp [s]; ring
    rw [this]
    have hc : Real.cos ((((n + 1 : ℕ) : ℤ) : ℝ) * Real.pi) ≠ 0 := by
      rw [Real.cos_int_mul_pi]; exact zpow_ne_zero _ (by norm_num)
    have e2 : Complex.cos (((n + 1 : ℕ) : ℂ) * (Real.pi : ℂ)) =
        ((Real.cos ((((n + 1 : ℕ) : ℤ) : ℝ) * Real.pi) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos]; push_cast; ring_nf
    rw [e2]; exact_mod_cast hc

/-- The grand-RH statement for the radial member: its zeros, apart from the negative integers and
`s = 1`, lie on `Re s = ½`. -/
def GRHMemberZero : Prop :=
  ∀ s : ℂ, angularL0 s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → (¬∃ n : ℕ, s = -(2 * n + 1)) →
    s ≠ 1 → s.re = 1 / 2

/-- **RH is in the family:** the radial member's grand-RH implies the Riemann hypothesis. -/
theorem rh_of_member_zero (h : GRHMemberZero) : RiemannHypothesis := by
  intro s hz htriv h1
  refine h s (by simp [angularL0, hz]) htriv ?_ h1
  rintro ⟨n, rfl⟩
  exact zeta_neg_odd_ne_zero n hz

end AngularFamily
