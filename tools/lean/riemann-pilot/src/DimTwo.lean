import Mathlib
import StructureD

/-! # Ground spaces of dimension at most two have all zeros on the cross

If `dim V ≤ 2`, every nonzero ground-space element `v` has `v̂` vanishing only on `ℝ ∪ iℝ`.

Proof: an off-cross zero `ω` of `v̂` puts both parts of `(∂² + ω²)⁻¹v` in `V` (round 48's Theorem A).
By the spanning half of Theorem D, all three transforms are polynomials of degree `< m` in
`q = −1/(t² + ¼)` times `ŵ`. Comparing gives `P(X)(1 + βX) = X·P_v(X)` with `β = ¼ + ω²` and `P_v`
real. For `m ≤ 2` the coefficients force `β = b/a` real, so `ω²` is real.

Consequence: RH follows from (a) for **any** family of ground states whose ground spaces eventually
have dimension at most two. Eventual simplicity (`m = 1`) is not needed.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

theorem polyOf_coeff_im {k : ℕ} (c : Fin k → ℝ) (j : ℕ) :
    ((polyOf fun i => (c i : ℂ)).coeff j).im = 0 := by
  rw [polyOf, Polynomial.finsetSum_coeff, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp

/-- **Dimension at most two ⇒ zeros on the cross.** -/
theorem zeros_cross_of_dim_le_two {a : ℝ} (ha : 0 < a) (hm : gdim a ≤ 2) {v : ℝ → ℝ}
    (hv : v ∈ groundSpace a) (hpos : 0 < normSq v) {ω : ℂ} (hω : ghatC v a ω = 0) :
    (ω ^ 2).im = 0 := by
  by_contra hσ
  obtain ⟨w, hc, hwpos⟩ := exists_long_chain ha
  set n := gdim a - 1
  have hn : n + 1 ≤ 2 := by omega
  have hω0 : ω ≠ 0 := by rintro rfl; apply hσ; simp
  obtain ⟨hu, hv'⟩ := green_mem_groundSpace ha hv hω hσ
  obtain ⟨c, hcu⟩ := chain_span_hat ha hc hwpos hu
  obtain ⟨d, hdv⟩ := chain_span_hat ha hc hwpos hv'
  obtain ⟨ev, hev⟩ := chain_span_hat ha hc hwpos hv
  have hw : Probe a w := (hc.1 0 (Nat.zero_le _)).1
  obtain ⟨α, ε, hα, hε, hne⟩ := exists_interval_ghat ha hw hwpos
  have hcont := hSw_continuous hv.1.memL2 a ω
  set P := polyOf (fun i : Fin (n + 1) => (c i : ℂ) + Complex.I * d i)
  set Pv := polyOf (fun i : Fin (n + 1) => (ev i : ℂ))
  set β : ℂ := 1 / 4 + ω ^ 2
  have hR : P * (1 + Polynomial.C β * Polynomial.X) - Polynomial.X * Pv = 0 := by
    refine poly_eq_zero_of_interval _ hα hε fun t ht => ?_
    obtain ⟨Q, hQe⟩ : ∃ Q : ℂ, Q = ((qr t : ℝ) : ℂ) := ⟨_, rfl⟩
    rw [← hQe]
    set D : ℂ := (t : ℂ) ^ 2 + 1 / 4
    have hD : D ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
      have : ((t ^ 2 + 1 / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      simpa [D] using this
    have hQ : Q = -1 / D := by rw [hQe]; simp only [D, qr]; push_cast; ring
    have hz : ((t : ℂ)) ^ 2 ≠ ω ^ 2 := by
      intro e; apply hσ; rw [← e]; norm_cast
    have hden : (t : ℂ) ^ 2 - ω ^ 2 ≠ 0 := sub_ne_zero.2 hz
    have hsplit : (∫ x in (-a)..a, hSw v a ω x * Complex.exp (Complex.I * t * x))
        = ghatC (fun x => (hSw v a ω x).re) a t + Complex.I * ghatC (fun x => (hSw v a ω x).im) a t := by
      have ci : ∀ F : ℝ → ℝ, Continuous F →
          IntervalIntegrable (fun x => ((F x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x)) volume (-a) a :=
        fun F hF => ((continuous_ofReal.comp hF).mul (by fun_prop)).intervalIntegrable _ _
      unfold ghatC
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (ci (fun x => (hSw v a ω x).re) (Complex.continuous_re.comp hcont))
        ((ci (fun x => (hSw v a ω x).im) (Complex.continuous_im.comp hcont)).const_mul _)]
      congr 1; funext x
      conv_lhs => rw [← Complex.re_add_im (hSw v a ω x)]
      ring
    have hhat := hSw_hat' hv.1 ha.le hω hω0 hz
    rw [hsplit, hcu t, hdv t, hev t, ← hQe] at hhat
    have hwt := hne t ht
    have hP : P.eval Q = (∑ i : Fin (n + 1), (c i : ℂ) * Q ^ (i : ℕ))
        + Complex.I * ∑ i : Fin (n + 1), (d i : ℂ) * Q ^ (i : ℕ) := by
      rw [polyOf_eval, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    have hPv : Pv.eval Q = ∑ i : Fin (n + 1), (ev i : ℂ) * Q ^ (i : ℕ) := polyOf_eval _ _
    have e : P.eval Q * ((t : ℂ) ^ 2 - ω ^ 2) = -Pv.eval Q := by
      have h2 := congrArg (· * ((t : ℂ) ^ 2 - ω ^ 2)) hhat
      rw [neg_mul, div_mul_cancel₀ _ hden] at h2
      have h3 : (P.eval Q * ((t : ℂ) ^ 2 - ω ^ 2) + Pv.eval Q) * ghatC w a t = 0 := by
        rw [hP, hPv]; linear_combination h2
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 h3).resolve_right hwt)
    have h1 : 1 + β * Q = ((t : ℂ) ^ 2 - ω ^ 2) * (-Q) := by
      have hDi : ((t : ℂ) ^ 2 + 1 / 4) * ((t : ℂ) ^ 2 + 1 / 4)⁻¹ = 1 := mul_inv_cancel₀ hD
      rw [hQ, div_eq_mul_inv]; simp only [β, D]
      linear_combination -hDi
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [h1]
    linear_combination (-Q) * e
  -- coefficients
  have hE : P + Polynomial.C β * (P * Polynomial.X) = Polynomial.X * Pv := by
    rw [← sub_eq_zero, ← hR]; ring
  have k0 := congrArg (fun p => Polynomial.coeff p 0) hE
  have k1 := congrArg (fun p => Polynomial.coeff p 1) hE
  have k2 := congrArg (fun p => Polynomial.coeff p 2) hE
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_zero,
    Polynomial.coeff_X_mul_zero, mul_zero, add_zero] at k0
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X,
    Polynomial.coeff_X_mul] at k1 k2
  have hP2 : P.coeff 2 = 0 := polyOf_coeff_ge _ hn
  rw [k0, mul_zero, add_zero] at k1
  rw [hP2, zero_add, k1] at k2
  -- `β · a = b` with `a, b` real
  set A := Pv.coeff 0
  set B := Pv.coeff 1
  have hA : A.im = 0 := polyOf_coeff_im ev 0
  have hB : B.im = 0 := polyOf_coeff_im ev 1
  have hβ : β.im = (ω ^ 2).im := by simp [β]
  by_cases hA0 : A = 0
  · -- then `P_v = 0`, so `v̂ ≡ 0` on the real line
    have hB0 : B = 0 := by rw [← k2, hA0, mul_zero]
    have hPv0 : Pv = 0 := by
      ext k
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k
        · exact hA0
        · exact hB0
      · rw [Polynomial.coeff_zero]; exact polyOf_coeff_ge _ (le_trans hn hk)
    obtain ⟨α', ε', _, hε', hne'⟩ := exists_interval_ghat ha hv.1 hpos
    set t := α' + ε' / 2
    have ht : t ∈ Ioo α' (α' + ε') := ⟨by simp only [t]; linarith, by simp only [t]; linarith⟩
    apply hne' t ht
    have h0 : polyOf (fun i : Fin (n + 1) => (ev i : ℂ)) = 0 := hPv0
    rw [hev t, ← polyOf_eval, h0, Polynomial.eval_zero, zero_mul]
  · have : β = B / A := by rw [← k2]; field_simp
    have him : (B / A).im = 0 := by rw [Complex.div_im, hA, hB]; simp
    exact hσ (by rw [← hβ, this, him])

/-- A simple ground state has a one-dimensional ground space. -/
theorem gdim_le_one_of_simple {a : ℝ} {g : ℝ → ℝ} (ha : 0 < a) (hs : SimpleGround a g) :
    gdim a ≤ 1 := by
  have hgV : g ∈ groundSpace a := ((isGroundState_iff ha).1 hs.1).1
  set y := iotaGS a ⟨g, hgV⟩
  have hle : LinearMap.range (iotaGS a) ≤ Submodule.span ℝ {y} := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := hs.2 x.1 x.2
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    show c • hgV.1.memL2.toLp g = x.2.1.memL2.toLp x.1
    rw [← MemLp.toLp_const_smul]
    have h1 : (c • g) =ᵐ[volume] (fun t => c * g t) := Eventually.of_forall fun t => rfl
    exact MemLp.toLp_congr _ _ (EventuallyEq.trans h1 hc.symm)
  unfold gdim
  exact (Submodule.finrank_mono hle).trans ((finrank_span_le_card _).trans (by simp))

/-- **RH from (a) for any ground states with eventually `dim V ≤ 2`.** -/
theorem rh_of_dim_le_two {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ 2)
    (hconv : HypConv a g) : RiemannHypothesis := by
  refine rh_of_prime_side_cross hgs ?_ hconv zetaNoZeroInUnitInterval
  filter_upwards [hdim] with n hn z hz
  obtain ⟨hV, hN⟩ := (isGroundState_iff (ha n)).1 (hgs n)
  have him := zeros_cross_of_dim_le_two (ha n) hn hV (by rw [hN]; norm_num) hz
  have : 2 * z.re * z.im = 0 := by rw [← him]; simp [pow_two]; ring
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; exact h

/-- The simple case is the special case `m = 1`. -/
theorem rh_of_eventually_simple' {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hsimple : ∀ᶠ n in atTop, SimpleGround (a n) (g n))
    (hconv : HypConv a g) : RiemannHypothesis :=
  rh_of_dim_le_two ha hgs (hsimple.mono fun n hs => (gdim_le_one_of_simple (ha n) hs).trans (by norm_num))
    hconv

end Pilot1ca

#print axioms Pilot1ca.zeros_cross_of_dim_le_two
#print axioms Pilot1ca.gdim_le_one_of_simple
#print axioms Pilot1ca.rh_of_dim_le_two
#print axioms Pilot1ca.rh_of_eventually_simple'
