import Mathlib
import XiBounds

/-! # Dodging D, and the curvature sum rule

* **Dodging D alone gives RH (`rh_of_dodging`, `rh_of_dodging_final`).** The paper's census finds D
  only "to the dodging tolerance, not exactly" (Theorem 1bu(ii)): every zero of `Ξ` below `T_D(n)` is
  matched with its own zero of `ĝ_n`, with total displacement `Σ|τ⁻² − γ⁻²| ≤ η_n → 0`. If `ĝ_n` is
  real-rooted, each of its parameters `τ⁻²` is a non-negative real (`HadamardW.nonneg_real`), so each
  `γ_j⁻²`, being eventually matched within `η_n`, is one too, and every zero of `Ξ` is real
  (`rh_of_Xi_params`). Nothing about `ĝ_n`'s unmatched zeros, and no convergence `ĝ_n → Ξ`, is used.
* **The curvature sum rule.** For a real-rooted `ĝ` of an even integrable `g`,
  `Σ_τ τ⁻² = ∫u²g / (2∫g)` (`ghat_sum_rule`, `ghat_curvature`). Round 10 used it as a hypothesis on
  the chain (the curvature of the ground states converging to `Ξ`'s); round 66 shows the chain does
  not need it.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## A. Dodging D alone gives RH -/

/-- A product with a zero factor is zero. -/
theorem hasProd_eq_zero_of_eq_zero {ι : Type*} {f : ι → ℂ} {p : ℂ} (h : HasProd f p) {i : ι}
    (hi : f i = 0) : p = 0 := by
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop {i}] with s hs
  exact (Finset.prod_eq_zero (Finset.singleton_subset_iff.1 hs) hi).symm

/-- **Real roots give real parameters.** If every zero of `f` is real, every parameter `w_i` of a
factorisation `f(z)/f(0) = ∏(1 − z²w_i)` is a non-negative real: `w_i ≠ 0` puts a zero at
`z = w_i^{−1/2}`. -/
theorem HadamardW.nonneg_real {ι : Type*} {f : ℂ → ℂ} {w : ι → ℂ} (h : HadamardW f w)
    (hRR : ∀ z, f z = 0 → z.im = 0) (i : ι) : (w i).im = 0 ∧ 0 ≤ (w i).re := by
  by_cases hw : w i = 0
  · simp [hw]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w i)⁻¹ two_pos
  have hfz : f z = 0 := by
    have h0 := hasProd_eq_zero_of_eq_zero (h.prod z) (i := i) (by rw [hz, inv_mul_cancel₀ hw, sub_self])
    exact (div_eq_zero_iff.1 h0).resolve_right h.f0
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = x := ⟨z.re, Complex.ext rfl (by simp [hRR z hfz])⟩
  have hwx : w i = ((x ^ 2)⁻¹ : ℝ) := by
    rw [← inv_inv (w i), ← hz]; push_cast; rfl
  rw [hwx, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, by positivity⟩

/-- **RH from real parameters.** If every parameter of a factorisation of `Ξ` is a non-negative
real, every zero of `Ξ` is real: the product converges absolutely, so it vanishes only at a vanishing
factor, and `z²v_j = 1` with `v_j > 0` forces `z` real. -/
theorem rh_of_Xi_params {κ : Type*} {v : κ → ℂ} (hX : HadamardW Xi v)
    (hv : ∀ j, (v j).im = 0 ∧ 0 ≤ (v j).re) : RiemannHypothesis := by
  have hreal : ∀ z, Xi z = 0 → z.im = 0 := by
    intro z hz
    by_contra him
    have hne : ∀ j, 1 + -(z ^ 2 * v j) ≠ 0 := by
      intro j hj
      have h1 : z ^ 2 * v j = 1 := by linear_combination -hj
      have hvr : v j = ((v j).re : ℂ) := Complex.ext rfl (by simp [(hv j).1])
      rw [hvr] at h1
      have hre := congrArg Complex.re h1
      have him' := congrArg Complex.im h1
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, mul_zero, sub_zero] at hre him'
      have hr : (v j).re ≠ 0 := fun h => by rw [h, mul_zero] at hre; exact zero_ne_one hre
      have hzre : z.re = 0 := by
        have : (z.re * z.im) * (2 * (v j).re) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact (mul_eq_zero.1 h).resolve_right him
        · exact absurd (by linarith : (v j).re = 0) hr
      rw [hzre] at hre
      nlinarith [sq_nonneg z.im, (hv j).2]
    have := tprod_one_add_ne_zero_of_summable hne (summable_scaled hX.summ z)
    rw [← hX.eq_tprod z, hz, zero_div] at this
    exact this rfl
  intro s hs htriv _
  apply re_eq_half_of_Xi_real
  apply hreal
  rw [Xi_at_ordinate, xi_eq_zero_of_nontrivial ⟨hs, htriv⟩]

/-- **Dodging D and real-rootedness alone give RH.** No curvature condition and no convergence
`ĝ_n → Ξ`: each parameter `v_j = γ_j⁻²` of `Ξ` is eventually matched, within `η_n → 0`, to a
parameter of a real-rooted `ĝ_n`, which is a non-negative real, so `v_j` is one too. -/
theorem rh_of_dodging {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW Xi v)
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ι n → Prop) (e : {i // p i} ≃ {j // t n < ‖v j‖}),
      (∑' i : {i // p i}, ‖w n i - v (e i)‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0)) :
    RiemannHypothesis := by
  refine rh_of_Xi_params hX fun j => ?_
  by_cases hj : v j = 0
  · simp [hj]
  set C : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}
  have hC : IsClosed C := (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)
  have hev : ∀ᶠ n in atTop, ∃ x ∈ C, dist (v j) x ≤ η n := by
    filter_upwards [ht.eventually (gt_mem_nhds (norm_pos_iff.2 hj))] with n hn
    obtain ⟨p, e, he⟩ := hD n
    set i := e.symm ⟨j, hn⟩
    have hei : (e i : κ) = j := by simp [i]
    have hs : Summable fun i : {i // p i} => ‖w n i - v (e i)‖ := by
      have h2 : Summable fun i : {i // p i} => ‖v (e i)‖ :=
        (e.summable_iff (f := fun j : {j // t n < ‖v j‖} => ‖v j‖)).2 (hX.summ.subtype _)
      exact (((hF n).summ.subtype _).add h2).of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun _ => norm_sub_le _ _)
    refine ⟨w n i, (hF n).nonneg_real (hRR n) i, ?_⟩
    rw [dist_eq_norm, norm_sub_rev, ← hei]
    exact (hs.le_tsum i fun _ _ => norm_nonneg _).trans he
  have hmem : v j ∈ closure C := Metric.mem_closure_iff.2 fun ε hε => by
    obtain ⟨n, ⟨x, hx, hd⟩, hn⟩ := (hev.and (hη.eventually (gt_mem_nhds hε))).exists
    exact ⟨x, hx, hd.trans_lt hn⟩
  rwa [hC.closure_eq] at hmem

/-! ## B. The curvature sum rule -/

theorem norm_prod_one_add_sub_one_le {ι : Type*} (t : Finset ι) (x : ι → ℂ) :
    ‖∏ i ∈ t, (1 + x i) - 1‖ ≤ ∏ i ∈ t, (1 + ‖x i‖) - 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj IH =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    set P := ∏ i ∈ t, (1 + x i)
    set Q := ∏ i ∈ t, (1 + ‖x i‖)
    have hP : ‖P‖ ≤ Q := by
      refine (Finset.norm_prod_le _ _).trans
        (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_)
      simpa using norm_add_le (1 : ℂ) (x i)
    have e : (1 + x j) * P - 1 = (P - 1) + x j * P := by ring
    rw [e]
    calc ‖(P - 1) + x j * P‖ ≤ ‖P - 1‖ + ‖x j‖ * ‖P‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (Q - 1) + ‖x j‖ * Q := by gcongr
      _ = (1 + ‖x j‖) * Q - 1 := by ring

/-- `‖Π(1 + x_i) − 1 − Σx_i‖ ≤ Π(1 + ‖x_i‖) − 1 − Σ‖x_i‖` over a finite set. -/
theorem norm_prod_one_add_sub_sum_le {ι : Type*} (t : Finset ι) (x : ι → ℂ) :
    ‖∏ i ∈ t, (1 + x i) - 1 - ∑ i ∈ t, x i‖ ≤ ∏ i ∈ t, (1 + ‖x i‖) - 1 - ∑ i ∈ t, ‖x i‖ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj IH =>
    have h1 := norm_prod_one_add_sub_one_le t x
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    set P := ∏ i ∈ t, (1 + x i)
    set Q := ∏ i ∈ t, (1 + ‖x i‖)
    set S := ∑ i ∈ t, x i
    set T := ∑ i ∈ t, ‖x i‖
    have e : (1 + x j) * P - 1 - (x j + S) = (P - 1 - S) + x j * (P - 1) := by ring
    rw [e]
    calc ‖(P - 1 - S) + x j * (P - 1)‖ ≤ ‖P - 1 - S‖ + ‖x j‖ * ‖P - 1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (Q - 1 - T) + ‖x j‖ * (Q - 1) := by gcongr
      _ = (1 + ‖x j‖) * Q - 1 - (‖x j‖ + T) := by ring

theorem prod_one_add_norm_le_exp {ι : Type*} (t : Finset ι) (x : ι → ℂ) :
    ∏ i ∈ t, (1 + ‖x i‖) ≤ Real.exp (∑ i ∈ t, ‖x i‖) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ => by positivity)
    fun i _ => by linarith [Real.add_one_le_exp ‖x i‖]

theorem exp_sub_one_sub_mono {s S : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) :
    Real.exp s - 1 - s ≤ Real.exp S - 1 - S := by
  have h1 : Real.exp S = Real.exp s * Real.exp (S - s) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.add_one_le_exp (S - s)
  have h3 : 1 ≤ Real.exp s := Real.one_le_exp hs
  nlinarith [mul_nonneg (Real.exp_pos s).le (show 0 ≤ Real.exp (S - s) - (S - s + 1) by linarith),
    mul_nonneg (show 0 ≤ Real.exp s - 1 by linarith) (show 0 ≤ S - s by linarith)]

/-- **`‖Π'(1 + x_i) − 1 − Σ'x_i‖ ≤ e^S − 1 − S`**, `S = Σ'‖x_i‖`. -/
theorem norm_tprod_one_add_sub_tsum_le {ι : Type*} {x : ι → ℂ} (hx : Summable fun i => ‖x i‖) :
    ‖(∏' i, (1 + x i)) - 1 - ∑' i, x i‖ ≤ Real.exp (∑' i, ‖x i‖) - 1 - ∑' i, ‖x i‖ := by
  have hpx := (multipliable_one_add_of_summable hx).hasProd
  have hsx := hx.of_norm.hasSum
  have ht : Tendsto (fun t : Finset ι => ‖∏ i ∈ t, (1 + x i) - 1 - ∑ i ∈ t, x i‖) atTop
      (𝓝 ‖(∏' i, (1 + x i)) - 1 - ∑' i, x i‖) :=
    ((hpx.sub tendsto_const_nhds).sub hsx).norm
  refine le_of_tendsto' ht fun t => (norm_prod_one_add_sub_sum_le t x).trans ?_
  have hs0 : 0 ≤ ∑ i ∈ t, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsS : ∑ i ∈ t, ‖x i‖ ≤ ∑' i, ‖x i‖ := hx.sum_le_tsum t fun i _ => norm_nonneg _
  linarith [prod_one_add_norm_le_exp t x, exp_sub_one_sub_mono hs0 hsS]

/-- **The second-order expansion of a Hadamard product**: `f(z)/f(0) = 1 − z²Σw + O(‖z‖⁴)`,
explicitly `≤ (‖z‖²Σ‖w‖)²` once `‖z‖²Σ‖w‖ ≤ 1`. -/
theorem HadamardW.expansion {ι : Type*} {f : ℂ → ℂ} {w : ι → ℂ} (h : HadamardW f w) (z : ℂ)
    (hz : ‖z‖ ^ 2 * ∑' i, ‖w i‖ ≤ 1) :
    ‖f z / f 0 - (1 - z ^ 2 * ∑' i, w i)‖ ≤ (‖z‖ ^ 2 * ∑' i, ‖w i‖) ^ 2 := by
  have hs := summable_scaled h.summ z
  have e1 : (∑' i, ‖-(z ^ 2 * w i)‖) = ‖z‖ ^ 2 * ∑' i, ‖w i‖ := by
    rw [← tsum_mul_left]; congr 1; funext i; simp [norm_pow]
  have e2 : (∑' i, -(z ^ 2 * w i)) = -(z ^ 2 * ∑' i, w i) := by
    rw [tsum_neg, tsum_mul_left]
  have key := norm_tprod_one_add_sub_tsum_le hs
  rw [e1, e2] at key
  rw [h.eq_tprod]
  have hS0 : 0 ≤ ‖z‖ ^ 2 * ∑' i, ‖w i‖ :=
    mul_nonneg (by positivity) (tsum_nonneg fun _ => norm_nonneg _)
  have hexp := Real.abs_exp_sub_one_sub_id_le (x := ‖z‖ ^ 2 * ∑' i, ‖w i‖)
    (by rw [abs_of_nonneg hS0]; exact hz)
  have e3 : (∏' i, (1 + -(z ^ 2 * w i))) - (1 - z ^ 2 * ∑' i, w i)
      = (∏' i, (1 + -(z ^ 2 * w i))) - 1 - -(z ^ 2 * ∑' i, w i) := by ring
  rw [e3]
  exact key.trans ((le_abs_self _).trans hexp)

theorem ghatC_zero (g : ℝ → ℝ) (a : ℝ) : ghatC g a 0 = ((∫ u in (-a)..a, g u : ℝ) : ℂ) := by
  unfold ghatC
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  exact intervalIntegral.integral_ofReal

/-- The odd moment of an even function vanishes. -/
theorem integral_mul_even_eq_zero {g : ℝ → ℝ} (heven : ∀ u, g (-u) = g u) (a : ℝ) :
    ∫ u in (-a)..a, u * g u = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) (f := fun u => u * g u)
  simp only [neg_neg, heven, neg_mul, intervalIntegral.integral_neg] at h
  linarith

theorem sum_range_three (y : ℂ) :
    ∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℂ) = 1 + y + y ^ 2 / 2 := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- **The second-order expansion of `ĝ`**: for even integrable `g` on `[−a, a]` and real `x` with
`|x|a ≤ 1`, `‖ĝ(x) − ∫g + (x²/2)∫u²g‖ ≤ |x|³a³∫|g|`. -/
theorem ghat_expansion {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (x : ℝ) (hx : |x| * a ≤ 1) :
    ‖ghatC g a x - ((∫ u in (-a)..a, g u : ℝ) : ℂ)
        + ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ)‖
      ≤ |x| ^ 3 * a ^ 3 * ∫ u in (-a)..a, |g u| := by
  have hle : -a ≤ a := by linarith
  have hgC : IntervalIntegrable (fun u => ((g u : ℝ) : ℂ)) volume (-a) a :=
    ⟨hg.1.ofReal, hg.2.ofReal⟩
  set R : ℝ → ℂ := fun u => Complex.exp (I * x * u) - (1 + I * x * u + (I * x * u) ^ 2 / 2)
    with hR
  have hRc : Continuous R := by simp only [hR]; fun_prop
  have hRi : IntervalIntegrable (fun u => ((g u : ℝ) : ℂ) * R u) volume (-a) a :=
    hgC.mul_continuousOn hRc.continuousOn
  have hr1 : IntervalIntegrable (fun u => u * g u) volume (-a) a :=
    hg.continuousOn_mul continuousOn_id
  have hr2 : IntervalIntegrable (fun u => u ^ 2 * g u) volume (-a) a :=
    hg.continuousOn_mul (continuous_pow 2).continuousOn
  have hc1 : IntervalIntegrable (fun u => ((u * g u : ℝ) : ℂ)) volume (-a) a :=
    ⟨hr1.1.ofReal, hr1.2.ofReal⟩
  have hc2 : IntervalIntegrable (fun u => ((u ^ 2 * g u : ℝ) : ℂ)) volume (-a) a :=
    ⟨hr2.1.ofReal, hr2.2.ofReal⟩
  have hfun : (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (I * x * u))
      = fun u => (((g u : ℝ) : ℂ) * R u + ((g u : ℝ) : ℂ))
          + ((I * x) * ((u * g u : ℝ) : ℂ) - ((x : ℂ) ^ 2 / 2) * ((u ^ 2 * g u : ℝ) : ℂ)) := by
    funext u
    simp only [hR]
    push_cast
    linear_combination ((g u : ℂ) * (x : ℂ) ^ 2 * (u : ℂ) ^ 2 / 2) * I_sq
  have hI : ghatC g a x = (∫ u in (-a)..a, ((g u : ℝ) : ℂ) * R u)
      + ((∫ u in (-a)..a, g u : ℝ) : ℂ)
      + ((I * x) * ((∫ u in (-a)..a, u * g u : ℝ) : ℂ)
        - ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ)) := by
    unfold ghatC
    rw [hfun, intervalIntegral.integral_add (hRi.add hgC) ((hc1.const_mul _).sub (hc2.const_mul _)),
      intervalIntegral.integral_add hRi hgC,
      intervalIntegral.integral_sub (hc1.const_mul _) (hc2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  rw [hI, integral_mul_even_eq_zero heven]
  have e : (∫ u in (-a)..a, ((g u : ℝ) : ℂ) * R u) + ((∫ u in (-a)..a, g u : ℝ) : ℂ)
      + ((I * x) * (((0 : ℝ)) : ℂ) - ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ))
      - ((∫ u in (-a)..a, g u : ℝ) : ℂ)
      + ((x : ℂ) ^ 2 / 2) * ((∫ u in (-a)..a, u ^ 2 * g u : ℝ) : ℂ)
      = ∫ u in (-a)..a, ((g u : ℝ) : ℂ) * R u := by push_cast; ring
  rw [e]
  have hb : IntervalIntegrable (fun u => |g u| * (|x| ^ 3 * a ^ 3)) volume (-a) a :=
    hg.abs.mul_const _
  refine (intervalIntegral.norm_integral_le_of_norm_le hle
    (Eventually.of_forall fun u hu => ?_) hb).trans ?_
  · have hua : |u| ≤ a := abs_le.2 ⟨hu.1.le, hu.2⟩
    have hy : ‖I * (x : ℂ) * (u : ℂ)‖ = |x| * |u| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    have hxu : |x| * |u| ≤ |x| * a := mul_le_mul_of_nonneg_left hua (abs_nonneg x)
    have hy1 : ‖I * (x : ℂ) * (u : ℂ)‖ ≤ 1 := by rw [hy]; linarith
    have hexp := Complex.exp_bound hy1 (n := 3) (by norm_num)
    rw [sum_range_three] at hexp
    have hc : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      norm_num [Nat.factorial]
    have hRu : ‖R u‖ ≤ |x| ^ 3 * a ^ 3 := by
      calc ‖R u‖ ≤ ‖I * (x : ℂ) * (u : ℂ)‖ ^ 3 * (((Nat.succ 3 : ℕ) : ℝ)
            * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹) := hexp
        _ ≤ ‖I * (x : ℂ) * (u : ℂ)‖ ^ 3 * 1 := by gcongr
        _ ≤ (|x| * a) ^ 3 := by
            rw [mul_one, hy]
            exact pow_le_pow_left₀ (by positivity) hxu 3
        _ = |x| ^ 3 * a ^ 3 := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hRu (abs_nonneg _)
  · rw [intervalIntegral.integral_mul_const]
    apply le_of_eq; ring

/-- For a real-rooted `ĝ`, the zeros of `sqF ĝ` are positive reals: `u⁻¹ = ‖u⁻¹‖`. -/
theorem inv_zero_eq_norm {g : ℝ → ℝ} {a : ℝ} (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (h0 : ghatC g a 0 ≠ 0) (hRR : RealRooted a g)
    (i : ZeroIdx (sqF (ghatC g a))) : (i.1⁻¹ : ℂ) = ((‖i.1⁻¹‖ : ℝ) : ℂ) := by
  have hF := sqF_differentiable (ghatC_differentiable hg) (fun z => ghatC_even heven a z)
  have hF0 : sqF (ghatC g a) 0 ≠ 0 := by rwa [sqF_zero]
  have hz : sqF (ghatC g a) i.1 = 0 :=
    (ordN_ne_zero_iff hF hF0 i.1).1 (Nat.pos_iff_ne_zero.1 i.2.pos)
  have him : (i.1 ^ ((2 : ℂ)⁻¹)).im = 0 := hRR _ hz
  obtain ⟨s, hs⟩ : ∃ s : ℝ, i.1 ^ ((2 : ℂ)⁻¹) = s :=
    ⟨(i.1 ^ ((2 : ℂ)⁻¹)).re, Complex.ext (by simp) (by simp [him])⟩
  have hu : i.1 = ((s ^ 2 : ℝ) : ℂ) := by
    rw [← sqrt_sq' i.1, hs]; push_cast; ring
  rw [hu, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (sq_nonneg s))]

/-- **The curvature sum rule**: for even integrable `g` with `∫g ≠ 0`,
`Σ_τ τ⁻² = ∫u²g / (2∫g)`, the sum over the zero pairs of `ĝ` taken in `w = τ⁻²` (in general complex;
see `ghat_curvature` for the real-rooted case). -/
theorem ghat_sum_rule {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (h0 : ghatC g a 0 ≠ 0) :
    ∑' i : ZeroIdx (sqF (ghatC g a)), i.1⁻¹
      = (((∫ u in (-a)..a, u ^ 2 * g u) / (2 * ∫ u in (-a)..a, g u) : ℝ) : ℂ) := by
  have hH := hadamardW_ghat ha hg heven h0
  set W := ∑' i : ZeroIdx (sqF (ghatC g a)), ‖i.1⁻¹‖ with hW
  set Sw := ∑' i : ZeroIdx (sqF (ghatC g a)), i.1⁻¹ with hSw
  set G0 := ∫ u in (-a)..a, g u with hG0d
  set G2 := ∫ u in (-a)..a, u ^ 2 * g u with hG2d
  set A := ∫ u in (-a)..a, |g u| with hAd
  have hg0 : ghatC g a 0 = (G0 : ℂ) := ghatC_zero g a
  have hG0 : (G0 : ℂ) ≠ 0 := hg0 ▸ h0
  have hG0' : G0 ≠ 0 := by exact_mod_cast hG0
  set κ : ℂ := ((G2 / (2 * G0) : ℝ) : ℂ) with hκ
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _
  set M := a ^ 3 * A / |G0| with hM
  have hM0 : 0 ≤ M := by positivity
  set x0 := 1 / (W + a + 1) with hx0d
  have hx0 : 0 < x0 := by positivity
  have hbound : ∀ x : ℝ, 0 < x → x ≤ x0 → ‖Sw - κ‖ ≤ x * (W ^ 2 + M) := by
    intro x hx hxx0
    have hsum1 : x * (W + a + 1) ≤ 1 := by
      calc x * (W + a + 1) ≤ x0 * (W + a + 1) := by gcongr
        _ = 1 := by rw [hx0d]; field_simp
    have hxW : x * W ≤ 1 := by nlinarith
    have hxa : x * a ≤ 1 := by nlinarith
    have hx1 : x ≤ 1 := by nlinarith
    have hz : ‖(x : ℂ)‖ ^ 2 * W ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; nlinarith
    have e1 := hH.expansion (x : ℂ) hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at e1
    have e2 := ghat_expansion ha hg heven x (by rw [abs_of_pos hx]; exact hxa)
    rw [abs_of_pos hx] at e2
    have e3 : ‖ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * κ)‖ ≤ x ^ 3 * M := by
      have : ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * κ)
          = (ghatC g a x - (G0 : ℂ) + ((x : ℂ) ^ 2 / 2) * (G2 : ℂ)) / (G0 : ℂ) := by
        rw [hg0, hκ]; push_cast; field_simp; ring
      rw [this, norm_div, Complex.norm_real, Real.norm_eq_abs,
        div_le_iff₀ (abs_pos.2 hG0')]
      calc _ ≤ x ^ 3 * a ^ 3 * A := e2
        _ = x ^ 3 * M * |G0| := by rw [hM]; field_simp
    have e4 : ‖(x : ℂ) ^ 2 * (Sw - κ)‖ ≤ (x ^ 2 * W) ^ 2 + x ^ 3 * M := by
      have : (x : ℂ) ^ 2 * (Sw - κ)
          = (ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * Sw))
            - (ghatC g a x / ghatC g a 0 - (1 - (x : ℂ) ^ 2 * κ)) := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at e4
    have hx2 : 0 < x ^ 2 := by positivity
    have hd : ‖Sw - κ‖ ≤ x ^ 2 * W ^ 2 + x * M := by
      refine le_of_mul_le_mul_left ?_ hx2
      calc x ^ 2 * ‖Sw - κ‖ ≤ (x ^ 2 * W) ^ 2 + x ^ 3 * M := e4
        _ = x ^ 2 * (x ^ 2 * W ^ 2 + x * M) := by ring
    have h1 : x ^ 2 * W ^ 2 ≤ x * W ^ 2 :=
      mul_le_mul_of_nonneg_right (show x ^ 2 ≤ x by nlinarith) (sq_nonneg W)
    have h2 : x * (W ^ 2 + M) = x * W ^ 2 + x * M := by ring
    linarith
  have hd0 : ‖Sw - κ‖ ≤ 0 := by
    have ht : Tendsto (fun x : ℝ => x * (W ^ 2 + M)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x * (W ^ 2 + M)) (𝓝 0) (𝓝 (0 * (W ^ 2 + M))) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hx0] with x hx
    exact hbound x hx.1 hx.2.le
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hd0)

/-- **The curvature sum rule, real-rooted**: `Σ_τ τ⁻² = ∫u²g / (2∫g)` as a sum of positive terms. -/
theorem ghat_curvature {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hg : IntervalIntegrable g volume (-a) a)
    (heven : ∀ u, g (-u) = g u) (h0 : ghatC g a 0 ≠ 0) (hRR : RealRooted a g) :
    ∑' i : ZeroIdx (sqF (ghatC g a)), ‖i.1⁻¹‖
      = (∫ u in (-a)..a, u ^ 2 * g u) / (2 * ∫ u in (-a)..a, g u) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, ← ghat_sum_rule ha hg heven h0]
  congr 1; funext i
  exact (inv_zero_eq_norm hg heven h0 hRR i).symm

/-- `Ξ`'s curvature: `Σ'_j v_j` is the `z²` coefficient of `Ξ(z)/Ξ(0)`
(numerically `−Ξ''(0)/(2Ξ(0)) = 0.023105`, Theorem 1bu(ii)). -/
theorem xi_expansion (z : ℂ)
    (hz : ‖z‖ ^ 2 * ∑' j : ZeroIdx (sqF Xi), ‖j.1⁻¹‖ ≤ 1) :
    ‖Xi z / Xi 0 - (1 - z ^ 2 * ∑' j : ZeroIdx (sqF Xi), j.1⁻¹)‖
      ≤ (‖z‖ ^ 2 * ∑' j : ZeroIdx (sqF Xi), ‖j.1⁻¹‖) ^ 2 :=
  (hadamardW_Xi xiGrowth Xi_zero_ne_zero).expansion z hz

/-! ## C. The chain for the explicit factorisations -/

/-- **Roadmap item 1 ⇒ `RiemannHypothesis`, with dodging D alone.**
For even integrable ground states `g_n` on `[−a_n, a_n]` with `∫g_n ≠ 0`:
* `ĝ_n` real-rooted (item 1(b));
* dodging D (item 1(a), to tolerance): below `T_D(n)` (`t n = T_D(n)⁻²`, `t → 0`), every zero of `Ξ`
  is matched with its own zero of `ĝ_n`, the matched `|τ⁻² − γ⁻²|` summing to `η_n → 0`.
Nothing about `ĝ_n`'s unmatched zeros, and no curvature condition, is assumed. -/
theorem rh_of_dodging_final {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (heven : ∀ n u, g n (-u) = g n u) (hg0 : ∀ n, (∫ u in (-(a n))..(a n), g n u) ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n))
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ZeroIdx (sqF (ghatC (g n) (a n))) → Prop)
      (e : {i // p i} ≃ {j : ZeroIdx (sqF Xi) // t n < ‖j.1⁻¹‖}),
      (∑' i : {i // p i}, ‖i.1.1⁻¹ - (e i).1.1⁻¹‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0)) :
    RiemannHypothesis := by
  have h0 : ∀ n, ghatC (g n) (a n) 0 ≠ 0 := fun n => by
    rw [ghatC_zero]; exact_mod_cast hg0 n
  exact rh_of_dodging hRR
    (w := fun n (i : ZeroIdx (sqF (ghatC (g n) (a n)))) => i.1⁻¹)
    (v := fun j : ZeroIdx (sqF Xi) => j.1⁻¹)
    (fun n => hadamardW_ghat (ha n) (hint n) (heven n) (h0 n))
    (hadamardW_Xi xiGrowth Xi_zero_ne_zero) hD hη ht

end Pilot1ca

#print axioms Pilot1ca.HadamardW.nonneg_real
#print axioms Pilot1ca.rh_of_Xi_params
#print axioms Pilot1ca.rh_of_dodging
#print axioms Pilot1ca.HadamardW.expansion
#print axioms Pilot1ca.ghat_expansion
#print axioms Pilot1ca.ghat_sum_rule
#print axioms Pilot1ca.ghat_curvature
#print axioms Pilot1ca.xi_expansion
#print axioms Pilot1ca.rh_of_dodging_final
