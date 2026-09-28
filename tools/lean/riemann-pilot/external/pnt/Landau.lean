/-
# Landau's lemma, general form (round 193): layer III of rung 3

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement.
* Hypothesis `PolylogGrowth a K`: `|ζ(σ+it)| ≤ K·(log|t|)^K` for `|t| ≥ 3` and
  `1 − (log|t|)^{−a} ≤ σ ≤ 2`. It says ζ grows at most like a power of `log t` in a thin
  strip reaching left of `Re s = 1`.
* `zeroFree_of_growth`: then ζ has no zeros in `σ ≥ 1 − A/(log|t|)^{n₁}`, for every `n₁ > a`.
* `logDerivBnd_of_growth` (for `a ≤ 1`): and there `|ζ'/ζ| ≤ C·(log|t|)³`.
* `rung3_of_growth`: hence `ψ(x) − x = O(x·exp(−c (log x)^{1/(1+n₁)}))` for every `n₁ > a`.

The hypothesis with `a = 2/3` is the Korobov–Vinogradov growth bound (layer II, not formalised
here), which would give every exponent below 3/5. A smaller `a` would give a larger exponent,
but no growth bound of this form is known for `a < 2/3`.

Route (Landau): the 3-4-1 inequality (`three_four_one`); Borel–Carathéodory at radius
`ρ = ¼(log|t|)^{−a}` via PNT+'s `FinalBound` (`local_bound`, `local_bound_point`);
`1/|ζ(s)| ≤ ζ(Re s)` (`inv_norm_zeta_le`); an explicit choice of the shift `δ(t)`
(`delta_choice`).
-/
import PrimeNumberTheoremAnd.StrongPNT

open Nat Filter Topology Set Function Complex Real ComplexConjugate MeasureTheory
open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

namespace Landau

/-- **3-4-1 ("the gears can't all point the wrong way"):** for `δ ∈ (0,1)` and any `t`,
`0 ≤ 3·(−Re ζ'/ζ(1+δ)) + 4·(−Re ζ'/ζ(1+δ+it)) + (−Re ζ'/ζ(1+δ+2it))`. -/
theorem three_four_one (δ : ℝ) (δrange : δ ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 ≤ 3 * -(ζ' (1 + δ) / ζ (1 + δ)).re +
      4 * -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re +
      -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re := by
  have hugeEq :
      3 * (-ζ' (1 + δ) / ζ (1 + δ)) +
      4 * (-ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)) +
      (-ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t))
    = ∑' (n : ℕ), Λ (n) * n ^ (-(1 : ℂ) - δ)
      * ((3 : ℂ) + 4 * n ^ (-I * t) + n ^ (-2 * I * t)) := by
    rw [LogDerivativeDirichlet (s := 1 + δ) (by simp [δrange.1]),
        LogDerivativeDirichlet (s := 1 + δ + I * t) (by simp [δrange.1]),
        LogDerivativeDirichlet (s := 1 + δ + 2 * I * t) (by simp [δrange.1])]
    simp only [← tsum_mul_left, ← neg_add', mul_add]; repeat rw [← Summable.tsum_add]
    · congr 1; funext n; by_cases heq0 : n = 0
      · simp only [heq0, ArithmeticFunction.map_zero, ofReal_zero, CharP.cast_eq_zero,
          zero_div, mul_zero, add_zero, neg_add_rev, zero_mul, neg_mul]
      · simp only [div_eq_mul_inv, mul_assoc, neg_mul]
        congr 2
        · simp only [← cpow_neg, neg_add_rev]
          ring_nf
        · simp only [← cpow_neg, neg_add_rev]
          rw [cpow_add _ _ ((cast_ne_zero (R := ℂ)).mpr heq0), mul_comm]
          ring_nf
        · simp only [← cpow_neg, neg_add_rev]
          rw [cpow_add _ _ ((cast_ne_zero (R := ℂ)).mpr heq0), mul_comm]
    · refine Summable.add (Summable.mul_left _ (vonMangoldtLSeriesSummable ?_))
        (Summable.mul_left _ (vonMangoldtLSeriesSummable ?_))
      · simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, δrange.1]
      · simp only [add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
          sub_self, add_zero, lt_add_iff_pos_right, δrange.1]
    · refine vonMangoldtLSeriesSummable ?_
      simp only [add_re, one_re, ofReal_re, mul_re, re_ofNat, I_re, mul_zero, im_ofNat, I_im,
        mul_one, sub_self, zero_mul, mul_im, add_zero, ofReal_im, lt_add_iff_pos_right, δrange.1]
    · refine Summable.mul_left _ (vonMangoldtLSeriesSummable ?_)
      simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, δrange.1]
    · refine Summable.mul_left _ (vonMangoldtLSeriesSummable ?_)
      simp only [add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, lt_add_iff_pos_right, δrange.1]
  have hugeEqRe :
      3 * -(ζ' (1 + δ) / ζ (1 + δ)).re +
      4 * -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re +
      -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re
    = 2 * ∑' (n : ℕ), Λ (n) * n ^ (-1 - δ) * (1 + Real.cos (-t * Real.log n)) ^ 2 := by
    have re_eq := congr_arg Complex.re hugeEq
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, neg_mul, neg_div,
      Complex.neg_re] at re_eq
    rw [re_eq, Complex.re_tsum, ← tsum_mul_left]
    · refine tsum_congr (fun n => ?_)
      by_cases heq0 : n = 0
      · simp [heq0]
      · repeat rw [Complex.cpow_def_of_ne_zero (cast_ne_zero (R := ℂ).mpr heq0)]
        simp only [← natCast_log, mul_neg, mul_re, ofReal_re, exp_re, sub_re, neg_re, one_re,
          ofReal_im, sub_im, neg_im, one_im, neg_zero, sub_self, mul_zero, sub_zero, mul_im,
          zero_mul, add_zero, Real.cos_zero, mul_one, exp_im, Real.sin_zero, add_re, re_ofNat,
          I_re, I_im, one_mul, zero_add, Real.exp_zero, Real.cos_neg, im_ofNat, Real.sin_neg,
          add_im, neg_mul, add_sq, one_pow, Real.cos_sq, one_div]
        rw [← Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero heq0))]
        ring_nf
    · simp only [mul_add, mul_assoc]; ring_nf
      refine Summable.add (Summable.add (Summable.mul_right _ ?_) (Summable.mul_right _ ?_)) ?_
      · refine (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (s := 1 + δ) (by simp [δrange.1])).congr (fun n => ?_)
        by_cases heq0 : n = 0
        · simp only [heq0, LSeries.term_zero, ArithmeticFunction.map_zero, ofReal_zero,
            CharP.cast_eq_zero, zero_mul]
        · simp only [ne_eq, heq0, not_false_eq_true, LSeries.term_of_ne_zero]
          rw [div_eq_mul_inv, ← Complex.cpow_neg, neg_add']
      · refine (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (s := 1 + δ + I * t) (by simp [δrange.1])).congr (fun n => ?_)
        by_cases heq0 : n = 0
        · simp only [heq0, LSeries.term_zero, ArithmeticFunction.map_zero, ofReal_zero,
            CharP.cast_eq_zero, zero_mul]
        · simp only [ne_eq, heq0, not_false_eq_true, LSeries.term_of_ne_zero]
          rw [div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
            Complex.cpow_add _  _ ((cast_ne_zero (R := ℂ)).mpr heq0)]
          ring_nf
      · refine (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (s := 1 + δ + 2 * I * t) (by simp [δrange.1])).congr (fun n => ?_)
        by_cases heq0 : n = 0
        · simp only [heq0, LSeries.term_zero, ArithmeticFunction.map_zero, ofReal_zero,
            CharP.cast_eq_zero, zero_mul]
        · simp only [ne_eq, heq0, not_false_eq_true, LSeries.term_of_ne_zero]
          rw [div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
            Complex.cpow_add _  _ ((cast_ne_zero (R := ℂ)).mpr heq0)]
          ring_nf
  rw [hugeEqRe]
  rw [mul_nonneg_iff_of_pos_left two_pos]
  exact tsum_nonneg (fun n => mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (sq_nonneg _))


/-! ## L2: the local log-derivative bound at an arbitrary radius -/

/-- The zeta function looked at through a disc of radius `ρr` around `s₀`, normalised to `1` at the
centre. -/
noncomputable def locF (s₀ : ℂ) (ρr : ℝ) (z : ℂ) : ℂ := ζ (s₀ + ρr * z) / ζ s₀

lemma locF_analytic {s₀ : ℂ} {ρr : ℝ} (hpole : ∀ z : ℂ, ‖z‖ < 2 → s₀ + ρr * z ≠ 1) :
    AnalyticOnNhd ℂ (locF s₀ ρr) (Metric.ball (0 : ℂ) 2) := by
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right] at hz
  unfold locF
  refine AnalyticAt.div_const ?_
  exact AnalyticAt.fun_comp (analyticAt_riemannZeta (hpole z hz))
    (analyticAt_const.fun_add (analyticAt_const.fun_mul analyticAt_id))

lemma finiteZeros_of_analytic {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 2))
    (hne : f 0 ≠ 0) : (SetOfZeros 1 f).Finite := by
  by_contra hinf; rw [Set.not_finite] at hinf
  have zerosSubset : SetOfZeros 1 f ⊆ Metric.closedBall (0 : ℂ) 1 := fun _ hx => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
  obtain ⟨x, hxK, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall 0 1) zerosSubset
  have hfeq : Set.EqOn f 0 (Metric.ball (0 : ℂ) 2) := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf
      Metric.isPreconnected_ball (z₀ := x) ?_ ?_
    · simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hxK ⊢
      linarith
    · simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
      exact hacc.mono (principal_mono.mpr fun _ h => h.2)
  exact hne (hfeq (Metric.mem_ball_self (by norm_num)))

/-- The universal constant from `FinalBound` at radii `r' = 1/4, r = 1/2, R' = 5/8, R = 3/4`. -/
noncomputable def Kc : ℝ :=
  16 * (1 / 2 : ℝ) ^ 2 / (1 / 2 - 1 / 4) ^ 3 +
    1 / (((3 / 4 : ℝ) ^ 2 / (5 / 8) - 5 / 8) * Real.log ((3 / 4) / (5 / 8)))

/-- **L2 (local bound).** Around `s₀` (with `Re s₀ > 1`), in a disc of radius `ρr` on which
`|ζ| ≤ B·|ζ(s₀)|`: `ρr·(−Re ζ'/ζ(s₀)) ≤ Kc·log B`, and a zero `β + i·Im s₀` within `ρr/2`
subtracts `ρr/(Re s₀ − β)`. -/
theorem local_bound {s₀ : ℂ} {ρr B : ℝ} (hs₀ : 1 < s₀.re) (hρ : 0 < ρr) (hB : 1 < B)
    (hpole : ∀ z : ℂ, ‖z‖ < 2 → s₀ + ρr * z ≠ 1)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖ζ (s₀ + ρr * z)‖ ≤ B * ‖ζ s₀‖) :
    ρr * -(ζ' s₀ / ζ s₀).re ≤ Kc * Real.log B ∧
    ∀ β : ℝ, ζ (β + s₀.im * I) = 0 → s₀.re - β ≤ ρr / 2 →
      ρr * -(ζ' s₀ / ζ s₀).re ≤ Kc * Real.log B - ρr / (s₀.re - β) := by
  set f := locF s₀ ρr with hfdef
  have hζ0 : ζ s₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs₀
  have hs1 : s₀ ≠ 1 := fun h => by rw [h] at hs₀; simp at hs₀
  have hf0 : f 0 = 1 := by simp [hfdef, locF, hζ0]
  have hfA2 := locF_analytic hpole
  have hfA : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    apply hfA2 z
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hfin : (SetOfZeros 1 f).Finite := finiteZeros_of_analytic hfA2 (by rw [hf0]; exact one_ne_zero)
  have hfb : ∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖f z‖ ≤ B := fun z hz => by
    simp only [hfdef, locF, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr hζ0)]
    exact hbound z hz
  have hz0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (1 / 4) \ SetOfZeros (5 / 8) f := by
    refine ⟨Metric.mem_closedBall_self (by norm_num), fun h => ?_⟩
    have := h.2; rw [hf0] at this; exact one_ne_zero this
  have FB := FinalBound (B := B) (r' := 1 / 4) (r := 1 / 2) (R' := 5 / 8) (R := 3 / 4) hB
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hfA hf0 hfin hfb hz0
  -- derivative of f at the centre
  have hderiv : deriv f 0 = ρr * (ζ' s₀ / ζ s₀) := by
    have h1 : HasDerivAt ζ (ζ' s₀) (s₀ + ρr * 0) := by
      simpa using (differentiableAt_riemannZeta hs1).hasDerivAt
    have hlin : HasDerivAt (fun z : ℂ => s₀ + ρr * z) (ρr : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (ρr : ℂ)).const_add s₀
    have h2 := (h1.comp (0 : ℂ) hlin).div_const (ζ s₀)
    rw [show f = (ζ ∘ fun z : ℂ => s₀ + ρr * z) / fun _ => ζ s₀ by
      funext z; simp [hfdef, locF]] 
    rw [show (ζ ∘ fun z : ℂ => s₀ + ρr * z) / (fun _ => ζ s₀) =
      fun z => (ζ ∘ fun z : ℂ => s₀ + ρr * z) z / ζ s₀ from rfl, h2.deriv]
    ring
  set Z := (finiteSetOfZeros_mono (r := 1 / 2) (by norm_num) hfin).toFinset with hZ
  set S : ℂ := ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (0 - ρ) with hS
  -- every zero in the disc lies to the left of the centre
  have hleft : ∀ ρ ∈ Z, ρ.re < 0 := by
    intro ρ hρ
    rw [hZ, Set.Finite.mem_toFinset] at hρ
    have hzero : ζ (s₀ + ρr * ρ) = 0 := by
      have := hρ.2; simp only [hfdef, locF, div_eq_zero_iff, hζ0, or_false] at this; exact this
    have hre : (s₀ + ρr * ρ).re < 1 := by
      by_contra h; rw [not_lt] at h
      exact riemannZeta_ne_zero_of_one_le_re h hzero
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hre
    by_contra h; rw [not_lt] at h; nlinarith
  have hterm : ∀ ρ ∈ Z, 0 ≤ ((analyticOrderNatAt f ρ : ℂ) / (0 - ρ)).re := by
    intro ρ hρ
    rw [zero_sub, div_eq_mul_inv, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, inv_re]
    have := hleft ρ hρ
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg (by simp; linarith) (normSq_nonneg _)
  have hSre : 0 ≤ S.re := by
    rw [hS, re_sum]; exact Finset.sum_nonneg hterm
  have hmain : ρr * -(ζ' s₀ / ζ s₀).re ≤ Kc * Real.log B - S.re := by
    have hre := Complex.re_le_norm (-(deriv f 0 / f 0 - S))
    rw [norm_neg, neg_re] at hre
    have FB' : ‖deriv f 0 / f 0 - S‖ ≤ Kc * Real.log B := FB
    have : -(deriv f 0 / f 0 - S).re ≤ Kc * Real.log B := le_trans hre FB'
    rw [hderiv, hf0, div_one, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at this
    linarith
  refine ⟨by linarith, fun β hβ hdist => ?_⟩
  -- the specific zero `β + i·Im s₀`
  have hβlt : β < s₀.re := by
    by_contra h; rw [not_lt] at h
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith) hβ
  set zs : ℂ := (((β - s₀.re) / ρr : ℝ) : ℂ) with hzs
  have hfzs : f zs = 0 := by
    simp only [hfdef, locF, div_eq_zero_iff, hζ0, or_false]
    convert hβ using 2
    apply Complex.ext <;> simp [hzs] <;> (try field_simp) <;> (try ring)
  have hzsnorm : ‖zs‖ ≤ 1 / 2 := by
    rw [hzs, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hρ,
      abs_of_neg (by linarith), div_le_iff₀ hρ]
    linarith
  have hzsZ : zs ∈ Z := by
    rw [hZ, Set.Finite.mem_toFinset]; exact ⟨hzsnorm, hfzs⟩
  -- its order is at least one
  have hord : 1 ≤ analyticOrderNatAt f zs := by
    have hnt : analyticOrderAt f zs ≠ ⊤ := by
      refine hfA2.analyticOrderAt_ne_top_of_isPreconnected Metric.isPreconnected_ball
        (Metric.mem_ball_self (by norm_num)) ?_ ?_
      · simp only [Metric.mem_ball, dist_zero_right]; linarith
      · have h0 : locF s₀ ρr 0 ≠ 0 := by rw [← hfdef, hf0]; exact one_ne_zero
        rw [(analyticOrderAt_eq_zero).mpr (Or.inr h0)]
        exact ENat.zero_ne_top
    have hn0 : analyticOrderAt f zs ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero, not_or, not_not, not_not]
      refine ⟨hfA2 zs ?_, hfzs⟩
      simp only [Metric.mem_ball, dist_zero_right]; linarith
    unfold analyticOrderNatAt
    by_contra h; rw [not_le] at h
    have : (analyticOrderAt f zs).toNat = 0 := by omega
    rcases ENat.toNat_eq_zero.mp this with h' | h'
    · exact hn0 h'
    · exact hnt h'
  have hterm_zs : ρr / (s₀.re - β) ≤ ((analyticOrderNatAt f zs : ℂ) / (0 - zs)).re := by
    have hval : ((analyticOrderNatAt f zs : ℂ) / (0 - zs)).re =
        (analyticOrderNatAt f zs : ℝ) * (ρr / (s₀.re - β)) := by
      have e : (0 : ℂ) - zs = (((s₀.re - β) / ρr : ℝ) : ℂ) := by rw [hzs]; push_cast; ring
      rw [e, ← ofReal_natCast, ← ofReal_div, ofReal_re]
      have : s₀.re - β ≠ 0 := by linarith
      field_simp
    rw [hval]
    have hpos : 0 < ρr / (s₀.re - β) := div_pos hρ (by linarith)
    have : (1 : ℝ) ≤ (analyticOrderNatAt f zs : ℝ) := by exact_mod_cast hord
    nlinarith
  have hSge : ρr / (s₀.re - β) ≤ S.re := by
    rw [hS, re_sum]
    exact le_trans hterm_zs (Finset.single_le_sum hterm hzsZ)
  linarith


/-! ## L3a: size of `1/ζ` to the right of the line -/

open LSeries in
lemma norm_term_one_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖term (fun _ => (1 : ℂ)) (σ : ℂ) n‖) := by
  have h := Real.summable_one_div_nat_rpow.mpr hσ
  refine h.congr (fun n => ?_)
  rw [norm_term_eq]
  split_ifs with hn
  · simp [hn, Real.zero_rpow (by linarith : σ ≠ 0)]
  · simp

open LSeries in
lemma term_one_eq_ofReal {σ : ℝ} (n : ℕ) :
    term (fun _ => (1 : ℂ)) (σ : ℂ) n = ((‖term (fun _ => (1 : ℂ)) (σ : ℂ) n‖ : ℝ) : ℂ) := by
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, if_neg hn]
    simp only [norm_one, ofReal_re]
    rw [ofReal_div, ofReal_one, ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]

/-- For `Re s > 1`: `1/|ζ(s)| ≤ ζ(Re s)`, via `1/ζ = Σ μ(n) n^{-s}`. -/
theorem inv_norm_zeta_le {s : ℂ} (hs : 1 < s.re) : 1 / ‖ζ s‖ ≤ ‖ζ (s.re : ℂ)‖ := by
  open LSeries in
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
  have hζ0 : ζ s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hμ : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 / ζ s := by
    rw [eq_div_iff hζ0, mul_comm]; exact hmul
  have hsum1 := norm_term_one_summable hs
  have hle : ∀ n, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun _ => (1 : ℂ)) (s.re : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · rfl
    · simp only [ofReal_re, norm_one]
      gcongr
      simpa [Complex.norm_intCast] using
        (show (|(ArithmeticFunction.moebius n : ℝ)|) ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
  have hsumμ : Summable (fun n => ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum1
  have h1 : 1 / ‖ζ s‖ = ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ := by
    rw [hμ, norm_div, norm_one]
  have hζσ : ζ (s.re : ℂ) = ∑' n, LSeries.term (fun _ => (1 : ℂ)) (s.re : ℂ) n := by
    rw [← LSeries_one_eq_riemannZeta (by simpa using hs)]; rfl
  have h2 : ‖ζ (s.re : ℂ)‖ = ∑' n, ‖LSeries.term (fun _ => (1 : ℂ)) (s.re : ℂ) n‖ := by
    rw [hζσ, show (fun n => LSeries.term (fun _ => (1 : ℂ)) (s.re : ℂ) n) =
      fun n => ((‖LSeries.term (fun _ => (1 : ℂ)) (s.re : ℂ) n‖ : ℝ) : ℂ) from
      funext term_one_eq_ofReal, ← ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  rw [h1, h2]
  exact (norm_tsum_le_tsum_norm hsumμ).trans (hsumμ.tsum_le_tsum hle hsum1)


/-! ## L3b: the growth hypothesis and the local bound at the KV radius -/

/-- **Polylog growth** of ζ in the region `σ ≥ 1 − (log|t|)^{−a}` (the Korobov–Vinogradov input
has `a = 2/3`). -/
def PolylogGrowth (a K : ℝ) : Prop :=
  ∀ t : ℝ, 3 ≤ |t| → ∀ σ : ℝ, 1 - Real.log |t| ^ (-a) ≤ σ → σ ≤ 2 →
    ‖ζ (σ + t * I)‖ ≤ K * Real.log |t| ^ K

noncomputable def Lg (T : ℝ) : ℝ := Real.log (|T| + 1)
noncomputable def rad (a T : ℝ) : ℝ := 1 / 4 * Lg T ^ (-a)
noncomputable def Bnd (K δ T : ℝ) : ℝ := 2 + K * Lg T ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖

lemma Lg_gt_one {T : ℝ} (hT : 4 ≤ |T|) : 1 < Lg T := by
  unfold Lg
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have := Real.exp_one_lt_d9; linarith

lemma rad_pos (a T : ℝ) (hT : 4 ≤ |T|) : 0 < rad a T := by
  unfold rad; have := Lg_gt_one hT; positivity

lemma rad_le (a : ℝ) (ha : 0 < a) {T : ℝ} (hT : 4 ≤ |T|) : rad a T ≤ 1 / 4 := by
  unfold rad
  have h1 : Lg T ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (Lg_gt_one hT).le (by linarith)
  linarith

/-- **L3b.** Under polylog growth, the local bound holds at `s₀ = 1 + δ + iT` with radius
`rad a T = ¼(log(|T|+1))^{−a}` and `B = Bnd K δ T`. -/
theorem apply_local {a K : ℝ} (ha : 0 < a) (hK : 0 < K) (hG : PolylogGrowth a K) {T δ : ℝ}
    (hT : 4 ≤ |T|) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    rad a T * -(ζ' ((1 + δ : ℝ) + T * I) / ζ ((1 + δ : ℝ) + T * I)).re ≤
        Kc * Real.log (Bnd K δ T) ∧
    ∀ β : ℝ, ζ (β + T * I) = 0 → 1 + δ - β ≤ rad a T / 2 →
      rad a T * -(ζ' ((1 + δ : ℝ) + T * I) / ζ ((1 + δ : ℝ) + T * I)).re ≤
        Kc * Real.log (Bnd K δ T) - rad a T / (1 + δ - β) := by
  set s₀ : ℂ := ((1 + δ : ℝ) : ℂ) + T * I with hs₀def
  have hre : s₀.re = 1 + δ := by simp [hs₀def]
  have him : s₀.im = T := by simp [hs₀def]
  set ρ := rad a T with hρdef
  have hρ := rad_pos a T hT
  have hρ4 := rad_le a ha hT
  have hL := Lg_gt_one hT
  have hζδ : 1 ≤ ‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖ := by
    have h := inv_norm_zeta_le (s := s₀) (by rw [hre]; linarith)
    rw [hre] at h
    have hz : 0 < ‖ζ s₀‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; linarith))
    rw [div_le_iff₀ hz] at h; linarith
  have hB : 1 < Bnd K δ T := by
    unfold Bnd; have : 0 ≤ K * Lg T ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by positivity
    linarith
  have hpole : ∀ z : ℂ, ‖z‖ < 2 → s₀ + ρ * z ≠ 1 := by
    intro z hz h
    have := congrArg Complex.im h
    simp only [add_im, him, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im] at this
    have hzi : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have : |T| ≤ ρ * |z.im| := by
      rw [show T = -(ρ * z.im) by linarith, abs_neg, abs_mul, abs_of_pos hρ]
    nlinarith [abs_nonneg z.im]
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖ζ (s₀ + ρ * z)‖ ≤ Bnd K δ T * ‖ζ s₀‖ := by
    intro z hz
    set s := s₀ + ρ * z with hsdef
    have hsre : s.re = 1 + δ + ρ * z.re := by simp [hsdef, hre]
    have hsim : s.im = T + ρ * z.im := by simp [hsdef, him]
    have hzr : |z.re| ≤ 3 / 4 := (Complex.abs_re_le_norm z).trans hz
    have hzi : |z.im| ≤ 3 / 4 := (Complex.abs_im_le_norm z).trans hz
    have hρzi : |ρ * z.im| ≤ 3 / 16 := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.im]
    have hρzr : |ρ * z.re| ≤ 3 / 4 * ρ := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.re]
    have hims : 3 ≤ |s.im| := by
      rw [hsim]; have := abs_sub_abs_le_abs_sub T (-(ρ * z.im))
      rw [abs_neg, sub_neg_eq_add] at this; linarith
    have hims2 : |s.im| ≤ |T| + 1 := by
      rw [hsim]; have := abs_add_le T (ρ * z.im); linarith
    have hlog_pos : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hlog_le : Real.log |s.im| ≤ Lg T := Real.log_le_log (by linarith) hims2
    have hpow : Lg T ^ (-a) ≤ Real.log |s.im| ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hlog_pos hlog_le (by linarith)
    have hlower : 1 - Real.log |s.im| ^ (-a) ≤ s.re := by
      rw [hsre]
      have : Lg T ^ (-a) = 4 * ρ := by rw [hρdef, rad]; ring
      have := abs_le.mp hρzr
      linarith
    have hupper : s.re ≤ 2 := by
      rw [hsre]; have := abs_le.mp hρzr; linarith
    have hgs := hG s.im hims s.re hlower hupper
    rw [Complex.re_add_im] at hgs
    have hKpow : K * Real.log |s.im| ^ K ≤ K * Lg T ^ K :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog_pos.le hlog_le hK.le) hK.le
    have hζs0 : 0 ≤ ‖ζ s₀‖ := norm_nonneg _
    calc ‖ζ s‖ ≤ K * Lg T ^ K := hgs.trans hKpow
      _ ≤ K * Lg T ^ K * (‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖) := by
          have : 0 ≤ K * Lg T ^ K := by positivity
          nlinarith
      _ ≤ Bnd K δ T * ‖ζ s₀‖ := by
          unfold Bnd; nlinarith [mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Lg T) K))
            (norm_nonneg (ζ ((1 + δ : ℝ) : ℂ))), hζs0]
  have hloc := local_bound (s₀ := s₀) (ρr := ρ) (B := Bnd K δ T) (by rw [hre]; linarith) hρ hB
    hpole hbound
  refine ⟨hloc.1, fun β hβ hd => ?_⟩
  have := hloc.2 β (by rw [him]; exact hβ) (by rw [hre]; exact hd)
  rwa [hre] at this


/-! ## L3c: the zero gap -/

/-- Algebra of the 3-4-1 argument: `4/(1+δ−β) ≤ 3/δ + M` with `δM ≤ 1/4` forces `1 − β ≥ 3δ/13`. -/
lemma gap_algebra {δ M β : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hδM : δ * M ≤ 1 / 4) (hβ : β < 1 + δ)
    (h : 4 / (1 + δ - β) ≤ 3 / δ + M) : 3 * δ / 13 ≤ 1 - β := by
  have hd : 0 < 1 + δ - β := by linarith
  rw [div_le_iff₀ hd] at h
  have h2 : 4 * δ ≤ (3 + δ * M) * (1 + δ - β) := by
    have e : (3 / δ + M) * (1 + δ - β) * δ = (3 + δ * M) * (1 + δ - β) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h hδ.le]
  nlinarith

/-- **L3c (zero gap).** Under polylog growth: if `ζ(β + it) = 0`, `|t| ≥ 4`, and `δ ∈ (0, 1/2]`
is small enough (`δ ≤ rad(t)/4` and `δ·M ≤ 1/4`, where `M` collects the three local bounds),
then `1 − β ≥ 3δ/13`. -/
theorem zero_gap {a K : ℝ} (ha : 0 < a) (hK : 0 < K) (hG : PolylogGrowth a K) :
    ∃ C0 ≥ (1 : ℝ), ∀ (β t δ : ℝ), ζ (β + t * I) = 0 → 4 ≤ |t| → 0 < δ → δ ≤ 1 / 2 →
      δ ≤ rad a t / 4 →
      δ * (3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / rad a t +
        Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t)) ≤ 1 / 4 →
      3 * δ / 13 ≤ 1 - β := by
  obtain ⟨C0, hC0, hShift⟩ := ShiftZeroBound
  refine ⟨C0, hC0, fun β t δ hβ ht hδ hδ2 hδr hδM => ?_⟩
  have hβ1 : β < 1 := by
    by_contra h; rw [not_lt] at h
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith) hβ
  have ht2 : 4 ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
  have hr1 := rad_pos a t ht
  have hr2 := rad_pos a (2 * t) ht2
  have hB1 : 0 ≤ Real.log (Bnd K δ t) := Real.log_nonneg (by
    unfold Bnd; have : 0 ≤ K * Lg t ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht).le; positivity
    linarith)
  have hB2 : 0 ≤ Real.log (Bnd K δ (2 * t)) := Real.log_nonneg (by
    unfold Bnd; have : 0 ≤ K * Lg (2 * t) ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht2).le; positivity
    linarith)
  have hKc : 0 ≤ Kc := by unfold Kc; positivity
  -- the three inputs
  have h341 := three_four_one δ ⟨hδ, by linarith⟩ t
  have hX := hShift δ ⟨hδ, by linarith⟩
  have hZloc := (apply_local ha hK hG ht2 hδ hδ2).1
  have e2 : ((1 + δ : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I = 1 + δ + 2 * I * t := by push_cast; ring
  rw [e2] at hZloc
  have hZ : -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re ≤
      Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t) := by
    rw [le_div_iff₀ hr2]; linarith
  have e1 : ((1 + δ : ℝ) : ℂ) + (t : ℂ) * I = 1 + δ + I * t := by push_cast; ring
  by_cases hnear : 1 + δ - β ≤ rad a t / 2
  · have hYloc := (apply_local ha hK hG ht hδ hδ2).2 β hβ hnear
    rw [e1] at hYloc
    have hd : 0 < 1 + δ - β := by linarith
    have hY : -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re ≤
        Kc * Real.log (Bnd K δ t) / rad a t - 1 / (1 + δ - β) := by
      have e : rad a t * (Kc * Real.log (Bnd K δ t) / rad a t - 1 / (1 + δ - β)) =
          Kc * Real.log (Bnd K δ t) - rad a t / (1 + δ - β) := by field_simp
      exact le_of_mul_le_mul_left (by rw [e]; exact hYloc) hr1
    set M := 3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / rad a t +
      Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t) with hMdef
    have hM : 0 ≤ M := by positivity
    have hineq : 4 / (1 + δ - β) ≤ 3 / δ + M := by
      have e3 : 4 / (1 + δ - β) = 4 * (1 / (1 + δ - β)) := by ring
      have e4 : 3 / δ = 3 * (1 / δ) := by ring
      have e5 : 4 * Kc * Real.log (Bnd K δ t) / rad a t =
          4 * (Kc * Real.log (Bnd K δ t) / rad a t) := by ring
      rw [e3, e4, hMdef, e5]
      linarith
    exact gap_algebra hδ hM hδM (by linarith) hineq
  · have := rad_pos a t ht
    rw [not_le] at hnear
    linarith


/-! ## L3d: choosing δ -/

lemma Lg_mono {T U : ℝ} (hT : 4 ≤ |T|) (h : |T| ≤ |U|) : Lg T ≤ Lg U := by
  unfold Lg; exact Real.log_le_log (by positivity) (by linarith)

lemma rad_anti (a : ℝ) (ha : 0 < a) {T U : ℝ} (hT : 4 ≤ |T|) (h : |T| ≤ |U|) : rad a U ≤ rad a T := by
  unfold rad
  have := Real.rpow_le_rpow_of_nonpos (by linarith [Lg_gt_one hT]) (Lg_mono hT h) (by linarith : -a ≤ 0)
  linarith

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; norm_num
  have h2 := Real.log_le_sub_one_of_pos hs
  linarith

/-- The explicit δ used at height `t`. -/
noncomputable def dlt (a N t : ℝ) : ℝ := rad a (2 * t) / (N * (1 + Real.log (Lg (2 * t))))

set_option maxHeartbeats 1600000 in
/-- **L3d.** There is `N ≥ 4` for which `δ = dlt a N t` meets all hypotheses of `zero_gap`,
for every `|t| ≥ 4`. -/
theorem delta_choice {a K : ℝ} (ha : 0 < a) (hK : 0 < K) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ N : ℝ, 4 ≤ N ∧ ∀ t : ℝ, 4 ≤ |t| →
      let δ := dlt a N t
      0 < δ ∧ δ ≤ 1 / 2 ∧ δ ≤ rad a t / 4 ∧
      δ * (3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / rad a t +
        Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t)) ≤ 1 / 4 := by
  obtain ⟨c1, hc1, hnear⟩ := ZetaNear1BndExact
  have hKc : 0 ≤ Kc := by unfold Kc; positivity
  set D := Real.log (2 + K * c1) + Real.log 4 with hD
  have hDnn : 0 ≤ D := by
    have : 0 ≤ Real.log (2 + K * c1) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  set P := 3 * C0 / 4 + 5 * Kc * (D + K + a + 1) with hP
  have hPnn : 0 ≤ P := by positivity
  set N := 8 * P + (80 * Kc) ^ 2 + 4 with hN
  refine ⟨N, by nlinarith [sq_nonneg (80 * Kc)], fun t ht => ?_⟩
  intro δ
  have ht2 : 4 ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
  have hle2 : |t| ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
  set L := Lg (2 * t) with hLdef
  have hL1 : 1 < L := Lg_gt_one ht2
  have hlogL : 0 < Real.log L := Real.log_pos hL1
  have hr2 := rad_pos a (2 * t) ht2
  have hr2le := rad_le a ha ht2
  have hr12 := rad_anti a ha ht hle2
  have hNpos : 0 < N := by nlinarith [sq_nonneg (80 * Kc)]
  have hN4 : 4 ≤ N := by nlinarith [sq_nonneg (80 * Kc)]
  have hden : 1 ≤ N * (1 + Real.log L) := by nlinarith
  have hδpos : 0 < δ := div_pos hr2 (by linarith)
  have hδle : δ ≤ rad a (2 * t) / 4 := by
    show rad a (2 * t) / (N * (1 + Real.log L)) ≤ rad a (2 * t) / 4
    exact div_le_div_of_nonneg_left hr2.le (by norm_num) (by nlinarith)
  have hδ12 : δ ≤ 1 / 2 := by linarith
  refine ⟨hδpos, hδ12, by linarith, ?_⟩
  -- bound on log B
  have hδ1 : δ ≤ 1 := by linarith
  have hζ : ‖ζ ((1 + δ : ℝ) : ℂ)‖ ≤ c1 / δ := by
    have := hnear (1 + δ) ⟨by linarith, by linarith⟩
    simpa using this
  have hLK : 1 ≤ L ^ K := Real.one_le_rpow hL1.le hK.le
  have hBle : Bnd K δ (2 * t) ≤ (2 + K * c1) * L ^ K / δ := by
    unfold Bnd
    rw [← hLdef]
    have h1 : K * L ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ ≤ K * L ^ K * (c1 / δ) :=
      mul_le_mul_of_nonneg_left hζ (by positivity)
    have h2 : (2 : ℝ) ≤ 2 * L ^ K / δ := by
      rw [le_div_iff₀ hδpos]; nlinarith
    have e : (2 + K * c1) * L ^ K / δ = 2 * L ^ K / δ + K * L ^ K * (c1 / δ) := by ring
    linarith
  have hB1le : Bnd K δ t ≤ Bnd K δ (2 * t) := by
    unfold Bnd
    have hmono : Lg t ^ K ≤ L ^ K :=
      Real.rpow_le_rpow (by linarith [Lg_gt_one ht]) (Lg_mono ht hle2) hK.le
    nlinarith [norm_nonneg (ζ ((1 + δ : ℝ) : ℂ)), mul_le_mul_of_nonneg_left hmono hK.le]
  have hB2pos : 1 < Bnd K δ (2 * t) := by
    unfold Bnd; have : 0 ≤ K * Lg (2 * t) ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht2).le; positivity
    linarith
  have hB1pos : 1 < Bnd K δ t := by
    unfold Bnd; have : 0 ≤ K * Lg t ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht).le; positivity
    linarith
  have hlogB : Real.log (Bnd K δ (2 * t)) ≤ D + Real.log N + (K + a + 1) * Real.log L := by
    have hpos : 0 < (2 + K * c1) * L ^ K / δ := by positivity
    have h1 := Real.log_le_log (by linarith) hBle
    rw [Real.log_div (by positivity) hδpos.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by linarith)] at h1
    -- log δ = log rad − log N − log(1 + log L), and log rad = −log 4 − a log L
    have hlogδ : Real.log δ = Real.log (rad a (2 * t)) - Real.log N - Real.log (1 + Real.log L) := by
      show Real.log (rad a (2 * t) / (N * (1 + Real.log L))) = _
      rw [Real.log_div hr2.ne' (by positivity), Real.log_mul hNpos.ne' (by positivity)]; ring
    have hlogrd : Real.log (rad a (2 * t)) = -Real.log 4 - a * Real.log L := by
      unfold rad; rw [← hLdef, Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by linarith)]
      rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]; ring
    have hl1 : Real.log (1 + Real.log L) ≤ Real.log L := by
      apply Real.log_le_log (by linarith)
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L); linarith
    rw [hlogδ, hlogrd] at h1
    linarith
  have hlogN : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hNpos
  have hsqrtN : 80 * Kc ≤ Real.sqrt N := by
    rw [show 80 * Kc = Real.sqrt ((80 * Kc) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- assemble
  set M := 3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / rad a t +
      Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t)
  have hlogB1 : Real.log (Bnd K δ t) ≤ Real.log (Bnd K δ (2 * t)) := Real.log_le_log (by linarith) hB1le
  have hlogB1nn : 0 ≤ Real.log (Bnd K δ t) := Real.log_nonneg hB1pos.le
  have hM : M ≤ 3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t) := by
    have h4 : 4 * Kc * Real.log (Bnd K δ t) / rad a t ≤
        4 * Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t) := by
      have hB2nn : 0 ≤ Real.log (Bnd K δ (2 * t)) := Real.log_nonneg hB2pos.le
      apply div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hKc) hB2nn)
        (by have := mul_le_mul_of_nonneg_left hlogB1 hKc; linarith) hr2 hr12
    have e : 5 * Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t) =
        4 * Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t) +
        Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t) := by ring
    linarith
  have hδrad : δ / rad a (2 * t) = 1 / (N * (1 + Real.log L)) := by
    show rad a (2 * t) / (N * (1 + Real.log L)) / rad a (2 * t) = _
    field_simp
  have hmain : δ * (3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t)) ≤ 1 / 4 := by
    have e : δ * (3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t)) =
        3 * C0 * δ + 5 * Kc * Real.log (Bnd K δ (2 * t)) * (δ / rad a (2 * t)) := by
      field_simp
    rw [e, hδrad]
    have h1 : 3 * C0 * δ ≤ 3 * C0 / (4 * N) := by
      have : δ ≤ 1 / (4 * N) := by
        show rad a (2 * t) / (N * (1 + Real.log L)) ≤ 1 / (4 * N)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc 3 * C0 * δ ≤ 3 * C0 * (1 / (4 * N)) := by gcongr
        _ = 3 * C0 / (4 * N) := by ring
    have h2 : 5 * Kc * Real.log (Bnd K δ (2 * t)) * (1 / (N * (1 + Real.log L))) ≤
        5 * Kc * (D + Real.log N + (K + a + 1)) / N := by
      have hq : (D + Real.log N + (K + a + 1) * Real.log L) / (1 + Real.log L) ≤
          D + Real.log N + (K + a + 1) := by
        rw [div_le_iff₀ (by linarith)]
        have hlogNnn : 0 ≤ Real.log N := Real.log_nonneg (by linarith [hN4])
        nlinarith
      have hB2nn : 0 ≤ Real.log (Bnd K δ (2 * t)) := Real.log_nonneg hB2pos.le
      calc 5 * Kc * Real.log (Bnd K δ (2 * t)) * (1 / (N * (1 + Real.log L)))
          = 5 * Kc / N * (Real.log (Bnd K δ (2 * t)) / (1 + Real.log L)) := by field_simp
        _ ≤ 5 * Kc / N * ((D + Real.log N + (K + a + 1) * Real.log L) / (1 + Real.log L)) := by
            gcongr
        _ ≤ 5 * Kc / N * (D + Real.log N + (K + a + 1)) := by gcongr
        _ = 5 * Kc * (D + Real.log N + (K + a + 1)) / N := by ring
    have h3 : 3 * C0 / (4 * N) + 5 * Kc * (D + Real.log N + (K + a + 1)) / N ≤ 1 / 4 := by
      have e : 3 * C0 / (4 * N) + 5 * Kc * (D + Real.log N + (K + a + 1)) / N =
          P / N + 5 * Kc * Real.log N / N := by rw [hP]; field_simp; ring
      rw [e]
      have hPN : P / N ≤ 1 / 8 := by
        rw [div_le_iff₀ hNpos]; nlinarith [sq_nonneg (80 * Kc)]
      have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
      have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
      have hLN : 5 * Kc * Real.log N / N ≤ 1 / 8 := by
        rw [div_le_iff₀ hNpos]
        have : 5 * Kc * Real.log N ≤ 10 * Kc * Real.sqrt N := by nlinarith
        nlinarith
      linarith
    linarith
  calc δ * M ≤ δ * (3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / rad a (2 * t)) :=
        mul_le_mul_of_nonneg_left hM hδpos.le
    _ ≤ 1 / 4 := hmain


/-! ## L3e: the zero-free region -/

/-- Zeros at height `|t| ≥ 4` stay `(3/13)·dlt` away from the line. -/
theorem zero_gap_explicit {a K : ℝ} (ha : 0 < a) (hK : 0 < K) (hG : PolylogGrowth a K) :
    ∃ N : ℝ, 4 ≤ N ∧ ∀ β t : ℝ, ζ (β + t * I) = 0 → 4 ≤ |t| → 3 * dlt a N t / 13 ≤ 1 - β := by
  obtain ⟨C0, hC0, hgap⟩ := zero_gap ha hK hG
  obtain ⟨N, hN, hch⟩ := delta_choice ha hK C0 hC0
  refine ⟨N, hN, fun β t hβ ht => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hch t ht
  exact hgap β t (dlt a N t) hβ ht h1 h2 h3 h4

lemma Lg_two_le {t : ℝ} (ht : 4 ≤ |t|) : Lg (2 * t) ≤ 2 * Real.log |t| := by
  unfold Lg
  rw [← Real.log_rpow (by linarith), abs_mul]
  apply Real.log_le_log (by positivity)
  norm_num
  have h := sq_abs t
  nlinarith [abs_nonneg t]

/-- **L3 (Landau's theorem, general form).** Polylog growth of ζ in `σ ≥ 1 − (log|t|)^{−a}` gives
a zero-free region of width `(log|t|)^{−n₁}` for every `n₁ > a`. -/
theorem zeroFree_of_growth {a K n₁ : ℝ} (ha : 0 < a) (hK : 0 < K) (hG : PolylogGrowth a K)
    (hn : a < n₁) : ZetaZeroFreeGenProp n₁ := by
  obtain ⟨N, hN, hgap⟩ := zero_gap_explicit ha hK hG
  obtain ⟨A₁, ⟨hA₁pos, hA₁le⟩, hfree1⟩ := ZetaZeroFree1
  set ε := n₁ - a with hε
  have hεpos : 0 < ε := by linarith
  set Abig : ℝ := 3 / 13 * (2 : ℝ) ^ (-a) / (4 * N) * (1 / (2 + 1 / ε)) / 2 with hAbig
  have hAbigpos : 0 < Abig := by positivity
  set A : ℝ := min (1 / 2) (min (A₁ / 2) Abig) with hA
  have hApos : 0 < A := lt_min (by norm_num) (lt_min (by linarith) hAbigpos)
  have hAle : A ≤ 1 / 2 := min_le_left _ _
  refine ⟨A, ⟨hApos, hAle⟩, fun σ t ht hσ hzero => ?_⟩
  obtain ⟨hσlo, hσhi⟩ := hσ
  have hℓ1 : 1 < Real.log |t| := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hℓpos : 0 < Real.log |t| := by linarith
  by_cases hbig : 4 ≤ |t|
  · -- large heights: the Landau gap
    have hg := hgap σ t hzero hbig
    set ℓ := Real.log |t| with hℓ
    set L := Lg (2 * t) with hL
    have hL1 : 1 < L := Lg_gt_one (by rw [abs_mul]; norm_num; linarith)
    have hLle : L ≤ 2 * ℓ := Lg_two_le hbig
    have hlogL : 0 < Real.log L := Real.log_pos hL1
    -- lower bound for dlt
    have hlogℓnn : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1.le
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hDpos : 0 < 1 + Real.log 2 + Real.log ℓ := by linarith
    have hdlt : 2 ^ (-a) * ℓ ^ (-a) / (4 * N * (1 + Real.log 2 + Real.log ℓ)) ≤ dlt a N t := by
      unfold dlt rad
      rw [← hL]
      have hpow : (2 * ℓ) ^ (-a) ≤ L ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hLle (by linarith)
      rw [Real.mul_rpow (by norm_num) hℓpos.le] at hpow
      have hlog2 : 1 + Real.log L ≤ 1 + Real.log 2 + Real.log ℓ := by
        have : Real.log L ≤ Real.log 2 + Real.log ℓ := by
          rw [← Real.log_mul (by norm_num) hℓpos.ne']; exact Real.log_le_log (by linarith) hLle
        linarith
      rw [div_le_div_iff₀ (mul_pos (by positivity) hDpos) (by positivity)]
      calc 2 ^ (-a) * ℓ ^ (-a) * (N * (1 + Real.log L))
          ≤ L ^ (-a) * (N * (1 + Real.log 2 + Real.log ℓ)) :=
            mul_le_mul hpow (mul_le_mul_of_nonneg_left hlog2 (by linarith)) (by positivity)
              (by positivity)
        _ = 1 / 4 * L ^ (-a) * (4 * N * (1 + Real.log 2 + Real.log ℓ)) := by ring
    have hlogℓ : Real.log ℓ ≤ ℓ ^ ε / ε := Real.log_le_rpow_div hℓpos.le hεpos
    have hℓε : 1 ≤ ℓ ^ ε := Real.one_le_rpow hℓ1.le hεpos.le
    have hden : 1 + Real.log 2 + Real.log ℓ ≤ (2 + 1 / ε) * ℓ ^ ε := by
      have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      have e : (2 + 1 / ε) * ℓ ^ ε = 2 * ℓ ^ ε + ℓ ^ ε / ε := by ring
      rw [e]; linarith
    have hsplit : ℓ ^ (-a) = ℓ ^ (-n₁) * ℓ ^ ε := by
      rw [← Real.rpow_add hℓpos]; congr 1; rw [hε]; ring
    have hq : 0 < ℓ ^ (-n₁) := by positivity
    set X := 2 ^ (-a) * ℓ ^ (-n₁) with hX
    have hXpos : 0 < X := by positivity
    have hQ : X / (4 * N * (2 + 1 / ε)) ≤ 2 ^ (-a) * ℓ ^ (-a) / (4 * N * (1 + Real.log 2 + Real.log ℓ)) := by
      rw [hsplit, div_le_div_iff₀ (by positivity) (mul_pos (by positivity) hDpos)]
      have := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ X * (4 * N))
      rw [hX]; nlinarith
    have hAbigX : Abig * ℓ ^ (-n₁) = 3 / 26 * (X / (4 * N * (2 + 1 / ε))) := by
      rw [hAbig, hX]; field_simp; ring
    have hup : 1 - σ ≤ A / ℓ ^ n₁ := by linarith
    have hAℓ : A / ℓ ^ n₁ ≤ Abig * ℓ ^ (-n₁) := by
      rw [Real.rpow_neg hℓpos.le, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _))
        (inv_nonneg.mpr (by positivity))
    have hXd : 0 < X / (4 * N * (2 + 1 / ε)) := by positivity
    linarith
  · -- small heights `3 < |t| < 4`: the classical region suffices
    rw [not_le] at hbig
    apply hfree1 σ t ht ⟨_, hσhi⟩ hzero
    have hAA : A ≤ A₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hcomp : A / Real.log |t| ^ n₁ ≤ A₁ / Real.log |t| ^ (1 : ℝ) := by
      rw [Real.rpow_one, div_le_div_iff₀ (by positivity) hℓpos]
      rcases le_or_gt 1 n₁ with h1 | h1
      · have : Real.log |t| ≤ Real.log |t| ^ n₁ := by
          calc Real.log |t| = Real.log |t| ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ Real.log |t| ^ n₁ := Real.rpow_le_rpow_of_exponent_le hℓ1.le h1
        nlinarith
      · have h1' : 1 ≤ Real.log |t| ^ n₁ := Real.one_le_rpow hℓ1.le (by linarith)
        have hℓ2 : Real.log |t| < 2 := by
          have h4 := Real.log_lt_log (by linarith) hbig
          have : Real.log 4 < 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            have := Real.log_two_lt_d9; push_cast; linarith
          linarith
        have hApos' : 0 ≤ A := hApos.le
        calc A * Real.log |t| ≤ A₁ / 2 * 2 := by nlinarith
          _ = A₁ * 1 := by ring
          _ ≤ A₁ * Real.log |t| ^ n₁ := by nlinarith
    linarith


/-! ## L4a: to the right of the line, `|ζ'/ζ(s)| ≤ −ζ'/ζ(Re s)` -/

theorem norm_logDeriv_le {s : ℂ} (hs : 1 < s.re) :
    ‖ζ' s / ζ s‖ ≤ -(ζ' (s.re : ℂ) / ζ (s.re : ℂ)).re := by
  have hsr : 1 < ((s.re : ℂ)).re := by simpa using hs
  have hsum := vonMangoldtLSeriesSummable hs
  have hnorm : ∀ n : ℕ, ‖(Λ n : ℂ) / (n : ℂ) ^ s‖ = Λ n / (n : ℝ) ^ s.re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hreal : ∀ n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ (s.re : ℂ) = ((Λ n / (n : ℝ) ^ s.re : ℝ) : ℂ) := by
    intro n
    rw [ofReal_div, ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
  have hsummR : Summable (fun n : ℕ => Λ n / (n : ℝ) ^ s.re) := by
    refine (Complex.summable_ofReal.mp ?_)
    exact (vonMangoldtLSeriesSummable hsr).congr hreal
  have h1 : ζ' s / ζ s = -∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s := by
    have h := LogDerivativeDirichlet s hs; linear_combination -h
  have h2 : -(ζ' (s.re : ℂ) / ζ (s.re : ℂ)) = ((∑' n : ℕ, Λ n / (n : ℝ) ^ s.re : ℝ) : ℂ) := by
    rw [show -(ζ' (s.re : ℂ) / ζ (s.re : ℂ)) = -ζ' (s.re : ℂ) / ζ (s.re : ℂ) by ring,
      LogDerivativeDirichlet _ hsr, ofReal_tsum]
    exact tsum_congr hreal
  rw [h1, norm_neg, show -(ζ' (s.re : ℂ) / ζ (s.re : ℂ)).re = (-(ζ' (s.re : ℂ) / ζ (s.re : ℂ))).re
    by simp, h2, ofReal_re]
  calc ‖∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s‖ ≤ ∑' n : ℕ, ‖(Λ n : ℂ) / (n : ℂ) ^ s‖ :=
        norm_tsum_le_tsum_norm (hsummR.congr (fun n => (hnorm n).symm))
    _ = ∑' n : ℕ, Λ n / (n : ℝ) ^ s.re := tsum_congr hnorm

/-! ## L4b: the local bound at a general point of the disc -/

/-- **L4b.** Around `s₀` with radius `ρr` and growth ratio `B` as in `local_bound`: at any point
`s = s₀ + ρr·z` with `‖z‖ ≤ 1/4`, `ζ(s) ≠ 0`, if every zero of ζ within `ρr/2` of `s₀` is at
distance `≥ g` from `s`, then `ρr·|ζ'/ζ(s)| ≤ Kc·log B + (ρr/g)·log B / log(3/2)`. -/
theorem local_bound_point {s₀ z : ℂ} {ρr B g : ℝ} (hs₀ : 1 < s₀.re) (hρ : 0 < ρr) (hB : 1 < B)
    (hg : 0 < g) (hz : ‖z‖ ≤ 1 / 4) (hζz : ζ (s₀ + ρr * z) ≠ 0)
    (hpole : ∀ w : ℂ, ‖w‖ < 2 → s₀ + ρr * w ≠ 1)
    (hbound : ∀ w : ℂ, ‖w‖ ≤ 3 / 4 → ‖ζ (s₀ + ρr * w)‖ ≤ B * ‖ζ s₀‖)
    (hgap : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ζ (s₀ + ρr * w) = 0 → g ≤ ‖(s₀ + ρr * z) - (s₀ + ρr * w)‖) :
    ρr * ‖ζ' (s₀ + ρr * z) / ζ (s₀ + ρr * z)‖ ≤
      Kc * Real.log B + ρr / g * (1 / Real.log ((3 / 4) / (1 / 2)) * Real.log B) := by
  set f := locF s₀ ρr with hfdef
  have hζ0 : ζ s₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs₀
  have hf0 : f 0 = 1 := by simp [hfdef, locF, hζ0]
  have hfA2 := locF_analytic hpole
  have hfA : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    apply hfA2 w
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hfin : (SetOfZeros 1 f).Finite := finiteZeros_of_analytic hfA2 (by rw [hf0]; exact one_ne_zero)
  have hfb : ∀ w : ℂ, ‖w‖ ≤ 3 / 4 → ‖f w‖ ≤ B := fun w hw => by
    simp only [hfdef, locF, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr hζ0)]
    exact hbound w hw
  have hfz : f z ≠ 0 := by simp only [hfdef, locF, div_ne_zero_iff]; exact ⟨hζz, hζ0⟩
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) (1 / 4) \ SetOfZeros (5 / 8) f := by
    refine ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hz, fun h => hfz h.2⟩
  have FB := FinalBound (B := B) (r' := 1 / 4) (r := 1 / 2) (R' := 5 / 8) (R := 3 / 4) hB
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hfA hf0 hfin hfb hzmem
  have ZB := ZerosBound (B := B) (r := 1 / 2) (R := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hfA hf0 hfin (fun w hw => hfb w hw)
  -- the logarithmic derivative of f at z
  have hs1 : s₀ + ρr * z ≠ 1 := hpole z (by linarith)
  have hderiv : deriv f z = ρr * ζ' (s₀ + ρr * z) / ζ s₀ := by
    have h1 : HasDerivAt ζ (ζ' (s₀ + ρr * z)) (s₀ + ρr * z) :=
      (differentiableAt_riemannZeta hs1).hasDerivAt
    have hlin : HasDerivAt (fun w : ℂ => s₀ + ρr * w) (ρr : ℂ) z := by
      simpa using ((hasDerivAt_id z).const_mul (ρr : ℂ)).const_add s₀
    have h2 := (h1.comp z hlin).div_const (ζ s₀)
    rw [show f = fun w => (ζ ∘ fun w : ℂ => s₀ + ρr * w) w / ζ s₀ by
      funext w; simp [hfdef, locF], h2.deriv]
    ring
  have hratio : deriv f z / f z = ρr * (ζ' (s₀ + ρr * z) / ζ (s₀ + ρr * z)) := by
    rw [hderiv]; simp only [hfdef, locF]; field_simp
  set Z := (finiteSetOfZeros_mono (r := 1 / 2) (by norm_num) hfin).toFinset with hZ
  set S : ℂ := ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) with hS
  have hSbound : ‖S‖ ≤ ρr / g * (1 / Real.log ((3 / 4) / (1 / 2)) * Real.log B) := by
    have hterm : ∀ q ∈ Z, ‖(analyticOrderNatAt f q : ℂ) / (z - q)‖ ≤
        (analyticOrderNatAt f q : ℝ) * (ρr / g) := by
      intro q hq
      rw [hZ, Set.Finite.mem_toFinset] at hq
      have hzero : ζ (s₀ + ρr * q) = 0 := by
        have := hq.2; simp only [hfdef, locF, div_eq_zero_iff, hζ0, or_false] at this; exact this
      have hgq := hgap q hq.1 hzero
      have hdist : ‖(s₀ + ρr * z) - (s₀ + ρr * q)‖ = ρr * ‖z - q‖ := by
        rw [show (s₀ + ρr * z) - (s₀ + ρr * q) = (ρr : ℂ) * (z - q) by ring, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
      rw [hdist] at hgq
      have hzq : 0 < ‖z - q‖ := by
        by_contra h; rw [not_lt] at h
        have : ρr * ‖z - q‖ ≤ 0 := by nlinarith [norm_nonneg (z - q)]
        linarith
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ hzq]
      have hm : (0 : ℝ) ≤ analyticOrderNatAt f q := Nat.cast_nonneg _
      have h1 : 1 ≤ ‖z - q‖ * (ρr / g) := by
        rw [show ‖z - q‖ * (ρr / g) = ρr * ‖z - q‖ / g by ring, le_div_iff₀ hg]; linarith
      nlinarith
    calc ‖S‖ ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) * (ρr / g) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * (ρr / g) := by rw [Finset.sum_mul]
      _ ≤ (1 / Real.log ((3 / 4) / (1 / 2)) * Real.log B) * (ρr / g) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast ZB
      _ = ρr / g * (1 / Real.log ((3 / 4) / (1 / 2)) * Real.log B) := by ring
  have FB' : ‖deriv f z / f z - S‖ ≤ Kc * Real.log B := FB
  have htri : ‖deriv f z / f z‖ ≤ ‖deriv f z / f z - S‖ + ‖S‖ := by
    have := norm_add_le (deriv f z / f z - S) S; simpa using this
  rw [hratio] at htri FB'
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at htri
  linarith

/-! ## L4c: helpers -/

/-- A power `ℓ^{ε}` beats `c₂ + log ℓ`: a uniform small constant. -/
lemma small_A {a ε c c₂ : ℝ} (hε : 0 < ε) (hc : 0 < c) (hc₂ : 1 ≤ c₂) :
    ∃ A > 0, ∀ ℓ : ℝ, 1 ≤ ℓ → A * ℓ ^ (-(a + ε)) ≤ c * ℓ ^ (-a) / (c₂ + Real.log ℓ) := by
  refine ⟨c / (c₂ + 1 / ε), by positivity, fun ℓ hℓ => ?_⟩
  have hℓpos : 0 < ℓ := by linarith
  have hlog : Real.log ℓ ≤ ℓ ^ ε / ε := Real.log_le_rpow_div hℓpos.le hε
  have hQ : 1 ≤ ℓ ^ ε := Real.one_le_rpow hℓ hε.le
  have hlognn : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hden : c₂ + Real.log ℓ ≤ (c₂ + 1 / ε) * ℓ ^ ε := by
    have e : (c₂ + 1 / ε) * ℓ ^ ε = c₂ * ℓ ^ ε + ℓ ^ ε / ε := by ring
    rw [e]; nlinarith
  have hsplit : ℓ ^ (-(a + ε)) = ℓ ^ (-a) / ℓ ^ ε := by
    rw [show -(a + ε) = -a + -ε by ring, Real.rpow_add hℓpos, Real.rpow_neg hℓpos.le ε, div_eq_mul_inv]
  have hlogpos : 0 < c₂ + Real.log ℓ := by linarith
  rw [hsplit, le_div_iff₀ hlogpos]
  have hQpos : 0 < ℓ ^ ε := by positivity
  have hX : 0 ≤ c / (c₂ + 1 / ε) * (ℓ ^ (-a) / ℓ ^ ε) := by positivity
  calc c / (c₂ + 1 / ε) * (ℓ ^ (-a) / ℓ ^ ε) * (c₂ + Real.log ℓ)
      ≤ c / (c₂ + 1 / ε) * (ℓ ^ (-a) / ℓ ^ ε) * ((c₂ + 1 / ε) * ℓ ^ ε) :=
        mul_le_mul_of_nonneg_left hden hX
    _ = c * ℓ ^ (-a) := by field_simp

/-- The disc facts used by the local bounds, at centre `(1+δ) + iT` and radius `rad a T`. -/
theorem disc_facts {a K : ℝ} (ha : 0 < a) (hK : 0 < K) (hG : PolylogGrowth a K) {T δ : ℝ}
    (hT : 4 ≤ |T|) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    (∀ z : ℂ, ‖z‖ < 2 → (((1 + δ : ℝ) : ℂ) + T * I) + rad a T * z ≠ 1) ∧
    (∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖ζ ((((1 + δ : ℝ) : ℂ) + T * I) + rad a T * z)‖ ≤
      Bnd K δ T * ‖ζ (((1 + δ : ℝ) : ℂ) + T * I)‖) ∧ 1 < Bnd K δ T := by
  set s₀ : ℂ := ((1 + δ : ℝ) : ℂ) + T * I with hs₀def
  have hre : s₀.re = 1 + δ := by simp [hs₀def]
  have him : s₀.im = T := by simp [hs₀def]
  set ρ := rad a T with hρdef
  have hρ := rad_pos a T hT
  have hρ4 := rad_le a ha hT
  have hL := Lg_gt_one hT
  have hζδ : 1 ≤ ‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖ := by
    have h := inv_norm_zeta_le (s := s₀) (by rw [hre]; linarith)
    rw [hre] at h
    have hz : 0 < ‖ζ s₀‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; linarith))
    rw [div_le_iff₀ hz] at h; linarith
  have hB : 1 < Bnd K δ T := by
    unfold Bnd; have : 0 ≤ K * Lg T ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by positivity
    linarith
  refine ⟨fun z hz h => ?_, fun z hz => ?_, hB⟩
  · have := congrArg Complex.im h
    simp only [add_im, him, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im] at this
    have hzi : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have : |T| ≤ ρ * |z.im| := by
      rw [show T = -(ρ * z.im) by linarith, abs_neg, abs_mul, abs_of_pos hρ]
    nlinarith [abs_nonneg z.im]
  · set s := s₀ + ρ * z with hsdef
    have hsre : s.re = 1 + δ + ρ * z.re := by simp [hsdef, hre]
    have hsim : s.im = T + ρ * z.im := by simp [hsdef, him]
    have hzr : |z.re| ≤ 3 / 4 := (Complex.abs_re_le_norm z).trans hz
    have hzi : |z.im| ≤ 3 / 4 := (Complex.abs_im_le_norm z).trans hz
    have hρzi : |ρ * z.im| ≤ 3 / 16 := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.im]
    have hρzr : |ρ * z.re| ≤ 3 / 4 * ρ := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.re]
    have hims : 3 ≤ |s.im| := by
      rw [hsim]; have := abs_sub_abs_le_abs_sub T (-(ρ * z.im))
      rw [abs_neg, sub_neg_eq_add] at this; linarith
    have hims2 : |s.im| ≤ |T| + 1 := by
      rw [hsim]; have := abs_add_le T (ρ * z.im); linarith
    have hlog_pos : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hlog_le : Real.log |s.im| ≤ Lg T := Real.log_le_log (by linarith) hims2
    have hpow : Lg T ^ (-a) ≤ Real.log |s.im| ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hlog_pos hlog_le (by linarith)
    have hlower : 1 - Real.log |s.im| ^ (-a) ≤ s.re := by
      rw [hsre]
      have : Lg T ^ (-a) = 4 * ρ := by rw [hρdef, rad]; ring
      have := abs_le.mp hρzr
      linarith
    have hupper : s.re ≤ 2 := by
      rw [hsre]; have := abs_le.mp hρzr; linarith
    have hgs := hG s.im hims s.re hlower hupper
    rw [Complex.re_add_im] at hgs
    have hKpow : K * Real.log |s.im| ^ K ≤ K * Lg T ^ K :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog_pos.le hlog_le hK.le) hK.le
    have hζs0 : 0 ≤ ‖ζ s₀‖ := norm_nonneg _
    calc ‖ζ s‖ ≤ K * Lg T ^ K := hgs.trans hKpow
      _ ≤ K * Lg T ^ K * (‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖) := by
          have : 0 ≤ K * Lg T ^ K := by positivity
          nlinarith
      _ ≤ Bnd K δ T * ‖ζ s₀‖ := by
          unfold Bnd; nlinarith [mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Lg T) K))
            (norm_nonneg (ζ ((1 + δ : ℝ) : ℂ))), hζs0]

lemma dlt_anti (a : ℝ) (ha : 0 < a) {N : ℝ} (hN : 0 < N) {T U : ℝ} (hT : 4 ≤ |T|) (h : |T| ≤ |U|) :
    dlt a N U ≤ dlt a N T := by
  have hT2 : 4 ≤ |2 * T| := by rw [abs_mul]; norm_num; linarith
  have hTU : |2 * T| ≤ |2 * U| := by rw [abs_mul, abs_mul]; norm_num; linarith
  unfold dlt
  have hr := rad_anti a ha hT2 hTU
  have hrpos := rad_pos a (2 * U) (by linarith)
  have hL1 := Lg_gt_one hT2
  have hlog : Real.log (Lg (2 * T)) ≤ Real.log (Lg (2 * U)) :=
    Real.log_le_log (by linarith) (Lg_mono hT2 hTU)
  have hlnn : 0 ≤ Real.log (Lg (2 * T)) := Real.log_nonneg hL1.le
  apply div_le_div₀ (rad_pos a (2 * T) hT2).le hr (by positivity)
  nlinarith

lemma two_log_bound {t : ℝ} (ht : 3 ≤ |t|) : Real.log (2 * (|t| + 1) + 1) ≤ 2 * Real.log |t| := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by positivity)
  norm_num
  have h := sq_abs t
  nlinarith [abs_nonneg t]

/-- `log |t| ≥ 1` once `|t| ≥ 3`. -/
lemma ell_ge_one {t : ℝ} (ht : 3 ≤ |t|) : 1 ≤ Real.log |t| := by
  rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith

lemma Lg_le_two_ell {t : ℝ} (ht : 4 ≤ |t|) : Lg t ≤ 2 * Real.log |t| := by
  have h2 : |t| ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith [abs_nonneg t]
  exact (Lg_mono ht h2).trans (Lg_two_le ht)

/-- `(2ℓ)^{-a} ≤ L^{-a}` for `1 ≤ L ≤ 2ℓ`, written as `2^{-a} ℓ^{-a}`. -/
lemma rpow_lower {a L ℓ : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (hLℓ : L ≤ 2 * ℓ) :
    (2 : ℝ) ^ (-a) * ℓ ^ (-a) ≤ L ^ (-a) := by
  have hℓ : 0 ≤ ℓ := by linarith
  rw [← Real.mul_rpow (by norm_num) hℓ]
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hLℓ (by linarith)

lemma rad_lower {a t : ℝ} (ha : 0 < a) (ht : 4 ≤ |t|) :
    (2 : ℝ) ^ (-a) * Real.log |t| ^ (-a) / 4 ≤ rad a t := by
  unfold rad
  have := rpow_lower ha (Lg_gt_one ht).le (Lg_le_two_ell ht)
  linarith

lemma inv_rad_le {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : 4 ≤ |t|) :
    1 / rad a t ≤ 8 * Real.log |t| := by
  have hL := Lg_gt_one ht
  have e : 1 / rad a t = 4 * Lg t ^ a := by
    unfold rad; rw [Real.rpow_neg (by linarith)]; field_simp
  have h1 : Lg t ^ a ≤ Lg t := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL.le ha1
  rw [e]; linarith [Lg_le_two_ell ht]

/-- The zero gap at height `|t|+1`, bounded below by an explicit function of `ℓ = log|t|`. -/
lemma dlt_lower {a N t : ℝ} (ha : 0 < a) (hN : 0 < N) (ht : 3 ≤ |t|) :
    (2 : ℝ) ^ (-a) * Real.log |t| ^ (-a) / (4 * N * (1 + Real.log 2 + Real.log (Real.log |t|))) ≤
      dlt a N (|t| + 1) := by
  have hℓ := ell_ge_one ht
  have hU : 4 ≤ |2 * (|t| + 1)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < |t| + 1)]; norm_num; linarith
  have hL1 := Lg_gt_one hU
  have hLle : Lg (2 * (|t| + 1)) ≤ 2 * Real.log |t| := by
    unfold Lg; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < |t| + 1), abs_two]
    exact two_log_bound ht
  unfold dlt rad
  have hnum := rpow_lower ha hL1.le hLle
  have hlog : Real.log (Lg (2 * (|t| + 1))) ≤ Real.log 2 + Real.log (Real.log |t|) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hLle
  have hlnn : 0 ≤ Real.log (Lg (2 * (|t| + 1))) := Real.log_nonneg hL1.le
  have hl2 : 0 ≤ Real.log (Real.log |t|) := Real.log_nonneg hℓ
  have hpos : 0 < (2 : ℝ) ^ (-a) * Real.log |t| ^ (-a) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul hnum (by nlinarith : N * (1 + Real.log (Lg (2 * (|t| + 1)))) ≤
      N * (1 + Real.log 2 + Real.log (Real.log |t|))) (by positivity) (by positivity)
  nlinarith

lemma inv_dlt_le {a N t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hN : 0 < N) (ht : 3 ≤ |t|) :
    1 / dlt a N (|t| + 1) ≤ 24 * N * Real.log |t| ^ 2 := by
  set ℓ := Real.log |t| with hℓdef
  have hℓ := ell_ge_one ht
  have hlow := dlt_lower (N := N) ha hN ht
  rw [← hℓdef] at hlow
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlℓ : Real.log ℓ ≤ ℓ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlnn : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hden : 0 < 4 * N * (1 + Real.log 2 + Real.log ℓ) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have hG : 0 < (2 : ℝ) ^ (-a) * ℓ ^ (-a) / (4 * N * (1 + Real.log 2 + Real.log ℓ)) := by positivity
  have hinv : 1 / dlt a N (|t| + 1) ≤
      4 * N * (1 + Real.log 2 + Real.log ℓ) * ((2 : ℝ) ^ a * ℓ ^ a) := by
    calc 1 / dlt a N (|t| + 1)
        ≤ 1 / ((2 : ℝ) ^ (-a) * ℓ ^ (-a) / (4 * N * (1 + Real.log 2 + Real.log ℓ))) :=
          one_div_le_one_div_of_le hG hlow
      _ = _ := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by linarith)]
          have : 0 < (2 : ℝ) ^ a := by positivity
          have : 0 < ℓ ^ a := by positivity
          field_simp
  have h2a : (2 : ℝ) ^ a ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
  have hℓa : ℓ ^ a ≤ ℓ := by
    have := Real.rpow_le_rpow_of_exponent_le hℓ ha1; rwa [Real.rpow_one] at this
  have h2apos : 0 ≤ (2 : ℝ) ^ a := by positivity
  have hℓapos : 0 ≤ ℓ ^ a := by positivity
  have hprod : (2 : ℝ) ^ a * ℓ ^ a ≤ 2 * ℓ := mul_le_mul h2a hℓa hℓapos (by norm_num)
  have hsum : 1 + Real.log 2 + Real.log ℓ ≤ 3 * ℓ := by linarith
  calc 1 / dlt a N (|t| + 1) ≤ 4 * N * (1 + Real.log 2 + Real.log ℓ) * ((2 : ℝ) ^ a * ℓ ^ a) := hinv
    _ ≤ 4 * N * (3 * ℓ) * (2 * ℓ) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsum (by positivity)) hprod
          (by positivity) (by positivity)
    _ = 24 * N * ℓ ^ 2 := by ring

/-- `log B` at the centre `1 + ρ/8`, `ρ = rad a t`, is `O(log |t|)`. -/
lemma logBnd_le {a K c1 t : ℝ} (ha : 0 < a) (hK : 0 < K) (hc1 : 0 < c1)
    (hnear : ∀ σ : ℝ, σ ∈ Set.Ioc 1 2 → ‖ζ σ‖ ≤ c1 / (σ - 1)) (ht : 4 ≤ |t|) :
    Real.log (Bnd K (rad a t / 8) t) ≤
      (Real.log (2 + 32 * K * c1) + 2 * (K + a)) * Real.log |t| := by
  have hL := Lg_gt_one ht
  have hρ := rad_pos a t ht
  have hρ4 := rad_le a ha ht
  have hℓ := ell_ge_one (by linarith : (3 : ℝ) ≤ |t|)
  have hζ : ‖ζ ((1 + rad a t / 8 : ℝ) : ℂ)‖ ≤ 32 * c1 * Lg t ^ a := by
    have h := hnear (1 + rad a t / 8) ⟨by linarith, by linarith⟩
    have e : c1 / (1 + rad a t / 8 - 1) = 32 * c1 * Lg t ^ a := by
      unfold rad; rw [Real.rpow_neg (by linarith)]
      have : 0 < Lg t ^ a := by positivity
      field_simp; ring
    rw [e] at h; exact h
  have hLK : 1 ≤ Lg t ^ (K + a) := Real.one_le_rpow hL.le (by linarith)
  have hB : Bnd K (rad a t / 8) t ≤ (2 + 32 * K * c1) * Lg t ^ (K + a) := by
    unfold Bnd
    have hKp : 0 ≤ K * Lg t ^ K := by positivity
    have e : Lg t ^ (K + a) = Lg t ^ K * Lg t ^ a := Real.rpow_add (by linarith) K a
    calc 2 + K * Lg t ^ K * ‖ζ ((1 + rad a t / 8 : ℝ) : ℂ)‖
        ≤ 2 + K * Lg t ^ K * (32 * c1 * Lg t ^ a) := by gcongr
      _ = 2 + 32 * K * c1 * Lg t ^ (K + a) := by rw [e]; ring
      _ ≤ 2 * Lg t ^ (K + a) + 32 * K * c1 * Lg t ^ (K + a) := by linarith
      _ = _ := by ring
  have hBpos : 0 < Bnd K (rad a t / 8) t := by
    unfold Bnd; positivity
  have hD : 0 ≤ Real.log (2 + 32 * K * c1) := Real.log_nonneg (by nlinarith)
  calc Real.log (Bnd K (rad a t / 8) t)
      ≤ Real.log ((2 + 32 * K * c1) * Lg t ^ (K + a)) := Real.log_le_log hBpos hB
    _ = Real.log (2 + 32 * K * c1) + (K + a) * Real.log (Lg t) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by linarith)]
    _ ≤ Real.log (2 + 32 * K * c1) + (K + a) * (2 * Real.log |t|) := by
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < Lg t)
        have := Lg_le_two_ell ht
        have hKa : 0 ≤ K + a := by linarith
        nlinarith
    _ ≤ _ := by nlinarith

set_option maxHeartbeats 1600000 in
/-- **L4c, inside the disc.** Near `Re s = 1` (to the left of `1 + ρ/8`, inside the zero-free
region), `ζ'/ζ = O((log |t|)³)`: the local bound at centre `1 + ρ/8 + it`, with every zero at
distance at least the gap `g = 3·dlt(|t|+1)/26`. -/
theorem near_bound {a K N c1 t σ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K)
    (hG : PolylogGrowth a K) (hN : 4 ≤ N)
    (hgap : ∀ β t : ℝ, ζ (β + t * I) = 0 → 4 ≤ |t| → 3 * dlt a N t / 13 ≤ 1 - β)
    (hc1 : 0 < c1) (hnear : ∀ σ : ℝ, σ ∈ Set.Ioc 1 2 → ‖ζ σ‖ ≤ c1 / (σ - 1))
    (ht : 5 ≤ |t|) (hζ : ζ (σ + t * I) ≠ 0) (hlo1 : 1 - σ ≤ rad a t / 8)
    (hlo2 : 1 - σ ≤ 3 * dlt a N (|t| + 1) / 26) (hhi : σ < 1 + rad a t / 8) :
    ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      (Real.log (2 + 32 * K * c1) + 2 * (K + a)) *
        (8 * Kc + 208 * (1 / Real.log ((3 / 4) / (1 / 2))) * N) * Real.log |t| ^ 3 := by
  have ht4 : 4 ≤ |t| := by linarith
  have ht3 : 3 ≤ |t| := by linarith
  set ℓ := Real.log |t| with hℓdef
  have hℓ : 1 ≤ ℓ := ell_ge_one ht3
  set ρ := rad a t with hρdef
  have hρ : 0 < ρ := rad_pos a t ht4
  have hρ4 : ρ ≤ 1 / 4 := rad_le a ha ht4
  set δ := ρ / 8 with hδdef
  set s₀ : ℂ := ((1 + δ : ℝ) : ℂ) + t * I with hs₀def
  obtain ⟨hpole, hbound, hB1⟩ := disc_facts ha hK hG (T := t) (δ := δ) ht4 (by positivity)
    (by linarith)
  set z : ℂ := (((σ - 1 - δ) / ρ : ℝ) : ℂ) with hzdef
  have hsz : s₀ + (ρ : ℂ) * z = σ + t * I := by
    apply Complex.ext
    · simp only [hs₀def, hzdef, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, sub_zero]
      field_simp; ring
    · simp [hs₀def, hzdef]
  have hz : ‖z‖ ≤ 1 / 4 := by
    rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hρ, div_le_iff₀ hρ,
      abs_le]
    constructor <;> linarith
  have hNpos : 0 < N := by linarith
  set g := 3 * dlt a N (|t| + 1) / 26 with hgdef
  have hlow := dlt_lower (N := N) ha hNpos ht3
  have hlnn : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlowpos : 0 < (2 : ℝ) ^ (-a) * ℓ ^ (-a) / (4 * N * (1 + Real.log 2 + Real.log ℓ)) := by
    positivity
  have hg : 0 < g := by rw [hgdef]; linarith
  have hgap' : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ζ (s₀ + ρ * w) = 0 →
      g ≤ ‖(s₀ + ρ * z) - (s₀ + ρ * w)‖ := by
    intro w hw hw0
    set u := s₀ + (ρ : ℂ) * w with hudef
    have hure : u.re = 1 + δ + ρ * w.re := by simp [hudef, hs₀def]
    have huim : u.im = t + ρ * w.im := by simp [hudef, hs₀def]
    have hwi : |w.im| ≤ 1 / 2 := (Complex.abs_im_le_norm w).trans hw
    have hρwi : |ρ * w.im| ≤ 1 / 8 := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg w.im]
    have hu4 : 4 ≤ |u.im| := by
      rw [huim]; have := abs_sub_abs_le_abs_sub t (-(ρ * w.im))
      rw [abs_neg, sub_neg_eq_add] at this; linarith
    have hu5 : |u.im| ≤ |t| + 1 := by
      rw [huim]; have := abs_add_le t (ρ * w.im); linarith
    have hz0 : ζ (u.re + u.im * I) = 0 := by rw [Complex.re_add_im]; exact hw0
    have h1 := hgap u.re u.im hz0 hu4
    have h2 := dlt_anti a ha hNpos (T := u.im) (U := |t| + 1) hu4
      (by rw [abs_of_pos (by positivity : (0 : ℝ) < |t| + 1)]; exact hu5)
    rw [hsz]
    have hre : ((σ : ℂ) + t * I - u).re = σ - u.re := by simp
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I - u)
    rw [hre] at this
    have hσu : g ≤ σ - u.re := by rw [hgdef] at hlo2 ⊢; linarith
    exact hσu.trans ((le_abs_self _).trans this)
  have hs₀ : 1 < s₀.re := by simp [hs₀def]; positivity
  have main := local_bound_point hs₀ hρ hB1 hg hz (by rw [hsz]; exact hζ) hpole hbound hgap'
  rw [hsz] at main
  set L := ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ with hLdef
  set lB := Real.log (Bnd K δ t) with hlBdef
  set cL := 1 / Real.log ((3 / 4) / (1 / 2)) with hcLdef
  set E := Real.log (2 + 32 * K * c1) + 2 * (K + a) with hEdef
  have hcL : 0 < cL := by
    rw [hcLdef]; have : 0 < Real.log ((3 / 4 : ℝ) / (1 / 2)) := Real.log_pos (by norm_num)
    positivity
  have hKc : 0 ≤ Kc := by unfold Kc; positivity
  have hlB : lB ≤ E * ℓ := logBnd_le ha hK hc1 hnear ht4
  have hlBpos : 0 < lB := Real.log_pos hB1
  have hinvρ : 1 / ρ ≤ 8 * ℓ := inv_rad_le ha ha1 ht4
  have hinvg : 1 / g ≤ 208 * N * ℓ ^ 2 := by
    have h := inv_dlt_le (N := N) ha ha1 hNpos ht3
    have hdpos : 0 < dlt a N (|t| + 1) := by linarith
    have e : 1 / g = 26 / 3 * (1 / dlt a N (|t| + 1)) := by rw [hgdef]; field_simp
    rw [e]; linarith
  have hL1 : L ≤ Kc * lB * (1 / ρ) + cL * lB * (1 / g) := by
    have h2 : L ≤ (Kc * lB + ρ / g * (cL * lB)) / ρ := by
      rw [le_div_iff₀ hρ]; linarith [main]
    have e : (Kc * lB + ρ / g * (cL * lB)) / ρ = Kc * lB * (1 / ρ) + cL * lB * (1 / g) := by
      field_simp
    linarith
  have hEnn : 0 ≤ E := by
    have : 0 ≤ Real.log (2 + 32 * K * c1) := Real.log_nonneg (by nlinarith)
    linarith
  have hE0 : 0 ≤ E * ℓ := by positivity
  have t1 : Kc * lB * (1 / ρ) ≤ Kc * (E * ℓ) * (8 * ℓ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlB hKc) hinvρ (by positivity) (by positivity)
  have t2 : cL * lB * (1 / g) ≤ cL * (E * ℓ) * (208 * N * ℓ ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlB hcL.le) hinvg (by positivity) (by positivity)
  have hℓ23 : ℓ ^ 2 ≤ ℓ ^ 3 := pow_le_pow_right₀ hℓ (by norm_num)
  have hKE : 0 ≤ Kc * E := mul_nonneg hKc hEnn
  calc L ≤ Kc * (E * ℓ) * (8 * ℓ) + cL * (E * ℓ) * (208 * N * ℓ ^ 2) := by linarith
    _ = 8 * (Kc * E) * ℓ ^ 2 + E * (208 * cL * N) * ℓ ^ 3 := by ring
    _ ≤ 8 * (Kc * E) * ℓ ^ 3 + E * (208 * cL * N) * ℓ ^ 3 := by nlinarith
    _ = E * (8 * Kc + 208 * cL * N) * ℓ ^ 3 := by ring

set_option maxHeartbeats 1600000 in
/-- **L4.** Polylog growth gives the log-derivative bound `ζ'/ζ = O((log|t|)³)` on the
zero-free region `σ ≥ 1 − A/(log|t|)^{n₁}`, for every `n₁ > a` (with `0 < a ≤ 1`). -/
theorem logDerivBnd_of_growth {a K n₁ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K)
    (hG : PolylogGrowth a K) (hn : a < n₁) : LogDerivZetaBndUnifGenProp n₁ 3 := by
  obtain ⟨N, hN, hgap⟩ := zero_gap_explicit ha hK hG
  obtain ⟨Az, ⟨hAzpos, hAzle⟩, hfree⟩ := zeroFree_of_growth ha hK hG hn
  obtain ⟨C3, hC3⟩ := LogDerivZetaBdd_of_Re_ge_three_halves
  obtain ⟨Cs, hCs, hstrip⟩ := LogDerivZetaUniformLogSquaredBoundStripSpec
  obtain ⟨C0, hC0, hshift⟩ := ShiftZeroBound
  obtain ⟨c1, hc1, hnear⟩ := ZetaNear1BndExact
  have hNpos : 0 < N := by linarith
  set ε := n₁ - a with hεdef
  have hε : 0 < ε := by linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨Ag, hAg, hAgb⟩ := small_A (a := a) (ε := ε) (c := 3 / 26 * (2 : ℝ) ^ (-a) / (4 * N))
    (c₂ := 1 + Real.log 2) hε (by positivity) (by linarith)
  have hF := FinIoo
  set A := min (min (1 / 2) (F / 2)) (min Az (min Ag ((2 : ℝ) ^ (-a) / 32))) with hAdef
  have hApos : 0 < A := by
    have : 0 < (2 : ℝ) ^ (-a) / 32 := by positivity
    simp only [hAdef, lt_min_iff]; refine ⟨⟨by norm_num, by linarith [hF.1]⟩, hAzpos, hAg, this⟩
  have hA1 : A ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hAF : A ≤ F / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hAz : A ≤ Az := (min_le_right _ _).trans (min_le_left _ _)
  have hAAg : A ≤ Ag := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hA2 : A ≤ (2 : ℝ) ^ (-a) / 32 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set En := (Real.log (2 + 32 * K * c1) + 2 * (K + a)) *
    (8 * Kc + 208 * (1 / Real.log ((3 / 4) / (1 / 2))) * N) with hEndef
  have hEn : 0 ≤ En := by
    have : 0 ≤ Real.log (2 + 32 * K * c1) := Real.log_nonneg (by nlinarith)
    have : 0 < Real.log ((3 / 4 : ℝ) / (1 / 2)) := Real.log_pos (by norm_num)
    have : 0 ≤ Kc := by unfold Kc; positivity
    positivity
  have hC3n : 0 ≤ max C3 0 := le_max_right _ _
  refine ⟨A, ⟨hApos, hA1⟩, max C3 0 + Cs + (64 + C0) + En + 1, by positivity,
    fun σ t ht hσ => ?_⟩
  rw [Set.mem_Ici] at hσ
  have ht3 : 3 ≤ |t| := ht.le
  set ℓ := Real.log |t| with hℓdef
  have hℓ : 1 ≤ ℓ := ell_ge_one ht3
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hℓ3 : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ
  have hℓ23 : ℓ ^ 2 ≤ ℓ ^ 3 := pow_le_pow_right₀ hℓ (by norm_num)
  have hℓ13 : ℓ ≤ ℓ ^ 3 := by nlinarith
  have hℓn : 1 ≤ ℓ ^ n₁ := Real.one_le_rpow hℓ (by linarith)
  have hApow : A / ℓ ^ n₁ = A * ℓ ^ (-n₁) := by
    rw [Real.rpow_neg (by linarith), div_eq_mul_inv]
  set C := max C3 0 + Cs + (64 + C0) + En + 1 with hCdef
  have hCpos : 0 ≤ C := by positivity
  have fin : ∀ P : ℝ, P ≤ C → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ P * ℓ ^ 3 →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * ℓ ^ 3 := fun P hP h =>
    h.trans (mul_le_mul_of_nonneg_right hP (by positivity))
  by_cases h32 : 3 / 2 ≤ σ
  · refine fin (max C3 0) (by linarith) ?_
    have h := hC3 (σ + t * I) (by simp; exact h32)
    have : max C3 0 ≤ max C3 0 * ℓ ^ 3 := le_mul_of_one_le_right hC3n hℓ3
    exact h.trans ((le_max_left _ _).trans this)
  rw [not_le] at h32
  by_cases ht5 : |t| < 5
  · refine fin Cs (by linarith) ?_
    have hℓ2 : ℓ < 2 := by
      rw [hℓdef, Real.log_lt_iff_lt_exp (by linarith)]
      have := Real.exp_one_gt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have hlo : 1 - F / ℓ ≤ σ := by
      have h1 : A / ℓ ^ n₁ ≤ A := div_le_self hApos.le hℓn
      have h2 : F / 2 ≤ F / ℓ := div_le_div_of_nonneg_left hF.1.le (by linarith) hℓ2.le
      linarith
    have h := hstrip t ht3 σ ⟨hlo, h32.le⟩
    exact h.trans (mul_le_mul_of_nonneg_left hℓ23 hCs.le)
  rw [not_lt] at ht5
  have ht4 : 4 ≤ |t| := by linarith
  set ρ := rad a t with hρdef
  have hρ : 0 < ρ := rad_pos a t ht4
  have hρ4 : ρ ≤ 1 / 4 := rad_le a ha ht4
  by_cases hin : σ < 1 + ρ / 8
  · refine fin En (by linarith) ?_
    have hpowle : ℓ ^ (-n₁) ≤ ℓ ^ (-a) := Real.rpow_le_rpow_of_exponent_le hℓ (by linarith)
    have hpn : 0 ≤ ℓ ^ (-n₁) := by positivity
    have hlo1 : 1 - σ ≤ ρ / 8 := by
      have hrl := rad_lower ha ht4
      rw [← hℓdef, ← hρdef] at hrl
      have : A * ℓ ^ (-n₁) ≤ (2 : ℝ) ^ (-a) / 32 * ℓ ^ (-a) :=
        mul_le_mul hA2 hpowle hpn (by positivity)
      linarith
    have hlo2 : 1 - σ ≤ 3 * dlt a N (|t| + 1) / 26 := by
      have hd := dlt_lower (N := N) ha hNpos ht3
      rw [← hℓdef] at hd
      have hb := hAgb ℓ hℓ
      rw [show -(a + ε) = -n₁ by rw [hεdef]; ring] at hb
      have e : 3 / 26 * (2 : ℝ) ^ (-a) / (4 * N) * ℓ ^ (-a) / (1 + Real.log 2 + Real.log ℓ) =
          3 / 26 * ((2 : ℝ) ^ (-a) * ℓ ^ (-a) / (4 * N * (1 + Real.log 2 + Real.log ℓ))) := by
        have : 0 < 1 + Real.log 2 + Real.log ℓ := by
          have := Real.log_nonneg hℓ; linarith
        field_simp
      rw [e] at hb
      have : A * ℓ ^ (-n₁) ≤ Ag * ℓ ^ (-n₁) := mul_le_mul_of_nonneg_right hAAg hpn
      linarith
    have hζ : ζ (σ + t * I) ≠ 0 := by
      by_cases h1 : 1 ≤ σ
      · exact riemannZeta_ne_zero_of_one_le_re (by simp; exact h1)
      · rw [not_le] at h1
        refine hfree σ t ht ⟨?_, h1⟩
        have : A / ℓ ^ n₁ ≤ Az / ℓ ^ n₁ := div_le_div_of_nonneg_right hAz (by positivity)
        linarith
    exact near_bound ha ha1 hK hG hN hgap hc1 hnear ht5 hζ hlo1 hlo2 hin
  · rw [not_lt] at hin
    refine fin (64 + C0) (by linarith) ?_
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    have h := norm_logDeriv_le (s := (σ : ℂ) + t * I) (by rw [hre]; linarith)
    rw [hre] at h
    have hs := hshift (σ - 1) ⟨by linarith, by linarith⟩
    have e : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
    rw [e] at hs
    have hinv : 1 / (σ - 1) ≤ 64 * ℓ := by
      have h1 : 1 / (σ - 1) ≤ 1 / (ρ / 8) := one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 := inv_rad_le ha ha1 ht4
      rw [← hρdef, ← hℓdef] at h2
      have e2 : 1 / (ρ / 8) = 8 * (1 / ρ) := by field_simp
      linarith
    calc ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ 64 * ℓ + C0 := by linarith
      _ ≤ (64 + C0) * ℓ ^ 3 := by nlinarith

/-- **Layer III, assembled: polylog growth ⇒ rung 3.** If `|ζ(σ+it)| ≤ K (log|t|)^K` on
`σ ≥ 1 − (log|t|)^{−a}` (`0 < a ≤ 1`), then for every `n₁ > a`,
`ψ(x) − x = O(x·exp(−c (log x)^{1/(1+n₁)}))`. -/
theorem rung3_of_growth {a K n₁ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K)
    (hG : PolylogGrowth a K) (hn : a < n₁) :
    ∃ c > 0, (fun x : ℝ => Chebyshev.psi x - x) =O[Filter.atTop]
      (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁)))) :=
  GenStrengthPNT (LogDerivZetaBoundedAndHoloGen (logDerivBnd_of_growth ha ha1 hK hG hn)
    (LogDerivZetaHolcLargeTGen (zeroFree_of_growth ha hK hG hn) (by linarith))) (by linarith)
    (by norm_num)

end Landau
