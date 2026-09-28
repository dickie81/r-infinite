/-
# Landau's lemma, general form (round 193+): step L1, the 3-4-1 inequality for ζ'/ζ

Built against PrimeNumberTheoremAnd at commit 650d312. The proof of `three_four_one` is the
identity from PNT+'s `ZeroInequality` (StrongPNT.lean), extracted as a standalone lemma valid for
every `δ ∈ (0,1)` and every height `t`.
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

end Landau
