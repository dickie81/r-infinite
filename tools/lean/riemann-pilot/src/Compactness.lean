import Mathlib
import Existence

/-! # Existence of the ground state, stage 2: compactness

A sequence of probes at half-support `a > 0` with bounded norm and bounded archimedean energy has a
subsequence converging in `L²`:

* the Fourier coefficients on `[−2a, 2a]` are bounded, so a subsequence converges coordinatewise
  (Tychonoff on `ℤ → ℂ`, first countable);
* the tails `Σ_{|n|≥N}|c_n|²` are uniformly small (`tail_le`), so by Parseval the subsequence is
  Cauchy in `L²`;
* `L²` is complete.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## `L²` completeness in terms of `normSq` -/

theorem L2_norm_sq (F : Lp ℝ 2 (volume : Measure ℝ)) : ‖F‖ ^ 2 = ∫ a, (F a) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1; funext a
  simp [sq]

/-- **A `normSq`-Cauchy sequence of `L²` functions has an `L²` limit.** -/
theorem exists_limit_of_cauchy {u : ℕ → ℝ → ℝ} (hu : ∀ j, MemLp (u j) 2 volume)
    (hc : ∀ ε > 0, ∃ M, ∀ i ≥ M, ∀ j ≥ M, normSq (fun t => u i t - u j t) < ε) :
    ∃ G : ℝ → ℝ, MemLp G 2 volume ∧
      Tendsto (fun j => normSq (fun t => u j t - G t)) atTop (𝓝 0) := by
  set U : ℕ → Lp ℝ 2 (volume : Measure ℝ) := fun j => (hu j).toLp (u j) with hU
  have hdist : ∀ i j, dist (U i) (U j) ^ 2 = normSq (fun t => u i t - u j t) := by
    intro i j
    rw [dist_eq_norm, hU, ← MemLp.toLp_sub, L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp ((hu i).sub (hu j))] with t ht
    rw [ht]; rfl
  have hcs : CauchySeq U := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hc (ε ^ 2) (by positivity)
    refine ⟨M, fun i hi j hj => ?_⟩
    have := hM i hi j hj
    rw [← hdist] at this
    exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨F, Lp.memLp F, ?_⟩
  have hn : Tendsto (fun j => ‖U j - F‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hF).pow 2
    simpa using this
  refine hn.congr fun j => ?_
  rw [L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (U j) F, MemLp.coeFn_toLp (hu j)] with t h1 h2
  rw [h1, Pi.sub_apply, h2]

/-! ## Coefficients -/

theorem coef_sq_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (n : ℤ) :
    ‖cf a g n‖ ^ 2 ≤ (4 * a)⁻¹ * normSq g :=
  le_hasSum (hasSum_cf_sq ha (by linarith) hp.memL2 hp.supp) n fun _ _ => sq_nonneg _

/-- Parseval for the difference of two probes. -/
theorem hasSum_sub {a : ℝ} (ha : 0 < a) {g₁ g₂ : ℝ → ℝ} (hp₁ : Probe a g₁) (hp₂ : Probe a g₂) :
    HasSum (fun n => ‖cf a g₁ n - cf a g₂ n‖ ^ 2)
      ((4 * a)⁻¹ * normSq (fun t => g₁ t - g₂ t)) := by
  have h := hasSum_cf_sq ha (by linarith : a < 2 * a) (hp₁.memL2.sub hp₂.memL2)
    (g := fun t => g₁ t - g₂ t) (fun u hu => by simp [hp₁.supp u hu, hp₂.supp u hu])
  simp_rw [cf_sub (memLp_intervalIntegrable hp₁.memL2 _ _)
    (memLp_intervalIntegrable hp₂.memL2 _ _)] at h
  exact h

theorem summable_coef {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) :
    Summable fun n => ‖cf a g n‖ ^ 2 :=
  (hasSum_cf_sq ha (by linarith) hp.memL2 hp.supp).summable

theorem archE_nonneg {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) : 0 ≤ archE g :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu => archIntegrand_nonneg hp.memL2 hu

/-! ## The frequency cut -/

/-- For every `τ > 0` there is a cut `N` at which `tail_le` applies with bound `≤ τ·(E + 1)`. -/
theorem exists_cut {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, 1 ≤ 2 * π * N / (4 * a) * b ∧ 0 < 2 * Real.log (2 * π * N / (4 * a) * b) - 6 ∧
      1 / (a * (2 * Real.log (2 * π * N / (4 * a) * b) - 6)) ≤ τ := by
  have hc : 0 < 2 * π / (4 * a) * b := by positivity
  have hlin : Tendsto (fun N : ℕ => 2 * π * N / (4 * a) * b) atTop atTop := by
    have : (fun N : ℕ => 2 * π * N / (4 * a) * b) = fun N : ℕ => (2 * π / (4 * a) * b) * N := by
      funext N; ring
    rw [this]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hL : Tendsto (fun N : ℕ => 2 * Real.log (2 * π * N / (4 * a) * b) - 6) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((Real.tendsto_log_atTop.comp hlin).const_mul_atTop two_pos)
  obtain ⟨N, hN⟩ := ((hlin.eventually_ge_atTop 1).and
    (hL.eventually_ge_atTop (1 / (a * τ) + 1))).exists
  have hpos : 0 < 1 / (a * τ) := by positivity
  have hLpos : 0 < 2 * Real.log (2 * π * N / (4 * a) * b) - 6 := by linarith [hN.2]
  refine ⟨N, hN.1, hLpos, ?_⟩
  rw [div_le_iff₀ (mul_pos ha hLpos)]
  have h1 : 1 / (a * τ) + 1 ≤ 2 * Real.log (2 * π * N / (4 * a) * b) - 6 := hN.2
  have h2 : 1 / (a * τ) * (a * τ) = 1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ a * τ)]

/-! ## Compactness -/

/-- **Bounded-energy probes are precompact in `L²`.** -/
theorem exists_convergent_subseq {a : ℝ} (ha : 0 < a) {h : ℕ → ℝ → ℝ}
    (hp : ∀ j, Probe a (h j)) {B C : ℝ} (hB : ∀ j, normSq (h j) ≤ B)
    (hC : ∀ j, archE (h j) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℝ → ℝ, MemLp G 2 volume ∧
      Tendsto (fun j => normSq (fun t => h (φ j) t - G t)) atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := (archE_nonneg (hp 0)).trans (hC 0)
  -- bounded coefficients
  set R := Real.sqrt ((4 * a)⁻¹ * B) with hR
  have hv : ∀ j, (fun n => cf a (h j) n) ∈ Set.pi univ fun _ : ℤ => Metric.closedBall (0 : ℂ) R := by
    intro j n _
    rw [Metric.mem_closedBall, dist_zero_right, hR]
    apply Real.le_sqrt_of_sq_le
    exact (coef_sq_le ha (hp j) n).trans (by gcongr; exact hB j)
  obtain ⟨w, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ : ℤ => isCompact_closedBall (0 : ℂ) R).tendsto_subseq hv
  have hco : ∀ n, Tendsto (fun j => cf a (h (φ j)) n) atTop (𝓝 (w n)) :=
    fun n => (tendsto_pi_nhds.1 hlim) n
  refine ⟨φ, hφ, ?_⟩
  set u : ℕ → ℝ → ℝ := fun j => h (φ j) with hu
  apply exists_limit_of_cauchy (fun j => (hp (φ j)).memL2)
  intro ε hε
  set b := min 1 (a / 2) with hb
  have hb0 : 0 < b := lt_min one_pos (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hba : b < a := (min_le_right _ _).trans_lt (by linarith)
  -- the cut
  obtain ⟨N, hN1, hNL, hNτ⟩ := exists_cut ha hb0 (τ := ε / (64 * a * (C + 1))) (by positivity)
  set L := 2 * Real.log (2 * π * N / (4 * a) * b) - 6 with hLdef
  have htail : ∀ j, (∑' n : ℤ, if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u j) n‖ ^ 2 else 0)
      ≤ ε / (64 * a) := by
    intro j
    refine (tail_le ha (hp (φ j)) hb0 hb1 hba hN1 hNL).trans ?_
    rw [div_eq_mul_one_div]
    calc archE (h (φ j)) * (1 / (a * L)) ≤ (C + 1) * (ε / (64 * a * (C + 1))) :=
          mul_le_mul (by linarith [hC (φ j)]) hNτ (one_div_pos.2 (mul_pos ha hNL)).le
            (by linarith)
      _ = ε / (64 * a) := by field_simp
  -- the finite part
  set F := Finset.Ioo (-(N : ℤ)) N with hF
  have hA : Tendsto (fun j => ∑ n ∈ F, ‖cf a (u j) n - w n‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum F fun n _ =>
      (((hco n).sub_const (w n)).norm.pow 2)
    simpa using this
  obtain ⟨M, hM⟩ := (hA.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / (32 * a)))).exists_forall_of_atTop
  refine ⟨M, fun i hi j hj => ?_⟩
  have hsum := hasSum_sub ha (hp (φ i)) (hp (φ j))
  have hsi := summable_coef ha (hp (φ i))
  have hsj := summable_coef ha (hp (φ j))
  set d : ℤ → ℝ := fun n => ‖cf a (u i) n - cf a (u j) n‖ ^ 2 with hd
  -- pointwise: `d_n ≤ [n ∈ F](2|c_i − w|² + 2|c_j − w|²) + [|n| ≥ N](2|c_i|² + 2|c_j|²)`
  set P : ℤ → ℝ := fun n => if n ∈ F then
      2 * ‖cf a (u i) n - w n‖ ^ 2 + 2 * ‖cf a (u j) n - w n‖ ^ 2 else 0 with hP
  set Q : ℤ → ℝ := fun n =>
      2 * (if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u i) n‖ ^ 2 else 0)
      + 2 * (if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u j) n‖ ^ 2 else 0) with hQ
  have hsq : ∀ x y : ℂ, ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    intro x y
    have := norm_sub_le x y
    nlinarith [norm_nonneg (x - y), sq_nonneg (‖x‖ - ‖y‖)]
  have hpt : ∀ n, d n ≤ P n + Q n := by
    intro n
    by_cases hn : n ∈ F
    · have hnN : ¬ (N : ℝ) ≤ |(n : ℝ)| := by
        rw [hF, Finset.mem_Ioo] at hn
        rw [not_le, ← Int.cast_abs]
        exact_mod_cast abs_lt.2 hn
      simp only [hd, hP, hQ, hn, hnN, ite_true, ite_false, mul_zero, add_zero]
      have := hsq (cf a (u i) n - w n) (cf a (u j) n - w n)
      rwa [sub_sub_sub_cancel_right] at this
    · have hnN : (N : ℝ) ≤ |(n : ℝ)| := by
        rw [hF, Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hn
        rw [← Int.cast_abs]
        have : (N : ℤ) ≤ |n| := by
          rcases hn with hn | hn
          · exact le_trans (by omega) (neg_le_abs n)
          · exact le_trans hn (le_abs_self n)
        exact_mod_cast this
      simp only [hd, hP, hQ, hn, hnN, ite_true, ite_false, zero_add]
      exact hsq _ _
  have hPs : HasSum P (∑ n ∈ F, (2 * ‖cf a (u i) n - w n‖ ^ 2 + 2 * ‖cf a (u j) n - w n‖ ^ 2)) := by
    have : HasSum P (∑ n ∈ F, P n) :=
      hasSum_sum_of_ne_finset_zero (f := P) (s := F) fun n hn => by simp [hP, hn]
    convert this using 1
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [hP, hn]
  have hti : Summable fun n : ℤ => if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u i) n‖ ^ 2 else 0 :=
    hsi.of_nonneg_of_le (fun n => by split_ifs <;> positivity) fun n => by
      split_ifs <;> first | exact le_rfl | positivity
  have htj : Summable fun n : ℤ => if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u j) n‖ ^ 2 else 0 :=
    hsj.of_nonneg_of_le (fun n => by split_ifs <;> positivity) fun n => by
      split_ifs <;> first | exact le_rfl | positivity
  have hQs : HasSum Q (2 * (∑' n : ℤ, if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u i) n‖ ^ 2 else 0)
      + 2 * (∑' n : ℤ, if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u j) n‖ ^ 2 else 0)) :=
    (hti.hasSum.mul_left 2).add (htj.hasSum.mul_left 2)
  have hle := hasSum_le hpt hsum (hPs.add hQs)
  have hAi : ∑ n ∈ F, ‖cf a (u i) n - w n‖ ^ 2 < ε / (32 * a) := hM i hi
  have hAj : ∑ n ∈ F, ‖cf a (u j) n - w n‖ ^ 2 < ε / (32 * a) := hM j hj
  have hfin : (∑ n ∈ F, (2 * ‖cf a (u i) n - w n‖ ^ 2 + 2 * ‖cf a (u j) n - w n‖ ^ 2))
      = 2 * (∑ n ∈ F, ‖cf a (u i) n - w n‖ ^ 2) + 2 * ∑ n ∈ F, ‖cf a (u j) n - w n‖ ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hfin] at hle
  have hti' := htail i
  have htj' := htail j
  have h4a : 0 < 4 * a := by positivity
  have key : (4 * a)⁻¹ * normSq (fun t => u i t - u j t) < ε / (4 * a) := by
    calc (4 * a)⁻¹ * normSq (fun t => u i t - u j t)
        ≤ 2 * (∑ n ∈ F, ‖cf a (u i) n - w n‖ ^ 2) + 2 * (∑ n ∈ F, ‖cf a (u j) n - w n‖ ^ 2)
          + (2 * (∑' n : ℤ, if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u i) n‖ ^ 2 else 0)
          + 2 * (∑' n : ℤ, if (N : ℝ) ≤ |(n : ℝ)| then ‖cf a (u j) n‖ ^ 2 else 0)) := hle
      _ < 2 * (ε / (32 * a)) + 2 * (ε / (32 * a)) + (2 * (ε / (64 * a)) + 2 * (ε / (64 * a))) := by
          linarith
      _ ≤ ε / (4 * a) := by
          have e : 2 * (ε / (32 * a)) + 2 * (ε / (32 * a)) + (2 * (ε / (64 * a)) + 2 * (ε / (64 * a)))
              = 3 / 4 * (ε / (4 * a)) := by field_simp; ring
          have : 0 < ε / (4 * a) := by positivity
          rw [e]; linarith
  rw [inv_mul_eq_div, div_lt_div_iff_of_pos_right h4a] at key
  exact key

end Pilot1ca

#print axioms Pilot1ca.exists_limit_of_cauchy
#print axioms Pilot1ca.exists_cut
#print axioms Pilot1ca.exists_convergent_subseq
