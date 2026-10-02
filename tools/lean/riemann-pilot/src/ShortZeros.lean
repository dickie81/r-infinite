import Mathlib
import ShortWeil
import WeilCount

/-! # Primes in short intervals, part 2: the zero sum and the prime window (round 235)

**The zero sum.** `lower_bound` (ShortWeil.lean) carries `Σ_ρ W(ρ)`, `W(ρ) = x^{|β−½|−½}/(1 + b|γ|)^k`.
Over the zero family of `Ξ` (`ρ = ½ ± iτ`) it is `2Σ_τ w(τ)`, `w(τ) = x^{|Im τ|−½}/(1 + b|Re τ|)^k`
(`hasSum_Wz`). It splits at height `T`:
* **the tail** `|Re τ| > T`: at most `4S₀/(b²(bT)^{k−2})` with `S₀ = Σ_τ |τ|^{−7/4}` (`tail_le`),
  from the zero count behind round 156's explicit formula (`summable_Xi_zeros_rpow`);
* **the head** `|Re τ| ≤ T`: if every such zero has `|Im τ| ≤ ½ − η` and at most `K·Q^{½−w}` of them
  have `|Im τ| ≥ w`, then the head is at most `M x^{1/(2M)} K (Q/x)^η` for every `M ≥ 1`, `Q ≤ x`
  (`head_le`, by slicing `|Im τ|` into `M` layers).

**The prime window.** `g_{J+1} ≤ (2b)^{k−1}` and vanishes off `|u| ≤ 2^{J+1}b`. So a lower bound on
`Σ Λ(n)n^{−½}g_{J+1}(log n − log x)` above `(2b)^{k−1}(xe^{−D})^{−½}·2√y log y`, `y = xe^D`, forces a
prime in `[xe^{−D}, xe^{D}]` (`exists_prime_of_weighted`), by Mathlib's `ψ − θ ≤ 2√y log y`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace ShortWeil

open Pilot1ca Pilot1bt

/-! ## The weight over the zeros of `Ξ` -/

/-- `w(τ) = x^{|Im τ| − ½}/(1 + b|Re τ|)^k`. -/
def wT (x b : ℝ) (k : ℕ) (τ : ℂ) : ℝ := x ^ (|τ.im| - 1 / 2) / (1 + b * |τ.re|) ^ k

theorem wT_nonneg {x b : ℝ} (hx : 0 < x) (hb : 0 ≤ b) (k : ℕ) (τ : ℂ) : 0 ≤ wT x b k τ := by
  unfold wT; positivity

theorem Wz_rhoXi (x b : ℝ) (k : ℕ) (p : Bool × ZeroIdx (sqF Xi)) :
    Wz x b k (rhoXi p) = wT x b k (tau p.2) := by
  unfold Wz wT rhoXi
  rcases p with ⟨_ | _, i⟩ <;> simp [abs_neg]

/-- `Σ_ρ W(ρ) = 2Σ_τ w(τ)`. -/
theorem hasSum_Wz {x b : ℝ} {k : ℕ} {S : ℝ} (hs : HasSum (fun i : ZeroIdx (sqF Xi) => wT x b k (tau i)) S) :
    HasSum (fun q => Wz x b k (zetaZeroFamily q)) (2 * S) := by
  have h2 : HasSum (fun p : Bool × ZeroIdx (sqF Xi) => Wz x b k (rhoXi p)) (S + S) := by
    have hsum : HasSum (fun s : ZeroIdx (sqF Xi) ⊕ ZeroIdx (sqF Xi) =>
        Sum.elim (fun i => wT x b k (tau i)) (fun i => wT x b k (tau i)) s) (S + S) :=
      HasSum.sum hs hs
    have := (Equiv.boolProdEquivSum (ZeroIdx (sqF Xi))).hasSum_iff.2 hsum
    convert this using 2 with p
    rcases p with ⟨_ | _, i⟩ <;> simp [Equiv.boolProdEquivSum, Wz_rhoXi]
  have := zetaEquiv.hasSum_iff.2 h2
  rw [two_mul]
  convert this using 2 with q
  simp [rhoXi_zetaEquiv]

theorem tau_ne_zero (i : ZeroIdx (sqF Xi)) : tau i ≠ 0 := fun h => Xi_zero_ne_zero (h ▸ Xi_tau i)

theorem norm_fst_eq (i : ZeroIdx (sqF Xi)) : ‖i.1‖ = ‖tau i‖ ^ 2 := by
  rw [← tau_sq i, norm_pow]

/-- `1/|τ|² ≤ |τ|^{−7/4}` for `|τ| ≥ 1`, in the form `S₀` sums. -/
theorem inv_sq_le_rpow {i : ZeroIdx (sqF Xi)} (h1 : 1 ≤ ‖tau i‖) :
    1 / ‖tau i‖ ^ 2 ≤ (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
  rw [norm_fst_eq, one_div]
  have hsq : 1 ≤ ‖tau i‖ ^ 2 := one_le_pow₀ h1
  apply inv_anti₀ (by positivity)
  calc (‖tau i‖ ^ 2) ^ (7 / 8 : ℝ) ≤ (‖tau i‖ ^ 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hsq (by norm_num)
    _ = _ := Real.rpow_one _

theorem one_le_rpow_inv {i : ZeroIdx (sqF Xi)} (h1 : ‖tau i‖ ≤ 1) : 1 ≤ (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
  have h0 : 0 < ‖i.1‖ := by rw [norm_fst_eq]; exact pow_pos (norm_pos_iff.2 (tau_ne_zero i)) 2
  have hle : ‖i.1‖ ≤ 1 := by rw [norm_fst_eq]; exact pow_le_one₀ (norm_nonneg _) h1
  rw [one_le_inv₀ (Real.rpow_pos_of_pos h0 _)]
  exact Real.rpow_le_one h0.le hle (by norm_num)

/-- `|Re τ| ≥ |τ| − ½` for a zero ordinate. -/
theorem norm_le_re (i : ZeroIdx (sqF Xi)) : ‖tau i‖ ≤ |(tau i).re| + 1 / 2 := by
  have him := tau_im i
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

theorem summable_wT {x b : ℝ} (hx : 1 ≤ x) (hb : 0 < b) {k : ℕ} (hk : 2 ≤ k) :
    Summable fun i : ZeroIdx (sqF Xi) => wT x b k (tau i) := by
  refine Summable.of_nonneg_of_le (fun i => wT_nonneg (by linarith) hb.le k _) (fun i => ?_)
    (summable_Xi_zeros_rpow.mul_left (1 + 16 / b ^ 2))
  set u := |(tau i).re|
  have hu : 0 ≤ u := abs_nonneg _
  have hq1 : 1 ≤ 1 + b * u := by nlinarith
  have hx1 : x ^ (|(tau i).im| - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [tau_im i])
  have hw : wT x b k (tau i) ≤ 1 / (1 + b * u) ^ 2 := by
    unfold wT
    calc x ^ (|(tau i).im| - 1 / 2) / (1 + b * u) ^ k ≤ 1 / (1 + b * u) ^ k :=
          div_le_div_of_nonneg_right hx1 (by positivity)
      _ ≤ 1 / (1 + b * u) ^ 2 := one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hq1 hk)
  have hS0 : 0 ≤ (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by positivity
  refine hw.trans ?_
  rcases le_or_gt ‖tau i‖ 1 with h1 | h1
  · have := one_le_rpow_inv h1
    have : 1 / (1 + b * u) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg b)]
  · have hr := inv_sq_le_rpow h1.le
    have hnu := norm_le_re i
    have hu2 : ‖tau i‖ / 4 ≤ u := by linarith
    have hn0 : 0 < ‖tau i‖ := by linarith
    have hstep : 1 / (1 + b * u) ^ 2 ≤ 16 / b ^ 2 * (1 / ‖tau i‖ ^ 2) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have : b * ‖tau i‖ ≤ 4 * (1 + b * u) := by nlinarith
      nlinarith [mul_pos hb hn0]
    calc 1 / (1 + b * u) ^ 2 ≤ 16 / b ^ 2 * (1 / ‖tau i‖ ^ 2) := hstep
      _ ≤ 16 / b ^ 2 * (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ (1 + 16 / b ^ 2) * (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by nlinarith

/-- `S₀ = Σ_τ |τ|^{−7/4}`. -/
def S0 : ℝ := ∑' i : ZeroIdx (sqF Xi), (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹

/-- **The tail**: the zeros with `|Re τ| > T` carry at most `4S₀/(b²(bT)^{k−2})`. -/
theorem tail_le {x b T : ℝ} (hx : 1 ≤ x) (hb : 0 < b) (hT : 1 ≤ T) {k : ℕ} (hk : 2 ≤ k) :
    ∑' i : ZeroIdx (sqF Xi), (if |(tau i).re| ≤ T then 0 else wT x b k (tau i))
      ≤ 4 * S0 / (b ^ 2 * (b * T) ^ (k - 2)) := by
  have hpt : ∀ i : ZeroIdx (sqF Xi), (if |(tau i).re| ≤ T then 0 else wT x b k (tau i))
      ≤ 4 / (b ^ 2 * (b * T) ^ (k - 2)) * (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
    intro i
    split_ifs with h
    · positivity
    push Not at h
    set u := |(tau i).re|
    have hbT : 0 < b * T := mul_pos hb (by linarith)
    have hbu : b * T ≤ b * u := by nlinarith
    have hx1 : x ^ (|(tau i).im| - 1 / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [tau_im i])
    have hn1 : 1 ≤ ‖tau i‖ := by
      have := Complex.abs_re_le_norm (tau i); linarith
    have hnu : ‖tau i‖ ≤ 2 * u := by have := norm_le_re i; linarith
    have hr := inv_sq_le_rpow hn1
    have hw : wT x b k (tau i) ≤ 1 / (b * u) ^ k := by
      unfold wT
      calc x ^ (|(tau i).im| - 1 / 2) / (1 + b * u) ^ k ≤ 1 / (1 + b * u) ^ k :=
            div_le_div_of_nonneg_right hx1 (by positivity)
        _ ≤ 1 / (b * u) ^ k := one_div_le_one_div_of_le (pow_pos (hbT.trans_le hbu) k)
            (pow_le_pow_left₀ (by positivity) (by linarith) k)
    have hsplit : (b * u) ^ k = (b * u) ^ (k - 2) * (b * u) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hk2 : (b * T) ^ (k - 2) ≤ (b * u) ^ (k - 2) := pow_le_pow_left₀ hbT.le hbu _
    have hu4 : ‖tau i‖ ^ 2 ≤ 4 * u ^ 2 := by nlinarith [norm_nonneg (tau i)]
    have hn0 : 0 < ‖tau i‖ := by linarith
    calc wT x b k (tau i) ≤ 1 / (b * u) ^ k := hw
      _ = 1 / ((b * u) ^ (k - 2) * (b ^ 2 * u ^ 2)) := by rw [hsplit, mul_pow b u 2]
      _ ≤ 1 / ((b * T) ^ (k - 2) * (b ^ 2 * (‖tau i‖ ^ 2 / 4))) := by
          apply one_div_le_one_div_of_le (by positivity)
          apply mul_le_mul hk2 _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 / (b ^ 2 * (b * T) ^ (k - 2)) * (1 / ‖tau i‖ ^ 2) := by
          field_simp
      _ ≤ 4 / (b ^ 2 * (b * T) ^ (k - 2)) * (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hr (by positivity)
  have hsum := summable_Xi_zeros_rpow.mul_left (4 / (b ^ 2 * (b * T) ^ (k - 2)))
  have hs2 : Summable fun i : ZeroIdx (sqF Xi) => (if |(tau i).re| ≤ T then 0 else wT x b k (tau i)) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs <;> [exact le_rfl; exact wT_nonneg (by linarith) hb.le k _])
      hpt hsum
  calc _ ≤ ∑' i : ZeroIdx (sqF Xi), 4 / (b ^ 2 * (b * T) ^ (k - 2)) * (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ :=
        hs2.tsum_le_tsum hpt hsum
    _ = 4 * S0 / (b ^ 2 * (b * T) ^ (k - 2)) := by rw [tsum_mul_left, S0]; ring

/-- **The head**, by slicing `|Im τ|` into `M` layers of width `1/(2M)`. -/
theorem head_le {ι : Type*} (S : Finset ι) (v : ι → ℝ) (hv0 : ∀ i ∈ S, 0 ≤ v i)
    {x Q K η : ℝ} (hx : 1 ≤ x) (hQ : 0 < Q) (hQx : Q ≤ x) (hK : 0 ≤ K)
    (hv1 : ∀ i ∈ S, v i < 1 / 2) (hfree : ∀ i ∈ S, v i ≤ 1 / 2 - η) {M : ℕ} (hM : 1 ≤ M)
    (hden : ∀ j < M, ((S.filter fun i => (j : ℝ) / (2 * M) ≤ v i).card : ℝ)
      ≤ K * Q ^ (1 / 2 - (j : ℝ) / (2 * M))) :
    ∑ i ∈ S, x ^ (v i - 1 / 2) ≤ M * x ^ (1 / (2 * M : ℝ)) * K * (Q / x) ^ η := by
  have hx0 : 0 < x := by linarith
  have hM0 : (0 : ℝ) < 2 * M := by positivity
  set jj : ι → ℕ := fun i => ⌊2 * M * v i⌋₊ with hjj
  have hj_lt : ∀ i ∈ S, jj i < M := by
    intro i hi
    have h1 : 2 * (M : ℝ) * v i < M := by
      have := hv1 i hi
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith
    exact (Nat.floor_lt (by have := hv0 i hi; positivity)).2 h1
  have hj_le : ∀ i ∈ S, (jj i : ℝ) / (2 * M) ≤ v i := by
    intro i hi
    rw [div_le_iff₀ hM0, mul_comm]
    exact Nat.floor_le (by have := hv0 i hi; positivity)
  have hj_gt : ∀ i ∈ S, v i < ((jj i : ℝ) + 1) / (2 * M) := by
    intro i hi
    rw [lt_div_iff₀ hM0, mul_comm]
    exact Nat.lt_floor_add_one _
  -- each term against its layer
  have hterm : ∀ i ∈ S, x ^ (v i - 1 / 2)
      ≤ x ^ (1 / (2 * M : ℝ)) * x ^ ((jj i : ℝ) / (2 * M) - 1 / 2) := by
    intro i hi
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx
    have := hj_gt i hi
    have e : ((jj i : ℝ) + 1) / (2 * M) = (jj i : ℝ) / (2 * M) + 1 / (2 * M) := by ring
    linarith
  have hmaps : ∀ i ∈ S, jj i ∈ Finset.range M := fun i hi => Finset.mem_range.2 (hj_lt i hi)
  calc ∑ i ∈ S, x ^ (v i - 1 / 2)
      ≤ ∑ i ∈ S, x ^ (1 / (2 * M : ℝ)) * x ^ ((jj i : ℝ) / (2 * M) - 1 / 2) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range M, ∑ i ∈ S.filter (fun i => jj i = j),
          x ^ (1 / (2 * M : ℝ)) * x ^ ((jj i : ℝ) / (2 * M) - 1 / 2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ Finset.range M, ((S.filter (fun i => jj i = j)).card : ℝ)
          * (x ^ (1 / (2 * M : ℝ)) * x ^ ((j : ℝ) / (2 * M) - 1 / 2)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.1 hi).2]; simp
    _ ≤ ∑ _j ∈ Finset.range M, x ^ (1 / (2 * M : ℝ)) * K * (Q / x) ^ η := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjM := Finset.mem_range.1 hj
        rcases (S.filter (fun i => jj i = j)).eq_empty_or_nonempty with he | ⟨i, hi⟩
        · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]; positivity
        obtain ⟨hiS, hij⟩ := Finset.mem_filter.1 hi
        have hwj : (j : ℝ) / (2 * M) ≤ 1 / 2 - η := by
          rw [← hij]; exact (hj_le i hiS).trans (hfree i hiS)
        have hsub : S.filter (fun i => jj i = j) ⊆ S.filter (fun i => (j : ℝ) / (2 * M) ≤ v i) := by
          intro i' hi'
          obtain ⟨hi'S, hi'j⟩ := Finset.mem_filter.1 hi'
          exact Finset.mem_filter.2 ⟨hi'S, hi'j ▸ hj_le i' hi'S⟩
        have hcard : ((S.filter (fun i => jj i = j)).card : ℝ) ≤ K * Q ^ (1 / 2 - (j : ℝ) / (2 * M)) :=
          (Nat.cast_le.2 (Finset.card_le_card hsub)).trans (hden j hjM)
        set y := 1 / 2 - (j : ℝ) / (2 * M) with hy
        have hyη : η ≤ y := by linarith
        have hQx1 : Q / x ≤ 1 := (div_le_one hx0).2 hQx
        have hpow : Q ^ y * x ^ (-y) = (Q / x) ^ y := by
          rw [Real.div_rpow hQ.le hx0.le, Real.rpow_neg hx0.le, div_eq_mul_inv]
        have hmono : (Q / x) ^ y ≤ (Q / x) ^ η :=
          Real.rpow_le_rpow_of_exponent_ge (by positivity) hQx1 hyη
        have e : (j : ℝ) / (2 * M) - 1 / 2 = -y := by rw [hy]; ring
        rw [e]
        calc ((S.filter (fun i => jj i = j)).card : ℝ) * (x ^ (1 / (2 * M : ℝ)) * x ^ (-y))
            ≤ K * Q ^ y * (x ^ (1 / (2 * M : ℝ)) * x ^ (-y)) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = x ^ (1 / (2 * M : ℝ)) * K * (Q ^ y * x ^ (-y)) := by ring
          _ ≤ x ^ (1 / (2 * M : ℝ)) * K * (Q / x) ^ η := by
              rw [hpow]; exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = M * x ^ (1 / (2 * M : ℝ)) * K * (Q / x) ^ η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ## The prime window -/

theorem integral_gI {b : ℝ} (hb : 0 < b) (j : ℕ) : ∫ u, gI b j u = (2 * b) ^ (2 ^ j) := by
  have hE := gI_esupp hb j
  have h1 := ghatC_gI hb 0 j
  rw [ghatC_eq_integral (by positivity) hE.supp, ghatC_bx b hb.le] at h1
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one, intervalIntegral.integral_const] at h1
  rw [integral_complex_ofReal] at h1
  have h2 : ((∫ u, gI b j u : ℝ) : ℂ) = (((2 * b) ^ (2 ^ j) : ℝ) : ℂ) := by
    rw [h1, Complex.real_smul]; push_cast; ring
  exact_mod_cast h2

/-- `g_j ≤ (2b)^{2^j − 1}`. -/
theorem gI_le {b : ℝ} (hb : 0 < b) : ∀ (j : ℕ) (u : ℝ), gI b j u ≤ (2 * b) ^ (2 ^ j - 1)
  | 0, u => by
    simp only [gI, pow_zero, Nat.sub_self]
    rw [bx_apply]; split_ifs <;> norm_num
  | j + 1, u => by
    have hE := gI_esupp hb j
    change ∫ t, gI b j t * gI b j (t + u) ≤ _
    have hmono : ∫ t, gI b j t * gI b j (t + u) ≤ ∫ t, gI b j t * (2 * b) ^ (2 ^ j - 1) :=
      integral_mono (integrable_mul_shift hE.memL2 u) (hE.integrable.mul_const _)
        fun t => mul_le_mul_of_nonneg_left (gI_le hb j (t + u)) (gI_nonneg b j t)
    rw [integral_mul_const, integral_gI hb j, ← pow_add] at hmono
    have e : 2 ^ j + (2 ^ j - 1) = 2 ^ (j + 1) - 1 := by
      have := Nat.one_le_two_pow (n := j); rw [pow_succ]; omega
    rwa [e] at hmono

/-- **The weighted sum is a window sum**: with `D = 2^{J+1}b`,
`Σ Λ(n)n^{−½}g_{J+1}(log n − log x) ≤ (2b)^{k−1}(xe^{−D})^{−½} Σ_{xe^{−D} ≤ n ≤ xe^D} Λ(n)`. -/
theorem weighted_le_window {b : ℝ} (hb : 0 < b) (J : ℕ) {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - Real.log x)
      ≤ (2 * b) ^ (2 ^ (J + 1) - 1) / Real.sqrt (x * Real.exp (-(2 ^ (J + 1) * b)))
        * ∑ n ∈ Finset.Icc ⌈x * Real.exp (-(2 ^ (J + 1) * b))⌉₊ ⌊x * Real.exp (2 ^ (J + 1) * b)⌋₊,
          ArithmeticFunction.vonMangoldt n := by
  set D := 2 ^ (J + 1) * b with hD
  set lo := x * Real.exp (-D) with hlo
  set I := Finset.Icc ⌈lo⌉₊ ⌊x * Real.exp D⌋₊ with hI
  set c := (2 * b) ^ (2 ^ (J + 1) - 1) / Real.sqrt lo with hc
  have hE := gI_esupp hb (J + 1)
  have hlo0 : 0 < lo := by positivity
  have hpt : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - Real.log x)
      ≤ c * (if n ∈ I then ArithmeticFunction.vonMangoldt n else 0) := by
    intro n
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    by_cases hg : gI b (J + 1) (Real.log n - Real.log x) = 0
    · rw [hg, mul_zero]; split_ifs <;> [positivity; simp]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hsupp : |Real.log n - Real.log x| ≤ D := by
      by_contra h; push Not at h; exact hg (hE.supp _ h)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlow : lo ≤ n := by
      rw [hlo, ← Real.exp_log hx, ← Real.exp_add, ← Real.exp_log hn0]
      exact Real.exp_le_exp.2 (by linarith [(abs_le.1 hsupp).1])
    have hhigh : (n : ℝ) ≤ x * Real.exp D := by
      rw [← Real.exp_log hx, ← Real.exp_add, ← Real.exp_log hn0]
      exact Real.exp_le_exp.2 (by linarith [(abs_le.1 hsupp).2])
    have hmem : n ∈ I := Finset.mem_Icc.2 ⟨Nat.ceil_le.2 hlow, Nat.le_floor hhigh⟩
    simp only [hmem, ↓reduceIte]
    have hsq : 1 / Real.sqrt n ≤ 1 / Real.sqrt lo :=
      one_div_le_one_div_of_le (Real.sqrt_pos.2 hlo0) (Real.sqrt_le_sqrt hlow)
    have hgle := gI_le hb (J + 1) (Real.log n - Real.log x)
    have hg0 := gI_nonneg b (J + 1) (Real.log n - Real.log x)
    rw [hc, div_eq_mul_one_div ((2 * b) ^ _), div_eq_mul_one_div (ArithmeticFunction.vonMangoldt n)]
    have h1 : 0 ≤ 1 / Real.sqrt (n : ℝ) := by positivity
    calc ArithmeticFunction.vonMangoldt n * (1 / √↑n) * gI b (J + 1) (Real.log ↑n - Real.log x)
        ≤ ArithmeticFunction.vonMangoldt n * (1 / √lo) * (2 * b) ^ (2 ^ (J + 1) - 1) := by
          gcongr
      _ = _ := by ring
  have hfin : Summable fun n : ℕ => c * (if n ∈ I then ArithmeticFunction.vonMangoldt n else 0) :=
    summable_of_ne_finset_zero (s := I) fun n hn => by simp [hn]
  have hl : Summable fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - Real.log x) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.sqrt_nonneg _)) (gI_nonneg b _ _)) hpt hfin
  refine (hl.tsum_le_tsum hpt hfin).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_eq_sum (s := I) (fun n hn => by simp [hn]), Finset.sum_ite_mem,
    Finset.inter_self]

/-- **A window with more `Λ`-mass than `2√c log c` holds a prime** (Mathlib's `|ψ − θ| ≤ 2√x log x`). -/
theorem exists_prime_of_window {a c : ℕ} (ha : 1 ≤ a)
    (h : 2 * Real.sqrt c * Real.log c < ∑ n ∈ Finset.Icc a c, ArithmeticFunction.vonMangoldt n) :
    ∃ p, p.Prime ∧ a ≤ p ∧ p ≤ c := by
  by_contra hno
  push Not at hno
  have hc : 1 ≤ c := by
    by_contra hc; push Not at hc
    have : Finset.Icc a c = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty] at h
    have : c = 0 := by omega
    subst this; simp at h
  set f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n - if n.Prime then Real.log n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n; simp only [hf]
    split_ifs with hp
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    · rw [sub_zero]; exact ArithmeticFunction.vonMangoldt_nonneg
  have e1 : ∑ n ∈ Finset.Icc a c, ArithmeticFunction.vonMangoldt n = ∑ n ∈ Finset.Icc a c, f n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have : ¬ n.Prime := fun hp => absurd h2 (not_le.2 (hno n hp h1))
    simp [hf, this]
  have hsub : Finset.Icc a c ⊆ Finset.Ioc 0 c := fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn; exact Finset.mem_Ioc.2 ⟨by omega, h2⟩
  have e2 : ∑ n ∈ Finset.Ioc 0 c, f n = Chebyshev.psi c - Chebyshev.theta c := by
    simp only [hf, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast, Finset.sum_sub_distrib,
      Finset.sum_filter]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hf0 n
  have hpt := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (c : ℝ)) (by exact_mod_cast hc)
  rw [e1] at h
  rw [e2] at hle
  linarith [le_abs_self (Chebyshev.psi c - Chebyshev.theta c)]

end ShortWeil

#print axioms ShortWeil.hasSum_Wz
#print axioms ShortWeil.summable_wT
#print axioms ShortWeil.tail_le
#print axioms ShortWeil.head_le
#print axioms ShortWeil.weighted_le_window
#print axioms ShortWeil.exists_prime_of_window
