import Mathlib
import ShortZeros

/-! # Primes in short intervals, part 3: assembly (round 235)

`short_primes_of_density`: a zero-density bound `N(σ, T) ≪ T^{A(1−σ)}(log T)^B` (`DensityXi`, in the
variable `w = σ − ½` over the zeros `τ` of `Ξ`) and a zero-free region of width `(log T)^{−α}`,
`α < 1` (`ZeroFreeXi`), give a prime in `(y, y + y^θ]` for every `θ > max(½, 1 − 1/A)` and all
large `y`. The parameters are `b = x^{θ'−1}` (the probe scale), `T = x^{1−θ'+ε}` (the height split)
and `k = 2^{J+1}` (the decay order), with `θ'` between `max(½, 1 − 1/A)` and `θ`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace ShortWeil

open Pilot1ca Pilot1bt

/-! ## The hypotheses -/

/-- `#{τ : |Re τ| ≤ T, |Im τ| ≥ w}` over the zeros of `Ξ` (with multiplicity): the zeros
`ρ = ½ ± iτ` of `ζ` with `|γ| ≤ T` and `β ≥ ½ + w`, counted once per pair. -/
def NX (w T : ℝ) : ℕ := Set.ncard {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T ∧ w ≤ |(tau i).im|}

/-- **Zero density** `N(½ + w, T) ≤ C T^{A(½ − w)}(log T)^B`. -/
def DensityXi (A B : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ w : ℝ, 0 ≤ w → w ≤ 1 / 2 →
    (NX w T : ℝ) ≤ C * T ^ (A * (1 / 2 - w)) * Real.log T ^ B

/-- **A zero-free region of width `A_z/(log T)^α`.** -/
def ZeroFreeXi (α : ℝ) : Prop :=
  ∃ Az T₀ : ℝ, 0 < Az ∧ ∀ T : ℝ, T₀ ≤ T → ∀ i : ZeroIdx (sqF Xi),
    |(tau i).re| ≤ T → |(tau i).im| ≤ 1 / 2 - Az / Real.log T ^ α

theorem finite_re_le (T : ℝ) : {i : ZeroIdx (sqF Xi) | |(tau i).re| ≤ T}.Finite := by
  set R := |T| + 1 with hR
  set ε₀ : ℝ := ((R ^ 2) ^ (7 / 8 : ℝ))⁻¹ with hε₀
  have hR0 : 0 < R := by positivity
  have hε : 0 < ε₀ := by positivity
  have hT : ∀ i : ZeroIdx (sqF Xi), |(tau i).re| ≤ T → ε₀ ≤ (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
    intro i hi
    have hn := norm_le_re i
    have h0 : 0 < ‖i.1‖ := by rw [norm_fst_eq]; exact pow_pos (norm_pos_iff.2 (tau_ne_zero i)) 2
    have hle : ‖i.1‖ ≤ R ^ 2 := by
      rw [norm_fst_eq]
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [le_abs_self T]) 2
    exact inv_anti₀ (Real.rpow_pos_of_pos h0 _) (Real.rpow_le_rpow h0.le hle (by norm_num))
  have hev := summable_Xi_zeros_rpow.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)
  rw [Filter.eventually_cofinite] at hev
  exact hev.subset fun i hi => not_lt.2 (hT i hi)

theorem NX_eq_card (w T : ℝ) :
    (NX w T : ℝ) = (((finite_re_le T).toFinset.filter fun i => w ≤ |(tau i).im|).card : ℝ) := by
  unfold NX
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i; simp

/-! ## The zero sum at a fixed `x` -/

/-- **The zero sum**: head (density and zero-free region) plus tail. -/
theorem wT_sum_le {x b T Q K η : ℝ} {k M : ℕ} (hx : 1 ≤ x) (hb : 0 < b) (hT : 1 ≤ T) (hk : 2 ≤ k)
    (hM : 1 ≤ M) (hQ : 0 < Q) (hQx : Q ≤ x) (hK : 0 ≤ K)
    (hfree : ∀ i : ZeroIdx (sqF Xi), |(tau i).re| ≤ T → |(tau i).im| ≤ 1 / 2 - η)
    (hden : ∀ w : ℝ, 0 ≤ w → w < 1 / 2 → (NX w T : ℝ) ≤ K * Q ^ (1 / 2 - w)) :
    ∑' i : ZeroIdx (sqF Xi), wT x b k (tau i)
      ≤ M * x ^ (1 / (2 * M : ℝ)) * K * (Q / x) ^ η + 4 * S0 / (b ^ 2 * (b * T) ^ (k - 2)) := by
  have hx0 : 0 < x := by linarith
  set S := (finite_re_le T).toFinset with hS
  set h : ZeroIdx (sqF Xi) → ℝ := fun i => if |(tau i).re| ≤ T then x ^ (|(tau i).im| - 1 / 2) else 0
    with hh
  set t : ZeroIdx (sqF Xi) → ℝ := fun i => if |(tau i).re| ≤ T then 0 else wT x b k (tau i) with ht
  have hw := summable_wT hx hb hk
  have hpt : ∀ i, wT x b k (tau i) ≤ h i + t i := by
    intro i
    simp only [hh, ht]
    split_ifs with hi
    · rw [add_zero]; unfold wT
      exact div_le_self (by positivity) (one_le_pow₀ (by nlinarith [abs_nonneg (tau i).re]))
    · rw [zero_add]
  have hsh : Summable h := summable_of_ne_finset_zero (s := S) fun i hi => by
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi; simp [hh, hi]
  have hst : Summable t := Summable.of_nonneg_of_le
    (fun i => by simp only [ht]; split_ifs <;> [exact le_rfl; exact wT_nonneg hx0 hb.le k _])
    (fun i => by simp only [ht]; split_ifs <;> [exact wT_nonneg hx0 hb.le k _; exact le_rfl]) hw
  have hsum : ∑' i, wT x b k (tau i) ≤ ∑' i, h i + ∑' i, t i := by
    rw [← hsh.tsum_add hst]; exact hw.tsum_le_tsum hpt (hsh.add hst)
  have hhead : ∑' i, h i = ∑ i ∈ S, x ^ (|(tau i).im| - 1 / 2) := by
    rw [tsum_eq_sum (s := S) fun i hi => by
      simp only [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi; simp [hh, hi]]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi; simp [hh, hi]
  have hH := head_le S (fun i => |(tau i).im|) (fun i _ => abs_nonneg _) hx hQ hQx hK
    (fun i _ => tau_im i) (fun i hi => hfree i (by simpa [hS] using hi)) hM (fun j hj => by
      have hw0 : (0 : ℝ) ≤ (j : ℝ) / (2 * M) := by positivity
      have hw1 : (j : ℝ) / (2 * M) < 1 / 2 := by
        rw [div_lt_iff₀ (by positivity)]
        have : (j : ℝ) < M := by exact_mod_cast hj
        linarith
      rw [← NX_eq_card]; exact hden _ hw0 hw1)
  have hT' := tail_le (x := x) (b := b) hx hb hT hk
  rw [hhead] at hsum
  linarith

/-! ## A prime near `x` from three inequalities -/

theorem sqrt_log_mono {c d : ℝ} (hc : 1 ≤ c) (hcd : c ≤ d) :
    2 * Real.sqrt c * Real.log c ≤ 2 * Real.sqrt d * Real.log d := by
  have h1 := Real.sqrt_le_sqrt hcd
  have h2 := Real.log_le_log (by linarith) hcd
  have h3 := Real.log_nonneg hc
  have h4 := Real.sqrt_nonneg c
  nlinarith [Real.sqrt_nonneg d]

/-- **The core**: with `k = 2^{J+1}`, `D = kb ≤ 1`, a small zero sum, a small archimedean term and a
large main term give a prime in `[xe^{−D}, xe^{D}]`. -/
theorem prime_of_bounds {b x : ℝ} {J : ℕ} (hb : 0 < b) (hJ : 1 ≤ J) (hD : 2 ^ (J + 1) * b ≤ 1)
    (hx : 3 ≤ x)
    (hZ : ∑' i : ZeroIdx (sqF Xi), wT x b (2 ^ (J + 1)) (tau i) ≤ (Real.exp (-1) / 2) ^ (2 ^ (J + 1)) / 8)
    (hA : (Real.log (1 / b) + 5 + |psiRe 0|) / (b * Real.sqrt x)
      ≤ (Real.exp (-(1 / 2)) / 2) ^ (2 ^ (J + 1)) / 2)
    (hW : 2 * Real.sqrt (3 * x) * Real.log (3 * x) < b * x * Real.exp (-((2 ^ (J + 1) + 1) / 2))) :
    ∃ p : ℕ, p.Prime ∧ x * Real.exp (-(2 ^ (J + 1) * b)) ≤ p ∧ (p : ℝ) ≤ x * Real.exp (2 ^ (J + 1) * b) := by
  set k := 2 ^ (J + 1) with hk
  set D := (2 : ℝ) ^ (J + 1) * b with hDdef
  have hkR : (k : ℝ) = (2 : ℝ) ^ (J + 1) := by rw [hk]; push_cast; ring
  have hk2 : 2 ≤ k := by
    have : 2 ^ 1 ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hk] using this
  have hx0 : 0 < x := by linarith
  have hb1 : b ≤ 1 := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (J + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hD0 : 0 ≤ D := by positivity
  -- the zero sum over `ζ`
  have hsw := summable_wT (by linarith : (1 : ℝ) ≤ x) hb hk2
  have hWz := hasSum_Wz hsw.hasSum
  have hlog3 : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]
    exact lt_of_lt_of_le (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith) hx
  have hL : (2 : ℝ) ^ (J + 1) * b < Real.log x := by linarith
  have hlow := lower_bound hb hb1 hJ (by linarith : 1 < x) hL hWz.summable
  rw [hWz.tsum_eq] at hlow
  set Zt := ∑' i : ZeroIdx (sqF Xi), wT x b k (tau i) with hZt
  set P := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
      * gI b (J + 1) (Real.log n - Real.log x) with hP
  set m := (2 * b * Real.exp (-(b / 2))) ^ k with hm
  set n := (4 * b * Real.exp (b / 2)) ^ k with hn
  set C2 := Real.log (1 / b) + 5 + |psiRe 0| with hC2
  have hm0 : 0 < m := by positivity
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  -- `n·Z ≤ m/4`
  have hnm : n ≤ m * (2 * Real.exp 1) ^ k := by
    rw [hn, hm, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : Real.exp (b / 2) ≤ Real.exp (-(b / 2)) * Real.exp 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    nlinarith [Real.exp_pos (-(b / 2)), Real.exp_pos 1]
  have hcancel : (2 * Real.exp 1) ^ k * (Real.exp (-1) / 2) ^ k = 1 := by
    rw [← mul_pow]
    have : 2 * Real.exp 1 * (Real.exp (-1) / 2) = 1 := by
      rw [Real.exp_neg]; field_simp
    rw [this, one_pow]
  have hZ2 : 0 ≤ Zt := tsum_nonneg fun i => wT_nonneg hx0 hb.le k _
  have hnZ : n * (2 * Zt) ≤ m / 4 := by
    calc n * (2 * Zt) ≤ m * (2 * Real.exp 1) ^ k * (2 * ((Real.exp (-1) / 2) ^ k / 8)) :=
          mul_le_mul hnm (by linarith) (by positivity) (by positivity)
      _ = m / 4 * ((2 * Real.exp 1) ^ k * (Real.exp (-1) / 2) ^ k) := by ring
      _ = m / 4 := by rw [hcancel, mul_one]
  -- the archimedean term
  have hmlow : (2 * b * Real.exp (-(1 / 2))) ^ k ≤ m := by
    rw [hm]; apply pow_le_pow_left₀ (by positivity)
    have := Real.exp_le_exp.2 (show -(1 / 2 : ℝ) ≤ -(b / 2) by linarith)
    nlinarith
  have hArch : (4 * b) ^ k * C2 / b ≤ Real.sqrt x * m / 2 := by
    have h1 : C2 / b ≤ Real.sqrt x * ((Real.exp (-(1 / 2)) / 2) ^ k / 2) := by
      rw [div_le_iff₀ (by positivity)] at hA
      rw [div_le_iff₀ hb]; nlinarith
    have e : (4 * b) ^ k * (Real.exp (-(1 / 2)) / 2) ^ k = (2 * b * Real.exp (-(1 / 2))) ^ k := by
      rw [← mul_pow]; congr 1; ring
    calc (4 * b) ^ k * C2 / b = (4 * b) ^ k * (C2 / b) := by ring
      _ ≤ (4 * b) ^ k * (Real.sqrt x * ((Real.exp (-(1 / 2)) / 2) ^ k / 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.sqrt x * ((4 * b) ^ k * (Real.exp (-(1 / 2)) / 2) ^ k) / 2 := by ring
      _ ≤ Real.sqrt x * m / 2 := by
          rw [e]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmlow hsx.le) (by norm_num)
  have hP2 : Real.sqrt x * m ≤ 2 * P := by
    have : 2 * Real.sqrt x * n * (2 * Zt) ≤ Real.sqrt x * m / 2 := by
      have := mul_le_mul_of_nonneg_left hnZ (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt x)
      linarith
    linarith
  -- the window
  have hwin := weighted_le_window hb J hx0
  set lo := x * Real.exp (-D) with hlo
  set hi := x * Real.exp D with hhi
  set W := ∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊, ArithmeticFunction.vonMangoldt n with hWdef
  have hlo0 : 0 < lo := by positivity
  have hslo : 0 < Real.sqrt lo := Real.sqrt_pos.2 hlo0
  have hb2 : 0 < (2 * b) ^ (k - 1) := by positivity
  have hWlow : b * x * Real.exp (-((k + 1) / 2)) ≤ W := by
    have h1 : Real.sqrt x * m / 2 ≤ (2 * b) ^ (k - 1) / Real.sqrt lo * W := by
      rw [← hk] at hwin; linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hslo] at h1
    have hmk : (2 * b) ^ k * Real.exp (-(k / 2)) ≤ m := by
      calc (2 * b) ^ k * Real.exp (-(k / 2)) = (2 * b) ^ k * Real.exp (-(1 / 2)) ^ k := by
            rw [← Real.exp_nat_mul]; congr 2; ring
        _ = (2 * b * Real.exp (-(1 / 2))) ^ k := (mul_pow _ _ _).symm
        _ ≤ m := hmlow
    have hsq : Real.sqrt x * Real.sqrt lo = x * Real.exp (-(D / 2)) := by
      rw [hlo, ← Real.sqrt_mul hx0.le, show x * (x * Real.exp (-D)) = (x * Real.exp (-(D / 2))) ^ 2 by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf,
        Real.sqrt_sq (by positivity)]
    have hk1 : (2 * b) ^ k = (2 * b) ^ (k - 1) * (2 * b) := by
      rw [← pow_succ]; congr 1; omega
    have hexp : Real.exp (-((k + 1) / 2)) ≤ Real.exp (-(k / 2)) * Real.exp (-(D / 2)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have key : (2 * b) ^ (k - 1) * (b * x * Real.exp (-((k + 1) / 2)))
        ≤ (2 * b) ^ (k - 1) * W := by
      have : (2 * b) ^ (k - 1) * (b * x * Real.exp (-((k + 1) / 2)))
          ≤ Real.sqrt x * m / 2 * Real.sqrt lo := by
        calc (2 * b) ^ (k - 1) * (b * x * Real.exp (-((k + 1) / 2)))
            ≤ (2 * b) ^ (k - 1) * (b * x * (Real.exp (-(k / 2)) * Real.exp (-(D / 2)))) := by gcongr
          _ = (2 * b) ^ k * Real.exp (-(k / 2)) * (x * Real.exp (-(D / 2))) / 2 := by rw [hk1]; ring
          _ ≤ m * (x * Real.exp (-(D / 2))) / 2 := by gcongr
          _ = Real.sqrt x * m / 2 * Real.sqrt lo := by rw [← hsq]; ring
      linarith
    exact le_of_mul_le_mul_left key hb2
  have hc : (⌊hi⌋₊ : ℝ) ≤ 3 * x := by
    have h1 : Real.exp D ≤ 3 := (Real.exp_le_exp.2 hD).trans (by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith)
    refine (Nat.floor_le (by positivity)).trans ?_
    calc hi = x * Real.exp D := hhi
      _ ≤ x * 3 := mul_le_mul_of_nonneg_left h1 hx0.le
      _ = 3 * x := by ring
  have hc1 : (1 : ℝ) ≤ ⌊hi⌋₊ := by
    have hhi1 : (1 : ℝ) ≤ hi := by
      have h1 := Real.one_le_exp hD0
      calc (1 : ℝ) ≤ x * 1 := by linarith
        _ ≤ x * Real.exp D := mul_le_mul_of_nonneg_left h1 hx0.le
    have : 1 ≤ ⌊hi⌋₊ := (Nat.one_le_floor_iff _).2 hhi1
    exact_mod_cast this
  have hWc : 2 * Real.sqrt (⌊hi⌋₊ : ℝ) * Real.log (⌊hi⌋₊ : ℝ) < W := by
    have := sqrt_log_mono hc1 hc
    rw [hk] at hWlow
    push_cast at hWlow ⊢
    linarith
  have ha : 1 ≤ ⌈lo⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; exact hlo0)
  obtain ⟨p, hp, h1, h2⟩ := exists_prime_of_window ha hWc
  exact ⟨p, hp, (Nat.ceil_le.1 h1), (Nat.le_floor_iff (by positivity)).1 h2⟩

/-! ## Asymptotics -/

theorem tendsto_logpow_exp {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) (s : ℝ) :
    Tendsto (fun x => Real.log x ^ s * Real.exp (-c * Real.log x ^ β)) atTop (𝓝 0) := by
  have hF := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / β) c hc
  have hg : Tendsto (fun x => Real.log x ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  refine (hF.comp hg).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hl, mul_div_cancel₀ _ hβ.ne']

theorem tendsto_log_rpow_neg {a : ℝ} (ha : 0 < a) (c₀ c₁ : ℝ) :
    Tendsto (fun x => (c₀ * Real.log x + c₁) * x ^ (-a)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x => Real.log x / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have h2 := tendsto_rpow_neg_atTop ha
  have h3 := (h1.const_mul c₀).add (h2.const_mul c₁)
  simp only [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]; ring

/-! ## The theorem -/

set_option maxHeartbeats 2000000 in
theorem short_primes_aux {A B α : ℝ} (hA : 0 < A) (hα : α < 1) (hden : DensityXi A B)
    (hzf : ZeroFreeXi α) {θ θ0 : ℝ} (hθ0 : θ0 = max (1 / 2) (1 - 1 / A)) (hθ : θ0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  obtain ⟨C, hC, hCd⟩ := hden
  obtain ⟨Az, T₀, hAz, hZF⟩ := hzf
  have hθ0h : 1 / 2 ≤ θ0 := hθ0 ▸ le_max_left _ _
  have hθ0A : 1 - 1 / A ≤ θ0 := hθ0 ▸ le_max_right _ _
  set ε := (θ - θ0) / 4 with hεdef
  set th := θ0 + 2 * ε with hth
  set lam := 1 - th + ε with hlamdef
  set κ := 1 - A * lam with hκdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hthh : 1 / 2 + 2 * ε ≤ th := by rw [hth]; linarith
  have hthθ : th < θ := by rw [hth, hεdef]; linarith
  have hth1 : th < 1 := by linarith
  have hlam : 0 < lam := by rw [hlamdef, hth, hεdef]; linarith
  have hA1 : A * (1 - θ0) ≤ 1 := by
    have : 1 - θ0 ≤ 1 / A := by linarith
    calc A * (1 - θ0) ≤ A * (1 / A) := mul_le_mul_of_nonneg_left this hA.le
      _ = 1 := by field_simp
  have hκ : A * ε ≤ κ := by
    have e : κ = 1 - A * (1 - θ0) + A * ε := by rw [hκdef, hlamdef, hth]; ring
    rw [e]; linarith
  have hκ0 : 0 < κ := lt_of_lt_of_le (mul_pos hA hε) hκ
  set J := ⌈3 / ε⌉₊ + 1 with hJdef
  set k := 2 ^ (J + 1) with hkdef
  have hJ : 1 ≤ J := by omega
  have hkJ : J + 2 ≤ k := by
    have := Nat.lt_two_pow_self (n := J + 1); rw [hkdef]; omega
  have hk3 : 3 ≤ ε * ((k : ℝ) - 2) := by
    have h1 : 3 / ε ≤ (⌈3 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈3 / ε⌉₊ : ℕ) : ℝ) + 1 + 2 ≤ (k : ℝ) := by exact_mod_cast hkJ
    have h3 : 3 / ε ≤ (k : ℝ) - 2 := by linarith
    rwa [div_le_iff₀ hε, mul_comm] at h3
  have hk2 : 2 ≤ k := by omega
  have hkR : ((2 : ℝ) ^ (J + 1)) = (k : ℝ) := by rw [hkdef]; push_cast; ring
  set S0' := S0 with hS0'
  have hS0 : 0 ≤ S0 := tsum_nonneg fun _ => by positivity
  set δZ : ℝ := (Real.exp (-1) / 2) ^ k / 8 with hδZ
  have hδZ0 : 0 < δZ := by positivity
  set cc := κ * Az / lam ^ α with hcc
  have hcc0 : 0 < cc := by positivity
  set KH := 2 * Real.exp (1 / 2) * C * lam ^ B with hKH
  -- the eventual inequalities in `x`
  have e2 : ∀ᶠ x : ℝ in atTop, (k : ℝ) * x ^ (th - 1) ≤ 1 := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - th)).const_mul (k : ℝ)
    rw [mul_zero] at h
    filter_upwards [h.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    rw [show th - 1 = -(1 - th) by ring]; exact hx
  have e3 : ∀ᶠ x : ℝ in atTop, max T₀ 2 ≤ x ^ lam :=
    (tendsto_rpow_atTop hlam).eventually (eventually_ge_atTop _)
  have e4 : ∀ᶠ x : ℝ in atTop,
      KH * (Real.log x ^ (B + 1) * Real.exp (-cc * Real.log x ^ (1 - α))) + 4 * S0 * x ^ (-(1 : ℝ))
        < δZ := by
    have h := ((tendsto_logpow_exp hcc0 (by linarith : (0 : ℝ) < 1 - α) (B + 1)).const_mul KH).add
      ((tendsto_rpow_neg_atTop one_pos).const_mul (4 * S0))
    rw [mul_zero, mul_zero, add_zero] at h
    exact h.eventually (gt_mem_nhds hδZ0)
  have e5 : ∀ᶠ x : ℝ in atTop, ((1 - th) * Real.log x + (5 + |psiRe 0|)) * x ^ (-(th - 1 / 2))
      ≤ (Real.exp (-(1 / 2)) / 2) ^ k / 2 :=
    (tendsto_log_rpow_neg (by linarith : (0 : ℝ) < th - 1 / 2) _ _).eventually
      (Iic_mem_nhds (by positivity))
  set c0 := 2 * Real.sqrt 3 * Real.exp ((k + 1) / 2) with hc0
  have e6 : ∀ᶠ x : ℝ in atTop, (c0 * Real.log x + c0 * Real.log 3) * x ^ (-(th - 1 / 2)) < 1 :=
    (tendsto_log_rpow_neg (by linarith : (0 : ℝ) < th - 1 / 2) _ _).eventually
      (gt_mem_nhds one_pos)
  have hX : ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x * Real.exp (-((k : ℝ) * x ^ (th - 1))) ≤ p ∧
      (p : ℝ) ≤ x * Real.exp ((k : ℝ) * x ^ (th - 1)) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ), e2, e3, e4, e5, e6] with x hx3 h2 h3 h4 h5 h6
    have hx0 : 0 < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    set b := x ^ (th - 1) with hb
    have hb0 : 0 < b := Real.rpow_pos_of_pos hx0 _
    have hlx : 1 < Real.log x := by
      rw [Real.lt_log_iff_exp_lt hx0]
      exact lt_of_lt_of_le (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith) hx3
    have hl0 : 0 < Real.log x := by linarith
    -- (Z) the zero sum
    set T := x ^ lam with hT
    set M := ⌈Real.log x⌉₊ with hM
    set Q := T ^ A with hQ
    set K := C * Real.log T ^ B with hK
    set η := Az / Real.log T ^ α with hη
    have hT1 : 1 ≤ T := le_trans (by norm_num) ((le_max_right _ _).trans h3)
    have hlogT : Real.log T = lam * Real.log x := Real.log_rpow hx0 _
    have hlT0 : 0 < Real.log T := by rw [hlogT]; positivity
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by
      rw [hM, Ne, Nat.ceil_eq_zero, not_le]; exact hl0)
    have hMge : Real.log x ≤ M := Nat.le_ceil _
    have hMle : (M : ℝ) ≤ Real.log x + 1 := (Nat.ceil_lt_add_one hl0.le).le
    have hQ0 : 0 < Q := by positivity
    have hQe : Q = x ^ (lam * A) := by rw [hQ, hT, ← Real.rpow_mul hx0.le]
    have hQx : Q ≤ x := by
      rw [hQe]
      calc x ^ (lam * A) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
        _ = x := Real.rpow_one x
    have hK0 : 0 ≤ K := by positivity
    have hsum := wT_sum_le (x := x) (b := b) (T := T) (Q := Q) (K := K) (η := η) (k := k) (M := M)
      hx1 hb0 hT1 hk2 hM1 hQ0 hQx hK0
      (fun i hi => hZF T ((le_max_left _ _).trans h3) i hi)
      (fun w hw0 hw1 => by
        have := hCd T ((le_max_right _ _).trans h3) w hw0 hw1.le
        rw [hQ, ← Real.rpow_mul (by positivity)]
        calc (NX w T : ℝ) ≤ C * T ^ (A * (1 / 2 - w)) * Real.log T ^ B := this
          _ = K * T ^ (A * (1 / 2 - w)) := by rw [hK]; ring)
    -- the head
    have hxM : x ^ (1 / (2 * M : ℝ)) ≤ Real.exp (1 / 2) := by
      rw [Real.rpow_def_of_pos hx0]
      apply Real.exp_le_exp.2
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    have hQxη : (Q / x) ^ η = Real.exp (-cc * Real.log x ^ (1 - α)) := by
      rw [Real.rpow_def_of_pos (div_pos hQ0 hx0), Real.log_div hQ0.ne' hx0.ne', hQe,
        Real.log_rpow hx0, hη, hlogT, Real.mul_rpow hlam.le hl0.le,
        Real.rpow_sub hl0, Real.rpow_one, hcc]
      congr 1
      have : lam ^ α > 0 := by positivity
      have : Real.log x ^ α > 0 := by positivity
      field_simp
      rw [hκdef]; ring
    have hKe : K = C * lam ^ B * Real.log x ^ B := by
      rw [hK, hlogT, Real.mul_rpow hlam.le hl0.le]; ring
    have hhead : (M : ℝ) * x ^ (1 / (2 * M : ℝ)) * K * (Q / x) ^ η
        ≤ KH * (Real.log x ^ (B + 1) * Real.exp (-cc * Real.log x ^ (1 - α))) := by
      rw [hQxη, hKe, hKH, Real.rpow_add_one hl0.ne']
      have hE0 : 0 ≤ Real.exp (-cc * Real.log x ^ (1 - α)) := (Real.exp_pos _).le
      have hLB : 0 ≤ Real.log x ^ B := by positivity
      have hlB : 0 ≤ lam ^ B := by positivity
      have hM2 : (M : ℝ) ≤ 2 * Real.log x := by linarith
      have hP : 0 ≤ C * lam ^ B * Real.log x ^ B * Real.exp (-cc * Real.log x ^ (1 - α)) := by
        positivity
      calc (M : ℝ) * x ^ (1 / (2 * M : ℝ)) * (C * lam ^ B * Real.log x ^ B)
            * Real.exp (-cc * Real.log x ^ (1 - α))
          = (M : ℝ) * x ^ (1 / (2 * M : ℝ))
            * (C * lam ^ B * Real.log x ^ B * Real.exp (-cc * Real.log x ^ (1 - α))) := by ring
        _ ≤ (2 * Real.log x) * Real.exp (1 / 2)
            * (C * lam ^ B * Real.log x ^ B * Real.exp (-cc * Real.log x ^ (1 - α))) := by
            gcongr
        _ = _ := by ring
    -- the tail
    have htail : 4 * S0 / (b ^ 2 * (b * T) ^ (k - 2)) ≤ 4 * S0 * x ^ (-(1 : ℝ)) := by
      have hbT : b * T = x ^ ε := by
        rw [hb, hT, ← Real.rpow_add hx0]; congr 1; rw [hlamdef]; ring
      have hden2 : x ^ (1 : ℝ) ≤ b ^ 2 * (b * T) ^ (k - 2) := by
        rw [hbT, hb, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
          ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
        apply Real.rpow_le_rpow_of_exponent_le hx1
        have : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by rw [Nat.cast_sub hk2]; push_cast; ring
        rw [this]; push_cast; nlinarith
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by rwa [Real.rpow_one] at hden2)
    have hZ : ∑' i : ZeroIdx (sqF Xi), wT x b (2 ^ (J + 1)) (tau i)
        ≤ (Real.exp (-1) / 2) ^ (2 ^ (J + 1)) / 8 := by
      rw [← hkdef]; linarith
    -- (A) the archimedean term
    have hA' : (Real.log (1 / b) + 5 + |psiRe 0|) / (b * Real.sqrt x)
        ≤ (Real.exp (-(1 / 2)) / 2) ^ (2 ^ (J + 1)) / 2 := by
      rw [← hkdef]
      have hlb : Real.log (1 / b) = (1 - th) * Real.log x := by
        rw [one_div, Real.log_inv, hb, Real.log_rpow hx0]; ring
      have hbx : b * Real.sqrt x = x ^ (th - 1 / 2) := by
        rw [hb, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; congr 1; ring
      rw [hlb, hbx, div_eq_mul_inv, ← Real.rpow_neg hx0.le]
      linarith
    -- (W) the main term
    have hW' : 2 * Real.sqrt (3 * x) * Real.log (3 * x)
        < b * x * Real.exp (-((2 ^ (J + 1) + 1) / 2)) := by
      have hkk : ((2 : ℝ) ^ (J + 1) + 1) / 2 = ((k : ℝ) + 1) / 2 := by rw [hkR]
      rw [hkk]
      set Y := b * x * Real.exp (-(((k : ℝ) + 1) / 2)) with hY
      have hY0 : 0 < Y := by positivity
      have e : 2 * Real.sqrt (3 * x) * Real.log (3 * x)
          = (c0 * Real.log x + c0 * Real.log 3) * x ^ (-(th - 1 / 2)) * Y := by
        rw [hY, hc0, hb, Real.sqrt_mul (by norm_num), Real.log_mul (by norm_num) hx0.ne']
        have h1 : x ^ (-(th - 1 / 2)) * (x ^ (th - 1) * x) = Real.sqrt x := by
          rw [← Real.rpow_add_one hx0.ne', ← Real.rpow_add hx0, Real.sqrt_eq_rpow]; congr 1; ring
        have h2 : Real.exp ((k + 1) / 2) * Real.exp (-((k + 1) / 2)) = 1 := by
          rw [← Real.exp_add]; simp
        calc 2 * (Real.sqrt 3 * Real.sqrt x) * (Real.log 3 + Real.log x)
            = 2 * Real.sqrt 3 * (Real.log x + Real.log 3) * (x ^ (-(th - 1 / 2)) * (x ^ (th - 1) * x))
              * (Real.exp ((k + 1) / 2) * Real.exp (-((k + 1) / 2))) := by rw [h1, h2]; ring
          _ = _ := by ring
      rw [e]
      calc (c0 * Real.log x + c0 * Real.log 3) * x ^ (-(th - 1 / 2)) * Y < 1 * Y :=
            mul_lt_mul_of_pos_right h6 hY0
        _ = Y := one_mul Y
    have hD : 2 ^ (J + 1) * b ≤ 1 := by rw [hkR]; exact h2
    obtain ⟨p, hp, h1, h2'⟩ := prime_of_bounds hb0 hJ hD hx3 hZ hA' hW'
    exact ⟨p, hp, by rw [← hkR]; exact h1, by rw [← hkR]; exact h2'⟩
  -- from `x` to `y = x − y^θ/2`
  have hxy : Tendsto (fun y : ℝ => y + y ^ θ / 2) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    have : 0 ≤ y ^ θ := Real.rpow_nonneg hy _
    simp only [id]; linarith
  have hX' := hxy.eventually hX
  have e7 : ∀ᶠ y : ℝ in atTop, 8 * (k : ℝ) < y ^ (θ - th) :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < θ - th)).eventually (eventually_gt_atTop _)
  filter_upwards [hX', e7, eventually_ge_atTop (1 : ℝ)] with y hXy h7 hy1
  obtain ⟨p, hp, h1, h2⟩ := hXy
  set x := y + y ^ θ / 2 with hx
  have hy0 : 0 < y := by linarith
  have hyθ : y ^ θ ≤ y := by
    calc y ^ θ ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 hθ1.le
      _ = y := Real.rpow_one y
  have hyθ0 : 0 < y ^ θ := Real.rpow_pos_of_pos hy0 _
  have hx0 : 0 < x := by positivity
  have hx2 : x ≤ 2 * y := by linarith
  have hxth : x ^ th ≤ 2 * y ^ th := by
    have h2th : (2 : ℝ) ^ th ≤ 2 := by
      calc (2 : ℝ) ^ th ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hth1.le
        _ = 2 := Real.rpow_one 2
    calc x ^ th ≤ (2 * y) ^ th := Real.rpow_le_rpow hx0.le hx2 (by linarith)
      _ = 2 ^ th * y ^ th := Real.mul_rpow (by norm_num) hy0.le
      _ ≤ 2 * y ^ th := mul_le_mul_of_nonneg_right h2th (by positivity)
  have hsplit : y ^ θ = y ^ (θ - th) * y ^ th := by rw [← Real.rpow_add hy0]; congr 1; ring
  have hyth0 : 0 < y ^ th := Real.rpow_pos_of_pos hy0 _
  have hkey : 2 * (k : ℝ) * x ^ th < y ^ θ / 2 := by
    have h8 := mul_lt_mul_of_pos_right h7 hyth0
    have hk0 : (0 : ℝ) ≤ k := by positivity
    rw [hsplit]; nlinarith
  set D := (k : ℝ) * x ^ (th - 1) with hD
  have hDx : D * x = (k : ℝ) * x ^ th := by
    rw [hD, mul_assoc, ← Real.rpow_add_one hx0.ne']; congr 2; ring
  have hD0 : 0 ≤ D := by positivity
  have hD1 : D ≤ 1 := by
    have hk0 : (0 : ℝ) ≤ k * x ^ th := by positivity
    have : D * x ≤ 1 * x := by rw [hDx]; linarith
    exact le_of_mul_le_mul_right this hx0
  have hexp := Real.abs_exp_sub_one_le (x := -D) (by rw [abs_neg, abs_of_nonneg hD0]; exact hD1)
  have hexp' := Real.abs_exp_sub_one_le (x := D) (by rw [abs_of_nonneg hD0]; exact hD1)
  rw [abs_neg, abs_of_nonneg hD0] at hexp
  rw [abs_of_nonneg hD0] at hexp'
  have hl : 1 - 2 * D ≤ Real.exp (-D) := by linarith [neg_abs_le (Real.exp (-D) - 1)]
  have hu : Real.exp D ≤ 1 + 2 * D := by linarith [le_abs_self (Real.exp D - 1)]
  refine ⟨p, hp, ?_, ?_⟩
  · have e1 : x * (1 - 2 * D) ≤ x * Real.exp (-D) := mul_le_mul_of_nonneg_left hl hx0.le
    have e2 : x * (1 - 2 * D) = x - 2 * ((k : ℝ) * x ^ th) := by rw [← hDx]; ring
    linarith
  · have e1 : x * Real.exp D ≤ x * (1 + 2 * D) := mul_le_mul_of_nonneg_left hu hx0.le
    have e2 : x * (1 + 2 * D) = x + 2 * ((k : ℝ) * x ^ th) := by rw [← hDx]; ring
    linarith

/-- **Primes in short intervals from zero density.** If `N(σ, T) ≪ T^{A(1−σ)}(log T)^B` and ζ has
a zero-free region of width `(log T)^{−α}` with `α < 1`, then for every `θ > max(½, 1 − 1/A)` every
large `y` has a prime in `(y, y + y^θ]`. -/
theorem short_primes_of_density {A B α : ℝ} (hA : 0 < A) (hα : α < 1) (hden : DensityXi A B)
    (hzf : ZeroFreeXi α) {θ : ℝ} (hθh : 1 / 2 < θ) (hθA : 1 - 1 / A < θ) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ θ := by
  set θ0 := max (1 / 2) (1 - 1 / A) with hθ0
  have hθ0θ : θ0 < θ := max_lt hθh hθA
  have hθ01 : θ0 < 1 := max_lt (by norm_num) (by have := one_div_pos.2 hA; linarith)
  have h1 : θ0 < min θ ((1 + θ0) / 2) := lt_min hθ0θ (by linarith)
  have h2 : min θ ((1 + θ0) / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  filter_upwards [short_primes_aux hA hα hden hzf hθ0 h1 h2, eventually_ge_atTop (1 : ℝ)]
    with y hy hy1
  obtain ⟨p, hp, hyp, hpy⟩ := hy
  refine ⟨p, hp, hyp, hpy.trans ?_⟩
  have := Real.rpow_le_rpow_of_exponent_le hy1 (min_le_left θ ((1 + θ0) / 2))
  linarith

end ShortWeil

#print axioms ShortWeil.short_primes_of_density

#print axioms ShortWeil.finite_re_le
#print axioms ShortWeil.wT_sum_le
#print axioms ShortWeil.prime_of_bounds
