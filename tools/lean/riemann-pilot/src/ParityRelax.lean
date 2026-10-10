import Mathlib
import ParitySplit

/-! # The relaxation for both parities and every prime power below the support (round 135)

Round 122–123's relaxation handled the even sector with at most one prime. Here it is made generic:

* **Any even mode weight** `w` with `Σ p_m w_m = P` (`trunc_W`). The prime side below `e^{2a}` is such a
  weight: `2S(g) = Σ_{n<K} c_n f(log n)` with `c_n = 2Λ(n)/√n` (`primeS_range`), and
  `f(u) = Σ p_m cos(πmu/4a)` makes `w_m = Σ_{n<K} c_n cos(πm log n/4a)` (`hasSum_wP`).
* **The even sector** (`weilQ_ge_relaxW`): vectors `cosh(t/2), cos(πkt/4a)`, as before.
* **The odd sector** (`weilQodd_ge_relaxW`): the odd pole term is `−2 poleR²` with
  `poleR = −∫ g sinh(t/2)`, and the odd mode masses are `p_k = (∫ g sin(πkt/4a))²/8a`, `p₀ = 0`. So
  `Q(g) ≥ κ + Σ sᵢ yᵢ²` with `y₀ = ∫ g sinh(t/2)` (`s₀ = −2`) and `y_k = ∫ g sin(πkt/4a)`.
* **Bessel for any continuous window vectors** (`bessel_V`, in PoleRelax.lean since round 335, where
  the even sector's `bessel_gram` is its case), the odd Gram entries in closed form
  (`gramO_eq`), monotonicity of the general form in the support (`weilQg_mono`), and the tail level
  from any certified `Cin` value (`tail_Wp`).
-/

open Real Filter Topology Complex MeasureTheory Set Matrix

noncomputable section

namespace Pilot1ca

/-! ## A. Truncation with a general even mode weight -/

/-- **Truncation with a weight**: if `Σ p_m w_m = P` and every mode outside `S₀` has `ψ_m − w_m ≥ τ`, then
`τ + Σ_{S₀} (ψ_m − w_m − τ) p_m ≤ Near − P`. -/
theorem trunc_W {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : SProbe a g) (hn : normSq g = 1)
    (w : ℤ → ℝ) {P : ℝ} (hW : HasSum (fun m => pm a g m * w m) P) (S₀ : Finset ℤ) {τ : ℝ}
    (hτ : ∀ m, m ∉ S₀ → τ ≤ modeE a m - w m) :
    τ + ∑ m ∈ S₀, (modeE a m - w m - τ) * pm a g m
      ≤ (∫ u in Ioc 0 (2 * a), archIntegrand g u) - P := by
  have hP := hasSum_pmS ha hp
  rw [hn] at hP
  have hT : Tendsto (fun S : Finset ℤ => ∑ m ∈ S₀, (modeE a m - w m - τ) * pm a g m
      + τ * ∑ m ∈ S, pm a g m + ∑ m ∈ S, pm a g m * w m) atTop
      (𝓝 (∑ m ∈ S₀, (modeE a m - w m - τ) * pm a g m + τ * 1 + P)) :=
    (tendsto_const_nhds.add (hP.const_mul τ)).add hW
  have hle : ∑ m ∈ S₀, (modeE a m - w m - τ) * pm a g m + τ * 1 + P
      ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
    refine le_of_tendsto hT ?_
    filter_upwards [eventually_ge_atTop S₀] with S hS
    have hsplit := Finset.sum_sdiff hS (f := pm a g)
    have hsplit2 := Finset.sum_sdiff hS (f := fun m => pm a g m * (modeE a m - w m))
    have htail : τ * ∑ m ∈ S \ S₀, pm a g m ≤ ∑ m ∈ S \ S₀, pm a g m * (modeE a m - w m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m hm' => ?_
      rw [Finset.mem_sdiff] at hm'
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hτ m hm'.2) (pm_nonneg ha g m)
    have hlow : ∑ m ∈ S₀, (modeE a m - w m - τ) * pm a g m
        = ∑ m ∈ S₀, pm a g m * (modeE a m - w m) - τ * ∑ m ∈ S₀, pm a g m := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hE : ∑ m ∈ S, pm a g m * (modeE a m - w m)
        = ∑ m ∈ S, pm a g m * modeE a m - ∑ m ∈ S, pm a g m * w m := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hmode := sum_modeE_leS ha hp hn S
    rw [← hsplit, mul_add] at *
    rw [← hsplit2] at hE
    linarith
  linarith

/-! ## B. The prime side below `e^{2a}` as a mode weight -/

/-- `c_n = 2Λ(n)/√n`. -/
def cwΛ (n : ℕ) : ℝ := 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n)

theorem cw_nonneg (n : ℕ) : 0 ≤ cwΛ n := by
  unfold cwΛ; have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity

/-- The prime weight `w_m = Σ_{n<K} c_n cos(πm log n/4a)`. -/
def wP (a : ℝ) (K : ℕ) (m : ℤ) : ℝ :=
  ∑ n ∈ Finset.range K, cwΛ n * Real.cos (π * m * Real.log n / (4 * a))

theorem wP_neg (a : ℝ) (K : ℕ) (m : ℤ) : wP a K (-m) = wP a K m := by
  unfold wP; refine Finset.sum_congr rfl fun n _ => ?_
  push_cast; rw [show π * -(m : ℝ) * Real.log n / (4 * a) = -(π * m * Real.log n / (4 * a)) by ring,
    Real.cos_neg]

theorem wP_le (a : ℝ) (K : ℕ) (m : ℤ) : wP a K m ≤ ∑ n ∈ Finset.range K, cwΛ n := by
  unfold wP; refine Finset.sum_le_sum fun n _ => ?_
  nlinarith [cw_nonneg n, Real.cos_le_one (π * m * Real.log n / (4 * a))]

theorem wP_zero (a : ℝ) (K : ℕ) : wP a K 0 = ∑ n ∈ Finset.range K, cwΛ n := by
  unfold wP; simp

theorem hasSum_wP {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : SProbe a g) (hn : normSq g = 1) {K : ℕ}
    (hK : ∀ n, n < K → Real.log n ≤ 2 * a) :
    HasSum (fun m => pm a g m * wP a K m) (∑ n ∈ Finset.range K, cwΛ n * autocorr g (Real.log n)) := by
  have h := hasSum_sum (s := Finset.range K) fun n hk =>
    (hasSum_autocorrS ha hp hn (Real.log_natCast_nonneg n) (hK n (Finset.mem_range.1 hk))).mul_left (cwΛ n)
  convert h using 1
  funext m; unfold wP; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

/-- **The prime side below `e^{2a}`**: `2S(g) = Σ_{n<K} c_n f(log n)` when `2a < log K`. -/
theorem primeS_range {a : ℝ} {g : ℝ → ℝ} (hp : SProbe a g) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : 2 * a < Real.log K) :
    2 * primeS g = ∑ n ∈ Finset.range K, cwΛ n * autocorr g (Real.log n) := by
  unfold primeS
  rw [tsum_eq_sum (s := Finset.range K), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n _ => by unfold cwΛ; ring
  · intro n hn
    have hKn : K ≤ n := by simpa using hn
    have hl : Real.log K ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast hK1) (by exact_mod_cast hKn)
    have hz : autocorr g (Real.log n) = 0 :=
      autocorr_eq_zero hp.supp (lt_of_lt_of_le (by linarith) (le_abs_self _))
    simp [hz]

/-! ## C. The even sector -/

/-- Even weights: `s₀ = 2`, `s₁ = (−w₀ − τ)/8a`, `s_{k+2} = 2(ψ̲_{k+1} − w_{k+1} − τ)/8a`. -/
def sfunW (a τ : ℝ) (w : ℤ → ℝ) (ψl : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 2 else if k = 1 then (-w 0 - τ) / (8 * a)
  else 2 * (ψl (k - 1) - w ((k - 1 : ℕ) : ℤ) - τ) / (8 * a)

/-- **The even relaxation with a general weight.** -/
theorem weilQ_ge_relaxW {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    (w : ℤ → ℝ) (hw : ∀ m, w (-m) = w m) {P : ℝ} (hW : HasSum (fun m => pm a g m * w m) P)
    (hprime : 2 * primeS g = P) (N : ℕ) (τ : ℝ) (ψl : ℕ → ℝ)
    (htail : ∀ n : ℤ, (N : ℤ) < n → τ ≤ modeE a n - w n)
    (hlow : ∀ k : ℕ, k < N → ψl (k + 1) ≤ modeE a ((k : ℤ) + 1)) :
    weilConst + (∫ u in Ioi (2 * a), kerK u) + τ
      + xv a g (N + 2) ⬝ᵥ (diagonal (fun i : Fin (N + 2) => sfunW a τ w ψl i) *ᵥ xv a g (N + 2))
      ≤ weilQ a g := by
  have hτ : ∀ n, n ∉ Finset.Icc (-(N : ℤ)) N → τ ≤ modeE a n - w n := by
    intro n hn'
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn'
    rcases hn' with h | h
    · have e1 := modeE_neg a (-n); have e2 := hw (-n); rw [neg_neg] at e1 e2
      rw [e1, e2]; exact htail _ (by omega)
    · exact htail n h
  have hE := trunc_W ha hp.toS hn w hW (Finset.Icc (-(N : ℤ)) N) hτ
  rw [sum_Icc_even N (fun k => by simp only [modeE_neg, hw, pm_neg ha hp])] at hE
  set X : ℕ → ℝ := fun k => ∫ t, g t * Real.cos (π * k * t / (4 * a)) with hX
  have hpm1 : ∀ k : ℕ, pm a g ((k : ℤ) + 1) = X (k + 1) ^ 2 / (8 * a) := by
    intro k; rw [pm_even ha hp]; simp only [hX]; push_cast; rfl
  have hpm0 : pm a g 0 = X 0 ^ 2 / (8 * a) := by
    rw [pm_even ha hp]; simp only [hX]; push_cast; rfl
  rw [modeE_zero, hpm0] at hE
  simp only [hpm1] at hE
  have hlowsum : ∑ k ∈ Finset.range N, (ψl (k + 1) - w ((k : ℤ) + 1) - τ) * (X (k + 1) ^ 2 / (8 * a))
      ≤ ∑ k ∈ Finset.range N, (modeE a ((k : ℤ) + 1) - w ((k : ℤ) + 1) - τ) * (X (k + 1) ^ 2 / (8 * a)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have := hlow k (Finset.mem_range.mp hk)
    have : 0 ≤ X (k + 1) ^ 2 / (8 * a) := by positivity
    nlinarith
  have hquad : xv a g (N + 2) ⬝ᵥ (diagonal (fun i : Fin (N + 2) => sfunW a τ w ψl i) *ᵥ xv a g (N + 2))
      = 2 * (∫ t, g t * Real.cosh (t / 2)) ^ 2 + ((-w 0 - τ) / (8 * a)) * X 0 ^ 2
        + ∑ k ∈ Finset.range N, 2 * (ψl (k + 1) - w ((k : ℤ) + 1) - τ) / (8 * a) * X (k + 1) ^ 2 := by
    simp only [dotProduct, mulVec_diagonal]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    rw [← Fin.sum_univ_eq_sum_range (fun k => 2 * (ψl (k + 1) - w ((k : ℤ) + 1) - τ) / (8 * a)
      * X (k + 1) ^ 2) N]
    simp only [xv, vv, sfunW, hX, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, ite_true, Nat.cast_zero, zero_mul,
      mul_zero, zero_div, Nat.add_one_sub_one]
    have hne : ∀ x : ℕ, x + 1 + 1 ≠ 1 := fun x => by omega
    have key : ∀ u v : ℝ, u * (v * u) = v * u ^ 2 := fun u v => by ring
    simp only [hne, ite_false, key]
    push_cast; ring
  have hQ : weilQ a g = 2 * poleR g a ^ 2 + weilConst
      + ((∫ u in Ioc 0 (2 * a), archIntegrand g u) + ∫ u in Ioi (2 * a), kerK u) - P := by
    rw [weilQ_eq', hn, archE_split ha hp hn]; linarith
  have hs2 : ∑ k ∈ Finset.range N, 2 * (ψl (k + 1) - w ((k : ℤ) + 1) - τ) / (8 * a) * X (k + 1) ^ 2
      = 2 * ∑ k ∈ Finset.range N, (ψl (k + 1) - w ((k : ℤ) + 1) - τ) * (X (k + 1) ^ 2 / (8 * a)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h0 : (0 - w 0 - τ) * (X 0 ^ 2 / (8 * a)) = (-w 0 - τ) / (8 * a) * X 0 ^ 2 := by ring
  rw [hquad, hQ, poleR_eq_xv0 ha hp, hs2]
  linarith

/-! ## D. The odd sector -/

/-- The odd window vectors: `v₀ = sinh(t/2)`, `v_{k+1} = sin(π(k+1)t/4a)`. -/
def vo (a : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => Real.sinh (t / 2)
  | k + 1 => fun t => Real.sin (π * ((k + 1 : ℕ) : ℝ) * t / (4 * a))

theorem vo_cont (a : ℝ) (i : ℕ) : Continuous (vo a i) := by
  cases i with
  | zero => simp only [vo]; fun_prop
  | succ k => simp only [vo]; fun_prop

def xo (a : ℝ) (g : ℝ → ℝ) (m : ℕ) : Fin m → ℝ := fun i => ∫ t, g t * vo a i t

/-- Odd weights: `s₀ = −2` (the pole term hurts), `s_k = 2(ψ̲_k − w_k − τ)/8a`. -/
def sfunO (a τ : ℝ) (w : ℤ → ℝ) (ψl : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then -2 else 2 * (ψl k - w (k : ℤ) - τ) / (8 * a)

theorem poleR_odd_eq {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) :
    poleR g a = -∫ t, g t * Real.sinh (t / 2) := by
  rw [poleR_eq_cosh_sub_sinh (oprobe_integrable hp).intervalIntegrable,
    intervalIntegral_odd (f := fun t => g t * Real.cosh (t / 2))
      (fun t => by rw [hp.odd, show -t / 2 = -(t / 2) by ring, Real.cosh_neg]; ring),
    integral_suppS ha hp.toS]
  ring

/-- **The odd relaxation with a general weight.** -/
theorem weilQodd_ge_relaxW {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1)
    (w : ℤ → ℝ) (hw : ∀ m, w (-m) = w m) {P : ℝ} (hW : HasSum (fun m => pm a g m * w m) P)
    (hprime : 2 * primeS g = P) (N : ℕ) (τ : ℝ) (ψl : ℕ → ℝ)
    (htail : ∀ n : ℤ, (N : ℤ) < n → τ ≤ modeE a n - w n)
    (hlow : ∀ k : ℕ, k < N → ψl (k + 1) ≤ modeE a ((k : ℤ) + 1)) :
    weilConst + (∫ u in Ioi (2 * a), kerK u) + τ
      + xo a g (N + 1) ⬝ᵥ (diagonal (fun i : Fin (N + 1) => sfunO a τ w ψl i) *ᵥ xo a g (N + 1))
      ≤ weilQg a g := by
  have hτ : ∀ n, n ∉ Finset.Icc (-(N : ℤ)) N → τ ≤ modeE a n - w n := by
    intro n hn'
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn'
    rcases hn' with h | h
    · have e1 := modeE_neg a (-n); have e2 := hw (-n); rw [neg_neg] at e1 e2
      rw [e1, e2]; exact htail _ (by omega)
    · exact htail n h
  have hE := trunc_W ha hp.toS hn w hW (Finset.Icc (-(N : ℤ)) N) hτ
  rw [sum_Icc_even N (fun k => by simp only [modeE_neg, hw, pm_negO ha hp])] at hE
  set Y : ℕ → ℝ := fun k => ∫ t, g t * Real.sin (π * k * t / (4 * a)) with hY
  have hpm1 : ∀ k : ℕ, pm a g ((k : ℤ) + 1) = Y (k + 1) ^ 2 / (8 * a) := by
    intro k; rw [pm_odd ha hp]; simp only [hY]; push_cast; rfl
  rw [pm_zeroO ha hp, mul_zero, zero_add] at hE
  simp only [hpm1] at hE
  have hlowsum : ∑ k ∈ Finset.range N, (ψl (k + 1) - w ((k : ℤ) + 1) - τ) * (Y (k + 1) ^ 2 / (8 * a))
      ≤ ∑ k ∈ Finset.range N, (modeE a ((k : ℤ) + 1) - w ((k : ℤ) + 1) - τ) * (Y (k + 1) ^ 2 / (8 * a)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have := hlow k (Finset.mem_range.mp hk)
    have : 0 ≤ Y (k + 1) ^ 2 / (8 * a) := by positivity
    nlinarith
  have hquad : xo a g (N + 1) ⬝ᵥ (diagonal (fun i : Fin (N + 1) => sfunO a τ w ψl i) *ᵥ xo a g (N + 1))
      = -2 * (∫ t, g t * Real.sinh (t / 2)) ^ 2
        + ∑ k ∈ Finset.range N, 2 * (ψl (k + 1) - w ((k : ℤ) + 1) - τ) / (8 * a) * Y (k + 1) ^ 2 := by
    simp only [dotProduct, mulVec_diagonal]
    rw [Fin.sum_univ_succ]
    rw [← Fin.sum_univ_eq_sum_range (fun k => 2 * (ψl (k + 1) - w ((k : ℤ) + 1) - τ) / (8 * a)
      * Y (k + 1) ^ 2) N]
    simp only [xo, vo, sfunO, hY, Fin.val_zero, Fin.val_succ]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, ite_true]
    have key : ∀ u v : ℝ, u * (v * u) = v * u ^ 2 := fun u v => by ring
    simp only [key]
    push_cast; ring
  have hQ : weilQg a g = -2 * poleR g a ^ 2 + weilConst
      + ((∫ u in Ioc 0 (2 * a), archIntegrand g u) + ∫ u in Ioi (2 * a), kerK u) - P := by
    rw [weilQg, poleL_odd hp, hn, archE_splitS ha hp.toS hn]; linarith
  have hs2 : ∑ k ∈ Finset.range N, 2 * (ψl (k + 1) - w ((k : ℤ) + 1) - τ) / (8 * a) * Y (k + 1) ^ 2
      = 2 * ∑ k ∈ Finset.range N, (ψl (k + 1) - w ((k : ℤ) + 1) - τ) * (Y (k + 1) ^ 2 / (8 * a)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hquad, hQ, poleR_odd_eq ha hp, neg_sq, hs2]
  linarith

/-! ## E. Bessel for any continuous window vectors, and the odd Gram matrix -/

theorem int_sinh_sin {a : ℝ} (ω : ℝ) :
    (∫ t in (-a)..a, Real.sinh (t / 2) * Real.sin (ω * t))
      = (Real.cosh (a / 2) * Real.sin (ω * a) - 2 * ω * Real.sinh (a / 2) * Real.cos (ω * a)) / (ω ^ 2 + 1 / 4) := by
  have hden : ω ^ 2 + 1 / 4 ≠ 0 := by positivity
  have hderiv : ∀ u ∈ Set.uIcc (-a) a, HasDerivAt
      (fun u => (1 / 2 * Real.cosh (u / 2) * Real.sin (ω * u) - ω * Real.sinh (u / 2) * Real.cos (ω * u))
        / (ω ^ 2 + 1 / 4))
      (Real.sinh (u / 2) * Real.sin (ω * u)) u := by
    intro u _
    have hc := ((hasDerivAt_id u).const_mul ω).cos
    have hs := ((hasDerivAt_id u).const_mul ω).sin
    have hsh := ((hasDerivAt_id u).div_const 2).sinh
    have hch := ((hasDerivAt_id u).div_const 2).cosh
    have := (((hch.const_mul (1 / 2)).mul hs).sub ((hsh.const_mul ω).mul hc)).div_const (ω ^ 2 + 1 / 4)
    convert this using 1
    · funext v; simp [id]
    · simp only [id, mul_one]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u => Real.sinh (u / 2) * Real.sin (ω * u)).intervalIntegrable _ _)]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, neg_div, Real.sinh_neg, Real.cosh_neg]
  field_simp; ring

theorem int_sin_sin {a α β : ℝ} (hm : α - β ≠ 0) (hp : α + β ≠ 0) :
    (∫ t in (-a)..a, Real.sin (α * t) * Real.sin (β * t))
      = Real.sin ((α - β) * a) / (α - β) - Real.sin ((α + β) * a) / (α + β) := by
  have hderiv : ∀ u ∈ Set.uIcc (-a) a, HasDerivAt
      (fun u => (Real.sin ((α - β) * u) / (α - β) - Real.sin ((α + β) * u) / (α + β)) / 2)
      (Real.sin (α * u) * Real.sin (β * u)) u := by
    intro u _
    have e1 := (((hasDerivAt_id u).const_mul (α - β)).sin).div_const (α - β)
    have e2 := (((hasDerivAt_id u).const_mul (α + β)).sin).div_const (α + β)
    have := (e1.sub e2).div_const 2
    convert this using 1
    · funext v; simp [id]
    · simp only [id, mul_one]
      rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u => Real.sin (α * u) * Real.sin (β * u)).intervalIntegrable _ _)]
  simp only [mul_neg, Real.sin_neg, neg_div]; ring

theorem int_sin_sq {a α : ℝ} (hα : α ≠ 0) :
    (∫ t in (-a)..a, Real.sin (α * t) * Real.sin (α * t)) = a - Real.sin (2 * α * a) / (2 * α) := by
  have hderiv : ∀ u ∈ Set.uIcc (-a) a, HasDerivAt (fun u => u / 2 - Real.sin (2 * α * u) / (4 * α))
      (Real.sin (α * u) * Real.sin (α * u)) u := by
    intro u _
    have e1 := (hasDerivAt_id u).div_const 2
    have e2 := (((hasDerivAt_id u).const_mul (2 * α)).sin).div_const (4 * α)
    convert e1.sub e2 using 1
    · funext v; simp [id]
    · simp only [id, mul_one]
      rw [show 2 * α * u = 2 * (α * u) by ring, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq (α * u)
      field_simp; nlinarith [this]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u => Real.sin (α * u) * Real.sin (α * u)).intervalIntegrable _ _)]
  simp only [mul_neg, Real.sin_neg, neg_div]; ring

/-- The odd Gram entries in closed form (`ω_k = πk/4a`). -/
def gCO (a : ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then
    (if j = 0 then Real.sinh a - a else
      (Real.cosh (a / 2) * Real.sin (omk a j * a) - 2 * omk a j * Real.sinh (a / 2) * Real.cos (omk a j * a))
        / (omk a j ^ 2 + 1 / 4))
  else if j = 0 then
    (Real.cosh (a / 2) * Real.sin (omk a i * a) - 2 * omk a i * Real.sinh (a / 2) * Real.cos (omk a i * a))
      / (omk a i ^ 2 + 1 / 4)
  else if i = j then a - Real.sin (2 * omk a i * a) / (2 * omk a i)
  else
    Real.sin ((omk a i - omk a j) * a) / (omk a i - omk a j)
      - Real.sin ((omk a i + omk a j) * a) / (omk a i + omk a j)

theorem vo_succ (a : ℝ) (k : ℕ) (t : ℝ) : vo a (k + 1) t = Real.sin (omk a (k + 1) * t) := by
  simp only [vo, omk]; ring_nf

theorem gramO_eq {a : ℝ} (ha : 0 < a) (m : ℕ) (i j : Fin m) : gramV (vo a) a m i j = gCO a i j := by
  simp only [gramV, Matrix.of_apply, gCO]
  have hω : ∀ k : ℕ, 0 < k → 0 < omk a k := fun k hk => by
    unfold omk; have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hωinj : ∀ p q : ℕ, omk a p = omk a q → p = q := by
    intro p q h; unfold omk at h
    have : (p : ℝ) = q := by
      have hπ := Real.pi_pos
      field_simp at h; nlinarith [h]
    exact_mod_cast this
  obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
  simp only
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [vo, ite_true]
      rw [← integral_sinh_sq_half]; congr 1; funext t; ring
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simp only [ite_true, show k + 1 ≠ 0 from by omega, ite_false]
      rw [show (fun t => vo a 0 t * vo a (k + 1) t)
        = fun t => Real.sinh (t / 2) * Real.sin (omk a (k + 1) * t) by
          funext t; rw [vo_succ]; rfl]
      exact int_sinh_sin _
  · obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [show p + 1 ≠ 0 from by omega, ite_false, ite_true]
      rw [show (fun t => vo a (p + 1) t * vo a 0 t)
        = fun t => Real.sinh (t / 2) * Real.sin (omk a (p + 1) * t) by
          funext t; rw [vo_succ, mul_comm]; rfl]
      exact int_sinh_sin _
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      simp only [show p + 1 ≠ 0 from by omega, show q + 1 ≠ 0 from by omega, ite_false]
      simp only [vo_succ]
      by_cases hpq : p = q
      · subst hpq
        simp only [ite_true]
        exact int_sin_sq (hω (p + 1) (by omega)).ne'
      · simp only [show p + 1 ≠ q + 1 from by omega, ite_false]
        have hm : omk a (p + 1) - omk a (q + 1) ≠ 0 := fun h => hpq (by
          have := hωinj (p + 1) (q + 1) (by linarith); omega)
        have hpl : omk a (p + 1) + omk a (q + 1) ≠ 0 := by
          have := hω (p + 1) (by omega); have := hω (q + 1) (by omega); linarith
        exact int_sin_sin hm hpl

/-! ## F. Monotonicity of the general form in the support: `weilQg_mono`, `OProbe.mono` (ParitySplit) -/

/-! ## G. The tail level from a certified `Cin` value -/

/-- If `T ≤ Cin(Mπ/2)`, every mode `n ≥ M` has `ψ_n − w_n ≥ T − err(a) − Σ c_n`. -/
theorem tail_Wp {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {M : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hC : T ≤ Cin (M * π / 2)) (K : ℕ) (n : ℤ) (hn : (M : ℤ) ≤ n) :
    T - errK a - ∑ k ∈ Finset.range K, cwΛ k ≤ modeE a n - wP a K n := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hnr : (M : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hC' : Cin (M * π / 2) ≤ Cin (π * n / 2) :=
    Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  have hπ := Real.pi_gt_three
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by nlinarith)
  have h2 : 2 / (π * n) ≤ 1 := by rw [div_le_one (by nlinarith)]; nlinarith
  have hD : 0 ≤ a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) := mul_nonneg ha.le (by linarith)
  have hw := wP_le a K n
  linarith

/-! ## H. From a certificate at one support to every smaller support -/

/-- The tail level `τ = T − err(b) − Σ_{n<K} c_n`. -/
def tauW (b T : ℝ) (K : ℕ) : ℝ := T - errK b - ∑ k ∈ Finset.range K, cwΛ k

/-- `κ = c₀ + Far(b) + τ`, with `Far` in closed form (`farField_eq`). -/
def kappaW (b T : ℝ) (K : ℕ) : ℝ :=
  weilConst + (-Real.log ((Real.exp b - 1) / (Real.exp b + 1)) + (π / 2 - Real.arctan (Real.sinh b)))
    + tauW b T K

theorem log_le_of_lt_K {b : ℝ} (hb : 0 < b) {K : ℕ} (hKlo : Real.log ((K - 1 : ℕ) : ℝ) ≤ 2 * b) :
    ∀ n, n < K → Real.log n ≤ 2 * b := fun n hn' => by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp; linarith
  · exact (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast (by omega : n ≤ K - 1))).trans hKlo

/-- **The even certificate theorem**: a positive-definite Gram matrix and
`(κ − ε)G + G diag(s) G ⪰ 0` at the support `b` give `Q(g) ≥ ε` for every normalised even probe at every
support `a ≤ b`. The prime side is every `n < K` (`log(K−1) ≤ 2b < log K`); the tail is `T ≤ Cin((N+1)π/2)`. -/
theorem weilQ_ge_of_certW {b T ε : ℝ} {K N : ℕ} (hb : 0 < b) (hb1 : b ≤ 1) (hK1 : 1 ≤ K)
    (hKlo : Real.log ((K - 1 : ℕ) : ℝ) ≤ 2 * b) (hKhi : 2 * b < Real.log K)
    (hC : T ≤ Cin ((N + 1 : ℕ) * π / 2)) (ψl : ℕ → ℝ)
    (hlow : ∀ k : ℕ, k < N → ψl (k + 1) ≤ modeE b ((k : ℤ) + 1))
    (hG : (Matrix.of fun i j : Fin (N + 2) => gC b i j).PosDef) (hκ : ε ≤ kappaW b T K)
    (hM : ((kappaW b T K - ε) • (Matrix.of fun i j : Fin (N + 2) => gC b i j)
      + (Matrix.of fun i j : Fin (N + 2) => gC b i j)
        * diagonal (fun i : Fin (N + 2) => sfunW b (tauW b T K) (wP b K) ψl i)
        * (Matrix.of fun i j : Fin (N + 2) => gC b i j)).PosSemidef)
    {a : ℝ} (ha : 0 < a) (hab : a ≤ b) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) :
    ε ≤ weilQ a g := by
  rw [← weilQ_mono ha.le hab hp]
  have hp' := hp.mono hab
  have hgram : (Matrix.of fun i j : Fin (N + 2) => gC b i j) = gramM b (N + 2) := by
    ext i j; simp only [Matrix.of_apply]; exact (gramM_eq hb (N + 2) i j).symm
  rw [hgram] at hG hM
  have hq := quad_lower (gramM b (N + 2)) hG _ (xv b g (N + 2)) (nrm := normSq g)
    (bessel_gram hb.le hp'.memL2 hp'.supp (N + 2)) hκ hM
  have hW := hasSum_wP hb hp'.toS hn (log_le_of_lt_K hb hKlo)
  have hr := weilQ_ge_relaxW hb hp' hn (wP b K) (wP_neg b K) hW (primeS_range hp'.toS hK1 hKhi) N
    (tauW b T K) ψl (fun n hn' => tail_Wp hb hb1 (M := N + 1) (by omega) hC K n (by push_cast; omega)) hlow
  rw [farField_eq hb] at hr
  rw [hn] at hq
  unfold kappaW at hq
  simp only [mul_one] at hq
  linarith

/-- **The odd certificate theorem**: the same, for normalised odd probes and the general form `weilQg`. -/
theorem weilQodd_ge_of_certW {b T ε : ℝ} {K N : ℕ} (hb : 0 < b) (hb1 : b ≤ 1) (hK1 : 1 ≤ K)
    (hKlo : Real.log ((K - 1 : ℕ) : ℝ) ≤ 2 * b) (hKhi : 2 * b < Real.log K)
    (hC : T ≤ Cin ((N + 1 : ℕ) * π / 2)) (ψl : ℕ → ℝ)
    (hlow : ∀ k : ℕ, k < N → ψl (k + 1) ≤ modeE b ((k : ℤ) + 1))
    (hG : (Matrix.of fun i j : Fin (N + 1) => gCO b i j).PosDef) (hκ : ε ≤ kappaW b T K)
    (hM : ((kappaW b T K - ε) • (Matrix.of fun i j : Fin (N + 1) => gCO b i j)
      + (Matrix.of fun i j : Fin (N + 1) => gCO b i j)
        * diagonal (fun i : Fin (N + 1) => sfunO b (tauW b T K) (wP b K) ψl i)
        * (Matrix.of fun i j : Fin (N + 1) => gCO b i j)).PosSemidef)
    {a : ℝ} (ha : 0 < a) (hab : a ≤ b) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) :
    ε ≤ weilQg a g := by
  rw [← weilQg_mono ha.le hab hp.supp]
  have hp' := hp.mono hab
  have hgram : (Matrix.of fun i j : Fin (N + 1) => gCO b i j) = gramV (vo b) b (N + 1) := by
    ext i j; simp only [Matrix.of_apply]; exact (gramO_eq hb (N + 1) i j).symm
  rw [hgram] at hG hM
  have hq := quad_lower (gramV (vo b) b (N + 1)) hG _ (xV (vo b) g (N + 1)) (nrm := normSq g)
    (bessel_V (vo_cont b) hb.le hp'.memL2 hp'.supp (N + 1)) hκ hM
  have hW := hasSum_wP hb hp'.toS hn (log_le_of_lt_K hb hKlo)
  have hr := weilQodd_ge_relaxW hb hp' hn (wP b K) (wP_neg b K) hW (primeS_range hp'.toS hK1 hKhi) N
    (tauW b T K) ψl (fun n hn' => tail_Wp hb hb1 (M := N + 1) (by omega) hC K n (by push_cast; omega)) hlow
  have hx : xo b g (N + 1) = xV (vo b) g (N + 1) := rfl
  rw [farField_eq hb, hx] at hr
  rw [hn] at hq
  unfold kappaW at hq
  simp only [mul_one] at hq
  linarith

/-- A bound on normalised odd probes is a bound `c‖g‖² ≤ Q(g)` on all of them. -/
theorem weilQodd_ge_mul_of {a c : ℝ} (h : ∀ g, OProbe a g → normSq g = 1 → c ≤ weilQg a g)
    {g : ℝ → ℝ} (hp : OProbe a g) : c * normSq g ≤ weilQg a g := by
  rcases (normSq_nonneg g).lt_or_eq with hpos | h0
  · set k := 1 / Real.sqrt (normSq g)
    have hc2 : k ^ 2 * normSq g = 1 := by
      simp only [k]; rw [div_pow, Real.sq_sqrt hpos.le]; field_simp
    have h1 := h _ (hp.smul k) (by rw [normSq_smul]; exact hc2)
    rw [weilQg_smul] at h1
    have hc0 : 0 < k ^ 2 := by positivity
    have e : c * normSq g * k ^ 2 = c := by rw [mul_assoc, mul_comm (normSq g), hc2, mul_one]
    have : c * normSq g * k ^ 2 ≤ weilQg a g * k ^ 2 := by rw [e, mul_comm]; exact h1
    exact le_of_mul_le_mul_right this hc0
  · have hz := ae_zero_of_normSq hp.memL2 h0.symm
    have hf : ∀ u, autocorr g u = 0 := fun u => by
      rw [autocorr_congr_ae hz u]; simp [autocorr]
    have hA : archE g = 0 := by
      unfold archE archIntegrand; simp [hf]
    have hS : primeS g = 0 := by unfold primeS; simp [hf]
    have hR : poleR g a = 0 := by rw [poleR_congr_ae hz]; simp [poleR]
    unfold weilQg; rw [hA, hS, hR, ← h0]; norm_num

/-- **Both parities**: sector bounds `ε_e`, `ε_o` on normalised probes give `min(ε_e, ε_o)‖g‖² ≤ Q(g)` for every
real `g` supported in `[−a, a]` (`weilQg_parity`). -/
theorem weilQg_ge_min {a εe εo : ℝ} (ha : 0 < a)
    (he : ∀ g, Probe a g → normSq g = 1 → εe ≤ weilQ a g)
    (ho : ∀ g, OProbe a g → normSq g = 1 → εo ≤ weilQg a g) {g : ℝ → ℝ} (hg : SProbe a g) :
    min εe εo * normSq g ≤ weilQg a g := by
  rw [weilQg_parity hg, normSq_parity hg.memL2]
  have h1 := weilQ_ge_mul ha he (probe_evenPart hg)
  have h2 := weilQodd_ge_mul_of ho (oprobe_oddPart hg)
  have m1 := min_le_left εe εo
  have m2 := min_le_right εe εo
  nlinarith [normSq_nonneg (evenPart g), normSq_nonneg (oddPart g)]

end Pilot1ca

#print axioms Pilot1ca.trunc_W
#print axioms Pilot1ca.primeS_range
#print axioms Pilot1ca.weilQ_ge_relaxW
#print axioms Pilot1ca.weilQodd_ge_relaxW
#print axioms Pilot1ca.gramO_eq
#print axioms Pilot1ca.weilQg_mono
#print axioms Pilot1ca.weilQ_ge_of_certW
#print axioms Pilot1ca.weilQodd_ge_of_certW
#print axioms Pilot1ca.weilQg_ge_min
