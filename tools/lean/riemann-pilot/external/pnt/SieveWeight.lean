/-
# Round 591: Lemma 1 of the sieve route for primes, with weights uniform in the scale

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`norm_Sp_le`). Let `f0` be smooth and real with support in `[1/2, 2]`, and `K ≥ 0` an integer.
There are `B, C ≥ 0` such that for every `q ≥ 1`, `χ ≠ 1` mod `q`, `½ ≤ θ ≤ 11/12`, `0 < δ ≤ 1/24`, `H ≥ 0`, `P ≥ 4`
and real `y`: if `L(·, χ)` has no zero in `Re s > θ`, `|Im s − y| < H + 1`, then
`|Σ_{p ≤ 2P} χ(p)(p/P)^{−iy}f0(p/P)| ≤ M A B(P^{θ+δ} + P^{11/12+δ}(1 + H)^{−K})/log P + C(⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)`,
with `N = ⌊2P⌋`, `M = KL(θ, θ + δ) + KL(11/12, 11/12 + δ)` and `A = log(q + 2) + log(|y| + 4) + 1`.

The weight `ψ_P(u) = f0(u)(1 + log u/log P)⁻¹` has `f0(n/P)/log n = ψ_P(n/P)/log P`, so the prime sum is
`1/log P` times `Σ_n χ(n)Λ(n)(n/P)^{−iy}ψ_P(n/P)`, less the proper prime powers' share (`Sw_wy_eq`), and
`SieveLemma1.norm_Sw_le` bounds that sum once `𝓜ψ_P` decays uniformly in `P` (`exists_mellin_bound`).

* `exists_bound_iteratedDeriv_gw`: in the variable `v = −log u`, `e^{−σv}ψ_P(e^{−v}) = e^{−σv}f0(e^{−v})(1 − av)⁻¹`
  with `a = 1/log P ≤ 1/log 4`. For `0 ≤ σ ≤ 2` its `k`-th derivative is zero outside `[−log 2, log 2]` and bounded
  on it by a constant that depends on `f0` and `k` only: Leibniz's rule, with
  `(d/dv)^k(1 − av)⁻¹ = k!a^k(1 − av)^{−1−k}` (Mathlib's `iter_deriv_inv_linear`) and `1 − av ≥ 1/2` there.
* `exists_mellin_bound`: `(1 + |t|)^{K+3}|𝓜ψ_P(σ + it)| ≤ B` for `0 ≤ σ ≤ 2` and `P ≥ 4`, by Mathlib's
  `mellin_eq_fourier` and `SieveSmooth.pow_mul_norm_fourier_le`.
* `mellinConvergent_psiw`, `differentiableAt_mellin_psiw`: for `P ≥ 4`, `𝓜ψ_P` converges and is holomorphic
  everywhere.
* `norm_Sw_wy_le`: `SieveLemma1.norm_Sw_le` for `w(u) = u^{−iy}ψ_P(u)`, whose Mellin transform is `𝓜ψ_P(s − iy)`.
* `card_properPrimePow_le`, `Sw_wy_eq`, `norm_Sp_le`: the primes, with at most `(⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)` proper
  prime powers up to `N`.
-/
import SieveLemma1
import SieveSmooth

open Complex Set Real Filter Topology MeasureTheory FourierTransform
open scoped Nat ContDiff

noncomputable section

namespace SieveWeight

/-! ### The factor `(1 − av)⁻¹` -/

/-- `(d/dv)^k (1 − av)⁻¹ = k!a^k(1 − av)^{−1−k}` (Mathlib's `iter_deriv_inv_linear`). -/
lemma iteratedDeriv_inv_one_sub (a : ℝ) (k : ℕ) (v : ℝ) :
    iteratedDeriv k (fun v : ℝ => (1 - a * v)⁻¹) v = k ! * a ^ k * (1 - a * v) ^ (-1 - k : ℤ) := by
  have e : (fun v : ℝ => (1 - a * v)⁻¹) = fun x => (-a * x + 1)⁻¹ := by funext x; ring_nf
  rw [iteratedDeriv_eq_iterate, e, iter_deriv_inv_linear k (-a) 1]
  have e2 : -a * v + 1 = 1 - a * v := by ring
  have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  simp only [e2, neg_pow a k]
  calc (-1) ^ k * (k ! : ℝ) * ((-1) ^ k * a ^ k) * (1 - a * v) ^ (-1 - k : ℤ)
      = ((-1 : ℝ) ^ k * (-1) ^ k) * (k ! * a ^ k * (1 - a * v) ^ (-1 - k : ℤ)) := by ring
    _ = k ! * a ^ k * (1 - a * v) ^ (-1 - k : ℤ) := by rw [h1, one_mul]

/-- `|(d/dv)^k (1 − av)⁻¹| ≤ k!2^{k+1}` where `0 ≤ a ≤ 1` and `av ≤ 1/2`. -/
lemma abs_iteratedDeriv_inv_one_sub_le {a v : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hav : a * v ≤ 1 / 2) (k : ℕ) :
    |iteratedDeriv k (fun v : ℝ => (1 - a * v)⁻¹) v| ≤ k ! * 2 ^ (k + 1) := by
  rw [iteratedDeriv_inv_one_sub]
  have h0 : (1 / 2 : ℝ) ≤ 1 - a * v := by linarith
  have hpos : 0 < 1 - a * v := by linarith
  have hz : (1 - a * v) ^ (-1 - k : ℤ) = ((1 - a * v) ^ (k + 1))⁻¹ := by
    rw [show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [hz]
  have hak : a ^ k ≤ 1 := pow_le_one₀ ha ha1
  have hinv : ((1 - a * v) ^ (k + 1))⁻¹ ≤ 2 ^ (k + 1) := by
    rw [inv_le_comm₀ (by positivity) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hf : (0 : ℝ) ≤ k ! := by positivity
  rw [abs_of_nonneg (by positivity)]
  calc (k ! : ℝ) * a ^ k * ((1 - a * v) ^ (k + 1))⁻¹ ≤ k ! * 1 * 2 ^ (k + 1) := by gcongr
    _ = k ! * 2 ^ (k + 1) := by ring

/-! ### The weight in the variable `v = −log u` -/

variable {f0 : ℝ → ℝ}

/-- `b(v) = f0(e^{−v})`. -/
def bw (f0 : ℝ → ℝ) (v : ℝ) : ℝ := f0 (Real.exp (-v))

/-- `g(v) = e^{−σv}f0(e^{−v})(1 − av)⁻¹`. -/
def gw (f0 : ℝ → ℝ) (σ a v : ℝ) : ℝ := Real.exp (-σ * v) * bw f0 v * (1 - a * v)⁻¹

lemma bw_eq_zero (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) {v : ℝ} (hv : Real.log 2 < |v|) : bw f0 v = 0 := by
  by_contra h
  have hm := hsupp h
  rw [mem_Icc] at hm
  have h2 : (0 : ℝ) < 2 := by norm_num
  rcases lt_abs.1 hv with hv' | hv'
  · -- `v > Real.log 2`: `e^{−v} < 1/2`
    have : Real.exp (-v) < 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by rw [Real.exp_neg, Real.exp_log h2]; norm_num]
      exact Real.exp_lt_exp.2 (by linarith)
    linarith [hm.1]
  · -- `v < −Real.log 2`: `e^{−v} > 2`
    have : 2 < Real.exp (-v) := by
      rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log h2]]
      exact Real.exp_lt_exp.2 (by linarith)
    linarith [hm.2]

lemma contDiff_bw (hf0 : ContDiff ℝ ∞ f0) : ContDiff ℝ ∞ (bw f0) :=
  hf0.comp (Real.contDiff_exp.comp contDiff_neg)

/-- `b` vanishes near every `v` with `|v| > Real.log 2`. -/
lemma bw_eventually_zero (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) {v : ℝ} (hv : Real.log 2 < |v|) :
    bw f0 =ᶠ[𝓝 v] fun _ => 0 := by
  have hopen : IsOpen {w : ℝ | Real.log 2 < |w|} := isOpen_lt continuous_const continuous_abs
  filter_upwards [hopen.mem_nhds hv] with w hw
  exact bw_eq_zero hsupp hw

lemma gw_eventually_zero (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (σ a : ℝ) {v : ℝ} (hv : Real.log 2 < |v|) :
    gw f0 σ a =ᶠ[𝓝 v] fun _ => 0 := by
  filter_upwards [bw_eventually_zero hsupp hv] with w hw
  simp [gw, hw]

/-- `g` is smooth for `0 ≤ a ≤ 1/Real.log 4`: where `av < 1` the factors are, and elsewhere `v ≥ Real.log 4`, where `g`
vanishes nearby. -/
lemma contDiff_gw (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (σ : ℝ) {a : ℝ}
    (ha : 0 ≤ a) (ha4 : a * Real.log 4 ≤ 1) : ContDiff ℝ ∞ (gw f0 σ a) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : a * v < 1
  · have h1 : ContDiffAt ℝ ∞ (fun v : ℝ => Real.exp (-σ * v)) v :=
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (bw f0) v := (contDiff_bw hf0).contDiffAt
    have h3 : ContDiffAt ℝ ∞ (fun v : ℝ => (1 - a * v)⁻¹) v :=
      (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv (fun h => by simp only [id] at h; linarith)
    exact (h1.mul h2).mul h3
  · have hl2 : Real.log 2 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv' : Real.log 2 < |v| := by
      have ha0 : 0 < a := by
        rcases ha.lt_or_eq with h | h
        · exact h
        · rw [← h] at hv; simp at hv
      have : Real.log 4 ≤ v := by
        by_contra h
        push Not at h
        have : a * v < a * Real.log 4 := mul_lt_mul_of_pos_left h ha0
        linarith
      rw [abs_of_pos (by linarith)]; linarith
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (gw_eventually_zero hsupp σ a hv')

/-! ### Bounds uniform in `σ ∈ [0, 2]` and `a ∈ [0, 1/log 4]` -/

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

lemma mul_le_half {a v : ℝ} (ha : 0 ≤ a) (ha4 : a * Real.log 4 ≤ 1) (hv : v ≤ Real.log 2) : a * v ≤ 1 / 2 := by
  have h1 : a * v ≤ a * Real.log 2 := mul_le_mul_of_nonneg_left hv ha
  rw [log_four] at ha4
  linarith

lemma exp_neg_mul_le_four {σ v : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) (hv : -Real.log 2 ≤ v) :
    Real.exp (-σ * v) ≤ 4 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : -σ * v ≤ Real.log 4 := by
    rw [log_four]
    nlinarith [mul_nonneg hσ0 (by linarith : 0 ≤ Real.log 2 + v), mul_nonneg (by linarith : 0 ≤ 2 - σ) hl2.le]
  calc Real.exp (-σ * v) ≤ Real.exp (Real.log 4) := Real.exp_le_exp.2 h
    _ = 4 := Real.exp_log (by norm_num)

lemma not_mem_Icc_log {v : ℝ} (hv : v ∉ Icc (-Real.log 2) (Real.log 2)) : Real.log 2 < |v| := by
  rw [mem_Icc, not_and_or] at hv
  rcases hv with h | h
  · push Not at h
    rw [abs_of_neg (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])]; linarith
  · push Not at h
    rw [abs_of_pos (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])]; linarith

/-- Each derivative of `b` is bounded. -/
lemma exists_bound_iteratedDeriv_bw (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2)
    (m : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ v, |iteratedDeriv m (bw f0) v| ≤ M := by
  have hc : Continuous (iteratedDeriv m (bw f0)) :=
    (contDiff_bw hf0).continuous_iteratedDeriv m (by exact_mod_cast le_top)
  have hs : HasCompactSupport (iteratedDeriv m (bw f0)) := by
    refine HasCompactSupport.intro (K := Icc (-Real.log 2) (Real.log 2)) isCompact_Icc fun v hv => ?_
    rw [(bw_eventually_zero hsupp (not_mem_Icc_log hv)).iteratedDeriv_eq m]
    simp
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun v => (Real.norm_eq_abs _ ▸ hC v).trans (le_max_left _ _)⟩

/-- **The derivatives of `g`**, uniformly: there are `G k` such that `|g^{(k)}(v)| ≤ G k` for `0 ≤ σ ≤ 2`,
`0 ≤ a ≤ 1/log 4` and every `v`; `g^{(k)}` vanishes outside `[−log 2, log 2]`, and on it Leibniz's rule bounds it by
the derivatives of `e^{−σv}` (at most `2^j·4`), of `b` and of `(1 − av)⁻¹` (at most `j!2^{j+1}`). -/
theorem exists_bound_iteratedDeriv_gw (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) :
    ∃ G : ℕ → ℝ, ∀ k, 0 ≤ G k ∧ ∀ σ a v : ℝ, 0 ≤ σ → σ ≤ 2 → 0 ≤ a → a * Real.log 4 ≤ 1 →
      |iteratedDeriv k (gw f0 σ a) v| ≤ G k := by
  choose Mb hMb0 hMb using exists_bound_iteratedDeriv_bw hf0 hsupp
  set D : ℕ → ℝ := fun i => ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 ^ j * 4) * Mb (i - j) with hD
  have hD0 : ∀ i, 0 ≤ D i := fun i => Finset.sum_nonneg fun j _ => by have := hMb0 (i - j); positivity
  refine ⟨fun k => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * D i * ((k - i)! * 2 ^ (k - i + 1)), fun k => ?_⟩
  refine ⟨Finset.sum_nonneg fun i _ => by have := hD0 i; positivity, fun σ a v hσ0 hσ2 ha ha4 => ?_⟩
  by_cases hv : v ∈ Icc (-Real.log 2) (Real.log 2)
  · -- Leibniz's rule on `U = (−log 3, log 3)`, where `(1 − av)⁻¹` is smooth
    set U : Set ℝ := Ioo (-Real.log 3) (Real.log 3) with hU
    have hl23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    have hl34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hvU : v ∈ U := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hUo : IsOpen U := isOpen_Ioo
    have hlt : ∀ w ∈ U, a * w < 1 := by
      intro w hw
      have h1 : a * w ≤ a * Real.log 3 := mul_le_mul_of_nonneg_left hw.2.le ha
      have h2 : a * Real.log 3 ≤ a * Real.log 4 := mul_le_mul_of_nonneg_left hl34.le ha
      rcases ha.lt_or_eq with ha' | ha'
      · have : a * Real.log 3 < a * Real.log 4 := mul_lt_mul_of_pos_left hl34 ha'
        linarith
      · rw [← ha']; norm_num
    set d : ℝ → ℝ := fun w => Real.exp (-σ * w) * bw f0 w with hd
    set c : ℝ → ℝ := fun w => (1 - a * w)⁻¹ with hc
    have hdc : gw f0 σ a = fun w => d w * c w := by funext w; simp [gw, hd, hc]
    have hdC : ContDiff ℝ ∞ d := (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (contDiff_bw hf0)
    have hcC : ContDiffOn ℝ ∞ c U := fun w hw =>
      ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv
        (fun h => by simp only [id] at h; linarith [hlt w hw])).contDiffWithinAt
    have hL := norm_iteratedFDerivWithin_mul_le hdC.contDiffOn hcC hUo.uniqueDiffOn hvU (n := k)
      (by exact_mod_cast le_top)
    rw [← hdc, iteratedFDerivWithin_of_isOpen k hUo hvU, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs] at hL
    refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
    rw [iteratedFDerivWithin_of_isOpen i hUo hvU, iteratedFDerivWithin_of_isOpen (k - i) hUo hvU,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Real.norm_eq_abs]
    -- the derivatives of `d`
    have hdi : |iteratedDeriv i d v| ≤ D i := by
      have hL2 := norm_iteratedFDeriv_mul_le (f := fun w => Real.exp (-σ * w)) (g := bw f0)
        (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)) (contDiff_bw hf0) v (n := i)
        (by exact_mod_cast le_top)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hL2
      refine hL2.trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        Real.norm_eq_abs, iteratedDeriv_exp_const_mul]
      have he : |(-σ) ^ j * Real.exp (-σ * v)| ≤ 2 ^ j * 4 := by
        rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hσ0, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (pow_le_pow_left₀ hσ0 hσ2 j) (exp_neg_mul_le_four hσ0 hσ2 hv.1) (by positivity)
          (by positivity)
      have := hMb (i - j) v
      gcongr
    -- the derivatives of `c`
    have hci : |iteratedDeriv (k - i) c v| ≤ (k - i)! * 2 ^ (k - i + 1) :=
      abs_iteratedDeriv_inv_one_sub_le ha (by
        have h4 : 1 ≤ Real.log 4 := by linarith [Real.log_two_gt_d9, log_four]
        nlinarith) (mul_le_half ha ha4 hv.2) (k - i)
    have := hD0 i
    gcongr
  · -- outside `[−log 2, log 2]` the derivative vanishes
    rw [(gw_eventually_zero hsupp σ a (not_mem_Icc_log hv)).iteratedDeriv_eq k, iteratedDeriv_const]
    have h0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * D i * ((k - i)! * 2 ^ (k - i + 1)) :=
      Finset.sum_nonneg fun i _ => by have := hD0 i; positivity
    split_ifs <;> simpa using h0

/-! ### The Mellin transform of the weight -/

/-- `ψ_P(u) = f0(u)(1 + log u/log P)⁻¹`, complex-valued. -/
def psiw (f0 : ℝ → ℝ) (P : ℝ) (u : ℝ) : ℂ := ((f0 u * (1 + Real.log u / Real.log P)⁻¹ : ℝ) : ℂ)

/-- The derivatives of a real function, seen in `ℂ`. -/
lemma iteratedDeriv_ofReal {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun x => (g x : ℂ)) x = ((iteratedDeriv n g x : ℝ) : ℂ) := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left Complex.ofRealCLM hg.contDiffAt (x := x) (i := n)
    (by exact_mod_cast le_top)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have e : (fun x => (g x : ℂ)) = Complex.ofRealCLM ∘ g := rfl
  rw [e, h]
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, Complex.ofRealCLM_apply]

lemma gw_log (P σ v : ℝ) :
    (Real.exp (-σ * v) : ℂ) * psiw f0 P (Real.exp (-v)) = (gw f0 σ (1 / Real.log P) v : ℂ) := by
  have e : (1 + -v / Real.log P) = (1 - 1 / Real.log P * v) := by ring
  rw [psiw, gw, bw, Real.log_exp, e]
  push_cast
  ring

/-- `𝓜ψ_P(σ + it)` is the Fourier transform of `g` at `t/2π`, `a = 1/log P` (Mathlib's `mellin_eq_fourier`). -/
lemma mellin_psiw_eq_fourier (P σ t : ℝ) :
    mellin (psiw f0 P) (σ + t * I) = 𝓕 (fun v => (gw f0 σ (1 / Real.log P) v : ℂ)) (t / (2 * π)) := by
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have him : ((σ : ℂ) + t * I).im = t := by simp
  have hfun : (fun u : ℝ => Real.exp (-σ * u) • psiw f0 P (Real.exp (-u))) =
      fun v => (gw f0 σ (1 / Real.log P) v : ℂ) := by
    funext v; rw [← gw_log P σ v, Complex.real_smul]
  rw [hre, him, hfun]

/-- `∫ |h| ≤ 2 log 2 · G` for `h` continuous, zero outside `[−log 2, log 2]` and at most `G` there. -/
lemma integral_norm_le_of_vanish {h : ℝ → ℂ} (hc : Continuous h) {G : ℝ}
    (h0 : ∀ x, x ∉ Icc (-Real.log 2) (Real.log 2) → h x = 0) (hG : ∀ x, ‖h x‖ ≤ G) :
    ∫ x, ‖h x‖ ≤ 2 * Real.log 2 * G := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : ∫ x in Icc (-Real.log 2) (Real.log 2), ‖h x‖ = ∫ x, ‖h x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [h0 x hx]
  rw [← e]
  calc ∫ x in Icc (-Real.log 2) (Real.log 2), ‖h x‖ ≤ ∫ _ in Icc (-Real.log 2) (Real.log 2), G :=
        setIntegral_mono_on (hc.norm.integrableOn_Icc) (integrableOn_const (by simp)) measurableSet_Icc
          fun x _ => hG x
    _ = 2 * Real.log 2 * G := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]; ring

/-- **The Mellin transform of `ψ_P`, uniformly in `P ≥ 4`**: for every `K` there is `B` with
`(1 + |t|)^{K+3}|𝓜ψ_P(σ + it)| ≤ B` for `0 ≤ σ ≤ 2`, from `|t|^j|𝓜ψ_P(σ + it)| ≤ ∫|g^{(j)}|` at `j = 0` and
`j = K + 3` (`SieveSmooth.pow_mul_norm_fourier_le`) and `exists_bound_iteratedDeriv_gw`. -/
theorem exists_mellin_bound (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ P σ t : ℝ, 4 ≤ P → 0 ≤ σ → σ ≤ 2 →
      (1 + |t|) ^ (K + 3) * ‖mellin (psiw f0 P) (σ + t * I)‖ ≤ B := by
  obtain ⟨G, hG⟩ := exists_bound_iteratedDeriv_gw hf0 hsupp
  refine ⟨2 ^ (K + 3) * (2 * Real.log 2 * G 0 + 2 * Real.log 2 * G (K + 3)), ?_, ?_⟩
  · have h1 := (hG 0).1
    have h2 := (hG (K + 3)).1
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2))
  intro P σ t hP hσ0 hσ2
  have hlP : Real.log 4 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlP0 : Real.log P ≠ 0 := by linarith
  set a := 1 / Real.log P with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg zero_le_one (by linarith)
  have ha4 : a * Real.log 4 ≤ 1 := by
    rw [ha, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; exact hlP
  set f : ℝ → ℂ := fun v => (gw f0 σ a v : ℂ) with hf
  have hgC : ContDiff ℝ ∞ (gw f0 σ a) := contDiff_gw hf0 hsupp σ ha0 ha4
  have hfC : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hgC
  have hvan : ∀ n : ℕ, ∀ x, x ∉ Icc (-Real.log 2) (Real.log 2) → iteratedDeriv n f x = 0 := by
    intro n x hx
    rw [iteratedDeriv_ofReal hgC, (gw_eventually_zero hsupp σ a (not_mem_Icc_log hx)).iteratedDeriv_eq n,
      iteratedDeriv_const]
    split_ifs <;> simp
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n f) := by
    intro n
    refine (hfC.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro (K := Icc (-Real.log 2) (Real.log 2)) isCompact_Icc (hvan n)
  have hbound : ∀ j : ℕ, |t| ^ j * ‖mellin (psiw f0 P) (σ + t * I)‖ ≤ 2 * Real.log 2 * G j := by
    intro j
    have h := SieveSmooth.pow_mul_norm_fourier_le (f := f) (K := j) (hfC.of_le (by exact_mod_cast le_top))
      (fun n _ => hint n) (t / (2 * π))
    have hpi : 0 < π := Real.pi_pos
    have e1 : 2 * π * |t / (2 * π)| = |t| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]; field_simp
    rw [e1, ← mellin_psiw_eq_fourier P σ t] at h
    refine h.trans (integral_norm_le_of_vanish (hfC.continuous_iteratedDeriv j (by exact_mod_cast le_top))
      (hvan j) fun x => ?_)
    rw [iteratedDeriv_ofReal hgC, Complex.norm_real, Real.norm_eq_abs]
    exact (hG j).2 σ a x hσ0 hσ2 ha0 ha4
  have h0 := hbound 0
  have hK := hbound (K + 3)
  rw [pow_zero, one_mul] at h0
  have hm0 : 0 ≤ ‖mellin (psiw f0 P) (σ + t * I)‖ := norm_nonneg _
  have hpow : (1 + |t|) ^ (K + 3) ≤ 2 ^ (K + 3) * (1 + |t| ^ (K + 3)) := by
    have ht0 : 0 ≤ |t| := abs_nonneg t
    rcases le_total |t| 1 with h1 | h1
    · calc (1 + |t|) ^ (K + 3) ≤ 2 ^ (K + 3) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ ≤ 2 ^ (K + 3) * (1 + |t| ^ (K + 3)) := by
            have : 0 ≤ |t| ^ (K + 3) := by positivity
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (K + 3)]
    · calc (1 + |t|) ^ (K + 3) ≤ (2 * |t|) ^ (K + 3) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 2 ^ (K + 3) * |t| ^ (K + 3) := mul_pow _ _ _
        _ ≤ 2 ^ (K + 3) * (1 + |t| ^ (K + 3)) := by
            have : (0 : ℝ) < 2 ^ (K + 3) := by positivity
            nlinarith
  calc (1 + |t|) ^ (K + 3) * ‖mellin (psiw f0 P) (σ + t * I)‖
      ≤ 2 ^ (K + 3) * (1 + |t| ^ (K + 3)) * ‖mellin (psiw f0 P) (σ + t * I)‖ := by gcongr
    _ = 2 ^ (K + 3) * (‖mellin (psiw f0 P) (σ + t * I)‖ + |t| ^ (K + 3) * ‖mellin (psiw f0 P) (σ + t * I)‖) := by
        ring
    _ ≤ 2 ^ (K + 3) * (2 * Real.log 2 * G 0 + 2 * Real.log 2 * G (K + 3)) := by gcongr

/-! ### Convergence and holomorphy of the Mellin transform -/

lemma psiw_eq_zero (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (P : ℝ) {u : ℝ} (hu : u ∉ Icc (1 / 2) 2) :
    psiw f0 P u = 0 := by
  have h : f0 u = 0 := Function.notMem_support.1 fun h => hu (hsupp h)
  simp [psiw, h]

/-- On `u > 0`, `ψ_P(u) = g(−log u)` at `σ = 0`, `a = 1/log P`. -/
lemma psiw_eq_gw (P : ℝ) {u : ℝ} (hu : 0 < u) : psiw f0 P u = (gw f0 0 (1 / Real.log P) (-Real.log u) : ℂ) := by
  simp only [psiw, gw, bw, neg_neg, Real.exp_log hu, neg_zero, zero_mul, Real.exp_zero, one_mul]
  push_cast
  ring_nf

lemma continuousAt_psiw (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) {P : ℝ}
    (hP : 4 ≤ P) {u : ℝ} (hu : 0 < u) : ContinuousAt (psiw f0 P) u := by
  have hlP : Real.log 4 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ 1 / Real.log P := div_nonneg zero_le_one (by linarith)
  have ha4 : 1 / Real.log P * Real.log 4 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; exact hlP
  have hg := (contDiff_gw hf0 hsupp 0 ha0 ha4).continuous
  have hc : ContinuousAt (fun u : ℝ => (gw f0 0 (1 / Real.log P) (-Real.log u) : ℂ)) u :=
    Complex.continuous_ofReal.continuousAt.comp (hg.continuousAt.comp
      (Real.continuousAt_log hu.ne').neg)
  refine hc.congr ?_
  filter_upwards [Ioi_mem_nhds hu] with w hw
  exact (psiw_eq_gw P hw).symm

lemma psiw_eventually_zero_atTop (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (P : ℝ) :
    psiw f0 P =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop 2] with u hu
  exact psiw_eq_zero hsupp P fun h => by linarith [h.2]

lemma psiw_eventually_zero_zero (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (P : ℝ) :
    psiw f0 P =ᶠ[𝓝[>] 0] 0 := by
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with u hu
  exact psiw_eq_zero hsupp P fun h => by linarith [h.1, mem_Iio.1 hu]

lemma locallyIntegrableOn_psiw (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) {P : ℝ}
    (hP : 4 ≤ P) : LocallyIntegrableOn (psiw f0 P) (Ioi 0) :=
  ContinuousOn.locallyIntegrableOn (fun _u hu => (continuousAt_psiw hf0 hsupp hP hu).continuousWithinAt)
    measurableSet_Ioi

theorem mellinConvergent_psiw (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) {P : ℝ}
    (hP : 4 ≤ P) (s : ℂ) : MellinConvergent (psiw f0 P) s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) (locallyIntegrableOn_psiw hf0 hsupp hP)
    ((psiw_eventually_zero_atTop hsupp P).trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)
    ((psiw_eventually_zero_zero hsupp P).trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)

theorem differentiableAt_mellin_psiw (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2)
    {P : ℝ} (hP : 4 ≤ P) (s : ℂ) : DifferentiableAt ℂ (mellin (psiw f0 P)) s :=
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) (locallyIntegrableOn_psiw hf0 hsupp hP)
    ((psiw_eventually_zero_atTop hsupp P).trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)
    ((psiw_eventually_zero_zero hsupp P).trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)

/-! ### The weight at height `y` -/

/-- `w(u) = u^{−iy}ψ_P(u)`, so that `w(n/P) = P^{iy}n^{−iy}ψ_P(n/P)` and `𝓜w(s) = 𝓜ψ_P(s − iy)`. -/
def wy (f0 : ℝ → ℝ) (P y : ℝ) (u : ℝ) : ℂ := (u : ℂ) ^ (-(y : ℂ) * I) • psiw f0 P u

lemma mellin_wy (P y : ℝ) (s : ℂ) : mellin (wy f0 P y) s = mellin (psiw f0 P) (s + -(y : ℂ) * I) :=
  mellin_cpow_smul _ s _

/-- **Lemma 1 for the weights `ψ_P`, in `Λ` form, uniformly in `P ≥ 4`.** For every `K` there is `B` such that for
`χ ≠ 1`, `½ ≤ θ ≤ 11/12`, `0 < δ ≤ 1/24`, `H ≥ 0` and `P ≥ 4`, if `L(·, χ)` has no zero in `Re s > θ`,
`|Im s − y| < H + 1`, then `|Σ_n χ(n)Λ(n)w(n/P)| ≤ M A B(P^{θ+δ} + P^{11/12+δ}(1 + H)^{−K})`
(`SieveLemma1.norm_Sw_le` with `exists_mellin_bound`). -/
theorem norm_Sw_wy_le (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ θ δ H P y : ℝ,
      1 / 2 ≤ θ → θ ≤ 11 / 12 → 0 < δ → δ ≤ 1 / 24 → 0 ≤ H → 4 ≤ P →
      (∀ s : ℂ, θ < s.re → |s.im - y| < H + 1 → DirichletCharacter.LFunction χ s ≠ 0) →
      ‖SieveLemma1.Sw χ (wy f0 P y) P‖ ≤ (Linnik.KL θ (θ + δ) + Linnik.KL (11 / 12) (11 / 12 + δ)) *
        (Real.log (q + 2) + Real.log (|y| + 4) + 1) * B * (P ^ (θ + δ) + P ^ (11 / 12 + δ) * ((1 + H) ^ K)⁻¹) := by
  obtain ⟨B, hB0, hB⟩ := exists_mellin_bound hf0 hsupp K
  refine ⟨B, hB0, fun q _ χ hχ θ δ H P y hθ hθ1 hδ hδ1 hH hP hloc => ?_⟩
  have hP0 : 0 < P := by linarith
  refine SieveLemma1.norm_Sw_le hχ hθ hθ1 hδ hδ1 hH (by linarith) (fun u hu => ?_) ?_ (fun s _ => ?_)
    (fun σ hσ t => ?_) hloc
  · exact ((continuousAt_ofReal_cpow_const u _ (Or.inr hu.ne')).smul (continuousAt_psiw hf0 hsupp hP hu))
  · exact (MellinConvergent.cpow_smul).2 (mellinConvergent_psiw hf0 hsupp hP _)
  · have e : mellin (wy f0 P y) = fun s => mellin (psiw f0 P) (s + -(y : ℂ) * I) := funext (mellin_wy P y)
    rw [e]
    exact (differentiableAt_mellin_psiw hf0 hsupp hP _).comp s (differentiableAt_id.add_const _)
  · rw [mellin_wy]
    have e : (σ : ℂ) + t * I + -(y : ℂ) * I = σ + ((t - y : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact hB P σ (t - y) hP (by linarith [hσ.1]) hσ.2

/-! ### From `Λ` to the primes -/

/-- At most `(⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)` proper prime powers `p^k ≤ N`, `k ≥ 2`: each is `p^k` with `p ≤ ⌊√N⌋` and
`k ≤ ⌊log₂ N⌋`. -/
lemma card_properPrimePow_le (N : ℕ) :
    (((Finset.range (N + 1)).filter fun n => IsPrimePow n ∧ ¬ n.Prime).card : ℝ) ≤
      (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  have hsub : ((Finset.range (N + 1)).filter fun n => IsPrimePow n ∧ ¬ n.Prime) ⊆
      ((Finset.range (Nat.sqrt N + 1)) ×ˢ (Finset.range (Nat.log 2 N + 1))).image fun pk => pk.1 ^ pk.2 := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      rw [this, pow_one] at hnp
      exact hnp hp
    rw [Finset.mem_image]
    refine ⟨(p, k), Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩, rfl⟩
    · have h1 : p * p ≤ N := by
        calc p * p = p ^ 2 := (sq p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
          _ ≤ N := by omega
      exact Nat.lt_succ_of_le (Nat.le_sqrt.2 h1)
    · have h1 : 2 ^ k ≤ N := by
        calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
          _ ≤ N := by omega
      exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by norm_num) h1)
  have h := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at h
  exact_mod_cast h

variable {q : ℕ} [NeZero q]

/-- The prime sum `Σ_{p ≤ 2P} χ(p)(p/P)^{−iy}f0(p/P)`. -/
def Sp (χ : DirichletCharacter ℂ q) (f0 : ℝ → ℝ) (P y : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊2 * P⌋₊ + 1)).filter Nat.Prime,
    χ n * (((n : ℝ) / P : ℝ) : ℂ) ^ (-(y : ℂ) * I) * (f0 (n / P) : ℂ)

/-- The proper prime powers' share, `Σ_{p^k ≤ 2P, k ≥ 2} χ(p^k)(Λ(p^k)/log p^k)(p^k/P)^{−iy}f0(p^k/P)`. -/
def Rp (χ : DirichletCharacter ℂ q) (f0 : ℝ → ℝ) (P y : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊2 * P⌋₊ + 1)).filter fun n => ¬ n.Prime,
    χ n * ((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ) * (((n : ℝ) / P : ℝ) : ℂ) ^ (-(y : ℂ) * I) *
      (f0 (n / P) : ℂ)

omit [NeZero q] in
/-- `Σ_n χ(n)Λ(n)w(n/P) = log P · (Σ_p + the proper prime powers' share)`: `Λ(n)ψ_P(n/P) = log P · (Λ(n)/log n)f0(n/P)`
where `f0(n/P) ≠ 0`, and `Λ(p)/log p = 1`. -/
theorem Sw_wy_eq (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (χ : DirichletCharacter ℂ q) {P : ℝ} (hP : 4 ≤ P)
    (y : ℝ) : SieveLemma1.Sw χ (wy f0 P y) P = Real.log P * (Sp χ f0 P y + Rp χ f0 P y) := by
  have hP0 : 0 < P := by linarith
  have hlP : 0 < Real.log P := Real.log_pos (by linarith)
  set s := Finset.range (⌊2 * P⌋₊ + 1) with hs
  -- the sum is finite
  have hfin : ∀ n ∉ s, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * wy f0 P y (n / P) = 0 := by
    intro n hn
    rw [hs, Finset.mem_range, not_lt] at hn
    have h1 : 2 * P < n := by
      have := Nat.lt_floor_add_one (2 * P)
      have h2 : ((⌊2 * P⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2; linarith
    have h2 : 2 < (n : ℝ) / P := by rw [lt_div_iff₀ hP0]; linarith
    rw [wy, psiw_eq_zero hsupp P fun h => by linarith [h.2], smul_zero, mul_zero]
  rw [SieveLemma1.Sw, tsum_eq_sum hfin]
  -- each term
  have hterm : ∀ n ∈ s, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * wy f0 P y (n / P) =
      Real.log P * (χ n * ((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ) *
        (((n : ℝ) / P : ℝ) : ℂ) ^ (-(y : ℂ) * I) * (f0 (n / P) : ℂ)) := by
    intro n _
    by_cases hf : f0 (n / P) = 0
    · simp [wy, psiw, hf]
    · have hm := hsupp hf
      rw [mem_Icc] at hm
      have hn2 : (2 : ℝ) ≤ n := by
        have := hm.1
        rw [le_div_iff₀ hP0] at this; linarith
      have hn0 : (0 : ℝ) < n := by linarith
      have hln : 0 < Real.log n := Real.log_pos (by linarith)
      have e : 1 + Real.log ((n : ℝ) / P) / Real.log P = Real.log n / Real.log P := by
        rw [Real.log_div hn0.ne' hP0.ne']; field_simp; ring
      rw [wy, psiw, e, smul_eq_mul]
      push_cast
      field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not s Nat.Prime, Sp, Rp]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hp := (Finset.mem_filter.1 hn).2
  have hln : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hln]
  push_cast
  ring

/-- **Lemma 1 for primes.** For every `K` there are `B, C ≥ 0` such that, under the hypotheses of `norm_Sw_wy_le`,
`|Σ_{p ≤ 2P} χ(p)(p/P)^{−iy}f0(p/P)| ≤ M A B(P^{θ+δ} + P^{11/12+δ}(1 + H)^{−K})/log P + C(⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)`,
`N = ⌊2P⌋`: `Sw_wy_eq`, `norm_Sw_wy_le`, and at most `(⌊√N⌋ + 1)(⌊log₂ N⌋ + 1)` proper prime powers up to `N`, each
weighted by at most `max |f0|`. -/
theorem norm_Sp_le (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Icc (1 / 2) 2) (K : ℕ) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ θ δ H P y : ℝ,
      1 / 2 ≤ θ → θ ≤ 11 / 12 → 0 < δ → δ ≤ 1 / 24 → 0 ≤ H → 4 ≤ P →
      (∀ s : ℂ, θ < s.re → |s.im - y| < H + 1 → DirichletCharacter.LFunction χ s ≠ 0) →
      ‖Sp χ f0 P y‖ ≤ (Linnik.KL θ (θ + δ) + Linnik.KL (11 / 12) (11 / 12 + δ)) *
          (Real.log (q + 2) + Real.log (|y| + 4) + 1) * B *
          (P ^ (θ + δ) + P ^ (11 / 12 + δ) * ((1 + H) ^ K)⁻¹) / Real.log P +
        C * ((Nat.sqrt ⌊2 * P⌋₊ + 1) * (Nat.log 2 ⌊2 * P⌋₊ + 1)) := by
  obtain ⟨B, hB0, hB⟩ := norm_Sw_wy_le hf0 hsupp K
  have hc : Continuous f0 := hf0.continuous
  have hs : HasCompactSupport f0 := HasCompactSupport.intro (K := Icc (1 / 2) 2) isCompact_Icc fun u hu =>
    Function.notMem_support.1 fun h => hu (hsupp h)
  obtain ⟨C₀, hC₀⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨B, max C₀ 0, hB0, le_max_right _ _, fun q _ χ hχ θ δ H P y hθ hθ1 hδ hδ1 hH hP hloc => ?_⟩
  have hP0 : 0 < P := by linarith
  have hlP : 0 < Real.log P := Real.log_pos (by linarith)
  have hW := hB q χ hχ θ δ H P y hθ hθ1 hδ hδ1 hH hP hloc
  have hEq := Sw_wy_eq hsupp χ hP y
  -- `Sp = Sw/log P − Rp`
  have hSp : Sp χ f0 P y = SieveLemma1.Sw χ (wy f0 P y) P / Real.log P - Rp χ f0 P y := by
    have hlPc : (Real.log P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlP.ne'
    rw [hEq, mul_div_cancel_left₀ _ hlPc]; ring
  -- the proper prime powers
  have hR : ‖Rp χ f0 P y‖ ≤ max C₀ 0 * ((Nat.sqrt ⌊2 * P⌋₊ + 1) * (Nat.log 2 ⌊2 * P⌋₊ + 1)) := by
    rw [Rp]
    set s := (Finset.range (⌊2 * P⌋₊ + 1)).filter fun n => ¬ n.Prime
    set s' := (Finset.range (⌊2 * P⌋₊ + 1)).filter fun n => IsPrimePow n ∧ ¬ n.Prime
    have hzero : ∀ n ∈ s, n ∉ s' → χ n * ((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ) *
        (((n : ℝ) / P : ℝ) : ℂ) ^ (-(y : ℂ) * I) * (f0 (n / P) : ℂ) = 0 := by
      intro n hn hn'
      have hnp : ¬ IsPrimePow n := fun h => hn' (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, h,
        (Finset.mem_filter.1 hn).2⟩)
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hnp]
      simp
    have hss : s' ⊆ s := fun n hn => Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2.2⟩
    rw [← Finset.sum_subset hss hzero]
    refine (norm_sum_le _ _).trans ?_
    have hcard := card_properPrimePow_le ⌊2 * P⌋₊
    calc ∑ n ∈ s', ‖χ n * ((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ) *
          (((n : ℝ) / P : ℝ) : ℂ) ^ (-(y : ℂ) * I) * (f0 (n / P) : ℂ)‖ ≤ ∑ _n ∈ s', max C₀ 0 := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn2 : 2 ≤ n := (Finset.mem_filter.1 hn).2.1.two_le
          rw [norm_mul, norm_mul, norm_mul]
          have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
          have h2 : ‖((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
            have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
            have hle := ArithmeticFunction.vonMangoldt_le_log (n := n)
            rcases le_or_gt (Real.log n) 0 with hl | hl
            · have : ArithmeticFunction.vonMangoldt n = 0 := le_antisymm (hle.trans hl) hΛ
              rw [this, zero_div]; constructor <;> norm_num
            · constructor
              · have := div_nonneg hΛ hl.le; linarith
              · exact (div_le_one hl).2 hle
          have h3 : ‖(((n : ℝ) / P : ℝ) : ℂ) ^ (-(y : ℂ) * I)‖ = 1 := by
            have hnP : 0 < (n : ℝ) / P := div_pos (by exact_mod_cast (by omega : 0 < n)) hP0
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hnP]
            simp
          have h4 : ‖(f0 (n / P) : ℂ)‖ ≤ max C₀ 0 := by
            rw [Complex.norm_real]; exact (hC₀ _).trans (le_max_left _ _)
          rw [h3, mul_one]
          calc ‖χ n‖ * ‖((ArithmeticFunction.vonMangoldt n / Real.log n : ℝ) : ℂ)‖ * ‖(f0 (n / P) : ℂ)‖
              ≤ 1 * 1 * max C₀ 0 := by gcongr
            _ = max C₀ 0 := by ring
      _ = max C₀ 0 * (s'.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ max C₀ 0 * ((Nat.sqrt ⌊2 * P⌋₊ + 1) * (Nat.log 2 ⌊2 * P⌋₊ + 1)) :=
          mul_le_mul_of_nonneg_left hcard (le_max_right _ _)
  rw [hSp]
  calc ‖SieveLemma1.Sw χ (wy f0 P y) P / Real.log P - Rp χ f0 P y‖
      ≤ ‖SieveLemma1.Sw χ (wy f0 P y) P / Real.log P‖ + ‖Rp χ f0 P y‖ := norm_sub_le _ _
    _ = ‖SieveLemma1.Sw χ (wy f0 P y) P‖ / Real.log P + ‖Rp χ f0 P y‖ := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlP.le]
    _ ≤ _ := by gcongr

end SieveWeight

#print axioms SieveWeight.abs_iteratedDeriv_inv_one_sub_le
#print axioms SieveWeight.contDiff_gw
#print axioms SieveWeight.exists_bound_iteratedDeriv_gw
#print axioms SieveWeight.exists_mellin_bound
#print axioms SieveWeight.norm_Sw_wy_le
#print axioms SieveWeight.Sw_wy_eq
#print axioms SieveWeight.norm_Sp_le
