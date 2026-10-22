/-
# Round 640: the Mellin transform of `w²`, and the Gram entries as vertical integrals (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 639's hypothesis `LinnikCGLS23.CGLS2` bounds `‖E‖_F² = Σ_{i≠k}|G(i, k)|²`, with
`G(i, k) = Σ_n w(n/N)²χ_i(n)χ̄_k(n)n^{i(t_i−t_k)}`. Chen–Gupta–Li bound it through the reflection of their Lemma 6.2,
which starts from the Mellin transform `H(s) = ∫w(u)²u^{s−1} du` of `w²`, whose decay is their (6.2), and from
`Σ_n w(n/N)²χ(n)n^{it} = (1/2πi)∫_{(2)} H(s)N^sL(s − it, χ) ds` (the display after their (6.2), by Mellin inversion).
This file gives both, for the weight `w` of `LinnikCGLMat`.

Plain statement (`exists_H_bound`). For every `K ≥ 0` and `S ≥ 0` there is `B ≥ 0` with
`(1 + |t|)^{K+3}|H(σ + it)| ≤ B` for all real `t` and `|σ| ≤ S`.

Plain statement (`differentiable_H`). `H` is entire.

Plain statement (`perron_gram`). For `i, k`, `N > 0` and `σ > 1`, with `ψ = χ_iχ̄_k` and `τ = t_i − t_k`,
`G(i, k) = N^{iτ}·(1/2π)∫ L(σ + iv, ψ)H(σ + iv + iτ)N^{σ+iv} dv`.

* `wsq`, `contDiff_wsq`, `wsq_eq_zero`, `support_wsq`: `w²` is smooth and vanishes outside `(1, 2)`; its support
  lies in the interval `[1/2, 2]` that round 591's lemmas take.
* `gE`, `exists_bound_iteratedDeriv_gE`: in the variable `v = −log u`, `g_σ(v) = e^{−σv}w(e^{−v})²` and its
  derivatives are bounded uniformly in `|σ| ≤ S`; they vanish outside `[−log 2, log 2]` (round 591's
  `SieveWeight.exists_bound_iteratedDeriv_gw` without the factor `(1 − av)⁻¹`, on `|σ| ≤ S` in place of `[0, 2]`).
* `H_eq_fourier`, `exists_H_bound`: `H(σ + it)` is the Fourier transform of `g_σ` at `t/2π` (Mathlib's
  `mellin_eq_fourier`), and `|t|^j|H(σ + it)| ≤ ∫|g_σ^{(j)}|` (round 588's `SieveSmooth.pow_mul_norm_fourier_le`).
* `mellinConvergent_Wc`, `differentiable_H`, `continuous_H_line`, `integrable_H_line`: convergence everywhere,
  holomorphy and integrability on vertical lines.
* `Wt`, `mellin_Wt`: the weight `W_τ(u) = u^{iτ}w(u)²`, with `𝓜W_τ(s) = H(s + iτ)` (Mathlib's `mellin_cpow_smul`).
* `perron_Wt`: round 591's `SieveLemma1.perron_weight` for `W_τ`:
  `(1/2π)∫ L(σ + iv, ψ)H(σ + iv + iτ)N^{σ+iv} dv = Σ_n ψ(n)W_τ(n/N)` for `σ > 1`.
* `gram_eq_tsum`, `perron_gram`: `G(i, k) = N^{iτ}Σ_n ψ(n)W_τ(n/N)`.

The file imports `LinnikCGLS23.lean` and `SieveWeight.lean`.
-/

import LinnikCGLS23
import SieveWeight

open Complex Set Real Filter Topology MeasureTheory FourierTransform
open scoped Nat ContDiff

noncomputable section

namespace LinnikCGLMellin

open LinnikCGLMat DirichletCharacter

/-! ### The weight `w²` -/

/-- `w(u)²`, real-valued. -/
def wsq (u : ℝ) : ℝ := wCGL u ^ 2

lemma contDiff_wsq : ContDiff ℝ ∞ wsq := wCGL_contDiff.pow 2

lemma wsq_eq_zero {u : ℝ} (h : u ≤ 1 ∨ 2 ≤ u) : wsq u = 0 := by
  simp [wsq, wCGL_zero h]

lemma support_wsq : Function.support wsq ⊆ Icc (1 / 2) 2 := by
  intro u hu
  by_contra h
  apply hu
  apply wsq_eq_zero
  rw [mem_Icc, not_and_or] at h
  rcases h with h | h
  · left; push Not at h; linarith
  · right; push Not at h; linarith

/-- `W(u) = w(u)²`, complex-valued. -/
def Wc (u : ℝ) : ℂ := (wsq u : ℂ)

/-- **The Mellin transform** `H(s) = ∫ w(u)²u^{s−1} du`. -/
def H (s : ℂ) : ℂ := mellin Wc s

/-! ### Its decay on vertical strips -/

/-- `g_σ(v) = e^{−σv}w(e^{−v})²`. -/
def gE (σ v : ℝ) : ℝ := Real.exp (-σ * v) * SieveWeight.bw wsq v

lemma contDiff_gE (σ : ℝ) : ContDiff ℝ ∞ (gE σ) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (SieveWeight.contDiff_bw contDiff_wsq)

lemma gE_eventually_zero (σ : ℝ) {v : ℝ} (hv : Real.log 2 < |v|) : gE σ =ᶠ[𝓝 v] fun _ => 0 := by
  filter_upwards [SieveWeight.bw_eventually_zero support_wsq hv] with w hw
  simp [gE, hw]

/-- **The derivatives of `g_σ`**, uniformly in `|σ| ≤ S`: Leibniz's rule on `[−log 2, log 2]`, with
`|(d/dv)^j e^{−σv}| ≤ S^j e^{S log 2}` there, and `0` outside it. -/
theorem exists_bound_iteratedDeriv_gE {S : ℝ} (hS : 0 ≤ S) :
    ∃ G : ℕ → ℝ, ∀ k, 0 ≤ G k ∧ ∀ σ v : ℝ, |σ| ≤ S → |iteratedDeriv k (gE σ) v| ≤ G k := by
  choose Mb hMb0 hMb using SieveWeight.exists_bound_iteratedDeriv_bw contDiff_wsq support_wsq
  refine ⟨fun k => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (S ^ j * Real.exp (S * Real.log 2)) * Mb (k - j),
    fun k => ⟨Finset.sum_nonneg fun j _ => by have := hMb0 (k - j); positivity, fun σ v hσ => ?_⟩⟩
  by_cases hv : v ∈ Icc (-Real.log 2) (Real.log 2)
  · have hL2 := norm_iteratedFDeriv_mul_le (f := fun w => Real.exp (-σ * w)) (g := SieveWeight.bw wsq)
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)) (SieveWeight.contDiff_bw contDiff_wsq) v (n := k)
      (by exact_mod_cast le_top)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hL2
    have e : gE σ = fun w => Real.exp (-σ * w) * SieveWeight.bw wsq w := rfl
    rw [e]
    refine hL2.trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Real.norm_eq_abs, iteratedDeriv_exp_const_mul]
    have he : |(-σ) ^ j * Real.exp (-σ * v)| ≤ S ^ j * Real.exp (S * Real.log 2) := by
      rw [abs_mul, abs_pow, abs_neg, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg σ) hσ j) (Real.exp_le_exp.2 ?_) (by positivity)
        (by positivity)
      have hv' : |v| ≤ Real.log 2 := abs_le.2 ⟨hv.1, hv.2⟩
      calc -σ * v ≤ |σ * v| := by rw [neg_mul]; exact neg_le_abs _
        _ = |σ| * |v| := abs_mul σ v
        _ ≤ S * Real.log 2 := mul_le_mul hσ hv' (abs_nonneg v) hS
    have := hMb (k - j) v
    gcongr
  · rw [(gE_eventually_zero σ (SieveWeight.not_mem_Icc_log hv)).iteratedDeriv_eq k, iteratedDeriv_const]
    have h0 : (0 : ℝ) ≤
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (S ^ j * Real.exp (S * Real.log 2)) * Mb (k - j) :=
      Finset.sum_nonneg fun j _ => by have := hMb0 (k - j); positivity
    split_ifs <;> simpa using h0

/-- `H(σ + it)` is the Fourier transform of `g_σ` at `t/2π` (Mathlib's `mellin_eq_fourier`). -/
lemma H_eq_fourier (σ t : ℝ) : H (σ + t * I) = 𝓕 (fun v => (gE σ v : ℂ)) (t / (2 * π)) := by
  unfold H
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have him : ((σ : ℂ) + t * I).im = t := by simp
  have hfun : (fun u : ℝ => Real.exp (-σ * u) • Wc (Real.exp (-u))) = fun v => (gE σ v : ℂ) := by
    funext v
    rw [Complex.real_smul]
    simp only [Wc, gE, SieveWeight.bw]
    push_cast
    ring
  rw [hre, him, hfun]

/-- **The decay of `H` on vertical strips**: for every `K ≥ 0` and `S ≥ 0` there is `B ≥ 0` with
`(1 + |t|)^{K+3}|H(σ + it)| ≤ B` for `|σ| ≤ S`, from `|t|^j|H(σ + it)| ≤ ∫|g_σ^{(j)}|` at `j = 0` and `j = K + 3`. -/
theorem exists_H_bound (K : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ t : ℝ, |σ| ≤ S → (1 + |t|) ^ (K + 3) * ‖H (σ + t * I)‖ ≤ B := by
  obtain ⟨G, hG⟩ := exists_bound_iteratedDeriv_gE hS
  refine ⟨2 ^ (K + 3) * (2 * Real.log 2 * G 0 + 2 * Real.log 2 * G (K + 3)), ?_, ?_⟩
  · have h1 := (hG 0).1
    have h2 := (hG (K + 3)).1
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro σ t hσ
  set f : ℝ → ℂ := fun v => (gE σ v : ℂ) with hf
  have hgC : ContDiff ℝ ∞ (gE σ) := contDiff_gE σ
  have hfC : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hgC
  have hvan : ∀ n : ℕ, ∀ x, x ∉ Icc (-Real.log 2) (Real.log 2) → iteratedDeriv n f x = 0 := by
    intro n x hx
    rw [SieveWeight.iteratedDeriv_ofReal hgC,
      (gE_eventually_zero σ (SieveWeight.not_mem_Icc_log hx)).iteratedDeriv_eq n, iteratedDeriv_const]
    split_ifs <;> simp
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n f) := by
    intro n
    refine (hfC.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro (K := Icc (-Real.log 2) (Real.log 2)) isCompact_Icc (hvan n)
  have hbound : ∀ j : ℕ, |t| ^ j * ‖H (σ + t * I)‖ ≤ 2 * Real.log 2 * G j := by
    intro j
    have h := SieveSmooth.pow_mul_norm_fourier_le (f := f) (K := j) (hfC.of_le (by exact_mod_cast le_top))
      (fun n _ => hint n) (t / (2 * π))
    have hpi : 0 < π := Real.pi_pos
    have e1 : 2 * π * |t / (2 * π)| = |t| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]; field_simp
    rw [e1, ← H_eq_fourier σ t] at h
    refine h.trans (SieveWeight.integral_norm_le_of_vanish
      (hfC.continuous_iteratedDeriv j (by exact_mod_cast le_top)) (hvan j) fun x => ?_)
    rw [SieveWeight.iteratedDeriv_ofReal hgC, Complex.norm_real, Real.norm_eq_abs]
    exact (hG j).2 σ x hσ
  have h0 := hbound 0
  have hK := hbound (K + 3)
  rw [pow_zero, one_mul] at h0
  have hm0 : 0 ≤ ‖H (σ + t * I)‖ := norm_nonneg _
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
  calc (1 + |t|) ^ (K + 3) * ‖H (σ + t * I)‖
      ≤ 2 ^ (K + 3) * (1 + |t| ^ (K + 3)) * ‖H (σ + t * I)‖ := by gcongr
    _ = 2 ^ (K + 3) * (‖H (σ + t * I)‖ + |t| ^ (K + 3) * ‖H (σ + t * I)‖) := by ring
    _ ≤ 2 ^ (K + 3) * (2 * Real.log 2 * G 0 + 2 * Real.log 2 * G (K + 3)) := by gcongr

/-! ### Convergence, holomorphy, and the lines -/

lemma Wc_eq_zero {u : ℝ} (hu : u ∉ Icc (1 / 2) 2) : Wc u = 0 := by
  have h : wsq u = 0 := Function.notMem_support.1 fun h => hu (support_wsq h)
  simp [Wc, h]

lemma continuous_Wc : Continuous Wc := Complex.continuous_ofReal.comp contDiff_wsq.continuous

lemma Wc_eventually_zero_atTop : Wc =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop 2] with u hu
  exact Wc_eq_zero fun h => by linarith [h.2]

lemma Wc_eventually_zero_zero : Wc =ᶠ[𝓝[>] 0] 0 := by
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with u hu
  exact Wc_eq_zero fun h => by linarith [h.1, mem_Iio.1 hu]

lemma locallyIntegrableOn_Wc : LocallyIntegrableOn Wc (Ioi 0) :=
  continuous_Wc.continuousOn.locallyIntegrableOn measurableSet_Ioi

theorem mellinConvergent_Wc (s : ℂ) : MellinConvergent Wc s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) locallyIntegrableOn_Wc
    (Wc_eventually_zero_atTop.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)
    (Wc_eventually_zero_zero.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)

/-- **`H` is entire.** -/
theorem differentiable_H : Differentiable ℂ H := fun s =>
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) locallyIntegrableOn_Wc
    (Wc_eventually_zero_atTop.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)
    (Wc_eventually_zero_zero.trans_isBigO (Asymptotics.isBigO_zero _ _)) (by linarith)

lemma continuous_H_line (σ c : ℝ) : Continuous fun t : ℝ => H (σ + t * I + c * I) :=
  differentiable_H.continuous.comp (by fun_prop)

/-- `t ↦ H(σ + it + ic)` is integrable, from `(1 + |t + c|)³|H| ≤ B`. -/
lemma integrable_H_line (σ c : ℝ) : Integrable fun t : ℝ => H (σ + t * I + c * I) := by
  obtain ⟨B, hB0, hB⟩ := exists_H_bound 0 (abs_nonneg σ)
  have hb : ∀ t : ℝ, ‖H (σ + t * I + c * I)‖ ≤ B * (1 + (t + c) ^ 2)⁻¹ := by
    intro t
    have e : (σ : ℂ) + t * I + c * I = σ + ((t + c : ℝ) : ℂ) * I := by push_cast; ring
    have h := hB σ (t + c) le_rfl
    rw [← e, show (0 + 3 : ℕ) = 3 by norm_num] at h
    have h1 : 1 + (t + c) ^ 2 ≤ (1 + |t + c|) ^ 3 := by
      have ha : 0 ≤ |t + c| := abs_nonneg (t + c)
      have hsq : (t + c) ^ 2 = |t + c| ^ 2 := (sq_abs _).symm
      rw [hsq]
      nlinarith [mul_nonneg ha (sq_nonneg |t + c|)]
    rw [show B * (1 + (t + c) ^ 2)⁻¹ = B / (1 + (t + c) ^ 2) by ring, le_div_iff₀ (by positivity)]
    calc ‖H (σ + t * I + c * I)‖ * (1 + (t + c) ^ 2) ≤ ‖H (σ + t * I + c * I)‖ * (1 + |t + c|) ^ 3 := by
          gcongr
      _ = (1 + |t + c|) ^ 3 * ‖H (σ + t * I + c * I)‖ := by ring
      _ ≤ B := h
  have hi : Integrable fun t : ℝ => B * (1 + (t + c) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_add_right c).const_mul B
  exact hi.mono' (continuous_H_line σ c).aestronglyMeasurable (Eventually.of_forall hb)

/-! ### The twisted weight and Perron's formula -/

/-- **The twisted weight** `W_τ(u) = u^{iτ}w(u)²`. -/
def Wt (τ : ℝ) (u : ℝ) : ℂ := (u : ℂ) ^ ((τ : ℂ) * I) • Wc u

lemma mellin_Wt (τ : ℝ) (s : ℂ) : mellin (Wt τ) s = H (s + τ * I) := mellin_cpow_smul _ s _

lemma continuousAt_Wt (τ : ℝ) {u : ℝ} (hu : 0 < u) : ContinuousAt (Wt τ) u := by
  unfold Wt
  exact (continuousAt_ofReal_cpow_const u ((τ : ℂ) * I) (Or.inr hu.ne')).smul continuous_Wc.continuousAt

/-- **Perron's formula for `W_τ`** (round 591's `SieveLemma1.perron_weight`): for `σ > 1` and `N > 0`,
`(1/2π)∫ L(σ + iv, ψ)H(σ + iv + iτ)N^{σ+iv} dv = Σ_n ψ(n)W_τ(n/N)`. -/
theorem perron_Wt {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (τ : ℝ) {σ N : ℝ} (hσ : 1 < σ)
    (hN : 0 < N) :
    (1 / (2 * π) : ℂ) * ∫ v : ℝ, LFunction ψ (σ + v * I) * H (σ + v * I + τ * I) * (N : ℂ) ^ ((σ : ℂ) + v * I) =
      ∑' n : ℕ, ψ n * Wt τ (n / N) := by
  set f : ℕ → ℂ := fun n => if n = 0 then 0 else ψ n with hf
  have hf0 : f 0 = 0 := by simp [hf]
  have hfg : ∀ {n : ℕ}, n ≠ 0 → f n = ψ n := fun {n} hn => by simp [hf, hn]
  have hMc : MellinConvergent (Wt τ) σ := by
    unfold Wt
    exact (MellinConvergent.cpow_smul (f := Wc) (s := (σ : ℂ)) (a := (τ : ℂ) * I)).2 (mellinConvergent_Wc _)
  have hMv : VerticalIntegrable (mellin (Wt τ)) σ := by
    have h := integrable_H_line σ τ
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [mellin_Wt]
  have hMcont : Continuous fun v : ℝ => mellin (Wt τ) (σ + v * I) := by
    simp only [mellin_Wt]; exact continuous_H_line σ τ
  have hsum : LSeriesSummable f σ := by
    rw [LSeriesSummable_congr (σ : ℂ) hfg]
    exact LSeriesSummable_of_one_lt_re ψ (by simpa using hσ)
  have h := SieveLemma1.perron_weight hf0 hN (fun x hx => continuousAt_Wt τ hx) hMc hMv hMcont hsum
  have hL : ∀ v : ℝ, LSeries f (σ + v * I) = LFunction ψ (σ + v * I) := by
    intro v
    rw [LSeries_congr hfg, LFunction_eq_LSeries ψ (by simpa using hσ)]
  simp only [hL, mellin_Wt] at h
  rw [h]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have hw0 : wsq 0 = 0 := wsq_eq_zero (Or.inl (by norm_num))
    simp [hf, Wt, Wc, hw0]
  · rw [hfg hn]

/-! ### The Gram entries -/

/-- `n^{ix}·conj(n^{iy}) = n^{i(x−y)}` for `n ≥ 1`. -/
lemma cpow_I_mul_star {n : ℕ} (hn : 0 < n) (x y : ℝ) :
    (n : ℂ) ^ ((x : ℂ) * I) * star ((n : ℂ) ^ ((y : ℂ) * I)) = (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I) := by
  rw [natCast_cpow_I hn, natCast_cpow_I hn, natCast_cpow_I hn, Complex.star_def, ← Complex.exp_conj,
    ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- `n^r = (n/N)^r·N^r` for `N > 0`. -/
lemma natCast_cpow_split (n : ℕ) {N : ℝ} (hN : 0 < N) (r : ℂ) :
    (n : ℂ) ^ r = (((n : ℝ) / N : ℝ) : ℂ) ^ r * (N : ℂ) ^ r := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) hN.le]
  congr 1
  push_cast
  field_simp

/-- **The Gram entries as weighted sums**: with `ψ = χ_iχ̄_k` and `τ = t_i − t_k`,
`G(i, k) = N^{iτ}Σ_n ψ(n)W_τ(n/N)`. -/
theorem gram_eq_tsum {ι : Type*} {q : ℕ} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (i k : ι) :
    gramP N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) *
      ∑' n : ℕ, (χ i * (χ k)⁻¹) n * Wt (t i - t k) (n / N) := by
  rw [tsum_eq_sum (s := colsP N) ?_]
  · unfold gramP
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 := colsP_pos hN hn
    have hw : star ((wCGL ((n : ℝ) / N) : ℂ)) = (wCGL ((n : ℝ) / N) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hs := cpow_I_mul_star hn0 (t i) (t k)
    have hsplit := natCast_cpow_split n hN (((t i - t k : ℝ) : ℂ) * I)
    unfold entP Wt Wc wsq
    rw [MulChar.mul_apply, star_mul', star_mul', hw, MulChar.star_apply', smul_eq_mul]
    calc (wCGL ((n : ℝ) / N) : ℂ) * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) *
          ((wCGL ((n : ℝ) / N) : ℂ) * (χ k)⁻¹ n * star ((n : ℂ) ^ ((t k : ℂ) * I)))
        = (wCGL ((n : ℝ) / N) : ℂ) ^ 2 * (χ i n * (χ k)⁻¹ n) *
          ((n : ℂ) ^ ((t i : ℂ) * I) * star ((n : ℂ) ^ ((t k : ℂ) * I))) := by ring
      _ = (wCGL ((n : ℝ) / N) : ℂ) ^ 2 * (χ i n * (χ k)⁻¹ n) * (n : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) := by
          rw [hs]
      _ = _ := by
          rw [hsplit]
          push_cast
          ring
  · intro n hn
    have hw : wsq ((n : ℝ) / N) = 0 := by
      apply wsq_eq_zero
      rw [colsP, Finset.mem_Icc, not_and_or] at hn
      rcases hn with h | h
      · left
        push Not at h
        have : (n : ℝ) < N := Nat.lt_ceil.1 h
        rw [div_le_one hN]; linarith
      · right
        push Not at h
        have : 2 * N < n := (Nat.floor_lt (by linarith)).1 h
        rw [le_div_iff₀ hN]; linarith
    simp [Wt, Wc, hw]

/-- **Perron's formula for the Gram entries**: for `σ > 1`, with `ψ = χ_iχ̄_k` and `τ = t_i − t_k`,
`G(i, k) = N^{iτ}·(1/2π)∫ L(σ + iv, ψ)H(σ + iv + iτ)N^{σ+iv} dv`. -/
theorem perron_gram {ι : Type*} {q : ℕ} [NeZero q] {N σ : ℝ} (hN : 0 < N) (hσ : 1 < σ)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) :
    gramP N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * ((1 / (2 * π) : ℂ) *
      ∫ v : ℝ, LFunction (χ i * (χ k)⁻¹) (σ + v * I) * H (σ + v * I + ((t i - t k : ℝ) : ℂ) * I) *
        (N : ℂ) ^ ((σ : ℂ) + v * I)) := by
  rw [gram_eq_tsum hN χ t i k, perron_Wt (χ i * (χ k)⁻¹) (t i - t k) hσ hN]

end LinnikCGLMellin

#print axioms LinnikCGLMellin.exists_H_bound
#print axioms LinnikCGLMellin.differentiable_H
#print axioms LinnikCGLMellin.integrable_H_line
#print axioms LinnikCGLMellin.perron_Wt
#print axioms LinnikCGLMellin.gram_eq_tsum
#print axioms LinnikCGLMellin.perron_gram
