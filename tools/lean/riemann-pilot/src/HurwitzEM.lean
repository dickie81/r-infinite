import Mathlib

/-!
# Euler–Maclaurin for the Hurwitz zeta function with an explicit remainder

For `x ∈ (0, 1]`, `M ≥ 1`, `K ≥ 1`, `Re s > 0`, `s ≠ 1` (`norm_hurwitzZeta_sub_EM_le`):

`ζ(s, x) = Σ_{m<M} (m+x)^{-s} + (M+x)^{1-s}/(s-1) + (M+x)^{-s}/2
          + Σ_{k<K} B_{2k+2}/(2k+2)! · s(s+1)⋯(s+2k) · (M+x)^{-s-2k-1} − R`,

`‖R‖ ≤ |B_{2K}|/(2K)! · ‖s(s+1)⋯(s+2K−1)‖ · (M+x)^{1−Re s−2K}/(Re s+2K−1)`,

with `|B_{2K}|/(2K)! = 2ζ(2K)/(2π)^{2K} ≤ (π²/3)/(2π)^{2K}` (`hasSum_zeta_CB`, `CB_le`).
`R = Σ_n ∫_0^1 B_{2K}(u)/(2K)! · (s)_{2K} (M+x+n+u)^{-s-2K} du` (`hurwitzZeta_eq_EM_explicit`).
A version uniform on boxes `σ₀ ≤ Re s ≤ σ₁, |Im s| ≤ τ` is `norm_hurwitzZeta_sub_EM_le_box`.

Route. §1: `|B_{2K}(u)| ≤ |B_{2K}|` on `[0,1]` from Mathlib's Fourier series of `B_{2K}`.
§2–4: `2K` integrations by parts on one unit interval give, for every `s ≠ 1` and `c > 0`,
`c^{-s} = T(c) − T(c+1) − R(c)` (`cpow_eq_T_sub`). §5: sharp and crude bounds on `R(c)`.
§6: summing over `c = M+x+n` for `Re s > 1` (`hurwitz_eq_of_one_lt`). §7: both sides are
holomorphic on `{Re s > 0, s ≠ 1}` (preconnected), so the identity theorem extends the identity
(`hurwitzZeta_eq_EM`); the remainder series converges locally uniformly because each `R(c)` is
the finite expression `T(c) − T(c+1) − c^{-s}`. §8: the remainder bound telescopes.
-/

open Complex Set Filter Topology intervalIntegral MeasureTheory HurwitzZeta
open scoped Nat Interval

noncomputable section

namespace HurwitzEM

/-! ## 1. The sup bound `|B_{2K}(x)| ≤ |B_{2K}|` on `[0, 1]` -/

theorem abs_bernoulliFun_le {K : ℕ} (hK : K ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * K) x| ≤ |(bernoulli (2 * K) : ℝ)| := by
  have h1 := hasSum_one_div_nat_pow_mul_cos hK hx
  have h2 := hasSum_zeta_nat hK
  have hle := h1.norm_le_of_bounded h2 (fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * K))]
    calc 1 / (n : ℝ) ^ (2 * K) * |Real.cos (2 * Real.pi * n * x)|
        ≤ 1 / (n : ℝ) ^ (2 * K) * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = 1 / (n : ℝ) ^ (2 * K) := mul_one _)
  change ‖(-1 : ℝ) ^ (K + 1) * (2 * Real.pi) ^ (2 * K) / 2 / ((2 * K)! : ℝ) *
    bernoulliFun (2 * K) x‖ ≤ _ at hle
  have h2K : (2 : ℝ) ^ (2 * K - 1) * 2 = 2 ^ (2 * K) := by
    rw [← pow_succ]; congr 1; omega
  set C : ℝ := (2 * Real.pi) ^ (2 * K) / 2 / ((2 * K)! : ℝ) with hC
  have hCpos : 0 < C := by positivity
  have e1 : (-1 : ℝ) ^ (K + 1) * (2 * Real.pi) ^ (2 * K) / 2 / ((2 * K)! : ℝ) *
      bernoulliFun (2 * K) x = (-1) ^ (K + 1) * (C * bernoulliFun (2 * K) x) := by
    rw [hC]; ring
  have e2 : (-1 : ℝ) ^ (K + 1) * 2 ^ (2 * K - 1) * Real.pi ^ (2 * K) * (bernoulli (2 * K) : ℝ) /
      ((2 * K)! : ℝ) = C * ((-1) ^ (K + 1) * (bernoulli (2 * K) : ℝ)) := by
    rw [hC, mul_pow, ← h2K]; ring
  rw [e1, e2, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    abs_mul, abs_of_pos hCpos] at hle
  have h3 : (-1 : ℝ) ^ (K + 1) * (bernoulli (2 * K) : ℝ) ≤ |(bernoulli (2 * K) : ℝ)| := by
    calc _ ≤ |(-1 : ℝ) ^ (K + 1) * (bernoulli (2 * K) : ℝ)| := le_abs_self _
      _ = _ := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact le_of_mul_le_mul_left (hle.trans (mul_le_mul_of_nonneg_left h3 hCpos.le)) hCpos

/-! ## 2. Derivatives of `t^{-s}` and the normalised Bernoulli functions -/

/-- The rising factorial `s(s+1)⋯(s+j−1)`. -/
def poch (s : ℂ) (j : ℕ) : ℂ := ∏ i ∈ Finset.range j, (s + i)

theorem poch_succ (s : ℂ) (j : ℕ) : poch s (j + 1) = poch s j * (s + j) := by
  simp [poch, Finset.prod_range_succ]

/-- `D s j t = (d/dt)^j t^{-s} = (-1)^j (s)_j t^{-s-j}`. -/
def D (s : ℂ) (j : ℕ) (t : ℝ) : ℂ := (-1) ^ j * poch s j * (t : ℂ) ^ (-s - j)

theorem hasDerivAt_D (s : ℂ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (D s j) (D s (j + 1) t) t := by
  have h := ((Complex.hasStrictDerivAt_cpow_const (c := -s - j)
    (ofReal_mem_slitPlane.2 ht)).hasDerivAt).comp_ofReal
  have h2 := h.const_mul ((-1 : ℂ) ^ j * poch s j)
  have hf : D s j = fun y : ℝ => (-1 : ℂ) ^ j * poch s j * (y : ℂ) ^ (-s - j) := rfl
  rw [hf]
  convert h2 using 1
  rw [D, poch_succ]
  have e : -s - ((j + 1 : ℕ) : ℂ) = -s - j - 1 := by push_cast; ring
  rw [e, pow_succ]
  ring

/-- `P_j(u) = B_j(u)/j!`, complex-valued. -/
def Pb (j : ℕ) (u : ℝ) : ℂ := ((bernoulliFun j u / (j ! : ℝ) : ℝ) : ℂ)

theorem hasDerivAt_Pb (j : ℕ) (u : ℝ) : HasDerivAt (Pb (j + 1)) (Pb j u) u := by
  have h := ((hasDerivAt_bernoulliFun (j + 1) u).div_const (((j + 1)! : ℕ) : ℝ)).ofReal_comp
  have hf : Pb (j + 1) = fun y : ℝ => ((bernoulliFun (j + 1) y / (((j + 1)! : ℕ) : ℝ) : ℝ) : ℂ) :=
    rfl
  rw [hf]
  convert h using 1
  rw [Pb, ofReal_inj, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have : (j ! : ℝ) ≠ 0 := by positivity
  field_simp

theorem continuous_Pb (j : ℕ) : Continuous (Pb j) :=
  continuous_ofReal.comp ((continuous_bernoulliFun j).div_const _)

/-! ## 3. Repeated integration by parts on one unit interval -/

/-- `I_j(c) = ∫_0^1 P_j(u) D_j(c+u) du`. -/
def Iint (s : ℂ) (j : ℕ) (c : ℝ) : ℂ := ∫ u in (0 : ℝ)..1, Pb j u * D s j (c + u)

/-- The boundary term of one integration by parts. -/
def bd (s : ℂ) (j : ℕ) (c : ℝ) : ℂ := Pb (j + 1) 1 * D s j (c + 1) - Pb (j + 1) 0 * D s j c

theorem Iint_ibp (s : ℂ) (j : ℕ) {c : ℝ} (hc : 0 < c) :
    Iint s j c = bd s j c - Iint s (j + 1) c := by
  have hpos : ∀ u ∈ [[(0 : ℝ), 1]], 0 < c + u := by
    intro u hu; rw [uIcc_of_le zero_le_one] at hu; linarith [hu.1]
  have hD : ∀ u ∈ [[(0 : ℝ), 1]],
      HasDerivAt (fun u => D s j (c + u)) (D s (j + 1) (c + u)) u := by
    intro u hu
    exact (hasDerivAt_D s j (hpos u hu)).comp_const_add c u
  have hP : ∀ u ∈ [[(0 : ℝ), 1]], HasDerivAt (Pb (j + 1)) (Pb j u) u :=
    fun u _ => hasDerivAt_Pb j u
  have hPi : IntervalIntegrable (Pb j) volume 0 1 := (continuous_Pb j).intervalIntegrable 0 1
  have hDi : IntervalIntegrable (fun u => D s (j + 1) (c + u)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact (ContinuousAt.comp (g := D s (j + 1)) (hasDerivAt_D s (j + 1) (hpos u hu)).continuousAt
      (by fun_prop : ContinuousAt (fun u : ℝ => c + u) u)).continuousWithinAt
  have := integral_mul_deriv_eq_deriv_mul hP hD hPi hDi
  unfold Iint bd
  rw [this, add_zero]
  ring

theorem Pb_odd_zero {k : ℕ} (hk : 1 ≤ k) : Pb (2 * k + 1) 0 = 0 := by
  rw [Pb, bernoulliFun_eval_zero, bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)]
  simp

theorem Pb_odd_one {k : ℕ} (hk : 1 ≤ k) : Pb (2 * k + 1) 1 = 0 := by
  rw [Pb, bernoulliFun_endpoints_eq_of_ne_one (by omega)]
  exact Pb_odd_zero hk

theorem bd_even_zero (s : ℂ) {k : ℕ} (hk : 1 ≤ k) (c : ℝ) : bd s (2 * k) c = 0 := by
  rw [bd, Pb_odd_one hk, Pb_odd_zero hk]; ring

theorem Iint_zero_eq (s : ℂ) (K : ℕ) {c : ℝ} (hc : 0 < c) :
    Iint s 0 c = bd s 0 c - ∑ k ∈ Finset.range (K + 1), bd s (2 * k + 1) c +
      Iint s (2 * K + 2) c := by
  induction K with
  | zero =>
    rw [Iint_ibp s 0 hc, Iint_ibp s 1 hc]; simp; ring
  | succ K ih =>
    have h0 : bd s (2 * K + 2) c = 0 := bd_even_zero s (k := K + 1) (by omega) c
    rw [Finset.sum_range_succ (fun k => bd s (2 * k + 1) c) (K + 1), ih,
      Iint_ibp s (2 * K + 2) hc, Iint_ibp s (2 * K + 2 + 1) hc, h0]
    have e1 : 2 * (K + 1) + 1 = 2 * K + 2 + 1 := by ring
    have e2 : 2 * (K + 1) + 2 = 2 * K + 2 + 1 + 1 := by ring
    rw [e1, e2]
    ring

/-! ## 4. The per-interval Euler–Maclaurin identity -/

theorem Iint_zero_val (s : ℂ) (hs : s ≠ 1) {c : ℝ} (hc : 0 < c) :
    Iint s 0 c = ((c : ℂ) ^ (1 - s) - ((c + 1 : ℝ) : ℂ) ^ (1 - s)) / (s - 1) := by
  have h1 : Iint s 0 c = ∫ u in (0 : ℝ)..1, (fun t : ℝ => (t : ℂ) ^ (-s)) (c + u) := by
    unfold Iint
    congr 1; ext u
    simp [Pb, D, poch]
  rw [h1, intervalIntegral.integral_comp_add_left (fun t : ℝ => (t : ℂ) ^ (-s)) c, add_zero]
  have hnot : (0 : ℝ) ∉ [[c, c + 1]] := by
    rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1]
  have hr : -s ≠ -1 := fun h => hs (by linear_combination -h)
  rw [integral_cpow (Or.inr ⟨hr, hnot⟩)]
  have h2 : (s - 1 : ℂ) ≠ 0 := sub_ne_zero.2 hs
  have h3 : (-s + 1 : ℂ) ≠ 0 := fun h => h2 (by linear_combination -h)
  have e : -s + 1 = 1 - s := by ring
  rw [e]
  rw [div_eq_div_iff (by rwa [← e]) h2]
  ring

theorem Pb_one_val (u : ℝ) : Pb 1 u = (u : ℂ) - 1 / 2 := by
  simp [Pb]

theorem bd_zero_val (s : ℂ) (c : ℝ) :
    bd s 0 c = ((c : ℂ) ^ (-s) + ((c + 1 : ℝ) : ℂ) ^ (-s)) / 2 := by
  simp [bd, Pb_one_val, D, poch]
  ring

theorem Pb_even_val (k : ℕ) {u : ℝ} (hu : u = 0 ∨ u = 1) :
    Pb (2 * k + 2) u = (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) := by
  have h : bernoulliFun (2 * k + 2) u = bernoulliFun (2 * k + 2) 0 := by
    rcases hu with rfl | rfl
    · rfl
    · exact bernoulliFun_endpoints_eq_of_ne_one (by omega)
  rw [Pb, h, bernoulliFun_eval_zero]
  push_cast
  ring

theorem bd_odd_val (s : ℂ) (k : ℕ) (c : ℝ) :
    bd s (2 * k + 1) c = (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) * poch s (2 * k + 1) *
      ((c : ℂ) ^ (-s - (2 * k + 1)) - ((c + 1 : ℝ) : ℂ) ^ (-s - (2 * k + 1))) := by
  have e : 2 * k + 1 + 1 = 2 * k + 2 := by ring
  rw [bd, e, Pb_even_val k (Or.inr rfl), Pb_even_val k (Or.inl rfl), D, D,
    Odd.neg_one_pow ⟨k, rfl⟩]
  push_cast
  ring

/-- The Euler–Maclaurin main term at `t`:
`t^{1-s}/(s-1) + t^{-s}/2 + Σ_{k<K} B_{2k+2}/(2k+2)! · (s)_{2k+1} · t^{-s-2k-1}`. -/
def T (s : ℂ) (K : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (1 - s) / (s - 1) + (t : ℂ) ^ (-s) / 2 +
    ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) * poch s (2 * k + 1) *
      (t : ℂ) ^ (-s - (2 * k + 1))

/-- The remainder on `[c, c+1]`: `R = ∫_0^1 P_{2K}(u) D_{2K}(c+u) du`. -/
def R (s : ℂ) (K : ℕ) (c : ℝ) : ℂ := Iint s (2 * K) c

/-- **One unit interval:** `c^{-s} = T(c) - T(c+1) - R(c)` for every `s ≠ 1`, `K ≥ 1`, `c > 0`. -/
theorem cpow_eq_T_sub (s : ℂ) (hs : s ≠ 1) {K : ℕ} (hK : 1 ≤ K) {c : ℝ} (hc : 0 < c) :
    (c : ℂ) ^ (-s) = T s K c - T s K (c + 1) - R s K c := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hmain := Iint_zero_eq s K hc
  rw [Iint_zero_val s hs hc, bd_zero_val, Finset.sum_congr rfl (fun k _ => bd_odd_val s k c),
    Finset.sum_congr rfl (fun k _ => mul_sub _ _ _), Finset.sum_sub_distrib] at hmain
  have e : 2 * K + 2 = 2 * (K + 1) := by ring
  rw [e] at hmain
  unfold T R
  linear_combination -hmain

/-! ## 5. Bounds on the remainder -/

/-- The constant `C_K = |B_{2K}|/(2K)!` `(= 2ζ(2K)/(2π)^{2K})`. -/
def CB (K : ℕ) : ℝ := |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ)

theorem CB_nonneg (K : ℕ) : 0 ≤ CB K := by unfold CB; positivity

theorem norm_integrand_le (s : ℂ) {K : ℕ} (hK : K ≠ 0) {c : ℝ} (hc : 0 < c) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖Pb (2 * K) u * D s (2 * K) (c + u)‖ ≤
      CB K * ‖poch s (2 * K)‖ * (c + u) ^ (-s.re - 2 * K) := by
  have hcu : 0 < c + u := by linarith [hu.1]
  rw [norm_mul, Pb, D, norm_mul, norm_mul, Complex.norm_real, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_cpow_eq_rpow_re_of_pos hcu]
  have hre : (-s - ((2 * K : ℕ) : ℂ)).re = -s.re - 2 * K := by simp
  rw [hre, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((2 * K)! : ℝ))]
  have hB := abs_bernoulliFun_le hK hu
  unfold CB
  have h1 : 0 ≤ ‖poch s (2 * K)‖ * (c + u) ^ (-s.re - 2 * K) := by positivity
  calc |bernoulliFun (2 * K) u| / ((2 * K)! : ℝ) * (‖poch s (2 * K)‖ * (c + u) ^ (-s.re - 2 * K))
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) *
          (‖poch s (2 * K)‖ * (c + u) ^ (-s.re - 2 * K)) := by gcongr
    _ = _ := by ring

theorem integral_rpow_shift {c q : ℝ} (hc : 0 < c) (hq : q ≠ -1) :
    ∫ u in (0 : ℝ)..1, (c + u) ^ q = ((c + 1) ^ (q + 1) - c ^ (q + 1)) / (q + 1) := by
  have h := intervalIntegral.integral_comp_add_left (fun t : ℝ => t ^ q) c (a := 0) (b := 1)
  simp only [add_zero] at h
  rw [h]
  have hnot : (0 : ℝ) ∉ [[c, c + 1]] := by
    rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1]
  exact integral_rpow (Or.inr ⟨hq, hnot⟩)

/-- **Sharp per-interval bound.** -/
theorem norm_R_le (s : ℂ) {K : ℕ} (hK : K ≠ 0) {c : ℝ} (hc : 0 < c)
    (hσ : 0 < s.re + 2 * K - 1) :
    ‖R s K c‖ ≤ CB K * ‖poch s (2 * K)‖ *
      ((c ^ (1 - s.re - 2 * K) - (c + 1) ^ (1 - s.re - 2 * K)) / (s.re + 2 * K - 1)) := by
  unfold R Iint
  have hcont : ContinuousOn (fun u : ℝ => CB K * ‖poch s (2 * K)‖ * (c + u) ^ (-s.re - 2 * K))
      [[0, 1]] := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro u hu; left; rw [uIcc_of_le zero_le_one] at hu; linarith [hu.1]
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ (fun u hu => norm_integrand_le s hK hc ⟨hu.1.le, hu.2⟩))
    hcont.intervalIntegrable).trans (le_of_eq ?_)
  have hq : -s.re - 2 * K ≠ -1 := fun h => by linarith
  rw [intervalIntegral.integral_const_mul, integral_rpow_shift hc hq]
  have e : -s.re - 2 * K + 1 = 1 - s.re - 2 * K := by ring
  rw [e]
  have h1 : (1 - s.re - 2 * K : ℝ) ≠ 0 := fun h => by linarith
  have h2 : (s.re + 2 * K - 1 : ℝ) ≠ 0 := fun h => by linarith
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff h1 h2]
  ring

/-- **Crude per-interval bound** (for local uniform convergence). -/
theorem norm_R_le_crude (s : ℂ) {K : ℕ} (hK : K ≠ 0) {c : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ s.re + 2 * K) :
    ‖R s K c‖ ≤ CB K * ‖poch s (2 * K)‖ * c ^ (-s.re - 2 * K) := by
  unfold R Iint
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun u => Pb (2 * K) u * D s (2 * K) (c + u))
    (C := CB K * ‖poch s (2 * K)‖ * c ^ (-s.re - 2 * K)) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      refine (norm_integrand_le s hK hc ⟨hu.1.le, hu.2⟩).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hc (by linarith [hu.1]) (by linarith))
        (mul_nonneg (CB_nonneg K) (norm_nonneg _)))
  simpa using this

theorem norm_R_le_sq (s : ℂ) (hs : 0 ≤ s.re) {K : ℕ} (hK : K ≠ 0) {c : ℝ} (hc : 1 ≤ c) :
    ‖R s K c‖ ≤ CB K * ‖poch s (2 * K)‖ * c ^ (-2 : ℝ) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hK
  refine (norm_R_le_crude s hK (by linarith) (by linarith)).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc (by linarith))
    (mul_nonneg (CB_nonneg K) (norm_nonneg _))

theorem summable_sq : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  simpa using this

theorem norm_R_shift_le (s : ℂ) (hs : 0 ≤ s.re) {K : ℕ} (hK : K ≠ 0) {a : ℝ} (ha : 1 ≤ a)
    (n : ℕ) : ‖R s K (a + n)‖ ≤ CB K * ‖poch s (2 * K)‖ * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  refine (norm_R_le_sq s hs hK (by linarith)).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
    (by norm_num)) (mul_nonneg (CB_nonneg K) (norm_nonneg _))

theorem summable_R (s : ℂ) (hs : 0 ≤ s.re) {K : ℕ} (hK : K ≠ 0) {a : ℝ} (ha : 1 ≤ a) :
    Summable (fun n : ℕ => R s K (a + n)) :=
  Summable.of_norm_bounded (summable_sq.mul_left _) (norm_R_shift_le s hs hK ha)

/-! ## 6. Summing over the unit intervals for `Re s > 1` -/

theorem tendsto_cpow_shift {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun N : ℕ => ((a + N : ℝ) : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_neg_atTop (y := -w.re) (by linarith)).comp h1
  refine h2.congr (fun N => ?_)
  have hN : (0 : ℝ) ≤ N := N.cast_nonneg
  simp only [Function.comp_apply, neg_neg]
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]

theorem tendsto_T (s : ℂ) (hs : 1 < s.re) (K : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => T s K (a + N)) atTop (𝓝 0) := by
  have h1 := tendsto_cpow_shift ha (w := 1 - s) (by simp; linarith)
  have h2 := tendsto_cpow_shift ha (w := -s) (by simp; linarith)
  have h3 : ∀ k ∈ Finset.range K, Tendsto (fun N : ℕ =>
      (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) * poch s (2 * k + 1) *
        ((a + N : ℝ) : ℂ) ^ (-s - (2 * k + 1))) atTop (𝓝 0) := by
    intro k _
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have := (tendsto_cpow_shift ha (w := -s - (2 * k + 1)) (by simp; linarith)).const_mul
      ((bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) * poch s (2 * k + 1))
    simpa using this
  have := ((h1.div_const (s - 1)).add (h2.div_const 2)).add (tendsto_finsetSum _ h3)
  simpa [T] using this

theorem hasSum_telescope {f : ℕ → ℂ} (hs : Summable (fun n => f n - f (n + 1)))
    (hf : Tendsto f atTop (𝓝 0)) : HasSum (fun n => f n - f (n + 1)) (f 0) := by
  have h1 := hs.hasSum.tendsto_sum_nat
  simp_rw [Finset.sum_range_sub'] at h1
  have h2 : Tendsto (fun n => f 0 - f n) atTop (𝓝 (f 0 - 0)) := tendsto_const_nhds.sub hf
  rw [sub_zero] at h2
  rw [← tendsto_nhds_unique h1 h2]
  exact hs.hasSum

theorem hasSum_shift (s : ℂ) (hs : 1 < s.re) {K : ℕ} (hK : 1 ≤ K) {a : ℝ} (ha : 1 ≤ a)
    (hsum : Summable (fun n : ℕ => ((a + n : ℝ) : ℂ) ^ (-s))) :
    HasSum (fun n : ℕ => ((a + n : ℝ) : ℂ) ^ (-s)) (T s K a - ∑' n : ℕ, R s K (a + n)) := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hR := summable_R s (by linarith) (by omega : K ≠ 0) ha
  have hid : ∀ n : ℕ, T s K (a + n) - T s K (a + ((n + 1 : ℕ) : ℝ)) =
      ((a + n : ℝ) : ℂ) ^ (-s) + R s K (a + n) := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have := cpow_eq_T_sub s hs1 hK (c := a + n) (by linarith)
    have e : a + ((n + 1 : ℕ) : ℝ) = a + n + 1 := by push_cast; ring
    rw [e]; linear_combination -this
  have hsT : Summable (fun n : ℕ => T s K (a + n) - T s K (a + ((n + 1 : ℕ) : ℝ))) := by
    simp_rw [hid]; exact hsum.add hR
  have h1 := hasSum_telescope (f := fun n : ℕ => T s K (a + n)) hsT (tendsto_T s hs K (by linarith))
  simp only [Nat.cast_zero, add_zero] at h1
  have h2 := h1.sub hR.hasSum
  convert h2 using 1
  ext n
  rw [hid]; ring

/-- **The Euler–Maclaurin identity for `Re s > 1`.** -/
theorem hurwitz_eq_of_one_lt {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) {M K : ℕ} (hM : 1 ≤ M)
    (hK : 1 ≤ K) {s : ℂ} (hs : 1 < s.re) :
    hurwitzZeta x s = ∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s) + T s K (M + x) -
      ∑' n : ℕ, R s K (M + x + n) := by
  have hH := hasSum_hurwitzZeta_of_one_lt_re (a := x) ⟨hx.1.le, hx.2⟩ hs
  have hf : (fun n : ℕ => 1 / ((n : ℂ) + (x : ℂ)) ^ s) =
      fun n : ℕ => ((n + x : ℝ) : ℂ) ^ (-s) := by
    ext n; rw [cpow_neg, one_div]; push_cast; rfl
  rw [hf] at hH
  rw [← hH.tsum_eq, ← hH.summable.sum_add_tsum_nat_add M]
  have hsh : Summable (fun n : ℕ => (((M + x : ℝ) + n : ℝ) : ℂ) ^ (-s)) := by
    have := (summable_nat_add_iff M).mpr hH.summable
    convert this using 2 with n
    push_cast; ring_nf
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 := hasSum_shift s hs hK (a := M + x) (by linarith [hx.1]) hsh
  have e : ∑' i : ℕ, ((((i + M : ℕ) : ℝ) + x : ℝ) : ℂ) ^ (-s) =
      ∑' n : ℕ, (((M + x : ℝ) + n : ℝ) : ℂ) ^ (-s) := by
    congr 1; ext n; push_cast; ring_nf
  rw [e, h2.tsum_eq]; ring

/-! ## 7. Analytic continuation to `Re s > 0`, `s ≠ 1` -/

/-- The Euler–Maclaurin main term `Σ_{m<M} (m+x)^{-s} + T s K (M+x)`. -/
def EMmain (x : ℝ) (M K : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s) + T s K (M + x)

/-- The total remainder `Σ_n R s K (M + x + n)`. -/
def EMrem (x : ℝ) (M K : ℕ) (s : ℂ) : ℂ := ∑' n : ℕ, R s K (M + x + n)

/-- The domain `{Re s > 0, s ≠ 1}`. -/
def V : Set ℂ := {s | 0 < s.re ∧ s ≠ 1}

theorem isOpen_V : IsOpen V := (isOpen_lt continuous_const continuous_re).inter isOpen_ne

theorem isPreconnected_V : IsPreconnected V := by
  have hA : IsPreconnected {s : ℂ | 0 < s.re ∧ 0 < s.im} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hD : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hB : IsPreconnected {s : ℂ | 0 < s.re ∧ s.im < 0} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hC : IsPreconnected {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hU : V = ({s : ℂ | 0 < s.re ∧ 0 < s.im} ∪ {s | 1 < s.re}) ∪
      ({s : ℂ | 0 < s.re ∧ s.im < 0} ∪ {s | 0 < s.re ∧ s.re < 1}) := by
    ext s
    simp only [V, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨h0, h1⟩
      rcases lt_trichotomy s.im 0 with h | h | h
      · exact Or.inr (Or.inl ⟨h0, h⟩)
      · rcases lt_trichotomy s.re 1 with h' | h' | h'
        · exact Or.inr (Or.inr ⟨h0, h'⟩)
        · exact absurd (Complex.ext (by simp [h']) (by simp [h])) h1
        · exact Or.inl (Or.inr h')
      · exact Or.inl (Or.inl ⟨h0, h⟩)
    · rintro ((⟨h0, h⟩ | h) | (⟨h0, h⟩ | ⟨h0, h⟩))
      · exact ⟨h0, fun e => by rw [e] at h; simp at h⟩
      · exact ⟨by linarith, fun e => by rw [e] at h; simp at h⟩
      · exact ⟨h0, fun e => by rw [e] at h; simp at h⟩
      · exact ⟨h0, fun e => by rw [e] at h; simp at h⟩
  rw [hU]
  refine IsPreconnected.union (2 - I) (Or.inr (by norm_num)) (Or.inl (by norm_num)) ?_ ?_
  · exact IsPreconnected.union (2 + I) (by norm_num) (by norm_num) hA hD
  · exact IsPreconnected.union (1 / 2 - I) (by norm_num) (by norm_num) hB hC

theorem differentiableAt_T {s : ℂ} (hs : s ≠ 1) (K : ℕ) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℂ (fun s => T s K t) s := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have hs' : s - 1 ≠ 0 := sub_ne_zero.2 hs
  unfold T poch
  fun_prop (disch := first | assumption | (left; assumption))

theorem differentiableAt_EMmain {x : ℝ} (hx : 0 < x) (M K : ℕ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (EMmain x M K) s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => ∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s)) s := by
    have : ∀ m : ℕ, ((m + x : ℝ) : ℂ) ≠ 0 := fun m => ofReal_ne_zero.2 (by positivity)
    fun_prop (disch := first | assumption | (left; apply this))
  exact h1.add (differentiableAt_T hs K (by positivity))

theorem differentiableOn_EMrem {x : ℝ} (hx : 0 < x) {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) :
    DifferentiableOn ℂ (EMrem x M K) V := by
  intro s0 hs0
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨hre, hne⟩ := hs0
  set r := min s0.re ‖s0 - 1‖ with hr
  have hr0 : 0 < r := lt_min hre (norm_pos_iff.2 (sub_ne_zero.2 hne))
  have hUV : ∀ s ∈ Metric.ball s0 r, 0 < s.re ∧ s ≠ 1 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    constructor
    · have h1 := abs_re_le_norm (s - s0)
      rw [sub_re] at h1
      have h2 : r ≤ s0.re := min_le_left _ _
      have h3 := neg_abs_le (s.re - s0.re)
      linarith
    · rintro rfl
      have : r ≤ ‖s0 - 1‖ := min_le_right _ _
      rw [norm_sub_rev] at hs; linarith
  set P0 : ℝ := ∏ i ∈ Finset.range (2 * K), (‖s0‖ + r + i) with hP0
  have hpoch : ∀ s ∈ Metric.ball s0 r, ‖poch s (2 * K)‖ ≤ P0 := by
    intro s hs
    rw [poch, norm_prod]
    apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    intro i _
    have h1 : ‖s‖ ≤ ‖s0‖ + r := by
      rw [Metric.mem_ball, dist_eq_norm] at hs
      calc ‖s‖ = ‖s0 + (s - s0)‖ := by ring_nf
        _ ≤ ‖s0‖ + ‖s - s0‖ := norm_add_le _ _
        _ ≤ ‖s0‖ + r := by linarith
    calc ‖s + i‖ ≤ ‖s‖ + ‖(i : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ + i := by rw [Complex.norm_natCast]
      _ ≤ ‖s0‖ + r + i := by linarith
  have hP0nn : 0 ≤ P0 := le_trans (norm_nonneg _) (hpoch s0 (Metric.mem_ball_self hr0))
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : (1 : ℝ) ≤ M + x := by linarith
  have hK0 : K ≠ 0 := by omega
  have hf : ∀ n : ℕ, DifferentiableOn ℂ (fun s => R s K (M + x + n)) (Metric.ball s0 r) := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hc : (0 : ℝ) < M + x + n := by linarith
    have hd : DifferentiableOn ℂ (fun s => T s K (M + x + n) - T s K (M + x + n + 1) -
        (((M + x + n : ℝ)) : ℂ) ^ (-s)) (Metric.ball s0 r) := by
      intro s hs
      have hs1 := (hUV s hs).2
      have hcz : (((M + x + n : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
      refine (((differentiableAt_T hs1 K hc).sub (differentiableAt_T hs1 K (by linarith))).sub
        ?_).differentiableWithinAt
      fun_prop (disch := first | assumption | (left; assumption))
    refine hd.congr (fun s hs => ?_)
    have := cpow_eq_T_sub s (hUV s hs).2 hK hc
    linear_combination this
  have hbd : ∀ (n : ℕ), ∀ s ∈ Metric.ball s0 r,
      ‖R s K (M + x + n)‖ ≤ CB K * P0 * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
    intro n s hs
    refine (norm_R_shift_le s (hUV s hs).1.le hK0 ha n).trans ?_
    gcongr
    · exact CB_nonneg K
    · exact hpoch s hs
  have hdiff := differentiableOn_tsum_of_summable_norm (summable_sq.mul_left (CB K * P0)) hf
    Metric.isOpen_ball hbd
  exact hdiff.differentiableAt (Metric.ball_mem_nhds s0 hr0)

/-- **The Euler–Maclaurin identity on `Re s > 0`, `s ≠ 1`.** -/
theorem hurwitzZeta_eq_EM {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) {M K : ℕ} (hM : 1 ≤ M)
    (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    hurwitzZeta x s = EMmain x M K s - EMrem x M K s := by
  have hL : DifferentiableOn ℂ (fun s => hurwitzZeta x s) V :=
    fun s hs => (differentiableAt_hurwitzZeta _ hs.2).differentiableWithinAt
  have hR : DifferentiableOn ℂ (fun s => EMmain x M K s - EMrem x M K s) V :=
    DifferentiableOn.sub (fun s hs => (differentiableAt_EMmain hx.1 M K hs.2).differentiableWithinAt)
      (differentiableOn_EMrem hx.1 hM hK)
  have h2V : (2 : ℂ) ∈ V := ⟨by norm_num, by norm_num⟩
  have hev : (fun s => hurwitzZeta x s) =ᶠ[𝓝 2] (fun s => EMmain x M K s - EMrem x M K s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hurwitz_eq_of_one_lt hx hM hK hz
  exact (hL.analyticOnNhd isOpen_V).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd isOpen_V) isPreconnected_V h2V hev ⟨hs, hs1⟩

/-! ## 8. The remainder bound -/

theorem norm_EMrem_le {x : ℝ} (hx : 0 < x) {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) {s : ℂ}
    (hs : 0 < s.re) :
    ‖EMrem x M K s‖ ≤
      CB K * ‖poch s (2 * K)‖ * ((M + x : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1)) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set a : ℝ := M + x with ha_def
  have ha : 1 ≤ a := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : K ≠ 0 := by omega
  have hσ : 0 < s.re + 2 * K - 1 := by linarith
  set q : ℝ := 1 - s.re - 2 * K with hq
  have hq0 : q < 0 := by linarith
  set h : ℝ → ℝ := fun t => t ^ q / (s.re + 2 * K - 1) with hh
  have hR := summable_R s hs.le hK0 ha
  have hmono : ∀ n : ℕ, 0 ≤ h (a + n) - h (a + n + 1) := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    simp only [hh]
    rw [← sub_div]
    apply div_nonneg _ hσ.le
    rw [sub_nonneg]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hq0.le
  have hlim : Tendsto (fun N : ℕ => h (a + N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop
    have h2 := ((tendsto_rpow_neg_atTop (y := -q) (by linarith)).comp h1).div_const
      (s.re + 2 * K - 1)
    simp only [neg_neg, zero_div] at h2
    exact h2
  have hg0 : HasSum (fun n : ℕ => h (a + n) - h (a + n + 1)) (h a) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hmono]
    have e : ∀ N : ℕ, ∑ i ∈ Finset.range N, (h (a + i) - h (a + i + 1)) = h a - h (a + N) := by
      intro N
      have := Finset.sum_range_sub' (fun i : ℕ => h (a + i)) N
      simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, ← add_assoc] at this
      exact this
    simp_rw [e]
    have := (tendsto_const_nhds (x := h a)).sub hlim
    rwa [sub_zero] at this
  have hg := hg0.mul_left (CB K * ‖poch s (2 * K)‖)
  refine (hR.hasSum.norm_le_of_bounded hg (fun n => ?_)).trans (le_of_eq ?_)
  · have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    refine (norm_R_le s hK0 (c := a + n) (by linarith) hσ).trans (le_of_eq ?_)
    simp only [hh]
    ring
  · simp only [hh]

/-! ## 9. The main theorem, stated with everything explicit -/

/-- **Euler–Maclaurin for the Hurwitz zeta function, with explicit remainder.**
For `x ∈ (0, 1]`, `M ≥ 1`, `K ≥ 1` and `Re s > 0`, `s ≠ 1`:
`ζ(s, x) = Σ_{m<M} (m+x)^{-s} + (M+x)^{1-s}/(s-1) + (M+x)^{-s}/2
          + Σ_{k<K} B_{2k+2}/(2k+2)! · s(s+1)⋯(s+2k) · (M+x)^{-s-2k-1} + R`,
with `‖R‖ ≤ |B_{2K}|/(2K)! · ‖s(s+1)⋯(s+2K-1)‖ · (M+x)^{1-Re s-2K}/(Re s+2K-1)`. -/
theorem norm_hurwitzZeta_sub_EM_le {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) {M K : ℕ} (hM : 1 ≤ M)
    (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖hurwitzZeta x s -
        (∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s) +
          ((M + x : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((M + x : ℝ) : ℂ) ^ (-s) / 2 +
          ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
            (∏ i ∈ Finset.range (2 * k + 1), (s + i)) * ((M + x : ℝ) : ℂ) ^ (-s - (2 * k + 1)))‖
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ‖∏ i ∈ Finset.range (2 * K), (s + i)‖ *
          ((M + x : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1)) := by
  have e : (∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s) +
          ((M + x : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((M + x : ℝ) : ℂ) ^ (-s) / 2 +
          ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
            (∏ i ∈ Finset.range (2 * k + 1), (s + i)) * ((M + x : ℝ) : ℂ) ^ (-s - (2 * k + 1)))
      = EMmain x M K s := by
    unfold EMmain T poch; ring
  rw [e, hurwitzZeta_eq_EM hx hM hK hs hs1, sub_sub_cancel_left, norm_neg]
  exact norm_EMrem_le hx.1 hM hK hs

/-- The same, as an exact identity with the remainder given explicitly as a sum of integrals
`R = -Σ_n ∫_0^1 B_{2K}(u)/(2K)! · (s)_{2K} (M+x+n+u)^{-s-2K} du`. -/
theorem hurwitzZeta_eq_EM_explicit {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) {M K : ℕ} (hM : 1 ≤ M)
    (hK : 1 ≤ K) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    hurwitzZeta x s =
        ∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s) +
          ((M + x : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((M + x : ℝ) : ℂ) ^ (-s) / 2 +
          ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
            (∏ i ∈ Finset.range (2 * k + 1), (s + i)) * ((M + x : ℝ) : ℂ) ^ (-s - (2 * k + 1)) -
        ∑' n : ℕ, ∫ u in (0 : ℝ)..1,
          ((bernoulliFun (2 * K) u / ((2 * K)! : ℝ) : ℝ) : ℂ) *
            ((∏ i ∈ Finset.range (2 * K), (s + i)) * (((M + x + n : ℝ) + u : ℝ) : ℂ) ^ (-s - (2 * K : ℕ))) := by
  rw [hurwitzZeta_eq_EM hx hM hK hs hs1]
  unfold EMmain EMrem R Iint T Pb D poch
  congr 1
  · ring
  · congr 1; ext n; congr 1; ext u
    rw [Even.neg_one_pow ⟨K, by ring⟩, one_mul]

/-! ## 10. The constant, and a bound uniform on a box (for the minimum-modulus certificate) -/

/-- `C_K = 2ζ(2K)/(2π)^{2K}`, in `HasSum` form: `Σ_n 1/n^{2K} = C_K (2π)^{2K}/2`. -/
theorem hasSum_zeta_CB {K : ℕ} (hK : K ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * K)) (CB K * (2 * Real.pi) ^ (2 * K) / 2) := by
  have h2 := hasSum_zeta_nat hK
  have h2K : (2 : ℝ) ^ (2 * K - 1) * 2 = 2 ^ (2 * K) := by
    rw [← pow_succ]; congr 1; omega
  set C : ℝ := (2 * Real.pi) ^ (2 * K) / 2 / ((2 * K)! : ℝ) with hC
  have hCpos : 0 < C := by positivity
  have e2 : (-1 : ℝ) ^ (K + 1) * 2 ^ (2 * K - 1) * Real.pi ^ (2 * K) * (bernoulli (2 * K) : ℝ) /
      ((2 * K)! : ℝ) = C * ((-1) ^ (K + 1) * (bernoulli (2 * K) : ℝ)) := by
    rw [hC, mul_pow, ← h2K]; ring
  rw [e2] at h2
  have hpos : 0 < C * ((-1) ^ (K + 1) * (bernoulli (2 * K) : ℝ)) := by
    have := le_hasSum h2 1 (fun j _ => by positivity)
    simp only [Nat.cast_one, one_pow, div_one] at this
    linarith
  have hB : (-1 : ℝ) ^ (K + 1) * (bernoulli (2 * K) : ℝ) = |(bernoulli (2 * K) : ℝ)| := by
    have h0 : 0 < (-1 : ℝ) ^ (K + 1) * (bernoulli (2 * K) : ℝ) := pos_of_mul_pos_right hpos hCpos.le
    rw [← abs_of_pos h0, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  convert h2 using 1
  rw [hB, hC, CB]
  ring

/-- `C_K ≤ (π²/3)/(2π)^{2K}` (from `ζ(2K) ≤ ζ(2) = π²/6`). -/
theorem CB_le {K : ℕ} (hK : K ≠ 0) : CB K ≤ (Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) := by
  have h1 := hasSum_zeta_CB hK
  have hle : CB K * (2 * Real.pi) ^ (2 * K) / 2 ≤ Real.pi ^ 2 / 6 := by
    refine hasSum_le (fun n => ?_) h1 hasSum_zeta_two
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hK]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ hn1 (by omega)
  have hpos : 0 < (2 * Real.pi) ^ (2 * K) := by positivity
  rw [le_div_iff₀ hpos]
  linarith

/-- `‖s(s+1)⋯(s+n-1)‖² ≤ Π_{i<n} ((σ₁+i)² + τ²)` for `0 ≤ Re s ≤ σ₁`, `|Im s| ≤ τ`. -/
theorem norm_poch_sq_le {s : ℂ} {σ₁ τ : ℝ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ σ₁) (hT : |s.im| ≤ τ)
    (n : ℕ) : ‖poch s n‖ ^ 2 ≤ ∏ i ∈ Finset.range n, ((σ₁ + i) ^ 2 + τ ^ 2) := by
  rw [poch, norm_prod, ← Finset.prod_pow]
  apply Finset.prod_le_prod₀ (fun i _ => by positivity)
  intro i _
  have hi : (0 : ℝ) ≤ i := i.cast_nonneg
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [add_re, natCast_re, add_im, natCast_im, add_zero]
  have e1 : (s.re + i) * (s.re + i) ≤ (σ₁ + i) ^ 2 := by nlinarith
  have e2 : s.im * s.im ≤ τ ^ 2 := by
    have := sq_abs s.im
    nlinarith [abs_nonneg s.im]
  linarith

/-- **Uniform bound on a box** `σ₀ ≤ Re s ≤ σ₁`, `|Im s| ≤ τ` (`σ₀ > 0`), for any `B ≥ 0` with
`Π_{i<2K} ((σ₁+i)² + τ²) ≤ B²`:
`‖ζ(s,x) − EM‖ ≤ (π²/3)/(2π)^{2K} · B · (M+x)^{1−σ₀−2K}/(σ₀+2K−1)`. -/
theorem norm_EMrem_le_box {x : ℝ} (hx : 0 < x) {M K : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K)
    {σ₀ σ₁ τ B : ℝ} (hσ₀ : 0 < σ₀) (hB : 0 ≤ B)
    (hPB : ∏ i ∈ Finset.range (2 * K), ((σ₁ + i) ^ 2 + τ ^ 2) ≤ B ^ 2)
    {s : ℂ} (hs0 : σ₀ ≤ s.re) (hs1 : s.re ≤ σ₁) (hsT : |s.im| ≤ τ) :
    ‖EMrem x M K s‖ ≤ (Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) * B *
      ((M + x : ℝ) ^ (1 - σ₀ - 2 * K) / (σ₀ + 2 * K - 1)) := by
  have hK0 : K ≠ 0 := by omega
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : (1 : ℝ) ≤ M + x := by linarith
  have hsre : 0 < s.re := by linarith
  refine (norm_EMrem_le hx hM hK hsre).trans ?_
  have hP : ‖poch s (2 * K)‖ ≤ B := by
    have := (norm_poch_sq_le hsre.le hs1 hsT (2 * K)).trans hPB
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB (by norm_num)).1 this
  have hpow : (M + x : ℝ) ^ (1 - s.re - 2 * K) ≤ (M + x : ℝ) ^ (1 - σ₀ - 2 * K) :=
    Real.rpow_le_rpow_of_exponent_le ha (by linarith)
  have hden : (M + x : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1) ≤
      (M + x : ℝ) ^ (1 - σ₀ - 2 * K) / (σ₀ + 2 * K - 1) := by
    apply div_le_div₀ (by positivity) hpow (by linarith) (by linarith)
  have hq : 0 ≤ (M + x : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1) := by
    apply div_nonneg (by positivity) (by linarith)
  calc CB K * ‖poch s (2 * K)‖ * ((M + x : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1))
      ≤ (Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) * B *
          ((M + x : ℝ) ^ (1 - s.re - 2 * K) / (s.re + 2 * K - 1)) := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul (CB_le hK0) hP (norm_nonneg _) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

/-- The box version of the main theorem, with the main term written out. -/
theorem norm_hurwitzZeta_sub_EM_le_box {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) {M K : ℕ} (hM : 1 ≤ M)
    (hK : 1 ≤ K) {σ₀ σ₁ τ B : ℝ} (hσ₀ : 0 < σ₀) (hB : 0 ≤ B)
    (hPB : ∏ i ∈ Finset.range (2 * K), ((σ₁ + i) ^ 2 + τ ^ 2) ≤ B ^ 2)
    {s : ℂ} (hs0 : σ₀ ≤ s.re) (hs1 : s.re ≤ σ₁) (hsT : |s.im| ≤ τ) (hs : s ≠ 1) :
    ‖hurwitzZeta x s -
        (∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s) +
          ((M + x : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((M + x : ℝ) : ℂ) ^ (-s) / 2 +
          ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
            (∏ i ∈ Finset.range (2 * k + 1), (s + i)) * ((M + x : ℝ) : ℂ) ^ (-s - (2 * k + 1)))‖
      ≤ (Real.pi ^ 2 / 3) / (2 * Real.pi) ^ (2 * K) * B *
          ((M + x : ℝ) ^ (1 - σ₀ - 2 * K) / (σ₀ + 2 * K - 1)) := by
  have e : (∑ m ∈ Finset.range M, ((m + x : ℝ) : ℂ) ^ (-s) +
          ((M + x : ℝ) : ℂ) ^ (1 - s) / (s - 1) + ((M + x : ℝ) : ℂ) ^ (-s) / 2 +
          ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
            (∏ i ∈ Finset.range (2 * k + 1), (s + i)) * ((M + x : ℝ) : ℂ) ^ (-s - (2 * k + 1)))
      = EMmain x M K s := by
    unfold EMmain T poch; ring
  rw [e, hurwitzZeta_eq_EM hx hM hK (by linarith) hs, sub_sub_cancel_left, norm_neg]
  exact norm_EMrem_le_box hx.1 hM hK hσ₀ hB hPB hs0 hs1 hsT

end HurwitzEM

open HurwitzEM in
#print axioms norm_hurwitzZeta_sub_EM_le
open HurwitzEM in
#print axioms hurwitzZeta_eq_EM_explicit
open HurwitzEM in
#print axioms norm_hurwitzZeta_sub_EM_le_box
open HurwitzEM in
#print axioms hasSum_zeta_CB
open HurwitzEM in
#print axioms CB_le
open HurwitzEM in
#print axioms hurwitzZeta_eq_EM
open HurwitzEM in
#print axioms norm_EMrem_le_box
