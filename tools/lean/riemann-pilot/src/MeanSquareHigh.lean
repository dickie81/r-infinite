import Mathlib
import HurwitzEM
import MeanSquareZeta

/-! # The mean square of ζ on Re s ≥ (2K+1)/(4K+1), from the Euler–Maclaurin formula of order 2K (round 402)

Round 401's mean square stops at `Re s = 2/3` because the first-order Euler–Maclaurin remainder needs
`N ≥ M^{1/σ}` terms while the mean value theorem's off-diagonal term `N^{2−2σ}` must stay below `M`. Round 264's
Euler–Maclaurin formula for the Hurwitz zeta function (`HurwitzEM.norm_hurwitzZeta_sub_EM_le`), of every even order
`2K`, at `x = 1` approximates `ζ` with remainder `≪ |t|^{2K} N^{1−σ−2K}`; the two requirements then meet at
`σ = (2K+1)/(4K+1)`.

* **`norm_zeta_sub_partial_le`**: for `K ≥ 1`, `N ≥ 1`, `0 < σ ≤ 4`, `|t| ≥ 2`, `|t| ≤ N + 1` and
  `|t|^{2K} ≤ (N+1)^{σ+2K−1}`, `|ζ(σ+it) − Σ_{n≤N} n^{−σ−it}| ≤ (N+1)^{1−σ}/|t| + CE K`.
* **`mean_square_of_pointwise`**: such a pointwise bound `X/|t| + C`, with `∫|Σ_{n≤N}|² ≤ B`, gives
  `∫|ζ|² ≤ 2B + 2X² + 4C²(b − a)`.
* **`mean_square_partial_gen`**: `∫_a^b |Σ_{n≤2^J} n^{−σ−it}|² ≤ (J+1)²(b − a + 8(J+1)(2^J)^{2−2σ₀})` for
  `σ ≥ σ₀ ∈ [½, 1]`.
* **`mean_square_zeta_le_order`**: for `σ ∈ [σ₀, 4]`, `[a, b]` with `2 ≤ |t| ≤ M` on it and
  `M^{2K} ≤ (2^J)^{σ₀+2K−1}`, `∫_a^b |ζ(σ+it)|² ≤ 2(J+1)²(b − a + 8(J+1)Q) + 4Q + 4·CE(K)²(b − a)`,
  `Q = (2^J)^{2−2σ₀}`.
* **`msPoly_of_order`**: for `K ≥ 1` and `(2K+1)/(4K+1) ≤ σ₀ ≤ 1`, `MSPoly σ₀`: some `A ≥ 0` has
  `∫_a^b |ζ(σ+it)|² ≤ A (log M)³ (b − a + M)` for every such `σ` and `[a, b]`.
-/

open Real Complex MeasureTheory Set Finset
open scoped Nat

noncomputable section

namespace MeanSquareHigh

open DirMean MeanSquareZeta

/-- The constant of the order-`2K` error bound. -/
def CE (K : ℕ) : ℝ :=
  1 / 2 + ∑ k ∈ range K, |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) * ((2 * K + 3 : ℕ) : ℝ) ^ (2 * k + 1)
    + |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ((2 * K + 3 : ℕ) : ℝ) ^ (2 * K)

lemma CE_nonneg (K : ℕ) : 0 ≤ CE K := by
  unfold CE; positivity

/-- One factor of the rising factorial: `|s + i| ≤ (2K+3)|t|` for `i < 2K`, `0 < σ ≤ 4`, `|t| ≥ 2`. -/
lemma norm_add_nat_le {K i : ℕ} (hi : i < 2 * K) {σ t : ℝ} (hσ0 : 0 < σ) (hσ4 : σ ≤ 4) (ht : 2 ≤ |t|) :
    ‖((σ : ℂ) + t * I) + i‖ ≤ ((2 * K + 3 : ℕ) : ℝ) * |t| := by
  have h1 : ‖((σ : ℂ) + t * I) + i‖ ≤ (σ + i) + |t| := by
    have e : ((σ : ℂ) + t * I) + i = ((σ + i : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hi' : (i : ℝ) + 1 ≤ 2 * K := by exact_mod_cast hi
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  push_cast
  nlinarith [mul_nonneg hK0 (show (0 : ℝ) ≤ |t| - 2 by linarith)]

/-- The rising factorial `s(s+1)⋯(s+j−1)` for `j ≤ 2K` is at most `((2K+3)|t|)^j`. -/
lemma norm_prod_add_le {K j : ℕ} (hj : j ≤ 2 * K) {σ t : ℝ} (hσ0 : 0 < σ) (hσ4 : σ ≤ 4) (ht : 2 ≤ |t|) :
    ‖∏ i ∈ range j, (((σ : ℂ) + t * I) + i)‖ ≤ (((2 * K + 3 : ℕ) : ℝ) * |t|) ^ j := by
  rw [norm_prod]
  calc ∏ i ∈ range j, ‖((σ : ℂ) + t * I) + i‖ ≤ ∏ _i ∈ range j, (((2 * K + 3 : ℕ) : ℝ) * |t|) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i hi =>
          norm_add_nat_le (by have := mem_range.1 hi; omega) hσ0 hσ4 ht
    _ = _ := by rw [prod_const, card_range]

/-- `Σ_{m<N} (m+1)^{−s} = Σ_{0<n≤N} n^{−s}`. -/
lemma sum_range_succ_cpow (N : ℕ) (s : ℂ) :
    ∑ m ∈ range N, (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s) = ∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-s) := by
  have hmap : Finset.Ioc 0 N = (range N).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩; omega
  rw [hmap, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  push_cast
  rfl

/-- **The order-`2K` approximation of `ζ` by its partial sums** (from round 264's Euler–Maclaurin formula for the
Hurwitz zeta function at `x = 1`): for `0 < σ ≤ 4`, `|t| ≥ 2`, `|t| ≤ N + 1` and `|t|^{2K} ≤ (N+1)^{σ+2K−1}`,
`|ζ(σ+it) − Σ_{n≤N} n^{−σ−it}| ≤ (N+1)^{1−σ}/|t| + CE K`. -/
theorem norm_zeta_sub_partial_le {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) {σ t : ℝ} (hσ0 : 0 < σ)
    (hσ4 : σ ≤ 4) (ht : 2 ≤ |t|) (htN : |t| ≤ N + 1)
    (hrem : |t| ^ (2 * K) ≤ ((N : ℝ) + 1) ^ (σ + 2 * K - 1)) :
    ‖riemannZeta (σ + t * I) - ∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-((σ : ℂ) + t * I))‖
      ≤ ((N : ℝ) + 1) ^ (1 - σ) / |t| + CE K := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have ht0 : 0 < |t| := by linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this
    rw [this, abs_zero] at ht; norm_num at ht
  have hEM := HurwitzEM.norm_hurwitzZeta_sub_EM_le (x := 1) ⟨one_pos, le_rfl⟩ hN hK
    (by rw [hsre]; exact hσ0) hs1
  have hz : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s = riemannZeta s := by
    rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero]
  rw [hz, sum_range_succ_cpow N s, hsre] at hEM
  set ν : ℝ := (N : ℝ) + 1 with hν
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hν1 : 1 ≤ ν := by rw [hν]; linarith
  have hν0 : 0 < ν := by linarith
  set P : ℂ := ∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-s) with hP
  set A1 : ℂ := ((ν : ℝ) : ℂ) ^ (1 - s) / (s - 1) with hA1
  set A2 : ℂ := ((ν : ℝ) : ℂ) ^ (-s) / 2 with hA2
  set A3 : ℂ := ∑ k ∈ Finset.range K, (bernoulli (2 * k + 2) : ℂ) / ((2 * k + 2)! : ℂ) *
      (∏ i ∈ Finset.range (2 * k + 1), (s + i)) * ((ν : ℝ) : ℂ) ^ (-s - (2 * k + 1)) with hA3
  have hνc : (((N : ℝ) + 1 : ℝ) : ℂ) = ((ν : ℝ) : ℂ) := rfl
  -- the three explicit terms
  have h1 : ‖A1‖ ≤ ν ^ (1 - σ) / |t| := by
    rw [hA1, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hν0]
    have hre : (1 - s).re = 1 - σ := by simp [hsre]
    rw [hre]
    apply div_le_div_of_nonneg_left (by positivity) ht0
    have := Complex.abs_im_le_norm (s - 1)
    simpa [hsim] using this
  have h2 : ‖A2‖ ≤ 1 / 2 := by
    rw [hA2, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hν0]
    have hre : (-s).re = -σ := by simp [hsre]
    rw [hre, Complex.norm_ofNat]
    have : ν ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hν1 (by linarith)
    linarith
  have h3 : ‖A3‖ ≤ ∑ k ∈ range K,
      |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) * ((2 * K + 3 : ℕ) : ℝ) ^ (2 * k + 1) := by
    rw [hA3]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hkK : 2 * k + 1 ≤ 2 * K := by have := mem_range.1 hk; omega
    rw [norm_mul, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hν0]
    have hre : (-s - (2 * (k : ℂ) + 1)).re = -σ - (2 * k + 1) := by simp [hsre]
    rw [hre]
    have hB : ‖(bernoulli (2 * k + 2) : ℂ)‖ = |(bernoulli (2 * k + 2) : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    have hF : ‖((2 * k + 2)! : ℂ)‖ = ((2 * k + 2)! : ℝ) := by
      rw [Complex.norm_natCast]
    rw [hB, hF]
    have hprod := norm_prod_add_le (K := K) hkK hσ0 hσ4 ht
    have hpow : (((2 * K + 3 : ℕ) : ℝ) * |t|) ^ (2 * k + 1) * ν ^ (-σ - (2 * k + 1))
        ≤ ((2 * K + 3 : ℕ) : ℝ) ^ (2 * k + 1) := by
      rw [mul_pow, mul_assoc]
      have hc0 : (0 : ℝ) ≤ ((2 * K + 3 : ℕ) : ℝ) ^ (2 * k + 1) := by positivity
      refine mul_le_of_le_one_right hc0 ?_
      have e : ν ^ (-σ - (2 * k + 1)) = ν ^ (-σ) * (ν ^ (2 * k + 1))⁻¹ := by
        rw [Real.rpow_sub hν0, ← Real.rpow_natCast, div_eq_mul_inv]; push_cast; ring_nf
      rw [e]
      have ht1 : |t| ^ (2 * k + 1) ≤ ν ^ (2 * k + 1) := pow_le_pow_left₀ (abs_nonneg t) htN _
      have hνp : 0 < ν ^ (2 * k + 1) := by positivity
      have hσp : ν ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hν1 (by linarith)
      have hσp0 : 0 ≤ ν ^ (-σ) := by positivity
      calc |t| ^ (2 * k + 1) * (ν ^ (-σ) * (ν ^ (2 * k + 1))⁻¹)
          = ν ^ (-σ) * (|t| ^ (2 * k + 1) / ν ^ (2 * k + 1)) := by ring
        _ ≤ 1 * 1 := by
            refine mul_le_mul hσp ?_ (by positivity) zero_le_one
            rw [div_le_one hνp]; exact ht1
        _ = 1 := one_mul 1
    have hBn : 0 ≤ |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) := by positivity
    calc |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) * ‖∏ i ∈ Finset.range (2 * k + 1), (s + i)‖
          * ν ^ (-σ - (2 * k + 1))
        ≤ |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) * (((2 * K + 3 : ℕ) : ℝ) * |t|) ^ (2 * k + 1)
          * ν ^ (-σ - (2 * k + 1)) := by gcongr
      _ = |(bernoulli (2 * k + 2) : ℝ)| / ((2 * k + 2)! : ℝ) *
          ((((2 * K + 3 : ℕ) : ℝ) * |t|) ^ (2 * k + 1) * ν ^ (-σ - (2 * k + 1))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hBn
  -- the remainder
  have h4 : ‖riemannZeta s - (P + A1 + A2 + A3)‖
      ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ((2 * K + 3 : ℕ) : ℝ) ^ (2 * K) := by
    refine hEM.trans ?_
    have hprod := norm_prod_add_le (K := K) (j := 2 * K) le_rfl hσ0 hσ4 ht
    have hCB : 0 ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) := by positivity
    have hden : 1 ≤ σ + 2 * K - 1 := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    have hkey : |t| ^ (2 * K) * ν ^ (1 - σ - 2 * K) ≤ 1 := by
      have e : ν ^ (1 - σ - 2 * K) = (ν ^ (σ + 2 * K - 1))⁻¹ := by
        rw [← Real.rpow_neg hν0.le]; congr 1; ring
      rw [e, ← div_eq_mul_inv, div_le_one (by positivity)]
      exact hrem
    calc |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ‖∏ i ∈ Finset.range (2 * K), (s + i)‖ *
          (ν ^ (1 - σ - 2 * K) / (σ + 2 * K - 1))
        ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * (((2 * K + 3 : ℕ) : ℝ) * |t|) ^ (2 * K) *
          (ν ^ (1 - σ - 2 * K) / 1) := by
          gcongr
      _ = |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ((2 * K + 3 : ℕ) : ℝ) ^ (2 * K) *
          (|t| ^ (2 * K) * ν ^ (1 - σ - 2 * K)) := by rw [mul_pow, div_one]; ring
      _ ≤ |(bernoulli (2 * K) : ℝ)| / ((2 * K)! : ℝ) * ((2 * K + 3 : ℕ) : ℝ) ^ (2 * K) * 1 :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = _ := mul_one _
  -- assemble
  have hsplit : riemannZeta s - P = (riemannZeta s - (P + A1 + A2 + A3)) + A1 + A2 + A3 := by ring
  rw [hsplit]
  have hn1 := norm_add_le (riemannZeta s - (P + A1 + A2 + A3) + A1 + A2) A3
  have hn2 := norm_add_le (riemannZeta s - (P + A1 + A2 + A3) + A1) A2
  have hn3 := norm_add_le (riemannZeta s - (P + A1 + A2 + A3)) A1
  unfold CE
  linarith [h1, h2, h3, h4]

/-- **The mean square of `ζ` from a pointwise approximation**: if `|ζ(σ+it) − D(t)| ≤ X/|t| + C` on `[a, b]`, where
`D` is the partial sum up to `N` and `|t| ≥ 2` on `[a, b]`, and `∫|D|² ≤ B`, then `∫|ζ|² ≤ 2B + 2X² + 4C²(b − a)`. -/
theorem mean_square_of_pointwise {σ a b X C B : ℝ} {N : ℕ} (hab : a ≤ b) (hside : 2 ≤ a ∨ b ≤ -2)
    (hE : ∀ t ∈ Icc a b, ‖riemannZeta (σ + t * I) - ∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-((σ : ℂ) + t * I))‖
      ≤ X / |t| + C)
    (hD : ∫ t in a..b, ‖∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2 ≤ B) :
    ∫ t in a..b, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ 2 * B + 2 * X ^ 2 + 4 * C ^ 2 * (b - a) := by
  have habs : ∀ t ∈ Icc a b, 2 ≤ |t| := by
    intro t ht
    rcases hside with h | h
    · rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    · rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]
  set D : ℝ → ℂ := fun t => ∑ n ∈ Finset.Ioc 0 N, (n : ℂ) ^ (-((σ : ℂ) + t * I)) with hDdef
  have hne : ∀ t ∈ Icc a b, (σ : ℂ) + t * I ≠ 1 := by
    intro t ht h
    have := congrArg Complex.im h
    simp at this
    have := habs t ht
    rw [‹t = 0›, abs_zero] at this
    norm_num at this
  have hzcont : ContinuousOn (fun t : ℝ => ‖riemannZeta (σ + t * I)‖ ^ 2) (Icc a b) := by
    intro t ht
    have hin : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
    have h1 : ContinuousAt (fun t : ℝ => riemannZeta (σ + t * I)) t :=
      ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I)
        (differentiableAt_riemannZeta (hne t ht)).continuousAt hin.continuousAt
    exact (h1.norm.pow 2).continuousWithinAt
  have hDc : Continuous D := by
    simp only [hDdef]
    refine continuous_finsetSum _ fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Ioc.1 hn).1
      exact_mod_cast (show n ≠ 0 by omega)
    exact (by fun_prop : Continuous fun t : ℝ => -((σ : ℂ) + t * I)).const_cpow (Or.inl hn0)
  have hDcont : Continuous fun t => ‖D t‖ ^ 2 := hDc.norm.pow 2
  have hne0 : ∀ t ∈ Icc a b, t ≠ 0 := by
    intro t ht h; have := habs t ht; rw [h, abs_zero] at this; norm_num at this
  have hmajcont : ContinuousOn (fun t : ℝ => 2 * ‖D t‖ ^ 2 + (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2))
      (Icc a b) :=
    (continuous_const.mul hDcont).continuousOn.add
      ((continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne0 t ht))).add
        continuousOn_const)
  have hpt : ∀ t ∈ Icc a b,
      ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ 2 * ‖D t‖ ^ 2 + (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2) := by
    intro t ht
    have h1 : ‖riemannZeta (σ + t * I)‖ ≤ ‖D t‖ + ‖riemannZeta (σ + t * I) - D t‖ := by
      have := norm_add_le (D t) (riemannZeta (σ + t * I) - D t)
      rwa [add_sub_cancel] at this
    have h2 := hE t ht
    have ht0 : 0 < |t| := by linarith [habs t ht]
    have hX : (X / |t|) ^ 2 = X ^ 2 * (t ^ 2)⁻¹ := by
      rw [div_pow, sq_abs, div_eq_mul_inv]
    have hE0 : 0 ≤ ‖riemannZeta (σ + t * I) - D t‖ := norm_nonneg _
    have hE2 : ‖riemannZeta (σ + t * I) - D t‖ ^ 2 ≤ (X / |t| + C) ^ 2 :=
      pow_le_pow_left₀ hE0 h2 2
    calc ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ (‖D t‖ + ‖riemannZeta (σ + t * I) - D t‖) ^ 2 := by
          gcongr
      _ ≤ 2 * ‖D t‖ ^ 2 + 2 * ‖riemannZeta (σ + t * I) - D t‖ ^ 2 := by
          nlinarith [sq_nonneg (‖D t‖ - ‖riemannZeta (σ + t * I) - D t‖)]
      _ ≤ 2 * ‖D t‖ ^ 2 + 2 * (X / |t| + C) ^ 2 := by linarith
      _ ≤ 2 * ‖D t‖ ^ 2 + 2 * (2 * (X / |t|) ^ 2 + 2 * C ^ 2) := by
          nlinarith [sq_nonneg (X / |t| - C)]
      _ = 2 * ‖D t‖ ^ 2 + (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2) := by rw [hX]; ring
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint_maj : IntervalIntegrable (fun t : ℝ => 2 * ‖D t‖ ^ 2 + (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2))
      volume a b := (hIcc ▸ hmajcont).intervalIntegrable
  have hint_z : IntervalIntegrable (fun t : ℝ => ‖riemannZeta (σ + t * I)‖ ^ 2) volume a b :=
    (hIcc ▸ hzcont).intervalIntegrable
  have hinvint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a b :=
    (hIcc ▸ ((continuousOn_pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne0 t ht))).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hab hint_z hint_maj hpt
  have hsplit : ∫ t in a..b, 2 * ‖D t‖ ^ 2 + (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2)
      = 2 * (∫ t in a..b, ‖D t‖ ^ 2) + 4 * X ^ 2 * (∫ t in a..b, (t ^ 2)⁻¹) + 4 * C ^ 2 * (b - a) := by
    have e1 : ∫ t in a..b, 2 * ‖D t‖ ^ 2 + (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2)
        = (∫ t in a..b, 2 * ‖D t‖ ^ 2) + ∫ t in a..b, (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2) :=
      intervalIntegral.integral_add ((hDcont.intervalIntegrable a b).const_mul 2)
        ((hinvint.const_mul (4 * X ^ 2)).add intervalIntegrable_const)
    have e2 : ∫ t in a..b, (4 * X ^ 2 * (t ^ 2)⁻¹ + 4 * C ^ 2)
        = (∫ t in a..b, 4 * X ^ 2 * (t ^ 2)⁻¹) + ∫ _ in a..b, (4 * C ^ 2 : ℝ) :=
      intervalIntegral.integral_add (hinvint.const_mul (4 * X ^ 2)) intervalIntegrable_const
    have e3 : ∫ t in a..b, 2 * ‖D t‖ ^ 2 = 2 * ∫ t in a..b, ‖D t‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    have e4 : ∫ t in a..b, 4 * X ^ 2 * (t ^ 2)⁻¹ = 4 * X ^ 2 * ∫ t in a..b, (t ^ 2)⁻¹ :=
      intervalIntegral.integral_const_mul _ _
    have e5 : ∫ _ in a..b, (4 * C ^ 2 : ℝ) = (b - a) * (4 * C ^ 2) := by simp; ring
    rw [e1, e2, e3, e4, e5]
    ring
  have hinv := integral_inv_sq_le hab hside
  rw [hsplit] at hmono
  have h4 : 4 * X ^ 2 * (∫ t in a..b, (t ^ 2)⁻¹) ≤ 4 * X ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have hD' : 2 * (∫ t in a..b, ‖D t‖ ^ 2) ≤ 2 * B := by simp only [hDdef]; linarith
  linarith [hmono, h4, hD']

/-- The dyadic block bound for `σ ≥ σ₀ ∈ [½, 1]`: for `P = 2^j` with `j ≤ J`,
`(b − a + 8P(1 + log P))·P·(P^{−σ})² ≤ (b − a) + 8(J + 1)(2^J)^{2−2σ₀}`. -/
lemma block_bound_gen {σ₀ σ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ ≤ 1) (hσ : σ₀ ≤ σ) {j J : ℕ} (hj : j ≤ J)
    {a b : ℝ} (hab : a ≤ b) :
    (b - a + 8 * (2 ^ j : ℕ) * (1 + Real.log (2 ^ j : ℕ))) * ((2 ^ j : ℕ) * (((2 ^ j : ℕ) : ℝ) ^ (-σ)) ^ 2)
      ≤ (b - a) + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) := by
  set P : ℝ := ((2 ^ j : ℕ) : ℝ) with hP
  have hP1 : 1 ≤ P := by rw [hP]; exact_mod_cast Nat.one_le_two_pow
  have hP0 : 0 < P := by linarith
  have hsq : P * (P ^ (-σ)) ^ 2 = P ^ (1 - 2 * σ) := by
    rw [← Real.rpow_natCast (P ^ (-σ)) 2, ← Real.rpow_mul hP0.le]
    rw [show (1 : ℝ) - 2 * σ = 1 + (-σ * ((2 : ℕ) : ℝ)) by push_cast; ring,
      Real.rpow_add hP0, Real.rpow_one]
  have hsq2 : P * P ^ (1 - 2 * σ) = P ^ (2 - 2 * σ) := by
    rw [show (2 : ℝ) - 2 * σ = 1 + (1 - 2 * σ) by ring, Real.rpow_add hP0, Real.rpow_one]
  rw [hsq]
  have h1 : P ^ (1 - 2 * σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
  have h2 : P ^ (2 - 2 * σ) ≤ P ^ (2 - 2 * σ₀) := Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hPJ : P ≤ (2 : ℝ) ^ J := by
    rw [hP]; push_cast; exact pow_le_pow_right₀ (by norm_num) hj
  have h3 : P ^ (2 - 2 * σ₀) ≤ ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) :=
    Real.rpow_le_rpow hP0.le hPJ (by linarith)
  have hlog : Real.log P ≤ J := by
    rw [hP]; push_cast
    rw [Real.log_pow]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    calc (j : ℝ) * Real.log 2 ≤ j * 1 := by gcongr
      _ = j := mul_one _
      _ ≤ J := by exact_mod_cast hj
  have hlog0 : 0 ≤ Real.log P := Real.log_nonneg hP1
  have hba : 0 ≤ b - a := by linarith
  have hpos1 : 0 ≤ P ^ (1 - 2 * σ) := by positivity
  calc (b - a + 8 * P * (1 + Real.log P)) * P ^ (1 - 2 * σ)
      = (b - a) * P ^ (1 - 2 * σ) + 8 * (1 + Real.log P) * (P * P ^ (1 - 2 * σ)) := by ring
    _ = (b - a) * P ^ (1 - 2 * σ) + 8 * (1 + Real.log P) * P ^ (2 - 2 * σ) := by rw [hsq2]
    _ ≤ (b - a) * 1 + 8 * (1 + J) * ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) := by
        have e1 : (b - a) * P ^ (1 - 2 * σ) ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left h1 hba
        have e2 : 8 * (1 + Real.log P) * P ^ (2 - 2 * σ) ≤ 8 * (1 + J) * ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) :=
          mul_le_mul (by linarith) (h2.trans h3) (by positivity) (by positivity)
        linarith
    _ = (b - a) + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) := by ring

/-- **The mean square of `Σ_{n≤2^J} n^{−σ−it}`** for `σ ≥ σ₀ ∈ [½, 1]`, from the dyadic mean value theorem
(`DirMean.mean_value`) and Cauchy–Schwarz over the `J + 1` blocks. -/
theorem mean_square_partial_gen {σ₀ σ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ ≤ 1) (hσ : σ₀ ≤ σ) (J : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖∑ n ∈ Ioc (0 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2
      ≤ (J + 1) ^ 2 * (b - a + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀)) := by
  set c : ℕ → ℂ := fun n => (((n : ℝ) ^ (-σ) : ℝ) : ℂ) with hc
  set Bk : ℕ → ℝ → ℂ := fun j t => dp (Finset.Ioc (2 ^ j) (2 ^ (j + 1))) c t with hBk
  set Q : ℝ := ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) with hQ
  have hD : ∀ t : ℝ, ∑ n ∈ Ioc (0 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + t * I))
      = 1 + ∑ j ∈ range J, Bk j t := by
    intro t
    rw [sum_Ioc_two_pow]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hBk, dp]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := by
        have h1 := (Finset.mem_Ioc.1 hn).1
        have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      rw [natCast_cpow_eq hn1]
  have hcs : ∀ t : ℝ, ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2
      ≤ (J + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2) := by
    intro t
    have hle : ‖1 + ∑ j ∈ range J, Bk j t‖ ≤ 1 + ∑ j ∈ range J, ‖Bk j t‖ :=
      (norm_add_le _ _).trans (by rw [norm_one]; gcongr; exact norm_sum_le _ _)
    have hcs0 := sq_sum_le_card_mul_sum_sq (s := range (J + 1))
      (f := fun i => if i = 0 then (1 : ℝ) else ‖Bk (i - 1) t‖)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hcs0
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, card_range, one_pow] at hcs0
    push_cast at hcs0
    calc ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2 ≤ (1 + ∑ j ∈ range J, ‖Bk j t‖) ^ 2 := by
          gcongr
      _ ≤ (J + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2) := by
          rw [add_comm (1 : ℝ) (∑ j ∈ range J, ‖Bk j t‖),
            add_comm (1 : ℝ) (∑ j ∈ range J, ‖Bk j t‖ ^ 2)]
          exact hcs0
  have hcontB : ∀ j, Continuous (Bk j) := fun j => continuous_dp _ _
  have hfun : (fun t : ℝ => ‖∑ n ∈ Ioc (0 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + t * I))‖ ^ 2)
      = fun t => ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2 := funext fun t => by rw [hD]
  rw [hfun]
  have hint1 : IntervalIntegrable (fun t => ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2) volume a b :=
    (by fun_prop : Continuous fun t => ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2).intervalIntegrable _ _
  have hintB : ∀ j ∈ range J, IntervalIntegrable (fun t => ‖Bk j t‖ ^ 2) volume a b :=
    fun j _ => ((hcontB j).norm.pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun t => ((J : ℝ) + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2)) volume a b :=
    (continuous_const.mul (continuous_const.add (continuous_finsetSum _
      fun j _ => (hcontB j).norm.pow 2))).intervalIntegrable _ _
  calc ∫ t in a..b, ‖1 + ∑ j ∈ range J, Bk j t‖ ^ 2
      ≤ ∫ t in a..b, ((J : ℝ) + 1) * (1 + ∑ j ∈ range J, ‖Bk j t‖ ^ 2) :=
        intervalIntegral.integral_mono_on hab hint1 hint2 fun t _ => hcs t
    _ = ((J : ℝ) + 1) * ((b - a) + ∑ j ∈ range J, ∫ t in a..b, ‖Bk j t‖ ^ 2) := by
        have hsum_int : IntervalIntegrable (fun t => ∑ j ∈ range J, ‖Bk j t‖ ^ 2) volume a b :=
          (continuous_finsetSum _ fun j _ => (hcontB j).norm.pow 2).intervalIntegrable _ _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          intervalIntegrable_const hsum_int,
          intervalIntegral.integral_finsetSum hintB, intervalIntegral.integral_const, smul_eq_mul,
          mul_one]
    _ ≤ ((J : ℝ) + 1) * ((b - a) + ∑ j ∈ range J, ((b - a) + 8 * (J + 1) * Q)) := by
        gcongr with j hj
        have hjJ : j ≤ J := (Finset.mem_range.1 hj).le
        have hP : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        have hS : Finset.Ioc (2 ^ j) (2 ^ (j + 1)) ⊆ Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
          rw [pow_succ, mul_comm]
        have hmv := mean_value hP hS c hab
        refine hmv.trans ?_
        refine le_trans ?_ (block_bound_gen hσ₀ hσ₀1 hσ hjJ hab)
        have hsum : ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ‖c n‖ ^ 2
            ≤ ((2 ^ j : ℕ) : ℝ) * ((((2 ^ j : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by
          have hcard : (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).card = 2 ^ j := by
            rw [Nat.card_Ioc, pow_succ]; omega
          calc ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ‖c n‖ ^ 2
              ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ((((2 ^ j : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by
                refine Finset.sum_le_sum fun n hn => ?_
                have hn' := (Finset.mem_Ioc.1 hn).1
                have hPr : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
                have hnr : ((2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.le
                have hle : (n : ℝ) ^ (-σ) ≤ ((2 ^ j : ℕ) : ℝ) ^ (-σ) :=
                  Real.rpow_le_rpow_of_nonpos hPr hnr (by linarith)
                have hn0 : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
                have hnorm : ‖c n‖ = (n : ℝ) ^ (-σ) := by
                  simp only [hc, Complex.norm_real, Real.norm_eq_abs]
                  exact abs_of_nonneg hn0
                rw [hnorm]
                exact pow_le_pow_left₀ hn0 hle 2
            _ = ((2 ^ j : ℕ) : ℝ) * ((((2 ^ j : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by
                rw [Finset.sum_const, hcard, nsmul_eq_mul]
        have hL0 : 0 ≤ b - a + 8 * (2 ^ j : ℕ) * (1 + Real.log (2 ^ j : ℕ)) := by
          have : 0 ≤ Real.log ((2 ^ j : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hP)
          have : 0 ≤ b - a := by linarith
          positivity
        push_cast at hsum hL0 ⊢
        exact mul_le_mul_of_nonneg_left hsum hL0
    _ = ((J : ℝ) + 1) * ((b - a) + J * ((b - a) + 8 * (J + 1) * Q)) := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
    _ ≤ (J + 1) ^ 2 * (b - a + 8 * (J + 1) * Q) := by
        have hQ0 : 0 ≤ Q := by positivity
        have hba : 0 ≤ b - a := by linarith
        have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
        nlinarith [mul_nonneg hJ hQ0, mul_nonneg (mul_nonneg hJ hJ) hQ0]

/-- **The mean square of `ζ` on `Re s ≥ σ₀` from the order-`2K` approximation**: for `K ≥ 1`, `σ₀ ∈ [½, 1]`,
`σ ∈ [σ₀, 4]`, `[a, b]` with `2 ≤ |t| ≤ M` on it and `M^{2K} ≤ (2^J)^{σ₀+2K−1}`,
`∫_a^b |ζ(σ+it)|² ≤ 2(J+1)²(b − a + 8(J+1)Q) + 4Q + 4·CE(K)²(b − a)`, where `Q = (2^J)^{2−2σ₀}`. -/
theorem mean_square_zeta_le_order {K J : ℕ} (hK : 1 ≤ K) {σ₀ σ M a b : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hσ₀1 : σ₀ ≤ 1) (hσ : σ₀ ≤ σ) (hσ4 : σ ≤ 4) (hM : 2 ≤ M)
    (hN : M ^ (2 * K) ≤ ((2 : ℝ) ^ J) ^ (σ₀ + 2 * K - 1)) (hab : a ≤ b) (hside : 2 ≤ a ∨ b ≤ -2)
    (hbd : ∀ t ∈ Icc a b, |t| ≤ M) :
    ∫ t in a..b, ‖riemannZeta (σ + t * I)‖ ^ 2
      ≤ 2 * ((J + 1) ^ 2 * (b - a + 8 * (J + 1) * ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀)))
        + 4 * ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) + 4 * CE K ^ 2 * (b - a) := by
  set Q : ℝ := ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) with hQ
  have hNr : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by push_cast; ring
  have hNr1 : (1 : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hσ0 : 0 < σ := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hMN : M ≤ ((2 ^ J : ℕ) : ℝ) := by
    have h1 : ((2 ^ J : ℕ) : ℝ) ^ (σ₀ + 2 * K - 1) ≤ ((2 ^ J : ℕ) : ℝ) ^ ((2 * K : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hNr1; push_cast; linarith
    rw [Real.rpow_natCast] at h1
    rw [← hNr] at hN
    have h2 : M ^ (2 * K) ≤ ((2 ^ J : ℕ) : ℝ) ^ (2 * K) := hN.trans h1
    exact le_of_pow_le_pow_left₀ (by omega) (by positivity) h2
  have habs : ∀ t ∈ Icc a b, 2 ≤ |t| := by
    intro t ht
    rcases hside with h | h
    · rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    · rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]
  have hpt : ∀ t ∈ Icc a b,
      ‖riemannZeta (σ + t * I) - ∑ n ∈ Finset.Ioc (0 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + t * I))‖
        ≤ (((2 ^ J : ℕ) : ℝ) + 1) ^ (1 - σ) / |t| + CE K := by
    intro t ht
    have h2 := habs t ht
    have hM' := hbd t ht
    refine norm_zeta_sub_partial_le hK Nat.one_le_two_pow hσ0 hσ4 h2 (by linarith) ?_
    have e1 : |t| ^ (2 * K) ≤ M ^ (2 * K) := pow_le_pow_left₀ (abs_nonneg t) hM' _
    have e2 : M ^ (2 * K) ≤ ((2 ^ J : ℕ) : ℝ) ^ (σ₀ + 2 * K - 1) := by rw [hNr]; exact hN
    have e3 : ((2 ^ J : ℕ) : ℝ) ^ (σ₀ + 2 * K - 1) ≤ (((2 ^ J : ℕ) : ℝ) + 1) ^ (σ₀ + 2 * K - 1) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have e4 : (((2 ^ J : ℕ) : ℝ) + 1) ^ (σ₀ + 2 * K - 1) ≤ (((2 ^ J : ℕ) : ℝ) + 1) ^ (σ + 2 * K - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    linarith
  have hms := mean_square_of_pointwise hab hside hpt (mean_square_partial_gen hσ₀ hσ₀1 hσ J hab)
  have hX : ((((2 ^ J : ℕ) : ℝ) + 1) ^ (1 - σ)) ^ 2 ≤ 2 * Q := by
    have e1 : ((((2 ^ J : ℕ) : ℝ) + 1) ^ (1 - σ)) ^ 2 = (((2 ^ J : ℕ) : ℝ) + 1) ^ (2 - 2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; push_cast; ring_nf
    have e2 : (((2 ^ J : ℕ) : ℝ) + 1) ^ (2 - 2 * σ) ≤ (((2 ^ J : ℕ) : ℝ) + 1) ^ (2 - 2 * σ₀) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e3 : (((2 ^ J : ℕ) : ℝ) + 1) ^ (2 - 2 * σ₀) ≤ (2 * ((2 ^ J : ℕ) : ℝ)) ^ (2 - 2 * σ₀) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have e4 : (2 * ((2 ^ J : ℕ) : ℝ)) ^ (2 - 2 * σ₀) = (2 : ℝ) ^ (2 - 2 * σ₀) * Q := by
      rw [Real.mul_rpow (by norm_num) (by positivity), hQ, hNr]
    have e5 : (2 : ℝ) ^ (2 - 2 * σ₀) ≤ 2 := by
      calc (2 : ℝ) ^ (2 - 2 * σ₀) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hQ0 : 0 ≤ Q := by positivity
    have e6 : (2 : ℝ) ^ (2 - 2 * σ₀) * Q ≤ 2 * Q := mul_le_mul_of_nonneg_right e5 hQ0
    rw [e1]
    linarith
  linarith

/-- **A mean-square bound of polylogarithmic size** for `ζ` on `σ₀ ≤ Re s ≤ 4`: some `A ≥ 0` has
`∫_a^b |ζ(σ+it)|² ≤ A (log M)³ (b − a + M)` for every `σ ∈ [σ₀, 4]` and `[a, b]` with `2 ≤ |t| ≤ M` on it. -/
def MSPoly (σ₀ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ σ M a b : ℝ, σ₀ ≤ σ → σ ≤ 4 → 2 ≤ M → a ≤ b → (2 ≤ a ∨ b ≤ -2) →
    (∀ t ∈ Icc a b, |t| ≤ M) →
      ∫ t in a..b, ‖riemannZeta (σ + t * I)‖ ^ 2 ≤ A * Real.log M ^ 3 * (b - a + M)

/-- The arithmetic of `msPoly_of_order`: with `x ≤ cℓ`, `Q ≤ 2M` and `ℓ ≥ ½`,
`2x²(D + 8xQ) + 4Q + 4E²D ≤ (4c² + 32E² + 32c³ + 64)ℓ³(D + M)`. -/
lemma arith_poly {x Q D M ℓ c E : ℝ} (hx0 : 0 ≤ x) (hxc : x ≤ c * ℓ) (hc0 : 0 ≤ c) (hQ0 : 0 ≤ Q)
    (hQM : Q ≤ 2 * M) (hD0 : 0 ≤ D) (hM0 : 0 ≤ M) (hℓh : 1 / 2 ≤ ℓ) :
    2 * (x ^ 2 * (D + 8 * x * Q)) + 4 * Q + 4 * E ^ 2 * D
      ≤ (4 * c ^ 2 + 32 * E ^ 2 + 32 * c ^ 3 + 64) * ℓ ^ 3 * (D + M) := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓ3 : 1 ≤ 8 * ℓ ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hℓh 3
    norm_num at this; linarith
  have hℓ23 : ℓ ^ 2 ≤ 2 * ℓ ^ 3 := by
    have h := mul_nonneg (sq_nonneg ℓ) (show (0 : ℝ) ≤ 2 * ℓ - 1 by linarith)
    nlinarith [h]
  have hx2 : x ^ 2 ≤ c ^ 2 * ℓ ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hx0 hxc 2
  have hx3 : x ^ 3 ≤ c ^ 3 * ℓ ^ 3 := by rw [← mul_pow]; exact pow_le_pow_left₀ hx0 hxc 3
  have t1 : x ^ 2 * D ≤ 2 * c ^ 2 * ℓ ^ 3 * D := by
    have h1 : c ^ 2 * ℓ ^ 2 ≤ 2 * c ^ 2 * ℓ ^ 3 := by
      have := mul_le_mul_of_nonneg_left hℓ23 (sq_nonneg c); linarith
    exact mul_le_mul_of_nonneg_right (hx2.trans h1) hD0
  have t2 : x ^ 3 * Q ≤ c ^ 3 * ℓ ^ 3 * (2 * M) := mul_le_mul hx3 hQM hQ0 (by positivity)
  have t3 : M ≤ 8 * ℓ ^ 3 * M := by nlinarith [mul_le_mul_of_nonneg_right hℓ3 hM0]
  have t4 : E ^ 2 * D ≤ 8 * E ^ 2 * ℓ ^ 3 * D := by
    have := mul_le_mul_of_nonneg_left hℓ3 (mul_nonneg (sq_nonneg E) hD0); nlinarith [this]
  have u1 : 0 ≤ c ^ 2 * ℓ ^ 3 * M := by positivity
  have u2 : 0 ≤ E ^ 2 * ℓ ^ 3 * M := by positivity
  have u3 : 0 ≤ c ^ 3 * ℓ ^ 3 * D := by positivity
  have u4 : 0 ≤ ℓ ^ 3 * D := by positivity
  nlinarith [t1, t2, t3, t4, u1, u2, u3, u4]

/-- **`MSPoly σ₀` for every `σ₀ ≥ (2K+1)/(4K+1)`**, `K ≥ 1`: with `2^J` the least power of two with
`(2^J)^{σ₀+2K−1} ≥ M^{2K}`, `Q = (2^J)^{2−2σ₀} ≤ 2M` exactly when `σ₀ ≥ (2K+1)/(4K+1)`, and `J + 1 ≪ log M`. -/
theorem msPoly_of_order {K : ℕ} (hK : 1 ≤ K) {σ₀ : ℝ} (hσ₀ : (2 * K + 1) / (4 * K + 1) ≤ σ₀)
    (hσ₀1 : σ₀ ≤ 1) : MSPoly σ₀ := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h41 : (0 : ℝ) < 4 * K + 1 := by positivity
  have hσ₀mul : 2 * K + 1 ≤ σ₀ * (4 * K + 1) := by rwa [div_le_iff₀ h41] at hσ₀
  have hσ₀h : 1 / 2 ≤ σ₀ := by nlinarith
  set e : ℝ := σ₀ + 2 * K - 1 with he
  have he0 : 0 < e := by rw [he]; linarith
  set θ : ℝ := 2 * K / e with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθe : θ * e = 2 * K := by rw [hθ]; field_simp
  have hθ1 : θ * (2 - 2 * σ₀) ≤ 1 := by
    rw [hθ, div_mul_eq_mul_div, div_le_one he0, he]; nlinarith
  set c : ℝ := 2 * (θ + 2) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨4 * c ^ 2 + 32 * CE K ^ 2 + 32 * c ^ 3 + 64, by positivity, ?_⟩
  intro σ M a b hσ hσ4 hM hab hside hbd
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hlb0 : 0 ≤ Real.logb 2 M := Real.logb_nonneg (by norm_num) hM1
  set J : ℕ := ⌈θ * Real.logb 2 M⌉₊ with hJ
  have hJlo : θ * Real.logb 2 M ≤ J := Nat.le_ceil _
  have hJhi : (J : ℝ) < θ * Real.logb 2 M + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2J : (2 : ℝ) ^ J = (2 : ℝ) ^ (J : ℝ) := (Real.rpow_natCast 2 J).symm
  have hMθ : (2 : ℝ) ^ (θ * Real.logb 2 M) = M ^ θ := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hM0]
  have hlo : M ^ θ ≤ (2 : ℝ) ^ J := by
    rw [h2J, ← hMθ]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hJlo
  have hhi : (2 : ℝ) ^ J ≤ 2 * M ^ θ := by
    rw [h2J, ← hMθ]
    calc (2 : ℝ) ^ (J : ℝ) ≤ (2 : ℝ) ^ (θ * Real.logb 2 M + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hJhi.le
      _ = 2 * (2 : ℝ) ^ (θ * Real.logb 2 M) := by rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have hN : M ^ (2 * K) ≤ ((2 : ℝ) ^ J) ^ (σ₀ + 2 * K - 1) := by
    have e1 : M ^ (2 * K) = (M ^ θ) ^ e := by
      rw [← Real.rpow_mul hM0.le, hθe, ← Real.rpow_natCast]; push_cast; ring_nf
    rw [e1, ← he]
    exact Real.rpow_le_rpow (by positivity) hlo he0.le
  have hms := mean_square_zeta_le_order hK hσ₀h hσ₀1 hσ hσ4 hM hN hab hside hbd
  set Q : ℝ := ((2 : ℝ) ^ J) ^ (2 - 2 * σ₀) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQM : Q ≤ 2 * M := by
    have e1 : Q ≤ (2 * M ^ θ) ^ (2 - 2 * σ₀) := Real.rpow_le_rpow (by positivity) hhi (by linarith)
    have e2 : (2 * M ^ θ) ^ (2 - 2 * σ₀) = (2 : ℝ) ^ (2 - 2 * σ₀) * M ^ (θ * (2 - 2 * σ₀)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hM0.le]
    have e3 : (2 : ℝ) ^ (2 - 2 * σ₀) ≤ 2 := by
      calc (2 : ℝ) ^ (2 - 2 * σ₀) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have e4 : M ^ (θ * (2 - 2 * σ₀)) ≤ M := by
      calc M ^ (θ * (2 - 2 * σ₀)) ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hθ1
        _ = M := Real.rpow_one M
    have e5 : 0 ≤ M ^ (θ * (2 - 2 * σ₀)) := by positivity
    have e6 : (2 : ℝ) ^ (2 - 2 * σ₀) * M ^ (θ * (2 - 2 * σ₀)) ≤ 2 * M :=
      mul_le_mul e3 e4 e5 (by norm_num)
    linarith
  have hℓ2 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hℓh : 1 / 2 ≤ Real.log M := by linarith
  have hlb : Real.logb 2 M ≤ 2 * Real.log M := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.log M := by linarith
    nlinarith
  have hlb1 : 1 ≤ Real.logb 2 M := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hM0, Real.rpow_one]; exact hM
  have hxc : (J : ℝ) + 1 ≤ c * Real.log M := by
    have e1 : (J : ℝ) + 1 ≤ θ * Real.logb 2 M + 2 := by linarith
    have e2 : θ * Real.logb 2 M + 2 ≤ (θ + 2) * Real.logb 2 M := by nlinarith
    have e3 : (θ + 2) * Real.logb 2 M ≤ (θ + 2) * (2 * Real.log M) :=
      mul_le_mul_of_nonneg_left hlb (by positivity)
    rw [hc]; linarith
  exact hms.trans (arith_poly (by positivity) hxc hc0 hQ0 hQM (by linarith) hM0.le hℓh)

end MeanSquareHigh

#print axioms MeanSquareHigh.CE_nonneg
#print axioms MeanSquareHigh.norm_add_nat_le
#print axioms MeanSquareHigh.norm_prod_add_le
#print axioms MeanSquareHigh.sum_range_succ_cpow
#print axioms MeanSquareHigh.norm_zeta_sub_partial_le
#print axioms MeanSquareHigh.mean_square_of_pointwise
#print axioms MeanSquareHigh.block_bound_gen
#print axioms MeanSquareHigh.mean_square_partial_gen
#print axioms MeanSquareHigh.mean_square_zeta_le_order
#print axioms MeanSquareHigh.arith_poly
#print axioms MeanSquareHigh.msPoly_of_order
