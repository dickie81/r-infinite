/-
# Round 698: the reflection of Heath-Brown's double sums (the CGL plan's stage M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 694's `σ(N)` is the double sum `Σ_{r,s}|Σ_{N<n≤2N}n^{−1/2}A_r(n)Ā_s(n)|²` with `A_r(n) = χ_r(n)n^{it_r}`, and
`Ŝ(Y)` the one over `1 ≤ n ≤ Y`. This file bounds `σ(N)` through the reflection of every Gram entry: round 642's
`norm_gram_le` for `χ_r ≠ χ_s` and round 697's `norm_gram_le0` for `χ_r = χ_s`. The dual sums of the pairs, gathered,
are again a double sum of the same family, of length `Z`. This is the step of Kerr's Corollary 28 for `q = 1`
(arXiv:1909.12075), which bounds his double sum at length `N` by the one at length `4∆/N` and two further terms.

The stack's form.
* Sharp to smooth: round 638's weight `w` is `1` on `[6/5, 9/5]`, so `w(n/N₁)² + w(n/N₂)² ≥ 1` on `(N, 2N]` for
  `N₁ = 5N/6` and `N₂ = 5N/4`. Positivity (round 694's `dsum_le`) with `n^{−1/2} ≤ N^{−1/2}` then bounds `σ(N)` by
  `(2/N)` times the sums of `|G(r, s)|²` over the two Gram matrices of round 638.
* Each Gram entry is bounded through its reflection, with the residue term for `χ_r = χ_s`.
* The dual sum of the pair `(r, s)` is `D_{rs}(u) = Σ_{m≤Z}m^{−1/2+iu}Ā_r(m)A_s(m)`, so `Σ_{r,s}|D_{rs}(u)|²` is the
  double sum of the conjugate family with the weights `m^{−1/2+iu}`, at most `Ŝ(Z)` (round 694's `dsum_conj` and
  positivity).
* Cauchy–Schwarz in the form `(∫hd)² ≤ (∫h)(∫hd²)`, from `2λhd ≤ λ²h + hd²` for every `λ > 0`.
* The residues: `|H(1 + iτ)| ≤ B(1 + |τ|)^{−3}` (round 641's `H_shift_bound`); and when the points with the same
  character are `1`-separated, `s ↦ ⌊t_r − t_s⌋` is injective on them, so their terms `(1 + |t_r − t_s|)^{−2}` sum to at
  most `C₀ = Σ_{m∈ℤ}|m + 1/2|^{−2}`.

Plain statements, with `R = |P|`, and `q ≥ 1` where `[NeZero q]`.
* `gramP_eq`, `wCGL_eq_zero_of_not_mem`, `gramP_eq_of_subset`: `G(r, s) = Σ_n w(n/N)²A_r(n)Ā_s(n)` over the columns;
  for `N > 0` the weight vanishes off them, so the sum may run over any larger set.
* `one_le_wsum`, `dyad_subset_cols`, `sig_le_gram`: for `N > 0`, `w(n/N₁)² + w(n/N₂)² ≥ 1` on `(N, 2N]`, which lies in
  the two sets of columns, and `σ(N) ≤ (2/N)(Σ_{r,s}|G_{N₁}(r, s)|² + Σ_{r,s}|G_{N₂}(r, s)|²)`.
* `TK`, `Drs`, `norm_gram_le_all`: for `N > 0` and `Z, K ≥ 1`, with `τ = t_r − t_s`,
  `|G(r, s)| ≤ [χ_r = χ_s]N|H(1 + iτ)| + (2π)⁻¹(N^{1/2}Q₀(q)∫|H(1/2 + iu)||D_{rs}(u)| du + T_K(N, τ))`, with `T_K` the
  bound of round 642's `norm_integral_Tl_le`. `Res` is the residue term `[χ_r = χ_s]|H(1 + iτ)|²` and `Imain` the
  integral `∫|H(1/2 + iu)||D_{rs}(u)| du`.
* `conj_natCast_cpow_I`, `Drs_eq`, `sum_norm_Drs_sq_le`: for `m ≥ 1`, `conj(m^{ix}) = m^{−ix}`; the form of `D_{rs}`
  above; and for real `u`, `Σ_{r,s}|D_{rs}(u)|² ≤ Ŝ(Z)`.
* `sq_le_of_forall`, `integral_mul_sq_le`: for `I, A, B ≥ 0` with `2λI ≤ λ²A + B` for every `λ > 0`, `I² ≤ AB`; and
  for `h, d ≥ 0` with `h`, `hd` and `hd²` integrable, `(∫hd)² ≤ (∫h)(∫hd²)`.
* `AH`, `AH_nonneg`, `integrable_H_half`, `integrable_H_Drs`, `sum_main_sq_le`: with `A_H = ∫|H(1/2 + iu)| du`,
  `Σ_{r,s}(∫|H(1/2 + iu)||D_{rs}(u)| du)² ≤ A_H²Ŝ(Z)`.
* `C0`, `summable_C0`, `C0_nonneg`, `inv_sq_le_floor`, `sum_sep_le`, `H_one_bound`, `sum_res_le`: for each `r`,
  `Σ_{s: χ_s = χ_r}(1 + |t_r − t_s|)^{−2} ≤ C₀` when the points with the same character are `1`-separated; there is
  `B ≥ 0` with `|H(1 + iτ)|² ≤ B²(1 + |τ|)^{−2}`; and for such `B`, `Σ_{r,s: χ_r = χ_s}|H(1 + i(t_r − t_s))|² ≤ B²C₀R`.
* `TT`, `TK_nonneg`, `TK_le`: with `T_K(N, Z, T) = 2^{ω(q)+1}πC_KEQh(q)q^{K+1/2}(NZ)^{−K}(1 + 2T)^{K+1}I_K` (`TT`),
  for `N > 0`, `5N/6 ≤ N'`, `Z ≥ 1` and `|τ| ≤ 2T`, `0 ≤ T_K(N', τ) ≤ 2^KT_K(N, Z, T)`.
* `add_sq_le_three`, `pair_sq_le`, `sum_sum_three`: `(a + b + d)² ≤ 3a² + 3b² + 3d²`; for `N > 0`, `Z, K ≥ 1` and
  `T_K(N, t_r − t_s) ≤ X`, `|G(r, s)|² ≤ 3N²Res + 3(2π)⁻²NQ₀(q)²Imain² + 3(2π)⁻²X²`; and the sum over the pairs of
  `f + g + k` is `Σf + Σg + kR²`.
* `sum_gram_sq_le`: for `N > 0`, `5N/6 ≤ N' ≤ 5N/4`, `Z, K ≥ 1`, `|t_r| ≤ T`, the separation and `B` as above,
  `Σ_{r,s}|G_{N'}(r, s)|² ≤ 5N²B²C₀R + (N/9)Q₀(q)²A_H²Ŝ(Z) + (4^K/12)T_K(N, Z, T)²R²`.
* `refl_arith`, `sig_le_refl`: the arithmetic of the last step; and for `K ≥ 1` there is `C ≥ 0` such that, for
  `q ≥ 1`, `N > 0`, `Z ≥ 1`, `|t_r| ≤ T` and the separation, `σ(N) ≤ C(NR + Q₀(q)²Ŝ(Z) + T_K(N, Z, T)²R²/N)`.

The file imports `LinnikCGLRefl0.lean` and `LinnikCGLHBPos.lean`.
-/

import LinnikCGLRefl0
import LinnikCGLHBPos

open Complex Set Real Filter Topology MeasureTheory
open scoped ComplexConjugate Classical

noncomputable section

namespace LinnikCGLHBRefl

open LinnikCGLMat LinnikCGLMellin LinnikCGLReflect LinnikCGLPair LinnikCGLRefl0 LinnikCGLHBPos LinnikCGLT101
  DirichletCharacter LinnikReflect

variable {ι : Type*}

/-! ### The Gram entries in the notation of the double sums -/

/-- `G(r, s) = Σ_n w(n/N)²A_r(n)Ā_s(n)` over the columns, with `A_r(n) = χ_r(n)n^{it_r}`. -/
lemma gramP_eq {q : ℕ} (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r s : ι) :
    gramP N χ t r s =
      ∑ n ∈ colsP N, ((wCGL (n / N) ^ 2 : ℝ) : ℂ) * famA χ t r n * conj (famA χ t s n) := by
  unfold gramP entP famA
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.star_def]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- For `N > 0` the weight vanishes off the columns: `n ∉ colsP N` gives `w(n/N) = 0`. -/
lemma wCGL_eq_zero_of_not_mem {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n ∉ colsP N) : wCGL (n / N) = 0 := by
  unfold colsP at hn
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  apply wCGL_zero
  rcases hn with h | h
  · left
    have h1 : (n : ℝ) < N := Nat.lt_ceil.1 h
    rw [div_le_one hN]
    exact h1.le
  · right
    have h1 : 2 * N < n := (Nat.floor_lt (by positivity)).1 h
    rw [le_div_iff₀ hN]
    exact h1.le

/-- For `N > 0` and `colsP N ⊆ S`, the Gram entry is the same sum over `S`. -/
lemma gramP_eq_of_subset {q : ℕ} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r s : ι)
    {S : Finset ℕ} (hS : colsP N ⊆ S) :
    gramP N χ t r s = ∑ n ∈ S, ((wCGL (n / N) ^ 2 : ℝ) : ℂ) * famA χ t r n * conj (famA χ t s n) := by
  rw [gramP_eq]
  refine Finset.sum_subset hS fun n _ hn => ?_
  rw [wCGL_eq_zero_of_not_mem hN hn]
  simp

/-! ### From the sharp sum to two smooth ones -/

/-- For `N > 0` the two plateaus cover `(N, 2N]`: there `w(n/(5N/6))² + w(n/(5N/4))² ≥ 1`. -/
lemma one_le_wsum {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n ∈ dyad N) :
    1 ≤ wCGL (n / (5 * N / 6)) ^ 2 + wCGL (n / (5 * N / 4)) ^ 2 := by
  obtain ⟨h1, h2⟩ := (mem_dyad hN.le).1 hn
  rcases le_or_gt (n : ℝ) (3 * N / 2) with h | h
  · have hw : wCGL (n / (5 * N / 6)) = 1 := by
      apply wCGL_one
      · rw [le_div_iff₀ (by positivity)]; linarith
      · rw [div_le_iff₀ (by positivity)]; linarith
    rw [hw]
    nlinarith [sq_nonneg (wCGL (n / (5 * N / 4)))]
  · have hw : wCGL (n / (5 * N / 4)) = 1 := by
      apply wCGL_one
      · rw [le_div_iff₀ (by positivity)]; linarith
      · rw [div_le_iff₀ (by positivity)]; linarith
    rw [hw]
    nlinarith [sq_nonneg (wCGL (n / (5 * N / 6)))]

/-- For `N > 0`, `(N, 2N]` lies in the columns of `5N/6` and of `5N/4`. -/
lemma dyad_subset_cols {N : ℝ} (hN : 0 < N) : dyad N ⊆ colsP (5 * N / 6) ∪ colsP (5 * N / 4) := by
  intro n hn
  obtain ⟨h1, h2⟩ := (mem_dyad hN.le).1 hn
  rw [Finset.mem_union]
  unfold colsP
  rcases le_or_gt (n : ℝ) (3 * N / 2) with h | h
  · left
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.2 (by linarith), Nat.le_floor (by linarith)⟩
  · right
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.2 (by linarith), Nat.le_floor (by linarith)⟩

/-- **Sharp to smooth**: for `N > 0`,
`σ(N) ≤ (2/N)(Σ_{r,s}|G_{5N/6}(r, s)|² + Σ_{r,s}|G_{5N/4}(r, s)|²)`. -/
theorem sig_le_gram {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {N : ℝ} (hN : 0 < N) :
    sig P χ t N ≤ 2 / N * (∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 6) χ t r s‖ ^ 2 +
      ∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 4) χ t r s‖ ^ 2) := by
  have hN₁0 : 0 < 5 * N / 6 := by positivity
  have hN₂0 : 0 < 5 * N / 4 := by positivity
  set S : Finset ℕ := colsP (5 * N / 6) ∪ colsP (5 * N / 4) with hS
  set w : ℕ → ℝ := fun n => wCGL (n / (5 * N / 6)) ^ 2 + wCGL (n / (5 * N / 4)) ^ 2 with hw
  have h1 : sig P χ t N ≤ dsum P (famA χ t) S (fun n => ((N ^ (-(1 / 2 : ℝ)) * w n : ℝ) : ℂ)) := by
    refine dsum_le P (famA χ t) (dyad_subset_cols hN) (fun n hn => ?_)
      (fun n _ => mul_nonneg (by positivity) (by simp only [hw]; positivity))
    rw [norm_wh]
    obtain ⟨hn1, _⟩ := (mem_dyad hN.le).1 hn
    have hnN : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ N ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN hn1.le (by norm_num)
    have hw1 : 1 ≤ w n := one_le_wsum hN hn
    have hN0 : 0 ≤ N ^ (-(1 / 2 : ℝ)) := by positivity
    calc (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ N ^ (-(1 / 2 : ℝ)) * 1 := by rw [mul_one]; exact hnN
      _ ≤ N ^ (-(1 / 2 : ℝ)) * w n := mul_le_mul_of_nonneg_left hw1 hN0
  have hc : (N ^ (-(1 / 2 : ℝ))) ^ 2 = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num [Real.rpow_neg_one]
  have h2 : dsum P (famA χ t) S (fun n => ((N ^ (-(1 / 2 : ℝ)) * w n : ℝ) : ℂ)) =
      N⁻¹ * dsum P (famA χ t) S (fun n => ((w n : ℝ) : ℂ)) := by
    have e : (fun n => ((N ^ (-(1 / 2 : ℝ)) * w n : ℝ) : ℂ)) =
        fun n => ((N ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((w n : ℝ) : ℂ) := by
      funext n
      exact Complex.ofReal_mul _ _
    rw [e, dsum_const_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hc]
  have h3 : dsum P (famA χ t) S (fun n => ((w n : ℝ) : ℂ)) ≤
      ∑ r ∈ P, ∑ s ∈ P, (2 * ‖gramP (5 * N / 6) χ t r s‖ ^ 2 + 2 * ‖gramP (5 * N / 4) χ t r s‖ ^ 2) := by
    unfold dsum
    refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => ?_
    have e : ∑ n ∈ S, ((w n : ℝ) : ℂ) * famA χ t r n * conj (famA χ t s n) =
        gramP (5 * N / 6) χ t r s + gramP (5 * N / 4) χ t r s := by
      rw [gramP_eq_of_subset hN₁0 χ t r s (show colsP (5 * N / 6) ⊆ S from Finset.subset_union_left),
        gramP_eq_of_subset hN₂0 χ t r s (show colsP (5 * N / 4) ⊆ S from Finset.subset_union_right),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hw]
      push_cast
      ring
    have h4 := norm_add_le (gramP (5 * N / 6) χ t r s) (gramP (5 * N / 4) χ t r s)
    have h5 : ‖gramP (5 * N / 6) χ t r s + gramP (5 * N / 4) χ t r s‖ ^ 2 ≤
        (‖gramP (5 * N / 6) χ t r s‖ + ‖gramP (5 * N / 4) χ t r s‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h4 2
    calc ‖∑ n ∈ S, ((w n : ℝ) : ℂ) * famA χ t r n * conj (famA χ t s n)‖ ^ 2
        = ‖gramP (5 * N / 6) χ t r s + gramP (5 * N / 4) χ t r s‖ ^ 2 := by rw [e]
      _ ≤ 2 * ‖gramP (5 * N / 6) χ t r s‖ ^ 2 + 2 * ‖gramP (5 * N / 4) χ t r s‖ ^ 2 := by
          nlinarith [sq_nonneg (‖gramP (5 * N / 6) χ t r s‖ - ‖gramP (5 * N / 4) χ t r s‖)]
  have h3' : ∑ r ∈ P, ∑ s ∈ P, (2 * ‖gramP (5 * N / 6) χ t r s‖ ^ 2 + 2 * ‖gramP (5 * N / 4) χ t r s‖ ^ 2) =
      2 * (∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 6) χ t r s‖ ^ 2) +
        2 * ∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 4) χ t r s‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  calc sig P χ t N ≤ N⁻¹ * dsum P (famA χ t) S (fun n => ((w n : ℝ) : ℂ)) := h1.trans h2.le
    _ ≤ N⁻¹ * (2 * (∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 6) χ t r s‖ ^ 2) +
          2 * ∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 4) χ t r s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h3.trans h3'.le) (inv_nonneg.2 hN.le)
    _ = 2 / N * (∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 6) χ t r s‖ ^ 2 +
          ∑ r ∈ P, ∑ s ∈ P, ‖gramP (5 * N / 4) χ t r s‖ ^ 2) := by ring

/-! ### Every Gram entry, reflected -/

/-- The tail bound `T_K(N, τ) = 2^{ω(q)+1}πC_KEQh(q)q^{K+1/2}(NZ)^{−K}(1 + |τ|)^{K+1}I_K` of round 642's
`norm_integral_Tl_le`. -/
def TK (q K : ℕ) (N : ℝ) (Z : ℕ) (τ : ℝ) : ℝ :=
  2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
    (N * Z) ^ (-(K : ℝ)) * (1 + |τ|) ^ (K + 1) * IK K

/-- The dual sum of the pair `(r, s)`: `D_{rs}(u) = Σ_{m≤Z}(χ_rχ̄_s)⁻¹(m)m^{−1/2+i(u−τ)}`, with `τ = t_r − t_s`. -/
def Drs {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (r s : ι) (u : ℝ) : ℂ :=
  dualS (χ r * (χ s)⁻¹)⁻¹ Z ((1 / 2 : ℝ) + (u - ((t r - t s : ℝ) : ℂ)) * I)

/-- **Every Gram entry**: for `q ≥ 1`, `N > 0` and `Z, K ≥ 1`, with `τ = t_r − t_s`,
`|G(r, s)| ≤ [χ_r = χ_s]N|H(1 + iτ)| + (2π)⁻¹(N^{1/2}Q₀(q)∫|H(1/2 + iu)||D_{rs}(u)| du + T_K(N, τ))` (round 642's
`norm_gram_le` and round 697's `norm_gram_le0`). -/
theorem norm_gram_le_all {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (r s : ι) {Z K : ℕ} (hZ : 1 ≤ Z) (hK : 1 ≤ K) :
    ‖gramP N χ t r s‖ ≤ (if χ r = χ s then N * ‖H (1 + ((t r - t s : ℝ) : ℂ) * I)‖ else 0) +
      (2 * Real.pi)⁻¹ * (N ^ (1 / 2 : ℝ) * Q0 q * (∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖) +
        TK q K N Z (t r - t s)) := by
  by_cases h : χ r = χ s
  · rw [ite_eq_left h]
    have h1 : (χ r * (χ s)⁻¹)⁻¹ = (1 : DirichletCharacter ℂ q)⁻¹ := by rw [h, mul_inv_cancel]
    unfold Drs TK
    rw [h1]
    exact norm_gram_le0 hN χ t h hZ hK
  · rw [ite_eq_right h, zero_add]
    exact norm_gram_le hN χ t h hZ hK

/-- The residue term of the pair `(r, s)`: `|H(1 + i(t_r − t_s))|²` when `χ_r = χ_s`, else `0`. -/
def Res {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r s : ι) : ℝ :=
  if χ r = χ s then ‖H (1 + ((t r - t s : ℝ) : ℂ) * I)‖ ^ 2 else 0

/-- The main term of the pair `(r, s)`: `∫|H(1/2 + iu)||D_{rs}(u)| du`. -/
def Imain {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (r s : ι) : ℝ :=
  ∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖

/-! ### The dual sums, gathered -/

/-- For `m ≥ 1` and real `x`, `conj(m^{ix}) = m^{−ix}`. -/
lemma conj_natCast_cpow_I {m : ℕ} (hm : 0 < m) (x : ℝ) :
    conj ((m : ℂ) ^ ((x : ℂ) * I)) = (m : ℂ) ^ (((-x : ℝ) : ℂ) * I) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hl : Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg m)]
  rw [Complex.cpow_def_of_ne_zero hm0, Complex.cpow_def_of_ne_zero hm0, ← Complex.exp_conj, hl]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `D_{rs}(u) = Σ_{m≤Z}m^{−1/2+iu}Ā_r(m)A_s(m)`, written as the summand of the double sum of the conjugate family. -/
lemma Drs_eq {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (r s : ι) (u : ℝ) :
    Drs χ t Z r s u = ∑ m ∈ Finset.Icc 1 Z,
      wh m * (m : ℂ) ^ ((u : ℂ) * I) * conj (famA χ t r m) * conj (conj (famA χ t s m)) := by
  unfold Drs dualS
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 0 < m := (Finset.mem_Icc.1 hm).1
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm1.ne'
  have hχ : (χ r * (χ s)⁻¹)⁻¹ (m : ZMod q) = conj (χ r m) * χ s m := by
    rw [← MulChar.star_apply', MulChar.mul_apply, ← MulChar.star_apply', star_mul', star_star]
    rfl
  have hw : wh m = (m : ℂ) ^ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    unfold wh
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast]
  have hp : (m : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + ((u : ℂ) - ((t r - t s : ℝ) : ℂ)) * I - 1) =
      (m : ℂ) ^ (((-(1 / 2 : ℝ)) : ℝ) : ℂ) * (m : ℂ) ^ ((u : ℂ) * I) * (m : ℂ) ^ (((-t r : ℝ) : ℂ) * I) *
        (m : ℂ) ^ ((t s : ℂ) * I) := by
    rw [← Complex.cpow_add _ _ hm0, ← Complex.cpow_add _ _ hm0, ← Complex.cpow_add _ _ hm0]
    congr 1
    push_cast
    ring
  rw [Complex.conj_conj, hχ, hp, hw]
  unfold famA
  rw [map_mul, conj_natCast_cpow_I hm1 (t r)]
  ring

/-- **The dual sums gathered**: for real `u`, `Σ_{r,s}|D_{rs}(u)|² ≤ Ŝ(Z)`. -/
lemma sum_norm_Drs_sq_le {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (u : ℝ) :
    ∑ r ∈ P, ∑ s ∈ P, ‖Drs χ t Z r s u‖ ^ 2 ≤ shat P χ t Z := by
  have e : ∑ r ∈ P, ∑ s ∈ P, ‖Drs χ t Z r s u‖ ^ 2 =
      dsum P (fun r n => conj (famA χ t r n)) (Finset.Icc 1 Z) (fun m => wh m * (m : ℂ) ^ ((u : ℂ) * I)) := by
    unfold dsum
    simp only [Drs_eq]
  rw [e, dsum_conj]
  unfold shat
  rw [Nat.floor_natCast]
  refine dsum_le P (famA χ t) le_rfl (b := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (fun n hn => ?_)
    (fun n _ => by positivity)
  have hn1 : 0 < n := (Finset.mem_Icc.1 hn).1
  rw [Complex.norm_conj, norm_mul, norm_wh, Complex.norm_natCast_cpow_of_pos hn1]
  simp

/-! ### Cauchy–Schwarz -/

/-- For `I, A, B ≥ 0` with `2λI ≤ λ²A + B` for every `λ > 0`, `I² ≤ AB`. -/
lemma sq_le_of_forall {I A B : ℝ} (hI : 0 ≤ I) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → 2 * l * I ≤ l ^ 2 * A + B) : I ^ 2 ≤ A * B := by
  rcases hI.eq_or_lt with hI0 | hIpos
  · rw [← hI0, sq, zero_mul]
    exact mul_nonneg hA hB
  rcases hA.eq_or_lt with hA0 | hApos
  · exfalso
    have h1 := h ((B + 1) / (2 * I)) (by positivity)
    have e : 2 * ((B + 1) / (2 * I)) * I = B + 1 := by field_simp
    rw [e, ← hA0, mul_zero, zero_add] at h1
    linarith
  · have h1 := h (I / A) (by positivity)
    have e1 : 2 * (I / A) * I = 2 * (I ^ 2 / A) := by ring
    have e2 : (I / A) ^ 2 * A = I ^ 2 / A := by field_simp
    rw [e1, e2] at h1
    have h3 : I ^ 2 / A ≤ B := by linarith
    rw [div_le_iff₀ hApos] at h3
    linarith

/-- **Cauchy–Schwarz**: for `h, d ≥ 0` with `h`, `hd` and `hd²` integrable, `(∫hd)² ≤ (∫h)(∫hd²)`. -/
lemma integral_mul_sq_le {h d : ℝ → ℝ} (hh : ∀ u, 0 ≤ h u) (hd : ∀ u, 0 ≤ d u) (h1 : Integrable h)
    (h2 : Integrable fun u => h u * d u) (h3 : Integrable fun u => h u * d u ^ 2) :
    (∫ u, h u * d u) ^ 2 ≤ (∫ u, h u) * ∫ u, h u * d u ^ 2 := by
  refine sq_le_of_forall (integral_nonneg fun u => mul_nonneg (hh u) (hd u)) (integral_nonneg hh)
    (integral_nonneg fun u => mul_nonneg (hh u) (sq_nonneg _)) fun l hl => ?_
  have hpt : ∀ u, 2 * l * (h u * d u) ≤ l ^ 2 * h u + h u * d u ^ 2 := fun u => by
    nlinarith [mul_nonneg (hh u) (sq_nonneg (l - d u))]
  calc 2 * l * ∫ u, h u * d u = ∫ u, 2 * l * (h u * d u) := (integral_const_mul _ _).symm
    _ ≤ ∫ u, (l ^ 2 * h u + h u * d u ^ 2) :=
        integral_mono (h2.const_mul _) ((h1.const_mul _).add h3) fun u => hpt u
    _ = l ^ 2 * (∫ u, h u) + ∫ u, h u * d u ^ 2 := by
        rw [integral_add (h1.const_mul _) h3, integral_const_mul]

/-! ### The main terms, summed -/

/-- `A_H = ∫|H(1/2 + iu)| du`. -/
def AH : ℝ := ∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖

lemma AH_nonneg : 0 ≤ AH := integral_nonneg fun _ => norm_nonneg _

lemma integrable_H_half : Integrable fun u : ℝ => H ((1 / 2 : ℝ) + u * I) := by
  have h := integrable_H_line (1 / 2) 0
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp

/-- `u ↦ |H(1/2 + iu)||D_{rs}(u)|^k` is integrable, being at most `Z^k|H(1/2 + iu)|`. -/
lemma integrable_H_Drs {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (r s : ι) (k : ℕ) :
    Integrable fun u : ℝ => ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖ ^ k := by
  have hc : Continuous fun u : ℝ => ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖ ^ k := by
    unfold Drs
    exact continuous_H_half.norm.mul ((continuous_dualS_line _ Z (1 / 2) (t r - t s)).norm.pow k)
  refine (integrable_H_half.norm.const_mul ((Z : ℝ) ^ k)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hD : ‖Drs χ t Z r s u‖ ≤ Z := by
    unfold Drs
    exact norm_dualS_le _ Z (by simp; norm_num)
  calc ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖ ^ k ≤ ‖H ((1 / 2 : ℝ) + u * I)‖ * (Z : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hD k) (norm_nonneg _)
    _ = (Z : ℝ) ^ k * ‖H ((1 / 2 : ℝ) + u * I)‖ := by ring

/-- **The main terms summed**: `Σ_{r,s}(∫|H(1/2 + iu)||D_{rs}(u)| du)² ≤ A_H²Ŝ(Z)`. -/
theorem sum_main_sq_le {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) :
    ∑ r ∈ P, ∑ s ∈ P, Imain χ t Z r s ^ 2 ≤ AH ^ 2 * shat P χ t Z := by
  unfold Imain
  have hint : ∀ r s, Integrable fun u : ℝ => ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖ ^ 2 :=
    fun r s => integrable_H_Drs χ t Z r s 2
  calc ∑ r ∈ P, ∑ s ∈ P, (∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖) ^ 2
      ≤ ∑ r ∈ P, ∑ s ∈ P, AH * ∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖ ^ 2 := by
        refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => ?_
        have h1 := integrable_H_Drs χ t Z r s 1
        simp only [pow_one] at h1
        exact integral_mul_sq_le (h := fun u => ‖H ((1 / 2 : ℝ) + u * I)‖) (d := fun u => ‖Drs χ t Z r s u‖)
          (fun u => norm_nonneg _) (fun u => norm_nonneg _) integrable_H_half.norm h1 (hint r s)
    _ = AH * ∫ u : ℝ, ∑ r ∈ P, ∑ s ∈ P, ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖Drs χ t Z r s u‖ ^ 2 := by
        rw [integral_finsetSum P fun r _ => integrable_finsetSum P fun s _ => hint r s, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [integral_finsetSum P fun s _ => hint r s, Finset.mul_sum]
    _ ≤ AH * ∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ * shat P χ t Z := by
        refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun u => ?_) AH_nonneg
        · exact integrable_finsetSum P fun r _ => integrable_finsetSum P fun s _ => hint r s
        · exact integrable_H_half.norm.mul_const _
        · simp only [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_norm_Drs_sq_le P χ t Z u) (norm_nonneg _)
    _ = AH ^ 2 * shat P χ t Z := by
        rw [integral_mul_const]
        unfold AH
        ring

/-! ### The residues -/

/-- `C₀ = Σ_{m∈ℤ}|m + 1/2|^{−2}`. -/
def C0 : ℝ := ∑' m : ℤ, 1 / |(m : ℝ) + 1 / 2| ^ (2 : ℝ)

lemma summable_C0 : Summable fun m : ℤ => 1 / |(m : ℝ) + 1 / 2| ^ (2 : ℝ) :=
  (Real.summable_one_div_int_add_rpow (1 / 2) 2).2 (by norm_num)

lemma C0_nonneg : 0 ≤ C0 := tsum_nonneg fun _ => by positivity

/-- `(1 + |x|)^{−2} ≤ |⌊x⌋ + 1/2|^{−2}`. -/
lemma inv_sq_le_floor (x : ℝ) : ((1 + |x|) ^ 2)⁻¹ ≤ 1 / |((⌊x⌋ : ℤ) : ℝ) + 1 / 2| ^ (2 : ℝ) := by
  have h1 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have h2 : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  have hpos : 0 < |((⌊x⌋ : ℤ) : ℝ) + 1 / 2| := by
    rw [abs_pos]
    intro h
    have h3 : (2 : ℝ) * ⌊x⌋ + 1 = 0 := by linarith
    have h4 : (2 * ⌊x⌋ + 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  have hle : |((⌊x⌋ : ℤ) : ℝ) + 1 / 2| ≤ 1 + |x| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le x, le_abs_self x]
  rw [Real.rpow_two, one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hle 2)

/-- **The residues over separated points**: if the points with the same character are `1`-separated, then for each
`r`, `Σ_{s: χ_r = χ_s}(1 + |t_r − t_s|)^{−2} ≤ C₀`. -/
lemma sum_sep_le {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) (r : ι) :
    ∑ s ∈ P.filter (fun s => χ r = χ s), ((1 + |t r - t s|) ^ 2)⁻¹ ≤ C0 := by
  set F := P.filter (fun s => χ r = χ s) with hF
  have hinj : Set.InjOn (fun s => ⌊t r - t s⌋) F := by
    intro s hs s' hs' hss'
    by_contra hne
    have hs1 := Finset.mem_filter.1 hs
    have hs1' := Finset.mem_filter.1 hs'
    have hlt := Int.abs_sub_lt_one_of_floor_eq_floor hss'
    have e : t r - t s - (t r - t s') = t s' - t s := by ring
    rw [e, abs_sub_comm] at hlt
    rcases hsep s hs1.1 s' hs1'.1 hne with h | h
    · exact h (hs1.2.symm.trans hs1'.2)
    · linarith
  calc ∑ s ∈ F, ((1 + |t r - t s|) ^ 2)⁻¹
      ≤ ∑ s ∈ F, 1 / |((⌊t r - t s⌋ : ℤ) : ℝ) + 1 / 2| ^ (2 : ℝ) :=
        Finset.sum_le_sum fun s _ => inv_sq_le_floor _
    _ = ∑ m ∈ F.image (fun s => ⌊t r - t s⌋), 1 / |(m : ℝ) + 1 / 2| ^ (2 : ℝ) :=
        (Finset.sum_image (f := fun m : ℤ => 1 / |(m : ℝ) + 1 / 2| ^ (2 : ℝ)) hinj).symm
    _ ≤ C0 := summable_C0.sum_le_tsum _ fun m _ => by positivity

/-- There is `B ≥ 0` with `|H(1 + iτ)|² ≤ B²(1 + |τ|)^{−2}` for every real `τ` (round 641's `H_shift_bound`). -/
lemma H_one_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, ‖H (1 + τ * I)‖ ^ 2 ≤ B ^ 2 * ((1 + |τ|) ^ 2)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := H_shift_bound 0 (S := 1) zero_le_one
  refine ⟨B, hB0, fun τ => ?_⟩
  have h := hB 1 0 τ (by norm_num)
  have e1 : ((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I + (τ : ℂ) * I = 1 + τ * I := by push_cast; ring
  have e2 : |(0 : ℝ) + τ| = |τ| := by rw [zero_add]
  rw [e1, e2] at h
  have hu : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have h3 : ((1 + |τ|) ^ (0 + 3))⁻¹ ≤ (1 + |τ|)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    calc 1 + |τ| = (1 + |τ|) ^ 1 := (pow_one _).symm
      _ ≤ (1 + |τ|) ^ (0 + 3) := pow_le_pow_right₀ hu (by norm_num)
  have h4 : ‖H (1 + τ * I)‖ ≤ B * (1 + |τ|)⁻¹ := h.trans (mul_le_mul_of_nonneg_left h3 hB0)
  calc ‖H (1 + τ * I)‖ ^ 2 ≤ (B * (1 + |τ|)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    _ = B ^ 2 * ((1 + |τ|) ^ 2)⁻¹ := by rw [mul_pow, inv_pow]

/-- **The residues summed**: if the points with the same character are `1`-separated and
`|H(1 + iτ)|² ≤ B²(1 + |τ|)^{−2}`, then `Σ_{r,s: χ_r = χ_s}|H(1 + i(t_r − t_s))|² ≤ B²C₀R`. -/
lemma sum_res_le {q : ℕ} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) {B : ℝ}
    (hB : ∀ τ : ℝ, ‖H (1 + τ * I)‖ ^ 2 ≤ B ^ 2 * ((1 + |τ|) ^ 2)⁻¹) :
    ∑ r ∈ P, ∑ s ∈ P, Res χ t r s ≤ B ^ 2 * C0 * P.card := by
  unfold Res
  calc ∑ r ∈ P, ∑ s ∈ P, (if χ r = χ s then ‖H (1 + ((t r - t s : ℝ) : ℂ) * I)‖ ^ 2 else 0)
      = ∑ r ∈ P, ∑ s ∈ P.filter (fun s => χ r = χ s), ‖H (1 + ((t r - t s : ℝ) : ℂ) * I)‖ ^ 2 :=
        Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm
    _ ≤ ∑ r ∈ P, B ^ 2 * C0 := by
        refine Finset.sum_le_sum fun r _ => ?_
        calc ∑ s ∈ P.filter (fun s => χ r = χ s), ‖H (1 + ((t r - t s : ℝ) : ℂ) * I)‖ ^ 2
            ≤ ∑ s ∈ P.filter (fun s => χ r = χ s), B ^ 2 * ((1 + |t r - t s|) ^ 2)⁻¹ :=
              Finset.sum_le_sum fun s _ => hB _
          _ = B ^ 2 * ∑ s ∈ P.filter (fun s => χ r = χ s), ((1 + |t r - t s|) ^ 2)⁻¹ := by
              rw [Finset.mul_sum]
          _ ≤ B ^ 2 * C0 := mul_le_mul_of_nonneg_left (sum_sep_le P χ t hsep r) (sq_nonneg B)
    _ = B ^ 2 * C0 * P.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### The tails -/

/-- `T_K(N, Z, T) = 2^{ω(q)+1}πC_KEQh(q)q^{K+1/2}(NZ)^{−K}(1 + 2T)^{K+1}I_K`. -/
def TT (q K : ℕ) (N : ℝ) (Z : ℕ) (T : ℝ) : ℝ :=
  2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
    (N * Z) ^ (-(K : ℝ)) * (1 + 2 * T) ^ (K + 1) * IK K

lemma TK_nonneg (q K : ℕ) (N : ℝ) (Z : ℕ) (τ : ℝ) (hN : 0 ≤ N) : 0 ≤ TK q K N Z τ := by
  unfold TK
  have := CGK_pos K
  have := EQh_pos q
  have := IK_nonneg K
  positivity

/-- For `N > 0`, `5N/6 ≤ N'`, `Z ≥ 1` and `|τ| ≤ 2T`, `T_K(N', τ) ≤ 2^KT_K(N, Z, T)`. -/
lemma TK_le {q K : ℕ} {N N' T τ : ℝ} {Z : ℕ} (hN : 0 < N) (hN' : 5 * N / 6 ≤ N') (hZ : 1 ≤ Z)
    (hτ : |τ| ≤ 2 * T) : TK q K N' Z τ ≤ 2 ^ K * TT q K N Z T := by
  have hZ0 : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hNZ : 0 < N * Z := by positivity
  have h1 : (N' * Z) ^ (-(K : ℝ)) ≤ 2 ^ K * (N * Z) ^ (-(K : ℝ)) := by
    have ha : 0 < 5 / 6 * (N * Z) := by positivity
    have hb : 5 / 6 * (N * Z) ≤ N' * Z := by nlinarith
    calc (N' * Z) ^ (-(K : ℝ)) ≤ (5 / 6 * (N * Z)) ^ (-(K : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos ha hb (by simp)
      _ = (5 / 6 : ℝ) ^ (-(K : ℝ)) * (N * Z) ^ (-(K : ℝ)) := Real.mul_rpow (by norm_num) hNZ.le
      _ ≤ 2 ^ K * (N * Z) ^ (-(K : ℝ)) := by
          gcongr
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
          exact pow_le_pow_left₀ (by norm_num) (by norm_num) K
  have h2 : (1 + |τ|) ^ (K + 1) ≤ (1 + 2 * T) ^ (K + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hCK := CGK_pos K
  have hEQ := EQh_pos q
  have hI := IK_nonneg K
  unfold TK TT
  calc 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N' * Z) ^ (-(K : ℝ)) * (1 + |τ|) ^ (K + 1) * IK K
      ≤ 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (2 ^ K * (N * Z) ^ (-(K : ℝ))) * (1 + 2 * T) ^ (K + 1) * IK K := by gcongr
    _ = 2 ^ K * (2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N * Z) ^ (-(K : ℝ)) * (1 + 2 * T) ^ (K + 1) * IK K) := by ring

/-! ### The reflected double sum -/

/-- `(a + b + d)² ≤ 3a² + 3b² + 3d²`. -/
lemma add_sq_le_three (a b d : ℝ) : (a + b + d) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * d ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - d), sq_nonneg (b - d)]

/-- **One pair**: for `q ≥ 1`, `N > 0`, `Z, K ≥ 1` and `T_K(N, t_r − t_s) ≤ X`,
`|G(r, s)|² ≤ 3[χ_r = χ_s]N²|H(1 + iτ)|² + 3(2π)⁻²NQ₀(q)²(∫|H(1/2 + iu)||D_{rs}(u)| du)² + 3(2π)⁻²X²`. -/
lemma pair_sq_le {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (r s : ι)
    {Z K : ℕ} (hZ : 1 ≤ Z) (hK : 1 ≤ K) {X : ℝ} (hX : TK q K N Z (t r - t s) ≤ X) :
    ‖gramP N χ t r s‖ ^ 2 ≤
      3 * N ^ 2 * Res χ t r s + 3 * ((2 * Real.pi)⁻¹) ^ 2 * N * Q0 q ^ 2 * Imain χ t Z r s ^ 2 +
        3 * ((2 * Real.pi)⁻¹) ^ 2 * X ^ 2 := by
  have h := norm_gram_le_all hN χ t r s hZ hK
  rw [← Imain] at h
  set c : ℝ := (2 * Real.pi)⁻¹ with hc
  set I1 := Imain χ t Z r s with hI1
  set a := (if χ r = χ s then N * ‖H (1 + ((t r - t s : ℝ) : ℂ) * I)‖ else 0) with ha
  set Y := TK q K N Z (t r - t s) with hY
  have hY0 : 0 ≤ Y := TK_nonneg q K N Z _ hN.le
  have hNh : (N ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have h1 : ‖gramP N χ t r s‖ ^ 2 ≤ (a + c * (N ^ (1 / 2 : ℝ) * Q0 q * I1) + c * Y) ^ 2 := by
    have e : a + c * (N ^ (1 / 2 : ℝ) * Q0 q * I1) + c * Y = a + c * (N ^ (1 / 2 : ℝ) * Q0 q * I1 + Y) := by ring
    rw [e]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have h2 := add_sq_le_three a (c * (N ^ (1 / 2 : ℝ) * Q0 q * I1)) (c * Y)
  have ha2 : a ^ 2 = N ^ 2 * Res χ t r s := by
    rw [ha]
    unfold Res
    split_ifs <;> ring
  have hb2 : (c * (N ^ (1 / 2 : ℝ) * Q0 q * I1)) ^ 2 = c ^ 2 * N * Q0 q ^ 2 * I1 ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hNh]
    ring
  have hd2 : (c * Y) ^ 2 ≤ c ^ 2 * X ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0 hX 2) (sq_nonneg c)
  rw [ha2, hb2] at h2
  linarith

/-- Three double sums: `Σ_{r,s}(f(r, s) + g(r, s) + k) = Σ_{r,s}f + Σ_{r,s}g + kR²`. -/
lemma sum_sum_three (P : Finset ι) (f g : ι → ι → ℝ) (k : ℝ) :
    ∑ r ∈ P, ∑ s ∈ P, (f r s + g r s + k) =
      ∑ r ∈ P, ∑ s ∈ P, f r s + ∑ r ∈ P, ∑ s ∈ P, g r s + k * ((P.card : ℝ) * P.card) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The Gram matrices summed**: for `q ≥ 1`, `N > 0`, `5N/6 ≤ N' ≤ 5N/4`, `Z, K ≥ 1`, `|t_r| ≤ T`, the points with
the same character `1`-separated and `|H(1 + iτ)|² ≤ B²(1 + |τ|)^{−2}`,
`Σ_{r,s}|G_{N'}(r, s)|² ≤ 5N²B²C₀R + (N/9)Q₀(q)²A_H²Ŝ(Z) + (4^K/12)T_K(N, Z, T)²R²`. -/
theorem sum_gram_sq_le {q : ℕ} [NeZero q] (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {T N N' : ℝ} {Z K : ℕ} (hN : 0 < N) (hN1 : 5 * N / 6 ≤ N') (hN2 : N' ≤ 5 * N / 4) (hZ : 1 ≤ Z) (hK : 1 ≤ K)
    (ht : ∀ i ∈ P, |t i| ≤ T) (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) {B : ℝ}
    (hB : ∀ τ : ℝ, ‖H (1 + τ * I)‖ ^ 2 ≤ B ^ 2 * ((1 + |τ|) ^ 2)⁻¹) :
    ∑ r ∈ P, ∑ s ∈ P, ‖gramP N' χ t r s‖ ^ 2 ≤
      5 * N ^ 2 * (B ^ 2 * C0 * P.card) + N / 9 * (Q0 q ^ 2 * (AH ^ 2 * shat P χ t Z)) +
        4 ^ K / 12 * (TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2) := by
  have hN' : 0 < N' := lt_of_lt_of_le (by positivity) hN1
  have hτ : ∀ r ∈ P, ∀ s ∈ P, |t r - t s| ≤ 2 * T := fun r hr s hs => by
    have := abs_sub (t r) (t s)
    linarith [ht r hr, ht s hs]
  set c : ℝ := (2 * Real.pi)⁻¹ with hc
  have hc2 : c ^ 2 ≤ 1 / 36 := by
    have hpi := Real.pi_gt_three
    have h36 : (36 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith
    rw [hc, inv_pow, one_div]
    exact inv_anti₀ (by norm_num) h36
  have hS0 : 0 ≤ shat P χ t Z := dsum_nonneg _ _ _ _
  have hC0 := C0_nonneg
  have hAH := AH_nonneg
  have h4K : (0 : ℝ) ≤ 4 ^ K := by positivity
  have hA : 3 * N' ^ 2 * ∑ r ∈ P, ∑ s ∈ P, Res χ t r s ≤ 5 * N ^ 2 * (B ^ 2 * C0 * P.card) := by
    have h5 : N' ^ 2 ≤ (5 * N / 4) ^ 2 := pow_le_pow_left₀ hN'.le hN2 2
    have h6 : 3 * N' ^ 2 ≤ 5 * N ^ 2 := by linarith [sq_nonneg N]
    calc 3 * N' ^ 2 * ∑ r ∈ P, ∑ s ∈ P, Res χ t r s ≤ 3 * N' ^ 2 * (B ^ 2 * C0 * P.card) :=
          mul_le_mul_of_nonneg_left (sum_res_le P χ t hsep hB) (by positivity)
      _ ≤ 5 * N ^ 2 * (B ^ 2 * C0 * P.card) := mul_le_mul_of_nonneg_right h6 (by positivity)
  have hBm : 3 * c ^ 2 * N' * Q0 q ^ 2 * ∑ r ∈ P, ∑ s ∈ P, Imain χ t Z r s ^ 2 ≤
      N / 9 * (Q0 q ^ 2 * (AH ^ 2 * shat P χ t Z)) := by
    have h5 := mul_le_mul_of_nonneg_right hc2 hN'.le
    have hcN : 3 * c ^ 2 * N' ≤ N / 9 := by linarith
    calc 3 * c ^ 2 * N' * Q0 q ^ 2 * ∑ r ∈ P, ∑ s ∈ P, Imain χ t Z r s ^ 2
        ≤ 3 * c ^ 2 * N' * Q0 q ^ 2 * (AH ^ 2 * shat P χ t Z) :=
          mul_le_mul_of_nonneg_left (sum_main_sq_le P χ t Z) (by positivity)
      _ = 3 * c ^ 2 * N' * (Q0 q ^ 2 * (AH ^ 2 * shat P χ t Z)) := by ring
      _ ≤ N / 9 * (Q0 q ^ 2 * (AH ^ 2 * shat P χ t Z)) := mul_le_mul_of_nonneg_right hcN (by positivity)
  have hCt : 3 * c ^ 2 * (2 ^ K * TT q K N Z T) ^ 2 * ((P.card : ℝ) * P.card) ≤
      4 ^ K / 12 * (TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2) := by
    have e4 : ((2 : ℝ) ^ K) ^ 2 = 4 ^ K := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h5 := mul_le_mul_of_nonneg_right hc2 h4K
    have hk : 3 * c ^ 2 * 4 ^ K ≤ 4 ^ K / 12 := by linarith
    calc 3 * c ^ 2 * (2 ^ K * TT q K N Z T) ^ 2 * ((P.card : ℝ) * P.card)
        = 3 * c ^ 2 * 4 ^ K * (TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2) := by rw [mul_pow, e4]; ring
      _ ≤ 4 ^ K / 12 * (TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hk (by positivity)
  have hpair : ∀ r ∈ P, ∀ s ∈ P, ‖gramP N' χ t r s‖ ^ 2 ≤
      3 * N' ^ 2 * Res χ t r s + 3 * c ^ 2 * N' * Q0 q ^ 2 * Imain χ t Z r s ^ 2 +
        3 * c ^ 2 * (2 ^ K * TT q K N Z T) ^ 2 :=
    fun r hr s hs => pair_sq_le hN' χ t r s hZ hK (TK_le hN hN1 hZ (hτ r hr s hs))
  calc ∑ r ∈ P, ∑ s ∈ P, ‖gramP N' χ t r s‖ ^ 2
      ≤ ∑ r ∈ P, ∑ s ∈ P, (3 * N' ^ 2 * Res χ t r s + 3 * c ^ 2 * N' * Q0 q ^ 2 * Imain χ t Z r s ^ 2 +
          3 * c ^ 2 * (2 ^ K * TT q K N Z T) ^ 2) :=
        Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun s hs => hpair r hr s hs
    _ = ∑ r ∈ P, ∑ s ∈ P, 3 * N' ^ 2 * Res χ t r s +
          ∑ r ∈ P, ∑ s ∈ P, 3 * c ^ 2 * N' * Q0 q ^ 2 * Imain χ t Z r s ^ 2 +
          3 * c ^ 2 * (2 ^ K * TT q K N Z T) ^ 2 * ((P.card : ℝ) * P.card) := sum_sum_three P _ _ _
    _ = 3 * N' ^ 2 * ∑ r ∈ P, ∑ s ∈ P, Res χ t r s +
          3 * c ^ 2 * N' * Q0 q ^ 2 * ∑ r ∈ P, ∑ s ∈ P, Imain χ t Z r s ^ 2 +
          3 * c ^ 2 * (2 ^ K * TT q K N Z T) ^ 2 * ((P.card : ℝ) * P.card) := by
        simp only [← Finset.mul_sum]
    _ ≤ 5 * N ^ 2 * (B ^ 2 * C0 * P.card) + N / 9 * (Q0 q ^ 2 * (AH ^ 2 * shat P χ t Z)) +
          4 ^ K / 12 * (TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2) := add_le_add (add_le_add hA hBm) hCt

/-- The arithmetic of the last step: for `N > 0`, `a, b, k, R, S, Y, Q ≥ 0` and
`X₁, X₂ ≤ 5N²aR + (N/9)QbS + (k/12)YR²` (the two bounds of `sum_gram_sq_le`),
`(2/N)(X₁ + X₂) ≤ 20(a + b + k)(NR + QS + YR²/N)`. -/
lemma refl_arith {N R S Y Q a b k X₁ X₂ : ℝ} (hN : 0 < N) (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ k) (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hY : 0 ≤ Y) (hQ : 0 ≤ Q)
    (h1 : X₁ ≤ 5 * N ^ 2 * (a * R) + N / 9 * (Q * (b * S)) + k / 12 * (Y * R ^ 2))
    (h2 : X₂ ≤ 5 * N ^ 2 * (a * R) + N / 9 * (Q * (b * S)) + k / 12 * (Y * R ^ 2)) :
    2 / N * (X₁ + X₂) ≤ 20 * (a + b + k) * (N * R + Q * S + Y * R ^ 2 / N) := by
  have hN0 : N ≠ 0 := hN.ne'
  have hX : X₁ + X₂ ≤ 2 * (5 * N ^ 2 * (a * R) + N / 9 * (Q * (b * S)) + k / 12 * (Y * R ^ 2)) := by linarith
  have e : 2 / N * (2 * (5 * N ^ 2 * (a * R) + N / 9 * (Q * (b * S)) + k / 12 * (Y * R ^ 2))) =
      20 * a * (N * R) + 4 / 9 * b * (Q * S) + k / 3 * (Y * R ^ 2 / N) := by
    field_simp
    ring
  have t1 : 0 ≤ N * R := by positivity
  have t2 : 0 ≤ Q * S := by positivity
  have t3 : 0 ≤ Y * R ^ 2 / N := by positivity
  calc 2 / N * (X₁ + X₂) ≤ 2 / N * (2 * (5 * N ^ 2 * (a * R) + N / 9 * (Q * (b * S)) + k / 12 * (Y * R ^ 2))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 20 * a * (N * R) + 4 / 9 * b * (Q * S) + k / 3 * (Y * R ^ 2 / N) := e
    _ ≤ 20 * (a + b + k) * (N * R + Q * S + Y * R ^ 2 / N) := by
        nlinarith [mul_nonneg ha t1, mul_nonneg hb t1, mul_nonneg hk t1, mul_nonneg ha t2, mul_nonneg hb t2,
          mul_nonneg hk t2, mul_nonneg ha t3, mul_nonneg hb t3, mul_nonneg hk t3]

/-- **The reflection of the double sum**: for `K ≥ 1` there is `C ≥ 0` such that, for `q ≥ 1`, `N > 0`, `Z ≥ 1`,
points with `|t_r| ≤ T` and the points with the same character `1`-separated,
`σ(N) ≤ C(NR + Q₀(q)²Ŝ(Z) + T_K(N, Z, T)²R²/N)`. -/
theorem sig_le_refl {K : ℕ} (hK : 1 ≤ K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (P : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T N : ℝ} {Z : ℕ}, 0 < N → 1 ≤ Z → (∀ i ∈ P, |t i| ≤ T) →
    (∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) →
    sig P χ t N ≤ C * (N * P.card + Q0 q ^ 2 * shat P χ t Z + TT q K N Z T ^ 2 * (P.card : ℝ) ^ 2 / N) := by
  obtain ⟨B, hB0, hB⟩ := H_one_bound
  have hC0 := C0_nonneg
  have hAH := AH_nonneg
  refine ⟨20 * (B ^ 2 * C0 + AH ^ 2 + 4 ^ K), by positivity, ?_⟩
  intro q _ ι P χ t T N Z hN hZ ht hsep
  have h1 := sig_le_gram P χ t hN
  have hg1 := sum_gram_sq_le P χ t hN le_rfl (by linarith) hZ hK ht hsep hB
  have hg2 := sum_gram_sq_le P χ t hN (by linarith) le_rfl hZ hK ht hsep hB
  have h := refl_arith (a := B ^ 2 * C0) (b := AH ^ 2) (k := 4 ^ K) (R := P.card) (S := shat P χ t Z)
    (Y := TT q K N Z T ^ 2) (Q := Q0 q ^ 2) hN (by positivity) (by positivity) (by positivity)
    (Nat.cast_nonneg _) (dsum_nonneg _ _ _ _) (sq_nonneg _) (sq_nonneg _)
    hg1 hg2
  exact h1.trans h

end LinnikCGLHBRefl

#print axioms LinnikCGLHBRefl.sig_le_gram
#print axioms LinnikCGLHBRefl.sum_norm_Drs_sq_le
#print axioms LinnikCGLHBRefl.sum_sep_le
#print axioms LinnikCGLHBRefl.sum_gram_sq_le
#print axioms LinnikCGLHBRefl.sig_le_refl
