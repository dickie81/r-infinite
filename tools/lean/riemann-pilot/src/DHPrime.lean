import Mathlib
import DHZeros

/-! # The prime side of the Davenport–Heilbronn function (round 256)

`dh(s) = Σ a(n) n^{−s}` on `Re s > 1` with `a(n) = (1 + ε′)χ₅(n) + (1 + ε)χ₅⁻¹(n)`
(`dhL_eq_LSeries`), and `a(1) = (1 + ε)(1 + ε′) ≠ 0` (`aDH_one_eq`, `aDH_one_ne_zero`). Normalising,
`a = a(1)·(δ + u)` with `u(n) = a(n)/a(1)` on `n ≥ 2` (`LSeries_aDH_eq`).

**The Dirichlet inverse** (namespace `DInv`, agent-built, re-read and recompiled by the lead): for any
`u` vanishing at `0, 1`, `dinv u` is the inverse of `δ + u` under Dirichlet convolution
(`convolution_dinv`), with the norm bound `Σ_{n ≤ N} ‖dinv u n‖ n^{−σ} ≤ 1/(1 − K)` whenever
`Σ_{n ≤ N} ‖u n‖ n^{−σ} ≤ K < 1` (`sum_norm_dinv_le`), hence `LSeries (δ + u) · LSeries (dinv u) = 1`
on `Re s ≥ σ` (`LSeries_mul_dinv`).

**The log-derivative.** With `c = logMul(δ + u) ⍟ dinv u` (`cDH`), for every primitive `χ ≠ 1` with
`ε_χ ≠ −1`: `DH_χ′(s)/DH_χ(s) = −Σ c(n) n^{−s}` on `Re s > 1`, `Re s ≥ σ` (`logDeriv_dhL_eq`, from
Mathlib's `LSeries_deriv` and `LSeries_convolution'`).

**The numerics for `χ₅`** (agent-built, re-read and recompiled by the lead): the Gauss sum is
`−2 sin(π/5) + 2i sin(2π/5)`, so `ε = (2 sin(2π/5) + 2i sin(π/5))/√5` (`rootNumber_chi5_eq`),
`‖ε‖ = 1` from `sin²(π/5) + sin²(2π/5) = 5/4` (`norm_rootNumber_chi5`), `Re ε ≥ 4/5`
(`re_rootNumber_chi5_ge`), `‖1 + ε‖, ‖1 + ε′‖ ≥ 9/5`, and `ε′ = ε̄` (`rootNumber_chi5_inv_eq_conj`).
Hence `‖u(n)‖ ≤ 10/9` and, with `Σ_{2 ≤ n ≤ N} n^{−2} ≤ 7/10`, `Σ_{n ≤ N} ‖u(n)‖ n^{−2} ≤ 7/9 < 1`
(`sum_norm_uDH_chi5_le`).

**The prime side of `dh`**: on `Re s > 2`, `dh′(s)/dh(s) = −Σ c(n) n^{−s}` with the series absolutely
convergent (`logDeriv_dh_eq`, `LSeriesSummable_cDH_chi5`), and `dh` has no zeros there
(`dh_ne_zero_of_two_lt`). The abscissa `2` is what the crude bounds give; the true zero-free abscissa
of `dh` is smaller. What remains for the explicit formula is the contour argument with the prime
side on `Re s > 2`, which needs the strip machinery of round 225 at width `> 3/2`; see the README.
-/

open Real Complex DirichletCharacter Filter Topology
open scoped LSeries.notation
open LSeries

noncomputable section

namespace DInv

/-- The Dirichlet inverse of `δ + u`, by strong recursion:
`dinv u 0 = 0`, `dinv u 1 = 1`, and for `n ≥ 2`,
`dinv u n = -∑_{(d,e) ∈ n.divisorsAntidiagonal, d ≠ 1} u d * dinv u e`. -/
def dinv (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => -∑ p ∈ ((n + 2).divisorsAntidiagonal.filter (fun p => p.1 ≠ 1)).attach,
      u p.1.1 * dinv u p.1.2
decreasing_by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨⟨hab, -⟩, ha1⟩ := hp
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab
  have h2 : 2 ≤ a := by omega
  show b < n + 2
  nlinarith

theorem dinv_zero (u : ℕ → ℂ) : dinv u 0 = 0 := by
  rw [dinv]

theorem dinv_one (u : ℕ → ℂ) : dinv u 1 = 1 := by
  rw [dinv]

theorem dinv_of_two_le (u : ℕ → ℂ) {n : ℕ} (hn : 2 ≤ n) :
    dinv u n = -∑ p ∈ n.divisorsAntidiagonal with p.1 ≠ 1, u p.1 * dinv u p.2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [dinv]
  congr 1
  exact Finset.sum_attach _ (fun p : ℕ × ℕ => u p.1 * dinv u p.2)

set_option linter.unusedVariables false in
theorem convolution_dinv (u : ℕ → ℂ) (hu0 : u 0 = 0) (hu1 : u 1 = 0) :
    (LSeries.delta + u) ⍟ dinv u = LSeries.delta := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.delta]
  rw [convolution_def]
  dsimp only
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ × ℕ => p.1 = 1)]
  have h1 : (n.divisorsAntidiagonal.filter (fun p : ℕ × ℕ => p.1 = 1)) = {(1, n)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hab, _⟩, rfl⟩
      exact ⟨rfl, by simpa using hab⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨by simp, by omega⟩, rfl⟩
  rw [h1, Finset.sum_singleton]
  have h2 : ∑ x ∈ n.divisorsAntidiagonal with ¬ x.1 = 1, (LSeries.delta + u) x.1 * dinv u x.2
      = ∑ x ∈ n.divisorsAntidiagonal with x.1 ≠ 1, u x.1 * dinv u x.2 := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp [LSeries.delta, hx.2]
  rw [h2]
  simp only [Pi.add_apply, hu1, add_zero]
  have hd1 : LSeries.delta 1 = 1 := by simp [LSeries.delta]
  rw [hd1, one_mul]
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp [dinv_one, Finset.filter_singleton, hd1]
  · rw [dinv_of_two_le u h]
    simp [LSeries.delta, show n ≠ 1 by omega]

/-- Pointwise bound feeding the norm estimate. -/
theorem norm_dinv_mul_le (u : ℕ → ℂ) (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖dinv u n‖ * (n : ℝ) ^ (-σ) ≤ (if n = 1 then 1 else 0) +
      ∑ p ∈ n.divisorsAntidiagonal,
        (‖u p.1‖ * (p.1 : ℝ) ^ (-σ)) * (‖dinv u p.2‖ * (p.2 : ℝ) ^ (-σ)) := by
  have hG : ∀ p ∈ n.divisorsAntidiagonal,
      0 ≤ (‖u p.1‖ * (p.1 : ℝ) ^ (-σ)) * (‖dinv u p.2‖ * (p.2 : ℝ) ^ (-σ)) :=
    fun p _ => by positivity
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp only [dinv_one, Nat.cast_one, Real.one_rpow, ↓reduceIte, norm_one, mul_one]
    have := Finset.sum_nonneg hG
    linarith
  · rw [dinv_of_two_le u h, norm_neg]
    simp only [show n ≠ 1 by omega, ↓reduceIte, zero_add]
    calc ‖∑ p ∈ n.divisorsAntidiagonal with p.1 ≠ 1, u p.1 * dinv u p.2‖ * (n : ℝ) ^ (-σ)
        ≤ (∑ p ∈ n.divisorsAntidiagonal with p.1 ≠ 1, ‖u p.1‖ * ‖dinv u p.2‖) *
            (n : ℝ) ^ (-σ) := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp))
      _ = ∑ p ∈ n.divisorsAntidiagonal with p.1 ≠ 1,
            (‖u p.1‖ * (p.1 : ℝ) ^ (-σ)) * (‖dinv u p.2‖ * (p.2 : ℝ) ^ (-σ)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          have hpn := (Nat.mem_divisorsAntidiagonal.1 (Finset.mem_filter.1 hp).1).1
          rw [← hpn, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
          ring
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
            (‖u p.1‖ * (p.1 : ℝ) ^ (-σ)) * (‖dinv u p.2‖ * (p.2 : ℝ) ^ (-σ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p hp _ => hG p hp)

/-- Reindexing a sum over divisor pairs into a product sum. -/
theorem sum_divisorsAntidiagonal_le (N : ℕ) (G : ℕ × ℕ → ℝ) (hG : ∀ p, 0 ≤ G p) :
    ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, G p ≤
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, G (d, e) := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ) Nat.divisorsAntidiagonal := by
    intro m _ n _ hmn
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpm hpn
    exact hmn ((Nat.mem_divisorsAntidiagonal.1 hpm).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.1 hpn).1)
  rw [← Finset.sum_biUnion hdisj, ← Finset.sum_product]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨n, ⟨h1, h2⟩, hpn, -⟩ := hp
    simp only [Finset.mem_product, Finset.mem_Icc]
    have ha : p.1 ≠ 0 := by rintro h; rw [h] at hpn; omega
    have hb : p.2 ≠ 0 := by rintro h; rw [h] at hpn; omega
    have hle1 : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ (by omega)
    have hle2 : p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · intro p _ _
    exact hG p

set_option linter.unusedVariables false in
theorem sum_norm_dinv_le (u : ℕ → ℂ) (hu0 : u 0 = 0) (hu1 : u 1 = 0) {σ K : ℝ} (hK0 : 0 ≤ K)
    (hK : K < 1) (hu : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖u n‖ * (n : ℝ) ^ (-σ) ≤ K) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖dinv u n‖ * (n : ℝ) ^ (-σ) ≤ 1 / (1 - K) := by
  have hB0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖dinv u n‖ * (n : ℝ) ^ (-σ) :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hstep : ∑ n ∈ Finset.Icc 1 N, ‖dinv u n‖ * (n : ℝ) ^ (-σ) ≤
      1 + K * ∑ n ∈ Finset.Icc 1 N, ‖dinv u n‖ * (n : ℝ) ^ (-σ) := by
    calc ∑ n ∈ Finset.Icc 1 N, ‖dinv u n‖ * (n : ℝ) ^ (-σ)
        ≤ ∑ n ∈ Finset.Icc 1 N, ((if n = 1 then (1 : ℝ) else 0) +
            ∑ p ∈ n.divisorsAntidiagonal,
              (‖u p.1‖ * (p.1 : ℝ) ^ (-σ)) * (‖dinv u p.2‖ * (p.2 : ℝ) ^ (-σ))) :=
          Finset.sum_le_sum (fun n hn => norm_dinv_mul_le u σ (Finset.mem_Icc.1 hn).1)
      _ = ∑ n ∈ Finset.Icc 1 N, (if n = 1 then (1 : ℝ) else 0) +
            ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
              (‖u p.1‖ * (p.1 : ℝ) ^ (-σ)) * (‖dinv u p.2‖ * (p.2 : ℝ) ^ (-σ)) :=
          Finset.sum_add_distrib
      _ ≤ 1 + ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
              (‖u d‖ * (d : ℝ) ^ (-σ)) * (‖dinv u e‖ * (e : ℝ) ^ (-σ)) := by
          gcongr ?_ + ?_
          · rw [Finset.sum_ite_eq']
            split_ifs <;> norm_num
          · exact sum_divisorsAntidiagonal_le N
              (fun p => (‖u p.1‖ * (p.1 : ℝ) ^ (-σ)) * (‖dinv u p.2‖ * (p.2 : ℝ) ^ (-σ)))
              (fun p => by positivity)
      _ = 1 + (∑ d ∈ Finset.Icc 1 N, ‖u d‖ * (d : ℝ) ^ (-σ)) *
            ∑ n ∈ Finset.Icc 1 N, ‖dinv u n‖ * (n : ℝ) ^ (-σ) := by
          rw [Finset.sum_mul_sum]
      _ ≤ 1 + K * ∑ n ∈ Finset.Icc 1 N, ‖dinv u n‖ * (n : ℝ) ^ (-σ) := by
          gcongr
          exact hu N
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- `δ` has a summable L-series everywhere. -/
theorem LSeriesSummable_delta (s : ℂ) : LSeriesSummable LSeries.delta s := by
  unfold LSeriesSummable
  have : term LSeries.delta s = fun n => if n = 1 then 1 else 0 := funext (term_delta s)
  rw [this]
  exact (hasSum_ite_eq 1 (1 : ℂ)).summable

theorem LSeriesSummable_dinv (u : ℕ → ℂ) (hu0 : u 0 = 0) (hu1 : u 1 = 0) {σ K : ℝ}
    (hK0 : 0 ≤ K) (hK : K < 1)
    (hu : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖u n‖ * (n : ℝ) ^ (-σ) ≤ K) {s : ℂ}
    (hs : σ ≤ s.re) : LSeriesSummable (dinv u) s := by
  have hterm : ∀ n, ‖term (dinv u) s n‖ ≤ ‖dinv u n‖ * (n : ℝ) ^ (-σ) := by
    intro n
    rw [norm_term_eq]
    split_ifs with hn
    · positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
      gcongr
  have hsum : ∀ n, ∑ i ∈ Finset.range n, ‖term (dinv u) s i‖ ≤ 1 / (1 - K) := by
    intro n
    have hsub : Finset.range n ⊆ insert 0 (Finset.Icc 1 n) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    calc ∑ i ∈ Finset.range n, ‖term (dinv u) s i‖
        ≤ ∑ i ∈ Finset.range n, ‖dinv u i‖ * (i : ℝ) ^ (-σ) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ∑ i ∈ insert 0 (Finset.Icc 1 n), ‖dinv u i‖ * (i : ℝ) ^ (-σ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ i ∈ Finset.Icc 1 n, ‖dinv u i‖ * (i : ℝ) ^ (-σ) := by
          rw [Finset.sum_insert (by simp), dinv_zero]
          simp
      _ ≤ 1 / (1 - K) := sum_norm_dinv_le u hu0 hu1 hK0 hK hu n
  exact Summable.of_norm (summable_of_sum_range_le (fun _ => norm_nonneg _) hsum)

theorem LSeries_mul_dinv (u : ℕ → ℂ) (hu0 : u 0 = 0) (hu1 : u 1 = 0) {σ K : ℝ}
    (hK0 : 0 ≤ K) (hK : K < 1)
    (hu : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖u n‖ * (n : ℝ) ^ (-σ) ≤ K) {s : ℂ}
    (hs : σ ≤ s.re) (hus : LSeriesSummable u s) :
    LSeries (LSeries.delta + u) s * LSeries (dinv u) s = 1 := by
  rw [← LSeries_convolution' ((LSeriesSummable_delta s).add hus)
    (LSeriesSummable_dinv u hu0 hu1 hK0 hK hu hs), convolution_dinv u hu0 hu1, LSeries_delta]
  rfl

end DInv

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-! ## The Dirichlet coefficients of `DH_χ` -/

/-- `a(n) = (1 + ε_{χ⁻¹}) χ(n) + (1 + ε_χ) χ⁻¹(n)`. -/
def aDH (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  (1 + rootNumber χ⁻¹) * χ n + (1 + rootNumber χ) * χ⁻¹ n

theorem aDH_one : aDH χ 1 = 2 + rootNumber χ + rootNumber χ⁻¹ := by
  simp [aDH]; ring

theorem norm_aDH_le (n : ℕ) : ‖aDH χ n‖ ≤ ‖1 + rootNumber χ⁻¹‖ + ‖1 + rootNumber χ‖ := by
  unfold aDH
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  gcongr
  · exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one χ _)
  · exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one χ⁻¹ _)

theorem LSeriesSummable_aDH {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (aDH χ) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_aDH_le n) hs

theorem abscissa_aDH_le : LSeries.abscissaOfAbsConv (aDH χ) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨_, fun n _ => norm_aDH_le n⟩

/-- **`DH_χ(s) = Σ a(n) n^{−s}` on `Re s > 1`.** -/
theorem dhL_eq_LSeries {s : ℂ} (hs : 1 < s.re) : dhL χ s = LSeries (aDH χ) s := by
  have h1 : LSeriesSummable (fun n : ℕ => χ n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_le_one χ _) hs
  have h2 : LSeriesSummable (fun n : ℕ => χ⁻¹ n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_le_one χ⁻¹ _) hs
  have e : aDH χ = (1 + rootNumber χ⁻¹) • (fun n : ℕ => χ n)
      + (1 + rootNumber χ) • (fun n : ℕ => χ⁻¹ n) := by
    funext n; simp [aDH]
  unfold dhL
  rw [LFunction_eq_LSeries χ hs, LFunction_eq_LSeries χ⁻¹ hs, e,
    LSeries_add (h1.smul _) (h2.smul _), LSeries_smul, LSeries_smul]

/-! ## The normalised coefficients `u = a/a(1)` on `n ≥ 2` -/

/-- `u(n) = a(n)/a(1)` for `n ≥ 2`, and `0` for `n ≤ 1`. -/
def uDH (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := if 2 ≤ n then aDH χ n / aDH χ 1 else 0

theorem uDH_zero : uDH χ 0 = 0 := by simp [uDH]

theorem uDH_one : uDH χ 1 = 0 := by simp [uDH]

theorem norm_uDH_le (n : ℕ) : ‖uDH χ n‖ ≤ (‖1 + rootNumber χ⁻¹‖ + ‖1 + rootNumber χ‖) / ‖aDH χ 1‖ := by
  unfold uDH
  split_ifs
  · rw [norm_div]; exact div_le_div_of_nonneg_right (norm_aDH_le n) (norm_nonneg _)
  · rw [norm_zero]; positivity

theorem aDH_eq_of_ne_zero (h1 : aDH χ 1 ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    aDH χ n = aDH χ 1 * (LSeries.delta + uDH χ) n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    simp [uDH, LSeries.delta]
  · have hn1 : n ≠ 1 := by omega
    simp only [Pi.add_apply, LSeries.delta, hn1, ite_false, uDH, h, ite_true, zero_add]
    field_simp

/-- **`Σ a(n) n^{−s} = a(1) · Σ (δ + u)(n) n^{−s}`.** -/
theorem LSeries_aDH_eq (h1 : aDH χ 1 ≠ 0) (s : ℂ) :
    LSeries (aDH χ) s = aDH χ 1 * LSeries (LSeries.delta + uDH χ) s := by
  rw [← LSeries_smul]
  exact LSeries_congr (fun {n} hn => aDH_eq_of_ne_zero h1 hn) s

theorem LSeriesSummable_delta_add_uDH {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (LSeries.delta + uDH χ) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1 + (‖1 + rootNumber χ⁻¹‖ + ‖1 + rootNumber χ‖) / ‖aDH χ 1‖) (fun n _ => ?_) hs
  refine (norm_add_le _ _).trans ?_
  gcongr
  · simp only [LSeries.delta]; split_ifs <;> simp
  · exact norm_uDH_le n

theorem abscissa_delta_add_uDH_le : LSeries.abscissaOfAbsConv (LSeries.delta + uDH χ) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1 + (‖1 + rootNumber χ⁻¹‖ + ‖1 + rootNumber χ‖) / ‖aDH χ 1‖,
    fun n _ => (norm_add_le _ _).trans (by
      gcongr
      · simp only [LSeries.delta]; split_ifs <;> simp
      · exact norm_uDH_le n)⟩

/-- **`a(1) = (1 + ε_χ)(1 + ε_{χ⁻¹})`**, nonzero when `ε_χ ≠ −1`. -/
theorem aDH_one_eq (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) :
    aDH χ 1 = (1 + rootNumber χ) * (1 + rootNumber χ⁻¹) := by
  have := rootNumber_mul_rootNumber_inv χ hχ1 hprim
  rw [aDH_one]; linear_combination -this

theorem aDH_one_ne_zero (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0) :
    aDH χ 1 ≠ 0 := by
  rw [aDH_one_eq hχ1 hprim]
  exact mul_ne_zero h1 (one_add_rootNumber_inv_ne_zero hχ1 hprim h1)


/-! ## Numeric facts about `ε_{χ₅}` -/

theorem gaussSum_chi5_im :
    (gaussSum chi5 ZMod.stdAddChar).im = 2 * Real.sin (2 * π / 5) := by
  have e1 : exp (2 * π * I / 5) = exp (((2 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e2 : exp (2 * π * I * 2 / 5) = exp (((4 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e3 : exp (2 * π * I * 3 / 5) = exp (((6 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e4 : exp (2 * π * I * 4 / 5) = exp (((8 * π / 5 : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have s8 : Real.sin (8 * π / 5) = -Real.sin (2 * π / 5) := by
    rw [show 8 * π / 5 = 2 * π - 2 * π / 5 by ring, Real.sin_two_pi_sub]
  have c4 : Real.cos (4 * π / 5) = -Real.cos (π / 5) := by
    rw [show 4 * π / 5 = π - π / 5 by ring, Real.cos_pi_sub]
  have c6 : Real.cos (6 * π / 5) = -Real.cos (π / 5) := by
    rw [show 6 * π / 5 = π / 5 + π by ring, Real.cos_add_pi]
  rw [gaussSum_chi5, e1, e2, e3, e4]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [s8, c4, c6]
  ring

theorem rootNumber_chi5_eq :
    rootNumber chi5 = ((2 * Real.sin (2 * π / 5) / Real.sqrt 5 : ℝ) : ℂ)
      + ((2 * Real.sin (π / 5) / Real.sqrt 5 : ℝ) : ℂ) * I := by
  have ht : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have hs : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [rootNumber, ite_eq_right chi5_odd.not_even, pow_one, Nat.cast_ofNat, cpow_five_half,
    div_div, div_eq_iff (mul_ne_zero I_ne_zero hs)]
  apply Complex.ext
  · rw [gaussSum_chi5_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  · rw [gaussSum_chi5_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    field_simp
    ring

theorem sin_sq_pi_div_five_add :
    Real.sin (π / 5) ^ 2 + Real.sin (2 * π / 5) ^ 2 = 5 / 4 := by
  have h2 : Real.cos (2 * π / 5) = 2 * Real.cos (π / 5) ^ 2 - 1 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul]
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [Real.sin_sq, Real.sin_sq, h2, Real.cos_pi_div_five]
  linear_combination ((-(Real.sqrt 5) ^ 2 - 4 * Real.sqrt 5 + 1) / 64) * s5

theorem norm_rootNumber_chi5 : ‖rootNumber chi5‖ = 1 := by
  have ht : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsum := sin_sq_pi_div_five_add
  rw [rootNumber_chi5_eq, Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add]
  rw [show (2 * Real.sin (2 * π / 5) / Real.sqrt 5) ^ 2 + (2 * Real.sin (π / 5) / Real.sqrt 5) ^ 2
      = 1 by
    rw [div_pow, div_pow, s5]
    linear_combination (4 / 5 : ℝ) * hsum, Real.sqrt_one]

theorem re_rootNumber_chi5_ge : (4 : ℝ) / 5 ≤ (rootNumber chi5).re := by
  have hpos5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h75 : (7 : ℝ) / 5 ≤ Real.sqrt 5 := by nlinarith
  have hc := Real.cos_pi_div_five
  have h2 : Real.cos (2 * π / 5) = 2 * Real.cos (π / 5) ^ 2 - 1 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul]
  have hsq : Real.sin (2 * π / 5) ^ 2 = (5 + Real.sqrt 5) / 8 := by
    rw [Real.sin_sq, h2, hc]
    linear_combination (-(Real.sqrt 5) ^ 2 - 4 * Real.sqrt 5 + 5) / 64 * s5
  have hspos : 0 < Real.sin (2 * π / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  rw [rootNumber_chi5_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero]
  rw [le_div_iff₀ hpos5]
  nlinarith

theorem norm_one_add_rootNumber_chi5_ge : (9 : ℝ) / 5 ≤ ‖1 + rootNumber chi5‖ := by
  have h := re_rootNumber_chi5_ge
  have h' := Complex.re_le_norm (1 + rootNumber chi5)
  rw [Complex.add_re, Complex.one_re] at h'
  linarith

theorem rootNumber_chi5_inv_eq_conj :
    rootNumber chi5⁻¹ = (starRingEnd ℂ) (rootNumber chi5) := by
  rw [eq_inv_of_mul_eq_one_right (rootNumber_mul_rootNumber_inv chi5 chi5_ne_one chi5_isPrimitive)]
  exact Complex.inv_eq_conj norm_rootNumber_chi5

theorem norm_one_add_rootNumber_chi5_inv_ge : (9 : ℝ) / 5 ≤ ‖1 + rootNumber chi5⁻¹‖ := by
  rw [rootNumber_chi5_inv_eq_conj,
    show (1 : ℂ) + (starRingEnd ℂ) (rootNumber chi5) = (starRingEnd ℂ) (1 + rootNumber chi5) by
      rw [map_add, map_one],
    Complex.norm_conj]
  exact norm_one_add_rootNumber_chi5_ge

theorem sum_Icc_inv_sq_le_aux (k : ℕ) :
    ∑ n ∈ Finset.Icc 2 (k + 3), ((n : ℝ) ^ 2)⁻¹ ≤ 25 / 36 - 1 / ((k : ℝ) + 3) := by
  induction k with
  | zero =>
    rw [show Finset.Icc 2 (0 + 3) = {2, 3} by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have key : (((k + 3 + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / ((k : ℝ) + 3) - 1 / (((k + 1 : ℕ) : ℝ) + 3) := by
      push_cast
      have e : 1 / ((k : ℝ) + 3) - 1 / ((k : ℝ) + 1 + 3) - (((k : ℝ) + 3 + 1) ^ 2)⁻¹
          = 1 / (((k : ℝ) + 3) * ((k : ℝ) + 4) ^ 2) := by
        field_simp
        ring
      have hp : 0 ≤ 1 / (((k : ℝ) + 3) * ((k : ℝ) + 4) ^ 2) := by positivity
      linarith
    linarith

theorem sum_Icc_inv_sq_le (N : ℕ) : ∑ n ∈ Finset.Icc 2 N, ((n : ℝ) ^ 2)⁻¹ ≤ 7 / 10 := by
  rcases Nat.lt_or_ge N 3 with hN | hN
  · interval_cases N
    · norm_num
    · norm_num
    · rw [Finset.Icc_self, Finset.sum_singleton]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
    have h := sum_Icc_inv_sq_le_aux k
    have hk : 0 ≤ 1 / ((k : ℝ) + 3) := by positivity
    linarith

theorem sum_Icc_rpow_neg_two_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-(2 : ℝ)) ≤ 7 / 10 := by
  calc ∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-(2 : ℝ))
      = ∑ n ∈ Finset.Icc 2 N, ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two]
    _ ≤ 7 / 10 := sum_Icc_inv_sq_le N



/-! ## The prime side: `−DH′/DH = Σ c(n) n^{−s}` -/

/-- The prime-side coefficients `c = logMul(δ + u) ⍟ (δ + u)^{−1}`. -/
def cDH (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  LSeries.logMul (LSeries.delta + uDH χ) ⍟ DInv.dinv (uDH χ)

/-- `DH_χ` agrees with its L-series near any `s` with `Re s > 1`. -/
theorem dhL_eventuallyEq {s : ℂ} (hs : 1 < s.re) : dhL χ =ᶠ[𝓝 s] LSeries (aDH χ) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact dhL_eq_LSeries hz

theorem LSeriesSummable_uDH {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (uDH χ) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_uDH_le n) hs

/-- **The logarithmic derivative of `DH_χ` is a Dirichlet series**: on `Re s > 1` with `Re s ≥ σ`,
where `Σ_{n ≤ N} ‖u(n)‖ n^{−σ} ≤ K < 1`, `DH_χ′(s)/DH_χ(s) = −Σ c(n) n^{−s}`. -/
theorem logDeriv_dhL_eq (hχ1 : χ ≠ 1) (hprim : χ.IsPrimitive) (h1 : 1 + rootNumber χ ≠ 0)
    {σ K : ℝ} (hK0 : 0 ≤ K) (hK : K < 1)
    (hu : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖uDH χ n‖ * (n : ℝ) ^ (-σ) ≤ K)
    {s : ℂ} (hs1 : 1 < s.re) (hsσ : σ ≤ s.re) :
    logDeriv (dhL χ) s = -LSeries (cDH χ) s := by
  have ha1 := aDH_one_ne_zero hχ1 hprim h1
  have habs : LSeries.abscissaOfAbsConv (aDH χ) < s.re :=
    lt_of_le_of_lt abscissa_aDH_le (by exact_mod_cast hs1)
  have habs' : LSeries.abscissaOfAbsConv (LSeries.delta + uDH χ) < s.re :=
    lt_of_le_of_lt abscissa_delta_add_uDH_le (by exact_mod_cast hs1)
  have hd : deriv (dhL χ) s = -LSeries (LSeries.logMul (aDH χ)) s := by
    rw [(dhL_eventuallyEq hs1).deriv_eq, LSeries_deriv habs]
  have hsum_u : LSeriesSummable (uDH χ) s := LSeriesSummable_uDH hs1
  have hinv := DInv.LSeries_mul_dinv (uDH χ) uDH_zero uDH_one hK0 hK hu hsσ hsum_u
  have hsum_dinv := DInv.LSeriesSummable_dinv (uDH χ) uDH_zero uDH_one hK0 hK hu hsσ
  have hsum_log : LSeriesSummable (LSeries.logMul (LSeries.delta + uDH χ)) s :=
    LSeriesSummable_logMul_of_lt_re habs'
  have hlogMul : LSeries.logMul (aDH χ) = aDH χ 1 • LSeries.logMul (LSeries.delta + uDH χ) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.logMul]
    · simp only [LSeries.logMul, Pi.smul_apply, smul_eq_mul, aDH_eq_of_ne_zero ha1 hn]; ring
  rw [logDeriv_apply, hd, hlogMul, LSeries_smul, dhL_eq_LSeries hs1, LSeries_aDH_eq ha1]
  unfold cDH
  rw [LSeries_convolution' hsum_log hsum_dinv]
  have hdinv_eq : LSeries (DInv.dinv (uDH χ)) s = (LSeries (LSeries.delta + uDH χ) s)⁻¹ :=
    eq_inv_of_mul_eq_one_right hinv
  rw [hdinv_eq]
  field_simp

theorem LSeriesSummable_cDH {σ K : ℝ} (hK0 : 0 ≤ K) (hK : K < 1)
    (hu : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖uDH χ n‖ * (n : ℝ) ^ (-σ) ≤ K)
    {s : ℂ} (hs1 : 1 < s.re) (hsσ : σ ≤ s.re) : LSeriesSummable (cDH χ) s :=
  (LSeriesSummable_logMul_of_lt_re
    (lt_of_le_of_lt abscissa_delta_add_uDH_le (by exact_mod_cast hs1))).convolution
    (DInv.LSeriesSummable_dinv (uDH χ) uDH_zero uDH_one hK0 hK hu hsσ)

/-! ## The Davenport–Heilbronn function: the prime side on `Re s > 2` -/

theorem norm_uDH_chi5_le (n : ℕ) : ‖uDH chi5 n‖ ≤ 10 / 9 := by
  refine (norm_uDH_le n).trans ?_
  rw [aDH_one_eq chi5_ne_one chi5_isPrimitive, norm_mul]
  have h1 := norm_one_add_rootNumber_chi5_ge
  have h2 := norm_one_add_rootNumber_chi5_inv_ge
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem sum_norm_uDH_chi5_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖uDH chi5 n‖ * (n : ℝ) ^ (-(2 : ℝ)) ≤ 7 / 9 := by
  have hsplit : ∀ n ∈ Finset.Icc 1 N, ‖uDH chi5 n‖ * (n : ℝ) ^ (-(2 : ℝ))
      ≤ 10 / 9 * (if 2 ≤ n then (n : ℝ) ^ (-(2 : ℝ)) else 0) := by
    intro n _
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (norm_uDH_chi5_le n) (by positivity)
    · have : n = 1 ∨ n = 0 := by omega
      rcases this with rfl | rfl <;> simp [uDH]
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [← Finset.mul_sum, ← Finset.sum_filter,
    show (Finset.Icc 1 N).filter (fun n => 2 ≤ n) = Finset.Icc 2 N by
      ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega]
  have := sum_Icc_rpow_neg_two_le N
  nlinarith

/-- **The prime side of the Davenport–Heilbronn function**: on `Re s > 2`,
`dh′(s)/dh(s) = −Σ c(n) n^{−s}` with `c = logMul(δ + u) ⍟ (δ + u)^{−1}`, `u(n) = a(n)/a(1)`. -/
theorem logDeriv_dh_eq {s : ℂ} (hs : 2 < s.re) : logDeriv dh s = -LSeries (cDH chi5) s :=
  logDeriv_dhL_eq chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero (σ := 2) (K := 7 / 9)
    (by norm_num) (by norm_num) sum_norm_uDH_chi5_le (by linarith) hs.le

theorem LSeriesSummable_cDH_chi5 {s : ℂ} (hs : 2 < s.re) : LSeriesSummable (cDH chi5) s :=
  LSeriesSummable_cDH (σ := 2) (K := 7 / 9) (by norm_num) (by norm_num) sum_norm_uDH_chi5_le
    (by linarith) hs.le

/-- `dh` has no zeros on `Re s > 2`: its L-series is invertible there. -/
theorem dh_ne_zero_of_two_lt {s : ℂ} (hs : 2 < s.re) : dh s ≠ 0 := by
  have ha1 := aDH_one_ne_zero chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero
  have hinv := DInv.LSeries_mul_dinv (uDH chi5) uDH_zero uDH_one (σ := 2) (K := 7 / 9) (by norm_num)
    (by norm_num) sum_norm_uDH_chi5_le hs.le (LSeriesSummable_uDH (by linarith))
  show dhL chi5 s ≠ 0
  rw [dhL_eq_LSeries (by linarith), LSeries_aDH_eq ha1]
  exact mul_ne_zero ha1 (left_ne_zero_of_mul_eq_one hinv)

end PsiOmega

#print axioms DInv.convolution_dinv
#print axioms DInv.sum_norm_dinv_le
#print axioms DInv.LSeries_mul_dinv
#print axioms PsiOmega.dhL_eq_LSeries
#print axioms PsiOmega.LSeries_aDH_eq
#print axioms PsiOmega.aDH_one_ne_zero
#print axioms PsiOmega.norm_rootNumber_chi5
#print axioms PsiOmega.re_rootNumber_chi5_ge
#print axioms PsiOmega.rootNumber_chi5_inv_eq_conj
#print axioms PsiOmega.sum_Icc_rpow_neg_two_le
#print axioms PsiOmega.logDeriv_dhL_eq
#print axioms PsiOmega.LSeriesSummable_cDH
#print axioms PsiOmega.sum_norm_uDH_chi5_le
#print axioms PsiOmega.logDeriv_dh_eq
#print axioms PsiOmega.LSeriesSummable_cDH_chi5
#print axioms PsiOmega.dh_ne_zero_of_two_lt
