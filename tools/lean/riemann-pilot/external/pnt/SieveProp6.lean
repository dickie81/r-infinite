/-
# Round 604: Proposition 6, Harman's fundamental theorem in the form used (milestone M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`prop6`). Fix `j`, `J₀`, `Λ₁ ≥ 0`, exponents `a₀ > 0` and `b₀` with `a₀ + b₀ < 0.599L` and
`0.515L < b₀ < L − 1` (`L = 2.333`), and `η > 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a`
mod `q`: let `rt` run over the `j`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω` (taken
at `m = 0`, with `m`-parts `c(0)` at most `Λ₁ log q`) forcing every `rt_i ≥ z₀ = ⌈q^{a₀}⌉` and `∏rt ≤ X' = ⌊q^{b₀}⌋`.
Then `Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))`, `r = ∏rt`, is at most `ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)` in absolute
value, where `A` is the `n ∈ (⌊q^L⌋, ⌊2q^L⌋]` with `n ≡ a` and `B` those prime to `q`.

This is Proposition 6 of `frontier/linnik/SIEVE-ROUTE.md` §5, the last part of §13's M5, built with one tree at the
threshold `X'` for every `r ≤ X'` in place of §5's two cases. The conditions on `a₀` and `b₀` say that the stops fall
in the lower window (`a₀ + b₀ < 0.599L`, `0.515L < b₀`) and that the leaves' remainder is small (`b₀ < L − 1`).

The proof:

* The tree (`SieveDiff.tree_weighted`) runs from `z₀` down to `w = ⌈q^{ε_w}⌉`, `ε_w = c/(2k + 4)`,
  `c = (L − 1 − b₀)/4`, at the threshold `X'`. `SieveStops2.stops2_bound` bounds its stops (`window_lo`,
  `window_hi`).
* `leaf_bound`: at a leaf `d = r∏P ≤ X'`, `SieveDiff.leaf_diff` with the ranges' levels `k + 2j` (`Jw_spec`,
  `SieveLeaf.leaf_gap`) gives `4ζ(k)·#{n : d ∣ n, w-rough}/φ(q) + 4·rem`, and the count is at most `Ψ(X/d, w)`
  (`count_le_psi`).
* `leaves_sum_le`: with `Ψ(X/d, w) ≤ 2X/(d log w)` from `SieveRough.psi_le`, the leaves total at most
  `(4ζ(k)·2X/(φ(q) log w) + 4·rem·X')·Σ_{rt} Σ_P 1/(r∏P)`, and the double sum is `Σ_{rt} 1/r ∏_{w ≤ p < z₀} (1 + 1/p)`
  (`sum_leaves_inv`), bounded by `sum_RT_inv_le` and `SieveRough.evLe_sum_inv`.
* `exists_k`, `main_coef`, `main_term`: an even `k` with `(2k + 4)²ζ(k)` small puts the main terms below
  `ηq^L/(φ(q) log q)`; `rem_le`, `rem_term`: the remainders total at most `q^{L−c}/φ(q)`.

The file imports `SieveStops2.lean`.
-/
import SieveStops2

open Real Finset SieveFamily SieveTree SieveCmp SieveBrun SieveLeaf SieveRanges

namespace SieveProp6

/-! ### The fundamental lemma's remainder -/

theorem geom_nat_le {n : ℕ} (hn : 2 ≤ n) (m : ℕ) : ∑ i ∈ Finset.range (m + 1), n ^ i ≤ 2 * n ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have : 2 * n ^ m ≤ n ^ (m + 1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hn
    calc ∑ i ∈ Finset.range (m + 1), n ^ i + n ^ (m + 1) ≤ 2 * n ^ m + n ^ (m + 1) := by omega
      _ ≤ 2 * n ^ (m + 1) := by omega

theorem sum_choose_le_two_pow (n m : ℕ) : ∑ i ∈ Finset.range (m + 1), n.choose i ≤ 2 ^ n := by
  calc ∑ i ∈ Finset.range (m + 1), n.choose i ≤ ∑ i ∈ Finset.range (m + n + 1), n.choose i :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    _ = ∑ i ∈ Finset.range (n + 1), n.choose i := by
        refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i hi hi' => ?_).symm
        rw [Finset.mem_range] at hi'
        exact Nat.choose_eq_zero_of_lt (by omega)
    _ = 2 ^ n := Nat.sum_range_choose n

/-- `Σ_{i ≤ m} C(n, i) ≤ 2 max(1, n)^m`. -/
theorem sum_choose_le (n m : ℕ) : ∑ i ∈ Finset.range (m + 1), n.choose i ≤ 2 * (max 1 n) ^ m := by
  rcases le_or_gt n 1 with hn | hn
  · rw [max_eq_left hn, one_pow, mul_one]
    calc ∑ i ∈ Finset.range (m + 1), n.choose i ≤ 2 ^ n := sum_choose_le_two_pow n m
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 2 := by norm_num
  · rw [max_eq_right hn.le]
    calc ∑ i ∈ Finset.range (m + 1), n.choose i ≤ ∑ i ∈ Finset.range (m + 1), n ^ i :=
          Finset.sum_le_sum fun i _ => Nat.choose_le_pow n i
      _ ≤ 2 * n ^ m := geom_nat_le (by omega) m

/-- A range has at most `w^{2^{−j}}` primes. -/
theorem card_T_le {w : ℝ} (hw : 1 ≤ w) (J : ℕ) (j : Fin J) :
    ((max 1 (T w J j).card : ℕ) : ℝ) ≤ w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := by
  set A := w ^ ((1 / 2 : ℝ) ^ ((j : ℕ) + 1)) with hA
  have hA2 : A ^ 2 = w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    rw [pow_succ]
    push_cast
    ring
  have h1 : (1 : ℝ) ≤ w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := Real.one_le_rpow hw (by positivity)
  rw [Nat.cast_max, Nat.cast_one]
  refine max_le h1 ?_
  rcases Nat.eq_zero_or_pos (T w J j).card with h0 | hpos
  · rw [h0, Nat.cast_zero]
    linarith
  · have hsub : T w J j ⊆ Finset.Ico 2 ⌈A ^ 2⌉₊ := by
      intro p hp
      obtain ⟨hpp, -, hpA⟩ := mem_rng.1 hp
      exact Finset.mem_Ico.2 ⟨hpp.two_le, Nat.lt_ceil.2 hpA⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hc2 : (T w J j).card + 2 ≤ ⌈A ^ 2⌉₊ := by omega
    have hc3 : ((T w J j).card : ℝ) + 2 ≤ ⌈A ^ 2⌉₊ := by exact_mod_cast hc2
    have hc4 : (⌈A ^ 2⌉₊ : ℝ) < A ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [← hA2]
    linarith

theorem sum_half_pow (J : ℕ) : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j = 2 - 2 * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem sum_mul_half_pow (J : ℕ) :
    ∑ j ∈ Finset.range J, (j : ℝ) * (1 / 2 : ℝ) ^ j = 2 - 2 * ((J : ℝ) + 1) * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

/-- `Σ_{j<J} 2^{−j}(k + 2j) ≤ 2k + 4`. -/
theorem sum_levels_exp_le (J k : ℕ) :
    ∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * ((k : ℝ) + 2 * (j : ℕ)) ≤ 2 * k + 4 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (1 / 2 : ℝ) ^ j * ((k : ℝ) + 2 * j)) J]
  have h1 := sum_half_pow J
  have h2 := sum_mul_half_pow J
  have e : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * ((k : ℝ) + 2 * j) =
      k * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j + 2 * ∑ j ∈ Finset.range J, (j : ℝ) * (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, h1, h2]
  have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := by positivity
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith

/-- The fundamental lemma's remainder at the levels `k + 2j`. -/
noncomputable def rem (w : ℝ) (J k : ℕ) : ℝ :=
  (J + 1) * 1 * ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ)

theorem rem_nonneg (w : ℝ) (J k : ℕ) : 0 ≤ rem w J k := by
  unfold rem
  positivity

/-- The remainder is at most `(J + 1)2^J w^{2k+4}`. -/
theorem rem_le {w : ℝ} (hw : 1 ≤ w) (J k : ℕ) :
    rem w J k ≤ (J + 1) * 2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ) := by
  unfold rem
  have hw0 : 0 < w := by linarith
  have h1 : ∀ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ) ≤
      2 * (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (k + 2 * (j : ℕ)) := by
    intro j
    have h := sum_choose_le (T w J j).card (k + 2 * (j : ℕ))
    have h' : ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ) ≤
        2 * ((max 1 (T w J j).card : ℕ) : ℝ) ^ (k + 2 * (j : ℕ)) := by exact_mod_cast h
    refine h'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (card_T_le hw J j) _)
      (by norm_num))
  have h2 : ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ) ≤
      ∏ j : Fin J, 2 * (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (k + 2 * (j : ℕ)) :=
    Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun i _ => by positivity) fun j _ => h1 j
  have h3 : ∏ j : Fin J, 2 * (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (k + 2 * (j : ℕ)) =
      2 ^ J * w ^ (∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * ((k : ℝ) + 2 * (j : ℕ))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.rpow_sum_of_pos hw0]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
    push_cast
    ring_nf
  have h4 : w ^ (∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * ((k : ℝ) + 2 * (j : ℕ))) ≤ w ^ ((2 * k + 4 : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hw
    push_cast
    exact sum_levels_exp_le J k
  calc ((J : ℝ) + 1) * 1 * ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ)
      ≤ ((J : ℝ) + 1) * 1 * (2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h2.trans (h3.le.trans (mul_le_mul_of_nonneg_left h4 (by positivity))))
          (by positivity)
    _ = (J + 1) * 2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ) := by ring

/-- The number of ranges, `J = 2⌊log₂ w⌋ + 2`. -/
def Jw (w : ℕ) : ℕ := 2 * Nat.log 2 w + 2

/-- `J = Jw w` covers the primes below `w` (`w^{2^{−J}} ≤ 2`), with `2^J ≤ 4w²` and `J + 1 ≤ 3w`. -/
theorem Jw_spec {w : ℕ} (hw : 2 ≤ w) :
    (w : ℝ) ^ ((1 / 2 : ℝ) ^ Jw w) ≤ 2 ∧ (2 : ℝ) ^ Jw w ≤ 4 * (w : ℝ) ^ 2 ∧ (Jw w : ℝ) + 1 ≤ 3 * w := by
  have hl1 : w < 2 ^ (Nat.log 2 w + 1) := Nat.lt_pow_succ_log_self (by norm_num) w
  have hl2 : 2 ^ Nat.log 2 w ≤ w := Nat.pow_log_le_self 2 (by omega)
  have hl3 : Nat.log 2 w < w := Nat.log_lt_self 2 (by omega)
  have hw0 : (0 : ℝ) < w := by positivity
  have hw2 : (2 : ℝ) ≤ w := by exact_mod_cast hw
  refine ⟨?_, ?_, ?_⟩
  · have hpow : (w : ℝ) ^ 2 < (2 : ℝ) ^ Jw w := by
      have h : (w : ℝ) < 2 ^ (Nat.log 2 w + 1) := by exact_mod_cast hl1
      have e : (2 : ℝ) ^ Jw w = (2 ^ (Nat.log 2 w + 1)) ^ 2 := by unfold Jw; ring
      rw [e]
      exact pow_lt_pow_left₀ h hw0.le (by norm_num)
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlogw : Real.log w ≤ (w : ℝ) ^ 2 * Real.log 2 := by
      have h1 := Real.log_le_sub_one_of_pos hw0
      nlinarith
    have hexp : (1 / 2 : ℝ) ^ Jw w * Real.log w ≤ Real.log 2 := by
      rw [one_div_pow, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      have hl2pos : 0 < Real.log 2 := by linarith
      nlinarith
    calc (w : ℝ) ^ ((1 / 2 : ℝ) ^ Jw w) = Real.exp ((1 / 2 : ℝ) ^ Jw w * Real.log w) := by
          rw [Real.rpow_def_of_pos hw0, mul_comm]
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hexp
      _ = 2 := Real.exp_log (by norm_num)
  · have e : (2 : ℝ) ^ Jw w = 4 * ((2 : ℝ) ^ Nat.log 2 w) ^ 2 := by unfold Jw; ring
    rw [e]
    have : ((2 : ℝ) ^ Nat.log 2 w) ≤ w := by exact_mod_cast hl2
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ Nat.log 2 w := by positivity
    nlinarith
  · unfold Jw
    have : (Nat.log 2 w : ℝ) + 1 ≤ w := by exact_mod_cast hl3
    push_cast
    linarith

/-! ### A leaf -/

/-- `ζ(k) = e^{2C₀}·(2C₀^k/k!)·exp(e^{2C₀}·2C₀^{k+1}/(k+1)!)`, the fundamental lemma's relative error at the
levels `k + 2j` (`SieveLeaf.leaf_gap`). -/
noncomputable def zeta (C₀ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (2 * C₀) * (2 * (C₀ ^ k / k.factorial)) *
    Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (k + 1) / (k + 1).factorial)))

theorem zeta_nonneg {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (k : ℕ) : 0 ≤ zeta C₀ k := by
  unfold zeta
  positivity

/-- The multiples of `d` in `(⌊X⌋, ⌊2X⌋]` with no prime factor below `w` are at most `Ψ(X/d, w)`. -/
theorem count_le_psi {X : ℝ} (hX : 0 ≤ X) {d w : ℕ} (hd : 0 < d) :
    ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => d ∣ n ∧ rough w n)).card ≤ SieveRough.Psi (X / d) w := by
  unfold SieveRough.Psi SieveRough.roughSet
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine Finset.card_le_card_of_injOn (fun n => n / d) ?_ ?_
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩, hr⟩ := hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    show (⌊X / d⌋₊ < d * m / d ∧ d * m / d ≤ ⌊2 * (X / d)⌋₊) ∧ ∀ p ∈ (d * m / d).primeFactors, w ≤ p
    rw [Nat.mul_div_cancel_left m hd]
    have h1' : X < ((d * m : ℕ) : ℝ) := (Nat.floor_lt hX).1 h1
    have h2' : ((d * m : ℕ) : ℝ) ≤ 2 * X := (Nat.le_floor_iff (by positivity)).1 h2
    push_cast at h1' h2'
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.floor_lt (by positivity), div_lt_iff₀ hd']
      linarith
    · rw [Nat.le_floor_iff (by positivity), mul_div_assoc', le_div_iff₀ hd']
      linarith
    · intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpm, -⟩ := hp
      by_contra hlt
      exact hr p (not_le.1 hlt) hpp (dvd_mul_of_dvd_right hpm d)
  · intro n hn n' hn' h
    rw [Finset.mem_coe, Finset.mem_filter] at hn hn'
    have := congrArg (· * d) h
    simp only at this
    rwa [Nat.div_mul_cancel hn.2.1, Nat.div_mul_cancel hn'.2.1] at this

/-- **A leaf.** For `a` a unit, `d > 0` with every prime factor at least `w ≥ 1`, the ranges with
`w^{2^{−J}} ≤ 2`, and levels `k + 2j` with `k ≥ 1` even, `2C₀² ≤ (k + 1)(k + 2)` and `ζ(k) ≤ 1/2`: the `n ∈ (N₁, N₂]`
with `d ∣ n` and no prime factor below `w` have `|A − B/φ(q)| ≤ 4ζ(k)·#{n : d ∣ n, w-rough}/φ(q) + 4·rem`. -/
theorem leaf_bound {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {d N₁ N₂ w : ℕ} (hd : 0 < d) (hw : 1 ≤ w)
    (hdw : ∀ p : ℕ, p.Prime → p ∣ d → w ≤ p) {J : ℕ} (hJ : (w : ℝ) ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (hN : N₁ ≤ N₂)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k)
    (hk1 : 1 ≤ k) (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hζ : zeta C₀ k ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if d ∣ n ∧ rough w n then 1 else 0)‖ ≤
      4 * zeta C₀ k * (((Finset.Ioc N₁ N₂).filter (fun n => d ∣ n ∧ rough w n)).card : ℝ) / q.totient +
        4 * rem w J k := by
  have hq : 0 < q := NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hζ0 := zeta_nonneg hC₀ k
  have hR0 := rem_nonneg (w : ℝ) J k
  have hcnt0 : (0 : ℝ) ≤ (((Finset.Ioc N₁ N₂).filter (fun n => d ∣ n ∧ rough w n)).card : ℝ) := Nat.cast_nonneg _
  have hRHS : 0 ≤ 4 * zeta C₀ k * (((Finset.Ioc N₁ N₂).filter (fun n => d ∣ n ∧ rough w n)).card : ℝ) /
      q.totient + 4 * rem w J k := by positivity
  by_cases hcop : Nat.Coprime d q
  · rw [SieveDiff.sum_dw_eq]
    have ha' : Nat.Coprime a.val q := (ZMod.isUnit_iff_coprime a.val q).1 (by rw [ZMod.natCast_zmod_val]; exact ha)
    have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have hdw' : ∀ p : ℕ, p.Prime → p ∣ d → (w : ℝ) ≤ p := fun p hp hpd => by exact_mod_cast hdw p hp hpd
    have hkk : ∀ j : Fin J, Even (k + 2 * (j : ℕ)) := fun j => by
      rcases hk with ⟨r, hr⟩; exact ⟨r + j, by omega⟩
    have hkk1 : ∀ j : Fin J, 1 ≤ k + 2 * (j : ℕ) := fun j => by omega
    have hA := leaf_A hq ha' hd hcop hw' hdw' hJ hN (fun j => k + 2 * (j : ℕ)) hkk hkk1
    have hB := leaf_B hq hd hcop hw' hdw' hJ hN (fun j => k + 2 * (j : ℕ)) hkk hkk1
    have hG := leaf_gap hw' J q hC₀ hC hk hkC
    rw [Nat.ceil_natCast] at hA hB
    beta_reduce at hA hB
    set A := (#{n ∈ Ioc N₁ N₂ | n ≡ a.val [MOD q] ∧ d ∣ n ∧ ∀ p < w, p.Prime → ¬ p ∣ n} : ℕ) with hAdef
    set B := (#{n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ d ∣ n ∧ ∀ p < w, p.Prime → ¬ p ∣ n} : ℕ) with hBdef
    have hAeq : ((Ioc N₁ N₂).filter (fun n => n ≡ a.val [MOD q] ∧ (d ∣ n ∧ rough w n))).card = A := rfl
    have hBeq : ((Ioc N₁ N₂).filter (fun n => Nat.Coprime n q ∧ (d ∣ n ∧ rough w n))).card = B := rfl
    rw [hAeq, hBeq]
    have hreal : ((A : ℂ) - (B : ℂ) / q.totient) = (((A : ℝ) - (B : ℝ) / q.totient : ℝ) : ℂ) := by push_cast; ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    set cnt := (((Finset.Ioc N₁ N₂).filter (fun n => d ∣ n ∧ rough w n)).card : ℝ) with hcnt
    have hBcnt : (B : ℝ) ≤ cnt := by
      have : B ≤ ((Finset.Ioc N₁ N₂).filter (fun n => d ∣ n ∧ rough w n)).card := by
        rw [hBdef]
        refine Finset.card_le_card fun n hn => ?_
        rw [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, hn.2.2⟩
      rw [hcnt]
      exact_mod_cast this
    set X := ((N₂ : ℝ) - N₁) / (d * q) with hX
    have hX0 : 0 ≤ X := by
      have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
      rw [hX]
      positivity
    set V := ∏ j : Fin J, ∏ p ∈ T w J j, (1 - g q p) with hV
    have hV0 : 0 ≤ V := Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun p hp =>
      sub_nonneg.2 (g_le_one (prime_of_mem_T hp).one_lt.le)
    set G := ∑ j : Fin J, esym (T w J j) (g q) (k + 2 * (j : ℕ)) *
      ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k + 2 * (i : ℕ)) with hGdef
    set R := rem w J k with hRdef
    have hR : R = (J + 1) * 1 * ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1),
        ((T w J j).card.choose i : ℝ) := rfl
    rw [← hR] at hA hB
    set ζ := zeta C₀ k with hζdef
    have hG' : G ≤ V * ζ := hG
    have hXG : X * G ≤ X * V * ζ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hG' hX0
    have hXV0 : 0 ≤ X * V := mul_nonneg hX0 hV0
    have hhalf : X * V * ζ ≤ X * V * (1 / 2) := mul_le_mul_of_nonneg_left hζ hXV0
    have hB1 := (abs_le.1 hB).1
    have hXV : X * V ≤ 2 * ((B : ℝ) / q.totient + R) := by linarith
    have htri : |(A : ℝ) - (B : ℝ) / q.totient| ≤ |(A : ℝ) - X * V| + |(B : ℝ) / q.totient - X * V| := by
      have e : (A : ℝ) - (B : ℝ) / q.totient = ((A : ℝ) - X * V) - ((B : ℝ) / q.totient - X * V) := by ring
      rw [e]
      exact abs_sub _ _
    have hfin : |(A : ℝ) - (B : ℝ) / q.totient| ≤ 2 * (X * G + R) := by linarith
    have hB' : (B : ℝ) / q.totient ≤ cnt / q.totient := div_le_div_of_nonneg_right hBcnt hφ.le
    have hζB : ζ * ((B : ℝ) / q.totient) ≤ ζ * (cnt / q.totient) := mul_le_mul_of_nonneg_left hB' hζ0
    have hζXV : X * V * ζ ≤ 2 * ((B : ℝ) / q.totient + R) * ζ := mul_le_mul_of_nonneg_right hXV hζ0
    have hζR : ζ * R ≤ (1 / 2) * R := mul_le_mul_of_nonneg_right hζ hR0
    have e4 : 4 * ζ * cnt / q.totient = 4 * (ζ * (cnt / q.totient)) := by ring
    rw [e4]
    nlinarith
  · have hzero : ∀ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if d ∣ n ∧ rough w n then 1 else 0) = 0 := by
      intro n _
      by_cases hn : d ∣ n ∧ rough w n
      · have hnc : ¬ Nat.Coprime n q := fun h => hcop (Nat.Coprime.coprime_dvd_left hn.1 h)
        have hnu : ¬ IsUnit (n : ZMod q) := fun h => hnc ((ZMod.isUnit_iff_coprime n q).1 h)
        have hna : (n : ZMod q) ≠ a := fun h => hnu (h ▸ ha)
        simp [dw, hn, hnu, hna]
      · simp [hn]
    rw [Finset.sum_eq_zero hzero, norm_zero]
    exact hRHS

/-! ### The sums of `1/d` over the leaves -/

/-- `Σ_{rt} Σ_{P ⊆ T} 1/(r∏P) = (Σ_{rt} 1/r)·∏_{p∈T}(1 + 1/p)`. -/
theorem sum_leaves_inv {j : ℕ} (RT : Finset (Fin j → ℕ)) (T : Finset ℕ) :
    ∑ rt ∈ RT, ∑ P ∈ T.powerset, 1 / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) =
      (∑ rt ∈ RT, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ T, (1 + 1 / (p : ℝ)) := by
  rw [Finset.prod_one_add, Finset.sum_mul]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one, one_div_mul_one_div]

/-- `Σ_{rt} 1/∏rt ≤ (Σ_{p∈s} 1/p)^j` over tuples with entries in `s`. -/
theorem sum_RT_inv_le {j : ℕ} {RT : Finset (Fin j → ℕ)} {s : Finset ℕ}
    (hRT : RT ⊆ Fintype.piFinset (fun _ : Fin j => s)) :
    ∑ rt ∈ RT, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ (∑ p ∈ s, 1 / (p : ℝ)) ^ j := by
  have h : ∀ rt : Fin j → ℕ, 1 / ((∏ i, rt i : ℕ) : ℝ) = ∏ i, 1 / (rt i : ℝ) := fun rt => by
    push_cast
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
  calc ∑ rt ∈ RT, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ ∑ rt ∈ Fintype.piFinset (fun _ : Fin j => s),
        1 / ((∏ i, rt i : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hRT fun rt _ _ => by positivity
    _ = ∑ rt ∈ Fintype.piFinset (fun _ : Fin j => s), ∏ i, 1 / (rt i : ℝ) :=
        Finset.sum_congr rfl fun rt _ => h rt
    _ = ∏ _i : Fin j, ∑ p ∈ s, 1 / (p : ℝ) := (Finset.prod_univ_sum (fun _ => s) (fun _ p => 1 / (p : ℝ))).symm
    _ = (∑ p ∈ s, 1 / (p : ℝ)) ^ j := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The leaves of the tree -/

/-- **The leaves.** The leaves of Buchstab's tree at the threshold `X'` (`SieveDiff.tree_weighted` with `r = ∏rt`),
summed over `rt`, are at most `(4ζ(k)B_ψ/φ(q) + 4·rem·X')·Σ_{rt}Σ_{P}1/(r∏P)`, given `Ψ(X/d, w) ≤ B_ψ/d` for
`d ≤ X'`. -/
theorem leaves_sum_le {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {X : ℝ} (hX : 0 ≤ X) {w z₀ X' J k : ℕ}
    {C₀ : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z₀) (hJ : (w : ℝ) ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ rng A, 1 / (p : ℝ) ≤ C₀) (hk : Even k) (hk1 : 1 ≤ k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) (hζ : zeta C₀ k ≤ 1 / 2) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hpsi : ∀ d : ℕ, 0 < d → d ≤ X' → (SieveRough.Psi (X / d) w : ℝ) ≤ Bψ / d)
    {j : ℕ} (RT : Finset (Fin j → ℕ)) (hRT : ∀ rt ∈ RT, (∀ i, (rt i).Prime) ∧ ∀ i, z₀ ≤ rt i) :
    ‖∑ rt ∈ RT, ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
        (if (∏ i, rt i) * ∏ p ∈ P, p ≤ X' then ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, dw q a n *
          (if (∏ i, rt i) * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0)‖ ≤
      (4 * zeta C₀ k * Bψ / q.totient + 4 * rem w J k * X') *
        ((∑ rt ∈ RT, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) := by
  have hq : 0 < q := NeZero.pos q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hζ0 := zeta_nonneg hC₀ k
  have hR0 := rem_nonneg (w : ℝ) J k
  set K := 4 * zeta C₀ k * Bψ / q.totient + 4 * rem w J k * X' with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  rw [← sum_leaves_inv, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun rt hrt => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P hP => ?_)
  obtain ⟨hrtp, hrtz⟩ := hRT rt hrt
  have hPs : P ⊆ primesIco w z₀ := Finset.mem_powerset.1 hP
  have hd0 : 0 < (∏ i, rt i) * ∏ p ∈ P, p :=
    Nat.mul_pos (Finset.prod_pos fun i _ => (hrtp i).pos)
      (Finset.prod_pos fun p hp => (mem_primesIco.1 (hPs hp)).2.2.pos)
  have hd0' : (0 : ℝ) < (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) := by exact_mod_cast hd0
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  by_cases hdX : (∏ i, rt i) * ∏ p ∈ P, p ≤ X'
  · rw [ite_eq_left hdX]
    have hdw : ∀ p : ℕ, p.Prime → p ∣ (∏ i, rt i) * ∏ p ∈ P, p → w ≤ p := by
      intro ℓ hℓ hd
      rcases (Nat.Prime.dvd_mul hℓ).1 hd with h | h
      · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h
        rw [(Nat.prime_dvd_prime_iff_eq hℓ (hrtp i)).1 hi]
        exact le_trans hwz (hrtz i)
      · obtain ⟨ℓ', hℓ', hd'⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h
        have hm := mem_primesIco.1 (hPs hℓ')
        rw [(Nat.prime_dvd_prime_iff_eq hℓ hm.2.2).1 hd']
        exact hm.1
    have hN : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_le_floor (by linarith)
    have hleaf := leaf_bound ha hd0 hw hdw hJ hN hC₀ hC hk hk1 hkC hζ
    have hcnt := count_le_psi hX (w := w) hd0
    have hcntR : (((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
        (fun n => (∏ i, rt i) * ∏ p ∈ P, p ∣ n ∧ rough w n)).card : ℝ) ≤
        Bψ / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) :=
      le_trans (by exact_mod_cast hcnt) (hpsi _ hd0 hdX)
    have hdX' : (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) ≤ X' := by exact_mod_cast hdX
    refine hleaf.trans ?_
    have e : K * (1 / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ)) =
        4 * zeta C₀ k * (Bψ / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ)) / q.totient +
          4 * rem w J k * (X' / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ)) := by
      rw [hK]; field_simp
    rw [e]
    have h1 : 4 * zeta C₀ k * (((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
        (fun n => (∏ i, rt i) * ∏ p ∈ P, p ∣ n ∧ rough w n)).card : ℝ) / q.totient ≤
        4 * zeta C₀ k * (Bψ / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ)) / q.totient :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcntR (by positivity)) hφ.le
    have h2 : 4 * rem w J k ≤ 4 * rem w J k * (X' / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ)) := by
      have : 1 ≤ (X' : ℝ) / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) := by
        rw [le_div_iff₀ hd0', one_mul]; exact hdX'
      nlinarith
    linarith
  · rw [ite_eq_right hdX, norm_zero]
    positivity

/-! ### The level `k` -/

theorem sq_le_four_pow (k : ℕ) : (((2 * k + 4 : ℕ) : ℝ)) ^ 2 ≤ 16 * 4 ^ k := by
  have h1 : k + 2 ≤ 2 ^ (k + 1) := by
    have := Nat.lt_two_pow_self (n := k + 1)
    omega
  have h2 : ((k : ℝ) + 2) ≤ 2 ^ (k + 1) := by exact_mod_cast h1
  have h3 : (((2 * k + 4 : ℕ) : ℝ)) = 2 * ((k : ℝ) + 2) := by push_cast; ring
  rw [h3, mul_pow, show (16 : ℝ) * 4 ^ k = 2 ^ 2 * (2 ^ (k + 1)) ^ 2 by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 2) (by norm_num)

/-- There is an even `k ≥ 2` with `2C₀² ≤ (k + 1)(k + 2)`, `ζ(k) ≤ 1/2`, `(2k + 4)²ζ(k) ≤ ε` and
`c < (2k + 4)a₀`. -/
theorem exists_k {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {ε c a₀ : ℝ} (hε : 0 < ε) (ha₀ : 0 < a₀) :
    ∃ k : ℕ, Even k ∧ 2 ≤ k ∧ 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2) ∧ zeta C₀ k ≤ 1 / 2 ∧
      (((2 * k + 4 : ℕ) : ℝ)) ^ 2 * zeta C₀ k ≤ ε ∧ c < ((2 * k + 4 : ℕ) : ℝ) * a₀ := by
  set M : ℝ := 32 * Real.exp (2 * C₀ + 1) with hM
  have hM0 : 0 < M := by positivity
  set ε' : ℝ := min ε (1 / 8) / M with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hF := FloorSemiring.tendsto_pow_div_factorial_atTop (4 * C₀)
  have hG := (FloorSemiring.tendsto_pow_div_factorial_atTop C₀).comp (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hF.eventually (ge_mem_nhds hε'0))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (hG.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp (2 * C₀)) by positivity)))
  set m : ℕ := max (max N₁ N₂) (max (⌈2 * C₀ ^ 2⌉₊ + 1) (⌈c / a₀⌉₊ + 1)) with hm
  have hN1m : N₁ ≤ m := le_trans (le_max_left N₁ N₂) (le_max_left _ _)
  have hN2m : N₂ ≤ m := le_trans (le_max_right N₁ N₂) (le_max_left _ _)
  have hCm : ⌈2 * C₀ ^ 2⌉₊ + 1 ≤ m := le_trans (le_max_left _ (⌈c / a₀⌉₊ + 1)) (le_max_right _ _)
  have hcm : ⌈c / a₀⌉₊ + 1 ≤ m := le_trans (le_max_right (⌈2 * C₀ ^ 2⌉₊ + 1) _) (le_max_right _ _)
  refine ⟨2 * m, ⟨m, by ring⟩, by omega, ?_, ?_⟩
  · have h1 : (⌈2 * C₀ ^ 2⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hCm
    have h2 := Nat.le_ceil (2 * C₀ ^ 2)
    push_cast
    nlinarith
  have hk1 : N₁ ≤ 2 * m := by omega
  have hk2 : N₂ ≤ 2 * m := by omega
  have hF' : (4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ) ≤ ε' := hN₁ _ hk1
  have hG' : C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤ 1 / (2 * Real.exp (2 * C₀)) := hN₂ _ hk2
  -- the bound `(2k + 4)²ζ(k) ≤ M·(4C₀)^k/k!`
  have hexp : Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)))) ≤
      Real.exp 1 := by
    apply Real.exp_le_exp.2
    have he : 0 < Real.exp (2 * C₀) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_left hG' (show (0 : ℝ) ≤ 2 * Real.exp (2 * C₀) by positivity)
    rw [mul_one_div_cancel (by positivity)] at this
    linarith
  have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hz : (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 2 * zeta C₀ (2 * m) ≤
      M * ((4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := by
    unfold zeta
    have h1 := sq_le_four_pow (2 * m)
    have h2 : (0 : ℝ) ≤ Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) := by positivity
    calc (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 2 * (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) *
          Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)))))
        ≤ (16 * 4 ^ (2 * m)) * (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) *
          Real.exp 1) := by
          apply mul_le_mul h1 (mul_le_mul_of_nonneg_left hexp h2) (by positivity) (by positivity)
      _ = M * ((4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := by
          rw [hM, mul_pow, Real.exp_add]
          ring
  have hzM : (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 2 * zeta C₀ (2 * m) ≤ min ε (1 / 8) := by
    calc _ ≤ M * ((4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := hz
      _ ≤ M * ε' := mul_le_mul_of_nonneg_left hF' hM0.le
      _ = min ε (1 / 8) := by rw [hε']; field_simp
  have hsq : (16 : ℝ) ≤ (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 2 := by
    have : (4 : ℝ) ≤ ((2 * (2 * m) + 4 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    nlinarith
  have hζ0 := zeta_nonneg hC₀ (2 * m)
  refine ⟨?_, hzM.trans (min_le_left _ _), ?_⟩
  · have := hzM.trans (min_le_right _ _)
    nlinarith
  · have h1 : (⌈c / a₀⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hcm
    have h2 := Nat.le_ceil (c / a₀)
    have h3 : c / a₀ < ((2 * (2 * m) + 4 : ℕ) : ℝ) := by push_cast; linarith
    rwa [div_lt_iff₀ ha₀] at h3

/-! ### The windows of the stops -/

/-- With `q^{L−(0.401L+a₀+b₀)} ≥ 5`: `X'z₀ ≤ N₁` and `q^{0.401L} ≤ ⌊N₁/(X'z₀)⌋`, `z₀ = ⌈q^{a₀}⌉`, `X' = ⌊q^{b₀}⌋`. -/
theorem window_lo {Q : ℝ} (hQ : 1 ≤ Q) {a₀ b₀ : ℝ} (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀)
    (h5 : 5 ≤ Q ^ (2333 / 1000 - (401 / 1000 * (2333 / 1000) + a₀ + b₀))) :
    ⌊Q ^ b₀⌋₊ * ⌈Q ^ a₀⌉₊ ≤ ⌊Q ^ (2333 / 1000 : ℝ)⌋₊ ∧
      Q ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ ((⌊Q ^ (2333 / 1000 : ℝ)⌋₊ / (⌊Q ^ b₀⌋₊ * ⌈Q ^ a₀⌉₊) : ℕ) : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  set s := 401 / 1000 * (2333 / 1000) + a₀ + b₀ with hs
  have hA1 : 1 ≤ Q ^ a₀ := Real.one_le_rpow hQ ha₀
  have hB1 : 1 ≤ Q ^ b₀ := Real.one_le_rpow hQ hb₀
  have hC1 : 1 ≤ Q ^ (401 / 1000 * (2333 / 1000) : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hs1 : 1 ≤ Q ^ s := Real.one_le_rpow hQ (by rw [hs]; positivity)
  have hX' : (⌊Q ^ b₀⌋₊ : ℝ) ≤ Q ^ b₀ := Nat.floor_le (by positivity)
  have hz₀ : (⌈Q ^ a₀⌉₊ : ℝ) ≤ 2 * Q ^ a₀ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Q ^ a₀ by positivity)
    linarith
  have hc : (⌈Q ^ (401 / 1000 * (2333 / 1000) : ℝ)⌉₊ : ℝ) ≤ 2 * Q ^ (401 / 1000 * (2333 / 1000) : ℝ) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Q ^ (401 / 1000 * (2333 / 1000) : ℝ) by positivity)
    linarith
  have hprod : Q ^ (401 / 1000 * (2333 / 1000) : ℝ) * Q ^ a₀ * Q ^ b₀ = Q ^ s := by
    rw [hs, Real.rpow_add hQ0, Real.rpow_add hQ0]
  have hL : Q ^ (2333 / 1000 : ℝ) = Q ^ s * Q ^ (2333 / 1000 - s) := by
    rw [← Real.rpow_add hQ0]; ring_nf
  have hN₁ : Q ^ (2333 / 1000 : ℝ) - 1 < (⌊Q ^ (2333 / 1000 : ℝ)⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  -- the key inequality `⌈q^{0.401L}⌉·X'z₀ ≤ N₁`
  have hkey : ⌈Q ^ (401 / 1000 * (2333 / 1000) : ℝ)⌉₊ * (⌊Q ^ b₀⌋₊ * ⌈Q ^ a₀⌉₊) ≤ ⌊Q ^ (2333 / 1000 : ℝ)⌋₊ := by
    have h1 : ((⌈Q ^ (401 / 1000 * (2333 / 1000) : ℝ)⌉₊ * (⌊Q ^ b₀⌋₊ * ⌈Q ^ a₀⌉₊) : ℕ) : ℝ) ≤ 4 * Q ^ s := by
      push_cast
      calc (⌈Q ^ (401 / 1000 * (2333 / 1000) : ℝ)⌉₊ : ℝ) * ((⌊Q ^ b₀⌋₊ : ℝ) * (⌈Q ^ a₀⌉₊ : ℝ))
          ≤ (2 * Q ^ (401 / 1000 * (2333 / 1000) : ℝ)) * (Q ^ b₀ * (2 * Q ^ a₀)) := by
            apply mul_le_mul hc (mul_le_mul hX' hz₀ (by positivity) (by positivity)) (by positivity)
              (by positivity)
        _ = 4 * (Q ^ (401 / 1000 * (2333 / 1000) : ℝ) * Q ^ a₀ * Q ^ b₀) := by ring
        _ = 4 * Q ^ s := by rw [hprod]
    have h2 : 4 * Q ^ s ≤ (⌊Q ^ (2333 / 1000 : ℝ)⌋₊ : ℝ) := by
      have : 5 * Q ^ s ≤ Q ^ (2333 / 1000 : ℝ) := by
        rw [hL]; nlinarith
      linarith
    exact_mod_cast h1.trans h2
  have hD0 : 0 < ⌊Q ^ b₀⌋₊ * ⌈Q ^ a₀⌉₊ := Nat.mul_pos (Nat.floor_pos.2 hB1) (Nat.ceil_pos.2 (by positivity))
  have hc1 : 1 ≤ ⌈Q ^ (401 / 1000 * (2333 / 1000) : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.2
    (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (by positivity)))
  refine ⟨le_trans (Nat.le_mul_of_pos_left _ hc1) hkey, ?_⟩
  have h3 : ⌈Q ^ (401 / 1000 * (2333 / 1000) : ℝ)⌉₊ ≤ ⌊Q ^ (2333 / 1000 : ℝ)⌋₊ / (⌊Q ^ b₀⌋₊ * ⌈Q ^ a₀⌉₊) :=
    (Nat.le_div_iff_mul_le hD0).2 hkey
  exact le_trans (Nat.le_ceil _) (by exact_mod_cast h3)

/-- With `q^{0.485L−(L−b₀)} ≥ 2`: `⌊N₂/(X' + 1)⌋ ≤ q^{0.485L}`, `X' = ⌊q^{b₀}⌋`, `N₂ = ⌊2q^L⌋`. -/
theorem window_hi {Q : ℝ} (hQ : 1 ≤ Q) {b₀ : ℝ} (h2 : 2 ≤ Q ^ (485 / 1000 * (2333 / 1000) - (2333 / 1000 - b₀))) :
    ((⌊2 * Q ^ (2333 / 1000 : ℝ)⌋₊ / (⌊Q ^ b₀⌋₊ + 1) : ℕ) : ℝ) ≤ Q ^ (485 / 1000 * (2333 / 1000) : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hB : Q ^ b₀ < (⌊Q ^ b₀⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hB0 : 0 < Q ^ b₀ := by positivity
  have hN₂ : (⌊2 * Q ^ (2333 / 1000 : ℝ)⌋₊ : ℝ) ≤ 2 * Q ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)
  have hsplit : Q ^ (2333 / 1000 : ℝ) = Q ^ b₀ * Q ^ (2333 / 1000 - b₀) := by
    rw [← Real.rpow_add hQ0]; ring_nf
  have hsplit2 : Q ^ (485 / 1000 * (2333 / 1000) : ℝ) =
      Q ^ (485 / 1000 * (2333 / 1000) - (2333 / 1000 - b₀)) * Q ^ (2333 / 1000 - b₀) := by
    rw [← Real.rpow_add hQ0]; ring_nf
  have hpos : (0 : ℝ) < (⌊Q ^ b₀⌋₊ : ℝ) + 1 := by positivity
  calc ((⌊2 * Q ^ (2333 / 1000 : ℝ)⌋₊ / (⌊Q ^ b₀⌋₊ + 1) : ℕ) : ℝ)
      ≤ (⌊2 * Q ^ (2333 / 1000 : ℝ)⌋₊ : ℝ) / ((⌊Q ^ b₀⌋₊ : ℝ) + 1) := by
        have := Nat.cast_div_le (α := ℝ) (m := ⌊2 * Q ^ (2333 / 1000 : ℝ)⌋₊) (n := ⌊Q ^ b₀⌋₊ + 1)
        push_cast at this
        exact this
    _ ≤ 2 * Q ^ (2333 / 1000 : ℝ) / Q ^ b₀ := by
        apply div_le_div₀ (by positivity) hN₂ hB0 hB.le
    _ = 2 * Q ^ (2333 / 1000 - b₀) := by rw [hsplit]; field_simp
    _ ≤ Q ^ (485 / 1000 * (2333 / 1000) : ℝ) := by
        rw [hsplit2]
        exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-! ### Arithmetic of the error terms -/

/-- The main term's coefficient: with `ε_w = c/(2k + 4)` and `(2k + 4)²Z ≤ ηc²/(8E(K₁ + 1)a₀)`, the coefficient
`8EK₁a₀Z/ε_w²` is at most `η`. -/
theorem main_coef {E K₁ a₀ Z εw c η : ℝ} {k : ℕ} (hE : 0 < E) (hK₁ : 0 ≤ K₁) (ha₀ : 0 < a₀) (hc : 0 < c)
    (hη : 0 < η) (hεw : εw = c / ((2 * k + 4 : ℕ) : ℝ))
    (hζε : ((2 * k + 4 : ℕ) : ℝ) ^ 2 * Z ≤ η * c ^ 2 / (8 * E * (K₁ + 1) * a₀)) :
    8 * E * K₁ * a₀ * Z / εw ^ 2 ≤ η := by
  have hk4 : (0 : ℝ) < ((2 * k + 4 : ℕ) : ℝ) := by positivity
  have hA : 8 * E * K₁ * a₀ * Z / εw ^ 2 = 8 * E * K₁ * a₀ * (((2 * k + 4 : ℕ) : ℝ) ^ 2 * Z) / c ^ 2 := by
    rw [hεw]; field_simp
  have hB : 8 * E * K₁ * a₀ * (((2 * k + 4 : ℕ) : ℝ) ^ 2 * Z) / c ^ 2 ≤
      8 * E * K₁ * a₀ * (η * c ^ 2 / (8 * E * (K₁ + 1) * a₀)) / c ^ 2 := by
    gcongr
  have hC : 8 * E * K₁ * a₀ * (η * c ^ 2 / (8 * E * (K₁ + 1) * a₀)) / c ^ 2 = η * (K₁ / (K₁ + 1)) := by
    field_simp
  have hD : η * (K₁ / (K₁ + 1)) ≤ η := by
    have : K₁ / (K₁ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  linarith

/-- The leaves' main term: for `L_w ≥ ε_w L_Q` (in use `L_w = log w`, `L_Q = log q`) and the coefficient
`8EK₁a₀Z/ε_w²` at most `η`, `4Z(2X/L_w)/φ · K₁(Ea₀/ε_w) ≤ ηX/(φL_Q)`. -/
theorem main_term {Z X Lw LQ φ K₁ E a₀ εw η : ℝ} (hZ : 0 ≤ Z) (hX : 0 ≤ X) (hφ : 0 < φ) (hK₁ : 0 ≤ K₁)
    (hE : 0 < E) (ha₀ : 0 < a₀) (hεw : 0 < εw) (hLQ : 0 < LQ) (hlw : εw * LQ ≤ Lw)
    (hcoef : 8 * E * K₁ * a₀ * Z / εw ^ 2 ≤ η) :
    4 * Z * (2 * X / Lw) / φ * (K₁ * (E * a₀ / εw)) ≤ η * X / (φ * LQ) := by
  have hLw : 0 < Lw := lt_of_lt_of_le (mul_pos hεw hLQ) hlw
  have hXw : X / (φ * Lw) ≤ X / (φ * (εw * LQ)) := by
    apply div_le_div_of_nonneg_left hX (by positivity)
    exact mul_le_mul_of_nonneg_left hlw hφ.le
  have e1 : 4 * Z * (2 * X / Lw) / φ * (K₁ * (E * a₀ / εw)) = (8 * E * K₁ * a₀ * Z / εw) * (X / (φ * Lw)) := by
    field_simp
    ring
  have e2 : (8 * E * K₁ * a₀ * Z / εw) * (X / (φ * (εw * LQ))) = (8 * E * K₁ * a₀ * Z / εw ^ 2) * (X / (φ * LQ)) := by
    field_simp
  have hpos : 0 ≤ 8 * E * K₁ * a₀ * Z / εw := by positivity
  have hpos2 : 0 ≤ X / (φ * LQ) := by positivity
  rw [e1]
  calc (8 * E * K₁ * a₀ * Z / εw) * (X / (φ * Lw)) ≤ (8 * E * K₁ * a₀ * Z / εw) * (X / (φ * (εw * LQ))) :=
        mul_le_mul_of_nonneg_left hXw hpos
    _ = (8 * E * K₁ * a₀ * Z / εw ^ 2) * (X / (φ * LQ)) := e2
    _ ≤ η * (X / (φ * LQ)) := mul_le_mul_of_nonneg_right hcoef hpos2
    _ = η * X / (φ * LQ) := by ring

/-- The leaves' remainder: for `1 ≤ w ≤ 2Q^{ε_w}`, `ε_w(2k + 7) ≤ 2c`, `0 ≤ X' ≤ Q^{b₀}`, `2^J ≤ 4w²`,
`J + 1 ≤ 3w`, `48·2^{2k+7}K ≤ Q^c`, `0 < φ ≤ Q`, `L − 1 − c = c + (b₀ + 2c)` and `R ≤ (J + 1)2^J w^{2k+4}`:
`4RX'K ≤ φ⁻¹Q^{L−c}`. -/
theorem rem_term {Q w X' φ K εw c b₀ Mrem R : ℝ} {k J : ℕ} (hQ1 : 1 ≤ Q) (hw1 : 1 ≤ w)
    (hwle : w ≤ 2 * Q ^ εw) (hεw7 : εw * ((2 * k + 7 : ℕ) : ℝ) ≤ 2 * c) (hX' : X' ≤ Q ^ b₀) (hX'0 : 0 ≤ X')
    (hK : 0 ≤ K) (hJ2 : (2 : ℝ) ^ J ≤ 4 * w ^ 2) (hJ3 : (J : ℝ) + 1 ≤ 3 * w)
    (hMrem : Mrem = 48 * 2 ^ (2 * k + 7) * K) (hM : Mrem ≤ Q ^ c) (hφ : 0 < φ) (hφq : φ ≤ Q)
    (hc : (2333 / 1000 - 1 - c : ℝ) = c + (b₀ + 2 * c))
    (hR : R ≤ (J + 1) * 2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ)) : 4 * R * X' * K ≤ φ⁻¹ * Q ^ (2333 / 1000 - c : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hw7 : R ≤ 12 * w ^ (2 * k + 7) := by
    refine hR.trans ?_
    rw [Real.rpow_natCast]
    have h0 : (0 : ℝ) ≤ w ^ (2 * k + 4) := by positivity
    calc ((J : ℝ) + 1) * 2 ^ J * w ^ (2 * k + 4) ≤ (3 * w) * (4 * w ^ 2) * w ^ (2 * k + 4) := by
          apply mul_le_mul (mul_le_mul hJ3 hJ2 (by positivity) (by positivity)) le_rfl h0 (by positivity)
      _ = 12 * w ^ (2 * k + 7) := by ring
  have hwpow : w ^ (2 * k + 7) ≤ 2 ^ (2 * k + 7) * Q ^ (2 * c) := by
    calc w ^ (2 * k + 7) ≤ (2 * Q ^ εw) ^ (2 * k + 7) := pow_le_pow_left₀ (by positivity) hwle _
      _ = 2 ^ (2 * k + 7) * Q ^ (εw * ((2 * k + 7 : ℕ) : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (Q ^ εw), ← Real.rpow_mul hQ0.le]
      _ ≤ 2 ^ (2 * k + 7) * Q ^ (2 * c) := by
          gcongr
  have hstep : 4 * R * X' * K ≤ Mrem * Q ^ (b₀ + 2 * c) := by
    calc 4 * R * X' * K ≤ 4 * (12 * (2 ^ (2 * k + 7) * Q ^ (2 * c))) * Q ^ b₀ * K := by
          gcongr
          exact hw7.trans (by gcongr)
      _ = Mrem * Q ^ (b₀ + 2 * c) := by
          rw [hMrem, Real.rpow_add hQ0]
          ring
  have hfin : Mrem * Q ^ (b₀ + 2 * c) ≤ Q ^ (2333 / 1000 - 1 - c) := by
    rw [hc, Real.rpow_add hQ0 c (b₀ + 2 * c)]
    exact mul_le_mul_of_nonneg_right hM (by positivity)
  have hφinv : Q ^ (2333 / 1000 - 1 - c) ≤ φ⁻¹ * Q ^ (2333 / 1000 - c : ℝ) := by
    have e : Q ^ (2333 / 1000 - c : ℝ) = Q ^ (2333 / 1000 - 1 - c) * Q := by
      rw [← Real.rpow_add_one hQ0.ne']; ring_nf
    rw [e, inv_mul_eq_div, le_div_iff₀ hφ]
    exact mul_le_mul_of_nonneg_left hφq (by positivity)
  linarith

/-! ### Proposition 6 -/

section Prop6

open Classical

set_option maxHeartbeats 1600000 in
/-- **Proposition 6** (Harman's fundamental theorem, in the form used). Fix `j`, `J₀`, `Λ₁ ≥ 0`, exponents `a₀ > 0`
and `b₀` with `a₀ + b₀ < 0.599L` and `0.515L < b₀ < L − 1` (`L = 2.333`), and `η > 0`. There are `δ > 0` and `q₀`
such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `j`-tuples of primes up to `⌊2q^L⌋` that satisfy
at most `J₀` comparisons `Ω` (taken at `m = 0`, with `m`-parts `c(0)` at most `Λ₁ log q`) forcing every
`rt_i ≥ z₀ = ⌈q^{a₀}⌉` and `∏rt ≤ ⌊q^{b₀}⌋`. Then `Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))`, `r = ∏rt`, is at most
`η q^L/(φ(q) log q) + q^{L−δ}/φ(q)` in absolute value. -/
theorem prop6 (j J₀ : ℕ) {Λ₁ a₀ b₀ : ℝ} (hΛ₁ : 0 ≤ Λ₁) (ha₀ : 0 < a₀)
    (hab : a₀ + b₀ < 599 / 1000 * (2333 / 1000)) (hb₁ : 515 / 1000 * (2333 / 1000) < b₀)
    (hb₂ : b₀ < 2333 / 1000 - 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ Ω : List (Cmp j), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∏ i, rt i ≤ ⌊(q : ℝ) ^ b₀⌋₊) →
      ‖∑ rt ∈ SieveStops2.RT j ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ a₀⌉₊ n then 1 else 0)‖ ≤
        η * (q : ℝ) ^ (2333 / 1000 : ℝ) / (q.totient * Real.log q) +
          (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  obtain ⟨C₀, hC₀1, hC⟩ := SieveRanges.rng_sum_le
  have hC₀ : 0 ≤ C₀ := by linarith
  set c : ℝ := (2333 / 1000 - 1 - b₀) / 4 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hb₀ : 0 < b₀ := by linarith
  have ha₀L : a₀ ≤ 2333 / 1000 + 1 := by linarith
  set K₁ : ℝ := (Real.log (2333 / 1000 + 1) - Real.log a₀ + 1) ^ j with hK₁
  have hlogpos : 0 ≤ Real.log (2333 / 1000 + 1) - Real.log a₀ + 1 := by
    have := Real.log_le_log ha₀ ha₀L
    linarith
  have hK₁0 : 0 ≤ K₁ := pow_nonneg hlogpos j
  obtain ⟨k, hkev, hk2, hkC, hζ, hζε, hca⟩ := exists_k hC₀
    (ε := η * c ^ 2 / (8 * Real.exp 1 * (K₁ + 1) * a₀)) (c := c) (by positivity) ha₀
  have hk4 : (0 : ℝ) < ((2 * k + 4 : ℕ) : ℝ) := by positivity
  set εw : ℝ := c / ((2 * k + 4 : ℕ) : ℝ) with hεw
  have hεw0 : 0 < εw := div_pos hc0 hk4
  have hεwa : εw < a₀ := by rw [hεw, div_lt_iff₀ hk4]; linarith
  have hεw7 : εw * ((2 * k + 7 : ℕ) : ℝ) ≤ 2 * c := by
    rw [hεw, div_mul_eq_mul_div, div_le_iff₀ hk4]
    push_cast
    nlinarith
  -- the stops
  obtain ⟨δ₁, hδ₁, q₁, hq₁⟩ := SieveStops2.stops2_bound hεw0 j J₀ hΛ₁
  -- rough numbers from above
  set U : ℝ := (2333 / 1000 + 1) / εw with hU
  obtain ⟨z₁, hz₁⟩ := SieveRough.psi_le U (ε := 1) one_pos
  -- the remainder's constant
  set Mrem : ℝ := 48 * 2 ^ (2 * k + 7) * (K₁ * (Real.exp 1 * a₀ / εw)) with hMrem
  set δ₀ : ℝ := min c δ₁ / 2 with hδ₀
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; exact half_pos (lt_min hc0 hδ₁)
  -- the conditions that hold for large `q`
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 3 ≤ x ∧ max 2 (z₁ : ℝ) ≤ x ^ εw ∧
      ∑ p ∈ SieveRough.primesIn (x ^ εw) (x ^ a₀), 1 / (p : ℝ) ≤ Real.log a₀ - Real.log εw + 1 ∧
      ∑ p ∈ SieveRough.primesIn (x ^ a₀) (x ^ (2333 / 1000 + 1 : ℝ)), 1 / (p : ℝ) ≤
        Real.log (2333 / 1000 + 1) - Real.log a₀ + 1 ∧
      5 ≤ x ^ (2333 / 1000 - (401 / 1000 * (2333 / 1000) + a₀ + b₀)) ∧
      2 ≤ x ^ (485 / 1000 * (2333 / 1000) - (2333 / 1000 - b₀)) ∧
      Mrem ≤ x ^ c ∧ 2 ≤ x ^ δ₀ :=
    (Filter.eventually_ge_atTop 3).and (((tendsto_rpow_atTop hεw0).eventually_ge_atTop _).and
      ((SieveRough.evLe_sum_inv hεw0 hεwa.le 1 one_pos).and ((SieveRough.evLe_sum_inv ha₀ ha₀L 1 one_pos).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      (((tendsto_rpow_atTop hc0).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop hδ₀0).eventually_ge_atTop _)))))))
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ₀, hδ₀0, max q₁ q₂, ?_⟩
  intro q _ hq a ha Ω hΩlen hΩc hΩ
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  obtain ⟨hq3, hQw, hM1, hM2, hW5, hW2, hMrem', hδ2⟩ := hq₂ q (le_trans (le_max_right _ _) hq)
  set Q : ℝ := (q : ℝ) with hQdef
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  set w : ℕ := ⌈Q ^ εw⌉₊ with hwdef
  set z₀ : ℕ := ⌈Q ^ a₀⌉₊ with hz₀def
  set X' : ℕ := ⌊Q ^ b₀⌋₊ with hX'def
  set X : ℝ := Q ^ (2333 / 1000 : ℝ) with hXdef
  set N₁ : ℕ := ⌊X⌋₊ with hN₁
  set N₂ : ℕ := ⌊2 * X⌋₊ with hN₂
  have hX0 : 0 ≤ X := by positivity
  have hεwle : Q ^ εw ≤ w := Nat.le_ceil _
  have hw2R : (2 : ℝ) ≤ w := le_trans (le_trans (le_max_left _ _) hQw) hεwle
  have hw2 : 2 ≤ w := by exact_mod_cast hw2R
  have hw1 : 1 ≤ w := by omega
  have hwz₁ : z₁ ≤ w := by
    have : (z₁ : ℝ) ≤ w := le_trans (le_trans (le_max_right _ _) hQw) hεwle
    exact_mod_cast this
  have hwz : w ≤ z₀ := Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hQ1 hεwa.le)
  have hwle : (w : ℝ) ≤ 2 * Q ^ εw := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ Q ^ εw by positivity)
    have h2 : (1 : ℝ) ≤ Q ^ εw := Real.one_le_rpow hQ1 hεw0.le
    linarith
  have hlogw : εw * Real.log Q ≤ Real.log w := by
    rw [← Real.log_rpow hQ0]
    exact Real.log_le_log (by positivity) hεwle
  have hlogw0 : 0 < Real.log w := lt_of_lt_of_le (mul_pos hεw0 hlogQ) hlogw
  have hX'1 : 1 ≤ X' := Nat.le_floor (by simpa using Real.one_le_rpow hQ1 hb₀.le)
  have hX'le : (X' : ℝ) ≤ Q ^ b₀ := Nat.floor_le (by positivity)
  obtain ⟨hXz, hP₁⟩ := window_lo hQ1 ha₀.le hb₀.le hW5
  have hP₂ := window_hi hQ1 hW2
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφq : (q.totient : ℝ) ≤ Q := Nat.cast_le.2 (Nat.totient_le q)
  have hN₂le : (N₂ : ℝ) ≤ 2 * X := Nat.floor_le (by positivity)
  -- the tuples
  have hRT : ∀ rt ∈ SieveStops2.RT j N₂ Ω, (∀ i, (rt i).Prime) ∧ (∀ i, z₀ ≤ rt i) ∧ ∏ i, rt i ≤ X' := by
    intro rt hrt
    rw [SieveStops2.RT, Finset.mem_filter, Fintype.mem_piFinset] at hrt
    have hp : ∀ i, (rt i).Prime := fun i => (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).2
    exact ⟨hp, (hΩ rt hp hrt.2).1, (hΩ rt hp hrt.2).2⟩
  -- the tree at the threshold `X'`, for each tuple
  have htree := fun rt (hrt : rt ∈ SieveStops2.RT j N₂ Ω) =>
    SieveDiff.tree_weighted (Finset.Ioc N₁ N₂) (dw q a) (r := ∏ i, rt i) (X := X') hwz
      (fun p hp hpd => by
        obtain ⟨hrtp, hrtz, -⟩ := hRT rt hrt
        obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hpd
        rw [(Nat.prime_dvd_prime_iff_eq hp (hrtp i)).1 hi]
        exact hrtz i)
      (hRT rt hrt).2.2
  rw [Finset.sum_congr rfl htree, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans ?_
  -- the stops
  have hstops := hq₁ q hq1 a ha X' w z₀ Ω hΩlen hΩc (fun rt hp hΩ' => (hΩ rt hp hΩ').1) hεwle hwz hX'1 hXz hP₁ hP₂
  -- the leaves
  have hpsi : ∀ d : ℕ, 0 < d → d ≤ X' → (SieveRough.Psi (X / d) w : ℝ) ≤ (2 * X / Real.log w) / d := by
    intro d hd hdX
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hdX' : (d : ℝ) ≤ X := by
      have : Q ^ b₀ ≤ X := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      have : (d : ℝ) ≤ X' := by exact_mod_cast hdX
      linarith
    have hy1 : 1 ≤ X / d := by rw [le_div_iff₀ (by linarith)]; linarith
    have hlog2 : Real.log (2 * (X / d)) ≤ U * Real.log w := by
      have h1 : 2 * (X / d) ≤ Q ^ (2333 / 1000 + 1 : ℝ) := by
        rw [Real.rpow_add hQ0, Real.rpow_one]
        have h1a : X / d ≤ X := div_le_self hX0 hd1
        have h1b : 2 * X ≤ X * Q := by
          rw [mul_comm X Q]
          exact mul_le_mul_of_nonneg_right (by linarith) hX0
        linarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_rpow hQ0] at h2
      have h3 : (2333 / 1000 + 1) * Real.log Q ≤ U * Real.log w := by
        rw [hU, div_mul_eq_mul_div, le_div_iff₀ hεw0]
        have := mul_le_mul_of_nonneg_left hlogw (by norm_num : (0 : ℝ) ≤ 2333 / 1000 + 1)
        linarith
      linarith
    have h := hz₁ w hwz₁ (X / d) hy1 hlog2
    have hω := SieveRough.omegaC_le_one (Real.log (2 * (X / d)) / Real.log w)
    calc (SieveRough.Psi (X / d) w : ℝ) ≤ (SieveCert.omegaC (Real.log (2 * (X / d)) / Real.log w) + 1) *
          (X / d) / Real.log w := h
      _ ≤ 2 * (X / d) / Real.log w := by
          apply div_le_div_of_nonneg_right _ hlogw0.le
          exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hX0 (by positivity))
      _ = (2 * X / Real.log w) / d := by ring
  have hJ := Jw_spec hw2
  have hleaves := leaves_sum_le ha hX0 hw1 hwz hJ.1 hC₀ hC hkev (by omega) hkC hζ
    (by positivity : 0 ≤ 2 * X / Real.log w) hpsi (SieveStops2.RT j N₂ Ω)
    (fun rt hrt => ⟨(hRT rt hrt).1, (hRT rt hrt).2.1⟩)
  -- the sums of `1/d`
  have hsRT : ∑ rt ∈ SieveStops2.RT j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ K₁ := by
    refine (sum_RT_inv_le (s := SieveRough.primesIn (Q ^ a₀) (Q ^ (2333 / 1000 + 1 : ℝ))) ?_).trans ?_
    · intro rt hrt
      rw [Fintype.mem_piFinset]
      intro i
      obtain ⟨hrtp, hrtz, -⟩ := hRT rt hrt
      have hrtY : rt i ≤ N₂ := by
        rw [SieveStops2.RT, Finset.mem_filter, Fintype.mem_piFinset] at hrt
        exact (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).1
      rw [SieveRough.mem_primesIn]
      refine ⟨hrtp i, le_trans (Nat.le_ceil _) (by exact_mod_cast hrtz i), ?_⟩
      have h1 : (rt i : ℝ) ≤ N₂ := by exact_mod_cast hrtY
      have h2 : 2 * X < Q ^ (2333 / 1000 + 1 : ℝ) := by
        rw [Real.rpow_add hQ0, Real.rpow_one, mul_comm X Q]
        exact mul_lt_mul_of_pos_right (by linarith) (by positivity)
      linarith
    · exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => by positivity) hM2 j
  have hsP : ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ)) ≤ Real.exp 1 * a₀ / εw := by
    refine (SieveBrun.prod_one_add_le_exp _ _ fun p _ => by positivity).trans ?_
    have h : ∑ p ∈ primesIco w z₀, 1 / (p : ℝ) ≤ Real.log a₀ - Real.log εw + 1 := hM1
    calc Real.exp (∑ p ∈ primesIco w z₀, 1 / (p : ℝ)) ≤ Real.exp (Real.log a₀ - Real.log εw + 1) :=
          Real.exp_le_exp.2 h
      _ = Real.exp 1 * a₀ / εw := by
          rw [Real.exp_add, Real.exp_sub, Real.exp_log ha₀, Real.exp_log hεw0]
          ring
  have hsum0 : 0 ≤ ∑ rt ∈ SieveStops2.RT j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ) :=
    Finset.sum_nonneg fun rt _ => by positivity
  have hsd : (∑ rt ∈ SieveStops2.RT j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) *
      ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ)) ≤ K₁ * (Real.exp 1 * a₀ / εw) :=
    mul_le_mul hsRT hsP (Finset.prod_nonneg fun p _ => by positivity) hK₁0
  -- the main term
  have hmain : 4 * zeta C₀ k * (2 * X / Real.log w) / q.totient * (K₁ * (Real.exp 1 * a₀ / εw)) ≤
      η * X / (q.totient * Real.log Q) :=
    main_term (zeta_nonneg hC₀ k) hX0 hφ hK₁0 (Real.exp_pos 1) ha₀ hεw0 hlogQ hlogw
      (main_coef (Real.exp_pos 1) hK₁0 ha₀ hc0 hη hεw hζε)
  -- the remainder
  have hrem : 4 * rem w (Jw w) k * X' * (K₁ * (Real.exp 1 * a₀ / εw)) ≤
      (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - c : ℝ) :=
    rem_term hQ1 (by linarith) hwle hεw7 hX'le (Nat.cast_nonneg _) (by positivity) hJ.2.1 hJ.2.2 hMrem hMrem'
      hφ hφq (by rw [hc]; ring) (rem_le (by linarith) (Jw w) k)
  -- combine
  have hL : ‖∑ rt ∈ SieveStops2.RT j N₂ Ω, ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
      (if (∏ i, rt i) * ∏ p ∈ P, p ≤ X' then ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n *
        (if (∏ i, rt i) * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0)‖ ≤
      η * X / (q.totient * Real.log Q) + (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - c : ℝ) := by
    refine hleaves.trans ?_
    have h1 : (4 * zeta C₀ k * (2 * X / Real.log w) / q.totient + 4 * rem w (Jw w) k * X') *
        ((∑ rt ∈ SieveStops2.RT j N₂ Ω, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ primesIco w z₀, (1 + 1 / (p : ℝ))) ≤
        (4 * zeta C₀ k * (2 * X / Real.log w) / q.totient + 4 * rem w (Jw w) k * X') *
          (K₁ * (Real.exp 1 * a₀ / εw)) :=
      mul_le_mul_of_nonneg_left hsd (by have := zeta_nonneg hC₀ k; have := rem_nonneg (w : ℝ) (Jw w) k; positivity)
    refine h1.trans ?_
    rw [add_mul]
    exact add_le_add hmain hrem
  have hcomb : (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - c : ℝ) + (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - δ₁ : ℝ) ≤
      (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - δ₀ : ℝ) := by
    have hm : 2 * δ₀ ≤ c ∧ 2 * δ₀ ≤ δ₁ := by
      rw [hδ₀]; exact ⟨by linarith [min_le_left c δ₁], by linarith [min_le_right c δ₁]⟩
    have h1 : Q ^ (2333 / 1000 - c : ℝ) ≤ Q ^ (2333 / 1000 - 2 * δ₀ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    have h2 : Q ^ (2333 / 1000 - δ₁ : ℝ) ≤ Q ^ (2333 / 1000 - 2 * δ₀ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
    have h3 : 2 * Q ^ (2333 / 1000 - 2 * δ₀ : ℝ) ≤ Q ^ (2333 / 1000 - δ₀ : ℝ) := by
      have e : Q ^ (2333 / 1000 - δ₀ : ℝ) = Q ^ δ₀ * Q ^ (2333 / 1000 - 2 * δ₀ : ℝ) := by
        rw [← Real.rpow_add hQ0]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_right hδ2 (by positivity)
    have hinv : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) hinv
  calc _ ≤ (η * X / (q.totient * Real.log Q) + (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - c : ℝ)) +
        (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - δ₁ : ℝ) := add_le_add hL hstops
    _ ≤ η * X / (q.totient * Real.log Q) + (q.totient : ℝ)⁻¹ * Q ^ (2333 / 1000 - δ₀ : ℝ) := by
        linarith [hcomb]

end Prop6

end SieveProp6
