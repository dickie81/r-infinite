/-
# Round 604: Type II families with sharp prime ranges (milestone M5)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_unw`). Fix `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such
that for `q ≥ q₀` and a unit `a` mod `q`: let `m` run over `S ⊆ (P₁, P₂]` with `q^{0.401L} ≤ P₁` and
`P₂ ≤ q^{0.485L}` (`L = 2.333`), with coefficients `|a_m| ≤ 1`, and let `n + 1 ≤ K₀` primes `x_i` run over all the
primes up to `⌊2q^L⌋`. Let `J ≤ J₀` sharp comparisons `P_j` hold when `ℓ_j = φ_j(m) + Σ_i e_{ji} log x_i > 0` and
imply `ℓ_j ≥ 0`, with `|e_{ji}| ≤ E₀`, `φ_j(m) ≤ Λ₁ log q` on `S`, and for each `j` a pivot `i` with `e_{ji} = ±1`.
If wherever all the comparisons hold each `x_i ≥ 2q^{e₁}` and `m∏_i x_i ≤ 2q^L`, then the family's `|A − B/φ(q)|`
(`SieveFamily.Dsum`) is at most `q^{L−δ}/φ(q)`.

This removes the dyadic weights from `SieveFamily.typeII_sharp`, whose primes carry `f0(x_i/Q_i)` at fixed scales
and whose `m` lies in a dyadic block, so that §13's M5 can use families with sharp ranges.

The proof:

* `blk_spec`: for `P₁ ≥ 1`, `m ∈ (P₁, P₂]` lies in the dyadic block `(P₁2^b, 2P₁2^b]` with `b = log₂((m − 1)/P₁)`.
* `SieveDyadic.sum_bump`: each prime's range is covered by `Σ_k bump(x/2^k) = 1`, so the family is a sum of families
  with weights `bump(x_i/Q_i)` at the scales `Q_i = 2^{k_i}`, and `box_change` puts each one in `Sp`'s ranges.
* `SieveFamily.typeII_sharp` bounds each piece by `q^{L−δ}/φ(q)` (with `f0 = bump`, `F₀ = 1`, `A₀ = 1`). The pieces
  number at most `(3 + 4 log q)^{K₀+1}`, which `ev_log_pow_le` puts below `q^{δ/2}`.

The file imports `SieveFamily.lean` and `SieveDyadic.lean`.
-/
import SieveFamily
import SieveDyadic

open Real Finset Filter Asymptotics SieveFamily

namespace SieveTypeIIU

/-- The primes up to `Y`. -/
def primesLe (Y : ℕ) : Finset ℕ := (Finset.range (Y + 1)).filter Nat.Prime

theorem mem_primesLe {Y p : ℕ} : p ∈ primesLe Y ↔ p ≤ Y ∧ p.Prime := by
  rw [primesLe, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The dyadic block of `m > P₁ ≥ 1`: `b = log₂((m − 1)/P₁)` has `P₁2^b < m ≤ 2P₁2^b`. -/
theorem blk_spec {P₁ m : ℕ} (hP : 1 ≤ P₁) (hm : P₁ < m) :
    P₁ * 2 ^ Nat.log 2 ((m - 1) / P₁) < m ∧ m ≤ 2 * (P₁ * 2 ^ Nat.log 2 ((m - 1) / P₁)) := by
  set t := (m - 1) / P₁ with ht
  have ht1 : 1 ≤ t := by
    rw [ht, Nat.le_div_iff_mul_le (by omega)]; omega
  have h1 : 2 ^ Nat.log 2 t ≤ t := Nat.pow_log_le_self 2 (by omega)
  have h2 : t < 2 ^ (Nat.log 2 t).succ := Nat.lt_pow_succ_log_self (by norm_num) t
  have h3 : P₁ * t ≤ m - 1 := Nat.mul_div_le (m - 1) P₁
  have h4 : m - 1 < P₁ * (t + 1) := by
    rw [ht]; exact Nat.lt_mul_div_succ (m - 1) (by omega)
  constructor
  · exact lt_of_le_of_lt (le_trans (Nat.mul_le_mul_left _ h1) h3) (by omega)
  · have h5 : P₁ * (t + 1) ≤ 2 * (P₁ * 2 ^ Nat.log 2 t) := by
      have := Nat.mul_le_mul_left P₁ (show t + 1 ≤ 2 ^ (Nat.log 2 t).succ by omega)
      rw [pow_succ] at this
      linarith
    generalize P₁ * (t + 1) = B at h4 h5
    generalize P₁ * 2 ^ Nat.log 2 t = A at h5 ⊢
    omega

/-- `Dsum` is additive in the weight. -/
theorem Dsum_sum {X ι : Type*} {q : ℕ} (a : ZMod q) (T : Finset X) (n : X → ℕ) (s : Finset ι)
    (w : ι → X → ℂ) : Dsum q a T n (fun x => ∑ i ∈ s, w i x) = ∑ i ∈ s, Dsum q a T n (w i) := by
  unfold Dsum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]

/-- `Dsum` splits over the fibres of a map into `t`. -/
theorem Dsum_fiber {X : Type*} {q : ℕ} (a : ZMod q) (T : Finset X) (n : X → ℕ) (w : X → ℂ) (g : X → ℕ)
    (t : Finset ℕ) (hg : ∀ x ∈ T, g x ∈ t) :
    Dsum q a T n w = ∑ b ∈ t, Dsum q a (T.filter (fun x => g x = b)) n w := by
  unfold Dsum
  exact (Finset.sum_fiberwise_of_maps_to hg _).symm

/-- `Dsum` over a smaller set, when the weight vanishes off it. -/
theorem Dsum_subset {X : Type*} {q : ℕ} (a : ZMod q) {T T' : Finset X} (h : T' ⊆ T) (n : X → ℕ) (w : X → ℂ)
    (hw : ∀ x ∈ T, x ∉ T' → w x = 0) : Dsum q a T n w = Dsum q a T' n w := by
  unfold Dsum
  exact (Finset.sum_subset h fun x hx hx' => by rw [hw x hx hx', zero_mul]).symm

theorem Dsum_congr {X : Type*} {q : ℕ} (a : ZMod q) (T : Finset X) (n : X → ℕ) {w w' : X → ℂ}
    (h : ∀ x ∈ T, w x = w' x) : Dsum q a T n w = Dsum q a T n w' := by
  unfold Dsum
  exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

/-- Eventually `(3 + 4 log x)^K ≤ x^r`, for `r > 0`. -/
theorem ev_log_pow_le (K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, (3 + 4 * Real.log x) ^ K ≤ x ^ r := by
  have hrK : 0 < r / (K + 1) := by positivity
  have h1 := (isLittleO_log_rpow_atTop hrK).def (show (0 : ℝ) < 1 / 7 by norm_num)
  filter_upwards [h1, eventually_ge_atTop (Real.exp 1)] with x hx1 hx2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx2
  have hl : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx2
  have hxr : 0 ≤ x ^ (r / (K + 1)) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg hxr] at hx1
  have h2 : 3 + 4 * Real.log x ≤ x ^ (r / (K + 1)) := by linarith
  calc (3 + 4 * Real.log x) ^ K ≤ (x ^ (r / (K + 1))) ^ K := pow_le_pow_left₀ (by linarith) h2 K
    _ = x ^ (r / (K + 1) * K) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    _ ≤ x ^ r := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (1 : ℝ)])
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem mem_primesTo {Q : ℝ} (hQ : 0 ≤ Q) {p : ℕ} : p ∈ primesTo Q ↔ (p : ℝ) ≤ 2 * Q ∧ p.Prime := by
  rw [primesTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]

/-- **Changing the box.** With dyadic weights `f0(x_i/Q_i)`, `Q_i > 0`, the primes up to `Y` may be replaced by
`Sp`'s ranges `primesTo Q_i`, when the weight vanishes unless every `x_i ≤ Y`. -/
theorem box_change {q : ℕ} (a : ZMod q) (Sb : Finset ℕ) {n : ℕ} (Y : ℕ) (Q : Fin (n + 1) → ℝ)
    (hQ : ∀ i, 0 < Q i) (F : ℕ → (Fin (n + 1) → ℕ) → ℂ)
    (hF : ∀ m ∈ Sb, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → F m x ≠ 0 → ∀ i, x i ≤ Y) :
    Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y)) (fun mx => mx.1 * ∏ i, mx.2 i)
        (fun mx => F mx.1 mx.2 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) =
      Dsum q a (Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i))) (fun mx => mx.1 * ∏ i, mx.2 i)
        (fun mx => F mx.1 mx.2 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) := by
  set box' := Fintype.piFinset (fun i : Fin (n + 1) => primesLe Y ∩ primesTo (Q i)) with hbox'
  have hbump0 : ∀ (x : Fin (n + 1) → ℕ) (i : Fin (n + 1)), 2 * Q i < x i →
      ∏ i, ((SieveDyadic.bump ((x i : ℝ) / Q i) : ℝ) : ℂ) = 0 := by
    intro x i hi
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have : SieveDyadic.bump ((x i : ℝ) / Q i) = 0 := by
      by_contra hne
      have h2 := (SieveDyadic.bump_support (Function.mem_support.2 hne)).2
      rw [div_le_iff₀ (hQ i)] at h2
      linarith
    rw [this, Complex.ofReal_zero]
  have h1 : Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y)) (fun mx => mx.1 * ∏ i, mx.2 i)
      (fun mx => F mx.1 mx.2 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) =
      Dsum q a (Sb ×ˢ box') (fun mx => mx.1 * ∏ i, mx.2 i)
      (fun mx => F mx.1 mx.2 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) := by
    refine Dsum_subset a (Finset.product_subset_product_right
      (Fintype.piFinset_subset _ _ fun i => Finset.inter_subset_left)) _ _ fun mx hmx hmx' => ?_
    obtain ⟨hm, hx⟩ := Finset.mem_product.1 hmx
    rw [Fintype.mem_piFinset] at hx
    have : ∃ i, mx.2 i ∉ primesTo (Q i) := by
      by_contra h
      push Not at h
      exact hmx' (Finset.mem_product.2 ⟨hm, Fintype.mem_piFinset.2 fun i => Finset.mem_inter.2 ⟨hx i, h i⟩⟩)
    obtain ⟨i, hi⟩ := this
    have hp := (mem_primesLe.1 (hx i)).2
    rw [mem_primesTo (hQ i).le] at hi
    have : 2 * Q i < mx.2 i := by
      by_contra h'
      exact hi ⟨not_lt.1 h', hp⟩
    rw [hbump0 mx.2 i this, mul_zero]
  have h2 : Dsum q a (Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i))) (fun mx => mx.1 * ∏ i, mx.2 i)
      (fun mx => F mx.1 mx.2 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) =
      Dsum q a (Sb ×ˢ box') (fun mx => mx.1 * ∏ i, mx.2 i)
      (fun mx => F mx.1 mx.2 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) := by
    refine Dsum_subset a (Finset.product_subset_product_right
      (Fintype.piFinset_subset _ _ fun i => Finset.inter_subset_right)) _ _ fun mx hmx hmx' => ?_
    obtain ⟨hm, hx⟩ := Finset.mem_product.1 hmx
    rw [Fintype.mem_piFinset] at hx
    have hpr : ∀ i, (mx.2 i).Prime := fun i => ((mem_primesTo (hQ i).le).1 (hx i)).2
    have : ∃ i, mx.2 i ∉ primesLe Y := by
      by_contra h
      push Not at h
      exact hmx' (Finset.mem_product.2 ⟨hm, Fintype.mem_piFinset.2 fun i => Finset.mem_inter.2 ⟨h i, hx i⟩⟩)
    obtain ⟨i, hi⟩ := this
    have hF0 : F mx.1 mx.2 = 0 := by
      by_contra hne
      exact hi (mem_primesLe.2 ⟨hF mx.1 hm mx.2 hpr hne i, hpr i⟩)
    rw [hF0, zero_mul]
  rw [h1, h2]

section Main

open Classical
open scoped ContDiff

/-- **Type II for families with sharp prime ranges.** Fix `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0` and `Λ₁ ≥ 0`. There are
`δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `m` run over `S ⊆ (P₁, P₂]` with
`q^{0.401L} ≤ P₁` and `P₂ ≤ q^{0.485L}`, with coefficients `|a_m| ≤ 1`, and let `n + 1 ≤ K₀` primes `x_i` run over
the primes up to `⌊2q^L⌋`. Let `J ≤ J₀` sharp comparisons `P_j` hold when `ℓ_j = φ_j(m) + Σ_i e_{ji} log x_i > 0` and
imply `ℓ_j ≥ 0`, with `|e_{ji}| ≤ E₀`, `φ_j(m) ≤ Λ₁ log q` on `S` and for each `j` a pivot `i` with `e_{ji} = ±1`. If
wherever all the comparisons hold each `x_i ≥ 2q^{e₁}` and `m∏_i x_i ≤ 2q^L`, then the family's `|A − B/φ(q)|` is at
most `q^{L−δ}/φ(q)`. -/
theorem typeII_unw (K₀ J₀ : ℕ) {e₁ E₀ Λ₁ : ℝ} (he₁ : 0 < e₁) (hE₀ : 0 ≤ E₀) (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P₁ P₂ : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P₁ P₂ →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (acoef : ℕ → ℂ), (∀ m, ‖acoef m‖ ≤ 1) →
      ∀ (n : ℕ), n + 1 ≤ K₀ →
      ∀ {J : ℕ}, J ≤ J₀ → ∀ (φ : Fin J → ℕ → ℝ) (e : Fin J → Fin (n + 1) → ℝ)
        (Pr : Fin J → ℕ → (Fin (n + 1) → ℕ) → Prop), (∀ j i, |e j i| ≤ E₀) →
      (∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
        (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i))) →
      (∀ j, ∀ m ∈ S, φ j m ≤ Λ₁ * Real.log q) →
      ∀ piv : Fin J → Fin (n + 1), (∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) →
      (∀ m ∈ S, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) → (∀ j, Pr j m x) →
        (∀ i, 2 * (q : ℝ) ^ e₁ ≤ x i) ∧ (m : ℝ) * ∏ i, (x i : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) →
      ‖Dsum q a (S ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊))
          (fun mx => mx.1 * ∏ i, mx.2 i)
          (fun mx => acoef mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ) := by
  have hΛ₀0 : 0 ≤ Λ₁ + K₀ * E₀ * (2333 / 1000 + 3) := by positivity
  obtain ⟨δ, hδ, q₁, hq₁⟩ := typeII_sharp (f0 := SieveDyadic.bump) (SieveDyadic.contDiff_bump (n := ⊤))
    SieveDyadic.bump_support SieveDyadic.bump_nonneg (F₀ := 1) SieveDyadic.bump_le_one (K₀ + 1) J₀
    (A₀ := 1) he₁ hE₀ hΛ₀0
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (ev_log_pow_le (K₀ + 1) (half_pos hδ)))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) 2, ?_⟩
  intro q _ hq a ha P₁ P₂ S hS hP₁ hP₂ acoef hacoef n hn J hJ φ e Pr he hP hφ piv hpiv hsupp
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq3 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hqR
  have hqL0 : 0 < (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.rpow_pos_of_pos hq0 _
  have hqL1 : (1 : ℝ) ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  set Y : ℕ := ⌊2 * (q : ℝ) ^ (2333 / 1000 : ℝ)⌋₊ with hY
  have hY0 : Y ≠ 0 := by
    have : 1 ≤ Y := Nat.le_floor (by push_cast; linarith)
    omega
  have hYle : (Y : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := Nat.floor_le (by positivity)
  set M : ℕ := Nat.log 2 Y + 1 with hM
  have hP₁1 : 1 ≤ P₁ := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    exact_mod_cast this.trans hP₁
  -- a nonzero weight has every `x_i ≤ Y`
  have hFY : ∀ m ∈ S, ∀ x : Fin (n + 1) → ℕ, (∀ i, (x i).Prime) →
      acoef m * ∏ j, ((if Pr j m x then 1 else 0 : ℝ) : ℂ) ≠ 0 → ∀ i, x i ≤ Y := by
    intro m hm x hx hne i
    have hall : ∀ j, Pr j m x := by
      intro j
      by_contra hj
      exact hne (by rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero])
    have h2 := (hsupp m hm x hx hall).2
    have hm1 : (1 : ℝ) ≤ m := by
      have := (Finset.mem_Ioc.1 (hS hm)).1
      exact_mod_cast (show 1 ≤ m by omega)
    have hxi : x i ≤ ∏ i, x i :=
      Nat.le_of_dvd (Finset.prod_pos fun j _ => (hx j).pos) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    have hxi' : (x i : ℝ) ≤ ∏ i, (x i : ℝ) := by exact_mod_cast hxi
    have hprod0 : (0 : ℝ) ≤ ∏ i, (x i : ℝ) := Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
    apply Nat.le_floor
    nlinarith
  -- the blocks of `m`
  have hP₂Y : P₂ ≤ Y := by
    apply Nat.le_floor
    calc (P₂ : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) := hP₂
      _ ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) := by linarith
  have hblkS : ∀ m ∈ S, Nat.log 2 ((m - 1) / P₁) ∈ Finset.range M := by
    intro m hm
    have hmI := Finset.mem_Ioc.1 (hS hm)
    obtain ⟨h1, -⟩ := blk_spec hP₁1 hmI.1
    rw [Finset.mem_range, hM, Nat.lt_succ_iff]
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    exact le_trans (Nat.le_mul_of_pos_left _ hP₁1) (le_trans h1.le (le_trans hmI.2 hP₂Y))
  rw [Dsum_fiber a _ _ _ (fun mx => Nat.log 2 ((mx.1 - 1) / P₁)) (Finset.range M)
    (fun mx hmx => hblkS mx.1 (Finset.mem_product.1 hmx).1)]
  -- one block
  have hblock : ∀ b ∈ Finset.range M,
      ‖Dsum q a ((S ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y)).filter
          (fun mx => Nat.log 2 ((mx.1 - 1) / P₁) = b)) (fun mx => mx.1 * ∏ i, mx.2 i)
          (fun mx => acoef mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        ((M + 1 : ℕ) : ℝ) ^ (n + 1) * ((q.totient : ℝ)⁻¹ * (1 * (q : ℝ) ^ (2333 / 1000 - δ : ℝ))) := by
    intro b _
    set Sb := S.filter (fun m => Nat.log 2 ((m - 1) / P₁) = b) with hSb
    have hfilt : (S ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y)).filter
        (fun mx => Nat.log 2 ((mx.1 - 1) / P₁) = b) =
        Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y) := by
      ext mx
      simp only [hSb, Finset.mem_filter, Finset.mem_product]
      tauto
    rw [hfilt]
    have hbound0 : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ (n + 1) *
        ((q.totient : ℝ)⁻¹ * (1 * (q : ℝ) ^ (2333 / 1000 - δ : ℝ))) := by positivity
    rcases Sb.eq_empty_or_nonempty with hSb0 | ⟨m₀, hm₀⟩
    · rw [hSb0, Finset.empty_product]
      simp only [Dsum, Finset.sum_empty, norm_zero]
      exact hbound0
    set P' := P₁ * 2 ^ b with hP'
    have hSbI : Sb ⊆ Finset.Ioc P' (2 * P') := by
      intro m hm
      obtain ⟨hmS, hmb⟩ := Finset.mem_filter.1 hm
      obtain ⟨h1, h2⟩ := blk_spec hP₁1 (Finset.mem_Ioc.1 (hS hmS)).1
      rw [hmb] at h1 h2
      exact Finset.mem_Ioc.2 ⟨h1, h2⟩
    have hm₀S := (Finset.mem_filter.1 hm₀).1
    have hP'm₀ : P' < m₀ := (Finset.mem_Ioc.1 (hSbI hm₀)).1
    have hP'lo : (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P' := by
      have : P₁ ≤ P' := Nat.le_mul_of_pos_right _ (by positivity)
      exact hP₁.trans (by exact_mod_cast this)
    have hP'hi : (P' : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) := by
      have : P' ≤ P₂ := le_trans hP'm₀.le (Finset.mem_Ioc.1 (hS hm₀S)).2
      exact (by exact_mod_cast this : (P' : ℝ) ≤ P₂).trans hP₂
    have hP'pos : (0 : ℝ) < P' := by
      have : 0 < P' := Nat.mul_pos hP₁1 (by positivity)
      exact_mod_cast this
    -- the dyadic scales of the primes
    set Kset := Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (M + 1)) with hKset
    have hdy : Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
        (fun mx => mx.1 * ∏ i, mx.2 i)
        (fun mx => acoef mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) =
        ∑ k ∈ Kset, Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
          (fun mx => mx.1 * ∏ i, mx.2 i)
          (fun mx => (acoef mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) *
            ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ (k i)) : ℝ) : ℂ)) := by
      rw [← Dsum_sum]
      refine Dsum_congr a _ _ fun mx hmx => ?_
      rw [← Finset.mul_sum]
      have hx := Fintype.mem_piFinset.1 (Finset.mem_product.1 hmx).2
      have hone : ∑ k ∈ Kset, ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ (k i)) : ℝ) : ℂ) = 1 := by
        have h := Finset.prod_univ_sum (fun _ : Fin (n + 1) => Finset.range (M + 1))
          (fun i k => ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ k) : ℝ) : ℂ))
        rw [hKset, ← h]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [← Complex.ofReal_sum, SieveDyadic.sum_bump, Complex.ofReal_one]
        · exact_mod_cast (mem_primesLe.1 (hx i)).2.one_lt.le
        · have h1 := (mem_primesLe.1 (hx i)).1
          have hYM : Y < 2 ^ M := Nat.lt_pow_succ_log_self (by norm_num) Y
          exact_mod_cast (show mx.2 i ≤ 2 ^ M by omega)
      rw [hone, mul_one]
    rw [hdy]
    refine (norm_sum_le _ _).trans ?_
    have hcard : (Kset.card : ℝ) = ((M + 1 : ℕ) : ℝ) ^ (n + 1) := by
      rw [hKset, Fintype.card_piFinset]
      simp
    rw [← hcard, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
    have hkM : ∀ i, k i ≤ M := fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hk i))
    set Q : ℕ → ℝ := fun j => if h : j < n + 1 then (2 : ℝ) ^ (k ⟨j, h⟩) else 1 with hQ
    have hQi : ∀ i : Fin (n + 1), Q i = (2 : ℝ) ^ (k i) := fun i => by rw [hQ]; exact dite_eq_left i.isLt
    have hQpos : ∀ i : Fin (n + 1), 0 < Q i := fun i => by rw [hQi]; positivity
    have hfam : Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
        (fun mx => mx.1 * ∏ i, mx.2 i)
        (fun mx => (acoef mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) *
          ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / 2 ^ (k i)) : ℝ) : ℂ)) =
        Dsum q a (Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i))) (fun mx => mx.1 * ∏ i, mx.2 i)
          (fun mx => (acoef mx.1 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) := by
      have hbc := box_change a Sb Y (fun i => Q i) hQpos
        (fun m x => acoef m * ∏ j, ((if Pr j m x then 1 else 0 : ℝ) : ℂ))
        (fun m hm x hx hne => hFY m (Finset.mem_filter.1 hm).1 x hx hne)
      calc _ = Dsum q a (Sb ×ˢ Fintype.piFinset (fun _ : Fin (n + 1) => primesLe Y))
            (fun mx => mx.1 * ∏ i, mx.2 i)
            (fun mx => (acoef mx.1 * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) *
              ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) :=
            Dsum_congr a _ _ fun mx _ => by simp only [hQi]
        _ = _ := hbc
        _ = _ := Dsum_congr a _ _ fun mx _ => by ring
    rw [hfam]
    -- the comparisons' forms on the box
    have hℓ : ∀ j, ∀ m ∈ Sb, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        φ j m + ∑ i, e j i * Real.log (x i) ≤ (Λ₁ + K₀ * E₀ * (2333 / 1000 + 3)) * Real.log q := by
      intro j m hm x hx
      rw [Fintype.mem_piFinset] at hx
      have hlogx : ∀ i, 0 ≤ Real.log (x i) ∧ Real.log (x i) ≤ (2333 / 1000 + 3) * Real.log q := by
        intro i
        obtain ⟨hxle, hxp⟩ := (mem_primesTo (hQpos i).le).1 (hx i)
        have hx1 : (1 : ℝ) ≤ x i := by exact_mod_cast hxp.one_lt.le
        refine ⟨Real.log_nonneg hx1, ?_⟩
        have h2M : (2 : ℝ) ^ M ≤ 4 * (q : ℝ) ^ (2333 / 1000 : ℝ) := by
          have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
          push_cast at h1
          rw [hM, pow_succ]
          linarith
        have hxi : (x i : ℝ) ≤ 8 * (q : ℝ) ^ (2333 / 1000 : ℝ) := by
          have : (2 : ℝ) ^ (k i) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (hkM i)
          rw [hQi] at hxle
          linarith
        calc Real.log (x i) ≤ Real.log (8 * (q : ℝ) ^ (2333 / 1000 : ℝ)) := Real.log_le_log (by linarith) hxi
          _ = Real.log 8 + 2333 / 1000 * Real.log q := by
              rw [Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0]
          _ ≤ (2333 / 1000 + 3) * Real.log q := by
              have : Real.log 8 = 3 * Real.log 2 := by
                rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
              nlinarith
      have hsum : ∑ i, e j i * Real.log (x i) ≤ ∑ _i : Fin (n + 1), E₀ * ((2333 / 1000 + 3) * Real.log q) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := hlogx i
        have h2 : e j i ≤ E₀ := le_trans (le_abs_self _) (he j i)
        exact le_trans (mul_le_mul_of_nonneg_right h2 h1.1) (mul_le_mul_of_nonneg_left h1.2 hE₀)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      push_cast at hsum
      have hφm := hφ j m (Finset.mem_filter.1 hm).1
      have hlq0 : 0 ≤ Real.log q := by linarith
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ K₀ := by exact_mod_cast hn
      push_cast at hn'
      have h3 : ((n : ℝ) + 1) * (E₀ * ((2333 / 1000 + 3) * Real.log q)) ≤
          (K₀ : ℝ) * (E₀ * ((2333 / 1000 + 3) * Real.log q)) :=
        mul_le_mul_of_nonneg_right hn' (by positivity)
      linarith
    by_cases hgood : (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) ∧
        ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ (K₀ + 1) * (q : ℝ) ^ (2333 / 1000 : ℝ) / P'
    · exact hq₁ q hq1 a ha P' Sb hSbI hP'lo hP'hi acoef hacoef n (by omega) Q hgood.1 hgood.2 hJ φ e Pr he hP
        hℓ piv hpiv
    · have hz : ∀ mx ∈ Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          (acoef mx.1 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ) = 0 := by
        intro mx hmx
        obtain ⟨hm, hx⟩ := Finset.mem_product.1 hmx
        rw [Fintype.mem_piFinset] at hx
        by_contra hne
        have hall : ∀ j, Pr j mx.1 mx.2 := by
          intro j
          by_contra hj
          exact hne (by rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero])
        have hbump : ∀ i : Fin (n + 1), Q i / 2 ≤ mx.2 i := by
          intro i
          by_contra hlt
          push Not at hlt
          apply hne
          have hb0 : SieveDyadic.bump ((mx.2 i : ℝ) / Q i) = 0 := by
            by_contra hb
            have h1 := (SieveDyadic.bump_support (Function.mem_support.2 hb)).1
            rw [le_div_iff₀ (hQpos i)] at h1
            linarith
          rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hb0, Complex.ofReal_zero]), mul_zero, zero_mul]
        have hpr : ∀ i, (mx.2 i).Prime := fun i => ((mem_primesTo (hQpos i).le).1 (hx i)).2
        obtain ⟨hlow, hhigh⟩ := hsupp mx.1 (Finset.mem_filter.1 hm).1 mx.2 hpr hall
        apply hgood
        refine ⟨fun j hj => ?_, ?_⟩
        · have h1 := ((mem_primesTo (hQpos ⟨j, hj⟩).le).1 (hx ⟨j, hj⟩)).1
          have h2 := hlow ⟨j, hj⟩
          have : Q (⟨j, hj⟩ : Fin (n + 1)) = Q j := rfl
          linarith
        · rw [← Fin.prod_univ_eq_prod_range]
          have hprodQ : ∏ i : Fin (n + 1), Q i ≤ ∏ i : Fin (n + 1), (2 * (mx.2 i : ℝ)) :=
            Finset.prod_le_prod₀ (fun i _ => (hQpos i).le) (fun i _ => by linarith [hbump i])
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprodQ
          have hmP : (P' : ℝ) < mx.1 := by exact_mod_cast (Finset.mem_Ioc.1 (hSbI hm)).1
          have hprod0 : (0 : ℝ) ≤ ∏ i, (mx.2 i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
          have hprodx : ∏ i, (mx.2 i : ℝ) ≤ 2 * (q : ℝ) ^ (2333 / 1000 : ℝ) / P' := by
            rw [le_div_iff₀ hP'pos]
            nlinarith
          have h2pow : (2 : ℝ) ^ (n + 2) ≤ 2 ^ (K₀ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          calc ∏ i : Fin (n + 1), Q ↑i ≤ 2 ^ (n + 1) * ∏ i, (mx.2 i : ℝ) := hprodQ
            _ ≤ 2 ^ (n + 1) * (2 * (q : ℝ) ^ (2333 / 1000 : ℝ) / P') := by gcongr
            _ = 2 ^ (n + 2) * ((q : ℝ) ^ (2333 / 1000 : ℝ) / P') := by ring
            _ ≤ 2 ^ (K₀ + 1) * ((q : ℝ) ^ (2333 / 1000 : ℝ) / P') :=
                mul_le_mul_of_nonneg_right h2pow (by positivity)
            _ = 2 ^ (K₀ + 1) * (q : ℝ) ^ (2333 / 1000 : ℝ) / P' := by ring
      have hz' : Dsum q a (Sb ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
          (fun mx => mx.1 * ∏ i, mx.2 i)
          (fun mx => (acoef mx.1 * ∏ i, ((SieveDyadic.bump ((mx.2 i : ℝ) / Q i) : ℝ) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ)) = 0 :=
        Finset.sum_eq_zero fun mx hmx => by beta_reduce; rw [hz mx hmx, zero_mul]
      rw [hz', norm_zero]
      positivity
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hblock).trans ?_)
  rw [Finset.card_range, nsmul_eq_mul]
  have hNlog : (Nat.log 2 Y : ℝ) ≤ 1 + 4 * Real.log q := by
    have h1 : ((2 ^ Nat.log 2 Y : ℕ) : ℝ) ≤ Y := by exact_mod_cast Nat.pow_log_le_self 2 hY0
    push_cast at h1
    have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 Y) ≤ Real.log (2 * (q : ℝ) ^ (2333 / 1000 : ℝ)) :=
      Real.log_le_log (by positivity) (h1.trans hYle)
    rw [Real.log_pow, Real.log_mul (by norm_num) hqL0.ne', Real.log_rpow hq0] at h3
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlq0 : 0 ≤ Real.log q := by linarith
    refine le_of_mul_le_mul_right ?_ hlog2
    nlinarith
  have hcount : (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (n + 1) ≤ (q : ℝ) ^ (δ / 2) := by
    have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 3 + 4 * Real.log q := by
      rw [hM]; push_cast; linarith
    have hM0 : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    calc (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (n + 1) ≤ ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (n + 1) := by
          gcongr; linarith
      _ = ((M + 1 : ℕ) : ℝ) ^ (n + 2) := by ring
      _ ≤ ((M + 1 : ℕ) : ℝ) ^ (K₀ + 1) := pow_le_pow_right₀ hM0 (by omega)
      _ ≤ (3 + 4 * Real.log q) ^ (K₀ + 1) := pow_le_pow_left₀ (by linarith) hM1 _
      _ ≤ (q : ℝ) ^ (δ / 2) := hq₂ q hq2
  calc (M : ℝ) * (((M + 1 : ℕ) : ℝ) ^ (n + 1) *
        ((q.totient : ℝ)⁻¹ * (1 * (q : ℝ) ^ (2333 / 1000 - δ : ℝ))))
      = ((M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (n + 1)) *
          ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)) := by ring
    _ ≤ (q : ℝ) ^ (δ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (2333 / 1000 - δ / 2 : ℝ) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

end Main

end SieveTypeIIU
