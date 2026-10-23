/-
# Round 708: the kept parts' `B`-count, from below

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK` and `Fits` where the Lean takes them);
`x = q^L`, `X = x/log x`, and `parQ q` is the decomposition's parameters at `x`. For a cell `(i, j)` of `reg2` and a
cell `k` that `keep` passes below it, the kept part `Kk(i, j, k)` counts the `n = p₁p₂q₁q₂ ∈ (N₁, N₂]` with `p₁, p₂, q₁`
in the cells `i, j, k`, `q₂` prime, `q₁ < q₂` and `q₁, q₂ ≠ p₁`; with the weights `g_B = 1[(n, q) = 1]/φ(q)` its count
is at least `φ(q)⁻¹(keepK/K − δ)X` for large `q`, for every `δ > 0` (`Kk_gB_ge`).

* `card_primeFactors_le`: `q` has at most `log q/log 2` prime factors.
* `pairs_ge`: for `F ≥ 0`, the sum of `F(p₁, p₂)` over the family `S2c i j` is at least its sum over the pairs of the
  cells `i` and `j`, when `reg2` holds and `q` is large.
* `q2_ge`: for primes `p₁, p₂, q₁` of the cells, none dividing `q` and `q₁ ≠ p₁`, the `q₂` of the kept part number at
  least `π(y) − 1 − ω(q)`, where `π(y)` counts the primes of `(⌊y⌋, ⌊2y⌋]`, `y = x/(p₁p₂q₁)`, and `ω(q)` the prime
  factors of `q`; each such `q₂` exceeds `q₁`, since `2(e_k + H) + e_i + e_j + 2H ≤ DEN`.
* `Kk_gB_ge`: the bound. The main term is the prime number theorem in dyadic intervals (`SieveMain.primes_dyadic_ge`),
  `π(y) ≥ (1 − ε)y/log y` with `log y ≤ (γ_hi/DEN)log x`, `γ_hi = DEN − e_i − e_j − e_k`, times the three cells'
  `Σ 1/p`, each at least `H/(e + H) − δ′` (`SieveRoughLo.evGe_cell_inv`); the triples with a prime dividing `q` or with
  `q₁ = p₁` cost at most `x(1 + 3ω(q))/z₀`, and the other exclusions `(2 + ω(q))` per triple, both `o(X)`.

The file imports `SieveMain.lean`, `SieveKeptLeaf.lean` and `SieveRoughLo.lean`.
-/
import SieveMain
import SieveKeptLeaf
import SieveRoughLo

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveRoute
  SieveRoughLo
open SieveCert (V DEN H U1 U2 cand dec keep reg2 keepK K surelyEval cell)

namespace SieveKeptB

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-! ### Counting -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- `q ≥ 1` has at most `log q/log 2` prime factors. -/
theorem card_primeFactors_le {q : ℕ} (hq : 1 ≤ q) :
    ((q.primeFactors).card : ℝ) ≤ Real.log q / Real.log 2 := by
  have h1 : 2 ^ (q.primeFactors).card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h3 : ((2 : ℕ) : ℝ) ^ (q.primeFactors).card ≤ q := by exact_mod_cast h1.trans h2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at h4
  push_cast at h4
  linarith

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- The primes of `(⌊y⌋, ⌊2y⌋]`. -/
theorem card_dyadic_le {y : ℝ} (hy : 0 ≤ y) :
    (((Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime).card : ℝ) ≤ y + 1 := by
  have h1 : ((Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime).card ≤ ⌊2 * y⌋₊ - ⌊y⌋₊ :=
    (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ioc])
  have h2 : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le (by positivity)
  have h3 : y - 1 < (⌊y⌋₊ : ℝ) := Nat.sub_one_lt_floor y
  have h4 : ((⌊2 * y⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) ≤ (⌊2 * y⌋₊ : ℝ) - ⌊y⌋₊ := by
    rw [Nat.cast_sub (Nat.floor_le_floor (by linarith))]
  have : (((Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime).card : ℝ) ≤ ((⌊2 * y⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-! ### The pairs, and one triple's `q₂` -/

omit [RouteOK] [SieveCert.GridOK] [Fits] in
/-- For `x > 1`, a prime of the cell `c` is at least `z₀`. -/
theorem z0_le {q : ℕ} (hx : 1 < xq q) {c p : ℕ} (hp : p ∈ cellP (xq q) c) : (parQ q).z₀ ≤ p := by
  have hD := SieveCert.DEN_pos'
  rw [Par.mem_cellP_iff] at hp
  show ⌈(q : ℝ) ^ a0⌉₊ ≤ p
  rw [Nat.ceil_le]
  have h1 : (q : ℝ) ^ a0 = xq q ^ ((V : ℝ) / DEN) := by rw [xq, xpow]; rfl
  rw [h1]
  refine le_trans (Real.rpow_le_rpow_of_exponent_le hx.le ?_) hp.2.1
  exact div_le_div_of_nonneg_right (by exact_mod_cast (show V ≤ SieveCert.e c by unfold SieveCert.e; omega)) hD.le

omit [SieveCert.GridOK] [Fits] in
/-- **The pairs of the cells.** For `LargeQ q`, a cell `(i, j)` of `reg2` and `F ≥ 0`: the sum of `F` over the family
`S2c i j` is at least its sum over the pairs of the cells' primes. -/
theorem pairs_ge {q : ℕ} (hL : LargeQ q) {i j : ℕ} (hr : reg2 i j = true) (F : ℕ → ℕ → ℝ) (hF : ∀ a b, 0 ≤ F a b) :
    ∑ p₁ ∈ cellP (xq q) i, ∑ p₂ ∈ cellP (xq q) j, F p₁ p₂ ≤
      ∑ rt ∈ famSet 2 (N2 q) ((parQ q).S2c i j), F (rt 0) (rt 1) := by
  have hx1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hD := SieveCert.DEN_pos'
  simp only [reg2, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨hji, hi2⟩ := hr
  -- a prime of the cell `i` is below `√x`
  have hsq : ∀ p, p ∈ cellP (xq q) i → p * p ≤ N2 q := by
    intro p hp
    rw [Par.mem_cellP_iff] at hp
    have h1 : (p : ℝ) < xq q ^ ((1 : ℝ) / 2) := lt_of_lt_of_le hp.2.2
      (Real.rpow_le_rpow_of_exponent_le hx1.le (by
        rw [div_le_div_iff₀ hD (by norm_num)]
        have : ((2 * (SieveCert.e i + H) : ℕ) : ℝ) ≤ DEN := by exact_mod_cast hi2
        push_cast at this
        linarith))
    have hhalf : xq q ^ ((1 : ℝ) / 2) * xq q ^ ((1 : ℝ) / 2) = xq q := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h2 : ((p * p : ℕ) : ℝ) < xq q := by
      push_cast
      have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      nlinarith
    have h3 : xq q ≤ (N2 q : ℝ) := N2_ge q (SieveQ.q1 hL)
    exact_mod_cast (h2.trans_le h3).le
  rw [← Finset.sum_product' (f := F)]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (![p.1, p.2] : Fin 2 → ℕ))
      ↑((cellP (xq q) i) ×ˢ (cellP (xq q) j) : Finset (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [h0, h1]
  have himg := Finset.sum_image (f := fun rt : Fin 2 → ℕ => F (rt 0) (rt 1)) hinj
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at himg
  rw [← himg]
  calc ∑ rt ∈ ((cellP (xq q) i) ×ˢ (cellP (xq q) j)).image (fun p : ℕ × ℕ => (![p.1, p.2] : Fin 2 → ℕ)),
          F (rt 0) (rt 1)
    _ ≤ ∑ rt ∈ famSet 2 (N2 q) ((parQ q).S2c i j), F (rt 0) (rt 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun rt _ _ => hF _ _
        intro rt hrt
        obtain ⟨⟨p₁, p₂⟩, hp, rfl⟩ := Finset.mem_image.1 hrt
        rw [Finset.mem_product] at hp
        obtain ⟨hp₁, hp₂⟩ := hp
        have hp₁' := Par.mem_cellP_iff.1 hp₁
        have hp₂' := Par.mem_cellP_iff.1 hp₂
        have h21 : p₂ < p₁ := by
          have : (p₂ : ℝ) < p₁ := lt_of_lt_of_le hp₂'.2.2 ((Par.rpow_cell_le hx1.le hji).trans hp₁'.2.1)
          exact_mod_cast this
        have hsq₁ := hsq p₁ hp₁
        have hN₁ : p₁ ≤ N2 q := le_trans (Nat.le_mul_of_pos_right p₁ hp₁'.1.pos) hsq₁
        have htop : p₁ < (parQ q).ztop := by
          show p₁ < Nat.sqrt (N2 q) + 1
          have : p₁ ≤ Nat.sqrt (N2 q) := Nat.le_sqrt.2 hsq₁
          omega
        exact (parQ q).mem_S2c_of ⟨hN₁, hp₁'.1⟩ ⟨by omega, hp₂'.1⟩ (z0_le hx1 hp₁) htop hp₁'.2 (z0_le hx1 hp₂) h21
          hp₂'.2

omit [SieveCert.GridOK] [Fits] in
/-- **One triple's `q₂`.** For `LargeQ q`, a cell `(i, j)` of `reg2`, a cell `k` that `keep` passes below it, and primes
`p₁, p₂, q₁` of the cells `i, j, k`, none dividing `q`, with `q₁ ≠ p₁`: the kept `q₂` give at least
`φ(q)⁻¹(π(y) − 1 − ω(q))`, where `y = x/(p₁p₂q₁)`, `π(y)` counts the primes of `(⌊y⌋, ⌊2y⌋]` and `ω(q)` the prime
factors of `q`. -/
theorem q2_ge {q : ℕ} (hL : LargeQ q) {i j k : ℕ} (hkeep : keep i j k = true) {p₁ p₂ q₁ : ℕ}
    (hp₁ : p₁ ∈ cellP (xq q) i) (hp₂ : p₂ ∈ cellP (xq q) j) (hq₁ : q₁ ∈ cellP (xq q) k) (hne : q₁ ≠ p₁)
    (h₁ : ¬ p₁ ∣ q) (h₂ : ¬ p₂ ∣ q) (h₃ : ¬ q₁ ∣ q) :
    (q.totient : ℝ)⁻¹ * ((((Ioc ⌊xq q / (p₁ * p₂ * q₁)⌋₊ ⌊2 * (xq q / (p₁ * p₂ * q₁))⌋₊).filter Nat.Prime).card : ℝ) -
        1 - ((q.primeFactors).card : ℝ)) ≤
      ∑ q₂ ∈ SieveTypeIIU.primesLe (N2 q), if (parQ q).KC p₁ p₂ q₁ q₂ then gB q (p₁ * p₂ * q₁ * q₂) else 0 := by
  have hq0 : q ≠ 0 := by have := hL.q3; omega
  have hx1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hx0 : (0 : ℝ) < xq q := by linarith
  have hD := SieveCert.DEN_pos'
  have hp₁' := Par.mem_cellP_iff.1 hp₁
  have hp₂' := Par.mem_cellP_iff.1 hp₂
  have hq₁' := Par.mem_cellP_iff.1 hq₁
  have hW : (0 : ℝ) < (p₁ : ℝ) * p₂ * q₁ := by
    have := hp₁'.1.pos; have := hp₂'.1.pos; have := hq₁'.1.pos; positivity
  set y := xq q / (p₁ * p₂ * q₁) with hy
  have hyW : y * (p₁ * p₂ * q₁) = xq q := by rw [hy, div_mul_cancel₀ _ hW.ne']
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  -- `q₁ < y`: `p₁p₂q₁² < x`, since `2(e_k + H) + e_i + e_j + 2H ≤ DEN`
  have hq₁y : (q₁ : ℝ) < y := by
    simp only [keep, Bool.and_eq_true, decide_eq_true_eq] at hkeep
    have hsum := hkeep.1.2
    have hb : xq q ^ (((SieveCert.e i : ℝ) + H) / DEN) * xq q ^ (((SieveCert.e j : ℝ) + H) / DEN) *
        xq q ^ (((SieveCert.e k : ℝ) + H) / DEN) * xq q ^ (((SieveCert.e k : ℝ) + H) / DEN) ≤ xq q := by
      rw [Par.rpow_div_add hx0, Par.rpow_div_add hx0, Par.rpow_div_add hx0]
      conv_rhs => rw [← Real.rpow_one (xq q)]
      refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
      rw [div_le_one hD]
      have : ((2 * (SieveCert.e k + H) + SieveCert.e i + SieveCert.e j + 2 * H : ℕ) : ℝ) ≤ DEN := by
        exact_mod_cast hsum
      push_cast at this
      linarith
    have h0 : ∀ r : ℝ, 0 ≤ xq q ^ r := fun r => Real.rpow_nonneg hx0.le r
    have hlt : (p₁ : ℝ) * p₂ * q₁ * q₁ < xq q := by
      have a1 := hp₁'.2.2; have a2 := hp₂'.2.2; have a3 := hq₁'.2.2
      have b1 : (0 : ℝ) ≤ p₁ := Nat.cast_nonneg _
      have b2 : (0 : ℝ) ≤ p₂ := Nat.cast_nonneg _
      have b3 : (0 : ℝ) ≤ q₁ := Nat.cast_nonneg _
      calc (p₁ : ℝ) * p₂ * q₁ * q₁ < xq q ^ (((SieveCert.e i : ℝ) + H) / DEN) *
            xq q ^ (((SieveCert.e j : ℝ) + H) / DEN) * xq q ^ (((SieveCert.e k : ℝ) + H) / DEN) *
            xq q ^ (((SieveCert.e k : ℝ) + H) / DEN) := by
            refine mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' a1 a2 b1 b2) a3 (by positivity) b3) a3
              (by positivity) b3
        _ ≤ xq q := hb
    rw [hy, lt_div_iff₀ hW]
    linarith
  -- the primes of `(⌊y⌋, ⌊2y⌋]` other than `p₁` and the prime factors of `q`
  set A := (Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime with hA
  set Dq := A.filter (fun q₂ => q₂ ≠ p₁ ∧ q₂ ∉ q.primeFactors) with hDq
  have hcard : (A.card : ℝ) ≤ Dq.card + 1 + (q.primeFactors).card := by
    have hsub : A ⊆ Dq ∪ (insert p₁ q.primeFactors) := by
      intro r hr
      rw [Finset.mem_union, Finset.mem_insert]
      by_cases h1 : r = p₁
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : r ∈ q.primeFactors
        · exact Or.inr (Or.inr h2)
        · exact Or.inl (Finset.mem_filter.2 ⟨hr, h1, h2⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 := Finset.card_insert_le p₁ q.primeFactors
    have : A.card ≤ Dq.card + ((q.primeFactors).card + 1) := by omega
    have h3 : (A.card : ℝ) ≤ (Dq.card : ℝ) + ((q.primeFactors).card + 1) := by exact_mod_cast this
    linarith
  -- each `q₂` of `Dq` is kept, with weight `1/φ(q)`
  have hgood : ∀ q₂ ∈ Dq, q₂ ∈ SieveTypeIIU.primesLe (N2 q) ∧ (parQ q).KC p₁ p₂ q₁ q₂ ∧
      gB q (p₁ * p₂ * q₁ * q₂) = (q.totient : ℝ)⁻¹ := by
    intro q₂ hq₂
    rw [hDq, hA, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hq₂
    obtain ⟨⟨⟨hlo, hhi⟩, hq₂p⟩, hne₂, hnd⟩ := hq₂
    have hyq : y < q₂ := by
      have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ q₂ := by exact_mod_cast hlo
      push_cast at h2
      linarith
    have hq₂2y : (q₂ : ℝ) ≤ 2 * y := (Nat.cast_le.2 hhi).trans (Nat.floor_le (by positivity))
    have h12 : q₁ < q₂ := by exact_mod_cast hq₁y.trans hyq
    have hN1 : N1 q < p₁ * p₂ * q₁ * q₂ := by
      have h1 : ((N1 q : ℕ) : ℝ) ≤ xq q := Nat.floor_le hx0.le
      have h2 : xq q < ((p₁ * p₂ * q₁ * q₂ : ℕ) : ℝ) := by
        push_cast
        rw [← hyW]
        nlinarith
      exact_mod_cast h1.trans_lt h2
    have hN2 : p₁ * p₂ * q₁ * q₂ ≤ N2 q := by
      refine Nat.le_floor ?_
      push_cast
      calc (p₁ : ℝ) * p₂ * q₁ * q₂ ≤ (p₁ * p₂ * q₁) * (2 * y) := mul_le_mul_of_nonneg_left hq₂2y hW.le
        _ = 2 * (q : ℝ) ^ L := by rw [show (p₁ : ℝ) * p₂ * q₁ * (2 * y) = 2 * (y * (p₁ * p₂ * q₁)) by ring, hyW]
    have hq₂N : q₂ ≤ N2 q := le_trans (Nat.le_mul_of_pos_left q₂ (by
      have := hp₁'.1.pos; have := hp₂'.1.pos; have := hq₁'.1.pos; positivity)) hN2
    have hnd' : ¬ q₂ ∣ q := fun h => hnd (Nat.mem_primeFactors.2 ⟨hq₂p, h, hq0⟩)
    refine ⟨SieveTypeIIU.mem_primesLe.2 ⟨hq₂N, hq₂p⟩, ⟨h12, hne, hne₂, hN1, hN2⟩, ?_⟩
    have hu : IsUnit ((p₁ * p₂ * q₁ * q₂ : ℕ) : ZMod q) := by
      push_cast
      exact (((ZMod.isUnit_prime_iff_not_dvd hp₁'.1).2 h₁).mul ((ZMod.isUnit_prime_iff_not_dvd hp₂'.1).2 h₂)).mul
        ((ZMod.isUnit_prime_iff_not_dvd hq₁'.1).2 h₃) |>.mul ((ZMod.isUnit_prime_iff_not_dvd hq₂p).2 hnd')
    unfold gB
    rw [ite_eq_left hu]
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  calc (q.totient : ℝ)⁻¹ * ((A.card : ℝ) - 1 - ((q.primeFactors).card : ℝ))
      ≤ (q.totient : ℝ)⁻¹ * Dq.card := mul_le_mul_of_nonneg_left (by linarith) hφ
    _ = ∑ q₂ ∈ Dq, (if (parQ q).KC p₁ p₂ q₁ q₂ then gB q (p₁ * p₂ * q₁ * q₂) else 0) := by
        rw [Finset.sum_congr rfl fun q₂ hq₂ => by rw [ite_eq_left (hgood q₂ hq₂).2.1, (hgood q₂ hq₂).2.2]]
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ q₂ ∈ SieveTypeIIU.primesLe (N2 q),
          (if (parQ q).KC p₁ p₂ q₁ q₂ then gB q (p₁ * p₂ * q₁ * q₂) else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun q₂ hq₂ => (hgood q₂ hq₂).1) fun q₂ _ _ => ?_
        split_ifs
        · exact SieveDrop.gB_nonneg q _
        · exact le_rfl

/-- The primes of `(⌊y⌋, ⌊2y⌋]`. -/
noncomputable def pc (y : ℝ) : ℕ := ((Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime).card

omit [SieveCert.GridOK] [Fits] in
/-- **The triples.** For `LargeQ q`, a cell `(i, j)` of `reg2` and a cell `k` that `keep` passes below it:
`φ(q)⁻¹ Σ_{p₁, p₂, q₁} [good](π(y) − 1 − ω(q)) ≤ Kk(g_B)`, over the primes of the cells `i, j, k`, where a triple is
good when `q₁ ≠ p₁` and none of its primes divides `q`, and `y = x/(p₁p₂q₁)`. -/
theorem triples_ge {q : ℕ} (hL : LargeQ q) {i j k : ℕ} (hr : reg2 i j = true) (hkeep : keep i j k = true) :
    (q.totient : ℝ)⁻¹ * ∑ p₁ ∈ cellP (xq q) i, ∑ p₂ ∈ cellP (xq q) j, ∑ q₁ ∈ cellP (xq q) k,
        (if q₁ ≠ p₁ ∧ ¬ p₁ ∣ q ∧ ¬ p₂ ∣ q ∧ ¬ q₁ ∣ q then
          (pc (xq q / (p₁ * p₂ * q₁)) : ℝ) - 1 - ((q.primeFactors).card : ℝ) else 0) ≤
      (parQ q).Kk (gB q) i j k := by
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hgB : ∀ m, 0 ≤ gB q m := SieveDrop.gB_nonneg q
  refine le_trans ?_ (pairs_ge hL hr (fun p₁ p₂ => (parQ q).keptAt (gB q) k p₁ p₂)
    fun a b => (parQ q).keptAt_nonneg hgB k a b)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p₁ hp₁ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p₂ hp₂ => ?_
  rw [Finset.mul_sum]
  unfold Par.keptAt
  refine Finset.sum_le_sum fun q₁ hq₁ => ?_
  split_ifs with hg
  · exact q2_ge hL hkeep hp₁ hp₂ hq₁ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  · rw [mul_zero]
    exact Finset.sum_nonneg fun q₂ _ => by split_ifs <;> first | exact hgB _ | exact le_rfl

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- For `x > 1` and primes of the cells `i, j, k`:
`x^{(e_i + e_j + e_k)/DEN} ≤ p₁p₂q₁ < x^{(e_i + e_j + e_k + 3H)/DEN}`. -/
theorem prod3_bounds {x : ℝ} (hx : 1 < x) {i j k p₁ p₂ q₁ : ℕ} (h₁ : InC x i p₁) (h₂ : InC x j p₂) (h₃ : InC x k q₁) :
    x ^ (((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k) / DEN) ≤ (p₁ : ℝ) * p₂ * q₁ ∧
      (p₁ : ℝ) * p₂ * q₁ < x ^ (((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + 3 * H) / DEN) := by
  have hx0 : 0 < x := by linarith
  have h0 : ∀ r : ℝ, 0 ≤ x ^ r := fun r => Real.rpow_nonneg hx0.le r
  constructor
  · rw [← Par.rpow_div_add hx0, ← Par.rpow_div_add hx0]
    exact mul_le_mul (mul_le_mul h₁.1 h₂.1 (h0 _) (Nat.cast_nonneg _)) h₃.1 (h0 _) (by positivity)
  · have e : ((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + 3 * H) =
        ((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H) + ((SieveCert.e k : ℝ) + H) := by ring
    rw [e, ← Par.rpow_div_add hx0, ← Par.rpow_div_add hx0]
    exact mul_lt_mul'' (mul_lt_mul'' h₁.2 h₂.2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)) h₃.2 (by positivity)
      (Nat.cast_nonneg _)

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- A triple sum of a product is the product of the sums. -/
theorem sum3_mul (s₁ s₂ s₃ : Finset ℕ) (u v w : ℕ → ℝ) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, u a * v b * w c = (∑ a ∈ s₁, u a) * (∑ b ∈ s₂, v b) * ∑ c ∈ s₃, w c := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul_sum]

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- The primes of a finite set at least `z > 0` dividing `q ≥ 1` have `Σ 1/p ≤ ω(q)/z`. -/
theorem sum_dvd_inv_le {s : Finset ℕ} {z : ℝ} (hz : 0 < z) (hs : ∀ p ∈ s, p.Prime ∧ z ≤ p) {q : ℕ} (hq : q ≠ 0) :
    ∑ p ∈ s, (if p ∣ q then 1 / (p : ℝ) else 0) ≤ ((q.primeFactors).card : ℝ) / z := by
  rw [← Finset.sum_filter]
  have hsub : s.filter (fun p => p ∣ q) ⊆ q.primeFactors := fun p hp => by
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.2 ⟨(hs p hp.1).1, hp.2, hq⟩
  calc ∑ p ∈ s.filter (fun p => p ∣ q), 1 / (p : ℝ) ≤ ∑ _p ∈ s.filter (fun p => p ∣ q), 1 / z :=
        Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le hz (hs p (Finset.mem_filter.1 hp).1).2
    _ = ((s.filter (fun p => p ∣ q)).card : ℝ) / z := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ((q.primeFactors).card : ℝ) / z :=
        div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hz.le

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- For `x ≥ 1`, the cell `c` has at most `x^{(e_c + H)/DEN} + 1` primes. -/
theorem card_cellP_le {x : ℝ} (hx : 1 ≤ x) (c : ℕ) :
    ((cellP x c).card : ℝ) ≤ x ^ (((SieveCert.e c : ℝ) + H) / DEN) + 1 := by
  set B := x ^ (((SieveCert.e c : ℝ) + H) / DEN) with hB
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by linarith) _
  have hsub : cellP x c ⊆ Finset.range ⌈B⌉₊ := fun p hp => by
    rw [SieveRough.cellP, SieveRough.mem_primesIn] at hp
    rw [Finset.mem_range, Nat.lt_ceil]
    exact hp.2.2
  have h1 : ((cellP x c).card : ℝ) ≤ ⌈B⌉₊ := by
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact_mod_cast this
  have h2 : (⌈B⌉₊ : ℝ) < B + 1 := Nat.ceil_lt_add_one hB0
  linarith

omit [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- **The exclusions are `o(x/log x)`.** For `L > 0`, `0 < v` and `s < 1`, for every `δ > 0`, eventually in `q`:
`x(1 + 3ω′)/x^v + (2 + ω′)·8x^s ≤ δx/log x`, with `x = q^L` and `ω′ = log q/log 2`. -/
theorem err_ev {v s : ℝ} (hv : 0 < v) (hs : s < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, xq q * (1 + 3 * (Real.log q / Real.log 2)) / xq q ^ v +
      (2 + Real.log q / Real.log 2) * (8 * xq q ^ s) ≤ δ * (xq q / Real.log (xq q)) := by
  have hL0 : (0 : ℝ) < L := L_pos
  set r : ℝ := min (L * v) (L * (1 - s)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (mul_pos hL0 (by linarith))
  have e1 := (SieveTypeIIU.ev_log_pow_le 2 (half_pos hr0))
  have e2 := (tendsto_rpow_atTop (half_pos hr0)).eventually_ge_atTop (64 * L / δ)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (e1.and e2), eventually_ge_atTop 3] with q hq hq3
  obtain ⟨hlog, hbig⟩ := hq
  have hq3' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  set t := Real.log q with ht
  have ht1 : 1 ≤ t := by
    rw [ht, Real.le_log_iff_exp_le hq0]
    exact le_trans (by have := Real.exp_one_lt_d9; linarith) hq3'
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl20 : 0 < Real.log 2 := by linarith
  have hω : t / Real.log 2 ≤ 2 * t := by
    rw [div_le_iff₀ hl20]; nlinarith
  have hω0 : 0 ≤ t / Real.log 2 := by positivity
  -- `x = q^L` and its powers
  have hx : xq q = (q : ℝ) ^ L := rfl
  have hxl : Real.log (xq q) = L * t := by rw [hx, Real.log_rpow hq0]
  have hxv : xq q ^ v = (q : ℝ) ^ (L * v) := by rw [hx, xpow]
  have hxs : xq q ^ s = (q : ℝ) ^ (L * s) := by rw [hx, xpow]
  have hpos : ∀ a : ℝ, 0 < (q : ℝ) ^ a := fun a => Real.rpow_pos_of_pos hq0 a
  -- `q^{L − Lv} ≤ q^{L − r}` and `q^{Ls} ≤ q^{L − r}`
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have h1 : xq q / xq q ^ v ≤ (q : ℝ) ^ (L - r) := by
    rw [hxv, hx, ← Real.rpow_sub hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by have := min_le_left (L * v) (L * (1 - s)); linarith)
  have h2 : xq q ^ s ≤ (q : ℝ) ^ (L - r) := by
    rw [hxs]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by have := min_le_right (L * v) (L * (1 - s)); nlinarith)
  -- the left side is at most `32(1 + t)q^{L − r}`
  have hlhs : xq q * (1 + 3 * (t / Real.log 2)) / xq q ^ v + (2 + t / Real.log 2) * (8 * xq q ^ s) ≤
      32 * (1 + t) * (q : ℝ) ^ (L - r) := by
    have a1 : xq q * (1 + 3 * (t / Real.log 2)) / xq q ^ v = (xq q / xq q ^ v) * (1 + 3 * (t / Real.log 2)) := by
      ring
    rw [a1]
    have b1 : (xq q / xq q ^ v) * (1 + 3 * (t / Real.log 2)) ≤ (q : ℝ) ^ (L - r) * (16 * (1 + t)) :=
      mul_le_mul h1 (by nlinarith) (by positivity) (hpos _).le
    have b2 : (2 + t / Real.log 2) * (8 * xq q ^ s) ≤ (16 * (1 + t)) * (q : ℝ) ^ (L - r) := by
      have : 0 ≤ xq q ^ s := Real.rpow_nonneg (by positivity) s
      nlinarith
    nlinarith [hpos (L - r)]
  -- and `32(1 + t)q^{L − r} ≤ δq^L/(Lt)`
  have hsplit : (q : ℝ) ^ L = (q : ℝ) ^ (L - r) * (q : ℝ) ^ (r / 2) * (q : ℝ) ^ (r / 2) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
  have hlog' : (3 + 4 * t) ^ 2 ≤ (q : ℝ) ^ (r / 2) := hlog
  have hrhs : 32 * (1 + t) * (q : ℝ) ^ (L - r) ≤ δ * (xq q / Real.log (xq q)) := by
    rw [hxl, hx, mul_div_assoc', le_div_iff₀ (by positivity), hsplit]
    have c1 : 32 * (1 + t) * (L * t) ≤ 32 * L * (3 + 4 * t) ^ 2 := by nlinarith
    have c2 : 32 * L * (3 + 4 * t) ^ 2 ≤ 32 * L * (q : ℝ) ^ (r / 2) := by nlinarith
    have c3 : 64 * L ≤ δ * (q : ℝ) ^ (r / 2) := by
      have := hbig; rw [div_le_iff₀ hδ] at this; linarith
    have hA := hpos (L - r)
    have hB := hpos (r / 2)
    calc 32 * (1 + t) * (q : ℝ) ^ (L - r) * (L * t) = (q : ℝ) ^ (L - r) * (32 * (1 + t) * (L * t)) := by ring
      _ ≤ (q : ℝ) ^ (L - r) * (32 * L * (q : ℝ) ^ (r / 2)) := mul_le_mul_of_nonneg_left (c1.trans c2) hA.le
      _ ≤ (q : ℝ) ^ (L - r) * (δ * (q : ℝ) ^ (r / 2) * (q : ℝ) ^ (r / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA.le
          nlinarith
      _ = δ * ((q : ℝ) ^ (L - r) * (q : ℝ) ^ (r / 2) * (q : ℝ) ^ (r / 2)) := by ring
  exact hlhs.trans hrhs

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- One triple's lower bound: for `P ≤ y + 1`, `y, ω ≥ 0` and an indicator sum `I` that vanishes on good triples and is
at least `1` on the others, `P − Iy − (2 + ω) ≤ [good](P − 1 − ω)`. -/
theorem pt_le {P y ω I : ℝ} (G : Prop) [Decidable G] (hP : P ≤ y + 1) (hy : 0 ≤ y) (hω : 0 ≤ ω)
    (hG : G → I = 0) (hnG : ¬ G → 1 ≤ I) : P - I * y - (2 + ω) ≤ if G then P - 1 - ω else 0 := by
  by_cases h : G
  · rw [ite_eq_left h, hG h]; linarith
  · rw [ite_eq_right h]; have := hnG h; nlinarith

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- One triple's main term: for `x > 1`, `γ > 0`, `ε ≤ 1/2`, `y ≥ max(Y₀, 2)` with `y ≤ x^{γ/DEN}`, and the prime number
theorem `(1 − ε)t/log t ≤ π(t)` for `t ≥ Y₀`: `(1 − ε)(DEN/γ)(y/log x) ≤ π(y)`. -/
theorem main_pt {x y γ ε Y0 : ℝ} (hx : 1 < x) (hγ : 0 < γ) (hε : ε ≤ 1 / 2) (hyY : max Y0 2 ≤ y)
    (hyle : y ≤ x ^ (γ / DEN)) (hpnt : ∀ t ≥ Y0, (1 - ε) * (t / Real.log t) ≤ (pc t : ℝ)) :
    (1 - ε) * ((DEN : ℝ) / γ) * (y / Real.log x) ≤ (pc y : ℝ) := by
  have hD := SieveCert.DEN_pos'
  have hy2 : 2 ≤ y := le_trans (le_max_right _ _) hyY
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlyle : Real.log y ≤ γ / DEN * Real.log x := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) hyle
  have h1 : (DEN : ℝ) / γ * (y / Real.log x) ≤ y / Real.log y := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hly]
    have : (DEN : ℝ) * y * Real.log y ≤ DEN * y * (γ / DEN * Real.log x) :=
      mul_le_mul_of_nonneg_left hlyle (by positivity)
    calc (DEN : ℝ) * y * Real.log y ≤ DEN * y * (γ / DEN * Real.log x) := this
      _ = y * (γ * Real.log x) := by field_simp
  calc (1 - ε) * ((DEN : ℝ) / γ) * (y / Real.log x) = (1 - ε) * ((DEN : ℝ) / γ * (y / Real.log x)) := by ring
    _ ≤ (1 - ε) * (y / Real.log y) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ _ := hpnt y (le_trans (le_max_left _ _) hyY)

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- For `x > 1` and primes of the cells `i, j, k`, `y = x/(p₁p₂q₁)` lies in `[x^{(γ − 3H)/DEN}, x^{γ/DEN}]`, where
`γ = DEN − e_i − e_j − e_k`. -/
theorem y_bounds {x : ℝ} (hx : 1 < x) {i j k p₁ p₂ q₁ : ℕ} (h₁ : InC x i p₁) (h₂ : InC x j p₂) (h₃ : InC x k q₁) :
    x ^ ((((DEN : ℝ) - SieveCert.e i - SieveCert.e j - SieveCert.e k) - 3 * H) / DEN) ≤ x / (p₁ * p₂ * q₁) ∧
      x / (p₁ * p₂ * q₁) ≤ x ^ (((DEN : ℝ) - SieveCert.e i - SieveCert.e j - SieveCert.e k) / DEN) := by
  have hD := SieveCert.DEN_pos'
  have hx0 : 0 < x := by linarith
  obtain ⟨hlo, hhi⟩ := prod3_bounds hx h₁ h₂ h₃
  have hW : (0 : ℝ) < (p₁ : ℝ) * p₂ * q₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hlo
  constructor
  · rw [le_div_iff₀ hW]
    have e : x ^ ((((DEN : ℝ) - SieveCert.e i - SieveCert.e j - SieveCert.e k) - 3 * H) / DEN) *
        x ^ (((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + 3 * H) / DEN) = x := by
      rw [Par.rpow_div_add hx0]
      conv_rhs => rw [← Real.rpow_one x]
      congr 1
      field_simp
      ring
    have h0 := Real.rpow_pos_of_pos hx0 ((((DEN : ℝ) - SieveCert.e i - SieveCert.e j - SieveCert.e k) - 3 * H) / DEN)
    nlinarith
  · rw [div_le_iff₀ hW]
    have e : x ^ (((DEN : ℝ) - SieveCert.e i - SieveCert.e j - SieveCert.e k) / DEN) *
        x ^ (((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k) / DEN) = x := by
      rw [Par.rpow_div_add hx0]
      conv_rhs => rw [← Real.rpow_one x]
      congr 1
      field_simp
      ring
    have h0 := Real.rpow_pos_of_pos hx0 (((DEN : ℝ) - SieveCert.e i - SieveCert.e j - SieveCert.e k) / DEN)
    nlinarith

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- **The bad triples.** For finite sets of primes at least `z > 0`, each with `Σ 1/p ≤ 1`, and `q ≠ 0`: the triples
with `c = a` or a prime dividing `q`, weighted by `x/(abc)`, total at most `x(1 + 3ω(q))/z`. -/
theorem bad_sum_le {s₁ s₂ s₃ : Finset ℕ} {x z : ℝ} {q : ℕ} (hx : 0 ≤ x) (hz : 0 < z) (hq : q ≠ 0)
    (h₁ : ∀ p ∈ s₁, p.Prime ∧ z ≤ p) (h₂ : ∀ p ∈ s₂, p.Prime ∧ z ≤ p) (h₃ : ∀ p ∈ s₃, p.Prime ∧ z ≤ p)
    (hS₁ : ∑ p ∈ s₁, 1 / (p : ℝ) ≤ 1) (hS₂ : ∑ p ∈ s₂, 1 / (p : ℝ) ≤ 1) (hS₃ : ∑ p ∈ s₃, 1 / (p : ℝ) ≤ 1) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ((if c = a then 1 else 0) + (if a ∣ q then 1 else 0) +
        (if b ∣ q then 1 else 0) + (if c ∣ q then 1 else 0)) * (x / ((a : ℝ) * b * c)) ≤
      x * (1 + 3 * ((q.primeFactors).card : ℝ)) / z := by
  have hpos : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ z ≤ p) → ∀ p ∈ s, (0 : ℝ) < p := fun s hs p hp => by
    exact_mod_cast (hs p hp).1.pos
  have hS0 : ∀ s : Finset ℕ, 0 ≤ ∑ p ∈ s, 1 / (p : ℝ) := fun s => Finset.sum_nonneg fun _ _ => by positivity
  have hsplit : ∀ a ∈ s₁, ∀ b ∈ s₂, ∀ c ∈ s₃,
      ((if c = a then 1 else 0) + (if a ∣ q then 1 else 0) + (if b ∣ q then 1 else 0) +
        (if c ∣ q then 1 else 0)) * (x / ((a : ℝ) * b * c)) =
      x * ((if c = a then (1 / (a : ℝ)) * (1 / (b : ℝ)) * (1 / (c : ℝ)) else 0) +
        (if a ∣ q then 1 / (a : ℝ) else 0) * (1 / (b : ℝ)) * (1 / (c : ℝ)) +
        (1 / (a : ℝ)) * (if b ∣ q then 1 / (b : ℝ) else 0) * (1 / (c : ℝ)) +
        (1 / (a : ℝ)) * (1 / (b : ℝ)) * (if c ∣ q then 1 / (c : ℝ) else 0)) := by
    intro a ha b hb c hc
    have e1 := hpos s₁ h₁ a ha
    have e2 := hpos s₂ h₂ b hb
    have e3 := hpos s₃ h₃ c hc
    split_ifs <;> field_simp <;> ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl
    fun c hc => hsplit a ha b hb c hc]
  have esum : ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃,
      x * ((if c = a then (1 / (a : ℝ)) * (1 / (b : ℝ)) * (1 / (c : ℝ)) else 0) +
        (if a ∣ q then 1 / (a : ℝ) else 0) * (1 / (b : ℝ)) * (1 / (c : ℝ)) +
        (1 / (a : ℝ)) * (if b ∣ q then 1 / (b : ℝ) else 0) * (1 / (c : ℝ)) +
        (1 / (a : ℝ)) * (1 / (b : ℝ)) * (if c ∣ q then 1 / (c : ℝ) else 0)) =
      x * ((∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃,
          (if c = a then (1 / (a : ℝ)) * (1 / (b : ℝ)) * (1 / (c : ℝ)) else 0)) +
        (∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, (if a ∣ q then 1 / (a : ℝ) else 0) * (1 / (b : ℝ)) * (1 / (c : ℝ))) +
        (∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, (1 / (a : ℝ)) * (if b ∣ q then 1 / (b : ℝ) else 0) * (1 / (c : ℝ))) +
        (∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, (1 / (a : ℝ)) * (1 / (b : ℝ)) * (if c ∣ q then 1 / (c : ℝ) else 0))) := by
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [esum, sum3_mul s₁ s₂ s₃ (fun a => if a ∣ q then 1 / (a : ℝ) else 0) (fun b => 1 / (b : ℝ))
    (fun c => 1 / (c : ℝ)), sum3_mul s₁ s₂ s₃ (fun a => 1 / (a : ℝ)) (fun b => if b ∣ q then 1 / (b : ℝ) else 0)
    (fun c => 1 / (c : ℝ)), sum3_mul s₁ s₂ s₃ (fun a => 1 / (a : ℝ)) (fun b => 1 / (b : ℝ))
    (fun c => if c ∣ q then 1 / (c : ℝ) else 0)]
  -- the diagonal `c = a`
  have hdiag : ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃,
      (if c = a then (1 / (a : ℝ)) * (1 / (b : ℝ)) * (1 / (c : ℝ)) else 0) ≤
      (∑ p ∈ s₁, 1 / (p : ℝ)) * (∑ p ∈ s₂, 1 / (p : ℝ)) / z := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.sum_ite_eq']
    have e1 := hpos s₁ h₁ a ha
    have e2 := hpos s₂ h₂ b hb
    split_ifs
    · have h1 : 1 / (a : ℝ) ≤ 1 / z := one_div_le_one_div_of_le hz (h₁ a ha).2
      calc 1 / (a : ℝ) * (1 / b) * (1 / a) ≤ 1 / a * (1 / b) * (1 / z) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 / a * (1 / b) / z := by ring
    · positivity
  set ω : ℝ := ((q.primeFactors).card : ℝ) with hω
  have hdv : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ z ≤ p) →
      ∑ p ∈ s, (if p ∣ q then 1 / (p : ℝ) else 0) ≤ ω / z := fun s hs => sum_dvd_inv_le hz hs hq
  have hdv0 : ∀ s : Finset ℕ, 0 ≤ ∑ p ∈ s, (if p ∣ q then 1 / (p : ℝ) else 0) := fun s =>
    Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
  have hwz : 0 ≤ ω / z := by positivity
  have b1 : (∑ p ∈ s₁, 1 / (p : ℝ)) * (∑ p ∈ s₂, 1 / (p : ℝ)) / z ≤ 1 / z :=
    div_le_div_of_nonneg_right (by nlinarith [hS0 s₁, hS0 s₂]) hz.le
  have b2 := mul_le_mul (mul_le_mul (hdv s₁ h₁) hS₂ (hS0 s₂) hwz) hS₃ (hS0 s₃) (by positivity)
  have b3 := mul_le_mul (mul_le_mul hS₁ (hdv s₂ h₂) (hdv0 s₂) (by norm_num)) hS₃ (hS0 s₃) (by positivity)
  have b4 := mul_le_mul (mul_le_mul hS₁ hS₂ (hS0 s₂) (by norm_num)) (hdv s₃ h₃) (hdv0 s₃) (by norm_num)
  have e : x * (1 + 3 * ω) / z = x * (1 / z + ω / z * 1 * 1 + 1 * (ω / z) * 1 + 1 * 1 * (ω / z)) := by
    field_simp; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hx
  linarith [hdiag]

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- For `x > 1`, the three cells' primes number at most `8x^{(e_i + e_j + e_k + 3H)/DEN}` triples. -/
theorem triples_card_le {x : ℝ} (hx : 1 < x) (i j k : ℕ) :
    ((cellP x i).card : ℝ) * (cellP x j).card * (cellP x k).card ≤
      8 * x ^ (((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + 3 * H) / DEN) := by
  have hx0 : 0 < x := by linarith
  have hc := fun c => card_cellP_le hx.le c
  have h1 : ∀ c : ℕ, x ^ (((SieveCert.e c : ℝ) + H) / DEN) + 1 ≤ 2 * x ^ (((SieveCert.e c : ℝ) + H) / DEN) :=
    fun c => by
      have : 1 ≤ x ^ (((SieveCert.e c : ℝ) + H) / DEN) := Real.one_le_rpow hx.le (by positivity)
      linarith
  have e : ((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + 3 * H) =
      ((SieveCert.e i : ℝ) + H) + ((SieveCert.e j : ℝ) + H) + ((SieveCert.e k : ℝ) + H) := by ring
  rw [e, ← Par.rpow_div_add hx0, ← Par.rpow_div_add hx0]
  have hnn : ∀ c : ℕ, (0 : ℝ) ≤ (cellP x c).card := fun c => Nat.cast_nonneg _
  calc ((cellP x i).card : ℝ) * (cellP x j).card * (cellP x k).card
      ≤ (2 * x ^ (((SieveCert.e i : ℝ) + H) / DEN)) * (2 * x ^ (((SieveCert.e j : ℝ) + H) / DEN)) *
          (2 * x ^ (((SieveCert.e k : ℝ) + H) / DEN)) :=
        mul_le_mul (mul_le_mul ((hc i).trans (h1 i)) ((hc j).trans (h1 j)) (hnn j) (by positivity))
          ((hc k).trans (h1 k)) (hnn k) (by positivity)
    _ = _ := by ring

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- Four indicators: their sum is at least `1` when one condition holds, and `0` when none does. -/
theorem ind4 (c₁ c₂ c₃ c₄ : Prop) [Decidable c₁] [Decidable c₂] [Decidable c₃] [Decidable c₄] :
    ((c₁ ∨ c₂ ∨ c₃ ∨ c₄) → 1 ≤ (if c₁ then (1 : ℝ) else 0) + (if c₂ then 1 else 0) + (if c₃ then 1 else 0) +
      (if c₄ then 1 else 0)) ∧
    ((¬ c₁ ∧ ¬ c₂ ∧ ¬ c₃ ∧ ¬ c₄) → (if c₁ then (1 : ℝ) else 0) + (if c₂ then 1 else 0) + (if c₃ then 1 else 0) +
      (if c₄ then 1 else 0) = 0) := by
  constructor
  · intro h
    rcases h with h | h | h | h <;> simp only [h, ite_true] <;> split_ifs <;> norm_num
  · rintro ⟨h1, h2, h3, h4⟩
    simp [h1, h2, h3, h4]

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- Three reals at least `a − d`, `b − d`, `c − d`, the last two in `[0, 1]`, with `a, b ∈ [0, 1]` and `d ≥ 0`, have
product at least `abc − 3d`. -/
theorem prod3_ge {a b c x y z d : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hd : 0 ≤ d)
    (hx : a - d ≤ x) (hy : b - d ≤ y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz : c - d ≤ z) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    a * b * c - 3 * d ≤ x * y * z := by
  have e : x * y * z - a * b * c = (x - a) * (y * z) + a * ((y - b) * z) + a * b * (z - c) := by ring
  have hyz0 : 0 ≤ y * z := mul_nonneg hy0 hz0
  have hyz1 : y * z ≤ 1 := by nlinarith [mul_le_mul hy1 hz1 hz0 zero_le_one]
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  have hab1 : a * b ≤ 1 := by nlinarith [mul_le_mul ha1 hb1 hb zero_le_one]
  have t1 : -d ≤ (x - a) * (y * z) := by
    rcases le_total 0 (x - a) with h | h
    · nlinarith [mul_nonneg h hyz0]
    · have : (x - a) * 1 ≤ (x - a) * (y * z) := mul_le_mul_of_nonpos_left hyz1 h
      linarith
  have t2 : -d ≤ a * ((y - b) * z) := by
    have hw : -d ≤ (y - b) * z := by
      rcases le_total 0 (y - b) with h | h
      · nlinarith [mul_nonneg h hz0]
      · have : (y - b) * 1 ≤ (y - b) * z := mul_le_mul_of_nonpos_left hz1 h
        linarith
    rcases le_total 0 ((y - b) * z) with h | h
    · nlinarith [mul_nonneg ha h]
    · have : 1 * ((y - b) * z) ≤ a * ((y - b) * z) := mul_le_mul_of_nonpos_right ha1 h
      linarith
  have t3 : -d ≤ a * b * (z - c) := by
    rcases le_total 0 (z - c) with h | h
    · nlinarith [mul_nonneg hab0 h]
    · have : 1 * (z - c) ≤ a * b * (z - c) := mul_le_mul_of_nonpos_right hab1 h
      linarith
  linarith

omit [Fits] in
set_option maxHeartbeats 1600000 in
/-- **The kept part's `B`-count, from below.** For a cell `(i, j)` of `reg2` and a cell `k` that `keep` passes below it,
for every `δ > 0`, eventually in `q`: if `LargeQ q`, then `φ(q)⁻¹(keepK/K − δ)X ≤ Kk(g_B)`, where `X = x/log x`. -/
theorem Kk_gB_ge {i j k : ℕ} (hr : reg2 i j = true) (hkeep : keep i j k = true) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, LargeQ q →
      (q.totient : ℝ)⁻¹ * (((keepK i j k : ℝ) / K - δ) * (xq q / Real.log (xq q))) ≤ (parQ q).Kk (gB q) i j k := by
  have hD := SieveCert.DEN_pos'
  have hH : (0 : ℝ) < H := by exact_mod_cast SieveCert.H_pos
  have hepos : ∀ c : ℕ, (0 : ℝ) < SieveCert.e c := fun c => by exact_mod_cast SieveCert.e_pos c
  have h4HV : (4 : ℝ) * H ≤ V := by exact_mod_cast SieveRough.four_H_le_V
  have hVe : ∀ c : ℕ, (V : ℝ) ≤ SieveCert.e c := fun c => by
    have : V ≤ SieveCert.e c := by unfold SieveCert.e; omega
    exact_mod_cast this
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (DEN : ℝ) - SieveCert.e i - SieveCert.e j - SieveCert.e k := ⟨_, rfl⟩
  have hkc := hkeep
  simp only [keep, Bool.and_eq_true, decide_eq_true_eq] at hkc
  have hsum : (2 : ℝ) * ((SieveCert.e k : ℝ) + H) + SieveCert.e i + SieveCert.e j + 2 * H ≤ DEN := by
    have : ((2 * (SieveCert.e k + H) + SieveCert.e i + SieveCert.e j + 2 * H : ℕ) : ℝ) ≤ DEN := by
      exact_mod_cast hkc.1.2
    push_cast at this
    linarith
  have hγlo : 0 < γ - 3 * H := by rw [hγ]; linarith [hepos k]
  have hγ0 : 0 < γ := by linarith
  -- the cells' `h/(a + h)` and the share `κ ≥ keepK/K`
  have hh : ∀ c : ℕ, 0 ≤ (H : ℝ) / ((SieveCert.e c : ℝ) + H) ∧ (H : ℝ) / ((SieveCert.e c : ℝ) + H) ≤ 1 := fun c =>
    ⟨by have := hepos c; positivity, by rw [div_le_one (by linarith [hepos c])]; linarith [hepos c]⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (DEN : ℝ) / γ * ((H : ℝ) / ((SieveCert.e i : ℝ) + H) *
      ((H : ℝ) / ((SieveCert.e j : ℝ) + H)) * ((H : ℝ) / ((SieveCert.e k : ℝ) + H))) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκdef]; have := (hh i).1; have := (hh j).1; have := (hh k).1; positivity
  have hκ : (keepK i j k : ℝ) / K ≤ κ := by
    refine (SieveCert.keepK_le hkeep).trans (le_of_eq ?_)
    rw [hκdef, hγ]
    have := hepos i; have := hepos j; have := hepos k
    field_simp
  -- the margins `ε` and `d`
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2) (δ / (4 * (κ + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := by rw [hεdef]; exact min_le_left _ _
  have hεκ : ε * κ ≤ δ / 4 := by
    have h1 : ε ≤ δ / (4 * (κ + 1)) := by rw [hεdef]; exact min_le_right _ _
    have h2 : δ / (4 * (κ + 1)) * κ ≤ δ / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc ε * κ ≤ δ / (4 * (κ + 1)) * κ := mul_le_mul_of_nonneg_right h1 hκ0
      _ ≤ δ / 4 := h2
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = δ * γ / (12 * DEN) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdD : 3 * d * ((DEN : ℝ) / γ) = δ / 4 := by rw [hd]; field_simp; ring
  -- the eventual facts
  have eGi := evGe_cell_inv i d hd0
  have eGj := evGe_cell_inv j d hd0
  have eGk := evGe_cell_inv k d hd0
  have eLi := evLe_cell_inv i (1 / 2) (by norm_num)
  have eLj := evLe_cell_inv j (1 / 2) (by norm_num)
  have eLk := evLe_cell_inv k (1 / 2) (by norm_num)
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.1 (SieveMain.primes_dyadic_ge hε0)
  have hpnt : ∀ t ≥ Y0, (1 - ε) * (t / Real.log t) ≤ (pc t : ℝ) := fun t ht => hY0 t ht
  have eY := (tendsto_rpow_atTop (div_pos hγlo hD)).eventually_ge_atTop (max Y0 2)
  have hs1 : ((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + 3 * H) / DEN < 1 := by
    rw [div_lt_one hD]; rw [hγ] at hγlo; linarith
  have eE := err_ev (v := (V : ℝ) / DEN) (div_pos (by linarith) hD) hs1 (half_pos hδ)
  filter_upwards [SieveDrop.tendsto_xq.eventually (eGi.and (eGj.and (eGk.and (eLi.and (eLj.and (eLk.and eY)))))),
    eE] with q hxv hE hL
  obtain ⟨gi, gj, gk, li, lj, lk, hYq⟩ := hxv
  -- at `x = q^L`
  have hq0 : q ≠ 0 := by have := hL.q3; omega
  have hx1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hx0 : (0 : ℝ) < xq q := by linarith
  have hlx : 0 < Real.log (xq q) := Real.log_pos hx1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = xq q / Real.log (xq q) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = ((q.primeFactors).card : ℝ) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hω]; exact Nat.cast_nonneg _
  have hωle : ω ≤ Real.log q / Real.log 2 := by rw [hω]; exact card_primeFactors_le (by omega)
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((parQ q).z₀ : ℝ) := ⟨_, rfl⟩
  have hzx : xq q ^ ((V : ℝ) / DEN) ≤ z := by
    rw [hz]
    show xq q ^ ((V : ℝ) / DEN) ≤ ((⌈(q : ℝ) ^ a0⌉₊ : ℕ) : ℝ)
    have : (q : ℝ) ^ a0 = xq q ^ ((V : ℝ) / DEN) := by rw [xq, xpow]; rfl
    rw [← this]
    exact Nat.le_ceil _
  have hz0 : 0 < z := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hzx
  have hzp : ∀ c, ∀ p ∈ cellP (xq q) c, p.Prime ∧ z ≤ p := fun c p hp => by
    refine ⟨(Par.mem_cellP_iff.1 hp).1, ?_⟩
    rw [hz]
    exact_mod_cast z0_le hx1 hp
  have hS0 : ∀ c, 0 ≤ ∑ p ∈ cellP (xq q) c, 1 / (p : ℝ) := fun c => Finset.sum_nonneg fun _ _ => by positivity
  have hSle : ∀ c : ℕ, ∑ p ∈ cellP (xq q) c, 1 / (p : ℝ) ≤ (H : ℝ) / SieveCert.e c + 1 / 2 →
      ∑ p ∈ cellP (xq q) c, 1 / (p : ℝ) ≤ 1 := fun c h => by
    have : (H : ℝ) / SieveCert.e c ≤ 1 / 4 := by
      rw [div_le_iff₀ (hepos c)]; linarith [hVe c]
    linarith
  have hSi1 := hSle i li
  have hSj1 := hSle j lj
  have hSk1 := hSle k lk
  -- one triple at a time
  have hpt : ∀ p₁ ∈ cellP (xq q) i, ∀ p₂ ∈ cellP (xq q) j, ∀ q₁ ∈ cellP (xq q) k,
      ((pc (xq q / (p₁ * p₂ * q₁)) : ℝ) -
        ((if q₁ = p₁ then 1 else 0) + (if p₁ ∣ q then 1 else 0) + (if p₂ ∣ q then 1 else 0) +
          (if q₁ ∣ q then 1 else 0)) * (xq q / (p₁ * p₂ * q₁)) - (2 + ω)) ≤
      (if q₁ ≠ p₁ ∧ ¬ p₁ ∣ q ∧ ¬ p₂ ∣ q ∧ ¬ q₁ ∣ q then
          (pc (xq q / (p₁ * p₂ * q₁)) : ℝ) - 1 - ((q.primeFactors).card : ℝ) else 0) := by
    intro p₁ hp₁ p₂ hp₂ q₁ hq₁
    have hW : (0 : ℝ) < (p₁ : ℝ) * p₂ * q₁ := by
      have := (hzp i p₁ hp₁).1.pos; have := (hzp j p₂ hp₂).1.pos; have := (hzp k q₁ hq₁).1.pos; positivity
    have hy0 : 0 ≤ xq q / (p₁ * p₂ * q₁) := by positivity
    rw [← hω]
    obtain ⟨hI1, hI0⟩ := ind4 (q₁ = p₁) (p₁ ∣ q) (p₂ ∣ q) (q₁ ∣ q)
    refine pt_le _ (card_dyadic_le hy0) hy0 hω0 (fun hg => hI0 ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2⟩)
      fun hng => hI1 ?_
    by_contra hc
    push Not at hc
    exact hng ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  -- the main term
  have hmainS : (1 - ε) * ((DEN : ℝ) / γ) * X * ((∑ p ∈ cellP (xq q) i, 1 / (p : ℝ)) *
      (∑ p ∈ cellP (xq q) j, 1 / (p : ℝ)) * ∑ p ∈ cellP (xq q) k, 1 / (p : ℝ)) ≤
      ∑ p₁ ∈ cellP (xq q) i, ∑ p₂ ∈ cellP (xq q) j, ∑ q₁ ∈ cellP (xq q) k, (pc (xq q / (p₁ * p₂ * q₁)) : ℝ) := by
    rw [← sum3_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun p₁ hp₁ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p₂ hp₂ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q₁ hq₁ => ?_
    obtain ⟨hlo, hhi⟩ := y_bounds hx1 (Par.mem_cellP_iff.1 hp₁).2 (Par.mem_cellP_iff.1 hp₂).2
      (Par.mem_cellP_iff.1 hq₁).2
    rw [← hγ] at hlo hhi
    have hm := main_pt hx1 hγ0 hε1 (le_trans hYq hlo) hhi hpnt
    have e : (1 - ε) * ((DEN : ℝ) / γ) * X * (1 / (p₁ : ℝ) * (1 / (p₂ : ℝ)) * (1 / (q₁ : ℝ))) =
        (1 - ε) * ((DEN : ℝ) / γ) * (xq q / (p₁ * p₂ * q₁) / Real.log (xq q)) := by
      rw [hX]; field_simp
    rw [e]
    exact hm
  -- the bad triples
  have hbadS := bad_sum_le hx0.le hz0 hq0 (hzp i) (hzp j) (hzp k) hSi1 hSj1 hSk1 (s₁ := cellP (xq q) i)
    (s₂ := cellP (xq q) j) (s₃ := cellP (xq q) k)
  rw [← hω] at hbadS
  -- the count
  have hT3 := triples_card_le hx1 i j k
  have hcnt : ∑ _p₁ ∈ cellP (xq q) i, ∑ _p₂ ∈ cellP (xq q) j, ∑ _q₁ ∈ cellP (xq q) k, (2 + ω) =
      (2 + ω) * (((cellP (xq q) i).card : ℝ) * (cellP (xq q) j).card * (cellP (xq q) k).card) := by
    simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have herr : xq q * (1 + 3 * ω) / z + (2 + ω) * (((cellP (xq q) i).card : ℝ) * (cellP (xq q) j).card *
      (cellP (xq q) k).card) ≤ δ / 2 * X := by
    have e1 : xq q * (1 + 3 * ω) / z ≤ xq q * (1 + 3 * (Real.log q / Real.log 2)) / xq q ^ ((V : ℝ) / DEN) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hx0.le)
        (Real.rpow_pos_of_pos hx0 _) hzx
    have e2 : (2 + ω) * (((cellP (xq q) i).card : ℝ) * (cellP (xq q) j).card * (cellP (xq q) k).card) ≤
        (2 + Real.log q / Real.log 2) *
          (8 * xq q ^ (((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + 3 * H) / DEN)) :=
      mul_le_mul (by linarith only [hωle]) hT3 (by positivity) (by linarith only [hω0, hωle])
    rw [hX]
    linarith only [hE, e1, e2]
  -- the product of the cells' sums
  have hprodS : (H : ℝ) / ((SieveCert.e i : ℝ) + H) * ((H : ℝ) / ((SieveCert.e j : ℝ) + H)) *
      ((H : ℝ) / ((SieveCert.e k : ℝ) + H)) - 3 * d ≤ (∑ p ∈ cellP (xq q) i, 1 / (p : ℝ)) *
        (∑ p ∈ cellP (xq q) j, 1 / (p : ℝ)) * ∑ p ∈ cellP (xq q) k, 1 / (p : ℝ) := by
    obtain ⟨h0i, h1i⟩ := hh i
    obtain ⟨h0j, h1j⟩ := hh j
    obtain ⟨h0k, -⟩ := hh k
    exact prod3_ge h0i h1i h0j h1j hd0.le gi gj (hS0 j) hSj1 gk (hS0 k) hSk1
  have hmainK : (κ - δ / 2) * X ≤ (1 - ε) * ((DEN : ℝ) / γ) * X * ((∑ p ∈ cellP (xq q) i, 1 / (p : ℝ)) *
      (∑ p ∈ cellP (xq q) j, 1 / (p : ℝ)) * ∑ p ∈ cellP (xq q) k, 1 / (p : ℝ)) := by
    have h1 : κ - δ / 2 ≤ (1 - ε) * ((DEN : ℝ) / γ) * ((H : ℝ) / ((SieveCert.e i : ℝ) + H) *
        ((H : ℝ) / ((SieveCert.e j : ℝ) + H)) * ((H : ℝ) / ((SieveCert.e k : ℝ) + H)) - 3 * d) := by
      have e1 : (1 - ε) * ((DEN : ℝ) / γ) * ((H : ℝ) / ((SieveCert.e i : ℝ) + H) *
          ((H : ℝ) / ((SieveCert.e j : ℝ) + H)) * ((H : ℝ) / ((SieveCert.e k : ℝ) + H)) - 3 * d) =
          (1 - ε) * κ - (1 - ε) * (3 * d * ((DEN : ℝ) / γ)) := by rw [hκdef]; ring
      rw [e1, hdD]
      nlinarith only [hεκ, hε0, hε1, hδ, hκ0]
    have h2 := mul_le_mul_of_nonneg_left hprodS
      (show (0 : ℝ) ≤ (1 - ε) * ((DEN : ℝ) / γ) from mul_nonneg (by linarith) (by positivity))
    calc (κ - δ / 2) * X ≤ (1 - ε) * ((DEN : ℝ) / γ) * ((∑ p ∈ cellP (xq q) i, 1 / (p : ℝ)) *
          (∑ p ∈ cellP (xq q) j, 1 / (p : ℝ)) * ∑ p ∈ cellP (xq q) k, 1 / (p : ℝ)) * X :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hX0
      _ = _ := by ring
  -- assembling
  have hsumL := triples_ge hL hr hkeep
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  rw [← hX]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hφ) hsumL
  refine le_trans ?_ (Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ =>
    Finset.sum_le_sum fun q₁ hq₁ => hpt p₁ hp₁ p₂ hp₂ q₁ hq₁)
  simp only [Finset.sum_sub_distrib]
  rw [hcnt]
  have hκX : (keepK i j k : ℝ) / K * X ≤ κ * X := mul_le_mul_of_nonneg_right hκ hX0
  linarith only [hmainS, hbadS, hmainK, herr, hκX]

end SieveKeptB

#print axioms SieveKeptB.Kk_gB_ge
