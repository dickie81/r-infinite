/-
# Round 706: Type II for exact products of chains of primes

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `L`, `w₁` and `w₂` are a route's parameters (`SieveRoute.Route`) with `RouteOK`, and the bounds below
assume its Type II estimate (`hII : SieveRoute.TypeIIAt`). `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

`SieveChain.chainTL_bound` estimates the multiples `n ∈ (N₁, N₂]` of a chain's product with no prime factor below its
last entry. This file estimates the products themselves: the `n = ∏rt ∈ (N₁, N₂]`, summed over the chains `rt`, which
is the case of `chainTL_bound`'s proof with no prime besides the chain's (`t = 0` in `SieveChain.sum_TL_eq`).

* `tuples_zero`: `SieveRoughTuple.tuples z Y 0` is the empty tuple alone, for `Y ≥ 1`.
* `chainT0_bound`: fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ 1` with
  `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over `RTg (k′ + 1) N₂ Ω` with at most `J₀` comparisons, whose
  `m`-parts at `m = 0` are at most `Λ₁ log q`, each such tuple strictly decreasing, with entries at least `q^{e₀}`
  and `P₁ < ∏_{i∈S} rt_i ≤ P₂`, where `q^{w₁L} ≤ P₁` and `P₂ ≤ q^{w₂L}`. Then the `n = ∏rt ∈ (N₁, N₂]`, summed over
  `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.
* `famE`, `sum_dw_famE`, `famE_nonneg`: a family's exact terms `Σ_{rt} g(∏rt)[N₁ < ∏rt ≤ N₂]`, and `dw = gA − gB`
  on them.
* `T0_spec`: `chainT0_bound` on a family of at most `18` atoms with thresholds as in `SieveLeaves.ThrOK`, as a bound on
  `|famE(g_A) − famE(g_B)|`.

The proof of `chainT0_bound`: `SieveChain.sum_TL_eq` at `t = 0` regroups the chains by `m = ∏_S rt`, a squarefree `m`
of `Mset S P₁ P₂`, with the other primes as the variables `x` and the comparisons `cmpsTL`; `SieveChain.typeII_gcmp'`
bounds the result. If `S` is all the indices, no chain has `∏rt ∈ (N₁, N₂]`, since `∏rt = ∏_S rt ≤ P₂ < N₁`.

The file imports `SieveLeaves.lean`.
-/
import SieveLeaves

open Real Finset SieveFamily SieveTree SieveChain SieveDecomp SieveRoute SieveLeaves

namespace SieveExact

open Classical

/-- `SieveRoughTuple.tuples z Y 0` is the empty tuple alone, for `Y ≥ 1`. -/
theorem tuples_zero {z Y : ℕ} (hY : 1 ≤ Y) : SieveRoughTuple.tuples z Y 0 = {fun i => i.elim0} := by
  ext y
  simp only [SieveRoughTuple.tuples, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
  constructor
  · intro _
    funext i
    exact i.elim0
  · rintro rfl
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    simpa using hY

set_option maxHeartbeats 1600000 in
/-- **Exact products of chains with a product of some of their primes in the window.** Assume `RouteOK` and the
route's Type II estimate (`hII`). Fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for
`q ≥ 1` with `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `(k′ + 1)`-tuples of primes up to `N₂ = ⌊2q^L⌋`
that satisfy at most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each such tuple strictly
decreasing, with entries at least `q^{e₀}` and `P₁ < ∏_{i∈S} rt_i ≤ P₂`, where `q^{w₁L} ≤ P₁` and `P₂ ≤ q^{w₂L}`.
Then the products `n = ∏rt ∈ (N₁, N₂]`, summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. -/
theorem chainT0_bound [Route] [RouteOK] (hII : TypeIIAt) {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ}
    (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (S : Finset (Fin (k' + 1))) (Ω : List (GCmp (k' + 1))) (P₁ P₂ : ℕ), Ω.length ≤ J₀ →
      (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (q : ℝ) ^ (w₁ * L) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          (if ⌊(q : ℝ) ^ L⌋₊ < ∏ i, rt i ∧ ∏ i, rt i ≤ ⌊2 * (q : ℝ) ^ L⌋₊ then dw q a (∏ i, rt i) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₁, hq₁⟩ := typeII_gcmp' hII (k' + 1) (J₀ + 2) (half_pos he₀)
    (show (0 : ℝ) ≤ Λ₁ + 2 * L + 2 by linarith [L_pos])
  have hev1 := (tendsto_rpow_atTop (half_pos he₀)).eventually_ge_atTop (2 : ℝ)
  have hev3 := (tendsto_rpow_atTop
    (show (0 : ℝ) < L - w₂ * L by route_num)).eventually_ge_atTop (2 : ℝ)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (hev1.and hev3))
  refine ⟨δ, hδ, max (max q₁ q₂) 3, ?_⟩
  intro q _ hq a ha S Ω P₁ P₂ hΩlen hΩc hP₁ hP₂ hreg
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  obtain ⟨hqe, hq485⟩ := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by linarith) (by route_num)
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [this]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  -- `P₂ < N₁`
  have hP₂N₁ : P₂ < N₁ := by
    have h1 : (q : ℝ) ^ L = (q : ℝ) ^ (w₂ * L) *
        (q : ℝ) ^ (L - w₂ * L : ℝ) := by
      rw [← Real.rpow_add hq0]; ring_nf
    have h2 : (1 : ℝ) ≤ (q : ℝ) ^ (w₂ * L) := Real.one_le_rpow (by linarith) (by route_num)
    have h3 : (q : ℝ) ^ L - 1 < N₁ := Nat.sub_one_lt_floor _
    have h4 : (P₂ : ℝ) < N₁ := by nlinarith
    exact_mod_cast h4
  -- the products as chains with the empty cofactor tuple
  have hreg' : ∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
      StrictAnti rt ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂ := fun rt hp hΩ' =>
    ⟨(hreg rt hp hΩ').1, (hreg rt hp hΩ').2.2⟩
  have hterm : ∀ rt ∈ RTg (k' + 1) N₂ Ω,
      (if N₁ < ∏ i, rt i ∧ ∏ i, rt i ≤ N₂ then dw q a (∏ i, rt i) else 0) =
        ∑ y ∈ SieveRoughTuple.tuples (rt (Fin.last k')) N₂ 0,
          (if N₁ < (∏ i, rt i) * ∏ a, y a ∧ (∏ i, rt i) * ∏ a, y a ≤ N₂
            then dw q a ((∏ i, rt i) * ∏ a, y a) else 0) := by
    intro rt _
    rw [tuples_zero hN₂1, Finset.sum_singleton]
    simp
  rw [Finset.sum_congr rfl hterm, sum_TL_eq S Ω 0 hreg' hN₁1 hN₁N₂ le_rfl (le_trans hP₂N₁.le hN₁N₂) (dw q a)]
  rcases Nat.eq_zero_or_pos (0 + Sᶜ.card) with h0 | hpos
  · -- no primes left: `n = ∏_S rt ≤ P₂ < N₁`
    rw [Finset.sum_eq_zero, norm_zero]
    · positivity
    intro m hm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [ite_eq_right]
    intro hall
    exfalso
    rw [Mset, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨-, hmP₂⟩, hcard, hprodm⟩ := hm
    have hx1 : ∀ i, 1 ≤ x i := fun i => by
      exact (SieveTypeIIU.mem_primesLe.1 (Fintype.mem_piFinset.1 hx i)).2.one_lt.le
    have hf1 : ∀ u, 1 ≤ factS (S := S) m u := fun u =>
      (Nat.prime_of_mem_primeFactors (SieveStops2.desc_mem hcard u)).one_lt.le
    obtain ⟨-, -, -, hlo, -⟩ := (cmpsTL_holds (S := S) (t := 0) Ω (by exact_mod_cast hN₁1)
      (by exact_mod_cast hN₂1) m x hx1 hf1).1 hall
    have hSc : Sᶜ.card = 0 := by omega
    have hprod : (∏ i, (merge S (factS (S := S) m) (fun v => x (Fin.natAdd 0 v)) i : ℝ)) = m := by
      rw [prod_split (S := S)]
      simp only [merge_inl, merge_inr]
      have h1 : ∏ v : Fin Sᶜ.card, ((x (Fin.natAdd 0 v) : ℕ) : ℝ) = 1 := by
        rw [Fintype.prod_eq_one]
        intro v
        exact absurd v.isLt (by omega)
      rw [h1, mul_one]
      have : (∏ u, factS (S := S) m u : ℕ) = m := by
        unfold factS
        rw [SieveStops2.prod_desc hcard, hprodm]
      exact_mod_cast this
    rw [hprod, Fintype.prod_empty, mul_one] at hlo
    have : (m : ℝ) ≤ P₂ := by exact_mod_cast hmP₂
    have : (P₂ : ℝ) < N₁ := by exact_mod_cast hP₂N₁
    linarith
  · -- the Type II bound
    have hlog : ∀ (t' c : ℝ), 0 < t' → t' ≤ (q : ℝ) ^ c → Real.log t' ≤ c * Real.log q := fun t' c ht' h => by
      rw [← Real.log_rpow hq0]
      exact Real.log_le_log ht' h
    have hN₂q : (N₂ : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
      have h0 : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
      have h1 : 2 * (q : ℝ) ^ L ≤ (q : ℝ) ^ L * q := by
        have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ q by linarith) h0
        linarith
      linarith
    have hlN₂ := hlog N₂ (L + 1) (by exact_mod_cast hN₂1) hN₂q
    have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
    have hL0 := (L_pos : (0 : ℝ) < L)
    have hB0 : 0 ≤ (Λ₁ + L + 1) * Real.log q := by positivity
    have hBsplit : (Λ₁ + L + 1) * Real.log q = Λ₁ * Real.log q + (L + 1) * Real.log q := by
      ring
    have hLq : 0 ≤ (L + 1) * Real.log q := by positivity
    have hΛB : Λ₁ * Real.log q ≤ (Λ₁ + L + 1) * Real.log q := by rw [hBsplit]; linarith
    have hN₂B : Real.log (N₂ : ℝ) ≤ (Λ₁ + L + 1) * Real.log q := by rw [hBsplit]; linarith
    have hN₁R : (1 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hN₁1
    have hcle := cmpsTL_c_le S 0 Ω (N₁ := (N₁ : ℝ)) (N₂ := (N₂ : ℝ)) (P₁ := P₁) (P₂ := P₂)
      (B := (Λ₁ + L + 1) * Real.log q) (fun C hC => (hΩc C hC).trans hΛB) hB0 hN₁R hN₂B
    have h := hq₁ q hq1 a ha P₁ P₂ (Mset S P₁ P₂) (Finset.filter_subset _ _) hP₁ hP₂ (fun _ => 1)
      (fun _ => by simp) (0 + Sᶜ.card) hpos (by have := Finset.card_le_univ Sᶜ; simp at this; omega)
      (cmpsTL S 0 Ω N₁ N₂) ?_ ?_ ?_
    · simpa only [one_mul] using h
    · unfold cmpsTL
      rw [List.length_map]
      refine (length_fullTL_le k' 0 Ω N₁ N₂).trans ?_
      omega
    · intro C hC m hm
      have h1 := hcle C hC m hm
      have hm1 : 1 ≤ m := by
        have := (Finset.mem_Ioc.1 (Finset.filter_subset _ _ hm)).1
        have hP₁1 : (1 : ℝ) ≤ P₁ := le_trans (Real.one_le_rpow (by linarith) (by route_num)) hP₁
        have : (1 : ℕ) ≤ P₁ := by exact_mod_cast hP₁1
        omega
      have hmq : (m : ℝ) ≤ (q : ℝ) ^ L := by
        have h1 : (m : ℝ) ≤ P₂ := by exact_mod_cast (Finset.mem_Ioc.1 (Finset.filter_subset _ _ hm)).2
        have h2 : (q : ℝ) ^ (w₂ * L) ≤ (q : ℝ) ^ L :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by route_num)
        linarith
      have hlm := hlog m (L) (by exact_mod_cast hm1) hmq
      have : (Λ₁ + L + 1) * Real.log q + L * Real.log q =
          (Λ₁ + 2 * L + 1) * Real.log q := by ring
      nlinarith
    · intro m hm x hx hall
      rw [Mset, Finset.mem_filter] at hm
      obtain ⟨-, hcard, hprodm⟩ := hm
      have hx1 : ∀ i, 1 ≤ x i := fun i => (hx i).one_lt.le
      have hfp : ∀ u, (factS (S := S) m u).Prime := fun u =>
        Nat.prime_of_mem_primeFactors (SieveStops2.desc_mem hcard u)
      have hf1 : ∀ u, 1 ≤ factS (S := S) m u := fun u => (hfp u).one_lt.le
      obtain ⟨hΩ', -, -, -, hhi⟩ := (cmpsTL_holds (S := S) (t := 0) Ω (by exact_mod_cast hN₁1)
        (by exact_mod_cast hN₂1) m x hx1 hf1).1 hall
      set rt := merge S (factS (S := S) m) (fun v => x (Fin.natAdd 0 v)) with hrt
      have hrtp : ∀ i, (rt i).Prime := by
        intro i
        obtain ⟨y, rfl⟩ := (eS S).surjective i
        rcases y with u | v
        · rw [hrt, merge_inl]; exact hfp u
        · rw [hrt, merge_inr]; exact hx _
      obtain ⟨-, hge, -, -⟩ := hreg rt hrtp hΩ'
      have hprod : (m : ℝ) * ∏ i, (x i : ℝ) = (∏ i, (rt i : ℝ)) * ∏ a, (x (Fin.castAdd Sᶜ.card a) : ℝ) := by
        rw [prod_split (S := S) (fun i => (rt i : ℝ)), Fin.prod_univ_add]
        simp only [hrt, merge_inl, merge_inr]
        have : (∏ u, factS (S := S) m u : ℕ) = m := by
          unfold factS
          rw [SieveStops2.prod_desc hcard, hprodm]
        have h' : (∏ u, (factS (S := S) m u : ℝ)) = m := by exact_mod_cast this
        rw [h']
        ring
      refine ⟨fun i => ?_, by rw [hprod]; linarith⟩
      refine Fin.addCases (fun a => a.elim0) (fun v => ?_) i
      have h1 : rt (eS S (Sum.inr v)) = x (Fin.natAdd 0 v) := by rw [hrt, merge_inr]
      have := hge (eS S (Sum.inr v))
      rw [h1] at this
      linarith

/-! ### On families of atoms -/

/-- The exact terms of a family: `Σ_{rt} g(∏rt)` over the tuples with `N₁ < ∏rt ≤ N₂`. -/
noncomputable def famE (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) : ℝ :=
  ∑ rt ∈ F, if N₁ < ∏ i, rt i ∧ ∏ i, rt i ≤ N₂ then g (∏ i, rt i) else 0

theorem famE_nonneg {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (N₁ N₂ : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) :
    0 ≤ famE g N₁ N₂ F :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> first | exact hg _ | exact le_rfl

theorem sum_dw_famE (q : ℕ) (a : ZMod q) (N₁ N₂ : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) :
    ∑ rt ∈ F, (if N₁ < ∏ i, rt i ∧ ∏ i, rt i ≤ N₂ then SieveFamily.dw q a (∏ i, rt i) else 0) =
      ((famE (gA q a) N₁ N₂ F - famE (gB q) N₁ N₂ F : ℝ) : ℂ) := by
  unfold famE
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [dw_eq]
  split_ifs <;> push_cast <;> ring

variable [Route] (a₀ : ℝ)

/-- **Exact products, on a family of atoms** (`chainT0_bound`). Assume `RouteOK` and the route's Type II estimate
(`hII`). For `a₀ > 0` and `k'` there are `δ > 0` and `q₀` such that for `q ≥ 1` with `q ≥ q₀` and a unit `a` mod `q`:
a family of `(k' + 1)`-tuples of primes cut out by at most `18` atoms with thresholds as in `ThrOK`, each tuple
strictly decreasing, with entries at least `q^{a₀}` and `P₁ < ∏_{i∈S} rt_i ≤ P₂`, where `q^{w₁L} ≤ P₁` and
`P₂ ≤ q^{w₂L}`, has `|famE(g_A) − famE(g_B)| ≤ q^{L−δ}/φ(q)`. -/
theorem T0_spec [RouteOK] (hII : TypeIIAt) (ha₀ : 0 < a₀) (k' : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (spec : List (Atom (k' + 1))) (S : Finset (Fin (k' + 1))) (P₁ P₂ : ℕ), spec.length ≤ 18 → ThrOK q spec →
      (q : ℝ) ^ (w₁ * L) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a₀ ≤ rt i) ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂) →
      |famE (gA q a) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec) -
          famE (gB q) (N1 q) (N2 q) (famSet (k' + 1) (N2 q) spec)| ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨δ, hδ, q₀, hq₀⟩ := chainT0_bound hII ha₀ k' 18 (Λ₁ := L + 1) (by linarith [L_pos])
  refine ⟨δ, hδ, q₀, fun q _ hq a ha spec S P₁ P₂ hlen hthr hP₁ hP₂ hreg => ?_⟩
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have h := hq₀ q hq a ha S (spec.map Atom.toG) P₁ P₂ (by simpa using hlen) (c_le_of_thrOK hq1 hthr) hP₁ hP₂
    fun rt hp hΩ => hreg rt hp ((holds_iff_sem hthr hp).1 hΩ)
  rwa [RTg_eq_of_thrOK hthr, sum_dw_famE, Complex.norm_real, Real.norm_eq_abs] at h

end SieveExact

#print axioms SieveExact.chainT0_bound
#print axioms SieveExact.T0_spec
