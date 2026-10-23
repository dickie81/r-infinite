/-
# Round 707: the kept parts' leaves at `x = q^L`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK` and `Fits` where the Lean takes them),
`parQ q` is the decomposition's parameters at `x = q^L`, and `LargeQ q` the facts about `q` that the proofs use.

* `T0at`: `SieveExact.T0_spec`'s estimate at `q` for four primes, with error `E`.
* `thrOK_KS`, `len_KS`: the sorted families' atoms have thresholds in `[1, q^{L+1}]` and number `14`.
* `lf_KS`: for `LargeQ q`, `E ≥ 0` and `T0at q a E`, a sorted family `KS a b i j k` with `a, b < 3` distinct and a cell
  `k` that `keep` passes below `(i, j)` has `|famE(g_A) − famE(g_B)| ≤ E`. The box `(i, j, k)` is surely evaluable, so
  a set `T` of the roles `p₁, p₂, q₁` has its sums inside `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)` on the box: in the lower
  window `T`'s product lies in `(P₁, P₂]`; in the upper window the product of the other primes lies in
  `(N₁/W₁, N₂/(X′ + 1)]`, since the four primes' product lies in `(N₁, N₂]`.
* `lf_Kk`: such a cell's kept part `Kk(i, j, k)` has `|A − B| ≤ 3E` (`SieveBuch.Par.Kk_eq`).
* `Leaves.mono`, `leaves_ev2`: given the route's Type II estimate (`hII`), for `η > 0` there are `δ > 0` and `q₀` such
  that for `q ≥ q₀` and `a` a unit mod `q`, `LargeQ q`, the leaves of `SieveQ.leaves_ev` and the kept leaves of
  `SieveBuch2.lean` are within `Err η δ q`.

The file imports `SieveQ.lean` and `SieveBuch2.lean`.
-/
import SieveQ
import SieveBuch2

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRoute SieveExact
open SieveCert (V DEN H U1 U2 cand dec keep reg2 surelyEval cell inside)

namespace SieveKeptLeaf

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-- The exact products' estimate at `q` for four primes, with error `E`. -/
def T0at (q : ℕ) (a : ZMod q) (E : ℝ) : Prop :=
  ∀ (spec : List (Atom 4)) (S : Finset (Fin 4)) (P₁ P₂ : ℕ), spec.length ≤ 18 → ThrOK q spec →
    (q : ℝ) ^ (w₁ * L) ≤ P₁ → (P₂ : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
    (∀ rt : Fin 4 → ℕ, (∀ i, (rt i).Prime) → (∀ A ∈ spec, A.sem rt) →
      StrictAnti rt ∧ (∀ i, (q : ℝ) ^ a0 ≤ rt i) ∧ P₁ < ∏ i ∈ S, rt i ∧ ∏ i ∈ S, rt i ≤ P₂) →
    |famE (gA q a) (N1 q) (N2 q) (famSet 4 (N2 q) spec) - famE (gB q) (N1 q) (N2 q) (famSet 4 (N2 q) spec)| ≤ E

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem T0at.mono {q : ℕ} {a : ZMod q} {E E' : ℝ} (h : T0at q a E) (hE : E ≤ E') : T0at q a E' :=
  fun spec S P₁ P₂ h1 h2 h3 h4 h5 => (h spec S P₁ P₂ h1 h2 h3 h4 h5).trans hE

omit [RouteOK] [SieveCert.GridOK] [Fits] in
theorem len_KS (q : ℕ) (a b : Fin 4) (i j k : ℕ) : ((parQ q).KS a b i j k).length ≤ 18 := by
  simp [Par.KS, cellA]

theorem thrOK_KS {q : ℕ} (hL : LargeQ q) (a b : Fin 4) {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hk : k < SieveCert.n) : ThrOK q ((parQ q).KS a b i j k) := by
  have hq : 1 ≤ q := SieveQ.q1 hL
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqL1 : (1 : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := Real.one_le_rpow hq1 (by route_num)
  obtain ⟨hz, ht, -⟩ := thr_bounds hL
  have hN1 : (1 : ℝ) ≤ (N1 q : ℝ) := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 (by route_num)
    exact_mod_cast Nat.le_floor (by exact_mod_cast this)
  have hN2 : (N2 q : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
    have h1 := N2_le q
    have hq0 : (0 : ℝ) < q := by linarith
    rw [Real.rpow_add hq0, Real.rpow_one]
    have h0 : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
    have : 2 * (q : ℝ) ^ L ≤ (q : ℝ) ^ L * q := by
      have h3 : (3 : ℝ) ≤ q := by exact_mod_cast hL.q3
      nlinarith
    linarith
  have hN12 : (N1 q : ℝ) ≤ (N2 q : ℝ) := by exact_mod_cast Nat.floor_le_floor (by
    have : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
    linarith)
  unfold Par.KS
  refine thrOK_append (thrOK_append (thrOK_append ?_ (thrOK_cellA hq a hi)) (thrOK_cellA hq 3 hj))
    (thrOK_cellA hq b hk)
  intro A hA
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨le_rfl, hqL1⟩
  · exact ⟨le_rfl, hqL1⟩
  · exact ⟨le_rfl, hqL1⟩
  · exact hz
  · exact ht
  · exact hz
  · exact ⟨hN1, hN12.trans hN2⟩
  · exact ⟨hN1.trans hN12, hN2⟩

/-- The roles `p₁, p₂, q₁` of a sorted family, at the positions `a`, `3`, `b`. -/
def roles (a b : Fin 4) : Fin 3 → Fin 4 := ![a, 3, b]

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
theorem roles_inj {a b : Fin 4} (ha : a < 3) (hb : b < 3) (hab : a ≠ b) : Function.Injective (roles a b) := by
  have ha' : a ≠ 3 := ne_of_lt ha
  have hb' : b ≠ 3 := ne_of_lt hb
  intro s t h
  fin_cases s <;> fin_cases t <;> simp only [roles] at h
  all_goals first
    | rfl
    | exact absurd h ha'
    | exact absurd h.symm ha'
    | exact absurd h hb'
    | exact absurd h.symm hb'
    | exact absurd h hab
    | exact absurd h.symm hab

/-- **A sorted family's leaf.** For `LargeQ q`, `E ≥ 0` and `T0at q a E`, a sorted family `KS a b i j k` with `a, b < 3`
distinct and a cell `k` that `keep` passes below `(i, j)` has `|famE(g_A) − famE(g_B)| ≤ E`. -/
theorem lf_KS {q : ℕ} (hL : LargeQ q) {a : ZMod q} {E : ℝ} (hT : T0at q a E) {pa pb : Fin 4} (ha : pa < 3)
    (hb : pb < 3) (hab : pa ≠ pb) {i j k : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hk : k < SieveCert.n)
    (hkeep : keep i j k = true) :
    |famE (gA q a) (N1 q) (N2 q) (famSet 4 (N2 q) ((parQ q).KS pa pb i j k)) -
        famE (gB q) (N1 q) (N2 q) (famSet 4 (N2 q) ((parQ q).KS pa pb i j k))| ≤ E := by
  have hq1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  set c : Fin 3 → ℕ := ![i, j, k] with hc
  have hsE : surelyEval (List.ofFn fun t => cell (c t)) = true := by
    simp only [keep, Bool.and_eq_true] at hkeep
    simpa [hc, List.ofFn_succ] using hkeep.2
  obtain ⟨T, hT'⟩ := exists_inside _ hsE
  set ρ := roles pa pb with hρ
  have hρi : Function.Injective ρ := roles_inj ha hb hab
  -- the facts of a tuple of the family
  have hfacts : ∀ rt : Fin 4 → ℕ, (∀ t, (rt t).Prime) → (∀ A ∈ (parQ q).KS pa pb i j k, A.sem rt) →
      StrictAnti rt ∧ (∀ t, (parQ q).z₀ ≤ rt t) ∧ (∀ t, InC (xq q) (c t) (rt (ρ t))) ∧
        N1 q < ∏ t, rt t ∧ ∏ t, rt t ≤ N2 q := by
    intro rt hp hs
    have hrt := mem_famSet_sum hp hs
    rw [Par.mem_KS] at hrt
    obtain ⟨-, ⟨h01, h12, h23⟩, ⟨hz, -, hz3⟩, ⟨hlo, hhi⟩, ⟨hCi, hCj, hCk⟩⟩ := hrt
    have hsa : StrictAnti rt := by
      rw [Fin.strictAnti_iff_succ_lt]
      intro u
      fin_cases u
      · exact h01
      · exact h12
      · exact h23
    refine ⟨hsa, fun t => ?_, fun t => ?_, hlo, hhi⟩
    · have : rt 3 ≤ rt t := hsa.antitone (Fin.le_last t)
      exact hz3.trans this
    · fin_cases t
      · exact hCi
      · exact hCj
      · exact hCk
  have hprodT : ∀ rt : Fin 4 → ℕ, ∏ t ∈ T, rt (ρ t) = ∏ s ∈ T.map ⟨ρ, hρi⟩, rt s := fun rt => by
    rw [Finset.prod_map]
    rfl
  simp only [inside, cell, Bool.or_eq_true, Bool.and_eq_true] at hT'
  rcases hT' with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> replace hlo := of_decide_eq_true hlo <;>
    replace hhi := of_decide_eq_true hhi
  · -- the lower window: `T`'s product in `(P₁, P₂]`
    refine hT _ (T.map ⟨ρ, hρi⟩) (P1 q) (P2 q) (len_KS q pa pb i j k) (thrOK_KS hL pa pb hi hj hk) (P1_ok hL)
      (P2_ok hL) fun rt hp hs => ?_
    obtain ⟨hsa, hz, hC, -, -⟩ := hfacts rt hp hs
    refine ⟨hsa, ha0_of hz, ?_, ?_⟩
    · rw [← hprodT]
      exact window_lo (rt := fun t => rt (ρ t)) hq1 hC hlo
    · rw [← hprodT]
      exact window_hi (rt := fun t => rt (ρ t)) hq1 hC hhi
  · -- the upper window: the other primes' product in `(N₁/W₁, N₂/(X′ + 1)]`
    refine hT _ (T.map ⟨ρ, hρi⟩)ᶜ (N1 q / SieveQ.W1 q) (N2 q / ((parQ q).Xp + 1)) (len_KS q pa pb i j k)
      (thrOK_KS hL pa pb hi hj hk) (W1_div hL) (W0_div hL) fun rt hp hs => ?_
    obtain ⟨hsa, hz, hC, hNlo, hNhi⟩ := hfacts rt hp hs
    refine ⟨hsa, ha0_of hz, ?_, ?_⟩
    · have hW : ∏ s ∈ T.map ⟨ρ, hρi⟩, rt s ≤ SieveQ.W1 q := by
        rw [← hprodT]
        exact window_hi (rt := fun t => rt (ρ t)) hq1 hC hhi
      have hsplit := Finset.prod_compl_mul_prod (T.map ⟨ρ, hρi⟩) rt
      have hW1 : 1 ≤ SieveQ.W1 q := W1_pos hL
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc N1 q < ∏ t, rt t := hNlo
        _ = (∏ s ∈ (T.map ⟨ρ, hρi⟩)ᶜ, rt s) * ∏ s ∈ T.map ⟨ρ, hρi⟩, rt s := hsplit.symm
        _ ≤ (∏ s ∈ (T.map ⟨ρ, hρi⟩)ᶜ, rt s) * SieveQ.W1 q := Nat.mul_le_mul_left _ hW
    · have hX : (parQ q).Xp < ∏ s ∈ T.map ⟨ρ, hρi⟩, rt s := by
        rw [← hprodT, Xp_eq]
        exact window_lo (rt := fun t => rt (ρ t)) hq1 hC hlo
      have hsplit := Finset.prod_compl_mul_prod (T.map ⟨ρ, hρi⟩) rt
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc (∏ s ∈ (T.map ⟨ρ, hρi⟩)ᶜ, rt s) * ((parQ q).Xp + 1)
          ≤ (∏ s ∈ (T.map ⟨ρ, hρi⟩)ᶜ, rt s) * ∏ s ∈ T.map ⟨ρ, hρi⟩, rt s := Nat.mul_le_mul_left _ hX
        _ = ∏ t, rt t := hsplit
        _ ≤ N2 q := hNhi

/-- **A kept part's leaf.** For `LargeQ q`, `E ≥ 0` and `T0at q a E`, a cell `k` that `keep` passes below `(i, j)` has
`|Kk(g_A) − Kk(g_B)| ≤ 3E`. -/
theorem lf_Kk {q : ℕ} (hL : LargeQ q) {a : ZMod q} {E : ℝ} (hT : T0at q a E) {i j k : ℕ} (hi : i < SieveCert.n)
    (hj : j < SieveCert.n) (hk : k < SieveCert.n) (hkeep : keep i j k = true) :
    |(parQ q).Kk (gA q a) i j k - (parQ q).Kk (gB q) i j k| ≤ 3 * E := by
  have hq1 : (1 : ℝ) < (parQ q).x := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hjk : SieveCert.e j + H ≤ SieveCert.e k := by
    simp only [keep, Bool.and_eq_true, decide_eq_true_eq] at hkeep
    exact hkeep.1.1
  rw [(parQ q).Kk_eq hq1 _ hjk, (parQ q).Kk_eq hq1 _ hjk, show (parQ q).N₁ = N1 q from rfl,
    show (parQ q).N₂ = N2 q from rfl]
  have h1 := lf_KS hL hT (pa := 0) (pb := 2) (by decide) (by decide) (by decide) hi hj hk hkeep
  have h2 := lf_KS hL hT (pa := 1) (pb := 2) (by decide) (by decide) (by decide) hi hj hk hkeep
  have h3 := lf_KS hL hT (pa := 2) (pb := 1) (by decide) (by decide) (by decide) hi hj hk hkeep
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem Leaves.mono {P : Par} {gA gB : ℕ → ℝ} {E E' : ℝ} (h : P.Leaves gA gB E) (hE : E ≤ E') :
    P.Leaves gA gB E' :=
  ⟨h.j0.trans hE, fun i hi hW => (h.e1 i hi hW).trans hE, fun i hi hW => (h.p1 i hi hW).trans hE,
    fun i hi j hj hc hd => (h.e2 i hi j hj hc hd).trans hE, fun i hi j hj hc hd => (h.p2 i hi j hj hc hd).trans hE,
    fun i hi hW j hj hc hs => (h.e2' i hi hW j hj hc hs).trans hE,
    fun i hi j hj hc hd k hk h1 h2 => (h.e3 i hi j hj hc hd k hk h1 h2).trans hE,
    fun i hi j hj hc hd k hk h1 h2 => (h.p3 i hi j hj hc hd k hk h1 h2).trans hE,
    fun i hi j hj hc hd k hk h1 h2 => (h.e3' i hi j hj hc hd k hk h1 h2).trans hE,
    fun i hi j hj hc hd k hk h1 h2 l hl h3 h4 => (h.e4 i hi j hj hc hd k hk h1 h2 l hl h3 h4).trans hE⟩

/-- **The leaves and the kept leaves, for large `q`.** For a route with `RouteOK` and a grid with `GridOK` that fit
(`Fits`), given the route's Type II estimate (`hII`), for `η > 0` there are `δ > 0` and `q₀` such that for `q ≥ q₀` and
`a` a unit mod `q`, `q` is large, every leaf of the tree at `x = q^L` is within `Err η δ q`, and every kept part's
`A` and `B` are within `3·Err η δ q`. -/
theorem leaves_ev2 (hII : TypeIIAt) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      LargeQ q ∧ (parQ q).Leaves (gA q a) (gB q) (Err η δ q) ∧ (parQ q).KLeaves (gA q a) (gB q) (Err η δ q) := by
  obtain ⟨d1, hd1, q1, h1⟩ := leaves_ev hII hη
  obtain ⟨d2, hd2, q2, h2⟩ := T0_spec a0 hII a0_pos 3
  refine ⟨min d1 d2, lt_min hd1 hd2, q1 + q2, fun q _ hq a ha => ?_⟩
  obtain ⟨hLq, Lv⟩ := h1 q (by omega) a ha
  have hq1 : 1 ≤ q := SieveQ.q1 hLq
  have hE1 : Err η d1 q ≤ Err η (min d1 d2) q := by
    have h := Err_ge' (η := η) (min_le_left d1 d2) q hq1
    unfold Err at h ⊢
    linarith
  have tT : T0at q a (Err η (min d1 d2) q) := T0at.mono (h2 q (by omega) a ha)
    (Err_ge hη (min_le_right d1 d2) q hq1)
  refine ⟨hLq, Leaves.mono Lv hE1, fun i hi j hj _ _ _ k hk hkeep => lf_Kk hLq tT hi hj hk hkeep⟩

end SieveKeptLeaf

#print axioms SieveKeptLeaf.leaves_ev2
