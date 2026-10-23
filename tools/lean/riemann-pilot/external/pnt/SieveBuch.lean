/-
# Round 604: the decomposition to depth 4, with the certificate's classification (milestone M8)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `Par` holds `x`, the sieve's floor `z₀`, its top `z_top`, Proposition 6's `X'` and the range
`(N₁, N₂]`; `Good` is what the decomposition needs of them (`SieveQ.good_of_large` proves it at `x = q^L` for large
`q`). For weights `g`, `T g = S_g(z_top)` and `J0 g = S_g(z₀)` count the `n ∈ (N₁, N₂]` with no prime factor below
`z_top` and `z₀`, weighted by `g`. The families of the tree are lists of `SieveDecomp` atoms: `S1` (`p₁ ∈ [z₀, z_top)`),
its cells `S1c i`, the extensions `S2 i`, `S3 i j`, `S4 i j k` (one more prime in `[z₀, rt_last)`), their cells
`S2c`, `S3c`, `S4c`, and the splits `S2le`/`S2gt`, `S3le`/`S3gt` at the product `X'`.

* `T_eq`, `I_S1` … `I_S4`: for `P.Good`, the exact identities of the decomposition,
  `S(A, z_top) = S(A, z₀) − Σ_{p₁} S(A_{p₁}, p₁)` and so on to depth 4: the cells of each new prime, Buchstab's identity
  on the cells that are decomposed, and the splits at `X'`.
* `I_S3c_vanish`, `I_S4c_vanish_lt`, `I_S4c_vanish_reg`: for `P.Good`, the cells outside `SieveCert.inKK` at depth 3,
  and at depth 4 the cells `l > k` and those outside the region, contribute `0`.
* `D1`: the dropped terms, as the certificate drops them. At depth 2 the candidate cells that are not decomposed
  (`cand ∧ ¬dec`) and the corner cells (`¬cand ∧ ¬surelyEval`), below a cell `i` of `p₁` outside the window
  (`inW`); at depth 4 the counted cells (`counted4`, `l ≤ k`) below the cells of depth 3 that are split.
* `Leaves`: the estimates the leaves need, each `|A − B| ≤ Err`: the evaluated families (`e1`, `e2`, `e2'`, `e3`,
  `e3'`, `e4`) and the families of Proposition 6 (`j0` for `S(z₀)`, `p1`, `p2`, `p3`).
* `decomp`: for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, and leaves within `Err ≥ 0`,
  `S_{g_A}(z_top) ≥ S_{g_B}(z_top) − D1(g_B) − (1 + n(1 + n(n(n + 2) + 2)))·Err`.

This is the decomposition of `frontier/linnik/SIEVE-ROUTE.md` §6, M8 of §13, with M7's classification by cells (the grid
of `SieveCert.Grid`: `n` cells a side, of side `H/DEN`, starting at `V/DEN = u₂ − u₁`; the identities `I_S1` … `I_S4`,
the levels and `decomp` take `GridOK`). At depth 1 a cell inside the window is evaluated, the others decomposed. At
depth 2 a candidate cell that `dec` allows is split at `X'` (above evaluated, below decomposed), a candidate cell not
allowed is dropped, and a non-candidate cell is evaluated when surely evaluable and dropped otherwise (the corner). At
depth 3 a cell of `inKK` is split at `X'` when not surely evaluable and evaluated otherwise. At depth 4 a counted cell
is dropped, and the rest are evaluated or vanish.

The proof of `decomp`: `lvl4`, `lvl3`, `lvl2`, `lvl1`, one level at a time. A dropped term has `A ≥ 0` and costs its
`B`-version; a term with sign `−` is bounded above, so it is evaluated or decomposed, never dropped.

Round 607 made the certificate's grid a parameter (`SieveCert.Grid`, with `GridOK` where the Lean takes it); the
statements of earlier rounds are the case `SieveCert.grid2333`.


The file imports `SieveDecomp.lean`.
-/
import SieveDecomp

open Real Finset SieveFamily SieveChain SieveDecomp
open SieveCert (V DEN H U1 U2 cand dec inKK ne3 counted4 surelyEval cell)

namespace SieveBuch

open Classical

/-- The parameters of the decomposition: `x`, the sieve's floor `z₀`, its top `z_top`, Proposition 6's `X'`, and the
range `(N₁, N₂]`. -/
structure Par where
  x : ℝ
  z₀ : ℕ
  ztop : ℕ
  Xp : ℕ
  N₁ : ℕ
  N₂ : ℕ

namespace Par

variable (P : Par) [SieveCert.Grid]

/-! ### The families of the tree -/

/-- Depth 1: `p₁ ∈ [z₀, z_top)`. -/
noncomputable def S1 : List (Atom 1) := [Atom.ge 0 P.z₀, Atom.lt 0 P.ztop]
/-- Depth 1, `p₁` in the cell `i`. -/
noncomputable def S1c (i : ℕ) : List (Atom 1) := P.S1 ++ cellA 0 P.x i
/-- Depth 2 below the cell `i`. -/
noncomputable def S2 (i : ℕ) : List (Atom 2) := extS (P.z₀ : ℝ) (P.S1c i)
/-- Depth 2, in the cell `(i, j)`. -/
noncomputable def S2c (i j : ℕ) : List (Atom 2) := P.S2 i ++ cellA 1 P.x j
/-- Depth 2, in the cell `(i, j)`, with `p₁p₂ ≤ X'`. -/
noncomputable def S2le (i j : ℕ) : List (Atom 2) := P.S2c i j ++ [Atom.prodLe Finset.univ P.Xp]
/-- Depth 2, in the cell `(i, j)`, with `p₁p₂ > X'`. -/
noncomputable def S2gt (i j : ℕ) : List (Atom 2) := P.S2c i j ++ [Atom.prodGt Finset.univ P.Xp]
/-- Depth 3 below `(i, j)`, `p₁p₂ ≤ X'`. -/
noncomputable def S3 (i j : ℕ) : List (Atom 3) := extS (P.z₀ : ℝ) (P.S2le i j)
/-- Depth 3, in the cell `(i, j, k)`. -/
noncomputable def S3c (i j k : ℕ) : List (Atom 3) := P.S3 i j ++ cellA 2 P.x k
/-- Depth 3, in the cell `(i, j, k)`, with `p₁p₂p₃ ≤ X'`. -/
noncomputable def S3le (i j k : ℕ) : List (Atom 3) := P.S3c i j k ++ [Atom.prodLe Finset.univ P.Xp]
/-- Depth 3, in the cell `(i, j, k)`, with `p₁p₂p₃ > X'`. -/
noncomputable def S3gt (i j k : ℕ) : List (Atom 3) := P.S3c i j k ++ [Atom.prodGt Finset.univ P.Xp]
/-- Depth 4 below `(i, j, k)`, `p₁p₂p₃ ≤ X'`. -/
noncomputable def S4 (i j k : ℕ) : List (Atom 4) := extS (P.z₀ : ℝ) (P.S3le i j k)
/-- Depth 4, in the cell `(i, j, k, l)`. -/
noncomputable def S4c (i j k l : ℕ) : List (Atom 4) := P.S4 i j k ++ cellA 3 P.x l

/-- The terms `S(A_{∏rt}, rt_last)` of a family. -/
noncomputable def I {k' : ℕ} (g : ℕ → ℝ) (spec : List (Atom (k' + 1))) : ℝ :=
  famI g P.N₁ P.N₂ (famSet (k' + 1) P.N₂ spec)

/-- The terms `S(A_{∏rt}, z₀)` of a family. -/
noncomputable def J {k : ℕ} (g : ℕ → ℝ) (spec : List (Atom k)) : ℝ :=
  famJ g P.N₁ P.N₂ P.z₀ (famSet k P.N₂ spec)

/-- `S(A, z_top)`. -/
noncomputable def T (g : ℕ → ℝ) : ℝ := ∑ m ∈ Ioc P.N₁ P.N₂, g m * (if SieveTree.rough P.ztop m then 1 else 0)

/-- `S(A, z₀)`. -/
noncomputable def J0 (g : ℕ → ℝ) : ℝ := ∑ m ∈ Ioc P.N₁ P.N₂, g m * (if SieveTree.rough P.z₀ m then 1 else 0)

/-- What the decomposition needs of the parameters (they hold at `SieveQ.parQ q` for large `q`,
`SieveQ.good_of_large`). -/
structure Good : Prop where
  hx : 1 < P.x
  hz₀ : P.x ^ ((V : ℝ) / DEN) ≤ P.z₀
  hztop : (P.ztop : ℝ) ≤ P.x ^ (((V : ℝ) + SieveCert.n * H) / DEN)
  hz₀top : P.z₀ ≤ P.ztop
  htopN : P.ztop ≤ P.N₂ + 1
  hXN : (P.Xp : ℝ) * Real.sqrt P.Xp ≤ P.N₁
  hN₂ : (P.N₂ : ℝ) < P.x ^ (((DEN : ℝ) + 1) / DEN)

/-! ### Chains -/

omit [SieveCert.Grid] in
theorem chain_S1 {Y : ℕ} : ∀ rt ∈ famSet 1 Y P.S1, Chain P.z₀ P.ztop rt := by
  intro rt hrt
  have h0 : ((P.z₀ : ℕ) : ℝ) ≤ rt 0 := sem_of_mem hrt (A := Atom.ge 0 P.z₀) (by simp [S1])
  have h1 : (rt 0 : ℝ) < P.ztop := sem_of_mem hrt (A := Atom.lt 0 P.ztop) (by simp [S1])
  refine ⟨fun a b hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _), fun i => ?_, fun i => ?_⟩
  · rw [Fin.fin_one_eq_zero i]; exact_mod_cast h0
  · rw [Fin.fin_one_eq_zero i]; exact_mod_cast h1

theorem chain_S1c {Y : ℕ} (i : ℕ) : ∀ rt ∈ famSet 1 Y (P.S1c i), Chain P.z₀ P.ztop rt :=
  chain_append _ P.chain_S1
theorem chain_S2 {Y : ℕ} (i : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2 i), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S1c i)
theorem chain_S2c {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2c i j), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S2 i)
theorem chain_S2le {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2le i j), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S2c i j)
theorem chain_S2gt {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 2 Y (P.S2gt i j), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S2c i j)
theorem chain_S3 {Y : ℕ} (i j : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3 i j), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S2le i j)
theorem chain_S3c {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3c i j k), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S3 i j)
theorem chain_S3le {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3le i j k), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S3c i j k)
theorem chain_S3gt {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 3 Y (P.S3gt i j k), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S3c i j k)
theorem chain_S4 {Y : ℕ} (i j k : ℕ) : ∀ rt ∈ famSet 4 Y (P.S4 i j k), Chain P.z₀ P.ztop rt :=
  chain_ext (P.chain_S3le i j k)
theorem chain_S4c {Y : ℕ} (i j k l : ℕ) : ∀ rt ∈ famSet 4 Y (P.S4c i j k l), Chain P.z₀ P.ztop rt :=
  chain_append _ (P.chain_S4 i j k)

variable {P}

/-- For `P.Good`, a chain's primes lie in the grid. -/
theorem range_of_chain (G : P.Good) {k : ℕ} {rt : Fin k → ℕ} (h : Chain P.z₀ P.ztop rt) (t : Fin k) :
    P.x ^ ((V : ℝ) / DEN) ≤ rt t ∧ (rt t : ℝ) < P.x ^ (((V : ℝ) + SieveCert.n * H) / DEN) := by
  refine ⟨G.hz₀.trans (by exact_mod_cast h.2.1 t), lt_of_lt_of_le (by exact_mod_cast h.2.2 t) G.hztop⟩

omit [SieveCert.Grid] in
theorem last_le_of_chain {k' : ℕ} {rt : Fin (k' + 1) → ℕ} (h : Chain P.z₀ P.ztop rt) :
    (∀ i, rt (Fin.last k') ≤ rt i) ∧ P.z₀ ≤ rt (Fin.last k') :=
  ⟨fun i => h.1.antitone (Fin.le_last i), h.2.1 _⟩

/-! ### The identities of the tree, depth by depth -/

/-- **Depth 0.** For `P.Good`, `S(A, z_top) = S(A, z₀) − Σ_{z₀ ≤ p₁ < z_top} S(A_{p₁}, p₁)`. -/
theorem T_eq (G : P.Good) (g : ℕ → ℝ) : P.T g = P.J0 g - P.I g P.S1 := by
  have hpt : ∀ m ∈ Ioc P.N₁ P.N₂, g m * (if SieveTree.rough P.ztop m then 1 else 0) =
      g m * (if SieveTree.rough P.z₀ m then 1 else 0) -
        ∑ p ∈ SieveTree.primesIco P.z₀ P.ztop, g m * (if p ∣ m ∧ SieveTree.rough p m then 1 else 0) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Ioc.1 hm).1; omega
    have h := buchstab_pt (W := 1) hm0 G.hz₀top (fun p hp hd => absurd (Nat.dvd_one.1 hd) hp.one_lt.ne')
    simp only [one_dvd, true_and, one_mul] at h
    rw [h, mul_sub, Finset.mul_sum]
  unfold T J0 I famI
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_nbij' (fun p => fun _ => p) (fun rt => rt 0) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [SieveTree.mem_primesIco] at hp
    rw [mem_famSet]
    refine ⟨fun _ => ⟨by have := G.htopN; omega, hp.2.2⟩, ?_⟩
    simp only [S1, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, Atom.sem_ge,
      Atom.sem_lt, Nat.cast_le, Nat.cast_lt]
    exact ⟨hp.1, hp.2.1⟩
  · intro rt hrt
    have hc := P.chain_S1 rt hrt
    rw [SieveTree.mem_primesIco]
    exact ⟨hc.2.1 0, hc.2.2 0, ((mem_famSet.1 hrt).1 0).2⟩
  · intro p _
    rfl
  · intro rt _
    funext i
    rw [Fin.fin_one_eq_zero i]
  · intro p _
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_add, pow_one]

/-- **Depth 1**, for a grid with `GridOK` and `P.Good`: the cells of `p₁`. -/
theorem I_S1 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) : P.I g P.S1 = ∑ i ∈ range SieveCert.n, P.I g (P.S1c i) :=
  famI_cells g P.N₁ P.N₂ G.hx P.S1 0 fun rt hrt => range_of_chain G (P.chain_S1 rt hrt) 0

/-- Depth 1: a cell decomposed. -/
theorem I_S1c (g : ℕ → ℝ) (i : ℕ) : P.I g (P.S1c i) = P.J g (P.S1c i) - P.I g (P.S2 i) :=
  buchstab_fam g P.N₁ P.N₂ (P.S1c i) fun rt hrt => last_le_of_chain (P.chain_S1c i rt hrt)

/-- **Depth 2**, for a grid with `GridOK` and `P.Good`: the cells of `p₂`. -/
theorem I_S2 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) (i : ℕ) :
    P.I g (P.S2 i) = ∑ j ∈ range SieveCert.n, P.I g (P.S2c i j) :=
  famI_cells g P.N₁ P.N₂ G.hx (P.S2 i) 1 fun rt hrt => range_of_chain G (P.chain_S2 i rt hrt) 1

/-- Depth 2: a cell split at `p₁p₂ = X'`. -/
theorem I_S2c (g : ℕ → ℝ) (i j : ℕ) : P.I g (P.S2c i j) = P.I g (P.S2le i j) + P.I g (P.S2gt i j) :=
  famI_split g P.N₁ P.N₂ (P.S2c i j) _ _ fun rt => by simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 2: the part `p₁p₂ ≤ X'` decomposed. -/
theorem I_S2le (g : ℕ → ℝ) (i j : ℕ) : P.I g (P.S2le i j) = P.J g (P.S2le i j) - P.I g (P.S3 i j) :=
  buchstab_fam g P.N₁ P.N₂ (P.S2le i j) fun rt hrt => last_le_of_chain (P.chain_S2le i j rt hrt)

/-- **Depth 3**, for a grid with `GridOK` and `P.Good`: the cells of `p₃`. -/
theorem I_S3 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) (i j : ℕ) :
    P.I g (P.S3 i j) = ∑ k ∈ range SieveCert.n, P.I g (P.S3c i j k) :=
  famI_cells g P.N₁ P.N₂ G.hx (P.S3 i j) 2 fun rt hrt => range_of_chain G (P.chain_S3 i j rt hrt) 2

/-- Depth 3: a cell split at `p₁p₂p₃ = X'`. -/
theorem I_S3c (g : ℕ → ℝ) (i j k : ℕ) :
    P.I g (P.S3c i j k) = P.I g (P.S3le i j k) + P.I g (P.S3gt i j k) :=
  famI_split g P.N₁ P.N₂ (P.S3c i j k) _ _ fun rt => by simp only [Atom.sem_prodLe, Atom.sem_prodGt, not_le]

/-- Depth 3: the part `p₁p₂p₃ ≤ X'` decomposed. -/
theorem I_S3le (g : ℕ → ℝ) (i j k : ℕ) :
    P.I g (P.S3le i j k) = P.J g (P.S3le i j k) - P.I g (P.S4 i j k) :=
  buchstab_fam g P.N₁ P.N₂ (P.S3le i j k) fun rt hrt => last_le_of_chain (P.chain_S3le i j k rt hrt)

/-- **Depth 4**, for a grid with `GridOK` and `P.Good`: the cells of `p₄`. -/
theorem I_S4 [SieveCert.GridOK] (G : P.Good) (g : ℕ → ℝ) (i j k : ℕ) :
    P.I g (P.S4 i j k) = ∑ l ∈ range SieveCert.n, P.I g (P.S4c i j k l) :=
  famI_cells g P.N₁ P.N₂ G.hx (P.S4 i j k) 3 fun rt hrt => range_of_chain G (P.chain_S4 i j k rt hrt) 3

/-! ### What the families say of their primes -/

theorem facts_S2c {Y : ℕ} {i j : ℕ} {rt : Fin 2 → ℕ} (hrt : rt ∈ famSet 2 Y (P.S2c i j)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) := by
  have h1 : Fin.init rt ∈ famSet 1 Y (P.S1c i) := init_mem hrt fun A hA => List.mem_append_left _ hA
  exact ⟨P.chain_S2c i j rt hrt, inC_of_mem h1 (t := 0) fun A hA => List.mem_append_right _ hA,
    inC_of_mem hrt (t := 1) fun A hA => List.mem_append_right _ hA⟩

theorem facts_S2le {Y : ℕ} {i j : ℕ} {rt : Fin 2 → ℕ} (hrt : rt ∈ famSet 2 Y (P.S2le i j)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ (rt 0 : ℝ) * rt 1 ≤ P.Xp := by
  obtain ⟨h1, h2, h3⟩ := facts_S2c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h4 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xp :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ P.Xp) (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_two] at h4
  exact ⟨h1, h2, h3, h4⟩

theorem facts_S3c {Y : ℕ} {i j k : ℕ} {rt : Fin 3 → ℕ} (hrt : rt ∈ famSet 3 Y (P.S3c i j k)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧
      (rt 0 : ℝ) * rt 1 ≤ P.Xp := by
  have h2 : Fin.init rt ∈ famSet 2 Y (P.S2le i j) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, h3, h4, h5⟩ := facts_S2le h2
  exact ⟨P.chain_S3c i j k rt hrt, h3, h4, inC_of_mem hrt (t := 2) fun A hA => List.mem_append_right _ hA, h5⟩

theorem facts_S3le {Y : ℕ} {i j k : ℕ} {rt : Fin 3 → ℕ} (hrt : rt ∈ famSet 3 Y (P.S3le i j k)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧
      (rt 0 : ℝ) * rt 1 ≤ P.Xp ∧ (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xp := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := facts_S3c (famSet_mono (fun A hA => List.mem_append_left _ hA) hrt)
  have h6 : ∏ t ∈ Finset.univ, (rt t : ℝ) ≤ P.Xp :=
    sem_of_mem hrt (A := Atom.prodLe Finset.univ P.Xp) (List.mem_append_right _ (List.mem_singleton_self _))
  rw [Fin.prod_univ_three] at h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem facts_S4c {Y : ℕ} {i j k l : ℕ} {rt : Fin 4 → ℕ} (hrt : rt ∈ famSet 4 Y (P.S4c i j k l)) :
    Chain P.z₀ P.ztop rt ∧ InC P.x i (rt 0) ∧ InC P.x j (rt 1) ∧ InC P.x k (rt 2) ∧ InC P.x l (rt 3) ∧
      (rt 0 : ℝ) * rt 1 ≤ P.Xp ∧ (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xp := by
  have h3 : Fin.init rt ∈ famSet 3 Y (P.S3le i j k) := init_mem hrt fun A hA => List.mem_append_left _ hA
  obtain ⟨-, h4, h5, h6, h7, h8⟩ := facts_S3le h3
  exact ⟨P.chain_S4c i j k l rt hrt, h4, h5, h6, inC_of_mem hrt (t := 3) fun A hA => List.mem_append_right _ hA,
    h7, h8⟩

/-! ### Cells that contribute nothing -/

omit [SieveCert.Grid] in
theorem rpow_div_add {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    x ^ (a / DEN) * x ^ (b / DEN) = x ^ ((a + b) / DEN) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

omit [SieveCert.Grid] in
/-- For `x > 0`, four reals at least `x^{a/DEN}`, …, `x^{d/DEN}` have product at least `x^{(a + b + c + d)/DEN}`. -/
theorem prod4_ge {x : ℝ} (hx : 0 < x) {a b c d : ℝ} {p₁ p₂ p₃ p₄ : ℝ} (h1 : x ^ (a / DEN) ≤ p₁)
    (h2 : x ^ (b / DEN) ≤ p₂) (h3 : x ^ (c / DEN) ≤ p₃) (h4 : x ^ (d / DEN) ≤ p₄) :
    x ^ ((a + b + c + d) / DEN) ≤ p₁ * p₂ * p₃ * p₄ := by
  rw [← rpow_div_add hx, ← rpow_div_add hx, ← rpow_div_add hx]
  have h0 : ∀ y : ℝ, 0 ≤ x ^ y := fun y => Real.rpow_nonneg hx.le y
  have hp1 : 0 ≤ p₁ := (h0 _).trans h1
  have hp2 : 0 ≤ p₂ := (h0 _).trans h2
  have hp3 : 0 ≤ p₃ := (h0 _).trans h3
  exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (h0 _) hp1) h3 (h0 _) (mul_nonneg hp1 hp2)) h4 (h0 _)
    (mul_nonneg (mul_nonneg hp1 hp2) hp3)

omit [SieveCert.Grid] in
/-- For `x ≥ 1` and `s > DEN`, `x^{(DEN + 1)/DEN} ≤ x^{s/DEN}`. -/
theorem rpow_region {x : ℝ} (hx : 1 ≤ x) {s : ℕ} (hs : DEN < s) :
    x ^ (((DEN : ℝ) + 1) / DEN) ≤ x ^ ((s : ℝ) / DEN) := by
  have hD := SieveCert.DEN_pos'
  refine Real.rpow_le_rpow_of_exponent_le hx (div_le_div_of_nonneg_right ?_ hD.le)
  have : DEN + 1 ≤ s := hs
  exact_mod_cast this

/-- For `x ≥ 1` and `e_j + H ≤ e_k`, `x^{(e_j + H)/DEN} ≤ x^{e_k/DEN}`. -/
theorem rpow_cell_le {x : ℝ} (hx : 1 ≤ x) {j k : ℕ} (h : SieveCert.e j + H ≤ SieveCert.e k) :
    x ^ (((SieveCert.e j : ℝ) + H) / DEN) ≤ x ^ ((SieveCert.e k : ℝ) / DEN) := by
  have hD := SieveCert.DEN_pos'
  refine Real.rpow_le_rpow_of_exponent_le hx (div_le_div_of_nonneg_right ?_ hD.le)
  exact_mod_cast h

theorem e_add_H_le_of_lt {k l : ℕ} (h : k < l) : SieveCert.e k + H ≤ SieveCert.e l := by
  unfold SieveCert.e
  have : H * k + H ≤ H * l := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left H h
  omega

omit [SieveCert.Grid] in
/-- The smallest prime of three below `√X'` when the two largest have product at most `X'`. -/
theorem third_lt_sqrt {p₁ p₂ p₃ : ℕ} {X : ℝ} (h21 : p₂ < p₁) (h32 : p₃ < p₂) (h : (p₁ : ℝ) * p₂ ≤ X) :
    (p₃ : ℝ) < Real.sqrt X := by
  rw [Real.lt_sqrt (by positivity)]
  have : p₃ * p₃ < p₁ * p₂ := Nat.mul_lt_mul'' (by omega) h32
  have : (p₃ : ℝ) * p₃ < p₁ * p₂ := by exact_mod_cast this
  nlinarith

/-- **Depth 3, outside `inKK`**, for `P.Good`: either `p₃` would exceed `p₂`, or `p₁p₂p₃² > N₂` while `p₁p₂p₃ ≤ N₁`. -/
theorem I_S3c_vanish (G : P.Good) (g : ℕ → ℝ) {i j k : ℕ} (h : inKK i j k = false) : P.I g (P.S3c i j k) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  simp only [inKK, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, not_le] at h
  rcases h with h | h
  · refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
    obtain ⟨hc, -, hj, hk, -⟩ := P.facts_S3c hrt
    have h21 : rt 2 < rt 1 := hc.1 (show (1 : Fin 3) < 2 by decide)
    have : (rt 1 : ℝ) < rt 2 := lt_of_lt_of_le hj.2 ((rpow_cell_le hx1 h).trans hk.1)
    exact absurd h21 (not_lt.2 (by exact_mod_cast this.le))
  · refine famI_vanish g _ _ _ fun rt hrt => ?_
    obtain ⟨hc, hi, hj, hk, hX⟩ := P.facts_S3c hrt
    have h10 : rt 1 < rt 0 := hc.1 (show (0 : Fin 3) < 1 by decide)
    have h21 : rt 2 < rt 1 := hc.1 (show (1 : Fin 3) < 2 by decide)
    have hs := third_lt_sqrt h10 h21 hX
    rw [Fin.prod_univ_three]
    have hX0 : (0 : ℝ) ≤ P.Xp := le_trans (by positivity) hX
    constructor
    · have : ((rt 0 * rt 1 * rt 2 : ℕ) : ℝ) ≤ P.N₁ := by
        push_cast
        calc (rt 0 : ℝ) * rt 1 * rt 2 ≤ P.Xp * Real.sqrt P.Xp := by
              apply mul_le_mul hX hs.le (by positivity) hX0
          _ ≤ P.N₁ := G.hXN
      exact_mod_cast this
    · have hp := prod4_ge hx0 hi.1 hj.1 hk.1 hk.1
      have hreg := rpow_region hx1 (s := SieveCert.e i + SieveCert.e j + 2 * SieveCert.e k) (by omega)
      have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt (Fin.last 2) : ℕ) : ℝ) := by
        push_cast
        refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
        congr 1
        push_cast
        ring
      exact_mod_cast this

/-- **Depth 4, `l > k`**, for `P.Good`: `p₄` would exceed `p₃`. -/
theorem I_S4c_vanish_lt (G : P.Good) (g : ℕ → ℝ) {i j k l : ℕ} (h : k < l) : P.I g (P.S4c i j k l) = 0 := by
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_eq_zero g _ _ _ fun rt hrt => False.elim ?_
  obtain ⟨hc, -, -, hk, hl, -⟩ := P.facts_S4c hrt
  have h32 : rt 3 < rt 2 := hc.1 (show (2 : Fin 4) < 3 by decide)
  have : (rt 2 : ℝ) < rt 3 := lt_of_lt_of_le hk.2 ((rpow_cell_le hx1 (e_add_H_le_of_lt h)).trans hl.1)
  exact absurd h32 (not_lt.2 (by exact_mod_cast this.le))

/-- **Depth 4, outside the region**, for `P.Good`: `p₁p₂p₃p₄² > N₂` while `p₁p₂p₃p₄ ≤ N₁`. -/
theorem I_S4c_vanish_reg (G : P.Good) (g : ℕ → ℝ) {i j k l : ℕ}
    (h : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + 2 * SieveCert.e l) :
    P.I g (P.S4c i j k l) = 0 := by
  have hx0 : 0 < P.x := by linarith [G.hx]
  have hx1 : 1 ≤ P.x := G.hx.le
  refine famI_vanish g _ _ _ fun rt hrt => ?_
  obtain ⟨hc, hi, hj, hk, hl, hX2, hX3⟩ := P.facts_S4c hrt
  have h10 : rt 1 < rt 0 := hc.1 (show (0 : Fin 4) < 1 by decide)
  have h21 : rt 2 < rt 1 := hc.1 (show (1 : Fin 4) < 2 by decide)
  have h32 : rt 3 < rt 2 := hc.1 (show (2 : Fin 4) < 3 by decide)
  have hs := third_lt_sqrt h10 h21 hX2
  have h3s : (rt 3 : ℝ) < Real.sqrt P.Xp := lt_trans (by exact_mod_cast h32) hs
  rw [Fin.prod_univ_four]
  have hX0 : (0 : ℝ) ≤ P.Xp := le_trans (by positivity) hX3
  constructor
  · have : ((rt 0 * rt 1 * rt 2 * rt 3 : ℕ) : ℝ) ≤ P.N₁ := by
      push_cast
      calc (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 ≤ P.Xp * Real.sqrt P.Xp := by
            apply mul_le_mul hX3 h3s.le (by positivity) hX0
        _ ≤ P.N₁ := G.hXN
    exact_mod_cast this
  · have hp4 := prod4_ge hx0 hi.1 hj.1 hk.1 hl.1
    have hp : P.x ^ ((((SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + SieveCert.e l) + SieveCert.e l) / DEN) ≤
        (rt 0 : ℝ) * rt 1 * rt 2 * rt 3 * rt 3 := by
      rw [← rpow_div_add hx0]
      exact mul_le_mul hp4 hl.1 (by positivity) (by positivity)
    have hreg := rpow_region hx1 (s := SieveCert.e i + SieveCert.e j + SieveCert.e k + 2 * SieveCert.e l) h
    have : (P.N₂ : ℝ) < ((rt 0 * rt 1 * rt 2 * rt 3 * rt (Fin.last 3) : ℕ) : ℝ) := by
      push_cast
      refine lt_of_lt_of_le G.hN₂ (hreg.trans (le_of_eq_of_le ?_ hp))
      congr 1
      push_cast
      ring
    exact_mod_cast this

/-! ### The inequality, level by level -/

/-- The cell `i` of `p₁` lies inside the window: its terms are evaluated at depth 1. -/
def inW (i : ℕ) : Prop := U1 < SieveCert.e i ∧ SieveCert.e i + H < U2

/-- The box `(i, j)` is surely evaluable. -/
def sE2 (i j : ℕ) : Bool := surelyEval [cell i, cell j]

/-- The box `(i, j, k, l)` is surely evaluable. -/
def sE4 (i j k l : ℕ) : Bool := surelyEval [cell i, cell j, cell k, cell l]

variable (P)

/-- The dropped terms of depth 4 below `(i, j, k)`: the counted cells. -/
noncomputable def D4 (g : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  ∑ l ∈ range (k + 1), if counted4 i j k l = true then P.I g (P.S4c i j k l) else 0

/-- The dropped terms below the cell `(i, j)`. -/
noncomputable def D3 (g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ range SieveCert.n, if inKK i j k = true ∧ ne3 i j k = true then P.D4 g i j k else 0

/-- The dropped terms below the cell `i`: the cells `(i, j)` dropped (candidates not decomposed, and the corner),
and those below the decomposed cells. -/
noncomputable def D2 (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range SieveCert.n,
    ((if (cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false) then P.I g (P.S2c i j) else 0) +
      (if cand i j = true ∧ dec i j = true then P.D3 g i j else 0))

/-- All the dropped terms. -/
noncomputable def D1 (g : ℕ → ℝ) : ℝ := ∑ i ∈ range SieveCert.n, if inW i then 0 else P.D2 g i

/-- The leaves' estimates: each evaluated family and each family of Proposition 6 has its `A`- and `B`-sums within
`Err`. -/
structure Leaves (gA gB : ℕ → ℝ) (Err : ℝ) : Prop where
  j0 : |P.J0 gA - P.J0 gB| ≤ Err
  e1 : ∀ i < SieveCert.n, inW i → |P.I gA (P.S1c i) - P.I gB (P.S1c i)| ≤ Err
  p1 : ∀ i < SieveCert.n, ¬ inW i → |P.J gA (P.S1c i) - P.J gB (P.S1c i)| ≤ Err
  e2 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → dec i j = true →
    |P.I gA (P.S2gt i j) - P.I gB (P.S2gt i j)| ≤ Err
  p2 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → dec i j = true →
    |P.J gA (P.S2le i j) - P.J gB (P.S2le i j)| ≤ Err
  e2' : ∀ i < SieveCert.n, ¬ inW i → ∀ j < SieveCert.n, cand i j = false → sE2 i j = true →
    |P.I gA (P.S2c i j) - P.I gB (P.S2c i j)| ≤ Err
  e3 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → dec i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → |P.I gA (P.S3gt i j k) - P.I gB (P.S3gt i j k)| ≤ Err
  p3 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → dec i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → |P.J gA (P.S3le i j k) - P.J gB (P.S3le i j k)| ≤ Err
  e3' : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → dec i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = false → |P.I gA (P.S3c i j k) - P.I gB (P.S3c i j k)| ≤ Err
  e4 : ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → dec i j = true → ∀ k < SieveCert.n,
    inKK i j k = true → ne3 i j k = true → ∀ l < k + 1, counted4 i j k l = false → sE4 i j k l = true →
      |P.I gA (P.S4c i j k l) - P.I gB (P.S4c i j k l)| ≤ Err

variable {P}

/-- **Level 4** (terms with sign `+`), for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, `k < n`, and the
row's surely evaluable cells of depth 4 that are not counted within `Err ≥ 0`: `A ≥ B − (dropped) − (k + 1)Err`. -/
theorem lvl4 [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    {i j k : ℕ} (hE : ∀ l < k + 1, counted4 i j k l = false → sE4 i j k l = true →
      |P.I gA (P.S4c i j k l) - P.I gB (P.S4c i j k l)| ≤ Err) (hk : k < SieveCert.n) :
    P.I gB (P.S4 i j k) - P.D4 gB i j k - (k + 1) * Err ≤ P.I gA (P.S4 i j k) := by
  have hsub : ∀ g, ∑ l ∈ range SieveCert.n, P.I g (P.S4c i j k l) = ∑ l ∈ range (k + 1), P.I g (P.S4c i j k l) := by
    intro g
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l hl hl' => ?_
    rw [Finset.mem_range] at hl hl'
    exact P.I_S4c_vanish_lt G g (by omega)
  rw [P.I_S4 G gA, P.I_S4 G gB, hsub gA, hsub gB]
  unfold D4
  have hErrs : ((k : ℝ) + 1) * Err = ∑ _l ∈ range (k + 1), Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l hl => ?_
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 4 P.N₂ (P.S4c i j k l))
  by_cases hc4 : counted4 i j k l = true
  · rw [ite_eq_left hc4]
    unfold I
    linarith
  · rw [ite_eq_right hc4]
    by_cases hs : sE4 i j k l = true
    · have := abs_le.1 (hE l (Finset.mem_range.1 hl) (by simpa using hc4) hs)
      linarith [this.1]
    · -- outside the region: both sums vanish
      have hreg : DEN < SieveCert.e i + SieveCert.e j + SieveCert.e k + 2 * SieveCert.e l := by
        simp only [sE4, Bool.not_eq_true] at hs
        simp only [counted4, hs, Bool.not_false, Bool.and_true, decide_eq_true_eq, not_le] at hc4
        exact hc4
      rw [P.I_S4c_vanish_reg G gA hreg, P.I_S4c_vanish_reg G gB hreg]
      linarith

/-- **Level 3** (terms with sign `−`), for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, leaves within
`Err ≥ 0`, and a candidate cell `(i, j)` that is decomposed: `A ≤ B + (dropped below) + n(n + 2)Err`. -/
theorem lvl3 [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    (Lv : P.Leaves gA gB Err) {i j : ℕ} (hi : i < SieveCert.n) (hj : j < SieveCert.n)
    (hcd : cand i j = true ∧ dec i j = true) :
    P.I gA (P.S3 i j) ≤ P.I gB (P.S3 i j) + P.D3 gB i j + SieveCert.n * (SieveCert.n + 2) * Err := by
  rw [P.I_S3 G gA, P.I_S3 G gB]
  unfold D3
  have hErrs : (SieveCert.n : ℝ) * (SieveCert.n + 2) * Err =
      ∑ _k ∈ range SieveCert.n, ((SieveCert.n : ℝ) + 2) * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hkn : ((k : ℝ) + 1) * Err ≤ SieveCert.n * Err :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hErr
  by_cases hkk : inKK i j k = true
  · by_cases hn3 : ne3 i j k = true
    · rw [ite_eq_left ⟨hkk, hn3⟩, P.I_S3c gA, P.I_S3c gB, P.I_S3le gA, P.I_S3le gB]
      have h4 := lvl4 G hgA hErr (Lv.e4 i hi j hj hcd.1 hcd.2 k hk' hkk hn3) hk'
      have hJ := abs_le.1 (Lv.p3 i hi j hj hcd.1 hcd.2 k hk' hkk hn3)
      have hE := abs_le.1 (Lv.e3 i hi j hj hcd.1 hcd.2 k hk' hkk hn3)
      have : ((SieveCert.n : ℝ) + 2) * Err = SieveCert.n * Err + 2 * Err := by ring
      linarith [hJ.2, hE.2]
    · have hn3' : ne3 i j k = false := by simpa using hn3
      rw [ite_eq_right (show ¬(inKK i j k = true ∧ ne3 i j k = true) from fun h => hn3 h.2)]
      have hE := abs_le.1 (Lv.e3' i hi j hj hcd.1 hcd.2 k hk' hkk hn3')
      have : Err ≤ ((SieveCert.n : ℝ) + 2) * Err :=
        le_mul_of_one_le_left hErr (by have : (0 : ℝ) ≤ SieveCert.n := Nat.cast_nonneg _; linarith)
      linarith [hE.2]
  · have hkk' : inKK i j k = false := by simpa using hkk
    rw [ite_eq_right (show ¬(inKK i j k = true ∧ ne3 i j k = true) from fun h => hkk h.1),
      P.I_S3c_vanish G gA hkk', P.I_S3c_vanish G gB hkk']
    have : 0 ≤ ((SieveCert.n : ℝ) + 2) * Err := by positivity
    linarith

/-- **Level 2** (terms with sign `+`), for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, leaves within
`Err ≥ 0`, and a cell `i < n` of `p₁` not inside the window: `A ≥ B − (dropped) − n(n(n + 2) + 2)Err`. -/
theorem lvl2 [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    (Lv : P.Leaves gA gB Err) {i : ℕ} (hi : i < SieveCert.n) (hW : ¬ inW i) :
    P.I gB (P.S2 i) - P.D2 gB i - SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2) * Err ≤
      P.I gA (P.S2 i) := by
  rw [P.I_S2 G gA, P.I_S2 G gB]
  unfold D2
  set c3 : ℝ := SieveCert.n * (SieveCert.n + 2) with hc3
  have hc30 : 0 ≤ c3 := by positivity
  have hErrs : (SieveCert.n : ℝ) * (c3 + 2) * Err = ∑ _j ∈ range SieveCert.n, (c3 + 2) * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 2 P.N₂ (P.S2c i j))
  have hE0 : 0 ≤ (c3 + 2) * Err := by positivity
  by_cases hc : cand i j = true
  · by_cases hd : dec i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false)) by
          simp [hc, hd]),
        ite_eq_left (show cand i j = true ∧ dec i j = true from ⟨hc, hd⟩), P.I_S2c gA, P.I_S2c gB, P.I_S2le gA,
        P.I_S2le gB]
      have h3 := lvl3 G hgA hErr Lv hi hj' ⟨hc, hd⟩
      have hJ := abs_le.1 (Lv.p2 i hi j hj' hc hd)
      have hE := abs_le.1 (Lv.e2 i hi j hj' hc hd)
      rw [← hc3] at h3
      have : (c3 + 2) * Err = c3 * Err + 2 * Err := by ring
      linarith [hJ.1, hE.1]
    · rw [ite_eq_left (show (cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inl ⟨hc, by simpa using hd⟩),
        ite_eq_right (show ¬(cand i j = true ∧ dec i j = true) from fun h => hd h.2)]
      unfold I at hA0 ⊢
      linarith
  · rw [ite_eq_right (show ¬(cand i j = true ∧ dec i j = true) from fun h => hc h.1)]
    by_cases hs : sE2 i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false)) by
          simp [hc, hs])]
      have hE := abs_le.1 (Lv.e2' i hi hW j hj' (by simpa using hc) hs)
      have : Err ≤ (c3 + 2) * Err := le_mul_of_one_le_left hErr (by linarith)
      linarith [hE.1]
    · rw [ite_eq_left (show (cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inr ⟨by simpa using hc, by simpa using hs⟩)]
      unfold I at hA0 ⊢
      linarith

/-- **Level 1** (terms with sign `−`), for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, and leaves
within `Err ≥ 0`: `A ≤ B + (dropped) + n(1 + n(n(n + 2) + 2))Err`. -/
theorem lvl1 [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    (Lv : P.Leaves gA gB Err) :
    P.I gA P.S1 ≤ P.I gB P.S1 + P.D1 gB +
      SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2)) * Err := by
  rw [P.I_S1 G gA, P.I_S1 G gB]
  unfold D1
  set c2 : ℝ := SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2) with hc2
  have hc20 : 0 ≤ c2 := by positivity
  have hErrs : (SieveCert.n : ℝ) * (1 + c2) * Err = ∑ _i ∈ range SieveCert.n, (1 + c2) * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  by_cases hW : inW i
  · rw [ite_eq_left hW]
    have hE := abs_le.1 (Lv.e1 i hi' hW)
    have : Err ≤ (1 + c2) * Err := le_mul_of_one_le_left hErr (by linarith)
    linarith [hE.2]
  · rw [ite_eq_right hW, P.I_S1c gA, P.I_S1c gB]
    have h2 := lvl2 G hgA hErr Lv hi' hW
    have hJ := abs_le.1 (Lv.p1 i hi' hW)
    rw [← hc2] at h2
    have : (1 + c2) * Err = Err + c2 * Err := by ring
    linarith [hJ.2]

/-- **The decomposition's inequality.** For a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, and leaves
within `Err ≥ 0`: `S(A, z_top) ≥ S(B, z_top) − (the dropped B-terms) − C·Err`, `C = 1 + n(1 + n(n(n + 2) + 2))`. -/
theorem decomp [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    (Lv : P.Leaves gA gB Err) :
    P.T gB - P.D1 gB - (1 + SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2))) * Err ≤
      P.T gA := by
  rw [P.T_eq G gA, P.T_eq G gB]
  have h1 := lvl1 G hgA hErr Lv
  have hJ := abs_le.1 Lv.j0
  set c1 : ℝ := SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2)) with hc1
  have : (1 + c1) * Err = Err + c1 * Err := by ring
  linarith [hJ.1]

end Par

end SieveBuch
