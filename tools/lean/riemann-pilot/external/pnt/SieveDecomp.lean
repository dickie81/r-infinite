/-
# Round 604: families of prime tuples, and Buchstab's identity on them (milestone M8)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. An `Atom k` is one condition on a `k`-tuple `x` of primes: `b ≤ x_t`, `x_t < b`, `x_t < x_s`,
`∏_{i∈T} x_i ≤ b` or `b < ∏_{i∈T} x_i` (`Atom.sem`). The family `famSet k Y spec` is the set of `k`-tuples of primes
up to `Y` that satisfy every atom of `spec`. For weights `g` on `(N₁, N₂]`, `famI` sums the terms
`S_g(∏rt, rt_last) = Σ_n g(n)[∏rt ∣ n, no prime factor of n below rt_last]` over a family, and `famJ` the terms
`S_g(∏rt, z)`.

* `RTg_eq`: with positive thresholds, a family is `SieveChain.RTg` of its atoms' comparisons (`Atom.toG`).
* `buchstab_pt`, `buchstab_fam`: Buchstab's identity. For a family whose tuples have their last prime least and at
  least `z`, `famI = famJ(z) − famI` of the extended family (`extS`: one more prime `p ∈ [z, rt_last)`).
* `famI_cells`: if every tuple has its prime `t` in `[x^{V/DEN}, x^{(V + nH)/DEN})`, `x > 1`, the family is the sum over
  the cells `c < n` of a grid with `GridOK` (`SieveCert.Grid`) of its subfamilies with
  `x^{e_c/DEN} ≤ rt_t < x^{(e_c + H)/DEN}` (`cellA`).
* `famI_split`: a family is the sum of its subfamilies under an atom and under its complement.
* `famI_eq_zero`, `famI_vanish`: a family contributes `0` when no `n ∈ (N₁, N₂]` is counted, in particular when every
  `∏rt ≤ N₁` while `∏rt·rt_last > N₂`.

These are the operations of the decomposition of `frontier/linnik/SIEVE-ROUTE.md` §6 (§13's M8), on families
described by finitely many atoms: extension by one prime (Buchstab), the cells of the newest prime, splits by a
product against a threshold, and families that vanish.

Round 607 made the certificate's grid a parameter (`SieveCert.Grid`, with `GridOK` where the Lean takes it); the
statements of earlier rounds are the case `SieveCert.grid2333`.


The file imports `SieveChain.lean`.
-/
import SieveChain

open Real Finset SieveFamily SieveChain

namespace SieveDecomp

open Classical

/-! ### Atoms of a family's region -/

/-- An atom of a family's region: a threshold for one prime, two primes compared, or a product of primes against a
threshold. -/
inductive Atom (k : ℕ) where
  | ge (t : Fin k) (b : ℝ)
  | lt (t : Fin k) (b : ℝ)
  | ltVar (s t : Fin k)
  | prodLe (T : Finset (Fin k)) (b : ℝ)
  | prodGt (T : Finset (Fin k)) (b : ℝ)

namespace Atom

variable {k : ℕ}

/-- What an atom says of a tuple: `b ≤ x_t`, `x_t < b`, `x_t < x_s`, `∏_T x ≤ b`, `b < ∏_T x`. -/
def sem : Atom k → (Fin k → ℕ) → Prop
  | ge t b, x => b ≤ x t
  | lt t b, x => (x t : ℝ) < b
  | ltVar s t, x => x t < x s
  | prodLe T b, x => ∏ i ∈ T, (x i : ℝ) ≤ b
  | prodGt T b, x => b < ∏ i ∈ T, (x i : ℝ)

@[simp] theorem sem_ge (t : Fin k) (b : ℝ) (x : Fin k → ℕ) : (ge t b).sem x ↔ b ≤ x t := Iff.rfl
@[simp] theorem sem_lt (t : Fin k) (b : ℝ) (x : Fin k → ℕ) : (lt t b).sem x ↔ (x t : ℝ) < b := Iff.rfl
@[simp] theorem sem_ltVar (s t : Fin k) (x : Fin k → ℕ) : (ltVar s t).sem x ↔ x t < x s := Iff.rfl
@[simp] theorem sem_prodLe (T : Finset (Fin k)) (b : ℝ) (x : Fin k → ℕ) :
    (prodLe T b).sem x ↔ ∏ i ∈ T, (x i : ℝ) ≤ b := Iff.rfl
@[simp] theorem sem_prodGt (T : Finset (Fin k)) (b : ℝ) (x : Fin k → ℕ) :
    (prodGt T b).sem x ↔ b < ∏ i ∈ T, (x i : ℝ) := Iff.rfl

/-- The atom's threshold (`1` for two primes compared). -/
noncomputable def thr : Atom k → ℝ
  | ge _ b => b
  | lt _ b => b
  | ltVar _ _ => 1
  | prodLe _ b => b
  | prodGt _ b => b

/-- The atom as a comparison. -/
noncomputable def toG : Atom k → GCmp k
  | ge t b => ⟨fun _ => -Real.log b, fun i => if i = t then 1 else 0, false, fun i => by split_ifs <;> simp⟩
  | lt t b => ⟨fun _ => Real.log b, fun i => -(if i = t then 1 else 0), true, fun i => by split_ifs <;> simp⟩
  | ltVar s t => ⟨fun _ => 0, fun i => (if i = s then 1 else 0) - (if i = t then 1 else 0), true,
      fun i => by split_ifs <;> simp⟩
  | prodLe T b => ⟨fun _ => Real.log b, fun i => -(if i ∈ T then 1 else 0), false,
      fun i => by split_ifs <;> simp⟩
  | prodGt T b => ⟨fun _ => -Real.log b, fun i => if i ∈ T then 1 else 0, true, fun i => by split_ifs <;> simp⟩

/-- With a positive threshold, on entries at least `1`, the comparison holds exactly when the atom does. -/
theorem toG_holds (A : Atom k) (hA : 0 < A.thr) (m : ℕ) {x : Fin k → ℕ} (hx : ∀ i, 1 ≤ x i) :
    A.toG.holds m x ↔ A.sem x := by
  have hpos : ∀ i, (0 : ℝ) < x i := fun i => by exact_mod_cast hx i
  have hprod : ∀ T : Finset (Fin k), (0 : ℝ) < ∏ i ∈ T, (x i : ℝ) := fun T => Finset.prod_pos fun i _ => hpos i
  cases A with
  | ge t b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, Bool.false_eq_true, ite_false, SieveCmp.sum_single,
      neg_add_eq_sub, sub_nonneg]
    exact Real.log_le_log_iff hA (hpos t)
  | lt t b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, ite_true, neg_mul, Finset.sum_neg_distrib, SieveCmp.sum_single,
      ← sub_eq_add_neg, sub_pos]
    exact Real.log_lt_log_iff (hpos t) hA
  | ltVar s t =>
    simp only [toG, GCmp.holds, GCmp.form, sem, ite_true, zero_add, sub_mul, Finset.sum_sub_distrib,
      SieveCmp.sum_single, sub_pos]
    rw [Real.log_lt_log_iff (hpos t) (hpos s), Nat.cast_lt]
  | prodLe T b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, Bool.false_eq_true, ite_false, neg_mul, Finset.sum_neg_distrib,
      SieveCmp.sum_set T x hx, ← sub_eq_add_neg, sub_nonneg]
    exact Real.log_le_log_iff (hprod T) hA
  | prodGt T b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, ite_true, SieveCmp.sum_set T x hx, neg_add_eq_sub, sub_pos]
    exact Real.log_lt_log_iff hA (hprod T)

/-- The comparison's part at `m = 0` is at most `|log thr|`. -/
theorem toG_c_le (A : Atom k) : A.toG.c 0 ≤ |Real.log A.thr| := by
  cases A <;> simp only [toG, thr, Real.log_one, abs_zero, le_refl] <;>
    first | exact neg_le_abs _ | exact le_abs_self _

/-- The atom on the first `k` primes of a `(k + 1)`-tuple. -/
def lift : Atom k → Atom (k + 1)
  | ge t b => ge t.castSucc b
  | lt t b => lt t.castSucc b
  | ltVar s t => ltVar s.castSucc t.castSucc
  | prodLe T b => prodLe (T.map Fin.castSuccEmb) b
  | prodGt T b => prodGt (T.map Fin.castSuccEmb) b

theorem lift_sem (A : Atom k) (x : Fin (k + 1) → ℕ) : A.lift.sem x ↔ A.sem (Fin.init x) := by
  cases A <;> simp [lift, sem, Fin.init, Finset.prod_map]

theorem lift_thr (A : Atom k) : A.lift.thr = A.thr := by
  cases A <;> rfl

end Atom

/-! ### Families -/

/-- The family of a list of atoms: the `k`-tuples of primes up to `Y` that satisfy them. -/
noncomputable def famSet (k Y : ℕ) (spec : List (Atom k)) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => SieveTypeIIU.primesLe Y).filter fun x => ∀ A ∈ spec, A.sem x

theorem mem_famSet {k Y : ℕ} {spec : List (Atom k)} {x : Fin k → ℕ} :
    x ∈ famSet k Y spec ↔ (∀ i, x i ≤ Y ∧ (x i).Prime) ∧ ∀ A ∈ spec, A.sem x := by
  rw [famSet, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [SieveTypeIIU.mem_primesLe]

/-- With positive thresholds, the family is `RTg` of the atoms' comparisons. -/
theorem RTg_eq (k Y : ℕ) (spec : List (Atom k)) (hpos : ∀ A ∈ spec, 0 < A.thr) :
    RTg k Y (spec.map Atom.toG) = famSet k Y spec := by
  unfold RTg famSet
  refine Finset.filter_congr fun x hx => ?_
  rw [Fintype.mem_piFinset] at hx
  have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hx i)).2.one_lt.le
  simp only [List.forall_mem_map]
  exact forall₂_congr fun A hA => A.toG_holds (hpos A hA) 0 hx1

/-- The terms `S(A_{∏rt}, rt_last)` of a family, with weights `g`. -/
noncomputable def famI (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) : ℝ :=
  ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, g n *
    (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0)

/-- The terms `S(A_{∏rt}, z)` of a family, with weights `g`. -/
noncomputable def famJ (g : ℕ → ℝ) (N₁ N₂ z : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) : ℝ :=
  ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0)

theorem famI_nonneg {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) :
    0 ≤ famI g N₁ N₂ F :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun n _ => mul_nonneg (hg n) (by split_ifs <;> norm_num)

/-! ### Buchstab's identity on a family -/

/-- For a prime `p` and `n ≥ 2`, `p ∣ n` with `n` free of primes below `p` means `p = minFac n`. -/
theorem dvd_rough_iff {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    p ∣ n ∧ SieveTree.rough p n ↔ p = Nat.minFac n := by
  constructor
  · rintro ⟨hd, hr⟩
    have h1 := Nat.minFac_le_of_dvd hp.two_le hd
    have h2 := (SieveStops2.rough_iff_le_minFac hn).1 hr
    omega
  · rintro rfl
    exact ⟨Nat.minFac_dvd n, (SieveStops2.rough_iff_le_minFac hn).2 le_rfl⟩

/-- **Buchstab's identity at one `n`.** For `W` whose primes are at least `P ≥ z` and `n ≠ 0`:
`[W ∣ n, rough P n] = [W ∣ n, rough z n] − Σ_{z ≤ p < P} [Wp ∣ n, rough p n]`. -/
theorem buchstab_pt {W P z n : ℕ} (hn : n ≠ 0) (hzP : z ≤ P) (hW : ∀ p : ℕ, p.Prime → p ∣ W → P ≤ p) :
    (if W ∣ n ∧ SieveTree.rough P n then (1 : ℝ) else 0) =
      (if W ∣ n ∧ SieveTree.rough z n then 1 else 0) -
        ∑ p ∈ SieveTree.primesIco z P, (if W * p ∣ n ∧ SieveTree.rough p n then 1 else 0) := by
  by_cases hWn : W ∣ n
  · have hcop : ∀ p ∈ SieveTree.primesIco z P, (W * p ∣ n ↔ p ∣ n) := by
      intro p hp
      rw [SieveTree.mem_primesIco] at hp
      have hc : Nat.Coprime W p := by
        refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.2.2).2 fun h => ?_)
        have := hW p hp.2.2 h
        omega
      exact ⟨fun h => dvd_trans (Dvd.intro_left W rfl) h, fun h => hc.mul_dvd_of_dvd_of_dvd hWn h⟩
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · -- `n = 1`: every condition is on primes dividing `1`
      have hn1 : n = 1 := by omega
      subst hn1
      have hr : ∀ w, SieveTree.rough w 1 := fun w p _ hp hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)
      rw [Finset.sum_eq_zero]
      · simp [hWn, hr]
      intro p hp
      rw [ite_eq_right_iff]
      rintro ⟨hd, -⟩
      have := (SieveTree.mem_primesIco.1 hp).2.2
      exact (this.one_lt.ne' (Nat.dvd_one.1 (dvd_trans (Dvd.intro_left W rfl) hd))).elim
    · have hsum : ∑ p ∈ SieveTree.primesIco z P, (if W * p ∣ n ∧ SieveTree.rough p n then (1 : ℝ) else 0) =
          if z ≤ Nat.minFac n ∧ Nat.minFac n < P then 1 else 0 := by
        have hterm : ∀ p ∈ SieveTree.primesIco z P,
            (if W * p ∣ n ∧ SieveTree.rough p n then (1 : ℝ) else 0) = if p = Nat.minFac n then 1 else 0 := by
          intro p hp
          have hiff : (W * p ∣ n ∧ SieveTree.rough p n) ↔ p = Nat.minFac n := by
            rw [hcop p hp]; exact dvd_rough_iff (SieveTree.mem_primesIco.1 hp).2.2 h2
          simp only [hiff]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
        simp only [SieveTree.mem_primesIco, Nat.minFac_prime (by omega : n ≠ 1), and_true]
      rw [hsum]
      have e1 : SieveTree.rough P n ↔ P ≤ Nat.minFac n := SieveStops2.rough_iff_le_minFac h2
      have e2 : SieveTree.rough z n ↔ z ≤ Nat.minFac n := SieveStops2.rough_iff_le_minFac h2
      simp only [e1, e2]
      by_cases ha : P ≤ Nat.minFac n
      · have hb : z ≤ Nat.minFac n := le_trans hzP ha
        simp [hWn, ha, hb, not_lt.2 ha]
      · by_cases hb : z ≤ Nat.minFac n
        · simp [hWn, ha, hb, not_le.1 ha]
        · simp [hWn, ha, hb]
  · have h0 : ∀ p, ¬ (W * p ∣ n ∧ SieveTree.rough p n) := fun p h => hWn (dvd_trans (Dvd.intro _ rfl) h.1)
    simp [hWn, h0]

/-- One more prime `p ∈ [z, rt_last)` after the family's primes. -/
def extS {k' : ℕ} (z : ℝ) (spec : List (Atom (k' + 1))) : List (Atom (k' + 2)) :=
  spec.map Atom.lift ++ [Atom.ltVar (Fin.last k').castSucc (Fin.last (k' + 1)), Atom.ge (Fin.last (k' + 1)) z]

theorem mem_famSet_extS {k' Y z : ℕ} {spec : List (Atom (k' + 1))} {x : Fin (k' + 2) → ℕ} :
    x ∈ famSet (k' + 2) Y (extS (z : ℝ) spec) ↔
      Fin.init x ∈ famSet (k' + 1) Y spec ∧ x (Fin.last _) ≤ Y ∧ (x (Fin.last _)).Prime ∧
        z ≤ x (Fin.last _) ∧ x (Fin.last _) < x (Fin.last k').castSucc := by
  simp only [mem_famSet, extS, List.forall_mem_append, List.forall_mem_map, Atom.lift_sem, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true, Atom.sem_ltVar, Atom.sem_ge, Nat.cast_le]
  constructor
  · rintro ⟨hx, hA, hlt, hz⟩
    exact ⟨⟨fun i => hx i.castSucc, hA⟩, (hx _).1, (hx _).2, hz, hlt⟩
  · rintro ⟨⟨hx, hA⟩, hY, hp, hz, hlt⟩
    refine ⟨fun i => ?_, hA, hlt, hz⟩
    induction i using Fin.lastCases with
    | last => exact ⟨hY, hp⟩
    | cast i => exact hx i

/-- **The extension's bijection.** The pairs `(rt, p)` with `rt` in the family and `p ∈ [z, rt_last)` prime are the
tuples of the extended family. -/
theorem sum_ext_eq {M : Type*} [AddCommMonoid M] {k' Y z : ℕ} (spec : List (Atom (k' + 1)))
    (G : (Fin (k' + 2) → ℕ) → M) :
    ∑ rt ∈ famSet (k' + 1) Y spec, ∑ p ∈ SieveTree.primesIco z (rt (Fin.last k')), G (Fin.snoc rt p) =
      ∑ x ∈ famSet (k' + 2) Y (extS (z : ℝ) spec), G x := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => Fin.snoc x.1 x.2) (fun x => ⟨Fin.init x, x (Fin.last _)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨rt, p⟩ h
    rw [Finset.mem_sigma] at h
    obtain ⟨hrt, hp⟩ := h
    dsimp only at hrt hp
    rw [SieveTree.mem_primesIco] at hp
    show (Fin.snoc rt p : Fin (k' + 2) → ℕ) ∈ _
    rw [mem_famSet_extS]
    have hrtY := ((mem_famSet.1 hrt).1 (Fin.last k')).1
    simp only [Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]
    exact ⟨hrt, by omega, hp.2.2, hp.1, hp.2.1⟩
  · intro x hx
    rw [mem_famSet_extS] at hx
    rw [Finset.mem_sigma, SieveTree.mem_primesIco]
    exact ⟨hx.1, hx.2.2.2.1, hx.2.2.2.2, hx.2.2.1⟩
  · rintro ⟨rt, p⟩ _
    simp only [Fin.init_snoc, Fin.snoc_last]
  · intro x _
    simp only [Fin.snoc_init_self]
  · intro _ _
    rfl

theorem prod_snoc {k : ℕ} (rt : Fin k → ℕ) (p : ℕ) : ∏ i, (Fin.snoc rt p : Fin (k + 1) → ℕ) i = (∏ i, rt i) * p := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- **Buchstab's identity on a family**: for a family whose tuples have their last prime least and at least `z`,
`Σ_rt S(A_{∏rt}, rt_last) = Σ_rt S(A_{∏rt}, z) − Σ_{rt'} S(A_{∏rt'}, rt'_last)` over the extended family. -/
theorem buchstab_fam (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' Y z : ℕ} (spec : List (Atom (k' + 1)))
    (hspec : ∀ rt ∈ famSet (k' + 1) Y spec, (∀ i, rt (Fin.last k') ≤ rt i) ∧ z ≤ rt (Fin.last k')) :
    famI g N₁ N₂ (famSet (k' + 1) Y spec) =
      famJ g N₁ N₂ z (famSet (k' + 1) Y spec) - famI g N₁ N₂ (famSet (k' + 2) Y (extS (z : ℝ) spec)) := by
  have hpt : ∀ rt ∈ famSet (k' + 1) Y spec, ∀ n ∈ Ioc N₁ N₂,
      g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) =
        g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0) -
          ∑ p ∈ SieveTree.primesIco z (rt (Fin.last k')),
            g n * (if (∏ i, (Fin.snoc rt p : Fin (k' + 2) → ℕ) i) ∣ n ∧
              SieveTree.rough ((Fin.snoc rt p : Fin (k' + 2) → ℕ) (Fin.last _)) n then 1 else 0) := by
    intro rt hrt n hn
    obtain ⟨hlast, hz⟩ := hspec rt hrt
    have hprime := fun i => ((mem_famSet.1 hrt).1 i).2
    have hW : ∀ p : ℕ, p.Prime → p ∣ ∏ i, rt i → rt (Fin.last k') ≤ p := by
      intro p hp hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hp (hprime i)).1 hi]
      exact hlast i
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hn).1; omega
    rw [buchstab_pt hn0 hz hW, mul_sub, Finset.mul_sum]
    simp only [prod_snoc, Fin.snoc_last]
  unfold famI famJ
  rw [Finset.sum_congr rfl fun rt hrt => Finset.sum_congr rfl (hpt rt hrt)]
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [← sum_ext_eq spec (fun x => ∑ n ∈ Ioc N₁ N₂, g n *
    (if (∏ i, x i) ∣ n ∧ SieveTree.rough (x (Fin.last _)) n then 1 else 0))]
  refine Finset.sum_congr rfl fun rt _ => ?_
  exact Finset.sum_comm

/-! ### Cells, splits and empty terms -/

/-- The atoms of the cell `c` for the prime `t`: `x^{e_c/DEN} ≤ rt_t < x^{(e_c + H)/DEN}`. -/
noncomputable def cellA [SieveCert.Grid] {k : ℕ} (t : Fin k) (x : ℝ) (c : ℕ) : List (Atom k) :=
  [Atom.ge t (x ^ ((SieveCert.e c : ℝ) / SieveCert.DEN)),
    Atom.lt t (x ^ (((SieveCert.e c : ℝ) + SieveCert.H) / SieveCert.DEN))]

theorem cellA_sem [SieveCert.Grid] {k : ℕ} (t : Fin k) (x : ℝ) (c : ℕ) (rt : Fin k → ℕ) :
    (∀ A ∈ cellA t x c, A.sem rt) ↔
      x ^ ((SieveCert.e c : ℝ) / SieveCert.DEN) ≤ rt t ∧
        (rt t : ℝ) < x ^ (((SieveCert.e c : ℝ) + SieveCert.H) / SieveCert.DEN) := by
  simp [cellA, Atom.sem]

/-- For `x > 1`, a prime is in the cell `c` exactly when its exponent `log p/log x` is. -/
theorem cell_iff [SieveCert.Grid] {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) (c : ℕ) :
    (x ^ ((SieveCert.e c : ℝ) / SieveCert.DEN) ≤ p ∧
      (p : ℝ) < x ^ (((SieveCert.e c : ℝ) + SieveCert.H) / SieveCert.DEN)) ↔
      SieveCert.InCell c (Real.log p / Real.log x) := by
  have h := SieveRough.mem_cellP hx (k := c) (p := p)
  rw [SieveRough.cellP, SieveRough.mem_primesIn] at h
  simpa [hp] using h

/-- On a grid with `GridOK`, for `x > 1`, each prime of `[x^{V/DEN}, x^{(V + nH)/DEN})` lies in exactly one cell
`c < n`. -/
theorem exists_unique_cell [SieveCert.Grid] [SieveCert.GridOK] {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (h0 : x ^ ((SieveCert.V : ℝ) / SieveCert.DEN) ≤ p)
    (h1 : (p : ℝ) < x ^ (((SieveCert.V : ℝ) + SieveCert.n * SieveCert.H) / SieveCert.DEN)) :
    (∃ c < SieveCert.n, SieveCert.InCell c (Real.log p / Real.log x)) ∧
      ∀ c c', SieveCert.InCell c (Real.log p / Real.log x) → SieveCert.InCell c' (Real.log p / Real.log x) →
        c = c' := by
  have hD := SieveCert.DEN_pos'
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set α := Real.log p / Real.log x with hα
  have key : ∀ r : ℝ, x ^ r ≤ p ↔ r * SieveCert.DEN ≤ α * SieveCert.DEN := by
    intro r
    rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos (by linarith) r) hp0, Real.log_rpow (by linarith),
      mul_le_mul_iff_of_pos_right hD, hα, le_div_iff₀ hlx]
  have key' : ∀ r : ℝ, (p : ℝ) < x ^ r ↔ α * SieveCert.DEN < r * SieveCert.DEN := by
    intro r
    rw [← not_le, key, not_le]
  rw [key, div_mul_cancel₀ _ hD.ne'] at h0
  rw [key', div_mul_cancel₀ _ hD.ne'] at h1
  refine ⟨SieveCert.exists_cell h0 h1, fun c c' hc hc' => ?_⟩
  have hH : (0 : ℝ) < SieveCert.H := by exact_mod_cast SieveCert.H_pos
  unfold SieveCert.InCell SieveCert.e at hc hc'
  push_cast at hc hc'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (c : ℝ) + 1 ≤ c' := by exact_mod_cast h
    nlinarith [hc.2, hc'.1]
  · have : (c' : ℝ) + 1 ≤ c := by exact_mod_cast h
    nlinarith [hc.1, hc'.2]

/-- A sum over a finite set split by a classifying index: each element in exactly one class. -/
theorem sum_classes {ι : Type*} (F : Finset ι) (φ : ι → ℝ) (P : ℕ → ι → Prop) (s : Finset ℕ)
    (hex : ∀ x ∈ F, ∃ c ∈ s, P c x) (huniq : ∀ x ∈ F, ∀ c c', P c x → P c' x → c = c') :
    ∑ x ∈ F, φ x = ∑ c ∈ s, ∑ x ∈ F.filter (P c), φ x := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨c₀, hc₀, hP⟩ := hex x hx
  rw [Finset.sum_eq_single_of_mem c₀ hc₀ fun c _ hne => ?_]
  · rw [ite_eq_left hP]
  · rw [ite_eq_right fun h => hne (huniq x hx c c₀ h hP)]

theorem famSet_append {k Y : ℕ} (spec spec' : List (Atom k)) :
    famSet k Y (spec ++ spec') = (famSet k Y spec).filter (fun x => ∀ A ∈ spec', A.sem x) := by
  ext x
  simp only [Finset.mem_filter, mem_famSet, List.forall_mem_append, and_assoc]

/-- **The cells of the prime `t`.** On a grid with `GridOK`, if `x > 1` and every tuple of the family has its prime `t`
in `[x^{V/DEN}, x^{(V + nH)/DEN})`, the family's terms are the sum over the cells `c < n` of those with `rt_t` in the
cell `c`. -/
theorem famI_cells [SieveCert.Grid] [SieveCert.GridOK] (g : ℕ → ℝ) (N₁ N₂ : ℕ) {x : ℝ} (hx : 1 < x) {k' Y : ℕ}
    (spec : List (Atom (k' + 1))) (t : Fin (k' + 1))
    (hrange : ∀ rt ∈ famSet (k' + 1) Y spec, x ^ ((SieveCert.V : ℝ) / SieveCert.DEN) ≤ rt t ∧
      (rt t : ℝ) < x ^ (((SieveCert.V : ℝ) + SieveCert.n * SieveCert.H) / SieveCert.DEN)) :
    famI g N₁ N₂ (famSet (k' + 1) Y spec) =
      ∑ c ∈ Finset.range SieveCert.n, famI g N₁ N₂ (famSet (k' + 1) Y (spec ++ cellA t x c)) := by
  unfold famI
  have hP : ∀ rt ∈ famSet (k' + 1) Y spec, (rt t).Prime := fun rt hrt => ((mem_famSet.1 hrt).1 t).2
  rw [sum_classes _ _ (fun c rt => ∀ A ∈ cellA t x c, A.sem rt) (Finset.range SieveCert.n)]
  · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext rt
    simp only [famSet_append, Finset.mem_filter]
  · intro rt hrt
    obtain ⟨⟨c, hc, hin⟩, -⟩ := exists_unique_cell hx (hP rt hrt) (hrange rt hrt).1 (hrange rt hrt).2
    exact ⟨c, Finset.mem_range.2 hc, (cellA_sem t x c rt).2 ((cell_iff hx (hP rt hrt) c).2 hin)⟩
  · intro rt hrt c c' h h'
    rw [cellA_sem, cell_iff hx (hP rt hrt)] at h h'
    exact (exists_unique_cell hx (hP rt hrt) (hrange rt hrt).1 (hrange rt hrt).2).2 c c' h h'

/-- **A split** of a family by an atom and its complement. -/
theorem famI_split (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' Y : ℕ} (spec : List (Atom (k' + 1))) (A B : Atom (k' + 1))
    (hAB : ∀ rt : Fin (k' + 1) → ℕ, B.sem rt ↔ ¬ A.sem rt) :
    famI g N₁ N₂ (famSet (k' + 1) Y spec) =
      famI g N₁ N₂ (famSet (k' + 1) Y (spec ++ [A])) + famI g N₁ N₂ (famSet (k' + 1) Y (spec ++ [B])) := by
  unfold famI
  rw [famSet_append, famSet_append, ← Finset.sum_filter_add_sum_filter_not (famSet (k' + 1) Y spec)
    (fun rt => ∀ A' ∈ [A], A'.sem rt)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext rt
  simp only [Finset.mem_filter, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    hAB]

/-- A family none of whose terms has an `n ∈ (N₁, N₂]` contributes `0`. -/
theorem famI_eq_zero (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ))
    (h : ∀ rt ∈ F, ∀ n ∈ Ioc N₁ N₂, ¬ ((∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n)) :
    famI g N₁ N₂ F = 0 :=
  Finset.sum_eq_zero fun rt hrt => Finset.sum_eq_zero fun n hn => by rw [ite_eq_right (h rt hrt n hn), mul_zero]

/-! ### Chains -/

/-- A chain: strictly decreasing primes in `[z₀, z_top)`. -/
def Chain (z₀ ztop : ℕ) {k : ℕ} (rt : Fin k → ℕ) : Prop :=
  StrictAnti rt ∧ (∀ i, z₀ ≤ rt i) ∧ ∀ i, rt i < ztop

theorem chain_append {k Y z₀ ztop : ℕ} {spec : List (Atom k)} (spec' : List (Atom k))
    (h : ∀ rt ∈ famSet k Y spec, Chain z₀ ztop rt) : ∀ rt ∈ famSet k Y (spec ++ spec'), Chain z₀ ztop rt := by
  intro rt hrt
  rw [famSet_append, Finset.mem_filter] at hrt
  exact h rt hrt.1

theorem chain_ext {k' Y z₀ ztop : ℕ} {spec : List (Atom (k' + 1))}
    (h : ∀ rt ∈ famSet (k' + 1) Y spec, Chain z₀ ztop rt) :
    ∀ x ∈ famSet (k' + 2) Y (extS (z₀ : ℝ) spec), Chain z₀ ztop x := by
  intro x hx
  rw [mem_famSet_extS] at hx
  obtain ⟨hinit, -, -, hz, hlt⟩ := hx
  obtain ⟨hsa, hge, hlt'⟩ := h _ hinit
  have hcs : ∀ i : Fin (k' + 1), x i.castSucc = Fin.init x i := fun i => rfl
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    induction i using Fin.lastCases with
    | last => simpa using hlt
    | cast i =>
      have := (Fin.strictAnti_iff_succ_lt.1 hsa) i
      simpa [Fin.init] using this
  · induction i using Fin.lastCases with
    | last => exact hz
    | cast i => rw [hcs]; exact hge i
  · induction i using Fin.lastCases with
    | last => exact lt_trans hlt (by rw [hcs]; exact hlt' _)
    | cast i => rw [hcs]; exact hlt' i

/-! ### Membership through the atoms -/

theorem sem_of_mem {k Y : ℕ} {spec : List (Atom k)} {rt : Fin k → ℕ} (hrt : rt ∈ famSet k Y spec) {A : Atom k}
    (hA : A ∈ spec) : A.sem rt :=
  (mem_famSet.1 hrt).2 A hA

theorem famSet_mono {k Y : ℕ} {spec spec' : List (Atom k)} (h : ∀ A ∈ spec, A ∈ spec') :
    famSet k Y spec' ⊆ famSet k Y spec := by
  intro rt hrt
  rw [mem_famSet] at hrt ⊢
  exact ⟨hrt.1, fun A hA => hrt.2 A (h A hA)⟩

/-- A prime in the cell `c`: `x^{e_c/DEN} ≤ p < x^{(e_c + H)/DEN}`. -/
def InC [SieveCert.Grid] (x : ℝ) (c p : ℕ) : Prop :=
  x ^ ((SieveCert.e c : ℝ) / SieveCert.DEN) ≤ p ∧ (p : ℝ) < x ^ (((SieveCert.e c : ℝ) + SieveCert.H) / SieveCert.DEN)

theorem inC_of_mem [SieveCert.Grid] {k Y : ℕ} {spec : List (Atom k)} {rt : Fin k → ℕ} (hrt : rt ∈ famSet k Y spec)
    {t : Fin k} {x : ℝ} {c : ℕ} (h : ∀ A ∈ cellA t x c, A ∈ spec) : InC x c (rt t) :=
  (cellA_sem t x c rt).1 fun A hA => sem_of_mem hrt (h A hA)

theorem init_mem {k' Y z : ℕ} {spec : List (Atom (k' + 1))} {spec' : List (Atom (k' + 2))}
    {rt : Fin (k' + 2) → ℕ} (hrt : rt ∈ famSet (k' + 2) Y spec') (h : ∀ A ∈ extS (z : ℝ) spec, A ∈ spec') :
    Fin.init rt ∈ famSet (k' + 1) Y spec :=
  (mem_famSet_extS.1 (famSet_mono h hrt)).1

/-- A family whose products are at most `N₁` and whose products times their last prime exceed `N₂` contributes `0`:
its `n = (∏rt)c ∈ (N₁, N₂]` would have `c ≥ 2` with no prime factor below `rt_last`. -/
theorem famI_vanish (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ))
    (h : ∀ rt ∈ F, (∏ i, rt i) ≤ N₁ ∧ N₂ < (∏ i, rt i) * rt (Fin.last k')) :
    famI g N₁ N₂ F = 0 := by
  refine famI_eq_zero g N₁ N₂ F fun rt hrt m hm hdr => ?_
  obtain ⟨hW, hN⟩ := h rt hrt
  obtain ⟨⟨c, rfl⟩, hr⟩ := hdr
  rw [Finset.mem_Ioc] at hm
  set W := ∏ i, rt i with hWdef
  have hc2 : 2 ≤ c := by
    by_contra hlt
    have h1 : W * c ≤ W * 1 := Nat.mul_le_mul_left W (by omega)
    omega
  have hrc : SieveTree.rough (rt (Fin.last k')) c := fun p hp1 hpp hpc => hr p hp1 hpp (dvd_mul_of_dvd_right hpc W)
  have hmin := (SieveStops2.rough_iff_le_minFac hc2).1 hrc
  have hmc := Nat.minFac_le (by omega : 0 < c)
  have : W * rt (Fin.last k') ≤ W * c := Nat.mul_le_mul_left W (by omega)
  omega

end SieveDecomp
