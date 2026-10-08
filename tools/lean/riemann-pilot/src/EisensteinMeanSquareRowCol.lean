import EisensteinMeanSquarePoisson

/-! # The mean square in row/column form (round 308)

S4 of round 291's plan, part 8: the second half of the algebra in the companion paper's proof of
its Proposition 4.5. Round 307's identity is carried, as one exact identity (`meanSquare_rowcol`), to
the form the paper reaches just before its change of variables `b = g/e, f = ev, k = eh`, with the
paired factor expanded in characters modulo `4`.

* **Reindexing sums over subsets** (generic): splitting a pair `A₁, A₂` into `B = A₁∩A₂` and the
  differences (`sum_powerset_pair_split`), splitting off `T ⊆ B` (`sum_powerset_sub_split`), both at
  once (`sum_pair_T_split`), and the paper's `1_{(z₁,z₂)=1} = Σ_{v∣z₁,v∣z₂} μ(v)` as
  `Σ_{C₁∩C₂=∅} F(C₁, C₂) = Σ_V (−1)^{|V|}·Σ_{M₁,M₂⊆U∖V} F(V ∪ M₁, V ∪ M₂)` (`sum_disjoint_mobius`).
* **Bounded norms**: `N(a + bω) = (a − b/2)² + 3b²/4` (`absNorm_crd`); the finite set `eltsLe Y` of
  elements of norm at most `Y` (`mem_eltsLe`) and `primesLe Y` of primes (`mem_primesLe`).
* **The paired factor in characters modulo `4`**: round 304's factor as a function of the two classes
  (`pairPsiCls`, well defined by `pairFactor_eq_of_mod_four`: `pairPsi_eq_cls`), of norm at most `1`
  (`norm_pairPsiCls_le`, so round 306's `norm_pairCoeff_le` bounds its coefficients);
  `a_ξ(idl C) = a(C)·ξ(C mod 4)`
  (`aXi_idl`); and `ā(C₁)a(C₂)Ψ(C₁, C₂) = Σ_{ξ₁,ξ₂} ĉ(ξ₁⁻¹, ξ₂)·ā_{ξ₁}(C₁)a_{ξ₂}(C₂)` for disjoint
  `C₁, C₂` (`pairTerm_expand`), in place of the paper's (4.15).
* **The zero frequency** (`tsum_mu_eq`): the dual sum is its `μ = 0` term, present only for
  `C₁ = C₂ = ∅`, plus a finite sum over nonzero `μ`; the paper: "The zero frequency occurs only when
  `z₁ = z₂ = 1`".
* **Factoring the columns** (`col_factor`): for `z_j = V ∪ M_j`, the paper's
  `a_ξ(vm) = a_ξ(v)a_ξ(m)χ_m(v)⁴` and `χ_m(he⁵v⁴) = χ_m(kf⁴)` give a row factor
  `ā_{ξ₁}(V)a_{ξ₂}(V)|χ_V(μ)|²` times the column coefficients `colA ξ k f M = a_ξ(M)(k/M)₆(f/M)₆⁴` at
  `k = d_T μ`, `f = d_T v`. The weights become `2H·N(b)/(√3·Z)·W₀·W₀` with `W₀(x) = x^{−1/2}W(x)`
  (`WW_kap`).
* **`meanSquare_rowcol`**: the smoothed mean square is the zero frequency plus
  `Σ_{ξ₁,ξ₂} ĉ(ξ₁⁻¹, ξ₂)·Σ_{b,T,V,μ,M₁,M₂} rcTerm`. Here `rcTerm` is the sign `(−1)^{|T|+|V|}`, the
  row factor, the normalization `2H·N(b)/(√3·Z)`, the conjugate of `colA ξ₁ k f M₁`, `colA ξ₂ k f M₂`,
  `W₀·W₀` and the dual weight `dualW`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### Reindexing sums over subsets -/

section Reindex

variable {α : Type*} [DecidableEq α]

/-- `Σ_{C ⊆ U, V ⊆ C} g(C) = Σ_{M ⊆ U∖V} g(V ∪ M)` for `V ⊆ U`. -/
theorem sum_supersets (U V : Finset α) (hV : V ⊆ U) (g : Finset α → ℂ) :
    ∑ C ∈ U.powerset.filter (V ⊆ ·), g C = ∑ M ∈ (U \ V).powerset, g (V ∪ M) := by
  refine (Finset.sum_bij' (fun C _ => C \ V) (fun M _ => V ∪ M) ?_ ?_ ?_ ?_ ?_).symm |>.symm
  · intro C hC
    rw [Finset.mem_filter, Finset.mem_powerset] at hC
    rw [Finset.mem_powerset]; exact Finset.sdiff_subset_sdiff hC.1 le_rfl
  · intro M hM
    rw [Finset.mem_powerset] at hM
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.union_subset hV (hM.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  · intro C hC
    rw [Finset.mem_filter] at hC
    exact Finset.union_sdiff_of_subset hC.2
  · intro M hM
    rw [Finset.mem_powerset] at hM
    have hd : Disjoint M V := Finset.disjoint_of_subset_left hM Finset.sdiff_disjoint
    rw [Finset.union_sdiff_left, hd.sdiff_eq_left]
  · intro C hC
    rw [Finset.mem_filter] at hC
    rw [Finset.union_sdiff_of_subset hC.2]

/-- For fixed `B ⊆ U`: the pairs `A₁, A₂ ⊆ U` with `A₁ ∩ A₂ = B` are the `(B ∪ C₁, B ∪ C₂)` with
`C₁, C₂ ⊆ U∖B` disjoint. -/
theorem sum_pair_inter_eq (U B : Finset α) (hB : B ⊆ U) (f : Finset α → Finset α → ℂ) :
    ∑ A1 ∈ U.powerset, ∑ A2 ∈ U.powerset, (if A1 ∩ A2 = B then f A1 A2 else 0) =
      ∑ C1 ∈ (U \ B).powerset, ∑ C2 ∈ (U \ B).powerset,
        (if Disjoint C1 C2 then f (B ∪ C1) (B ∪ C2) else 0) := by
  rw [← Finset.sum_product' (f := fun A1 A2 => if A1 ∩ A2 = B then f A1 A2 else 0),
    ← Finset.sum_product' (f := fun C1 C2 => if Disjoint C1 C2 then f (B ∪ C1) (B ∪ C2) else 0)]
  rw [← Finset.sum_filter (fun p : Finset α × Finset α => p.1 ∩ p.2 = B),
    ← Finset.sum_filter (fun q : Finset α × Finset α => Disjoint q.1 q.2)]
  refine Finset.sum_bij' (fun p _ => (p.1 \ B, p.2 \ B)) (fun q _ => (B ∪ q.1, B ∪ q.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A1, A2⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨⟨Finset.sdiff_subset_sdiff h1 le_rfl, Finset.sdiff_subset_sdiff h2 le_rfl⟩, ?_⟩
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_sdiff] at hx1 hx2
    exact hx1.2 (h3 ▸ Finset.mem_inter.2 ⟨hx1.1, hx2.1⟩)
  · rintro ⟨C1, C2⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hq ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    refine ⟨⟨Finset.union_subset hB (h1.trans Finset.sdiff_subset),
      Finset.union_subset hB (h2.trans Finset.sdiff_subset)⟩, ?_⟩
    rw [← Finset.union_inter_distrib_left, Finset.disjoint_iff_inter_eq_empty.1 h3,
      Finset.union_empty]
  · rintro ⟨A1, A2⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp
    obtain ⟨-, h3⟩ := hp
    have hB1 : B ⊆ A1 := h3 ▸ Finset.inter_subset_left
    have hB2 : B ⊆ A2 := h3 ▸ Finset.inter_subset_right
    simp only [Finset.union_sdiff_of_subset hB1, Finset.union_sdiff_of_subset hB2]
  · rintro ⟨C1, C2⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hq
    obtain ⟨⟨h1, h2⟩, -⟩ := hq
    have hd1 : Disjoint C1 B := Finset.disjoint_of_subset_left h1 Finset.sdiff_disjoint
    have hd2 : Disjoint C2 B := Finset.disjoint_of_subset_left h2 Finset.sdiff_disjoint
    simp only [Finset.union_sdiff_left, hd1.sdiff_eq_left, hd2.sdiff_eq_left]
  · rintro ⟨A1, A2⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp
    obtain ⟨-, h3⟩ := hp
    have hB1 : B ⊆ A1 := h3 ▸ Finset.inter_subset_left
    have hB2 : B ⊆ A2 := h3 ▸ Finset.inter_subset_right
    simp only [Finset.union_sdiff_of_subset hB1, Finset.union_sdiff_of_subset hB2]

/-- **Splitting a pair of subsets** into its intersection and the two differences:
`Σ_{A₁,A₂⊆U} f(A₁, A₂) = Σ_{B⊆U} Σ_{C₁,C₂⊆U∖B, C₁∩C₂=∅} f(B ∪ C₁, B ∪ C₂)`. -/
theorem sum_powerset_pair_split (U : Finset α) (f : Finset α → Finset α → ℂ) :
    ∑ A1 ∈ U.powerset, ∑ A2 ∈ U.powerset, f A1 A2 =
      ∑ B ∈ U.powerset, ∑ C1 ∈ (U \ B).powerset, ∑ C2 ∈ (U \ B).powerset,
        (if Disjoint C1 C2 then f (B ∪ C1) (B ∪ C2) else 0) := by
  have h1 : ∀ A1 ∈ U.powerset, ∀ A2 ∈ U.powerset,
      f A1 A2 = ∑ B ∈ U.powerset, (if A1 ∩ A2 = B then f A1 A2 else 0) := by
    intro A1 hA1 A2 _
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_powerset.2 ((Finset.inter_subset_left).trans
      (Finset.mem_powerset.1 hA1)))]
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => h1 A1 hA1 A2 hA2]
  rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun B hB => sum_pair_inter_eq U B (Finset.mem_powerset.1 hB) f

/-- **Splitting off a subset**: `Σ_{B⊆U} Σ_{T⊆B} g(B, T) = Σ_{b⊆U} Σ_{T⊆U∖b} g(b ∪ T, T)`. -/
theorem sum_powerset_sub_split (U : Finset α) (g : Finset α → Finset α → ℂ) :
    ∑ B ∈ U.powerset, ∑ T ∈ B.powerset, g B T =
      ∑ b ∈ U.powerset, ∑ T ∈ (U \ b).powerset, g (b ∪ T) T := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨p.1 \ p.2, p.2⟩) (fun q _ => ⟨q.1 ∪ q.2, q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨B, T⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp ⊢
    exact ⟨Finset.sdiff_subset.trans hp.1,
      Finset.subset_sdiff.2 ⟨hp.2.trans hp.1, Finset.disjoint_sdiff⟩⟩
  · rintro ⟨b, T⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hq ⊢
    exact ⟨Finset.union_subset hq.1 (hq.2.trans Finset.sdiff_subset), Finset.subset_union_right⟩
  · rintro ⟨B, T⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp
    simp only [Finset.sdiff_union_of_subset hp.2]
  · rintro ⟨b, T⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hq
    have hd : Disjoint b T := (Finset.subset_sdiff.1 hq.2).2.symm
    simp only [Finset.union_sdiff_right, hd.sdiff_eq_left]
  · rintro ⟨B, T⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp
    simp only [Finset.sdiff_union_of_subset hp.2]

/-- **Möbius inversion of disjointness** (the paper's `1_{(z₁,z₂)=1} = Σ_{v∣z₁, v∣z₂} μ(v)`):
`Σ_{C₁,C₂⊆U, C₁∩C₂=∅} F(C₁, C₂) = Σ_{V⊆U} (−1)^{|V|} Σ_{M₁,M₂⊆U∖V} F(V ∪ M₁, V ∪ M₂)`. -/
theorem sum_disjoint_mobius (U : Finset α) (F : Finset α → Finset α → ℂ) :
    ∑ C1 ∈ U.powerset, ∑ C2 ∈ U.powerset, (if Disjoint C1 C2 then F C1 C2 else 0) =
      ∑ V ∈ U.powerset, (-1 : ℂ) ^ V.card *
        ∑ M1 ∈ (U \ V).powerset, ∑ M2 ∈ (U \ V).powerset, F (V ∪ M1) (V ∪ M2) := by
  have h1 : ∀ C1 ∈ U.powerset, ∀ C2 ∈ U.powerset, (if Disjoint C1 C2 then F C1 C2 else 0) =
      ∑ V ∈ U.powerset, (if V ⊆ C1 ∧ V ⊆ C2 then (-1 : ℂ) ^ V.card * F C1 C2 else 0) := by
    intro C1 hC1 C2 _
    have hsub : (C1 ∩ C2).powerset = U.powerset.filter (fun V => V ⊆ C1 ∧ V ⊆ C2) := by
      ext V
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_inter_iff]
      constructor
      · intro h; exact ⟨h.1.trans (Finset.mem_powerset.1 hC1), h⟩
      · intro h; exact h.2
    rw [← Finset.sum_filter, ← hsub, ← Finset.sum_mul]
    have hs : ∑ V ∈ (C1 ∩ C2).powerset, (-1 : ℂ) ^ V.card =
        if C1 ∩ C2 = ∅ then 1 else 0 := by
      have := Finset.sum_powerset_neg_one_pow_card (x := C1 ∩ C2)
      exact_mod_cast this
    rw [hs]
    by_cases h : Disjoint C1 C2
    · rw [ite_eq_left h, ite_eq_left (Finset.disjoint_iff_inter_eq_empty.1 h), one_mul]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Finset.disjoint_iff_inter_eq_empty.2 h')),
        zero_mul]
  rw [Finset.sum_congr rfl fun C1 hC1 => Finset.sum_congr rfl fun C2 hC2 => h1 C1 hC1 C2 hC2]
  rw [Finset.sum_congr rfl fun C1 _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun V hV => ?_
  have hVU : V ⊆ U := Finset.mem_powerset.1 hV
  have e : ∀ C1 ∈ U.powerset, ∑ C2 ∈ U.powerset,
      (if V ⊆ C1 ∧ V ⊆ C2 then (-1 : ℂ) ^ V.card * F C1 C2 else 0) =
      if V ⊆ C1 then (-1 : ℂ) ^ V.card * ∑ C2 ∈ U.powerset.filter (V ⊆ ·), F C1 C2 else 0 := by
    intro C1 _
    split_ifs with hC1
    · rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun C2 _ => by
        by_cases hC2 : V ⊆ C2
        · rw [ite_eq_left ⟨hC1, hC2⟩, ite_eq_left hC2]
        · rw [ite_eq_right (fun h => hC2 h.2), ite_eq_right hC2]
    · exact Finset.sum_eq_zero fun C2 _ => ite_eq_right (fun h => hC1 h.1)
  rw [Finset.sum_congr rfl e, ← Finset.sum_filter, ← Finset.mul_sum, sum_supersets U V hVU]
  congr 1
  refine Finset.sum_congr rfl fun M1 _ => ?_
  exact sum_supersets U V hVU _

end Reindex

section Reindex2

variable {α : Type*} [DecidableEq α]

theorem pair_split_facts {B C1 C2 : Finset α} (h1 : Disjoint C1 B) (h2 : Disjoint C2 B)
    (h12 : Disjoint C1 C2) :
    (B ∪ C1) ∩ (B ∪ C2) = B ∧ (B ∪ C1) \ (B ∪ C2) = C1 ∧ (B ∪ C2) \ (B ∪ C1) = C2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.union_inter_distrib_left, Finset.disjoint_iff_inter_eq_empty.1 h12,
      Finset.union_empty]
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hn⟩; push Not at hn; tauto
    · intro hx
      exact ⟨Or.inr hx, by
        push Not
        exact ⟨Finset.disjoint_left.1 h1 hx, Finset.disjoint_left.1 h12 hx⟩⟩
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx, hn⟩; push Not at hn; tauto
    · intro hx
      exact ⟨Or.inr hx, by
        push Not
        exact ⟨Finset.disjoint_left.1 h2 hx, Finset.disjoint_right.1 h12 hx⟩⟩

/-- **The pair split with the exclusion subsets**:
`Σ_{A₁,A₂⊆U} w(A₁,A₂)·Σ_{T⊆A₁∩A₂} τ(A₁∖A₂, A₂∖A₁, T) =
Σ_{b⊆U} Σ_{T⊆U∖b} Σ_{C₁,C₂⊆U∖(b∪T), C₁∩C₂=∅} w(b∪T∪C₁, b∪T∪C₂)·τ(C₁, C₂, T)`. -/
theorem sum_pair_T_split (U : Finset α) (w : Finset α → Finset α → ℂ)
    (τ : Finset α → Finset α → Finset α → ℂ) :
    ∑ A1 ∈ U.powerset, ∑ A2 ∈ U.powerset,
        w A1 A2 * ∑ T ∈ (A1 ∩ A2).powerset, τ (A1 \ A2) (A2 \ A1) T =
      ∑ b ∈ U.powerset, ∑ T ∈ (U \ b).powerset,
        ∑ C1 ∈ (U \ (b ∪ T)).powerset, ∑ C2 ∈ (U \ (b ∪ T)).powerset,
          (if Disjoint C1 C2 then w ((b ∪ T) ∪ C1) ((b ∪ T) ∪ C2) * τ C1 C2 T else 0) := by
  rw [sum_powerset_pair_split U]
  -- simplify the split pairs
  have e : ∀ B ∈ U.powerset, ∀ C1 ∈ (U \ B).powerset, ∀ C2 ∈ (U \ B).powerset,
      (if Disjoint C1 C2 then w (B ∪ C1) (B ∪ C2) *
        ∑ T ∈ ((B ∪ C1) ∩ (B ∪ C2)).powerset,
          τ ((B ∪ C1) \ (B ∪ C2)) ((B ∪ C2) \ (B ∪ C1)) T else 0) =
      ∑ T ∈ B.powerset, (if Disjoint C1 C2 then w (B ∪ C1) (B ∪ C2) * τ C1 C2 T else 0) := by
    intro B _ C1 hC1 C2 hC2
    by_cases h12 : Disjoint C1 C2
    · have hd1 : Disjoint C1 B :=
        Finset.disjoint_of_subset_left (Finset.mem_powerset.1 hC1) Finset.sdiff_disjoint
      have hd2 : Disjoint C2 B :=
        Finset.disjoint_of_subset_left (Finset.mem_powerset.1 hC2) Finset.sdiff_disjoint
      obtain ⟨e1, e2, e3⟩ := pair_split_facts hd1 hd2 h12
      rw [ite_eq_left h12, e1, e2, e3, Finset.mul_sum]
      exact Finset.sum_congr rfl fun T _ => (ite_eq_left h12).symm
    · rw [ite_eq_right h12]
      exact (Finset.sum_eq_zero fun T _ => ite_eq_right h12).symm
  rw [Finset.sum_congr rfl fun B hB => Finset.sum_congr rfl fun C1 hC1 =>
    Finset.sum_congr rfl fun C2 hC2 => e B hB C1 hC1 C2 hC2]
  -- move `T` outward
  have e2 : ∀ B ∈ U.powerset,
      ∑ C1 ∈ (U \ B).powerset, ∑ C2 ∈ (U \ B).powerset, ∑ T ∈ B.powerset,
        (if Disjoint C1 C2 then w (B ∪ C1) (B ∪ C2) * τ C1 C2 T else 0) =
      ∑ T ∈ B.powerset, ∑ C1 ∈ (U \ B).powerset, ∑ C2 ∈ (U \ B).powerset,
        (if Disjoint C1 C2 then w (B ∪ C1) (B ∪ C2) * τ C1 C2 T else 0) := by
    intro B _
    rw [Finset.sum_congr rfl fun C1 _ => Finset.sum_comm, Finset.sum_comm]
  rw [Finset.sum_congr rfl e2]
  exact sum_powerset_sub_split U (fun B T => ∑ C1 ∈ (U \ B).powerset, ∑ C2 ∈ (U \ B).powerset,
    (if Disjoint C1 C2 then w (B ∪ C1) (B ∪ C2) * τ C1 C2 T else 0))

omit [DecidableEq α] in
/-- Extending a double sum from a family of subsets to all subsets, when the summand vanishes
outside the family. -/
theorem sum_family_eq_powerset (U : Finset α) (𝒜 : Finset (Finset α)) (h𝒜 : ∀ A ∈ 𝒜, A ⊆ U)
    (g : Finset α → Finset α → ℂ) (hg : ∀ A1 ⊆ U, ∀ A2 ⊆ U, (A1 ∉ 𝒜 ∨ A2 ∉ 𝒜) → g A1 A2 = 0) :
    ∑ A1 ∈ 𝒜, ∑ A2 ∈ 𝒜, g A1 A2 = ∑ A1 ∈ U.powerset, ∑ A2 ∈ U.powerset, g A1 A2 := by
  have hsub : 𝒜 ⊆ U.powerset := fun A hA => Finset.mem_powerset.2 (h𝒜 A hA)
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun A1 hA1 => ?_
    exact Finset.sum_subset hsub fun A2 hA2 h2 =>
      hg A1 (Finset.mem_powerset.1 hA1) A2 (Finset.mem_powerset.1 hA2) (Or.inr h2)
  · intro A1 hA1 h1
    exact Finset.sum_eq_zero fun A2 hA2 =>
      hg A1 (Finset.mem_powerset.1 hA1) A2 (h𝒜 A2 hA2) (Or.inl h1)

end Reindex2

/-! ### Elements and primes of bounded norm -/

/-- `N(a + bω) = (a − b/2)² + 3b²/4`. -/
theorem absNorm_crd (n : Fin 2 → ℤ) :
    (absNorm (span {crd n}) : ℝ) = ((n 0 : ℝ) - (n 1 : ℝ) / 2) ^ 2 + 3 / 4 * (n 1 : ℝ) ^ 2 := by
  rw [← normSq_σO, σO_crd, Mw_apply]
  obtain ⟨hre, him⟩ := varpi_re_im
  simp only [PlanePoisson.cpt, PlanePoisson.nR, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, hre]
  nlinarith [him]

open Classical in
/-- The elements of norm at most `Y`, a finite set. -/
def eltsLe (Y : ℝ) : Finset (𝓞 K) :=
  ((Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-⌈2 * Real.sqrt Y⌉) ⌈2 * Real.sqrt Y⌉).image
    crd).filter fun μ => (absNorm (span {μ}) : ℝ) ≤ Y

theorem mem_eltsLe {Y : ℝ} {μ : 𝓞 K} : μ ∈ eltsLe Y ↔ (absNorm (span {μ}) : ℝ) ≤ Y := by
  classical
  unfold eltsLe
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨n, rfl⟩ := crd_surjective μ
  refine Finset.mem_image.2 ⟨n, Fintype.mem_piFinset.2 fun i => ?_, rfl⟩
  rw [absNorm_crd] at h
  have hY : 0 ≤ Y := le_trans (by positivity) h
  have hs := Real.sqrt_nonneg Y
  have h1 : |(n 1 : ℝ)| ≤ 2 * Real.sqrt Y := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((n 1 : ℝ) ^ 2) ≤ Real.sqrt (4 * Y) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((n 0 : ℝ) - (n 1 : ℝ) / 2)])
      _ = 2 * Real.sqrt Y := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have h0' : |(n 0 : ℝ) - (n 1 : ℝ) / 2| ≤ Real.sqrt Y := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (n 1 : ℝ)])
  have h0 : |(n 0 : ℝ)| ≤ 2 * Real.sqrt Y := by
    have := abs_sub_abs_le_abs_sub (n 0 : ℝ) ((n 1 : ℝ) / 2)
    rw [abs_div, abs_two] at this
    linarith
  have hc := Int.le_ceil (2 * Real.sqrt Y)
  rw [Finset.mem_Icc]
  fin_cases i
  · simp only [Fin.zero_eta]
    constructor
    · have := neg_abs_le (n 0 : ℝ)
      have : (-(⌈2 * Real.sqrt Y⌉ : ℤ) : ℝ) ≤ (n 0 : ℝ) := by linarith
      exact_mod_cast this
    · have := le_abs_self (n 0 : ℝ)
      have : (n 0 : ℝ) ≤ (⌈2 * Real.sqrt Y⌉ : ℤ) := by linarith
      exact_mod_cast this
  · simp only [Fin.mk_one]
    constructor
    · have := neg_abs_le (n 1 : ℝ)
      have : (-(⌈2 * Real.sqrt Y⌉ : ℤ) : ℝ) ≤ (n 1 : ℝ) := by linarith
      exact_mod_cast this
    · have := le_abs_self (n 1 : ℝ)
      have : (n 1 : ℝ) ≤ (⌈2 * Real.sqrt Y⌉ : ℤ) := by linarith
      exact_mod_cast this

/-- The primes of norm at most `Y`. -/
def primesLe (Y : ℝ) : Finset Pr := (fsLe Y).biUnion id

theorem absNorm_idl_singleton (P : Pr) : absNorm (idl {P}) = absNorm P.1 := by
  rw [absNorm_idl, Finset.prod_singleton]

theorem one_le_absNorm_Pr (P : Pr) : 1 ≤ absNorm P.1 :=
  Nat.one_le_iff_ne_zero.2 (by rw [Ne, absNorm_eq_zero_iff]; exact Pr_ne_bot P)

/-- `N(idl S) ≤ N(idl S')` for `S ⊆ S'`. -/
theorem absNorm_idl_mono {S S' : Finset Pr} (h : S ⊆ S') : absNorm (idl S) ≤ absNorm (idl S') := by
  rw [absNorm_idl, absNorm_idl]
  exact Finset.prod_le_prod_of_subset_of_one_le h fun P _ _ => one_le_absNorm_Pr P

theorem mem_primesLe {Y : ℝ} {P : Pr} : P ∈ primesLe Y ↔ absNorm P.1 ≤ ⌊Y⌋₊ := by
  unfold primesLe
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨A, hA, hP⟩
    rw [← absNorm_idl_singleton]
    exact le_trans (absNorm_idl_mono (Finset.singleton_subset_iff.2 hP)) (mem_fsLe.1 hA)
  · intro h
    exact ⟨{P}, mem_fsLe.2 (by rw [absNorm_idl_singleton]; exact h), Finset.mem_singleton_self P⟩

theorem subset_primesLe {Y : ℝ} {A : Finset Pr} (hA : A ∈ fsLe Y) : A ⊆ primesLe Y :=
  fun _ hP => Finset.mem_biUnion.2 ⟨A, hA, hP⟩

/-! ### The paired factor through characters modulo `4` -/

instance finite_quot4 : Finite (𝓞 K ⧸ span {(4 : 𝓞 K)}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)

instance fintype_mulChar4 : Fintype (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) := Fintype.ofFinite _

instance fintype_units4 : Fintype (𝓞 K ⧸ span {(4 : 𝓞 K)})ˣ := Fintype.ofFinite _

/-- The class modulo `4` of the primary generator `∏_{P∈C} π_P`. -/
def cls4 (C : Finset Pr) : 𝓞 K ⧸ span {(4 : 𝓞 K)} :=
  Ideal.Quotient.mk (span {(4 : 𝓞 K)}) (∏ P ∈ C, πP P)

theorem isUnit_cls4 (C : Finset Pr) : IsUnit (cls4 C) :=
  isUnit_mk_four (IsCoprime.prod_left fun P _ => isCoprime_two (πP P) (h6Pr P))

open Classical in
/-- Round 304's paired factor as a function of the two classes modulo `4`: by
`pairFactor_eq_of_mod_four` it is well defined on the pairs of classes of disjoint sets of primes,
and it is `0` on the other pairs. -/
def pairPsiCls (x y : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : ℂ :=
  if h : ∃ C : Finset Pr × Finset Pr, Disjoint C.1 C.2 ∧ cls4 C.1 = x ∧ cls4 C.2 = y then
    pairPsi h.choose.1 h.choose.2 else 0

theorem pairPsi_eq_cls {C1 C2 : Finset Pr} (hd : Disjoint C1 C2) :
    pairPsi C1 C2 = pairPsiCls (cls4 C1) (cls4 C2) := by
  classical
  have h : ∃ C : Finset Pr × Finset Pr, Disjoint C.1 C.2 ∧ cls4 C.1 = cls4 C1 ∧
      cls4 C.2 = cls4 C2 := ⟨(C1, C2), hd, rfl, rfl⟩
  rw [pairPsiCls, dite_eq_left h]
  obtain ⟨hd', h1, h2⟩ := h.choose_spec
  unfold pairPsi
  exact pairFactor_eq_of_mod_four πP h6Pr C1 C2 h.choose.1 h.choose.2 (hcopPr _) (hcopPr _) hd hd'
    (fun P _ => (πP_spec P).1) (fun P _ => (πP_spec P).1) (Ideal.Quotient.eq.1 h1.symm)
    (Ideal.Quotient.eq.1 h2.symm)

theorem norm_pairPsi (C1 C2 : Finset Pr) : ‖pairPsi C1 C2‖ = 1 := by
  unfold pairPsi
  rw [norm_mul, norm_mul, norm_inv, norm_prod, norm_prod,
    Finset.prod_eq_one fun P _ => norm_chiF_four πP h6Pr P,
    Finset.prod_eq_one fun P _ => norm_chiF_four πP h6Pr P, inv_one, one_mul, one_mul]
  exact norm_gamF πP _ (hcopPr _) _ (fun P _ => chi6_pow_ne_one _ (h6Pr P) (by simp))
    (fun P _ => chiF_pow_pow_six πP h6Pr P 3)

theorem norm_pairPsiCls_le (x y : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : ‖pairPsiCls x y‖ ≤ 1 := by
  classical
  unfold pairPsiCls
  split_ifs with h
  · exact (norm_pairPsi _ _).le
  · rw [norm_zero]; exact zero_le_one

open Classical in
/-- `a_ξ(idl C) = a(C)·ξ(C mod 4)`. -/
theorem aXi_idl (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (C : Finset Pr) :
    aXi ξ (idl C) = aF πP h6Pr C * ξ (cls4 C) := by
  unfold aXi
  rw [ite_eq_left ⟨idl_coprime6 C, idl_squarefree C⟩, alphaI_eq_prod (idl_coprime6 C)
    (idl_squarefree C), gamI_eq_gamF two_ne_zero (idl_coprime6 C) (idl_squarefree C),
    primeSet_idl, pgen_idl, aF]
  rfl

/-- **The pair coefficients in characters modulo `4`** (in place of the paper's (4.15)): for disjoint
`C₁, C₂`, `ā(C₁)a(C₂)Ψ(C₁, C₂) = Σ_{ξ₁,ξ₂} ĉ(ξ₁⁻¹, ξ₂)·ā_{ξ₁}(C₁)·a_{ξ₂}(C₂)`. -/
theorem pairTerm_expand {C1 C2 : Finset Pr} (hd : Disjoint C1 C2) :
    conj (aF πP h6Pr C1) * aF πP h6Pr C2 * pairPsi C1 C2 =
      ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff pairPsiCls ξ1⁻¹ ξ2 * (conj (aXi ξ1 (idl C1)) * aXi ξ2 (idl C2)) := by
  set x := (isUnit_cls4 C1).unit
  set y := (isUnit_cls4 C2).unit
  have hx : (x : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C1 := IsUnit.unit_spec _
  have hy : (y : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C2 := IsUnit.unit_spec _
  have hexp := pair_eq_sum_mulChar pairPsiCls x y
  rw [hx, hy] at hexp
  rw [pairPsi_eq_cls hd, hexp, Finset.mul_sum]
  -- reindex `ξ₁ ↦ ξ₁⁻¹`
  rw [← Equiv.sum_comp (Equiv.inv (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ))]
  refine Finset.sum_congr rfl fun ξ1 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ2 _ => ?_
  have hc : (ξ1⁻¹ : MulChar _ ℂ) (cls4 C1) = conj (ξ1 (cls4 C1)) := by
    rw [← hx, MulChar.inv_apply_eq_inv', conj_eq_inv_of_norm]
    have hord : 0 < orderOf x := orderOf_pos x
    have h1 : ξ1 (x : 𝓞 K ⧸ span {(4 : 𝓞 K)}) ^ orderOf x = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    exact norm_eq_one_of_pow_eq_one h1 hord.ne'
  simp only [Equiv.inv_apply]
  rw [aXi_idl, aXi_idl, map_mul, hc]
  ring

/-! ### The terms in normalized form -/

/-- `N(A)` as a real number. -/
def nI (A : Finset Pr) : ℝ := (absNorm (idl A) : ℝ)

/-- The weight `2H/(√3·√(N(Z₁)N(Z₂))·N(T))` of a term after Poisson summation. -/
def kap (H : ℝ) (Z1 Z2 T : Finset Pr) : ℝ :=
  2 * H / (Real.sqrt 3 * Real.sqrt (nI Z1 * nI Z2) * nI T)

/-- The dual weight `Φ̂(√(4HN(μ)/(3N(Z₁)N(Z₂)N(T))))`. -/
def dualW (H : ℝ) (Z1 Z2 T : Finset Pr) (μ : 𝓞 K) : ℂ :=
  dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) / (3 * (nI Z1 * nI Z2) * nI T)))

theorem span_prod_πP (S : Finset Pr) : span {∏ P ∈ S, πP P} = idl S := by
  rw [← Ideal.prod_span_singleton]
  exact Finset.prod_congr rfl fun P _ => (πP_spec P).2

theorem absNorm_span_prod_πP (S : Finset Pr) :
    (absNorm (span {∏ P ∈ S, πP P}) : ℝ) = nI S := by
  rw [span_prod_πP]; rfl

theorem nI_union {A B : Finset Pr} (h : Disjoint A B) : nI (A ∪ B) = nI A * nI B := by
  unfold nI; rw [idl_union h, map_mul, Nat.cast_mul]

theorem one_le_nI (A : Finset Pr) : 1 ≤ nI A := by
  unfold nI
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rw [Ne, absNorm_eq_zero_iff]; exact idl_ne_bot A)

theorem nI_pos (A : Finset Pr) : 0 < nI A := lt_of_lt_of_le one_pos (one_le_nI A)

theorem nI_empty : nI ∅ = 1 := by
  unfold nI idl; rw [Finset.prod_empty, map_one, Nat.cast_one]

theorem chiS_empty (u : 𝓞 K) : chiS ∅ u = 1 := by unfold chiS; rw [Finset.prod_empty]

theorem chiS_zero {C : Finset Pr} (hC : C.Nonempty) : chiS C 0 = 0 := by
  obtain ⟨P, hP⟩ := hC
  unfold chiS
  exact Finset.prod_eq_zero hP (by rw [map_zero, MulChar.map_zero])

theorem gamF_empty (χ : ∀ P : Pr, MulChar (𝓞 K ⧸ span {πP P}) ℂ) : gamF πP ∅ χ = 1 := by
  unfold gamF
  simp only [Finset.prod_empty]
  rw [gaussTr_one_const, map_one, norm_one, Complex.ofReal_one, div_one]

theorem aF_empty : aF πP h6Pr ∅ = 1 := by
  unfold aF; rw [Finset.prod_empty, map_one, gamF_empty, one_mul]

theorem pairPsi_empty : pairPsi ∅ ∅ = 1 := by
  unfold pairPsi
  simp only [Finset.prod_empty, Finset.empty_union, inv_one, one_mul]
  exact gamF_empty _

/-- `pairSum_poisson` with the norms written through `nI`, `kap` and `dualW`. -/
theorem pairSum_clean (H : ℝ) (hH : 0 < H) (A1 A2 : Finset Pr) :
    (-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
      ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
    ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) *
      (conj (aF πP h6Pr (A1 \ A2)) * aF πP h6Pr (A2 \ A1) * pairPsi (A1 \ A2) (A2 \ A1)) *
      (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
      ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
        dualW H (A1 \ A2) (A2 \ A1) T μ := by
  rw [pairSum_poisson H hH A1 A2]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hd : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  rw [absNorm_span_prod_πP, absNorm_span_prod_πP, nI_union hd]
  rfl

open Classical in
/-- **The zero frequency and the finite dual sum**: if `3R²N(C₁)N(C₂)N(T) ≤ 4HY`, with `Φ̂`
vanishing beyond `R`, then `Σ_μ F̄(μ)·G(μ)` is its `μ = 0` term, `Φ̂(0)` when `C₁ = C₂ = ∅` and `0`
otherwise, plus the finite sum over the nonzero `μ` of norm at most `Y`. -/
theorem tsum_mu_eq (H : ℝ) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0)
    {Y : ℝ} (C1 C2 T : Finset Pr) (hY : 3 * R ^ 2 * (nI C1 * nI C2 * nI T) ≤ 4 * H * Y) :
    ∑' μ : 𝓞 K, conj (chiS C1 μ * conj (chiS C2 μ)) * dualW H C1 C2 T μ =
      (if C1 = ∅ ∧ C2 = ∅ then dualG 0 else 0) +
        ∑ μ ∈ (eltsLe Y).erase 0, conj (chiS C1 μ * conj (chiS C2 μ)) * dualW H C1 C2 T μ := by
  have hP : 0 < nI C1 * nI C2 * nI T := by
    have := nI_pos C1; have := nI_pos C2; have := nI_pos T; positivity
  have hY0 : 0 ≤ Y := by
    have : 0 < 3 * R ^ 2 * (nI C1 * nI C2 * nI T) := by positivity
    nlinarith
  rw [tsum_eq_sum (s := eltsLe Y)]
  · have h00 : (absNorm (span {(0 : 𝓞 K)}) : ℝ) ≤ Y := by
      rw [show (span {(0 : 𝓞 K)} : Ideal (𝓞 K)) = ⊥ from Ideal.span_singleton_eq_bot.2 rfl,
        absNorm_bot, Nat.cast_zero]
      exact hY0
    rw [← Finset.add_sum_erase _ _ (mem_eltsLe.2 h00)]
    congr 1
    have h0 : dualW H C1 C2 T 0 = dualG 0 := by
      unfold dualW; simp
    rw [h0]
    split_ifs with h
    · rw [h.1, h.2, chiS_empty, map_one, mul_one, map_one, one_mul]
    · have hne : C1.Nonempty ∨ C2.Nonempty := by
        by_contra hc
        push Not at hc
        exact h ⟨hc.1, hc.2⟩
      rcases hne with hn | hn
      · rw [chiS_zero hn]; simp
      · rw [chiS_zero hn]; simp
  · intro μ hμ
    rw [mem_eltsLe, not_le] at hμ
    have hG : dualW H C1 C2 T μ = 0 := by
      unfold dualW
      refine hR _ ?_
      rw [show R = Real.sqrt (R ^ 2) from (Real.sqrt_sq hR0.le).symm]
      refine Real.sqrt_le_sqrt ?_
      have hD : 0 < 3 * (nI C1 * nI C2) * nI T := by nlinarith
      rw [le_div_iff₀ hD]
      nlinarith
    rw [hG, mul_zero]

/-! ### Factoring the columns -/

/-- The primary generator `∏_{P∈S} π_P` of `idl S`. -/
def eS (S : Finset Pr) : 𝓞 K := ∏ P ∈ S, πP P

theorem prime_πP (P : Pr) : Prime (πP P) :=
  (Ideal.span_singleton_prime (ne_zero_of_maximal (πP P))).1 (instMaxPr P).isPrime

theorem πP_dvd_πP {P Q : Pr} (h : πP P ∣ πP Q) : P = Q := by
  have hle : span {πP Q} ≤ span {πP P} := Ideal.span_singleton_le_span_singleton.2 h
  rw [(πP_spec P).2, (πP_spec Q).2] at hle
  exact (Subtype.ext (Q.2.1.eq_of_le P.2.1.ne_top hle)).symm

theorem not_dvd_eS {P : Pr} {T : Finset Pr} (hP : P ∉ T) : ¬ πP P ∣ eS T := by
  intro h
  obtain ⟨Q, hQ, hd⟩ := (prime_πP P).dvd_finsetProd_iff _ |>.1 h
  exact hP (πP_dvd_πP hd ▸ hQ)

theorem chiS_mul (M : Finset Pr) (a b : 𝓞 K) : chiS M (a * b) = chiS M a * chiS M b := by
  unfold chiS; rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun P _ => by rw [map_mul, map_mul]

theorem chiS_pow (M : Finset Pr) (a : 𝓞 K) (n : ℕ) : chiS M (a ^ n) = chiS M a ^ n := by
  unfold chiS; rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun P _ => by rw [map_pow, map_pow]

/-- `|χ_V(d_T)|² = 1` for `V` disjoint from `T`. -/
theorem chiS_mul_conj_eS {V T : Finset Pr} (h : Disjoint V T) :
    chiS V (eS T) * conj (chiS V (eS T)) = 1 := by
  classical
  unfold chiS
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun P hP => ?_
  rw [chiF, chi6_mul_conj, ite_eq_right]
  rw [mk_πP_eq_zero_iff]
  exact not_dvd_eS (Finset.disjoint_left.1 h hP)

/-- `χ̄_M(d_T) = χ_M(d_T⁵)` for `M` disjoint from `T`. -/
theorem conj_chiS_eS {M T : Finset Pr} (h : Disjoint M T) :
    conj (chiS M (eS T)) = chiS M (eS T ^ 5) := by
  unfold chiS
  rw [map_prod]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hx : Ideal.Quotient.mk (span {πP P}) (eS T) ≠ 0 := by
    rw [Ne, mk_πP_eq_zero_iff]; exact not_dvd_eS (Finset.disjoint_left.1 h hP)
  have h6 := chi6_pow_six_of_ne_zero (span {πP P}) (h6Pr P) hx
  set z := chiF πP h6Pr P (Ideal.Quotient.mk (span {πP P}) (eS T)) with hzdef
  have hz6 : z ^ 6 = 1 := h6
  have hz : ‖z‖ = 1 := norm_eq_one_of_pow_eq_one hz6 (by norm_num)
  have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz6; norm_num at hz6
  rw [map_pow, map_pow, ← hzdef, conj_eq_inv_of_norm hz]
  calc z⁻¹ = z⁻¹ * z ^ 6 := by rw [hz6, mul_one]
    _ = z ^ 5 := by field_simp

theorem chiS_eS_pow_six {M T : Finset Pr} (h : Disjoint M T) : chiS M (eS T) ^ 6 = 1 := by
  unfold chiS
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun P hP => ?_
  have hx : Ideal.Quotient.mk (span {πP P}) (eS T) ≠ 0 := by
    rw [Ne, mk_πP_eq_zero_iff]; exact not_dvd_eS (Finset.disjoint_left.1 h hP)
  exact chi6_pow_six_of_ne_zero (span {πP P}) (h6Pr P) hx

/-- The column coefficient `a_ξ(𝔪)·(k/𝔪)₆·(f/𝔪)₆⁴` of the dual mean square. -/
def colA (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) (M : Finset Pr) : ℂ :=
  aXi ξ (idl M) * chiS M k * chiS M f ^ 4

/-- **Factoring the columns** (the paper's `a_ξ(vm) = a_ξ(v)a_ξ(m)χ_m(v)⁴` and
`χ_m(h e⁵ v⁴) = χ_m(k f⁴)`): for `z_j = V ∪ M_j` with `T, V, M_j` pairwise disjoint, the coefficient
of a pair splits into a row factor `ā_{ξ₁}(V)a_{ξ₂}(V)|χ_V(μ)|²` and the two column coefficients at
`k = d_T μ`, `f = d_T·v`. -/
theorem col_factor (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {T V M1 M2 : Finset Pr}
    (hVT : Disjoint V T) (h1T : Disjoint M1 T) (h2T : Disjoint M2 T) (h1V : Disjoint V M1)
    (h2V : Disjoint V M2) (μ : 𝓞 K) :
    conj (aXi ξ1 (idl (V ∪ M1))) * aXi ξ2 (idl (V ∪ M2)) *
        (chiS (V ∪ M1) (eS T) * conj (chiS (V ∪ M2) (eS T))) *
        conj (chiS (V ∪ M1) μ * conj (chiS (V ∪ M2) μ)) =
      (conj (aXi ξ1 (idl V)) * aXi ξ2 (idl V) * (chiS V μ * conj (chiS V μ))) *
        (conj (colA ξ1 (eS T * μ) (eS T * eS V) M1) * colA ξ2 (eS T * μ) (eS T * eS V) M2) := by
  have hpg : pgen (idl V) = eS V := pgen_idl V
  rw [idl_union h1V, idl_union h2V, aXi_mul_left ξ1 (idl_coprime6 V) (idl_squarefree V),
    aXi_mul_left ξ2 (idl_coprime6 V) (idl_squarefree V), hpg, sym6_idl, sym6_idl]
  simp only [chiS_union h1V, chiS_union h2V]
  unfold colA
  simp only [chiS_mul, map_mul, map_pow, Complex.conj_conj]
  have e1 := chiS_mul_conj_eS hVT
  have h1 : conj (chiS M1 (eS T)) = chiS M1 (eS T) ^ 5 := by rw [conj_chiS_eS h1T, chiS_pow]
  have h2 : conj (chiS M2 (eS T)) = chiS M2 (eS T) ^ 5 := by rw [conj_chiS_eS h2T, chiS_pow]
  have hm := chiS_eS_pow_six h1T
  rw [h1, h2]
  set m1d := chiS M1 (eS T)
  set A' := conj (aXi ξ1 (idl V)) * conj (aXi ξ1 (idl M1)) * conj (chiS M1 (eS V)) ^ 4 *
    aXi ξ2 (idl V) * aXi ξ2 (idl M2) * chiS M2 (eS V) ^ 4 * chiS M2 (eS T) ^ 5 *
    conj (chiS V μ) * conj (chiS M1 μ) * chiS V μ * chiS M2 μ
  linear_combination (A' * m1d) * e1 - (A' * m1d * (m1d ^ 18 + m1d ^ 12 + m1d ^ 6 + 1)) * hm

/-! ### One pair in characters, frequencies split -/

/-- The term of `(C₁, C₂, T)` for the characters `ξ₁, ξ₂` and the frequencies in `E`. -/
def tauXi (H : ℝ) (E : Finset (𝓞 K)) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (C1 C2 T : Finset Pr) : ℂ :=
  (-1 : ℂ) ^ T.card * (kap H C1 C2 T : ℂ) * (conj (aXi ξ1 (idl C1)) * aXi ξ2 (idl C2)) *
    (chiS C1 (eS T) * conj (chiS C2 (eS T))) *
    ∑ μ ∈ E, conj (chiS C1 μ * conj (chiS C2 μ)) * dualW H C1 C2 T μ

theorem sdiff_eq_empty_both {A1 A2 : Finset Pr} :
    (A1 \ A2 = ∅ ∧ A2 \ A1 = ∅) ↔ A1 = A2 := by
  rw [Finset.sdiff_eq_empty_iff_subset, Finset.sdiff_eq_empty_iff_subset]
  exact ⟨fun h => Finset.Subset.antisymm h.1 h.2, fun h => ⟨h ▸ le_rfl, h ▸ le_rfl⟩⟩

/-- `N(C₁)N(C₂)N(T) ≤ N(A₁)N(A₂)` for `C₁ = A₁∖A₂`, `C₂ = A₂∖A₁`, `T ⊆ A₁∩A₂`. -/
theorem nI_pair_le {A1 A2 T : Finset Pr} (hT : T ⊆ A1 ∩ A2) :
    nI (A1 \ A2) * nI (A2 \ A1) * nI T ≤ nI A1 * nI A2 := by
  have hd : Disjoint (A1 \ A2) T :=
    Finset.disjoint_of_subset_right hT (Finset.disjoint_sdiff_inter A1 A2)
  have h1 : nI (A1 \ A2) * nI T ≤ nI A1 := by
    rw [← nI_union hd]
    unfold nI
    exact_mod_cast absNorm_idl_mono (Finset.union_subset Finset.sdiff_subset
      (hT.trans Finset.inter_subset_left))
  have h2 : nI (A2 \ A1) ≤ nI A2 := by
    unfold nI; exact_mod_cast absNorm_idl_mono Finset.sdiff_subset
  calc nI (A1 \ A2) * nI (A2 \ A1) * nI T = (nI (A1 \ A2) * nI T) * nI (A2 \ A1) := by ring
    _ ≤ nI A1 * nI A2 :=
        mul_le_mul h1 h2 (le_trans zero_le_one (one_le_nI _)) (le_trans zero_le_one (one_le_nI _))

open Classical in
/-- **One pair after Poisson summation, in characters modulo `4`**: for `N(A₁), N(A₂) ≤ M` and
`3R²M² ≤ 4HY` (with `Φ̂` vanishing beyond `R`), `μ(A₁)μ(A₂)·Σ_u χ_{A₁}χ̄_{A₂}·Φ(u/√H)` is the zero
frequency, present only for `A₁ = A₂`, plus `Σ_{ξ₁,ξ₂} ĉ(ξ₁⁻¹, ξ₂)·Σ_{T⊆A₁∩A₂} τ_{ξ₁ξ₂}(A₁∖A₂, A₂∖A₁, T)`
over the nonzero frequencies of norm at most `Y`. -/
theorem pair_char_form (H : ℝ) (hH : 0 < H) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {M Y : ℝ} (hY : 3 * R ^ 2 * M ^ 2 ≤ 4 * H * Y)
    {A1 A2 : Finset Pr} (h1 : nI A1 ≤ M) (h2 : nI A2 ≤ M) :
    (-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
      ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
    (if A1 = A2 then ∑ T ∈ A1.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
      ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff pairPsiCls ξ1⁻¹ ξ2 *
          ∑ T ∈ (A1 ∩ A2).powerset, tauXi H ((eltsLe Y).erase 0) ξ1 ξ2 (A1 \ A2) (A2 \ A1) T := by
  rw [pairSum_clean H hH A1 A2]
  have hd : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  have hM0 : 0 ≤ M := le_trans zero_le_one ((one_le_nI A1).trans h1)
  -- split the frequencies in each term
  have hsplit : ∀ T ∈ (A1 ∩ A2).powerset,
      (-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) *
        (conj (aF πP h6Pr (A1 \ A2)) * aF πP h6Pr (A2 \ A1) * pairPsi (A1 \ A2) (A2 \ A1)) *
        (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
        ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
          dualW H (A1 \ A2) (A2 \ A1) T μ =
      (if A1 = A2 then (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
        ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff pairPsiCls ξ1⁻¹ ξ2 *
            tauXi H ((eltsLe Y).erase 0) ξ1 ξ2 (A1 \ A2) (A2 \ A1) T := by
    intro T hT
    have hTs : T ⊆ A1 ∩ A2 := Finset.mem_powerset.1 hT
    have hYT : 3 * R ^ 2 * (nI (A1 \ A2) * nI (A2 \ A1) * nI T) ≤ 4 * H * Y := by
      have hle := nI_pair_le hTs
      have hMM : nI A1 * nI A2 ≤ M ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (le_trans zero_le_one (one_le_nI A2)) hM0
      nlinarith [sq_nonneg R]
    rw [tsum_mu_eq H hH hR0 hR _ _ _ hYT, mul_add]
    congr 1
    · by_cases he : A1 = A2
      · have he' := sdiff_eq_empty_both.2 he
        rw [ite_eq_left he, ite_eq_left he', he'.1, he'.2, aF_empty, pairPsi_empty, chiS_empty,
          map_one]
        ring
      · have hn : ¬(A1 \ A2 = ∅ ∧ A2 \ A1 = ∅) := fun h => he (sdiff_eq_empty_both.1 h)
        rw [ite_eq_right he, ite_eq_right hn, mul_zero]
    · rw [pairTerm_expand hd]
      have e : ∀ (c S d g : ℂ), c * S * d * g = S * (c * d * g) := fun c S d g => by ring
      rw [e, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ξ1 _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun ξ2 _ => ?_
      unfold tauXi eS
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · split_ifs with he
    · subst he; rw [Finset.inter_self]
    · exact Finset.sum_eq_zero fun T _ => rfl
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ2 _ => ?_
    rw [Finset.mul_sum]

/-- `W₀(x) = x^{−1/2}·W(x)`, the paper's `W₀`. -/
def W0f (W : ℝ → ℝ) (x : ℝ) : ℝ := W x / Real.sqrt x

theorem W_eq_W0f (W : ℝ → ℝ) {x : ℝ} (hx : 0 < x) : W x = W0f W x * Real.sqrt x := by
  unfold W0f; rw [div_mul_cancel₀ _ (Real.sqrt_pos.2 hx).ne']

/-- **The weights after the change of variables**: `W(N(bfm₁)/Z)·W(N(bfm₂)/Z)·2H/(√3·√(N(vm₁)N(vm₂))·N(e))
= 2H·N(b)/(√3·Z)·W₀(N(bfm₁)/Z)·W₀(N(bfm₂)/Z)` for `f = ev`. -/
theorem WW_kap (W : ℝ → ℝ) {Z H nb nT nV n1 n2 : ℝ} (hZ : 0 < Z) (hb : 0 < nb) (hT : 0 < nT)
    (hV : 0 < nV) (h1 : 0 < n1) (h2 : 0 < n2) :
    W (nb * nT * (nV * n1) / Z) * W (nb * nT * (nV * n2) / Z) *
        (2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT)) =
      2 * H * nb / (Real.sqrt 3 * Z) *
        (W0f W (nb * nT * nV * n1 / Z) * W0f W (nb * nT * nV * n2 / Z)) := by
  have hx1 : 0 < nb * nT * nV * n1 / Z := by positivity
  have hx2 : 0 < nb * nT * nV * n2 / Z := by positivity
  rw [show nb * nT * (nV * n1) / Z = nb * nT * nV * n1 / Z by ring,
    show nb * nT * (nV * n2) / Z = nb * nT * nV * n2 / Z by ring, W_eq_W0f W hx1, W_eq_W0f W hx2]
  have hs : Real.sqrt (nb * nT * nV * n1 / Z) * Real.sqrt (nb * nT * nV * n2 / Z) =
      nb * nT * nV * Real.sqrt (n1 * n2) / Z := by
    rw [← Real.sqrt_mul hx1.le, show nb * nT * nV * n1 / Z * (nb * nT * nV * n2 / Z) =
      (nb * nT * nV / Z) ^ 2 * (n1 * n2) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    ring
  have hs2 : Real.sqrt (nV * n1 * (nV * n2)) = nV * Real.sqrt (n1 * n2) := by
    rw [show nV * n1 * (nV * n2) = nV ^ 2 * (n1 * n2) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hV.le]
  have hq : 0 < Real.sqrt (n1 * n2) := Real.sqrt_pos.2 (by positivity)
  have h3 : 0 < Real.sqrt 3 := by positivity
  rw [hs2]
  calc W0f W (nb * nT * nV * n1 / Z) * Real.sqrt (nb * nT * nV * n1 / Z) *
        (W0f W (nb * nT * nV * n2 / Z) * Real.sqrt (nb * nT * nV * n2 / Z)) *
        (2 * H / (Real.sqrt 3 * (nV * Real.sqrt (n1 * n2)) * nT))
      = W0f W (nb * nT * nV * n1 / Z) * W0f W (nb * nT * nV * n2 / Z) *
        (Real.sqrt (nb * nT * nV * n1 / Z) * Real.sqrt (nb * nT * nV * n2 / Z)) *
        (2 * H / (Real.sqrt 3 * (nV * Real.sqrt (n1 * n2)) * nT)) := by ring
    _ = _ := by rw [hs]; field_simp

/-- The term of the dual sum at `(b, T, V, μ, M₁, M₂)`: the row factor, the normalization
`2H·N(b)/(√3·Z)`, the two column coefficients at `k = d_T μ`, `f = d_T v`, the weights `W₀` and
the dual weight. -/
def rcTerm (W : ℝ → ℝ) (Z H : ℝ) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (b T V : Finset Pr) (μ : 𝓞 K) (M1 M2 : Finset Pr) : ℂ :=
  ((-1 : ℂ) ^ T.card * (-1) ^ V.card) *
    (conj (aXi ξ1 (idl V)) * aXi ξ2 (idl V) * (chiS V μ * conj (chiS V μ))) *
    ((2 * H * nI b / (Real.sqrt 3 * Z) : ℝ) : ℂ) *
    (conj (colA ξ1 (eS T * μ) (eS T * eS V) M1) * colA ξ2 (eS T * μ) (eS T * eS V) M2) *
    ((W0f W (nI b * nI T * nI V * nI M1 / Z) * W0f W (nI b * nI T * nI V * nI M2 / Z) : ℝ) : ℂ) *
    dualW H (V ∪ M1) (V ∪ M2) T μ

/-! ### The row/column form of the mean square -/

/-- **One term of the Möbius-expanded sum in row/column form**: for pairwise disjoint
`b, T, V, M_j` (`M₁, M₂` may meet), `(−1)^{|V|}·W(N(b T V M₁)/Z)W(N(b T V M₂)/Z)·τ(V∪M₁, V∪M₂, T)` is
`Σ_{μ∈E} rcTerm(b, T, V, μ, M₁, M₂)`. -/
theorem term_factor (W : ℝ → ℝ) {Z H : ℝ} (hZ : 0 < Z) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (E : Finset (𝓞 K)) {b T V M1 M2 : Finset Pr} (hbT : Disjoint b T) (hbV : Disjoint b V)
    (hb1 : Disjoint b M1) (hb2 : Disjoint b M2) (hTV : Disjoint T V) (hT1 : Disjoint T M1)
    (hT2 : Disjoint T M2) (hV1 : Disjoint V M1) (hV2 : Disjoint V M2) :
    (-1 : ℂ) ^ V.card *
        (((W (nI ((b ∪ T) ∪ (V ∪ M1)) / Z) * W (nI ((b ∪ T) ∪ (V ∪ M2)) / Z)) : ℝ) : ℂ) *
        tauXi H E ξ1 ξ2 (V ∪ M1) (V ∪ M2) T =
      ∑ μ ∈ E, rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 := by
  have hd1 : Disjoint (b ∪ T) (V ∪ M1) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb1⟩, hTV, hT1⟩
  have hd2 : Disjoint (b ∪ T) (V ∪ M2) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb2⟩, hTV, hT2⟩
  have hn1 : nI ((b ∪ T) ∪ (V ∪ M1)) = nI b * nI T * (nI V * nI M1) := by
    rw [nI_union hd1, nI_union hbT, nI_union hV1]
  have hn2 : nI ((b ∪ T) ∪ (V ∪ M2)) = nI b * nI T * (nI V * nI M2) := by
    rw [nI_union hd2, nI_union hbT, nI_union hV2]
  have hk : kap H (V ∪ M1) (V ∪ M2) T =
      2 * H / (Real.sqrt 3 * Real.sqrt (nI V * nI M1 * (nI V * nI M2)) * nI T) := by
    unfold kap; rw [nI_union hV1, nI_union hV2]
  have hWK := WW_kap W (H := H) hZ (nI_pos b) (nI_pos T) (nI_pos V) (nI_pos M1) (nI_pos M2)
  unfold tauXi
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hcf := col_factor ξ1 ξ2 hTV.symm hT1.symm hT2.symm hV1 hV2 μ
  unfold rcTerm
  rw [hn1, hn2, hk]
  have hcast : (((W (nI b * nI T * (nI V * nI M1) / Z) * W (nI b * nI T * (nI V * nI M2) / Z)) :
      ℝ) : ℂ) * ((2 * H / (Real.sqrt 3 * Real.sqrt (nI V * nI M1 * (nI V * nI M2)) * nI T) :
      ℝ) : ℂ) = ((2 * H * nI b / (Real.sqrt 3 * Z) : ℝ) : ℂ) *
      ((W0f W (nI b * nI T * nI V * nI M1 / Z) * W0f W (nI b * nI T * nI V * nI M2 / Z) : ℝ) :
        ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hWK]
  calc (-1 : ℂ) ^ V.card *
        (((W (nI b * nI T * (nI V * nI M1) / Z) * W (nI b * nI T * (nI V * nI M2) / Z)) : ℝ) :
          ℂ) *
        ((-1 : ℂ) ^ T.card *
          ((2 * H / (Real.sqrt 3 * Real.sqrt (nI V * nI M1 * (nI V * nI M2)) * nI T) : ℝ) : ℂ) *
          (conj (aXi ξ1 (idl (V ∪ M1))) * aXi ξ2 (idl (V ∪ M2))) *
          (chiS (V ∪ M1) (eS T) * conj (chiS (V ∪ M2) (eS T))) *
          (conj (chiS (V ∪ M1) μ * conj (chiS (V ∪ M2) μ)) * dualW H (V ∪ M1) (V ∪ M2) T μ))
      = ((-1 : ℂ) ^ T.card * (-1) ^ V.card) *
          ((((W (nI b * nI T * (nI V * nI M1) / Z) * W (nI b * nI T * (nI V * nI M2) / Z)) :
            ℝ) : ℂ) *
          ((2 * H / (Real.sqrt 3 * Real.sqrt (nI V * nI M1 * (nI V * nI M2)) * nI T) : ℝ) : ℂ)) *
          (conj (aXi ξ1 (idl (V ∪ M1))) * aXi ξ2 (idl (V ∪ M2)) *
            (chiS (V ∪ M1) (eS T) * conj (chiS (V ∪ M2) (eS T))) *
            conj (chiS (V ∪ M1) μ * conj (chiS (V ∪ M2) μ))) *
          dualW H (V ∪ M1) (V ∪ M2) T μ := by ring
    _ = _ := by rw [hcast, hcf]; ring

theorem disjoint_of_mem_powerset_sdiff {X Y S : Finset Pr} (h : X ∈ (S \ Y).powerset) :
    Disjoint Y X := ((Finset.subset_sdiff.1 (Finset.mem_powerset.1 h)).2).symm

/-- **The chain for one pair of characters**: from the sum over pairs of sets of primes to the
row/column form. The family `𝒜` is extended to all subsets of `U` (the weights vanish outside it),
split by `sum_pair_T_split`, Möbius-inverted by `sum_disjoint_mobius`, and factored by
`term_factor`. -/
theorem xi_chain (W : ℝ → ℝ) {Z H : ℝ} (hZ : 0 < Z) (E : Finset (𝓞 K))
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : Finset Pr) (𝒜 : Finset (Finset Pr))
    (h𝒜 : ∀ A ∈ 𝒜, A ⊆ U) (hvan : ∀ A ⊆ U, A ∉ 𝒜 → W (nI A / Z) = 0) :
    ∑ A1 ∈ 𝒜, ∑ A2 ∈ 𝒜, (((W (nI A1 / Z) * W (nI A2 / Z)) : ℝ) : ℂ) *
        ∑ T ∈ (A1 ∩ A2).powerset, tauXi H E ξ1 ξ2 (A1 \ A2) (A2 \ A1) T =
      ∑ b ∈ U.powerset, ∑ T ∈ (U \ b).powerset, ∑ V ∈ (U \ (b ∪ T)).powerset, ∑ μ ∈ E,
        ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
          rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 := by
  rw [sum_family_eq_powerset U 𝒜 h𝒜 _ (fun A1 h1 A2 h2 h => by
    rcases h with h | h
    · rw [hvan A1 h1 h]; simp
    · rw [hvan A2 h2 h]; simp)]
  rw [sum_pair_T_split U (fun A1 A2 => (((W (nI A1 / Z) * W (nI A2 / Z)) : ℝ) : ℂ))
    (tauXi H E ξ1 ξ2)]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun T hT => ?_
  rw [sum_disjoint_mobius (U \ (b ∪ T)) (fun C1 C2 =>
    (((W (nI ((b ∪ T) ∪ C1) / Z) * W (nI ((b ∪ T) ∪ C2) / Z)) : ℝ) : ℂ) * tauXi H E ξ1 ξ2 C1 C2 T)]
  refine Finset.sum_congr rfl fun V hV => ?_
  have hbT : Disjoint b T := disjoint_of_mem_powerset_sdiff hT
  have hVbT : Disjoint (b ∪ T) V := disjoint_of_mem_powerset_sdiff hV
  rw [Finset.disjoint_union_left] at hVbT
  have e : ∀ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∀ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
      (-1 : ℂ) ^ V.card * ((((W (nI ((b ∪ T) ∪ (V ∪ M1)) / Z) *
        W (nI ((b ∪ T) ∪ (V ∪ M2)) / Z)) : ℝ) : ℂ) * tauXi H E ξ1 ξ2 (V ∪ M1) (V ∪ M2) T) =
      ∑ μ ∈ E, rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 := by
    intro M1 hM1 M2 hM2
    have hV1 : Disjoint V M1 := disjoint_of_mem_powerset_sdiff hM1
    have hV2 : Disjoint V M2 := disjoint_of_mem_powerset_sdiff hM2
    have hM1' : M1 ⊆ U \ (b ∪ T) := (Finset.mem_powerset.1 hM1).trans Finset.sdiff_subset
    have hM2' : M2 ⊆ U \ (b ∪ T) := (Finset.mem_powerset.1 hM2).trans Finset.sdiff_subset
    have hbT1 : Disjoint (b ∪ T) M1 := ((Finset.subset_sdiff.1 hM1').2).symm
    have hbT2 : Disjoint (b ∪ T) M2 := ((Finset.subset_sdiff.1 hM2').2).symm
    rw [Finset.disjoint_union_left] at hbT1 hbT2
    rw [← mul_assoc]
    exact term_factor W hZ ξ1 ξ2 E hbT hVbT.1 hbT1.1 hbT2.1 hVbT.2 hbT1.2 hbT2.2 hV1 hV2
  rw [Finset.mul_sum]
  calc ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, (-1 : ℂ) ^ V.card *
        ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset, (((W (nI ((b ∪ T) ∪ (V ∪ M1)) / Z) *
          W (nI ((b ∪ T) ∪ (V ∪ M2)) / Z)) : ℝ) : ℂ) * tauXi H E ξ1 ξ2 (V ∪ M1) (V ∪ M2) T
      = ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
          ∑ μ ∈ E, rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 := by
        refine Finset.sum_congr rfl fun M1 hM1 => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun M2 hM2 => e M1 hM1 M2 hM2
    _ = _ := by
        rw [Finset.sum_congr rfl fun M1 _ => Finset.sum_comm, Finset.sum_comm]

theorem nI_le_of_mem_fsLe {M : ℕ} {A : Finset Pr} (hA : A ∈ fsLe (M : ℝ)) : nI A ≤ M := by
  have := mem_fsLe.1 hA
  rw [Nat.floor_natCast] at this
  unfold nI; exact_mod_cast this

theorem W_nI_eq_zero {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)
    {A : Finset Pr} (hA : A ∉ fsLe (⌈β * Z⌉₊ : ℝ)) : W (nI A / Z) = 0 := by
  rw [mem_fsLe, Nat.floor_natCast, not_le] at hA
  refine hW _ ?_
  rw [lt_div_iff₀ hZ]
  have : (⌈β * Z⌉₊ : ℝ) < nI A := by unfold nI; exact_mod_cast hA
  linarith [Nat.le_ceil (β * Z)]

open Classical in
/-- **The mean square in row/column form** (the paper's (4.16) before the dyadic ranges, for each pair
of characters modulo `4`): with `M = ⌈βZ⌉`, `Φ̂` vanishing beyond `R`, `3R²M² ≤ 4HY` and `U` containing
the primes of norm at most `M`, the smoothed mean square of the family is the zero frequency
`Σ_A W(N(A)/Z)²·Σ_{T⊆A} (−1)^{|T|}·2H/(√3·N(T))·Φ̂(0)` plus
`Σ_{ξ₁,ξ₂} ĉ(ξ₁⁻¹, ξ₂)·Σ_{b, T, V, μ, M₁, M₂} rcTerm`, over `b ⊆ U`, `T ⊆ U∖b`, `V ⊆ U∖(b∪T)`, the
nonzero `μ` of norm at most `Y`, and `M₁, M₂ ⊆ U∖(b∪T)∖V`. -/
theorem meanSquare_rowcol {W : ℝ → ℝ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)
    {H : ℝ} (hH : 0 < H) {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {Y : ℝ}
    (hY : 3 * R ^ 2 * (⌈β * Z⌉₊ : ℝ) ^ 2 ≤ 4 * H * Y) (U : Finset Pr)
    (hU : primesLe (⌈β * Z⌉₊ : ℝ) ⊆ U) :
    ∑' u : 𝓞 K, famSum W Z u * conj (famSum W Z u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ A ∈ fsLe (⌈β * Z⌉₊ : ℝ), ((W (nI A / Z) ^ 2 : ℝ) : ℂ) *
          ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 +
        ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff pairPsiCls ξ1⁻¹ ξ2 *
            ∑ b ∈ U.powerset, ∑ T ∈ (U \ b).powerset, ∑ V ∈ (U \ (b ∪ T)).powerset,
              ∑ μ ∈ (eltsLe Y).erase 0,
                ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
                  rcTerm W Z H ξ1 ξ2 b T V μ M1 M2 := by
  set 𝒜 := fsLe (⌈β * Z⌉₊ : ℝ) with h𝒜def
  rw [famSum_majorant_eq hW hZ H hH]
  have hpair : ∀ A1 ∈ 𝒜, ∀ A2 ∈ 𝒜,
      ((W ((absNorm (idl A1) : ℝ) / Z) * W ((absNorm (idl A2) : ℝ) / Z) : ℝ) : ℂ) *
        ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
          ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))) =
      (if A1 = A2 then ((W (nI A1 / Z) ^ 2 : ℝ) : ℂ) *
          ∑ T ∈ A1.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
        ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff pairPsiCls ξ1⁻¹ ξ2 *
            ((((W (nI A1 / Z) * W (nI A2 / Z)) : ℝ) : ℂ) *
              ∑ T ∈ (A1 ∩ A2).powerset,
                tauXi H ((eltsLe Y).erase 0) ξ1 ξ2 (A1 \ A2) (A2 \ A1) T) := by
    intro A1 hA1 A2 hA2
    rw [pair_char_form H hH hR0 hR hY (nI_le_of_mem_fsLe hA1) (nI_le_of_mem_fsLe hA2), mul_add]
    congr 1
    · split_ifs with he
      · subst he; unfold nI; push_cast; ring
      · rw [mul_zero]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ2 _ => ?_
      unfold nI; ring
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => hpair A1 hA1 A2 hA2]
  simp only [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun A1 hA1 => ?_
    rw [Finset.sum_ite_eq]
    rw [ite_eq_left hA1]
  · rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ1 _ => ?_
    rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ2 _ => ?_
    simp_rw [← Finset.mul_sum]
    congr 1
    exact xi_chain W hZ _ ξ1 ξ2 U 𝒜 (fun A hA => (subset_primesLe hA).trans hU)
      (fun A _ hA => W_nI_eq_zero hW hZ hA)

end Eis

end

#print axioms Eis.sum_supersets
#print axioms Eis.sum_pair_inter_eq
#print axioms Eis.sum_powerset_pair_split
#print axioms Eis.sum_powerset_sub_split
#print axioms Eis.sum_disjoint_mobius
#print axioms Eis.pair_split_facts
#print axioms Eis.sum_pair_T_split
#print axioms Eis.sum_family_eq_powerset
#print axioms Eis.absNorm_crd
#print axioms Eis.mem_eltsLe
#print axioms Eis.absNorm_idl_singleton
#print axioms Eis.one_le_absNorm_Pr
#print axioms Eis.absNorm_idl_mono
#print axioms Eis.mem_primesLe
#print axioms Eis.subset_primesLe
#print axioms Eis.isUnit_cls4
#print axioms Eis.pairPsi_eq_cls
#print axioms Eis.norm_pairPsi
#print axioms Eis.norm_pairPsiCls_le
#print axioms Eis.aXi_idl
#print axioms Eis.pairTerm_expand
#print axioms Eis.span_prod_πP
#print axioms Eis.absNorm_span_prod_πP
#print axioms Eis.nI_union
#print axioms Eis.one_le_nI
#print axioms Eis.nI_pos
#print axioms Eis.nI_empty
#print axioms Eis.chiS_empty
#print axioms Eis.chiS_zero
#print axioms Eis.gamF_empty
#print axioms Eis.aF_empty
#print axioms Eis.pairPsi_empty
#print axioms Eis.pairSum_clean
#print axioms Eis.tsum_mu_eq
#print axioms Eis.prime_πP
#print axioms Eis.πP_dvd_πP
#print axioms Eis.not_dvd_eS
#print axioms Eis.chiS_mul
#print axioms Eis.chiS_pow
#print axioms Eis.chiS_mul_conj_eS
#print axioms Eis.conj_chiS_eS
#print axioms Eis.chiS_eS_pow_six
#print axioms Eis.col_factor
#print axioms Eis.sdiff_eq_empty_both
#print axioms Eis.nI_pair_le
#print axioms Eis.pair_char_form
#print axioms Eis.W_eq_W0f
#print axioms Eis.WW_kap
#print axioms Eis.term_factor
#print axioms Eis.disjoint_of_mem_powerset_sdiff
#print axioms Eis.xi_chain
#print axioms Eis.nI_le_of_mem_fsLe
#print axioms Eis.W_nI_eq_zero
#print axioms Eis.meanSquare_rowcol
