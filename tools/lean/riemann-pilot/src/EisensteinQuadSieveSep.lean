import EisensteinQuadSieveBase

/-! # The quadratic large sieve, part 3: Heath-Brown's Lemmas 2 and 10 (round 346)

S5e of round 312's plan, part 3 (round 343's S5e-3), for a weighted norm in prime-set coordinates.

* **The weighted norm** (`FBound w N Δ`): rows the arguments `m ∈ ℤ[ω]` with weights `w(m)`,
  columns the squarefree moduli `∏_{P∈A} π_P`, given by their sets of primes `A`, of norm at most
  `N`. With the weight `admW M` of the admissible arguments of norm at most `M` it is round 344's
  `QBound N M`, by duality (`qBound_of_fBound`, `fBound_of_qBound`). A sub-family of the columns
  satisfies the norm at the smaller scale (`FBound.sub`).
* **Möbius inversion, factored** (`sum_disjoint_factor`, `sum_inter_eq_factor`): a double sum over
  pairs of columns with `A₁ ∩ A₂ = ∅`, or with `A₁ ∩ A₂ = G`, is an alternating sum of products of
  single sums over the columns containing a set.
* **Heath-Brown's Lemma 2** (`fBound_gcd`; Goldmakher and Louvel's Lemma 5.1): the expanded mean
  square sorted by the greatest common divisor `G` of each pair (`gcdPart`). The parts with
  `N(G) ≤ g₀` are bounded by hypothesis. The others are alternating sums of norms at `N/g₀`
  (`gcdPart_eq`), at most `4^{|A|}` of them for each column (`sum_triple_le`), so they cost
  `C·N^δ`.
* **Heath-Brown's Lemma 10** (`fBound_sep`; Goldmakher and Louvel's Lemma 7.1): for moduli `d`
  with `D < N(d) ≤ 2D`, the sums over coprime pairs with `d ∣ n₁n₂` split as `d = d₁d₂` with
  `d₁ ∣ n₁`, `d₂ ∣ n₂` (`ite_disjoint_cover`, `sepInner_eq`), and Cauchy–Schwarz (`sep_one`,
  `sum3_sqrt_le`) bounds each dyadic class `2^{j−1} < N(d₁) ≤ 2^j` by the norms at `2N/2^j` and
  `N·2^j/D`, with the counts of `count_cover`.
-/

open NumberField Complex Ideal
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- **The weighted norm in prime-set coordinates**: rows the arguments `m ∈ ℤ[ω]` with weights
`w(m)`, columns the squarefree moduli `∏_{P∈A} π_P` of norm at most `N`, given by their sets of
primes `A`: `Σ_m w(m)|Σ_A α(A)(m/A)₂|² ≤ Δ Σ_A |α(A)|²`. -/
def FBound (w : 𝓞 K → ℝ) (N Δ : ℝ) : Prop :=
  ∀ (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ), (∀ A ∈ 𝒩, nI A ≤ N) →
    ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 ≤ Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2

theorem FBound.mono {w : 𝓞 K → ℝ} {N N' Δ Δ' : ℝ} (h : FBound w N' Δ) (hN : N ≤ N')
    (hΔ : Δ ≤ Δ') : FBound w N Δ' := fun 𝒩 α h𝒩 =>
  (h 𝒩 α fun A hA => (h𝒩 A hA).trans hN).trans
    (mul_le_mul_of_nonneg_right hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem norm_q2Sum_le (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ) (m : 𝓞 K) :
    ‖∑ A ∈ 𝒩, α A * q2 A m‖ ≤ ∑ A ∈ 𝒩, ‖α A‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun A _ => by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_q2_le A m))

theorem summable_w_mul {w : 𝓞 K → ℝ} (hw : Summable w) {g : 𝓞 K → ℝ} {B : ℝ}
    (hg : ∀ m, |g m| ≤ B) : Summable fun m => w m * g m := by
  refine Summable.of_norm_bounded (hw.abs.mul_right B) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hg m) (abs_nonneg _)

theorem summable_w_colSum {w : 𝓞 K → ℝ} (hw : Summable w) (𝒩 : Finset (Finset Pr))
    (α : Finset Pr → ℂ) : Summable fun m => w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 := by
  refine summable_w_mul hw (B := (∑ A ∈ 𝒩, ‖α A‖) ^ 2) fun m => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_q2Sum_le 𝒩 α m) 2

theorem nI_sdiff_mul {F A : Finset Pr} (h : F ⊆ A) : nI (A \ F) * nI F = nI A := by
  rw [← nI_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]

theorem q2_sdiff_mul {F A : Finset Pr} (h : F ⊆ A) (m : 𝓞 K) :
    q2 A m = q2 F m * q2 (A \ F) m := by
  rw [← q2_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h]

open Classical in
/-- **A sub-family**: the columns containing `F`, with `F` taken out, are columns of norm at most
`x` when `N(A) ≤ x·N(F)`; and `|ρ_F(m)| ≤ 1`. -/
theorem FBound.sub {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {x Δ : ℝ}
    (h : FBound w x Δ) (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ) (F : Finset Pr)
    (hx : ∀ A ∈ 𝒩, F ⊆ A → nI A ≤ x * nI F) :
    ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩.filter (F ⊆ ·), α A * q2 A m‖ ^ 2 ≤
      Δ * ∑ A ∈ 𝒩.filter (F ⊆ ·), ‖α A‖ ^ 2 := by
  set 𝒩F := 𝒩.filter (F ⊆ ·) with h𝒩F
  have hinj : Set.InjOn (· \ F) (𝒩F : Set (Finset Pr)) := by
    intro A hA B hB hAB
    have hA' : F ⊆ A := (Finset.mem_filter.1 hA).2
    have hB' : F ⊆ B := (Finset.mem_filter.1 hB).2
    simp only at hAB
    rw [← Finset.sdiff_union_of_subset hA', ← Finset.sdiff_union_of_subset hB', hAB]
  set 𝒩' := 𝒩F.image (· \ F) with h𝒩'
  set α' : Finset Pr → ℂ := fun B => α (B ∪ F) with hα'
  have hcols : ∀ B ∈ 𝒩', nI B ≤ x := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
    have hA' := Finset.mem_filter.1 hA
    have h1 := hx A hA'.1 hA'.2
    have h2 := nI_sdiff_mul hA'.2
    have hF := nI_pos F
    nlinarith
  have hX : ∀ m, ∑ A ∈ 𝒩F, α A * q2 A m = q2 F m * ∑ B ∈ 𝒩', α' B * q2 B m := by
    intro m
    rw [Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA => ?_
    have hA' : F ⊆ A := (Finset.mem_filter.1 hA).2
    simp only [hα', Finset.sdiff_union_of_subset hA']
    rw [q2_sdiff_mul hA']; ring
  have hle : ∀ m, w m * ‖∑ A ∈ 𝒩F, α A * q2 A m‖ ^ 2 ≤
      w m * ‖∑ B ∈ 𝒩', α' B * q2 B m‖ ^ 2 := by
    intro m
    refine mul_le_mul_of_nonneg_left ?_ (hw0 m)
    rw [hX, norm_mul]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_left (norm_nonneg _) (norm_q2_le F m)) 2
  have hsum : ∑ B ∈ 𝒩', ‖α' B‖ ^ 2 = ∑ A ∈ 𝒩F, ‖α A‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun A hA => ?_
    have hA' : F ⊆ A := (Finset.mem_filter.1 hA).2
    simp only [hα', Finset.sdiff_union_of_subset hA']
  calc ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩F, α A * q2 A m‖ ^ 2
      ≤ ∑' m : 𝓞 K, w m * ‖∑ B ∈ 𝒩', α' B * q2 B m‖ ^ 2 :=
        (summable_w_colSum hw 𝒩F α).tsum_le_tsum hle (summable_w_colSum hw 𝒩' α')
    _ ≤ Δ * ∑ B ∈ 𝒩', ‖α' B‖ ^ 2 := h 𝒩' α' hcols
    _ = Δ * ∑ A ∈ 𝒩F, ‖α A‖ ^ 2 := by rw [hsum]

/-- **Möbius inversion of disjointness, factored**: for families of subsets of `U`,
`Σ_{A₁,A₂} [A₁ ∩ A₂ = ∅, P(A₁), Q(A₂)] f(A₁)g(A₂)
  = Σ_{E⊆U} (−1)^{|E|} (Σ_{A₁ ⊇ E, P(A₁)} f(A₁))(Σ_{A₂ ⊇ E, Q(A₂)} g(A₂))`. -/
theorem sum_disjoint_factor {α : Type*} [DecidableEq α] (U : Finset α)
    (𝒩 : Finset (Finset α)) (h𝒩 : ∀ A ∈ 𝒩, A ⊆ U) (P Q : Finset α → Prop) [DecidablePred P]
    [DecidablePred Q] (f g : Finset α → ℂ) :
    ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, (if Disjoint A1 A2 ∧ P A1 ∧ Q A2 then f A1 * g A2 else 0) =
      ∑ E ∈ U.powerset, (-1 : ℂ) ^ E.card *
        ((∑ A1 ∈ 𝒩.filter (fun A => E ⊆ A ∧ P A), f A1) *
          (∑ A2 ∈ 𝒩.filter (fun A => E ⊆ A ∧ Q A), g A2)) := by
  have h1 : ∀ A1 ∈ 𝒩, ∀ A2 ∈ 𝒩,
      (if Disjoint A1 A2 ∧ P A1 ∧ Q A2 then f A1 * g A2 else 0) =
      ∑ E ∈ U.powerset, (if (E ⊆ A1 ∧ P A1) ∧ (E ⊆ A2 ∧ Q A2) then
        (-1 : ℂ) ^ E.card * (f A1 * g A2) else 0) := by
    intro A1 hA1 A2 _
    have hsub : (A1 ∩ A2).powerset = U.powerset.filter (fun E => E ⊆ A1 ∧ E ⊆ A2) := by
      ext E
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_inter_iff]
      constructor
      · intro h; exact ⟨h.1.trans (h𝒩 A1 hA1), h⟩
      · intro h; exact h.2
    have hs : ∑ E ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ E.card = if A1 ∩ A2 = ∅ then 1 else 0 := by
      have := Finset.sum_powerset_neg_one_pow_card (x := A1 ∩ A2)
      exact_mod_cast this
    by_cases hPQ : P A1 ∧ Q A2
    · have e : ∀ E ∈ U.powerset, (if (E ⊆ A1 ∧ P A1) ∧ (E ⊆ A2 ∧ Q A2) then
          (-1 : ℂ) ^ E.card * (f A1 * g A2) else 0) =
          (if E ⊆ A1 ∧ E ⊆ A2 then (-1 : ℂ) ^ E.card else 0) * (f A1 * g A2) := by
        intro E _
        by_cases hE : E ⊆ A1 ∧ E ⊆ A2
        · rw [ite_eq_left ⟨⟨hE.1, hPQ.1⟩, ⟨hE.2, hPQ.2⟩⟩, ite_eq_left hE]
        · rw [ite_eq_right (fun h => hE ⟨h.1.1, h.2.1⟩), ite_eq_right hE, zero_mul]
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ← Finset.sum_filter, ← hsub, hs]
      by_cases hd : Disjoint A1 A2
      · rw [ite_eq_left ⟨hd, hPQ⟩, ite_eq_left (Finset.disjoint_iff_inter_eq_empty.1 hd),
          one_mul]
      · rw [ite_eq_right (fun h => hd h.1),
          ite_eq_right (fun h' => hd (Finset.disjoint_iff_inter_eq_empty.2 h')), zero_mul]
    · rw [ite_eq_right (fun h => hPQ h.2)]
      exact (Finset.sum_eq_zero fun E _ => ite_eq_right fun h => hPQ ⟨h.1.2, h.2.2⟩).symm
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => h1 A1 hA1 A2 hA2]
  rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A1 _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]
  by_cases h1 : E ⊆ A1 ∧ P A1
  · rw [ite_eq_left h1]
    refine Finset.sum_congr rfl fun A2 _ => ?_
    by_cases h2 : E ⊆ A2 ∧ Q A2
    · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h2]
    · rw [ite_eq_right (fun h => h2 h.2), ite_eq_right h2]
  · rw [ite_eq_right h1]
    exact Finset.sum_eq_zero fun A2 _ => ite_eq_right fun h => h1 h.1

/-- The weighted pair sum `S_w(A₁, A₂) = Σ_m w(m)ρ_{A₁}(m)ρ_{A₂}(m)`. -/
def pW (w : 𝓞 K → ℝ) (A1 A2 : Finset Pr) : ℂ :=
  ∑' m : 𝓞 K, (w m : ℂ) * (q2 A1 m * q2 A2 m)

open Classical in
/-- The part of the expanded mean square from the pairs of columns with greatest common divisor
`G`. -/
def gcdPart (w : 𝓞 K → ℝ) (G : Finset Pr) (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ) : ℂ :=
  ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0

/-- **Möbius inversion of a fixed intersection, factored**: for families of subsets of `U`,
`Σ_{A₁,A₂} [A₁ ∩ A₂ = G] f(A₁)g(A₂) = Σ_{E⊆U∖G} (−1)^{|E|} (Σ_{A₁ ⊇ G∪E} f)(Σ_{A₂ ⊇ G∪E} g)`. -/
theorem sum_inter_eq_factor {α : Type*} [DecidableEq α] (U : Finset α)
    (𝒩 : Finset (Finset α)) (h𝒩 : ∀ A ∈ 𝒩, A ⊆ U) (G : Finset α) (f g : Finset α → ℂ) :
    ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, (if A1 ∩ A2 = G then f A1 * g A2 else 0) =
      ∑ E ∈ (U \ G).powerset, (-1 : ℂ) ^ E.card *
        ((∑ A1 ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), f A1) *
          (∑ A2 ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), g A2)) := by
  have h1 : ∀ A1 ∈ 𝒩, ∀ A2 ∈ 𝒩, (if A1 ∩ A2 = G then f A1 * g A2 else 0) =
      ∑ E ∈ (U \ G).powerset, (if G ∪ E ⊆ A1 ∧ G ∪ E ⊆ A2 then
        (-1 : ℂ) ^ E.card * (f A1 * g A2) else 0) := by
    intro A1 hA1 A2 _
    by_cases hG : G ⊆ A1 ∩ A2
    · have hsub : ((A1 ∩ A2) \ G).powerset =
          (U \ G).powerset.filter (fun E => G ∪ E ⊆ A1 ∧ G ∪ E ⊆ A2) := by
        ext E
        simp only [Finset.mem_powerset, Finset.mem_filter, Finset.union_subset_iff]
        constructor
        · intro h
          have hE : E ⊆ A1 ∩ A2 := h.trans Finset.sdiff_subset
          refine ⟨fun x hx => ?_, ⟨(Finset.subset_inter_iff.1 hG).1,
            (Finset.subset_inter_iff.1 hE).1⟩, ⟨(Finset.subset_inter_iff.1 hG).2,
            (Finset.subset_inter_iff.1 hE).2⟩⟩
          have hx' := h hx
          rw [Finset.mem_sdiff] at hx' ⊢
          exact ⟨h𝒩 A1 hA1 (Finset.mem_inter.1 hx'.1).1, hx'.2⟩
        · rintro ⟨hEU, ⟨_, hE1⟩, ⟨_, hE2⟩⟩ x hx
          rw [Finset.mem_sdiff]
          exact ⟨Finset.mem_inter.2 ⟨hE1 hx, hE2 hx⟩, (Finset.mem_sdiff.1 (hEU hx)).2⟩
      have hs : ∑ E ∈ ((A1 ∩ A2) \ G).powerset, (-1 : ℂ) ^ E.card =
          if (A1 ∩ A2) \ G = ∅ then 1 else 0 := by
        have := Finset.sum_powerset_neg_one_pow_card (x := (A1 ∩ A2) \ G)
        exact_mod_cast this
      have e : ∀ E ∈ (U \ G).powerset, (if G ∪ E ⊆ A1 ∧ G ∪ E ⊆ A2 then
          (-1 : ℂ) ^ E.card * (f A1 * g A2) else 0) =
          (if G ∪ E ⊆ A1 ∧ G ∪ E ⊆ A2 then (-1 : ℂ) ^ E.card else 0) * (f A1 * g A2) := by
        intro E _
        split_ifs <;> ring
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ← Finset.sum_filter, ← hsub, hs]
      have hiff : A1 ∩ A2 = G ↔ (A1 ∩ A2) \ G = ∅ := by
        rw [Finset.sdiff_eq_empty_iff_subset]
        exact ⟨fun h => h.le, fun h => le_antisymm h hG⟩
      by_cases h : A1 ∩ A2 = G
      · rw [ite_eq_left h, ite_eq_left (hiff.1 h), one_mul]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.2 h')), zero_mul]
    · have hne : A1 ∩ A2 ≠ G := fun h => hG h.ge
      rw [ite_eq_right hne]
      refine (Finset.sum_eq_zero fun E _ => ite_eq_right fun h => hG ?_).symm
      exact Finset.subset_inter (Finset.union_subset_iff.1 h.1).1
        (Finset.union_subset_iff.1 h.2).1
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => h1 A1 hA1 A2 hA2]
  rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A1 _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]
  by_cases h1 : G ∪ E ⊆ A1
  · rw [ite_eq_left h1]
    refine Finset.sum_congr rfl fun A2 _ => ?_
    by_cases h2 : G ∪ E ⊆ A2
    · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h2]
    · rw [ite_eq_right (fun h => h2 h.2), ite_eq_right h2]
  · rw [ite_eq_right h1]
    exact Finset.sum_eq_zero fun A2 _ => ite_eq_right fun h => h1 h.1

theorem summable_w_pair {w : 𝓞 K → ℝ} (hw : Summable w) (A1 A2 : Finset Pr) :
    Summable fun m : 𝓞 K => (w m : ℂ) * (q2 A1 m * q2 A2 m) := by
  refine Summable.of_norm_bounded (hw.abs.mul_right 1) fun m => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖q2 A1 m‖ * ‖q2 A2 m‖ ≤ 1 * 1 :=
        mul_le_mul (norm_q2_le A1 m) (norm_q2_le A2 m) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem mul_conj_q2Sum (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ) (m : 𝓞 K) :
    (∑ A ∈ 𝒩, α A * q2 A m) * conj (∑ A ∈ 𝒩, α A * q2 A m) =
      ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, α A1 * conj (α A2) * (q2 A1 m * q2 A2 m) := by
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun A1 _ => Finset.sum_congr rfl fun A2 _ => ?_
  rw [map_mul, conj_q2]; ring

/-- **The expansion**: `Σ_m w(m)|Σ_A α(A)ρ_A(m)|² = Σ_{A₁,A₂} α(A₁)ᾱ(A₂)S_w(A₁, A₂)`. -/
theorem tsum_w_colSum_eq {w : 𝓞 K → ℝ} (hw : Summable w) (𝒩 : Finset (Finset Pr))
    (α : Finset Pr → ℂ) :
    ((∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 : ℝ) : ℂ) =
      ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, α A1 * conj (α A2) * pW w A1 A2 := by
  rw [Complex.ofReal_tsum]
  have hpt : ∀ m : 𝓞 K, ((w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 : ℝ) : ℂ) =
      ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, α A1 * conj (α A2) * ((w m : ℂ) * (q2 A1 m * q2 A2 m)) := by
    intro m
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', mul_conj_q2Sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun A1 _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun A2 _ => by ring
  rw [tsum_congr hpt]
  have hs : ∀ A1 A2 : Finset Pr, Summable fun m : 𝓞 K =>
      α A1 * conj (α A2) * ((w m : ℂ) * (q2 A1 m * q2 A2 m)) := fun A1 A2 =>
    (summable_w_pair hw A1 A2).mul_left _
  rw [Summable.tsum_finsetSum fun A1 _ => summable_sum fun A2 _ => hs A1 A2]
  refine Finset.sum_congr rfl fun A1 _ => ?_
  rw [Summable.tsum_finsetSum fun A2 _ => hs A1 A2]
  refine Finset.sum_congr rfl fun A2 _ => ?_
  rw [tsum_mul_left]; rfl

open Classical in
/-- **A part with large greatest common divisor**: `gcdPart w G = Σ_{E⊆U∖G} (−1)^{|E|}
Σ_m w(m)|Σ_{A ⊇ G∪E} α(A)ρ_A(m)|²`. -/
theorem gcdPart_eq {w : 𝓞 K → ℝ} (hw : Summable w) (U : Finset Pr) (𝒩 : Finset (Finset Pr))
    (h𝒩 : ∀ A ∈ 𝒩, A ⊆ U) (G : Finset Pr) (α : Finset Pr → ℂ) :
    gcdPart w G 𝒩 α = ∑ E ∈ (U \ G).powerset, (-1 : ℂ) ^ E.card *
      ((∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), α A * q2 A m‖ ^ 2 : ℝ) : ℂ) := by
  set X : Finset Pr → 𝓞 K → ℂ := fun E m =>
    ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), α A * q2 A m with hX
  have hpt : ∀ A1 ∈ 𝒩, ∀ A2 ∈ 𝒩, (if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0) =
      ∑' m : 𝓞 K, (w m : ℂ) * (if A1 ∩ A2 = G then
        (α A1 * q2 A1 m) * conj (α A2 * q2 A2 m) else 0) := by
    intro A1 _ A2 _
    split_ifs with h
    · rw [pW, ← tsum_mul_left]
      refine tsum_congr fun m => ?_
      rw [map_mul, conj_q2]; ring
    · simp
  have hs : ∀ A1 A2 : Finset Pr, Summable fun m : 𝓞 K => (w m : ℂ) * (if A1 ∩ A2 = G then
      (α A1 * q2 A1 m) * conj (α A2 * q2 A2 m) else 0) := by
    intro A1 A2
    split_ifs
    · refine ((summable_w_pair hw A1 A2).mul_left (α A1 * conj (α A2))).congr fun m => ?_
      rw [map_mul, conj_q2]; ring
    · simp only [mul_zero]; exact summable_zero
  have hfac : ∀ m : 𝓞 K, ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, (w m : ℂ) * (if A1 ∩ A2 = G then
      (α A1 * q2 A1 m) * conj (α A2 * q2 A2 m) else 0) =
      ∑ E ∈ (U \ G).powerset, (-1 : ℂ) ^ E.card * ((w m * ‖X E m‖ ^ 2 : ℝ) : ℂ) := by
    intro m
    have h1 := sum_inter_eq_factor U 𝒩 h𝒩 G (fun A => α A * q2 A m)
      (fun A => conj (α A * q2 A m))
    calc ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, (w m : ℂ) * (if A1 ∩ A2 = G then
          (α A1 * q2 A1 m) * conj (α A2 * q2 A2 m) else 0)
        = (w m : ℂ) * ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, (if A1 ∩ A2 = G then
          (α A1 * q2 A1 m) * conj (α A2 * q2 A2 m) else 0) := by
          simp_rw [Finset.mul_sum]
      _ = (w m : ℂ) * ∑ E ∈ (U \ G).powerset, (-1 : ℂ) ^ E.card * (X E m * conj (X E m)) := by
          rw [h1, hX]; simp only [map_sum]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun E _ => ?_
          rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']; ring
  have hsE : ∀ E : Finset Pr, Summable fun m : 𝓞 K =>
      (-1 : ℂ) ^ E.card * ((w m * ‖X E m‖ ^ 2 : ℝ) : ℂ) := fun E =>
    (Complex.ofRealCLM.summable (summable_w_colSum hw _ α)).mul_left _
  calc gcdPart w G 𝒩 α
      = ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, ∑' m : 𝓞 K, (w m : ℂ) * (if A1 ∩ A2 = G then
          (α A1 * q2 A1 m) * conj (α A2 * q2 A2 m) else 0) :=
        Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => hpt A1 hA1 A2 hA2
    _ = ∑' m : 𝓞 K, ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, (w m : ℂ) * (if A1 ∩ A2 = G then
          (α A1 * q2 A1 m) * conj (α A2 * q2 A2 m) else 0) := by
        rw [Summable.tsum_finsetSum fun A1 _ => summable_sum fun A2 _ => hs A1 A2]
        refine Finset.sum_congr rfl fun A1 _ => ?_
        rw [Summable.tsum_finsetSum fun A2 _ => hs A1 A2]
    _ = ∑' m : 𝓞 K, ∑ E ∈ (U \ G).powerset, (-1 : ℂ) ^ E.card *
          ((w m * ‖X E m‖ ^ 2 : ℝ) : ℂ) := tsum_congr hfac
    _ = ∑ E ∈ (U \ G).powerset, (-1 : ℂ) ^ E.card *
          ((∑' m : 𝓞 K, w m * ‖X E m‖ ^ 2 : ℝ) : ℂ) := by
        rw [Summable.tsum_finsetSum fun E _ => hsE E]
        refine Finset.sum_congr rfl fun E _ => ?_
        rw [tsum_mul_left, Complex.ofReal_tsum]

/-- The pairs `(G, E)` with `G ∪ E ⊆ A` number at most `4^{|A|}`. -/
theorem sum_pair_subset_le {α : Type*} [DecidableEq α] (U : Finset α) (A : Finset α) :
    ∑ G ∈ U.powerset, ∑ E ∈ U.powerset, (if G ∪ E ⊆ A then (1 : ℝ) else 0) ≤ 4 ^ A.card := by
  have e : ∀ G ∈ U.powerset, ∑ E ∈ U.powerset, (if G ∪ E ⊆ A then (1 : ℝ) else 0) =
      (if G ⊆ A then 1 else 0) * ∑ E ∈ U.powerset, (if E ⊆ A then (1 : ℝ) else 0) := by
    intro G _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    by_cases hG : G ⊆ A <;> by_cases hE : E ⊆ A <;>
      simp [hG, hE, Finset.union_subset_iff]
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
  have hc : ∑ G ∈ U.powerset, (if G ⊆ A then (1 : ℝ) else 0) ≤ 2 ^ A.card := by
    rw [Finset.sum_boole]
    have : (U.powerset.filter (· ⊆ A)).card ≤ A.powerset.card :=
      Finset.card_le_card fun G hG => Finset.mem_powerset.2 (Finset.mem_filter.1 hG).2
    rw [Finset.card_powerset] at this
    exact_mod_cast this
  have h0 : 0 ≤ ∑ G ∈ U.powerset, (if G ⊆ A then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  calc (∑ G ∈ U.powerset, (if G ⊆ A then (1 : ℝ) else 0)) *
        ∑ E ∈ U.powerset, (if E ⊆ A then (1 : ℝ) else 0) ≤ 2 ^ A.card * 2 ^ A.card :=
        mul_le_mul hc hc h0 (by positivity)
    _ = 4 ^ A.card := by rw [← mul_pow]; norm_num

/-- **The divisor count**: `Σ_{G}Σ_{E} Σ_{A ⊇ G∪E} h(A) ≤ Σ_A 4^{|A|}h(A)` for `h ≥ 0`. -/
theorem sum_triple_le {α : Type*} [DecidableEq α] (U : Finset α) (𝒩 : Finset (Finset α))
    (S1 : Finset (Finset α)) (hS1 : S1 ⊆ U.powerset) (S2 : Finset α → Finset (Finset α))
    (hS2 : ∀ G, S2 G ⊆ U.powerset) (h : Finset α → ℝ) (hh : ∀ A, 0 ≤ h A) :
    ∑ G ∈ S1, ∑ E ∈ S2 G, ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), h A ≤
      ∑ A ∈ 𝒩, 4 ^ A.card * h A := by
  have hnn : ∀ G E, 0 ≤ ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), h A := fun G E =>
    Finset.sum_nonneg fun A _ => hh A
  calc ∑ G ∈ S1, ∑ E ∈ S2 G, ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), h A
      ≤ ∑ G ∈ S1, ∑ E ∈ U.powerset, ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), h A :=
        Finset.sum_le_sum fun G _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (hS2 G) fun E _ _ => hnn G E
    _ ≤ ∑ G ∈ U.powerset, ∑ E ∈ U.powerset, ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), h A :=
        Finset.sum_le_sum_of_subset_of_nonneg hS1 fun G _ _ =>
          Finset.sum_nonneg fun E _ => hnn G E
    _ = ∑ G ∈ U.powerset, ∑ E ∈ U.powerset, ∑ A ∈ 𝒩, (if G ∪ E ⊆ A then h A else 0) := by
        simp_rw [Finset.sum_filter]
    _ = ∑ G ∈ U.powerset, ∑ A ∈ 𝒩, ∑ E ∈ U.powerset, (if G ∪ E ⊆ A then h A else 0) :=
        Finset.sum_congr rfl fun G _ => Finset.sum_comm
    _ = ∑ A ∈ 𝒩, ∑ G ∈ U.powerset, ∑ E ∈ U.powerset, (if G ∪ E ⊆ A then h A else 0) :=
        Finset.sum_comm
    _ = ∑ A ∈ 𝒩, h A * ∑ G ∈ U.powerset, ∑ E ∈ U.powerset,
          (if G ∪ E ⊆ A then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun E _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ A ∈ 𝒩, h A * 4 ^ A.card :=
        Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_left (sum_pair_subset_le U A) (hh A)
    _ = ∑ A ∈ 𝒩, 4 ^ A.card * h A := Finset.sum_congr rfl fun A _ => mul_comm _ _

theorem nI_mono {A B : Finset Pr} (h : A ⊆ B) : nI A ≤ nI B := by
  unfold nI; exact_mod_cast absNorm_idl_mono h

open Classical in
/-- **Heath-Brown's Lemma 2** (Goldmakher and Louvel's Lemma 5.1), for any nonnegative summable
weight on the arguments: the pairs of columns are sorted by their greatest common divisor `G`.
Those with `N(G) ≤ g₀` are bounded by hypothesis; for the others the coprimality of the cofactors
is detected by Möbius inversion, each piece is the norm at `N/g₀`, and the pieces number at most
`4^{ω}`. -/
theorem fBound_gcd {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N g0 Δ : ℝ) (F3 : Finset Pr → ℝ), 1 ≤ N → 0 < g0 → 0 ≤ Δ →
      (∀ G, 0 ≤ F3 G) → FBound w (N / g0) Δ →
      (∀ G ∈ fsLe g0, ∀ (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ), (∀ A ∈ 𝒩, nI A ≤ N) →
        (gcdPart w G 𝒩 α).re ≤ F3 G * ∑ A ∈ 𝒩, ‖α A‖ ^ 2) →
      FBound w N (C * N ^ δ * Δ + ∑ G ∈ fsLe g0, F3 G) := by
  obtain ⟨C4, hC4pos, hC4⟩ := four_pow_card_le hδ
  refine ⟨C4, hC4pos.le, fun N g0 Δ F3 hN hg0 hΔ hF3 hF h3 𝒩 α h𝒩 => ?_⟩
  set U : Finset Pr := 𝒩.sup id with hU
  have h𝒩U : ∀ A ∈ 𝒩, A ⊆ U := fun A hA => Finset.le_sup (f := id) hA
  set S2 : ℝ := ∑ A ∈ 𝒩, ‖α A‖ ^ 2 with hS2
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the expansion, sorted by the greatest common divisor
  have hexp : ((∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 : ℝ) : ℂ) =
      ∑ G ∈ U.powerset, gcdPart w G 𝒩 α := by
    rw [tsum_w_colSum_eq hw]
    unfold gcdPart
    symm
    calc ∑ G ∈ U.powerset, ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
          (if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0)
        = ∑ A1 ∈ 𝒩, ∑ G ∈ U.powerset, ∑ A2 ∈ 𝒩,
          (if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0) := Finset.sum_comm
      _ = ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, ∑ G ∈ U.powerset,
          (if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0) :=
          Finset.sum_congr rfl fun A1 _ => Finset.sum_comm
      _ = ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, α A1 * conj (α A2) * pW w A1 A2 := by
          refine Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 _ => ?_
          have hmem : A1 ∩ A2 ∈ U.powerset :=
            Finset.mem_powerset.2 (Finset.inter_subset_left.trans (h𝒩U A1 hA1))
          rw [Finset.sum_ite_eq, ite_eq_left hmem]
  have hre : (∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2) =
      ∑ G ∈ U.powerset, (gcdPart w G 𝒩 α).re := by
    have := congrArg Complex.re hexp
    rw [Complex.ofReal_re, Complex.re_sum] at this
    exact this
  rw [hre, ← Finset.sum_filter_add_sum_filter_not U.powerset (· ∈ fsLe g0)]
  -- the small greatest common divisors
  have hsmall : ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), (gcdPart w G 𝒩 α).re ≤
      (∑ G ∈ fsLe g0, F3 G) * S2 := by
    calc ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), (gcdPart w G 𝒩 α).re
        ≤ ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), F3 G * S2 :=
          Finset.sum_le_sum fun G hG => h3 G (Finset.mem_filter.1 hG).2 𝒩 α h𝒩
      _ ≤ ∑ G ∈ fsLe g0, F3 G * S2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun G hG => (Finset.mem_filter.1 hG).2)
            fun G _ _ => mul_nonneg (hF3 G) hS20
      _ = (∑ G ∈ fsLe g0, F3 G) * S2 := by rw [Finset.sum_mul]
  -- the large greatest common divisors
  have hpiece : ∀ G ∈ U.powerset.filter (· ∉ fsLe g0), ∀ E : Finset Pr,
      ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), α A * q2 A m‖ ^ 2 ≤
        Δ * ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 := by
    intro G hG E
    have hGl : g0 < nI G := lt_nI_of_not_mem_fsLe (Finset.mem_filter.1 hG).2
    refine hF.sub hw0 hw 𝒩 α (G ∪ E) fun A hA _ => ?_
    have h1 : g0 ≤ nI (G ∪ E) := hGl.le.trans (nI_mono Finset.subset_union_left)
    have h2 := h𝒩 A hA
    rw [div_mul_eq_mul_div, le_div_iff₀ hg0]
    nlinarith
  have hlarge : ∀ G ∈ U.powerset.filter (· ∉ fsLe g0), (gcdPart w G 𝒩 α).re ≤
      ∑ E ∈ (U \ G).powerset, Δ * ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 := by
    intro G hG
    refine (Complex.re_le_norm _).trans ?_
    rw [gcdPart_eq hw U 𝒩 h𝒩U G α]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun E _ => ?_)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun m => mul_nonneg (hw0 m) (sq_nonneg _))]
    exact hpiece G hG E
  have hcount : ∑ G ∈ U.powerset.filter (· ∉ fsLe g0), ∑ E ∈ (U \ G).powerset,
      ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 ≤ C4 * N ^ δ * S2 := by
    refine (sum_triple_le U 𝒩 _ (Finset.filter_subset _ _) (fun G => (U \ G).powerset)
      (fun G => Finset.powerset_mono.2 Finset.sdiff_subset) (fun A => ‖α A‖ ^ 2)
      fun A => sq_nonneg _).trans ?_
    rw [hS2, Finset.mul_sum]
    refine Finset.sum_le_sum fun A hA => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc (4 : ℝ) ^ A.card ≤ C4 * nI A ^ δ := hC4 A
      _ ≤ C4 * N ^ δ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (nI_pos A).le (h𝒩 A hA) hδ.le) hC4pos.le
  calc ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), (gcdPart w G 𝒩 α).re +
        ∑ G ∈ U.powerset.filter (· ∉ fsLe g0), (gcdPart w G 𝒩 α).re
      ≤ (∑ G ∈ fsLe g0, F3 G) * S2 + ∑ G ∈ U.powerset.filter (· ∉ fsLe g0),
          ∑ E ∈ (U \ G).powerset, Δ * ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 :=
        add_le_add hsmall (Finset.sum_le_sum hlarge)
    _ = (∑ G ∈ fsLe g0, F3 G) * S2 + Δ * ∑ G ∈ U.powerset.filter (· ∉ fsLe g0),
          ∑ E ∈ (U \ G).powerset, ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ ≤ (∑ G ∈ fsLe g0, F3 G) * S2 + Δ * (C4 * N ^ δ * S2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hΔ)
    _ = (C4 * N ^ δ * Δ + ∑ G ∈ fsLe g0, F3 G) * S2 := by ring

open Classical in
/-- The column sum over the columns containing `F`. -/
def colX (𝒩 : Finset (Finset Pr)) (γ : Finset Pr → ℂ) (F : Finset Pr) (m : 𝓞 K) : ℂ :=
  ∑ A ∈ 𝒩.filter (fun A => F ⊆ A), γ A * q2 A m

/-- **The splitting of `d ∣ n₁n₂`**: for disjoint `A₁, A₂`, `Ad ⊆ A₁ ∪ A₂` holds for exactly one
`D₁ ⊆ Ad` with `D₁ ⊆ A₁` and `Ad ∖ D₁ ⊆ A₂`, namely `Ad ∩ A₁`. -/
theorem ite_disjoint_cover {α : Type*} [DecidableEq α] (Ad A1 A2 : Finset α) (x : ℂ) :
    (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then x else 0) =
      ∑ D1 ∈ Ad.powerset, (if Disjoint A1 A2 ∧ D1 ⊆ A1 ∧ Ad \ D1 ⊆ A2 then x else 0) := by
  have key : ∀ D1 ⊆ Ad, Disjoint A1 A2 → D1 ⊆ A1 → Ad \ D1 ⊆ A2 → D1 = Ad ∩ A1 := by
    intro D1 hD1 hd h1 h2
    ext y
    simp only [Finset.mem_inter]
    constructor
    · intro hy; exact ⟨hD1 hy, h1 hy⟩
    · rintro ⟨hyA, hy1⟩
      by_contra hy
      have hy2 : y ∈ A2 := h2 (Finset.mem_sdiff.2 ⟨hyA, hy⟩)
      exact Finset.disjoint_left.1 hd hy1 hy2
  by_cases h : Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2
  · have hsd : Ad \ (Ad ∩ A1) ⊆ A2 := by
      intro y hy
      rw [Finset.mem_sdiff, Finset.mem_inter] at hy
      rcases Finset.mem_union.1 (h.2 hy.1) with h1 | h2
      · exact absurd ⟨hy.1, h1⟩ hy.2
      · exact h2
    rw [ite_eq_left h, Finset.sum_eq_single (Ad ∩ A1)]
    · rw [ite_eq_left ⟨h.1, Finset.inter_subset_right, hsd⟩]
    · intro D1 hD1 hne
      exact ite_eq_right fun h' =>
        hne (key D1 (Finset.mem_powerset.1 hD1) h'.1 h'.2.1 h'.2.2)
    · intro hn
      exact absurd (Finset.mem_powerset.2 Finset.inter_subset_left) hn
  · rw [ite_eq_right h]
    refine (Finset.sum_eq_zero fun D1 hD1 => ite_eq_right fun h' => h ⟨h'.1, ?_⟩).symm
    intro y hy
    by_cases hy1 : y ∈ D1
    · exact Finset.mem_union_left _ (h'.2.1 hy1)
    · exact Finset.mem_union_right _ (h'.2.2 (Finset.mem_sdiff.2 ⟨hy, hy1⟩))

open Classical in
/-- **The inner sum, separated**: with `U` containing every column,
`Σ_{A₁,A₂ disjoint, Ad ⊆ A₁∪A₂} α(A₁)β(A₂)ρ_{A₁}ρ_{A₂}(m)
  = Σ_{D₁⊆Ad} Σ_{E⊆U} (−1)^{|E|} X_α(D₁ ∪ E)(m)·X_β((Ad ∖ D₁) ∪ E)(m)`. -/
theorem sepInner_eq (U : Finset Pr) (𝒩 : Finset (Finset Pr)) (h𝒩 : ∀ A ∈ 𝒩, A ⊆ U)
    (α β : Finset Pr → ℂ) (Ad : Finset Pr) (m : 𝓞 K) :
    ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
      (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0) =
      ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset, (-1 : ℂ) ^ E.card *
        (colX 𝒩 α (D1 ∪ E) m * colX 𝒩 β ((Ad \ D1) ∪ E) m) := by
  have h1 : ∀ A1 ∈ 𝒩, ∀ A2 ∈ 𝒩,
      (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0) =
      ∑ D1 ∈ Ad.powerset, (if Disjoint A1 A2 ∧ D1 ⊆ A1 ∧ Ad \ D1 ⊆ A2 then
        (α A1 * q2 A1 m) * (β A2 * q2 A2 m) else 0) := by
    intro A1 _ A2 _
    rw [ite_disjoint_cover]
    refine Finset.sum_congr rfl fun D1 _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => h1 A1 hA1 A2 hA2]
  rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun D1 _ => ?_
  rw [sum_disjoint_factor U 𝒩 h𝒩 (fun A => D1 ⊆ A) (fun A => Ad \ D1 ⊆ A)
    (fun A => α A * q2 A m) (fun A => β A * q2 A m)]
  refine Finset.sum_congr rfl fun E _ => ?_
  have f1 : 𝒩.filter (fun A => E ⊆ A ∧ D1 ⊆ A) = 𝒩.filter (fun A => D1 ∪ E ⊆ A) :=
    Finset.filter_congr fun A _ => by rw [Finset.union_subset_iff, and_comm]
  have f2 : 𝒩.filter (fun A => E ⊆ A ∧ Ad \ D1 ⊆ A) = 𝒩.filter (fun A => (Ad \ D1) ∪ E ⊆ A) :=
    Finset.filter_congr fun A _ => by rw [Finset.union_subset_iff, and_comm]
  rw [f1, f2]; rfl

/-- **Cauchy–Schwarz for nonnegative series**, from the finite sums. -/
theorem tsum_le_sqrt_mul_sqrt {ι : Type*} {a b c : ι → ℝ} (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i) (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ Real.sqrt (a i) * Real.sqrt (b i)) :
    ∑' i, c i ≤ Real.sqrt (∑' i, a i) * Real.sqrt (∑' i, b i) := by
  refine Real.tsum_le_of_sum_le hc0 fun s => ?_
  calc ∑ i ∈ s, c i ≤ ∑ i ∈ s, Real.sqrt (a i) * Real.sqrt (b i) := Finset.sum_le_sum fun i _ => hc i
    _ ≤ Real.sqrt (∑ i ∈ s, a i) * Real.sqrt (∑ i ∈ s, b i) := Real.sum_sqrt_mul_sqrt_le s ha0 hb0
    _ ≤ Real.sqrt (∑' i, a i) * Real.sqrt (∑' i, b i) :=
        mul_le_mul (Real.sqrt_le_sqrt (ha.sum_le_tsum s fun i _ => ha0 i))
          (Real.sqrt_le_sqrt (hb.sum_le_tsum s fun i _ => hb0 i)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)

/-- `2^{⌈log₂ n⌉}` lies in `[n, 2n)` for `n ≥ 1`. -/
theorem pow_clog_lt_two_mul {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n < 2 * n := by
  rcases Nat.lt_or_eq_of_le hn with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
    have h2 : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) h
    calc 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
          rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel h2]
      _ < 2 * n := by omega
  · subst h; simp [Nat.clog_one_right]

/-- The squarefree ideals of norm at most `x ≥ 0` number at most `(2κ+5)x`. -/
theorem card_fsLe_le' {x : ℝ} (hx : 0 ≤ x) : ((fsLe x).card : ℝ) ≤ (2 * kappa + 5) * x := by
  by_cases h1 : 1 ≤ x
  · exact card_fsLe_le h1
  · have : fsLe x = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      have h := mem_fsLe.1 hA
      have hf : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.2 (lt_of_not_ge h1)
      rw [hf, Nat.le_zero, absNorm_eq_zero_iff] at h
      exact idl_ne_bot A h
    rw [this, Finset.card_empty, Nat.cast_zero]
    have := kappa_pos
    positivity

/-- The subsets `E ⊆ U` with `D ∪ E ⊆ A` number at most `[D ⊆ A]·2^{|A|}`. -/
theorem sum_union_subset_le {α : Type*} [DecidableEq α] (U D A : Finset α) :
    ∑ E ∈ U.powerset, (if D ∪ E ⊆ A then (1 : ℝ) else 0) ≤
      if D ⊆ A then (2 : ℝ) ^ A.card else 0 := by
  split_ifs with hD
  · rw [Finset.sum_boole]
    have : (U.powerset.filter (fun E => D ∪ E ⊆ A)).card ≤ A.powerset.card :=
      Finset.card_le_card fun E hE =>
        Finset.mem_powerset.2 (Finset.union_subset_iff.1 (Finset.mem_filter.1 hE).2).2
    rw [Finset.card_powerset] at this
    exact_mod_cast this
  · exact (Finset.sum_eq_zero fun E _ =>
      ite_eq_right fun h => hD (Finset.union_subset_iff.1 h).1).le

open Classical in
/-- **The count of the splittings `d = d₁d₂` meeting a column**: when `N(Ad ∖ D) ≤ X` on the
selected pairs, the triples `(Ad, D, E)` with `D ∪ E ⊆ A` number at most `4^{|A|}·(2κ+5)X`. -/
theorem count_cover (𝒟 : Finset (Finset Pr)) (U A : Finset Pr)
    (P : Finset Pr → Finset Pr → Prop) [∀ Ad D, Decidable (P Ad D)] {X : ℝ} (hX : 0 ≤ X)
    (hP : ∀ Ad ∈ 𝒟, ∀ D ⊆ Ad, P Ad D → nI (Ad \ D) ≤ X) :
    ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset, (if P Ad D then
      ∑ E ∈ U.powerset, (if D ∪ E ⊆ A then (1 : ℝ) else 0) else 0) ≤
      4 ^ A.card * ((2 * kappa + 5) * X) := by
  have hk := kappa_pos
  have step1 : ∀ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset, (if P Ad D then
      ∑ E ∈ U.powerset, (if D ∪ E ⊆ A then (1 : ℝ) else 0) else 0) ≤
      ∑ D ∈ A.powerset, (if D ⊆ Ad ∧ P Ad D then (2 : ℝ) ^ A.card else 0) := by
    intro Ad _
    calc ∑ D ∈ Ad.powerset, (if P Ad D then
          ∑ E ∈ U.powerset, (if D ∪ E ⊆ A then (1 : ℝ) else 0) else 0)
        ≤ ∑ D ∈ Ad.powerset, (if P Ad D ∧ D ⊆ A then (2 : ℝ) ^ A.card else 0) := by
          refine Finset.sum_le_sum fun D _ => ?_
          by_cases hPD : P Ad D
          · rw [ite_eq_left hPD]
            refine (sum_union_subset_le U D A).trans ?_
            by_cases hDA : D ⊆ A
            · rw [ite_eq_left hDA, ite_eq_left ⟨hPD, hDA⟩]
            · rw [ite_eq_right hDA, ite_eq_right (fun h => hDA h.2)]
          · rw [ite_eq_right hPD, ite_eq_right (fun h => hPD h.1)]
      _ = ∑ D ∈ A.powerset, (if D ⊆ Ad ∧ P Ad D then (2 : ℝ) ^ A.card else 0) := by
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          congr 1
          ext D
          simp only [Finset.mem_filter, Finset.mem_powerset]
          tauto
  have step2 : ∀ D ∈ A.powerset, ∑ Ad ∈ 𝒟, (if D ⊆ Ad ∧ P Ad D then (2 : ℝ) ^ A.card else 0) ≤
      (2 : ℝ) ^ A.card * ((2 * kappa + 5) * X) := by
    intro D _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (card_fsLe_le' hX)
    have hinj : Set.InjOn (· \ D) (𝒟.filter (fun Ad => D ⊆ Ad ∧ P Ad D) : Set (Finset Pr)) := by
      intro Ad hAd Ad' hAd' h
      have h1 := (Finset.mem_filter.1 hAd).2.1
      have h2 := (Finset.mem_filter.1 hAd').2.1
      simp only at h
      rw [← Finset.sdiff_union_of_subset h1, ← Finset.sdiff_union_of_subset h2, h]
    have hmaps : ∀ Ad ∈ 𝒟.filter (fun Ad => D ⊆ Ad ∧ P Ad D), Ad \ D ∈ fsLe X := by
      intro Ad hAd
      obtain ⟨hAd𝒟, hDAd, hPAd⟩ := Finset.mem_filter.1 hAd
      exact mem_fsLe_of_nI_le (hP Ad hAd𝒟 D hDAd hPAd)
    exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
  calc ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset, (if P Ad D then
        ∑ E ∈ U.powerset, (if D ∪ E ⊆ A then (1 : ℝ) else 0) else 0)
      ≤ ∑ Ad ∈ 𝒟, ∑ D ∈ A.powerset, (if D ⊆ Ad ∧ P Ad D then (2 : ℝ) ^ A.card else 0) :=
        Finset.sum_le_sum step1
    _ = ∑ D ∈ A.powerset, ∑ Ad ∈ 𝒟, (if D ⊆ Ad ∧ P Ad D then (2 : ℝ) ^ A.card else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _D ∈ A.powerset, (2 : ℝ) ^ A.card * ((2 * kappa + 5) * X) := Finset.sum_le_sum step2
    _ = 4 ^ A.card * ((2 * kappa + 5) * X) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, ← mul_assoc]
        push_cast
        rw [← mul_pow]; norm_num

open Classical in
/-- **Exchanging the order**: a nested sum of column weights over the triples `(Ad, D, E)` is
`Σ_A h(A)` times the number of triples reaching `A`. -/
theorem sum_triple_swap (𝒟 : Finset (Finset Pr)) (U : Finset Pr) (𝒩 : Finset (Finset Pr))
    (h : Finset Pr → ℝ) (Q : Finset Pr → Finset Pr → Prop) [∀ Ad, DecidablePred (Q Ad)]
    (G : Finset Pr → Finset Pr → Finset Pr) :
    ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset.filter (Q Ad), ∑ E ∈ U.powerset,
      ∑ A ∈ 𝒩.filter (fun A => G Ad D ∪ E ⊆ A), h A =
      ∑ A ∈ 𝒩, h A * ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset, (if Q Ad D then
        ∑ E ∈ U.powerset, (if G Ad D ∪ E ⊆ A then (1 : ℝ) else 0) else 0) := by
  have e1 : ∀ A ∈ 𝒩, h A * ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset, (if Q Ad D then
      ∑ E ∈ U.powerset, (if G Ad D ∪ E ⊆ A then (1 : ℝ) else 0) else 0) =
      ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset.filter (Q Ad), ∑ E ∈ U.powerset,
        (if G Ad D ∪ E ⊆ A then h A else 0) := by
    intro A _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Ad _ => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun D _ => ?_
    split_ifs with hQ
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      split_ifs <;> simp
    · simp
  symm
  calc ∑ A ∈ 𝒩, h A * ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset, (if Q Ad D then
        ∑ E ∈ U.powerset, (if G Ad D ∪ E ⊆ A then (1 : ℝ) else 0) else 0)
      = ∑ A ∈ 𝒩, ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset.filter (Q Ad), ∑ E ∈ U.powerset,
          (if G Ad D ∪ E ⊆ A then h A else 0) := Finset.sum_congr rfl e1
    _ = ∑ Ad ∈ 𝒟, ∑ A ∈ 𝒩, ∑ D ∈ Ad.powerset.filter (Q Ad), ∑ E ∈ U.powerset,
          (if G Ad D ∪ E ⊆ A then h A else 0) := Finset.sum_comm
    _ = ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset.filter (Q Ad), ∑ A ∈ 𝒩, ∑ E ∈ U.powerset,
          (if G Ad D ∪ E ⊆ A then h A else 0) :=
        Finset.sum_congr rfl fun Ad _ => Finset.sum_comm
    _ = ∑ Ad ∈ 𝒟, ∑ D ∈ Ad.powerset.filter (Q Ad), ∑ E ∈ U.powerset, ∑ A ∈ 𝒩,
          (if G Ad D ∪ E ⊆ A then h A else 0) :=
        Finset.sum_congr rfl fun Ad _ => Finset.sum_congr rfl fun D _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun Ad _ => Finset.sum_congr rfl fun D _ =>
          Finset.sum_congr rfl fun E _ => (Finset.sum_filter _ _).symm

/-- **Cauchy–Schwarz over a triple sum.** -/
theorem sum3_sqrt_le {ι κ μ : Type*} (s : Finset ι) (t : ι → Finset κ) (u : Finset μ)
    (f g : ι → κ → μ → ℝ) (hf : ∀ i k l, 0 ≤ f i k l) (hg : ∀ i k l, 0 ≤ g i k l) :
    ∑ i ∈ s, ∑ k ∈ t i, ∑ l ∈ u, Real.sqrt (f i k l) * Real.sqrt (g i k l) ≤
      Real.sqrt (∑ i ∈ s, ∑ k ∈ t i, ∑ l ∈ u, f i k l) *
        Real.sqrt (∑ i ∈ s, ∑ k ∈ t i, ∑ l ∈ u, g i k l) := by
  calc ∑ i ∈ s, ∑ k ∈ t i, ∑ l ∈ u, Real.sqrt (f i k l) * Real.sqrt (g i k l)
      ≤ ∑ i ∈ s, ∑ k ∈ t i, Real.sqrt (∑ l ∈ u, f i k l) * Real.sqrt (∑ l ∈ u, g i k l) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
          Real.sum_sqrt_mul_sqrt_le u (hf i k) (hg i k)
    _ ≤ ∑ i ∈ s, Real.sqrt (∑ k ∈ t i, ∑ l ∈ u, f i k l) *
          Real.sqrt (∑ k ∈ t i, ∑ l ∈ u, g i k l) :=
        Finset.sum_le_sum fun i _ => Real.sum_sqrt_mul_sqrt_le (t i)
          (fun k => Finset.sum_nonneg fun l _ => hf i k l)
          (fun k => Finset.sum_nonneg fun l _ => hg i k l)
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le s
          (fun i => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hf i k l)
          (fun i => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hg i k l)

/-- **The complement on a power set**: `Σ_{D⊆Ad} f(D) = Σ_{D⊆Ad} f(Ad ∖ D)`. -/
theorem sum_powerset_compl {α : Type*} [DecidableEq α] (Ad : Finset α) (f : Finset α → ℝ) :
    ∑ D ∈ Ad.powerset, f D = ∑ D ∈ Ad.powerset, f (Ad \ D) := by
  refine Finset.sum_nbij' (fun D => Ad \ D) (fun D => Ad \ D) ?_ ?_ ?_ ?_ ?_
  · intro D _; exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro D _; exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro D hD; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hD)
  · intro D hD; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hD)
  · intro D hD; rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hD)]

open Classical in
theorem norm_colX_le (𝒩 : Finset (Finset Pr)) (γ : Finset Pr → ℂ) (F : Finset Pr) (m : 𝓞 K) :
    ‖colX 𝒩 γ F m‖ ≤ ∑ A ∈ 𝒩, ‖γ A‖ :=
  (norm_q2Sum_le _ γ m).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => norm_nonneg _)

theorem summable_w_colX {w : 𝓞 K → ℝ} (hw : Summable w) (𝒩 : Finset (Finset Pr))
    (γ : Finset Pr → ℂ) (F : Finset Pr) :
    Summable fun m => w m * ‖colX 𝒩 γ F m‖ ^ 2 := by
  unfold colX; exact summable_w_colSum hw _ γ

/-- The pointwise Cauchy–Schwarz identity `w|X||Y| = √(w|X|²)·√(w|Y|²)` for `w ≥ 0`. -/
theorem w_mul_eq_sqrt {w x y : ℝ} (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    w * x * y = Real.sqrt (w * x ^ 2) * Real.sqrt (w * y ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  rw [show w * x ^ 2 * (w * y ^ 2) = (w * x * y) ^ 2 by ring, Real.sqrt_sq (by positivity)]

open Classical in
/-- **One separated sum**: `Σ_m w(m)|Σ_{A₁,A₂ disjoint, Ad ⊆ A₁∪A₂} …| ≤
Σ_{D₁⊆Ad} Σ_{E⊆U} √(a(D₁ ∪ E))·√(b((Ad ∖ D₁) ∪ E))`. -/
theorem sep_one {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) (U : Finset Pr)
    (𝒩 : Finset (Finset Pr)) (h𝒩 : ∀ A ∈ 𝒩, A ⊆ U) (α β : Finset Pr → ℂ) (Ad : Finset Pr) :
    ∑' m : 𝓞 K, w m * ‖∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
      (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0)‖ ≤
      ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset,
        Real.sqrt (∑' m : 𝓞 K, w m * ‖colX 𝒩 α (D1 ∪ E) m‖ ^ 2) *
          Real.sqrt (∑' m : 𝓞 K, w m * ‖colX 𝒩 β ((Ad \ D1) ∪ E) m‖ ^ 2) := by
  set Ba := ∑ A ∈ 𝒩, ‖α A‖
  set Bb := ∑ A ∈ 𝒩, ‖β A‖
  have hBa : 0 ≤ Ba := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hBb : 0 ≤ Bb := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set g : Finset Pr → Finset Pr → 𝓞 K → ℝ := fun D1 E m =>
    w m * ‖colX 𝒩 α (D1 ∪ E) m‖ * ‖colX 𝒩 β ((Ad \ D1) ∪ E) m‖ with hg
  have hgs : ∀ D1 E, Summable (g D1 E) := by
    intro D1 E
    have := summable_w_mul hw (g := fun m => ‖colX 𝒩 α (D1 ∪ E) m‖ * ‖colX 𝒩 β ((Ad \ D1) ∪ E) m‖)
      (B := Ba * Bb) fun m => by
        rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul (norm_colX_le 𝒩 α _ m) (norm_colX_le 𝒩 β _ m) (norm_nonneg _) hBa
    refine this.congr fun m => ?_
    simp only [hg]; ring
  have hpt : ∀ m : 𝓞 K, w m * ‖∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
      (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0)‖ ≤
      ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset, g D1 E m := by
    intro m
    rw [sepInner_eq U 𝒩 h𝒩 α β Ad m]
    calc w m * ‖∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset, (-1 : ℂ) ^ E.card *
          (colX 𝒩 α (D1 ∪ E) m * colX 𝒩 β ((Ad \ D1) ∪ E) m)‖
        ≤ w m * ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset,
            ‖colX 𝒩 α (D1 ∪ E) m‖ * ‖colX 𝒩 β ((Ad \ D1) ∪ E) m‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (hw0 m)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun D1 _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun E _ => ?_)
          rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      _ = ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset, g D1 E m := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun D1 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun E _ => ?_
          simp only [hg]; ring
  have hRs : Summable fun m => ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset, g D1 E m :=
    summable_sum fun D1 _ => summable_sum fun E _ => hgs D1 E
  have hLs := Summable.of_nonneg_of_le (fun m => mul_nonneg (hw0 m) (norm_nonneg _)) hpt hRs
  calc ∑' m : 𝓞 K, w m * ‖∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
        (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0)‖
      ≤ ∑' m : 𝓞 K, ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset, g D1 E m :=
        hLs.tsum_le_tsum hpt hRs
    _ = ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset, ∑' m : 𝓞 K, g D1 E m := by
        rw [Summable.tsum_finsetSum fun D1 _ => summable_sum fun E _ => hgs D1 E]
        refine Finset.sum_congr rfl fun D1 _ => ?_
        rw [Summable.tsum_finsetSum fun E _ => hgs D1 E]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun D1 _ => Finset.sum_le_sum fun E _ => ?_
        have hc0 : ∀ m, 0 ≤ g D1 E m := fun m =>
          mul_nonneg (mul_nonneg (hw0 m) (norm_nonneg _)) (norm_nonneg _)
        have hc : ∀ m, g D1 E m ≤
            Real.sqrt (w m * ‖colX 𝒩 α (D1 ∪ E) m‖ ^ 2) *
              Real.sqrt (w m * ‖colX 𝒩 β ((Ad \ D1) ∪ E) m‖ ^ 2) := fun m =>
          (w_mul_eq_sqrt (hw0 m) (norm_nonneg _) (norm_nonneg _)).le
        exact tsum_le_sqrt_mul_sqrt (summable_w_colX hw _ _ _) (summable_w_colX hw _ _ _)
          (fun m => mul_nonneg (hw0 m) (sq_nonneg _)) (fun m => mul_nonneg (hw0 m) (sq_nonneg _))
          hc0 hc

/-- With `j = ⌈log₂ N(D)⌉`: `2^j < 2N(D)` and `N(D) ≤ 2^j`. -/
theorem nI_clog_bounds (D1 : Finset Pr) :
    (2 : ℝ) ^ Nat.clog 2 (absNorm (idl D1)) < 2 * nI D1 ∧
      nI D1 ≤ (2 : ℝ) ^ Nat.clog 2 (absNorm (idl D1)) := by
  have h1 : 1 ≤ absNorm (idl D1) := Nat.one_le_iff_ne_zero.2 (absNorm_idl_ne_zero D1)
  constructor
  · have := pow_clog_lt_two_mul h1
    unfold nI; exact_mod_cast this
  · have := Nat.le_pow_clog (by norm_num : 1 < 2) (absNorm (idl D1))
    unfold nI; exact_mod_cast this

open Classical in
/-- **Heath-Brown's Lemma 10** (Goldmakher and Louvel's Lemma 7.1), for any nonnegative summable
weight on the arguments. For moduli `d` (sets of primes `Ad`) with `D < N(d) ≤ 2D` and columns of
norm at most `N`, the sums `Σ_m w(m)|Σ_{(n₁,n₂)=1, d∣n₁n₂} α(n₁)β(n₂)(m/n₁n₂)₂|` are at most
`C·N^δ·Σ_j √(4D·F(2N/2^j)·F(N·2^j/D))·‖α‖·‖β‖`, where `F(x)` is a constant for the norm at `x`
and `j` runs over `0 ≤ j ≤ ⌈log₂ 2D⌉`: the `j`-th class has `d = d₁d₂` with
`2^{j−1} < N(d₁) ≤ 2^j`. -/
theorem fBound_sep {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N D : ℝ) (F : ℝ → ℝ), 1 ≤ N → 0 < D → (∀ x, 0 ≤ F x) →
      (∀ x, FBound w x (F x)) →
      ∀ (𝒩 𝒟 : Finset (Finset Pr)) (α β : Finset Pr → ℂ), (∀ A ∈ 𝒩, nI A ≤ N) →
        (∀ Ad ∈ 𝒟, D < nI Ad ∧ nI Ad ≤ 2 * D) →
        ∑ Ad ∈ 𝒟, ∑' m : 𝓞 K, w m * ‖∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
          (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0)‖ ≤
        C * N ^ δ * (∑ j ∈ Finset.range (Nat.clog 2 ⌊2 * D⌋₊ + 1),
          Real.sqrt (4 * D * F (2 * N / 2 ^ j) * F (N * 2 ^ j / D))) *
          Real.sqrt (∑ A ∈ 𝒩, ‖α A‖ ^ 2) * Real.sqrt (∑ A ∈ 𝒩, ‖β A‖ ^ 2) := by
  obtain ⟨C4, hC4pos, hC4⟩ := four_pow_card_le hδ
  have hk := kappa_pos
  refine ⟨(2 * kappa + 5) * C4, by positivity, fun N D F hN hD hF0 hF 𝒩 𝒟 α β h𝒩 h𝒟 => ?_⟩
  set U : Finset Pr := 𝒩.sup id with hU
  have h𝒩U : ∀ A ∈ 𝒩, A ⊆ U := fun A hA => Finset.le_sup (f := id) hA
  set L := Nat.clog 2 ⌊2 * D⌋₊ + 1 with hL
  set cls : Finset Pr → ℕ := fun D1 => Nat.clog 2 (absNorm (idl D1)) with hcls
  set a : Finset Pr → ℝ := fun F' => ∑' m : 𝓞 K, w m * ‖colX 𝒩 α F' m‖ ^ 2 with ha
  set b : Finset Pr → ℝ := fun F' => ∑' m : 𝓞 K, w m * ‖colX 𝒩 β F' m‖ ^ 2 with hb
  set Sα := ∑ A ∈ 𝒩, ‖α A‖ ^ 2 with hSα
  set Sβ := ∑ A ∈ 𝒩, ‖β A‖ ^ 2 with hSβ
  have ha0 : ∀ F', 0 ≤ a F' := fun F' => tsum_nonneg fun m => mul_nonneg (hw0 m) (sq_nonneg _)
  have hb0 : ∀ F', 0 ≤ b F' := fun F' => tsum_nonneg fun m => mul_nonneg (hw0 m) (sq_nonneg _)
  have hSα0 : 0 ≤ Sα := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSβ0 : 0 ≤ Sβ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set c0 : ℝ := C4 * N ^ δ with hc0
  have hNδ : 0 ≤ N ^ δ := Real.rpow_nonneg (by linarith) δ
  have hc00 : 0 ≤ c0 := mul_nonneg hC4pos.le hNδ
  have h4 : ∀ A ∈ 𝒩, (4 : ℝ) ^ A.card ≤ c0 := fun A hA =>
    (hC4 A).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (nI_pos A).le (h𝒩 A hA) hδ.le) hC4pos.le)
  -- the classes of the splittings
  have hcls_lt : ∀ Ad ∈ 𝒟, ∀ D1 ∈ Ad.powerset, cls D1 ∈ Finset.range L := by
    intro Ad hAd D1 hD1
    rw [Finset.mem_range, hL, Nat.lt_succ_iff]
    refine Nat.clog_mono_right 2 ?_
    have e1 : absNorm (idl D1) ≤ absNorm (idl Ad) := absNorm_idl_mono (Finset.mem_powerset.1 hD1)
    have e2 : ((absNorm (idl Ad) : ℕ) : ℝ) ≤ 2 * D := (h𝒟 Ad hAd).2
    exact e1.trans (Nat.le_floor e2)
  -- the column count for `α`
  have hA : ∀ j : ℕ, ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
      ∑ E ∈ U.powerset, a (D1 ∪ E) ≤
        F (2 * N / 2 ^ j) * ((2 * kappa + 5) * (4 * D / 2 ^ j) * c0 * Sα) := by
    intro j
    have hj : (0 : ℝ) < 2 ^ j := by positivity
    have hpiece : ∀ Ad ∈ 𝒟, ∀ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j), ∀ E : Finset Pr,
        a (D1 ∪ E) ≤ F (2 * N / 2 ^ j) *
          ∑ A ∈ 𝒩.filter (fun A => D1 ∪ E ⊆ A), ‖α A‖ ^ 2 := by
      intro Ad _ D1 hD1 E
      have hcl : cls D1 = j := (Finset.mem_filter.1 hD1).2
      have hb1 := (nI_clog_bounds D1).1
      simp only [hcls] at hcl
      rw [hcl] at hb1
      refine (hF (2 * N / 2 ^ j)).sub hw0 hw 𝒩 α (D1 ∪ E) fun A hA _ => ?_
      have e1 : nI D1 ≤ nI (D1 ∪ E) := nI_mono Finset.subset_union_left
      have e2 := h𝒩 A hA
      rw [div_mul_eq_mul_div, le_div_iff₀ hj]
      nlinarith
    have hX : 0 ≤ 4 * D / 2 ^ j := by positivity
    calc ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
          ∑ E ∈ U.powerset, a (D1 ∪ E)
        ≤ ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j), ∑ E ∈ U.powerset,
            F (2 * N / 2 ^ j) * ∑ A ∈ 𝒩.filter (fun A => D1 ∪ E ⊆ A), ‖α A‖ ^ 2 :=
          Finset.sum_le_sum fun Ad hAd => Finset.sum_le_sum fun D1 hD1 =>
            Finset.sum_le_sum fun E _ => hpiece Ad hAd D1 hD1 E
      _ = F (2 * N / 2 ^ j) * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 * ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset,
            (if cls D1 = j then ∑ E ∈ U.powerset,
              (if D1 ∪ E ⊆ A then (1 : ℝ) else 0) else 0) := by
          rw [← sum_triple_swap 𝒟 U 𝒩 (fun A => ‖α A‖ ^ 2) (fun _ D1 => cls D1 = j)
            (fun _ D1 => D1)]
          simp_rw [Finset.mul_sum]
      _ ≤ F (2 * N / 2 ^ j) * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 *
            (4 ^ A.card * ((2 * kappa + 5) * (4 * D / 2 ^ j))) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun A _ =>
            mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (hF0 _)
          refine count_cover 𝒟 U A (fun _ D1 => cls D1 = j) hX fun Ad hAd D1 hD1 hcl => ?_
          have hb1 := (nI_clog_bounds D1).1
          simp only [hcls] at hcl
          rw [hcl] at hb1
          have e1 := nI_sdiff_mul hD1
          have e2 := (h𝒟 Ad hAd).2
          have e3 := nI_pos (Ad \ D1)
          rw [le_div_iff₀ hj]
          nlinarith
      _ ≤ F (2 * N / 2 ^ j) * ((2 * kappa + 5) * (4 * D / 2 ^ j) * c0 * Sα) := by
          refine mul_le_mul_of_nonneg_left ?_ (hF0 _)
          rw [hSα, Finset.mul_sum]
          refine Finset.sum_le_sum fun A hA => ?_
          have hX' : 0 ≤ (2 * kappa + 5) * (4 * D / 2 ^ j) := by positivity
          have := mul_le_mul_of_nonneg_left (h4 A hA) (mul_nonneg (sq_nonneg ‖α A‖) hX')
          nlinarith [this]
  -- the column count for `β`
  have hB : ∀ j : ℕ, ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
      ∑ E ∈ U.powerset, b ((Ad \ D1) ∪ E) ≤
        F (N * 2 ^ j / D) * ((2 * kappa + 5) * 2 ^ j * c0 * Sβ) := by
    intro j
    have hj : (0 : ℝ) < 2 ^ j := by positivity
    have hpiece : ∀ Ad ∈ 𝒟, ∀ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j), ∀ E : Finset Pr,
        b ((Ad \ D1) ∪ E) ≤ F (N * 2 ^ j / D) *
          ∑ A ∈ 𝒩.filter (fun A => (Ad \ D1) ∪ E ⊆ A), ‖β A‖ ^ 2 := by
      intro Ad hAd D1 hD1 E
      have hcl : cls D1 = j := (Finset.mem_filter.1 hD1).2
      have hD1s : D1 ⊆ Ad := Finset.mem_powerset.1 (Finset.mem_filter.1 hD1).1
      have hb2 := (nI_clog_bounds D1).2
      simp only [hcls] at hcl
      rw [hcl] at hb2
      refine (hF (N * 2 ^ j / D)).sub hw0 hw 𝒩 β ((Ad \ D1) ∪ E) fun A hA _ => ?_
      have e1 : nI (Ad \ D1) ≤ nI ((Ad \ D1) ∪ E) := nI_mono Finset.subset_union_left
      have e2 := h𝒩 A hA
      have e3 := nI_sdiff_mul hD1s
      have e4 := (h𝒟 Ad hAd).1
      have e6 := nI_pos (Ad \ D1)
      have hN0 : (0 : ℝ) ≤ N := by linarith
      have p1 : nI A * D ≤ N * D := mul_le_mul_of_nonneg_right e2 hD.le
      have p2 : N * D ≤ N * nI Ad := mul_le_mul_of_nonneg_left e4.le hN0
      have p3 : N * nI Ad ≤ N * (nI (Ad \ D1) * 2 ^ j) := by
        refine mul_le_mul_of_nonneg_left ?_ hN0
        rw [← e3]; exact mul_le_mul_of_nonneg_left hb2 e6.le
      have p4 : N * (nI (Ad \ D1) * 2 ^ j) ≤ N * 2 ^ j * nI ((Ad \ D1) ∪ E) := by
        have := mul_le_mul_of_nonneg_left e1 (mul_nonneg hN0 hj.le)
        nlinarith [this]
      rw [div_mul_eq_mul_div, le_div_iff₀ hD]
      linarith
    have hX : (0 : ℝ) ≤ 2 ^ j := hj.le
    have hcount : ∀ A, ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset, (if cls D1 = j then
        ∑ E ∈ U.powerset, (if (Ad \ D1) ∪ E ⊆ A then (1 : ℝ) else 0) else 0) ≤
        4 ^ A.card * ((2 * kappa + 5) * 2 ^ j) := by
      intro A
      have e : ∀ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset, (if cls D1 = j then
          ∑ E ∈ U.powerset, (if (Ad \ D1) ∪ E ⊆ A then (1 : ℝ) else 0) else 0) =
          ∑ D2 ∈ Ad.powerset, (if cls (Ad \ D2) = j then
            ∑ E ∈ U.powerset, (if D2 ∪ E ⊆ A then (1 : ℝ) else 0) else 0) := by
        intro Ad _
        rw [sum_powerset_compl Ad]
        refine Finset.sum_congr rfl fun D2 hD2 => ?_
        rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hD2)]
      rw [Finset.sum_congr rfl e]
      refine count_cover 𝒟 U A (fun Ad D2 => cls (Ad \ D2) = j) hX fun Ad _ D2 _ hcl => ?_
      have hb2 := (nI_clog_bounds (Ad \ D2)).2
      simp only [hcls] at hcl
      rwa [hcl] at hb2
    calc ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
          ∑ E ∈ U.powerset, b ((Ad \ D1) ∪ E)
        ≤ ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j), ∑ E ∈ U.powerset,
            F (N * 2 ^ j / D) * ∑ A ∈ 𝒩.filter (fun A => (Ad \ D1) ∪ E ⊆ A), ‖β A‖ ^ 2 :=
          Finset.sum_le_sum fun Ad hAd => Finset.sum_le_sum fun D1 hD1 =>
            Finset.sum_le_sum fun E _ => hpiece Ad hAd D1 hD1 E
      _ = F (N * 2 ^ j / D) * ∑ A ∈ 𝒩, ‖β A‖ ^ 2 * ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset,
            (if cls D1 = j then ∑ E ∈ U.powerset,
              (if (Ad \ D1) ∪ E ⊆ A then (1 : ℝ) else 0) else 0) := by
          rw [← sum_triple_swap 𝒟 U 𝒩 (fun A => ‖β A‖ ^ 2) (fun _ D1 => cls D1 = j)
            (fun Ad D1 => Ad \ D1)]
          simp_rw [Finset.mul_sum]
      _ ≤ F (N * 2 ^ j / D) * ∑ A ∈ 𝒩, ‖β A‖ ^ 2 * (4 ^ A.card * ((2 * kappa + 5) * 2 ^ j)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun A _ =>
            mul_le_mul_of_nonneg_left (hcount A) (sq_nonneg _)) (hF0 _)
      _ ≤ F (N * 2 ^ j / D) * ((2 * kappa + 5) * 2 ^ j * c0 * Sβ) := by
          refine mul_le_mul_of_nonneg_left ?_ (hF0 _)
          rw [hSβ, Finset.mul_sum]
          refine Finset.sum_le_sum fun A hA => ?_
          have hX' : 0 ≤ (2 * kappa + 5) * (2 : ℝ) ^ j := by positivity
          have := mul_le_mul_of_nonneg_left (h4 A hA) (mul_nonneg (sq_nonneg ‖β A‖) hX')
          nlinarith [this]
  -- one class
  have hclass : ∀ j : ℕ, ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
      ∑ E ∈ U.powerset, Real.sqrt (a (D1 ∪ E)) * Real.sqrt (b ((Ad \ D1) ∪ E)) ≤
        (2 * kappa + 5) * C4 * N ^ δ *
          Real.sqrt (4 * D * F (2 * N / 2 ^ j) * F (N * 2 ^ j / D)) *
            Real.sqrt Sα * Real.sqrt Sβ := by
    intro j
    have hj : (0 : ℝ) < 2 ^ j := by positivity
    refine (sum3_sqrt_le 𝒟 (fun Ad => Ad.powerset.filter (fun D1 => cls D1 = j)) U.powerset
      (fun _ D1 E => a (D1 ∪ E)) (fun Ad D1 E => b ((Ad \ D1) ∪ E)) (fun _ _ _ => ha0 _)
      (fun _ _ _ => hb0 _)).trans ?_
    set F1 := F (2 * N / 2 ^ j)
    set F2 := F (N * 2 ^ j / D)
    have hF1 : 0 ≤ F1 := hF0 _
    have hF2 : 0 ≤ F2 := hF0 _
    have hPa : 0 ≤ F1 * ((2 * kappa + 5) * (4 * D / 2 ^ j) * c0 * Sα) := by positivity
    have hPb : 0 ≤ F2 * ((2 * kappa + 5) * 2 ^ j * c0 * Sβ) := by positivity
    calc Real.sqrt (∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
          ∑ E ∈ U.powerset, a (D1 ∪ E)) *
        Real.sqrt (∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
          ∑ E ∈ U.powerset, b ((Ad \ D1) ∪ E))
        ≤ Real.sqrt (F1 * ((2 * kappa + 5) * (4 * D / 2 ^ j) * c0 * Sα)) *
            Real.sqrt (F2 * ((2 * kappa + 5) * 2 ^ j * c0 * Sβ)) :=
          mul_le_mul (Real.sqrt_le_sqrt (hA j)) (Real.sqrt_le_sqrt (hB j)) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt (((2 * kappa + 5) * c0) ^ 2 * ((4 * D * F1 * F2) * (Sα * Sβ))) := by
          rw [← Real.sqrt_mul hPa]
          congr 1
          field_simp
      _ = (2 * kappa + 5) * C4 * N ^ δ * Real.sqrt (4 * D * F1 * F2) *
            Real.sqrt Sα * Real.sqrt Sβ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
            Real.sqrt_mul (by positivity), Real.sqrt_mul hSα0, hc0]
          ring
  -- the assembly
  calc ∑ Ad ∈ 𝒟, ∑' m : 𝓞 K, w m * ‖∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
        (if Disjoint A1 A2 ∧ Ad ⊆ A1 ∪ A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0)‖
      ≤ ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset, ∑ E ∈ U.powerset,
          Real.sqrt (a (D1 ∪ E)) * Real.sqrt (b ((Ad \ D1) ∪ E)) :=
        Finset.sum_le_sum fun Ad _ => sep_one hw0 hw U 𝒩 h𝒩U α β Ad
    _ = ∑ Ad ∈ 𝒟, ∑ j ∈ Finset.range L, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
          ∑ E ∈ U.powerset, Real.sqrt (a (D1 ∪ E)) * Real.sqrt (b ((Ad \ D1) ∪ E)) :=
        Finset.sum_congr rfl fun Ad hAd =>
          (Finset.sum_fiberwise_of_maps_to (hcls_lt Ad hAd) _).symm
    _ = ∑ j ∈ Finset.range L, ∑ Ad ∈ 𝒟, ∑ D1 ∈ Ad.powerset.filter (fun D1 => cls D1 = j),
          ∑ E ∈ U.powerset, Real.sqrt (a (D1 ∪ E)) * Real.sqrt (b ((Ad \ D1) ∪ E)) :=
        Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range L, (2 * kappa + 5) * C4 * N ^ δ *
          Real.sqrt (4 * D * F (2 * N / 2 ^ j) * F (N * 2 ^ j / D)) *
            Real.sqrt Sα * Real.sqrt Sβ := Finset.sum_le_sum fun j _ => hclass j
    _ = (2 * kappa + 5) * C4 * N ^ δ * (∑ j ∈ Finset.range L,
          Real.sqrt (4 * D * F (2 * N / 2 ^ j) * F (N * 2 ^ j / D))) *
            Real.sqrt Sα * Real.sqrt Sβ := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]

theorem qAdm_prod_πP (A : Finset Pr) : QAdm (∏ P ∈ A, πP P) := by
  refine ⟨primary_prod_πP A, ?_, ?_⟩
  · rw [span_prod_πP]; exact idl_squarefree A
  · rw [span_prod_πP]; exact idl_coprime6 A

theorem primeSet_prod_πP (A : Finset Pr) : primeSet (span {∏ P ∈ A, πP P}) = A := by
  rw [span_prod_πP, primeSet_idl]

open Classical in
/-- The weight of the admissible arguments of norm at most `M`. -/
def admW (M : ℝ) (m : 𝓞 K) : ℝ := if QAdm m ∧ (absNorm (span {m}) : ℝ) ≤ M then 1 else 0

theorem admW_nonneg (M : ℝ) (m : 𝓞 K) : 0 ≤ admW M m := by
  unfold admW; split_ifs <;> norm_num

theorem summable_admW (M : ℝ) : Summable (admW M) := by
  refine summable_of_ne_finset_zero (s := eltsLe M) fun m hm => ?_
  unfold admW
  exact ite_eq_right fun h => hm (mem_eltsLe.2 h.2)

open Classical in
/-- **From the weighted norm to the sieve norm**: with the admissible arguments of norm at most
`M` as rows, the weighted norm at `N` gives round 344's `QBound N M`, by duality. -/
theorem qBound_of_fBound {M N Δ : ℝ} (hΔ : 0 ≤ Δ) (h : FBound (admW M) N Δ) :
    QBound N M Δ := by
  intro Ks Ns a hK hN
  refine duality Ks Ns (fun k n => sym2 n (span {k})) hΔ (fun b => ?_) a
  set 𝒩 := Ks.image (fun k => primeSet (span {k})) with h𝒩d
  set α : Finset Pr → ℂ := fun A => b (∏ P ∈ A, πP P) with hα
  have hinj : Set.InjOn (fun k => primeSet (span {k})) (Ks : Set (𝓞 K)) :=
    fun k hk k' hk' e => eq_of_primeSet_eq (hK k hk).1 (hK k' hk').1 e
  have hcol : ∀ n, ∑ k ∈ Ks, b k * sym2 n (span {k}) = ∑ A ∈ 𝒩, α A * q2 A n := by
    intro n
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [hα]
    rw [← (eq_prod_of_adm (hK k hk).1).1, sym2_eq_q2 (hK k hk).1]
  have hnorm : ∑ A ∈ 𝒩, ‖α A‖ ^ 2 = ∑ k ∈ Ks, ‖b k‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [hα]
    rw [← (eq_prod_of_adm (hK k hk).1).1]
  have h𝒩 : ∀ A ∈ 𝒩, nI A ≤ N := by
    intro A hA
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hA
    rw [nI_primeSet (hK k hk).1]; exact (hK k hk).2
  calc ∑ n ∈ Ns, ‖∑ k ∈ Ks, b k * sym2 n (span {k})‖ ^ 2
      = ∑ n ∈ Ns, admW M n * ‖∑ A ∈ 𝒩, α A * q2 A n‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hw : admW M n = 1 := by unfold admW; exact ite_eq_left (hN n hn)
        rw [hcol, hw, one_mul]
    _ ≤ ∑' m : 𝓞 K, admW M m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 :=
        (summable_w_colSum (summable_admW M) 𝒩 α).sum_le_tsum Ns
          fun m _ => mul_nonneg (admW_nonneg M m) (sq_nonneg _)
    _ ≤ Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := h 𝒩 α h𝒩
    _ = Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2 := by rw [hnorm]

open Classical in
/-- **From the sieve norm to the weighted norm**: round 344's `QBound N M` gives the weighted
norm at `N` with the admissible arguments of norm at most `M` as rows, by duality. -/
theorem fBound_of_qBound {M N Δ : ℝ} (hΔ : 0 ≤ Δ) (h : QBound N M Δ) :
    FBound (admW M) N Δ := by
  intro 𝒩 α h𝒩
  set Ms : Finset (𝓞 K) := (eltsLe M).filter QAdm with hMs
  set Ks : Finset (𝓞 K) := 𝒩.image (fun A => ∏ P ∈ A, πP P) with hKs
  set b : 𝓞 K → ℂ := fun k => α (primeSet (span {k})) with hb
  have hinj : Set.InjOn (fun A : Finset Pr => ∏ P ∈ A, πP P) (𝒩 : Set (Finset Pr)) := by
    intro A _ B _ e
    have := congrArg (fun k => primeSet (span {k})) e
    simpa only [primeSet_prod_πP] using this
  have hK : ∀ k ∈ Ks, QAdm k ∧ (absNorm (span {k}) : ℝ) ≤ N := by
    intro k hk
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨qAdm_prod_πP A, by rw [absNorm_span_prod_πP]; exact h𝒩 A hA⟩
  have hM : ∀ n ∈ Ms, QAdm n ∧ (absNorm (span {n}) : ℝ) ≤ M := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hn
    exact ⟨h2, mem_eltsLe.1 h1⟩
  have hd := duality Ms Ks (fun n k => sym2 n (span {k})) hΔ (fun a => h Ks Ms a hK hM) b
  have hcol : ∀ m, ∑ k ∈ Ks, b k * sym2 m (span {k}) = ∑ A ∈ 𝒩, α A * q2 A m := by
    intro m
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun A _ => ?_
    simp only [hb, primeSet_prod_πP]
    rw [span_prod_πP, sym2_idl]; rfl
  have hnorm : ∑ k ∈ Ks, ‖b k‖ ^ 2 = ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun A _ => ?_
    simp only [hb, primeSet_prod_πP]
  have htsum : ∑' m : 𝓞 K, admW M m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 =
      ∑ m ∈ Ms, ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 := by
    rw [tsum_eq_sum (s := Ms)]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hw : admW M m = 1 := by unfold admW; exact ite_eq_left (hM m hm)
      rw [hw, one_mul]
    · intro m hm
      have hw : admW M m = 0 := by
        unfold admW
        refine ite_eq_right fun h' => hm ?_
        exact Finset.mem_filter.2 ⟨mem_eltsLe.2 h'.2, h'.1⟩
      rw [hw, zero_mul]
  rw [htsum, ← hnorm]
  calc ∑ m ∈ Ms, ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2
      = ∑ m ∈ Ms, ‖∑ k ∈ Ks, b k * sym2 m (span {k})‖ ^ 2 :=
        Finset.sum_congr rfl fun m _ => by rw [hcol]
    _ ≤ Δ * ∑ k ∈ Ks, ‖b k‖ ^ 2 := hd

end Eis

end

#print axioms Eis.FBound.sub
#print axioms Eis.sum_disjoint_factor
#print axioms Eis.sum_inter_eq_factor
#print axioms Eis.tsum_w_colSum_eq
#print axioms Eis.gcdPart_eq
#print axioms Eis.sum_triple_le
#print axioms Eis.fBound_gcd
#print axioms Eis.ite_disjoint_cover
#print axioms Eis.sepInner_eq
#print axioms Eis.tsum_le_sqrt_mul_sqrt
#print axioms Eis.count_cover
#print axioms Eis.sum_triple_swap
#print axioms Eis.sep_one
#print axioms Eis.fBound_sep
#print axioms Eis.qBound_of_fBound
#print axioms Eis.fBound_of_qBound
