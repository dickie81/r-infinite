import EisensteinTransferRegroup

/-! # Lemma 7.3, part 2: the column mean square of a block (round 324)

S5c-5, part 3, in round 316's plan. In the companion paper's proof of Lemma 7.3 the columns are
"`a^\sharp(n) =a_{\xi'}(n)\ind_{(n,r)=1}\chi_n(k')\chi_n(f')^4`", and for each dyadic block
"Lemma~\ref{lem:remove-exclusions} then gives" the column mean square through the child mean squares at
`(X′/N(j), F′N(j))`, `j ∣ r`. This file proves the pilot's form for one block of round 323's rows: the
column hypothesis of round 317's bilinear bound.

* **The columns as an excluded column sum** (`fQe`, **`colQ_eq`**, `eS_fQ`, `colB`, `sum_aQ_eq_colB`,
  `sum_rQ_eq_colB`, **`sum_aQ_eq_colSum`**): `colQ = colA ξ k′ f′·χ_M(d_V)⁶`, and a row's column sum
  is `conj(C_r(X′; k′, f′))`, round 305's column sum with the exclusion `r`, for the conjugated test
  function.
* **The multiplicity** (`phiQ`, **`card_fiber_phiQ_le`**, `sum_phiQ_le`): the rows with a given image
  `(r, 𝔣′, k′)` are determined by `(V, b, T, T₂)`, so there are at most `2^{|r|}·8^{|f′|}` of them.
* **The child mean squares** (`ChildBound`, `colSum_const_mul`, `rowE_const_mul`,
  `ChildBound.scaled`, `Ctriv`, **`child_rowE_le`**): `ChildBound` is `TransferEstimate`'s hypothesis on
  the child mean squares, verbatim. A child with `X′ ≥ 1` is bounded by it, one with `X′ < 1` by round
  315's count.
* **The block** (`blkQ`, `mem_blkQ`, `absNorm_kQ`, `kQ_bounds`, `blk_RF_le`, **`blockQ_colMS`**):
  `Σ_ρ |Σ_n aQ(n)U(x_n)|² ≤ B·Σ_r 4^{|r|}·(M + C_triv)·N²·(L/R)²` for test functions supported in
  `[α/16, 4β]` with their first `m` derivatives bounded by `N`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The columns of a row as an excluded column sum -/

/-- The element `f′ = d_b·d_T·d_{T₂}·d_{V₂}` of a row. -/
def fQe (ρ : RowQ) : 𝓞 K := eS ρ.1.1 * eS ρ.1.2.1 * eS ρ.2.1.2.1 * eS ρ.2.1.2.2

/-- **The column factor of a row** (the companion paper's regrouping
`χ_n(d_{T₂}h·(d_{T₂}w)⁴·b⁴T⁵V⁶) = χ_n(k′f′⁴)·χ_n(V)⁶`): `colQ = colA ξ k′ f′·χ_M(d_V)⁶`. -/
theorem colQ_eq (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (ρ : RowQ) (M : Finset Pr) :
    colQ ξ ρ M = colA ξ (kQ ρ) (fQe ρ) M * chiS M (eS ρ.1.2.2) ^ 6 := by
  unfold colQ colA kQ fQe
  simp only [chiS_mul, chiS_pow]
  ring

open Classical in
theorem eS_fQ {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} (h : ρ ∈ rowsQ U0 β H L S F) :
    pgen (idl (fQ ρ)) = fQe ρ := by
  obtain ⟨h1, -, -, h4, hx⟩ := rowsQ_disjoint h
  have hbT : ρ.1.1 ∪ ρ.1.2.1 ⊆ ρ.1.1 ∪ ρ.1.2.1 ∪ ρ.1.2.2 := Finset.subset_union_left
  have d1 : Disjoint (ρ.1.1 ∪ ρ.1.2.1) ρ.2.1.2.1 :=
    Finset.disjoint_of_subset_left hbT (Finset.disjoint_of_subset_right
      (Finset.subset_union_right.trans Finset.subset_union_left) hx)
  have d2 : Disjoint (ρ.1.1 ∪ ρ.1.2.1 ∪ ρ.2.1.2.1) ρ.2.1.2.2 := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left hbT
      (Finset.disjoint_of_subset_right Finset.subset_union_right hx),
      Finset.disjoint_of_subset_left Finset.subset_union_right h4⟩
  rw [pgen_idl]
  change eS (fQ ρ) = fQe ρ
  unfold fQ fQe
  rw [eS_union d2, eS_union d1, eS_union h1]

/-- The columns prime to `b₂ ∪ T₂ ∪ V₂ ∪ V`. -/
def colB (U0 : Finset Pr) (ρ : RowQ) : Finset (Finset Pr) :=
  (U0 \ (ρ.2.1.1 ∪ ρ.2.1.2.1 ∪ ρ.2.1.2.2 ∪ ρ.1.2.2)).powerset

theorem colB_subset_colRange (U0 : Finset Pr) (ρ : RowQ) : colB U0 ρ ⊆ colRange U0 ρ := by
  intro n hn
  unfold colB at hn
  unfold colRange
  rw [Finset.mem_powerset] at hn ⊢
  intro P hP
  have h := hn hP
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h ⊢
  exact ⟨⟨h.1, h.2.1.1.1, h.2.1.1.2⟩, h.2.1.2⟩

theorem disjoint_V_of_mem_colB {U0 : Finset Pr} {ρ : RowQ} {n : Finset Pr} (h : n ∈ colB U0 ρ) :
    Disjoint n ρ.1.2.2 :=
  Finset.disjoint_of_subset_left (Finset.mem_powerset.1 h)
    (Finset.disjoint_of_subset_right Finset.subset_union_right Finset.sdiff_disjoint)

open Classical in
/-- The coefficients `aQ` live on `colB`, where they are `conj(colA ξ k′ f′)`. -/
theorem sum_aQ_eq_colB (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U0 : Finset Pr) (ρ : RowQ)
    (g : Finset Pr → ℂ) :
    ∑ n ∈ U0.powerset, aQ U0 ξ ρ n * g n =
      ∑ n ∈ colB U0 ρ, conj (colA ξ (kQ ρ) (fQe ρ) n) * g n := by
  have hsub : colB U0 ρ ⊆ U0.powerset := Finset.powerset_mono.2 Finset.sdiff_subset
  have hz : ∀ n ∈ U0.powerset, n ∉ colB U0 ρ → aQ U0 ξ ρ n * g n = 0 := by
    intro n hn hnB
    unfold aQ
    split_ifs with hc
    · -- a column of the row outside `colB` meets `V`
      have hmeet : ¬ Disjoint n ρ.1.2.2 := by
        intro hd
        apply hnB
        unfold colB
        rw [Finset.mem_powerset]
        intro P hP
        have hP0 := Finset.mem_powerset.1 hn hP
        have hPc := Finset.mem_powerset.1 hc hP
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hPc ⊢
        exact ⟨hP0, ⟨⟨hPc.1.2.1, hPc.1.2.2⟩, hPc.2⟩, Finset.disjoint_left.1 hd hP⟩
      rw [Finset.not_disjoint_iff] at hmeet
      obtain ⟨P, hPn, hPV⟩ := hmeet
      have hdv : πP P ∣ eS ρ.1.2.2 := Finset.dvd_prod_of_mem _ hPV
      rw [colQ_eq, chiS_eq_zero_of_dvd hPn hdv]
      simp
    · simp
  rw [← Finset.sum_subset hsub hz]
  refine Finset.sum_congr rfl fun n hn => ?_
  unfold aQ
  rw [ite_eq_left (colB_subset_colRange U0 ρ hn), colQ_eq,
    chiS_eS_pow_six (disjoint_V_of_mem_colB hn), mul_one]

open Classical in
/-- The excluded column sum lives on `colB`: its columns prime to `r = V ∪ b₂` that meet `T₂ ∪ V₂`
have `colA ξ k′ f′ = 0`, since `T₂ ∪ V₂` divides `f′`. -/
theorem sum_rQ_eq_colB (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U0 : Finset Pr) (ρ : RowQ)
    (g : Finset Pr → ℂ) :
    ∑ M ∈ (U0 \ rQ ρ).powerset, colA ξ (kQ ρ) (fQe ρ) M * g M =
      ∑ n ∈ colB U0 ρ, colA ξ (kQ ρ) (fQe ρ) n * g n := by
  have hsub : colB U0 ρ ⊆ (U0 \ rQ ρ).powerset := by
    unfold colB rQ
    refine Finset.powerset_mono.2 (Finset.sdiff_subset_sdiff le_rfl ?_)
    intro P hP
    simp only [Finset.mem_union] at hP ⊢
    tauto
  symm
  refine Finset.sum_subset hsub fun M hM hMB => ?_
  -- a column prime to `V ∪ b₂` outside `colB` meets `T₂ ∪ V₂`
  have hmeet : ∃ P ∈ M, P ∈ ρ.2.1.2.1 ∨ P ∈ ρ.2.1.2.2 := by
    by_contra hno
    push Not at hno
    apply hMB
    unfold colB
    rw [Finset.mem_powerset]
    intro P hP
    have h0 := Finset.mem_powerset.1 hM hP
    unfold rQ at h0
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at h0 ⊢
    exact ⟨h0.1, ⟨⟨h0.2.2, (hno P hP).1⟩, (hno P hP).2⟩, h0.2.1⟩
  obtain ⟨P, hPM, hP⟩ := hmeet
  have hdvd : πP P ∣ fQe ρ := by
    unfold fQe
    rcases hP with h | h
    · have hdv : πP P ∣ eS ρ.2.1.2.1 := Finset.dvd_prod_of_mem _ h
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdv _) _
    · have hdv : πP P ∣ eS ρ.2.1.2.2 := Finset.dvd_prod_of_mem _ h
      exact dvd_mul_of_dvd_right hdv _
  rw [colA_eq_zero ξ _ _ hPM hdvd, zero_mul]

open Classical in
/-- **A row's column sum is a column sum with exclusion** (the companion paper's columns
`Σ_{(n, r) = 1} a_ξ(n)χ_n(k′f′⁴)W(N(n)/X)` of Lemma 7.3): for a test function `U` vanishing beyond `β'`
and `U₀` containing the primes of norm at most `β'X`, `X = L/(RF′)`,
`Σ_{n ⊆ U₀} aQ(n)·U(x_n) = conj(C_r(X; k′, f′))` for the conjugated test function. -/
theorem sum_aQ_eq_colSum (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ} {β' : ℝ}
    (hU : ∀ x, β' < x → U x = 0) {L R Fp : ℝ} (hL : 0 < L) (hR : 0 < R) (hFp : 0 < Fp)
    {U0 : Finset Pr} (hU0 : primesLe (β' * (L / (R * Fp))) ⊆ U0) {β H S F : ℝ} {ρ : RowQ}
    (hρ : ρ ∈ rowsQ U0 β H L S F) :
    ∑ n ∈ U0.powerset, aQ U0 ξ ρ n * U (xQ L R Fp n) =
      conj (colSum ξ (fun x => conj (U x)) (L / (R * Fp)) (idl (rQ ρ)) (kQ ρ)
        (pgen (idl (fQ ρ)))) := by
  have hX : 0 < L / (R * Fp) := by positivity
  have hUc : ∀ x, β' < x → (fun x => conj (U x)) x = 0 := fun x hx => by
    simp only [hU x hx, map_zero]
  have hxe : ∀ n : Finset Pr, nI n / (L / (R * Fp)) = xQ L R Fp n := fun n => by
    unfold xQ; field_simp
  rw [colSum_eq_powerset ξ hUc hX hU0, eS_fQ hρ]
  rw [sum_rQ_eq_colB ξ U0 ρ (fun M => (fun x => conj (U x)) (nI M / (L / (R * Fp)))),
    sum_aQ_eq_colB ξ U0 ρ (fun n => U (xQ L R Fp n)), map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [map_mul, Complex.conj_conj, hxe]

/-! ### The multiplicity of `(r, f′, k′)` -/

/-- The image `(r, 𝔣′, k′)` of a row. -/
def phiQ (ρ : RowQ) : Finset Pr × Ideal (𝓞 K) × 𝓞 K := (rQ ρ, idl (fQ ρ), kQ ρ)

open Classical in
/-- **The multiplicity of the regrouping** (in place of the companion paper's exact preimage count):
the rows with a given image `(r, 𝔣′, k′)` are determined by `(V, b, T, T₂)`, with `V ⊆ r` and
`b, T, T₂ ⊆ f′`, so there are at most `2^{|r|}·8^{|f′|}` of them. -/
theorem card_fiber_phiQ_le {U0 : Finset Pr} {β H L S F : ℝ} {s : Finset RowQ}
    (hs : s ⊆ rowsQ U0 β H L S F) (ρ0 : RowQ) :
    (s.filter fun ρ => phiQ ρ = phiQ ρ0).card ≤ 2 ^ (rQ ρ0).card * 8 ^ (fQ ρ0).card := by
  set ψ : RowQ → Finset Pr × Finset Pr × Finset Pr × Finset Pr :=
    fun ρ => (ρ.1.2.2, ρ.1.1, ρ.1.2.1, ρ.2.1.2.1) with hψ
  have hfib : ∀ ρ ∈ s.filter (fun ρ => phiQ ρ = phiQ ρ0),
      ρ ∈ rowsQ U0 β H L S F ∧ rQ ρ = rQ ρ0 ∧ fQ ρ = fQ ρ0 ∧ kQ ρ = kQ ρ0 := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    have h := hρ.2
    unfold phiQ at h
    simp only [Prod.mk.injEq] at h
    refine ⟨hs hρ.1, h.1, ?_, h.2.2⟩
    rw [← primeSet_idl (fQ ρ), h.2.1, primeSet_idl]
  have hmaps : ∀ ρ ∈ s.filter (fun ρ => phiQ ρ = phiQ ρ0),
      ψ ρ ∈ (rQ ρ0).powerset ×ˢ ((fQ ρ0).powerset ×ˢ ((fQ ρ0).powerset ×ˢ (fQ ρ0).powerset)) := by
    intro ρ hρ
    obtain ⟨-, hr, hf, -⟩ := hfib ρ hρ
    simp only [hψ, Finset.mem_product, Finset.mem_powerset]
    rw [← hr, ← hf]
    unfold rQ fQ
    refine ⟨Finset.subset_union_left, ?_, ?_, ?_⟩
    · exact Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
    · exact Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)
    · exact Finset.subset_union_right.trans Finset.subset_union_left
  have hinj : Set.InjOn ψ (s.filter (fun ρ => phiQ ρ = phiQ ρ0) : Set RowQ) := by
    intro ρ hρ ρ' hρ' he
    obtain ⟨hm, hr, hf, hk⟩ := hfib ρ hρ
    obtain ⟨hm', hr', hf', hk'⟩ := hfib ρ' hρ'
    simp only [hψ, Prod.mk.injEq] at he
    obtain ⟨hV, hb, hT, hT2⟩ := he
    obtain ⟨-, -, -, h4, hx⟩ := rowsQ_disjoint hm
    obtain ⟨-, -, -, h4', hx'⟩ := rowsQ_disjoint hm'
    -- `b₂ = r ∖ V`
    have hVb2 : ∀ {σ : RowQ}, σ ∈ rowsQ U0 β H L S F → rQ σ \ σ.1.2.2 = σ.2.1.1 := by
      intro σ hσ
      obtain ⟨-, -, -, -, hxσ⟩ := rowsQ_disjoint hσ
      unfold rQ
      refine Finset.union_sdiff_cancel_left
        (Finset.disjoint_of_subset_left Finset.subset_union_right
          (Finset.disjoint_of_subset_right
            (Finset.subset_union_left.trans Finset.subset_union_left) hxσ))
    -- `V₂ = f′ ∖ (b ∪ T ∪ T₂)`
    have hV2 : ∀ {σ : RowQ}, σ ∈ rowsQ U0 β H L S F →
        fQ σ \ (σ.1.1 ∪ σ.1.2.1 ∪ σ.2.1.2.1) = σ.2.1.2.2 := by
      intro σ hσ
      obtain ⟨-, -, -, h4σ, hxσ⟩ := rowsQ_disjoint hσ
      unfold fQ
      refine Finset.union_sdiff_cancel_left ?_
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_left Finset.subset_union_left
        (Finset.disjoint_of_subset_right Finset.subset_union_right hxσ),
        Finset.disjoint_of_subset_left Finset.subset_union_right h4σ⟩
    have eb2 : ρ.2.1.1 = ρ'.2.1.1 := by
      rw [← hVb2 hm, ← hVb2 hm', hr, hr', hV]
    have eV2 : ρ.2.1.2.2 = ρ'.2.1.2.2 := by
      rw [← hV2 hm, ← hV2 hm', hf, hf', hb, hT, hT2]
    have eμ : ρ.2.2 = ρ'.2.2 := by
      have hk2 : kQ ρ = kQ ρ' := hk.trans hk'.symm
      unfold kQ at hk2
      rw [hT, hT2] at hk2
      exact mul_left_cancel₀ (mul_ne_zero (eS_ne_zero _) (eS_ne_zero _)) hk2
    obtain ⟨⟨b, T, V⟩, ⟨b2, T2, V2⟩, μ⟩ := ρ
    obtain ⟨⟨b', T', V'⟩, ⟨b2', T2', V2'⟩, μ'⟩ := ρ'
    simp only at hV hb hT hT2 eb2 eV2 eμ
    subst hV hb hT hT2 eb2 eV2 eμ
    rfl
  calc (s.filter fun ρ => phiQ ρ = phiQ ρ0).card
      ≤ ((rQ ρ0).powerset ×ˢ ((fQ ρ0).powerset ×ˢ ((fQ ρ0).powerset ×ˢ (fQ ρ0).powerset))).card :=
        Finset.card_le_card_of_injOn ψ hmaps hinj
    _ = 2 ^ (rQ ρ0).card * 8 ^ (fQ ρ0).card := by
        simp only [Finset.card_product, Finset.card_powerset]
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
        ring

open Classical in
/-- **The sum over the rows of a block by multiplicity**: for `G ≥ 0`,
`Σ_ρ G(r, f′, k′) ≤ B·Σ_{r ∈ Rs} Σ_{f ∈ Fs} Σ_{k ∈ Tk} G(r, f, k)` when `2^{|r|}8^{|f′|} ≤ B`. -/
theorem sum_phiQ_le {U0 : Finset Pr} {β H L S F : ℝ} {s : Finset RowQ}
    (hs : s ⊆ rowsQ U0 β H L S F) (G : Finset Pr × Ideal (𝓞 K) × 𝓞 K → ℝ) (hG : ∀ y, 0 ≤ G y)
    {Bm : ℝ} (hBm : ∀ ρ ∈ s, (2 : ℝ) ^ (rQ ρ).card * 8 ^ (fQ ρ).card ≤ Bm) :
    ∑ ρ ∈ s, G (phiQ ρ) ≤ Bm * ∑ r ∈ s.image rQ, ∑ f ∈ s.image (fun ρ => idl (fQ ρ)),
      ∑ k ∈ s.image kQ, G (r, f, k) := by
  have hBm0 : ∀ ρ ∈ s, 0 ≤ Bm := fun ρ hρ => le_trans (by positivity) (hBm ρ hρ)
  rw [Finset.sum_comp]
  have hsub : s.image phiQ ⊆ s.image rQ ×ˢ (s.image (fun ρ => idl (fQ ρ)) ×ˢ s.image kQ) := by
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hy
    simp only [phiQ, Finset.mem_product, Finset.mem_image]
    exact ⟨⟨ρ, hρ, rfl⟩, ⟨ρ, hρ, rfl⟩, ⟨ρ, hρ, rfl⟩⟩
  calc ∑ y ∈ s.image phiQ, (s.filter fun ρ => phiQ ρ = y).card • G y
      ≤ ∑ y ∈ s.image phiQ, Bm * G y := by
        refine Finset.sum_le_sum fun y hy => ?_
        obtain ⟨ρ0, hρ0, rfl⟩ := Finset.mem_image.1 hy
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hG _)
        refine le_trans ?_ (hBm ρ0 hρ0)
        exact_mod_cast card_fiber_phiQ_le hs ρ0
    _ = Bm * ∑ y ∈ s.image phiQ, G y := by rw [Finset.mul_sum]
    _ ≤ Bm * ∑ y ∈ s.image rQ ×ˢ (s.image (fun ρ => idl (fQ ρ)) ×ˢ s.image kQ), G y := by
        rcases s.eq_empty_or_nonempty with he | ⟨ρ1, hρ1⟩
        · subst he; simp
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => hG y) (hBm0 ρ1 hρ1)
    _ = _ := by
        rw [Finset.sum_product]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_product]


/-! ### The child mean squares -/

/-- **The transfer estimate's hypothesis on the child mean squares** (`TransferEstimate`'s inner
hypothesis, verbatim): the row sums at `𝓗′, X′, F′ ≥ 1` with `𝓗′ ≤ 𝓗L/(ΣF)`, `𝓗′/(X′F′) ≤ 𝓗/Σ` and
`X′F′ ≤ L`, for test functions supported in `[α/16, 4β]` with their first `m` derivatives bounded by
`1`, are at most `M·(X′F′)²`. -/
def ChildBound (α β : ℝ) (m : ℕ) (Hh L S F M : ℝ) : Prop :=
  ∀ Hh' X' F' : ℝ, 1 ≤ Hh' → 1 ≤ X' → 1 ≤ F' → Hh' ≤ Hh * L / (S * F) →
    Hh' / (X' * F') ≤ Hh / S → X' * F' ≤ L →
    ∀ ξ' : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ U : ℝ → ℂ, ContDiff ℝ ∞ U →
      (∀ x, x < α / 16 ∨ 4 * β < x → U x = 0) →
      (∀ i ≤ m, ∀ x, ‖iteratedDeriv i U x‖ ≤ 1) →
    ∀ (Fs' : Finset (Ideal (𝓞 K))) (T' : Finset (𝓞 K)),
      (∀ f ∈ Fs', (absNorm f).Coprime 6 ∧ Squarefree f ∧ F' ≤ (absNorm f : ℝ) ∧
        (absNorm f : ℝ) < 2 * F') →
      (∀ k ∈ T', k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh') →
      rowE ξ' U X' Fs' T' ≤ M * (X' * F') ^ 2

theorem colSum_const_mul (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (c : ℂ) (W : ℝ → ℂ)
    (X : ℝ) (R : Ideal (𝓞 K)) (k f : 𝓞 K) :
    colSum ξ (fun x => c * W x) X R k f = c * colSum ξ W X R k f := by
  unfold colSum
  rw [← tsum_mul_left]
  congr 1
  funext I
  ring

theorem rowE_const_mul (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (c : ℂ) (W : ℝ → ℂ) (X : ℝ)
    (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)) :
    rowE ξ (fun x => c * W x) X Fs T = ‖c‖ ^ 2 * rowE ξ W X Fs T := by
  unfold rowE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [colSum_const_mul, norm_mul, mul_pow]

/-- **The child hypothesis for test functions with derivatives bounded by `N`**: the row sums are at
most `M·N²·(X′F′)²`. -/
theorem ChildBound.scaled {α β : ℝ} {m : ℕ} {Hh L S F M : ℝ} (hM : ChildBound α β m Hh L S F M)
    {Hh' X' F' : ℝ} (h1 : 1 ≤ Hh') (h2 : 1 ≤ X') (h3 : 1 ≤ F') (h4 : Hh' ≤ Hh * L / (S * F))
    (h5 : Hh' / (X' * F') ≤ Hh / S) (h6 : X' * F' ≤ L)
    (ξ' : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ} (hU : ContDiff ℝ ∞ U)
    (hUs : ∀ x, x < α / 16 ∨ 4 * β < x → U x = 0) {N : ℝ}
    (hN : ∀ i ≤ m, ∀ x, ‖iteratedDeriv i U x‖ ≤ N) (Fs' : Finset (Ideal (𝓞 K)))
    (T' : Finset (𝓞 K))
    (hFs' : ∀ f ∈ Fs', (absNorm f).Coprime 6 ∧ Squarefree f ∧ F' ≤ (absNorm f : ℝ) ∧
      (absNorm f : ℝ) < 2 * F')
    (hT' : ∀ k ∈ T', k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh') :
    rowE ξ' U X' Fs' T' ≤ M * N ^ 2 * (X' * F') ^ 2 := by
  have hU0 : ∀ x, ‖U x‖ ≤ N := fun x => by
    have := hN 0 (Nat.zero_le _) x; rwa [iteratedDeriv_zero] at this
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hU0 0)
  rcases hN0.eq_or_lt with h0 | hpos
  · -- `N = 0`: the test function vanishes
    have hz : U = fun x => (0 : ℂ) * U x := by
      funext x
      have := hU0 x
      rw [← h0, norm_le_zero_iff] at this
      rw [this, mul_zero]
    rw [hz, rowE_const_mul, norm_zero, ← h0]
    simp
  · set U1 : ℝ → ℂ := fun x => ((N⁻¹ : ℝ) : ℂ) * U x with hU1
    have hU1d : ∀ i ≤ m, ∀ x, ‖iteratedDeriv i U1 x‖ ≤ 1 := by
      intro i hi x
      rw [hU1, iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
      calc N⁻¹ * ‖iteratedDeriv i U x‖ ≤ N⁻¹ * N :=
            mul_le_mul_of_nonneg_left (hN i hi x) (inv_nonneg.2 hpos.le)
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    have hU1s : ∀ x, x < α / 16 ∨ 4 * β < x → U1 x = 0 := fun x hx => by
      rw [hU1]; simp only [hUs x hx, mul_zero]
    have hb := hM Hh' X' F' h1 h2 h3 h4 h5 h6 ξ' U1 (contDiff_const.mul hU) hU1s hU1d Fs' T'
      hFs' hT'
    have hUe : U = fun x => (N : ℂ) * U1 x := by
      funext x
      rw [hU1, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one,
        one_mul]
    rw [hUe, rowE_const_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    calc N ^ 2 * rowE ξ' U1 X' Fs' T' ≤ N ^ 2 * (M * (X' * F') ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = M * N ^ 2 * (X' * F') ^ 2 := by ring

/-- The constant of the counting bound for the short children, `98(2κ+5)³·16β²·4β`. -/
def Ctriv (β : ℝ) : ℝ := 98 * (2 * kappa + 5) ^ 3 * (16 * β ^ 2) * (4 * β)

theorem Ctriv_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ Ctriv β := by
  have := kappa_pos; unfold Ctriv; positivity

/-- **One child of the regrouping** (the companion paper's application of the transfer
hypothesis after Lemma 4.4): at the scale `X′ = L/(RF′N(S))` with rows of norm in
`[N(S)F′, 2N(S)F′)` and `N(k) ≤ 𝓗L/(ΣFR²)`, the row sum is at most `(M + C_triv)·N²·(L/R)²`. Long
children (`X′ ≥ 1`) go to the hypothesis; short ones are counted (`rowE_le_count`). -/
theorem child_rowE_le {α β : ℝ} (hβ : 0 ≤ β) {m : ℕ} {Hh L S F M : ℝ}
    (hM : ChildBound α β m Hh L S F M) (hM0 : 0 ≤ M) (hHS : Hh ≤ S) (hF : 1 ≤ F) (hL : 0 < L)
    (hH : 0 < Hh) {R Fp nS : ℝ} (hR : 1 ≤ R) (hFp : 1 ≤ Fp) (hRF : R * Fp ≤ 2 * β * L)
    (hnS1 : 1 ≤ nS) (hnS : nS < 2 * R) (ξ' : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ}
    (hU : ContDiff ℝ ∞ U) (hUs : ∀ x, x < α / 16 ∨ 4 * β < x → U x = 0) {N : ℝ}
    (hN : ∀ i ≤ m, ∀ x, ‖iteratedDeriv i U x‖ ≤ N) (Fs' : Finset (Ideal (𝓞 K)))
    (T' : Finset (𝓞 K))
    (hFs' : ∀ f ∈ Fs', (absNorm f).Coprime 6 ∧ Squarefree f ∧ nS * Fp ≤ (absNorm f : ℝ) ∧
      (absNorm f : ℝ) < 2 * (nS * Fp))
    (hT' : ∀ k ∈ T', k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh * L / (S * F * R ^ 2)) :
    rowE ξ' U (L / (R * Fp) / nS) Fs' T' ≤ (M + Ctriv β) * N ^ 2 * (L / R) ^ 2 := by
  have hU0 : ∀ x, ‖U x‖ ≤ N := fun x => by
    have := hN 0 (Nat.zero_le _) x; rwa [iteratedDeriv_zero] at this
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hU0 0)
  have hR0 : 0 < R := by linarith
  have hFp0 : 0 < Fp := by linarith
  have hnS0 : 0 < nS := by linarith
  have hS0 : 0 < S := lt_of_lt_of_le hH hHS
  have hF0 : 0 < F := by linarith
  have hCt := Ctriv_nonneg hβ
  have hRHS : 0 ≤ (M + Ctriv β) * N ^ 2 * (L / R) ^ 2 := by positivity
  -- no rows `k`: nothing to bound
  rcases T'.eq_empty_or_nonempty with hTe | ⟨k0, hk0⟩
  · rw [hTe]; unfold rowE; simpa using hRHS
  set Hh' := Hh * L / (S * F * R ^ 2) with hHh'
  have hH1 : 1 ≤ Hh' := (one_le_absNorm_span (hT' k0 hk0).1).trans (hT' k0 hk0).2
  set X' := L / (R * Fp) / nS with hX'
  have hX0 : 0 < X' := by positivity
  have hF1 : 1 ≤ nS * Fp := one_le_mul_of_one_le_of_one_le hnS1 hFp
  have hXF : X' * (nS * Fp) = L / R := by rw [hX']; field_simp
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  by_cases hX1 : 1 ≤ X'
  · -- a long child: the hypothesis
    have h4 : Hh' ≤ Hh * L / (S * F) := by
      rw [hHh']
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (le_mul_of_one_le_right (by positivity) hR2)
    have h5 : Hh' / (X' * (nS * Fp)) ≤ Hh / S := by
      have hFR : 1 ≤ F * R := one_le_mul_of_one_le_of_one_le hF hR
      have e : Hh * L / (S * F * R ^ 2) / (L / R) = Hh / S / (F * R) := by field_simp
      rw [hXF, hHh', e]
      exact div_le_self (by positivity) hFR
    have h6 : X' * (nS * Fp) ≤ L := by rw [hXF]; exact div_le_self hL.le hR
    have hb := hM.scaled hH1 hX1 hF1 h4 h5 h6 ξ' hU hUs hN Fs' T' hFs' (fun k hk => hT' k hk)
    rw [hXF] at hb
    calc rowE ξ' U X' Fs' T' ≤ M * N ^ 2 * (L / R) ^ 2 := hb
      _ ≤ (M + Ctriv β) * N ^ 2 * (L / R) ^ 2 := by gcongr; linarith
  · -- a short child: counting
    rw [not_le] at hX1
    have hW : ∀ x, 4 * β < x → U x = 0 := fun x hx => hUs x (Or.inr hx)
    rcases lt_or_ge (4 * β * X') 1 with h4 | h4
    · rw [rowE_eq_zero_of_lt ξ' hW hX0 h4]; exact hRHS
    have hc := rowE_le_count ξ' hW hU0 hH1 hF1 hX0 h4 hFs' (fun k hk => hT' k hk)
    have hX2 : (4 * β * X') ^ 2 ≤ 16 * β ^ 2 := by
      have : 4 * β * X' ≤ 4 * β := mul_le_of_le_one_right (by positivity) hX1.le
      nlinarith
    have hFH : nS * Fp * Hh' ≤ 4 * β * (L / R) ^ 2 := by
      have hFp' : Fp ≤ 2 * β * L / R := by rw [le_div_iff₀ hR0]; linarith
      have hFS : Hh / (S * F) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      calc nS * Fp * Hh' ≤ (2 * R) * (2 * β * L / R) * Hh' :=
            mul_le_mul_of_nonneg_right (mul_le_mul hnS.le hFp' hFp0.le (by positivity))
              (by positivity)
        _ = 4 * β * (L / R) ^ 2 * (Hh / (S * F)) := by rw [hHh']; field_simp; ring
        _ ≤ 4 * β * (L / R) ^ 2 * 1 := mul_le_mul_of_nonneg_left hFS (by positivity)
        _ = 4 * β * (L / R) ^ 2 := mul_one _
    have hk := kappa_pos
    calc rowE ξ' U X' Fs' T'
        ≤ 98 * (2 * kappa + 5) ^ 3 * (4 * β * X') ^ 2 * N ^ 2 * (nS * Fp) * Hh' := hc
      _ = 98 * (2 * kappa + 5) ^ 3 * (4 * β * X') ^ 2 * N ^ 2 * (nS * Fp * Hh') := by ring
      _ ≤ 98 * (2 * kappa + 5) ^ 3 * (16 * β ^ 2) * N ^ 2 * (4 * β * (L / R) ^ 2) := by
          gcongr
      _ = Ctriv β * N ^ 2 * (L / R) ^ 2 := by unfold Ctriv; ring
      _ ≤ (M + Ctriv β) * N ^ 2 * (L / R) ^ 2 := by gcongr; linarith


/-! ### The column mean square of a block -/

open Classical in
/-- The rows of the block `p = (i, j)`: `⌊log₂ N(r)⌋ = i` and `⌊log₂ N(f′)⌋ = j`. -/
def blkQ (U0 : Finset Pr) (β H L S F : ℝ) (p : ℕ × ℕ) : Finset RowQ :=
  (rowsQ U0 β H L S F).filter fun ρ => (lvl (rQ ρ), lvl (fQ ρ)) = p

open Classical in
theorem mem_blkQ {U0 : Finset Pr} {β H L S F : ℝ} {p : ℕ × ℕ} {ρ : RowQ}
    (h : ρ ∈ blkQ U0 β H L S F p) :
    ρ ∈ rowsQ U0 β H L S F ∧ (2 : ℝ) ^ p.1 ≤ nI (rQ ρ) ∧ nI (rQ ρ) < 2 * (2 : ℝ) ^ p.1 ∧
      (2 : ℝ) ^ p.2 ≤ nI (fQ ρ) ∧ nI (fQ ρ) < 2 * (2 : ℝ) ^ p.2 := by
  unfold blkQ at h
  rw [Finset.mem_filter] at h
  obtain ⟨hρ, hp⟩ := h
  have h1 := lvl_bounds (rQ ρ)
  have h2 := lvl_bounds (fQ ρ)
  rw [← hp]
  exact ⟨hρ, h1.1, h1.2, h2.1, h2.2⟩

theorem absNorm_kQ (ρ : RowQ) :
    (absNorm (span {kQ ρ}) : ℝ) = nI ρ.1.2.1 * nI ρ.2.1.2.1 * (absNorm (span {ρ.2.2}) : ℝ) := by
  unfold kQ
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    map_mul, map_mul]
  push_cast
  rw [show eS ρ.1.2.1 = ∏ P ∈ ρ.1.2.1, πP P from rfl,
    show eS ρ.2.1.2.1 = ∏ P ∈ ρ.2.1.2.1, πP P from rfl, absNorm_span_prod_πP,
    absNorm_span_prod_πP]

open Classical in
/-- The rows `k′` of a block are nonzero of norm at most `𝓗L/(ΣFR²)`, `R = 2^i`. -/
theorem kQ_bounds {U0 : Finset Pr} {β H L S F : ℝ} (hS : 0 < S) (hF : 0 < F) {p : ℕ × ℕ}
    {ρ : RowQ} (h : ρ ∈ blkQ U0 β H L S F p) :
    kQ ρ ≠ 0 ∧ (absNorm (span {kQ ρ}) : ℝ) ≤ H * L / (S * F * ((2 : ℝ) ^ p.1) ^ 2) := by
  obtain ⟨hρ, hR1, -, -, -⟩ := mem_blkQ h
  obtain ⟨⟨-, -, hμ⟩, hg⟩ := mem_rowsQ.1 hρ
  have hμ0 : ρ.2.2 ≠ 0 := Finset.ne_of_mem_erase hμ
  refine ⟨mul_ne_zero (mul_ne_zero (eS_ne_zero _) (eS_ne_zero _)) hμ0, ?_⟩
  have h3 := hg.2.2
  rw [absNorm_kQ]
  have hr := nI_rQ hρ
  have hR0 : (0 : ℝ) < (2 : ℝ) ^ p.1 := by positivity
  have hRr : ((2 : ℝ) ^ p.1) ^ 2 ≤ (nI ρ.2.1.1 * nI ρ.1.2.2) ^ 2 := by
    rw [mul_comm (nI ρ.2.1.1), ← hr]
    exact pow_le_pow_left₀ hR0.le hR1 2
  have hSF : 0 < S * F := mul_pos hS hF
  rw [le_div_iff₀ hSF] at h3
  rw [le_div_iff₀ (by positivity)]
  have hN0 : 0 ≤ nI ρ.1.2.1 * nI ρ.2.1.2.1 * (absNorm (span {ρ.2.2}) : ℝ) := by
    have := nI_pos ρ.1.2.1; have := nI_pos ρ.2.1.2.1; positivity
  calc nI ρ.1.2.1 * nI ρ.2.1.2.1 * (absNorm (span {ρ.2.2}) : ℝ) * (S * F * ((2 : ℝ) ^ p.1) ^ 2)
      ≤ nI ρ.1.2.1 * nI ρ.2.1.2.1 * (absNorm (span {ρ.2.2}) : ℝ) *
          (S * F * (nI ρ.2.1.1 * nI ρ.1.2.2) ^ 2) := by gcongr
    _ = (absNorm (span {ρ.2.2}) : ℝ) * nI ρ.1.2.1 * nI ρ.2.1.2.1 *
          (nI ρ.2.1.1 * nI ρ.1.2.2) ^ 2 * (S * F) := by ring
    _ ≤ H * L := h3

open Classical in
/-- `R·F′ ≤ 2βL` for a nonempty block. -/
theorem blk_RF_le {U0 : Finset Pr} {β H L S F : ℝ} {p : ℕ × ℕ} {ρ : RowQ}
    (h : ρ ∈ blkQ U0 β H L S F p) : (2 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2 ≤ 2 * β * L := by
  obtain ⟨hρ, hR1, -, hF1, -⟩ := mem_blkQ h
  exact le_trans (mul_le_mul hR1 hF1 (by positivity) (nI_pos _).le) (nI_rQ_fQ_le hρ)

open Classical in
/-- **The column mean square of a block** (the companion paper's bound of the columns in the proof of
Lemma 7.3): for a test function `U` supported in `[α/16, 4β]` with its first `m` derivatives
bounded by `N`, the block's rows satisfy
`Σ_ρ |Σ_n aQ(n)·U(x_n)|² ≤ B·Σ_r 4^{|r|}·(M + C_triv)·N²·(L/R)²`: each row's sum is an excluded column
sum (`sum_aQ_eq_colSum`), the rows are counted by `(r, f′, k′)` with multiplicity at most
`B ≥ 2^{|r|}8^{|f′|}` (`sum_phiQ_le`), the exclusion is removed by Lemma 4.4
(`colSum_excl_meanSquare_le`) and each child is bounded by `child_rowE_le`. -/
theorem blockQ_colMS {α β : ℝ} (hβ : 0 ≤ β) {m : ℕ} {Hh L S F M : ℝ}
    (hM : ChildBound α β m Hh L S F M) (hM0 : 0 ≤ M) (hHS : Hh ≤ S) (hF : 1 ≤ F) (hL : 0 < L)
    (hH : 0 < Hh) {U0 : Finset Pr} (hU0 : primesLe (4 * β * L) ⊆ U0)
    (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (p : ℕ × ℕ) {Bm : ℝ}
    (hBm : ∀ ρ ∈ blkQ U0 β Hh L S F p, (2 : ℝ) ^ (rQ ρ).card * 8 ^ (fQ ρ).card ≤ Bm)
    {U : ℝ → ℂ} (hU : ContDiff ℝ ∞ U) (hUs : ∀ x, x < α / 16 ∨ 4 * β < x → U x = 0) {N : ℝ}
    (hN : ∀ i ≤ m, ∀ x, ‖iteratedDeriv i U x‖ ≤ N) :
    ∑ ρ ∈ blkQ U0 β Hh L S F p,
        ‖∑ n ∈ U0.powerset, aQ U0 ξ ρ n * U (xQ L ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) n)‖ ^ 2 ≤
      Bm * ((∑ r ∈ (blkQ U0 β Hh L S F p).image rQ, (4 : ℝ) ^ r.card) *
        ((M + Ctriv β) * N ^ 2 * (L / (2 : ℝ) ^ p.1) ^ 2)) := by
  set blk := blkQ U0 β Hh L S F p with hblk
  set R : ℝ := (2 : ℝ) ^ p.1 with hRdef
  set Fp : ℝ := (2 : ℝ) ^ p.2 with hFpdef
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hFp1 : 1 ≤ Fp := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by linarith
  have hFp0 : 0 < Fp := by linarith
  have hS0 : 0 < S := lt_of_lt_of_le hH hHS
  have hF0 : 0 < F := by linarith
  set X := L / (R * Fp) with hXdef
  have hX0 : 0 < X := by positivity
  have hXL : X ≤ L := div_le_self hL.le (one_le_mul_of_one_le_of_one_le hR1 hFp1)
  have hU0' : primesLe (4 * β * X) ⊆ U0 :=
    (primesLe_mono (mul_le_mul_of_nonneg_left hXL (by positivity))).trans hU0
  set Ub : ℝ → ℂ := fun x => conj (U x) with hUb
  have hW : ∀ x, 4 * β < x → U x = 0 := fun x hx => hUs x (Or.inr hx)
  have hWb : ∀ x, 4 * β < x → Ub x = 0 := fun x hx => by simp only [hUb, hW x hx, map_zero]
  have hsub : blk ⊆ rowsQ U0 β Hh L S F := Finset.filter_subset _ _
  set G : Finset Pr × Ideal (𝓞 K) × 𝓞 K → ℝ :=
    fun y => ‖colSum ξ Ub X (idl y.1) y.2.2 (pgen y.2.1)‖ ^ 2 with hG
  -- step 1: each row's sum is an excluded column sum
  have h1 : ∀ ρ ∈ blk, ‖∑ n ∈ U0.powerset, aQ U0 ξ ρ n * U (xQ L R Fp n)‖ ^ 2 = G (phiQ ρ) := by
    intro ρ hρ
    rw [sum_aQ_eq_colSum ξ hW hL hR0 hFp0 hU0' (hsub hρ), RCLike.norm_conj]
    rfl
  rw [Finset.sum_congr rfl h1]
  -- step 2: the multiplicity
  refine (sum_phiQ_le hsub G (fun y => sq_nonneg _) hBm).trans ?_
  rcases blk.eq_empty_or_nonempty with hbe | ⟨ρ1, hρ1⟩
  · rw [hbe]; simp
  have hBm0 : 0 ≤ Bm := le_trans (by positivity) (hBm ρ1 hρ1)
  refine mul_le_mul_of_nonneg_left ?_ hBm0
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r hr => ?_
  obtain ⟨ρr, hρr, rfl⟩ := Finset.mem_image.1 hr
  -- step 3: Lemma 4.4
  have hFs : ∀ f ∈ blk.image (fun ρ => idl (fQ ρ)), (absNorm f).Coprime 6 ∧ Squarefree f := by
    intro f hf
    obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨idl_coprime6 _, idl_squarefree _⟩
  have h44 := colSum_excl_meanSquare_le ξ hWb hX0 (idl_coprime6 (rQ ρr)) (idl_squarefree (rQ ρr))
    (blk.image (fun ρ => idl (fQ ρ))) hFs (blk.image kQ)
  rw [primeSet_idl] at h44
  refine le_trans (le_of_eq_of_le rfl h44) ?_
  -- step 4: the children
  have hchild : ∀ S' ∈ (rQ ρr).powerset,
      ∑ f ∈ ((blk.image fun ρ => idl (fQ ρ)).filter (IsRelPrime (∏ P ∈ S', P.1))).image
          ((∏ P ∈ S', P.1) * ·),
        ∑ k ∈ blk.image kQ, ‖colSum ξ Ub (X / (absNorm (∏ P ∈ S', P.1) : ℝ)) 1 k (pgen f)‖ ^ 2 ≤
      (M + Ctriv β) * N ^ 2 * (L / R) ^ 2 := by
    intro S' hS'
    have hS'r := Finset.mem_powerset.1 hS'
    have hnS1 : 1 ≤ nI S' := one_le_nI S'
    have hnS : nI S' < 2 * R := by
      obtain ⟨-, -, hr2, -, -⟩ := mem_blkQ hρr
      refine lt_of_le_of_lt ?_ hr2
      unfold nI; exact_mod_cast absNorm_idl_mono hS'r
    have hXe : X / (absNorm (∏ P ∈ S', P.1) : ℝ) = L / (R * Fp) / nI S' := rfl
    rw [hXe]
    refine child_rowE_le hβ hM hM0 hHS hF hL hH hR1 hFp1 (blk_RF_le hρr) hnS1 hnS ξ
      (contDiff_conj_comp hU) (fun x hx => by simp only [hUs x hx, map_zero])
      (fun i hi x => by rw [norm_iteratedDeriv_conj_comp]; exact hN i hi x) _ _ ?_ ?_
    · intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hf
      rw [Finset.mem_filter] at hg
      obtain ⟨hg1, hrel⟩ := hg
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hg1
      obtain ⟨-, -, -, hf1, hf2⟩ := mem_blkQ hρ
      have hn : (absNorm ((∏ P ∈ S', P.1) * idl (fQ ρ)) : ℝ) = nI S' * nI (fQ ρ) := by
        rw [map_mul]; push_cast; rfl
      refine ⟨coprime6_mul (idl_coprime6 S') (idl_coprime6 _),
        squarefree_mul_of (idl_squarefree S') (idl_squarefree _) hrel, ?_, ?_⟩
      · rw [hn]; exact mul_le_mul_of_nonneg_left hf1 (by linarith)
      · rw [hn]
        calc nI S' * nI (fQ ρ) < nI S' * (2 * Fp) :=
              mul_lt_mul_of_pos_left hf2 (by linarith)
          _ = 2 * (nI S' * Fp) := by ring
    · intro k hk
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hk
      exact kQ_bounds hS0 hF0 hρ
  calc (2 : ℝ) ^ (rQ ρr).card * ∑ S' ∈ (rQ ρr).powerset,
        ∑ f ∈ ((blk.image fun ρ => idl (fQ ρ)).filter (IsRelPrime (∏ P ∈ S', P.1))).image
            ((∏ P ∈ S', P.1) * ·),
          ∑ k ∈ blk.image kQ, ‖colSum ξ Ub (X / (absNorm (∏ P ∈ S', P.1) : ℝ)) 1 k (pgen f)‖ ^ 2
      ≤ (2 : ℝ) ^ (rQ ρr).card * ∑ _S' ∈ (rQ ρr).powerset, (M + Ctriv β) * N ^ 2 * (L / R) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hchild) (by positivity)
    _ = (4 : ℝ) ^ (rQ ρr).card * ((M + Ctriv β) * N ^ 2 * (L / R) ^ 2) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, ← mul_assoc]
        push_cast
        rw [← mul_pow]
        norm_num

end Eis

end

#print axioms Eis.colQ_eq
#print axioms Eis.eS_fQ
#print axioms Eis.colB_subset_colRange
#print axioms Eis.disjoint_V_of_mem_colB
#print axioms Eis.sum_aQ_eq_colB
#print axioms Eis.sum_rQ_eq_colB
#print axioms Eis.sum_aQ_eq_colSum
#print axioms Eis.card_fiber_phiQ_le
#print axioms Eis.sum_phiQ_le
#print axioms Eis.colSum_const_mul
#print axioms Eis.rowE_const_mul
#print axioms Eis.ChildBound.scaled
#print axioms Eis.Ctriv_nonneg
#print axioms Eis.child_rowE_le
#print axioms Eis.mem_blkQ
#print axioms Eis.absNorm_kQ
#print axioms Eis.kQ_bounds
#print axioms Eis.blk_RF_le
#print axioms Eis.blockQ_colMS
