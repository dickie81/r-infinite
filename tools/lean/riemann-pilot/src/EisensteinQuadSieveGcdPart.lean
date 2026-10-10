import EisensteinQuadSieveMainBound

/-! # The quadratic large sieve, part 7b: the bound for one gcd part (round 356)

S5e of round 312's plan, the second piece of S5e-7: the part of the expanded norm of Heath-Brown's
`B(M, N, K)` from the pairs of columns with greatest common divisor `G` (round 346's `gcdPart`) is
bounded through the explicit formulas of rounds 350–354 and the bilinear bounds of rounds 352
and 355. This is Goldmakher and Louvel's Proposition for one `𝔤`, with the norms of the rows left
as hypotheses.

* **The pairs** (`gcdPart_eq_pairs`, with `colG`, `mem_colG`, `inter_eq_iff_disjoint_sdiff`):
  the pairs with greatest common divisor `G` are `(G ∪ B₁, G ∪ B₂)` with `B₁, B₂` disjoint.
* **The pair sum is `Σ_3 − Σ_4`** (`pW_bw_pair`, with `q2_self_mul`, `Phi_re_ofReal`): for the rows
  of `B(M, N, K)`, `S(G ∪ B₁, G ∪ B₂) = Σ_3(G, B₁ ∪ B₂) − Σ_4(G, B₁ ∪ B₂)`.
* **The pair identity for every pair** (`pair_eq_parS`, with `cMain`, `parS`, `pairX`,
  `q2_neg_one_cases`, `norm_q2_neg_one`): `w·(Σ_3 − Σ_4) = h·X_p` with the parity factor
  `h = (1 + ρ_{B₁}(−1)ρ_{B₂}(−1))/2` and round 354's right side `X_p`.
* **The bound** (`gcdPart_bw_le`, with `bilin_pairX`, `sum_colG_le`, `one_le_eulB`): with
  `X_lo ≤ N(B) ≤ X` on the columns, `3R²X²N(G) ≤ 4MK₁`, `K₁ ≤ K ≤ M`, and the norms `Δ_m`, `Δ₃`,
  `Δ₄` of the rows of round 355, of the squarefree rows up to `K₁` and up to `K`,
  `|gcdPart| ≤ w⁻¹·(|c|√M·4^{|G|}Δ_m + 2^{|G|}(2M/√3)C₃(4MK₁/3)^{ε/2}Δ₃/X_lo + C₄Π_GΔ₄)·P·Σ|α|²`.
-/

open Complex MeasureTheory Set NumberField Ideal
open scoped Classical ComplexConjugate

noncomputable section

namespace Eis

/-- The columns containing `G`, with `G` removed. -/
def colG (𝒩 : Finset (Finset Pr)) (G : Finset Pr) : Finset (Finset Pr) :=
  (𝒩.filter (fun A => G ⊆ A)).image (fun A => A \ G)

theorem mem_colG {𝒩 : Finset (Finset Pr)} {G B : Finset Pr} :
    B ∈ colG 𝒩 G ↔ Disjoint G B ∧ G ∪ B ∈ 𝒩 := by
  unfold colG
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [Finset.mem_filter] at hA
    exact ⟨Finset.disjoint_sdiff, by rw [Finset.union_sdiff_of_subset hA.2]; exact hA.1⟩
  · rintro ⟨hd, hB⟩
    refine ⟨G ∪ B, Finset.mem_filter.2 ⟨hB, Finset.subset_union_left⟩, ?_⟩
    rw [Finset.union_sdiff_left]
    exact Finset.sdiff_eq_self_of_disjoint hd.symm

theorem inter_eq_iff_disjoint_sdiff {G A1 A2 : Finset Pr} (h1 : G ⊆ A1) (h2 : G ⊆ A2) :
    A1 ∩ A2 = G ↔ Disjoint (A1 \ G) (A2 \ G) := by
  rw [Finset.disjoint_left, Finset.ext_iff]
  constructor
  · intro h x hx1 hx2
    rw [Finset.mem_sdiff] at hx1 hx2
    exact hx1.2 ((h x).1 (Finset.mem_inter.2 ⟨hx1.1, hx2.1⟩))
  · intro h x
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨hx1, hx2⟩
      by_contra hxG
      exact h (Finset.mem_sdiff.2 ⟨hx1, hxG⟩) (Finset.mem_sdiff.2 ⟨hx2, hxG⟩)
    · intro hx; exact ⟨h1 hx, h2 hx⟩

/-- **A gcd part over disjoint pairs**: the pairs of columns with greatest common divisor `G` are
`(G ∪ B₁, G ∪ B₂)` with `B₁, B₂` disjoint. -/
theorem gcdPart_eq_pairs (w : 𝓞 K → ℝ) (G : Finset Pr) (𝒩 : Finset (Finset Pr))
    (α : Finset Pr → ℂ) :
    gcdPart w G 𝒩 α = ∑ B1 ∈ colG 𝒩 G, ∑ B2 ∈ colG 𝒩 G, if Disjoint B1 B2 then
      α (G ∪ B1) * conj (α (G ∪ B2)) * pW w (G ∪ B1) (G ∪ B2) else 0 := by
  set f : Finset Pr → Finset Pr → ℂ := fun A1 A2 =>
    if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0 with hf
  have hz : ∀ A1 A2, ¬ (G ⊆ A1 ∧ G ⊆ A2) → f A1 A2 = 0 := fun A1 A2 h =>
    ite_eq_right fun h' : A1 ∩ A2 = G =>
      h ⟨h' ▸ Finset.inter_subset_left, h' ▸ Finset.inter_subset_right⟩
  have hinj : Set.InjOn (fun A => A \ G) (𝒩.filter (fun A => G ⊆ A) : Set (Finset Pr)) := by
    intro A1 hA1 A2 hA2 h
    simp only [Finset.coe_filter] at hA1 hA2
    have e1 := Finset.union_sdiff_of_subset hA1.2
    have e2 := Finset.union_sdiff_of_subset hA2.2
    simp only at h
    rw [← e1, ← e2, h]
  unfold gcdPart colG
  rw [Finset.sum_image hinj]
  simp_rw [Finset.sum_image hinj]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun A1 _ => ?_
  rw [Finset.sum_filter]
  by_cases h1 : G ⊆ A1
  · rw [ite_eq_left h1]
    refine Finset.sum_congr rfl fun A2 _ => ?_
    by_cases h2 : G ⊆ A2
    · rw [ite_eq_left h2, Finset.union_sdiff_of_subset h1, Finset.union_sdiff_of_subset h2]
      exact if_congr (inter_eq_iff_disjoint_sdiff h1 h2) rfl rfl
    · rw [ite_eq_right h2]; exact hz A1 A2 fun h => h2 h.2
  · rw [ite_eq_right h1]
    exact Finset.sum_eq_zero fun A2 _ => hz A1 A2 fun h => h1 h.1

theorem q2_self_mul (G : Finset Pr) (m : 𝓞 K) :
    q2 G m * q2 G m = if ∀ Q ∈ G, ¬ πP Q ∣ m then 1 else 0 := by
  rw [q2_mul_q2]
  simp only [Finset.inter_self, Finset.sdiff_self, Finset.union_empty]
  congr 1

theorem Phi_re_ofReal (z : ℂ) : (((Majorant.Phi z).re : ℝ) : ℂ) = Majorant.Phi z :=
  Complex.ext (by simp) (by simp [Majorant.Phi_im])

/-- **The pair sum of `B(M, N, K)` is `Σ_3 − Σ_4`**: for `G`, `B₁`, `B₂` pairwise disjoint,
`S_w(G ∪ B₁, G ∪ B₂) = Σ_3(G, B₁ ∪ B₂) − Σ_4(G, B₁ ∪ B₂)` with `w` the rows of `B(M, N, K)`. -/
theorem pW_bw_pair {M : ℝ} (hM : 0 < M) (Kt : ℝ) {G B1 B2 : Finset Pr} (h1 : Disjoint G B1)
    (h2 : Disjoint G B2) (h12 : Disjoint B1 B2) :
    pW (bw M Kt) (G ∪ B1) (G ∪ B2) = sig3 M G (B1 ∪ B2) - sig4 M Kt G (B1 ∪ B2) := by
  have hb3 : ∀ m : 𝓞 K, ‖(if ∀ Q ∈ G, ¬ πP Q ∣ m then (1 : ℂ) else 0) * q2 (B1 ∪ B2) m‖ ≤ 1 :=
    fun m => by
      rw [norm_mul]
      have := norm_q2_le (B1 ∪ B2) m
      split_ifs <;> simp [this]
  have hb4 : ∀ m : 𝓞 K, ‖(if sqN m ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ m then (1 : ℂ) else 0) *
      q2 (B1 ∪ B2) m‖ ≤ 1 := fun m => by
    rw [norm_mul]
    have := norm_q2_le (B1 ∪ B2) m
    split_ifs <;> simp [this]
  have hs3 := summable_mul_Phi M hM _ hb3
  have hs4 := summable_mul_Phi M hM _ hb4
  have e3 : sig3 M G (B1 ∪ B2) = ∑' m : 𝓞 K, (if ∀ Q ∈ G, ¬ πP Q ∣ m then (1 : ℂ) else 0) *
      q2 (B1 ∪ B2) m * Majorant.Phi (σO m / (Real.sqrt M : ℂ)) := by
    unfold sig3
    refine tsum_congr fun m => ?_
    split_ifs <;> ring
  have e4 : sig4 M Kt G (B1 ∪ B2) = ∑' m : 𝓞 K, (if sqN m ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ m then
      (1 : ℂ) else 0) * q2 (B1 ∪ B2) m * Majorant.Phi (σO m / (Real.sqrt M : ℂ)) := by
    unfold sig4
    refine tsum_congr fun m => ?_
    split_ifs <;> ring
  rw [e3, e4, ← hs3.tsum_sub hs4]
  unfold pW
  refine tsum_congr fun m => ?_
  have hq : q2 (G ∪ B1) m * q2 (G ∪ B2) m =
      (if ∀ Q ∈ G, ¬ πP Q ∣ m then 1 else 0) * q2 (B1 ∪ B2) m := by
    rw [q2_union h1, q2_union h2, q2_union h12, ← q2_self_mul]
    ring
  rw [hq]
  unfold bw
  by_cases hk : Kt < sqN m
  · rw [ite_eq_left hk, Phi_re_ofReal, ite_eq_right (show ¬ (sqN m ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ m)
      from fun h => absurd h.1 (not_le.2 hk))]
    ring
  · rw [ite_eq_right hk]
    by_cases hc : ∀ Q ∈ G, ¬ πP Q ∣ m
    · rw [ite_eq_left hc, ite_eq_left ⟨not_lt.1 hk, hc⟩]; push_cast; ring
    · rw [ite_eq_right hc, ite_eq_right fun h => hc h.2]; push_cast; ring

/-- The constant of the main term, `(2π/√3)·∫_0^∞Φ`. -/
def cMain : ℂ := ((2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), PhiOnR y)

/-- The parity factor `(1 + ρ_{B₁}(−1)ρ_{B₂}(−1))/2`: `1` when `ρ_D(−1) = 1`, else `0`. -/
def parS (B1 B2 : Finset Pr) : ℂ := (1 + q2 B1 (-1) * q2 B2 (-1)) / 2

/-- The pair's term after the explicit formulas. -/
def pairX (M K₁ Kt : ℝ) (G D : Finset Pr) : ℂ :=
  -(cMain * ((Real.sqrt M : ℝ) : ℂ)) * (phiS D * pairMain K₁ Kt G D) + err3 M K₁ G D -
    err4 M Kt G D

theorem q2_neg_one_cases (D : Finset Pr) : q2 D (-1) = 1 ∨ q2 D (-1) = -1 := by
  have h : q2 D (-1) * q2 D (-1) = 1 := by rw [← q2_mul, neg_one_mul, neg_neg, q2_one]
  exact mul_self_eq_one_iff.1 h

theorem norm_q2_neg_one (D : Finset Pr) : ‖q2 D (-1)‖ = 1 := by
  rcases q2_neg_one_cases D with h | h <;> simp [h]

/-- **The pair identity for every pair**: with the parity factor, `w·(Σ_3 − Σ_4) = h·X_p` for
every `D = B₁ ⊔ B₂ ≠ ∅` disjoint from `G`. -/
theorem pair_eq_parS {M K₁ Kt : ℝ} (hM : 0 < M) {G B1 B2 : Finset Pr} (h1 : Disjoint G B1)
    (h2 : Disjoint G B2) (h12 : Disjoint B1 B2) (hD : (B1 ∪ B2).Nonempty)
    (hK₁ : 3 * RΦ ^ 2 * nI (B1 ∪ B2) * nI G ≤ 4 * M * K₁) (hK : K₁ ≤ Kt) :
    (Fintype.card (𝓞 K)ˣ : ℂ) * (sig3 M G (B1 ∪ B2) - sig4 M Kt G (B1 ∪ B2)) =
      parS B1 B2 * pairX M K₁ Kt G (B1 ∪ B2) := by
  have hGD : Disjoint G (B1 ∪ B2) := Finset.disjoint_union_right.2 ⟨h1, h2⟩
  have hq : q2 (B1 ∪ B2) (-1) = q2 B1 (-1) * q2 B2 (-1) := q2_union h12 (-1)
  rcases q2_neg_one_cases (B1 ∪ B2) with h | h
  · have hh : parS B1 B2 = 1 := by unfold parS; rw [← hq, h]; norm_num
    rw [hh, one_mul, pair_eq hM hD hGD h hK₁ hK, pairX, phiS, pairMain, cMain]
    ring
  · have hh : parS B1 B2 = 0 := by unfold parS; rw [← hq, h]; norm_num
    rw [hh, zero_mul, sig3_eq_zero G h, sig4_eq_zero G h, sub_zero, mul_zero]

theorem sum_colG_le (𝒩 : Finset (Finset Pr)) (G : Finset Pr) {f : Finset Pr → ℝ}
    (hf : ∀ A, 0 ≤ f A) : ∑ B ∈ colG 𝒩 G, f (G ∪ B) ≤ ∑ A ∈ 𝒩, f A := by
  have hinj : Set.InjOn (fun A => A \ G) (𝒩.filter (fun A => G ⊆ A) : Set (Finset Pr)) := by
    intro A1 hA1 A2 hA2 h
    simp only [Finset.coe_filter] at hA1 hA2
    have e1 := Finset.union_sdiff_of_subset hA1.2
    have e2 := Finset.union_sdiff_of_subset hA2.2
    simp only at h
    rw [← e1, ← e2, h]
  unfold colG
  rw [Finset.sum_image hinj]
  calc ∑ A ∈ 𝒩.filter (fun A => G ⊆ A), f (G ∪ (A \ G))
      = ∑ A ∈ 𝒩.filter (fun A => G ⊆ A), f A := Finset.sum_congr rfl fun A hA => by
        rw [Finset.union_sdiff_of_subset (Finset.mem_filter.1 hA).2]
    _ ≤ ∑ A ∈ 𝒩, f A := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun A _ _ => hf A

/-- **The three bilinear bounds for `X_p`**: coefficients of norm `r(B)` on a family of columns
disjoint from `G`, of norm at most `X`. -/
theorem bilin_pairX {ε : ℝ} (hε : 0 < ε) :
    ∃ C3 C4 : ℝ, 0 ≤ C3 ∧ 0 ≤ C4 ∧ ∀ (M K₁ Kt X Δm Δ3 Δ4 : ℝ) (G : Finset Pr)
      (𝒞 : Finset (Finset Pr)) (a b : Finset Pr → ℂ) (r : Finset Pr → ℝ), 0 < M → Kt ≤ M →
      0 ≤ Δm → 0 ≤ Δ3 → 0 ≤ Δ4 → FBound (wR (K₁ / nI G) Kt) X Δm → FBound (sqfW K₁) X Δ3 →
      FBound (sqfW Kt) X Δ4 → (∀ B ∈ 𝒞, nI B ≤ X ∧ Disjoint G B) → (∀ B, ‖a B‖ = r B) →
      (∀ B, ‖b B‖ = r B) →
      ‖∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, if Disjoint B1 B2 then a B1 * b B2 * pairX M K₁ Kt G (B1 ∪ B2)
          else 0‖ ≤
        ‖cMain‖ * Real.sqrt M * (4 : ℝ) ^ G.card * Δm * (∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * r B ^ 2) +
        (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 *
          ((Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * Δ3 *
            ∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
              ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * r B ^ 2)) +
        C4 * ((∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Δ4 *
          ∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 *
            r B ^ 2)) := by
  obtain ⟨C3, hC3, h3⟩ := err3_bilin hε
  obtain ⟨C4, hC4, h4⟩ := err4_bilin hε
  refine ⟨C3, C4, hC3, hC4, fun M K₁ Kt X Δm Δ3 Δ4 G 𝒞 a b r hM hKM hm0 h30 h40 hFm hF3 hF4
    h𝒞 ha hb => ?_⟩
  have hX : ∀ B ∈ 𝒞, nI B ≤ X := fun B hB => (h𝒞 B hB).1
  have hG : ∀ B ∈ 𝒞, Disjoint G B := fun B hB => (h𝒞 B hB).2
  -- the sums of squares, with `‖a‖ = ‖b‖ = r`
  have hsq : ∀ (c : Finset Pr → ℝ), (∀ B, 0 ≤ c B) →
      Real.sqrt (∑ B ∈ 𝒞, c B * ‖a B‖ ^ 2) * Real.sqrt (∑ B ∈ 𝒞, c B * ‖b B‖ ^ 2) =
        ∑ B ∈ 𝒞, c B * r B ^ 2 := by
    intro c hc
    simp only [ha, hb]
    exact Real.mul_self_sqrt (Finset.sum_nonneg fun B _ => mul_nonneg (hc B) (sq_nonneg _))
  have hm := main_bilin hm0 hFm 𝒞 hX a b
  have he3 := h3 M K₁ X Δ3 G 𝒞 a b hM h30 hF3 hX
  have he4 := h4 M Kt X Δ4 G 𝒞 a b hM hKM h40 hF4 hX hG
  rw [hsq (fun B => (2 : ℝ) ^ B.card) (fun B => by positivity)] at hm
  have e3 : Real.sqrt (∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
        ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖a B‖ ^ 2)) *
      Real.sqrt (∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
        ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖b B‖ ^ 2)) =
      ∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
        ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * r B ^ 2) := by
    have := hsq (fun B => (2 : ℝ) ^ B.card * ((Real.sqrt (nI B))⁻¹ *
      ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2) (fun B => by positivity)
    simp only [mul_assoc] at this ⊢
    exact this
  have e4 : Real.sqrt (∑ B ∈ 𝒞, (2 : ℝ) ^ B.card *
        ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖a B‖ ^ 2)) *
      Real.sqrt (∑ B ∈ 𝒞, (2 : ℝ) ^ B.card *
        ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * ‖b B‖ ^ 2)) =
      ∑ B ∈ 𝒞, (2 : ℝ) ^ B.card *
        ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * r B ^ 2) := by
    have := hsq (fun B => (2 : ℝ) ^ B.card * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2)
      (fun B => by positivity)
    simp only [mul_assoc] at this ⊢
    exact this
  rw [e3] at he3
  rw [e4] at he4
  -- the split of `X_p`
  have hsplit : (∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, if Disjoint B1 B2 then a B1 * b B2 *
      pairX M K₁ Kt G (B1 ∪ B2) else 0) =
      -(cMain * ((Real.sqrt M : ℝ) : ℂ)) * (∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, if Disjoint B1 B2 then a B1 * b B2 *
        (phiS (B1 ∪ B2) * pairMain K₁ Kt G (B1 ∪ B2)) else 0) +
      (∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, if Disjoint B1 B2 then a B1 * b B2 * err3 M K₁ G (B1 ∪ B2) else 0) -
      (∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, if Disjoint B1 B2 then a B1 * b B2 * err4 M Kt G (B1 ∪ B2)
        else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun B1 _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun B2 _ => ?_
    split_ifs
    · unfold pairX; ring
    · ring
  rw [hsplit]
  set S1 := ∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, (if Disjoint B1 B2 then a B1 * b B2 *
    (phiS (B1 ∪ B2) * pairMain K₁ Kt G (B1 ∪ B2)) else 0) with hS1
  set S3 := ∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, (if Disjoint B1 B2 then a B1 * b B2 * err3 M K₁ G (B1 ∪ B2)
    else 0) with hS3
  set S4 := ∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, (if Disjoint B1 B2 then a B1 * b B2 * err4 M Kt G (B1 ∪ B2)
    else 0) with hS4
  have hcm : 0 ≤ ‖cMain‖ * Real.sqrt M := by positivity
  have hn1 : ‖-(cMain * ((Real.sqrt M : ℝ) : ℂ)) * S1‖ ≤
      ‖cMain‖ * Real.sqrt M * ((4 : ℝ) ^ G.card * (Δm * ∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * r B ^ 2)) := by
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hm hcm
  calc ‖-(cMain * ((Real.sqrt M : ℝ) : ℂ)) * S1 + S3 - S4‖
      ≤ ‖-(cMain * ((Real.sqrt M : ℝ) : ℂ)) * S1‖ + ‖S3‖ + ‖S4‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hn1 he3) he4
    _ = _ := by ring

theorem one_le_eulB (ε : ℝ) (B : Finset Pr) : 1 ≤ ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) :=
  Finset.one_le_prod₀ fun _ _ => le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg _) _)

set_option maxHeartbeats 800000 in
/-- **The bound for one gcd part** (Goldmakher and Louvel's Proposition, for one `𝔤`): for the rows
of `B(M, N, K)`, columns `G ∪ B` with `X_lo ≤ N(B) ≤ X`, `3R²X²N(G) ≤ 4MK₁`, `K₁ ≤ K ≤ M` and the
three norms `Δ_m` (rows `N(d)^{−1/2}` on `(K₁/N(G), K]`), `Δ₃` (squarefree rows up to `K₁`) and
`Δ₄` (squarefree rows up to `K`) at `X`,
`|gcdPart| ≤ w⁻¹·(|c_J|√M·4^{|G|}Δ_m + 2^{|G|}(2M/√3)C₃(4MK₁/3)^{ε/2}Δ₃/X_lo + C₄Π_GΔ₄)·P·Σ|α|²`,
where `P` bounds `2^{|B|}Π_B²`. -/
theorem gcdPart_bw_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C3 C4 : ℝ, 0 ≤ C3 ∧ 0 ≤ C4 ∧ ∀ (M K₁ Kt X Xlo Δm Δ3 Δ4 P : ℝ) (G : Finset Pr)
      (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ), 0 < M → Kt ≤ M → K₁ ≤ Kt → 1 < Xlo →
      0 ≤ Δm → 0 ≤ Δ3 → 0 ≤ Δ4 → 0 ≤ P → 3 * RΦ ^ 2 * X ^ 2 * nI G ≤ 4 * M * K₁ →
      FBound (wR (K₁ / nI G) Kt) X Δm → FBound (sqfW K₁) X Δ3 → FBound (sqfW Kt) X Δ4 →
      (∀ B ∈ colG 𝒩 G, Xlo ≤ nI B ∧ nI B ≤ X ∧
        (2 : ℝ) ^ B.card * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 ≤ P) →
      ‖gcdPart (bw M Kt) G 𝒩 α‖ ≤ (Fintype.card (𝓞 K)ˣ : ℝ)⁻¹ *
        ((‖cMain‖ * Real.sqrt M * (4 : ℝ) ^ G.card * Δm +
          (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 *
            (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * Δ3 / Xlo +
          C4 * (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Δ4) * P) * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := by
  obtain ⟨C3, C4, hC3, hC4, hb⟩ := bilin_pairX hε
  refine ⟨C3, C4, hC3, hC4, fun M K₁ Kt X Xlo Δm Δ3 Δ4 P G 𝒩 α hM hKM hK hXlo hm0 h30 h40
    hP0 hK₁ hFm hF3 hF4 h𝒞 => ?_⟩
  set 𝒞 := colG 𝒩 G with h𝒞def
  set r : Finset Pr → ℝ := fun B => ‖α (G ∪ B)‖ with hr
  set s : Finset Pr → ℂ := fun B => q2 B (-1) with hs
  have hGB : ∀ B ∈ 𝒞, Disjoint G B := fun B hB => (mem_colG.1 hB).1
  have hne : ∀ B ∈ 𝒞, B.Nonempty := fun B hB => by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have := (h𝒞 ∅ hB).1
    rw [nI_empty] at this
    linarith
  have hu : (0 : ℝ) < Fintype.card (𝓞 K)ˣ := by exact_mod_cast Fintype.card_pos
  -- the pairs
  have hpair : ∀ B1 ∈ 𝒞, ∀ B2 ∈ 𝒞, Disjoint B1 B2 →
      (Fintype.card (𝓞 K)ˣ : ℂ) * pW (bw M Kt) (G ∪ B1) (G ∪ B2) =
        parS B1 B2 * pairX M K₁ Kt G (B1 ∪ B2) := by
    intro B1 hB1 B2 hB2 h12
    rw [pW_bw_pair hM Kt (hGB B1 hB1) (hGB B2 hB2) h12]
    refine pair_eq_parS hM (hGB B1 hB1) (hGB B2 hB2) h12
      ((hne B1 hB1).mono Finset.subset_union_left) ?_ hK
    rw [nI_union h12]
    have hx1 := (h𝒞 B1 hB1).2.1
    have hx2 := (h𝒞 B2 hB2).2.1
    have hp1 := nI_pos B1
    have hp2 := nI_pos B2
    have hG := nI_pos G
    have hR : 0 ≤ 3 * RΦ ^ 2 := by positivity
    have h12' : nI B1 * nI B2 ≤ X ^ 2 := by nlinarith
    calc 3 * RΦ ^ 2 * (nI B1 * nI B2) * nI G ≤ 3 * RΦ ^ 2 * X ^ 2 * nI G := by
          gcongr
      _ ≤ 4 * M * K₁ := hK₁
  have hmain : (Fintype.card (𝓞 K)ˣ : ℂ) * gcdPart (bw M Kt) G 𝒩 α =
      (1 / 2 : ℂ) * (∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, if Disjoint B1 B2 then α (G ∪ B1) * conj (α (G ∪ B2)) *
        pairX M K₁ Kt G (B1 ∪ B2) else 0) +
      (1 / 2 : ℂ) * (∑ B1 ∈ 𝒞, ∑ B2 ∈ 𝒞, if Disjoint B1 B2 then (α (G ∪ B1) * s B1) *
        (conj (α (G ∪ B2)) * s B2) * pairX M K₁ Kt G (B1 ∪ B2) else 0) := by
    rw [gcdPart_eq_pairs, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B1 hB1 => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B2 hB2 => ?_
    by_cases h12 : Disjoint B1 B2
    · rw [ite_eq_left h12, ite_eq_left h12, ite_eq_left h12]
      have := hpair B1 hB1 B2 hB2 h12
      calc (Fintype.card (𝓞 K)ˣ : ℂ) * (α (G ∪ B1) * conj (α (G ∪ B2)) *
            pW (bw M Kt) (G ∪ B1) (G ∪ B2))
          = α (G ∪ B1) * conj (α (G ∪ B2)) *
            ((Fintype.card (𝓞 K)ˣ : ℂ) * pW (bw M Kt) (G ∪ B1) (G ∪ B2)) := by ring
        _ = _ := by rw [this, parS]; simp only [hs]; ring
    · rw [ite_eq_right h12, ite_eq_right h12, ite_eq_right h12]; ring
  -- the bilinear bound, twice
  have hra : ∀ B, ‖α (G ∪ B)‖ = r B := fun B => rfl
  have hrb : ∀ B, ‖conj (α (G ∪ B))‖ = r B := fun B => by rw [RCLike.norm_conj]
  have hras : ∀ B, ‖α (G ∪ B) * s B‖ = r B := fun B => by
    rw [norm_mul, hs, norm_q2_neg_one, mul_one]
  have hrbs : ∀ B, ‖conj (α (G ∪ B)) * s B‖ = r B := fun B => by
    rw [norm_mul, hs, norm_q2_neg_one, mul_one, RCLike.norm_conj]
  have h𝒞X : ∀ B ∈ 𝒞, nI B ≤ X ∧ Disjoint G B := fun B hB => ⟨(h𝒞 B hB).2.1, hGB B hB⟩
  have hT1 := hb M K₁ Kt X Δm Δ3 Δ4 G 𝒞 _ _ r hM hKM hm0 h30 h40 hFm hF3 hF4 h𝒞X hra hrb
  have hT2 := hb M K₁ Kt X Δm Δ3 Δ4 G 𝒞 _ _ r hM hKM hm0 h30 h40 hFm hF3 hF4 h𝒞X hras hrbs
  set T := ‖cMain‖ * Real.sqrt M * (4 : ℝ) ^ G.card * Δm * (∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * r B ^ 2) +
    (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 *
      ((Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * Δ3 *
        ∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
          ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * r B ^ 2)) +
    C4 * ((∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Δ4 *
      ∑ B ∈ 𝒞, (2 : ℝ) ^ B.card * ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * r B ^ 2))
    with hT
  have hunit : (Fintype.card (𝓞 K)ˣ : ℝ) * ‖gcdPart (bw M Kt) G 𝒩 α‖ ≤ T := by
    have h := congrArg norm hmain
    rw [norm_mul, Complex.norm_natCast] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    linarith
  -- the sums of squares
  set S := ∑ B ∈ 𝒞, r B ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun B _ => sq_nonneg _
  have hSle : S ≤ ∑ A ∈ 𝒩, ‖α A‖ ^ 2 :=
    sum_colG_le 𝒩 G (f := fun A => ‖α A‖ ^ 2) fun A => sq_nonneg _
  have hXlo0 : 0 < Xlo := by linarith
  have hq0 : ∀ B ∈ 𝒞, (2 : ℝ) ^ B.card * r B ^ 2 ≤ P * r B ^ 2 := fun B hB => by
    have h1 := one_le_eulB ε B
    have hP := (h𝒞 B hB).2.2
    have h2 : (2 : ℝ) ^ B.card ≤ P := by
      have : (2 : ℝ) ^ B.card * 1 ≤ (2 : ℝ) ^ B.card * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ h1) (by positivity)
      linarith
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hq3 : ∀ B ∈ 𝒞, (2 : ℝ) ^ B.card * (((Real.sqrt (nI B))⁻¹ *
      ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * r B ^ 2) ≤ P / Xlo * r B ^ 2 := fun B hB => by
    have hP := (h𝒞 B hB).2.2
    have hlo := (h𝒞 B hB).1
    have hn := nI_pos B
    rw [mul_pow, inv_pow, Real.sq_sqrt hn.le]
    have hE : 0 ≤ (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 := sq_nonneg _
    have hinv : (nI B)⁻¹ ≤ Xlo⁻¹ := inv_anti₀ hXlo0 hlo
    have hr2 := sq_nonneg (r B)
    calc (2 : ℝ) ^ B.card * ((nI B)⁻¹ * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 * r B ^ 2)
        = (nI B)⁻¹ * ((2 : ℝ) ^ B.card * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2) *
          r B ^ 2 := by ring
      _ ≤ Xlo⁻¹ * P * r B ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hinv hP
          (mul_nonneg (pow_nonneg zero_le_two _) hE) (inv_nonneg.2 hXlo0.le)) hr2
      _ = P / Xlo * r B ^ 2 := by ring
  have hq4 : ∀ B ∈ 𝒞, (2 : ℝ) ^ B.card * ((∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 *
      r B ^ 2) ≤ P * r B ^ 2 := fun B hB => by
    have hP := (h𝒞 B hB).2.2
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hP (sq_nonneg _)
  have hs0 := Finset.sum_le_sum hq0
  have hs3 := Finset.sum_le_sum hq3
  have hs4 := Finset.sum_le_sum hq4
  rw [← Finset.mul_sum] at hs0 hs3 hs4
  have hΛ : 0 ≤ Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε := by positivity
  have hPiG : 0 ≤ ∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε) := le_trans zero_le_one (one_le_eulB ε G)
  have h1 : 0 ≤ ‖cMain‖ * Real.sqrt M * (4 : ℝ) ^ G.card * Δm := by positivity
  have h2 : 0 ≤ (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 := by
    have : 0 ≤ 2 * M / Real.sqrt 3 := by positivity
    positivity
  set br : ℝ := ‖cMain‖ * Real.sqrt M * (4 : ℝ) ^ G.card * Δm +
    (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 *
      (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * Δ3 / Xlo +
    C4 * (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Δ4 with hbr
  have hbr0 : 0 ≤ br := by
    have : 0 ≤ (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 *
      (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * Δ3 / Xlo := by positivity
    have : 0 ≤ C4 * (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Δ4 := by positivity
    linarith
  have hT' : T ≤ br * P * S := by
    rw [hT]
    calc _ ≤ ‖cMain‖ * Real.sqrt M * (4 : ℝ) ^ G.card * Δm * (P * S) +
          (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 *
            ((Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) * Δ3 * (P / Xlo * S)) +
          C4 * ((∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Δ4 * (P * S)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hs0 h1)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs3 (mul_nonneg hΛ h30)) h2))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs4 (mul_nonneg hPiG h40)) hC4)
      _ = br * P * S := by rw [hbr]; ring
  have hfin : (Fintype.card (𝓞 K)ˣ : ℝ) * ‖gcdPart (bw M Kt) G 𝒩 α‖ ≤
      br * P * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 :=
    hunit.trans (hT'.trans (mul_le_mul_of_nonneg_left hSle (mul_nonneg hbr0 hP0)))
  rw [mul_assoc, le_inv_mul_iff₀ hu]
  linarith

end Eis

end

#print axioms Eis.mem_colG
#print axioms Eis.inter_eq_iff_disjoint_sdiff
#print axioms Eis.gcdPart_eq_pairs
#print axioms Eis.q2_self_mul
#print axioms Eis.Phi_re_ofReal
#print axioms Eis.pW_bw_pair
#print axioms Eis.q2_neg_one_cases
#print axioms Eis.norm_q2_neg_one
#print axioms Eis.pair_eq_parS
#print axioms Eis.sum_colG_le
#print axioms Eis.bilin_pairX
#print axioms Eis.one_le_eulB
#print axioms Eis.gcdPart_bw_le
