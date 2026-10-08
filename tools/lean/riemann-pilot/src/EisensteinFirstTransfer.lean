import EisensteinTransferRowCol

/-! # The companion paper's Lemma 7.1, the first transfer (round 320)

S5c-3 in round 316's plan. The companion paper's Lemma 7.1, with its LaTeX rendered as text: "If
`M≥0` satisfies `𝒬_{ξ_1}(U)≤M‖U‖²_{C^j(I_*)}` for every `U∈C_c^∞(I_*)` and every `ξ_1`, then
`𝒜(W)≪D^{ε_0}(Σ+M)‖W‖²_{C^{2j+4}(I)}`." After round 319's identity, its proof bounds the zero
frequency, counts the multiplicity of `y = hf²`, and separates the row-dependent kernels with its
Lemma B.2.

* **The form `𝒬`** of the paper's (7.2) (`ellS`, `Ycd`, `Pcol`, `qTriples`, `Qform`).
* **The multiplicity of `y = μf²`** (`card_sq_dvd_le`, `sum_pairs_le_mult`).
* **The terms that vanish** (`rcDual_eq_zero_of_meet`, `rcDual_eq_zero_of_large_bTV`,
  `rcDual_eq_zero_of_large_mu`).
* **The bilinear form with enlarged columns** (`rcDual_eq_bilin`, `rowSumD_eq_bilinear`): the row-
  dependent column scale `ℓ = L/(N(C)N(t))` is absorbed by indexing the columns by pairs (row, set of
  primes).
* **The column mean square** (`rows_meanSquareD`), **the bound for one pair of characters**
  (`blockD_bound`, through round 317's `bilinear_dual_bound_unif`), **the zero frequency**
  (`zero_rowD_le`) and **`first_transfer`**.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The multiplicity of `y = μf²` -/

theorem pgen_ne_zero {f : Ideal (𝓞 K)} (h6 : (absNorm f).Coprime 6) : pgen f ≠ 0 := by
  intro h
  have hs := (pgen_spec6 h6).2
  rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hs
  exact ne_bot_of_coprime6 h6 hs.symm

theorem primeSet_subset_of_dvd {f : Ideal (𝓞 K)} {y : 𝓞 K} (hy : y ≠ 0)
    (h6 : (absNorm f).Coprime 6) (hd : f ∣ span {y}) : primeSet f ⊆ primeSet (span {y}) := by
  intro P hP
  rw [mem_primeSet] at hP ⊢
  have hy0 : span {y} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  exact Multiset.subset_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_coprime6 h6) hy0).1 hd) hP

open Classical in
/-- **The divisor count for `f² ∣ y`**: for `δ > 0` there is `C` such that, for `y ≠ 0`, the
squarefree ideals `f` of norm prime to `6` in any finite family with `pgen(f)² ∣ y` number at most
`C·N(y)^δ`. They are determined by their sets of primes, which lie among the primes of `(y)`, and
`2^{ω(y)} ≤ 4^{ω(y)} ≤ C·N(y)^δ` (round 310's `four_pow_card_le`). -/
theorem card_sq_dvd_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Fs : Finset (Ideal (𝓞 K))),
      (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f) → ∀ y : 𝓞 K, y ≠ 0 →
        ((Fs.filter fun f => pgen f ^ 2 ∣ y).card : ℝ) ≤
          C * (absNorm (span {y}) : ℝ) ^ δ := by
  obtain ⟨C, hC0, hC⟩ := four_pow_card_le hδ
  refine ⟨C, hC0, fun Fs hFs y hy => ?_⟩
  set A := primeSet (span {y}) with hA
  have hy0 : span {y} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hmaps : Set.MapsTo primeSet ↑(Fs.filter fun f => pgen f ^ 2 ∣ y) ↑A.powerset := by
    intro f hf
    rw [Finset.mem_coe, Finset.mem_filter] at hf
    obtain ⟨h6, hsq⟩ := hFs f hf.1
    rw [Finset.mem_coe, Finset.mem_powerset]
    refine primeSet_subset_of_dvd hy h6 ?_
    rw [← span_pgen h6 hsq, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact (dvd_pow_self _ two_ne_zero).trans hf.2
  have hinj : Set.InjOn primeSet ↑(Fs.filter fun f => pgen f ^ 2 ∣ y) := by
    intro f hf f' hf' he
    rw [Finset.mem_coe, Finset.mem_filter] at hf hf'
    have h1 := hFs f hf.1
    have h2 := hFs f' hf'.1
    rw [← idl_primeSet h1.1 h1.2, ← idl_primeSet h2.1 h2.2, he]
  have hcard := Finset.card_le_card_of_injOn primeSet hmaps hinj
  rw [Finset.card_powerset] at hcard
  have h4 : (2 : ℝ) ^ A.card ≤ 4 ^ A.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hnI : nI A ≤ (absNorm (span {y}) : ℝ) := by
    have hd : idl A ∣ span {y} := dvd_of_subset_primeSet hy0 subset_rfl
    have hpos : 0 < absNorm (span {y}) :=
      Nat.pos_of_ne_zero (by rwa [Ne, absNorm_eq_zero_iff])
    unfold nI
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd absNorm hd)
  calc ((Fs.filter fun f => pgen f ^ 2 ∣ y).card : ℝ) ≤ (2 : ℝ) ^ A.card := by exact_mod_cast hcard
    _ ≤ 4 ^ A.card := h4
    _ ≤ C * nI A ^ δ := hC A
    _ ≤ C * (absNorm (span {y}) : ℝ) ^ δ := by
        have := nI_pos A
        gcongr

open Classical in
/-- **The multiplicity of `y = μf²`** (the companion paper's "the map `(f,h)↦y=hf^2` has
divisor-bounded multiplicity in `y`"): for nonnegative `G` and a finite set of pairs `(f, μ)` with
`f` squarefree of norm prime to `6`, `μ ≠ 0` and `N(μf²) ≤ Y`,
`Σ_{(f,μ)} G(μ·pgen(f)²) ≤ C·Y^δ·Σ_{y} G(y)` over the image. -/
theorem sum_pairs_le_mult {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Rs : Finset (Ideal (𝓞 K) × 𝓞 K)) (Y : ℝ),
      (∀ p ∈ Rs, (absNorm p.1).Coprime 6 ∧ Squarefree p.1 ∧ p.2 ≠ 0 ∧
        (absNorm (span {p.2 * pgen p.1 ^ 2}) : ℝ) ≤ Y) →
      ∀ G : 𝓞 K → ℝ, (∀ y, 0 ≤ G y) →
      ∑ p ∈ Rs, G (p.2 * pgen p.1 ^ 2) ≤
        C * Y ^ δ * ∑ y ∈ Rs.image (fun p => p.2 * pgen p.1 ^ 2), G y := by
  obtain ⟨C, hC0, hC⟩ := card_sq_dvd_le hδ
  refine ⟨C, hC0, fun Rs Y hRs G hG => ?_⟩
  rw [Finset.sum_comp, Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨p0, hp0, hp0y⟩ := Finset.mem_image.1 hy
  obtain ⟨h06, h0sq, h0μ, h0Y⟩ := hRs p0 hp0
  have hy0 : y ≠ 0 := by
    rw [← hp0y]; exact mul_ne_zero h0μ (pow_ne_zero 2 (pgen_ne_zero h06))
  have hFs : ∀ f ∈ Rs.image Prod.fst, (absNorm f).Coprime 6 ∧ Squarefree f := by
    intro f hf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨(hRs p hp).1, (hRs p hp).2.1⟩
  have hfib : (Rs.filter fun p => p.2 * pgen p.1 ^ 2 = y).card ≤
      ((Rs.image Prod.fst).filter fun f => pgen f ^ 2 ∣ y).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_image_of_mem _ hp.1, hp.2 ▸ dvd_mul_left _ _⟩
    · intro p hp p' hp' he
      rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      have hne : pgen p.1 ^ 2 ≠ 0 := pow_ne_zero 2 (pgen_ne_zero (hRs p hp.1).1)
      have h2 : p.2 = p'.2 := by
        have e : p.2 * pgen p.1 ^ 2 = p'.2 * pgen p.1 ^ 2 := by rw [hp.2, he, hp'.2]
        exact mul_right_cancel₀ hne e
      exact Prod.ext he h2
  have hNy : (absNorm (span {y}) : ℝ) ≤ Y := by rw [← hp0y]; exact h0Y
  have hcard : ((Rs.filter fun p => p.2 * pgen p.1 ^ 2 = y).card : ℝ) ≤ C * Y ^ δ := by
    calc ((Rs.filter fun p => p.2 * pgen p.1 ^ 2 = y).card : ℝ)
        ≤ (((Rs.image Prod.fst).filter fun f => pgen f ^ 2 ∣ y).card : ℝ) := by
          exact_mod_cast hfib
      _ ≤ C * (absNorm (span {y}) : ℝ) ^ δ := hC _ hFs y hy0
      _ ≤ C * Y ^ δ := by
          gcongr
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard (hG y)

/-! ### The companion paper's form `𝒬_{ξ₁}(U)` of (7.2) -/

/-- The column scale `ℓ = L/(N(C)N(t))` of the companion paper's Section 7, with `C = b ∪ T` and
`t = V`. -/
def ellS (L : ℝ) (b T V : Finset Pr) : ℝ := L / (nI b * nI T * nI V)

/-- The row range `Y_{C,d} = c_I·ΣLF·N(d)/(𝓗N(C)²)` of the companion paper's Section 7, with
`C = b ∪ T` and `d = T`: `c_I·SLF/(H·N(b)²N(T))`. -/
def Ycd (cI S L F H : ℝ) (b T : Finset Pr) : ℝ := cI * S * L * F / (H * nI b ^ 2 * nI T)

/-- **The Möbius column sum `P_{C,d,t}(y; U)`** of the companion paper's (7.1), with `C = b ∪ T`,
`d = T`, `t = V` and `p_y = colP ξ₁ y (b⁴T⁵V⁶)`, over the columns of norm at most `2βℓ`. -/
def Pcol (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ) (β L : ℝ) (b T V : Finset Pr)
    (y : 𝓞 K) : ℂ :=
  ∑ M ∈ fsLe (2 * β * ellS L b T V),
    colP ξ1 y (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * U (nI M / ellS L b T V)

open Classical in
/-- The index set of the companion paper's (7.2), the coprime squarefree `C, t` with `N(C)N(t) ≤ 2vL`
and the `d ∣ C`, as the triples `(b, d, t)` of pairwise disjoint sets of primes of norm product at
most `Λ` (`C = b ∪ d`). -/
def qTriples (Λ : ℝ) : Finset (Finset Pr × Finset Pr × Finset Pr) :=
  (fsLe Λ ×ˢ fsLe Λ ×ˢ fsLe Λ).filter fun t =>
    Disjoint t.1 t.2.1 ∧ Disjoint (t.1 ∪ t.2.1) t.2.2 ∧ nI t.1 * nI t.2.1 * nI t.2.2 ≤ Λ

/-- **The companion paper's nonnegative form `𝒬_{ξ₁}(U)` of (7.2)**, times `2LF/√3`: over the triples
`(b, d, t)` of `qTriples (2βL)`, the weight `2H·N(b)/(√3·L)` times
`Re Σ_y |P_{C,d,t}(y; U)|²·Φ(y/√Y_{C,d})`. The paper's weight is `w_{C,d} = 𝓗N(C)/(N(d)L²F)`, and
`N(C)/N(d) = N(b)`. -/
def Qform (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ) (β H L S F cI : ℝ) : ℝ :=
  ∑ t ∈ qTriples (2 * β * L),
    2 * H * nI t.1 / (Real.sqrt 3 * L) *
      (∑' y : 𝓞 K, Pcol ξ1 U β L t.1 t.2.1 t.2.2 y * conj (Pcol ξ1 U β L t.1 t.2.1 t.2.2 y) *
        Majorant.Phi (σO y / (Real.sqrt (Ycd cI S L F H t.1 t.2.1) : ℂ))).re

/-! ### The terms that vanish -/

section Vanish

variable (W : ℝ → ℂ) (X H : ℝ) (f : 𝓞 K) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
  (b T V : Finset Pr) (μ : 𝓞 K) (M1 M2 : Finset Pr)

theorem rcDual_eq_zero_of_W1 (h : MellinSep.W0c W (nI b * nI T * nI V * nI M1 / X) = 0) :
    rcDual W X H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcDual; rw [h]; ring

theorem rcDual_eq_zero_of_W2 (h : MellinSep.W0c W (nI b * nI T * nI V * nI M2 / X) = 0) :
    rcDual W X H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcDual; rw [h]; simp

theorem rcDual_eq_zero_of_dualW (h : dualW H (V ∪ M1) (V ∪ M2) T μ = 0) :
    rcDual W X H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcDual; rw [h]; ring

theorem rcDual_eq_zero_of_colP1
    (h : colP ξ1 (μ * f ^ 2) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M1 = 0) :
    rcDual W X H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcDual; rw [h]; ring

theorem rcDual_eq_zero_of_colP2
    (h : colP ξ2 (μ * f ^ 2) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M2 = 0) :
    rcDual W X H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  unfold rcDual; rw [h]; simp

end Vanish

theorem W0c_eq_zero_of_gt {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {x : ℝ} (hx : β < x) :
    MellinSep.W0c W x = 0 := by
  unfold MellinSep.W0c; rw [hW x hx, zero_div]

/-- A prime of `b ∪ T ∪ V` divides `c = b⁴T⁵V⁶`. -/
theorem dvd_c_of_mem {b T V : Finset Pr} {P : Pr} (hP : P ∈ b ∪ T ∪ V) :
    πP P ∣ eS b ^ 4 * eS T ^ 5 * eS V ^ 6 := by
  rcases Finset.mem_union.1 hP with h | h
  · rcases Finset.mem_union.1 h with h | h
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        ((Finset.dvd_prod_of_mem _ h).trans (dvd_pow_self _ (by norm_num))) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
        ((Finset.dvd_prod_of_mem _ h).trans (dvd_pow_self _ (by norm_num))) _) _
  · exact dvd_mul_of_dvd_right ((Finset.dvd_prod_of_mem _ h).trans (dvd_pow_self _ (by norm_num))) _

/-- **The columns meeting `b ∪ T ∪ V` vanish** (the companion paper's "the other original zeros are
supplied by `p_{hf^2}(x_i)`"). -/
theorem rcDual_eq_zero_of_meet (W : ℝ → ℂ) (X H : ℝ) (f : 𝓞 K)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (b T V : Finset Pr) (μ : 𝓞 K)
    (M1 M2 : Finset Pr) (h : ¬ Disjoint (b ∪ T ∪ V) M1 ∨ ¬ Disjoint (b ∪ T ∪ V) M2) :
    rcDual W X H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  rcases h with h | h
  · rw [Finset.not_disjoint_iff] at h
    obtain ⟨P, hP, hPM⟩ := h
    exact rcDual_eq_zero_of_colP1 W X H f ξ1 ξ2 b T V μ M1 M2
      (colP_eq_zero_of_dvd ξ1 _ _ hPM (dvd_c_of_mem hP))
  · rw [Finset.not_disjoint_iff] at h
    obtain ⟨P, hP, hPM⟩ := h
    exact rcDual_eq_zero_of_colP2 W X H f ξ1 ξ2 b T V μ M1 M2
      (colP_eq_zero_of_dvd ξ2 _ _ hPM (dvd_c_of_mem hP))

/-- **The rows of norm beyond `βX` vanish**: if `N(b)N(T)N(V) > βX`, every term vanishes. -/
theorem rcDual_eq_zero_of_large_bTV {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ}
    (hX : 0 < X) (H : ℝ) (f : 𝓞 K) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    {b T V : Finset Pr} (μ : 𝓞 K) (M1 M2 : Finset Pr) (h : β * X < nI b * nI T * nI V) :
    rcDual W X H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  refine rcDual_eq_zero_of_W1 W X H f ξ1 ξ2 b T V μ M1 M2 (W0c_eq_zero_of_gt hW ?_)
  rw [lt_div_iff₀ hX]
  have := one_le_nI M1
  have : 0 < nI b * nI T * nI V := by have := nI_pos b; have := nI_pos T; have := nI_pos V; positivity
  nlinarith

/-- **The rows beyond the paper's `Y_{C,d}` vanish** (the companion paper's "its nonzero image
satisfies `N(y)≤4C_Φv^2L^2F^2N(d)/(𝓗N(C)^2)≤Y_{C,d}`"): with `3β²R² ≤ c_I`, `LF ≤ S`, `Φ̂` vanishing beyond `R`, and
`Y_{C,d} < 4F²·N(μ)`, every term with columns prime to `V` vanishes. -/
theorem rcDual_eq_zero_of_large_mu {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {L H S F cI : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hF : 0 < F) (hS : L * F ≤ S) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) (hcI : 3 * β ^ 2 * R ^ 2 ≤ cI) (f : 𝓞 K)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (b T V : Finset Pr) (μ : 𝓞 K)
    {M1 M2 : Finset Pr} (hV1 : Disjoint V M1) (hV2 : Disjoint V M2)
    (hy : Ycd cI S L F H b T < (absNorm (span {μ}) : ℝ) * (4 * F ^ 2)) :
    rcDual W L H f ξ1 ξ2 b T V μ M1 M2 = 0 := by
  by_cases h1 : MellinSep.W0c W (nI b * nI T * nI V * nI M1 / L) = 0
  · exact rcDual_eq_zero_of_W1 W L H f ξ1 ξ2 b T V μ M1 M2 h1
  by_cases h2 : MellinSep.W0c W (nI b * nI T * nI V * nI M2 / L) = 0
  · exact rcDual_eq_zero_of_W2 W L H f ξ1 ξ2 b T V μ M1 M2 h2
  have hx1 : nI b * nI T * nI V * nI M1 / L ≤ β := by
    by_contra hc; exact h1 (W0c_eq_zero_of_gt hW (not_le.1 hc))
  have hx2 : nI b * nI T * nI V * nI M2 / L ≤ β := by
    by_contra hc; exact h2 (W0c_eq_zero_of_gt hW (not_le.1 hc))
  refine rcDual_eq_zero_of_dualW W L H f ξ1 ξ2 b T V μ M1 M2 ?_
  unfold dualW
  refine hR _ ?_
  have hb := nI_pos b
  have hT := nI_pos T
  have hV := nI_pos V
  have hm1 := nI_pos M1
  have hm2 := nI_pos M2
  set Nμ := (absNorm (span {μ}) : ℝ) with hNμ
  have hNμ0 : 0 ≤ Nμ := Nat.cast_nonneg _
  rw [Real.le_sqrt' hR0, nI_union hV1, nI_union hV2, le_div_iff₀ (by positivity)]
  have e1 : nI b * nI T * nI V * nI M1 ≤ β * L := by rwa [div_le_iff₀ hL] at hx1
  have e2 : nI b * nI T * nI V * nI M2 ≤ β * L := by rwa [div_le_iff₀ hL] at hx2
  have ey : cI * S * L * F < Nμ * (4 * F ^ 2) * (H * nI b ^ 2 * nI T) := by
    unfold Ycd at hy; rwa [div_lt_iff₀ (by positivity)] at hy
  have hcI0 : 0 ≤ cI := le_trans (by positivity) hcI
  have eS' : cI * (L * F) * L * F ≤ cI * S * L * F := by
    have := mul_le_mul_of_nonneg_left hS hcI0
    nlinarith [mul_pos hL hF]
  have ek : cI * L ^ 2 < 4 * Nμ * H * nI b ^ 2 * nI T := by
    have h4 : cI * L ^ 2 * F ^ 2 < 4 * Nμ * H * nI b ^ 2 * nI T * F ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_right h4 (sq_nonneg F)
  have e3 : (nI b * nI T * nI V * nI M1) * (nI b * nI T * nI V * nI M2) ≤ (β * L) * (β * L) :=
    mul_le_mul e1 e2 (by positivity) (le_trans (by positivity) e1)
  have key : R ^ 2 * (3 * (nI V * nI M1 * (nI V * nI M2)) * nI T) * (nI b ^ 2 * nI T) ≤
      4 * H * Nμ * (nI b ^ 2 * nI T) := by
    calc R ^ 2 * (3 * (nI V * nI M1 * (nI V * nI M2)) * nI T) * (nI b ^ 2 * nI T)
        = 3 * R ^ 2 * ((nI b * nI T * nI V * nI M1) * (nI b * nI T * nI V * nI M2)) := by ring
      _ ≤ 3 * R ^ 2 * ((β * L) * (β * L)) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = 3 * β ^ 2 * R ^ 2 * L ^ 2 := by ring
      _ ≤ cI * L ^ 2 := mul_le_mul_of_nonneg_right hcI (sq_nonneg L)
      _ ≤ 4 * Nμ * H * nI b ^ 2 * nI T := ek.le
      _ = 4 * H * Nμ * (nI b ^ 2 * nI T) := by ring
  exact le_of_mul_le_mul_right key (by positivity)

/-- `N(μ·pgen(f)²) = N(μ)·N(f)²` for `f` of norm prime to `6`. -/
theorem absNorm_mul_pgen_sq {f : Ideal (𝓞 K)} (h6 : (absNorm f).Coprime 6) (μ : 𝓞 K) :
    (absNorm (span {μ * pgen f ^ 2}) : ℝ) = (absNorm (span {μ}) : ℝ) * (absNorm f : ℝ) ^ 2 := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, (pgen_spec6 h6).2,
    map_mul, map_pow]
  push_cast; ring

/-! ### Flattening the triples -/

theorem powerset_sdiff_eq_filter (U0 b : Finset Pr) :
    (U0 \ b).powerset = U0.powerset.filter (fun T => Disjoint b T) := by
  ext T
  simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_sdiff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩

open Classical in
/-- The triples `(b, T, V)` of pairwise disjoint subsets of `U₀`. -/
def triplesOf (U0 : Finset Pr) : Finset (Finset Pr × Finset Pr × Finset Pr) :=
  (U0.powerset ×ˢ U0.powerset ×ˢ U0.powerset).filter fun t =>
    Disjoint t.1 t.2.1 ∧ Disjoint (t.1 ∪ t.2.1) t.2.2

open Classical in
theorem sum_nested_eq_triplesOf (U0 : Finset Pr) (g : Finset Pr → Finset Pr → Finset Pr → ℂ) :
    ∑ b ∈ U0.powerset, ∑ T ∈ (U0 \ b).powerset, ∑ V ∈ (U0 \ (b ∪ T)).powerset, g b T V =
      ∑ t ∈ triplesOf U0, g t.1 t.2.1 t.2.2 := by
  unfold triplesOf
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_product, powerset_sdiff_eq_filter U0 b, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [powerset_sdiff_eq_filter U0 (b ∪ T), Finset.sum_filter]
  by_cases h : Disjoint b T
  · rw [ite_eq_left h]
    exact Finset.sum_congr rfl fun V _ => by simp only [h, true_and]
  · rw [ite_eq_right h]
    exact (Finset.sum_eq_zero fun V _ => by simp [h]).symm

/-! ### Rows and the bilinear form -/

/-- A row `((b, T, V), (𝔣, μ))` of the transfer's dual sum: the paper's `C = b ∪ T`, `d = T`, `t = V`,
the row ideal `𝔣` and the frequency `μ` (its `h`). -/
abbrev RowD := (Finset Pr × Finset Pr × Finset Pr) × (Ideal (𝓞 K) × 𝓞 K)

/-- The weight of a row: the sign `μ(T)μ(V)` and the factor
`ξ₁(V)ξ̄₂(V)·|χ_V(f)⁴|²|χ_V(μ)|²|χ_{bT}(f)⁴|²` of `rcDual`, with `f = pgen 𝔣`. -/
def wRowD (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (r : RowD) : ℂ :=
  ((-1 : ℂ) ^ r.1.2.1.card * (-1) ^ r.1.2.2.card) *
    (ξ1 (cls4 r.1.2.2) * conj (ξ2 (cls4 r.1.2.2)) *
      (chiS r.1.2.2 (pgen r.2.1) ^ 4 * conj (chiS r.1.2.2 (pgen r.2.1) ^ 4)) *
      (chiS r.1.2.2 r.2.2 * conj (chiS r.1.2.2 r.2.2)) *
      (chiS (r.1.1 ∪ r.1.2.1) (pgen r.2.1) ^ 4 * conj (chiS (r.1.1 ∪ r.1.2.1) (pgen r.2.1) ^ 4)))

theorem norm_wRowD_le (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (r : RowD) :
    ‖wRowD ξ1 ξ2 r‖ ≤ 1 := by
  unfold wRowD
  have hc : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖z * conj z‖ ≤ 1 := fun z hz => by
    rw [norm_mul, RCLike.norm_conj]
    calc ‖z‖ * ‖z‖ ≤ 1 * 1 := mul_le_mul hz hz (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h4 : ∀ (A : Finset Pr) (u : 𝓞 K), ‖chiS A u ^ 4‖ ≤ 1 := fun A u => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_chiS_le A u)
  set A := chiS r.1.2.2 (pgen r.2.1) ^ 4 * conj (chiS r.1.2.2 (pgen r.2.1) ^ 4) with hA
  set B := chiS r.1.2.2 r.2.2 * conj (chiS r.1.2.2 r.2.2) with hB
  set Cc := chiS (r.1.1 ∪ r.1.2.1) (pgen r.2.1) ^ 4 *
    conj (chiS (r.1.1 ∪ r.1.2.1) (pgen r.2.1) ^ 4) with hCc
  have hA1 : ‖A‖ ≤ 1 := hc _ (h4 _ _)
  have hB1 : ‖B‖ ≤ 1 := hc _ (norm_chiS_le _ _)
  have hC1 : ‖Cc‖ ≤ 1 := hc _ (h4 _ _)
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg,
    norm_one, one_pow, one_pow, RCLike.norm_conj, norm_xi_cls4, norm_xi_cls4]
  calc 1 * 1 * (1 * 1 * ‖A‖ * ‖B‖ * ‖Cc‖) = ‖A‖ * ‖B‖ * ‖Cc‖ := by ring
    _ ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by ring

/-- The parameter `A_r = 4H·N(μ)·N(b)²N(T)/(3L²)` of a row's dual weight. -/
def ARowD (H L : ℝ) (r : RowD) : ℝ :=
  4 * H * (absNorm (span {r.2.2}) : ℝ) * nI r.1.1 ^ 2 * nI r.1.2.1 / (3 * L ^ 2)

/-- The row weight `2H·N(b)/(√3·L)`, the paper's `w_{C,d}` times `2LF/√3`. -/
def wtD (H L : ℝ) (r : RowD) : ℝ := 2 * H * nI r.1.1 / (Real.sqrt 3 * L)

open Classical in
/-- The coefficients of the enlarged columns `(r', M)`: `√w_r·p_{μf²}(M)` on the row's own block
`r' = r`, and `0` elsewhere. -/
def colE (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (H L : ℝ) (r : RowD) (n : RowD × Finset Pr) : ℂ :=
  if n.1 = r then ((Real.sqrt (wtD H L r) : ℝ) : ℂ) *
    colP ξ (r.2.2 * pgen r.2.1 ^ 2) (eS r.1.1 ^ 4 * eS r.1.2.1 ^ 5 * eS r.1.2.2 ^ 6) n.2 else 0

/-- The point of an enlarged column: `x_{(r, M)} = N(M)/ℓ_r`. -/
def xE (L : ℝ) (n : RowD × Finset Pr) : ℝ := nI n.2 / ellS L n.1.1.1 n.1.1.2.1 n.1.1.2.2

theorem ellS_pos {L : ℝ} (hL : 0 < L) (b T V : Finset Pr) : 0 < ellS L b T V := by
  unfold ellS; have := nI_pos b; have := nI_pos T; have := nI_pos V; positivity

theorem xE_pos {L : ℝ} (hL : 0 < L) (n : RowD × Finset Pr) : 0 < xE L n := by
  unfold xE; exact div_pos (nI_pos _) (ellS_pos hL _ _ _)

/-- **One term in the shape of the bilinear form**: for columns prime to `V`,
`rcDual = w̃_r·(√w_r p(M₁))·conj(√w_r p(M₂))·W₀(x₁)·conj(W₀(x₂))·Φ̂(√(A_r/(x₁x₂)))` with
`x_i = N(M_i)/ℓ_r`. -/
theorem rcDual_eq_bilin (W : ℝ → ℂ) {L H : ℝ} (hL : 0 < L) (hH : 0 ≤ H)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (r : RowD) {M1 M2 : Finset Pr}
    (hV1 : Disjoint r.1.2.2 M1) (hV2 : Disjoint r.1.2.2 M2) :
    rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 =
      wRowD ξ1 ξ2 r * (colE ξ1 H L r (r, M1) * conj (colE ξ2 H L r (r, M2)) *
        (MellinSep.W0c W (1 * xE L (r, M1)) * conj (MellinSep.W0c W (1 * xE L (r, M2))) *
          dualG (Real.sqrt (ARowD H L r / (xE L (r, M1) * xE L (r, M2)))))) := by
  have hb := nI_pos r.1.1
  have hT := nI_pos r.1.2.1
  have hV := nI_pos r.1.2.2
  have h1 := nI_pos M1
  have h2 := nI_pos M2
  have hw : 0 ≤ wtD H L r := by unfold wtD; positivity
  have hx1 : nI r.1.1 * nI r.1.2.1 * nI r.1.2.2 * nI M1 / L = 1 * xE L (r, M1) := by
    unfold xE ellS; field_simp
  have hx2 : nI r.1.1 * nI r.1.2.1 * nI r.1.2.2 * nI M2 / L = 1 * xE L (r, M2) := by
    unfold xE ellS; field_simp
  have hg : dualW H (r.1.2.2 ∪ M1) (r.1.2.2 ∪ M2) r.1.2.1 r.2.2 =
      dualG (Real.sqrt (ARowD H L r / (xE L (r, M1) * xE L (r, M2)))) := by
    unfold dualW
    congr 2
    unfold ARowD xE ellS
    rw [nI_union hV1, nI_union hV2]
    field_simp
  have hsq : ((Real.sqrt (wtD H L r) : ℝ) : ℂ) * conj ((Real.sqrt (wtD H L r) : ℝ) : ℂ) =
      ((2 * H * nI r.1.1 / (Real.sqrt 3 * L) : ℝ) : ℂ) := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hw]; rfl
  unfold rcDual colE wRowD
  rw [ite_eq_left rfl, ite_eq_left rfl, hx1, hx2, hg, map_mul]
  rw [← hsq]
  ring

/-- Sums over the enlarged columns collapse to the row's own block. -/
theorem sum_enlarged {ι κ : Type*} (Rows : Finset ι) (Cs : Finset κ) {r : ι} (hr : r ∈ Rows)
    (g : ι × κ → ℂ) (hg : ∀ n : ι × κ, n.1 ≠ r → g n = 0) :
    ∑ n ∈ Rows ×ˢ Cs, g n = ∑ M ∈ Cs, g (r, M) := by
  rw [Finset.sum_product, Finset.sum_eq_single r]
  · intro r' _ hne; exact Finset.sum_eq_zero fun M _ => hg _ hne
  · intro h; exact absurd hr h

theorem colE_eq_zero_of_ne (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (H L : ℝ) (r : RowD)
    {n : RowD × Finset Pr} (h : n.1 ≠ r) : colE ξ H L r n = 0 := by
  unfold colE; rw [ite_eq_right h]

/-- **A row's double column sum as the bilinear form** (round 309's `rowSum_eq_bilinear` for the
transfer): the columns `M ⊆ U₀∖(b∪T)∖V` of round 319 are completed to the enlarged columns
`Rows ×ˢ 2^{U₀}`, whose extra coefficients vanish. -/
theorem rowSumD_eq_bilinear (W : ℝ → ℂ) {L H : ℝ} (hL : 0 < L) (hH : 0 ≤ H)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U0 : Finset Pr} (Rows : Finset RowD) {r : RowD}
    (hr : r ∈ Rows) :
    ∑ M1 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
        ∑ M2 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
          rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 =
      wRowD ξ1 ξ2 r * ∑ n1 ∈ Rows ×ˢ U0.powerset, ∑ n2 ∈ Rows ×ˢ U0.powerset,
        colE ξ1 H L r n1 * conj (colE ξ2 H L r n2) *
          (MellinSep.W0c W (1 * xE L n1) * conj (MellinSep.W0c W (1 * xE L n2)) *
            dualG (Real.sqrt (ARowD H L r / (xE L n1 * xE L n2)))) := by
  set G : Finset Pr → Finset Pr → ℂ := fun M1 M2 =>
    colE ξ1 H L r (r, M1) * conj (colE ξ2 H L r (r, M2)) *
      (MellinSep.W0c W (1 * xE L (r, M1)) * conj (MellinSep.W0c W (1 * xE L (r, M2))) *
        dualG (Real.sqrt (ARowD H L r / (xE L (r, M1) * xE L (r, M2))))) with hG
  -- collapse the enlarged columns
  have hcol : ∑ n1 ∈ Rows ×ˢ U0.powerset, ∑ n2 ∈ Rows ×ˢ U0.powerset,
      colE ξ1 H L r n1 * conj (colE ξ2 H L r n2) *
        (MellinSep.W0c W (1 * xE L n1) * conj (MellinSep.W0c W (1 * xE L n2)) *
          dualG (Real.sqrt (ARowD H L r / (xE L n1 * xE L n2)))) =
      ∑ M1 ∈ U0.powerset, ∑ M2 ∈ U0.powerset, G M1 M2 := by
    rw [sum_enlarged Rows U0.powerset hr _ fun n hn => by
      rw [Finset.sum_eq_zero fun n2 _ => by rw [colE_eq_zero_of_ne ξ1 H L r hn]; ring]]
    refine Finset.sum_congr rfl fun M1 _ => ?_
    exact sum_enlarged Rows U0.powerset hr _ fun n hn => by
      rw [colE_eq_zero_of_ne ξ2 H L r hn]; simp
  rw [hcol, Finset.mul_sum]
  -- the vanishing of the columns meeting `b ∪ T ∪ V`
  have hsub : ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset ⊆ U0.powerset :=
    Finset.powerset_mono.2 (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hmeet : ∀ M ∈ U0.powerset, M ∉ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset →
      ¬ Disjoint (r.1.1 ∪ r.1.2.1 ∪ r.1.2.2) M := by
    intro M hM hM' hd
    apply hM'
    rw [Finset.mem_powerset] at hM ⊢
    intro P hP
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    have hP' := Finset.disjoint_right.1 hd hP
    simp only [Finset.mem_union, not_or] at hP'
    exact ⟨⟨hM hP, by simp only [Finset.mem_union, not_or]; exact ⟨hP'.1.1, hP'.1.2⟩⟩, hP'.2⟩
  have hcolP : ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (M : Finset Pr),
      ¬ Disjoint (r.1.1 ∪ r.1.2.1 ∪ r.1.2.2) M → colE ξ H L r (r, M) = 0 := by
    intro ξ M h
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨P, hP, hPM⟩ := h
    unfold colE
    rw [ite_eq_left rfl, colP_eq_zero_of_dvd ξ _ _ hPM (dvd_c_of_mem hP), mul_zero]
  have hterm : ∀ M1 ∈ U0.powerset, ∀ M2 ∈ U0.powerset,
      rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 =
        wRowD ξ1 ξ2 r * G M1 M2 := by
    intro M1 _ M2 _
    by_cases h1 : Disjoint (r.1.1 ∪ r.1.2.1 ∪ r.1.2.2) M1
    · by_cases h2 : Disjoint (r.1.1 ∪ r.1.2.1 ∪ r.1.2.2) M2
      · rw [Finset.disjoint_union_left] at h1 h2
        exact rcDual_eq_bilin W hL hH ξ1 ξ2 r h1.2 h2.2
      · rw [rcDual_eq_zero_of_meet W L H _ ξ1 ξ2 _ _ _ _ M1 M2 (Or.inr h2), hG]
        simp only
        rw [hcolP ξ2 M2 h2]; simp
    · rw [rcDual_eq_zero_of_meet W L H _ ξ1 ξ2 _ _ _ _ M1 M2 (Or.inl h1), hG]
      simp only
      rw [hcolP ξ1 M1 h1]; ring
  -- extend the column ranges
  have hext : ∀ M1 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
      ∑ M2 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
        rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 =
      ∑ M2 ∈ U0.powerset, rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 := by
    intro M1 _
    exact Finset.sum_subset hsub fun M2 hM2 hM2' =>
      rcDual_eq_zero_of_meet W L H _ ξ1 ξ2 _ _ _ _ M1 M2 (Or.inr (hmeet M2 hM2 hM2'))
  rw [Finset.sum_congr rfl hext]
  rw [Finset.sum_subset hsub fun M1 hM1 hM1' => Finset.sum_eq_zero fun M2 _ =>
    rcDual_eq_zero_of_meet W L H _ ξ1 ξ2 _ _ _ _ M1 M2 (Or.inl (hmeet M1 hM1 hM1'))]
  refine Finset.sum_congr rfl fun M1 hM1 => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun M2 hM2 => hterm M1 hM1 M2 hM2

/-! ### The column mean square of the rows -/

theorem lt_nI_of_not_mem_fsLe {Y : ℝ} {A : Finset Pr} (hA : A ∉ fsLe Y) : Y < nI A := by
  rw [mem_fsLe, not_le] at hA
  have h1 : (⌊Y⌋₊ : ℝ) + 1 ≤ nI A := by
    unfold nI; exact_mod_cast hA
  linarith [Nat.lt_floor_add_one Y]

theorem mem_fsLe_of_nI_le {Y : ℝ} {A : Finset Pr} (h : nI A ≤ Y) : A ∈ fsLe Y := by
  rw [mem_fsLe]; exact Nat.le_floor h

/-- `Pcol` as a sum over the subsets of any `U₀` containing the primes of norm at most `2βL`. -/
theorem Pcol_eq_powerset (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ} {β L : ℝ}
    (hU : ∀ x, 2 * β < x → U x = 0) (hβ : 0 ≤ β) (hL : 0 < L) {U0 : Finset Pr}
    (hU0 : primesLe (2 * β * L) ⊆ U0) (b T V : Finset Pr) (y : 𝓞 K) :
    Pcol ξ U β L b T V y = ∑ M ∈ U0.powerset,
      colP ξ y (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * U (nI M / ellS L b T V) := by
  have hℓ := ellS_pos hL b T V
  have hℓL : ellS L b T V ≤ L := by
    unfold ellS
    exact div_le_self hL.le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_nI b) (one_le_nI T)) (one_le_nI V))
  unfold Pcol
  refine Finset.sum_subset (fun M hM => ?_) fun M _ hM => ?_
  · rw [Finset.mem_powerset]
    refine (subset_primesLe hM).trans ((primesLe_mono ?_).trans hU0)
    have : 0 ≤ 2 * β := by linarith
    exact mul_le_mul_of_nonneg_left hℓL this
  · have h := lt_nI_of_not_mem_fsLe hM
    rw [hU _ (by rw [lt_div_iff₀ hℓ]; linarith), mul_zero]

theorem norm_Pcol_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ} {NU : ℝ}
    (hNU : ∀ x, ‖U x‖ ≤ NU) (β L : ℝ) (b T V : Finset Pr) (y : 𝓞 K) :
    ‖Pcol ξ U β L b T V y‖ ≤ (fsLe (2 * β * ellS L b T V)).card * NU := by
  unfold Pcol
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun M _ => ?_
  rw [norm_mul]
  calc ‖colP ξ y (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M‖ * ‖U (nI M / ellS L b T V)‖ ≤ 1 * NU :=
        mul_le_mul (norm_colP_le _ _ _ _) (hNU _) (norm_nonneg _) zero_le_one
    _ = NU := one_mul NU

theorem re_majorant_nonneg {H : ℝ} (hH : 0 < H) (g : 𝓞 K → ℂ) {B : ℝ} (hg : ∀ u, ‖g u‖ ≤ B) :
    0 ≤ (∑' u : 𝓞 K, g u * conj (g u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))).re := by
  have := sum_sq_le_majorant H hH g hg ∅ (by simp)
  simpa using this

open Classical in
/-- The rows of the transfer's dual sum that can contribute: the triples of `U₀` with
`N(b)N(T)N(V) ≤ βL`, and the pairs `(𝔣, μ) ∈ Fs × E` with `N(μ·pgen(𝔣)²) ≤ Y_{C,d}`. -/
def rowsD (U0 : Finset Pr) (Fs : Finset (Ideal (𝓞 K))) (E : Finset (𝓞 K)) (β H L S F cI : ℝ) :
    Finset RowD :=
  (((triplesOf U0).filter fun t => nI t.1 * nI t.2.1 * nI t.2.2 ≤ β * L) ×ˢ (Fs ×ˢ E)).filter
    fun r => (absNorm (span {r.2.2 * pgen r.2.1 ^ 2}) : ℝ) ≤ Ycd cI S L F H r.1.1 r.1.2.1

theorem Ycd_pos {cI S L F H : ℝ} (hcI : 0 < cI) (hS : 0 < S) (hL : 0 < L) (hF : 0 < F)
    (hH : 0 < H) (b T : Finset Pr) : 0 < Ycd cI S L F H b T := by
  unfold Ycd; have := nI_pos b; have := nI_pos T; positivity

theorem Ycd_le {cI S L F H : ℝ} (hcI : 0 < cI) (hS : 0 < S) (hL : 0 < L) (hF : 0 < F)
    (hH : 0 < H) (b T : Finset Pr) : Ycd cI S L F H b T ≤ cI * S * L * F / H := by
  unfold Ycd
  have hb := one_le_nI b
  have hT := one_le_nI T
  have h1 : 1 ≤ nI b ^ 2 * nI T := by nlinarith [one_le_pow₀ hb (n := 2)]
  rw [div_le_div_iff₀ (by positivity) hH]
  have : 0 < cI * S * L * F := by positivity
  have hH' : H ≤ H * nI b ^ 2 * nI T := by
    have := le_mul_of_one_le_right hH.le h1
    linarith [mul_assoc H (nI b ^ 2) (nI T)]
  exact mul_le_mul_of_nonneg_left hH' this.le

open Classical in
/-- **The column mean square of the rows is at most a multiple of `𝒬`** (the companion paper's
"`Σ_{C,t}Σ_{d∣C}w_{C,d}Σ_{f,h}|P_{C,d,t}(hf^2;U)|^2 ≼ 𝒬_{ξ_1}(U)`", where `A≼B` means `A≪_εD^εB`): for a test function `U`
vanishing beyond `2β`, the enlarged column sums of `rowsD` satisfy
`Σ_r |Σ_n colE(r, n)·U(x_n)|² ≤ C·(c_I·SLF/H)^δ·𝒬_ξ(U)`, through the multiplicity of `y = μf²`
(`sum_pairs_le_mult`) and the majorant (round 307's `sum_sq_le_majorant`). -/
theorem rows_meanSquareD {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {β H L S F cI : ℝ},
      0 ≤ β → 0 < H → 0 < L → 0 < S → 0 < F → 0 < cI →
      ∀ {U0 : Finset Pr}, primesLe (2 * β * L) ⊆ U0 →
      ∀ (Fs : Finset (Ideal (𝓞 K))), (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f) →
      ∀ (E : Finset (𝓞 K)), (∀ μ ∈ E, μ ≠ 0) →
      ∀ (U : ℝ → ℂ), (∀ x, 2 * β < x → U x = 0) → ∀ NU : ℝ, (∀ x, ‖U x‖ ≤ NU) →
      ∑ r ∈ rowsD U0 Fs E β H L S F cI,
          ‖∑ n ∈ rowsD U0 Fs E β H L S F cI ×ˢ U0.powerset, colE ξ H L r n * U (xE L n)‖ ^ 2 ≤
        C * (cI * S * L * F / H) ^ δ * Qform ξ U β H L S F cI := by
  obtain ⟨C, hC0, hC⟩ := sum_pairs_le_mult hδ
  refine ⟨C, hC0, fun ξ β H L S F cI hβ hH hL hS hF hcI U0 hU0 Fs hFs E hE U hU NU hNU => ?_⟩
  set Rows := rowsD U0 Fs E β H L S F cI with hRows
  set Ym := cI * S * L * F / H with hYm
  have hYm0 : 0 < Ym := by positivity
  -- the row sums are `√w_r·P_r(y_r)`
  have hrow : ∀ r ∈ Rows,
      ‖∑ n ∈ Rows ×ˢ U0.powerset, colE ξ H L r n * U (xE L n)‖ ^ 2 =
        wtD H L r * ‖Pcol ξ U β L r.1.1 r.1.2.1 r.1.2.2 (r.2.2 * pgen r.2.1 ^ 2)‖ ^ 2 := by
    intro r hr
    rw [sum_enlarged Rows U0.powerset hr _ fun n hn => by
      rw [colE_eq_zero_of_ne ξ H L r hn, zero_mul]]
    have hw : 0 ≤ wtD H L r := by unfold wtD; have := nI_pos r.1.1; positivity
    have e : ∑ M ∈ U0.powerset, colE ξ H L r (r, M) * U (xE L (r, M)) =
        ((Real.sqrt (wtD H L r) : ℝ) : ℂ) * Pcol ξ U β L r.1.1 r.1.2.1 r.1.2.2
          (r.2.2 * pgen r.2.1 ^ 2) := by
      rw [Pcol_eq_powerset ξ hU hβ hL hU0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun M _ => ?_
      unfold colE xE
      rw [ite_eq_left rfl]
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hw]
  rw [Finset.sum_congr rfl hrow]
  -- regroup by the triple
  set Tr := (triplesOf U0).filter fun t => nI t.1 * nI t.2.1 * nI t.2.2 ≤ β * L with hTr
  set Pr' : (Finset Pr × Finset Pr × Finset Pr) → Finset (Ideal (𝓞 K) × 𝓞 K) := fun t =>
    (Fs ×ˢ E).filter fun p => (absNorm (span {p.2 * pgen p.1 ^ 2}) : ℝ) ≤ Ycd cI S L F H t.1 t.2.1
    with hPr'
  have hsplit : ∑ r ∈ Rows, wtD H L r *
        ‖Pcol ξ U β L r.1.1 r.1.2.1 r.1.2.2 (r.2.2 * pgen r.2.1 ^ 2)‖ ^ 2 =
      ∑ t ∈ Tr, ∑ p ∈ Pr' t, wtD H L (t, p) *
        ‖Pcol ξ U β L t.1 t.2.1 t.2.2 (p.2 * pgen p.1 ^ 2)‖ ^ 2 := by
    rw [hRows]
    unfold rowsD
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_filter]
  rw [hsplit]
  -- the bound for one triple
  have htri : ∀ t ∈ Tr, ∑ p ∈ Pr' t, wtD H L (t, p) *
        ‖Pcol ξ U β L t.1 t.2.1 t.2.2 (p.2 * pgen p.1 ^ 2)‖ ^ 2 ≤
      C * Ym ^ δ * (wtD H L (t, (⊥, 0)) *
        (∑' y : 𝓞 K, Pcol ξ U β L t.1 t.2.1 t.2.2 y * conj (Pcol ξ U β L t.1 t.2.1 t.2.2 y) *
          Majorant.Phi (σO y / (Real.sqrt (Ycd cI S L F H t.1 t.2.1) : ℂ))).re) := by
    intro t _
    set Yt := Ycd cI S L F H t.1 t.2.1 with hYt
    have hYt0 : 0 < Yt := Ycd_pos hcI hS hL hF hH _ _
    have hw : wtD H L (t, (⊥, 0)) = 2 * H * nI t.1 / (Real.sqrt 3 * L) := rfl
    have hw' : ∀ p : Ideal (𝓞 K) × 𝓞 K, wtD H L (t, p) = wtD H L (t, (⊥, 0)) := fun p => rfl
    have hw0 : 0 ≤ wtD H L (t, (⊥, 0)) := by rw [hw]; have := nI_pos t.1; positivity
    simp_rw [hw']
    rw [← Finset.mul_sum]
    have hB := norm_Pcol_le ξ hNU β L t.1 t.2.1 t.2.2
    have hm := hC (Pr' t) Yt (fun p hp => by
      rw [hPr', Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨(hFs p.1 hp.1.1).1, (hFs p.1 hp.1.1).2, hE p.2 hp.1.2, hp.2⟩)
      (fun y => ‖Pcol ξ U β L t.1 t.2.1 t.2.2 y‖ ^ 2) (fun y => sq_nonneg _)
    have hmaj := sum_sq_le_majorant Yt hYt0 (fun y => Pcol ξ U β L t.1 t.2.1 t.2.2 y) hB
      ((Pr' t).image fun p => p.2 * pgen p.1 ^ 2) (fun y hy => by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
        rw [hPr', Finset.mem_filter] at hp
        exact hp.2)
    have hre := re_majorant_nonneg hYt0 (fun y => Pcol ξ U β L t.1 t.2.1 t.2.2 y) hB
    have hYle : Yt ^ δ ≤ Ym ^ δ :=
      Real.rpow_le_rpow hYt0.le (Ycd_le hcI hS hL hF hH _ _) hδ.le
    calc wtD H L (t, (⊥, 0)) * ∑ p ∈ Pr' t, ‖Pcol ξ U β L t.1 t.2.1 t.2.2 (p.2 * pgen p.1 ^ 2)‖ ^ 2
        ≤ wtD H L (t, (⊥, 0)) * (C * Yt ^ δ *
            ∑ y ∈ (Pr' t).image (fun p => p.2 * pgen p.1 ^ 2),
              ‖Pcol ξ U β L t.1 t.2.1 t.2.2 y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hm hw0
      _ ≤ wtD H L (t, (⊥, 0)) * (C * Ym ^ δ *
            (∑' y : 𝓞 K, Pcol ξ U β L t.1 t.2.1 t.2.2 y * conj (Pcol ξ U β L t.1 t.2.1 t.2.2 y) *
              Majorant.Phi (σO y / (Real.sqrt Yt : ℂ))).re) := by
          gcongr
      _ = C * Ym ^ δ * (wtD H L (t, (⊥, 0)) *
            (∑' y : 𝓞 K, Pcol ξ U β L t.1 t.2.1 t.2.2 y * conj (Pcol ξ U β L t.1 t.2.1 t.2.2 y) *
              Majorant.Phi (σO y / (Real.sqrt Yt : ℂ))).re) := by ring
  refine (Finset.sum_le_sum htri).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the triples lie in the index set of `𝒬`
  unfold Qform
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) fun t _ _ => ?_
  · rw [hTr, Finset.mem_filter] at ht
    obtain ⟨ht1, ht2⟩ := ht
    unfold triplesOf at ht1
    rw [Finset.mem_filter] at ht1
    unfold qTriples
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    have hb := one_le_nI t.1
    have hT := one_le_nI t.2.1
    have hV := one_le_nI t.2.2
    have h2 : β * L ≤ 2 * β * L := by nlinarith
    have hbT : 1 ≤ nI t.1 * nI t.2.1 := one_le_mul_of_one_le_of_one_le hb hT
    have hb0 : 0 ≤ nI t.1 := le_trans zero_le_one hb
    have hT0 : 0 ≤ nI t.2.1 := le_trans zero_le_one hT
    have hV0 : 0 ≤ nI t.2.2 := le_trans zero_le_one hV
    have e1 : nI t.1 ≤ nI t.1 * nI t.2.1 * nI t.2.2 :=
      le_mul_of_one_le_right hb0 (one_le_mul_of_one_le_of_one_le hT hV) |>.trans_eq (mul_assoc _ _ _).symm
    have e2 : nI t.2.1 ≤ nI t.1 * nI t.2.1 * nI t.2.2 := by
      have := le_mul_of_one_le_left hT0 (one_le_mul_of_one_le_of_one_le hb hV)
      linarith [mul_comm (nI t.1) (nI t.2.1), mul_assoc (nI t.2.1) (nI t.1) (nI t.2.2),
        mul_assoc (nI t.1) (nI t.2.2) (nI t.2.1), mul_comm (nI t.2.2) (nI t.2.1)]
    have e3 : nI t.2.2 ≤ nI t.1 * nI t.2.1 * nI t.2.2 := le_mul_of_one_le_left hV0 hbT
    refine ⟨⟨mem_fsLe_of_nI_le ?_, mem_fsLe_of_nI_le ?_, mem_fsLe_of_nI_le ?_⟩, ht1.2.1, ht1.2.2,
      ht2.trans h2⟩
    · linarith
    · linarith
    · linarith
  · have hw0 : 0 ≤ 2 * H * nI t.1 / (Real.sqrt 3 * L) := by have := nI_pos t.1; positivity
    exact mul_nonneg hw0 (re_majorant_nonneg (Ycd_pos hcI hS hL hF hH _ _) _
      (norm_Pcol_le ξ hNU β L t.1 t.2.1 t.2.2))

open Classical in
theorem mem_rowsD {U0 : Finset Pr} {Fs : Finset (Ideal (𝓞 K))} {E : Finset (𝓞 K)}
    {β H L S F cI : ℝ} {r : RowD} :
    r ∈ rowsD U0 Fs E β H L S F cI ↔
      ((r.1 ∈ triplesOf U0 ∧ nI r.1.1 * nI r.1.2.1 * nI r.1.2.2 ≤ β * L) ∧
        r.2.1 ∈ Fs ∧ r.2.2 ∈ E) ∧
        (absNorm (span {r.2.2 * pgen r.2.1 ^ 2}) : ℝ) ≤ Ycd cI S L F H r.1.1 r.1.2.1 := by
  unfold rowsD
  simp only [Finset.mem_filter, Finset.mem_product]

theorem ARowD_ge {H L : ℝ} (hH : 0 ≤ H) (hL : 0 < L) {r : RowD} (hμ : r.2.2 ≠ 0) :
    4 * H / (3 * L ^ 2) ≤ ARowD H L r := by
  unfold ARowD
  have hN := one_le_absNorm_span hμ
  have hb := one_le_nI r.1.1
  have hT := one_le_nI r.1.2.1
  have h1 : 1 ≤ (absNorm (span {r.2.2}) : ℝ) * nI r.1.1 ^ 2 * nI r.1.2.1 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN (one_le_pow₀ hb)) hT
  rw [div_le_div_iff_of_pos_right (by positivity)]
  have h4 : 0 ≤ 4 * H := by positivity
  calc 4 * H = 4 * H * 1 := (mul_one _).symm
    _ ≤ 4 * H * ((absNorm (span {r.2.2}) : ℝ) * nI r.1.1 ^ 2 * nI r.1.2.1) :=
        mul_le_mul_of_nonneg_left h1 h4
    _ = _ := by ring

/-- **A bump** equal to `1` on `[α, β]` with topological support in `[α/2, 2β]`, for `0 < α ≤ β`
(round 310's `exists_bump` with the paper's `I_* = [u/2, 2v]`). -/
theorem exists_bump_one {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ V : ℝ → ℂ, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ tsupport V ⊆ Set.Ioi 0 ∧
      tsupport V ⊆ Set.Icc (α / 2) (2 * β) ∧ ∀ y, α ≤ y → y ≤ β → V y = 1 := by
  let f : ContDiffBump ((α + β) / 2) :=
    ⟨(β - α) / 2 + α / 8, (β - α) / 2 + α / 4, by linarith, by linarith⟩
  refine ⟨fun x => ((f x : ℝ) : ℂ), ofRealCLM.contDiff.comp f.contDiff, ?_, ?_, ?_, ?_⟩
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero
  · intro x hx
    have hx' : x ∈ tsupport f := tsupport_comp_subset Complex.ofReal_zero _ hx
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx'
    have := neg_abs_le (x - (α + β) / 2)
    show 0 < x
    change |x - (α + β) / 2| ≤ (β - α) / 2 + α / 4 at hx'
    linarith
  · intro x hx
    have hx' : x ∈ tsupport f := tsupport_comp_subset Complex.ofReal_zero _ hx
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx'
    change |x - (α + β) / 2| ≤ (β - α) / 2 + α / 4 at hx'
    have h1 := neg_abs_le (x - (α + β) / 2)
    have h2 := le_abs_self (x - (α + β) / 2)
    exact ⟨by linarith, by linarith⟩
  · intro y hy1 hy2
    have : f y = 1 := f.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq]
      change |y - (α + β) / 2| ≤ (β - α) / 2 + α / 8
      rw [abs_le]
      constructor <;> linarith)
    simp [this]

open Classical in
/-- **The bound for one pair of characters** (the companion paper's application of its Lemma B.2 in
the proof of Lemma 7.1, through round 317's `bilinear_dual_bound_unif` with the enlarged columns of
`rowSumD_eq_bilinear`): if `𝒬_ξ(U) ≤ M_Q·N_U²` for every test function `U` vanishing outside
`[α/2, 2β]` (the paper's `I_*`) with its first `J` derivatives bounded by `N_U`, then the rows of `rowsD` contribute at
most `K·N_W²·A_min^{−σ}·(c_I·SLF/H)^δ·M_Q`, with `A_min = 4H/(3L²)`. -/
theorem blockD_bound {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (J : ℕ) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) :
    ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (W : ℝ → ℂ),
      ContDiff ℝ ∞ W → (∀ x, x < α ∨ β < x → W x = 0) → ∀ NW : ℝ,
      (∀ j ≤ 2 * J + 2, ∀ x, ‖iteratedDeriv j W x‖ ≤ NW) →
      ∀ {H L S F cI : ℝ}, 0 < H → 0 < L → 0 < S → 0 < F → 0 < cI →
      ∀ {U0 : Finset Pr}, primesLe (2 * β * L) ⊆ U0 →
      ∀ (Fs : Finset (Ideal (𝓞 K))), (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f) →
      ∀ (E : Finset (𝓞 K)), (∀ μ ∈ E, μ ≠ 0) →
      ∀ MQ : ℝ, 0 ≤ MQ →
      (∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ U : ℝ → ℂ, ContDiff ℝ ∞ U →
        (∀ x, x < α / 2 ∨ 2 * β < x → U x = 0) → ∀ NU : ℝ,
        (∀ j ≤ J, ∀ x, ‖iteratedDeriv j U x‖ ≤ NU) → Qform ξ U β H L S F cI ≤ MQ * NU ^ 2) →
      ‖∑ r ∈ rowsD U0 Fs E β H L S F cI,
          ∑ M1 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
            ∑ M2 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
              rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2‖ ≤
        Kt * NW ^ 2 * (4 * H / (3 * L ^ 2)) ^ (-σ) * (cI * S * L * F / H) ^ δ * MQ := by
  obtain ⟨V, hV, hVc, hVp, hVs, hV1⟩ := exists_bump_one hα hαβ
  obtain ⟨R, hR0, hR⟩ := exists_dualG_eq_zero
  obtain ⟨Kb, hKb0, hKb⟩ := MellinSep.bilinear_dual_bound_unif hα hαβ V hV hVc hVp
    (ρ0 := 1) (ρ1 := 1) one_pos (fun y h1 h2 => hV1 y (by rwa [div_one] at h1)
      (by rwa [div_one] at h2)) J dualG dualG_contDiff dualG_bounded hR hσ
  obtain ⟨Cw, hCw0, hCw⟩ := MellinSep.W0c_unif hα hαβ (2 * J + 2)
  obtain ⟨Cm, hCm0, hCm⟩ := rows_meanSquareD hδ
  have hβ : 0 ≤ β := le_trans hα.le hαβ
  refine ⟨Kb * Cw ^ 2 * Cm, by positivity, fun ξ1 ξ2 W hW hWs NW hNW H L S F cI hH hL hS hF hcI
    U0 hU0 Fs hFs E hE MQ hMQ hQ => ?_⟩
  obtain ⟨hW0, hW0d⟩ := hCw W hW hWs NW hNW
  set Rows := rowsD U0 Fs E β H L S F cI with hRows
  set Ym := cI * S * L * F / H with hYm
  have hYm0 : 0 < Ym := by positivity
  rw [Finset.sum_congr rfl fun r hr => rowSumD_eq_bilinear W hL hH.le ξ1 ξ2 Rows hr]
  have hcol : ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ U : ℝ → ℂ, ContDiff ℝ ∞ U →
      tsupport U ⊆ tsupport V → ∀ N : ℝ, (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
      ∑ r ∈ Rows, ‖∑ n ∈ Rows ×ˢ U0.powerset, colE ξ H L r n * U (xE L n)‖ ^ 2 ≤
        (Cm * Ym ^ δ * MQ) * N ^ 2 := by
    intro ξ U hU hUs N hN
    have hUv : ∀ x, x < α / 2 ∨ 2 * β < x → U x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => by
        have := hVs (hUs h)
        rw [Set.mem_Icc] at this
        rcases hx with hx | hx <;> linarith [this.1, this.2]
    have hUN : ∀ x, ‖U x‖ ≤ N := fun x => by
      have := hN 0 (Nat.zero_le _) x; rwa [iteratedDeriv_zero] at this
    have h1 := hCm ξ hβ hH hL hS hF hcI hU0 Fs hFs E hE U (fun x hx => hUv x (Or.inr hx)) N hUN
    have h2 := hQ ξ U hU hUv N hN
    calc ∑ r ∈ Rows, ‖∑ n ∈ Rows ×ˢ U0.powerset, colE ξ H L r n * U (xE L n)‖ ^ 2
        ≤ Cm * Ym ^ δ * Qform ξ U β H L S F cI := h1
      _ ≤ Cm * Ym ^ δ * (MQ * N ^ 2) := by gcongr
      _ = (Cm * Ym ^ δ * MQ) * N ^ 2 := by ring
  have hbound := hKb (MellinSep.W0c W) hW0 (fun y hy => MellinSep.W0c_eq_zero hWs hy) (Cw * NW)
    hW0d Rows (Rows ×ˢ U0.powerset) (colE ξ1 H L) (colE ξ2 H L) (xE L)
    (fun n _ => xE_pos hL n) (Cm * Ym ^ δ * MQ) (by positivity) (hcol ξ1) (hcol ξ2)
    (fun _ => 1) (fun _ _ => ⟨le_rfl, le_rfl⟩) (wRowD ξ1 ξ2) (fun r _ => norm_wRowD_le ξ1 ξ2 r)
    (ARowD H L) (4 * H / (3 * L ^ 2)) (by positivity)
    (fun r hr => ARowD_ge hH.le hL (hE _ (mem_rowsD.1 hr).1.2.2))
  calc _ ≤ Kb * (Cw * NW) ^ 2 * (4 * H / (3 * L ^ 2)) ^ (-σ) * (Cm * Ym ^ δ * MQ) := hbound
    _ = Kb * Cw ^ 2 * Cm * NW ^ 2 * (4 * H / (3 * L ^ 2)) ^ (-σ) * Ym ^ δ * MQ := by ring

/-! ### A fixed support radius for `Φ̂` -/

/-- A support radius of the dual weight: `dualG` vanishes on `[RΦ, ∞)` (round 303's
`exists_dualG_eq_zero`, with the radius fixed once). -/
def RΦ : ℝ := Classical.choose exists_dualG_eq_zero

theorem RΦ_pos : 0 < RΦ := (Classical.choose_spec exists_dualG_eq_zero).1

theorem dualG_eq_zero_of_ge {ρ : ℝ} (h : RΦ ≤ ρ) : dualG ρ = 0 :=
  (Classical.choose_spec exists_dualG_eq_zero).2 ρ h

/-! ### The zero frequency -/

theorem fsLe_mono {x y : ℝ} (h : x ≤ y) : fsLe x ⊆ fsLe y := fun _A hA =>
  mem_fsLe.2 ((mem_fsLe.1 hA).trans (Nat.floor_mono h))

/-- **The zero frequency of one row** (the companion paper's zero frequency `Z`, which it bounds by
`𝓗‖W‖²_∞`, for one row before the normalization `1/(LF)`):
for `W` vanishing beyond `β`, bounded by `N` and `1 ≤ L`, the zero frequency of `dualMS_rowcol` has
norm at most `(2κ+5)·max(β,1)L·N²·2H/√3·|Φ̂(0)|`. -/
theorem zero_rowD_le {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {N : ℝ}
    (hN : ∀ x, ‖W x‖ ≤ N) {L H : ℝ} (hL : 1 ≤ L) (hH : 0 ≤ H) (U0 : Finset Pr) (f : 𝓞 K) :
    ‖∑ A ∈ U0.powerset, (chiS A f ^ 4 * conj (chiS A f ^ 4)) *
        (W (nI A / L) * conj (W (nI A / L))) *
        ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0‖ ≤
      (2 * kappa + 5) * (max β 1 * L) * (N ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖)) := by
  classical
  have hL0 : 0 < L := by linarith
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  set g : Finset Pr → ℂ := fun A => (chiS A f ^ 4 * conj (chiS A f ^ 4)) *
      (W (nI A / L) * conj (W (nI A / L))) *
      ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 with hg
  have hfilt : ∑ A ∈ U0.powerset, g A = ∑ A ∈ U0.powerset.filter (fun A => nI A ≤ β * L), g A := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    split_ifs with h
    · rfl
    · have : W (nI A / L) = 0 := hW _ (by rw [lt_div_iff₀ hL0]; linarith [not_le.1 h])
      simp [hg, this]
  have hterm : ∀ A, ‖g A‖ ≤ N ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖) := by
    intro A
    simp only [hg]
    rw [← Finset.sum_mul, sum_kap_empty]
    obtain ⟨h0, h1⟩ := prod_one_sub_inv_mem A
    have hc1 : ‖chiS A f ^ 4 * conj (chiS A f ^ 4)‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj, norm_pow]
      have := norm_chiS_le A f
      have h4 : ‖chiS A f‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) this
      calc ‖chiS A f‖ ^ 4 * ‖chiS A f‖ ^ 4 ≤ 1 * 1 := mul_le_mul h4 h4 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    have hc2 : ‖W (nI A / L) * conj (W (nI A / L))‖ ≤ N ^ 2 := by
      rw [norm_mul, RCLike.norm_conj, sq]
      exact mul_le_mul (hN _) (hN _) (norm_nonneg _) hN0
    have hc3 : ‖((2 * H / Real.sqrt 3 * ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) : ℝ) : ℂ)‖ ≤
        2 * H / Real.sqrt 3 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc 2 * H / Real.sqrt 3 * ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) ≤
            2 * H / Real.sqrt 3 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := mul_one _
    have hc4 : ‖((2 * H / Real.sqrt 3 * ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) : ℝ) : ℂ) * dualG 0‖ ≤
        2 * H / Real.sqrt 3 * ‖dualG 0‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hc3 (norm_nonneg _)
    calc _ ≤ ‖chiS A f ^ 4 * conj (chiS A f ^ 4)‖ * ‖W (nI A / L) * conj (W (nI A / L))‖ *
          ‖((2 * H / Real.sqrt 3 * ∏ P ∈ A, (1 - 1 / (absNorm P.1 : ℝ)) : ℝ) : ℂ) * dualG 0‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * N ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖) := by gcongr
      _ = N ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖) := by ring
  have hcard : ((U0.powerset.filter (fun A => nI A ≤ β * L)).card : ℝ) ≤
      (2 * kappa + 5) * (max β 1 * L) := by
    have hsub : U0.powerset.filter (fun A => nI A ≤ β * L) ⊆ fsLe (max β 1 * L) := fun A hA =>
      fsLe_mono (mul_le_mul_of_nonneg_right (le_max_left β 1) hL0.le)
        (mem_fsLe_of_nI_le (Finset.mem_filter.1 hA).2)
    calc ((U0.powerset.filter (fun A => nI A ≤ β * L)).card : ℝ) ≤ (fsLe (max β 1 * L)).card := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (2 * kappa + 5) * (max β 1 * L) :=
          card_fsLe_le (one_le_mul_of_one_le_of_one_le (le_max_right β 1) hL)
  rw [hfilt]
  calc ‖∑ A ∈ U0.powerset.filter (fun A => nI A ≤ β * L), g A‖
      ≤ ∑ A ∈ U0.powerset.filter (fun A => nI A ≤ β * L), ‖g A‖ := norm_sum_le _ _
    _ ≤ ∑ _A ∈ U0.powerset.filter (fun A => nI A ≤ β * L),
          N ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖) := Finset.sum_le_sum fun A _ => hterm A
    _ = ((U0.powerset.filter (fun A => nI A ≤ β * L)).card : ℝ) *
          (N ^ 2 * (2 * H / Real.sqrt 3 * ‖dualG 0‖)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

/-! ### The rows of all the `f` -/

theorem norm_colSum_le_card (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β' : ℝ}
    (hW : ∀ x, β' < x → W x = 0) {N : ℝ} (hN : ∀ x, ‖W x‖ ≤ N) {X : ℝ} (hX : 0 < X)
    {U : Finset Pr} (hU : primesLe (β' * X) ⊆ U) (k f : 𝓞 K) :
    ‖colSum ξ W X 1 k f‖ ≤ U.powerset.card * N := by
  rw [colSum_eq_powerset_one ξ hW hX hU k f]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun M _ => ?_
  rw [norm_mul, norm_mul, norm_mul, norm_pow]
  have h1 := norm_aXi_le ξ (idl M)
  have h2 := norm_chiS_le M f
  have h3 := norm_chiS_le M k
  have h4 : ‖chiS M f‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) h2
  have h5 := hN (nI M / X)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  calc ‖aXi ξ (idl M)‖ * ‖chiS M f‖ ^ 4 * ‖W (nI M / X)‖ * ‖chiS M k‖ ≤ 1 * 1 * N * 1 := by
        gcongr
    _ = N := by ring

open Classical in
/-- **The rows of all the `f` in one sum**: `Σ_{f∈Fs}` of the nonzero frequencies of
`dualMS_rowcol`, for one pair of characters, is the sum over the rows of `rowsD`. The other rows
vanish: those with `N(b)N(T)N(V) > βL` (`rcDual_eq_zero_of_large_bTV`) and those beyond `Y_{C,d}`
(`rcDual_eq_zero_of_large_mu`). -/
theorem sum_f_eq_rowsD {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {L H S F cI : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hF : 0 < F) (hS : L * F ≤ S) (hcI : 3 * β ^ 2 * RΦ ^ 2 ≤ cI)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U0 : Finset Pr) (Fs : Finset (Ideal (𝓞 K)))
    (hFs : ∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ (absNorm f : ℝ) < 2 * F) (E : Finset (𝓞 K)) :
    ∑ f ∈ Fs, ∑ b ∈ U0.powerset, ∑ T ∈ (U0 \ b).powerset, ∑ V ∈ (U0 \ (b ∪ T)).powerset,
        ∑ μ ∈ E, ∑ M1 ∈ ((U0 \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U0 \ (b ∪ T)) \ V).powerset,
          rcDual W L H (pgen f) ξ1 ξ2 b T V μ M1 M2 =
      ∑ r ∈ rowsD U0 Fs E β H L S F cI,
        ∑ M1 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
          ∑ M2 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
            rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 := by
  set G : RowD → ℂ := fun r => ∑ M1 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
    ∑ M2 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
      rcDual W L H (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 with hG
  have h1 : ∀ f ∈ Fs, ∑ b ∈ U0.powerset, ∑ T ∈ (U0 \ b).powerset, ∑ V ∈ (U0 \ (b ∪ T)).powerset,
      ∑ μ ∈ E, ∑ M1 ∈ ((U0 \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U0 \ (b ∪ T)) \ V).powerset,
        rcDual W L H (pgen f) ξ1 ξ2 b T V μ M1 M2 =
      ∑ t ∈ triplesOf U0, ∑ μ ∈ E, G (t, (f, μ)) := fun f _ =>
    sum_nested_eq_triplesOf U0 (fun b T V => ∑ μ ∈ E,
      ∑ M1 ∈ ((U0 \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U0 \ (b ∪ T)) \ V).powerset,
        rcDual W L H (pgen f) ξ1 ξ2 b T V μ M1 M2)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∑ t ∈ triplesOf U0, ∑ f ∈ Fs, ∑ μ ∈ E, G (t, (f, μ)) =
      ∑ r ∈ triplesOf U0 ×ˢ (Fs ×ˢ E), G r := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_product]
  rw [h2]
  have hsub : rowsD U0 Fs E β H L S F cI ⊆ triplesOf U0 ×ˢ (Fs ×ˢ E) := by
    intro r hr
    obtain ⟨⟨⟨ht, _⟩, hf, hμ⟩, _⟩ := mem_rowsD.1 hr
    exact Finset.mem_product.2 ⟨ht, Finset.mem_product.2 ⟨hf, hμ⟩⟩
  symm
  refine Finset.sum_subset hsub fun r hr hr' => ?_
  rw [Finset.mem_product, Finset.mem_product] at hr
  obtain ⟨ht, hf, hμ⟩ := hr
  rw [mem_rowsD] at hr'
  by_cases hbig : nI r.1.1 * nI r.1.2.1 * nI r.1.2.2 ≤ β * L
  · have hy : ¬ (absNorm (span {r.2.2 * pgen r.2.1 ^ 2}) : ℝ) ≤ Ycd cI S L F H r.1.1 r.1.2.1 :=
      fun h => hr' ⟨⟨⟨ht, hbig⟩, hf, hμ⟩, h⟩
    rw [not_le] at hy
    obtain ⟨h6, hfF⟩ := hFs r.2.1 hf
    have hNf0 : (0 : ℝ) ≤ absNorm r.2.1 := Nat.cast_nonneg _
    have hNμ0 : (0 : ℝ) ≤ absNorm (span {r.2.2}) := Nat.cast_nonneg _
    have hyF : Ycd cI S L F H r.1.1 r.1.2.1 < (absNorm (span {r.2.2}) : ℝ) * (4 * F ^ 2) := by
      have hsq : (absNorm r.2.1 : ℝ) ^ 2 ≤ 4 * F ^ 2 := by nlinarith
      rw [absNorm_mul_pgen_sq h6] at hy
      calc Ycd cI S L F H r.1.1 r.1.2.1 < (absNorm (span {r.2.2}) : ℝ) * (absNorm r.2.1 : ℝ) ^ 2 := hy
        _ ≤ (absNorm (span {r.2.2}) : ℝ) * (4 * F ^ 2) := mul_le_mul_of_nonneg_left hsq hNμ0
    refine Finset.sum_eq_zero fun M1 hM1 => Finset.sum_eq_zero fun M2 hM2 => ?_
    exact rcDual_eq_zero_of_large_mu hW hL hH hF hS RΦ_pos (fun ρ h => dualG_eq_zero_of_ge h) hcI
      _ ξ1 ξ2 _ _ _ _ (disjoint_of_mem_powerset_sdiff hM1) (disjoint_of_mem_powerset_sdiff hM2) hyF
  · rw [not_le] at hbig
    exact Finset.sum_eq_zero fun M1 _ => Finset.sum_eq_zero fun M2 _ =>
      rcDual_eq_zero_of_large_bTV hW hL H _ ξ1 ξ2 _ M1 M2 hbig

theorem norm_pairCoeff_xi_le (ξ ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) :
    ‖pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹‖ ≤ 1 :=
  norm_pairCoeff_le (pairPsiXi ξ) (fun c1 c2 => norm_pairPsiXi_le ξ _ _ c1.isUnit c2.isUnit) _ _

open Classical in
/-- **The companion paper's Lemma 7.1** ("If `M≥0` satisfies `𝒬_{ξ_1}(U)≤M‖U‖²_{C^j(I_*)}` for every
`U∈C_c^∞(I_*)` and every `ξ_1`, then `𝒜(W)≪D^{ε_0}(Σ+M)‖W‖²_{C^{2j+4}(I)}`"), in the pilot's form:
for `W` supported in `[α, β]` with its first `2J+2` derivatives bounded by `N_W`, if
`𝒬_{ξ₁}(U) ≤ M_Q·N_U²` for every `ξ₁` and every test function `U` vanishing outside `[α/2, 2β]` (the
paper's `I_* = [u/2, 2v]`) with its first `J` derivatives bounded by `N_U`, then the row sum of round 314 satisfies
`E ≤ K₁·N_W²·HLF + K₂·N_W²·(4H/(3L²))^{−σ}·(c_I·SLF/H)^δ·M_Q`. The first term is the zero frequency
(the paper's `𝓗‖W‖²_∞`, times `LF`); the second is the bilinear bound of `blockD_bound` over the pairs
of characters modulo `4`, with the losses `A_min^{−σ}` and `Y^δ` of the pilot's separation and
multiplicity count in place of the paper's `D^{ε_0}`. -/
theorem first_transfer {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (J : ℕ) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
      ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (W : ℝ → ℂ), ContDiff ℝ ∞ W →
      (∀ x, x < α ∨ β < x → W x = 0) → ∀ NW : ℝ,
      (∀ j ≤ 2 * J + 2, ∀ x, ‖iteratedDeriv j W x‖ ≤ NW) →
      ∀ {Hh L S F cI : ℝ}, 1 ≤ Hh → 1 ≤ L → 1 ≤ F → L * F ≤ S →
      3 * β ^ 2 * RΦ ^ 2 ≤ cI → 0 < cI → ∀ MQ : ℝ, 0 ≤ MQ →
      (∀ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ U : ℝ → ℂ, ContDiff ℝ ∞ U →
        (∀ x, x < α / 2 ∨ 2 * β < x → U x = 0) → ∀ NU : ℝ,
        (∀ j ≤ J, ∀ x, ‖iteratedDeriv j U x‖ ≤ NU) → Qform ξ1 U β Hh L S F cI ≤ MQ * NU ^ 2) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) →
        rowE ξ W L Fs T ≤ K1 * NW ^ 2 * (Hh * L * F) +
          K2 * NW ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-σ) * (cI * S * L * F / Hh) ^ δ * MQ := by
  obtain ⟨Kt, hKt0, hKt⟩ := blockD_bound hα hαβ J hσ hδ
  set nξ : ℝ := (Fintype.card (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) : ℝ) with hnξ
  have hk := kappa_pos
  refine ⟨2 * (2 * kappa + 5) * ((2 * kappa + 5) * max β 1) * (2 / Real.sqrt 3 * ‖dualG 0‖),
    nξ ^ 2 * Kt, by positivity, by positivity, fun ξ W hW hWs NW hNW Hh L S F cI hH hL hF hS hcI
      hcI0 MQ hMQ hQ Fs T hFs hT => ?_⟩
  have hWβ : ∀ x, β < x → W x = 0 := fun x hx => hWs x (Or.inr hx)
  have hNW' : ∀ x, ‖W x‖ ≤ NW := fun x => by
    have := hNW 0 (Nat.zero_le _) x; rwa [iteratedDeriv_zero] at this
  have hNW0 : 0 ≤ NW := (norm_nonneg _).trans (hNW' 0)
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < Hh := by linarith
  have hF0 : 0 < F := by linarith
  have hS0 : 0 < S := lt_of_lt_of_le (mul_pos hL0 hF0) hS
  set U0 := primesLe (2 * β * L) with hU0def
  have hU : primesLe (β * L) ⊆ U0 := primesLe_mono (by nlinarith)
  set Y0 := 3 * RΦ ^ 2 * (β * L) ^ 2 / (4 * Hh) with hY0def
  have hY0 : 3 * RΦ ^ 2 * (β * L) ^ 2 ≤ 4 * Hh * Y0 := by
    rw [hY0def, mul_div_cancel₀ _ (by positivity)]
  set E := (eltsLe Y0).erase 0 with hEdef
  have hE : ∀ μ ∈ E, μ ≠ 0 := fun μ hμ => Finset.ne_of_mem_erase hμ
  set Zf : Ideal (𝓞 K) → ℂ := fun f => ∑ A ∈ U0.powerset,
    (chiS A (pgen f) ^ 4 * conj (chiS A (pgen f) ^ 4)) * (W (nI A / L) * conj (W (nI A / L))) *
      ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap Hh ∅ ∅ T : ℂ) * dualG 0 with hZf
  set Nf : Ideal (𝓞 K) → MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ →
      MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ → ℂ := fun f ξ1 ξ2 =>
    ∑ b ∈ U0.powerset, ∑ T ∈ (U0 \ b).powerset, ∑ V ∈ (U0 \ (b ∪ T)).powerset, ∑ μ ∈ E,
      ∑ M1 ∈ ((U0 \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U0 \ (b ∪ T)) \ V).powerset,
        rcDual W L Hh (pgen f) ξ1 ξ2 b T V μ M1 M2 with hNf
  have hid : ∀ f : Ideal (𝓞 K), ∑' u : 𝓞 K, colSum ξ W L 1 u (pgen f) *
      conj (colSum ξ W L 1 u (pgen f)) * Majorant.Phi (σO u / (Real.sqrt Hh : ℂ)) =
      Zf f + ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ * Nf f ξ1 ξ2 := fun f =>
    dualMS_rowcol ξ hWβ hL0 hU (pgen f) hH0 RΦ_pos (fun _ h => dualG_eq_zero_of_ge h) hY0
  -- the majorant, row by row
  have hstep1 : rowE ξ W L Fs T ≤ ∑ f ∈ Fs, (∑' u : 𝓞 K, colSum ξ W L 1 u (pgen f) *
      conj (colSum ξ W L 1 u (pgen f)) * Majorant.Phi (σO u / (Real.sqrt Hh : ℂ))).re := by
    unfold rowE
    exact Finset.sum_le_sum fun f _ => sum_sq_le_majorant Hh hH0
      (fun u => colSum ξ W L 1 u (pgen f)) (fun k => norm_colSum_le_card ξ hWβ hNW' hL0 hU k _) T
      (fun k hk => (hT k hk).2)
  -- the zero frequency and the nonzero frequencies
  have hreorder : ∑ f ∈ Fs, ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
      ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ * Nf f ξ1 ξ2 =
      ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ * ∑ f ∈ Fs, Nf f ξ1 ξ2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ1 _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ξ2 _ => (Finset.mul_sum _ _ _).symm
  have hstep2 : ∑ f ∈ Fs, (∑' u : 𝓞 K, colSum ξ W L 1 u (pgen f) *
      conj (colSum ξ W L 1 u (pgen f)) * Majorant.Phi (σO u / (Real.sqrt Hh : ℂ))).re ≤
      ‖∑ f ∈ Fs, Zf f‖ + ‖∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ * ∑ f ∈ Fs, Nf f ξ1 ξ2‖ := by
    simp_rw [hid]
    rw [← Complex.re_sum, Finset.sum_add_distrib, hreorder]
    exact (Complex.re_le_norm _).trans (norm_add_le _ _)
  -- the zero frequency
  have hzero : ‖∑ f ∈ Fs, Zf f‖ ≤ 2 * (2 * kappa + 5) * ((2 * kappa + 5) * max β 1) *
      (2 / Real.sqrt 3 * ‖dualG 0‖) * NW ^ 2 * (Hh * L * F) := by
    have hcardF := card_rows_le hF hFs
    have hz : ∀ f ∈ Fs, ‖Zf f‖ ≤ (2 * kappa + 5) * (max β 1 * L) *
        (NW ^ 2 * (2 * Hh / Real.sqrt 3 * ‖dualG 0‖)) := fun f _ =>
      zero_rowD_le hWβ hNW' hL hH0.le U0 (pgen f)
    calc ‖∑ f ∈ Fs, Zf f‖ ≤ ∑ f ∈ Fs, ‖Zf f‖ := norm_sum_le _ _
      _ ≤ ∑ _f ∈ Fs, (2 * kappa + 5) * (max β 1 * L) *
            (NW ^ 2 * (2 * Hh / Real.sqrt 3 * ‖dualG 0‖)) := Finset.sum_le_sum hz
      _ = (Fs.card : ℝ) * ((2 * kappa + 5) * (max β 1 * L) *
            (NW ^ 2 * (2 * Hh / Real.sqrt 3 * ‖dualG 0‖))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (2 * kappa + 5) * F) * ((2 * kappa + 5) * (max β 1 * L) *
            (NW ^ 2 * (2 * Hh / Real.sqrt 3 * ‖dualG 0‖))) := by
          gcongr
      _ = 2 * (2 * kappa + 5) * ((2 * kappa + 5) * max β 1) *
            (2 / Real.sqrt 3 * ‖dualG 0‖) * NW ^ 2 * (Hh * L * F) := by ring
  -- the nonzero frequencies
  have hblock : ∀ ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ‖∑ f ∈ Fs, Nf f ξ1 ξ2‖ ≤
      Kt * NW ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-σ) * (cI * S * L * F / Hh) ^ δ * MQ := by
    intro ξ1 ξ2
    have heq : ∑ f ∈ Fs, Nf f ξ1 ξ2 = ∑ r ∈ rowsD U0 Fs E β Hh L S F cI,
        ∑ M1 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
          ∑ M2 ∈ ((U0 \ (r.1.1 ∪ r.1.2.1)) \ r.1.2.2).powerset,
            rcDual W L Hh (pgen r.2.1) ξ1 ξ2 r.1.1 r.1.2.1 r.1.2.2 r.2.2 M1 M2 :=
      sum_f_eq_rowsD hWβ hL0 hH0 hF0 hS hcI ξ1 ξ2 U0 Fs
        (fun f hf => ⟨(hFs f hf).1, (hFs f hf).2.2.2⟩) E
    rw [heq]
    exact hKt ξ1 ξ2 W hW hWs NW hNW hH0 hL0 hS0 hF0 hcI0 le_rfl Fs
      (fun f hf => ⟨(hFs f hf).1, (hFs f hf).2.1⟩) E hE MQ hMQ hQ
  have hnon : ‖∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
      ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ * ∑ f ∈ Fs, Nf f ξ1 ξ2‖ ≤
      nξ ^ 2 * Kt * NW ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-σ) * (cI * S * L * F / Hh) ^ δ * MQ := by
    set Bk := Kt * NW ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-σ) * (cI * S * L * F / Hh) ^ δ * MQ
      with hBk
    have hterm : ∀ ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        ‖pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ * ∑ f ∈ Fs, Nf f ξ1 ξ2‖ ≤ Bk := fun ξ1 ξ2 => by
      rw [norm_mul]
      calc ‖pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹‖ * ‖∑ f ∈ Fs, Nf f ξ1 ξ2‖ ≤ 1 * Bk :=
            mul_le_mul (norm_pairCoeff_xi_le ξ ξ1 ξ2) (hblock ξ1 ξ2) (norm_nonneg _) zero_le_one
        _ = Bk := one_mul _
    calc _ ≤ ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          ‖∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
            pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ * ∑ f ∈ Fs, Nf f ξ1 ξ2‖ := norm_sum_le _ _
      _ ≤ ∑ _ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          ∑ _ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, Bk :=
          Finset.sum_le_sum fun ξ1 _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun ξ2 _ => hterm ξ1 ξ2)
      _ = nξ ^ 2 * Bk := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
          rw [hnξ]; ring
      _ = _ := by rw [hBk]; ring
  calc rowE ξ W L Fs T ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ ≤ 2 * (2 * kappa + 5) * ((2 * kappa + 5) * max β 1) * (2 / Real.sqrt 3 * ‖dualG 0‖) *
          NW ^ 2 * (Hh * L * F) +
        nξ ^ 2 * Kt * NW ^ 2 * (4 * Hh / (3 * L ^ 2)) ^ (-σ) * (cI * S * L * F / Hh) ^ δ * MQ :=
        add_le_add hzero hnon
    _ = _ := by ring

end Eis

end

#print axioms Eis.pgen_ne_zero
#print axioms Eis.primeSet_subset_of_dvd
#print axioms Eis.card_sq_dvd_le
#print axioms Eis.sum_pairs_le_mult
#print axioms Eis.rcDual_eq_zero_of_W1
#print axioms Eis.rcDual_eq_zero_of_W2
#print axioms Eis.rcDual_eq_zero_of_dualW
#print axioms Eis.rcDual_eq_zero_of_colP1
#print axioms Eis.rcDual_eq_zero_of_colP2
#print axioms Eis.W0c_eq_zero_of_gt
#print axioms Eis.dvd_c_of_mem
#print axioms Eis.rcDual_eq_zero_of_meet
#print axioms Eis.rcDual_eq_zero_of_large_bTV
#print axioms Eis.rcDual_eq_zero_of_large_mu
#print axioms Eis.absNorm_mul_pgen_sq
#print axioms Eis.powerset_sdiff_eq_filter
#print axioms Eis.sum_nested_eq_triplesOf
#print axioms Eis.norm_wRowD_le
#print axioms Eis.ellS_pos
#print axioms Eis.xE_pos
#print axioms Eis.rcDual_eq_bilin
#print axioms Eis.sum_enlarged
#print axioms Eis.colE_eq_zero_of_ne
#print axioms Eis.rowSumD_eq_bilinear
#print axioms Eis.lt_nI_of_not_mem_fsLe
#print axioms Eis.mem_fsLe_of_nI_le
#print axioms Eis.Pcol_eq_powerset
#print axioms Eis.norm_Pcol_le
#print axioms Eis.re_majorant_nonneg
#print axioms Eis.Ycd_pos
#print axioms Eis.Ycd_le
#print axioms Eis.rows_meanSquareD
#print axioms Eis.mem_rowsD
#print axioms Eis.ARowD_ge
#print axioms Eis.exists_bump_one
#print axioms Eis.blockD_bound
#print axioms Eis.RΦ_pos
#print axioms Eis.dualG_eq_zero_of_ge
#print axioms Eis.fsLe_mono
#print axioms Eis.zero_rowD_le
#print axioms Eis.norm_colSum_le_card
#print axioms Eis.sum_f_eq_rowsD
#print axioms Eis.norm_pairCoeff_xi_le
#print axioms Eis.first_transfer
