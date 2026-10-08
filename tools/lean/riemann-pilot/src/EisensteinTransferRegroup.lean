import EisensteinPairRatio

/-! # Lemma 7.3, part 1: the regrouping (round 323)

S5c-5, part 2, in round 316's plan. Round 320's `Qform` (the companion paper's `𝒬` of (7.2), times
`2LF/√3`) sums, over the triples `t = (b, T, V)` of `qTriples (2βL)`, the weight `2𝓗·N(b)/(√3·L)` times
the second mean square, which round 322's `Mq_rowcolD` writes in row/column form. The paper's proof of
Lemma 7.3 regroups that output by "`r=tg/e,\quad f'=Cew,\quad k'=deh`", here
`r = V ∪ b₂`, `f′ = b ∪ T ∪ T₂ ∪ V₂` and `k′ = d_T·d_{T₂}·μ`, with the column length
"`X'_0&=\frac{\ell}{N(g)N(w)}=\frac L{N(r)N(f')}`".

* **The split of `𝒬`** (`zeroQ`, `dualQ`, `hY2_common`, `wtQ`, **`Qform_le_split`**): with
  `c_I ≥ 3β²R_Φ²`, the second frequencies of every triple lie in the common range
  `N(μ) ≤ 𝓗L/(ΣF)`, and `𝒬 ≤ |Σ_t w_t·zeroQ t| + Σ_ξ |ĉ(ξ)|·|Σ_t w_t·dualQ ξ t|`.
* **Rows** (`RowQ`, `colRange`, `termQ`, `sum_wt_dualQ_eq`): the nonzero frequencies as one sum over
  the rows `((b, T, V), (b₂, T₂, V₂), μ)` and the columns of each row.
* **The rows that vanish** (`rcQ_eq_zero_of_bT`, …, `goodQ`, **`termQ_eq_zero_of_not_good`**,
  `rowsQ`, `sum_rows_eq_rowsQ`): a prime shared by `b ∪ T ∪ V` and `b₂ ∪ T₂ ∪ V₂`,
  `N(b)⋯N(V₂) > 2βL`, or `N(μ)N(T)N(T₂)·(N(b₂)N(V))² > 𝓗L/(ΣF)` (the paper's "In particular its nonzero
  support requires").
* **The bilinear shape** (`rQ`, `fQ`, `kQ`, `colQ`, `aQ`, `wQr`, `xQ`, `rhoQ`, `AQ`, `WBQ`,
  **`termQ_eq_bilin`**, `rowSumQ_eq_bilinear`): with dyadic parameters `R, F′` and the common column
  scale `X′ = L/(RF′)`, each term is `W_B·w_ρ·a(M₁)·conj(a(M₂))·W₀(ρ_ρx₁)·conj(W₀(ρ_ρx₂))·
  Φ̂(√(A_ρ/(x₁x₂)))`, with `x_M = N(M)/X′`, `ρ_ρ = N(r)N(f′)/(RF′)` on the rows,
  `W_B = 8c_IΣFR/(3L)`, `W₀ = conj ∘ W₀c U` and `w_ρ` the row factor times `N(V)N(b₂)/(2R)`.
* **The dyadic blocks** (`lvl`, `lvl_bounds`, `nI_rQ_fQ_le`, `sum_rowsQ_blocks`): `(⌊log₂ N(r)⌋,
  ⌊log₂ N(f′)⌋) ∈ [0, ⌊log₂⌊2βL⌋⌋]²`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The split of `𝒬` -/

/-- The zero frequency of the second mean square at the triple `t = (b, T, V)`. -/
def zeroQ (U : ℝ → ℂ) (β H L S F cI : ℝ) (t : Finset Pr × Finset Pr × Finset Pr) : ℂ :=
  ∑ A ∈ fsLe (2 * β * ellS L t.1 t.2.1 t.2.2),
    wQ U (ellS L t.1 t.2.1 t.2.2) (eS t.1 ^ 4 * eS t.2.1 ^ 5 * eS t.2.2 ^ 6) A A *
      ∑ T2 ∈ A.powerset, (-1 : ℂ) ^ T2.card * (kap (Ycd cI S L F H t.1 t.2.1) ∅ ∅ T2 : ℂ) *
        dualG 0

open Classical in
/-- The nonzero frequencies of the second mean square at the triple `t = (b, T, V)` in the character
`ξ`, over the subsets of `U₀` and the frequencies of norm at most `𝓗L/(ΣF)`. -/
def dualQ (U : ℝ → ℂ) (H L S F cI : ℝ) (U0 : Finset Pr)
    (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (t : Finset Pr × Finset Pr × Finset Pr) : ℂ :=
  ∑ b2 ∈ U0.powerset, ∑ T2 ∈ (U0 \ b2).powerset, ∑ V2 ∈ (U0 \ (b2 ∪ T2)).powerset,
    ∑ μ ∈ (eltsLe (H * L / (S * F))).erase 0,
      ∑ M1 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset, ∑ M2 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset,
        rcQ U (ellS L t.1 t.2.1 t.2.2) (Ycd cI S L F H t.1 t.2.1)
          (eS t.1 ^ 4 * eS t.2.1 ^ 5 * eS t.2.2 ^ 6) ξ ξ b2 T2 V2 μ M1 M2

theorem ellS_le {L : ℝ} (hL : 0 ≤ L) (b T V : Finset Pr) : ellS L b T V ≤ L := by
  unfold ellS
  exact div_le_self hL (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_nI b) (one_le_nI T)) (one_le_nI V))

/-- **The common range of the second frequencies**: with `c_I ≥ 3β²R²`,
`3R²(2βℓ)² ≤ 4·Y_{C,d}·𝓗L/(ΣF)` for every triple. -/
theorem hY2_common {β H L S F cI R : ℝ} (hH : 0 < H) (hL : 0 < L) (hS : 0 < S) (hF : 0 < F)
    (hcI : 3 * β ^ 2 * R ^ 2 ≤ cI) (b T V : Finset Pr) :
    3 * R ^ 2 * (2 * β * ellS L b T V) ^ 2 ≤ 4 * Ycd cI S L F H b T * (H * L / (S * F)) := by
  have hb := nI_pos b
  have hT := nI_pos T
  have hV := nI_pos V
  have hT1 := one_le_nI T
  have hV1 := one_le_nI V
  have e1 : 3 * R ^ 2 * (2 * β * ellS L b T V) ^ 2 =
      (3 * β ^ 2 * R ^ 2) * (4 * L ^ 2 / (nI b ^ 2 * (nI T ^ 2 * nI V ^ 2))) := by
    unfold ellS; field_simp; ring
  have e2 : 4 * Ycd cI S L F H b T * (H * L / (S * F)) =
      cI * (4 * L ^ 2 / (nI b ^ 2 * nI T)) := by
    unfold Ycd; field_simp
  rw [e1, e2]
  have hk : 4 * L ^ 2 / (nI b ^ 2 * (nI T ^ 2 * nI V ^ 2)) ≤ 4 * L ^ 2 / (nI b ^ 2 * nI T) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : nI T ≤ nI T ^ 2 := le_self_pow₀ hT1 (by norm_num)
    have h2 : 1 ≤ nI V ^ 2 := one_le_pow₀ hV1
    nlinarith
  have hc0 : 0 ≤ cI := le_trans (by positivity) hcI
  calc (3 * β ^ 2 * R ^ 2) * (4 * L ^ 2 / (nI b ^ 2 * (nI T ^ 2 * nI V ^ 2)))
      ≤ cI * (4 * L ^ 2 / (nI b ^ 2 * (nI T ^ 2 * nI V ^ 2))) :=
        mul_le_mul_of_nonneg_right hcI (by positivity)
    _ ≤ cI * (4 * L ^ 2 / (nI b ^ 2 * nI T)) := mul_le_mul_of_nonneg_left hk hc0

/-- The row weight `w_t = 2H·N(b)/(√3·L)` of `Qform`. -/
def wtQ (H L : ℝ) (t : Finset Pr × Finset Pr × Finset Pr) : ℝ :=
  2 * H * nI t.1 / (Real.sqrt 3 * L)

open Classical in
/-- **The split of `𝒬`** (the companion paper's Lemma 7.2 inserted into (7.2)): with `c_I ≥ 3β²R_Φ²`
and `U₀` containing the primes of norm at most `2βL`, `𝒬_{ξ₁}(U)` is at most the norm of the zero
frequencies plus `Σ_ξ |ĉ(ξ)|·|Σ_t w_t·dualQ ξ t|`, at the common range `Y₂ = 𝓗L/(ΣF)`. -/
theorem Qform_le_split (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ}
    {β H L S F cI : ℝ} (hβ : 0 ≤ β) (hH : 0 < H) (hL : 0 < L) (hS : 0 < S) (hF : 0 < F)
    (hcI : 3 * β ^ 2 * RΦ ^ 2 ≤ cI) (hcI0 : 0 < cI) (hU : ∀ x, 2 * β < x → U x = 0)
    {U0 : Finset Pr} (hU0 : primesLe (2 * β * L) ⊆ U0) :
    Qform ξ1 U β H L S F cI ≤
      ‖∑ t ∈ qTriples (2 * β * L), (wtQ H L t : ℂ) * zeroQ U β H L S F cI t‖ +
        ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ‖classCoeff (pairH ξ1) ξ‖ *
          ‖∑ t ∈ qTriples (2 * β * L), (wtQ H L t : ℂ) * dualQ U H L S F cI U0 ξ t‖ := by
  have key : ∀ t : Finset Pr × Finset Pr × Finset Pr,
      ∑' y : 𝓞 K, Pcol ξ1 U β L t.1 t.2.1 t.2.2 y * conj (Pcol ξ1 U β L t.1 t.2.1 t.2.2 y) *
        Majorant.Phi (σO y / (Real.sqrt (Ycd cI S L F H t.1 t.2.1) : ℂ)) =
      zeroQ U β H L S F cI t + ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        classCoeff (pairH ξ1) ξ * dualQ U H L S F cI U0 ξ t := by
    intro t
    have hℓL := ellS_le hL.le t.1 t.2.1 t.2.2
    have h2β : 0 ≤ 2 * β := by positivity
    have hsub : primesLe (2 * β * ellS L t.1 t.2.1 t.2.2) ⊆ U0 :=
      (primesLe_mono (mul_le_mul_of_nonneg_left hℓL h2β)).trans hU0
    have h := Mq_rowcolD ξ1 hβ hL hU t.1 t.2.1 t.2.2 (Ycd_pos hcI0 hS hL hF hH t.1 t.2.1) RΦ_pos
      (fun _ h => dualG_eq_zero_of_ge h) (hY2_common hH hL hS hF hcI t.1 t.2.1 t.2.2) hsub
    rw [h]
    rfl
  have hQ : Qform ξ1 U β H L S F cI =
      (∑ t ∈ qTriples (2 * β * L), (wtQ H L t : ℂ) * (zeroQ U β H L S F cI t +
        ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          classCoeff (pairH ξ1) ξ * dualQ U H L S F cI U0 ξ t)).re := by
    unfold Qform
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← key t, Complex.re_ofReal_mul]
    rfl
  have hsplit : ∑ t ∈ qTriples (2 * β * L), (wtQ H L t : ℂ) * (zeroQ U β H L S F cI t +
        ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          classCoeff (pairH ξ1) ξ * dualQ U H L S F cI U0 ξ t) =
      ∑ t ∈ qTriples (2 * β * L), (wtQ H L t : ℂ) * zeroQ U β H L S F cI t +
        ∑ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, classCoeff (pairH ξ1) ξ *
          ∑ t ∈ qTriples (2 * β * L), (wtQ H L t : ℂ) * dualQ U H L S F cI U0 ξ t := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hQ, hsplit]
  refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans (add_le_add le_rfl ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
  rw [norm_mul]

/-! ### Rows of the regrouping -/

/-- A row `((b, T, V), (b₂, T₂, V₂), μ)` of the regrouped second dual sum: the first Poisson
summation's `C = b ∪ T`, `d = T`, `t = V`, the second's `g = b₂ ∪ T₂`, `e = T₂`, `w = V₂`, and the
frequency `μ` (the paper's `h`). -/
abbrev RowQ := (Finset Pr × Finset Pr × Finset Pr) × (Finset Pr × Finset Pr × Finset Pr) × 𝓞 K

/-- The columns of a row: the subsets of `U₀` prime to `b₂ ∪ T₂ ∪ V₂`. -/
def colRange (U0 : Finset Pr) (ρ : RowQ) : Finset (Finset Pr) :=
  ((U0 \ (ρ.2.1.1 ∪ ρ.2.1.2.1)) \ ρ.2.1.2.2).powerset

/-- The term `w_t·rcQ` of a row and two columns. -/
def termQ (U : ℝ → ℂ) (H L S F cI : ℝ) (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (ρ : RowQ)
    (M1 M2 : Finset Pr) : ℂ :=
  (wtQ H L ρ.1 : ℂ) * rcQ U (ellS L ρ.1.1 ρ.1.2.1 ρ.1.2.2) (Ycd cI S L F H ρ.1.1 ρ.1.2.1)
    (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6) ξ ξ ρ.2.1.1 ρ.2.1.2.1 ρ.2.1.2.2 ρ.2.2 M1 M2

open Classical in
/-- **The weighted dual sums as one sum over rows**: `Σ_t w_t·dualQ ξ t` is the sum of `termQ` over
the rows `(t, (b₂, T₂, V₂), μ)` and the columns of each row. -/
theorem sum_wt_dualQ_eq (U : ℝ → ℂ) (H L S F cI : ℝ) (U0 : Finset Pr)
    (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (Λ : ℝ) :
    ∑ t ∈ qTriples Λ, (wtQ H L t : ℂ) * dualQ U H L S F cI U0 ξ t =
      ∑ ρ ∈ qTriples Λ ×ˢ (triplesOf U0 ×ˢ (eltsLe (H * L / (S * F))).erase 0),
        ∑ M1 ∈ colRange U0 ρ, ∑ M2 ∈ colRange U0 ρ, termQ U H L S F cI ξ ρ M1 M2 := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold dualQ
  rw [sum_nested_eq_triplesOf U0 (fun b2 T2 V2 => ∑ μ ∈ (eltsLe (H * L / (S * F))).erase 0,
    ∑ M1 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset, ∑ M2 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset,
      rcQ U (ellS L t.1 t.2.1 t.2.2) (Ycd cI S L F H t.1 t.2.1)
        (eS t.1 ^ 4 * eS t.2.1 ^ 5 * eS t.2.2 ^ 6) ξ ξ b2 T2 V2 μ M1 M2), Finset.sum_product,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  unfold colRange termQ
  simp only [Finset.mul_sum]

/-! ### The rows that vanish -/

section VanishQ

variable (U : ℝ → ℂ) (ℓ H : ℝ) (c : 𝓞 K) (ξa ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
  (b T V : Finset Pr) (μ : 𝓞 K) (M1 M2 : Finset Pr)

theorem rcQ_eq_zero_of_bT (h : chiS (b ∪ T) c = 0) : rcQ U ℓ H c ξa ξb b T V μ M1 M2 = 0 := by
  unfold rcQ; rw [h]; simp

theorem rcQ_eq_zero_of_V (h : chiS V c = 0) : rcQ U ℓ H c ξa ξb b T V μ M1 M2 = 0 := by
  unfold rcQ; rw [h]; simp

theorem rcQ_eq_zero_of_W1 (h : MellinSep.W0c U (nI b * nI T * nI V * nI M1 / ℓ) = 0) :
    rcQ U ℓ H c ξa ξb b T V μ M1 M2 = 0 := by
  unfold rcQ; rw [h]; simp

theorem rcQ_eq_zero_of_W2 (h : MellinSep.W0c U (nI b * nI T * nI V * nI M2 / ℓ) = 0) :
    rcQ U ℓ H c ξa ξb b T V μ M1 M2 = 0 := by
  unfold rcQ; rw [h]; simp

theorem rcQ_eq_zero_of_dualW (h : dualW H (V ∪ M1) (V ∪ M2) T μ = 0) :
    rcQ U ℓ H c ξa ξb b T V μ M1 M2 = 0 := by
  unfold rcQ; rw [h]; simp

end VanishQ

/-- The rows that can contribute: `b ∪ T ∪ V` prime to `b₂ ∪ T₂ ∪ V₂`,
`N(b)N(T)N(V)·N(b₂)N(T₂)N(V₂) ≤ 2βL` and `N(μ)N(T)N(T₂)·(N(b₂)N(V))² ≤ 𝓗L/(ΣF)`. -/
def goodQ (β H L S F : ℝ) (ρ : RowQ) : Prop :=
  Disjoint (ρ.1.1 ∪ ρ.1.2.1 ∪ ρ.1.2.2) (ρ.2.1.1 ∪ ρ.2.1.2.1 ∪ ρ.2.1.2.2) ∧
    nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.1.2.2 * (nI ρ.2.1.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2) ≤ 2 * β * L ∧
    (absNorm (span {ρ.2.2}) : ℝ) * nI ρ.1.2.1 * nI ρ.2.1.2.1 * (nI ρ.2.1.1 * nI ρ.1.2.2) ^ 2 ≤
      H * L / (S * F)

/-- **The rows that are not good vanish**: a prime shared by `b ∪ T ∪ V` and `b₂ ∪ T₂ ∪ V₂` kills the
row factor; `N(b)⋯N(V₂) > 2βL` puts the first weight beyond `2β`; and
`N(μ)N(T)N(T₂)(N(b₂)N(V))² > 𝓗L/(ΣF)` puts the dual weight beyond `R_Φ` (with `c_I ≥ 3β²R_Φ²`). -/
theorem termQ_eq_zero_of_not_good {U : ℝ → ℂ} {β : ℝ} (hU : ∀ x, 2 * β < x → U x = 0)
    {H L S F cI : ℝ} (hH : 0 < H) (hL : 0 < L) (hS : 0 < S) (hF : 0 < F)
    (hcI : 3 * β ^ 2 * RΦ ^ 2 ≤ cI) (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U0 : Finset Pr}
    {ρ : RowQ} (hρ : ¬ goodQ β H L S F ρ) {M1 M2 : Finset Pr} (hM1 : M1 ∈ colRange U0 ρ)
    (hM2 : M2 ∈ colRange U0 ρ) : termQ U H L S F cI ξ ρ M1 M2 = 0 := by
  obtain ⟨⟨b, T, V⟩, ⟨b2, T2, V2⟩, μ⟩ := ρ
  unfold termQ
  refine mul_eq_zero_of_right _ ?_
  set c := eS b ^ 4 * eS T ^ 5 * eS V ^ 6 with hc
  set ℓ := ellS L b T V with hℓ
  set Y := Ycd cI S L F H b T with hY
  have hV1 : Disjoint V2 M1 := disjoint_of_mem_powerset_sdiff hM1
  have hV2 : Disjoint V2 M2 := disjoint_of_mem_powerset_sdiff hM2
  unfold goodQ at hρ
  by_cases hd : Disjoint (b ∪ T ∪ V) (b2 ∪ T2 ∪ V2)
  swap
  · rw [Finset.not_disjoint_iff] at hd
    obtain ⟨P, hP, hP2⟩ := hd
    have hdvd := dvd_c_of_mem hP
    rcases Finset.mem_union.1 hP2 with h | h
    · exact rcQ_eq_zero_of_bT U ℓ Y c ξ ξ b2 T2 V2 μ M1 M2 (chiS_eq_zero_of_dvd h hdvd)
    · exact rcQ_eq_zero_of_V U ℓ Y c ξ ξ b2 T2 V2 μ M1 M2 (chiS_eq_zero_of_dvd h hdvd)
  have hℓ0 : 0 < ℓ := ellS_pos hL b T V
  have hb := nI_pos b
  have hT := nI_pos T
  have hV := nI_pos V
  have hb2 := nI_pos b2
  have hT2 := nI_pos T2
  have hV2' := nI_pos V2
  have hm1 := one_le_nI M1
  have hm2 := one_le_nI M2
  -- the weights at `x₁, x₂`
  have hx : ∀ M : Finset Pr, nI b2 * nI T2 * nI V2 * nI M / ℓ =
      nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) * nI M / L := by
    intro M; rw [hℓ]; unfold ellS; field_simp
  by_cases hW1 : MellinSep.W0c U (nI b2 * nI T2 * nI V2 * nI M1 / ℓ) = 0
  · exact rcQ_eq_zero_of_W1 U ℓ Y c ξ ξ b2 T2 V2 μ M1 M2 hW1
  by_cases hW2 : MellinSep.W0c U (nI b2 * nI T2 * nI V2 * nI M2 / ℓ) = 0
  · exact rcQ_eq_zero_of_W2 U ℓ Y c ξ ξ b2 T2 V2 μ M1 M2 hW2
  have hx1 : nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) * nI M1 ≤ 2 * β * L := by
    by_contra hc'
    refine hW1 (W0c_eq_zero_of_gt hU ?_)
    rw [hx, lt_div_iff₀ hL]; linarith
  have hx2 : nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) * nI M2 ≤ 2 * β * L := by
    by_contra hc'
    refine hW2 (W0c_eq_zero_of_gt hU ?_)
    rw [hx, lt_div_iff₀ hL]; linarith
  have hP0 : 0 < nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) := by positivity
  have hbig : nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) ≤ 2 * β * L :=
    le_trans (le_mul_of_one_le_right hP0.le hm1) hx1
  have hmu : H * L / (S * F) <
      (absNorm (span {μ}) : ℝ) * nI T * nI T2 * (nI b2 * nI V) ^ 2 := by
    by_contra hc'
    exact hρ ⟨hd, hbig, not_lt.1 hc'⟩
  -- the dual weight vanishes
  refine rcQ_eq_zero_of_dualW U ℓ Y c ξ ξ b2 T2 V2 μ M1 M2 ?_
  unfold dualW
  refine dualG_eq_zero_of_ge ?_
  set Nμ := (absNorm (span {μ}) : ℝ) with hNμ
  have hNμ0 : 0 ≤ Nμ := Nat.cast_nonneg _
  rw [Real.le_sqrt' RΦ_pos, nI_union hV1, nI_union hV2, le_div_iff₀ (by positivity)]
  have hcI0 : 0 ≤ cI := le_trans (by positivity) hcI
  have h2βL : 0 ≤ 2 * β * L := le_trans hP0.le hbig
  have e3 : (nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) * nI M1) *
      (nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) * nI M2) ≤ (2 * β * L) * (2 * β * L) :=
    mul_le_mul hx1 hx2 (by positivity) h2βL
  have hmu' : H * L < Nμ * nI T * nI T2 * (nI b2 * nI V) ^ 2 * (S * F) := by
    rwa [div_lt_iff₀ (by positivity)] at hmu
  have hY' : Y * (H * nI b ^ 2 * nI T) = cI * S * L * F := by
    rw [hY]; unfold Ycd; field_simp
  -- `3R²·N(V₂)²N(M₁)N(M₂)N(T₂) ≤ 4Y·N(μ)`
  have key : RΦ ^ 2 * (3 * (nI V2 * nI M1 * (nI V2 * nI M2)) * nI T2) *
      ((nI b * nI T * nI V * nI b2) ^ 2 * nI T2 * H) ≤
      4 * Y * Nμ * ((nI b * nI T * nI V * nI b2) ^ 2 * nI T2 * H) := by
    calc RΦ ^ 2 * (3 * (nI V2 * nI M1 * (nI V2 * nI M2)) * nI T2) *
          ((nI b * nI T * nI V * nI b2) ^ 2 * nI T2 * H)
        = 3 * RΦ ^ 2 * H * ((nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) * nI M1) *
          (nI b * nI T * nI V * (nI b2 * nI T2 * nI V2) * nI M2)) := by ring
      _ ≤ 3 * RΦ ^ 2 * H * ((2 * β * L) * (2 * β * L)) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = 4 * (3 * β ^ 2 * RΦ ^ 2) * (H * L) * L := by ring
      _ ≤ 4 * cI * (Nμ * nI T * nI T2 * (nI b2 * nI V) ^ 2 * (S * F)) * L := by
          have h1 : 4 * (3 * β ^ 2 * RΦ ^ 2) * (H * L) ≤ 4 * cI * (H * L) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have h2 : 4 * cI * (H * L) ≤ 4 * cI * (Nμ * nI T * nI T2 * (nI b2 * nI V) ^ 2 * (S * F)) :=
            mul_le_mul_of_nonneg_left hmu'.le (by positivity)
          nlinarith
      _ = 4 * Nμ * (nI T * nI V ^ 2 * nI b2 ^ 2 * nI T2) * (cI * S * L * F) := by ring
      _ = 4 * Nμ * (nI T * nI V ^ 2 * nI b2 ^ 2 * nI T2) * (Y * (H * nI b ^ 2 * nI T)) := by
          rw [hY']
      _ = 4 * Y * Nμ * ((nI b * nI T * nI V * nI b2) ^ 2 * nI T2 * H) := by ring
  exact le_of_mul_le_mul_right key (by positivity)

open Classical in
/-- The rows of the regrouping: the good rows among `(t, (b₂, T₂, V₂), μ)`. -/
def rowsQ (U0 : Finset Pr) (β H L S F : ℝ) : Finset RowQ :=
  (qTriples (2 * β * L) ×ˢ (triplesOf U0 ×ˢ (eltsLe (H * L / (S * F))).erase 0)).filter
    (goodQ β H L S F)

open Classical in
/-- **The sum over the good rows**: the other rows contribute `0`. -/
theorem sum_rows_eq_rowsQ {U : ℝ → ℂ} {β : ℝ} (hU : ∀ x, 2 * β < x → U x = 0)
    {H L S F cI : ℝ} (hH : 0 < H) (hL : 0 < L) (hS : 0 < S) (hF : 0 < F)
    (hcI : 3 * β ^ 2 * RΦ ^ 2 ≤ cI) (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U0 : Finset Pr) :
    ∑ ρ ∈ qTriples (2 * β * L) ×ˢ (triplesOf U0 ×ˢ (eltsLe (H * L / (S * F))).erase 0),
        ∑ M1 ∈ colRange U0 ρ, ∑ M2 ∈ colRange U0 ρ, termQ U H L S F cI ξ ρ M1 M2 =
      ∑ ρ ∈ rowsQ U0 β H L S F,
        ∑ M1 ∈ colRange U0 ρ, ∑ M2 ∈ colRange U0 ρ, termQ U H L S F cI ξ ρ M1 M2 := by
  unfold rowsQ
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs with hg
  · rfl
  · exact Finset.sum_eq_zero fun M1 hM1 => Finset.sum_eq_zero fun M2 hM2 =>
      termQ_eq_zero_of_not_good hU hH hL hS hF hcI ξ hg hM1 hM2


/-! ### The rows in the shape of the bilinear form -/

open Classical in
theorem mem_rowsQ {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} :
    ρ ∈ rowsQ U0 β H L S F ↔
      (ρ.1 ∈ qTriples (2 * β * L) ∧ ρ.2.1 ∈ triplesOf U0 ∧
        ρ.2.2 ∈ (eltsLe (H * L / (S * F))).erase 0) ∧ goodQ β H L S F ρ := by
  unfold rowsQ
  simp only [Finset.mem_filter, Finset.mem_product]

open Classical in
/-- The disjointness of a row's sets of primes. -/
theorem rowsQ_disjoint {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ}
    (h : ρ ∈ rowsQ U0 β H L S F) :
    Disjoint ρ.1.1 ρ.1.2.1 ∧ Disjoint (ρ.1.1 ∪ ρ.1.2.1) ρ.1.2.2 ∧ Disjoint ρ.2.1.1 ρ.2.1.2.1 ∧
      Disjoint (ρ.2.1.1 ∪ ρ.2.1.2.1) ρ.2.1.2.2 ∧
      Disjoint (ρ.1.1 ∪ ρ.1.2.1 ∪ ρ.1.2.2) (ρ.2.1.1 ∪ ρ.2.1.2.1 ∪ ρ.2.1.2.2) := by
  obtain ⟨⟨ht, hs, -⟩, hg⟩ := mem_rowsQ.1 h
  unfold qTriples at ht
  unfold triplesOf at hs
  rw [Finset.mem_filter] at ht hs
  exact ⟨ht.2.1, ht.2.2.1, hs.2.1, hs.2.2, hg.1⟩

/-- The set of primes `r = V ∪ b₂` of a row (the companion paper's `r`). -/
def rQ (ρ : RowQ) : Finset Pr := ρ.1.2.2 ∪ ρ.2.1.1

/-- The set of primes `f′ = b ∪ T ∪ T₂ ∪ V₂` of a row. -/
def fQ (ρ : RowQ) : Finset Pr := ρ.1.1 ∪ ρ.1.2.1 ∪ ρ.2.1.2.1 ∪ ρ.2.1.2.2

/-- The element `k′ = d_T·d_{T₂}·μ` of a row. -/
def kQ (ρ : RowQ) : 𝓞 K := eS ρ.1.2.1 * eS ρ.2.1.2.1 * ρ.2.2

open Classical in
theorem nI_rQ {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} (h : ρ ∈ rowsQ U0 β H L S F) :
    nI (rQ ρ) = nI ρ.1.2.2 * nI ρ.2.1.1 := by
  obtain ⟨-, -, -, -, hx⟩ := rowsQ_disjoint h
  unfold rQ
  refine nI_union (Finset.disjoint_of_subset_left ?_ (Finset.disjoint_of_subset_right ?_ hx))
  · exact Finset.subset_union_right
  · exact Finset.subset_union_left.trans Finset.subset_union_left

open Classical in
theorem nI_fQ {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} (h : ρ ∈ rowsQ U0 β H L S F) :
    nI (fQ ρ) = nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2 := by
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
  unfold fQ
  rw [nI_union d2, nI_union d1, nI_union h1]

/-- The column coefficient `colA ξ (d_{T₂}μ) (d_{T₂}w) M·χ_M(c)` of a row, `c = b⁴T⁵V⁶`. -/
def colQ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (ρ : RowQ) (M : Finset Pr) : ℂ :=
  colA ξ (eS ρ.2.1.2.1 * ρ.2.2) (eS ρ.2.1.2.1 * eS ρ.2.1.2.2) M *
    chiS M (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6)

open Classical in
/-- The bilinear form's coefficients: `conj(colQ)` on the columns of the row, `0` elsewhere. -/
def aQ (U0 : Finset Pr) (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (ρ : RowQ) (M : Finset Pr) : ℂ :=
  if M ∈ colRange U0 ρ then conj (colQ ξ ρ M) else 0

/-- The row weight: the sign, the row factor of `rcQ` and `N(V)N(b₂)/(2R)`. -/
def wQr (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (R : ℝ) (ρ : RowQ) : ℂ :=
  ((-1 : ℂ) ^ ρ.2.1.2.1.card * (-1) ^ ρ.2.1.2.2.card) *
    (conj (aXi ξ (idl ρ.2.1.2.2)) * aXi ξ (idl ρ.2.1.2.2) *
      (chiS ρ.2.1.2.2 ρ.2.2 * conj (chiS ρ.2.1.2.2 ρ.2.2)) *
      ((conj (chiS (ρ.2.1.1 ∪ ρ.2.1.2.1) (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6)) *
          chiS (ρ.2.1.1 ∪ ρ.2.1.2.1) (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6)) *
        (conj (chiS ρ.2.1.2.2 (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6)) *
          chiS ρ.2.1.2.2 (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6)))) *
    ((nI ρ.1.2.2 * nI ρ.2.1.1 / (2 * R) : ℝ) : ℂ)

/-- The point of a column in a block: `x_M = N(M)/X` with `X = L/(RF′)`. -/
def xQ (L R Fp : ℝ) (M : Finset Pr) : ℝ := nI M * (R * Fp) / L

/-- The dilation of a row in a block: `N(b)N(T)N(V)N(b₂)N(T₂)N(V₂)/(RF′)`, that is `N(r)N(f′)/(RF′)`. -/
def rhoQ (R Fp : ℝ) (ρ : RowQ) : ℝ :=
  nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.1.2.2 * (nI ρ.2.1.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2) / (R * Fp)

/-- The kernel parameter of a row in a block: `A = 4Y_{C,d}N(μ)/(3N(V₂)²N(T₂)X²)`. -/
def AQ (cI S L F H R Fp : ℝ) (ρ : RowQ) : ℝ :=
  4 * Ycd cI S L F H ρ.1.1 ρ.1.2.1 * (absNorm (span {ρ.2.2}) : ℝ) * (R * Fp) ^ 2 /
    (3 * nI ρ.2.1.2.2 ^ 2 * nI ρ.2.1.2.1 * L ^ 2)

/-- The common weight of a block, `8c_IΣFR/(3L)`. -/
def WBQ (cI S F L R : ℝ) : ℝ := 8 * cI * S * F * R / (3 * L)

/-- **One term in the shape of the bilinear form** (the companion paper's regrouping of Lemma 7.3 for
one row): for columns of the row, `termQ = W_B·w_ρ·a(M₁)·conj(a(M₂))·W₀(ρ_ρx₁)·conj(W₀(ρ_ρx₂))·
Φ̂(√(A_ρ/(x₁x₂)))` with `W₀ = conj ∘ W₀c U`. -/
theorem termQ_eq_bilin (U : ℝ → ℂ) {H L S F cI R Fp : ℝ} (hH : 0 < H) (hL : 0 < L) (hR : 0 < R)
    (hFp : 0 < Fp) (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U0 : Finset Pr) (ρ : RowQ)
    {M1 M2 : Finset Pr} (hM1 : M1 ∈ colRange U0 ρ) (hM2 : M2 ∈ colRange U0 ρ) :
    termQ U H L S F cI ξ ρ M1 M2 = (WBQ cI S F L R : ℂ) * (wQr ξ R ρ *
      (aQ U0 ξ ρ M1 * conj (aQ U0 ξ ρ M2) *
        ((fun y => conj (MellinSep.W0c U y)) (rhoQ R Fp ρ * xQ L R Fp M1) *
          conj ((fun y => conj (MellinSep.W0c U y)) (rhoQ R Fp ρ * xQ L R Fp M2)) *
          dualG (Real.sqrt (AQ cI S L F H R Fp ρ / (xQ L R Fp M1 * xQ L R Fp M2)))))) := by
  obtain ⟨⟨b, T, V⟩, ⟨b2, T2, V2⟩, μ⟩ := ρ
  have hV1 : Disjoint V2 M1 := disjoint_of_mem_powerset_sdiff hM1
  have hV2 : Disjoint V2 M2 := disjoint_of_mem_powerset_sdiff hM2
  have hb := nI_pos b
  have hT := nI_pos T
  have hV := nI_pos V
  have hb2 := nI_pos b2
  have hT2 := nI_pos T2
  have hV2' := nI_pos V2
  have hm1 := nI_pos M1
  have hm2 := nI_pos M2
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  -- the weights
  have hw : (wtQ H L (b, T, V) : ℂ) *
      ((2 * Ycd cI S L F H b T * nI b2 / (Real.sqrt 3 * ellS L b T V) : ℝ) : ℂ) =
      (WBQ cI S F L R : ℂ) * ((nI V * nI b2 / (2 * R) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    unfold wtQ WBQ Ycd ellS
    simp only
    field_simp
    rw [show Real.sqrt 3 ^ 2 = 3 by rw [sq]; exact h3]
    ring
  -- the points
  have hx : ∀ M : Finset Pr, rhoQ R Fp ((b, T, V), (b2, T2, V2), μ) * xQ L R Fp M =
      nI b2 * nI T2 * nI V2 * nI M / ellS L b T V := by
    intro M
    unfold rhoQ xQ ellS
    simp only
    field_simp
  -- the kernel
  have hk : dualW (Ycd cI S L F H b T) (V2 ∪ M1) (V2 ∪ M2) T2 μ =
      dualG (Real.sqrt (AQ cI S L F H R Fp ((b, T, V), (b2, T2, V2), μ) /
        (xQ L R Fp M1 * xQ L R Fp M2))) := by
    unfold dualW
    congr 2
    unfold AQ xQ
    simp only
    rw [nI_union hV1, nI_union hV2]
    field_simp
  unfold termQ aQ wQr
  rw [ite_eq_left hM1, ite_eq_left hM2]
  simp only
  rw [hx M1, hx M2, Complex.conj_conj, Complex.conj_conj, ← hk]
  unfold rcQ colQ
  simp only
  linear_combination ((-1 : ℂ) ^ T2.card * (-1) ^ V2.card) *
    (conj (aXi ξ (idl V2)) * aXi ξ (idl V2) * (chiS V2 μ * conj (chiS V2 μ)) *
      ((conj (chiS (b2 ∪ T2) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6)) *
          chiS (b2 ∪ T2) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6)) *
        (conj (chiS V2 (eS b ^ 4 * eS T ^ 5 * eS V ^ 6)) *
          chiS V2 (eS b ^ 4 * eS T ^ 5 * eS V ^ 6)))) *
    (conj (colA ξ (eS T2 * μ) (eS T2 * eS V2) M1 * chiS M1 (eS b ^ 4 * eS T ^ 5 * eS V ^ 6)) *
      (colA ξ (eS T2 * μ) (eS T2 * eS V2) M2 * chiS M2 (eS b ^ 4 * eS T ^ 5 * eS V ^ 6))) *
    (conj (MellinSep.W0c U (nI b2 * nI T2 * nI V2 * nI M1 / ellS L b T V)) *
      MellinSep.W0c U (nI b2 * nI T2 * nI V2 * nI M2 / ellS L b T V)) *
    dualW (Ycd cI S L F H b T) (V2 ∪ M1) (V2 ∪ M2) T2 μ * hw


open Classical in
/-- **A row's double column sum as the bilinear form**: the columns of the row are completed to all
subsets of `U₀`, where the coefficients `aQ` vanish outside the row's columns. -/
theorem rowSumQ_eq_bilinear (U : ℝ → ℂ) {H L S F cI R Fp : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hR : 0 < R) (hFp : 0 < Fp) (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U0 : Finset Pr)
    (ρ : RowQ) :
    ∑ M1 ∈ colRange U0 ρ, ∑ M2 ∈ colRange U0 ρ, termQ U H L S F cI ξ ρ M1 M2 =
      (WBQ cI S F L R : ℂ) * (wQr ξ R ρ * ∑ n1 ∈ U0.powerset, ∑ n2 ∈ U0.powerset,
        aQ U0 ξ ρ n1 * conj (aQ U0 ξ ρ n2) *
          ((fun y => conj (MellinSep.W0c U y)) (rhoQ R Fp ρ * xQ L R Fp n1) *
            conj ((fun y => conj (MellinSep.W0c U y)) (rhoQ R Fp ρ * xQ L R Fp n2)) *
            dualG (Real.sqrt (AQ cI S L F H R Fp ρ / (xQ L R Fp n1 * xQ L R Fp n2))))) := by
  set g : Finset Pr → Finset Pr → ℂ := fun n1 n2 => aQ U0 ξ ρ n1 * conj (aQ U0 ξ ρ n2) *
    ((fun y => conj (MellinSep.W0c U y)) (rhoQ R Fp ρ * xQ L R Fp n1) *
      conj ((fun y => conj (MellinSep.W0c U y)) (rhoQ R Fp ρ * xQ L R Fp n2)) *
      dualG (Real.sqrt (AQ cI S L F H R Fp ρ / (xQ L R Fp n1 * xQ L R Fp n2)))) with hg
  have hsub : colRange U0 ρ ⊆ U0.powerset :=
    Finset.powerset_mono.2 (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hz : ∀ n, n ∉ colRange U0 ρ → aQ U0 ξ ρ n = 0 := fun n hn => by
    unfold aQ; rw [ite_eq_right hn]
  have hext : ∑ n1 ∈ U0.powerset, ∑ n2 ∈ U0.powerset, g n1 n2 =
      ∑ n1 ∈ colRange U0 ρ, ∑ n2 ∈ colRange U0 ρ, g n1 n2 := by
    symm
    rw [Finset.sum_subset hsub fun n1 _ hn1 => Finset.sum_eq_zero fun n2 _ => by
      simp only [hg, hz n1 hn1, zero_mul]]
    refine Finset.sum_congr rfl fun n1 _ => ?_
    exact Finset.sum_subset hsub fun n2 _ hn2 => by simp only [hg, hz n2 hn2, map_zero, mul_zero,
      zero_mul]
  rw [hext, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M1 hM1 => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun M2 hM2 => termQ_eq_bilin U hH hL hR hFp ξ U0 ρ hM1 hM2

/-! ### The dyadic blocks -/

/-- The dyadic level `⌊log₂ N(A)⌋` of a set of primes. -/
def lvl (A : Finset Pr) : ℕ := Nat.log 2 (absNorm (idl A))

theorem lvl_le {A : Finset Pr} {x : ℝ} (h : nI A ≤ x) : lvl A ≤ Nat.log 2 ⌊x⌋₊ :=
  Nat.log_mono_right (Nat.le_floor (by unfold nI at h; exact_mod_cast h))

/-- `2^{lvl A} ≤ N(A) < 2·2^{lvl A}`. -/
theorem lvl_bounds (A : Finset Pr) :
    (2 : ℝ) ^ lvl A ≤ nI A ∧ nI A < 2 * (2 : ℝ) ^ lvl A := nI_log_bounds A

open Classical in
/-- `N(r)N(f′) ≤ 2βL` on the rows. -/
theorem nI_rQ_fQ_le {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} (h : ρ ∈ rowsQ U0 β H L S F) :
    nI (rQ ρ) * nI (fQ ρ) ≤ 2 * β * L := by
  rw [nI_rQ h, nI_fQ h]
  have hg := ((mem_rowsQ.1 h).2).2.1
  calc nI ρ.1.2.2 * nI ρ.2.1.1 * (nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2)
      = nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.1.2.2 * (nI ρ.2.1.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2) := by ring
    _ ≤ 2 * β * L := hg

open Classical in
/-- **The rows in dyadic blocks**: a sum over the rows is the sum over the blocks
`(lvl r, lvl f′) ∈ [0, ⌊log₂⌊2βL⌋⌋]²`. -/
theorem sum_rowsQ_blocks {U0 : Finset Pr} {β H L S F : ℝ} (G : RowQ → ℂ) :
    ∑ ρ ∈ rowsQ U0 β H L S F, G ρ =
      ∑ p ∈ Finset.range (Nat.log 2 ⌊2 * β * L⌋₊ + 1) ×ˢ Finset.range (Nat.log 2 ⌊2 * β * L⌋₊ + 1),
        ∑ ρ ∈ rowsQ U0 β H L S F with (lvl (rQ ρ), lvl (fQ ρ)) = p, G ρ := by
  refine (Finset.sum_fiberwise_of_maps_to (g := fun ρ : RowQ => (lvl (rQ ρ), lvl (fQ ρ)))
    (fun ρ hρ => ?_) G).symm
  have hrf := nI_rQ_fQ_le hρ
  have hr := one_le_nI (rQ ρ)
  have hf := one_le_nI (fQ ρ)
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range, Nat.lt_succ_iff, Nat.lt_succ_iff]
  exact ⟨lvl_le (by nlinarith), lvl_le (by nlinarith)⟩


end Eis

end

#print axioms Eis.ellS_le
#print axioms Eis.hY2_common
#print axioms Eis.Qform_le_split
#print axioms Eis.sum_wt_dualQ_eq
#print axioms Eis.rcQ_eq_zero_of_bT
#print axioms Eis.rcQ_eq_zero_of_V
#print axioms Eis.rcQ_eq_zero_of_W1
#print axioms Eis.rcQ_eq_zero_of_W2
#print axioms Eis.rcQ_eq_zero_of_dualW
#print axioms Eis.termQ_eq_zero_of_not_good
#print axioms Eis.sum_rows_eq_rowsQ
#print axioms Eis.mem_rowsQ
#print axioms Eis.rowsQ_disjoint
#print axioms Eis.nI_rQ
#print axioms Eis.nI_fQ
#print axioms Eis.termQ_eq_bilin
#print axioms Eis.rowSumQ_eq_bilinear
#print axioms Eis.lvl_le
#print axioms Eis.lvl_bounds
#print axioms Eis.nI_rQ_fQ_le
#print axioms Eis.sum_rowsQ_blocks
