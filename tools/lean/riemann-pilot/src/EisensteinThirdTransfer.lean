import EisensteinTransferColumns

/-! # Lemma 7.3 (round 325)

S5c-5, part 4, in round 316's plan: the companion paper's Lemma 7.3,
"`\mathcal Q_{\xi_1}(U)\ll D^{\varepsilon_0}\Sigma(1+S_m) \|U\|_{C^{2m+4}(I_*)}^2`", in the pilot's form, from
the blocks of rounds 323–324.

* **The block quantities** (`norm_wQr_le`, `norm_wQr_blk_le`, `rhoQ_blk_mem`, `AQ_blk_ge`): on a block,
  `|w_ρ| ≤ 1`, `ρ_ρ ∈ [1, 4]` and `A_ρ ≥ 1/(3𝓗L)`.
* **The bound for one block** (**`blockQ_bound`**): round 317's `bilinear_dual_bound_unif` with the bump
  equal to `1` on `[α/8, 2β]`, `W₀ = conj ∘ W₀c U` and round 324's column mean square.
* **The counting factors** (`nI_rQ_le`, `nI_fQ_le`, `four_pow_le_of`, `mult_le`, `sum_four_pow_rQ_le`,
  `one_div_rpow_neg`, `blockBoundQ_eq`): `2^{|r|}8^{|f′|} ≤ C³(2βL)^{3δ}` and
  `Σ_r 4^{|r|} ≤ (2κ+5)·2R·C(2βL)^δ`, after which `R` cancels (the paper's
  "`(\Sigma R/L^2)R(L/R)^2=\Sigma`").
* **All blocks** (**`dualQ_sum_le`**) and **the zero frequencies** (`mem_qTriples`,
  `sum_qTriples_inv_le`, **`zeroQ_sum_le`**).
* **Lemma 7.3** (`rpow_pow_le`, `add_le_one_add_mul`, **`third_transfer`**):
  `𝒬_{ξ₁}(U) ≤ K·c_IΣFL·(3𝓗L)^σ·L^η·(1 + M)·N_U²` under `ChildBound α β m 𝓗 L Σ F M`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The block quantities -/

theorem norm_mul_conj_le_one {z : ℂ} (h : ‖z‖ ≤ 1) : ‖conj z * z‖ ≤ 1 := by
  rw [norm_mul, RCLike.norm_conj]
  calc ‖z‖ * ‖z‖ ≤ 1 * 1 := mul_le_mul h h (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_mul_conj_le_one' {z : ℂ} (h : ‖z‖ ≤ 1) : ‖z * conj z‖ ≤ 1 := by
  rw [mul_comm]; exact norm_mul_conj_le_one h

/-- `|w_ρ| ≤ 1` when `N(V)N(b₂) ≤ 2R`. -/
theorem norm_wQr_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {R : ℝ} (hR : 0 < R) (ρ : RowQ)
    (h : nI ρ.1.2.2 * nI ρ.2.1.1 ≤ 2 * R) : ‖wQr ξ R ρ‖ ≤ 1 := by
  unfold wQr
  have hs : ‖(-1 : ℂ) ^ ρ.2.1.2.1.card * (-1) ^ ρ.2.1.2.2.card‖ = 1 := by
    rw [norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_pow, one_mul]
  have h1 := norm_mul_conj_le_one (norm_aXi_le ξ (idl ρ.2.1.2.2))
  have h2 := norm_mul_conj_le_one' (norm_chiS_le ρ.2.1.2.2 ρ.2.2)
  have h3 := norm_mul_conj_le_one
    (norm_chiS_le (ρ.2.1.1 ∪ ρ.2.1.2.1) (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6))
  have h4 := norm_mul_conj_le_one
    (norm_chiS_le ρ.2.1.2.2 (eS ρ.1.1 ^ 4 * eS ρ.1.2.1 ^ 5 * eS ρ.1.2.2 ^ 6))
  have hp : 0 ≤ nI ρ.1.2.2 * nI ρ.2.1.1 / (2 * R) := by
    have := nI_pos ρ.1.2.2; have := nI_pos ρ.2.1.1; positivity
  have h5 : ‖((nI ρ.1.2.2 * nI ρ.2.1.1 / (2 * R) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hp, div_le_one (by positivity)]
    exact h
  exact norm_mul_le_one (norm_mul_le_one hs.le
    (norm_mul_le_one (norm_mul_le_one h1 h2) (norm_mul_le_one h3 h4))) h5

open Classical in
/-- The row weights of a block: `|w_ρ| ≤ 1`. -/
theorem norm_wQr_blk_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U0 : Finset Pr}
    {β H L S F : ℝ} {p : ℕ × ℕ} {ρ : RowQ} (h : ρ ∈ blkQ U0 β H L S F p) :
    ‖wQr ξ ((2 : ℝ) ^ p.1) ρ‖ ≤ 1 := by
  obtain ⟨hρ, -, hr2, -, -⟩ := mem_blkQ h
  refine norm_wQr_le ξ (by positivity) ρ ?_
  rw [← nI_rQ hρ]; exact hr2.le

open Classical in
/-- The dilations of a block lie in `[1, 4]`. -/
theorem rhoQ_blk_mem {U0 : Finset Pr} {β H L S F : ℝ} {p : ℕ × ℕ} {ρ : RowQ}
    (h : ρ ∈ blkQ U0 β H L S F p) :
    1 ≤ rhoQ ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) ρ ∧ rhoQ ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) ρ ≤ 4 := by
  obtain ⟨hρ, hr1, hr2, hf1, hf2⟩ := mem_blkQ h
  have e : rhoQ ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) ρ =
      nI (rQ ρ) * nI (fQ ρ) / ((2 : ℝ) ^ p.1 * (2 : ℝ) ^ p.2) := by
    unfold rhoQ; rw [nI_rQ hρ, nI_fQ hρ]; ring
  have hR0 : (0 : ℝ) < (2 : ℝ) ^ p.1 := by positivity
  have hF0 : (0 : ℝ) < (2 : ℝ) ^ p.2 := by positivity
  rw [e]
  constructor
  · rw [one_le_div (by positivity)]
    exact mul_le_mul hr1 hf1 hF0.le (nI_pos _).le
  · rw [div_le_iff₀ (by positivity)]
    have := mul_lt_mul'' hr2 hf2 (nI_pos _).le (nI_pos _).le
    nlinarith

open Classical in
/-- **The lower bound for the kernel parameters of a block**: `A_ρ ≥ 1/(3𝓗L)` for `c_I, Σ, F ≥ 1`. -/
theorem AQ_blk_ge {U0 : Finset Pr} {β H L S F cI : ℝ} (hH : 0 < H) (hL : 0 < L) (hS : 1 ≤ S)
    (hF : 1 ≤ F) (hcI : 1 ≤ cI) {p : ℕ × ℕ} {ρ : RowQ} (h : ρ ∈ blkQ U0 β H L S F p) :
    1 / (3 * H * L) ≤ AQ cI S L F H ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) ρ := by
  obtain ⟨hρ, hr1, -, -, hf2⟩ := mem_blkQ h
  obtain ⟨⟨-, -, hμ⟩, -⟩ := mem_rowsQ.1 hρ
  have hNμ : (1 : ℝ) ≤ (absNorm (span {ρ.2.2}) : ℝ) :=
    one_le_absNorm_span (Finset.ne_of_mem_erase hμ)
  set R : ℝ := (2 : ℝ) ^ p.1
  set Fp : ℝ := (2 : ℝ) ^ p.2
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hb := nI_pos ρ.1.1
  have hT := nI_pos ρ.1.2.1
  have hT2 := nI_pos ρ.2.1.2.1
  have hV2 := nI_pos ρ.2.1.2.2
  have hT1 := one_le_nI ρ.1.2.1
  have hT21 := one_le_nI ρ.2.1.2.1
  have hFp0 : (0 : ℝ) < Fp := by positivity
  have e : AQ cI S L F H R Fp ρ =
      (4 * cI * S * F * (absNorm (span {ρ.2.2}) : ℝ) * R ^ 2 * Fp ^ 2) /
      (3 * H * L * (nI ρ.1.1 ^ 2 * nI ρ.1.2.1 * nI ρ.2.1.2.2 ^ 2 * nI ρ.2.1.2.1)) := by
    unfold AQ Ycd; field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have hf : nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2 < 2 * Fp := by
    rw [← nI_fQ hρ]; exact hf2
  have h4 : (nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2) ^ 2 < 4 * Fp ^ 2 := by
    have := pow_lt_pow_left₀ hf (by positivity) (two_ne_zero)
    nlinarith
  have h5 : nI ρ.1.1 ^ 2 * nI ρ.1.2.1 * nI ρ.2.1.2.2 ^ 2 * nI ρ.2.1.2.1 ≤
      (nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2) ^ 2 := by
    have e2 : (nI ρ.1.1 * nI ρ.1.2.1 * nI ρ.2.1.2.1 * nI ρ.2.1.2.2) ^ 2 =
        nI ρ.1.1 ^ 2 * nI ρ.1.2.1 * nI ρ.2.1.2.2 ^ 2 * nI ρ.2.1.2.1 *
          (nI ρ.1.2.1 * nI ρ.2.1.2.1) := by ring
    rw [e2]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hT1 hT21)
  have h6 : 1 ≤ cI * S * F * (absNorm (span {ρ.2.2}) : ℝ) * R ^ 2 := by
    have : 1 ≤ R ^ 2 := one_le_pow₀ hR1
    have h1 : 1 ≤ cI * S := one_le_mul_of_one_le_of_one_le hcI hS
    have h2 : 1 ≤ cI * S * F := one_le_mul_of_one_le_of_one_le h1 hF
    have h3 : 1 ≤ cI * S * F * (absNorm (span {ρ.2.2}) : ℝ) :=
      one_le_mul_of_one_le_of_one_le h2 hNμ
    exact one_le_mul_of_one_le_of_one_le h3 this
  have hkey : nI ρ.1.1 ^ 2 * nI ρ.1.2.1 * nI ρ.2.1.2.2 ^ 2 * nI ρ.2.1.2.1 ≤
      4 * cI * S * F * (absNorm (span {ρ.2.2}) : ℝ) * R ^ 2 * Fp ^ 2 := by
    calc nI ρ.1.1 ^ 2 * nI ρ.1.2.1 * nI ρ.2.1.2.2 ^ 2 * nI ρ.2.1.2.1
        ≤ 4 * Fp ^ 2 := h5.trans h4.le
      _ = 4 * Fp ^ 2 * 1 := (mul_one _).symm
      _ ≤ 4 * Fp ^ 2 * (cI * S * F * (absNorm (span {ρ.2.2}) : ℝ) * R ^ 2) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 4 * cI * S * F * (absNorm (span {ρ.2.2}) : ℝ) * R ^ 2 * Fp ^ 2 := by ring
  have hHL : 0 < 3 * H * L := by positivity
  nlinarith

/-! ### The bound for one block -/

open Classical in
/-- **The bound for one block** (the companion paper's application of its Lemma B.2 in the proof of
Lemma 7.3, through round 317's `bilinear_dual_bound_unif` with dilations in `[1, 4]`): for a test
function `U` supported in `[α/2, 2β]` with its first `2m+2` derivatives bounded by `N_U`, the rows of
one block contribute at most `W_B·K·N_U²·A_min^{−σ}·B·Σ_r 4^{|r|}·(M + C_triv)·(L/R)²`, with
`A_min = 1/(3𝓗L)`. -/
theorem blockQ_bound {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (m : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ), ContDiff ℝ ∞ U →
      (∀ x, x < α / 2 ∨ 2 * β < x → U x = 0) → ∀ NU : ℝ,
      (∀ j ≤ 2 * m + 2, ∀ x, ‖iteratedDeriv j U x‖ ≤ NU) →
      ∀ {Hh L S F cI M : ℝ}, 1 ≤ Hh → 1 ≤ L → 1 ≤ F → Hh ≤ S → 1 ≤ cI → 0 ≤ M →
      ChildBound α β m Hh L S F M →
      ∀ {U0 : Finset Pr}, primesLe (4 * β * L) ⊆ U0 → ∀ (p : ℕ × ℕ) {Bm : ℝ}, 0 ≤ Bm →
      (∀ ρ ∈ blkQ U0 β Hh L S F p, (2 : ℝ) ^ (rQ ρ).card * 8 ^ (fQ ρ).card ≤ Bm) →
      ‖∑ ρ ∈ blkQ U0 β Hh L S F p, ∑ M1 ∈ colRange U0 ρ, ∑ M2 ∈ colRange U0 ρ,
          termQ U Hh L S F cI ξ ρ M1 M2‖ ≤
        WBQ cI S F L ((2 : ℝ) ^ p.1) * (Kb * NU ^ 2 * (1 / (3 * Hh * L)) ^ (-σ) *
          (Bm * ((∑ r ∈ (blkQ U0 β Hh L S F p).image rQ, (4 : ℝ) ^ r.card) *
            ((M + Ctriv β) * (L / (2 : ℝ) ^ p.1) ^ 2)))) := by
  have hβ : 0 ≤ β := le_trans hα.le hαβ
  have hα8 : 0 < α / 8 := by positivity
  have hαβ8 : α / 8 ≤ 2 * β := by linarith
  obtain ⟨V, hV, hVc, hVp, hVs, hV1⟩ := exists_bump_one hα8 hαβ8
  have hα2 : 0 < α / 2 := by positivity
  have hαβ2 : α / 2 ≤ 2 * β := by linarith
  obtain ⟨Kb, hKb0, hKb⟩ := MellinSep.bilinear_dual_bound_unif hα2 hαβ2 V hV hVc hVp
    (ρ0 := 1) (ρ1 := 4) one_pos (fun y h1 h2 => hV1 y (by linarith) (by rwa [div_one] at h2)) m
    dualG dualG_contDiff dualG_bounded (fun ρ h => dualG_eq_zero_of_ge h) hσ
  obtain ⟨Cw, hCw0, hCw⟩ := MellinSep.W0c_unif hα2 hαβ2 (2 * m + 2)
  refine ⟨Kb * Cw ^ 2, by positivity, fun ξ U hU hUs NU hNU Hh L S F cI M hH hL hF hHS hcI hM0 hM
    U0 hU0 p Bm hBm0 hBm => ?_⟩
  obtain ⟨hW0, hW0d⟩ := hCw U hU hUs NU hNU
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < Hh := by linarith
  have hS1 : 1 ≤ S := hH.trans hHS
  set R : ℝ := (2 : ℝ) ^ p.1 with hRdef
  set Fp : ℝ := (2 : ℝ) ^ p.2 with hFpdef
  have hR0 : 0 < R := by positivity
  have hFp0 : 0 < Fp := by positivity
  set blk := blkQ U0 β Hh L S F p with hblk
  set Mb := Bm * ((∑ r ∈ blk.image rQ, (4 : ℝ) ^ r.card) * ((M + Ctriv β) * (L / R) ^ 2))
    with hMb
  have hMb0 : 0 ≤ Mb := by
    have := Ctriv_nonneg hβ
    positivity
  -- the rows as the bilinear form
  rw [Finset.sum_congr rfl fun ρ _ => rowSumQ_eq_bilinear U hH0 hL0 hR0 hFp0 ξ U0 ρ,
    ← Finset.mul_sum, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by unfold WBQ; positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by unfold WBQ; positivity)
  -- the column mean squares
  have hcol : ∀ U' : ℝ → ℂ, ContDiff ℝ ∞ U' → tsupport U' ⊆ tsupport V → ∀ N : ℝ,
      (∀ j ≤ m, ∀ y, ‖iteratedDeriv j U' y‖ ≤ N) →
      ∑ ρ ∈ blk, ‖∑ n ∈ U0.powerset, aQ U0 ξ ρ n * U' (xQ L R Fp n)‖ ^ 2 ≤ Mb * N ^ 2 := by
    intro U' hU' hU's N hN
    have hU'v : ∀ x, x < α / 16 ∨ 4 * β < x → U' x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => by
        have := hVs (hU's h)
        rw [Set.mem_Icc] at this
        rcases hx with hx | hx
        · have : α / 8 / 2 ≤ x := this.1
          linarith
        · have : x ≤ 2 * (2 * β) := this.2
          linarith
    have h := blockQ_colMS hβ hM hM0 hHS hF hL0 hH0 hU0 ξ p hBm hU' hU'v hN
    calc _ ≤ Bm * ((∑ r ∈ blk.image rQ, (4 : ℝ) ^ r.card) *
          ((M + Ctriv β) * N ^ 2 * (L / R) ^ 2)) := h
      _ = Mb * N ^ 2 := by rw [hMb]; ring
  have hb := hKb (fun y => conj (MellinSep.W0c U y)) (contDiff_conj_comp hW0)
    (fun y hy => by simp only [MellinSep.W0c_eq_zero hUs hy, map_zero]) (Cw * NU)
    (fun j hj y => by rw [norm_iteratedDeriv_conj_comp]; exact hW0d j hj y)
    blk U0.powerset (aQ U0 ξ) (aQ U0 ξ) (xQ L R Fp)
    (fun n _ => by unfold xQ; have := nI_pos n; positivity) Mb hMb0 hcol hcol
    (rhoQ R Fp) (fun ρ hρ => rhoQ_blk_mem hρ) (wQr ξ R) (fun ρ hρ => norm_wQr_blk_le ξ hρ)
    (AQ cI S L F Hh R Fp) (1 / (3 * Hh * L)) (by positivity)
    (fun ρ hρ => AQ_blk_ge hH0 hL0 hS1 hF hcI hρ)
  calc _ ≤ Kb * (Cw * NU) ^ 2 * (1 / (3 * Hh * L)) ^ (-σ) * Mb := hb
    _ = Kb * Cw ^ 2 * NU ^ 2 * (1 / (3 * Hh * L)) ^ (-σ) * Mb := by ring


/-! ### The counting factors of a block -/

open Classical in
/-- `N(r), N(f′) ≤ 2βL` on the rows. -/
theorem nI_rQ_le {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} (h : ρ ∈ rowsQ U0 β H L S F) :
    nI (rQ ρ) ≤ 2 * β * L :=
  le_trans (le_mul_of_one_le_right (nI_pos _).le (one_le_nI _)) (nI_rQ_fQ_le h)

open Classical in
theorem nI_fQ_le {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} (h : ρ ∈ rowsQ U0 β H L S F) :
    nI (fQ ρ) ≤ 2 * β * L :=
  le_trans (le_mul_of_one_le_left (nI_pos _).le (one_le_nI _)) (nI_rQ_fQ_le h)

/-- `4^{|A|} ≤ C·x^δ` for `N(A) ≤ x`. -/
theorem four_pow_le_of {δ C : ℝ} (hδ : 0 < δ) (hC : ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ C * nI b ^ δ)
    {A : Finset Pr} {x : ℝ} (hx : nI A ≤ x) : (4 : ℝ) ^ A.card ≤ C * x ^ δ := by
  have hC0 : 0 ≤ C := by
    have := hC ∅
    simp only [Finset.card_empty, pow_zero, nI_empty, Real.one_rpow, mul_one] at this
    linarith
  exact (hC A).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (nI_pos A).le hx hδ.le) hC0)

open Classical in
/-- **The multiplicity bound on the rows**: `2^{|r|}8^{|f′|} ≤ C³(2βL)^{3δ}`. -/
theorem mult_le {δ C : ℝ} (hδ : 0 < δ) (hC : ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ C * nI b ^ δ)
    {U0 : Finset Pr} {β H L S F : ℝ} {ρ : RowQ} (h : ρ ∈ rowsQ U0 β H L S F) :
    (2 : ℝ) ^ (rQ ρ).card * 8 ^ (fQ ρ).card ≤ C ^ 3 * ((2 * β * L) ^ δ) ^ 3 := by
  have h1 := four_pow_le_of hδ hC (nI_rQ_le h)
  have h2 := four_pow_le_of hδ hC (nI_fQ_le h)
  have h2' : (2 : ℝ) ^ (rQ ρ).card ≤ (4 : ℝ) ^ (rQ ρ).card :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h8 : (8 : ℝ) ^ (fQ ρ).card ≤ ((4 : ℝ) ^ (fQ ρ).card) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h40 : (0 : ℝ) ≤ (4 : ℝ) ^ (fQ ρ).card := by positivity
  calc (2 : ℝ) ^ (rQ ρ).card * 8 ^ (fQ ρ).card
      ≤ (4 : ℝ) ^ (rQ ρ).card * ((4 : ℝ) ^ (fQ ρ).card) ^ 2 :=
        mul_le_mul h2' h8 (by positivity) (by positivity)
    _ ≤ (C * (2 * β * L) ^ δ) * (C * (2 * β * L) ^ δ) ^ 2 :=
        mul_le_mul h1 (pow_le_pow_left₀ h40 h2 2) (by positivity) (le_trans (by positivity) h1)
    _ = C ^ 3 * ((2 * β * L) ^ δ) ^ 3 := by ring

open Classical in
/-- **The sum of `4^{|r|}` over the sets `r` of a block**: at most `(2κ+5)·2R·C(2βL)^δ`. -/
theorem sum_four_pow_rQ_le {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ C * nI b ^ δ) {U0 : Finset Pr} {β H L S F : ℝ}
    (hβL : 0 < 2 * β * L) (p : ℕ × ℕ) :
    ∑ r ∈ (blkQ U0 β H L S F p).image rQ, (4 : ℝ) ^ r.card ≤
      (2 * kappa + 5) * (2 * (2 : ℝ) ^ p.1) * (C * (2 * β * L) ^ δ) := by
  have hC0 : 0 ≤ C := by
    have := hC ∅
    simp only [Finset.card_empty, pow_zero, nI_empty, Real.one_rpow, mul_one] at this
    linarith
  have hsub : (blkQ U0 β H L S F p).image rQ ⊆ fsLe (2 * (2 : ℝ) ^ p.1) := by
    intro r hr
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hr
    exact mem_fsLe_of_nI_le (mem_blkQ hρ).2.2.1.le
  have hterm : ∀ r ∈ (blkQ U0 β H L S F p).image rQ, (4 : ℝ) ^ r.card ≤ C * (2 * β * L) ^ δ := by
    intro r hr
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hr
    exact four_pow_le_of hδ hC (nI_rQ_le (mem_blkQ hρ).1)
  have hk := kappa_pos
  calc ∑ r ∈ (blkQ U0 β H L S F p).image rQ, (4 : ℝ) ^ r.card
      ≤ ∑ _r ∈ (blkQ U0 β H L S F p).image rQ, C * (2 * β * L) ^ δ := Finset.sum_le_sum hterm
    _ = ((blkQ U0 β H L S F p).image rQ).card * (C * (2 * β * L) ^ δ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (fsLe (2 * (2 : ℝ) ^ p.1)).card * (C * (2 * β * L) ^ δ) := by
        gcongr
    _ ≤ (2 * kappa + 5) * (2 * (2 : ℝ) ^ p.1) * (C * (2 * β * L) ^ δ) := by
        gcongr
        exact card_fsLe_le (by have : (1 : ℝ) ≤ (2 : ℝ) ^ p.1 := one_le_pow₀ (by norm_num); linarith)

/-- `(1/(3𝓗L))^{−σ} = (3𝓗L)^σ`. -/
theorem one_div_rpow_neg {x σ : ℝ} (hx : 0 < x) : (1 / x) ^ (-σ) = x ^ σ := by
  rw [Real.rpow_neg (by positivity), one_div, Real.inv_rpow hx.le, inv_inv]

/-- **The bound for one block, simplified**: the factor `R` cancels,
`W_B·K·N²·(3𝓗L)^σ·C³(2βL)^{3δ}·(2κ+5)2RC(2βL)^δ·(M + C_triv)(L/R)²
= (16/3)(2κ+5)·K·C⁴·c_IΣFL·(3𝓗L)^σ·((2βL)^δ)⁴·(M + C_triv)·N²`. -/
theorem blockBoundQ_eq {cI S F L R Kb NU Hh σ C δ β M Ct : ℝ} (hL : 0 < L) (hR : 0 < R) :
    WBQ cI S F L R * (Kb * NU ^ 2 * (3 * Hh * L) ^ σ *
      (C ^ 3 * ((2 * β * L) ^ δ) ^ 3 * ((2 * kappa + 5) * (2 * R) * (C * (2 * β * L) ^ δ) *
        ((M + Ct) * (L / R) ^ 2)))) =
    16 / 3 * (2 * kappa + 5) * Kb * C ^ 4 * (cI * S * F * L) * (3 * Hh * L) ^ σ *
      ((2 * β * L) ^ δ) ^ 4 * (M + Ct) * NU ^ 2 := by
  unfold WBQ
  field_simp
  ring


/-! ### The nonzero frequencies over all blocks -/

open Classical in
/-- **The nonzero frequencies of `𝒬` in one character** (the blocks of the companion paper's proof of
Lemma 7.3 summed): `‖Σ_t w_t·dualQ ξ t‖ ≤ (⌊log₂⌊2βL⌋⌋ + 1)²·K·c_IΣFL·(3𝓗L)^σ·((2βL)^δ)⁴·
(M + C_triv)·N_U²`. -/
theorem dualQ_sum_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (m : ℕ) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ), ContDiff ℝ ∞ U →
      (∀ x, x < α / 2 ∨ 2 * β < x → U x = 0) → ∀ NU : ℝ,
      (∀ j ≤ 2 * m + 2, ∀ x, ‖iteratedDeriv j U x‖ ≤ NU) →
      ∀ {Hh L S F cI M : ℝ}, 1 ≤ Hh → 1 ≤ L → 1 ≤ F → Hh ≤ S → 3 * β ^ 2 * RΦ ^ 2 ≤ cI →
      1 ≤ cI → 0 ≤ M → ChildBound α β m Hh L S F M →
      ‖∑ t ∈ qTriples (2 * β * L),
          (wtQ Hh L t : ℂ) * dualQ U Hh L S F cI (primesLe (4 * β * L)) ξ t‖ ≤
        ((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (Kd * (cI * S * F * L) *
          (3 * Hh * L) ^ σ * ((2 * β * L) ^ δ) ^ 4 * (M + Ctriv β) * NU ^ 2) := by
  obtain ⟨Kb, hKb0, hKb⟩ := blockQ_bound hα hαβ m hσ
  obtain ⟨C4, hC40, hC4⟩ := four_pow_card_le hδ
  have hk := kappa_pos
  refine ⟨16 / 3 * (2 * kappa + 5) * Kb * C4 ^ 4, by positivity,
    fun ξ U hU hUs NU hNU Hh L S F cI M hH hL hF hHS hcI hcI1 hM0 hM => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < Hh := by linarith
  have hS0 : 0 < S := by linarith
  have hF0 : 0 < F := by linarith
  have hβL : 0 < 2 * β * L := by positivity
  set U0 := primesLe (4 * β * L) with hU0def
  have hU2 : ∀ x, 2 * β < x → U x = 0 := fun x hx => hUs x (Or.inr hx)
  set NL := Nat.log 2 ⌊2 * β * L⌋₊ with hNL
  set Bblk := 16 / 3 * (2 * kappa + 5) * Kb * C4 ^ 4 * (cI * S * F * L) * (3 * Hh * L) ^ σ *
    ((2 * β * L) ^ δ) ^ 4 * (M + Ctriv β) * NU ^ 2 with hBblk
  rw [sum_wt_dualQ_eq, sum_rows_eq_rowsQ hU2 hH0 hL0 hS0 hF0 hcI, sum_rowsQ_blocks]
  have hblk : ∀ p ∈ Finset.range (NL + 1) ×ˢ Finset.range (NL + 1),
      ‖∑ ρ ∈ blkQ U0 β Hh L S F p, ∑ M1 ∈ colRange U0 ρ, ∑ M2 ∈ colRange U0 ρ,
        termQ U Hh L S F cI ξ ρ M1 M2‖ ≤ Bblk := by
    intro p _
    have hBm0 : 0 ≤ C4 ^ 3 * ((2 * β * L) ^ δ) ^ 3 := by positivity
    have hb := hKb ξ U hU hUs NU hNU hH hL hF hHS hcI1 hM0 hM (le_refl U0) p hBm0
      (fun ρ hρ => mult_le hδ hC4 (Finset.mem_filter.1 hρ).1)
    have hS4 := sum_four_pow_rQ_le hδ hC4 hβL (U0 := U0) (H := Hh) (S := S) (F := F) p
    have hR0 : (0 : ℝ) < (2 : ℝ) ^ p.1 := by positivity
    have hCt := Ctriv_nonneg hβ.le
    refine hb.trans ?_
    rw [one_div_rpow_neg (by positivity : (0 : ℝ) < 3 * Hh * L), hBblk,
      ← blockBoundQ_eq (cI := cI) (S := S) (F := F) (Kb := Kb) (NU := NU) (Hh := Hh) (σ := σ)
        (C := C4) (δ := δ) (β := β) (M := M) (Ct := Ctriv β) hL0 hR0]
    have hW : 0 ≤ WBQ cI S F L ((2 : ℝ) ^ p.1) := by unfold WBQ; positivity
    gcongr
  have hcard : ((Finset.range (NL + 1) ×ˢ Finset.range (NL + 1)).card : ℝ) =
      ((NL : ℕ) + 1 : ℝ) ^ 2 := by
    rw [Finset.card_product, Finset.card_range]; push_cast; ring
  calc _ ≤ ∑ p ∈ Finset.range (NL + 1) ×ˢ Finset.range (NL + 1),
        ‖∑ ρ ∈ blkQ U0 β Hh L S F p, ∑ M1 ∈ colRange U0 ρ, ∑ M2 ∈ colRange U0 ρ,
          termQ U Hh L S F cI ξ ρ M1 M2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.range (NL + 1) ×ˢ Finset.range (NL + 1), Bblk := Finset.sum_le_sum hblk
    _ = ((NL : ℕ) + 1 : ℝ) ^ 2 * Bblk := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = _ := by rw [hBblk]


/-! ### The zero frequencies -/

open Classical in
theorem mem_qTriples {Λ : ℝ} {t : Finset Pr × Finset Pr × Finset Pr} (h : t ∈ qTriples Λ) :
    (t.1 ∈ fsLe Λ ∧ t.2.1 ∈ fsLe Λ ∧ t.2.2 ∈ fsLe Λ) ∧
      nI t.1 * nI t.2.1 * nI t.2.2 ≤ Λ := by
  unfold qTriples at h
  simp only [Finset.mem_filter, Finset.mem_product] at h
  exact ⟨h.1, h.2.2.2⟩

open Classical in
/-- The harmonic sum over the triples: `Σ_t 1/(N(b)N(T)N(V)) ≤ (Σ_{A∈fsLe Λ} 1/N(A))³`. -/
theorem sum_qTriples_inv_le (Λ : ℝ) :
    ∑ t ∈ qTriples Λ, 1 / (nI t.1 * nI t.2.1 * nI t.2.2) ≤ (∑ A ∈ fsLe Λ, 1 / nI A) ^ 3 := by
  have hsub : qTriples Λ ⊆ fsLe Λ ×ˢ fsLe Λ ×ˢ fsLe Λ := Finset.filter_subset _ _
  have hnn : ∀ t : Finset Pr × Finset Pr × Finset Pr, 0 ≤ 1 / (nI t.1 * nI t.2.1 * nI t.2.2) :=
    fun t => by have := nI_pos t.1; have := nI_pos t.2.1; have := nI_pos t.2.2; positivity
  calc ∑ t ∈ qTriples Λ, 1 / (nI t.1 * nI t.2.1 * nI t.2.2)
      ≤ ∑ t ∈ fsLe Λ ×ˢ fsLe Λ ×ˢ fsLe Λ, 1 / (nI t.1 * nI t.2.1 * nI t.2.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => hnn t
    _ = ∑ b ∈ fsLe Λ, ∑ T ∈ fsLe Λ, ∑ V ∈ fsLe Λ, 1 / nI b * (1 / nI T * (1 / nI V)) := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun V _ => ?_
        have := nI_pos b; have := nI_pos T; have := nI_pos V
        field_simp
    _ = (∑ A ∈ fsLe Λ, 1 / nI A) ^ 3 := by
        rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.mul_sum]

open Classical in
/-- **The zero frequencies of `𝒬`** (the companion paper's `|Z| ≪ Yℓ‖U‖²_∞` of Lemma 7.2 summed over
(7.2)): `‖Σ_t w_t·zeroQ t‖ ≤ (2κ+5)·(8/3)β|Φ̂(0)|·c_IΣFL·N_U²·(2(2κ+5)(⌊log₂⌊2βL⌋⌋ + 1))³`. -/
theorem zeroQ_sum_le {U : ℝ → ℂ} {NU : ℝ} (hNU : ∀ x, ‖U x‖ ≤ NU) {β H L S F cI : ℝ}
    (hβ : 0 ≤ β) (hH : 0 < H) (hL : 0 < L) (hS : 0 < S) (hF : 0 < F) (hcI : 0 < cI) :
    ‖∑ t ∈ qTriples (2 * β * L), (wtQ H L t : ℂ) * zeroQ U β H L S F cI t‖ ≤
      (2 * kappa + 5) * (8 / 3 * β) * ‖dualG 0‖ * (cI * S * F * L) * NU ^ 2 *
        (2 * (2 * kappa + 5) * ((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) + 1 : ℝ)) ^ 3 := by
  have hk := kappa_pos
  have hNU0 : 0 ≤ NU := (norm_nonneg _).trans (hNU 0)
  set Cz := (2 * kappa + 5) * (8 / 3 * β) * ‖dualG 0‖ * (cI * S * F * L) * NU ^ 2 with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hterm : ∀ t ∈ qTriples (2 * β * L), ‖(wtQ H L t : ℂ) * zeroQ U β H L S F cI t‖ ≤
      Cz * (1 / (nI t.1 * nI t.2.1 * nI t.2.2)) := by
    intro t ht
    obtain ⟨-, hprod⟩ := mem_qTriples ht
    have hb := nI_pos t.1
    have hT := nI_pos t.2.1
    have hV := nI_pos t.2.2
    have hb1 := one_le_nI t.1
    have hT1 := one_le_nI t.2.1
    set ℓ := ellS L t.1 t.2.1 t.2.2 with hℓ
    set Y := Ycd cI S L F H t.1 t.2.1 with hY
    have hY0 : 0 ≤ Y := (Ycd_pos hcI hS hL hF hH t.1 t.2.1).le
    have hz := zero_Mq_le hNU ℓ (eS t.1 ^ 4 * eS t.2.1 ^ 5 * eS t.2.2 ^ 6) hY0
      (fsLe (2 * β * ℓ))
    have h1 : 1 ≤ 2 * β * ℓ := by
      rw [hℓ]; unfold ellS
      rw [← mul_div_assoc, le_div_iff₀ (by positivity), one_mul]
      exact hprod
    have hcard := card_fsLe_le h1
    have hw0 : 0 ≤ wtQ H L t := by unfold wtQ; positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    have hz' : ‖zeroQ U β H L S F cI t‖ ≤
        (2 * kappa + 5) * (2 * β * ℓ) * (NU ^ 2 * (2 * Y / Real.sqrt 3 * ‖dualG 0‖)) :=
      hz.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hs30 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have e : wtQ H L t * ((2 * kappa + 5) * (2 * β * ℓ) *
        (NU ^ 2 * (2 * Y / Real.sqrt 3 * ‖dualG 0‖))) =
        Cz * (1 / (nI t.1 * nI t.2.1 * nI t.2.2)) * (1 / (nI t.1 * nI t.2.1)) := by
      rw [hCz, hℓ, hY]
      unfold wtQ ellS Ycd
      field_simp
      rw [show Real.sqrt 3 ^ 2 = 3 by rw [sq]; exact hs3]
      ring
    have hle : 1 / (nI t.1 * nI t.2.1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_mul_of_one_le_of_one_le hb1 hT1
    calc wtQ H L t * ‖zeroQ U β H L S F cI t‖
        ≤ wtQ H L t * ((2 * kappa + 5) * (2 * β * ℓ) *
          (NU ^ 2 * (2 * Y / Real.sqrt 3 * ‖dualG 0‖))) := mul_le_mul_of_nonneg_left hz' hw0
      _ = Cz * (1 / (nI t.1 * nI t.2.1 * nI t.2.2)) * (1 / (nI t.1 * nI t.2.1)) := e
      _ ≤ Cz * (1 / (nI t.1 * nI t.2.1 * nI t.2.2)) * 1 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = Cz * (1 / (nI t.1 * nI t.2.1 * nI t.2.2)) := mul_one _
  calc _ ≤ ∑ t ∈ qTriples (2 * β * L), ‖(wtQ H L t : ℂ) * zeroQ U β H L S F cI t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ qTriples (2 * β * L), Cz * (1 / (nI t.1 * nI t.2.1 * nI t.2.2)) :=
        Finset.sum_le_sum hterm
    _ = Cz * ∑ t ∈ qTriples (2 * β * L), 1 / (nI t.1 * nI t.2.1 * nI t.2.2) := by
        rw [Finset.mul_sum]
    _ ≤ Cz * (∑ A ∈ fsLe (2 * β * L), 1 / nI A) ^ 3 :=
        mul_le_mul_of_nonneg_left (sum_qTriples_inv_le _) hCz0
    _ ≤ Cz * (2 * (2 * kappa + 5) * ((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) + 1 : ℝ)) ^ 3 := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ (sum_fsLe_inv_le _) 3) hCz0
        exact Finset.sum_nonneg fun A _ => by have := nI_pos A; positivity


/-! ### Lemma 7.3 -/

/-- `(L^e)^k ≤ L^η` for `L ≥ 1` and `k·e ≤ η`. -/
theorem rpow_pow_le {L e η : ℝ} (hL : 1 ≤ L) (k : ℕ) (h : k * e ≤ η) :
    (L ^ e) ^ k ≤ L ^ η := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hL (by linarith [mul_comm e (k : ℝ)])

/-- `M + C ≤ (1 + C)(1 + M)` for `M, C ≥ 0`. -/
theorem add_le_one_add_mul {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) : M + C ≤ (1 + C) * (1 + M) := by
  nlinarith [mul_nonneg hC hM]

open Classical in
/-- **The companion paper's Lemma 7.3** ("If the induction hypothesis (5.1) holds below, then
`𝒬_{ξ_1}(U) ≼ (Σ + M)‖U‖²`"), in the pilot's form: if the child mean squares satisfy the transfer
estimate's hypothesis with constant `M` (`ChildBound`), then for every `ξ₁` and every test function
`U` supported in `[α/2, 2β]` with its first `2m+2` derivatives bounded by `N_U`,
`𝒬_{ξ₁}(U) ≤ K·c_IΣFL·(3𝓗L)^σ·L^η·(1 + M)·N_U²`. The form `𝒬` of `Qform` is the paper's times
`2LF/√3`; the losses `(3𝓗L)^σ` (the separation's `A_min^{−σ}`) and `L^η` (the multiplicity, the
divisor bounds and the number of dyadic blocks) stand in for the paper's `D^{ε}`. -/
theorem third_transfer {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (m : ℕ) {σ η : ℝ} (hσ : 0 < σ)
    (hη : 0 < η) :
    ∃ K3 : ℝ, 0 ≤ K3 ∧ ∀ (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ),
      ContDiff ℝ ∞ U → (∀ x, x < α / 2 ∨ 2 * β < x → U x = 0) → ∀ NU : ℝ,
      (∀ j ≤ 2 * m + 2, ∀ x, ‖iteratedDeriv j U x‖ ≤ NU) →
      ∀ {Hh L S F cI M : ℝ}, 1 ≤ Hh → 1 ≤ L → 1 ≤ F → Hh ≤ S → 3 * β ^ 2 * RΦ ^ 2 ≤ cI →
      1 ≤ cI → 0 ≤ M → ChildBound α β m Hh L S F M →
      Qform ξ1 U β Hh L S F cI ≤
        K3 * (cI * S * F * L) * (3 * Hh * L) ^ σ * L ^ η * (1 + M) * NU ^ 2 := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  set δ := η / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨Kd, hKd0, hKd⟩ := dualQ_sum_le hα hαβ m hσ hδ0
  set Clog := (1 / (δ * Real.log 2) + 1) * (2 * β + 1) ^ δ with hClog
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hClog0 : 0 ≤ Clog := by positivity
  set nξ : ℝ := (Fintype.card (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) : ℝ) with hnξ
  have hk := kappa_pos
  set Kz := (2 * kappa + 5) * (8 / 3 * β) * ‖dualG 0‖ * (2 * (2 * kappa + 5) * Clog) ^ 3 with hKz
  set Kd' := Kd * Clog ^ 2 * (2 * β) ^ (4 * δ) * (1 + Ctriv β) with hKd'
  have hCt := Ctriv_nonneg hβ.le
  have hKz0 : 0 ≤ Kz := by positivity
  have hKd'0 : 0 ≤ Kd' := by positivity
  refine ⟨Kz + nξ * (2 * Kd'), by positivity,
    fun ξ1 U hU hUs NU hNU Hh L S F cI M hH hL hF hHS hcI hcI1 hM0 hM => ?_⟩
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < Hh := by linarith
  have hS1 : 1 ≤ S := hH.trans hHS
  have hS0 : 0 < S := by linarith
  have hF0 : 0 < F := by linarith
  have hcI0 : 0 < cI := by linarith
  have hNU' : ∀ x, ‖U x‖ ≤ NU := fun x => by
    have := hNU 0 (Nat.zero_le _) x; rwa [iteratedDeriv_zero] at this
  have hNU0 : 0 ≤ NU := (norm_nonneg _).trans (hNU' 0)
  have hU2 : ∀ x, 2 * β < x → U x = 0 := fun x hx => hUs x (Or.inr hx)
  have hU0 : primesLe (2 * β * L) ⊆ primesLe (4 * β * L) := primesLe_mono (by nlinarith)
  have hσ1 : 1 ≤ (3 * Hh * L) ^ σ :=
    Real.one_le_rpow (by nlinarith) hσ.le
  have hη1 : 1 ≤ L ^ η := Real.one_le_rpow hL hη.le
  have hP0 : 0 ≤ cI * S * F * L := by positivity
  -- the log factor
  have hlog : ((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) : ℝ) + 1 ≤ Clog * L ^ δ :=
    log_floor_succ_le hδ0 (by positivity : 0 ≤ 2 * β) hL
  have hlog0 : (0 : ℝ) ≤ ((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) : ℝ) + 1 := by positivity
  -- the zero frequencies
  have hA0 : 0 ≤ (cI * S * F * L) * (3 * Hh * L) ^ σ := by positivity
  have hB0 : 0 ≤ (1 + M) * NU ^ 2 := by positivity
  have hzero : ‖∑ t ∈ qTriples (2 * β * L), (wtQ Hh L t : ℂ) * zeroQ U β Hh L S F cI t‖ ≤
      Kz * ((cI * S * F * L) * (3 * Hh * L) ^ σ * L ^ η * (1 + M) * NU ^ 2) := by
    refine (zeroQ_sum_le hNU' hβ.le hH0 hL0 hS0 hF0 hcI0).trans ?_
    have h3 : (2 * (2 * kappa + 5) * (((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) : ℝ) + 1)) ^ 3 ≤
        (2 * (2 * kappa + 5) * Clog) ^ 3 * L ^ η := by
      calc (2 * (2 * kappa + 5) * (((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) : ℝ) + 1)) ^ 3
          ≤ (2 * (2 * kappa + 5) * (Clog * L ^ δ)) ^ 3 := by gcongr
        _ = (2 * (2 * kappa + 5) * Clog) ^ 3 * (L ^ δ) ^ 3 := by ring
        _ ≤ (2 * (2 * kappa + 5) * Clog) ^ 3 * L ^ η := by
            gcongr
            exact rpow_pow_le hL 3 (by rw [hδ]; push_cast; linarith)
    calc (2 * kappa + 5) * (8 / 3 * β) * ‖dualG 0‖ * (cI * S * F * L) * NU ^ 2 *
          (2 * (2 * kappa + 5) * (((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) : ℝ) + 1)) ^ 3
        ≤ (2 * kappa + 5) * (8 / 3 * β) * ‖dualG 0‖ * (cI * S * F * L) * NU ^ 2 *
          ((2 * (2 * kappa + 5) * Clog) ^ 3 * L ^ η) := by gcongr
      _ = Kz * ((cI * S * F * L) * 1 * L ^ η * (1 * NU ^ 2)) := by rw [hKz]; ring
      _ ≤ Kz * ((cI * S * F * L) * (3 * Hh * L) ^ σ * L ^ η * ((1 + M) * NU ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKz0
          refine mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hσ1 hP0) (by positivity)) ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  -- the nonzero frequencies, one character at a time
  have hdual : ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
      ‖∑ t ∈ qTriples (2 * β * L),
        (wtQ Hh L t : ℂ) * dualQ U Hh L S F cI (primesLe (4 * β * L)) ξ t‖ ≤
        Kd' * ((cI * S * F * L) * (3 * Hh * L) ^ σ * L ^ η * (1 + M) * NU ^ 2) := by
    intro ξ
    refine (hKd ξ U hU hUs NU hNU hH hL hF hHS hcI hcI1 hM0 hM).trans ?_
    have hpow : ((2 * β * L) ^ δ) ^ 4 = (2 * β) ^ (4 * δ) * (L ^ δ) ^ 4 := by
      rw [Real.mul_rpow (by positivity) hL0.le, mul_pow, ← Real.rpow_natCast ((2 * β) ^ δ),
        ← Real.rpow_mul (by positivity)]
      congr 2
      push_cast; ring
    have hLL : (L ^ δ) ^ 2 * (L ^ δ) ^ 4 ≤ L ^ η := by
      rw [← pow_add]
      exact rpow_pow_le hL 6 (by rw [hδ]; push_cast; linarith)
    have hMC := add_le_one_add_mul hM0 hCt
    calc ((Nat.log 2 ⌊2 * β * L⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (Kd * (cI * S * F * L) *
          (3 * Hh * L) ^ σ * ((2 * β * L) ^ δ) ^ 4 * (M + Ctriv β) * NU ^ 2)
        ≤ (Clog * L ^ δ) ^ 2 * (Kd * (cI * S * F * L) * (3 * Hh * L) ^ σ *
          ((2 * β) ^ (4 * δ) * (L ^ δ) ^ 4) * ((1 + Ctriv β) * (1 + M)) * NU ^ 2) := by
          rw [hpow]
          gcongr
      _ = Kd' * (((cI * S * F * L) * (3 * Hh * L) ^ σ) * ((L ^ δ) ^ 2 * (L ^ δ) ^ 4) *
          ((1 + M) * NU ^ 2)) := by rw [hKd']; ring
      _ ≤ Kd' * (((cI * S * F * L) * (3 * Hh * L) ^ σ) * L ^ η * ((1 + M) * NU ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLL hA0) hB0) hKd'0
      _ = _ := by ring
  -- the split
  refine (Qform_le_split ξ1 hβ.le hH0 hL0 hS0 hF0 hcI hcI0 hU2 hU0).trans ?_
  calc _ ≤ Kz * ((cI * S * F * L) * (3 * Hh * L) ^ σ * L ^ η * (1 + M) * NU ^ 2) +
        ∑ _ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          2 * (Kd' * ((cI * S * F * L) * (3 * Hh * L) ^ σ * L ^ η * (1 + M) * NU ^ 2)) := by
        refine add_le_add hzero (Finset.sum_le_sum fun ξ _ => ?_)
        exact mul_le_mul (norm_classCoeff_pairH_le ξ1 ξ) (hdual ξ) (norm_nonneg _) (by norm_num)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hnξ]; ring


end Eis

end

#print axioms Eis.norm_mul_conj_le_one
#print axioms Eis.norm_mul_conj_le_one'
#print axioms Eis.norm_wQr_le
#print axioms Eis.norm_wQr_blk_le
#print axioms Eis.rhoQ_blk_mem
#print axioms Eis.AQ_blk_ge
#print axioms Eis.blockQ_bound
#print axioms Eis.nI_rQ_le
#print axioms Eis.nI_fQ_le
#print axioms Eis.four_pow_le_of
#print axioms Eis.mult_le
#print axioms Eis.sum_four_pow_rQ_le
#print axioms Eis.one_div_rpow_neg
#print axioms Eis.blockBoundQ_eq
#print axioms Eis.dualQ_sum_le
#print axioms Eis.mem_qTriples
#print axioms Eis.sum_qTriples_inv_le
#print axioms Eis.zeroQ_sum_le
#print axioms Eis.rpow_pow_le
#print axioms Eis.add_le_one_add_mul
#print axioms Eis.third_transfer
