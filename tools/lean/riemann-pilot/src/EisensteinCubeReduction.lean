import EisensteinCompletedSums

/-! # Lemma 5.3, the cube reduction (round 314)

The rest of S5a in round 312's plan: the companion paper's Lemma 5.3, with its Proposition 5.2 (the
completed mean-square estimate) as a displayed hypothesis.

* **The completed sum through the column sums** (`compT_eq_sum_colSum`):
  `T(X/n³) = Σ_𝔟 ᾱ(𝔟)³Ψ(𝔟)³/N𝔟 · L^{−1/2}·Σ_𝔫 a_ξ(𝔫)(k/𝔫)₆(f/𝔫)₆⁴W(N𝔫/L)` with `L = X/(N𝔟³n³)`, and
  the cube inversion (5.8) as a finite sum (`cube_inversion_sum`).
* **The split** (`colSum_split`) of the cube inversion at `N(𝔥)³ ≤ H_c³`: the short terms keep their
  completed sums; the long ones are expanded into column sums at the scales `X/N(𝔥𝔟)³`.
* **Cauchy–Schwarz over the rows** (`rows_cs`, `rows_short_le`, `rows_long_le`). For the long part the
  paper groups the pairs by `b = hc` and weighs by `τ(b)/N(b)`; here the weight is `1/(N𝔥·N𝔟)` on the
  pairs themselves, whose sum is at most `(Σ_{N𝔞 ≤ βX} 1/N𝔞)²`, the bound the paper gives for its divisor
  sum. The harmonic sum is `O(log X)` by dyadic shells (`sum_idealsLe_inv_le`, in
  `EisensteinMeanSquareDual.lean` since round 332).
* **The long part at one scale** (`inv_mul_rowE_le`): from the hypothesis when `L > 1`, and by counting
  when `L ≤ 1` (`card_rows_le`, `card_T_le`, `card_eltsLe_le`, and round 315's `rowE_le_count` and
  `rowE_eq_zero_of_lt`, in this file since round 332).
* **`CompletedMeanSquare`** (the paper's Proposition 5.2, displayed) and **`cube_reduction`** (the
  paper's Lemma 5.3): the row sum at `X` is at most `K·D^ε·(N²(XF)² + XF·E_sup)` when the row sums at
  the long scales `1 < L ≤ X`, `L·H_c³ < X`, are at most `E_sup·LF`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

section Columns

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K)

/-- For `0 < L ≤ Y`, the column sum at `L` is a sum over the ideals of norm at most `βY` (used at the
long scales `L = X/N(𝔥𝔟)³ ≤ X` with `Y = X`). -/
theorem colSum_eq_sum_gCoef_le {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {Y L : ℝ}
    (hL : 0 < L) (hLY : L ≤ Y) :
    colSum ξ W L 1 k f = ∑ I ∈ idealsLe (β * Y), gCoef ξ k f I * W ((absNorm I : ℝ) / L) := by
  rw [colSum_eq_sum_gCoef ξ k f hW hL]
  by_cases hβ : 0 ≤ β
  · refine Finset.sum_subset (fun I hI => ?_) (fun I _ hI => ?_)
    · rw [mem_idealsLe] at hI ⊢
      exact ⟨hI.1, hI.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left hLY hβ))⟩
    · by_cases hg : gCoef ξ k f I = 0
      · rw [hg, zero_mul]
      have h1 := one_le_absNorm_of_coprime6 (coprime6_of_gCoef ξ k f hg)
      have hgt : β * L < absNorm I := by
        by_contra hle
        exact hI (mem_idealsLe_of h1 (not_lt.1 hle))
      rw [hW _ (by rw [lt_div_iff₀ hL]; linarith), mul_zero]
  · -- `β < 0`: every term vanishes
    have hβ' : β < 0 := not_le.1 hβ
    have hz : ∀ I : Ideal (𝓞 K), gCoef ξ k f I * W ((absNorm I : ℝ) / L) = 0 := fun I => by
      rw [hW _ (by have : (0 : ℝ) ≤ (absNorm I : ℝ) / L := by positivity
                   linarith), mul_zero]
    rw [Finset.sum_eq_zero fun I _ => hz I, Finset.sum_eq_zero fun I _ => hz I]

end Columns

/-! ### Norm bounds and counts -/

theorem norm_moebius_le (H : Ideal (𝓞 K)) : ‖(moebius H : ℂ)‖ ≤ 1 := by
  classical
  unfold moebius
  split_ifs <;> simp

theorem norm_alphaI_le (I : Ideal (𝓞 K)) : ‖alphaI I‖ ≤ 1 := by
  unfold alphaI
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact div_self_le_one _

theorem norm_dCoef_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) (J : Ideal (𝓞 K)) :
    ‖dCoef ξ k f J‖ ≤ 1 := by
  unfold dCoef
  rw [norm_mul, norm_pow, norm_pow, RCLike.norm_conj]
  calc ‖alphaI J‖ ^ 3 * ‖twistPsi ξ k f J‖ ^ 3 ≤ 1 ^ 3 * 1 ^ 3 := by
        gcongr
        · exact norm_alphaI_le J
        · exact norm_twistPsi_le ξ k f J
    _ = 1 := by norm_num

theorem norm_gCoef_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) (I : Ideal (𝓞 K)) :
    ‖gCoef ξ k f I‖ ≤ 1 := by
  rw [gCoef_eq_col, norm_mul, norm_mul, norm_pow]
  calc ‖aXi ξ I‖ * ‖sym6 k I‖ * ‖sym6 f I‖ ^ 4 ≤ 1 * 1 * 1 ^ 4 := by
        gcongr
        · exact norm_aXi_le ξ I
        · exact norm_sym6_le k I
        · exact norm_sym6_le f I
    _ = 1 := by norm_num

/-- At most `49Y` elements of norm at most `Y ≥ 1`: they lie in the box `|a|, |b| ≤ ⌈2√Y⌉`. -/
theorem card_eltsLe_le {Y : ℝ} (hY : 1 ≤ Y) : ((eltsLe Y).card : ℝ) ≤ 49 * Y := by
  classical
  set c : ℤ := ⌈2 * Real.sqrt Y⌉ with hc
  have hs1 : 1 ≤ Real.sqrt Y := Real.one_le_sqrt.2 hY
  have hc0 : 0 ≤ c := Int.ceil_nonneg (by positivity)
  have hcle : (c : ℝ) < 2 * Real.sqrt Y + 1 := Int.ceil_lt_add_one _
  have hcard : (eltsLe Y).card ≤ ((2 * c + 1).toNat) ^ 2 := by
    unfold eltsLe
    refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc, show c + 1 - -c = 2 * c + 1 by ring]
  have hcast : (((2 * c + 1).toNat : ℕ) : ℝ) = 2 * (c : ℝ) + 1 := by
    have : (((2 * c + 1).toNat : ℕ) : ℤ) = 2 * c + 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  calc ((eltsLe Y).card : ℝ) ≤ (((2 * c + 1).toNat : ℕ) : ℝ) ^ 2 := by exact_mod_cast hcard
    _ = (2 * (c : ℝ) + 1) ^ 2 := by rw [hcast]
    _ ≤ (7 * Real.sqrt Y) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
    _ = 49 * Y := by rw [mul_pow, Real.sq_sqrt (by linarith)]; norm_num

/-- **Weighted Cauchy–Schwarz**: `|Σ cᵢwᵢzᵢ|² ≤ (Σ wᵢ)(Σ wᵢ|zᵢ|²)` for `|cᵢ| ≤ 1`, `wᵢ ≥ 0`. -/
theorem norm_sum_sq_le_weighted {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    ‖∑ i ∈ s, c i * (w i : ℂ) * z i‖ ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, c i * (w i : ℂ) * z i‖ ≤
      ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * ‖z i‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i hi), ← mul_assoc,
      Real.mul_self_sqrt (hw i hi)]
    calc ‖c i‖ * w i * ‖z i‖ ≤ 1 * w i * ‖z i‖ := by
          gcongr
          · exact hw i hi
          · exact hc i hi
      _ = w i * ‖z i‖ := by ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * ‖z i‖)
  have e1 : ∑ i ∈ s, Real.sqrt (w i) ^ 2 = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have e2 : ∑ i ∈ s, (Real.sqrt (w i) * ‖z i‖) ^ 2 = ∑ i ∈ s, w i * ‖z i‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [e1, e2] at h2
  calc ‖∑ i ∈ s, c i * (w i : ℂ) * z i‖ ^ 2
      ≤ (∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * ‖z i‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2).trans add_sq_le

section Expand

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K)

/-- **The completed sum through the column sums**: `T(X/n³) = Σ_𝔟 ᾱ(𝔟)³Ψ(𝔟)³/N𝔟 ·
L^{−1/2}·Σ_𝔫 a_ξ(𝔫)(k/𝔫)₆(f/𝔫)₆⁴W(N𝔫/L)` with `L = X/(N𝔟³n³)`. -/
theorem compT_eq_sum_colSum {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ}
    (hX : 0 < X) {nH : ℝ} (hnH : 1 ≤ nH) :
    compT ξ k f W (X / nH ^ 3) = ∑ J ∈ idealsLe (β * X), dCoef ξ k f J / (absNorm J : ℂ) *
      (((Real.sqrt (X / ((absNorm J : ℝ) ^ 3 * nH ^ 3)) : ℝ) : ℂ)⁻¹ *
        colSum ξ W (X / ((absNorm J : ℝ) ^ 3 * nH ^ 3)) 1 k f) := by
  rw [compT_eq_sum ξ k f hW hX hnH, Finset.sum_comm]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hJ1 : (1 : ℝ) ≤ absNorm J := by rw [mem_idealsLe] at hJ; exact_mod_cast hJ.1
  have hd : (0 : ℝ) < (absNorm J : ℝ) ^ 3 * nH ^ 3 := by
    have : (0 : ℝ) < nH := by linarith
    have : (0 : ℝ) < absNorm J := by linarith
    positivity
  set L := X / ((absNorm J : ℝ) ^ 3 * nH ^ 3) with hLdef
  have hL : 0 < L := div_pos hX hd
  have hLX : L ≤ X := by
    rw [hLdef, div_le_iff₀ hd]
    have : (1 : ℝ) ≤ (absNorm J : ℝ) ^ 3 * nH ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hJ1) (one_le_pow₀ hnH)
    nlinarith
  rw [colSum_eq_sum_gCoef_le ξ k f hW hL hLX, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hI1 : (1 : ℝ) ≤ absNorm I := by rw [mem_idealsLe] at hI; exact_mod_cast hI.1
  unfold Vstar
  have e1 : (absNorm I : ℝ) * (absNorm J : ℝ) ^ 3 * nH ^ 3 / X = (absNorm I : ℝ) / L := by
    rw [hLdef]; field_simp
  rw [e1, Real.sqrt_div (by positivity) L]
  have hsI : (0 : ℝ) < Real.sqrt (absNorm I : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsL : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.2 hL
  have hJ0 : (absNorm J : ℂ) ≠ 0 := by
    have : absNorm J ≠ 0 := by
      intro h0; rw [h0] at hJ1; norm_num at hJ1
    exact_mod_cast this
  have hsI' : ((Real.sqrt (absNorm I : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsI.ne'
  have hsL' : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsL.ne'
  push_cast
  field_simp

/-- **The cube inversion as a finite sum** over the ideals of norm at most `βX`. -/
theorem cube_inversion_sum {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ}
    (hX : 0 < X) :
    ((Real.sqrt X : ℝ) : ℂ)⁻¹ * colSum ξ W X 1 k f =
      ∑ H ∈ idealsLe (β * X), (moebius H : ℂ) * dCoef ξ k f H / (absNorm H : ℂ) *
        compT ξ k f W (X / (absNorm H : ℝ) ^ 3) := by
  rw [cube_inversion ξ k f hW hX, tsum_compT_eq_sum ξ k f hW hX]

end Expand

/-! ### The row sums -/

/-- The dual mean square of a finite set of rows at column scale `L`, before its normalisation:
`Σ_{𝔣 ∈ Fs} Σ_{k ∈ T} |Σ_𝔫 a_ξ(𝔫)(k/𝔫)₆(f/𝔫)₆⁴W(N𝔫/L)|²`, `f` the primary generator of `𝔣`. On the
paper's rows it is `LF·E(𝓗, L, F; ξ, W)`. -/
def rowE (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (W : ℝ → ℂ) (L : ℝ)
    (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)) : ℝ :=
  ∑ f ∈ Fs, ∑ k ∈ T, ‖colSum ξ W L 1 k (pgen f)‖ ^ 2

theorem norm_inv_sqrt_mul_sq {L : ℝ} (hL : 0 ≤ L) (c : ℂ) :
    ‖((Real.sqrt L : ℝ) : ℂ)⁻¹ * c‖ ^ 2 = L⁻¹ * ‖c‖ ^ 2 := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    inv_pow, Real.sq_sqrt hL]

theorem norm_sq_eq_mul_inv_sqrt {X : ℝ} (hX : 0 < X) (c : ℂ) :
    ‖c‖ ^ 2 = X * ‖((Real.sqrt X : ℝ) : ℂ)⁻¹ * c‖ ^ 2 := by
  rw [norm_inv_sqrt_mul_sq hX.le, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]

theorem norm_mul_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-! ### The split at `N(𝔥) = H_c` -/

/-- The column scale `L = X/(N𝔟³N𝔥³)` of a pair `(𝔥, 𝔟)`. -/
def pairScale (X : ℝ) (p : Ideal (𝓞 K) × Ideal (𝓞 K)) : ℝ :=
  X / ((absNorm p.2 : ℝ) ^ 3 * (absNorm p.1 : ℝ) ^ 3)

theorem pairScale_nonneg {X : ℝ} (hX : 0 ≤ X) (p : Ideal (𝓞 K) × Ideal (𝓞 K)) :
    0 ≤ pairScale X p := by
  unfold pairScale; positivity

section Split

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K)

/-- **The split of the cube inversion**: the terms `N(𝔥)³ ≤ H_c³` are kept as completed sums, and the
completed sums of the others are expanded into column sums at the scales `L_{𝔥𝔟} = X/N(𝔥𝔟)³`. -/
theorem colSum_split {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ} (hX : 0 < X)
    (Hc3 : ℝ) :
    ((Real.sqrt X : ℝ) : ℂ)⁻¹ * colSum ξ W X 1 k f =
      ∑ H ∈ (idealsLe (β * X)).filter (fun H => (absNorm H : ℝ) ^ 3 ≤ Hc3),
          ((moebius H : ℂ) * dCoef ξ k f H) * ((1 / (absNorm H : ℝ) : ℝ) : ℂ) *
            compT ξ k f W (X / (absNorm H : ℝ) ^ 3) +
      ∑ p ∈ (idealsLe (β * X)).filter (fun H => ¬ (absNorm H : ℝ) ^ 3 ≤ Hc3) ×ˢ idealsLe (β * X),
          ((moebius p.1 : ℂ) * dCoef ξ k f p.1 * dCoef ξ k f p.2) *
            ((1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) : ℝ) : ℂ) *
            (((Real.sqrt (pairScale X p) : ℝ) : ℂ)⁻¹ * colSum ξ W (pairScale X p) 1 k f) := by
  rw [cube_inversion_sum ξ k f hW hX,
    ← Finset.sum_filter_add_sum_filter_not (idealsLe (β * X))
      (fun H => (absNorm H : ℝ) ^ 3 ≤ Hc3)]
  congr 1
  · refine Finset.sum_congr rfl fun H _ => ?_
    push_cast; ring
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun H hH => ?_
    have h1 : (1 : ℝ) ≤ absNorm H := by
      rw [Finset.mem_filter, mem_idealsLe] at hH; exact_mod_cast hH.1.1
    rw [compT_eq_sum_colSum ξ k f hW hX h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    dsimp only [pairScale]
    push_cast; ring

end Split

/-! ### Cauchy–Schwarz over the rows -/

/-- **Weighted Cauchy–Schwarz over the rows**. -/
theorem rows_cs {ι κ₁ κ₂ : Type*} (s : Finset ι) (A : Finset κ₁) (B : Finset κ₂)
    (c z : ι → κ₁ → κ₂ → ℂ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hc : ∀ i ∈ s, ∀ a b, ‖c i a b‖ ≤ 1) :
    ∑ a ∈ A, ∑ b ∈ B, ‖∑ i ∈ s, c i a b * (w i : ℂ) * z i a b‖ ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ∑ a ∈ A, ∑ b ∈ B, ‖z i a b‖ ^ 2 := by
  calc ∑ a ∈ A, ∑ b ∈ B, ‖∑ i ∈ s, c i a b * (w i : ℂ) * z i a b‖ ^ 2
      ≤ ∑ a ∈ A, ∑ b ∈ B, (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i a b‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          norm_sum_sq_le_weighted s (fun i => c i a b) (fun i => z i a b) w hw
            (fun i hi => hc i hi a b)
    _ = (∑ i ∈ s, w i) * ∑ a ∈ A, ∑ b ∈ B, ∑ i ∈ s, w i * ‖z i a b‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ∑ a ∈ A, ∑ b ∈ B, ‖z i a b‖ ^ 2 := by
        congr 1
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

section Rows

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)

/-- **The short part** (the paper's (5.9)): weighted Cauchy–Schwarz in `𝔥`, then a bound `B` for the
completed sums at each `𝔥` and row `𝔣`. -/
theorem rows_short_le {W : ℝ → ℂ} (X : ℝ) (S Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K))
    {B : ℝ} (hB : ∀ H ∈ S, ∀ f ∈ Fs,
      ∑ k ∈ T, ‖compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)‖ ^ 2 ≤ B) :
    ∑ f ∈ Fs, ∑ k ∈ T, ‖∑ H ∈ S, ((moebius H : ℂ) * dCoef ξ k (pgen f) H) *
        ((1 / (absNorm H : ℝ) : ℝ) : ℂ) * compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)‖ ^ 2 ≤
      (∑ H ∈ S, 1 / (absNorm H : ℝ)) ^ 2 * (Fs.card * B) := by
  have h := rows_cs S Fs T (fun H f k => (moebius H : ℂ) * dCoef ξ k (pgen f) H)
    (fun H f k => compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)) (fun H => 1 / (absNorm H : ℝ))
    (fun H _ => by positivity)
    (fun H _ f k => norm_mul_le_one (norm_moebius_le H) (norm_dCoef_le ξ k (pgen f) H))
  refine h.trans ?_
  have hw0 : 0 ≤ ∑ H ∈ S, 1 / (absNorm H : ℝ) := Finset.sum_nonneg fun H _ => by positivity
  have h2 : ∑ H ∈ S, 1 / (absNorm H : ℝ) *
        ∑ f ∈ Fs, ∑ k ∈ T, ‖compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)‖ ^ 2 ≤
      ∑ H ∈ S, 1 / (absNorm H : ℝ) * (Fs.card * B) := by
    refine Finset.sum_le_sum fun H hH => mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ f ∈ Fs, ∑ k ∈ T, ‖compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)‖ ^ 2
        ≤ ∑ _f ∈ Fs, B := Finset.sum_le_sum fun f hf => hB H hH f hf
      _ = Fs.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ H ∈ S, 1 / (absNorm H : ℝ)) * ∑ H ∈ S, 1 / (absNorm H : ℝ) *
        ∑ f ∈ Fs, ∑ k ∈ T, ‖compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)‖ ^ 2
      ≤ (∑ H ∈ S, 1 / (absNorm H : ℝ)) * ∑ H ∈ S, 1 / (absNorm H : ℝ) * (Fs.card * B) :=
        mul_le_mul_of_nonneg_left h2 hw0
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- **The long part**: weighted Cauchy–Schwarz over the pairs `(𝔥, 𝔟)`, then a bound `M` for
`L⁻¹·(the row sum at L)` at each pair's scale. -/
theorem rows_long_le {W : ℝ → ℂ} {X : ℝ} (hX : 0 ≤ X) (P : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)) {M : ℝ}
    (hM : ∀ p ∈ P, (pairScale X p)⁻¹ * rowE ξ W (pairScale X p) Fs T ≤ M) :
    ∑ f ∈ Fs, ∑ k ∈ T, ‖∑ p ∈ P,
        ((moebius p.1 : ℂ) * dCoef ξ k (pgen f) p.1 * dCoef ξ k (pgen f) p.2) *
          ((1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) : ℝ) : ℂ) *
          (((Real.sqrt (pairScale X p) : ℝ) : ℂ)⁻¹ * colSum ξ W (pairScale X p) 1 k (pgen f))‖ ^ 2 ≤
      (∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ))) ^ 2 * M := by
  have h := rows_cs P Fs T
    (fun p f k => (moebius p.1 : ℂ) * dCoef ξ k (pgen f) p.1 * dCoef ξ k (pgen f) p.2)
    (fun p f k => ((Real.sqrt (pairScale X p) : ℝ) : ℂ)⁻¹ * colSum ξ W (pairScale X p) 1 k (pgen f))
    (fun p => 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)))
    (fun p _ => by positivity)
    (fun p _ f k => norm_mul_le_one (norm_mul_le_one (norm_moebius_le _) (norm_dCoef_le _ _ _ _))
      (norm_dCoef_le _ _ _ _))
  refine h.trans ?_
  have hw0 : 0 ≤ ∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) :=
    Finset.sum_nonneg fun p _ => by positivity
  have h2 : ∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) *
        ∑ f ∈ Fs, ∑ k ∈ T,
          ‖((Real.sqrt (pairScale X p) : ℝ) : ℂ)⁻¹ * colSum ξ W (pairScale X p) 1 k (pgen f)‖ ^ 2 ≤
      ∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) * M := by
    refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : ∑ f ∈ Fs, ∑ k ∈ T,
        ‖((Real.sqrt (pairScale X p) : ℝ) : ℂ)⁻¹ * colSum ξ W (pairScale X p) 1 k (pgen f)‖ ^ 2 =
        (pairScale X p)⁻¹ * rowE ξ W (pairScale X p) Fs T := by
      unfold rowE
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => norm_inv_sqrt_mul_sq (pairScale_nonneg hX p) _
    rw [e]; exact hM p hp
  calc (∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ))) *
        ∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) *
          ∑ f ∈ Fs, ∑ k ∈ T,
            ‖((Real.sqrt (pairScale X p) : ℝ) : ℂ)⁻¹ * colSum ξ W (pairScale X p) 1 k (pgen f)‖ ^ 2
      ≤ (∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ))) *
          ∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) * M :=
        mul_le_mul_of_nonneg_left h2 hw0
    _ = _ := by rw [← Finset.sum_mul]; ring

end Rows

/-- At most `2(2κ+5)F` rows of norm in `[F, 2F)`. -/
theorem card_rows_le {F : ℝ} (hF : 1 ≤ F) {Fs : Finset (Ideal (𝓞 K))}
    (hFs : ∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
      (absNorm f : ℝ) < 2 * F) :
    (Fs.card : ℝ) ≤ 2 * (2 * kappa + 5) * F := by
  have hsub : Fs ⊆ idealsLe (2 * F) := fun f hf => by
    obtain ⟨h6, -, -, h2⟩ := hFs f hf
    exact mem_idealsLe_of (one_le_absNorm_of_coprime6 h6) h2.le
  calc (Fs.card : ℝ) ≤ (idealsLe (2 * F)).card := by exact_mod_cast Finset.card_le_card hsub
    _ = idealCount (2 * F) := by rw [card_idealsLe]
    _ ≤ (2 * kappa + 5) * (2 * F) := idealCount_le (by linarith)
    _ = _ := by ring

/-- At most `49𝓗` rows `k` of norm at most `𝓗 ≥ 1`. -/
theorem card_T_le {Hh : ℝ} (hH : 1 ≤ Hh) {T : Finset (𝓞 K)}
    (hT : ∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) : (T.card : ℝ) ≤ 49 * Hh := by
  have hsub : T ⊆ eltsLe Hh := fun k hk => mem_eltsLe.2 (hT k hk).2
  calc (T.card : ℝ) ≤ (eltsLe Hh).card := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ 49 * Hh := card_eltsLe_le hH

theorem rowE_nonneg (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (W : ℝ → ℂ) (L : ℝ)
    (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)) : 0 ≤ rowE ξ W L Fs T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

section Final

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)

/-- A column sum at a scale `X` with `βX < 1` is empty. -/
theorem colSum_eq_zero_of_lt {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ}
    (hX : 0 < X) (h : β * X < 1) (k f : 𝓞 K) : colSum ξ W X 1 k f = 0 := by
  rw [colSum_eq_sum_gCoef ξ k f hW hX]
  refine Finset.sum_eq_zero fun I hI => ?_
  exfalso
  rw [mem_idealsLe] at hI
  have h0 : ⌊β * X⌋₊ = 0 := Nat.floor_eq_zero.2 h
  omega

/-- A column sum at a scale `X` with `βX ≥ 1` has at most `(2κ+5)βX` terms, each at most `N`. -/
theorem norm_colSum_le {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {N : ℝ}
    (hN : ∀ x, ‖W x‖ ≤ N) {X : ℝ} (hX : 0 < X) (h1 : 1 ≤ β * X) (k f : 𝓞 K) :
    ‖colSum ξ W X 1 k f‖ ≤ (2 * kappa + 5) * (β * X) * N := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  rw [colSum_eq_sum_gCoef ξ k f hW hX]
  calc ‖∑ I ∈ idealsLe (β * X), gCoef ξ k f I * W ((absNorm I : ℝ) / X)‖
      ≤ ∑ I ∈ idealsLe (β * X), ‖gCoef ξ k f I * W ((absNorm I : ℝ) / X)‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ idealsLe (β * X), N := Finset.sum_le_sum fun I _ => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_gCoef_le ξ k f I)).trans (hN _)
    _ = (idealsLe (β * X)).card * N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * kappa + 5) * (β * X) * N := by
        rw [card_idealsLe]
        exact mul_le_mul_of_nonneg_right (idealCount_le h1) hN0

/-- **The row sum by counting**: `≤ 98(2κ+5)³(βX)²N²·F·𝓗` for `βX ≥ 1`. -/
theorem rowE_le_count {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {N : ℝ}
    (hN : ∀ x, ‖W x‖ ≤ N) {Hh X F : ℝ} (hH : 1 ≤ Hh) (hF : 1 ≤ F) (hX : 0 < X)
    (h1 : 1 ≤ β * X) {Fs : Finset (Ideal (𝓞 K))} {T : Finset (𝓞 K)}
    (hFs : ∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
      (absNorm f : ℝ) < 2 * F)
    (hT : ∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) :
    rowE ξ W X Fs T ≤ 98 * (2 * kappa + 5) ^ 3 * (β * X) ^ 2 * N ^ 2 * F * Hh := by
  have hk := kappa_pos
  have hrow : rowE ξ W X Fs T ≤ (Fs.card : ℝ) * (T.card * ((2 * kappa + 5) * (β * X) * N) ^ 2) := by
    unfold rowE
    calc ∑ f ∈ Fs, ∑ k ∈ T, ‖colSum ξ W X 1 k (pgen f)‖ ^ 2
        ≤ ∑ _f ∈ Fs, ∑ _k ∈ T, ((2 * kappa + 5) * (β * X) * N) ^ 2 :=
          Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun k _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_colSum_le ξ hW hN hX h1 k (pgen f)) 2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hFc := card_rows_le hF hFs
  have hTc := card_T_le hH hT
  calc rowE ξ W X Fs T ≤ (Fs.card : ℝ) * (T.card * ((2 * kappa + 5) * (β * X) * N) ^ 2) := hrow
    _ ≤ (2 * (2 * kappa + 5) * F) * ((49 * Hh) * ((2 * kappa + 5) * (β * X) * N) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- A row sum at a scale `X` with `βX < 1` vanishes. -/
theorem rowE_eq_zero_of_lt {W : ℝ → ℂ} {β : ℝ} (hW : ∀ x, β < x → W x = 0) {X : ℝ}
    (hX : 0 < X) (h : β * X < 1) (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)) :
    rowE ξ W X Fs T = 0 := by
  unfold rowE
  refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun k _ => ?_
  rw [colSum_eq_zero_of_lt ξ hW hX h k (pgen f), norm_zero]; norm_num

/-- **The long part at one scale**: `L⁻¹·(the row sum at L) ≤ F·(E_sup + 98(2κ+5)³β³N²·XF)` for
`0 < L ≤ X` with `L·H_c³ < X`: from the hypothesis when `L > 1`, and by counting when `L ≤ 1` (the
paper's `E(𝓗, L_b, F) ≪ (𝓗/L_b)‖W‖²_∞`). -/
theorem inv_mul_rowE_le {W : ℝ → ℂ} {β : ℝ} (hβ : 1 ≤ β) (hW : ∀ x, β < x → W x = 0)
    {N : ℝ} (hN : ∀ x, ‖W x‖ ≤ N) {Hh X F : ℝ} (hH : 1 ≤ Hh) (hF : 1 ≤ F)
    (hHXF : Hh ≤ X * F) {Fs : Finset (Ideal (𝓞 K))} {T : Finset (𝓞 K)}
    (hFs : ∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
      (absNorm f : ℝ) < 2 * F)
    (hT : ∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) {Esup : ℝ} (hE : 0 ≤ Esup) {Hc3 : ℝ}
    (hlong : ∀ L : ℝ, 1 < L → L ≤ X → L * Hc3 < X → rowE ξ W L Fs T ≤ Esup * (L * F))
    {L : ℝ} (hL : 0 < L) (hLX : L ≤ X) (hLc : L * Hc3 < X) :
    L⁻¹ * rowE ξ W L Fs T ≤ F * (Esup + 98 * (2 * kappa + 5) ^ 3 * β ^ 3 * N ^ 2 * (X * F)) := by
  have hk := kappa_pos
  have hF0 : 0 < F := by linarith
  have hXF : 0 < X * F := by linarith
  rcases lt_or_ge 1 L with h1 | h1
  · calc L⁻¹ * rowE ξ W L Fs T ≤ L⁻¹ * (Esup * (L * F)) :=
          mul_le_mul_of_nonneg_left (hlong L h1 hLX hLc) (by positivity)
      _ = F * Esup := by field_simp
      _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by positivity :
            (0 : ℝ) ≤ 98 * (2 * kappa + 5) ^ 3 * β ^ 3) (sq_nonneg N)) hXF.le) hF0.le]
  rcases lt_or_ge (β * L) 1 with h2 | h2
  · rw [rowE_eq_zero_of_lt ξ hW hL h2, mul_zero]; positivity
  have hc := rowE_le_count ξ hW hN hH hF hL h2 hFs hT
  calc L⁻¹ * rowE ξ W L Fs T
      ≤ L⁻¹ * (98 * (2 * kappa + 5) ^ 3 * (β * L) ^ 2 * N ^ 2 * F * Hh) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 98 * (2 * kappa + 5) ^ 3 * β ^ 2 * N ^ 2 * F * (L * Hh) := by field_simp
    _ ≤ 98 * (2 * kappa + 5) ^ 3 * β ^ 2 * N ^ 2 * F * (β * (X * F)) := by
        gcongr
        linarith
    _ ≤ _ := by nlinarith [mul_nonneg hF0.le hE]

/-- **The cube reduction with its explicit constants**: with `s₁ = Σ_{N𝔥 ≤ βX} 1/N𝔥`, a bound `B` for
the completed sums at the short `𝔥` (`N𝔥³ ≤ H_c³`) and the hypothesis at the long scales,
`(row sum at X) ≤ 2X·(s₁²·#Fs·B + s₁⁴·F·(E_sup + 98(2κ+5)³β³N²XF))`. -/
theorem rowE_le_explicit {W : ℝ → ℂ} {β : ℝ} (hβ : 1 ≤ β) (hW : ∀ x, β < x → W x = 0)
    {N : ℝ} (hN : ∀ x, ‖W x‖ ≤ N) {Hh X F : ℝ} (hH : 1 ≤ Hh) (hX : 0 < X) (hF : 1 ≤ F)
    (hHXF : Hh ≤ X * F) {Fs : Finset (Ideal (𝓞 K))} {T : Finset (𝓞 K)}
    (hFs : ∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
      (absNorm f : ℝ) < 2 * F)
    (hT : ∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) {Esup : ℝ} (hE : 0 ≤ Esup) {Hc3 : ℝ}
    (hlong : ∀ L : ℝ, 1 < L → L ≤ X → L * Hc3 < X → rowE ξ W L Fs T ≤ Esup * (L * F))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ H ∈ idealsLe (β * X), (absNorm H : ℝ) ^ 3 ≤ Hc3 → ∀ f ∈ Fs,
      ∑ k ∈ T, ‖compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)‖ ^ 2 ≤ B) :
    rowE ξ W X Fs T ≤ 2 * X * ((∑ H ∈ idealsLe (β * X), 1 / (absNorm H : ℝ)) ^ 2 * (Fs.card * B) +
      (∑ H ∈ idealsLe (β * X), 1 / (absNorm H : ℝ)) ^ 4 *
        (F * (Esup + 98 * (2 * kappa + 5) ^ 3 * β ^ 3 * N ^ 2 * (X * F)))) := by
  have hk := kappa_pos
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  set 𝓘 := idealsLe (β * X) with h𝓘
  set S := 𝓘.filter (fun H => (absNorm H : ℝ) ^ 3 ≤ Hc3) with hS
  set P := 𝓘.filter (fun H => ¬ (absNorm H : ℝ) ^ 3 ≤ Hc3) ×ˢ 𝓘 with hP
  set s1 := ∑ H ∈ 𝓘, 1 / (absNorm H : ℝ) with hs1
  set M := F * (Esup + 98 * (2 * kappa + 5) ^ 3 * β ^ 3 * N ^ 2 * (X * F)) with hM
  have hM0 : 0 ≤ M := by positivity
  have hs10 : 0 ≤ s1 := Finset.sum_nonneg fun H _ => by positivity
  set Ps : Ideal (𝓞 K) → 𝓞 K → ℂ := fun f k => ∑ H ∈ S,
    ((moebius H : ℂ) * dCoef ξ k (pgen f) H) * ((1 / (absNorm H : ℝ) : ℝ) : ℂ) *
      compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3) with hPs
  set Pl : Ideal (𝓞 K) → 𝓞 K → ℂ := fun f k => ∑ p ∈ P,
    ((moebius p.1 : ℂ) * dCoef ξ k (pgen f) p.1 * dCoef ξ k (pgen f) p.2) *
      ((1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) : ℝ) : ℂ) *
      (((Real.sqrt (pairScale X p) : ℝ) : ℂ)⁻¹ * colSum ξ W (pairScale X p) 1 k (pgen f)) with hPl
  have hsplit : ∀ f k, ((Real.sqrt X : ℝ) : ℂ)⁻¹ * colSum ξ W X 1 k (pgen f) = Ps f k + Pl f k :=
    fun f k => colSum_split ξ k (pgen f) hW hX Hc3
  -- the short part
  have hshort : ∑ f ∈ Fs, ∑ k ∈ T, ‖Ps f k‖ ^ 2 ≤ s1 ^ 2 * (Fs.card * B) := by
    refine (rows_short_le ξ X S Fs T (fun H hH f hf => hB H (Finset.filter_subset _ _ hH)
      (Finset.mem_filter.1 hH).2 f hf)).trans ?_
    have hSs : ∑ H ∈ S, 1 / (absNorm H : ℝ) ≤ s1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun H _ _ => by positivity
    have hS0 : 0 ≤ ∑ H ∈ S, 1 / (absNorm H : ℝ) := Finset.sum_nonneg fun H _ => by positivity
    gcongr
  -- the long part
  have hlong' : ∀ p ∈ P, (pairScale X p)⁻¹ * rowE ξ W (pairScale X p) Fs T ≤ M := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter] at hp
    obtain ⟨⟨hp1, hp3⟩, hp2⟩ := hp
    have h1 : (1 : ℝ) ≤ absNorm p.1 := by rw [mem_idealsLe] at hp1; exact_mod_cast hp1.1
    have h2 : (1 : ℝ) ≤ absNorm p.2 := by rw [mem_idealsLe] at hp2; exact_mod_cast hp2.1
    have hd1 : (1 : ℝ) ≤ (absNorm p.2 : ℝ) ^ 3 * (absNorm p.1 : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ h2) (one_le_pow₀ h1)
    have hd0 : (0 : ℝ) < (absNorm p.2 : ℝ) ^ 3 * (absNorm p.1 : ℝ) ^ 3 := by linarith
    have hL : 0 < pairScale X p := div_pos hX hd0
    have hLX : pairScale X p ≤ X := div_le_self hX.le hd1
    have hLc : pairScale X p * Hc3 < X := by
      unfold pairScale
      rw [div_mul_eq_mul_div, div_lt_iff₀ hd0]
      have h3 : Hc3 < (absNorm p.1 : ℝ) ^ 3 := not_le.1 hp3
      have h4 : (absNorm p.1 : ℝ) ^ 3 ≤ (absNorm p.2 : ℝ) ^ 3 * (absNorm p.1 : ℝ) ^ 3 := by
        have := one_le_pow₀ (n := 3) h2
        have : (0 : ℝ) ≤ (absNorm p.1 : ℝ) ^ 3 := by positivity
        nlinarith
      nlinarith
    exact inv_mul_rowE_le ξ hβ hW hN hH hF hHXF hFs hT hE hlong hL hLX hLc
  have hlongP : ∑ f ∈ Fs, ∑ k ∈ T, ‖Pl f k‖ ^ 2 ≤ s1 ^ 4 * M := by
    refine (rows_long_le ξ hX.le P Fs T hlong').trans ?_
    have hPs : ∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) ≤ s1 ^ 2 := by
      rw [hP, Finset.sum_product]
      calc ∑ H ∈ 𝓘.filter (fun H => ¬ (absNorm H : ℝ) ^ 3 ≤ Hc3), ∑ J ∈ 𝓘,
            1 / ((absNorm (H, J).1 : ℝ) * (absNorm (H, J).2 : ℝ))
          = (∑ H ∈ 𝓘.filter (fun H => ¬ (absNorm H : ℝ) ^ 3 ≤ Hc3), 1 / (absNorm H : ℝ)) *
              ∑ J ∈ 𝓘, 1 / (absNorm J : ℝ) := by
            rw [Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun J _ => ?_
            rw [one_div_mul_one_div]
        _ ≤ s1 * s1 := by
            refine mul_le_mul_of_nonneg_right ?_ hs10
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun H _ _ => by positivity
        _ = s1 ^ 2 := by ring
    have hP0 : 0 ≤ ∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ)) :=
      Finset.sum_nonneg fun p _ => by positivity
    calc (∑ p ∈ P, 1 / ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ))) ^ 2 * M
        ≤ (s1 ^ 2) ^ 2 * M := by gcongr
      _ = s1 ^ 4 * M := by ring
  -- assemble
  calc rowE ξ W X Fs T = ∑ f ∈ Fs, ∑ k ∈ T, X * ‖Ps f k + Pl f k‖ ^ 2 := by
        unfold rowE
        refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun k _ => ?_
        rw [norm_sq_eq_mul_inv_sqrt hX, hsplit]
    _ ≤ ∑ f ∈ Fs, ∑ k ∈ T, 2 * X * (‖Ps f k‖ ^ 2 + ‖Pl f k‖ ^ 2) := by
        refine Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun k _ => ?_
        have := norm_add_sq_le_two (Ps f k) (Pl f k)
        nlinarith
    _ = 2 * X * (∑ f ∈ Fs, ∑ k ∈ T, ‖Ps f k‖ ^ 2 + ∑ f ∈ Fs, ∑ k ∈ T, ‖Pl f k‖ ^ 2) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * X * (s1 ^ 2 * (Fs.card * B) + s1 ^ 4 * M) := by gcongr

/-- **The completed mean-square estimate** (the companion paper's Proposition 5.2), displayed as a
hypothesis: for every `ε > 0` and `C₀ ≥ 1` there is a derivative order `J` such that, for every
interval `[α, β] ⊂ (0, ∞)`, uniformly in the character `ξ` and the smooth weight `W` supported in
`[α, β]` with its first `J` derivatives bounded by `N`, the scales `1 ≤ 𝓗, X ≤ D^{C₀}` and the
squarefree row `𝔣` of norm prime to `6` and at most `D^{C₀}`, every finite set of nonzero `k` of norm
at most `𝓗` satisfies `Σ_k |T(X; k, f)|² ≤ K·N²·D^ε·(𝓗 + 𝓗²N𝔣/X)`, `f` the primary generator of `𝔣`.
The paper lets the constant depend on `ξ`; there are finitely many `ξ`, so the uniform form is
equivalent. -/
def CompletedMeanSquare : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ J : ℕ, ∀ α β : ℝ, 0 < α → ∃ Kc : ℝ,
    ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ, (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W x‖ ≤ N) →
      ∀ D Hh X : ℝ, 1 ≤ D → 1 ≤ Hh → 1 ≤ X → Hh ≤ D ^ C₀ → X ≤ D ^ C₀ →
      ∀ f : Ideal (𝓞 K), (absNorm f).Coprime 6 → Squarefree f → (absNorm f : ℝ) ≤ D ^ C₀ →
      ∀ T : Finset (𝓞 K), (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) →
        ∑ k ∈ T, ‖compT ξ k (pgen f) W X‖ ^ 2 ≤
          Kc * N ^ 2 * D ^ ε * (Hh + Hh ^ 2 * (absNorm f : ℝ) / X)

end Final

/-- **Lemma 5.3, the cube reduction** (the companion paper's (5.7)), from the completed mean-square
estimate: for every `ε > 0` and `C₀ ≥ 1` there is a derivative order `J` such that, for every interval
`[α, β] ⊂ (0, ∞)`, uniformly in `ξ` and the smooth weight `W` supported in `[α, β]` with its first `J`
derivatives bounded by `N`, the scales `1 ≤ 𝓗, X, F ≤ D^{C₀}` with `𝓗 ≤ XF`, and every finite set of
rows (`𝔣` squarefree of norm prime to `6` in `[F, 2F)`, `0 < N(k) ≤ 𝓗`): if the row sums at the
scales `1 < L ≤ X` with `L·H_c³ < X`, `H_c³ = min(X, X²/𝓗²)`, are at most `E_sup·LF`, then the row
sum at `X` is at most `K·D^ε·(N²(XF)² + XF·E_sup)`. Normalised by `XF`, this is
`E(𝓗, X, F) ≪ D^ε(XF‖W‖² + E_sup)`. The paper's supremum runs over `L_b = X/N(b)³` with
`N(b) > H_c` and `L_b > 1`; the hypothesis here asks for the bound at every real `L` in that range. -/
theorem cube_reduction (hC : CompletedMeanSquare) :
    ∀ ε : ℝ, 0 < ε → ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ J : ℕ, ∀ α β : ℝ, 0 < α → ∃ Kc : ℝ,
    ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ, (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W x‖ ≤ N) →
      ∀ D Hh X F : ℝ, 1 ≤ D → 1 ≤ Hh → 1 ≤ X → 1 ≤ F → Hh ≤ D ^ C₀ → X ≤ D ^ C₀ →
        F ≤ D ^ C₀ → Hh ≤ X * F →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) →
      ∀ Esup : ℝ, 0 ≤ Esup →
        (∀ L : ℝ, 1 < L → L ≤ X → L * min X (X ^ 2 / Hh ^ 2) < X →
          rowE ξ W L Fs T ≤ Esup * (L * F)) →
        rowE ξ W X Fs T ≤ Kc * D ^ ε * (N ^ 2 * (X * F) ^ 2 + X * F * Esup) := by
  intro ε hε C₀ hC₀
  obtain ⟨J, hJ⟩ := hC (ε / 2) (by positivity) C₀ hC₀
  refine ⟨J, fun α β hα => ?_⟩
  obtain ⟨Kc₀, hKc₀⟩ := hJ α β hα
  have hk := kappa_pos
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC₀0 : 0 < C₀ := by linarith
  set β₁ := max β 1 with hβ₁def
  have hβ₁ : 1 ≤ β₁ := le_max_right _ _
  set e := ε / (4 * C₀) with he_def
  have he : 0 < e := by positivity
  set c₁ := 2 * (2 * kappa + 5) * ((1 / (e * Real.log 2) + 1) * (β₁ + 1) ^ e) with hc₁def
  have hc₁ : 0 ≤ c₁ := by positivity
  set K₀ := max Kc₀ 0 with hK₀def
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  refine ⟨12 * (2 * kappa + 5) * c₁ ^ 2 * K₀ * 2 ^ (ε / 2) +
    2 * c₁ ^ 4 * (98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3) + 2 * c₁ ^ 4, ?_⟩
  intro ξ W hWs hWsupp N hN D Hh X F hD hH hX hF hHD hXD hFD hHXF Fs T hFs hT Esup hE hlong
  have hW₁ : ∀ x, β₁ < x → W x = 0 := fun x hx =>
    hWsupp x (Or.inr (lt_of_le_of_lt (le_max_left _ _) hx))
  have hN' : ∀ x, ‖W x‖ ≤ N := fun x => by
    have := hN 0 (Nat.zero_le _) x
    rwa [iteratedDeriv_zero] at this
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN' 0)
  have hX0 : 0 < X := by linarith
  have hF0 : 0 < F := by linarith
  have hH0 : 0 < Hh := by linarith
  have hD0 : 0 ≤ D := by linarith
  set u := D ^ (ε / 4) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hD0 _
  have hu2 : D ^ (ε / 2) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hD0]
    congr 1; push_cast; ring
  have hu4 : D ^ ε = u ^ 4 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hD0]
    congr 1; push_cast; ring
  have h2D : (2 * D) ^ (ε / 2) = 2 ^ (ε / 2) * u ^ 2 := by
    rw [Real.mul_rpow (by norm_num) hD0, hu2]
  have h2e : (0 : ℝ) ≤ 2 ^ (ε / 2) := Real.rpow_nonneg (by norm_num) _
  set B := K₀ * N ^ 2 * (2 ^ (ε / 2) * u ^ 2) * (3 * (X * F)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  -- the completed mean square at the short `𝔥`, applied at `2D`
  have hB : ∀ H ∈ idealsLe (β₁ * X), (absNorm H : ℝ) ^ 3 ≤ min X (X ^ 2 / Hh ^ 2) → ∀ f ∈ Fs,
      ∑ k ∈ T, ‖compT ξ k (pgen f) W (X / (absNorm H : ℝ) ^ 3)‖ ^ 2 ≤ B := by
    intro H hHm hH3 f hf
    obtain ⟨h6, hsq, -, hf2⟩ := hFs f hf
    have hH1 : (1 : ℝ) ≤ absNorm H := by rw [mem_idealsLe] at hHm; exact_mod_cast hHm.1
    have hH3' : (0 : ℝ) < (absNorm H : ℝ) ^ 3 := by positivity
    have hY1 : 1 ≤ X / (absNorm H : ℝ) ^ 3 := by
      rw [le_div_iff₀ hH3']
      have := min_le_left X (X ^ 2 / Hh ^ 2)
      linarith
    have hYX : X / (absNorm H : ℝ) ^ 3 ≤ X := div_le_self hX0.le (one_le_pow₀ hH1)
    have hDC : D ^ C₀ ≤ (2 * D) ^ C₀ := Real.rpow_le_rpow hD0 (by linarith) hC₀0.le
    have h2C : 2 * D ^ C₀ ≤ (2 * D) ^ C₀ := by
      rw [Real.mul_rpow (by norm_num) hD0]
      have h22 : (2 : ℝ) ≤ 2 ^ C₀ := by
        calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ 2 ^ C₀ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hC₀
      have : 0 ≤ D ^ C₀ := Real.rpow_nonneg hD0 _
      nlinarith
    have hcms := hKc₀ ξ W hWs hWsupp N hN (2 * D) Hh (X / (absNorm H : ℝ) ^ 3) (by linarith) hH hY1
      (hHD.trans hDC) ((hYX.trans hXD).trans hDC) f h6 hsq (by linarith) T hT
    refine hcms.trans ?_
    rw [h2D]
    have hc3 : (absNorm H : ℝ) ^ 3 ≤ X ^ 2 / Hh ^ 2 := hH3.trans (min_le_right _ _)
    have h1 : Hh ^ 2 * (absNorm H : ℝ) ^ 3 ≤ X ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hc3; linarith
    have e1 : Hh ^ 2 * (absNorm f : ℝ) / (X / (absNorm H : ℝ) ^ 3) =
        (absNorm f : ℝ) * (Hh ^ 2 * (absNorm H : ℝ) ^ 3) / X := by
      field_simp
    have h2 : (absNorm f : ℝ) * (Hh ^ 2 * (absNorm H : ℝ) ^ 3) / X ≤ 2 * (X * F) := by
      rw [div_le_iff₀ hX0]
      have hfn : (0 : ℝ) ≤ absNorm f := Nat.cast_nonneg _
      calc (absNorm f : ℝ) * (Hh ^ 2 * (absNorm H : ℝ) ^ 3) ≤ (2 * F) * X ^ 2 :=
            mul_le_mul hf2.le h1 (by positivity) (by positivity)
        _ = 2 * (X * F) * X := by ring
    have hq : Hh + Hh ^ 2 * (absNorm f : ℝ) / (X / (absNorm H : ℝ) ^ 3) ≤ 3 * (X * F) := by
      rw [e1]; linarith
    have hq0 : 0 ≤ Hh + Hh ^ 2 * (absNorm f : ℝ) / (X / (absNorm H : ℝ) ^ 3) := by positivity
    calc Kc₀ * N ^ 2 * (2 ^ (ε / 2) * u ^ 2) *
          (Hh + Hh ^ 2 * (absNorm f : ℝ) / (X / (absNorm H : ℝ) ^ 3))
        ≤ K₀ * N ^ 2 * (2 ^ (ε / 2) * u ^ 2) *
          (Hh + Hh ^ 2 * (absNorm f : ℝ) / (X / (absNorm H : ℝ) ^ 3)) := by
          gcongr
          exact le_max_left _ _
      _ ≤ B := by rw [hBdef]; gcongr
  -- the harmonic sum
  have hs1 : ∑ H ∈ idealsLe (β₁ * X), 1 / (absNorm H : ℝ) ≤ c₁ * u := by
    have h1 := sum_idealsLe_inv_le (β₁ * X)
    have h2 := log_floor_succ_le he (by linarith : (0 : ℝ) ≤ β₁) hX
    have h3 : X ^ e ≤ u := by
      calc X ^ e ≤ (D ^ C₀) ^ e := Real.rpow_le_rpow hX0.le hXD he.le
        _ = D ^ (C₀ * e) := (Real.rpow_mul hD0 _ _).symm
        _ = u := by rw [hu]; congr 1; rw [he_def]; field_simp
    have h4 : (0 : ℝ) ≤ (1 / (e * Real.log 2) + 1) * (β₁ + 1) ^ e := by positivity
    calc ∑ H ∈ idealsLe (β₁ * X), 1 / (absNorm H : ℝ)
        ≤ 2 * (2 * kappa + 5) * ((Nat.log 2 ⌊β₁ * X⌋₊ : ℕ) + 1 : ℝ) := h1
      _ ≤ 2 * (2 * kappa + 5) * ((1 / (e * Real.log 2) + 1) * (β₁ + 1) ^ e * X ^ e) := by
          gcongr
      _ ≤ 2 * (2 * kappa + 5) * ((1 / (e * Real.log 2) + 1) * (β₁ + 1) ^ e * u) := by
          gcongr
      _ = c₁ * u := by rw [hc₁def]; ring
  have hs10 : 0 ≤ ∑ H ∈ idealsLe (β₁ * X), 1 / (absNorm H : ℝ) :=
    Finset.sum_nonneg fun H _ => by positivity
  have hcard := card_rows_le hF hFs
  have hexp := rowE_le_explicit ξ hβ₁ hW₁ hN' hH hX0 hF hHXF hFs hT hE hlong hB0 hB
  refine hexp.trans ?_
  rw [hu4]
  have hM0 : 0 ≤ F * (Esup + 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3 * N ^ 2 * (X * F)) := by positivity
  calc 2 * X * ((∑ H ∈ idealsLe (β₁ * X), 1 / (absNorm H : ℝ)) ^ 2 * (Fs.card * B) +
        (∑ H ∈ idealsLe (β₁ * X), 1 / (absNorm H : ℝ)) ^ 4 *
          (F * (Esup + 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3 * N ^ 2 * (X * F))))
      ≤ 2 * X * ((c₁ * u) ^ 2 * ((2 * (2 * kappa + 5) * F) * B) +
        (c₁ * u) ^ 4 * (F * (Esup + 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3 * N ^ 2 * (X * F)))) := by
        gcongr
    _ ≤ (12 * (2 * kappa + 5) * c₁ ^ 2 * K₀ * 2 ^ (ε / 2) +
          2 * c₁ ^ 4 * (98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3) + 2 * c₁ ^ 4) * u ^ 4 *
          (N ^ 2 * (X * F) ^ 2 + X * F * Esup) := by
        rw [hBdef]
        have key : (12 * (2 * kappa + 5) * c₁ ^ 2 * K₀ * 2 ^ (ε / 2) +
            2 * c₁ ^ 4 * (98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3) + 2 * c₁ ^ 4) * u ^ 4 *
            (N ^ 2 * (X * F) ^ 2 + X * F * Esup) -
            2 * X * ((c₁ * u) ^ 2 * ((2 * (2 * kappa + 5) * F) *
              (K₀ * N ^ 2 * (2 ^ (ε / 2) * u ^ 2) * (3 * (X * F)))) +
            (c₁ * u) ^ 4 * (F * (Esup + 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3 * N ^ 2 * (X * F)))) =
            12 * (2 * kappa + 5) * c₁ ^ 2 * K₀ * 2 ^ (ε / 2) * u ^ 4 * (X * F) * Esup +
            2 * c₁ ^ 4 * (98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3) * u ^ 4 * (X * F) * Esup +
            2 * c₁ ^ 4 * u ^ 4 * N ^ 2 * (X * F) ^ 2 := by ring
        have hpos : 0 ≤ 12 * (2 * kappa + 5) * c₁ ^ 2 * K₀ * 2 ^ (ε / 2) * u ^ 4 * (X * F) * Esup +
            2 * c₁ ^ 4 * (98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3) * u ^ 4 * (X * F) * Esup +
            2 * c₁ ^ 4 * u ^ 4 * N ^ 2 * (X * F) ^ 2 := by positivity
        linarith
    _ = _ := by ring

end Eis

end

#print axioms Eis.colSum_eq_sum_gCoef_le
#print axioms Eis.norm_moebius_le
#print axioms Eis.norm_alphaI_le
#print axioms Eis.norm_dCoef_le
#print axioms Eis.norm_gCoef_le
#print axioms Eis.card_eltsLe_le
#print axioms Eis.norm_sum_sq_le_weighted
#print axioms Eis.norm_add_sq_le_two
#print axioms Eis.compT_eq_sum_colSum
#print axioms Eis.cube_inversion_sum
#print axioms Eis.norm_sq_eq_mul_inv_sqrt
#print axioms Eis.norm_mul_le_one
#print axioms Eis.norm_inv_sqrt_mul_sq
#print axioms Eis.pairScale_nonneg
#print axioms Eis.colSum_split
#print axioms Eis.rows_cs
#print axioms Eis.rows_short_le
#print axioms Eis.rows_long_le
#print axioms Eis.card_rows_le
#print axioms Eis.card_T_le
#print axioms Eis.rowE_nonneg
#print axioms Eis.colSum_eq_zero_of_lt
#print axioms Eis.norm_colSum_le
#print axioms Eis.rowE_le_count
#print axioms Eis.rowE_eq_zero_of_lt
#print axioms Eis.inv_mul_rowE_le
#print axioms Eis.rowE_le_explicit
#print axioms Eis.cube_reduction
