/-
# Layer II, steps (B′) and (Z): the box sum factorises and saves (round 204)

Plain statements.
* `Z_factor`: the box sum `Σ_{z∈D} |Σ_{y∈B} e(Σ_j α_j z_j y_j)|` over boxes
  `D = ∏[−L_j, L_j]` and `B = ∏[1, L_j]` equals the product over coordinates of the
  one-dimensional sums `Σ_{|z|≤L_j} |Σ_{y=1}^{L_j} e(α_j z y)|`.
* `oneD_bound` (step B′): if `0 < |α|·X ≤ 1/2`, then
  `Σ_{|z|≤X} |Σ_{y=1}^{Y} e(αzy)| ≤ Y + (1/|α|)(1 + log X)`, against the trivial `(2X+1)·Y`.
  No wrap-around occurs (`|αz| ≤ 1/2`), so `‖αz‖ = |αz|` and the geometric bound (A) applies
  term by term.
* `oneD_trivial`: the trivial bound `(2X+1)·Y`.
-/
import ExpSum

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

/-- For `|θ| ≤ 1/2`, the distance to the nearest integer is `|θ|`, or at least `|θ|`. -/
lemma abs_le_dist_round {θ : ℝ} (h : |θ| ≤ 1 / 2) : |θ| ≤ |θ - round θ| := by
  rcases eq_or_ne (round θ) 0 with h0 | h0
  · rw [h0]; simp
  · have h1 : (1 : ℝ) ≤ |((round θ : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
    have := abs_sub_abs_le_abs_sub ((round θ : ℤ) : ℝ) θ
    rw [abs_sub_comm] at this
    linarith

/-- Reindexing `y ∈ [1, L]` as `1 + i`, `i < L`. -/
lemma sum_Icc_one (f : ℤ → ℂ) (L : ℕ) :
    ∑ y ∈ Icc (1 : ℤ) L, f y = ∑ i ∈ range L, f (1 + i) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ← ih]
    have : Icc (1 : ℤ) ((L + 1 : ℕ) : ℤ) = insert ((L : ℤ) + 1) (Icc (1 : ℤ) L) := by
      ext y; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [this, sum_insert (by simp)]
    ring_nf

/-- The inner one-dimensional sum. -/
noncomputable def inner (α : ℝ) (z : ℤ) (L : ℕ) : ℂ := ∑ y ∈ Icc (1 : ℤ) L, ee (α * z * y)

lemma inner_eq (α : ℝ) (z : ℤ) (L : ℕ) :
    inner α z L = ∑ i ∈ range L, ee ((α * z) * ((1 : ℝ) + i)) := by
  unfold inner
  rw [sum_Icc_one]
  apply sum_congr rfl; intro i _; push_cast; ring_nf

lemma norm_inner_neg (α : ℝ) (z : ℤ) (L : ℕ) : ‖inner α (-z) L‖ = ‖inner α z L‖ := by
  have : inner α (-z) L = (starRingEnd ℂ) (inner α z L) := by
    unfold inner; rw [map_sum]
    apply sum_congr rfl; intro y _
    rw [conj_ee]; congr 1; push_cast; ring
  rw [this, Complex.norm_conj]

lemma norm_inner_le (α : ℝ) (z : ℤ) (L : ℕ) : ‖inner α z L‖ ≤ L := by
  rw [inner_eq]; exact geom_trivial _ _ _

/-- Symmetric sums over `[−X, X]`. -/
lemma sum_Icc_symm (f : ℤ → ℝ) (hf : ∀ z, f (-z) = f z) (X : ℕ) :
    ∑ z ∈ Icc (-(X : ℤ)) X, f z = f 0 + 2 * ∑ m ∈ Icc (1 : ℕ) X, f m := by
  induction X with
  | zero => simp
  | succ X ih =>
    have hset : Icc (-((X + 1 : ℕ) : ℤ)) ((X + 1 : ℕ) : ℤ) =
        insert (-((X : ℤ) + 1)) (insert ((X : ℤ) + 1) (Icc (-(X : ℤ)) X)) := by
      ext y; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp; omega), sum_insert (by simp), ih,
      Finset.sum_Icc_succ_top (by omega), hf]
    push_cast; ring

/-- **Step (B′).** No wrap-around: `Σ_{|z|≤X} |inner α z Y| ≤ Y + (1/|α|)(1 + log X)`. -/
theorem oneD_bound (α : ℝ) (hα : α ≠ 0) (X Y : ℕ) (hX : |α| * X ≤ 1 / 2) :
    ∑ z ∈ Icc (-(X : ℤ)) X, ‖inner α z Y‖ ≤ Y + (1 / |α|) * (1 + Real.log X) := by
  have hαp : 0 < |α| := abs_pos.mpr hα
  rw [sum_Icc_symm (fun z => ‖inner α z Y‖) (fun z => norm_inner_neg α z Y)]
  have h0 : ‖inner α 0 Y‖ ≤ Y := norm_inner_le _ _ _
  have hm : ∀ m ∈ Icc (1 : ℕ) X, ‖inner α (m : ℤ) Y‖ ≤ 1 / (2 * |α|) * (1 / (m : ℝ)) := by
    intro m hm
    rw [mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hmX : (m : ℝ) ≤ X := by exact_mod_cast hm.2
    set θ := α * ((m : ℤ) : ℝ)
    have hθ : |θ| = |α| * m := by simp [θ, abs_mul]
    have hθ2 : |θ| ≤ 1 / 2 := by
      rw [hθ]; nlinarith
    have hθpos : 0 < |θ| := by rw [hθ]; positivity
    have hd := abs_le_dist_round hθ2
    have hd0 : θ - round θ ≠ 0 := by
      intro h; rw [h, abs_zero] at hd; linarith
    rw [inner_eq]
    have hg := geom_bound θ 1 Y hd0
    refine hg.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (2 * |α|) * (1 / (m : ℝ)) * (2 * |θ - round θ|) ≥
        1 / (2 * |α|) * (1 / (m : ℝ)) * (2 * (|α| * m)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); rw [← hθ]; linarith
    have e : 1 / (2 * |α|) * (1 / (m : ℝ)) * (2 * (|α| * m)) = 1 := by field_simp
    linarith
  have hsum : ∑ m ∈ Icc (1 : ℕ) X, ‖inner α (m : ℤ) Y‖ ≤
      1 / (2 * |α|) * (1 + Real.log X) := by
    calc ∑ m ∈ Icc (1 : ℕ) X, ‖inner α (m : ℤ) Y‖
        ≤ ∑ m ∈ Icc (1 : ℕ) X, 1 / (2 * |α|) * (1 / (m : ℝ)) := sum_le_sum hm
      _ = 1 / (2 * |α|) * (harmonic X : ℝ) := by
          rw [← Finset.mul_sum, harmonic_eq_sum_Icc]; push_cast
          congr 1; apply sum_congr rfl; intro m _; rw [one_div]
      _ ≤ 1 / (2 * |α|) * (1 + Real.log X) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (by positivity)
  have e2 : 2 * (1 / (2 * |α|) * (1 + Real.log X)) = (1 / |α|) * (1 + Real.log X) := by
    field_simp
  linarith

/-- The trivial one-dimensional bound. -/
lemma oneD_trivial (α : ℝ) (X Y : ℕ) :
    ∑ z ∈ Icc (-(X : ℤ)) X, ‖inner α z Y‖ ≤ (2 * X + 1) * Y := by
  calc ∑ z ∈ Icc (-(X : ℤ)) X, ‖inner α z Y‖ ≤ ∑ _z ∈ Icc (-(X : ℤ)) X, (Y : ℝ) :=
        sum_le_sum fun z _ => norm_inner_le _ _ _
    _ = (2 * X + 1) * Y := by
        rw [sum_const, Int.card_Icc, nsmul_eq_mul]
        congr 1
        rw [show (X : ℤ) + 1 - -(X : ℤ) = ((2 * X + 1 : ℕ) : ℤ) by push_cast; ring,
          Int.toNat_natCast]
        push_cast; ring

/-- **The box sum factorises over coordinates.** -/
theorem Z_factor {K : ℕ} (α : Fin K → ℝ) (L : Fin K → ℕ) :
    ∑ z ∈ Fintype.piFinset (fun j => Icc (-(L j : ℤ)) (L j)),
        ‖∑ y ∈ Fintype.piFinset (fun j => Icc (1 : ℤ) (L j)), T α z y‖ =
      ∏ j, ∑ zj ∈ Icc (-(L j : ℤ)) (L j), ‖inner (α j) zj (L j)‖ := by
  have hin : ∀ z : Fin K → ℤ, ∑ y ∈ Fintype.piFinset (fun j => Icc (1 : ℤ) (L j)), T α z y =
      ∏ j, inner (α j) (z j) (L j) := by
    intro z
    unfold inner
    rw [Finset.prod_univ_sum]
    apply sum_congr rfl; intro y _
    unfold T
    rw [ee_sum]
  simp_rw [hin, norm_prod]
  rw [Finset.prod_univ_sum]

/-- The box side lengths `L_j = ℓ·M^{j+1}`. -/
def Lbox (K M ℓ : ℕ) : Fin K → ℕ := fun j => ℓ * M ^ (j.val + 1)

lemma pv_mem_box {K M ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : Fin ℓ → ℕ)
    (hb : b ∈ Vinogradov.box ℓ M) :
    pv K b ∈ Fintype.piFinset (fun j => Icc (1 : ℤ) (Lbox K M ℓ j)) := by
  rw [Fintype.mem_piFinset]
  intro j
  rw [Vinogradov.box, Fintype.mem_piFinset] at hb
  have hb' : ∀ i, 1 ≤ b i ∧ b i ≤ M := fun i => mem_Icc.mp (hb i)
  rw [mem_Icc, pv, Lbox]
  constructor
  · have : (1 : ℕ) ≤ ∑ i, b i ^ (j.val + 1) := by
      obtain ⟨i0⟩ : Nonempty (Fin ℓ) := ⟨⟨0, by omega⟩⟩
      calc 1 ≤ b i0 ^ (j.val + 1) := Nat.one_le_pow _ _ (by have := (hb' i0).1; omega)
        _ ≤ ∑ i, b i ^ (j.val + 1) :=
            Finset.single_le_sum (f := fun i => b i ^ (j.val + 1)) (fun _ _ => Nat.zero_le _)
              (mem_univ i0)
    exact_mod_cast this
  · have : ∑ i, b i ^ (j.val + 1) ≤ ℓ * M ^ (j.val + 1) := by
      calc ∑ i, b i ^ (j.val + 1) ≤ ∑ _i : Fin ℓ, M ^ (j.val + 1) :=
            sum_le_sum fun i _ => Nat.pow_le_pow_left (hb' i).2 _
        _ = ℓ * M ^ (j.val + 1) := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    exact_mod_cast this

/-- **Per-`n` bilinear bound.** `|Σ_{a,b≤M} e(Σ_j α_j (ab)^{j+1})|^{2ℓ²} ≤ M^{4ℓ(ℓ−1)} J² ∏_j Z_j`,
with `Z_j = Σ_{|z|≤L_j} |Σ_{y=1}^{L_j} e(α_j z y)|` and `L_j = ℓM^{j+1}`. -/
theorem bilinear_bound {K : ℕ} (α : Fin K → ℝ) {M ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖ ^ (2 * ℓ ^ 2) ≤
      (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * (J ℓ K M : ℝ) ^ 2 *
        ∏ j, ∑ zj ∈ Icc (-(Lbox K M ℓ j : ℤ)) (Lbox K M ℓ j), ‖inner (α j) zj (Lbox K M ℓ j)‖ := by
  set L := Lbox K M ℓ
  set Ys := Fintype.piFinset (fun j => Icc (1 : ℤ) (L j))
  set D := Fintype.piFinset (fun j => Icc (-(L j : ℤ)) (L j))
  have hXY : (Vinogradov.box ℓ M).image (pv K) ⊆ Ys := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    exact pv_mem_box hℓ b hb
  apply double_holder α hℓ _ Ys hXY
  intro x hx
  rw [← Z_factor]
  calc ∑ x' ∈ (Vinogradov.box ℓ M).image (pv K), ‖∑ y ∈ Ys, T α (x - x') y‖
      ≤ ∑ z ∈ ((Vinogradov.box ℓ M).image (pv K)).image (fun x' => x - x'),
          ‖∑ y ∈ Ys, T α z y‖ := by
        exact le_of_eq (sum_image (f := fun z => ‖∑ y ∈ Ys, T α z y‖)
          (g := fun x' => x - x') (fun a _ b _ h => sub_right_injective h)).symm
    _ ≤ ∑ z ∈ D, ‖∑ y ∈ Ys, T α z y‖ := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => norm_nonneg _)
        intro z hz
        obtain ⟨x', hx', rfl⟩ := mem_image.mp hz
        have h1 := Fintype.mem_piFinset.mp (hXY hx)
        have h2 := Fintype.mem_piFinset.mp (hXY hx')
        rw [Fintype.mem_piFinset]
        intro j
        have a1 := mem_Icc.mp (h1 j)
        have a2 := mem_Icc.mp (h2 j)
        rw [mem_Icc, Pi.sub_apply]
        constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

end ExpSum
