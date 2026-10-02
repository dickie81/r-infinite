/-
# Layer II, step (D): the double Hölder bound (round 203)

Plain statement (`double_holder`). For coefficients `α ∈ ℝ^K` and `M, ℓ ≥ 1`, put
`Σ(α) = Σ_{a,b=1}^{M} e(Σ_j α_j a^{j+1} b^{j+1})`. Then
  `|Σ(α)|^{2ℓ²} ≤ M^{4ℓ(ℓ−1)} · J_{ℓ,K}(M)² · Z`
for any `Z` bounding `Σ_{x'∈X} |Σ_{y∈Y} e(α·(x − x')·y)|` for every `x ∈ X` (any `Y ⊇ X`), where `X` is the
set of power-sum vectors of `ℓ`-tuples from `[1, M]`.

This is how Vinogradov's mean value `J` controls an exponential sum. The proof:
* power mean in `a`;
* the `ℓ`-th power of the inner sum is a sum over `ℓ`-tuples;
* power mean over tuples, then Cauchy–Schwarz against the representation counts;
* expanding a square reduces to the box sum `Z`.

Spec: `frontier/expsum/EXPSUM_SPEC.md`, step (D).
-/
import VinoHolder

open Finset Complex

namespace ExpSum

open Vinogradov VinoHolder

variable {K : ℕ}

/-- The bilinear phase `e(Σ_j α_j x_j y_j)`. -/
noncomputable def T (α : Fin K → ℝ) (x y : Fin K → ℤ) : ℂ :=
  ee (∑ j, α j * (x j : ℝ) * (y j : ℝ))

lemma norm_T (α : Fin K → ℝ) (x y : Fin K → ℤ) : ‖T α x y‖ = 1 := norm_ee _

lemma T_comm (α : Fin K → ℝ) (x y : Fin K → ℤ) : T α x y = T α y x := by
  unfold T; congr 1; apply sum_congr rfl; intro j _; ring

lemma T_sum_left {ι : Type*} (α : Fin K → ℝ) (s : Finset ι) (x : ι → Fin K → ℤ)
    (y : Fin K → ℤ) : T α (∑ i ∈ s, x i) y = ∏ i ∈ s, T α (x i) y := by
  unfold T
  rw [← ee_sum]
  congr 1
  simp only [Finset.sum_apply]
  push_cast
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro j _
  rw [Finset.mul_sum, Finset.sum_mul]

lemma T_sub_left (α : Fin K → ℝ) (x x' y : Fin K → ℤ) :
    T α (x - x') y = T α x y * (starRingEnd ℂ) (T α x' y) := by
  unfold T
  rw [conj_ee, ← ee_add]
  congr 1
  simp only [Pi.sub_apply]
  push_cast
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply sum_congr rfl; intro j _; ring

/-- The moment curve point `(a, a², …, a^K)`. -/
def A (K : ℕ) (a : ℕ) : Fin K → ℤ := fun j => (a : ℤ) ^ (j.val + 1)

lemma pv_eq_sum_A {ℓ : ℕ} (b : Fin ℓ → ℕ) : pv K b = ∑ i, A K (b i) := by
  funext j; simp [pv, A, Finset.sum_apply]

/-- `ℓ`-th power of a weighted sum over the moment curve: a sum over `ℓ`-tuples. -/
lemma pow_expand (α : Fin K → ℝ) (M ℓ : ℕ) (c : ℕ → ℂ) (y : Fin K → ℤ) :
    (∑ a ∈ Icc 1 M, c a * T α (A K a) y) ^ ℓ =
      ∑ a ∈ Vinogradov.box ℓ M, (∏ i, c (a i)) * T α (pv K a) y := by
  have h1 : (∑ a ∈ Icc 1 M, c a * T α (A K a) y) ^ ℓ =
      ∏ _i : Fin ℓ, ∑ a ∈ Icc 1 M, c a * T α (A K a) y := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, Finset.prod_univ_sum]
  unfold Vinogradov.box
  apply sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib, pv_eq_sum_A, T_sum_left]

/-- Power mean over a finset: `(Σ r)^ℓ ≤ (#s)^{ℓ−1} Σ r^ℓ` for `r ≥ 0`, `ℓ ≥ 1`. -/
lemma power_mean_fs {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) : (∑ i ∈ s, r i) ^ ℓ ≤ (s.card : ℝ) ^ (ℓ - 1) * ∑ i ∈ s, r i ^ ℓ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp; exact (zero_pow (by omega)).le
  have h := pow_sum_div_card_le_sum_pow (s := s) (f := r) (fun i _ => hr i) (ℓ - 1)
  rw [Nat.sub_add_cancel hℓ] at h
  have hpos : (0 : ℝ) < (s.card : ℝ) ^ (ℓ - 1) := by
    have : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    positivity
  rw [div_le_iff₀ hpos] at h
  linarith [mul_comm ((s.card : ℝ) ^ (ℓ - 1)) (∑ i ∈ s, r i ^ ℓ)]

/-- The squared-norm expansion used in step (4). -/
lemma sum_normSq_le {X Ys : Finset (Fin K → ℤ)} (α : Fin K → ℝ) (μ : (Fin K → ℤ) → ℂ)
    (ν : (Fin K → ℤ) → ℝ) (hμ : ∀ x, ‖μ x‖ ≤ ν x) (Zb : ℝ)
    (hZ : ∀ x ∈ X, ∑ x' ∈ X, ‖∑ y ∈ Ys, T α (x - x') y‖ ≤ Zb) :
    ∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2 ≤ (∑ x ∈ X, ν x ^ 2) * Zb := by
  set W : (Fin K → ℤ) → (Fin K → ℤ) → ℝ := fun x x' => ‖∑ y ∈ Ys, T α (x - x') y‖ with hW
  have hWsym : ∀ x x', W x' x = W x x' := by
    intro x x'
    simp only [hW]
    have : ∀ y, T α (x' - x) y = (starRingEnd ℂ) (T α (x - x') y) := by
      intro y
      rw [T_sub_left, T_sub_left, map_mul, Complex.conj_conj, mul_comm]
    simp_rw [this, ← map_sum, Complex.norm_conj]
  have hν0 : ∀ x, 0 ≤ ν x := fun x => (norm_nonneg _).trans (hμ x)
  have hexp : ((∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ X, ∑ x' ∈ X, μ x * (starRingEnd ℂ) (μ x') * ∑ y ∈ Ys, T α (x - x') y := by
    push_cast
    have e1 : ∀ y, ((‖∑ x ∈ X, μ x * T α x y‖ ^ 2 : ℝ) : ℂ) =
        ∑ x ∈ X, ∑ x' ∈ X, μ x * (starRingEnd ℂ) (μ x') * T α (x - x') y := by
      intro y
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro x' _
      rw [T_sub_left, map_mul]; ring
    simp_rw [← Complex.ofReal_pow, e1]
    rw [Finset.sum_comm]
    apply sum_congr rfl; intro x _
    rw [Finset.sum_comm]
    apply sum_congr rfl; intro x' _
    rw [Finset.mul_sum]
  have hle : ∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2 ≤ ∑ x ∈ X, ∑ x' ∈ X, ν x * ν x' * W x x' := by
    have hnn : 0 ≤ ∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2 := by positivity
    calc ∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2
        = ‖((∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ = ‖∑ x ∈ X, ∑ x' ∈ X, μ x * (starRingEnd ℂ) (μ x') * ∑ y ∈ Ys, T α (x - x') y‖ := by
          rw [hexp]
      _ ≤ ∑ x ∈ X, ∑ x' ∈ X, ‖μ x * (starRingEnd ℂ) (μ x') * ∑ y ∈ Ys, T α (x - x') y‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun x _ => norm_sum_le _ _)
      _ ≤ ∑ x ∈ X, ∑ x' ∈ X, ν x * ν x' * W x x' := by
          apply sum_le_sum; intro x _; apply sum_le_sum; intro x' _
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul (mul_le_mul (hμ x) (hμ x') (norm_nonneg _) (hν0 x)) le_rfl
            (norm_nonneg _) (mul_nonneg (hν0 x) (hν0 x'))
  have hW0 : ∀ x x', 0 ≤ W x x' := fun x x' => norm_nonneg _
  have hamgm : ∑ x ∈ X, ∑ x' ∈ X, ν x * ν x' * W x x' ≤ ∑ x ∈ X, ∑ x' ∈ X, ν x ^ 2 * W x x' := by
    have h1 : ∑ x ∈ X, ∑ x' ∈ X, ν x * ν x' * W x x' ≤
        ∑ x ∈ X, ∑ x' ∈ X, ((ν x ^ 2 + ν x' ^ 2) / 2) * W x x' := by
      apply sum_le_sum; intro x _; apply sum_le_sum; intro x' _
      apply mul_le_mul_of_nonneg_right _ (hW0 x x')
      nlinarith [sq_nonneg (ν x - ν x')]
    have h2 : ∑ x ∈ X, ∑ x' ∈ X, ν x' ^ 2 * W x x' = ∑ x ∈ X, ∑ x' ∈ X, ν x ^ 2 * W x x' := by
      rw [Finset.sum_comm]
      apply sum_congr rfl; intro x _; apply sum_congr rfl; intro x' _
      rw [hWsym]
    have h3 : ∑ x ∈ X, ∑ x' ∈ X, ((ν x ^ 2 + ν x' ^ 2) / 2) * W x x' =
        (∑ x ∈ X, ∑ x' ∈ X, ν x ^ 2 * W x x' + ∑ x ∈ X, ∑ x' ∈ X, ν x' ^ 2 * W x x') / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply sum_congr rfl; intro x _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply sum_congr rfl; intro x' _
      ring
    rw [h3, h2] at h1
    linarith
  calc ∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2 ≤ ∑ x ∈ X, ∑ x' ∈ X, ν x ^ 2 * W x x' :=
        hle.trans hamgm
    _ = ∑ x ∈ X, ν x ^ 2 * ∑ x' ∈ X, W x x' := by
        apply sum_congr rfl; intro x _; rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ X, ν x ^ 2 * Zb := by
        apply sum_le_sum; intro x hx
        exact mul_le_mul_of_nonneg_left (hZ x hx) (sq_nonneg _)
    _ = (∑ x ∈ X, ν x ^ 2) * Zb := by rw [Finset.sum_mul]

set_option maxHeartbeats 1600000 in
/-- **Step (D), double Hölder.** `|Σ(α)|^{2ℓ²} ≤ M^{4ℓ(ℓ−1)} J_{ℓ,K}(M)² Z`. -/
theorem double_holder (α : Fin K → ℝ) {M ℓ : ℕ} (hℓ : 1 ≤ ℓ) (Zb : ℝ)
    (Ys : Finset (Fin K → ℤ)) (hYs : (Vinogradov.box ℓ M).image (pv K) ⊆ Ys)
    (hZ : ∀ x ∈ (Vinogradov.box ℓ M).image (pv K), ∑ x' ∈ (Vinogradov.box ℓ M).image (pv K),
      ‖∑ y ∈ Ys, T α (x - x') y‖ ≤ Zb) :
    ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖ ^ (2 * ℓ ^ 2) ≤
      (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * (J ℓ K M : ℝ) ^ 2 * Zb := by
  classical
  set Bx := Vinogradov.box ℓ M with hBx
  set X := Bx.image (pv K) with hX
  set ν : (Fin K → ℤ) → ℝ := fun y => ((Bx.filter fun b => pv K b = y).card : ℝ) with hν
  have hJ : (J ℓ K M : ℝ) = ∑ y ∈ X, ν y ^ 2 := by
    rw [J_eq_shiftCount, shiftCount_eq_sum]
    push_cast
    simp only [hν, hX, hBx, sq, sub_zero]
    congr!
  have hsumν : ∀ g : (Fin K → ℤ) → ℝ, ∑ b ∈ Bx, g (pv K b) = ∑ y ∈ X, ν y * g y := by
    intro g
    rw [Finset.sum_comp]
    apply sum_congr rfl; intro y _
    rw [nsmul_eq_mul]
  -- the inner sums
  set G : ℕ → ℂ := fun a => ∑ b ∈ Bx, T α (pv K b) (A K a) with hG
  have hG1 : ∀ a, (∑ b ∈ Icc 1 M, T α (A K a) (A K b)) ^ ℓ = G a := by
    intro a
    have := pow_expand α M ℓ (fun _ => (1 : ℂ)) (A K a)
    simp only [Finset.prod_const_one, one_mul] at this
    calc (∑ b ∈ Icc 1 M, T α (A K a) (A K b)) ^ ℓ = (∑ b ∈ Icc 1 M, T α (A K b) (A K a)) ^ ℓ := by
          congr 1; exact sum_congr rfl (fun b _ => T_comm _ _ _)
      _ = G a := this
  set c : ℕ → ℂ := fun a => if G a = 0 then 0 else (starRingEnd ℂ) (G a) / (‖G a‖ : ℂ) with hc
  have hc1 : ∀ a, c a * G a = (‖G a‖ : ℂ) := by
    intro a
    simp only [hc]
    split_ifs with h
    · simp [h]
    · have hn : (‖G a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
      rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
      ring
  have hcn : ∀ a, ‖c a‖ ≤ 1 := by
    intro a
    simp only [hc]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]
  set F : (Fin K → ℤ) → ℂ := fun y => ∑ a ∈ Icc 1 M, c a * T α (A K a) y with hF
  -- step A: dualise
  have hA : ∑ a ∈ Icc 1 M, ‖G a‖ ≤ ∑ b ∈ Bx, ‖F (pv K b)‖ := by
    have hC : ((∑ a ∈ Icc 1 M, ‖G a‖ : ℝ) : ℂ) = ∑ b ∈ Bx, F (pv K b) := by
      push_cast
      calc ∑ a ∈ Icc 1 M, ((‖G a‖ : ℝ) : ℂ) = ∑ a ∈ Icc 1 M, c a * G a :=
            sum_congr rfl (fun a _ => (hc1 a).symm)
        _ = ∑ a ∈ Icc 1 M, ∑ b ∈ Bx, c a * T α (pv K b) (A K a) :=
            sum_congr rfl (fun a _ => Finset.mul_sum _ _ _)
        _ = ∑ b ∈ Bx, ∑ a ∈ Icc 1 M, c a * T α (A K a) (pv K b) := by
            rw [Finset.sum_comm]
            exact sum_congr rfl (fun b _ => sum_congr rfl (fun a _ => by rw [T_comm]))
        _ = ∑ b ∈ Bx, F (pv K b) := rfl
    have hnn : 0 ≤ ∑ a ∈ Icc 1 M, ‖G a‖ := by positivity
    calc ∑ a ∈ Icc 1 M, ‖G a‖ = ‖((∑ a ∈ Icc 1 M, ‖G a‖ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ = ‖∑ b ∈ Bx, F (pv K b)‖ := by rw [hC]
      _ ≤ _ := norm_sum_le _ _
  -- step B: power mean in `a`
  set S0 := ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖ with hS0
  set R := ∑ b ∈ Bx, ‖F (pv K b)‖ with hR
  set Q := ∑ b ∈ Bx, ‖F (pv K b)‖ ^ ℓ with hQ
  have hB : S0 ^ ℓ ≤ (M : ℝ) ^ (ℓ - 1) * R := by
    have h1 : S0 ≤ ∑ a ∈ Icc 1 M, ‖∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖ := norm_sum_le _ _
    have h2 := power_mean_fs (Icc 1 M) (fun a => ‖∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖)
      (fun _ => norm_nonneg _) hℓ
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h2
    have h3 : ∑ a ∈ Icc 1 M, ‖∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖ ^ ℓ =
        ∑ a ∈ Icc 1 M, ‖G a‖ := by
      apply sum_congr rfl; intro a _; rw [← norm_pow, hG1]
    rw [h3] at h2
    calc S0 ^ ℓ ≤ (∑ a ∈ Icc 1 M, ‖∑ b ∈ Icc 1 M, T α (A K a) (A K b)‖) ^ ℓ :=
          pow_le_pow_left₀ (norm_nonneg _) h1 _
      _ ≤ (M : ℝ) ^ (ℓ - 1) * ∑ a ∈ Icc 1 M, ‖G a‖ := h2
      _ ≤ (M : ℝ) ^ (ℓ - 1) * R := mul_le_mul_of_nonneg_left hA (by positivity)
  -- step C: power mean over tuples
  have hCm : R ^ ℓ ≤ ((M : ℝ) ^ ℓ) ^ (ℓ - 1) * Q := by
    have h := power_mean_fs Bx (fun b => ‖F (pv K b)‖) (fun _ => norm_nonneg _) hℓ
    rwa [hBx, card_box, Nat.cast_pow] at h
  -- step D: Cauchy–Schwarz against ν
  have hQ2 : Q ^ 2 ≤ (∑ y ∈ X, ν y ^ 2) * ∑ y ∈ X, (‖F y‖ ^ ℓ) ^ 2 := by
    rw [hQ, hsumν (fun y => ‖F y‖ ^ ℓ)]
    exact sum_mul_sq_le_sq_mul_sq X ν (fun y => ‖F y‖ ^ ℓ)
  -- step E: the square expansion
  set μ : (Fin K → ℤ) → ℂ := fun x => ∑ a ∈ Bx.filter (fun a => pv K a = x), ∏ i, c (a i) with hμ
  have hμν : ∀ x, ‖μ x‖ ≤ ν x := by
    intro x
    calc ‖μ x‖ ≤ ∑ a ∈ Bx.filter (fun a => pv K a = x), ‖∏ i, c (a i)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ Bx.filter (fun a => pv K a = x), (1 : ℝ) := by
          apply sum_le_sum; intro a _
          rw [norm_prod]
          exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hcn _)
      _ = ν x := by rw [sum_const, nsmul_one]
  have hFpow : ∀ y, F y ^ ℓ = ∑ x ∈ X, μ x * T α x y := by
    intro y
    rw [hF, pow_expand]
    rw [← Finset.sum_fiberwise_of_maps_to (g := pv K) (t := X)
      (fun a ha => mem_image_of_mem _ ha)]
    apply sum_congr rfl; intro x _
    rw [hμ, Finset.sum_mul]
    apply sum_congr rfl; intro a ha
    rw [(mem_filter.mp ha).2]
  have hE : ∑ y ∈ X, (‖F y‖ ^ ℓ) ^ 2 ≤ (∑ y ∈ X, ν y ^ 2) * Zb := by
    have h := sum_normSq_le (X := X) (Ys := Ys) α μ ν hμν Zb hZ
    calc ∑ y ∈ X, (‖F y‖ ^ ℓ) ^ 2 ≤ ∑ y ∈ Ys, (‖F y‖ ^ ℓ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hYs (fun _ _ _ => sq_nonneg _)
      _ = ∑ y ∈ Ys, ‖∑ x ∈ X, μ x * T α x y‖ ^ 2 := by
          apply sum_congr rfl; intro y _; rw [← norm_pow, hFpow]
      _ ≤ _ := h
  -- combine
  have hJ0 : 0 ≤ ∑ y ∈ X, ν y ^ 2 := Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun b _ => pow_nonneg (norm_nonneg _) _)
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun b _ => norm_nonneg _)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  rw [hJ]
  calc S0 ^ (2 * ℓ ^ 2) = (S0 ^ ℓ) ^ (2 * ℓ) := by rw [← pow_mul]; ring_nf
    _ ≤ ((M : ℝ) ^ (ℓ - 1) * R) ^ (2 * ℓ) := pow_le_pow_left₀ (by positivity) hB _
    _ = ((M : ℝ) ^ (ℓ - 1)) ^ (2 * ℓ) * (R ^ ℓ) ^ 2 := by
        rw [mul_pow, ← pow_mul R]; ring_nf
    _ ≤ ((M : ℝ) ^ (ℓ - 1)) ^ (2 * ℓ) * (((M : ℝ) ^ ℓ) ^ (ℓ - 1) * Q) ^ 2 := by
        gcongr
    _ = (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * Q ^ 2 := by
        simp only [mul_pow, ← pow_mul]
        rw [← mul_assoc, ← pow_add]
        congr 2; ring
    _ ≤ (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) *
          ((∑ y ∈ X, ν y ^ 2) * ((∑ y ∈ X, ν y ^ 2) * Zb)) := by
        gcongr
        exact hQ2.trans (mul_le_mul_of_nonneg_left hE hJ0)
    _ = (M : ℝ) ^ (4 * ℓ * (ℓ - 1)) * (∑ y ∈ X, ν y ^ 2) ^ 2 * Zb := by ring

/-! ## Step (A): the geometric sum -/

lemma norm_ee_sub_one (θ : ℝ) : ‖ee θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * θ)
  rw [show (2 * Real.pi * θ) / 2 = Real.pi * θ by ring, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two] at h
  rw [← h, ee]
  congr 2
  push_cast; ring

/-- Jordan: `|sin(πθ)| ≥ 2‖θ‖`, where `‖θ‖ = |θ − round θ|`. -/
lemma abs_sin_ge (θ : ℝ) : 2 * |θ - round θ| ≤ |Real.sin (Real.pi * θ)| := by
  set d := θ - round θ with hd
  have hsin : |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * |d|)| := by
    have e : Real.pi * θ = Real.pi * d + (round θ : ℤ) * Real.pi := by rw [hd]; ring
    rw [e, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
    rcases le_or_gt 0 d with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, Real.sin_neg, abs_neg]
  rw [hsin]
  have hd2 : |d| ≤ 1 / 2 := abs_sub_round θ
  have h0 : 0 ≤ Real.pi * |d| := by positivity
  have h1 : Real.pi * |d| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hj := Real.mul_le_sin h0 h1
  have hs0 : 0 ≤ Real.sin (Real.pi * |d|) := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  rw [abs_of_nonneg hs0]
  calc 2 * |d| = 2 / Real.pi * (Real.pi * |d|) := by field_simp
    _ ≤ _ := hj

lemma ee_nat_mul (θ : ℝ) (n : ℕ) : ee (θ * n) = ee θ ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih => rw [Nat.cast_succ, mul_add, mul_one, ee_add, ih, pow_succ]

/-- **Step (A).** `|Σ_{i<Y} e(θ(u+i))| ≤ 1/(2‖θ‖)` when `θ` is not an integer. -/
theorem geom_bound (θ u : ℝ) (Y : ℕ) (hd : θ - round θ ≠ 0) :
    ‖∑ i ∈ range Y, ee (θ * (u + i))‖ ≤ 1 / (2 * |θ - round θ|) := by
  have hdpos : 0 < |θ - round θ| := abs_pos.mpr hd
  have hsin := abs_sin_ge θ
  have hne : ee θ - 1 ≠ 0 := by
    intro h
    have := norm_ee_sub_one θ
    rw [h, norm_zero] at this
    linarith
  have hsum : ∑ i ∈ range Y, ee (θ * (u + i)) = ee (θ * u) * ((ee θ ^ Y - 1) / (ee θ - 1)) := by
    rw [← geom_sum_eq (sub_ne_zero.mp hne), Finset.mul_sum]
    apply sum_congr rfl; intro i _
    rw [← ee_nat_mul, ← ee_add]; congr 1; ring
  rw [hsum, norm_mul, norm_ee, one_mul, norm_div, norm_ee_sub_one]
  have hnum : ‖ee θ ^ Y - 1‖ ≤ 2 := by
    calc ‖ee θ ^ Y - 1‖ ≤ ‖ee θ ^ Y‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ee, one_pow, norm_one]; norm_num
  have hden : 0 < 2 * |Real.sin (Real.pi * θ)| := by linarith
  rw [div_le_div_iff₀ hden (by positivity)]
  nlinarith

/-- The trivial bound. -/
lemma geom_trivial (θ u : ℝ) (Y : ℕ) : ‖∑ i ∈ range Y, ee (θ * (u + i))‖ ≤ Y := by
  calc ‖∑ i ∈ range Y, ee (θ * (u + i))‖ ≤ ∑ i ∈ range Y, ‖ee (θ * (u + i))‖ := norm_sum_le _ _
    _ = Y := by simp [norm_ee]

end ExpSum
