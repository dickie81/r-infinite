import EisensteinThetaRows

/-! # One transformed term in mean square (round 341)

S5d of round 312's plan, part 3 (continued): the bookkeeping in the companion paper's proof of its Lemma 6.6, from
one transformed term to its mean square over the rows, with the quadratic large sieve displayed (round 340).

* **The coefficients**: the factors at `j_P ≢ 4` bounded by `w_P` (`wB`, `norm_coefRest_le`), the factors at
  `j_P ≡ 4` taken out (`dualCoef_eq`), and each piece of the reindexing with coefficient at most `a₀`, scale
  `Y′ ≤ Y` and `a′²Y′ ≤ a₀²Y/N(Q)` (`piece_coef_le`, `piece_scale_le`, `piece_cost_le`).
* **The cost identity** (`cost_eq`): `(∏_{j_P ≢ 4} w_P)²N(𝒜)²/N(Q) = ∏_{P∈𝒜} N(P)^{c(j_P)}`, `c = 1` at
  `j ≡ 0, 4` and `2` otherwise: the paper's local updates of `(a², Y)`.
* **`dualTerm_meanSquare`**: `Σ_k |dualTerm(k)|² ≤ K·16^{|𝒜|}K_d²N_w²·H₀^σ max(1, Y)^{2σ}·
  (H₀ + N(c₀)²(H₀²/X)∏_{P∈𝒜} N(P)^{c(j_P)})`, by Cauchy–Schwarz over the units and the pieces and
  `prepSum_meanSquare` (round 340) on each piece.
* **The cost of the active primes** (`cost_le`): `∏_{P∈𝒜} N(P)^{c(j_P)} ≤ N(t)²N(g)` for `t` squarefree and
  `𝒜` admissible: the paper's `a²Y ≪ (𝓗₀²/X)N(t)²N(g)`.
-/

open Complex MeasureTheory Set NumberField Ideal UniqueFactorizationMonoid
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section

namespace Eis

/-- Cauchy–Schwarz over a finite index set. -/
theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖f i‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq

/-- `ℤ[ω]` has (at most) six units. -/
theorem card_units_le : Fintype.card (𝓞 K)ˣ ≤ 6 := by
  classical
  have h : (Finset.univ : Finset (𝓞 K)ˣ) ⊆
      ([1, -1, ωu, -ωu, ωu ^ 2, -ωu ^ 2] : List (𝓞 K)ˣ).toFinset := fun u _ =>
    List.mem_toFinset.2 (units_mem u)
  calc Fintype.card (𝓞 K)ˣ = (Finset.univ : Finset (𝓞 K)ˣ).card := Finset.card_univ.symm
    _ ≤ _ := Finset.card_le_card h
    _ ≤ _ := List.toFinset_card_le _

/-- The weight bounding `B_{P,j}` for `j ≢ 4`: `N(P)^{−1/2}` at `j ≡ 0`, else `1`. -/
def wB (P : Pr) (j : ℕ) : ℝ := if j % 6 = 0 then (Real.sqrt (absNorm P.1))⁻¹ else 1

theorem wB_nonneg (P : Pr) (j : ℕ) : 0 ≤ wB P j := by
  unfold wB; split_ifs
  · exact inv_nonneg.2 (Real.sqrt_nonneg _)
  · exact zero_le_one

theorem wB_le_one (P : Pr) (j : ℕ) : wB P j ≤ 1 := by
  unfold wB; split_ifs
  · exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast one_le_absNorm_Pr P))
  · exact le_rfl

theorem norm_Bloc_le_wB (P : Pr) {j : ℕ} (h4 : j % 6 ≠ 4) (x : 𝓞 K) : ‖Bloc P.1 j x‖ ≤ wB P j := by
  unfold wB
  split_ifs with h0
  · exact norm_Bloc_zero_le h0 x
  · exact norm_Bloc_le_one h4 h0 x

/-- The coefficient of a transformed term with the factors at `j_P ≡ 4` taken out. -/
def coefRest (d : DualIdx → ℂ) (A : Finset Pr) (j : Pr → ℕ) (u : (𝓞 K)ˣ) (m : ℕ)
    (n b : Ideal (𝓞 K)) : ℂ :=
  (((3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) : ℝ) : ℂ) * d (u, m, n, b) *
    ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), Bloc P.1 (j P) (dualPt (u, m, n, b))

theorem dualCoef_eq {d : DualIdx → ℂ}
    (hds : ∀ q : DualIdx, d q ≠ 0 →
      Squarefree q.2.2.1 ∧ (absNorm q.2.2.1).Coprime 3 ∧ (absNorm q.2.2.2).Coprime 3)
    (A : Finset Pr) (j : Pr → ℕ) (u : (𝓞 K)ˣ) (m : ℕ) (n b : Ideal (𝓞 K)) :
    dualCoef d A j u m n b =
      coefRest d A j u m n b * ∏ P ∈ A.filter (fun P => j P % 6 = 4), B4 P n b := by
  unfold dualCoef coefRest
  by_cases h0 : d (u, m, n, b) = 0
  · rw [h0]; ring
  obtain ⟨-, hn, hb⟩ := hds _ h0
  rw [← Finset.prod_filter_mul_prod_filter_not A (fun P => j P % 6 = 4),
    Finset.prod_congr rfl fun P hP => Bloc_dualPt_four P (Finset.mem_filter.1 hP).2
      (q := (u, m, n, b)) hn hb]
  ring

theorem norm_coefRest_le {d : DualIdx → ℂ} {Kd : ℝ} (hKd : 0 ≤ Kd)
    (hd : ∀ q : DualIdx, ‖d q‖ ≤ Kd * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2))
    (A : Finset Pr) (j : Pr → ℕ) (u : (𝓞 K)ˣ) (m : ℕ) (n b : Ideal (𝓞 K)) :
    ‖coefRest d A j u m n b‖ ≤
      Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) := by
  unfold coefRest
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hPB : ‖∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), Bloc P.1 (j P) (dualPt (u, m, n, b))‖ ≤
      ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P hP =>
      norm_Bloc_le_wB P (Finset.mem_filter.1 hP).2 _
  have hP0 : 0 ≤ ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) :=
    Finset.prod_nonneg fun P _ => wB_nonneg P _
  have h3 : 0 ≤ Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) := mul_nonneg hKd (Real.rpow_nonneg (by norm_num) _)
  rcases (Real.sqrt_nonneg (absNorm b : ℝ)).eq_or_lt with hb | hb
  · rw [← hb, div_zero, abs_zero, zero_mul, zero_mul]; exact mul_nonneg h3 hP0
  · have hpos : 0 ≤ (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) hb.le
    rw [abs_of_nonneg hpos]
    have hdq := hd (u, m, n, b)
    have hR0 : 0 ≤ Kd * (3 : ℝ) ^ ((m : ℝ) / 6) * Real.sqrt (absNorm b) :=
      mul_nonneg (mul_nonneg hKd (Real.rpow_nonneg (by norm_num) _)) hb.le
    have e1 : (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) * (3 : ℝ) ^ ((m : ℝ) / 6) = (3 : ℝ) ^ (-(4 : ℝ) / 3) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    calc (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) * ‖d (u, m, n, b)‖ *
          ‖∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), Bloc P.1 (j P) (dualPt (u, m, n, b))‖
        ≤ (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) *
            (Kd * (3 : ℝ) ^ ((m : ℝ) / 6) * Real.sqrt (absNorm b)) *
            ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdq hpos) hPB (norm_nonneg _) (mul_nonneg hpos hR0)
      _ = Kd * ((3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) * (3 : ℝ) ^ ((m : ℝ) / 6)) *
            (Real.sqrt (absNorm b) / Real.sqrt (absNorm b)) *
            ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) := by ring
      _ = _ := by rw [e1, div_self hb.ne', mul_one]

theorem coefRest_support {d : DualIdx → ℂ}
    (hds : ∀ q : DualIdx, d q ≠ 0 →
      Squarefree q.2.2.1 ∧ (absNorm q.2.2.1).Coprime 3 ∧ (absNorm q.2.2.2).Coprime 3)
    {A : Finset Pr} {j : Pr → ℕ} {u : (𝓞 K)ˣ} {m : ℕ} {n b : Ideal (𝓞 K)}
    (h : coefRest d A j u m n b ≠ 0) :
    Squarefree n ∧ (absNorm n).Coprime 3 ∧ (absNorm b).Coprime 3 := by
  have h0 : d (u, m, n, b) ≠ 0 := by
    intro h0; apply h; unfold coefRest; rw [h0]; ring
  exact hds _ h0

/-- **One piece, bounded**: for `a′ ≤ a₀`, `a′²Y′ ≤ B` and `0 < Y′ ≤ Y`,
`a′²(H₀^{1+σ}Y′^{2σ} + H₀^σY′^{1+2σ}) ≤ H₀^σ max(1, Y)^{2σ}(a₀²H₀ + B)`. -/
theorem piece_bound {σ a' a₀ Y' Y B H₀ : ℝ} (hσ : 0 < σ) (ha' : 0 ≤ a') (haa : a' ≤ a₀)
    (hB : a' ^ 2 * Y' ≤ B) (hY' : 0 < Y') (hYY : Y' ≤ Y) (hH : 1 ≤ H₀) :
    a' ^ 2 * (H₀ ^ (1 + σ) * Y' ^ (2 * σ) + H₀ ^ σ * Y' ^ (1 + 2 * σ)) ≤
      H₀ ^ σ * max 1 Y ^ (2 * σ) * (a₀ ^ 2 * H₀ + B) := by
  have hH0 : 0 < H₀ := by linarith
  have hYm : Y' ^ (2 * σ) ≤ max 1 Y ^ (2 * σ) :=
    Real.rpow_le_rpow hY'.le (hYY.trans (le_max_right _ _)) (by linarith)
  have hYm0 : 0 ≤ Y' ^ (2 * σ) := Real.rpow_nonneg hY'.le _
  have hHs : 0 ≤ H₀ ^ σ := Real.rpow_nonneg hH0.le _
  have e1 : H₀ ^ (1 + σ) = H₀ * H₀ ^ σ := by
    rw [Real.rpow_add hH0, Real.rpow_one]
  have e2 : Y' ^ (1 + 2 * σ) = Y' * Y' ^ (2 * σ) := by
    rw [Real.rpow_add hY', Real.rpow_one]
  have ha2 : a' ^ 2 ≤ a₀ ^ 2 := pow_le_pow_left₀ ha' haa 2
  have hB0 : 0 ≤ B := le_trans (mul_nonneg (sq_nonneg _) hY'.le) hB
  rw [e1, e2]
  have hmax0 : 0 ≤ max 1 Y ^ (2 * σ) := Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  calc a' ^ 2 * (H₀ * H₀ ^ σ * Y' ^ (2 * σ) + H₀ ^ σ * (Y' * Y' ^ (2 * σ)))
      = a' ^ 2 * H₀ * (H₀ ^ σ * Y' ^ (2 * σ)) + (a' ^ 2 * Y') * (H₀ ^ σ * Y' ^ (2 * σ)) := by ring
    _ ≤ a₀ ^ 2 * H₀ * (H₀ ^ σ * max 1 Y ^ (2 * σ)) + B * (H₀ ^ σ * max 1 Y ^ (2 * σ)) := by
        gcongr
    _ = _ := by ring

theorem nI_eq_absNorm (A : Finset Pr) : nI A = (absNorm (idl A) : ℝ) := rfl

/-- The coefficient bound of a piece is at most `a₀`. -/
theorem piece_coef_le {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (Q T T₁ : Finset Pr) :
    a₀ * (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
        (Real.sqrt (absNorm (idl (T \ T₁))))⁻¹ ≤ a₀ := by
  have h1 : ∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => inv_nonneg.2 (Real.sqrt_nonneg _)) fun P _ =>
      inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast one_le_absNorm_Pr P))
  have h2 : (Real.sqrt (absNorm (idl (T \ T₁)) : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (one_le_nI _))
  have h10 : 0 ≤ ∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹ :=
    Finset.prod_nonneg fun _ _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  calc a₀ * (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
        (Real.sqrt (absNorm (idl (T \ T₁))))⁻¹ ≤ a₀ * 1 * 1 := by
        gcongr
    _ = a₀ := by ring

theorem piece_coef_nonneg {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (Q T T₁ : Finset Pr) :
    0 ≤ a₀ * (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
        (Real.sqrt (absNorm (idl (T \ T₁))))⁻¹ :=
  mul_nonneg (mul_nonneg ha₀ (Finset.prod_nonneg fun _ _ => inv_nonneg.2 (Real.sqrt_nonneg _)))
    (inv_nonneg.2 (Real.sqrt_nonneg _))

theorem piece_scale_pos {Y : ℝ} (hY : 0 < Y) (T T₁ : Finset Pr) :
    0 < Y / ((absNorm (idl T₁) : ℝ) * (absNorm (idl (T \ T₁)) : ℝ) ^ 3) :=
  div_pos hY (mul_pos (lt_of_lt_of_le one_pos (one_le_nI _))
    (pow_pos (lt_of_lt_of_le one_pos (one_le_nI _)) 3))

theorem piece_scale_le {Y : ℝ} (hY : 0 < Y) (T T₁ : Finset Pr) :
    Y / ((absNorm (idl T₁) : ℝ) * (absNorm (idl (T \ T₁)) : ℝ) ^ 3) ≤ Y := by
  have h1 : 1 ≤ (absNorm (idl T₁) : ℝ) := one_le_nI _
  have h2 : 1 ≤ (absNorm (idl (T \ T₁)) : ℝ) := one_le_nI _
  exact div_le_self hY.le (one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ h2))

/-- **The cost of the active primes at `j_P ≡ 4`**: `a′²Y′ ≤ a₀²Y/N(Q)` for every piece. -/
theorem piece_cost_le {a₀ Y : ℝ} (hY : 0 < Y) {Q T T₁ : Finset Pr} (hT : T ⊆ Q) (hT₁ : T₁ ⊆ T) :
    (a₀ * (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
        (Real.sqrt (absNorm (idl (T \ T₁))))⁻¹) ^ 2 *
      (Y / ((absNorm (idl T₁) : ℝ) * (absNorm (idl (T \ T₁)) : ℝ) ^ 3)) ≤ a₀ ^ 2 * Y / nI Q := by
  set p : ℝ := ∏ P ∈ Q \ T, (absNorm P.1 : ℝ) with hp
  set x₁ : ℝ := (absNorm (idl T₁) : ℝ) with hx₁
  set x₂ : ℝ := (absNorm (idl (T \ T₁)) : ℝ) with hx₂
  have hp1 : 1 ≤ p := by rw [hp, ← nI_eq_prod]; exact one_le_nI _
  have h1 : 1 ≤ x₁ := one_le_nI _
  have h2 : 1 ≤ x₂ := one_le_nI _
  have hpsq : (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) ^ 2 = p⁻¹ := by
    rw [← Finset.prod_pow, hp, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hx2sq : (Real.sqrt x₂)⁻¹ ^ 2 = x₂⁻¹ := by rw [inv_pow, Real.sq_sqrt (by linarith)]
  have hnQ : nI Q = p * (x₂ * x₁) := by
    rw [nI_eq_prod, hp, hx₁, hx₂, ← Finset.prod_sdiff hT, ← Finset.prod_sdiff hT₁, absNorm_idl,
      absNorm_idl, Nat.cast_prod, Nat.cast_prod]
  rw [hnQ, mul_pow, mul_pow, hpsq, hx2sq]
  have hp0 : 0 < p := by linarith
  have hx10 : 0 < x₁ := by linarith
  have hx20 : 0 < x₂ := by linarith
  have hx23 : 1 ≤ x₂ ^ 3 := one_le_pow₀ h2
  have hp' : p ≠ 0 := hp0.ne'
  have hx1' : x₁ ≠ 0 := hx10.ne'
  have hx2' : x₂ ≠ 0 := hx20.ne'
  have hc0 : 0 ≤ a₀ ^ 2 * Y / (p * (x₂ * x₁)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) hY.le) (mul_pos hp0 (mul_pos hx20 hx10)).le
  calc a₀ ^ 2 * p⁻¹ * x₂⁻¹ * (Y / (x₁ * x₂ ^ 3))
      = a₀ ^ 2 * Y / (p * (x₂ * x₁)) * (x₂ ^ 3)⁻¹ := by field_simp
    _ ≤ a₀ ^ 2 * Y / (p * (x₂ * x₁)) * 1 :=
        mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hx23) hc0
    _ = a₀ ^ 2 * Y / (p * (x₂ * x₁)) := mul_one _

/-- The cost exponent of an active prime in `a²Y`: `1` at `j ≡ 0, 4`, else `2`. -/
def jCost (j : ℕ) : ℕ := if j % 6 = 0 ∨ j % 6 = 4 then 1 else 2

theorem wB_sq_mul (P : Pr) {j : ℕ} (h4 : ¬ j % 6 = 4) :
    wB P j ^ 2 * (absNorm P.1 : ℝ) ^ 2 = (absNorm P.1 : ℝ) ^ jCost j := by
  have hN : 0 < (absNorm P.1 : ℝ) := absNorm_Pr_pos P
  unfold wB jCost
  by_cases h0 : j % 6 = 0
  · rw [ite_eq_left h0, ite_eq_left (Or.inl h0), inv_pow, Real.sq_sqrt hN.le, pow_one]
    field_simp
  · rw [ite_eq_right h0, ite_eq_right (by tauto)]; ring

/-- **The cost identity**: `(∏_{j_P ≢ 4} w_P)² N(𝒜)² / N(Q) = ∏_{P∈𝒜} N(P)^{c(j_P)}` with `Q` the
primes at `j_P ≡ 4` and `c = 1` at `j ≡ 0, 4`, `2` otherwise. -/
theorem cost_eq (A : Finset Pr) (j : Pr → ℕ) :
    (∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P)) ^ 2 * nI A ^ 2 /
        nI (A.filter fun P => j P % 6 = 4) =
      ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P) := by
  have hA : nI A = nI (A.filter fun P => j P % 6 = 4) * nI (A.filter fun P => ¬ j P % 6 = 4) := by
    rw [← nI_union (Finset.disjoint_filter_filter_not A A _), Finset.filter_union_filter_not_eq]
  rw [hA, ← Finset.prod_filter_mul_prod_filter_not A (fun P => j P % 6 = 4)]
  have hQ : ∏ P ∈ A.filter (fun P => j P % 6 = 4), (absNorm P.1 : ℝ) ^ jCost (j P) =
      nI (A.filter fun P => j P % 6 = 4) := by
    rw [nI_eq_prod]
    refine Finset.prod_congr rfl fun P hP => ?_
    have h4 : j P % 6 = 4 := (Finset.mem_filter.1 hP).2
    unfold jCost; rw [ite_eq_left (Or.inr h4), pow_one]
  have hR : ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), (absNorm P.1 : ℝ) ^ jCost (j P) =
      (∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P)) ^ 2 *
        nI (A.filter fun P => ¬ j P % 6 = 4) ^ 2 := by
    rw [nI_eq_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun P hP => (wB_sq_mul P (Finset.mem_filter.1 hP).2).symm
  rw [hQ, hR]
  have : 0 < nI (A.filter fun P => j P % 6 = 4) := nI_pos _
  field_simp

/-- The index set of the pieces of one transformed term: the units, and `T₁ ⊆ T ⊆ Q`. -/
def pieces (Q : Finset Pr) : Finset ((𝓞 K)ˣ × (Σ _ : Finset Pr, Finset Pr)) :=
  Finset.univ ×ˢ Q.powerset.sigma fun T => T.powerset

theorem card_pieces_le (Q : Finset Pr) : ((pieces Q).card : ℝ) ≤ 6 * 4 ^ Q.card := by
  unfold pieces
  rw [Finset.card_product, Finset.card_sigma]
  have h1 : (Finset.univ : Finset (𝓞 K)ˣ).card ≤ 6 := by rw [Finset.card_univ]; exact card_units_le
  have h2 : ∑ T ∈ Q.powerset, T.powerset.card ≤ 4 ^ Q.card := by
    calc ∑ T ∈ Q.powerset, T.powerset.card ≤ ∑ _T ∈ Q.powerset, 2 ^ Q.card :=
          Finset.sum_le_sum fun T hT => by
            rw [Finset.card_powerset]
            exact Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card (Finset.mem_powerset.1 hT))
      _ = 2 ^ Q.card * 2 ^ Q.card := by rw [Finset.sum_const, Finset.card_powerset, smul_eq_mul]
      _ = 4 ^ Q.card := by rw [← mul_pow]; norm_num
  have : (Finset.univ : Finset (𝓞 K)ˣ).card * ∑ T ∈ Q.powerset, T.powerset.card ≤ 6 * 4 ^ Q.card :=
    Nat.mul_le_mul h1 h2
  exact_mod_cast this

/-- The scalar bookkeeping: `a₀² ≤ K_d²` and `a₀²Y/N(Q) ≤ K_d² N(c₀)²(H₀²/X)∏_{P∈𝒜} N(P)^{c(j_P)}`
for `a₀ = K_d 3^{−4/3} ∏_{j_P ≢ 4} w_P` and `Y = N(c₀)²N(𝒜)²H₀²/X`. -/
theorem a0_sq_le {Kd : ℝ} (hKd : 0 ≤ Kd) (A : Finset Pr) (j : Pr → ℕ) :
    (Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P)) ^ 2 ≤
      Kd ^ 2 := by
  have hW0 : 0 ≤ ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) :=
    Finset.prod_nonneg fun P _ => wB_nonneg P _
  have hW1 : ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) ≤ 1 :=
    Finset.prod_le_one₀ (fun P _ => wB_nonneg P _) fun P _ => wB_le_one P _
  have h30 : 0 ≤ (3 : ℝ) ^ (-(4 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  have h31 : (3 : ℝ) ^ (-(4 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg hKd h30) hW0) ?_ 2
  calc Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P)
      ≤ Kd * 1 * 1 := by gcongr
    _ = Kd := by ring

theorem a0_cost_le (Kd : ℝ) (c₀ : 𝓞 K) (A : Finset Pr) (j : Pr → ℕ) {H₀ X : ℝ}
    (hX : 0 < X) :
    (Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P)) ^ 2 *
        dualY c₀ A H₀ X / nI (A.filter fun P => j P % 6 = 4) ≤
      Kd ^ 2 * ((absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
        ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P)) := by
  have hc := cost_eq A j
  have hnQ : 0 < nI (A.filter fun P => j P % 6 = 4) := nI_pos _
  have h3 : ((3 : ℝ) ^ (-(4 : ℝ) / 3)) ^ 2 ≤ 1 :=
    pow_le_one₀ (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num))
  have hP0 : 0 ≤ ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P) :=
    Finset.prod_nonneg fun P _ => pow_nonneg (Nat.cast_nonneg _) _
  have hR0 : 0 ≤ (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) :=
    mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hX.le)
  unfold dualY
  calc (Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P)) ^ 2 *
        ((absNorm (span {c₀}) : ℝ) ^ 2 * nI A ^ 2 * H₀ ^ 2 / X) / nI (A.filter fun P => j P % 6 = 4)
      = Kd ^ 2 * ((3 : ℝ) ^ (-(4 : ℝ) / 3)) ^ 2 * ((absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X)) *
          ((∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P)) ^ 2 * nI A ^ 2 /
            nI (A.filter fun P => j P % 6 = 4)) := by
        field_simp
    _ = Kd ^ 2 * ((3 : ℝ) ^ (-(4 : ℝ) / 3)) ^ 2 * ((absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X)) *
          ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P) := by rw [hc]
    _ ≤ Kd ^ 2 * 1 * ((absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X)) *
          ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 (sq_nonneg _)) hR0) hP0
    _ = _ := by ring

/-- The piece `x = (u, T, T₁)` of a transformed term at the row `k`:
`Σ_m (uλ^m/k)₆³(𝔯₁𝔯₂/k)₆³ 𝒮_{m−4}[reCoef, Y/(N𝔯₁N𝔯₂³)](k)`. -/
def pieceSum (h : ℝ → ℂ) (d : DualIdx → ℂ) (A : Finset Pr) (j : Pr → ℕ) (Q : Finset Pr) (Y H₀ : ℝ)
    (x : (𝓞 K)ˣ × (Σ _ : Finset Pr, Finset Pr)) (k : 𝓞 K) : ℂ :=
  ∑' m : ℕ, (dualPhase x.1 m k * sym6 (pgen (idl x.2.2) * pgen (idl (x.2.1 \ x.2.2))) (span {k}) ^ 3) *
    prepSum h (Y / ((absNorm (idl x.2.2) : ℝ) * (absNorm (idl (x.2.1 \ x.2.2)) : ℝ) ^ 3)) H₀
      ((m : ℤ) - 4) (reCoef (coefRest d A j x.1 m) Q x.2.1 x.2.2) k

theorem mem_pieces {Q : Finset Pr} {x : (𝓞 K)ˣ × (Σ _ : Finset Pr, Finset Pr)} (hx : x ∈ pieces Q) :
    x.2.1 ⊆ Q ∧ x.2.2 ⊆ x.2.1 := by
  unfold pieces at hx
  rw [Finset.mem_product, Finset.mem_sigma, Finset.mem_powerset, Finset.mem_powerset] at hx
  exact hx.2

/-- **One transformed term in mean square** (the companion paper's proof of its Lemma 6.6, from the
transformed term to the bound, at one index): for the rows `k` (primary, squarefree, norm prime to `6`,
`N(k) ≤ H₀`) and one class of data `(d, c₀, 𝒜, j)`,
`Σ_k |dualTerm(k)|² ≤ K·16^{|𝒜|}K_d²N_w²·H₀^σ max(1, Y)^{2σ}·(H₀ + N(c₀)²(H₀²/X)∏_{P∈𝒜} N(P)^{c(j_P)})`
with `Y = N(c₀)²N(𝒜)²H₀²/X`, given the quadratic large sieve (displayed). -/
theorem dualTerm_meanSquare (hLS : QuadLargeSieve) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → ∀ Nw : ℝ,
      (∀ i ≤ 2, ∀ w, ‖iteratedDeriv i h w‖ ≤ Nw * (1 + Real.exp w) ^ (-(1 : ℝ))) →
      ∀ (d : DualIdx → ℂ) (Kd : ℝ), 0 ≤ Kd →
      (∀ q : DualIdx, d q ≠ 0 →
        Squarefree q.2.2.1 ∧ (absNorm q.2.2.1).Coprime 3 ∧ (absNorm q.2.2.2).Coprime 3) →
      (∀ q : DualIdx, ‖d q‖ ≤ Kd * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2)) →
      ∀ c₀ : 𝓞 K, c₀ ≠ 0 → ∀ (A : Finset Pr) (j : Pr → ℕ) (H₀ X : ℝ), 1 ≤ H₀ → 0 < X →
      ∀ Ks : Finset (𝓞 K), (∀ k ∈ Ks, Primary k ∧ Squarefree (span {k}) ∧
        (absNorm (span {k})).Coprime 6 ∧ (absNorm (span {k}) : ℝ) ≤ H₀) →
      ∑ k ∈ Ks, ‖dualTerm h d c₀ A j k X‖ ^ 2 ≤
        Kc * (16 : ℝ) ^ A.card * Kd ^ 2 * Nw ^ 2 * (H₀ ^ σ * max 1 (dualY c₀ A H₀ X) ^ (2 * σ)) *
          (H₀ + (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
            ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P)) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := prepSum_meanSquare hLS hσ (A := 1) (by linarith)
  refine ⟨36 * K₀, by positivity, ?_⟩
  intro h hhs Nw hNw d Kd hKd hds hd c₀ hc₀ A j H₀ X hH hX Ks hKs
  have hH0 : 0 < H₀ := by linarith
  have hh0 : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-(1 : ℝ)) := fun w => by
    simpa using hNw 0 (Nat.zero_le _) w
  have hNw0 : 0 ≤ Nw := by
    have := (norm_nonneg _).trans (hh0 0)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hc : 0 < (absNorm (span {c₀}) : ℝ) := by
    have : absNorm (span {c₀}) ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc₀
    exact_mod_cast Nat.pos_of_ne_zero this
  have hY : 0 < dualY c₀ A H₀ X := by
    unfold dualY
    exact div_pos (mul_pos (mul_pos (pow_pos hc 2) (pow_pos (nI_pos A) 2)) (pow_pos hH0 2)) hX
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset Pr, Q = A.filter fun P => j P % 6 = 4 := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ,
      a₀ = Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A.filter (fun P => ¬ j P % 6 = 4), wB P (j P) :=
    ⟨_, rfl⟩
  have ha₀0 : 0 ≤ a₀ := by
    rw [ha₀]
    exact mul_nonneg (mul_nonneg hKd (Real.rpow_nonneg (by norm_num) _))
      (Finset.prod_nonneg fun P _ => wB_nonneg P _)
  have hA₀ : ∀ u m, ∀ n b, ‖coefRest d A j u m n b‖ ≤ a₀ := fun u m n b => by
    rw [ha₀]; exact norm_coefRest_le hKd hd A j u m n b
  have hA₀3 : ∀ u m, ∀ n b, coefRest d A j u m n b ≠ 0 →
      (absNorm n).Coprime 3 ∧ (absNorm b).Coprime 3 := fun u m n b hne =>
    ⟨(coefRest_support hds hne).2.1, (coefRest_support hds hne).2.2⟩
  have hA₀s : ∀ u m, ∀ n b, coefRest d A j u m n b ≠ 0 → Squarefree n ∧ (absNorm n).Coprime 3 :=
    fun u m n b hne => ⟨(coefRest_support hds hne).1, (coefRest_support hds hne).2.1⟩
  -- each piece in mean square
  have hpiece : ∀ x ∈ pieces Q,
      (∀ k ∈ Ks, Summable fun m : ℕ =>
        (dualPhase x.1 m k * sym6 (pgen (idl x.2.2) * pgen (idl (x.2.1 \ x.2.2))) (span {k}) ^ 3) *
          prepSum h (dualY c₀ A H₀ X /
              ((absNorm (idl x.2.2) : ℝ) * (absNorm (idl (x.2.1 \ x.2.2)) : ℝ) ^ 3)) H₀
            ((m : ℤ) - 4) (reCoef (coefRest d A j x.1 m) Q x.2.1 x.2.2) k) ∧
      ∑ k ∈ Ks, ‖pieceSum h d A j Q (dualY c₀ A H₀ X) H₀ x k‖ ^ 2 ≤
        K₀ * (a₀ * (∏ P ∈ Q \ x.2.1, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
            (Real.sqrt (absNorm (idl (x.2.1 \ x.2.2))))⁻¹) ^ 2 * Nw ^ 2 *
          (H₀ ^ (1 + σ) * (dualY c₀ A H₀ X /
              ((absNorm (idl x.2.2) : ℝ) * (absNorm (idl (x.2.1 \ x.2.2)) : ℝ) ^ 3)) ^ (2 * σ) +
            H₀ ^ σ * (dualY c₀ A H₀ X /
              ((absNorm (idl x.2.2) : ℝ) * (absNorm (idl (x.2.1 \ x.2.2)) : ℝ) ^ 3)) ^ (1 + 2 * σ)) := by
    intro x hx
    obtain ⟨-, hT₁⟩ := mem_pieces hx
    have hc1 : ∀ (m : ℕ) (k : 𝓞 K), ‖dualPhase x.1 m k *
        sym6 (pgen (idl x.2.2) * pgen (idl (x.2.1 \ x.2.2))) (span {k}) ^ 3‖ ≤ 1 := fun m k => by
      rw [norm_mul, norm_pow]
      calc _ ≤ 1 * 1 := mul_le_mul (norm_dualPhase_le _ _ _)
            (pow_le_one₀ (norm_nonneg _) (norm_sym6_le _ _)) (pow_nonneg (norm_nonneg _) _) zero_le_one
        _ = 1 := one_mul 1
    have := hK₀ h hhs Nw hNw _ H₀ (piece_scale_pos hY x.2.1 x.2.2) hH
      (fun m => reCoef (coefRest d A j x.1 m) Q x.2.1 x.2.2)
      (a₀ * (∏ P ∈ Q \ x.2.1, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
        (Real.sqrt (absNorm (idl (x.2.1 \ x.2.2))))⁻¹)
      (fun m n b => norm_reCoef_le (hA₀ x.1 m) hT₁ n b)
      (fun m n b hne => reCoef_support (hA₀s x.1 m) hne) Ks hKs
      (fun m k => dualPhase x.1 m k *
        sym6 (pgen (idl x.2.2) * pgen (idl (x.2.1 \ x.2.2))) (span {k}) ^ 3) hc1
    exact ⟨this.1, this.2⟩
  -- the representation through the pieces
  have hrep : ∀ k ∈ Ks, dualTerm h d c₀ A j k X =
      ∑ x ∈ pieces Q, pieceSum h d A j Q (dualY c₀ A H₀ X) H₀ x k := by
    intro k hk
    obtain ⟨-, hsq, h6, -⟩ := hKs k hk
    have hkpos := absNorm_pos_of_coprime6 h6
    rw [(dualTerm_eq_sum hNw0 hh0 hKd hd hc₀ A j h6 hsq hH0 hX).2]
    unfold pieces
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hexp : ∀ m : ℕ, dualPhase u m k *
        prepSum h (dualY c₀ A H₀ X) H₀ ((m : ℤ) - 4) (dualCoef d A j u m) k =
        ∑ σ ∈ Q.powerset.sigma (fun T => T.powerset),
          (dualPhase u m k * sym6 (pgen (idl σ.2) * pgen (idl (σ.1 \ σ.2))) (span {k}) ^ 3) *
            prepSum h (dualY c₀ A H₀ X /
                ((absNorm (idl σ.2) : ℝ) * (absNorm (idl (σ.1 \ σ.2)) : ℝ) ^ 3)) H₀
              ((m : ℤ) - 4) (reCoef (coefRest d A j u m) Q σ.1 σ.2) k := by
      intro m
      have hcoef : dualCoef d A j u m = fun n b => coefRest d A j u m n b * ∏ P ∈ Q, B4 P n b := by
        funext n b; rw [hQ]; exact dualCoef_eq hds A j u m n b
      rw [hcoef, prepSum_B4 hNw0 (by norm_num : (1 / 2 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1)
        hh0 hY hH0 _ (hA₀ u m) (hA₀3 u m) hkpos Q, Finset.sum_sigma, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T₁ _ => ?_
      dsimp only
      ring
    rw [tsum_congr hexp, Summable.tsum_finsetSum fun σ hσ =>
      (hpiece (u, σ) (Finset.mem_product.2 ⟨Finset.mem_univ _, hσ⟩)).1 k hk]
    rfl
  -- each piece, bounded through the scales
  have hM0 : 0 ≤ H₀ ^ σ * max 1 (dualY c₀ A H₀ X) ^ (2 * σ) :=
    mul_nonneg (Real.rpow_nonneg hH0.le _)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hB0 : 0 ≤ a₀ ^ 2 * H₀ + a₀ ^ 2 * dualY c₀ A H₀ X / nI Q :=
    add_nonneg (mul_nonneg (sq_nonneg _) hH0.le)
      (div_nonneg (mul_nonneg (sq_nonneg _) hY.le) (nI_pos Q).le)
  have hbound : ∀ x ∈ pieces Q, ∑ k ∈ Ks, ‖pieceSum h d A j Q (dualY c₀ A H₀ X) H₀ x k‖ ^ 2 ≤
      K₀ * Nw ^ 2 * (H₀ ^ σ * max 1 (dualY c₀ A H₀ X) ^ (2 * σ) *
        (a₀ ^ 2 * H₀ + a₀ ^ 2 * dualY c₀ A H₀ X / nI Q)) := by
    intro x hx
    obtain ⟨hT, hT₁⟩ := mem_pieces hx
    have hpb := piece_bound hσ (piece_coef_nonneg ha₀0 Q x.2.1 x.2.2)
      (piece_coef_le ha₀0 Q x.2.1 x.2.2) (piece_cost_le hY hT hT₁) (piece_scale_pos hY x.2.1 x.2.2)
      (piece_scale_le hY x.2.1 x.2.2) hH
    exact (hpiece x hx).2.trans (Eq.trans_le (by ring)
      (mul_le_mul_of_nonneg_left hpb (mul_nonneg hK₀0 (sq_nonneg Nw))))
  -- the scalars
  have hQA : Q.card ≤ A.card := by rw [hQ]; exact Finset.card_filter_le _ _
  have h6 : ((6 : ℝ) * 4 ^ Q.card) ^ 2 ≤ 36 * 16 ^ A.card := by
    rw [mul_pow, ← pow_mul, mul_comm Q.card 2, pow_mul]
    norm_num
    exact pow_le_pow_right₀ (by norm_num) hQA
  have hB : a₀ ^ 2 * H₀ + a₀ ^ 2 * dualY c₀ A H₀ X / nI Q ≤
      Kd ^ 2 * (H₀ + (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
        ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P)) := by
    have h1 : a₀ ^ 2 ≤ Kd ^ 2 := by rw [ha₀]; exact a0_sq_le hKd A j
    have h2 : a₀ ^ 2 * dualY c₀ A H₀ X / nI Q ≤ Kd ^ 2 * ((absNorm (span {c₀}) : ℝ) ^ 2 *
        (H₀ ^ 2 / X) * ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P)) := by
      rw [ha₀, hQ]; exact a0_cost_le Kd c₀ A j hX
    calc a₀ ^ 2 * H₀ + a₀ ^ 2 * dualY c₀ A H₀ X / nI Q
        ≤ Kd ^ 2 * H₀ + Kd ^ 2 * ((absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
            ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P)) :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hH0.le) h2
      _ = _ := by ring
  have hcard : (0 : ℝ) ≤ (pieces Q).card := Nat.cast_nonneg _
  calc ∑ k ∈ Ks, ‖dualTerm h d c₀ A j k X‖ ^ 2
      ≤ ∑ k ∈ Ks, ((pieces Q).card : ℝ) *
          ∑ x ∈ pieces Q, ‖pieceSum h d A j Q (dualY c₀ A H₀ X) H₀ x k‖ ^ 2 :=
        Finset.sum_le_sum fun k hk => by rw [hrep k hk]; exact norm_sum_sq_le_card _ _
    _ = ((pieces Q).card : ℝ) *
          ∑ x ∈ pieces Q, ∑ k ∈ Ks, ‖pieceSum h d A j Q (dualY c₀ A H₀ X) H₀ x k‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((pieces Q).card : ℝ) * ∑ _x ∈ pieces Q, K₀ * Nw ^ 2 *
          (H₀ ^ σ * max 1 (dualY c₀ A H₀ X) ^ (2 * σ) *
            (a₀ ^ 2 * H₀ + a₀ ^ 2 * dualY c₀ A H₀ X / nI Q)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound) hcard
    _ = ((pieces Q).card : ℝ) ^ 2 * (K₀ * Nw ^ 2 *
          (H₀ ^ σ * max 1 (dualY c₀ A H₀ X) ^ (2 * σ) *
            (a₀ ^ 2 * H₀ + a₀ ^ 2 * dualY c₀ A H₀ X / nI Q))) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (36 * 16 ^ A.card) * (K₀ * Nw ^ 2 *
          (H₀ ^ σ * max 1 (dualY c₀ A H₀ X) ^ (2 * σ) *
            (Kd ^ 2 * (H₀ + (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
              ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P))))) := by
        refine mul_le_mul ((pow_le_pow_left₀ hcard (card_pieces_le Q) 2).trans h6)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hM0)
            (mul_nonneg hK₀0 (sq_nonneg _)))
          (mul_nonneg (mul_nonneg hK₀0 (sq_nonneg _)) (mul_nonneg hM0 hB0)) (by positivity)
    _ = _ := by ring

/-- `∏_{P∈𝒜} N(P)^{v_P(I)}` divides `N(I)`. -/
theorem prod_pow_count_dvd (A : Finset Pr) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (∏ P ∈ A, absNorm P.1 ^ (normalizedFactors I).count P.1) ∣ absNorm I := by
  classical
  have hI' : absNorm I = ∏ Q ∈ (normalizedFactors I).toFinset,
      absNorm Q ^ (normalizedFactors I).count Q := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
    rw [map_multiset_prod, Finset.prod_multiset_map_count]
  rw [hI', ← Finset.prod_image (f := fun Q => absNorm Q ^ (normalizedFactors I).count Q)
    (g := Subtype.val) fun x _ y _ h => Subtype.ext h]
  calc ∏ Q ∈ A.image Subtype.val, absNorm Q ^ (normalizedFactors I).count Q
      ∣ ∏ Q ∈ A.image Subtype.val ∪ (normalizedFactors I).toFinset,
          absNorm Q ^ (normalizedFactors I).count Q :=
        Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left
    _ = ∏ Q ∈ (normalizedFactors I).toFinset, absNorm Q ^ (normalizedFactors I).count Q :=
        (Finset.prod_subset Finset.subset_union_right fun Q _ hQ => by
          rw [Multiset.count_eq_zero.2 fun h => hQ (Multiset.mem_toFinset.2 h), pow_zero]).symm

theorem prod_pow_count_le (A : Finset Pr) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∏ P ∈ A, (absNorm P.1 : ℝ) ^ (normalizedFactors I).count P.1 ≤ absNorm I := by
  have h0 : absNorm I ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (prod_pow_count_dvd A hI)
  exact_mod_cast this

/-- `c(j) ≤ 2a + c` for `j ≡ a + 4c (mod 6)`, `a ≤ 1`, `a + c ≥ 1`. -/
theorem jCost_le (a c : ℕ) (ha : a ≤ 1) (hac : 1 ≤ a + c) : jCost ((a + 4 * c) % 6) ≤ 2 * a + c := by
  unfold jCost
  split_ifs with h <;> omega

/-- **The cost of the active primes** (the companion paper's display after the local updates in its
proof of Lemma 6.6): `∏_{P∈𝒜} N(P)^{c(j_P)} ≤ N(t)²N(g)` for `t` squarefree and `𝒜` admissible. -/
theorem cost_le {t g : 𝓞 K} (ht : t ≠ 0) (hg : g ≠ 0) (htsq : Squarefree (span {t}))
    {A : Finset Pr} (hA : A ∈ admissible t g) :
    ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (jFix t g P) ≤
      (absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g}) := by
  classical
  have hAsub : A ⊆ primeSet (span {t * g}) := Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1
  have htb : span {t} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact ht
  have hgb : span {g} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hg
  have hnd := (squarefree_iff_nodup_normalizedFactors htb).1 htsq
  have hle : ∀ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (jFix t g P) ≤
      ((absNorm P.1 : ℝ) ^ (normalizedFactors (span {t})).count P.1) ^ 2 *
        (absNorm P.1 : ℝ) ^ (normalizedFactors (span {g})).count P.1 := by
    intro P hP
    have ha : (normalizedFactors (span {t})).count P.1 ≤ 1 :=
      Multiset.nodup_iff_count_le_one.1 hnd P.1
    have hmem : P.1 ∈ normalizedFactors (span {t * g}) := mem_primeSet.1 (hAsub hP)
    rw [← Ideal.span_singleton_mul_span_singleton, normalizedFactors_mul htb hgb] at hmem
    have hac : 1 ≤ (normalizedFactors (span {t})).count P.1 +
        (normalizedFactors (span {g})).count P.1 := by
      rw [← Multiset.count_add]; exact Multiset.count_pos.2 hmem
    rw [← pow_mul, ← pow_add]
    refine pow_le_pow_right₀ (by exact_mod_cast one_le_absNorm_Pr P) ?_
    have := jCost_le _ _ ha hac
    unfold jFix
    omega
  have hn0 : ∀ P ∈ A, 0 ≤ (absNorm P.1 : ℝ) ^ jCost (jFix t g P) := fun P _ =>
    pow_nonneg (Nat.cast_nonneg _) _
  have h1 := prod_pow_count_le A htb
  have h2 := prod_pow_count_le A hgb
  calc ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (jFix t g P)
      ≤ ∏ P ∈ A, ((absNorm P.1 : ℝ) ^ (normalizedFactors (span {t})).count P.1) ^ 2 *
          (absNorm P.1 : ℝ) ^ (normalizedFactors (span {g})).count P.1 :=
        Finset.prod_le_prod₀ hn0 hle
    _ = (∏ P ∈ A, (absNorm P.1 : ℝ) ^ (normalizedFactors (span {t})).count P.1) ^ 2 *
          ∏ P ∈ A, (absNorm P.1 : ℝ) ^ (normalizedFactors (span {g})).count P.1 := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
    _ ≤ (absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g}) :=
        mul_le_mul (pow_le_pow_left₀ (Finset.prod_nonneg fun P _ => pow_nonneg (Nat.cast_nonneg _) _)
          h1 2) h2 (Finset.prod_nonneg fun P _ => pow_nonneg (Nat.cast_nonneg _) _)
          (sq_nonneg _)

end Eis

end

#print axioms Eis.dualCoef_eq
#print axioms Eis.piece_cost_le
#print axioms Eis.cost_eq
#print axioms Eis.dualTerm_meanSquare
#print axioms Eis.cost_le
