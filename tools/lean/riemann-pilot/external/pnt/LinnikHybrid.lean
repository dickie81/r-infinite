/-
# Round 521, part 1: the hybrid mean value over the characters mod `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `S ⊆ (P, 2P]`, `c_j ∈ ℂ` and `q ≥ 1`, and write `D_χ(t) = Σ_{j∈S} c_jχ(j)j^{−it}` (`DirMean.dp`).
Summed over all Dirichlet characters mod `q`, `Σ_χ ∫_a^b |D_χ(t)|² dt ≤ (q(b − a) + 8P(1 + log P))Σ|c_j|²` for
`a ≤ b` (`mean_value_chars`). At one point `x_χ ∈ [lo + ½, hi − ½]` for each character in a set `R`, with nothing
relating the points of different characters,
`Σ_{χ∈R} |D_χ(x_χ)|² ≤ (q(hi − lo) + 8P(1 + log P))(2 + log²(2P))Σ|c_j|²` (`large_values_chars`). With the weights
`j^{−β_χ}`, `σ ≤ β_χ ≤ σ + ½`, the same holds with a factor `e` and `Σ|a_j|²j^{−2σ}` on the right
(`large_values_chars_off`).

* `mean_value_row`: `∫_a^b |Σ_{j∈S} c_j j^{−it}|² dt ≤ (b − a + 4PK)Σ|c_j|²` when `Σ_{j′ ∈ S, j′ ≠ j} 1/|j − j′| ≤ K`
  for every `j ∈ S` (`DirMean.mean_value` is the case `K = 2(1 + log P)`).
* `row_sum_class`: in one residue class mod `q` the row sums are at most `(2/q)(1 + log P)`.
* `sum_chars_norm_sq_le`: `Σ_χ |Σ_a χ(a)D_a|² ≤ φ(q)Σ_a |D_a|²`, from Mathlib's
  `DirichletCharacter.sum_char_inv_mul_char_eq`.
* `mean_value_chars`: `D_χ` splits over the classes mod `q` (`dp_twist_eq`); orthogonality, then `mean_value_row` in
  each class with `row_sum_class`, and `φ(q) ≤ q`.
* `large_values_chars`, `large_values_chars_off`: `DirMean.gallagher_one` on the unit interval about each `x_χ` (the
  derivative of `D_χ` is a polynomial of the same kind, with coefficients `−c_j log j`), then `mean_value_chars` on
  `[lo, hi]`; the weights by the Taylor bound `DirMean.dp_off_le`.
-/
import DirMean

open Real Complex MeasureTheory Set Finset

noncomputable section

namespace LinnikHybrid

open DirMean

/-! ### The mean value theorem with a row bound -/

/-- **The mean value theorem with a row bound**: for `S ⊆ (P, 2P]` with
`Σ_{j′ ∈ S, j′ ≠ j} 1/|j − j′| ≤ K` for every `j ∈ S`, `∫_a^b |D|² ≤ (b − a + 4PK)·Σ|c_j|²`
(`DirMean.mean_value` is the case `K = 2(1 + log P)`). -/
theorem mean_value_row {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    {a b : ℝ} (hab : a ≤ b) {K : ℝ}
    (hK : ∀ j ∈ S, ∑ j' ∈ S, (if j' = j then (0 : ℝ) else 1 / |(j : ℝ) - j'|) ≤ K) :
    ∫ t in a..b, ‖dp S c t‖ ^ 2 ≤ (b - a + 4 * P * K) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  set E : ℕ → ℕ → ℝ → ℂ := fun j j' t => c j * (starRingEnd ℂ) (c j')
      * Complex.exp (I * (((Real.log j' - Real.log j) * t : ℝ) : ℂ)) with hE
  have hcont : ∀ j j', Continuous (E j j') := fun j j' => by simp only [hE]; fun_prop
  have hsum_int : ∀ j ∈ S, ∀ j' ∈ S, IntervalIntegrable (E j j') volume a b :=
    fun j _ j' _ => (hcont j j').intervalIntegrable _ _
  have hc : Continuous fun t => ∑ j ∈ S, ∑ j' ∈ S, E j j' t := by fun_prop
  have hint : ∫ t in a..b, ‖dp S c t‖ ^ 2 = (∑ j ∈ S, ∑ j' ∈ S, ∫ t in a..b, E j j' t).re := by
    simp_rw [sq_norm_dp]
    show ∫ t in a..b, (∑ j ∈ S, ∑ j' ∈ S, E j j' t).re = _
    have key := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM (hc.intervalIntegrable (μ := volume) a b)
    simp only [Complex.reCLM_apply] at key
    rw [key]
    congr 1
    rw [intervalIntegral.integral_finsetSum fun j hj =>
      (continuous_finsetSum _ fun j' _ => hcont j j').intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [intervalIntegral.integral_finsetSum fun j' hj' => hsum_int j hj j' hj']
  rw [hint]
  set B : ℕ → ℕ → ℝ := fun j j' =>
    if j = j' then ‖c j‖ ^ 2 * (b - a) else ‖c j‖ * ‖c j'‖ * (4 * P / |(j : ℝ) - j'|) with hB
  have hbound : ∀ j ∈ S, ∀ j' ∈ S, ‖∫ t in a..b, E j j' t‖ ≤ B j j' := by
    intro j hj j' hj'
    simp only [hE, hB]
    rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, Complex.norm_conj]
    split_ifs with h
    · subst h
      have e : ∫ t in a..b, Complex.exp (I * (((Real.log j - Real.log j) * t : ℝ) : ℂ))
          = ((b - a : ℝ) : ℂ) := by simp
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)]
      ring_nf; exact le_refl _
    · have hlog := abs_log_sub_ge (hS hj) (hS hj') h
      have hjj : (0 : ℝ) < |(j : ℝ) - j'| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast h))
      have hP1 : 1 ≤ P := by
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 (hS hj); omega
      have hP1r : (1 : ℝ) ≤ P := by exact_mod_cast hP1
      have hP0 : (0 : ℝ) < 2 * P := by linarith
      have hl0 : 0 < |Real.log j' - Real.log j| := by
        rw [abs_sub_comm]; exact lt_of_lt_of_le (div_pos hjj hP0) hlog
      have hne : Real.log j' - Real.log j ≠ 0 := fun h0 => by
        rw [h0, abs_zero] at hl0; exact lt_irrefl _ hl0
      have h1 := norm_integral_exp_le hne a b
      have h2 : 2 / |Real.log j' - Real.log j| ≤ 4 * P / |(j : ℝ) - j'| := by
        rw [div_le_div_iff₀ hl0 hjj]
        have := (div_le_iff₀ hP0).1 hlog
        rw [abs_sub_comm (Real.log j')]
        nlinarith
      calc ‖c j‖ * ‖c j'‖ * ‖∫ t in a..b, Complex.exp (I * (((Real.log j' - Real.log j) * t : ℝ) : ℂ))‖
          ≤ ‖c j‖ * ‖c j'‖ * (2 / |Real.log j' - Real.log j|) := by
            gcongr
        _ ≤ ‖c j‖ * ‖c j'‖ * (4 * P / |(j : ℝ) - j'|) := by gcongr
  set Kf : ℕ → ℕ → ℝ := fun j j' => if j' = j then 0 else 1 / |(j : ℝ) - j'| with hKf
  have hK0 : ∀ j j', 0 ≤ Kf j j' := fun j j' => by simp only [hKf]; split_ifs <;> positivity
  have hKsym : ∀ j j', Kf j' j = Kf j j' := fun j j' => by
    simp only [hKf]; rw [abs_sub_comm]; split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  have hBle : ∀ j ∈ S, ∀ j' ∈ S, B j j' ≤ (if j = j' then ‖c j‖ ^ 2 * (b - a) else 0)
      + 2 * P * (‖c j‖ ^ 2 * Kf j j' + ‖c j'‖ ^ 2 * Kf j j') := by
    intro j _ j' _
    simp only [hB, hKf]
    by_cases h : j = j'
    · subst h; simp
    · simp only [h, Ne.symm h, ↓reduceIte, zero_add]
      have hjj : (0 : ℝ) < |(j : ℝ) - j'| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast h))
      have h2 := two_mul_le_add_sq ‖c j‖ ‖c j'‖
      rw [mul_div_assoc', div_le_iff₀ hjj]
      field_simp
      nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hc2 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  calc (∑ j ∈ S, ∑ j' ∈ S, ∫ t in a..b, E j j' t).re
      ≤ ‖∑ j ∈ S, ∑ j' ∈ S, ∫ t in a..b, E j j' t‖ := Complex.re_le_norm _
    _ ≤ ∑ j ∈ S, ∑ j' ∈ S, ‖∫ t in a..b, E j j' t‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j ∈ S, ∑ j' ∈ S, ((if j = j' then ‖c j‖ ^ 2 * (b - a) else 0)
          + 2 * P * (‖c j‖ ^ 2 * Kf j j' + ‖c j'‖ ^ 2 * Kf j j')) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun j' hj' =>
          (hbound j hj j' hj').trans (hBle j hj j' hj')
    _ = (b - a) * ∑ j ∈ S, ‖c j‖ ^ 2 + 2 * P * (∑ j ∈ S, ‖c j‖ ^ 2 * ∑ j' ∈ S, Kf j j'
          + ∑ j ∈ S, ∑ j' ∈ S, ‖c j'‖ ^ 2 * Kf j j') := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq]
        congr 1
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j hj => by simp only [hj, ↓reduceIte]; ring
        · rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j' _ => by ring
    _ = (b - a) * ∑ j ∈ S, ‖c j‖ ^ 2 + 2 * P * (2 * ∑ j ∈ S, ‖c j‖ ^ 2 * ∑ j' ∈ S, Kf j j') := by
        congr 2
        rw [Finset.sum_comm]
        have : ∑ j' ∈ S, ∑ j ∈ S, ‖c j'‖ ^ 2 * Kf j j' = ∑ j' ∈ S, ‖c j'‖ ^ 2 * ∑ j ∈ S, Kf j' j := by
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hKsym]
        rw [this]; ring
    _ ≤ (b - a) * ∑ j ∈ S, ‖c j‖ ^ 2 + 2 * P * (2 * ∑ j ∈ S, ‖c j‖ ^ 2 * K) := by
        gcongr with j hj
        exact hK j hj
    _ = _ := by rw [← Finset.sum_mul]; ring

/-! ### Residue classes -/

/-- In a residue class mod `q`, `Σ_{j′ ≠ j} 1/|j − j′| ≤ (2/q)(1 + log P)` on `(P, 2P]`. -/
theorem row_sum_class {P q j : ℕ} (hq : 1 ≤ q) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P))
    (hmod : ∀ j' ∈ S, j' ≡ j [MOD q]) (hj : j ∈ S) :
    ∑ j' ∈ S, (if j' = j then (0 : ℝ) else 1 / |(j : ℝ) - j'|) ≤ 2 / q * (1 + Real.log P) := by
  obtain ⟨hjl, hju⟩ := Finset.mem_Ioc.1 (hS hj)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hH : ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / h ≤ 1 + Real.log P := by
    have := harmonic_le_one_add_log P
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [one_div] using this
  have hnn : ∀ h ∈ Finset.Icc 1 P, (0 : ℝ) ≤ 1 / (q * h) := fun _ _ => by positivity
  have hle : ∀ j' ∈ S, (if j' = j then (0 : ℝ) else 1 / |(j : ℝ) - j'|)
      ≤ (if j < j' then (1 : ℝ) / ((j' - j : ℕ) : ℝ) else 0)
        + (if j' < j then (1 : ℝ) / ((j - j' : ℕ) : ℝ) else 0) := by
    intro j' _
    rcases lt_trichotomy j j' with h | h | h
    · have hlt : (j : ℝ) < j' := by exact_mod_cast h
      simp only [show j' ≠ j by omega, show ¬ j' < j by omega, h, ↓reduceIte, add_zero]
      rw [Nat.cast_sub h.le, abs_sub_comm, abs_of_pos (sub_pos.2 hlt)]
    · subst h; simp
    · have hlt : (j' : ℝ) < j := by exact_mod_cast h
      simp only [show j' ≠ j by omega, show ¬ j < j' by omega, h, ↓reduceIte, zero_add]
      rw [Nat.cast_sub h.le, abs_of_pos (sub_pos.2 hlt)]
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  -- each difference is `q·h` with `1 ≤ h ≤ P`
  have hA : ∑ j' ∈ S.filter (fun j' => j < j'), (1 : ℝ) / ((j' - j : ℕ) : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / (q * h) := by
    have hdiv : ∀ j' ∈ S.filter (fun j' => j < j'), q ∣ j' - j := fun j' hj' => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hj'
      exact (Nat.modEq_iff_dvd' h2.le).1 (hmod j' h1).symm
    have e : ∀ j' ∈ S.filter (fun j' => j < j'), (1 : ℝ) / ((j' - j : ℕ) : ℝ)
        = (1 : ℝ) / (q * (((j' - j) / q : ℕ) : ℝ)) := fun j' hj' => by
      congr 1
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdiv j' hj')]
    rw [Finset.sum_congr rfl e]
    rw [← Finset.sum_image (f := fun h : ℕ => (1 : ℝ) / (q * h)) (g := fun j' => (j' - j) / q)
      (fun x hx y hy hxy => by
        have hx' := hdiv x hx; have hy' := hdiv y hy
        have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2
        simp only at hxy
        have e1 := Nat.mul_div_cancel' hx'; have e2 := Nat.mul_div_cancel' hy'
        rw [hxy] at e1
        omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) (fun h hh _ => hnn h hh)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    obtain ⟨hx3, hx4⟩ := Finset.mem_Ioc.1 (hS hx1)
    have hx' := hdiv x hx
    have e1 := Nat.mul_div_cancel' hx'
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos ((x - j) / q) with h0 | h0
      · rw [h0, mul_zero] at e1; omega
      · exact h0
    · calc (x - j) / q ≤ x - j := Nat.div_le_self _ _
        _ ≤ P := by omega
  have hB : ∑ j' ∈ S.filter (fun j' => j' < j), (1 : ℝ) / ((j - j' : ℕ) : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / (q * h) := by
    have hdiv : ∀ j' ∈ S.filter (fun j' => j' < j), q ∣ j - j' := fun j' hj' => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hj'
      exact (Nat.modEq_iff_dvd' h2.le).1 (hmod j' h1)
    have e : ∀ j' ∈ S.filter (fun j' => j' < j), (1 : ℝ) / ((j - j' : ℕ) : ℝ)
        = (1 : ℝ) / (q * (((j - j') / q : ℕ) : ℝ)) := fun j' hj' => by
      congr 1
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdiv j' hj')]
    rw [Finset.sum_congr rfl e]
    rw [← Finset.sum_image (f := fun h : ℕ => (1 : ℝ) / (q * h)) (g := fun j' => (j - j') / q)
      (fun x hx y hy hxy => by
        have hx' := hdiv x hx; have hy' := hdiv y hy
        have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2
        simp only at hxy
        have e1 := Nat.mul_div_cancel' hx'; have e2 := Nat.mul_div_cancel' hy'
        rw [hxy] at e1
        omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) (fun h hh _ => hnn h hh)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    obtain ⟨hx3, hx4⟩ := Finset.mem_Ioc.1 (hS hx1)
    have hx' := hdiv x hx
    have e1 := Nat.mul_div_cancel' hx'
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos ((j - x) / q) with h0 | h0
      · rw [h0, mul_zero] at e1; omega
      · exact h0
    · calc (j - x) / q ≤ j - x := Nat.div_le_self _ _
        _ ≤ P := by omega
  have hsum : ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / (q * h) = (1 / q) * ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / h := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by rw [one_div_mul_one_div]
  have : (1 / (q : ℝ)) * ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / h ≤ (1 / q) * (1 + Real.log P) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have e2 : 2 / (q : ℝ) * (1 + Real.log P) = 2 * ((1 / q) * (1 + Real.log P)) := by ring
  rw [e2]
  linarith

/-! ### Orthogonality -/

/-- `conj χ(b) = χ(b⁻¹)` for a unit `b`. -/
theorem conj_apply_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ZMod q} (hb : IsUnit b) :
    (starRingEnd ℂ) (χ b) = χ b⁻¹ := by
  have h1 : (starRingEnd ℂ) (χ b) = χ⁻¹ b := MulChar.star_apply' χ b
  rw [h1, MulChar.inv_apply_eq_inv']
  have hu : χ b * χ b⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit _ hb, map_one]
  exact inv_eq_of_mul_eq_one_right hu

/-- **Orthogonality**: `Σ_χ |Σ_a χ(a)D_a|² ≤ φ(q)Σ_a |D_a|²`. -/
theorem sum_chars_norm_sq_le (q : ℕ) [NeZero q] (D : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ a, χ a * D a‖ ^ 2 ≤ q.totient * ∑ a, ‖D a‖ ^ 2 := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have horth : ∀ a b : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ a * (starRingEnd ℂ) (χ b)
      = if IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
    intro a b
    by_cases hb : IsUnit b
    · have e : ∀ χ : DirichletCharacter ℂ q, χ a * (starRingEnd ℂ) (χ b) = χ b⁻¹ * χ a := fun χ => by
        rw [conj_apply_unit χ hb, mul_comm]
      rw [Finset.sum_congr rfl fun χ _ => e χ, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb a]
      by_cases hab : a = b
      · simp [hab, hb]
      · simp [hab, Ne.symm hab]
    · have e : ∀ χ : DirichletCharacter ℂ q, χ a * (starRingEnd ℂ) (χ b) = 0 := fun χ => by
        rw [MulChar.map_nonunit χ hb, map_zero, mul_zero]
      rw [Finset.sum_congr rfl fun χ _ => e χ]
      simp [hb]
  have key : ∑ χ : DirichletCharacter ℂ q, (∑ a, χ a * D a) * (starRingEnd ℂ) (∑ a, χ a * D a)
      = (q.totient : ℂ) * ∑ b, (if IsUnit b then D b * (starRingEnd ℂ) (D b) else 0) := by
    simp_rw [map_sum, map_mul, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, ∑ b, χ a * D a * ((starRingEnd ℂ) (χ b) * (starRingEnd ℂ) (D b))
        = ∑ b, D a * (starRingEnd ℂ) (D b) * ∑ χ : DirichletCharacter ℂ q, χ a * (starRingEnd ℂ) (χ b) := by
      intro a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [Finset.sum_congr rfl fun a _ => this a]
    simp_rw [horth]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · by_cases ha : IsUnit a
      · simp [ha]; ring
      · simp [ha]
    · intro b _ hba
      simp [Ne.symm hba]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hre : ∑ χ : DirichletCharacter ℂ q, ‖∑ a, χ a * D a‖ ^ 2
      = q.totient * ∑ b, (if IsUnit b then ‖D b‖ ^ 2 else 0) := by
    have h1 : ∑ χ : DirichletCharacter ℂ q, ‖∑ a, χ a * D a‖ ^ 2
        = (∑ χ : DirichletCharacter ℂ q, (∑ a, χ a * D a) * (starRingEnd ℂ) (∑ a, χ a * D a)).re := by
      rw [Complex.re_sum]; exact Finset.sum_congr rfl fun χ _ => hsq _
    rw [h1, key]
    have h2 : ((q.totient : ℂ) * ∑ b, (if IsUnit b then D b * (starRingEnd ℂ) (D b) else 0))
        = (((q.totient : ℝ) * ∑ b, (if IsUnit b then ‖D b‖ ^ 2 else 0) : ℝ) : ℂ) := by
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · rfl
    rw [h2, Complex.ofReal_re]
  rw [hre]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun b _ => by split_ifs; exacts [le_rfl, by positivity]

/-- A twisted polynomial splits over the residue classes: `Σ_{j∈S} c_jχ(j)j^{−it} = Σ_a χ(a)D_a(t)`. -/
theorem dp_twist_eq (q : ℕ) [NeZero q] (S : Finset ℕ) (c : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    dp S (fun j => c j * χ j) t = ∑ a : ZMod q, χ a * dp (S.filter (fun j => (j : ZMod q) = a)) c t := by
  unfold dp
  rw [← Finset.sum_fiberwise S (fun j => (j : ZMod q))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h := (Finset.mem_filter.1 hj).2
  simp only [h]; ring

/-- **The hybrid mean value**: `Σ_χ ∫_a^b |Σ_{j∈S} c_jχ(j)j^{−it}|² dt ≤ (q(b − a) + 8P(1 + log P))Σ|c_j|²`
for `S ⊆ (P, 2P]`: orthogonality reduces it to the residue classes mod `q`, in each of which the frequencies are
`q/(2P)` apart (`row_sum_class`). -/
theorem mean_value_chars {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] {a b : ℝ} (hab : a ≤ b) :
    ∑ χ : DirichletCharacter ℂ q, ∫ t in a..b, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ (q * (b - a) + 8 * P * (1 + Real.log P)) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set Sa : ZMod q → Finset ℕ := fun a => S.filter (fun j => (j : ZMod q) = a) with hSa
  have hSaS : ∀ a, Sa a ⊆ Finset.Ioc P (2 * P) := fun a => (Finset.filter_subset _ _).trans hS
  have hlog : 0 ≤ 1 + Real.log P := by have := Real.log_natCast_nonneg P; linarith
  -- each class
  have hclass : ∀ r, ∫ t in a..b, ‖dp (Sa r) c t‖ ^ 2
      ≤ (b - a + 4 * P * (2 / q * (1 + Real.log P))) * ∑ j ∈ Sa r, ‖c j‖ ^ 2 := by
    intro r
    refine mean_value_row (hSaS r) c hab fun j hj => row_sum_class hq1 (hSaS r) (fun j' hj' => ?_) hj
    have h1 := (Finset.mem_filter.1 hj').2
    have h2 := (Finset.mem_filter.1 hj).2
    exact (ZMod.natCast_eq_natCast_iff j' j q).1 (h1.trans h2.symm)
  have hcont : ∀ χ : DirichletCharacter ℂ q, Continuous fun t => ‖dp S (fun j => c j * χ j) t‖ ^ 2 :=
    fun χ => (continuous_dp S _).norm.pow 2
  have hcont' : ∀ r : ZMod q, Continuous fun t => ‖dp (Sa r) c t‖ ^ 2 := fun r => (continuous_dp _ _).norm.pow 2
  have hpt : ∀ t, ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ q.totient * ∑ r : ZMod q, ‖dp (Sa r) c t‖ ^ 2 := by
    intro t
    simp_rw [dp_twist_eq q S c _ t]
    exact sum_chars_norm_sq_le q (fun r => dp (Sa r) c t)
  have hsplit : ∑ r : ZMod q, ∑ j ∈ Sa r, ‖c j‖ ^ 2 = ∑ j ∈ S, ‖c j‖ ^ 2 :=
    Finset.sum_fiberwise S (fun j => (j : ZMod q)) _
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hc0 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ χ : DirichletCharacter ℂ q, ∫ t in a..b, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      = ∫ t in a..b, ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2 :=
        (intervalIntegral.integral_finsetSum fun χ _ => (hcont χ).intervalIntegrable _ _).symm
    _ ≤ ∫ t in a..b, (q.totient : ℝ) * ∑ r : ZMod q, ‖dp (Sa r) c t‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on hab ?_ ?_ fun t _ => hpt t
        · exact (continuous_finsetSum _ fun χ _ => hcont χ).intervalIntegrable _ _
        · exact (continuous_const.mul (continuous_finsetSum _ fun r _ => hcont' r)).intervalIntegrable _ _
    _ = (q.totient : ℝ) * ∑ r : ZMod q, ∫ t in a..b, ‖dp (Sa r) c t‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum fun r _ => (hcont' r).intervalIntegrable _ _]
    _ ≤ (q.totient : ℝ) * ∑ r : ZMod q,
          (b - a + 4 * P * (2 / q * (1 + Real.log P))) * ∑ j ∈ Sa r, ‖c j‖ ^ 2 := by
        gcongr with r; exact hclass r
    _ = (q.totient : ℝ) * (b - a + 8 * (P / q) * (1 + Real.log P)) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
        rw [← Finset.mul_sum, hsplit]; ring
    _ ≤ (q * (b - a) + 8 * P * (1 + Real.log P)) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hc0
        have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
        have e : (q.totient : ℝ) * (8 * (P / q) * (1 + Real.log P)) ≤ 8 * P * (1 + Real.log P) := by
          have : (q.totient : ℝ) / q ≤ 1 := (div_le_one hq0).2 hφ
          have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
          calc (q.totient : ℝ) * (8 * (P / q) * (1 + Real.log P))
              = (q.totient / q) * (8 * P * (1 + Real.log P)) := by field_simp
            _ ≤ 1 * (8 * P * (1 + Real.log P)) := by gcongr
            _ = _ := one_mul _
        nlinarith [mul_le_mul_of_nonneg_right hφ (sub_nonneg.2 hab)]

/-- **Large values at one point per character**: for distinct characters `χ ∈ Rs` with points
`x_χ ∈ [lo + ½, hi − ½]`, `Σ_χ |Σ_{j∈S} c_jχ(j)j^{−ix_χ}|² ≤ (q(hi − lo) + 8P(1 + log P))(2 + log²(2P))Σ|c_j|²`
(Gallagher's lemma at each point, `DirMean.gallagher_one`, and `mean_value_chars`). -/
theorem large_values_chars {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] {lo hi : ℝ} (hab : lo ≤ hi) (Rs : Finset (DirichletCharacter ℂ q))
    (x : DirichletCharacter ℂ q → ℝ) (hR : ∀ χ ∈ Rs, lo + 1 / 2 ≤ x χ ∧ x χ ≤ hi - 1 / 2) :
    ∑ χ ∈ Rs, ‖dp S (fun j => c j * χ j) (x χ)‖ ^ 2
      ≤ (q * (hi - lo) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  set c' : ℕ → ℂ := fun j => c j * (-(I * (Real.log j : ℂ))) with hc'
  set L := q * (hi - lo) + 8 * P * (1 + Real.log P) with hL
  have hderiv : ∀ χ : DirichletCharacter ℂ q, ∀ t, HasDerivAt (dp S (fun j => c j * χ j))
      (dp S (fun j => c' j * χ j) t) t := fun χ t => by
    have h := hasDerivAt_dp S (fun j => c j * χ j) t
    have e : (fun j => c' j * χ j) = (fun j => c j * χ j * (-(I * (Real.log j : ℂ)))) := by
      funext j; simp only [hc']; ring
    rw [e]; exact h
  set g : DirichletCharacter ℂ q → ℝ → ℝ := fun χ t => ‖dp S (fun j => c j * χ j) t‖ ^ 2
      + 2 * ‖dp S (fun j => c j * χ j) t‖ * ‖dp S (fun j => c' j * χ j) t‖ with hg
  have hgc : ∀ χ, Continuous (g χ) := fun χ => by
    simp only [hg]
    have h1 := continuous_dp S (fun j => c j * χ j)
    have h2 := continuous_dp S (fun j => c' j * χ j)
    fun_prop
  have hg0 : ∀ χ t, 0 ≤ g χ t := fun χ t => by simp only [hg]; positivity
  have hone : ∀ χ ∈ Rs, ‖dp S (fun j => c j * χ j) (x χ)‖ ^ 2 ≤ ∫ t in lo..hi, g χ t := by
    intro χ hχ
    have h1 := gallagher_one (hderiv χ) (continuous_dp S _) (x χ)
    refine h1.trans ?_
    obtain ⟨hx1, hx2⟩ := hR χ hχ
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun t => hg0 χ t) ((hgc χ).intervalIntegrable _ _)
  have hInt0 : ∀ χ, 0 ≤ ∫ t in lo..hi, g χ t := fun χ =>
    intervalIntegral.integral_nonneg hab fun t _ => hg0 χ t
  have hle2 : ∀ χ, ∫ t in lo..hi, g χ t ≤ 2 * (∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2)
      + ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2 := by
    intro χ
    have i2 : IntervalIntegrable (fun t => 2 * ‖dp S (fun j => c j * χ j) t‖ ^ 2) MeasureTheory.volume lo hi :=
      (continuous_const.mul ((continuous_dp S _).norm.pow 2)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => ‖dp S (fun j => c' j * χ j) t‖ ^ 2) MeasureTheory.volume lo hi :=
      ((continuous_dp S _).norm.pow 2).intervalIntegrable _ _
    have := intervalIntegral.integral_mono_on hab ((hgc χ).intervalIntegrable _ _) (i2.add i3)
      fun t _ => by
        simp only [hg]
        nlinarith [sq_nonneg (‖dp S (fun j => c j * χ j) t‖ - ‖dp S (fun j => c' j * χ j) t‖)]
    rwa [intervalIntegral.integral_add i2 i3, intervalIntegral.integral_const_mul] at this
  have hm : ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ L * ∑ j ∈ S, ‖c j‖ ^ 2 := mean_value_chars hS c q hab
  have hm' : ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2
      ≤ L * ∑ j ∈ S, ‖c' j‖ ^ 2 := mean_value_chars hS c' q hab
  have hc'le : ∑ j ∈ S, ‖c' j‖ ^ 2 ≤ Real.log (2 * P) ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 (hS hj)
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hlj : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
    have hlj2 : Real.log j ≤ Real.log (2 * P) := Real.log_le_log hj0 (by exact_mod_cast hj2)
    simp only [hc', norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlj, mul_pow]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlj hlj2 2) (by positivity)
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [hL]; nlinarith [sub_nonneg.2 hab]
  have hS0 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ χ ∈ Rs, ‖dp S (fun j => c j * χ j) (x χ)‖ ^ 2 ≤ ∑ χ ∈ Rs, ∫ t in lo..hi, g χ t :=
        Finset.sum_le_sum hone
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, g χ t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun χ _ _ => hInt0 χ
    _ ≤ ∑ χ : DirichletCharacter ℂ q, (2 * (∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2)
          + ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2) := Finset.sum_le_sum fun χ _ => hle2 χ
    _ = 2 * (∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c j * χ j) t‖ ^ 2)
          + ∑ χ : DirichletCharacter ℂ q, ∫ t in lo..hi, ‖dp S (fun j => c' j * χ j) t‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + L * ∑ j ∈ S, ‖c' j‖ ^ 2 := by linarith
    _ ≤ 2 * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + L * (Real.log (2 * P) ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_left hc'le hL0; linarith
    _ = L * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2 := by ring

/-- **Large values off the line at one point per character**: as `large_values_chars`, each character with its
own `β_χ ∈ [σ, σ + ½]`, against `Σ_j |a_j|² j^{−2σ}` (the Taylor weights of `DirMean.dp_off_le`). -/
theorem large_values_chars_off {P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P))
    (a : ℕ → ℂ) (q : ℕ) [NeZero q] {σ lo hi : ℝ} (hab : lo ≤ hi)
    (Rs : Finset (DirichletCharacter ℂ q)) (x β : DirichletCharacter ℂ q → ℝ)
    (hR : ∀ χ ∈ Rs, lo + 1 / 2 ≤ x χ ∧ x χ ≤ hi - 1 / 2) (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ ≤ σ + 1 / 2) :
    ∑ χ ∈ Rs, ‖dp S (fun j => a j * χ j * (((j : ℝ) ^ (-β χ) : ℝ) : ℂ)) (x χ)‖ ^ 2
      ≤ Real.exp 1 * ((q * (hi - lo) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2))
        * ∑ j ∈ S, ‖a j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := by
  set L := (q * (hi - lo) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) with hL
  set Q0 := ∑ j ∈ S, ‖a j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 with hQ0
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [hL]; apply mul_nonneg _ (by positivity); nlinarith [sub_nonneg.2 hab]
  -- the polynomials `G_m` twisted by `χ`
  have hGform : ∀ (χ : DirichletCharacter ℂ q) m, cG (fun j => a j * χ j) σ P m = fun j => cG a σ P m j * χ j :=
    fun χ m => by funext j; simp only [cG]; ring
  have hGm : ∀ m, ∑ χ ∈ Rs, ‖dp S (cG (fun j => a j * χ j) σ P m) (x χ)‖ ^ 2 ≤ L * Q0 := by
    intro m
    simp_rw [hGform]
    refine (large_values_chars hS (cG a σ P m) q hab Rs x hR).trans ?_
    rw [hL]
    apply mul_le_mul_of_nonneg_left _ (by
      have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      apply mul_nonneg _ (by positivity); nlinarith [sub_nonneg.2 hab])
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hl0, hl1⟩ := ell_bounds (hS hj)
    rw [cG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow,
      mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ((j : ℝ) ^ (-σ)) ^ 2 * (Real.log ((j : ℝ) / P) ^ m) ^ 2 ≤ ((j : ℝ) ^ (-σ)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) (pow_le_one₀ hl0 hl1)) (by positivity)
      _ = _ := mul_one _
  have hK : ∀ (χ : DirichletCharacter ℂ q) y m, ‖dp S (cG (fun j => a j * χ j) σ P m) y‖
      ≤ ∑ j ∈ S, ‖a j‖ * (j : ℝ) ^ (-σ) := by
    intro χ y m
    refine (norm_dp_cG_le hS _ σ m y).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _)
      (DirichletCharacter.norm_le_one χ _)) (by positivity)
  have hs2 : ∀ (χ : DirichletCharacter ℂ q) y, Summable fun m => wT m * ‖dp S (cG (fun j => a j * χ j) σ P m) y‖ ^ 2 :=
    fun χ y => Summable.of_nonneg_of_le (fun m => mul_nonneg (wT_nonneg m) (by positivity))
      (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hK χ y m) 2) (wT_nonneg m))
      (hasSum_wT.summable.mul_right _)
  have hQ00 : 0 ≤ Q0 := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ χ ∈ Rs, ‖dp S (fun j => a j * χ j * (((j : ℝ) ^ (-β χ) : ℝ) : ℂ)) (x χ)‖ ^ 2
      ≤ ∑ χ ∈ Rs, Real.exp (1 / 2) * ∑' m, wT m * ‖dp S (cG (fun j => a j * χ j) σ P m) (x χ)‖ ^ 2 :=
        Finset.sum_le_sum fun χ hχ => dp_off_le hP hS (fun j => a j * χ j) (hβ χ hχ).1 (hβ χ hχ).2 (x χ)
    _ = Real.exp (1 / 2) * ∑' m, wT m * ∑ χ ∈ Rs, ‖dp S (cG (fun j => a j * χ j) σ P m) (x χ)‖ ^ 2 := by
        rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun χ _ => hs2 χ (x χ)]
        congr 1; congr 1; funext m; rw [Finset.mul_sum]
    _ ≤ Real.exp (1 / 2) * ∑' m, wT m * (L * Q0) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Summable.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left (hGm m) (wT_nonneg m))
          (Summable.of_nonneg_of_le (fun m => mul_nonneg (wT_nonneg m)
            (Finset.sum_nonneg fun _ _ => by positivity))
            (fun m => mul_le_mul_of_nonneg_left (hGm m) (wT_nonneg m)) (hasSum_wT.summable.mul_right _))
          (hasSum_wT.summable.mul_right _)
    _ = Real.exp 1 * L * Q0 := by
        rw [tsum_mul_right, hasSum_wT.tsum_eq]
        have : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
        rw [this]; ring

end LinnikHybrid

#print axioms LinnikHybrid.mean_value_row
#print axioms LinnikHybrid.sum_chars_norm_sq_le
#print axioms LinnikHybrid.mean_value_chars
#print axioms LinnikHybrid.large_values_chars
#print axioms LinnikHybrid.large_values_chars_off
