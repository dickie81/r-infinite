import Mathlib

/-! # Mean values and large values of Dirichlet polynomials (round 235)

For `D(t) = Σ_{j∈S} c_j j^{−it}` with `S ⊆ (P, 2P]`:
* `mean_value`: `∫_a^b |D|² ≤ (b − a + 8P(1 + log P))·Σ|c_j|²` (the diagonal gives `(b − a)Σ|c_j|²`;
  off the diagonal `|∫e^{iλt}| ≤ 2/|λ|` and `|log j − log j'| ≥ |j − j'|/(2P)`);
* `gallagher`: for `f` with a continuous derivative and `x₀`, `|f(x₀)|² ≤ ∫_{x₀−½}^{x₀+½}(|f|² + 2|f||f'|)`;
* `large_values`: at 1-separated points `x ∈ [a + ½, b − ½]`,
  `Σ_x |D(x)|² ≤ (b − a + 8P(1 + log P))(2 + log²(2P))·Σ|c_j|²`.
-/

open Real Complex MeasureTheory Set Finset

noncomputable section

namespace DirMean

/-- `D(t) = Σ_{j∈S} c_j e^{−it log j}`. -/
def dp (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ S, c j * Complex.exp (-(I * ((t * Real.log j : ℝ) : ℂ)))

theorem norm_exp_I_mul (x : ℝ) : ‖Complex.exp (I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem norm_exp_neg_I_mul (x : ℝ) : ‖Complex.exp (-(I * (x : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem continuous_dp (S : Finset ℕ) (c : ℕ → ℂ) : Continuous (dp S c) := by
  unfold dp; fun_prop

/-! ## The oscillatory integral -/

theorem norm_integral_exp_le {lam : ℝ} (hl : lam ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (I * ((lam * t : ℝ) : ℂ))‖ ≤ 2 / |lam| := by
  have hc : I * (lam : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hl)
  have e : (fun t : ℝ => Complex.exp (I * ((lam * t : ℝ) : ℂ))) = fun t : ℝ => Complex.exp ((I * lam) * t) := by
    funext t; push_cast; ring_nf
  rw [e, integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  have h1 : ‖Complex.exp (I * lam * b)‖ = 1 := by
    have := norm_exp_I_mul (lam * b); push_cast at this; rwa [mul_assoc]
  have h2 : ‖Complex.exp (I * lam * a)‖ = 1 := by
    have := norm_exp_I_mul (lam * a); push_cast at this; rwa [mul_assoc]
  rw [h1, h2]; norm_num

/-! ## Spacing of the frequencies -/

theorem log_sub_ge {j j' : ℕ} (hj : 0 < j) (hjj : j < j') {P : ℕ} (hP : j' ≤ 2 * P) :
    ((j' : ℝ) - j) / (2 * P) ≤ Real.log j' - Real.log j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj'0 : (0 : ℝ) < j' := by exact_mod_cast hj.trans hjj
  have hP0 : (j' : ℝ) ≤ 2 * P := by exact_mod_cast hP
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hj'0 hj0)
  rw [Real.log_div hj'0.ne' hj0.ne', inv_div] at h
  have h2 : ((j' : ℝ) - j) / (2 * P) ≤ 1 - j / j' := by
    rw [one_sub_div hj'0.ne']
    have hlt : (j : ℝ) < j' := by exact_mod_cast hjj
    exact div_le_div_of_nonneg_left (by linarith) hj'0 hP0
  linarith

theorem abs_log_sub_ge {P : ℕ} {j j' : ℕ} (hj : j ∈ Finset.Ioc P (2 * P)) (hj' : j' ∈ Finset.Ioc P (2 * P))
    (hne : j ≠ j') : |(j : ℝ) - j'| / (2 * P) ≤ |Real.log j - Real.log j'| := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 hj
  obtain ⟨hj'1, hj'2⟩ := Finset.mem_Ioc.1 hj'
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj'0 : (0 : ℝ) < j' := by exact_mod_cast (show 0 < j' by omega)
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt : (j : ℝ) < j' := by exact_mod_cast h
    rw [abs_sub_comm (j : ℝ), abs_of_pos (sub_pos.2 hlt), abs_sub_comm (Real.log j),
      abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hj0 hlt.le))]
    exact log_sub_ge (by omega) h hj'2
  · have hlt : (j' : ℝ) < j := by exact_mod_cast h
    rw [abs_of_pos (sub_pos.2 hlt), abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hj'0 hlt.le))]
    exact log_sub_ge (by omega) h hj2

/-- `Σ_{j'∈(P,2P], j'≠j} 1/|j − j'| ≤ 2(1 + log P)` for `j ∈ (P, 2P]`. -/
theorem sum_inv_dist_le {P j : ℕ} (hj : j ∈ Finset.Ioc P (2 * P)) :
    ∑ j' ∈ Finset.Ioc P (2 * P), (if j' = j then (0 : ℝ) else 1 / |(j : ℝ) - j'|)
      ≤ 2 * (1 + Real.log P) := by
  obtain ⟨hjl, hju⟩ := Finset.mem_Ioc.1 hj
  have hH : ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / h ≤ 1 + Real.log P := by
    have := harmonic_le_one_add_log P
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [one_div] using this
  have hnn : ∀ h ∈ Finset.Icc 1 P, (0 : ℝ) ≤ 1 / h := fun _ _ => by positivity
  -- each `j' ≠ j` is `j + h` or `j − h` with `1 ≤ h ≤ P`
  have hle : ∀ j' ∈ Finset.Ioc P (2 * P), (if j' = j then (0 : ℝ) else 1 / |(j : ℝ) - j'|)
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
  have hA : ∑ j' ∈ (Finset.Ioc P (2 * P)).filter (fun j' => j < j'), (1 : ℝ) / ((j' - j : ℕ) : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / h := by
    rw [← Finset.sum_image (f := fun h : ℕ => (1 : ℝ) / h) (g := fun j' => j' - j) (fun x hx y hy hxy => by
      have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2
      simp only at hxy; omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) (fun h hh _ => hnn h hh)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    obtain ⟨hx3, hx4⟩ := Finset.mem_Ioc.1 hx1
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hB : ∑ j' ∈ (Finset.Ioc P (2 * P)).filter (fun j' => j' < j), (1 : ℝ) / ((j - j' : ℕ) : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 P, (1 : ℝ) / h := by
    rw [← Finset.sum_image (f := fun h : ℕ => (1 : ℝ) / h) (g := fun j' => j - j') (fun x hx y hy hxy => by
      have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2
      simp only at hxy; omega)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) (fun h hh _ => hnn h hh)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    obtain ⟨hx3, hx4⟩ := Finset.mem_Ioc.1 hx1
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  linarith

/-! ## The mean value theorem -/

theorem exp_mul_conj_exp (x y : ℝ) :
    Complex.exp (-(I * (x : ℂ))) * (starRingEnd ℂ) (Complex.exp (-(I * (y : ℂ))))
      = Complex.exp (I * ((y - x : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

theorem sq_norm_dp (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ‖dp S c t‖ ^ 2 = (∑ j ∈ S, ∑ j' ∈ S, c j * (starRingEnd ℂ) (c j')
      * Complex.exp (I * (((Real.log j' - Real.log j) * t : ℝ) : ℂ))).re := by
  have h : dp S c t * (starRingEnd ℂ) (dp S c t) = ∑ j ∈ S, ∑ j' ∈ S, c j * (starRingEnd ℂ) (c j')
      * Complex.exp (I * (((Real.log j' - Real.log j) * t : ℝ) : ℂ)) := by
    unfold dp
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [map_mul]
    have := exp_mul_conj_exp (t * Real.log j) (t * Real.log j')
    rw [show (t * Real.log j' - t * Real.log j) = (Real.log j' - Real.log j) * t by ring] at this
    rw [← this]; ring
  rw [← h, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- **The mean value theorem** for Dirichlet polynomials supported in `(P, 2P]`. -/
theorem mean_value {P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖dp S c t‖ ^ 2 ≤ (b - a + 8 * P * (1 + Real.log P)) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
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
      have hP0 : (0 : ℝ) < 2 * P := by positivity
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
  set K : ℕ → ℕ → ℝ := fun j j' => if j' = j then 0 else 1 / |(j : ℝ) - j'| with hK
  have hK0 : ∀ j j', 0 ≤ K j j' := fun j j' => by simp only [hK]; split_ifs <;> positivity
  have hKsym : ∀ j j', K j' j = K j j' := fun j j' => by
    simp only [hK]; rw [abs_sub_comm]; split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  have hrow : ∀ j ∈ S, ∑ j' ∈ S, K j j' ≤ 2 * (1 + Real.log P) :=
    fun j hj => (Finset.sum_le_sum_of_subset_of_nonneg hS fun j' _ _ => hK0 j j').trans
      (sum_inv_dist_le (hS hj))
  have hBle : ∀ j ∈ S, ∀ j' ∈ S, B j j' ≤ (if j = j' then ‖c j‖ ^ 2 * (b - a) else 0)
      + 2 * P * (‖c j‖ ^ 2 * K j j' + ‖c j'‖ ^ 2 * K j j') := by
    intro j _ j' _
    simp only [hB, hK]
    by_cases h : j = j'
    · subst h; simp
    · simp only [h, Ne.symm h, ↓reduceIte, zero_add]
      have hjj : (0 : ℝ) < |(j : ℝ) - j'| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast h))
      have h2 := two_mul_le_add_sq ‖c j‖ ‖c j'‖
      rw [mul_div_assoc', div_le_iff₀ hjj]
      field_simp
      nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hlogP : 0 ≤ Real.log P := Real.log_natCast_nonneg P
  have hc2 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  calc (∑ j ∈ S, ∑ j' ∈ S, ∫ t in a..b, E j j' t).re
      ≤ ‖∑ j ∈ S, ∑ j' ∈ S, ∫ t in a..b, E j j' t‖ := Complex.re_le_norm _
    _ ≤ ∑ j ∈ S, ∑ j' ∈ S, ‖∫ t in a..b, E j j' t‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j ∈ S, ∑ j' ∈ S, ((if j = j' then ‖c j‖ ^ 2 * (b - a) else 0)
          + 2 * P * (‖c j‖ ^ 2 * K j j' + ‖c j'‖ ^ 2 * K j j')) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun j' hj' =>
          (hbound j hj j' hj').trans (hBle j hj j' hj')
    _ = (b - a) * ∑ j ∈ S, ‖c j‖ ^ 2 + 2 * P * (∑ j ∈ S, ‖c j‖ ^ 2 * ∑ j' ∈ S, K j j'
          + ∑ j ∈ S, ∑ j' ∈ S, ‖c j'‖ ^ 2 * K j j') := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq]
        congr 1
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j hj => by simp only [hj, ↓reduceIte]; ring
        · rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j' _ => by ring
    _ = (b - a) * ∑ j ∈ S, ‖c j‖ ^ 2 + 2 * P * (2 * ∑ j ∈ S, ‖c j‖ ^ 2 * ∑ j' ∈ S, K j j') := by
        congr 2
        rw [Finset.sum_comm]
        have : ∑ j' ∈ S, ∑ j ∈ S, ‖c j'‖ ^ 2 * K j j' = ∑ j' ∈ S, ‖c j'‖ ^ 2 * ∑ j ∈ S, K j' j := by
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hKsym]
        rw [this]; ring
    _ ≤ (b - a) * ∑ j ∈ S, ‖c j‖ ^ 2 + 2 * P * (2 * ∑ j ∈ S, ‖c j‖ ^ 2 * (2 * (1 + Real.log P))) := by
        gcongr with j hj
        exact hrow j hj
    _ = _ := by rw [← Finset.sum_mul]; ring

/-! ## Gallagher's lemma -/

theorem gallagher_one {f f' : ℝ → ℂ} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') (x : ℝ) :
    ‖f x‖ ^ 2 ≤ ∫ t in (x - 1 / 2)..(x + 1 / 2), (‖f t‖ ^ 2 + 2 * ‖f t‖ * ‖f' t‖) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  set g' : ℝ → ℝ := fun t => 2 * inner ℝ (f t) (f' t) with hg'
  have hg : ∀ t, HasDerivAt (fun t => ‖f t‖ ^ 2) (g' t) t := fun t => (hf t).norm_sq
  have hg'c : Continuous g' := by simp only [hg']; fun_prop
  have hgb : ∀ t, |g' t| ≤ 2 * ‖f t‖ * ‖f' t‖ := fun t => by
    simp only [hg', abs_mul, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  set lo := x - 1 / 2
  set hi := x + 1 / 2
  have hlohi : lo ≤ hi := by simp only [lo, hi]; linarith
  have habs : IntervalIntegrable (fun u => |g' u|) volume lo hi := (hg'c.abs).intervalIntegrable _ _
  have key : ∀ t ∈ Icc lo hi, ‖f x‖ ^ 2 ≤ ‖f t‖ ^ 2 + ∫ u in lo..hi, |g' u| := by
    intro t ht
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := t) (b := x) (fun u _ => hg u)
      (hg'c.intervalIntegrable _ _)
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc lo hi)] fun u => |g' u| := Filter.Eventually.of_forall fun _ => abs_nonneg _
    have hx : x ∈ Icc lo hi := ⟨by simp only [lo]; linarith, by simp only [hi]; linarith⟩
    have h2 : |∫ u in t..x, g' u| ≤ ∫ u in lo..hi, |g' u| := by
      rcases le_total t x with htx | htx
      · refine (intervalIntegral.abs_integral_le_integral_abs htx).trans ?_
        exact intervalIntegral.integral_mono_interval ht.1 htx hx.2 hnn habs
      · rw [intervalIntegral.integral_symm, abs_neg]
        refine (intervalIntegral.abs_integral_le_integral_abs htx).trans ?_
        exact intervalIntegral.integral_mono_interval hx.1 htx ht.2 hnn habs
    rw [hftc] at h2
    linarith [le_abs_self (‖f x‖ ^ 2 - ‖f t‖ ^ 2)]
  have hgc : Continuous fun t => ‖f t‖ ^ 2 := by fun_prop
  have hI := intervalIntegral.integral_mono_on (μ := volume) hlohi intervalIntegrable_const
    ((hgc.intervalIntegrable lo hi).add intervalIntegrable_const) key
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hgc.intervalIntegrable lo hi)
    intervalIntegrable_const, intervalIntegral.integral_const] at hI
  have hlen : hi - lo = 1 := by simp only [lo, hi]; ring
  rw [hlen, one_smul, one_smul] at hI
  have h3 : ∫ u in lo..hi, |g' u| ≤ ∫ u in lo..hi, 2 * ‖f u‖ * ‖f' u‖ :=
    intervalIntegral.integral_mono_on hlohi habs ((by fun_prop : Continuous fun u =>
      2 * ‖f u‖ * ‖f' u‖).intervalIntegrable (μ := volume) _ _) fun u _ => hgb u
  rw [intervalIntegral.integral_add (hgc.intervalIntegrable lo hi)
    ((by fun_prop : Continuous fun u => 2 * ‖f u‖ * ‖f' u‖).intervalIntegrable lo hi)]
  linarith

theorem gallagher {f f' : ℝ → ℂ} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') {a b : ℝ}
    (R : Finset ℝ) (hsep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 1 ≤ |x - y|)
    (hR : ∀ x ∈ R, a + 1 / 2 ≤ x ∧ x ≤ b - 1 / 2) (hab : a ≤ b) :
    ∑ x ∈ R, ‖f x‖ ^ 2 ≤ ∫ t in a..b, (‖f t‖ ^ 2 + 2 * ‖f t‖ * ‖f' t‖) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  set h : ℝ → ℝ := fun t => ‖f t‖ ^ 2 + 2 * ‖f t‖ * ‖f' t‖ with hh
  have hc : Continuous h := by simp only [hh]; fun_prop
  have h0 : ∀ t, 0 ≤ h t := fun t => by simp only [hh]; positivity
  set I : ℝ → Set ℝ := fun x => Ioc (x - 1 / 2) (x + 1 / 2)
  have hint : ∀ x, Integrable ((I x).indicator h) :=
    fun x => (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have h1 : ∑ x ∈ R, ‖f x‖ ^ 2 ≤ ∑ x ∈ R, ∫ t, (I x).indicator h t := by
    refine Finset.sum_le_sum fun x _ => ?_
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact gallagher_one hf hf' x
  have h2 : ∀ t, ∑ x ∈ R, (I x).indicator h t ≤ (Ioc a b).indicator h t := by
    intro t
    have hcard : (R.filter fun x => t ∈ I x).card ≤ 1 := by
      refine Finset.card_le_one.2 fun x hx y hy => ?_
      obtain ⟨_, hxt⟩ := Finset.mem_filter.1 hx
      obtain ⟨_, hyt⟩ := Finset.mem_filter.1 hy
      by_contra hne
      have := hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hne
      simp only [I, Set.mem_Ioc] at hxt hyt
      rcases le_or_gt 0 (x - y) with hxy | hxy
      · rw [abs_of_nonneg hxy] at this; linarith [hxt.1, hyt.2]
      · rw [abs_of_neg hxy] at this; linarith [hxt.2, hyt.1]
    have e : ∑ x ∈ R, (I x).indicator h t = (R.filter fun x => t ∈ I x).card * h t := by
      rw [← Finset.sum_filter_add_sum_filter_not R (fun x => t ∈ I x)]
      rw [Finset.sum_congr rfl (fun x hx => Set.indicator_of_mem (Finset.mem_filter.1 hx).2 h),
        Finset.sum_congr rfl (fun x hx => Set.indicator_of_notMem (Finset.mem_filter.1 hx).2 h)]
      simp
    rw [e]
    by_cases ht : t ∈ Ioc a b
    · rw [Set.indicator_of_mem ht]
      have := h0 t
      calc ((R.filter fun x => t ∈ I x).card : ℝ) * h t ≤ 1 * h t :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) this
        _ = h t := one_mul _
    · rw [Set.indicator_of_notMem ht]
      have : (R.filter fun x => t ∈ I x) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun x hx htx => ht ?_
        obtain ⟨h1, h2⟩ := hR x hx
        simp only [I, Set.mem_Ioc] at htx
        exact ⟨by linarith [htx.1], by linarith [htx.2]⟩
      rw [this]; simp
  calc ∑ x ∈ R, ‖f x‖ ^ 2 ≤ ∑ x ∈ R, ∫ t, (I x).indicator h t := h1
    _ = ∫ t, ∑ x ∈ R, (I x).indicator h t := (integral_finsetSum _ fun x _ => hint x).symm
    _ ≤ ∫ t, (Ioc a b).indicator h t :=
        integral_mono (integrable_finsetSum _ fun x _ => hint x)
          ((hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc) h2
    _ = ∫ t in a..b, h t := by rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab]

/-! ## Large values -/

theorem hasDerivAt_dp (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (dp S c) (dp S (fun j => c j * (-(I * (Real.log j : ℂ)))) t) t := by
  unfold dp
  have hterm : ∀ j ∈ S, HasDerivAt (fun t : ℝ => c j * Complex.exp (-(I * ((t * Real.log j : ℝ) : ℂ))))
      (c j * (-(I * (Real.log j : ℂ))) * Complex.exp (-(I * ((t * Real.log j : ℝ) : ℂ)))) t := by
    intro j _
    have h1 : HasDerivAt (fun t : ℝ => ((t * Real.log j : ℝ) : ℂ)) ((Real.log j : ℝ) : ℂ) t := by
      have := ((hasDerivAt_id' t).mul_const (Real.log j)).ofReal_comp
      rwa [one_mul] at this
    have h3 : HasDerivAt (fun y : ℝ => -(I * ((y * Real.log j : ℝ) : ℂ))) (-(I * (Real.log j : ℂ))) t :=
      (h1.const_mul I).neg
    have h2 := h3.cexp.const_mul (c j)
    convert h2 using 1
    ring
  convert HasDerivAt.fun_sum hterm using 1

theorem continuous_dp' (S : Finset ℕ) (c : ℕ → ℂ) : Continuous (dp S c) := continuous_dp S c

/-- **Large values** at 1-separated points of `[a + ½, b − ½]`. -/
theorem large_values {P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    {a b : ℝ} (hab : a ≤ b) (R : Finset ℝ) (hsep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 1 ≤ |x - y|)
    (hR : ∀ x ∈ R, a + 1 / 2 ≤ x ∧ x ≤ b - 1 / 2) :
    ∑ x ∈ R, ‖dp S c x‖ ^ 2
      ≤ (b - a + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  set c' : ℕ → ℂ := fun j => c j * (-(I * (Real.log j : ℂ))) with hc'
  have hG := gallagher (fun t => hasDerivAt_dp S c t) (continuous_dp S c') R hsep hR hab
  have i1 : IntervalIntegrable (fun t => ‖dp S c t‖ ^ 2 + 2 * ‖dp S c t‖ * ‖dp S c' t‖) volume a b :=
    ((continuous_dp S c).norm.pow 2 |>.add
      ((continuous_const.mul (continuous_dp S c).norm).mul (continuous_dp S c').norm)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => 2 * ‖dp S c t‖ ^ 2) volume a b :=
    (continuous_const.mul ((continuous_dp S c).norm.pow 2)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => ‖dp S c' t‖ ^ 2) volume a b :=
    ((continuous_dp S c').norm.pow 2).intervalIntegrable _ _
  have hle : ∫ t in a..b, (‖dp S c t‖ ^ 2 + 2 * ‖dp S c t‖ * ‖dp S c' t‖)
      ≤ 2 * (∫ t in a..b, ‖dp S c t‖ ^ 2) + ∫ t in a..b, ‖dp S c' t‖ ^ 2 := by
    have := intervalIntegral.integral_mono_on hab i1 (i2.add i3)
      fun t _ => by nlinarith [sq_nonneg (‖dp S c t‖ - ‖dp S c' t‖)]
    rwa [intervalIntegral.integral_add i2 i3, intervalIntegral.integral_const_mul] at this
  have hm := mean_value hP hS c hab
  have hm' := mean_value hP hS c' hab
  set L := b - a + 8 * P * (1 + Real.log P) with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    rw [hL]; nlinarith [sub_nonneg.2 hab]
  have hc'le : ∑ j ∈ S, ‖c' j‖ ^ 2 ≤ Real.log (2 * P) ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 (hS hj)
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hlj : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
    have hlj2 : Real.log j ≤ Real.log (2 * P) :=
      Real.log_le_log hj0 (by exact_mod_cast hj2)
    simp only [hc', norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlj, mul_pow]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlj hlj2 2) (by positivity)
  have hS0 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ x ∈ R, ‖dp S c x‖ ^ 2 ≤ 2 * (∫ t in a..b, ‖dp S c t‖ ^ 2) + ∫ t in a..b, ‖dp S c' t‖ ^ 2 :=
        hG.trans hle
    _ ≤ 2 * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + L * ∑ j ∈ S, ‖c' j‖ ^ 2 := by linarith
    _ ≤ 2 * (L * ∑ j ∈ S, ‖c j‖ ^ 2) + L * (Real.log (2 * P) ^ 2 * ∑ j ∈ S, ‖c j‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_left hc'le hL0; linarith
    _ = L * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2 := by ring

/-! ## Off the line: `β ≥ σ`, by Taylor expansion of `j^{−(β−σ)}` -/

/-- Weighted Cauchy–Schwarz for series. -/
theorem sq_tsum_le {w y : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) (hws : Summable w)
    (hwy : Summable fun m => w m * y m) (hwy2 : Summable fun m => w m * y m ^ 2) :
    (∑' m, w m * y m) ^ 2 ≤ (∑' m, w m) * ∑' m, w m * y m ^ 2 := by
  set W := ∑' m, w m
  set A := ∑' m, w m * y m
  set B := ∑' m, w m * y m ^ 2
  have hW : 0 ≤ W := tsum_nonneg hw
  have key : ∀ t : ℝ, 0 ≤ B - 2 * t * A + t ^ 2 * W := by
    intro t
    have h : HasSum (fun m => w m * (y m - t) ^ 2) (B - 2 * t * A + t ^ 2 * W) := by
      have := (hwy2.hasSum.sub (hwy.hasSum.mul_left (2 * t))).add (hws.hasSum.mul_left (t ^ 2))
      convert this using 1; funext m; ring
    exact h.nonneg fun m => mul_nonneg (hw m) (sq_nonneg _)
  rcases hW.lt_or_eq with hW0 | hW0
  · have h := key (A / W)
    have e : B - 2 * (A / W) * A + (A / W) ^ 2 * W = B - A ^ 2 / W := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hW0] at h
    linarith [mul_comm B W]
  · by_cases hA : A = 0
    · rw [hA, ← hW0]; simp
    · exfalso
      have h := key ((B + 1) / (2 * A))
      rw [← hW0] at h
      have e : B - 2 * ((B + 1) / (2 * A)) * A + ((B + 1) / (2 * A)) ^ 2 * 0 = -1 := by
        field_simp; ring
      linarith

/-- `ℓ_j = log(j/P) ∈ [0, 1)` on `(P, 2P]`. -/
theorem ell_bounds {P j : ℕ} (hj : j ∈ Finset.Ioc P (2 * P)) :
    0 ≤ Real.log ((j : ℝ) / P) ∧ Real.log ((j : ℝ) / P) ≤ 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hj
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hjP : (P : ℝ) ≤ j := by exact_mod_cast h1.le
  have hj2 : (j : ℝ) ≤ 2 * P := by exact_mod_cast h2
  constructor
  · exact Real.log_nonneg (by rw [le_div_iff₀ hP0]; linarith)
  · have : (j : ℝ) / P ≤ 2 := by rw [div_le_iff₀ hP0]; linarith
    have hj0 : (0 : ℝ) < j := by linarith
    calc Real.log ((j : ℝ) / P) ≤ Real.log 2 := Real.log_le_log (div_pos hj0 hP0) this
      _ ≤ 1 := by have := Real.log_two_lt_d9; linarith

/-- The Taylor weights `w_m = 2^{−m}/m!`, with `Σ w_m = e^{1/2}`. -/
def wT (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ m / m.factorial

theorem hasSum_wT : HasSum wT (Real.exp (1 / 2)) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (1 / 2)
  rw [← Real.exp_eq_exp_ℝ] at this
  exact this

theorem wT_nonneg (m : ℕ) : 0 ≤ wT m := by unfold wT; positivity

/-- The line polynomials `G_m(x) = Σ_j a_j j^{−σ} ℓ_j^m j^{−ix}`. -/
def cG (a : ℕ → ℂ) (σ : ℝ) (P : ℕ) (m : ℕ) (j : ℕ) : ℂ :=
  a j * (((j : ℝ) ^ (-σ) * Real.log ((j : ℝ) / P) ^ m : ℝ) : ℂ)

theorem norm_dp_cG_le {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ) (σ : ℝ)
    (m : ℕ) (x : ℝ) : ‖dp S (cG a σ P m) x‖ ≤ ∑ j ∈ S, ‖a j‖ * (j : ℝ) ^ (-σ) := by
  unfold dp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  obtain ⟨hl0, hl1⟩ := ell_bounds (hS hj)
  rw [norm_mul, norm_exp_neg_I_mul, mul_one, cG, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc (j : ℝ) ^ (-σ) * Real.log ((j : ℝ) / P) ^ m ≤ (j : ℝ) ^ (-σ) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hl0 hl1) (by positivity)
    _ = _ := mul_one _

/-- **One point off the line**: `|F(β + ix)|² ≤ e^{1/2} Σ_m w_m |G_m(x)|²` for `σ ≤ β ≤ σ + ½`. -/
theorem dp_off_le {P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ)
    {σ β : ℝ} (h1 : σ ≤ β) (h2 : β ≤ σ + 1 / 2) (x : ℝ) :
    ‖dp S (fun j => a j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) x‖ ^ 2
      ≤ Real.exp (1 / 2) * ∑' m, wT m * ‖dp S (cG a σ P m) x‖ ^ 2 := by
  set u := β - σ with hu
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 / 2 := by linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  set K := ∑ j ∈ S, ‖a j‖ * (j : ℝ) ^ (-σ) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => by positivity
  have hGb : ∀ m, ‖dp S (cG a σ P m) x‖ ≤ K := fun m => norm_dp_cG_le hS a σ m x
  set E : ℕ → ℂ := fun j => Complex.exp (-(I * ((x * Real.log j : ℝ) : ℂ))) with hE
  set ell : ℕ → ℝ := fun j => Real.log ((j : ℝ) / P) with hell
  -- the expansion, one `j` at a time
  have hj : ∀ j ∈ S, HasSum (fun m => ((((-u) ^ m / m.factorial : ℝ)) : ℂ) * (cG a σ P m j * E j))
      (a j * (((j : ℝ) ^ (-σ) * Real.exp (-u * ell j) : ℝ) : ℂ) * E j) := by
    intro j _
    have hexp := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-u * ell j)
    rw [← Real.exp_eq_exp_ℝ] at hexp
    have hc := (Complex.ofRealCLM.hasSum hexp).mul_left (a j * (((j : ℝ) ^ (-σ) : ℝ) : ℂ) * E j)
    convert hc using 1
    · funext m
      simp only [cG, Complex.ofRealCLM_apply, hell]
      push_cast
      rw [mul_pow]; ring
    · simp only [Complex.ofRealCLM_apply]; push_cast; ring
  have hsum := hasSum_sum hj
  have e1 : ∀ j ∈ S, ((j : ℝ) ^ (-σ) * Real.exp (-u * ell j) : ℝ) = (P : ℝ) ^ u * (j : ℝ) ^ (-β) := by
    intro j hjS
    obtain ⟨hj1, _⟩ := Finset.mem_Ioc.1 (hS hjS)
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    simp only [hell]
    rw [Real.log_div hj0.ne' hP0.ne', Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos hj0,
      Real.rpow_def_of_pos hj0, ← Real.exp_add, ← Real.exp_add]
    congr 1; rw [hu]; ring
  have hval : ∑ j ∈ S, a j * (((j : ℝ) ^ (-σ) * Real.exp (-u * ell j) : ℝ) : ℂ) * E j
      = (((P : ℝ) ^ u : ℝ) : ℂ) * dp S (fun j => a j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) x := by
    unfold dp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hjS => ?_
    rw [e1 j hjS]; simp only [hE]; push_cast; ring
  have hterm : ∀ m, (∑ j ∈ S, ((((-u) ^ m / m.factorial : ℝ)) : ℂ) * (cG a σ P m j * E j))
      = ((((-u) ^ m / m.factorial : ℝ)) : ℂ) * dp S (cG a σ P m) x := by
    intro m; unfold dp; rw [Finset.mul_sum]
  simp_rw [hterm] at hsum
  rw [hval] at hsum
  -- norms
  have hwm : ∀ m, ‖((((-u) ^ m / m.factorial : ℝ)) : ℂ) * dp S (cG a σ P m) x‖
      ≤ wT m * ‖dp S (cG a σ P m) x‖ := by
    intro m
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
      abs_of_nonneg hu0, Nat.abs_cast]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    unfold wT
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hu0 hu1 m) (by positivity)
  have hs1 : Summable fun m => wT m * ‖dp S (cG a σ P m) x‖ :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (wT_nonneg m) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (hGb m) (wT_nonneg m)) (hasSum_wT.summable.mul_right K)
  have hs2 : Summable fun m => wT m * ‖dp S (cG a σ P m) x‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (wT_nonneg m) (by positivity))
      (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hGb m) 2) (wT_nonneg m))
      (hasSum_wT.summable.mul_right (K ^ 2))
  have hn : Summable fun m => ‖((((-u) ^ m / m.factorial : ℝ)) : ℂ) * dp S (cG a σ P m) x‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hwm hs1
  have hF : ‖dp S (fun j => a j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) x‖ ≤ ∑' m, wT m * ‖dp S (cG a σ P m) x‖ := by
    have hPu : 1 ≤ (P : ℝ) ^ u := Real.one_le_rpow (by exact_mod_cast hP) hu0
    have h1 : ‖(((P : ℝ) ^ u : ℝ) : ℂ) * dp S (fun j => a j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) x‖
        ≤ ∑' m, wT m * ‖dp S (cG a σ P m) x‖ := by
      rw [← hsum.tsum_eq]
      exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hwm hs1)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    nlinarith [norm_nonneg (dp S (fun j => a j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) x)]
  have hcs := sq_tsum_le wT_nonneg hasSum_wT.summable hs1 hs2
  rw [hasSum_wT.tsum_eq] at hcs
  calc ‖dp S (fun j => a j * (((j : ℝ) ^ (-β) : ℝ) : ℂ)) x‖ ^ 2
      ≤ (∑' m, wT m * ‖dp S (cG a σ P m) x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
    _ ≤ _ := hcs

/-- **Large values off the line**: at 1-separated points `x ∈ [a + ½, b − ½]`, each with its own
`β_x ∈ [σ, σ + ½]`, `Σ_x |Σ_j a_j j^{−β_x − ix}|² ≤ e·(b − a + 8P(1 + log P))(2 + log²(2P))·Σ_j |a_j|² j^{−2σ}`. -/
theorem large_values_off {P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P))
    (a : ℕ → ℂ) {σ : ℝ} {lo hi : ℝ} (hab : lo ≤ hi) (R : Finset ℝ)
    (hsep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 1 ≤ |x - y|) (hR : ∀ x ∈ R, lo + 1 / 2 ≤ x ∧ x ≤ hi - 1 / 2)
    (β : ℝ → ℝ) (hβ : ∀ x ∈ R, σ ≤ β x ∧ β x ≤ σ + 1 / 2) :
    ∑ x ∈ R, ‖dp S (fun j => a j * (((j : ℝ) ^ (-β x) : ℝ) : ℂ)) x‖ ^ 2
      ≤ Real.exp 1 * ((hi - lo + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2))
        * ∑ j ∈ S, ‖a j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := by
  set L := (hi - lo + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) with hL
  set Q0 := ∑ j ∈ S, ‖a j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 with hQ0
  have hQ0' : 0 ≤ Q0 := Finset.sum_nonneg fun _ _ => by positivity
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    rw [hL]; apply mul_nonneg _ (by positivity); nlinarith [sub_nonneg.2 hab]
  -- each `G_m` at the points of `R`
  have hGm : ∀ m, ∑ x ∈ R, ‖dp S (cG a σ P m) x‖ ^ 2 ≤ L * Q0 := by
    intro m
    refine (large_values hP hS (cG a σ P m) hab R hsep hR).trans ?_
    rw [hL]
    apply mul_le_mul_of_nonneg_left _ (by
      have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
      apply mul_nonneg _ (by positivity); nlinarith [sub_nonneg.2 hab])
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hl0, hl1⟩ := ell_bounds (hS hj)
    rw [cG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow,
      mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ((j : ℝ) ^ (-σ)) ^ 2 * (Real.log ((j : ℝ) / P) ^ m) ^ 2 ≤ ((j : ℝ) ^ (-σ)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) (pow_le_one₀ hl0 hl1)) (by positivity)
      _ = _ := mul_one _
  -- summability in `m` at each point
  have hK : ∀ x, ∀ m, ‖dp S (cG a σ P m) x‖ ≤ ∑ j ∈ S, ‖a j‖ * (j : ℝ) ^ (-σ) :=
    fun x m => norm_dp_cG_le hS a σ m x
  have hs2 : ∀ x, Summable fun m => wT m * ‖dp S (cG a σ P m) x‖ ^ 2 := fun x =>
    Summable.of_nonneg_of_le (fun m => mul_nonneg (wT_nonneg m) (by positivity))
      (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hK x m) 2) (wT_nonneg m))
      (hasSum_wT.summable.mul_right _)
  calc ∑ x ∈ R, ‖dp S (fun j => a j * (((j : ℝ) ^ (-β x) : ℝ) : ℂ)) x‖ ^ 2
      ≤ ∑ x ∈ R, Real.exp (1 / 2) * ∑' m, wT m * ‖dp S (cG a σ P m) x‖ ^ 2 :=
        Finset.sum_le_sum fun x hx => dp_off_le hP hS a (hβ x hx).1 (hβ x hx).2 x
    _ = Real.exp (1 / 2) * ∑' m, wT m * ∑ x ∈ R, ‖dp S (cG a σ P m) x‖ ^ 2 := by
        rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun x _ => hs2 x]
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

/-- `large_values_off` for an indexed family of points. -/
theorem large_values_off' {ι : Type*} {P : ℕ} (hP : 1 ≤ P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P))
    (a : ℕ → ℂ) {σ : ℝ} {lo hi : ℝ} (hab : lo ≤ hi) (Rs : Finset ι) (x β : ι → ℝ)
    (hsep : ∀ r ∈ Rs, ∀ s ∈ Rs, r ≠ s → 1 ≤ |x r - x s|)
    (hR : ∀ r ∈ Rs, lo + 1 / 2 ≤ x r ∧ x r ≤ hi - 1 / 2)
    (hβ : ∀ r ∈ Rs, σ ≤ β r ∧ β r ≤ σ + 1 / 2) :
    ∑ r ∈ Rs, ‖dp S (fun j => a j * (((j : ℝ) ^ (-β r) : ℝ) : ℂ)) (x r)‖ ^ 2
      ≤ Real.exp 1 * ((hi - lo + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2))
        * ∑ j ∈ S, ‖a j‖ ^ 2 * ((j : ℝ) ^ (-σ)) ^ 2 := by
  classical
  have hinj : Set.InjOn x Rs := by
    intro r hr s hs hrs
    by_contra hne
    have := hsep r hr s hs hne
    rw [hrs, sub_self, abs_zero] at this
    linarith
  set β' : ℝ → ℝ := fun y => if h : ∃ r ∈ Rs, x r = y then β h.choose else σ with hβ'
  have hβ'x : ∀ r ∈ Rs, β' (x r) = β r := fun r hr => by
    have h : ∃ r' ∈ Rs, x r' = x r := ⟨r, hr, rfl⟩
    simp only [hβ', h, ↓reduceDIte]
    rw [hinj h.choose_spec.1 hr h.choose_spec.2]
  have hR' : ∀ y ∈ Rs.image x, lo + 1 / 2 ≤ y ∧ y ≤ hi - 1 / 2 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
    exact hR r hr
  have hsep' : ∀ y ∈ Rs.image x, ∀ z ∈ Rs.image x, y ≠ z → 1 ≤ |y - z| := by
    intro y hy z hz hyz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hz
    exact hsep r hr s hs fun h => hyz (h ▸ rfl)
  have hβ'' : ∀ y ∈ Rs.image x, σ ≤ β' y ∧ β' y ≤ σ + 1 / 2 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
    rw [hβ'x r hr]; exact hβ r hr
  have h := large_values_off hP hS a hab (Rs.image x) hsep' hR' β' hβ''
  rw [Finset.sum_image hinj] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun r hr => ?_) h
  rw [hβ'x r hr]

end DirMean

#print axioms DirMean.mean_value
#print axioms DirMean.large_values
#print axioms DirMean.large_values_off
#print axioms DirMean.large_values_off'
