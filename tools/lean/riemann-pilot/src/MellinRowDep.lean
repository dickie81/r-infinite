import MellinUniform

/-! # Weights that depend on the row (round 340)

S5d of round 312's plan, part 2: the analysis that the companion paper's proof of its Lemma 6.6 uses to
bound its prepared sums, independent of its Lemma 6.5 and of its theta transformation.

* **Weights that depend on the row** (`rowDep_meanSquare`, `rowDep_meanSquare'`): if every row `r` carries a
  smooth compactly supported weight `g_r` in the logarithmic variable with `∫|g_r| ≤ B` and `∫|g_r''| ≤ B`, and
  the twisted sums satisfy `Σ_r |Σ_n a_{r,n} x_n^{2πit}|² ≤ M` for every real `t`, then
  `Σ_r |Σ_n a_{r,n} g_r(log x_n)|² ≤ B²M`. The Mellin coefficient of `g_r` is `𝓕g_r`, bounded by the common
  majorant `2B/(1 + (2πt)²)` of mass `B` (`norm_fourier_le_of_L1`, `integral_majorant`); weighted
  Cauchy–Schwarz over `t` (round 302's `sq_integral_mul_le`) then sums the rows. This is the companion paper's
  (B.6) with its Lemma B.1 in logarithmic coordinates.
* **A smooth dyadic partition** (`dyadicBump`): `V(y) = φ(y) − φ(2y)` with `φ = 1` on `(−∞, 1]` and `0` on
  `[2, ∞)` (Mathlib's `Real.smoothTransition`). It is smooth, `0 ≤ V ≤ 1` on `[0, ∞)`, supported in
  `[1/2, 2]`, and `Σ_{j ≥ 0} V(y/2^j) = 1` for `y ≥ 1` (`sum_dyadicBump`, `hasSum_dyadicBump`).
* **The separated weights** (`logWeight`, `logWeight_deriv_le`, `integral_logWeight_le`):
  `v ↦ V(e^v)h(v + log R)`. If the first `q` derivatives of `h` are bounded by `N(1 + e^w)^{−A}`, those of the
  weight are bounded by `C·N(1 + R)^{−A}`, and so are their integrals, with `C` depending only on `A` and `q`.
* **Series over finitely many rows** (`sum_norm_tsum_sq_le`): Minkowski's inequality in `ℓ²` of the rows for
  a series of row vectors, and weighted Cauchy–Schwarz for finite sums (`norm_sum_mul_sq_le`).
-/

open Complex MeasureTheory Set
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section

namespace MellinSep

/-- The derivatives of a smooth compactly supported function are integrable. -/
theorem integrable_iteratedDeriv_of_compact {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (n : ℕ) : Integrable (iteratedDeriv n g) := by
  refine (hg.continuous_iteratedDeriv n (nat_le_infty n)).integrable_of_hasCompactSupport ?_
  have : iteratedDeriv n g = (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ =>
      L (fun _ => 1)) ∘ iteratedFDeriv ℝ n g := by
    funext x; simp [iteratedDeriv_eq_iteratedFDeriv]
  rw [this]
  exact (hgc.iteratedFDeriv n).comp_left (by simp)

/-- **The Mellin coefficient of a weight in logarithmic coordinates has a majorant of mass `B`**: if
`∫|g| ≤ B` and `∫|g''| ≤ B`, then `|𝓕g(t)| ≤ 2B/(1 + (2πt)²)`. -/
theorem norm_fourier_le_of_L1 {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {B : ℝ} (h0 : ∫ v, ‖g v‖ ≤ B) (h2 : ∫ v, ‖iteratedDeriv 2 g v‖ ≤ B) (t : ℝ) :
    ‖𝓕 g t‖ ≤ 2 * B * (1 + (2 * Real.pi * t) ^ 2)⁻¹ := by
  have hint := integrable_iteratedDeriv_of_compact hg hgc
  have e0 : ‖𝓕 g t‖ ≤ B :=
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans h0
  have e2 : (2 * Real.pi * t) ^ 2 * ‖𝓕 g t‖ ≤ B := by
    have e := congrFun (Real.fourier_iteratedDeriv (N := ((2 : ℕ) : ℕ∞))
      (hg.of_le (by exact_mod_cast le_top)) (fun n _ => hint n) le_rfl) t
    have hn : ‖𝓕 (iteratedDeriv 2 g) t‖ ≤ ∫ v, ‖iteratedDeriv 2 g v‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    rw [e, norm_smul, norm_pow] at hn
    have h2' : ‖(2 * ↑Real.pi * I * (t : ℂ))‖ = |2 * Real.pi * t| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
      ring
    rw [h2', sq_abs] at hn
    exact hn.trans h2
  have hpos : (0 : ℝ) < 1 + (2 * Real.pi * t) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith [norm_nonneg (𝓕 g t)]

/-- `∫ 2B/(1 + (2πt)²) dt = B`. -/
theorem integral_majorant (B : ℝ) : ∫ t : ℝ, 2 * B * (1 + (2 * Real.pi * t) ^ 2)⁻¹ = B := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have e : ∫ t : ℝ, (1 + (2 * Real.pi * t) ^ 2)⁻¹ = |(2 * Real.pi)⁻¹| * Real.pi := by
    have := Measure.integral_comp_mul_left (fun u : ℝ => (1 + u ^ 2)⁻¹) (2 * Real.pi)
    rw [this, integral_univ_inv_one_add_sq, smul_eq_mul]
  rw [integral_const_mul, e, abs_of_pos (inv_pos.2 hpi)]
  field_simp

theorem integrable_majorant (B : ℝ) :
    Integrable fun t : ℝ => 2 * B * (1 + (2 * Real.pi * t) ^ 2)⁻¹ := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  exact ((integrable_inv_one_add_sq.comp_mul_left' hpi).const_mul (2 * B))

/-- **Weights that depend on the row** (the companion paper's (B.6), weighted Cauchy–Schwarz with a
common majorant, after its Lemma B.1 in logarithmic coordinates). Let each row `r` carry a smooth
compactly supported weight `g r` in the logarithmic variable with `∫|g_r| ≤ B` and `∫|g_r''| ≤ B`. If for
every real `t` the twisted sums satisfy `Σ_r |Σ_n a_{r,n} x_n^{2πit}|² ≤ M`, then
`Σ_r |Σ_n a_{r,n} g_r(log x_n)|² ≤ B²·M`. -/
theorem rowDep_meanSquare {ι κ : Type*} (T : Finset ι) (C : Finset κ) (g : ι → ℝ → ℂ)
    (hg : ∀ r, ContDiff ℝ ∞ (g r)) (hgc : ∀ r, HasCompactSupport (g r)) {B : ℝ}
    (h0 : ∀ r, ∫ v, ‖g r v‖ ≤ B) (h2 : ∀ r, ∫ v, ‖iteratedDeriv 2 (g r) v‖ ≤ B)
    (a : ι → κ → ℂ) (x : κ → ℝ) (hx : ∀ n ∈ C, 0 < x n) {M : ℝ}
    (hM : ∀ t : ℝ, ∑ r ∈ T, ‖∑ n ∈ C, a r n * ((x n : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I))‖ ^ 2
      ≤ M) :
    ∑ r ∈ T, ‖∑ n ∈ C, a r n * g r (Real.log (x n))‖ ^ 2 ≤ B ^ 2 * M := by
  set m : ℝ → ℝ := fun t => 2 * B * (1 + (2 * Real.pi * t) ^ 2)⁻¹ with hm
  set e : ℝ → ℂ := fun t => ((2 * Real.pi * t : ℝ) : ℂ) * I with he
  set S : ι → ℝ → ℂ := fun r t => ∑ n ∈ C, a r n * ((x n : ℂ) ^ e t) with hS
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun r _ => by positivity) (hM 0)
  rcases T.eq_empty_or_nonempty with hT | ⟨r0, hr0⟩
  · rw [hT, Finset.sum_empty]; positivity
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun v => norm_nonneg _) (h0 r0)
  have hm0 : ∀ t, 0 ≤ m t := fun t => by simp only [hm]; positivity
  have hmi : Integrable m := integrable_majorant B
  have hmint : ∫ t, m t = B := integral_majorant B
  -- the Schwartz functions and their coefficients
  set gs : ι → 𝓢(ℝ, ℂ) := fun r => (hgc r).toSchwartzMap (hg r) with hgs
  have hgs_apply : ∀ r v, gs r v = g r v := fun r v => rfl
  have hc : ∀ r t, ‖𝓕 (gs r : ℝ → ℂ) t‖ ≤ m t := fun r t =>
    norm_fourier_le_of_L1 (hg r) (hgc r) (h0 r) (h2 r) t
  have hcont_e : ∀ n ∈ C, Continuous fun t => (x n : ℂ) ^ e t := fun n hn =>
    continuous_tI.const_cpow (Or.inl (by exact_mod_cast (hx n hn).ne'))
  have hnorm_e : ∀ n ∈ C, ∀ t, ‖(x n : ℂ) ^ e t‖ = 1 := fun n hn t =>
    norm_cpow_tI (x n) t (hx n hn)
  have hScont : ∀ r, Continuous (S r) := fun r =>
    continuous_finsetSum _ fun n hn => continuous_const.mul (hcont_e n hn)
  have hSb : ∀ r t, ‖S r t‖ ≤ ∑ n ∈ C, ‖a r n‖ := fun r t => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul, hnorm_e n hn t, mul_one]
  -- the row sums as Mellin integrals
  have hrep : ∀ r, ∑ n ∈ C, a r n * g r (Real.log (x n)) =
      ∫ t, 𝓕 (gs r : ℝ → ℂ) t * S r t := by
    intro r
    have hint : ∀ n ∈ C, Integrable fun t => a r n * (𝓕 (gs r : ℝ → ℂ) t * (x n : ℂ) ^ e t) := by
      intro n hn
      refine ((𝓕 (gs r)).integrable.mul_bdd (c := 1) (hcont_e n hn).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => (hnorm_e n hn t).le)).const_mul (a r n) |>.congr ?_
      refine Filter.Eventually.of_forall fun t => ?_
      simp only [SchwartzMap.fourier_coe]
    have h1 : ∀ n ∈ C, a r n * g r (Real.log (x n)) =
        ∫ t, a r n * (𝓕 (gs r : ℝ → ℂ) t * (x n : ℂ) ^ e t) := by
      intro n hn
      rw [← hgs_apply, log_fourier_inversion (gs r) (x n) (hx n hn), integral_const_mul]
    rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hS]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  -- integrability of the weighted row sums
  have hmS : ∀ r, Integrable fun t => m t * ‖S r t‖ := fun r =>
    hmi.mul_bdd (c := ∑ n ∈ C, ‖a r n‖) (hScont r).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_norm]; exact hSb r t)
  have hmS2 : ∀ r, Integrable fun t => m t * ‖S r t‖ ^ 2 := fun r =>
    hmi.mul_bdd (c := (∑ n ∈ C, ‖a r n‖) ^ 2) ((hScont r).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hSb r t) 2)
  have hcS : ∀ r, Integrable fun t => ‖𝓕 (gs r : ℝ → ℂ) t‖ * ‖S r t‖ := fun r =>
    (𝓕 (gs r)).integrable.norm.mul_bdd (c := ∑ n ∈ C, ‖a r n‖)
      (hScont r).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_norm]; exact hSb r t) |>.congr
      (Filter.Eventually.of_forall fun t => by simp only [SchwartzMap.fourier_coe])
  -- one row: `|∫ c_r S_r|² ≤ B·∫ m|S_r|²`
  have hrow : ∀ r, ‖∫ t, 𝓕 (gs r : ℝ → ℂ) t * S r t‖ ^ 2 ≤ B * ∫ t, m t * ‖S r t‖ ^ 2 := by
    intro r
    have e1 : ‖∫ t, 𝓕 (gs r : ℝ → ℂ) t * S r t‖ ≤ ∫ t, m t * ‖S r t‖ := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) (hmS r)
        (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc r t) (norm_nonneg _)
    calc ‖∫ t, 𝓕 (gs r : ℝ → ℂ) t * S r t‖ ^ 2 ≤ (∫ t, m t * ‖S r t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) e1 2
      _ ≤ (∫ t, m t) * ∫ t, m t * ‖S r t‖ ^ 2 := sq_integral_mul_le hm0 hmi (hmS r) (hmS2 r)
      _ = B * ∫ t, m t * ‖S r t‖ ^ 2 := by rw [hmint]
  calc ∑ r ∈ T, ‖∑ n ∈ C, a r n * g r (Real.log (x n))‖ ^ 2
      = ∑ r ∈ T, ‖∫ t, 𝓕 (gs r : ℝ → ℂ) t * S r t‖ ^ 2 :=
        Finset.sum_congr rfl fun r _ => by rw [hrep r]
    _ ≤ ∑ r ∈ T, B * ∫ t, m t * ‖S r t‖ ^ 2 := Finset.sum_le_sum fun r _ => hrow r
    _ = B * ∫ t, ∑ r ∈ T, m t * ‖S r t‖ ^ 2 := by
        rw [← Finset.mul_sum, integral_finsetSum _ fun r _ => hmS2 r]
    _ ≤ B * ∫ t, m t * M := by
        refine mul_le_mul_of_nonneg_left (integral_mono (integrable_finsetSum _ fun r _ => hmS2 r)
          (hmi.mul_const M) fun t => ?_) hB0
        simp only
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hM t) (hm0 t)
    _ = B ^ 2 * M := by rw [integral_mul_const, hmint]; ring

open Classical in
/-- `rowDep_meanSquare` with the hypotheses on the weights only for the rows in `T`. -/
theorem rowDep_meanSquare' {ι κ : Type*} (T : Finset ι) (C : Finset κ) (g : ι → ℝ → ℂ)
    (hg : ∀ r ∈ T, ContDiff ℝ ∞ (g r)) (hgc : ∀ r ∈ T, HasCompactSupport (g r)) {B : ℝ}
    (h0 : ∀ r ∈ T, ∫ v, ‖g r v‖ ≤ B) (h2 : ∀ r ∈ T, ∫ v, ‖iteratedDeriv 2 (g r) v‖ ≤ B)
    (a : ι → κ → ℂ) (x : κ → ℝ) (hx : ∀ n ∈ C, 0 < x n) {M : ℝ}
    (hM : ∀ t : ℝ, ∑ r ∈ T, ‖∑ n ∈ C, a r n * ((x n : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I))‖ ^ 2
      ≤ M) :
    ∑ r ∈ T, ‖∑ n ∈ C, a r n * g r (Real.log (x n))‖ ^ 2 ≤ B ^ 2 * M := by
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun r _ => by positivity) (hM 0)
  rcases T.eq_empty_or_nonempty with hT | ⟨r0, hr0⟩
  · rw [hT, Finset.sum_empty]; positivity
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun v => norm_nonneg _) (h0 r0 hr0)
  set g' : ι → ℝ → ℂ := fun r => if r ∈ T then g r else 0 with hg'
  have e : ∀ r ∈ T, g' r = g r := fun r hr => by simp only [hg', ite_eq_left hr]
  have key := rowDep_meanSquare T C g'
    (fun r => by by_cases hr : r ∈ T
                 · rw [e r hr]; exact hg r hr
                 · simp only [hg', ite_eq_right hr]; exact contDiff_const)
    (fun r => by by_cases hr : r ∈ T
                 · rw [e r hr]; exact hgc r hr
                 · simp only [hg', ite_eq_right hr]; exact HasCompactSupport.zero)
    (fun r => by by_cases hr : r ∈ T
                 · rw [e r hr]; exact h0 r hr
                 · simp only [hg', ite_eq_right hr]; simpa using hB0)
    (fun r => by by_cases hr : r ∈ T
                 · rw [e r hr]; exact h2 r hr
                 · simp only [hg', ite_eq_right hr]
                   simpa using hB0)
    a x hx hM
  refine le_trans (le_of_eq ?_) key
  exact Finset.sum_congr rfl fun r hr => by rw [e r hr]

/-! ### A smooth dyadic partition of unity -/

/-- `φ(x) = 1` for `x ≤ 1` and `φ(x) = 0` for `x ≥ 2`. -/
def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2 - x)

theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)

theorem cutoff_of_le_one {x : ℝ} (hx : x ≤ 1) : cutoff x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_of_two_le {x : ℝ} (hx : 2 ≤ x) : cutoff x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- **The dyadic bump** `V(y) = φ(y) − φ(2y)`, supported in `[1/2, 2]`. -/
def dyadicBump (y : ℝ) : ℝ := cutoff y - cutoff (2 * y)

theorem dyadicBump_contDiff : ContDiff ℝ ∞ dyadicBump :=
  cutoff_contDiff.sub (cutoff_contDiff.comp (contDiff_const.mul contDiff_id))

theorem dyadicBump_eq_zero {y : ℝ} (hy : y ≤ 1 / 2 ∨ 2 ≤ y) : dyadicBump y = 0 := by
  unfold dyadicBump
  rcases hy with hy | hy
  · rw [cutoff_of_le_one (by linarith), cutoff_of_le_one (by linarith)]; ring
  · rw [cutoff_of_two_le hy, cutoff_of_two_le (by linarith)]; ring

theorem abs_dyadicBump_le (y : ℝ) : |dyadicBump y| ≤ 1 := by
  unfold dyadicBump cutoff
  have h1 := Real.smoothTransition.nonneg (2 - y)
  have h2 := Real.smoothTransition.le_one (2 - y)
  have h3 := Real.smoothTransition.nonneg (2 - 2 * y)
  have h4 := Real.smoothTransition.le_one (2 - 2 * y)
  rw [abs_le]; constructor <;> linarith

theorem cutoff_antitone : Antitone cutoff := fun x y hxy =>
  Real.smoothTransition.monotone (by linarith : 2 - y ≤ 2 - x)

theorem dyadicBump_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ dyadicBump y := by
  unfold dyadicBump
  have := cutoff_antitone (by linarith : y ≤ 2 * y)
  linarith

/-- **The dyadic pieces sum to one**: `Σ_{j ≤ J} V(y/2^j) = 1` for `1 ≤ y ≤ 2^J`. -/
theorem sum_dyadicBump {y : ℝ} (hy : 1 ≤ y) {J : ℕ} (hJ : y ≤ 2 ^ J) :
    ∑ j ∈ Finset.range (J + 1), dyadicBump (y / 2 ^ j) = 1 := by
  have tel : ∀ K : ℕ, ∑ j ∈ Finset.range (K + 1), dyadicBump (y / 2 ^ j) =
      cutoff (y / 2 ^ K) - cutoff (2 * y) := by
    intro K
    induction K with
    | zero => simp [dyadicBump]
    | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold dyadicBump
      have : 2 * (y / 2 ^ (K + 1)) = y / 2 ^ K := by rw [pow_succ]; field_simp
      rw [this]; ring
  rw [tel, cutoff_of_le_one, cutoff_of_two_le (by linarith)]
  · ring
  · rw [div_le_one (by positivity)]; exact hJ

/-- The `j`-th piece vanishes unless `2^{j−1} < y < 2^{j+1}`. -/
theorem dyadicBump_div_eq_zero {y : ℝ} {j : ℕ} (hy : y ≤ 2 ^ j / 2 ∨ 2 * 2 ^ j ≤ y) :
    dyadicBump (y / 2 ^ j) = 0 := by
  apply dyadicBump_eq_zero
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rcases hy with hy | hy
  · left; rw [div_le_iff₀ h2]; linarith
  · right; rw [le_div_iff₀ h2]; linarith

/-- **The dyadic partition as a series**: `Σ_{j ≥ 0} V(y/2^j) = 1` for `y ≥ 1`. -/
theorem hasSum_dyadicBump {y : ℝ} (hy : 1 ≤ y) : HasSum (fun j : ℕ => dyadicBump (y / 2 ^ j)) 1 := by
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt y (by norm_num : (1 : ℝ) < 2)
  rw [← sum_dyadicBump hy hJ.le]
  refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
  rw [Finset.mem_range, not_lt] at hj
  apply dyadicBump_div_eq_zero
  left
  have h1 : (2 : ℝ) ^ (J + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  rw [pow_succ] at h1
  linarith

/-! ### The separated weights -/

/-- The weight of the Mellin separation in `N(n)/U`, in logarithmic coordinates:
`v ↦ V(e^v)·h(v + c)`. -/
def logWeight (h : ℝ → ℂ) (c : ℝ) (v : ℝ) : ℂ := (dyadicBump (Real.exp v) : ℂ) * h (v + c)

theorem bumpExp_contDiff : ContDiff ℝ ∞ fun v : ℝ => (dyadicBump (Real.exp v) : ℂ) :=
  ofRealCLM.contDiff.comp (dyadicBump_contDiff.comp Real.contDiff_exp)

theorem bumpExp_eq_zero {v : ℝ} (hv : v ∉ Icc (-Real.log 2) (Real.log 2)) :
    (dyadicBump (Real.exp v) : ℂ) = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hv
  rw [dyadicBump_eq_zero, Complex.ofReal_zero]
  rcases hv with hv | hv
  · left
    have := Real.exp_lt_exp.2 hv
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
    linarith
  · right
    have := Real.exp_lt_exp.2 hv
    rw [Real.exp_log (by norm_num)] at this
    linarith

theorem bumpExp_hasCompactSupport :
    HasCompactSupport fun v : ℝ => (dyadicBump (Real.exp v) : ℂ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -Real.log 2) (b := Real.log 2))
    fun _ hv => bumpExp_eq_zero hv

theorem logWeight_contDiff {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (c : ℝ) :
    ContDiff ℝ ∞ (logWeight h c) :=
  bumpExp_contDiff.mul (hh.comp (contDiff_id.add contDiff_const))

theorem logWeight_hasCompactSupport (h : ℝ → ℂ) (c : ℝ) : HasCompactSupport (logWeight h c) :=
  bumpExp_hasCompactSupport.mul_right

theorem logWeight_eq_zero (h : ℝ → ℂ) (c : ℝ) {v : ℝ} (hv : v ∉ Icc (-Real.log 2) (Real.log 2)) :
    logWeight h c v = 0 := by
  unfold logWeight; rw [bumpExp_eq_zero hv, zero_mul]

/-- `(1 + R e^v)^{−A} ≤ 2^A (1 + R)^{−A}` for `|v| ≤ log 2`. -/
theorem one_add_mul_exp_rpow_le {A : ℝ} (hA : 0 ≤ A) {R : ℝ} (hR : 0 ≤ R) {v : ℝ}
    (hv : -Real.log 2 ≤ v) : (1 + R * Real.exp v) ^ (-A) ≤ 2 ^ A * (1 + R) ^ (-A) := by
  have he : 1 / 2 ≤ Real.exp v := by
    have := Real.exp_le_exp.2 hv
    rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at this
  have h1 : (1 + R) / 2 ≤ 1 + R * Real.exp v := by nlinarith
  have hpos : 0 < (1 + R) / 2 := by positivity
  calc (1 + R * Real.exp v) ^ (-A) ≤ ((1 + R) / 2) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos hpos h1 (by linarith)
    _ = 2 ^ A * (1 + R) ^ (-A) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          div_eq_mul_inv, inv_inv]
        ring

/-- **The separated weights decay with the scale**: if the first `q` derivatives of `h` are bounded
by `N(1 + e^w)^{−A}`, then those of `v ↦ V(e^v)h(v + log R)` are bounded by `C·N(1 + R)^{−A}` with
`C` depending only on `A` and `q`. -/
theorem logWeight_deriv_le (q : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → ∀ N : ℝ,
      (∀ i ≤ q, ∀ w, ‖iteratedDeriv i h w‖ ≤ N * (1 + Real.exp w) ^ (-A)) →
      ∀ R : ℝ, 0 < R → ∀ j ≤ q, ∀ v,
        ‖iteratedDeriv j (logWeight h (Real.log R)) v‖ ≤ C * N * (1 + R) ^ (-A) := by
  obtain ⟨Kψ, hKψ0, hKψ⟩ := bumpExp_hasCompactSupport.exists_bound_iteratedFDeriv bumpExp_contDiff q
  refine ⟨2 ^ q * Kψ * 2 ^ A, by positivity, fun h hh N hN R hR j hj v => ?_⟩
  have hN0 : 0 ≤ N := by
    have := (norm_nonneg _).trans (hN 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  by_cases hv : v ∈ Icc (-Real.log 2) (Real.log 2)
  · rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hshift : ContDiff ℝ ∞ fun v => h (v + Real.log R) :=
      hh.comp (contDiff_id.add contDiff_const)
    have hlw : logWeight h (Real.log R) =
        fun v => (dyadicBump (Real.exp v) : ℂ) * h (v + Real.log R) := rfl
    rw [hlw]
    refine (norm_iteratedFDeriv_mul_le bumpExp_contDiff hshift v (nat_le_infty j)).trans ?_
    have hdecay : ∀ i ≤ q, ‖iteratedFDeriv ℝ i (fun v => h (v + Real.log R)) v‖ ≤
        N * (2 ^ A * (1 + R) ^ (-A)) := by
      intro i hi
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_comp_add_const]
      refine (hN i hi _).trans (mul_le_mul_of_nonneg_left ?_ hN0)
      rw [Real.exp_add, Real.exp_log hR, mul_comm]
      exact one_add_mul_exp_rpow_le hA hR.le hv.1
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun v => (dyadicBump (Real.exp v) : ℂ)) v‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun v => h (v + Real.log R)) v‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Kψ * (N * (2 ^ A * (1 + R) ^ (-A))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          gcongr
          · exact hKψ i (hi'.trans hj) v
          · exact hdecay (j - i) (by omega)
      _ = (2 : ℝ) ^ j * Kψ * (N * (2 ^ A * (1 + R) ^ (-A))) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ q * Kψ * 2 ^ A * N * (1 + R) ^ (-A) := by
          have : (2 : ℝ) ^ j ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hj
          have : 0 ≤ Kψ * (N * (2 ^ A * (1 + R) ^ (-A))) := by positivity
          nlinarith
  · have hev : logWeight h (Real.log R) =ᶠ[nhds v] fun _ => (0 : ℂ) := by
      have hopen : IsOpen (Icc (-Real.log 2) (Real.log 2))ᶜ := isClosed_Icc.isOpen_compl
      exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hv) fun w hw =>
        logWeight_eq_zero h _ hw
    rw [iteratedDeriv_eq_iteratedFDeriv, (hev.iteratedFDeriv ℝ j).eq_of_nhds,
      iteratedFDeriv_fun_zero]
    refine le_trans (le_of_eq ?_) (by positivity : (0 : ℝ) ≤ 2 ^ q * Kψ * 2 ^ A * N * (1 + R) ^ (-A))
    simp

/-- **The `L¹` norms of the separated weights**: `∫|g^{(j)}| ≤ 2 log 2 · C·N(1 + R)^{−A}`. -/
theorem integral_logWeight_le (q : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → ∀ N : ℝ,
      (∀ i ≤ q, ∀ w, ‖iteratedDeriv i h w‖ ≤ N * (1 + Real.exp w) ^ (-A)) →
      ∀ R : ℝ, 0 < R → ∀ j ≤ q,
        ∫ v, ‖iteratedDeriv j (logWeight h (Real.log R)) v‖ ≤ C * N * (1 + R) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := logWeight_deriv_le q hA
  refine ⟨2 * Real.log 2 * C, by positivity, fun h hh N hN R hR j hj => ?_⟩
  set g := logWeight h (Real.log R) with hg
  have hgd : ContDiff ℝ ∞ g := logWeight_contDiff hh _
  have hzero : ∀ v ∉ Icc (-Real.log 2) (Real.log 2), ‖iteratedDeriv j g v‖ = 0 := by
    intro v hv
    have hev : g =ᶠ[nhds v] fun _ => (0 : ℂ) := by
      have hopen : IsOpen (Icc (-Real.log 2) (Real.log 2))ᶜ := isClosed_Icc.isOpen_compl
      exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hv) fun w hw =>
        logWeight_eq_zero h _ hw
    rw [iteratedDeriv_eq_iteratedFDeriv, (hev.iteratedFDeriv ℝ j).eq_of_nhds,
      iteratedFDeriv_fun_zero]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc ∫ v in Icc (-Real.log 2) (Real.log 2), ‖iteratedDeriv j g v‖
      ≤ ∫ _v in Icc (-Real.log 2) (Real.log 2), C * N * (1 + R) ^ (-A) := by
        refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Icc
          fun v _ => hC h hh N hN R hR j hj v
        exact (hgd.continuous_iteratedDeriv j (nat_le_infty j)).norm.integrableOn_Icc
    _ = 2 * Real.log 2 * C * N * (1 + R) ^ (-A) := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring

/-! ### The `ℓ²` triangle inequality for series over finitely many rows -/

/-- **Minkowski over a series**: if `Σ_{r ∈ T} |F_i(r)|² ≤ b_i²` with `Σ b_i < ∞`, then every row
series converges and `Σ_{r ∈ T} |Σ_i F_i(r)|² ≤ (Σ_i b_i)²`. -/
theorem sum_norm_tsum_sq_le {ι ρ : Type*} (T : Finset ρ) (F : ι → ρ → ℂ) (b : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Summable b) (hF : ∀ i, ∑ r ∈ T, ‖F i r‖ ^ 2 ≤ b i ^ 2) :
    (∀ r ∈ T, Summable fun i => F i r) ∧
      ∑ r ∈ T, ‖∑' i, F i r‖ ^ 2 ≤ (∑' i, b i) ^ 2 := by
  have hle : ∀ i, ∀ r ∈ T, ‖F i r‖ ≤ b i := by
    intro i r hr
    have h1 : ‖F i r‖ ^ 2 ≤ b i ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun r => ‖F i r‖ ^ 2) (fun _ _ => by positivity) hr)
        (hF i)
    nlinarith [norm_nonneg (F i r), hb0 i]
  have hsr : ∀ r ∈ T, Summable fun i => F i r := fun r hr =>
    Summable.of_norm_bounded hb fun i => hle i r hr
  refine ⟨hsr, ?_⟩
  -- the rows as vectors of `ℓ²(T)`
  set G : ι → EuclideanSpace ℂ T := fun i => WithLp.toLp 2 fun r : T => F i r with hG
  have hGn : ∀ i, ‖G i‖ ≤ b i := by
    intro i
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.2 ⟨hb0 i, ?_⟩
    calc ∑ r : T, ‖G i r‖ ^ 2 = ∑ r ∈ T, ‖F i r‖ ^ 2 := by
          rw [← Finset.sum_coe_sort T]
      _ ≤ b i ^ 2 := hF i
  have hGs : Summable fun i => ‖G i‖ := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hGn hb
  have hGs' : Summable G := hGs.of_norm
  have happ : ∀ r : T, (∑' i, G i) r = ∑' i, F i r := by
    intro r
    have := (PiLp.proj 2 (fun _ : T => ℂ) (𝕜 := ℂ) r).map_tsum hGs'
    simpa [hG] using this
  have hnorm : ‖∑' i, G i‖ ≤ ∑' i, b i :=
    (norm_tsum_le_tsum_norm hGs).trans (hGs.tsum_le_tsum hGn hb)
  calc ∑ r ∈ T, ‖∑' i, F i r‖ ^ 2 = ∑ r : T, ‖(∑' i, G i) r‖ ^ 2 := by
        rw [← Finset.sum_coe_sort T]
        exact Finset.sum_congr rfl fun r _ => by rw [happ r]
    _ = ‖∑' i, G i‖ ^ 2 := (EuclideanSpace.norm_sq_eq _).symm
    _ ≤ (∑' i, b i) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- **Weighted Cauchy–Schwarz for finite sums**: `|Σ w_i x_i|² ≤ (Σ w_i)·Σ w_i|x_i|²` for `w ≥ 0`. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (x : ι → ℂ) :
    ‖∑ i ∈ s, (w i : ℂ) * x i‖ ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖x i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, (w i : ℂ) * x i‖ ≤ ∑ i ∈ s, w i * ‖x i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  have h2 : (∑ i ∈ s, w i * ‖x i‖) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖x i‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
      (fun i => Real.sqrt (w i) * ‖x i‖)
    have e1 : ∀ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * ‖x i‖) = w i * ‖x i‖ := fun i hi => by
      rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
    have e2 : ∀ i ∈ s, Real.sqrt (w i) ^ 2 = w i := fun i hi => Real.sq_sqrt (hw i hi)
    have e3 : ∀ i ∈ s, (Real.sqrt (w i) * ‖x i‖) ^ 2 = w i * ‖x i‖ ^ 2 := fun i hi => by
      rw [mul_pow, Real.sq_sqrt (hw i hi)]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at this
    exact this
  calc ‖∑ i ∈ s, (w i : ℂ) * x i‖ ^ 2 ≤ (∑ i ∈ s, w i * ‖x i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end MellinSep

end

#print axioms MellinSep.rowDep_meanSquare
#print axioms MellinSep.rowDep_meanSquare'
#print axioms MellinSep.hasSum_dyadicBump
#print axioms MellinSep.integral_logWeight_le
#print axioms MellinSep.sum_norm_tsum_sq_le
#print axioms MellinSep.norm_sum_mul_sq_le
