import Mathlib

/-! # Poisson summation in the plane (round 293)

S4 of the round-291 plan begins with Poisson summation over the lattice `ℤ[ω] ⊂ ℂ`. Mathlib has
Poisson summation on `ℝ` (`Real.tsum_eq_tsum_fourier`) and Fourier series on tori
(`UnitAddTorus`). This file proves the two-dimensional formula for Schwartz functions on `ℂ`, and
transfers it to every linear image of `ℤ²`. It is general analysis; the `ℤ[ω]` specialisation is next.

* **Decay** (`schwartz_decay'`, `summable_lattice_inv`): `(1 + |z|)³·|F(z)| ≤ C`, and
  `Σ_{n∈ℤ²} (1 + |n|)^{−3} < ∞`.
* **The periodization** (`per`, `perT`): `Σ_{n∈ℤ²} F(x + n)` converges locally uniformly
  (`locally_summable`), is `ℤ²`-periodic (`per_add`), and descends to a continuous function on the torus
  `𝕋² = (ℝ/ℤ)²` through the open quotient map `qT` (`qT_isOpenQuotientMap`, `perT_qT`).
* **Unfolding** (`integral_eq_tsum_box`): `∫_{ℝ²} g = Σ_{n∈ℤ²} ∫_{(0,1]²} g(x + n)`, from Mathlib's
  fundamental domain of the lattice `ℤ²` (`ZSpan.isAddFundamentalDomain`).
* **The Fourier coefficients** (`mFourierCoeff_perT`): the `k`-th coefficient of the periodization is
  `𝓕F(k)`.
* **`pair_poisson`**: `Σ_{n∈ℤ²} F(n₀ + n₁i) = Σ_{k∈ℤ²} 𝓕F(k₀ + k₁i)`, by evaluating the Fourier series at
  `0` (Mathlib's `hasSum_mFourier_series_apply_of_summable`).
* **`fourier_comp_linearEquiv`**: `𝓕(f ∘ M)(w) = |det M|⁻¹·𝓕f((M⁻¹)* w)` for a linear automorphism `M` of
  a finite-dimensional real inner product space (Mathlib has the isometric case).
* **`lattice_poisson`**: for an `ℝ`-linear automorphism `M` of `ℂ`,
  `Σ_{n∈ℤ²} F(Mn) = |det M|⁻¹·Σ_{k∈ℤ²} 𝓕F((M⁻¹)* k)`.
-/

open Complex MeasureTheory UnitAddTorus
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace PlanePoisson

section Decay

/-- The point `x₀ + x₁ i` of `ℂ`. -/
def cpt (x : Fin 2 → ℝ) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * I

theorem cpt_eq (x : Fin 2 → ℝ) : cpt x = measurableEquivPi.symm x := rfl

theorem cpt_add (x y : Fin 2 → ℝ) : cpt (x + y) = cpt x + cpt y := by
  simp [cpt]; ring

theorem prod_le_sq_cpt (x : Fin 2 → ℝ) :
    (1 + |x 0|) * (1 + |x 1|) ≤ (1 + ‖cpt x‖) ^ 2 := by
  have h0 : |x 0| ≤ ‖cpt x‖ := by
    have := Complex.abs_re_le_norm (cpt x); simpa [cpt] using this
  have h1 : |x 1| ≤ ‖cpt x‖ := by
    have := Complex.abs_im_le_norm (cpt x); simpa [cpt] using this
  rw [sq]
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

theorem summable_one_add_abs_rpow {b : ℝ} (hb : 1 < b) :
    Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ (-b) := by
  apply Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hb)
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpos : 0 < |(m : ℝ)| := abs_pos.2 hm0
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)

/-- `Σ_{n ∈ ℤ²} (1 + |n|)^{−3} < ∞`. -/
theorem summable_lattice_decay :
    Summable fun n : Fin 2 → ℤ => (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-3 : ℝ) := by
  have h1 := summable_one_add_abs_rpow (b := 3 / 2) (by norm_num)
  have h2 := Summable.mul_of_nonneg h1 h1 (fun _ => by positivity) (fun _ => by positivity)
  have h3 : Summable fun n : Fin 2 → ℤ =>
      (1 + |((n 0 : ℤ) : ℝ)|) ^ (-(3 / 2 : ℝ)) * (1 + |((n 1 : ℤ) : ℝ)|) ^ (-(3 / 2 : ℝ)) :=
    (finTwoArrowEquiv ℤ).summable_iff.2 h2
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) h3
  set x : Fin 2 → ℝ := fun i => (n i : ℝ)
  have hx := prod_le_sq_cpt x
  have hA : 0 < 1 + |x 0| := by positivity
  have hB : 0 < 1 + |x 1| := by positivity
  have hN : 0 < 1 + ‖cpt x‖ := by positivity
  rw [← Real.mul_rpow hA.le hB.le]
  calc (1 + ‖cpt x‖) ^ (-3 : ℝ) = ((1 + ‖cpt x‖) ^ (2 : ℝ)) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_mul hN.le]; norm_num
    _ ≤ ((1 + |x 0|) * (1 + |x 1|)) ^ (-(3 / 2 : ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
        rw [Real.rpow_two]; exact hx

/-- Schwartz functions on `ℂ` decay like `(1 + |z|)^{−3}`. -/
theorem schwartz_decay (F : SchwartzMap ℂ ℂ) :
    ∃ C, 0 ≤ C ∧ ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ (-3 : ℝ) := by
  set C := 2 ^ 3 * (Finset.Iic ((3 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨C, by positivity, fun z => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) (k := 3) (n := 0)
    le_rfl le_rfl F z
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < 1 + ‖z‖ := by positivity
  have h' : (1 + ‖z‖) ^ 3 * ‖F z‖ ≤ C := by simpa [C] using h
  rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [mul_comm]; exact_mod_cast h'

end Decay

section Periodization

/-- Integer points of `ℝ²`. -/
def nR (n : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (n i : ℝ)

theorem nR_add (m n : Fin 2 → ℤ) : nR (m + n) = nR m + nR n := by
  ext i; simp [nR]

theorem cpt_continuous : Continuous cpt := by unfold cpt; fun_prop

/-- Schwartz decay in polynomial form: `(1 + |z|)³·|F(z)| ≤ C`. -/
theorem schwartz_decay' (F : SchwartzMap ℂ ℂ) : ∃ C, 0 ≤ C ∧ ∀ z, (1 + ‖z‖) ^ 3 * ‖F z‖ ≤ C := by
  refine ⟨2 ^ 3 * (Finset.Iic ((3 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F, by positivity, fun z => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) (k := 3) (n := 0)
    le_rfl le_rfl F z
  rw [norm_iteratedFDeriv_zero] at h
  simpa using h

theorem summable_lattice_inv :
    Summable fun n : Fin 2 → ℤ => 1 / (1 + ‖cpt (nR n)‖) ^ 3 := by
  refine summable_lattice_decay.congr fun n => ?_
  have hpos : 0 < 1 + ‖cpt (nR n)‖ := by positivity
  show (1 + ‖cpt (nR n)‖) ^ (-3 : ℝ) = _
  rw [Real.rpow_neg hpos.le, one_div, ← Real.rpow_natCast]; norm_num

variable (F : SchwartzMap ℂ ℂ)

/-- `x ↦ F(x₀ + x₁ i)` on `ℝ²`. -/
def fC : C(Fin 2 → ℝ, ℂ) := ⟨fun x => F (cpt x), F.continuous.comp cpt_continuous⟩

theorem shift_bound {C R : ℝ} (hC : ∀ z, (1 + ‖z‖) ^ 3 * ‖F z‖ ≤ C) (hR : 0 ≤ R)
    {x : Fin 2 → ℝ} (hx : ‖cpt x‖ ≤ R) (n : Fin 2 → ℤ) :
    ‖F (cpt (x + nR n))‖ ≤ (1 + R) ^ 3 * C * (1 / (1 + ‖cpt (nR n)‖) ^ 3) := by
  set a := 1 + ‖cpt (x + nR n)‖
  set b := 1 + ‖cpt (nR n)‖
  have ha : 1 ≤ a := by simp [a]
  have hb : 0 < b := by positivity
  have hab : b ≤ a * (1 + R) := by
    have : ‖cpt (nR n)‖ ≤ ‖cpt (x + nR n)‖ + ‖cpt x‖ := by
      rw [cpt_add]
      calc ‖cpt (nR n)‖ = ‖(cpt x + cpt (nR n)) - cpt x‖ := by ring_nf
        _ ≤ ‖cpt x + cpt (nR n)‖ + ‖cpt x‖ := norm_sub_le _ _
    simp only [a, b]; nlinarith [norm_nonneg (cpt (x + nR n))]
  have h3 : b ^ 3 ≤ a ^ 3 * (1 + R) ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hb.le hab 3
  have hFa := hC (cpt (x + nR n))
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  calc ‖F (cpt (x + nR n))‖ * b ^ 3 ≤ ‖F (cpt (x + nR n))‖ * (a ^ 3 * (1 + R) ^ 3) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = (1 + R) ^ 3 * (a ^ 3 * ‖F (cpt (x + nR n))‖) := by ring
    _ ≤ (1 + R) ^ 3 * C := mul_le_mul_of_nonneg_left hFa (by positivity)

theorem locally_summable :
    ∀ K : TopologicalSpace.Compacts (Fin 2 → ℝ),
      Summable fun n : Fin 2 → ℤ => ‖((fC F).comp (ContinuousMap.addRight (nR n))).restrict K‖ := by
  intro K
  obtain ⟨C, hC0, hC⟩ := schwartz_decay' F
  obtain ⟨R, hR⟩ := (K.isCompact.image cpt_continuous).isBounded.exists_norm_le
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_lattice_inv.mul_left ((1 + max R 0) ^ 3 * C))
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro x
  simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    fC, ContinuousMap.coe_mk]
  exact shift_bound F hC hR0 ((hR _ ⟨x, x.2, rfl⟩).trans (le_max_left _ _)) n

/-- The periodization `Σ_{n∈ℤ²} F(x + n)`. -/
def per : C(Fin 2 → ℝ, ℂ) := ∑' n : Fin 2 → ℤ, (fC F).comp (ContinuousMap.addRight (nR n))

theorem per_apply (x : Fin 2 → ℝ) : per F x = ∑' n : Fin 2 → ℤ, F (cpt (x + nR n)) := by
  rw [per, ← ContinuousMap.tsum_apply
    (ContinuousMap.summable_of_locally_summable_norm (locally_summable F))]
  rfl

theorem per_add (x : Fin 2 → ℝ) (m : Fin 2 → ℤ) : per F (x + nR m) = per F x := by
  rw [per_apply, per_apply]
  conv_rhs => rw [← (Equiv.addLeft m).tsum_eq]
  congr 1; ext n
  simp only [Equiv.coe_addLeft, nR_add, add_assoc]

end Periodization

section Torus

/-- The quotient map `ℝ² → 𝕋²`. -/
def qT : (Fin 2 → ℝ) → UnitAddTorus (Fin 2) :=
  Pi.map fun _ => (QuotientAddGroup.mk : ℝ → UnitAddCircle)

theorem qT_isOpenQuotientMap : IsOpenQuotientMap qT :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem qT_eq_iff {x y : Fin 2 → ℝ} (h : qT y = qT x) : ∃ m : Fin 2 → ℤ, y = x + nR m := by
  have : ∀ i, ∃ k : ℤ, y i = x i + k := by
    intro i
    have hi := congrFun h i
    simp only [qT, Pi.map_apply] at hi
    rw [QuotientAddGroup.eq] at hi
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hi
    refine ⟨-k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    push_cast; linarith
  choose m hm using this
  exact ⟨m, funext fun i => by simp [nR, hm i]⟩

variable (F : SchwartzMap ℂ ℂ)

/-- The periodization, on the torus. -/
def perT : C(UnitAddTorus (Fin 2), ℂ) :=
  ⟨fun t => per F (Function.surjInv qT_isOpenQuotientMap.surjective t), by
    rw [← qT_isOpenQuotientMap.continuous_comp_iff]
    have : (fun t => per F (Function.surjInv qT_isOpenQuotientMap.surjective t)) ∘ qT =
        per F := by
      funext x
      simp only [Function.comp_apply]
      obtain ⟨m, hm⟩ := qT_eq_iff (Function.surjInv_eq qT_isOpenQuotientMap.surjective (qT x))
      rw [hm, per_add]
    rw [this]; exact (per F).continuous⟩

theorem perT_qT (x : Fin 2 → ℝ) : perT F (qT x) = per F x := by
  show per F (Function.surjInv qT_isOpenQuotientMap.surjective (qT x)) = per F x
  obtain ⟨m, hm⟩ := qT_eq_iff (Function.surjInv_eq qT_isOpenQuotientMap.surjective (qT x))
  rw [hm, per_add]

end Torus

section Unfolding

/-- The integer lattice `ℤ²` as the `ℤ`-span of the standard basis. -/
abbrev Lat : Submodule ℤ (Fin 2 → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))

theorem nR_mem (n : Fin 2 → ℤ) : nR n ∈ Lat := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨n, ?_⟩
  ext i
  fin_cases i <;> simp [nR, Fin.sum_univ_two]

def latEquiv : (Fin 2 → ℤ) ≃ Lat where
  toFun n := ⟨nR n, nR_mem n⟩
  invFun γ := fun i => ⌊(γ : Fin 2 → ℝ) i⌋
  left_inv n := by ext i; simp [nR]
  right_inv γ := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 γ.2
    apply Subtype.ext
    ext i
    have hγ : (γ : Fin 2 → ℝ) i = c i := by
      rw [← hc]; fin_cases i <;> simp [Fin.sum_univ_two]
    simp [nR, hγ]

instance : VAddInvariantMeasure Lat (Fin 2 → ℝ) volume :=
  ⟨fun γ s _ => by
    simp only [Submodule.vadd_def, vadd_eq_add]
    exact measure_preimage_add volume (γ : Fin 2 → ℝ) s⟩

theorem box_ae_eq :
    (Set.pi Set.univ fun _ : Fin 2 => Set.Ico (0 : ℝ) 1) =ᵐ[volume]
      (Set.pi Set.univ fun _ : Fin 2 => Set.Ioc (0 : ℝ) 1) :=
  (Measure.univ_pi_Ico_ae_eq_Icc).trans (Measure.univ_pi_Ioc_ae_eq_Icc).symm

/-- **Unfolding over the unit box**: `∫_{ℝ²} g = Σ_{n∈ℤ²} ∫_{(0,1]²} g(x + n)`. -/
theorem integral_eq_tsum_box (g : (Fin 2 → ℝ) → ℂ) (hg : Integrable g) :
    ∫ y, g y = ∑' n : Fin 2 → ℤ,
      ∫ x in Set.pi Set.univ (fun _ : Fin 2 => Set.Ioc (0 : ℝ) 1), g (x + nR n) := by
  have h := ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin 2)) volume
  rw [h.integral_eq_tsum' g hg, ZSpan.fundamentalDomain_pi_basisFun]
  rw [← ((Equiv.neg (Fin 2 → ℤ)).trans latEquiv).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [setIntegral_congr_set box_ae_eq]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun x _ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, latEquiv, Equiv.coe_fn_mk, Submodule.vadd_def,
    vadd_eq_add]
  congr 1
  ext i; simp [nR]; ring

end Unfolding

section Coefficients

/-- The box `(0, 1]²`. -/
abbrev box : Set (Fin 2 → ℝ) := Set.pi Set.univ fun _ : Fin 2 => Set.Ioc (0 : ℝ) 1

theorem qT_add (x : Fin 2 → ℝ) (n : Fin 2 → ℤ) : qT (x + nR n) = qT x := by
  funext i
  simp only [qT, Pi.map_apply, Pi.add_apply, nR]
  rw [QuotientAddGroup.eq]
  exact ⟨-n i, by simp⟩

/-- `x ↦ e(−k·x)` on `ℝ²`. -/
def ek (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) : ℂ := mFourier (-k) (qT x)

theorem ek_add (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) (n : Fin 2 → ℤ) : ek k (x + nR n) = ek k x := by
  rw [ek, ek, qT_add]

theorem norm_ek (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) : ‖ek k x‖ = 1 := by
  unfold ek mFourier
  simp [Fin.prod_univ_two, fourier_apply]

theorem ek_continuous (k : Fin 2 → ℤ) : Continuous (ek k) :=
  (mFourier (-k)).continuous.comp qT_isOpenQuotientMap.continuous

theorem ek_eq (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    ek k x = Complex.exp (↑(-2 * Real.pi * ⟪cpt x, cpt (nR k)⟫) * Complex.I) := by
  unfold ek mFourier qT
  simp only [ContinuousMap.coe_mk, Pi.map_apply, Fin.prod_univ_two, Pi.neg_apply]
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  simp [Complex.inner, cpt, nR]
  ring

theorem box_volume_lt_top : volume box < ⊤ := by
  calc volume box ≤ volume (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
        measure_mono (Set.pi_mono fun _ _ => Set.Ioc_subset_Icc_self)
    _ < ⊤ := (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top

theorem norm_cpt_le_of_mem_box {x : Fin 2 → ℝ} (hx : x ∈ box) : ‖cpt x‖ ≤ 2 := by
  have h0 := hx 0 (Set.mem_univ _)
  have h1 := hx 1 (Set.mem_univ _)
  calc ‖cpt x‖ ≤ ‖(x 0 : ℂ)‖ + ‖(x 1 : ℂ) * I‖ := norm_add_le _ _
    _ = |x 0| + |x 1| := by simp
    _ ≤ 2 := by
      rw [abs_of_pos h0.1, abs_of_pos h1.1]; linarith [h0.2, h1.2]

variable (F : SchwartzMap ℂ ℂ)

/-- **The Fourier coefficients of the periodization are the values of `𝓕F` on `ℤ²`.** -/
theorem mFourierCoeff_perT (k : Fin 2 → ℤ) :
    mFourierCoeff (perT F) k = 𝓕 (F : ℂ → ℂ) (cpt (nR k)) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_decay' F
  rw [mFourierCoeff_eq_integral (perT F) k 0]
  have hset : {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)} =
      box := by ext x; simp [Set.mem_pi]
  rw [hset]
  have hint : ∀ x : Fin 2 → ℝ, mFourier (-k) (fun i => (x i : UnitAddCircle)) •
      perT F (fun i => (x i : UnitAddCircle)) =
      ∑' n : Fin 2 → ℤ, ek k (x + nR n) * F (cpt (x + nR n)) := by
    intro x
    have hq : (fun i => (x i : UnitAddCircle)) = qT x := rfl
    rw [hq, perT_qT, per_apply, smul_eq_mul, ← tsum_mul_left]
    congr 1; ext n; rw [ek_add]; rfl
  simp_rw [hint]
  -- swap the sum and the integral over the box
  set G : (Fin 2 → ℝ) → ℂ := fun y => ek k y * F (cpt y)
  have hGc : Continuous G := (ek_continuous k).mul (F.continuous.comp cpt_continuous)
  have hbound : ∀ n : Fin 2 → ℤ, ∀ x ∈ box,
      ‖G (x + nR n)‖ ≤ (1 + 2) ^ 3 * C * (1 / (1 + ‖cpt (nR n)‖) ^ 3) := by
    intro n x hx
    simp only [G, norm_mul, norm_ek, one_mul]
    exact shift_bound F hC (by norm_num) (norm_cpt_le_of_mem_box hx) n
  have hmeas : MeasurableSet box := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hint_n : ∀ n : Fin 2 → ℤ, Integrable (fun x => G (x + nR n)) (volume.restrict box) := by
    intro n
    refine IntegrableOn.of_bound box_volume_lt_top
      ((hGc.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      ((1 + 2) ^ 3 * C * (1 / (1 + ‖cpt (nR n)‖) ^ 3)) ?_
    exact ae_restrict_of_forall_mem hmeas (hbound n)
  have hsum : Summable fun n : Fin 2 → ℤ => ∫ x in box, ‖G (x + nR n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_)
      ((summable_lattice_inv.mul_left ((1 + 2) ^ 3 * C)).mul_left (volume box).toReal)
    have := norm_setIntegral_le_of_norm_le_const box_volume_lt_top
      (f := fun x => ‖G (x + nR n)‖) (fun x hx => by
        rw [norm_norm]; exact hbound n x hx)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), measureReal_def] at this
    linarith [this]
  rw [← integral_tsum_of_summable_integral_norm hint_n hsum]
  -- unfold over the box
  have hFint : Integrable (fun y : Fin 2 → ℝ => F (cpt y)) := by
    have h := (Complex.volume_preserving_equiv_pi.symm).integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _) (g := (F : ℂ → ℂ))
    exact h.2 F.integrable
  have hGint : Integrable G := by
    refine hFint.mono hGc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    simp [G, norm_ek]
  rw [← integral_eq_tsum_box G hGint]
  -- change of variables `ℝ² → ℂ`
  rw [Real.fourier_eq']
  have hcv := (Complex.volume_preserving_equiv_pi.symm).integral_comp'
    (g := fun v : ℂ => Complex.exp (↑(-2 * Real.pi * ⟪v, cpt (nR k)⟫) * Complex.I) • F v)
  rw [← hcv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [G, ek_eq, smul_eq_mul]
  rfl

/-- **Poisson summation over `ℤ²`** for Schwartz functions on `ℂ`:
`Σ_{n∈ℤ²} F(n₀ + n₁ i) = Σ_{k∈ℤ²} 𝓕F(k₀ + k₁ i)`. -/
theorem pair_poisson :
    ∑' n : Fin 2 → ℤ, F (cpt (nR n)) = ∑' k : Fin 2 → ℤ, 𝓕 (F : ℂ → ℂ) (cpt (nR k)) := by
  have hsum : Summable (mFourierCoeff (perT F)) := by
    obtain ⟨C, hC0, hC⟩ := schwartz_decay' (𝓕 F)
    refine Summable.of_norm_bounded (summable_lattice_inv.mul_left C) fun k => ?_
    rw [mFourierCoeff_perT, ← SchwartzMap.fourier_coe]
    have h := hC (cpt (nR k))
    have hpos : 0 < (1 + ‖cpt (nR k)‖) ^ 3 := by positivity
    rw [mul_one_div, le_div_iff₀ hpos, mul_comm]; exact h
  have h := (hasSum_mFourier_series_apply_of_summable hsum 0).tsum_eq
  have h0 : (0 : UnitAddTorus (Fin 2)) = qT 0 := by funext i; simp [qT]
  rw [h0, perT_qT, per_apply] at h
  simp only [zero_add] at h
  rw [← h]
  refine tsum_congr fun k => ?_
  rw [mFourierCoeff_perT, smul_eq_mul]
  have hm : mFourier k (qT 0) = 1 := by
    simp [mFourier, qT, Fin.prod_univ_two]
  rw [hm, mul_one]

end Coefficients

section ChangeOfVariables

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The Fourier transform under a linear change of variables**:
`𝓕(f ∘ M)(w) = |det M|⁻¹ · 𝓕f((M⁻¹)* w)`. -/
theorem fourier_comp_linearEquiv (M : V ≃ₗ[ℝ] V) (f : V → E) (w : V) :
    𝓕 (f ∘ M) w = |(LinearMap.det (M : V →ₗ[ℝ] V))⁻¹| •
      𝓕 f (LinearMap.adjoint (M.symm : V →ₗ[ℝ] V) w) := by
  have hdet : LinearMap.det (M : V →ₗ[ℝ] V) ≠ 0 := (LinearEquiv.isUnit_det' M).ne_zero
  rw [Real.fourier_eq, Real.fourier_eq]
  set g : V → E := fun u => 𝐞 (-⟪M.symm u, w⟫) • f u
  have h1 : (fun v => 𝐞 (-⟪v, w⟫) • (f ∘ M) v) = fun v => g (M v) := by
    funext v; simp [g]
  rw [h1]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure V)) hdet
  let Me : V ≃ᵐ V := M.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hMe : (Me : V → V) = (M : V →ₗ[ℝ] V) := rfl
  have h2 : ∫ v, g (M v) = ∫ u, g u ∂(Measure.map (M : V →ₗ[ℝ] V) volume) := by
    rw [← hMe, integral_map_equiv Me g]
    rfl
  rw [h2, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [g]
  congr 2
  rw [LinearMap.adjoint_inner_right]
  rfl

end ChangeOfVariables

section Lattice

/-- **Poisson summation over a linear image of `ℤ²`**: for an `ℝ`-linear automorphism `M` of `ℂ`,
`Σ_{n∈ℤ²} F(M n) = |det M|⁻¹ Σ_{k∈ℤ²} 𝓕F((M⁻¹)* k)`. -/
theorem lattice_poisson (F : SchwartzMap ℂ ℂ) (M : ℂ ≃ₗ[ℝ] ℂ) :
    ∑' n : Fin 2 → ℤ, F (M (cpt (nR n))) =
      |(LinearMap.det (M : ℂ →ₗ[ℝ] ℂ))⁻¹| *
        ∑' k : Fin 2 → ℤ, 𝓕 (F : ℂ → ℂ) (LinearMap.adjoint (M.symm : ℂ →ₗ[ℝ] ℂ) (cpt (nR k))) := by
  set G : SchwartzMap ℂ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ M.toContinuousLinearEquiv F
  have hG : ∀ z, G z = F (M z) := fun z => rfl
  have h := pair_poisson G
  simp only [hG] at h
  rw [h, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hGf : (G : ℂ → ℂ) = (F : ℂ → ℂ) ∘ M := rfl
  rw [hGf, fourier_comp_linearEquiv, Complex.real_smul]

end Lattice

end PlanePoisson

end

#print axioms PlanePoisson.schwartz_decay'
#print axioms PlanePoisson.summable_lattice_inv
#print axioms PlanePoisson.locally_summable
#print axioms PlanePoisson.per_add
#print axioms PlanePoisson.qT_isOpenQuotientMap
#print axioms PlanePoisson.perT_qT
#print axioms PlanePoisson.integral_eq_tsum_box
#print axioms PlanePoisson.mFourierCoeff_perT
#print axioms PlanePoisson.pair_poisson
#print axioms PlanePoisson.fourier_comp_linearEquiv
#print axioms PlanePoisson.lattice_poisson
