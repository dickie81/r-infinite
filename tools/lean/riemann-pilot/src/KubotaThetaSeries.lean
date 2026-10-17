import KubotaThetaGrowth
import KubotaTorus

/-! # θ's Fourier series (round 436)

S5f-10 of round 360's plan, part 19 (S5f-10f, ninth part). Round 435's next step planned θ's Fourier series
`S` with round 434's coefficients: its convergence, continuity and periodicity, and its Fourier coefficients
on `3P`. This round proves them for round 361's theta-type series `thSer c d` with `|d(m)| ≤ C|m|⁵`,
`d(0) = 0` and `d` supported on `δ₃ℤ[ω]`, and then for θ's coefficients:

* **Convergence and continuity** (`thTerm`, a definition; **`exists_norm_thTerm_le`**, **`summable_thTerm`**
  and **`continuousOn_thSer`**, with `thSer_eq`, `pow_five_exp_le`, `summable_rpow_neg_three` and
  `continuousOn_thTerm`): on `{α ≤ v ≤ β}` with `α > 0` the terms are at most `B(1 + |m|)^{−3}` (round 361's
  `bkR_le_exp`), so the series converges absolutely and locally uniformly on upper half-space and is
  continuous there (Mathlib's `continuousOn_tsum`).
* **Periodicity** (**`thSer_add_period`**): the series is periodic under `3ℤ[ω]` (round 428's `ebr_period`).
* **The Fourier coefficients** (**`integral_ebr_thSer`**, with `continuous_thTerm_fst`, `norm_thTerm_eq` and
  `integral_ebr_thTerm`): for `v > 0`, `∫_{3P} ĕ(−σ(δ₃x)z/9)·thSer c d z v dz` is `(9√3/2)·c·v^{2/3}` at
  `x = 0`, plus `(9√3/2)·d(δ₃x)·v·K_{1/3}(4π|δ₃x|v/9)`, by termwise integration (Mathlib's
  `integral_tsum_of_summable_integral_norm`) and round 435's orthogonality.
* **θ's series** (`tauTh` and `thS`, definitions; **`continuousOn_thS`**, **`thS_add_period`**,
  **`integral_ebr_thS`** and **`integral_thS`**, with `tauTh_δ3_mul`, `tauTh_of_not`, `tauTh_zero`,
  `dvd_of_tauTh_ne_zero` and `exists_norm_tauTh_le`): with `τ(δ₃x) = ρ(δ₃x)/(9√3/2)` for `x ≠ 0` and
  `S = thSer (Res φ) τ`, `S` is continuous on upper half-space and periodic, and for every `v > 0` its Fourier
  coefficients are the right sides of round 432's `coef_thetaF_ae` and round 433's `const_thetaF_ae`, which
  give those of `θ̃` at almost every `v`.
-/

open MeasureTheory Set Filter NumberField Complex
open scoped ENNReal Topology

noncomputable section

namespace Eis

/-! ### Theta-type series with polynomially bounded coefficients -/

/-- The `m`-th term `d(m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)` of round 361's `thSer c d`. -/
def thTerm (d : 𝓞 K → ℂ) (m : 𝓞 K) (p : ℂ × ℝ) : ℂ :=
  d m * (p.2 : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * p.2 / 9) * ebr (σO m * p.1 / 9)

theorem thSer_eq (c : ℂ) (d : 𝓞 K → ℂ) (z : ℂ) (v : ℝ) :
    thSer c d z v = c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) + ∑' m, thTerm d m (z, v) := rfl

/-- `t⁵e^{−ct} ≤ (8!·e^c/c⁸)(1 + t)^{−3}` for `t ≥ 0`, `c > 0`. -/
theorem pow_five_exp_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 5 * Real.exp (-(c * t)) ≤ (40320 * Real.exp c / c ^ 8) * (1 + t) ^ (-3 : ℝ) := by
  have h1t : 0 < 1 + t := by linarith
  have hfac : (c * (1 + t)) ^ 8 / 40320 ≤ Real.exp (c * (1 + t)) := by
    have := Real.pow_div_factorial_le_exp (c * (1 + t)) (by positivity) 8
    simpa [Nat.factorial] using this
  have hpow : t ^ 5 ≤ (1 + t) ^ 5 := pow_le_pow_left₀ ht (by linarith) 5
  rw [Real.rpow_neg h1t.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have e3 : (1 + t) ^ (3 : ℝ) = (1 + t) ^ 3 := by norm_cast
  rw [e3]
  have hexp : Real.exp (-(c * t)) = Real.exp c / Real.exp (c * (1 + t)) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [hexp]
  have hE := Real.exp_pos (c * (1 + t))
  rw [div_eq_mul_inv]
  have hc8 : 0 < c ^ 8 := by positivity
  calc t ^ 5 * (Real.exp c * (Real.exp (c * (1 + t)))⁻¹) * (1 + t) ^ 3
      ≤ (1 + t) ^ 5 * (Real.exp c * (Real.exp (c * (1 + t)))⁻¹) * (1 + t) ^ 3 := by
        gcongr
    _ = Real.exp c * ((1 + t) ^ 8 / Real.exp (c * (1 + t))) := by ring
    _ ≤ Real.exp c * (40320 / c ^ 8) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos c).le
        rw [div_le_div_iff₀ hE hc8]
        have : (c * (1 + t)) ^ 8 = c ^ 8 * (1 + t) ^ 8 := by ring
        nlinarith [hfac, this]
    _ = 40320 * Real.exp c / c ^ 8 := by ring

/-- **The terms on a strip**: for coefficients with `|d(m)| ≤ C|m|⁵` and `d(0) = 0`, and `0 < α`, the terms
are at most `B(1 + |m|)^{−3}` on `{α ≤ v ≤ β}`, with `B` independent of `m` and `z`. -/
theorem exists_norm_thTerm_le {d : 𝓞 K → ℂ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ m, ‖d m‖ ≤ C * ‖σO m‖ ^ 5)
    (hd0 : d 0 = 0) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∃ B : ℝ, ∀ m p, α ≤ p.2 → p.2 ≤ β → ‖thTerm d m p‖ ≤ B * (1 + ‖σO m‖) ^ (-3 : ℝ) := by
  set c := 2 * Real.pi * α / 9 with hc_def
  have hc : 0 < c := by positivity
  set B := C * β * (1 / 2) * bkR (1 / 3) (4 * Real.pi * α / 9 / 2) * (40320 * Real.exp c / c ^ 8) with hB
  refine ⟨max B 0, fun m p hp1 hp2 => ?_⟩
  have hbk0 := bkR_nonneg (1 / 3) (4 * Real.pi * α / 9 / 2)
  have hβ : 0 ≤ β := hα.le.trans (hp1.trans hp2)
  by_cases hm : m = 0
  · rw [hm]
    simp only [thTerm, hd0, zero_mul, norm_zero]
    positivity
  have h1 := one_le_norm_σO hm
  have hv : 0 < p.2 := hα.trans_le hp1
  rw [thTerm, norm_mul, norm_mul, norm_mul, norm_ebr, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hv.le]
  have hK := norm_besselK_le (1 / 3 : ℂ) (4 * Real.pi * ‖σO m‖ * p.2 / 9)
  have hre : (1 / 3 : ℂ).re = 1 / 3 := by norm_num
  rw [hre] at hK
  have hx₀ : 0 < 4 * Real.pi * α / 9 := by positivity
  have hxx : 4 * Real.pi * α / 9 ≤ 4 * Real.pi * ‖σO m‖ * p.2 / 9 := by
    have := Real.pi_pos
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    have : α ≤ ‖σO m‖ * p.2 := by nlinarith
    nlinarith
  have hdecay := bkR_le_exp (r := 1 / 3) hx₀ hxx
  have hexp : Real.exp (-(4 * Real.pi * ‖σO m‖ * p.2 / 9 / 2)) ≤ Real.exp (-(c * ‖σO m‖)) := by
    apply Real.exp_le_exp.2
    rw [hc_def]
    have := Real.pi_pos
    have : α * ‖σO m‖ ≤ p.2 * ‖σO m‖ := mul_le_mul_of_nonneg_right hp1 (norm_nonneg _)
    nlinarith
  have hpoly := pow_five_exp_le hc (norm_nonneg (σO m))
  calc ‖d m‖ * p.2 * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * p.2 / 9)‖
      ≤ (C * ‖σO m‖ ^ 5) * β *
          ((1 / 2) * (Real.exp (-(c * ‖σO m‖)) * bkR (1 / 3) (4 * Real.pi * α / 9 / 2))) := by
        gcongr
        · exact hd m
        · exact hK.trans (by gcongr; exact hdecay.trans (by gcongr))
    _ = C * β * (1 / 2) * bkR (1 / 3) (4 * Real.pi * α / 9 / 2) *
          (‖σO m‖ ^ 5 * Real.exp (-(c * ‖σO m‖))) := by ring
    _ ≤ C * β * (1 / 2) * bkR (1 / 3) (4 * Real.pi * α / 9 / 2) *
          ((40320 * Real.exp c / c ^ 8) * (1 + ‖σO m‖) ^ (-3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hpoly
        positivity
    _ = B * (1 + ‖σO m‖) ^ (-3 : ℝ) := by rw [hB]; ring
    _ ≤ max B 0 * (1 + ‖σO m‖) ^ (-3 : ℝ) := by
        gcongr
        exact le_max_left _ _

theorem summable_rpow_neg_three (B : ℝ) : Summable fun m : 𝓞 K => B * (1 + ‖σO m‖) ^ (-3 : ℝ) := by
  have h : Summable fun m : 𝓞 K => (1 + ‖σO m‖) ^ (-3 : ℝ) :=
    summable_O_of_le (fun m => by positivity) (A := 1) fun m => by rw [one_mul]
  exact h.mul_left B

/-- **Absolute convergence** for `v > 0`. -/
theorem summable_thTerm {d : 𝓞 K → ℂ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ m, ‖d m‖ ≤ C * ‖σO m‖ ^ 5)
    (hd0 : d 0 = 0) {p : ℂ × ℝ} (hp : 0 < p.2) : Summable fun m => thTerm d m p := by
  obtain ⟨B, hB⟩ := exists_norm_thTerm_le hC hd hd0 hp p.2
  exact Summable.of_norm_bounded (summable_rpow_neg_three B) fun m => hB m p le_rfl le_rfl

theorem continuousOn_thTerm (d : 𝓞 K → ℂ) (hd0 : d 0 = 0) (m : 𝓞 K) :
    ContinuousOn (thTerm d m) {p : ℂ × ℝ | 0 < p.2} := by
  by_cases hm : m = 0
  · have e : thTerm d m = fun _ => 0 := by
      funext p
      simp [thTerm, hm, hd0]
    rw [e]
    exact continuousOn_const
  intro p hp
  have hp' : 0 < p.2 := hp
  have h1 := one_le_norm_σO hm
  have harg : 0 < 4 * Real.pi * ‖σO m‖ * p.2 / 9 := by positivity
  have hf : ContinuousAt (fun q : ℂ × ℝ => 4 * Real.pi * ‖σO m‖ * q.2 / 9) p := by fun_prop
  have hK : ContinuousAt (fun q : ℂ × ℝ => besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * q.2 / 9)) p :=
    ContinuousAt.comp (g := besselK (1 / 3)) (continuousAt_besselK (1 / 3) harg) hf
  have hE : Continuous fun q : ℂ × ℝ => ebr (σO m * q.1 / 9) := by
    unfold ebr; fun_prop
  refine ContinuousAt.continuousWithinAt ?_
  unfold thTerm
  exact ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd)).mul
    hK).mul hE.continuousAt

/-- **Continuity on upper half-space**. -/
theorem continuousOn_thSer (c : ℂ) {d : 𝓞 K → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ m, ‖d m‖ ≤ C * ‖σO m‖ ^ 5) (hd0 : d 0 = 0) :
    ContinuousOn (fun p : ℂ × ℝ => thSer c d p.1 p.2) {p : ℂ × ℝ | 0 < p.2} := by
  intro p hp
  have hp' : 0 < p.2 := hp
  refine ContinuousAt.continuousWithinAt ?_
  simp only [thSer_eq]
  have hc : ContinuousAt (fun q : ℂ × ℝ => c * ((q.2 ^ (2 / 3 : ℝ) : ℝ) : ℂ)) p := by
    have : ContinuousAt (fun q : ℂ × ℝ => q.2 ^ (2 / 3 : ℝ)) p :=
      (Real.continuousAt_rpow_const _ _ (Or.inl hp'.ne')).comp continuousAt_snd
    exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp this)
  refine hc.add ?_
  set s := {q : ℂ × ℝ | q.2 ∈ Ioo (p.2 / 2) (2 * p.2)} with hs
  have hso : IsOpen s := isOpen_Ioo.preimage continuous_snd
  have hps : p ∈ s := ⟨by linarith, by linarith⟩
  obtain ⟨B, hB⟩ := exists_norm_thTerm_le hC hd hd0 (half_pos hp') (2 * p.2)
  have hcont : ContinuousOn (fun q : ℂ × ℝ => ∑' m, thTerm d m q) s := by
    refine continuousOn_tsum (fun m => (continuousOn_thTerm d hd0 m).mono fun q hq => ?_)
      (summable_rpow_neg_three B) fun m q hq => hB m q hq.1.le hq.2.le
    exact (half_pos hp').trans hq.1
  exact hcont.continuousAt (hso.mem_nhds hps)

/-- **Periodicity under `3ℤ[ω]`**, for coefficients supported on `δ₃ℤ[ω]`. -/
theorem thSer_add_period (c : ℂ) {d : 𝓞 K → ℂ} (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m) (z : ℂ) (u : 𝓞 K)
    (v : ℝ) : thSer c d (z + σO (3 * u)) v = thSer c d z v := by
  simp only [thSer_eq]
  congr 1
  refine tsum_congr fun m => ?_
  by_cases h : d m = 0
  · simp [thTerm, h]
  obtain ⟨x, rfl⟩ := hsupp m h
  simp only [thTerm]
  congr 1
  rw [show σO (δ3 * x) * (z + σO (3 * u)) / 9 = σO (δ3 * x) * z / 9 + σO (δ3 * x) * σO (3 * u) / 9 by ring,
    ebr_add, ebr_period, mul_one]

/-! ### The Fourier coefficients of the series -/

theorem continuous_thTerm_fst (d : 𝓞 K → ℂ) (m : 𝓞 K) (v : ℝ) :
    Continuous fun z : ℂ => thTerm d m (z, v) := by
  have hE : Continuous fun z : ℂ => ebr (σO m * z / 9) := by unfold ebr; fun_prop
  exact continuous_const.mul hE (f := fun _ : ℂ =>
    d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9))

theorem norm_thTerm_eq (d : 𝓞 K → ℂ) (m : 𝓞 K) (z : ℂ) (v : ℝ) :
    ‖thTerm d m (z, v)‖ = ‖d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ := by
  rw [thTerm, norm_mul _ (ebr _), norm_ebr, mul_one]

open Classical in
/-- **One term's coefficient**: for `d` supported on `δ₃ℤ[ω]`, `∫_{3P} ĕ(−σ(δ₃x)z/9)·T_m(z, v) dz` is
`(9√3/2)·d(m)·v·K_{1/3}(4π|m|v/9)` if `m = δ₃x`, and `0` otherwise (round 435's `integral_fundP3_ebr_mul`). -/
theorem integral_ebr_thTerm {d : 𝓞 K → ℂ} (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m) (x m : 𝓞 K) (v : ℝ) :
    ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thTerm d m (z, v) =
      if m = δ3 * x then ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
        (d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)) else 0 := by
  by_cases hd : d m = 0
  · simp [thTerm, hd]
  obtain ⟨x', rfl⟩ := hsupp _ hd
  have e : ∀ z, ebr (-(σO (δ3 * x) / 9 * z)) * thTerm d (δ3 * x') (z, v) =
      (d (δ3 * x') * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x')‖ * v / 9)) *
        (ebr (-(σO (δ3 * x) / 9 * z)) * ebr (σO (δ3 * x') * z / 9)) := by
    intro z; simp only [thTerm]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_fundP3_ebr_mul]
  have hiff : δ3 * x' = δ3 * x ↔ x = x' :=
    ⟨fun h => (mul_left_cancel₀ δ3_ne_zero h).symm, fun h => by rw [h]⟩
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (hiff.2 h1) h2
  · exact absurd (hiff.1 h2) h1
  · ring

open Classical in
/-- **The Fourier coefficients of a theta-type series**: for `d` with `|d(m)| ≤ C|m|⁵`, `d(0) = 0`, supported
on `δ₃ℤ[ω]`, and `v > 0`, `∫_{3P} ĕ(−σ(δ₃x)z/9)·thSer c d z v dz` is `(9√3/2)·c·v^{2/3}` at `x = 0` plus
`(9√3/2)·d(δ₃x)·v·K_{1/3}(4π|δ₃x|v/9)`. -/
theorem integral_ebr_thSer (c : ℂ) {d : 𝓞 K → ℂ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ m, ‖d m‖ ≤ C * ‖σO m‖ ^ 5)
    (hd0 : d 0 = 0) (hsupp : ∀ m, d m ≠ 0 → δ3 ∣ m) (x : 𝓞 K) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thSer c d z v =
      (if x = 0 then ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) else 0) +
        ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
          (d (δ3 * x) * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x)‖ * v / 9)) := by
  have hfin : IsFiniteMeasure (volume.restrict fundP3) :=
    isFiniteMeasure_restrict.2 (by rw [volume_fundP3]; exact ENNReal.ofReal_ne_top)
  obtain ⟨e, he⟩ : ∃ e : ℂ → ℂ, e = fun z => ebr (-(σO (δ3 * x) / 9 * z)) := ⟨_, rfl⟩
  have hec : Continuous e := by rw [he]; unfold ebr; fun_prop
  have hne : ∀ z, ‖e z‖ = 1 := fun z => by rw [he]; exact norm_ebr _
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K → ℝ,
      a = fun m => ‖d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)‖ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ := exists_norm_thTerm_le hC hd hd0 hv v
  have hsa : Summable a := by
    refine Summable.of_nonneg_of_le (fun m => by rw [ha]; exact norm_nonneg _) (fun m => ?_)
      (summable_rpow_neg_three B)
    simp only [ha]
    rw [← norm_thTerm_eq d m 0 v]
    exact hB m (0, v) le_rfl le_rfl
  obtain ⟨F, hF⟩ : ∃ F : 𝓞 K → ℂ → ℂ, F = fun m z => e z * thTerm d m (z, v) := ⟨_, rfl⟩
  have hFn : ∀ m z, ‖F m z‖ = a m := fun m z => by
    rw [hF, ha, norm_mul, hne, one_mul, norm_thTerm_eq]
  have hFc : ∀ m, Continuous (F m) := fun m => by
    rw [hF]; exact hec.mul (continuous_thTerm_fst d m v)
  have hFi : ∀ m, Integrable (F m) (volume.restrict fundP3) := fun m =>
    (integrable_const (a m)).mono' (hFc m).aestronglyMeasurable (ae_of_all _ fun z => (hFn m z).le)
  have hsum : Summable fun m => ∫ z in fundP3, ‖F m z‖ := by
    simp_rw [hFn]
    simp only [integral_const, smul_eq_mul]
    exact hsa.mul_left _
  have hT : Continuous fun z => ∑' m, F m z :=
    continuous_tsum hFc hsa fun m z => (hFn m z).le
  have hTi : Integrable (fun z => ∑' m, F m z) (volume.restrict fundP3) :=
    (integrable_const (∑' m, a m)).mono' hT.aestronglyMeasurable (ae_of_all _ fun z =>
      (norm_tsum_le_tsum_norm (hsa.of_norm_bounded fun m => (hFn m z).le).norm).trans
        (by simp only [hFn]; exact le_rfl))
  have hconst : Integrable (fun z => e z * (c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ))) (volume.restrict fundP3) :=
    (integrable_const ‖c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖).mono'
      (hec.mul continuous_const).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [norm_mul, hne, one_mul])
  have hsplit : ∀ z, e z * thSer c d z v = e z * (c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) + ∑' m, F m z := by
    intro z
    rw [thSer_eq, mul_add, hF]
    congr 1
    exact tsum_mul_left.symm
  have hint : ∫ z in fundP3, e z * thSer c d z v =
      (∫ z in fundP3, e z * (c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ))) + ∫ z in fundP3, ∑' m, F m z :=
    calc ∫ z in fundP3, e z * thSer c d z v
        = ∫ z in fundP3, (e z * (c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) + ∑' m, F m z) :=
          integral_congr_ae (ae_of_all _ hsplit)
      _ = _ := integral_add hconst hTi
  have he0 : ∫ z in fundP3, e z = if x = 0 then ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) else 0 := by
    have h := integral_fundP3_ebr_mul x 0
    simp only [mul_zero, map_zero, zero_mul, zero_div, ebr_zero, mul_one] at h
    rw [he]
    exact h
  have hterms : ∀ m, ∫ z in fundP3, F m z = if m = δ3 * x then ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) *
      (d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9)) else 0 := fun m => by
    rw [hF, he]
    exact integral_ebr_thTerm hsupp x m v
  have hgoal : ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thSer c d z v =
      ∫ z in fundP3, e z * thSer c d z v := by rw [he]
  rw [hgoal, hint, ← integral_tsum_of_summable_integral_norm hFi hsum, integral_mul_const, he0,
    tsum_congr hterms, tsum_eq_single (δ3 * x) fun m hm => by simp [hm]]
  split_ifs <;> simp_all

/-! ### θ's series -/

open Classical in
/-- **θ's coefficients in the index of `thSer`**: `τ(δ₃x) = ρ(δ₃x)/(9√3/2)` for `x ≠ 0`, with round 431's
`rhoM`, and `0` at the other indices. -/
def tauTh (r Y : ℝ) (hY : 0 < Y) (m : 𝓞 K) : ℂ :=
  if h : ∃ x, x ≠ 0 ∧ m = δ3 * x then
    rhoM (Classical.choose h) r Y hY / ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ)
  else 0

theorem tauTh_δ3_mul (r Y : ℝ) (hY : 0 < Y) {x : 𝓞 K} (hx : x ≠ 0) :
    tauTh r Y hY (δ3 * x) = rhoM x r Y hY / ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) := by
  have h : ∃ x', x' ≠ 0 ∧ δ3 * x = δ3 * x' := ⟨x, hx, rfl⟩
  have hc : Classical.choose h = x :=
    (mul_left_cancel₀ δ3_ne_zero (Classical.choose_spec h).2).symm
  rw [tauTh, dite_eq_left h, hc]

theorem tauTh_of_not (r Y : ℝ) (hY : 0 < Y) {m : 𝓞 K} (h : ¬∃ x, x ≠ 0 ∧ m = δ3 * x) :
    tauTh r Y hY m = 0 := by
  rw [tauTh, dite_eq_right h]

theorem tauTh_zero (r Y : ℝ) (hY : 0 < Y) : tauTh r Y hY 0 = 0 :=
  tauTh_of_not r Y hY fun ⟨_, hx, h⟩ => hx ((mul_eq_zero.1 h.symm).resolve_left δ3_ne_zero)

theorem dvd_of_tauTh_ne_zero {r Y : ℝ} {hY : 0 < Y} {m : 𝓞 K} (h : tauTh r Y hY m ≠ 0) : δ3 ∣ m := by
  by_contra hd
  exact h (tauTh_of_not r Y hY fun ⟨x, _, hm⟩ => hd ⟨x, hm⟩)

/-- **`|τ(m)| ≤ C|m|⁵`**, from round 434's `norm_rhoM_le`. -/
theorem exists_norm_tauTh_le {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖tauTh r Y hY m‖ ≤ C * ‖σO m‖ ^ 5 := by
  obtain ⟨C, hC⟩ := norm_rhoM_le hr hY
  have hc9 : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
  refine ⟨max C 0 / (9 * (Real.sqrt 3 / 2)), by positivity, fun m => ?_⟩
  by_cases h : ∃ x, x ≠ 0 ∧ m = δ3 * x
  · obtain ⟨x, hx, rfl⟩ := h
    rw [tauTh_δ3_mul r Y hY hx, norm_div, Complex.norm_real, Real.norm_of_nonneg hc9.le,
      div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc9]
    exact (hC x hx).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
  · rw [tauTh_of_not r Y hY h, norm_zero]
    positivity

/-- **θ's Fourier series**: `S(z, v) = Res φ·v^{2/3} + Σ_m τ(m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)`, round 361's
`thSer` with `Res φ = phiG(4/3)/3` (round 427) and `τ = tauTh`. -/
def thS (r Y : ℝ) (hY : 0 < Y) (p : ℂ × ℝ) : ℂ := thSer (phiG (4 / 3) / 3) (tauTh r Y hY) p.1 p.2

theorem continuousOn_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ContinuousOn (thS r Y hY) {p : ℂ × ℝ | 0 < p.2} := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_tauTh_le hr hY
  exact continuousOn_thSer _ hC0 hC (tauTh_zero r Y hY)

theorem thS_add_period (r Y : ℝ) (hY : 0 < Y) (z : ℂ) (u : 𝓞 K) (v : ℝ) :
    thS r Y hY (z + σO (3 * u), v) = thS r Y hY (z, v) :=
  thSer_add_period _ (fun _ h => dvd_of_tauTh_ne_zero h) z u v

/-- **The series has `θ̃`'s Fourier coefficients**: for `x ≠ 0` and `v > 0`,
`∫_{3P} ĕ(−σ(δ₃x)z/9)·S(z, v) dz = ρ(δ₃x)·v·K_{1/3}(4π|σ(δ₃x)/9|v)`, the right side of round 432's
`coef_thetaF_ae`. -/
theorem integral_ebr_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {x : 𝓞 K} (hx : x ≠ 0) {v : ℝ}
    (hv : 0 < v) :
    ∫ z in fundP3, ebr (-(σO (δ3 * x) / 9 * z)) * thS r Y hY (z, v) =
      rhoM x r Y hY * ((v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_tauTh_le hr hY
  have h := integral_ebr_thSer (phiG (4 / 3) / 3) hC0 hC (tauTh_zero r Y hY)
    (fun _ h => dvd_of_tauTh_ne_zero h) x hv
  have hc9 : ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    exact_mod_cast this.ne'
  have harg : 4 * Real.pi * ‖σO (δ3 * x)‖ * v / 9 = 4 * Real.pi * ‖σO (δ3 * x) / 9‖ * v := by
    rw [norm_div, show ‖(9 : ℂ)‖ = 9 by norm_num]
    ring
  simp only [thS, hx, ite_false, zero_add, tauTh_δ3_mul r Y hY hx, harg] at h ⊢
  rw [h]
  field_simp

/-- **The series has `θ̃`'s constant term**: for `v > 0`, `∫_{3P} S(z, v) dz = (9√3/2)·Res φ·v^{2/3}`, the
right side of round 433's `const_thetaF_ae`. -/
theorem integral_thS {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, thS r Y hY (z, v) =
      ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_tauTh_le hr hY
  have h := integral_ebr_thSer (phiG (4 / 3) / 3) hC0 hC (tauTh_zero r Y hY)
    (fun _ h => dvd_of_tauTh_ne_zero h) 0 hv
  simp only [mul_zero, map_zero, zero_div, zero_mul, neg_zero, ebr_zero, one_mul, ite_true,
    tauTh_zero, add_zero] at h
  simp only [thS]
  rw [h]
  ring

end Eis

end

#print axioms Eis.thSer_eq
#print axioms Eis.pow_five_exp_le
#print axioms Eis.exists_norm_thTerm_le
#print axioms Eis.summable_rpow_neg_three
#print axioms Eis.summable_thTerm
#print axioms Eis.continuousOn_thTerm
#print axioms Eis.continuousOn_thSer
#print axioms Eis.thSer_add_period
#print axioms Eis.continuous_thTerm_fst
#print axioms Eis.norm_thTerm_eq
#print axioms Eis.integral_ebr_thTerm
#print axioms Eis.integral_ebr_thSer
#print axioms Eis.tauTh_δ3_mul
#print axioms Eis.tauTh_of_not
#print axioms Eis.tauTh_zero
#print axioms Eis.dvd_of_tauTh_ne_zero
#print axioms Eis.exists_norm_tauTh_le
#print axioms Eis.continuousOn_thS
#print axioms Eis.thS_add_period
#print axioms Eis.integral_ebr_thS
#print axioms Eis.integral_thS
