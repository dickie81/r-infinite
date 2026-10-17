import Mathlib
import KaiserDeriv

/-! # The tail of the Kaiser trial (round 163, part 7)

`SH x = Σ_{n≥1} H(nx)` and its termwise derivative `SHd x = Σ n H′(nx)`.

* `hasDerivAt_SH`: `SH′ = SHd` on `(0, ∞)` (dominated by the global Cauchy bound);
* `norm_SH_tail`, `norm_SHd_tail`: for `x ≥ L ≥ 1`, `|SH x| ≤ 4P x^{−4}` and `|SHd x| ≤ 2P D₀ x^{−3}`,
  with `P = (πη)^{−8}` and `D₀ = 6 + 2β² + 32πη` — polynomial in `L`, no `e^{βL}`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

variable {L η α : ℝ}

/-- `SHd x = Σ n H′(nx)`. -/
def SHd (L η α : ℝ) (x : ℝ) : ℂ := ∑' n : ℕ, ((n : ℂ) + 1) * kHd L η α ((n + 1) * x)

theorem hasDerivAt_Hr (L η α : ℝ) (y : ℝ) : HasDerivAt (Hr L η α) (kHd L η α y) y :=
  (hasDerivAt_kH L η α y).comp_ofReal

theorem hasDerivAt_Hr_scaled (L η α : ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Hr L η α ((n + 1) * y)) (((n : ℂ) + 1) * kHd L η α ((n + 1) * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1) * y) ((n : ℝ) + 1) y := by
    simpa using (hasDerivAt_id y).const_mul ((n : ℝ) + 1)
  have := (hasDerivAt_Hr L η α ((n + 1) * y)).scomp y h1
  convert this using 1
  · rfl
  · rw [Complex.real_smul]; push_cast; ring

/-- The global derivative constant. -/
def kG (L η α : ℝ) : ℝ := 64 * kA2 L η α * Real.exp (2 * π * L)

theorem kG_nonneg (L η α : ℝ) : 0 ≤ kG L η α := by
  unfold kG; have := kA2_nonneg L η α; positivity

theorem norm_term_d_le (hp : Par L η) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) {y : ℝ} (hy : δ < y) :
    ‖((n : ℂ) + 1) * kHd L η α ((n + 1) * y)‖ ≤ kG L η α * δ⁻¹ ^ 4 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hy0 : 0 < y := hδ.trans hy
  have hb := norm_kHd_glob hp.pos hp.small hp.big ((n + 1) * y) (α := α)
  have hG := kG_nonneg L η α
  rw [norm_mul, show ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn]]
  have hyn : δ * ((n : ℝ) + 1) ≤ (n + 1) * y := by nlinarith
  have hq : (δ * ((n : ℝ) + 1)) ^ 4 ≤ (1 + ((n + 1) * y) ^ 2) ^ 2 := by
    have h1 : (δ * ((n : ℝ) + 1)) ^ 2 ≤ ((n + 1) * y) ^ 2 := by gcongr
    calc (δ * ((n : ℝ) + 1)) ^ 4 = ((δ * ((n : ℝ) + 1)) ^ 2) ^ 2 := by ring
      _ ≤ (1 + ((n + 1) * y) ^ 2) ^ 2 := by gcongr; linarith
  calc ((n : ℝ) + 1) * ‖kHd L η α ((n + 1) * y)‖
      ≤ ((n : ℝ) + 1) * (kG L η α / (1 + ((n + 1) * y) ^ 2) ^ 2) := by
        gcongr; simpa [kG] using hb
    _ ≤ ((n : ℝ) + 1) * (kG L η α / (δ * ((n : ℝ) + 1)) ^ 4) := by
        gcongr
    _ = kG L η α * δ⁻¹ ^ 4 * (((n : ℝ) + 1)⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹) := by
        field_simp
    _ ≤ kG L η α * δ⁻¹ ^ 4 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
        have h1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
        have h2 : 0 ≤ ((n : ℝ) + 1)⁻¹ ^ 2 := by positivity
        have h3 : 0 ≤ kG L η α * δ⁻¹ ^ 4 := by positivity
        calc kG L η α * δ⁻¹ ^ 4 * (((n : ℝ) + 1)⁻¹ ^ 2 * ((n : ℝ) + 1)⁻¹)
            ≤ kG L η α * δ⁻¹ ^ 4 * (((n : ℝ) + 1)⁻¹ ^ 2 * 1) := by gcongr
          _ = _ := by ring

/-- **Termwise differentiation.** -/
theorem hasDerivAt_SH (hp : Par L η) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Sf (Hr L η α)) (SHd L η α x) x := by
  set δ := x / 2
  have hδ : 0 < δ := by positivity
  exact hasDerivAt_tsum_of_isPreconnected (summable_inv_sq_succ.mul_left (kG L η α * δ⁻¹ ^ 4))
    isOpen_Ioi isPreconnected_Ioi (fun n y _ => hasDerivAt_Hr_scaled L η α n y)
    (fun n y hy => norm_term_d_le hp hδ n hy) (y₀ := x) (by simp only [δ, mem_Ioi]; linarith)
    (summable_Hr_nat' hp hx) (by simp only [δ, mem_Ioi]; linarith)

theorem continuousOn_SHd (hp : Par L η) : ContinuousOn (SHd L η α) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀ : (0 : ℝ) < x₀ := hx₀
  set δ := x₀ / 2
  have hδ : 0 < δ := by positivity
  have hcont : ∀ n : ℕ, Continuous (fun y : ℝ => ((n : ℂ) + 1) * kHd L η α ((n + 1) * y)) := fun n => by
    have := continuous_kHd L η α; fun_prop
  have hc : ContinuousOn (fun y : ℝ => ∑' n : ℕ, ((n : ℂ) + 1) * kHd L η α ((n + 1) * y)) (Ioi δ) :=
    continuousOn_tsum (fun n => (hcont n).continuousOn)
      (summable_inv_sq_succ.mul_left (kG L η α * δ⁻¹ ^ 4)) fun n y hy => norm_term_d_le hp hδ n hy
  exact (hc.continuousAt (Ioi_mem_nhds (by simp only [δ]; linarith))).continuousWithinAt


/-! ## Sharp tail bounds for `SH`, `SHd` -/

def kP (η : ℝ) : ℝ := (1 / (π * η)) ^ 8
def kD0 (L η : ℝ) : ℝ := 6 + 2 * (2 * π * (L - 4 * η)) ^ 2 + 32 * π * η

theorem kP_pos (hη : 0 < η) : 0 < kP η := by unfold kP; have := pi_pos; positivity
theorem kD0_nonneg (hη : 0 < η) : 0 ≤ kD0 L η := by unfold kD0; have := pi_pos; positivity

/-- Standing hypotheses for the tail. -/
structure Tail (L η α : ℝ) : Prop where
  par : Par L η
  alpha : |α| ≤ 1
  one : 1 ≤ L

theorem inv_succ_pow_le (n : ℕ) (k : ℕ) (hk : 2 ≤ k) : ((n : ℝ) + 1)⁻¹ ^ k ≤ ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have h0 : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have h1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  exact pow_le_pow_of_le_one h0 h1 hk

theorem norm_Hr_scaled_tail (ht : Tail L η α) {x : ℝ} (hx : L ≤ x) (n : ℕ) :
    ‖Hr L η α ((n + 1) * x)‖ ≤ 2 * kP η * x⁻¹ ^ 4 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hx1 : 1 ≤ x := ht.one.trans hx
  set y := ((n : ℝ) + 1) * x
  have hy : x ≤ y := by nlinarith
  have hy1 : 1 ≤ y := hx1.trans hy
  have hη := ht.par.pos
  have hpey : 0 < π * η * y := by have := pi_pos; positivity
  have hb := norm_Hr_tail (L := L) ht.alpha (by nlinarith) (by nlinarith [ht.one]) hpey.ne' (α := α)
  rw [abs_of_pos hpey] at hb
  have e : 2 * y ^ 4 * (1 / (π * η * y)) ^ 8 = 2 * kP η * y⁻¹ ^ 4 := by unfold kP; field_simp
  have hxy : y⁻¹ ^ 4 = x⁻¹ ^ 4 * ((n : ℝ) + 1)⁻¹ ^ 4 := by simp only [y]; rw [mul_inv, mul_pow]; ring
  have hP := (kP_pos hη).le
  calc ‖Hr L η α y‖ ≤ 2 * y ^ 4 * (1 / (π * η * y)) ^ 8 := hb
    _ = 2 * kP η * x⁻¹ ^ 4 * ((n : ℝ) + 1)⁻¹ ^ 4 := by rw [e, hxy]; ring
    _ ≤ 2 * kP η * x⁻¹ ^ 4 * ((n : ℝ) + 1)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left (inv_succ_pow_le n 4 (by norm_num)) (by positivity)

theorem norm_SH_tail (ht : Tail L η α) {x : ℝ} (hx : L ≤ x) :
    ‖Sf (Hr L η α) x‖ ≤ 4 * kP η * x⁻¹ ^ 4 := by
  have hs := summable_inv_sq_succ.mul_left (2 * kP η * x⁻¹ ^ 4)
  calc ‖Sf (Hr L η α) x‖ ≤ ∑' n : ℕ, 2 * kP η * x⁻¹ ^ 4 * ((n : ℝ) + 1)⁻¹ ^ 2 :=
        tsum_of_norm_bounded hs.hasSum (norm_Hr_scaled_tail ht hx)
    _ = 2 * kP η * x⁻¹ ^ 4 * ∑' n : ℕ, ((n : ℝ) + 1)⁻¹ ^ 2 := tsum_mul_left
    _ ≤ 2 * kP η * x⁻¹ ^ 4 * 2 := by
        have := (kP_pos ht.par.pos).le
        gcongr; exact tsum_inv_sq_succ_le
    _ = 4 * kP η * x⁻¹ ^ 4 := by ring

theorem norm_termd_tail (ht : Tail L η α) {x : ℝ} (hx : L < x) (n : ℕ) :
    ‖((n : ℂ) + 1) * kHd L η α ((n + 1) * x)‖ ≤ kP η * kD0 L η * x⁻¹ ^ 3 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hx1 : 1 ≤ x := ht.one.trans hx.le
  set y := ((n : ℝ) + 1) * x
  have hy : x ≤ y := by nlinarith
  have hy1 : 1 ≤ y := hx1.trans hy
  have hη := ht.par.pos
  have hL0 : 0 ≤ L := by linarith [ht.one]
  have hyL : L ^ 2 < y ^ 2 := by nlinarith
  have hb := norm_kHd_tail hη ht.alpha hy1 hyL (α := α)
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [norm_mul, hnorm]
  have hD := kD0_nonneg (L := L) hη
  have hP := kP_pos hη
  have hyinv : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy1
  have hy0 : 0 < y := by linarith
  -- `(6y³ + 2β²y⁵ + 32πηy⁴)(πηy)^{−8} ≤ P·D₀·y^{−3}`
  have hmain : (6 * y ^ 3 + 2 * (2 * π * (L - 4 * η)) ^ 2 * y ^ 5 + 32 * π * η * y ^ 4)
      * (1 / (π * η * y)) ^ 8 ≤ kP η * kD0 L η * y⁻¹ ^ 3 := by
    have e : (1 / (π * η * y)) ^ 8 = kP η * y⁻¹ ^ 8 := by unfold kP; field_simp
    rw [e]
    have h5 : y ^ 3 * y⁻¹ ^ 8 ≤ y⁻¹ ^ 3 := by
      have : y ^ 3 * y⁻¹ ^ 8 = y⁻¹ ^ 5 := by field_simp
      rw [this]; exact pow_le_pow_of_le_one (by positivity) hyinv (by norm_num)
    have h4 : y ^ 4 * y⁻¹ ^ 8 ≤ y⁻¹ ^ 3 := by
      have : y ^ 4 * y⁻¹ ^ 8 = y⁻¹ ^ 4 := by field_simp
      rw [this]; exact pow_le_pow_of_le_one (by positivity) hyinv (by norm_num)
    have h3 : y ^ 5 * y⁻¹ ^ 8 = y⁻¹ ^ 3 := by field_simp
    have hb2 : 0 ≤ 2 * (2 * π * (L - 4 * η)) ^ 2 := by positivity
    have hpe : 0 ≤ 32 * π * η := by have := pi_pos; positivity
    calc (6 * y ^ 3 + 2 * (2 * π * (L - 4 * η)) ^ 2 * y ^ 5 + 32 * π * η * y ^ 4) * (kP η * y⁻¹ ^ 8)
        = kP η * (6 * (y ^ 3 * y⁻¹ ^ 8) + 2 * (2 * π * (L - 4 * η)) ^ 2 * (y ^ 5 * y⁻¹ ^ 8)
            + 32 * π * η * (y ^ 4 * y⁻¹ ^ 8)) := by ring
      _ ≤ kP η * (6 * y⁻¹ ^ 3 + 2 * (2 * π * (L - 4 * η)) ^ 2 * y⁻¹ ^ 3 + 32 * π * η * y⁻¹ ^ 3) := by
          rw [h3]; gcongr
      _ = kP η * kD0 L η * y⁻¹ ^ 3 := by unfold kD0; ring
  have hfin : ((n : ℝ) + 1) * (kP η * kD0 L η * y⁻¹ ^ 3) ≤ kP η * kD0 L η * x⁻¹ ^ 3 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
    have e : ((n : ℝ) + 1) * y⁻¹ ^ 3 = x⁻¹ ^ 3 * ((n : ℝ) + 1)⁻¹ ^ 2 := by
      simp only [y]; field_simp
    have h2 : kP η * kD0 L η * (((n : ℝ) + 1) * y⁻¹ ^ 3) = kP η * kD0 L η * (x⁻¹ ^ 3 * ((n : ℝ) + 1)⁻¹ ^ 2) := by
      rw [e]
    nlinarith [h2]
  have hcast : ((n : ℂ) + 1) * (x : ℂ) = ((y : ℝ) : ℂ) := by simp only [y]; push_cast; ring
  rw [hcast]
  calc ((n : ℝ) + 1) * ‖kHd L η α (y : ℂ)‖ ≤ ((n : ℝ) + 1) * (kP η * kD0 L η * y⁻¹ ^ 3) := by
        gcongr; exact hb.trans hmain
    _ ≤ _ := hfin

theorem norm_SHd_tail (ht : Tail L η α) {x : ℝ} (hx : L < x) :
    ‖SHd L η α x‖ ≤ 2 * kP η * kD0 L η * x⁻¹ ^ 3 := by
  have hs := summable_inv_sq_succ.mul_left (kP η * kD0 L η * x⁻¹ ^ 3)
  have hx0 : 0 < x := by linarith [ht.one]
  calc ‖SHd L η α x‖ ≤ ∑' n : ℕ, kP η * kD0 L η * x⁻¹ ^ 3 * ((n : ℝ) + 1)⁻¹ ^ 2 :=
        tsum_of_norm_bounded hs.hasSum (norm_termd_tail ht hx)
    _ = kP η * kD0 L η * x⁻¹ ^ 3 * ∑' n : ℕ, ((n : ℝ) + 1)⁻¹ ^ 2 := tsum_mul_left
    _ ≤ kP η * kD0 L η * x⁻¹ ^ 3 * 2 := by
        have := (kP_pos ht.par.pos).le
        have := kD0_nonneg (L := L) ht.par.pos
        gcongr; exact tsum_inv_sq_succ_le
    _ = 2 * kP η * kD0 L η * x⁻¹ ^ 3 := by ring

end Kaiser

#print axioms Kaiser.norm_SH_tail
#print axioms Kaiser.norm_SHd_tail

#print axioms Kaiser.hasDerivAt_SH
#print axioms Kaiser.continuousOn_SHd
