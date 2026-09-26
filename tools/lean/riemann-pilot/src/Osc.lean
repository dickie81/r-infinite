import Mathlib
import T1ca

/-! # Theorem 1ca(iii): the leftover oscillation

`w_T`, `sqrt_ratio`, `F_k^s` (`Fs`), `F_k^s′` (`Fp`), `F_k^s″` (`Fpp`) and `T·G` (`TG`) come from
`T1ca.lean`. -/

open Real MeasureTheory intervalIntegral
open Filter Topology

noncomputable section

namespace Pilot1ca

/-! ## 1ca(iii): the weight defect -/

/-- The weight defect `D_T(r) = (1/r)[(1 − r²/T²)^{−1/2} − 1]` (1ca(iii)), so `w_T = 4/r + 4D_T`. -/
def DT (T r : ℝ) : ℝ := 1 / r * ((Real.sqrt (1 - r ^ 2 / T ^ 2))⁻¹ - 1)

theorem wT_eq (T : ℝ) {r : ℝ} (hr : r ≠ 0) : wT T r = 4 / r + 4 * DT T r := by
  unfold wT DT
  rcases eq_or_ne (Real.sqrt (1 - r ^ 2 / T ^ 2)) 0 with h | h
  · rw [h]; simp; ring
  · field_simp
    ring

/-- `v = √(1 − r²/T²)` on `(0, T)`: `0 < v ≤ 1` and `v² = 1 − r²/T²`. -/
theorem sqrt_facts {T r : ℝ} (hr : 0 < r) (hrT : r < T) :
    0 < Real.sqrt (1 - r ^ 2 / T ^ 2) ∧ Real.sqrt (1 - r ^ 2 / T ^ 2) ≤ 1 ∧
      Real.sqrt (1 - r ^ 2 / T ^ 2) ^ 2 = 1 - r ^ 2 / T ^ 2 := by
  have hT : 0 < T := by linarith
  have hq : 0 < 1 - r ^ 2 / T ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have hq1 : 1 - r ^ 2 / T ^ 2 ≤ 1 := by
    have : 0 ≤ r ^ 2 / T ^ 2 := by positivity
    linarith
  refine ⟨Real.sqrt_pos.2 hq, ?_, Real.sq_sqrt hq.le⟩
  rw [Real.sqrt_le_one]
  exact hq1

theorem DT_nonneg {T r : ℝ} (hr : 0 < r) (hrT : r < T) : 0 ≤ DT T r := by
  obtain ⟨hv0, hv1, -⟩ := sqrt_facts hr hrT
  unfold DT
  apply mul_nonneg (by positivity)
  rw [sub_nonneg]
  exact one_le_inv₀ hv0 |>.2 hv1

/-- The derivative of `D_T` in `r` on `(0, T)`. -/
def DTd (T r : ℝ) : ℝ :=
  -(1 / r ^ 2) * ((Real.sqrt (1 - r ^ 2 / T ^ 2))⁻¹ - 1)
    + 1 / r * (r / (T ^ 2 * Real.sqrt (1 - r ^ 2 / T ^ 2) ^ 3))

theorem hasDerivAt_DT {T r : ℝ} (hr : 0 < r) (hrT : r < T) :
    HasDerivAt (DT T) (DTd T r) r := by
  have hT : 0 < T := by linarith
  obtain ⟨hv0, -, hv2⟩ := sqrt_facts hr hrT
  set v := Real.sqrt (1 - r ^ 2 / T ^ 2) with hv
  have hq : HasDerivAt (fun r => 1 - r ^ 2 / T ^ 2) (-(2 * r / T ^ 2)) r := by
    have := ((hasDerivAt_pow 2 r).div_const (T ^ 2)).const_sub 1
    convert this using 1; push_cast; ring
  have hq0 : 1 - r ^ 2 / T ^ 2 ≠ 0 := by
    intro h0; rw [h0, Real.sqrt_zero] at hv; linarith
  have hs := hq.sqrt hq0
  have hsi := hs.inv (by rw [← hv]; exact hv0.ne')
  have hri : HasDerivAt (fun r : ℝ => 1 / r) (-(1 / r ^ 2)) r := by
    simpa [one_div] using hasDerivAt_inv hr.ne'
  have hprod := hri.mul (hsi.sub_const 1)
  refine hprod.congr_deriv ?_
  simp only [Pi.inv_apply]
  unfold DTd
  rw [← hv]
  field_simp

theorem DTd_nonneg {T r : ℝ} (hr : 0 < r) (hrT : r < T) : 0 ≤ DTd T r := by
  have hT : 0 < T := by linarith
  obtain ⟨hv0, hv1, hv2⟩ := sqrt_facts hr hrT
  set v := Real.sqrt (1 - r ^ 2 / T ^ 2) with hv
  have hr2 : r ^ 2 = T ^ 2 * (1 - v ^ 2) := by
    rw [hv2]; field_simp; ring
  unfold DTd
  rw [← hv]
  have hT2 : 0 < T ^ 2 := by positivity
  have hkey : (1 / r ^ 2) * (v⁻¹ - 1) ≤ 1 / r * (r / (T ^ 2 * v ^ 3)) := by
    have e1 : 1 / r * (r / (T ^ 2 * v ^ 3)) = 1 / (T ^ 2 * v ^ 3) := by
      field_simp
    rw [e1, hr2]
    have hv1' : 1 - v ^ 2 > 0 ∨ 1 - v ^ 2 = 0 := by
      rcases eq_or_lt_of_le hv1 with h | h
      · right; rw [h]; ring
      · left; nlinarith
    rcases hv1' with hpos | hzero
    · rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      rw [show v⁻¹ - 1 = (1 - v) / v by field_simp]
      rw [div_mul_eq_mul_div, div_le_iff₀ hv0]
      -- (1 - v) * (T²v³) ≤ T²(1 - v²) * v, i.e. v² ≤ 1 + v
      have hvv : v ^ 2 ≤ 1 + v := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 hv1) (mul_nonneg (le_of_lt hT2) (pow_pos hv0 2).le),
        mul_nonneg (mul_nonneg (le_of_lt hT2) hv0.le) (sub_nonneg.2 hvv)]
    · have hv1'' : v = 1 := by nlinarith
      rw [hv1'']; simp; positivity
  linarith

theorem DT_continuousOn {T a b : ℝ} (ha : 0 < a) (hbT : b < T) :
    ContinuousOn (DT T) (Set.Icc a b) := by
  intro x hx
  exact (hasDerivAt_DT (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt

/-- `−arccosh(T/r) − ln r` is an antiderivative of `D_T` on `(0, T)`. -/
theorem hasDerivAt_DT_antider {T r : ℝ} (hr : 0 < r) (hrT : r < T) :
    HasDerivAt (fun r => -Real.arcosh (T / r) - Real.log r) (DT T r) r := by
  have hT : 0 < T := by linarith
  have hx : 0 < T ^ 2 - r ^ 2 := by nlinarith
  have h1 : T / r ∈ Set.Ioi 1 := by
    rw [Set.mem_Ioi, one_lt_div hr]; exact hrT
  have hd : HasDerivAt (fun r : ℝ => T / r) (-(T / r ^ 2)) r := by
    have := (hasDerivAt_id r).inv hr.ne' |>.const_mul T
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]
  have h2 := ((Real.hasDerivAt_arcosh h1).comp r hd).neg.sub (Real.hasDerivAt_log hr.ne')
  refine h2.congr_deriv ?_
  have hsq1 : Real.sqrt ((T / r) ^ 2 - 1) = Real.sqrt (T ^ 2 - r ^ 2) / r := by
    rw [show (T / r) ^ 2 - 1 = (T ^ 2 - r ^ 2) / r ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ r ^ 2), Real.sqrt_sq hr.le]
  have hs : 0 < Real.sqrt (T ^ 2 - r ^ 2) := Real.sqrt_pos.2 hx
  unfold DT
  rw [hsq1, sqrt_ratio hT hx]
  field_simp

/-- **`∫_{T−Δ}^T D_T = arccosh(T/(T−Δ)) − ln(T/(T−Δ))`** (1ca(iii)), an improper integral at `T`. -/
theorem integral_DT {T b : ℝ} (hb : 0 < b) (hbT : b < T) :
    ∫ r in b..T, DT T r = Real.arcosh (T / b) - Real.log (T / b) ∧
      IntervalIntegrable (DT T) volume b T := by
  have hT : 0 < T := by linarith
  set F := fun r => -Real.arcosh (T / r) - Real.log r with hF
  have hcont : ContinuousOn F (Set.Icc b T) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply Real.continuousOn_arcosh.comp (continuousOn_const.div continuousOn_id
        (fun x hx => (lt_of_lt_of_le hb hx.1).ne'))
      intro x hx
      show 1 ≤ T / x
      rw [le_div_iff₀ (lt_of_lt_of_le hb hx.1)]
      linarith [hx.2]
    · exact Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx.1])
  have hderiv : ∀ x ∈ Set.Ioo b T, HasDerivAt F (DT T x) x :=
    fun x hx => hasDerivAt_DT_antider (by linarith [hx.1]) hx.2
  have hint : IntervalIntegrable (DT T) volume b T := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := F)
    · rw [Set.uIcc_of_le hbT.le]; exact hcont
    · intro x hx
      rw [min_eq_left hbT.le, max_eq_right hbT.le] at hx
      exact hderiv x hx
    · intro x hx
      rw [min_eq_left hbT.le, max_eq_right hbT.le] at hx
      exact DT_nonneg (by linarith [hx.1]) hx.2
  refine ⟨?_, hint⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hbT.le hcont hderiv hint]
  simp only [hF, div_self hT.ne', Real.arcosh_zero]
  rw [Real.log_div hT.ne' hb.ne']
  ring

/-! ## 1ca(iii): the oscillation `S`, its primitive `S₁`, and `Osc(T)` -/

/-- Standing hypotheses on 1bs's oscillation `S`: measurable, locally integrable, and continuous off
a countable set (the classical `S` jumps at the zeros). -/
structure OscS (S : ℝ → ℝ) : Prop where
  meas : Measurable S
  loc : ∀ a b, IntervalIntegrable S volume a b
  jumps : ∃ C : Set ℝ, C.Countable ∧ ∀ x ∉ C, ContinuousAt S x

/-- `S₁(r) = ∫_{γ₁}^r S`. -/
def S1 (S : ℝ → ℝ) (G r : ℝ) : ℝ := ∫ t in G..r, S t

/-- The leftover oscillation `Osc(T) = ∫_{γ₁}^T S(r) w_T(r) dr` of 1ca(i). -/
def Osc (S : ℝ → ℝ) (G T : ℝ) : ℝ := ∫ r in G..T, S r * wT T r

theorem S1_continuous {S : ℝ → ℝ} (hS : OscS S) (G : ℝ) : Continuous (S1 S G) :=
  intervalIntegral.continuous_primitive hS.loc G

theorem S1_self (S : ℝ → ℝ) (G : ℝ) : S1 S G G = 0 := intervalIntegral.integral_same

theorem hasDerivAt_S1 {S : ℝ → ℝ} (hS : OscS S) (G : ℝ) {x : ℝ} (hx : ContinuousAt S x) :
    HasDerivAt (S1 S G) (S x) x :=
  intervalIntegral.integral_hasDerivAt_right (hS.loc G x)
    hS.meas.stronglyMeasurable.stronglyMeasurableAtFilter hx

/-- Integration by parts, with the derivative of `u` known only off a countable set. -/
theorem ibp_off_countable {u u' v v' : ℝ → ℝ} {a b : ℝ} {C : Set ℝ} (hab : a ≤ b)
    (hC : C.Countable) (hu : ContinuousOn u (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc a b))
    (hu' : ∀ x ∈ Set.Ioo a b \ C, HasDerivAt u (u' x) x)
    (hv' : ∀ x ∈ Set.Ioo a b, HasDerivAt v (v' x) x)
    (hi : IntervalIntegrable (fun x => u' x * v x + u x * v' x) volume a b) :
    ∫ x in a..b, (u' x * v x + u x * v' x) = u b * v b - u a * v a :=
  integral_eq_of_hasDerivAt_off_countable_of_le (fun x => u x * v x) _ hab hC (hu.mul hv)
    (fun x hx => (hu' x hx).mul (hv' x hx.1)) hi

theorem inv_continuousOn {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun r : ℝ => 1 / r) (Set.Icc a b) :=
  continuousOn_const.div continuousOn_id (fun _ hx => (lt_of_lt_of_le ha hx.1).ne')

theorem inv_sq_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun r : ℝ => 1 / r ^ 2) (Set.Icc a b) :=
  continuousOn_const.div (continuousOn_id.pow 2)
    (fun _ hx => (pow_pos (lt_of_lt_of_le ha hx.1) 2).ne')

/-- The tail by parts: `∫_T^X S/r = S₁(X)/X − S₁(T)/T + ∫_T^X S₁/r²`. -/
theorem tail_ibp {S : ℝ → ℝ} (hS : OscS S) {G T X : ℝ} (hT : 0 < T) (hTX : T ≤ X) :
    ∫ r in T..X, S r * (1 / r)
      = S1 S G X / X - S1 S G T / T + ∫ r in T..X, S1 S G r * (1 / r ^ 2) := by
  obtain ⟨C, hC, hcont⟩ := hS.jumps
  have hSr : IntervalIntegrable (fun r => S r * (1 / r)) volume T X :=
    (hS.loc T X).mul_continuousOn (by rw [Set.uIcc_of_le hTX]; exact inv_continuousOn hT)
  have hS1r : IntervalIntegrable (fun r => S1 S G r * (1 / r ^ 2)) volume T X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hTX]
    exact (S1_continuous hS G).continuousOn.mul (inv_sq_continuousOn hT)
  have hS1r' : IntervalIntegrable (fun r => S1 S G r * -(1 / r ^ 2)) volume T X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hTX]
    exact (S1_continuous hS G).continuousOn.mul (inv_sq_continuousOn hT).neg
  have hibp := ibp_off_countable (u := S1 S G) (u' := S) (v := fun r => 1 / r)
    (v' := fun r => -(1 / r ^ 2)) hTX hC (S1_continuous hS G).continuousOn (inv_continuousOn hT)
    (fun x hx => hasDerivAt_S1 hS G (hcont x hx.2))
    (fun x hx => by simpa [one_div] using hasDerivAt_inv (lt_trans hT hx.1).ne')
    (hSr.add hS1r')
  have e : ∫ r in T..X, S r * (1 / r)
      = ∫ r in T..X, ((S r * (1 / r) + S1 S G r * -(1 / r ^ 2)) + S1 S G r * (1 / r ^ 2)) := by
    congr 1; funext r; ring
  rw [e, intervalIntegral.integral_add (hSr.add hS1r') hS1r, hibp]
  ring

theorem tail_tendsto {S : ℝ → ℝ} (hS : OscS S) {G T : ℝ} (hT : 0 < T)
    (h1 : Tendsto (fun X => S1 S G X / X) atTop (𝓝 0))
    (h2 : IntegrableOn (fun r => S1 S G r * (1 / r ^ 2)) (Set.Ioi T)) :
    Tendsto (fun X => ∫ r in T..X, S r * (1 / r)) atTop
      (𝓝 (-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2))) := by
  have h3 := intervalIntegral_tendsto_integral_Ioi T h2 tendsto_id
  have h4 := (h1.sub_const (S1 S G T / T)).add h3
  rw [zero_sub] at h4
  apply h4.congr'
  filter_upwards [eventually_ge_atTop T] with X hX
  rw [tail_ibp (G := G) hS hT hX]
  rfl

theorem S_div_intervalIntegrable {S : ℝ → ℝ} (hS : OscS S) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (c : ℝ) : IntervalIntegrable (fun r => S r * (c / r)) volume a b :=
  (hS.loc a b).mul_continuousOn (by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id (fun x hx => (lt_of_lt_of_le ha hx.1).ne'))

/-- `Osc_∞ = ∫_{γ₁}^T S·4/r + 4 ∫_T^∞ S/r`, the tail by parts. -/
theorem oscInf_eq {S : ℝ → ℝ} (hS : OscS S) {G T OscInf : ℝ} (hG : 0 < G) (hGT : G ≤ T)
    (h1 : Tendsto (fun X => S1 S G X / X) atTop (𝓝 0))
    (h2 : IntegrableOn (fun r => S1 S G r * (1 / r ^ 2)) (Set.Ioi T))
    (hInf : Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop (𝓝 OscInf)) :
    OscInf = (∫ r in G..T, S r * (4 / r))
      + 4 * (-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)) := by
  have hT : 0 < T := lt_of_lt_of_le hG hGT
  have ht := tail_tendsto hS hT h1 h2
  have hlim : Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop
      (𝓝 ((∫ r in G..T, S r * (4 / r))
        + 4 * (-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)))) := by
    have := (ht.const_mul 4).const_add (∫ r in G..T, S r * (4 / r))
    apply this.congr'
    filter_upwards [eventually_ge_atTop T] with X hX
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := T)
      (S_div_intervalIntegrable hS hG hGT 4) (S_div_intervalIntegrable hS hT hX 4)]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    ring
  exact tendsto_nhds_unique hInf hlim

/-- `S·D_T` is integrable on `[γ₁, T]` when `S` is bounded near `T` (`D_T` is integrable at `T`). -/
theorem SDT_intervalIntegrable {S : ℝ → ℝ} (hS : OscS S) {G T Δ MS : ℝ} (hG : 0 < G)
    (hΔ : 0 < Δ) (hΔT : Δ < T - G) (hMS : ∀ r ∈ Set.Icc (T - Δ) T, |S r| ≤ MS) :
    IntervalIntegrable (fun r => S r * DT T r) volume G (T - Δ) ∧
      IntervalIntegrable (fun r => S r * DT T r) volume (T - Δ) T := by
  have hb : 0 < T - Δ := by linarith
  have hbT : T - Δ < T := by linarith
  constructor
  · exact (hS.loc G (T - Δ)).mul_continuousOn (by
      rw [Set.uIcc_of_le (by linarith)]; exact DT_continuousOn hG hbT)
  · obtain ⟨-, hDi⟩ := integral_DT hb hbT
    have hmeas : Measurable (DT T) := by unfold DT; fun_prop
    apply IntervalIntegrable.mono_fun (hDi.const_mul MS)
      ((hS.meas.mul hmeas).aestronglyMeasurable)
    rw [Set.uIoc_of_le hbT.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume T).filter_mono ae_restrict_le] with t ht htT
    have htT' : t < T := lt_of_le_of_ne ht.2 htT
    have hD := DT_nonneg (lt_trans hb ht.1) htT'
    have hSt := hMS t ⟨ht.1.le, ht.2⟩
    have hMS0 : 0 ≤ MS := le_trans (abs_nonneg _) hSt
    have hle : |S t * DT T t| ≤ |MS * DT T t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hD, abs_of_nonneg hMS0]
      exact mul_le_mul_of_nonneg_right hSt hD
    simpa [Real.norm_eq_abs] using hle

/-- **The exact decomposition of 1ca(iii)**:
`Osc(T) − Osc_∞ = 4∫_{γ₁}^T S D_T − 4∫_T^∞ S/r`, the last by parts `−S₁(T)/T + ∫_T^∞ S₁/r²`. -/
theorem osc_decomp {S : ℝ → ℝ} (hS : OscS S) {G T Δ MS OscInf : ℝ} (hG : 0 < G) (hΔ : 0 < Δ)
    (hΔT : Δ < T - G) (hMS : ∀ r ∈ Set.Icc (T - Δ) T, |S r| ≤ MS)
    (h1 : Tendsto (fun X => S1 S G X / X) atTop (𝓝 0))
    (h2 : IntegrableOn (fun r => S1 S G r * (1 / r ^ 2)) (Set.Ioi T))
    (hInf : Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop (𝓝 OscInf)) :
    Osc S G T - OscInf = 4 * (∫ r in G..T, S r * DT T r)
      - 4 * (-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)) := by
  have hGT : G ≤ T := by linarith
  obtain ⟨hi1, hi2⟩ := SDT_intervalIntegrable hS hG hΔ hΔT hMS
  have hSD : IntervalIntegrable (fun r => S r * DT T r) volume G T := hi1.trans hi2
  have hOsc : Osc S G T = (∫ r in G..T, S r * (4 / r)) + 4 * ∫ r in G..T, S r * DT T r := by
    unfold Osc
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (S_div_intervalIntegrable hS hG hGT 4) (hSD.const_mul 4)]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le hGT] at hr
    simp only
    rw [wT_eq T (lt_of_lt_of_le hG hr.1).ne']
    ring
  rw [hOsc, oscInf_eq hS hG hGT h1 h2 hInf]
  ring

/-- `|∫_{γ₁}^T S D_T| ≤ sup_{[T−Δ,T]}|S|·[arccosh(T/(T−Δ)) − ln(T/(T−Δ))] + 2 sup_{[γ₁,T]}|S₁|·D_T(T−Δ)`:
near `T` by the size of `S` against `∫ D_T`; below `T − Δ` by parts against `S₁`, `D_T` increasing. -/
theorem inner_bound {S : ℝ → ℝ} (hS : OscS S) {G T Δ MS M1 : ℝ} (hG : 0 < G) (hΔ : 0 < Δ)
    (hΔT : Δ < T - G) (hMS : ∀ r ∈ Set.Icc (T - Δ) T, |S r| ≤ MS)
    (hM1 : ∀ r ∈ Set.Icc G T, |S1 S G r| ≤ M1) :
    |∫ r in G..T, S r * DT T r|
      ≤ MS * (Real.arcosh (T / (T - Δ)) - Real.log (T / (T - Δ))) + 2 * M1 * DT T (T - Δ) := by
  obtain ⟨C, hC, hcont⟩ := hS.jumps
  set b := T - Δ with hb_def
  have hb : 0 < b := by linarith
  have hbT : b < T := by linarith
  have hGb : G < b := by linarith
  obtain ⟨hi1, hi2⟩ := SDT_intervalIntegrable hS hG hΔ hΔT hMS
  obtain ⟨hDint, hDi⟩ := integral_DT hb hbT
  have hM1_0 : 0 ≤ M1 := by
    have := hM1 G ⟨le_rfl, by linarith⟩
    rw [S1_self] at this; simpa using this
  -- near T
  have hnear : |∫ r in b..T, S r * DT T r| ≤ MS * (Real.arcosh (T / b) - Real.log (T / b)) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (f := fun r => S r * DT T r)
      (g := fun r => MS * DT T r) hbT.le (by
        filter_upwards [Measure.ae_ne volume T] with t htT ht
        have htT' : t < T := lt_of_le_of_ne ht.2 htT
        have hD := DT_nonneg (lt_trans hb ht.1) htT'
        have hSt := hMS t ⟨ht.1.le, ht.2⟩
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hD]
        exact mul_le_mul_of_nonneg_right hSt hD) (hDi.const_mul MS)
    rw [intervalIntegral.integral_const_mul, hDint] at h
    simpa [Real.norm_eq_abs] using h
  -- below T − Δ: by parts against S₁
  have hDTc : ContinuousOn (DT T) (Set.Icc G b) := DT_continuousOn hG hbT
  have hDTd_int : IntervalIntegrable (DTd T) volume G b := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := DT T)
    · rw [Set.uIcc_of_le hGb.le]; exact hDTc
    · intro x hx
      rw [min_eq_left hGb.le, max_eq_right hGb.le] at hx
      exact hasDerivAt_DT (by linarith [hx.1]) (by linarith [hx.2])
    · intro x hx
      rw [min_eq_left hGb.le, max_eq_right hGb.le] at hx
      exact DTd_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  have hS1c : ContinuousOn (S1 S G) (Set.uIcc G b) := (S1_continuous hS G).continuousOn
  have hS1D : IntervalIntegrable (fun r => S1 S G r * DTd T r) volume G b :=
    hDTd_int.continuousOn_mul hS1c
  have hibp := ibp_off_countable (u := S1 S G) (u' := S) (v := DT T) (v' := DTd T) hGb.le hC
    (S1_continuous hS G).continuousOn hDTc
    (fun x hx => hasDerivAt_S1 hS G (hcont x hx.2))
    (fun x hx => hasDerivAt_DT (by linarith [hx.1]) (by linarith [hx.2]))
    (hi1.add hS1D)
  rw [intervalIntegral.integral_add hi1 hS1D, S1_self, zero_mul, sub_zero] at hibp
  have hftc : ∫ r in G..b, DTd T r = DT T b - DT T G :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hGb.le hDTc
      (fun x hx => hasDerivAt_DT (by linarith [hx.1]) (by linarith [hx.2])) hDTd_int
  have hS1Db : |∫ r in G..b, S1 S G r * DTd T r| ≤ M1 * (DT T b - DT T G) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (f := fun r => S1 S G r * DTd T r)
      (g := fun r => M1 * DTd T r) hGb.le (by
        refine Filter.Eventually.of_forall (fun t ht => ?_)
        have hd := DTd_nonneg (by linarith [ht.1] : 0 < t) (by linarith [ht.2] : t < T)
        have hS1t := hM1 t ⟨ht.1.le, by linarith [ht.2]⟩
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right hS1t hd) (hDTd_int.const_mul M1)
    rw [intervalIntegral.integral_const_mul, hftc] at h
    simpa [Real.norm_eq_abs] using h
  have hDG : 0 ≤ DT T G := DT_nonneg hG (by linarith)
  have hDb : 0 ≤ DT T b := DT_nonneg hb hbT
  have hS1b : |S1 S G b| ≤ M1 := hM1 b ⟨hGb.le, hbT.le⟩
  have hfar : |∫ r in G..b, S r * DT T r| ≤ 2 * M1 * DT T b := by
    have e : ∫ r in G..b, S r * DT T r = S1 S G b * DT T b - ∫ r in G..b, S1 S G r * DTd T r := by
      linarith
    rw [e]
    calc |S1 S G b * DT T b - ∫ r in G..b, S1 S G r * DTd T r|
        ≤ |S1 S G b * DT T b| + |∫ r in G..b, S1 S G r * DTd T r| := abs_sub _ _
      _ ≤ M1 * DT T b + M1 * (DT T b - DT T G) := by
          rw [abs_mul, abs_of_nonneg hDb]
          exact add_le_add (mul_le_mul_of_nonneg_right hS1b hDb) hS1Db
      _ ≤ 2 * M1 * DT T b := by nlinarith
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  calc |(∫ r in G..b, S r * DT T r) + ∫ r in b..T, S r * DT T r|
      ≤ |∫ r in G..b, S r * DT T r| + |∫ r in b..T, S r * DT T r| := abs_add_le _ _
    _ ≤ 2 * M1 * DT T b + MS * (Real.arcosh (T / b) - Real.log (T / b)) := add_le_add hfar hnear
    _ = _ := by ring

/-- `∫_T^∞ dr/r² = 1/T`. -/
theorem Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun r : ℝ => 1 / r ^ 2) (Set.Ioi T) ∧ ∫ r in Set.Ioi T, 1 / r ^ 2 = 1 / T := by
  have hderiv : ∀ x ∈ Set.Ioi T, HasDerivAt (fun r : ℝ => -(1 / r)) (1 / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_trans hT hx).ne'
    simpa [one_div] using (hasDerivAt_inv hx0).fun_neg
  have hcont : ContinuousWithinAt (fun r : ℝ => -(1 / r)) (Set.Ici T) T :=
    ((continuousAt_const.div continuousAt_id hT.ne').neg).continuousWithinAt
  have hlim : Tendsto (fun r : ℝ => -(1 / r)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id
    simpa using this.neg
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun x _ => by positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  ring

/-- `∫_T^∞ ln r/r² dr = (ln T + 1)/T` for `T ≥ 1`. -/
theorem Ioi_log_div_sq {T : ℝ} (hT : 1 ≤ T) :
    IntegrableOn (fun r : ℝ => Real.log r * (1 / r ^ 2)) (Set.Ioi T) ∧
      ∫ r in Set.Ioi T, Real.log r * (1 / r ^ 2) = (Real.log T + 1) / T := by
  have hT0 : 0 < T := by linarith
  have hderiv : ∀ x ∈ Set.Ioi T,
      HasDerivAt (fun r : ℝ => -((Real.log r + 1) / r)) (Real.log x * (1 / x ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hT0 hx
    have h1 := (((Real.hasDerivAt_log hx0.ne').add_const 1).div (hasDerivAt_id x) hx0.ne').neg
    refine h1.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun r : ℝ => -((Real.log r + 1) / r)) (Set.Ici T) T :=
    ((((Real.continuousAt_log hT0.ne').add continuousAt_const).div continuousAt_id
      hT0.ne').neg).continuousWithinAt
  have hlim : Tendsto (fun r : ℝ => -((Real.log r + 1) / r)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => Real.log r / r) atTop (𝓝 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using this
    have h2 : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id
    have h3 := (h1.add h2).neg
    simp only [add_zero, neg_zero] at h3
    apply h3.congr'
    filter_upwards [eventually_gt_atTop 0] with r hr
    field_simp
  have hpos : ∀ x ∈ Set.Ioi T, 0 ≤ Real.log x * (1 / x ^ 2) := fun x hx =>
    mul_nonneg (Real.log_nonneg (le_trans hT (le_of_lt hx))) (by positivity)
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  ring

theorem S1_div_sq_integrable {S : ℝ → ℝ} (hS : OscS S) {G T : ℝ} (_hT : 0 < T)
    {B : ℝ → ℝ} (hB : IntegrableOn (fun r => B r * (1 / r ^ 2)) (Set.Ioi T))
    (hle : ∀ r, T < r → |S1 S G r| ≤ B r) :
    IntegrableOn (fun r => S1 S G r * (1 / r ^ 2)) (Set.Ioi T) := by
  have hmeas : AEStronglyMeasurable (fun r => S1 S G r * (1 / r ^ 2))
      (volume.restrict (Set.Ioi T)) :=
    ((S1_continuous hS G).measurable.mul (by fun_prop)).aestronglyMeasurable
  refine Integrable.mono' hB hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / r ^ 2)]
  exact mul_le_mul_of_nonneg_right (hle r hr) (by positivity)

theorem tail_abs_le {S : ℝ → ℝ} (_hS : OscS S) {G T : ℝ} (_hT : 0 < T)
    {B : ℝ → ℝ} (hB : IntegrableOn (fun r => B r * (1 / r ^ 2)) (Set.Ioi T))
    (hle : ∀ r, T < r → |S1 S G r| ≤ B r) :
    |∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)| ≤ ∫ r in Set.Ioi T, B r * (1 / r ^ 2) := by
  have h := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun r => S1 S G r * (1 / r ^ 2)) hB (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / r ^ 2)]
    exact mul_le_mul_of_nonneg_right (hle r hr) (by positivity))
  simpa [Real.norm_eq_abs] using h

/-- The decomposition's bound with a general tail bound `TB ≥ |∫_T^∞ S/r|`. -/
theorem osc_abs_le {S : ℝ → ℝ} (hS : OscS S) {G T Δ MS M1 OscInf TB : ℝ} (hG : 0 < G)
    (hΔ : 0 < Δ) (hΔT : Δ < T - G) (hMS : ∀ r ∈ Set.Icc (T - Δ) T, |S r| ≤ MS)
    (hM1 : ∀ r ∈ Set.Icc G T, |S1 S G r| ≤ M1)
    (h1 : Tendsto (fun X => S1 S G X / X) atTop (𝓝 0))
    (h2 : IntegrableOn (fun r => S1 S G r * (1 / r ^ 2)) (Set.Ioi T))
    (hInf : Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop (𝓝 OscInf))
    (htail : |-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)| ≤ TB) :
    |Osc S G T - OscInf| ≤ 4 * (MS * (Real.arcosh (T / (T - Δ)) - Real.log (T / (T - Δ)))
      + 2 * M1 * DT T (T - Δ)) + 4 * TB := by
  have hdec := osc_decomp hS hG hΔ hΔT hMS h1 h2 hInf
  have hin := inner_bound hS hG hΔ hΔT hMS hM1
  rw [hdec]
  have hsub := abs_sub (4 * ∫ r in G..T, S r * DT T r)
    (4 * (-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)))
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hsub
  have h4 := mul_le_mul_of_nonneg_left hin (by norm_num : (0 : ℝ) ≤ 4)
  have h5 := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 4)
  exact le_trans hsub (add_le_add h4 h5)

/-- **1ca(iii), the displayed bound**: for every `Δ ∈ (0, T − γ₁)`, with `MS ≥ sup_{[T−Δ,T]}|S|`,
`M1 ≥ sup_{[γ₁,T]}|S₁|` and `M2 ≥ sup_{[T,∞)}|S₁|`,
`|Osc(T) − Osc_∞| ≤ 4MS[arccosh(T/(T−Δ)) − ln(T/(T−Δ))] + 8M1·D_T(T−Δ) + 8M2/T`. -/
theorem osc_bound {S : ℝ → ℝ} (hS : OscS S) {G T Δ MS M1 M2 OscInf : ℝ} (hG : 0 < G)
    (hΔ : 0 < Δ) (hΔT : Δ < T - G)
    (hMS : ∀ r ∈ Set.Icc (T - Δ) T, |S r| ≤ MS)
    (hM1 : ∀ r ∈ Set.Icc G T, |S1 S G r| ≤ M1)
    (hM2 : ∀ r, T ≤ r → |S1 S G r| ≤ M2)
    (hInf : Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop (𝓝 OscInf)) :
    |Osc S G T - OscInf| ≤ 4 * MS * (Real.arcosh (T / (T - Δ)) - Real.log (T / (T - Δ)))
      + 8 * M1 * DT T (T - Δ) + 8 * M2 / T := by
  have hT : 0 < T := by linarith
  obtain ⟨hIi, hIv⟩ := Ioi_inv_sq hT
  have hB : IntegrableOn (fun r => (fun _ => M2) r * (1 / r ^ 2)) (Set.Ioi T) := hIi.const_mul M2
  have hle : ∀ r, T < r → |S1 S G r| ≤ (fun _ => M2) r := fun r hr => hM2 r hr.le
  have h1 : Tendsto (fun X => S1 S G X / X) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_const_nhds (x := M2)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop T] with X hX
    have hX0 : 0 < X := lt_of_lt_of_le hT hX
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hX0]
    exact div_le_div_of_nonneg_right (hM2 X hX) hX0.le
  have h2 := S1_div_sq_integrable hS hT hB hle
  have hI := tail_abs_le hS hT hB hle
  rw [MeasureTheory.integral_const_mul, hIv] at hI
  have hS1T : |S1 S G T / T| ≤ M2 / T := by
    rw [abs_div, abs_of_pos hT]; exact div_le_div_of_nonneg_right (hM2 T le_rfl) hT.le
  have htail : |-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)| ≤ 2 * M2 / T := by
    calc _ ≤ |-(S1 S G T / T)| + |∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)| := abs_add_le _ _
      _ ≤ M2 / T + M2 * (1 / T) := by rw [abs_neg]; exact add_le_add hS1T hI
      _ = 2 * M2 / T := by ring
  calc _ ≤ _ := osc_abs_le hS hG hΔ hΔT hMS hM1 h1 h2 hInf htail
    _ = _ := by ring

theorem arcosh_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    Real.arcosh x - Real.log x ≤ Real.sqrt (2 * (x - 1)) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
  unfold Real.arcosh
  rw [← Real.log_div (by positivity) hx0.ne']
  have hpos : 0 < (x + Real.sqrt (x ^ 2 - 1)) / x := by positivity
  calc Real.log ((x + Real.sqrt (x ^ 2 - 1)) / x) ≤ (x + Real.sqrt (x ^ 2 - 1)) / x - 1 :=
        Real.log_le_sub_one_of_pos hpos
    _ = Real.sqrt (x ^ 2 - 1) / x := by field_simp; ring
    _ ≤ Real.sqrt (2 * (x - 1)) := by
        rw [div_le_iff₀ hx0]
        have h1 : Real.sqrt (2 * (x - 1)) * x = Real.sqrt (2 * (x - 1) * x ^ 2) := by
          have e : Real.sqrt (2 * (x - 1) * x ^ 2) = Real.sqrt (2 * (x - 1)) * x := by
            rw [Real.sqrt_mul' (2 * (x - 1)) (sq_nonneg x), Real.sqrt_sq hx0.le]
          exact e.symm
        rw [h1]
        apply Real.sqrt_le_sqrt
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx))
          (by linarith : (0 : ℝ) ≤ 2 * x + 1)]

/-- `arccosh(T/(T−Δ)) − ln(T/(T−Δ)) ≤ 2√Δ/√T` for `T ≥ 2Δ` (the paper's `√(2Δ/T)(1 + O(√(Δ/T)))`). -/
theorem near_term_le {T Δ : ℝ} (hΔ : 0 < Δ) (hT : 2 * Δ ≤ T) :
    Real.arcosh (T / (T - Δ)) - Real.log (T / (T - Δ)) ≤ 2 * Real.sqrt Δ / Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hr : 0 < T - Δ := by linarith
  have hx : 1 ≤ T / (T - Δ) := by rw [le_div_iff₀ hr]; linarith
  refine le_trans (arcosh_sub_log_le hx) ?_
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  rw [le_div_iff₀ hsT, ← Real.sqrt_mul (mul_nonneg (by norm_num) (sub_nonneg.2 hx))]
  have h2 : 2 * Real.sqrt Δ = Real.sqrt (4 * Δ) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h2]
  apply Real.sqrt_le_sqrt
  rw [show 2 * (T / (T - Δ) - 1) * T = 2 * Δ * T / (T - Δ) by field_simp; ring]
  rw [div_le_iff₀ hr]
  nlinarith

/-- `D_T(T−Δ) ≤ 2/(√Δ √T)` for `T ≥ 2Δ` (the paper's `(2ΔT)^{−1/2}(1 + O(√(Δ/T)))`). -/
theorem DT_le {T Δ : ℝ} (hΔ : 0 < Δ) (hT : 2 * Δ ≤ T) :
    DT T (T - Δ) ≤ 2 / (Real.sqrt Δ * Real.sqrt T) := by
  have hT0 : 0 < T := by linarith
  have hr : 0 < T - Δ := by linarith
  have hx : 0 < T ^ 2 - (T - Δ) ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (T ^ 2 - (T - Δ) ^ 2) := Real.sqrt_pos.2 hx
  have hge : Real.sqrt Δ * Real.sqrt T ≤ Real.sqrt (T ^ 2 - (T - Δ) ^ 2) := by
    rw [← Real.sqrt_mul hΔ.le]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hsd : 0 < Real.sqrt Δ * Real.sqrt T := by positivity
  unfold DT
  rw [sqrt_ratio hT0 hx]
  calc 1 / (T - Δ) * ((Real.sqrt (T ^ 2 - (T - Δ) ^ 2) / T)⁻¹ - 1)
      ≤ 1 / (T - Δ) * (Real.sqrt (T ^ 2 - (T - Δ) ^ 2) / T)⁻¹ := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = T / (T - Δ) / Real.sqrt (T ^ 2 - (T - Δ) ^ 2) := by field_simp
    _ ≤ 2 / Real.sqrt (T ^ 2 - (T - Δ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ hs.le
        rw [div_le_iff₀ hr]; linarith
    _ ≤ 2 / (Real.sqrt Δ * Real.sqrt T) := div_le_div_of_nonneg_left (by norm_num) hsd hge

/-- **1ca(iii): `Osc(T) = Osc_∞ + O(ln T/√T)`.** From von Mangoldt's `|S(t)| ≤ C ln t` and
Littlewood's `|S₁(t)| ≤ C ln t` on `[γ₁, ∞)` (the named classical inputs): the improper integral
`Osc_∞ = ∫_{γ₁}^∞ S·4/r` converges, and for any fixed `Δ > 0` and every `T ≥ max(γ₁ + 2Δ, 3)`,
`|Osc(T) − Osc_∞| ≤ (8C√Δ + 16C/√Δ + 12C) · ln T/√T`. The tail is bounded through `|S₁(T)|/T` and
`∫_T^∞ |S₁|/r² ≤ C(ln T + 1)/T` (under `S₁ = O(ln t)` the displayed `sup_{[T,∞)}|S₁|` need not be
finite). -/
theorem osc_log {S : ℝ → ℝ} (hS : OscS S) {G Δ C : ℝ} (hG : 1 ≤ G) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (hSlog : ∀ t, G ≤ t → |S t| ≤ C * Real.log t)
    (hS1log : ∀ t, G ≤ t → |S1 S G t| ≤ C * Real.log t) :
    ∃ OscInf : ℝ, Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop (𝓝 OscInf) ∧
      ∀ T, G + 2 * Δ ≤ T → 3 ≤ T →
        |Osc S G T - OscInf|
          ≤ (8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C) * (Real.log T / Real.sqrt T) := by
  have hG0 : 0 < G := by linarith
  have h1 : Tendsto (fun X => S1 S G X / X) atTop (𝓝 0) := by
    have hlog : Tendsto (fun X => C * (Real.log X / X)) atTop (𝓝 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using this.const_mul C
    apply squeeze_zero_norm' _ hlog
    filter_upwards [eventually_ge_atTop G] with X hX
    have hX0 : 0 < X := lt_of_lt_of_le hG0 hX
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hX0, mul_div_assoc']
    exact div_le_div_of_nonneg_right (hS1log X hX) hX0.le
  have hB : ∀ T, 1 ≤ T → IntegrableOn (fun r => (fun r => C * Real.log r) r * (1 / r ^ 2))
      (Set.Ioi T) := by
    intro T hT
    obtain ⟨hLi, -⟩ := Ioi_log_div_sq hT
    have h : IntegrableOn (fun r => C * (Real.log r * (1 / r ^ 2))) (Set.Ioi T) :=
      hLi.const_mul C
    refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
    show C * (Real.log r * (1 / r ^ 2)) = C * Real.log r * (1 / r ^ 2)
    ring
  have h2 : ∀ T, G ≤ T → IntegrableOn (fun r => S1 S G r * (1 / r ^ 2)) (Set.Ioi T) :=
    fun T hT => S1_div_sq_integrable hS (by linarith) (hB T (le_trans hG hT))
      (fun r hr => hS1log r (by linarith [hr.le]))
  set OscInf := 4 * (-(S1 S G G / G) + ∫ r in Set.Ioi G, S1 S G r * (1 / r ^ 2)) with hOI
  have hInf : Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop (𝓝 OscInf) := by
    have ht := (tail_tendsto hS hG0 h1 (h2 G le_rfl)).const_mul 4
    apply ht.congr'
    filter_upwards with X
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    ring
  refine ⟨OscInf, hInf, fun T hT hT3 => ?_⟩
  have hGT : G ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hΔT : Δ < T - G := by linarith
  set L := Real.log T with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9
    linarith
  have hmono : ∀ r, 0 < r → r ≤ T → C * Real.log r ≤ C * L := fun r hr hrT =>
    mul_le_mul_of_nonneg_left (Real.log_le_log hr hrT) hC
  have hMS : ∀ r ∈ Set.Icc (T - Δ) T, |S r| ≤ C * L := fun r hr =>
    le_trans (hSlog r (by linarith [hr.1])) (hmono r (by linarith [hr.1]) hr.2)
  have hM1 : ∀ r ∈ Set.Icc G T, |S1 S G r| ≤ C * L := fun r hr =>
    le_trans (hS1log r hr.1) (hmono r (by linarith [hr.1]) hr.2)
  -- the tail: |S₁(T)|/T + ∫_T^∞ |S₁|/r² ≤ C L/T + C(L + 1)/T
  obtain ⟨-, hLv⟩ := Ioi_log_div_sq (le_trans hG hGT)
  have hI := tail_abs_le hS hT0 (hB T (le_trans hG hGT)) (fun r hr => hS1log r (by linarith [hr.le]))
  have hIv : ∫ r in Set.Ioi T, (fun r => C * Real.log r) r * (1 / r ^ 2)
      = C * ((L + 1) / T) := by
    rw [← hLv, ← MeasureTheory.integral_const_mul]
    congr 1
    funext r
    ring
  rw [hIv] at hI
  have hS1T : |S1 S G T / T| ≤ C * L / T := by
    rw [abs_div, abs_of_pos hT0]; exact div_le_div_of_nonneg_right (hS1log T hGT) hT0.le
  have htail : |-(S1 S G T / T) + ∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)|
      ≤ C * L / T + C * ((L + 1) / T) := by
    calc _ ≤ |-(S1 S G T / T)| + |∫ r in Set.Ioi T, S1 S G r * (1 / r ^ 2)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; exact add_le_add hS1T hI
  have hmain := osc_abs_le hS hG0 hΔ hΔT hMS hM1 h1 (h2 T hGT) hInf htail
  -- the √T estimates
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hsΔ : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔ
  have hsT1 : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; linarith
  have hTsT : Real.sqrt T ≤ T := by
    have := Real.sq_sqrt hT0.le
    nlinarith
  have hA := near_term_le hΔ (by linarith : 2 * Δ ≤ T)
  have hD := DT_le hΔ (by linarith : 2 * Δ ≤ T)
  have hCL : 0 ≤ C * L := mul_nonneg hC (by linarith)
  have t1 : C * L * (Real.arcosh (T / (T - Δ)) - Real.log (T / (T - Δ)))
      ≤ C * L * (2 * Real.sqrt Δ / Real.sqrt T) := mul_le_mul_of_nonneg_left hA hCL
  have t2 : 2 * (C * L) * DT T (T - Δ) ≤ 2 * (C * L) * (2 / (Real.sqrt Δ * Real.sqrt T)) :=
    mul_le_mul_of_nonneg_left hD (by linarith)
  have t3 : C * L / T + C * ((L + 1) / T) ≤ 3 * (C * L) / Real.sqrt T := by
    have e : C * L / T + C * ((L + 1) / T) = C * (2 * L + 1) / T := by ring
    rw [e]
    calc C * (2 * L + 1) / T ≤ 3 * (C * L) / T := by
          apply div_le_div_of_nonneg_right _ hT0.le
          nlinarith
      _ ≤ 3 * (C * L) / Real.sqrt T := div_le_div_of_nonneg_left (by linarith) hsT hTsT
  calc |Osc S G T - OscInf|
      ≤ 4 * (C * L * (Real.arcosh (T / (T - Δ)) - Real.log (T / (T - Δ)))
          + 2 * (C * L) * DT T (T - Δ)) + 4 * (C * L / T + C * ((L + 1) / T)) := hmain
    _ ≤ 4 * (C * L * (2 * Real.sqrt Δ / Real.sqrt T)
          + 2 * (C * L) * (2 / (Real.sqrt Δ * Real.sqrt T))) + 4 * (3 * (C * L) / Real.sqrt T) := by
        gcongr
    _ = (8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C) * (L / Real.sqrt T) := by
        field_simp
        ring

/-! ## 1ca(iii), the consequences: the minimum's value and the wall's stability -/

/-- **The minimum's value.** If `F = F^s + Osc` on `I` (the split (i)), `T^s ∈ I` minimizes `F^s` and
`T_u ∈ I` minimizes `F` on `I`, and `|Osc − Osc_∞| ≤ ε` on `I`, then
`|min F − (F^s(T^s) + Osc_∞)| ≤ ε` and `F^s(T_u) − F^s(T^s) ≤ Osc(T^s) − Osc(T_u) ≤ 2ε`. -/
theorem wall_value {F Fs O : ℝ → ℝ} {I : Set ℝ} {Ts Tu OscInf ε : ℝ}
    (hsplit : ∀ T ∈ I, F T = Fs T + O T) (hTs : Ts ∈ I) (hTu : Tu ∈ I)
    (hmins : ∀ T ∈ I, Fs Ts ≤ Fs T) (hminu : ∀ T ∈ I, F Tu ≤ F T)
    (hosc : ∀ T ∈ I, |O T - OscInf| ≤ ε) :
    |F Tu - (Fs Ts + OscInf)| ≤ ε ∧ Fs Tu - Fs Ts ≤ O Ts - O Tu ∧ Fs Tu - Fs Ts ≤ 2 * ε := by
  have h1 := hminu Ts hTs
  have h2 := hmins Tu hTu
  have e1 := hsplit Ts hTs
  have e2 := hsplit Tu hTu
  have o1 := abs_le.1 (hosc Ts hTs)
  have o2 := abs_le.1 (hosc Tu hTu)
  refine ⟨abs_le.2 ⟨by linarith [o1.1, o2.1], by linarith [o1.2]⟩, by linarith, by linarith⟩

/-- **The convexity of (ii), quantitatively**: if `f′(a) = 0` and `f″ ≥ κ` on an interval containing
`a, b`, then `f(b) − f(a) ≥ κ(b − a)²/2`. -/
theorem convex_quadratic_lower {f f' f'' : ℝ → ℝ} {lo hi a b κ : ℝ}
    (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hf : ∀ x ∈ Set.Icc lo hi, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc lo hi, HasDerivAt f' (f'' x) x)
    (hκ : ∀ x ∈ Set.Icc lo hi, κ ≤ f'' x) (hcrit : f' a = 0) :
    κ * (b - a) ^ 2 / 2 ≤ f b - f a := by
  set g : ℝ → ℝ := fun x => f x - f a - κ * (x - a) ^ 2 / 2 with hg
  set g' : ℝ → ℝ := fun x => f' x - κ * (x - a) with hg'
  have hgd : ∀ x ∈ Set.Icc lo hi, HasDerivAt g (g' x) x := by
    intro x hx
    have h := ((hf x hx).sub_const (f a)).sub
      ((((hasDerivAt_id x).sub_const a).pow 2).const_mul κ |>.div_const 2)
    refine h.congr_deriv ?_
    simp only [id, hg']
    push_cast
    ring
  have hg'd : ∀ x ∈ Set.Icc lo hi, HasDerivAt g' (f'' x - κ) x := by
    intro x hx
    have h := (hf' x hx).sub (((hasDerivAt_id x).sub_const a).const_mul κ)
    refine h.congr_deriv ?_
    simp
  have hmono : MonotoneOn g' (Set.Icc lo hi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc lo hi) (f' := fun x => f'' x - κ)
    · intro x hx; exact (hg'd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hg'd x (Set.Ioo_subset_Icc_self hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      linarith [hκ x (Set.Ioo_subset_Icc_self hx)]
  have hg'a : g' a = 0 := by simp [hg', hcrit]
  have hga : g a = 0 := by simp [hg]
  have key : 0 ≤ g b := by
    rcases le_total a b with hab | hab
    · have hm : MonotoneOn g (Set.Icc a b) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := g')
        · intro x hx
          exact (hgd x ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hgd x ⟨le_trans ha.1 hx.1.le, le_trans hx.2.le hb.2⟩).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have := hmono ha ⟨le_trans ha.1 hx.1.le, le_trans hx.2.le hb.2⟩ hx.1.le
          linarith
      have := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
      linarith
    · have hm : AntitoneOn g (Set.Icc b a) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc b a) (f' := g')
        · intro x hx
          exact (hgd x ⟨le_trans hb.1 hx.1, le_trans hx.2 ha.2⟩).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hgd x ⟨le_trans hb.1 hx.1.le, le_trans hx.2.le ha.2⟩).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have := hmono ⟨le_trans hb.1 hx.1.le, le_trans hx.2.le ha.2⟩ ha hx.2.le
          linarith
      have := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
      linarith
  simp only [hg] at key
  linarith

/-- **1ca(iii): the unlocking height's law is the smooth wall's.** With the split `F = F^s + Osc`
on `J = [lo, hi]`, `F^s′(T^s) = 0`, `F^s″ ≥ κ > 0` on `J`, `T_u` a minimizer of `F` on `J`, and
`|Osc − Osc_∞| ≤ ε` on `J`: `(T_u − T^s)² ≤ 4ε/κ` and `|min F − (F^s(T^s) + Osc_∞)| ≤ ε`. With
`ε = O(ln T/√T)` (`osc_log`) and `κ = (1 − o(1))/T` this is `|T_u − T^s| = O(T^{1/4}(ln T)^{1/2})`. -/
theorem wall_stability {F Fs Fs' Fs'' O : ℝ → ℝ} {lo hi Ts Tu OscInf ε κ : ℝ}
    (hκ0 : 0 < κ) (hTs : Ts ∈ Set.Icc lo hi) (hTu : Tu ∈ Set.Icc lo hi)
    (hf : ∀ x ∈ Set.Icc lo hi, HasDerivAt Fs (Fs' x) x)
    (hf' : ∀ x ∈ Set.Icc lo hi, HasDerivAt Fs' (Fs'' x) x)
    (hκ : ∀ x ∈ Set.Icc lo hi, κ ≤ Fs'' x) (hcrit : Fs' Ts = 0)
    (hsplit : ∀ T ∈ Set.Icc lo hi, F T = Fs T + O T)
    (hminu : ∀ T ∈ Set.Icc lo hi, F Tu ≤ F T)
    (hosc : ∀ T ∈ Set.Icc lo hi, |O T - OscInf| ≤ ε) :
    |F Tu - (Fs Ts + OscInf)| ≤ ε ∧ (Tu - Ts) ^ 2 ≤ 4 * ε / κ := by
  have hmins : ∀ T ∈ Set.Icc lo hi, Fs Ts ≤ Fs T := by
    intro T hT
    have := convex_quadratic_lower hTs hT hf hf' hκ hcrit
    have : 0 ≤ κ * (T - Ts) ^ 2 / 2 := by positivity
    linarith
  obtain ⟨hv, -, h2ε⟩ := wall_value hsplit hTs hTu hmins hminu hosc
  refine ⟨hv, ?_⟩
  have hq := convex_quadratic_lower hTs hTu hf hf' hκ hcrit
  rw [le_div_iff₀ hκ0]
  nlinarith

/-- **1ca(iii) for the paper's `F_k^s`**: on a window `J = [lo, hi]` past the inflection of `F_k^s′`
(`T·G(lo) < 1`), `F_k^s″ ≥ κ := (1 − T·G(lo))/hi` on `J`, by `T·F″ = 1 − T·G` and `T·G` decreasing
(1ca(ii), with `R < 1` from `rise_lt_fall`). So if the smooth wall `T^s ∈ J` is a zero of `F_k^s′`,
`F_k = F_k^s + Osc` on `J`, `T_u` minimizes `F_k` on `J` and `|Osc − Osc_∞| ≤ ε` on `J`, then
`|F_k(T_u) − (F_k^s(T^s) + Osc_∞)| ≤ ε` and `(T_u − T^s)² ≤ 4ε·hi/(1 − T·G(lo))`. -/
theorem wall_stability_Fs {G a L lo hi Ts Tu OscInf ε : ℝ} {H : Finset ℝ} {F O : ℝ → ℝ}
    (hG14 : 14 ≤ G) (hGe : G ≤ 2 * π * Real.exp 1) (hLG : G ≤ L)
    (hH : ∀ h ∈ H, 0 < h ∧ h ≤ L) (hlo : L < lo) (hTG : TG G H lo < 1)
    (hTs : Ts ∈ Set.Icc lo hi) (hTu : Tu ∈ Set.Icc lo hi)
    (hcrit : Fp G (2 * π * Real.exp (2 * a)) H Ts = 0)
    (hsplit : ∀ T ∈ Set.Icc lo hi, F T = Fs G a H T + O T)
    (hminu : ∀ T ∈ Set.Icc lo hi, F Tu ≤ F T)
    (hosc : ∀ T ∈ Set.Icc lo hi, |O T - OscInf| ≤ ε) :
    |F Tu - (Fs G a H Ts + OscInf)| ≤ ε ∧
      (Tu - Ts) ^ 2 ≤ 4 * ε * hi / (1 - TG G H lo) := by
  have S : Setup G L H := ⟨by linarith, hLG, fun h hh => ⟨(hH h hh).1.le, (hH h hh).2⟩⟩
  have hT₀ : 0 < 2 * π * Real.exp (2 * a) := by positivity
  have hlohi : lo ≤ hi := le_trans hTs.1 hTs.2
  have hlo0 : 0 < lo := by linarith
  have hhi0 : 0 < hi := by linarith
  have hR : ∀ T, L < T → rise G T < fall G T := fun T hT => rise_lt_fall hG14 hGe (by linarith)
  have hanti := TG_strictAntiOn S hGe hR
  have hmem : ∀ x ∈ Set.Icc lo hi, L < x := fun x hx => lt_of_lt_of_le hlo hx.1
  have hκ0 : 0 < (1 - TG G H lo) / hi := div_pos (by linarith) hhi0
  have hFpp : ∀ x ∈ Set.Icc lo hi, (1 - TG G H lo) / hi ≤ Fpp G H x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hlo0 hx.1
    have hTGx : TG G H x ≤ TG G H lo :=
      hanti.antitoneOn (Set.mem_Ioi.2 hlo) (Set.mem_Ioi.2 (hmem x hx)) hx.1
    have e := T_mul_Fpp G H hx0.ne'
    have h1 : (1 - TG G H lo) / hi ≤ (1 - TG G H x) / hi :=
      div_le_div_of_nonneg_right (by linarith) hhi0.le
    have h2 : (1 - TG G H x) / hi ≤ (1 - TG G H x) / x :=
      div_le_div_of_nonneg_left (by linarith) hx0 hx.2
    have h3 : (1 - TG G H x) / x = Fpp G H x := by rw [← e]; field_simp
    linarith
  have hf : ∀ x ∈ Set.Icc lo hi,
      HasDerivAt (Fs G a H) (Fp G (2 * π * Real.exp (2 * a)) H x) x :=
    fun x hx => hasDerivAt_Fs (by linarith) hLG hH (hmem x hx)
  have hf' : ∀ x ∈ Set.Icc lo hi,
      HasDerivAt (Fp G (2 * π * Real.exp (2 * a)) H) (Fpp G H x) x :=
    fun x hx => hasDerivAt_Fp S hT₀ (hmem x hx)
  obtain ⟨hv, hq⟩ := wall_stability hκ0 hTs hTu hf hf' hFpp hcrit hsplit hminu hosc
  refine ⟨hv, ?_⟩
  have e : 4 * ε / ((1 - TG G H lo) / hi) = 4 * ε * hi / (1 - TG G H lo) := by
    field_simp
  rw [← e]
  exact hq

/-- **1ca(iii), assembled from the named classical inputs**: with von Mangoldt's `|S(t)| ≤ C ln t`
and Littlewood's `|S₁(t)| ≤ C ln t` on `[γ₁, ∞)`, `Osc_∞` exists, and for any window
`J = [lo, hi]` with `lo ≥ γ₁ + 2Δ` past the inflection (`T·G(lo) < 1`), containing the smooth
wall `T^s` and a minimizer `T_u` on `J` of `F_k = F_k^s + Osc`:
`|F_k(T_u) − (F_k^s(T^s) + Osc_∞)| ≤ K ln(hi)/√lo` and
`(T_u − T^s)² ≤ 4K ln(hi)/√lo · hi/(1 − T·G(lo))`, `K = 8C√Δ + 16C/√Δ + 12C`. For `J` near `T`
and `T·G(lo)` bounded away from 1 this is the paper's `|T_u − T^s| = O(T^{1/4}(ln T)^{1/2})`. -/
theorem wall_law_Fs {S : ℝ → ℝ} (hS : OscS S) {G a L Δ C lo hi Ts Tu : ℝ} {H : Finset ℝ}
    {F : ℝ → ℝ} (hG14 : 14 ≤ G) (hGe : G ≤ 2 * π * Real.exp 1) (hLG : G ≤ L)
    (hH : ∀ h ∈ H, 0 < h ∧ h ≤ L) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (hSlog : ∀ t, G ≤ t → |S t| ≤ C * Real.log t)
    (hS1log : ∀ t, G ≤ t → |S1 S G t| ≤ C * Real.log t)
    (hlo : L < lo) (hloΔ : G + 2 * Δ ≤ lo) (hTG : TG G H lo < 1)
    (hTs : Ts ∈ Set.Icc lo hi) (hTu : Tu ∈ Set.Icc lo hi)
    (hcrit : Fp G (2 * π * Real.exp (2 * a)) H Ts = 0)
    (hsplit : ∀ T ∈ Set.Icc lo hi, F T = Fs G a H T + Osc S G T)
    (hminu : ∀ T ∈ Set.Icc lo hi, F Tu ≤ F T) :
    ∃ OscInf : ℝ, Tendsto (fun X => ∫ r in G..X, S r * (4 / r)) atTop (𝓝 OscInf) ∧
      |F Tu - (Fs G a H Ts + OscInf)|
        ≤ (8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C) * (Real.log hi / Real.sqrt lo) ∧
      (Tu - Ts) ^ 2 ≤ 4 * ((8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C)
        * (Real.log hi / Real.sqrt lo)) * hi / (1 - TG G H lo) := by
  obtain ⟨OscInf, hInf, hb⟩ := osc_log hS (by linarith : (1 : ℝ) ≤ G) hΔ hC hSlog hS1log
  have hK : 0 ≤ 8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C := by positivity
  have hosc : ∀ T ∈ Set.Icc lo hi, |Osc S G T - OscInf|
      ≤ (8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C) * (Real.log hi / Real.sqrt lo) := by
    intro T hT
    have hT0 : 0 < T := by linarith [hT.1]
    have hslo : 0 < Real.sqrt lo := Real.sqrt_pos.2 (by linarith)
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith [hT.1])
    have hloghi : Real.log T ≤ Real.log hi := Real.log_le_log hT0 hT.2
    have hsq : Real.sqrt lo ≤ Real.sqrt T := Real.sqrt_le_sqrt hT.1
    have hr : Real.log T / Real.sqrt T ≤ Real.log hi / Real.sqrt lo :=
      div_le_div₀ (le_trans hlogT hloghi) hloghi hslo hsq
    exact le_trans (hb T (by linarith [hT.1]) (by linarith [hT.1]))
      (mul_le_mul_of_nonneg_left hr hK)
  obtain ⟨hv, hq⟩ := wall_stability_Fs hG14 hGe hLG hH hlo hTG hTs hTu hcrit hsplit hminu hosc
  exact ⟨OscInf, hInf, hv, hq⟩

end Pilot1ca

#print axioms Pilot1ca.integral_DT
#print axioms Pilot1ca.DTd_nonneg
#print axioms Pilot1ca.tail_ibp
#print axioms Pilot1ca.oscInf_eq
#print axioms Pilot1ca.osc_decomp
#print axioms Pilot1ca.inner_bound
#print axioms Pilot1ca.osc_bound
#print axioms Pilot1ca.near_term_le
#print axioms Pilot1ca.DT_le
#print axioms Pilot1ca.Ioi_log_div_sq
#print axioms Pilot1ca.osc_log
#print axioms Pilot1ca.wall_value
#print axioms Pilot1ca.convex_quadratic_lower
#print axioms Pilot1ca.wall_stability
#print axioms Pilot1ca.wall_stability_Fs
#print axioms Pilot1ca.wall_law_Fs
