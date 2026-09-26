import Mathlib
import Osc

/-! # Theorem 1ca(i): the split `F_k = F_k^s + Osc`, and 1ca(i)–(iii) assembled

`N₀`, `w_T`, `F_k^s` (`Fs`) and the smooth-wall machinery come from `T1ca.lean`; `D_T`, `Osc`, `S₁`
and the oscillation bound from `Osc.lean`. -/

open Real MeasureTheory intervalIntegral
open Filter Topology

noncomputable section

namespace Pilot1ca

/-! ## The continuum `I(T) = ∫₀^T N₀ w_T = T[ln(T/2π) − 1 − ln 2]` -/

theorem sin_image_Ioo {T : ℝ} (hT : 0 < T) :
    (fun θ => T * Real.sin θ) '' Set.Ioo 0 (π / 2) = Set.Ioo 0 T := by
  ext y
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have hs0 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hs1 : Real.sin θ < 1 := by
      have := Real.strictMonoOn_sin ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
        ⟨by linarith [Real.pi_pos], le_rfl⟩ hθ.2
      rwa [Real.sin_pi_div_two] at this
    exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨h0, h1⟩
    have hy : y / T < 1 := by rw [div_lt_one hT]; exact h1
    have hy0 : 0 < y / T := div_pos h0 hT
    refine ⟨Real.arcsin (y / T), ⟨Real.arcsin_pos.2 hy0, Real.arcsin_lt_pi_div_two.2 hy⟩, ?_⟩
    show T * Real.sin (Real.arcsin (y / T)) = y
    rw [Real.sin_arcsin (by linarith) hy.le]
    field_simp

theorem sin_injOn {T : ℝ} (hT : 0 < T) :
    Set.InjOn (fun θ => T * Real.sin θ) (Set.Ioo 0 (π / 2)) := by
  intro x hx y hy hxy
  have hs : Real.sin x = Real.sin y := by
    have := mul_left_cancel₀ hT.ne' hxy
    exact this
  exact Real.strictMonoOn_sin.injOn ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
    ⟨by linarith [hy.1, Real.pi_pos], hy.2.le⟩ hs

/-- On `(0, π/2)`, `|T cos θ|·N₀(T sin θ) w_T(T sin θ) = (2T/π)(ln(T sin θ/2π) − 1)`. -/
theorem N0wT_sin {T θ : ℝ} (hT : 0 < T) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |T * Real.cos θ| • (N0 (T * Real.sin θ) * wT T (T * Real.sin θ))
      = 2 * T / π * (Real.log (T * Real.sin θ / (2 * π)) - 1) := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hsq : Real.sqrt (1 - (T * Real.sin θ) ^ 2 / T ^ 2) = Real.cos θ := by
    rw [show 1 - (T * Real.sin θ) ^ 2 / T ^ 2 = Real.cos θ ^ 2 by
      rw [Real.cos_sq']; field_simp]
    exact Real.sqrt_sq hc.le
  rw [smul_eq_mul, abs_of_pos (by positivity), N0, wT, hsq]
  field_simp
  ring

theorem I_integrand_integrableOn {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun θ => 2 * T / π * (Real.log (T * Real.sin θ / (2 * π)) - 1))
      (Set.Ioo 0 (π / 2)) := by
  have hls : IntegrableOn (fun θ => Real.log (Real.sin θ)) (Set.Ioo 0 (π / 2)) := by
    have h := (intervalIntegrable_log_sin (a := 0) (b := π / 2)).1
    exact (h.mono_set Set.Ioo_subset_Ioc_self)
  have hc : IntegrableOn (fun _ : ℝ => 2 * T / π * (Real.log T - Real.log (2 * π) - 1))
      (Set.Ioo 0 (π / 2)) := integrableOn_const (by simp)
  refine (hc.add (hls.const_mul (2 * T / π))).congr_fun (fun θ hθ => ?_) measurableSet_Ioo
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  show 2 * T / π * (Real.log T - Real.log (2 * π) - 1) + 2 * T / π * Real.log (Real.sin θ)
    = 2 * T / π * (Real.log (T * Real.sin θ / (2 * π)) - 1)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hT.ne' hs.ne']
  ring

/-- **The continuum of the zero sum** (1bs(ii), used in 1ca(i)): `N₀ w_T` is integrable on `[0, T]`
and `∫₀^T N₀(r) w_T(r) dr = T[ln(T/2π) − 1 − ln 2]`, by `r = T sin θ` and
`∫₀^{π/2} ln sin θ dθ = −(π/2) ln 2`. -/
theorem I_closed {T : ℝ} (hT : 0 < T) :
    IntervalIntegrable (fun r => N0 r * wT T r) volume 0 T ∧
      ∫ r in (0 : ℝ)..T, N0 r * wT T r = T * (Real.log (T / (2 * π)) - 1 - Real.log 2) := by
  have hmeas : MeasurableSet (Set.Ioo (0 : ℝ) (π / 2)) := measurableSet_Ioo
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivWithinAt (fun θ => T * Real.sin θ) (T * Real.cos x) (Set.Ioo 0 (π / 2)) x := by
    intro x _
    exact ((Real.hasDerivAt_sin x).const_mul T).hasDerivWithinAt
  have hcongr : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |T * Real.cos θ| • (N0 (T * Real.sin θ) * wT T (T * Real.sin θ))
        = 2 * T / π * (Real.log (T * Real.sin θ / (2 * π)) - 1) :=
    fun θ hθ => N0wT_sin hT hθ
  -- integrability on (0, T)
  have hint : IntegrableOn (fun r => N0 r * wT T r) (Set.Ioo 0 T) := by
    rw [← sin_image_Ioo hT,
      integrableOn_image_iff_integrableOn_abs_deriv_smul hmeas hderiv (sin_injOn hT)]
    exact (I_integrand_integrableOn hT).congr_fun (fun θ hθ => (hcongr θ hθ).symm) hmeas
  have hint' : IntervalIntegrable (fun r => N0 r * wT T r) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top).2 hint
  refine ⟨hint', ?_⟩
  -- the value
  rw [intervalIntegral.integral_of_le hT.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← sin_image_Ioo hT, integral_image_eq_integral_abs_deriv_smul hmeas hderiv (sin_injOn hT),
    MeasureTheory.setIntegral_congr_fun hmeas hcongr]
  have hls : ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Real.log (Real.sin θ) = -Real.log 2 * π / 2 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      (by positivity), integral_log_sin_zero_pi_div_two]
  have hsplit : ∫ θ in Set.Ioo (0 : ℝ) (π / 2), 2 * T / π * (Real.log (T * Real.sin θ / (2 * π)) - 1)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          (2 * T / π * (Real.log T - Real.log (2 * π) - 1) + 2 * T / π * Real.log (Real.sin θ)) := by
    apply MeasureTheory.setIntegral_congr_fun hmeas
    intro θ hθ
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    show 2 * T / π * (Real.log (T * Real.sin θ / (2 * π)) - 1)
      = 2 * T / π * (Real.log T - Real.log (2 * π) - 1) + 2 * T / π * Real.log (Real.sin θ)
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hT.ne' hs.ne']
    ring
  have hls_int : IntegrableOn (fun θ => Real.log (Real.sin θ)) (Set.Ioo 0 (π / 2)) :=
    (intervalIntegrable_log_sin (a := 0) (b := π / 2)).1.mono_set Set.Ioo_subset_Ioc_self
  have hc : IntegrableOn (fun _ : ℝ => 2 * T / π * (Real.log T - Real.log (2 * π) - 1))
      (Set.Ioo 0 (π / 2)) := integrableOn_const (by simp)
  rw [hsplit, MeasureTheory.integral_add hc (hls_int.const_mul _),
    MeasureTheory.integral_const_mul (2 * T / π) (fun θ => Real.log (Real.sin θ)), hls,
    MeasureTheory.setIntegral_const]
  rw [smul_eq_mul, Real.volume_real_Ioo_of_le (by positivity), Real.log_div hT.ne' (by positivity)]
  field_simp
  ring

/-- **`∫_b^T w_T = 4 arccosh(T/b)`** for `0 < b < T` (an improper integral at `T`), with
`w_T` integrable on `[b, T]`. -/
theorem integral_wT {T b : ℝ} (hb : 0 < b) (hbT : b < T) :
    IntervalIntegrable (wT T) volume b T ∧ ∫ r in b..T, wT T r = 4 * Real.arcosh (T / b) := by
  obtain ⟨hDv, hDi⟩ := integral_DT hb hbT
  have hinv : IntervalIntegrable (fun r : ℝ => 1 / r) volume b T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbT.le]
    exact continuousOn_const.div continuousOn_id (fun x hx => (lt_of_lt_of_le hb hx.1).ne')
  have heq : ∀ r ∈ Set.uIcc b T, wT T r = 4 * (1 / r) + 4 * DT T r := by
    intro r hr
    rw [Set.uIcc_of_le hbT.le] at hr
    rw [wT_eq T (lt_of_lt_of_le hb hr.1).ne']
    ring
  have hi : IntervalIntegrable (fun r => 4 * (1 / r) + 4 * DT T r) volume b T :=
    (hinv.const_mul 4).add (hDi.const_mul 4)
  refine ⟨hi.congr (fun r hr => (heq r (Set.uIoc_subset_uIcc hr)).symm) , ?_⟩
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_add (hinv.const_mul 4)
    (hDi.const_mul 4), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one_div_of_pos hb (by linarith), hDv]
  ring

/-! ## The zero model and the split (i) -/

/-- The zero count `N(r) = #{i : γ i < r}` of a family of ordinates `γ` (with multiplicity). -/
def Ncnt {ι : Type*} (γ : ι → ℝ) (r : ℝ) : ℝ := (({i | γ i < r} : Set ι).ncard : ℝ)

/-- **Theorem 1by's unlocking functional**, the zero sum over the family `γ`:
`F_k(T) = 4Σ_{γ<T} arccosh(T/γ) − 2aT + 4Σ_h arccosh(T/h)`. -/
def Fk {ι : Type*} (γ : ι → ℝ) (a : ℝ) (H : Finset ℝ) (T : ℝ) : ℝ :=
  4 * (∑ᶠ i ∈ {i | γ i < T}, Real.arcosh (T / γ i)) - 2 * a * T
    + 4 * ∑ h ∈ H, Real.arcosh (T / h)

/-- 1bs's oscillation `S = N − N₀ − 7/8`. -/
def Sz {ι : Type*} (γ : ι → ℝ) (r : ℝ) : ℝ := Ncnt γ r - N0 r - 7 / 8

theorem Ncnt_eq_sum {ι : Type*} {γ : ι → ℝ} {T r : ℝ} (hfin : ({i | γ i < T} : Set ι).Finite)
    (hr : r ≤ T) :
    Ncnt γ r = ∑ i ∈ hfin.toFinset, (if γ i < r then (1 : ℝ) else 0) := by
  unfold Ncnt
  have hsub : ({i | γ i < r} : Set ι) = ↑(hfin.toFinset.filter (fun i => γ i < r)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    constructor
    · intro h; exact ⟨lt_of_lt_of_le h hr, h⟩
    · intro h; exact h.2
  rw [hsub, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  rfl

/-- **The Stieltjes step** (1bs(ii)): `∫_{γ₁}^T N w_T = 4Σ_{γ<T} arccosh(T/γ)` for a family with every
ordinate `≥ γ₁`, since `4 arccosh(T/γ) = ∫_γ^T w_T`. -/
theorem integral_Ncnt_wT {ι : Type*} {γ : ι → ℝ} {G T : ℝ}
    (hfin : ({i | γ i < T} : Set ι).Finite) (hγ : ∀ i, G ≤ γ i) (hG : 0 < G) (hGT : G < T) :
    IntervalIntegrable (fun r => Ncnt γ r * wT T r) volume G T ∧
      ∫ r in G..T, Ncnt γ r * wT T r = 4 * ∑ i ∈ hfin.toFinset, Real.arcosh (T / γ i) := by
  obtain ⟨hwi, -⟩ := integral_wT hG hGT
  have hwi' : IntegrableOn (wT T) (Set.Ioc G T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hGT.le).1 hwi
  have hterm : ∀ i ∈ hfin.toFinset,
      IntegrableOn (Set.indicator (Set.Ioi (γ i)) (wT T)) (Set.Ioc G T) :=
    fun i _ => hwi'.indicator measurableSet_Ioi
  have hpt : ∀ r ∈ Set.Ioc G T, Ncnt γ r * wT T r
      = ∑ i ∈ hfin.toFinset, Set.indicator (Set.Ioi (γ i)) (wT T) r := by
    intro r hr
    rw [Ncnt_eq_sum hfin hr.2, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : γ i < r
    · rw [ite_eq_left h, one_mul, Set.indicator_of_mem (Set.mem_Ioi.2 h)]
    · rw [ite_eq_right h, zero_mul, Set.indicator_of_notMem (by simpa using h)]
  have hsum : IntegrableOn (fun r => ∑ i ∈ hfin.toFinset, Set.indicator (Set.Ioi (γ i)) (wT T) r)
      (Set.Ioc G T) := integrable_finsetSum _ hterm
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hGT.le]
    exact hsum.congr_fun (fun r hr => (hpt r hr).symm) measurableSet_Ioc
  · rw [intervalIntegral.integral_of_le hGT.le,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt,
      MeasureTheory.integral_finsetSum _ hterm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hiT : γ i < T := (Set.Finite.mem_toFinset hfin).1 hi
    have hi0 : 0 < γ i := lt_of_lt_of_le hG (hγ i)
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioc_inter_Ioi,
      max_eq_right (hγ i), ← intervalIntegral.integral_of_le hiT.le,
      (integral_wT hi0 hiT).2]

/-- **1ca(i), the split, an identity**: for a locally finite family of zero ordinates `γ i ≥ γ₁ > 0`
(with multiplicity) and every `T > γ₁`, `F_k(T) = F_k^s(T) + Osc(T)` with `S = N − N₀ − 7/8`. -/
theorem split {ι : Type*} {γ : ι → ℝ} {G a T : ℝ} {H : Finset ℝ}
    (hfin : ({i | γ i < T} : Set ι).Finite) (hγ : ∀ i, G ≤ γ i) (hG : 0 < G) (hGT : G < T) :
    Fk γ a H T = Fs G a H T + Osc (Sz γ) G T := by
  have hT : 0 < T := by linarith
  obtain ⟨hNi, hNv⟩ := integral_Ncnt_wT hfin hγ hG hGT
  obtain ⟨hIi, hIv⟩ := I_closed hT
  obtain ⟨hwi, hwv⟩ := integral_wT hG hGT
  have hI0G : IntervalIntegrable (fun r => N0 r * wT T r) volume 0 G :=
    hIi.mono_set (by
      rw [Set.uIcc_of_le hG.le, Set.uIcc_of_le hT.le]; exact Set.Icc_subset_Icc le_rfl hGT.le)
  have hIGT : IntervalIntegrable (fun r => N0 r * wT T r) volume G T :=
    hIi.mono_set (by
      rw [Set.uIcc_of_le hGT.le, Set.uIcc_of_le hT.le]; exact Set.Icc_subset_Icc hG.le le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI0G hIGT
  have hosc : Osc (Sz γ) G T = (∫ r in G..T, Ncnt γ r * wT T r) - (∫ r in G..T, N0 r * wT T r)
      - 7 / 8 * ∫ r in G..T, wT T r := by
    have e : (fun r => Sz γ r * wT T r)
        = fun r => (Ncnt γ r * wT T r - N0 r * wT T r) - 7 / 8 * wT T r := by
      funext r; unfold Sz; ring
    unfold Osc
    rw [e, intervalIntegral.integral_sub (hNi.sub hIGT) (hwi.const_mul _),
      intervalIntegral.integral_sub hNi hIGT, intervalIntegral.integral_const_mul]
  have hB : ∑ᶠ i ∈ {i | γ i < T}, Real.arcosh (T / γ i)
      = ∑ i ∈ hfin.toFinset, Real.arcosh (T / γ i) :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  unfold Fk Fs
  rw [hB, hosc, hwv]
  linarith [hNv, hIv, hadd]

theorem Ncnt_mono {ι : Type*} {γ : ι → ℝ} (hfin : ∀ T, ({i | γ i < T} : Set ι).Finite) :
    Monotone (Ncnt γ) := by
  intro r r' h
  unfold Ncnt
  exact_mod_cast Set.ncard_le_ncard (fun i (hi : γ i < r) => lt_of_lt_of_le hi h) (hfin r')

/-- `S = N − N₀ − 7/8` meets the standing hypotheses of 1ca(iii): measurable, locally integrable, and
continuous off the countable set of `N`'s jumps. -/
theorem oscS_Sz {ι : Type*} {γ : ι → ℝ} (hfin : ∀ T, ({i | γ i < T} : Set ι).Finite) :
    OscS (Sz γ) := by
  have hm := Ncnt_mono hfin
  refine ⟨?_, ?_, ?_⟩
  · show Measurable (fun r => Ncnt γ r - N0 r - 7 / 8)
    exact (hm.measurable.sub continuous_N0.measurable).sub measurable_const
  · intro a b
    exact (hm.intervalIntegrable.sub (continuous_N0.intervalIntegrable a b)).sub
      intervalIntegrable_const
  · refine ⟨{x | ¬ContinuousAt (Ncnt γ) x}, hm.countable_not_continuousAt, fun x hx => ?_⟩
    have hc : ContinuousAt (Ncnt γ) x := by
      simp only [Set.mem_ofPred_eq, not_not] at hx; exact hx
    exact (hc.sub continuous_N0.continuousAt).sub continuousAt_const

/-- **1ca(i)–(iii) assembled, for the zero-sum functional itself.** Let `γ` be a locally finite family
of zero ordinates, all `≥ γ₁ ∈ [14, 2πe]` (with multiplicity), whose oscillation `S = N − N₀ − 7/8`
obeys von Mangoldt's `|S(t)| ≤ C ln t` and Littlewood's `|S₁(t)| ≤ C ln t` on `[γ₁, ∞)` (the named
classical inputs). Take any hole set in `(0, L]`, a window `J = [lo, hi]` with `lo > L`,
`lo ≥ γ₁ + 2Δ` and `T·G(lo) < 1`, the smooth wall `T^s ∈ J` (`F_k^s′(T^s) = 0`), and `T_u ∈ J` minimizing
the unlocking functional `F_k` on `J`. Then `Osc_∞` exists and
`|F_k(T_u) − (F_k^s(T^s) + Osc_∞)| ≤ K ln(hi)/√lo`, `(T_u − T^s)² ≤ 4K ln(hi)/√lo · hi/(1 − T·G(lo))`,
`K = 8C√Δ + 16C/√Δ + 12C`. -/
theorem wall_law_zeros {ι : Type*} {γ : ι → ℝ} {G a L Δ C lo hi Ts Tu : ℝ} {H : Finset ℝ}
    (hfin : ∀ T, ({i | γ i < T} : Set ι).Finite) (hγ : ∀ i, G ≤ γ i)
    (hG14 : 14 ≤ G) (hGe : G ≤ 2 * π * Real.exp 1) (hLG : G ≤ L)
    (hH : ∀ h ∈ H, 0 < h ∧ h ≤ L) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (hSlog : ∀ t, G ≤ t → |Sz γ t| ≤ C * Real.log t)
    (hS1log : ∀ t, G ≤ t → |S1 (Sz γ) G t| ≤ C * Real.log t)
    (hlo : L < lo) (hloΔ : G + 2 * Δ ≤ lo) (hTG : TG G H lo < 1)
    (hTs : Ts ∈ Set.Icc lo hi) (hTu : Tu ∈ Set.Icc lo hi)
    (hcrit : Fp G (2 * π * Real.exp (2 * a)) H Ts = 0)
    (hminu : ∀ T ∈ Set.Icc lo hi, Fk γ a H Tu ≤ Fk γ a H T) :
    ∃ OscInf : ℝ, Tendsto (fun X => ∫ r in G..X, Sz γ r * (4 / r)) atTop (𝓝 OscInf) ∧
      |Fk γ a H Tu - (Fs G a H Ts + OscInf)|
        ≤ (8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C) * (Real.log hi / Real.sqrt lo) ∧
      (Tu - Ts) ^ 2 ≤ 4 * ((8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C)
        * (Real.log hi / Real.sqrt lo)) * hi / (1 - TG G H lo) :=
  wall_law_Fs (oscS_Sz hfin) hG14 hGe hLG hH hΔ hC hSlog hS1log hlo hloΔ hTG hTs hTu hcrit
    (fun T hT => split (hfin T) hγ (by linarith) (by linarith [hT.1])) hminu

end Pilot1ca

#print axioms Pilot1ca.I_closed
#print axioms Pilot1ca.integral_wT
#print axioms Pilot1ca.integral_Ncnt_wT
#print axioms Pilot1ca.split
#print axioms Pilot1ca.oscS_Sz
#print axioms Pilot1ca.wall_law_zeros
