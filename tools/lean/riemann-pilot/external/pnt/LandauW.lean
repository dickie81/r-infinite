/-
# The last bit, step R3: Landau's lemma for a general width (round 215)

Plain statements.
* `WidthOK w C_w`: `w` is positive, at most 1 and non-increasing on `[1, ∞)`, with
  `log(1/w(L)) ≤ C_w(1 + log L)`.
* `GrowthW w K`: `|ζ(σ+it)| ≤ K(log|t|)^K` for `|t| ≥ 3`, `1 − w(log|t|) ≤ σ ≤ 2`.
* `zero_gap_explicitW`: then zeros at `|t| ≥ 4` satisfy `1 − β ≥ (3/13)·w(Lg 2t)/(4N(1 + log Lg 2t))`.

This is round 193's argument (`Landau.lean`) with the radius `¼(log|t|)^{−a}` replaced by
`¼·w(log(|t|+1))`; the proofs are the same, and use only the four properties above.
-/
import KVBridge
import VinoKV

open Nat Filter Topology Set Function Complex Real ComplexConjugate MeasureTheory

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

namespace LandauW

open Landau

/-- Admissible widths. -/
structure WidthOK (w : ℝ → ℝ) (Cw : ℝ) : Prop where
  pos : ∀ L, 1 ≤ L → 0 < w L
  le1 : ∀ L, 1 ≤ L → w L ≤ 1
  anti : ∀ L L', 1 ≤ L → L ≤ L' → w L' ≤ w L
  logb : ∀ L, 1 ≤ L → -Real.log (w L) ≤ Cw * (1 + Real.log L)
  Cw_nonneg : 0 ≤ Cw

/-- Polylog growth on the region of width `w`. -/
def GrowthW (w : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ t : ℝ, 3 ≤ |t| → ∀ σ : ℝ, 1 - w (Real.log |t|) ≤ σ → σ ≤ 2 →
    ‖ζ (σ + t * I)‖ ≤ K * Real.log |t| ^ K

noncomputable def radW (w : ℝ → ℝ) (T : ℝ) : ℝ := 1 / 4 * w (Lg T)

lemma radW_pos {w : ℝ → ℝ} {Cw : ℝ} (hw : WidthOK w Cw) (T : ℝ) (hT : 4 ≤ |T|) :
    0 < radW w T := by
  unfold radW; have := hw.pos _ (Lg_gt_one hT).le; positivity

lemma radW_le {w : ℝ → ℝ} {Cw : ℝ} (hw : WidthOK w Cw) {T : ℝ} (hT : 4 ≤ |T|) :
    radW w T ≤ 1 / 4 := by
  unfold radW; have := hw.le1 _ (Lg_gt_one hT).le; linarith

lemma radW_anti {w : ℝ → ℝ} {Cw : ℝ} (hw : WidthOK w Cw) {T U : ℝ} (hT : 4 ≤ |T|)
    (h : |T| ≤ |U|) : radW w U ≤ radW w T := by
  unfold radW
  have := hw.anti _ _ (Lg_gt_one hT).le (Lg_mono hT h)
  linarith

theorem apply_localW {w : ℝ → ℝ} {Cw K : ℝ} (hw : WidthOK w Cw) (hK : 0 < K) (hG : GrowthW w K) {T δ : ℝ}
    (hT : 4 ≤ |T|) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    radW w T * -(ζ' ((1 + δ : ℝ) + T * I) / ζ ((1 + δ : ℝ) + T * I)).re ≤
        Kc * Real.log (Bnd K δ T) ∧
    ∀ β : ℝ, ζ (β + T * I) = 0 → 1 + δ - β ≤ radW w T / 2 →
      radW w T * -(ζ' ((1 + δ : ℝ) + T * I) / ζ ((1 + δ : ℝ) + T * I)).re ≤
        Kc * Real.log (Bnd K δ T) - radW w T / (1 + δ - β) := by
  set s₀ : ℂ := ((1 + δ : ℝ) : ℂ) + T * I with hs₀def
  have hre : s₀.re = 1 + δ := by simp [hs₀def]
  have him : s₀.im = T := by simp [hs₀def]
  set ρ := radW w T with hρdef
  have hρ := radW_pos hw T hT
  have hρ4 := radW_le hw hT
  have hL := Lg_gt_one hT
  have hζδ : 1 ≤ ‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖ := by
    have h := inv_norm_zeta_le (s := s₀) (by rw [hre]; linarith)
    rw [hre] at h
    have hz : 0 < ‖ζ s₀‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; linarith))
    rw [div_le_iff₀ hz] at h; linarith
  have hB : 1 < Bnd K δ T := by
    unfold Bnd; have : 0 ≤ K * Lg T ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by positivity
    linarith
  have hpole : ∀ z : ℂ, ‖z‖ < 2 → s₀ + ρ * z ≠ 1 := by
    intro z hz h
    have := congrArg Complex.im h
    simp only [add_im, him, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im] at this
    have hzi : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have : |T| ≤ ρ * |z.im| := by
      rw [show T = -(ρ * z.im) by linarith, abs_neg, abs_mul, abs_of_pos hρ]
    nlinarith [abs_nonneg z.im]
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 3 / 4 → ‖ζ (s₀ + ρ * z)‖ ≤ Bnd K δ T * ‖ζ s₀‖ := by
    intro z hz
    set s := s₀ + ρ * z with hsdef
    have hsre : s.re = 1 + δ + ρ * z.re := by simp [hsdef, hre]
    have hsim : s.im = T + ρ * z.im := by simp [hsdef, him]
    have hzr : |z.re| ≤ 3 / 4 := (Complex.abs_re_le_norm z).trans hz
    have hzi : |z.im| ≤ 3 / 4 := (Complex.abs_im_le_norm z).trans hz
    have hρzi : |ρ * z.im| ≤ 3 / 16 := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.im]
    have hρzr : |ρ * z.re| ≤ 3 / 4 * ρ := by
      rw [abs_mul, abs_of_pos hρ]; nlinarith [abs_nonneg z.re]
    have hims : 3 ≤ |s.im| := by
      rw [hsim]; have := abs_sub_abs_le_abs_sub T (-(ρ * z.im))
      rw [abs_neg, sub_neg_eq_add] at this; linarith
    have hims2 : |s.im| ≤ |T| + 1 := by
      rw [hsim]; have := abs_add_le T (ρ * z.im); linarith
    have hlog_pos : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hlog_le : Real.log |s.im| ≤ Lg T := Real.log_le_log (by linarith) hims2
    have hlog1 : 1 ≤ Real.log |s.im| := by
      rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
    have hpow : w (Lg T) ≤ w (Real.log |s.im|) := hw.anti _ _ hlog1 hlog_le
    have hlower : 1 - w (Real.log |s.im|) ≤ s.re := by
      rw [hsre]
      have : w (Lg T) = 4 * ρ := by rw [hρdef, radW]; ring
      have := abs_le.mp hρzr
      linarith
    have hupper : s.re ≤ 2 := by
      rw [hsre]; have := abs_le.mp hρzr; linarith
    have hgs := hG s.im hims s.re hlower hupper
    rw [Complex.re_add_im] at hgs
    have hKpow : K * Real.log |s.im| ^ K ≤ K * Lg T ^ K :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog_pos.le hlog_le hK.le) hK.le
    have hζs0 : 0 ≤ ‖ζ s₀‖ := norm_nonneg _
    calc ‖ζ s‖ ≤ K * Lg T ^ K := hgs.trans hKpow
      _ ≤ K * Lg T ^ K * (‖ζ ((1 + δ : ℝ) : ℂ)‖ * ‖ζ s₀‖) := by
          have : 0 ≤ K * Lg T ^ K := by positivity
          nlinarith
      _ ≤ Bnd K δ T * ‖ζ s₀‖ := by
          unfold Bnd; nlinarith [mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Lg T) K))
            (norm_nonneg (ζ ((1 + δ : ℝ) : ℂ))), hζs0]
  have hloc := local_bound (s₀ := s₀) (ρr := ρ) (B := Bnd K δ T) (by rw [hre]; linarith) hρ hB
    hpole hbound
  refine ⟨hloc.1, fun β hβ hd => ?_⟩
  have := hloc.2 β (by rw [him]; exact hβ) (by rw [hre]; exact hd)
  rwa [hre] at this


/-! ## L3c: the zero gap (the algebra is `Landau.gap_algebra`) -/

/-- **L3c (zero gap).** Under polylog growth: if `ζ(β + it) = 0`, `|t| ≥ 4`, and `δ ∈ (0, 1/2]`
is small enough (`δ ≤ rad(t)/4` and `δ·M ≤ 1/4`, where `M` collects the three local bounds),
then `1 − β ≥ 3δ/13`. -/
theorem zero_gapW {w : ℝ → ℝ} {Cw K : ℝ} (hw : WidthOK w Cw) (hK : 0 < K) (hG : GrowthW w K) :
    ∃ C0 ≥ (1 : ℝ), ∀ (β t δ : ℝ), ζ (β + t * I) = 0 → 4 ≤ |t| → 0 < δ → δ ≤ 1 / 2 →
      δ ≤ radW w t / 4 →
      δ * (3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / radW w t +
        Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t)) ≤ 1 / 4 →
      3 * δ / 13 ≤ 1 - β := by
  obtain ⟨C0, hC0, hShift⟩ := ShiftZeroBound
  refine ⟨C0, hC0, fun β t δ hβ ht hδ hδ2 hδr hδM => ?_⟩
  have hβ1 : β < 1 := by
    by_contra h; rw [not_lt] at h
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith) hβ
  have ht2 : 4 ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
  have hr1 := radW_pos hw t ht
  have hr2 := radW_pos hw (2 * t) ht2
  have hB1 : 0 ≤ Real.log (Bnd K δ t) := Real.log_nonneg (by
    unfold Bnd; have : 0 ≤ K * Lg t ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht).le; positivity
    linarith)
  have hB2 : 0 ≤ Real.log (Bnd K δ (2 * t)) := Real.log_nonneg (by
    unfold Bnd; have : 0 ≤ K * Lg (2 * t) ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht2).le; positivity
    linarith)
  have hKc : 0 ≤ Kc := by unfold Kc; positivity
  -- the three inputs
  have h341 := three_four_one δ ⟨hδ, by linarith⟩ t
  have hX := hShift δ ⟨hδ, by linarith⟩
  have hZloc := (apply_localW hw hK hG ht2 hδ hδ2).1
  have e2 : ((1 + δ : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I = 1 + δ + 2 * I * t := by push_cast; ring
  rw [e2] at hZloc
  have hZ : -(ζ' (1 + δ + 2 * I * t) / ζ (1 + δ + 2 * I * t)).re ≤
      Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t) := by
    rw [le_div_iff₀ hr2]; linarith
  have e1 : ((1 + δ : ℝ) : ℂ) + (t : ℂ) * I = 1 + δ + I * t := by push_cast; ring
  by_cases hnear : 1 + δ - β ≤ radW w t / 2
  · have hYloc := (apply_localW hw hK hG ht hδ hδ2).2 β hβ hnear
    rw [e1] at hYloc
    have hd : 0 < 1 + δ - β := by linarith
    have hY : -(ζ' (1 + δ + I * t) / ζ (1 + δ + I * t)).re ≤
        Kc * Real.log (Bnd K δ t) / radW w t - 1 / (1 + δ - β) := by
      have e : radW w t * (Kc * Real.log (Bnd K δ t) / radW w t - 1 / (1 + δ - β)) =
          Kc * Real.log (Bnd K δ t) - radW w t / (1 + δ - β) := by field_simp
      exact le_of_mul_le_mul_left (by rw [e]; exact hYloc) hr1
    set M := 3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / radW w t +
      Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t) with hMdef
    have hM : 0 ≤ M := by positivity
    have hineq : 4 / (1 + δ - β) ≤ 3 / δ + M := by
      have e3 : 4 / (1 + δ - β) = 4 * (1 / (1 + δ - β)) := by ring
      have e4 : 3 / δ = 3 * (1 / δ) := by ring
      have e5 : 4 * Kc * Real.log (Bnd K δ t) / radW w t =
          4 * (Kc * Real.log (Bnd K δ t) / radW w t) := by ring
      rw [e3, e4, hMdef, e5]
      linarith
    exact Landau.gap_algebra hδ hM hδM (by linarith) hineq
  · have := radW_pos hw t ht
    rw [not_le] at hnear
    linarith


/-! ## L3d: choosing δ -/

/-- The explicit δ used at height `t`. -/
noncomputable def dltW (w : ℝ → ℝ) (N t : ℝ) : ℝ := radW w (2 * t) / (N * (1 + Real.log (Lg (2 * t))))

set_option maxHeartbeats 1600000 in
/-- **L3d.** There is `N ≥ 4` for which `δ = dltW w N t` meets all hypotheses of `zero_gap`,
for every `|t| ≥ 4`. -/
theorem delta_choiceW {w : ℝ → ℝ} {Cw K : ℝ} (hw : WidthOK w Cw) (hK : 0 < K) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ N : ℝ, 4 ≤ N ∧ ∀ t : ℝ, 4 ≤ |t| →
      let δ := dltW w N t
      0 < δ ∧ δ ≤ 1 / 2 ∧ δ ≤ radW w t / 4 ∧
      δ * (3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / radW w t +
        Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t)) ≤ 1 / 4 := by
  obtain ⟨c1, hc1, hnear⟩ := ZetaNear1BndExact
  have hKc : 0 ≤ Kc := by unfold Kc; positivity
  set D := Real.log (2 + K * c1) + Real.log 4 + Cw with hD
  have hDnn : 0 ≤ D := by
    have : 0 ≤ Real.log (2 + K * c1) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have := hw.Cw_nonneg
    linarith
  set P := 3 * C0 / 4 + 5 * Kc * (D + K + Cw + 1) with hP
  have hPnn : 0 ≤ P := by have := hw.Cw_nonneg; positivity
  set N := 8 * P + (80 * Kc) ^ 2 + 4 with hN
  refine ⟨N, by nlinarith [sq_nonneg (80 * Kc)], fun t ht => ?_⟩
  intro δ
  have ht2 : 4 ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
  have hle2 : |t| ≤ |2 * t| := by rw [abs_mul]; norm_num; linarith
  set L := Lg (2 * t) with hLdef
  have hL1 : 1 < L := Lg_gt_one ht2
  have hlogL : 0 < Real.log L := Real.log_pos hL1
  have hr2 := radW_pos hw (2 * t) ht2
  have hr2le := radW_le hw ht2
  have hr12 := radW_anti hw ht hle2
  have hNpos : 0 < N := by nlinarith [sq_nonneg (80 * Kc)]
  have hN4 : 4 ≤ N := by nlinarith [sq_nonneg (80 * Kc)]
  have hden : 1 ≤ N * (1 + Real.log L) := by nlinarith
  have hδpos : 0 < δ := div_pos hr2 (by linarith)
  have hδle : δ ≤ radW w (2 * t) / 4 := by
    show radW w (2 * t) / (N * (1 + Real.log L)) ≤ radW w (2 * t) / 4
    exact div_le_div_of_nonneg_left hr2.le (by norm_num) (by nlinarith)
  have hδ12 : δ ≤ 1 / 2 := by linarith
  refine ⟨hδpos, hδ12, by linarith, ?_⟩
  -- bound on log B
  have hδ1 : δ ≤ 1 := by linarith
  have hζ : ‖ζ ((1 + δ : ℝ) : ℂ)‖ ≤ c1 / δ := by
    have := hnear (1 + δ) ⟨by linarith, by linarith⟩
    simpa using this
  have hLK : 1 ≤ L ^ K := Real.one_le_rpow hL1.le hK.le
  have hBle : Bnd K δ (2 * t) ≤ (2 + K * c1) * L ^ K / δ := by
    unfold Bnd
    rw [← hLdef]
    have h1 : K * L ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ ≤ K * L ^ K * (c1 / δ) :=
      mul_le_mul_of_nonneg_left hζ (by positivity)
    have h2 : (2 : ℝ) ≤ 2 * L ^ K / δ := by
      rw [le_div_iff₀ hδpos]; nlinarith
    have e : (2 + K * c1) * L ^ K / δ = 2 * L ^ K / δ + K * L ^ K * (c1 / δ) := by ring
    linarith
  have hB1le : Bnd K δ t ≤ Bnd K δ (2 * t) := by
    unfold Bnd
    have hmono : Lg t ^ K ≤ L ^ K :=
      Real.rpow_le_rpow (by linarith [Lg_gt_one ht]) (Lg_mono ht hle2) hK.le
    nlinarith [norm_nonneg (ζ ((1 + δ : ℝ) : ℂ)), mul_le_mul_of_nonneg_left hmono hK.le]
  have hB2pos : 1 < Bnd K δ (2 * t) := by
    unfold Bnd; have : 0 ≤ K * Lg (2 * t) ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht2).le; positivity
    linarith
  have hB1pos : 1 < Bnd K δ t := by
    unfold Bnd; have : 0 ≤ K * Lg t ^ K * ‖ζ ((1 + δ : ℝ) : ℂ)‖ := by
      have := (Lg_gt_one ht).le; positivity
    linarith
  have hlogB : Real.log (Bnd K δ (2 * t)) ≤ D + Real.log N + (K + Cw + 1) * Real.log L := by
    have hpos : 0 < (2 + K * c1) * L ^ K / δ := by positivity
    have h1 := Real.log_le_log (by linarith) hBle
    rw [Real.log_div (by positivity) hδpos.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by linarith)] at h1
    -- log δ = log rad − log N − log(1 + log L), and log rad = −log 4 − a log L
    have hlogδ : Real.log δ = Real.log (radW w (2 * t)) - Real.log N - Real.log (1 + Real.log L) := by
      show Real.log (radW w (2 * t) / (N * (1 + Real.log L))) = _
      rw [Real.log_div hr2.ne' (by positivity), Real.log_mul hNpos.ne' (by positivity)]; ring
    have hlogrd : -Real.log 4 - Cw - Cw * Real.log L ≤ Real.log (radW w (2 * t)) := by
      have hwL := hw.pos L hL1.le
      have hb := hw.logb L hL1.le
      unfold radW; rw [← hLdef, Real.log_mul (by norm_num) hwL.ne']
      rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]; linarith
    have hl1 : Real.log (1 + Real.log L) ≤ Real.log L := by
      apply Real.log_le_log (by linarith)
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L); linarith
    rw [hlogδ] at h1
    linarith
  have hlogN : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hNpos
  have hsqrtN : 80 * Kc ≤ Real.sqrt N := by
    rw [show 80 * Kc = Real.sqrt ((80 * Kc) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- assemble
  set M := 3 * C0 + 4 * Kc * Real.log (Bnd K δ t) / radW w t +
      Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t)
  have hlogB1 : Real.log (Bnd K δ t) ≤ Real.log (Bnd K δ (2 * t)) := Real.log_le_log (by linarith) hB1le
  have hlogB1nn : 0 ≤ Real.log (Bnd K δ t) := Real.log_nonneg hB1pos.le
  have hM : M ≤ 3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t) := by
    have h4 : 4 * Kc * Real.log (Bnd K δ t) / radW w t ≤
        4 * Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t) := by
      have hB2nn : 0 ≤ Real.log (Bnd K δ (2 * t)) := Real.log_nonneg hB2pos.le
      apply div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hKc) hB2nn)
        (by have := mul_le_mul_of_nonneg_left hlogB1 hKc; linarith) hr2 hr12
    have e : 5 * Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t) =
        4 * Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t) +
        Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t) := by ring
    linarith
  have hδrad : δ / radW w (2 * t) = 1 / (N * (1 + Real.log L)) := by
    show radW w (2 * t) / (N * (1 + Real.log L)) / radW w (2 * t) = _
    field_simp
  have hmain : δ * (3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t)) ≤ 1 / 4 := by
    have e : δ * (3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t)) =
        3 * C0 * δ + 5 * Kc * Real.log (Bnd K δ (2 * t)) * (δ / radW w (2 * t)) := by
      field_simp
    rw [e, hδrad]
    have h1 : 3 * C0 * δ ≤ 3 * C0 / (4 * N) := by
      have : δ ≤ 1 / (4 * N) := by
        show radW w (2 * t) / (N * (1 + Real.log L)) ≤ 1 / (4 * N)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc 3 * C0 * δ ≤ 3 * C0 * (1 / (4 * N)) := by gcongr
        _ = 3 * C0 / (4 * N) := by ring
    have h2 : 5 * Kc * Real.log (Bnd K δ (2 * t)) * (1 / (N * (1 + Real.log L))) ≤
        5 * Kc * (D + Real.log N + (K + Cw + 1)) / N := by
      have hq : (D + Real.log N + (K + Cw + 1) * Real.log L) / (1 + Real.log L) ≤
          D + Real.log N + (K + Cw + 1) := by
        rw [div_le_iff₀ (by linarith)]
        have hlogNnn : 0 ≤ Real.log N := Real.log_nonneg (by linarith [hN4])
        have hCw := hw.Cw_nonneg
        nlinarith [mul_nonneg hDnn hlogL.le, mul_nonneg hlogNnn hlogL.le]
      have hB2nn : 0 ≤ Real.log (Bnd K δ (2 * t)) := Real.log_nonneg hB2pos.le
      calc 5 * Kc * Real.log (Bnd K δ (2 * t)) * (1 / (N * (1 + Real.log L)))
          = 5 * Kc / N * (Real.log (Bnd K δ (2 * t)) / (1 + Real.log L)) := by field_simp
        _ ≤ 5 * Kc / N * ((D + Real.log N + (K + Cw + 1) * Real.log L) / (1 + Real.log L)) := by
            gcongr
        _ ≤ 5 * Kc / N * (D + Real.log N + (K + Cw + 1)) := by gcongr
        _ = 5 * Kc * (D + Real.log N + (K + Cw + 1)) / N := by ring
    have h3 : 3 * C0 / (4 * N) + 5 * Kc * (D + Real.log N + (K + Cw + 1)) / N ≤ 1 / 4 := by
      have e : 3 * C0 / (4 * N) + 5 * Kc * (D + Real.log N + (K + Cw + 1)) / N =
          P / N + 5 * Kc * Real.log N / N := by rw [hP]; field_simp; ring
      rw [e]
      have hPN : P / N ≤ 1 / 8 := by
        rw [div_le_iff₀ hNpos]; nlinarith [sq_nonneg (80 * Kc)]
      have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
      have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
      have hLN : 5 * Kc * Real.log N / N ≤ 1 / 8 := by
        rw [div_le_iff₀ hNpos]
        have : 5 * Kc * Real.log N ≤ 10 * Kc * Real.sqrt N := by nlinarith
        nlinarith
      linarith
    linarith
  calc δ * M ≤ δ * (3 * C0 + 5 * Kc * Real.log (Bnd K δ (2 * t)) / radW w (2 * t)) :=
        mul_le_mul_of_nonneg_left hM hδpos.le
    _ ≤ 1 / 4 := hmain


/-! ## L3e: the zero-free region -/

/-- Zeros at height `|t| ≥ 4` stay `(3/13)·dlt` away from the line. -/
theorem zero_gap_explicitW {w : ℝ → ℝ} {Cw K : ℝ} (hw : WidthOK w Cw) (hK : 0 < K) (hG : GrowthW w K) :
    ∃ N : ℝ, 4 ≤ N ∧ ∀ β t : ℝ, ζ (β + t * I) = 0 → 4 ≤ |t| → 3 * dltW w N t / 13 ≤ 1 - β := by
  obtain ⟨C0, hC0, hgap⟩ := zero_gapW hw hK hG
  obtain ⟨N, hN, hch⟩ := delta_choiceW hw hK C0 hC0
  refine ⟨N, hN, fun β t hβ ht => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hch t ht
  exact hgap β t (dltW w N t) hβ ht h1 h2 h3 h4

end LandauW
