import KaiserKV
import WeilLandau
import WeilCount
import Unconditional
import ZetaInputs

/-!
# The Korobov–Vinogradov region as a lower bound on the twin form (round 237)

`weil_twins_rate` (WeilLandau) says: `Q(twin (box 1) λ) ≥ −C e^{σλ}` for all `λ ≥ 0` iff every zero
has `|2 Re ρ − 1| ≤ σ`. The KV zero-free region (`KaiserKV.abs_im_tau_le`) gives, for the zeros up
to height `T`, `|2 Re ρ − 1| ≤ 1 − 2A/f(T)`, `f(T) = (log T)^{2/3}(log log T)^{1/3}`; the zeros
above `T` are controlled by the tail `Σ_{|t_ρ| > T} |ĝ₀(t_ρ)|² ≪ T^{−1/4}`. With `T = e^{8λ}` this
gives the unconditional lower bound `Q(twin (box 1) λ) ≥ −C·exp((1 − A/f(e^{8λ}))·λ)` for `λ ≥ 1`,
i.e. `−C·exp(λ − c·λ^{1/3}(log 8λ)^{−1/3})`. The exponent `1/3` is an artefact of the cutoff
`T = e^{8λ}`: with the cutoff free (`twins_lower_cut`) and optimised, the defect is
`−C·exp(λ − c·λ^{3/5}(log λ)^{−1/5})` (`twins_lower_KV_sharp`, round 242), the shape of `PNT_KV`.
-/

open Complex Real Set Filter
open Pilot1ca Pilot1bt PilotWeil KaiserKV


namespace TwinKV

/-- The `Ξ`-coordinate `τ` of a zero of `ζ` (through `zetaEquiv`). -/
noncomputable def tz (q : ZIdx) : ℂ := tau (zetaEquiv q).2

theorem abs_re_poleP_eq (q : ZIdx) : |(poleP q).re| = 2 * |(tz q).im| := by
  have h := rhoXi_zetaEquiv q
  have e : (poleP q).re = 2 * ((rhoXi (zetaEquiv q)).re - 1 / 2) := by
    unfold poleP; rw [h]; simp
  rw [e]; unfold rhoXi tz
  rcases Bool.eq_false_or_eq_true (zetaEquiv q).1 with hb | hb <;> simp [hb, abs_mul, abs_neg]

theorem ordi_eq (q : ZIdx) : ordi zetaZeroFamily q = poleP q / (2 * I) := by
  rw [← two_I_ordi]; field_simp

theorem norm_tz_pos (q : ZIdx) : 0 < ‖tz q‖ := by
  rw [norm_pos_iff]; unfold tz
  intro h
  have h1 := norm_zZF_sub q
  rw [h, norm_zero, norm_eq_zero, sub_eq_zero] at h1
  have := im_zetaZeroFamily_ne q
  rw [h1] at this; simp at this

theorem norm_ordi (q : ZIdx) : ‖ordi zetaZeroFamily q‖ = ‖tz q‖ := by
  rw [ordi_eq, norm_div, poleP, norm_mul, norm_zZF_sub]
  unfold tz; simp

theorem im_ordi (q : ZIdx) : (ordi zetaZeroFamily q).im = -(poleP q).re / 2 := by
  rw [ordi_eq]; simp [Complex.div_im]; ring

/-- `K₀ = 2·box 1 (0)·cosh(1/2)`, the constant in `|ĝ₀(t_ρ)| ≤ K₀/|t_ρ|`. -/
noncomputable def K0 : ℝ := 2 * box 1 0 * Real.cosh (1 / 2)

theorem K0_nonneg : 0 ≤ K0 := by
  unfold K0
  have := box_nonneg 0 ⟨le_rfl, zero_le_one⟩
  positivity

theorem norm_ghat_ordi_le (q : ZIdx) : ‖ghatC (box 1) 1 (ordi zetaZeroFamily q)‖ ≤ K0 / ‖tz q‖ := by
  have hz : ordi zetaZeroFamily q ≠ 0 := by
    intro h; have := norm_tz_pos q; rw [← norm_ordi, h, norm_zero] at this; exact lt_irrefl _ this
  have h := norm_ghatC_le_of_antitone one_pos (box_probe 1).even box_antitone box_nonneg hz
  rw [norm_ordi] at h
  refine h.trans ?_
  unfold K0
  have hb := box_nonneg 0 ⟨le_rfl, zero_le_one⟩
  have hc : Real.cosh (1 * |(ordi zetaZeroFamily q).im|) ≤ Real.cosh (1 / 2) := by
    rw [Real.cosh_le_cosh, one_mul, abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), im_ordi]
    have := abs_re_poleP q
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  gcongr

/-- `‖ĝ₀(t_ρ)²‖ ≤ K₀² / ‖u_ρ‖`, `u_ρ = t_ρ²` the coordinate of the `Ξ`-zero family. -/
theorem norm_cw_le (q : ZIdx) : ‖cw q‖ ≤ K0 ^ 2 / ‖(zetaEquiv q).2.1‖ := by
  unfold cw
  rw [norm_pow]
  have e : ‖(zetaEquiv q).2.1‖ = ‖tz q‖ ^ 2 := by unfold tz; rw [← tau_sq, norm_pow]
  rw [e, ← div_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_ghat_ordi_le q) 2

/-- `S₁ = Σ_ρ |u_ρ|^{−7/8}` over the zeros of `ζ` (finite by `summable_Xi_zeros_rpow`). -/
noncomputable def S1 : ℝ := ∑' q : ZIdx, (‖(zetaEquiv q).2.1‖ ^ (7 / 8 : ℝ))⁻¹

theorem summable_S1 : Summable fun q : ZIdx => (‖(zetaEquiv q).2.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
  have h : Summable fun p : Bool × ZeroIdx (sqF Xi) => (‖p.2.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
    rw [summable_prod_of_nonneg (fun _ => by positivity)]
    exact ⟨fun _ => summable_Xi_zeros_rpow, (hasSum_fintype _).summable⟩
  exact (zetaEquiv.summable_iff (f := fun p : Bool × ZeroIdx (sqF Xi) => (‖p.2.1‖ ^ (7 / 8 : ℝ))⁻¹)).2 h

theorem S1_nonneg : 0 ≤ S1 := tsum_nonneg fun _ => by positivity

/-- The far zeros: `|Re t_ρ| > T` gives `‖ĝ₀(t_ρ)²‖ ≤ K₀² T^{−1/4} |u_ρ|^{−7/8}`. -/
theorem far_term_le {T : ℝ} (hT : 0 < T) (q : ZIdx) :
    (if |(tz q).re| ≤ T then 0 else ‖cw q‖) ≤
      K0 ^ 2 / T ^ ((1 : ℝ) / 4) * (‖(zetaEquiv q).2.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
  split_ifs with h
  · positivity
  · push Not at h
    set v := ‖(zetaEquiv q).2.1‖ with hv
    have hv2 : v = ‖tz q‖ ^ 2 := by rw [hv]; unfold tz; rw [← tau_sq, norm_pow]
    have hTv : T ^ 2 < v := by
      rw [hv2]
      have := Complex.abs_re_le_norm (tz q)
      nlinarith
    have hv0 : 0 < v := lt_trans (by positivity) hTv
    have hT4 : T ^ ((1 : ℝ) / 4) ≤ v ^ ((1 : ℝ) / 8) := by
      have : T ^ ((1 : ℝ) / 4) = (T ^ 2) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]; norm_num
      rw [this]
      exact Real.rpow_le_rpow (by positivity) hTv.le (by norm_num)
    have hsplit : v = v ^ ((1 : ℝ) / 8) * v ^ ((7 : ℝ) / 8) := by
      rw [← Real.rpow_add hv0]; norm_num
    have hden : T ^ ((1 : ℝ) / 4) * v ^ ((7 : ℝ) / 8) ≤ v := by
      calc T ^ ((1 : ℝ) / 4) * v ^ ((7 : ℝ) / 8) ≤ v ^ ((1 : ℝ) / 8) * v ^ ((7 : ℝ) / 8) := by
            gcongr
        _ = v := hsplit.symm
    have hpos : 0 < T ^ ((1 : ℝ) / 4) * v ^ ((7 : ℝ) / 8) := by positivity
    calc ‖cw q‖ ≤ K0 ^ 2 / v := norm_cw_le q
      _ ≤ K0 ^ 2 / (T ^ ((1 : ℝ) / 4) * v ^ ((7 : ℝ) / 8)) :=
          div_le_div_of_nonneg_left (by positivity) hpos hden
      _ = K0 ^ 2 / T ^ ((1 : ℝ) / 4) * (v ^ ((7 : ℝ) / 8))⁻¹ := by
          have h1 : T ^ ((1 : ℝ) / 4) ≠ 0 := by positivity
          have h2 : v ^ ((7 : ℝ) / 8) ≠ 0 := by positivity
          field_simp

theorem summable_far {T : ℝ} (hT : 0 < T) :
    Summable fun q : ZIdx => (if |(tz q).re| ≤ T then 0 else ‖cw q‖) :=
  (summable_S1.mul_left (K0 ^ 2 / T ^ ((1 : ℝ) / 4))).of_nonneg_of_le
    (fun q => by split_ifs <;> positivity) (far_term_le hT)

theorem far_sum_le {T : ℝ} (hT : 0 < T) :
    ∑' q : ZIdx, (if |(tz q).re| ≤ T then 0 else ‖cw q‖) ≤ K0 ^ 2 / T ^ ((1 : ℝ) / 4) * S1 := by
  calc ∑' q : ZIdx, (if |(tz q).re| ≤ T then 0 else ‖cw q‖)
      ≤ ∑' q : ZIdx, K0 ^ 2 / T ^ ((1 : ℝ) / 4) * (‖(zetaEquiv q).2.1‖ ^ (7 / 8 : ℝ))⁻¹ :=
        (summable_far hT).tsum_le_tsum (far_term_le hT) (summable_S1.mul_left _)
    _ = _ := tsum_mul_left

/-- The near zeros: `|Re t_ρ| ≤ T`, `T ≥ e³`, gives `|Re P_ρ| ≤ 1 − 2A/f(T)`. -/
theorem near_rate {A T : ℝ} (hreg : ∀ T : ℝ, Real.exp 3 ≤ T →
      ∀ i : ZeroIdx (sqF Xi), |(tau i).re| ≤ T → |(tau i).im| ≤ 1 / 2 - A / fKV T)
    (hT : Real.exp 3 ≤ T) (q : ZIdx) (hq : |(tz q).re| ≤ T) :
    |(poleP q).re| ≤ 1 - 2 * A / fKV T := by
  rw [abs_re_poleP_eq]
  have := hreg T hT (zetaEquiv q).2 hq
  have e : 2 * A / fKV T = 2 * (A / fKV T) := by ring
  rw [e]; unfold tz; linarith

/-- **The KV-graded lower bound for the twin form.** There are `C` and `A > 0` with
`Q(twin (box 1) λ) ≥ −C·exp((1 − A/f(e^{8λ}))·λ)` for every `λ ≥ 1`, where
`f(T) = (log T)^{2/3}(log log T)^{1/3}` is the Korobov–Vinogradov width. -/
theorem twins_lower_KV : ∃ C A : ℝ, 0 < A ∧ ∀ l : ℝ, 1 ≤ l →
    -(C * Real.exp ((1 - A / fKV (Real.exp (8 * l))) * l)) ≤ weilQ (l + 1) (twin (box 1) l) := by
  obtain ⟨A, hA, hA3, hreg⟩ := abs_im_tau_le
  set S : ℝ := ∑' q : ZIdx, ‖cw q‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨4 * (S + K0 ^ 2 * S1), 2 * A, by linarith, fun l hl => ?_⟩
  have hl0 : 0 ≤ l := by linarith
  set T : ℝ := Real.exp (8 * l) with hTdef
  have hT3 : Real.exp 3 ≤ T := Real.exp_le_exp.2 (by linarith)
  have hT0 : 0 < T := Real.exp_pos _
  have hf : 0 < fKV T := fKV_pos hT3
  have hAf : A ≤ fKV T / 2 := hA3.trans (by linarith [fKV_mono (le_refl (Real.exp 3)) hT3])
  have hAf1 : 2 * A / fKV T ≤ 1 := by rw [div_le_iff₀ hf]; linarith
  set r : ZIdx → ℝ := fun q => if |(tz q).re| ≤ T then 1 - 2 * A / fKV T else 1 with hr
  have hr1 : ∀ q, r q ≤ 1 := fun q => by
    simp only [hr]; split_ifs
    · have : 0 ≤ 2 * A / fKV T := by positivity
      linarith
    · exact le_rfl
  have hrP : ∀ q, |(poleP q).re| ≤ r q := fun q => by
    simp only [hr]; split_ifs with h
    · exact near_rate hreg hT3 q h
    · exact (abs_re_poleP q).le
  -- the termwise majorant
  have hterm : ∀ q, ‖cw q‖ * Real.exp (r q * l) ≤
      ‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) +
        (if |(tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l := fun q => by
    simp only [hr]; split_ifs with h
    · simp only [zero_mul, add_zero]; exact le_rfl
    · simp only [one_mul]
      have : 0 ≤ ‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) := by positivity
      linarith
  have hsum1 : Summable fun q : ZIdx => ‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) :=
    summable_cw.mul_right _
  have hsum2 : Summable fun q : ZIdx => (if |(tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l :=
    (summable_far hT0).mul_right _
  have hs : Summable fun q : ZIdx => ‖cw q‖ * Real.exp (r q * l) :=
    (hsum1.add hsum2).of_nonneg_of_le (fun q => by positivity) hterm
  have hQ := TwinLandau.Q_ge_of_rates twinData_zeta hrP hl0 hs
  -- bound the sum
  have hT4 : T ^ ((1 : ℝ) / 4) = Real.exp (2 * l) := by
    rw [hTdef, ← Real.exp_mul]; ring_nf
  have htail : ∑' q : ZIdx, (if |(tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l ≤
      K0 ^ 2 * S1 * Real.exp (-l) := by
    rw [tsum_mul_right]
    have h := far_sum_le hT0
    rw [hT4] at h
    have hE : Real.exp (-l) = Real.exp l / Real.exp (2 * l) := by
      rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add]; ring_nf
    rw [hE]
    calc (∑' q : ZIdx, (if |(tz q).re| ≤ T then 0 else ‖cw q‖)) * Real.exp l
        ≤ K0 ^ 2 / Real.exp (2 * l) * S1 * Real.exp l :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = K0 ^ 2 * S1 * (Real.exp l / Real.exp (2 * l)) := by ring
  have hexp : Real.exp (-l) ≤ Real.exp ((1 - 2 * A / fKV T) * l) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hbound : ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l) ≤
      (S + K0 ^ 2 * S1) * Real.exp ((1 - 2 * A / fKV T) * l) := by
    calc ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l)
        ≤ ∑' q : ZIdx, (‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) +
            (if |(tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l) :=
          hs.tsum_le_tsum hterm (hsum1.add hsum2)
      _ = S * Real.exp ((1 - 2 * A / fKV T) * l) +
            ∑' q : ZIdx, (if |(tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l := by
          rw [hsum1.tsum_add hsum2, tsum_mul_right]
      _ ≤ S * Real.exp ((1 - 2 * A / fKV T) * l) + K0 ^ 2 * S1 * Real.exp (-l) := by
          gcongr
      _ ≤ S * Real.exp ((1 - 2 * A / fKV T) * l) +
            K0 ^ 2 * S1 * Real.exp ((1 - 2 * A / fKV T) * l) := by
          gcongr
          exact mul_nonneg (by positivity) S1_nonneg
      _ = _ := by ring
  have : -(4 * (S + K0 ^ 2 * S1) * Real.exp ((1 - 2 * A / fKV T) * l)) ≤
      -(4 * ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l)) := by
    have := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  exact this.trans hQ

/-- `f_KV(e^{8λ}) = 4 λ^{2/3} (log 8λ)^{1/3}`. -/
theorem fKV_exp_eight {l : ℝ} (hl : 1 ≤ l) :
    fKV (Real.exp (8 * l)) = 4 * l ^ ((2 : ℝ) / 3) * Real.log (8 * l) ^ ((1 : ℝ) / 3) := by
  have hl0 : 0 < l := by linarith
  unfold fKV
  rw [Real.log_exp, Real.mul_rpow (by norm_num) hl0.le]
  have : (8 : ℝ) ^ ((2 : ℝ) / 3) = 4 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [this]

/-- **The KV-graded lower bound in explicit shape**: `Q(twin (box 1) λ) ≥ −C·exp(λ − c λ^{1/3}(log 8λ)^{−1/3})`
for `λ ≥ 1`. -/
theorem twins_lower_KV' : ∃ C c : ℝ, 0 < c ∧ ∀ l : ℝ, 1 ≤ l →
    -(C * Real.exp (l - c * l ^ ((1 : ℝ) / 3) / Real.log (8 * l) ^ ((1 : ℝ) / 3))) ≤
      weilQ (l + 1) (twin (box 1) l) := by
  obtain ⟨C, A, hA, h⟩ := twins_lower_KV
  refine ⟨C, A / 4, by positivity, fun l hl => ?_⟩
  have hl0 : 0 < l := by linarith
  have hL : 0 < Real.log (8 * l) := Real.log_pos (by linarith)
  have e3 : l = l ^ ((1 : ℝ) / 3) * l ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hl0]; norm_num
  have E : (1 - A / fKV (Real.exp (8 * l))) * l =
      l - A / 4 * l ^ ((1 : ℝ) / 3) / Real.log (8 * l) ^ ((1 : ℝ) / 3) := by
    rw [fKV_exp_eight hl]
    set u := l ^ ((1 : ℝ) / 3) with hu
    set v := l ^ ((2 : ℝ) / 3) with hv
    set w := Real.log (8 * l) ^ ((1 : ℝ) / 3) with hw
    have hv0 : 0 < v := by positivity
    have hw0 : 0 < w := by positivity
    rw [e3]
    field_simp
  have := h l hl
  rwa [E] at this


/-- **The lower bound with a free cutoff `u`** (`T = e^u`; round 242). -/
theorem twins_lower_cut : ∃ C A : ℝ, 0 ≤ C ∧ 0 < A ∧ ∀ l u : ℝ, 0 ≤ l → 3 ≤ u →
    -(C * (Real.exp ((1 - 2 * A / fKV (Real.exp u)) * l) + Real.exp (l - u / 4))) ≤
      weilQ (l + 1) (twin (box 1) l) := by
  obtain ⟨A, hA, hA3, hreg⟩ := abs_im_tau_le
  set S : ℝ := ∑' q : ZIdx, ‖cw q‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hK : 0 ≤ TwinKV.K0 ^ 2 * TwinKV.S1 := mul_nonneg (sq_nonneg _) TwinKV.S1_nonneg
  refine ⟨4 * (S + TwinKV.K0 ^ 2 * TwinKV.S1), A, mul_nonneg (by norm_num) (add_nonneg hS0 hK), hA,
    fun l u hl hu => ?_⟩
  set T : ℝ := Real.exp u with hTdef
  have hT3 : Real.exp 3 ≤ T := Real.exp_le_exp.2 hu
  have hT0 : 0 < T := Real.exp_pos _
  set r : ZIdx → ℝ := fun q => if |(TwinKV.tz q).re| ≤ T then 1 - 2 * A / fKV T else 1 with hr
  have hrP : ∀ q, |(poleP q).re| ≤ r q := fun q => by
    simp only [hr]; split_ifs with h
    · exact TwinKV.near_rate hreg hT3 q h
    · exact (abs_re_poleP q).le
  have hterm : ∀ q, ‖cw q‖ * Real.exp (r q * l) ≤
      ‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) +
        (if |(TwinKV.tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l := fun q => by
    simp only [hr]; split_ifs with h
    · simp only [zero_mul, add_zero]; exact le_rfl
    · simp only [one_mul]
      have : 0 ≤ ‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) := by positivity
      linarith
  have hsum1 : Summable fun q : ZIdx => ‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) :=
    summable_cw.mul_right _
  have hsum2 : Summable fun q : ZIdx =>
      (if |(TwinKV.tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l :=
    (TwinKV.summable_far hT0).mul_right _
  have hs : Summable fun q : ZIdx => ‖cw q‖ * Real.exp (r q * l) :=
    (hsum1.add hsum2).of_nonneg_of_le (fun q => by positivity) hterm
  have hQ := TwinLandau.Q_ge_of_rates twinData_zeta hrP hl hs
  have hT4 : T ^ ((1 : ℝ) / 4) = Real.exp (u / 4) := by
    rw [hTdef, ← Real.exp_mul]; ring_nf
  have htail : ∑' q : ZIdx, (if |(TwinKV.tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l ≤
      TwinKV.K0 ^ 2 * TwinKV.S1 * Real.exp (l - u / 4) := by
    rw [tsum_mul_right]
    have h := TwinKV.far_sum_le hT0
    rw [hT4] at h
    rw [Real.exp_sub]
    calc (∑' q : ZIdx, (if |(TwinKV.tz q).re| ≤ T then 0 else ‖cw q‖)) * Real.exp l
        ≤ TwinKV.K0 ^ 2 / Real.exp (u / 4) * TwinKV.S1 * Real.exp l :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = TwinKV.K0 ^ 2 * TwinKV.S1 * (Real.exp l / Real.exp (u / 4)) := by ring
  have hbound : ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l) ≤
      (S + TwinKV.K0 ^ 2 * TwinKV.S1) *
        (Real.exp ((1 - 2 * A / fKV T) * l) + Real.exp (l - u / 4)) := by
    have e1 := Real.exp_pos ((1 - 2 * A / fKV T) * l)
    have e2 := Real.exp_pos (l - u / 4)
    calc ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l)
        ≤ ∑' q : ZIdx, (‖cw q‖ * Real.exp ((1 - 2 * A / fKV T) * l) +
            (if |(TwinKV.tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l) :=
          hs.tsum_le_tsum hterm (hsum1.add hsum2)
      _ = S * Real.exp ((1 - 2 * A / fKV T) * l) +
            ∑' q : ZIdx, (if |(TwinKV.tz q).re| ≤ T then 0 else ‖cw q‖) * Real.exp l := by
          rw [hsum1.tsum_add hsum2, tsum_mul_right]
      _ ≤ S * Real.exp ((1 - 2 * A / fKV T) * l) +
            TwinKV.K0 ^ 2 * TwinKV.S1 * Real.exp (l - u / 4) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hS0 e2.le, mul_nonneg hK e1.le]
  have : -(4 * (S + TwinKV.K0 ^ 2 * TwinKV.S1) *
      (Real.exp ((1 - 2 * A / fKV T) * l) + Real.exp (l - u / 4))) ≤
      -(4 * ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l)) := by
    have := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  exact this.trans hQ

/-- **Exponent `3/5`**: the cutoff `u = 3λ^{3/5}` gives `Q(twin (box 1) λ) ≥ −C·exp(λ − c λ^{3/5}(log 3λ^{3/5})^{−1/3})`. -/
theorem twins_lower_KV35 : ∃ C c : ℝ, 0 < c ∧ ∀ l : ℝ, 1 ≤ l →
    -(C * Real.exp (l - c * l ^ ((3 : ℝ) / 5) / Real.log (3 * l ^ ((3 : ℝ) / 5)) ^ ((1 : ℝ) / 3))) ≤
      weilQ (l + 1) (twin (box 1) l) := by
  obtain ⟨C, A, hC, hA, h⟩ := twins_lower_cut
  have h32 : (0 : ℝ) < (3 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  have hcpos : 0 < min (2 * A / (3 : ℝ) ^ ((2 : ℝ) / 3)) (3 / 4) := lt_min (by positivity) (by norm_num)
  refine ⟨2 * C, min (2 * A / (3 : ℝ) ^ ((2 : ℝ) / 3)) (3 / 4), hcpos, fun l hl => ?_⟩
  have hl0 : 0 < l := by linarith
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = l ^ ((3 : ℝ) / 5) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = l ^ ((2 : ℝ) / 5) := ⟨_, rfl⟩
  have hv1 : 1 ≤ v := by rw [hv]; exact Real.one_le_rpow hl (by norm_num)
  have hw0 : 0 < w := by rw [hw]; positivity
  have hvw : v * w = l := by
    rw [hv, hw, ← Real.rpow_add hl0]; norm_num
  have hv23 : v ^ ((2 : ℝ) / 3) = w := by
    rw [hv, hw, ← Real.rpow_mul hl0.le]; norm_num
  have hu3 : (3 : ℝ) ≤ 3 * v := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.log (3 * v) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hL1 : 1 ≤ Real.log (3 * v) := by
    have h3 : Real.log 3 ≤ Real.log (3 * v) := Real.log_le_log (by norm_num) hu3
    have h3' : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hM1 : 1 ≤ M := by rw [hM]; exact Real.one_le_rpow hL1 (by norm_num)
  have hM0 : 0 < M := by linarith
  have hf : fKV (Real.exp (3 * v)) = (3 : ℝ) ^ ((2 : ℝ) / 3) * w * M := by
    unfold fKV
    rw [Real.log_exp, Real.mul_rpow (x := 3) (y := v) (by norm_num) (by linarith), hv23, ← hM]
  have H := h l (3 * v) hl0.le hu3
  rw [hf] at H
  rw [← hv, ← hM]
  set c := min (2 * A / (3 : ℝ) ^ ((2 : ℝ) / 3)) (3 / 4) with hc
  have hc1 : c ≤ 2 * A / (3 : ℝ) ^ ((2 : ℝ) / 3) := min_le_left _ _
  have hc2 : c ≤ 3 / 4 := min_le_right _ _
  have hw' : w ≠ 0 := hw0.ne'
  have hM' : M ≠ 0 := hM0.ne'
  have h32' : (3 : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 := h32.ne'
  have e1 : (1 - 2 * A / ((3 : ℝ) ^ ((2 : ℝ) / 3) * w * M)) * l ≤ l - c * v / M := by
    have hx : 2 * A / ((3 : ℝ) ^ ((2 : ℝ) / 3) * w * M) * l =
        2 * A / (3 : ℝ) ^ ((2 : ℝ) / 3) * v / M := by
      rw [← hvw]; field_simp
    have hy : c * v / M ≤ 2 * A / (3 : ℝ) ^ ((2 : ℝ) / 3) * v / M :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 (by linarith)) hM0.le
    nlinarith
  have e2 : l - 3 * v / 4 ≤ l - c * v / M := by
    have : c * v / M ≤ 3 * v / 4 := by
      rw [div_le_iff₀ hM0]
      nlinarith [mul_le_mul_of_nonneg_right hc2 (by linarith : (0 : ℝ) ≤ v),
        mul_nonneg (by linarith : (0 : ℝ) ≤ v) (by linarith : (0 : ℝ) ≤ M - 1)]
    linarith
  have E1 := Real.exp_le_exp.2 e1
  have E2 := Real.exp_le_exp.2 e2
  have H' : -(2 * C * Real.exp (l - c * v / M)) ≤
      -(C * (Real.exp ((1 - 2 * A / ((3 : ℝ) ^ ((2 : ℝ) / 3) * w * M)) * l) +
        Real.exp (l - 3 * v / 4))) := by
    nlinarith [mul_le_mul_of_nonneg_left E1 hC, mul_le_mul_of_nonneg_left E2 hC]
  exact H'.trans H

/-! ## The optimal cutoff: exponent `3/5` with `(log λ)^{−1/5}`, the shape of `PNT_KV` (round 242) -/

/-- The one-variable inequality: `c·λ^{3/5}/(log λ)^{1/5} ≤ u/4 + 2Aλ/(u^{2/3}(log u)^{1/3})` for
`u ≥ 3`, `λ ≥ e`, with `c = min(1/4, 2A)`. -/
theorem exponent_le {A l u : ℝ} (hA : 0 < A) (hl : Real.exp 1 ≤ l) (hu : 3 ≤ u) :
    min (1 / 4) (2 * A) * (l ^ ((3 : ℝ) / 5) / Real.log l ^ ((1 : ℝ) / 5))
      ≤ u / 4 + 2 * A * l / (u ^ ((2 : ℝ) / 3) * Real.log u ^ ((1 : ℝ) / 3)) := by
  have hl0 : 0 < l := lt_of_lt_of_le (Real.exp_pos 1) hl
  have h1l : 1 ≤ l := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hl
  have hl1 : 1 ≤ Real.log l := (Real.le_log_iff_exp_le hl0).2 hl
  set L := Real.log l with hLdef
  set M := l ^ ((3 : ℝ) / 5) / L ^ ((1 : ℝ) / 5) with hM
  have hLpos : 0 < L := by linarith
  have hM0 : 0 < M := by positivity
  have hMle : M ≤ l := by
    have h1 : 1 ≤ L ^ ((1 : ℝ) / 5) := Real.one_le_rpow hl1 (by norm_num)
    have h2 : l ^ ((3 : ℝ) / 5) ≤ l := by
      calc l ^ ((3 : ℝ) / 5) ≤ l ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1l (by norm_num)
        _ = l := Real.rpow_one l
    calc M = l ^ ((3 : ℝ) / 5) / L ^ ((1 : ℝ) / 5) := rfl
      _ ≤ l ^ ((3 : ℝ) / 5) := div_le_self (by positivity) h1
      _ ≤ l := h2
  have hc1 : min (1 / 4 : ℝ) (2 * A) ≤ 1 / 4 := min_le_left _ _
  have hc2 : min (1 / 4 : ℝ) (2 * A) ≤ 2 * A := min_le_right _ _
  have hc0 : 0 ≤ min (1 / 4 : ℝ) (2 * A) := le_min (by norm_num) (by linarith)
  have hu0 : 0 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hf : 0 < u ^ ((2 : ℝ) / 3) * Real.log u ^ ((1 : ℝ) / 3) := by positivity
  have hsecond : 0 ≤ 2 * A * l / (u ^ ((2 : ℝ) / 3) * Real.log u ^ ((1 : ℝ) / 3)) := by positivity
  rcases le_or_gt M u with hMu | huM
  · have : min (1 / 4 : ℝ) (2 * A) * M ≤ u / 4 := by nlinarith
    linarith
  · have hul : u ≤ l := huM.le.trans hMle
    have h1 : u ^ ((2 : ℝ) / 3) ≤ M ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow hu0.le huM.le (by norm_num)
    have h2 : Real.log u ^ ((1 : ℝ) / 3) ≤ L ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hlogu.le (Real.log_le_log hu0 hul) (by norm_num)
    have e1 : M ^ ((2 : ℝ) / 3) * M = M ^ ((5 : ℝ) / 3) := by
      have : M ^ ((2 : ℝ) / 3) * M = M ^ ((2 : ℝ) / 3) * M ^ (1 : ℝ) := by rw [Real.rpow_one]
      rw [this, ← Real.rpow_add hM0]; norm_num
    have e2 : M ^ ((5 : ℝ) / 3) = l / L ^ ((1 : ℝ) / 3) := by
      rw [hM, Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hl0.le,
        ← Real.rpow_mul hLpos.le]
      norm_num
    have hL3 : 0 < L ^ ((1 : ℝ) / 3) := by positivity
    have hM53 : M ^ ((2 : ℝ) / 3) * M * L ^ ((1 : ℝ) / 3) = l := by
      rw [e1, e2]; field_simp
    have hfM : (u ^ ((2 : ℝ) / 3) * Real.log u ^ ((1 : ℝ) / 3)) * M ≤ l := by
      calc (u ^ ((2 : ℝ) / 3) * Real.log u ^ ((1 : ℝ) / 3)) * M
          ≤ (M ^ ((2 : ℝ) / 3) * L ^ ((1 : ℝ) / 3)) * M := by gcongr
        _ = l := by rw [← hM53]; ring
    have h3 : 2 * A * M ≤ 2 * A * l / (u ^ ((2 : ℝ) / 3) * Real.log u ^ ((1 : ℝ) / 3)) := by
      rw [le_div_iff₀ hf]; nlinarith
    have h4 : min (1 / 4 : ℝ) (2 * A) * M ≤ 2 * A * M := by nlinarith
    linarith

/-- **The twin form with the PNT exponent.** `Q(twin (box 1) λ) ≥ −C·exp(λ − c·λ^{3/5}/(log λ)^{1/5})`
for every `λ ≥ e`. -/
theorem twins_lower_KV_sharp : ∃ C c : ℝ, 0 < c ∧ ∀ l : ℝ, Real.exp 1 ≤ l →
    -(C * Real.exp (l - c * (l ^ ((3 : ℝ) / 5) / Real.log l ^ ((1 : ℝ) / 5)))) ≤
      weilQ (l + 1) (twin (box 1) l) := by
  obtain ⟨A, hA, -, hreg⟩ := abs_im_tau_le
  set c := min (1 / 4 : ℝ) (2 * A) with hc
  have hc0 : 0 < c := lt_min (by norm_num) (by linarith)
  refine ⟨4 * (K0 ^ 2 * Real.exp (3 / 4) * TwinKV.S1), c, hc0, fun l hl => ?_⟩
  have hl0 : 0 ≤ l := (Real.exp_pos 1).le.trans hl
  set M := l ^ ((3 : ℝ) / 5) / Real.log l ^ ((1 : ℝ) / 5) with hM
  set Tq : ZIdx → ℝ := fun q => max |(tz q).re| (Real.exp 3) with hTq
  have hT3 : ∀ q, Real.exp 3 ≤ Tq q := fun q => le_max_right _ _
  set r : ZIdx → ℝ := fun q => 1 - 2 * A / fKV (Tq q) with hr
  have hrP : ∀ q, |(poleP q).re| ≤ r q := fun q => near_rate hreg (hT3 q) q (le_max_left _ _)
  have hv1 : ∀ q, 1 ≤ ‖(zetaEquiv q).2.1‖ := fun q => by
    have e : ‖(zetaEquiv q).2.1‖ = ‖tz q‖ ^ 2 := by unfold tz; rw [← tau_sq, norm_pow]
    have h4 := four_lt_abs_im_zero q
    have h5 : |(zetaZeroFamily q).im| ≤ ‖tz q‖ := by
      have := Complex.abs_im_le_norm (zetaZeroFamily q - 1 / 2)
      unfold tz; rw [← norm_zZF_sub q]; simpa using this
    rw [e]; nlinarith
  have hterm : ∀ q, ‖cw q‖ * Real.exp (r q * l) ≤
      K0 ^ 2 * Real.exp (3 / 4) * (‖(zetaEquiv q).2.1‖ ^ (7 / 8 : ℝ))⁻¹ * Real.exp (l - c * M) := by
    intro q
    set v := ‖(zetaEquiv q).2.1‖ with hv
    have hv2 : v = ‖tz q‖ ^ 2 := by rw [hv]; unfold tz; rw [← tau_sq, norm_pow]
    have hv1' : 1 ≤ v := hv1 q
    have hv0 : 0 < v := by linarith
    have hTv : (Tq q) ^ ((1 : ℝ) / 4) ≤ Real.exp (3 / 4) * v ^ ((1 : ℝ) / 8) := by
      rcases le_total |(tz q).re| (Real.exp 3) with h | h
      · have hT : Tq q = Real.exp 3 := max_eq_right h
        rw [hT, ← Real.exp_mul]
        have h8 : 1 ≤ v ^ ((1 : ℝ) / 8) := Real.one_le_rpow hv1' (by norm_num)
        have e : Real.exp (3 * (1 / 4)) = Real.exp (3 / 4) := by norm_num
        rw [e]; nlinarith [Real.exp_pos (3 / 4)]
      · have hT : Tq q = |(tz q).re| := max_eq_left h
        rw [hT]
        have hre : |(tz q).re| ≤ ‖tz q‖ := Complex.abs_re_le_norm _
        have e : v ^ ((1 : ℝ) / 8) = ‖tz q‖ ^ ((1 : ℝ) / 4) := by
          rw [hv2, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num
        rw [e]
        have h14 := Real.rpow_le_rpow (abs_nonneg _) hre (by norm_num : (0 : ℝ) ≤ 1 / 4)
        have h1 : 1 ≤ Real.exp (3 / 4) := Real.one_le_exp (by norm_num)
        have h2 : 0 ≤ ‖tz q‖ ^ ((1 : ℝ) / 4) := by positivity
        nlinarith
    have hu3 : 3 ≤ Real.log (Tq q) := three_le_log (hT3 q)
    have hTpos : 0 < Tq q := (Real.exp_pos 3).trans_le (hT3 q)
    have hexpo := exponent_le hA hl hu3
    have hf : fKV (Tq q) =
        Real.log (Tq q) ^ ((2 : ℝ) / 3) * Real.log (Real.log (Tq q)) ^ ((1 : ℝ) / 3) := rfl
    rw [← hf] at hexpo
    have hkey : Real.exp (r q * l) ≤ (Tq q) ^ ((1 : ℝ) / 4) * Real.exp (l - c * M) := by
      have e1 : (Tq q) ^ ((1 : ℝ) / 4) = Real.exp (Real.log (Tq q) * (1 / 4)) :=
        Real.rpow_def_of_pos hTpos _
      rw [e1, ← Real.exp_add, Real.exp_le_exp]
      have h' : r q * l = l - 2 * A * l / fKV (Tq q) := by simp only [hr]; ring
      rw [h']
      linarith [hexpo]
    have hcw := norm_cw_le q
    have hsplit : v = v ^ ((1 : ℝ) / 8) * v ^ ((7 : ℝ) / 8) := by
      rw [← Real.rpow_add hv0]; norm_num
    calc ‖cw q‖ * Real.exp (r q * l)
        ≤ K0 ^ 2 / v * ((Tq q) ^ ((1 : ℝ) / 4) * Real.exp (l - c * M)) :=
          mul_le_mul hcw hkey (Real.exp_pos _).le (by positivity)
      _ ≤ K0 ^ 2 / v * (Real.exp (3 / 4) * v ^ ((1 : ℝ) / 8) * Real.exp (l - c * M)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTv (Real.exp_pos _).le)
            (by positivity)
      _ = K0 ^ 2 * Real.exp (3 / 4) * (v ^ (7 / 8 : ℝ))⁻¹ * Real.exp (l - c * M) := by
          have h8 : 0 < v ^ ((1 : ℝ) / 8) := by positivity
          have h78 : 0 < v ^ ((7 : ℝ) / 8) := by positivity
          have hv' : K0 ^ 2 / v = K0 ^ 2 / (v ^ ((1 : ℝ) / 8) * v ^ ((7 : ℝ) / 8)) := by
            rw [← hsplit]
          rw [hv']
          field_simp
  have hsum' : Summable fun q : ZIdx =>
      K0 ^ 2 * Real.exp (3 / 4) * (‖(zetaEquiv q).2.1‖ ^ (7 / 8 : ℝ))⁻¹ * Real.exp (l - c * M) :=
    (summable_S1.mul_left (K0 ^ 2 * Real.exp (3 / 4))).mul_right _
  have hs : Summable fun q : ZIdx => ‖cw q‖ * Real.exp (r q * l) :=
    hsum'.of_nonneg_of_le (fun q => by positivity) hterm
  have hQ := TwinLandau.Q_ge_of_rates twinData_zeta hrP hl0 hs
  have hbound : ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l) ≤
      K0 ^ 2 * Real.exp (3 / 4) * TwinKV.S1 * Real.exp (l - c * M) := by
    calc ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l)
        ≤ ∑' q : ZIdx, K0 ^ 2 * Real.exp (3 / 4) * (‖(zetaEquiv q).2.1‖ ^ (7 / 8 : ℝ))⁻¹ *
            Real.exp (l - c * M) := hs.tsum_le_tsum hterm hsum'
      _ = K0 ^ 2 * Real.exp (3 / 4) * TwinKV.S1 * Real.exp (l - c * M) := by
          rw [tsum_mul_right, tsum_mul_left]; rfl
  have h4 := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)
  have : -(4 * (K0 ^ 2 * Real.exp (3 / 4) * TwinKV.S1) * Real.exp (l - c * M)) ≤
      -(4 * ∑' q : ZIdx, ‖cw q‖ * Real.exp (r q * l)) := by linarith
  exact this.trans hQ

end TwinKV

#print axioms TwinLandau.Q_ge_of_rates
#print axioms TwinKV.twins_lower_KV
#print axioms TwinKV.twins_lower_KV'
#print axioms TwinKV.twins_lower_cut
#print axioms TwinKV.twins_lower_KV35
#print axioms TwinKV.twins_lower_KV_sharp
