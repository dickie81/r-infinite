import KaiserKV
import WeilLandau
import WeilCount
import Unconditional

/-!
# The Korobov–Vinogradov region as a lower bound on the twin form (round 237)

`weil_twins_rate` (WeilLandau) says: `Q(twin (box 1) λ) ≥ −C e^{σλ}` for all `λ ≥ 0` iff every zero
has `|2 Re ρ − 1| ≤ σ`. The KV zero-free region (`KaiserKV.abs_im_tau_le`) gives, for the zeros up
to height `T`, `|2 Re ρ − 1| ≤ 1 − 2A/f(T)`, `f(T) = (log T)^{2/3}(log log T)^{1/3}`; the zeros
above `T` are controlled by the tail `Σ_{|t_ρ| > T} |ĝ₀(t_ρ)|² ≪ T^{−1/4}`. With `T = e^{8λ}` this
gives the unconditional lower bound `Q(twin (box 1) λ) ≥ −C·exp((1 − A/f(e^{8λ}))·λ)` for `λ ≥ 1`,
i.e. `−C·exp(λ − c·λ^{1/3}(log 8λ)^{−1/3})`: the twin form's negative part is subexponential by
exactly the KV margin.
-/

open Complex Real Set
open Pilot1ca Pilot1bt PilotWeil KaiserKV

namespace TwinLandau

variable {ι : Type*} {P c : ι → ℂ} {G : ℂ → ℂ} {Q : ℝ → ℝ}

/-- **The converse bound with a rate per pole**: if `|Re P_q| ≤ r_q` for every `q` and
`Σ ‖c_q‖ e^{r_q λ} < ∞`, then `Q(λ) ≥ −4 Σ_q ‖c_q‖ e^{r_q λ}`. -/
theorem Q_ge_of_rates (D : TwinData P c G Q) {r : ι → ℝ} (hr : ∀ q, |(P q).re| ≤ r q) {l : ℝ}
    (hl : 0 ≤ l) (hs : Summable fun q => ‖c q‖ * Real.exp (r q * l)) :
    -(4 * ∑' q, ‖c q‖ * Real.exp (r q * l)) ≤ Q l := by
  rw [← Aw_eq D hl]
  have hb : ∀ q, ‖wq P c q l‖ ≤ 4 * (‖c q‖ * Real.exp (r q * l)) := fun q => by
    have h := norm_wq_le_of (P := P) (c := c) (hr q) l
    rw [abs_of_nonneg hl] at h
    linarith
  have hs' : Summable fun q => ‖wq P c q l‖ :=
    (hs.mul_left 4).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have h1 : ‖Wsum P c l‖ ≤ 4 * ∑' q, ‖c q‖ * Real.exp (r q * l) := by
    unfold Wsum
    calc ‖∑' q, wq P c q l‖ ≤ ∑' q, ‖wq P c q l‖ := norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' q, 4 * (‖c q‖ * Real.exp (r q * l)) := hs'.tsum_le_tsum hb (hs.mul_left 4)
      _ = _ := tsum_mul_left
  have h2 := neg_abs_le (Wsum P c l).re
  have h3 := Complex.abs_re_le_norm (Wsum P c l)
  unfold Aw; linarith

end TwinLandau

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

end TwinKV

#print axioms TwinLandau.Q_ge_of_rates
#print axioms TwinKV.twins_lower_KV
