import Mathlib
import Zeta
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete

open Real Complex MeasureTheory Set

noncomputable section

namespace SlogZeta

open Pilot1ca Pilot1bt

/-! ## 1. The two zero counts agree at good heights -/

theorem nontriv_iff {ρ : ℂ} (hi : 0 < ρ.im) :
    Pilot1bt.IsNontrivialZero ρ ↔ Zeta23.IsNontrivialZero ρ := by
  constructor
  · intro h; exact ⟨h.1, h.re_pos, h.re_lt_one⟩
  · rintro ⟨hz, -, -⟩
    refine ⟨hz, ?_⟩
    rintro ⟨n, rfl⟩
    simp at hi

/-- Zeros with `0 < γ < T`. -/
def Zs (T : ℝ) : Set ℂ := {ρ | Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im < T}

theorem Zs_finite (T : ℝ) : (Zs T).Finite :=
  (finite_zeros_below T).subset fun _ ⟨h, h0, h1⟩ => ⟨(nontriv_iff h0).2 h, h0, h1⟩

theorem finsum_eq_card {s : Set ℂ} (hs : s.Finite) (f : ℂ → ℕ) :
    ∑ᶠ ρ ∈ s, f ρ = Nat.card (Σ ρ : s, Fin (f ρ)) := by
  have := hs.fintype
  rw [Nat.card_sigma, finsum_mem_eq_finite_toFinset_sum _ hs]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← Finset.sum_coe_sort hs.toFinset]
  exact Finset.sum_equiv (Equiv.subtypeEquivRight fun x => by simp) (by simp) (fun _ _ => rfl)

/-- `Ncnt zetaOrd T` is the number of zeros with `0 < γ < T`, with multiplicity. -/
theorem Ncnt_eq (T : ℝ) : Ncnt zetaOrd T = ((∑ᶠ ρ ∈ Zs T, Zeta23.zeroMult ρ : ℕ) : ℝ) := by
  unfold Ncnt
  rw [finsum_eq_card (Zs_finite T), ← Nat.card_coe_set_eq]
  congr 1
  refine Nat.card_congr ?_
  exact
    { toFun := fun p => ⟨⟨p.1.1.1.1, (nontriv_iff p.1.2).1 p.1.1.1.2, p.1.2, p.2⟩, p.1.1.2⟩
      invFun := fun q => ⟨⟨⟨⟨q.1.1, (nontriv_iff q.1.2.2.1).2 q.1.2.1⟩, q.2⟩, q.1.2.2.1⟩, q.1.2.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }

/-- At a good height, `zerosIn 0 T = Zs T`. -/
theorem zerosIn_eq {T : ℝ} (hT : Zeta23.RvM.GoodHeight T) : Zeta23.zerosIn 0 T = Zs T := by
  ext ρ
  simp only [Zeta23.zerosIn, Zs, mem_ofPred_eq]
  constructor
  · rintro ⟨h, h0, h1⟩; exact ⟨h, h0, lt_of_le_of_ne h1 (hT ρ h)⟩
  · rintro ⟨h, h0, h1⟩; exact ⟨h, h0, h1.le⟩

theorem Ncnt_good {T : ℝ} (hT : Zeta23.RvM.GoodHeight T) :
    Ncnt zetaOrd T = (Zeta23.Ncount 0 T : ℝ) := by
  rw [Ncnt_eq, Zeta23.Ncount, zerosIn_eq hT]

/-! ## 2. The argument principle with one end fixed -/

section Contour

open Zeta23 Zeta23.RvM

/-- `N(T₁, T₂) = ∫_{T₁}^{T₂} μ + O(log T₁ + log T₂)` at good heights above Backlund's threshold. -/
theorem Ncount_contour {CB TB : ℝ}
    (hB : ∀ T : ℝ, TB ≤ T → GoodHeight T →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ CB * Real.log T)
    {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (hTB : TB ≤ T₁) (h12 : T₁ < T₂) (hg1 : GoodHeight T₁)
    (hg2 : GoodHeight T₂) :
    |(Ncount T₁ T₂ : ℝ) - ∫ t in T₁..T₂, mu t|
      ≤ (|CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂) / Real.pi := by
  have hN := N_eq_halfContour_completedZeta h1 h12 hg1 hg2
  have hsplit := halfContour_completedZeta_split h1 h12 hg1 hg2
  have hgam := gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  have hbk1 := hB T₁ hTB hg1
  have hbk2 := hB T₂ (by linarith) hg2
  have hvert := vertical_two T₁ T₂
  have hlog₁0 : 0 ≤ Real.log T₁ := Real.log_nonneg h1
  have hlog₂0 : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hζ : |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
    unfold halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [eim]
    have hmulI : ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
        = (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))).symm
    have e1 : CB * Real.log T₁ ≤ |CB| * Real.log T₁ :=
      mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₁0
    have e2 : CB * Real.log T₂ ≤ |CB| * Real.log T₂ :=
      mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₂0
    calc _ ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im|
          + |((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by rw [hmulI]; linarith
  have e : (Ncount T₁ T₂ : ℝ) - ∫ t in T₁..T₂, mu t
      = (halfContour (logDeriv riemannZeta) T₁ T₂).im / Real.pi := by
    rw [hN, hsplit, Complex.add_im, ← hgam]; ring
  rw [e, abs_div, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right hζ Real.pi_pos.le

end Contour

/-! ## 3. Stirling: `∫ μ = N₀(b) − N₀(a) + O(1)` -/

theorem hasDerivAt_N0 {r : ℝ} (hr : 0 < r) :
    HasDerivAt N0 (1 / (2 * π) * Real.log (r / (2 * π))) r := by
  have hπ : 0 < 2 * π := by positivity
  have h1 : HasDerivAt (fun r : ℝ => r / (2 * π)) (1 / (2 * π)) r := by
    simpa using (hasDerivAt_id r).div_const (2 * π)
  have h2 := (h1.log (by positivity)).sub_const 1
  have h := h1.mul h2
  unfold N0
  convert h using 1
  field_simp
  ring

theorem continuousOn_L {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun τ : ℝ => 1 / (2 * π) * Real.log (τ / (2 * π))) (uIcc a b) := by
  refine continuousOn_const.mul (ContinuousOn.log (by fun_prop) fun x hx => ?_)
  rw [uIcc_of_le hab] at hx
  have : 0 < x := by linarith [hx.1]
  positivity

theorem N0_sub_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    N0 b - N0 a = ∫ τ in a..b, 1 / (2 * π) * Real.log (τ / (2 * π)) := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_N0 ?_)
    ((continuousOn_L ha hab).intervalIntegrable)).symm
  rw [uIcc_of_le hab] at hx; linarith [hx.1]

theorem continuous_mu : Continuous Zeta23.mu := Zeta23.gammaFacts.smooth.continuous

theorem int_mu_near {Cs : ℝ}
    (hst : ∀ τ : ℝ, 1 ≤ |τ| →
      |Zeta23.mu τ - (1 / (2 * π)) * Real.log (|τ| / (2 * π))| ≤ Cs / τ ^ 2)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∫ τ in a..b, Zeta23.mu τ) - (N0 b - N0 a)| ≤ |Cs| := by
  have ha0 : 0 < a := by linarith
  rw [N0_sub_eq ha0 hab, ← intervalIntegral.integral_sub (continuous_mu.intervalIntegrable _ _)
    ((continuousOn_L ha0 hab).intervalIntegrable)]
  have hg : ContinuousOn (fun τ : ℝ => |Cs| / τ ^ 2) (uIcc a b) := by
    refine continuousOn_const.div (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le hab] at hx; have : 0 < x := by linarith [hx.1]
    positivity
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
    (Filter.Eventually.of_forall fun τ (hτ : τ ∈ Ioc a b) => by
      have hτ1 : 1 ≤ τ := by linarith [hτ.1]
      have h := hst τ (by rw [abs_of_pos (by linarith)]; exact hτ1)
      rw [abs_of_pos (by linarith : (0:ℝ) < τ)] at h
      rw [Real.norm_eq_abs]
      exact h.trans (div_le_div_of_nonneg_right (le_abs_self Cs) (by positivity)))
    hg.intervalIntegrable
  have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun τ : ℝ => -(|Cs| / τ)) (|Cs| / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have := ((hasDerivAt_id x).inv hx0).const_mul (-|Cs|)
    convert this using 1
    · funext τ; simp [div_eq_mul_inv]
    · simp; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hg.intervalIntegrable, Real.norm_eq_abs]
    at hle
  have hb0 : 0 < b := by linarith
  have : -(|Cs| / b) - -(|Cs| / a) ≤ |Cs| := by
    have h1 : |Cs| / a ≤ |Cs| := div_le_self (abs_nonneg _) ha
    have h2 : 0 ≤ |Cs| / b := by positivity
    linarith
  linarith

/-! ## 4. `S(T) = O(log T)` -/

theorem log_le_two_log {T x : ℝ} (hT : 2 ≤ T) (hx : 0 < x) (hxT : x ≤ T + 1) :
    Real.log x ≤ 2 * Real.log T := by
  have : x ≤ T ^ 2 := by nlinarith
  calc Real.log x ≤ Real.log (T ^ 2) := Real.log_le_log hx this
    _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring

/-- `N₀(b) − N₀(a) ≤ log b` for `2π ≤ a ≤ b ≤ a + 1`. -/
theorem N0_sub_le {a b : ℝ} (ha : 2 * π ≤ a) (hab : a ≤ b) (hb : b ≤ a + 1) :
    N0 b - N0 a ≤ Real.log b := by
  have hπ : 0 < 2 * π := by positivity
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  set c := 1 / (2 * π) * Real.log (b / (2 * π))
  rw [N0_sub_eq ha0 hab]
  have hmono : ∫ τ in a..b, 1 / (2 * π) * Real.log (τ / (2 * π)) ≤ ∫ _ in a..b, c := by
    refine intervalIntegral.integral_mono_on hab ((continuousOn_L ha0 hab).intervalIntegrable)
      intervalIntegrable_const fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right hx.2 hπ.le)) (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hc0 : 0 ≤ c := mul_nonneg (by positivity)
    (Real.log_nonneg (by rw [le_div_iff₀ hπ]; linarith))
  have hc : c ≤ Real.log b := by
    have h1 : Real.log (b / (2 * π)) ≤ Real.log b :=
      Real.log_le_log (by positivity) (div_le_self hb0.le (by nlinarith [Real.pi_gt_three]))
    have h2 : 1 / (2 * π) ≤ 1 := by rw [div_le_one hπ]; nlinarith [Real.pi_gt_three]
    have h3 : 0 ≤ Real.log (b / (2 * π)) := Real.log_nonneg (by rw [le_div_iff₀ hπ]; linarith)
    calc c ≤ 1 * Real.log (b / (2 * π)) := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ Real.log b := by linarith
  nlinarith

section Slog

open Zeta23 Zeta23.RvM

/-- **`S(T) = O(log T)`, eventually**, from zeta23's argument principle, Backlund's bound and
Stirling. -/
theorem Slog_eventually : ∃ A B T₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 2 * π + 2 ≤ T₀ ∧
    ∀ T, T₀ ≤ T → |Sz zetaOrd T| ≤ A + B * Real.log T := by
  obtain ⟨CB, TB, hB⟩ := backlund_horizontal
  obtain ⟨Cs, hCs⟩ := gammaFacts.stirling
  obtain ⟨T₁, hT₁, hg1⟩ := exists_goodHeight (max (max TB 1) (2 * π))
  have hT₁TB : TB ≤ T₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT₁.1
  have hT₁1 : 1 ≤ T₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT₁.1
  have hT₁π : 2 * π ≤ T₁ := le_trans (le_max_right _ _) hT₁.1
  have hπ : 0 < π := Real.pi_pos
  set K : ℝ := (Ncount 0 T₁ : ℝ)
  have hL1 : 0 ≤ Real.log T₁ := Real.log_nonneg hT₁1
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = |K| + |Pilot1ca.N0 T₁| + |Cs| + |CB| * Real.log T₁ / π + 1 + 7 / 8 :=
    ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = 2 * |CB| / π + 2 := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hAd]; positivity
  have hB0 : 0 ≤ B := by rw [hBd]; positivity
  refine ⟨A, B, T₁ + 2, hA, hB0, by linarith, fun T hT => ?_⟩
  have hT2 : 2 ≤ T := by linarith
  have hTπ : 2 * π ≤ T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  obtain ⟨T₂, hT₂, hg2⟩ := exists_goodHeight T
  obtain ⟨T₃, hT₃, hg3⟩ := exists_goodHeight (T - 1)
  have h12 : T₁ < T₂ := by linarith [hT₂.1]
  have h13 : T₁ < T₃ := by linarith [hT₃.1]
  -- the counts
  have hN2 : Ncnt zetaOrd T₂ = K + (Ncount T₁ T₂ : ℝ) := by
    rw [Ncnt_good hg2, Ncount_add (by linarith) h12.le]; push_cast; rfl
  have hN3 : Ncnt zetaOrd T₃ = K + (Ncount T₁ T₃ : ℝ) := by
    rw [Ncnt_good hg3, Ncount_add (by linarith) h13.le]; push_cast; rfl
  have hup : Ncnt zetaOrd T ≤ Ncnt zetaOrd T₂ := Ncnt_mono zetaOrd_finite hT₂.1
  have hlo : Ncnt zetaOrd T₃ ≤ Ncnt zetaOrd T := Ncnt_mono zetaOrd_finite (by linarith [hT₃.2])
  -- contour and Stirling
  have hc2 := Ncount_contour hB hT₁1 hT₁TB h12 hg1 hg2
  have hc3 := Ncount_contour hB hT₁1 hT₁TB h13 hg1 hg3
  have hs2 := int_mu_near hCs hT₁1 h12.le
  have hs3 := int_mu_near hCs hT₁1 h13.le
  have hd2 := N0_sub_le hTπ hT₂.1 hT₂.2
  have hT₃T : T₃ ≤ T := by linarith [hT₃.2]
  have hd3 := N0_sub_le (by linarith [hT₃.1]) hT₃T (by linarith [hT₃.1])
  -- logs
  have hl2 : Real.log T₂ ≤ 2 * Real.log T := log_le_two_log hT2 (by linarith [hT₂.1]) hT₂.2
  have hl3 : Real.log T₃ ≤ Real.log T := Real.log_le_log (by linarith [hT₃.1]) hT₃T
  have hl30 : 0 ≤ Real.log T₃ := Real.log_nonneg (by linarith [hT₃.1])
  have hD2 : (|CB| * Real.log T₁ + π + |CB| * Real.log T₂) / π ≤ |CB| * Real.log T₁ / π + 1 + 2 * |CB| / π * Real.log T := by
    rw [div_le_iff₀ hπ]
    have : |CB| * Real.log T₂ ≤ |CB| * (2 * Real.log T) := mul_le_mul_of_nonneg_left hl2 (abs_nonneg _)
    field_simp; nlinarith
  have hD3 : (|CB| * Real.log T₁ + π + |CB| * Real.log T₃) / π ≤ |CB| * Real.log T₁ / π + 1 + 2 * |CB| / π * Real.log T := by
    rw [div_le_iff₀ hπ]
    have : |CB| * Real.log T₃ ≤ |CB| * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    field_simp; nlinarith
  obtain ⟨hc2a, hc2b⟩ := abs_le.1 hc2
  obtain ⟨hc3a, hc3b⟩ := abs_le.1 hc3
  obtain ⟨hs2a, hs2b⟩ := abs_le.1 hs2
  obtain ⟨hs3a, hs3b⟩ := abs_le.1 hs3
  have hK := neg_abs_le K
  have hK' := le_abs_self K
  have hPilot1ca.N0 := neg_abs_le (Pilot1ca.N0 T₁)
  have hN0' := le_abs_self (Pilot1ca.N0 T₁)
  have hlT2 : Real.log T₂ ≤ 2 * Real.log T := hl2
  have hBl : B * Real.log T = 2 * |CB| / π * Real.log T + 2 * Real.log T := by rw [hBd]; ring
  unfold Sz
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **`S(t) = O(log t)` on `t ≥ 14`**: von Mangoldt's bound for Mathlib's `riemannZeta`, as the
hypothesis `hSlog` of `wall_law_zeta` asks for it. -/
theorem Slog_zeta : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 14 ≤ t → |Sz zetaOrd t| ≤ C * Real.log t := by
  obtain ⟨A, B, T₀, hA, hB, hT₀, h⟩ := Slog_eventually
  have hl14 : 0 < Real.log 14 := Real.log_pos (by norm_num)
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = Ncnt zetaOrd T₀ + |Pilot1ca.N0 14| + |Pilot1ca.N0 T₀| + 7 / 8 :=
    ⟨_, rfl⟩
  have hE : 0 ≤ E := by
    have : 0 ≤ Ncnt zetaOrd T₀ := by unfold Ncnt; positivity
    rw [hEd]; positivity
  refine ⟨A / Real.log 14 + B + E / Real.log 14, by positivity, fun t ht => ?_⟩
  have hlt : Real.log 14 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlt0 : 0 < Real.log t := by linarith
  have hAl : A ≤ A / Real.log 14 * Real.log t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl14]; exact mul_le_mul_of_nonneg_left hlt hA
  have hEl : E ≤ E / Real.log 14 * Real.log t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl14]; exact mul_le_mul_of_nonneg_left hlt hE
  have hEl0 : 0 ≤ E / Real.log 14 * Real.log t := by positivity
  have hAl0 : 0 ≤ A / Real.log 14 * Real.log t := by positivity
  rcases le_or_gt T₀ t with hTt | hTt
  · have := h t hTt
    nlinarith
  · have hπ14 : 2 * π ≤ 14 := by nlinarith [Real.pi_lt_d2]
    have hm1 : Pilot1ca.N0 14 ≤ Pilot1ca.N0 t := N0_mono hπ14 ht
    have hm2 : Pilot1ca.N0 t ≤ Pilot1ca.N0 T₀ := N0_mono (by linarith) hTt.le
    have hn1 : 0 ≤ Ncnt zetaOrd t := by unfold Ncnt; positivity
    have hn2 : Ncnt zetaOrd t ≤ Ncnt zetaOrd T₀ := Ncnt_mono zetaOrd_finite hTt.le
    have hS : |Sz zetaOrd t| ≤ E := by
      unfold Sz; rw [abs_le]
      constructor <;> linarith [hEd, le_abs_self (Pilot1ca.N0 14), neg_abs_le (Pilot1ca.N0 14), le_abs_self (Pilot1ca.N0 T₀),
        neg_abs_le (Pilot1ca.N0 T₀)]
    have : 0 ≤ B * Real.log t := mul_nonneg hB hlt0.le
    nlinarith

end Slog

/-- **1ca(i)–(iii) for ζ, with von Mangoldt's bound proved.** `wall_law_zeta` without the hypothesis
`hSlog`. The constant `C` of the conclusion is the larger of Littlewood's constant `C₁` (still a named
input, `hS1log`) and the constant of `Slog_zeta`. -/
theorem wall_law_zeta_S {G a L Δ C₁ lo hi Ts Tu : ℝ} {H : Finset ℝ}
    (h_height : ∀ p, G ≤ zetaOrd p)
    (hG14 : 14 ≤ G) (hGe : G ≤ 2 * π * Real.exp 1) (hLG : G ≤ L)
    (hH : ∀ h ∈ H, 0 < h ∧ h ≤ L) (hΔ : 0 < Δ) (hC₁ : 0 ≤ C₁)
    (hS1log : ∀ t, G ≤ t → |S1 (Sz zetaOrd) G t| ≤ C₁ * Real.log t)
    (hlo : L < lo) (hloΔ : G + 2 * Δ ≤ lo) (hTG : TG G H lo < 1)
    (hTs : Ts ∈ Set.Icc lo hi) (hTu : Tu ∈ Set.Icc lo hi)
    (hcrit : Fp G (2 * π * Real.exp (2 * a)) H Ts = 0)
    (hminu : ∀ T ∈ Set.Icc lo hi, Fk zetaOrd a H Tu ≤ Fk zetaOrd a H T) :
    ∃ C : ℝ, C₁ ≤ C ∧ ∃ OscInf : ℝ,
      Filter.Tendsto (fun X => ∫ r in G..X, Sz zetaOrd r * (4 / r)) Filter.atTop (nhds OscInf) ∧
      |Fk zetaOrd a H Tu - (Fs G a H Ts + OscInf)|
        ≤ (8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C) * (Real.log hi / Real.sqrt lo) ∧
      (Tu - Ts) ^ 2 ≤ 4 * ((8 * C * Real.sqrt Δ + 16 * C / Real.sqrt Δ + 12 * C)
        * (Real.log hi / Real.sqrt lo)) * hi / (1 - TG G H lo) := by
  obtain ⟨C₀, hC₀, hS⟩ := Slog_zeta
  refine ⟨max C₀ C₁, le_max_right _ _, ?_⟩
  have hlog : ∀ t, G ≤ t → 0 ≤ Real.log t := fun t ht => Real.log_nonneg (by linarith)
  exact wall_law_zeta h_height hG14 hGe hLG hH hΔ (le_trans hC₁ (le_max_right _ _))
    (fun t ht => (hS t (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog t ht)))
    (fun t ht => (hS1log t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlog t ht)))
    hlo hloΔ hTG hTs hTu hcrit hminu

end SlogZeta

#print axioms SlogZeta.Ncnt_good
#print axioms SlogZeta.Ncount_contour
#print axioms SlogZeta.int_mu_near
#print axioms SlogZeta.Slog_eventually
#print axioms SlogZeta.Slog_zeta
#print axioms SlogZeta.wall_law_zeta_S
