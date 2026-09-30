import LandauKV
import KaiserSplit

/-! # The Korobov–Vinogradov region in the Kaiser prefactor (round 234)

Round 164's `lam_prefactor` bounds the ground energy by `λ₁(a) ≤ K(a + 1)e^{10a − 4πe^{2a}}`. The factor
`eᵃ` over Connes' `e^{9a}` is the weight `e^{2a|Im τ|} ≤ eᵃ` of a zero, and round 164 said of it: "The known
zero-free regions only save a constant here." That holds for de la Vallée Poussin's region. The
Korobov–Vinogradov region (`LandauKV.zeroFree_KV`, round 215) saves a growing amount.

* `region`: with PNT+'s `ZetaNoZerosInBox` below height `e³`, every zero `β + iγ` with `|γ| ≤ T` has
  `β < 1 − A/f(T)`, `f(T) = (log T)^{2/3}(log log T)^{1/3}`, for every `T ≥ e³`.
* `abs_im_tau_le`: so the zeros of `Ξ` with `|Re τ| ≤ T` have `|Im τ| ≤ ½ − A/f(T)`.
* **`lam_prefactor_KV`**: `λ₁(a) ≤ K(a + 1)·exp(10a − c·a^{1/3}/(log a)^{1/3} − 4πe^{2a})` for `a ≥ 4`, with
  no RH input. The zeros below `2e^{40a}` get the weight `e^{a − 2aA/f(2e^{40a})}` (`Kaiser.lam_le_split`); those
  above keep `eᵃ`.

No bearing on RH: this is a sharper upper bound on `λ₁`.
-/

open Complex Real Set Filter

noncomputable section

namespace KaiserKV

open Pilot1ca Pilot1bt Kaiser

/-- The Korobov–Vinogradov width `f(T) = (log T)^{2/3}(log log T)^{1/3}`. -/
def fKV (T : ℝ) : ℝ := Real.log T ^ ((2 : ℝ) / 3) * Real.log (Real.log T) ^ ((1 : ℝ) / 3)

theorem three_le_log {T : ℝ} (hT : Real.exp 3 ≤ T) : 3 ≤ Real.log T :=
  (Real.le_log_iff_exp_le ((Real.exp_pos 3).trans_le hT)).2 hT

theorem fKV_pos {T : ℝ} (hT : Real.exp 3 ≤ T) : 0 < fKV T := by
  have h3 := three_le_log hT
  have hl : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  unfold fKV
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos hl _)

theorem fKV_mono {u v : ℝ} (hu : Real.exp 3 ≤ u) (huv : u ≤ v) : fKV u ≤ fKV v := by
  have h3 := three_le_log hu
  have hu0 : 0 < u := (Real.exp_pos 3).trans_le hu
  have hlog : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  have hll : 0 ≤ Real.log (Real.log u) := (Real.log_pos (by linarith)).le
  unfold fKV
  exact mul_le_mul (Real.rpow_le_rpow (by linarith) hlog (by norm_num))
    (Real.rpow_le_rpow hll (Real.log_le_log (by linarith) hlog) (by norm_num))
    (Real.rpow_nonneg hll _) (Real.rpow_nonneg (by linarith) _)

/-- **The zero-free region at every height up to `T`.** -/
theorem region : ∃ A : ℝ, 0 < A ∧ A ≤ fKV (Real.exp 3) / 2 ∧ ∀ T : ℝ, Real.exp 3 ≤ T →
    ∀ β γ : ℝ, |γ| ≤ T → riemannZeta (β + γ * I) = 0 → β < 1 - A / fKV T := by
  obtain ⟨A₀, hA₀, hKV⟩ := LandauKV.zeroFree_KV
  obtain ⟨σ₀, hσ₀, hbox⟩ := ZetaNoZerosInBox (Real.exp 3)
  have hf3 := fKV_pos (le_refl (Real.exp 3))
  set f3 := fKV (Real.exp 3)
  refine ⟨min A₀ (min ((1 - σ₀) * f3) (f3 / 2)), ?_, ?_, fun T hT β γ hγ hz => ?_⟩
  · exact lt_min hA₀ (lt_min (mul_pos (by linarith) hf3) (by linarith))
  · exact (min_le_right _ _).trans (min_le_right _ _)
  set A := min A₀ (min ((1 - σ₀) * f3) (f3 / 2))
  have hA0 : 0 ≤ A := (lt_min hA₀ (lt_min (mul_pos (by linarith) hf3) (by linarith))).le
  have hfT := fKV_pos hT
  have hf3T : f3 ≤ fKV T := fKV_mono (le_refl _) hT
  by_contra hβ
  push Not at hβ
  rcases le_or_gt (Real.exp 3) |γ| with h3 | h3
  · have hfγ := fKV_pos h3
    have hγT : fKV |γ| ≤ fKV T := fKV_mono h3 hγ
    have h1 : A / fKV T ≤ A₀ / fKV |γ| :=
      (div_le_div_of_nonneg_right (min_le_left _ _) hfT.le).trans
        (div_le_div_of_nonneg_left hA₀.le hfγ hγT)
    exact hKV β γ h3 (show 1 - A₀ / fKV |γ| ≤ β by linarith) hz
  · have h1 : A / fKV T ≤ 1 - σ₀ := by
      rw [div_le_iff₀ hfT]
      calc A ≤ (1 - σ₀) * f3 := (min_le_right _ _).trans (min_le_left _ _)
        _ ≤ (1 - σ₀) * fKV T := mul_le_mul_of_nonneg_left hf3T (by linarith)
    exact hbox γ h3.le β (by linarith) hz

/-- Each zero of `Ξ` is a zero of `ζ`, at both `½ ± iτ`. -/
theorem zeta_rhoXi (p : Bool × ZeroIdx (sqF Xi)) : riemannZeta (rhoXi p) = 0 := by
  have h := rhoXi_zetaEquiv (zetaEquiv.symm p)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact (zetaEquiv.symm p).1.2.1

/-- **The zeros of `Ξ` up to height `T`**: `|Im τ| ≤ ½ − A/f(T)`. -/
theorem abs_im_tau_le : ∃ A : ℝ, 0 < A ∧ A ≤ fKV (Real.exp 3) / 2 ∧ ∀ T : ℝ, Real.exp 3 ≤ T →
    ∀ i : ZeroIdx (sqF Xi), |(tau i).re| ≤ T → |(tau i).im| ≤ 1 / 2 - A / fKV T := by
  obtain ⟨A, hA, hA2, hreg⟩ := region
  refine ⟨A, hA, hA2, fun T hT i hi => ?_⟩
  have e1 : rhoXi (true, i) = ((1 / 2 - (tau i).im : ℝ) : ℂ) + ((tau i).re : ℝ) * I := by
    apply Complex.ext
    · simp [rhoXi]; ring
    · simp [rhoXi]
  have e2 : rhoXi (false, i) = ((1 / 2 + (tau i).im : ℝ) : ℂ) + ((-(tau i).re : ℝ) : ℝ) * I := by
    apply Complex.ext <;> simp [rhoXi]
  have h1 := hreg T hT _ _ hi (by rw [← e1]; exact zeta_rhoXi _)
  have h2 := hreg T hT _ _ (by rwa [abs_neg]) (by rw [← e2]; exact zeta_rhoXi _)
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem log_forty_one_lt : Real.log 41 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have : (2.7182818283 : ℝ) ^ 4 < Real.exp 1 ^ 4 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  linarith [show (41 : ℝ) < 2.7182818283 ^ 4 by norm_num]

/-- `f(2e^{40a}) ≤ (41a)^{2/3}(4 log a)^{1/3}` for `a ≥ 4`. -/
theorem fKV_le {a : ℝ} (ha : 4 ≤ a) :
    fKV (2 * Real.exp (40 * a)) ≤ (41 * a) ^ ((2 : ℝ) / 3) * (4 * Real.log a) ^ ((1 : ℝ) / 3) := by
  have ha0 : 0 < a := by linarith
  have hlogT : Real.log (2 * Real.exp (40 * a)) = Real.log 2 + 40 * a := by
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hT3 : Real.exp 3 ≤ 2 * Real.exp (40 * a) := by
    have := Real.exp_le_exp.2 (by linarith : (3 : ℝ) ≤ 40 * a); linarith [Real.exp_pos (40 * a)]
  have h3 := three_le_log hT3
  have hle1 : Real.log (2 * Real.exp (40 * a)) ≤ 41 * a := by rw [hlogT]; linarith
  have hloga : 4 / 3 ≤ Real.log a := by
    have : Real.log 4 ≤ Real.log a := Real.log_le_log (by norm_num) ha
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hle2 : Real.log (Real.log (2 * Real.exp (40 * a))) ≤ 4 * Real.log a := by
    calc Real.log (Real.log (2 * Real.exp (40 * a))) ≤ Real.log (41 * a) :=
          Real.log_le_log (by linarith) hle1
      _ = Real.log 41 + Real.log a := Real.log_mul (by norm_num) ha0.ne'
      _ ≤ 4 * Real.log a := by linarith [log_forty_one_lt]
  have hll : 0 ≤ Real.log (Real.log (2 * Real.exp (40 * a))) := (Real.log_pos (by linarith)).le
  unfold fKV
  exact mul_le_mul (Real.rpow_le_rpow (by linarith) hle1 (by norm_num))
    (Real.rpow_le_rpow hll hle2 (by norm_num)) (Real.rpow_nonneg hll _) (Real.rpow_nonneg (by positivity) _)

/-- **The Kaiser prefactor with the Korobov–Vinogradov saving**: for `a ≥ 4`,
`λ₁(a) ≤ K(a + 1)·exp(10a − c·a^{1/3}/(log a)^{1/3} − 4πe^{2a})`, with no RH input. -/
theorem lam_prefactor_KV : ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ a : ℝ, 4 ≤ a →
    lam a ≤ K * (a + 1) *
      Real.exp (10 * a - c * a ^ ((1 : ℝ) / 3) / Real.log a ^ ((1 : ℝ) / 3) - 4 * π * Real.exp (2 * a)) := by
  obtain ⟨K, hK, hsplit⟩ := lam_le_split
  obtain ⟨A, hA, hA2, htau⟩ := abs_im_tau_le
  have h41 : 0 < (41 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have h4 : 0 < (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨K, 2 * A / ((41 : ℝ) ^ ((2 : ℝ) / 3) * (4 : ℝ) ^ ((1 : ℝ) / 3)), hK, by positivity,
    fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  set T := 2 * Real.exp (40 * a)
  have hT3 : Real.exp 3 ≤ T := by
    have := Real.exp_le_exp.2 (by linarith : (3 : ℝ) ≤ 40 * a)
    simp only [T]; linarith [Real.exp_pos (40 * a)]
  have hfT := fKV_pos hT3
  have hf3T : fKV (Real.exp 3) ≤ fKV T := fKV_mono (le_refl _) hT3
  set s := 2 * a * A / fKV T
  have hs : s ≤ a := by
    simp only [s]
    rw [div_le_iff₀ hfT]
    nlinarith
  have hκ : ∀ i : ZeroIdx (sqF Xi), |(tau i).re| ≤ T → Real.exp (2 * a * |(tau i).im|) ≤ Real.exp (a - s) := by
    intro i hi
    refine Real.exp_le_exp.2 ?_
    have h := htau T hT3 i hi
    have e : a - s = 2 * a * (1 / 2 - A / fKV T) := by simp only [s]; field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left h (by linarith)
  have hL := hsplit a ha (Real.exp (a - s)) (Real.one_le_exp (by linarith)) hκ
  -- the saving
  have hlog : 0 < Real.log a := Real.log_pos (by linarith)
  have hla : 0 < Real.log a ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hlog _
  have ha23 : 0 < a ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos ha0 _
  have ha13 : 0 < a ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ha0 _
  have hden : (41 * a) ^ ((2 : ℝ) / 3) * (4 * Real.log a) ^ ((1 : ℝ) / 3)
      = (41 : ℝ) ^ ((2 : ℝ) / 3) * (4 : ℝ) ^ ((1 : ℝ) / 3) * a ^ ((2 : ℝ) / 3) * Real.log a ^ ((1 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num) ha0.le, Real.mul_rpow (by norm_num) hlog.le]; ring
  have hsplit_a : a = a ^ ((1 : ℝ) / 3) * a ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add ha0]; norm_num
  have hsave : 2 * A / ((41 : ℝ) ^ ((2 : ℝ) / 3) * (4 : ℝ) ^ ((1 : ℝ) / 3)) * a ^ ((1 : ℝ) / 3)
      / Real.log a ^ ((1 : ℝ) / 3) ≤ s := by
    have hfle := fKV_le ha
    rw [hden] at hfle
    have h1 : 2 * a * A / ((41 : ℝ) ^ ((2 : ℝ) / 3) * (4 : ℝ) ^ ((1 : ℝ) / 3) * a ^ ((2 : ℝ) / 3)
        * Real.log a ^ ((1 : ℝ) / 3)) ≤ s :=
      div_le_div_of_nonneg_left (by positivity) hfT hfle
    refine le_of_eq_of_le ?_ h1
    have e : 2 * a * A = 2 * A * (a ^ ((1 : ℝ) / 3) * a ^ ((2 : ℝ) / 3)) := by
      rw [← hsplit_a]; ring
    rw [e]
    field_simp
  refine hL.trans ?_
  rw [mul_assoc (K * (a + 1)), ← Real.exp_add]
  gcongr
  linarith

end KaiserKV

#print axioms KaiserKV.region
#print axioms KaiserKV.abs_im_tau_le
#print axioms KaiserKV.lam_prefactor_KV
