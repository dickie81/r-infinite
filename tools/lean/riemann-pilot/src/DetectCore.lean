import Mathlib
import MollId
import DensityAsym
import WeilZeta

/-! # Zero detection from the Euler–Maclaurin bound at a zero (round 400)

Round 235's detection argument, moved from `external/pnt/DetectEM.lean` with its one PNT+ input displayed. `EMBound`
is the bound `|Σ_{n≤N} n^{−ρ}| ≤ N^{1−β}/|γ| + N^{−β}/2 + 2|γ|N^{−β}/β` at a zero `ρ = β + iγ` of `ζ` with
`0 < β ≤ 2` and `|γ| ≥ 2`, which PNT+'s Euler–Maclaurin formula gives (`DetectEM.norm_partial_zeta_le`).

* **`detectHyp_of_EMBound`**: `EMBound` gives `DetectHyp δ` for every `0 < δ ≤ ¼`.
* **`density_of_EMBound`**: hence `DensityXi (4(1+δ)) 11`, through `density_of_detect`.

`external/pnt/DetectEM.lean` proves `EMBound` from PNT+, and `external/zeta23/ShellDensity.lean` proves it from
zeta23's copy of the same PNT+ file. The two layers cannot be imported together (their PNT+ declarations clash), so
the proof lives here and each layer supplies the bound.
-/

open Real Filter Topology Complex Finset

noncomputable section

namespace DetectCore

open ShortWeil Pilot1ca Pilot1bt DirMean

/-- **The Euler–Maclaurin bound at a zero of `ζ`**, as a displayed input. -/
def EMBound : Prop :=
  ∀ {β γ : ℝ}, 0 < β → β ≤ 2 → 2 ≤ |γ| → riemannZeta ((β : ℂ) + γ * I) = 0 → ∀ {N : ℕ}, 1 ≤ N →
    ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖
      ≤ (N : ℝ) ^ (1 - β) / |γ| + (N : ℝ) ^ (-β) / 2 + 2 * |γ| * (N : ℝ) ^ (-β) / β

/-- The zero `½ ± iτ` of `ζ` with `β ≥ ½`. -/
theorem zeta_βsγs (i : ZeroIdx (sqF Xi)) : riemannZeta ((βs i : ℂ) + (γs i : ℝ) * I) = 0 := by
  have zeta_rhoXi : ∀ p : Bool × ZeroIdx (sqF Xi), riemannZeta (rhoXi p) = 0 := fun p => by
    have h := rhoXi_zetaEquiv (zetaEquiv.symm p)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    exact (zetaEquiv.symm p).1.2.1
  by_cases h : (tau i).im ≤ 0
  · have e : rhoXi (true, i) = (βs i : ℂ) + (γs i : ℝ) * I := by
      unfold βs γs; simp only [h, ↓reduceIte]; rw [abs_of_nonpos h]
      apply Complex.ext <;> simp [rhoXi]
    rw [← e]; exact zeta_rhoXi _
  · push Not at h
    have e : rhoXi (false, i) = (βs i : ℂ) + (γs i : ℝ) * I := by
      unfold βs γs; simp only [not_le.2 h, ↓reduceIte]; rw [abs_of_pos h]
      apply Complex.ext <;> simp [rhoXi]
    rw [← e]; exact zeta_rhoXi _

theorem aux_Z {U γ β q : ℝ} (hU : 1 ≤ U) (hγ : |γ| ≤ 2 * U) (hβ : 3 / 4 ≤ β) (hq : 0 ≤ q) :
    q / 2 + 2 * |γ| * q / β ≤ 7 * U * q := by
  have hβ0 : 0 < β := by linarith
  have h1 : 2 * |γ| / β ≤ 6 * U := by
    rw [div_le_iff₀ hβ0]
    have : 2 * |γ| ≤ 4 * U := by linarith
    have : 4 * U ≤ 6 * U * β := by nlinarith
    linarith
  have e : 2 * |γ| * q / β = (2 * |γ| / β) * q := by ring
  rw [e]
  have h2 := mul_le_mul_of_nonneg_right h1 hq
  have h3 : q / 2 ≤ U * q := by nlinarith
  linarith

theorem aux_exp1 {σ δ : ℝ} (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hδ1 : δ ≤ 1 / 4) :
    (2 * σ - 1) * (1 - σ) + (3 - 2 * σ + 2 * δ) * (1 - σ) + (-1) ≤ -(1 / 4) := by
  have e : (2 * σ - 1) * (1 - σ) + (3 - 2 * σ + 2 * δ) * (1 - σ) + (-1) = (2 + 2 * δ) * (1 - σ) - 1 := by ring
  rw [e]
  have h1 : 0 ≤ 1 - σ := by linarith
  have h2 : (2 + 2 * δ) * (1 - σ) ≤ (5 / 2) * (1 / 4) :=
    mul_le_mul (by linarith) (by linarith) h1 (by norm_num)
  linarith

theorem aux_exp2 {σ δ : ℝ} (hσ : 3 / 4 ≤ σ) (hδ0 : 0 < δ) :
    (2 * σ - 1) * (1 - σ) + 1 + -((3 - 2 * σ + 2 * δ) * σ) ≤ -(3 * δ / 2) := by
  have e : (2 * σ - 1) * (1 - σ) + 1 + -((3 - 2 * σ + 2 * δ) * σ) = -(2 * δ * σ) := by ring
  rw [e]
  have : 3 * δ / 2 ≤ 2 * δ * σ := by nlinarith
  linarith


/-- **Detection from the Euler–Maclaurin bound**, for every `0 < δ ≤ ¼`. -/
theorem detectHyp_of_EMBound (hEM : EMBound) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) : DetectHyp δ := by
  have hev : ∀ᶠ U : ℝ in atTop,
      (1 + Real.log U) * (U ^ (-(1 / 4 : ℝ)) + 14 * U ^ (-(3 * δ / 2))) ≤ 1 / 2 := by
    have h1 := tendsto_log_rpow_neg (a := 1 / 4) (by norm_num) 1 1
    have h2 := tendsto_log_rpow_neg (a := 3 * δ / 2) (by positivity) 14 14
    have h3 := h1.add h2
    rw [add_zero] at h3
    filter_upwards [h3.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with U hU
    have e : (1 + Real.log U) * (U ^ (-(1 / 4 : ℝ)) + 14 * U ^ (-(3 * δ / 2)))
        = (1 * Real.log U + 1) * U ^ (-(1 / 4 : ℝ)) + (14 * Real.log U + 14) * U ^ (-(3 * δ / 2)) := by
      ring
    rw [e]; exact hU
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.1 hev
  refine ⟨max U₁ 2, le_max_right _ _, fun σ U hσ hσ1 hU i hlo hhi hβ => ?_⟩
  have hU2 : 2 ≤ U := (le_max_right _ _).trans hU
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hUb := hU₁ U ((le_max_left _ _).trans hU)
  have hlU : 0 ≤ Real.log U := Real.log_nonneg hU1
  set β := βs i with hβdef
  set γ := γs i with hγdef
  have hγabs : |γ| = |(tau i).re| := abs_γs i
  have hγU : U ≤ |γ| := by rw [hγabs]; exact hlo
  have hγ2U : |γ| ≤ 2 * U := by rw [hγabs]; exact hhi
  have hγ2 : 2 ≤ |γ| := hU2.trans hγU
  have hβ1 : β < 1 := βs_lt_one i
  have hβ0 : 0 < β := by linarith
  -- the parameters
  set a := 3 - 2 * σ + 2 * δ with ha
  set y1 := U ^ (2 * σ - 1) with hy1def
  set y2 := U ^ a with hy2def
  set X := Xp σ U with hXdef
  set N := Np δ σ U with hNdef
  have hy1 : 1 ≤ y1 := Real.one_le_rpow hU1 (by linarith)
  have hy2 : 1 ≤ y2 := Real.one_le_rpow hU1 (by rw [ha]; linarith)
  have hX1 : 1 ≤ X := (Nat.one_le_floor_iff _).2 hy1
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff _).2 hy2
  have hy12 : y1 ≤ y2 := Real.rpow_le_rpow_of_exponent_le hU1 (by rw [ha]; linarith)
  have hXN : X ≤ N := Nat.floor_le_floor hy12
  have hXle : (X : ℝ) ≤ y1 := Nat.floor_le (by linarith)
  have hNle : (N : ℝ) ≤ y2 := Nat.floor_le (by linarith)
  have hNge : y2 / 2 ≤ N := by
    have h := Nat.lt_floor_add_one y2
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    change y2 < (N : ℝ) + 1 at h
    linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- the identity
  have hz := zeta_βsγs i
  have hZ := hEM hβ0 (by linarith) hγ2 hz hN1
  have hM := norm_moll_le (X := X) (γ := γ) hσ1 hβ
  have hid := moll_identity hX1 hXN ((β : ℂ) + γ * I)
  have hD : DPval X N β γ = moll X ((β : ℂ) + γ * I) * ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I)) - 1 := by
    rw [DPval_eq_cpow, hid]; ring
  -- `|M|` and `|Z|` in powers of `U`
  set p1 := (2 * σ - 1) * (1 - σ) with hp1
  have hXp : (X : ℝ) ^ (1 - σ) ≤ U ^ p1 := by
    calc (X : ℝ) ^ (1 - σ) ≤ y1 ^ (1 - σ) := Real.rpow_le_rpow hX0.le hXle (by linarith)
      _ = U ^ p1 := by rw [hy1def, ← Real.rpow_mul hU0.le]
  have hlX : 1 + Real.log X ≤ 1 + Real.log U := by
    have : (X : ℝ) ≤ U := hXle.trans (by
      calc y1 ≤ U ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
        _ = U := Real.rpow_one U)
    linarith [Real.log_le_log hX0 this]
  have hMb : ‖moll X ((β : ℂ) + γ * I)‖ ≤ U ^ p1 * (1 + Real.log U) :=
    hM.trans (mul_le_mul hXp hlX (by linarith [Real.log_nonneg (by exact_mod_cast hX1 : (1 : ℝ) ≤ X)])
      (by positivity))
  have hNa : (N : ℝ) ^ (1 - β) ≤ U ^ (a * (1 - σ)) := by
    calc (N : ℝ) ^ (1 - β) ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ ≤ y2 ^ (1 - σ) := Real.rpow_le_rpow hN0.le hNle (by linarith)
      _ = U ^ (a * (1 - σ)) := by rw [hy2def, ← Real.rpow_mul hU0.le]
  have hNb : (N : ℝ) ^ (-β) ≤ 2 * U ^ (-(a * σ)) := by
    have h2σ : (2 : ℝ) ^ σ ≤ 2 := by
      calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
        _ = 2 := Real.rpow_one 2
    calc (N : ℝ) ^ (-β) ≤ (N : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      _ ≤ (y2 / 2) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by positivity) hNge (by linarith)
      _ = y2 ^ (-σ) * 2 ^ σ := by
          rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            div_inv_eq_mul]
      _ ≤ y2 ^ (-σ) * 2 := by gcongr
      _ = 2 * U ^ (-(a * σ)) := by rw [hy2def, ← Real.rpow_mul hU0.le]; ring_nf
  have hZb : ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖
      ≤ U ^ (a * (1 - σ)) / U + 14 * U * U ^ (-(a * σ)) := by
    refine hZ.trans ?_
    have hNbpos : 0 ≤ (N : ℝ) ^ (-β) := by positivity
    have t1 : (N : ℝ) ^ (1 - β) / |γ| ≤ U ^ (a * (1 - σ)) / U :=
      div_le_div₀ (by positivity) hNa hU0 hγU
    have t2 : (N : ℝ) ^ (-β) / 2 + 2 * |γ| * (N : ℝ) ^ (-β) / β ≤ 7 * U * (N : ℝ) ^ (-β) :=
      aux_Z hU1 hγ2U (by linarith) hNbpos
    have t3 : 7 * U * (N : ℝ) ^ (-β) ≤ 14 * U * U ^ (-(a * σ)) := by
      have := mul_le_mul_of_nonneg_left hNb (by linarith : (0 : ℝ) ≤ 7 * U)
      linarith
    linarith
  -- the two exponents
  have hE1 : U ^ p1 * (U ^ (a * (1 - σ)) / U) ≤ U ^ (-(1 / 4 : ℝ)) := by
    have e : U ^ p1 * (U ^ (a * (1 - σ)) / U) = U ^ (p1 + a * (1 - σ) + (-1)) := by
      rw [Real.rpow_add hU0, Real.rpow_add hU0, Real.rpow_neg_one]; ring
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hU1 (by rw [hp1, ha]; exact aux_exp1 hσ hσ1 hδ1)
  have hE2 : U ^ p1 * (14 * U * U ^ (-(a * σ))) ≤ 14 * U ^ (-(3 * δ / 2)) := by
    have e : U ^ p1 * (14 * U * U ^ (-(a * σ))) = 14 * U ^ (p1 + 1 + (-(a * σ))) := by
      rw [Real.rpow_add hU0, Real.rpow_add hU0, Real.rpow_one]; ring
    rw [e]
    gcongr
    rw [hp1, ha]; exact aux_exp2 hσ hδ0
  have hMZ : ‖moll X ((β : ℂ) + γ * I)‖ * ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖ ≤ 1 / 2 := by
    calc ‖moll X ((β : ℂ) + γ * I)‖ * ‖∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I))‖
        ≤ (U ^ p1 * (1 + Real.log U)) * (U ^ (a * (1 - σ)) / U + 14 * U * U ^ (-(a * σ))) :=
          mul_le_mul hMb hZb (norm_nonneg _) (by positivity)
      _ = (1 + Real.log U) * (U ^ p1 * (U ^ (a * (1 - σ)) / U) + U ^ p1 * (14 * U * U ^ (-(a * σ)))) := by
          ring
      _ ≤ (1 + Real.log U) * (U ^ (-(1 / 4 : ℝ)) + 14 * U ^ (-(3 * δ / 2))) := by gcongr
      _ ≤ 1 / 2 := hUb
  rw [hD]
  have := norm_sub_norm_le (1 : ℂ) (moll X ((β : ℂ) + γ * I) * ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-((β : ℂ) + γ * I)))
  rw [norm_one, norm_mul, norm_sub_rev] at this
  linarith


/-- **Zero density from the Euler–Maclaurin bound**: `N(σ, T) ≪ T^{4(1+δ)(1−σ)}(log T)^{11}`. -/
theorem density_of_EMBound (hEM : EMBound) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    DensityXi (4 * (1 + δ)) 11 :=
  density_of_detect hδ0 hδ1 (detectHyp_of_EMBound hEM hδ0 hδ1)

end DetectCore

#print axioms DetectCore.zeta_βsγs
#print axioms DetectCore.aux_Z
#print axioms DetectCore.aux_exp1
#print axioms DetectCore.aux_exp2
#print axioms DetectCore.detectHyp_of_EMBound
#print axioms DetectCore.density_of_EMBound
