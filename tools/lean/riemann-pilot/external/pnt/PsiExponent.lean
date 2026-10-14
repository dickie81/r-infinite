/-
# Round 469: the exponent of the error in the prime number theorem

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `Θ` be the supremum of the real parts of the nontrivial zeros of `ζ` (`Theta`). Then
`½ ≤ Θ ≤ 11/12` (`half_le_Theta`, `Theta_le`) and `limsup_{x→∞} log|ψ(x) − x| / log x = Θ` (`limsup_expo`).

* `Theta_le`: round 466's half-plane `Re s > 11/12` (`Eis.ne_zero_of_re_gt_eleven_twelfths`).
* `half_le_Theta`: round 220's zero with `Re ρ ≥ ½` (`PsiOmega.exists_zero_re_ge_half`).
* `psi_isBigO_Theta`: `ψ(x) − x = O(x^{Θ+ε})` for every `ε > 0`. It is round 338's `psi_isBigO_of_zeroFree`
  at `Θ`, since `ζ(s) ≠ 0` on `Re s > Θ` (`zeta_ne_zero_of_Theta_lt`) and `Θ < 1`.
* `psi_omega_Theta`: `ψ(x) − x = Ω±(x^{Θ−ε})` for `0 < ε < Θ`. It is round 220's `PsiOmega.psi_omega` at a
  zero with `Re ρ > Θ − ε`.
* `limsup_expo`: the two halves, as a limit superior of `log|ψ(x) − x| / log x` (`expo`).
-/
import HalfPlaneFinal
import PsiOmega

open Asymptotics Filter Topology
open scoped Chebyshev

namespace PsiExponent

open Pilot1bt

/-- The real parts of the nontrivial zeros of `ζ`. -/
def zeroReals : Set ℝ := {σ | ∃ ρ : ℂ, IsNontrivialZero ρ ∧ ρ.re = σ}

/-- `Θ`, the supremum of the real parts of the nontrivial zeros of `ζ`. -/
noncomputable def Theta : ℝ := sSup zeroReals

theorem re_le_eleven_twelfths {ρ : ℂ} (hρ : IsNontrivialZero ρ) : ρ.re ≤ 11 / 12 := by
  by_contra h
  exact (Eis.ne_zero_of_re_gt_eleven_twelfths (not_le.1 h)).1 hρ.1

theorem re_trivial_neg (n : ℕ) : (-2 * ((n : ℂ) + 1)).re < 0 := by
  simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
    Complex.neg_im, Complex.add_im, Complex.natCast_im, Complex.one_im]
  norm_num
  positivity

theorem exists_nontrivialZero_re_ge_half : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 1 / 2 ≤ ρ.re := by
  obtain ⟨ρ, hρ, hre⟩ := PsiOmega.exists_zero_re_ge_half
  refine ⟨ρ, ⟨hρ, ?_⟩, hre⟩
  rintro ⟨n, rfl⟩
  linarith [re_trivial_neg n]

theorem zeroReals_bddAbove : BddAbove zeroReals :=
  ⟨11 / 12, fun _ ⟨_, hρ, h⟩ => h ▸ re_le_eleven_twelfths hρ⟩

theorem zeroReals_nonempty : zeroReals.Nonempty := by
  obtain ⟨ρ, hρ, _⟩ := exists_nontrivialZero_re_ge_half
  exact ⟨ρ.re, ρ, hρ, rfl⟩

theorem re_le_Theta {ρ : ℂ} (hρ : IsNontrivialZero ρ) : ρ.re ≤ Theta :=
  le_csSup zeroReals_bddAbove ⟨ρ, hρ, rfl⟩

/-- **`Θ ≤ 11/12`**, from round 466's half-plane. -/
theorem Theta_le : Theta ≤ 11 / 12 :=
  csSup_le zeroReals_nonempty fun _ ⟨_, hρ, h⟩ => h ▸ re_le_eleven_twelfths hρ

/-- **`½ ≤ Θ`**, from round 220's zero with `Re ρ ≥ ½`. -/
theorem half_le_Theta : 1 / 2 ≤ Theta := by
  obtain ⟨ρ, hρ, hre⟩ := exists_nontrivialZero_re_ge_half
  exact hre.trans (re_le_Theta hρ)

/-- `ζ(s) ≠ 0` for `Re s > Θ`. -/
theorem zeta_ne_zero_of_Theta_lt {s : ℂ} (hs : Theta < s.re) : riemannZeta s ≠ 0 := by
  intro h0
  by_cases ht : ∃ n : ℕ, s = -2 * (n + 1)
  · obtain ⟨n, rfl⟩ := ht
    linarith [re_trivial_neg n, half_le_Theta]
  · exact absurd (re_le_Theta ⟨h0, ht⟩) (not_le.2 hs)

/-- Some nontrivial zero has real part above `Θ − ε`. -/
theorem exists_zero_re_gt {ε : ℝ} (hε : 0 < ε) : ∃ ρ : ℂ, IsNontrivialZero ρ ∧ Theta - ε < ρ.re := by
  obtain ⟨_, ⟨ρ, hρ, rfl⟩, h⟩ :=
    exists_lt_of_lt_csSup zeroReals_nonempty (by linarith : Theta - ε < Theta)
  exact ⟨ρ, hρ, h⟩

/-- **The upper half**: `ψ(x) − x = O(x^{Θ+ε})` (round 338's `psi_isBigO_of_zeroFree` at `Θ`). -/
theorem psi_isBigO_Theta {ε : ℝ} (hε : 0 < ε) :
    (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ (Theta + ε) :=
  HalfPlanePNT.psi_isBigO_of_zeroFree (by linarith [Theta_le]) (fun _ hs ↦ zeta_ne_zero_of_Theta_lt hs) hε

/-- **The lower half**: `ψ(x) − x = Ω±(x^{Θ−ε})` (round 220's `PsiOmega.psi_omega`). -/
theorem psi_omega_Theta {ε : ℝ} (hε : 0 < ε) (hεΘ : ε < Theta) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ (Theta - ε) < ψ x - x) ∧
      (∃ x, X < x ∧ ψ x - x < -(c * x ^ (Theta - ε))) := by
  obtain ⟨ρ, hρ, hre⟩ := exists_zero_re_gt hε
  exact PsiOmega.psi_omega hρ.1 (by linarith) hre c X

/-- The exponent of the error at `x`: `log|ψ(x) − x| / log x`. -/
noncomputable def expo (x : ℝ) : ℝ := Real.log |ψ x - x| / Real.log x

theorem eventually_expo_le {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x in atTop, expo x ≤ Theta + 2 * ε := by
  obtain ⟨C, hC⟩ := (psi_isBigO_Theta hε).bound
  have hlog : ∀ᶠ x in atTop, Real.log (max C 1) ≤ ε * Real.log x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (max C 1) / ε)] with x hx
    rw [div_le_iff₀ hε] at hx
    linarith
  filter_upwards [hC, hlog, eventually_gt_atTop 1] with x hx hl h1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos h1
  have hxp : 0 < x ^ (Theta + ε) := Real.rpow_pos_of_pos hx0 _
  simp only [Pi.sub_apply, id, Real.norm_eq_abs, abs_of_pos hxp] at hx
  unfold expo
  rw [div_le_iff₀ hlx]
  rcases eq_or_lt_of_le (abs_nonneg (ψ x - x)) with h | h
  · rw [← h, Real.log_zero]
    exact mul_nonneg (by linarith [half_le_Theta]) hlx.le
  · have hC1 : |ψ x - x| ≤ max C 1 * x ^ (Theta + ε) :=
      hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxp.le)
    calc Real.log |ψ x - x| ≤ Real.log (max C 1 * x ^ (Theta + ε)) := Real.log_le_log h hC1
      _ = Real.log (max C 1) + (Theta + ε) * Real.log x := by
        rw [Real.log_mul (by positivity) hxp.ne', Real.log_rpow hx0]
      _ ≤ (Theta + 2 * ε) * Real.log x := by
        have e : (Theta + 2 * ε) * Real.log x = (Theta + ε) * Real.log x + ε * Real.log x := by ring
        rw [e]
        linarith

theorem frequently_le_expo {ε : ℝ} (hε : 0 < ε) (hεΘ : ε < Theta) :
    ∃ᶠ x in atTop, Theta - ε ≤ expo x := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨x, hx, hlt⟩ := (psi_omega_Theta hε hεΘ 1 (max a 1)).1
  refine ⟨x, (le_max_left _ _).trans hx.le, ?_⟩
  have h1 : 1 < x := (le_max_right _ _).trans_lt hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos h1
  rw [one_mul] at hlt
  have hpos : 0 < x ^ (Theta - ε) := Real.rpow_pos_of_pos hx0 _
  have habs : x ^ (Theta - ε) ≤ |ψ x - x| := hlt.le.trans (le_abs_self _)
  unfold expo
  rw [le_div_iff₀ hlx, ← Real.log_rpow hx0]
  exact Real.log_le_log hpos habs

/-- **The exponent of the error in the prime number theorem is `Θ`**:
`limsup_{x→∞} log|ψ(x) − x| / log x = Θ`. -/
theorem limsup_expo : limsup expo atTop = Theta := by
  have hΘ := half_le_Theta
  have hb : IsBoundedUnder (· ≤ ·) atTop expo := isBoundedUnder_of_eventually_le (eventually_expo_le one_pos)
  have hcb : IsCoboundedUnder (· ≤ ·) atTop expo :=
    IsCoboundedUnder.of_frequently_ge (frequently_le_expo (ε := Theta / 2) (by linarith) (by linarith))
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact limsup_le_of_le hcb ((eventually_expo_le (half_pos hε)).mono fun x hx => by linarith)
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hm : 0 < min ε (Theta / 2) := lt_min hε (by linarith)
    have hm' : min ε (Theta / 2) < Theta := by linarith [min_le_right ε (Theta / 2)]
    have h := le_limsup_of_frequently_le (frequently_le_expo hm hm') hb
    linarith [min_le_left ε (Theta / 2)]

end PsiExponent

#print axioms PsiExponent.Theta_le
#print axioms PsiExponent.half_le_Theta
#print axioms PsiExponent.zeta_ne_zero_of_Theta_lt
#print axioms PsiExponent.psi_isBigO_Theta
#print axioms PsiExponent.psi_omega_Theta
#print axioms PsiExponent.limsup_expo
