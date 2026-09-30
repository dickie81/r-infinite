import SlogZeta

/-! # Bounded gaps between the ordinates of the zeros of `ζ` (round 248)

From zeta23's `S(T) = O(log T)` and the growth of the main term `N₀`: there is `H` such that every window `[t, t + H)` with `t ≥ T₀` contains a zero ordinate.
-/

open Real MeasureTheory Set

namespace ZeroWindow

open Pilot1ca Pilot1bt SlogZeta

/-- `N₀(b) − N₀(a) ≥ (b − a)·log(a/2π)/(2π)` for `2π ≤ a ≤ b` (the mirror of `SlogZeta.N0_sub_le`). -/
theorem N0_sub_ge {a b : ℝ} (ha : 2 * π ≤ a) (hab : a ≤ b) :
    (b - a) * (1 / (2 * π) * Real.log (a / (2 * π))) ≤ N0 b - N0 a := by
  have hπ : 0 < 2 * π := by positivity
  have ha0 : 0 < a := by linarith
  rw [N0_sub_eq ha0 hab]
  have hmono : ∫ _ in a..b, (1 / (2 * π) * Real.log (a / (2 * π))) ≤
      ∫ τ in a..b, 1 / (2 * π) * Real.log (τ / (2 * π)) := by
    refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
      ((continuousOn_L ha0 hab).intervalIntegrable) fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right hx.1 hπ.le)) (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  exact hmono

/-- **Bounded gaps between the zeros of `ζ`**: there is `H` such that every window `[t, t + H)` with
`t ≥ T₀` contains the ordinate of a nontrivial zero. From `S(T) = O(log T)` (zeta23 layer) and the
growth of `N₀` (pilot). -/
theorem zero_in_window : ∃ H T₀ : ℝ, 0 < H ∧ ∀ t : ℝ, T₀ ≤ t →
    ∃ p : PosZeroIdx, t ≤ zetaOrd p ∧ zetaOrd p < t + H := by
  obtain ⟨C, hC, hS⟩ := Slog_zeta
  have hπ : 0 < π := Real.pi_pos
  refine ⟨16 * π * C + 1, 16 * π * C + 64, by positivity, fun t ht => ?_⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = 16 * π * C + 1 := ⟨_, rfl⟩
  rw [← hH]
  have hH0 : 0 < H := by rw [hH]; positivity
  have ht64 : 64 ≤ t := by nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hπ.le) hC]
  have htH : t + H ≤ 2 * t := by rw [hH] at *; linarith
  by_contra hno
  push Not at hno
  -- no zero in the window: the count does not grow
  have hN : Ncnt zetaOrd (t + H) ≤ Ncnt zetaOrd t := by
    unfold Ncnt
    exact_mod_cast Set.ncard_le_ncard (fun p (hp : zetaOrd p < t + H) => show zetaOrd p < t by
      by_contra h; push Not at h; linarith [hno p h]) (zetaOrd_finite t)
  have h1 := hS t (by linarith)
  have h2 := hS (t + H) (by linarith)
  unfold Sz at h1 h2
  have hpi4 : π < 4 := by linarith [Real.pi_lt_d2]
  have h2π : 2 * π ≤ t := by linarith
  have h3 := N0_sub_ge h2π (by linarith : t ≤ t + H)
  -- the logarithms
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hsq : 2 * π ≤ Real.sqrt t := by
    rw [Real.le_sqrt (by positivity) (by linarith)]
    nlinarith [Real.pi_lt_d2]
  have hsqt : Real.sqrt t ≤ t / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have := Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ t)
    nlinarith [Real.sqrt_nonneg t]
  have hlog1 : Real.log t / 2 ≤ Real.log (t / (2 * π)) := by
    rw [← Real.log_sqrt (by linarith)]
    exact Real.log_le_log (Real.sqrt_pos.2 (by linarith)) hsqt
  have hlog2 : Real.log (t + H) ≤ 2 * Real.log t := by
    have : t + H ≤ t ^ 2 := by nlinarith
    calc Real.log (t + H) ≤ Real.log (t ^ 2) := Real.log_le_log (by linarith) this
      _ = 2 * Real.log t := by rw [Real.log_pow]; push_cast; ring
  have hA : H * (1 / (2 * π) * (Real.log t / 2)) ≤ H * (1 / (2 * π) * Real.log (t / (2 * π))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog1 (by positivity)) hH0.le
  have hB : C * Real.log (t + H) ≤ C * (2 * Real.log t) := mul_le_mul_of_nonneg_left hlog2 hC
  have e : H * (1 / (2 * π) * (Real.log t / 2)) = 4 * (C * Real.log t) + Real.log t / (4 * π) := by
    rw [hH]; field_simp; ring
  have hpos : 0 < Real.log t / (4 * π) := by positivity
  rw [abs_le] at h1 h2
  nlinarith [h1.1, h1.2, h2.1, h2.2]

end ZeroWindow

#print axioms ZeroWindow.N0_sub_ge
#print axioms ZeroWindow.zero_in_window
