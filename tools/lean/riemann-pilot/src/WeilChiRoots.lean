import WeilChiDensity
import ArchShift
import HurwitzCross
import ParabolaGap

/-! # The root locus of `Ξ_χ` and the `hS` blind spot (round 246)

`GRH' χ` (GRH off the real axis) is `τ_i ∈ ℝ ∪ iℝ` for every zero index, i.e. every root `u_i = τ_i²` real; `hS` is `no root with u ≤ 0`; GRH is `every root real and positive` (`grh_iff_roots_pos`). Duplication of the archimedean kernel (`archKer q + archKer (q + ½) = archKer (2q)(u/2)`) and ground-state uniqueness restated below `log 2`.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace ChiRoots

open PsiOmega DirichletCharacter Pilot1ca Pilot1bt PilotWeil

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

def GRH' (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.im ≠ 0 → s.re = 1 / 2

theorem sq_re' (τ : ℂ) : (τ ^ 2).re = τ.re ^ 2 - τ.im ^ 2 := by rw [pow_two, mul_re]; ring

theorem sq_im' (τ : ℂ) : (τ ^ 2).im = 2 * τ.re * τ.im := by rw [pow_two, mul_im]; ring

/-- `τ` is on the cross `ℝ ∪ iℝ` iff `τ²` is real. -/
theorem mem_crossSet_iff (τ : ℂ) : τ ∈ crossSet ↔ (τ ^ 2).im = 0 := by
  rw [sq_im']
  show τ.re = 0 ∨ τ.im = 0 ↔ _
  constructor
  · rintro (h | h) <;> simp [h]
  · intro h
    have : τ.re * τ.im = 0 := by linarith
    exact mul_eq_zero.1 this

theorem re_half_add (t : ℂ) : (1 / 2 + I * t).re = 1 / 2 - t.im := by simp; ring

theorem im_half_add (t : ℂ) : (1 / 2 + I * t).im = t.re := by simp

theorem half_add_I_tau {s : ℂ} {t : ℂ} (hi : t = (s - 1 / 2) / I ∨ t = -((s - 1 / 2) / I)) :
    1 / 2 + I * t = s ∨ 1 / 2 + I * t = 1 - s := by
  rcases hi with hi | hi
  · left; rw [hi]; field_simp; ring
  · right; rw [hi]; field_simp; ring

/-- **`GRH'` ⟺ every `τ` lies on the cross.** -/
theorem grh'_iff_cross (hG : GoodChar χ) : GRH' χ ↔ ∀ i : ZeroIdx (sqF (XiC χ)), tauC i ∈ crossSet := by
  constructor
  · intro h' i
    show (tauC i).re = 0 ∨ (tauC i).im = 0
    obtain ⟨hz, h0, h1⟩ := zero_of_tau hG i
    by_cases hr : (tauC i).re = 0
    · exact Or.inl hr
    · right
      have := h' _ hz h0 h1 (by rw [im_half_add]; exact hr)
      rw [re_half_add] at this; linarith
  · intro h s hs h0 h1 hne
    obtain ⟨i, hi⟩ := tau_of_zero hG hs h0
    have hc : (tauC i).re = 0 ∨ (tauC i).im = 0 := h i
    rcases half_add_I_tau hi with e | e
    · have hre : s.re = 1 / 2 - (tauC i).im := by rw [← e, re_half_add]
      have him : s.im = (tauC i).re := by rw [← e, im_half_add]
      rcases hc with hc | hc
      · exact absurd (him.trans hc) hne
      · rw [hre, hc]; ring
    · have hre : 1 - s.re = 1 / 2 - (tauC i).im := by
        rw [← re_half_add, e]; simp
      have him : -s.im = (tauC i).re := by
        rw [← im_half_add, e]; simp
      rcases hc with hc | hc
      · exact absurd (by linarith : s.im = 0) hne
      · linarith

/-- **`GRH'` ⟺ every zero `w` of `Ξ_χ(√w)` is real.** -/
theorem grh'_iff_roots_real (hG : GoodChar χ) :
    GRH' χ ↔ ∀ i : ZeroIdx (sqF (XiC χ)), (i.1).im = 0 := by
  rw [grh'_iff_cross hG]
  refine forall_congr' fun i => ?_
  rw [mem_crossSet_iff, tauC_sq]

/-- **`hS` ⟺ no zero `w ≤ 0`.** -/
theorem hS_iff_no_nonpos_root (hG : GoodChar χ) :
    (∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) ↔
      ∀ i : ZeroIdx (sqF (XiC χ)), ¬((i.1).im = 0 ∧ (i.1).re ≤ 0) := by
  constructor
  · rintro hS i ⟨him, hre⟩
    rw [← tauC_sq i, sq_im'] at him
    rw [← tauC_sq i, sq_re'] at hre
    have hr : (tauC i).re = 0 := by
      by_contra hne
      have hi0 : (tauC i).im = 0 := by
        have : (tauC i).re * (tauC i).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [hi0] at hre
      have : 0 < (tauC i).re ^ 2 := by positivity
      linarith
    obtain ⟨hz, h0, h1⟩ := zero_of_tau hG i
    have e : (1 / 2 + I * tauC i) = (((1 / 2 + I * tauC i).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by rw [im_half_add, hr]; simp)
    rw [e] at hz
    exact hS _ h0 h1 hz
  · intro h σ h0 h1 hz
    obtain ⟨i, hi⟩ := tau_of_zero hG hz (by simpa using h0)
    have hr : (tauC i).re = 0 := by
      rcases half_add_I_tau hi with e | e
      · rw [← im_half_add, e]; simp
      · have := congrArg Complex.im e
        rw [im_half_add] at this; rw [this]; simp
    refine h i ⟨?_, ?_⟩
    · rw [← tauC_sq i, sq_im', hr]; ring
    · rw [← tauC_sq i, sq_re', hr]; nlinarith [sq_nonneg (tauC i).im]

/-- **`GRH` ⟺ every zero `w` of `Ξ_χ(√w)` is real and positive.** -/
theorem grh_iff_roots_pos (hG : GoodChar χ) :
    GRH χ ↔ ∀ i : ZeroIdx (sqF (XiC χ)), (i.1).im = 0 ∧ 0 < (i.1).re := by
  constructor
  · intro hGRH i
    have hi := tau_real_of_GRH hG hGRH i
    have hne := ZeroIdxC_ne_zero hG i
    have him : (i.1).im = 0 := by rw [← tauC_sq i, sq_im', hi]; ring
    refine ⟨him, ?_⟩
    have hre : (i.1).re = (tauC i).re ^ 2 := by rw [← tauC_sq i, sq_re', hi]; ring
    rcases (sq_nonneg (tauC i).re).lt_or_eq with hlt | heq
    · rw [hre]; exact hlt
    · exact absurd (Complex.ext (by rw [hre, ← heq]; simp) (by rw [him]; simp)) hne
  · intro h s hs h0 h1
    obtain ⟨i, hi⟩ := tau_of_zero hG hs h0
    obtain ⟨him, hre⟩ := h i
    rw [← tauC_sq i, sq_im'] at him
    rw [← tauC_sq i, sq_re'] at hre
    have hi0 : (tauC i).im = 0 := by
      have hr : (tauC i).re ≠ 0 := by
        intro hr; rw [hr] at hre; nlinarith [sq_nonneg (tauC i).im]
      have : (tauC i).re * (tauC i).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hr
    rcases half_add_I_tau hi with e | e
    · rw [← e, re_half_add, hi0]; ring
    · have := congrArg Complex.re e
      rw [re_half_add, hi0] at this; simp at this; linarith

end ChiRoots

/-! ## (G) Legendre duplication for the archimedean kernel -/

namespace ArchKerDup

open Pilot1ca

theorem archKer_dup (q : ℝ) {u : ℝ} (hu : 0 < u) :
    archKer q u + archKer (q + 1 / 2) u = archKer (2 * q) (u / 2) := by
  unfold archKer
  have hs : Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    have := Real.sinh_two_mul (u / 2); rwa [show 2 * (u / 2) = u by ring] at this
  have h2 : 0 < Real.sinh (u / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  have e1 : Real.exp ((1 - 2 * q) * u)
      = Real.exp ((1 - 2 * (2 * q)) * (u / 2)) * Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 - 2 * (q + 1 / 2)) * u)
      = Real.exp ((1 - 2 * (2 * q)) * (u / 2)) * Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2, ← add_div, ← mul_add]
  have hcosh : Real.exp (u / 2) + Real.exp (-(u / 2)) = 2 * Real.cosh (u / 2) := by
    rw [Real.cosh_eq]; ring
  rw [hcosh, hs, div_eq_div_iff (mul_pos (mul_pos two_pos h2) hc).ne' h2.ne']
  ring

/-- The Dedekind `ζ_{ℚ(i)}` kernel: `K_{1/4} + K_{3/4} = K_{1/2}(·/2)`. -/
theorem archKer_quarter_dup {u : ℝ} (hu : 0 < u) :
    archKer (1 / 4) u + archKer (3 / 4) u = archKer (1 / 2) (u / 2) := by
  have h := archKer_dup (1 / 4) hu
  rw [show (1 / 4 : ℝ) + 1 / 2 = 3 / 4 by norm_num, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at h
  exact h

end ArchKerDup

/-! ## (H) nested uniqueness -/

namespace GroundUnique

open Pilot1ca

theorem groundState_unique_035' {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t :=
  groundState_unique_036 ha (by linarith) hg hh

theorem groundState_unique_below_log2' {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2)
    {g h : ℝ → ℝ} (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  have : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  exact groundState_unique_036 ha (by linarith) hg hh

end GroundUnique

#print axioms ChiRoots.mem_crossSet_iff
#print axioms ChiRoots.grh'_iff_cross
#print axioms ChiRoots.grh'_iff_roots_real
#print axioms ChiRoots.hS_iff_no_nonpos_root
#print axioms ChiRoots.grh_iff_roots_pos
#print axioms ArchKerDup.archKer_dup
#print axioms ArchKerDup.archKer_quarter_dup
#print axioms GroundUnique.groundState_unique_035'
#print axioms GroundUnique.groundState_unique_below_log2'
