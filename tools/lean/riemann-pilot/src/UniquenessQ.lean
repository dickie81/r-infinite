import Mathlib
import StrictPositivity

/-! # Uniqueness for the full form `Q`: what the structure forces

Perron–Frobenius does not apply to `Q = Q₀ + 2⟨g, w⟩²`: the pole term grows under `g ↦ |g|`. The
`Q₀` results still pin down how uniqueness can fail.

1. **Strict gap.** `λ₀ < λ₁`. If `λ₀ = λ₁`, a ground state of `Q` has `⟨g, w⟩ = 0` and is a ground
   state of `Q₀`, hence `±φ₀`. But `⟨φ₀, w⟩ > 0`, because `φ₀ > 0` a.e. on `[−a, a]` and `w > 0` there.
2. **Euler–Lagrange off the pole.** A ground state `v` of `Q` with `⟨v, w⟩ = 0` satisfies `Q₀`'s
   weak eigen-equation at level `λ₁`: `B(v, ψ) = λ₁⟨v, ψ⟩` for every probe `ψ`.
3. **Orthogonality.** `B` is symmetric, so `(λ₁ − λ₀)⟨v, φ₀⟩ = 0` and `v ⊥ φ₀`.

Result: `Q`'s ground state is unique up to sign, *or* `Q₀` has an excited eigenvalue exactly equal
to `λ₁`, attained by a normalised `v` with `v ⊥ w` and `v ⊥ φ₀`. The dichotomy is sharp: nothing in
the structure of `Q` excludes the second branch, so uniqueness for `Q` is not proved.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

theorem xcorr_comm (φ ψ : ℝ → ℝ) (u : ℝ) : xcorr φ ψ u = xcorr ψ φ u := by unfold xcorr; ring

/-- The bilinear form of `Q₀` is symmetric. -/
theorem bil0_comm (a : ℝ) (φ ψ : ℝ → ℝ) : bil0 a φ ψ = bil0 a ψ φ := by
  unfold bil0 primeX archX; simp only [xcorr_comm φ ψ]

theorem weilQ0_le (a : ℝ) (g : ℝ → ℝ) : weilQ0 a g ≤ weilQ a g := by
  unfold weilQ0; nlinarith [sq_nonneg (poleR g a)]

theorem lam0_le_lam {a : ℝ} (ha : 0 < a) : lam0 a ≤ lam a := by
  refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
  rintro q ⟨h, hp, hn, rfl⟩
  exact (lam0_le hp hn).trans (weilQ0_le a h)

/-- **`ĝ(i/2) = ⟨φ, w⟩ > 0`** for `φ ≥ 0` with `φ > 0` a.e. on `[−a, a]`. -/
theorem poleR_pos {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hp : Probe a φ) (h0 : ∀ t, 0 ≤ φ t)
    (hpos : ∀ᵐ t, |t| ≤ a → 0 < φ t) : 0 < poleR φ a := by
  unfold poleR
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun t => mul_nonneg (h0 t) (Real.exp_pos _).le)
    (poleR_integrable hp.memL2 a)]
  refine ⟨by linarith, ?_⟩
  have hsub : Ioc (-a) a ≤ᵐ[volume]
      (Function.support (fun u => φ u * Real.exp (-(u / 2))) ∩ Ioc (-a) a) := by
    filter_upwards [hpos] with t ht hs
    refine ⟨?_, hs⟩
    have : 0 < φ t := ht (abs_le.2 ⟨hs.1.le, hs.2⟩)
    exact (mul_pos this (Real.exp_pos _)).ne'
  calc (0 : ENNReal) < volume (Ioc (-a) a) := by
        rw [Real.volume_Ioc]; exact ENNReal.ofReal_pos.2 (by linarith)
    _ ≤ _ := measure_mono_ae hsub

/-- **Strict gap `λ₀ < λ₁`.** -/
theorem lam0_lt_lam {a : ℝ} (ha : 0 < a) : lam0 a < lam a := by
  obtain ⟨φ, hφ, h0, hpos, huniq⟩ := exists_positive_groundState0 ha
  obtain ⟨g, hg⟩ := exists_groundState ha
  refine lt_of_le_of_ne (lam0_le_lam ha) fun heq => ?_
  have hq : weilQ a g = lam a := by
    have := ((isGroundState_iff ha).1 hg).1.2; rw [this, hg.2.1, mul_one]
  have hl0 := lam0_le hg.1 hg.2.1
  unfold weilQ0 at hl0
  have hsq : poleR g a ^ 2 ≤ 0 := by linarith
  have hp0 : poleR g a = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hsq (sq_nonneg _))
  have hg0 : IsGroundState0 a g := by
    refine ⟨hg.1, hg.2.1, fun h hph hnh => ?_⟩
    have := lam0_le hph hnh
    unfold weilQ0 at this ⊢
    rw [hp0]; linarith
  have hφp := poleR_pos ha hφ.1 h0 hpos
  rcases huniq g hg0 with h | h
  · rw [poleR_congr_ae h] at hp0; linarith
  · rw [poleR_congr_ae h, show (fun t => -φ t) = fun t => (-1) * φ t by funext t; ring,
      poleR_smul] at hp0
    linarith

/-- Euler–Lagrange for any ground-space element. -/
theorem euler_lagrange_mem {a : ℝ} {w ψ : ℝ → ℝ} (hw : w ∈ groundSpace a) (hψ : Probe a ψ) :
    bil0 a w ψ + 2 * poleR w a * poleR ψ a = lam a * xcorr w ψ 0 := by
  have hq : weilQ a w = lam a * normSq w := hw.2
  have hpole : ∀ s : ℝ, poleR (fun t => w t + s * ψ t) a = poleR w a + s * poleR ψ a := by
    intro s
    rw [poleR_add hw.1.memL2 (hψ.memL2.const_mul s) a, poleR_smul]
  apply sub_eq_zero.1
  refine quad_zero (c := weilQ0 a ψ + 2 * poleR ψ a ^ 2 - lam a * normSq ψ) fun s => ?_
  have h := lam_mul_le (probe_add_smul hw.1 hψ s)
  have hQ : ∀ f, weilQ a f = weilQ0 a f + 2 * poleR f a ^ 2 := fun f => by unfold weilQ0; ring
  rw [hQ, weilQ0_add_smul hw.1 hψ, hpole, normSq_add_smul hw.1.memL2 hψ.memL2] at h
  rw [hQ] at hq
  nlinarith [h]

/-- **Euler–Lagrange off the pole**: a ground state `v` of `Q` with `ĝ(i/2) = 0` satisfies `Q₀`'s
weak eigen-equation at level `λ₁`. -/
theorem euler_lagrange_perp {a : ℝ} (ha : 0 < a) {v ψ : ℝ → ℝ} (hv : IsGroundState a v)
    (hv0 : poleR v a = 0) (hψ : Probe a ψ) : bil0 a v ψ = lam a * xcorr v ψ 0 := by
  simpa [hv0] using euler_lagrange_mem ⟨hv.1, ((isGroundState_iff ha).1 hv).1.2⟩ hψ

/-- **Orthogonality**: such a `v` is orthogonal to the ground state of `Q₀`. -/
theorem perp_groundState0 {a : ℝ} (ha : 0 < a) {φ v : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hv : IsGroundState a v) (hv0 : poleR v a = 0) : (∫ t, v t * φ t) = 0 := by
  have e1 := euler_lagrange_perp ha hv hv0 hφ.1
  have e2 := euler_lagrange0 ha hφ hv.1
  rw [bil0_comm, xcorr_comm] at e2
  have hlt := lam0_lt_lam ha
  have : (lam a - lam0 a) * xcorr v φ 0 = 0 := by linear_combination e2 - e1
  rw [← xcorr_zero_eq]
  exact (mul_eq_zero.1 this).resolve_left (by linarith)

/-- **The uniqueness dichotomy for `Q`.** `λ₀ < λ₁`; `Q₀` has a ground state `φ₀ > 0` a.e. on
`[−a, a]` with `ĝ(i/2) > 0`; and either the ground state of `Q` is unique up to sign, or there is a
ground state `v` of `Q` with `v ⊥ w`, `v ⊥ φ₀`, `Q₀(v) = λ₁`, solving `Q₀`'s weak eigen-equation at
level `λ₁`, i.e. an excited state of `Q₀` at exactly the energy `λ₁`. -/
theorem groundState_unique_or_excited {a : ℝ} (ha : 0 < a) :
    lam0 a < lam a ∧ ∃ φ, IsGroundState0 a φ ∧ (∀ t, 0 ≤ φ t) ∧ (∀ᵐ t, |t| ≤ a → 0 < φ t) ∧
      0 < poleR φ a ∧
      ((∀ g h, IsGroundState a g → IsGroundState a h →
          g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t) ∨
        ∃ v, IsGroundState a v ∧ poleR v a = 0 ∧ (∫ t, v t * φ t) = 0 ∧ weilQ0 a v = lam a ∧
          ∀ ψ, Probe a ψ → bil0 a v ψ = lam a * xcorr v ψ 0) := by
  obtain ⟨φ, hφ, h0, hpos, -⟩ := exists_positive_groundState0 ha
  refine ⟨lam0_lt_lam ha, φ, hφ, h0, hpos, poleR_pos ha hφ.1 h0 hpos, ?_⟩
  by_cases hw : ∀ v, IsGroundState a v → poleR v a ≠ 0
  · exact Or.inl fun g h hg hh => groundState_unique ha hw hg hh
  · right
    simp only [not_forall, not_not] at hw
    obtain ⟨v, hv, hv0⟩ := hw
    refine ⟨v, hv, hv0, perp_groundState0 ha hφ hv hv0, ?_,
      fun ψ hψ => euler_lagrange_perp ha hv hv0 hψ⟩
    have hq := ((isGroundState_iff ha).1 hv).1.2
    unfold weilQ0; rw [hv0, hq, hv.2.1]; ring

end Pilot1ca

#print axioms Pilot1ca.bil0_comm
#print axioms Pilot1ca.lam0_le_lam
#print axioms Pilot1ca.poleR_pos
#print axioms Pilot1ca.lam0_lt_lam
#print axioms Pilot1ca.euler_lagrange_perp
#print axioms Pilot1ca.perp_groundState0
#print axioms Pilot1ca.groundState_unique_or_excited
