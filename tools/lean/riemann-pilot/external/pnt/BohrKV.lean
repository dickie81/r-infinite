import LandauKV
import BohrJoins

/-! # The Korobov–Vinogradov region as a shell around the Bohr sphere (round 399)

Round 398's `BohrJoins.shell_of_zeroFree` turns a zero-free half-plane into a shell around round 391's sphere. The
Korobov–Vinogradov region of round 215 (`LandauKV.zeroFree_KV`) is not a half-plane: its width shrinks with the
height. This file states it as a shell at each height (**`shell_of_KV`**): a nontrivial zero `ρ` with `|Im ρ| ≥ e³`
has its Bohr vector strictly between the radii at `1 − δ` and `δ`, where
`δ = A/((log|Im ρ|)^{2/3}(log log|Im ρ|)^{1/3})`. The bound `Re ρ > δ` comes from the reflection `ρ ↦ 1 − ρ`
(`PsiOmega.IsNontrivialZero.one_sub`). Since `δ → 0` as `|Im ρ| → ∞`, these shells approach the unconditional one
(`BohrJoins.shell_unconditional`); that limit is not stated as a theorem.
-/

open Complex BohrSphere

namespace BohrKV

/-- **The Korobov–Vinogradov region is a shell at each height.** -/
theorem shell_of_KV : ∃ A : ℝ, 0 < A ∧ ∀ F : Finset Nat.Primes, F.Nonempty → ∀ ρ : ℂ,
    Pilot1bt.IsNontrivialZero ρ → Real.exp 3 ≤ |ρ.im| →
      ‖vF F ((1 - A / (Real.log |ρ.im| ^ ((2 : ℝ) / 3) * Real.log (Real.log |ρ.im|) ^ ((1 : ℝ) / 3)) : ℝ) : ℂ)‖
          < ‖vF F ρ‖ ∧
        ‖vF F ρ‖ <
          ‖vF F ((A / (Real.log |ρ.im| ^ ((2 : ℝ) / 3) * Real.log (Real.log |ρ.im|) ^ ((1 : ℝ) / 3)) : ℝ) : ℂ)‖ := by
  obtain ⟨A, hA, hzf⟩ := LandauKV.zeroFree_KV
  refine ⟨A, hA, fun F hF ρ hρ ht => ?_⟩
  set δ := A / (Real.log |ρ.im| ^ ((2 : ℝ) / 3) * Real.log (Real.log |ρ.im|) ^ ((1 : ℝ) / 3)) with hδ
  have h1 : ρ.re < 1 - δ := by
    by_contra h
    exact hzf ρ.re ρ.im ht (not_lt.1 h) (by rw [Complex.re_add_im]; exact hρ.1)
  have h2 : δ < ρ.re := by
    have hρ' := PsiOmega.IsNontrivialZero.one_sub hρ
    have him : |(1 - ρ).im| = |ρ.im| := by simp [abs_neg]
    by_contra h
    refine hzf (1 - ρ).re (1 - ρ).im (him ▸ ht) ?_ (by rw [Complex.re_add_im]; exact hρ'.1)
    rw [him, Complex.sub_re, Complex.one_re]
    linarith [not_lt.1 h]
  exact ⟨norm_vF_lt_norm_vF hF (by simpa using h1), norm_vF_lt_norm_vF hF (by simpa using h2)⟩

end BohrKV

#print axioms BohrKV.shell_of_KV
