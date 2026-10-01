import Mathlib
import WeilConverse

/-! # Riemann's kernel is a null vector of the explicit formula (round 132)

Weil's explicit formula (`WeilExplicit`) equates the zero sum `Σ_ρ h(t_ρ)` with its prime side
`weilRHS h hR` (pole terms, archimedean integral, prime sum). At every nontrivial zero of `ζ`,
`Ξ(t_ρ) = ξ(ρ) = 0` (`Xi_zeta_zero`). So every test transform divisible by `Ξ` is annihilated:

* `explicit_null_of_Xi`: `h = Ξ·m` ⟹ `weilRHS h hR = 0`;
* `explicit_null_RPhi`: Riemann's formula `Φ̂ = Ξ/2` (`RPhiHat_eq`, RiemannKernel.lean) makes
  `Φ̂·m` null for every `m`: **`Φ` is a null vector of the bilinear Weil functional**;
* `weil_energy_RPhi`: for `h = Φ̂²` the pole terms are `Ξ(±i/2)²/4 = ξ(0)²/4 = ξ(1)²/4 = 1/16`, so the
  archimedean-plus-prime side of `Φ̂²` equals exactly `−1/8`: Weil's energy of `Φ` is `0`.

`bil_zero_sum` is the polarised bridge for probes: `Σ_ρ ĝ(t_ρ)k̂(t_ρ) = (Q(g + k) − Q(g − k))/4`.

**Not formalised**: identifying the explicit formula's `g_h` for `h = Φ̂k̂` with the pilot's
cross-correlation `∫Φ(t)k(t + u) dt` (Fourier inversion and a signed Fubini for a non-compactly
supported `Φ`), which would state the nullity as `B(Φ, k) = 0` in the pilot's own prime-side form.
Scope: a restatement of the explicit formula at a function vanishing on the zeros; no bearing on RH.
-/

open Real Complex

noncomputable section

namespace Pilot1ca

open Pilot1bt

/-- `Ξ` vanishes at the ordinate of every nontrivial zero of `ζ`. -/
theorem Xi_zeta_zero (p : Σ z : NontrivialZero, Fin (zeroMult z)) :
    Xi ((zetaZeroFamily p - 1 / 2) / I) = 0 := by
  rw [Xi_at_ordinate]; exact xi_eq_zero_of_nontrivial p.1.2

/-- **Test transforms divisible by `Ξ` are null**: if every member of the family is a zero of `Ξ`
(in the ordinate variable) and the explicit formula holds for `h = Ξ·m`, its prime side vanishes. -/
theorem explicit_null_of_Xi {ι : Type*} {ρ : ι → ℂ} (hz : ∀ i, Xi ((ρ i - 1 / 2) / I) = 0)
    {m : ℂ → ℂ} {hR : ℝ → ℝ} (hE : WeilExplicit ρ (fun z => Xi z * m z) hR) :
    weilRHS (fun z => Xi z * m z) hR = 0 := by
  have h : HasSum (fun i => Xi ((ρ i - 1 / 2) / I) * m ((ρ i - 1 / 2) / I))
      (weilRHS (fun z => Xi z * m z) hR) := hE.2
  simp only [hz, zero_mul] at h
  exact h.unique hasSum_zero

/-- **`Φ` is a null vector of the explicit formula**: for every `m`, the prime side of `Φ̂·m` vanishes
(over the zeros of `ζ`, given the explicit formula for this `h`). -/
theorem explicit_null_RPhi {m : ℂ → ℂ} {hR : ℝ → ℝ}
    (hE : WeilExplicit zetaZeroFamily (fun z => RPhiHat z * m z) hR) :
    weilRHS (fun z => RPhiHat z * m z) hR = 0 := by
  have e : (fun z => RPhiHat z * m z) = fun z => Xi z * (m z / 2) := by
    funext z; rw [RPhiHat_eq]; ring
  rw [e] at hE ⊢
  exact explicit_null_of_Xi Xi_zeta_zero hE

theorem xi_zero : xi 0 = 1 / 2 := by simp [xi]
theorem xi_one : xi 1 = 1 / 2 := by simp [xi]

theorem RPhiHat_I_half : RPhiHat (I / 2) = 1 / 4 := by
  rw [RPhiHat_eq, Xi, show (1 : ℂ) / 2 + I * (I / 2) = 0 by
    have := I_mul_I; linear_combination this / 2, xi_zero]; norm_num

theorem RPhiHat_neg_I_half : RPhiHat (-(I / 2)) = 1 / 4 := by
  rw [RPhiHat_eq, Xi, show (1 : ℂ) / 2 + I * -(I / 2) = 1 by
    have := I_mul_I; linear_combination -this / 2, xi_one]; norm_num

/-- **Weil's energy of `Φ` is zero, explicitly**: for `h = Φ̂²` the pole terms are `1/16` each, so the
archimedean-plus-prime side is exactly `−1/8`. -/
theorem weil_energy_RPhi {hR : ℝ → ℝ}
    (hE : WeilExplicit zetaZeroFamily (fun z => RPhiHat z ^ 2) hR) :
    -(gh hR 0 * Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe r)
      - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n) = -1 / 8 := by
  have e : (fun z => RPhiHat z ^ 2) = fun z => RPhiHat z * RPhiHat z := by funext z; ring
  rw [e] at hE
  have h0 := explicit_null_RPhi hE
  unfold weilRHS at h0
  beta_reduce at h0
  rw [RPhiHat_I_half, RPhiHat_neg_I_half] at h0
  generalize (-(gh hR 0 * Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe r)
    - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n)) = X at h0 ⊢
  have := congrArg Complex.re h0
  norm_num at this
  linarith

/-! ## The polarised bridge -/

variable {a : ℝ} {g k : ℝ → ℝ}

theorem ghatC_sub' (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume) (hk : MeasureTheory.MemLp k 2 MeasureTheory.volume)
    (z : ℂ) : ghatC (fun t => g t - k t) a z = ghatC g a z - ghatC k a z := by
  unfold ghatC
  rw [← intervalIntegral.integral_sub (ii_mul_exp hg z _ _) (ii_mul_exp hk z _ _)]
  congr 1; funext u; push_cast; ring

/-- **The bilinear Weil form is the bilinear zero sum**: `Σ_ρ ĝ(t_ρ)k̂(t_ρ) = (Q(g + k) − Q(g − k))/4`. -/
theorem bil_zero_sum {ι : Type*} {ρ : ι → ℂ} (hg : Probe a g) (hk : Probe a k) (ha : 0 < a)
    (hEp : WeilExplicit ρ (fun z => ghatC (fun t => g t + k t) a z ^ 2) (hsq (fun t => g t + k t) a))
    (hEm : WeilExplicit ρ (fun z => ghatC (fun t => g t - k t) a z ^ 2) (hsq (fun t => g t - k t) a)) :
    HasSum (fun i => ghatC g a ((ρ i - 1 / 2) / I) * ghatC k a ((ρ i - 1 / 2) / I))
      (((weilQ a (fun t => g t + k t) - weilQ a (fun t => g t - k t)) / 4 : ℝ) : ℂ) := by
  obtain ⟨hpp, hpm⟩ := probe_add_sub hg hk
  have hp := weilQ_eq_zero_sum hpp ha hEp
  have hm := weilQ_eq_zero_sum hpm ha hEm
  have h := (hp.sub hm).div_const 4
  convert h using 1
  · funext i
    rw [show (fun t => g t + k t) = g + k from rfl, ghatC_add hg.memL2 hk.memL2,
      ghatC_sub' hg.memL2 hk.memL2]
    ring
  · push_cast; ring

end Pilot1ca

#print axioms Pilot1ca.Xi_zeta_zero
#print axioms Pilot1ca.explicit_null_of_Xi
#print axioms Pilot1ca.explicit_null_RPhi
#print axioms Pilot1ca.weil_energy_RPhi
#print axioms Pilot1ca.bil_zero_sum
