import Mathlib
import PsiOmega

/-! # Prime races: Landau's oscillation theorem for Dirichlet L-functions (round 222)

The generic zero-free theorem (`PsiOmega.ne_zero_of_mellin`) applies to any entire `Z` with no zero on
`Re s ≥ 1` and no real zero above `θ`. For a nontrivial real Dirichlet character `χ`, take
`Z = L(·, χ)` (entire, `DirichletCharacter.differentiable_LFunction`; no zero on `Re s ≥ 1`,
`DirichletCharacter.LFunction_ne_zero_of_one_le_re`) and `ψ(x, χ) = Σ_{n ≤ x} Λ(n)χ(n)`, whose
L-series is `−L′/L(s, χ)` (`LSeries_twist_vonMangoldt_eq`).

* `LFunction_ne_zero_of_psiChi`: if `L(σ, χ) ≠ 0` for real `σ ∈ (θ, 1)`, a one-sided bound
  `εψ(x, χ) ≤ c·x^θ` makes `L(s, χ) ≠ 0` on `Re s > θ`.
* `psiChi_omega`: under the same real-zero hypothesis, any zero `ρ` of `L(s, χ)` with `Re ρ > θ` makes
  `ψ(x, χ) = Ω±(x^θ)`.
* `race_four`: for `χ₄`, `ψ(x, χ₄) = ψ(x; 4, 1) − ψ(x; 4, 3)`, so a zero of `L(s, χ₄)` with
  `Re ρ > θ` and no real zero in `(θ, 1)` make the lead in the race between primes `≡ 1` and `≡ 3`
  (mod 4), weighted by `log p`, change sign infinitely often, by more than `c·x^θ` each way.

**The two hypotheses are real restrictions.** A real zero `β ∈ (θ, 1)` of `L(s, χ)` (a Siegel zero, if
`β` is near 1) is a singularity on the real axis, which Landau's theorem permits, so the zero-free
conclusion needs `L(σ, χ) ≠ 0` there; numerically `L(σ, χ₄) > 0` on `(0, 1)`, which is not proved
here. The existence of a zero of `L(s, χ)` needs a Hadamard product for `L`; the pilot has one only
for `Ξ` (`PsiOmega.exists_zero_re_ge_half`), so the zero is a hypothesis. With both, this is the
`ψ`-form of Littlewood's 1914 theorem that the race mod 4 changes lead infinitely often.
Both hypotheses are proved for `χ₄` (and `χ₋₃`, `χ₋₈`) in `RealDirichlet.lean` and
`PrimeRaces.lean` (rounds 223–224), giving `race_four_half` with no hypotheses.

No bearing on RH.
-/

open Real Complex MeasureTheory Filter Topology Set ArithmeticFunction

noncomputable section

namespace PsiOmega

open LandauLaplace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {θ c ε : ℝ}

/-- `χ` is real-valued. -/
def IsReal (χ : DirichletCharacter ℂ N) : Prop := ∀ n : ℕ, ((χ n).re : ℂ) = χ n

/-- `Λ(n) Re χ(n)`, whose summatory function is `ψ(x, χ)` when `χ` is real. -/
def fχ (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ := vonMangoldt n * (χ n).re

omit [NeZero N] in
theorem linBound_fχ : LinBound (fχ χ) (Real.log 4 + 4) := fun x hx => by
  calc |summ (fχ χ) x| ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |fχ χ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt k : ℝ) := Finset.sum_le_sum fun k _ => by
        rw [fχ, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_of_le_one_right vonMangoldt_nonneg
          ((Complex.abs_re_le_norm _).trans (norm_le_one χ _))
    _ = Chebyshev.psi x := summ_vonMangoldt x
    _ ≤ _ := Chebyshev.psi_le_const_mul_self hx

theorem LSeries_fχ (hχ : IsReal χ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (fχ χ n : ℂ)) s = -deriv (LFunction χ) s / LFunction χ s := by
  have e : (fun n => (fχ χ n : ℂ)) = (fun n : ℕ => χ n) * fun n => (vonMangoldt n : ℂ) := by
    funext n; simp only [fχ, Pi.mul_apply]; push_cast; rw [hχ n, mul_comm]
  rw [e, LSeries_twist_vonMangoldt_eq χ hs, deriv_LFunction_eq_deriv_LSeries χ hs,
    LFunction_eq_LSeries χ hs]

omit [NeZero N] in
theorem LSeriesSummable_fχ (hχ : IsReal χ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (fχ χ n : ℂ)) s := by
  have e : (fun n => (fχ χ n : ℂ)) = (fun n : ℕ => χ n) * fun n => (vonMangoldt n : ℂ) := by
    funext n; simp only [fχ, Pi.mul_apply]; push_cast; rw [hχ n, mul_comm]
  rw [e]; exact LSeriesSummable_twist_vonMangoldt χ hs

/-- **The transform equals `F = c/(s − θ) + εL′/(sL)` for `Re s > 1`.** -/
theorem lap_eq_FZ_chi (hχ : IsReal χ) (hθ1 : θ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    lap μ1 (Aof (fχ χ) 0 θ c ε) Real.log s = FZ (LFunction χ) θ c ε 0 s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hL : LFunction χ s ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inr fun h => by
    rw [h, one_re] at hs; exact lt_irrefl _ hs) hs.le
  rw [lap_Aof linBound_fχ hθ1 hs (LSeriesSummable_fχ hχ hs), LSeries_fχ hχ hs]
  unfold FZ
  push_cast
  field_simp
  ring

/-- `L(·, χ)` satisfies the hypotheses of the generic theorem above `θ`. -/
theorem zData_LFunction (hχ1 : χ ≠ 1) (hS : ∀ σ : ℝ, θ < σ → σ < 1 → LFunction χ σ ≠ 0) :
    ZData (LFunction χ) θ where
  diff := differentiable_LFunction hχ1
  ne_zero_re_ge_one s hs := LFunction_ne_zero_of_one_le_re χ (.inl hχ1) hs
  real_ne_zero σ hσ := by
    rcases lt_or_ge σ 1 with h | h
    · exact hS σ hσ h
    · exact LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (by rw [ofReal_re]; exact h)

/-- **Landau's theorem for `ψ(x, χ)`.** Let `χ ≠ 1` be real with `L(σ, χ) ≠ 0` on `(θ, 1)`. If
`εψ(x, χ) ≤ c·x^θ` for every `x > 1`, with `ε ≠ 0` and `0 < θ ≤ 1`, then `L(s, χ)` has no zero with
`Re s > θ`. -/
theorem LFunction_ne_zero_of_psiChi (hχ1 : χ ≠ 1) (hχ : IsReal χ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hε : ε ≠ 0) (hS : ∀ σ : ℝ, θ < σ → σ < 1 → LFunction χ σ ≠ 0)
    (h : ∀ x : ℝ, 1 < x → ε * summ (fχ χ) x ≤ c * x ^ θ) {ρ : ℂ} (hρθ : θ < ρ.re) :
    LFunction χ ρ ≠ 0 := by
  have h' : ∀ x : ℝ, 1 < x → ε * (summ (fχ χ) x - 0 * x) ≤ c * x ^ θ := fun x hx => by
    rw [zero_mul, sub_zero]; exact h x hx
  have hZ := zData_LFunction hχ1 hS
  exact ne_zero_of_mellin (F := FZ (LFunction χ) θ c ε 0) (R0 := 1) hZ (hyp_Aof h')
    (conv_Aof_three linBound_fχ hθ1) (fun s hs => (lap_eq_FZ_chi hχ hθ1 hs).symm)
    (fun s hs hZs => FZ_differentiableAt hZ.diff
      (fun e => by rw [e, ofReal_re] at hs; exact lt_irrefl _ hs)
      (fun e => by rw [e, zero_re] at hs; linarith) hZs)
    (fun q hq _ n g hn hg hg0 hZg => FZ_pole hε hq hθ hn hg hg0 hZg) hρθ

/-- **`ψ(x, χ) = Ω±(x^θ)`.** For `χ ≠ 1` real, a zero `ρ` of `L(s, χ)` with `Re ρ > θ > 0`, and no
real zero of `L(s, χ)` in `(θ, 1)`: whatever `c` and `X`, `ψ(x, χ)` exceeds `c·x^θ` at some `x > X`
and falls below `−c·x^θ` at some `x > X`. -/
theorem psiChi_omega (hχ1 : χ ≠ 1) (hχ : IsReal χ) {ρ : ℂ} (hρ : LFunction χ ρ = 0) (hθ : 0 < θ)
    (hθρ : θ < ρ.re) (hS : ∀ σ : ℝ, θ < σ → σ < 1 → LFunction χ σ ≠ 0) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < summ (fχ χ) x) ∧ (∃ x, X < x ∧ summ (fχ χ) x < -(c * x ^ θ)) := by
  have hρ1 : ρ.re < 1 := by
    by_contra h'; exact LFunction_ne_zero_of_one_le_re χ (.inl hχ1) (not_lt.1 h') hρ
  have H := omega_of_zeroFree (κ := 0) linBound_fχ hθ (fun c ε hε h =>
    LFunction_ne_zero_of_psiChi (c := c) (ε := ε) hχ1 hχ hθ (by linarith)
      (by rcases hε with rfl | rfl <;> norm_num) hS
      (fun x hx => by have := h x hx; rwa [zero_mul, sub_zero] at this) hθρ hρ) c X
  simp only [zero_mul, sub_zero] at H
  exact H

/-! ## The race mod 4 -/

/-- `χ₄` as a Dirichlet character with complex values. -/
def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chi4_nat (n : ℕ) : chi4 n = ((ZMod.χ₄ n : ℤ) : ℂ) := rfl

theorem chi4_ne_one : chi4 ≠ 1 := fun h => by
  have h3 : IsUnit ((3 : ℕ) : ZMod 4) := by
    rw [← ZMod.coe_unitOfCoprime 3 (by norm_num : Nat.Coprime 3 4)]; exact Units.isUnit _
  have := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ℕ)) h
  simp only [MulChar.one_apply h3, chi4_nat, ZMod.χ₄_nat_eq_if_mod_four] at this
  norm_num at this

theorem chi4_isReal : IsReal chi4 := fun n => by rw [chi4_nat]; simp

/-- `ψ(x; q, a) = Σ_{n ≤ x, n ≡ a (q)} Λ(n)`. -/
def psiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, if k % q = a then (vonMangoldt k : ℝ) else 0

theorem summ_fχ_chi4 (x : ℝ) : summ (fχ chi4) x = psiAP 4 1 x - psiAP 4 3 x := by
  unfold summ psiAP
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fχ, chi4_nat, ZMod.χ₄_nat_eq_if_mod_four]
  have h4 := Nat.mod_lt k (show 0 < 4 by norm_num)
  have h2 : k % 2 = k % 4 % 2 := (Nat.mod_mod_of_dvd k (by norm_num)).symm
  interval_cases hk : k % 4 <;> simp_all

/-- **The prime race mod 4 changes lead infinitely often.** If `L(s, χ₄)` has a zero `ρ` with
`Re ρ > θ > 0` and no real zero in `(θ, 1)`, then for every `c` and `X` there are `x, x' > X` with
`ψ(x; 4, 1) − ψ(x; 4, 3) > c·x^θ` and `ψ(x'; 4, 1) − ψ(x'; 4, 3) < −c·x'^θ`. -/
theorem race_four {ρ : ℂ} (hρ : LFunction chi4 ρ = 0) (hθ : 0 < θ) (hθρ : θ < ρ.re)
    (hS : ∀ σ : ℝ, θ < σ → σ < 1 → LFunction chi4 σ ≠ 0) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < psiAP 4 1 x - psiAP 4 3 x) ∧
      (∃ x, X < x ∧ psiAP 4 1 x - psiAP 4 3 x < -(c * x ^ θ)) := by
  simpa only [summ_fχ_chi4] using psiChi_omega chi4_ne_one chi4_isReal hρ hθ hθρ hS c X

end PsiOmega

#print axioms PsiOmega.LFunction_ne_zero_of_psiChi
#print axioms PsiOmega.psiChi_omega
#print axioms PsiOmega.race_four
