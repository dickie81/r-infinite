import Mathlib
import DHPrime

/-! # The two channels of the Davenport–Heilbronn function

`dh = (1 + ε′)L(s, χ₅) + (1 + ε)L(s, χ₅⁻¹)` (`DavenportHeilbronn.lean`) is a sum of two channels,
`L(s, χ)` and `L(s, χ⁻¹)`. This file proves the identities that relate the channels to each other.

**Conjugation symmetry.** For every Dirichlet character `χ ≠ 1`, `conj L(s, χ) = L(s̄, χ⁻¹)`
for every `s` (`conj_LFunction`): `χ⁻¹ = χ̄`, so the two Dirichlet series agree termwise on
`Re s > 1`, and both sides are entire (the identity theorem, as in Mathlib's `riemannZeta_conj`).

**The archimedean-free functional equation of the channel ratio.** For every primitive `χ`,
with `ε = ε_χ` Mathlib's root number, and every `s ∈ ℂ`:
`L(s, χ) L(1 − s, χ) = ε² L(s, χ⁻¹) L(1 − s, χ⁻¹)` (`LFunction_mul_one_sub`). Mathlib's functional
equation `Λ(1 − s, χ) = N^{s − ½} ε Λ(s, χ⁻¹)`, applied at `s` and at `1 − s`, gives the same identity
for the completed functions with the conductor powers cancelling (`completedLFunction_mul_one_sub`);
`χ` and `χ⁻¹` have the same parity, so the same Gamma factor (`gammaFactor_inv`), and Mathlib's
`L = Λ/Γ_χ` holds at every `s` when `N ≠ 1` (division by zero included), so the Gamma factors cancel
with no exceptional points. Equivalently, `R(s)R(1 − s) = ε²` for the channel ratio
`R = L(·, χ)/L(·, χ⁻¹)` wherever it is defined (`LFunction_ratio_mul`).

**The phase lock on the critical line.** For primitive `χ ≠ 1` with `‖ε‖ = 1`, for every real
`t`, `ε̄ L(½ + it, χ) conj L(½ + it, χ⁻¹)` is real (`phase_lock`): on the line `s̄ = 1 − s`, so the
number is `ε̄ L(s, χ) L(1 − s, χ)`, which the functional equation and the conjugation symmetry make
self-conjugate. Hence `L(½ + it, χ)/(ε L(½ + it, χ⁻¹))` is real (`channel_ratio_real`).

**The zero condition.** For primitive `χ ≠ 1` with `ε ≠ −1`, `(1 + ε) = ε(1 + ε′)` (from `εε′ = 1`)
gives `DH_χ(s) = (1 + ε′)(L(s, χ) + ε L(s, χ⁻¹))` (`dhL_eq_mul`), so `DH_χ(s) = 0` iff
`L(s, χ) = −ε L(s, χ⁻¹)` (`dhL_eq_zero_iff_channel`).

**For `χ₅`** (`ε = rootNumber chi5`, `‖ε‖ = 1` by `norm_rootNumber_chi5`): `chi5_channel_fe`,
`chi5_phase_lock`, `chi5_channel_ratio_real`, `dh_eq_zero_iff_channel`, `chi5_channel_ratio`. On the
critical line, where `L(½ + it, χ₅⁻¹) ≠ 0`, the zero condition of `dh` is one real equation in `t`:
`dh(½ + it) = 0` iff the real number `L(½ + it, χ₅)/(ε L(½ + it, χ₅⁻¹))` equals `−1`
(`dh_line_zero_iff`).
-/

open Complex DirichletCharacter

noncomputable section

namespace PsiOmega

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-! ## Conjugation symmetry -/

omit [NeZero N] in
/-- `conj (χ n) = χ⁻¹ n`. -/
theorem conj_apply_natCast (n : ℕ) : (starRingEnd ℂ) (χ n) = χ⁻¹ n := by
  rw [← MulChar.star_apply']
  rfl

/-- `conj (Σ f(n) n^{−s̄}) = Σ conj f(n) n^{−s}`, termwise and without summability hypotheses. -/
theorem conj_LSeries_conj (f : ℕ → ℂ) (s : ℂ) :
    (starRingEnd ℂ) (LSeries f ((starRingEnd ℂ) s)) =
      LSeries (fun n => (starRingEnd ℂ) (f n)) s := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext n
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hn
  · exact map_zero _
  · rw [map_div₀, ← Complex.conj_cpow (n : ℂ) s
      (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne), Complex.conj_natCast]

/-- **Conjugation symmetry**: `conj L(s, χ) = L(s̄, χ⁻¹)` for every `s`, for `χ ≠ 1`. -/
theorem conj_LFunction (hχ : χ ≠ 1) (s : ℂ) :
    (starRingEnd ℂ) (LFunction χ s) = LFunction χ⁻¹ ((starRingEnd ℂ) s) := by
  have hχ' : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ LFunction χ ∘ (starRingEnd ℂ) with hg
  have hgd : Differentiable ℂ g := fun z =>
    differentiableAt_conj_conj_iff.mpr (differentiable_LFunction hχ _)
  have hgz : ∀ z : ℂ, 1 < z.re → g z = LFunction χ⁻¹ z := by
    intro z hz
    simp only [hg, Function.comp_apply]
    rw [LFunction_eq_LSeries χ (by rwa [Complex.conj_re]), LFunction_eq_LSeries χ⁻¹ hz,
      conj_LSeries_conj]
    congr 1
    funext n
    exact conj_apply_natCast χ n
  have heq : g = LFunction χ⁻¹ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hgd.analyticAt z)
      (fun z _ => (differentiable_LFunction hχ').analyticAt z) (z₀ := 2) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hgz z hz
  have h := congrFun heq ((starRingEnd ℂ) s)
  simp only [hg, Function.comp_apply, Complex.conj_conj] at h
  exact h

/-! ## The functional equation of the channel ratio -/

omit [NeZero N] in
theorem even_inv (heven : χ.Even) : χ⁻¹.Even := by
  show χ⁻¹ (-1) = 1
  rw [MulChar.inv_apply_eq_inv', heven, inv_one]

omit [NeZero N] in
/-- `χ` and `χ⁻¹` have the same Gamma factor. -/
theorem gammaFactor_inv (s : ℂ) : gammaFactor χ⁻¹ s = gammaFactor χ s := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, (even_inv χ h).gammaFactor_def]
  · rw [h.gammaFactor_def, (odd_inv χ h).gammaFactor_def]

/-- `Λ(s, χ) Λ(1 − s, χ) = ε² Λ(s, χ⁻¹) Λ(1 − s, χ⁻¹)`: Mathlib's functional equation at `s` and
at `1 − s`; the conductor powers `N^{s − ½} N^{½ − s}` cancel. -/
theorem completedLFunction_mul_one_sub (hprim : χ.IsPrimitive) (s : ℂ) :
    completedLFunction χ s * completedLFunction χ (1 - s) =
      rootNumber χ ^ 2 * (completedLFunction χ⁻¹ s * completedLFunction χ⁻¹ (1 - s)) := by
  have h1 := hprim.completedLFunction_one_sub s
  have h2 := hprim.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at h2
  have hpow : (N : ℂ) ^ (s - 1 / 2) * (N : ℂ) ^ (1 - s - 1 / 2) = 1 := by
    rw [← cpow_add _ _ natCast_ne_zero', show s - 1 / 2 + (1 - s - 1 / 2) = 0 by ring, cpow_zero]
  linear_combination completedLFunction χ s * h1
    + ((N : ℂ) ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s) * h2
    + (rootNumber χ ^ 2 * completedLFunction χ⁻¹ s * completedLFunction χ⁻¹ (1 - s)) * hpow

/-- **The archimedean-free functional equation**: for every primitive `χ` and every `s`,
`L(s, χ) L(1 − s, χ) = ε² L(s, χ⁻¹) L(1 − s, χ⁻¹)`, `ε = ε_χ`. -/
theorem LFunction_mul_one_sub (hprim : χ.IsPrimitive) (s : ℂ) :
    LFunction χ s * LFunction χ (1 - s) =
      rootNumber χ ^ 2 * (LFunction χ⁻¹ s * LFunction χ⁻¹ (1 - s)) := by
  rcases eq_or_ne N 1 with rfl | hN
  · have h1 : χ = 1 := level_one χ
    subst h1
    rw [inv_one, rootNumber_modOne]
    ring
  · rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN),
      LFunction_eq_completed_div_gammaFactor χ (1 - s) (Or.inr hN),
      LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inr hN),
      LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inr hN),
      gammaFactor_inv, gammaFactor_inv, div_mul_div_comm, div_mul_div_comm,
      completedLFunction_mul_one_sub χ hprim s, mul_div_assoc]

/-- **The channel ratio** `R = L(·, χ)/L(·, χ⁻¹)` satisfies `R(s) R(1 − s) = ε²`. -/
theorem LFunction_ratio_mul (hprim : χ.IsPrimitive) {s : ℂ} (h1 : LFunction χ⁻¹ s ≠ 0)
    (h2 : LFunction χ⁻¹ (1 - s) ≠ 0) :
    LFunction χ s / LFunction χ⁻¹ s * (LFunction χ (1 - s) / LFunction χ⁻¹ (1 - s)) =
      rootNumber χ ^ 2 := by
  rw [div_mul_div_comm, div_eq_iff (mul_ne_zero h1 h2), LFunction_mul_one_sub χ hprim s]

/-! ## The phase lock on the critical line -/

omit [NeZero N] in
theorem conj_line (t : ℝ) : (starRingEnd ℂ) (1 / 2 + t * I) = 1 - (1 / 2 + t * I) := by
  apply Complex.ext
  · simp
    norm_num
  · simp

/-- **The phase lock**: if `‖ε‖ = 1`, then `ε̄ L(½ + it, χ) conj L(½ + it, χ⁻¹)` is real for every
real `t`. -/
theorem phase_lock (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hε : ‖rootNumber χ‖ = 1) (t : ℝ) :
    ((starRingEnd ℂ) (rootNumber χ) * LFunction χ (1 / 2 + t * I) *
      (starRingEnd ℂ) (LFunction χ⁻¹ (1 / 2 + t * I))).im = 0 := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hcs : (starRingEnd ℂ) s = 1 - s := conj_line t
  have hcs' : (starRingEnd ℂ) (1 - s) = s := by rw [map_sub, map_one, hcs]; ring
  have hc1 : (starRingEnd ℂ) (LFunction χ⁻¹ s) = LFunction χ (1 - s) := by
    rw [conj_LFunction χ⁻¹ (inv_ne_one.2 hχ), inv_inv, hcs]
  have hc2 : (starRingEnd ℂ) (LFunction χ s) = LFunction χ⁻¹ (1 - s) := by
    rw [conj_LFunction χ hχ, hcs]
  have hc3 : (starRingEnd ℂ) (LFunction χ (1 - s)) = LFunction χ⁻¹ s := by
    rw [conj_LFunction χ hχ, hcs']
  have hεε : (starRingEnd ℂ) (rootNumber χ) * rootNumber χ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hε]
    norm_num
  have hP := LFunction_mul_one_sub χ hprim s
  rw [hc1]
  apply Complex.conj_eq_iff_im.1
  rw [map_mul, map_mul, Complex.conj_conj, hc2, hc3]
  linear_combination (-(starRingEnd ℂ) (rootNumber χ)) * hP
    - (rootNumber χ * LFunction χ⁻¹ s * LFunction χ⁻¹ (1 - s)) * hεε

/-- On the critical line the channel ratio, rotated by `ε`, is real:
`L(½ + it, χ)/(ε L(½ + it, χ⁻¹)) ∈ ℝ` (with Lean's `x/0 = 0`). -/
theorem channel_ratio_real (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hε : ‖rootNumber χ‖ = 1)
    (t : ℝ) :
    (LFunction χ (1 / 2 + t * I) / (rootNumber χ * LFunction χ⁻¹ (1 / 2 + t * I))).im = 0 := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hεε : rootNumber χ * (starRingEnd ℂ) (rootNumber χ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hε]
    norm_num
  have hX := phase_lock χ hχ hprim hε t
  rw [← hs] at hX
  have e : LFunction χ s / (rootNumber χ * LFunction χ⁻¹ s) =
      ((starRingEnd ℂ) (rootNumber χ) * LFunction χ s * (starRingEnd ℂ) (LFunction χ⁻¹ s)) *
        ((Complex.normSq (LFunction χ⁻¹ s) : ℝ) : ℂ)⁻¹ := by
    rcases eq_or_ne (LFunction χ⁻¹ s) 0 with h0 | h0
    · simp [h0]
    · have hε0 : rootNumber χ ≠ 0 := by
        intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
      have hc0 : (starRingEnd ℂ) (LFunction χ⁻¹ s) ≠ 0 := (map_ne_zero _).2 h0
      rw [← Complex.mul_conj, eq_comm, mul_inv_eq_iff_eq_mul₀ (mul_ne_zero h0 hc0),
        div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hε0 h0)]
      linear_combination
        (LFunction χ s * LFunction χ⁻¹ s * (starRingEnd ℂ) (LFunction χ⁻¹ s)) * hεε
  rw [e, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hX,
    zero_mul, mul_zero, add_zero]

/-! ## The zero condition -/

/-- `DH_χ(s) = (1 + ε′)(L(s, χ) + ε L(s, χ⁻¹))`, from `1 + ε = ε(1 + ε′)`. -/
theorem dhL_eq_mul (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (s : ℂ) :
    dhL χ s = (1 + rootNumber χ⁻¹) * (LFunction χ s + rootNumber χ * LFunction χ⁻¹ s) := by
  have heps := rootNumber_mul_rootNumber_inv χ hχ hprim
  unfold dhL
  linear_combination (-LFunction χ⁻¹ s) * heps

/-- **The zero condition**: `DH_χ(s) = 0 ↔ L(s, χ) = −ε L(s, χ⁻¹)`, when `ε ≠ −1`. -/
theorem dhL_eq_zero_iff_channel (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (h1 : 1 + rootNumber χ ≠ 0) (s : ℂ) :
    dhL χ s = 0 ↔ LFunction χ s = -rootNumber χ * LFunction χ⁻¹ s := by
  rw [dhL_eq_mul χ hχ hprim, mul_eq_zero,
    or_iff_right (one_add_rootNumber_inv_ne_zero hχ hprim h1)]
  constructor <;> intro h <;> linear_combination h

/-! ## The Davenport–Heilbronn function -/

/-- **(1) for `χ₅`**: `L(s, χ₅) L(1 − s, χ₅) = ε² L(s, χ₅⁻¹) L(1 − s, χ₅⁻¹)` for every `s`. -/
theorem chi5_channel_fe (s : ℂ) :
    LFunction chi5 s * LFunction chi5 (1 - s) =
      rootNumber chi5 ^ 2 * (LFunction chi5⁻¹ s * LFunction chi5⁻¹ (1 - s)) :=
  LFunction_mul_one_sub chi5 chi5_isPrimitive s

/-- **(2) for `χ₅`, the phase lock**: `ε̄ L(½ + it, χ₅) conj L(½ + it, χ₅⁻¹)` is real. -/
theorem chi5_phase_lock (t : ℝ) :
    ((starRingEnd ℂ) (rootNumber chi5) * LFunction chi5 (1 / 2 + t * I) *
      (starRingEnd ℂ) (LFunction chi5⁻¹ (1 / 2 + t * I))).im = 0 :=
  phase_lock chi5 chi5_ne_one chi5_isPrimitive norm_rootNumber_chi5 t

/-- On the critical line, `L(½ + it, χ₅)/(ε L(½ + it, χ₅⁻¹))` is real. -/
theorem chi5_channel_ratio_real (t : ℝ) :
    (LFunction chi5 (1 / 2 + t * I) / (rootNumber chi5 * LFunction chi5⁻¹ (1 / 2 + t * I))).im
      = 0 :=
  channel_ratio_real chi5 chi5_ne_one chi5_isPrimitive norm_rootNumber_chi5 t

/-- **(3) The zero condition of `dh`**: `dh(s) = 0 ↔ L(s, χ₅) = −ε L(s, χ₅⁻¹)`. -/
theorem dh_eq_zero_iff_channel (s : ℂ) :
    dh s = 0 ↔ LFunction chi5 s = -rootNumber chi5 * LFunction chi5⁻¹ s :=
  dhL_eq_zero_iff_channel chi5 chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero s

/-- **(4) The channel ratio of `χ₅`**: `R(s) R(1 − s) = ε²` where both denominators are nonzero. -/
theorem chi5_channel_ratio {s : ℂ} (h1 : LFunction chi5⁻¹ s ≠ 0)
    (h2 : LFunction chi5⁻¹ (1 - s) ≠ 0) :
    LFunction chi5 s / LFunction chi5⁻¹ s * (LFunction chi5 (1 - s) / LFunction chi5⁻¹ (1 - s)) =
      rootNumber chi5 ^ 2 :=
  LFunction_ratio_mul chi5 chi5_isPrimitive h1 h2

/-- **On the critical line the zero condition is one real equation**: where
`L(½ + it, χ₅⁻¹) ≠ 0`, `dh(½ + it) = 0` iff the real number (`chi5_channel_ratio_real`)
`L(½ + it, χ₅)/(ε L(½ + it, χ₅⁻¹))` equals `−1`. -/
theorem dh_line_zero_iff (t : ℝ) (h : LFunction chi5⁻¹ (1 / 2 + t * I) ≠ 0) :
    dh (1 / 2 + t * I) = 0 ↔
      LFunction chi5 (1 / 2 + t * I) / (rootNumber chi5 * LFunction chi5⁻¹ (1 / 2 + t * I))
        = -1 := by
  have hε0 : rootNumber chi5 ≠ 0 := by
    intro h0
    have h1 := norm_rootNumber_chi5
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  rw [dh_eq_zero_iff_channel, div_eq_iff (mul_ne_zero hε0 h)]
  constructor <;> intro h' <;> linear_combination h'

end PsiOmega

#print axioms PsiOmega.conj_LSeries_conj
#print axioms PsiOmega.conj_LFunction
#print axioms PsiOmega.gammaFactor_inv
#print axioms PsiOmega.completedLFunction_mul_one_sub
#print axioms PsiOmega.LFunction_mul_one_sub
#print axioms PsiOmega.LFunction_ratio_mul
#print axioms PsiOmega.phase_lock
#print axioms PsiOmega.channel_ratio_real
#print axioms PsiOmega.dhL_eq_mul
#print axioms PsiOmega.dhL_eq_zero_iff_channel
#print axioms PsiOmega.chi5_channel_fe
#print axioms PsiOmega.chi5_phase_lock
#print axioms PsiOmega.chi5_channel_ratio_real
#print axioms PsiOmega.dh_eq_zero_iff_channel
#print axioms PsiOmega.chi5_channel_ratio
#print axioms PsiOmega.dh_line_zero_iff
