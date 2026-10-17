/-
# Round 526, part 1: ratios of `Γ` on vertical lines, and the functional equation reflected to the modulus `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 526 proves a large-values estimate of Huxley's shape over the characters mod `q`, one point per character
(`LinnikReflect.huxley_large_values`, part 6): the off-diagonal terms of the Halász–Montgomery inequality are
reflected through the functional equation, and the dual sums are bounded by the product trick against the large values
themselves. This part gives the functional equation in the form the reflection uses, with explicit bounds on the
reflected factors.

* `norm_Gamma_le_ratio`: `|Γ(a + iv)| ≤ e^{KQ(a, b)}(1 + |v|)^{a−b}|Γ(b + iv)|` for `a, b ≥ 1/4` (round 524's
  `LinnikGamma.log_norm_Gamma_le` and `LinnikGamma.log_norm_Gamma_ge`).
* `norm_Gamma_half_ratio`: `|Γ((1 − s + a)/2)|·|Γ((s + a)/2)⁻¹| ≤ (128/3)(15e⁴)⁶(1 + |Im s|)^{1/2−Re s}` for
  `0 ≤ a ≤ 1` and `−5/16 ≤ Re s ≤ 13/16`.
* `norm_gr_le`: `|γ_{ψ⁻¹}(1 − s)/γ_ψ(s)| ≤ CG(1 + |Im s|)^{1/2−Re s}` on `−5/16 ≤ Re s ≤ 13/16`, for every Dirichlet
  character `ψ`.
* `norm_eulerQ_inv_le`: the Euler factor `eulerQ(s) = ∏_{p | q}(1 − ψ⁻¹(p)p^{−(1−s)})` has
  `|eulerQ(s)|⁻¹ ≤ ∏_{p | q}(1 − p^{−θ})⁻¹` on `Re s ≤ 1 − θ`, `θ > 0`; `prod_inv_one_sub_le` bounds that product by
  `(1 − 2^{−θ})^{−⌈Y⌉}q^ε`, `Y = max(2^{1/θ}, 2^{1/ε})`.
* `LFunction_eq_reflect`: for `ψ` primitive mod `f`, `ψ ≠ 1`, `f | q` and `Re s < 1`,
  `L(s, ψ) = f^{1/2−s}ε(ψ)·(γ_{ψ⁻¹}(1 − s)/γ_ψ(s))·eulerQ(s)⁻¹·L(1 − s, χ⁻¹)` with `χ` the character mod `q` induced by
  `ψ` (Mathlib's `completedLFunction_one_sub` and `LFunction_changeLevel`).
-/

import LinnikHuxley

open Complex Real Finset MeasureTheory Set

noncomputable section

namespace LinnikReflect

open DirichletCharacter

/-! ### Ratios of values of `Γ` on a horizontal line -/

/-- The constant of `norm_Gamma_le_ratio`. -/
def KQ (a b : ℝ) : ℝ :=
  |a - 1 / 2| * Real.log (5 * Real.exp 4 * max 1 a) + |b - 1 / 2| * Real.log (5 * Real.exp 4)

/-- `|Γ(a + iv)| ≤ e^{KQ(a, b)}(1 + |v|)^{a−b}|Γ(b + iv)|` for `a, b ≥ 1/4` (round 524's
`LinnikGamma.log_norm_Gamma_le` at `a` and `LinnikGamma.log_norm_Gamma_ge` at `b`). -/
theorem norm_Gamma_le_ratio {a b : ℝ} (ha : 1 / 4 ≤ a) (hb : 1 / 4 ≤ b) (v : ℝ) :
    ‖Complex.Gamma (a + v * I)‖ ≤ Real.exp (KQ a b) * (1 + |v|) ^ (a - b) * ‖Complex.Gamma (b + v * I)‖ := by
  have hA := LinnikGamma.log_norm_Gamma_le ha v
  have hB := LinnikGamma.log_norm_Gamma_ge hb v
  have hpa : 0 < ‖Complex.Gamma (a + v * I)‖ := by
    rw [norm_pos_iff]; exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpb : 0 < ‖Complex.Gamma (b + v * I)‖ := by
    rw [norm_pos_iff]; exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hv : 0 < 1 + |v| := by positivity
  rw [← Real.exp_log hpa, ← Real.exp_log hpb, Real.rpow_def_of_pos hv, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  unfold KQ
  linarith

/-- `KQ(a, b) ≤ 2 log(15e⁴)` for `a, b ∈ [1/4, 3]`. -/
lemma KQ_le {a b : ℝ} (ha : 1 / 4 ≤ a) (ha3 : a ≤ 3) (hb : 1 / 4 ≤ b) (hb3 : b ≤ 3) :
    KQ a b ≤ 6 * Real.log (15 * Real.exp 4) := by
  have he : (1 : ℝ) ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  have hL1 : Real.log (5 * Real.exp 4 * max 1 a) ≤ Real.log (15 * Real.exp 4) := by
    apply Real.log_le_log (by positivity)
    have : max 1 a ≤ 3 := max_le (by norm_num) ha3
    nlinarith
  have hL2 : Real.log (5 * Real.exp 4) ≤ Real.log (15 * Real.exp 4) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hL0 : 0 ≤ Real.log (5 * Real.exp 4) := Real.log_nonneg (by nlinarith)
  have hL0' : 0 ≤ Real.log (5 * Real.exp 4 * max 1 a) := by
    apply Real.log_nonneg
    have : 1 ≤ max 1 a := le_max_left _ _
    nlinarith
  have h1 : |a - 1 / 2| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |b - 1 / 2| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
  unfold KQ
  calc |a - 1 / 2| * Real.log (5 * Real.exp 4 * max 1 a) + |b - 1 / 2| * Real.log (5 * Real.exp 4)
      ≤ 3 * Real.log (15 * Real.exp 4) + 3 * Real.log (15 * Real.exp 4) :=
        add_le_add (mul_le_mul h1 hL1 hL0' (by norm_num)) (mul_le_mul h2 hL2 hL0 (by norm_num))
    _ = 6 * Real.log (15 * Real.exp 4) := by ring

/-- `Γ(w)⁻¹ = w·Γ(w + 1)⁻¹` for every `w` (both sides vanish at `w = 0`). -/
lemma Gamma_inv_eq (w : ℂ) : (Complex.Gamma w)⁻¹ = w * (Complex.Gamma (w + 1))⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one w hw, mul_inv, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]

/-- `(1 + |v/2|)^e ≤ 2^{|e|}(1 + |v|)^e`. -/
lemma one_add_half_rpow_le (v e : ℝ) : (1 + |v / 2|) ^ e ≤ 2 ^ |e| * (1 + |v|) ^ e := by
  have hv : 0 < 1 + |v| := by positivity
  have h1 : (1 + |v|) / 2 ≤ 1 + |v / 2| := by rw [abs_div, abs_two]; linarith [abs_nonneg v]
  have h2 : 1 + |v / 2| ≤ 1 + |v| := by rw [abs_div, abs_two]; linarith [abs_nonneg v]
  have h0 : 0 < 1 + |v / 2| := by positivity
  rcases le_or_gt 0 e with he | he
  · calc (1 + |v / 2|) ^ e ≤ (1 + |v|) ^ e := Real.rpow_le_rpow h0.le h2 he
      _ ≤ 2 ^ |e| * (1 + |v|) ^ e := le_mul_of_one_le_left (by positivity)
          (Real.one_le_rpow (by norm_num) (abs_nonneg e))
  · calc (1 + |v / 2|) ^ e ≤ ((1 + |v|) / 2) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) h1 he.le
      _ = 2 ^ |e| * (1 + |v|) ^ e := by
          rw [Real.div_rpow hv.le (by norm_num), abs_of_neg he, Real.rpow_neg (by norm_num)]
          field_simp

/-- **The ratio `Γ((1 − s + a)/2)/Γ((s + a)/2)`**: for `0 ≤ a ≤ 1` and `−5/16 ≤ Re s ≤ 13/16`,
`|Γ((1 − s + a)/2)|·|Γ((s + a)/2)⁻¹| ≤ (128/3)(15e⁴)⁶(1 + |Im s|)^{1/2−Re s}`. Both arguments are moved right by one
(`Γ(A) = Γ(A + 1)/A`, `Γ(B)⁻¹ = BΓ(B + 1)⁻¹`), and then `norm_Gamma_le_ratio`. -/
theorem norm_Gamma_half_ratio {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {s : ℂ} (hs1 : -5 / 16 ≤ s.re)
    (hs2 : s.re ≤ 13 / 16) :
    ‖Complex.Gamma ((1 - s + a) / 2)‖ * ‖(Complex.Gamma ((s + a) / 2))⁻¹‖ ≤
      128 / 3 * (15 * Real.exp 4) ^ (6 : ℝ) * (1 + |s.im|) ^ (1 / 2 - s.re) := by
  set x := s.re with hx
  set y := s.im with hy
  set A : ℂ := (1 - s + a) / 2 with hA
  set B : ℂ := (s + a) / 2 with hB
  have hAre : A.re = (1 - x + a) / 2 := by simp [hA, hx]
  have hAim : A.im = -(y / 2) := by simp [hA, hy]; ring
  have hBre : B.re = (x + a) / 2 := by simp [hB, hx]
  have hBim : B.im = y / 2 := by simp [hB, hy]
  have hA0 : A ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hAre] at this; simp at this; linarith
  -- `Γ(A) = Γ(A + 1)/A` and `|Γ(A + 1)| = |Γ(conj(A + 1))|`
  have hGA : ‖Complex.Gamma A‖ = ‖Complex.Gamma (((1 - x + a) / 2 + 1 : ℝ) + (y / 2 : ℝ) * I)‖ / ‖A‖ := by
    have e1 : Complex.Gamma A = Complex.Gamma (A + 1) / A := by
      rw [Complex.Gamma_add_one A hA0]; field_simp
    have e2 : (((1 - x + a) / 2 + 1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I = (starRingEnd ℂ) (A + 1) := by
      apply Complex.ext <;> simp [hAre, hAim]
    rw [e1, norm_div, e2, Complex.Gamma_conj, Complex.norm_conj]
  have hGB : ‖(Complex.Gamma B)⁻¹‖ = ‖B‖ * ‖(Complex.Gamma (((x + a) / 2 + 1 : ℝ) + (y / 2 : ℝ) * I))⁻¹‖ := by
    have e2 : B + 1 = (((x + a) / 2 + 1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hBre, hBim]
    rw [Gamma_inv_eq B, norm_mul, e2]
  have hr := norm_Gamma_le_ratio (a := (1 - x + a) / 2 + 1) (b := (x + a) / 2 + 1) (by linarith) (by linarith)
    (y / 2)
  have hK := KQ_le (a := (1 - x + a) / 2 + 1) (b := (x + a) / 2 + 1) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hpos : 0 < ‖Complex.Gamma (((x + a) / 2 + 1 : ℝ) + (y / 2 : ℝ) * I)‖ := by
    rw [norm_pos_iff]; exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  -- `|B| ≤ (64/3)|A|`
  have hBA : ‖B‖ ≤ 64 / 3 * ‖A‖ := by
    have h1 : ‖B‖ ≤ |B.re| + |B.im| := Complex.norm_le_abs_re_add_abs_im B
    have h2 : |A.re| ≤ ‖A‖ := Complex.abs_re_le_norm A
    have h3 : |A.im| ≤ ‖A‖ := Complex.abs_im_le_norm A
    rw [hBre, hBim] at h1
    rw [hAre] at h2
    rw [hAim, abs_neg] at h3
    have hb : |(x + a) / 2| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have ha' : 3 / 32 ≤ |(1 - x + a) / 2| := le_abs.2 (Or.inl (by linarith))
    linarith
  have hApos : 0 < ‖A‖ := norm_pos_iff.2 hA0
  -- the exponent
  have hexp : (1 - x + a) / 2 + 1 - ((x + a) / 2 + 1) = 1 / 2 - x := by ring
  rw [hexp] at hr
  have hhalf := one_add_half_rpow_le y (1 / 2 - x)
  have habs : |1 / 2 - x| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h2abs : (2 : ℝ) ^ |1 / 2 - x| ≤ 2 := by
    calc (2 : ℝ) ^ |1 / 2 - x| ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) habs
      _ = 2 := Real.rpow_one 2
  have hexpK : Real.exp (KQ ((1 - x + a) / 2 + 1) ((x + a) / 2 + 1)) ≤ (15 * Real.exp 4) ^ (6 : ℝ) := by
    calc Real.exp (KQ ((1 - x + a) / 2 + 1) ((x + a) / 2 + 1)) ≤ Real.exp (6 * Real.log (15 * Real.exp 4)) :=
          Real.exp_le_exp.2 hK
      _ = (15 * Real.exp 4) ^ (6 : ℝ) := by
          rw [Real.rpow_def_of_pos (by positivity), mul_comm]
  rw [hGA, hGB]
  set G1 := ‖Complex.Gamma (((1 - x + a) / 2 + 1 : ℝ) + (y / 2 : ℝ) * I)‖ with hG1
  set G2 := ‖Complex.Gamma (((x + a) / 2 + 1 : ℝ) + (y / 2 : ℝ) * I)‖ with hG2
  have hG2inv : ‖(Complex.Gamma (((x + a) / 2 + 1 : ℝ) + (y / 2 : ℝ) * I))⁻¹‖ = G2⁻¹ := by rw [norm_inv]
  rw [hG2inv]
  have hy2 : (1 + |y / 2|) ^ (1 / 2 - x) ≤ 2 * (1 + |y|) ^ (1 / 2 - x) :=
    hhalf.trans (mul_le_mul_of_nonneg_right h2abs (by positivity))
  have hP : 0 ≤ (1 + |y|) ^ (1 / 2 - x) := by positivity
  have hP' : 0 ≤ (1 + |y / 2|) ^ (1 / 2 - x) := by positivity
  have hq1 : G1 * G2⁻¹ ≤ Real.exp (KQ ((1 - x + a) / 2 + 1) ((x + a) / 2 + 1)) * (1 + |y / 2|) ^ (1 / 2 - x) := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact hr
  have hq2 : ‖B‖ / ‖A‖ ≤ 64 / 3 := by rw [div_le_iff₀ hApos]; exact hBA
  calc G1 / ‖A‖ * (‖B‖ * G2⁻¹) = G1 * G2⁻¹ * (‖B‖ / ‖A‖) := by field_simp
    _ ≤ (Real.exp (KQ ((1 - x + a) / 2 + 1) ((x + a) / 2 + 1)) * (1 + |y / 2|) ^ (1 / 2 - x)) * (64 / 3) :=
        mul_le_mul hq1 hq2 (by positivity) (by positivity)
    _ ≤ ((15 * Real.exp 4) ^ (6 : ℝ) * (2 * (1 + |y|) ^ (1 / 2 - x))) * (64 / 3) := by gcongr
    _ = 128 / 3 * (15 * Real.exp 4) ^ (6 : ℝ) * (1 + |y|) ^ (1 / 2 - x) := by ring

/-! ### The reflection factor -/

/-- The ratio of Archimedean factors `γ_{ψ⁻¹}(1 − s)/γ_ψ(s)`. -/
def gr {f : ℕ} (ψ : DirichletCharacter ℂ f) (s : ℂ) : ℂ := gammaFactor ψ⁻¹ (1 - s) * (gammaFactor ψ s)⁻¹

/-- The constant of `norm_gr_le`. -/
def CG : ℝ := Real.pi * (128 / 3 * (15 * Real.exp 4) ^ (6 : ℝ))

lemma CG_pos : 0 < CG := by unfold CG; positivity

/-- `‖π^{−u/2}‖ = π^{−Re u/2}`. -/
lemma norm_pi_cpow (u : ℂ) : ‖(Real.pi : ℂ) ^ (-u / 2)‖ = Real.pi ^ (-u.re / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  simp

/-- **The ratio of Archimedean factors**: `|γ_{ψ⁻¹}(1 − s)/γ_ψ(s)| ≤ CG(1 + |Im s|)^{1/2−Re s}` on
`−5/16 ≤ Re s ≤ 13/16`, for every Dirichlet character `ψ` (`norm_Gamma_half_ratio` with `a = 0` or `1`). -/
theorem norm_gr_le {f : ℕ} (ψ : DirichletCharacter ℂ f) {s : ℂ} (hs1 : -5 / 16 ≤ s.re) (hs2 : s.re ≤ 13 / 16) :
    ‖gr ψ s‖ ≤ CG * (1 + |s.im|) ^ (1 / 2 - s.re) := by
  -- the common step
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ‖Complex.Gammaℝ (1 - s + a) * (Complex.Gammaℝ (s + a))⁻¹‖ ≤ CG * (1 + |s.im|) ^ (1 / 2 - s.re) := by
    intro a ha0 ha1
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, mul_inv, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv,
      norm_pi_cpow, norm_pi_cpow]
    have hG := norm_Gamma_half_ratio ha0 ha1 hs1 hs2
    have hre1 : (1 - s + (a : ℂ)).re = 1 - s.re + a := by simp
    have hre2 : (s + (a : ℂ)).re = s.re + a := by simp
    rw [hre1, hre2]
    have hpi : Real.pi ^ (-(1 - s.re + a) / 2) * (Real.pi ^ (-(s.re + a) / 2))⁻¹ ≤ Real.pi := by
      rw [← Real.rpow_neg Real.pi_pos.le, ← Real.rpow_add Real.pi_pos]
      calc Real.pi ^ (-(1 - s.re + a) / 2 + -(-(s.re + a) / 2)) ≤ Real.pi ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
        _ = Real.pi := Real.rpow_one _
    have e1 : Complex.Gamma ((1 - s + a) / 2) = Complex.Gamma ((1 - s + (a : ℂ)) / 2) := rfl
    have hG' : ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2)‖ * ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖⁻¹ ≤
        128 / 3 * (15 * Real.exp 4) ^ (6 : ℝ) * (1 + |s.im|) ^ (1 / 2 - s.re) := by
      rw [← norm_inv]; exact hG
    have hp1 : 0 ≤ Real.pi ^ (-(1 - s.re + a) / 2) := by positivity
    have hp2 : 0 ≤ (Real.pi ^ (-(s.re + a) / 2))⁻¹ := by positivity
    calc Real.pi ^ (-(1 - s.re + a) / 2) * ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2)‖ *
          ((Real.pi ^ (-(s.re + a) / 2))⁻¹ * ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖⁻¹)
        = (Real.pi ^ (-(1 - s.re + a) / 2) * (Real.pi ^ (-(s.re + a) / 2))⁻¹) *
            (‖Complex.Gamma ((1 - s + (a : ℂ)) / 2)‖ * ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖⁻¹) := by ring
      _ ≤ Real.pi * (128 / 3 * (15 * Real.exp 4) ^ (6 : ℝ) * (1 + |s.im|) ^ (1 / 2 - s.re)) :=
          mul_le_mul hpi hG' (by positivity) Real.pi_pos.le
      _ = CG * (1 + |s.im|) ^ (1 / 2 - s.re) := by unfold CG; ring
  unfold gr
  rcases ψ.even_or_odd with h | h
  · have h' : ψ⁻¹.Even := (LinnikFE.even_inv_iff ψ).2 h
    rw [h'.gammaFactor_def, h.gammaFactor_def]
    simpa using key 0 le_rfl zero_le_one
  · have h' : ψ⁻¹.Odd := (LinnikFE.odd_inv_iff ψ).2 h
    rw [h'.gammaFactor_def, h.gammaFactor_def]
    have := key 1 zero_le_one le_rfl
    simpa using this

/-- The Euler factor `∏_{p | q}(1 − ψ⁻¹(p)p^{−(1−s)})` relating `L(1 − s, ψ⁻¹)` to the `L`-function of the
character mod `q` induced by `ψ⁻¹`. -/
def eulerQ {f : ℕ} (ψ : DirichletCharacter ℂ f) (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - ψ⁻¹ p * (p : ℂ) ^ (-(1 - s)))

/-- Each factor of `eulerQ` is at least `1 − p^{Re s − 1}` in modulus. -/
lemma norm_eulerQ_factor_ge {f : ℕ} (ψ : DirichletCharacter ℂ f) {s : ℂ} {p : ℕ} (hp : p.Prime) :
    1 - (p : ℝ) ^ (s.re - 1) ≤ ‖1 - ψ⁻¹ p * (p : ℂ) ^ (-(1 - s))‖ := by
  have hp0 : 0 < p := hp.pos
  have hb : ‖ψ⁻¹ p * (p : ℂ) ^ (-(1 - s))‖ ≤ (p : ℝ) ^ (s.re - 1) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have h1 := DirichletCharacter.norm_le_one ψ⁻¹ p
    have he : (-(1 - s)).re = s.re - 1 := by simp
    rw [he]
    calc ‖ψ⁻¹ p‖ * (p : ℝ) ^ (s.re - 1) ≤ 1 * (p : ℝ) ^ (s.re - 1) := by gcongr
      _ = _ := one_mul _
  have := norm_sub_norm_le (1 : ℂ) (ψ⁻¹ p * (p : ℂ) ^ (-(1 - s)))
  rw [norm_one] at this
  linarith

/-- `eulerQ ψ q s ≠ 0` for `Re s < 1`. -/
lemma eulerQ_ne_zero {f : ℕ} (ψ : DirichletCharacter ℂ f) (q : ℕ) {s : ℂ} (hs : s.re < 1) : eulerQ ψ q s ≠ 0 := by
  unfold eulerQ
  rw [Finset.prod_ne_zero_iff]
  intro p hp h
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h1 := norm_eulerQ_factor_ge ψ (s := s) hpp
  rw [h, norm_zero] at h1
  have : (p : ℝ) ^ (s.re - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by linarith)
  linarith

/-- `∏_{p | q}(1 − p^{−θ})⁻¹ ≤ (1 − 2^{−θ})^{−⌈X⌉}q^ε` with `X = max(2^{1/θ}, 2^{1/ε})`. -/
theorem prod_inv_one_sub_le {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) {q : ℕ} (hq : q ≠ 0) :
    ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-θ))⁻¹ ≤
      ((1 - (2 : ℝ) ^ (-θ))⁻¹) ^ ⌈max ((2 : ℝ) ^ (1 / θ)) ((2 : ℝ) ^ (1 / ε))⌉₊ * (q : ℝ) ^ ε := by
  set X : ℝ := max ((2 : ℝ) ^ (1 / θ)) ((2 : ℝ) ^ (1 / ε)) with hX
  set K : ℝ := (1 - (2 : ℝ) ^ (-θ))⁻¹ with hK
  have h2θ : (2 : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK1 : 1 ≤ K := by
    rw [hK]; apply one_le_inv_iff₀.2; constructor
    · linarith
    · have : 0 < (2 : ℝ) ^ (-θ) := by positivity
      linarith
  have hfac : ∀ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-θ))⁻¹ ≤ (if (p : ℝ) < X then K else 1) * (p : ℝ) ^ ε := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpθ : (p : ℝ) ^ (-θ) ≤ (2 : ℝ) ^ (-θ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have hpos : 0 < 1 - (p : ℝ) ^ (-θ) := by linarith
    have hpe : (1 : ℝ) ≤ (p : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
    split_ifs with h
    · have h1 : (1 - (p : ℝ) ^ (-θ))⁻¹ ≤ K := by
        rw [hK]; apply inv_anti₀ (by linarith) (by linarith)
      calc (1 - (p : ℝ) ^ (-θ))⁻¹ ≤ K := h1
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (p : ℝ) ^ ε := by gcongr
    · push Not at h
      have hθX : (2 : ℝ) ^ (1 / θ) ≤ p := (le_max_left _ _).trans h
      have hεX : (2 : ℝ) ^ (1 / ε) ≤ p := (le_max_right _ _).trans h
      -- `p^θ ≥ 2`, so `p^{−θ} ≤ 1/2`
      have hpθ2 : (p : ℝ) ^ (-θ) ≤ 1 / 2 := by
        have h1 : (2 : ℝ) ≤ (p : ℝ) ^ θ := by
          calc (2 : ℝ) = ((2 : ℝ) ^ (1 / θ)) ^ θ := by
                rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hθ.ne', Real.rpow_one]
            _ ≤ (p : ℝ) ^ θ := Real.rpow_le_rpow (by positivity) hθX hθ.le
        rw [Real.rpow_neg hp0.le]
        rw [inv_le_comm₀ (by positivity) (by norm_num)]
        linarith
      have h2ε : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
          _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hεX hε.le
      have h1 : (1 - (p : ℝ) ^ (-θ))⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hpos (by norm_num)]; linarith
      linarith
  have h0 : ∀ p ∈ q.primeFactors, 0 ≤ (1 - (p : ℝ) ^ (-θ))⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpθ : (p : ℝ) ^ (-θ) ≤ (2 : ℝ) ^ (-θ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have : 0 < 1 - (p : ℝ) ^ (-θ) := by linarith
    positivity
  refine (Finset.prod_le_prod₀ h0 hfac).trans ?_
  rw [Finset.prod_mul_distrib]
  have hcount : ∏ p ∈ q.primeFactors, (if (p : ℝ) < X then K else 1) ≤ K ^ ⌈X⌉₊ := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hsub : Finset.filter (fun p : ℕ => (p : ℝ) < X) q.primeFactors ⊆ Finset.range ⌈X⌉₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_range]
      exact_mod_cast hp.2.trans_le (Nat.le_ceil X)
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    exact pow_le_pow_right₀ hK1 hc
  have hrad : ∏ p ∈ q.primeFactors, (p : ℝ) ^ ε ≤ (q : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  exact mul_le_mul hcount hrad (Finset.prod_nonneg fun p _ => by positivity) (by positivity)

/-- `‖eulerQ ψ q s‖⁻¹ ≤ ∏_{p | q}(1 − p^{−θ})⁻¹` when `Re s ≤ 1 − θ`, `θ > 0`. -/
theorem norm_eulerQ_inv_le {f : ℕ} (ψ : DirichletCharacter ℂ f) (q : ℕ) {θ : ℝ} (hθ : 0 < θ) {s : ℂ}
    (hs : s.re ≤ 1 - θ) :
    ‖(eulerQ ψ q s)⁻¹‖ ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-θ))⁻¹ := by
  unfold eulerQ
  rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod₀
  · intro p _; positivity
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have h1 := norm_eulerQ_factor_ge ψ (s := s) hpp
    have hle : (p : ℝ) ^ (s.re - 1) ≤ (p : ℝ) ^ (-θ) := Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have hlt : (p : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hpos : 0 < 1 - (p : ℝ) ^ (-θ) := by linarith
    exact inv_anti₀ hpos (by linarith)

/-! ### The functional equation in reflected form -/

/-- **The functional equation, reflected to the modulus `q`**: for `ψ` primitive mod `f`, `ψ ≠ 1`, `f | q` and
`Re s < 1`, `L(s, ψ) = f^{1/2−s}ε(ψ)·(γ_{ψ⁻¹}(1 − s)/γ_ψ(s))·eulerQ(s)⁻¹·L(1 − s, χ⁻¹)` with `χ` the character mod `q`
induced by `ψ`: Mathlib's `completedLFunction_one_sub` and `LFunction_changeLevel`. -/
theorem LFunction_eq_reflect {f q : ℕ} [NeZero f] [NeZero q] (hfq : f ∣ q) {ψ : DirichletCharacter ℂ f}
    (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) {s : ℂ} (hs : s.re < 1) :
    LFunction ψ s = (f : ℂ) ^ (1 / 2 - s) * rootNumber ψ * gr ψ s * (eulerQ ψ q s)⁻¹ *
      LFunction (changeLevel hfq ψ)⁻¹ (1 - s) := by
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hψ (Subsingleton.elim _ _)
  have hψi : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ
  -- `L(s, ψ) = Λ(s, ψ)/γ_ψ(s)`
  rw [LFunction_eq_completed_div_gammaFactor ψ s (Or.inr hf1)]
  -- the functional equation at `1 − s`
  have hFE := IsPrimitive.completedLFunction_one_sub hprim (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  -- `Λ(1 − s, ψ⁻¹) = L(1 − s, ψ⁻¹)·γ_{ψ⁻¹}(1 − s)`
  have hγ : gammaFactor ψ⁻¹ (1 - s) ≠ 0 := by
    rcases ψ⁻¹.even_or_odd with h | h
    · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hL1 : completedLFunction ψ⁻¹ (1 - s) = LFunction ψ⁻¹ (1 - s) * gammaFactor ψ⁻¹ (1 - s) := by
    rw [LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inr hf1), div_mul_cancel₀ _ hγ]
  -- the change of level
  have hcl : changeLevel hfq ψ⁻¹ = (changeLevel hfq ψ)⁻¹ := map_inv _ ψ
  have hL2 := LFunction_changeLevel hfq ψ⁻¹ (s := 1 - s) (Or.inl hψi)
  rw [hcl] at hL2
  have hE : eulerQ ψ q s = ∏ p ∈ q.primeFactors, (1 - ψ⁻¹ p * (p : ℂ) ^ (-(1 - s))) := rfl
  have hE0 := eulerQ_ne_zero ψ q hs
  have hL3 : LFunction ψ⁻¹ (1 - s) = (eulerQ ψ q s)⁻¹ * LFunction (changeLevel hfq ψ)⁻¹ (1 - s) := by
    rw [hL2, ← hE, mul_comm (LFunction ψ⁻¹ (1 - s)), ← mul_assoc, inv_mul_cancel₀ hE0, one_mul]
  rw [hL1, hL3]
  have hexp : (f : ℂ) ^ (1 - s - 1 / 2) = (f : ℂ) ^ (1 / 2 - s) := by ring_nf
  rw [hexp]
  unfold gr
  ring

end LinnikReflect

#print axioms LinnikReflect.norm_Gamma_le_ratio
#print axioms LinnikReflect.norm_Gamma_half_ratio
#print axioms LinnikReflect.norm_gr_le
#print axioms LinnikReflect.norm_eulerQ_inv_le
#print axioms LinnikReflect.LFunction_eq_reflect
