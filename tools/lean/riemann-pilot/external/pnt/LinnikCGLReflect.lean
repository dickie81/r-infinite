/-
# Round 641: the reflection of the Gram entries (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 640's `LinnikCGLMellin.perron_gram` writes a Gram entry `G(i, k)` as `N^{iτ}(1/2π)∫ L(2 + iv, ψ)H(2 + iv + iτ)
N^{2+iv} dv`, with `ψ = χ_iχ̄_k` and `τ = t_i − t_k`. This file moves that integral into Chen–Gupta–Li's reflected
form, the identity behind their Lemma 6.2: a short dual sum on `Re s = 1/2` and its tail on a line far left.

Plain statement (`reflect_gram`). Let `χ ≠ 1` be a Dirichlet character mod `q`, `ψ` the primitive character mod `f`
inducing it, `N > 0`, `τ` real, `Z ≥ 0` and `K ≥ 1`. With `Φ(s) = f^{1/2−s}ε(ψ)·γ_{ψ⁻¹}(1 − s)/γ_ψ(s)·
∏_{p|q}(1 − ψ⁻¹(p)p^{s−1})⁻¹` (round 526's `LinnikReflect.Phi`) and `E(s) = ∏_{p|q}(1 − ψ(p)p^{−s})`, and writing
`s = σ + iv` on each line,
`∫ L(s, χ)H(s + iτ)N^s dv` on `σ = 2` equals
`∫ H(s + iτ)N^sE(s)Φ(s)Σ_{m≤Z}χ⁻¹(m)m^{s−1} dv` on `σ = 1/2` plus
`∫ H(s + iτ)N^sE(s)Φ(s)Σ_{m>Z}χ⁻¹(m)m^{s−1} dv` on `σ = −K`.

Plain statement (`gram_reflect`). For `χ_i ≠ χ_k`, `G(i, k)` is `N^{iτ}/2π` times that right side at `χ = χ_iχ̄_k`.

Plain statement (`norm_Phi_le_far`). `|Φ(s)| ≤ f^{1/2−Re s}·π·CGK(K)(1 + |Im s|)^{1/2−Re s}·EQh(q)` on
`−K ≤ Re s ≤ 1/2`, with `EQh(q) = ∏_{p|q}(1 − p^{−1/2})⁻¹`; round 526's `norm_Phi_le` covers `−5/16 ≤ Re s ≤ 13/16`.

Their proof of Lemma 6.2 reaches the same identity in another order. It shifts to `Re s = −1`, applies the functional
equation there, splits the dual series at `M`, and then, in their words, "shifting the contour of the integral
involving terms with m ≤ M to Re(s) = 1/2, while shifting the integral involving terms with m > M to Re(s) = −2k
for a large k ∈ ℕ". Here the integral moves to `Re s = 1/2` first, where `L(s, χ) = Φ(s)L(1 − s, χ⁻¹)E(s)`; the
dual series splits there into its first `Z` terms and the rest, an entire function, which moves to `Re s = −K`, where
it is the series' tail. Their `P` and the imprimitive `L(1 − s + it, χ̄)` are this file's `E`, the Euler factor
inside `Φ` and `L(1 − s, χ⁻¹)`.

* `Gamma_inv_eq_prod`, `CGK`, `norm_Gamma_half_ratio_far`, `norm_gr_le_far`, `EQh`, `norm_Phi_le_far`: the
  reflection factor on `−K ≤ Re s ≤ 1/2`. The argument `(s + a)/2` of `Γ` moves right by `K + 1`
  (`Γ(B)⁻¹ = ∏_{j≤K}(B + j)·Γ(B + K + 1)⁻¹`), and then round 526's `norm_Gamma_le_ratio`.
* `Eu`, `norm_Eu_le`, `differentiable_Eu`, `LFunction_eq_prim_mul_Eu`, `LFunction_reflected`:
  `L(s, χ) = L(s, ψ)E(s)` (Mathlib's `LFunction_changeLevel`), so `L(s, χ) = Φ(s)L(1 − s, χ⁻¹)E(s)` for `Re s < 1`
  (round 526's `LFunction_eq_Phi`).
* `one_add_abs_le`, `integrable_of_bound`, `decay_of_bound`, `shift_of_bound`: a contour shift for an integrand
  that is at most `M(1 + |Im s + τ|)^{−2}` on a closed strip (round 472's `SmoothPerron.verticalIntegral_shift`).
* `G1`, `Cf`, `Mn`, `Rt`, `Tl`, `G1_eq`, `Rt_eq_Tl`: the integrands; `G1 = Mn + Rt` for `Re s < 1`, and `Rt = Tl`
  for `Re s < 0` (round 526's `LFunction_sub_dualS`).
* `H_shift_bound`, `G1_bound`, `Cf_bound`, `rest_factor_bound`, `Rt_bound`, `Mn_bound`: the bounds
  `M(1 + |Im s + τ|)^{−2}`, from the decay of `H`, round 254's `PsiOmega.norm_LFunction_leC`
  (`|L(s, χ)| ≤ (q + 1)|s|/Re s`) and round 526's `norm_dualS_le`.
* `differentiableAt_G1`, `differentiableAt_Cf`, `differentiableAt_dualS`, `differentiableAt_Rt`, `differentiableAt_Mn`,
  `continuous_line`: holomorphy where the shifts need it.
* `reflect_gram`, `gram_reflect`: the identity.

The file imports `LinnikCGLMellin.lean` and `LinnikReflect.lean`.
-/

import LinnikCGLMellin
import LinnikReflect

open Complex Set Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikCGLReflect

open LinnikCGLMat LinnikCGLMellin DirichletCharacter LinnikReflect

/-! ### The Gamma ratio on `−K ≤ Re s ≤ 1/2` -/

/-- `Γ(B)⁻¹ = (∏_{j<n}(B + j))Γ(B + n)⁻¹`, from round 526's `Gamma_inv_eq`. -/
lemma Gamma_inv_eq_prod (B : ℂ) (n : ℕ) :
    (Complex.Gamma B)⁻¹ = (∏ j ∈ Finset.range n, (B + j)) * (Complex.Gamma (B + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Gamma_inv_eq (B + n), Finset.prod_range_succ]
    push_cast
    ring_nf

/-- The constant of `norm_Gamma_half_ratio_far`. -/
def CGK (K : ℕ) : ℝ :=
  Real.exp ((K + 2) * (Real.log (5 * Real.exp 4 * (K + 2)) + Real.log (5 * Real.exp 4))) * 2 ^ (K + 1) *
    (2 * K + 2) ^ (K + 1)

lemma CGK_pos (K : ℕ) : 0 < CGK K := by unfold CGK; positivity

/-- **The ratio `Γ((1 − s + a)/2)/Γ((s + a)/2)` far left**: for `0 ≤ a ≤ 1` and `−K ≤ Re s ≤ 1/2`,
`|Γ((1 − s + a)/2)|·|Γ((s + a)/2)⁻¹| ≤ CGK(K)(1 + |Im s|)^{1/2−Re s}`. The second argument moves right by `K + 1`
(`Gamma_inv_eq_prod`), and then round 526's `norm_Gamma_le_ratio`. -/
theorem norm_Gamma_half_ratio_far (K : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {s : ℂ} (hs1 : -(K : ℝ) ≤ s.re)
    (hs2 : s.re ≤ 1 / 2) :
    ‖Complex.Gamma ((1 - s + a) / 2)‖ * ‖(Complex.Gamma ((s + a) / 2))⁻¹‖ ≤
      CGK K * (1 + |s.im|) ^ (1 / 2 - s.re) := by
  set x := s.re with hx
  set y := s.im with hy
  set n : ℕ := K + 1 with hn
  set A : ℂ := (1 - s + a) / 2 with hA
  set B : ℂ := (s + a) / 2 with hB
  have hAre : A.re = (1 - x + a) / 2 := by simp [hA, hx]
  have hAim : A.im = -(y / 2) := by simp [hA, hy]; ring
  have hBre : B.re = (x + a) / 2 := by simp [hB, hx]
  have hBim : B.im = y / 2 := by simp [hB, hy]
  set a' : ℝ := (1 - x + a) / 2 with ha'
  set b' : ℝ := (x + a) / 2 + n with hb'
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hnR : (n : ℝ) = K + 1 := by rw [hn]; push_cast; ring
  have ha'1 : 1 / 4 ≤ a' := by rw [ha']; linarith
  have hb'1 : 1 / 4 ≤ b' := by rw [hb', hnR]; linarith
  -- `|Γ(A)| = |Γ(a' + iy/2)|`
  have hGA : ‖Complex.Gamma A‖ = ‖Complex.Gamma ((a' : ℂ) + (y / 2 : ℝ) * I)‖ := by
    have e2 : ((a' : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I = (starRingEnd ℂ) A := by
      apply Complex.ext <;> simp [hAre, hAim, ha']
    rw [e2, Complex.Gamma_conj, Complex.norm_conj]
  -- `Γ(B)⁻¹ = ∏(B + j)·Γ(b' + iy/2)⁻¹`
  have hBn : B + n = (b' : ℂ) + (y / 2 : ℝ) * I := by
    apply Complex.ext <;> simp [hBre, hBim, hb']
  have hGB : ‖(Complex.Gamma B)⁻¹‖ =
      ‖∏ j ∈ Finset.range n, (B + j)‖ * ‖(Complex.Gamma ((b' : ℂ) + (y / 2 : ℝ) * I))⁻¹‖ := by
    rw [Gamma_inv_eq_prod B n, norm_mul, hBn]
  have hr := norm_Gamma_le_ratio ha'1 hb'1 (y / 2)
  have hpos : 0 < ‖Complex.Gamma ((b' : ℂ) + (y / 2 : ℝ) * I)‖ := by
    rw [norm_pos_iff]; exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  -- the constant
  have he4 : (1 : ℝ) ≤ 5 * Real.exp 4 := by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 4); linarith
  have hKQ : KQ a' b' ≤ (K + 2) * (Real.log (5 * Real.exp 4 * (K + 2)) + Real.log (5 * Real.exp 4)) := by
    unfold KQ
    have h1 : |a' - 1 / 2| ≤ K + 2 := abs_le.2 ⟨by rw [ha']; linarith, by rw [ha']; linarith⟩
    have h2 : |b' - 1 / 2| ≤ K + 2 := abs_le.2 ⟨by rw [hb', hnR]; linarith, by rw [hb', hnR]; linarith⟩
    have hL1 : Real.log (5 * Real.exp 4 * max 1 a') ≤ Real.log (5 * Real.exp 4 * (K + 2)) := by
      apply Real.log_le_log (by positivity)
      have : max 1 a' ≤ K + 2 := max_le (by linarith) (by rw [ha']; linarith)
      gcongr
    have hL0 : 0 ≤ Real.log (5 * Real.exp 4 * max 1 a') :=
      Real.log_nonneg (by nlinarith [le_max_left 1 a'])
    have hL2 : 0 ≤ Real.log (5 * Real.exp 4) := Real.log_nonneg he4
    have hL3 : 0 ≤ Real.log (5 * Real.exp 4 * (K + 2)) := hL0.trans hL1
    calc |a' - 1 / 2| * Real.log (5 * Real.exp 4 * max 1 a') + |b' - 1 / 2| * Real.log (5 * Real.exp 4)
        ≤ (K + 2) * Real.log (5 * Real.exp 4 * (K + 2)) + (K + 2) * Real.log (5 * Real.exp 4) := by
          gcongr
      _ = _ := by ring
  -- the product
  have hprod : ‖∏ j ∈ Finset.range n, (B + j)‖ ≤ (2 * K + 2) ^ (K + 1) * (1 + |y|) ^ n := by
    rw [norm_prod]
    have hBn' : ‖B‖ ≤ (K + 2) / 2 + |y| / 2 := by
      have h1 : ‖B‖ ≤ |B.re| + |B.im| := Complex.norm_le_abs_re_add_abs_im B
      rw [hBre, hBim] at h1
      have e1 : |(x + a) / 2| = |x + a| / 2 := by rw [abs_div, abs_two]
      have e2 : |y / 2| = |y| / 2 := by rw [abs_div, abs_two]
      rw [e1, e2] at h1
      have h2 : |x + a| ≤ K + 2 := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    calc ∏ j ∈ Finset.range n, ‖B + j‖ ≤ ∏ _j ∈ Finset.range n, ((2 * K + 2) * (1 + |y|)) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j hj => ?_
          have hj' : (j : ℝ) ≤ K := by
            have := Finset.mem_range.1 hj
            rw [hn] at this
            exact_mod_cast Nat.lt_succ_iff.1 this
          calc ‖B + j‖ ≤ ‖B‖ + j := by
                refine (norm_add_le _ _).trans ?_
                simp
            _ ≤ (K + 2) / 2 + |y| / 2 + K := by linarith
            _ ≤ (2 * K + 2) * (1 + |y|) := by nlinarith [abs_nonneg y]
      _ = ((2 * K + 2) * (1 + |y|)) ^ n := by rw [Finset.prod_const, Finset.card_range]
      _ = (2 * K + 2) ^ (K + 1) * (1 + |y|) ^ n := by rw [mul_pow, hn]
  -- assemble
  have hexp : a' - b' = 1 / 2 - x - n := by rw [ha', hb']; ring
  rw [hexp] at hr
  have hhalf := one_add_half_rpow_le y (1 / 2 - x - n)
  have habs : |1 / 2 - x - (n : ℝ)| ≤ K + 1 := abs_le.2 ⟨by rw [hnR]; linarith, by rw [hnR]; linarith⟩
  have h2abs : (2 : ℝ) ^ |1 / 2 - x - (n : ℝ)| ≤ 2 ^ (K + 1) := by
    calc (2 : ℝ) ^ |1 / 2 - x - (n : ℝ)| ≤ 2 ^ ((K + 1 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 2 ^ (K + 1) := Real.rpow_natCast 2 (K + 1)
  rw [hGA, hGB]
  set G1 := ‖Complex.Gamma ((a' : ℂ) + (y / 2 : ℝ) * I)‖ with hG1
  set G2 := ‖Complex.Gamma ((b' : ℂ) + (y / 2 : ℝ) * I)‖ with hG2
  have hG2inv : ‖(Complex.Gamma ((b' : ℂ) + (y / 2 : ℝ) * I))⁻¹‖ = G2⁻¹ := by rw [norm_inv]
  rw [hG2inv]
  have hq1 : G1 * G2⁻¹ ≤ Real.exp (KQ a' b') * (1 + |y / 2|) ^ (1 / 2 - x - n) := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact hr
  have hy0 : 0 < 1 + |y| := by positivity
  have hcomb : (1 + |y|) ^ (1 / 2 - x - n) * (1 + |y|) ^ n = (1 + |y|) ^ (1 / 2 - x) := by
    rw [← Real.rpow_natCast (1 + |y|) n, ← Real.rpow_add hy0]; ring_nf
  have hexpK : Real.exp (KQ a' b') ≤
      Real.exp ((K + 2) * (Real.log (5 * Real.exp 4 * (K + 2)) + Real.log (5 * Real.exp 4))) :=
    Real.exp_le_exp.2 hKQ
  calc G1 * (‖∏ j ∈ Finset.range n, (B + j)‖ * G2⁻¹)
      = G1 * G2⁻¹ * ‖∏ j ∈ Finset.range n, (B + j)‖ := by ring
    _ ≤ (Real.exp (KQ a' b') * (2 ^ |1 / 2 - x - (n : ℝ)| * (1 + |y|) ^ (1 / 2 - x - n))) *
          ((2 * K + 2) ^ (K + 1) * (1 + |y|) ^ n) :=
        mul_le_mul (hq1.trans (mul_le_mul_of_nonneg_left hhalf (Real.exp_pos _).le)) hprod (norm_nonneg _)
          (by positivity)
    _ ≤ (Real.exp ((K + 2) * (Real.log (5 * Real.exp 4 * (K + 2)) + Real.log (5 * Real.exp 4))) *
          (2 ^ (K + 1) * (1 + |y|) ^ (1 / 2 - x - n))) * ((2 * K + 2) ^ (K + 1) * (1 + |y|) ^ n) := by
        gcongr
    _ = CGK K * ((1 + |y|) ^ (1 / 2 - x - n) * (1 + |y|) ^ n) := by unfold CGK; ring
    _ = CGK K * (1 + |y|) ^ (1 / 2 - x) := by rw [hcomb]

/-- **The Archimedean ratio far left**: `|γ_{ψ⁻¹}(1 − s)/γ_ψ(s)| ≤ π·CGK(K)(1 + |Im s|)^{1/2−Re s}` on
`−K ≤ Re s ≤ 1/2`, for every Dirichlet character `ψ` (`norm_Gamma_half_ratio_far` with `a = 0` or `1`, as round 526's
`norm_gr_le`). -/
theorem norm_gr_le_far {f : ℕ} (ψ : DirichletCharacter ℂ f) (K : ℕ) {s : ℂ} (hs1 : -(K : ℝ) ≤ s.re)
    (hs2 : s.re ≤ 1 / 2) :
    ‖gr ψ s‖ ≤ Real.pi * CGK K * (1 + |s.im|) ^ (1 / 2 - s.re) := by
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ‖Complex.Gammaℝ (1 - s + a) * (Complex.Gammaℝ (s + a))⁻¹‖ ≤
        Real.pi * CGK K * (1 + |s.im|) ^ (1 / 2 - s.re) := by
    intro a ha0 ha1
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, mul_inv, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv,
      norm_pi_cpow, norm_pi_cpow]
    have hG := norm_Gamma_half_ratio_far K ha0 ha1 hs1 hs2
    have hre1 : (1 - s + (a : ℂ)).re = 1 - s.re + a := by simp
    have hre2 : (s + (a : ℂ)).re = s.re + a := by simp
    rw [hre1, hre2]
    have hpi : Real.pi ^ (-(1 - s.re + a) / 2) * (Real.pi ^ (-(s.re + a) / 2))⁻¹ ≤ Real.pi := by
      rw [← Real.rpow_neg Real.pi_pos.le, ← Real.rpow_add Real.pi_pos]
      calc Real.pi ^ (-(1 - s.re + a) / 2 + -(-(s.re + a) / 2)) ≤ Real.pi ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
        _ = Real.pi := Real.rpow_one _
    have hG' : ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2)‖ * ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖⁻¹ ≤
        CGK K * (1 + |s.im|) ^ (1 / 2 - s.re) := by
      rw [← norm_inv]; exact hG
    have hp1 : 0 ≤ Real.pi ^ (-(1 - s.re + a) / 2) := by positivity
    have hp2 : 0 ≤ (Real.pi ^ (-(s.re + a) / 2))⁻¹ := by positivity
    have hC := CGK_pos K
    calc Real.pi ^ (-(1 - s.re + a) / 2) * ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2)‖ *
          ((Real.pi ^ (-(s.re + a) / 2))⁻¹ * ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖⁻¹)
        = (Real.pi ^ (-(1 - s.re + a) / 2) * (Real.pi ^ (-(s.re + a) / 2))⁻¹) *
            (‖Complex.Gamma ((1 - s + (a : ℂ)) / 2)‖ * ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖⁻¹) := by ring
      _ ≤ Real.pi * (CGK K * (1 + |s.im|) ^ (1 / 2 - s.re)) :=
          mul_le_mul hpi hG' (by positivity) Real.pi_pos.le
      _ = Real.pi * CGK K * (1 + |s.im|) ^ (1 / 2 - s.re) := by ring
  unfold gr
  rcases ψ.even_or_odd with h | h
  · have h' : ψ⁻¹.Even := (LinnikFE.even_inv_iff ψ).2 h
    rw [h'.gammaFactor_def, h.gammaFactor_def]
    simpa using key 0 le_rfl zero_le_one
  · have h' : ψ⁻¹.Odd := (LinnikFE.odd_inv_iff ψ).2 h
    rw [h'.gammaFactor_def, h.gammaFactor_def]
    have := key 1 zero_le_one le_rfl
    simpa using this

/-- The constant `∏_{p | q}(1 − p^{−1/2})⁻¹` bounding `eulerQ(s)⁻¹` on `Re s ≤ 1/2`. -/
def EQh (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

lemma EQh_pos (q : ℕ) : 0 < EQh q := by
  unfold EQh
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have : (p : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have : 0 < 1 - (p : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
  positivity

/-- **The reflection factor far left**: `|Φ(s)| ≤ f^{1/2−Re s}·π·CGK(K)(1 + |Im s|)^{1/2−Re s}·EQh(q)` on
`−K ≤ Re s ≤ 1/2` (round 526's `norm_Phi_le` with `norm_gr_le_far`). -/
theorem norm_Phi_le_far {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hprim : ψ.IsPrimitive) (q K : ℕ) {s : ℂ}
    (hs1 : -(K : ℝ) ≤ s.re) (hs2 : s.re ≤ 1 / 2) :
    ‖Phi ψ q s‖ ≤ (f : ℝ) ^ (1 / 2 - s.re) * (Real.pi * CGK K * (1 + |s.im|) ^ (1 / 2 - s.re)) * EQh q := by
  unfold Phi
  rw [norm_mul, norm_mul, norm_mul, LinnikFE.norm_rootNumber hprim, mul_one]
  have hf : ‖(f : ℂ) ^ (1 / 2 - s)‖ ≤ (f : ℝ) ^ (1 / 2 - s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne f))]; simp
  have hg := norm_gr_le_far ψ K hs1 hs2
  have hE := norm_eulerQ_inv_le ψ q (θ := 1 / 2) (by norm_num) (s := s) (by linarith)
  have hE' : ‖(eulerQ ψ q s)⁻¹‖ ≤ EQh q := by unfold EQh; simpa using hE
  have hC := CGK_pos K
  exact mul_le_mul (mul_le_mul hf hg (norm_nonneg _) (by positivity)) hE' (norm_nonneg _) (by positivity)

/-! ### The Euler factor and the reflected `L`-function -/

/-- The Euler factor `E(s) = ∏_{p | q}(1 − ψ(p)p^{−s})` of `L(s, χ)` over `L(s, ψ)`, for `χ` mod `q` induced by `ψ`. -/
def Eu {f : ℕ} (ψ : DirichletCharacter ℂ f) (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))

/-- `|E(s)| ≤ ∏_{p | q}(1 + p^c)` for `−Re s ≤ c`. -/
lemma norm_Eu_le {f : ℕ} (ψ : DirichletCharacter ℂ f) (q : ℕ) {s : ℂ} {c : ℝ} (hc : -s.re ≤ c) :
    ‖Eu ψ q s‖ ≤ ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ c) := by
  unfold Eu
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  calc ‖1 - ψ p * (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖ψ p * (p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ) ^ c := by
        rw [norm_one, norm_mul]
        have h1 : ‖ψ p‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
        have h2 : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
          rw [Complex.norm_natCast_cpow_of_pos hpp.pos]; simp
        rw [h2]
        have h3 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hp1 hc
        have h4 : 0 ≤ (p : ℝ) ^ (-s.re) := by positivity
        nlinarith [norm_nonneg (ψ p)]

lemma differentiable_Eu {f : ℕ} (ψ : DirichletCharacter ℂ f) (q : ℕ) : Differentiable ℂ (Eu ψ q) := by
  intro s
  unfold Eu
  refine DifferentiableAt.fun_finsetProd fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiableAt_const _).sub
    ((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hp0)))

instance conductor_neZero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) : NeZero ψ.conductor :=
  ⟨ψ.conductor_ne_zero⟩

lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) :
    ψ.primitiveCharacter ≠ 1 := by
  intro h
  apply hψ
  rw [← changeLevel_primitiveCharacter ψ, h, changeLevel_one]

/-- `L(s, χ) = L(s, ψ)E(s)` for `χ ≠ 1` and `ψ` its primitive character (Mathlib's `LFunction_changeLevel`). -/
lemma LFunction_eq_prim_mul_Eu {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (s : ℂ) :
    LFunction χ s = LFunction χ.primitiveCharacter s * Eu χ.primitiveCharacter q s := by
  have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (s := s)
    (Or.inl (primitiveCharacter_ne_one hχ))
  rw [changeLevel_primitiveCharacter] at h
  exact h

/-- **The reflected `L`-function**: for `χ ≠ 1` and `Re s < 1`, `L(s, χ) = Φ(s)L(1 − s, χ⁻¹)E(s)`, with `Φ` and `E`
those of the primitive character of `χ` (round 526's `LFunction_eq_Phi`). -/
lemma LFunction_reflected {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ} (hs : s.re < 1) :
    LFunction χ s =
      Phi χ.primitiveCharacter q s * LFunction χ⁻¹ (1 - s) * Eu χ.primitiveCharacter q s := by
  rw [LFunction_eq_prim_mul_Eu hχ s, LFunction_eq_Phi χ.conductor_dvd_level χ.primitiveCharacter_isPrimitive
    (primitiveCharacter_ne_one hχ) hs, changeLevel_primitiveCharacter]

/-! ### Contour shifts -/

/-- `1 + |y| ≤ (1 + |τ|)(1 + |y + τ|)`. -/
lemma one_add_abs_le (y τ : ℝ) : 1 + |y| ≤ (1 + |τ|) * (1 + |y + τ|) := by
  have h1 : |y| ≤ |y + τ| + |τ| := by
    calc |y| = |(y + τ) + (-τ)| := by ring_nf
      _ ≤ |y + τ| + |-τ| := abs_add_le _ _
      _ = |y + τ| + |τ| := by rw [abs_neg]
  nlinarith [abs_nonneg τ, abs_nonneg (y + τ), mul_nonneg (abs_nonneg τ) (abs_nonneg (y + τ))]

/-- **Integrability on a line** from `|G(x + iy)| ≤ M(1 + |y + τ|)^{−2}`. -/
lemma integrable_of_bound {G : ℂ → ℂ} {x M τ : ℝ} (hcont : Continuous fun y : ℝ => G (x + y * I))
    (hb : ∀ y : ℝ, ‖G (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹) : Integrable fun y : ℝ => G (x + y * I) := by
  have hd : ∀ y : ℝ, M * ((1 + |y + τ|) ^ 2)⁻¹ ≤ |M| * (1 + (y + τ) ^ 2)⁻¹ := by
    intro y
    have h1 : 1 + (y + τ) ^ 2 ≤ (1 + |y + τ|) ^ 2 := by nlinarith [abs_nonneg (y + τ), sq_abs (y + τ)]
    have h2 : ((1 + |y + τ|) ^ 2)⁻¹ ≤ (1 + (y + τ) ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
    calc M * ((1 + |y + τ|) ^ 2)⁻¹ ≤ |M| * ((1 + |y + τ|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ ≤ |M| * (1 + (y + τ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)
  exact ((integrable_inv_one_add_sq.comp_add_right τ).const_mul |M|).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => (hb y).trans (hd y))

/-- **Uniform decay on a strip** from `|G(x + iy)| ≤ M(1 + |y + τ|)^{−2}` there. -/
lemma decay_of_bound {G : ℂ → ℂ} {σ' σ M τ : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc σ' σ, ∀ y : ℝ, ‖G (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹) :
    ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc σ' σ, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η := by
  intro η hη
  refine ⟨|τ| + M / η + 1, fun x hx y hy => (hb x hx y).trans ?_⟩
  have h0 : |y| ≤ |y + τ| + |τ| := by
    calc |y| = |(y + τ) + (-τ)| := by ring_nf
      _ ≤ |y + τ| + |-τ| := abs_add_le _ _
      _ = |y + τ| + |τ| := by rw [abs_neg]
  have h1 : M / η + 1 ≤ 1 + |y + τ| := by linarith
  have h2 : 1 + |y + τ| ≤ (1 + |y + τ|) ^ 2 := by nlinarith [abs_nonneg (y + τ)]
  have hpos : 0 < (1 + |y + τ|) ^ 2 := by positivity
  rw [mul_inv_le_iff₀ hpos]
  have h3 : M = η * (M / η) := by field_simp
  have h4 : 0 ≤ M / η := div_nonneg hM hη.le
  nlinarith

/-- **A contour shift** (round 523's `SmoothPerron.verticalIntegral_shift`) for `G` differentiable on the closed strip
`σ' ≤ Re s ≤ σ` with `|G(x + iy)| ≤ M(1 + |y + τ|)^{−2}` there. -/
theorem shift_of_bound {G : ℂ → ℂ} {σ' σ M τ : ℝ} (hσ : σ' ≤ σ) (hM : 0 ≤ M)
    (hG : ∀ z : ℂ, σ' ≤ z.re → z.re ≤ σ → DifferentiableAt ℂ G z)
    (hb : ∀ x ∈ Icc σ' σ, ∀ y : ℝ, ‖G (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹) :
    ∫ y : ℝ, G (σ + y * I) = ∫ y : ℝ, G (σ' + y * I) := by
  have hcont : ∀ x ∈ Icc σ' σ, Continuous fun y : ℝ => G (x + y * I) := by
    intro x hx
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hz : DifferentiableAt ℂ G (x + y * I) := hG _ (by simp; exact hx.1) (by simp; exact hx.2)
    have hinner : ContinuousAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) y := by fun_prop
    exact ContinuousAt.comp (g := G) hz.continuousAt hinner
  have hhol : HolomorphicOn G (Icc σ' σ ×ℂ univ) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact (hG z hz.1.1 hz.1.2).differentiableWithinAt
  have h := SmoothPerron.verticalIntegral_shift hσ hhol
    (integrable_of_bound (hcont σ ⟨hσ, le_rfl⟩) (hb σ ⟨hσ, le_rfl⟩))
    (integrable_of_bound (hcont σ' ⟨le_rfl, hσ⟩) (hb σ' ⟨le_rfl, hσ⟩)) (decay_of_bound hM hb)
  unfold VerticalIntegral at h
  exact smul_right_injective ℂ Complex.I_ne_zero h

/-! ### The integrands -/

variable {q : ℕ} [NeZero q]

/-- `G₁(s) = L(s, χ)H(s + iτ)N^s`, the integrand of `perron_gram`. -/
def G1 (χ : DirichletCharacter ℂ q) (τ N : ℝ) (s : ℂ) : ℂ := LFunction χ s * H (s + τ * I) * (N : ℂ) ^ s

/-- The common factor `H(s + iτ)N^sE(s)Φ(s)` of the reflected integrands. -/
def Cf (χ : DirichletCharacter ℂ q) (τ N : ℝ) (s : ℂ) : ℂ :=
  H (s + τ * I) * (N : ℂ) ^ s * Eu χ.primitiveCharacter q s * Phi χ.primitiveCharacter q s

/-- **The main part**, `H(s + iτ)N^sE(s)Φ(s)Σ_{m≤Z}χ⁻¹(m)m^{s−1}`. -/
def Mn (χ : DirichletCharacter ℂ q) (τ N : ℝ) (Z : ℕ) (s : ℂ) : ℂ := Cf χ τ N s * dualS χ⁻¹ Z s

/-- The rest, `H(s + iτ)N^sE(s)Φ(s)(L(1 − s, χ⁻¹) − Σ_{m≤Z}χ⁻¹(m)m^{s−1})`. -/
def Rt (χ : DirichletCharacter ℂ q) (τ N : ℝ) (Z : ℕ) (s : ℂ) : ℂ :=
  Cf χ τ N s * (LFunction χ⁻¹ (1 - s) - dualS χ⁻¹ Z s)

/-- **The tail**, `H(s + iτ)N^sE(s)Φ(s)Σ_{m>Z}χ⁻¹(m)m^{s−1}`. -/
def Tl (χ : DirichletCharacter ℂ q) (τ N : ℝ) (Z : ℕ) (s : ℂ) : ℂ := Cf χ τ N s * dualT χ⁻¹ Z s

lemma G1_eq {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (τ N : ℝ) (Z : ℕ) {s : ℂ} (hs : s.re < 1) :
    G1 χ τ N s = Mn χ τ N Z s + Rt χ τ N Z s := by
  unfold G1 Mn Rt Cf
  rw [LFunction_reflected hχ hs]
  ring

lemma Rt_eq_Tl (χ : DirichletCharacter ℂ q) (τ N : ℝ) (Z : ℕ) {s : ℂ} (hs : s.re < 0) :
    Rt χ τ N Z s = Tl χ τ N Z s := by
  unfold Rt Tl
  rw [LFunction_sub_dualS χ⁻¹ Z hs]

/-! ### Their bounds -/

/-- `|H(x + iy + iτ)| ≤ B(1 + |y + τ|)^{−(J+3)}` for `|x| ≤ S`. -/
lemma H_shift_bound (J : ℕ) {S : ℝ} (hS : 0 ≤ S) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x y τ : ℝ, |x| ≤ S →
    ‖H (x + y * I + τ * I)‖ ≤ B * ((1 + |y + τ|) ^ (J + 3))⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := exists_H_bound J hS
  refine ⟨B, hB0, fun x y τ hx => ?_⟩
  have e : (x : ℂ) + y * I + τ * I = x + ((y + τ : ℝ) : ℂ) * I := by push_cast; ring
  rw [e]
  have h := hB x (y + τ) hx
  have hpos : 0 < (1 + |y + τ|) ^ (J + 3) := by positivity
  rw [le_mul_inv_iff₀ hpos]
  linarith [h]

lemma differentiable_cpow_const {N : ℝ} (hN : 0 < N) : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ s :=
  fun _ => differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hN.ne'))

/-- **`G₁` on `1/2 ≤ Re s ≤ 2`**: `|G₁(x + iy)| ≤ M(1 + |y + τ|)^{−2}`, from `|L(s, χ)| ≤ (q + 1)|s|/Re s` (round 254's
`PsiOmega.norm_LFunction_leC`) and the decay of `H`. -/
lemma G1_bound {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (τ : ℝ) {N : ℝ} (hN : 0 < N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (1 / 2 : ℝ) 2, ∀ y : ℝ, ‖G1 χ τ N (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := H_shift_bound 0 (S := 2) (by norm_num)
  refine ⟨4 * ((q : ℝ) + 1) * (1 + |τ|) * B * (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)), by positivity, fun x hx y => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  set s : ℂ := x + y * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hL := PsiOmega.norm_LFunction_leC hχ (s := s) (by rw [hsre]; linarith)
  have hsn : ‖s‖ ≤ 2 + |y| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + |y| := by rw [hsre, hsim, abs_of_pos (by linarith)]; linarith
  have hL' : ‖LFunction χ s‖ ≤ 2 * ((q : ℝ) + 1) * (2 + |y|) := by
    rw [hsre] at hL
    calc ‖LFunction χ s‖ ≤ ((q : ℝ) + 1) * ‖s‖ / x := hL
      _ ≤ ((q : ℝ) + 1) * (2 + |y|) / (1 / 2) := by
          have : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
          gcongr
      _ = 2 * ((q : ℝ) + 1) * (2 + |y|) := by ring
  have hHb := hB x y τ (by rw [abs_of_pos (by linarith)]; linarith)
  have hNb : ‖(N : ℂ) ^ s‖ ≤ N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN, hsre]
    exact rpow_le_add_ends hN hx1 hx2
  have hy := one_add_abs_le y τ
  have hu : 0 < 1 + |y + τ| := by positivity
  unfold G1
  rw [norm_mul, norm_mul]
  have hpoly : 2 + |y| ≤ 2 * ((1 + |τ|) * (1 + |y + τ|)) := by linarith [abs_nonneg y]
  calc ‖LFunction χ s‖ * ‖H (s + τ * I)‖ * ‖(N : ℂ) ^ s‖
      ≤ (2 * ((q : ℝ) + 1) * (2 * ((1 + |τ|) * (1 + |y + τ|)))) * (B * ((1 + |y + τ|) ^ (0 + 3))⁻¹) *
          (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)) := by
        gcongr
        exact hL'.trans (by gcongr)
    _ = 4 * ((q : ℝ) + 1) * (1 + |τ|) * B * (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)) *
          ((1 + |y + τ|) * ((1 + |y + τ|) ^ 3)⁻¹) := by ring
    _ = 4 * ((q : ℝ) + 1) * (1 + |τ|) * B * (N ^ (2 : ℝ) + N ^ (1 / 2 : ℝ)) * ((1 + |y + τ|) ^ 2)⁻¹ := by
        congr 1
        field_simp

/-- **The common factor on `−K ≤ Re s ≤ 1/2`**: `|H(s + iτ)N^sE(s)Φ(s)| ≤ C(1 + |y|)^{K+1}(1 + |y + τ|)^{−(K+5)}`. -/
lemma Cf_bound (χ : DirichletCharacter ℂ q) (τ : ℝ) {N : ℝ} (hN : 0 < N) {K : ℕ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-(K : ℝ)) (1 / 2), ∀ y : ℝ,
      ‖Cf χ τ N (x + y * I)‖ ≤ C * (1 + |y|) ^ (K + 1) * ((1 + |y + τ|) ^ (K + 5))⁻¹ := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  obtain ⟨B, hB0, hB⟩ := H_shift_bound (K + 2) (S := K) (by positivity)
  set f := χ.conductor with hfdef
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (χ.conductor_ne_zero)
  set PE : ℝ := ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (K : ℝ)) with hPE
  have hPE0 : 0 ≤ PE := Finset.prod_nonneg fun p _ => by positivity
  have hC := CGK_pos K
  have hEQ := EQh_pos q
  refine ⟨B * (N ^ (1 / 2 : ℝ) + N ^ (-(K : ℝ))) * PE * ((f : ℝ) ^ (1 / 2 + (K : ℝ)) * (Real.pi * CGK K) * EQh q),
    by positivity, fun x hx y => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  set s : ℂ := x + y * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hHb := hB x y τ (abs_le.2 ⟨by linarith, by linarith⟩)
  have hNb : ‖(N : ℂ) ^ s‖ ≤ N ^ (1 / 2 : ℝ) + N ^ (-(K : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN, hsre]
    exact rpow_le_add_ends hN hx1 hx2
  have hEb : ‖Eu χ.primitiveCharacter q s‖ ≤ PE := norm_Eu_le _ q (c := K) (by rw [hsre]; linarith)
  have hPb := norm_Phi_le_far χ.primitiveCharacter_isPrimitive q K (s := s) (by rw [hsre]; exact hx1)
    (by rw [hsre]; exact hx2)
  rw [hsre, hsim] at hPb
  have hf' : (f : ℝ) ^ (1 / 2 - x) ≤ (f : ℝ) ^ (1 / 2 + (K : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hf1 (by linarith)
  have hy1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hy' : (1 + |y|) ^ (1 / 2 - x) ≤ (1 + |y|) ^ (K + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (by push_cast; linarith)
  have hPb' : ‖Phi χ.primitiveCharacter q s‖ ≤
      (f : ℝ) ^ (1 / 2 + (K : ℝ)) * (Real.pi * CGK K) * EQh q * (1 + |y|) ^ (K + 1) := by
    refine hPb.trans ?_
    calc (f : ℝ) ^ (1 / 2 - x) * (Real.pi * CGK K * (1 + |y|) ^ (1 / 2 - x)) * EQh q
        ≤ (f : ℝ) ^ (1 / 2 + (K : ℝ)) * (Real.pi * CGK K * (1 + |y|) ^ (K + 1)) * EQh q := by gcongr
      _ = _ := by ring
  unfold Cf
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖H (s + τ * I)‖ * ‖(N : ℂ) ^ s‖ * ‖Eu χ.primitiveCharacter q s‖ * ‖Phi χ.primitiveCharacter q s‖
      ≤ (B * ((1 + |y + τ|) ^ (K + 2 + 3))⁻¹) * (N ^ (1 / 2 : ℝ) + N ^ (-(K : ℝ))) * PE *
          ((f : ℝ) ^ (1 / 2 + (K : ℝ)) * (Real.pi * CGK K) * EQh q * (1 + |y|) ^ (K + 1)) := by
        gcongr
    _ = B * (N ^ (1 / 2 : ℝ) + N ^ (-(K : ℝ))) * PE * ((f : ℝ) ^ (1 / 2 + (K : ℝ)) * (Real.pi * CGK K) * EQh q) *
          (1 + |y|) ^ (K + 1) * ((1 + |y + τ|) ^ (K + 5))⁻¹ := by ring_nf

/-- `|L(1 − s, χ⁻¹) − Σ_{m≤Z}χ⁻¹(m)m^{s−1}| ≤ (2(q + 1)(K + 1) + Z)(1 + |Im s|)` on `−K ≤ Re s ≤ 1/2`. -/
lemma rest_factor_bound {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (Z K : ℕ) {x y : ℝ} (hx1 : -(K : ℝ) ≤ x)
    (hx2 : x ≤ 1 / 2) :
    ‖LFunction χ⁻¹ (1 - (x + y * I)) - dualS χ⁻¹ Z (x + y * I)‖ ≤
      (2 * ((q : ℝ) + 1) * (K + 1) + Z) * (1 + |y|) := by
  set s : ℂ := x + y * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hre : (1 - s).re = 1 - x := by simp [hsre]
  have hL := PsiOmega.norm_LFunction_leC (inv_ne_one.2 hχ) (s := 1 - s) (by rw [hre]; linarith)
  rw [hre] at hL
  have hn : ‖1 - s‖ ≤ 1 + K + |y| := by
    calc ‖1 - s‖ ≤ |(1 - s).re| + |(1 - s).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |1 - x| + |y| := by rw [hre]; simp [hsim]
      _ ≤ 1 + K + |y| := by rw [abs_of_pos (by linarith)]; linarith
  have hL' : ‖LFunction χ⁻¹ (1 - s)‖ ≤ 2 * ((q : ℝ) + 1) * (K + 1) * (1 + |y|) := by
    calc ‖LFunction χ⁻¹ (1 - s)‖ ≤ ((q : ℝ) + 1) * ‖1 - s‖ / (1 - x) := hL
      _ ≤ ((q : ℝ) + 1) * (1 + K + |y|) / (1 / 2) := by
          have : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
          gcongr
          linarith
      _ ≤ 2 * ((q : ℝ) + 1) * (K + 1) * (1 + |y|) := by
          have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
          have : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
          rw [div_eq_mul_inv, show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num]
          nlinarith [abs_nonneg y, mul_nonneg this (abs_nonneg y), mul_nonneg (mul_nonneg this hK0) (abs_nonneg y)]
  have hS := norm_dualS_le χ⁻¹ Z (s := s) (by rw [hsre]; linarith)
  have hy1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  calc ‖LFunction χ⁻¹ (1 - s) - dualS χ⁻¹ Z s‖ ≤ ‖LFunction χ⁻¹ (1 - s)‖ + ‖dualS χ⁻¹ Z s‖ := norm_sub_le _ _
    _ ≤ 2 * ((q : ℝ) + 1) * (K + 1) * (1 + |y|) + Z * (1 + |y|) := by
        have : (Z : ℝ) ≤ Z * (1 + |y|) := le_mul_of_one_le_right (Nat.cast_nonneg Z) hy1
        linarith
    _ = (2 * ((q : ℝ) + 1) * (K + 1) + Z) * (1 + |y|) := by ring

/-- **The rest on `−K ≤ Re s ≤ 1/2`**: `|Rt(x + iy)| ≤ M(1 + |y + τ|)^{−2}`. -/
lemma Rt_bound {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {K : ℕ}
    (hK : 1 ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-(K : ℝ)) (1 / 2), ∀ y : ℝ,
      ‖Rt χ τ N Z (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := Cf_bound χ τ hN hK
  set D : ℝ := 2 * ((q : ℝ) + 1) * (K + 1) + Z with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨C * D * (1 + |τ|) ^ (K + 2), by positivity, fun x hx y => ?_⟩
  have hCb := hC x hx y
  have hRb := rest_factor_bound hχ Z K (y := y) hx.1 hx.2
  have hu : 0 < 1 + |y + τ| := by positivity
  have hu1 : 1 ≤ 1 + |y + τ| := by linarith [abs_nonneg (y + τ)]
  have hpoly : (1 + |y|) ^ (K + 2) ≤ (1 + |τ|) ^ (K + 2) * (1 + |y + τ|) ^ (K + 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (one_add_abs_le y τ) _
  unfold Rt
  rw [norm_mul]
  calc ‖Cf χ τ N (x + y * I)‖ * ‖LFunction χ⁻¹ (1 - (x + y * I)) - dualS χ⁻¹ Z (x + y * I)‖
      ≤ (C * (1 + |y|) ^ (K + 1) * ((1 + |y + τ|) ^ (K + 5))⁻¹) * (D * (1 + |y|)) :=
        mul_le_mul hCb hRb (norm_nonneg _) (by positivity)
    _ = C * D * (1 + |y|) ^ (K + 2) * ((1 + |y + τ|) ^ (K + 5))⁻¹ := by ring
    _ ≤ C * D * ((1 + |τ|) ^ (K + 2) * (1 + |y + τ|) ^ (K + 2)) * ((1 + |y + τ|) ^ (K + 5))⁻¹ := by gcongr
    _ = C * D * (1 + |τ|) ^ (K + 2) * ((1 + |y + τ|) ^ 3)⁻¹ := by
        field_simp
        ring
    _ ≤ C * D * (1 + |τ|) ^ (K + 2) * ((1 + |y + τ|) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ hu1 (by norm_num : 2 ≤ 3)))
          (by positivity)

/-- **The main part on `−K ≤ Re s ≤ 1/2`**: `|Mn(x + iy)| ≤ M(1 + |y + τ|)^{−2}`. -/
lemma Mn_bound (χ : DirichletCharacter ℂ q) (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-(K : ℝ)) (1 / 2), ∀ y : ℝ,
      ‖Mn χ τ N Z (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := Cf_bound χ τ hN hK
  refine ⟨C * Z * (1 + |τ|) ^ (K + 1), by positivity, fun x hx y => ?_⟩
  have hCb := hC x hx y
  have hS := norm_dualS_le χ⁻¹ Z (s := x + y * I) (by simp; linarith [hx.2])
  have hu1 : 1 ≤ 1 + |y + τ| := by linarith [abs_nonneg (y + τ)]
  have hpoly : (1 + |y|) ^ (K + 1) ≤ (1 + |τ|) ^ (K + 1) * (1 + |y + τ|) ^ (K + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (one_add_abs_le y τ) _
  unfold Mn
  rw [norm_mul]
  calc ‖Cf χ τ N (x + y * I)‖ * ‖dualS χ⁻¹ Z (x + y * I)‖
      ≤ (C * (1 + |y|) ^ (K + 1) * ((1 + |y + τ|) ^ (K + 5))⁻¹) * Z :=
        mul_le_mul hCb hS (norm_nonneg _) (by positivity)
    _ ≤ (C * ((1 + |τ|) ^ (K + 1) * (1 + |y + τ|) ^ (K + 1)) * ((1 + |y + τ|) ^ (K + 5))⁻¹) * Z := by gcongr
    _ = C * Z * (1 + |τ|) ^ (K + 1) * ((1 + |y + τ|) ^ 4)⁻¹ := by
        field_simp
        ring
    _ ≤ C * Z * (1 + |τ|) ^ (K + 1) * ((1 + |y + τ|) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ hu1 (by norm_num : 2 ≤ 4)))
          (by positivity)

/-! ### Differentiability -/

lemma differentiableAt_H_shift (τ : ℝ) (s : ℂ) : DifferentiableAt ℂ (fun s : ℂ => H (s + τ * I)) s :=
  differentiable_H.differentiableAt.comp s (differentiableAt_id.add_const _)

lemma differentiableAt_G1 {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (τ : ℝ) {N : ℝ} (hN : 0 < N) (s : ℂ) :
    DifferentiableAt ℂ (G1 χ τ N) s :=
  (((differentiable_LFunction hχ).differentiableAt).mul (differentiableAt_H_shift τ s)).mul
    (differentiable_cpow_const hN s)

lemma differentiableAt_Cf (χ : DirichletCharacter ℂ q) (τ : ℝ) {N : ℝ} (hN : 0 < N) {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (Cf χ τ N) s :=
  (((differentiableAt_H_shift τ s).mul (differentiable_cpow_const hN s)).mul
    (differentiable_Eu _ q s)).mul (differentiableAt_Phi _ q hs)

omit [NeZero q] in
lemma differentiableAt_dualS (χ : DirichletCharacter ℂ q) (Z : ℕ) (s : ℂ) : DifferentiableAt ℂ (dualS χ Z) s := by
  unfold dualS
  have : (fun s : ℂ => ∑ m ∈ Finset.Icc 1 Z, χ m * (m : ℂ) ^ (s - 1)) =
      fun s : ℂ => ∑ m ∈ Finset.Icc 1 Z, (fun s : ℂ => χ m * (m : ℂ) ^ (s - 1)) s := rfl
  rw [this]
  refine DifferentiableAt.fun_sum fun m hm => ?_
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (Finset.mem_Icc.1 hm).1; omega)
  exact (differentiableAt_const _).mul ((differentiableAt_id.sub_const 1).const_cpow (Or.inl hm0))

lemma differentiableAt_Rt {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {s : ℂ}
    (hs : s.re < 1) : DifferentiableAt ℂ (Rt χ τ N Z) s := by
  have hL : DifferentiableAt ℂ (fun s : ℂ => LFunction χ⁻¹ (1 - s)) s :=
    (differentiable_LFunction (inv_ne_one.2 hχ)).differentiableAt.comp s
      ((differentiableAt_const _).sub differentiableAt_id)
  exact (differentiableAt_Cf χ τ hN hs).mul (hL.sub (differentiableAt_dualS χ⁻¹ Z s))

lemma differentiableAt_Mn (χ : DirichletCharacter ℂ q) (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {s : ℂ}
    (hs : s.re < 1) : DifferentiableAt ℂ (Mn χ τ N Z) s :=
  (differentiableAt_Cf χ τ hN hs).mul (differentiableAt_dualS χ⁻¹ Z s)

/-- Continuity on a line from differentiability there. -/
lemma continuous_line {G : ℂ → ℂ} {x : ℝ} (h : ∀ y : ℝ, DifferentiableAt ℂ G (x + y * I)) :
    Continuous fun y : ℝ => G (x + y * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hinner : ContinuousAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) y := by fun_prop
  exact ContinuousAt.comp (g := G) (h y).continuousAt hinner

/-! ### The reflection -/

/-- **The reflection of the Perron integral**: for `χ ≠ 1`, `N > 0`, `Z ≥ 0` and `K ≥ 1`,
`∫_{(2)} L(s, χ)H(s + iτ)N^s = ∫_{(1/2)} H(s + iτ)N^sE(s)Φ(s)Σ_{m≤Z}χ⁻¹(m)m^{s−1}
+ ∫_{(−K)} H(s + iτ)N^sE(s)Φ(s)Σ_{m>Z}χ⁻¹(m)m^{s−1}`, the integrals over `v` with `s = σ + iv`. -/
theorem reflect_gram {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) {K : ℕ}
    (hK : 1 ≤ K) :
    ∫ v : ℝ, G1 χ τ N ((2 : ℝ) + v * I) =
      (∫ v : ℝ, Mn χ τ N Z ((1 / 2 : ℝ) + v * I)) + ∫ v : ℝ, Tl χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  -- the shift from `2` to `1/2`
  obtain ⟨M₁, hM₁, hb₁⟩ := G1_bound hχ τ hN
  have h1 : ∫ v : ℝ, G1 χ τ N ((2 : ℝ) + v * I) = ∫ v : ℝ, G1 χ τ N ((1 / 2 : ℝ) + v * I) :=
    shift_of_bound (G := G1 χ τ N) (σ' := 1 / 2) (σ := 2) (by norm_num) hM₁
      (fun z _ _ => differentiableAt_G1 hχ τ hN z) hb₁
  -- the split on `Re s = 1/2`
  obtain ⟨M₂, hM₂, hb₂⟩ := Rt_bound hχ τ hN Z hK
  obtain ⟨M₃, hM₃, hb₃⟩ := Mn_bound χ τ hN Z hK
  have hhalf : (1 / 2 : ℝ) ∈ Icc (-(K : ℝ)) (1 / 2) := ⟨by linarith, le_rfl⟩
  have hre : ∀ v : ℝ, (((1 / 2 : ℝ) : ℂ) + v * I).re < 1 := fun v => by simp; norm_num
  have hRt_int : Integrable fun v : ℝ => Rt χ τ N Z ((1 / 2 : ℝ) + v * I) :=
    integrable_of_bound (continuous_line fun v => differentiableAt_Rt hχ τ hN Z (hre v)) (hb₂ _ hhalf)
  have hMn_int : Integrable fun v : ℝ => Mn χ τ N Z ((1 / 2 : ℝ) + v * I) :=
    integrable_of_bound (continuous_line fun v => differentiableAt_Mn χ τ hN Z (hre v)) (hb₃ _ hhalf)
  have h2 : ∫ v : ℝ, G1 χ τ N ((1 / 2 : ℝ) + v * I) =
      (∫ v : ℝ, Mn χ τ N Z ((1 / 2 : ℝ) + v * I)) + ∫ v : ℝ, Rt χ τ N Z ((1 / 2 : ℝ) + v * I) := by
    rw [← integral_add hMn_int hRt_int]
    exact integral_congr_ae (Eventually.of_forall fun v => G1_eq hχ τ N Z (hre v))
  -- the shift of the rest from `1/2` to `−K`
  have h3 : ∫ v : ℝ, Rt χ τ N Z ((1 / 2 : ℝ) + v * I) = ∫ v : ℝ, Rt χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I) :=
    shift_of_bound (G := Rt χ τ N Z) (σ' := -(K : ℝ)) (σ := 1 / 2) (by linarith) hM₂
      (fun z _ hz2 => differentiableAt_Rt hχ τ hN Z (by linarith)) hb₂
  -- on `Re s = −K` the rest is the tail
  have h4 : ∫ v : ℝ, Rt χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I) = ∫ v : ℝ, Tl χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I) :=
    integral_congr_ae (Eventually.of_forall fun v => Rt_eq_Tl χ τ N Z (by simp; linarith))
  rw [h1, h2, h3, h4]

/-- **The Gram entries reflected**: for `χ_i ≠ χ_k`, with `ψ = χ_iχ̄_k` and `τ = t_i − t_k`,
`G(i, k) = N^{iτ}(1/2π)(∫_{(1/2)} H(s + iτ)N^sE(s)Φ(s)Σ_{m≤Z}ψ⁻¹(m)m^{s−1}
+ ∫_{(−K)} H(s + iτ)N^sE(s)Φ(s)Σ_{m>Z}ψ⁻¹(m)m^{s−1})` (`LinnikCGLMellin.perron_gram` at `σ = 2`). -/
theorem gram_reflect {ι : Type*} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {i k : ι}
    (hik : χ i ≠ χ k) (Z : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    gramP N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * ((1 / (2 * π) : ℂ) *
      ((∫ v : ℝ, Mn (χ i * (χ k)⁻¹) (t i - t k) N Z ((1 / 2 : ℝ) + v * I)) +
        ∫ v : ℝ, Tl (χ i * (χ k)⁻¹) (t i - t k) N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I))) := by
  have hψ : χ i * (χ k)⁻¹ ≠ 1 := fun h => hik (mul_inv_eq_one.1 h)
  rw [perron_gram hN (σ := 2) (by norm_num) χ t i k, ← reflect_gram hψ (t i - t k) hN Z hK]
  rfl

end LinnikCGLReflect

#print axioms LinnikCGLReflect.norm_Gamma_half_ratio_far
#print axioms LinnikCGLReflect.norm_Phi_le_far
#print axioms LinnikCGLReflect.LFunction_reflected
#print axioms LinnikCGLReflect.shift_of_bound
#print axioms LinnikCGLReflect.reflect_gram
#print axioms LinnikCGLReflect.gram_reflect
