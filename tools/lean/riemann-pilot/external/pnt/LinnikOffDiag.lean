/-
# Round 525, part 2: `L(s, χ)` on the line `Re s = 1/12 − δ` and the off-diagonal sums

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For `0 < δ ≤ 1/24` and `ε′ > 0` there is `C` with `|L(1/12 − δ + it, χ)| ≤ C(q(|t| + 2))^{5/12+δ+2ε′}`
for every character `χ ≠ 1` modulo every `q ≥ 1` (`left_line`). For `ε′ ≤ 1/4` there is `C` with
`|Σ_{n≥1} ψ(n)n^{−z}e^{−n/Λ}| ≤ CΛ^{1/12−δ}(q(T′ + 2))^{5/12+δ+2ε′}` for every `ψ ≠ 1` mod `q`, `Λ ≥ 1`,
`0 ≤ Re z ≤ (1/12 − δ)/2` and `|Im z| ≤ T′` (`norm_offK_le`): the off-diagonal input `B` of
`LinnikPower.hm_duality`.

* `left_line_primitive`: for primitive `χ ≠ 1`, the functional equation (round 522's
  `LinnikFE.norm_LFunction_one_sub_le`) from `Re s = 11/12 + δ`, where `LinnikLindelof.lindelof` holds for `χ⁻¹`.
* `left_line`: the primitive character inducing `χ` and Mathlib's `LFunction_changeLevel`, with
  `∏_{p | q}(1 + p^{−(1/12−δ)}) ≤ 2^{⌈e^{1/ε′}⌉}q^{ε′}` (`prod_primeFactors_le'`).
* `kTerm_tsum_eq`: `Σ_{n≥1} ψ(n)n^{−z}e^{−n/Λ} = (1/2π)∫ L(z + c′ + iv, ψ)Γ(c′ + iv)Λ^{c′+iv} dv` for `0 < c′ ≤ 2`:
  round 520's `Linnik.perron_exp` on `Re w = 2`, moved to `Re w = c′` (`SmoothPerron.verticalIntegral_shift`).
* `norm_offK_le`: `kTerm_tsum_eq` on the line `Re(z + w) = 1/12 − δ`, `left_line` there and
  `|Γ(c′ + iv)|(1 + |v|)⁵ ≤ KG/c′` (`norm_Gamma_small`).
-/

import LinnikPower

open Complex Real Finset MeasureTheory Set

noncomputable section

namespace LinnikOffDiag

open DirichletCharacter

/-! ### `L(s, χ)` on the line `Re s = 1/12 − δ`, uniformly in the modulus -/

/-- `∏_{p | q}(1 + p^{−l}) ≤ 2^{⌈e^{1/ε}⌉}q^ε` for `l ≥ 0` (`LinnikSubconvex.prod_primeFactors_le` at a general
exponent). -/
theorem prod_primeFactors_le' {ε l : ℝ} (hε : 0 < ε) (hl : 0 ≤ l) {q : ℕ} (hq : q ≠ 0) :
    ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-l)) ≤ 2 ^ ⌈Real.exp (1 / ε)⌉₊ * (q : ℝ) ^ ε := by
  set X : ℝ := Real.exp (1 / ε) with hX
  have hfac : ∀ p ∈ q.primeFactors, 1 + (p : ℝ) ^ (-l) ≤ (if (p : ℝ) < X then (2 : ℝ) else 1) * (p : ℝ) ^ ε := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hp0 : (0 : ℝ) < p := by linarith
    have hl1 : (p : ℝ) ^ (-l) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    have hpe : (1 : ℝ) ≤ (p : ℝ) ^ ε := Real.one_le_rpow hp1 hε.le
    split_ifs with h
    · nlinarith
    · push Not at h
      have hlog : 1 / ε ≤ Real.log p := by
        rw [← Real.log_exp (1 / ε)]; exact Real.log_le_log (Real.exp_pos _) h
      have h1 : 1 ≤ ε * Real.log p := by
        have := mul_le_mul_of_nonneg_left hlog hε.le
        rwa [mul_one_div_cancel hε.ne'] at this
      have h2 : (p : ℝ) ^ ε = Real.exp (ε * Real.log p) := by
        rw [Real.rpow_def_of_pos hp0, mul_comm]
      have h3 : 2 ≤ (p : ℝ) ^ ε := by
        rw [h2]; linarith [Real.add_one_le_exp (ε * Real.log p)]
      linarith
  have h0 : ∀ p ∈ q.primeFactors, 0 ≤ 1 + (p : ℝ) ^ (-l) := fun p _ => by positivity
  refine (Finset.prod_le_prod₀ h0 hfac).trans ?_
  rw [Finset.prod_mul_distrib]
  have hcount : ∏ p ∈ q.primeFactors, (if (p : ℝ) < X then (2 : ℝ) else 1) ≤ 2 ^ ⌈X⌉₊ := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hsub : Finset.filter (fun p : ℕ => (p : ℝ) < X) q.primeFactors ⊆ Finset.range ⌈X⌉₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_range]
      exact_mod_cast hp.2.trans_le (Nat.le_ceil X)
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    exact pow_le_pow_right₀ (by norm_num) hc
  have hrad : ∏ p ∈ q.primeFactors, (p : ℝ) ^ ε ≤ (q : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  calc (∏ p ∈ q.primeFactors, (if (p : ℝ) < X then (2 : ℝ) else 1)) * ∏ p ∈ q.primeFactors, (p : ℝ) ^ ε
      ≤ 2 ^ ⌈X⌉₊ * (q : ℝ) ^ ε := mul_le_mul hcount hrad (Finset.prod_nonneg fun p _ => by positivity)
        (by positivity)

/-- **The left line for primitive characters**: for `0 < δ ≤ 1/24` and `ε′ > 0` there is `C` with
`|L(1/12 − δ + it, χ)| ≤ C(N(|t| + 2))^{5/12+δ+ε′}` for every primitive `χ ≠ 1` modulo every `N`: the functional
equation (`LinnikFE.norm_LFunction_one_sub_le`) from the line `Re s = 11/12 + δ`, where round 522's Lindelöf bound
(`LinnikLindelof.lindelof`) holds for `χ⁻¹`. -/
theorem left_line_primitive {δ ε' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hε' : 0 < ε') :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ t : ℝ, ‖LFunction χ (((1 / 12 - δ : ℝ) : ℂ) + t * I)‖ ≤ C * ((N : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + ε') := by
  set u : ℝ := 11 / 12 + δ with hu
  have hu1 : u < 1 := by linarith
  obtain ⟨C₂, hC₂0, hL⟩ := LinnikLindelof.lindelof (σ₀ := u) (by linarith) hε'
  refine ⟨6 * Real.exp (4 * (u - 1 / 2)) * C₂ * 6 ^ ε', by positivity, fun N _ χ hprim hχ t => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ
  have e : ((1 / 12 - δ : ℝ) : ℂ) + t * I = 1 - ((u : ℂ) + (-t : ℝ) * I) := by rw [hu]; push_cast; ring
  rw [e]
  refine (LinnikFE.norm_LFunction_one_sub_le hprim (by linarith) hu1 (-t)).trans ?_
  have hn : ‖(u : ℂ) + (-t : ℝ) * I‖ ≤ 1 + |t| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < u)]
    linarith
  have hpow : (Real.exp 4 * ‖(u : ℂ) + (-t : ℝ) * I‖) ^ (u - 1 / 2) ≤
      Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2) := by
    calc (Real.exp 4 * ‖(u : ℂ) + (-t : ℝ) * I‖) ^ (u - 1 / 2)
        ≤ (Real.exp 4 * (1 + |t|)) ^ (u - 1 / 2) :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hn (Real.exp_pos 4).le) (by linarith)
      _ = Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2) := by
          rw [Real.mul_rpow (Real.exp_pos 4).le (by positivity), ← Real.exp_mul]
  have hr := (hL N χ⁻¹ hχi u (-t) le_rfl).1
  rw [abs_neg] at hr
  have hbase : ((N : ℝ) + 2) * (|t| + 4) ≤ 6 * ((N : ℝ) * (|t| + 2)) := by nlinarith [abs_nonneg t]
  have hr' : ‖LFunction χ⁻¹ ((u : ℂ) + (-t : ℝ) * I)‖ ≤ C₂ * 6 ^ ε' * ((N : ℝ) * (|t| + 2)) ^ ε' := by
    refine hr.trans ?_
    calc C₂ * (((N : ℝ) + 2) * (|t| + 4)) ^ ε' ≤ C₂ * (6 * ((N : ℝ) * (|t| + 2))) ^ ε' := by
          gcongr
      _ = C₂ * 6 ^ ε' * ((N : ℝ) * (|t| + 2)) ^ ε' := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  have hNt : (N : ℝ) ^ (u - 1 / 2) * (1 + |t|) ^ (u - 1 / 2) ≤ ((N : ℝ) * (|t| + 2)) ^ (u - 1 / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      (by linarith)
  have hsplit : ((N : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + ε') =
      ((N : ℝ) * (|t| + 2)) ^ (u - 1 / 2) * ((N : ℝ) * (|t| + 2)) ^ ε' := by
    rw [← Real.rpow_add (by positivity)]; congr 1; rw [hu]; ring
  have hNp : 0 ≤ (N : ℝ) ^ (u - 1 / 2) := by positivity
  calc 6 * (N : ℝ) ^ (u - 1 / 2) * (Real.exp 4 * ‖(u : ℂ) + (-t : ℝ) * I‖) ^ (u - 1 / 2)
        * ‖LFunction χ⁻¹ ((u : ℂ) + (-t : ℝ) * I)‖
      ≤ 6 * (N : ℝ) ^ (u - 1 / 2) * (Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2))
        * (C₂ * 6 ^ ε' * ((N : ℝ) * (|t| + 2)) ^ ε') := by gcongr
    _ = 6 * Real.exp (4 * (u - 1 / 2)) * C₂ * 6 ^ ε' *
        (((N : ℝ) ^ (u - 1 / 2) * (1 + |t|) ^ (u - 1 / 2)) * ((N : ℝ) * (|t| + 2)) ^ ε') := by ring
    _ ≤ 6 * Real.exp (4 * (u - 1 / 2)) * C₂ * 6 ^ ε' *
        (((N : ℝ) * (|t| + 2)) ^ (u - 1 / 2) * ((N : ℝ) * (|t| + 2)) ^ ε') := by gcongr
    _ = 6 * Real.exp (4 * (u - 1 / 2)) * C₂ * 6 ^ ε' * ((N : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + ε') := by
        rw [hsplit]

/-- **The left line for every character `χ ≠ 1`, uniformly in the modulus**: `|L(1/12 − δ + it, χ)| ≤
C(q(|t| + 2))^{5/12+δ+2ε′}`. The character is induced by its primitive character `χ* ≠ 1` mod the conductor, and
`L(s, χ) = L(s, χ*)∏_{p | q}(1 − χ*(p)p^{−s})` (Mathlib's `LFunction_changeLevel`); the product is at most
`∏_{p | q}(1 + p^{−(1/12−δ)})` (`prod_primeFactors_le'`). -/
theorem left_line {δ ε' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hε' : 0 < ε') :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ t : ℝ, ‖LFunction χ (((1 / 12 - δ : ℝ) : ℂ) + t * I)‖ ≤ C * ((q : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + 2 * ε') := by
  obtain ⟨C, hC0, hC⟩ := left_line_primitive hδ hδ1 hε'
  refine ⟨C * 2 ^ ⌈Real.exp (1 / ε')⌉₊, by positivity, fun q _ χ hχ t => ?_⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χ' := χ.primitiveCharacter with hχ'def
  have hprim : χ'.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hχ' : χ' ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, ← hχ'def, h, changeLevel_one]
  set l : ℝ := 1 / 12 - δ with hl
  have hl0 : 0 ≤ l := by rw [hl]; linarith
  set s : ℂ := (l : ℂ) + t * I with hs
  have hsre : s.re = l := by simp [hs]
  have hL : LFunction χ s = LFunction χ' s * ∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-s)) := by
    have h := LFunction_changeLevel χ.conductor_dvd_level χ' (s := s) (Or.inl hχ')
    rwa [hχ'def, χ.changeLevel_primitiveCharacter] at h
  have hfac : ∀ p ∈ q.primeFactors, ‖1 - χ' p * (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-l) := by
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, hsre]
    have := DirichletCharacter.norm_le_one χ' p
    have hp' : 0 ≤ (p : ℝ) ^ (-l) := by positivity
    nlinarith
  have hprod : ‖∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-s))‖ ≤
      2 ^ ⌈Real.exp (1 / ε')⌉₊ * (q : ℝ) ^ ε' := by
    rw [norm_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfac).trans
      (prod_primeFactors_le' hε' hl0 (NeZero.ne q))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hprimb := hC χ.conductor χ' hprim hχ' t
  have hmono : ((χ.conductor : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + ε') ≤ ((q : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + ε') :=
    Real.rpow_le_rpow (by positivity)
      (by gcongr; exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level)
      (by linarith)
  have hqε : (q : ℝ) ^ ε' ≤ ((q : ℝ) * (|t| + 2)) ^ ε' :=
    Real.rpow_le_rpow (by positivity) (le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg t]))
      hε'.le
  have h2 : (0 : ℝ) ≤ 2 ^ ⌈Real.exp (1 / ε')⌉₊ := by positivity
  rw [hL, norm_mul]
  calc ‖LFunction χ' s‖ * ‖∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-s))‖
      ≤ (C * ((q : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + ε')) *
          (2 ^ ⌈Real.exp (1 / ε')⌉₊ * ((q : ℝ) * (|t| + 2)) ^ ε') := by
        gcongr
        · exact hprimb.trans (mul_le_mul_of_nonneg_left hmono hC0.le)
        · exact hprod.trans (mul_le_mul_of_nonneg_left hqε h2)
    _ = C * 2 ^ ⌈Real.exp (1 / ε')⌉₊ * ((q : ℝ) * (|t| + 2)) ^ (5 / 12 + δ + 2 * ε') := by
        rw [show (5 / 12 + δ + 2 * ε' : ℝ) = (5 / 12 + δ + ε') + ε' by ring,
          Real.rpow_add (by positivity) (5 / 12 + δ + ε') ε']
        ring

end LinnikOffDiag

namespace LinnikOffDiag

open DirichletCharacter InghamDensity LinnikPower

variable {q : ℕ} [NeZero q]

/-! ### The weighted twisted sum by Mellin inversion -/

/-- The integrand `L(z + w, ψ)Γ(w)Λ^w`. -/
def offG (ψ : DirichletCharacter ℂ q) (Λ : ℝ) (z w : ℂ) : ℂ :=
  LFunction ψ (z + w) * Complex.Gamma w * (Λ : ℂ) ^ w

omit [NeZero q] in
lemma kTerm_eq (ψ : DirichletCharacter ℂ q) (Λ : ℝ) (z : ℂ) (n : ℕ) :
    kTerm ψ Λ z n = (if n = 0 then 0 else ψ n * (n : ℂ) ^ (-z)) * (Real.exp (-((n : ℝ) / Λ)) : ℂ) := by
  unfold kTerm; split_ifs <;> simp

omit [NeZero q] in
lemma term_twist (ψ : DirichletCharacter ℂ q) (z w : ℂ) (n : ℕ) :
    LSeries.term (fun n => if n = 0 then 0 else ψ n * (n : ℂ) ^ (-z)) w n
      = LSeries.term (fun n => ψ n) (z + w) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, ite_eq_right hn]
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [Complex.cpow_add _ _ hn', Complex.cpow_neg]
    field_simp

/-- **The strip bound**: `|L(z + w, ψ)Γ(w)Λ^w|(1 + |Im w|)³` is bounded on `c′ ≤ Re w ≤ 2` for `0 ≤ Re z ≤ 1`
and `c′ > 0`. -/
lemma offG_strip_bound {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 1 ≤ Λ) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 1) {c' : ℝ} (hc' : 0 < c') :
    ∃ K : ℝ, ∀ w : ℂ, c' ≤ w.re → w.re ≤ 2 → ‖offG ψ Λ z w‖ * (1 + |w.im|) ^ 3 ≤ K := by
  set A : ℝ := max 3 (1 / c') * ((q : ℝ) + 1) * (|z.im| + 2) with hA
  refine ⟨A * (KG / c') * Λ ^ (2 : ℝ), fun w hw1 hw2 => ?_⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hwre : 0 < w.re := hc'.trans_le hw1
  -- `|L(z + w)| ≤ A(1 + |Im w|)`
  have hL : ‖LFunction ψ (z + w)‖ ≤ A * (1 + |w.im|) := by
    have him : |(z + w).im| ≤ |z.im| + |w.im| := by simp only [add_im]; exact abs_add_le _ _
    have hgrow : (|z.im| + |w.im| + 2) ≤ (|z.im| + 2) * (1 + |w.im|) := by
      nlinarith [abs_nonneg z.im, abs_nonneg w.im]
    rcases le_or_gt (1 / 2) (z + w).re with h | h
    · have h3 : (z + w).re ≤ 3 := by simp only [add_re]; linarith
      refine (Linnik.LFunction_growth hψ h h3).trans ?_
      calc 3 * ((q : ℝ) + 1) * (|(z + w).im| + 2) ≤ 3 * ((q : ℝ) + 1) * (|z.im| + |w.im| + 2) := by
            gcongr
        _ ≤ max 3 (1 / c') * ((q : ℝ) + 1) * ((|z.im| + 2) * (1 + |w.im|)) := by
            gcongr; exact le_max_left _ _
        _ = A * (1 + |w.im|) := by rw [hA]; ring
    · have hl : c' ≤ (z + w).re := by simp only [add_re]; linarith
      refine (LinnikSubconvex.norm_LFunction_strip_le hψ hc' hl (by linarith)).trans ?_
      calc ((q : ℝ) + 1) / c' * (1 + |(z + w).im|) ≤ ((q : ℝ) + 1) / c' * (|z.im| + |w.im| + 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 1 / c' * ((q : ℝ) + 1) * (|z.im| + |w.im| + 2) := by ring
        _ ≤ max 3 (1 / c') * ((q : ℝ) + 1) * ((|z.im| + 2) * (1 + |w.im|)) := by
            gcongr; exact le_max_right _ _
        _ = A * (1 + |w.im|) := by rw [hA]; ring
  -- `|Γ(w)|(1 + |Im w|)⁵ ≤ KG/c′`
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre
  have hG : ‖Complex.Gamma w‖ * (1 + |w.im|) ^ 5 ≤ KG / c' := by
    have h := norm_Gamma_le' (z := w + 1) (by simp; linarith) (by simp; linarith)
    have hGim : (w + 1).im = w.im := by simp
    rw [hGim] at h
    have hwn : c' ≤ ‖w‖ := hw1.trans (Complex.re_le_norm w)
    rw [show Complex.Gamma w = Complex.Gamma (w + 1) / w by
      rw [Complex.Gamma_add_one w hw0]; field_simp, norm_div]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hc']
    calc ‖Complex.Gamma (w + 1)‖ * (1 + |w.im|) ^ 5 * c' ≤ KG * ‖w‖ := by
          have := mul_le_mul h hwn hc'.le KG_pos.le
          linarith
      _ = KG * ‖w‖ := rfl
  have hΛw : ‖(Λ : ℂ) ^ w‖ ≤ Λ ^ (2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hΛ hw2
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  unfold offG
  rw [norm_mul, norm_mul]
  have h1 : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
  calc ‖LFunction ψ (z + w)‖ * ‖Complex.Gamma w‖ * ‖(Λ : ℂ) ^ w‖ * (1 + |w.im|) ^ 3
      ≤ (A * (1 + |w.im|)) * ‖Complex.Gamma w‖ * Λ ^ (2 : ℝ) * (1 + |w.im|) ^ 3 := by gcongr
    _ = A * Λ ^ (2 : ℝ) * (‖Complex.Gamma w‖ * (1 + |w.im|) ^ 5) / (1 + |w.im|) := by
        field_simp
    _ ≤ A * Λ ^ (2 : ℝ) * (KG / c') / (1 + |w.im|) := by
        have hAL : 0 ≤ A * Λ ^ (2 : ℝ) := mul_nonneg hA0 (by positivity)
        gcongr
    _ ≤ A * Λ ^ (2 : ℝ) * (KG / c') / 1 := by
        apply div_le_div_of_nonneg_left _ one_pos h1
        exact mul_nonneg (mul_nonneg hA0 (by positivity)) (div_nonneg KG_pos.le hc'.le)
    _ = A * (KG / c') * Λ ^ (2 : ℝ) := by ring

lemma norm_Gamma_small {w : ℂ} {c' : ℝ} (hc' : 0 < c') (hw1 : c' ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖Complex.Gamma w‖ * (1 + |w.im|) ^ 5 ≤ KG / c' := by
  have hwre : 0 < w.re := hc'.trans_le hw1
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre
  have h := norm_Gamma_le' (z := w + 1) (by simp; linarith) (by simp; linarith)
  have hGim : (w + 1).im = w.im := by simp
  rw [hGim] at h
  have hwn : c' ≤ ‖w‖ := hw1.trans (Complex.re_le_norm w)
  rw [show Complex.Gamma w = Complex.Gamma (w + 1) / w by
    rw [Complex.Gamma_add_one w hw0]; field_simp, norm_div]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hc']
  have := mul_le_mul h hwn hc'.le KG_pos.le
  linarith

lemma differentiableAt_offG {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 0 < Λ) (z : ℂ) {w : ℂ}
    (hw : 0 < w.re) : DifferentiableAt ℂ (offG ψ Λ z) w := by
  have h1 : DifferentiableAt ℂ (fun w => LFunction ψ (z + w)) w :=
    (differentiable_LFunction hψ).differentiableAt.comp w (by fun_prop)
  have h2 : DifferentiableAt ℂ Complex.Gamma w := by
    refine Complex.differentiableAt_Gamma _ fun m h => ?_
    have := congrArg Complex.re h
    simp only [neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h3 : DifferentiableAt ℂ (fun w : ℂ => (Λ : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.2 hΛ.ne'))
  exact (h1.mul h2).mul h3

/-- **Mellin inversion, moved to a line left of `1`**: for `ψ ≠ 1`, `0 ≤ Re z ≤ 1`, `Λ ≥ 1` and `0 < c′ ≤ 2`,
`Σ_{n≥1} ψ(n)n^{−z}e^{−n/Λ} = (1/2π)∫ L(z + c′ + iv, ψ)Γ(c′ + iv)Λ^{c′+iv} dv`: round 520's `Linnik.perron_exp`
on `Re w = 2`, then the line moves to `Re w = c′` (`SmoothPerron.verticalIntegral_shift`); the integrand has no pole
on `Re w > 0` since `L(·, ψ)` is entire. -/
theorem kTerm_tsum_eq {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {Λ : ℝ} (hΛ : 1 ≤ Λ) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 1) {c' : ℝ} (hc' : 0 < c') (hc'2 : c' ≤ 2) :
    ∑' n, kTerm ψ Λ z n = (1 / (2 * π) : ℂ) * ∫ v : ℝ, offG ψ Λ z (c' + v * I) := by
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨K, hK⟩ := offG_strip_bound hψ hΛ hz0 hz1 hc'
  set a : ℕ → ℂ := fun n => if n = 0 then 0 else ψ n * (n : ℂ) ^ (-z) with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have hsum2 : LSeriesSummable a ((2 : ℝ) : ℂ) := by
    have h := ZMod.LSeriesSummable_of_one_lt_re (fun n => ψ n) (s := z + ((2 : ℝ) : ℂ)) (by simp; linarith)
    unfold LSeriesSummable at h ⊢
    have e : LSeries.term a ((2 : ℝ) : ℂ) = LSeries.term (fun n => ψ n) (z + ((2 : ℝ) : ℂ)) :=
      funext fun n => term_twist ψ z _ n
    rw [e]; exact h
  have hp := Linnik.perron_exp ha0 (c := 2) (by norm_num) (by norm_num) hΛ0 hsum2
  have hleft : ∑' n, kTerm ψ Λ z n = ∑' n, a n * (Real.exp (-((n : ℝ) / Λ)) : ℂ) := by
    congr 1; funext n; rw [kTerm_eq]
  rw [hleft, hp]
  have hright : ∀ t : ℝ, LSeries a ((2 : ℝ) + t * I) * Complex.Gamma ((2 : ℝ) + t * I) * (Λ : ℂ) ^ ((2 : ℝ) + t * I)
      = offG ψ Λ z (((2 : ℝ) : ℂ) + t * I) := by
    intro t
    have hL : LSeries a ((2 : ℝ) + t * I) = LFunction ψ (z + ((2 : ℝ) + t * I)) := by
      rw [LFunction_eq_LSeries ψ (by simp; linarith)]
      unfold LSeries; congr 1; funext n; exact term_twist ψ z _ n
    rw [hL]; rfl
  simp_rw [hright]
  have hcont : ∀ σ : ℝ, 0 < σ → Continuous fun t : ℝ => offG ψ Λ z (σ + t * I) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (g := offG ψ Λ z) (f := fun t : ℝ => (σ : ℂ) + t * I)
      (differentiableAt_offG hψ hΛ0 z (by simpa using hσ)).continuousAt (by fun_prop)
  have hint : ∀ σ : ℝ, c' ≤ σ → σ ≤ 2 → MeasureTheory.Integrable fun t : ℝ => offG ψ Λ z (σ + t * I) := by
    intro σ h1 h2
    refine integrable_of_le_sq (hcont σ (hc'.trans_le h1)) (K := K) fun t => ?_
    have h := hK (σ + t * I) (by simpa using h1) (by simpa using h2)
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rw [him] at h
    have h23 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 3 := pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
    calc ‖offG ψ Λ z (σ + t * I)‖ * (1 + |t|) ^ 2 ≤ ‖offG ψ Λ z (σ + t * I)‖ * (1 + |t|) ^ 3 := by gcongr
      _ ≤ K := h
  have hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc c' 2, ∀ y : ℝ, T₀ ≤ |y| → ‖offG ψ Λ z (x + y * I)‖ ≤ η := by
    intro η hη
    refine ⟨K / η, fun x hx y hy => ?_⟩
    have hb := hK (x + y * I) (by simpa using hx.1) (by simpa using hx.2)
    have him : ((x : ℂ) + y * I).im = y := by simp
    rw [him] at hb
    have hpos : 0 < 1 + |y| := by positivity
    have h3 : 1 + |y| ≤ (1 + |y|) ^ 3 := le_self_pow₀ (by linarith [abs_nonneg y]) (by norm_num)
    have hKη : K ≤ η * |y| := by rwa [div_le_iff₀ hη, mul_comm] at hy
    have hG0 := norm_nonneg (offG ψ Λ z (x + y * I))
    have : ‖offG ψ Λ z (x + y * I)‖ * (1 + |y|) ≤ η * (1 + |y|) := by
      nlinarith [mul_le_mul_of_nonneg_left h3 hG0]
    exact le_of_mul_le_mul_right this hpos
  have hhol : HolomorphicOn (offG ψ Λ z) (Icc c' 2 ×ℂ univ) := by
    intro w hw
    rw [mem_reProdIm] at hw
    exact (differentiableAt_offG hψ hΛ0 z (by linarith [hw.1.1])).differentiableWithinAt
  have hshift := SmoothPerron.verticalIntegral_shift (G := offG ψ Λ z) (σ' := c') (σ := 2) hc'2 hhol
    (hint 2 hc'2 le_rfl) (hint c' le_rfl hc'2) hdecay
  simp only [VerticalIntegral] at hshift
  congr 1
  exact smul_right_injective ℂ I_ne_zero hshift

/-- **The off-diagonal bound**: for `0 < δ ≤ 1/24` and `0 < ε′ ≤ 1/4` there is `C` with
`|Σ_{n≥1} ψ(n)n^{−z}e^{−n/Λ}| ≤ CΛ^{1/12−δ}(q(T′ + 2))^{5/12+δ+2ε′}` for every `ψ ≠ 1` mod `q`, `Λ ≥ 1` and
`0 ≤ Re z ≤ (1/12 − δ)/2`, `|Im z| ≤ T′`: `kTerm_tsum_eq` on the line `Re(z + w) = 1/12 − δ`, with `left_line` there and
`|Γ(c′ + iv)|(1 + |v|)⁵ ≤ KG/c′`. -/
theorem norm_offK_le {δ ε' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hε' : 0 < ε') (hε'1 : ε' ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ Λ : ℝ, 1 ≤ Λ →
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ (1 / 12 - δ) / 2 → ∀ T' : ℝ, |z.im| ≤ T' →
        ‖∑' n, kTerm ψ Λ z n‖ ≤ C * Λ ^ (1 / 12 - δ) * ((q : ℝ) * (T' + 2)) ^ (5 / 12 + δ + 2 * ε') := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := left_line hδ hδ1 hε'
  refine ⟨C₁ * (24 * KG), by have := KG_pos; positivity, fun q _ ψ hψ Λ hΛ z hz0 hz1 T' hT' => ?_⟩
  set l : ℝ := 1 / 12 - δ with hl
  have hl0 : 1 / 24 ≤ l := by rw [hl]; linarith
  set c' : ℝ := l - z.re with hc'
  have hc'0 : l / 2 ≤ c' := by rw [hc']; linarith
  have hc'pos : 0 < c' := by linarith
  have hc'l : c' ≤ l := by rw [hc']; linarith
  have hc'2 : c' ≤ 2 := by linarith
  have hT'0 : 0 ≤ T' := (abs_nonneg _).trans hT'
  set e : ℝ := 5 / 12 + δ + 2 * ε' with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  have he1 : e ≤ 1 := by rw [he]; linarith
  set M : ℝ := C₁ * ((q : ℝ) * (T' + 2)) ^ e * (KG / c') * Λ ^ l with hM
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hKG := KG_pos
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  rw [kTerm_tsum_eq hψ hΛ hz0 (by linarith) hc'pos hc'2]
  -- the integrand on the line
  have hpt : ∀ v : ℝ, ‖offG ψ Λ z (c' + v * I)‖ ≤ M * (1 + v ^ 2)⁻¹ := by
    intro v
    have hsum : z + ((c' : ℂ) + v * I) = ((l : ℝ) : ℂ) + ((z.im + v : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hc']
    have hLb := hC₁ q ψ hψ (z.im + v)
    have hbase : (q : ℝ) * (|z.im + v| + 2) ≤ (q : ℝ) * (T' + 2) * (1 + |v|) := by
      have h1 := abs_add_le z.im v
      have : |z.im + v| + 2 ≤ (T' + 2) * (1 + |v|) := by nlinarith [abs_nonneg v]
      calc (q : ℝ) * (|z.im + v| + 2) ≤ q * ((T' + 2) * (1 + |v|)) := by gcongr
        _ = _ := by ring
    have hLv : ‖LFunction ψ (z + ((c' : ℂ) + v * I))‖ ≤ C₁ * ((q : ℝ) * (T' + 2)) ^ e * (1 + |v|) := by
      rw [hsum]
      refine hLb.trans ?_
      calc C₁ * ((q : ℝ) * (|z.im + v| + 2)) ^ e ≤ C₁ * ((q : ℝ) * (T' + 2) * (1 + |v|)) ^ e := by
            gcongr
        _ = C₁ * ((q : ℝ) * (T' + 2)) ^ e * (1 + |v|) ^ e := by
            rw [Real.mul_rpow (by positivity) (by positivity)]; ring
        _ ≤ C₁ * ((q : ℝ) * (T' + 2)) ^ e * (1 + |v|) := by
            gcongr
            calc (1 + |v|) ^ e ≤ (1 + |v|) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) he1
              _ = 1 + |v| := Real.rpow_one _
    have hGv := norm_Gamma_small (w := (c' : ℂ) + v * I) hc'pos (by simp) (by simp; linarith)
    have him : ((c' : ℂ) + v * I).im = v := by simp
    rw [him] at hGv
    have hΛv : ‖(Λ : ℂ) ^ ((c' : ℂ) + v * I)‖ ≤ Λ ^ l := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le hΛ hc'l
    have hv1 : 0 < 1 + |v| := by positivity
    have h4 : (1 + |v|) * (1 + v ^ 2) ≤ (1 + |v|) ^ 5 := by
      have hsq : 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v, sq_abs v]
      have h11 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
      calc (1 + |v|) * (1 + v ^ 2) ≤ (1 + |v|) * (1 + |v|) ^ 2 := by gcongr
        _ = (1 + |v|) ^ 3 := by ring
        _ ≤ (1 + |v|) ^ 5 := pow_le_pow_right₀ h11 (by norm_num)
    have hGv' : ‖Complex.Gamma ((c' : ℂ) + v * I)‖ ≤ KG / c' / (1 + |v|) ^ 5 := by
      rw [le_div_iff₀ (by positivity)]; exact hGv
    unfold offG
    rw [norm_mul, norm_mul]
    calc ‖LFunction ψ (z + ((c' : ℂ) + v * I))‖ * ‖Complex.Gamma ((c' : ℂ) + v * I)‖ *
          ‖(Λ : ℂ) ^ ((c' : ℂ) + v * I)‖
        ≤ (C₁ * ((q : ℝ) * (T' + 2)) ^ e * (1 + |v|)) * (KG / c' / (1 + |v|) ^ 5) * Λ ^ l := by gcongr
      _ = M * ((1 + |v|) / (1 + |v|) ^ 5) := by rw [hM]; field_simp
      _ ≤ M * (1 + v ^ 2)⁻¹ := by
          gcongr
          rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
          linarith
  -- integrate
  have hintn : MeasureTheory.Integrable fun v : ℝ => ‖offG ψ Λ z (c' + v * I)‖ := by
    refine MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul M)
      (by
        have hc : Continuous fun v : ℝ => offG ψ Λ z (c' + v * I) := by
          rw [continuous_iff_continuousAt]
          intro t
          exact ContinuousAt.comp (g := offG ψ Λ z) (f := fun t : ℝ => (c' : ℂ) + t * I)
            (differentiableAt_offG hψ (by linarith) z (by simpa using hc'pos)).continuousAt (by fun_prop)
        exact hc.norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun v => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt v)
  have hI : ‖∫ v : ℝ, offG ψ Λ z (c' + v * I)‖ ≤ M * π := by
    calc ‖∫ v : ℝ, offG ψ Λ z (c' + v * I)‖ ≤ ∫ v : ℝ, ‖offG ψ Λ z (c' + v * I)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, M * (1 + v ^ 2)⁻¹ :=
          MeasureTheory.integral_mono hintn (integrable_inv_one_add_sq.const_mul M) hpt
      _ = M * π := by rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hc2]
  have hpi : 0 < π := Real.pi_pos
  calc 1 / (2 * π) * ‖∫ v : ℝ, offG ψ Λ z (c' + v * I)‖ ≤ 1 / (2 * π) * (M * π) := by gcongr
    _ = M / 2 := by field_simp
    _ = C₁ * ((q : ℝ) * (T' + 2)) ^ e * (KG / c') * Λ ^ l / 2 := by rw [hM]
    _ ≤ C₁ * (24 * KG) * Λ ^ l * ((q : ℝ) * (T' + 2)) ^ e := by
        have hKc : KG / c' / 2 ≤ 24 * KG := by
          rw [div_div, div_le_iff₀ (by positivity)]
          nlinarith
        have hp : 0 ≤ C₁ * ((q : ℝ) * (T' + 2)) ^ e * Λ ^ l := by positivity
        calc C₁ * ((q : ℝ) * (T' + 2)) ^ e * (KG / c') * Λ ^ l / 2
            = C₁ * ((q : ℝ) * (T' + 2)) ^ e * Λ ^ l * (KG / c' / 2) := by ring
          _ ≤ C₁ * ((q : ℝ) * (T' + 2)) ^ e * Λ ^ l * (24 * KG) := by gcongr
          _ = C₁ * (24 * KG) * Λ ^ l * ((q : ℝ) * (T' + 2)) ^ e := by ring

end LinnikOffDiag

#print axioms LinnikOffDiag.left_line
#print axioms LinnikOffDiag.kTerm_tsum_eq
#print axioms LinnikOffDiag.norm_offK_le
