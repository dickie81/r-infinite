/-
# Round 522, part 3: `|L(1/2 + it, χ)| ≪ (q(|t| + 2))^{5/24+ε}` uniformly in `q`, and Linnik's exponent `17/6 + η`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `ε > 0` there is `C` such that `|L(1/2 + it, χ)| ≤ C(q(|t| + 2))^{5/24+ε}` for every
modulus `q ≥ 1`, every Dirichlet character `χ ≠ 1` mod `q` and every real `t`: round 521's `CritBoundχ (5/24 + ε)`
(`critBoundχ`). So every reduced class modulo every `q ≥ 1` has a prime `p ≤ K q^{17/6+η}` for every `η > 0`
(`linnik_seventeen_sixths`), with no hypothesis. Round 521's `linnik_four` had the exponent `4 + η`.

* `primitive_bound`: the bound for primitive `χ ≠ 1`. Part 2's Lindelöf bound on `Re s = u = 11/12 + δ` for `χ` and
  `χ⁻¹`; part 1's functional equation carries the latter to `Re s = 1 − u` with the factor
  `6N^{u−1/2}e^{4(u−1/2)}(1 + |t|)^{u−1/2}`; round 517's `Subconvexity.norm_le_interp_strip` interpolates at the
  midpoint `σ = 1/2`, where each edge carries the weight `1/2`, so the modulus enters as `N^{(u−1/2)/2+ε/2}`; the
  growth in the strip is round 254's `PsiOmega.norm_LFunction_leC` (`norm_LFunction_strip_le`).
* `prod_primeFactors_le`: `∏_{p | q}(1 + p^{−1/2}) ≤ 2^{⌈e^{1/ε}⌉}q^ε`.
* `critBoundχ`: a character `χ ≠ 1` mod `q` is induced by its primitive character `χ* ≠ 1` mod the conductor, and
  `L(s, χ) = L(s, χ*)∏_{p | q}(1 − χ*(p)p^{−s})` (Mathlib's `LFunction_changeLevel`).
* `linnik_seventeen_sixths`: round 521's `LinnikDensity.linnik_of_critBound` at `c = 5/24 + min(η, 1)/8`.
-/
import LinnikFE
import LinnikLindelof

open Complex Real Filter Topology Set

noncomputable section

namespace LinnikSubconvex

open DirichletCharacter

/-! ### Primitive characters -/

/-- `‖L(z, χ)‖ ≤ ((N + 1)/l)(1 + |Im z|)` on `l ≤ Re z ≤ 1`, `l > 0`, for `χ ≠ 1` (round 254's
`PsiOmega.norm_LFunction_leC`). -/
theorem norm_LFunction_strip_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {l : ℝ}
    (hl : 0 < l) {z : ℂ} (hz1 : l ≤ z.re) (hz2 : z.re ≤ 1) :
    ‖LFunction χ z‖ ≤ ((N : ℝ) + 1) / l * (1 + |z.im|) := by
  have hz0 : 0 < z.re := hl.trans_le hz1
  refine (PsiOmega.norm_LFunction_leC hχ hz0).trans ?_
  have hn : ‖z‖ ≤ 1 + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz0] at this
    linarith
  have hN : (0 : ℝ) ≤ N + 1 := by positivity
  calc ((N : ℝ) + 1) * ‖z‖ / z.re ≤ ((N : ℝ) + 1) * (1 + |z.im|) / l := by gcongr
    _ = ((N : ℝ) + 1) / l * (1 + |z.im|) := by ring

/-- **Subconvexity for primitive characters, uniformly in the modulus.** For every `ε > 0` there is `C` such that
for every modulus `N ≥ 1`, every primitive Dirichlet character `χ ≠ 1` mod `N` and every real `t`,
`|L(1/2 + it, χ)| ≤ C(N(|t| + 2))^{5/24 + ε}`. The proof takes the Lindelöf bound
`LinnikLindelof.lindelof` on `Re s = u = 11/12 + δ` for `χ` and `χ⁻¹`, carries the latter to `Re s = 1 − u` with
the factor `N^{u−1/2}(1 + |t|)^{u−1/2}` by the functional equation (`LinnikFE.norm_LFunction_one_sub_le`), and
interpolates at `σ = 1/2`, the midpoint, with `Subconvexity.norm_le_interp_strip`. -/
theorem primitive_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ t : ℝ, ‖LFunction χ (1 / 2 + t * I)‖ ≤ C * ((N : ℝ) * (|t| + 2)) ^ (5 / 24 + ε) := by
  set δ : ℝ := min ε (1 / 24) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 / 24 := min_le_right _ _
  set u : ℝ := 11 / 12 + δ with hu
  set l : ℝ := 1 - u with hl
  have hu1 : u < 1 := by linarith
  have hl0 : 0 < l := by linarith
  have hlu : l < u := by linarith
  set ε' : ℝ := ε / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨C₂, hC₂0, hL⟩ := LinnikLindelof.lindelof (σ₀ := u) (by linarith) hε'0
  set α : ℝ := u - 1 / 2 + ε' with hα
  have hα0 : 0 ≤ α := by linarith
  set c₀ : ℝ := 6 * Real.exp (4 * (u - 1 / 2)) with hc₀
  set E : ℝ := Real.exp (l ^ 2 + α ^ 2 / 4) * Real.exp (u ^ 2 + ε' ^ 2 / 4) with hE
  set D : ℝ := (c₀ * E * C₂ ^ 2 * (12 : ℝ) ^ (2 * ε')) ^ (1 / 2 : ℝ) with hD
  have hD0 : 0 < D := by positivity
  refine ⟨D, hD0, fun N _ χ hprim hχ t₀ => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ
  set B : ℝ := C₂ * (((N : ℝ) + 2) * 4) ^ ε' with hB
  have hB0 : 0 ≤ B := by positivity
  -- the right line, for `χ` and `χ⁻¹`
  have hright_of : ∀ ψ : DirichletCharacter ℂ N, ψ ≠ 1 → ∀ t : ℝ,
      ‖LFunction ψ (u + t * I)‖ ≤ B * (1 + |t|) ^ ε' := by
    intro ψ hψ t
    refine ((hL N ψ hψ u t le_rfl).1).trans ?_
    have h1 : ((N : ℝ) + 2) * (|t| + 4) ≤ ((N : ℝ) + 2) * 4 * (1 + |t|) := by nlinarith [abs_nonneg t]
    calc C₂ * (((N : ℝ) + 2) * (|t| + 4)) ^ ε' ≤ C₂ * (((N : ℝ) + 2) * 4 * (1 + |t|)) ^ ε' := by
          gcongr
      _ = B * (1 + |t|) ^ ε' := by
          rw [hB, Real.mul_rpow (by positivity) (by positivity)]; ring
  have hright := hright_of χ hχ
  -- the left line
  set A : ℝ := c₀ * (N : ℝ) ^ (u - 1 / 2) * B with hA
  have hleft : ∀ t : ℝ, ‖LFunction χ (l + t * I)‖ ≤ A * (1 + |t|) ^ α := by
    intro t
    have e : (l : ℂ) + t * I = 1 - ((u : ℂ) + (-t : ℝ) * I) := by rw [hl]; push_cast; ring
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
            Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hn (Real.exp_pos 4).le)
              (by linarith)
        _ = Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2) := by
            rw [Real.mul_rpow (Real.exp_pos 4).le (by positivity), ← Real.exp_mul]
    have hr := hright_of χ⁻¹ hχi (-t)
    rw [abs_neg] at hr
    have hNp : 0 ≤ (N : ℝ) ^ (u - 1 / 2) := by positivity
    calc 6 * (N : ℝ) ^ (u - 1 / 2) * (Real.exp 4 * ‖(u : ℂ) + (-t : ℝ) * I‖) ^ (u - 1 / 2) *
          ‖LFunction χ⁻¹ (u + (-t : ℝ) * I)‖
        ≤ 6 * (N : ℝ) ^ (u - 1 / 2) * (Real.exp (4 * (u - 1 / 2)) * (1 + |t|) ^ (u - 1 / 2)) *
          (B * (1 + |t|) ^ ε') := by gcongr
      _ = A * ((1 + |t|) ^ (u - 1 / 2) * (1 + |t|) ^ ε') := by rw [hA, hc₀]; ring
      _ = A * (1 + |t|) ^ α := by rw [← Real.rpow_add (by positivity)]
  -- polynomial growth in the strip
  have hgr : ∀ z : ℂ, z.re ∈ Icc l u →
      ‖LFunction χ z‖ ≤ ((N : ℝ) + 1) / l * (1 + |z.im|) ^ (1 : ℝ) := by
    intro z hz
    rw [Real.rpow_one]
    exact norm_LFunction_strip_le hχ hl0 hz.1 (by linarith [hz.2])
  have hdiff : DifferentiableOn ℂ (LFunction χ) (re ⁻¹' Icc l u) :=
    (differentiable_LFunction hχ).differentiableOn
  have hσ : (1 / 2 : ℝ) ∈ Icc l u := ⟨by linarith, by linarith⟩
  have key := Subconvexity.norm_le_interp_strip hlu hα0 hε'0.le zero_le_one hdiff hleft hright hgr hσ t₀
  have hlam : (1 / 2 - l) / (u - l) = 1 / 2 := by
    rw [div_eq_iff (sub_pos.2 hlu).ne', hl]; ring
  have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hc : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [hlam, e1, hc] at key
  -- the product of the two edge constants
  set X : ℝ := A * Real.exp (l ^ 2 + α ^ 2 / 4) with hX
  set Y : ℝ := B * Real.exp (u ^ 2 + ε' ^ 2 / 4) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hBle : B ≤ C₂ * (12 : ℝ) ^ ε' * (N : ℝ) ^ ε' := by
    rw [hB, mul_assoc, ← Real.mul_rpow (by norm_num) hN0.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hε'0.le) hC₂0.le
  have h12 : (12 : ℝ) ^ (2 * ε') = 12 ^ ε' * 12 ^ ε' := by rw [two_mul, Real.rpow_add (by norm_num)]
  have hNe : (N : ℝ) ^ (u - 1 / 2 + 2 * ε') = (N : ℝ) ^ (u - 1 / 2) * (N : ℝ) ^ ε' * (N : ℝ) ^ ε' := by
    rw [two_mul, ← add_assoc, Real.rpow_add hN0, Real.rpow_add hN0]
  have hXY : X * Y ≤ (c₀ * E * C₂ ^ 2 * (12 : ℝ) ^ (2 * ε')) * (N : ℝ) ^ (u - 1 / 2 + 2 * ε') := by
    have hc0 : 0 ≤ c₀ * (N : ℝ) ^ (u - 1 / 2) * E := by positivity
    calc X * Y = (c₀ * (N : ℝ) ^ (u - 1 / 2) * E) * (B * B) := by rw [hX, hY, hA, hE]; ring
      _ ≤ (c₀ * (N : ℝ) ^ (u - 1 / 2) * E) *
            ((C₂ * (12 : ℝ) ^ ε' * (N : ℝ) ^ ε') * (C₂ * (12 : ℝ) ^ ε' * (N : ℝ) ^ ε')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hBle hBle hB0 (by positivity)) hc0
      _ = (c₀ * E * C₂ ^ 2 * (12 : ℝ) ^ (2 * ε')) * (N : ℝ) ^ (u - 1 / 2 + 2 * ε') := by
          rw [h12, hNe]; ring
  have hsq : X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) ≤ D * (N : ℝ) ^ ((u - 1 / 2) / 2 + ε') := by
    rw [← Real.mul_rpow hX0 hY0]
    calc (X * Y) ^ (1 / 2 : ℝ)
        ≤ ((c₀ * E * C₂ ^ 2 * (12 : ℝ) ^ (2 * ε')) * (N : ℝ) ^ (u - 1 / 2 + 2 * ε')) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (mul_nonneg hX0 hY0) hXY (by norm_num)
      _ = D * (N : ℝ) ^ ((u - 1 / 2) / 2 + ε') := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN0.le, hD]
          congr 2
          ring
  -- assemble
  set e : ℝ := (u - 1 / 2) / 2 + ε' with he
  have he0 : 0 ≤ e := by linarith
  have hexp : 1 / 2 * α + 1 / 2 * ε' = e := by rw [hα, he]; ring
  rw [hexp] at key
  have hT : (1 + |t₀|) ^ e ≤ (|t₀| + 2) ^ e :=
    Real.rpow_le_rpow (by positivity) (by linarith) he0
  have hbase : (1 : ℝ) ≤ (N : ℝ) * (|t₀| + 2) :=
    one_le_mul_of_one_le_of_one_le hN1 (by linarith [abs_nonneg t₀])
  have hee : e ≤ 5 / 24 + ε := by rw [he, hu, hε']; linarith
  calc ‖LFunction χ (1 / 2 + t₀ * I)‖ ≤ X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) * (1 + |t₀|) ^ e := key
    _ ≤ D * (N : ℝ) ^ e * (|t₀| + 2) ^ e := by
        gcongr
    _ = D * ((N : ℝ) * (|t₀| + 2)) ^ e := by
        rw [Real.mul_rpow hN0.le (by positivity)]; ring
    _ ≤ D * ((N : ℝ) * (|t₀| + 2)) ^ (5 / 24 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hee) hD0.le

/-! ### Every character `χ ≠ 1` -/

/-- `∏_{p | q}(1 + p^{−1/2}) ≤ 2^{⌈e^{1/ε}⌉}q^ε` for `q ≥ 1` and `ε > 0`: a factor is at most `2 ≤ p^ε` when
`ε log p ≥ 1`, and at most `2 ≤ 2p^ε` for the primes `p < e^{1/ε}`; and `∏_{p | q} p ≤ q`. -/
theorem prod_primeFactors_le {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : q ≠ 0) :
    ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 2 ^ ⌈Real.exp (1 / ε)⌉₊ * (q : ℝ) ^ ε := by
  set X : ℝ := Real.exp (1 / ε) with hX
  have hfac : ∀ p ∈ q.primeFactors, 1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (if (p : ℝ) < X then (2 : ℝ) else 1) * (p : ℝ) ^ ε := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hp0 : (0 : ℝ) < p := by linarith
    have hhalf : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
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
  have h0 : ∀ p ∈ q.primeFactors, 0 ≤ 1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) := fun p _ => by positivity
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
  have hc0 : 0 ≤ ∏ p ∈ q.primeFactors, (if (p : ℝ) < X then (2 : ℝ) else 1) :=
    Finset.prod_nonneg fun p _ => by split_ifs <;> norm_num
  calc (∏ p ∈ q.primeFactors, (if (p : ℝ) < X then (2 : ℝ) else 1)) * ∏ p ∈ q.primeFactors, (p : ℝ) ^ ε
      ≤ 2 ^ ⌈X⌉₊ * (q : ℝ) ^ ε := mul_le_mul hcount hrad (Finset.prod_nonneg fun p _ => by positivity)
        (by positivity)

/-- **The bound on the critical line for every character `χ ≠ 1`, uniformly in the modulus**:
`CritBoundχ (5/24 + ε)` for every `ε > 0`. A character `χ ≠ 1` mod `q` is induced by its primitive character
`χ* ≠ 1` mod the conductor `f | q`, and `L(s, χ) = L(s, χ*)∏_{p | q}(1 − χ*(p)p^{−s})` (Mathlib's
`LFunction_changeLevel`); on `Re s = 1/2` the product is at most `∏_{p | q}(1 + p^{−1/2})`
(`prod_primeFactors_le`). -/
theorem critBoundχ {ε : ℝ} (hε : 0 < ε) : LinnikDensity.CritBoundχ (5 / 24 + ε) := by
  obtain ⟨C, hC0, hC⟩ := primitive_bound (half_pos hε)
  refine ⟨C * 2 ^ ⌈Real.exp (1 / (ε / 2))⌉₊, fun q _ χ hχ t => ?_⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χ' := χ.primitiveCharacter with hχ'def
  have hprim : χ'.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hχ' : χ' ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, ← hχ'def, h, changeLevel_one]
  set s : ℂ := 1 / 2 + t * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hL : LFunction χ s = LFunction χ' s * ∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-s)) := by
    have h := LFunction_changeLevel χ.conductor_dvd_level χ' (s := s) (Or.inl hχ')
    rwa [hχ'def, χ.changeLevel_primitiveCharacter] at h
  have hfac : ∀ p ∈ q.primeFactors, ‖1 - χ' p * (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re, hsre]
    have := DirichletCharacter.norm_le_one χ' p
    have hp' : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  have hprod : ‖∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-s))‖ ≤
      2 ^ ⌈Real.exp (1 / (ε / 2))⌉₊ * (q : ℝ) ^ (ε / 2) := by
    rw [norm_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfac).trans
      (prod_primeFactors_le (half_pos hε) (NeZero.ne q))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hfq : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hprimb := hC χ.conductor χ' hprim hχ' t
  have hbase : (1 : ℝ) ≤ (q : ℝ) * (|t| + 2) :=
    one_le_mul_of_one_le_of_one_le hq1 (by linarith [abs_nonneg t])
  have hmono : ((χ.conductor : ℝ) * (|t| + 2)) ^ (5 / 24 + ε / 2) ≤ ((q : ℝ) * (|t| + 2)) ^ (5 / 24 + ε / 2) :=
    Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
  have hqε : (q : ℝ) ^ (ε / 2) ≤ ((q : ℝ) * (|t| + 2)) ^ (ε / 2) :=
    Real.rpow_le_rpow (by positivity) (le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg t]))
      (by positivity)
  have h2 : (0 : ℝ) ≤ 2 ^ ⌈Real.exp (1 / (ε / 2))⌉₊ := by positivity
  rw [hL, norm_mul]
  calc ‖LFunction χ' s‖ * ‖∏ p ∈ q.primeFactors, (1 - χ' p * (p : ℂ) ^ (-s))‖
      ≤ (C * ((q : ℝ) * (|t| + 2)) ^ (5 / 24 + ε / 2)) *
          (2 ^ ⌈Real.exp (1 / (ε / 2))⌉₊ * ((q : ℝ) * (|t| + 2)) ^ (ε / 2)) := by
        gcongr
        · exact hprimb.trans (mul_le_mul_of_nonneg_left hmono hC0.le)
        · exact hprod.trans (mul_le_mul_of_nonneg_left hqε h2)
    _ = C * 2 ^ ⌈Real.exp (1 / (ε / 2))⌉₊ * ((q : ℝ) * (|t| + 2)) ^ (5 / 24 + ε) := by
        rw [show (5 / 24 + ε : ℝ) = (5 / 24 + ε / 2) + ε / 2 by ring,
          Real.rpow_add (by linarith) (5 / 24 + ε / 2) (ε / 2)]
        ring

/-! ### Linnik's exponent `17/6 + η` -/

/-- **Linnik's theorem with exponent `17/6 + η`, with no hypothesis.** For every `η > 0` there is `K` such that for
every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{17/6 + η}`: round 521's
`LinnikDensity.linnik_of_critBound` at `c = 5/24 + min(η, 1)/8`, fed `critBoundχ`. -/
theorem linnik_seventeen_sixths {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (17 / 6 + η) := by
  set η' : ℝ := min η 1 with hη'
  have hη'0 : 0 < η' := lt_min hη one_pos
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'1 : η' ≤ 1 := min_le_right _ _
  obtain ⟨K, hK⟩ := LinnikDensity.linnik_of_critBound (c := 5 / 24 + η' / 8) (by positivity) (by linarith)
    (critBoundχ (by positivity)) (half_pos hη)
  refine ⟨K, fun q _ a ha => ?_⟩
  obtain ⟨p, hp, hpa, hpK⟩ := hK q a ha
  refine ⟨p, hp, hpa, hpK.trans ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqx : 0 < (q : ℝ) ^ (2 + 4 * (5 / 24 + η' / 8) + η / 2) := by positivity
  have hK0 : 0 ≤ K := by
    by_contra h
    push Not at h
    have : K * (q : ℝ) ^ (2 + 4 * (5 / 24 + η' / 8) + η / 2) < 0 := mul_neg_of_neg_of_pos h hqx
    linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) hK0

end LinnikSubconvex

#print axioms LinnikSubconvex.primitive_bound
#print axioms LinnikSubconvex.prod_primeFactors_le
#print axioms LinnikSubconvex.critBoundχ
#print axioms LinnikSubconvex.linnik_seventeen_sixths
