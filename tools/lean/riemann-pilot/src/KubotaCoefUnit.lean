import KubotaCoefSqfree

/-! # The unit `−1`: `τ(−m) = τ(m)` (round 456)

S5f-14 of round 360's plan, part 1. Round 455's next step planned the unit `−1`: `τ(−m) = τ(m)`, which gives
round 361's display its coefficient at `−δ₃nb³`. This round proves it, through round 428's sums and round
450's residue principle:

* **Sums over classes** (`tsum_quot_congr`): a sum over the classes modulo `N` of a function periodic modulo
  `N` depends only on the ideal `(N)`.
* **The sums and the series** (`smTerm_neg`, **`cuspSm_neg`**, `dirD_neg` and `dirL_neg`):
  `S_{−m}(c) = S_m(−c)`, so `D_{−m} = D_m` and `Λ_{−x} = Λ_x` for `Re s > 2`.
* **θ's coefficients** (`rhoM_neg` and **`tauTh_neg`**): `ρ(−x) = ρ(x)`, and `τ(−m) = τ(m)` for every `m`.
* **The display's coefficients** (**`tauTh_display_coef`**): the coefficient conjunct of round 361's
  `KubotaTheta` for θ, with `C = τ(δ₃)`: `τ(±δ₃nb³) = τ(δ₃)·N(b)^{1/2}·(δ₃/n)₆²·conj γ₂(n)`.
-/

open Ideal NumberField
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Eis

/-- **A sum over the classes modulo `N` of a function periodic modulo `N` depends only on the ideal `(N)`.**
-/
theorem tsum_quot_congr {N N' : 𝓞 K} (hN : N ≠ 0) (h : span {N} = span {N'}) {F : 𝓞 K → ℂ}
    (hF : ∀ y y', N ∣ y - y' → F y = F y') :
    ∑' r : 𝓞 K ⧸ span {N}, F (repQ N r) = ∑' r : 𝓞 K ⧸ span {N'}, F (repQ N' r) := by
  have hN' : N' ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.span_singleton_eq_bot] at h
    exact hN h
  have := finite_quot N hN
  have := finite_quot N' hN'
  let := Fintype.ofFinite (𝓞 K ⧸ span {N})
  let := Fintype.ofFinite (𝓞 K ⧸ span {N'})
  rw [tsum_fintype, tsum_fintype]
  refine Fintype.sum_equiv (Ideal.quotEquivOfEq h).toEquiv _ _ fun r => hF _ _ ?_
  have h1 : Ideal.Quotient.mk (span {N'}) (repQ N r) =
      Ideal.Quotient.mk (span {N'}) (repQ N' ((Ideal.quotEquivOfEq h) r)) := by
    rw [repQ_mk, ← Ideal.quotEquivOfEq_mk h, repQ_mk]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  have hNN' : N ∣ N' := by
    rw [← Ideal.mem_span_singleton, h]
    exact Ideal.mem_span_singleton_self N'
  exact hNN'.trans h1

/-- **`smTerm (−m) c d = smTerm m (−c) d`**: `(c, d)` and `(−c, d)` are bottom rows together,
`(−c/d)₃ = (c/d)₃` for primary `d` (round 362's `cub_neg`), and `ĕ((−m/9)(d/c)) = ĕ((m/9)(d/(−c)))`. -/
theorem smTerm_neg (m c d : 𝓞 K) : smTerm (-m) c d = smTerm m (-c) d := by
  classical
  unfold smTerm
  have hrow : BRow (c, d) ↔ BRow (-c, d) := by
    unfold BRow
    simp only [IsCoprime.neg_left_iff, dvd_neg]
  by_cases h : BRow (c, d)
  · rw [ite_eq_left h, ite_eq_left (hrow.1 h), cub_neg h.2.2]
    congr 1
    congr 1
    rw [map_neg, map_neg, div_neg]
    ring
  · rw [ite_eq_right h, ite_eq_right (mt hrow.2 h)]

/-- **`S_{−m}(c) = S_m(−c)`** for `m = δ₃x` and `c ≠ 0`: the summands agree (`smTerm_neg`), and the classes
modulo `3c` and `−3c` are the same (`tsum_quot_congr`), with round 451's `smTerm_add` for the periodicity. -/
theorem cuspSm_neg (x : 𝓞 K) {c : 𝓞 K} (hc : c ≠ 0) : cuspSm (δ3 * -x) c = cuspSm (δ3 * x) (-c) := by
  have h30 : (3 : 𝓞 K) ≠ 0 := fun h => by
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  rw [cuspSm_eq, cuspSm_eq]
  simp_rw [show δ3 * -x = -(δ3 * x) by ring, smTerm_neg]
  refine tsum_quot_congr (mul_ne_zero h30 hc)
    (by rw [show (3 : 𝓞 K) * -c = -(3 * c) by ring, Ideal.span_singleton_neg]) fun y y' hyy => ?_
  obtain ⟨u, hu⟩ := hyy
  rw [show y = y' + 3 * -c * -u by linear_combination hu]
  exact smTerm_add x (-c) y' (-u) (neg_ne_zero.2 hc)

/-- **`D_{−m}(s) = D_m(s)`** for `m = δ₃x` and `Re s > 2`: reindex `c ↦ −c`, with `N(−c) = N(c)`. -/
theorem dirD_neg (x : 𝓞 K) {s : ℂ} (hs : 2 < s.re) : dirD (δ3 * -x) s = dirD (δ3 * x) s := by
  have hs0 : -s ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold dirD
  conv_lhs => rw [← (Equiv.neg (𝓞 K)).tsum_eq]
  refine tsum_congr fun c => ?_
  simp only [Equiv.neg_apply]
  by_cases hc : c = 0
  · subst hc
    simp [Complex.zero_cpow hs0]
  · rw [cuspSm_neg x (neg_ne_zero.2 hc), neg_neg, map_neg, Complex.normSq_neg]

/-- **`Λ_{−x} = Λ_x`** for `Re s > 2`, with round 450's completed series. -/
theorem dirL_neg (x : 𝓞 K) {s : ℂ} (hs : 2 < s.re) : dirL (-x) s = dirL x s := by
  rw [dirL_eq, dirL_eq, dirD_neg x hs, show δ3 * -x = -(δ3 * x) by ring, map_neg, neg_div, norm_neg]

/-- **`ρ(−x) = ρ(x)`** for `x ≠ 0`, from `dirL_neg` and round 450's `sum_rhoM_eq_zero` (round 431's `rhoM`).
-/
theorem rhoM_neg {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) {x : 𝓞 K} (hx : x ≠ 0) :
    rhoM (-x) r Y hY = rhoM x r Y hY := by
  set xs : Fin 2 → 𝓞 K := ![-x, x] with hxs_def
  set a : Fin 2 → ℂ → ℂ := ![fun _ => 1, fun _ => -1] with ha_def
  have hxs : ∀ i, xs i ≠ 0 := by
    intro i
    fin_cases i
    · exact neg_ne_zero.2 hx
    · exact hx
  have ha : ∀ i, Differentiable ℂ (a i) := by
    intro i
    fin_cases i <;> exact differentiable_const _
  have hrel : ∀ s : ℂ, 2 < s.re → ∑ i, a i s * dirL (xs i) s = 0 := by
    intro s hs
    simp only [Fin.sum_univ_two, ha_def, hxs_def, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [dirL_neg x hs]
    ring
  have key := sum_rhoM_eq_zero hr hY xs hxs a ha hrel
  simp only [Fin.sum_univ_two, ha_def, hxs_def, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  linear_combination key

/-- **`τ(−m) = τ(m)`** for every `m`, with round 436's `tauTh`, which is `0` off `δ₃·(ℤ[ω] ∖ 0)`. -/
theorem tauTh_neg {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) (m : 𝓞 K) :
    tauTh r Y hY (-m) = tauTh r Y hY m := by
  by_cases h : ∃ x, x ≠ 0 ∧ m = δ3 * x
  · obtain ⟨x, hx, rfl⟩ := h
    rw [show -(δ3 * x) = δ3 * -x by ring, tauTh_δ3_mul r Y hY (neg_ne_zero.2 hx), tauTh_δ3_mul r Y hY hx,
      rhoM_neg hr hY hx]
  · have h' : ¬ ∃ x, x ≠ 0 ∧ -m = δ3 * x := by
      rintro ⟨x, hx, hxe⟩
      exact h ⟨-x, neg_ne_zero.2 hx, by linear_combination -hxe⟩
    rw [tauTh_of_not r Y hY h, tauTh_of_not r Y hY h']

/-- **The coefficient conjunct of round 361's `KubotaTheta` for θ**, with `C = τ(δ₃)`: for primary `n` and `b`
with `(n)` squarefree and `N(nb)` prime to `6`, `τ(±δ₃nb³) = τ(δ₃)·N(b)^{1/2}·(δ₃/n)₆²·conj γ₂(n)`. -/
theorem tauTh_display_coef {r : ℝ} (hr : 0 < r) {Y : ℝ} (hY : 0 < Y) :
    ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) → (absNorm (span {n * b})).Coprime 6 →
      tauTh r Y hY (δ3 * n * b ^ 3) = tauTh r Y hY δ3 * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) ∧
      tauTh r Y hY (-(δ3 * n * b ^ 3)) = tauTh r Y hY δ3 * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})) := by
  intro n b hn hb hsq h6
  have h := tauTh_sqfree_cube hr hY hn hb hsq h6
  exact ⟨h, by rw [tauTh_neg hr hY, h]⟩

end Eis

end

#print axioms Eis.tsum_quot_congr
#print axioms Eis.smTerm_neg
#print axioms Eis.cuspSm_neg
#print axioms Eis.dirD_neg
#print axioms Eis.dirL_neg
#print axioms Eis.rhoM_neg
#print axioms Eis.tauTh_neg
#print axioms Eis.tauTh_display_coef
