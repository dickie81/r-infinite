import PNTProgressions
import DHHadamard
import DirichletCharHalfPlane

/-! # Stack review 3, door D1 (STRUCTURAL-REVIEW.md §9.2): the prime number theorem modulo every `q`

Not compiled by any build script. Compile it against the built stack, from a built Mathlib checkout:
`LEAN_PATH="$(lake env printenv LEAN_PATH):<pilot>/build" lean <pilot>/review/stack3/DoorAP.lean`
(8 s at round 508's head; both printed axiom lists are `[propext, Classical.choice, Quot.sound]`).

`ChiPNT.psiChi_isBigO_of_zeroFree` with round 254's `PsiOmega.norm_LFunction_leC` (every `χ ≠ 1`) in place of
round 224's `PsiOmega.norm_LFunction_le` (quadratic `χ`), at round 495's half-plane `Eis.LFunction_ne_zero_of_re_gt`;
then round 479's `PNTProgressions.psiAP_isBigO` without its hypothesis that every character mod `q` is quadratic.
-/

open Complex Set Real Filter Topology MeasureTheory Asymptotics ArithmeticFunction

namespace ChiPNTAll

open SmoothPerron HalfPlanePNT ChiPNT

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `ChiPNT.psiChi_isBigO_of_zeroFree` without the quadratic hypothesis: the growth bound is
`PsiOmega.norm_LFunction_leC` (every `χ ≠ 1`) in place of `PsiOmega.norm_LFunction_le`. -/
theorem psiChi_isBigO_of_zeroFree (hχ : χ ≠ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hzf : ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction χ s ≠ 0) {η : ℝ}
    (hη : 0 < η) : psiChi χ =O[atTop] fun x ↦ x ^ (θ + η) := by
  have hF := DirichletCharacter.differentiable_LFunction hχ
  have hgrowth : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℂ, δ ≤ s.re → s.re ≤ 3 → 1 ≤ |s.im| →
      ‖DirichletCharacter.LFunction χ s‖ ≤ c * |s.im| := by
    intro δ hδ
    refine ⟨(N + 1) * 4 / δ, by positivity, fun s hs1 hs3 him ↦ ?_⟩
    have hre : 0 < s.re := by linarith
    have hn : ‖s‖ ≤ 4 * |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 3 + |s.im| := by rw [abs_of_pos hre]; linarith
        _ ≤ 4 * |s.im| := by linarith
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ (N + 1) * ‖s‖ / s.re :=
          PsiOmega.norm_LFunction_leC hχ hre
      _ ≤ (N + 1) * (4 * |s.im|) / δ := by
          gcongr
      _ = (N + 1) * 4 / δ * |s.im| := by ring
  have hμ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) ((3 / 2 : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by norm_num))
  have hlow : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (ctr t)‖⁻¹ ≤
      ∑' n, ‖LSeries.term (fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)) (3 / 2 : ℝ) n‖ := by
    intro t
    have hs : 1 < (ctr t).re := by rw [ctr_re]; norm_num
    have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    have hne : LSeries (fun n ↦ χ n) (ctr t) ≠ 0 := fun h ↦ by simp [h] at hm
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hm]
    exact norm_LSeries_le hμ t
  have hΛ : LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
      ((3 / 2 : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num)
  have hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s‖ ≤
      ∑' n, ‖LSeries.term (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℝ) n‖ := by
    intro s hs
    rw [← norm_neg, ← LSeries_twist_vonMangoldt_eq_LFunction χ (by linarith)]
    exact norm_LSeries_le_of_le_re hΛ hs
  have hfΛ : ∀ n : ℕ,
      ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one _ _)
  exact sum_isBigO_of_zeroFree hF hθ0 hθ1 hzf hgrowth hlow hright (by simp) hfΛ
    (fun s hs ↦ LSeries_twist_vonMangoldt_eq_LFunction χ hs) hη

/-- **`ψ(x, χ) = O(x^{11/12+η})` for every Dirichlet character `χ ≠ 1`**, from round 495's half-plane. -/
theorem psiChi_isBigO_eleven_twelfths (hχ : χ ≠ 1) {η : ℝ} (hη : 0 < η) :
    psiChi χ =O[atTop] fun x ↦ x ^ (11 / 12 + η) :=
  psiChi_isBigO_of_zeroFree hχ (by norm_num) (by norm_num)
    (fun _ hs ↦ Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)) hη

end ChiPNTAll

open scoped Chebyshev

namespace PNTProgressionsAll

open PNTProgressions

/-- **The prime number theorem in progressions modulo every `q`**: for `a` prime to `q`, `a < q`,
`ψ(x; q, a) − x/φ(q) = O(x^{11/12+η})` for every `η > 0`. -/
theorem psiAP_isBigO {q : ℕ} [NeZero q] {a : ℕ} (ha : a.Coprime q) (haq : a < q) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.psiAP q a x - x / q.totient) =O[atTop] fun x ↦ x ^ (11 / 12 + η) := by
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hainv : IsUnit ((a : ZMod q)⁻¹) :=
    IsUnit.of_mul_eq_one (a : ZMod q) (by rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hau)
  set e : ℝ := 11 / 12 + η with hedef
  have he : 0 < e := by linarith
  set E : ℝ → ℝ := fun x ↦ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (if k.Coprime q then 0 else Λ k) with hEdef
  have hdec : ∀ x : ℝ, (((PsiOmega.psiAP q a x - x / q.totient : ℝ)) : ℂ) =
      (q.totient : ℂ)⁻¹ * ((((ψ x - x : ℝ)) : ℂ) - ((E x : ℝ) : ℂ) +
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          χ ((a : ZMod q)⁻¹) * ChiPNT.psiChi χ x) := by
    intro x
    have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
    have h1 := psiAP_eq_sum q ha haq x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), MulChar.one_apply hainv, one_mul,
      psiChi_one] at h1
    push_cast at h1 ⊢
    rw [h1, hEdef]
    push_cast
    field_simp
    ring
  have hψ : (fun x : ℝ ↦ (((ψ x - x : ℝ)) : ℂ)) =O[atTop] fun x ↦ x ^ e := by
    have h := HalfPlanePNT.psi_isBigO_eleven_twelfths hη
    rw [← isBigO_norm_left] at h ⊢
    refine h.congr_left fun x ↦ ?_
    rw [Complex.norm_real]
    rfl
  have hE : (fun x : ℝ ↦ ((E x : ℝ) : ℂ)) =O[atTop] fun x ↦ x ^ e := by
    refine IsBigO.of_bound (q.primeFactors.card / e) ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have hE0 : 0 ≤ E x := Finset.sum_nonneg fun k _ ↦ by
      split_ifs
      · exact le_rfl
      · exact vonMangoldt_nonneg
    rw [Complex.norm_real, Real.norm_of_nonneg hE0, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hfl : 0 < (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.floor_pos.2 hx
    calc E x ≤ q.primeFactors.card * Real.log ⌊x⌋₊ := sum_not_coprime_le (NeZero.ne q) _
      _ ≤ q.primeFactors.card * Real.log x := by
          gcongr
          exact Nat.floor_le hx0.le
      _ ≤ q.primeFactors.card * (x ^ e / e) := by
          gcongr
          exact Real.log_le_rpow_div hx0.le he
      _ = q.primeFactors.card / e * x ^ e := by ring
  have hχ : (fun x : ℝ ↦ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      χ ((a : ZMod q)⁻¹) * ChiPNT.psiChi χ x) =O[atTop] fun x ↦ x ^ e := by
    have h := IsBigO.sum (A := fun χ x ↦ χ ((a : ZMod q)⁻¹) * ChiPNT.psiChi χ x)
      (s := Finset.univ.erase (1 : DirichletCharacter ℂ q)) (l := atTop)
      (g := fun x : ℝ ↦ x ^ e) fun χ hχ ↦
        (ChiPNTAll.psiChi_isBigO_eleven_twelfths (Finset.ne_of_mem_erase hχ) hη).const_mul_left _
    rwa [Finset.sum_fn] at h
  have hC : (fun x : ℝ ↦ (((PsiOmega.psiAP q a x - x / q.totient : ℝ)) : ℂ)) =O[atTop]
      fun x ↦ x ^ e := by
    simp_rw [hdec]
    exact ((hψ.sub hE).add hχ).const_mul_left _
  rw [← isBigO_norm_left] at hC ⊢
  exact hC.congr_left fun x ↦ Complex.norm_real _

end PNTProgressionsAll

#print axioms ChiPNTAll.psiChi_isBigO_eleven_twelfths
#print axioms PNTProgressionsAll.psiAP_isBigO
