/-
# Round 479: the prime number theorem modulo the divisors of `24`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `q ∣ 24`, every `a < q` prime to `q` and every `η > 0`,
`ψ(x; q, a) − x/φ(q) = O(x^{11/12+η})`, with round 222's `ψ(x; q, a) = Σ_{1 ≤ n ≤ x, n ≡ a (q)} Λ(n)`
(`PsiOmega.psiAP`) (`psiAP_isBigO_of_dvd_24`); the same for every `q ≥ 1` whose Dirichlet characters are all
quadratic (`psiAP_isBigO`). No hypothesis.

* `psiAP_eq_sum`: orthogonality, `ψ(x; q, a) = φ(q)⁻¹ Σ_χ χ(a⁻¹)ψ(x, χ)` (Mathlib's
  `DirichletCharacter.sum_char_inv_mul_char_eq`).
* `psiChi_one`, `sum_dvd_le_log`, `sum_not_coprime_le`: for the trivial character mod `q`,
  `ψ(x, 1) = ψ(x) − Σ_{n ≤ x, (n, q) > 1} Λ(n)`, and the subtracted sum is at most `ω(q) log x`: each prime `p ∣ q`
  contributes the `Λ(p^m) = log p` with `p^m ≤ x`, which sum to at most `log x`.
* `psiAP_isBigO`: round 467's `HalfPlanePNT.psi_isBigO_eleven_twelfths` for `ψ(x) − x`, round 478's
  `ChiPNT.psiChi_isBigO_eleven_twelfths` for each `ψ(x, χ)` with `χ ≠ 1`, and `log x ≤ x^e/e`.
* `isQuadratic_of_sq_eq_one`, `sq_eq_one_of_dvd_24`: every unit of `ℤ/24` squares to `1` (`decide`), so every
  unit of `ℤ/q` does for `q ∣ 24` (Mathlib's `ZMod.unitsMap_surjective`), and then every character mod `q` is
  quadratic.
-/
import ChiPNT

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology Asymptotics ArithmeticFunction

open scoped Chebyshev

namespace PNTProgressions

/-! ### The prime powers that share a factor with `q` -/

/-- `Σ_{n ≤ N, p ∣ n} Λ(n) ≤ log N` for a prime `p`: the terms are the `Λ(p^m) = log p` with
`p^m ≤ N`, and they sum to `log p^M ≤ log N` with `M = ⌊log_p N⌋`. -/
lemma sum_dvd_le_log {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ k ∈ (Finset.Icc 1 N).filter (p ∣ ·), Λ k ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set M := Nat.log p N with hMdef
  have hpM : p ^ M ≤ N := Nat.pow_log_le_self p hN.ne'
  have hsub : ((Finset.Icc 1 N).filter (p ∣ ·)).filter (fun k ↦ Λ k ≠ 0) ⊆ (p ^ M).divisors := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨⟨_, hkN⟩, hpk⟩, hΛ⟩ := hk
    have hpp : IsPrimePow k := by
      by_contra h
      exact hΛ (vonMangoldt_eq_zero_iff.2 h)
    obtain ⟨r, m, hr, hm, rfl⟩ := (isPrimePow_nat_iff k).1 hpp
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hpk)
    subst hpr
    have hmM : m ≤ M := Nat.le_log_of_pow_le hp.one_lt hkN
    rw [Nat.mem_divisors]
    exact ⟨pow_dvd_pow p hmM, pow_ne_zero _ hp.ne_zero⟩
  calc ∑ k ∈ (Finset.Icc 1 N).filter (p ∣ ·), Λ k
      = ∑ k ∈ ((Finset.Icc 1 N).filter (p ∣ ·)).filter (fun k ↦ Λ k ≠ 0), Λ k :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ k ∈ (p ^ M).divisors, Λ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ vonMangoldt_nonneg
    _ = Real.log ((p ^ M : ℕ) : ℝ) := vonMangoldt_sum
    _ ≤ Real.log N := Real.log_le_log (by have := hp.pos; positivity) (by exact_mod_cast hpM)

/-- `Σ_{n ≤ N, (n, q) > 1} Λ(n) ≤ ω(q) log N` for `q ≠ 0`. -/
lemma sum_not_coprime_le {q : ℕ} (hq : q ≠ 0) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (if k.Coprime q then 0 else Λ k) ≤ q.primeFactors.card * Real.log N := by
  have hnn : ∀ k p : ℕ, 0 ≤ (if p ∣ k then Λ k else 0) := fun k p ↦ by
    split_ifs
    · exact vonMangoldt_nonneg
    · exact le_rfl
  calc ∑ k ∈ Finset.Icc 1 N, (if k.Coprime q then 0 else Λ k)
      ≤ ∑ k ∈ Finset.Icc 1 N, ∑ p ∈ q.primeFactors, (if p ∣ k then Λ k else 0) := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        split_ifs with hk
        · exact Finset.sum_nonneg fun p _ ↦ hnn k p
        · obtain ⟨p, hp, hpk, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.1 hk
          have hpP : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, hq⟩
          calc Λ k = (if p ∣ k then Λ k else 0) := by simp [hpk]
            _ ≤ ∑ p ∈ q.primeFactors, (if p ∣ k then Λ k else 0) :=
                Finset.single_le_sum (f := fun p ↦ if p ∣ k then Λ k else 0)
                  (fun p _ ↦ hnn k p) hpP
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ Finset.Icc 1 N, (if p ∣ k then Λ k else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, Real.log N := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        rw [← Finset.sum_filter]
        exact sum_dvd_le_log (Nat.prime_of_mem_primeFactors hp) N
    _ = q.primeFactors.card * Real.log N := by simp

/-! ### Characters whose values are all real -/

/-- If every unit of `ℤ/q` squares to `1`, every Dirichlet character mod `q` is quadratic. -/
theorem isQuadratic_of_sq_eq_one {q : ℕ} (h : ∀ u : (ZMod q)ˣ, u ^ 2 = 1)
    (χ : DirichletCharacter ℂ q) : χ.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  refine MulChar.ext fun u ↦ ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, h u,
    Units.val_one, map_one]

/-- Every unit of `ℤ/q` squares to `1` when `q ∣ 24`. -/
theorem sq_eq_one_of_dvd_24 {q : ℕ} (hq : q ∣ 24) (u : (ZMod q)ˣ) : u ^ 2 = 1 := by
  have h24 : ∀ a : ZMod 24, a.val.Coprime 24 → a ^ 2 = 1 := by decide
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hq u
  have hv : v ^ 2 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h24 _ (ZMod.val_coe_unit_coprime v))
  rw [← map_pow, hv, map_one]

/-! ### The prime number theorem in progressions -/

/-- `ψ(x, χ)` for the trivial character mod `q`: `ψ(x)` less the prime powers sharing a factor
with `q`. -/
lemma psiChi_one (q : ℕ) [NeZero q] (x : ℝ) :
    ChiPNT.psiChi (1 : DirichletCharacter ℂ q) x =
      ((ψ x - ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (if k.Coprime q then 0 else Λ k) : ℝ) : ℂ) := by
  have hI : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
    simpa using (Finset.Icc_add_one_left_eq_Ioc 0 ⌊x⌋₊).symm
  rw [ChiPNT.psiChi, Chebyshev.psi, hI, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : k.Coprime q
  · have hu : IsUnit (k : ZMod q) := (ZMod.isUnit_iff_coprime k q).2 hk
    rw [MulChar.one_apply hu, ite_eq_left hk]
    push_cast
    ring
  · have hu : ¬ IsUnit (k : ZMod q) := fun h ↦ hk ((ZMod.isUnit_iff_coprime k q).1 h)
    rw [MulChar.map_nonunit _ hu, ite_eq_right hk]
    ring

/-- **Orthogonality**: `ψ(x; q, a) = φ(q)⁻¹ Σ_χ χ(a⁻¹) ψ(x, χ)` for `a` prime to `q`, `a < q`. -/
lemma psiAP_eq_sum (q : ℕ) [NeZero q] {a : ℕ} (ha : a.Coprime q) (haq : a < q) (x : ℝ) :
    ((PsiOmega.psiAP q a x : ℝ) : ℂ) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * ChiPNT.psiChi χ x := by
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  simp only [PsiOmega.psiAP, ChiPNT.psiChi, Finset.mul_sum]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hau (k : ZMod q)
  have hiff : k % q = a ↔ (a : ZMod q) = (k : ZMod q) := by
    rw [eq_comm, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt haq]
  have hre : ∑ χ : DirichletCharacter ℂ q,
      (q.totient : ℂ)⁻¹ * (χ ((a : ZMod q)⁻¹) * (χ k * (Λ k : ℂ))) =
      (q.totient : ℂ)⁻¹ * (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ k) * Λ k := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun χ _ ↦ by ring
  rw [hre, horth]
  by_cases h : k % q = a
  · simp only [h, hiff.1 h, ite_true]
    field_simp
  · have h' : ¬ (a : ZMod q) = k := fun h' ↦ h (hiff.2 h')
    simp [h, h']

/-- **The prime number theorem in progressions modulo `q` with every character real**: if every
Dirichlet character mod `q` is quadratic, then for `a` prime to `q`, `a < q`,
`ψ(x; q, a) − x/φ(q) = O(x^{11/12+η})` for every `η > 0`. -/
theorem psiAP_isBigO {q : ℕ} [NeZero q] (hreal : ∀ χ : DirichletCharacter ℂ q, χ.IsQuadratic)
    {a : ℕ} (ha : a.Coprime q) (haq : a < q) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.psiAP q a x - x / q.totient) =O[atTop] fun x ↦ x ^ (11 / 12 + η) := by
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hainv : IsUnit ((a : ZMod q)⁻¹) :=
    IsUnit.of_mul_eq_one (a : ZMod q) (by rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hau)
  set e : ℝ := 11 / 12 + η with hedef
  have he : 0 < e := by linarith
  set E : ℝ → ℝ := fun x ↦ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (if k.Coprime q then 0 else Λ k) with hEdef
  -- the decomposition
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
  -- the pieces
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
        (ChiPNT.psiChi_isBigO_eleven_twelfths (hreal χ) (Finset.ne_of_mem_erase hχ) hη).const_mul_left _
    rwa [Finset.sum_fn] at h
  have hC : (fun x : ℝ ↦ (((PsiOmega.psiAP q a x - x / q.totient : ℝ)) : ℂ)) =O[atTop]
      fun x ↦ x ^ e := by
    simp_rw [hdec]
    exact ((hψ.sub hE).add hχ).const_mul_left _
  rw [← isBigO_norm_left] at hC ⊢
  exact hC.congr_left fun x ↦ Complex.norm_real _

/-- **The prime number theorem modulo the divisors of `24`**: for `q ∣ 24` and `a` prime to `q`,
`a < q`, `ψ(x; q, a) = x/φ(q) + O(x^{11/12+η})` for every `η > 0`. -/
theorem psiAP_isBigO_of_dvd_24 {q : ℕ} [NeZero q] (hq : q ∣ 24) {a : ℕ} (ha : a.Coprime q)
    (haq : a < q) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.psiAP q a x - x / q.totient) =O[atTop] fun x ↦ x ^ (11 / 12 + η) :=
  psiAP_isBigO (isQuadratic_of_sq_eq_one (sq_eq_one_of_dvd_24 hq)) ha haq hη

end PNTProgressions
