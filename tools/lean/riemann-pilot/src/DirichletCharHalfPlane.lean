import SexticCharHalfPlane

/-!
# Round 495: every Dirichlet character, `L(s, χ) ≠ 0` on `Re s > 11/12` (door 5(b), step 4)

Step 4 of round 491's plan for door 5(b), and the end of door 5 of round 481: the half-plane for every Dirichlet
character, through the family twisted by `χ∘N` (round 494) instead of a member of the family.

* **The norm modulo `q`** (`normZ`, `normZ_mul`, `normZ_one`, **`normZ_congr`**): `N(a) mod q` is multiplicative and
  depends only on `a` modulo `q`: `N(a) = a·ā` (round 290's `mul_cj_eq_absNorm`), so `a ≡ b (mod q)` gives
  `N(a) − N(b) ∈ q·𝓞 K`, and an integer divisible by `q` in `𝓞 K` is divisible by `q` in `ℤ`
  (`intCast_dvd_of_dvd`: compare the norms, `q² ∣ z²`).
* **The twist** (**`nuChi`**): for a Dirichlet character `χ` mod `q` and `m` with `q ∣ m` in `𝓞 K`, the character
  `ν_χ(a mod m) = χ(N(a))` on the units of `𝓞 K/(m)` and `0` elsewhere (`nuChi_mk`). An element whose norm is prime
  to `n` is a unit modulo `n` (`isUnit_mk_of_coprime`, from a Bézout identity and `N(a) = a·ā`). So at `m = 4q`,
  `ν_χ(pgen 𝔞 mod 4q) = χ(N𝔞)` for every ideal `𝔞` of norm prime to `6` (**`nuChi_pgen`**).
* **The half-plane** (**`LFunction_ne_zero_of_sq_ne_one`**): for `χ² ≠ 1`, round 495's `ne_zero_of_famTwist` at
  level `3q`, with the family twisted by `ν_χ` modulo `4q` (round 494's `meanSquareNu`) and the member `1`, gives
  `L(s, χ)L(s, χχ₋₃) ≠ 0` at level `3q` on `Re s > 11/12`; Mathlib's `LFunction_changeLevel` returns to
  `L(s, χ)`, as in round 489's `LFunction_ne_zero_of_member`. With round 477 for the real characters:
  **`LFunction_ne_zero_of_re_gt`**: `L(s, χ) ≠ 0` for every Dirichlet character `χ` of every modulus `q ≥ 1` and
  every `s` with `Re s > 11/12`, the trivial character excepted at `s = 1`.
-/

open NumberField Ideal

namespace Eis

open DirichletCharacter HalfPlaneS0

/-! ### The norm modulo `q` -/

/-- The norm of `a`, modulo `q`. -/
noncomputable def normZ (q : ℕ) (a : 𝓞 K) : ZMod q := (absNorm (span {a}) : ZMod q)

theorem normZ_mul (q : ℕ) (a b : 𝓞 K) : normZ q (a * b) = normZ q a * normZ q b := by
  unfold normZ
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul]

theorem normZ_one (q : ℕ) : normZ q 1 = 1 := by
  unfold normZ
  rw [Ideal.span_singleton_one, Ideal.absNorm_top, Nat.cast_one]

/-- An integer divisible by `q` in `𝓞 K` is divisible by `q` in `ℤ`: the norms give `q² ∣ z²`. -/
theorem intCast_dvd_of_dvd {q : ℕ} {z : ℤ} (h : (q : 𝓞 K) ∣ (z : 𝓞 K)) : (q : ℤ) ∣ z := by
  have h1 : absNorm (span {(q : 𝓞 K)}) ∣ absNorm (span {(z : 𝓞 K)}) :=
    map_dvd absNorm (Ideal.span_singleton_dvd_span_singleton_iff_dvd.2 h)
  rw [absNorm_natCast_span_sq, absNorm_span_intCast] at h1
  exact Int.natCast_dvd.2 ((Nat.pow_dvd_pow_iff two_ne_zero).1 h1)

/-- **The norm modulo `q` depends only on the class modulo `q`**: `N(a) − N(b) = q·(t·ā + b·t̄)` for
`a − b = q·t`, since `N(x) = x·x̄`. -/
theorem normZ_congr {q : ℕ} {a b : 𝓞 K} (h : (q : 𝓞 K) ∣ a - b) : normZ q a = normZ q b := by
  obtain ⟨t, ht⟩ := h
  have hb : b = a - q * t := by rw [← ht]; ring
  have e : (((absNorm (span {a}) : ℤ) - (absNorm (span {b}) : ℤ) : ℤ) : 𝓞 K) =
      (q : 𝓞 K) * (t * cj a + b * cj t) := by
    push_cast
    rw [← mul_cj_eq_absNorm, ← mul_cj_eq_absNorm, hb, map_sub, map_mul, map_natCast]
    ring
  have hd := intCast_dvd_of_dvd (z := (absNorm (span {a}) : ℤ) - (absNorm (span {b}) : ℤ)) ⟨_, e⟩
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hd
  push_cast at h0
  exact sub_eq_zero.1 h0

/-- **An element whose norm is prime to `n` is a unit modulo `n`**: `a·(x·ā) + n·y = 1` from a Bézout identity
`x·N(a) + y·n = 1` and `N(a) = a·ā`. -/
theorem isUnit_mk_of_coprime {n : ℕ} {a : 𝓞 K} (h : (absNorm (span {a})).Coprime n) :
    IsUnit (Ideal.Quotient.mk (span {(n : 𝓞 K)}) a) := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 h
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ ((x : 𝓞 K) * cj a)) ?_
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨-(y : 𝓞 K), ?_⟩
  have e := mul_cj_eq_absNorm a
  have e2 := congrArg (fun z : ℤ => (z : 𝓞 K)) hxy
  push_cast at e2
  linear_combination (x : 𝓞 K) * e + e2

/-! ### The twist `ν_χ` -/

section Twist

variable {q : ℕ} {m : 𝓞 K}

/-- A representative of a class modulo `m`. -/
noncomputable def liftM (x : 𝓞 K ⧸ span {m}) : 𝓞 K := (Ideal.Quotient.mk_surjective x).choose

theorem mk_liftM (x : 𝓞 K ⧸ span {m}) : Ideal.Quotient.mk (span {m}) (liftM x) = x :=
  (Ideal.Quotient.mk_surjective x).choose_spec

theorem normZ_liftM_mk (hqm : (q : 𝓞 K) ∣ m) (a : 𝓞 K) :
    normZ q (liftM (Ideal.Quotient.mk (span {m}) a)) = normZ q a := by
  refine normZ_congr (dvd_trans hqm ?_)
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_liftM]

open Classical in
/-- **The twist by `χ∘N` modulo `m`**: for a Dirichlet character `χ` mod `q` and `q ∣ m` in `𝓞 K`,
`ν_χ(a mod m) = χ(N(a))` on the units of `𝓞 K/(m)`, and `0` elsewhere. -/
noncomputable def nuChi (χ : DirichletCharacter ℂ q) (hqm : (q : 𝓞 K) ∣ m) : MulChar (𝓞 K ⧸ span {m}) ℂ where
  toFun x := if IsUnit x then χ (normZ q (liftM x)) else 0
  map_one' := by
    have h1 := normZ_liftM_mk hqm 1
    rw [map_one] at h1
    simp only [isUnit_one, ite_true, h1, normZ_one, map_one]
  map_mul' x y := by
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · simp only [hx, hy, hx.mul hy, ite_true]
        rw [← map_mul χ, ← normZ_mul]
        congr 1
        conv_lhs => rw [← mk_liftM x, ← mk_liftM y, ← map_mul]
        exact normZ_liftM_mk hqm _
      · have hxy : ¬ IsUnit (x * y) := fun h => hy (isUnit_of_mul_isUnit_right h)
        simp only [hxy, hy, ite_false, mul_zero]
    · have hxy : ¬ IsUnit (x * y) := fun h => hx (isUnit_of_mul_isUnit_left h)
      simp only [hxy, hx, ite_false, zero_mul]
  map_nonunit' x hx := by simp only [hx, ite_false]

open Classical in
theorem nuChi_mk (χ : DirichletCharacter ℂ q) (hqm : (q : 𝓞 K) ∣ m) {a : 𝓞 K}
    (ha : IsUnit (Ideal.Quotient.mk (span {m}) a)) :
    nuChi χ hqm (Ideal.Quotient.mk (span {m}) a) = χ (normZ q a) := by
  change (if IsUnit (Ideal.Quotient.mk (span {m}) a) then
    χ (normZ q (liftM (Ideal.Quotient.mk (span {m}) a))) else 0) = _
  rw [ite_eq_left ha, normZ_liftM_mk hqm]

/-- `q` divides `4q`. -/
theorem natCast_dvd_four_mul (q : ℕ) : (q : 𝓞 K) ∣ ((4 * q : ℕ) : 𝓞 K) := ⟨4, by push_cast; ring⟩

/-- **The twist at the primary generators**: `ν_χ(pgen 𝔞 mod 4q) = χ(N𝔞)` for every ideal `𝔞` of norm prime to
`6`. If the class is a unit this is `nuChi_mk`, since `(pgen 𝔞) = 𝔞`; otherwise `N𝔞` is not prime to `q`
(`isUnit_mk_of_coprime`, `N𝔞` being odd), and both sides are `0`. -/
theorem nuChi_pgen (χ : DirichletCharacter ℂ q) {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    nuChi χ (natCast_dvd_four_mul q) (Ideal.Quotient.mk _ (pgen I)) = χ (absNorm I) := by
  have hspan : span {pgen I} = I := (pgen_spec6 hI).2
  by_cases hu : IsUnit (Ideal.Quotient.mk (span {((4 * q : ℕ) : 𝓞 K)}) (pgen I))
  · rw [nuChi_mk χ _ hu, normZ, hspan]
  · rw [MulChar.map_nonunit _ hu]
    symm
    apply MulChar.map_nonunit
    intro hχu
    apply hu
    rw [ZMod.isUnit_iff_coprime] at hχu
    apply isUnit_mk_of_coprime
    rw [hspan]
    have h2 : (absNorm I).Coprime 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hI
    exact Nat.Coprime.mul_right (by simpa using h2.pow_right 2) hχu

end Twist

/-! ### The half-plane -/

/-- At the norms prime to `6`, `χ` and `χ` at level `3q` agree. -/
theorem changeLevel_three_mul_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hqN : q ∣ 3 * q) {n : ℕ}
    (hn : n.Coprime 6) : changeLevel hqN χ n = χ n := by
  by_cases hnq : n.Coprime q
  · have hnN : IsCoprime ((n : ℕ) : ℤ) ((3 * q : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2
        (Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right (by norm_num) hn) hnq)
    have e := changeLevel_eq_cast_of_dvd' χ hqN hnN
    simp only [Int.cast_natCast] at e
    exact e
  · have h1 : changeLevel hqN χ n = 0 := by
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      exact fun h ↦ hnq (Nat.Coprime.coprime_dvd_right hqN h)
    have h2 : χ n = 0 := by
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      exact hnq
    rw [h1, h2]

/-- **The half-plane `Re s > 11/12` for the characters with `χ² ≠ 1`**: round 495's `ne_zero_of_famTwist` at
level `3q`, for the family twisted by `ν_χ` modulo `4q` (round 494's `meanSquareNu`) at the member `1`. -/
theorem LFunction_ne_zero_of_sq_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 ≠ 1)
    {s : ℂ} (hs : 11 / 12 < s.re) : LFunction χ s ≠ 0 := by
  have hqN : q ∣ 3 * q := Dvd.intro_left 3 rfl
  have h3 : 3 ∣ 3 * q := Dvd.intro q rfl
  have : NeZero (3 * q) := ⟨by have := NeZero.ne q; positivity⟩
  have hχ1 : χ ≠ 1 := fun h ↦ hχ2 (by rw [h, one_pow])
  have hχ' : changeLevel hqN χ ≠ 1 := fun h ↦ hχ1 ((changeLevel_eq_one_iff hqN).1 h)
  have hχ'3 : mulChi3 h3 (changeLevel hqN χ) ≠ 1 := by
    intro h
    apply hχ2
    have hc : changeLevel hqN χ = (changeLevel h3 PsiOmega.chi3)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hc2 : changeLevel h3 PsiOmega.chi3 ^ 2 = 1 := by
      rw [← map_pow, MulChar.isQuadratic_iff_sq_eq_one.1 PsiOmega.chi3_isQuadratic, map_one]
    apply (changeLevel_eq_one_iff hqN).1
    rw [map_pow, hc, inv_pow, hc2, inv_one]
  have hm0 : ((4 * q : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (by have := NeZero.ne q; positivity)
  have : NeZero ((4 * q : ℕ) : 𝓞 K) := ⟨hm0⟩
  have : Fact ((4 : 𝓞 K) ∣ ((4 * q : ℕ) : 𝓞 K)) := ⟨⟨q, by push_cast; ring⟩⟩
  have hc : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 →
      (fun I => nuChi χ (natCast_dvd_four_mul q) (Ideal.Quotient.mk _ (pgen I))) I * sym6 1 I =
        changeLevel hqN χ (absNorm I) := by
    intro I hI
    simp only [sym6_one_left hI, mul_one]
    rw [nuChi_pgen χ hI, changeLevel_three_mul_apply χ hqN hI]
  have hL := (ne_zero_of_famTwist h3 (fun _ hσ => meanSquareNu (nuChi χ (natCast_dvd_four_mul q)) hσ)
    one_ne_zero hc hχ' hχ'3 hs).1
  rw [LFunction_changeLevel hqN χ (Or.inl hχ1)] at hL
  exact left_ne_zero_of_mul hL

/-- **The half-plane `Re s > 11/12` for every Dirichlet character** (door 5(b)): for every modulus `q ≥ 1`, every
Dirichlet character `χ` mod `q` and every `s` with `Re s > 11/12`, `L(s, χ) ≠ 0`, the trivial character excepted
at `s = 1`. The real characters are round 477's. -/
theorem LFunction_ne_zero_of_re_gt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 11 / 12 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : LFunction χ s ≠ 0 := by
  by_cases hχ2 : χ ^ 2 = 1
  · exact RealChar.LFunction_ne_zero_of_isQuadratic (MulChar.isQuadratic_iff_sq_eq_one.2 hχ2) hs hχs
  exact LFunction_ne_zero_of_sq_ne_one hχ2 hs

end Eis

#print axioms Eis.normZ_mul
#print axioms Eis.normZ_one
#print axioms Eis.intCast_dvd_of_dvd
#print axioms Eis.normZ_congr
#print axioms Eis.isUnit_mk_of_coprime
#print axioms Eis.mk_liftM
#print axioms Eis.normZ_liftM_mk
#print axioms Eis.nuChi_mk
#print axioms Eis.natCast_dvd_four_mul
#print axioms Eis.nuChi_pgen
#print axioms Eis.changeLevel_three_mul_apply
#print axioms Eis.LFunction_ne_zero_of_sq_ne_one
#print axioms Eis.LFunction_ne_zero_of_re_gt
