import HalfPlaneTwistMean

/-!
# Round 477: every real Dirichlet L-function is zero-free on `Re s > 11/12`

Step 5 of round 471's plan, the real primitive characters, and with it step 4 for every real
character.

* **Real characters in `ℤ`** (`toInt`, `isQuadratic_of_im`): a complex Dirichlet character with
  real values takes only the values `0` and `±1`, and is the image of a character with values in
  `ℤ`.
* **Conductors from the unit kernel** (`isPrimitive_iff_of_ker`): two characters mod `q`, with
  values in any rings, that take the value `1` at the same units factor through the same levels
  (Mathlib's `factorsThrough_iff_ker_unitsMap`), so one is primitive if and only if the other is.
* **`τ(χ, e)·τ(χ⁻¹, e) = χ(−1)·q`** (`gaussSum_mul_gaussSum_inv`) for a primitive `χ` mod `q`, `q`
  composite allowed, and a primitive additive character `e` of `ℤ/q`, over any domain: sum Mathlib's
  `gaussSum_mulShift_of_isPrimitive`, `τ(χ, e(y·)) = χ⁻¹(y)τ(χ, e)`, against `e(y)`, and evaluate
  the inner sums `Σ_y e(y(x + 1))` by `AddChar.sum_mulShift`. For quadratic `χ`,
  `τ(χ, e)² = χ(−1)·q`.
* **`χ(p) = J(χ(−1)q | p)`** (`apply_prime_eq_jacobiSym`) for a primitive quadratic `χ` mod `q`
  with values in `ℤ` and an odd prime `p ∤ q`. Read `χ` in the cyclotomic field `F` over `ZMod p`
  that carries Mathlib's primitive additive character of `ℤ/q` (`AddChar.primitiveZModChar`, which
  needs `p ∤ q`); it stays primitive and quadratic there, as `ringChar F = p ≠ 2`. Mathlib's
  `Char.card_pow_char_pow`, the Frobenius `τ^p = χ(p)τ` in a form whose docstring says it "can be
  used when `R` is not a field", gives `(χ(−1)q)^{(p−1)/2} = χ(p)` in `F`, and round 474's Euler
  criterion `intCast_pow_card_div_two` in `ZMod p` turns the left side into `J(χ(−1)q | p)`. By
  multiplicativity, `χ(n) = J(χ(−1)q | n)` for every `n` prime to `2q` (`apply_eq_jacobiSym`).
* **The half-plane for primitive characters** (`LFunction_ne_zero_of_isPrimitive`): for a primitive
  quadratic `χ ≠ 1` mod `q`, the lift `χ'` of `χ` to level `6q` agrees with `J(d | ·)`,
  `d = χ(−1)q`, at every `n` prime to `6` (both vanish when `(n, q) > 1`), so round 476's
  `ne_zero_of_jacobiTwist` gives `L(s, χ') ≠ 0` on `Re s > 11/12` unless `χ'χ₋₃ = 1`, and Mathlib's
  `LFunction_changeLevel`, `L(s, χ') = L(s, χ)·∏_{p ∣ 6q}(1 − χ(p)p^{−s})`, returns to `L(s, χ)`. If
  `χ'χ₋₃ = 1`, `χ'` is the lift of `χ₋₃`; the conductors give `q = 3`, and `χ = χ₋₃`
  (`LFunction_eq_chi3`), which is round 466's.
* **Every real character** (`LFunction_ne_zero_of_isQuadratic`, `LFunction_ne_zero_of_real`):
  through Mathlib's `primitiveCharacter`, with the Euler factors `1 − ψ(p)p^{−s}` nonzero for
  `Re s > 0` (`one_sub_mul_cpow_ne_zero`); the trivial character, away from `s = 1`, is round 466's
  `ζ` times such factors (Mathlib's `LFunctionTrivChar_eq_mul_riemannZeta`).
* **The release's `SiegelZeros.lean` statements** (`dirichletRealZeroBound`,
  `exists_absolute_real_zero_gap`), with `c = (log 3)/12`: a real zero `β ∈ (0, 1)` has `β ≤ 11/12`,
  and `log q ≥ log 3`.
-/

open Complex DirichletCharacter

namespace Eis

namespace RealChar

/-! ### Real characters as characters with values in `ℤ` -/

open Classical in
/-- The integer `1`, `−1` or `0` named by a complex number (`0` off `{1, −1}`). -/
noncomputable def intOf (z : ℂ) : ℤ := if z = 1 then 1 else if z = -1 then -1 else 0

theorem intOf_cast {z : ℂ} (hz : z = 0 ∨ z = 1 ∨ z = -1) : (intOf z : ℂ) = z := by
  rcases hz with rfl | rfl | rfl <;> norm_num [intOf]

variable {q : ℕ}

/-- A quadratic character with complex values, as a character with values in `ℤ`. -/
noncomputable def toInt (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) :
    DirichletCharacter ℤ q where
  toFun a := intOf (χ a)
  map_one' := by simp [intOf]
  map_mul' a b := Int.cast_injective (α := ℂ) (by
    push_cast
    rw [intOf_cast (hχ _), intOf_cast (hχ _), intOf_cast (hχ _), map_mul])
  map_nonunit' a ha := by simp [intOf, χ.map_nonunit ha]

theorem toInt_cast {χ : DirichletCharacter ℂ q} (hχ : χ.IsQuadratic) (a : ZMod q) :
    ((toInt χ hχ a : ℤ) : ℂ) = χ a :=
  intOf_cast (hχ a)

theorem isQuadratic_toInt {χ : DirichletCharacter ℂ q} (hχ : χ.IsQuadratic) :
    (toInt χ hχ).IsQuadratic := fun a => by
  show intOf (χ a) = 0 ∨ intOf (χ a) = 1 ∨ intOf (χ a) = -1
  unfold intOf
  split_ifs <;> simp

/-- A Dirichlet character with real values is quadratic. -/
theorem isQuadratic_of_im {χ : DirichletCharacter ℂ q} (h : ∀ a, (χ a).im = 0) :
    χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · right
    have h1 : ‖χ a‖ = 1 := by simpa using χ.unit_norm_eq_one ha.unit
    have hre : χ a = ((χ a).re : ℂ) := Complex.ext rfl (by simp [h a])
    rw [hre, Complex.norm_real, Real.norm_eq_abs] at h1
    rcases abs_eq zero_le_one |>.1 h1 with h' | h'
    · left; rw [hre, h']; simp
    · right; rw [hre, h']; simp
  · left; exact χ.map_nonunit ha

/-! ### Conductors are determined by the unit kernel -/

section Conductor

variable {R₁ R₂ : Type*} [CommMonoidWithZero R₁] [CommMonoidWithZero R₂] [NeZero q]
  {χ₁ : DirichletCharacter R₁ q} {χ₂ : DirichletCharacter R₂ q}

/-- Two characters mod `q` that take the value `1` at the same units factor through the same
levels. -/
theorem factorsThrough_iff_of_ker (h : ∀ u : (ZMod q)ˣ, χ₁ u = 1 ↔ χ₂ u = 1) (d : ℕ) :
    χ₁.FactorsThrough d ↔ χ₂.FactorsThrough d := by
  have hker : χ₁.toUnitHom.ker = χ₂.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
    exact h u
  constructor
  · intro hd
    have hdvd := hd.dvd
    rw [factorsThrough_iff_ker_unitsMap hdvd] at hd
    rw [factorsThrough_iff_ker_unitsMap hdvd, ← hker]
    exact hd
  · intro hd
    have hdvd := hd.dvd
    rw [factorsThrough_iff_ker_unitsMap hdvd] at hd
    rw [factorsThrough_iff_ker_unitsMap hdvd, hker]
    exact hd

theorem conductor_eq_of_ker (h : ∀ u : (ZMod q)ˣ, χ₁ u = 1 ↔ χ₂ u = 1) :
    χ₁.conductor = χ₂.conductor := by
  show sInf χ₁.conductorSet = sInf χ₂.conductorSet
  congr 1
  ext d
  exact factorsThrough_iff_of_ker h d

theorem isPrimitive_iff_of_ker (h : ∀ u : (ZMod q)ˣ, χ₁ u = 1 ↔ χ₂ u = 1) :
    χ₁.IsPrimitive ↔ χ₂.IsPrimitive := by
  rw [isPrimitive_def, isPrimitive_def, conductor_eq_of_ker h]

end Conductor

/-! ### The Gauss sum of a primitive character times that of its inverse -/

section Gauss

variable [NeZero q] {R : Type*} [CommRing R] [IsDomain R]

/-- **`τ(χ, e)·τ(χ⁻¹, e) = χ(−1)·q`** for a primitive Dirichlet character `χ` mod `q` and a
primitive additive character `e` of `ℤ/q`, over any domain. -/
theorem gaussSum_mul_gaussSum_inv {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e = χ (-1) * q := by
  classical
  have h1 : ∑ y : ZMod q, gaussSum χ (e.mulShift y) * e y = gaussSum χ e * gaussSum χ⁻¹ e := by
    have hg : gaussSum χ⁻¹ e = ∑ y, χ⁻¹ y * e y := rfl
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [gaussSum_mulShift_of_isPrimitive e hχ]
    ring
  have hin : ∀ x : ZMod q, ∑ y : ZMod q, χ x * e.mulShift y x * e y =
      χ x * (if x + 1 = 0 then (q : R) else 0) := by
    intro x
    have hs := AddChar.sum_mulShift (x + 1) he
    rw [ZMod.card] at hs
    push_cast at hs
    rw [← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddChar.mulShift_apply, mul_add, mul_one, AddChar.map_add_eq_mul, mul_assoc, mul_comm y x]
  have h2 : ∑ y : ZMod q, gaussSum χ (e.mulShift y) * e y = χ (-1) * q := by
    simp only [gaussSum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [hin]
    have hite : ∀ x : ZMod q, χ x * (if x + 1 = 0 then (q : R) else 0) =
        if x = -1 then χ (-1) * q else 0 := by
      intro x
      by_cases hx : x = -1
      · simp [hx]
      · have h0 : x + 1 ≠ 0 := fun h => hx (eq_neg_of_add_eq_zero_left h)
        simp [hx, h0]
    simp_rw [hite]
    rw [Finset.sum_ite_eq' Finset.univ (-1 : ZMod q)]
    simp
  rw [← h1, h2]

/-- **`τ(χ, e)² = χ(−1)·q`** for a primitive quadratic character. -/
theorem gaussSum_sq_of_isQuadratic {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * q := by
  rw [sq]
  nth_rewrite 2 [← hq.inv]
  exact gaussSum_mul_gaussSum_inv hχ he

end Gauss

/-! ### The value at an odd prime: `χ(p) = J(χ(−1)q | p)` -/

section Frobenius

variable [NeZero q]

/-- **Values of a primitive quadratic character at odd primes.** For a primitive quadratic character
`χ` mod `q` with values in `ℤ` and an odd prime `p ∤ q`: `χ(p) = J(χ(−1)·q | p)`. -/
theorem apply_prime_eq_jacobiSym {χ : DirichletCharacter ℤ q} (hq : χ.IsQuadratic)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) :
    χ p = jacobiSym (χ (-1) * q) p := by
  have := Fact.mk hp
  set n : ℕ+ := ⟨q, NeZero.pos q⟩
  have hn : ((n : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpq
  set ψ := AddChar.primitiveZModChar n (ZMod p) hn
  set F := CyclotomicField ψ.n (ZMod p)
  have : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
  set f := Int.castRingHom F
  set χp : DirichletCharacter F q := χ.ringHomComp f
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hker : ∀ u : (ZMod q)ˣ, χ u = 1 ↔ χp u = 1 := by
    intro u
    simp only [χp, MulChar.ringHomComp_apply, f, eq_intCast]
    constructor
    · intro h; rw [h]; simp
    · intro h
      exact Int.cast_injOn_of_ringChar_ne_two hF2 (hq u) (by simp) (by rw [h]; simp)
  have hprim : χp.IsPrimitive := (isPrimitive_iff_of_ker hker).1 hχ
  have hqp : χp.IsQuadratic := hq.comp f
  have hg : gaussSum χp ψ.char ^ 2 = χp (-1) * Fintype.card (ZMod q) := by
    rw [ZMod.card]
    exact gaussSum_sq_of_isQuadratic hprim hqp ψ.prim
  have hunit : IsUnit (p : ZMod q) :=
    (ZMod.isUnit_iff_coprime p q).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
  have key := Char.card_pow_char_pow hqp ψ.char p 1 hunit hp2 hg
  rw [pow_one, pow_one, ZMod.card] at key
  simp only [χp, MulChar.ringHomComp_apply, f, eq_intCast] at key
  have hz := intCast_pow_card_div_two (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    (χ (-1) * q)
  rw [ZMod.card] at hz
  have e2 : ((χ p : ℤ) : F) = ((jacobiSym (χ (-1) * q) p : ℤ) : F) := by
    rw [← key]
    have := congrArg (algebraMap (ZMod p) F) hz
    simpa [map_pow, map_intCast] using this
  exact Int.cast_injOn_of_ringChar_ne_two hF2 (hq p) (jacobiSym.trichotomy _ _) e2

/-- **Every value prime to `2q`**: `χ(n) = J(χ(−1)·q | n)` for `n` prime to `2` and to `q`. -/
theorem apply_eq_jacobiSym {χ : DirichletCharacter ℤ q} (hq : χ.IsQuadratic) (hχ : χ.IsPrimitive)
    {n : ℕ} (hn2 : n.Coprime 2) (hnq : n.Coprime q) : χ n = jacobiSym (χ (-1) * q) n := by
  induction n using induction_on_primes with
  | zero => exact absurd hn2 (by decide)
  | one => simp
  | prime_mul p a hp ih =>
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd (Nat.Coprime.coprime_dvd_left (dvd_mul_right 2 a) hn2) (by decide)
    have hpq : ¬ p ∣ q := fun h => hp.one_lt.ne'
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_right p a) hnq) h)
    have ha2 : a.Coprime 2 := Nat.Coprime.coprime_dvd_left (dvd_mul_left a p) hn2
    have haq : a.Coprime q := Nat.Coprime.coprime_dvd_left (dvd_mul_left a p) hnq
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero a := ⟨fun h => by subst h; exact absurd ha2 (by decide)⟩
    rw [Nat.cast_mul, map_mul, ih ha2 haq, apply_prime_eq_jacobiSym hq hχ hp hp2 hpq,
      jacobiSym.mul_right]

end Frobenius

/-! ### Every real character -/

section Real

open HalfPlaneS0

/-- If the lift of a primitive `χ` mod `q` to level `N` is the lift of `χ₋₃`, then `q = 3` and
`χ = χ₋₃`, so `L(s, χ) = L(s, χ₋₃)`. -/
theorem LFunction_eq_chi3 {q N : ℕ} [NeZero q] [NeZero N] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hqN : q ∣ N) (h3 : 3 ∣ N)
    (h : changeLevel hqN χ = changeLevel h3 PsiOmega.chi3) (s : ℂ) :
    LFunction χ s = LFunction PsiOmega.chi3 s := by
  have hq3 : q = 3 := by
    have e1 := conductor_changeLevel (χ := χ) hqN
    rw [h, conductor_changeLevel, (isPrimitive_def _).1 PsiOmega.chi3_isPrimitive,
      (isPrimitive_def _).1 hprim] at e1
    exact e1.symm
  subst hq3
  rw [changeLevel_injective hqN h]

/-- `χ(−1) = ±1`. -/
theorem toInt_neg_one {χ : DirichletCharacter ℂ q} (hq : χ.IsQuadratic) :
    toInt χ hq (-1) = 1 ∨ toInt χ hq (-1) = -1 := by
  have h0 : toInt χ hq (-1) ≠ 0 := (isUnit_one.neg.map (toInt χ hq)).ne_zero
  rcases isQuadratic_toInt hq (-1) with h | h | h
  · exact absurd h h0
  · exact Or.inl h
  · exact Or.inr h

/-- **The half-plane for a real primitive character**: `L(s, χ) ≠ 0` on `Re s > 11/12` for every
primitive quadratic `χ ≠ 1`. -/
theorem LFunction_ne_zero_of_isPrimitive [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ} (hs : 11 / 12 < s.re) :
    LFunction χ s ≠ 0 := by
  have hqN : q ∣ 6 * q := Dvd.intro_left 6 rfl
  have h3 : 3 ∣ 6 * q := Dvd.dvd.mul_right (by norm_num : 3 ∣ 6) q
  have : NeZero (6 * q) := ⟨by have := NeZero.ne q; positivity⟩
  have hker : ∀ u : (ZMod q)ˣ, χ u = 1 ↔ toInt χ hq u = 1 := by
    intro u
    rw [← toInt_cast hq]
    exact_mod_cast Iff.rfl
  have hχz : (toInt χ hq).IsPrimitive := (isPrimitive_iff_of_ker hker).1 hprim
  have hd : toInt χ hq (-1) * (q : ℤ) ≠ 0 := by
    have := NeZero.ne q
    rcases toInt_neg_one hq with h | h <;> rw [h] <;> simpa using this
  have hχd : ∀ n : ℕ, n.Coprime 6 →
      changeLevel hqN χ n = jacobiSym (toInt χ hq (-1) * q) n := by
    intro n hn
    by_cases hnq : n.Coprime q
    · have hnN : IsCoprime (n : ℤ) ((6 * q : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_right hn hnq)
      have e := changeLevel_eq_cast_of_dvd' χ hqN hnN
      simp only [Int.cast_natCast] at e
      rw [e, ← toInt_cast hq, apply_eq_jacobiSym (isQuadratic_toInt hq) hχz
        (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hn) hnq]
    · have : NeZero n := ⟨fun h => by subst h; exact absurd hn (by decide)⟩
      have h1 : changeLevel hqN χ n = 0 := by
        apply MulChar.map_nonunit
        rw [ZMod.isUnit_iff_coprime]
        exact fun h => hnq (Nat.Coprime.coprime_dvd_right hqN h)
      have h2 : jacobiSym (toInt χ hq (-1) * q) n = 0 := by
        rw [jacobiSym.eq_zero_iff_not_coprime]
        intro h
        apply hnq
        rcases toInt_neg_one hq with h' | h' <;>
          · rw [h'] at h
            simpa [Int.gcd, Nat.coprime_comm] using h
      rw [h1, h2]
      simp
  by_cases hc : mulChi3 h3 (changeLevel hqN χ) = 1
  · have e : changeLevel hqN χ = changeLevel h3 PsiOmega.chi3 := by
      have := eq_inv_of_mul_eq_one_left hc
      rw [this, ← map_inv, PsiOmega.chi3_isQuadratic.inv]
    rw [LFunction_eq_chi3 hprim hqN h3 e s]
    exact (ne_zero_of_re_gt_eleven_twelfths hs).2
  · have hχ' : changeLevel hqN χ ≠ 1 := fun h => hχ ((changeLevel_eq_one_iff hqN).1 h)
    have hL := (ne_zero_of_jacobiTwist h3 hd hχd hχ' hc hs).1
    rw [LFunction_changeLevel hqN χ (Or.inl hχ)] at hL
    exact left_ne_zero_of_mul hL

/-- An Euler factor `1 − a·p^{−s}` with `|a| ≤ 1`, `p` prime and `Re s > 0` does not vanish. -/
theorem one_sub_mul_cpow_ne_zero {p : ℕ} (hp : p.Prime) {a : ℂ} (ha : ‖a‖ ≤ 1) {s : ℂ}
    (hs : 0 < s.re) : 1 - a * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : a * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have hlt : ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
    have : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
    calc ‖a‖ * (p : ℝ) ^ (-s.re) ≤ 1 * (p : ℝ) ^ (-s.re) := by gcongr
      _ < 1 := by rw [one_mul]; exact this
  rw [h1, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- **Every real Dirichlet L-function is zero-free on `Re s > 11/12`**: for every quadratic
Dirichlet character `χ` (any modulus, primitive or not) and `Re s > 11/12`, `L(s, χ) ≠ 0`, the
trivial character excepted at `s = 1`. -/
theorem LFunction_ne_zero_of_isQuadratic [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : χ.IsQuadratic) {s : ℂ} (hs : 11 / 12 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  by_cases hχ : χ = 1
  · subst hχ
    have hs1 : s ≠ 1 := hχs.resolve_left (not_not.2 rfl)
    rw [show LFunction (1 : DirichletCharacter ℂ q) s = LFunctionTrivChar q s from rfl,
      LFunctionTrivChar_eq_mul_riemannZeta hs1]
    refine mul_ne_zero ?_ (ne_zero_of_re_gt_eleven_twelfths hs).1
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    simpa using one_sub_mul_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp) (a := 1) (by simp) hs0
  · have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    have hψ1 : χ.primitiveCharacter ≠ 1 := by
      intro h
      apply hχ
      rw [← changeLevel_primitiveCharacter χ, h, map_one]
    have hψq : χ.primitiveCharacter.IsQuadratic := by
      rw [MulChar.isQuadratic_iff_sq_eq_one] at hq ⊢
      apply (changeLevel_eq_one_iff (conductor_dvd_level χ)).1
      rw [map_pow, changeLevel_primitiveCharacter, hq]
    rw [← changeLevel_primitiveCharacter χ,
      LFunction_changeLevel (conductor_dvd_level χ) _ (Or.inl hψ1)]
    refine mul_ne_zero (LFunction_ne_zero_of_isPrimitive hψq (primitiveCharacter_isPrimitive χ)
      hψ1 hs) ?_
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact one_sub_mul_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp)
      (DirichletCharacter.norm_le_one _ _) hs0

/-- **Every Dirichlet character with real values**: the same, with "real" read as `Im χ(a) = 0`. -/
theorem LFunction_ne_zero_of_real [NeZero q] {χ : DirichletCharacter ℂ q}
    (hre : ∀ a, (χ a).im = 0) {s : ℂ} (hs : 11 / 12 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_isQuadratic (isQuadratic_of_im hre) hs hχs

/-- **The release's `dirichletRealZeroBound_proof` statement**, with `c = (log 3)/12`: a real zero
`β ∈ (0, 1)` of `L(s, χ)` for a primitive real character `χ ≠ 1` mod `q ≥ 3` has
`(1 − β)·log q ≥ (log 3)/12`. -/
theorem dirichletRealZeroBound :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ) := by
  refine ⟨Real.log 3 / 12, div_pos (Real.log_pos (by norm_num)) (by norm_num),
    fun q _ hq3 χ _ hχ hre β ⟨_, _, hL⟩ => ?_⟩
  have hβ : β ≤ 11 / 12 := by
    rcases le_or_gt β (11 / 12) with h | h
    · exact h
    · exact absurd hL (LFunction_ne_zero_of_real hre (by simpa using h) (Or.inl hχ))
  have hlog : Real.log 3 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β - 1 / 12)
    (by linarith : (0 : ℝ) ≤ Real.log q)]

/-- **The release's `exists_absolute_real_zero_gap` statement**, the same with the hypotheses on `β`
curried. -/
theorem exists_absolute_real_zero_gap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  obtain ⟨c, hc, h⟩ := dirichletRealZeroBound
  exact ⟨c, hc, fun q _ hq3 χ hprim hχ hre β h0 h1 hL => h q hq3 χ hprim hχ hre β ⟨h0, h1, hL⟩⟩

end Real

end RealChar

end Eis

#print axioms Eis.RealChar.isQuadratic_of_im
#print axioms Eis.RealChar.isPrimitive_iff_of_ker
#print axioms Eis.RealChar.gaussSum_mul_gaussSum_inv
#print axioms Eis.RealChar.gaussSum_sq_of_isQuadratic
#print axioms Eis.RealChar.apply_prime_eq_jacobiSym
#print axioms Eis.RealChar.apply_eq_jacobiSym
#print axioms Eis.RealChar.LFunction_eq_chi3
#print axioms Eis.RealChar.LFunction_ne_zero_of_isPrimitive
#print axioms Eis.RealChar.one_sub_mul_cpow_ne_zero
#print axioms Eis.RealChar.LFunction_ne_zero_of_isQuadratic
#print axioms Eis.RealChar.LFunction_ne_zero_of_real
#print axioms Eis.RealChar.dirichletRealZeroBound
#print axioms Eis.RealChar.exists_absolute_real_zero_gap
