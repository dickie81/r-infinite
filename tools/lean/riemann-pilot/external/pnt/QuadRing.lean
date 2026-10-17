/-
# Round 486: the ring of integers of a quadratic field

Imports Mathlib only.

Plain statement. Let `K` be a number field of degree `2` and `s ∈ K` with `s² = d`, `d` a squarefree integer
other than `1`. Then `K = ℚ + ℚs` (`exists_eq`), and `a + bs` (`a, b ∈ ℚ`) is an algebraic integer exactly when
`2a` and `2b` are integers `A`, `B` with `4 ∣ A² − dB²` (`isIntegral_iff`). So:

* if `d ≡ 1 (mod 4)`, `𝓞 K = ℤ[θ]` with `θ = (1 + s)/2` (`span_θ₁`, `basis₁`, `adjoin_θ₁`), the minimal polynomial
  of `θ` over `ℤ` is `X² − X − (d − 1)/4` (`minpoly_θ₁`), and the discriminant is `D_K = d` (`discr_θ₁`);
* if `d ≡ 2, 3 (mod 4)`, `𝓞 K = ℤ[s]` (`span_θ₂`, `basis₂`, `adjoin_θ₂`), the minimal polynomial of `s` over `ℤ` is
  `X² − d` (`minpoly_θ₂`), and `D_K = 4d` (`discr_θ₂`).

Every quadratic field contains such an `s` (`exists_sqrt`).

* `int_of_mul_sq`: if `d` is squarefree and `dr² ∈ ℤ`, then `r ∈ ℤ` (the denominator's square divides `d`).
* `minpoly_eq`: for `b ≠ 0`, the minimal polynomial of `a + bs` over `ℚ` is `X² − 2aX + (a² − db²)`; for an
  algebraic integer its coefficients are integers (Mathlib's `minpoly.isIntegrallyClosed_eq_field_fractions'`),
  so `2a ∈ ℤ`, `a² − db² ∈ ℤ`, and then `d(2b)² ∈ ℤ` gives `2b ∈ ℤ`.
* `two_dvd_sub`, `two_dvd_both`: the residues of `A² − dB²` mod `4` (by `decide` in `ZMod 4`) force `A ≡ B (mod 2)`
  for `d ≡ 1` and `A ≡ B ≡ 0 (mod 2)` for `d ≡ 2, 3 (mod 4)`.
* `discr_eq_of_basis`: if `(1, θ)` is a `ℤ`-basis of `𝓞 K` with `θ² = c + eθ`, then `D_K = 4c + e²`, from the
  traces `Tr 1 = 2`, `Tr θ = e`, `Tr θ² = 2c + e²` (Mathlib's `Algebra.trace_eq_matrix_trace`) and
  Mathlib's `NumberField.discr_eq_discr`.
* `exists_sqrt`: complete the square in the minimal polynomial of an element outside `ℚ`, clear denominators,
  and write the integer as `f²d` with `d` squarefree (Mathlib's `exists_sq_mul_squarefree`).
-/
import Mathlib

open NumberField Polynomial

namespace QuadRing

/-! ### Rationals with `d r² ∈ ℤ` -/

/-- If `d` is squarefree and `d r² ∈ ℤ`, then `r ∈ ℤ`. -/
theorem int_of_mul_sq {d : ℤ} (hd : Squarefree d) {r : ℚ} {k : ℤ} (h : (d : ℚ) * r ^ 2 = k) :
    ∃ m : ℤ, r = m := by
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hr : r = r.num / r.den := (Rat.num_div_den r).symm
  have h2 : d * r.num ^ 2 = k * (r.den : ℤ) ^ 2 := by
    have : (d : ℚ) * (r.num : ℚ) ^ 2 = (k : ℚ) * ((r.den : ℤ) : ℚ) ^ 2 := by
      rw [hr] at h
      field_simp at h
      push_cast
      linarith
    exact_mod_cast this
  have hcop1 : IsCoprime (r.den : ℤ) r.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact r.reduced
  have hcop : IsCoprime ((r.den : ℤ) ^ 2) (r.num ^ 2) := hcop1.pow
  have hdvd : (r.den : ℤ) ^ 2 ∣ d := by
    have : (r.den : ℤ) ^ 2 ∣ d * r.num ^ 2 := ⟨k, by rw [h2]; ring⟩
    exact hcop.dvd_of_dvd_mul_right this
  have hu : IsUnit (r.den : ℤ) := hd _ (by rw [← sq]; exact hdvd)
  have h1 : r.den = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h
    · exact_mod_cast h
    · have : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
      omega
  exact ⟨r.num, by rw [hr, h1]; simp⟩

/-- A squarefree `d ≠ 1` is not the square of a rational. -/
theorem not_sq {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) (r : ℚ) : r ^ 2 ≠ d := by
  intro h
  obtain ⟨m, rfl⟩ := int_of_mul_sq squarefree_one (k := d) (by rw [Int.cast_one, one_mul, h])
  have h' : m * m = d := by exact_mod_cast (by rw [← sq]; exact_mod_cast h)
  have hu : IsUnit m := hd m ⟨1, by rw [mul_one, h']⟩
  rcases Int.isUnit_iff.1 hu with rfl | rfl <;> simp at h' <;> exact hd1 h'.symm

variable {K : Type*} [Field K] [NumberField K] {d : ℤ} {s : K}

/-! ### `K = ℚ + ℚs` -/

section Basis

variable (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
include hd hd1 hs

/-- `s ∉ ℚ`. -/
theorem not_mem_range : s ∉ Set.range (algebraMap ℚ K) := by
  rintro ⟨r, rfl⟩
  apply not_sq hd hd1 r
  have : algebraMap ℚ K (r ^ 2) = algebraMap ℚ K d := by rw [map_pow, hs]; simp
  exact (algebraMap ℚ K).injective this

/-- `1` and `s` are linearly independent over `ℚ`. -/
theorem linearIndependent : LinearIndependent ℚ ![(1 : K), s] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  by_cases hb : b = 0
  · subst hb
    simp only [zero_smul, add_zero] at h
    exact ⟨by simpa using h, rfl⟩
  · exfalso
    apply not_mem_range hd hd1 hs
    have hb' : (algebraMap ℚ K b) ≠ 0 := by simpa using hb
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
    have : s = algebraMap ℚ K (-a / b) := by
      rw [map_div₀, map_neg, eq_div_iff hb']
      linear_combination h
    exact ⟨-a / b, this.symm⟩

variable (hK : Module.finrank ℚ K = 2)
include hK

/-- **Every element of `K` is `a + bs`.** -/
theorem exists_eq (x : K) : ∃ a b : ℚ, x = a + b * s := by
  have hspan := (linearIndependent hd hd1 hs).span_eq_top_of_card_eq_finrank' (by simp [hK])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), s]) := by rw [hspan]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hx
  obtain ⟨a, b, h⟩ := hx
  refine ⟨a, b, ?_⟩
  rw [← h, Algebra.smul_def, Algebra.smul_def, mul_one]
  rfl

end Basis

/-! ### The minimal polynomial of `a + bs` -/

section Minpoly

variable (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
include hd hd1 hs

/-- `X² − 2aX + (a² − db²)`. -/
noncomputable def quadPoly (a b : ℚ) : ℚ[X] := X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2)

omit hd hd1 hs in
theorem quadPoly_monic (a b : ℚ) : (quadPoly (d := d) a b).Monic := by
  unfold quadPoly
  monicity!

omit hd hd1 hs in
theorem quadPoly_natDegree (a b : ℚ) : (quadPoly (d := d) a b).natDegree = 2 := by
  unfold quadPoly
  compute_degree!

omit hd hd1 in
theorem aeval_quadPoly (a b : ℚ) : aeval ((a : K) + b * s) (quadPoly (d := d) a b) = 0 := by
  simp only [quadPoly, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    eq_ratCast]
  push_cast
  linear_combination (b : K) ^ 2 * hs

/-- **The minimal polynomial of `a + bs`, `b ≠ 0`, is `X² − 2aX + (a² − db²)`.** -/
theorem minpoly_eq {a b : ℚ} (hb : b ≠ 0) : minpoly ℚ ((a : K) + b * s) = quadPoly (d := d) a b := by
  have hx : ((a : K) + b * s) ∉ (algebraMap ℚ K).range := by
    rintro ⟨r, hr⟩
    apply not_mem_range hd hd1 hs
    refine ⟨(r - a) / b, ?_⟩
    have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
    rw [map_div₀, map_sub, hr, eq_ratCast, eq_ratCast]
    field_simp
    ring
  have hint : IsIntegral ℚ ((a : K) + b * s) := .of_finite ℚ _
  have hdvd : minpoly ℚ ((a : K) + b * s) ∣ quadPoly (d := d) a b :=
    minpoly.dvd ℚ _ (aeval_quadPoly hs a b)
  have hdeg1 : (minpoly ℚ ((a : K) + b * s)).natDegree ≠ 1 := fun h ↦ hx (minpoly.natDegree_eq_one_iff.1 h)
  have hdeg0 : 0 < (minpoly ℚ ((a : K) + b * s)).natDegree := minpoly.natDegree_pos hint
  have hle : (minpoly ℚ ((a : K) + b * s)).natDegree ≤ 2 := by
    rw [← quadPoly_natDegree (d := d) a b]
    exact natDegree_le_of_dvd hdvd (quadPoly_monic a b).ne_zero
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (quadPoly_monic a b) hdvd
    (by rw [quadPoly_natDegree]; omega)).symm

end Minpoly

/-! ### Residues mod `4` -/

theorem zmod4_eq_zero {x : ℤ} (h : 4 ∣ x) : ((x : ℤ) : ZMod 4) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x 4).2 (by exact_mod_cast h)

theorem dvd_of_zmod4 {x : ℤ} (h : ((x : ℤ) : ZMod 4) = 0) : 4 ∣ x := by
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x 4).1 h

theorem zmod4_of_emod {d r : ℤ} (h : d % 4 = r) : ((d : ℤ) : ZMod 4) = ((r : ℤ) : ZMod 4) := by
  rw [← ZMod.intCast_mod d 4]
  push_cast [h]
  rfl

/-- For `d ≡ 1 (mod 4)`, `4 ∣ A² − dB²` forces `A ≡ B (mod 2)`. -/
theorem two_dvd_sub {A B d : ℤ} (hd : d % 4 = 1) (h : 4 ∣ A ^ 2 - d * B ^ 2) : 2 ∣ A - B := by
  have h1 := zmod4_eq_zero h
  push_cast [zmod4_of_emod hd] at h1
  have key : ∀ x y : ZMod 4, x ^ 2 - (1 : ℤ) * y ^ 2 = 0 → x - y = 0 ∨ x - y - 2 = 0 := by decide
  rcases key _ _ h1 with h2 | h2
  · obtain ⟨k, hk⟩ := dvd_of_zmod4 (x := A - B) (by push_cast; exact h2)
    exact ⟨2 * k, by rw [hk]; ring⟩
  · obtain ⟨k, hk⟩ := dvd_of_zmod4 (x := A - B - 2) (by push_cast; exact h2)
    exact ⟨2 * k + 1, by linarith⟩

/-- For `d ≡ 2, 3 (mod 4)`, `4 ∣ A² − dB²` forces `A` and `B` even. -/
theorem two_dvd_both {A B d : ℤ} (hd : d % 4 = 2 ∨ d % 4 = 3) (h : 4 ∣ A ^ 2 - d * B ^ 2) :
    2 ∣ A ∧ 2 ∣ B := by
  have h1 := zmod4_eq_zero h
  have key2 : ∀ x y : ZMod 4, x ^ 2 - (2 : ℤ) * y ^ 2 = 0 →
      (x = 0 ∨ x - 2 = 0) ∧ (y = 0 ∨ y - 2 = 0) := by decide
  have key3 : ∀ x y : ZMod 4, x ^ 2 - (3 : ℤ) * y ^ 2 = 0 →
      (x = 0 ∨ x - 2 = 0) ∧ (y = 0 ∨ y - 2 = 0) := by decide
  have hev : ∀ z : ℤ, ((z : ℤ) : ZMod 4) = 0 ∨ ((z : ℤ) : ZMod 4) - 2 = 0 → 2 ∣ z := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨k, hk⟩ := dvd_of_zmod4 hz
      exact ⟨2 * k, by rw [hk]; ring⟩
    · obtain ⟨k, hk⟩ := dvd_of_zmod4 (x := z - 2) (by push_cast; exact hz)
      exact ⟨2 * k + 1, by linarith⟩
  rcases hd with hd | hd
  · push_cast [zmod4_of_emod hd] at h1
    obtain ⟨hA, hB⟩ := key2 _ _ h1
    exact ⟨hev A hA, hev B hB⟩
  · push_cast [zmod4_of_emod hd] at h1
    obtain ⟨hA, hB⟩ := key3 _ _ h1
    exact ⟨hev A hA, hev B hB⟩

/-! ### Integrality -/

section Integral

variable (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d)
include hd hd1 hs

omit hd hd1 in
/-- `a + bs` with `2a = A`, `2b = B` and `4 ∣ A² − dB²` is integral over `ℤ`. -/
theorem isIntegral_of {a b : ℚ} {A B c : ℤ} (hA : 2 * a = A) (hB : 2 * b = B)
    (hc : A ^ 2 - d * B ^ 2 = 4 * c) : IsIntegral ℤ ((a : K) + b * s) := by
  refine ⟨X ^ 2 - C A * X + C c, by monicity!, ?_⟩
  have hA' : (A : K) = 2 * a := by exact_mod_cast hA.symm
  have hB' : (B : K) = 2 * b := by exact_mod_cast hB.symm
  have hc' : (c : K) = ((A : K) ^ 2 - d * (B : K) ^ 2) / 4 := by
    have : ((A ^ 2 - d * B ^ 2 : ℤ) : K) = ((4 * c : ℤ) : K) := by rw [hc]
    push_cast at this
    linear_combination -this / 4
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
  simp only [eq_intCast]
  rw [hc', hA', hB']
  linear_combination (b : K) ^ 2 * hs

/-- **Integrality of `a + bs`**: it is integral over `ℤ` exactly when `2a` and `2b` are integers
`A`, `B` with `4 ∣ A² − dB²`. -/
theorem isIntegral_iff (a b : ℚ) :
    IsIntegral ℤ ((a : K) + b * s) ↔ ∃ A B : ℤ, 2 * a = A ∧ 2 * b = B ∧ 4 ∣ A ^ 2 - d * B ^ 2 := by
  constructor
  · intro hint
    by_cases hb : b = 0
    · subst hb
      have ha : IsIntegral ℤ a := by
        have : IsIntegral ℤ (algebraMap ℚ K a) := by simpa using hint
        exact isIntegral_algebraMap_iff.1 this
      obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 ha
      refine ⟨2 * m, 0, ?_, by simp, ⟨m ^ 2, by ring⟩⟩
      rw [← hm, eq_intCast]; push_cast; ring
    · have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
      rw [minpoly_eq hd hd1 hs hb] at h1
      have hc1 := congrArg (fun p : ℚ[X] ↦ p.coeff 1) h1
      have hc0 := congrArg (fun p : ℚ[X] ↦ p.coeff 0) h1
      simp only [quadPoly, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C,
        coeff_map, eq_intCast] at hc1 hc0
      norm_num at hc1 hc0
      set A : ℤ := -(minpoly ℤ ((a : K) + b * s)).coeff 1 with hAdef
      set c : ℤ := (minpoly ℤ ((a : K) + b * s)).coeff 0 with hcdef
      have hA : 2 * a = A := by rw [hAdef]; push_cast; linarith
      have hc : a ^ 2 - d * b ^ 2 = c := by rw [hcdef]; linarith
      obtain ⟨B, hB⟩ := int_of_mul_sq hd (r := 2 * b) (k := A ^ 2 - 4 * c) (by
        push_cast; rw [← hA, ← hc]; ring)
      refine ⟨A, B, hA, hB, ⟨c, ?_⟩⟩
      have : ((A ^ 2 - d * B ^ 2 : ℤ) : ℚ) = ((4 * c : ℤ) : ℚ) := by
        push_cast; rw [← hA, ← hB, ← hc]; ring
      exact_mod_cast this
  · rintro ⟨A, B, hA, hB, c, hc⟩
    exact isIntegral_of hs hA hB hc

end Integral

/-! ### The discriminant of a basis `(1, θ)` -/

/-- **If `(1, θ)` is a `ℤ`-basis of `𝓞 K` with `θ² = c + eθ`, then `D_K = 4c + e²`.** -/
theorem discr_eq_of_basis {θ : 𝓞 K} {c e : ℤ} (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb0 : b 0 = 1)
    (hb1 : b 1 = θ) (hθ : θ ^ 2 = c + e * θ) : discr K = 4 * c + e ^ 2 := by
  classical
  have hfin : Module.finrank ℤ (𝓞 K) = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  have hrepr1 : b.repr θ = Finsupp.single 1 1 := by rw [← hb1, Module.Basis.repr_self]
  have hθθ : θ * θ = c • b 0 + e • b 1 := by
    rw [hb0, hb1, ← sq, hθ, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  have hrepr2 : b.repr (θ * θ) = c • Finsupp.single 0 1 + e • Finsupp.single 1 1 := by
    rw [hθθ, map_add, map_zsmul, map_zsmul, Module.Basis.repr_self, Module.Basis.repr_self]
  have htr1 : Algebra.trace ℤ (𝓞 K) 1 = 2 := by
    rw [← map_one (algebraMap ℤ (𝓞 K)), Algebra.trace_algebraMap, hfin]
    rfl
  have htrθ : Algebra.trace ℤ (𝓞 K) θ = e := by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one, hrepr1, hrepr2]
    simp
  have htrθ2 : Algebra.trace ℤ (𝓞 K) (θ * θ) = 2 * c + e * e := by
    rw [hθθ, map_add, map_zsmul, map_zsmul, hb0, hb1, htr1, htrθ, smul_eq_mul, smul_eq_mul]
    ring
  rw [← NumberField.discr_eq_discr K b, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb0, hb1, one_mul, mul_one, htr1,
    htrθ, htrθ2]
  ring

/-! ### The generator for `d ≡ 1 (mod 4)`: `θ = (1 + s)/2` -/

section One

theorem isIntegral_θ₁ (hs : s ^ 2 = d) (h1 : d % 4 = 1) : IsIntegral ℤ ((1 + s) / 2) := by
  have e : ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * s = (1 + s) / 2 := by
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; ring
  rw [← e]
  exact isIntegral_of hs (A := 1) (B := 1) (c := (1 - d) / 4) (by norm_num) (by norm_num)
    (by norm_num; omega)

/-- `θ = (1 + s)/2 ∈ 𝓞 K`, for `d ≡ 1 (mod 4)`. -/
noncomputable def θ₁ (hs : s ^ 2 = d) (h1 : d % 4 = 1) : 𝓞 K :=
  ⟨(1 + s) / 2, (mem_integralClosure_iff ℤ K).2 (isIntegral_θ₁ hs h1)⟩

variable (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d) (h1 : d % 4 = 1)

theorem coe_θ₁ : ((θ₁ hs h1 : 𝓞 K) : K) = (1 + s) / 2 := rfl

theorem algebraMap_θ₁ : algebraMap (𝓞 K) K (θ₁ hs h1) = (1 + s) / 2 := rfl

omit hd hd1 hs h1 in
theorem intCast_quarter (h1 : d % 4 = 1) : (((d - 1) / 4 : ℤ) : K) = ((d : K) - 1) / 4 := by
  have h : (d - 1) / 4 * 4 = d - 1 := Int.ediv_mul_cancel (by omega)
  have h' : ((((d - 1) / 4 : ℤ) * 4 : ℤ) : K) = ((d - 1 : ℤ) : K) := by rw [h]
  push_cast at h'
  linear_combination h' / 4

/-- `θ² = (d − 1)/4 + θ`. -/
theorem θ₁_sq : θ₁ hs h1 ^ 2 = (((d - 1) / 4 : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * θ₁ hs h1 := by
  ext
  rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_add, map_mul,
    map_intCast, map_intCast, algebraMap_θ₁, intCast_quarter h1]
  push_cast
  linear_combination hs / 4

include hd hd1 hs h1

variable (hK : Module.finrank ℚ K = 2)

omit h1 in
theorem linearIndependent_θ₁ (h1 : d % 4 = 1) : LinearIndependent ℤ ![(1 : 𝓞 K), θ₁ hs h1] := by
  rw [LinearIndependent.pair_iff]
  intro u v h
  have hK' : (u : K) + (v : K) * ((1 + s) / 2) = 0 := by
    have := congrArg (algebraMap (𝓞 K) K) h
    rw [map_add, map_zsmul, map_zsmul, map_one, zsmul_eq_mul, zsmul_eq_mul, mul_one, map_zero] at this
    rw [← RingOfIntegers.coe_eq_algebraMap, coe_θ₁] at this
    exact this
  have hli0 := linearIndependent hd hd1 hs
  rw [LinearIndependent.pair_iff] at hli0
  have key : ((u : ℚ) + (v : ℚ) / 2) • (1 : K) + ((v : ℚ) / 2) • s = 0 := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
    simp only [map_add, map_div₀, map_intCast, map_ofNat]
    linear_combination hK'
  obtain ⟨hu, hv⟩ := hli0 _ _ key
  have hv' : (v : ℚ) = 0 := by linarith
  have hu' : (u : ℚ) = 0 := by linarith
  exact ⟨by exact_mod_cast hu', by exact_mod_cast hv'⟩

include hK

/-- **Every integer of `K` is `u + vθ`**, `u, v ∈ ℤ`. -/
theorem span_θ₁ (y : 𝓞 K) : ∃ u v : ℤ, y = u + v * θ₁ hs h1 := by
  obtain ⟨a, b, hy⟩ := exists_eq hd hd1 hs hK (y : K)
  have hint : IsIntegral ℤ ((a : K) + b * s) := by
    rw [← hy]; exact RingOfIntegers.isIntegral_coe y
  obtain ⟨A, B, hA, hB, h4⟩ := (isIntegral_iff hd hd1 hs a b).1 hint
  obtain ⟨m, hm⟩ := two_dvd_sub h1 h4
  refine ⟨m, B, ?_⟩
  ext
  rw [RingOfIntegers.coe_eq_algebraMap (_ + _), map_add, map_mul, map_intCast, map_intCast,
    algebraMap_θ₁, hy]
  have hA' : (a : K) = (A : K) / 2 := by
    have : ((2 * a : ℚ) : K) = ((A : ℚ) : K) := by rw [hA]
    push_cast at this; linear_combination this / 2
  have hB' : (b : K) = (B : K) / 2 := by
    have : ((2 * b : ℚ) : K) = ((B : ℚ) : K) := by rw [hB]
    push_cast at this; linear_combination this / 2
  have hm' : (A : K) - B = 2 * m := by exact_mod_cast hm
  rw [hA', hB']
  linear_combination hm' / 2

/-- The `ℤ`-basis `(1, θ)` of `𝓞 K`. -/
noncomputable def basis₁ : Module.Basis (Fin 2) ℤ (𝓞 K) :=
  Module.Basis.mk (linearIndependent_θ₁ hd hd1 hs h1) (by
    intro y _
    obtain ⟨u, v, rfl⟩ := span_θ₁ hd hd1 hs h1 hK y
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
    refine Submodule.add_mem _ ?_ ?_
    · rw [show (u : 𝓞 K) = u • (1 : 𝓞 K) by rw [zsmul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    · rw [show (v : 𝓞 K) * θ₁ hs h1 = v • θ₁ hs h1 by rw [zsmul_eq_mul]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))

/-- **`𝓞 K = ℤ[θ]`.** -/
theorem adjoin_θ₁ : Algebra.adjoin ℤ {θ₁ hs h1} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨u, v, rfl⟩ := span_θ₁ hd hd1 hs h1 hK y
  exact Subalgebra.add_mem _ (intCast_mem _ u)
    (Subalgebra.mul_mem _ (intCast_mem _ v) (Algebra.subset_adjoin (Set.mem_singleton _)))

/-- **The discriminant is `d`.** -/
theorem discr_θ₁ : discr K = d := by
  rw [discr_eq_of_basis (basis₁ hd hd1 hs h1 hK) (by simp [basis₁]) (by simp [basis₁])
    (θ₁_sq hs h1)]
  omega

omit hK in
/-- **The minimal polynomial of `θ = (1 + s)/2` over `ℤ` is `X² − X − (d − 1)/4`.** -/
theorem minpoly_θ₁ : minpoly ℤ (θ₁ hs h1) = X ^ 2 - X - C ((d - 1) / 4) := by
  rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K), algebraMap_θ₁]
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (isIntegral_θ₁ hs h1)]
  have e : ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * s = (1 + s) / 2 := by
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; ring
  rw [← e, minpoly_eq hd hd1 hs (by norm_num : (1 / 2 : ℚ) ≠ 0), quadPoly, Polynomial.map_sub,
    Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, eq_intCast]
  rw [intCast_quarter (K := ℚ) h1, show (2 * (1 / 2) : ℚ) = 1 by norm_num, C_1, one_mul,
    show ((1 / 2 : ℚ) ^ 2 - d * (1 / 2) ^ 2) = -(((d : ℚ) - 1) / 4) by ring, C_neg]
  ring

end One

/-! ### The generator for `d ≡ 2, 3 (mod 4)`: `θ = s` -/

section Two

theorem isIntegral_θ₂ (hs : s ^ 2 = d) : IsIntegral ℤ s := by
  have e : ((0 : ℚ) : K) + ((1 : ℚ) : K) * s = s := by simp
  rw [← e]
  exact isIntegral_of hs (A := 0) (B := 2) (c := -d) (by norm_num) (by norm_num) (by ring)

/-- `θ = s ∈ 𝓞 K`. -/
noncomputable def θ₂ (hs : s ^ 2 = d) : 𝓞 K := ⟨s, (mem_integralClosure_iff ℤ K).2 (isIntegral_θ₂ hs)⟩

variable (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d) (h23 : d % 4 = 2 ∨ d % 4 = 3)

theorem coe_θ₂ : ((θ₂ hs : 𝓞 K) : K) = s := rfl

theorem algebraMap_θ₂ : algebraMap (𝓞 K) K (θ₂ hs) = s := rfl

theorem θ₂_sq : θ₂ hs ^ 2 = ((d : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * θ₂ hs := by
  ext
  rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_add, map_mul,
    map_intCast, map_intCast, algebraMap_θ₂, hs]
  push_cast
  ring

include hd hd1 hs

theorem linearIndependent_θ₂ : LinearIndependent ℤ ![(1 : 𝓞 K), θ₂ hs] := by
  rw [LinearIndependent.pair_iff]
  intro u v h
  have hK' : (u : K) + (v : K) * s = 0 := by
    have := congrArg (algebraMap (𝓞 K) K) h
    rw [map_add, map_zsmul, map_zsmul, map_one, zsmul_eq_mul, zsmul_eq_mul, mul_one, map_zero] at this
    rw [← RingOfIntegers.coe_eq_algebraMap, coe_θ₂] at this
    exact this
  have hli0 := linearIndependent hd hd1 hs
  rw [LinearIndependent.pair_iff] at hli0
  have key : (u : ℚ) • (1 : K) + (v : ℚ) • s = 0 := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
    simp only [map_intCast]
    exact hK'
  obtain ⟨hu, hv⟩ := hli0 _ _ key
  exact ⟨by exact_mod_cast hu, by exact_mod_cast hv⟩

variable (hK : Module.finrank ℚ K = 2)
include h23 hK

theorem span_θ₂ (y : 𝓞 K) : ∃ u v : ℤ, y = u + v * θ₂ hs := by
  obtain ⟨a, b, hy⟩ := exists_eq hd hd1 hs hK (y : K)
  have hint : IsIntegral ℤ ((a : K) + b * s) := by
    rw [← hy]; exact RingOfIntegers.isIntegral_coe y
  obtain ⟨A, B, hA, hB, h4⟩ := (isIntegral_iff hd hd1 hs a b).1 hint
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := two_dvd_both h23 h4
  refine ⟨k, l, ?_⟩
  ext
  rw [RingOfIntegers.coe_eq_algebraMap (_ + _), map_add, map_mul, map_intCast, map_intCast,
    algebraMap_θ₂, hy]
  have hA' : (a : K) = k := by
    have : ((2 * a : ℚ) : K) = ((A : ℚ) : K) := by rw [hA]
    rw [hk] at this; push_cast at this; linear_combination this / 2
  have hB' : (b : K) = l := by
    have : ((2 * b : ℚ) : K) = ((B : ℚ) : K) := by rw [hB]
    rw [hl] at this; push_cast at this; linear_combination this / 2
  rw [hA', hB']

/-- The `ℤ`-basis `(1, s)` of `𝓞 K`. -/
noncomputable def basis₂ : Module.Basis (Fin 2) ℤ (𝓞 K) :=
  Module.Basis.mk (linearIndependent_θ₂ hd hd1 hs) (by
    intro y _
    obtain ⟨u, v, rfl⟩ := span_θ₂ hd hd1 hs h23 hK y
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
    refine Submodule.add_mem _ ?_ ?_
    · rw [show (u : 𝓞 K) = u • (1 : 𝓞 K) by rw [zsmul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    · rw [show (v : 𝓞 K) * θ₂ hs = v • θ₂ hs by rw [zsmul_eq_mul]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))

/-- **`𝓞 K = ℤ[s]`.** -/
theorem adjoin_θ₂ : Algebra.adjoin ℤ {θ₂ hs} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨u, v, rfl⟩ := span_θ₂ hd hd1 hs h23 hK y
  exact Subalgebra.add_mem _ (intCast_mem _ u)
    (Subalgebra.mul_mem _ (intCast_mem _ v) (Algebra.subset_adjoin (Set.mem_singleton _)))

/-- **The discriminant is `4d`.** -/
theorem discr_θ₂ : discr K = 4 * d := by
  rw [discr_eq_of_basis (basis₂ hd hd1 hs h23 hK) (by simp [basis₂]) (by simp [basis₂]) (θ₂_sq hs)]
  ring

omit h23 hK in
/-- **The minimal polynomial of `s` over `ℤ` is `X² − d`.** -/
theorem minpoly_θ₂ : minpoly ℤ (θ₂ hs) = X ^ 2 - C d := by
  rw [← minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K), algebraMap_θ₂]
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (isIntegral_θ₂ hs)]
  have e : ((0 : ℚ) : K) + ((1 : ℚ) : K) * s = s := by simp
  rw [← e, minpoly_eq hd hd1 hs one_ne_zero, quadPoly, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, eq_intCast]
  rw [show ((0 : ℚ) ^ 2 - d * 1 ^ 2) = -(d : ℚ) by ring, C_neg, mul_zero, C_0, zero_mul, sub_zero]
  ring

end Two

/-! ### Every quadratic field is `ℚ(√d)` -/

/-- **Every quadratic field contains a square root `s` of a squarefree integer `d ≠ 1`.** -/
theorem exists_sqrt (hK : Module.finrank ℚ K = 2) :
    ∃ (d : ℤ) (s : K), Squarefree d ∧ d ≠ 1 ∧ s ^ 2 = d := by
  -- an element outside `ℚ`
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ Set.range (algebraMap ℚ K) := by
    by_contra h
    push Not at h
    have htop : (⊥ : Subalgebra ℚ K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Algebra.mem_bot.2 (h x)
    rw [Subalgebra.bot_eq_top_iff_finrank_eq_one, hK] at htop
    exact absurd htop (by norm_num)
  have hint : IsIntegral ℚ x := .of_finite ℚ x
  -- its minimal polynomial has degree `2`
  have hdeg : (minpoly ℚ x).natDegree = 2 := by
    have h1 : (minpoly ℚ x).natDegree ≠ 1 := fun h ↦ hx (minpoly.natDegree_eq_one_iff.1 h)
    have h0 : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
    have h2 : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
    omega
  have hrel : x ^ 2 + ((minpoly ℚ x).coeff 1 : K) * x + ((minpoly ℚ x).coeff 0 : K) = 0 := by
    have h := minpoly.aeval ℚ x
    rw [aeval_eq_sum_range, hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      show (minpoly ℚ x).coeff 2 = 1 by
        rw [← hdeg]; exact (minpoly.monic hint).leadingCoeff] at h
    simp only [pow_zero, pow_one, Algebra.smul_def, mul_one, eq_ratCast, Rat.cast_one, one_mul] at h
    linear_combination h
  set p := (minpoly ℚ x).coeff 1 with hp
  set q := (minpoly ℚ x).coeff 0 with hq
  -- complete the square: `y = x + p/2`, `y² = r`
  set y : K := x + p / 2 with hydef
  set r : ℚ := p ^ 2 / 4 - q with hrdef
  have hy2 : y ^ 2 = r := by
    rw [hydef, hrdef]
    push_cast
    linear_combination hrel
  have hy : y ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨t, ht⟩
    apply hx
    refine ⟨t - p / 2, ?_⟩
    rw [map_sub, ht, hydef, map_div₀, eq_ratCast, eq_ratCast]
    push_cast
    ring
  -- clear the denominator: `(n y)² = n·m`
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, Rat.cast_zero, sq_eq_zero_iff] at hy2
    exact hy ⟨0, by rw [hy2, map_zero]⟩
  set n : ℕ := r.den
  set m : ℤ := r.num
  have hrnm : (r : K) = (m : K) / n := by
    have := Rat.num_div_den r
    rw [← this]
    push_cast
    rfl
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hN : ((n : K) * y) ^ 2 = ((n * m : ℤ) : K) := by
    rw [mul_pow, hy2, hrnm]
    push_cast
    field_simp
  have hN0 : (n : ℤ) * m ≠ 0 := by
    apply mul_ne_zero (by exact_mod_cast r.den_nz)
    exact Rat.num_ne_zero.2 hr0
  obtain ⟨f, d, hfd, hd⟩ := exists_sq_mul_squarefree ((n : ℤ) * m)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_mul] at hfd
    exact hN0 hfd.symm
  have hf' : (f : K) ≠ 0 := by exact_mod_cast hf0
  have hsq : ((n : K) * y / f) ^ 2 = d := by
    rw [div_pow, hN, ← hfd]
    push_cast
    rw [mul_comm, mul_div_assoc, div_self (pow_ne_zero 2 hf'), mul_one]
  refine ⟨d, (n : K) * y / f, hd, ?_, hsq⟩
  -- `d = 1` would put `y` in `ℚ`
  rintro rfl
  have h01 : ((n : K) * y / f - 1) * ((n : K) * y / f + 1) = 0 := by
    rw [Int.cast_one] at hsq
    linear_combination hsq
  apply hy
  rcases mul_eq_zero.1 h01 with h | h
  · have h' : (n : K) * y = f := (div_eq_one_iff_eq hf').1 (sub_eq_zero.1 h)
    refine ⟨(f : ℚ) / n, ?_⟩
    rw [map_div₀, eq_ratCast, eq_ratCast, Rat.cast_intCast, Rat.cast_natCast, eq_comm, eq_div_iff hn0,
      mul_comm]
    exact h'
  · have h' : (n : K) * y = -f := by
      have := (div_eq_iff hf').1 (eq_neg_of_add_eq_zero_left h)
      rw [this]; ring
    refine ⟨-(f : ℚ) / n, ?_⟩
    rw [map_div₀, eq_ratCast, eq_ratCast, Rat.cast_neg, Rat.cast_intCast, Rat.cast_natCast, eq_comm,
      eq_div_iff hn0, mul_comm]
    exact h'

end QuadRing
