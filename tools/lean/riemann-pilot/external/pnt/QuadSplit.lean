/-
# Round 487: the splitting law in a quadratic field

Imports Mathlib and the pilot's `QuadIdeals` and `QuadRing`.

Plain statement. Let `K` be a number field of degree `2`, `d` a squarefree integer other than `1` and `s ∈ K` with
`s² = d` (round 486's `QuadRing.exists_sqrt` supplies them), and `p` a prime. `Split`, `Inert` and `Ramified` are
round 485's (`QuadIdeals`).

* `d ≡ 2, 3 (mod 4)`: `p` ramifies if `p ∣ d` or `p = 2` (`ramified_of_dvd₂`, `ramified_two₂`); for odd `p ∤ d`, `p`
  splits if `d` is a square mod `p` (`split₂`), and `p` is inert if `d` is not a square mod `p` (`inert₂`).
* `d ≡ 1 (mod 4)`: an odd `p` ramifies if `p ∣ d` (`ramified_of_dvd₁`), splits if `p ∤ d` and `d` is a square mod `p`
  (`split₁`), and is inert if `d` is not a square mod `p` (`inert₁`); `2` splits if `d ≡ 1 (mod 8)` (`split_two₁`) and
  is inert if `d ≡ 5 (mod 8)` (`inert_two₁`).

* `split_of_factors`, `ramified_of_factors`, `inert_of_factors`: for `θ` with `ℤ[θ] = 𝓞 K`, the splitting type of `p`
  from the factorization of the minimal polynomial of `θ` mod `p`, through Mathlib's Kummer–Dedekind bijection
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` between the primes over `p` and the monic irreducible factors,
  and its `inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'`: the norm of a prime over `p` is `p` to the
  degree of its factor (`absNorm_eq`, with Mathlib's `Ideal.pow_inertiaDeg`). Two distinct linear factors give two
  distinct primes; the square of a linear factor gives one prime, of norm `p`; an irreducible quadratic gives a
  prime of norm `p²`; round 485's `QuadIdeals.pFactors_cases` does the rest.
* `split_of_root`, `ramified_of_root`, `inert_of_no_root`: the same for a minimal polynomial `X² + bX + a` mod `p`
  with a root `r`, `2r + b ≠ 0` (two distinct roots), a root `r` with `2r + b = 0` (a double root), or no root.
* The roots: `X² − d` has the root `u` when `d ≡ u²`, and `X² − X − (d − 1)/4` has the root `(1 + u)/2` when
  `d ≡ u²` and `p` is odd (`root_half`); mod `2` the roots are checked by `decide`.

With `[Fact p.Prime]` in context, `-x` in `ZMod p` elaborates through Mathlib's instance "a simple nilpotent additive
group is commutative" (`GroupTheory/Nilpotent.lean`), and `ring` and `simp` fail on it (`ring` does not close
`b + -b = 0`); the file erases that instance.
-/
import Mathlib
import QuadIdeals
import QuadRing

open NumberField Polynomial Ideal UniqueFactorizationMonoid

/- See the module docstring: erased for `ring` and `simp` in `ZMod p`. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace QuadSplit

/-! ### Monic quadratics over a field -/

section Quadratic

variable {F : Type*} [Field F] [DecidableEq F]

theorem normalizedFactors_mul_X_sub_C (r r' : F) :
    normalizedFactors ((X - C r) * (X - C r')) = {X - C r, X - C r'} := by
  rw [normalizedFactors_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero r'),
    normalizedFactors_irreducible (irreducible_X_sub_C r),
    normalizedFactors_irreducible (irreducible_X_sub_C r'),
    (monic_X_sub_C r).normalize_eq_self, (monic_X_sub_C r').normalize_eq_self]
  rfl

omit [DecidableEq F] in
theorem quad_eq_mul {a b r : F} (hr : r ^ 2 + b * r + a = 0) :
    X ^ 2 + C b * X + C a = (X - C r) * (X - C (-b - r)) := by
  have ha : a = -r ^ 2 - b * r := by linear_combination hr
  rw [ha]
  simp only [map_sub, map_neg, map_mul, map_pow]
  ring

omit [DecidableEq F] in
theorem quad_natDegree (a b : F) : (X ^ 2 + C b * X + C a).natDegree = 2 := by
  compute_degree!

omit [DecidableEq F] in
theorem quad_monic (a b : F) : (X ^ 2 + C b * X + C a).Monic := by
  monicity!

omit [DecidableEq F] in
theorem quad_irreducible {a b : F} (h : ∀ r : F, r ^ 2 + b * r + a ≠ 0) :
    Irreducible (X ^ 2 + C b * X + C a) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [quad_natDegree]; decide
  · intro r hr
    apply h r
    simpa [IsRoot.def, eval_add, eval_pow, eval_X, eval_mul, eval_C] using hr

omit [DecidableEq F] in
theorem X_sub_C_ne {r r' : F} (h : r ≠ r') : X - C r ≠ X - C r' := by
  intro h'
  apply h
  have := congrArg (eval 0) h'
  simpa using this

/-- No root: the quadratic is its own factorization. -/
theorem factors_of_no_root {a b : F} (h : ∀ r : F, r ^ 2 + b * r + a ≠ 0) :
    normalizedFactors (X ^ 2 + C b * X + C a) = {X ^ 2 + C b * X + C a} := by
  rw [normalizedFactors_irreducible (quad_irreducible h), (quad_monic a b).normalize_eq_self]

/-- A root `r`: the factors are `X − r` and `X − (−b − r)`. -/
theorem factors_of_root {a b r : F} (hr : r ^ 2 + b * r + a = 0) :
    normalizedFactors (X ^ 2 + C b * X + C a) = {X - C r, X - C (-b - r)} := by
  rw [quad_eq_mul hr, normalizedFactors_mul_X_sub_C]

omit [DecidableEq F] in
theorem ne_of_two_mul_add_ne {b r : F} (hne : 2 * r + b ≠ 0) : r ≠ -b - r := by
  intro h
  apply hne
  linear_combination h

omit [DecidableEq F] in
theorem eq_of_two_mul_add_eq {b r : F} (heq : 2 * r + b = 0) : -b - r = r := by
  linear_combination -heq

end Quadratic

/-! ### Kummer–Dedekind for a monogenic ring of integers -/

section KD

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [hp : Fact p.Prime]

attribute [local instance] Int.ideal_span_isMaximal_of_prime

omit [NumberField K] in
theorem not_dvd_exponent (hθ : Algebra.adjoin ℤ {θ} = ⊤) : ¬ p ∣ RingOfIntegers.exponent θ := by
  rw [RingOfIntegers.exponent_eq_one_iff.2 hθ]
  exact hp.out.not_dvd_one

/-- The primes over `p` are the prime factors of `p𝓞 K`. -/
theorem mem_primesOver_iff {P : Ideal (𝓞 K)} :
    P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ↔ P ∈ QuadIdeals.pFactors (K := K) p := by
  rw [mem_primesOver_iff_mem_normalizedFactors (𝓞 K) (by simpa using hp.out.ne_zero),
    QuadIdeals.pFactors, Ideal.map_span, Set.image_singleton, map_natCast]

/-- The norm of a prime over `p` is `p` to the degree of its factor. -/
theorem absNorm_eq (hθ : Algebra.adjoin ℤ {θ} = ⊤) (P : (span {(p : ℤ)}).primesOver (𝓞 K)) :
    absNorm (P : Ideal (𝓞 K)) =
      p ^ ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent hθ) P :
        (ZMod p)[X])).natDegree := by
  have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (not_dvd_exponent hθ)
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent hθ) P).prop
  rw [Subtype.coe_eta, Equiv.symm_apply_apply] at h
  rw [← Ideal.pow_inertiaDeg p (P : Ideal (𝓞 K)), h]

variable (hK : Module.finrank ℚ K = 2) (hθ : Algebra.adjoin ℤ {θ} = ⊤)
include hK hθ

theorem split_of_factors {r r' : ZMod p} (hrr : r ≠ r')
    (h : normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) = {X - C r, X - C r'}) :
    QuadIdeals.Split K p := by
  have hr : X - C r ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [Multiset.mem_toFinset, h]; simp
  have hr' : X - C r' ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [Multiset.mem_toFinset, h]; simp
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := K) (not_dvd_exponent (p := p) hθ)
  have hne : ((e.symm ⟨_, hr⟩ : _) : Ideal (𝓞 K)) ≠ (e.symm ⟨_, hr'⟩ : _) := by
    intro heq
    have h2 := congrArg (fun P ↦ (e P : (ZMod p)[X])) (Subtype.ext heq)
    simp only [Equiv.apply_symm_apply] at h2
    exact X_sub_C_ne hrr h2
  have h1 : ((e.symm ⟨_, hr⟩ : _) : Ideal (𝓞 K)) ∈ QuadIdeals.pFactors p :=
    mem_primesOver_iff.1 (e.symm ⟨_, hr⟩).prop
  have h2 : ((e.symm ⟨_, hr'⟩ : _) : Ideal (𝓞 K)) ∈ QuadIdeals.pFactors p :=
    mem_primesOver_iff.1 (e.symm ⟨_, hr'⟩).prop
  rcases QuadIdeals.pFactors_cases hK hp.out with ⟨P, hf, -⟩ | ⟨hc, hall⟩
  · rw [hf, Multiset.mem_singleton] at h1 h2
    exact absurd (h1.trans h2.symm) hne
  · obtain ⟨P, Q, hPQ⟩ := Multiset.card_eq_two.1 hc
    have hP : P ∈ QuadIdeals.pFactors (K := K) p := by rw [hPQ]; simp
    have hQ : Q ∈ QuadIdeals.pFactors (K := K) p := by rw [hPQ]; simp
    by_cases hPQe : P = Q
    · subst hPQe
      rw [hPQ] at h1 h2
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, or_self] at h1 h2
      exact absurd (h1.trans h2.symm) hne
    · exact ⟨P, Q, hPQe, hPQ, hall P hP, hall Q hQ⟩

theorem ramified_of_factors {r : ZMod p}
    (h : normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) = {X - C r, X - C r}) :
    QuadIdeals.Ramified K p := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := K) (not_dvd_exponent (p := p) hθ)
  have he : ∀ P, (e P : (ZMod p)[X]) = X - C r := by
    intro P
    have h1 := (e P).prop
    rw [Multiset.mem_toFinset, h] at h1
    simpa using h1
  rcases QuadIdeals.pFactors_cases hK hp.out with ⟨P, hf, hPn⟩ | ⟨hc, hall⟩
  · exfalso
    have hP : P ∈ QuadIdeals.pFactors (K := K) p := by rw [hf]; exact Multiset.mem_singleton_self P
    have hn := absNorm_eq hθ ⟨P, mem_primesOver_iff.2 hP⟩
    rw [he, natDegree_X_sub_C, pow_one, hPn] at hn
    have := hp.out.two_le
    nlinarith
  · obtain ⟨P, Q, hPQ⟩ := Multiset.card_eq_two.1 hc
    have hP : P ∈ QuadIdeals.pFactors (K := K) p := by rw [hPQ]; simp
    have hQ : Q ∈ QuadIdeals.pFactors (K := K) p := by rw [hPQ]; simp
    have hPQe : P = Q := by
      have := e.injective (a₁ := ⟨P, mem_primesOver_iff.2 hP⟩) (a₂ := ⟨Q, mem_primesOver_iff.2 hQ⟩)
        (Subtype.ext (by rw [he, he]))
      exact congrArg Subtype.val this
    subst hPQe
    exact ⟨P, hPQ, hall P hP⟩

theorem inert_of_factors
    (h : normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) =
      {(minpoly ℤ θ).map (Int.castRingHom (ZMod p))})
    (hdeg : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).natDegree = 2) :
    QuadIdeals.Inert K p := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := K) (not_dvd_exponent (p := p) hθ)
  rcases QuadIdeals.pFactors_cases hK hp.out with ⟨P, hf, hPn⟩ | ⟨hc, hall⟩
  · exact ⟨P, hf, hPn⟩
  · exfalso
    obtain ⟨P, hP⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hc]; norm_num)
    have hPo : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := mem_primesOver_iff.2 hP
    have hn := absNorm_eq hθ ⟨P, hPo⟩
    have hmem := (e ⟨P, hPo⟩).prop
    rw [Multiset.mem_toFinset, h, Multiset.mem_singleton] at hmem
    rw [hmem, hdeg, hall P hP] at hn
    have := hp.out.two_le
    nlinarith

/-- **The splitting law from the roots mod `p`**, for `minpoly θ ≡ X² + bX + a (mod p)`. -/
theorem split_of_root {a b : ZMod p}
    (hmin : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = X ^ 2 + C b * X + C a)
    {r : ZMod p} (hr : r ^ 2 + b * r + a = 0) (hne : 2 * r + b ≠ 0) : QuadIdeals.Split K p := by
  refine split_of_factors hK hθ (ne_of_two_mul_add_ne hne) ?_
  rw [hmin]
  exact factors_of_root hr

theorem ramified_of_root {a b : ZMod p}
    (hmin : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = X ^ 2 + C b * X + C a)
    {r : ZMod p} (hr : r ^ 2 + b * r + a = 0) (heq : 2 * r + b = 0) : QuadIdeals.Ramified K p := by
  refine ramified_of_factors hK hθ (r := r) ?_
  rw [hmin, factors_of_root hr, eq_of_two_mul_add_eq heq]

theorem inert_of_no_root {a b : ZMod p}
    (hmin : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = X ^ 2 + C b * X + C a)
    (h : ∀ r : ZMod p, r ^ 2 + b * r + a ≠ 0) : QuadIdeals.Inert K p := by
  refine inert_of_factors hK hθ ?_ ?_
  · rw [hmin, factors_of_no_root h]
  · rw [hmin, quad_natDegree]

end KD

/-! ### Field identities for the roots -/

section Roots

variable {F : Type*} [Field F]

theorem form_two {R : Type*} [CommRing R] (e : R) : (X ^ 2 - C e : R[X]) = X ^ 2 + C 0 * X + C (-e) := by
  simp only [map_zero, map_neg, zero_mul, add_zero]
  ring

theorem form_one {R : Type*} [CommRing R] (e : R) :
    (X ^ 2 - X - C e : R[X]) = X ^ 2 + C (-1) * X + C (-e) := by
  simp only [map_neg, map_one]
  ring

theorem root_sq {e u : F} (hu : e = u * u) : u ^ 2 + 0 * u + -e = 0 := by
  linear_combination (-1 : F) * hu

theorem sq_of_root_sq {e r : F} (hr : r ^ 2 + 0 * r + -e = 0) : e = r * r := by
  linear_combination -hr

theorem two_mul_ne {u : F} (h2 : (2 : F) ≠ 0) (hu : u ≠ 0) : 2 * u + 0 ≠ 0 := by
  rw [add_zero]
  exact mul_ne_zero h2 hu

theorem root_half {c u : F} (h2 : (2 : F) ≠ 0) (hu : 4 * c + 1 = u * u) :
    ((1 + u) / 2) ^ 2 + -1 * ((1 + u) / 2) + -c = 0 := by
  have h2' : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination (-(2 : F)⁻¹ ^ 2) * hu + ((1 + u) * 2⁻¹ + c * (2 * 2⁻¹ + 1)) * h2'

theorem two_mul_half {u : F} (h2 : (2 : F) ≠ 0) : 2 * ((1 + u) / 2) + -1 = u := by
  have h2' : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination (1 + u) * h2'

theorem sq_of_root_one {c r : F} (hr : r ^ 2 + -1 * r + -c = 0) :
    4 * c + 1 = (2 * r - 1) * (2 * r - 1) := by
  linear_combination (-4 : F) * hr

end Roots

theorem two_ne_zero_of_ne {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

/-! ### The splitting law for `ℚ(√d)` -/

section Law

variable {K : Type*} [Field K] [NumberField K] {d : ℤ} {s : K}
  (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d) (hK : Module.finrank ℚ K = 2)
include hd hd1 hs hK

/-! #### `d ≡ 2, 3 (mod 4)`: `𝓞 K = ℤ[s]`, `minpoly s = X² − d` -/

section TwoThree

variable (h23 : d % 4 = 2 ∨ d % 4 = 3)
include h23

omit hK h23 in
theorem map_minpoly_θ₂ (p : ℕ) [Fact p.Prime] :
    (minpoly ℤ (QuadRing.θ₂ hs)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 + C 0 * X + C (-(d : ZMod p)) := by
  rw [QuadRing.minpoly_θ₂ hd hd1 hs, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, eq_intCast]
  exact form_two _

/-- `p ∣ d`: `p` ramifies. -/
theorem ramified_of_dvd₂ {p : ℕ} [Fact p.Prime] (hpd : (p : ℤ) ∣ d) : QuadIdeals.Ramified K p := by
  have hd0 : (d : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).2 hpd
  refine ramified_of_root hK (QuadRing.adjoin_θ₂ hd hd1 hs h23 hK) (map_minpoly_θ₂ hd hd1 hs p)
    (r := 0) ?_ ?_
  · rw [hd0]; simp
  · simp

/-- `2` ramifies. -/
theorem ramified_two₂ : QuadIdeals.Ramified K 2 := by
  rcases Int.emod_two_eq_zero_or_one d with h | h
  · exact ramified_of_dvd₂ hd hd1 hs hK h23 (by exact_mod_cast Int.dvd_of_emod_eq_zero h)
  · have hd2 : (d : ZMod 2) = 1 := by
      rw [← ZMod.intCast_mod d 2, show d % ((2 : ℕ) : ℤ) = 1 by omega]; rfl
    refine ramified_of_root hK (QuadRing.adjoin_θ₂ hd hd1 hs h23 hK) (map_minpoly_θ₂ hd hd1 hs 2)
      (r := 1) ?_ ?_
    · rw [hd2]; decide
    · decide

/-- `p` odd, `p ∤ d`, `d` a square mod `p`: `p` splits. -/
theorem split₂ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d)
    (hsq : IsSquare (d : ZMod p)) : QuadIdeals.Split K p := by
  obtain ⟨u, hu⟩ := hsq
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hu
    exact hpd hu
  exact split_of_root hK (QuadRing.adjoin_θ₂ hd hd1 hs h23 hK) (map_minpoly_θ₂ hd hd1 hs p)
    (root_sq hu) (two_mul_ne (two_ne_zero_of_ne hp2) hu0)

/-- `d` not a square mod `p`: `p` is inert. -/
theorem inert₂ {p : ℕ} [Fact p.Prime] (hsq : ¬ IsSquare (d : ZMod p)) : QuadIdeals.Inert K p :=
  inert_of_no_root hK (QuadRing.adjoin_θ₂ hd hd1 hs h23 hK) (map_minpoly_θ₂ hd hd1 hs p)
    (fun r hr ↦ hsq ⟨r, sq_of_root_sq hr⟩)

end TwoThree

/-! #### `d ≡ 1 (mod 4)`: `𝓞 K = ℤ[θ]`, `minpoly θ = X² − X − (d − 1)/4` -/

section One

variable (h1 : d % 4 = 1)
include h1

omit hK in
theorem map_minpoly_θ₁ (p : ℕ) [Fact p.Prime] :
    (minpoly ℤ (QuadRing.θ₁ hs h1)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 + C (-1) * X + C (-((((d - 1) / 4 : ℤ)) : ZMod p)) := by
  rw [QuadRing.minpoly_θ₁ hd hd1 hs h1, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, eq_intCast]
  exact form_one _

omit hd hd1 hs hK in
theorem cast_d (p : ℕ) : (d : ZMod p) = 4 * ((((d - 1) / 4 : ℤ)) : ZMod p) + 1 := by
  have h : d = 4 * ((d - 1) / 4) + 1 := by omega
  conv_lhs => rw [h]
  push_cast
  rfl

/-- `p` odd, `p ∣ d`: `p` ramifies. -/
theorem ramified_of_dvd₁ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpd : (p : ℤ) ∣ d) :
    QuadIdeals.Ramified K p := by
  have h2 := two_ne_zero_of_ne hp2
  have hd0 : (d : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).2 hpd
  have hu : 4 * ((((d - 1) / 4 : ℤ)) : ZMod p) + 1 = 0 * 0 := by
    rw [← cast_d h1, hd0, mul_zero]
  exact ramified_of_root hK (QuadRing.adjoin_θ₁ hd hd1 hs h1 hK) (map_minpoly_θ₁ hd hd1 hs h1 p)
    (root_half h2 hu) (two_mul_half h2)

/-- `p` odd, `p ∤ d`, `d` a square mod `p`: `p` splits. -/
theorem split₁ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d)
    (hsq : IsSquare (d : ZMod p)) : QuadIdeals.Split K p := by
  have h2 := two_ne_zero_of_ne hp2
  obtain ⟨u, hu⟩ := hsq
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hu
    exact hpd hu
  have hu' : 4 * ((((d - 1) / 4 : ℤ)) : ZMod p) + 1 = u * u := (cast_d h1 p).symm.trans hu
  refine split_of_root hK (QuadRing.adjoin_θ₁ hd hd1 hs h1 hK) (map_minpoly_θ₁ hd hd1 hs h1 p)
    (root_half h2 hu') ?_
  rw [two_mul_half h2]
  exact hu0

/-- `d` not a square mod `p`: `p` is inert. -/
theorem inert₁ {p : ℕ} [Fact p.Prime] (hsq : ¬ IsSquare (d : ZMod p)) : QuadIdeals.Inert K p :=
  inert_of_no_root hK (QuadRing.adjoin_θ₁ hd hd1 hs h1 hK) (map_minpoly_θ₁ hd hd1 hs h1 p)
    (fun r hr ↦ hsq ⟨2 * r - 1, (cast_d h1 p).trans (sq_of_root_one hr)⟩)

/-- `d ≡ 1 (mod 8)`: `2` splits. -/
theorem split_two₁ (h8 : d % 8 = 1) : QuadIdeals.Split K 2 := by
  have hc : ((((d - 1) / 4 : ℤ)) : ZMod 2) = 0 := by
    rw [← ZMod.intCast_mod, show (d - 1) / 4 % ((2 : ℕ) : ℤ) = 0 by omega]; rfl
  refine split_of_root hK (QuadRing.adjoin_θ₁ hd hd1 hs h1 hK) (map_minpoly_θ₁ hd hd1 hs h1 2)
    (r := 0) ?_ ?_
  · rw [hc]; decide
  · decide

/-- `d ≡ 5 (mod 8)`: `2` is inert. -/
theorem inert_two₁ (h8 : d % 8 = 5) : QuadIdeals.Inert K 2 := by
  have hc : ((((d - 1) / 4 : ℤ)) : ZMod 2) = 1 := by
    rw [← ZMod.intCast_mod, show (d - 1) / 4 % ((2 : ℕ) : ℤ) = 1 by omega]; rfl
  refine inert_of_no_root hK (QuadRing.adjoin_θ₁ hd hd1 hs h1 hK) (map_minpoly_θ₁ hd hd1 hs h1 2) ?_
  rw [hc]
  decide

end One

end Law

end QuadSplit
