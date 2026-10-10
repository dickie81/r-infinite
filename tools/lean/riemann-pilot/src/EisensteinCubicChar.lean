import EisensteinMobius

/-! # S1, part 3a: the cubic residue character on `ℤ[ω]`, its Jacobi sum and the Gauss-sum relation (round 290)

Cubic reciprocity is derived on the pilot's own stack in two files; this is the first. It holds the
objects and the two identities from which the reciprocity law follows (`EisensteinCubicRecip.lean`).

* **The character** (`cubChar`): for a maximal `P` with `3 ∉ P`, `χ_P(x)` is the cube root of unity
  `u ∈ {1, ω, ω²} ⊂ ℤ[ω]` with `u ≡ x^{(N(P)−1)/3} (mod P)` (`cubChar_spec`). The three cube roots stay
  distinct modulo `P` (`red_cube_injective`), and every cube root of unity of `ℤ[ω]/P` is one of them
  (`exists_red_cube_eq`), so `3 ∣ N(P) − 1` (`three_dvd_card_sub_one`).
* **Coordinates and primary elements**: every element is `m + nω` (`exists_coords`). `a` is *primary*
  when `a ≡ 1 (mod 3)` (`Primary`). Every element prime to `λ = ω − 1` has a primary associate
  (`exists_primary`), unique because the six units are distinct modulo `3` (`unit_eq_one_of_three_dvd`,
  `Primary.unit_eq_one`).
* **Conjugation** (`cj`): the ring automorphism of `ℤ[ω]` with `ω ↦ ω²`, from Mathlib's
  `IsCyclotomicExtension.fromZetaAut`. It preserves norms of principal ideals (`absNorm_span_cj`) and
  acts on the cube roots of unity as the square (`cj_of_cube`).
* **The Jacobi sum** (`jacobiSum_eq_neg`): for `P = (π)` with `π` primary, `J(χ_P, χ_P) = −π`.
  - `J ∈ P` (`jacobiSum_mem`): modulo `P` it is `Σ_x x^m(1 − x)^m` with `2m < N(P) − 1`.
  - `J·J̄ = N(P)` (`jacobiSum_mul_cj`, from Mathlib's `jacobiSum_mul_jacobiSum_inv` in `K`), so `(J) = P`.
  - `J ≡ −1 (mod 3)` (`three_dvd_jacobiSum_add_one`, from Mathlib's `exists_jacobiSum_eq_neg_one_add`
    at `μ = ω`, with `(ω − 1)² = −3ω`), which fixes the unit.
* **The Gauss-sum relation** (`cubChar_fundamental`): for `P = (π)`, `π` primary, and a maximal `Q` prime
  to `3` and to `N(P)`, `χ_Q(−N(P)·π) = χ_P(N(Q))²`. The Gauss sum `g` of `χ_P` with values in a field of
  characteristic `ℓ = char(𝓞/Q)` has `g³ = N(P)·J(χ_P, χ_P)` (Mathlib's `gaussSum_pow_eq_prod_jacobiSum`) and,
  by Frobenius (`gaussSum_pow_char_pow`), `g^{N(Q)} = χ_P(N(Q))⁻¹·g`; and `x^{(N(Q)−1)/3}` is `χ_Q(x)` modulo `Q`.
-/

open NumberField Ideal Polynomial

namespace Eis

/-! ### The cubic residue character with values in `ℤ[ω]` -/

section CubicChar

/-- The units of `ℤ[ω]` whose cube is `1` are `1`, `ω`, `ω²`. -/
theorem cube_root_cases {u : (𝓞 K)ˣ} (hu : u ^ 3 = 1) : u = 1 ∨ u = ωu ∨ u = ωu ^ 2 := by
  have hneg : ∀ v : (𝓞 K)ˣ, v ^ 3 = 1 → (-v) ^ 3 ≠ 1 := by
    intro v hv h
    rw [neg_pow, hv, mul_one] at h
    have := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at this
    have h2 : (2 : 𝓞 K) = 0 := by
      have h' : ((-1 : 𝓞 K)) ^ 3 = -1 := by norm_num
      linear_combination h' - this
    exact two_ne_zero h2
  have h1 : (1 : (𝓞 K)ˣ) ^ 3 = 1 := one_pow 3
  have hω : ωu ^ 3 = 1 := ωu_cube
  have hω2 : (ωu ^ 2) ^ 3 = 1 := by rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ωu_cube, one_pow]
  rcases List.mem_cons.1 (units_mem u) with rfl | h
  · exact Or.inl rfl
  rcases List.mem_cons.1 h with rfl | h
  · exact absurd hu (hneg 1 h1)
  rcases List.mem_cons.1 h with rfl | h
  · exact Or.inr (Or.inl rfl)
  rcases List.mem_cons.1 h with rfl | h
  · exact absurd hu (hneg ωu hω)
  rcases List.mem_cons.1 h with rfl | h
  · exact Or.inr (Or.inr rfl)
  rcases List.mem_cons.1 h with rfl | h
  · exact absurd hu (hneg (ωu ^ 2) hω2)
  simp at h

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P)

omit hPm in
include hP3 in
theorem lam_not_mem' : ω - 1 ∉ P := fun h => hP3 (three_mem_of_lam_mem h)

include hP3 in
/-- Away from `λ`, the cube roots of unity `1, ω, ω²` stay distinct modulo `P`. -/
theorem red_cube_injective {u v : (𝓞 K)ˣ} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (h : red P u = red P v) : u = v := by
  have hw : (u * v⁻¹) ^ 3 = 1 := by rw [mul_pow, inv_pow, hu, hv, inv_one, mul_one]
  have hred : red P (u * v⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have hne : ∀ w : (𝓞 K)ˣ, w ≠ 1 → w ^ 3 = 1 → red P w ≠ 1 := by
    intro w hw1 hw3 hr
    have hmem : (w : 𝓞 K) - 1 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← coe_red, hr, Units.val_one, sub_self]
    rcases cube_root_cases hw3 with rfl | rfl | rfl
    · exact hw1 rfl
    · exact lam_not_mem' P hP3 (by rwa [coe_ωu] at hmem)
    · apply lam_not_mem' P hP3
      have hf : (ω - 1) * (ω + 1) ∈ P := by
        have : (ω - 1) * (ω + 1) = ((ωu ^ 2 : (𝓞 K)ˣ) : 𝓞 K) - 1 := by simp [coe_ωu]; ring
        rw [this]; exact hmem
      rcases hPm.isPrime.mem_or_mem hf with h1 | h1
      · exact h1
      · exfalso
        have hu1 : IsUnit (ω + 1) := by
          have : ω + 1 = ((-(ωu ^ 2) : (𝓞 K)ˣ) : 𝓞 K) := by
            simp [coe_ωu]; linear_combination ω_sq_add
          rw [this]; exact Units.isUnit _
        exact hPm.ne_top (P.eq_top_of_isUnit_mem h1 hu1)
  by_contra huv
  exact hne _ (fun h1 => huv (by rw [mul_inv_eq_one] at h1; exact h1)) hw hred

/-- Every cube root of unity modulo `P` is the reduction of `1`, `ω` or `ω²`. -/
theorem exists_red_cube_eq {ξ : 𝓞 K ⧸ P} (hξ : ξ ^ 3 = 1) :
    ∃ u : (𝓞 K)ˣ, u ^ 3 = 1 ∧ ((red P u : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) = ξ := by
  set e := Ideal.Quotient.mk P ω with he_def
  have he := mk_ω_sq_add P
  have he3 := mk_ω_cube P
  rw [← he_def] at he he3
  have h1 : ξ ^ 3 - 1 = (ξ - 1) * (ξ - e) * (ξ - e ^ 2) := by
    linear_combination (ξ ^ 2 - ξ) * he + (1 - ξ) * he3
  have h0 : (ξ - 1) * (ξ - e) * (ξ - e ^ 2) = 0 := by rw [← h1, hξ, sub_self]
  have hω : ((ωu : (𝓞 K)ˣ) : 𝓞 K) = ω := coe_ωu
  have hω3 : (ωu ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ωu_cube, one_pow]
  rcases mul_eq_zero.1 h0 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact ⟨1, one_pow 3, by rw [coe_red]; simp; linear_combination -h⟩
    · exact ⟨ωu, ωu_cube, by rw [coe_red, hω, ← he_def]; linear_combination -h⟩
  · exact ⟨ωu ^ 2, hω3, by
      rw [coe_red, Units.val_pow_eq_pow_val, hω, map_pow, ← he_def]; linear_combination -h⟩

include hP3 in
/-- `3 ∣ N(P) − 1`: the reduction of `ω` has order `3`. -/
theorem three_dvd_card_sub_one : 3 ∣ Fintype.card (𝓞 K ⧸ P) - 1 := by
  classical
  set g := red P ωu
  have hg3 : g ^ 3 = 1 := by rw [← map_pow, ωu_cube, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    have := red_cube_injective P hP3 ωu_cube (one_pow 3) (by show g = red P 1; rw [h, map_one])
    have h2 := congrArg Units.val this
    rw [coe_ωu, Units.val_one] at h2
    exact lam_not_mem' P hP3 (by rw [h2, sub_self]; exact P.zero_mem)
  have hord : orderOf g = 3 := by
    have := orderOf_eq_prime hg3 hg1
    exact this
  have h1 : orderOf g ∣ Fintype.card (𝓞 K ⧸ P)ˣ := orderOf_dvd_card
  rw [hord, Fintype.card_units] at h1
  exact h1

/-- The exponent `(N(P) − 1)/3`. -/
noncomputable def m3 : ℕ := (Fintype.card (𝓞 K ⧸ P) - 1) / 3

include hP3 in
theorem pow_m3_pow_three (x : (𝓞 K ⧸ P)ˣ) : (x ^ m3 P) ^ 3 = 1 := by
  classical
  rw [← pow_mul, m3, Nat.div_mul_cancel (three_dvd_card_sub_one P hP3), ← Fintype.card_units]
  exact pow_card_eq_one

/-- `x ↦ x^{(N(P)−1)/3}`, into the cube roots of unity. -/
noncomputable def powR3 : (𝓞 K ⧸ P)ˣ →* rootsOfUnity 3 (𝓞 K ⧸ P) :=
  (powMonoidHom (m3 P)).codRestrict _ fun x => (mem_rootsOfUnity _ _).2 (pow_m3_pow_three P hP3 x)

omit hPm in
/-- Reduction of the cube roots of unity. -/
noncomputable def redR3 : rootsOfUnity 3 (𝓞 K) →* rootsOfUnity 3 (𝓞 K ⧸ P) :=
  ((red P).comp (rootsOfUnity 3 (𝓞 K)).subtype).codRestrict _ fun u =>
    (mem_rootsOfUnity _ _).2 (by
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
      rw [← map_pow, (mem_rootsOfUnity _ _).1 u.2, map_one])

include hP3 in
theorem redR3_bijective : Function.Bijective (redR3 P) := by
  refine ⟨fun u v h => ?_, fun ξ => ?_⟩
  · have h' : red P (u : (𝓞 K)ˣ) = red P (v : (𝓞 K)ˣ) := congrArg Subtype.val h
    exact Subtype.ext (red_cube_injective P hP3 ((mem_rootsOfUnity _ _).1 u.2)
      ((mem_rootsOfUnity _ _).1 v.2) h')
  · have hξ : ((ξ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ξ.2, Units.val_one]
    obtain ⟨u, hu3, hu⟩ := exists_red_cube_eq P hξ
    exact ⟨⟨u, (mem_rootsOfUnity _ _).2 hu3⟩, Subtype.ext (Units.ext hu)⟩

/-- The cube roots of unity of `ℤ[ω]` are those modulo `P`. -/
noncomputable def redEquiv3 : rootsOfUnity 3 (𝓞 K) ≃* rootsOfUnity 3 (𝓞 K ⧸ P) :=
  MulEquiv.ofBijective (redR3 P) (redR3_bijective P hP3)

/-- **The cubic residue character modulo `P`, with values in `ℤ[ω]`**: `χ_P(x)` is the cube root of
unity `u ∈ {1, ω, ω²}` with `u ≡ x^{(N(P)−1)/3} (mod P)`. -/
noncomputable def cubChar : MulChar (𝓞 K ⧸ P) (𝓞 K) :=
  MulChar.ofUnitHom ((rootsOfUnity 3 (𝓞 K)).subtype.comp
    ((redEquiv3 P hP3).symm.toMonoidHom.comp (powR3 P hP3)))

/-- The defining congruence: `χ_P(x) ≡ x^{(N(P)−1)/3}` and `χ_P(x)³ = 1` on units. -/
theorem cubChar_spec (x : (𝓞 K ⧸ P)ˣ) :
    Ideal.Quotient.mk P (cubChar P hP3 x) = (x : 𝓞 K ⧸ P) ^ m3 P ∧ cubChar P hP3 x ^ 3 = 1 := by
  set r := (redEquiv3 P hP3).symm (powR3 P hP3 x)
  have hval : cubChar P hP3 x = ((r : (𝓞 K)ˣ) : 𝓞 K) := by
    simp [cubChar, r]
  have h := (redEquiv3 P hP3).apply_symm_apply (powR3 P hP3 x)
  have h2 : red P (r : (𝓞 K)ˣ) = x ^ m3 P := congrArg Subtype.val h
  refine ⟨?_, ?_⟩
  · rw [hval, ← coe_red, h2, Units.val_pow_eq_pow_val]
  · rw [hval, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 r.2, Units.val_one]

end CubicChar

/-! ### Coordinates, primary elements, conjugation -/

section Primary

/-- Every element of `ℤ[ω]` is `m + nω` with `m, n ∈ ℤ`. -/
theorem exists_coords (x : 𝓞 K) : ∃ m n : ℤ, x = m + n * ω := by
  obtain ⟨f, rfl⟩ := exists_eq_aeval_ω x
  induction f using Polynomial.induction_on with
  | C a => exact ⟨a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨m, n, hmn⟩ := hp
    obtain ⟨m', n', hmn'⟩ := hq
    exact ⟨m + m', n + n', by rw [map_add, hmn, hmn']; push_cast; ring⟩
  | monomial k a ih =>
    obtain ⟨m, n, hmn⟩ := ih
    refine ⟨-n, m - n, ?_⟩
    rw [pow_succ, ← mul_assoc, map_mul, hmn, aeval_X]
    push_cast
    linear_combination (n : 𝓞 K) * ω_sq_add

theorem lam_dvd_three : (ω - 1) ∣ (3 : 𝓞 K) :=
  ⟨-(ω ^ 2) * (ω - 1), by linear_combination ω_sq_add + (ω - 2) * ω_cube⟩

theorem not_three_dvd_one : ¬ (3 : 𝓞 K) ∣ 1 := by
  intro h
  have hu : IsUnit (3 : 𝓞 K) := isUnit_of_dvd_one h
  have h9 := absNorm_natCast_span_sq 3
  rw [show ((3 : ℕ) : 𝓞 K) = 3 by norm_num, Ideal.span_singleton_eq_top.2 hu, Ideal.absNorm_top] at h9
  norm_num at h9

theorem not_three_dvd_unit (u : (𝓞 K)ˣ) : ¬ (3 : 𝓞 K) ∣ u := fun h =>
  not_three_dvd_one (by
    have := dvd_mul_of_dvd_left h ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
    rwa [Units.mul_inv] at this)

theorem not_three_dvd_lam : ¬ (3 : 𝓞 K) ∣ ω - 1 := by
  rintro ⟨c, hc⟩
  -- `λ² = −3ω`, so `−3ω = 9c²` and `3 ∣ ω`
  have h : (3 : 𝓞 K) * (-ω) = 3 * (3 * c ^ 2) := by
    linear_combination (-1 : 𝓞 K) * lam_sq + (ω - 1 + 3 * c) * hc
  have h3 : (3 : 𝓞 K) ≠ 0 := fun h0 => by
    have := congrArg ((↑) : 𝓞 K → K) h0; norm_num at this
  have hω : -ω = 3 * c ^ 2 := mul_left_cancel₀ h3 h
  apply not_three_dvd_unit (-ωu)
  rw [Units.val_neg, coe_ωu, hω]; exact dvd_mul_right _ _

/-- The six units are distinct modulo `3`. -/
theorem unit_eq_one_of_three_dvd {u : (𝓞 K)ˣ} (h : (3 : 𝓞 K) ∣ (u : 𝓞 K) - 1) : u = 1 := by
  have hω : ((ωu : (𝓞 K)ˣ) : 𝓞 K) = ω := coe_ωu
  rcases List.mem_cons.1 (units_mem u) with rfl | h'
  · rfl
  rcases List.mem_cons.1 h' with rfl | h'
  · exfalso; apply not_three_dvd_one
    have h2 : (3 : 𝓞 K) ∣ 2 := by
      have e : ((-1 : (𝓞 K)ˣ) : 𝓞 K) - 1 = -2 := by simp; ring
      rw [e, dvd_neg] at h; exact h
    have := dvd_sub (dvd_refl (3 : 𝓞 K)) h2
    rwa [show (3 : 𝓞 K) - 2 = 1 by ring] at this
  rcases List.mem_cons.1 h' with rfl | h'
  · exfalso; rw [hω] at h; exact not_three_dvd_lam h
  rcases List.mem_cons.1 h' with rfl | h'
  · exfalso; apply not_three_dvd_unit (ωu ^ 2)
    rw [Units.val_neg, hω] at h
    rw [Units.val_pow_eq_pow_val, hω, show ω ^ 2 = -ω - 1 by linear_combination ω_sq_add]
    exact h
  rcases List.mem_cons.1 h' with rfl | h'
  · exfalso; apply not_three_dvd_lam
    rw [Units.val_pow_eq_pow_val, hω] at h
    have := dvd_mul_of_dvd_left h (-ω)
    rw [show (ω ^ 2 - 1) * -ω = ω - 1 by linear_combination (-1 : 𝓞 K) * ω_cube] at this
    exact this
  rcases List.mem_cons.1 h' with rfl | h'
  · exfalso; apply not_three_dvd_unit ωu
    rw [Units.val_neg, Units.val_pow_eq_pow_val, hω] at h
    rw [hω, show ω = -ω ^ 2 - 1 by linear_combination ω_sq_add]; exact h
  simp at h'

/-- `a` is **primary**: `a ≡ 1 (mod 3)`. -/
def Primary (a : 𝓞 K) : Prop := (3 : 𝓞 K) ∣ a - 1

theorem primary_one : Primary 1 := by simp [Primary]

theorem Primary.mul {a b : 𝓞 K} (ha : Primary a) (hb : Primary b) : Primary (a * b) := by
  unfold Primary at *
  rw [show a * b - 1 = (a - 1) * b + (b - 1) by ring]
  exact dvd_add (dvd_mul_of_dvd_left ha b) hb

theorem Primary.not_lam_dvd {a : 𝓞 K} (ha : Primary a) : ¬ (ω - 1) ∣ a := by
  intro h
  have h1 : (ω - 1) ∣ a - 1 := lam_dvd_three.trans ha
  have : (ω - 1) ∣ (1 : 𝓞 K) := by
    have := dvd_sub h h1; rwa [sub_sub_cancel] at this
  obtain ⟨d, hd⟩ := this
  exact not_three_dvd_one ⟨-ω * d ^ 2, by linear_combination (1 + (ω - 1) * d) * hd + d ^ 2 * lam_sq⟩

/-- **Uniqueness**: a primary associate of a primary element is itself. -/
theorem Primary.unit_eq_one {a : 𝓞 K} {u : (𝓞 K)ˣ} (ha : Primary a) (hua : Primary (u * a)) :
    u = 1 := by
  apply unit_eq_one_of_three_dvd
  have := dvd_sub hua (dvd_mul_of_dvd_right ha (u : 𝓞 K))
  rwa [show (u : 𝓞 K) * a - 1 - u * (a - 1) = u - 1 by ring] at this

/-- **Existence**: an element prime to `λ = ω − 1` has a primary associate. -/
theorem exists_primary {a : 𝓞 K} (ha : ¬ (ω - 1) ∣ a) : ∃ u : (𝓞 K)ˣ, Primary (u * a) := by
  obtain ⟨m, n, rfl⟩ := exists_coords a
  have hω : ((ωu : (𝓞 K)ˣ) : 𝓞 K) = ω := coe_ωu
  have h3 : ¬ (3 : ℤ) ∣ m + n := by
    rintro ⟨k, hk⟩
    apply ha
    have e : (m : 𝓞 K) + n * ω = 3 * k + n * (ω - 1) := by
      have : ((m + n : ℤ) : 𝓞 K) = ((3 * k : ℤ) : 𝓞 K) := by rw [hk]
      push_cast at this; linear_combination this
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left lam_dvd_three _) (dvd_mul_left _ _)
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  obtain ⟨a, ha'⟩ : ∃ a, m = 3 * a + m % 3 := ⟨m / 3, by omega⟩
  obtain ⟨b, hb'⟩ : ∃ b, n = 3 * b + n % 3 := ⟨n / 3, by omega⟩
  rcases hm with hm | hm | hm <;> rcases hn with hn | hn | hn <;> rw [hm] at ha' <;>
    rw [hn] at hb' <;> subst ha' hb'
  · exact absurd ⟨a + b, by ring⟩ h3
  · exact ⟨ωu ^ 2, ⟨b - a - a * ω, by
      rw [Units.val_pow_eq_pow_val, hω]; push_cast
      linear_combination (3 * a : 𝓞 K) * ω_sq_add + (3 * b + 1 : 𝓞 K) * ω_cube⟩⟩
  · exact ⟨-(ωu ^ 2), ⟨a - b - 1 + a * ω, by
      rw [Units.val_neg, Units.val_pow_eq_pow_val, hω]; push_cast
      linear_combination (-(3 * a) : 𝓞 K) * ω_sq_add - (3 * b + 2 : 𝓞 K) * ω_cube⟩⟩
  · exact ⟨1, ⟨a + b * ω, by push_cast; ring⟩⟩
  · exact ⟨-ωu, ⟨b + (b - a) * ω, by
      rw [Units.val_neg, hω]; push_cast
      linear_combination (-(3 * b + 1) : 𝓞 K) * ω_sq_add⟩⟩
  · exact absurd ⟨a + b + 1, by ring⟩ h3
  · exact ⟨-1, ⟨-a - 1 - b * ω, by push_cast; ring⟩⟩
  · exact absurd ⟨a + b + 1, by ring⟩ h3
  · exact ⟨ωu, ⟨-b - 1 + (a - b) * ω, by
      rw [hω]; push_cast
      linear_combination (3 * b + 2 : 𝓞 K) * ω_sq_add⟩⟩

end Primary

/-! ### Conjugation -/

section Conj

theorem hζ2 : IsPrimitiveRoot (ζ ^ 2) 3 := hζ.pow_of_coprime 2 (by norm_num)

/-- The nontrivial automorphism `ζ ↦ ζ²` of `K`. -/
noncomputable def τK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut hζ2 (Polynomial.cyclotomic.irreducible_rat (by norm_num))

theorem τK_ζ : τK ζ = ζ ^ 2 := IsCyclotomicExtension.fromZetaAut_spec _ _

/-- **Conjugation** on `ℤ[ω]`, `ω ↦ ω² = ω̄`. -/
noncomputable def cj : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv τK.toRingEquiv

theorem cj_ω : cj ω = ω ^ 2 := by
  apply RingOfIntegers.ext
  rw [cj, RingOfIntegers.mapRingEquiv_apply]
  show τK ζ = _
  simp [τK_ζ]; rfl

theorem cj_coords (m n : ℤ) : cj (m + n * ω) = ((m - n : ℤ) : 𝓞 K) - n * ω := by
  rw [map_add, map_mul, map_intCast, map_intCast, cj_ω]; push_cast
  linear_combination (n : 𝓞 K) * ω_sq_add

theorem cj_cj (x : 𝓞 K) : cj (cj x) = x := by
  obtain ⟨m, n, rfl⟩ := exists_coords x
  rw [cj_coords, show ((m - n : ℤ) : 𝓞 K) - n * ω = ((m - n : ℤ) : 𝓞 K) + ((-n : ℤ) : 𝓞 K) * ω by
    push_cast; ring, cj_coords]
  push_cast; ring

theorem mul_cj_coords (m n : ℤ) :
    ((m : 𝓞 K) + n * ω) * cj (m + n * ω) = ((m ^ 2 - m * n + n ^ 2 : ℤ) : 𝓞 K) := by
  rw [cj_coords]; push_cast
  linear_combination (-(n : 𝓞 K) ^ 2) * ω_sq_add

theorem cj_unit_cube {u : (𝓞 K)ˣ} (hu : u ^ 3 = 1) : cj (u : 𝓞 K) = (u : 𝓞 K) ^ 2 := by
  rcases cube_root_cases hu with rfl | rfl | rfl
  · simp
  · rw [coe_ωu, cj_ω]
  · rw [Units.val_pow_eq_pow_val, coe_ωu, map_pow, cj_ω]

/-- On the cube roots of unity, conjugation is the square. -/
theorem cj_of_cube {y : 𝓞 K} (hy : y ^ 3 = 1) : cj y = y ^ 2 := by
  have hu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ 2, by rw [← pow_succ']; exact hy⟩
  obtain ⟨u, rfl⟩ := hu
  exact cj_unit_cube (Units.ext (by rw [Units.val_pow_eq_pow_val, hy, Units.val_one]))

theorem Primary.cj {a : 𝓞 K} (ha : Primary a) : Primary (cj a) := by
  unfold Primary at *
  have := map_dvd (Eis.cj : 𝓞 K →+* 𝓞 K) ha
  rwa [map_sub, map_one, map_ofNat] at this

theorem absNorm_span_cj (x : 𝓞 K) : absNorm (span {cj x}) = absNorm (span {x}) := by
  have e : span {cj x} = (span {x}).map (cj : 𝓞 K →+* 𝓞 K) := by
    rw [Ideal.map_span]; simp
  rw [e, absNorm_apply, absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv (span {x}) _ cj rfl).toEquiv).symm

end Conj

/-! ### The Jacobi sum `J(χ_π, χ_π) = −π` -/

section Jacobi

theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 K)} (h : I ≤ J) (hn : absNorm I = absNorm J)
    (h0 : absNorm J ≠ 0) : I = J := by
  obtain ⟨L, rfl⟩ := Ideal.dvd_iff_le.2 h
  rw [map_mul] at hn
  have : absNorm L = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) (by rw [hn, mul_one])
  rw [Ideal.absNorm_eq_one_iff.1 this, Ideal.mul_top]

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P)
include hP3

theorem cubChar_pow_three : cubChar P hP3 ^ 3 = 1 := by
  ext x
  rw [MulChar.pow_apply_coe, (cubChar_spec P hP3 x).2, MulChar.one_apply_coe]

theorem m3_pos : 0 < m3 P := by
  have h := three_dvd_card_sub_one P hP3
  have h2 : 1 < Fintype.card (𝓞 K ⧸ P) := Fintype.one_lt_card
  unfold m3; omega

theorem mk_cubChar (x : 𝓞 K ⧸ P) : Ideal.Quotient.mk P (cubChar P hP3 x) = x ^ m3 P := by
  by_cases hx : x = 0
  · rw [hx, MulChar.map_zero, map_zero, zero_pow (m3_pos P hP3).ne']
  · simpa using (cubChar_spec P hP3 (Units.mk0 x hx)).1

theorem cubChar_ne_one : cubChar P hP3 ≠ 1 := by
  classical
  intro h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 K ⧸ P)ˣ)
  have h2 := (cubChar_spec P hP3 g).1
  rw [h, MulChar.one_apply_coe, map_one] at h2
  have h3 : g ^ m3 P = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ← h2, Units.val_one])
  have hord : orderOf g = Fintype.card (𝓞 K ⧸ P)ˣ :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
  have hd := orderOf_dvd_of_pow_eq_one h3
  rw [hord, Fintype.card_units] at hd
  have hm := m3_pos P hP3
  have hle := Nat.le_of_dvd hm hd
  have h3d := three_dvd_card_sub_one P hP3
  unfold m3 at hle hm; omega

theorem orderOf_cubChar : orderOf (cubChar P hP3) = 3 :=
  orderOf_eq_prime (cubChar_pow_three P hP3) (cubChar_ne_one P hP3)

/-- `J(χ_P, χ_P) ∈ P`: modulo `P` it is `Σ_x x^m(1 − x)^m`, a polynomial sum of degree
`2m < N(P) − 1`. -/
theorem jacobiSum_mem : jacobiSum (cubChar P hP3) (cubChar P hP3) ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, jacobiSum, map_sum]
  simp_rw [map_mul, mk_cubChar]
  set m := m3 P
  have hq : Fintype.card (𝓞 K ⧸ P) - 1 = 3 * m := by
    rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (three_dvd_card_sub_one P hP3)).symm
  have hm := m3_pos P hP3
  calc ∑ x : 𝓞 K ⧸ P, x ^ m * (1 - x) ^ m
      = ∑ x : 𝓞 K ⧸ P, ∑ k ∈ Finset.range (m + 1),
          ((-1) ^ (k + m) * (m.choose k : 𝓞 K ⧸ P)) * x ^ (m + (m - k)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [sub_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [one_pow, pow_add]; ring
    _ = ∑ k ∈ Finset.range (m + 1),
          ((-1) ^ (k + m) * (m.choose k : 𝓞 K ⧸ P)) * ∑ x : 𝓞 K ⧸ P, x ^ (m + (m - k)) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = 0 := Finset.sum_eq_zero fun k _ => by
        rw [FiniteField.sum_pow_lt_card_sub_one (𝓞 K ⧸ P) _ (by omega), mul_zero]

/-- `J(χ_P, χ_P) ≡ −1 (mod 3)`. -/
theorem three_dvd_jacobiSum_add_one :
    (3 : 𝓞 K) ∣ jacobiSum (cubChar P hP3) (cubChar P hP3) + 1 := by
  obtain ⟨z, -, hz⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num : 2 < 3)
    (cubChar_pow_three P hP3) (cubChar_pow_three P hP3) (three_dvd_card_sub_one P hP3)
    hζ.toInteger_isPrimitiveRoot
  have hz' : jacobiSum (cubChar P hP3) (cubChar P hP3) = -1 + z * (ω - 1) ^ 2 := hz
  exact ⟨-(z * ω), by rw [hz']; linear_combination z * lam_sq⟩

omit hP3 in
theorem inverse_of_cube {y : 𝓞 K} (hy : y ^ 3 = 1) : Ring.inverse y = y ^ 2 := by
  have hu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ 2, by rw [← pow_succ']; exact hy⟩
  rw [← mul_one (Ring.inverse y), Ring.inverse_mul_eq_iff_eq_mul _ _ _ hu, ← pow_succ', hy]

theorem cubChar_inv_apply (x : 𝓞 K ⧸ P) : (cubChar P hP3)⁻¹ x = cj (cubChar P hP3 x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have h3 := (cubChar_spec P hP3 u).2
    rw [MulChar.inv_apply_eq_inv, inverse_of_cube h3, cj_of_cube h3]
  · rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit _ hx, map_zero]

theorem jacobiSum_inv_eq_cj : jacobiSum (cubChar P hP3)⁻¹ (cubChar P hP3)⁻¹ =
    cj (jacobiSum (cubChar P hP3) (cubChar P hP3)) := by
  simp only [jacobiSum, map_sum, map_mul, cubChar_inv_apply]

theorem jacobiSum_mul_cj : jacobiSum (cubChar P hP3) (cubChar P hP3) *
    cj (jacobiSum (cubChar P hP3) (cubChar P hP3)) = Fintype.card (𝓞 K ⧸ P) := by
  rw [← jacobiSum_inv_eq_cj]
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := RingOfIntegers.coe_injective
  apply hinj
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp, ← MulChar.ringHomComp_inv,
    map_natCast]
  have hne : (cubChar P hP3).ringHomComp (algebraMap (𝓞 K) K) ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff hinj).2 (cubChar_ne_one P hP3)
  apply jacobiSum_mul_jacobiSum_inv _ hne hne
  · rw [← MulChar.ringHomComp_mul]
    refine (MulChar.ringHomComp_ne_one_iff hinj).2 fun h => cubChar_ne_one P hP3 ?_
    have h3 := cubChar_pow_three P hP3
    rw [pow_succ, sq, h, one_mul] at h3; exact h3
  · obtain ⟨n, hp, -⟩ := FiniteField.card (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P))
    rw [ringChar.eq_zero]; exact hp.ne_zero.symm

/-- **The Jacobi sum of the cubic character at a primary generator**: `J(χ_P, χ_P) = −π` for
`P = (π)` with `π ≡ 1 (mod 3)`. -/
theorem jacobiSum_eq_neg {π : 𝓞 K} (hπ : Primary π) (hP : P = span {π}) :
    jacobiSum (cubChar P hP3) (cubChar P hP3) = -π := by
  set J := jacobiSum (cubChar P hP3) (cubChar P hP3)
  have hNP : absNorm P = Fintype.card (𝓞 K ⧸ P) := by
    rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hsq : absNorm (span {J}) ^ 2 = absNorm P ^ 2 := by
    have e1 : span {J} * span {cj J} = span {((Fintype.card (𝓞 K ⧸ P) : ℕ) : 𝓞 K)} := by
      rw [Ideal.span_singleton_mul_span_singleton, jacobiSum_mul_cj]
    have := congrArg absNorm e1
    rw [map_mul, absNorm_span_cj, absNorm_natCast_span_sq] at this
    rw [hNP, ← this, sq]
  have hN : absNorm (span {J}) = absNorm P :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hsq
  have hle : span {J} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 (jacobiSum_mem P hP3)
  have hP0 : absNorm P ≠ 0 := by
    rw [hNP]; exact Fintype.card_ne_zero
  have heq := eq_of_le_of_absNorm_eq hle hN hP0
  rw [hP, Ideal.span_singleton_eq_span_singleton] at heq
  obtain ⟨u, hu⟩ := heq.symm
  -- `J = π·u` with `J ≡ −1` and `π ≡ 1`, so `−u ≡ 1` and `u = −1`
  have h1 : Primary ((-u : (𝓞 K)ˣ) * π) := by
    have := three_dvd_jacobiSum_add_one P hP3
    unfold Primary
    rw [Units.val_neg, show -(u : 𝓞 K) * π - 1 = -(J + 1) by rw [← hu]; ring]
    exact (dvd_neg).2 this
  have h2 := hπ.unit_eq_one h1
  have hu1 : u = -1 := by rw [← neg_neg u, h2]
  rw [← hu, hu1, Units.val_neg, Units.val_one, mul_neg_one]

end Jacobi

/-! ### The Gauss-sum relation in characteristic `ℓ` -/

section Gauss

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P)
variable (Q : Ideal (𝓞 K)) [hQm : Q.IsMaximal] (hQ3 : (3 : 𝓞 K) ∉ Q)

/-- Frobenius on a Gauss sum, iterated. -/
theorem gaussSum_pow_char_pow {F E : Type*} [Field F] [Fintype F] [Field E] (ℓ : ℕ)
    [Fact ℓ.Prime] [CharP E ℓ] (χ : MulChar F E) (ψ : AddChar F E) (k : ℕ) :
    gaussSum χ ψ ^ ℓ ^ k = gaussSum (χ ^ ℓ ^ k) (ψ ^ ℓ ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, gaussSum_frob, ← pow_mul, ← pow_mul, ← pow_succ]

include hQ3 in
/-- Cube roots of unity are determined by their residues modulo `Q`. -/
theorem cube_eq_of_mk_eq {y z : 𝓞 K} (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (h : Ideal.Quotient.mk Q y = Ideal.Quotient.mk Q z) : y = z := by
  obtain ⟨u, rfl⟩ := isUnit_iff_exists_inv.2 ⟨y ^ 2, by rw [← pow_succ']; exact hy⟩
  obtain ⟨v, rfl⟩ := isUnit_iff_exists_inv.2 ⟨z ^ 2, by rw [← pow_succ']; exact hz⟩
  have hu : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hy, Units.val_one])
  have hv : v ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hz, Units.val_one])
  have : red Q u = red Q v := Units.ext (by rw [coe_red, coe_red]; exact h)
  rw [red_cube_injective Q hQ3 hu hv this]

include hP3 hQ3 in
/-- **The fundamental relation.** For `P = (π)` with `π` primary and a maximal `Q` prime to `3` and to
`N(P)`: `χ_Q(−N(P)·π) = χ_P(N(Q))²`. The Gauss sum `g` of `χ_P` with values in a field of
characteristic `ℓ = char(𝓞/Q)` satisfies `g³ = N(P)·J(χ_P, χ_P) = −N(P)·π` and, by Frobenius,
`g^{N(Q)} = χ_P(N(Q))⁻¹·g`; and `x^{(N(Q)−1)/3}` is `χ_Q(x)` modulo `Q`. -/
theorem cubChar_fundamental {π : 𝓞 K} (hπ : Primary π) (hP : P = span {π})
    (hPQ : ((Fintype.card (𝓞 K ⧸ P) : ℕ) : 𝓞 K) ∉ Q) :
    cubChar Q hQ3 (Ideal.Quotient.mk Q (-((Fintype.card (𝓞 K ⧸ P) : ℕ) : 𝓞 K) * π)) =
      cubChar P hP3 ((Fintype.card (𝓞 K ⧸ Q) : ℕ) : 𝓞 K ⧸ P) ^ 2 := by
  classical
  set F := 𝓞 K ⧸ P
  set E₀ := 𝓞 K ⧸ Q
  have hch : ringChar E₀ ≠ ringChar F := by
    intro h
    obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
    apply hPQ
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hc, Nat.cast_pow, ← h,
      ringChar.Nat.cast_ringChar, zero_pow (PNat.ne_zero n)]
  let ψ := AddChar.FiniteField.primitiveChar F E₀ hch
  let E := CyclotomicField ψ.n E₀
  let ι : 𝓞 K →+* E := (algebraMap E₀ E).comp (Ideal.Quotient.mk Q)
  let χ : MulChar F E := (cubChar P hP3).ringHomComp ι
  have hιinj : Function.Injective (algebraMap E₀ E) := (algebraMap E₀ E).injective
  -- `χ` is a nontrivial cubic character
  have hχ3 : χ ^ 3 = 1 := by
    rw [MulChar.ringHomComp_pow, cubChar_pow_three, MulChar.ringHomComp_one]
  have hχ1 : χ ≠ 1 := by
    intro h
    apply cubChar_ne_one P hP3
    rw [MulChar.eq_one_iff] at h ⊢
    intro a
    have ha := h a
    have h3 := (cubChar_spec P hP3 a).2
    have hu : IsUnit (cubChar P hP3 a) := isUnit_iff_exists_inv.2 ⟨_, by rw [← pow_succ']; exact h3⟩
    obtain ⟨u, hu⟩ := hu
    have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, h3, Units.val_one])
    have : red Q u = red Q 1 := by
      apply Units.ext
      apply hιinj
      rw [coe_red, coe_red, hu]
      simpa [χ, ι] using ha
    rw [← hu, red_cube_injective Q hQ3 hu3 (one_pow 3) this, Units.val_one]
  have hord : orderOf χ = 3 := orderOf_eq_prime hχ3 hχ1
  have hm1 : χ (-1) = 1 := by
    have h1 : χ (-1) ^ 3 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), hχ3, MulChar.one_apply (isUnit_one.neg)]
    have h2 : χ (-1) ^ 2 = 1 := by
      rw [sq, ← map_mul, neg_one_mul, neg_neg, MulChar.map_one]
    calc χ (-1) = χ (-1) ^ 3 * (χ (-1) ^ 2)⁻¹ := by
          rw [h2, inv_one, mul_one, pow_succ, h2, one_mul]
      _ = 1 := by rw [h1, h2, inv_one, one_mul]
  -- the Gauss sum
  set g := gaussSum χ ψ.char
  have hcardF : ((Fintype.card F : ℕ) : E) ≠ 0 := by
    intro h
    apply hPQ
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hιinj
    rw [map_zero, map_natCast, map_natCast]; exact h
  have hg0 : g ≠ 0 := gaussSum_ne_zero_of_nontrivial hcardF hχ1 ψ.prim
  have hg3 : g ^ 3 = ι (-((Fintype.card F : ℕ) : 𝓞 K) * π) := by
    have := gaussSum_pow_eq_prod_jacobiSum (χ := χ) (ψ := ψ.char) (by rw [hord]; norm_num) ψ.prim
    rw [hord] at this
    rw [this, hm1, one_mul]
    simp only [show Finset.Ico 1 (3 - 1) = {1} by rfl, Finset.prod_singleton, pow_one]
    rw [jacobiSum_ringHomComp, jacobiSum_eq_neg P hP3 hπ hP, map_mul, map_neg, map_neg, map_natCast]
    ring
  -- `N(Q) = 3m + 1`
  have hN1 : 1 ≤ Fintype.card E₀ := Fintype.card_pos
  obtain ⟨m, hm⟩ : 3 ∣ Fintype.card E₀ - 1 := three_dvd_card_sub_one Q hQ3
  have hNm : Fintype.card E₀ = 3 * m + 1 := by omega
  have hm3 : m3 Q = m := by
    show (Fintype.card E₀ - 1) / 3 = m
    omega
  -- Frobenius: `g^{N(Q)} = g(χ^{N(Q)}, ψ^{N(Q)}) = χ⁻¹(N(Q))·g`
  obtain ⟨f, hℓ, hcQ⟩ := FiniteField.card E₀ (ringChar E₀)
  have : Fact (ringChar E₀).Prime := ⟨hℓ⟩
  have hchE : CharP E (ringChar E₀) := by
    rw [Algebra.ringChar_eq E₀ E]; exact ringChar.charP E
  have hfrob := gaussSum_pow_char_pow (ringChar E₀) χ ψ.char f
  rw [← hcQ] at hfrob
  have hχN : χ ^ Fintype.card E₀ = χ := by rw [hNm, pow_succ, pow_mul, hχ3, one_pow, one_mul]
  rw [hχN, AddChar.pow_mulShift] at hfrob
  have hNF : IsUnit ((Fintype.card E₀ : ℕ) : F) := by
    rw [isUnit_iff_ne_zero, hcQ, Nat.cast_pow]
    apply pow_ne_zero
    intro h0
    obtain ⟨-, hpF, -⟩ := FiniteField.card F (ringChar F)
    rw [ringChar.spec F] at h0
    exact hch ((Nat.prime_dvd_prime_iff_eq hpF hℓ).1 h0).symm
  have hshift := gaussSum_mulShift_eq χ ψ.char hNF.unit
  rw [IsUnit.unit_spec] at hshift
  rw [hshift] at hfrob
  have key : (g ^ 3) ^ m = χ⁻¹ ((Fintype.card E₀ : ℕ) : F) := by
    have e : g ^ Fintype.card E₀ = (g ^ 3) ^ m * g := by rw [hNm, pow_succ, pow_mul]
    rw [e] at hfrob
    exact mul_right_cancel₀ hg0 hfrob
  have hχinv : χ⁻¹ = χ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hχ3)
  rw [hχinv, MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0), hg3, ← map_pow,
    MulChar.ringHomComp_apply, ← map_pow] at key
  have key2 : Ideal.Quotient.mk Q ((-((Fintype.card F : ℕ) : 𝓞 K) * π) ^ m) =
      Ideal.Quotient.mk Q (cubChar P hP3 ((Fintype.card E₀ : ℕ) : F) ^ 2) := hιinj key
  -- Euler's criterion modulo `Q`
  have hπQ : π ∉ Q := fun h => hPQ (by
    have hle : P ≤ Q := by rw [hP, Ideal.span_singleton_le_iff_mem]; exact h
    have hPeq : P = Q := hPm.eq_of_le hQm.ne_top hle
    rw [← hPeq]
    have hNP : absNorm P = Fintype.card F := by
      rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have := natCast_span_le P
    rw [hNP] at this
    exact this (Ideal.mem_span_singleton_self _))
  set x := Ideal.Quotient.mk Q (-((Fintype.card F : ℕ) : 𝓞 K) * π) with hx
  have hx0 : x ≠ 0 := by
    rw [hx, Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    rcases hQm.isPrime.mem_or_mem h with h1 | h1
    · exact hPQ (Q.neg_mem_iff.1 h1)
    · exact hπQ h1
  have hspec := cubChar_spec Q hQ3 (Units.mk0 x hx0)
  rw [Units.val_mk0, hm3, hx, ← map_pow, key2] at hspec
  have hc3 := (cubChar_spec P hP3 hNF.unit).2
  rw [IsUnit.unit_spec] at hc3
  have hc3' : (cubChar P hP3 ((Fintype.card E₀ : ℕ) : F) ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  exact cube_eq_of_mk_eq Q hQ3 hspec.2 hc3' hspec.1

end Gauss

end Eis

#print axioms Eis.cube_root_cases
#print axioms Eis.red_cube_injective
#print axioms Eis.three_dvd_card_sub_one
#print axioms Eis.cubChar_spec
#print axioms Eis.exists_coords
#print axioms Eis.unit_eq_one_of_three_dvd
#print axioms Eis.exists_primary
#print axioms Eis.Primary.unit_eq_one
#print axioms Eis.cj_ω
#print axioms Eis.cj_cj
#print axioms Eis.absNorm_span_cj
#print axioms Eis.cubChar_ne_one
#print axioms Eis.jacobiSum_mem
#print axioms Eis.three_dvd_jacobiSum_add_one
#print axioms Eis.jacobiSum_mul_cj
#print axioms Eis.jacobiSum_eq_neg
#print axioms Eis.gaussSum_pow_char_pow
#print axioms Eis.cubChar_fundamental
