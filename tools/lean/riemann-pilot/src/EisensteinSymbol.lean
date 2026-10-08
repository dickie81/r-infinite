import Mathlib

/-! # S1, part 1: the sextic residue symbol on `ℤ[ω]` (round 281)

`K = ℚ(ζ₃)` is Mathlib's `CyclotomicField 3 ℚ`. Its ring of integers `𝓞 K = ℤ[ω]` is a principal
ideal domain (Mathlib's `three_pid`), and its units are `±1, ±ω, ±ω²` (`units_mem`, from Mathlib's
`IsCyclotomicExtension.Rat.Three.Units.mem`), so every unit has sixth power `1` (`units_pow_six`).

* **Away from `6`.** Let `P` be a maximal ideal with `6 ∉ P`. Reduction modulo `P` is injective on
  units (`red_injective`), every sixth root of unity modulo `P` is the reduction of a unit
  (`exists_red_eq`), and so `6 ∣ N(P) − 1` (`six_dvd_card_sub_one`).
* **The sextic residue character** `χ_P` (`chi6`): `χ_P(x) = σ(u)`, where `u` is the unit with
  `u ≡ x^{(N(P)−1)/6} (mod P)` and `σ : K → ℂ` is a fixed complex embedding (`chi6_spec`). It has
  `χ_P⁶ = 1` (`chi6_pow_six`).
* **The symbol** `(a/𝔞)₆ = Π_{P ∣ 𝔞} χ_P(a)` (`sym6`) is the product over the prime factors of `𝔞`,
  with multiplicity. It is multiplicative in `a` and in `𝔞` (`sym6_mul_left`, `sym6_mul_right`), and
  `χ_P(a) = 0` when `a ∈ P` (`chiP_eq_zero_of_mem`). The cubic and quadratic symbols are its square
  and cube (`sym3`, `sym2`).

The definitions use no primary normalisation: given `σ` they are canonical. Primary generators,
cubic reciprocity, the ideal counts and the split-prime count are later parts of S1.
-/

open NumberField

namespace Eis

abbrev K : Type := CyclotomicField 3 ℚ

instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
instance : NumberField K := IsCyclotomicExtension.numberField {3} ℚ K
instance : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K

noncomputable def ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
theorem hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K

/-- `ω`, a primitive cube root of unity in `𝓞 K = ℤ[ω]`. -/
noncomputable def ω : 𝓞 K := hζ.toInteger

/-- `ω` as a unit. -/
noncomputable def ωu : (𝓞 K)ˣ := (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit

theorem coe_ωu : (ωu : 𝓞 K) = ω := rfl

theorem ω_cube : ω ^ 3 = 1 := hζ.toInteger_cube_eq_one

theorem ω_sq_add : ω ^ 2 + ω + 1 = 0 := by
  have := IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ
  simpa [IsCyclotomicExtension.Rat.Three.coe_eta, ω] using this

/-- The units of `ℤ[ω]` are `±1, ±ω, ±ω²`. -/
theorem units_mem (u : (𝓞 K)ˣ) : u ∈ [1, -1, ωu, -ωu, ωu ^ 2, -ωu ^ 2] :=
  IsCyclotomicExtension.Rat.Three.Units.mem hζ u

theorem ωu_cube : ωu ^ 3 = 1 := Units.ext (by simp [coe_ωu, ω_cube])

theorem units_pow_six (u : (𝓞 K)ˣ) : u ^ 6 = 1 := by
  have h3 := ωu_cube
  have e6 : Even 6 := ⟨3, rfl⟩
  have hω : ωu ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, h3, one_pow]
  have hω2 : (ωu ^ 2) ^ 6 = 1 := by rw [← pow_mul, show 2 * 6 = 3 * 4 by rfl, pow_mul, h3, one_pow]
  rcases List.mem_cons.1 (units_mem u) with rfl | h
  · exact one_pow 6
  rcases List.mem_cons.1 h with rfl | h
  · rw [e6.neg_pow, one_pow]
  rcases List.mem_cons.1 h with rfl | h
  · exact hω
  rcases List.mem_cons.1 h with rfl | h
  · rw [e6.neg_pow, hω]
  rcases List.mem_cons.1 h with rfl | h
  · exact hω2
  rcases List.mem_cons.1 h with rfl | h
  · rw [e6.neg_pow, hω2]
  simp at h

/-- `λ = ω − 1` has `λ² = −3ω`. -/
theorem lam_sq : (ω - 1) ^ 2 = -3 * ω := by linear_combination ω_sq_add

section Residue

variable (P : Ideal (𝓞 K)) [hP : P.IsPrime]

omit hP in
theorem six_mem_of_two_mem (h : (2 : 𝓞 K) ∈ P) : (6 : 𝓞 K) ∈ P := by
  have : (6 : 𝓞 K) = 3 * 2 := by norm_num
  rw [this]; exact P.mul_mem_left _ h

omit hP in
theorem six_mem_of_lam_mem (h : ω - 1 ∈ P) : (6 : 𝓞 K) ∈ P := by
  have h2 : (ω - 1) ^ 2 ∈ P := P.pow_mem_of_mem h 2 (by norm_num)
  rw [lam_sq] at h2
  have h3 : (3 : 𝓞 K) ∈ P := by
    have : (3 : 𝓞 K) = -(-3 * ω) * ω ^ 2 := by linear_combination (-3 : 𝓞 K) * ω_cube
    rw [this]; exact P.mul_mem_right _ (P.neg_mem_iff.2 h2)
  have : (6 : 𝓞 K) = 2 * 3 := by norm_num
  rw [this]; exact P.mul_mem_left _ h3

/-- Away from `6`, a unit `w ≠ 1` of `ℤ[ω]` stays `≠ 1` modulo `P`. -/
theorem sub_one_not_mem (hP6 : (6 : 𝓞 K) ∉ P) {w : (𝓞 K)ˣ} (hw : w ≠ 1) : (w : 𝓞 K) - 1 ∉ P := by
  intro hmem
  have hne : ∀ x : 𝓞 K, IsUnit x → x ∉ P := fun x hx hxP => hP.ne_top (P.eq_top_of_isUnit_mem hxP hx)
  rcases List.mem_cons.1 (units_mem w) with rfl | h
  · exact hw rfl
  rcases List.mem_cons.1 h with rfl | h
  · apply hP6; apply six_mem_of_two_mem
    have : (2 : 𝓞 K) = -((((-1 : (𝓞 K)ˣ)) : 𝓞 K) - 1) := by simp; norm_num
    rw [this]; exact P.neg_mem_iff.2 hmem
  rcases List.mem_cons.1 h with rfl | h
  · exact hP6 (six_mem_of_lam_mem P (by simpa [coe_ωu] using hmem))
  rcases List.mem_cons.1 h with rfl | h
  · have hu2 : IsUnit (ω ^ 2) := by rw [← coe_ωu]; exact ωu.isUnit.pow 2
    apply hne (ω ^ 2) hu2
    have : ω ^ 2 = ((-ωu : (𝓞 K)ˣ) : 𝓞 K) - 1 := by
      simp [coe_ωu]; linear_combination ω_sq_add
    rw [this]; exact hmem
  rcases List.mem_cons.1 h with rfl | h
  · have hf : (ω - 1) * (ω + 1) ∈ P := by
      have : (ω - 1) * (ω + 1) = ((ωu ^ 2 : (𝓞 K)ˣ) : 𝓞 K) - 1 := by simp [coe_ωu]; ring
      rw [this]; exact hmem
    rcases hP.mem_or_mem hf with h1 | h1
    · exact hP6 (six_mem_of_lam_mem P h1)
    · apply hne (ω + 1) _ h1
      have : ω + 1 = ((-(ωu ^ 2) : (𝓞 K)ˣ) : 𝓞 K) := by simp [coe_ωu]; linear_combination ω_sq_add
      rw [this]; exact Units.isUnit _
  rcases List.mem_cons.1 h with rfl | h
  · apply hne ω (by rw [← coe_ωu]; exact ωu.isUnit)
    have : ω = ((-(ωu ^ 2) : (𝓞 K)ˣ) : 𝓞 K) - 1 := by simp [coe_ωu]; linear_combination ω_sq_add
    rw [this]; exact hmem
  simp at h

end Residue

section Char

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal]

noncomputable instance fieldQ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P

theorem ne_bot : P ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField K)

noncomputable instance fintypeQ : Fintype (𝓞 K ⧸ P) :=
  @Fintype.ofFinite _ (Ideal.finiteQuotientOfFreeOfNeBot P (ne_bot P))

/-- Reduction of units modulo `P`. -/
noncomputable def red : (𝓞 K)ˣ →* (𝓞 K ⧸ P)ˣ :=
  Units.map (Ideal.Quotient.mk P : 𝓞 K →* 𝓞 K ⧸ P)

omit hPm in
theorem coe_red (u : (𝓞 K)ˣ) : ((red P u : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) = Ideal.Quotient.mk P (u : 𝓞 K) :=
  rfl

variable (hP6 : (6 : 𝓞 K) ∉ P)
include hP6

theorem red_injective : Function.Injective (red P) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  apply sub_one_not_mem P hP6 hne
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ← coe_red, hw, Units.val_one, sub_self]

omit hPm hP6 in
theorem mk_ω_sq_add : (Ideal.Quotient.mk P ω) ^ 2 + Ideal.Quotient.mk P ω + 1 = 0 := by
  rw [← map_pow, ← map_add, ← map_one (Ideal.Quotient.mk P), ← map_add, ω_sq_add, map_zero]

omit hPm hP6 in
theorem mk_ω_cube : (Ideal.Quotient.mk P ω) ^ 3 = 1 := by
  rw [← map_pow, ω_cube, map_one]

omit hP6 in
/-- Every sixth root of unity modulo `P` is the reduction of a unit. -/
theorem exists_red_eq {ξ : 𝓞 K ⧸ P} (hξ : ξ ^ 6 = 1) :
    ∃ u : (𝓞 K)ˣ, ((red P u : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) = ξ := by
  set e := Ideal.Quotient.mk P ω with he_def
  have he := mk_ω_sq_add P
  have he3 := mk_ω_cube P
  rw [← he_def] at he he3
  have h1 : ξ ^ 3 - 1 = (ξ - 1) * (ξ - e) * (ξ - e ^ 2) := by
    linear_combination (ξ ^ 2 - ξ) * he + (1 - ξ) * he3
  have h2 : ξ ^ 3 + 1 = (ξ + 1) * (ξ + e) * (ξ + e ^ 2) := by
    linear_combination (-ξ ^ 2 - ξ) * he + (-ξ - 1) * he3
  have h0 : (ξ - 1) * (ξ - e) * (ξ - e ^ 2) * ((ξ + 1) * (ξ + e) * (ξ + e ^ 2)) = 0 := by
    rw [← h1, ← h2]; linear_combination hξ
  have hω : ((ωu : (𝓞 K)ˣ) : 𝓞 K) = ω := coe_ωu
  rcases mul_eq_zero.1 h0 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact ⟨1, by rw [coe_red]; simp; linear_combination -h⟩
      · exact ⟨ωu, by rw [coe_red, hω, ← he_def]; linear_combination -h⟩
    · exact ⟨ωu ^ 2, by rw [coe_red, Units.val_pow_eq_pow_val, hω, map_pow, ← he_def]; linear_combination -h⟩
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact ⟨-1, by rw [coe_red]; simp; linear_combination -h⟩
      · exact ⟨-ωu, by rw [coe_red, Units.val_neg, hω, map_neg, ← he_def]; linear_combination -h⟩
    · exact ⟨-(ωu ^ 2), by
        rw [coe_red, Units.val_neg, Units.val_pow_eq_pow_val, hω, map_neg, map_pow, ← he_def]
        linear_combination -h⟩

/-- `6 ∣ N(P) − 1`: the reduction of `−ω` has order `6`. -/
theorem six_dvd_card_sub_one : 6 ∣ Fintype.card (𝓞 K ⧸ P) - 1 := by
  classical
  set g := red P (-ωu)
  have hω2 : ωu ^ 2 ≠ 1 := by
    intro h
    have := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, coe_ωu, Units.val_one] at this
    exact hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) this
  have hm1 : (-1 : (𝓞 K)ˣ) ≠ 1 := by
    intro h
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    have h2 : (2 : 𝓞 K) = 0 := by linear_combination -this
    exact two_ne_zero h2
  have hg6 : g ^ 6 = 1 := by rw [← map_pow, units_pow_six, map_one]
  have hg2 : g ^ 2 ≠ 1 := by
    rw [← map_pow, show (-ωu) ^ 2 = ωu ^ 2 by rw [neg_sq]]
    intro h; exact hω2 (red_injective P hP6 (by rw [h, map_one]))
  have hg3 : g ^ 3 ≠ 1 := by
    rw [← map_pow, show (-ωu) ^ 3 = -1 by rw [neg_pow, ωu_cube, mul_one]; exact Odd.neg_one_pow ⟨1, rfl⟩]
    intro h; exact hm1 (red_injective P hP6 (by rw [h, map_one]))
  have hord : orderOf g = 6 := by
    have hd : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one hg6
    have h2 : ¬ orderOf g ∣ 2 := fun h => hg2 (orderOf_dvd_iff_pow_eq_one.1 h)
    have h3 : ¬ orderOf g ∣ 3 := fun h => hg3 (orderOf_dvd_iff_pow_eq_one.1 h)
    have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hd (by norm_num)
    have hle : orderOf g ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : orderOf g <;> simp_all
  rw [← Fintype.card_units, ← hord]
  exact orderOf_dvd_card

end Char

section Symbol

/-- The fixed complex embedding of `K`. -/
noncomputable def σ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom

/-- Units of `ℤ[ω]` in `ℂ`. -/
noncomputable def σu : (𝓞 K)ˣ →* ℂˣ := Units.map ((σ.comp (algebraMap (𝓞 K) K) : 𝓞 K →+* ℂ) : 𝓞 K →* ℂ)

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P)

/-- The exponent `(N(P) − 1)/6`. -/
noncomputable def m6 : ℕ := (Fintype.card (𝓞 K ⧸ P) - 1) / 6

include hP6

theorem pow_m6_pow_six (x : (𝓞 K ⧸ P)ˣ) : (x ^ m6 P) ^ 6 = 1 := by
  classical
  rw [← pow_mul, m6, Nat.div_mul_cancel (six_dvd_card_sub_one P hP6), ← Fintype.card_units]
  exact pow_card_eq_one

/-- `x ↦ x^{(N(P)−1)/6}`, into the sixth roots of unity. -/
noncomputable def powR : (𝓞 K ⧸ P)ˣ →* rootsOfUnity 6 (𝓞 K ⧸ P) :=
  (powMonoidHom (m6 P)).codRestrict _ fun x => (mem_rootsOfUnity _ _).2 (pow_m6_pow_six P hP6 x)

omit hP6 in
/-- Reduction of units, into the sixth roots of unity. -/
noncomputable def redR : (𝓞 K)ˣ →* rootsOfUnity 6 (𝓞 K ⧸ P) :=
  (red P).codRestrict _ fun u => (mem_rootsOfUnity _ _).2 (by rw [← map_pow, units_pow_six, map_one])

theorem redR_bijective : Function.Bijective (redR P) := by
  refine ⟨fun u v h => red_injective P hP6 (congrArg Subtype.val h), fun ξ => ?_⟩
  have hξ : ((ξ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) ^ 6 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ξ.2, Units.val_one]
  obtain ⟨u, hu⟩ := exists_red_eq P hξ
  exact ⟨u, Subtype.ext (Units.ext hu)⟩

/-- The unit group of `ℤ[ω]` is the group of sixth roots of unity modulo `P`. -/
noncomputable def redEquiv : (𝓞 K)ˣ ≃* rootsOfUnity 6 (𝓞 K ⧸ P) :=
  MulEquiv.ofBijective (redR P) (redR_bijective P hP6)

/-- **The sextic residue character modulo `P`**: `χ_P(x) = σ(u)`, where `u` is the unit of `ℤ[ω]`
with `u ≡ x^{(N(P)−1)/6} (mod P)`. -/
noncomputable def chi6 : MulChar (𝓞 K ⧸ P) ℂ :=
  MulChar.ofUnitHom (σu.comp ((redEquiv P hP6).symm.toMonoidHom.comp (powR P hP6)))

/-- The defining congruence. -/
theorem chi6_spec (x : (𝓞 K ⧸ P)ˣ) : ∃ u : (𝓞 K)ˣ,
    Ideal.Quotient.mk P (u : 𝓞 K) = ((x : 𝓞 K ⧸ P)) ^ m6 P ∧ chi6 P hP6 x = σ (u : 𝓞 K) := by
  refine ⟨(redEquiv P hP6).symm (powR P hP6 x), ?_, ?_⟩
  · have h := (redEquiv P hP6).apply_symm_apply (powR P hP6 x)
    have h2 : red P ((redEquiv P hP6).symm (powR P hP6 x)) = x ^ m6 P := congrArg Subtype.val h
    have h3 := congrArg Units.val h2
    rw [coe_red, Units.val_pow_eq_pow_val] at h3
    exact h3
  · simp [chi6, σu]

/-- `χ_P^6 = 1`. -/
theorem chi6_pow_six : chi6 P hP6 ^ 6 = 1 := by
  ext x
  obtain ⟨u, -, hu⟩ := chi6_spec P hP6 x
  have h6 : ((u : 𝓞 K) : K) ^ 6 = 1 := by
    have : (u : 𝓞 K) ^ 6 = 1 := by rw [← Units.val_pow_eq_pow_val, units_pow_six, Units.val_one]
    exact_mod_cast congrArg (fun y : 𝓞 K => (y : K)) this
  rw [MulChar.pow_apply_coe, hu, MulChar.one_apply_coe, ← map_pow, h6, map_one]

end Symbol

section IdealSymbol

open Classical in
/-- `χ_P(a)` for every ideal `P`: `0` unless `P` is maximal and `6 ∉ P`. -/
noncomputable def chiP (P : Ideal (𝓞 K)) (a : 𝓞 K) : ℂ :=
  if h : P.IsMaximal ∧ (6 : 𝓞 K) ∉ P then
    haveI := h.1; chi6 P h.2 (Ideal.Quotient.mk P a)
  else 0

theorem chiP_mul (P : Ideal (𝓞 K)) (a b : 𝓞 K) : chiP P (a * b) = chiP P a * chiP P b := by
  unfold chiP
  split_ifs with h
  · have := h.1; rw [map_mul, map_mul]
  · simp

theorem chiP_one {P : Ideal (𝓞 K)} (h : P.IsMaximal ∧ (6 : 𝓞 K) ∉ P) : chiP P 1 = 1 := by
  unfold chiP
  split_ifs with h'
  · have := h'.1; rw [map_one, MulChar.map_one]
  · exact absurd h h'

theorem chiP_eq_zero_of_mem {P : Ideal (𝓞 K)} {a : 𝓞 K} (ha : a ∈ P) : chiP P a = 0 := by
  unfold chiP; split_ifs with h
  · have := h.1
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 ha, MulChar.map_zero]
  · rfl

/-- **The sextic residue symbol** `(a/𝔞)₆ = Π_{P ∣ 𝔞} χ_P(a)`, the product over the prime factors of
`𝔞` with multiplicity. -/
noncomputable def sym6 (a : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map fun P => chiP P a).prod

theorem sym6_mul_left (a b : 𝓞 K) (I : Ideal (𝓞 K)) : sym6 (a * b) I = sym6 a I * sym6 b I := by
  simp only [sym6, chiP_mul, Multiset.prod_map_mul]

theorem sym6_mul_right (a : 𝓞 K) {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
    sym6 a (I * J) = sym6 a I * sym6 a J := by
  simp only [sym6, UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add,
    Multiset.prod_add]

theorem sym6_one_right (a : 𝓞 K) : sym6 a 1 = 1 := by
  rw [sym6, UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-- The cubic and quadratic symbols are the square and the cube. -/
noncomputable def sym3 (a : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ := sym6 a I ^ 2
noncomputable def sym2 (a : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ := sym6 a I ^ 3

end IdealSymbol

end Eis

#print axioms Eis.units_pow_six
#print axioms Eis.sub_one_not_mem
#print axioms Eis.red_injective
#print axioms Eis.exists_red_eq
#print axioms Eis.six_dvd_card_sub_one
#print axioms Eis.chi6_spec
#print axioms Eis.chi6_pow_six
#print axioms Eis.chiP_mul
#print axioms Eis.chiP_eq_zero_of_mem
#print axioms Eis.sym6_mul_left
#print axioms Eis.sym6_mul_right
#print axioms Eis.sym6_one_right
