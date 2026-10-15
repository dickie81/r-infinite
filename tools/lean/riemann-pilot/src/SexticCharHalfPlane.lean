import CubicCharHalfPlane
import EisensteinQuadSupplement
import RealCharHalfPlane

/-!
# Round 490: the characters of order dividing `6`, `L(s, χ) ≠ 0` on `Re s > 11/12` (door 5(a), part 2)

Door 5(a) of round 481, completed: the half-plane for every Dirichlet character `χ` with `χ⁶ = 1`, of every modulus,
through the family's own members.

* **The member `q⁶`** (`sym6_natCast_pow_six`): `(q⁶/𝔞)₆` is `1` if `N𝔞` is prime to `q` and `0` otherwise, on the
  ideals of norm prime to `6`. So a member that matches `χ` on the norms prime to `6q`, times `q⁶`, matches it on
  every norm prime to `6`, both sides vanishing at the norms not prime to `q`; round 489's bridge
  `LFunction_ne_zero_of_member` then applies (`LFunction_ne_zero_of_member_coprime`).
* **The characters mod `9`** (`exists_member_nine`): every `χ` mod `9` has a member `ω^{2j}`. Round 362's
  `prod_chi3_omega` gives `(ω/𝔞)₃ = ω^{(N𝔞−1)/3}` and `N𝔞 ≡ 1 (mod 3)` (`cub_omega_ideal`), so
  `(ω/𝔞)₆² = σ(ω)^{(N𝔞−1)/3}`; and `N𝔞 ≡ 4^{(N𝔞−1)/3} (mod 9)` (`natCast_zmod_nine`), with `χ(4)` a cube root of
  unity, `σ(ω)^j` (`complex_cube_root_cases`).
* **Coprime moduli** (`unitsCRT`, `charFst`, `charSnd`, `eq_changeLevel_mul`): a character mod `mn` with
  `(m, n) = 1` is the product of its parts at `m` and `n`, lifted, through Mathlib's `ZMod.chineseRemainder` on
  units; the parts of a cubic character are cubic.
* **Prime powers** (`pow_totient_div_eq_one`, `factorsThrough_prime_of_cube`, `exists_cube_of_pow`,
  `factorsThrough_nine_of_cube`): the kernel of `(ℤ/m)ˣ → (ℤ/d)ˣ` has `φ(m)/φ(d)` elements. A cubic character mod
  `p^k`, `p ≠ 3`, factors through `p`, as `gcd(3, p^{k−1}) = 1`; one mod `3^k`, `k ≥ 2`, factors through `9`, as
  `(ℤ/3^k)ˣ` is cyclic (Mathlib's `ZMod.isCyclic_units_of_prime_pow`) and the elements of the kernel are cubes.
* **The members of the cubic characters** (`exists_member_cube`): for every `q` and every `χ` mod `q` with `χ³ = 1`,
  a member `u ≠ 0` with `(u/𝔞)₆ = χ(N𝔞)` on the norms prime to `6q`, by induction over prime powers and coprime
  products (Mathlib's `Nat.recOnPrimeCoprime`), with round 489's `exists_member_of_cube_prime` at the primes.
* **The real members** (`exists_member_real`): for `χ² = 1`, `d³` with `d = ψ(−1)f` for the primitive `ψ` mod `f`
  that induces `χ` (round 477's `apply_eq_jacobiSym`, round 474's `sym6_intCast_cube`).
* **`LFunction_ne_zero_of_pow_six`**: for every modulus `q ≥ 1` and every `χ` mod `q` with `χ⁶ = 1`,
  `L(s, χ) ≠ 0` on `Re s > 11/12`, the trivial character excepted at `s = 1`. For `χ² = 1` it is round 477's
  `LFunction_ne_zero_of_isQuadratic`; otherwise `χ = χ⁴χ³`, and the member of the cubic `χ⁴` times that of the
  real `χ³` is a member of `χ` (`exists_member_six`). The cubic case is `LFunction_ne_zero_of_cube`.
-/

open NumberField Ideal

namespace Eis

open DirichletCharacter HalfPlaneS0

/-! ### The member `q⁶` -/

section SixthPower

/-- A maximal ideal `Q` contains the rational integer `q` exactly when `N(Q)` is not prime to `q`. -/
theorem natCast_mem_iff {Q : Ideal (𝓞 K)} [hQ : Q.IsMaximal] (q : ℕ) :
    (q : 𝓞 K) ∈ Q ↔ ¬ (absNorm Q).Coprime q := by
  classical
  obtain ⟨f, hp, hc⟩ := FiniteField.card (𝓞 K ⧸ Q) (ringChar (𝓞 K ⧸ Q))
  have hN : absNorm Q = ringChar (𝓞 K ⧸ Q) ^ (f : ℕ) := by rw [absNorm_eq_card, hc]
  rw [hN, Nat.coprime_pow_left_iff f.pos, Nat.Prime.coprime_iff_not_dvd hp, not_not,
    ← CharP.cast_eq_zero_iff (𝓞 K ⧸ Q) (ringChar (𝓞 K ⧸ Q)), ← map_natCast (Ideal.Quotient.mk Q),
    Ideal.Quotient.eq_zero_iff_mem]

/-- **The member `q⁶`**: `(q⁶/𝔞)₆` is `1` if `N𝔞` is prime to `q` and `0` otherwise, on the ideals of norm prime
to `6`. -/
theorem sym6_natCast_pow_six (q : ℕ) {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    sym6 ((q : 𝓞 K) ^ 6) I = if (absNorm I).Coprime q then 1 else 0 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    exfalso
    rw [Submodule.zero_eq_bot, absNorm_bot] at hI
    norm_num at hI
  | h₂ I hu =>
    rw [Ideal.isUnit_iff.1 hu, absNorm_top, ← Ideal.one_eq_top, sym6_one_right,
      ite_eq_left_of_eq_true _ _ (eq_true (Nat.coprime_one_left q))]
  | h₃ I Q hI0 hQ ih =>
    rw [map_mul] at hI
    have hQN : (absNorm Q).Coprime 6 := Nat.Coprime.coprime_mul_right hI
    have hIN : (absNorm I).Coprime 6 := Nat.Coprime.coprime_mul_left hI
    obtain ⟨hQm, hQ6⟩ := isMaximal_and_six_not_mem hQ hQN
    have hsQ : sym6 ((q : 𝓞 K) ^ 6) Q = chiP Q ((q : 𝓞 K) ^ 6) := by
      rw [sym6, UniqueFactorizationMonoid.normalizedFactors_irreducible hQ.irreducible, normalize_eq,
        Multiset.map_singleton, Multiset.prod_singleton]
    rw [sym6_mul_right _ hQ.ne_zero hI0, ih hIN, hsQ, chiP_pow_of ⟨hQm, hQ6⟩, chiP_pow_six hQm hQ6, map_mul]
    have key : (absNorm Q * absNorm I).Coprime q ↔ (absNorm Q).Coprime q ∧ (absNorm I).Coprime q :=
      Nat.coprime_mul_iff_left
    by_cases hq : (q : 𝓞 K) ∈ Q
    · have hQq : ¬ (absNorm Q).Coprime q := (natCast_mem_iff q).1 hq
      rw [ite_eq_left_of_eq_true _ _ (eq_true hq), zero_mul,
        ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hQq (key.1 h).1)]
    · have hQq : (absNorm Q).Coprime q := not_not.1 (mt (natCast_mem_iff q).2 hq)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hq), one_mul]
      by_cases hIq : (absNorm I).Coprime q
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hIq), ite_eq_left_of_eq_true _ _ (eq_true (key.2 ⟨hQq, hIq⟩))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hIq),
          ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hIq (key.1 h).2)]

end SixthPower

/-! ### The cubic characters modulo `9` -/

section Nine

/-- The norm of an ideal prime to `3` is `1` mod `3`, and `(ω/𝔞)₃ = ω^{(N𝔞−1)/3}`. -/
theorem cub_omega_ideal {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    cub ω I = ω ^ ((absNorm I - 1) / 3) ∧ absNorm I % 3 = 1 := by
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    rw [absNorm_bot] at hI
    norm_num at hI
  have hN : absNorm I = ((UniqueFactorizationMonoid.normalizedFactors I).map absNorm).prod := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.prod_hom]
  have hs : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, P.IsMaximal ∧ (3 : 𝓞 K) ∉ P := by
    intro P hP
    have hPm := isMaximal_of_mem_nf hP
    refine ⟨hPm, fun h3 ↦ ?_⟩
    have hdvd : absNorm P ∣ absNorm I := by
      rw [hN]; exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hP)
    have hP3 : ¬ (absNorm P).Coprime 3 := (natCast_mem_iff 3).1 (by exact_mod_cast h3)
    exact hP3 (Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.coprime_dvd_right (by norm_num) hI))
  have h := prod_chi3_omega _ hs
  rw [← hN] at h
  exact h

/-- An integer `n ≡ 1 (mod 3)` is `4^{(n−1)/3}` modulo `9`. -/
theorem natCast_zmod_nine {n : ℕ} (hn : n % 3 = 1) : (n : ZMod 9) = 4 ^ ((n - 1) / 3) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 3 * t + 1 := ⟨n / 3, by omega⟩
  rw [show (3 * t + 1 - 1) / 3 = t by omega]
  obtain ⟨s, r, hr, rfl⟩ : ∃ s r, r < 3 ∧ t = 3 * s + r := ⟨t / 3, t % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [pow_add, pow_mul, show (4 : ZMod 9) ^ 3 = 1 by decide, one_pow, one_mul,
    show 3 * (3 * s + r) + 1 = 9 * s + (3 * r + 1) by ring, Nat.cast_add,
    (ZMod.natCast_eq_zero_iff (9 * s) 9).2 (dvd_mul_right 9 s), zero_add]
  interval_cases r <;> decide

/-- A cube root of unity in `ℂ` is `1`, `w` or `w²` for a cube root of unity `w ≠ 1`. -/
theorem complex_cube_root_cases {z w : ℂ} (hz : z ^ 3 = 1) (hw : w ^ 3 = 1) (hw1 : w ≠ 1) :
    z = 1 ∨ z = w ∨ z = w ^ 2 := by
  have h1w : 1 + w + w ^ 2 = 0 := by
    have : (w - 1) * (1 + w + w ^ 2) = 0 := by linear_combination hw
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hw1)
  have hfac : (z - 1) * (z - w) * (z - w ^ 2) = 0 := by
    linear_combination hz + (z - z ^ 2) * h1w + (z - 1) * hw
  rcases mul_eq_zero.1 hfac with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h))

/-- **The members of the characters modulo `9`**: for every `χ` mod `9` there is `u = ω^{2j}` with
`(u/𝔞)₆ = χ(N𝔞)` on the ideals of norm prime to `6`. On the norms, all `1` mod `3`, `χ` is a power of `χ(4)`, a
cube root of unity since `4³ = 1` mod `9`. -/
theorem exists_member_nine (χ : DirichletCharacter ℂ 9) :
    ∃ u : 𝓞 K, u ≠ 0 ∧ ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u I = χ (absNorm I) := by
  have h4 : χ 4 ^ 3 = 1 := by
    rw [← map_pow, show (4 : ZMod 9) ^ 3 = 1 by decide, map_one]
  have hw : σO ω ^ 3 = 1 := by rw [← map_pow, ω_cube, map_one]
  have hw1 : σO ω ≠ 1 := by
    intro h
    apply ω_ne_one
    exact σO_injective (by rw [RingHom.comp_apply] at h ⊢; simpa using h)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, χ 4 = σO ω ^ j := by
    rcases complex_cube_root_cases h4 hw hw1 with h | h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
    · exact ⟨2, h⟩
  refine ⟨ω ^ (2 * j), pow_ne_zero _ (ωu.ne_zero), fun I hI ↦ ?_⟩
  obtain ⟨hc, h3⟩ := cub_omega_ideal hI
  have hsq : sym6 ω I ^ 2 = σO ω ^ ((absNorm I - 1) / 3) := by
    rw [sym6_sq_eq_cub hI, hc, map_pow]
  have hpow : ∀ k : ℕ, sym6 (ω ^ k) I = sym6 ω I ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, sym6_one_left hI]
    | succ k ih => rw [pow_succ, sym6_mul_left, ih, pow_succ]
  rw [hpow, pow_mul, hsq, natCast_zmod_nine h3, map_pow, hj, ← pow_mul, ← pow_mul, mul_comm]

end Nine

/-! ### Characters modulo a product of coprime moduli -/

section CRT

variable {m n : ℕ} (hmn : m.Coprime n)

/-- The first coordinate of Mathlib's `ZMod.chineseRemainder` is the reduction modulo `m`. -/
theorem chineseRemainder_fst (x : ZMod (m * n)) :
    (ZMod.chineseRemainder hmn x).1 = ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x :=
  DFunLike.congr_fun (RingHom.ext_zmod ((RingHom.fst _ _).comp (ZMod.chineseRemainder hmn).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m))) x

/-- The second coordinate of Mathlib's `ZMod.chineseRemainder` is the reduction modulo `n`. -/
theorem chineseRemainder_snd (x : ZMod (m * n)) :
    (ZMod.chineseRemainder hmn x).2 = ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x :=
  DFunLike.congr_fun (RingHom.ext_zmod ((RingHom.snd _ _).comp (ZMod.chineseRemainder hmn).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n))) x

/-- The units modulo `mn` as pairs of units modulo `m` and `n`. -/
noncomputable def unitsCRT : (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hmn).toMulEquiv).trans MulEquiv.prodUnits

/-- The first coordinate of `unitsCRT` is Mathlib's `ZMod.unitsMap` to `m`. -/
theorem unitsCRT_fst (u : (ZMod (m * n))ˣ) : (unitsCRT hmn u).1 = ZMod.unitsMap (Nat.dvd_mul_right m n) u :=
  Units.ext (chineseRemainder_fst hmn u)

/-- The second coordinate of `unitsCRT` is Mathlib's `ZMod.unitsMap` to `n`. -/
theorem unitsCRT_snd (u : (ZMod (m * n))ˣ) : (unitsCRT hmn u).2 = ZMod.unitsMap (Nat.dvd_mul_left n m) u :=
  Units.ext (chineseRemainder_snd hmn u)

/-- The part of a character mod `mn` at `m`. -/
noncomputable def charFst (χ : DirichletCharacter ℂ (m * n)) : DirichletCharacter ℂ m :=
  MulChar.ofUnitHom (χ.toUnitHom.comp ((unitsCRT hmn).symm.toMonoidHom.comp (MonoidHom.inl _ _)))

/-- The part of a character mod `mn` at `n`. -/
noncomputable def charSnd (χ : DirichletCharacter ℂ (m * n)) : DirichletCharacter ℂ n :=
  MulChar.ofUnitHom (χ.toUnitHom.comp ((unitsCRT hmn).symm.toMonoidHom.comp (MonoidHom.inr _ _)))

/-- `charFst χ` at `v` is `χ` at the unit that is `v` modulo `m` and `1` modulo `n`. -/
theorem charFst_apply (χ : DirichletCharacter ℂ (m * n)) (v : (ZMod m)ˣ) :
    charFst hmn χ v = χ ((unitsCRT hmn).symm (v, 1) : (ZMod (m * n))ˣ) := by
  rw [charFst, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl

/-- `charSnd χ` at `v` is `χ` at the unit that is `1` modulo `m` and `v` modulo `n`. -/
theorem charSnd_apply (χ : DirichletCharacter ℂ (m * n)) (v : (ZMod n)ˣ) :
    charSnd hmn χ v = χ ((unitsCRT hmn).symm (1, v) : (ZMod (m * n))ˣ) := by
  rw [charSnd, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl

/-- **A character mod `mn` is the product of its parts at `m` and `n`.** -/
theorem eq_changeLevel_mul [NeZero m] [NeZero n] (χ : DirichletCharacter ℂ (m * n)) :
    χ = changeLevel (Nat.dvd_mul_right m n) (charFst hmn χ) *
      changeLevel (Nat.dvd_mul_left n m) (charSnd hmn χ) := by
  ext u
  rw [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd,
    ← ZMod.unitsMap_val (Nat.dvd_mul_right m n), ← ZMod.unitsMap_val (Nat.dvd_mul_left n m), ← unitsCRT_fst hmn,
    ← unitsCRT_snd hmn, charFst_apply, charSnd_apply,
    ← map_mul, ← Units.val_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, MulEquiv.symm_apply_apply]

/-- The part at `m` of a cubic character is cubic. -/
theorem charFst_pow_three {χ : DirichletCharacter ℂ (m * n)} (hχ : χ ^ 3 = 1) : charFst hmn χ ^ 3 = 1 := by
  ext v
  rw [MulChar.pow_apply_coe, charFst_apply, ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe,
    MulChar.one_apply_coe]

/-- The part at `n` of a cubic character is cubic. -/
theorem charSnd_pow_three {χ : DirichletCharacter ℂ (m * n)} (hχ : χ ^ 3 = 1) : charSnd hmn χ ^ 3 = 1 := by
  ext v
  rw [MulChar.pow_apply_coe, charSnd_apply, ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe,
    MulChar.one_apply_coe]

end CRT

/-! ### Characters of prime-power modulus -/

section PrimePower

/-- A character lifted to a multiple of its modulus keeps its values at the integers prime to the multiple. -/
theorem changeLevel_natCast {d m : ℕ} (h : d ∣ m) (ψ : DirichletCharacter ℂ d) {a : ℕ} (ha : a.Coprime m) :
    changeLevel h ψ a = ψ a := by
  have := changeLevel_eq_cast_of_dvd' ψ h (Nat.isCoprime_iff_coprime.2 ha)
  rwa [Int.cast_natCast, Int.cast_natCast] at this

/-- **The kernel of `(ℤ/m)ˣ → (ℤ/d)ˣ`** has `φ(m)/φ(d)` elements, so each of them has `u^{φ(m)/φ(d)} = 1`. -/
theorem pow_totient_div_eq_one {m d : ℕ} [NeZero m] (hd : d ∣ m) {u : (ZMod m)ˣ}
    (hu : ZMod.unitsMap hd u = 1) : u ^ (m.totient / d.totient) = 1 := by
  have hd0 : d ≠ 0 := fun h ↦ NeZero.ne m (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have : NeZero d := ⟨hd0⟩
  have hK : Nat.card (ZMod.unitsMap hd).ker * d.totient = m.totient := by
    have h1 := Subgroup.card_mul_index (ZMod.unitsMap hd).ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective hd), Subgroup.card_top,
      Nat.card_eq_fintype_card (α := (ZMod d)ˣ), Nat.card_eq_fintype_card (α := (ZMod m)ˣ),
      ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at h1
    exact h1
  rw [← hK, Nat.mul_div_cancel _ (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd0))]
  have h2 := congrArg Subtype.val
    (pow_card_eq_one' (G := (ZMod.unitsMap hd).ker) (x := ⟨u, MonoidHom.mem_ker.2 hu⟩))
  simpa using h2

/-- **A cubic character modulo `p^k`, `p ≠ 3`, factors through `p`**: the kernel of `(ℤ/p^k)ˣ → (ℤ/p)ˣ` has
exponent dividing `p^{k−1}`, prime to `3`. -/
theorem factorsThrough_prime_of_cube {p k : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hk : 0 < k)
    {χ : DirichletCharacter ℂ (p ^ k)} (hχ : χ ^ 3 = 1) : FactorsThrough χ p := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hd : p ∣ p ^ k := dvd_pow_self p hk.ne'
  rw [factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have h1 := pow_totient_div_eq_one hd hu
  rw [Nat.totient_prime_pow hp hk, Nat.totient_prime hp,
    Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hp.one_lt)] at h1
  have hv3 : χ u ^ 3 = 1 := by rw [← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  have hvk : χ u ^ (p ^ (k - 1)) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  have hcop : Nat.gcd 3 (p ^ (k - 1)) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
  have h := pow_gcd_eq_one.2 ⟨hv3, hvk⟩
  rw [hcop, pow_one] at h
  exact Units.ext (by rw [MulChar.coe_toUnitHom, h, Units.val_one])

/-- In a finite cyclic group whose order is divisible by `3`, every `x` with `x^{|G|/3} = 1` is a cube. -/
theorem exists_cube_of_pow {G : Type*} [Group G] [Finite G] [IsCyclic G] (h3 : 3 ∣ Nat.card G) {x : G}
    (hx : x ^ (Nat.card G / 3) = 1) : ∃ g : G, x = g ^ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨t, ht⟩ := h3
  have htpos : 0 < t := by
    have := Nat.card_pos (α := G)
    omega
  rw [ht, Nat.mul_div_cancel_left t (by norm_num : 0 < 3), ← zpow_natCast, ← zpow_mul] at hx
  have hdvd := orderOf_dvd_iff_zpow_eq_one.2 hx
  rw [hord, ht] at hdvd
  push_cast at hdvd
  obtain ⟨i, rfl⟩ : (3 : ℤ) ∣ j := (mul_dvd_mul_iff_right (by exact_mod_cast htpos.ne')).1 hdvd
  exact ⟨g ^ i, by rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring⟩

/-- **A cubic character modulo `3^k`, `k ≥ 2`, factors through `9`**: `(ℤ/3^k)ˣ` is cyclic of order `2·3^{k−1}`,
and the kernel of `(ℤ/3^k)ˣ → (ℤ/9)ˣ` has exponent dividing `3^{k−2}`, so its elements are cubes. -/
theorem factorsThrough_nine_of_cube {k : ℕ} (hk : 2 ≤ k) {χ : DirichletCharacter ℂ (3 ^ k)} (hχ : χ ^ 3 = 1) :
    FactorsThrough χ 9 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have : NeZero (3 ^ (j + 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hd : 9 ∣ 3 ^ (j + 2) := ⟨3 ^ j, by ring⟩
  rw [factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have h1 := pow_totient_div_eq_one hd hu
  have ht : (3 ^ (j + 2)).totient = 3 ^ j * 6 := by
    rw [show j + 2 = (j + 1) + 1 by ring, Nat.totient_prime_pow_succ Nat.prime_three, pow_succ]
    norm_num
    ring
  have h9 : (9 : ℕ).totient = 6 := by
    rw [show (9 : ℕ) = 3 ^ (1 + 1) by norm_num, Nat.totient_prime_pow_succ Nat.prime_three]
    norm_num
  rw [ht, h9, Nat.mul_div_cancel _ (by norm_num)] at h1
  have := ZMod.isCyclic_units_of_prime_pow 3 Nat.prime_three (by norm_num) (j + 2)
  have hcard : Nat.card (ZMod (3 ^ (j + 2)))ˣ = 3 * (3 ^ j * 2) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, ht]
    ring
  obtain ⟨g, rfl⟩ := exists_cube_of_pow (G := (ZMod (3 ^ (j + 2)))ˣ) ⟨_, hcard⟩
    (by rw [hcard, Nat.mul_div_cancel_left _ (by norm_num), pow_mul, h1, one_pow])
  exact Units.ext (by
    rw [MulChar.coe_toUnitHom, Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply_coe, hχ,
      MulChar.one_apply_coe, Units.val_one])

end PrimePower

/-! ### The members of the cubic characters -/

section Members

/-- The members of the cubic characters of prime modulus, the trivial one included, on the ideals of norm prime
to `6p`. -/
theorem exists_member_prime {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p} (hχ3 : χ ^ 3 = 1) :
    ∃ u : 𝓞 K, u ≠ 0 ∧ ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → (absNorm I).Coprime p →
      sym6 u I = χ (absNorm I) := by
  by_cases hχ : χ = 1
  · exact ⟨1, one_ne_zero, fun I hI hIp ↦ by
      rw [hχ, sym6_one_left hI, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).2 hIp)]⟩
  · obtain ⟨u, hu0, hu⟩ := exists_member_of_cube_prime hχ3 hχ
    exact ⟨u, hu0, fun I hI _ ↦ hu I hI⟩

/-- **The members of the cubic characters**: for every modulus `q` and every Dirichlet character `χ` mod `q` with
`χ³ = 1`, there is `u ≠ 0` with `(u/𝔞)₆ = χ(N𝔞)` for every ideal `𝔞` of norm prime to `6q`. -/
theorem exists_member_cube (q : ℕ) :
    ∀ χ : DirichletCharacter ℂ q, χ ^ 3 = 1 → ∃ u : 𝓞 K, u ≠ 0 ∧ ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 →
      (absNorm I).Coprime q → sym6 u I = χ (absNorm I) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero =>
    intro χ _
    refine ⟨1, one_ne_zero, fun I hI hI0 ↦ ?_⟩
    rw [Nat.coprime_zero_right] at hI0
    rw [sym6_one_left hI, hI0, Nat.cast_one, map_one]
  | prime_pow p k hp =>
    intro χ hχ
    have := Fact.mk hp
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero p)
      refine ⟨1, one_ne_zero, fun I hI _ ↦ ?_⟩
      rw [sym6_one_left hI, Subsingleton.elim ((absNorm I : ℕ) : ZMod (p ^ 0)) 1, map_one]
    · by_cases hp3 : p = 3
      · subst hp3
        obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : DirichletCharacter ℂ 9, ∀ n : ℕ, n.Coprime 3 → χ n = χ₀ n := by
          by_cases hk2 : 2 ≤ k
          · obtain ⟨h9, χ₀, rfl⟩ := factorsThrough_nine_of_cube hk2 hχ
            exact ⟨χ₀, fun n hn ↦ changeLevel_natCast h9 χ₀ (Nat.Coprime.pow_right k hn)⟩
          · have hd : 3 ^ k ∣ 9 := by simpa using Nat.pow_dvd_pow 3 (show k ≤ 2 by omega)
            exact ⟨changeLevel hd χ, fun n hn ↦
              (changeLevel_natCast hd χ (by simpa using Nat.Coprime.pow_right 2 hn)).symm⟩
        obtain ⟨u, hu0, hu⟩ := exists_member_nine χ₀
        refine ⟨u, hu0, fun I hI _ ↦ ?_⟩
        rw [hu I hI, hχ₀ _ (Nat.Coprime.coprime_dvd_right (by norm_num) hI)]
      · obtain ⟨hdp, χ₀, rfl⟩ := factorsThrough_prime_of_cube hp hp3 hk hχ
        have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
        have hχ₀3 : χ₀ ^ 3 = 1 := changeLevel_injective hdp (by rw [map_pow, hχ, map_one])
        obtain ⟨u, hu0, hu⟩ := exists_member_prime hχ₀3
        refine ⟨u, hu0, fun I hI hIq ↦ ?_⟩
        rw [changeLevel_natCast hdp χ₀ hIq, hu I hI (Nat.Coprime.coprime_dvd_right hdp hIq)]
  | coprime a b ha hb hab iha ihb =>
    intro χ hχ
    have : NeZero a := ⟨by omega⟩
    have : NeZero b := ⟨by omega⟩
    obtain ⟨ua, hua0, hua⟩ := iha _ (charFst_pow_three hab hχ)
    obtain ⟨ub, hub0, hub⟩ := ihb _ (charSnd_pow_three hab hχ)
    refine ⟨ua * ub, mul_ne_zero hua0 hub0, fun I hI hIab ↦ ?_⟩
    have hIa : (absNorm I).Coprime a := Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right a b) hIab
    have hIb : (absNorm I).Coprime b := Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left b a) hIab
    rw [sym6_mul_left, hua I hI hIa, hub I hI hIb]
    conv_rhs => rw [eq_changeLevel_mul hab χ]
    rw [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_natCast _ _ hIab, changeLevel_natCast _ _ hIab]

end Members

/-! ### The characters of order dividing `6` -/

section Sextic

open RealChar

/-- **The members of the real characters**: for every modulus `q ≥ 1` and every Dirichlet character `χ` mod `q`
with `χ² = 1`, there is `u ≠ 0` with `(u/𝔞)₆ = χ(N𝔞)` for every ideal `𝔞` of norm prime to `6q`: `u = 1` for
`χ = 1`, and otherwise `u = d³` with `d = ψ(−1)f` for the primitive character `ψ` mod `f` that induces `χ`
(round 477's `apply_eq_jacobiSym` and round 474's `sym6_intCast_cube`). -/
theorem exists_member_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 = 1) :
    ∃ u : 𝓞 K, u ≠ 0 ∧ ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → (absNorm I).Coprime q →
      sym6 u I = χ (absNorm I) := by
  by_cases hχ1 : χ = 1
  · refine ⟨1, one_ne_zero, fun I hI hIq ↦ ?_⟩
    rw [hχ1, sym6_one_left hI, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).2 hIq)]
  have : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
  have hψq : χ.primitiveCharacter.IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one]
    apply (changeLevel_eq_one_iff (conductor_dvd_level χ)).1
    rw [map_pow, changeLevel_primitiveCharacter, hχ2]
  have hker : ∀ u : (ZMod χ.conductor)ˣ, χ.primitiveCharacter u = 1 ↔ toInt _ hψq u = 1 := by
    intro u
    rw [← toInt_cast hψq]
    exact_mod_cast Iff.rfl
  have hψz : (toInt _ hψq).IsPrimitive :=
    (isPrimitive_iff_of_ker hker).1 (primitiveCharacter_isPrimitive χ)
  have hd : toInt _ hψq (-1) * (χ.conductor : ℤ) ≠ 0 := by
    have := NeZero.ne χ.conductor
    rcases toInt_neg_one hψq with h | h <;> rw [h] <;> simpa using this
  refine ⟨((toInt _ hψq (-1) * χ.conductor : ℤ) : 𝓞 K) ^ 3, pow_ne_zero _ (Int.cast_ne_zero.2 hd),
    fun I hI hIq ↦ ?_⟩
  rw [sym6_intCast_cube _ hI]
  conv_rhs => rw [← changeLevel_primitiveCharacter χ]
  rw [changeLevel_natCast _ _ hIq, ← toInt_cast hψq, apply_eq_jacobiSym (isQuadratic_toInt hψq) hψz
    (Nat.Coprime.coprime_dvd_right (by norm_num) hI)
    (Nat.Coprime.coprime_dvd_right (conductor_dvd_level χ) hIq)]

/-- **The members of the characters of order dividing `6`**: for every modulus `q ≥ 1` and every `χ` mod `q`
with `χ⁶ = 1`, there is `u ≠ 0` with `(u/𝔞)₆ = χ(N𝔞)` for every ideal `𝔞` of norm prime to `6q`, the product of
the members of the cubic `χ⁴` and the real `χ³`, as `χ = χ⁴χ³`. -/
theorem exists_member_six {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ6 : χ ^ 6 = 1) :
    ∃ u : 𝓞 K, u ≠ 0 ∧ ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → (absNorm I).Coprime q →
      sym6 u I = χ (absNorm I) := by
  obtain ⟨u₁, hu₁0, hu₁⟩ := exists_member_cube q (χ ^ 4)
    (by rw [← pow_mul, show 4 * 3 = 6 * 2 by norm_num, pow_mul, hχ6, one_pow])
  obtain ⟨u₂, hu₂0, hu₂⟩ := exists_member_real (χ := χ ^ 3)
    (by rw [← pow_mul, show 3 * 2 = 6 by norm_num, hχ6])
  have hχ7 : χ ^ 4 * χ ^ 3 = χ := by
    rw [← pow_add, show 4 + 3 = 6 + 1 by norm_num, pow_succ, hχ6, one_mul]
  refine ⟨u₁ * u₂, mul_ne_zero hu₁0 hu₂0, fun I hI hIq ↦ ?_⟩
  rw [sym6_mul_left, hu₁ I hI hIq, hu₂ I hI hIq, ← MulChar.mul_apply, hχ7]

end Sextic

/-! ### The half-plane -/

/-- **From a member on the norms prime to `6q` to the half-plane**: if `χ² ≠ 1` and `u ≠ 0` has `(u/𝔞)₆ = χ(N𝔞)`
for every ideal `𝔞` of norm prime to `6q`, then `L(s, χ) ≠ 0` on `Re s > 11/12`, by the bridge at the member
`q⁶u`. -/
theorem LFunction_ne_zero_of_member_coprime {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 ≠ 1)
    {u : 𝓞 K} (hu0 : u ≠ 0)
    (hu : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → (absNorm I).Coprime q → sym6 u I = χ (absNorm I))
    {s : ℂ} (hs : 11 / 12 < s.re) : LFunction χ s ≠ 0 := by
  have hq : ((q : 𝓞 K) ^ 6) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne q))
  refine LFunction_ne_zero_of_member hχ2 (mul_ne_zero hq hu0) (fun I hI ↦ ?_) hs
  rw [sym6_mul_left, sym6_natCast_pow_six q hI]
  by_cases hIq : (absNorm I).Coprime q
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hIq), one_mul, hu I hI hIq]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hIq), zero_mul,
      MulChar.map_nonunit χ (fun h ↦ hIq ((ZMod.isUnit_iff_coprime _ _).1 h))]

/-- **The half-plane `Re s > 11/12` for the characters of order dividing `6`**: for every modulus `q ≥ 1`, every
Dirichlet character `χ` mod `q` with `χ⁶ = 1` and every `s` with `Re s > 11/12`, `L(s, χ) ≠ 0`, the trivial
character excepted at `s = 1`. The real ones are round 477's. -/
theorem LFunction_ne_zero_of_pow_six {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ6 : χ ^ 6 = 1)
    {s : ℂ} (hs : 11 / 12 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : LFunction χ s ≠ 0 := by
  by_cases hχ2 : χ ^ 2 = 1
  · exact RealChar.LFunction_ne_zero_of_isQuadratic (MulChar.isQuadratic_iff_sq_eq_one.2 hχ2) hs hχs
  obtain ⟨u, hu0, hu⟩ := exists_member_six hχ6
  exact LFunction_ne_zero_of_member_coprime hχ2 hu0 hu hs

/-- **The half-plane `Re s > 11/12` for the cubic characters**: for every modulus `q ≥ 1` and every Dirichlet
character `χ` mod `q` with `χ³ = 1` and `χ ≠ 1`, `L(s, χ) ≠ 0`. -/
theorem LFunction_ne_zero_of_cube {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ3 : χ ^ 3 = 1)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 11 / 12 < s.re) : LFunction χ s ≠ 0 := by
  obtain ⟨u, hu0, hu⟩ := exists_member_cube q χ hχ3
  exact LFunction_ne_zero_of_member_coprime (sq_ne_one_of_cube hχ3 hχ) hu0 hu hs

end Eis

#print axioms Eis.sym6_natCast_pow_six
#print axioms Eis.exists_member_nine
#print axioms Eis.eq_changeLevel_mul
#print axioms Eis.pow_totient_div_eq_one
#print axioms Eis.factorsThrough_prime_of_cube
#print axioms Eis.exists_cube_of_pow
#print axioms Eis.factorsThrough_nine_of_cube
#print axioms Eis.exists_member_cube
#print axioms Eis.exists_member_real
#print axioms Eis.exists_member_six
#print axioms Eis.LFunction_ne_zero_of_member_coprime
#print axioms Eis.LFunction_ne_zero_of_pow_six
#print axioms Eis.LFunction_ne_zero_of_cube
