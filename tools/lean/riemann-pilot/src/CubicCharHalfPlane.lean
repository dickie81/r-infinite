import HalfPlaneTwistMean
import EisensteinSupplement

/-!
# Round 489: the cubic characters of prime modulus, `L(s, χ) ≠ 0` on `Re s > 11/12` (door 5(a), part 1)

Door 5(a) of round 481, first part: the half-plane for the cubic Dirichlet characters of prime modulus, through the
family's own members.

* **The member of a cubic character** (`sym6_cubicMember`): for a primary `π` with `(π)` prime,
  `(π²π̄⁴/𝔞)₆ = σ((N𝔞/π)₃)` for every ideal `𝔞` of norm prime to `6`. At a prime `𝔮 ∤ 6` other than `(π)` and `(π̄)`,
  round 290's cubic reciprocity (`chi3_pgen_recip`) and conjugation (`chi3_map_cj`) give
  `(π²π̄⁴/𝔮)₆ = (π/𝔮)₃(π̄/𝔮)₃² = σ((q/π)₃(q̄/π)₃) = σ((N𝔮/π)₃)` with `q` the primary generator of `𝔮`
  (`chiP_cubicMember`); at `(π)` and `(π̄)` both sides vanish.
* **The bridge** (`LFunction_ne_zero_of_member`): for a Dirichlet character `χ` mod `q` with `χ² ≠ 1` and `u₀ ≠ 0`
  with `(u₀/𝔞)₆ = χ(N𝔞)` on the ideals of norm prime to `6`, `L(s, χ) ≠ 0` on `Re s > 11/12`. At level `3q`,
  `χχ₋₃ ≠ 1` because `χ` is not real, `HalfPlaneTwistMean.ne_zero_of_memberTwist` applies, and the Euler factors of
  Mathlib's `DirichletCharacter.LFunction_changeLevel` return to level `q`.
* **The character** (`cubDir`): for a prime `P ∤ 3` of norm `p`, `n ↦ σ((n/P)₃)` as a Dirichlet character mod `p`,
  through `ℤ/p ≅ 𝓞 K/P` (`redP`, `redP_bijective`); it is cubic and nontrivial (`cubDir_pow_three`,
  `cubDir_ne_one`), and its member is `π²π̄⁴` for `(π) = P` (`sym6_cubDir`).
* **The classification** (`eq_pow_of_cube`, `mod_three_eq_one_of_cube`): modulo a prime `p`, a cubic `χ ≠ 1` exists
  only for `p ≡ 1 (mod 3)`, and every cubic `χ` is `1`, `ψ` or `ψ²` for any cubic `ψ ≠ 1`, by the values at a
  generator of `(ℤ/p)ˣ` (Mathlib's `ZMod.isCyclic_units_prime`).
* **`LFunction_ne_zero_of_cube_prime`**: for every prime `p` and every Dirichlet character `χ` mod `p` with `χ³ = 1`
  and `χ ≠ 1`, `L(s, χ) ≠ 0` on `Re s > 11/12`. The prime `p ≡ 1 (mod 3)` splits (`split_of_mod_one`) into primes
  of norm `p` with primary generators (`pgen_maximal`), `χ` is `χ_π` or `χ_π²`, and their members are `π²π̄⁴` and
  `(π²π̄⁴)²`.
-/

open NumberField Ideal

namespace Eis

/-! ### The member of a cubic character -/

section Member

/-- For `ζ = 0` or `ζ³ = 1`, `cj(ζ)² = ζ`. -/
theorem cj_sq_of_cube_or_zero {ζ : 𝓞 K} (h : ζ = 0 ∨ ζ ^ 3 = 1) : cj ζ ^ 2 = ζ := by
  rcases h with rfl | h
  · simp
  · rw [cj_of_cube h]
    linear_combination ζ * h

theorem chiP_pow_of {P : Ideal (𝓞 K)} (h : P.IsMaximal ∧ (6 : 𝓞 K) ∉ P) (a : 𝓞 K) (n : ℕ) :
    chiP P (a ^ n) = chiP P a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, chiP_one h]
  | succ n ih => rw [pow_succ, chiP_mul, ih, pow_succ]

/-- **The sextic symbol of `π²π̄⁴` at a prime `Q` away from `6` is the cubic character of `π` at the norm of
`Q`.** -/
theorem chiP_cubicMember {π : 𝓞 K} (hπ : Primary π) (hP : (span {π} : Ideal (𝓞 K)).IsMaximal)
    {Q : Ideal (𝓞 K)} (hQ : Q.IsMaximal) (hQ6 : (6 : 𝓞 K) ∉ Q) :
    chiP Q (π ^ 2 * cj π ^ 4) = σO (chi3 (span {π}) (absNorm Q : 𝓞 K)) := by
  set P : Ideal (𝓞 K) := span {π} with hPdef
  have hP3 : (3 : 𝓞 K) ∉ P :=
    three_not_mem_of_primary_mem hP.ne_top hπ (Ideal.mem_span_singleton_self π)
  have hQ3 : (3 : 𝓞 K) ∉ Q := three_not_mem_of_six Q hQ6
  -- the conjugate prime
  have hPc : (span {cj π} : Ideal (𝓞 K)).IsMaximal := by
    rw [← map_cj_span]
    exact Ideal.map_isMaximal_of_equiv cj
  have hpP : ((absNorm P : ℕ) : 𝓞 K) ∈ P := by
    rw [← mul_cj_eq_absNorm]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
  by_cases h1 : π ∈ Q
  · -- `Q = P`
    have hQP : Q = P := (hP.eq_of_le hQ.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h1)).symm
    subst hQP
    rw [chiP_eq_zero_of_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ h1 2 two_pos)),
      chi3_of_mem hpP, map_zero]
  by_cases h2 : cj π ∈ Q
  · -- `Q = P̄`
    have hQP : Q = span {cj π} :=
      (hPc.eq_of_le hQ.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h2)).symm
    have hN : absNorm Q = absNorm P := by rw [hQP, absNorm_span_cj]
    rw [chiP_eq_zero_of_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h2 4 (by norm_num))),
      hN, chi3_of_mem hpP, map_zero]
  -- `Q` is neither: cubic reciprocity
  obtain ⟨hq, hqQ⟩ := pgen_maximal Q hQ3
  set q := pgen Q with hqdef
  have hPQ : P ≠ Q := fun h ↦ h1 (h ▸ Ideal.mem_span_singleton_self π)
  have hPcQ : span {cj π} ≠ Q := fun h ↦ h2 (h ▸ Ideal.mem_span_singleton_self (cj π))
  have hPc3 : (3 : 𝓞 K) ∉ (span {cj π} : Ideal (𝓞 K)) :=
    three_not_mem_of_primary_mem hPc.ne_top hπ.cj (Ideal.mem_span_singleton_self _)
  have r1 : chi3 Q π = chi3 P q := by
    have := chi3_pgen_recip (hP := hP) (hQ := hQ) hP3 hQ3 hPQ
    rwa [hPdef, pgen_eq hπ] at this
  have r2 : chi3 Q (cj π) = cj (chi3 P (cj q)) := by
    have := chi3_pgen_recip (hP := hPc) (hQ := hQ) hPc3 hQ3 hPcQ
    rw [pgen_eq hπ.cj] at this
    rw [this, ← map_cj_span, ← hqdef]
    conv_lhs => rw [← cj_cj q]
    exact chi3_map_cj (P := P) hP3 (cj q)
  have hζ : chi3 P (cj q) = 0 ∨ chi3 P (cj q) ^ 3 = 1 := by
    by_cases hm : cj q ∈ P
    · exact Or.inl (chi3_of_mem hm)
    · exact Or.inr (chi3_pow_three (hP := hP) hP3 hm)
  have hQ' : Q.IsMaximal := hQ
  rw [chiP_mul, chiP_pow_of ⟨hQ, hQ6⟩, chiP_pow_of ⟨hQ, hQ6⟩, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    chiP_sq hQ6, chiP_sq hQ6, r1, r2, ← map_pow, cj_sq_of_cube_or_zero hζ, ← map_mul, ← chi3_mul,
    mul_cj_eq_absNorm, hqQ]

/-- **The ideal form**: `(π²π̄⁴/𝔞)₆ = σ(χ_π(N𝔞))` for every ideal `𝔞` of norm prime to `6`. -/
theorem sym6_cubicMember {π : 𝓞 K} (hπ : Primary π) (hP : (span {π} : Ideal (𝓞 K)).IsMaximal)
    {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    sym6 (π ^ 2 * cj π ^ 4) I = σO (chi3 (span {π}) (absNorm I : 𝓞 K)) := by
  have hP3 : (3 : 𝓞 K) ∉ (span {π} : Ideal (𝓞 K)) :=
    three_not_mem_of_primary_mem hP.ne_top hπ (Ideal.mem_span_singleton_self π)
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    exfalso
    rw [Submodule.zero_eq_bot, absNorm_bot] at hI
    norm_num at hI
  | h₂ I hu =>
    rw [Ideal.isUnit_iff.1 hu, absNorm_top, ← Ideal.one_eq_top, sym6_one_right, Nat.cast_one,
      chi3_one (hP := hP) hP3, map_one]
  | h₃ I Q hI0 hQ ih =>
    rw [map_mul] at hI
    have hQN : (absNorm Q).Coprime 6 := Nat.Coprime.coprime_mul_right hI
    have hIN : (absNorm I).Coprime 6 := Nat.Coprime.coprime_mul_left hI
    obtain ⟨hQm, hQ6⟩ := isMaximal_and_six_not_mem hQ hQN
    have hsQ : sym6 (π ^ 2 * cj π ^ 4) Q = chiP Q (π ^ 2 * cj π ^ 4) := by
      rw [sym6, UniqueFactorizationMonoid.normalizedFactors_irreducible hQ.irreducible, normalize_eq,
        Multiset.map_singleton, Multiset.prod_singleton]
    rw [sym6_mul_right _ hQ.ne_zero hI0, map_mul, Nat.cast_mul, chi3_mul, map_mul, ih hIN, hsQ,
      chiP_cubicMember hπ hP hQm hQ6]

end Member

open DirichletCharacter HalfPlaneS0

/-! ### The bridge: a character that agrees with a member -/

section Bridge

/-- **`L(s, χ) ≠ 0` on `Re s > 11/12` for a character that agrees with a member.** For a Dirichlet character
`χ` mod `q` with `χ² ≠ 1` and `u₀ ≠ 0` with `(u₀/𝔞)₆ = χ(N𝔞)` on the ideals of norm prime to `6`. -/
theorem LFunction_ne_zero_of_member {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 ≠ 1)
    {u₀ : 𝓞 K} (hu₀0 : u₀ ≠ 0)
    (hu₀ : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u₀ I = χ (absNorm I))
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
  have hu₀' : ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 →
      sym6 u₀ I = changeLevel hqN χ (absNorm I) := by
    intro I hI
    rw [hu₀ I hI]
    by_cases hnq : (absNorm I).Coprime q
    · have hnN : IsCoprime ((absNorm I : ℕ) : ℤ) ((3 * q : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2
          (Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right (by norm_num) hI) hnq)
      have e := changeLevel_eq_cast_of_dvd' χ hqN hnN
      simp only [Int.cast_natCast] at e
      exact e.symm
    · have h1 : changeLevel hqN χ (absNorm I) = 0 := by
        apply MulChar.map_nonunit
        rw [ZMod.isUnit_iff_coprime]
        exact fun h ↦ hnq (Nat.Coprime.coprime_dvd_right hqN h)
      have h2 : χ (absNorm I) = 0 := by
        apply MulChar.map_nonunit
        rw [ZMod.isUnit_iff_coprime]
        exact hnq
      rw [h1, h2]
  have hL := (ne_zero_of_memberTwist h3 hu₀0 hu₀' hχ' hχ'3 hs).1
  rw [LFunction_changeLevel hqN χ (Or.inl hχ1)] at hL
  exact left_ne_zero_of_mul hL

end Bridge

/-! ### The cubic character of a prime of degree one, as a Dirichlet character -/

section CubicChar

/-- The residue field of a prime `P` of norm `p` has characteristic `p`. -/
theorem charP_of_absNorm (P : Ideal (𝓞 K)) [P.IsMaximal] {p : ℕ} [hp : Fact p.Prime] (hN : absNorm P = p) :
    CharP (𝓞 K ⧸ P) p := by
  rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    ← hN]
  exact Ideal.absNorm_mem P

/-- The reduction `ℤ/p → 𝓞 K/P` for a prime `P` of norm `p`. -/
noncomputable def redP (P : Ideal (𝓞 K)) [P.IsMaximal] {p : ℕ} [Fact p.Prime] (hN : absNorm P = p) :
    ZMod p →+* 𝓞 K ⧸ P :=
  haveI := charP_of_absNorm P hN
  ZMod.castHom (dvd_refl p) (𝓞 K ⧸ P)

theorem redP_bijective (P : Ideal (𝓞 K)) [P.IsMaximal] {p : ℕ} [Fact p.Prime] (hN : absNorm P = p) :
    Function.Bijective (redP P hN) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨(redP P hN).injective, ?_⟩
  rw [ZMod.card, ← absNorm_eq_card, hN]

/-- **The cubic character of `P` modulo `p = N(P)`**: `n ↦ σ((n/P)₃)`. -/
noncomputable def cubDir (P : Ideal (𝓞 K)) [P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) {p : ℕ} [Fact p.Prime]
    (hN : absNorm P = p) : DirichletCharacter ℂ p :=
  MulChar.ofUnitHom ((cubCharC P hP3).toUnitHom.comp (Units.map (redP P hN).toMonoidHom))

theorem cubDir_apply_unit (P : Ideal (𝓞 K)) [P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) {p : ℕ} [Fact p.Prime]
    (hN : absNorm P = p) (u : (ZMod p)ˣ) : cubDir P hP3 hN u = cubCharC P hP3 (redP P hN u) := by
  rw [cubDir, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom, Units.coe_map]
  rfl

theorem cubDir_natCast (P : Ideal (𝓞 K)) [P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) {p : ℕ} [Fact p.Prime]
    (hN : absNorm P = p) (n : ℕ) : cubDir P hP3 hN n = σO (chi3 P n) := by
  by_cases hu : IsUnit (n : ZMod p)
  · rw [← hu.unit_spec, cubDir_apply_unit, hu.unit_spec, map_natCast (redP P hN), cubCharC,
      MulChar.ringHomComp_apply, chi3_eq hP3, map_natCast (Ideal.Quotient.mk P)]
  · have h0 : (n : ZMod p) = 0 := by
      by_contra h
      exact hu (Ne.isUnit h)
    have hmem : (n : 𝓞 K) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← map_natCast (redP P hN), h0, map_zero]
    rw [MulChar.map_nonunit _ hu, chi3_of_mem hmem, map_zero]

theorem cubDir_ne_one (P : Ideal (𝓞 K)) [P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) {p : ℕ} [Fact p.Prime]
    (hN : absNorm P = p) : cubDir P hP3 hN ≠ 1 := by
  intro h
  apply cubCharC_ne_one P hP3
  ext a
  obtain ⟨b, hb⟩ := (redP_bijective P hN).2 (a : 𝓞 K ⧸ P)
  have hbu : IsUnit b := by
    rw [isUnit_iff_ne_zero]
    rintro rfl
    rw [map_zero] at hb
    exact a.ne_zero hb.symm
  have e := cubDir_apply_unit P hP3 hN hbu.unit
  rw [IsUnit.unit_spec, hb, h, MulChar.one_apply hbu] at e
  rw [MulChar.one_apply_coe, ← e]

theorem cubDir_pow_three (P : Ideal (𝓞 K)) [P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) {p : ℕ} [Fact p.Prime]
    (hN : absNorm P = p) : cubDir P hP3 hN ^ 3 = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, cubDir_apply_unit]
  have h := congrArg (fun χ : MulChar (𝓞 K ⧸ P) ℂ ↦ χ ((Units.map (redP P hN).toMonoidHom u : (𝓞 K ⧸ P)ˣ) :
    𝓞 K ⧸ P)) (cubCharC_pow_three P hP3)
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, Units.coe_map] at h
  exact h

/-- **The member of `χ_π`**: `(π²π̄⁴/𝔞)₆ = χ_π(N𝔞)` for every ideal `𝔞` of norm prime to `6`, where
`(π) = P`. -/
theorem sym6_cubDir (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) {p : ℕ} [Fact p.Prime]
    (hN : absNorm P = p) {π : 𝓞 K} (hπ : Primary π) (hspan : span {π} = P) {I : Ideal (𝓞 K)}
    (hI : (absNorm I).Coprime 6) : sym6 (π ^ 2 * cj π ^ 4) I = cubDir P hP3 hN (absNorm I) := by
  subst hspan
  rw [sym6_cubicMember hπ hP hI, cubDir_natCast]

end CubicChar

/-! ### The cubic characters modulo a prime -/

section Classify

variable {p : ℕ} [hp : Fact p.Prime]

/-- Two Dirichlet characters modulo a prime that agree at a generator of `(ℤ/p)ˣ` are equal. -/
theorem eq_of_apply_gen {g : (ZMod p)ˣ} (hg : ∀ u, u ∈ Subgroup.zpowers g)
    {χ₁ χ₂ : DirichletCharacter ℂ p} (h : χ₁ g = χ₂ g) : χ₁ = χ₂ := by
  ext u
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg u)
  have hu : χ₁.toUnitHom g = χ₂.toUnitHom g := Units.ext (by rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom, h])
  rw [← MulChar.coe_toUnitHom, ← MulChar.coe_toUnitHom, map_zpow, map_zpow, hu]

/-- **A cubic character modulo a prime is `1`, `ψ` or `ψ²`** for every cubic `ψ ≠ 1`. -/
theorem eq_pow_of_cube {χ ψ : DirichletCharacter ℂ p} (hχ : χ ^ 3 = 1) (hψ : ψ ^ 3 = 1) (hψ1 : ψ ≠ 1) :
    χ = 1 ∨ χ = ψ ∨ χ = ψ ^ 2 := by
  have := ZMod.isCyclic_units_prime hp.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hz : χ g ^ 3 = 1 := by rw [← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  have hw : ψ g ^ 3 = 1 := by rw [← MulChar.pow_apply_coe, hψ, MulChar.one_apply_coe]
  have hw1 : ψ g ≠ 1 := by
    intro h
    apply hψ1
    exact eq_of_apply_gen hg (by rw [h, MulChar.one_apply_coe])
  have h1w : 1 + ψ g + ψ g ^ 2 = 0 := by
    have : (ψ g - 1) * (1 + ψ g + ψ g ^ 2) = 0 := by linear_combination hw
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hw1)
  have hfac : (χ g - 1) * (χ g - ψ g) * (χ g - ψ g ^ 2) = 0 := by
    linear_combination hz + (χ g - χ g ^ 2) * h1w + (χ g - 1) * hw
  rcases mul_eq_zero.1 hfac with h | h
  · rcases mul_eq_zero.1 h with h | h
    · left
      exact eq_of_apply_gen hg (by rw [MulChar.one_apply_coe]; linear_combination h)
    · right; left
      exact eq_of_apply_gen hg (by linear_combination h)
  · right; right
    exact eq_of_apply_gen hg (by rw [MulChar.pow_apply_coe]; linear_combination h)

/-- A Dirichlet character modulo a prime `p` with `χ³ = 1` and `χ ≠ 1` has `p ≡ 1 (mod 3)`. -/
theorem mod_three_eq_one_of_cube {χ : DirichletCharacter ℂ p} (hχ : χ ^ 3 = 1) (hχ1 : χ ≠ 1) :
    p % 3 = 1 := by
  by_contra hne
  apply hχ1
  have := ZMod.isCyclic_units_prime hp.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  apply eq_of_apply_gen hg
  rw [MulChar.one_apply_coe]
  have h3 : χ g ^ 3 = 1 := by rw [← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  have hp1 : χ g ^ (p - 1) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one, map_one]
  have hcop : Nat.gcd 3 (p - 1) = 1 := by
    have h2 := hp.out.two_le
    rw [← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  have := pow_gcd_eq_one.2 ⟨h3, hp1⟩
  rwa [hcop, pow_one] at this

end Classify

/-! ### The half-plane for the cubic characters of prime modulus -/

section Prime

theorem sq_ne_one_of_cube {G : Type*} [Group G] {x : G} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : x ^ 2 ≠ 1 := by
  intro h2
  apply h1
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

/-- **The members of the cubic characters of prime modulus**: for every prime `p` and every Dirichlet character `χ`
mod `p` with `χ³ = 1` and `χ ≠ 1`, there is `u ≠ 0` with `(u/𝔞)₆ = χ(N𝔞)` for every ideal `𝔞` of norm prime to `6`,
namely `π²π̄⁴` or `(π²π̄⁴)²` for the primary generator `π` of a prime of norm `p`. -/
theorem exists_member_of_cube_prime {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (hχ3 : χ ^ 3 = 1) (hχ : χ ≠ 1) :
    ∃ u : 𝓞 K, u ≠ 0 ∧ ∀ I : Ideal (𝓞 K), (absNorm I).Coprime 6 → sym6 u I = χ (absNorm I) := by
  have h1 := mod_three_eq_one_of_cube hχ3 hχ
  obtain ⟨P, Q, -, hpf, hN, -⟩ := split_of_mod_one hp.out h1
  have hPf : P ∈ pFactors p := by rw [hpf]; exact Multiset.mem_cons_self _ _
  obtain ⟨hPp, hpP⟩ := (mem_pFactors hp.out.ne_zero).1 hPf
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, absNorm_bot] at hN
    exact hp.out.ne_zero hN.symm
  have hPm : P.IsMaximal := hPp.isMaximal hP0
  have hP3 : (3 : 𝓞 K) ∉ P := fun h3 ↦ not_coprime_mem hPm.ne_top
    ((Nat.coprime_primes Nat.prime_three hp.out).2 (by omega)) (by exact_mod_cast h3) hpP
  obtain ⟨hπ, hspan⟩ := pgen_maximal P hP3
  have hπ0 := primary_ne_zero hπ
  have hu0 : pgen P ^ 2 * cj (pgen P) ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hπ0) (pow_ne_zero _ ((map_ne_zero_iff cj cj.injective).2 hπ0))
  rcases eq_pow_of_cube hχ3 (cubDir_pow_three P hP3 hN) (cubDir_ne_one P hP3 hN) with h | h | h
  · exact absurd h hχ
  · exact ⟨_, hu0, fun I hI ↦ by rw [h]; exact sym6_cubDir P hP3 hN hπ hspan hI⟩
  · refine ⟨_, mul_ne_zero hu0 hu0, fun I hI ↦ ?_⟩
    rw [h, sym6_mul_left, sym6_cubDir P hP3 hN hπ hspan hI, MulChar.pow_apply' _ two_ne_zero, sq]

/-- **The half-plane `Re s > 11/12` for the cubic characters of prime modulus**: for every prime `p` and every
Dirichlet character `χ` mod `p` with `χ³ = 1` and `χ ≠ 1`, `L(s, χ) ≠ 0`. -/
theorem LFunction_ne_zero_of_cube_prime {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (hχ3 : χ ^ 3 = 1) (hχ : χ ≠ 1) {s : ℂ} (hs : 11 / 12 < s.re) : LFunction χ s ≠ 0 := by
  obtain ⟨u, hu0, hu⟩ := exists_member_of_cube_prime hχ3 hχ
  exact LFunction_ne_zero_of_member (sq_ne_one_of_cube hχ3 hχ) hu0 hu hs

end Prime

end Eis

#print axioms Eis.chiP_cubicMember
#print axioms Eis.sym6_cubicMember
#print axioms Eis.LFunction_ne_zero_of_member
#print axioms Eis.redP_bijective
#print axioms Eis.cubDir_natCast
#print axioms Eis.cubDir_ne_one
#print axioms Eis.cubDir_pow_three
#print axioms Eis.sym6_cubDir
#print axioms Eis.eq_pow_of_cube
#print axioms Eis.mod_three_eq_one_of_cube
#print axioms Eis.exists_member_of_cube_prime
#print axioms Eis.LFunction_ne_zero_of_cube_prime
