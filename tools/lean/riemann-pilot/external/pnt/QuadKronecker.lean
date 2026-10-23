/-
# Round 487: the Kronecker character of a quadratic field

Imports Mathlib and the pilot's `QuadIdeals`, `QuadRing` and `QuadSplit`.

Plain statement. For every number field `K` of degree `2` there is a Dirichlet character `χ` modulo `|D_K|`
(`D_K` = Mathlib's `discr K`), quadratic (values `0`, `±1`) and `≠ 1`, with `χ(p) = 1`, `−1` or `0` as the prime `p`
splits, is inert or ramifies in `K`, and `ζ_K(s) = ζ(s)L(s, χ)` for `Re s > 1` (`exists_kronecker`). For `K`
imaginary, `L(1, χ) = 2πh_K/(w_K√|D_K|)` (`classNumber_formula`).

* `jacBot`: `a ↦ J(a | m)` on `ZMod m`, a character by Mathlib's `jacobiSym.mul_left` and `jacobiSym.mod_left`. For
  `d ≡ 1 (mod 4)` the character is `jacBot |d|`: `J(p | |d|) = J(d | p)` for odd `p` by quadratic reciprocity
  (`jacobiSym_natAbs`), and `J(2 | |d|)` is `1` or `−1` as `d ≡ 1` or `5 (mod 8)` (`jacobiSym_two_natAbs`).
* `jacTop`: `a ↦ J(d | a)` for odd `a` and `0` for even `a`, on `ZMod (4|d|)`, a character since `J(d | ·)` has
  period `4|d|` on odd numbers (Mathlib's `jacobiSym.mod_right`). For `d ≡ 2, 3 (mod 4)` the character is `jacTop d`.
* `type_one`, `type_two_three`: the values at the primes are the splitting types, from `QuadSplit` and the
  Legendre symbol (`type_of_legendre`).
* `dedekindZeta_eq`: then round 485's `QuadIdeals.rA_eq` and `QuadIdeals.dedekindZeta_eq` give `ζ_K = ζ·L(·, χ)`.
* `ne_one_of_eq`: a character in such a factorization is not `1`. If it were, `(s − 1)²ζ_K(s)` would tend to
  `∏_{p∣N}(1 − 1/p) ≠ 0` as `s → 1⁺` (Mathlib's `riemannZeta_residue_one` and
  `DirichletCharacter.LFunctionTrivChar_residue_one`), but `(s − 1)ζ_K(s)` has a finite limit (Mathlib's
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`), so `(s − 1)²ζ_K(s)` tends to `0`.
-/
import Mathlib
import QuadSplit

open NumberField Filter Topology

/- As in `QuadSplit`: erased for `ring` and `simp` in `ZMod p`. -/
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace QuadKronecker

/-! ### Two Jacobi characters -/

/-- `a ↦ J(a | m)` on `ZMod m`, for `m ≥ 2`. -/
def jacBot (m : ℕ) (hm : 1 < m) : MulChar (ZMod m) ℤ where
  toFun a := jacobiSym (a.val : ℤ) m
  map_one' := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hm, Nat.cast_one]
    exact jacobiSym.one_left m
  map_mul' a b := by
    rw [ZMod.val_mul, Int.natCast_mod, ← jacobiSym.mod_left, Nat.cast_mul, jacobiSym.mul_left]
  map_nonunit' a ha := by
    have : NeZero m := ⟨by omega⟩
    have hc : ¬ (a.val).Coprime m := by
      intro hc
      apply ha
      rw [← ZMod.natCast_zmod_val a]
      exact (ZMod.isUnit_iff_coprime _ _).2 hc
    exact jacobiSym.eq_zero_iff_not_coprime.2 (by rw [Int.gcd_natCast_natCast]; exact hc)

theorem jacBot_natCast (m : ℕ) (hm : 1 < m) (n : ℕ) : jacBot m hm (n : ZMod m) = jacobiSym n m := by
  show jacobiSym ((n : ZMod m).val : ℤ) m = _
  rw [ZMod.val_natCast, Int.natCast_mod, ← jacobiSym.mod_left]

theorem jacBot_isQuadratic (m : ℕ) (hm : 1 < m) : (jacBot m hm).IsQuadratic :=
  fun _ ↦ jacobiSym.trichotomy _ _

/-- `a ↦ J(d | a)` for odd `a`, `0` for even `a`, on `ZMod (4|d|)`. -/
def jacTop (d : ℤ) (hd : d ≠ 0) : MulChar (ZMod (4 * d.natAbs)) ℤ where
  toFun a := if a.val % 2 = 1 then jacobiSym d a.val else 0
  map_one' := by
    have hd' : 0 < d.natAbs := Int.natAbs_pos.2 hd
    have h1 : (1 : ZMod (4 * d.natAbs)).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    show (if (1 : ZMod (4 * d.natAbs)).val % 2 = 1 then jacobiSym d (1 : ZMod (4 * d.natAbs)).val
      else 0) = 1
    rw [h1, ite_eq_left (by norm_num)]
    exact jacobiSym.one_right d
  map_mul' a b := by
    show (if (a * b).val % 2 = 1 then jacobiSym d (a * b).val else 0) =
      (if a.val % 2 = 1 then jacobiSym d a.val else 0) * (if b.val % 2 = 1 then jacobiSym d b.val else 0)
    rw [ZMod.val_mul]
    have hpar : a.val * b.val % (4 * d.natAbs) % 2 = a.val * b.val % 2 :=
      Nat.mod_mod_of_dvd _ (Dvd.intro (2 * d.natAbs) (by ring))
    rw [hpar]
    by_cases ha : a.val % 2 = 1 <;> by_cases hb : b.val % 2 = 1
    · have hab : a.val * b.val % 2 = 1 := by rw [Nat.mul_mod, ha, hb]
      rw [ite_eq_left hab, ite_eq_left ha, ite_eq_left hb, ← jacobiSym.mod_right d (Nat.odd_iff.2 hab)]
      exact jacobiSym.mul_right' d (by omega) (by omega)
    · have hab : ¬ a.val * b.val % 2 = 1 := by rw [Nat.mul_mod, ha]; omega
      rw [ite_eq_right hab, ite_eq_right hb, mul_zero]
    · have hab : ¬ a.val * b.val % 2 = 1 := by
        rw [Nat.mul_mod, show a.val % 2 = 0 by omega, zero_mul]; omega
      rw [ite_eq_right hab, ite_eq_right ha, zero_mul]
    · have hab : ¬ a.val * b.val % 2 = 1 := by
        rw [Nat.mul_mod, show a.val % 2 = 0 by omega, zero_mul]; omega
      rw [ite_eq_right hab, ite_eq_right ha, zero_mul]
  map_nonunit' a ha := by
    show (if a.val % 2 = 1 then jacobiSym d a.val else 0) = 0
    split_ifs with hodd
    · have : NeZero a.val := ⟨by omega⟩
      have : NeZero (4 * d.natAbs) := ⟨by have := Int.natAbs_pos.2 hd; omega⟩
      refine jacobiSym.eq_zero_iff_not_coprime.2 fun hg ↦ ha ?_
      rw [← ZMod.natCast_zmod_val a]
      refine (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.mul_right ?_ ?_)
      · have h2 : Nat.Coprime a.val 2 := by
          rw [Nat.coprime_two_right]; exact Nat.odd_iff.2 hodd
        simpa using h2.pow_right 2
      · rw [Int.gcd_eq_natAbs, Int.natAbs_natCast] at hg
        exact Nat.coprime_comm.1 hg
    · rfl

theorem jacTop_natCast (d : ℤ) (hd : d ≠ 0) (n : ℕ) :
    jacTop d hd (n : ZMod (4 * d.natAbs)) = if n % 2 = 1 then jacobiSym d n else 0 := by
  show (if (n : ZMod (4 * d.natAbs)).val % 2 = 1 then jacobiSym d (n : ZMod (4 * d.natAbs)).val
    else 0) = _
  rw [ZMod.val_natCast]
  have hpar : n % (4 * d.natAbs) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (Dvd.intro (2 * d.natAbs) (by ring))
  rw [hpar]
  split_ifs with h
  · exact (jacobiSym.mod_right d (Nat.odd_iff.2 h)).symm
  · rfl

theorem jacTop_isQuadratic (d : ℤ) (hd : d ≠ 0) : (jacTop d hd).IsQuadratic := by
  intro a
  have h : jacTop d hd a = if a.val % 2 = 1 then jacobiSym d a.val else 0 := rfl
  rw [h]
  split_ifs
  · exact jacobiSym.trichotomy _ _
  · exact Or.inl rfl

/-! ### Values at the primes -/

/-- For `d ≡ 1 (mod 4)` and an odd prime `p`, `J(p | |d|) = J(d | p)`. -/
theorem jacobiSym_natAbs {d : ℤ} (h1 : d % 4 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiSym p d.natAbs = jacobiSym d p := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨N, rfl | rfl⟩ : ∃ N : ℕ, d = N ∨ d = -N := ⟨d.natAbs, Int.natAbs_eq d⟩
  · have hN4 : N % 4 = 1 := by omega
    rw [Int.natAbs_natCast, jacobiSym.quadratic_reciprocity_one_mod_four' hpo hN4]
  · have hN4 : N % 4 = 3 := by omega
    rw [Int.natAbs_neg, Int.natAbs_natCast, jacobiSym.neg _ hpo]
    rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hpo) with hp4 | hp4
    · rw [ZMod.χ₄_nat_one_mod_four hp4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four hp4 (Nat.odd_iff.2 (by omega))]
    · rw [ZMod.χ₄_nat_three_mod_four hp4, jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN4]
      ring

/-- For `d ≡ 1 (mod 4)`, `J(2 | |d|)` is `1` if `d ≡ 1 (mod 8)` and `−1` if `d ≡ 5 (mod 8)`. -/
theorem jacobiSym_two_natAbs {d : ℤ} (h1 : d % 4 = 1) :
    jacobiSym ((2 : ℕ) : ℤ) d.natAbs = if d % 8 = 1 then 1 else -1 := by
  have hodd : Odd d.natAbs := Nat.odd_iff.2 (by omega)
  rw [Nat.cast_ofNat, jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  rw [ite_eq_right (by omega)]
  by_cases h8 : d % 8 = 1
  · rw [ite_eq_left h8, ite_eq_left (by omega)]
  · rw [ite_eq_right h8, ite_eq_right (by omega)]

/-! ### The splitting type from the Legendre symbol -/

section Legendre

variable {K : Type*} [Field K] [NumberField K]

theorem type_of_legendre {d : ℤ} {p : ℕ} [Fact p.Prime]
    (hram : (p : ℤ) ∣ d → QuadIdeals.Ramified K p)
    (hsplit : ¬ (p : ℤ) ∣ d → IsSquare (d : ZMod p) → QuadIdeals.Split K p)
    (hinert : ¬ IsSquare (d : ZMod p) → QuadIdeals.Inert K p) :
    (legendreSym p d = 1 ∧ QuadIdeals.Split K p) ∨ (legendreSym p d = -1 ∧ QuadIdeals.Inert K p) ∨
      (legendreSym p d = 0 ∧ QuadIdeals.Ramified K p) := by
  by_cases h0 : (d : ZMod p) = 0
  · exact Or.inr (Or.inr ⟨(legendreSym.eq_zero_iff p d).2 h0,
      hram ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).1 h0)⟩)
  · rcases legendreSym.eq_one_or_neg_one p h0 with h | h
    · exact Or.inl ⟨h, hsplit (fun hd ↦ h0 ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).2 hd))
        ((legendreSym.eq_one_iff p h0).1 h)⟩
    · exact Or.inr (Or.inl ⟨h, hinert ((legendreSym.eq_neg_one_iff p).1 h)⟩)

end Legendre

/-! ### From the splitting types to `ζ_K = ζ·L(·, χ)` -/

section Assemble

variable {K : Type*} [Field K] [NumberField K]

open ArithmeticFunction in
/-- The arithmetic function `n ↦ χ(n)`. -/
noncomputable def charFun {N : ℕ} (χ : MulChar (ZMod N) ℤ) : ArithmeticFunction ℤ :=
  toArithmeticFunction fun n ↦ χ (n : ZMod N)

open ArithmeticFunction in
theorem charFun_apply {N : ℕ} (χ : MulChar (ZMod N) ℤ) {n : ℕ} (hn : n ≠ 0) :
    charFun χ n = χ (n : ZMod N) := by
  simp [charFun, toArithmeticFunction, hn]

open ArithmeticFunction in
theorem charFun_zero {N : ℕ} (χ : MulChar (ZMod N) ℤ) : charFun χ 0 = 0 := by
  simp [charFun, toArithmeticFunction]

theorem charFun_mult {N : ℕ} (χ : MulChar (ZMod N) ℤ) : (charFun χ).IsMultiplicative := by
  refine ⟨by rw [charFun_apply χ one_ne_zero, Nat.cast_one, map_one], fun {m n} _ ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · rw [zero_mul, charFun_zero, zero_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [mul_zero, charFun_zero, mul_zero]
  rw [charFun_apply χ (mul_ne_zero hm hn), charFun_apply χ hm, charFun_apply χ hn, Nat.cast_mul,
    map_mul]

theorem charFun_pow {N : ℕ} (χ : MulChar (ZMod N) ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    charFun χ (p ^ k) = charFun χ p ^ k := by
  rw [charFun_apply χ (pow_ne_zero k hp.ne_zero), charFun_apply χ hp.ne_zero, Nat.cast_pow, map_pow]

/-- The complex Dirichlet character of `χ`. -/
noncomputable def toC {N : ℕ} (χ : MulChar (ZMod N) ℤ) : DirichletCharacter ℂ N :=
  χ.ringHomComp (Int.castRingHom ℂ)

theorem toC_apply {N : ℕ} (χ : MulChar (ZMod N) ℤ) (a : ZMod N) : toC χ a = (χ a : ℂ) := by
  simp [toC]

/-- **`ζ_K = ζ·L(·, χ)`** for a character `χ` whose values at the primes are the splitting types. -/
theorem dedekindZeta_eq {N : ℕ} [NeZero N] (hN : 1 < N)
    (χ : MulChar (ZMod N) ℤ)
    (htype : ∀ p : ℕ, p.Prime → (χ (p : ZMod N) = 1 ∧ QuadIdeals.Split K p) ∨
      (χ (p : ZMod N) = -1 ∧ QuadIdeals.Inert K p) ∨ (χ (p : ZMod N) = 0 ∧ QuadIdeals.Ramified K p))
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction (toC χ) s := by
  have hrA := QuadIdeals.rA_eq (K := K) (charFun_mult χ) (fun p k hp ↦ charFun_pow χ hp k)
    (fun p hp ↦ by rw [charFun_apply χ hp.ne_zero]; exact htype p hp)
  refine QuadIdeals.dedekindZeta_eq (toC χ) (c := charFun χ) (fun n ↦ ?_) hrA hs
  rcases eq_or_ne n 0 with rfl | hn
  · have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
    rw [charFun_zero, Nat.cast_zero, MulChar.map_zero, Int.cast_zero]
  · rw [toC_apply, charFun_apply χ hn]

/-- **A character in a factorization `ζ_K = ζ·L(·, χ)` is not trivial**: `ζ_K` has a simple pole at `1`
(Mathlib's class number formula), while `ζ·L(·, 1)` would have a double one (Mathlib's
`DirichletCharacter.LFunctionTrivChar_residue_one`). -/
theorem ne_one_of_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s) :
    χ ≠ 1 := by
  rintro rfl
  have hres := tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hof : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hof ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h1
    have := Complex.ofReal_injective (h1.trans Complex.ofReal_one.symm)
    exact (ne_of_gt (Set.mem_Ioi.1 hs)) this
  have hz := riemannZeta_residue_one.comp hmap
  have hL := (DirichletCharacter.LFunctionTrivChar_residue_one (N := N)).comp hmap
  have hprod := hz.mul hL
  have hres' : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
    convert hres using 2
  have hlin : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1)) (𝓝[>] 1) (𝓝 0) := by
    simpa using hof.sub_const 1
  have h0 := hlin.mul hres'
  rw [zero_mul] at h0
  have heq : (fun s : ℝ ↦ ((s : ℂ) - 1) * (((s : ℂ) - 1) * dedekindZeta K s)) =ᶠ[𝓝[>] 1]
      ((fun s : ℂ ↦ (s - 1) * riemannZeta s) ∘ (fun s : ℝ ↦ (s : ℂ))) *
        ((fun s : ℂ ↦ (s - 1) * DirichletCharacter.LFunctionTrivChar N s) ∘
          (fun s : ℝ ↦ (s : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [h s (by simpa using hs)]
    ring
  have hlim := tendsto_nhds_unique h0 (hprod.congr' heq.symm)
  rw [one_mul] at hlim
  refine (Finset.prod_ne_zero_iff.2 fun p hp ↦ ?_) hlim.symm
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  rw [sub_ne_zero]
  intro h1
  have hp1 : (p : ℂ) = 1 := by rw [← inv_inv (p : ℂ), ← h1, inv_one]
  norm_cast at hp1
  omega

end Assemble

/-! ### The Kronecker character of `ℚ(√d)` -/

section Kronecker

variable {K : Type*} [Field K] [NumberField K] {d : ℤ} {s : K}
  (hd : Squarefree d) (hd1 : d ≠ 1) (hs : s ^ 2 = d) (hK : Module.finrank ℚ K = 2)
include hd hd1 hs hK

/-- **The splitting law, `d ≡ 1 (mod 4)`**: `p` splits, is inert or ramifies as `J(p | |d|)` is
`1`, `−1` or `0`. -/
theorem type_one (h1 : d % 4 = 1) (hm : 1 < d.natAbs) {p : ℕ} (hp : p.Prime) :
    (jacBot d.natAbs hm (p : ZMod d.natAbs) = 1 ∧ QuadIdeals.Split K p) ∨
      (jacBot d.natAbs hm (p : ZMod d.natAbs) = -1 ∧ QuadIdeals.Inert K p) ∨
      (jacBot d.natAbs hm (p : ZMod d.natAbs) = 0 ∧ QuadIdeals.Ramified K p) := by
  have := Fact.mk hp
  rw [jacBot_natCast]
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [jacobiSym_two_natAbs h1]
    by_cases h8 : d % 8 = 1
    · exact Or.inl ⟨ite_eq_left h8, QuadSplit.split_two₁ hd hd1 hs hK h1 h8⟩
    · exact Or.inr (Or.inl ⟨ite_eq_right h8, QuadSplit.inert_two₁ hd hd1 hs hK h1 (by omega)⟩)
  · rw [jacobiSym_natAbs h1 hp hp2, ← jacobiSym.legendreSym.to_jacobiSym]
    exact type_of_legendre (QuadSplit.ramified_of_dvd₁ hd hd1 hs hK h1 hp2)
      (QuadSplit.split₁ hd hd1 hs hK h1 hp2) (QuadSplit.inert₁ hd hd1 hs hK h1)

/-- **The splitting law, `d ≡ 2, 3 (mod 4)`**: `p` splits, is inert or ramifies as `J(d | p)` (`p` odd)
is `1`, `−1` or `0`; `2` ramifies. -/
theorem type_two_three (h23 : d % 4 = 2 ∨ d % 4 = 3) (hd0 : d ≠ 0) {p : ℕ} (hp : p.Prime) :
    (jacTop d hd0 (p : ZMod (4 * d.natAbs)) = 1 ∧ QuadIdeals.Split K p) ∨
      (jacTop d hd0 (p : ZMod (4 * d.natAbs)) = -1 ∧ QuadIdeals.Inert K p) ∨
      (jacTop d hd0 (p : ZMod (4 * d.natAbs)) = 0 ∧ QuadIdeals.Ramified K p) := by
  have := Fact.mk hp
  rw [jacTop_natCast]
  rcases eq_or_ne p 2 with rfl | hp2
  · exact Or.inr (Or.inr ⟨ite_eq_right (by norm_num), QuadSplit.ramified_two₂ hd hd1 hs hK h23⟩)
  · rw [ite_eq_left (Nat.odd_iff.1 (hp.odd_of_ne_two hp2)), ← jacobiSym.legendreSym.to_jacobiSym]
    exact type_of_legendre (QuadSplit.ramified_of_dvd₂ hd hd1 hs hK h23)
      (QuadSplit.split₂ hd hd1 hs hK h23 hp2) (QuadSplit.inert₂ hd hd1 hs hK h23)

end Kronecker

/-! ### Every quadratic field -/

section Main

variable {K : Type*} [Field K] [NumberField K]

/-- **The Kronecker character of a quadratic field.** For every number field `K` of degree `2` there is
a quadratic Dirichlet character `χ ≠ 1` modulo `|D_K|` whose value at each prime `p` is `1`, `−1` or `0`
as `p` splits, is inert or ramifies in `K`, and `ζ_K(s) = ζ(s)L(s, χ)` for `Re s > 1`. -/
theorem exists_kronecker (hK : Module.finrank ℚ K = 2) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N),
      (N : ℤ) = |discr K| ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      (∀ p : ℕ, p.Prime → (χ p = 1 ∧ QuadIdeals.Split K p) ∨ (χ p = -1 ∧ QuadIdeals.Inert K p) ∨
        (χ p = 0 ∧ QuadIdeals.Ramified K p)) ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  obtain ⟨d, t, hd, hd1, ht⟩ := QuadRing.exists_sqrt hK
  have hd0 : d ≠ 0 := fun h ↦ not_squarefree_zero (h ▸ hd)
  have hcases : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
    have h0 : d % 4 ≠ 0 := by
      intro h
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
      have := hd 2 ⟨k, by rw [hk]; ring⟩
      exact absurd (Int.isUnit_iff.1 this) (by omega)
    omega
  -- the generic conclusion from a character with the splitting types
  have key : ∀ {N : ℕ} [NeZero N] (hN : 1 < N) (χ : MulChar (ZMod N) ℤ), (N : ℤ) = |discr K| →
      χ.IsQuadratic →
      (∀ p : ℕ, p.Prime → (χ (p : ZMod N) = 1 ∧ QuadIdeals.Split K p) ∨
        (χ (p : ZMod N) = -1 ∧ QuadIdeals.Inert K p) ∨
        (χ (p : ZMod N) = 0 ∧ QuadIdeals.Ramified K p)) →
      ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N),
        (N : ℤ) = |discr K| ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
        (∀ p : ℕ, p.Prime → (χ p = 1 ∧ QuadIdeals.Split K p) ∨ (χ p = -1 ∧ QuadIdeals.Inert K p) ∨
          (χ p = 0 ∧ QuadIdeals.Ramified K p)) ∧
        ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s := by
    intro N _ hN χ hND hq htype
    have hz := fun (s : ℂ) (hs : 1 < s.re) ↦ dedekindZeta_eq hN χ htype hs
    refine ⟨N, inferInstance, toC χ, hND, hq.comp _, ne_one_of_eq _ hz, fun p hp ↦ ?_, hz⟩
    rw [toC_apply]
    rcases htype p hp with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h]
    · exact Or.inl ⟨by norm_num, h'⟩
    · exact Or.inr (Or.inl ⟨by norm_num, h'⟩)
    · exact Or.inr (Or.inr ⟨by norm_num, h'⟩)
  rcases hcases with h1 | h23
  · have hm : 1 < d.natAbs := by omega
    have : NeZero d.natAbs := ⟨by omega⟩
    refine key hm (jacBot d.natAbs hm) ?_ (jacBot_isQuadratic _ hm)
      (fun p hp ↦ type_one hd hd1 ht hK h1 hm hp)
    rw [QuadRing.discr_θ₁ hd hd1 ht h1 hK, Int.natCast_natAbs]
  · have h23' : d % 4 = 2 ∨ d % 4 = 3 := h23
    have hm : 1 < 4 * d.natAbs := by have := Int.natAbs_pos.2 hd0; omega
    have : NeZero (4 * d.natAbs) := ⟨by omega⟩
    refine key hm (jacTop d hd0) ?_ (jacTop_isQuadratic d hd0)
      (fun p hp ↦ type_two_three hd hd1 ht hK h23' hd0 hp)
    rw [QuadRing.discr_θ₂ hd hd1 ht h23' hK, abs_mul, Nat.cast_mul, Int.natCast_natAbs]
    rfl

/-- **The class number formula for every imaginary quadratic field, with its Kronecker character**:
`L(1, χ_K) = 2πh_K/(w_K√|D_K|)`, `χ_K` a quadratic character `≠ 1` modulo `|D_K|`. -/
theorem classNumber_formula (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N),
      (N : ℤ) = |discr K| ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      DirichletCharacter.LFunction χ 1 =
        ((2 * Real.pi * classNumber K / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) : ℝ) :
          ℂ) := by
  obtain ⟨N, hN, χ, hND, hq, hχ, -, hz⟩ := exists_kronecker hK
  exact ⟨N, hN, χ, hND, hq, hχ, QuadIdeals.LFunction_one_eq_imag hK hc χ hχ hz⟩

end Main

end QuadKronecker
