import KubotaConstTerm

/-! # The character sums of the constant term: `S(c)` vanishes off the cubes (round 414)

S5f-9b of round 360's plan, part 3a. Round 389's `S(c) = Σ_{d mod 3c} (c/d)₃`, over the classes of the `d`
with `(c, d)` a bottom row of `Γ_1(3)`, is zero unless `c = m³` with `δ₃ ∣ m`; there it counts the bottom
rows, `S(m³) = N(m)³·Π_{P ∣ m, 3 ∉ P}(1 − 1/N(P))`.

* **Twisting** (`cuspF`, a definition; **`cuspS_twist`**, with `cuspF_add`, `cuspF_congr`, `cuspS_eq_tsum`,
  `primary_mul_iff`, `bRow_mul_iff`, `cuspF_mul` and `isUnit_mk_of_bRow`): for a bottom row `(c, d₀)`,
  `S(c) = (c/d₀)₃·S(c)`, by the bijection `r ↦ r·d₀` of the classes modulo `3c`. So a bottom row with
  `(c/d₀)₃ ≠ 1` gives `S(c) = 0` (**`cuspS_eq_zero_of_witness`**), and so does `3 ∤ c`
  (`cuspS_eq_zero_of_not_three_dvd`); where every symbol is `1`, `S(c)` counts the bottom rows
  (`cuspS_of_trivial`).
* **Cubes, from the symbols** (**`cube_of_cub_trivial`**, with `exists_crt`, `isCoprime_of_dvd_sub_one`,
  `isCoprime_of_irreducible`, `exists_max_pow_dvd`, `cub_pow_span` and `pow_ne_one_of_cube`): a primary `n`
  with `(d/n)₃ = 1` for every `d ≡ 1 (mod 9)` prime to `n` is the cube of a primary element. The proof is by
  strong induction on the norm: at a prime `P = (π)` of `n` with multiplicity `e`, take `g` with
  `χ_P(g) ≠ 1` (round 290's `cubChar_ne_one`) and `d ≡ g (mod π)`, `d ≡ 1 (mod 9n/π^e)`; then
  `(d/n)₃ = χ_P(g)^e`, so `3 ∣ e`.
* **The symbols at `4` and `1 + 3ω`** (`primary_four`, `absNorm_span_four`, **`cub_omega_four`**,
  `cub_δ3_four`, `primary_seven_pt`, `absNorm_span_seven_pt`, **`cub_δ3_seven_pt_ne_one`**,
  `cub_δ3_seven_pt_cube` and **`unit_eq_of_cub_four`**): `(ω/4)₃ = ω²` and `(δ₃/4)₃ = 1`, so a unit `u`
  with `(u/4)₃ = 1` is `±1`; and `(δ₃/1 + 3ω)₃ ≠ 1`, since modulo the prime `1 + 3ω` of norm `7` it is
  `δ₃² = −3`, which is not `1` there.
* **The classification** (**`cube_of_trivial`**, with `exists_unit_δ3_primary`, `absNorm_span_three`,
  `absNorm_unit_δ3_mul`, `coprime_three_absNorm`, `two_le_of_three_dvd`, `bRow_of_parts` and `cub_parts`):
  if `3 ∣ c ≠ 0` and `(c/d)₃ = 1` at every bottom row `(c, d)`, then `c = m³` with `δ₃ ∣ m`. Write
  `c = u·δ₃^a·n` with `u` a unit and `n` primary (`a ≥ 2` by norms). The `d ≡ 1 (mod 9)` make `n` a cube,
  by round 290's `cub_recip` and round 362's supplementary laws; a `d ≡ 4 (mod 9)` prime to `n` gives
  `u = ±1`; a `d ≡ 1 + 3ω (mod 9)` prime to `n` gives `3 ∣ a`.
* **`S(c)` vanishes off the cubes** (**`cuspS_eq_zero_of_not_cube`**, with `cub_cube_trivial` and
  `cuspS_cube`): for `c ≠ 0` not of the form `m³` with `δ₃ ∣ m`, `S(c) = 0`. At every cube the symbols at
  the bottom rows are `1`, and `S(m³)` counts the bottom rows.
* **The count** (`primesOff3`, a definition; **`count_primary_mem`**, **`count_bRow`** and
  **`cuspS_cube_eq`**, with `card_fiber_mul`, `card_quot_eq_absNorm`, `mem_primesOff3`,
  `mem_primesOff3_of`, `bRow_iff_primary`, `sup_three_eq_top`, `three_dvd_cube` and `primesOff3_pow`): for
  `3 ∣ c ≠ 0` the classes modulo `3c` of the bottom rows number `N(c)·Π_{P ∣ c, 3 ∉ P}(1 − 1/N(P))`. The
  proof is inclusion–exclusion over the primes of `c` off `3` (round 332's `indicator_forall_not`, round
  288's `sum_powerset_inv`), with the CRT count `N(c)/N(𝔡)` of the classes that are primary and lie in
  `𝔡 ∣ (c)`. So `S(m³) = N(m)³·Π_{P ∣ m, 3 ∉ P}(1 − 1/N(P))` for `δ₃ ∣ m ≠ 0`.
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson UniqueFactorizationMonoid
open scoped ENNReal ComplexConjugate MatrixGroups Pointwise

noncomputable section

namespace Eis

/-! ### The summand of `S(c)`, and twisting -/

open Classical in
/-- The summand of `S(c)` at `d`: `(c/d)₃` if `(c, d)` is a bottom row of `Γ_1(3)`, else `0`. -/
def cuspF (c d : 𝓞 K) : ℂ := if BRow (c, d) then σO (cub c (span {d})) else 0

theorem cuspF_add (c d x : 𝓞 K) : cuspF c (d + 3 * c * x) = cuspF c d := by
  unfold cuspF
  by_cases h : BRow (c, d)
  · rw [ite_eq_left ((bRow_add_iff x).2 h), ite_eq_left h, cub_add_of_bRow h x]
  · rw [ite_eq_right (fun h' => h ((bRow_add_iff x).1 h')), ite_eq_right h]

theorem cuspF_congr {c d d' : 𝓞 K} (h : 3 * c ∣ d' - d) : cuspF c d' = cuspF c d := by
  obtain ⟨x, hx⟩ := h
  rw [show d' = d + 3 * c * x by linear_combination hx, cuspF_add]

theorem cuspS_eq_tsum (c : 𝓞 K) :
    cuspS c = ∑' r : 𝓞 K ⧸ span {3 * c}, cuspF c (repQ (3 * c) r) := rfl

theorem primary_mul_iff {a d : 𝓞 K} (ha : Primary a) : Primary (a * d) ↔ Primary d := by
  refine ⟨fun h => ?_, fun h => ha.mul h⟩
  have h1 : (3 : 𝓞 K) ∣ a * (d - 1) := by
    have := dvd_sub h ha
    rwa [show a * d - 1 - (a - 1) = a * (d - 1) by ring] at this
  exact (isCoprime_three_of_primary ha).dvd_of_dvd_mul_left h1

theorem bRow_mul_iff {c d₀ d : 𝓞 K} (h₀ : BRow (c, d₀)) : BRow (c, d₀ * d) ↔ BRow (c, d) := by
  obtain ⟨h1, h2, h3⟩ := h₀
  simp only [BRow]
  rw [IsCoprime.mul_right_iff, primary_mul_iff h3]
  tauto

theorem cuspF_mul {c d₀ : 𝓞 K} (h₀ : BRow (c, d₀)) (d : 𝓞 K) :
    cuspF c (d₀ * d) = σO (cub c (span {d₀})) * cuspF c d := by
  unfold cuspF
  by_cases h : BRow (c, d)
  · rw [ite_eq_left ((bRow_mul_iff h₀).2 h), ite_eq_left h,
      cub_mul_span c (primary_ne_zero h₀.2.2) (primary_ne_zero h.2.2), map_mul]
  · rw [ite_eq_right (fun h' => h ((bRow_mul_iff h₀).1 h')), ite_eq_right h, mul_zero]

theorem isUnit_mk_of_bRow {c d₀ : 𝓞 K} (h₀ : BRow (c, d₀)) :
    IsUnit (Ideal.Quotient.mk (span {3 * c}) d₀) := by
  have hcop : IsCoprime d₀ (3 * c) :=
    IsCoprime.mul_right (isCoprime_three_of_primary h₀.2.2).symm h₀.1.symm
  obtain ⟨u, v, huv⟩ := hcop
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ u) ?_
  rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨-v, by linear_combination huv⟩

/-- **Twisting**: for a bottom row `(c, d₀)`, `S(c) = (c/d₀)₃·S(c)`, by `r ↦ r·d₀` on the classes. -/
theorem cuspS_twist {c d₀ : 𝓞 K} (h₀ : BRow (c, d₀)) :
    cuspS c = σO (cub c (span {d₀})) * cuspS c := by
  rw [cuspS_eq_tsum]
  set u := (isUnit_mk_of_bRow h₀).unit
  have key : ∀ r : 𝓞 K ⧸ span {3 * c},
      cuspF c (repQ (3 * c) (r * u)) = σO (cub c (span {d₀})) * cuspF c (repQ (3 * c) r) := by
    intro r
    rw [← cuspF_mul h₀]
    apply cuspF_congr
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, repQ_mk, map_mul, repQ_mk,
      IsUnit.unit_spec]
    exact mul_comm _ _
  calc ∑' r : 𝓞 K ⧸ span {3 * c}, cuspF c (repQ (3 * c) r)
      = ∑' r : 𝓞 K ⧸ span {3 * c}, cuspF c (repQ (3 * c) (r * u)) :=
        ((Units.mulRight u).tsum_eq (fun r => cuspF c (repQ (3 * c) r))).symm
    _ = ∑' r : 𝓞 K ⧸ span {3 * c}, σO (cub c (span {d₀})) * cuspF c (repQ (3 * c) r) :=
        tsum_congr key
    _ = _ := tsum_mul_left

/-- A bottom row with `(c/d₀)₃ ≠ 1` makes `S(c)` vanish. -/
theorem cuspS_eq_zero_of_witness {c d₀ : 𝓞 K} (h₀ : BRow (c, d₀)) (hne : cub c (span {d₀}) ≠ 1) :
    cuspS c = 0 := by
  have h := cuspS_twist h₀
  have h1 : σO (cub c (span {d₀})) ≠ 1 := fun h' => hne (σO_injective (by
    change σO _ = σO 1; rw [h', map_one]))
  have h2 : (1 - σO (cub c (span {d₀}))) * cuspS c = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm h1))

open Classical in
/-- Where every symbol is `1`, `S(c)` counts the bottom rows modulo `3c`. -/
theorem cuspS_of_trivial {c : 𝓞 K} (h : ∀ d, BRow (c, d) → cub c (span {d}) = 1) :
    cuspS c = ∑' r : 𝓞 K ⧸ span {3 * c}, if BRow (c, repQ (3 * c) r) then (1 : ℂ) else 0 := by
  rw [cuspS_eq_tsum]
  refine tsum_congr fun r => ?_
  unfold cuspF
  by_cases hb : BRow (c, repQ (3 * c) r)
  · rw [ite_eq_left hb, ite_eq_left hb, h _ hb, map_one]
  · rw [ite_eq_right hb, ite_eq_right hb]

/-- Without a bottom row (`3 ∤ c`), `S(c) = 0`. -/
theorem cuspS_eq_zero_of_not_three_dvd {c : 𝓞 K} (h3 : ¬ (3 : 𝓞 K) ∣ c) : cuspS c = 0 := by
  rw [cuspS_eq_tsum]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  unfold cuspF
  exact ite_eq_right fun hb => h3 hb.2.1

/-! ### Decomposition, and the symbols at `4` and `1 + 3ω` -/

/-- Every `z ≠ 0` is `u·δ₃^a·n` with `u` a unit and `n` primary. -/
theorem exists_unit_δ3_primary {z : 𝓞 K} (hz : z ≠ 0) :
    ∃ (u : (𝓞 K)ˣ) (a : ℕ) (n : 𝓞 K), Primary n ∧ z = u * δ3 ^ a * n := by
  obtain ⟨ε, a, b, z', hz', -, rfl⟩ := exists_S_decomp _ z rfl hz
  refine ⟨ε * (-1) ^ b, a, (-2) ^ b * z', (primary_pow primary_neg_two b).mul hz', ?_⟩
  have h1 : ((-1 : 𝓞 K)) ^ b * (-1) ^ b = 1 := by rw [← mul_pow]; norm_num
  have h2 : ((-2 : 𝓞 K)) ^ b = (-1) ^ b * 2 ^ b := by rw [← mul_pow]; norm_num
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [h2]
  linear_combination (-((ε : 𝓞 K) * δ3 ^ a * 2 ^ b * z')) * h1

theorem absNorm_span_three : absNorm (span {(3 : 𝓞 K)}) = 9 := by
  have h := mul_cj_eq_absNorm (3 : 𝓞 K)
  rw [map_ofNat] at h
  have : ((absNorm (span {(3 : 𝓞 K)}) : ℕ) : 𝓞 K) = ((9 : ℕ) : 𝓞 K) := by rw [← h]; norm_num
  exact_mod_cast this

theorem absNorm_unit_δ3_mul (u : (𝓞 K)ˣ) (a : ℕ) (n : 𝓞 K) :
    absNorm (span {(u : 𝓞 K) * δ3 ^ a * n}) = 3 ^ a * absNorm (span {n}) := by
  rw [← span_singleton_mul_span_singleton, ← span_singleton_mul_span_singleton, map_mul, map_mul,
    ← Ideal.span_singleton_pow, map_pow, absNorm_span_δ3,
    (Ideal.span_singleton_eq_top.2 u.isUnit), Ideal.absNorm_top, one_mul]

theorem coprime_three_absNorm {n : 𝓞 K} (hn : Primary n) : Nat.Coprime 3 (absNorm (span {n})) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by have := absNorm_primary_mod hn; omega)

/-- `3 ∣ u·δ₃^a·n` with `n` primary forces `a ≥ 2`, by norms. -/
theorem two_le_of_three_dvd {u : (𝓞 K)ˣ} {a : ℕ} {n : 𝓞 K} (hn : Primary n)
    (h3 : (3 : 𝓞 K) ∣ u * δ3 ^ a * n) : 2 ≤ a := by
  have hN := Ideal.absNorm_dvd_absNorm_of_le (Ideal.span_singleton_le_span_singleton.2 h3)
  rw [absNorm_span_three, absNorm_unit_δ3_mul] at hN
  have hcop : Nat.Coprime 9 (absNorm (span {n})) := Nat.Coprime.pow_left 2 (coprime_three_absNorm hn)
  have h9 : 9 ∣ 3 ^ a := hcop.dvd_of_dvd_mul_right hN
  by_contra ha
  push Not at ha
  interval_cases a <;> norm_num at h9

theorem primary_four : Primary (4 : 𝓞 K) := ⟨1, by norm_num⟩

theorem absNorm_span_four : absNorm (span {(4 : 𝓞 K)}) = 16 := by
  rw [show (4 : 𝓞 K) = 2 * 2 by norm_num, ← span_singleton_mul_span_singleton, map_mul,
    absNorm_span_two]

theorem cub_omega_four : cub ω (span {(4 : 𝓞 K)}) = ω ^ 2 := by
  rw [cub_omega primary_four, absNorm_span_four,
    show (16 - 1) / 3 = 3 + 2 by norm_num, pow_add, ω_cube, one_mul]

theorem cub_δ3_four : cub δ3 (span {(4 : 𝓞 K)}) = 1 := by
  rw [show (4 : 𝓞 K) = (-2) * (-2) by norm_num, cub_mul_span δ3 (by norm_num) (by norm_num),
    cub_δ3_neg_two, one_mul]

theorem primary_seven_pt : Primary (1 + 3 * ω) := ⟨ω, by ring⟩

theorem absNorm_span_seven_pt : absNorm (span {1 + 3 * ω}) = 7 := by
  have h := mul_cj_eq_absNorm (1 + 3 * ω)
  rw [map_add, map_mul, map_one, map_ofNat, cj_ω] at h
  have e : (1 + 3 * ω) * (1 + 3 * ω ^ 2) = ((7 : ℕ) : 𝓞 K) := by
    push_cast; linear_combination 3 * ω_sq_add + 9 * ω_cube
  rw [e] at h
  exact_mod_cast h.symm

/-- `(δ₃/1 + 3ω)₃ ≠ 1`: it is `≡ δ₃² = −3` modulo the prime `1 + 3ω` of norm `7`, which does not divide
`4`. -/
theorem cub_δ3_seven_pt_ne_one : cub δ3 (span {1 + 3 * ω}) ≠ 1 := by
  set P : Ideal (𝓞 K) := span {1 + 3 * ω} with hPdef
  have hN : absNorm P = 7 := absNorm_span_seven_pt
  have hprime : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm
    (by rw [hN]; exact (Nat.prime_iff.1 (by norm_num : Nat.Prime 7)).irreducible)
  have hne : P ≠ ⊥ := fun h => by rw [h, Ideal.absNorm_bot] at hN; norm_num at hN
  have hmax : P.IsMaximal := hprime.isMaximal hne
  have h7 : ((7 : ℕ) : 𝓞 K) ∈ P := hN ▸ Ideal.absNorm_mem P
  have hP3 : (3 : 𝓞 K) ∉ P := fun h3 => hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ (by
      have e : (1 : 𝓞 K) = ((7 : ℕ) : 𝓞 K) - 2 * 3 := by push_cast; norm_num
      exact e ▸ P.sub_mem h7 (P.mul_mem_left 2 h3)) isUnit_one)
  have h4 : (4 : 𝓞 K) ∉ P := fun h4 => hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ (by
      have e : (1 : 𝓞 K) = 2 * 4 - ((7 : ℕ) : 𝓞 K) := by push_cast; norm_num
      exact e ▸ P.sub_mem (P.mul_mem_left 2 h4) h7) isUnit_one)
  have hδ : Ideal.Quotient.mk P δ3 ≠ 0 := fun h => hP3 (by
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    have e : (3 : 𝓞 K) = -(δ3 * δ3) := by rw [← sq, δ3_sq]; ring
    rw [e]; exact P.neg_mem (P.mul_mem_left _ h))
  rw [cub_prime, chi3_eq hP3]
  intro h1
  have hspec := (cubChar_spec P hP3 (Units.mk0 _ hδ)).1
  rw [Units.val_mk0, h1, map_one] at hspec
  have hm3 : m3 P = 2 := by
    rw [m3, ← absNorm_eq_card, hN]
  rw [hm3, ← map_pow, δ3_sq, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at hspec
  exact h4 (by
    have e : (4 : 𝓞 K) = 1 - -3 := by norm_num
    rw [e]; exact hspec)

theorem cub_δ3_seven_pt_cube : cub δ3 (span {1 + 3 * ω}) ^ 3 = 1 := cub_δ3_cube primary_seven_pt

/-- `ζ³ = 1`, `ζ ≠ 1` and `3 ∤ a` give `ζ^a ≠ 1`. -/
theorem pow_ne_one_of_cube {M : Type*} [Monoid M] {ζ : M} (h3 : ζ ^ 3 = 1) (h1 : ζ ≠ 1) {a : ℕ}
    (ha : ¬ 3 ∣ a) : ζ ^ a ≠ 1 := fun h =>
  ha (orderOf_eq_prime h3 h1 ▸ orderOf_dvd_of_pow_eq_one h)

/-- The cubic symbol of a power of the denominator. -/
theorem cub_pow_span (a : 𝓞 K) {x : 𝓞 K} (hx : x ≠ 0) (k : ℕ) :
    cub a (span {x ^ k}) = cub a (span {x}) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, cub_one_right]
  | succ k ih => rw [pow_succ, cub_mul_span a (pow_ne_zero k hx) hx, ih, pow_succ]

/-- **The Chinese remainder theorem** for coprime elements. -/
theorem exists_crt {p q : 𝓞 K} (h : IsCoprime p q) (a b : 𝓞 K) : ∃ x, p ∣ x - a ∧ q ∣ x - b := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨a * (v * q) + b * (u * p), ⟨(b - a) * u, by linear_combination a * huv⟩,
    ⟨(a - b) * v, by linear_combination b * huv⟩⟩

theorem isCoprime_of_dvd_sub_one {n d : 𝓞 K} (h : n ∣ d - 1) : IsCoprime n d := by
  obtain ⟨t, ht⟩ := h
  exact ⟨-t, 1, by linear_combination ht⟩

/-- Irreducible elements not dividing `x` are coprime to it. -/
theorem isCoprime_of_irreducible {π x : 𝓞 K} (hπ : Irreducible π) (h : ¬ π ∣ x) : IsCoprime π x :=
  (Irreducible.coprime_iff_not_dvd hπ).2 h

/-- A largest power of a non-unit dividing `n ≠ 0`. -/
theorem exists_max_pow_dvd {π n : 𝓞 K} (hπ : ¬ IsUnit π) (hπ0 : π ≠ 0) (hn : n ≠ 0) :
    ∃ e : ℕ, π ^ e ∣ n ∧ ¬ π ^ (e + 1) ∣ n := by
  classical
  have hN0 : absNorm (span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hn
  have hπN : 2 ≤ absNorm (span {π}) := by
    have h0 : absNorm (span {π}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hπ0
    have h1 : absNorm (span {π}) ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact hπ
    omega
  have hex : ∃ k : ℕ, ¬ π ^ (k + 1) ∣ n := by
    refine ⟨absNorm (span {n}), fun h => ?_⟩
    have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.span_singleton_le_span_singleton.2 h))
    rw [← Ideal.span_singleton_pow, map_pow] at hd
    have : 2 ^ (absNorm (span {n}) + 1) ≤ absNorm (span {π}) ^ (absNorm (span {n}) + 1) :=
      Nat.pow_le_pow_left hπN _
    have h2 : absNorm (span {n}) < 2 ^ (absNorm (span {n}) + 1) :=
      lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]; exact one_dvd n
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [hk]; push Not at this; exact this

/-- **Cubes, from the symbols** (by induction on the norm): a primary `n` with `(d/n)₃ = 1` for every
`d ≡ 1 (mod 9)` prime to `n` is the cube of a primary element. At a prime factor `P = (π)` of `n` with
multiplicity `e`, take `g` with `χ_P(g) ≠ 1` (round 290's `cubChar_ne_one`) and `d ≡ g (mod π)`,
`d ≡ 1 (mod 9n/π^e)`; then `(d/n)₃ = χ_P(g)^e`, so `3 ∣ e`. -/
theorem cube_of_cub_trivial : ∀ (N : ℕ) (n : 𝓞 K), absNorm (span {n}) = N → Primary n →
    (∀ d : 𝓞 K, (9 : 𝓞 K) ∣ d - 1 → IsCoprime n d → cub d (span {n}) = 1) →
    ∃ m : 𝓞 K, Primary m ∧ n = m ^ 3 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hN hn htriv
  by_cases hu : IsUnit n
  · exact ⟨1, primary_one, by rw [primary_eq_one_of_isUnit hn hu, one_pow]⟩
  obtain ⟨P, hPmax, hnP⟩ := Ideal.exists_le_maximal (span {n})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  rw [Ideal.span_singleton_le_iff_mem] at hnP
  have hP3 : (3 : 𝓞 K) ∉ P := three_not_mem_of_primary_mem hPmax.ne_top hn hnP
  obtain ⟨hπ, hπP⟩ := pgen_maximal P hP3
  set π := pgen P with hπdef
  have hπ0 : π ≠ 0 := primary_ne_zero hπ
  have hπprime : Prime π := (Ideal.span_singleton_prime hπ0).1 (hπP ▸ hPmax.isPrime)
  have hπirr : Irreducible π := hπprime.irreducible
  have hπn : π ∣ n := by rw [← Ideal.mem_span_singleton, hπP]; exact hnP
  have hn0 : n ≠ 0 := primary_ne_zero hn
  obtain ⟨e, he, he1⟩ := exists_max_pow_dvd hπprime.not_isUnit hπ0 hn0
  obtain ⟨n₁, rfl⟩ := he
  have hn₁ : Primary n₁ := (primary_mul_iff (primary_pow hπ e)).1 hn
  have hπn₁ : ¬ π ∣ n₁ := fun h => he1 (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have he0 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0; rw [pow_zero, one_mul] at hπn; exact absurd hπn hπn₁
    · exact h0
  have hcop1 : IsCoprime π (9 * n₁) :=
    ((isCoprime_nine_of_primary hπ).mul_right (isCoprime_of_irreducible hπirr hπn₁))
  have hcub : ∀ d : 𝓞 K, cub d (span {π ^ e * n₁}) =
      cub d (span {π}) ^ e * cub d (span {n₁}) := fun d => by
    rw [cub_mul_span d (pow_ne_zero e hπ0) (primary_ne_zero hn₁), cub_pow_span d hπ0]
  have hcubπ : ∀ d : 𝓞 K, cub d (span {π}) = chi3 P d := fun d => by
    rw [hπP, cub_prime]
  by_cases h3e : 3 ∣ e
  · obtain ⟨f, rfl⟩ := h3e
    -- the hypothesis passes to `n₁`
    have htriv₁ : ∀ d : 𝓞 K, (9 : 𝓞 K) ∣ d - 1 → IsCoprime n₁ d → cub d (span {n₁}) = 1 := by
      intro d hd9 hdc
      obtain ⟨d', hd'1, hd'2⟩ := exists_crt hcop1.symm d 1
      have h9' : (9 : 𝓞 K) ∣ d' - 1 := by
        have := dvd_add (dvd_trans (dvd_mul_right 9 n₁) hd'1) hd9
        rwa [show d' - d + (d - 1) = d' - 1 by ring] at this
      have hπd' : ¬ π ∣ d' := fun h => hπprime.not_isUnit (by
        have := dvd_sub h hd'2
        rw [show d' - (d' - 1) = 1 by ring] at this
        exact isUnit_of_dvd_one this)
      have hcd' : IsCoprime (π ^ (3 * f) * n₁) d' :=
        (isCoprime_of_irreducible hπirr hπd').pow_left.mul_left
          (isCoprime_of_dvd_sub hdc.symm (dvd_trans (dvd_mul_left n₁ 9) hd'1)).symm
      have := htriv d' h9' hcd'
      rw [hcub, hcubπ] at this
      have hχ : chi3 P d' = 1 := by
        rw [show d' = 1 + (d' - 1) by ring, chi3_add_mem 1 (by
          rw [← hπP, Ideal.mem_span_singleton]; exact hd'2), chi3_one hP3]
      rw [hχ, one_pow, one_mul] at this
      rw [cub_congr (dvd_trans (dvd_mul_left n₁ 9) hd'1 : n₁ ∣ d' - d) |>.symm]
      exact this
    have hlt : absNorm (span {n₁}) < N := by
      rw [← hN, ← span_singleton_mul_span_singleton, map_mul, ← Ideal.span_singleton_pow, map_pow]
      have h1 : 0 < absNorm (span {n₁}) := Nat.pos_of_ne_zero (by
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact primary_ne_zero hn₁)
      have h2 : 2 ≤ absNorm (span {π}) := by
        have h0 : absNorm (span {π}) ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hπ0
        have h1' : absNorm (span {π}) ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact hπprime.not_isUnit
        omega
      have h3 : 2 ≤ absNorm (span {π}) ^ (3 * f) :=
        le_trans h2 (Nat.le_self_pow (by omega) _)
      nlinarith
    obtain ⟨m₁, hm₁, rfl⟩ := ih _ hlt n₁ rfl hn₁ htriv₁
    exact ⟨π ^ f * m₁, (primary_pow hπ f).mul hm₁, by ring⟩
  · exfalso
    obtain ⟨x, hx⟩ := MulChar.ne_one_iff.1 (cubChar_ne_one P hP3)
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (x : 𝓞 K ⧸ P)
    have hgP : g ∉ P := fun h => x.ne_zero (by rw [← hg, Ideal.Quotient.eq_zero_iff_mem]; exact h)
    have hχg : chi3 P g ≠ 1 := by rw [chi3_eq hP3, hg]; exact hx
    obtain ⟨d, hd1, hd2⟩ := exists_crt hcop1 g 1
    have h9 : (9 : 𝓞 K) ∣ d - 1 := dvd_trans (dvd_mul_right 9 n₁) hd2
    have hπd : ¬ π ∣ d := fun h => hgP (by
      rw [← hπP, Ideal.mem_span_singleton]
      have := dvd_sub h hd1
      rwa [show d - (d - g) = g by ring] at this)
    have hcd : IsCoprime (π ^ e * n₁) d :=
      (isCoprime_of_irreducible hπirr hπd).pow_left.mul_left
        (isCoprime_of_dvd_sub_one (dvd_trans (dvd_mul_left n₁ 9) hd2))
    have := htriv d h9 hcd
    rw [hcub, hcubπ, cub_congr (dvd_trans (dvd_mul_left n₁ 9) hd2 : n₁ ∣ d - 1), cub_one hn₁,
      mul_one] at this
    have hχd : chi3 P d = chi3 P g := by
      rw [show d = g + (d - g) by ring, chi3_add_mem g (by
        rw [← hπP, Ideal.mem_span_singleton]; exact hd1)]
    rw [hχd] at this
    exact pow_ne_one_of_cube (chi3_pow_three hP3 hgP) hχg h3e this

/-- The units with `(u/4)₃ = 1` are `±1`. -/
theorem unit_eq_of_cub_four (u : (𝓞 K)ˣ) (h : cub (u : 𝓞 K) (span {(4 : 𝓞 K)}) = 1) :
    (u : 𝓞 K) = 1 ∨ (u : 𝓞 K) = -1 := by
  have hω1 : ω ≠ 1 := fun h' => by
    have := ω_sq_add
    rw [h'] at this
    norm_num at this
  have hω2 : ω ^ 2 ≠ 1 := fun h' => hω1 (by
    calc ω = ω ^ 2 * ω := by rw [h', one_mul]
      _ = 1 := by rw [← pow_succ, ω_cube])
  have hω4 : (ω ^ 2) ^ 2 ≠ 1 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ω_cube, one_mul]
    exact hω1
  rcases List.mem_cons.1 (units_mem u) with hu | hu
  · exact Or.inl (by rw [hu]; rfl)
  rcases List.mem_cons.1 hu with hu | hu
  · exact Or.inr (by rw [hu]; simp)
  rcases List.mem_cons.1 hu with hu | hu
  · rw [hu, coe_ωu, cub_omega_four] at h; exact absurd h hω2
  rcases List.mem_cons.1 hu with hu | hu
  · rw [hu, Units.val_neg, coe_ωu, cub_neg primary_four, cub_omega_four] at h; exact absurd h hω2
  rcases List.mem_cons.1 hu with hu | hu
  · rw [hu, Units.val_pow_eq_pow_val, coe_ωu, cub_pow_left primary_four, cub_omega_four] at h
    exact absurd h hω4
  rcases List.mem_cons.1 hu with hu | hu
  · rw [hu, Units.val_neg, Units.val_pow_eq_pow_val, coe_ωu, cub_neg primary_four,
      cub_pow_left primary_four, cub_omega_four] at h
    exact absurd h hω4
  simp at hu

theorem bRow_of_parts {u : (𝓞 K)ˣ} {a : ℕ} {n d : 𝓞 K} (h3 : (3 : 𝓞 K) ∣ u * δ3 ^ a * n)
    (hd : Primary d) (hnd : IsCoprime n d) : BRow (u * δ3 ^ a * n, d) :=
  ⟨((isCoprime_unit_right d u).symm.mul_left (isCoprime_δ3 hd).pow_left).mul_left hnd, h3, hd⟩

theorem cub_parts (u : (𝓞 K)ˣ) (a : ℕ) (n : 𝓞 K) {d : 𝓞 K} (hd : Primary d) :
    cub ((u : 𝓞 K) * δ3 ^ a * n) (span {d}) =
      cub (u : 𝓞 K) (span {d}) * cub δ3 (span {d}) ^ a * cub n (span {d}) := by
  rw [cub_mul_left, cub_mul_left, cub_pow_left hd]

/-- **The classification**: if `3 ∣ c ≠ 0` and every symbol `(c/d)₃` at a bottom row is `1`, then
`c = m³` with `δ₃ ∣ m`. With `c = u·δ₃^a·n`: the witnesses `d ≡ 1 (mod 9)` make `n` a cube; then
`d ≡ 4 (mod 9)` gives `(u/4)₃ = 1`, so `u = ±1`, and `d ≡ 1 + 3ω (mod 9)` gives `3 ∣ a`. -/
theorem cube_of_trivial {c : 𝓞 K} (hc : c ≠ 0) (h3 : (3 : 𝓞 K) ∣ c)
    (htriv : ∀ d, BRow (c, d) → cub c (span {d}) = 1) : ∃ m : 𝓞 K, δ3 ∣ m ∧ c = m ^ 3 := by
  obtain ⟨u, a, n, hn, rfl⟩ := exists_unit_δ3_primary hc
  have ha2 := two_le_of_three_dvd hn h3
  -- `n` is a cube
  obtain ⟨m, hm, rfl⟩ := cube_of_cub_trivial _ n rfl hn (by
    intro d hd9 hnd
    have hd := primary_of_nine hd9
    have := htriv d (bRow_of_parts h3 hd hnd)
    rw [cub_parts u a n hd, cub_unit_of_nine u hd9, cub_δ3_of_nine hd9, one_pow, one_mul,
      one_mul] at this
    rw [← cub_recip hn hd hnd]; exact this)
  have hm3d : ∀ d : 𝓞 K, Primary d → IsCoprime (m ^ 3) d → cub (m ^ 3) (span {d}) = 1 :=
    fun d hd hcd => by
      rw [cub_pow_left hd, cub_pow_three hd (hcd.of_isCoprime_of_dvd_left (dvd_pow_self m (by norm_num)))]
  have hcop9 : IsCoprime (9 : 𝓞 K) (m ^ 3) := (isCoprime_nine_of_primary (primary_pow hm 3)).symm
  -- `u = ±1`
  obtain ⟨d, hd4, hd1⟩ := exists_crt hcop9 4 1
  have hd : Primary d := by
    have := dvd_add (dvd_trans (⟨3, by norm_num⟩ : (3 : 𝓞 K) ∣ 9) hd4) (primary_four)
    rwa [show d - 4 + (4 - 1) = d - 1 by ring] at this
  have hu := htriv d (bRow_of_parts h3 hd (isCoprime_of_dvd_sub_one hd1))
  rw [cub_parts u a _ hd, hm3d d hd (isCoprime_of_dvd_sub_one hd1), mul_one,
    cub_δ3_congr hd primary_four hd4, cub_δ3_four, one_pow, mul_one,
    cub_unit_congr u hd primary_four (cub_omega_congr hd primary_four hd4)] at hu
  have hu' := unit_eq_of_cub_four u hu
  -- `3 ∣ a`
  obtain ⟨d', hd'7, hd'1⟩ := exists_crt hcop9 (1 + 3 * ω) 1
  have hd' : Primary d' := by
    have := dvd_add (dvd_trans (⟨3, by norm_num⟩ : (3 : 𝓞 K) ∣ 9) hd'7) primary_seven_pt
    rwa [show d' - (1 + 3 * ω) + (1 + 3 * ω - 1) = d' - 1 by ring] at this
  have ha := htriv d' (bRow_of_parts h3 hd' (isCoprime_of_dvd_sub_one hd'1))
  rw [cub_parts u a _ hd', hm3d d' hd' (isCoprime_of_dvd_sub_one hd'1), mul_one,
    cub_δ3_congr hd' primary_seven_pt hd'7] at ha
  have hu1 : cub (u : 𝓞 K) (span {d'}) = 1 := by
    rcases hu' with h | h
    · rw [h, cub_one hd']
    · rw [h, cub_neg hd', cub_one hd']
  rw [hu1, one_mul] at ha
  have h3a : 3 ∣ a := by
    by_contra h3a
    exact pow_ne_one_of_cube cub_δ3_seven_pt_cube cub_δ3_seven_pt_ne_one h3a ha
  obtain ⟨k, rfl⟩ := h3a
  have hk : 1 ≤ k := by omega
  refine ⟨(u : 𝓞 K) * δ3 ^ k * m, ⟨(u : 𝓞 K) * δ3 ^ (k - 1) * m, ?_⟩, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  · have hu3 : ((u : 𝓞 K)) ^ 3 = u := by rcases hu' with h | h <;> rw [h] <;> norm_num
    calc (u : 𝓞 K) * δ3 ^ (3 * k) * m ^ 3 = (u : 𝓞 K) ^ 3 * (δ3 ^ k) ^ 3 * m ^ 3 := by
          rw [hu3, ← pow_mul, mul_comm k 3]
      _ = ((u : 𝓞 K) * δ3 ^ k * m) ^ 3 := by ring

/-- At a cube `m³` (`δ₃ ∣ m` or not), every symbol at a bottom row is `1`. -/
theorem cub_cube_trivial {m d : 𝓞 K} (hd : BRow (m ^ 3, d)) : cub (m ^ 3) (span {d}) = 1 := by
  rw [cub_pow_left hd.2.2, cub_pow_three hd.2.2
    (hd.1.of_isCoprime_of_dvd_left (dvd_pow_self m (by norm_num)))]

/-- **`S(c)` vanishes off the cubes**: for `c ≠ 0` not of the form `m³` with `δ₃ ∣ m`, `S(c) = 0`. -/
theorem cuspS_eq_zero_of_not_cube {c : 𝓞 K} (hc : c ≠ 0) (h : ¬ ∃ m : 𝓞 K, δ3 ∣ m ∧ c = m ^ 3) :
    cuspS c = 0 := by
  by_cases h3 : (3 : 𝓞 K) ∣ c
  · by_contra hS
    exact h (cube_of_trivial hc h3 fun d hd => by
      by_contra hne
      exact hS (cuspS_eq_zero_of_witness hd hne))
  · exact cuspS_eq_zero_of_not_three_dvd h3

open Classical in
/-- **At the cubes, `S(c)` counts the bottom rows modulo `3c`.** -/
theorem cuspS_cube (m : 𝓞 K) :
    cuspS (m ^ 3) = ∑' r : 𝓞 K ⧸ span {3 * m ^ 3},
      if BRow (m ^ 3, repQ (3 * m ^ 3) r) then (1 : ℂ) else 0 :=
  cuspS_of_trivial fun _ hd => cub_cube_trivial hd

/-! ### The count at the cubes -/

/-- The fibres of a surjective homomorphism of finite additive groups have `#G/#H` elements. -/
theorem card_fiber_mul {G H : Type*} [AddGroup G] [Fintype G] [AddGroup H] [Fintype H]
    [DecidableEq H] (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (Finset.univ.filter fun g => f g = y).card * Fintype.card H = Fintype.card G := by
  have h1 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset G))
    (t := (Finset.univ : Finset H)) (f := f) (fun g _ => Finset.mem_univ (f g))
  rw [Finset.card_univ] at h1
  rw [h1, Finset.sum_congr rfl fun z _ => AddMonoidHom.card_fiber_eq_of_mem_range f (hf z) (hf y),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

theorem card_quot_eq_absNorm (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
    Fintype.card (𝓞 K ⧸ I) = absNorm I := by
  rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]

open Classical in
/-- **Classes in a residue class** (CRT): for `𝔡 ∣ (c)` prime to `3`, the classes modulo `3c` whose
representative is primary and lies in `𝔡` number `N(c)/N(𝔡)`. -/
theorem count_primary_mem {c : 𝓞 K} (hc : c ≠ 0) {D : Ideal (𝓞 K)} (hDc : D ∣ span {c})
    (hD3 : D ⊔ span {(3 : 𝓞 K)} = ⊤) :
    (∑' r : 𝓞 K ⧸ span {3 * c},
      if Primary (repQ (3 * c) r) ∧ repQ (3 * c) r ∈ D then (1 : ℂ) else 0) * absNorm D =
      absNorm (span {c}) := by
  obtain ⟨e, he, t, ht, het⟩ :=
    Submodule.mem_sup.1 (hD3 ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ D ⊔ span {3})
  obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton.1 ht
  set B : Ideal (𝓞 K) := span {(3 : 𝓞 K)} * D with hB
  have hBinf : B = span {(3 : 𝓞 K)} ⊓ D := Ideal.mul_eq_inf_of_coprime (by rwa [sup_comm])
  have hcD : c ∈ D := by rw [← Ideal.span_singleton_le_iff_mem]; exact Ideal.le_of_dvd hDc
  have hAB : span {3 * c} ≤ B := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self 3) hcD
  have hcond : ∀ x : 𝓞 K, (Primary x ∧ x ∈ D) ↔
      Ideal.Quotient.mk B x = Ideal.Quotient.mk B e := by
    intro x
    rw [Ideal.Quotient.eq, hBinf, Submodule.mem_inf, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨⟨k, hk⟩, hxD⟩
      exact ⟨⟨k + t', by linear_combination hk - het⟩, D.sub_mem hxD he⟩
    · rintro ⟨⟨j, hj⟩, hD⟩
      refine ⟨⟨j - t', by linear_combination hj + het⟩, ?_⟩
      have := D.add_mem hD he
      rwa [sub_add_cancel] at this
  have hfin := finite_quot_three_mul hc
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * c})
  have hB0 : B ≠ ⊥ := fun h => by
    have := hAB (Ideal.mem_span_singleton_self (3 * c))
    rw [h, Ideal.mem_bot] at this
    exact three_mul_ne_zero hc this
  have : Finite (𝓞 K ⧸ B) := Ideal.finiteQuotientOfFreeOfNeBot _ hB0
  let := Fintype.ofFinite (𝓞 K ⧸ B)
  have key : (Finset.univ.filter fun r : 𝓞 K ⧸ span {3 * c} =>
      Primary (repQ (3 * c) r) ∧ repQ (3 * c) r ∈ D) =
      Finset.univ.filter fun r => Ideal.Quotient.factor hAB r = Ideal.Quotient.mk B e := by
    refine Finset.filter_congr fun r _ => ?_
    rw [hcond, ← Ideal.Quotient.factor_mk hAB (repQ (3 * c) r), repQ_mk]
  have hfib := card_fiber_mul (Ideal.Quotient.factor hAB).toAddMonoidHom
    (Ideal.Quotient.factor_surjective hAB) (Ideal.Quotient.mk B e)
  have hNB : absNorm B = 9 * absNorm D := by rw [hB, map_mul, absNorm_span_three]
  have hNA : absNorm (span {3 * c}) = 9 * absNorm (span {c}) := by
    rw [← span_singleton_mul_span_singleton, map_mul, absNorm_span_three]
  rw [card_quot_eq_absNorm, card_quot_eq_absNorm, hNB, hNA] at hfib
  have hN : (Finset.univ.filter fun r => Ideal.Quotient.factor hAB r = Ideal.Quotient.mk B e).card *
      absNorm D = absNorm (span {c}) := by
    have hfib' : (Finset.univ.filter fun r => Ideal.Quotient.factor hAB r =
        Ideal.Quotient.mk B e).card * (9 * absNorm D) = 9 * absNorm (span {c}) := hfib
    have h9 : 9 * ((Finset.univ.filter fun r => Ideal.Quotient.factor hAB r =
        Ideal.Quotient.mk B e).card * absNorm D) = 9 * absNorm (span {c}) := by
      rw [← hfib']; ring
    omega
  rw [tsum_fintype, Finset.sum_boole, key]
  exact_mod_cast hN

open Classical in
/-- The primes of `I` not over `3`. -/
def primesOff3 (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  (normalizedFactors I).toFinset.filter fun P => (3 : 𝓞 K) ∉ P

open Classical in
theorem mem_primesOff3 {c : 𝓞 K} (hc : c ≠ 0) {P : Ideal (𝓞 K)} (hP : P ∈ primesOff3 (span {c})) :
    P.IsMaximal ∧ c ∈ P ∧ (3 : 𝓞 K) ∉ P := by
  rw [primesOff3, Finset.mem_filter, Multiset.mem_toFinset] at hP
  have hbot : span {c} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨hPp, hle⟩ := (Ideal.mem_normalizedFactors_iff hbot).1 hP.1
  have hcP : c ∈ P := hle (Ideal.mem_span_singleton_self c)
  have hP0 : P ≠ ⊥ := fun h => hc (by rw [h] at hcP; exact Ideal.mem_bot.1 hcP)
  exact ⟨hPp.isMaximal hP0, hcP, hP.2⟩

open Classical in
theorem mem_primesOff3_of {c : 𝓞 K} (hc : c ≠ 0) {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hcP : c ∈ P)
    (h3 : (3 : 𝓞 K) ∉ P) : P ∈ primesOff3 (span {c}) := by
  rw [primesOff3, Finset.mem_filter, Multiset.mem_toFinset]
  have hbot : span {c} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  exact ⟨(Ideal.mem_normalizedFactors_iff hbot).2 ⟨hP, by rwa [Ideal.span_singleton_le_iff_mem]⟩, h3⟩

/-- For `3 ∣ c ≠ 0`: `(c, d)` is a bottom row iff `d` is primary and lies in no prime of `c` off `3`. -/
theorem bRow_iff_primary {c d : 𝓞 K} (hc : c ≠ 0) (h3 : (3 : 𝓞 K) ∣ c) :
    BRow (c, d) ↔ Primary d ∧ ∀ P ∈ primesOff3 (span {c}), d ∉ P := by
  constructor
  · rintro ⟨hcd, -, hd⟩
    refine ⟨hd, fun P hP hdP => ?_⟩
    obtain ⟨hPmax, hcP, -⟩ := mem_primesOff3 hc hP
    obtain ⟨u, v, huv⟩ := hcd
    exact hPmax.ne_top (P.eq_top_of_isUnit_mem
      (huv ▸ P.add_mem (P.mul_mem_left u hcP) (P.mul_mem_left v hdP)) isUnit_one)
  · rintro ⟨hd, hS⟩
    refine ⟨?_, h3, hd⟩
    by_contra hcd
    have hsup : span {c} ⊔ span {d} ≠ ⊤ := fun h =>
      hcd ((Ideal.isCoprime_span_singleton_iff c d).1 (Ideal.isCoprime_iff_sup_eq.2 h))
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hsup
    have hcP : c ∈ P := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))
    have hdP : d ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self d))
    by_cases h3P : (3 : 𝓞 K) ∈ P
    · obtain ⟨k, hk⟩ := hd
      have h1 : (1 : 𝓞 K) ∈ P := by
        rw [show (1 : 𝓞 K) = d - 3 * k by linear_combination (-1 : 𝓞 K) * hk]
        exact P.sub_mem hdP (P.mul_mem_right k h3P)
      exact hPmax.ne_top (P.eq_top_of_isUnit_mem h1 isUnit_one)
    · exact hS P (mem_primesOff3_of hc hPmax.isPrime hcP h3P) hdP

theorem sup_three_eq_top {T : Finset (Ideal (𝓞 K))}
    (hT : ∀ P ∈ T, P.IsMaximal ∧ (3 : 𝓞 K) ∉ P) : (∏ P ∈ T, P) ⊔ span {(3 : 𝓞 K)} = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq]
  refine IsCoprime.prod_left fun P hP => Ideal.isCoprime_iff_sup_eq.2 ?_
  obtain ⟨y, i, hi, hyi⟩ := (hT P hP).1.exists_inv (hT P hP).2
  rw [Ideal.eq_top_iff_one, ← hyi, add_comm]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hi)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ y (Ideal.mem_span_singleton_self 3)))

open Classical in
/-- **The count of bottom rows**: for `3 ∣ c ≠ 0`, the classes `d` modulo `3c` with `(c, d)` a bottom
row number `N(c)·Π_{P ∣ c, 3 ∉ P}(1 − 1/N(P))`, by inclusion–exclusion over the primes of `c` off `3`
(round 332's `indicator_forall_not`) and the CRT count `count_primary_mem`. -/
theorem count_bRow {c : 𝓞 K} (hc : c ≠ 0) (h3 : (3 : 𝓞 K) ∣ c) :
    (∑' r : 𝓞 K ⧸ span {3 * c}, if BRow (c, repQ (3 * c) r) then (1 : ℂ) else 0) =
      absNorm (span {c}) * ∏ P ∈ primesOff3 (span {c}), (1 - 1 / (absNorm P : ℂ)) := by
  have hfin := finite_quot_three_mul hc
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * c})
  set S := primesOff3 (span {c}) with hSdef
  have hSP : ∀ P ∈ S, P.IsMaximal ∧ c ∈ P ∧ (3 : 𝓞 K) ∉ P := fun P hP => mem_primesOff3 hc hP
  have hind : ∀ d : 𝓞 K, (if BRow (c, d) then (1 : ℂ) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        (if Primary d ∧ d ∈ ∏ P ∈ T, P then 1 else 0) := by
    intro d
    have e1 : (if BRow (c, d) then (1 : ℂ) else 0) =
        (if Primary d then (1 : ℂ) else 0) * (if ∀ P ∈ S, ¬ d ∈ P then 1 else 0) := by
      rw [ite_zero_mul_ite_zero, one_mul]
      exact if_congr (bRow_iff_primary hc h3) rfl rfl
    rw [e1, indicator_forall_not S (fun P => d ∈ P), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTmax : ∀ P ∈ T, P.IsMaximal := fun P hP => (hSP P (Finset.mem_powerset.1 hT hP)).1
    have hmem : (d ∈ ∏ P ∈ T, P) ↔ ∀ P ∈ T, d ∈ P := by
      rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, prod_dvd_iff hTmax]
      exact forall₂_congr fun P _ => by rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    rw [mul_left_comm, ite_zero_mul_ite_zero, one_mul]
    exact congrArg _ (if_congr (and_congr_right fun _ => hmem.symm) rfl rfl)
  have hcount : ∀ T ∈ S.powerset, (∑' r : 𝓞 K ⧸ span {3 * c},
      if Primary (repQ (3 * c) r) ∧ repQ (3 * c) r ∈ ∏ P ∈ T, P then (1 : ℂ) else 0) =
      absNorm (span {c}) / ∏ P ∈ T, (absNorm P : ℂ) := by
    intro T hT
    have hTP : ∀ P ∈ T, P.IsMaximal ∧ c ∈ P ∧ (3 : 𝓞 K) ∉ P :=
      fun P hP => hSP P (Finset.mem_powerset.1 hT hP)
    have hDc : (∏ P ∈ T, P) ∣ span {c} := (prod_dvd_iff (fun P hP => (hTP P hP).1) _).2
      fun P hP => by rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact (hTP P hP).2.1
    have hD3 := sup_three_eq_top (T := T) fun P hP => ⟨(hTP P hP).1, (hTP P hP).2.2⟩
    have h := count_primary_mem hc hDc hD3
    have hN0 : (∏ P ∈ T, (absNorm P : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P hP => by
      have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField (hTP P hP).1
        (RingOfIntegers.not_isField K)
      exact_mod_cast fun h0 => hP0 (Ideal.absNorm_eq_zero_iff.1 h0)
    rw [map_prod, Nat.cast_prod] at h
    rw [eq_div_iff hN0, h]
  calc (∑' r : 𝓞 K ⧸ span {3 * c}, if BRow (c, repQ (3 * c) r) then (1 : ℂ) else 0)
      = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * ∑' r : 𝓞 K ⧸ span {3 * c},
          (if Primary (repQ (3 * c) r) ∧ repQ (3 * c) r ∈ ∏ P ∈ T, P then 1 else 0) := by
        simp_rw [hind, tsum_fintype]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun T _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (absNorm (span {c}) / ∏ P ∈ T, (absNorm P : ℂ)) :=
        Finset.sum_congr rfl fun T hT => by rw [hcount T hT]
    _ = absNorm (span {c}) * ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card / ∏ P ∈ T, (absNorm P : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun T _ => by ring
    _ = _ := by
        congr 1
        have h := congrArg (fun x : ℝ => (x : ℂ)) (sum_powerset_inv S)
        push_cast at h
        exact h

theorem three_dvd_cube {m : 𝓞 K} (hδ : δ3 ∣ m) : (3 : 𝓞 K) ∣ m ^ 3 := by
  obtain ⟨k, rfl⟩ := hδ
  exact ⟨-(δ3 * k ^ 3), by linear_combination (δ3 * k ^ 3) * δ3_sq⟩

theorem primesOff3_pow (I : Ideal (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : primesOff3 (I ^ n) = primesOff3 I := by
  classical
  rw [primesOff3, primesOff3, normalizedFactors_pow, Multiset.toFinset_nsmul _ _ hn]

/-- **The value at the cubes**: for `δ₃ ∣ m ≠ 0`, `S(m³) = N(m)³·Π_{P ∣ m, 3 ∉ P}(1 − 1/N(P))`. -/
theorem cuspS_cube_eq {m : 𝓞 K} (hm : m ≠ 0) (hδ : δ3 ∣ m) :
    cuspS (m ^ 3) =
      (absNorm (span {m}) : ℂ) ^ 3 * ∏ P ∈ primesOff3 (span {m}), (1 - 1 / (absNorm P : ℂ)) := by
  rw [cuspS_cube, count_bRow (pow_ne_zero 3 hm) (three_dvd_cube hδ), ← Ideal.span_singleton_pow,
    primesOff3_pow _ (by norm_num), map_pow, Nat.cast_pow]

end Eis

end

#print axioms Eis.cuspF_add
#print axioms Eis.cuspF_congr
#print axioms Eis.cuspS_eq_tsum
#print axioms Eis.primary_mul_iff
#print axioms Eis.bRow_mul_iff
#print axioms Eis.cuspF_mul
#print axioms Eis.isUnit_mk_of_bRow
#print axioms Eis.cuspS_twist
#print axioms Eis.cuspS_eq_zero_of_witness
#print axioms Eis.cuspS_of_trivial
#print axioms Eis.cuspS_eq_zero_of_not_three_dvd
#print axioms Eis.exists_unit_δ3_primary
#print axioms Eis.absNorm_span_three
#print axioms Eis.absNorm_unit_δ3_mul
#print axioms Eis.coprime_three_absNorm
#print axioms Eis.two_le_of_three_dvd
#print axioms Eis.primary_four
#print axioms Eis.absNorm_span_four
#print axioms Eis.cub_omega_four
#print axioms Eis.cub_δ3_four
#print axioms Eis.primary_seven_pt
#print axioms Eis.absNorm_span_seven_pt
#print axioms Eis.cub_δ3_seven_pt_ne_one
#print axioms Eis.cub_δ3_seven_pt_cube
#print axioms Eis.pow_ne_one_of_cube
#print axioms Eis.cub_pow_span
#print axioms Eis.exists_crt
#print axioms Eis.isCoprime_of_dvd_sub_one
#print axioms Eis.isCoprime_of_irreducible
#print axioms Eis.exists_max_pow_dvd
#print axioms Eis.cube_of_cub_trivial
#print axioms Eis.unit_eq_of_cub_four
#print axioms Eis.bRow_of_parts
#print axioms Eis.cub_parts
#print axioms Eis.cube_of_trivial
#print axioms Eis.cub_cube_trivial
#print axioms Eis.cuspS_eq_zero_of_not_cube
#print axioms Eis.cuspS_cube
#print axioms Eis.card_fiber_mul
#print axioms Eis.card_quot_eq_absNorm
#print axioms Eis.count_primary_mem
#print axioms Eis.mem_primesOff3
#print axioms Eis.mem_primesOff3_of
#print axioms Eis.bRow_iff_primary
#print axioms Eis.sup_three_eq_top
#print axioms Eis.count_bRow
#print axioms Eis.three_dvd_cube
#print axioms Eis.primesOff3_pow
#print axioms Eis.cuspS_cube_eq
