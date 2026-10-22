/-
# Round 672: their Lemma 10.7, the fourth moment of `R` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Lemma 10.7: "For any M ≥ 1, we have Σ_{n₁,n₂∼M, (n₁n₂,q)=1} |R(n₁/n₂, n₁n₂^{−1})|⁴ ⪅ E(W)M² + |W|⁴M +
E(W)^{3/4}|W|(qT)^{1/2}M." (text layer lines 4814–4825; spaces restored; the sum, fraction, large bars, which the text
layer encodes as four form feeds each, large parentheses, subscripts and exponents transcribed). Their proof: "We define
the set U_{B,q₁} := {(u,χ) : #{(t₁,χ₁),(t₂,χ₂) ∈ W : ⌊t₁−t₂⌋ = u, χ₁χ̄₂ = χ} ∼ B, cond(χ) = q₁}, where cond(χ) is the
conductor of χ." (lines 4826–4828; spaces restored, the subscripts transcribed; the bar over `χ₂`, which the text layer
drops, is a rule at y = 354.2 spanning x = 381.6–388.9, over the `χ` at x = 381.6–388.9 in the row y = 345.1 of PDF
page 42, `scratchpad/r672/p42_all.txt`). They sum over the classes "by the Cauchy-Schwarz inequality and the divisor
bound" (line 4829), then "Expanding the square" (line 4901), pass to "U*_{B,q₁} := {(u,χ*) : χ* is primitive,
(u,χ₀χ*) ∈ U_{B,q₁}}" (lines 4955–4956; spaces restored, the subscripts and superscripts transcribed), and "with Lemma
10.4, we replace the supremum with an integral and then apply Theorem 10.1" (lines 4957–4958). Their last step:
"Notice that B|U*_{B,q₁}| ≤ |W|² and B²|U*_{B,q₁}| ≤ E(W)." (lines 4986–4988; spaces restored, the subscripts,
superscripts and exponents transcribed).

The stack's form.
* `R₂(n₁, n₂) = Σ_iχ_i(n₁)χ̄_i(n₂)e^{it_i(log n₁ − log n₂)}` (round 669) is their `R(n₁/n₂, n₁n₂⁻¹)` for
  `(n₁n₂, q) = 1` and `0` otherwise, so the sum over all `n₁, n₂ ∼ M` is theirs. Its square is
  `|R₂(n₁, n₂)|² = Σ_{p∈R×R}F_p(n₁)F̄_p(n₂)`, with `F_{(i,j)} = a_iā_j` and `a_i(n) = χ_i(n)e^{it_i log n}`.
* A pair `(i, j)` has the key `(⌊t_i − t_j⌋, χ_iχ_j⁻¹)` (`key`), and the pairs with one key form its class (`cls`):
  their `(u, χ)`. The keys are grouped by the conductor `q₁` of their character and by `⌊log₂|cls|⌋` (`grp`), so a
  group's classes have from `2^{g₂}` to fewer than `2·2^{g₂}` pairs, in place of their `∼ B` (`B < # ≤ 2B`) with
  `B = 2^{g₂}`. There are at most
  `d(q)(⌊log₂|R|²⌋ + 1)` groups (`card_grps_le`), and Cauchy–Schwarz over them is their first step, with the count
  explicit.
* In one group, the Gram expansion `Σ_{n₁,n₂}|Σ_pF_p(n₁)F̄_p(n₂)|² = Σ_{p,p′}|Σ_nF_p(n)F̄_{p′}(n)|²` (`sum_sq_gram`)
  is their expansion of the square. Each inner sum is `D_c(t_i − t_j − (t_k − t_l))` with `c(n) = κ(n)κ̄′(n)` for the
  keys' characters (`F_mul_conj`), and its frequency is within `1` of `⌊t_i − t_j⌋ − ⌊t_k − t_l⌋`, so round 669's
  `norm_sq_Dp_le_shift`, their Lemma 10.4, bounds its square by `J(κ, κ′) = ∫κ(ξ)|D_c(u − u′ + πξ)|² dξ`
  (`inner_le`).
* For each `ξ`, the keys' characters, all of conductor `q₁`, are induced from primitive characters `ψ` modulo `q₁`
  (`exists_primitive`, from Mathlib's `primitiveCharacter`), so `c(n) = 1_{(n,q)=1}ψ(n)ψ̄′(n)`, as in their passage
  to `U*`. Round
  670's `CGLT101` at the modulus `q₁`, with the points `(u, ψ)`, separated because distinct keys differ in `ψ` or in
  the integer `u`, with the coefficients `1_{(n,q)=1}n^{iπξ}` and with `T′ = max(1, Q₀)(2T + 2)`, which makes
  `q₁T′ ≥ Q₀` for every `q₁`, is their Theorem 10.1 (`group_le`); integrating against `κ` gives `sum_Jk_le`.
* Their last step: `B|K| ≤ |R|²` and `B²|K| ≤ E` for the keys `K` of a group (`pow_mul_card_kg_le`,
  `pow_sq_mul_card_kg_le`), the second because two pairs `(i, j)` and `(k, l)` with one key give the quadruple
  `(i, l, k, j)` of the energy (`sum_card_cls_sq_le`); then `B²|K|^{5/4} ≤ E^{3/4}|R|` (`key_ineq`).

Plain statements, with `q ≥ 1`, `n ∼ M` round 670's `dyad`, `E` round 659's `energy` and `G` the groups (`grps`).
* `changeLevel_natCast`: a character modulo `q` induced from `ψ` modulo `q₁ ∣ q` is `ψ(n)` for `(n, q) = 1` and `0`
  otherwise. `exists_primitive`: a character modulo `q` of conductor `q₁` is induced from a primitive one modulo `q₁`.
* `sum_card_cls_sq_le`: `Σ_κ|cls κ|² ≤ E`. `card_grps_le`: `|G| ≤ d(q)(⌊log₂|R|²⌋ + 1)`.
* `norm_R2_four`, `sum_sq_gram`: `|R₂(n₁, n₂)|⁴ = |Σ_{p∈R×R}F_p(n₁)F̄_p(n₂)|²`, and the Gram expansion.
* `inner_le`: for `M > 0`, `|Σ_{n∼M}F_p(n)F̄_{p′}(n)|² ≤ J(key p, key p′)`.
* `group_le`, `sum_Jk_le`: from `CGLT101` at `ε`, `C` and `Q₀`, for keys `K` of conductor `q₁ ∣ q` with `|u| ≤ T′`,
  `Q₀ ≤ q₁T′` and `T′, M ≥ 1`, `Σ_{κ,κ′∈K}J(κ, κ′) ≤ ∫κ·C(q₁T′M)^ε(|K|M² + |K|²M + |K|^{5/4}(q₁T′)^{1/2}M)`.
* `sum_sq_Y_le`, `sum_R2_four_le`: for `M > 0`, a group's part `Y_g` of `|R₂|²` has
  `Σ_{n₁,n₂∼M}|Y_g|² ≤ 4·2^{2g₂}Σ_{κ,κ′}J(κ, κ′)`; and `Σ_{n₁,n₂}|R₂|⁴ ≤ |G|Σ_gΣ_{n₁,n₂}|Y_g|²`.
* `lemma107`: from `CGLT101`, for every `ε > 0` there is `C ≥ 0` such that, for `T, M ≥ 1` and points `|t_i| ≤ T`,
  `Σ_{n₁,n₂∼M}|R₂(n₁, n₂)|⁴ ≤ C(d(q)(⌊log₂|R|²⌋ + 1))²(qTM)^ε(EM² + |R|⁴M + E^{3/4}|R|(qT)^{1/2}M)`.

The factor `(d(q)(⌊log₂|R|²⌋ + 1))²` is the square of the bound on the number of groups: one factor comes from the
Cauchy–Schwarz step, and one from summing the groups' bounds, where they take the largest group. Their `⪅` absorbs it;
the stack keeps it explicit. `lemma107` assumes neither that `χ` is injective on `R` nor a lower bound on `qT`.

The file imports `LinnikCGLT101.lean`.
-/

import LinnikCGLT101

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLL107

open LinnikCGLL105 LinnikCGLT101 LinnikCGLMom4

/-! ### Characters -/

/-- `χ̄(n) = χ⁻¹(n)`. -/
lemma conj_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) : conj (χ n) = χ⁻¹ n :=
  MulChar.star_apply' χ n

/-- `(χψ⁻¹)(n) = χ(n)ψ̄(n)`. -/
lemma mul_inv_apply {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    (χ * ψ⁻¹) n = χ n * conj (ψ n) := by
  rw [MulChar.mul_apply, conj_apply]

/-- A character modulo `q` induced from `ψ` modulo `q₁ ∣ q` is `ψ(n)` for `(n, q) = 1` and `0` otherwise. -/
lemma changeLevel_natCast {q q₁ : ℕ} (hq : q₁ ∣ q) (ψ : DirichletCharacter ℂ q₁) (n : ℕ) :
    DirichletCharacter.changeLevel hq ψ n = if n.Coprime q then ψ n else 0 := by
  split_ifs with hn
  · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hq hu.unit
    rw [IsUnit.unit_spec] at h
    rw [h, ZMod.cast_natCast hq]
  · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

/-- Every character modulo `q` of conductor `q₁` is induced from a primitive character modulo `q₁`. -/
lemma exists_primitive {q q₁ : ℕ} (hq : q₁ ∣ q) (χ : DirichletCharacter ℂ q) (h : χ.conductor = q₁) :
    ∃ ψ : DirichletCharacter ℂ q₁, ψ.IsPrimitive ∧ DirichletCharacter.changeLevel hq ψ = χ := by
  subst h
  exact ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩

/-! ### The classes of pairs -/

section keys

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- The key of a pair `(i, j)`: `(⌊t_i − t_j⌋, χ_iχ_j⁻¹)`. -/
def key (p : ι × ι) : ℤ × DirichletCharacter ℂ q := (⌊t p.1 - t p.2⌋, χ p.1 * (χ p.2)⁻¹)

open scoped Classical in
/-- The pairs of `R` with the key `κ`, its class. -/
def cls (κ : ℤ × DirichletCharacter ℂ q) : Finset (ι × ι) := (R ×ˢ R).filter fun p => key χ t p = κ

open scoped Classical in
/-- The keys of the pairs of `R`. -/
def keys : Finset (ℤ × DirichletCharacter ℂ q) := (R ×ˢ R).image (key χ t)

/-- The group of a key: its conductor and the dyadic size `⌊log₂|cls κ|⌋` of its class. -/
def grp (κ : ℤ × DirichletCharacter ℂ q) : ℕ × ℕ := (κ.2.conductor, Nat.log 2 (cls R χ t κ).card)

open scoped Classical in
/-- The groups of the keys. -/
def grps : Finset (ℕ × ℕ) := (keys R χ t).image (grp R χ t)

open scoped Classical in
/-- The keys in the group `g`. -/
def kg (g : ℕ × ℕ) : Finset (ℤ × DirichletCharacter ℂ q) := (keys R χ t).filter fun κ => grp R χ t κ = g

lemma mem_cls {κ : ℤ × DirichletCharacter ℂ q} {p : ι × ι} :
    p ∈ cls R χ t κ ↔ p ∈ R ×ˢ R ∧ key χ t p = κ := by
  classical
  simp only [cls, Finset.mem_filter]

lemma mem_keys {κ : ℤ × DirichletCharacter ℂ q} : κ ∈ keys R χ t ↔ ∃ p ∈ R ×ˢ R, key χ t p = κ := by
  classical
  simp only [keys, Finset.mem_image]

lemma mem_kg {g : ℕ × ℕ} {κ : ℤ × DirichletCharacter ℂ q} :
    κ ∈ kg R χ t g ↔ κ ∈ keys R χ t ∧ grp R χ t κ = g := by
  classical
  simp only [kg, Finset.mem_filter]

lemma card_cls_pos {κ : ℤ × DirichletCharacter ℂ q} (hκ : κ ∈ keys R χ t) : 0 < (cls R χ t κ).card := by
  obtain ⟨p, hp, rfl⟩ := (mem_keys R χ t).mp hκ
  exact Finset.card_pos.mpr ⟨p, (mem_cls R χ t).mpr ⟨hp, rfl⟩⟩

lemma pow_lev_le {κ : ℤ × DirichletCharacter ℂ q} (hκ : κ ∈ keys R χ t) :
    2 ^ Nat.log 2 (cls R χ t κ).card ≤ (cls R χ t κ).card :=
  Nat.pow_log_le_self 2 (card_cls_pos R χ t hκ).ne'

lemma card_cls_lt (κ : ℤ × DirichletCharacter ℂ q) :
    (cls R χ t κ).card < 2 * 2 ^ Nat.log 2 (cls R χ t κ).card := by
  calc (cls R χ t κ).card < 2 ^ (Nat.log 2 (cls R χ t κ).card).succ := Nat.lt_pow_succ_log_self (by norm_num) _
    _ = 2 * 2 ^ Nat.log 2 (cls R χ t κ).card := by rw [pow_succ, mul_comm]

/-- `Σ_{p∈R×R}h(p) = Σ_κΣ_{p∈cls κ}h(p)`. -/
lemma sum_pairs_eq {M : Type*} [AddCommMonoid M] (h : ι × ι → M) :
    ∑ p ∈ R ×ˢ R, h p = ∑ κ ∈ keys R χ t, ∑ p ∈ cls R χ t κ, h p := by
  classical
  unfold cls
  rw [Finset.sum_fiberwise_of_maps_to (g := key χ t) (t := keys R χ t)]
  intro p hp
  exact (mem_keys R χ t).mpr ⟨p, hp, rfl⟩

/-- `Σ_κH(κ) = Σ_gΣ_{κ∈kg g}H(κ)`. -/
lemma sum_keys_eq {M : Type*} [AddCommMonoid M] (H : ℤ × DirichletCharacter ℂ q → M) :
    ∑ κ ∈ keys R χ t, H κ = ∑ g ∈ grps R χ t, ∑ κ ∈ kg R χ t g, H κ := by
  classical
  unfold kg
  rw [Finset.sum_fiberwise_of_maps_to (g := grp R χ t) (t := grps R χ t)]
  intro κ hκ
  unfold grps
  exact Finset.mem_image_of_mem _ hκ

/-- `Σ_κ|cls κ| = |R|²`. -/
lemma sum_card_cls : ∑ κ ∈ keys R χ t, (cls R χ t κ).card = R.card ^ 2 := by
  have h := sum_pairs_eq R χ t (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_product] at h
  rw [← h, sq]

lemma cls_subset (κ : ℤ × DirichletCharacter ℂ q) : cls R χ t κ ⊆ R ×ˢ R := fun _ hp => ((mem_cls R χ t).mp hp).1

/-- `Σ_κ|cls κ|² ≤ E`: two pairs `(i, j)` and `(k, l)` with one key give the quadruple `(i, l, k, j)` of the energy,
since `|t_i + t_l − t_k − t_j| < 1` when `⌊t_i − t_j⌋ = ⌊t_k − t_l⌋`, and `χ_iχ_j⁻¹ = χ_kχ_l⁻¹` is `χ_iχ_l = χ_kχ_j`. -/
lemma sum_card_cls_sq_le : ∑ κ ∈ keys R χ t, (cls R χ t κ).card ^ 2 ≤ energy R χ t := by
  classical
  have e : ∑ κ ∈ keys R χ t, (cls R χ t κ).card ^ 2 =
      ((keys R χ t).sigma fun κ => cls R χ t κ ×ˢ cls R χ t κ).card := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl fun κ _ => by rw [Finset.card_product, sq]
  rw [e]
  unfold energy
  refine Finset.card_le_card_of_injOn (fun x => (x.2.1.1, x.2.2.2, x.2.2.1, x.2.1.2)) ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product, mem_cls, mem_cls] at hx
    obtain ⟨-, ⟨hp, hpk⟩, ⟨hp', hp'k⟩⟩ := hx
    rw [Finset.mem_product] at hp hp'
    have hk : key χ t x.2.1 = key χ t x.2.2 := hpk.trans hp'k.symm
    unfold key at hk
    rw [Prod.mk.injEq] at hk
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Finset.mem_product]
      exact ⟨hp.1, hp'.2, hp'.1, hp.2⟩
    · have h := Int.abs_sub_lt_one_of_floor_eq_floor hk.1
      have e2 : t x.2.1.1 + t x.2.2.2 - t x.2.2.1 - t x.2.1.2 =
          t x.2.1.1 - t x.2.1.2 - (t x.2.2.1 - t x.2.2.2) := by ring
      dsimp only
      rw [e2]
      exact h.le
    · have h2 := hk.2
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at h2
      exact h2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product, mem_cls] at hx hy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3, h4⟩ := hxy
    have e1 : x.2.1 = y.2.1 := Prod.ext h1 h4
    have e2 : x.2.2 = y.2.2 := Prod.ext h3 h2
    have ek : x.1 = y.1 := by rw [← hx.2.1.2, ← hy.2.1.2, e1]
    exact Sigma.ext ek (heq_of_eq (Prod.ext e1 e2))

/-- `2^{g₂}|kg g| ≤ |R|²`: each class in the group `g` has at least `2^{g₂}` pairs. -/
lemma pow_mul_card_kg_le (g : ℕ × ℕ) : 2 ^ g.2 * (kg R χ t g).card ≤ R.card ^ 2 := by
  calc 2 ^ g.2 * (kg R χ t g).card = ∑ κ ∈ kg R χ t g, 2 ^ g.2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ κ ∈ kg R χ t g, (cls R χ t κ).card := Finset.sum_le_sum fun κ hκ => by
        obtain ⟨hκ1, hκ2⟩ := (mem_kg R χ t).mp hκ
        have e : Nat.log 2 (cls R χ t κ).card = g.2 := by rw [← hκ2]; rfl
        rw [← e]
        exact pow_lev_le R χ t hκ1
    _ ≤ ∑ κ ∈ keys R χ t, (cls R χ t κ).card :=
        Finset.sum_le_sum_of_subset fun κ hκ => ((mem_kg R χ t).mp hκ).1
    _ = R.card ^ 2 := sum_card_cls R χ t

/-- `(2^{g₂})²|kg g| ≤ E`. -/
lemma pow_sq_mul_card_kg_le (g : ℕ × ℕ) : (2 ^ g.2) ^ 2 * (kg R χ t g).card ≤ energy R χ t := by
  calc (2 ^ g.2) ^ 2 * (kg R χ t g).card = ∑ κ ∈ kg R χ t g, (2 ^ g.2) ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ κ ∈ kg R χ t g, (cls R χ t κ).card ^ 2 := Finset.sum_le_sum fun κ hκ => by
        obtain ⟨hκ1, hκ2⟩ := (mem_kg R χ t).mp hκ
        have e : Nat.log 2 (cls R χ t κ).card = g.2 := by rw [← hκ2]; rfl
        rw [← e]
        exact Nat.pow_le_pow_left (pow_lev_le R χ t hκ1) 2
    _ ≤ ∑ κ ∈ keys R χ t, (cls R χ t κ).card ^ 2 :=
        Finset.sum_le_sum_of_subset fun κ hκ => ((mem_kg R χ t).mp hκ).1
    _ ≤ energy R χ t := sum_card_cls_sq_le R χ t

/-- The number of groups: at most `d(q)(⌊log₂|R|²⌋ + 1)`. -/
lemma card_grps_le [NeZero q] : (grps R χ t).card ≤ q.divisors.card * (Nat.log 2 (R.card ^ 2) + 1) := by
  classical
  calc (grps R χ t).card ≤ (q.divisors ×ˢ Finset.range (Nat.log 2 (R.card ^ 2) + 1)).card := by
        refine Finset.card_le_card fun g hg => ?_
        simp only [grps, Finset.mem_image] at hg
        obtain ⟨κ, -, rfl⟩ := hg
        rw [Finset.mem_product, Nat.mem_divisors, Finset.mem_range]
        refine ⟨⟨κ.2.conductor_dvd_level, NeZero.ne q⟩, Nat.lt_succ_of_le ?_⟩
        show Nat.log 2 (cls R χ t κ).card ≤ Nat.log 2 (R.card ^ 2)
        refine Nat.log_mono_right ?_
        calc (cls R χ t κ).card ≤ (R ×ˢ R).card := Finset.card_le_card (cls_subset R χ t κ)
          _ = R.card ^ 2 := by rw [Finset.card_product, sq]
    _ = q.divisors.card * (Nat.log 2 (R.card ^ 2) + 1) := by rw [Finset.card_product, Finset.card_range]

end keys

/-! ### The fourth power of `R₂` as a Gram matrix -/

section gram

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- `a_i(n) = χ_i(n)e^{it_i log n}`. -/
def aR (i : ι) (n : ℕ) : ℂ := χ i n * cexp (↑(t i * Real.log n) * I)

/-- `F_p(n) = a_i(n)ā_j(n)` for `p = (i, j)`. -/
def F (p : ι × ι) (n : ℕ) : ℂ := aR χ t p.1 n * conj (aR χ t p.2 n)

lemma conj_cexp (x : ℝ) : conj (cexp (↑x * I)) = cexp (↑(-x) * I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

lemma cexp_mul_cexp (x y : ℝ) : cexp (↑x * I) * cexp (↑y * I) = cexp (↑(x + y) * I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `R₂(n₁, n₂) = Σ_ia_i(n₁)ā_i(n₂)`. -/
lemma R2_eq (n₁ n₂ : ℕ) : R2 R χ t n₁ n₂ = ∑ i ∈ R, aR χ t i n₁ * conj (aR χ t i n₂) := by
  unfold R2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [aR, map_mul, conj_cexp]
  have e2 : cexp (↑(t i * (Real.log n₁ - Real.log n₂)) * I) =
      cexp (↑(t i * Real.log n₁) * I) * cexp (↑(-(t i * Real.log n₂)) * I) := by
    rw [cexp_mul_cexp]
    congr 3
    ring
  rw [e2]
  ring

/-- `|R₂(n₁, n₂)|⁴ = |Σ_{p∈R×R}F_p(n₁)F̄_p(n₂)|²`. -/
lemma norm_R2_four (n₁ n₂ : ℕ) :
    ‖R2 R χ t n₁ n₂‖ ^ 4 = ‖∑ p ∈ R ×ˢ R, F χ t p n₁ * conj (F χ t p n₂)‖ ^ 2 := by
  have h : ((‖R2 R χ t n₁ n₂‖ ^ 2 : ℝ) : ℂ) = ∑ p ∈ R ×ˢ R, F χ t p n₁ * conj (F χ t p n₂) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, R2_eq, map_sum, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [F, map_mul, Complex.conj_conj]
    ring
  calc ‖R2 R χ t n₁ n₂‖ ^ 4 = ‖((‖R2 R χ t n₁ n₂‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 := by
        rw [Complex.norm_of_nonneg (by positivity)]
        ring
    _ = _ := by rw [h]

/-- **The Gram expansion**: `Σ_{n₁,n₂∈S}|Σ_{p∈P}a_p(n₁)ā_p(n₂)|² = Σ_{p,p′∈P}|Σ_{n∈S}a_p(n)ā_{p′}(n)|²`. -/
lemma sum_sq_gram {κ : Type*} (P : Finset κ) (a : κ → ℕ → ℂ) (S : Finset ℕ) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖∑ p ∈ P, a p n₁ * conj (a p n₂)‖ ^ 2 =
      ∑ p ∈ P, ∑ p' ∈ P, ‖∑ n ∈ S, a p n * conj (a p' n)‖ ^ 2 := by
  have hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * conj z := fun z => by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ofReal_injective
  push_cast
  simp only [hsq, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := P) (t := S)]
  refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The coefficients `c_{κκ′}(n) = κ(n)κ̄′(n)` of two keys. -/
def cc (κ κ' : ℤ × DirichletCharacter ℂ q) (n : ℕ) : ℂ := κ.2 n * conj (κ'.2 n)

lemma npow_eq {n : ℕ} (hn : 0 < n) (θ : ℝ) : (n : ℂ) ^ ((θ : ℂ) * I) = cexp (↑(θ * Real.log n) * I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 1
  push_cast
  ring

/-- `F_p(n)F̄_{p′}(n) = c_{key p, key p′}(n)n^{i(t_i − t_j − (t_k − t_l))}` for `n > 0`. -/
lemma F_mul_conj [NeZero q] (p p' : ι × ι) {n : ℕ} (hn : 0 < n) :
    F χ t p n * conj (F χ t p' n) =
      cc (key χ t p) (key χ t p') n * (n : ℂ) ^ (((t p.1 - t p.2 - (t p'.1 - t p'.2) : ℝ) : ℂ) * I) := by
  rw [npow_eq hn]
  unfold F aR cc key
  simp only [mul_inv_apply, map_mul, Complex.conj_conj, conj_cexp]
  have e : cexp (↑((t p.1 - t p.2 - (t p'.1 - t p'.2)) * Real.log n) * I) =
      cexp (↑(t p.1 * Real.log n) * I) * cexp (↑(-(t p.2 * Real.log n)) * I) *
        (cexp (↑(-(t p'.1 * Real.log n)) * I) * cexp (↑(t p'.2 * Real.log n) * I)) := by
    rw [cexp_mul_cexp, cexp_mul_cexp, cexp_mul_cexp]
    congr 2
    push_cast
    ring
  rw [e]
  ring_nf

/-- `Σ_{n∈S}F_p(n)F̄_{p′}(n) = D_{c}(t_i − t_j − (t_k − t_l))` with `c = c_{key p, key p′}`, for `S` of positive
integers. -/
lemma inner_eq_Dp [NeZero q] (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (p p' : ι × ι) :
    ∑ n ∈ S, F χ t p n * conj (F χ t p' n) =
      Dp S (cc (key χ t p) (key χ t p')) (t p.1 - t p.2 - (t p'.1 - t p'.2)) := by
  unfold Dp
  exact Finset.sum_congr rfl fun n hn => F_mul_conj χ t p p' (hS n hn)

/-- `J(κ, κ′) = ∫κ(ξ)|D_{c_{κκ′}}(u − u′ + πξ)|² dξ` for the keys `κ = (u, ·)` and `κ′ = (u′, ·)`. -/
def Jk (S : Finset ℕ) (κ κ' : ℤ × DirichletCharacter ℂ q) : ℝ :=
  ∫ ξ, kmaj ξ * ‖Dp S (cc κ κ') ((κ.1 : ℝ) - κ'.1 + π * ξ)‖ ^ 2

lemma Jk_nonneg (S : Finset ℕ) (κ κ' : ℤ × DirichletCharacter ℂ q) : 0 ≤ Jk S κ κ' :=
  integral_nonneg fun ξ => mul_nonneg (kmaj_nonneg ξ) (by positivity)

lemma dyad_pos {M : ℝ} (hM : 0 < M) : ∀ n ∈ dyad M, 0 < n := fun n hn => by
  have := ((mem_dyad hM.le).mp hn).1
  exact_mod_cast hM.trans this

/-- **The local average** (their Lemma 10.4, through round 669's `norm_sq_Dp_le_shift`): for `M > 0`,
`|Σ_{n∼M}F_p(n)F̄_{p′}(n)|² ≤ J(key p, key p′)`, since the frequency `t_i − t_j − (t_k − t_l)` is within `1` of
`⌊t_i − t_j⌋ − ⌊t_k − t_l⌋`. -/
lemma inner_le [NeZero q] {M : ℝ} (hM : 0 < M) (p p' : ι × ι) :
    ‖∑ n ∈ dyad M, F χ t p n * conj (F χ t p' n)‖ ^ 2 ≤ Jk (dyad M) (key χ t p) (key χ t p') := by
  have hS : ∀ n ∈ dyad M, M ≤ n ∧ (n : ℝ) ≤ 2 * M := fun n hn => by
    have := (mem_dyad hM.le).mp hn
    exact ⟨this.1.le, this.2⟩
  rw [inner_eq_Dp χ t (dyad M) (dyad_pos hM) p p']
  unfold Jk
  refine norm_sq_Dp_le_shift (dyad M) _ hM hS ?_
  have h1 := Int.floor_le (t p.1 - t p.2)
  have h2 := Int.lt_floor_add_one (t p.1 - t p.2)
  have h3 := Int.floor_le (t p'.1 - t p'.2)
  have h4 := Int.lt_floor_add_one (t p'.1 - t p'.2)
  simp only [key]
  rw [abs_le]
  constructor <;> linarith

/-- The integrand of `J` is integrable. -/
lemma integrable_Jk (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (c : ℕ → ℂ) (a : ℝ) :
    Integrable fun ξ => kmaj ξ * ‖Dp S c (a + π * ξ)‖ ^ 2 := by
  have hC := continuous_Dp S c hS
  refine (integrable_kmaj.mul_const ((∑ n ∈ S, ‖c n‖) ^ 2)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (continuous_const.div (by fun_prop) (fun ξ => by positivity) |>.mul
      ((hC.comp (by fun_prop)).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kmaj_nonneg ξ) (by positivity))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_Dp_le S c _) 2) (kmaj_nonneg ξ)

end gram

/-! ### Their Theorem 10.1 on one group -/

/-- `CGLT101`'s statement at `ε`, with the constants `C` and `Q₀`. -/
def T101At (ε C Q₀ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] {ι : Type} (P : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (T M B : ℝ)
    (c : ℕ → ℂ),
    Q₀ ≤ (q : ℝ) * T → 1 ≤ T → 1 ≤ M → (∀ i ∈ P, (χ i).IsPrimitive) → (∀ i ∈ P, |t i| ≤ T) →
    (∀ i ∈ P, ∀ j ∈ P, i ≠ j → χ i ≠ χ j ∨ 1 ≤ |t i - t j|) → (∀ n ∈ dyad M, ‖c n‖ ≤ B) →
    ∑ i ∈ P, ∑ j ∈ P, ‖∑ n ∈ dyad M, c n * χ i n * conj (χ j n) * (n : ℂ) ^ (((t i - t j : ℝ) : ℂ) * I)‖ ^ 2 ≤
      C * ((q : ℝ) * T * M) ^ ε * ((P.card : ℝ) * M ^ 2 + (P.card : ℝ) ^ 2 * M +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) * B ^ 2

lemma t101At (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) : ∃ C Q₀ : ℝ, T101At ε C Q₀ := hT ε hε

/-- The constant may be taken nonnegative. -/
lemma T101At.max {ε C Q₀ : ℝ} (hC : T101At ε C Q₀) : T101At ε (max C 0) Q₀ := by
  intro q _ ι P χ t T M B c hQ hT hM hprim ht hsep hc
  refine (hC q P χ t T M B c hQ hT hM hprim ht hsep hc).trans ?_
  have hX : 0 ≤ ((q : ℝ) * T * M) ^ ε * ((P.card : ℝ) * M ^ 2 + (P.card : ℝ) ^ 2 * M +
      (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) := by
    have hM0 : (0 : ℝ) ≤ M := by linarith
    have hT0 : (0 : ℝ) ≤ T := by linarith
    positivity
  have e : ∀ C' : ℝ, C' * ((q : ℝ) * T * M) ^ ε * ((P.card : ℝ) * M ^ 2 + (P.card : ℝ) ^ 2 * M +
      (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) * B ^ 2 =
      C' * (((q : ℝ) * T * M) ^ ε * ((P.card : ℝ) * M ^ 2 + (P.card : ℝ) ^ 2 * M +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M)) * B ^ 2 := fun C' => by ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX) (sq_nonneg B)

/-- **Their Theorem 10.1 on one group of keys**: from `CGLT101` at `ε`, `C` and `Q₀` (`T101At`), for keys `K` modulo
`q` whose characters all have conductor `q₁ ∣ q`, with `|u| ≤ T′`, `Q₀ ≤ q₁T′`, `T′, M ≥ 1` and each `ξ`,
`Σ_{κ,κ′∈K}|D_{c_{κκ′}}(u − u′ + πξ)|² ≤ C(q₁T′M)^ε(|K|M² + |K|²M + |K|^{5/4}(q₁T′)^{1/2}M)`. Each character is
induced from a primitive character `ψ` modulo `q₁` (`exists_primitive`), so `c_{κκ′}(n) = 1_{(n,q)=1}ψ(n)ψ̄′(n)`; the
keys are distinct, so the points `(u, ψ)` are separated; and `|1_{(n,q)=1}n^{iπξ}| ≤ 1`. -/
theorem group_le {ε C Q₀ : ℝ} (hC : T101At ε C Q₀) {q q₁ : ℕ} [NeZero q] (hq₁ : q₁ ∣ q)
    (K : Finset (ℤ × DirichletCharacter ℂ q)) (hK : ∀ κ ∈ K, κ.2.conductor = q₁) {T' M : ℝ}
    (hKT : ∀ κ ∈ K, |(κ.1 : ℝ)| ≤ T') (hQ : Q₀ ≤ q₁ * T') (hT' : 1 ≤ T') (hM : 1 ≤ M) (ξ : ℝ) :
    ∑ κ ∈ K, ∑ κ' ∈ K, ‖Dp (dyad M) (cc κ κ') ((κ.1 : ℝ) - κ'.1 + π * ξ)‖ ^ 2 ≤
      C * ((q₁ : ℝ) * T' * M) ^ ε * ((K.card : ℝ) * M ^ 2 + (K.card : ℝ) ^ 2 * M +
        (K.card : ℝ) ^ (5 / 4 : ℝ) * ((q₁ : ℝ) * T') ^ (1 / 2 : ℝ) * M) := by
  classical
  have : NeZero q₁ := ⟨fun h => NeZero.ne q (Nat.eq_zero_of_zero_dvd (h ▸ hq₁))⟩
  set f : ℤ × DirichletCharacter ℂ q₁ → ℤ × DirichletCharacter ℂ q :=
    fun x => (x.1, DirichletCharacter.changeLevel hq₁ x.2) with hf
  have hfi : Function.Injective f := by
    intro x y h
    simp only [hf, Prod.mk.injEq] at h
    exact Prod.ext h.1 (DirichletCharacter.changeLevel_injective hq₁ h.2)
  set Ks := (K.preimage f hfi.injOn).filter fun x => x.2.IsPrimitive with hKs
  have hKe : K = Ks.image f := by
    ext κ
    simp only [hKs, Finset.mem_image, Finset.mem_filter, Finset.mem_preimage]
    constructor
    · intro hκ
      obtain ⟨ψ, hψ, hψκ⟩ := exists_primitive hq₁ κ.2 (hK κ hκ)
      have hfκ : f (κ.1, ψ) = κ := by simp only [hf, hψκ]
      exact ⟨(κ.1, ψ), ⟨hfκ ▸ hκ, hψ⟩, hfκ⟩
    · rintro ⟨x, ⟨hx, -⟩, rfl⟩
      exact hx
  set c : ℕ → ℂ := fun n => (if n.Coprime q then 1 else 0) * (n : ℂ) ^ (((π * ξ : ℝ) : ℂ) * I) with hc
  have hterm : ∀ x x' : ℤ × DirichletCharacter ℂ q₁,
      Dp (dyad M) (cc (f x) (f x')) (((f x).1 : ℝ) - (f x').1 + π * ξ) =
        ∑ n ∈ dyad M, c n * x.2 n * conj (x'.2 n) * (n : ℂ) ^ ((((x.1 : ℝ) - x'.1 : ℝ) : ℂ) * I) := by
    intro x x'
    unfold Dp
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (dyad_pos (by linarith) n hn).ne'
    have hsplit : (n : ℂ) ^ (((((x.1 : ℝ) - x'.1 + π * ξ : ℝ)) : ℂ) * I) =
        (n : ℂ) ^ ((((x.1 : ℝ) - x'.1 : ℝ) : ℂ) * I) * (n : ℂ) ^ (((π * ξ : ℝ) : ℂ) * I) := by
      rw [← Complex.cpow_add _ _ hn0]
      congr 1
      push_cast
      ring
    simp only [hf, cc, changeLevel_natCast, hc]
    rw [hsplit]
    split_ifs with hcop
    · ring
    · simp
  rw [hKe, Finset.sum_image hfi.injOn, Finset.card_image_of_injective _ hfi]
  simp_rw [Finset.sum_image hfi.injOn, hterm]
  have h := hC q₁ Ks Prod.snd (fun x => (x.1 : ℝ)) T' M 1 c hQ hT' hM
    (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_ ?_
  · rw [one_pow, mul_one] at h
    exact h
  · intro x hx
    have := hKT (f x) (Finset.mem_preimage.mp (Finset.mem_filter.mp hx).1)
    simpa [hf] using this
  · intro x _ y _ hxy
    by_cases h2 : x.2 = y.2
    · right
      have h1 : x.1 ≠ y.1 := fun h1 => hxy (Prod.ext h1 h2)
      have h3 : (1 : ℤ) ≤ |x.1 - y.1| := Int.one_le_abs (sub_ne_zero.mpr h1)
      have h4 : (1 : ℝ) ≤ |((x.1 - y.1 : ℤ) : ℝ)| := by exact_mod_cast h3
      simpa using h4
    · left
      exact h2
  · intro n hn
    have hn0 := dyad_pos (by linarith) n hn
    simp only [hc, norm_mul, Complex.norm_natCast_cpow_of_pos hn0]
    have hre : ((((π * ξ : ℝ) : ℂ) * I)).re = 0 := by simp
    rw [hre, Real.rpow_zero, mul_one]
    split_ifs <;> simp

/-- **One group, integrated**: `Σ_{κ,κ′∈K}J(κ, κ′) ≤ ∫κ·C(q₁T′M)^ε(|K|M² + |K|²M + |K|^{5/4}(q₁T′)^{1/2}M)` under
`group_le`'s hypotheses. -/
theorem sum_Jk_le {ε C Q₀ : ℝ} (hC : T101At ε C Q₀) {q q₁ : ℕ} [NeZero q] (hq₁ : q₁ ∣ q)
    (K : Finset (ℤ × DirichletCharacter ℂ q)) (hK : ∀ κ ∈ K, κ.2.conductor = q₁) {T' M : ℝ}
    (hKT : ∀ κ ∈ K, |(κ.1 : ℝ)| ≤ T') (hQ : Q₀ ≤ q₁ * T') (hT' : 1 ≤ T') (hM : 1 ≤ M) :
    ∑ κ ∈ K, ∑ κ' ∈ K, Jk (dyad M) κ κ' ≤ (∫ ξ, kmaj ξ) * (C * ((q₁ : ℝ) * T' * M) ^ ε *
      ((K.card : ℝ) * M ^ 2 + (K.card : ℝ) ^ 2 * M +
        (K.card : ℝ) ^ (5 / 4 : ℝ) * ((q₁ : ℝ) * T') ^ (1 / 2 : ℝ) * M)) := by
  have hpos := dyad_pos (by linarith : (0 : ℝ) < M)
  have hint : ∀ κ κ' : ℤ × DirichletCharacter ℂ q,
      Integrable fun ξ => kmaj ξ * ‖Dp (dyad M) (cc κ κ') ((κ.1 : ℝ) - κ'.1 + π * ξ)‖ ^ 2 :=
    fun κ κ' => integrable_Jk (dyad M) hpos (cc κ κ') ((κ.1 : ℝ) - κ'.1)
  have e1 : ∑ κ ∈ K, ∑ κ' ∈ K, Jk (dyad M) κ κ' =
      ∫ ξ, kmaj ξ * ∑ κ ∈ K, ∑ κ' ∈ K, ‖Dp (dyad M) (cc κ κ') ((κ.1 : ℝ) - κ'.1 + π * ξ)‖ ^ 2 := by
    unfold Jk
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun κ _ => integrable_finsetSum _ fun κ' _ => hint κ κ']
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [integral_finsetSum _ fun κ' _ => hint κ κ']
  rw [e1, ← integral_mul_const]
  refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => ?_) (integrable_kmaj.mul_const _)
    (Eventually.of_forall fun ξ => ?_)
  · exact mul_nonneg (kmaj_nonneg ξ) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  · exact mul_le_mul_of_nonneg_left (group_le hC hq₁ K hK hKT hQ hT' hM ξ) (kmaj_nonneg ξ)

/-! ### The groups summed -/

section groups

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- `Y_g(n₁, n₂) = Σ_{κ∈kg g}Σ_{p∈cls κ}F_p(n₁)F̄_p(n₂)`, the part of `|R₂(n₁, n₂)|²` in the group `g`. -/
def Y (g : ℕ × ℕ) (n₁ n₂ : ℕ) : ℂ := ∑ κ ∈ kg R χ t g, ∑ p ∈ cls R χ t κ, F χ t p n₁ * conj (F χ t p n₂)

/-- **One group's Gram matrix**: for `M > 0`, `Σ_{n₁,n₂∼M}|Y_g|² ≤ 4(2^{g₂})²Σ_{κ,κ′∈kg g}J(κ, κ′)`. The Gram
expansion gives
`Σ_{p,p′}|Σ_nF_pF̄_{p′}|²` over the pairs of the group, each term is at most `J(key p, key p′)` (`inner_le`), and each
class in the group has fewer than `2·2^{g₂}` pairs. -/
theorem sum_sq_Y_le [NeZero q] {M : ℝ} (hM : 0 < M) (g : ℕ × ℕ) :
    ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖Y R χ t g n₁ n₂‖ ^ 2 ≤
      4 * ((2 : ℝ) ^ g.2) ^ 2 * ∑ κ ∈ kg R χ t g, ∑ κ' ∈ kg R χ t g, Jk (dyad M) κ κ' := by
  classical
  set P := (kg R χ t g).sigma fun κ => cls R χ t κ with hP
  have hY : ∀ n₁ n₂, Y R χ t g n₁ n₂ = ∑ x ∈ P, F χ t x.2 n₁ * conj (F χ t x.2 n₂) := fun n₁ n₂ => by
    rw [hP, Finset.sum_sigma]
    rfl
  simp_rw [hY]
  rw [sum_sq_gram P (fun x => F χ t x.2) (dyad M)]
  have hb : ∀ κ ∈ kg R χ t g, ((cls R χ t κ).card : ℝ) ≤ 2 * 2 ^ g.2 := fun κ hκ => by
    have e : Nat.log 2 (cls R χ t κ).card = g.2 := by rw [← ((mem_kg R χ t).mp hκ).2]; rfl
    have h := card_cls_lt R χ t κ
    rw [e] at h
    exact_mod_cast h.le
  calc ∑ x ∈ P, ∑ x' ∈ P, ‖∑ n ∈ dyad M, F χ t x.2 n * conj (F χ t x'.2 n)‖ ^ 2
      ≤ ∑ x ∈ P, ∑ x' ∈ P, Jk (dyad M) x.1 x'.1 := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x' hx' => ?_
        have h1 : key χ t x.2 = x.1 := ((mem_cls R χ t).mp (Finset.mem_sigma.mp hx).2).2
        have h2 : key χ t x'.2 = x'.1 := ((mem_cls R χ t).mp (Finset.mem_sigma.mp hx').2).2
        rw [← h1, ← h2]
        exact inner_le χ t hM x.2 x'.2
    _ = ∑ κ ∈ kg R χ t g, ∑ κ' ∈ kg R χ t g,
          ((cls R χ t κ).card : ℝ) * (cls R χ t κ').card * Jk (dyad M) κ κ' := by
        rw [hP, Finset.sum_sigma]
        refine Finset.sum_congr rfl fun κ _ => ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_sigma, Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ' _ => ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ κ ∈ kg R χ t g, ∑ κ' ∈ kg R χ t g, 4 * ((2 : ℝ) ^ g.2) ^ 2 * Jk (dyad M) κ κ' := by
        refine Finset.sum_le_sum fun κ hκ => Finset.sum_le_sum fun κ' hκ' => ?_
        refine mul_le_mul_of_nonneg_right ?_ (Jk_nonneg _ _ _)
        calc ((cls R χ t κ).card : ℝ) * (cls R χ t κ').card ≤ (2 * 2 ^ g.2) * (2 * 2 ^ g.2) :=
              mul_le_mul (hb κ hκ) (hb κ' hκ') (by positivity) (by positivity)
          _ = 4 * ((2 : ℝ) ^ g.2) ^ 2 := by ring
    _ = 4 * ((2 : ℝ) ^ g.2) ^ 2 * ∑ κ ∈ kg R χ t g, ∑ κ' ∈ kg R χ t g, Jk (dyad M) κ κ' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [Finset.mul_sum]

/-- **Cauchy–Schwarz over the groups**: `Σ_{n₁,n₂}|R₂|⁴ ≤ |G|Σ_{g∈G}Σ_{n₁,n₂}|Y_g|²`, since
`|R₂(n₁, n₂)|² = Σ_{g∈G}Y_g(n₁, n₂)`. -/
theorem sum_R2_four_le (S : Finset ℕ) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 4 ≤
      (grps R χ t).card * ∑ g ∈ grps R χ t, ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖Y R χ t g n₁ n₂‖ ^ 2 := by
  have h : ∀ n₁ n₂, ‖R2 R χ t n₁ n₂‖ ^ 4 ≤ (grps R χ t).card * ∑ g ∈ grps R χ t, ‖Y R χ t g n₁ n₂‖ ^ 2 := by
    intro n₁ n₂
    rw [norm_R2_four, sum_pairs_eq R χ t, sum_keys_eq R χ t]
    calc ‖∑ g ∈ grps R χ t, Y R χ t g n₁ n₂‖ ^ 2 ≤ (∑ g ∈ grps R χ t, ‖Y R χ t g n₁ n₂‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  calc ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 4
      ≤ ∑ n₁ ∈ S, ∑ n₂ ∈ S, (grps R χ t).card * ∑ g ∈ grps R χ t, ‖Y R χ t g n₁ n₂‖ ^ 2 :=
        Finset.sum_le_sum fun n₁ _ => Finset.sum_le_sum fun n₂ _ => h n₁ n₂
    _ = (grps R χ t).card * ∑ n₁ ∈ S, ∑ n₂ ∈ S, ∑ g ∈ grps R χ t, ‖Y R χ t g n₁ n₂‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₁ _ => ?_
        rw [Finset.mul_sum]
    _ = _ := by
        congr 1
        calc ∑ n₁ ∈ S, ∑ n₂ ∈ S, ∑ g ∈ grps R χ t, ‖Y R χ t g n₁ n₂‖ ^ 2
            = ∑ n₁ ∈ S, ∑ g ∈ grps R χ t, ∑ n₂ ∈ S, ‖Y R χ t g n₁ n₂‖ ^ 2 :=
              Finset.sum_congr rfl fun n₁ _ => Finset.sum_comm
          _ = _ := Finset.sum_comm

end groups

/-- `B²K^{5/4} ≤ E^{3/4}W` for `B, K, E, W ≥ 0`, `BK ≤ W²` and `B²K ≤ E`: the fourth powers are `(B²K)³(BK)²` and
`E³W⁴`. -/
lemma key_ineq {B K E W : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hE : 0 ≤ E) (hW : 0 ≤ W) (h1 : B * K ≤ W ^ 2)
    (h2 : B ^ 2 * K ≤ E) : B ^ 2 * K ^ (5 / 4 : ℝ) ≤ E ^ (3 / 4 : ℝ) * W := by
  have hK4 : (K ^ (5 / 4 : ℝ)) ^ 4 = K ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK]
    norm_num
  have hE4 : (E ^ (3 / 4 : ℝ)) ^ 4 = E ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
  rw [mul_pow, mul_pow, hK4, hE4]
  calc (B ^ 2) ^ 4 * K ^ 5 = (B ^ 2 * K) ^ 3 * (B * K) ^ 2 := by ring
    _ ≤ E ^ 3 * (W ^ 2) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h2 3) (pow_le_pow_left₀ (by positivity) h1 2)
          (by positivity) (by positivity)
    _ = E ^ 3 * W ^ 4 := by ring

/-- `x^z ≤ b^z·c^z` for `0 ≤ x ≤ bc`, `b, c ≥ 0` and `z ≥ 0`. -/
lemma rpow_le_mul_rpow {x b c z : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (hc : 0 ≤ c) (hxbc : x ≤ b * c) (hz : 0 ≤ z) :
    x ^ z ≤ b ^ z * c ^ z := by
  rw [← Real.mul_rpow hb hc]
  exact Real.rpow_le_rpow hx hxbc hz

/-! ### Their Lemma 10.7 -/

/-- **One group, bounded**: for a group `g` of `R`'s keys, `ε ≥ 0`, `C ≥ 0`, `T, M ≥ 1`, points `|t_i| ≤ T`,
`T′ ≥ 2T + 1` and `Q₀ ≤ T′`, from `CGLT101` at `ε`, `C` and `Q₀`,
`Σ_{n₁,n₂∼M}|Y_g|² ≤ 4∫κ·C(qT′M)^ε(EM² + |R|⁴M + E^{3/4}|R|(qT′)^{1/2}M)`. With `B = 2^{g₂}` and `K` the group's keys,
`B|K| ≤ |R|²` and `B²|K| ≤ E`, so `B²|K|² ≤ |R|⁴` and `B²|K|^{5/4} ≤ E^{3/4}|R|`; the group's conductor `q₁` divides
`q`. -/
theorem group_bound {ε C Q₀ : ℝ} (hC : T101At ε C Q₀) (hC0 : 0 ≤ C) (hε : 0 ≤ ε) {ι : Type*} {q : ℕ} [NeZero q]
    (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) {T T' M : ℝ} (hT : 1 ≤ T) (hM : 1 ≤ M)
    (ht : ∀ i ∈ R, |t i| ≤ T) (hT' : 2 * T + 1 ≤ T') (hQ : Q₀ ≤ T') {g : ℕ × ℕ} (hg : g ∈ grps R χ t) :
    ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖Y R χ t g n₁ n₂‖ ^ 2 ≤
      4 * (∫ ξ, kmaj ξ) * C * ((q : ℝ) * T' * M) ^ ε * ((energy R χ t : ℝ) * M ^ 2 + (R.card : ℝ) ^ 4 * M +
        (energy R χ t : ℝ) ^ (3 / 4 : ℝ) * R.card * ((q : ℝ) * T') ^ (1 / 2 : ℝ) * M) := by
  classical
  have hM0 : (0 : ℝ) < M := by linarith
  have hT'1 : 1 ≤ T' := by linarith
  have hT'0 : (0 : ℝ) ≤ T' := by linarith
  obtain ⟨κ₀, -, hgκ⟩ : ∃ κ₀ ∈ keys R χ t, grp R χ t κ₀ = g := by
    simp only [grps, Finset.mem_image] at hg
    exact hg
  have hq₁ : g.1 ∣ q := by
    rw [← hgκ]
    exact κ₀.2.conductor_dvd_level
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq₁1 : (1 : ℝ) ≤ g.1 := by exact_mod_cast Nat.pos_of_dvd_of_pos hq₁ hqpos
  have hq₁q : (g.1 : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hqpos hq₁
  have hK : ∀ κ ∈ kg R χ t g, κ.2.conductor = g.1 := fun κ hκ => by
    rw [← ((mem_kg R χ t).mp hκ).2]
    rfl
  have hKT : ∀ κ ∈ kg R χ t g, |(κ.1 : ℝ)| ≤ T' := fun κ hκ => by
    obtain ⟨p, hp, rfl⟩ := (mem_keys R χ t).mp ((mem_kg R χ t).mp hκ).1
    rw [Finset.mem_product] at hp
    have h1 := abs_le.mp (ht p.1 hp.1)
    have h2 := abs_le.mp (ht p.2 hp.2)
    have h3 := Int.floor_le (t p.1 - t p.2)
    have h4 := Int.lt_floor_add_one (t p.1 - t p.2)
    simp only [key]
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hQ' : Q₀ ≤ g.1 * T' := le_trans hQ (by nlinarith)
  have hJ := sum_Jk_le hC hq₁ (kg R χ t g) hK hKT hQ' hT'1 hM
  have hY := sum_sq_Y_le R χ t hM0 g
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (2 : ℝ) ^ g.2 := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = (kg R χ t g).card := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = energy R χ t := ⟨_, rfl⟩
  obtain ⟨Rc, hRc⟩ : ∃ Rc : ℝ, Rc = R.card := ⟨_, rfl⟩
  rw [← hB] at hY
  rw [← hKc] at hJ
  rw [← hE, ← hRc]
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hK0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hR0 : 0 ≤ Rc := by rw [hRc]; positivity
  have hBK : B * Kc ≤ Rc ^ 2 := by
    rw [hB, hKc, hRc]
    exact_mod_cast pow_mul_card_kg_le R χ t g
  have hBK2 : B ^ 2 * Kc ≤ E := by
    rw [hB, hKc, hE]
    exact_mod_cast pow_sq_mul_card_kg_le R χ t g
  have hkey := key_ineq hB0 hK0 hE0 hR0 hBK hBK2
  have hI : 0 ≤ ∫ ξ, kmaj ξ := integral_nonneg kmaj_nonneg
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ, P1 = ((g.1 : ℝ) * T' * M) ^ ε := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ((q : ℝ) * T' * M) ^ ε := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ X1 : ℝ, X1 = ((g.1 : ℝ) * T') ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ((q : ℝ) * T') ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hP1, ← hX1] at hJ
  rw [← hP, ← hX]
  have hP10 : 0 ≤ P1 := by rw [hP1]; exact Real.rpow_nonneg (by positivity) _
  have hX10 : 0 ≤ X1 := by rw [hX1]; exact Real.rpow_nonneg (by positivity) _
  have hPP : P1 ≤ P := by
    rw [hP1, hP]
    exact Real.rpow_le_rpow (by positivity) (by gcongr) hε
  have hXX : X1 ≤ X := by
    rw [hX1, hX]
    exact Real.rpow_le_rpow (by positivity) (by gcongr) (by norm_num)
  have hS0 : 0 ≤ Kc * M ^ 2 + Kc ^ 2 * M + Kc ^ (5 / 4 : ℝ) * X1 * M := by
    have : 0 ≤ Kc ^ (5 / 4 : ℝ) := Real.rpow_nonneg hK0 _
    positivity
  calc ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖Y R χ t g n₁ n₂‖ ^ 2
      ≤ 4 * B ^ 2 * ∑ κ ∈ kg R χ t g, ∑ κ' ∈ kg R χ t g, Jk (dyad M) κ κ' := hY
    _ ≤ 4 * B ^ 2 * ((∫ ξ, kmaj ξ) * (C * P1 * (Kc * M ^ 2 + Kc ^ 2 * M + Kc ^ (5 / 4 : ℝ) * X1 * M))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = 4 * (∫ ξ, kmaj ξ) * C * P1 *
          (B ^ 2 * Kc * M ^ 2 + (B * Kc) ^ 2 * M + B ^ 2 * Kc ^ (5 / 4 : ℝ) * X1 * M) := by ring
    _ ≤ 4 * (∫ ξ, kmaj ξ) * C * P1 * (E * M ^ 2 + (Rc ^ 2) ^ 2 * M + E ^ (3 / 4 : ℝ) * Rc * X1 * M) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) ?_) (by positivity)
        · exact mul_le_mul_of_nonneg_right hBK2 (by positivity)
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hBK 2) hM0.le
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hX10) hM0.le
    _ ≤ 4 * (∫ ξ, kmaj ξ) * C * P * (E * M ^ 2 + Rc ^ 4 * M + E ^ (3 / 4 : ℝ) * Rc * X * M) := by
        have hE34 : 0 ≤ E ^ (3 / 4 : ℝ) := Real.rpow_nonneg hE0 _
        have h1 : E * M ^ 2 + (Rc ^ 2) ^ 2 * M + E ^ (3 / 4 : ℝ) * Rc * X1 * M ≤
            E * M ^ 2 + Rc ^ 4 * M + E ^ (3 / 4 : ℝ) * Rc * X * M := by
          have : E ^ (3 / 4 : ℝ) * Rc * X1 * M ≤ E ^ (3 / 4 : ℝ) * Rc * X * M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXX (by positivity)) hM0.le
          have e : (Rc ^ 2) ^ 2 = Rc ^ 4 := by ring
          rw [e]
          linarith
        have h2 : 0 ≤ E * M ^ 2 + (Rc ^ 2) ^ 2 * M + E ^ (3 / 4 : ℝ) * Rc * X1 * M := by positivity
        calc 4 * (∫ ξ, kmaj ξ) * C * P1 * (E * M ^ 2 + (Rc ^ 2) ^ 2 * M + E ^ (3 / 4 : ℝ) * Rc * X1 * M)
            ≤ 4 * (∫ ξ, kmaj ξ) * C * P * (E * M ^ 2 + (Rc ^ 2) ^ 2 * M + E ^ (3 / 4 : ℝ) * Rc * X1 * M) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPP (by positivity)) h2
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by rw [hP]; positivity)

/-- **Their Lemma 10.7, from `CGLT101`**: for every `ε > 0` there is `C ≥ 0` such that, for `T, M ≥ 1` and points
`|t_i| ≤ T`, `Σ_{n₁,n₂∼M}|R₂(n₁, n₂)|⁴ ≤ C(d(q)(⌊log₂|R|²⌋ + 1))²(qTM)^ε(EM² + |R|⁴M + E^{3/4}|R|(qT)^{1/2}M)`,
with `E` round 659's `energy`. -/
theorem lemma107 (hT : CGLT101) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
      (t : ι → ℝ) (T M : ℝ), 1 ≤ T → 1 ≤ M → (∀ i ∈ R, |t i| ≤ T) →
      ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖R2 R χ t n₁ n₂‖ ^ 4 ≤
        C * ((q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1)) ^ 2 * ((q : ℝ) * T * M) ^ ε *
          ((energy R χ t : ℝ) * M ^ 2 + (R.card : ℝ) ^ 4 * M +
            (energy R χ t : ℝ) ^ (3 / 4 : ℝ) * R.card * ((q : ℝ) * T) ^ (1 / 2 : ℝ) * M) := by
  obtain ⟨C, Q₀, hCQ⟩ := t101At hT hε
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : ℝ, Q₁ = max 1 Q₀ := ⟨_, rfl⟩
  have hQ₁1 : 1 ≤ Q₁ := hQ₁ ▸ le_max_left _ _
  have hQ₀ : Q₀ ≤ Q₁ := hQ₁ ▸ le_max_right _ _
  have hI : 0 ≤ ∫ ξ, kmaj ξ := integral_nonneg kmaj_nonneg
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hA0 : 0 ≤ (4 * Q₁) ^ ε * (4 * Q₁) ^ (1 / 2 : ℝ) := by
    have : 0 ≤ 4 * Q₁ := by linarith
    positivity
  refine ⟨4 * (∫ ξ, kmaj ξ) * max C 0 * ((4 * Q₁) ^ ε * (4 * Q₁) ^ (1 / 2 : ℝ)), by positivity, ?_⟩
  intro q _ ι R χ t T M hT1 hM ht
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  obtain ⟨T', hT'⟩ : ∃ T' : ℝ, T' = Q₁ * (2 * T + 2) := ⟨_, rfl⟩
  have hT'1 : 2 * T + 1 ≤ T' := by rw [hT']; nlinarith
  have hT'0 : 0 ≤ T' := by linarith
  have hQT' : Q₀ ≤ T' := by rw [hT']; nlinarith
  have hTT : T' ≤ 4 * Q₁ * T := by rw [hT']; nlinarith
  have hgb := fun g hg => group_bound hCQ.max hC0 hε.le R χ t hT1 hM ht hT'1 hQT' (g := g) hg
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = energy R χ t := ⟨_, rfl⟩
  obtain ⟨Rc, hRc⟩ : ∃ Rc : ℝ, Rc = R.card := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (grps R χ t).card := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (q.divisors.card : ℝ) * (Nat.log 2 (R.card ^ 2) + 1) := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ P' : ℝ, P' = ((q : ℝ) * T' * M) ^ ε := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ((q : ℝ) * T * M) ^ ε := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X' : ℝ, X' = ((q : ℝ) * T') ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ((q : ℝ) * T) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨Aε, hAε⟩ : ∃ Aε : ℝ, Aε = (4 * Q₁) ^ ε := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (4 * Q₁) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  simp only [← hE, ← hRc, ← hP', ← hX'] at hgb
  rw [← hE, ← hRc, ← hD, ← hP, ← hX, ← hAε, ← hA]
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hR0 : 0 ≤ Rc := by rw [hRc]; positivity
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hGD : G ≤ D := by rw [hG, hD]; exact_mod_cast card_grps_le R χ t
  have hP'0 : 0 ≤ P' := by rw [hP']; exact Real.rpow_nonneg (by positivity) _
  have hX'0 : 0 ≤ X' := by rw [hX']; exact Real.rpow_nonneg (by positivity) _
  have hX0 : 0 ≤ X := by rw [hX]; exact Real.rpow_nonneg (by positivity) _
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg (by positivity) _
  have hAε0 : 0 ≤ Aε := by rw [hAε]; exact Real.rpow_nonneg (by linarith) _
  have hA1 : 1 ≤ A := by rw [hA]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hPP : P' ≤ Aε * P := by
    rw [hP', hAε, hP]
    refine rpow_le_mul_rpow (by positivity) (by linarith) (by positivity) ?_ hε.le
    have : (q : ℝ) * T' * M ≤ (q : ℝ) * (4 * Q₁ * T) * M := by gcongr
    linarith
  have hXX : X' ≤ A * X := by
    rw [hX', hA, hX]
    refine rpow_le_mul_rpow (by positivity) (by linarith) (by positivity) ?_ (by norm_num)
    have : (q : ℝ) * T' ≤ (q : ℝ) * (4 * Q₁ * T) := by gcongr
    linarith
  have hE34 : 0 ≤ E ^ (3 / 4 : ℝ) := Real.rpow_nonneg hE0 _
  set W := E * M ^ 2 + Rc ^ 4 * M + E ^ (3 / 4 : ℝ) * Rc * X' * M with hW
  set W₀ := E * M ^ 2 + Rc ^ 4 * M + E ^ (3 / 4 : ℝ) * Rc * X * M with hW₀
  have hW0 : 0 ≤ W := by positivity
  have hWW : W ≤ A * W₀ := by
    have t1 : E * M ^ 2 ≤ A * (E * M ^ 2) := le_mul_of_one_le_left (by positivity) hA1
    have t2 : Rc ^ 4 * M ≤ A * (Rc ^ 4 * M) := le_mul_of_one_le_left (by positivity) hA1
    have t3 : E ^ (3 / 4 : ℝ) * Rc * X' * M ≤ E ^ (3 / 4 : ℝ) * Rc * (A * X) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXX (by positivity)) hM0
    rw [hW, hW₀]
    linarith
  set c0 := 4 * (∫ ξ, kmaj ξ) * max C 0 with hc0
  have hc00 : 0 ≤ c0 := by positivity
  have hV : c0 * P' * W ≤ c0 * (Aε * P) * (A * W₀) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hPP hc00) hWW hW0 (by positivity)
  have hsum : ∑ g ∈ grps R χ t, ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖Y R χ t g n₁ n₂‖ ^ 2 ≤ G * (c0 * P' * W) := by
    calc _ ≤ ∑ _g ∈ grps R χ t, c0 * P' * W := Finset.sum_le_sum fun g hg => hgb g hg
      _ = G * (c0 * P' * W) := by rw [Finset.sum_const, nsmul_eq_mul, hG]
  have hV0 : 0 ≤ c0 * P' * W := by positivity
  calc ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖R2 R χ t n₁ n₂‖ ^ 4
      ≤ G * ∑ g ∈ grps R χ t, ∑ n₁ ∈ dyad M, ∑ n₂ ∈ dyad M, ‖Y R χ t g n₁ n₂‖ ^ 2 := by
        rw [hG]
        exact sum_R2_four_le R χ t (dyad M)
    _ ≤ G * (G * (c0 * P' * W)) := mul_le_mul_of_nonneg_left hsum hG0
    _ ≤ D * (D * (c0 * (Aε * P) * (A * W₀))) := by
        have hD0 : 0 ≤ D := hG0.trans hGD
        exact mul_le_mul hGD (mul_le_mul hGD hV hV0 hD0) (mul_nonneg hG0 hV0) hD0
    _ = c0 * (Aε * A) * D ^ 2 * P * W₀ := by ring

end LinnikCGLL107

#print axioms LinnikCGLL107.group_le
#print axioms LinnikCGLL107.lemma107
