import EisensteinQuadSupplement

/-! # The companion paper's (6.17): the twist of the rows through sextic reciprocity (round 365)

S5f-2d, in round 363's split of round 360's S5f-2. For the rows `k = u₀tk₀`, the companion paper's (6.17)
writes the twist as "`\Psi_k(n)=\Psi_0(n)\prod_{p\in\mathcal P}\chi_p^{j_p}(n),`" with
"`j_p\equiv v_p(k)+4v_p(g)\pmod6`", and Appendix A.2 expands `φ = χ_n(λ)²Ψ₀` modulo a fixed `L`. This file
proves it in the form round 363's translates use (**`twist_617`**): `φ(x) = χ_x(λ)²Ψ(x)` (round 363's
`phiTw`) is `φ₀(x)·∏_{P ∣ tg}χ_P^{j_P}(x)·∏_{P ∣ k₀}χ_P(x)` with round 341's `jFix` and `chiPow`, where `φ₀` is
periodic modulo `72`, depends on `k₀` only modulo `4`, has modulus at most `1` and vanishes at `0`.

* **The part prime to `6`** (`absNorm_span_δ3`, **`exists_S_decomp`**): every `z ≠ 0` is `ε·δ₃^a·2^b·z'` with
  `ε` a unit and `z'` primary and odd, by induction on the norm.
* **Sextic reciprocity for coprime primary elements** (**`sym6_recip_gen`**): `(a/b)₆ = (a/b)₂(b/a)₂·(b/a)₆`,
  from round 290's cubic reciprocity and round 364's `(a/𝔞)₆ = (a/𝔞)₂σ((a/𝔞)₃)²`.
* **The reciprocity factor** (`Rn`, `norm_Rn_le`, **`Rn_eq`**, `Rn_congr`): `R(k, x) = 2φ(kx)/(φ(k)φ(x))`
  normalized to modulus at most `1`; at coprime primary `k, x` of norm prime to `6` it is `(x/k)₂(k/x)₂`
  (round 364's `sym2_recip_gen`), and it depends on `k` and `x` only modulo `4`.
* **The multiplicities** (`count_S`, `primeSet_S`, `prod_primeSet_count`, **`prod_jFix`**): the primes
  prime to `6` of `z` and their multiplicities are those of `z'`; the product of `χ_P(x)` over them with
  multiplicity is `(x/z')₆`; and at `x` in no prime of `tg`,
  `∏_{P ∣ tg}χ_P^{j_P}(x) = (x/t')₆(x/g')₆⁴`.
* **(6.17)** (`key_617`, **`twist_617`**): with `t = ε_tδ₃^{a}2^{b}t'` and `g = ε_gδ₃^{c}2^{d}g'`,
  `φ₀(x) = χ_x(λ)²·ξ(x)·(u₀ε_tδ₃^a2^b/x)₆·(ε_gδ₃^c2^d/x)₆⁴·R(t'k₀, x)` on primary `x` of norm prime to `6`.
  At `x` prime to `t'g'k₀`, sextic reciprocity turns `(t'/x)₆(k₀/x)₆(g'/x)₆⁴` into
  `R(t'k₀, x)·(x/t')₆(x/g')₆⁴(x/k₀)₆` (the fourth power of `R(g', x) = ±1` is `1`); at any other `x` a
  common prime makes both sides vanish. The periodicity of `φ₀` is round 362's and round 364's.
-/

open NumberField Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate

noncomputable section

namespace Eis

theorem cj_δ3 : cj δ3 = -δ3 := by
  unfold δ3
  rw [map_add, map_mul, map_one, map_ofNat, cj_ω]
  linear_combination 2 * ω_sq_add

theorem absNorm_span_δ3 : absNorm (span {δ3}) = 3 := by
  have h := mul_cj_eq_absNorm δ3
  rw [cj_δ3, show δ3 * -δ3 = -(δ3 ^ 2) by ring, δ3_sq, neg_neg] at h
  exact_mod_cast h.symm

theorem absNorm_lt_of_mul {c w : 𝓞 K} (hw : w ≠ 0) (hc : 1 < absNorm (span {c})) :
    absNorm (span {w}) < absNorm (span {c * w}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  have : 0 < absNorm (span {w}) := Nat.pos_of_ne_zero (by
    rw [Ne, absNorm_eq_zero_iff, span_singleton_eq_bot]; exact hw)
  nlinarith

/-- **The part prime to `6`**: every `z ≠ 0` is `ε·δ₃^a·2^b·z'` with `ε` a unit and `z'` primary and odd. -/
theorem exists_S_decomp : ∀ (N : ℕ) (z : 𝓞 K), absNorm (span {z}) = N → z ≠ 0 →
    ∃ (ε : (𝓞 K)ˣ) (a b : ℕ) (z' : 𝓞 K), Primary z' ∧ ¬ (2 : 𝓞 K) ∣ z' ∧
      z = ε * δ3 ^ a * 2 ^ b * z' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z hN hz
    by_cases h3 : δ3 ∣ z
    · obtain ⟨w, rfl⟩ := h3
      have hw : w ≠ 0 := right_ne_zero_of_mul hz
      obtain ⟨ε, a, b, z', h1, h2, h3⟩ := ih _ (hN ▸ absNorm_lt_of_mul hw (by rw [absNorm_span_δ3]; norm_num))
        w rfl hw
      exact ⟨ε, a + 1, b, z', h1, h2, by rw [h3]; ring⟩
    by_cases h2 : (2 : 𝓞 K) ∣ z
    · obtain ⟨w, rfl⟩ := h2
      have hw : w ≠ 0 := right_ne_zero_of_mul hz
      obtain ⟨ε, a, b, z', h1, h2, h3⟩ := ih _ (hN ▸ absNorm_lt_of_mul hw (by rw [absNorm_span_two]; norm_num))
        w rfl hw
      exact ⟨ε, a, b + 1, z', h1, h2, by rw [h3]; ring⟩
    have hlam : ¬ (ω - 1 : 𝓞 K) ∣ z := fun h => h3 (by
      obtain ⟨c, hc⟩ := h
      exact ⟨-ω ^ 2 * c, by rw [hc]; unfold δ3; linear_combination c * ω_sq_add + 2 * c * ω_cube⟩)
    obtain ⟨v, hv⟩ := exists_primary hlam
    refine ⟨v⁻¹, 0, 0, (v : 𝓞 K) * z, hv, fun h => h2 ?_, ?_⟩
    · obtain ⟨c, hc⟩ := h
      exact ⟨((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * c, by
        rw [← mul_assoc, mul_comm (2 : 𝓞 K), mul_assoc, ← hc, ← mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_mul]⟩
    · rw [pow_zero, pow_zero, mul_one, mul_one, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]

/-- **Sextic reciprocity for coprime primary elements of norm prime to `6`**:
`(a/b)₆ = (a/b)₂(b/a)₂·(b/a)₆`, from round 290's cubic reciprocity and `(a/𝔞)₆ = (a/𝔞)₂σ((a/𝔞)₃)²`. -/
theorem sym6_recip_gen {a b : 𝓞 K} (ha : Primary a) (hb : Primary b)
    (ha6 : (absNorm (span {a})).Coprime 6) (hb6 : (absNorm (span {b})).Coprime 6)
    (hab : IsCoprime a b) :
    sym6 a (span {b}) = sym2 a (span {b}) * sym2 b (span {a}) * sym6 b (span {a}) := by
  have h1 := sym6_eq_sym2_mul hb6 a
  have h2 := sym6_eq_sym2_mul ha6 b
  have hc := cub_recip ha hb hab
  have hs := sym2_sq_eq_one ha6 hab.symm
  rw [h1, h2, hc]
  linear_combination (-(sym2 a (span {b}) * σO (cub b (span {a})) ^ 2)) * hs

/-! ### The reciprocity factor -/

/-- The reciprocity factor `R(k, x) = 2φ(kx)/(φ(k)φ(x))`, normalized to modulus at most `1`. -/
def Rn (k x : 𝓞 K) : ℂ :=
  2 * gq4 (k * x) / (gq4 k * gq4 x) / ((‖2 * gq4 (k * x) / (gq4 k * gq4 x)‖ : ℝ) : ℂ)

theorem norm_Rn_le (k x : 𝓞 K) : ‖Rn k x‖ ≤ 1 := by
  unfold Rn
  set z := 2 * gq4 (k * x) / (gq4 k * gq4 x)
  by_cases hz : z = 0
  · rw [hz]; simp
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.2 hz)]

theorem norm_sym2_of_coprime {a b : 𝓞 K} (hb : (absNorm (span {b})).Coprime 6) (h : IsCoprime a b) :
    ‖sym2 a (span {b})‖ = 1 := by
  have h2 := congrArg norm (sym2_sq_eq_one hb h)
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

/-- At coprime primary `k, x` of norm prime to `6`, `R(k, x) = (x/k)₂(k/x)₂`. -/
theorem Rn_eq {k x : 𝓞 K} (hk : Primary k) (hx : Primary x)
    (hk6 : (absNorm (span {k})).Coprime 6) (hx6 : (absNorm (span {x})).Coprime 6)
    (hcop : IsCoprime k x) : Rn k x = sym2 x (span {k}) * sym2 k (span {x}) := by
  have hrec := sym2_recip_gen hk hx hk6 hx6 hcop
  have hne := mul_ne_zero (gq4_ne_zero_of_primary hk hk6) (gq4_ne_zero_of_primary hx hx6)
  have e : 2 * gq4 (k * x) / (gq4 k * gq4 x) = sym2 x (span {k}) * sym2 k (span {x}) := by
    rw [div_eq_iff hne]; exact hrec.symm
  unfold Rn
  rw [e, norm_mul, norm_sym2_of_coprime hk6 hcop.symm, norm_sym2_of_coprime hx6 hcop]
  simp

theorem Rn_congr {k k' x x' : 𝓞 K} (hk : (4 : 𝓞 K) ∣ k - k') (hx : (4 : 𝓞 K) ∣ x - x') :
    Rn k x = Rn k' x' := by
  have e1 : gq4 k = gq4 k' := gq4_congr (mk_four_eq hk)
  have e2 : gq4 x = gq4 x' := gq4_congr (mk_four_eq hx)
  have e3 : gq4 (k * x) = gq4 (k' * x') := by
    refine gq4_congr (mk_four_eq ?_)
    obtain ⟨a, ha⟩ := hk
    obtain ⟨b, hb⟩ := hx
    exact ⟨a * x + k' * b, by linear_combination x * ha + k' * hb⟩
  unfold Rn; rw [e1, e2, e3]

theorem span_ne_bot {z : 𝓞 K} (hz : z ≠ 0) : span {z} ≠ ⊥ := by
  rwa [Ne, span_singleton_eq_bot]

theorem count_nf_mul (P : Ideal (𝓞 K)) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    (normalizedFactors (I * J)).count P = (normalizedFactors I).count P + (normalizedFactors J).count P := by
  classical
  rw [normalizedFactors_mul hI hJ, Multiset.count_add]

theorem count_nf_eq_zero_of_mem {P : Pr} {c : 𝓞 K} (hc : c ∈ P.1 → (6 : 𝓞 K) ∈ P.1) (z : 𝓞 K)
    (hz : span {z} = span {c}) : (normalizedFactors (span {z})).count P.1 = 0 := by
  classical
  rw [Multiset.count_eq_zero]
  intro hP
  apply P.2.2
  apply hc
  have := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
  rw [hz] at this
  exact this (Ideal.mem_span_singleton_self c)

theorem six_of_δ3 {P : Ideal (𝓞 K)} (h : δ3 ∈ P) : (6 : 𝓞 K) ∈ P := by
  have h3 : (3 : 𝓞 K) ∈ P := by
    have : (3 : 𝓞 K) = -(δ3 * δ3) := by rw [← sq, δ3_sq]; ring
    rw [this]; exact P.neg_mem (P.mul_mem_left _ h)
  rw [show (6 : 𝓞 K) = 2 * 3 by norm_num]; exact P.mul_mem_left _ h3

theorem six_of_two {P : Ideal (𝓞 K)} (h : (2 : 𝓞 K) ∈ P) : (6 : 𝓞 K) ∈ P := by
  rw [show (6 : 𝓞 K) = 3 * 2 by norm_num]; exact P.mul_mem_left _ h

theorem count_nf_pow (P : Ideal (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (n : ℕ) :
    (normalizedFactors (I ^ n)).count P = n * (normalizedFactors I).count P := by
  classical
  induction n with
  | zero => rw [pow_zero, normalizedFactors_one, Multiset.count_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ, count_nf_mul P (pow_ne_zero n hI) hI, ih]; ring

/-- **The multiplicities prime to `6` are those of the part prime to `6`.** -/
theorem count_S (P : Pr) (ε : (𝓞 K)ˣ) (a b : ℕ) {z' : 𝓞 K} (hz' : z' ≠ 0) :
    (normalizedFactors (span {(ε : 𝓞 K) * δ3 ^ a * 2 ^ b * z'})).count P.1 =
      (normalizedFactors (span {z'})).count P.1 := by
  have hδ : δ3 ≠ 0 := δ3_ne_zero
  have e : span {(ε : 𝓞 K) * δ3 ^ a * 2 ^ b * z'} = span {δ3} ^ a * span {(2 : 𝓞 K)} ^ b * span {z'} := by
    rw [show (ε : 𝓞 K) * δ3 ^ a * 2 ^ b * z' = (ε : 𝓞 K) * (δ3 ^ a * 2 ^ b * z') by ring,
      Ideal.span_singleton_mul_left_unit ε.isUnit, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
  have h2 : (2 : 𝓞 K) ≠ 0 := two_ne_zero
  rw [e, count_nf_mul _ (mul_ne_zero (pow_ne_zero _ (span_ne_bot hδ)) (pow_ne_zero _ (span_ne_bot h2)))
    (span_ne_bot hz'), count_nf_mul _ (pow_ne_zero _ (span_ne_bot hδ)) (pow_ne_zero _ (span_ne_bot h2)),
    count_nf_pow _ (span_ne_bot hδ), count_nf_pow _ (span_ne_bot h2),
    count_nf_eq_zero_of_mem six_of_δ3 δ3 rfl, count_nf_eq_zero_of_mem six_of_two 2 rfl]
  ring

theorem primeSet_S (ε : (𝓞 K)ˣ) (a b : ℕ) {z' : 𝓞 K} (hz' : z' ≠ 0) :
    primeSet (span {(ε : 𝓞 K) * δ3 ^ a * 2 ^ b * z'}) = primeSet (span {z'}) := by
  classical
  ext P
  rw [mem_primeSet, mem_primeSet, ← Multiset.count_pos, ← Multiset.count_pos, count_S P ε a b hz']

/-- **The product over the primes with multiplicity is the sextic symbol**, for `N(𝔞)` prime to `6`. -/
theorem prod_primeSet_count {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (x : 𝓞 K) :
    ∏ P ∈ primeSet I, chiP P.1 x ^ (normalizedFactors I).count P.1 = sym6 x I := by
  classical
  have hmap : (primeSet I).map ⟨Subtype.val, Subtype.val_injective⟩ = (normalizedFactors I).toFinset := by
    ext Q
    rw [Finset.mem_map, Multiset.mem_toFinset]
    constructor
    · rintro ⟨P, hP, rfl⟩; exact mem_primeSet.1 hP
    · intro hQ
      exact ⟨⟨Q, isMaximal_of_factor hQ, six_not_mem_of_factor hI hQ⟩, mem_primeSet.2 hQ, rfl⟩
  unfold sym6
  rw [Finset.prod_multiset_map_count, ← hmap, Finset.prod_map]
  rfl

/-- **The product of `jFix`** splits into the two factors, at `x` in no prime of `tg`. -/
theorem prod_jFix {t g x : 𝓞 K} (ht : t ≠ 0) (hg : g ≠ 0)
    (hx : ∀ P ∈ primeSet (span {t * g}), x ∉ P.1) :
    ∏ P ∈ primeSet (span {t * g}), chiPow P.1 (jFix t g P) x =
      (∏ P ∈ primeSet (span {t}), chiP P.1 x ^ (normalizedFactors (span {t})).count P.1) *
        (∏ P ∈ primeSet (span {g}), chiP P.1 x ^ (normalizedFactors (span {g})).count P.1) ^ 4 := by
  classical
  have htg : span {t * g} = span {t} * span {g} := (Ideal.span_singleton_mul_span_singleton t g).symm
  have hsub : ∀ {I J : Ideal (𝓞 K)}, I ≠ ⊥ → J ≠ ⊥ → primeSet I ⊆ primeSet (I * J) := by
    intro I J hI hJ P hP
    rw [mem_primeSet] at hP ⊢
    rw [normalizedFactors_mul hI hJ]; exact Multiset.mem_add.2 (Or.inl hP)
  have hsub' : ∀ {I J : Ideal (𝓞 K)}, I ≠ ⊥ → J ≠ ⊥ → primeSet J ⊆ primeSet (I * J) := by
    intro I J hI hJ P hP
    rw [mem_primeSet] at hP ⊢
    rw [normalizedFactors_mul hI hJ]; exact Multiset.mem_add.2 (Or.inr hP)
  have ext1 : ∏ P ∈ primeSet (span {t}), chiP P.1 x ^ (normalizedFactors (span {t})).count P.1 =
      ∏ P ∈ primeSet (span {t * g}), chiP P.1 x ^ (normalizedFactors (span {t})).count P.1 := by
    rw [htg]
    refine Finset.prod_subset (hsub (span_ne_bot ht) (span_ne_bot hg)) fun P _ hP => ?_
    rw [mem_primeSet, ← Multiset.count_eq_zero] at hP
    rw [hP, pow_zero]
  have ext2 : ∏ P ∈ primeSet (span {g}), chiP P.1 x ^ (normalizedFactors (span {g})).count P.1 =
      ∏ P ∈ primeSet (span {t * g}), chiP P.1 x ^ (normalizedFactors (span {g})).count P.1 := by
    rw [htg]
    refine Finset.prod_subset (hsub' (span_ne_bot ht) (span_ne_bot hg)) fun P _ hP => ?_
    rw [mem_primeSet, ← Multiset.count_eq_zero] at hP
    rw [hP, pow_zero]
  rw [ext1, ext2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hxP := hx P hP
  unfold chiPow jFix
  rw [ite_eq_right hxP]
  have h6 : chiP P.1 x ^ 6 = 1 := by
    rw [chiP_pow_six P.2.1 P.2.2, ite_eq_right hxP]
  set ct := (normalizedFactors (span {t})).count P.1
  set cg := (normalizedFactors (span {g})).count P.1
  rw [← pow_mul, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (ct + cg * 4) 6, pow_add, pow_mul, h6, one_pow, mul_one]
  congr 1
  omega

/-- A primary element is of norm prime to `6` iff it is odd. -/
theorem coprime6_iff_odd {x : 𝓞 K} (hx : Primary x) :
    (absNorm (span {x})).Coprime 6 ↔ ¬ (2 : 𝓞 K) ∣ x := by
  constructor
  · intro h6 h2
    obtain ⟨c, rfl⟩ := h2
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_span_two] at h6
    have := Nat.Coprime.coprime_dvd_left (dvd_mul_right 4 _) h6
    norm_num at this
  · exact coprime6_of_primary_two hx

theorem primary_add_iff {x y : 𝓞 K} (h : (3 : 𝓞 K) ∣ y) : Primary (x + y) ↔ Primary x := by
  unfold Primary
  constructor
  · intro h'; have := dvd_sub h' h; rwa [show x + y - 1 - y = x - 1 by ring] at this
  · intro h'; have := dvd_add h' h; rwa [show x - 1 + y = x + y - 1 by ring] at this

theorem mem_nf_span_of_mem {x : 𝓞 K} (hx : x ≠ 0) {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (h : x ∈ P) :
    P ∈ normalizedFactors (span {x}) := by
  refine mem_nf_of_dvd (span_ne_bot hx) (Ideal.prime_of_isPrime (ne_bot P) hP.isPrime) ?_
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]; exact h

theorem isCoprime_unit_right (x : 𝓞 K) (u : (𝓞 K)ˣ) : IsCoprime x (u : 𝓞 K) := by
  have := (isCoprime_mul_unit_left_left u.isUnit 1 x).2 isCoprime_one_left
  rw [mul_one] at this
  exact this.symm

theorem isCoprime_S {x : 𝓞 K} (hx : Primary x) (hx6 : (absNorm (span {x})).Coprime 6)
    (ε : (𝓞 K)ˣ) (a b : ℕ) {z' : 𝓞 K} (hz : IsCoprime x z') :
    IsCoprime x ((ε : 𝓞 K) * δ3 ^ a * 2 ^ b * z') :=
  (((isCoprime_unit_right x ε).mul_right ((isCoprime_δ3 hx).symm.pow_right)).mul_right
    ((isCoprime_two_of_odd (Nat.Coprime.coprime_dvd_right (by norm_num) hx6)).pow_right)).mul_right hz

theorem mem_S_of_mem {P : Ideal (𝓞 K)} (ε : (𝓞 K)ˣ) (a b : ℕ) {z' : 𝓞 K} (h : z' ∈ P) :
    (ε : 𝓞 K) * δ3 ^ a * 2 ^ b * z' ∈ P := P.mul_mem_left _ h

/-- **The key identity of (6.17)**: `(t'/x)₆(k₀/x)₆(g'/x)₆⁴ = R(t'k₀, x)·∏_{P ∣ tg}χ_P^{j_P}(x)·(x/k₀)₆`. -/
theorem key_617 {εt εg : (𝓞 K)ˣ} {at' bt ag bg : ℕ} {t' g' k₀ x : 𝓞 K}
    (ht1 : Primary t') (ht6 : (absNorm (span {t'})).Coprime 6) (hg1 : Primary g')
    (hg6 : (absNorm (span {g'})).Coprime 6) (hk₀ : Primary k₀)
    (hk₀6 : (absNorm (span {k₀})).Coprime 6) (hxp : Primary x)
    (hx6 : (absNorm (span {x})).Coprime 6) :
    sym6 t' (span {x}) * sym6 k₀ (span {x}) * sym6 g' (span {x}) ^ 4 =
      Rn (t' * k₀) x * (∏ P ∈ primeSet (span {(εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t' *
          ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g')}), chiPow P.1
          (jFix ((εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t') ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g') P) x) *
        sym6 x (span {k₀}) := by
  classical
  have hx0 := primary_ne_zero hxp
  have ht'0 := primary_ne_zero ht1
  have hg'0 := primary_ne_zero hg1
  have hk0 := primary_ne_zero hk₀
  have hS0 : ∀ (ε : (𝓞 K)ˣ) (a b : ℕ), (ε : 𝓞 K) * δ3 ^ a * 2 ^ b ≠ 0 := fun ε a b =>
    mul_ne_zero (mul_ne_zero ε.ne_zero (pow_ne_zero _ δ3_ne_zero)) (pow_ne_zero _ two_ne_zero)
  have ht0 : (εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t' ≠ 0 := mul_ne_zero (hS0 _ _ _) ht'0
  have hg0 : (εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g' ≠ 0 := mul_ne_zero (hS0 _ _ _) hg'0
  by_cases hc : IsCoprime x (t' * g' * k₀)
  · have hxt : IsCoprime x t' := hc.of_mul_right_left.of_mul_right_left
    have hxg : IsCoprime x g' := hc.of_mul_right_left.of_mul_right_right
    have hxk : IsCoprime x k₀ := hc.of_mul_right_right
    have r1 := sym6_recip_gen ht1 hxp ht6 hx6 hxt.symm
    have r2 := sym6_recip_gen hk₀ hxp hk₀6 hx6 hxk.symm
    have r3 := sym6_recip_gen hg1 hxp hg6 hx6 hxg.symm
    have htk6 : (absNorm (span {t' * k₀})).Coprime 6 := by
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
      exact Nat.coprime_mul_iff_left.2 ⟨ht6, hk₀6⟩
    have hRn := Rn_eq (ht1.mul hk₀) hxp htk6 hx6 (hxt.symm.mul_left hxk.symm)
    have e1 : sym2 x (span {t' * k₀}) = sym2 x (span {t'}) * sym2 x (span {k₀}) := by
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact sym2_mul_right x (span_ne_zero_of_coprime6 ht6) (span_ne_zero_of_coprime6 hk₀6)
    have e2 : sym2 (t' * k₀) (span {x}) = sym2 t' (span {x}) * sym2 k₀ (span {x}) :=
      sym2_mul_left _ _ _
    have sq1 : sym2 g' (span {x}) ^ 2 = 1 := sym2_sq_eq_one hx6 hxg.symm
    have sq2 : sym2 x (span {g'}) ^ 2 = 1 := sym2_sq_eq_one hg6 hxg
    have hnot : ∀ P ∈ primeSet (span {(εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t' *
        ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g')}), x ∉ P.1 := fun P hP =>
      not_mem_factor_of_isCoprime ((isCoprime_S hxp hx6 εt at' bt hxt).mul_right
        (isCoprime_S hxp hx6 εg ag bg hxg)) (mem_primeSet.1 hP)
    have hprod : ∏ P ∈ primeSet (span {(εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t' *
        ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g')}), chiPow P.1
        (jFix ((εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t') ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g') P) x =
        sym6 x (span {t'}) * sym6 x (span {g'}) ^ 4 := by
      rw [prod_jFix ht0 hg0 hnot, primeSet_S εt at' bt ht'0, primeSet_S εg ag bg hg'0,
        ← prod_primeSet_count ht6, ← prod_primeSet_count hg6]
      congr 1
      · exact Finset.prod_congr rfl fun P _ => by rw [count_S P εt at' bt ht'0]
      · congr 1
        exact Finset.prod_congr rfl fun P _ => by rw [count_S P εg ag bg hg'0]
    rw [r1, r2, r3, hRn, e1, e2, hprod]
    set a := sym2 g' (span {x})
    set b := sym2 x (span {g'})
    linear_combination (sym2 t' (span {x}) * sym2 x (span {t'}) * sym6 x (span {t'}) *
      (sym2 k₀ (span {x}) * sym2 x (span {k₀}) * sym6 x (span {k₀})) * sym6 x (span {g'}) ^ 4) *
      ((a ^ 2 + 1) * b ^ 4 * sq1 + (b ^ 2 + 1) * sq2)
  · rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq] at hc
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hc
    have hxP : x ∈ P := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
    have hyP : t' * g' * k₀ ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hPnf : P ∈ normalizedFactors (span {x}) := mem_nf_span_of_mem hx0 hxP
    have hP6 : (6 : 𝓞 K) ∉ P := six_not_mem_of_factor hx6 hPnf
    have htg : ∀ h : ((εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t' *
        ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g')) ∈ P,
        ∏ Q ∈ primeSet (span {(εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t' *
          ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g')}), chiPow Q.1
          (jFix ((εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t') ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g') Q) x = 0 := by
      intro h
      refine Finset.prod_eq_zero (i := ⟨P, hPmax, hP6⟩)
        (mem_primeSet.2 (mem_nf_span_of_mem (mul_ne_zero ht0 hg0) h)) ?_
      unfold chiPow; rw [ite_eq_left hxP]
    rcases hPmax.isPrime.mem_or_mem hyP with h | hk
    · rcases hPmax.isPrime.mem_or_mem h with ht | hg
      · rw [sym6_eq_zero_of_mem hPnf ht, htg (P.mul_mem_right _ (mem_S_of_mem εt at' bt ht))]; ring
      · rw [sym6_eq_zero_of_mem hPnf hg, htg (P.mul_mem_left _ (mem_S_of_mem εg ag bg hg))]; ring
    · have hPk : P ∈ normalizedFactors (span {k₀}) := mem_nf_span_of_mem hk0 hk
      rw [sym6_eq_zero_of_mem hPnf hk, sym6_eq_zero_of_mem hPk hxP]; ring

/-- **The companion paper's (6.17)**: for the twist `Ψ = Ψ_{u₀tk₀, g}` of the rows, `φ(x) = χ_x(λ)²Ψ(x)`
is `φ₀(x)·∏_{P ∣ tg}χ_P^{j_P}(x)·∏_{P ∣ k₀}χ_P(x)` with `j_P = jFix`, where `φ₀` is periodic modulo `72`,
depends on `k₀` only modulo `4`, has modulus at most `1`, and vanishes at `0`. -/
theorem twist_617 (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (u₀ : (𝓞 K)ˣ) {t g : 𝓞 K}
    (ht : t ≠ 0) (hg : g ≠ 0) :
    ∃ φ₀ : 𝓞 K → 𝓞 K → ℂ,
      (∀ k x u, φ₀ k (x + 72 * u) = φ₀ k x) ∧
      (∀ k k' x, (4 : 𝓞 K) ∣ k - k' → φ₀ k x = φ₀ k' x) ∧
      (∀ k x, ‖φ₀ k x‖ ≤ 1) ∧
      (∀ k, φ₀ k 0 = 0) ∧
      ∀ k₀ : 𝓞 K, Primary k₀ → Squarefree (span {k₀}) → (absNorm (span {k₀})).Coprime 6 →
        IsCoprime k₀ (t * g) → ∀ x : 𝓞 K,
        phiTw (twistPsi ξ (u₀ * t * k₀) g) x =
          φ₀ k₀ x * (∏ P ∈ primeSet (span {t * g}), chiPow P.1 (jFix t g P) x) *
            ∏ P ∈ primeSet (span {k₀}), chiP P.1 x := by
  classical
  obtain ⟨εt, at', bt, t', ht1, ht2, rfl⟩ := exists_S_decomp _ t rfl ht
  obtain ⟨εg, ag, bg, g', hg1, hg2, rfl⟩ := exists_S_decomp _ g rfl hg
  have ht6 := coprime6_of_primary_two ht1 ht2
  have hg6 := coprime6_of_primary_two hg1 hg2
  obtain ⟨St, hSt⟩ : ∃ St : 𝓞 K, St = ((u₀ * εt : (𝓞 K)ˣ) : 𝓞 K) * δ3 ^ at' * 2 ^ bt := ⟨_, rfl⟩
  obtain ⟨Sg, hSg⟩ : ∃ Sg : 𝓞 K, Sg = (εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg := ⟨_, rfl⟩
  refine ⟨fun k x => if Primary x ∧ (absNorm (span {x})).Coprime 6 then
    sym6 δ3 (span {x}) ^ 2 * (ξ (Ideal.Quotient.mk _ x) * sym6 St (span {x}) *
      sym6 Sg (span {x}) ^ 4 * Rn (t' * k) x) else 0, ?_, ?_, ?_, ?_, ?_⟩
  · -- periodic modulo 72
    intro k x u
    beta_reduce
    have h3 : (3 : 𝓞 K) ∣ 72 * u := ⟨24 * u, by ring⟩
    have hP := primary_add_iff (x := x) h3
    by_cases hx : Primary x
    · have hx' : Primary (x + 72 * u) := hP.2 hx
      have h2 : (2 : 𝓞 K) ∣ x + 72 * u ↔ (2 : 𝓞 K) ∣ x := by
        constructor
        · intro h; have := dvd_sub h (⟨36 * u, by ring⟩ : (2 : 𝓞 K) ∣ 72 * u); rwa [add_sub_cancel_right] at this
        · intro h; exact dvd_add h ⟨36 * u, by ring⟩
      by_cases hx6 : (absNorm (span {x})).Coprime 6
      · have hx6' : (absNorm (span {x + 72 * u})).Coprime 6 :=
          (coprime6_iff_odd hx').2 (fun h => (coprime6_iff_odd hx).1 hx6 (h2.1 h))
        rw [ite_eq_left ⟨hx', hx6'⟩, ite_eq_left ⟨hx, hx6⟩]
        have hd : (72 : 𝓞 K) ∣ x + 72 * u - x := ⟨u, by ring⟩
        have h9 : (9 : 𝓞 K) ∣ x + 72 * u - x := ⟨8 * u, by ring⟩
        have h4 : (4 : 𝓞 K) ∣ x + 72 * u - x := ⟨18 * u, by ring⟩
        rw [sym6_sq_δ3_congr hx' hx hx6' hx6 h9, mk_four_eq h4,
          hSt, sym6_S_congr (u₀ * εt) at' bt hx' hx hx6' hx6 hd,
          hSg, sym6_S_congr εg ag bg hx' hx hx6' hx6 hd, Rn_congr (by rw [sub_self]; exact dvd_zero _) h4]
      · have hx6' : ¬ (absNorm (span {x + 72 * u})).Coprime 6 := fun h =>
          hx6 ((coprime6_iff_odd hx).2 fun h' => (coprime6_iff_odd hx').1 h (h2.2 h'))
        rw [ite_eq_right (fun h => hx6' h.2), ite_eq_right (fun h => hx6 h.2)]
    · have hx' : ¬ Primary (x + 72 * u) := fun h => hx (hP.1 h)
      rw [ite_eq_right (fun h => hx' h.1), ite_eq_right (fun h => hx h.1)]
  · -- depends on k only modulo 4
    intro k k' x hk
    simp only
    split_ifs
    · rw [Rn_congr (k := t' * k) (k' := t' * k') (x := x) (x' := x)
        (by obtain ⟨c, hc⟩ := hk; exact ⟨t' * c, by rw [← mul_sub, hc]; ring⟩) (by simp)]
    · rfl
  · -- modulus at most 1
    intro k x
    simp only
    split_ifs
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 := norm_sym6_le δ3 (span {x})
      have h2 := norm_xi_le ξ (Ideal.Quotient.mk _ x)
      have h3 := norm_sym6_le St (span {x})
      have h4 := norm_sym6_le Sg (span {x})
      have h5 := norm_Rn_le (t' * k) x
      calc ‖sym6 δ3 (span {x})‖ ^ 2 * (‖ξ (Ideal.Quotient.mk _ x)‖ * ‖sym6 St (span {x})‖ *
            ‖sym6 Sg (span {x})‖ ^ 4 * ‖Rn (t' * k) x‖) ≤ 1 ^ 2 * (1 * 1 * 1 ^ 4 * 1) := by gcongr
        _ = 1 := by norm_num
    · simp
  · -- vanishes at 0
    intro k
    simp only
    rw [ite_eq_right fun h => primary_ne_zero h.1 rfl]
  · intro k₀ hk₀ hk₀sq hk₀6 hk₀c x
    beta_reduce
    by_cases hx : Primary x ∧ (absNorm (span {x})).Coprime 6
    swap
    · unfold phiTw; rw [ite_eq_right hx, ite_eq_right hx, zero_mul, zero_mul]
    obtain ⟨hxp, hx6⟩ := hx
    have hx0 := primary_ne_zero hxp
    have ht'0 := primary_ne_zero ht1
    have hg'0 := primary_ne_zero hg1
    have hk0 := primary_ne_zero hk₀
    have hu : ((u₀ : 𝓞 K)) * ((εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t') * k₀ = St * (t' * k₀) := by
      rw [hSt, Units.val_mul]; ring
    unfold phiTw twistPsi
    rw [ite_eq_left ⟨hxp, hx6⟩, ite_eq_left hx6, ite_eq_left ⟨hxp, hx6⟩, pgen_eq hxp, hu,
      sym6_mul_left St (t' * k₀), sym6_mul_left t' k₀, sym6_mul_left ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg) g']
    -- the product over the primes of `k₀`
    have hk₀prod : ∏ P ∈ primeSet (span {k₀}), chiP P.1 x = sym6 x (span {k₀}) := by
      unfold sym6
      rw [normalizedFactors_eq_map hk₀6 hk₀sq, Multiset.map_map, Finset.prod_eq_multiset_prod]
      rfl
    -- the key identity
    have key : sym6 t' (span {x}) * sym6 k₀ (span {x}) * sym6 g' (span {x}) ^ 4 =
        Rn (t' * k₀) x * (∏ P ∈ primeSet (span {(εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t' *
          ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g')}), chiPow P.1
          (jFix ((εt : 𝓞 K) * δ3 ^ at' * 2 ^ bt * t') ((εg : 𝓞 K) * δ3 ^ ag * 2 ^ bg * g') P) x) *
          ∏ P ∈ primeSet (span {k₀}), chiP P.1 x := by
      rw [hk₀prod]
      exact key_617 ht1 ht6 hg1 hg6 hk₀ hk₀6 hxp hx6
    rw [hk₀prod] at key ⊢
    rw [← hSg] at key ⊢
    linear_combination (sym6 δ3 (span {x}) ^ 2 * ξ (Ideal.Quotient.mk _ x) * sym6 St (span {x}) *
      sym6 Sg (span {x}) ^ 4) * key

end Eis

end

#print axioms Eis.cj_δ3
#print axioms Eis.absNorm_span_δ3
#print axioms Eis.absNorm_lt_of_mul
#print axioms Eis.exists_S_decomp
#print axioms Eis.sym6_recip_gen
#print axioms Eis.norm_Rn_le
#print axioms Eis.norm_sym2_of_coprime
#print axioms Eis.Rn_eq
#print axioms Eis.Rn_congr
#print axioms Eis.span_ne_bot
#print axioms Eis.count_nf_mul
#print axioms Eis.count_nf_eq_zero_of_mem
#print axioms Eis.six_of_δ3
#print axioms Eis.six_of_two
#print axioms Eis.count_nf_pow
#print axioms Eis.count_S
#print axioms Eis.primeSet_S
#print axioms Eis.prod_primeSet_count
#print axioms Eis.prod_jFix
#print axioms Eis.coprime6_iff_odd
#print axioms Eis.primary_add_iff
#print axioms Eis.mem_nf_span_of_mem
#print axioms Eis.isCoprime_unit_right
#print axioms Eis.isCoprime_S
#print axioms Eis.mem_S_of_mem
#print axioms Eis.key_617
#print axioms Eis.twist_617
