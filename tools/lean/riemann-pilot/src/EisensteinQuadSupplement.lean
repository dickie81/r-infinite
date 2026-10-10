import EisensteinQuadSieveSquares
import EisensteinSupplement
import KubotaTranslates

/-! # Quadratic reciprocity beyond squarefree moduli, and the supplementary laws at `2`, `λ` and the units (round 364)

S5f-2c, in round 363's split of round 360's S5f-2. The fixed factor `Ψ₀` of the companion paper's (6.17)
contains the sextic symbols of the units, of `λ` and of `2` at `n`, and the reciprocity factor `R(n, k)`
at every primary `n`, squarefree or not. This file proves that these depend only on `n` modulo a fixed
modulus, from quadratic and cubic reciprocity and Mathlib's evaluation of the quadratic character of a
finite field at `−1` and `2`.

* **Quadratic reciprocity for coprime primary elements of norm prime to `6`** (**`sym2_recip_gen`**):
  `(x/k)₂(k/x)₂·φ(k)φ(x) = 2φ(kx)` with round 344's `φ` (`gq4`), extending round 344's `sym2_recip_adm`
  from squarefree arguments. Every such element is `d·e²` with `d` admissible and `e` primary
  (`exists_adm_mul_sq`, from round 349's `sqk_spec`); the squares drop out of the symbols
  (`sym2_sq_eq_one`) and of `φ` (`gq4_mul_sq`, from round 322's `gamQ_mul_sq`).
* **`−1`, `2`, `ω` and the units** (`chiP_cube_eq`, **`sym2_neg_one`**, **`sym2_two`**, `sym2_omega`,
  `sym2_unit_congr`): `χ_P(a)³` is the quadratic character of `𝒪/P`, so `(−1/𝔞)₂ = χ₄(N𝔞)` and
  `(2/𝔞)₂ = χ₈(N𝔞)` by Mathlib's `quadraticChar_neg_one` and `quadraticChar_two`; `(ω/x)₂ = 1`; the
  quadratic symbols of the units depend only on `x mod 4`.
* **The quadratic supplement for `λ`** (`sym2_δ3_formula`, **`sym2_δ3_congr`**): `(δ₃/x)₂` depends only
  on `x mod 36`. Write `x = ω^j + δ₃v⁻¹r` with `j ∈ {1, 2}` chosen so that `x − ω^j` is odd and `r`
  primary. Then `((x − ω^j)/x)₂ = (−1/x)₂`, `(x/r)₂ = (ω^j/r)₂ = 1`, and reciprocity between `r` and `x`
  gives `(δ₃/x)₂·2φ(rx) = (−1/x)₂(v⁻¹/x)₂·φ(r)φ(x)`; for `x' ≡ x (mod 36)` the same `j` and `v` serve
  and `r' ≡ r (mod 4)`.
* **The cubic symbol of `2`** (`cub_two_congr`): `(2/x)₃ = (−2/x)₃ = (x/−2)₃` depends only on `x mod 2`.
* **The sextic symbols** (`sym6_pow_seven`, **`sym6_eq_sym2_mul`**, `sym6_unit_congr`, `sym6_δ3_congr`,
  `sym6_two_congr`, **`sym6_S_congr`**): `(a/𝔞)₆ = (a/𝔞)₂·σ((a/𝔞)₃)²`, so with round 362's cubic
  periodicity, `(uδ₃^m2^n/x)₆` depends only on `x mod 72` for every unit `u` and `m, n ∈ ℕ`.
-/

open NumberField Ideal UniqueFactorizationMonoid

noncomputable section

namespace Eis

/-! ### `φ(cy²) = φ(c)` -/

/-- **`φ` is invariant under odd squares**: `φ(cy²) = φ(c)` for `y` prime to `2` (round 322's
`gamQ_mul_sq`, since `Γ_quad = φ/2`). -/
theorem gq4_mul_sq (c : 𝓞 K) {y : 𝓞 K} (hy : IsCoprime y 2) : gq4 (c * y ^ 2) = gq4 c := by
  have h := gamQ_mul_sq c y hy
  unfold gamQ at h
  unfold gq4
  rw [sq, ← mul_assoc]
  linear_combination 2 * h

/-! ### The quadratic symbol -/

theorem sym2_mul_left (a b : 𝓞 K) (I : Ideal (𝓞 K)) : sym2 (a * b) I = sym2 a I * sym2 b I := by
  unfold sym2; rw [sym6_mul_left, mul_pow]

theorem sym2_mul_right (a : 𝓞 K) {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
    sym2 a (I * J) = sym2 a I * sym2 a J := by
  unfold sym2; rw [sym6_mul_right a hI hJ, mul_pow]

theorem not_mem_factor_of_isCoprime {a b : 𝓞 K} (h : IsCoprime a b) {P : Ideal (𝓞 K)}
    (hP : P ∈ normalizedFactors (span {b})) : a ∉ P := by
  intro ha
  have := isMaximal_of_mem_nf hP
  have hb : b ∈ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP) (Ideal.mem_span_singleton_self b)
  obtain ⟨u, v, huv⟩ := h
  exact IsMaximal.ne_top ‹P.IsMaximal› ((Ideal.eq_top_iff_one _).2
    (huv ▸ P.add_mem (P.mul_mem_left u ha) (P.mul_mem_left v hb)))

/-- `(a/b)₂² = 1` for coprime `a, b` with `N(b)` prime to `6`. -/
theorem sym2_sq_eq_one {a b : 𝓞 K} (hb : (absNorm (span {b})).Coprime 6) (h : IsCoprime a b) :
    sym2 a (span {b}) ^ 2 = 1 := by
  rw [sym2, ← pow_mul, ← sym6_pow_succ a _ 5, sym6_pow_six hb,
    ite_eq_left fun P hP => not_mem_factor_of_isCoprime h hP]

/-- An element of odd norm is prime to `2`. -/
theorem isCoprime_two_of_odd {n : 𝓞 K} (h : (absNorm (span {n})).Coprime 2) : IsCoprime n 2 := by
  have hodd : absNorm (span {n}) % 2 = 1 := Nat.coprime_two_right.1 h |> Nat.odd_iff.1
  obtain ⟨k, hk⟩ : ∃ k, absNorm (span {n}) = 2 * k + 1 := ⟨absNorm (span {n}) / 2, by omega⟩
  have hN := mul_cj_eq_absNorm n
  rw [hk] at hN
  refine ⟨cj n, -(k : 𝓞 K), ?_⟩
  push_cast at hN
  linear_combination hN

theorem coprime6_of_dvd {a b : 𝓞 K} (h : a ∣ b) (hb : (absNorm (span {b})).Coprime 6) :
    (absNorm (span {a})).Coprime 6 := by
  obtain ⟨c, rfl⟩ := h
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul] at hb
  exact coprime6_left hb

/-- **Squarefree times a square**: a primary `x` of norm prime to `6` is `d·e²` with `d` admissible
(primary, squarefree, of norm prime to `6`) and `e` primary of odd norm. -/
theorem exists_adm_mul_sq {x : 𝓞 K} (hx : Primary x) (hx6 : (absNorm (span {x})).Coprime 6) :
    ∃ d e : 𝓞 K, QAdm d ∧ Primary e ∧ (absNorm (span {e})).Coprime 6 ∧ x = d * e ^ 2 := by
  have hx0 := primary_ne_zero hx
  obtain ⟨h1, h2, h3⟩ := sqk_spec hx0
  have hex : sqe x ∣ x := by
    have : sqe x ∣ sqk x * sqe x ^ 2 := ⟨sqk x * sqe x, by ring⟩
    rwa [← h1] at this
  have hlam : ¬ (ω - 1 : 𝓞 K) ∣ sqe x := fun h => hx.not_lam_dvd (h.trans hex)
  obtain ⟨v, hv⟩ := exists_primary hlam
  have hvv : ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set e := (v : 𝓞 K) * sqe x with he
  set d := ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 2 * sqk x with hd
  have hxde : x = d * e ^ 2 := by
    rw [hd, he]
    calc x = sqk x * sqe x ^ 2 := h1
      _ = (((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K)) ^ 2 * (sqk x * sqe x ^ 2) := by rw [hvv]; ring
      _ = _ := by ring
  have he6 : (absNorm (span {e})).Coprime 6 := by
    have : e ∣ x := ⟨d * e, by rw [hxde]; ring⟩
    exact coprime6_of_dvd this hx6
  have hd6 : (absNorm (span {d})).Coprime 6 := coprime6_of_dvd ⟨e ^ 2, by rw [hxde]⟩ hx6
  have hdp : Primary d := by
    obtain ⟨s, hs⟩ := hx
    obtain ⟨r, hr⟩ := hv
    refine ⟨s - d * r * (e + 1), ?_⟩
    have : e - 1 = 3 * r := hr
    linear_combination hs - hxde - d * (e + 1) * this
  have hdsq : Squarefree (span {d}) := by
    rw [hd, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_top.2 ((v⁻¹).isUnit.pow 2), Ideal.top_mul]
    exact h2
  exact ⟨d, e, ⟨hdp, hdsq, hd6⟩, hv, he6, hxde⟩

/-- **Quadratic reciprocity for coprime primary elements of norm prime to `6`**, squarefree or not:
`(x/k)₂(k/x)₂·φ(k)φ(x) = 2φ(kx)`. -/
theorem sym2_recip_gen {k x : 𝓞 K} (hk : Primary k) (hx : Primary x)
    (hk6 : (absNorm (span {k})).Coprime 6) (hx6 : (absNorm (span {x})).Coprime 6)
    (hcop : IsCoprime k x) :
    sym2 x (span {k}) * sym2 k (span {x}) * (gq4 k * gq4 x) = 2 * gq4 (k * x) := by
  obtain ⟨d₁, e₁, hd₁, he₁, he₁6, rfl⟩ := exists_adm_mul_sq hk hk6
  obtain ⟨d₂, e₂, hd₂, he₂, he₂6, rfl⟩ := exists_adm_mul_sq hx hx6
  have he₁2 := isCoprime_two_of_odd (Nat.Coprime.coprime_dvd_right (by norm_num) he₁6)
  have he₂2 := isCoprime_two_of_odd (Nat.Coprime.coprime_dvd_right (by norm_num) he₂6)
  have hd₁0 := span_ne_zero_of_coprime6 hd₁.2.2
  have hd₂0 := span_ne_zero_of_coprime6 hd₂.2.2
  have he₁0 := span_ne_zero_of_coprime6 he₁6
  have he₂0 := span_ne_zero_of_coprime6 he₂6
  -- coprimality of the pieces
  have c11 : IsCoprime d₁ d₂ := hcop.of_mul_left_left.of_mul_right_left
  have c12 : IsCoprime d₁ e₂ :=
    (IsCoprime.pow_right_iff two_pos).1 hcop.of_mul_left_left.of_mul_right_right
  have c21 : IsCoprime e₁ d₂ :=
    (IsCoprime.pow_left_iff two_pos).1 hcop.of_mul_left_right.of_mul_right_left
  have c22 : IsCoprime e₁ e₂ := (IsCoprime.pow_right_iff two_pos).1
    ((IsCoprime.pow_left_iff two_pos).1 hcop.of_mul_left_right.of_mul_right_right)
  have hk2 : span {d₁ * e₁ ^ 2} = span {d₁} * (span {e₁} * span {e₁}) := by
    rw [sq, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  have hx2 : span {d₂ * e₂ ^ 2} = span {d₂} * (span {e₂} * span {e₂}) := by
    rw [sq, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  have hd₁6 := hd₁.2.2
  have hd₂6 := hd₂.2.2
  -- the symbols reduce to the squarefree parts
  have s1 : sym2 (d₂ * e₂ ^ 2) (span {d₁ * e₁ ^ 2}) = sym2 d₂ (span {d₁}) := by
    rw [hk2, sym2_mul_right _ hd₁0 (mul_ne_zero he₁0 he₁0), sym2_mul_right _ he₁0 he₁0, ← sq,
      sym2_sq_eq_one he₁6 (c21.symm.mul_left (c22.symm.pow_left)), sym2_mul_left, sq e₂,
      sym2_mul_left, ← sq, sym2_sq_eq_one hd₁6 c12.symm]
    ring
  have s2 : sym2 (d₁ * e₁ ^ 2) (span {d₂ * e₂ ^ 2}) = sym2 d₁ (span {d₂}) := by
    rw [hx2, sym2_mul_right _ hd₂0 (mul_ne_zero he₂0 he₂0), sym2_mul_right _ he₂0 he₂0, ← sq,
      sym2_sq_eq_one he₂6 (c12.mul_left (c22.pow_left)), sym2_mul_left, sq e₁,
      sym2_mul_left, ← sq, sym2_sq_eq_one hd₂6 c21]
    ring
  have g1 := gq4_mul_sq d₁ he₁2
  have g2 := gq4_mul_sq d₂ he₂2
  have g3 : gq4 (d₁ * e₁ ^ 2 * (d₂ * e₂ ^ 2)) = gq4 (d₁ * d₂) := by
    rw [show d₁ * e₁ ^ 2 * (d₂ * e₂ ^ 2) = d₁ * d₂ * (e₁ * e₂) ^ 2 by ring]
    exact gq4_mul_sq _ (he₁2.mul_left he₂2)
  rw [s1, s2, g1, g2, g3]
  exact sym2_recip_adm hd₁ hd₂ c11

theorem chiP_congr {P : Ideal (𝓞 K)} {a b : 𝓞 K} (h : a - b ∈ P) : chiP P a = chiP P b := by
  unfold chiP
  split_ifs with hP
  · have := hP.1
    rw [Ideal.Quotient.eq.2 h]
  · rfl

/-- The sextic symbol depends on the numerator modulo the denominator. -/
theorem sym6_congr {x a b : 𝓞 K} (h : x ∣ a - b) : sym6 a (span {x}) = sym6 b (span {x}) := by
  unfold sym6
  congr 1
  refine Multiset.map_congr rfl fun P hP => chiP_congr ?_
  have hx : x ∈ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP) (Ideal.mem_span_singleton_self x)
  obtain ⟨c, hc⟩ := h
  rw [hc]; exact P.mul_mem_right c hx

theorem sym2_congr {x a b : 𝓞 K} (h : x ∣ a - b) : sym2 a (span {x}) = sym2 b (span {x}) := by
  unfold sym2; rw [sym6_congr h]

open Classical in
/-- `χ_P(a)³` is the quadratic character of `𝒪/P` at `a`. -/
theorem chiP_cube_eq {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) (a : 𝓞 K) :
    chiP P a ^ 3 = ((quadraticChar (𝓞 K ⧸ P) (Ideal.Quotient.mk P a) : ℤ) : ℂ) := by
  classical
  unfold chiP
  rw [dite_eq_left ⟨hP, hP6⟩, ← MulChar.pow_apply' _ (by norm_num), chi6_cube P hP6]
  rw [MulChar.ringHomComp_apply]
  rfl

/-- `(−1/P)₂ = χ₄(N(P))`. -/
theorem chiP_cube_neg_one {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) :
    chiP P (-1) ^ 3 = ((ZMod.χ₄ (absNorm P : ZMod 4) : ℤ) : ℂ) := by
  classical
  rw [chiP_cube_eq hP6, map_neg, map_one, quadraticChar_neg_one (ringChar_ne_two P hP6),
    absNorm_eq_card]

/-- `(2/P)₂ = χ₈(N(P))`. -/
theorem chiP_cube_two {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) :
    chiP P 2 ^ 3 = ((ZMod.χ₈ (absNorm P : ZMod 8) : ℤ) : ℂ) := by
  classical
  rw [chiP_cube_eq hP6, map_ofNat, quadraticChar_two (ringChar_ne_two P hP6),
    absNorm_eq_card]

theorem absNorm_eq_prod_nf {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    absNorm I = ((normalizedFactors I).map absNorm).prod := by
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  rw [Multiset.prod_hom]

/-- **`(−1/𝔞)₂ = χ₄(N(𝔞))`** for `N(𝔞)` prime to `6`. -/
theorem sym2_neg_one {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    sym2 (-1) I = ((ZMod.χ₄ (absNorm I : ZMod 4) : ℤ) : ℂ) := by
  unfold sym2 sym6
  rw [← Multiset.prod_map_pow,
    Multiset.map_congr rfl fun P hP => by
      have := isMaximal_of_factor hP; exact chiP_cube_neg_one (six_not_mem_of_factor hI hP),
    absNorm_eq_prod_nf (ne_bot_of_coprime6 hI), Nat.cast_multiset_prod, map_multiset_prod,
    Int.cast_multiset_prod, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  rfl

/-- **`(2/𝔞)₂ = χ₈(N(𝔞))`** for `N(𝔞)` prime to `6`. -/
theorem sym2_two {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) :
    sym2 2 I = ((ZMod.χ₈ (absNorm I : ZMod 8) : ℤ) : ℂ) := by
  unfold sym2 sym6
  rw [← Multiset.prod_map_pow,
    Multiset.map_congr rfl fun P hP => by
      have := isMaximal_of_factor hP; exact chiP_cube_two (six_not_mem_of_factor hI hP),
    absNorm_eq_prod_nf (ne_bot_of_coprime6 hI), Nat.cast_multiset_prod, map_multiset_prod,
    Int.cast_multiset_prod, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  rfl

/-- `b ≡ b' (mod m)` gives `N(b) ≡ N(b') (mod m)`. -/
theorem absNorm_congr (m : ℤ) {b b' : 𝓞 K} (h : (m : 𝓞 K) ∣ b - b') :
    ((absNorm (span {b}) : ℤ) - absNorm (span {b'})) % m = 0 := by
  have h1 := mul_cj_eq_absNorm b
  have h2 := mul_cj_eq_absNorm b'
  have hc : (m : 𝓞 K) ∣ cj b - cj b' := by
    obtain ⟨z, hz⟩ := h
    exact ⟨cj z, by rw [← map_sub, hz, map_mul, map_intCast]⟩
  have h3 : (m : 𝓞 K) ∣ b * cj b - b' * cj b' := by
    have : b * cj b - b' * cj b' = b * (cj b - cj b') + (b - b') * cj b' := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hc _) (dvd_mul_of_dvd_left h _)
  rw [h1, h2] at h3
  have h4 : (m : 𝓞 K) ∣ (((absNorm (span {b}) : ℤ) - absNorm (span {b'}) : ℤ) : 𝓞 K) := by
    push_cast; exact_mod_cast h3
  exact Int.emod_eq_zero_of_dvd (int_dvd_of_dvd h4)

theorem sym2_neg_one_congr {x x' : 𝓞 K} (h6 : (absNorm (span {x})).Coprime 6)
    (h6' : (absNorm (span {x'})).Coprime 6) (h4 : (4 : 𝓞 K) ∣ x - x') :
    sym2 (-1) (span {x}) = sym2 (-1) (span {x'}) := by
  rw [sym2_neg_one h6, sym2_neg_one h6']
  have := absNorm_congr 4 (by exact_mod_cast h4)
  have e : ((absNorm (span {x}) : ℕ) : ZMod 4) = ((absNorm (span {x'}) : ℕ) : ZMod 4) := by
    rw [ZMod.natCast_eq_natCast_iff']; omega
  rw [e]

theorem sym2_two_congr {x x' : 𝓞 K} (h6 : (absNorm (span {x})).Coprime 6)
    (h6' : (absNorm (span {x'})).Coprime 6) (h8 : (8 : 𝓞 K) ∣ x - x') :
    sym2 2 (span {x}) = sym2 2 (span {x'}) := by
  rw [sym2_two h6, sym2_two h6']
  have := absNorm_congr 8 (by exact_mod_cast h8)
  have e : ((absNorm (span {x}) : ℕ) : ZMod 8) = ((absNorm (span {x'}) : ℕ) : ZMod 8) := by
    rw [ZMod.natCast_eq_natCast_iff']; omega
  rw [e]

/-- `(ω/x)₂ = 1`: `ω = (ω²)²`. -/
theorem sym2_omega {x : 𝓞 K} (h6 : (absNorm (span {x})).Coprime 6) : sym2 ω (span {x}) = 1 := by
  have hω : (ω : 𝓞 K) = ω ^ 2 * ω ^ 2 := by
    rw [← pow_add, show (2 + 2 : ℕ) = 3 + 1 by norm_num, pow_succ, ω_cube, one_mul]
  rw [hω, sym2_mul_left, ← sq]
  refine sym2_sq_eq_one h6 ?_
  have hu : IsUnit (ω : 𝓞 K) := by rw [← coe_ωu]; exact ωu.isUnit
  have := (isCoprime_mul_unit_left_left (hu.pow 2) 1 x).2 isCoprime_one_left
  rwa [mul_one] at this

/-- **The quadratic symbols of the units** depend only on the class modulo `4`. -/
theorem sym6_one_left {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) : sym6 1 I = 1 := by
  unfold sym6
  exact Multiset.prod_eq_one fun y hy => by
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hy
    exact chiP_one ⟨isMaximal_of_factor hP, six_not_mem_of_factor hI hP⟩

theorem sym2_omega_pow {x : 𝓞 K} (h6 : (absNorm (span {x})).Coprime 6) (j : ℕ) :
    sym2 (ω ^ j) (span {x}) = 1 := by
  induction j with
  | zero => rw [pow_zero, sym2, sym6_one_left h6, one_pow]
  | succ j ih => rw [pow_succ, sym2_mul_left, ih, sym2_omega h6, one_mul]

theorem sym2_unit_congr (u : (𝓞 K)ˣ) {x x' : 𝓞 K} (h6 : (absNorm (span {x})).Coprime 6)
    (h6' : (absNorm (span {x'})).Coprime 6) (h4 : (4 : 𝓞 K) ∣ x - x') :
    sym2 (u : 𝓞 K) (span {x}) = sym2 (u : 𝓞 K) (span {x'}) := by
  have hn := sym2_neg_one_congr h6 h6' h4
  have hw := sym2_omega_pow h6
  have hw' := sym2_omega_pow h6'
  have hneg : ∀ j : ℕ, sym2 (-(ω ^ j)) (span {x}) = sym2 (-(ω ^ j)) (span {x'}) := fun j => by
    rw [neg_eq_neg_one_mul, sym2_mul_left, sym2_mul_left, hw, hw', hn]
  rcases List.mem_cons.1 (units_mem u) with rfl | hu
  · simpa using congrArg id (show sym2 (ω ^ 0) (span {x}) = sym2 (ω ^ 0) (span {x'}) by rw [hw, hw'])
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_neg, Units.val_one]; exact hn
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [coe_ωu]; simpa using (show sym2 (ω ^ 1) (span {x}) = sym2 (ω ^ 1) (span {x'}) by rw [hw, hw'])
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_neg, coe_ωu]; simpa using hneg 1
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_pow_eq_pow_val, coe_ωu, hw, hw']
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_neg, Units.val_pow_eq_pow_val, coe_ωu]; exact hneg 2
  simp at hu

theorem gq4_ne_zero_of_primary {y : 𝓞 K} (hy : Primary y) (h6 : (absNorm (span {y})).Coprime 6) :
    gq4 y ≠ 0 := by
  obtain ⟨d, e, hd, he, he6, rfl⟩ := exists_adm_mul_sq hy h6
  rw [gq4_mul_sq d (isCoprime_two_of_odd (Nat.Coprime.coprime_dvd_right (by norm_num) he6))]
  exact gq4_ne_zero_of_adm hd

theorem coprime6_of_primary_two {r : 𝓞 K} (hr : Primary r) (h2 : ¬ (2 : 𝓞 K) ∣ r) :
    (absNorm (span {r})).Coprime 6 :=
  coprime6_of_primary (primary_ne_zero hr) hr h2

/-- **The comparison for `λ`**: if `x = ω^j + δ₃v⁻¹r` with `x, r` primary, `N(x)` prime to `6` and `r`
odd, then `(δ₃/x)₂·2φ(rx) = (−1/x)₂(v⁻¹/x)₂·φ(r)φ(x)`. -/
theorem sym2_δ3_formula {x r : 𝓞 K} {j : ℕ} (v : (𝓞 K)ˣ) (hx : Primary x)
    (h6 : (absNorm (span {x})).Coprime 6) (hr : Primary r) (hr2 : ¬ (2 : 𝓞 K) ∣ r)
    (hxr : x = ω ^ j + δ3 * ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * r) :
    sym2 δ3 (span {x}) * (2 * gq4 (r * x)) =
      sym2 (-1) (span {x}) * sym2 ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) (span {x}) * (gq4 r * gq4 x) := by
  have hr6 := coprime6_of_primary_two hr hr2
  set u := ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) with hu_def
  have hωu : IsUnit (ω ^ j : 𝓞 K) := by
    have : IsUnit (ω : 𝓞 K) := by rw [← coe_ωu]; exact ωu.isUnit
    exact this.pow j
  -- (i) and (ii): two expressions for ((x − ω^j)/x)₂
  have e1 : sym2 (x - ω ^ j) (span {x}) = sym2 (-1) (span {x}) := by
    rw [sym2_congr (b := -(ω ^ j)) ⟨1, by ring⟩, neg_eq_neg_one_mul, sym2_mul_left,
      sym2_omega_pow h6, mul_one]
  have e2 : sym2 (x - ω ^ j) (span {x}) =
      sym2 δ3 (span {x}) * sym2 u (span {x}) * sym2 r (span {x}) := by
    rw [show x - ω ^ j = δ3 * u * r by rw [hxr]; ring, sym2_mul_left, sym2_mul_left]
  -- (iii) reciprocity between `r` and `x`
  have hcop : IsCoprime r x := by
    obtain ⟨w, hw⟩ := hωu
    refine ⟨-(δ3 * u * ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K)), ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K), ?_⟩
    have hww : ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (w : 𝓞 K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hw] at hww
    linear_combination (((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) * hxr + hww
  have hrec := sym2_recip_gen hr hx hr6 h6 hcop
  have e3 : sym2 x (span {r}) = 1 := by
    rw [sym2_congr (b := ω ^ j) ⟨δ3 * u, by rw [hxr]; ring⟩]
    exact sym2_omega_pow hr6 j
  rw [e3, one_mul] at hrec
  have hsq : sym2 u (span {x}) ^ 2 = 1 := by
    refine sym2_sq_eq_one h6 ?_
    have := (isCoprime_mul_unit_left_left (v⁻¹).isUnit 1 x).2 isCoprime_one_left
    rwa [mul_one] at this
  have e12 := e1.symm.trans e2
  -- combine
  have key : sym2 δ3 (span {x}) * (2 * gq4 (r * x)) =
      sym2 δ3 (span {x}) * sym2 u (span {x}) ^ 2 * (sym2 r (span {x}) * (gq4 r * gq4 x)) := by
    rw [hsq, hrec]; ring
  rw [key]
  linear_combination (-(sym2 u (span {x}) * (gq4 r * gq4 x))) * e12


theorem lam_dvd_δ3 : (ω - 1 : 𝓞 K) ∣ δ3 := ⟨-ω, by unfold δ3; linear_combination ω_sq_add⟩

/-- One of `x − ω`, `x − ω²` is odd. -/
theorem odd_sub_omega (x : 𝓞 K) : ¬ (2 : 𝓞 K) ∣ x - ω ∨ ¬ (2 : 𝓞 K) ∣ x - ω ^ 2 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have h3 := dvd_mul_of_dvd_right (dvd_sub h1 h2) (ω ^ 2)
  rw [show ω ^ 2 * ((x - ω) - (x - ω ^ 2)) = ω - 1 by linear_combination (ω - 1) * ω_cube] at h3
  have h4 : (2 : 𝓞 K) ∣ 3 - 2 := dvd_sub (h3.trans lam_dvd_three) (dvd_refl 2)
  rw [show (3 : 𝓞 K) - 2 = 1 by norm_num] at h4
  exact not_isUnit_two (isUnit_of_dvd_one h4)

theorem mk_four_eq {a b : 𝓞 K} (h : (4 : 𝓞 K) ∣ a - b) :
    Ideal.Quotient.mk (span {(4 : 𝓞 K)}) a = Ideal.Quotient.mk (span {(4 : 𝓞 K)}) b :=
  Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)

/-- **The quadratic supplement for `λ`, as periodicity**: for primary `x, x'` of norm prime to `6`
with `x ≡ x' (mod 36)`, `(δ₃/x)₂ = (δ₃/x')₂`. Compare `x` with `ω` or `ω²`. -/
theorem sym2_δ3_congr {x x' : 𝓞 K} (hx : Primary x) (hx' : Primary x')
    (h6 : (absNorm (span {x})).Coprime 6) (h6' : (absNorm (span {x'})).Coprime 6)
    (h36 : (36 : 𝓞 K) ∣ x - x') : sym2 δ3 (span {x}) = sym2 δ3 (span {x'}) := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨t', ht'⟩ := hx'
  have hx0 : Primary x := ⟨t, ht⟩
  have hx0' : Primary x' := ⟨t', ht'⟩
  obtain ⟨k, hk⟩ := h36
  have htt : t - t' = 12 * k := by
    have h3 : (3 : 𝓞 K) * (t - t') = 3 * (12 * k) := by linear_combination -ht + ht' + hk
    exact mul_left_cancel₀ (by norm_num) h3
  have hδ := δ3_sq
  have main : ∀ (j : ℕ) (c : 𝓞 K), IsUnit c → ω ^ j + δ3 * c = 1 → ¬ (2 : 𝓞 K) ∣ x - ω ^ j →
      sym2 δ3 (span {x}) = sym2 δ3 (span {x'}) := by
    intro j c hc hjc h2
    have hlam : ¬ (ω - 1 : 𝓞 K) ∣ c - δ3 * t := by
      intro h
      have := dvd_add h (dvd_mul_of_dvd_left lam_dvd_δ3 t)
      rw [sub_add_cancel] at this
      exact lam_not_unit (isUnit_of_dvd_unit this hc)
    obtain ⟨v, hv⟩ := exists_primary hlam
    have hvv : ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    set u := ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
    set r := (v : 𝓞 K) * (c - δ3 * t) with hr_def
    set r' := (v : 𝓞 K) * (c - δ3 * t') with hr'_def
    have hrr : r - r' = -(12 * (v : 𝓞 K) * δ3 * k) := by
      rw [hr_def, hr'_def]; linear_combination (-(v : 𝓞 K) * δ3) * htt
    have hr' : Primary r' := by
      obtain ⟨s, hs⟩ := hv
      exact ⟨s + 4 * (v : 𝓞 K) * δ3 * k, by linear_combination hs - hrr⟩
    have hxr : x = ω ^ j + δ3 * u * r := by
      rw [hr_def]; linear_combination ht - hjc + t * hδ - δ3 * (c - δ3 * t) * hvv
    have hxr' : x' = ω ^ j + δ3 * u * r' := by
      rw [hr'_def]; linear_combination ht' - hjc + t' * hδ - δ3 * (c - δ3 * t') * hvv
    have h2r : ¬ (2 : 𝓞 K) ∣ r := fun h => h2 (by
      rw [show x - ω ^ j = δ3 * u * r by rw [hxr]; ring]; exact dvd_mul_of_dvd_right h _)
    have h2' : ¬ (2 : 𝓞 K) ∣ x' - ω ^ j := fun h => h2 (by
      rw [show x - ω ^ j = (x' - ω ^ j) + 2 * (18 * k) by linear_combination hk]
      exact dvd_add h (dvd_mul_right 2 _))
    have h2r' : ¬ (2 : 𝓞 K) ∣ r' := fun h => h2' (by
      rw [show x' - ω ^ j = δ3 * u * r' by rw [hxr']; ring]; exact dvd_mul_of_dvd_right h _)
    have f := sym2_δ3_formula v hx0 h6 hv h2r hxr
    have f' := sym2_δ3_formula v hx0' h6' hr' h2r' hxr'
    have c4 : (4 : 𝓞 K) ∣ x - x' := ⟨9 * k, by rw [hk]; ring⟩
    have g1 : gq4 r = gq4 r' := gq4_congr (mk_four_eq ⟨-(3 * (v : 𝓞 K) * δ3 * k), by rw [hrr]; ring⟩)
    have g2 : gq4 x = gq4 x' := gq4_congr (mk_four_eq c4)
    have g3 : gq4 (r * x) = gq4 (r' * x') := by
      refine gq4_congr (mk_four_eq ?_)
      obtain ⟨a, ha⟩ := c4
      refine ⟨-(3 * (v : 𝓞 K) * δ3 * k) * x + r' * a, ?_⟩
      linear_combination x * hrr + r' * ha
    rw [sym2_neg_one_congr h6 h6' c4, sym2_unit_congr _ h6 h6' c4, g1, g2, ← f', ← g3] at f
    have hrx6 : (absNorm (span {r * x})).Coprime 6 := by
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
      exact Nat.coprime_mul_iff_left.2 ⟨coprime6_of_primary_two hv h2r, h6⟩
    exact mul_right_cancel₀ (mul_ne_zero two_ne_zero (gq4_ne_zero_of_primary (hv.mul hx0) hrx6)) f
  rcases odd_sub_omega x with h | h
  · refine main 1 (ω ^ 2) ?_ ?_ (by rwa [pow_one])
    · have : IsUnit (ω : 𝓞 K) := by rw [← coe_ωu]; exact ωu.isUnit
      exact this.pow 2
    · unfold δ3; linear_combination ω_sq_add + 2 * ω_cube
  · refine main 2 (-ω) ?_ ?_ h
    · have : IsUnit (ω : 𝓞 K) := by rw [← coe_ωu]; exact ωu.isUnit
      exact this.neg
    · unfold δ3; linear_combination -ω_sq_add

/-- **`(2/x)₃` depends only on `x mod 2`**: `(2/x)₃ = (−2/x)₃ = (x/−2)₃` by cubic reciprocity, `−2` being
a primary prime. -/
theorem cub_two_congr {x x' : 𝓞 K} (hx : Primary x) (hx' : Primary x') (h2 : IsCoprime x 2)
    (h2' : IsCoprime x' 2) (hxx : (2 : 𝓞 K) ∣ x - x') : cub 2 (span {x}) = cub 2 (span {x'}) := by
  have e : ∀ y : 𝓞 K, Primary y → IsCoprime y 2 → cub 2 (span {y}) = cub y (span {(-2 : 𝓞 K)}) := by
    intro y hy hy2
    rw [← cub_neg hy, cub_recip primary_neg_two hy (by simpa using hy2.symm.neg_left)]
  rw [e x hx h2, e x' hx' h2']
  exact cub_congr (by simpa using hxx.neg_left)

theorem chiP_pow_seven (P : Ideal (𝓞 K)) (a : 𝓞 K) : chiP P a ^ 7 = chiP P a := by
  classical
  by_cases h : P.IsMaximal ∧ (6 : 𝓞 K) ∉ P
  · rw [pow_succ, chiP_pow_six h.1 h.2]
    split_ifs with ha
    · rw [chiP_eq_zero_of_mem ha]; ring
    · ring
  · unfold chiP; rw [dite_eq_right h]; ring

theorem sym6_pow_seven (a : 𝓞 K) (I : Ideal (𝓞 K)) : sym6 a I ^ 7 = sym6 a I := by
  unfold sym6
  rw [← Multiset.prod_map_pow]
  congr 1
  exact Multiset.map_congr rfl fun P _ => chiP_pow_seven P a

/-- **The sextic symbol is the quadratic one times the square of the cubic one**:
`(a/𝔞)₆ = (a/𝔞)₂·σ((a/𝔞)₃)²` for `N(𝔞)` prime to `6`. -/
theorem sym6_eq_sym2_mul {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (a : 𝓞 K) :
    sym6 a I = sym2 a I * σO (cub a I) ^ 2 := by
  rw [← sym6_sq_eq_cub hI, sym2, ← pow_mul, ← pow_add, sym6_pow_seven]

theorem dvd_of_dvd_mul_left' {a b c : 𝓞 K} (h : a * b ∣ c) : a ∣ c := (dvd_mul_right a b).trans h

/-- The sextic symbols of the units modulo `36`. -/
theorem sym6_unit_congr (u : (𝓞 K)ˣ) {x x' : 𝓞 K} (hx : Primary x) (hx' : Primary x')
    (h6 : (absNorm (span {x})).Coprime 6) (h6' : (absNorm (span {x'})).Coprime 6)
    (h36 : (36 : 𝓞 K) ∣ x - x') : sym6 (u : 𝓞 K) (span {x}) = sym6 (u : 𝓞 K) (span {x'}) := by
  have h4 : (4 : 𝓞 K) ∣ x - x' := dvd_of_dvd_mul_left' (by simpa [show (36 : 𝓞 K) = 4 * 9 by norm_num] using h36)
  have h9 : (9 : 𝓞 K) ∣ x - x' := (dvd_mul_left 9 4).trans (by simpa [show (36 : 𝓞 K) = 4 * 9 by norm_num] using h36)
  rw [sym6_eq_sym2_mul h6, sym6_eq_sym2_mul h6', sym2_unit_congr u h6 h6' h4,
    cub_unit_congr u hx hx' (cub_omega_congr hx hx' h9)]

/-- **The sextic supplement for `λ`, as periodicity**: `(δ₃/x)₆ = (δ₃/x')₆` for `x ≡ x' (mod 36)`. -/
theorem sym6_δ3_congr {x x' : 𝓞 K} (hx : Primary x) (hx' : Primary x')
    (h6 : (absNorm (span {x})).Coprime 6) (h6' : (absNorm (span {x'})).Coprime 6)
    (h36 : (36 : 𝓞 K) ∣ x - x') : sym6 δ3 (span {x}) = sym6 δ3 (span {x'}) := by
  have h9 : (9 : 𝓞 K) ∣ x - x' := (dvd_mul_left 9 4).trans (by simpa [show (36 : 𝓞 K) = 4 * 9 by norm_num] using h36)
  rw [sym6_eq_sym2_mul h6, sym6_eq_sym2_mul h6', sym2_δ3_congr hx hx' h6 h6' h36,
    cub_δ3_congr hx hx' h9]

/-- **The sextic supplement for `2`, as periodicity**: `(2/x)₆ = (2/x')₆` for `x ≡ x' (mod 8)`. -/
theorem sym6_two_congr {x x' : 𝓞 K} (hx : Primary x) (hx' : Primary x')
    (h6 : (absNorm (span {x})).Coprime 6) (h6' : (absNorm (span {x'})).Coprime 6)
    (h8 : (8 : 𝓞 K) ∣ x - x') : sym6 2 (span {x}) = sym6 2 (span {x'}) := by
  have h2 : (2 : 𝓞 K) ∣ x - x' := (dvd_mul_right 2 4).trans (by simpa [show (8 : 𝓞 K) = 2 * 4 by norm_num] using h8)
  rw [sym6_eq_sym2_mul h6, sym6_eq_sym2_mul h6', sym2_two_congr h6 h6' h8,
    cub_two_congr hx hx' (isCoprime_two_of_odd (Nat.Coprime.coprime_dvd_right (by norm_num) h6))
      (isCoprime_two_of_odd (Nat.Coprime.coprime_dvd_right (by norm_num) h6')) h2]

/-- **The symbols at the primes above `2` and `3` and at the units, as periodicity**: for any unit `u`
and `m, n ∈ ℕ`, `(uδ₃^m2^n/x)₆` depends only on `x mod 72`, for primary `x` of norm prime to `6`. -/
theorem sym6_S_congr (u : (𝓞 K)ˣ) (m n : ℕ) {x x' : 𝓞 K} (hx : Primary x) (hx' : Primary x')
    (h6 : (absNorm (span {x})).Coprime 6) (h6' : (absNorm (span {x'})).Coprime 6)
    (h72 : (72 : 𝓞 K) ∣ x - x') :
    sym6 ((u : 𝓞 K) * δ3 ^ m * 2 ^ n) (span {x}) = sym6 ((u : 𝓞 K) * δ3 ^ m * 2 ^ n) (span {x'}) := by
  have h36 : (36 : 𝓞 K) ∣ x - x' := (dvd_mul_right 36 2).trans (by simpa [show (72 : 𝓞 K) = 36 * 2 by norm_num] using h72)
  have h8 : (8 : 𝓞 K) ∣ x - x' := (dvd_mul_right 8 9).trans (by simpa [show (72 : 𝓞 K) = 8 * 9 by norm_num] using h72)
  have hp : ∀ (a : 𝓞 K) (k : ℕ), sym6 a (span {x}) = sym6 a (span {x'}) →
      sym6 (a ^ k) (span {x}) = sym6 (a ^ k) (span {x'}) := by
    intro a k ha
    induction k with
    | zero => rw [pow_zero, sym6_one_left h6, sym6_one_left h6']
    | succ k ih => rw [pow_succ, sym6_mul_left, sym6_mul_left, ih, ha]
  rw [sym6_mul_left, sym6_mul_left, sym6_mul_left, sym6_mul_left, sym6_unit_congr u hx hx' h6 h6' h36,
    hp δ3 m (sym6_δ3_congr hx hx' h6 h6' h36), hp 2 n (sym6_two_congr hx hx' h6 h6' h8)]

end Eis

end

#print axioms Eis.gq4_mul_sq
#print axioms Eis.sym2_mul_left
#print axioms Eis.sym2_mul_right
#print axioms Eis.not_mem_factor_of_isCoprime
#print axioms Eis.sym2_sq_eq_one
#print axioms Eis.isCoprime_two_of_odd
#print axioms Eis.coprime6_of_dvd
#print axioms Eis.exists_adm_mul_sq
#print axioms Eis.sym2_recip_gen
#print axioms Eis.chiP_congr
#print axioms Eis.sym6_congr
#print axioms Eis.sym2_congr
#print axioms Eis.chiP_cube_eq
#print axioms Eis.chiP_cube_neg_one
#print axioms Eis.chiP_cube_two
#print axioms Eis.absNorm_eq_prod_nf
#print axioms Eis.sym2_neg_one
#print axioms Eis.sym2_two
#print axioms Eis.absNorm_congr
#print axioms Eis.sym2_neg_one_congr
#print axioms Eis.sym2_two_congr
#print axioms Eis.sym2_omega
#print axioms Eis.sym6_one_left
#print axioms Eis.sym2_omega_pow
#print axioms Eis.sym2_unit_congr
#print axioms Eis.gq4_ne_zero_of_primary
#print axioms Eis.coprime6_of_primary_two
#print axioms Eis.sym2_δ3_formula
#print axioms Eis.lam_dvd_δ3
#print axioms Eis.odd_sub_omega
#print axioms Eis.mk_four_eq
#print axioms Eis.sym2_δ3_congr
#print axioms Eis.cub_two_congr
#print axioms Eis.chiP_pow_seven
#print axioms Eis.sym6_pow_seven
#print axioms Eis.sym6_eq_sym2_mul
#print axioms Eis.dvd_of_dvd_mul_left'
#print axioms Eis.sym6_unit_congr
#print axioms Eis.sym6_δ3_congr
#print axioms Eis.sym6_two_congr
#print axioms Eis.sym6_S_congr
