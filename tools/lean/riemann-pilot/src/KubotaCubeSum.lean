import KubotaTorusScale

/-! # The cube sum of Kubota's character (round 445)

S5f-12 of round 360's plan, part 6. Round 444's next step planned the cubic character identity behind the cube
eigenrelation. Let `p` be a primary prime and `(a, c)` the first column of `γ ∈ Γ_1(3)`: `a` primary, `3 ∣ c`,
and `a`, `c` coprime. For `r ∈ ℤ[ω]` let `p^k` be the greatest common divisor of `x = a + 3rc` and `p³`. In
the plan `M_rγ = γ_rβ_r`, and the first column of `γ_r` is `(x/p^k, cp^{3−k})`. With Kubota's symbol
`κ(a, c) = (c/a)₃`, and `1` for `c = 0` (round 361's `kub` of the first column, `kub_eq_kubC`), this round
proves `Σ_{r mod p³} κ(x/p^k, cp^{3−k})·|p|^{(4k−6)/3} = N(p)²·κ(a, c)`:

* **The exponent and the quotient** (`ordP3` and `quoP3`, definitions; **`ordP3_eq`**, **`ordP3_congr`**,
  **`quoP3_congr`**, with `ordP3_le`, `pow_ordP3_dvd`, `not_pow_succ_ordP3_dvd`, `ordP3_mul_of_coprime`,
  `quoP3_spec`, `quoP3_eq`, `not_dvd_quoP3`, `quoP3_mul_of_coprime`, `primary_quoP3`, `ordP3_eq_zero_iff`,
  `ordP3_eq_three_iff` and `quoP3_of_ordP3_zero`): `k = ordP3 p y` is the exponent of `p` in `y`, capped at
  `3`, and `y = p^k·quoP3 p y`. The exponent is periodic modulo `p³`, the quotient is periodic modulo `p` when
  `k < 3`, and a factor prime to `p` passes through both.
* **The cubic character modulo `p`** (**`exists_cub_ne_one`**, with `span_isMaximal_of_prime`,
  `three_not_mem_span`, `isCoprime_of_not_dvd` and `cub_span_eq_zero`): some `g` prime to `p` has `(g/p)₃ ≠ 1`
  (round 290's `cubChar_ne_one`).
* **Sums over `ℤ[ω]/p³`** (**`tsum_quot_affine`**, **`tsum_quot_dvd`** and **`tsum_quot_dvd_three`**, with
  `finite_quot_pow3`, `dvd_repQ_sub` and `card_quot_pow3`): `y ↦ a + uy` permutes the classes for `u` prime to
  `p`; `N(p)²` of the `N(p)³` classes are divisible by `p` (round 414's `card_fiber_mul`), and one by `p³`.
* **The cube sum without its column** (`cubeW`, `cubeV`, `cubeV1` and `cubeV2`, definitions; **`tsum_cubeV`**,
  **`cubeV_split`**, **`tsum_eq_zero_of_twist`**, **`tsum_cubeV1`** and **`tsum_cubeV2`**, with `norm_sq_σO`,
  `cubeW_zero`, `cubeW_three`, `cubeV_congr`, `cubeV1_congr`, `cubeV2_congr`, `cubeV1_mul`, `cubeV2_mul` and
  `σO_pow_ne_one`): for `ζ = (c/p)₃` with `ζ³ = 1`,
  `Σ_{y mod p³} σ(ζ^{2k}·(y′/p)₃^{3−k})·|p|^{(4k−6)/3} = N(p)²`, with `k = ordP3 p y` and `y′ = quoP3 p y`.
  The exponent `0` gives `(N(p)³ − N(p)²)·N(p)⁻¹` (round 362's `cub_pow_three`), the exponent `3` gives
  `N(p)`, and the exponents `1` and `2` give `0`: `y ↦ gy`, for `g` prime to `p` with `(g/p)₃ ≠ 1`, multiplies
  their sums by `(g/p)₃² ≠ 1` and `(g/p)₃ ≠ 1`.
* **The column** (`kubC` and `cubeTerm`, definitions; **`kubC_col`** and **`cubeTerm_eq`**, with
  `kub_eq_kubC`): `κ(x/p^k, cp^{3−k}) = κ(a, c)·σ(ζ^{2k}·(x′/p)₃^{3−k})` with `x′ = x/p^k`, through
  `κ(x, c) = κ(a, c)` (round 382's `cub_add_three_mul`), multiplicativity (round 362's `cub_mul_left` and
  `cub_mul_span`) and cubic reciprocity `(p/x′)₃ = (x′/p)₃` for `k < 3` (round 290's `cub_recip`). For
  `k ≥ 1`, `p ∣ x`, so `p ∤ c` and `ζ³ = 1`.
* **The cube sum** (**`tsum_cubeTerm`** and **`tsum_cubeTerm_gam3`**, with `cubeV_of_not_dvd`): for `p ∣ c`
  every `x` is prime to `p`, so every term is `κ(a, c)·N(p)⁻¹`; for `p ∤ c`, `r ↦ a + 3rc` permutes the
  classes modulo `p³`, and `tsum_cubeV` applies. The first column of `γ ∈ Γ_1(3)` satisfies the hypotheses,
  and then `κ(a, c) = κ(γ)`.
-/

open Ideal NumberField
open scoped BigOperators MatrixGroups

noncomputable section

namespace Eis

/-! ### The exponent of `p`, capped at `3` -/

open Classical in
/-- The exponent of `p` in `y`, capped at `3`. -/
def ordP3 (p y : 𝓞 K) : ℕ :=
  if p ^ 3 ∣ y then 3 else if p ^ 2 ∣ y then 2 else if p ∣ y then 1 else 0

/-- `ordP3 p y ≤ 3`. -/
theorem ordP3_le (p y : 𝓞 K) : ordP3 p y ≤ 3 := by
  unfold ordP3; split_ifs <;> omega

/-- `p^k ∣ y` for `k = ordP3 p y`. -/
theorem pow_ordP3_dvd (p y : 𝓞 K) : p ^ ordP3 p y ∣ y := by
  unfold ordP3
  split_ifs with h3 h2 h1
  · exact h3
  · exact h2
  · rw [pow_one]; exact h1
  · rw [pow_zero]; exact one_dvd y

/-- `p^{k+1} ∤ y` for `k = ordP3 p y < 3`. -/
theorem not_pow_succ_ordP3_dvd {p y : 𝓞 K} (h : ordP3 p y < 3) : ¬ p ^ (ordP3 p y + 1) ∣ y := by
  unfold ordP3 at h ⊢
  split_ifs at h ⊢ with h3 h2 h1
  · omega
  · exact h3
  · exact h2
  · rw [zero_add, pow_one]; exact h1

/-- **The exponent from its two defining properties.** -/
theorem ordP3_eq {p y : 𝓞 K} {k : ℕ} (hk : k ≤ 3) (hdvd : p ^ k ∣ y)
    (hnot : k < 3 → ¬ p ^ (k + 1) ∣ y) : ordP3 p y = k := by
  have h1 : ∀ j, j ≤ k → p ^ j ∣ y := fun j hj => (pow_dvd_pow p hj).trans hdvd
  have h2 : ∀ j, j ≤ 3 → k < j → ¬ p ^ j ∣ y := fun j hj3 hj h => hnot (by omega)
    ((pow_dvd_pow p (show k + 1 ≤ j by omega)).trans h)
  unfold ordP3
  interval_cases k
  · have a3 := h2 3 le_rfl (by norm_num)
    have a2 := h2 2 (by norm_num) (by norm_num)
    have a1 : ¬ p ∣ y := by simpa using h2 1 (by norm_num) (by norm_num)
    simp [a3, a2, a1]
  · have a3 := h2 3 le_rfl (by norm_num)
    have a2 := h2 2 (by norm_num) (by norm_num)
    have a1 : p ∣ y := by simpa using h1 1 le_rfl
    simp [a3, a2, a1]
  · have a3 := h2 3 le_rfl (by norm_num)
    simp [a3, h1 2 le_rfl]
  · simp [h1 3 le_rfl]

/-- `ordP3` is periodic modulo `p³`. -/
theorem ordP3_congr {p y y' : 𝓞 K} (h : p ^ 3 ∣ y - y') : ordP3 p y = ordP3 p y' := by
  have key : ∀ j, j ≤ 3 → (p ^ j ∣ y ↔ p ^ j ∣ y') := by
    intro j hj
    have hd : p ^ j ∣ y - y' := (pow_dvd_pow p hj).trans h
    constructor
    · intro hy
      have := dvd_sub hy hd
      rwa [sub_sub_cancel] at this
    · intro hy'
      have := dvd_add hy' hd
      rwa [add_sub_cancel] at this
  refine ordP3_eq (ordP3_le p y') ?_ ?_
  · exact (key _ (ordP3_le p y')).2 (pow_ordP3_dvd p y')
  · intro hk hdvd
    exact not_pow_succ_ordP3_dvd hk ((key _ (by omega)).1 hdvd)

/-- `ordP3` is unchanged by a factor prime to `p`. -/
theorem ordP3_mul_of_coprime {p g y : 𝓞 K} (hg : IsCoprime g p) : ordP3 p (g * y) = ordP3 p y := by
  have key : ∀ j, (p ^ j ∣ g * y ↔ p ^ j ∣ y) := by
    intro j
    constructor
    · intro h
      exact (hg.pow_right (n := j)).symm.dvd_of_dvd_mul_left h
    · exact fun h => dvd_mul_of_dvd_right h g
  refine ordP3_eq (ordP3_le p y) ?_ ?_
  · exact (key _).2 (pow_ordP3_dvd p y)
  · intro hk hdvd
    exact not_pow_succ_ordP3_dvd hk ((key _).1 hdvd)

/-! ### The quotient `y/p^k` -/

/-- `y/p^k` for `k = ordP3 p y`. -/
def quoP3 (p y : 𝓞 K) : 𝓞 K := (pow_ordP3_dvd p y).choose

/-- `y = p^k·(y/p^k)` for `k = ordP3 p y`. -/
theorem quoP3_spec (p y : 𝓞 K) : y = p ^ ordP3 p y * quoP3 p y := (pow_ordP3_dvd p y).choose_spec

/-- For `p ≠ 0` the quotient is the cofactor of `p^k`. -/
theorem quoP3_eq {p y x : 𝓞 K} (hp : p ≠ 0) (h : y = p ^ ordP3 p y * x) : quoP3 p y = x := by
  have h1 := quoP3_spec p y
  exact mul_left_cancel₀ (pow_ne_zero _ hp) (h1.symm.trans h)

/-- `p ∤ y/p^k` for `k = ordP3 p y < 3`. -/
theorem not_dvd_quoP3 {p y : 𝓞 K} (h : ordP3 p y < 3) : ¬ p ∣ quoP3 p y := by
  intro hd
  apply not_pow_succ_ordP3_dvd h
  conv_rhs => rw [quoP3_spec p y]
  rw [pow_succ]
  exact mul_dvd_mul_left _ hd

/-- `(gy)/p^k = g·(y/p^k)` for `g` prime to `p`. -/
theorem quoP3_mul_of_coprime {p g y : 𝓞 K} (hp : p ≠ 0) (hg : IsCoprime g p) :
    quoP3 p (g * y) = g * quoP3 p y := by
  refine quoP3_eq hp ?_
  rw [ordP3_mul_of_coprime hg]
  conv_lhs => rw [quoP3_spec p y]
  ring

/-- **The quotient is periodic modulo `p`**, when the exponent is below `3` and `y ≡ y′ (mod p³)`. -/
theorem quoP3_congr {p y y' : 𝓞 K} (hp : p ≠ 0) (h : p ^ 3 ∣ y - y') (hk : ordP3 p y < 3) :
    p ∣ quoP3 p y - quoP3 p y' := by
  have he := ordP3_congr h
  have hy := quoP3_spec p y
  have hy' := quoP3_spec p y'
  rw [← he] at hy'
  set k := ordP3 p y with hk'
  have hdiff : p ^ k * (quoP3 p y - quoP3 p y') = y - y' := by
    rw [mul_sub, ← hy, ← hy']
  have h3 : p ^ k * p ^ (3 - k) ∣ p ^ k * (quoP3 p y - quoP3 p y') := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega), hdiff]
    exact h
  have h4 := (mul_dvd_mul_iff_left (pow_ne_zero k hp)).1 h3
  exact (dvd_pow_self p (by omega : 3 - k ≠ 0)).trans h4

/-- `y/p^k` is primary for `p` and `y` primary. -/
theorem primary_quoP3 {p y : 𝓞 K} (hp : Primary p) (hy : Primary y) : Primary (quoP3 p y) := by
  have h := quoP3_spec p y
  rw [h] at hy
  exact (primary_mul_iff (primary_pow hp _)).1 hy

/-! ### The cubic character modulo a primary prime -/

/-- `(p)` is maximal for `p` prime. -/
theorem span_isMaximal_of_prime {p : 𝓞 K} (hp : Prime p) : (span {p} : Ideal (𝓞 K)).IsMaximal :=
  ((span_singleton_prime hp.ne_zero).2 hp).isMaximal (by rw [Ne, span_singleton_eq_bot]; exact hp.ne_zero)

/-- `3 ∉ (p)` for a primary prime `p`. -/
theorem three_not_mem_span {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) : (3 : 𝓞 K) ∉ span {p} :=
  three_not_mem_of_primary (span_isMaximal_of_prime hp).ne_top hpp rfl

/-- `x` and `p` are coprime for `p` prime with `p ∤ x`. -/
theorem isCoprime_of_not_dvd {p x : 𝓞 K} (hp : Prime p) (h : ¬ p ∣ x) : IsCoprime x p :=
  (isCoprime_of_irreducible hp.irreducible h).symm

/-- `(x/p)₃ = 0` for `p ∣ x`. -/
theorem cub_span_eq_zero {p x : 𝓞 K} (hp : Prime p) (h : p ∣ x) : cub x (span {p}) = 0 := by
  have := span_isMaximal_of_prime hp
  rw [cub_prime]
  exact chi3_of_mem (Ideal.mem_span_singleton.2 h)

/-- **A residue with a nontrivial symbol**: some `g` prime to `p` has `(g/p)₃ ≠ 1` (round 290's
`cubChar_ne_one`). -/
theorem exists_cub_ne_one {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) :
    ∃ g : 𝓞 K, IsCoprime g p ∧ cub g (span {p}) ≠ 1 := by
  have := span_isMaximal_of_prime hp
  have hP3 := three_not_mem_span hp hpp
  obtain ⟨x, hx⟩ := MulChar.ne_one_iff.1 (cubChar_ne_one (span {p}) hP3)
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (x : 𝓞 K ⧸ span {p})
  have hgP : ¬ p ∣ g := fun h => x.ne_zero (by
    rw [← hg, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton.2 h)
  refine ⟨g, isCoprime_of_not_dvd hp hgP, ?_⟩
  rw [cub_prime, chi3_eq hP3, hg]
  exact hx

/-! ### Sums over `ℤ[ω]/p³` -/

/-- `ℤ[ω]/p³` is finite for `p ≠ 0`. -/
theorem finite_quot_pow3 {p : 𝓞 K} (hp : p ≠ 0) : Finite (𝓞 K ⧸ span {p ^ 3}) :=
  finite_quot _ (pow_ne_zero 3 hp)

/-- The representative of the class of `y` modulo `c` is `≡ y (mod c)`. -/
theorem dvd_repQ_sub (c y : 𝓞 K) : c ∣ repQ c (Ideal.Quotient.mk (span {c}) y) - y := by
  have h := repQ_mk c (Ideal.Quotient.mk (span {c}) y)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  exact h

/-- **An affine change of variables on `ℤ[ω]/p³`**: for `F` periodic modulo `p³` and `u` prime to `p`,
`Σ_q F(a + u·q) = Σ_q F(q)`. -/
theorem tsum_quot_affine {p u : 𝓞 K} (hp : p ≠ 0) (hu : IsCoprime u p) {F : 𝓞 K → ℂ}
    (hF : ∀ y y', p ^ 3 ∣ y - y' → F y = F y') (a : 𝓞 K) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, F (a + u * repQ (p ^ 3) q) =
      ∑' q : 𝓞 K ⧸ span {p ^ 3}, F (repQ (p ^ 3) q) := by
  have := finite_quot_pow3 hp
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  rw [tsum_fintype, tsum_fintype]
  set e : 𝓞 K ⧸ span {p ^ 3} → 𝓞 K ⧸ span {p ^ 3} :=
    fun q => Ideal.Quotient.mk (span {p ^ 3}) (a + u * repQ (p ^ 3) q) with he
  have hinj : Function.Injective e := by
    intro q q' h
    rw [he, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have h' : p ^ 3 ∣ u * (repQ (p ^ 3) q - repQ (p ^ 3) q') := by
      have : a + u * repQ (p ^ 3) q - (a + u * repQ (p ^ 3) q') =
          u * (repQ (p ^ 3) q - repQ (p ^ 3) q') := by ring
      rwa [this] at h
    have h'' := (hu.pow_right (n := 3)).symm.dvd_of_dvd_mul_left h'
    rw [← repQ_mk (p ^ 3) q, ← repQ_mk (p ^ 3) q', Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h''
  refine Fintype.sum_bijective e (Finite.injective_iff_bijective.1 hinj) _ _ fun q => ?_
  exact hF _ _ (by
    have := dvd_repQ_sub (p ^ 3) (a + u * repQ (p ^ 3) q)
    rw [← dvd_neg, neg_sub] at this
    exact this)

/-- `ℤ[ω]/p³` has `N(p)³` classes (round 363's `card_quot`). -/
theorem card_quot_pow3 {p : 𝓞 K} [Fintype (𝓞 K ⧸ span {p ^ 3})] :
    Fintype.card (𝓞 K ⧸ span {p ^ 3}) = absNorm (span {p}) ^ 3 := by
  rw [card_quot, ← span_singleton_pow, map_pow]

open Classical in
/-- **The classes divisible by `p`**: `N(p)²` of the `N(p)³` classes modulo `p³`. -/
theorem tsum_quot_dvd {p : 𝓞 K} (hp : p ≠ 0) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, (if p ∣ repQ (p ^ 3) q then (1 : ℂ) else 0) =
      (absNorm (span {p}) : ℂ) ^ 2 := by
  have := finite_quot_pow3 hp
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  have : Finite (𝓞 K ⧸ span {p}) := finite_quot _ hp
  have := Fintype.ofFinite (𝓞 K ⧸ span {p})
  have hle : span {p ^ 3} ≤ span {p} := span_singleton_le_span_singleton.2 (dvd_pow_self p (by norm_num))
  have key : (Finset.univ.filter fun q : 𝓞 K ⧸ span {p ^ 3} => p ∣ repQ (p ^ 3) q) =
      Finset.univ.filter fun q => Ideal.Quotient.factor hle q = 0 := by
    refine Finset.filter_congr fun q _ => ?_
    rw [← repQ_mk (p ^ 3) q, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, repQ_mk]
  have hfib := card_fiber_mul (Ideal.Quotient.factor hle).toAddMonoidHom
    (Ideal.Quotient.factor_surjective hle) 0
  rw [card_quot_pow3, card_quot] at hfib
  have hN : absNorm (span {p}) ≠ 0 := by
    rw [Ne, absNorm_eq_zero_iff, span_singleton_eq_bot]; exact hp
  have hc : (Finset.univ.filter fun q : 𝓞 K ⧸ span {p ^ 3} => Ideal.Quotient.factor hle q = 0).card =
      absNorm (span {p}) ^ 2 := by
    have h1 : (Finset.univ.filter fun q : 𝓞 K ⧸ span {p ^ 3} =>
        Ideal.Quotient.factor hle q = 0).card * absNorm (span {p}) =
        absNorm (span {p}) ^ 2 * absNorm (span {p}) := by
      rw [show absNorm (span {p}) ^ 2 * absNorm (span {p}) = absNorm (span {p}) ^ 3 by ring]
      exact hfib
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN) h1
  rw [tsum_fintype, Finset.sum_boole, key, hc]
  push_cast
  ring

open Classical in
/-- The class `0` is the one class divisible by `p³`. -/
theorem tsum_quot_dvd_three {p : 𝓞 K} (hp : p ≠ 0) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, (if p ^ 3 ∣ repQ (p ^ 3) q then (1 : ℂ) else 0) = 1 := by
  have := finite_quot_pow3 hp
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  rw [tsum_fintype]
  have key : ∀ q : 𝓞 K ⧸ span {p ^ 3}, (p ^ 3 ∣ repQ (p ^ 3) q ↔ q = 0) := by
    intro q
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, repQ_mk]
  simp_rw [key]
  simp

/-! ### The weights -/

/-- The weight `(|p|^{2k−3})^{2/3}` of the cube term with exponent `k`. -/
def cubeW (p : 𝓞 K) (k : ℕ) : ℝ := (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3) ^ (2 / 3 : ℝ)

/-- `|p|² = N(p)` (round 294's `normSq_σO`). -/
theorem norm_sq_σO (p : 𝓞 K) : ‖σO p‖ ^ 2 = (absNorm (span {p}) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, normSq_σO]

/-- `w_0 = N(p)⁻¹`. -/
theorem cubeW_zero {p : 𝓞 K} (hp : p ≠ 0) : cubeW p 0 = (absNorm (span {p}) : ℝ)⁻¹ := by
  have hpos : 0 < ‖σO p‖ := norm_pos_iff.2 (σO_ne_zero hp)
  unfold cubeW
  rw [mul_zero, pow_zero, one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le, ← norm_sq_σO, ← Real.rpow_natCast ‖σO p‖ 2]
  norm_num

/-- `w_3 = N(p)`. -/
theorem cubeW_three {p : 𝓞 K} (hp : p ≠ 0) : cubeW p 3 = (absNorm (span {p}) : ℝ) := by
  have hpos : 0 < ‖σO p‖ := norm_pos_iff.2 (σO_ne_zero hp)
  unfold cubeW
  rw [show ‖σO p‖ ^ (2 * 3) / ‖σO p‖ ^ 3 = ‖σO p‖ ^ 3 by field_simp, ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le, ← norm_sq_σO, ← Real.rpow_natCast ‖σO p‖ 2]
  norm_num

/-! ### The cube sum without its column -/

/-- The term of the cube sum at `y`, with `ζ = (c/p)₃`:
`σ(ζ^{2k}·((y/p^k)/p)₃^{3−k})·w_k` for `k = ordP3 p y`. -/
def cubeV (p c y : 𝓞 K) : ℂ :=
  σO (cub c (span {p}) ^ (2 * ordP3 p y) * cub (quoP3 p y) (span {p}) ^ (3 - ordP3 p y)) *
    (cubeW p (ordP3 p y) : ℂ)

/-- `cubeV` is periodic modulo `p³`. -/
theorem cubeV_congr {p : 𝓞 K} (hp : p ≠ 0) (c : 𝓞 K) {y y' : 𝓞 K} (h : p ^ 3 ∣ y - y') :
    cubeV p c y = cubeV p c y' := by
  unfold cubeV
  have he := ordP3_congr h
  rw [← he]
  by_cases hk : ordP3 p y < 3
  · rw [cub_congr (quoP3_congr hp h hk)]
  · have h3 : ordP3 p y = 3 := le_antisymm (ordP3_le p y) (by omega)
    rw [h3, Nat.sub_self, pow_zero, pow_zero]

open Classical in
/-- The part of the cube sum with exponent `1`. -/
def cubeV1 (p y : 𝓞 K) : ℂ := if ordP3 p y = 1 then σO (cub (quoP3 p y) (span {p}) ^ 2) else 0

open Classical in
/-- The part of the cube sum with exponent `2`. -/
def cubeV2 (p y : 𝓞 K) : ℂ := if ordP3 p y = 2 then σO (cub (quoP3 p y) (span {p})) else 0

/-- `cubeV1` is periodic modulo `p³`. -/
theorem cubeV1_congr {p : 𝓞 K} (hp : p ≠ 0) {y y' : 𝓞 K} (h : p ^ 3 ∣ y - y') : cubeV1 p y = cubeV1 p y' := by
  unfold cubeV1
  rw [← ordP3_congr h]
  split_ifs with h1
  · rw [cub_congr (quoP3_congr hp h (by omega))]
  · rfl

/-- `cubeV2` is periodic modulo `p³`. -/
theorem cubeV2_congr {p : 𝓞 K} (hp : p ≠ 0) {y y' : 𝓞 K} (h : p ^ 3 ∣ y - y') : cubeV2 p y = cubeV2 p y' := by
  unfold cubeV2
  rw [← ordP3_congr h]
  split_ifs with h1
  · rw [cub_congr (quoP3_congr hp h (by omega))]
  · rfl

/-- **The twist of the part with exponent `1`**: `cubeV1(gy) = σ((g/p)₃²)·cubeV1(y)` for `g` prime to `p`. -/
theorem cubeV1_mul {p g : 𝓞 K} (hp : p ≠ 0) (hg : IsCoprime g p) (y : 𝓞 K) :
    cubeV1 p (g * y) = σO (cub g (span {p}) ^ 2) * cubeV1 p y := by
  unfold cubeV1
  rw [ordP3_mul_of_coprime hg, quoP3_mul_of_coprime hp hg, cub_mul_left]
  split_ifs
  · rw [mul_pow, map_mul]
  · rw [mul_zero]

/-- **The twist of the part with exponent `2`**: `cubeV2(gy) = σ((g/p)₃)·cubeV2(y)` for `g` prime to `p`. -/
theorem cubeV2_mul {p g : 𝓞 K} (hp : p ≠ 0) (hg : IsCoprime g p) (y : 𝓞 K) :
    cubeV2 p (g * y) = σO (cub g (span {p})) * cubeV2 p y := by
  unfold cubeV2
  rw [ordP3_mul_of_coprime hg, quoP3_mul_of_coprime hp hg, cub_mul_left]
  split_ifs
  · rw [map_mul]
  · rw [mul_zero]

/-- **The twist**: a sum over `ℤ[ω]/p³` that a factor `λ ≠ 1` multiplies is `0`. -/
theorem tsum_eq_zero_of_twist {p g : 𝓞 K} (hp : p ≠ 0) (hg : IsCoprime g p) {F : 𝓞 K → ℂ}
    (hF : ∀ y y', p ^ 3 ∣ y - y' → F y = F y') {l : ℂ} (hl : l ≠ 1) (hmul : ∀ y, F (g * y) = l * F y) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, F (repQ (p ^ 3) q) = 0 := by
  have h := tsum_quot_affine hp hg hF 0
  simp only [zero_add, hmul] at h
  rw [tsum_mul_left] at h
  have : (l - 1) * ∑' q : 𝓞 K ⧸ span {p ^ 3}, F (repQ (p ^ 3) q) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl)

/-- `σ(ζ^a) ≠ 1` for `ζ³ = 1`, `ζ ≠ 1` and `3 ∤ a`. -/
theorem σO_pow_ne_one {ζ : 𝓞 K} (h3 : ζ ^ 3 = 1) (h1 : ζ ≠ 1) {a : ℕ} (ha : ¬ 3 ∣ a) : σO (ζ ^ a) ≠ 1 := by
  rw [← map_one σO]
  exact fun h => pow_ne_one_of_cube h3 h1 ha (σO_injective h)

/-- **The parts with exponents `1` and `2` vanish**: they are sums of `((y/p)/p)₃²` and `((y/p²)/p)₃`, which
the twist by `g` with `(g/p)₃ ≠ 1` multiplies by `(g/p)₃² ≠ 1` and `(g/p)₃ ≠ 1`. -/
theorem tsum_cubeV1 {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, cubeV1 p (repQ (p ^ 3) q) = 0 := by
  obtain ⟨g, hg, hg1⟩ := exists_cub_ne_one hp hpp
  exact tsum_eq_zero_of_twist hp.ne_zero hg (fun y y' h => cubeV1_congr hp.ne_zero h)
    (σO_pow_ne_one (cub_pow_three hpp hg) hg1 (by norm_num)) (cubeV1_mul hp.ne_zero hg)

/-- The part with exponent `2` vanishes, as in `tsum_cubeV1`. -/
theorem tsum_cubeV2 {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, cubeV2 p (repQ (p ^ 3) q) = 0 := by
  obtain ⟨g, hg, hg1⟩ := exists_cub_ne_one hp hpp
  refine tsum_eq_zero_of_twist hp.ne_zero hg (fun y y' h => cubeV2_congr hp.ne_zero h) ?_
    (cubeV2_mul hp.ne_zero hg)
  rw [← pow_one (cub g (span {p}))]
  exact σO_pow_ne_one (cub_pow_three hpp hg) hg1 (by norm_num)

/-! ### The sum of `cubeV` -/

/-- `ordP3 p y = 0` exactly when `p ∤ y`. -/
theorem ordP3_eq_zero_iff {p y : 𝓞 K} : ordP3 p y = 0 ↔ ¬ p ∣ y := by
  constructor
  · intro h hd
    have := not_pow_succ_ordP3_dvd (show ordP3 p y < 3 by omega)
    rw [h, zero_add, pow_one] at this
    exact this hd
  · intro h
    exact ordP3_eq (by norm_num) (by rw [pow_zero]; exact one_dvd y) fun _ => by rwa [zero_add, pow_one]

/-- `ordP3 p y = 3` exactly when `p³ ∣ y`. -/
theorem ordP3_eq_three_iff {p y : 𝓞 K} : ordP3 p y = 3 ↔ p ^ 3 ∣ y := by
  constructor
  · intro h
    have := pow_ordP3_dvd p y
    rwa [h] at this
  · intro h
    exact ordP3_eq le_rfl h fun h' => absurd h' (lt_irrefl 3)

/-- For `ordP3 p y = 0` the quotient is `y`. -/
theorem quoP3_of_ordP3_zero {p y : 𝓞 K} (hp : p ≠ 0) (h : ordP3 p y = 0) : quoP3 p y = y :=
  quoP3_eq hp (by rw [h, pow_zero, one_mul])

open Classical in
/-- **`cubeV` by exponent**, for `(c/p)₃³ = 1`. -/
theorem cubeV_split {p c : 𝓞 K} (hp : Prime p) (hpp : Primary p) (hζ : cub c (span {p}) ^ 3 = 1) (y : 𝓞 K) :
    cubeV p c y = (if ordP3 p y = 0 then (cubeW p 0 : ℂ) else 0) +
      (if ordP3 p y = 3 then (cubeW p 3 : ℂ) else 0) +
      σO (cub c (span {p}) ^ 2) * (cubeW p 1 : ℂ) * cubeV1 p y +
      σO (cub c (span {p}) ^ 4) * (cubeW p 2 : ℂ) * cubeV2 p y := by
  unfold cubeV cubeV1 cubeV2
  have hk := ordP3_le p y
  rcases (show ordP3 p y = 0 ∨ ordP3 p y = 1 ∨ ordP3 p y = 2 ∨ ordP3 p y = 3 by omega)
    with h | h | h | h
  · have hq : quoP3 p y = y := quoP3_of_ordP3_zero hp.ne_zero h
    have hcop : IsCoprime y p := isCoprime_of_not_dvd hp (ordP3_eq_zero_iff.1 h)
    simp only [h, hq, mul_zero, pow_zero, Nat.sub_zero, one_mul, cub_pow_three hpp hcop, map_one,
      ite_true, show (0 : ℕ) ≠ 3 by norm_num, show (0 : ℕ) ≠ 1 by norm_num, show (0 : ℕ) ≠ 2 by norm_num,
      ite_false, add_zero, mul_zero]
  · simp only [h, show (1 : ℕ) ≠ 0 by norm_num, show (1 : ℕ) ≠ 3 by norm_num, show (1 : ℕ) ≠ 2 by norm_num,
      ite_true, ite_false, zero_add, add_zero, mul_zero, map_mul]
    ring_nf
  · simp only [h, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 3 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
      ite_true, ite_false, zero_add, add_zero, mul_zero, map_mul]
    ring_nf
  · have h6 : cub c (span {p}) ^ (2 * 3) = 1 := by rw [pow_mul', hζ, one_pow]
    simp only [h, h6, Nat.sub_self, pow_zero, mul_one, map_one, one_mul,
      show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num,
      ite_true, ite_false, zero_add, add_zero, mul_zero]

/-- **`Σ_{y mod p³} cubeV(y) = N(p)²`**, for `(c/p)₃³ = 1`: the exponent `0` gives `(N³ − N²)·N⁻¹`, the
exponent `3` gives `N`, and the exponents `1` and `2` give `0`. -/
theorem tsum_cubeV {p c : 𝓞 K} (hp : Prime p) (hpp : Primary p) (hζ : cub c (span {p}) ^ 3 = 1) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, cubeV p c (repQ (p ^ 3) q) = (absNorm (span {p}) : ℂ) ^ 2 := by
  classical
  have hp0 := hp.ne_zero
  have := finite_quot_pow3 hp0
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  have h1 := tsum_cubeV1 hp hpp
  have h2 := tsum_cubeV2 hp hpp
  have hd := tsum_quot_dvd hp0
  have hd3 := tsum_quot_dvd_three hp0
  rw [tsum_fintype] at h1 h2 hd hd3 ⊢
  simp_rw [cubeV_split hp hpp hζ, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, mul_zero, add_zero]
  have e0 : ∀ q : 𝓞 K ⧸ span {p ^ 3}, (if ordP3 p (repQ (p ^ 3) q) = 0 then (cubeW p 0 : ℂ) else 0) =
      (cubeW p 0 : ℂ) * (1 - if p ∣ repQ (p ^ 3) q then (1 : ℂ) else 0) := by
    intro q
    by_cases h : p ∣ repQ (p ^ 3) q
    · have h0 : ordP3 p (repQ (p ^ 3) q) ≠ 0 := fun h0 => ordP3_eq_zero_iff.1 h0 h
      simp [h, h0]
    · simp [h, ordP3_eq_zero_iff.2 h]
  have e3 : ∀ q : 𝓞 K ⧸ span {p ^ 3}, (if ordP3 p (repQ (p ^ 3) q) = 3 then (cubeW p 3 : ℂ) else 0) =
      (cubeW p 3 : ℂ) * (if p ^ 3 ∣ repQ (p ^ 3) q then (1 : ℂ) else 0) := by
    intro q
    by_cases h : p ^ 3 ∣ repQ (p ^ 3) q
    · simp [h, ordP3_eq_three_iff.2 h]
    · have h3 : ordP3 p (repQ (p ^ 3) q) ≠ 3 := fun h3 => h (ordP3_eq_three_iff.1 h3)
      simp [h, h3]
  simp_rw [e0, e3, ← Finset.mul_sum, Finset.sum_sub_distrib, hd, hd3, Finset.sum_const, Finset.card_univ,
    card_quot_pow3, cubeW_zero hp0, cubeW_three hp0]
  have hN : (absNorm (span {p}) : ℂ) ≠ 0 := absNorm_span_ne_zero hp0
  push_cast
  field_simp
  ring

/-! ### The cube sum of a column -/

open Classical in
/-- **Kubota's symbol of a first column** `(a, c)`: `κ(a, c) = (c/a)₃`, and `1` for `c = 0`. -/
def kubC (a c : 𝓞 K) : ℂ := if c = 0 then 1 else σO (cub c (span {a}))

/-- Round 361's `kub` is `kubC` of the first column. -/
theorem kub_eq_kubC (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) : kub γ = kubC (γ 0 0) (γ 1 0) := rfl

/-- **The term of the cube sum at `r`** for the column `(a, c)`: with `x = a + 3rc` and `p^k` the greatest
common divisor of `x` and `p³` (`k = ordP3 p x`), Kubota's symbol `κ(x/p^k, cp^{3−k})` times the weight
`w_k`. -/
def cubeTerm (p a c r : 𝓞 K) : ℂ :=
  kubC (quoP3 p (a + 3 * c * r)) (c * p ^ (3 - ordP3 p (a + 3 * c * r))) *
    (cubeW p (ordP3 p (a + 3 * c * r)) : ℂ)

/-- **The symbol of the reduced column**: for a primary prime `p`, `k ≤ 3`, `x = p^k·x′` with `x′` primary
and, when `k < 3`, prime to `p`, and `x` prime to `c`,
`κ(x′, cp^{3−k}) = κ(x, c)·σ((c/p)₃^{2k}·(x′/p)₃^{3−k})`: multiplicativity, `(p/x′)₃ = (x′/p)₃` (round 290's
`cub_recip`), and `(c/p)₃³ = 1` when `k ≥ 1`, since then `p ∣ x` and `p ∤ c`. -/
theorem kubC_col {p c x x' : 𝓞 K} {k : ℕ} (hp : Prime p) (hpp : Primary p) (hx' : Primary x') (hk : k ≤ 3)
    (hxk : x = p ^ k * x') (hnd : k < 3 → ¬ p ∣ x') (hxc : IsCoprime x c) :
    kubC x' (c * p ^ (3 - k)) =
      kubC x c * σO (cub c (span {p}) ^ (2 * k) * cub x' (span {p}) ^ (3 - k)) := by
  have hp0 := hp.ne_zero
  have hx'0 := primary_ne_zero hx'
  by_cases hc0 : c = 0
  · subst hc0
    have hu : IsUnit x := isCoprime_zero_right.1 hxc
    have hk0 : k = 0 := by
      by_contra h
      exact hp.not_isUnit (isUnit_of_dvd_unit (hxk ▸ dvd_mul_of_dvd_left (dvd_pow_self p h) x') hu)
    subst hk0
    rw [pow_zero, one_mul] at hxk
    subst hxk
    simp [kubC, cub_pow_three hpp (isCoprime_of_not_dvd hp (hnd (by norm_num)))]
  have hz : cub c (span {p}) ^ (3 * k) = 1 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, mul_zero, pow_zero]
    · have hpx : p ∣ x := hxk ▸ dvd_mul_of_dvd_left (dvd_pow_self p hpos.ne') x'
      have hpc : ¬ p ∣ c := fun hpc => hp.not_isUnit (hxc.isUnit_of_dvd' hpx hpc)
      rw [pow_mul, cub_pow_three hpp (isCoprime_of_not_dvd hp hpc), one_pow]
  have hrec : cub p (span {x'}) ^ (3 - k) = cub x' (span {p}) ^ (3 - k) := by
    rcases hk.lt_or_eq with hlt | heq
    · rw [cub_recip hpp hx' (isCoprime_of_not_dvd hp (hnd hlt)).symm]
    · rw [heq, Nat.sub_self, pow_zero, pow_zero]
  subst hxk
  have hcp : c * p ^ (3 - k) ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ hp0)
  simp only [kubC, hc0, hcp, ↓reduceIte]
  rw [← map_mul, cub_mul_left, cub_pow_left hx', cub_mul_span c (pow_ne_zero k hp0) hx'0, cub_pow_span c hp0,
    hrec]
  have e : cub c (span {p}) ^ k * cub c (span {x'}) *
      (cub c (span {p}) ^ (2 * k) * cub x' (span {p}) ^ (3 - k)) =
      cub c (span {p}) ^ (3 * k) * (cub c (span {x'}) * cub x' (span {p}) ^ (3 - k)) := by ring
  rw [e, hz, one_mul]

/-- **The cube term through the column's symbol**: `cubeTerm(a, c, r) = κ(a, c)·cubeV(a + 3rc)` for a primary
prime `p`, `a` primary, `3 ∣ c` and `a`, `c` coprime, by `κ(a + 3rc, c) = κ(a, c)` (round 382's
`cub_add_three_mul`) and `kubC_col`. -/
theorem cubeTerm_eq {p a c : 𝓞 K} (hp : Prime p) (hpp : Primary p) (ha : Primary a) (hc : (3 : 𝓞 K) ∣ c)
    (hac : IsCoprime a c) (r : 𝓞 K) : cubeTerm p a c r = kubC a c * cubeV p c (a + 3 * c * r) := by
  have hxp : Primary (a + 3 * c * r) := by
    have e : a + 3 * c * r - 1 = (a - 1) + 3 * (c * r) := by ring
    unfold Primary
    rw [e]
    exact dvd_add ha (dvd_mul_right 3 _)
  have hxc : IsCoprime (a + 3 * c * r) c := by
    have h := hac.add_mul_left_left (3 * r)
    rwa [show a + c * (3 * r) = a + 3 * c * r by ring] at h
  have hka : kubC a c = kubC (a + 3 * c * r) c := by
    by_cases h : c = 0 <;> simp [kubC, h, cub_add_three_mul ha hac hc r]
  unfold cubeTerm cubeV
  rw [kubC_col hp hpp (primary_quoP3 hpp hxp) (ordP3_le _ _) (quoP3_spec _ _) not_dvd_quoP3 hxc, hka]
  ring

/-- For `p ∤ y`, `cubeV(y) = w_0 = N(p)⁻¹`, since `(y/p)₃³ = 1` (round 362's `cub_pow_three`). -/
theorem cubeV_of_not_dvd {p c y : 𝓞 K} (hp : Prime p) (hpp : Primary p) (h : ¬ p ∣ y) :
    cubeV p c y = (absNorm (span {p}) : ℂ)⁻¹ := by
  have h0 := ordP3_eq_zero_iff.2 h
  unfold cubeV
  rw [h0, quoP3_of_ordP3_zero hp.ne_zero h0, mul_zero, pow_zero, one_mul, Nat.sub_zero,
    cub_pow_three hpp (isCoprime_of_not_dvd hp h), map_one, one_mul, cubeW_zero hp.ne_zero]
  push_cast
  rfl

/-- **The cube sum of a column**: `Σ_{r mod p³} cubeTerm(a, c, r) = N(p)²·κ(a, c)` for a primary prime `p` and
a column `(a, c)` with `a` primary, `3 ∣ c` and `a`, `c` coprime. For `p ∣ c` every `a + 3rc` is prime to `p`
(`cubeV_of_not_dvd`); for `p ∤ c`, `r ↦ a + 3rc` permutes the classes modulo `p³` (`tsum_quot_affine`), and
`tsum_cubeV` applies. -/
theorem tsum_cubeTerm {p a c : 𝓞 K} (hp : Prime p) (hpp : Primary p) (ha : Primary a) (hc : (3 : 𝓞 K) ∣ c)
    (hac : IsCoprime a c) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, cubeTerm p a c (repQ (p ^ 3) q) =
      (absNorm (span {p}) : ℂ) ^ 2 * kubC a c := by
  have hp0 := hp.ne_zero
  simp_rw [cubeTerm_eq hp hpp ha hc hac]
  rw [tsum_mul_left, mul_comm]
  congr 1
  by_cases hpc : p ∣ c
  · have hnd : ∀ y, ¬ p ∣ a + 3 * c * y := fun y hd => hp.not_isUnit (hac.isUnit_of_dvd' (by
      have e : a = (a + 3 * c * y) - 3 * c * y := by ring
      rw [e]
      exact dvd_sub hd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpc 3) y)) hpc)
    have e : ∀ q : 𝓞 K ⧸ span {p ^ 3}, cubeV p c (a + 3 * c * repQ (p ^ 3) q) =
        (absNorm (span {p}) : ℂ)⁻¹ := fun q => cubeV_of_not_dvd hp hpp (hnd _)
    simp_rw [e]
    have := finite_quot_pow3 hp0
    have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
    have hN : (absNorm (span {p}) : ℂ) ≠ 0 := absNorm_span_ne_zero hp0
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, card_quot_pow3, nsmul_eq_mul]
    push_cast
    field_simp
  · have h3 : IsCoprime (3 : 𝓞 K) p :=
      isCoprime_of_not_dvd hp fun h => three_not_mem_span hp hpp (Ideal.mem_span_singleton.2 h)
    rw [tsum_quot_affine hp0 (h3.mul_left (isCoprime_of_not_dvd hp hpc))
      (fun y y' h => cubeV_congr hp0 c h) a]
    exact tsum_cubeV hp hpp (cub_pow_three hpp (isCoprime_of_not_dvd hp hpc))

/-- **The cube sum for `γ ∈ Γ_1(3)`**: `Σ_{r mod p³} cubeTerm(a, c, r) = N(p)²·κ(γ)` for a primary prime `p`
and the first column `(a, c)` of `γ`, which has `a` primary, `3 ∣ c` and `a`, `c` coprime. -/
theorem tsum_cubeTerm_gam3 {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) :
    ∑' q : 𝓞 K ⧸ span {p ^ 3}, cubeTerm p (γ 0 0) (γ 1 0) (repQ (p ^ 3) q) =
      (absNorm (span {p}) : ℂ) ^ 2 * kub ↑γ := by
  have h3 := mem_Gam3.1 hγ
  have hdet := γ.2
  rw [Matrix.det_fin_two] at hdet
  rw [kub_eq_kubC]
  refine tsum_cubeTerm hp hpp (by simpa [Primary] using h3 0 0) (by simpa using h3 1 0)
    ⟨γ 1 1, -γ 0 1, by linear_combination hdet⟩

end Eis

end

#print axioms Eis.ordP3_le
#print axioms Eis.pow_ordP3_dvd
#print axioms Eis.not_pow_succ_ordP3_dvd
#print axioms Eis.ordP3_eq
#print axioms Eis.ordP3_congr
#print axioms Eis.ordP3_mul_of_coprime
#print axioms Eis.quoP3_spec
#print axioms Eis.quoP3_eq
#print axioms Eis.not_dvd_quoP3
#print axioms Eis.quoP3_mul_of_coprime
#print axioms Eis.quoP3_congr
#print axioms Eis.primary_quoP3
#print axioms Eis.span_isMaximal_of_prime
#print axioms Eis.three_not_mem_span
#print axioms Eis.isCoprime_of_not_dvd
#print axioms Eis.cub_span_eq_zero
#print axioms Eis.exists_cub_ne_one
#print axioms Eis.finite_quot_pow3
#print axioms Eis.dvd_repQ_sub
#print axioms Eis.tsum_quot_affine
#print axioms Eis.card_quot_pow3
#print axioms Eis.tsum_quot_dvd
#print axioms Eis.tsum_quot_dvd_three
#print axioms Eis.norm_sq_σO
#print axioms Eis.cubeW_zero
#print axioms Eis.cubeW_three
#print axioms Eis.cubeV_congr
#print axioms Eis.cubeV1_congr
#print axioms Eis.cubeV2_congr
#print axioms Eis.cubeV1_mul
#print axioms Eis.cubeV2_mul
#print axioms Eis.tsum_eq_zero_of_twist
#print axioms Eis.σO_pow_ne_one
#print axioms Eis.tsum_cubeV1
#print axioms Eis.tsum_cubeV2
#print axioms Eis.ordP3_eq_zero_iff
#print axioms Eis.ordP3_eq_three_iff
#print axioms Eis.quoP3_of_ordP3_zero
#print axioms Eis.cubeV_split
#print axioms Eis.tsum_cubeV
#print axioms Eis.kub_eq_kubC
#print axioms Eis.kubC_col
#print axioms Eis.cubeTerm_eq
#print axioms Eis.cubeV_of_not_dvd
#print axioms Eis.tsum_cubeTerm
#print axioms Eis.tsum_cubeTerm_gam3
