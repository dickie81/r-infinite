import HalfPlaneWeighted

/-!
# The ideals of `ℤ[ω]` of bounded norm (round 287)

S2′ averages the family over the ideals `𝔟` of norm at most `Y`, and needs the count of those
divisible by a fixed `𝔡` with an error `O(√Y)`. This file proves it.
* **The count at each norm** (`rA_eq`): the number of ideals of norm `n ≥ 1` is `Σ_{d∣n} χ₋₃(d)`. The
  prime powers come from round 284's splitting law (`card_ofNorm_split`, `card_ofNorm_inert`,
  `card_ofNorm_three`), and multiplicativity from round 283's `ofNorm_mul`.
* **The constant** `κ = Σ_d χ₋₃(d)/d = L(1, χ₋₃)` (`kappa`), as the sum of the pairs
  `1/(3k+1) − 1/(3k+2)`. It is positive (`kappa_pos`), and `|Σ_{d≤U} χ₋₃(d)/d − κ| ≤ 3/(U+1)`
  (`abs_sum_chi_div_sub_kappa_le`).
* **Dirichlet's hyperbola method** (`hyperbola`): `|Σ_{n≤N} χ₋₃(n)⌊N/n⌋ − κN| ≤ 5√N`, using that the
  partial sums of `χ₋₃` are `0` or `1` (`sum_chiInt_Ioc`).
* **The ideal theorem with a square-root error** (`abs_idealCount_sub_le`):
  `|#{𝔞 ≠ 0 : N𝔞 ≤ x} − κx| ≤ 5√x + κ`.
* **Multiples** (`card_multiples`): the multiples of `𝔡 ≠ 0` of norm at most `Y` are counted by
  `#{𝔞 ≠ 0 : N𝔞 ≤ Y/N𝔡}`.

No lattice-point geometry is used: the count is arithmetic, through `ζ_{ℚ(√−3)} = ζ·L(·, χ₋₃)`.
-/

open NumberField Ideal UniqueFactorizationMonoid

namespace Eis

/-! ### The number of ideals of norm `n`: `Σ_{d ∣ n} χ₋₃(d)` -/

section IdealCount

theorem chiInt_mul (m n : ℕ) : chiInt (m * n) = chiInt m * chiInt n := by
  unfold chiInt
  have h := Nat.mul_mod m n 3
  have hm : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hm' : m % 3 <;> interval_cases hn' : n % 3 <;> simp_all

/-- An ideal all of whose prime factors equal `P` is a power of `P`. -/
theorem eq_pow_of_factors {I P : Ideal (𝓞 K)} (hI : I ≠ ⊥) (h : ∀ Q ∈ normalizedFactors I, Q = P) :
    I = P ^ (normalizedFactors I).card := by
  have hrep : normalizedFactors I = Multiset.replicate (normalizedFactors I).card P :=
    Multiset.eq_replicate.2 ⟨rfl, h⟩
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, hrep]
  rw [Multiset.prod_replicate]

/-- An ideal all of whose prime factors are `P` or `Q` is `P^a Q^b`. -/
theorem eq_pow_mul_pow_of_factors {I P Q : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hPQ : P ≠ Q)
    (h : ∀ R ∈ normalizedFactors I, R = P ∨ R = Q) :
    I = P ^ (normalizedFactors I).count P * Q ^ (normalizedFactors I).count Q := by
  classical
  have hsplit : normalizedFactors I = Multiset.replicate ((normalizedFactors I).count P) P +
      Multiset.replicate ((normalizedFactors I).count Q) Q := by
    ext R
    rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    by_cases hRP : R = P
    · subst hRP; rw [ite_eq_left rfl, ite_eq_right (Ne.symm hPQ), add_zero]
    by_cases hRQ : R = Q
    · subst hRQ; rw [ite_eq_right hPQ, ite_eq_left rfl, zero_add]
    rw [ite_eq_right (Ne.symm hRP), ite_eq_right (Ne.symm hRQ), add_zero, Multiset.count_eq_zero]
    intro hR
    rcases h R hR with h' | h'
    · exact hRP h'
    · exact hRQ h'
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, hsplit]
  rw [Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate]

theorem ne_bot_of_norm {I : Ideal (𝓞 K)} {n : ℕ} (hn : n ≠ 0) (hI : absNorm I = n) : I ≠ ⊥ := by
  rintro rfl; rw [Ideal.absNorm_bot] at hI; exact hn hI.symm

theorem factors_pow_mul_pow {P Q : Ideal (𝓞 K)} (hP : P.IsPrime) (hQ : Q.IsPrime) (hP0 : P ≠ ⊥)
    (hQ0 : Q ≠ ⊥) (a b : ℕ) :
    normalizedFactors (P ^ a * Q ^ b) = Multiset.replicate a P + Multiset.replicate b Q := by
  have hPi : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hQi : Irreducible Q := (Ideal.prime_of_isPrime hQ0 hQ).irreducible
  rw [normalizedFactors_mul (pow_ne_zero _ (by simpa using hP0)) (pow_ne_zero _ (by simpa using hQ0)),
    normalizedFactors_pow, normalizedFactors_pow, normalizedFactors_irreducible hPi,
    normalizedFactors_irreducible hQi, normalize_eq, normalize_eq, Multiset.nsmul_singleton,
    Multiset.nsmul_singleton]


/-- **Split**: `p ≡ 1 (mod 3)` has `k + 1` ideals of norm `p^k`, the `P^a Q^{k−a}`. -/
theorem card_ofNorm_split {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) (k : ℕ) :
    (ofNorm (p ^ k)).card = k + 1 := by
  classical
  obtain ⟨P, Q, hPQ, hf, hPn, hQn⟩ := split_of_mod_one hp h1
  have hPf : P ∈ pFactors p := by rw [hf]; simp
  have hQf : Q ∈ pFactors p := by rw [hf]; simp
  obtain ⟨hPp, hP0⟩ := pFactors_prime hp hPf
  obtain ⟨hQp, hQ0⟩ := pFactors_prime hp hQf
  have himg : ofNorm (p ^ k) = (Finset.range (k + 1)).image (fun a => P ^ a * Q ^ (k - a)) := by
    ext I
    rw [mem_ofNorm, Finset.mem_image]
    constructor
    · intro hI
      have hI0 := ne_bot_of_norm (pow_ne_zero k hp.ne_zero) hI
      have hfac : ∀ R ∈ normalizedFactors I, R = P ∨ R = Q := fun R hR => by
        have := mem_pFactors_of_mem hp hI hR
        rw [hf] at this; simpa using this
      have hIe := eq_pow_mul_pow_of_factors hI0 hPQ hfac
      have hab : (normalizedFactors I).count P + (normalizedFactors I).count Q = k := by
        have h' := hI
        rw [hIe, map_mul, map_pow, map_pow, hPn, hQn, ← pow_add] at h'
        exact Nat.pow_right_injective hp.two_le h'
      refine ⟨(normalizedFactors I).count P, Finset.mem_range.2 (by omega), ?_⟩
      rw [show k - (normalizedFactors I).count P = (normalizedFactors I).count Q by omega]
      exact hIe.symm
    · rintro ⟨a, ha, rfl⟩
      have hak : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
      rw [map_mul, map_pow, map_pow, hPn, hQn, ← pow_add, Nat.add_sub_cancel' hak]
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro a _ b _ hab
  have h := congrArg (fun I => (normalizedFactors I).count P) hab
  simp only [factors_pow_mul_pow hPp hQp hP0 hQ0, Multiset.count_add,
    Multiset.count_replicate_self, Multiset.count_replicate, ite_eq_right (Ne.symm hPQ),
    add_zero] at h
  exact h

/-- **Inert**: `p ≡ 2 (mod 3)` has one ideal of norm `p^k` if `k` is even, none otherwise. -/
theorem card_ofNorm_inert {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) (k : ℕ) :
    (ofNorm (p ^ k)).card = if 2 ∣ k then 1 else 0 := by
  classical
  obtain ⟨P, hf, hPn⟩ := inert_of_mod_two hp h2
  have hfac : ∀ {I : Ideal (𝓞 K)}, absNorm I = p ^ k → ∀ R ∈ normalizedFactors I, R = P :=
    fun {I} hI R hR => by
      have := mem_pFactors_of_mem hp hI hR
      rw [hf] at this; simpa using this
  split_ifs with hk
  · obtain ⟨j, rfl⟩ := hk
    rw [Finset.card_eq_one]
    refine ⟨P ^ j, ?_⟩
    ext I
    rw [mem_ofNorm, Finset.mem_singleton]
    constructor
    · intro hI
      have hI0 := ne_bot_of_norm (pow_ne_zero _ hp.ne_zero) hI
      have hIe := eq_pow_of_factors hI0 (hfac hI)
      have h' := hI
      rw [hIe, map_pow, hPn, ← pow_mul] at h'
      have := Nat.pow_right_injective hp.two_le h'
      rw [hIe, show (normalizedFactors I).card = j by omega]
    · rintro rfl
      rw [map_pow, hPn, ← pow_mul]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro I hI
    rw [mem_ofNorm] at hI
    have hI0 := ne_bot_of_norm (pow_ne_zero _ hp.ne_zero) hI
    have hIe := eq_pow_of_factors hI0 (hfac hI)
    have h' := hI
    rw [hIe, map_pow, hPn, ← pow_mul] at h'
    exact hk ⟨_, (Nat.pow_right_injective hp.two_le h').symm⟩

/-- **Ramified**: one ideal of norm `3^k`, `(ω − 1)^k`. -/
theorem card_ofNorm_three (k : ℕ) : (ofNorm (3 ^ k)).card = 1 := by
  classical
  obtain ⟨hf, hn⟩ := ramified_three
  rw [Finset.card_eq_one]
  refine ⟨span {ω - 1} ^ k, ?_⟩
  ext I
  rw [mem_ofNorm, Finset.mem_singleton]
  constructor
  · intro hI
    have hI0 := ne_bot_of_norm (pow_ne_zero _ (by norm_num)) hI
    have hfac : ∀ R ∈ normalizedFactors I, R = span {ω - 1} := fun R hR => by
      have := mem_pFactors_of_mem Nat.prime_three hI hR
      rw [hf] at this; simpa using this
    have hIe := eq_pow_of_factors hI0 hfac
    have h' := hI
    rw [hIe, map_pow, hn] at h'
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h'
    rw [hIe, this]
  · rintro rfl
    rw [map_pow, hn]


section CountMult

open ArithmeticFunction

/-- `χ₋₃` as an arithmetic function into `ℤ`. -/
def chiA : ArithmeticFunction ℤ := ⟨chiInt, by simp [chiInt]⟩

theorem chiA_apply (n : ℕ) : chiA n = chiInt n := rfl

theorem chiInt_one : chiInt 1 = 1 := by simp [chiInt]

theorem chiInt_npow (p j : ℕ) : chiInt (p ^ j) = chiInt p ^ j := by
  induction j with
  | zero => simp [chiInt_one]
  | succ j ih => rw [pow_succ, chiInt_mul, ih, pow_succ]

theorem chiA_mult : chiA.IsMultiplicative :=
  ⟨by rw [chiA_apply, chiInt_one], fun {m n} _ => chiInt_mul m n⟩

/-- The number of ideals of norm `n`, as an arithmetic function. -/
noncomputable def rA : ArithmeticFunction ℤ := toArithmeticFunction fun n => ((ofNorm n).card : ℤ)

theorem rA_apply {n : ℕ} (hn : n ≠ 0) : rA n = (ofNorm n).card := by
  simp [rA, toArithmeticFunction, hn]

theorem card_ofNorm_mul {a b : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    (ofNorm (a * b)).card = (ofNorm a).card * (ofNorm b).card := by
  rw [ofNorm_mul hab ha hb, Finset.card_image_of_injOn (injOn_mul hab), Finset.card_product]

theorem card_ofNorm_one : (ofNorm 1).card = 1 := by
  have := card_ofNorm_three 0
  simpa using this

theorem rA_mult : rA.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by rw [rA_apply one_ne_zero, card_ofNorm_one]; rfl,
    fun {m n} hm hn hmn => ?_⟩
  rw [rA_apply (mul_ne_zero hm hn), rA_apply hm, rA_apply hn,
    card_ofNorm_mul hmn (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)]
  push_cast; ring

theorem sum_neg_one_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j = if 2 ∣ k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), show j + j + 1 = 2 * j + 1 by ring, pow_succ,
        pow_mul]
      norm_num
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]
      norm_num

/-- **The ideal count**: the number of ideals of `ℤ[ω]` of norm `n` is `Σ_{d ∣ n} χ₋₃(d)`. -/
theorem rA_eq : rA = chiA * (zeta : ArithmeticFunction ℤ) := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ rA_mult _
    (chiA_mult.mul isMultiplicative_zeta.natCast)]
  intro p k hp
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, rA_apply (pow_ne_zero _ hp.ne_zero)]
  simp only [chiA_apply, chiInt_npow]
  have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · have hp3 : p = 3 := by
      have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
    subst hp3
    rw [card_ofNorm_three, show chiInt 3 = 0 by simp [chiInt], Finset.sum_range_succ']
    simp
  · rw [card_ofNorm_split hp h1, show chiInt p = 1 by simp [chiInt, h1]]
    simp
  · rw [card_ofNorm_inert hp h2, show chiInt p = -1 by simp [chiInt, h2], sum_neg_one_pow]
    split_ifs <;> simp

end CountMult

section Kappa

/-- The partial sums of `χ₋₃` are `1` or `0`. -/
theorem sum_chiInt_Ioc (y : ℕ) :
    ∑ d ∈ Finset.Ioc 0 y, chiInt d = if y % 3 = 1 then 1 else 0 := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le y), ih]
    have h := Nat.mod_lt y (show 3 > 0 by norm_num)
    have e : (y + 1) % 3 = (y % 3 + 1) % 3 := by omega
    interval_cases hy : y % 3 <;> simp [chiInt, e]

/-- `χ₋₃` sums to `−1`, `0` or `1` over every interval. -/
theorem abs_sum_chiInt_Ioc_le (a b : ℕ) : |∑ d ∈ Finset.Ioc a b, (chiInt d : ℝ)| ≤ 1 := by
  rcases le_or_gt a b with hab | hab
  · have h := Finset.sum_Ioc_consecutive (fun d => (chiInt d : ℝ)) (Nat.zero_le a) hab
    have ha := sum_chiInt_Ioc a
    have hb := sum_chiInt_Ioc b
    have e : ∑ d ∈ Finset.Ioc a b, (chiInt d : ℝ) =
        ((∑ d ∈ Finset.Ioc 0 b, chiInt d : ℤ) : ℝ) - ((∑ d ∈ Finset.Ioc 0 a, chiInt d : ℤ) : ℝ) := by
      push_cast; linarith
    rw [e, ha, hb]
    split_ifs <;> norm_num
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero]; norm_num

/-- The pairs `1/(3k+1) − 1/(3k+2)` of the series `Σ_d χ₋₃(d)/d`. -/
noncomputable def bk (k : ℕ) : ℝ := 1 / (3 * k + 1) - 1 / (3 * k + 2)

theorem bk_nonneg (k : ℕ) : 0 ≤ bk k := by
  unfold bk
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (by positivity); linarith

theorem bk_le (k : ℕ) : bk k ≤ 1 / (3 * k + 1) - 1 / (3 * ((k + 1 : ℕ) : ℝ) + 1) := by
  unfold bk
  push_cast
  have : 1 / (3 * (k : ℝ) + 2) ≥ 1 / (3 * ((k : ℝ) + 1) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem sum_bk_le (q n : ℕ) : ∑ i ∈ Finset.range n, bk (i + q) ≤ 1 / (3 * q + 1) := by
  have htel : ∑ i ∈ Finset.range n, (1 / (3 * ((i + q : ℕ) : ℝ) + 1) -
      1 / (3 * ((i + q + 1 : ℕ) : ℝ) + 1)) = 1 / (3 * q + 1) - 1 / (3 * ((n + q : ℕ) : ℝ) + 1) := by
    have := Finset.sum_range_sub' (fun i => 1 / (3 * ((i + q : ℕ) : ℝ) + 1)) n
    simp only [show ∀ i, i + 1 + q = i + q + 1 from fun i => by ring] at this
    rw [this]; simp
  calc ∑ i ∈ Finset.range n, bk (i + q)
      ≤ ∑ i ∈ Finset.range n, (1 / (3 * ((i + q : ℕ) : ℝ) + 1) -
          1 / (3 * ((i + q + 1 : ℕ) : ℝ) + 1)) := Finset.sum_le_sum fun i _ => bk_le (i + q)
    _ = _ := htel
    _ ≤ 1 / (3 * q + 1) := by
        have : 0 ≤ 1 / (3 * ((n + q : ℕ) : ℝ) + 1) := by positivity
        linarith

theorem summable_bk : Summable bk :=
  summable_of_sum_range_le bk_nonneg (c := 1) fun n => by
    have := sum_bk_le 0 n
    simpa using this

/-- **`κ = Σ_d χ₋₃(d)/d = L(1, χ₋₃)`**, as the sum of the pairs `1/(3k+1) − 1/(3k+2)`. -/
noncomputable def kappa : ℝ := ∑' k, bk k

theorem kappa_pos : 0 < kappa := by
  have h := summable_bk.sum_add_tsum_nat_add 1
  have h0 : bk 0 = 1 / 2 := by norm_num [bk]
  have : 0 ≤ ∑' i, bk (i + 1) := tsum_nonneg fun i => bk_nonneg _
  rw [kappa, ← h, Finset.sum_range_one, h0]
  linarith

/-- The tail of `κ`'s series. -/
theorem kappa_tail (q : ℕ) :
    0 ≤ kappa - ∑ k ∈ Finset.range q, bk k ∧ kappa - ∑ k ∈ Finset.range q, bk k ≤ 1 / (3 * q + 1) := by
  have h := summable_bk.sum_add_tsum_nat_add q
  have e : kappa - ∑ k ∈ Finset.range q, bk k = ∑' i, bk (i + q) := by rw [kappa, ← h]; ring
  rw [e]
  exact ⟨tsum_nonneg fun i => bk_nonneg _,
    Real.tsum_le_of_sum_range_le (fun i => bk_nonneg _) fun n => sum_bk_le q n⟩

/-- `Σ_{d ≤ 3q} χ₋₃(d)/d` is the `q`-th partial sum of the pairs. -/
theorem sum_chi_div_three_mul (q : ℕ) :
    ∑ d ∈ Finset.Ioc 0 (3 * q), (chiInt d : ℝ) / d = ∑ k ∈ Finset.range q, bk k := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 * q + 2 + 1 by ring, Finset.sum_Ioc_succ_top (by omega),
      Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), ih,
      Finset.sum_range_succ]
    have h1 : chiInt (3 * q + 1) = 1 := by simp [chiInt]
    have h2 : chiInt (3 * q + 1 + 1) = -1 := by simp [chiInt]; omega
    have h3 : chiInt (3 * q + 2 + 1) = 0 := by simp [chiInt]; omega
    rw [show 3 * q + 2 = 3 * q + 1 + 1 by ring] at *
    rw [h1, h2, h3]
    unfold bk; push_cast; ring

/-- **`|Σ_{d ≤ U} χ₋₃(d)/d − κ| ≤ 3/(U + 1)`.** -/
theorem abs_sum_chi_div_sub_kappa_le (U : ℕ) :
    |∑ d ∈ Finset.Ioc 0 U, (chiInt d : ℝ) / d - kappa| ≤ 3 / (U + 1) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ U = 3 * q + r := ⟨U / 3, U % 3, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod U 3).symm⟩
  obtain ⟨t0, t1⟩ := kappa_tail q
  have hq : (0 : ℝ) < 3 * q + 1 := by positivity
  have hfin : 1 / (3 * (q : ℝ) + 1) ≤ 3 / (((3 * q + r : ℕ) : ℝ) + 1) := by
    rw [div_le_div_iff₀ hq (by positivity)]; push_cast
    have : (r : ℝ) ≤ 2 := by exact_mod_cast (show r ≤ 2 by omega)
    nlinarith
  -- the partial sum is `P(q) + δ` with `0 ≤ δ ≤ 1/(3q+1)`
  obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ δ ≤ 1 / (3 * q + 1) ∧
      ∑ d ∈ Finset.Ioc 0 (3 * q + r), (chiInt d : ℝ) / d = ∑ k ∈ Finset.range q, bk k + δ := by
    interval_cases r
    · exact ⟨0, le_rfl, by positivity, by rw [add_zero, add_zero, sum_chi_div_three_mul]⟩
    · refine ⟨1 / (3 * q + 1), by positivity, le_rfl, ?_⟩
      rw [Finset.sum_Ioc_succ_top (by omega), sum_chi_div_three_mul]
      have h1 : chiInt (3 * q + 1) = 1 := by simp [chiInt]
      rw [show 3 * q + 0 + 1 = 3 * q + 1 by ring] at *
      rw [h1]; push_cast; ring
    · refine ⟨1 / (3 * q + 1) - 1 / (3 * q + 2), ?_, ?_, ?_⟩
      · rw [sub_nonneg]; exact one_div_le_one_div_of_le (by positivity) (by linarith)
      · have : 0 ≤ 1 / (3 * (q : ℝ) + 2) := by positivity
        linarith
      · rw [show 3 * q + 2 = 3 * q + 1 + 1 by ring, Finset.sum_Ioc_succ_top (by omega),
          Finset.sum_Ioc_succ_top (by omega), sum_chi_div_three_mul]
        have h1 : chiInt (3 * q + 1) = 1 := by simp [chiInt]
        have h2 : chiInt (3 * q + 1 + 1) = -1 := by simp [chiInt]; omega
        rw [h1, h2]; push_cast; ring
  rw [hδ, abs_le]
  constructor <;> linarith

end Kappa

section Hyperbola

open ArithmeticFunction

/-- The number of nonzero ideals of `ℤ[ω]` of norm at most `x`. -/
noncomputable def idealCount (x : ℝ) : ℕ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ofNorm n).card

/-- The count as `Σ_{n ≤ N} χ₋₃(n)·⌊N/n⌋`. -/
theorem sum_card_ofNorm (N : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 N, (ofNorm n).card : ℕ) : ℝ) =
      ∑ n ∈ Finset.Ioc 0 N, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) := by
  have h : ((∑ n ∈ Finset.Ioc 0 N, (ofNorm n).card : ℕ) : ℤ) =
      ∑ n ∈ Finset.Ioc 0 N, chiInt n * ((N / n : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl fun n hn => (rA_apply (Finset.mem_Ioc.1 hn).1.ne').symm, rA_eq,
      sum_Ioc_mul_zeta_eq_sum]
    rfl
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h' ⊢
  exact h'

theorem abs_chiInt_le (n : ℕ) : |(chiInt n : ℝ)| ≤ 1 := by
  unfold chiInt; split_ifs <;> norm_num

/-- The pairs `(n, m)` with `U < n` and `nm ≤ N`, counted either way. -/
theorem mem_swap {U N n m : ℕ} :
    (n ∈ Finset.Ioc U N ∧ m ∈ Finset.Ioc 0 (N / n)) ↔
      (n ∈ Finset.Ioc U (N / m) ∧ m ∈ Finset.Ioc 0 N) := by
  simp only [Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hUn, hnN⟩, hm0, hmn⟩
    have hn0 : 0 < n := by omega
    have h1 : m * n ≤ N := (Nat.le_div_iff_mul_le hn0).1 hmn
    refine ⟨⟨hUn, (Nat.le_div_iff_mul_le hm0).2 (by rw [mul_comm]; exact h1)⟩, hm0, ?_⟩
    exact le_trans hmn (Nat.div_le_self N n)
  · rintro ⟨⟨hUn, hnm⟩, hm0, hmN⟩
    have hn0 : 0 < n := by omega
    have h1 : n * m ≤ N := (Nat.le_div_iff_mul_le hm0).1 hnm
    exact ⟨⟨hUn, le_trans hnm (Nat.div_le_self N m)⟩, hm0,
      (Nat.le_div_iff_mul_le hn0).2 (by rw [mul_comm]; exact h1)⟩

/-- **Dirichlet's hyperbola method**: `|Σ_{n ≤ N} χ₋₃(n)⌊N/n⌋ − κN| ≤ 5√N`. -/
theorem hyperbola (N : ℕ) :
    |∑ n ∈ Finset.Ioc 0 N, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) - kappa * N| ≤ 5 * √N := by
  set U := Nat.sqrt N with hUdef
  have hUN : U ≤ N := Nat.sqrt_le_self N
  have hsq1 : √(N : ℝ) ≤ U + 1 := Real.real_sqrt_le_nat_sqrt_succ
  have hsq0 : (U : ℝ) ≤ √N := Real.nat_sqrt_le_real_sqrt
  have hsqrt0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have hNU : (N : ℝ) / (U + 1) ≤ √N := by
    rw [div_le_iff₀ (by positivity)]
    calc (N : ℝ) = √N * √N := (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
      _ ≤ √N * (U + 1) := mul_le_mul_of_nonneg_left hsq1 hsqrt0
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUN]
  -- the short range `n ≤ U`
  have e1 : |∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) -
      N * ∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n| ≤ U := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.Ioc 0 U, |(chiInt n : ℝ) * ((N / n : ℕ) : ℝ) - N * ((chiInt n : ℝ) / n)|
        ≤ ∑ n ∈ Finset.Ioc 0 U, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
          have e : (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) - N * ((chiInt n : ℝ) / n) =
              (chiInt n : ℝ) * (((N / n : ℕ) : ℝ) - N / n) := by ring
          rw [e, abs_mul]
          have hfl : ((N / n : ℕ) : ℝ) ≤ N / n := Nat.cast_div_le
          have hfl2 : (N : ℝ) / n < ((N / n : ℕ) : ℝ) + 1 := by
            rw [div_lt_iff₀ hn0]
            have := Nat.lt_div_mul_add (a := N) (b := n) (by exact_mod_cast hn0)
            have h' : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast this
            linarith
          have habs : |((N / n : ℕ) : ℝ) - N / n| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          calc |(chiInt n : ℝ)| * |((N / n : ℕ) : ℝ) - N / n| ≤ 1 * 1 :=
                mul_le_mul (abs_chiInt_le n) habs (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = U := by simp
  have e2 : |(N : ℝ) * ∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n - kappa * N| ≤ 3 * √N := by
    rw [show (N : ℝ) * ∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n - kappa * N =
      N * (∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n - kappa) by ring, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg N)]
    calc (N : ℝ) * |∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n - kappa|
        ≤ N * (3 / (U + 1)) := mul_le_mul_of_nonneg_left (abs_sum_chi_div_sub_kappa_le U)
          (Nat.cast_nonneg N)
      _ = 3 * (N / (U + 1)) := by ring
      _ ≤ 3 * √N := by linarith
  -- the long range `n > U`, by swapping the order of summation
  have e3 : |∑ n ∈ Finset.Ioc U N, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ)| ≤ √N := by
    have hswap : ∑ n ∈ Finset.Ioc U N, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) =
        ∑ m ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Ioc U (N / m), (chiInt n : ℝ) := by
      have h1 : ∀ n, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) =
          ∑ m ∈ Finset.Ioc 0 (N / n), (chiInt n : ℝ) := fun n => by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero, mul_comm]
      simp_rw [h1]
      exact Finset.sum_comm' fun n m => mem_swap
    rw [hswap]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ Finset.Ioc 0 N, |∑ n ∈ Finset.Ioc U (N / m), (chiInt n : ℝ)|
        ≤ ∑ m ∈ Finset.Ioc 0 N, (if m ≤ N / (U + 1) then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm0 : 0 < m := (Finset.mem_Ioc.1 hm).1
          split_ifs with hle
          · exact abs_sum_chiInt_Ioc_le U (N / m)
          · have : N / m ≤ U := by
              by_contra hc
              apply hle
              rw [Nat.le_div_iff_mul_le (by omega)]
              have := (Nat.le_div_iff_mul_le hm0).1 (show U + 1 ≤ N / m by omega)
              rw [mul_comm]; exact this
            rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero]
      _ ≤ ∑ m ∈ Finset.Ioc 0 (N / (U + 1)), (1 : ℝ) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            simp only [Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
            exact ⟨hm.1.1, hm.2⟩
          · intros; norm_num
      _ = ((N / (U + 1) : ℕ) : ℝ) := by simp
      _ ≤ (N : ℝ) / ((U + 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ √N := by push_cast; exact hNU
  calc |∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) +
        ∑ n ∈ Finset.Ioc U N, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) - kappa * N|
      ≤ |∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) -
          N * ∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n| +
        |(N : ℝ) * ∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n - kappa * N| +
        |∑ n ∈ Finset.Ioc U N, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ)| := by
        have := abs_add_three (∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ) -
          N * ∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n)
          ((N : ℝ) * ∑ n ∈ Finset.Ioc 0 U, (chiInt n : ℝ) / n - kappa * N)
          (∑ n ∈ Finset.Ioc U N, (chiInt n : ℝ) * ((N / n : ℕ) : ℝ))
        convert this using 2; ring
    _ ≤ U + 3 * √N + √N := by linarith
    _ ≤ 5 * √N := by linarith

/-- **The ideal theorem for `ℚ(√−3)` with a square-root error**:
`|#{𝔞 ≠ 0 : N𝔞 ≤ x} − κx| ≤ 5√x + κ`, `κ = L(1, χ₋₃)`. -/
theorem abs_idealCount_sub_le {x : ℝ} (hx : 0 ≤ x) :
    |(idealCount x : ℝ) - kappa * x| ≤ 5 * √x + kappa := by
  set N := ⌊x⌋₊ with hNdef
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx
  have hN' : x < N + 1 := Nat.lt_floor_add_one x
  have h := hyperbola N
  rw [← sum_card_ofNorm] at h
  have hk := kappa_pos
  calc |(idealCount x : ℝ) - kappa * x|
      = |((∑ n ∈ Finset.Ioc 0 N, (ofNorm n).card : ℕ) : ℝ) - kappa * N - kappa * (x - N)| := by
        rw [idealCount, ← hNdef]; congr 1; ring
    _ ≤ |((∑ n ∈ Finset.Ioc 0 N, (ofNorm n).card : ℕ) : ℝ) - kappa * N| + |kappa * (x - N)| :=
        abs_sub _ _
    _ ≤ 5 * √N + kappa := by
        refine add_le_add h ?_
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
    _ ≤ 5 * √x + kappa := by gcongr

end Hyperbola

section Multiples

/-- The nonzero ideals of norm at most `x`. -/
noncomputable def idealsLe (x : ℝ) : Finset (Ideal (𝓞 K)) := (Finset.Ioc 0 ⌊x⌋₊).biUnion ofNorm

theorem mem_idealsLe {x : ℝ} {J : Ideal (𝓞 K)} :
    J ∈ idealsLe x ↔ 0 < absNorm J ∧ absNorm J ≤ ⌊x⌋₊ := by
  simp only [idealsLe, Finset.mem_biUnion, Finset.mem_Ioc, mem_ofNorm]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact hn
  · intro h; exact ⟨_, h, rfl⟩

theorem card_idealsLe (x : ℝ) : (idealsLe x).card = idealCount x := by
  rw [idealsLe, Finset.card_biUnion, idealCount]
  intro m _ n _ hmn
  rw [Function.onFun, Finset.disjoint_left]
  intro J hm hn
  exact hmn ((mem_ofNorm.1 hm).symm.trans (mem_ofNorm.1 hn))

open Classical in
/-- **The multiples of `D` of norm at most `Y`**: there are `#{𝔞 : N𝔞 ≤ Y/N(D)}` of them. -/
theorem card_multiples {D : Ideal (𝓞 K)} (hD : D ≠ ⊥) {Y : ℝ} (hY : 0 ≤ Y) :
    ((idealsLe Y).filter (fun J => D ∣ J)).card = idealCount (Y / absNorm D) := by
  classical
  have hND : 0 < absNorm D := Nat.pos_of_ne_zero (fun h => hD (Ideal.absNorm_eq_zero_iff.1 h))
  have hNDr : (0 : ℝ) < absNorm D := by exact_mod_cast hND
  rw [← card_idealsLe]
  symm
  refine Finset.card_bij (fun J _ => D * J) ?_ ?_ ?_
  · intro J hJ
    rw [mem_idealsLe] at hJ
    rw [Finset.mem_filter, mem_idealsLe, map_mul]
    refine ⟨⟨Nat.mul_pos hND hJ.1, ?_⟩, dvd_mul_right D J⟩
    rw [Nat.le_floor_iff hY]
    have h2 := (Nat.le_floor_iff (div_nonneg hY hNDr.le)).1 hJ.2
    rw [le_div_iff₀ hNDr] at h2
    push_cast; linarith
  · intro J _ J' _ h
    exact mul_left_cancel₀ (by simpa using hD) h
  · intro J hJ
    rw [Finset.mem_filter, mem_idealsLe] at hJ
    obtain ⟨⟨h0, hle⟩, J', rfl⟩ := hJ
    refine ⟨J', ?_, rfl⟩
    rw [map_mul] at h0 hle
    rw [mem_idealsLe]
    refine ⟨Nat.pos_of_mul_pos_left h0, ?_⟩
    rw [Nat.le_floor_iff (div_nonneg hY hNDr.le), le_div_iff₀ hNDr]
    have h2 := (Nat.le_floor_iff hY).1 hle
    push_cast at h2; linarith

end Multiples
end IdealCount

end Eis

#print axioms Eis.card_ofNorm_split
#print axioms Eis.card_ofNorm_inert
#print axioms Eis.card_ofNorm_three
#print axioms Eis.rA_eq
#print axioms Eis.sum_chiInt_Ioc
#print axioms Eis.abs_sum_chiInt_Ioc_le
#print axioms Eis.kappa_pos
#print axioms Eis.kappa_tail
#print axioms Eis.abs_sum_chi_div_sub_kappa_le
#print axioms Eis.hyperbola
#print axioms Eis.abs_idealCount_sub_le
#print axioms Eis.card_idealsLe
#print axioms Eis.card_multiples
