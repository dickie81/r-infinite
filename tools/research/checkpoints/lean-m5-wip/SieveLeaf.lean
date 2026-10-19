import SieveRanges
import SieveCount

open Real Finset

namespace SieveLeaf

open SieveBrun SieveRanges

/-- The ranges `[w^{2^{−j−1}}, w^{2^{−j}})`, `j < J`. -/
noncomputable def T (w : ℝ) (J : ℕ) (j : Fin J) : Finset ℕ := rng (w ^ ((1 / 2 : ℝ) ^ ((j : ℕ) + 1)))

/-- The density of the sieve: `1/p`, or `0` for `p ∣ q`. -/
noncomputable def g (q p : ℕ) : ℝ := if p ∣ q then 0 else 1 / p

theorem prime_of_mem_T {w : ℝ} {J : ℕ} {j : Fin J} {p : ℕ} (hp : p ∈ T w J j) : p.Prime :=
  (mem_rng.1 hp).1

theorem lt_w_of_mem_T {w : ℝ} (hw : 1 ≤ w) {J : ℕ} {j : Fin J} {p : ℕ} (hp : p ∈ T w J j) : (p : ℝ) < w :=
  lt_w_of_mem_rng hw hp

theorem T_disjoint {w : ℝ} (hw : 1 ≤ w) (J : ℕ) :
    (Set.univ : Set (Fin J)).PairwiseDisjoint (T w J) := by
  intro i _ j _ hij
  exact rng_disjoint hw (fun h => hij (Fin.ext h))

/-- The sifted condition by the ranges is the condition by the primes below `w`. -/
theorem sifted_iff {w : ℝ} (hw : 1 ≤ w) {J : ℕ} (hJ : w ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (n : ℕ) :
    (∀ j, ∀ p ∈ T w J j, ¬ p ∣ n) ↔ ∀ p < ⌈w⌉₊, p.Prime → ¬ p ∣ n := by
  constructor
  · intro h p hpw hp
    obtain ⟨j, hj, hmem⟩ := cover hJ hp (Nat.lt_ceil.1 hpw)
    exact h ⟨j, hj⟩ p hmem
  · intro h j p hp
    exact h p (Nat.lt_ceil.2 (lt_w_of_mem_T hw hp)) (prime_of_mem_T hp)

/-- For `s_j ⊆ T_j`, divisibility by all the `p ∈ s_j` is divisibility by their product. -/
theorem dvd_iff {w : ℝ} {J : ℕ} (s : Fin J → Finset ℕ) (hs : ∀ j, s j ⊆ T w J j) (n : ℕ) :
    (∀ j, ∀ p ∈ s j, p ∣ n) ↔ (∏ p ∈ Finset.univ.biUnion s, p) ∣ n := by
  constructor
  · intro h
    refine Finset.prod_primes_dvd n (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hp
      exact (prime_of_mem_T (hs j hj)).prime
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hp
      exact h j p hj
  · intro h j p hp
    exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hp⟩)) h

theorem prod_g_eq {w : ℝ} (hw : 1 ≤ w) {J : ℕ} (s : Fin J → Finset ℕ) (hs : ∀ j, s j ⊆ T w J j) (f : ℕ → ℝ) :
    ∏ j, ∏ p ∈ s j, f p = ∏ p ∈ Finset.univ.biUnion s, f p := by
  rw [Finset.prod_biUnion]
  intro i _ j _ hij
  exact Disjoint.mono (hs i) (hs j) (T_disjoint hw J (Set.mem_univ i) (Set.mem_univ j) hij)

/-- `m`, whose primes are at least `w`, is prime to the product of primes below `w`. -/
theorem coprime_m {w : ℝ} (hw : 1 ≤ w) {J : ℕ} (s : Fin J → Finset ℕ) (hs : ∀ j, s j ⊆ T w J j) {m : ℕ}
    (hmw : ∀ p : ℕ, p.Prime → p ∣ m → w ≤ p) : Nat.Coprime m (∏ p ∈ Finset.univ.biUnion s, p) := by
  refine Nat.Coprime.prod_right fun p hp => ?_
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hp
  have hpp := prime_of_mem_T (hs j hj)
  have hpw := lt_w_of_mem_T hw (hs j hj)
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun hdvd => ?_))
  linarith [hmw p hpp hdvd]

/-- **The model for `A`.** For `s_j ⊆ T_j`, `#{n ∈ A_m : p ∣ n for p ∈ s_j}` is `X ∏ g` within `1`. -/
theorem hR_A {q a m N₁ N₂ : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) (hm : 0 < m) (hmq : Nat.Coprime m q)
    {w : ℝ} (hw : 1 ≤ w) (hmw : ∀ p : ℕ, p.Prime → p ∣ m → w ≤ p) {J : ℕ} (hN : N₁ ≤ N₂)
    (s : Fin J → Finset ℕ) (hs : ∀ j, s j ⊆ T w J j) :
    |((({n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n}).filter fun n => ∀ j, ∀ p ∈ s j, p ∣ n).card : ℝ) -
      ((N₂ : ℝ) - N₁) / (m * q) * ∏ j, ∏ p ∈ s j, g q p| ≤ 1 := by
  set U := Finset.univ.biUnion s with hU
  set D := ∏ p ∈ U, p with hD
  have hprime : ∀ p ∈ U, p.Prime := fun p hp => by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hp
    exact prime_of_mem_T (hs j hj)
  rw [prod_g_eq hw s hs]
  have hfilt : ({n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n}).filter (fun n => ∀ j, ∀ p ∈ s j, p ∣ n) =
      {n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n ∧ D ∣ n} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun n _ => ?_
    rw [dvd_iff s hs n, and_assoc]
  rw [hfilt]
  by_cases hbad : ∃ p ∈ U, p ∣ q
  · -- no `n ≡ a` is divisible by a prime of `q`
    obtain ⟨p, hpU, hpq⟩ := hbad
    have hzero : {n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n ∧ D ∣ n} = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro n - ⟨hna, -, hDn⟩
      have hpn : p ∣ n := dvd_trans (Finset.dvd_prod_of_mem _ hpU) hDn
      have hpa : p ∣ a := by
        have := (Nat.ModEq.of_dvd hpq hna)
        exact (Nat.ModEq.dvd_iff this (dvd_refl p)).1 hpn
      have : p ∣ Nat.gcd a q := Nat.dvd_gcd hpa hpq
      rw [ha] at this
      exact (hprime p hpU).one_lt.ne' (Nat.dvd_one.1 this)
    have hg0 : ∏ p ∈ U, g q p = 0 := Finset.prod_eq_zero hpU (by simp [g, hpq])
    rw [hzero, hg0]
    simp
  · push Not at hbad
    have hDq : Nat.Coprime D q := Nat.Coprime.prod_left fun p hp =>
      (Nat.Prime.coprime_iff_not_dvd (hprime p hp)).2 (hbad p hp)
    have hmD : Nat.Coprime m D := coprime_m hw s hs hmw
    have hD0 : 0 < D := Finset.prod_pos fun p hp => (hprime p hp).pos
    have hset : {n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n ∧ D ∣ n} = {n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m * D ∣ n} := by
      refine Finset.filter_congr fun n _ => ?_
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Nat.Coprime.mul_dvd_of_dvd_of_dvd hmD h2 h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, dvd_trans (dvd_mul_right m D) h2, dvd_trans (dvd_mul_left D m) h2⟩
    have hgU : ∏ p ∈ U, g q p = 1 / (D : ℝ) := by
      rw [hD, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      simp [g, hbad p hp]
    rw [hset, hgU]
    have h := SieveCount.card_A hq (Nat.mul_pos hm hD0) (Nat.coprime_mul_iff_left.2 ⟨hmq, hDq⟩) hN a
    have heq : ((N₂ : ℝ) - N₁) / (m * q) * (1 / (D : ℝ)) = ((N₂ : ℝ) - N₁) / (((m * D : ℕ) : ℝ) * q) := by
      push_cast; field_simp
    rw [heq]
    exact h

/-- **The model for `B`.** For `s_j ⊆ T_j`, `#{n ∈ B_m : p ∣ n for p ∈ s_j}` is `φ(q)X ∏ g` within `φ(q)`. -/
theorem hR_B {q m N₁ N₂ : ℕ} (hq : 0 < q) (hm : 0 < m) (hmq : Nat.Coprime m q)
    {w : ℝ} (hw : 1 ≤ w) (hmw : ∀ p : ℕ, p.Prime → p ∣ m → w ≤ p) {J : ℕ} (hN : N₁ ≤ N₂)
    (s : Fin J → Finset ℕ) (hs : ∀ j, s j ⊆ T w J j) :
    |((({n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n}).filter fun n => ∀ j, ∀ p ∈ s j, p ∣ n).card : ℝ) -
      q.totient * (((N₂ : ℝ) - N₁) / (m * q)) * ∏ j, ∏ p ∈ s j, g q p| ≤ q.totient := by
  set U := Finset.univ.biUnion s with hU
  set D := ∏ p ∈ U, p with hD
  have hprime : ∀ p ∈ U, p.Prime := fun p hp => by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hp
    exact prime_of_mem_T (hs j hj)
  rw [prod_g_eq hw s hs]
  have hfilt : ({n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n}).filter (fun n => ∀ j, ∀ p ∈ s j, p ∣ n) =
      {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n ∧ D ∣ n} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun n _ => ?_
    rw [dvd_iff s hs n, and_assoc]
  rw [hfilt]
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  by_cases hbad : ∃ p ∈ U, p ∣ q
  · obtain ⟨p, hpU, hpq⟩ := hbad
    have hzero : {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n ∧ D ∣ n} = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro n - ⟨hnq, -, hDn⟩
      have hpn : p ∣ n := dvd_trans (Finset.dvd_prod_of_mem _ hpU) hDn
      have : p ∣ Nat.gcd n q := Nat.dvd_gcd hpn hpq
      rw [hnq] at this
      exact (hprime p hpU).one_lt.ne' (Nat.dvd_one.1 this)
    have hg0 : ∏ p ∈ U, g q p = 0 := Finset.prod_eq_zero hpU (by simp [g, hpq])
    rw [hzero, hg0]
    simp
  · push Not at hbad
    have hDq : Nat.Coprime D q := Nat.Coprime.prod_left fun p hp =>
      (Nat.Prime.coprime_iff_not_dvd (hprime p hp)).2 (hbad p hp)
    have hmD : Nat.Coprime m D := coprime_m hw s hs hmw
    have hD0 : 0 < D := Finset.prod_pos fun p hp => (hprime p hp).pos
    have hset : {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n ∧ D ∣ n} =
        {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m * D ∣ n} := by
      refine Finset.filter_congr fun n _ => ?_
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Nat.Coprime.mul_dvd_of_dvd_of_dvd hmD h2 h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, dvd_trans (dvd_mul_right m D) h2, dvd_trans (dvd_mul_left D m) h2⟩
    have hgU : ∏ p ∈ U, g q p = 1 / (D : ℝ) := by
      rw [hD, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      simp [g, hbad p hp]
    rw [hset, hgU]
    have h := SieveCount.card_B hq (Nat.mul_pos hm hD0) (Nat.coprime_mul_iff_left.2 ⟨hmq, hDq⟩) hN
    have heq : q.totient * (((N₂ : ℝ) - N₁) / (m * q)) * (1 / (D : ℝ)) =
        q.totient * (((N₂ : ℝ) - N₁) / (((m * D : ℕ) : ℝ) * q)) := by
      push_cast; field_simp
    rw [heq]
    exact h

theorem g_nonneg (q p : ℕ) : 0 ≤ g q p := by
  unfold g; split_ifs <;> positivity

theorem g_le_one {q p : ℕ} (hp : 1 ≤ p) : g q p ≤ 1 := by
  unfold g; split_ifs
  · norm_num
  · rw [div_le_one (by exact_mod_cast hp)]; exact_mod_cast hp

theorem div_bound {S φ X V G N c : ℝ} (hφ : 0 < φ) (h : |S - φ * X * V| ≤ φ * X * G + c * φ * N) :
    |S / φ - X * V| ≤ X * G + c * 1 * N := by
  have e1 : S / φ - X * V = (S - φ * X * V) / φ := by field_simp
  rw [e1, abs_div, abs_of_pos hφ, div_le_iff₀ hφ]
  calc |S - φ * X * V| ≤ φ * X * G + c * φ * N := h
    _ = (X * G + c * 1 * N) * φ := by ring

/-- **A leaf, for `A`.** The `n ∈ (N₁, N₂]` with `n ≡ a (mod q)`, `m ∣ n` and no prime factor below `w` number
`X ∏_j ∏_{T_j} (1 − g)`, `X = (N₂ − N₁)/(mq)`, within the fundamental lemma's error. -/
theorem leaf_A {q a m N₁ N₂ : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) (hm : 0 < m) (hmq : Nat.Coprime m q)
    {w : ℝ} (hw : 1 ≤ w) (hmw : ∀ p : ℕ, p.Prime → p ∣ m → w ≤ p) {J : ℕ} (hJ : w ^ ((1 / 2 : ℝ) ^ J) ≤ 2)
    (hN : N₁ ≤ N₂) (k : Fin J → ℕ) (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j) :
    |((#{n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n ∧ ∀ p < ⌈w⌉₊, p.Prime → ¬ p ∣ n} : ℕ) : ℝ) -
        ((N₂ : ℝ) - N₁) / (m * q) * ∏ j, ∏ p ∈ T w J j, (1 - g q p)| ≤
      ((N₂ : ℝ) - N₁) / (m * q) * ∑ j, esym (T w J j) (g q) (k j) *
          ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k i) +
        (J + 1) * 1 * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T w J j).card.choose i : ℝ) := by
  have hX : 0 ≤ ((N₂ : ℝ) - N₁) / (m * q) := by
    have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
    apply div_nonneg (by linarith); positivity
  have h := fundamental (C := {n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n}) (T w J) k hk hk1 hX
    (g := g q) (fun j p _ => g_nonneg q p) (fun j p hp => g_le_one (prime_of_mem_T hp).one_lt.le) (R := 1)
    (fun s hs => by convert hR_A hq ha hm hmq hw hmw hN s hs)
  have hset : ({n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n}).filter (fun n => ∀ j, ∀ p ∈ T w J j, ¬ p ∣ n) =
      {n ∈ Ioc N₁ N₂ | n ≡ a [MOD q] ∧ m ∣ n ∧ ∀ p < ⌈w⌉₊, p.Prime → ¬ p ∣ n} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun n _ => ?_
    rw [sifted_iff hw hJ n, and_assoc]
  rw [← hset]
  convert h using 3
  · congr
  · simp

/-- **A leaf, for `B/φ(q)`.** The same for the `n` prime to `q`, divided by `φ(q)`. -/
theorem leaf_B {q m N₁ N₂ : ℕ} (hq : 0 < q) (hm : 0 < m) (hmq : Nat.Coprime m q)
    {w : ℝ} (hw : 1 ≤ w) (hmw : ∀ p : ℕ, p.Prime → p ∣ m → w ≤ p) {J : ℕ} (hJ : w ^ ((1 / 2 : ℝ) ^ J) ≤ 2)
    (hN : N₁ ≤ N₂) (k : Fin J → ℕ) (hk : ∀ j, Even (k j)) (hk1 : ∀ j, 1 ≤ k j) :
    |((#{n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n ∧ ∀ p < ⌈w⌉₊, p.Prime → ¬ p ∣ n} : ℕ) : ℝ) /
          q.totient - ((N₂ : ℝ) - N₁) / (m * q) * ∏ j, ∏ p ∈ T w J j, (1 - g q p)| ≤
      ((N₂ : ℝ) - N₁) / (m * q) * ∑ j, esym (T w J j) (g q) (k j) *
          ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k i) +
        (J + 1) * 1 * ∏ j, ∑ i ∈ Finset.range (k j + 1), ((T w J j).card.choose i : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hX : 0 ≤ q.totient * (((N₂ : ℝ) - N₁) / (m * q)) := by
    have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
    apply mul_nonneg hφ.le; apply div_nonneg (by linarith); positivity
  have h := fundamental (C := {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n}) (T w J) k hk hk1 hX
    (g := g q) (fun j p _ => g_nonneg q p) (fun j p hp => g_le_one (prime_of_mem_T hp).one_lt.le)
    (R := q.totient) (fun s hs => by convert hR_B hq hm hmq hw hmw hN s hs)
  have hset : ({n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n}).filter (fun n => ∀ j, ∀ p ∈ T w J j, ¬ p ∣ n) =
      {n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ m ∣ n ∧ ∀ p < ⌈w⌉₊, p.Prime → ¬ p ∣ n} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun n _ => ?_
    rw [sifted_iff hw hJ n, and_assoc]
  rw [← hset]
  have h2 := div_bound hφ h
  convert h2 using 3
  · congr
  · simp

/-! ### The leaves' relative error -/

theorem exp_neg_two_mul_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-(2 * x)) ≤ 1 - x := by
  have he := Real.add_one_le_exp (2 * x)
  have hpos : 0 < Real.exp (2 * x) := Real.exp_pos _
  rw [Real.exp_neg, inv_le_comm₀ hpos (by linarith), ← one_div, div_le_iff₀ (by linarith)]
  nlinarith

theorem g_le_inv (q p : ℕ) : g q p ≤ 1 / p := by
  unfold g; split_ifs
  · positivity
  · exact le_rfl

/-- The relative error of a leaf: with the levels `k_j = k + 2j` and `C₀` bounding the ranges' prime sums, the gap
is at most `V·ζ(k)`, `ζ(k) = e^{2C₀}(2C₀^k/k!)·exp(e^{2C₀}·2C₀^{k+1}/(k + 1)!)`. -/
theorem leaf_gap {w : ℝ} (hw : 1 ≤ w) (J q : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k)
    (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ∑ j : Fin J, esym (T w J j) (g q) (k + 2 * j) *
        ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k + 2 * i) ≤
      (∏ j : Fin J, ∏ p ∈ T w J j, (1 - g q p)) *
        (Real.exp (2 * C₀) * (2 * (C₀ ^ k / k.factorial)) *
          Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (k + 1) / (k + 1).factorial)))) := by
  set c₀ := Real.exp (-(2 * C₀)) with hc₀
  have hc₀pos : 0 < c₀ := Real.exp_pos _
  have hc₀inv : c₀⁻¹ = Real.exp (2 * C₀) := by rw [hc₀, Real.exp_neg, inv_inv]
  have hA : ∀ j : Fin J, 1 ≤ w ^ ((1 / 2 : ℝ) ^ ((j : ℕ) + 1)) := fun j => Real.one_le_rpow hw (by positivity)
  have hsum : ∀ j : Fin J, ∑ p ∈ T w J j, g q p ≤ C₀ := fun j =>
    (Finset.sum_le_sum fun p _ => g_le_inv q p).trans (hC _ (hA j))
  have hV : ∀ j : Fin J, c₀ ≤ ∏ p ∈ T w J j, (1 - g q p) := fun j => by
    have h1 : ∏ p ∈ T w J j, Real.exp (-(2 * g q p)) ≤ ∏ p ∈ T w J j, (1 - g q p) :=
      Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_T hp).two_le
        have hg : g q p ≤ 1 / 2 := (g_le_inv q p).trans (by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
        exact exp_neg_two_mul_le (g_nonneg q p) hg
    rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.mul_sum] at h1
    refine le_trans ?_ h1
    rw [hc₀, Real.exp_le_exp]
    have := hsum j
    linarith
  have hgap := gap_le (T w J) (fun j : Fin J => k + 2 * (j : ℕ)) (fun j => by
      rcases hk with ⟨r, hr⟩; exact ⟨r + j, by omega⟩)
    (g := g q) (fun j p _ => g_nonneg q p) (fun j p hp => g_le_one (prime_of_mem_T hp).one_lt.le) hC₀ hc₀pos
    hsum hV
  refine hgap.trans ?_
  have hV0 : 0 ≤ ∏ j : Fin J, ∏ p ∈ T w J j, (1 - g q p) :=
    Finset.prod_nonneg fun j _ => le_trans hc₀pos.le (hV j)
  -- the sum of the levels
  have hs1 : ∑ j : Fin J, C₀ ^ (k + 2 * (j : ℕ)) / ((k + 2 * (j : ℕ)).factorial : ℝ) ≤ 2 * (C₀ ^ k / k.factorial) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => C₀ ^ (k + 2 * j) / ((k + 2 * j).factorial : ℝ)) J]
    exact sum_levels_le hC₀ hkC J
  -- the product of the corrections
  have hs2 : ∏ i : Fin J, (1 + C₀ ^ (k + 2 * (i : ℕ) + 1) / (((k + 2 * (i : ℕ) + 1).factorial : ℝ) * c₀)) ≤
      Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (k + 1) / (k + 1).factorial))) := by
    refine (prod_one_add_le_exp _ _ fun i _ => by positivity).trans (Real.exp_le_exp.2 ?_)
    have hkC' : 2 * C₀ ^ 2 ≤ (((k + 1 : ℕ) : ℝ) + 1) * ((k + 1 : ℕ) + 2) := by push_cast; nlinarith
    have h := sum_levels_le hC₀ hkC' J
    rw [← Fin.sum_univ_eq_sum_range (fun j => C₀ ^ (k + 1 + 2 * j) / ((k + 1 + 2 * j).factorial : ℝ)) J] at h
    calc ∑ i : Fin J, C₀ ^ (k + 2 * (i : ℕ) + 1) / (((k + 2 * (i : ℕ) + 1).factorial : ℝ) * c₀)
        = c₀⁻¹ * ∑ i : Fin J, C₀ ^ (k + 1 + 2 * (i : ℕ)) / ((k + 1 + 2 * (i : ℕ)).factorial : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show k + 2 * (i : ℕ) + 1 = k + 1 + 2 * (i : ℕ) by ring]
          field_simp
      _ ≤ c₀⁻¹ * (2 * (C₀ ^ (k + 1) / (k + 1).factorial)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc₀pos.le)
      _ = Real.exp (2 * C₀) * (2 * (C₀ ^ (k + 1) / (k + 1).factorial)) := by rw [hc₀inv]
  have hs1' : c₀⁻¹ * ∑ j : Fin J, C₀ ^ (k + 2 * (j : ℕ)) / ((k + 2 * (j : ℕ)).factorial : ℝ) ≤
      Real.exp (2 * C₀) * (2 * (C₀ ^ k / k.factorial)) := by
    rw [hc₀inv]; exact mul_le_mul_of_nonneg_left hs1 (Real.exp_pos _).le
  have hP0 : 0 ≤ c₀⁻¹ * ∑ j : Fin J, C₀ ^ (k + 2 * (j : ℕ)) / ((k + 2 * (j : ℕ)).factorial : ℝ) :=
    mul_nonneg (inv_nonneg.2 hc₀pos.le) (Finset.sum_nonneg fun j _ => by positivity)
  have hQ0 : 0 ≤ ∏ i : Fin J, (1 + C₀ ^ (k + 2 * (i : ℕ) + 1) / (((k + 2 * (i : ℕ) + 1).factorial : ℝ) * c₀)) :=
    Finset.prod_nonneg fun i _ => by positivity
  calc (∏ j : Fin J, ∏ p ∈ T w J j, (1 - g q p)) *
        (c₀⁻¹ * ∑ j : Fin J, C₀ ^ (k + 2 * (j : ℕ)) / ((k + 2 * (j : ℕ)).factorial : ℝ)) *
        ∏ i : Fin J, (1 + C₀ ^ (k + 2 * (i : ℕ) + 1) / (((k + 2 * (i : ℕ) + 1).factorial : ℝ) * c₀))
      ≤ (∏ j : Fin J, ∏ p ∈ T w J j, (1 - g q p)) * (Real.exp (2 * C₀) * (2 * (C₀ ^ k / k.factorial))) *
          Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (k + 1) / (k + 1).factorial))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hs1' hV0) hs2 hQ0
        exact mul_nonneg hV0 (by positivity)
    _ = _ := by ring

end SieveLeaf
