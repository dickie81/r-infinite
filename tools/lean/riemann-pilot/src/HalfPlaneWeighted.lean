import EisensteinMobius

/-!
# S0′: the totient-weighted sums over `ℤ[ω]` give S0's hypothesis (round 285)

Averaging the family of round 282 over `b ∈ ℤ[ω]` extracts the sums
`Σ_𝔞 μ(𝔞)·Π_{P∣𝔞}(1 − 1/N P)·W(N𝔞/Z)` over the ideals `𝔞` of norm prime to `6`. Their coefficients
`f(n) = Σ_{N𝔞=n} wf(𝔞)` are not round 278's `μ_K`. This file joins them to S0.
* `f` is multiplicative (`fA_mult`), with explicit prime-power values (`fW_split`, `fW_inert`,
  `fW_three`, `fW_two`).
* `μ_K = f ⍟ h` for an explicit multiplicative `h` (`fA_mul_hA`). The local factors of `h` are the
  coefficients of `(1 − x)(1 − χ₋₃(p)x)/F_p(x)`, where `F_p(x) = Σ_k f(p^k)x^k`.
* `Σ_n |h(n)| n^{−σ} < ∞` for every `σ > 0` (`summable_hfun`). The local bound is
  `|h(p^k)| ≤ (k + 2)/p` (`norm_Hloc_le`), and Mathlib's Euler product over smooth numbers bounds the
  partial sums (`summable_of_mult_local`).
* So `Σ_n μ_K(n)W(n/Z) = Σ_d h(d)·Σ_m f(m)W(md/Z)` (`smoothSum_eq_sum_h`), and a bound `O(Z^{θ+ε})` on
  the `f`-sums for every weight and every `ε > 0` gives `SmoothBound θ` when `θ ≥ 0`
  (`smoothBound_of_weightedBound`).

`WeightedBound θ` stays a displayed hypothesis: S2′, the sixth-power average and Cauchy–Schwarz, is to
derive it from the family's mean square.
-/

open NumberField Ideal UniqueFactorizationMonoid

namespace Eis

/-! ### Norm sums of ideal weights -/

/-- `Σ_{N𝔞 = n} w(𝔞)`. -/
noncomputable def normSum (w : Ideal (𝓞 K) → ℂ) (n : ℕ) : ℂ := ∑ I ∈ ofNorm n, w I

/-- A weight multiplicative on relatively prime ideals has multiplicative norm sums. -/
theorem normSum_mul (w : Ideal (𝓞 K) → ℂ)
    (hw : ∀ J L, IsRelPrime J L → w (J * L) = w J * w L) {a b : ℕ} (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) : normSum w (a * b) = normSum w a * normSum w b := by
  rw [normSum, ofNorm_mul hab ha hb, Finset.sum_image (injOn_mul hab), normSum, normSum,
    Finset.sum_mul_sum, Finset.sum_product]
  exact Finset.sum_congr rfl fun J hJ => Finset.sum_congr rfl fun L hL =>
    hw J L (isRelPrime_of_norm hab (mem_ofNorm.1 hJ) (mem_ofNorm.1 hL))

/-- At prime powers, a weight supported on squarefree ideals sums over sets of prime factors of `p𝓞`. -/
theorem normSum_prime_pow (w : Ideal (𝓞 K) → ℂ) (hw : ∀ I, ¬ Squarefree I → w I = 0)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    normSum w (p ^ k) = ∑ T ∈ (pFactors p).toFinset.powerset with ∏ P ∈ T, absNorm P = p ^ k,
      w (∏ P ∈ T, P) := by
  classical
  have hprimes : ∀ T ∈ (pFactors p).toFinset.powerset, ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ := by
    intro T hT P hP
    have hPf : P ∈ pFactors p := Multiset.mem_toFinset.1 (Finset.mem_powerset.1 hT hP)
    refine ⟨((mem_pFactors hp.ne_zero).1 hPf).1, fun h => ?_⟩
    have := ((mem_pFactors hp.ne_zero).1 hPf).2
    rw [h, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  rw [normSum, ← Finset.sum_filter_add_sum_filter_not (ofNorm (p ^ k)) Squarefree]
  rw [Finset.sum_eq_zero (s := (ofNorm (p ^ k)).filter (fun I => ¬ Squarefree I))
    (fun I hI => hw I (Finset.mem_filter.1 hI).2), add_zero]
  symm
  refine Finset.sum_nbij' (fun T => ∏ P ∈ T, P) (fun I => (normalizedFactors I).toFinset)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter] at hT ⊢
    obtain ⟨hsq, -⟩ := finset_prod_spec (hprimes T hT.1)
    refine ⟨mem_ofNorm.2 ?_, hsq⟩
    rw [map_prod]; exact hT.2
  · intro I hI
    simp only [Finset.mem_filter, mem_ofNorm] at hI ⊢
    refine ⟨Finset.mem_powerset.2 fun P hP => Multiset.mem_toFinset.2
      (mem_pFactors_of_mem hp hI.1 (Multiset.mem_toFinset.1 hP)), ?_⟩
    have hI0 : I ≠ 0 := fun h => by
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI; exact pow_ne_zero k hp.ne_zero hI.1.symm
    have hnd := (squarefree_iff_nodup_normalizedFactors hI0).1 hI.2
    rw [← map_prod, Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val,
      hnd.dedup, Ideal.prod_normalizedFactors_eq_self hI0, hI.1]
  · intro T hT
    simp only [Finset.mem_filter] at hT
    rw [(finset_prod_spec (hprimes T hT.1)).2, Finset.val_toFinset]
  · intro I hI
    simp only [Finset.mem_filter, mem_ofNorm] at hI
    have hI0 : I ≠ 0 := fun h => by
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI; exact pow_ne_zero k hp.ne_zero hI.1.symm
    have hnd := (squarefree_iff_nodup_normalizedFactors hI0).1 hI.2
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
      Ideal.prod_normalizedFactors_eq_self hI0]
  · intro T hT; rfl


/-! ### The totient-weighted Möbius weight -/

/-- `Π_{P ∣ I} (1 − 1/N(P))`. -/
noncomputable def tot (I : Ideal (𝓞 K)) : ℂ :=
  ∏ P ∈ (normalizedFactors I).toFinset, (1 - 1 / (absNorm P : ℂ))

/-- **The weight of the extracted sum**: `μ(I)·Π_{P∣I}(1 − 1/NP)` on ideals of norm prime to `6`. -/
noncomputable def wf (I : Ideal (𝓞 K)) : ℂ :=
  if (absNorm I).Coprime 6 then (moebius I : ℂ) * tot I else 0

theorem tot_one : tot (1 : Ideal (𝓞 K)) = 1 := by
  rw [tot, normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]

theorem tot_mul {J L : Ideal (𝓞 K)} (h : IsRelPrime J L) : tot (J * L) = tot J * tot L := by
  classical
  rcases eq_or_ne J 0 with rfl | hJ
  · have hL : L = 1 := Ideal.isUnit_iff.1 (isRelPrime_zero_left.1 h) ▸ (Ideal.one_eq_top).symm
    rw [hL, mul_one, tot_one, mul_one]
  rcases eq_or_ne L 0 with rfl | hL
  · have hJ1 : J = 1 := Ideal.isUnit_iff.1 (isRelPrime_zero_right.1 h) ▸ (Ideal.one_eq_top).symm
    rw [hJ1, one_mul, tot_one, one_mul]
  rw [tot, normalizedFactors_mul hJ hL, Multiset.toFinset_add, Finset.prod_union, tot, tot]
  rw [Finset.disjoint_left]
  intro P hPJ hPL
  have hpJ := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hPJ)
  have hpL := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hPL)
  exact (irreducible_of_normalized_factor P (Multiset.mem_toFinset.1 hPJ)).not_isUnit (h hpJ hpL)

theorem wf_mul (J L : Ideal (𝓞 K)) (h : IsRelPrime J L) : wf (J * L) = wf J * wf L := by
  unfold wf
  by_cases hJ : (absNorm J).Coprime 6
  · by_cases hL : (absNorm L).Coprime 6
    · rw [ite_eq_left (by rw [map_mul]; exact Nat.Coprime.mul_left hJ hL), ite_eq_left hJ, ite_eq_left hL,
        h.moebius_mul, tot_mul h]
      push_cast; ring
    · rw [ite_eq_right (by rw [map_mul, Nat.coprime_mul_iff_left]; exact fun hc => hL hc.2), ite_eq_right hL,
        mul_zero]
  · rw [ite_eq_right (by rw [map_mul, Nat.coprime_mul_iff_left]; exact fun hc => hJ hc.1), ite_eq_right hJ,
      zero_mul]

theorem wf_eq_zero_of_not_squarefree {I : Ideal (𝓞 K)} (hI : ¬ Squarefree I) : wf I = 0 := by
  unfold wf; split_ifs <;> simp [moebius_of_not_squarefree hI]

/-- The values of the weight on products of distinct prime factors of `p𝓞`. -/
theorem wf_finset_prod {T : Finset (Ideal (𝓞 K))} (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    wf (∏ P ∈ T, P) = if (∏ P ∈ T, absNorm P).Coprime 6 then
      (-1) ^ T.card * ∏ P ∈ T, (1 - 1 / (absNorm P : ℂ)) else 0 := by
  unfold wf
  rw [map_prod]
  split_ifs
  · rw [moebius_finset_prod hT, tot, (finset_prod_spec hT).2, Finset.val_toFinset]; push_cast; ring
  · rfl


/-- The prime factors of `p𝓞` are nonzero primes. -/
theorem pFactors_prime {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ pFactors p) :
    P.IsPrime ∧ P ≠ ⊥ := by
  refine ⟨((mem_pFactors hp.ne_zero).1 hP).1, fun h => ?_⟩
  have := ((mem_pFactors hp.ne_zero).1 hP).2
  rw [h, Ideal.mem_bot] at this
  exact hp.ne_zero (by exact_mod_cast this)

/-- If every prime factor of `p𝓞` in `S` has norm `p^f`, a sum over subsets of `S` of total norm
`p^k` of a function of the subset's size is a binomial count. -/
theorem weighted_count {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, absNorm P = p ^ f) (k : ℕ) (g : ℕ → ℂ) :
    (∑ T ∈ S.powerset with ∏ P ∈ T, absNorm P = p ^ k, g T.card) =
      if f ∣ k then (S.card.choose (k / f) : ℂ) * g (k / f) else 0 := by
  classical
  have hnorm : ∀ T ∈ S.powerset, ∏ P ∈ T, absNorm P = p ^ (f * T.card) := by
    intro T hT
    rw [Finset.prod_congr rfl fun P hP => hS P (Finset.mem_powerset.1 hT hP), Finset.prod_const,
      ← pow_mul, mul_comm]
  have hiff : ∀ T ∈ S.powerset, (∏ P ∈ T, absNorm P = p ^ k) ↔ f * T.card = k := by
    intro T hT
    rw [hnorm T hT]
    exact (Nat.pow_right_injective hp.two_le).eq_iff
  rw [Finset.sum_filter, Finset.sum_congr rfl fun T hT => by rw [if_congr (hiff T hT) rfl rfl]]
  rw [← Finset.sum_filter]
  split_ifs with hdvd
  · obtain ⟨j, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left _ hf]
    have hset : S.powerset.filter (fun T => f * T.card = f * j) = S.powersetCard j := by
      rw [Finset.powersetCard_eq_filter]
      congr 1; ext T; exact (Nat.mul_right_inj hf.ne').trans Iff.rfl
    rw [hset, Finset.sum_congr rfl fun T hT => by rw [(Finset.mem_powersetCard.1 hT).2],
      Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  · rw [Finset.sum_eq_zero]
    intro T hT
    exact absurd ⟨T.card, (Finset.mem_filter.1 hT).2.symm⟩ hdvd

/-- `f(p^k)` as a binomial count, when the prime factors of `p𝓞` all have norm `p^f`. -/
theorem fW_prime_pow_of {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hS : ∀ P ∈ (pFactors p).toFinset, absNorm P = p ^ f) (k : ℕ) :
    normSum wf (p ^ k) = if (p ^ k).Coprime 6 then
      (if f ∣ k then ((pFactors p).toFinset.card.choose (k / f) : ℂ) *
        (-(1 - 1 / (p : ℂ) ^ f)) ^ (k / f) else 0) else 0 := by
  classical
  rw [normSum_prime_pow wf (fun I hI => wf_eq_zero_of_not_squarefree hI) hp k]
  have hterm : ∀ T ∈ (pFactors p).toFinset.powerset.filter (fun T => ∏ P ∈ T, absNorm P = p ^ k),
      wf (∏ P ∈ T, P) = if (p ^ k).Coprime 6 then (-(1 - 1 / (p : ℂ) ^ f)) ^ T.card else 0 := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have hTp : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ := fun P hP =>
      pFactors_prime hp (Multiset.mem_toFinset.1 (Finset.mem_powerset.1 hT.1 hP))
    rw [wf_finset_prod hTp, hT.2]
    split_ifs
    · rw [Finset.prod_congr rfl fun P hP => by
        rw [hS P (Finset.mem_powerset.1 hT.1 hP)], Finset.prod_const]
      push_cast; rw [← mul_pow]; congr 1; ring
    · rfl
  rw [Finset.sum_congr rfl hterm]
  by_cases hc : (p ^ k).Coprime 6
  · simp only [ite_eq_left hc]
    exact weighted_count hp hf _ hS k (fun j => (-(1 - 1 / (p : ℂ) ^ f)) ^ j)
  · simp only [ite_eq_right hc, Finset.sum_const_zero]

/-- **Ramified**: `f(3^k) = [k = 0]`. -/
theorem fW_three (k : ℕ) : normSum wf (3 ^ k) = if k = 0 then 1 else 0 := by
  classical
  obtain ⟨hf, hn⟩ := ramified_three
  have hfin : (pFactors 3).toFinset = {span {ω - 1}} := by rw [hf]; ext; simp
  rw [fW_prime_pow_of Nat.prime_three one_pos (by rw [hfin]; simpa using hn) k]
  rcases k with _ | k
  · simp
  · have : ¬ (3 ^ (k + 1)).Coprime 6 := by
      rw [Nat.Coprime, Nat.gcd_comm]; intro h
      have h3 : 3 ∣ Nat.gcd 6 (3 ^ (k + 1)) :=
        Nat.dvd_gcd (by norm_num) (dvd_pow_self 3 (by omega))
      rw [h] at h3; norm_num at h3
    simp [this]

/-- **Two is inert, but not prime to `6`**: `f(2^k) = [k = 0]`. -/
theorem fW_two (k : ℕ) : normSum wf (2 ^ k) = if k = 0 then 1 else 0 := by
  classical
  obtain ⟨P, hf, hPn⟩ := inert_of_mod_two Nat.prime_two (by norm_num)
  rw [fW_prime_pow_of Nat.prime_two two_pos (by rw [hf]; simpa using hPn) k]
  rcases k with _ | k
  · simp
  · have : ¬ (2 ^ (k + 1)).Coprime 6 := by
      rw [Nat.Coprime, Nat.gcd_comm]; intro h
      have h2 : 2 ∣ Nat.gcd 6 (2 ^ (k + 1)) :=
        Nat.dvd_gcd (by norm_num) (dvd_pow_self 2 (by omega))
      rw [h] at h2; norm_num at h2
    simp [this]

theorem coprime_six_of_ne {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (k : ℕ) :
    (p ^ k).Coprime 6 := by
  apply Nat.Coprime.pow_left
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  exact Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).2 h2)
    ((Nat.coprime_primes hp Nat.prime_three).2 h3)

/-- **Split**: `f(p^k) = C(2, k)·(−(1 − 1/p))^k` for `p ≡ 1 (mod 3)`. -/
theorem fW_split {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) (k : ℕ) :
    normSum wf (p ^ k) = ((2 : ℕ).choose k : ℂ) * (-(1 - 1 / (p : ℂ))) ^ k := by
  classical
  obtain ⟨P, Q, hPQ, hf, hPn, hQn⟩ := split_of_mod_one hp h1
  have hfin : (pFactors p).toFinset = {P, Q} := by rw [hf]; ext; simp
  rw [fW_prime_pow_of hp one_pos (by
    rw [hfin]; intro R hR; rcases Finset.mem_insert.1 hR with rfl | hR
    · simpa using hPn
    · rw [Finset.mem_singleton.1 hR]; simpa using hQn) k]
  rw [ite_eq_left (coprime_six_of_ne hp (by rintro rfl; norm_num at h1) (by rintro rfl; norm_num at h1) k),
    hfin, Finset.card_pair hPQ]
  simp

/-- **Inert, `p ≥ 5`**: `f(p^k) = [2 ∣ k]·C(1, k/2)·(−(1 − 1/p²))^{k/2}` for `p ≡ 2 (mod 3)`. -/
theorem fW_inert {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) (hp2 : p ≠ 2) (k : ℕ) :
    normSum wf (p ^ k) = if 2 ∣ k then ((1 : ℕ).choose (k / 2) : ℂ) *
      (-(1 - 1 / (p : ℂ) ^ 2)) ^ (k / 2) else 0 := by
  classical
  obtain ⟨P, hf, hPn⟩ := inert_of_mod_two hp h2
  rw [fW_prime_pow_of hp two_pos (by rw [hf]; simpa using hPn) k,
    ite_eq_left (coprime_six_of_ne hp hp2 (by rintro rfl; norm_num at h2) k), hf]
  simp


/-! ### The Euler correction `h = μ_K / f` -/

section Correction

open ArithmeticFunction

/-- The local factor of the Euler correction at `p^k`: the `k`-th coefficient of
`(1 − x)(1 − χ₋₃(p)x)/F_p(x)`, where `F_p(x) = Σ_k f(p^k)x^k`. -/
noncomputable def Hloc (p k : ℕ) : ℂ :=
  if k = 0 then 1
  else if p = 3 then (if k = 1 then -1 else 0)
  else if p = 2 then (if k = 2 then -1 else 0)
  else if p % 3 = 1 then
    -(2 / (p : ℂ)) * (1 - 1 / (p : ℂ)) ^ (k - 1) +
      ((k - 1 : ℕ) : ℂ) * (1 - 1 / (p : ℂ)) ^ (k - 2) / (p : ℂ) ^ 2
  else if 2 ∣ k then -((1 - 1 / (p : ℂ) ^ 2) ^ (k / 2 - 1)) / (p : ℂ) ^ 2 else 0

theorem Hloc_zero (p : ℕ) : Hloc p 0 = 1 := by simp [Hloc]

/-- The Euler correction `h(n) = Π_{p^k ∥ n} H(p, k)`. -/
noncomputable def hfun (n : ℕ) : ℂ := if n = 0 then 0 else n.factorization.prod Hloc

theorem hfun_one : hfun 1 = 1 := by simp [hfun]

theorem hfun_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : hfun (p ^ k) = Hloc p k := by
  rw [hfun, ite_eq_right (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (Hloc_zero p)]

theorem hfun_mul {m n : ℕ} (hmn : m.Coprime n) : hfun (m * n) = hfun m * hfun n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [(Nat.coprime_zero_left n).1 hmn]; simp [hfun]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [(Nat.coprime_zero_right m).1 hmn]; simp [hfun]
  rw [hfun, ite_eq_right (mul_ne_zero hm hn), hfun, ite_eq_right hm, hfun, ite_eq_right hn,
    Nat.factorization_mul_of_coprime hmn, ← Finsupp.prod_add_index_of_disjoint]
  exact hmn.disjoint_primeFactors

/-- `f` and `h` as arithmetic functions. -/
noncomputable def fA : ArithmeticFunction ℂ := toArithmeticFunction (normSum wf)
noncomputable def hA : ArithmeticFunction ℂ := toArithmeticFunction hfun

theorem fA_apply {n : ℕ} (hn : n ≠ 0) : fA n = normSum wf n := by
  simp [fA, toArithmeticFunction, hn]

theorem hA_apply {n : ℕ} (hn : n ≠ 0) : hA n = hfun n := by
  simp [hA, toArithmeticFunction, hn]

theorem normSum_wf_one : normSum wf 1 = 1 := by
  have := fW_two 0
  simpa using this

theorem fA_mult : fA.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by rw [fA_apply one_ne_zero, normSum_wf_one],
    fun {m n} hm hn hmn => ?_⟩
  rw [fA_apply (mul_ne_zero hm hn), fA_apply hm, fA_apply hn,
    normSum_mul wf wf_mul hmn (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)]

theorem hA_mult : hA.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by rw [hA_apply one_ne_zero, hfun_one],
    fun {m n} hm hn hmn => ?_⟩
  rw [hA_apply (mul_ne_zero hm hn), hA_apply hm, hA_apply hn, hfun_mul hmn]

/-- A convolution with a factor supported on `{0, 1, 2}`. -/
theorem conv_small (F H : ℕ → ℂ) (hF : ∀ i, 3 ≤ i → F i = 0) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), F i * H (k - i) =
      F 0 * H k + (if 1 ≤ k then F 1 * H (k - 1) else 0) +
        (if 2 ≤ k then F 2 * H (k - 2) else 0) := by
  rcases k with _ | _ | _ | k
  · simp
  · simp [Finset.sum_range_succ]
  · simp [Finset.sum_range_succ]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, ite_true]
      simp only [Nat.sub_zero, show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
        show 0 + 1 = 1 by rfl, show 0 + 1 + 1 = 2 by rfl]
      ring
    · intro i _
      rw [hF (i + 1 + 1 + 1) (by omega), zero_mul]

/-- The convolution `(f ⍟ h)(p^k)` as a sum over exponents. -/
theorem conv_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (fA * hA) (p ^ k) = ∑ i ∈ Finset.range (k + 1), normSum wf (p ^ i) * Hloc p (k - i) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => fA a * hA b),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div hik hp.pos, fA_apply (pow_ne_zero _ hp.ne_zero),
    hA_apply (pow_ne_zero _ hp.ne_zero), hfun_prime_pow hp]


theorem Hloc_split {p : ℕ} (h1 : p % 3 = 1) {k : ℕ} (hk : k ≠ 0) :
    Hloc p k = -(2 / (p : ℂ)) * (1 - 1 / (p : ℂ)) ^ (k - 1) +
      ((k - 1 : ℕ) : ℂ) * (1 - 1 / (p : ℂ)) ^ (k - 2) / (p : ℂ) ^ 2 := by
  have h3 : p ≠ 3 := by omega
  have h2 : p ≠ 2 := by omega
  simp only [Hloc, hk, h3, h2, h1, ite_false, ite_true]

theorem Hloc_inert {p : ℕ} (h2 : p % 3 = 2) (hp2 : p ≠ 2) {k : ℕ} (hk : k ≠ 0) :
    Hloc p k = if 2 ∣ k then -((1 - 1 / (p : ℂ) ^ 2) ^ (k / 2 - 1)) / (p : ℂ) ^ 2 else 0 := by
  have h3 : p ≠ 3 := by omega
  have h1 : ¬ p % 3 = 1 := by omega
  simp only [Hloc, hk, h3, hp2, h1, ite_false]

/-- The split recurrence: `H(k) − 2c·H(k−1) + c²·H(k−2) = 0` for `k ≥ 3`, `c = 1 − 1/p`. -/
theorem split_rec {p : ℕ} (h1 : p % 3 = 1) (m : ℕ) :
    Hloc p (m + 3) + (-2 * (1 - 1 / (p : ℂ))) * Hloc p (m + 2) +
      (1 - 1 / (p : ℂ)) ^ 2 * Hloc p (m + 1) = 0 := by
  rw [Hloc_split h1 (k := m + 3) (by omega), Hloc_split h1 (k := m + 2) (by omega),
    Hloc_split h1 (k := m + 1) (by omega)]
  rcases m with _ | n
  · norm_num; ring
  · simp only [show n + 1 + 3 - 1 = n + 3 by omega, show n + 1 + 3 - 2 = n + 2 by omega,
      show n + 1 + 2 - 1 = n + 2 by omega, show n + 1 + 2 - 2 = n + 1 by omega,
      show n + 1 + 1 - 1 = n + 1 by omega, show n + 1 + 1 - 2 = n by omega]
    push_cast; ring

/-- The inert recurrence: `H(k) − c′·H(k−2) = 0` for even `k ≥ 4`, `c′ = 1 − 1/p²`. -/
theorem inert_rec {p : ℕ} (h2 : p % 3 = 2) (hp2 : p ≠ 2) (j : ℕ) :
    Hloc p (2 * j + 4) + (-(1 - 1 / (p : ℂ) ^ 2)) * Hloc p (2 * j + 2) = 0 := by
  rw [Hloc_inert h2 hp2 (k := 2 * j + 4) (by omega), Hloc_inert h2 hp2 (k := 2 * j + 2) (by omega),
    ite_eq_left (by omega), ite_eq_left (by omega),
    show (2 * j + 4) / 2 - 1 = j + 1 by omega, show (2 * j + 2) / 2 - 1 = j by omega]
  ring

theorem Hloc_odd {p : ℕ} (h2 : p % 3 = 2) (hp2 : p ≠ 2) {k : ℕ} (hk : ¬ 2 ∣ k) : Hloc p k = 0 := by
  rw [Hloc_inert h2 hp2 (by rintro rfl; exact hk (dvd_zero 2)), ite_eq_right hk]

/-- **`f ⍟ h = μ_K`**: the Euler correction turns the totient-weighted coefficients back into the
Möbius coefficients of `1/(ζ(s)L(s, χ₋₃))`. -/
theorem fA_mul_hA : fA * hA = muA * muB := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (fA_mult.mul hA_mult) _ (muA_mult.mul muB_mult)]
  intro p k hp
  rw [show (muA * muB) (p ^ k) = HalfPlaneS0.muK (p ^ k) from rfl, muK_prime_pow hp,
    conv_prime_pow hp]
  have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · -- `p = 3`
    have hp3 : p = 3 := by
      have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this).symm
    subst hp3
    rw [conv_small (fun i => normSum wf (3 ^ i)) (Hloc 3) (fun i hi => by
      rw [fW_three, ite_eq_right (by omega)]) k]
    simp only [fW_three]
    rcases k with _ | _ | _ | k <;> simp [Hloc, chiInt]
  · -- split
    have hc : chiInt p = 1 := by simp [chiInt, h1]
    rw [conv_small (fun i => normSum wf (p ^ i)) (Hloc p) (fun i hi => by
      rw [fW_split hp h1, Nat.choose_eq_zero_of_lt (by omega)]; simp) k]
    have hF0 : normSum wf (p ^ 0) = 1 := by rw [fW_split hp h1]; simp
    have hF1 : normSum wf (p ^ 1) = -2 * (1 - 1 / (p : ℂ)) := by rw [fW_split hp h1]; norm_num; ring
    have hF2 : normSum wf (p ^ 2) = (1 - 1 / (p : ℂ)) ^ 2 := by rw [fW_split hp h1]; norm_num; ring
    rw [hF0, hF1, hF2, hc]
    rcases k with _ | _ | _ | m
    · simp [Hloc_zero]
    · rw [Hloc_split h1 (k := 1) (by omega)]; norm_num [Hloc_zero]; ring
    · rw [Hloc_split h1 (k := 2) (by omega), Hloc_split h1 (k := 1) (by omega)]
      norm_num [Hloc_zero]
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp; ring
    · simp only [show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, ite_true,
        show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
      norm_num
      linear_combination split_rec h1 m
  · by_cases hp2 : p = 2
    · subst hp2
      rw [conv_small (fun i => normSum wf (2 ^ i)) (Hloc 2) (fun i hi => by
        rw [fW_two, ite_eq_right (by omega)]) k]
      simp only [fW_two]
      rcases k with _ | _ | _ | k <;> simp [Hloc, chiInt]
    · -- inert, `p ≥ 5`
      have hc : chiInt p = -1 := by simp [chiInt, h2]
      rw [conv_small (fun i => normSum wf (p ^ i)) (Hloc p) (fun i hi => by
        rw [fW_inert hp h2 hp2]
        split_ifs with hd
        · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
        · rfl) k]
      have hF0 : normSum wf (p ^ 0) = 1 := by rw [fW_inert hp h2 hp2]; simp
      have hF1 : normSum wf (p ^ 1) = 0 := by rw [fW_inert hp h2 hp2]; simp
      have hF2 : normSum wf (p ^ 2) = -(1 - 1 / (p : ℂ) ^ 2) := by rw [fW_inert hp h2 hp2]; norm_num
      rw [hF0, hF1, hF2, hc]
      rcases k with _ | _ | _ | m
      · simp [Hloc_zero]
      · rw [Hloc_odd h2 hp2 (k := 1) (by omega)]; simp
      · rw [Hloc_inert h2 hp2 (k := 2) (by omega)]; norm_num [Hloc_zero]; ring
      · simp only [show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, ite_true,
          show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
        norm_num
        rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · rw [Hloc_odd h2 hp2 (k := j + j + 3) (by omega), Hloc_odd h2 hp2 (k := j + j + 1) (by omega)]
          ring
        · rw [show 2 * j + 1 + 3 = 2 * j + 4 by omega, show 2 * j + 1 + 1 = 2 * j + 2 by omega]
          linear_combination inert_rec h2 hp2 j
end Correction


/-! ### Convergence of the correction on `Re s > 0` -/

section Summable

/-- **Multiplicative functions with small local factors are summable.** A nonnegative multiplicative
`g` whose local sums satisfy `Σ_k g(p^k) ≤ 1 + A·p^{−(1+σ)}` with `σ > 0` is summable: its partial sums
are bounded by `Π_p (1 + A p^{−1−σ}) ≤ exp(A Σ_n n^{−1−σ})` (Mathlib's Euler product over smooth
numbers). -/
theorem summable_of_mult_local {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hgz : g 0 = 0) (hg1 : g 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n)
    (hloc : ∀ {p : ℕ}, p.Prime → Summable fun k => g (p ^ k))
    {A σ : ℝ} (hA : 0 ≤ A) (hσ : 0 < σ)
    (hb : ∀ {p : ℕ}, p.Prime → ∑' k, g (p ^ k) ≤ 1 + A * (p : ℝ) ^ (-(1 + σ))) :
    Summable g := by
  have hz : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + σ)) := Real.summable_nat_rpow.2 (by linarith)
  refine summable_of_sum_range_le hg0 (c := Real.exp (A * ∑' n : ℕ, (n : ℝ) ^ (-(1 + σ))))
    fun N => ?_
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (R := ℝ)
    (f := g) hg1 hmul (fun hp => (hloc hp).congr fun k => by
      rw [Real.norm_of_nonneg (hg0 _)]) N).2
  have hind : HasSum ((N.smoothNumbers).indicator g)
      (∏ p ∈ N.primesBelow, ∑' k, g (p ^ k)) := hasSum_subtype_iff_indicator.1 hsum
  have hpos : ∀ p ∈ N.primesBelow, 0 ≤ (p : ℝ) ^ (-(1 + σ)) := fun p _ => by positivity
  calc ∑ i ∈ Finset.range N, g i = ∑ i ∈ Finset.range N, (N.smoothNumbers).indicator g i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [hgz, Set.indicator_of_notMem (by simp [Nat.smoothNumbers])]
        · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hi0 (Finset.mem_range.1 hi))]
    _ ≤ ∏ p ∈ N.primesBelow, ∑' k, g (p ^ k) :=
        sum_le_hasSum _ (fun i _ => Set.indicator_nonneg (fun j _ => hg0 j) i) hind
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (A * (p : ℝ) ^ (-(1 + σ))) := by
        refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg fun k => hg0 _) fun p hp => ?_
        exact (hb (Nat.prime_of_mem_primesBelow hp)).trans (by
          linarith [Real.add_one_le_exp (A * (p : ℝ) ^ (-(1 + σ)))])
    _ = Real.exp (A * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(1 + σ))) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (A * ∑' n : ℕ, (n : ℝ) ^ (-(1 + σ))) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hA)
        exact hz.sum_le_tsum _ fun i _ => by positivity

theorem norm_one_sub_inv_le {p : ℕ} (hp : 1 ≤ p) : ‖1 - 1 / (p : ℂ)‖ ≤ 1 := by
  have h : (1 - 1 / (p : ℂ)) = ((1 - 1 / (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hp'
  rw [h, Complex.norm_real, Real.norm_of_nonneg h0]
  have : 0 ≤ 1 / (p : ℝ) := by positivity
  linarith

theorem norm_one_sub_inv_sq_le {p : ℕ} (hp : 1 ≤ p) : ‖1 - 1 / (p : ℂ) ^ 2‖ ≤ 1 := by
  have h : (1 - 1 / (p : ℂ) ^ 2) = ((1 - 1 / (p : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : 0 ≤ 1 - 1 / (p : ℝ) ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  rw [h, Complex.norm_real, Real.norm_of_nonneg h0]
  have : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
  linarith

/-- **The local factors are small**: `|H(p, k)| ≤ (k + 2)/p` for `k ≥ 1`. -/
theorem norm_Hloc_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    ‖Hloc p k‖ ≤ ((k : ℝ) + 2) / p := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < p := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  by_cases h3 : p = 3
  · subst h3
    have : ‖Hloc 3 k‖ ≤ 1 := by
      simp only [Hloc, hk, ite_false, ite_true]; split_ifs <;> simp
    refine this.trans ?_
    rw [le_div_iff₀ (by norm_num)]; push_cast; linarith
  by_cases h2 : p = 2
  · subst h2
    have : ‖Hloc 2 k‖ ≤ 1 := by
      simp only [Hloc, hk, h3, ite_false, ite_true]; split_ifs <;> simp
    refine this.trans ?_
    rw [le_div_iff₀ (by norm_num)]; push_cast; linarith
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have : p % 3 ≠ 0 := fun h0 => h3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.dvd_of_mod_eq_zero h0)).symm)
    omega
  have hpp : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  rcases hmod with h1 | h2'
  · rw [Hloc_split h1 hk]
    have hc := norm_one_sub_inv_le hp1
    have hk0 : (0 : ℝ) ≤ k - 1 := by linarith
    have hk' : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have e1 : ‖-(2 / (p : ℂ)) * (1 - 1 / (p : ℂ)) ^ (k - 1)‖ ≤ 2 / p := by
      rw [norm_mul, norm_neg, norm_div, Complex.norm_natCast, Complex.norm_ofNat, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
    have e2 : ‖((k - 1 : ℕ) : ℂ) * (1 - 1 / (p : ℂ)) ^ (k - 2) / (p : ℂ) ^ 2‖ ≤
        ((k : ℝ) - 1) / p := by
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast, hk']
      calc ((k : ℝ) - 1) * ‖1 - 1 / (p : ℂ)‖ ^ (k - 2) / (p : ℝ) ^ 2
          ≤ ((k : ℝ) - 1) / (p : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_of_le_one_right hk0
              (pow_le_one₀ (norm_nonneg _) hc)) (by positivity)
        _ ≤ ((k : ℝ) - 1) / p := div_le_div_of_nonneg_left hk0 hpos hpp
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 2 / (p : ℝ) + ((k : ℝ) - 1) / p := add_le_add e1 e2
      _ = ((k : ℝ) + 1) / p := by ring
      _ ≤ ((k : ℝ) + 2) / p := div_le_div_of_nonneg_right (by linarith) hpos.le
  · rw [Hloc_inert h2' h2 hk]
    split_ifs
    · rw [norm_div, norm_neg, norm_pow, norm_pow, Complex.norm_natCast]
      have hc := norm_one_sub_inv_sq_le hp1
      calc ‖1 - 1 / (p : ℂ) ^ 2‖ ^ (k / 2 - 1) / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hc) (by positivity)
        _ ≤ 1 / p := div_le_div_of_nonneg_left zero_le_one hpos hpp
        _ ≤ ((k : ℝ) + 2) / p := div_le_div_of_nonneg_right (by linarith) hpos.le
    · simp; positivity

/-- `|h(p^k)| p^{−kσ} ≤ [k = 0] + (3/p)·k·y^k` with `y = p^{−σ}`. -/
theorem hloc_term_le {p : ℕ} (hp : p.Prime) (σ : ℝ) (k : ℕ) :
    ‖hfun (p ^ k)‖ * ((p ^ k : ℕ) : ℝ) ^ (-σ) ≤
      (if k = 0 then 1 else 0) + 3 / (p : ℝ) * ((k : ℝ) * ((p : ℝ) ^ (-σ)) ^ k) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hy : ((p ^ k : ℕ) : ℝ) ^ (-σ) = ((p : ℝ) ^ (-σ)) ^ k := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le, mul_comm, Real.rpow_mul hpos.le,
      Real.rpow_natCast]
  rw [hy, hfun_prime_pow hp]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [Hloc_zero]
  · rw [ite_eq_right hk, zero_add]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    have hyk : 0 ≤ ((p : ℝ) ^ (-σ)) ^ k := by positivity
    have h3 : ((k : ℝ) + 2) ≤ 3 * k := by linarith
    calc ‖Hloc p k‖ * ((p : ℝ) ^ (-σ)) ^ k ≤ ((k : ℝ) + 2) / p * ((p : ℝ) ^ (-σ)) ^ k :=
          mul_le_mul_of_nonneg_right (norm_Hloc_le hp hk) hyk
      _ ≤ (3 * k) / p * ((p : ℝ) ^ (-σ)) ^ k :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h3 hpos.le) hyk
      _ = 3 / (p : ℝ) * ((k : ℝ) * ((p : ℝ) ^ (-σ)) ^ k) := by ring

theorem summable_indicator_zero : Summable fun k : ℕ => (if k = 0 then (1 : ℝ) else 0) :=
  summable_of_ne_finset_zero (s := {0}) fun k hk => by
    rw [Finset.mem_singleton] at hk; rw [ite_eq_right hk]

theorem summable_local_majorant (c : ℝ) {y : ℝ} (hy : ‖y‖ < 1) :
    Summable fun k : ℕ => c * ((k : ℝ) * y ^ k) :=
  ((summable_pow_mul_geometric_of_norm_lt_one 1 hy).mul_left c).congr fun k => by ring

/-- **The Euler correction converges absolutely on `Re s > 0`**: `Σ_n |h(n)| n^{−σ} < ∞` for every
`σ > 0`. -/
theorem summable_hfun {σ : ℝ} (hσ : 0 < σ) :
    Summable fun n : ℕ => ‖hfun n‖ * (n : ℝ) ^ (-σ) := by
  set y0 : ℝ := (2 : ℝ) ^ (-σ) with hy0def
  have hy0 : y0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hy00 : 0 < y0 := by positivity
  set A : ℝ := 3 / (1 - y0) ^ 2 with hAdef
  have hA : 0 ≤ A := by positivity
  have hyn : ∀ {p : ℕ}, p.Prime → ‖(p : ℝ) ^ (-σ)‖ < 1 := fun {p} hp => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hloc_summ : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ =>
      (if k = 0 then (1 : ℝ) else 0) + 3 / (p : ℝ) * ((k : ℝ) * ((p : ℝ) ^ (-σ)) ^ k) :=
    fun {p} hp => summable_indicator_zero.add (summable_local_majorant _ (hyn hp))
  refine summable_of_mult_local (g := fun n => ‖hfun n‖ * (n : ℝ) ^ (-σ)) (fun n => by positivity)
    (by simp [hfun]) (by simp [hfun_one]) (fun {m n} hmn => ?_) (fun {p} hp => ?_) hA hσ
    (fun {p} hp => ?_)
  · rw [hfun_mul hmn, norm_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
    ring
  · exact Summable.of_nonneg_of_le (fun k => by positivity) (fun k => hloc_term_le hp σ k)
      (hloc_summ hp)
  · have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hyy : (p : ℝ) ^ (-σ) ≤ y0 := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have hy0' : 0 < (p : ℝ) ^ (-σ) := by positivity
    calc ∑' k, ‖hfun (p ^ k)‖ * ((p ^ k : ℕ) : ℝ) ^ (-σ)
        ≤ ∑' k : ℕ, ((if k = 0 then (1 : ℝ) else 0) +
            3 / (p : ℝ) * ((k : ℝ) * ((p : ℝ) ^ (-σ)) ^ k)) :=
          Summable.tsum_le_tsum (fun k => hloc_term_le hp σ k)
            (Summable.of_nonneg_of_le (fun k => by positivity) (fun k => hloc_term_le hp σ k)
              (hloc_summ hp)) (hloc_summ hp)
      _ = 1 + 3 / (p : ℝ) * ((p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ)) ^ 2) := by
          rw [summable_indicator_zero.tsum_add (summable_local_majorant _ (hyn hp)),
            tsum_ite_eq 0 (fun _ => (1 : ℝ)), tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one (hyn hp)]
      _ ≤ 1 + A * (p : ℝ) ^ (-(1 + σ)) := by
          have hsplit : (p : ℝ) ^ (-(1 + σ)) = 1 / p * (p : ℝ) ^ (-σ) := by
            rw [show -(1 + σ) = -1 + -σ by ring, Real.rpow_add hpos, Real.rpow_neg_one]
            ring
          rw [hsplit, hAdef]
          have h1 : 0 < 1 - y0 := by linarith
          have h2 : 1 - y0 ≤ 1 - (p : ℝ) ^ (-σ) := by linarith
          have hsq : (1 - y0) ^ 2 ≤ (1 - (p : ℝ) ^ (-σ)) ^ 2 := by gcongr
          have : 3 / (p : ℝ) * ((p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ)) ^ 2) ≤
              3 / (1 - y0) ^ 2 * (1 / p * (p : ℝ) ^ (-σ)) := by
            rw [show 3 / (p : ℝ) * ((p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ)) ^ 2) =
                3 / p * (p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ)) ^ 2 by ring,
              show 3 / (1 - y0) ^ 2 * (1 / p * (p : ℝ) ^ (-σ)) =
                3 / p * (p : ℝ) ^ (-σ) / (1 - y0) ^ 2 by ring]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
          linarith

end Summable

/-! ### The transfer to S0's hypothesis -/

section Transfer

open ArithmeticFunction Filter Asymptotics HalfPlaneS0

theorem normSum_wf_zero : normSum wf 0 = 0 := by
  classical
  have : ofNorm 0 = {(⊥ : Ideal (𝓞 K))} := by
    ext I; simp [mem_ofNorm, Ideal.absNorm_eq_zero_iff]
  rw [normSum, this, Finset.sum_singleton, wf, ite_eq_right]
  rw [Ideal.absNorm_bot, Nat.coprime_zero_left]; norm_num

theorem coe_fA : ⇑fA = normSum wf := by
  funext n; rcases eq_or_ne n 0 with rfl | hn
  · rw [normSum_wf_zero]; rfl
  · exact fA_apply hn

theorem coe_hA : ⇑hA = hfun := by
  funext n; rcases eq_or_ne n 0 with rfl | hn
  · simp [hfun]
  · exact hA_apply hn

/-- The smoothed totient-weighted sum `Σ_n f(n) W(n/Z)`, `f(n) = Σ_{N𝔞=n} wf(𝔞)`. -/
noncomputable def fSmooth (W : ℝ → ℝ) (Z : ℝ) : ℂ := ∑' n : ℕ, normSum wf n * (W (n / Z) : ℂ)

/-- **The S0′ hypothesis at exponent `θ`**: power savings for the totient-weighted sums. -/
def WeightedBound (θ : ℝ) : Prop :=
  ∀ W : ℝ → ℝ, Weight W → ∀ ε : ℝ, 0 < ε → fSmooth W =O[atTop] fun Z => Z ^ (θ + ε)

/-- A weighted form of Mathlib's `sum_Ioc_mul_eq_sum_prod_filter`. -/
theorem sum_Ioc_mul_weight (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (f * g) n * w n =
      ∑ x ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N with x.1 * x.2 ≤ N, f x.1 * g x.2 * w (x.1 * x.2) := by
  simp only [mul_apply, Finset.sum_mul]
  trans ∑ n ∈ Finset.Ioc 0 N, ∑ x ∈ Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N with x.1 * x.2 = n,
    f x.1 * g x.2 * w (x.1 * x.2)
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Ioc] at hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  · simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_product, Finset.mem_Ioc] at hx
    have h1 : 0 < x.1 * x.2 := Nat.mul_pos hx.1.1 hx.2.1
    by_cases hle : x.1 * x.2 ≤ N <;> simp [hle, h1]

/-- On `Z > 0`, with `W` vanishing beyond `R` and `R·Z ≤ N`, the smoothed sum is a finite sum. -/
theorem tsum_eq_Ioc {a : ℕ → ℂ} (ha : a 0 = 0) {W : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R < x → W x = 0)
    {Z : ℝ} (hZ : 0 < Z) {N : ℕ} (hN : R * Z ≤ N) :
    ∑' n : ℕ, a n * (W (n / Z) : ℂ) = ∑ n ∈ Finset.Ioc 0 N, a n * (W (n / Z) : ℂ) := by
  refine tsum_eq_sum fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [ha, zero_mul]
  · have hnN : N < n := by
      by_contra h; exact hn (Finset.mem_Ioc.2 ⟨hn0, not_lt.1 h⟩)
    have : R < n / Z := by
      rw [lt_div_iff₀ hZ]
      calc R * Z ≤ N := hN
        _ < n := by exact_mod_cast hnN
    rw [hR _ this, Complex.ofReal_zero, mul_zero]

/-- **The transfer identity**: `Σ_n μ_K(n)W(n/Z) = Σ_d h(d)·Σ_m f(m)W(md/Z)`. -/
theorem smoothSum_eq_sum_h {W : ℝ → ℝ} {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x, R < x → W x = 0)
    {Z : ℝ} (hZ : 0 < Z) {N : ℕ} (hN : R * Z ≤ N) :
    smoothSum W Z = ∑ d ∈ Finset.Ioc 0 N, hfun d * fSmooth W (Z / d) := by
  rw [smoothSum, tsum_eq_Ioc muK_zero hR hZ hN, muK_eq, ← fA_mul_hA]
  rw [sum_Ioc_mul_weight fA hA (fun n => (W (n / Z) : ℂ)) N]
  -- drop the constraint `x.1 * x.2 ≤ N`: the other terms vanish
  rw [Finset.sum_filter_of_ne fun x hx hne => ?_]
  · rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := (Finset.mem_Ioc.1 hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [fSmooth]
    have hZd : 0 < Z / d := div_pos hZ hdR
    rw [tsum_eq_Ioc normSum_wf_zero hR hZd (N := N) (by
      calc R * (Z / d) ≤ R * Z := by
            apply mul_le_mul_of_nonneg_left _ hR0
            exact div_le_self hZ.le (by exact_mod_cast hd0)
        _ ≤ N := hN)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [coe_fA, coe_hA]
    have e : ((m * d : ℕ) : ℝ) / Z = (m : ℝ) / (Z / d) := by
      push_cast; field_simp
    simp only [e]; ring
  · -- a term with `x.1 * x.2 > N` vanishes
    by_contra hle
    apply hne
    have hlt : N < x.1 * x.2 := not_le.1 hle
    have : R < ((x.1 * x.2 : ℕ) : ℝ) / Z := by
      rw [lt_div_iff₀ hZ]
      calc R * Z ≤ N := hN
        _ < ((x.1 * x.2 : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [hR _ this, Complex.ofReal_zero, mul_zero]


/-- From `O(Z^α)` at infinity to a bound at every `Z > 0`: for small `Z` the sum vanishes, and in
between it is a bounded finite sum. -/
theorem fSmooth_uniform {W : ℝ → ℝ} (hW : Weight W) {α : ℝ} (hα : 0 ≤ α)
    (hb : fSmooth W =O[atTop] fun Z => Z ^ α) :
    ∃ K, 0 ≤ K ∧ ∀ Z, 0 < Z → ‖fSmooth W Z‖ ≤ K * Z ^ α := by
  obtain ⟨c, hc⟩ := hb.bound
  obtain ⟨Z0, hZ0⟩ := Filter.eventually_atTop.1 hc
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  set R1 := R + 1 with hR1def
  have hR1 : 0 < R1 := by linarith
  have hR1' : ∀ x, R1 < x → W x = 0 := fun x hx => hR x (by linarith)
  obtain ⟨M, hM⟩ := hW.compact.exists_bound_of_continuous hW.continuous
  set Z1 := max Z0 1 with hZ1def
  obtain ⟨N, hN⟩ := exists_nat_ge (R1 * Z1)
  set B := (∑ n ∈ Finset.Ioc 0 N, ‖normSum wf n‖) * M with hBdef
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hB0 : 0 ≤ B := mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hM0
  refine ⟨max (max c 0) (B * R1 ^ α), le_trans (le_max_right c 0) (le_max_left _ _),
    fun Z hZ => ?_⟩
  have hZa : 0 ≤ Z ^ α := Real.rpow_nonneg hZ.le α
  by_cases hZ1 : Z1 ≤ Z
  · have h := hZ0 Z (le_trans (le_max_left _ _) hZ1)
    rw [Real.norm_of_nonneg hZa] at h
    calc ‖fSmooth W Z‖ ≤ c * Z ^ α := h
      _ ≤ max c 0 * Z ^ α := mul_le_mul_of_nonneg_right (le_max_left _ _) hZa
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hZa
  · push Not at hZ1
    have hRZ : R1 * Z ≤ N := le_trans (mul_le_mul_of_nonneg_left hZ1.le hR1.le) hN
    have hfin := tsum_eq_Ioc normSum_wf_zero hR1' hZ hRZ
    by_cases hZs : R1 * Z < 1
    · have h0 : fSmooth W Z = 0 := by
        rw [fSmooth, hfin]
        refine Finset.sum_eq_zero fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
        have : R1 < n / Z := by rw [lt_div_iff₀ hZ]; linarith
        rw [hR1' _ this, Complex.ofReal_zero, mul_zero]
      rw [h0, norm_zero]
      exact mul_nonneg (le_trans (le_max_right c 0) (le_max_left _ _)) hZa
    · push Not at hZs
      have hsum : ‖fSmooth W Z‖ ≤ B := by
        rw [fSmooth, hfin]
        calc ‖∑ n ∈ Finset.Ioc 0 N, normSum wf n * (W (n / Z) : ℂ)‖
            ≤ ∑ n ∈ Finset.Ioc 0 N, ‖normSum wf n * (W (n / Z) : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ioc 0 N, ‖normSum wf n‖ * M := by
              refine Finset.sum_le_sum fun n _ => ?_
              rw [norm_mul, Complex.norm_real]
              exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
          _ = B := by rw [← Finset.sum_mul]
      calc ‖fSmooth W Z‖ ≤ B := hsum
        _ ≤ B * (R1 * Z) ^ α := le_mul_of_one_le_right hB0 (Real.one_le_rpow hZs hα)
        _ = B * R1 ^ α * Z ^ α := by rw [Real.mul_rpow hR1.le hZ.le]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hZa

/-- **S0′: the totient-weighted sums give S0's hypothesis.** If the smoothed sums
`Σ_𝔞 μ(𝔞)·Π_{P∣𝔞}(1 − 1/NP)·W(N𝔞/Z)` over the ideals of `ℤ[ω]` of norm prime to `6` are
`O(Z^{θ+ε})` for every weight and every `ε > 0`, with `θ ≥ 0`, then so are the smoothed Möbius sums
of `ζ·L(·, χ₋₃)`: `SmoothBound θ`. The proof is the identity `μ_K = f ⍟ h`, whose correction `h`
converges absolutely on `Re s > 0`. -/
theorem smoothBound_of_weightedBound {θ : ℝ} (hθ : 0 ≤ θ) (h : WeightedBound θ) :
    SmoothBound θ := by
  intro W hW ε hε
  have hα : 0 ≤ θ + ε := by linarith
  obtain ⟨K, hK0, hK⟩ := fSmooth_uniform hW hα (h W hW ε hε)
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  have hsumm := summable_hfun (σ := θ + ε) (by linarith)
  set Hs := ∑' d : ℕ, ‖hfun d‖ * (d : ℝ) ^ (-(θ + ε)) with hHs
  refine IsBigO.of_bound (K * Hs) ?_
  filter_upwards [eventually_gt_atTop 0] with Z hZ
  obtain ⟨N, hN⟩ := exists_nat_ge (R * Z)
  have hZa : 0 ≤ Z ^ (θ + ε) := Real.rpow_nonneg hZ.le _
  rw [smoothSum_eq_sum_h hR0 hR hZ hN, Real.norm_of_nonneg hZa]
  calc ‖∑ d ∈ Finset.Ioc 0 N, hfun d * fSmooth W (Z / d)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N, ‖hfun d‖ * ‖fSmooth W (Z / d)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        rw [norm_mul]
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, ‖hfun d‖ * (K * (Z / d) ^ (θ + ε)) := by
        refine Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (hK _ ?_) (norm_nonneg _)
        exact div_pos hZ (by exact_mod_cast (Finset.mem_Ioc.1 hd).1)
    _ = K * Z ^ (θ + ε) * ∑ d ∈ Finset.Ioc 0 N, ‖hfun d‖ * (d : ℝ) ^ (-(θ + ε)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.1 hd).1
        rw [Real.div_rpow hZ.le hd.le, Real.rpow_neg hd.le]
        field_simp
    _ ≤ K * Z ^ (θ + ε) * Hs :=
        mul_le_mul_of_nonneg_left (hsumm.sum_le_tsum _ fun _ _ => by positivity)
          (mul_nonneg hK0 hZa)
    _ = K * Hs * Z ^ (θ + ε) := by ring
end Transfer
end Eis

#print axioms Eis.normSum_mul
#print axioms Eis.normSum_prime_pow
#print axioms Eis.weighted_count
#print axioms Eis.tot_mul
#print axioms Eis.wf_mul
#print axioms Eis.wf_finset_prod
#print axioms Eis.fW_three
#print axioms Eis.fW_two
#print axioms Eis.fW_split
#print axioms Eis.fW_inert
#print axioms Eis.hfun_mul
#print axioms Eis.fA_mult
#print axioms Eis.hA_mult
#print axioms Eis.conv_small
#print axioms Eis.conv_prime_pow
#print axioms Eis.fA_mul_hA
#print axioms Eis.summable_of_mult_local
#print axioms Eis.norm_Hloc_le
#print axioms Eis.summable_hfun
#print axioms Eis.smoothSum_eq_sum_h
#print axioms Eis.fSmooth_uniform
#print axioms Eis.smoothBound_of_weightedBound
