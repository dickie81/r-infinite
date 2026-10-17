import KubotaCuspSums

/-! # The Dirichlet series behind the scattering coefficient (round 415)

S5f-9b of round 360's plan, part 3b, first half. Round 414 gave `S(m³) = N(m)³·Π_{P ∣ m, 3 ∉ P}(1 − 1/N(P))`.
This file sums that weight over the ideals of each norm and evaluates its Dirichlet series:
`Σ_n (Σ_{N𝔞=n} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P)))·n^{−u} = ζ_K(u)/((1 − 3^{−u−1})·ζ_K(u + 1))` for `Re u > 1`,
with `ζ_K = ζ·L(·, χ₋₃)`.

* **Primes over `3`** (**`three_mem_iff_dvd_absNorm`**, with `not_three_dvd_absNorm_of_factor`): a nonzero
  prime contains `3` exactly when `3` divides its norm.
* **The weight as a divisor sum** (`totP` and `gP`, definitions; **`totP_eq_sum_dvd`**, with `totP_eq_sum`
  and `mem_primesOff3_iff`): `Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P)) = Σ_{𝔡 ∣ 𝔞} [3 ∤ N(𝔡)]·μ(𝔡)/N(𝔡)`, by
  inclusion–exclusion and the bijection `T ↦ Π_{P∈T} P` from the sets of primes of `𝔞` off `3` onto its
  squarefree divisors of norm prime to `3`.
* **The finite identity** (**`normSum_totP`**, with `card_ofNorm_dvd`): `Σ_{N𝔞=n} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P))
  = Σ_{ab=n} [3 ∤ a]·m(a)/a·#{N𝔟 = b}`, with round 283's `m(a) = Σ_{N𝔡=a} μ(𝔡)`; the ideals of norm `n`
  divisible by `𝔡` are `𝔡𝔟` with `N(𝔟) = n/N(𝔡)`.
* **The Dirichlet series** (`mu3` and `eul3`, definitions; **`muK_eq_conv`**, **`LSeries_mu3_mul`** and
  **`LSeries_normSum_totP_mul`**, with `rK_eq_card`, `normSum_totP_eq_conv`, `LSeriesSummable_rK`,
  `chiInt_three`, `muK_three`, `muK_eq_zero_of_nine_dvd`, `LSeries_eul3`, `LSeriesSummable_eul3`,
  `LSeriesSummable_mu3` and `term_div_natCast`): the number of ideals of norm `n` is round 278's `r(n)`;
  `μ_K = μ₃ ⍟ (δ₁ − δ₃)` with `μ₃ = [3 ∤ ·]·μ_K`, so `L(μ₃, s)(1 − 3^{−s})ζ_K(s) = 1` (round 278's
  `LSeries_muK_mul`); and `Σ_n (Σ_{N𝔞=n} ⋯)·n^{−u}·(1 − 3^{−u−1})·ζ_K(u + 1) = ζ_K(u)` for `Re u > 1`.
-/

open NumberField Ideal UniqueFactorizationMonoid
open scoped LSeries.notation

noncomputable section

namespace Eis

/-! ### Primes over `3` -/

/-- A nonzero prime contains `3` exactly when `3` divides its norm. -/
theorem three_mem_iff_dvd_absNorm {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (3 : 𝓞 K) ∈ P ↔ 3 ∣ absNorm P := by
  constructor
  · intro h3
    have hd : absNorm P ∣ 3 ^ 2 := by
      rw [← absNorm_natCast_span_sq 3]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using h3))
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    rcases i with _ | i
    · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using he)) hP.ne_top
    · rw [he]; exact dvd_pow_self 3 (Nat.succ_ne_zero i)
  · intro h3
    have hq0 : absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h)
    obtain ⟨e, r, hr, hq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq0 3 (by norm_num)
    have hmem : ((absNorm P : ℕ) : 𝓞 K) ∈ P := Ideal.absNorm_mem P
    rw [hq, Nat.cast_mul, Nat.cast_pow] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact hP.mem_of_pow_mem e (by exact_mod_cast h)
    · exfalso
      have hd : absNorm P ∣ r ^ 2 := by
        rw [← absNorm_natCast_span_sq r]
        exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
      exact hr (Nat.prime_three.dvd_of_dvd_pow (dvd_trans h3 hd))

theorem not_three_dvd_absNorm_of_factor {I P : Ideal (𝓞 K)} (hI : ¬ 3 ∣ absNorm I)
    (hP : P ∈ normalizedFactors I) : (3 : 𝓞 K) ∉ P :=
  three_not_mem_of_factor (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hI)) hP

/-! ### The weight `Π_{P ∣ I, 3 ∉ P}(1 − 1/N(P))` -/

/-- `Π_{P ∣ I, 3 ∉ P}(1 − 1/N(P))`. -/
def totP (I : Ideal (𝓞 K)) : ℂ := ∏ P ∈ primesOff3 I, (1 - 1 / (absNorm P : ℂ))

theorem totP_eq_sum (I : Ideal (𝓞 K)) :
    totP I = ∑ T ∈ (primesOff3 I).powerset, (-1 : ℂ) ^ T.card / ∏ P ∈ T, (absNorm P : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (sum_powerset_inv (primesOff3 I))
  push_cast at h
  rw [totP]; exact h.symm

open Classical in
/-- `μ(𝔡)/N(𝔡)` on the ideals of norm prime to `3`, and `0` on the others. -/
def gP (J : Ideal (𝓞 K)) : ℂ := if 3 ∣ absNorm J then 0 else (moebius J : ℂ) / absNorm J

open Classical in
theorem mem_primesOff3_iff {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {P : Ideal (𝓞 K)} :
    P ∈ primesOff3 I ↔ P.IsPrime ∧ I ≤ P ∧ (3 : 𝓞 K) ∉ P := by
  rw [primesOff3, Finset.mem_filter, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI, and_assoc]

open Classical in
/-- **`Π(1 − 1/N(P))` as a divisor sum**: for `I ≠ 0` and a finite set `D` holding the divisors of `I`,
`Π_{P ∣ I, 3 ∉ P}(1 − 1/N(P)) = Σ_{𝔡 ∈ D, 𝔡 ∣ I} [3 ∤ N(𝔡)]·μ(𝔡)/N(𝔡)`. -/
theorem totP_eq_sum_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {D : Finset (Ideal (𝓞 K))}
    (hD : ∀ J, J ∣ I → J ∈ D) :
    totP I = ∑ J ∈ D, if J ∣ I then gP J else 0 := by
  set S := primesOff3 I with hSdef
  have hSP : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥ ∧ (3 : 𝓞 K) ∉ P ∧ I ≤ P := by
    intro P hP
    obtain ⟨hPp, hIP, h3⟩ := (mem_primesOff3_iff hI).1 hP
    refine ⟨hPp, fun h => hI ?_, h3, hIP⟩
    rw [h] at hIP; exact le_bot_iff.1 hIP
  have hprod : ∀ T ∈ S.powerset, ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ := fun T hT P hP =>
    ⟨(hSP P (Finset.mem_powerset.1 hT hP)).1, (hSP P (Finset.mem_powerset.1 hT hP)).2.1⟩
  have hdvd : ∀ T ∈ S.powerset, (∏ P ∈ T, P) ∣ I := by
    intro T hT
    have hle : T.val ≤ normalizedFactors I := (Multiset.le_iff_subset T.nodup).2 fun P hP =>
      (Ideal.mem_normalizedFactors_iff hI).2 ⟨(hSP P (Finset.mem_powerset.1 hT hP)).1,
        (hSP P (Finset.mem_powerset.1 hT hP)).2.2.2⟩
    have := Multiset.prod_dvd_prod_of_le hle
    rwa [Ideal.prod_normalizedFactors_eq_self hI, ← Multiset.map_id' T.val,
      ← Finset.prod_eq_multiset_prod] at this
  have hnot3 : ∀ T ∈ S.powerset, ¬ 3 ∣ absNorm (∏ P ∈ T, P) := by
    intro T hT h3
    rw [map_prod] at h3
    obtain ⟨P, hP, h3P⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).1 h3
    have hPS := hSP P (Finset.mem_powerset.1 hT hP)
    exact hPS.2.2.1 ((three_mem_iff_dvd_absNorm hPS.1 hPS.2.1).2 h3P)
  have hg : ∀ T ∈ S.powerset, gP (∏ P ∈ T, P) = (-1 : ℂ) ^ T.card / ∏ P ∈ T, (absNorm P : ℂ) := by
    intro T hT
    rw [gP, ite_eq_right (hnot3 T hT), moebius_finset_prod (hprod T hT), map_prod, Nat.cast_prod]
    push_cast; rfl
  have hinj : Set.InjOn (fun T : Finset (Ideal (𝓞 K)) => ∏ P ∈ T, P) ↑S.powerset := by
    intro T hT T' hT' h
    have h1 := (finset_prod_spec (hprod T hT)).2
    have h2 := (finset_prod_spec (hprod T' hT')).2
    simp only at h
    rw [h] at h1
    exact Finset.val_inj.1 (h1.symm.trans h2)
  rw [totP_eq_sum, ← Finset.sum_filter]
  have hsub : S.powerset.image (fun T => ∏ P ∈ T, P) ⊆ D.filter (· ∣ I) := by
    intro J hJ
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hJ
    exact Finset.mem_filter.2 ⟨hD _ (hdvd T hT), hdvd T hT⟩
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image hinj]
  · exact (Finset.sum_congr rfl hg).symm
  · intro J hJ hJn
    obtain ⟨-, hJI⟩ := Finset.mem_filter.1 hJ
    by_contra hne
    have h3 : ¬ 3 ∣ absNorm J := fun h => hne (by rw [gP, ite_eq_left h])
    have hsq : Squarefree J := by
      by_contra hsq
      exact hne (by rw [gP, ite_eq_right h3, moebius_of_not_squarefree hsq]; simp)
    have hJ0 : J ≠ ⊥ := fun h => hI (by rw [h] at hJI; exact (zero_dvd_iff.1 (by simpa using hJI)))
    have hnd := (squarefree_iff_nodup_normalizedFactors (by simpa using hJ0)).1 hsq
    apply hJn
    refine Finset.mem_image.2 ⟨(normalizedFactors J).toFinset, Finset.mem_powerset.2 fun P hP => ?_, ?_⟩
    · have hPJ := Multiset.mem_toFinset.1 hP
      have hPp := (Ideal.mem_normalizedFactors_iff hJ0).1 hPJ
      exact (mem_primesOff3_iff hI).2 ⟨hPp.1, le_trans (Ideal.le_of_dvd hJI) hPp.2,
        not_three_dvd_absNorm_of_factor h3 hPJ⟩
    · show ∏ P ∈ (normalizedFactors J).toFinset, P = J
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
        Ideal.prod_normalizedFactors_eq_self hJ0]

open Classical in
/-- The ideals of norm `n` divisible by `𝔡` correspond to the ideals of norm `n/N(𝔡)`. -/
theorem card_ofNorm_dvd {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) {n : ℕ} (hn : absNorm J ∣ n) :
    ((ofNorm n).filter (J ∣ ·)).card = (ofNorm (n / absNorm J)).card := by
  have hJ0 : absNorm J ≠ 0 := fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)
  symm
  refine Finset.card_bij (fun M _ => J * M) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter, mem_ofNorm]
    refine ⟨?_, dvd_mul_right J M⟩
    rw [map_mul, mem_ofNorm.1 hM, Nat.mul_div_cancel' hn]
  · intro M1 _ M2 _ h
    exact mul_left_cancel₀ (by simpa using hJ) h
  · intro I hI
    rw [Finset.mem_filter, mem_ofNorm] at hI
    obtain ⟨hIn, M, rfl⟩ := hI
    refine ⟨M, ?_, rfl⟩
    rw [mem_ofNorm, ← hIn, map_mul, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hJ0)]

open Classical in
/-- **The finite identity**: `Σ_{N𝔞=n} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P)) = Σ_{ab=n} [3 ∤ a]·m(a)/a·#{N𝔟 = b}`,
with round 283's `m(a) = Σ_{N𝔡=a} μ(𝔡)`. -/
theorem normSum_totP {n : ℕ} (hn : n ≠ 0) :
    normSum totP n = ∑ x ∈ n.divisorsAntidiagonal,
      (if 3 ∣ x.1 then 0 else (mI x.1 : ℂ) / x.1) * ((ofNorm x.2).card : ℂ) := by
  set D := n.divisors.biUnion ofNorm with hD
  have hDdvd : ∀ I ∈ ofNorm n, ∀ J, J ∣ I → J ∈ D := by
    intro I hI J hJ
    rw [hD, Finset.mem_biUnion]
    refine ⟨absNorm J, ?_, mem_ofNorm.2 rfl⟩
    rw [Nat.mem_divisors]
    exact ⟨(mem_ofNorm.1 hI) ▸ Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hJ), hn⟩
  have hI0 : ∀ I ∈ ofNorm n, I ≠ ⊥ := fun I hI => ne_bot_of_norm hn (mem_ofNorm.1 hI)
  calc normSum totP n = ∑ I ∈ ofNorm n, ∑ J ∈ D, (if J ∣ I then gP J else 0) := by
        rw [normSum]
        exact Finset.sum_congr rfl fun I hI => totP_eq_sum_dvd (hI0 I hI) (hDdvd I hI)
    _ = ∑ J ∈ D, gP J * (((ofNorm n).filter (J ∣ ·)).card : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        split_ifs <;> simp
    _ = ∑ a ∈ n.divisors, ∑ J ∈ ofNorm a, gP J * (((ofNorm n).filter (J ∣ ·)).card : ℂ) := by
        rw [hD, Finset.sum_biUnion]
        intro a _ b _ hab
        exact Finset.disjoint_left.2 fun J hJa hJb =>
          hab ((mem_ofNorm.1 hJa).symm.trans (mem_ofNorm.1 hJb))
    _ = ∑ a ∈ n.divisors, (if 3 ∣ a then 0 else (mI a : ℂ) / a) * ((ofNorm (n / a)).card : ℂ) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have hadvd : a ∣ n := Nat.dvd_of_mem_divisors ha
        have ha0 : a ≠ 0 := fun h => hn (by rw [h] at hadvd; exact zero_dvd_iff.1 hadvd)
        have e : ∀ J ∈ ofNorm a, gP J * (((ofNorm n).filter (J ∣ ·)).card : ℂ) =
            gP J * ((ofNorm (n / a)).card : ℂ) := fun J hJ => by
          have hJa := mem_ofNorm.1 hJ
          rw [card_ofNorm_dvd (ne_bot_of_norm ha0 hJa) (hJa ▸ hadvd), hJa]
        rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
        congr 1
        by_cases h3 : 3 ∣ a
        · rw [ite_eq_left h3]
          exact Finset.sum_eq_zero fun J hJ => by
            rw [gP, ite_eq_left (show 3 ∣ absNorm J by rw [mem_ofNorm.1 hJ]; exact h3)]
        · rw [ite_eq_right h3, mI, Int.cast_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun J hJ => by
            rw [gP, ite_eq_right (show ¬ 3 ∣ absNorm J by rw [mem_ofNorm.1 hJ]; exact h3), mem_ofNorm.1 hJ]
    _ = _ := (Nat.sum_divisorsAntidiagonal
        (fun a b => (if 3 ∣ a then 0 else (mI a : ℂ) / a) * ((ofNorm b).card : ℂ))).symm

/-! ### The Dirichlet series -/

section Series

open ArithmeticFunction LSeries HalfPlaneS0 DirichletCharacter

/-- The number of ideals of norm `n` is round 278's `r(n) = Σ_{d ∣ n} χ₋₃(d)`. -/
theorem rK_eq_card {n : ℕ} (hn : n ≠ 0) : rK n = ((ofNorm n).card : ℂ) := by
  have h1 : ((ofNorm n).card : ℂ) = ((rA n : ℤ) : ℂ) := by rw [rA_apply hn]; push_cast; rfl
  rw [h1, rA_eq, ArithmeticFunction.mul_apply, rK, LSeries.convolution_def]
  push_cast
  conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨-, hx2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
  simp [chiA_apply, chi3_eq_chiInt, hx2]

open Classical in
theorem normSum_totP_eq_conv {n : ℕ} (hn : n ≠ 0) :
    normSum totP n = ((fun a => (if 3 ∣ a then 0 else muK a) / a) ⍟ rK) n := by
  rw [normSum_totP hn, LSeries.convolution_def]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
  rw [rK_eq_card hx2, mI_eq_muK]
  split_ifs <;> simp

theorem LSeriesSummable_rK {u : ℂ} (hu : 1 < u.re) : LSeriesSummable rK u :=
  (LSeriesSummable_one_iff.mpr hu).convolution (LSeriesSummable_of_one_lt_re PsiOmega.chi3 hu)

open Classical in
/-- `μ_K` with its Euler factor at `3` removed. -/
def mu3 (n : ℕ) : ℂ := if 3 ∣ n then 0 else muK n

/-- `δ₁ − δ₃`, whose `L`-series is `1 − 3^{−s}`. -/
def eul3 (n : ℕ) : ℂ := if n = 1 then 1 else if n = 3 then -1 else 0

theorem chiInt_three : chiInt 3 = 0 := by simp [chiInt]

theorem muK_three : muK 3 = -1 := by
  have h := muK_prime_pow Nat.prime_three 1
  rw [pow_one] at h
  rw [h, chiInt_three]; simp

theorem muK_eq_zero_of_nine_dvd {n : ℕ} (hn : n ≠ 0) (h9 : 9 ∣ n) : muK n = 0 := by
  obtain ⟨e, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have he : 2 ≤ e := by
    by_contra he
    push Not at he
    have hc : Nat.Coprime 9 r := Nat.Coprime.pow_left 2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hr)
    have := hc.dvd_of_dvd_mul_right h9
    interval_cases e <;> simp_all
  rw [muK_mul ((Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hr))),
    muK_prime_pow Nat.prime_three e, chiInt_three]
  have h0 : e ≠ 0 := by omega
  have h1 : e ≠ 1 := by omega
  rw [ite_eq_right h0, ite_eq_right h1]
  split_ifs <;> simp

theorem muK_eq_conv {n : ℕ} (hn : n ≠ 0) : muK n = (mu3 ⍟ eul3) n := by
  rw [LSeries.convolution_def]
  simp only
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => mu3 a * eul3 b)]
  by_cases h3 : 3 ∣ n
  · rw [Finset.sum_eq_add 1 3 (by norm_num) ?_ ?_ ?_]
    · obtain ⟨m, rfl⟩ := h3
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      rw [Nat.div_one, Nat.mul_div_cancel_left m (by norm_num), eul3, eul3, mu3]
      simp only [ite_eq_left (dvd_mul_right 3 m), ite_false,
        show (3 : ℕ) ≠ 1 by norm_num, ite_true, mul_neg, mul_one, zero_add]
      by_cases h3m : 3 ∣ m
      · rw [mu3, ite_eq_left h3m, neg_zero]
        exact muK_eq_zero_of_nine_dvd hn (by obtain ⟨k, rfl⟩ := h3m; exact ⟨k, by ring⟩)
      · rw [mu3, ite_eq_right h3m, muK_mul ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3m),
          muK_three]
        ring
    · intro c _ hc
      rw [eul3, ite_eq_right hc.1, ite_eq_right hc.2, mul_zero]
    · intro h; exact absurd (Nat.one_mem_divisors.2 hn) h
    · intro h; exact absurd (Nat.mem_divisors.2 ⟨h3, hn⟩) h
  · rw [Finset.sum_eq_single 1 ?_ ?_]
    · rw [Nat.div_one, eul3, ite_eq_left rfl, mul_one, mu3, ite_eq_right h3]
    · intro c hc hc1
      have hc3 : c ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_divisors hc)
      rw [eul3, ite_eq_right hc1, ite_eq_right hc3, mul_zero]
    · intro h; exact absurd (Nat.one_mem_divisors.2 hn) h

theorem LSeries_eul3 (w : ℂ) : LSeries eul3 w = 1 - 3 ^ (-w) := by
  rw [LSeries, tsum_eq_sum (s := {1, 3}) ?_, Finset.sum_pair (by norm_num)]
  · rw [term_of_ne_zero one_ne_zero, term_of_ne_zero (by norm_num), eul3, eul3]
    simp only [ite_true, show (3 : ℕ) ≠ 1 by norm_num, ite_false, Nat.cast_one, Complex.one_cpow,
      div_one, Nat.cast_ofNat, Complex.cpow_neg]
    ring
  · intro n hn
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [term_def, eul3, ite_eq_right hn.1, ite_eq_right hn.2]
    simp

theorem LSeriesSummable_eul3 (w : ℂ) : LSeriesSummable eul3 w := by
  refine summable_of_ne_finset_zero (s := {1, 3}) fun n hn => ?_
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rw [term_def, eul3, ite_eq_right hn.1, ite_eq_right hn.2]
  simp

theorem LSeriesSummable_mu3 {w : ℂ} (hw : 1 < w.re) : LSeriesSummable mu3 w := by
  have h := (LSeriesSummable_muK hw).norm
  refine Summable.of_norm_bounded h fun n => ?_
  rw [term_def, term_def, mu3]
  split_ifs <;> simp; positivity

/-- **`μ_K` without its factor at `3`**: `L(μ₃, s)·(1 − 3^{−s})·ζ(s)L(s, χ₋₃) = 1` on `Re s > 1`. -/
theorem LSeries_mu3_mul {w : ℂ} (hw : 1 < w.re) :
    LSeries mu3 w * ((1 - 3 ^ (-w)) * (riemannZeta w * LFunction PsiOmega.chi3 w)) = 1 := by
  have h1 : LSeries muK w = LSeries (mu3 ⍟ eul3) w := LSeries_congr (fun hn => muK_eq_conv hn) w
  rw [LSeries_convolution' (LSeriesSummable_mu3 hw) (LSeriesSummable_eul3 w), LSeries_eul3] at h1
  have h2 := LSeries_muK_mul hw
  rw [h1] at h2
  linear_combination h2

theorem term_div_natCast (f : ℕ → ℂ) (u : ℂ) :
    term (fun a => f a / a) u = term f (u + 1) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.2 hn), Complex.cpow_one, div_div, mul_comm]

open Classical in
/-- **The Dirichlet series**: for `Re u > 1`,
`Σ_n (Σ_{N𝔞=n} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P)))·n^{−u}·(1 − 3^{−u−1})·ζ_K(u + 1) = ζ_K(u)`,
with `ζ_K = ζ·L(·, χ₋₃)`. -/
theorem LSeries_normSum_totP_mul {u : ℂ} (hu : 1 < u.re) :
    LSeries (normSum totP) u * ((1 - 3 ^ (-(u + 1))) *
      (riemannZeta (u + 1) * LFunction PsiOmega.chi3 (u + 1))) = riemannZeta u * LFunction PsiOmega.chi3 u := by
  have hu1 : 1 < (u + 1).re := by simp; linarith
  have hf : (fun a : ℕ => (if 3 ∣ a then 0 else muK a) / (a : ℂ)) = fun a => mu3 a / a := rfl
  have hsum : LSeriesSummable (fun a : ℕ => mu3 a / a) u := by
    have := LSeriesSummable_mu3 hu1
    unfold LSeriesSummable at this ⊢
    rwa [term_div_natCast]
  have hL : LSeries (fun a : ℕ => mu3 a / a) u = LSeries mu3 (u + 1) := by
    unfold LSeries; rw [term_div_natCast]
  have hc : LSeries (normSum totP) u = LSeries ((fun a : ℕ => mu3 a / a) ⍟ rK) u :=
    LSeries_congr (fun hn => by rw [normSum_totP_eq_conv hn, hf]) u
  rw [hc, LSeries_convolution' hsum (LSeriesSummable_rK hu), LSeries_rK hu, hL]
  have h := LSeries_mu3_mul hu1
  linear_combination (riemannZeta u * LFunction PsiOmega.chi3 u) * h

end Series

end Eis

end

#print axioms Eis.three_mem_iff_dvd_absNorm
#print axioms Eis.not_three_dvd_absNorm_of_factor
#print axioms Eis.totP_eq_sum
#print axioms Eis.mem_primesOff3_iff
#print axioms Eis.totP_eq_sum_dvd
#print axioms Eis.card_ofNorm_dvd
#print axioms Eis.normSum_totP
#print axioms Eis.rK_eq_card
#print axioms Eis.normSum_totP_eq_conv
#print axioms Eis.LSeriesSummable_rK
#print axioms Eis.chiInt_three
#print axioms Eis.muK_three
#print axioms Eis.muK_eq_zero_of_nine_dvd
#print axioms Eis.muK_eq_conv
#print axioms Eis.LSeries_eul3
#print axioms Eis.LSeriesSummable_eul3
#print axioms Eis.LSeriesSummable_mu3
#print axioms Eis.LSeries_mu3_mul
#print axioms Eis.term_div_natCast
#print axioms Eis.LSeries_normSum_totP_mul
