import EisensteinIdealCount

/-!
# S2′: the family's mean square gives a zero-free half-plane (round 288)

The family of round 282 is `A_Z(u) = Σ_𝔞 μ(𝔞)(u/𝔞)₆ W(N𝔞/Z)` over the ideals `𝔞` of `ℤ[ω]` of norm prime
to `6` (`famSum`). Its mean square at `σ` is the displayed hypothesis `MeanSquare σ`: for every weight
`W` and `ε > 0`, `Σ_{z∈T} |A_Z(z)|² = O(Z^{2+σ+ε})` over finite sets `T` of nonzero `z` with
`N(z) ≤ Z^{1+σ}`. This file derives from it the hypothesis of round 285's S0′, and with S0′ and S0 the
conditional milestone (`ne_zero_of_meanSquare`): `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on
`Re s > (11 + 5σ)/12`.
* **Sixth powers** (`sym6_pow_six`): for `𝔞` of norm prime to `6`, `(b⁶/𝔞)₆` is `1` if `b` lies in no
  prime factor of `𝔞`, and `0` otherwise.
* **Inclusion–exclusion** (`card_coprime`, `abs_card_coprime_sub_le`): the ideals `𝔟` of norm at most
  `Y` divisible by no prime of a set `S` number `κY·Π_{P∈S}(1 − 1/N P) + E`, `|E| ≤ 2^{|S|}(5√Y + κ)`,
  from round 287's count.
* **The average** (`norm_sum_famSum_sub_le`): `Σ_{N𝔟≤Y} A_Z(gen(𝔟)⁶) = κY·Σ_n f(n)W(n/Z) + Err`, where
  `f` is round 285's totient-weighted coefficient and `|Err| ≤ B(5√Y + κ)·Σ_{N𝔞≤M} 2^{ω(𝔞)}` for `W`
  bounded by `B` and vanishing beyond `M/Z`. The divisor sum is `O(M^{1+ε})` (`sum_w2_le`, through
  round 285's `summable_of_mult_local`).
* **Cauchy–Schwarz** over the sixth powers, which are distinct (`gen_pow_six_injOn`) and of norm at most
  `Y⁶`, against `MeanSquare σ` with `Y = Z^{(1+σ)/6}` (`weightedBound_of_meanSquare`).

`MeanSquare σ` is a displayed hypothesis, the socket for S3–S5 of the round-277 plan.
-/

open NumberField Ideal UniqueFactorizationMonoid

namespace Eis

/-! ### The symbol at sixth powers -/

section SixthPowers

theorem absNorm_six : absNorm (span {(6 : 𝓞 K)}) = 36 := by
  have := absNorm_natCast_span_sq 6
  simpa using this

/-- A prime factor of an ideal of norm prime to `6` does not contain `6`. -/
theorem six_not_mem_of_factor {I P : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6)
    (hP : P ∈ normalizedFactors I) : (6 : 𝓞 K) ∉ P := by
  intro h6
  have hPprime := prime_of_normalized_factor P hP
  have hPI : P ∣ I := dvd_of_mem_normalizedFactors hP
  have hNPI : absNorm P ∣ absNorm I := absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPI)
  have hNP6 : absNorm P ∣ 36 := by
    rw [← absNorm_six]
    exact absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h6)
  have hc : (absNorm P).Coprime 36 := by
    rw [show (36 : ℕ) = 6 ^ 2 by norm_num]
    exact (Nat.Coprime.coprime_dvd_left hNPI hI).pow_right 2
  have h1 : absNorm P = 1 := Nat.Coprime.eq_one_of_dvd hc hNP6
  exact (Ideal.isPrime_of_prime hPprime).ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem isMaximal_of_factor {I P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors I) : P.IsMaximal := by
  have hPprime := prime_of_normalized_factor P hP
  exact (Ideal.isPrime_of_prime hPprime).isMaximal hPprime.ne_zero

open Classical in
/-- `χ_P(b)^6 = [b ∉ P]`. -/
theorem chiP_pow_six {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (h6 : (6 : 𝓞 K) ∉ P) (b : 𝓞 K) :
    chiP P b ^ 6 = if b ∈ P then 0 else 1 := by
  unfold chiP
  split_ifs with h hb
  · rw [(Ideal.Quotient.eq_zero_iff_mem).2 hb, MulChar.map_zero]; norm_num
  · rw [← MulChar.pow_apply' _ (by norm_num : (6 : ℕ) ≠ 0), chi6_pow_six]
    apply MulChar.one_apply
    exact isUnit_iff_ne_zero.2 fun h' => hb ((Ideal.Quotient.eq_zero_iff_mem).1 h')
  · exact absurd ⟨hP, h6⟩ h
  · exact absurd ⟨hP, h6⟩ h

theorem sym6_pow_succ (a : 𝓞 K) (I : Ideal (𝓞 K)) (n : ℕ) :
    sym6 (a ^ (n + 1)) I = sym6 a I ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, sym6_mul_left, ih, ← pow_succ]

theorem multiset_prod_ite {M : Multiset (Ideal (𝓞 K))} (p : Ideal (𝓞 K) → Prop) [DecidablePred p] :
    (M.map fun P => if p P then (0 : ℂ) else 1).prod = if ∀ P ∈ M, ¬ p P then 1 else 0 := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih]
    by_cases ha : p a
    · simp [ha]
    · by_cases hM : ∀ P ∈ M, ¬ p P
      · simp [ha]
      · simp only [ha, hM, ite_false, mul_zero]
        rw [ite_eq_right]
        intro h; exact hM fun P hP => h P (Multiset.mem_cons_of_mem hP)

open Classical in
/-- **The family at sixth powers**: for `𝔞` of norm prime to `6`, `(b⁶/𝔞)₆ = 1` if `b` lies in no
prime factor of `𝔞`, and `0` otherwise. -/
theorem sym6_pow_six {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (b : 𝓞 K) :
    sym6 (b ^ 6) I = if ∀ P ∈ normalizedFactors I, b ∉ P then 1 else 0 := by
  classical
  rw [sym6_pow_succ b I 5, sym6, ← Multiset.prod_map_pow]
  rw [Multiset.map_congr rfl fun P hP => chiP_pow_six (isMaximal_of_factor hP)
    (six_not_mem_of_factor hI hP) b]
  exact multiset_prod_ite (fun P => b ∈ P)

end SixthPowers


/-! ### Ideals prime to a squarefree ideal, by inclusion–exclusion -/

section Coprime

/-- A product of distinct maximal ideals divides `J` iff each does. -/
theorem prod_dvd_iff {T : Finset (Ideal (𝓞 K))} (hT : ∀ P ∈ T, P.IsMaximal) (J : Ideal (𝓞 K)) :
    (∏ P ∈ T, P) ∣ J ↔ ∀ P ∈ T, P ∣ J := by
  constructor
  · intro h P hP; exact dvd_trans (Finset.dvd_prod_of_mem (fun Q : Ideal (𝓞 K) => Q) hP) h
  · intro h
    have hpair : (↑T : Set (Ideal (𝓞 K))).Pairwise (Function.onFun IsCoprime fun P => P) :=
      fun P hP Q hQ hPQ =>
        Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne (hT P hP) (hT Q hQ) hPQ)
    exact Finset.prod_dvd_of_coprime (s := fun P => P) (t := T) hpair h

theorem prod_ne_bot {T : Finset (Ideal (𝓞 K))} (hT : ∀ P ∈ T, P.IsMaximal) : (∏ P ∈ T, P) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun P hP h => by
    have := (hT P hP).ne_top
    have hb : P = ⊥ := by rw [← Ideal.zero_eq_bot]; exact h
    exact Ring.ne_bot_of_isMaximal_of_not_isField (hT P hP) (RingOfIntegers.not_isField K) hb

open Classical in
/-- Inclusion–exclusion at one ideal: `[no P ∈ S divides J] = Σ_{T ⊆ S} (−1)^{|T|}[every P ∈ T divides J]`. -/
theorem indicator_coprime (S : Finset (Ideal (𝓞 K))) (J : Ideal (𝓞 K)) :
    (if ∀ P ∈ S, ¬ P ∣ J then (1 : ℝ) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (if ∀ P ∈ T, P ∣ J then 1 else 0) := by
  have hset : S.powerset.filter (fun T => ∀ P ∈ T, P ∣ J) = (S.filter fun P => P ∣ J).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
    constructor
    · rintro ⟨h1, h2⟩ P hP; exact ⟨h1 hP, h2 P hP⟩
    · intro h; exact ⟨fun P hP => (h hP).1, fun P hP => (h hP).2⟩
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hset]
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (Finset.sum_powerset_neg_one_pow_card (x := S.filter fun P => P ∣ J))
  push_cast at h
  rw [h]
  congr 1
  apply propext
  rw [Finset.filter_eq_empty_iff]

open Classical in
/-- **The ideals of norm at most `Y` divisible by no `P ∈ S`**, for distinct maximal `P`:
`Σ_{T ⊆ S} (−1)^{|T|}·#{𝔞 ≠ 0 : N𝔞 ≤ Y/Π_{P∈T} N P}`. -/
theorem card_coprime {S : Finset (Ideal (𝓞 K))} (hS : ∀ P ∈ S, P.IsMaximal) {Y : ℝ} (hY : 0 ≤ Y) :
    (((idealsLe Y).filter (fun J => ∀ P ∈ S, ¬ P ∣ J)).card : ℝ) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (idealCount (Y / ∏ P ∈ T, (absNorm P : ℝ)) : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  simp_rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, indicator_coprime S]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTm : ∀ P ∈ T, P.IsMaximal := fun P hP => hS P (Finset.mem_powerset.1 hT hP)
  rw [← Finset.mul_sum]
  congr 1
  have hc := card_multiples (prod_ne_bot hTm) hY
  rw [map_prod, Nat.cast_prod] at hc
  rw [← hc, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [prod_dvd_iff hTm J]
  split_ifs <;> simp

/-- `Σ_{T ⊆ S} (−1)^{|T|}/Π_{P∈T} N P = Π_{P∈S} (1 − 1/N P)`. -/
theorem sum_powerset_inv (S : Finset (Ideal (𝓞 K))) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card / ∏ P ∈ T, (absNorm P : ℝ) =
      ∏ P ∈ S, (1 - 1 / (absNorm P : ℝ)) := by
  classical
  have := Finset.prod_add (fun P => -1 / (absNorm P : ℝ)) (fun _ => (1 : ℝ)) S
  simp only [Finset.prod_const_one, mul_one] at this
  rw [Finset.prod_congr rfl fun P _ => (show 1 - 1 / (absNorm P : ℝ) = -1 / (absNorm P : ℝ) + 1 by ring),
    this]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_div_distrib, Finset.prod_const]

open Classical in
/-- **The count with its main term**: `#{𝔟 : N𝔟 ≤ Y, no P ∈ S divides 𝔟} = κY·Π_{P∈S}(1 − 1/NP) + E`
with `|E| ≤ 2^{|S|}(5√Y + κ)`. -/
theorem abs_card_coprime_sub_le {S : Finset (Ideal (𝓞 K))} (hS : ∀ P ∈ S, P.IsMaximal) {Y : ℝ}
    (hY : 0 ≤ Y) :
    |(((idealsLe Y).filter (fun J => ∀ P ∈ S, ¬ P ∣ J)).card : ℝ) -
      kappa * Y * ∏ P ∈ S, (1 - 1 / (absNorm P : ℝ))| ≤ 2 ^ S.card * (5 * √Y + kappa) := by
  classical
  rw [card_coprime hS hY, ← sum_powerset_inv, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hk := kappa_pos
  calc ∑ T ∈ S.powerset, |(-1 : ℝ) ^ T.card * (idealCount (Y / ∏ P ∈ T, (absNorm P : ℝ)) : ℝ) -
        kappa * Y * ((-1 : ℝ) ^ T.card / ∏ P ∈ T, (absNorm P : ℝ))|
      ≤ ∑ T ∈ S.powerset, (5 * √Y + kappa) := by
        refine Finset.sum_le_sum fun T hT => ?_
        have hTm : ∀ P ∈ T, P.IsMaximal := fun P hP => hS P (Finset.mem_powerset.1 hT hP)
        have hN1 : ∀ P ∈ T, (1 : ℝ) ≤ absNorm P := fun P hP => by
          have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField (hTm P hP)
            (RingOfIntegers.not_isField K)
          have : absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h)
          exact_mod_cast Nat.one_le_iff_ne_zero.2 this
        have hprod : (1 : ℝ) ≤ ∏ P ∈ T, (absNorm P : ℝ) := Finset.one_le_prod₀ hN1
        have hpos : (0 : ℝ) < ∏ P ∈ T, (absNorm P : ℝ) := by linarith
        set y := Y / ∏ P ∈ T, (absNorm P : ℝ)
        have hy0 : 0 ≤ y := div_nonneg hY hpos.le
        have hyY : y ≤ Y := div_le_self hY hprod
        have e : (-1 : ℝ) ^ T.card * (idealCount y : ℝ) -
            kappa * Y * ((-1 : ℝ) ^ T.card / ∏ P ∈ T, (absNorm P : ℝ)) =
            (-1 : ℝ) ^ T.card * ((idealCount y : ℝ) - kappa * y) := by
          simp only [y]; field_simp
        rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        calc |(idealCount y : ℝ) - kappa * y| ≤ 5 * √y + kappa := abs_idealCount_sub_le hy0
          _ ≤ 5 * √Y + kappa := by gcongr
    _ = 2 ^ S.card * (5 * √Y + kappa) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]; push_cast; ring

end Coprime


/-! ### `Σ_{N𝔞 ≤ X} 2^{ω(𝔞)} ≪ X^{1+ε}` over squarefree `𝔞` -/

section TwoOmega

open Classical in
/-- `2^{ω(𝔞)}` on squarefree ideals, `0` otherwise. -/
noncomputable def w2 (I : Ideal (𝓞 K)) : ℂ :=
  if Squarefree I then 2 ^ (normalizedFactors I).card else 0

theorem w2_mul (J L : Ideal (𝓞 K)) (h : IsRelPrime J L) : w2 (J * L) = w2 J * w2 L := by
  classical
  unfold w2
  by_cases hJ : Squarefree J <;> by_cases hL : Squarefree L
  · have hJL : Squarefree (J * L) := squarefree_mul_iff.2 ⟨h, hJ, hL⟩
    have hJ0 : J ≠ 0 := hJ.ne_zero
    have hL0 : L ≠ 0 := hL.ne_zero
    rw [ite_eq_left hJL, ite_eq_left hJ, ite_eq_left hL, normalizedFactors_mul hJ0 hL0,
      Multiset.card_add, pow_add]
  · rw [ite_eq_right (fun h' => hL (squarefree_mul_iff.1 h').2.2), ite_eq_right hL, mul_zero]
  · rw [ite_eq_right (fun h' => hJ (squarefree_mul_iff.1 h').2.1), ite_eq_right hJ, zero_mul]
  · rw [ite_eq_right (fun h' => hJ (squarefree_mul_iff.1 h').2.1), ite_eq_right hJ, zero_mul]

theorem w2_eq_zero_of_not_squarefree {I : Ideal (𝓞 K)} (hI : ¬ Squarefree I) : w2 I = 0 := by
  classical
  unfold w2; rw [ite_eq_right hI]

/-- The values of `Σ_{N𝔞 = p^k} 2^{ω(𝔞)}`: at most `4` for `k = 1, 2`, and `0` for `k ≥ 3`. -/
theorem norm_normSum_w2_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖normSum w2 (p ^ k)‖ ≤ if k = 0 then 1 else if k ≤ 2 then 4 else 0 := by
  classical
  rw [normSum_prime_pow w2 (fun I hI => w2_eq_zero_of_not_squarefree hI) hp k]
  have hterm : ∀ T ∈ (pFactors p).toFinset.powerset.filter (fun T => ∏ P ∈ T, absNorm P = p ^ k),
      w2 (∏ P ∈ T, P) = (2 : ℂ) ^ T.card := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have hTp : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ := fun P hP =>
      pFactors_prime hp (Multiset.mem_toFinset.1 (Finset.mem_powerset.1 hT.1 hP))
    obtain ⟨hsq, hnf⟩ := finset_prod_spec hTp
    unfold w2; rw [ite_eq_left hsq, hnf, Finset.card_val]
  rw [Finset.sum_congr rfl hterm]
  rcases pFactors_cases hp with ⟨P, hf, hPn⟩ | ⟨hc2, hall⟩
  · -- one prime of norm `p²`
    have hS : ∀ Q ∈ (pFactors p).toFinset, absNorm Q = p ^ 2 := by
      intro Q hQ; rw [hf] at hQ; simp at hQ; rw [hQ]; exact hPn
    rw [weighted_count hp two_pos _ hS k (fun j => (2 : ℂ) ^ j), hf, Multiset.toFinset_singleton,
      Finset.card_singleton]
    rcases k with _ | _ | _ | k
    · simp
    · simp
    · simp; norm_num
    · rw [ite_eq_right (show k + 1 + 1 + 1 ≠ 0 by omega),
        ite_eq_right (show ¬ (k + 1 + 1 + 1 ≤ 2) by omega)]
      split_ifs with hd
      · obtain ⟨j, hj⟩ := hd
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      · simp
  · -- two primes (with multiplicity) of norm `p`
    have hS : ∀ Q ∈ (pFactors p).toFinset, absNorm Q = p ^ 1 := by
      intro Q hQ; rw [pow_one]; exact hall Q (Multiset.mem_toFinset.1 hQ)
    have hcard : (pFactors p).toFinset.card ≤ 2 := by
      rw [← hc2]; exact Multiset.toFinset_card_le _
    rw [weighted_count hp one_pos _ hS k (fun j => (2 : ℂ) ^ j)]
    simp only [Nat.one_dvd, ite_true, Nat.div_one]
    set g := (pFactors p).toFinset.card
    rw [norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_ofNat]
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · simp
      · have : (g : ℝ) ≤ 2 := by exact_mod_cast hcard
        norm_num; linarith
      · have h1 : g.choose 2 ≤ 1 := by interval_cases g <;> simp
        have h2 : ((g.choose 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
        norm_num; nlinarith
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul,
        ite_eq_right (by omega), ite_eq_right (by omega)]

/-- **`Σ_n |Σ_{N𝔞=n} 2^{ω(𝔞)}| n^{−1−ε}` converges** for every `ε > 0`. -/
theorem summable_w2 {ε : ℝ} (hε : 0 < ε) :
    Summable fun n : ℕ => ‖normSum w2 n‖ * (n : ℝ) ^ (-(1 + ε)) := by
  have hw1 : normSum w2 1 = 1 := by
    have := norm_normSum_w2_le Nat.prime_two 0
    classical
    have hof : ofNorm 1 = {(⊤ : Ideal (𝓞 K))} := by
      ext I; simp [mem_ofNorm, Ideal.absNorm_eq_one_iff]
    rw [normSum, hof, Finset.sum_singleton, w2, ite_eq_left (by rw [← Ideal.one_eq_top]; exact squarefree_one),
      ← Ideal.one_eq_top, normalizedFactors_one]
    simp
  have h0 : ((0 : ℕ) : ℝ) ^ (-(1 + ε)) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
  refine summable_of_mult_local (g := fun n => ‖normSum w2 n‖ * (n : ℝ) ^ (-(1 + ε)))
    (fun n => by positivity) ?_ (by simp [hw1]) (fun {m n} hmn => ?_) (fun {p} hp => ?_)
    (A := 8) (by norm_num) hε (fun {p} hp => ?_)
  · simp only [h0, mul_zero]
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [zero_mul, h0, mul_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [mul_zero, h0]
    rw [normSum_mul w2 w2_mul hmn hm hn, norm_mul, Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity)]
    ring
  · refine summable_of_ne_finset_zero (s := Finset.range 3) fun k hk => ?_
    rw [Finset.mem_range, not_lt] at hk
    have h := norm_normSum_w2_le hp k
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h
    rw [le_antisymm h (norm_nonneg _), zero_mul]
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpos : (0 : ℝ) < p := by linarith
    rw [tsum_eq_sum (s := Finset.range 3) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      have h := norm_normSum_w2_le hp k
      rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h
      rw [le_antisymm h (norm_nonneg _), zero_mul]]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 := norm_normSum_w2_le hp 0
    have h1 := norm_normSum_w2_le hp 1
    have h2 := norm_normSum_w2_le hp 2
    simp only [one_ne_zero, ite_false, show (1 : ℕ) ≤ 2 by norm_num, ite_true, show (2 : ℕ) ≠ 0 by norm_num,
      le_refl, ite_true] at h0 h1 h2
    have e1 : (((p ^ 1 : ℕ) : ℝ)) ^ (-(1 + ε)) = (p : ℝ) ^ (-(1 + ε)) := by simp
    have e2 : (((p ^ 2 : ℕ) : ℝ)) ^ (-(1 + ε)) ≤ (p : ℝ) ^ (-(1 + ε)) := by
      rw [Nat.cast_pow]
      apply Real.rpow_le_rpow_of_nonpos hpos (by nlinarith) (by linarith)
    have hq : 0 ≤ (p : ℝ) ^ (-(1 + ε)) := by positivity
    have hq2 : 0 ≤ (((p ^ 2 : ℕ) : ℝ)) ^ (-(1 + ε)) := by positivity
    simp only [pow_zero, Nat.cast_one, Real.one_rpow, mul_one] at h0 ⊢
    rw [e1]
    nlinarith [norm_nonneg (normSum w2 (p ^ 1)), norm_nonneg (normSum w2 (p ^ 2))]

/-- **`Σ_{n ≤ M} Σ_{N𝔞=n} 2^{ω(𝔞)} ≤ C_ε M^{1+ε}`.** -/
theorem sum_w2_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ M : ℕ, ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ ≤ C * (M : ℝ) ^ (1 + ε) := by
  refine ⟨∑' n : ℕ, ‖normSum w2 n‖ * (n : ℝ) ^ (-(1 + ε)),
    tsum_nonneg fun n => by positivity, fun M => ?_⟩
  have hs := summable_w2 hε
  calc ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖
      ≤ ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ * (n : ℝ) ^ (-(1 + ε)) * (M : ℝ) ^ (1 + ε) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
        have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Ioc.1 hn).2
        have h1 : 1 ≤ (n : ℝ) ^ (-(1 + ε)) * (M : ℝ) ^ (1 + ε) := by
          rw [Real.rpow_neg hn0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
          exact Real.rpow_le_rpow hn0.le hnM (by linarith)
        rw [mul_assoc]
        exact le_mul_of_one_le_right (norm_nonneg _) h1
    _ = (∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ * (n : ℝ) ^ (-(1 + ε))) * (M : ℝ) ^ (1 + ε) := by
        rw [Finset.sum_mul]
    _ ≤ (∑' n : ℕ, ‖normSum w2 n‖ * (n : ℝ) ^ (-(1 + ε))) * (M : ℝ) ^ (1 + ε) :=
        mul_le_mul_of_nonneg_right (hs.sum_le_tsum _ fun n _ => by positivity) (by positivity)

end TwoOmega


/-! ### The family and its average over sixth powers -/

section Family

open HalfPlaneS0

open Classical in
/-- The family's weight: `μ(𝔞)·(u/𝔞)₆` on ideals of norm prime to `6`. -/
noncomputable def wsym (u : 𝓞 K) (I : Ideal (𝓞 K)) : ℂ :=
  if (absNorm I).Coprime 6 then (moebius I : ℂ) * sym6 u I else 0

/-- **The family** `A_Z(u) = Σ_𝔞 μ(𝔞)(u/𝔞)₆ W(N𝔞/Z)` over the ideals `𝔞` of norm prime to `6`. -/
noncomputable def famSum (W : ℝ → ℝ) (Z : ℝ) (u : 𝓞 K) : ℂ :=
  ∑' n : ℕ, normSum (wsym u) n * (W (n / Z) : ℂ)

/-- A generator of a (principal) ideal. -/
noncomputable def gen (J : Ideal (𝓞 K)) : 𝓞 K := Submodule.IsPrincipal.generator J

theorem span_gen (J : Ideal (𝓞 K)) : span {gen J} = J := Ideal.span_singleton_generator J

theorem gen_mem_iff {J P : Ideal (𝓞 K)} : gen J ∈ P ↔ P ∣ J := by
  rw [Ideal.dvd_iff_le, ← Ideal.span_singleton_le_iff_mem, span_gen]

theorem normSum_wsym_zero (u : 𝓞 K) : normSum (wsym u) 0 = 0 := by
  classical
  have : ofNorm 0 = {(⊥ : Ideal (𝓞 K))} := by
    ext I; simp [mem_ofNorm, Ideal.absNorm_eq_zero_iff]
  rw [normSum, this, Finset.sum_singleton, wsym, ite_eq_right]
  rw [Ideal.absNorm_bot, Nat.coprime_zero_left]; norm_num

open Classical in
/-- Summing the family's weight at `𝔞` over the sixth powers of the generators of the ideals of norm
at most `Y` counts the ideals prime to `𝔞`. -/
theorem sum_wsym_gen (I : Ideal (𝓞 K)) (Y : ℝ) :
    ∑ J ∈ idealsLe Y, wsym (gen J ^ 6) I =
      if (absNorm I).Coprime 6 then (moebius I : ℂ) *
        (((idealsLe Y).filter fun J => ∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J).card : ℂ)
      else 0 := by
  unfold wsym
  split_ifs with hc
  · rw [← Finset.mul_sum, Finset.card_filter, Nat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [sym6_pow_six hc]
    have e : (∀ P ∈ normalizedFactors I, gen J ∉ P) ↔
        (∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J) := by
      simp only [Multiset.mem_toFinset, gen_mem_iff]
    by_cases h : ∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J
    · rw [ite_eq_left (e.2 h), ite_eq_left h]; simp
    · rw [ite_eq_right (fun h' => h (e.1 h')), ite_eq_right h]; simp
  · simp

open Classical in
/-- **The average of the family over sixth powers**, as a finite sum. -/
theorem sum_famSum_gen {W : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R < x → W x = 0) {Z : ℝ} (hZ : 0 < Z)
    {M : ℕ} (hM : R * Z ≤ M) (Y : ℝ) :
    ∑ J ∈ idealsLe Y, famSum W Z (gen J ^ 6) =
      ∑ n ∈ Finset.Ioc 0 M, (W (n / Z) : ℂ) * ∑ I ∈ ofNorm n,
        (if (absNorm I).Coprime 6 then (moebius I : ℂ) *
          (((idealsLe Y).filter fun J => ∀ P ∈ (normalizedFactors I).toFinset, ¬ P ∣ J).card : ℂ)
        else 0) := by
  simp only [famSum]
  rw [Finset.sum_congr rfl fun J _ => tsum_eq_Ioc (normSum_wsym_zero (gen J ^ 6)) hR hZ hM,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  simp only [normSum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun I _ => sum_wsym_gen I Y

theorem norm_w2_eq (I : Ideal (𝓞 K)) : w2 I = ((‖w2 I‖ : ℝ) : ℂ) := by
  classical
  unfold w2
  split_ifs
  · rw [norm_pow, Complex.norm_ofNat]; push_cast; rfl
  · simp

theorem norm_normSum_w2 (n : ℕ) : ‖normSum w2 n‖ = ∑ I ∈ ofNorm n, ‖w2 I‖ := by
  rw [normSum, Finset.sum_congr rfl fun I _ => norm_w2_eq I, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun I _ => norm_nonneg _)]

/-- `|μ(𝔞)|·2^{ω(𝔞)} ≤ |w₂(𝔞)|`. -/
theorem abs_moebius_mul_two_pow_le (I : Ideal (𝓞 K)) :
    |(moebius I : ℝ)| * 2 ^ (normalizedFactors I).toFinset.card ≤ ‖w2 I‖ := by
  classical
  by_cases hI : Squarefree I
  · have hI0 : I ≠ 0 := hI.ne_zero
    have hnd := (squarefree_iff_nodup_normalizedFactors hI0).1 hI
    rw [hI.moebius_eq, w2, ite_eq_left hI, Multiset.toFinset_card_of_nodup hnd, norm_pow,
      Complex.norm_ofNat]
    simp
  · rw [moebius_of_not_squarefree hI]; simp

open Classical in
/-- **The averaged identity with its error**: for `W` vanishing beyond `R`, bounded by `B`, and
`RZ ≤ M`, `|Σ_{N𝔟≤Y} A_Z(𝔟⁶) − κY·Σ_n f(n)W(n/Z)| ≤ B(5√Y + κ)·Σ_{n≤M} Σ_{N𝔞=n} 2^{ω(𝔞)}`. -/
theorem norm_sum_famSum_sub_le {W : ℝ → ℝ} {R B : ℝ} (hR : ∀ x, R < x → W x = 0)
    (hB : ∀ x, |W x| ≤ B) {Z : ℝ} (hZ : 0 < Z) {M : ℕ} (hM : R * Z ≤ M) {Y : ℝ} (hY : 0 ≤ Y) :
    ‖∑ J ∈ idealsLe Y, famSum W Z (gen J ^ 6) - ((kappa * Y : ℝ) : ℂ) * fSmooth W Z‖ ≤
      B * (5 * √Y + kappa) * ∑ n ∈ Finset.Ioc 0 M, ‖normSum w2 n‖ := by
  have hk := kappa_pos
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  rw [sum_famSum_gen hR hZ hM Y, fSmooth, tsum_eq_Ioc normSum_wf_zero hR hZ hM, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [normSum, Finset.sum_mul, mul_comm (((kappa * Y : ℝ) : ℂ)), Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, norm_normSum_w2, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  -- one ideal `𝔞`
  set S := (normalizedFactors I).toFinset
  have hSmax : ∀ P ∈ S, P.IsMaximal := fun P hP => isMaximal_of_factor (Multiset.mem_toFinset.1 hP)
  have hcnt := abs_card_coprime_sub_le hSmax hY
  have hWn : ‖(W (n / Z) : ℂ)‖ ≤ B := by rw [Complex.norm_real]; exact hB _
  unfold wf tot
  set c : ℕ := ((idealsLe Y).filter fun J => ∀ P ∈ S, ¬ P ∣ J).card with hcdef
  set t : ℝ := ∏ P ∈ S, (1 - 1 / (absNorm P : ℝ)) with htdef
  have hct : |(c : ℝ) - kappa * Y * t| ≤ 2 ^ S.card * (5 * √Y + kappa) := hcnt
  by_cases hc : (absNorm I).Coprime 6
  · rw [ite_eq_left hc, ite_eq_left hc]
    calc _ = ‖(W (n / Z) : ℂ) * (moebius I : ℂ) * ((((c : ℝ) - kappa * Y * t : ℝ)) : ℂ)‖ := by
          congr 1; simp only [htdef, S]; push_cast; ring
      _ = ‖(W (n / Z) : ℂ)‖ * |(moebius I : ℝ)| * |(c : ℝ) - kappa * Y * t| := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, Complex.norm_intCast]
      _ ≤ B * |(moebius I : ℝ)| * (2 ^ S.card * (5 * √Y + kappa)) := by gcongr
      _ = B * (5 * √Y + kappa) * (|(moebius I : ℝ)| * 2 ^ S.card) := by ring
      _ ≤ B * (5 * √Y + kappa) * ‖w2 I‖ :=
          mul_le_mul_of_nonneg_left (abs_moebius_mul_two_pow_le I) (by positivity)
  · rw [ite_eq_right hc, ite_eq_right hc]
    simp only [mul_zero, zero_mul, sub_zero, norm_zero]
    positivity

end Family


/-! ### Cauchy–Schwarz against the mean square -/

section MeanSquare

open HalfPlaneS0 Filter Asymptotics

/-- **The S2′ hypothesis: the family's mean square at `σ`.** For every weight `W` and `ε > 0`, the
sum of `|A_Z(z)|²` over any finite set of nonzero `z` with `N(z) ≤ Z^{1+σ}` is `O(Z^{2+σ+ε})`. -/
def MeanSquare (σ : ℝ) : Prop :=
  ∀ W : ℝ → ℝ, Weight W → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Z : ℝ, 1 ≤ Z → ∀ T : Finset (𝓞 K),
    (∀ z ∈ T, z ≠ 0 ∧ (absNorm (span {z}) : ℝ) ≤ Z ^ (1 + σ)) →
      ∑ z ∈ T, ‖famSum W Z z‖ ^ 2 ≤ C * Z ^ (2 + σ + ε)

theorem gen_ne_zero {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) : gen J ≠ 0 := by
  intro h; apply hJ; rw [← span_gen J, h, Ideal.span_singleton_eq_bot]

theorem ne_bot_of_mem_idealsLe {Y : ℝ} {J : Ideal (𝓞 K)} (hJ : J ∈ idealsLe Y) : J ≠ ⊥ := by
  intro h; rw [mem_idealsLe, h, Ideal.absNorm_bot] at hJ; exact lt_irrefl 0 hJ.1

theorem span_gen_pow (J : Ideal (𝓞 K)) (k : ℕ) : span {gen J ^ k} = J ^ k := by
  rw [← Ideal.span_singleton_pow, span_gen]

/-- `𝔟 ↦ gen(𝔟)⁶` is injective on nonzero ideals. -/
theorem gen_pow_six_injOn (Y : ℝ) : Set.InjOn (fun J => gen J ^ 6) ↑(idealsLe Y) := by
  intro J hJ J' hJ' h
  have hJ0 := ne_bot_of_mem_idealsLe hJ
  have hJ0' := ne_bot_of_mem_idealsLe hJ'
  have h6 : J ^ 6 = J' ^ 6 := by
    rw [← span_gen_pow, ← span_gen_pow]; simp only at h; rw [h]
  have hnf : normalizedFactors J = normalizedFactors J' := by
    have := congrArg normalizedFactors h6
    rw [normalizedFactors_pow, normalizedFactors_pow] at this
    exact nsmul_right_injective (by norm_num : (6 : ℕ) ≠ 0) this
  rw [← Ideal.prod_normalizedFactors_eq_self hJ0, ← Ideal.prod_normalizedFactors_eq_self hJ0', hnf]

/-- The sixth powers of the generators of the ideals of norm at most `Y`. -/
noncomputable def sixthPowers (Y : ℝ) : Finset (𝓞 K) := by
  classical exact (idealsLe Y).image fun J => gen J ^ 6

theorem card_sixthPowers (Y : ℝ) : (sixthPowers Y).card = idealCount Y := by
  classical
  rw [sixthPowers, Finset.card_image_of_injOn (gen_pow_six_injOn Y), card_idealsLe]

theorem sum_sixthPowers (A : 𝓞 K → ℂ) (Y : ℝ) :
    ∑ z ∈ sixthPowers Y, A z = ∑ J ∈ idealsLe Y, A (gen J ^ 6) := by
  classical
  rw [sixthPowers, Finset.sum_image (gen_pow_six_injOn Y)]

theorem mem_sixthPowers_spec {Y : ℝ} (hY : 0 ≤ Y) {z : 𝓞 K} (hz : z ∈ sixthPowers Y) :
    z ≠ 0 ∧ (absNorm (span {z}) : ℝ) ≤ Y ^ 6 := by
  classical
  rw [sixthPowers, Finset.mem_image] at hz
  obtain ⟨J, hJ, rfl⟩ := hz
  have hJ0 := ne_bot_of_mem_idealsLe hJ
  refine ⟨pow_ne_zero _ (gen_ne_zero hJ0), ?_⟩
  rw [span_gen_pow, map_pow, Nat.cast_pow]
  have h := (mem_idealsLe.1 hJ).2
  have : (absNorm J : ℝ) ≤ Y := le_trans (by exact_mod_cast h) (Nat.floor_le hY)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 6

/-- Cauchy–Schwarz: `|Σ_{z∈T} A(z)|² ≤ |T|·Σ_{z∈T} |A(z)|²`. -/
theorem norm_sum_sq_le (T : Finset (𝓞 K)) (A : 𝓞 K → ℂ) :
    ‖∑ z ∈ T, A z‖ ^ 2 ≤ T.card * ∑ z ∈ T, ‖A z‖ ^ 2 := by
  calc ‖∑ z ∈ T, A z‖ ^ 2 ≤ (∑ z ∈ T, ‖A z‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ T.card * ∑ z ∈ T, ‖A z‖ ^ 2 := sq_sum_le_card_mul_sum_sq


/-- Taking square roots: `x² ≤ c s² C Z^e` gives `x ≤ √(cC)·s·Z^{e/2}`. -/
theorem le_of_sq_le_aux {x c C s Z e : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hZ : 0 < Z) (h : x ^ 2 ≤ c * s ^ 2 * (C * Z ^ e)) : x ≤ √(c * C) * s * Z ^ (e / 2) := by
  have hR : (√(c * C) * s * Z ^ (e / 2)) ^ 2 = c * s ^ 2 * (C * Z ^ e) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hc hC), ← Real.rpow_natCast (Z ^ (e / 2)),
      ← Real.rpow_mul hZ.le]
    norm_num; ring
  refine (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 ?_
  rw [hR]; exact h

/-- The last division: `κs²F ≤ A₁s·s u + A₂s·s v` with `u, v ≤ w` gives `F ≤ (A₁ + A₂)/κ·w`. -/
theorem le_of_mul_le_aux {κ s A1 A2 F u v w : ℝ} (hk : 0 < κ) (hs : 0 < s) (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) (hu : u ≤ w) (hv : v ≤ w)
    (h : κ * s ^ 2 * F ≤ A1 * s * (s * u) + A2 * s * (s * v)) : F ≤ (A1 + A2) / κ * w := by
  have hs2 : 0 < s ^ 2 := by positivity
  have h1 : κ * F * s ^ 2 ≤ ((A1 + A2) * w) * s ^ 2 := by
    have : A1 * s * (s * u) + A2 * s * (s * v) ≤ ((A1 + A2) * w) * s ^ 2 := by
      have e : A1 * s * (s * u) + A2 * s * (s * v) = (A1 * u + A2 * v) * s ^ 2 := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ hs2.le
      nlinarith
    linarith [show κ * s ^ 2 * F = κ * F * s ^ 2 by ring]
  have h2 : κ * F ≤ (A1 + A2) * w := le_of_mul_le_mul_right h1 hs2
  rw [div_mul_eq_mul_div, le_div_iff₀ hk]; linarith

/-- The error of the average, in powers of `Z`. -/
theorem err_bound_aux {B κ C2 R ε Z s Y E : ℝ} {M : ℕ} (hB : 0 ≤ B) (hk : 0 < κ) (hC2 : 0 ≤ C2)
    (hR : 0 ≤ R) (hε : 0 < ε) (hZ : 0 < Z) (hs1 : 1 ≤ s) (hsY : √Y = s)
    (hM : (M : ℝ) ≤ (R + 1) * Z) (hE : E ≤ C2 * (M : ℝ) ^ (1 + ε)) :
    B * (5 * √Y + κ) * E ≤ B * (5 + κ) * C2 * (R + 1) ^ (1 + ε) * s * Z ^ (1 + ε) := by
  have h1 : 5 * √Y + κ ≤ (5 + κ) * s := by rw [hsY]; nlinarith
  have h2 : E ≤ C2 * ((R + 1) ^ (1 + ε) * Z ^ (1 + ε)) := by
    rw [← Real.mul_rpow (by linarith) hZ.le]
    exact hE.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hM (by linarith)) hC2)
  have hE0 : 0 ≤ C2 * ((R + 1) ^ (1 + ε) * Z ^ (1 + ε)) := by positivity
  calc B * (5 * √Y + κ) * E ≤ B * ((5 + κ) * s) * (C2 * ((R + 1) ^ (1 + ε) * Z ^ (1 + ε))) := by
        have h0 : 0 ≤ 5 * √Y + κ := by positivity
        rcases le_or_gt 0 E with hE0' | hE0'
        · exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hB) h2 hE0' (by positivity)
        · have hneg : B * (5 * √Y + κ) * E ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hB h0) hE0'.le
          have hpos : 0 ≤ B * ((5 + κ) * s) * (C2 * ((R + 1) ^ (1 + ε) * Z ^ (1 + ε))) := by
            have : 0 ≤ s := by linarith
            positivity
          linarith
    _ = _ := by ring

/-- **S2′: the family's mean square gives the totient-weighted bound.** If `MeanSquare σ` holds with
`σ ≥ 0`, then `Σ_n f(n)W(n/Z) = O(Z^{(11+5σ)/12+ε})` for every weight `W` and `ε > 0`. The average is
taken over `𝔟⁶`, `N𝔟 ≤ Y = Z^{(1+σ)/6}`; Cauchy–Schwarz and the mean square bound it by
`√Y·Z^{1+σ/2+ε/2}`, and the error of the average is `O(√Y·Z^{1+ε})`. -/
theorem weightedBound_of_meanSquare {σ : ℝ} (hσ : 0 ≤ σ) (h : MeanSquare σ) :
    WeightedBound ((11 + 5 * σ) / 12) := by
  intro W hW ε hε
  obtain ⟨R, hR0, hR⟩ := hW.exists_vanish_right
  obtain ⟨B, hB⟩ := hW.compact.exists_bound_of_continuous hW.continuous
  have hB' : ∀ x, |W x| ≤ B := fun x => by have := hB x; rwa [Real.norm_eq_abs] at this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB' 0)
  obtain ⟨Cms, hCms⟩ := h W hW ε hε
  obtain ⟨C2, hC20, hC2⟩ := sum_w2_le hε
  have hk := kappa_pos
  set C1 : ℝ := max Cms 0 with hC1
  have hC10 : 0 ≤ C1 := le_max_right _ _
  set A1 : ℝ := √((2 * kappa + 5) * C1) with hA1
  set A2 : ℝ := B * (5 + kappa) * C2 * (R + 1) ^ (1 + ε) with hA2
  have hA10 : 0 ≤ A1 := Real.sqrt_nonneg _
  have hA20 : 0 ≤ A2 := by positivity
  refine IsBigO.of_bound ((A1 + A2) / kappa) ?_
  filter_upwards [eventually_ge_atTop 1] with Z hZ
  have hZ0 : 0 < Z := by linarith
  set s : ℝ := Z ^ ((1 + σ) / 12) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hZ (by linarith)
  have hs0 : 0 < s := by linarith
  set Y : ℝ := s ^ 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hsqrtY : √Y = s := Real.sqrt_sq hs0.le
  have hY6 : Y ^ 6 = Z ^ (1 + σ) := by
    rw [hY, ← pow_mul, hs, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    congr 1; push_cast; ring
  set M : ℕ := ⌈R * Z⌉₊ with hMdef
  have hM : R * Z ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ (R + 1) * Z := by
    have := Nat.ceil_lt_add_one (mul_nonneg hR0 hZ0.le)
    nlinarith
  -- the error of the average
  have herr := (norm_sum_famSum_sub_le hR hB' hZ0 hM hY0).trans
    (err_bound_aux hB0 hk hC20 hR0 hε hZ0 hs1 hsqrtY hM2 (hC2 M))
  -- the main sum, by Cauchy–Schwarz and the mean square
  have hT : ∀ z ∈ sixthPowers Y, z ≠ 0 ∧ (absNorm (span {z}) : ℝ) ≤ Z ^ (1 + σ) := fun z hz => by
    obtain ⟨h1, h2⟩ := mem_sixthPowers_spec hY0 hz
    exact ⟨h1, hY6 ▸ h2⟩
  have hms := hCms Z hZ (sixthPowers Y) hT
  have hcs := norm_sum_sq_le (sixthPowers Y) (famSum W Z)
  rw [sum_sixthPowers (famSum W Z) Y, card_sixthPowers] at hcs
  have hcount : (idealCount Y : ℝ) ≤ (2 * kappa + 5) * Y := by
    have := abs_idealCount_sub_le hY0
    have hsq : √Y ≤ Y := by rw [hsqrtY, hY]; nlinarith
    rw [abs_le] at this; nlinarith
  have hsum0 : 0 ≤ ∑ z ∈ sixthPowers Y, ‖famSum W Z z‖ ^ 2 :=
    Finset.sum_nonneg fun z _ => by positivity
  have hsq : ‖∑ J ∈ idealsLe Y, famSum W Z (gen J ^ 6)‖ ^ 2 ≤
      (2 * kappa + 5) * s ^ 2 * (C1 * Z ^ (2 + σ + ε)) :=
    hcs.trans (mul_le_mul hcount (hms.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity))) hsum0 (by positivity))
  have hmain := le_of_sq_le_aux (norm_nonneg _) (by positivity) hC10 hs0.le hZ0 hsq
  -- combine
  have hcomb : kappa * Y * ‖fSmooth W Z‖ ≤
      A1 * s * Z ^ ((2 + σ + ε) / 2) + A2 * s * Z ^ (1 + ε) := by
    have e : kappa * Y * ‖fSmooth W Z‖ = ‖((kappa * Y : ℝ) : ℂ) * fSmooth W Z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [e]
    have htri := norm_sub_le (∑ J ∈ idealsLe Y, famSum W Z (gen J ^ 6))
      (∑ J ∈ idealsLe Y, famSum W Z (gen J ^ 6) - ((kappa * Y : ℝ) : ℂ) * fSmooth W Z)
    rw [sub_sub_cancel] at htri
    exact htri.trans (add_le_add hmain herr)
  -- divide by `κY = κs²`, and compare exponents
  have hE1 : Z ^ ((2 + σ + ε) / 2) = s * Z ^ ((11 + 5 * σ) / 12 + ε / 2) := by
    rw [hs, ← Real.rpow_add hZ0]; congr 1; ring
  have hE2 : Z ^ (1 + ε) = s * Z ^ (1 + ε - (1 + σ) / 12) := by
    rw [hs, ← Real.rpow_add hZ0]; congr 1; ring
  rw [hE1, hE2, hY] at hcomb
  rw [Real.norm_of_nonneg (by positivity)]
  exact le_of_mul_le_aux hk hs0 hA10 hA20
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hcomb

/-- **The conditional milestone: the family's mean square at `σ ≥ 0` gives
`ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > (11 + 5σ)/12`.** Through S2′, S0′ and S0. At the release's
`σ = 1/10` this is `Re s > 23/24`. -/
theorem ne_zero_of_meanSquare {σ : ℝ} (hσ : 0 ≤ σ) (h : MeanSquare σ) {s : ℂ}
    (hs : (11 + 5 * σ) / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_smoothBound
    (smoothBound_of_weightedBound (by positivity) (weightedBound_of_meanSquare hσ h)) hs

end MeanSquare

end Eis

#print axioms Eis.six_not_mem_of_factor
#print axioms Eis.chiP_pow_six
#print axioms Eis.sym6_pow_six
#print axioms Eis.prod_dvd_iff
#print axioms Eis.indicator_coprime
#print axioms Eis.card_coprime
#print axioms Eis.sum_powerset_inv
#print axioms Eis.abs_card_coprime_sub_le
#print axioms Eis.w2_mul
#print axioms Eis.norm_normSum_w2_le
#print axioms Eis.summable_w2
#print axioms Eis.sum_w2_le
#print axioms Eis.sum_wsym_gen
#print axioms Eis.sum_famSum_gen
#print axioms Eis.norm_sum_famSum_sub_le
#print axioms Eis.gen_pow_six_injOn
#print axioms Eis.mem_sixthPowers_spec
#print axioms Eis.norm_sum_sq_le
#print axioms Eis.weightedBound_of_meanSquare
#print axioms Eis.ne_zero_of_meanSquare
