import EisensteinThetaMeanSquare

/-! # Lemma 6.6 from the displayed transformation and the quadratic large sieve (round 342)

S5d of round 312's plan, part 4: the assembly in the companion paper's proof of its Lemma 6.6, and with
round 339 the zero-free half-plane `Re s > 11/12` from the two displayed inputs.

* **The split of a squarefree row** (`exists_row_split`): `s = u·gen(𝔱)·k₀` with `u` a unit, `𝔱` the
  product of the primes of `s` dividing `6g`, and `k₀` primary, squarefree, of norm prime to `6` and prime
  to `gen(𝔱)·g`, with `N(s) = N(𝔱)N(k₀)`. The ideal `𝔱` is a product of a subset of the primes of `(6)`
  and of `g` (`tIdeals`), so at most `6·2^{c₆+ω(g)}` keys `(u, 𝔱)` occur (`card_units_le`,
  `card_tIdeals_le`).
* **The rows with one `t`** (`rows_meanSquare`): the displayed transformation (`ThetaRows`) writes each
  row's completed sum as `Σ_{i,𝒜} C·dualTerm`. Cauchy–Schwarz over `(i, 𝒜)`, the classes `k₀ mod M` (at
  most `N((M))` of them, `card_image_mk_le`), round 341's `dualTerm_meanSquare` and `cost_le` bound the
  mean square by `K₁64^{ω(tg)}N²·H₀^σ max(1, K_c²N(rad tg)²H₀²/X)^{2σ}(H₀ + K_c²(H₀²/X)N(t)²N(g))`.
* **`squarefreeCompleted_of`**: `ThetaRows → QuadLargeSieve → SquarefreeCompleted`, the paper's Lemma 6.6,
  with `H₀ = 𝓗/N(t)`, `σ = min(1/2, ε/(26C₀))` and the divisor bound of round 310's `four_pow_card_le`
  at `δ = ε/(14C₀)`, so that `D^{7C₀δ + 13C₀σ} ≤ D^ε`.
* **`ne_zero_of_theta`**: `ThetaRows → QuadLargeSieve → 11/12 < Re s → ζ(s) ≠ 0 ∧ L(s, χ₋₃) ≠ 0`, through
  round 339's `ne_zero_of_squarefree`.
-/

open Complex MeasureTheory Set NumberField Ideal UniqueFactorizationMonoid
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section

namespace Eis

/-- The completed sum of the zero weight vanishes. -/
theorem compT_eq_zero_of_zero (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) {W : ℝ → ℂ}
    (hW : ∀ x, W x = 0) (X : ℝ) : compT ξ k f W X = 0 := by
  unfold compT Vstar
  simp [hW]

theorem idl_primeSet_dvd (I : Ideal (𝓞 K)) : idl (primeSet I) ∣ I :=
  (prod_Pr_dvd_iff _ I).2 fun _ hP => dvd_of_mem_normalizedFactors (mem_primeSet.1 hP)

/-- `N(∏_{P ∣ I, P ∤ 6} P) ≤ N(I)`. -/
theorem nI_primeSet_le {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : nI (primeSet I) ≤ absNorm I := by
  have h0 : absNorm I ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0)
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd (idl_primeSet_dvd I)))
  rw [nI_eq_absNorm]; exact_mod_cast this

open Classical in
/-- The primes of `(6)` together with those of `g` prime to `6`. -/
def primesU (g : 𝓞 K) : Finset (Ideal (𝓞 K)) :=
  (normalizedFactors (span {(6 : 𝓞 K)})).toFinset ∪ (primeSet (span {g})).image Subtype.val

open Classical in
/-- The candidate ideals `(t)`: the products of the subsets of `primesU g`. -/
def tIdeals (g : 𝓞 K) : Finset (Ideal (𝓞 K)) := (primesU g).powerset.image fun F => ∏ P ∈ F, P

/-- The number of primes of `(6)`. -/
def c6 : ℕ := (normalizedFactors (span {(6 : 𝓞 K)})).toFinset.card

theorem card_tIdeals_le (g : 𝓞 K) : (tIdeals g).card ≤ 2 ^ (c6 + (primeSet (span {g})).card) := by
  classical
  unfold tIdeals
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_powerset]
  refine Nat.pow_le_pow_right (by norm_num) ((Finset.card_union_le _ _).trans ?_)
  unfold c6
  exact Nat.add_le_add_left Finset.card_image_le _

/-- A prime ideal dividing a nonzero ideal is one of its factors. -/
theorem mem_nf_of_dvd {I Q : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hQ : Prime Q) (h : Q ∣ I) :
    Q ∈ normalizedFactors I := by
  obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hI hQ.irreducible h
  rwa [associated_iff_eq.1 hassoc]

/-- A maximal ideal `P ≠ ⊥` not containing `J` is coprime to it. -/
theorem isCoprime_of_not_le {P J : Ideal (𝓞 K)} (hP : P.IsMaximal) (hJ : ¬ J ≤ P) :
    IsCoprime P J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  exact hP.out.2 _ (lt_of_le_of_ne le_sup_left fun h => hJ (h ▸ le_sup_right))

open Classical in
/-- **The split of a squarefree row**: `s = u·gen(𝔱)·k₀` with `u` a unit, `𝔱` squarefree among the
candidate ideals of `g`, and `k₀` primary, squarefree, of norm prime to `6` and prime to `gen(𝔱)·g`, and
`N(s) = N(𝔱)N(k₀)`. -/
theorem exists_row_split {s g : 𝓞 K} (hs : s ≠ 0) (hsq : Squarefree (span {s})) (hg : g ≠ 0) :
    ∃ (u : (𝓞 K)ˣ) (T : Ideal (𝓞 K)) (k₀ : 𝓞 K), s = u * gen T * k₀ ∧ T ∈ tIdeals g ∧
      T ≠ ⊥ ∧ Squarefree T ∧ Primary k₀ ∧ Squarefree (span {k₀}) ∧
      (absNorm (span {k₀})).Coprime 6 ∧ IsCoprime k₀ (gen T * g) ∧
      absNorm (span {s}) = absNorm T * absNorm (span {k₀}) := by
  have hS0 : span {s} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hG0 : span {g} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  set R : Finset Pr := (primeSet (span {s})).filter fun P => ¬ P.1 ∣ span {g} with hR
  obtain ⟨hprim, hspan⟩ := pgen_spec6 (idl_coprime6 R)
  set k₀ := pgen (idl R) with hk₀
  have hRdvd : idl R ∣ span {s} :=
    (prod_Pr_dvd_iff R _).2 fun P hP =>
      dvd_of_mem_normalizedFactors (mem_primeSet.1 (Finset.mem_filter.1 hP).1)
  obtain ⟨T, hT⟩ := hRdvd
  have hk0dvd : k₀ ∣ s := by
    rw [← Ideal.span_singleton_dvd_span_singleton_iff_dvd, hspan, hT]
    exact dvd_mul_right _ _
  obtain ⟨t', ht'⟩ := hk0dvd
  have hR0 : idl R ≠ 0 := idl_ne_bot R
  have hspanT : span {t'} = T := by
    have h1 : span {s} = idl R * span {t'} := by
      rw [ht', ← Ideal.span_singleton_mul_span_singleton, hspan]
    exact mul_left_cancel₀ hR0 (h1.symm.trans hT)
  have hassoc : Associated t' (gen T) := by
    rw [← Ideal.span_singleton_eq_span_singleton, hspanT, span_gen]
  obtain ⟨v, hv⟩ := hassoc
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    rw [mul_bot] at hT
    exact hS0 hT
  have hTsq : Squarefree T := hsq.squarefree_of_dvd ⟨idl R, by rw [hT, mul_comm]⟩
  refine ⟨v⁻¹, T, k₀, ?_, ?_, hT0, hTsq, hprim, ?_, ?_, ?_, ?_⟩
  · -- s = v⁻¹ * gen T * k₀
    rw [ht', ← hv]
    have : ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc k₀ * t' = (((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K)) * t' * k₀ := by rw [this]; ring
      _ = _ := by ring
  · -- T ∈ tIdeals g
    unfold tIdeals
    rw [Finset.mem_image]
    refine ⟨(normalizedFactors T).toFinset, Finset.mem_powerset.2 fun Q hQ => ?_, ?_⟩
    · rw [Multiset.mem_toFinset] at hQ
      have hQprime := prime_of_normalized_factor Q hQ
      have hQmax := isMaximal_of_mem_nf hQ
      unfold primesU
      rw [Finset.mem_union]
      by_cases h6 : (6 : 𝓞 K) ∈ Q
      · left
        rw [Multiset.mem_toFinset]
        refine mem_nf_of_dvd (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num) hQprime ?_
        rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact h6
      · right
        rw [Finset.mem_image]
        refine ⟨⟨Q, hQmax, h6⟩, ?_, rfl⟩
        rw [mem_primeSet]
        have hQs : Q ∣ span {s} := by
          rw [hT]; exact dvd_mul_of_dvd_right (dvd_of_mem_normalizedFactors hQ) _
        have hQR : (⟨Q, hQmax, h6⟩ : Pr) ∉ R := by
          intro hmem
          have h1 : Q ∣ idl R := (dvd_idl_iff ⟨Q, hQmax, h6⟩ R).2 hmem
          have h2 : Q ∣ T := dvd_of_mem_normalizedFactors hQ
          have h3 : Q * Q ∣ span {s} := by rw [hT]; exact mul_dvd_mul h1 h2
          exact hQprime.not_isUnit (hsq Q h3)
        have hQg : Q ∣ span {g} := by
          by_contra hng
          apply hQR
          rw [hR, Finset.mem_filter, mem_primeSet]
          exact ⟨mem_nf_of_dvd hS0 hQprime hQs, hng⟩
        exact mem_nf_of_dvd hG0 hQprime hQg
    · have hnd := (squarefree_iff_nodup_normalizedFactors hT0).1 hTsq
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup, Multiset.map_id',
        Ideal.prod_normalizedFactors_eq_self hT0]
  · rw [hspan]; exact idl_squarefree R
  · rw [hspan]; exact idl_coprime6 R
  · -- coprimality
    rw [← Ideal.isCoprime_span_singleton_iff, hspan, ← Ideal.span_singleton_mul_span_singleton,
      span_gen]
    unfold idl
    refine IsCoprime.prod_left fun P hP => isCoprime_of_not_le P.2.1 fun hle => ?_
    have hdvd : P.1 ∣ T * span {g} := Ideal.dvd_iff_le.2 hle
    rcases (prime_Pr P).dvd_or_dvd hdvd with h | h
    · have h1 : P.1 ∣ idl R := (dvd_idl_iff P R).2 hP
      have h3 : P.1 * P.1 ∣ span {s} := by rw [hT]; exact mul_dvd_mul h1 h
      exact (prime_Pr P).not_isUnit (hsq _ h3)
    · exact (Finset.mem_filter.1 hP).2 h
  · rw [hT, map_mul, hspan, mul_comm]

open Classical in
/-- At most `N((M))` residue classes modulo `M` meet a finite set. -/
theorem card_image_mk_le {M : 𝓞 K} (hM : M ≠ 0) (Ks : Finset (𝓞 K)) :
    ((Ks.image (Ideal.Quotient.mk (span {M}))).card : ℝ) ≤ absNorm (span {M}) := by
  have : Finite (𝓞 K ⧸ span {M}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {M}) := Fintype.ofFinite _
  have h1 := Finset.card_le_univ (Ks.image (Ideal.Quotient.mk (span {M})))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact_mod_cast h1

theorem card_admissible_le (t g : 𝓞 K) :
    (admissible t g).card ≤ 2 ^ (primeSet (span {t * g})).card := by
  unfold admissible
  exact (Finset.card_filter_le _ _).trans (Finset.card_powerset _).le

theorem subset_of_mem_admissible {t g : 𝓞 K} {A : Finset Pr} (hA : A ∈ admissible t g) :
    A ⊆ primeSet (span {t * g}) :=
  Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1

/-- `‖Σ_x C_x D_x‖² ≤ |X|·Σ_x ‖D_x‖²` for `|C_x| ≤ 1`. -/
theorem norm_sum_mul_sq_le_card {ι : Type*} (s : Finset ι) (C D : ι → ℂ) (hC : ∀ x, ‖C x‖ ≤ 1) :
    ‖∑ x ∈ s, C x * D x‖ ^ 2 ≤ s.card * ∑ x ∈ s, ‖D x‖ ^ 2 := by
  refine (norm_sum_sq_le_card s _).trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun x _ => ?_) (Nat.cast_nonneg _))
  rw [norm_mul, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hC x))

/-- One class of data bounded uniformly in the class (the bound of `dualTerm_meanSquare` with
`N(c₀) ≤ K_c`, `𝒜 ⊆ primeSet(tg)` and `cost_le`). -/
theorem class_bound_le {Kσ Kd Nw σ H₀ X Kc : ℝ} (hKσ : 0 ≤ Kσ) (hσ : 0 ≤ σ) (hH : 1 ≤ H₀)
    (hX : 0 < X) {c₀ t g : 𝓞 K} (hc : (absNorm (span {c₀}) : ℝ) ≤ Kc) (ht : t ≠ 0) (hg : g ≠ 0)
    (htsq : Squarefree (span {t})) {A : Finset Pr} (hA : A ∈ admissible t g) (j : Pr → ℕ)
    (hj : j = jFix t g) :
    Kσ * (16 : ℝ) ^ A.card * Kd ^ 2 * Nw ^ 2 * (H₀ ^ σ * max 1 (dualY c₀ A H₀ X) ^ (2 * σ)) *
        (H₀ + (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
          ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (j P)) ≤
      Kσ * (16 : ℝ) ^ (primeSet (span {t * g})).card * Kd ^ 2 * Nw ^ 2 *
        (H₀ ^ σ * max 1 (Kc ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^ (2 * σ)) *
        (H₀ + Kc ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g}))) := by
  subst hj
  have hH0 : 0 < H₀ := by linarith
  have hc0 : 0 ≤ (absNorm (span {c₀}) : ℝ) := Nat.cast_nonneg _
  have hAsub := subset_of_mem_admissible hA
  have h16 : (16 : ℝ) ^ A.card ≤ 16 ^ (primeSet (span {t * g})).card :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hAsub)
  have hnI : nI A ≤ nI (primeSet (span {t * g})) := by
    unfold nI; exact_mod_cast absNorm_idl_mono hAsub
  have hY : dualY c₀ A H₀ X ≤ Kc ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X := by
    unfold dualY
    have h1 : (absNorm (span {c₀}) : ℝ) ^ 2 ≤ Kc ^ 2 := pow_le_pow_left₀ hc0 hc 2
    have h2 : nI A ^ 2 ≤ nI (primeSet (span {t * g})) ^ 2 :=
      pow_le_pow_left₀ (nI_pos A).le hnI 2
    gcongr
  have hmax : max 1 (dualY c₀ A H₀ X) ^ (2 * σ) ≤
      max 1 (Kc ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^ (2 * σ) :=
    Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) (max_le_max le_rfl hY) (by linarith)
  have hcost := cost_le ht hg htsq hA
  have hP0 : 0 ≤ ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (jFix t g P) :=
    Finset.prod_nonneg fun P _ => pow_nonneg (Nat.cast_nonneg _) _
  have hlast : H₀ + (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
        ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (jFix t g P) ≤
      H₀ + Kc ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g})) := by
    have h1 : (absNorm (span {c₀}) : ℝ) ^ 2 ≤ Kc ^ 2 := pow_le_pow_left₀ hc0 hc 2
    have hHX : 0 ≤ H₀ ^ 2 / X := div_nonneg (sq_nonneg _) hX.le
    have := mul_le_mul (mul_le_mul_of_nonneg_right h1 hHX) hcost hP0
      (mul_nonneg (le_trans (sq_nonneg _) h1) hHX)
    linarith
  have hM0 : 0 ≤ H₀ ^ σ := Real.rpow_nonneg hH0.le _
  have hm0 : 0 ≤ max 1 (dualY c₀ A H₀ X) ^ (2 * σ) :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have hL0 : 0 ≤ H₀ + (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
      ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (jFix t g P) := by
    have : 0 ≤ (absNorm (span {c₀}) : ℝ) ^ 2 * (H₀ ^ 2 / X) *
        ∏ P ∈ A, (absNorm P.1 : ℝ) ^ jCost (jFix t g P) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hX.le)) hP0
    linarith
  have hK0 : 0 ≤ Kσ * (16 : ℝ) ^ A.card * Kd ^ 2 * Nw ^ 2 := by positivity
  have hX2 : 0 ≤ H₀ ^ σ * max 1 (Kc ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^ (2 * σ) :=
    mul_nonneg hM0 (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hL2 : 0 ≤ H₀ + Kc ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g})) :=
    le_trans hL0 hlast
  have step1 := mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax hM0) hK0) hlast
    hL0 (mul_nonneg hK0 hX2)
  have step2 : Kσ * (16 : ℝ) ^ A.card * Kd ^ 2 * Nw ^ 2 *
        (H₀ ^ σ * max 1 (Kc ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^ (2 * σ)) *
        (H₀ + Kc ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g}))) ≤
      Kσ * (16 : ℝ) ^ (primeSet (span {t * g})).card * Kd ^ 2 * Nw ^ 2 *
        (H₀ ^ σ * max 1 (Kc ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^ (2 * σ)) *
        (H₀ + Kc ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g}))) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h16 hKσ) (sq_nonneg _)) (sq_nonneg _))
      hX2) hL2
  exact step1.trans step2

theorem sixtyfour_pow (n : ℕ) : (64 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 * 16 ^ n := by
  rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]; norm_num

open Classical in
/-- **The rows with one `t`** (the companion paper's proof of Lemma 6.6, for fixed `t`): from the
displayed transformation and the quadratic large sieve,
`Σ_{k₀} |T(X; u₀tk₀, g)|² ≤ K₁ 64^{ω(tg)}N²·H₀^σ max(1, K_c²N(rad tg)²H₀²/X)^{2σ}·(H₀ + K_c²(H₀²/X)N(t)²N(g))`
over the rows `k₀` primary, squarefree, of norm prime to `6`, prime to `tg`, with `N(k₀) ≤ H₀`. -/
theorem rows_meanSquare (hθ : ThetaRows) (hLS : QuadLargeSieve) {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / 2) :
    ∃ J : ℕ, ∀ α β : ℝ, 0 < α → α ≤ β → ∃ K₁ Kc : ℝ, 0 ≤ K₁ ∧ 0 ≤ Kc ∧
    ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (W : ℝ → ℂ), ContDiff ℝ ∞ W →
      (∀ y, y < α ∨ β < y → W y = 0) → ∀ N : ℝ, (∀ i ≤ J, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
      ∀ (u₀ : (𝓞 K)ˣ) (t g : 𝓞 K), t ≠ 0 → g ≠ 0 → Squarefree (span {t}) →
      ∀ (H₀ X : ℝ), 1 ≤ H₀ → 0 < X →
      ∀ Ks : Finset (𝓞 K), (∀ k₀ ∈ Ks, Primary k₀ ∧ Squarefree (span {k₀}) ∧
        (absNorm (span {k₀})).Coprime 6 ∧ IsCoprime k₀ (t * g) ∧ (absNorm (span {k₀}) : ℝ) ≤ H₀) →
      ∑ k₀ ∈ Ks, ‖compT ξ (u₀ * t * k₀) g W X‖ ^ 2 ≤
        K₁ * (64 : ℝ) ^ (primeSet (span {t * g})).card * N ^ 2 *
          (H₀ ^ σ * max 1 (Kc ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^ (2 * σ)) *
          (H₀ + Kc ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g}))) := by
  obtain ⟨J₀, hJ⟩ := hθ
  obtain ⟨Kσ, hKσ0, hKσ⟩ := dualTerm_meanSquare hLS hσ hσ'
  refine ⟨J₀, fun α β hα hαβ => ?_⟩
  obtain ⟨Cw, M, KH, Kd, Kc₀, hM, hrest⟩ := hJ α β hα hαβ
  refine ⟨(KH : ℝ) ^ 2 * (absNorm (span {M}) : ℝ) * Kσ * max Kd 0 ^ 2 * Cw ^ 2, max Kc₀ 0,
    by positivity, le_max_right _ _, ?_⟩
  intro ξ W hW hsupp N hN u₀ t g ht hg htsq H₀ X hH hX Ks hKs
  obtain ⟨h, hhs, hhb, hrep⟩ := hrest W hW hsupp N hN
  obtain ⟨d, c₀, hc₀, hds, hdb, hT⟩ := hrep ξ u₀ t g ht hg htsq
  have hrows : ∀ k₀ ∈ Ks, ∃ C : ℕ → Finset Pr → ℂ, (∀ i A, ‖C i A‖ ≤ 1) ∧
      compT ξ (u₀ * t * k₀) g W X = ∑ i ∈ Finset.range KH, ∑ A ∈ admissible t g,
        C i A * dualTerm h (d (Ideal.Quotient.mk _ k₀) i A) (c₀ (Ideal.Quotient.mk _ k₀) i A) A
          (jFix t g) k₀ X := fun k₀ hk =>
    hT k₀ (hKs k₀ hk).1 (hKs k₀ hk).2.1 (hKs k₀ hk).2.2.1 (hKs k₀ hk).2.2.2.1 X hX
  choose! C hC hCeq using hrows
  -- Cauchy–Schwarz over the transformed terms, for each row
  have hrow : ∀ k₀ ∈ Ks, ‖compT ξ (u₀ * t * k₀) g W X‖ ^ 2 ≤
      ((Finset.range KH ×ˢ admissible t g).card : ℝ) * ∑ x ∈ Finset.range KH ×ˢ admissible t g,
        ‖dualTerm h (d (Ideal.Quotient.mk _ k₀) x.1 x.2) (c₀ (Ideal.Quotient.mk _ k₀) x.1 x.2) x.2
          (jFix t g) k₀ X‖ ^ 2 := by
    intro k₀ hk
    rw [hCeq k₀ hk, ← Finset.sum_product']
    exact norm_sum_mul_sq_le_card (Finset.range KH ×ˢ admissible t g) (fun x => C k₀ x.1 x.2)
      (fun x => dualTerm h (d (Ideal.Quotient.mk _ k₀) x.1 x.2) (c₀ (Ideal.Quotient.mk _ k₀) x.1 x.2)
        x.2 (jFix t g) k₀ X) fun x => hC k₀ hk x.1 x.2
  -- the bound of one class
  have hKd : 0 ≤ max Kd 0 := le_max_right _ _
  have hdb' : ∀ ρ i A (q : DualIdx), ‖d ρ i A q‖ ≤
      max Kd 0 * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2) := fun ρ i A q =>
    (hdb ρ i A q).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _)) (Real.sqrt_nonneg _))
  set B : ℝ := Kσ * (16 : ℝ) ^ (primeSet (span {t * g})).card * max Kd 0 ^ 2 * (Cw * N) ^ 2 *
      (H₀ ^ σ * max 1 (max Kc₀ 0 ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^ (2 * σ)) *
      (H₀ + max Kc₀ 0 ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g})))
    with hB
  have hH0 : 0 < H₀ := by linarith
  have hL0 : 0 ≤ H₀ + max Kc₀ 0 ^ 2 * (H₀ ^ 2 / X) *
      ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g})) := by
    have : 0 ≤ max Kc₀ 0 ^ 2 * (H₀ ^ 2 / X) * ((absNorm (span {t}) : ℝ) ^ 2 * absNorm (span {g})) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hX.le))
        (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    linarith
  have hX0 : 0 ≤ H₀ ^ σ * max 1 (max Kc₀ 0 ^ 2 * nI (primeSet (span {t * g})) ^ 2 * H₀ ^ 2 / X) ^
      (2 * σ) :=
    mul_nonneg (Real.rpow_nonneg hH0.le _) (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKσ0 (pow_nonneg (by norm_num) _))
      (sq_nonneg _)) (sq_nonneg _)) hX0) hL0
  have hclass : ∀ x ∈ Finset.range KH ×ˢ admissible t g, ∑ k₀ ∈ Ks,
      ‖dualTerm h (d (Ideal.Quotient.mk _ k₀) x.1 x.2) (c₀ (Ideal.Quotient.mk _ k₀) x.1 x.2) x.2
        (jFix t g) k₀ X‖ ^ 2 ≤ (absNorm (span {M}) : ℝ) * B := by
    intro x hx
    have hxA : x.2 ∈ admissible t g := (Finset.mem_product.1 hx).2
    have hfib : ∀ ρ ∈ Ks.image (Ideal.Quotient.mk (span {M})), ∑ k₀ ∈ Ks with
        Ideal.Quotient.mk (span {M}) k₀ = ρ,
        ‖dualTerm h (d (Ideal.Quotient.mk _ k₀) x.1 x.2) (c₀ (Ideal.Quotient.mk _ k₀) x.1 x.2) x.2
          (jFix t g) k₀ X‖ ^ 2 ≤ B := by
      intro ρ _
      have hcongr : ∑ k₀ ∈ Ks with Ideal.Quotient.mk (span {M}) k₀ = ρ,
          ‖dualTerm h (d (Ideal.Quotient.mk _ k₀) x.1 x.2) (c₀ (Ideal.Quotient.mk _ k₀) x.1 x.2) x.2
            (jFix t g) k₀ X‖ ^ 2 = ∑ k₀ ∈ Ks with Ideal.Quotient.mk (span {M}) k₀ = ρ,
          ‖dualTerm h (d ρ x.1 x.2) (c₀ ρ x.1 x.2) x.2 (jFix t g) k₀ X‖ ^ 2 :=
        Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.1 hk).2]
      rw [hcongr]
      have hrowsρ : ∀ k ∈ Ks.filter (fun k => Ideal.Quotient.mk (span {M}) k = ρ), Primary k ∧
          Squarefree (span {k}) ∧ (absNorm (span {k})).Coprime 6 ∧ (absNorm (span {k}) : ℝ) ≤ H₀ :=
        fun k hk => by
          have hk' := hKs k (Finset.mem_filter.1 hk).1
          exact ⟨hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.2⟩
      refine (hKσ h hhs (Cw * N) hhb (d ρ x.1 x.2) (max Kd 0) hKd (hds ρ x.1 x.2) (hdb' ρ x.1 x.2)
        (c₀ ρ x.1 x.2) (hc₀ ρ x.1 x.2).1 x.2 (jFix t g) H₀ X hH hX _ hrowsρ).trans ?_
      exact class_bound_le hKσ0 hσ.le hH hX ((hc₀ ρ x.1 x.2).2.trans (le_max_left _ _)) ht hg htsq
        hxA _ rfl
    rw [← Finset.sum_fiberwise_of_maps_to (t := Ks.image (Ideal.Quotient.mk (span {M})))
      (g := Ideal.Quotient.mk (span {M})) fun k hk => Finset.mem_image_of_mem _ hk]
    calc _ ≤ ∑ _ρ ∈ Ks.image (Ideal.Quotient.mk (span {M})), B := Finset.sum_le_sum hfib
      _ = ((Ks.image (Ideal.Quotient.mk (span {M}))).card : ℝ) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (absNorm (span {M}) : ℝ) * B := mul_le_mul_of_nonneg_right (card_image_mk_le hM Ks) hB0
  -- the sum over the rows and the classes
  have hI : ((Finset.range KH ×ˢ admissible t g).card : ℝ) ≤
      (KH : ℝ) * 2 ^ (primeSet (span {t * g})).card := by
    rw [Finset.card_product, Finset.card_range]
    exact_mod_cast Nat.mul_le_mul_left KH (card_admissible_le t g)
  have hNM : 0 ≤ (absNorm (span {M}) : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  calc ∑ k₀ ∈ Ks, ‖compT ξ (u₀ * t * k₀) g W X‖ ^ 2
      ≤ ∑ k₀ ∈ Ks, ((Finset.range KH ×ˢ admissible t g).card : ℝ) *
          ∑ x ∈ Finset.range KH ×ˢ admissible t g,
            ‖dualTerm h (d (Ideal.Quotient.mk _ k₀) x.1 x.2) (c₀ (Ideal.Quotient.mk _ k₀) x.1 x.2) x.2
              (jFix t g) k₀ X‖ ^ 2 := Finset.sum_le_sum hrow
    _ = ((Finset.range KH ×ˢ admissible t g).card : ℝ) *
          ∑ x ∈ Finset.range KH ×ˢ admissible t g, ∑ k₀ ∈ Ks,
            ‖dualTerm h (d (Ideal.Quotient.mk _ k₀) x.1 x.2) (c₀ (Ideal.Quotient.mk _ k₀) x.1 x.2) x.2
              (jFix t g) k₀ X‖ ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((Finset.range KH ×ˢ admissible t g).card : ℝ) *
          ∑ _x ∈ Finset.range KH ×ˢ admissible t g, (absNorm (span {M}) : ℝ) * B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hclass) (Nat.cast_nonneg _)
    _ = ((Finset.range KH ×ˢ admissible t g).card : ℝ) ^ 2 * ((absNorm (span {M}) : ℝ) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ((KH : ℝ) * 2 ^ (primeSet (span {t * g})).card) ^ 2 * ((absNorm (span {M}) : ℝ) * B) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hI 2) hNM
    _ = _ := by rw [hB, sixtyfour_pow]; ring

/-- `64^ω ≤ C³D^{6C₀δ}` from `4^ω ≤ C x^δ` and `x ≤ D^{2C₀}`. -/
theorem pow64_le {m : ℕ} {C δ x D C₀ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hD : 1 ≤ D)
    (h4 : (4 : ℝ) ^ m ≤ C * x ^ δ) (hxD : x ≤ D ^ (2 * C₀)) :
    (64 : ℝ) ^ m ≤ C ^ 3 * D ^ (6 * C₀ * δ) := by
  have hD0 : 0 < D := by linarith
  have h64 : (64 : ℝ) ^ m = ((4 : ℝ) ^ m) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hxδ : x ^ δ ≤ D ^ (2 * C₀ * δ) := by
    rw [Real.rpow_mul hD0.le]; exact Real.rpow_le_rpow hx hxD hδ
  have hD3 : (D ^ (2 * C₀ * δ)) ^ 3 = D ^ (6 * C₀ * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; congr 1; push_cast; ring
  rw [h64]
  calc ((4 : ℝ) ^ m) ^ 3 ≤ (C * x ^ δ) ^ 3 := pow_le_pow_left₀ (by positivity) h4 3
    _ ≤ (C * D ^ (2 * C₀ * δ)) ^ 3 :=
        pow_le_pow_left₀ (mul_nonneg hC (Real.rpow_nonneg hx _))
          (mul_le_mul_of_nonneg_left hxδ hC) 3
    _ = C ^ 3 * D ^ (6 * C₀ * δ) := by rw [mul_pow, hD3]

/-- `H^σ ≤ D^{C₀σ}` for `0 < H ≤ D^{C₀}`. -/
theorem rpow_le_of_le_rpow {H D C₀ σ : ℝ} (hH : 0 ≤ H) (hD : 0 < D) (hσ : 0 ≤ σ)
    (hHD : H ≤ D ^ C₀) : H ^ σ ≤ D ^ (C₀ * σ) := by
  rw [Real.rpow_mul hD.le]; exact Real.rpow_le_rpow hH hHD hσ

/-- `max(1, K²n²H²/X)^{2σ} ≤ max(1, K²)D^{12C₀σ}` for `n ≤ D^{2C₀}`, `H ≤ D^{C₀}`, `X ≥ 1`,
`0 ≤ σ ≤ 1/2`. -/
theorem max_rpow_le {K n H X D C₀ σ : ℝ} (hn : 0 ≤ n) (hH : 0 ≤ H) (hX : 1 ≤ X) (hD : 1 ≤ D)
    (hC₀ : 0 ≤ C₀) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1 / 2) (hnD : n ≤ D ^ (2 * C₀)) (hHD : H ≤ D ^ C₀) :
    max 1 (K ^ 2 * n ^ 2 * H ^ 2 / X) ^ (2 * σ) ≤ max 1 (K ^ 2) * D ^ (12 * C₀ * σ) := by
  have hD0 : 0 < D := by linarith
  have hX0 : 0 < X := by linarith
  have hD6 : 1 ≤ D ^ (6 * C₀) := Real.one_le_rpow hD (by linarith)
  have hinner : K ^ 2 * n ^ 2 * H ^ 2 / X ≤ max 1 (K ^ 2) * D ^ (6 * C₀) := by
    have h1 : n ^ 2 ≤ D ^ (4 * C₀) := by
      calc n ^ 2 ≤ (D ^ (2 * C₀)) ^ 2 := pow_le_pow_left₀ hn hnD 2
        _ = D ^ (4 * C₀) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; congr 1; push_cast; ring
    have h2 : H ^ 2 ≤ D ^ (2 * C₀) := by
      calc H ^ 2 ≤ (D ^ C₀) ^ 2 := pow_le_pow_left₀ hH hHD 2
        _ = D ^ (2 * C₀) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; congr 1; push_cast; ring
    have h6 : D ^ (4 * C₀) * D ^ (2 * C₀) = D ^ (6 * C₀) := by
      rw [← Real.rpow_add hD0]; congr 1; ring
    calc K ^ 2 * n ^ 2 * H ^ 2 / X ≤ K ^ 2 * n ^ 2 * H ^ 2 :=
          div_le_self (by positivity) hX
      _ ≤ max 1 (K ^ 2) * (D ^ (4 * C₀) * D ^ (2 * C₀)) := by
          rw [mul_assoc]
          exact mul_le_mul (le_max_right _ _) (mul_le_mul h1 h2 (sq_nonneg _) (by positivity))
            (by positivity) (le_trans zero_le_one (le_max_left _ _))
      _ = max 1 (K ^ 2) * D ^ (6 * C₀) := by rw [h6]
  have hM1 : 1 ≤ max 1 (K ^ 2) := le_max_left _ _
  have hmax : max 1 (K ^ 2 * n ^ 2 * H ^ 2 / X) ≤ max 1 (K ^ 2) * D ^ (6 * C₀) :=
    max_le (one_le_mul_of_one_le_of_one_le hM1 hD6) hinner
  calc max 1 (K ^ 2 * n ^ 2 * H ^ 2 / X) ^ (2 * σ)
      ≤ (max 1 (K ^ 2) * D ^ (6 * C₀)) ^ (2 * σ) :=
        Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) hmax (by linarith)
    _ = max 1 (K ^ 2) ^ (2 * σ) * D ^ (12 * C₀ * σ) := by
        rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hD0.le]
        congr 2; ring
    _ ≤ max 1 (K ^ 2) * D ^ (12 * C₀ * σ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc max 1 (K ^ 2) ^ (2 * σ) ≤ max 1 (K ^ 2) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
          _ = max 1 (K ^ 2) := Real.rpow_one _

/-- `Hh/n + K²((Hh/n)²/X)(n²G) ≤ max(1, K²)(Hh + Hh²G/X)` for `n ≥ 1`. -/
theorem last_le {Hh n G K X : ℝ} (hH : 0 ≤ Hh) (hn : 1 ≤ n) (hG : 0 ≤ G) (hX : 0 < X) :
    Hh / n + K ^ 2 * ((Hh / n) ^ 2 / X) * (n ^ 2 * G) ≤ max 1 (K ^ 2) * (Hh + Hh ^ 2 * G / X) := by
  have hn0 : 0 < n := by linarith
  have h1 : Hh / n ≤ Hh := div_le_self hH hn
  have h2 : K ^ 2 * ((Hh / n) ^ 2 / X) * (n ^ 2 * G) = K ^ 2 * (Hh ^ 2 * G / X) := by
    field_simp
  rw [h2]
  have hM1 : 1 ≤ max 1 (K ^ 2) := le_max_left _ _
  have hK : K ^ 2 ≤ max 1 (K ^ 2) := le_max_right _ _
  have hHG : 0 ≤ Hh ^ 2 * G / X := div_nonneg (mul_nonneg (sq_nonneg _) hG) hX.le
  calc Hh / n + K ^ 2 * (Hh ^ 2 * G / X) ≤ max 1 (K ^ 2) * Hh + max 1 (K ^ 2) * (Hh ^ 2 * G / X) :=
        add_le_add (h1.trans (le_mul_of_one_le_left hH hM1)) (mul_le_mul_of_nonneg_right hK hHG)
    _ = max 1 (K ^ 2) * (Hh + Hh ^ 2 * G / X) := by ring

/-- Monotonicity of `K a₁ n (a₂ a₃) a₄` in the four factors. -/
theorem mul5_le {K n a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℝ} (hK : 0 ≤ K) (hn : 0 ≤ n) (h1 : a₁ ≤ b₁)
    (h10 : 0 ≤ a₁) (h2 : a₂ ≤ b₂) (h20 : 0 ≤ a₂) (h3 : a₃ ≤ b₃) (h30 : 0 ≤ a₃) (h4 : a₄ ≤ b₄)
    (h40 : 0 ≤ a₄) : K * a₁ * n * (a₂ * a₃) * a₄ ≤ K * b₁ * n * (b₂ * b₃) * b₄ := by
  have hb1 : 0 ≤ b₁ := h10.trans h1
  have hb2 : 0 ≤ b₂ := h20.trans h2
  have hb3 : 0 ≤ b₃ := h30.trans h3
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hn)
    (mul_le_mul h2 h3 h30 hb2) (mul_nonneg h20 h30) (mul_nonneg (mul_nonneg hK hb1) hn)) h4 h40
    (mul_nonneg (mul_nonneg (mul_nonneg hK hb1) hn) (mul_nonneg hb2 hb3))

open Classical in
/-- **Lemma 6.6 from the displayed transformation and the quadratic large sieve** (the companion
paper's proof of its Lemma 6.6): `ThetaRows → QuadLargeSieve → SquarefreeCompleted`. -/
theorem squarefreeCompleted_of (hθ : ThetaRows) (hLS : QuadLargeSieve) : SquarefreeCompleted := by
  intro ε hε C₀ hC₀
  have hC₀0 : 0 < C₀ := by linarith
  set σ : ℝ := min (1 / 2) (ε / (26 * C₀)) with hσdef
  have hσ : 0 < σ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hσ' : σ ≤ 1 / 2 := min_le_left _ _
  have hσε : 13 * C₀ * σ ≤ ε / 2 := by
    have h1 : σ ≤ ε / (26 * C₀) := min_le_right _ _
    calc 13 * C₀ * σ ≤ 13 * C₀ * (ε / (26 * C₀)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = ε / 2 := by field_simp; ring
  set δ : ℝ := ε / (14 * C₀) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : 7 * C₀ * δ = ε / 2 := by rw [hδdef]; field_simp; ring
  obtain ⟨Cδ, hCδ0, hCδ⟩ := four_pow_card_le hδ
  obtain ⟨J, hJ⟩ := rows_meanSquare hθ hLS hσ hσ'
  refine ⟨J, fun α β hα => ?_⟩
  by_cases hαβ : α ≤ β
  swap
  · refine ⟨0, fun ξ W _ hsupp N _ D Hh X _ _ _ _ _ g _ _ Ss _ => ?_⟩
    have hW0 : ∀ x, W x = 0 := fun x => hsupp x (by
      rcases lt_or_ge x α with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_lt_of_le (lt_of_not_ge hαβ) h))
    simp [compT_eq_zero_of_zero ξ _ g hW0 X]
  obtain ⟨K₁, Kc, hK₁, hKc, hrows⟩ := hJ α β hα hαβ
  refine ⟨6 * 2 ^ c6 * Cδ ^ 4 * K₁ * max 1 (Kc ^ 2) ^ 2, ?_⟩
  intro ξ W hW hsupp N hN D Hh X hD hH hX hHD hXD g hg hgD Ss hSs
  have hD0 : 0 < D := by linarith
  have hX0 : 0 < X := by linarith
  have hnG : 1 ≤ (absNorm (span {g}) : ℝ) := one_le_absNorm_span hg
  have hsplit : ∀ s ∈ Ss, ∃ (u : (𝓞 K)ˣ) (T : Ideal (𝓞 K)) (k₀ : 𝓞 K), s = u * gen T * k₀ ∧
      T ∈ tIdeals g ∧ T ≠ ⊥ ∧ Squarefree T ∧ Primary k₀ ∧ Squarefree (span {k₀}) ∧
      (absNorm (span {k₀})).Coprime 6 ∧ IsCoprime k₀ (gen T * g) ∧
      absNorm (span {s}) = absNorm T * absNorm (span {k₀}) :=
    fun s hs => exists_row_split (hSs s hs).1 (hSs s hs).2.1 hg
  choose! u T k₀ hsp using hsplit
  set G : ℝ := K₁ * Cδ ^ 3 * max 1 (Kc ^ 2) ^ 2 * N ^ 2 * D ^ (6 * C₀ * δ + 13 * C₀ * σ) *
      (Hh + Hh ^ 2 * (absNorm (span {g}) : ℝ) / X) with hGdef
  have hgroup : ∀ p ∈ Ss.image (fun s => (u s, T s)),
      ∑ s ∈ Ss with (u s, T s) = p, ‖compT ξ s g W X‖ ^ 2 ≤ G := by
    intro p hp
    obtain ⟨s₀, hs₀, hs₀p⟩ := Finset.mem_image.1 hp
    have hmemF : ∀ s ∈ Ss.filter (fun s => (u s, T s) = p), s ∈ Ss ∧ u s = p.1 ∧ T s = p.2 := by
      intro s hs
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hs
      exact ⟨h1, by rw [← h2], by rw [← h2]⟩
    have heq : ∀ s ∈ Ss.filter (fun s => (u s, T s) = p), s = p.1 * gen p.2 * k₀ s := by
      intro s hs
      obtain ⟨h1, h2, h3⟩ := hmemF s hs
      rw [← h2, ← h3]; exact (hsp s h1).1
    have hsum : ∑ s ∈ Ss with (u s, T s) = p, ‖compT ξ s g W X‖ ^ 2 =
        ∑ k ∈ (Ss.filter (fun s => (u s, T s) = p)).image k₀,
          ‖compT ξ (p.1 * gen p.2 * k) g W X‖ ^ 2 := by
      rw [Finset.sum_image fun x hx y hy hxy => (by rw [heq x hx, heq y hy, hxy] : x = y)]
      exact Finset.sum_congr rfl fun s hs => by rw [← heq s hs]
    rw [hsum]
    have hp2 : p.2 = T s₀ := by rw [← hs₀p]
    obtain ⟨-, -, hT0, hTsq, -, -, h60, -, hN₀⟩ := hsp s₀ hs₀
    rw [← hp2] at hT0 hTsq hN₀
    set nT : ℝ := (absNorm p.2 : ℝ) with hnTdef
    have hnT1 : 1 ≤ nT := by
      have : absNorm p.2 ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
      rw [hnTdef]; exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    have hk1 := one_le_absNorm_of_coprime6 h60
    have hs₀N : (absNorm (span {s₀}) : ℝ) ≤ Hh := (hSs s₀ hs₀).2.2
    rw [hN₀] at hs₀N; push_cast at hs₀N
    have hnTH : nT ≤ Hh := le_trans (le_mul_of_one_le_right (by linarith) hk1) hs₀N
    have hH₀ : 1 ≤ Hh / nT := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have hrowsP : ∀ k ∈ (Ss.filter (fun s => (u s, T s) = p)).image k₀, Primary k ∧
        Squarefree (span {k}) ∧ (absNorm (span {k})).Coprime 6 ∧ IsCoprime k (gen p.2 * g) ∧
        (absNorm (span {k}) : ℝ) ≤ Hh / nT := by
      intro k hk
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hk
      obtain ⟨h1, -, h3⟩ := hmemF s hs
      obtain ⟨-, -, -, -, hpr, hsq', h6, hcop, hNs⟩ := hsp s h1
      rw [h3] at hcop hNs
      refine ⟨hpr, hsq', h6, hcop, ?_⟩
      rw [le_div_iff₀ (by linarith)]
      have hsN : (absNorm (span {s}) : ℝ) ≤ Hh := (hSs s h1).2.2
      rw [hNs] at hsN; push_cast at hsN
      linarith
    have hR := hrows ξ W hW hsupp N hN p.1 (gen p.2) g (gen_ne_zero hT0) hg
      (by rw [span_gen]; exact hTsq) (Hh / nT) X hH₀ hX0 _ hrowsP
    refine hR.trans ?_
    have hspanmul : span {gen p.2 * g} = p.2 * span {g} := by
      rw [← Ideal.span_singleton_mul_span_singleton, span_gen]
    have hne : span {gen p.2 * g} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero (gen_ne_zero hT0) hg
    have hxle : nI (primeSet (span {gen p.2 * g})) ≤ nT * (absNorm (span {g}) : ℝ) := by
      calc nI (primeSet (span {gen p.2 * g})) ≤ absNorm (span {gen p.2 * g}) := nI_primeSet_le hne
        _ = nT * (absNorm (span {g}) : ℝ) := by rw [hspanmul, map_mul]; push_cast; rfl
    have hxD : nT * (absNorm (span {g}) : ℝ) ≤ D ^ (2 * C₀) := by
      have h1 : nT ≤ D ^ C₀ := hnTH.trans hHD
      calc nT * (absNorm (span {g}) : ℝ) ≤ D ^ C₀ * D ^ C₀ :=
            mul_le_mul h1 hgD (by linarith) (Real.rpow_nonneg hD0.le _)
        _ = D ^ (2 * C₀) := by rw [← Real.rpow_add hD0]; ring_nf
    have hx0 : 0 ≤ nI (primeSet (span {gen p.2 * g})) := (nI_pos _).le
    have h64 := pow64_le hCδ0.le hδ.le hx0 hD (hCδ _) (hxle.trans hxD)
    have hH0le : Hh / nT ≤ D ^ C₀ := (div_le_self (by linarith) hnT1).trans hHD
    have hH00 : 0 ≤ Hh / nT := div_nonneg (by linarith) (by linarith)
    have hHσ := rpow_le_of_le_rpow hH00 hD0 hσ.le hH0le
    have hmax := max_rpow_le (K := Kc) hx0 hH00 hX hD hC₀0.le hσ.le hσ' (hxle.trans hxD) hH0le
    have hspan_gen : (absNorm (span {gen p.2}) : ℝ) = nT := by rw [span_gen]
    have hlast := last_le (K := Kc) (by linarith : (0 : ℝ) ≤ Hh) hnT1
      (by linarith : (0 : ℝ) ≤ (absNorm (span {g}) : ℝ)) hX0
    rw [hspan_gen]
    have hL0 : 0 ≤ Hh / nT + Kc ^ 2 * ((Hh / nT) ^ 2 / X) * (nT ^ 2 * (absNorm (span {g}) : ℝ)) :=
      add_nonneg hH00 (mul_nonneg (mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hX0.le))
        (mul_nonneg (sq_nonneg _) (by linarith)))
    have hD3 : D ^ (6 * C₀ * δ) * (D ^ (C₀ * σ) * D ^ (12 * C₀ * σ)) =
        D ^ (6 * C₀ * δ + 13 * C₀ * σ) := by
      rw [← Real.rpow_add hD0, ← Real.rpow_add hD0]; ring_nf
    refine (mul5_le hK₁ (sq_nonneg N) h64 (pow_nonneg (by norm_num) _) hHσ
      (Real.rpow_nonneg hH00 _) hmax
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) hlast hL0).trans_eq ?_
    rw [hGdef, ← hD3]; ring
  -- the sum over the groups
  have hXX : 0 ≤ Hh + Hh ^ 2 * (absNorm (span {g}) : ℝ) / X :=
    add_nonneg (by linarith) (div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hX0.le)
  have hK0 : 0 ≤ 6 * 2 ^ c6 * Cδ ^ 4 * K₁ * max 1 (Kc ^ 2) ^ 2 * N ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hCδ0.le 4)) hK₁)
      (sq_nonneg _)) (sq_nonneg _)
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK₁ (pow_nonneg hCδ0.le 3))
      (sq_nonneg _)) (sq_nonneg _)) (Real.rpow_nonneg hD0.le _)) hXX
  have hcard : ((Ss.image (fun s => (u s, T s))).card : ℝ) ≤ 6 * 2 ^ c6 * (Cδ * D ^ (C₀ * δ)) := by
    have hsub : Ss.image (fun s => (u s, T s)) ⊆ Finset.univ ×ˢ tIdeals g := by
      intro p hp
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hp
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, (hsp s hs).2.1⟩
    have h1 : (Ss.image (fun s => (u s, T s))).card ≤ 6 * 2 ^ (c6 + (primeSet (span {g})).card) := by
      calc (Ss.image (fun s => (u s, T s))).card ≤ (Finset.univ ×ˢ tIdeals g).card :=
            Finset.card_le_card hsub
        _ = Fintype.card (𝓞 K)ˣ * (tIdeals g).card := by rw [Finset.card_product, Finset.card_univ]
        _ ≤ 6 * 2 ^ (c6 + (primeSet (span {g})).card) :=
            Nat.mul_le_mul card_units_le (card_tIdeals_le g)
    have hgne : span {g} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    have h2 : (2 : ℝ) ^ (primeSet (span {g})).card ≤ Cδ * D ^ (C₀ * δ) := by
      calc (2 : ℝ) ^ (primeSet (span {g})).card ≤ 4 ^ (primeSet (span {g})).card :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ ≤ Cδ * nI (primeSet (span {g})) ^ δ := hCδ _
        _ ≤ Cδ * D ^ (C₀ * δ) :=
            mul_le_mul_of_nonneg_left
              (rpow_le_of_le_rpow (nI_pos _).le hD0 hδ.le ((nI_primeSet_le hgne).trans hgD))
              hCδ0.le
    calc ((Ss.image (fun s => (u s, T s))).card : ℝ) ≤ 6 * 2 ^ (c6 + (primeSet (span {g})).card) := by
          exact_mod_cast h1
      _ = 6 * 2 ^ c6 * 2 ^ (primeSet (span {g})).card := by rw [pow_add]; ring
      _ ≤ 6 * 2 ^ c6 * (Cδ * D ^ (C₀ * δ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hDε : D ^ (C₀ * δ) * D ^ (6 * C₀ * δ + 13 * C₀ * σ) ≤ D ^ ε := by
    rw [← Real.rpow_add hD0]
    exact Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  calc ∑ s ∈ Ss, ‖compT ξ s g W X‖ ^ 2
      = ∑ p ∈ Ss.image (fun s => (u s, T s)), ∑ s ∈ Ss with (u s, T s) = p,
          ‖compT ξ s g W X‖ ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun s hs => Finset.mem_image_of_mem _ hs) _).symm
    _ ≤ ∑ _p ∈ Ss.image (fun s => (u s, T s)), G := Finset.sum_le_sum hgroup
    _ = ((Ss.image (fun s => (u s, T s))).card : ℝ) * G := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 6 * 2 ^ c6 * (Cδ * D ^ (C₀ * δ)) * G := mul_le_mul_of_nonneg_right hcard hG0
    _ = 6 * 2 ^ c6 * Cδ ^ 4 * K₁ * max 1 (Kc ^ 2) ^ 2 * N ^ 2 *
          (D ^ (C₀ * δ) * D ^ (6 * C₀ * δ + 13 * C₀ * σ)) *
          (Hh + Hh ^ 2 * (absNorm (span {g}) : ℝ) / X) := by rw [hGdef]; ring
    _ ≤ 6 * 2 ^ c6 * Cδ ^ 4 * K₁ * max 1 (Kc ^ 2) ^ 2 * N ^ 2 * D ^ ε *
          (Hh + Hh ^ 2 * (absNorm (span {g}) : ℝ) / X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDε hK0) hXX

/-- **The zero-free half-plane from the two displayed inputs**: the companion paper's theta
transformation for the rows (`ThetaRows`) and its quadratic large sieve (`QuadLargeSieve`) give
`ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > 11/12`. -/
theorem ne_zero_of_theta (hθ : ThetaRows) (hLS : QuadLargeSieve) {s : ℂ} (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_squarefree (squarefreeCompleted_of hθ hLS) hs

end Eis

end

#print axioms Eis.compT_eq_zero_of_zero
#print axioms Eis.nI_primeSet_le
#print axioms Eis.card_tIdeals_le
#print axioms Eis.exists_row_split
#print axioms Eis.card_image_mk_le
#print axioms Eis.class_bound_le
#print axioms Eis.rows_meanSquare
#print axioms Eis.squarefreeCompleted_of
#print axioms Eis.ne_zero_of_theta
