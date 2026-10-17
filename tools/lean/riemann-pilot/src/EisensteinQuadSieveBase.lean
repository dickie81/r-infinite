import EisensteinQuadSieveNorm

/-! # The quadratic large sieve, part 2: the base case `(E_2)` (round 345)

S5e of round 312's plan, part 2 (round 343's S5e-2): Heath-Brown's base case, the exponent `2`, by
the plane majorant and Poisson summation with excluded primes.

* **The pair product** (`q2_mul_q2`): with `ρ_A(u) = ∏_{P∈A} ρ_P(u)`, `ρ_{A₁}(u)ρ_{A₂}(u)` is
  `ρ_D(u)` for `D = (A₁ \ A₂) ∪ (A₂ \ A₁)` when `u` is prime to `A₁ ∩ A₂`, and `0` otherwise.
* **The Gauss sum bound** (`norm_gaussTr_q2_le`, `gaussTr_q2_zero`): `|G_c(ρ_D, μ)| ≤ |σc|` for
  `c = ∏_{P∈D} π_P`, and `G_c(ρ_D, 0) = 0` for nonempty `D`.
* **The dual sum** (`norm_tsum_dualG_le`): the majorant's dual weight vanishes beyond `R_Φ`, so the
  dual sum is its zero frequency plus at most `49Y` nonzero frequencies.
* **The pair sums** (`pS`, `norm_pS_le`): Poisson summation with the primes of `A₁ ∩ A₂` excluded
  gives `|S(A₁, A₂)| ≤ 2^{|A₁∩A₂|}·(2H·|G_c(ρ_D, 0)|·B + 49R_Φ²B·√N(c))`. Off the diagonal the
  first term vanishes (`norm_pS_off`); on it `c = 1` (`norm_pS_diag`).
* **The transposed base bound** (`dual_q2_bound`): for admissible moduli `k` of norm at most `M` and
  any arguments `u` of norm at most `H`, `Σ_u |Σ_k b(k)(u/k)₂|² ≤ C·M^δ·(H + M²)·Σ_k |b(k)|²`.
* **`qBound_base`**: `QBound M N (C·M^δ·(N + M²))`, by duality.
* **`qExp_two`**: `QExp 2`, by the symmetry of the norm (`QBound.symm`, Heath-Brown's Lemma 1).
-/

open NumberField Complex Ideal
open scoped ComplexConjugate

noncomputable section

namespace Eis

open Classical in
/-- The quadratic character of `∏_{P∈A} π_P` as a product over the primes. -/
def q2 (A : Finset Pr) (u : 𝓞 K) : ℂ :=
  ∏ P ∈ A, quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) u)

open Classical in
theorem quadR_sq_mk (P : Pr) (u : 𝓞 K) :
    quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) u) ^ 2 =
      if πP P ∣ u then 0 else 1 := by
  split_ifs with h
  · have : Ideal.Quotient.mk (span {πP P}) u = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton.2 h
    rw [this, MulChar.map_zero, zero_pow two_ne_zero]
  · refine quadR_sq_eq_one _ _ ?_
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hm => h (Ideal.mem_span_singleton.1 hm)

open Classical in
theorem q2_union {A B : Finset Pr} (h : Disjoint A B) (u : 𝓞 K) :
    q2 (A ∪ B) u = q2 A u * q2 B u := by
  unfold q2; rw [Finset.prod_union h]

open Classical in
/-- **The pair product**: `ρ_{A₁}(u)ρ_{A₂}(u)` is `ρ_D(u)` with `D = A₁ △ A₂` when `u` is prime to
`A₁ ∩ A₂`, and `0` otherwise. -/
theorem q2_mul_q2 (A1 A2 : Finset Pr) (u : 𝓞 K) :
    q2 A1 u * q2 A2 u =
      if ∀ P ∈ A1 ∩ A2, ¬ πP P ∣ u then q2 ((A1 \ A2) ∪ (A2 \ A1)) u else 0 := by
  have d1 : Disjoint (A1 \ A2) (A1 ∩ A2) := Finset.disjoint_sdiff_inter A1 A2
  have d2 : Disjoint (A2 \ A1) (A1 ∩ A2) := by
    rw [Finset.inter_comm]; exact Finset.disjoint_sdiff_inter A2 A1
  have d3 : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  have hsq : q2 (A1 ∩ A2) u * q2 (A1 ∩ A2) u =
      if ∀ P ∈ A1 ∩ A2, ¬ πP P ∣ u then 1 else 0 := by
    unfold q2
    rw [← Finset.prod_mul_distrib]
    simp_rw [← sq, quadR_sq_mk]
    split_ifs with h
    · exact Finset.prod_eq_one fun P hP => by simp only [h P hP, ↓reduceIte]
    · push Not at h
      obtain ⟨P, hP, hd⟩ := h
      exact Finset.prod_eq_zero hP (by simp only [hd, ↓reduceIte])
  have h1 : q2 A1 u = q2 (A1 \ A2) u * q2 (A1 ∩ A2) u := by
    rw [← q2_union d1, Finset.sdiff_union_inter]
  have h2 : q2 A2 u = q2 (A2 \ A1) u * q2 (A1 ∩ A2) u := by
    rw [← q2_union d2, Finset.inter_comm, Finset.sdiff_union_inter]
  have : q2 A1 u * q2 A2 u = q2 ((A1 \ A2) ∪ (A2 \ A1)) u * (q2 (A1 ∩ A2) u * q2 (A1 ∩ A2) u) := by
    rw [h1, h2, q2_union d3]
    ring
  rw [this, hsq]
  split_ifs <;> ring

open Classical in
theorem q2_periodic (A : Finset Pr) (z u : 𝓞 K) :
    q2 A (z + (∏ P ∈ A, πP P) * u) = q2 A z := by
  unfold q2
  refine Finset.prod_congr rfl fun P hP => ?_
  congr 1
  rw [Ideal.Quotient.eq, add_sub_cancel_left, Ideal.mem_span_singleton]
  exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hP) u

open Classical in
theorem q2_mul (A : Finset Pr) (a z : 𝓞 K) : q2 A (a * z) = q2 A a * q2 A z := by
  unfold q2; rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun P _ => by rw [map_mul, map_mul]

open Classical in
theorem norm_q2_le (A : Finset Pr) (u : 𝓞 K) : ‖q2 A u‖ ≤ 1 := by
  unfold q2
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun P _ => ?_
  have h := quadR_sq_mk P u
  split_ifs at h with hd
  · rw [pow_eq_zero_iff two_ne_zero] at h; rw [h, norm_zero]; exact zero_le_one
  · have : ‖quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) u)‖ ^ 2 = 1 := by
      rw [← norm_pow, h, norm_one]
    nlinarith [norm_nonneg (quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) u))]

open Classical in
theorem conj_q2 (A : Finset Pr) (u : 𝓞 K) : conj (q2 A u) = q2 A u := by
  unfold q2
  rw [map_prod]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [MulChar.ringHomComp_apply]
  exact map_intCast (starRingEnd ℂ) _

open Classical in
theorem quadR_ne_one (P : Pr) : quadR (𝓞 K ⧸ span {πP P}) ℂ ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).2
    (quadraticChar_ne_one (ringChar_ne_two_of_two (πP P) (two_not_mem_Pr P)))

open Classical in
theorem quadR_pow_six (P : Pr) : quadR (𝓞 K ⧸ span {πP P}) ℂ ^ 6 = 1 := by
  have hq : (quadR (𝓞 K ⧸ span {πP P}) ℂ).IsQuadratic := (quadraticChar_isQuadratic _).comp _
  rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hq.sq_eq_one, one_pow]

open Classical in
/-- **The Gauss sum bound**: `|G_c(ρ_D, μ)| ≤ |σc|` for `c = ∏_{P∈D} π_P`, with `G_c(ρ_D, 0) = 0` for
nonempty `D`. -/
theorem gaussTr_q2_eq (D : Finset Pr) (μ : 𝓞 K) :
    gaussTr (∏ P ∈ D, πP P) (q2 D) μ =
      (∏ P ∈ D, (quadR (𝓞 K ⧸ span {πP P}) ℂ)⁻¹ (Ideal.Quotient.mk (span {πP P}) μ)) *
        (((‖σO (∏ P ∈ D, πP P)‖ : ℝ) : ℂ) *
          gamF πP D (fun P => quadR (𝓞 K ⧸ span {πP P}) ℂ)) := by
  have h := gaussTr_chars_mu D (fun P => quadR (𝓞 K ⧸ span {πP P}) ℂ) (fun P _ => quadR_ne_one P) μ
  rw [gaussTr_one_eq_gamF] at h
  exact h

open Classical in
theorem norm_gaussTr_q2_le (D : Finset Pr) (μ : 𝓞 K) :
    ‖gaussTr (∏ P ∈ D, πP P) (q2 D) μ‖ ≤ ‖σO (∏ P ∈ D, πP P)‖ := by
  rw [gaussTr_q2_eq, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    norm_gamF πP D (hcopPr D) _ (fun P _ => quadR_ne_one P) (fun P _ => quadR_pow_six P), mul_one]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun P _ => ?_
  rw [MulChar.inv_apply_eq_inv']
  have h := quadR_sq_mk P μ
  split_ifs at h with hd
  · rw [pow_eq_zero_iff two_ne_zero] at h; rw [h, inv_zero, norm_zero]; exact zero_le_one
  · have h1 : ‖quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) μ)‖ = 1 := by
      have : ‖quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) μ)‖ ^ 2 = 1 := by
        rw [← norm_pow, h, norm_one]
      nlinarith [norm_nonneg (quadR (𝓞 K ⧸ span {πP P}) ℂ (Ideal.Quotient.mk (span {πP P}) μ))]
    rw [norm_inv, h1, inv_one]

open Classical in
theorem gaussTr_q2_zero {D : Finset Pr} (hD : D.Nonempty) :
    gaussTr (∏ P ∈ D, πP P) (q2 D) 0 = 0 := by
  rw [gaussTr_q2_eq]
  obtain ⟨P, hP⟩ := hD
  rw [Finset.prod_eq_zero hP (by rw [map_zero, MulChar.map_zero]), zero_mul]

/-- A bound for the majorant's dual weight. -/
theorem exists_norm_dualG_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ, ‖dualG ρ‖ ≤ B := by
  obtain ⟨C, hC⟩ := dualG_bounded 0
  have h : ∀ ρ, ‖dualG ρ‖ ≤ C := fun ρ => by
    have := hC ρ
    rwa [norm_iteratedFDeriv_zero] at this
  exact ⟨C, (norm_nonneg _).trans (h 0), h⟩

theorem one_le_absNorm_of_ne_zero {μ : 𝓞 K} (hμ : μ ≠ 0) : (1 : ℝ) ≤ (absNorm (span {μ}) : ℝ) := by
  have h : absNorm (span {μ} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h

open Classical in
/-- **The dual sum**: with `|g| ≤ G` and the dual weight vanishing beyond `R_Φ`,
`|Σ_μ g(μ)·G(√(4H·N(μ)/(3ab)))| ≤ |g(0)|·B + 49·Y·G·B` with `Y = 3R_Φ²ab/(4H)`. -/
theorem norm_tsum_dualG_le {H a b G B : ℝ} (hH : 0 < H) (ha : 0 < a) (hb : 0 < b)
    (hB : ∀ ρ, ‖dualG ρ‖ ≤ B) (g : 𝓞 K → ℂ) (hg : ∀ μ, ‖g μ‖ ≤ G) :
    ‖∑' μ : 𝓞 K, g μ * dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) / (3 * a * b)))‖ ≤
      ‖g 0‖ * B + 49 * (3 * RΦ ^ 2 * (a * b) / (4 * H)) * G * B := by
  have hX : 0 < a * b := mul_pos ha hb
  set X : ℝ := a * b with hXd
  have h3 : 3 * a * b = 3 * X := by rw [hXd]; ring
  simp_rw [h3]
  set Y : ℝ := 3 * RΦ ^ 2 * X / (4 * H) with hY
  have hY0 : 0 < Y := by have := RΦ_pos; positivity
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hg 0)
  have h00 : (absNorm (span {(0 : 𝓞 K)}) : ℝ) = 0 := by
    rw [show (span {(0 : 𝓞 K)} : Ideal (𝓞 K)) = ⊥ from Ideal.span_singleton_eq_bot.2 rfl,
      absNorm_bot, Nat.cast_zero]
  have h0mem : (0 : 𝓞 K) ∈ eltsLe Y := mem_eltsLe.2 (by rw [h00]; exact hY0.le)
  rw [tsum_eq_sum (s := eltsLe Y)]
  · rw [← Finset.add_sum_erase _ _ h0mem]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · refine (norm_sum_le _ _).trans ?_
      have hcard : (((eltsLe Y).erase 0).card : ℝ) ≤ 49 * Y := by
        by_cases h1 : 1 ≤ Y
        · exact (Nat.cast_le.2 (Finset.card_erase_le)).trans (card_eltsLe_le h1)
        · have : (eltsLe Y).erase 0 = ∅ := by
            refine Finset.eq_empty_of_forall_notMem fun μ hμ => ?_
            obtain ⟨hne, hm⟩ := Finset.mem_erase.1 hμ
            exact h1 ((one_le_absNorm_of_ne_zero hne).trans (mem_eltsLe.1 hm))
          rw [this, Finset.card_empty, Nat.cast_zero]; positivity
      calc ∑ μ ∈ (eltsLe Y).erase 0,
            ‖g μ * dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) / (3 * X)))‖
          ≤ ∑ _μ ∈ (eltsLe Y).erase 0, G * B := by
            refine Finset.sum_le_sum fun μ _ => ?_
            rw [norm_mul]; exact mul_le_mul (hg μ) (hB _) (norm_nonneg _) hG0
        _ = (((eltsLe Y).erase 0).card : ℝ) * (G * B) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 49 * Y * (G * B) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hG0 hB0)
        _ = 49 * Y * G * B := by ring
  · intro μ hμ
    rw [mem_eltsLe, not_le] at hμ
    have hz : dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) / (3 * X))) = 0 := by
      refine dualG_eq_zero_of_ge ?_
      rw [show RΦ = Real.sqrt (RΦ ^ 2) from (Real.sqrt_sq RΦ_pos.le).symm]
      refine Real.sqrt_le_sqrt ?_
      rw [le_div_iff₀ (by positivity)]
      rw [hY, div_lt_iff₀ (by positivity)] at hμ
      nlinarith
    rw [hz, mul_zero]

/-- The quadratic pair sum `Σ_u ρ_{A₁}(u)ρ_{A₂}(u)·Φ(σu/√H)`. -/
def pS (H : ℝ) (A1 A2 : Finset Pr) : ℂ :=
  ∑' u : 𝓞 K, q2 A1 u * q2 A2 u * Majorant.Phi (σO u / (Real.sqrt H : ℂ))

theorem sqrt3_ge : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by
  rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

open Classical in
/-- **One term of the dual side**: the `T`-term of Poisson summation for the pair sum is at most
`2H/(√3·N(c)·N(d_T))·|G_c(ρ_D, 0)|·B + 49·R_Φ²·B·√N(c)`, with `c = ∏_{P∈D} π_P`. -/
theorem norm_pS_term_le {H : ℝ} (hH : 0 < H) {B : ℝ} (hB : ∀ ρ, ‖dualG ρ‖ ≤ B) (D T : Finset Pr) :
    ‖(-1 : ℂ) ^ T.card *
        (((2 * H / (Real.sqrt 3 * (absNorm (span {∏ P ∈ D, πP P}) : ℝ) *
            (absNorm (span {∏ P ∈ T, πP P}) : ℝ)) : ℝ) : ℂ) *
          ∑' μ : 𝓞 K, gaussTr (∏ P ∈ D, πP P) (fun z => q2 D ((∏ P ∈ T, πP P) * z)) μ *
            dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
              (3 * (absNorm (span {∏ P ∈ D, πP P}) : ℝ) *
                (absNorm (span {∏ P ∈ T, πP P}) : ℝ)))))‖ ≤
      2 * H * ‖gaussTr (∏ P ∈ D, πP P) (q2 D) 0‖ * B + 49 * RΦ ^ 2 * B * Real.sqrt (nI D) := by
  rw [absNorm_span_prod_πP, absNorm_span_prod_πP]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have ha := nI_pos D
  have hb := nI_pos T
  have hs3 : (3 : ℝ) / 2 ≤ Real.sqrt 3 := sqrt3_ge
  set c : 𝓞 K := ∏ P ∈ D, πP P with hc
  set g : 𝓞 K → ℂ := fun μ => gaussTr c (fun z => q2 D ((∏ P ∈ T, πP P) * z)) μ with hg
  have hgeq : ∀ μ, g μ = q2 D (∏ P ∈ T, πP P) * gaussTr c (q2 D) μ := fun μ => by
    rw [hg]; simp only [q2_mul]
    exact gaussTr_const_mul c (prod_πP_ne_zero D) _ (q2 D) μ
  have hgle : ∀ μ, ‖g μ‖ ≤ Real.sqrt (nI D) := fun μ => by
    rw [hgeq, norm_mul, ← absNorm_span_prod_πP D, ← norm_σO_eq_sqrt]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_q2_le D _)).trans (norm_gaussTr_q2_le D μ)
  have hg0 : ‖g 0‖ ≤ ‖gaussTr c (q2 D) 0‖ := by
    rw [hgeq, norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (norm_q2_le D _)
  have hT := norm_tsum_dualG_le hH ha hb hB g hgle
  have hpos : 0 < Real.sqrt 3 * nI D * nI T := by positivity
  have hk : 2 * H / (Real.sqrt 3 * nI D * nI T) ≤ 2 * H := by
    rw [div_le_iff₀ hpos]
    have h1 : 1 ≤ nI D := one_le_nI D
    have h2 : 1 ≤ nI T := one_le_nI T
    have : 1 ≤ Real.sqrt 3 * nI D * nI T := by
      have : (1 : ℝ) ≤ Real.sqrt 3 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ Real.sqrt 3 * nI D * nI T := by gcongr
    nlinarith
  have hcoef : 2 * H / (Real.sqrt 3 * nI D * nI T) * (49 * (3 * RΦ ^ 2 * (nI D * nI T) / (4 * H)) *
      Real.sqrt (nI D) * B) ≤ 49 * RΦ ^ 2 * B * Real.sqrt (nI D) := by
    have e : 2 * H / (Real.sqrt 3 * nI D * nI T) * (49 * (3 * RΦ ^ 2 * (nI D * nI T) / (4 * H)) *
        Real.sqrt (nI D) * B) = (3 / (2 * Real.sqrt 3)) * (49 * RΦ ^ 2 * B * Real.sqrt (nI D)) := by
      field_simp
      ring
    rw [e]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [div_le_one (by positivity)]
    linarith
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc 2 * H / (Real.sqrt 3 * nI D * nI T) *
        ‖∑' μ : 𝓞 K, g μ * dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
          (3 * nI D * nI T)))‖
      ≤ 2 * H / (Real.sqrt 3 * nI D * nI T) *
          (‖g 0‖ * B + 49 * (3 * RΦ ^ 2 * (nI D * nI T) / (4 * H)) * Real.sqrt (nI D) * B) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 2 * H / (Real.sqrt 3 * nI D * nI T) * (‖g 0‖ * B) +
          2 * H / (Real.sqrt 3 * nI D * nI T) *
            (49 * (3 * RΦ ^ 2 * (nI D * nI T) / (4 * H)) * Real.sqrt (nI D) * B) := by ring
    _ ≤ 2 * H * (‖gaussTr c (q2 D) 0‖ * B) + 49 * RΦ ^ 2 * B * Real.sqrt (nI D) := by
        refine add_le_add ?_ hcoef
        exact mul_le_mul hk (mul_le_mul_of_nonneg_right hg0 hB0) (by positivity) (by positivity)
    _ = 2 * H * ‖gaussTr c (q2 D) 0‖ * B + 49 * RΦ ^ 2 * B * Real.sqrt (nI D) := by ring

open Classical in
/-- **The pair sum bound**: with `D = A₁ △ A₂` and `c = ∏_{P∈D} π_P`,
`|S(A₁, A₂)| ≤ 2^{|A₁∩A₂|}·(2H·|G_c(ρ_D, 0)|·B + 49·R_Φ²·B·√N(c))`. -/
theorem norm_pS_le {H : ℝ} (hH : 0 < H) {B : ℝ} (hB : ∀ ρ, ‖dualG ρ‖ ≤ B) (A1 A2 : Finset Pr) :
    ‖pS H A1 A2‖ ≤ 2 ^ (A1 ∩ A2).card *
      (2 * H * ‖gaussTr (∏ P ∈ (A1 \ A2) ∪ (A2 \ A1), πP P) (q2 ((A1 \ A2) ∪ (A2 \ A1))) 0‖ * B +
        49 * RΦ ^ 2 * B * Real.sqrt (nI ((A1 \ A2) ∪ (A2 \ A1)))) := by
  set D := (A1 \ A2) ∪ (A2 \ A1) with hD
  have hpo := poisson_excl_Phi H hH (∏ P ∈ D, πP P) (prod_πP_ne_zero D) (q2 D) (q2_periodic D)
    (A1 ∩ A2) πP (fun P _ => ne_zero_of_maximal (πP P)) (hcopPr _)
  have hL : pS H A1 A2 = ∑' u : 𝓞 K, (if ∀ i ∈ A1 ∩ A2, ¬ πP i ∣ u then q2 D u else 0) *
      Majorant.Phi (σO u / (Real.sqrt H : ℂ)) := by
    unfold pS
    refine tsum_congr fun u => ?_
    rw [q2_mul_q2]
  rw [hL, hpo]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ T ∈ (A1 ∩ A2).powerset, ‖(-1 : ℂ) ^ T.card *
        (((2 * H / (Real.sqrt 3 * (absNorm (span {∏ P ∈ D, πP P}) : ℝ) *
            (absNorm (span {∏ P ∈ T, πP P}) : ℝ)) : ℝ) : ℂ) *
          ∑' μ : 𝓞 K, gaussTr (∏ P ∈ D, πP P) (fun z => q2 D ((∏ P ∈ T, πP P) * z)) μ *
            dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
              (3 * (absNorm (span {∏ P ∈ D, πP P}) : ℝ) *
                (absNorm (span {∏ P ∈ T, πP P}) : ℝ)))))‖
      ≤ ∑ _T ∈ (A1 ∩ A2).powerset, (2 * H * ‖gaussTr (∏ P ∈ D, πP P) (q2 D) 0‖ * B +
          49 * RΦ ^ 2 * B * Real.sqrt (nI D)) :=
        Finset.sum_le_sum fun T _ => norm_pS_term_le hH hB D T
    _ = _ := by rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat]

open Classical in
/-- **Off the diagonal**: for `A₁ ≠ A₂`, `|S(A₁, A₂)| ≤ 2^{|A₁∩A₂|}·49·R_Φ²·B·√N(A₁ △ A₂)`. -/
theorem norm_pS_off {H : ℝ} (hH : 0 < H) {B : ℝ} (hB : ∀ ρ, ‖dualG ρ‖ ≤ B) {A1 A2 : Finset Pr}
    (hne : A1 ≠ A2) :
    ‖pS H A1 A2‖ ≤ 2 ^ (A1 ∩ A2).card * (49 * RΦ ^ 2 * B * Real.sqrt (nI ((A1 \ A2) ∪ (A2 \ A1)))) := by
  have hD : ((A1 \ A2) ∪ (A2 \ A1)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset,
      Finset.sdiff_eq_empty_iff_subset] at h
    exact hne (Finset.Subset.antisymm h.1 h.2)
  have h := norm_pS_le hH hB A1 A2
  rwa [gaussTr_q2_zero hD, norm_zero, mul_zero, zero_mul, zero_add] at h

open Classical in
/-- **On the diagonal**: `|S(A, A)| ≤ 2^{|A|}·(2H + 49·R_Φ²)·B`. -/
theorem norm_pS_diag {H : ℝ} (hH : 0 < H) {B : ℝ} (hB : ∀ ρ, ‖dualG ρ‖ ≤ B) (A : Finset Pr) :
    ‖pS H A A‖ ≤ 2 ^ A.card * ((2 * H + 49 * RΦ ^ 2) * B) := by
  have h := norm_pS_le hH hB A A
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  simp only [Finset.sdiff_self, Finset.union_empty, Finset.inter_self] at h
  have h1 : ‖gaussTr (∏ P ∈ (∅ : Finset Pr), πP P) (q2 ∅) 0‖ ≤ 1 := by
    refine (norm_gaussTr_q2_le ∅ 0).trans ?_
    rw [Finset.prod_empty, norm_σO_eq_sqrt, Ideal.span_singleton_one, absNorm_top, Nat.cast_one,
      Real.sqrt_one]
  rw [nI_empty, Real.sqrt_one, mul_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have : 2 * H * ‖gaussTr (∏ P ∈ (∅ : Finset Pr), πP P) (q2 ∅) 0‖ * B ≤ 2 * H * B := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * H)
    nlinarith
  nlinarith

theorem sym2_eq_q2 {k : 𝓞 K} (hk : QAdm k) (u : 𝓞 K) :
    sym2 u (span {k}) = q2 (primeSet (span {k})) u := by
  conv_lhs => rw [(eq_prod_of_adm hk).2]
  rw [sym2_idl]; rfl

theorem eq_of_primeSet_eq {k k' : 𝓞 K} (hk : QAdm k) (hk' : QAdm k')
    (h : primeSet (span {k}) = primeSet (span {k'})) : k = k' := by
  rw [(eq_prod_of_adm hk).1, (eq_prod_of_adm hk').1, h]

theorem nI_primeSet {k : 𝓞 K} (hk : QAdm k) :
    nI (primeSet (span {k})) = (absNorm (span {k}) : ℝ) := by
  rw [nI, ← (eq_prod_of_adm hk).2]

/-- **The mean square as a double sum of pair sums** over admissible moduli. -/
theorem majorant_expand_q2 (H : ℝ) (hH : 0 < H) (Ks : Finset (𝓞 K)) (b : 𝓞 K → ℂ)
    (hK : ∀ k ∈ Ks, QAdm k) :
    ∑' u : 𝓞 K, (∑ k ∈ Ks, b k * sym2 u (span {k})) *
        conj (∑ k ∈ Ks, b k * sym2 u (span {k})) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ k1 ∈ Ks, ∑ k2 ∈ Ks, b k1 * conj (b k2) *
        pS H (primeSet (span {k1})) (primeSet (span {k2})) := by
  have hexp : ∀ u : 𝓞 K, (∑ k ∈ Ks, b k * sym2 u (span {k})) *
      conj (∑ k ∈ Ks, b k * sym2 u (span {k})) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ k1 ∈ Ks, ∑ k2 ∈ Ks, b k1 * conj (b k2) *
        (q2 (primeSet (span {k1})) u * q2 (primeSet (span {k2})) u *
          Majorant.Phi (σO u / (Real.sqrt H : ℂ))) := by
    intro u
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k1 hk1 => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k2 hk2 => ?_
    rw [map_mul, sym2_eq_q2 (hK k1 hk1), sym2_eq_q2 (hK k2 hk2), conj_q2]
    ring
  rw [tsum_congr hexp]
  have hs : ∀ k1 k2 : 𝓞 K, Summable fun u : 𝓞 K => b k1 * conj (b k2) *
      (q2 (primeSet (span {k1})) u * q2 (primeSet (span {k2})) u *
        Majorant.Phi (σO u / (Real.sqrt H : ℂ))) := by
    intro k1 k2
    have hb : ∀ u, ‖q2 (primeSet (span {k1})) u * q2 (primeSet (span {k2})) u‖ ≤ 1 := fun u => by
      rw [norm_mul]
      calc ‖q2 (primeSet (span {k1})) u‖ * ‖q2 (primeSet (span {k2})) u‖ ≤ 1 * 1 :=
            mul_le_mul (norm_q2_le _ u) (norm_q2_le _ u) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact (summable_mul_Phi H hH _ hb).mul_left _
  rw [Summable.tsum_finsetSum fun k1 _ => summable_sum fun k2 _ => hs k1 k2]
  refine Finset.sum_congr rfl fun k1 _ => ?_
  rw [Summable.tsum_finsetSum fun k2 _ => hs k1 k2]
  refine Finset.sum_congr rfl fun k2 _ => ?_
  rw [tsum_mul_left]; rfl

theorem nI_sdiff_union_le (A1 A2 : Finset Pr) :
    nI ((A1 \ A2) ∪ (A2 \ A1)) ≤ nI A1 * nI A2 := by
  classical
  rw [nI_union disjoint_sdiff_sdiff]
  have h1 : nI (A1 \ A2) ≤ nI A1 := by
    unfold nI; exact_mod_cast absNorm_idl_mono Finset.sdiff_subset
  have h2 : nI (A2 \ A1) ≤ nI A2 := by
    unfold nI; exact_mod_cast absNorm_idl_mono Finset.sdiff_subset
  exact mul_le_mul h1 h2 (nI_pos _).le (nI_pos _).le

open Classical in
/-- **The pair sums for admissible moduli**: `|S(k₁, k₂)| ≤ [k₁ = k₂]·D + E`, with
`D = C₄M^δ·(2 + 49R_Φ²)·B·H` and `E = C₄M^δ·49R_Φ²·B·M`, where `4^{ω(k)} ≤ C₄N(k)^δ`. -/
theorem norm_pS_adm_le {H M δ B C4 : ℝ} (hH : 1 ≤ H) (hδ : 0 < δ) (hB : ∀ ρ, ‖dualG ρ‖ ≤ B)
    (hC4 : ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ C4 * nI b ^ δ) {k1 k2 : 𝓞 K}
    (hk1 : QAdm k1 ∧ (absNorm (span {k1}) : ℝ) ≤ M) (hk2 : QAdm k2 ∧ (absNorm (span {k2}) : ℝ) ≤ M) :
    ‖pS H (primeSet (span {k1})) (primeSet (span {k2}))‖ ≤
      (if k1 = k2 then C4 * M ^ δ * (2 + 49 * RΦ ^ 2) * B * H else 0) +
        C4 * M ^ δ * (49 * RΦ ^ 2) * B * M := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hR := RΦ_pos
  set A1 := primeSet (span {k1}) with hA1
  set A2 := primeSet (span {k2}) with hA2
  have hM1 : nI A1 ≤ M := by rw [hA1, nI_primeSet hk1.1]; exact hk1.2
  have hM2 : nI A2 ≤ M := by rw [hA2, nI_primeSet hk2.1]; exact hk2.2
  have hMpos : 1 ≤ M := (one_le_nI A1).trans hM1
  have hpow : ∀ A : Finset Pr, nI A ≤ M → (2 : ℝ) ^ A.card ≤ C4 * M ^ δ := by
    intro A hA
    calc (2 : ℝ) ^ A.card ≤ (4 : ℝ) ^ A.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ C4 * nI A ^ δ := hC4 A
      _ ≤ C4 * M ^ δ := by
          have hC40 : 0 ≤ C4 := by
            have h := hC4 ∅
            rw [Finset.card_empty, pow_zero, nI_empty, Real.one_rpow, mul_one] at h
            linarith
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (nI_pos A).le hA hδ.le) hC40
  have hE0 : 0 ≤ C4 * M ^ δ * (49 * RΦ ^ 2) * B * M := by
    have := hpow ∅ (by rw [nI_empty]; exact hMpos)
    have h0 : 0 ≤ C4 * M ^ δ := le_trans (by positivity) this
    have : 0 ≤ (49 * RΦ ^ 2) * B * M := by positivity
    nlinarith
  by_cases heq : k1 = k2
  · subst heq
    rw [ite_eq_left rfl]
    refine le_trans ?_ (le_add_of_nonneg_right hE0)
    refine (norm_pS_diag (by linarith) hB A1).trans ?_
    have h2 := hpow A1 hM1
    have hb : (2 * H + 49 * RΦ ^ 2) * B ≤ (2 + 49 * RΦ ^ 2) * B * H := by
      have : 2 * H + 49 * RΦ ^ 2 ≤ (2 + 49 * RΦ ^ 2) * H := by nlinarith
      nlinarith
    calc (2 : ℝ) ^ A1.card * ((2 * H + 49 * RΦ ^ 2) * B)
        ≤ C4 * M ^ δ * ((2 + 49 * RΦ ^ 2) * B * H) :=
          mul_le_mul h2 hb (by positivity) (le_trans (by positivity) h2)
      _ = C4 * M ^ δ * (2 + 49 * RΦ ^ 2) * B * H := by ring
  · rw [ite_eq_right heq, zero_add]
    have hne : A1 ≠ A2 := fun h => heq (eq_of_primeSet_eq hk1.1 hk2.1 h)
    refine (norm_pS_off (by linarith) hB hne).trans ?_
    have h2 : (2 : ℝ) ^ (A1 ∩ A2).card ≤ C4 * M ^ δ :=
      (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card Finset.inter_subset_left)).trans
        (hpow A1 hM1)
    have hs : Real.sqrt (nI ((A1 \ A2) ∪ (A2 \ A1))) ≤ M := by
      rw [show M = Real.sqrt (M ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      refine Real.sqrt_le_sqrt ((nI_sdiff_union_le A1 A2).trans ?_)
      rw [sq]; exact mul_le_mul hM1 hM2 (nI_pos _).le (by linarith)
    calc (2 : ℝ) ^ (A1 ∩ A2).card * (49 * RΦ ^ 2 * B * Real.sqrt (nI ((A1 \ A2) ∪ (A2 \ A1))))
        ≤ C4 * M ^ δ * (49 * RΦ ^ 2 * B * M) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
            (le_trans (by positivity) h2)
      _ = C4 * M ^ δ * (49 * RΦ ^ 2) * B * M := by ring

/-- **The transposed base bound** (Heath-Brown's `B(M, N) ≪ (MN)^ε(M + N²)`, transposed): for
admissible moduli `k` of norm at most `M` and any arguments `u` of norm at most `H`,
`Σ_u |Σ_k b(k)(u/k)₂|² ≤ C·M^δ·(H + M²)·Σ_k |b(k)|²`. -/
theorem dual_q2_bound {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ M H : ℝ, 1 ≤ M → 1 ≤ H →
    ∀ (Ks Us : Finset (𝓞 K)) (b : 𝓞 K → ℂ),
      (∀ k ∈ Ks, QAdm k ∧ (absNorm (span {k}) : ℝ) ≤ M) →
      (∀ u ∈ Us, (absNorm (span {u}) : ℝ) ≤ H) →
      ∑ u ∈ Us, ‖∑ k ∈ Ks, b k * sym2 u (span {k})‖ ^ 2 ≤
        C * M ^ δ * (H + M ^ 2) * ∑ k ∈ Ks, ‖b k‖ ^ 2 := by
  classical
  obtain ⟨B, hB0, hB⟩ := exists_norm_dualG_le
  obtain ⟨C4, hC4pos, hC4⟩ := four_pow_card_le hδ
  have hR := RΦ_pos
  have hk0 := kappa_pos
  refine ⟨C4 * B * ((2 + 49 * RΦ ^ 2) + 49 * RΦ ^ 2 * (2 * kappa + 5)), by positivity,
    fun M H hM hH Ks Us b hK hU => ?_⟩
  set g : 𝓞 K → ℂ := fun u => ∑ k ∈ Ks, b k * sym2 u (span {k}) with hg
  have hgb : ∀ u, ‖g u‖ ≤ ∑ k ∈ Ks, ‖b k‖ := fun u => by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_sym2_le _ _)
  have h1 := sum_sq_le_majorant H (by linarith) g hgb Us hU
  rw [hg, majorant_expand_q2 H (by linarith) Ks b fun k hk => (hK k hk).1] at h1
  set Dg : ℝ := C4 * M ^ δ * (2 + 49 * RΦ ^ 2) * B * H with hDg
  set E : ℝ := C4 * M ^ δ * (49 * RΦ ^ 2) * B * M with hE
  have hMδ : 0 ≤ M ^ δ := Real.rpow_nonneg (by linarith) δ
  have hDg0 : 0 ≤ Dg := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hpair : ∀ k1 ∈ Ks, ∀ k2 ∈ Ks, ‖pS H (primeSet (span {k1})) (primeSet (span {k2}))‖ ≤
      (if k1 = k2 then Dg else 0) + E := fun k1 hk1 k2 hk2 =>
    norm_pS_adm_le hH hδ hB hC4 (hK k1 hk1) (hK k2 hk2)
  have hcard : (Ks.card : ℝ) ≤ (2 * kappa + 5) * M :=
    (card_adm_le hK).trans (idealCount_le hM)
  have hS0 : 0 ≤ ∑ k ∈ Ks, ‖b k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hCS : (∑ k ∈ Ks, ‖b k‖) ^ 2 ≤ (Ks.card : ℝ) * ∑ k ∈ Ks, ‖b k‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc ∑ u ∈ Us, ‖∑ k ∈ Ks, b k * sym2 u (span {k})‖ ^ 2
      ≤ (∑ k1 ∈ Ks, ∑ k2 ∈ Ks, b k1 * conj (b k2) *
          pS H (primeSet (span {k1})) (primeSet (span {k2}))).re := h1
    _ ≤ ‖∑ k1 ∈ Ks, ∑ k2 ∈ Ks, b k1 * conj (b k2) *
          pS H (primeSet (span {k1})) (primeSet (span {k2}))‖ := Complex.re_le_norm _
    _ ≤ ∑ k1 ∈ Ks, ∑ k2 ∈ Ks, ‖b k1‖ * ‖b k2‖ * ((if k1 = k2 then Dg else 0) + E) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k1 hk1 => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k2 hk2 => ?_)
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_left (hpair k1 hk1 k2 hk2) (by positivity)
    _ = Dg * ∑ k ∈ Ks, ‖b k‖ ^ 2 + E * (∑ k ∈ Ks, ‖b k‖) ^ 2 := by
        have e : ∀ k1 ∈ Ks, ∑ k2 ∈ Ks, ‖b k1‖ * ‖b k2‖ * ((if k1 = k2 then Dg else 0) + E) =
            Dg * ‖b k1‖ ^ 2 + E * (‖b k1‖ * ∑ k2 ∈ Ks, ‖b k2‖) := by
          intro k1 hk1
          have e1 : ∀ k2 ∈ Ks, ‖b k1‖ * ‖b k2‖ * ((if k1 = k2 then Dg else 0) + E) =
              (if k1 = k2 then Dg * ‖b k1‖ ^ 2 else 0) + E * (‖b k1‖ * ‖b k2‖) := by
            intro k2 _
            split_ifs with h
            · subst h; ring
            · ring
          rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_ite_eq Ks k1,
            ite_eq_left hk1, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.sum_mul, sq (∑ k ∈ Ks, ‖b k‖)]
    _ ≤ Dg * ∑ k ∈ Ks, ‖b k‖ ^ 2 + E * ((2 * kappa + 5) * M * ∑ k ∈ Ks, ‖b k‖ ^ 2) := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (hCS.trans ?_) hE0)
        exact mul_le_mul_of_nonneg_right hcard hS0
    _ ≤ C4 * B * ((2 + 49 * RΦ ^ 2) + 49 * RΦ ^ 2 * (2 * kappa + 5)) * M ^ δ * (H + M ^ 2) *
          ∑ k ∈ Ks, ‖b k‖ ^ 2 := by
        rw [hDg, hE]
        have hX : 0 ≤ C4 * M ^ δ * B * ∑ k ∈ Ks, ‖b k‖ ^ 2 := by positivity
        have key : (2 + 49 * RΦ ^ 2) * H + 49 * RΦ ^ 2 * M * ((2 * kappa + 5) * M) ≤
            ((2 + 49 * RΦ ^ 2) + 49 * RΦ ^ 2 * (2 * kappa + 5)) * (H + M ^ 2) := by
          have hR2 : 0 ≤ 49 * RΦ ^ 2 := by positivity
          have hk5 : 0 ≤ 2 * kappa + 5 := by linarith
          nlinarith [mul_nonneg hR2 hk5, sq_nonneg M, mul_nonneg (mul_nonneg hR2 hk5) (sq_nonneg M),
            mul_nonneg (by positivity : (0 : ℝ) ≤ 2 + 49 * RΦ ^ 2) (sq_nonneg M),
            mul_nonneg (mul_nonneg hR2 hk5) (by linarith : (0 : ℝ) ≤ H)]
        calc C4 * M ^ δ * (2 + 49 * RΦ ^ 2) * B * H * ∑ k ∈ Ks, ‖b k‖ ^ 2 +
              C4 * M ^ δ * (49 * RΦ ^ 2) * B * M * ((2 * kappa + 5) * M * ∑ k ∈ Ks, ‖b k‖ ^ 2)
            = (C4 * M ^ δ * B * ∑ k ∈ Ks, ‖b k‖ ^ 2) *
                ((2 + 49 * RΦ ^ 2) * H + 49 * RΦ ^ 2 * M * ((2 * kappa + 5) * M)) := by ring
          _ ≤ (C4 * M ^ δ * B * ∑ k ∈ Ks, ‖b k‖ ^ 2) *
                (((2 + 49 * RΦ ^ 2) + 49 * RΦ ^ 2 * (2 * kappa + 5)) * (H + M ^ 2)) :=
              mul_le_mul_of_nonneg_left key hX
          _ = _ := by ring

/-- **The base bound with the moduli as rows**: duality turns the transposed bound into
`QBound M N (C·M^δ·(N + M²))`. -/
theorem qBound_base {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → QBound M N (C * M ^ δ * (N + M ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := dual_q2_bound hδ
  refine ⟨C, hC0, fun M N hM hN Ks Ns a hK hNs => ?_⟩
  have hΔ : 0 ≤ C * M ^ δ * (N + M ^ 2) :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) δ)) (by positivity)
  exact duality Ks Ns (fun k n => sym2 n (span {k})) hΔ
    (fun b => hC M N hM hN Ks Ns b hK fun n hn => (hNs n hn).2) a

/-- **The base case `(E_2)`** (Heath-Brown's `B(M,N) ≪ (MN)^ε(M + N²)`): `QExp 2`, from the base
bound with rows and columns exchanged and the symmetry of the norm. -/
theorem qExp_two : QExp 2 := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := qBound_base hε
  set c4 : ℝ := (absNorm (span {(4 : 𝓞 K)}) : ℝ) with hc4
  have hc40 : 0 ≤ c4 := Nat.cast_nonneg _
  refine ⟨c4 * C, mul_nonneg hc40 hC0, fun M N hM hN => ?_⟩
  have h1 := hC N M hN hM
  have hΔ : 0 ≤ C * N ^ ε * (M + N ^ 2) :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) ε)) (by positivity)
  refine (QBound.symm hΔ h1).mono le_rfl le_rfl ?_
  rw [Real.rpow_two]
  have hNε : N ^ ε ≤ (M * N) ^ ε :=
    Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hM) hε.le
  have hp : 0 ≤ M + N ^ 2 := by positivity
  calc c4 * (C * N ^ ε * (M + N ^ 2)) = c4 * C * (M + N ^ 2) * N ^ ε := by ring
    _ ≤ c4 * C * (M + N ^ 2) * (M * N) ^ ε :=
        mul_le_mul_of_nonneg_left hNε (mul_nonneg (mul_nonneg hc40 hC0) hp)
    _ = c4 * C * (M * N) ^ ε * (M + N ^ 2) := by ring

end Eis

end

#print axioms Eis.q2_mul_q2
#print axioms Eis.conj_q2
#print axioms Eis.norm_gaussTr_q2_le
#print axioms Eis.gaussTr_q2_zero
#print axioms Eis.exists_norm_dualG_le
#print axioms Eis.norm_tsum_dualG_le
#print axioms Eis.norm_pS_le
#print axioms Eis.norm_pS_off
#print axioms Eis.norm_pS_diag
#print axioms Eis.majorant_expand_q2
#print axioms Eis.norm_pS_adm_le
#print axioms Eis.dual_q2_bound
#print axioms Eis.qBound_base
#print axioms Eis.qExp_two
