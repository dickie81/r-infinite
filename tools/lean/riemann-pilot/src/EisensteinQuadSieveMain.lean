import EisensteinQuadSieveGamma

/-! # The quadratic large sieve, part 6b: the cancellation of the main terms (round 354)

S5e of round 312's plan, the second piece of S5e-6: the main terms of `Σ_3` (rows up to `K₁`, a
sum over `T ⊆ G`) and of `Σ_4` (rows up to `K`, prime to `G`) cancel except on the rows near `K₁`
and between `K₁` and `K`.

* **Splitting a squarefree row along `G`** (`tsum_sqf_split`, with `prod_πP_dvd_iff`,
  `πP_dvd_prod_mul_iff`, `sqf_prod_mul_iff`, `sum_powerset_part`): every squarefree `d` is
  `π_U·ℓ` for exactly one `U ⊆ G` and one squarefree `ℓ` prime to `G`, so a series supported on
  the squarefree rows is `Σ_{U⊆G} Σ_{ℓ sqf, (ℓ,G)=1} f(π_U·ℓ)`. The proof sorts the rows by their
  `G`-part (a partition of unity over `U ⊆ G`) and removes the divisibility by `π_U` with round
  332's `tsum_ite_dvd_eq`, so no division is taken.
* **The cancellation** (`main_cancel`): for `F` completely multiplicative with `F(π_P)² = N(P)⁻¹`
  on `G` and `K₁ ≤ K`, `S(Y) = Σ_{U⊆G}F(π_U)S_G(Y/N(U))` (`sqfS_split`) and
  `φ*(G) = (Σ_T(−1)^{|T|}F(π_T))(Σ_U F(π_U))` (`phiStar_eq`, from `(1 − x)(1 + x) = 1 − x²`), so
  `Σ_T(−1)^{|T|}F(π_T)·S(K₁) − φ*(G)·S_G(K)
    = −(Σ_T(−1)^{|T|}F(π_T))·Σ_U F(π_U)·Σ_{d sqf, (d,G)=1, K₁ < N(U)N(d), N(d) ≤ K} F(d)`.
* **The pair identity** (`pair_eq`): with `F_D(x) = ρ_D(x)/√N(x)` (`FD`; `FD_sq` for `P ∉ D`),
  rounds 350, 351 and 353 give, for `D ≠ ∅` disjoint from `G`, `ρ_D(−1) = 1`,
  `3R²N(D)N(G) ≤ 4MK₁` and `K₁ ≤ K`,
  `w·(Σ_3 − Σ_4) = −(2π/√3)J·φ*(D)·√M·(Σ_T(−1)^{|T|}F_D(π_T))·Σ_U F_D(π_U)·R_U + err₃ − err₄`.
-/

open Complex MeasureTheory Set NumberField Ideal
open scoped Classical

noncomputable section

namespace Eis

theorem prod_πP_dvd_iff (U : Finset Pr) (d : 𝓞 K) :
    (∏ P ∈ U, πP P) ∣ d ↔ ∀ P ∈ U, πP P ∣ d := by
  refine ⟨fun h P hP => (Finset.dvd_prod_of_mem _ hP).trans h, fun h => ?_⟩
  exact Finset.prod_dvd_of_coprime (fun i hi j hj hij => hcopPr U i hi j hj hij) h

theorem πP_dvd_prod_mul_iff {P : Pr} {U : Finset Pr} (hP : P ∉ U) (x : 𝓞 K) :
    πP P ∣ (∏ Q ∈ U, πP Q) * x ↔ πP P ∣ x := by
  rw [(prime_πP P).dvd_mul]
  have h : ¬ πP P ∣ ∏ Q ∈ U, πP Q := fun h => prod_not_mem hP (Ideal.mem_span_singleton.2 h)
  tauto

/-- `π_U·x` is squarefree iff `x` is and no prime of `U` divides `x`. -/
theorem sqf_prod_mul_iff (U : Finset Pr) (x : 𝓞 K) :
    Squarefree (span {(∏ P ∈ U, πP P) * x}) ↔ Squarefree (span {x}) ∧ ∀ P ∈ U, ¬ πP P ∣ x := by
  by_cases hx : x = 0
  · subst hx
    have h0 : ¬ Squarefree (span {(0 : 𝓞 K)}) := fun h =>
      h.ne_zero (Ideal.span_singleton_eq_bot.2 rfl)
    rw [mul_zero]
    exact ⟨fun h => absurd h h0, fun h => absurd h.1 h0⟩
  have hI : span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [← Ideal.span_singleton_mul_span_singleton, span_prod_πP, mul_comm, squarefree_mul_iff,
    isRelPrime_iff_primeSet hI (idl_coprime6 U) (idl_squarefree U)]
  have hps : primeSet (idl U) = U := by rw [← span_prod_πP]; exact primeSet_prod_πP U
  rw [hps]
  have hdvd : ∀ P : Pr, P.1 ∣ span {x} ↔ πP P ∣ x := fun P => by
    rw [Ideal.dvd_iff_le, ← (πP_spec P).2, Ideal.span_singleton_le_span_singleton]
  simp only [hdvd]
  have := idl_squarefree U
  tauto

/-- **The partition by the `G`-part**: exactly one `U ⊆ G` has `π_P ∣ d` for `P ∈ U` and
`π_P ∤ d` for `P ∈ G ∖ U`. -/
theorem sum_powerset_part (G : Finset Pr) (d : 𝓞 K) :
    ∑ U ∈ G.powerset, (if (∀ P ∈ U, πP P ∣ d) ∧ ∀ P ∈ G \ U, ¬ πP P ∣ d then (1 : ℂ) else 0) =
      1 := by
  rw [Finset.sum_eq_single (G.filter fun P => πP P ∣ d)]
  · refine ite_eq_left ⟨fun P hP => (Finset.mem_filter.1 hP).2, fun P hP h => ?_⟩
    rw [Finset.mem_sdiff, Finset.mem_filter] at hP
    exact hP.2 ⟨hP.1, h⟩
  · intro U hU hne
    refine ite_eq_right fun h => hne ?_
    ext P
    rw [Finset.mem_filter]
    constructor
    · intro hP; exact ⟨Finset.mem_powerset.1 hU hP, h.1 P hP⟩
    · rintro ⟨hPG, hPd⟩
      by_contra hPU
      exact h.2 P (Finset.mem_sdiff.2 ⟨hPG, hPU⟩) hPd
  · intro h; exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ _)) h

/-- **Splitting off the `G`-part of a squarefree row**: for `f` summable and supported on the
squarefree rows, `Σ_d f(d) = Σ_{U⊆G} Σ_{ℓ sqf, (ℓ,G)=1} f(π_U·ℓ)`. -/
theorem tsum_sqf_split (G : Finset Pr) (f : 𝓞 K → ℂ) (hf : Summable f)
    (hsupp : ∀ d, ¬ Squarefree (span {d}) → f d = 0) :
    ∑' d, f d = ∑ U ∈ G.powerset, ∑' ℓ, (if Squarefree (span {ℓ}) ∧ ∀ P ∈ G, ¬ πP P ∣ ℓ then
      f ((∏ P ∈ U, πP P) * ℓ) else 0) := by
  have h1 : ∀ d, f d = ∑ U ∈ G.powerset,
      (if (∀ P ∈ U, πP P ∣ d) ∧ ∀ P ∈ G \ U, ¬ πP P ∣ d then f d else 0) := by
    intro d
    calc f d = (∑ U ∈ G.powerset, (if (∀ P ∈ U, πP P ∣ d) ∧ ∀ P ∈ G \ U, ¬ πP P ∣ d then
          (1 : ℂ) else 0)) * f d := by rw [sum_powerset_part, one_mul]
      _ = _ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun U _ => by split_ifs <;> simp
  have hsU : ∀ U ∈ G.powerset, Summable fun d =>
      (if (∀ P ∈ U, πP P ∣ d) ∧ ∀ P ∈ G \ U, ¬ πP P ∣ d then f d else 0) := fun U _ =>
    Summable.of_norm_bounded hf.norm fun d => by
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
  rw [tsum_congr h1, Summable.tsum_finsetSum hsU]
  refine Finset.sum_congr rfl fun U hU => ?_
  have hUG := Finset.mem_powerset.1 hU
  have h2 : ∀ d, (if (∀ P ∈ U, πP P ∣ d) ∧ ∀ P ∈ G \ U, ¬ πP P ∣ d then f d else 0) =
      if (∏ P ∈ U, πP P) ∣ d then (if ∀ P ∈ G \ U, ¬ πP P ∣ d then f d else 0) else 0 := by
    intro d
    rw [prod_πP_dvd_iff]
    by_cases ha : ∀ P ∈ U, πP P ∣ d
    · by_cases hb : ∀ P ∈ G \ U, ¬ πP P ∣ d
      · rw [ite_eq_left ⟨ha, hb⟩, ite_eq_left ha, ite_eq_left hb]
      · rw [ite_eq_right fun h => hb h.2, ite_eq_left ha, ite_eq_right hb]
    · rw [ite_eq_right fun h => ha h.1, ite_eq_right ha]
  rw [tsum_congr h2, tsum_ite_dvd_eq _ (prod_πP_ne_zero U)]
  refine tsum_congr fun ℓ => ?_
  have hc1 : (∀ P ∈ G \ U, ¬ πP P ∣ (∏ Q ∈ U, πP Q) * ℓ) ↔ ∀ P ∈ G \ U, ¬ πP P ∣ ℓ := by
    refine forall₂_congr fun P hP => ?_
    rw [πP_dvd_prod_mul_iff (Finset.mem_sdiff.1 hP).2]
  have hc2 : (Squarefree (span {ℓ}) ∧ ∀ P ∈ G, ¬ πP P ∣ ℓ) ↔
      ((∀ P ∈ G \ U, ¬ πP P ∣ ℓ) ∧ Squarefree (span {(∏ Q ∈ U, πP Q) * ℓ})) := by
    rw [sqf_prod_mul_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun P hP => h2 P (Finset.mem_sdiff.1 hP).1, h1, fun P hP => h2 P (hUG hP)⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, fun P hP => ?_⟩
      by_cases hPU : P ∈ U
      · exact h3 P hPU
      · exact h1 P (Finset.mem_sdiff.2 ⟨hP, hPU⟩)
  by_cases hs : Squarefree (span {(∏ Q ∈ U, πP Q) * ℓ})
  · by_cases hcop : ∀ P ∈ G \ U, ¬ πP P ∣ ℓ
    · rw [ite_eq_left ((hc1).2 hcop), ite_eq_left (hc2.2 ⟨hcop, hs⟩)]
    · rw [ite_eq_right fun h => hcop (hc1.1 h), ite_eq_right fun h => hcop (hc2.1 h).1]
  · rw [hsupp _ hs]
    split_ifs <;> rfl

/-- The rows' sum `S(Y) = Σ_{d sqf, N(d) ≤ Y} F(d)`. -/
def sqfS (F : 𝓞 K → ℂ) (Y : ℝ) : ℂ :=
  ∑' d : 𝓞 K, if Squarefree (span {d}) ∧ (absNorm (span {d}) : ℝ) ≤ Y then F d else 0

/-- The rows' sum prime to `G` on a range, `Σ_{d sqf, (d,G)=1, Y₁ < c·N(d), N(d) ≤ Y₂} F(d)`. -/
def sqfR (F : 𝓞 K → ℂ) (G : Finset Pr) (c Y₁ Y₂ : ℝ) : ℂ :=
  ∑' d : 𝓞 K, if Squarefree (span {d}) ∧ (∀ P ∈ G, ¬ πP P ∣ d) ∧
    Y₁ < c * (absNorm (span {d}) : ℝ) ∧ (absNorm (span {d}) : ℝ) ≤ Y₂ then F d else 0

theorem summable_of_eltsLe {f : 𝓞 K → ℂ} (Y : ℝ)
    (h : ∀ d, Y < (absNorm (span {d}) : ℝ) → f d = 0) : Summable f :=
  summable_of_ne_finset_zero (s := eltsLe Y) fun d hd => h d (by
    rw [mem_eltsLe] at hd; linarith [not_le.1 hd])

theorem absNorm_prod_mul (U : Finset Pr) (x : 𝓞 K) :
    (absNorm (span {(∏ P ∈ U, πP P) * x}) : ℝ) = nI U * (absNorm (span {x}) : ℝ) := by
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul, absNorm_span_prod_πP]

theorem F_prod {F : 𝓞 K → ℂ} (hF1 : F 1 = 1) (hFmul : ∀ x y, F (x * y) = F x * F y)
    (T : Finset Pr) : F (∏ P ∈ T, πP P) = ∏ P ∈ T, F (πP P) := by
  induction T using Finset.induction_on with
  | empty => simp [hF1]
  | insert P T hPT ih => rw [Finset.prod_insert hPT, Finset.prod_insert hPT, hFmul, ih]

/-- **Splitting `S(Y)` along `G`**: `S(Y) = Σ_{U⊆G} F(π_U)·S_G(Y/N(U))`. -/
theorem sqfS_split {F : 𝓞 K → ℂ} (hFmul : ∀ x y, F (x * y) = F x * F y) (G : Finset Pr)
    (Y : ℝ) :
    sqfS F Y = ∑ U ∈ G.powerset, F (∏ P ∈ U, πP P) *
      ∑' d : 𝓞 K, (if Squarefree (span {d}) ∧ (∀ P ∈ G, ¬ πP P ∣ d) ∧
        (absNorm (span {d}) : ℝ) ≤ Y / nI U then F d else 0) := by
  set f : 𝓞 K → ℂ := fun d =>
    if Squarefree (span {d}) ∧ (absNorm (span {d}) : ℝ) ≤ Y then F d else 0 with hf
  have hfs : Summable f := summable_of_eltsLe Y fun d hd => by
    simp only [hf]; exact ite_eq_right fun h => absurd h.2 (not_le.2 hd)
  have hsupp : ∀ d, ¬ Squarefree (span {d}) → f d = 0 := fun d hd => by
    simp only [hf]; exact ite_eq_right fun h => hd h.1
  unfold sqfS
  show ∑' d, f d = _
  rw [tsum_sqf_split G f hfs hsupp]
  refine Finset.sum_congr rfl fun U hU => ?_
  have hUG := Finset.mem_powerset.1 hU
  rw [← tsum_mul_left]
  refine tsum_congr fun ℓ => ?_
  have hnU := nI_pos U
  by_cases h1 : Squarefree (span {ℓ}) ∧ ∀ P ∈ G, ¬ πP P ∣ ℓ
  · have hs : Squarefree (span {(∏ P ∈ U, πP P) * ℓ}) :=
      (sqf_prod_mul_iff U ℓ).2 ⟨h1.1, fun P hP => h1.2 P (hUG hP)⟩
    simp only [hf, hs, true_and, absNorm_prod_mul]
    rw [ite_eq_left h1, hFmul]
    by_cases h2 : nI U * (absNorm (span {ℓ}) : ℝ) ≤ Y
    · rw [ite_eq_left h2, ite_eq_left ⟨h1.1, h1.2, by rw [le_div_iff₀ hnU]; linarith⟩]
    · rw [ite_eq_right h2, ite_eq_right fun h => h2 (by
        have := h.2.2; rw [le_div_iff₀ hnU] at this; linarith), mul_zero]
  · rw [ite_eq_right h1, ite_eq_right fun h => h1 ⟨h.1, h.2.1⟩, mul_zero]

/-- **`φ*(G)` as two sums over `G`**: with `F(π_P)² = N(P)⁻¹`,
`∏_{Q∈G}(1 − N(Q)⁻¹) = (Σ_{T⊆G}(−1)^{|T|}F(π_T))·(Σ_{U⊆G}F(π_U))`. -/
theorem phiStar_eq {F : 𝓞 K → ℂ} (hF1 : F 1 = 1) (hFmul : ∀ x y, F (x * y) = F x * F y)
    {G : Finset Pr} (hF2 : ∀ P ∈ G, F (πP P) ^ 2 = (((absNorm P.1 : ℝ) : ℂ))⁻¹) :
    ∏ Q ∈ G, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹) =
      (∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * F (∏ P ∈ T, πP P)) *
        ∑ U ∈ G.powerset, F (∏ P ∈ U, πP P) := by
  simp_rw [F_prod hF1 hFmul]
  rw [sum_powerset_neg_prod G (fun P => F (πP P)), ← Finset.prod_one_add, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP => ?_
  rw [← hF2 P hP]
  ring

/-- **The cancellation of the main terms**: for `F` completely multiplicative with
`F(π_P)² = N(P)⁻¹` on `G` and `K₁ ≤ K`,
`Σ_{T⊆G}(−1)^{|T|}F(π_T)·S(K₁) − φ*(G)·S_G(K)
  = −Σ_{T⊆G}Σ_{U⊆G}(−1)^{|T|}F(π_T)F(π_U)·Σ_{d sqf, (d,G)=1, K₁ < N(U)N(d) ≤ N(U)K} F(d)`:
only the rows near `K₁` and between `K₁` and `K` survive. -/
theorem main_cancel {F : 𝓞 K → ℂ} (hF1 : F 1 = 1) (hFmul : ∀ x y, F (x * y) = F x * F y)
    {G : Finset Pr} (hF2 : ∀ P ∈ G, F (πP P) ^ 2 = (((absNorm P.1 : ℝ) : ℂ))⁻¹)
    {K₁ Kt : ℝ} (hK : K₁ ≤ Kt) :
    (∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * F (∏ P ∈ T, πP P)) * sqfS F K₁ -
        (∏ Q ∈ G, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)) *
          ∑' d : 𝓞 K, (if Squarefree (span {d}) ∧ (∀ P ∈ G, ¬ πP P ∣ d) ∧
            (absNorm (span {d}) : ℝ) ≤ Kt then F d else 0) =
      -((∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * F (∏ P ∈ T, πP P)) *
        ∑ U ∈ G.powerset, F (∏ P ∈ U, πP P) * sqfR F G (nI U) K₁ Kt) := by
  rw [sqfS_split hFmul G K₁, phiStar_eq hF1 hFmul hF2]
  set A : ℂ := ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * F (∏ P ∈ T, πP P) with hA
  set SGK : ℂ := ∑' d : 𝓞 K, (if Squarefree (span {d}) ∧ (∀ P ∈ G, ¬ πP P ∣ d) ∧
    (absNorm (span {d}) : ℝ) ≤ Kt then F d else 0) with hSGK
  have hB : (∑ U ∈ G.powerset, F (∏ P ∈ U, πP P)) * SGK =
      ∑ U ∈ G.powerset, F (∏ P ∈ U, πP P) * SGK := Finset.sum_mul _ _ _
  rw [mul_assoc A, hB, ← mul_sub, ← Finset.sum_sub_distrib, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun U _ => ?_
  have hnU := nI_pos U
  have hnU1 := one_le_nI U
  have hs : ∀ Y : ℝ, Summable fun d : 𝓞 K => (if Squarefree (span {d}) ∧
      (∀ P ∈ G, ¬ πP P ∣ d) ∧ (absNorm (span {d}) : ℝ) ≤ Y then F d else 0) := fun Y =>
    summable_of_eltsLe Y fun d hd => ite_eq_right fun h => absurd h.2.2 (not_le.2 hd)
  have hs' : Summable fun d : 𝓞 K => (if Squarefree (span {d}) ∧
      (∀ P ∈ G, ¬ πP P ∣ d) ∧ (absNorm (span {d}) : ℝ) ≤ K₁ / nI U then F d else 0) := hs _
  rw [← mul_sub, ← mul_neg, ← hs'.tsum_sub (hs Kt), sqfR, ← tsum_neg]
  congr 1
  refine tsum_congr fun d => ?_
  have hN0 : (0 : ℝ) ≤ absNorm (span {d}) := Nat.cast_nonneg _
  by_cases h1 : Squarefree (span {d}) ∧ ∀ P ∈ G, ¬ πP P ∣ d
  · by_cases h2 : (absNorm (span {d}) : ℝ) ≤ K₁ / nI U
    · have h2' : nI U * (absNorm (span {d}) : ℝ) ≤ K₁ := by rwa [le_div_iff₀ hnU, mul_comm] at h2
      have h3 : (absNorm (span {d}) : ℝ) ≤ Kt := by nlinarith
      rw [ite_eq_left ⟨h1.1, h1.2, h2⟩, ite_eq_left ⟨h1.1, h1.2, h3⟩,
        ite_eq_right fun h => absurd h.2.2.1 (not_lt.2 h2'), sub_self, neg_zero]
    · have h2' : K₁ < nI U * (absNorm (span {d}) : ℝ) := by
        rw [le_div_iff₀ hnU, mul_comm] at h2; exact not_le.1 h2
      rw [ite_eq_right fun h => h2 h.2.2, zero_sub]
      by_cases h3 : (absNorm (span {d}) : ℝ) ≤ Kt
      · rw [ite_eq_left ⟨h1.1, h1.2, h3⟩, ite_eq_left ⟨h1.1, h1.2, h2', h3⟩]
      · rw [ite_eq_right fun h => h3 h.2.2, ite_eq_right fun h => h3 h.2.2.2, neg_zero]
  · rw [ite_eq_right fun h => h1 ⟨h.1, h.2.1⟩, ite_eq_right fun h => h1 ⟨h.1, h.2.1⟩,
      ite_eq_right fun h => h1 ⟨h.1, h.2.1⟩, sub_zero, neg_zero]

/-- `F_D(x) = ρ_D(x)/√N(x)`, completely multiplicative. -/
def FD (D : Finset Pr) (x : 𝓞 K) : ℂ :=
  q2 D x * (((Real.sqrt (absNorm (span {x}) : ℝ))⁻¹ : ℝ) : ℂ)

theorem FD_one (D : Finset Pr) : FD D 1 = 1 := by
  simp [FD, q2_one]

theorem FD_mul (D : Finset Pr) (x y : 𝓞 K) : FD D (x * y) = FD D x * FD D y := by
  unfold FD
  rw [q2_mul, ← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]
  push_cast
  ring

theorem q2_πP_sq {D : Finset Pr} {P : Pr} (hP : P ∉ D) : q2 D (πP P) ^ 2 = 1 := by
  rw [sq, ← q2_mul, ← sq, q2_sq]
  refine ite_eq_left fun Q hQ h => hP ?_
  rw [← πP_dvd_πP h]; exact hQ

theorem FD_sq {D : Finset Pr} {P : Pr} (hP : P ∉ D) :
    FD D (πP P) ^ 2 = (((absNorm P.1 : ℝ) : ℂ))⁻¹ := by
  unfold FD
  rw [mul_pow, q2_πP_sq hP, one_mul, (πP_spec P).2]
  have h0 : (0 : ℝ) ≤ absNorm P.1 := Nat.cast_nonneg _
  rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt h0, Complex.ofReal_inv]

/-- **`Σ_3`'s main sum in `F_D`**: `Σ_T (−1)^{|T|}ρ_D(π_T)Σ_d ρ_D(d)√(M/(N(T)N(d)))
  = √M·(Σ_T (−1)^{|T|}F_D(π_T))·S(K₁)`. -/
theorem main3_eq (G D : Finset Pr) {M : ℝ} (hM : 0 < M) (K₁ : ℝ) :
    ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * q2 D (∏ P ∈ T, πP P) *
      ∑ d ∈ eltsLe K₁, (if Squarefree (span {d}) then
        q2 D d * ((Real.sqrt (M / (nI T * (absNorm (span {d}) : ℝ))) : ℝ) : ℂ) else 0) =
    ((Real.sqrt M : ℝ) : ℂ) * ((∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * FD D (∏ P ∈ T, πP P)) *
      sqfS (FD D) K₁) := by
  have hS : sqfS (FD D) K₁ = ∑ d ∈ eltsLe K₁,
      (if Squarefree (span {d}) then FD D d else 0) := by
    unfold sqfS
    rw [tsum_eq_sum (s := eltsLe K₁) fun d hd =>
      ite_eq_right fun h => hd (mem_eltsLe.2 h.2)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hN := mem_eltsLe.1 hd
    by_cases h : Squarefree (span {d})
    · rw [ite_eq_left ⟨h, hN⟩, ite_eq_left h]
    · rw [ite_eq_right fun h' => h h'.1, ite_eq_right h]
  rw [hS, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : Squarefree (span {d})
  · rw [ite_eq_left h, ite_eq_left h]
    unfold FD
    rw [absNorm_span_prod_πP]
    have hT := nI_pos T
    have hN : (0 : ℝ) ≤ absNorm (span {d}) := Nat.cast_nonneg _
    rw [Real.sqrt_div hM.le, Real.sqrt_mul hT.le, div_eq_mul_inv, mul_inv]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right h]; ring

/-- **`Σ_4`'s main sum in `F_D`**: `Σ_{d sqf, (d,G)=1, N(d) ≤ K} ρ_D(d)√(M/N(d))
  = √M·Σ_{d sqf, (d,G)=1, N(d) ≤ K} F_D(d)`. -/
theorem main4_eq (G D : Finset Pr) {M : ℝ} (hM : 0 < M) (Kt : ℝ) :
    ∑ d ∈ eltsLe Kt, (if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
      q2 D d * ((Real.sqrt (M / (absNorm (span {d}) : ℝ))) : ℂ) else 0) =
    ((Real.sqrt M : ℝ) : ℂ) * ∑' d : 𝓞 K, (if Squarefree (span {d}) ∧ (∀ P ∈ G, ¬ πP P ∣ d) ∧
      (absNorm (span {d}) : ℝ) ≤ Kt then FD D d else 0) := by
  rw [tsum_eq_sum (s := eltsLe Kt) fun d hd =>
    ite_eq_right fun h => hd (mem_eltsLe.2 h.2.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hN := mem_eltsLe.1 hd
  by_cases h : Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d
  · rw [ite_eq_left h, ite_eq_left ⟨h.1, h.2, hN⟩]
    unfold FD
    rw [Real.sqrt_div hM.le, div_eq_mul_inv]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩, mul_zero]

/-- **The pair identity**: for a pair with greatest common divisor `G` and symmetric difference
`D ≠ ∅` disjoint from `G`, `ρ_D(−1) = 1`, `3R²N(D)N(G) ≤ 4MK₁` and `K₁ ≤ K`, with `w` the number
of units, `J = ∫_0^∞Φ` and `A = Σ_{T⊆G}(−1)^{|T|}F_D(π_T)`,
`w·(Σ_3 − Σ_4) = −(2π/√3)J·φ*(D)·√M·A·Σ_{U⊆G}F_D(π_U)·R_U + err₃ − err₄`,
`R_U = Σ_{d sqf, (d,G)=1, K₁ < N(U)N(d), N(d) ≤ K} F_D(d)`. -/
theorem pair_eq {M K₁ Kt : ℝ} (hM : 0 < M) {G D : Finset Pr} (hD : D.Nonempty)
    (hGD : Disjoint G D) (hneg : q2 D (-1) = 1) (hK₁ : 3 * RΦ ^ 2 * nI D * nI G ≤ 4 * M * K₁)
    (hK : K₁ ≤ Kt) :
    (Fintype.card (𝓞 K)ˣ : ℂ) * (sig3 M G D - sig4 M Kt G D) =
      -(((2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), PhiOnR y) *
          (∏ Q ∈ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)) * ((Real.sqrt M : ℝ) : ℂ) *
          ((∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * FD D (∏ P ∈ T, πP P)) *
            ∑ U ∈ G.powerset, FD D (∏ P ∈ U, πP P) * sqfR (FD D) G (nI U) K₁ Kt)) +
        err3 M K₁ G D - err4 M Kt G D := by
  have h3 := sig3_eq_main_add hM G hD hK₁
  have h4 := sig4_eq_main_add hM Kt G hD
  rw [gamD_eq_one hneg, one_mul, main3_eq G D hM K₁] at h3
  rw [main4_eq G D hM Kt] at h4
  have hF2 : ∀ P ∈ G, FD D (πP P) ^ 2 = (((absNorm P.1 : ℝ) : ℂ))⁻¹ := fun P hP =>
    FD_sq (Finset.disjoint_left.1 hGD hP)
  have hc := main_cancel (FD_one D) (FD_mul D) hF2 hK
  have hphi : ∏ Q ∈ G ∪ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹) =
      (∏ Q ∈ G, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)) * ∏ Q ∈ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹) :=
    Finset.prod_union hGD
  rw [hphi] at h4
  rw [mul_sub, h3, h4, err3, err4]
  simp only [err3T]
  linear_combination (((2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), PhiOnR y) *
    (∏ Q ∈ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)) * ((Real.sqrt M : ℝ) : ℂ)) * hc

end Eis

end

#print axioms Eis.prod_πP_dvd_iff
#print axioms Eis.πP_dvd_prod_mul_iff
#print axioms Eis.sqf_prod_mul_iff
#print axioms Eis.sum_powerset_part
#print axioms Eis.tsum_sqf_split
#print axioms Eis.summable_of_eltsLe
#print axioms Eis.absNorm_prod_mul
#print axioms Eis.F_prod
#print axioms Eis.sqfS_split
#print axioms Eis.phiStar_eq
#print axioms Eis.main_cancel
#print axioms Eis.FD_one
#print axioms Eis.FD_mul
#print axioms Eis.q2_πP_sq
#print axioms Eis.FD_sq
#print axioms Eis.main3_eq
#print axioms Eis.main4_eq
#print axioms Eis.pair_eq
