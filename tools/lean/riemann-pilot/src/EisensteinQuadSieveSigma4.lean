import EisensteinQuadSieveSquares

/-! # The quadratic large sieve, part 4d: Heath-Brown's `Σ_4` for a pair, and disjoint pairs (round 350)

S5e of round 312's plan, the first piece of S5e-4d as replanned in round 348.

* **`Σ_4` for a pair of columns** (`sig4`, `sig4_eq`, `sig4_eq_main_add`): for a pair of columns
  with greatest common divisor `G` and symmetric difference `D ≠ ∅`, Heath-Brown's `Σ_4` is the sum
  of `Φ(σm/√M)ρ_D(m)` over the arguments `m` prime to `G` with `s(m) ≤ K`. Writing `m = d·e²`
  with `(d)` squarefree (round 349's `sum_sqf_sq_iter`), `w·Σ_4` (`w` the number of units) is the
  sum over the squarefree `d` prime to `G` with `N(d) ≤ K` of `ρ_D(d)` times round 348's inner sum
  over the `e` prime to `G ∪ D`, at `β = √(N(d)/M)`. Round 348's `excl_eq_main_add` then gives
  the main term `(2π/√3)(∫_0^∞Φ)∏_{Q∈G∪D}(1 − N(Q)⁻¹)·Σ_d ρ_D(d)√(M/N(d))` and the error
  `Σ_d ρ_D(d)Σ_{T⊆G∪D}(−1)^{|T|}r_Φ(√(N(d)/M)·N(T))`.
* **The bilinear bound over disjoint pairs** (`bilin_disj_le`, `bilin_disj_le_c`): with
  `FBound w X Δ` and columns of norm at most `X`, the sum over the disjoint pairs of columns
  `Σ_m w(m)|Σ_{A₁∩A₂=∅} α(A₁)β(A₂)ρ_{A₁}(m)ρ_{A₂}(m)|` is at most
  `Δ·√(Σ_A 2^{|A|}|α(A)|²)·√(Σ_A 2^{|A|}|β(A)|²)`, and so is the modulus of the sum with complex
  row coefficients bounded by `w`. This is round 346's `sep_one` with no divisor, with each
  column sum bounded by `FBound.sub` and Cauchy–Schwarz over the common subsets `E`
  (`sum_powerset_filter_sub`). The error terms of `Σ_3` and `Σ_4` are to be bounded through it.
-/

open Complex MeasureTheory Set NumberField Ideal
open scoped Classical SchwartzMap

noncomputable section

namespace Eis

theorem πP_dvd_mul_sq (Q : Pr) (d e : 𝓞 K) : πP Q ∣ d * e ^ 2 ↔ πP Q ∣ d ∨ πP Q ∣ e := by
  rw [(prime_πP Q).dvd_mul, (prime_πP Q).dvd_pow_iff_dvd two_ne_zero]

/-- `ρ_D(e²)` is the indicator of `e` prime to `D`. -/
theorem q2_sq (D : Finset Pr) (e : 𝓞 K) :
    q2 D (e ^ 2) = if ∀ Q ∈ D, ¬ πP Q ∣ e then 1 else 0 := by
  unfold q2
  have h : ∀ Q ∈ D, quadR (𝓞 K ⧸ span {πP Q}) ℂ (Ideal.Quotient.mk (span {πP Q}) (e ^ 2)) =
      if πP Q ∣ e then 0 else 1 := by
    intro Q _
    rw [map_pow, map_pow, quadR_sq_mk]
  rw [Finset.prod_congr rfl h]
  split_ifs with hc
  · exact Finset.prod_eq_one fun Q hQ => ite_eq_right (hc Q hQ)
  · obtain ⟨Q, hQ, hd⟩ : ∃ Q ∈ D, πP Q ∣ e := by
      by_contra hne; exact hc fun Q hQ hd => hne ⟨Q, hQ, hd⟩
    exact Finset.prod_eq_zero hQ (ite_eq_left hd)

theorem q2_zero {D : Finset Pr} (hD : D.Nonempty) : q2 D 0 = 0 := by
  obtain ⟨Q, hQ⟩ := hD
  unfold q2
  exact Finset.prod_eq_zero hQ (by rw [map_zero, MulChar.map_zero])

/-- `|σ(d·e²)/√M| = √(N(d)/M)·N(e)`. -/
theorem norm_σO_mul_sq {M : ℝ} (hM : 0 < M) (d e : 𝓞 K) :
    ‖σO (d * e ^ 2) / (Real.sqrt M : ℂ)‖ =
      Real.sqrt ((absNorm (span {d}) : ℝ) / M) * (absNorm (span {e}) : ℝ) := by
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hd : ‖σO d‖ = Real.sqrt (absNorm (span {d}) : ℝ) := by
    rw [← sq_norm_σO, Real.sqrt_sq (norm_nonneg _)]
  rw [norm_div, map_mul, map_pow, norm_mul, norm_pow, sq_norm_σO, hd, Complex.norm_real,
    Real.norm_of_nonneg hsM.le, Real.sqrt_div (Nat.cast_nonneg _)]
  ring

/-- The majorant on the real line. -/
def PhiOnR : 𝓢(ℝ, ℂ) := onReal Majorant.Phi

/-- **Heath-Brown's `Σ_4` for a pair of columns** with greatest common divisor `G` and symmetric
difference `D`: the arguments prime to `G` with `s(m) ≤ K`, weighted by the majorant. -/
def sig4 (M Kt : ℝ) (G D : Finset Pr) : ℂ :=
  ∑' m : 𝓞 K, (if sqN m ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ m then
    Majorant.Phi (σO m / (Real.sqrt M : ℂ)) else 0) * q2 D m

theorem sqf_ne_zero {d : 𝓞 K} (hd : Squarefree (span {d})) : d ≠ 0 := by
  intro h; rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hd; exact hd.ne_zero rfl

/-- **`Σ_4` as a sum over squarefree kernels**: with `w` the number of units,
`w·Σ_4 = Σ_{d sqf, (d,G)=1, N(d) ≤ K} ρ_D(d)·Σ_{e prime to G ∪ D} Φ(√(N(d)/M)·N(e))`. -/
theorem sig4_eq {M : ℝ} (hM : 0 < M) (Kt : ℝ) (G : Finset Pr) {D : Finset Pr}
    (hD : D.Nonempty) :
    (Fintype.card (𝓞 K)ˣ : ℂ) * sig4 M Kt G D =
      ∑ d ∈ eltsLe Kt, if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
        q2 D d * ∑' e : 𝓞 K, (if ∀ Q ∈ G ∪ D, ¬ πP Q ∣ e then
          PhiOnR (Real.sqrt ((absNorm (span {d}) : ℝ) / M) * (absNorm (span {e}) : ℝ)) else 0)
      else 0 := by
  set f : 𝓞 K → ℂ := fun m => (if sqN m ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ m then
    Majorant.Phi (σO m / (Real.sqrt M : ℂ)) else 0) * q2 D m with hf
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hb : ((Real.sqrt M)⁻¹ : ℂ) ≠ 0 := by
    rw [ne_eq, inv_eq_zero]; exact_mod_cast hsM.ne'
  have hfs : Summable f := by
    have hs := summable_σO (affS Majorant.Phi 0 ((Real.sqrt M)⁻¹ : ℂ) hb)
    refine Summable.of_norm_bounded hs.norm fun m => ?_
    rw [affS_apply, zero_add, ← div_eq_inv_mul]
    simp only [hf]
    rw [norm_mul]
    refine (mul_le_of_le_one_right (norm_nonneg _) (norm_q2_le D m)).trans ?_
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hf0 : f 0 = 0 := by simp only [hf, q2_zero hD, mul_zero]
  obtain ⟨-, heq⟩ := sum_sqf_sq_iter f hfs hf0
  have hcopU : ∀ e : 𝓞 K, (∀ Q ∈ G ∪ D, ¬ πP Q ∣ e) ↔
      (∀ Q ∈ G, ¬ πP Q ∣ e) ∧ (∀ Q ∈ D, ¬ πP Q ∣ e) := by
    intro e
    simp only [Finset.mem_union]
    constructor
    · intro h; exact ⟨fun Q hQ => h Q (Or.inl hQ), fun Q hQ => h Q (Or.inr hQ)⟩
    · rintro ⟨h1, h2⟩ Q (hQ | hQ)
      · exact h1 Q hQ
      · exact h2 Q hQ
  have hcopM : ∀ d e : 𝓞 K, (∀ Q ∈ G, ¬ πP Q ∣ d * e ^ 2) ↔
      (∀ Q ∈ G, ¬ πP Q ∣ d) ∧ (∀ Q ∈ G, ¬ πP Q ∣ e) := by
    intro d e
    simp only [πP_dvd_mul_sq, not_or]
    exact ⟨fun h => ⟨fun Q hQ => (h Q hQ).1, fun Q hQ => (h Q hQ).2⟩,
      fun h Q hQ => ⟨h.1 Q hQ, h.2 Q hQ⟩⟩
  -- one term of the inner sum
  have hterm : ∀ d : 𝓞 K, Squarefree (span {d}) → ∀ e : 𝓞 K,
      f (d * e ^ 2) = (if (absNorm (span {d}) : ℝ) ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
          q2 D d else 0) *
        (if ∀ Q ∈ G ∪ D, ¬ πP Q ∣ e then
          PhiOnR (Real.sqrt ((absNorm (span {d}) : ℝ) / M) * (absNorm (span {e}) : ℝ)) else 0) := by
    intro d hd e
    obtain ⟨Q0, hQ0⟩ := hD
    by_cases he : e = 0
    · subst he
      have hn : ¬ ∀ Q ∈ G ∪ D, ¬ πP Q ∣ (0 : 𝓞 K) :=
        fun h => h Q0 (Finset.mem_union_right _ hQ0) (dvd_zero _)
      rw [ite_eq_right hn, mul_zero, show d * (0 : 𝓞 K) ^ 2 = 0 by ring, hf0]
    · have hPhi : Majorant.Phi (σO (d * e ^ 2) / (Real.sqrt M : ℂ)) =
          PhiOnR (Real.sqrt ((absNorm (span {d}) : ℝ) / M) * (absNorm (span {e}) : ℝ)) := by
        rw [Phi_eq_norm, norm_σO_mul_sq hM, PhiOnR, onReal_apply]
      simp only [hf]
      rw [sqN_sqf_mul_sq hd he, q2_mul, q2_sq, hPhi]
      simp only [hcopM, hcopU]
      by_cases h12 : (absNorm (span {d}) : ℝ) ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ d
      · rw [ite_eq_left h12]
        by_cases h34 : (∀ Q ∈ G, ¬ πP Q ∣ e) ∧ ∀ Q ∈ D, ¬ πP Q ∣ e
        · rw [ite_eq_left ⟨h12.1, h12.2, h34.1⟩, ite_eq_left h34.2, ite_eq_left h34]; ring
        · rw [ite_eq_right h34]
          by_cases h3 : ∀ Q ∈ G, ¬ πP Q ∣ e
          · rw [ite_eq_right fun h4 => h34 ⟨h3, h4⟩]; ring
          · rw [ite_eq_right fun h => h3 h.2.2]; ring
      · rw [ite_eq_right h12, ite_eq_right fun h => h12 ⟨h.1, h.2.1⟩]; ring
  -- the outer sum, over the rows of norm at most `K`
  have hout : ∀ d : 𝓞 K, (if Squarefree (span {d}) then ∑' e : 𝓞 K, f (d * e ^ 2) else 0) =
      if Squarefree (span {d}) ∧ (absNorm (span {d}) : ℝ) ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
        q2 D d * ∑' e : 𝓞 K, (if ∀ Q ∈ G ∪ D, ¬ πP Q ∣ e then
          PhiOnR (Real.sqrt ((absNorm (span {d}) : ℝ) / M) * (absNorm (span {e}) : ℝ)) else 0)
      else 0 := by
    intro d
    by_cases hd : Squarefree (span {d})
    · rw [ite_eq_left hd, tsum_congr (hterm d hd), tsum_mul_left]
      by_cases h2 : (absNorm (span {d}) : ℝ) ≤ Kt ∧ ∀ Q ∈ G, ¬ πP Q ∣ d
      · rw [ite_eq_left h2, ite_eq_left ⟨hd, h2⟩]
      · rw [ite_eq_right h2, zero_mul, ite_eq_right fun h => h2 h.2]
    · rw [ite_eq_right hd, ite_eq_right fun h => hd h.1]
  show (Fintype.card (𝓞 K)ˣ : ℂ) * ∑' m, f m = _
  rw [← heq, tsum_congr hout, tsum_eq_sum (s := eltsLe Kt) fun d hd =>
    ite_eq_right fun h => hd (mem_eltsLe.2 h.2.1)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hN := mem_eltsLe.1 hd
  by_cases h : Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d
  · rw [ite_eq_left ⟨h.1, hN, h.2⟩, ite_eq_left h]
  · rw [ite_eq_right fun h' => h ⟨h'.1, h'.2.2⟩, ite_eq_right h]

/-- **The explicit formula for `Σ_4`**: with `w` the number of units,
`w·Σ_4 = (2π/√3)(∫_0^∞Φ)∏_{Q∈G∪D}(1 − N(Q)⁻¹)·Σ_d ρ_D(d)√(M/N(d))
  + Σ_d ρ_D(d)·Σ_{T⊆G∪D}(−1)^{|T|}r_Φ(√(N(d)/M)·N(T))`,
the sums over the squarefree `d` prime to `G` with `N(d) ≤ K`. -/
theorem sig4_eq_main_add {M : ℝ} (hM : 0 < M) (Kt : ℝ) (G : Finset Pr) {D : Finset Pr}
    (hD : D.Nonempty) :
    (Fintype.card (𝓞 K)ˣ : ℂ) * sig4 M Kt G D =
      ((2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), PhiOnR y) *
          (∏ Q ∈ G ∪ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)) *
          ∑ d ∈ eltsLe Kt, (if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
            q2 D d * ((Real.sqrt (M / (absNorm (span {d}) : ℝ)) : ℝ) : ℂ) else 0) +
        ∑ d ∈ eltsLe Kt, (if Squarefree (span {d}) ∧ ∀ Q ∈ G, ¬ πP Q ∣ d then
          q2 D d * ∑ T ∈ (G ∪ D).powerset, (-1 : ℂ) ^ T.card *
            latErr PhiOnR (Real.sqrt ((absNorm (span {d}) : ℝ) / M) * nI T) else 0) := by
  rw [sig4_eq hM Kt G hD, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with hd
  · have hN : (0 : ℝ) < absNorm (span {d}) := by
      refine Nat.cast_pos.2 (Nat.pos_of_ne_zero ?_)
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact sqf_ne_zero hd.1
    have hβ : 0 < Real.sqrt ((absNorm (span {d}) : ℝ) / M) := Real.sqrt_pos.2 (div_pos hN hM)
    rw [excl_eq_main_add PhiOnR hβ (G ∪ D)]
    have hc : ((2 * Real.pi / (Real.sqrt 3 * Real.sqrt ((absNorm (span {d}) : ℝ) / M)) : ℝ) : ℂ) =
        ((2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) *
          ((Real.sqrt (M / (absNorm (span {d}) : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [show M / (absNorm (span {d}) : ℝ) = ((absNorm (span {d}) : ℝ) / M)⁻¹ by rw [inv_div],
        Real.sqrt_inv]
      field_simp
    rw [hc]; ring
  · simp

/-- `Σ_{E⊆U} Σ_{A ⊇ E} g(A) = Σ_A 2^{|A|}·g(A)` for a family of subsets of `U`. -/
theorem sum_powerset_filter_sub (U : Finset Pr) (𝒩 : Finset (Finset Pr))
    (h𝒩 : ∀ A ∈ 𝒩, A ⊆ U) (g : Finset Pr → ℝ) :
    ∑ E ∈ U.powerset, ∑ A ∈ 𝒩.filter (E ⊆ ·), g A = ∑ A ∈ 𝒩, (2 : ℝ) ^ A.card * g A := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h : U.powerset.filter (· ⊆ A) = A.powerset := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans (h𝒩 A hA), h⟩⟩
  rw [h, Finset.card_powerset]
  push_cast
  ring

/-- **The bilinear bound over disjoint pairs**: for a nonnegative summable weight `w` with
`FBound w X Δ` and columns of norm at most `X`,
`Σ_m w(m)|Σ_{A₁,A₂ disjoint} α(A₁)β(A₂)ρ_{A₁}(m)ρ_{A₂}(m)|
  ≤ Δ·√(Σ_A 2^{|A|}|α(A)|²)·√(Σ_A 2^{|A|}|β(A)|²)`. -/
theorem bilin_disj_le {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {X Δ : ℝ}
    (hΔ : 0 ≤ Δ) (h : FBound w X Δ) (𝒩 : Finset (Finset Pr)) (h𝒩 : ∀ A ∈ 𝒩, nI A ≤ X)
    (α β : Finset Pr → ℂ) :
    ∑' m : 𝓞 K, w m * ‖∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
      (if Disjoint A1 A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0)‖ ≤
      Δ * (Real.sqrt (∑ A ∈ 𝒩, (2 : ℝ) ^ A.card * ‖α A‖ ^ 2) *
        Real.sqrt (∑ A ∈ 𝒩, (2 : ℝ) ^ A.card * ‖β A‖ ^ 2)) := by
  set U : Finset Pr := 𝒩.sup id with hU
  have h𝒩U : ∀ A ∈ 𝒩, A ⊆ U := fun A hA => Finset.le_sup (f := id) hA
  have hs := sep_one hw0 hw U 𝒩 h𝒩U α β ∅
  simp only [Finset.empty_subset, and_true, Finset.powerset_empty, Finset.sum_singleton,
    Finset.empty_union, Finset.empty_sdiff] at hs
  have hX : ∀ E : Finset Pr, ∀ A ∈ 𝒩, E ⊆ A → nI A ≤ X * nI E := by
    intro E A hA _
    have h1 := h𝒩 A hA
    have h2 := one_le_nI E
    have h3 := nI_pos A
    nlinarith
  set SA : Finset Pr → ℝ := fun E => ∑ A ∈ 𝒩.filter (E ⊆ ·), ‖α A‖ ^ 2 with hSA
  set SB : Finset Pr → ℝ := fun E => ∑ A ∈ 𝒩.filter (E ⊆ ·), ‖β A‖ ^ 2 with hSB
  have hSA0 : ∀ E, 0 ≤ SA E := fun E => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSB0 : ∀ E, 0 ≤ SB E := fun E => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha : ∀ E, ∑' m : 𝓞 K, w m * ‖colX 𝒩 α E m‖ ^ 2 ≤ Δ * SA E :=
    fun E => h.sub hw0 hw 𝒩 α E (hX E)
  have hb : ∀ E, ∑' m : 𝓞 K, w m * ‖colX 𝒩 β E m‖ ^ 2 ≤ Δ * SB E :=
    fun E => h.sub hw0 hw 𝒩 β E (hX E)
  refine hs.trans ?_
  calc ∑ E ∈ U.powerset, Real.sqrt (∑' m : 𝓞 K, w m * ‖colX 𝒩 α E m‖ ^ 2) *
        Real.sqrt (∑' m : 𝓞 K, w m * ‖colX 𝒩 β E m‖ ^ 2)
      ≤ ∑ E ∈ U.powerset, Real.sqrt (Δ * SA E) * Real.sqrt (Δ * SB E) :=
        Finset.sum_le_sum fun E _ => mul_le_mul (Real.sqrt_le_sqrt (ha E))
          (Real.sqrt_le_sqrt (hb E)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Δ * ∑ E ∈ U.powerset, Real.sqrt (SA E) * Real.sqrt (SB E) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun E _ => ?_
        rw [Real.sqrt_mul hΔ, Real.sqrt_mul hΔ]
        have := Real.mul_self_sqrt hΔ
        calc Real.sqrt Δ * Real.sqrt (SA E) * (Real.sqrt Δ * Real.sqrt (SB E))
            = (Real.sqrt Δ * Real.sqrt Δ) * (Real.sqrt (SA E) * Real.sqrt (SB E)) := by ring
          _ = Δ * (Real.sqrt (SA E) * Real.sqrt (SB E)) := by rw [this]
    _ ≤ Δ * (Real.sqrt (∑ E ∈ U.powerset, SA E) * Real.sqrt (∑ E ∈ U.powerset, SB E)) :=
        mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le _ hSA0 hSB0) hΔ
    _ = _ := by
        simp only [hSA, hSB]
        rw [sum_powerset_filter_sub U 𝒩 h𝒩U, sum_powerset_filter_sub U 𝒩 h𝒩U]

/-- **The bilinear bound with complex row coefficients**: for `|c(m)| ≤ w(m)`,
`|Σ_m c(m)Σ_{A₁,A₂ disjoint} α(A₁)β(A₂)ρ_{A₁}(m)ρ_{A₂}(m)|
  ≤ Δ·√(Σ_A 2^{|A|}|α(A)|²)·√(Σ_A 2^{|A|}|β(A)|²)`. -/
theorem bilin_disj_le_c {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {X Δ : ℝ}
    (hΔ : 0 ≤ Δ) (h : FBound w X Δ) (𝒩 : Finset (Finset Pr)) (h𝒩 : ∀ A ∈ 𝒩, nI A ≤ X)
    (α β : Finset Pr → ℂ) (c : 𝓞 K → ℂ) (hc : ∀ m, ‖c m‖ ≤ w m) :
    ‖∑' m : 𝓞 K, c m * ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
      (if Disjoint A1 A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0)‖ ≤
      Δ * (Real.sqrt (∑ A ∈ 𝒩, (2 : ℝ) ^ A.card * ‖α A‖ ^ 2) *
        Real.sqrt (∑ A ∈ 𝒩, (2 : ℝ) ^ A.card * ‖β A‖ ^ 2)) := by
  set Z : 𝓞 K → ℂ := fun m => ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
    (if Disjoint A1 A2 then α A1 * β A2 * (q2 A1 m * q2 A2 m) else 0) with hZ
  have hZb : ∀ m, ‖Z m‖ ≤ (∑ A ∈ 𝒩, ‖α A‖) * (∑ A ∈ 𝒩, ‖β A‖) := by
    intro m
    rw [Finset.sum_mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A1 _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun A2 _ => ?_))
    split_ifs
    · rw [norm_mul, norm_mul, norm_mul]
      have h1 := norm_q2_le A1 m
      have h2 := norm_q2_le A2 m
      have h12 : ‖q2 A1 m‖ * ‖q2 A2 m‖ ≤ 1 := by
        nlinarith [norm_nonneg (q2 A1 m), norm_nonneg (q2 A2 m)]
      have hab := mul_nonneg (norm_nonneg (α A1)) (norm_nonneg (β A2))
      nlinarith
    · rw [norm_zero]; positivity
  have hs : Summable fun m => w m * ‖Z m‖ :=
    summable_w_mul hw (g := fun m => ‖Z m‖) fun m => by
      rw [abs_of_nonneg (norm_nonneg _)]; exact hZb m
  have hs' : Summable fun m => ‖c m * Z m‖ :=
    hs.of_nonneg_of_le (fun m => norm_nonneg _) fun m => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hc m) (norm_nonneg _)
  calc ‖∑' m : 𝓞 K, c m * Z m‖ ≤ ∑' m : 𝓞 K, ‖c m * Z m‖ := norm_tsum_le_tsum_norm hs'
    _ ≤ ∑' m : 𝓞 K, w m * ‖Z m‖ := hs'.tsum_le_tsum (fun m => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hc m) (norm_nonneg _)) hs
    _ ≤ _ := bilin_disj_le hw0 hw hΔ h 𝒩 h𝒩 α β

end Eis

end

#print axioms Eis.πP_dvd_mul_sq
#print axioms Eis.q2_sq
#print axioms Eis.q2_zero
#print axioms Eis.norm_σO_mul_sq
#print axioms Eis.sqf_ne_zero
#print axioms Eis.sig4_eq
#print axioms Eis.sig4_eq_main_add
#print axioms Eis.sum_powerset_filter_sub
#print axioms Eis.bilin_disj_le
#print axioms Eis.bilin_disj_le_c
