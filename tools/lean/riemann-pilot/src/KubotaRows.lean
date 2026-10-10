import KubotaRowsDual
import KubotaVsharp
import EisensteinQuadSieveFinal

/-! # The theta transformation for the rows, from the Kubota–Patterson theorem (round 381)

S5f-6 of round 360's plan, part 4, which completes S5f-6. The companion paper writes:
"`Proposition~\ref{lem:reflection} and Lemmas~\ref{lem:reflection-uniformity} and~\ref{lem:theta-bounds} are
proved in Appendix~\ref{app:fixed-ray}.`" This file completes their proof for the rows, in the form of the
display `Eis.ThetaRows` (round 341), from the display `Eis.KubotaTheta` (round 361). With round 359's
`ne_zero_of_thetaRows`, the half-plane `Re s > 11/12` then rests on `KubotaTheta` alone.

* **The dual parameters** (`GoodQ`, a definition; **`dualPt_inj`**, with `dualPt_neg`, `exists_good_of_ne` and
  `dualNorm_pos`): `q ↦ u(ω − 1)^m·n·b³` is injective on the good parameters (`𝔫` squarefree, `N𝔫` and `N𝔟`
  prime to `3`), and the support of a series under `ThetaSupp` consists of their dual points.
* **One group** (`cuspCoefQ`, a definition; **`dual_sum_eq`**, with `prod_rowJ`, `normSq_cusp` and
  `dual_term_eq`): round 380's dual sum of the group with the active set `𝒜_fix ∪ {P ∣ k₀}` is `(9i/4)·N(c)/K₀`
  times `ThetaRows`' `dualTerm`, with `c₀ = D` and `h(w) = V^♯((2π)⁴e^w/27)`.
* **The active sets** (**`sum_rowPs_admissible`**): only the groups `𝒜_fix ∪ {P ∣ k₀}` with `𝒜_fix`
  admissible survive.
* **The assembly** (**`thetaRows_of_data`**, with `goodQ_of_cuspCoefQ_ne`, `norm_cuspCoefQ_le`,
  `finsum_eq_sum_range` and `rcls_rows`; **`thetaRows_of_kubota`**): `KubotaTheta → ThetaRows`, with
  `J = 16`, `M = 9·72`, and the residues modulo `72` as the indices `i`.
* **The half-plane** (**`ne_zero_of_kubotaTheta`**): `ζ(s)L(s, χ₋₃) ≠ 0` for `Re s > 11/12`, from
  `KubotaTheta`.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics UniqueFactorizationMonoid
open scoped Topology ComplexConjugate

noncomputable section

namespace Eis

/-- The good dual parameters: `𝔫` squarefree, and `N𝔫`, `N𝔟` prime to `3`. -/
def GoodQ (q : DualIdx) : Prop :=
  Squarefree q.2.2.1 ∧ (absNorm q.2.2.1).Coprime 3 ∧ (absNorm q.2.2.2).Coprime 3

/-- **The dual point determines its parameters**: `q ↦ uλ^m·n·b³` is injective on the good parameters. -/
theorem dualPt_inj {q q' : DualIdx} (hq : GoodQ q) (hq' : GoodQ q') (h : dualPt q = dualPt q') :
    q = q' := by
  obtain ⟨hsq, hn, hb⟩ := hq
  obtain ⟨hsq', hn', hb'⟩ := hq'
  obtain ⟨hn1, hn2⟩ := pgen_spec3 hn
  obtain ⟨hb1, hb2⟩ := pgen_spec3 hb
  obtain ⟨hn1', hn2'⟩ := pgen_spec3 hn'
  obtain ⟨hb1', hb2'⟩ := pgen_spec3 hb'
  have hpa : Primary (pgen q.2.2.1 * pgen q.2.2.2 ^ 3) := hn1.mul (primary_pow hb1 3)
  have hpa' : Primary (pgen q'.2.2.1 * pgen q'.2.2.2 ^ 3) := hn1'.mul (primary_pow hb1' 3)
  have hl : (Eis.ω - 1 : 𝓞 K) ≠ 0 := fun h0 => by
    have := normSq_σO_lam
    rw [h0, map_zero, map_zero] at this
    norm_num at this
  have e : (q.1 : 𝓞 K) * (Eis.ω - 1) ^ q.2.1 * (pgen q.2.2.1 * pgen q.2.2.2 ^ 3) =
      (q'.1 : 𝓞 K) * (Eis.ω - 1) ^ q'.2.1 * (pgen q'.2.2.1 * pgen q'.2.2.2 ^ 3) := by
    unfold dualPt at h; linear_combination h
  -- the exponents of `λ` agree
  have key : ∀ {k k' : ℕ} {u u' : (𝓞 K)ˣ} {a a' : 𝓞 K}, Primary a → k < k' →
      (u : 𝓞 K) * (Eis.ω - 1) ^ k * a ≠ (u' : 𝓞 K) * (Eis.ω - 1) ^ k' * a' := by
    intro k k' u u' a a' ha hlt he
    obtain ⟨d, rfl⟩ : ∃ d, k' = k + (d + 1) := ⟨k' - k - 1, by omega⟩
    have e2 : (u : 𝓞 K) * a = (u' : 𝓞 K) * (Eis.ω - 1) ^ (d + 1) * a' := by
      apply mul_left_cancel₀ (pow_ne_zero k hl)
      linear_combination he
    have hdvd : (Eis.ω - 1 : 𝓞 K) ∣ (u : 𝓞 K) * a :=
      ⟨(u' : 𝓞 K) * (Eis.ω - 1) ^ d * a', by rw [e2]; ring⟩
    exact ha.not_lam_dvd (Units.dvd_mul_left.1 hdvd)
  have hk : q.2.1 = q'.2.1 := by
    rcases lt_trichotomy q.2.1 q'.2.1 with hlt | heq | hgt
    · exact absurd e (key hpa hlt)
    · exact heq
    · exact absurd e.symm (key hpa' hgt)
  rw [hk] at e
  have e3 : (q.1 : 𝓞 K) * (pgen q.2.2.1 * pgen q.2.2.2 ^ 3) =
      (q'.1 : 𝓞 K) * (pgen q'.2.2.1 * pgen q'.2.2.2 ^ 3) := by
    apply mul_left_cancel₀ (pow_ne_zero q'.2.1 hl)
    linear_combination e
  -- the ideals agree
  have hspan : q.2.2.1 * q.2.2.2 ^ 3 = q'.2.2.1 * q'.2.2.2 ^ 3 := by
    have h1 : span {pgen q.2.2.1 * pgen q.2.2.2 ^ 3} = span {pgen q'.2.2.1 * pgen q'.2.2.2 ^ 3} := by
      rw [Ideal.span_singleton_eq_span_singleton]
      refine ⟨q.1 * q'.1⁻¹, ?_⟩
      apply mul_left_cancel₀ q'.1.ne_zero
      rw [Units.val_mul]
      calc (q'.1 : 𝓞 K) * ((pgen q.2.2.1 * pgen q.2.2.2 ^ 3) * ((q.1 : 𝓞 K) * ((q'.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K))) =
          (q.1 : 𝓞 K) * (pgen q.2.2.1 * pgen q.2.2.2 ^ 3) * ((q'.1 : 𝓞 K) * ((q'.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) := by
            ring
        _ = (q'.1 : 𝓞 K) * (pgen q'.2.2.1 * pgen q'.2.2.2 ^ 3) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, e3]
    rwa [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hn2, hb2,
      ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hn2', hb2'] at h1
  obtain ⟨h𝔫, h𝔟⟩ := sqfree_cube_unique hsq hsq' (ne_bot_of_coprime3 hb) hspan
  have hpg : ∀ {I : Ideal (𝓞 K)}, (absNorm I).Coprime 3 → pgen I ≠ 0 := fun {I} hI h0 => by
    have h2 := (pgen_spec3 hI).2
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at h2
    exact ne_bot_of_coprime3 hI h2.symm
  have ha0 : pgen q.2.2.1 * pgen q.2.2.2 ^ 3 ≠ 0 := mul_ne_zero (hpg hn) (pow_ne_zero 3 (hpg hb))
  rw [← h𝔫, ← h𝔟] at e3
  have hu : q.1 = q'.1 := Units.ext (mul_right_cancel₀ ha0 e3)
  exact Prod.ext hu (Prod.ext hk (Prod.ext h𝔫 h𝔟))

theorem dualPt_neg (q : DualIdx) : dualPt (-q.1, q.2) = -dualPt q := by
  unfold dualPt; simp only [Units.val_neg]; ring

/-- Where `d_H(−m) ≠ 0`, `m` is the dual point of a good parameter, with the bound of `ThetaSupp`. -/
theorem exists_good_of_ne {Kc : ℝ} {dH : 𝓞 K → ℂ} (hdH : ThetaSupp Kc dH) {m : 𝓞 K} (h : dH (-m) ≠ 0) :
    ∃ q : DualIdx, GoodQ q ∧ dualPt q = m ∧
      ‖dH (-m)‖ ≤ Kc * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2) := by
  obtain ⟨q, hq, hsq, hn, hb, hbd⟩ := hdH.2 _ h
  exact ⟨(-q.1, q.2), ⟨hsq, hn, hb⟩, by rw [dualPt_neg, hq, neg_neg], hbd⟩

/-- The local factors of the active set `𝒜 = 𝒜_fix ∪ {P ∣ k₀}`, with `j_P = 1` at the primes of `k₀`. -/
theorem prod_rowJ {t g k₀ : 𝓞 K} (hcop : IsCoprime k₀ (t * g)) {A' : Finset Pr}
    (hA' : A' ⊆ primeSet (span {t * g})) (m : 𝓞 K) :
    ∏ P : ↥(A' ∪ primeSet (span {k₀})), Bloc P.1.1 (rowJ t g k₀ P.1) m =
      (∏ P ∈ A', Bloc P.1 (jFix t g P) m) * ∏ P ∈ primeSet (span {k₀}), Bloc P.1 1 m := by
  have hdisj : Disjoint A' (primeSet (span {k₀})) :=
    Finset.disjoint_of_subset_left hA' (disjoint_primeSet hcop)
  rw [Finset.prod_coe_sort (A' ∪ primeSet (span {k₀})) (fun P => Bloc P.1 (rowJ t g k₀ P) m),
    Finset.prod_union hdisj]
  congr 1
  · refine Finset.prod_congr rfl fun P hP => ?_
    rw [rowJ, ite_eq_right (Finset.disjoint_left.1 hdisj hP)]
  · refine Finset.prod_congr rfl fun P hP => ?_
    rw [rowJ, ite_eq_left hP]

/-- `N(c) = N(D)·N(𝒜_fix)·N(k₀)` for `c = D∏_{P∈𝒜}π_P`. -/
theorem normSq_cusp {D k₀ : 𝓞 K} (hk : QAdm k₀) {A' : Finset Pr}
    (hdisj : Disjoint A' (primeSet (span {k₀}))) :
    Complex.normSq (σO (D * ∏ P ∈ A' ∪ primeSet (span {k₀}), πP P)) =
      (absNorm (span {D}) : ℝ) * nI A' * (absNorm (span {k₀}) : ℝ) := by
  rw [normSq_σO, ← Ideal.span_singleton_mul_span_singleton, map_mul, span_prod_πP, Nat.cast_mul]
  have e : (absNorm (idl (A' ∪ primeSet (span {k₀}))) : ℝ) = nI (A' ∪ primeSet (span {k₀})) := rfl
  rw [e, nI_union hdisj, nI_primeSet hk]
  ring

open Classical in
/-- The coefficients of the dual sums in the parameters `q = (u, m, 𝔫, 𝔟)`: at the good `q`, with
`x = uλ^m n b³`, `K₀·d̄_H(−x)ψ_{λ³D}(−xy)·σ(x)/|σ(x)|`; `0` at the others. -/
def cuspCoefQ (K₀ : ℝ) (dH : 𝓞 K → ℂ) (D y : 𝓞 K) (q : DualIdx) : ℂ :=
  if GoodQ q then (K₀ : ℂ) * (conj (dH (-dualPt q)) * ψc (δ3 ^ 3 * D) (-(dualPt q * y)) *
    (σO (dualPt q) / (‖σO (dualPt q)‖ : ℂ))) else 0

theorem dualNorm_pos {q : DualIdx} (hq : GoodQ q) : 0 < dualNorm q := by
  have h1 : (0 : ℝ) < absNorm q.2.2.1 := by
    have := ne_bot_of_coprime3 hq.2.1
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => this (absNorm_eq_zero_iff.1 h0)
  have h2 : (0 : ℝ) < absNorm q.2.2.2 := by
    have := ne_bot_of_coprime3 hq.2.2
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => this (absNorm_eq_zero_iff.1 h0)
  unfold dualNorm; positivity

/-- **One term of the dual sums**: at a good `q`, the term of round 376's dual sum at `x = dualPt q` is
`(9i/4)·N(c)/K₀` times the term of `ThetaRows`' `dualTerm` with the coefficient `cuspCoefQ` and
`h(w) = V^♯((2π)⁴e^w/27)`. -/
theorem dual_term_eq {dH : 𝓞 K → ℂ} {D y : 𝓞 K} {K₀ Nc nD nA nk : ℝ} (hK₀ : K₀ ≠ 0) (hNc : 0 < Nc)
    (hN : Nc = nD * nA * nk) (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X) (B₁ B₂ : ℂ) {q : DualIdx} (hq : GoodQ q) :
    conj (dH (-dualPt q)) * ψc (δ3 ^ 3 * D) (-(dualPt q * y)) * (B₁ * B₂) *
        (2 * Real.pi * I * σO (dualPt q) / 9) *
        ((Nc * ((4 * Real.pi * ‖σO (dualPt q)‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
        (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO (dualPt q)‖ / 9) ^ 2 / (4 * Nc ^ 2) *
          (4 * Real.pi ^ 2 * X / 27))) =
      9 * I / 4 * ((Nc / K₀ : ℝ) : ℂ) * (cuspCoefQ K₀ dH D y q * B₁ * B₂ *
        Vsharp W ((2 * Real.pi) ^ 4 / 27 * Real.exp (Real.log (dualNorm q / 81 * X / (nD ^ 2 * nA ^ 2 * nk ^ 2)))) /
        ((Real.sqrt (dualNorm q) : ℝ) : ℂ)) := by
  have hdn := dualNorm_pos hq
  have hr2 : ‖σO (dualPt q)‖ ^ 2 = dualNorm q := by
    rw [← Complex.normSq_eq_norm_sq, normSq_dualPt hq.2.1 hq.2.2]
  have hr : 0 < ‖σO (dualPt q)‖ := by
    rcases (norm_nonneg (σO (dualPt q))).lt_or_eq with h | h
    · exact h
    · rw [← h] at hr2; linarith
  have hsq : Real.sqrt (dualNorm q) = ‖σO (dualPt q)‖ := by
    rw [← hr2, Real.sqrt_sq hr.le]
  have hprod : 0 < nD ^ 2 * nA ^ 2 * nk ^ 2 := by
    have : nD ^ 2 * nA ^ 2 * nk ^ 2 = Nc ^ 2 := by rw [hN]; ring
    rw [this]; positivity
  have harg : (2 * Real.pi) ^ 4 / 27 * Real.exp (Real.log (dualNorm q / 81 * X / (nD ^ 2 * nA ^ 2 * nk ^ 2))) =
      (4 * Real.pi * ‖σO (dualPt q)‖ / 9) ^ 2 / (4 * Nc ^ 2) * (4 * Real.pi ^ 2 * X / 27) := by
    rw [Real.exp_log (by positivity), ← hr2,
      show nD ^ 2 * nA ^ 2 * nk ^ 2 = Nc ^ 2 by rw [hN]; ring]
    field_simp
    ring
  unfold cuspCoefQ
  rw [ite_eq_left hq, harg, hsq]
  generalize Vsharp W ((4 * Real.pi * ‖σO (dualPt q)‖ / 9) ^ 2 / (4 * Nc ^ 2) * (4 * Real.pi ^ 2 * X / 27)) = V
  have hr0 : ((‖σO (dualPt q)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hK : ((K₀ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hK₀
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  have hr2c : ((‖σO (dualPt q)‖ : ℝ) : ℂ) ^ 2 = ((dualNorm q : ℝ) : ℂ) := by exact_mod_cast hr2
  push_cast
  field_simp
  ring

/-- **One group's dual sum in the parameters of `ThetaRows`**: for the active set `𝒜_fix ∪ {P ∣ k₀}`,
round 376's dual sum over `m` is `(9i/4)·N(c)/K₀` times `dualTerm` with the coefficients `cuspCoefQ`,
`c₀ = D` and `h(w) = V^♯((2π)⁴e^w/27)`. The sum over `m` is reindexed by the good parameters `q`, through
`m = dualPt q`. -/
theorem dual_sum_eq {Kc : ℝ} {dH : 𝓞 K → ℂ} (hdH : ThetaSupp Kc dH) {D y : 𝓞 K} (hD : D ≠ 0)
    {t g k₀ : 𝓞 K} (hk : QAdm k₀) (hcop : IsCoprime k₀ (t * g)) {A' : Finset Pr}
    (hA' : A' ⊆ primeSet (span {t * g})) (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X) {K₀ : ℝ} (hK₀ : K₀ ≠ 0) :
    ∑' m : 𝓞 K, conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * y)) *
        (∏ P : ↥(A' ∪ primeSet (span {k₀})), Bloc P.1.1 (rowJ t g k₀ P.1) m) *
        (2 * Real.pi * I * σO m / 9) *
        ((Complex.normSq (σO (D * ∏ P ∈ A' ∪ primeSet (span {k₀}), πP P)) *
          ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
        (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
          (4 * Complex.normSq (σO (D * ∏ P ∈ A' ∪ primeSet (span {k₀}), πP P)) ^ 2) *
          (4 * Real.pi ^ 2 * X / 27))) =
      9 * I / 4 * ((Complex.normSq (σO (D * ∏ P ∈ A' ∪ primeSet (span {k₀}), πP P)) / K₀ : ℝ) : ℂ) *
        dualTerm (fun w => Vsharp W ((2 * Real.pi) ^ 4 / 27 * Real.exp w)) (cuspCoefQ K₀ dH D y) D A'
          (jFix t g) k₀ X := by
  set Nc := Complex.normSq (σO (D * ∏ P ∈ A' ∪ primeSet (span {k₀}), πP P)) with hNc
  have hdisj : Disjoint A' (primeSet (span {k₀})) :=
    Finset.disjoint_of_subset_left hA' (disjoint_primeSet hcop)
  have hNeq : Nc = (absNorm (span {D}) : ℝ) * nI A' * (absNorm (span {k₀}) : ℝ) := normSq_cusp hk hdisj
  have hNpos : 0 < Nc := by
    rw [hNc, Complex.normSq_pos]
    intro h0
    exact mul_ne_zero hD (prod_πP_ne_zero _) (σO_injective (h0.trans (map_zero σO).symm))
  unfold dualTerm
  rw [← tsum_mul_left]
  -- the value identity at the good parameters
  have hval : ∀ q : DualIdx, GoodQ q →
      conj (dH (-dualPt q)) * ψc (δ3 ^ 3 * D) (-(dualPt q * y)) *
          (∏ P : ↥(A' ∪ primeSet (span {k₀})), Bloc P.1.1 (rowJ t g k₀ P.1) (dualPt q)) *
          (2 * Real.pi * I * σO (dualPt q) / 9) *
          ((Nc * ((4 * Real.pi * ‖σO (dualPt q)‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
          (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO (dualPt q)‖ / 9) ^ 2 / (4 * Nc ^ 2) *
            (4 * Real.pi ^ 2 * X / 27))) =
        9 * I / 4 * ((Nc / K₀ : ℝ) : ℂ) *
          (cuspCoefQ K₀ dH D y q * (∏ P ∈ A', Bloc P.1 (jFix t g P) (dualPt q)) *
            (∏ P ∈ primeSet (span {k₀}), Bloc P.1 1 (dualPt q)) *
            Vsharp W ((2 * Real.pi) ^ 4 / 27 * Real.exp (Real.log (dualNorm q / 81 * X /
              ((absNorm (span {D}) : ℝ) ^ 2 * nI A' ^ 2 * (absNorm (span {k₀}) : ℝ) ^ 2)))) /
            ((Real.sqrt (dualNorm q) : ℝ) : ℂ)) := by
    intro q hq
    rw [prod_rowJ hcop hA']
    exact dual_term_eq hK₀ hNpos hNeq W hX _ _ hq
  have hgood : ∀ q : DualIdx, cuspCoefQ K₀ dH D y q ≠ 0 → GoodQ q := by
    intro q hq
    by_contra hg
    apply hq
    unfold cuspCoefQ
    rw [ite_eq_right hg]
  refine tsum_eq_tsum_of_ne_zero_bij (fun q => dualPt q.1) ?_ ?_ ?_
  · -- injective on the support
    intro q q' hqq
    have h1 : cuspCoefQ K₀ dH D y q.1 ≠ 0 := fun h0 => q.2 (by simp [h0])
    have h2 : cuspCoefQ K₀ dH D y q'.1 ≠ 0 := fun h0 => q'.2 (by simp [h0])
    exact Subtype.ext (dualPt_inj (hgood _ h1) (hgood _ h2) hqq)
  · -- the support of the sum over `m` is in the range
    intro m hm
    have hdH0 : dH (-m) ≠ 0 := fun h0 => hm (by simp [h0])
    obtain ⟨q, hq, rfl, -⟩ := exists_good_of_ne hdH hdH0
    refine ⟨⟨q, ?_⟩, rfl⟩
    intro h0
    apply hm
    dsimp only
    rw [hval q hq]
    exact h0
  · -- the terms agree
    rintro ⟨q, hq⟩
    have h1 : cuspCoefQ K₀ dH D y q ≠ 0 := fun h0 => hq (by simp [h0])
    dsimp only
    rw [hval q (hgood q h1)]

/-- **The active sets of the rows** (the companion paper's `𝒜 = 𝒜_fix ∪ {p : p ∣ k₀}`): in the sum over the
subsets `𝒜` of the primes of `tg` and of `k₀`, the groups with an inactive prime of exponent `≢ 0` vanish.
The others are `𝒜_fix ∪ {P ∣ k₀}` with `𝒜_fix` admissible, and their inactive primes are those of `tg`
outside `𝒜_fix`. -/
theorem sum_rowPs_admissible {t g k₀ : 𝓞 K} (hcop : IsCoprime k₀ (t * g)) (F : Finset Pr → ℂ) :
    ∑ A ∈ (rowPs t g k₀).powerset, (∏ P ∈ rowPs t g k₀ \ A, locCoef P (rowJ t g k₀ P) 0) * F A =
      ∑ A' ∈ admissible t g, (∏ P ∈ primeSet (span {t * g}) \ A', locCoef P (jFix t g P) 0) *
        F (A' ∪ primeSet (span {k₀})) := by
  classical
  have hdisj : Disjoint (primeSet (span {t * g})) (primeSet (span {k₀})) := disjoint_primeSet hcop
  have hsub : ∀ A' ∈ admissible t g, A' ⊆ primeSet (span {t * g}) := fun A' h =>
    Finset.mem_powerset.1 (Finset.mem_filter.1 h).1
  -- the inactive primes of `𝒜_fix ∪ {P ∣ k₀}`
  have hsd : ∀ A' ∈ admissible t g, rowPs t g k₀ \ (A' ∪ primeSet (span {k₀})) =
      primeSet (span {t * g}) \ A' := by
    intro A' hA'
    ext P
    simp only [rowPs, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨h1, fun h => h2 (Or.inl h)⟩
      · exact absurd (Or.inr h1) h2
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inl h1, fun h => h.elim h2 (Finset.disjoint_left.1 hdisj h1)⟩
  have hloc : ∀ A' ∈ admissible t g,
      ∏ P ∈ rowPs t g k₀ \ (A' ∪ primeSet (span {k₀})), locCoef P (rowJ t g k₀ P) 0 =
        ∏ P ∈ primeSet (span {t * g}) \ A', locCoef P (jFix t g P) 0 := by
    intro A' hA'
    rw [hsd A' hA']
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [rowJ, ite_eq_right (Finset.disjoint_left.1 hdisj (Finset.mem_sdiff.1 hP).1)]
  have hinj : Set.InjOn (fun A' => A' ∪ primeSet (span {k₀})) (admissible t g : Set (Finset Pr)) := by
    intro A₁ h₁ A₂ h₂ he
    have e : ∀ A' ∈ admissible t g, (A' ∪ primeSet (span {k₀})) \ primeSet (span {k₀}) = A' := by
      intro A' hA'
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint
        (Finset.disjoint_of_subset_left (hsub A' hA') hdisj)]
    rw [← e A₁ h₁, ← e A₂ h₂]
    exact congrArg (· \ primeSet (span {k₀})) he
  symm
  rw [show (∑ A' ∈ admissible t g, (∏ P ∈ primeSet (span {t * g}) \ A', locCoef P (jFix t g P) 0) *
        F (A' ∪ primeSet (span {k₀}))) =
      ∑ A' ∈ admissible t g, (fun A => (∏ P ∈ rowPs t g k₀ \ A, locCoef P (rowJ t g k₀ P) 0) * F A)
        (A' ∪ primeSet (span {k₀})) from
      Finset.sum_congr rfl fun A' hA' => by simp only []; rw [hloc A' hA']]
  refine (Finset.sum_image (f := fun A => (∏ P ∈ rowPs t g k₀ \ A, locCoef P (rowJ t g k₀ P) 0) * F A)
    hinj).symm.trans ?_
  refine Finset.sum_subset ?_ fun A hA hnot => ?_
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.1 hA
    rw [Finset.mem_powerset, rowPs]
    exact Finset.union_subset_union (hsub A' hA') le_rfl
  · -- the groups outside the image vanish
    by_contra hne
    have hprod : ∏ P ∈ rowPs t g k₀ \ A, locCoef P (rowJ t g k₀ P) 0 ≠ 0 := left_ne_zero_of_mul hne
    have hact : ∀ P ∈ rowPs t g k₀, rowJ t g k₀ P % 6 ≠ 0 → P ∈ A := by
      intro P hP hj
      by_contra hPA
      exact hprod (prod_locCoef_zero_eq_zero (Finset.mem_sdiff.2 ⟨hP, hPA⟩) hj)
    have hK : primeSet (span {k₀}) ⊆ A := fun P hP => hact P (Finset.mem_union_right _ hP)
      (by rw [rowJ, ite_eq_left hP]; norm_num)
    apply hnot
    refine Finset.mem_image.2 ⟨A ∩ primeSet (span {t * g}), ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 Finset.inter_subset_right, fun P hP hj => ?_⟩
      refine Finset.mem_inter.2 ⟨hact P (Finset.mem_union_left _ hP) ?_, hP⟩
      rw [rowJ, ite_eq_right (Finset.disjoint_left.1 hdisj hP), jFix, Nat.mod_mod]
      exact hj
    · ext P
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨h1, -⟩ | h1)
        · exact h1
        · exact hK h1
      · intro h1
        have hP := (Finset.mem_powerset.1 hA) h1
        rcases Finset.mem_union.1 hP with h2 | h2
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h2

theorem goodQ_of_cuspCoefQ_ne {K₀ : ℝ} {dH : 𝓞 K → ℂ} {D y : 𝓞 K} {q : DualIdx}
    (h : cuspCoefQ K₀ dH D y q ≠ 0) : GoodQ q := by
  by_contra hg
  apply h
  unfold cuspCoefQ
  rw [ite_eq_right hg]

/-- The coefficients `cuspCoefQ` satisfy the size condition of `ThetaRows`, with `K₀` times the
constant of `ThetaSupp`. -/
theorem norm_cuspCoefQ_le {Kc K₀ : ℝ} (hK₀ : 0 ≤ K₀) {dH : 𝓞 K → ℂ} (hdH : ThetaSupp Kc dH)
    (D y : 𝓞 K) (q : DualIdx) :
    ‖cuspCoefQ K₀ dH D y q‖ ≤ K₀ * Kc * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2) := by
  have hKc := hdH.1
  unfold cuspCoefQ
  by_cases hq : GoodQ q
  · rw [ite_eq_left hq, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK₀,
      Complex.norm_conj, norm_ψc, mul_one, norm_div, Complex.norm_real, norm_norm]
    have h1 : ‖σO (dualPt q)‖ / ‖σO (dualPt q)‖ ≤ 1 := div_self_le_one _
    by_cases h0 : dH (-dualPt q) = 0
    · rw [h0, norm_zero, zero_mul, mul_zero]; positivity
    · obtain ⟨q', hq', hpt, hbd⟩ := exists_good_of_ne hdH h0
      obtain rfl := dualPt_inj hq' hq hpt
      calc K₀ * (‖dH (-dualPt q')‖ * (‖σO (dualPt q')‖ / ‖σO (dualPt q')‖)) ≤ K₀ * (‖dH (-dualPt q')‖ * 1) := by
            gcongr
        _ ≤ K₀ * (Kc * (3 : ℝ) ^ ((q'.2.1 : ℝ) / 6) * Real.sqrt (absNorm q'.2.2.2) * 1) := by gcongr
        _ = _ := by ring
  · rw [ite_eq_right hq, norm_zero]; positivity

/-- A sum over a finite type as a sum over `range` of its cardinality, through an enumeration `z`. -/
theorem finsum_eq_sum_range {α : Type*} [Fintype α] (e : α ≃ Fin (Fintype.card α)) (z : ℕ → α)
    (hz : ∀ i (hi : i < Fintype.card α), z i = e.symm ⟨i, hi⟩) (F : α → ℂ) :
    ∑ᶠ a, F a = ∑ i ∈ Finset.range (Fintype.card α), F (z i) := by
  rw [finsum_eq_sum_of_fintype, Finset.sum_range, ← e.symm.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [hz i i.2]

/-- The class of the active set of a row: `∏_{P∈𝒜_fix∪{P∣k₀}}π_P ≡ (∏_{P∈𝒜_fix}π_P)·k₀ (mod 9L)`. -/
theorem rcls_rows {L k₀ : 𝓞 K} (hk : QAdm k₀) {A' : Finset Pr} (hdisj : Disjoint A' (primeSet (span {k₀}))) :
    rcls L (A' ∪ primeSet (span {k₀})) =
      Ideal.Quotient.mk _ (∏ P ∈ A', πP P) * Ideal.Quotient.mk (span {9 * L}) k₀ := by
  rw [rcls, Finset.prod_union hdisj, map_mul, ← (eq_prod_of_adm hk).1]

open Classical in
/-- **`ThetaRows` from the data of the display** (the companion paper's Proposition 6.2 with its Lemmas
6.3 and 6.4, for the rows): under the data and the value formula of `KubotaTheta`, the displayed theta
transformation for the rows holds, with `J = 16`, `M = 9·72`, `KH` the number of residues modulo `72`,
`h(w) = V^♯((2π)⁴e^w/27)` and the coefficients `cuspCoefQ`. -/
theorem thetaRows_of_data {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {C : ℂ} (hC : C ≠ 0)
    (hval : ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n}))) :
    ThetaRows := by
  obtain ⟨D, dH, y, hDATA, hrows⟩ := compT_rows_dual hd hC hval
  set Kt : ℂ := (((8 * Real.pi / 27 : ℝ)) : ℂ) / (conj C * (2 * Real.pi * I * conj (σO δ3) / 9)) with hKt
  set K₀ : ℝ := ‖Kt‖ * (9 / 4) + 1 with hK₀
  have hK₀pos : 0 < K₀ := by positivity
  clear_value Kt K₀
  have hfin := finite_quot (72 : 𝓞 K) (by norm_num)
  let _ : Fintype (𝓞 K ⧸ span {(72 : 𝓞 K)}) := Fintype.ofFinite _
  set KH : ℕ := Fintype.card (𝓞 K ⧸ span {(72 : 𝓞 K)}) with hKH
  set e : (𝓞 K ⧸ span {(72 : 𝓞 K)}) ≃ Fin KH := Fintype.equivFin _ with he
  set hz : ℕ → 𝓞 K ⧸ span {(72 : 𝓞 K)} := fun i => if hi : i < KH then e.symm ⟨i, hi⟩ else 0 with hhz
  set ρA : (𝓞 K ⧸ span {9 * (72 : 𝓞 K)}) → Finset Pr → (𝓞 K ⧸ span {9 * (72 : 𝓞 K)}) :=
    fun ρ A => Ideal.Quotient.mk _ (∏ P ∈ A, πP P) * ρ with hρA
  refine ⟨16, fun α β hα hαβ => ?_⟩
  obtain ⟨Cw, -, hCw⟩ := Vsharp_decay hα hαβ (κ := (2 * Real.pi) ^ 4 / 27) (by positivity)
  refine ⟨Cw, 9 * 72, KH, K₀ * Kc, (absNorm (span {(72 : 𝓞 K)}) : ℝ), by norm_num,
    fun W hW hsupp N hN => ?_⟩
  obtain ⟨hsmooth, hbound⟩ := hCw W hW hsupp N hN
  refine ⟨fun w => Vsharp W ((2 * Real.pi) ^ 4 / 27 * Real.exp w), hsmooth, hbound,
    fun ξ u₀ t g ht hg _ => ?_⟩
  obtain ⟨φ₀, -, -, hbd, -, hk⟩ := hrows ξ u₀ t g ht hg
  refine ⟨fun ρ i A => cuspCoefQ K₀ (dH (hz i) (ρA ρ A)) (D (hz i) (ρA ρ A)) (y (hz i) (ρA ρ A)),
    fun ρ i A => D (hz i) (ρA ρ A), fun ρ i A => ⟨(hDATA _ _).1, ?_⟩,
    fun ρ i A q hq => goodQ_of_cuspCoefQ_ne hq,
    fun ρ i A q => norm_cuspCoefQ_le hK₀pos.le (hDATA _ _).2.2 _ _ q,
    fun k₀ hk1 hk2 hk3 hcop X hX => ?_⟩
  · -- `N(c₀) ≤ N(72)`
    have hdvd := absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_span_singleton).2 (hDATA (hz i) (ρA ρ A)).2.1)
    have h72 : absNorm (span {(72 : 𝓞 K)}) ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; norm_num
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h72) hdvd
  have hkA : QAdm k₀ := ⟨hk1, hk2, hk3⟩
  obtain ⟨C₀, hC₀, hid⟩ := hk k₀ hk1 hk2 hk3 hcop
  have hsubA : ∀ A ∈ admissible t g, A ⊆ primeSet (span {t * g}) := fun A hA =>
    Finset.mem_powerset.1 (Finset.mem_filter.1 hA).1
  have hdisjA : ∀ A ∈ admissible t g, Disjoint A (primeSet (span {k₀})) := fun A hA =>
    Finset.disjoint_of_subset_left (hsubA A hA) (disjoint_primeSet hcop)
  have hρ : ∀ A ∈ admissible t g,
      ρA (Ideal.Quotient.mk (span {9 * 72}) k₀) A = rcls 72 (A ∪ primeSet (span {k₀})) := by
    intro A hA
    rw [rcls_rows hkA (hdisjA A hA)]
  have hcne : ∀ (i : ℕ) (A : Finset Pr),
      σO (D (hz i) (rcls 72 (A ∪ primeSet (span {k₀}))) * ∏ P ∈ A ∪ primeSet (span {k₀}), πP P) ≠ 0 := by
    intro i A h0
    exact mul_ne_zero (hDATA _ _).1 (prod_πP_ne_zero _) (σO_injective (h0.trans (map_zero σO).symm))
  refine ⟨fun i A => if A ∈ admissible t g then Kt * (9 * I / 4) / (K₀ : ℂ) *
      fCoef 72 (φ₀ k₀) (repQ 72 (hz i)) *
      (∏ P ∈ primeSet (span {t * g}) \ A, locCoef P (jFix t g P) 0) * C₀ (hz i) (A ∪ primeSet (span {k₀})) *
      (((Complex.normSq (σO (D (hz i) (rcls 72 (A ∪ primeSet (span {k₀}))) *
          ∏ P ∈ A ∪ primeSet (span {k₀}), πP P)) : ℝ) : ℂ) *
        (-(σO (D (hz i) (rcls 72 (A ∪ primeSet (span {k₀}))) * ∏ P ∈ A ∪ primeSet (span {k₀}), πP P) ^ 2))⁻¹)
    else 0, fun i A => ?_, ?_⟩
  · -- the scalars have modulus at most `1`
    dsimp only
    split_ifs with hA
    · have hmem : A ∪ primeSet (span {k₀}) ∈ (rowPs t g k₀).powerset := by
        rw [Finset.mem_powerset, rowPs]
        exact Finset.union_subset_union (hsubA A hA) le_rfl
      have h1 : ‖Kt * (9 * I / 4) / (K₀ : ℂ)‖ ≤ 1 := by
        rw [norm_div, norm_mul, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_of_nonneg hK₀pos.le, div_le_one hK₀pos]
        have h9 : ‖(9 : ℂ)‖ = 9 := by norm_num
        have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
        rw [h9, h4, hK₀]
        linarith
      have h2 : ‖fCoef 72 (φ₀ k₀) (repQ 72 (hz i))‖ ≤ 1 :=
        norm_fCoef_le 72 (by norm_num) (φ₀ k₀) (fun x => hbd k₀ x) _
      have h3 := norm_prod_locCoef_zero_le (primeSet (span {t * g}) \ A) (jFix t g)
      have h4 : ‖((Complex.normSq (σO (D (hz i) (rcls 72 (A ∪ primeSet (span {k₀}))) *
          ∏ P ∈ A ∪ primeSet (span {k₀}), πP P)) : ℝ) : ℂ) *
          (-(σO (D (hz i) (rcls 72 (A ∪ primeSet (span {k₀}))) * ∏ P ∈ A ∪ primeSet (span {k₀}), πP P) ^ 2))⁻¹‖ =
          1 := by
        have hn := norm_pos_iff.2 (hcne i A)
        rw [norm_mul, norm_inv, norm_neg, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
        field_simp
      rw [norm_mul, norm_mul, norm_mul, norm_mul, hC₀ _ _ hmem, h4, mul_one, mul_one]
      calc ‖Kt * (9 * I / 4) / (K₀ : ℂ)‖ * ‖fCoef 72 (φ₀ k₀) (repQ 72 (hz i))‖ *
            ‖∏ P ∈ primeSet (span {t * g}) \ A, locCoef P (jFix t g P) 0‖ ≤ 1 * 1 * 1 := by
            gcongr
        _ = 1 := by norm_num
    · rw [norm_zero]; exact zero_le_one
  · -- the identity
    rw [hid W α β hα hαβ hsupp hW N (fun i hi => hN i (by omega)) X hX,
      finsum_eq_sum_range e hz (fun i hi => by rw [hhz]; exact dite_eq_left hi), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_rowPs_admissible hcop, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA => ?_
    dsimp only
    rw [ite_eq_left hA, hρ A hA,
      dual_sum_eq (hDATA _ _).2.2 (hDATA _ _).1 hkA hcop (hsubA A hA) W hX hK₀pos.ne']
    push_cast
    field_simp

/-- **The theta transformation for the rows, from the Kubota–Patterson theorem** (S5f-6, round 360's
target): the display `KubotaTheta` (round 361) implies the display `ThetaRows` (round 341). -/
theorem thetaRows_of_kubota (hK : KubotaTheta) : ThetaRows := by
  obtain ⟨θ, Kc, C, c₀, cP, cM, τ, tP, tM, hC, h1, h2, h3, h4, h5, h6, h7, h8, h9, hv⟩ := hK
  exact thetaRows_of_data ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hC
    fun n b hn hb hsq h6' => (hv n b hn hb hsq h6').2

/-- **The half-plane from the Kubota–Patterson theorem alone**: `ζ(s)L(s, χ₋₃) ≠ 0` on `Re s > 11/12`
from the display `KubotaTheta`, through round 359's `ne_zero_of_thetaRows`. -/
theorem ne_zero_of_kubotaTheta (hK : KubotaTheta) {s : ℂ} (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_thetaRows (thetaRows_of_kubota hK) hs

end Eis

end

#print axioms Eis.dualPt_inj
#print axioms Eis.dualPt_neg
#print axioms Eis.exists_good_of_ne
#print axioms Eis.prod_rowJ
#print axioms Eis.normSq_cusp
#print axioms Eis.dualNorm_pos
#print axioms Eis.dual_term_eq
#print axioms Eis.dual_sum_eq
#print axioms Eis.sum_rowPs_admissible
#print axioms Eis.goodQ_of_cuspCoefQ_ne
#print axioms Eis.norm_cuspCoefQ_le
#print axioms Eis.finsum_eq_sum_range
#print axioms Eis.rcls_rows
#print axioms Eis.thetaRows_of_data
#print axioms Eis.thetaRows_of_kubota
#print axioms Eis.ne_zero_of_kubotaTheta
