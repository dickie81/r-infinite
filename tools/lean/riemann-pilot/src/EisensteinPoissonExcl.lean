import EisensteinGaussTransform
import PlaneMajorant

/-! # Poisson summation with excluded primes (round 303)

S4 of round 291's plan, part 3: the companion paper's Lemma 4.2 in the pilot's normalization, and
its form for round 301's majorant `Φ`.

* **Inclusion–exclusion** (`indicator_not_dvd`): for pairwise coprime `π_i`,
  `1_{π_i ∤ u for all i ∈ S} = Σ_{T⊆S} (−1)^{|T|}·1_{d_T ∣ u}` with `d_T = ∏_{i∈T} π_i`.
* **`poisson_excl`**: for `f` periodic modulo `c ≠ 0` and Schwartz `F`,
  `Σ_{u : π_i ∤ u ∀i} f(u)F(σu) = Σ_{T⊆S} (−1)^{|T|}·2/(√3·N(c)·N(d_T))
  ·Σ_μ G_c(f(d_T·), μ)·𝓕F(conj(2σ(μ)/σ(δc))/conj σ(d_T))`.
  Each term reindexes `u = d_T ℓ` (`tsum_dvd_eq`) and applies round 295's `eis_poisson_gaussTr`
  to `ℓ ↦ f(d_T ℓ)` against `F(σ(d_T)·)` (round 294's `affS`, `fourier_affS`).
* **The dual weight** `G(ρ) = 𝓕Φ(ρ)` (`dualG`): `𝓕Φ(w) = G(|w|)` (`fourier_Phi_eq_dualG`, by round
  301's `fourier_Phi_rot`); `G` is smooth (`dualG_contDiff`), its derivatives are bounded
  (`dualG_bounded`), and it vanishes on `[R, ∞)` (`exists_dualG_eq_zero`). These are the
  hypotheses on `G` in round 302's `MellinSep.mellin_of_dual` and `MellinSep.bilinear_dual_bound`.
* **`poisson_excl_Phi`**: for `H > 0`,
  `Σ_{u : π_i ∤ u ∀i} f(u)·Φ(σu/√H) = Σ_{T⊆S} (−1)^{|T|}·2H/(√3·N(c)·N(d_T))
  ·Σ_μ G_c(f(d_T·), μ)·G(√(4H·N(μ)/(3·N(c)·N(d_T))))`, using `|σ(δ)|² = 3` (`normSq_σO_δ3`).

The paper's Lemma 4.2 also evaluates the Gauss transform of a primitive character `χ` as
`√N(𝔪)·γ(χ)·χ̄(h)`; in the pilot that is round 295's `gaussTr_prod_primes`, applied when the
character is fixed.
-/

open NumberField Complex Ideal
open scoped ComplexConjugate FourierTransform RealInnerProductSpace ContDiff SchwartzMap

noncomputable section

namespace Eis


open Classical in
/-- **Inclusion–exclusion over a set of pairwise coprime primes**:
`1_{π_i ∤ u for all i ∈ S} = Σ_{T ⊆ S} (−1)^{|T|}·1_{∏_{i∈T} π_i ∣ u}`. An instance of
`indicator_forall_not` (round 332), since a product of pairwise coprime divisors divides `u`. -/
theorem indicator_not_dvd {ι : Type*} [DecidableEq ι] (S : Finset ι) (π : ι → 𝓞 K)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j)) (u : 𝓞 K) :
    (if ∀ i ∈ S, ¬ π i ∣ u then (1 : ℂ) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (if (∏ i ∈ T, π i) ∣ u then 1 else 0) := by
  rw [indicator_forall_not S (fun i => π i ∣ u)]
  refine Finset.sum_congr rfl fun T hT => ?_
  congr 1
  refine if_congr ⟨fun h => ?_, fun h i hi => (Finset.dvd_prod_of_mem π hi).trans h⟩ rfl rfl
  exact Finset.prod_dvd_of_coprime (fun i hi j hj hij =>
    hcop i (Finset.mem_powerset.1 hT hi) j (Finset.mem_powerset.1 hT hj) hij) h

/-- A function periodic modulo `c ≠ 0` is bounded. -/
theorem exists_bound_of_periodic (c : 𝓞 K) (hc : c ≠ 0) (f : 𝓞 K → ℂ)
    (hf : ∀ z u, f (z + c * u) = f z) : ∃ B, ∀ z, ‖f z‖ ≤ B := by
  have : Finite (𝓞 K ⧸ span {c}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {c}) := Fintype.ofFinite _
  refine ⟨∑ r : 𝓞 K ⧸ span {c}, ‖f (repQ c r)‖, fun z => ?_⟩
  rw [periodic_congr c f hf (repQ_mk c (Ideal.Quotient.mk (span {c}) z)).symm]
  exact Finset.single_le_sum (f := fun r => ‖f (repQ c r)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

open Classical in
/-- `Σ_u 1_{d ∣ u}·g(u) = Σ_ℓ g(dℓ)` for `d ≠ 0` (`tsum_ite_dvd_eq`, since round 332). -/
theorem tsum_dvd_eq (d : 𝓞 K) (hd : d ≠ 0) (g : 𝓞 K → ℂ) :
    ∑' u : 𝓞 K, (if d ∣ u then g u else 0) = ∑' ℓ : 𝓞 K, g (d * ℓ) := by
  convert tsum_ite_dvd_eq d hd g

open Classical in
/-- **Poisson summation with excluded primes** (the companion paper's Lemma 4.2, in the pilot's
normalization): for `f` periodic modulo `c ≠ 0`, a Schwartz `F` and pairwise coprime `π_i ≠ 0`,
`Σ_{u : π_i ∤ u ∀i∈S} f(u)F(σu) = Σ_{T⊆S} (−1)^{|T|}·2/(√3·N(c)·N(d_T))
  ·Σ_μ G_c(f(d_T·), μ)·𝓕F(conj(2σ(μ)/σ(δc))/conj σ(d_T))` with `d_T = ∏_{i∈T} π_i`. -/
theorem poisson_excl (F : SchwartzMap ℂ ℂ) (c : 𝓞 K) (hc : c ≠ 0) (f : 𝓞 K → ℂ)
    (hf : ∀ z u, f (z + c * u) = f z) {ι : Type*} [DecidableEq ι] (S : Finset ι) (π : ι → 𝓞 K)
    (hπ : ∀ i ∈ S, π i ≠ 0) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j)) :
    ∑' u : 𝓞 K, (if ∀ i ∈ S, ¬ π i ∣ u then f u else 0) * F (σO u) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        (((2 / (Real.sqrt 3 * (absNorm (span {c}) : ℝ) *
            (absNorm (span {∏ i ∈ T, π i}) : ℝ)) : ℝ) : ℂ) *
          ∑' μ : 𝓞 K, gaussTr c (fun z => f ((∏ i ∈ T, π i) * z)) μ *
            𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c)) / conj (σO (∏ i ∈ T, π i)))) := by
  obtain ⟨B, hB⟩ := exists_bound_of_periodic c hc f hf
  -- each term of the inclusion–exclusion
  set g : Finset ι → 𝓞 K → ℂ := fun T u =>
    (-1 : ℂ) ^ T.card * ((if (∏ i ∈ T, π i) ∣ u then 1 else 0) * f u * F (σO u)) with hg
  have hsplit : ∀ u, (if ∀ i ∈ S, ¬ π i ∣ u then f u else 0) * F (σO u) =
      ∑ T ∈ S.powerset, g T u := by
    intro u
    have h := indicator_not_dvd S π hcop u
    have e : (if ∀ i ∈ S, ¬ π i ∣ u then f u else 0) =
        (if ∀ i ∈ S, ¬ π i ∣ u then (1 : ℂ) else 0) * f u := by split_ifs <;> ring
    rw [e, h, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [hg]; ring
  have hsum : ∀ T ∈ S.powerset, Summable (g T) := by
    intro T _
    refine Summable.of_norm_bounded ((summable_σO F).norm.mul_left B) fun u => ?_
    simp only [hg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h01 : ‖(if (∏ i ∈ T, π i) ∣ u then (1 : ℂ) else 0)‖ ≤ 1 := by
      split_ifs <;> simp
    calc ‖(if (∏ i ∈ T, π i) ∣ u then (1 : ℂ) else 0)‖ * ‖f u‖ * ‖F (σO u)‖
        ≤ 1 * B * ‖F (σO u)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul h01 (hB u) (norm_nonneg _) zero_le_one)
            (norm_nonneg _)
      _ = B * ‖F (σO u)‖ := by ring
  rw [tsum_congr hsplit, Summable.tsum_finsetSum hsum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT := Finset.mem_powerset.1 hT
  set d : 𝓞 K := ∏ i ∈ T, π i with hd
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => hπ i (hT hi)
  have hσd : σO d ≠ 0 := fun h => hd0 (σO_injective (h.trans (map_zero σO).symm))
  -- reindex `u = dℓ`
  have h1 : ∑' u : 𝓞 K, g T u = (-1 : ℂ) ^ T.card * ∑' ℓ : 𝓞 K, f (d * ℓ) * F (σO (d * ℓ)) := by
    simp only [hg, ← hd]
    rw [tsum_mul_left]
    congr 1
    rw [← tsum_dvd_eq d hd0 (fun u => f u * F (σO u))]
    refine tsum_congr fun u => ?_
    split_ifs <;> ring
  -- Poisson for `ℓ ↦ f(dℓ)` against `F(σd·)`
  have hfd : ∀ z u, f (d * (z + c * u)) = f (d * z) := fun z u => by
    rw [mul_add, mul_left_comm]; exact hf _ _
  have h2 : ∑' ℓ : 𝓞 K, f (d * ℓ) * F (σO (d * ℓ)) =
      ∑' ℓ : 𝓞 K, f (d * ℓ) * affS F 0 (σO d) hσd (σO ℓ) := by
    refine tsum_congr fun ℓ => ?_
    rw [affS_apply, zero_add, map_mul]
  have h3 := eis_poisson_gaussTr (affS F 0 (σO d) hσd) c hc (fun z => f (d * z)) hfd
  rw [h1, h2, h3]
  have h4 : ∀ μ : 𝓞 K, 𝓕 (affS F 0 (σO d) hσd : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c))) =
      ((absNorm (span {d}) : ℝ) : ℂ)⁻¹ *
        𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c)) / conj (σO d)) := by
    intro μ
    rw [fourier_affS, inner_zero_left, AddChar.map_zero_eq_one, normSq_σO]
    simp
  simp_rw [h4]
  have hN : (absNorm (span {d}) : ℝ) ≠ 0 := by
    have : absNorm (span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
    exact_mod_cast this
  have hc3 : Real.sqrt 3 * (absNorm (span {c}) : ℝ) ≠ 0 := by
    have : absNorm (span {c}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
    have h3 : Real.sqrt 3 ≠ 0 := by positivity
    exact mul_ne_zero h3 (by exact_mod_cast this)
  rw [show (fun μ : 𝓞 K => gaussTr c (fun z => f (d * z)) μ *
      (((absNorm (span {d}) : ℝ) : ℂ)⁻¹ *
        𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c)) / conj (σO d)))) =
      fun μ => ((absNorm (span {d}) : ℝ) : ℂ)⁻¹ * (gaussTr c (fun z => f (d * z)) μ *
        𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c)) / conj (σO d))) by
      funext μ; ring, tsum_mul_left]
  push_cast
  field_simp

/-! ### The majorant's dual weight -/

/-- The dual weight `G(ρ) = 𝓕Φ(ρ)` of round 301's majorant, on the real line. -/
def dualG (ρ : ℝ) : ℂ := 𝓕 (Majorant.Phi : ℂ → ℂ) (ρ : ℂ)

/-- **`𝓕Φ` is a function of `|w|`**: `𝓕Φ(w) = G(|w|)`. -/
theorem fourier_Phi_eq_dualG (w : ℂ) : 𝓕 (Majorant.Phi : ℂ → ℂ) w = dualG ‖w‖ := by
  have hw : w = ((Circle.exp (Complex.arg w) : Circle) : ℂ) * ((‖w‖ : ℝ) : ℂ) := by
    rw [Circle.coe_exp, mul_comm]; exact (norm_mul_exp_arg_mul_I w).symm
  rw [dualG]
  conv_lhs => rw [hw]
  exact Majorant.fourier_Phi_rot _ _

theorem dualG_contDiff : ContDiff ℝ ∞ dualG := by
  have h : dualG = ((𝓕 Majorant.Phi : 𝓢(ℂ, ℂ)) : ℂ → ℂ) ∘ ofRealCLM := by
    funext ρ; simp [dualG, SchwartzMap.fourier_coe]
  rw [h]
  exact ((𝓕 Majorant.Phi : 𝓢(ℂ, ℂ)).smooth ⊤).comp ofRealCLM.contDiff

theorem dualG_bounded (n : ℕ) : ∃ C, ∀ ρ, ‖iteratedFDeriv ℝ n dualG ρ‖ ≤ C := by
  have h : dualG = ((𝓕 Majorant.Phi : 𝓢(ℂ, ℂ)) : ℂ → ℂ) ∘ ofRealCLM := by
    funext ρ; simp [dualG, SchwartzMap.fourier_coe]
  obtain ⟨C, hC⟩ := (𝓕 Majorant.Phi : 𝓢(ℂ, ℂ)).decay 0 n
  refine ⟨C, fun ρ => ?_⟩
  rw [h, ofRealCLM.iteratedFDeriv_comp_right ((𝓕 Majorant.Phi : 𝓢(ℂ, ℂ)).smooth ⊤) ρ
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [ofRealCLM_norm, Finset.prod_const_one, mul_one]
  have := hC.2 (ofRealCLM ρ)
  simpa using this

theorem exists_dualG_eq_zero : ∃ R : ℝ, 0 < R ∧ ∀ ρ, R ≤ ρ → dualG ρ = 0 := by
  obtain ⟨R, hR, h⟩ := Majorant.exists_fourier_Phi_eq_zero
  refine ⟨R, hR, fun ρ hρ => h _ ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hρ.trans (le_abs_self ρ)

/-- `|σ(δ)|² = 3`. -/
theorem normSq_σO_δ3 : Complex.normSq (σO δ3) = 3 := by
  rw [σO_δ3, Complex.normSq_mul, Complex.normSq_I, mul_one, Complex.normSq_mul,
    Complex.normSq_ofReal]
  have h := varpi_re_im.2
  simp only [Complex.normSq_ofNat]
  nlinarith [h]

open Classical in
/-- **Lemma 4.2 with round 301's majorant**: for `H > 0`,
`Σ_{u : π_i ∤ u ∀i∈S} f(u)·Φ(σu/√H) = Σ_{T⊆S} (−1)^{|T|}·2H/(√3·N(c)·N(d_T))
  ·Σ_μ G_c(f(d_T·), μ)·G(√(4H·N(μ)/(3·N(c)·N(d_T))))` with `G = dualG`. -/
theorem poisson_excl_Phi (H : ℝ) (hH : 0 < H) (c : 𝓞 K) (hc : c ≠ 0) (f : 𝓞 K → ℂ)
    (hf : ∀ z u, f (z + c * u) = f z) {ι : Type*} [DecidableEq ι] (S : Finset ι) (π : ι → 𝓞 K)
    (hπ : ∀ i ∈ S, π i ≠ 0) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j)) :
    ∑' u : 𝓞 K, (if ∀ i ∈ S, ¬ π i ∣ u then f u else 0) *
        Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        (((2 * H / (Real.sqrt 3 * (absNorm (span {c}) : ℝ) *
            (absNorm (span {∏ i ∈ T, π i}) : ℝ)) : ℝ) : ℂ) *
          ∑' μ : 𝓞 K, gaussTr c (fun z => f ((∏ i ∈ T, π i) * z)) μ *
            dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
              (3 * (absNorm (span {c}) : ℝ) * (absNorm (span {∏ i ∈ T, π i}) : ℝ))))) := by
  have hsH : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.2 hH
  have hb : ((Real.sqrt H)⁻¹ : ℂ) ≠ 0 := by
    rw [ne_eq, inv_eq_zero]; exact_mod_cast hsH.ne'
  set F : SchwartzMap ℂ ℂ := affS Majorant.Phi 0 ((Real.sqrt H)⁻¹ : ℂ) hb with hF
  have hFapp : ∀ w, F w = Majorant.Phi (w / (Real.sqrt H : ℂ)) := fun w => by
    rw [hF, affS_apply, zero_add, div_eq_inv_mul]
  have hL : ∀ u : 𝓞 K, (if ∀ i ∈ S, ¬ π i ∣ u then f u else 0) *
      Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      (if ∀ i ∈ S, ¬ π i ∣ u then f u else 0) * F (σO u) := fun u => by rw [hFapp]
  rw [tsum_congr hL, poisson_excl F c hc f hf S π hπ hcop]
  refine Finset.sum_congr rfl fun T _ => ?_
  set d : 𝓞 K := ∏ i ∈ T, π i with hd
  congr 1
  -- the Fourier transform of `F` at the dual points
  have hFF : ∀ ξ : ℂ, 𝓕 (F : ℂ → ℂ) ξ = (H : ℂ) * dualG ‖(Real.sqrt H : ℂ) * ξ‖ := by
    intro ξ
    rw [hF, fourier_affS, inner_zero_left, AddChar.map_zero_eq_one, ← fourier_Phi_eq_dualG]
    have h1 : Complex.normSq ((Real.sqrt H)⁻¹ : ℂ) = H⁻¹ := by
      rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hH.le]
    have h2 : ξ / conj ((Real.sqrt H)⁻¹ : ℂ) = (Real.sqrt H : ℂ) * ξ := by
      rw [map_inv₀, Complex.conj_ofReal, div_inv_eq_mul, mul_comm]
    rw [h1, h2]
    push_cast
    rw [inv_inv]; simp
  have hnorm : ∀ μ : 𝓞 K, ‖(Real.sqrt H : ℂ) * (conj (2 * σO μ / σO (δ3 * c)) / conj (σO d))‖ =
      Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
        (3 * (absNorm (span {c}) : ℝ) * (absNorm (span {d}) : ℝ))) := by
    intro μ
    rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm]
    congr 1
    rw [Complex.normSq_mul, Complex.normSq_div, Complex.normSq_conj, Complex.normSq_conj,
      Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hH.le,
      map_mul, Complex.normSq_mul, normSq_σO_δ3, normSq_σO, normSq_σO, normSq_σO,
      Complex.normSq_ofNat]
    ring
  simp_rw [hFF, hnorm]
  rw [show (fun μ : 𝓞 K => gaussTr c (fun z => f (d * z)) μ * ((H : ℂ) *
      dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
        (3 * (absNorm (span {c}) : ℝ) * (absNorm (span {d}) : ℝ)))))) =
      fun μ => (H : ℂ) * (gaussTr c (fun z => f (d * z)) μ *
        dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
          (3 * (absNorm (span {c}) : ℝ) * (absNorm (span {d}) : ℝ))))) by
      funext μ; ring, tsum_mul_left]
  push_cast
  ring

end Eis

end

#print axioms Eis.indicator_not_dvd
#print axioms Eis.exists_bound_of_periodic
#print axioms Eis.tsum_dvd_eq
#print axioms Eis.poisson_excl
#print axioms Eis.fourier_Phi_eq_dualG
#print axioms Eis.dualG_contDiff
#print axioms Eis.dualG_bounded
#print axioms Eis.exists_dualG_eq_zero
#print axioms Eis.normSq_σO_δ3
#print axioms Eis.poisson_excl_Phi
