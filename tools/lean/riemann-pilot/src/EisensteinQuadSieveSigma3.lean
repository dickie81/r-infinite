import EisensteinQuadSieveSigma4

/-! # The quadratic large sieve, part 4d: Heath-Brown's `Σ_3` for a pair (round 351)

S5e of round 312's plan, the second piece of S5e-4d.

* **Poisson summation for `Σ_3`** (`sig3`, `sig3_poisson`): for a pair of columns with greatest
  common divisor `G` and symmetric difference `D`, the pair's term of Heath-Brown's `Σ_3` is the
  sum of `Φ(σm/√M)ρ_D(m)` over all arguments `m` prime to `G`. Round 303's `poisson_excl_Phi` with
  `f = ρ_D` and the Gauss sum `G_c(ρ_D, μ) = ρ_D(μ)·√N(D)·γ(D)` (`gaussTr_q2_eq_q2`, from round
  345's `gaussTr_q2_eq` and `χ⁻¹ = χ` for a quadratic `χ`) give
  `Σ_3 = γ(D)·Σ_{T⊆G}(−1)^{|T|}·2M/(√3√N(D)N(T))·ρ_D(π_T)·Σ_μ ρ_D(μ)G(√(κ_T N(μ)))` with
  `κ_T = 4M/(3N(D)N(T))` and `G` the dual weight.
* **The dual sum over squarefree kernels, truncated at its support** (`dual_sqf_eq`): for
  `R² ≤ κK₁`, `R` the radius of the support of the dual weight, `w·Σ_μ ρ_D(μ)G(√(κN(μ)))` is the sum
  over the squarefree `d` with `N(d) ≤ K₁` of `ρ_D(d)` times the sum over the `e` prime to `D` of
  `G(√(κN(d))·N(e))` (`dualR` is `G` as a Schwartz function on the line): for `N(d) > K₁` every
  term vanishes.
* **The explicit formula for `Σ_3`** (`sig3_eq_main_add`): for `3R²N(D)N(G) ≤ 4MK₁`, round 348's
  `excl_eq_main_add` with the dual weight gives the main term
  `γ(D)·(2π/√3)(∫_0^∞Φ)∏_{Q∈D}(1 − N(Q)⁻¹)·Σ_{T⊆G}(−1)^{|T|}ρ_D(π_T)Σ_d ρ_D(d)√(M/(N(T)N(d)))`
  (round 347's `integral_dualG_Ioi` makes the two integrals equal, `integral_dualR_Ioi`) and the
  error `γ(D)·Σ_T (−1)^{|T|}·2M/(√3√N(D)N(T))·ρ_D(π_T)Σ_d ρ_D(d)Σ_{T'⊆D}(−1)^{|T'|}r_G(√(κ_T N(d))N(T'))`.
-/

open Complex MeasureTheory Set NumberField Ideal
open scoped Classical SchwartzMap FourierTransform

noncomputable section

namespace Eis

/-- The majorant's dual weight as a Schwartz function on the line. -/
def dualR : 𝓢(ℝ, ℂ) := onReal (𝓕 Majorant.Phi)

theorem dualR_apply (ρ : ℝ) : dualR ρ = dualG ρ := by
  simp [dualR, onReal_apply, dualG, SchwartzMap.fourier_coe]

theorem integral_dualR_Ioi : ∫ y in Ioi (0 : ℝ), dualR y = ∫ y in Ioi (0 : ℝ), PhiOnR y := by
  simp_rw [dualR_apply, PhiOnR, onReal_apply]
  exact integral_dualG_Ioi

theorem absNorm_mul_sq (d e : 𝓞 K) :
    (absNorm (span {d * e ^ 2}) : ℝ) = (absNorm (span {d}) : ℝ) * (absNorm (span {e}) : ℝ) ^ 2 := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, map_mul, map_pow]
  push_cast; ring

theorem dualG_sqrt_eq_zero {x : ℝ} (hx : RΦ ^ 2 ≤ x) : dualG (Real.sqrt x) = 0 := by
  refine dualG_eq_zero_of_ge ?_
  rw [← Real.sqrt_sq RΦ_pos.le]
  exact Real.sqrt_le_sqrt hx

/-- **The dual sum over squarefree kernels, truncated at its support**: for `κ > 0` and
`R² ≤ κK₁` (`R` the radius of the support of the dual weight), with `w` the number of units,
`w·Σ_μ ρ_D(μ)G(√(κN(μ))) = Σ_{d sqf, N(d) ≤ K₁} ρ_D(d)·Σ_{e prime to D} G(√(κN(d))·N(e))`. -/
theorem dual_sqf_eq {κ K₁ : ℝ} (hκ : 0 < κ) (hK : RΦ ^ 2 ≤ κ * K₁) {D : Finset Pr}
    (hD : D.Nonempty) :
    (Fintype.card (𝓞 K)ˣ : ℂ) *
        ∑' μ : 𝓞 K, q2 D μ * dualG (Real.sqrt (κ * (absNorm (span {μ}) : ℝ))) =
      ∑ d ∈ eltsLe K₁, if Squarefree (span {d}) then
        q2 D d * ∑' e : 𝓞 K, (if ∀ Q ∈ D, ¬ πP Q ∣ e then
          dualR (Real.sqrt (κ * (absNorm (span {d}) : ℝ)) * (absNorm (span {e}) : ℝ)) else 0)
      else 0 := by
  set f : 𝓞 K → ℂ := fun μ => q2 D μ * dualG (Real.sqrt (κ * (absNorm (span {μ}) : ℝ)))
    with hf
  have hfz : ∀ μ, μ ∉ eltsLe (RΦ ^ 2 / κ) → f μ = 0 := by
    intro μ hμ
    rw [mem_eltsLe, not_le, div_lt_iff₀ hκ] at hμ
    simp only [hf]
    rw [dualG_sqrt_eq_zero (by nlinarith), mul_zero]
  have hfs : Summable f := summable_of_ne_finset_zero hfz
  have hf0 : f 0 = 0 := by simp only [hf, q2_zero hD, zero_mul]
  obtain ⟨-, heq⟩ := sum_sqf_sq_iter f hfs hf0
  have hterm : ∀ d e : 𝓞 K, f (d * e ^ 2) = q2 D d * (if ∀ Q ∈ D, ¬ πP Q ∣ e then
      dualR (Real.sqrt (κ * (absNorm (span {d}) : ℝ)) * (absNorm (span {e}) : ℝ)) else 0) := by
    intro d e
    simp only [hf]
    rw [q2_mul, q2_sq, absNorm_mul_sq, dualR_apply]
    have hsq : Real.sqrt (κ * ((absNorm (span {d}) : ℝ) * (absNorm (span {e}) : ℝ) ^ 2)) =
        Real.sqrt (κ * (absNorm (span {d}) : ℝ)) * (absNorm (span {e}) : ℝ) := by
      rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hκ.le (Nat.cast_nonneg _)),
        Real.sqrt_sq (Nat.cast_nonneg _)]
    rw [hsq]
    split_ifs <;> ring
  have hbig : ∀ d : 𝓞 K, K₁ < (absNorm (span {d}) : ℝ) → ∀ e : 𝓞 K,
      (if ∀ Q ∈ D, ¬ πP Q ∣ e then
        dualR (Real.sqrt (κ * (absNorm (span {d}) : ℝ)) * (absNorm (span {e}) : ℝ)) else 0) =
        0 := by
    intro d hd e
    split_ifs with he
    · obtain ⟨Q, hQ⟩ := hD
      have he0 : e ≠ 0 := fun h => he Q hQ (h ▸ dvd_zero _)
      have h1 := one_le_absNorm_of_ne_zero he0
      rw [dualR_apply]
      refine dualG_eq_zero_of_ge ?_
      have hlt := mul_lt_mul_of_pos_left hd hκ
      have h2 : RΦ ≤ Real.sqrt (κ * (absNorm (span {d}) : ℝ)) := by
        rw [← Real.sqrt_sq RΦ_pos.le]
        exact Real.sqrt_le_sqrt (by linarith)
      have h3 : 0 ≤ Real.sqrt (κ * (absNorm (span {d}) : ℝ)) := Real.sqrt_nonneg _
      nlinarith
    · rfl
  have hzero : ∀ d ∉ eltsLe K₁,
      (if Squarefree (span {d}) then ∑' e : 𝓞 K, f (d * e ^ 2) else 0) = 0 := by
    intro d hd
    rw [mem_eltsLe, not_le] at hd
    split_ifs
    · rw [tsum_congr (hterm d)]
      simp only [hbig d hd, mul_zero, tsum_zero]
    · rfl
  show (Fintype.card (𝓞 K)ˣ : ℂ) * ∑' μ, f μ = _
  rw [← heq, tsum_eq_sum hzero]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · rw [tsum_congr (hterm d), tsum_mul_left]
  · rfl

/-- `γ(D)`: the Gauss sum of `ρ_D` at `1` over `|σc|`. -/
def gamD (D : Finset Pr) : ℂ := gamF πP D (fun P => quadR (𝓞 K ⧸ span {πP P}) ℂ)

/-- **The Gauss sum of `ρ_D`**: `G_c(ρ_D, μ) = ρ_D(μ)·√N(D)·γ(D)`, each `ρ_P` being quadratic. -/
theorem gaussTr_q2_eq_q2 (D : Finset Pr) (μ : 𝓞 K) :
    gaussTr (∏ P ∈ D, πP P) (q2 D) μ = q2 D μ * (((Real.sqrt (nI D)) : ℝ) : ℂ) * gamD D := by
  rw [gaussTr_q2_eq, norm_σO_eq_sqrt, absNorm_span_prod_πP, gamD, ← mul_assoc]
  congr 2
  unfold q2
  refine Finset.prod_congr rfl fun P _ => ?_
  have hq : (quadR (𝓞 K ⧸ span {πP P}) ℂ).IsQuadratic := (quadraticChar_isQuadratic _).comp _
  rw [hq.inv]

/-- **Heath-Brown's `Σ_3` for a pair of columns**: all arguments prime to `G`, weighted by the
majorant, against `ρ_D`. -/
def sig3 (M : ℝ) (G D : Finset Pr) : ℂ :=
  ∑' m : 𝓞 K, (if ∀ Q ∈ G, ¬ πP Q ∣ m then
    Majorant.Phi (σO m / (Real.sqrt M : ℂ)) else 0) * q2 D m

theorem coef_sqrt {M a b : ℝ} (ha : 0 < a) :
    2 * M / (Real.sqrt 3 * a * b) * Real.sqrt a = 2 * M / (Real.sqrt 3 * Real.sqrt a * b) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  set s := Real.sqrt a with hsdef
  have hss : s * s = a := Real.mul_self_sqrt ha.le
  rw [← hss]
  by_cases hb : b = 0
  · simp [hb]
  · field_simp

/-- **Poisson summation for `Σ_3`** (round 303's `poisson_excl_Phi` with `f = ρ_D`):
`Σ_3 = γ(D)·Σ_{T⊆G}(−1)^{|T|}·2M/(√3·√N(D)·N(T))·ρ_D(π_T)·Σ_μ ρ_D(μ)G(√(κ_T N(μ)))`,
`κ_T = 4M/(3N(D)N(T))`. -/
theorem sig3_poisson {M : ℝ} (hM : 0 < M) (G D : Finset Pr) :
    sig3 M G D = gamD D * ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card *
      ((((2 * M / (Real.sqrt 3 * Real.sqrt (nI D) * nI T)) : ℝ) : ℂ) *
        q2 D (∏ P ∈ T, πP P) *
        ∑' μ : 𝓞 K, q2 D μ *
          dualG (Real.sqrt (4 * M / (3 * nI D * nI T) * (absNorm (span {μ}) : ℝ)))) := by
  have hc := prod_πP_ne_zero D
  have h := poisson_excl_Phi M hM (∏ P ∈ D, πP P) hc (q2 D) (fun z u => q2_periodic D z u) G πP
    (fun i _ => (prime_πP i).ne_zero) (hcopPr G)
  have hL : sig3 M G D = ∑' u : 𝓞 K, (if ∀ i ∈ G, ¬ πP i ∣ u then q2 D u else 0) *
      Majorant.Phi (σO u / (Real.sqrt M : ℂ)) :=
    tsum_congr fun m => by split_ifs <;> ring
  rw [hL, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hgt : ∀ μ, gaussTr (∏ P ∈ D, πP P) (fun z => q2 D ((∏ i ∈ T, πP i) * z)) μ =
      q2 D (∏ i ∈ T, πP i) * (q2 D μ * (((Real.sqrt (nI D)) : ℝ) : ℂ) * gamD D) := by
    intro μ
    simp_rw [q2_mul]
    rw [gaussTr_const_mul _ hc, gaussTr_q2_eq_q2]
  simp_rw [hgt]
  rw [absNorm_span_prod_πP, absNorm_span_prod_πP]
  have hS : ∀ μ : 𝓞 K, q2 D (∏ i ∈ T, πP i) * (q2 D μ * (((Real.sqrt (nI D)) : ℝ) : ℂ) * gamD D) *
      dualG (Real.sqrt (4 * M * (absNorm (span {μ}) : ℝ) / (3 * nI D * nI T))) =
      (q2 D (∏ i ∈ T, πP i) * (((Real.sqrt (nI D)) : ℝ) : ℂ) * gamD D) *
        (q2 D μ * dualG (Real.sqrt (4 * M / (3 * nI D * nI T) * (absNorm (span {μ}) : ℝ)))) := by
    intro μ
    rw [show 4 * M * (absNorm (span {μ}) : ℝ) / (3 * nI D * nI T) =
      4 * M / (3 * nI D * nI T) * (absNorm (span {μ}) : ℝ) by ring]
    ring
  rw [tsum_congr hS, tsum_mul_left]
  have hcoef : ((2 * M / (Real.sqrt 3 * nI D * nI T) : ℝ) : ℂ) * (((Real.sqrt (nI D)) : ℝ) : ℂ) =
      ((2 * M / (Real.sqrt 3 * Real.sqrt (nI D) * nI T) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, coef_sqrt (nI_pos D)]
  rw [← hcoef]
  ring

theorem coef_main {M a b n : ℝ} (hM : 0 < M) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    2 * M / (Real.sqrt 3 * Real.sqrt a * b) *
        (2 * Real.pi / (Real.sqrt 3 * Real.sqrt (4 * M / (3 * a * b) * n))) =
      2 * Real.pi / Real.sqrt 3 * Real.sqrt (M / (b * n)) := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hR : 0 ≤ 2 * Real.sqrt M * Real.sqrt n / (Real.sqrt 3 * Real.sqrt a * Real.sqrt b) := by
    positivity
  have e1 : Real.sqrt (4 * M / (3 * a * b) * n) =
      2 * Real.sqrt M * Real.sqrt n / (Real.sqrt 3 * Real.sqrt a * Real.sqrt b) := by
    rw [← Real.sqrt_sq hR]
    congr 1
    rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hM.le, Real.sq_sqrt hn.le,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    field_simp
    ring
  have e2 : Real.sqrt (M / (b * n)) = Real.sqrt M / (Real.sqrt b * Real.sqrt n) := by
    rw [Real.sqrt_div hM.le, Real.sqrt_mul hb.le]
  rw [e1, e2]
  have hbb : b = Real.sqrt b * Real.sqrt b := (Real.mul_self_sqrt hb.le).symm
  have hMM : M = Real.sqrt M * Real.sqrt M := (Real.mul_self_sqrt hM.le).symm
  set sb := Real.sqrt b
  set sM := Real.sqrt M
  rw [hbb, hMM]
  field_simp

/-- **The explicit formula for `Σ_3`**: for `D ≠ ∅`, `M > 0` and `3R²N(D)N(G) ≤ 4MK₁`, with `w`
the number of units, `J = ∫_0^∞Φ`, `κ_T = 4M/(3N(D)N(T))` and the sums over the squarefree `d`
with `N(d) ≤ K₁`,
`w·Σ_3 = γ(D)·((2π/√3)J∏_{Q∈D}(1 − N(Q)⁻¹)Σ_{T⊆G}(−1)^{|T|}ρ_D(π_T)Σ_d ρ_D(d)√(M/(N(T)N(d)))
  + Σ_{T⊆G}(−1)^{|T|}·2M/(√3√N(D)N(T))·ρ_D(π_T)Σ_d ρ_D(d)Σ_{T'⊆D}(−1)^{|T'|}r_G(√(κ_T N(d))N(T')))`. -/
theorem sig3_eq_main_add {M K₁ : ℝ} (hM : 0 < M) (G : Finset Pr) {D : Finset Pr}
    (hD : D.Nonempty) (hK : 3 * RΦ ^ 2 * nI D * nI G ≤ 4 * M * K₁) :
    (Fintype.card (𝓞 K)ˣ : ℂ) * sig3 M G D =
      gamD D * (((2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), PhiOnR y) *
          (∏ Q ∈ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)) *
          ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * q2 D (∏ P ∈ T, πP P) *
            ∑ d ∈ eltsLe K₁, (if Squarefree (span {d}) then
              q2 D d * ((Real.sqrt (M / (nI T * (absNorm (span {d}) : ℝ))) : ℝ) : ℂ) else 0) +
        ∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card *
          ((((2 * M / (Real.sqrt 3 * Real.sqrt (nI D) * nI T)) : ℝ) : ℂ) *
            q2 D (∏ P ∈ T, πP P) *
            ∑ d ∈ eltsLe K₁, (if Squarefree (span {d}) then
              q2 D d * ∑ T' ∈ D.powerset, (-1 : ℂ) ^ T'.card *
                latErr dualR (Real.sqrt (4 * M / (3 * nI D * nI T) *
                  (absNorm (span {d}) : ℝ)) * nI T')
              else 0))) := by
  rw [sig3_poisson hM, ← mul_assoc, mul_comm (Fintype.card (𝓞 K)ˣ : ℂ) (gamD D), mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTG : T ⊆ G := Finset.mem_powerset.1 hT
  have hDp := nI_pos D
  have hTp := nI_pos T
  have hκ : 0 < 4 * M / (3 * nI D * nI T) := by positivity
  have hKT : RΦ ^ 2 ≤ 4 * M / (3 * nI D * nI T) * K₁ := by
    have hTG' := nI_mono hTG
    have hR := RΦ_pos
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 3 * RΦ ^ 2 * nI D * nI T ≤ 3 * RΦ ^ 2 * nI D * nI G := by
      have h0 : 0 ≤ 3 * RΦ ^ 2 * nI D := by positivity
      exact mul_le_mul_of_nonneg_left hTG' h0
    nlinarith
  have hS := dual_sqf_eq hκ hKT hD
  set C : ℂ := (((2 * M / (Real.sqrt 3 * Real.sqrt (nI D) * nI T)) : ℝ) : ℂ) with hC
  set q : ℂ := q2 D (∏ P ∈ T, πP P) with hq
  rw [show (Fintype.card (𝓞 K)ˣ : ℂ) * ((-1) ^ T.card * (C * q *
      ∑' μ : 𝓞 K, q2 D μ * dualG (Real.sqrt (4 * M / (3 * nI D * nI T) *
        (absNorm (span {μ}) : ℝ))))) =
      (-1) ^ T.card * (C * q * ((Fintype.card (𝓞 K)ˣ : ℂ) * ∑' μ : 𝓞 K, q2 D μ *
        dualG (Real.sqrt (4 * M / (3 * nI D * nI T) * (absNorm (span {μ}) : ℝ))))) by ring, hS]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with hd
  · have hN : (0 : ℝ) < absNorm (span {d}) := by
      refine Nat.cast_pos.2 (Nat.pos_of_ne_zero ?_)
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact sqf_ne_zero hd
    have hβ : 0 < Real.sqrt (4 * M / (3 * nI D * nI T) * (absNorm (span {d}) : ℝ)) :=
      Real.sqrt_pos.2 (mul_pos hκ hN)
    rw [excl_eq_main_add dualR hβ D, integral_dualR_Ioi]
    have hco := coef_main hM hDp hTp hN
    have hco' : C * ((2 * Real.pi / (Real.sqrt 3 *
        Real.sqrt (4 * M / (3 * nI D * nI T) * (absNorm (span {d}) : ℝ))) : ℝ) : ℂ) =
        ((2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) *
          ((Real.sqrt (M / (nI T * (absNorm (span {d}) : ℝ))) : ℝ) : ℂ) := by
      rw [hC, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hco]
    linear_combination (q2 D d * (∫ y in Ioi (0 : ℝ), PhiOnR y) *
      (∏ Q ∈ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)) * (-1) ^ T.card * q) * hco'
  · simp

end Eis

end

#print axioms Eis.dualR_apply
#print axioms Eis.integral_dualR_Ioi
#print axioms Eis.absNorm_mul_sq
#print axioms Eis.dualG_sqrt_eq_zero
#print axioms Eis.dual_sqf_eq
#print axioms Eis.gaussTr_q2_eq_q2
#print axioms Eis.coef_sqrt
#print axioms Eis.sig3_poisson
#print axioms Eis.coef_main
#print axioms Eis.sig3_eq_main_add
