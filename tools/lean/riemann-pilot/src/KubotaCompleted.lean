import KubotaContour

/-! # The completed sum as a contour integral of the theta series (round 378)

S5f-6 of round 360's plan, part 1. The companion paper writes: "`With $V_*$ from \eqref{eq:T} and its Mellin
transform defined before \eqref{eq:theta-weight}, Mellin inversion gives`" (its (A.13)), and "`We now compute
the normalization relating $\mathcal T(s,\Psi)$ to the Mellin transform of the derivative of $\Theta_\Psi$.`"
(its (A.16)). This file proves both for round 313's completed sum `compT`, from the value formula of the
display `Eis.KubotaTheta` (round 361), and combines them.

* **The support** (`twisted_support`, with `sqfree_cube_unique`, `δ3_eq_neg_ω_lam` and `ω_cube_eq`): if
  `φ(m/δ₃)·conj τ(−m) ≠ 0` for round 363's twist `φ` and `τ` under the support and size condition, then
  `m = δ₃·nb³` with `n, b` primary, `n` squarefree and `N(nb)` prime to `6`.
* **(A.16)** (`compD` and `thetaK`, definitions; **`theta_dirichlet`**, with `theta_term`, `theta_pow_id`,
  `norm_phiTw_le` and `mem_S_of_term_ne_zero`): for `Re s ≥ 5/3`, the Mellin transform of the twisted
  derivative series at `2s`, over `Γ(s + 1/3)Γ(s + 2/3)`, is `thetaK(C, s)·𝒯(s, Ψ)`.
* **(A.13)** (**`compT_mellin`**, with `compT_pow_id`, `mellin_Vstar_line_integrable` and the instance
  `countable_ideal`): `T(X; Ψ) = (1/2π)∫V̂_*(s − 1/2)𝒯(s, Ψ)X^{s−1/2} du` along `s = 2 + iu`.
* **Combined** (**`compT_theta`**, with `theta_scale_id` and `thetaK_mul_scale`): `T(X; Ψ)` is
  `(8π/27)/(C̄·2πiσ̄(δ₃)/9)` times the left side of round 376's `voronoi_FE` at `Z = 4π²X/27`.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics UniqueFactorizationMonoid
open scoped Topology ComplexConjugate

noncomputable section

namespace Eis

/-- **The cube part of an ideal is unique**: `D·E³ = D'·E'³` with `D, D'` squarefree and `E ≠ ⊥` gives
`D = D'` and `E = E'`. -/
theorem sqfree_cube_unique {D D' E E' : Ideal (𝓞 K)} (hD : Squarefree D) (hD' : Squarefree D')
    (hE : E ≠ ⊥) (h : D * E ^ 3 = D' * E' ^ 3) : D = D' ∧ E = E' := by
  have hD0 : D ≠ ⊥ := hD.ne_zero
  have hD'0 : D' ≠ ⊥ := hD'.ne_zero
  have hE3 : E ^ 3 ≠ ⊥ := pow_ne_zero 3 hE
  have hE' : E' ≠ ⊥ := by
    rintro rfl
    have h0 : D' * (⊥ : Ideal (𝓞 K)) ^ 3 = ⊥ := by simp
    rw [h0, Ideal.mul_eq_bot] at h
    rcases h with h | h
    · exact hD0 h
    · exact hE3 h
  have hE'3 : E' ^ 3 ≠ ⊥ := pow_ne_zero 3 hE'
  have hnf := congrArg normalizedFactors h
  rw [normalizedFactors_mul hD0 hE3, normalizedFactors_mul hD'0 hE'3, normalizedFactors_pow,
    normalizedFactors_pow] at hnf
  have hnd := (squarefree_iff_nodup_normalizedFactors hD0).1 hD
  have hnd' := (squarefree_iff_nodup_normalizedFactors hD'0).1 hD'
  have hc : ∀ P, Multiset.count P (normalizedFactors D) = Multiset.count P (normalizedFactors D') ∧
      Multiset.count P (normalizedFactors E) = Multiset.count P (normalizedFactors E') := by
    intro P
    have h1 := congrArg (Multiset.count P) hnf
    simp only [Multiset.count_add, Multiset.count_nsmul] at h1
    have a1 := Multiset.nodup_iff_count_le_one.1 hnd P
    have a2 := Multiset.nodup_iff_count_le_one.1 hnd' P
    omega
  have hDD : normalizedFactors D = normalizedFactors D' := Multiset.ext.2 fun P => (hc P).1
  have hEE : normalizedFactors E = normalizedFactors E' := Multiset.ext.2 fun P => (hc P).2
  exact ⟨associated_iff_eq.1 ((associated_iff_normalizedFactors_eq_normalizedFactors hD0 hD'0).2 hDD),
    associated_iff_eq.1 ((associated_iff_normalizedFactors_eq_normalizedFactors hE hE').2 hEE)⟩

/-- `δ₃ = −ω(ω − 1)`. -/
theorem δ3_eq_neg_ω_lam : δ3 = -(ω * (ω - 1)) := by
  unfold δ3; linear_combination ω_sq_add

theorem ω_cube_eq : ω * ω ^ 2 = (1 : 𝓞 K) := by rw [← pow_succ']; exact ω_cube

/-- **The support of the twisted coefficients**: if `φ(m/δ₃)·conj τ(−m) ≠ 0` for the twist `φ` of
round 363's `phiTw` and `τ` under the support and size condition, then `m = δ₃·nb³` with `n, b` primary,
`n` squarefree and `N(nb)` prime to `6`. -/
theorem twisted_support {Kc : ℝ} {τ : 𝓞 K → ℂ} (hτ : ThetaSupp Kc τ) (Ψ : Ideal (𝓞 K) → ℂ) {m : 𝓞 K}
    (hm : twAt (phiTw Ψ) m * conj (τ (-m)) ≠ 0) :
    ∃ n b : 𝓞 K, Primary n ∧ Primary b ∧ Squarefree (span {n}) ∧
      (absNorm (span {n * b})).Coprime 6 ∧ m = δ3 * (n * b ^ 3) := by
  classical
  have h1 : twAt (phiTw Ψ) m ≠ 0 := left_ne_zero_of_mul hm
  have h2 : τ (-m) ≠ 0 := fun h => hm (by rw [h, map_zero, mul_zero])
  have hdvd : δ3 ∣ m := by
    by_contra hd
    apply h1
    unfold twAt
    simp [hd]
  obtain ⟨x, rfl⟩ := hdvd
  rw [twAt_mul] at h1
  have hx : Primary x ∧ (absNorm (span {x})).Coprime 6 := by
    by_contra hx
    apply h1
    unfold phiTw
    simp only [hx, ite_false]
  obtain ⟨q, hq, hsq, hn3, hb3, -⟩ := hτ.2 _ h2
  -- the norms: `3^k N𝔫 N𝔟³ = 3 N(x)`
  have hN : (3 : ℕ) ^ q.2.1 * absNorm q.2.2.1 * absNorm q.2.2.2 ^ 3 = 3 * absNorm (span {x}) := by
    have e1 := normSq_dualPt hn3 hb3
    rw [hq, map_neg, Complex.normSq_neg, map_mul, Complex.normSq_mul, normSq_σO_δ3, normSq_σO] at e1
    unfold dualNorm at e1
    exact_mod_cast e1.symm
  have hx3 : (absNorm (span {x})).Coprime 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hx.2
  have hk : q.2.1 = 1 := by
    rcases Nat.lt_or_ge q.2.1 1 with h | h
    · have h0 : q.2.1 = 0 := by omega
      rw [h0, pow_zero, one_mul] at hN
      have hd : 3 ∣ absNorm q.2.2.1 * absNorm q.2.2.2 ^ 3 := ⟨_, hN⟩
      have hco : Nat.Coprime 3 (absNorm q.2.2.1 * absNorm q.2.2.2 ^ 3) :=
        Nat.Coprime.mul_right hn3.symm (Nat.Coprime.pow_right 3 hb3.symm)
      have := Nat.Coprime.eq_one_of_dvd hco hd
      omega
    · rcases Nat.lt_or_ge q.2.1 2 with h' | h'
      · omega
      · obtain ⟨j, hj⟩ : ∃ j, q.2.1 = j + 2 := ⟨q.2.1 - 2, by omega⟩
        rw [hj, pow_add] at hN
        have hd : 3 ∣ absNorm (span {x}) := ⟨3 ^ j * absNorm q.2.2.1 * absNorm q.2.2.2 ^ 3, by
          have : 3 * absNorm (span {x}) = 3 * (3 * (3 ^ j * absNorm q.2.2.1 * absNorm q.2.2.2 ^ 3)) := by
            rw [← hN]; ring
          omega⟩
        have := Nat.Coprime.eq_one_of_dvd hx3.symm hd
        omega
  -- the element: `u·n·b³ = ω·x`, so `x = nb³`
  obtain ⟨hn1, hn2⟩ := pgen_spec3 hn3
  obtain ⟨hb1, hb2⟩ := pgen_spec3 hb3
  have hq' := hq
  unfold dualPt at hq'
  rw [hk, pow_one, δ3_eq_neg_ω_lam] at hq'
  have hlam : (ω - 1 : 𝓞 K) ≠ 0 := fun h => by
    have := normSq_σO_lam
    rw [h, map_zero, map_zero] at this
    norm_num at this
  have hcanc : (q.1 : 𝓞 K) * (pgen q.2.2.1 * pgen q.2.2.2 ^ 3) = ω * x := by
    apply mul_left_cancel₀ hlam
    linear_combination hq'
  have hxeq : x = pgen q.2.2.1 * pgen q.2.2.2 ^ 3 := by
    have hprim : Primary (pgen q.2.2.1 * pgen q.2.2.2 ^ 3) := hn1.mul (primary_pow hb1 3)
    refine primary_unique hx.1 hprim ?_
    rw [Ideal.span_singleton_eq_span_singleton]
    refine ⟨q.1⁻¹ * ⟨ω, ω ^ 2, ω_cube_eq, by rw [mul_comm]; exact ω_cube_eq⟩, ?_⟩
    simp only [Units.val_mul]
    have hu : ((q.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (q.1 : 𝓞 K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc x * (((q.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ω) = ((q.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (ω * x) := by ring
      _ = ((q.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((q.1 : 𝓞 K) * (pgen q.2.2.1 * pgen q.2.2.2 ^ 3)) := by rw [hcanc]
      _ = _ := by rw [← mul_assoc, hu, one_mul]
  refine ⟨pgen q.2.2.1, pgen q.2.2.2, hn1, hb1, by rw [hn2]; exact hsq, ?_, by rw [hxeq]⟩
  have hx6 := hx.2
  rw [hxeq, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hn2, hb2, map_mul,
    map_pow] at hx6
  rw [← Ideal.span_singleton_mul_span_singleton, hn2, hb2, map_mul]
  exact Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hx6,
    Nat.Coprime.coprime_dvd_left (dvd_pow_self _ (by norm_num))
      (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hx6)⟩

/-- **The Dirichlet series of the completed sum**:
`𝒯(s, Ψ) = Σ_{𝔫,𝔟} ᾱ(𝔫)γ₂(𝔫)Ψ(𝔫)·ᾱ(𝔟)³Ψ(𝔟)³·N𝔫^{−s}N𝔟^{−3s+1/2}`. -/
def compD (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) (s : ℂ) : ℂ :=
  ∑' p : Ideal (𝓞 K) × Ideal (𝓞 K), gCoef ξ k f p.1 * dCoef ξ k f p.2 *
    (((absNorm p.1 : ℝ)) : ℂ) ^ (-s) * (((absNorm p.2 : ℝ)) : ℂ) ^ (-(3 * s) + 1 / 2)

/-- The constant of (A.16): `C̄·(2πi·σ̄(δ₃)/9)·2^{2s−1}(4π√3/9)^{−(2s+1)}`. -/
def thetaK (C : ℂ) (s : ℂ) : ℂ :=
  conj C * (2 * Real.pi * I * conj (σO δ3) / 9) *
    (2 ^ (2 * s - 1) * (((4 * Real.pi * Real.sqrt 3 / 9 : ℝ)) : ℂ) ^ (-(2 * s + 1)))

theorem norm_phiTw_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f x : 𝓞 K) :
    ‖phiTw (twistPsi ξ k f) x‖ ≤ 1 := by
  unfold phiTw
  split_ifs
  · rw [norm_mul, norm_pow]
    calc ‖sym6 δ3 (span {x})‖ ^ 2 * ‖twistPsi ξ k f (span {x})‖ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ (norm_nonneg _) (norm_sym6_le _ _)) (norm_twistPsi_le ξ k f _)
            (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp

/-- `r_b·(ρr_nr_b³)^{−(2s+1)} = ρ^{−(2s+1)}·r_n^{−1}r_b^{−3}(r_n²)^{−s}(r_b²)^{−3s+1/2}`. -/
theorem theta_pow_id {ρ rn rb : ℝ} (hρ : 0 < ρ) (hn : 0 < rn) (hb : 0 < rb) (s : ℂ) :
    (rb : ℂ) * (((ρ * rn * rb ^ 3 : ℝ)) : ℂ) ^ (-(2 * s + 1)) =
      ((ρ : ℝ) : ℂ) ^ (-(2 * s + 1)) * (((rn : ℂ))⁻¹ * ((rb : ℂ) ^ 3)⁻¹ *
        (((rn ^ 2 : ℝ)) : ℂ) ^ (-s) * (((rb ^ 2 : ℝ)) : ℂ) ^ (-(3 * s) + 1 / 2)) := by
  rw [ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp hρ, ofReal_cpow_eq_exp (by positivity),
    ofReal_cpow_eq_exp (by positivity), ofReal_eq_exp hb, ofReal_eq_exp hn, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hρ.ne' hn.ne', Real.log_pow,
    Real.log_pow, Real.log_pow]
  push_cast
  ring

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K)

/-- **One term of (A.16)**: at `m = δ₃·nb³` with `n = pgen 𝔫`, `b = pgen 𝔟`, the term of the theta
Dirichlet series is the constant of (A.16) times the term of `𝒯(s, Ψ)` at `(𝔫, 𝔟)`. -/
theorem theta_term {τ : 𝓞 K → ℂ} {C : ℂ}
    (hval : ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})))
    {𝔫 𝔟 : Ideal (𝓞 K)} (hsq : Squarefree 𝔫) (h𝔫 : (absNorm 𝔫).Coprime 6) (h𝔟 : (absNorm 𝔟).Coprime 6)
    (s : ℂ) :
    twAt (phiTw (twistPsi ξ k f)) (δ3 * (pgen 𝔫 * pgen 𝔟 ^ 3)) * conj (τ (-(δ3 * (pgen 𝔫 * pgen 𝔟 ^ 3)))) *
        (2 * Real.pi * I * conj (σO (δ3 * (pgen 𝔫 * pgen 𝔟 ^ 3))) / 9) *
        (2 ^ (2 * s - 1) *
          (((4 * Real.pi * ‖σO (δ3 * (pgen 𝔫 * pgen 𝔟 ^ 3))‖ / 9 : ℝ)) : ℂ) ^ (-(2 * s + 1))) =
      thetaK C s * (gCoef ξ k f 𝔫 * dCoef ξ k f 𝔟 *
        (((absNorm 𝔫 : ℝ)) : ℂ) ^ (-s) * (((absNorm 𝔟 : ℝ)) : ℂ) ^ (-(3 * s) + 1 / 2)) := by
  obtain ⟨hn1, hn2⟩ := pgen_spec6 h𝔫
  obtain ⟨hb1, hb2⟩ := pgen_spec6 h𝔟
  set n := pgen 𝔫 with hn
  set b := pgen 𝔟 with hb
  have h6 : (absNorm (span {n * b})).Coprime 6 := by
    rw [← Ideal.span_singleton_mul_span_singleton, hn2, hb2, map_mul]
    exact Nat.coprime_mul_iff_left.2 ⟨h𝔫, h𝔟⟩
  have hsq' : Squarefree (span {n}) := by rw [hn2]; exact hsq
  have hcr := coef_realization (twistPsi ξ k f) (twistPsi_mul ξ k f) hn1 hb1 h6 (hval n b hn1 hb1 hsq' h6)
  rw [hn2, hb2] at hcr
  have hrn : ‖σO n‖ ^ 2 = (absNorm 𝔫 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, normSq_σO, hn2]
  have hrb : ‖σO b‖ ^ 2 = (absNorm 𝔟 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, normSq_σO, hb2]
  have hn0 : 0 < ‖σO n‖ := by
    have := one_le_absNorm_of_coprime6 h𝔫; nlinarith [norm_nonneg (σO n)]
  have hb0 : 0 < ‖σO b‖ := by
    have := one_le_absNorm_of_coprime6 h𝔟; nlinarith [norm_nonneg (σO b)]
  have hsqrt : Real.sqrt (absNorm 𝔟) = ‖σO b‖ := by
    rw [← hrb, Real.sqrt_sq (norm_nonneg _)]
  have h3 : ‖σO δ3‖ = Real.sqrt 3 := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_σO_δ3_sq]
  have hx : 4 * Real.pi * ‖σO (δ3 * (n * b ^ 3))‖ / 9 =
      (4 * Real.pi * Real.sqrt 3 / 9) * ‖σO n‖ * ‖σO b‖ ^ 3 := by
    rw [map_mul, map_mul, map_pow, norm_mul, norm_mul, norm_pow, h3]; ring
  have hpow := theta_pow_id (ρ := 4 * Real.pi * Real.sqrt 3 / 9) (by positivity) hn0 hb0 s
  have hσ : σO (δ3 * (n * b ^ 3)) = σO δ3 * (σO n * σO b ^ 3) := by rw [map_mul, map_mul, map_pow]
  rw [twAt_mul, hx, hσ, map_mul, map_mul, map_pow]
  rw [show phiTw (twistPsi ξ k f) (n * b ^ 3) * conj (τ (-(δ3 * (n * b ^ 3)))) =
    conj (τ (-(δ3 * (n * b ^ 3)))) * phiTw (twistPsi ξ k f) (n * b ^ 3) by ring, hcr, hsqrt]
  unfold gCoef dCoef thetaK alphaI
  rw [ite_eq_left hsq, ← hn, ← hb, ← hrn, ← hrb]
  push_cast at hpow ⊢
  simp only [map_div₀, Complex.conj_ofReal]
  linear_combination (conj C * gamI 2 𝔫 * twistPsi ξ k f 𝔫 * twistPsi ξ k f 𝔟 ^ 3 *
    (2 * Real.pi * I * conj (σO δ3) / 9) * (conj (σO n) * conj (σO b) ^ 3) * 2 ^ (2 * s - 1)) * hpow

theorem mem_S_of_term_ne_zero {𝔫 𝔟 : Ideal (𝓞 K)} {c : ℂ}
    (h : c * (gCoef ξ k f 𝔫 * dCoef ξ k f 𝔟 * (((absNorm 𝔫 : ℝ)) : ℂ) ^ (-(s : ℂ)) *
      (((absNorm 𝔟 : ℝ)) : ℂ) ^ (-(3 * s) + 1 / 2)) ≠ 0) :
    Squarefree 𝔫 ∧ (absNorm 𝔫).Coprime 6 ∧ (absNorm 𝔟).Coprime 6 := by
  have hg : gCoef ξ k f 𝔫 ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have hd : dCoef ξ k f 𝔟 ≠ 0 := fun h0 => h (by rw [h0]; ring)
  refine ⟨?_, coprime6_of_gCoef ξ k f hg, coprime6_of_dCoef ξ k f hd⟩
  by_contra hsq
  apply hg
  unfold gCoef
  rw [ite_eq_right hsq]

/-- **The theta Dirichlet series is `𝒯(s, Ψ)`** (the paper's (A.16)): for `Re s ≥ 5/3`, the Mellin
transform of the twisted derivative series divided by its Gamma factors is `thetaK(C, s)·𝒯(s, Ψ)`. -/
theorem theta_dirichlet {τ : 𝓞 K → ℂ} {Kc : ℝ} {C : ℂ} (hτ : ThetaSupp Kc τ)
    (hval : ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})))
    {s : ℂ} (hs : 5 / 3 ≤ s.re) :
    Fq (fun m => twAt (phiTw (twistPsi ξ k f)) m * conj (τ (-m)))
      (fun m => 2 * Real.pi * I * conj (σO m) / 9) s = thetaK C s * compD ξ k f s := by
  have ha : ThetaSupp (1 * Kc) (fun m => twAt (phiTw (twistPsi ξ k f)) m * conj (τ (-m))) :=
    thetaSupp_twisted hτ zero_le_one (norm_phiTw_le ξ k f)
  have hg1 : Gamma (s + 1 / 3) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hg2 : Gamma (s + 2 / 3) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  unfold Fq
  rw [mellin_dSer ha (fun m => norm_phiInf_le m) hs, ← tsum_mul_right, ← tsum_mul_right]
  set F : 𝓞 K → ℂ := fun m => twAt (phiTw (twistPsi ξ k f)) m * conj (τ (-m)) *
    (2 * Real.pi * I * conj (σO m) / 9) *
    (2 ^ (2 * s - 1) * (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * s + 1))) with hF
  have e1 : ∀ m : 𝓞 K, twAt (phiTw (twistPsi ξ k f)) m * conj (τ (-m)) *
      (2 * Real.pi * I * conj (σO m) / 9) * (2 ^ (2 * s - 1) * Gamma (s + 1 / 3) * Gamma (s + 2 / 3) *
        (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * s + 1))) * (Gamma (s + 1 / 3))⁻¹ *
        (Gamma (s + 2 / 3))⁻¹ = F m := by
    intro m
    simp only [hF]
    generalize Gamma (s + 1 / 3) = g1 at hg1 ⊢
    generalize Gamma (s + 2 / 3) = g2 at hg2 ⊢
    field_simp
  rw [tsum_congr e1]
  set G : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ := fun p => thetaK C s * (gCoef ξ k f p.1 * dCoef ξ k f p.2 *
    (((absNorm p.1 : ℝ)) : ℂ) ^ (-s) * (((absNorm p.2 : ℝ)) : ℂ) ^ (-(3 * s) + 1 / 2)) with hG
  have hGsum : thetaK C s * compD ξ k f s = ∑' p, G p := by
    unfold compD; rw [← tsum_mul_left]
  rw [hGsum]
  have hS : ∀ p : Function.support G, Squarefree p.1.1 ∧ (absNorm p.1.1).Coprime 6 ∧
      (absNorm p.1.2).Coprime 6 := fun p => mem_S_of_term_ne_zero ξ k f p.2
  refine tsum_eq_tsum_of_ne_zero_bij (fun p => δ3 * (pgen p.1.1 * pgen p.1.2 ^ 3)) ?_ ?_ ?_
  · -- injective
    intro x y hxy
    obtain ⟨hx1, hx2, hx3⟩ := hS x
    obtain ⟨hy1, hy2, hy3⟩ := hS y
    have h1 : pgen x.1.1 * pgen x.1.2 ^ 3 = pgen y.1.1 * pgen y.1.2 ^ 3 :=
      mul_left_cancel₀ δ3_ne_zero hxy
    have h2 := congrArg (fun z => span {z}) h1
    simp only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
      (pgen_spec6 hx2).2, (pgen_spec6 hx3).2, (pgen_spec6 hy2).2, (pgen_spec6 hy3).2] at h2
    obtain ⟨e1, e2⟩ := sqfree_cube_unique hx1 hy1 (ne_bot_of_coprime6 hx3) h2
    exact Subtype.ext (Prod.ext e1 e2)
  · -- the support of `F` is in the range
    intro m hm
    have ha0 : twAt (phiTw (twistPsi ξ k f)) m * conj (τ (-m)) ≠ 0 := by
      intro h0; apply hm; simp only [hF]; rw [h0]; ring
    obtain ⟨n, b, hn, hb, hsq, h6, rfl⟩ := twisted_support hτ _ ha0
    have hsp : span {n * b} = span {n} * span {b} := (Ideal.span_singleton_mul_span_singleton n b).symm
    rw [hsp, map_mul] at h6
    have hn6 := coprime6_left h6
    have hb6 := coprime6_right h6
    have hterm := theta_term ξ k f hval hsq hn6 hb6 s
    rw [pgen_eq hn, pgen_eq hb] at hterm
    have hG0 : G (span {n}, span {b}) ≠ 0 := by
      simp only [hG]; rw [← hterm]; exact hm
    exact ⟨⟨(span {n}, span {b}), hG0⟩, by simp only [pgen_eq hn, pgen_eq hb]⟩
  · -- the terms agree
    intro p
    obtain ⟨h1, h2, h3⟩ := hS p
    exact theta_term ξ k f hval h1 h2 h3 s

open scoped ContDiff

/-- `(√a·b)^{−1}(ab³/X)^{−w} = a^{−(w+1/2)}b^{−3(w+1/2)+1/2}X^w`. -/
theorem compT_pow_id {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (w : ℂ) :
    (((Real.sqrt a : ℝ) : ℂ) * (b : ℂ))⁻¹ * (((a * b ^ 3 / X : ℝ)) : ℂ) ^ (-w) =
      ((a : ℂ)) ^ (-(w + 1 / 2)) * ((b : ℂ)) ^ (-(3 * (w + 1 / 2)) + 1 / 2) * (X : ℂ) ^ w := by
  rw [ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp ha, ofReal_cpow_eq_exp hb,
    ofReal_cpow_eq_exp hX, ofReal_eq_exp (Real.sqrt_pos.2 ha), ofReal_eq_exp hb, ← Complex.exp_add,
    ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Real.log_div (by positivity) hX.ne', Real.log_mul ha.ne' (by positivity), Real.log_pow,
    Real.log_sqrt ha.le]
  push_cast
  ring

/-- The ideals of `𝓞 K` are countable: each is spanned by a finite set. -/
instance countable_ideal : Countable (Ideal (𝓞 K)) := by
  refine Function.Surjective.countable (f := fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) ?_
  intro J
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J : J.FG)
  exact ⟨s, hs⟩

theorem mellin_Vstar_line_integrable {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hW : ∀ y, y < α ∨ β < y → W y = 0) (hs : ContDiff ℝ ∞ W) {N : ℝ}
    (hN : ∀ i ≤ 2, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) (σ : ℝ) :
    Integrable fun u : ℝ => mellin (Vstar W) ((σ : ℂ) + u * I) := by
  obtain ⟨C, hC, hdec⟩ := mellin_Vstar_decay hα hαβ 2 σ σ
  have hd := differentiable_mellin_of_support hα (Vstar_eq_zero_out hW) (continuous_Vstar hs.continuous)
  refine ((integrable_inv_one_add_abs_sq).const_mul (C * N)).mono'
    ((hd.continuous.comp (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  have := hdec W hW hs N hN ((σ : ℂ) + u * I) (by simp) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add] at this
  simpa [div_eq_mul_inv] using this

/-- **Mellin inversion for the completed sum** (the paper's (A.13)): `T(X; Ψ)` is
`(1/2π)∫V̂_*(s − 1/2)𝒯(s, Ψ)X^{s−1/2} du` along `Re s = 2`. -/
theorem compT_mellin {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hW : ∀ y, y < α ∨ β < y → W y = 0) (hs : ContDiff ℝ ∞ W) {N : ℝ}
    (hN : ∀ i ≤ 2, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) {X : ℝ} (hX : 0 < X) :
    compT ξ k f W X = 1 / (2 * Real.pi) * ∫ u : ℝ, mellin (Vstar W) (((2 : ℝ) : ℂ) + u * I - 1 / 2) *
      compD ξ k f (((2 : ℝ) : ℂ) + u * I) * (X : ℂ) ^ (((2 : ℝ) : ℂ) + u * I - 1 / 2) := by
  set V : ℝ → ℂ := fun u => mellin (Vstar W) (((3 / 2 : ℝ) : ℂ) + u * I) with hV
  have hVint : Integrable V := mellin_Vstar_line_integrable hα hαβ hW hs hN (3 / 2)
  set w : ℝ → ℂ := fun u => ((3 / 2 : ℝ) : ℂ) + u * I with hw
  set T : Ideal (𝓞 K) × Ideal (𝓞 K) → ℝ → ℂ := fun p u => gCoef ξ k f p.1 * dCoef ξ k f p.2 *
    (((absNorm p.1 : ℝ)) : ℂ) ^ (-(w u + 1 / 2)) * (((absNorm p.2 : ℝ)) : ℂ) ^ (-(3 * (w u + 1 / 2)) + 1 / 2) *
    ((X : ℂ) ^ (w u) * V u) with hT
  -- each term of `compT`
  have hterm : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), gCoef ξ k f p.1 * dCoef ξ k f p.2 /
      (((Real.sqrt (absNorm p.1 : ℝ) : ℝ) : ℂ) * (absNorm p.2 : ℂ)) *
        Vstar W ((absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 / X) =
      1 / (2 * Real.pi) * ∫ u, T p u := by
    intro p
    by_cases hc : gCoef ξ k f p.1 * dCoef ξ k f p.2 = 0
    · simp only [hT, hc, zero_mul, zero_div, integral_zero, mul_zero]
    have hg : gCoef ξ k f p.1 ≠ 0 := left_ne_zero_of_mul hc
    have hd : dCoef ξ k f p.2 ≠ 0 := right_ne_zero_of_mul hc
    have h1 := one_le_absNorm_of_coprime6 (coprime6_of_gCoef ξ k f hg)
    have h2 := one_le_absNorm_of_coprime6 (coprime6_of_dCoef ξ k f hd)
    have hy : 0 < (absNorm p.1 : ℝ) * (absNorm p.2 : ℝ) ^ 3 / X := by positivity
    rw [← Vstar_mellinInv hα hαβ hW hs hN (3 / 2) hy]
    unfold mellinInv
    rw [Complex.real_smul, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hT, hw, hV, smul_eq_mul]
    have hid := compT_pow_id (a := (absNorm p.1 : ℝ)) (b := (absNorm p.2 : ℝ)) (by linarith) (by linarith)
      hX (((3 / 2 : ℝ) : ℂ) + u * I)
    have hNc : ((absNorm p.2 : ℕ) : ℂ) = (((absNorm p.2 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hNc]
    rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * Real.pi) by push_cast; rfl]
    linear_combination (1 / (2 * (Real.pi : ℂ)) * (gCoef ξ k f p.1 * dCoef ξ k f p.2) *
      mellin (Vstar W) (((3 / 2 : ℝ) : ℂ) + u * I)) * hid
  -- the majorant `X^{3/2}·N𝔫^{−2}N𝔟^{−11/2}·|V̂_*|`
  have hre1 : ∀ u, (-(w u + 1 / 2)).re = -2 := fun u => by simp [hw]; norm_num
  have hre2 : ∀ u, (-(3 * (w u + 1 / 2)) + 1 / 2).re = -(11 / 2) := fun u => by simp [hw]; norm_num
  have hre3 : ∀ u, (w u).re = 3 / 2 := fun u => by simp [hw]
  have hB : ∀ p u, ‖T p u‖ ≤ X ^ (3 / 2 : ℝ) *
      ((absNorm p.1 : ℝ) ^ (-(2 : ℝ)) * (absNorm p.2 : ℝ) ^ (-(11 / 2 : ℝ))) * ‖V u‖ := by
    intro p u
    simp only [hT]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _) (by rw [hre1]; norm_num),
      norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _) (by rw [hre2]; norm_num),
      norm_cpow_eq_rpow_re_of_pos hX, hre1, hre2, hre3]
    have h1 := norm_gCoef_le ξ k f p.1
    have h2 := norm_dCoef_le ξ k f p.2
    have h3 : 0 ≤ (absNorm p.1 : ℝ) ^ (-(2 : ℝ)) := by positivity
    have h4 : 0 ≤ (absNorm p.2 : ℝ) ^ (-(11 / 2 : ℝ)) := by positivity
    have h5 : 0 ≤ X ^ (3 / 2 : ℝ) := by positivity
    have h6 := norm_nonneg (V u)
    have h7 : ‖gCoef ξ k f p.1‖ * ‖dCoef ξ k f p.2‖ ≤ 1 :=
      (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    calc ‖gCoef ξ k f p.1‖ * ‖dCoef ξ k f p.2‖ * (absNorm p.1 : ℝ) ^ (-(2 : ℝ)) *
          (absNorm p.2 : ℝ) ^ (-(11 / 2 : ℝ)) * (X ^ (3 / 2 : ℝ) * ‖V u‖) =
        (‖gCoef ξ k f p.1‖ * ‖dCoef ξ k f p.2‖) * (X ^ (3 / 2 : ℝ) *
          ((absNorm p.1 : ℝ) ^ (-(2 : ℝ)) * (absNorm p.2 : ℝ) ^ (-(11 / 2 : ℝ))) * ‖V u‖) := by ring
      _ ≤ 1 * (X ^ (3 / 2 : ℝ) *
          ((absNorm p.1 : ℝ) ^ (-(2 : ℝ)) * (absNorm p.2 : ℝ) ^ (-(11 / 2 : ℝ))) * ‖V u‖) := by
        gcongr
      _ = _ := one_mul _
  have hVc : Continuous V := by
    have hd := differentiable_mellin_of_support hα (Vstar_eq_zero_out hW) (continuous_Vstar hs.continuous)
    exact hd.continuous.comp (by fun_prop)
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hint : ∀ p, Integrable (T p) := by
    intro p
    refine ((hVint.norm.const_mul _)).mono' ?_ (Eventually.of_forall fun u => hB p u)
    simp only [hT]
    refine (((Continuous.aestronglyMeasurable continuous_const).mul ?_).mul ?_).mul
      (((Continuous.const_cpow hwc (Or.inl ?_)).mul hVc).aestronglyMeasurable)
    · exact (measurable_const.pow (by fun_prop : Measurable fun u => -(w u + 1 / 2))).aestronglyMeasurable
    · exact (measurable_const.pow (by fun_prop :
        Measurable fun u => -(3 * (w u + 1 / 2)) + 1 / 2)).aestronglyMeasurable
    · exact_mod_cast hX.ne'
  have hsum : Summable fun p => ∫ u, ‖T p u‖ := by
    have hs2 := (summable_absNorm_rpow (s := 2) (by norm_num)).mul_of_nonneg
      (summable_absNorm_rpow (s := 11 / 2) (by norm_num)) (fun _ => by positivity)
      (fun _ => by positivity)
    refine ((hs2.mul_left (X ^ (3 / 2 : ℝ))).mul_right (∫ u, ‖V u‖)).of_nonneg_of_le
      (fun p => integral_nonneg fun u => norm_nonneg _) fun p => ?_
    rw [← integral_const_mul]
    refine integral_mono (hint p).norm (hVint.norm.const_mul _) fun u => ?_
    simpa [mul_assoc] using hB p u
  unfold compT
  rw [tsum_congr hterm, tsum_mul_left, integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e1 : w u + 1 / 2 = ((2 : ℝ) : ℂ) + u * I := by simp only [hw]; push_cast; ring
  have e2 : ((2 : ℝ) : ℂ) + u * I - 1 / 2 = w u := by simp only [hw]; push_cast; ring
  simp only [hT]
  rw [tsum_mul_right, e2]
  unfold compD
  rw [← e1]
  simp only [hV, hw]
  ring

/-- `2^{2s−1}ρ^{−(2s+1)}·ρ²·(ρ²X/4)^{s−1/2} = X^{s−1/2}` for `ρ = 4π√3/9`, so `ρ² = 16π²/27` and
`ρ²/4 = 4π²/27`. -/
theorem theta_scale_id {X : ℝ} (hX : 0 < X) (s : ℂ) :
    (2 : ℂ) ^ (2 * s - 1) * (((4 * Real.pi * Real.sqrt 3 / 9 : ℝ)) : ℂ) ^ (-(2 * s + 1)) *
      (((16 * Real.pi ^ 2 / 27 : ℝ)) : ℂ) * (((4 * Real.pi ^ 2 * X / 27 : ℝ)) : ℂ) ^ (s - 1 / 2) =
      (X : ℂ) ^ (s - 1 / 2) := by
  set ρ : ℝ := 4 * Real.pi * Real.sqrt 3 / 9 with hρ
  have hρ0 : 0 < ρ := by positivity
  have e1 : (16 * Real.pi ^ 2 / 27 : ℝ) = ρ ^ 2 := by
    rw [hρ, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have e2 : (4 * Real.pi ^ 2 * X / 27 : ℝ) = ρ ^ 2 * X / 2 ^ 2 := by rw [← e1]; ring
  rw [e1, e2]
  clear_value ρ
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2, ofReal_cpow_eq_exp (by norm_num : (0 : ℝ) < 2), ofReal_cpow_eq_exp hρ0,
    ofReal_eq_exp (by positivity : 0 < ρ ^ 2), ofReal_cpow_eq_exp (by positivity : 0 < ρ ^ 2 * X / 2 ^ 2),
    ofReal_cpow_eq_exp hX, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hX.ne', Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `thetaK(C, s)·(16π²/27)/(C̄·2πiσ̄(δ₃)/9)·(4π²X/27)^{s−1/2} = X^{s−1/2}`. -/
theorem thetaK_mul_scale {C : ℂ} (hC : C ≠ 0) {X : ℝ} (hX : 0 < X) (s : ℂ) :
    thetaK C s * ((((16 * Real.pi ^ 2 / 27 : ℝ)) : ℂ) / (conj C * (2 * Real.pi * I * conj (σO δ3) / 9)) *
      (((4 * Real.pi ^ 2 * X / 27 : ℝ)) : ℂ) ^ (s - 1 / 2)) = (X : ℂ) ^ (s - 1 / 2) := by
  have hc1 : conj C * (2 * Real.pi * I * conj (σO δ3) / 9) ≠ 0 := by
    refine mul_ne_zero ((map_ne_zero _).2 hC) (div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_pos.ne')) I_ne_zero) ?_) (by norm_num))
    rw [map_ne_zero]
    exact fun h => δ3_ne_zero (σO_injective (h.trans (map_zero σO).symm))
  rw [← theta_scale_id hX s]
  unfold thetaK
  generalize conj C * (2 * Real.pi * I * conj (σO δ3) / 9) = c at hc1 ⊢
  field_simp

/-- **The completed sum as a contour integral of the theta Dirichlet series** ((A.13) with (A.16)):
`T(X; Ψ) = (8π/27)/(C̄·2πiσ̄(δ₃)/9)·∫V̂_*(s − 1/2)·Fq(s)·(4π²X/27)^{s−1/2} du` along `Re s = 2`, where
`Fq` is the Mellin transform of the twisted derivative series over its Gamma factors. -/
theorem compT_theta {τ : 𝓞 K → ℂ} {Kc : ℝ} {C : ℂ} (hτ : ThetaSupp Kc τ)
    (hval : ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n})))
    (hC : C ≠ 0) {W : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hW : ∀ y, y < α ∨ β < y → W y = 0) (hs : ContDiff ℝ ∞ W) {N : ℝ}
    (hN : ∀ i ≤ 2, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) {X : ℝ} (hX : 0 < X) :
    compT ξ k f W X = (((8 * Real.pi / 27 : ℝ)) : ℂ) / (conj C * (2 * Real.pi * I * conj (σO δ3) / 9)) *
      ∫ u : ℝ, mellin (Vstar W) (((2 : ℝ) : ℂ) + u * I - 1 / 2) *
        Fq (fun m => twAt (phiTw (twistPsi ξ k f)) m * conj (τ (-m)))
          (fun m => 2 * Real.pi * I * conj (σO m) / 9) (((2 : ℝ) : ℂ) + u * I) *
        (((4 * Real.pi ^ 2 * X / 27 : ℝ)) : ℂ) ^ (((2 : ℝ) : ℂ) + u * I - 1 / 2) := by
  rw [compT_mellin ξ k f hα hαβ hW hs hN hX, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  have hs' : 5 / 3 ≤ (((2 : ℝ) : ℂ) + u * I).re := by simp; norm_num
  rw [theta_dirichlet ξ k f hτ hval hs', ← thetaK_mul_scale hC hX]
  have hpi : (((8 * Real.pi / 27 : ℝ)) : ℂ) = 1 / (2 * Real.pi) * (((16 * Real.pi ^ 2 / 27 : ℝ)) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [hpi]
  ring

end Eis

end

#print axioms Eis.sqfree_cube_unique
#print axioms Eis.δ3_eq_neg_ω_lam
#print axioms Eis.ω_cube_eq
#print axioms Eis.twisted_support
#print axioms Eis.norm_phiTw_le
#print axioms Eis.theta_pow_id
#print axioms Eis.theta_term
#print axioms Eis.mem_S_of_term_ne_zero
#print axioms Eis.theta_dirichlet
#print axioms Eis.compT_pow_id
#print axioms Eis.mellin_Vstar_line_integrable
#print axioms Eis.compT_mellin
#print axioms Eis.theta_scale_id
#print axioms Eis.thetaK_mul_scale
#print axioms Eis.compT_theta
