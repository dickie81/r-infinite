import KubotaCuspData

/-! # The twisted theta function in cusp coordinates (round 371)

S5f-3e, the last part of round 360's S5f-3. For a group of translates the companion paper combines the
multiplier, the additive Chinese remainder theorem (its (A.11),
"`\breve e(-\delta'\ell/c) =\psi(\lambda^4\ell)\prod_{p\mid r}e(\epsilon_ph_p^{-1}\lambda^4\ell/p),`") and the
local transformation (A.12): "`Consequently, for each fixed $h_0$ and active set $\mathcal A$, combining the
Fourier coefficients $d_\sigma(\ell)$ of $\overline{\theta(H(z,v))}$ with the sums over $h_p\ne0$ gives`"
"`d_\sigma(\ell)\psi(\lambda^4\ell) \prod_{p\in\mathcal A}B_{p,j_p}(\lambda^4\ell),`" "`up to a scalar
independent of $\ell$.`" This file proves it and, with round 367's grouping, the expansion of the twisted
`θ̄` in cusp coordinates.

* **Tools** (`conj_ψc`, `conj_chiP_sq`, `πP_mem`, `thetaSupp_mul`, **`sum_thSer_mul`**, `thSer_mul_const`):
  a finite combination of theta-type series on a common support is one theta-type series.
* **The phase at `π_P`** (`psiR_local`): with `δ′s_Ph_P ≡ 1` and `s_Pt_P ≡ 1 (mod π_P)`,
  `ψ_{π_P}(−mδ′w) = ψ_P(e·m/h_P)` with `e = −wt_P`.
* **The phase split** (`phase_split`): `ψ_{λ³Dr}(−mδ′) = ψ_{λ³D}(−mδ₀u)∏_Pψ_{π_P}(−mδ′w_P)` for
  `δ′ ≡ δ₀ (mod 9D)`, by round 366's `ψc_prod_crt`.
* **The sum over a group at one frequency** (**`group_local_sum`**): round 366's `local_transform` at every
  prime of `A`, through the expansion of a product of sums.
* **The per-group identity** (**`group_sum`**, **`group_expansion`**): the sum over a group of
  `∏_PC_{P,j_P}(h_P)·θ̄(z + z_h, v)` is a unimodular `C₀` times one theta-type series at `(−W, V)`, with
  coefficients `d̄_H(−m)ψ_{λ³D}(−my)∏_PB_{P,j_P}(m)`.
* **The expansion** (**`twisted_theta_expansion`**): the twisted `θ̄` of round 367 as a sum over `h₀` and the
  active sets of these series.
-/

open NumberField Ideal UniqueFactorizationMonoid Complex
open scoped ComplexConjugate

noncomputable section

namespace Eis

theorem conj_ψc (c x : 𝓞 K) : conj (ψc c x) = ψc c (-x) := by
  rw [← Complex.inv_eq_conj (norm_ψc c x)]
  have h := ψc_add c x (-x)
  rw [add_neg_cancel, ψc_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm).symm

theorem conj_chiP_sq (P : Pr) {a : 𝓞 K} (ha : a ∉ P.1) : conj (chiP P.1 a ^ 2) = (chiP P.1 a ^ 2)⁻¹ := by
  rw [Complex.inv_eq_conj (by rw [norm_pow, norm_chiP_of_not_mem P ha, one_pow])]

theorem πP_mem (P : Pr) : πP P ∈ P.1 := by
  rw [← (πP_spec P).2]; exact Ideal.mem_span_singleton_self _

theorem thetaSupp_mul {Kc : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (hφ : ∀ m, ‖φ m‖ ≤ 1) :
    ThetaSupp Kc fun m => d m * φ m := by
  refine ⟨h.1, fun m hm => ?_⟩
  have hd : d m ≠ 0 := fun h0 => hm (by simp [h0])
  obtain ⟨q, hq, h1, h2, h3, h4⟩ := h.2 m hd
  refine ⟨q, hq, h1, h2, h3, ?_⟩
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (hφ m)).trans h4

/-- **A finite combination of theta-type series on a common support** is a theta-type series. -/
theorem sum_thSer_mul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ℂ) {Kc : ℝ} {d : 𝓞 K → ℂ}
    (hd : ThetaSupp Kc d) (φ : ι → 𝓞 K → ℂ) (hφ : ∀ i ∈ s, ∀ m, ‖φ i m‖ ≤ 1) (z : ℂ) {v : ℝ}
    (hv : 0 < v) :
    ∑ i ∈ s, a i * thSer c (fun m => d m * φ i m) z v =
      thSer ((∑ i ∈ s, a i) * c) (fun m => d m * ∑ i ∈ s, a i * φ i m) z v := by
  unfold thSer
  have hsum : ∀ i ∈ s, Summable fun m : 𝓞 K => a i * (d m * φ i m * (v : ℂ) *
      besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9)) :=
    fun i hi => (summable_thSer (thetaSupp_mul hd (hφ i hi)) z hv).mul_left (a i)
  have e1 : ∀ i ∈ s, a i * (c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) + ∑' m : 𝓞 K, d m * φ i m * (v : ℂ) *
      besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9)) =
      a i * (c * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) + ∑' m : 𝓞 K, a i * (d m * φ i m * (v : ℂ) *
      besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9)) := by
    intro i _
    rw [mul_add, tsum_mul_left]
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Summable.tsum_finsetSum hsum]
  congr 1
  · rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine tsum_congr fun m => ?_
    beta_reduce
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem thSer_mul_const (a c : ℂ) (d : 𝓞 K → ℂ) (z : ℂ) (v : ℝ) :
    thSer (a * c) (fun m => a * d m) z v = a * thSer c d z v := by
  unfold thSer
  rw [mul_add, ← tsum_mul_left]
  congr 1
  · ring
  · exact tsum_congr fun m => by ring

/-- **The phase at `π_P`**: with `δ′s_Ph_P ≡ 1` and `s_Pt_P ≡ 1 (mod π_P)`,
`ψ_{π_P}(−mδ′w) = ψ_P(e·m/h_P)` with `e = −wt_P`. -/
theorem psiR_local (P : Pr) {h : 𝓞 K ⧸ span {πP P}} (hh : h ≠ 0) {s t δ w : 𝓞 K} (m : 𝓞 K)
    (hδ : δ * (s * repQ (πP P) h) - 1 ∈ P.1) (ht : s * t - 1 ∈ P.1) :
    ψc (πP P) (-(m * δ) * w) = psiR P (Ideal.Quotient.mk (span {πP P}) (-(w * t) * m) * h⁻¹) := by
  have e1 := (mkP_eq_zero_iff P _).2 hδ
  have e2 := (mkP_eq_zero_iff P _).2 ht
  rw [map_sub, map_mul, map_mul, repQ_mk, map_one, sub_eq_zero] at e1
  rw [map_sub, map_mul, map_one, sub_eq_zero] at e2
  have hδ' : Ideal.Quotient.mk (span {πP P}) δ = Ideal.Quotient.mk (span {πP P}) t * h⁻¹ := by
    calc Ideal.Quotient.mk (span {πP P}) δ
        = Ideal.Quotient.mk (span {πP P}) δ *
            (Ideal.Quotient.mk (span {πP P}) s * Ideal.Quotient.mk (span {πP P}) t) := by
          rw [e2, mul_one]
      _ = (Ideal.Quotient.mk (span {πP P}) δ * (Ideal.Quotient.mk (span {πP P}) s * h)) *
            Ideal.Quotient.mk (span {πP P}) t * h⁻¹ := by
          field_simp
      _ = Ideal.Quotient.mk (span {πP P}) t * h⁻¹ := by rw [e1, one_mul]
  have key : Ideal.Quotient.mk (span {πP P}) (-(m * δ) * w) =
      Ideal.Quotient.mk (span {πP P}) (-(w * t) * m) * h⁻¹ := by
    simp only [map_mul, map_neg]
    rw [hδ']
    ring
  rw [← key]
  exact (ψQ_mk (πP P) (ne_zero_of_maximal (πP P)) _).symm

open Classical in
/-- **The sum over a group at one frequency** (the companion paper's (A.12) for a group): with
`δ′(h)s_Ph_P ≡ 1` and `s_Pt_P ≡ 1 (mod π_P)`, the sum over the nonzero `h_P` of
`∏_P C_{P,j_P}(h_P)(χ_P(s_Ph_P)²)⁻¹ψ_{π_P}(−mδ′(h)w_P)` is `∏_P(χ_P(s_P)²)⁻¹ω_{P,j_P}(−w_Pt_P)B_{P,j_P}(m)`. -/
theorem group_local_sum (A : Finset Pr) (j : Pr → ℕ) {s t w : Pr → 𝓞 K}
    (hs : ∀ P ∈ A, s P ∉ P.1) (ht : ∀ P ∈ A, s P * t P - 1 ∈ P.1) (hw : ∀ P ∈ A, w P ∉ P.1)
    (δ : ((P : A) → 𝓞 K ⧸ span {πP P.1}) → 𝓞 K)
    (hδ : ∀ h : (P : A) → 𝓞 K ⧸ span {πP P.1}, (∀ P, h P ≠ 0) →
      ∀ P : A, δ h * (s P.1 * repQ (πP P.1) (h P)) - 1 ∈ P.1.1) (m : 𝓞 K) :
    ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
        (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P)) *
          (chiP P.1.1 (s P.1 * repQ (πP P.1) (h P)) ^ 2)⁻¹) *
        ∏ P : A, ψc (πP P.1) (-(m * δ h) * w P.1) =
      ∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (-(w P.1 * t P.1)) * Bloc P.1.1 (j P.1) m := by
  classical
  have he : ∀ P ∈ A, -(w P * t P) ∉ P.1 := fun P hP hm => by
    have h1 : w P * t P ∈ P.1 := by have := P.1.neg_mem hm; rwa [neg_neg] at this
    rcases P.2.1.isPrime.mem_or_mem h1 with h | h
    · exact hw P hP h
    · apply P.2.1.ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.1.sub_mem (P.1.mul_mem_left (s P) h) (ht P hP)
      rwa [show s P * t P - (s P * t P - 1) = 1 by ring] at this
  rw [Finset.prod_congr rfl fun P _ => (local_transform P.1 (j P.1) (hs P.1 P.2) (he P.1 P.2) m).symm,
    Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hh' : ∀ P, h P ≠ 0 := fun P => (Finset.mem_erase.1 (Fintype.mem_piFinset.1 hh P)).1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [psiR_local P.1 (hh' P) m (hδ h hh' P) (ht P.1 P.2)]

/-- The phase `ψ_{λ³Dr}(−mδ′)` split at `λ³D` and the primes of `A`, with `δ′ ≡ δ₀ (mod 9D)`. -/
theorem phase_split {A : Finset Pr} {D δ δ₀ u : 𝓞 K} {w : Pr → 𝓞 K} (hc : δ3 ^ 3 * D ≠ 0)
    (hcrt : ∀ x, ψc (δ3 ^ 3 * D * ∏ P ∈ A, πP P) x = ψc (δ3 ^ 3 * D) (x * u) * ∏ P ∈ A, ψc (πP P) (x * w P))
    (hδ : 9 * D ∣ δ - δ₀) (m : 𝓞 K) :
    ψc (δ3 ^ 3 * (D * ∏ P ∈ A, πP P)) (-(m * δ)) =
      ψc (δ3 ^ 3 * D) (-(m * δ₀) * u) * ∏ P : A, ψc (πP P.1) (-(m * δ) * w P.1) := by
  rw [← mul_assoc, hcrt, Finset.prod_coe_sort A (fun P => ψc (πP P) (-(m * δ) * w P))]
  congr 1
  obtain ⟨k, hk⟩ := hδ
  have e : -(m * δ) * u = -(m * δ₀) * u + δ3 ^ 3 * D * (-(m * δ3 * k * u)) := by
    rw [nine_eq_δ3_pow] at hk
    linear_combination (-(m * u)) * hk
  rw [e, ψc_add_mul _ hc]

open Classical in
/-- **The per-group identity** (S5f-3e; the companion paper's (A.11)–(A.12) for a group): under the
cusp data of round 370, the sum over a group of `∏_PC_{P,j_P}(h_P)·θ̄(z + z_h, v)` is
`κ̄₀∏_P(χ_P(s_P)²)⁻¹ω_{P,j_P}(e_P)` times one theta-type series at `(−W, V)`, with constant term
`c̄_H∏_PB_{P,j_P}(0)` and coefficients `d̄_H(−m)ψ_{λ³D}(−mδ₀u)∏_PB_{P,j_P}(m)`. -/
theorem group_sum {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {L : 𝓞 K} (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr)
    (j : Pr → ℕ) {D δ₀ : 𝓞 K} {cH κ₀ : ℂ} {dH : 𝓞 K → ℂ} {s : Pr → 𝓞 K}
    (hD : D ≠ 0) (hDA : ∀ P ∈ A, D ∉ P.1) (hdH : ThetaSupp Kc dH) (hs : ∀ P ∈ A, s P ∉ P.1)
    (hall : ∀ h : (P : A) → 𝓞 K ⧸ span {πP P.1}, (∀ P, h P ≠ 0) →
      ∃ δ : 𝓞 K, 9 * D ∣ δ - δ₀ ∧ (∀ P : A, δ * (s P.1 * repQ (πP P.1) (h P)) - 1 ∈ P.1.1) ∧
        ∀ z (v : ℝ), 0 < v → θ (z + trShift L ⟨(h₀, A), h⟩) v =
          κ₀ * (∏ P : A, chiP P.1.1 (s P.1 * repQ (πP P.1) (h P)) ^ 2) *
            thSer cH (fun m => dH m * ψc (δ3 ^ 3 * (D * ∏ P ∈ A, πP P)) (-(m * δ)))
              (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v)) :
    ∃ (u : 𝓞 K) (e : Pr → 𝓞 K), (∀ P ∈ A, e P ∉ P.1) ∧ ∀ z (v : ℝ), 0 < v →
      ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
          (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) * conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) =
        conj κ₀ * (∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (e P.1)) *
          thSer (conj cH * ∏ P : A, Bloc P.1.1 (j P.1) 0)
            (fun m => conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * δ₀) * u) * ∏ P : A, Bloc P.1.1 (j P.1) m)
            (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v) := by
  have hc : δ3 ^ 3 * D ≠ 0 := mul_ne_zero (pow_ne_zero 3 δ3_ne_zero) hD
  have hcA : ∀ P ∈ A, δ3 ^ 3 * D ∉ P.1 := fun P hP hm => by
    rcases P.2.1.isPrime.mem_or_mem hm with h | h
    · exact δ3_not_mem P (P.2.1.isPrime.mem_of_pow_mem 3 h)
    · exact hDA P hP h
  obtain ⟨u, w, hw, hcrt⟩ := ψc_prod_crt A hc hcA
  have ht0 : ∀ P : Pr, ∃ t : 𝓞 K, P ∈ A → s P * t - 1 ∈ P.1 := by
    intro P
    by_cases hP : P ∈ A
    · obtain ⟨α, β, hαβ⟩ := (isCoprime_πP_iff P (s P)).2 (hs P hP)
      refine ⟨α, fun _ => ?_⟩
      rw [show s P * α - 1 = -(β * πP P) by linear_combination hαβ]
      exact P.1.neg_mem (P.1.mul_mem_left _ (πP_mem P))
    · exact ⟨0, fun h => absurd h hP⟩
  choose t ht using ht0
  choose! δ hδ1 hδ2 hδ3 using hall
  have he : ∀ P ∈ A, -(w P * t P) ∉ P.1 := fun P hP hm => by
    have h1 : w P * t P ∈ P.1 := by have := P.1.neg_mem hm; rwa [neg_neg] at this
    rcases P.2.1.isPrime.mem_or_mem h1 with h | h
    · exact hw P hP h
    · apply P.2.1.ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.1.sub_mem (P.1.mul_mem_left (s P) h) (ht P hP)
      rwa [show s P * t P - (s P * t P - 1) = 1 by ring] at this
  refine ⟨u, fun P => -(w P * t P), he, fun z v hv => ?_⟩
  have hV : 0 < cuspV (D * ∏ P ∈ A, πP P) z v := cuspV_pos (mul_ne_zero hD (prod_πP_ne_zero A)) z hv
  -- the weights and the phases of the translates
  obtain ⟨a, ha⟩ : ∃ a : ((P : A) → 𝓞 K ⧸ span {πP P.1}) → ℂ, a = fun h =>
      ∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P)) *
        (chiP P.1.1 (s P.1 * repQ (πP P.1) (h P)) ^ 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ((P : A) → 𝓞 K ⧸ span {πP P.1}) → 𝓞 K → ℂ, φ = fun h m =>
      ψc (δ3 ^ 3 * (D * ∏ P ∈ A, πP P)) (-(m * δ h)) := ⟨_, rfl⟩
  have hmem : ∀ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
      ∀ P, h P ≠ 0 := fun h hh P => (Finset.mem_erase.1 (Fintype.mem_piFinset.1 hh P)).1
  -- each term
  have step1 : ∀ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
      (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) * conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) =
        conj κ₀ * (a h * thSer (conj cH) (fun m => conj (dH (-m)) * φ h m)
          (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v)) := by
    intro h hh
    have hh' := hmem h hh
    rw [hδ3 h hh' z v hv, map_mul, map_mul, conj_thSer, map_prod]
    have hX : ∏ P : A, conj (chiP P.1.1 (s P.1 * repQ (πP P.1) (h P)) ^ 2) =
        ∏ P : A, (chiP P.1.1 (s P.1 * repQ (πP P.1) (h P)) ^ 2)⁻¹ := by
      refine Finset.prod_congr rfl fun P _ => conj_chiP_sq P.1 fun hm => ?_
      rcases P.1.2.1.isPrime.mem_or_mem hm with h1 | h1
      · exact hs P.1 P.2 h1
      · exact repQ_not_mem P.1 (hh' P) h1
    have hS : (fun m => conj (dH (-m) * ψc (δ3 ^ 3 * (D * ∏ P ∈ A, πP P)) (-(-m * δ h)))) =
        fun m => conj (dH (-m)) * φ h m := by
      funext m
      rw [hφ, map_mul, conj_ψc]
      congr 2
      ring
    rw [hX, hS, ha]
    beta_reduce
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl step1, ← Finset.mul_sum,
    sum_thSer_mul _ a (conj cH) (thetaSupp_conj hdH) φ (fun h _ m => by rw [hφ]; exact (norm_ψc _ _).le) _ hV]
  -- the sums over the group
  have hloc := fun m => group_local_sum A j hs (fun P hP => ht P hP) hw δ (fun h hh => hδ2 h hh) m
  have hcoef : ∀ m, ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
      a h * φ h m = ψc (δ3 ^ 3 * D) (-(m * δ₀) * u) *
        ((∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (-(w P.1 * t P.1))) *
          ∏ P : A, Bloc P.1.1 (j P.1) m) := by
    intro m
    rw [← Finset.prod_mul_distrib, ← hloc m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [hφ, ha]
    beta_reduce
    rw [phase_split hc (fun x => hcrt x) (hδ1 h (hmem h hh)) m]
    ring
  have hconst : ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
      a h = (∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (-(w P.1 * t P.1))) *
        ∏ P : A, Bloc P.1.1 (j P.1) 0 := by
    rw [← Finset.prod_mul_distrib, ← hloc 0]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [ha, ψc_zero]
  rw [hconst, show (fun m => conj (dH (-m)) * ∑ h ∈ Fintype.piFinset
      (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0), a h * φ h m) =
      fun m => (∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (-(w P.1 * t P.1))) *
        (conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * δ₀) * u) * ∏ P : A, Bloc P.1.1 (j P.1) m) from by
      funext m; rw [hcoef m]; ring,
    show (∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (-(w P.1 * t P.1))) *
        (∏ P : A, Bloc P.1.1 (j P.1) 0) * conj cH =
      (∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (-(w P.1 * t P.1))) *
        (conj cH * ∏ P : A, Bloc P.1.1 (j P.1) 0) by ring,
    thSer_mul_const]
  ring

open Classical in
/-- **The expansion of a group** (S5f-3e, from the display): for a group `(h₀, A)` with the primes of
`A` prime to `L`, the sum over the group of `∏_PC_{P,j_P}(h_P)·θ̄(z + z_h, v)` is a unimodular `C₀` times
the theta-type series at `(−W, V)` with constant term `c̄_H∏_PB_{P,j_P}(0)` and coefficients
`d̄_H(−m)ψ_{λ³D}(−my)∏_PB_{P,j_P}(m)`, for some `D ∣ L` and `y`, with `d_H` under the support and
size condition. -/
theorem group_expansion {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr)
    (hA : ∀ P ∈ A, L ∉ P.1) (j : Pr → ℕ) :
    ∃ (D : 𝓞 K) (C₀ cH : ℂ) (dH : 𝓞 K → ℂ) (y : 𝓞 K), D ≠ 0 ∧ D ∣ L ∧ ‖C₀‖ = 1 ∧ ThetaSupp Kc dH ∧
      ∀ z (v : ℝ), 0 < v →
        ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
            (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) *
              conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) =
          C₀ * thSer (conj cH * ∏ P : A, Bloc P.1.1 (j P.1) 0)
            (fun m => conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * y)) * ∏ P : A, Bloc P.1.1 (j P.1) m)
            (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v) := by
  obtain ⟨D, cH, dH, κ₀, δ₀, s, hD, hDL, hdH, hκ, hs, hall⟩ := group_cusp_exists hd hL h₀ A hA
  have hDA : ∀ P ∈ A, D ∉ P.1 := fun P hP hm => hA P hP (by
    obtain ⟨k, hk⟩ := hDL
    rw [hk]; exact P.1.mul_mem_right _ hm)
  obtain ⟨u, e, he, hsum⟩ := group_sum h₀ A j hD hDA hdH hs hall
  refine ⟨D, conj κ₀ * ∏ P : A, (chiP P.1.1 (s P.1) ^ 2)⁻¹ * ωloc P.1 (j P.1) (e P.1), cH, dH, δ₀ * u, hD,
    hDL, ?_, hdH, fun z v hv => ?_⟩
  · rw [norm_mul, Complex.norm_conj, hκ, one_mul, norm_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    rw [norm_mul, norm_inv, norm_pow, norm_chiP_of_not_mem P.1 (hs P.1 P.2), one_pow, inv_one, one_mul,
      norm_ωloc P.1 (j P.1) (he P.1 P.2)]
  · rw [hsum z v hv]
    congr 2
    funext m
    rw [show -(m * (δ₀ * u)) = -(m * δ₀) * u by ring]

open Classical in
/-- **The twisted `θ̄` in cusp coordinates** (the end of S5f-3; the companion paper's (A.4) with
(A.8)–(A.12)): the twisted series is a sum over the residues `h₀ mod L` and the active sets `A ⊆ Ps`
of `φ̂₀(h₀)∏_{P∉A}C_{P,j_P}(0)` times a unimodular `C₀(h₀, A)` times one theta-type series at the
coordinates `(−W, V)` of the group's cusp, with coefficients `d̄_H(−m)ψ_{λ³D}(−my)∏_{P∈A}B_{P,j_P}(m)`. -/
theorem twisted_theta_expansion {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (hφ0 : φ₀ 0 = 0) (Ps : Finset Pr) (hPs : ∀ P ∈ Ps, L ∉ P.1)
    (j : Pr → ℕ) :
    ∃ (D : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K) (C₀ cH : (𝓞 K ⧸ span {L}) → Finset Pr → ℂ)
      (dH : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K → ℂ) (y : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K),
      (∀ h₀, ∀ A ∈ Ps.powerset, D h₀ A ≠ 0 ∧ D h₀ A ∣ L ∧ ‖C₀ h₀ A‖ = 1 ∧ ThetaSupp Kc (dH h₀ A)) ∧
      ∀ z (v : ℝ), 0 < v →
        ∑' m : 𝓞 K, twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)) * (v : ℂ) *
            besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9) =
          ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
            ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
              (C₀ h₀ A * thSer (conj (cH h₀ A) * ∏ P : A, Bloc P.1.1 (j P.1) 0)
                (fun m => conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
                  ∏ P : A, Bloc P.1.1 (j P.1) m)
                (-cuspW (D h₀ A * ∏ P ∈ A, πP P) z v) (cuspV (D h₀ A * ∏ P ∈ A, πP P) z v)) := by
  have hex : ∀ (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr), ∃ (D : 𝓞 K) (C₀ cH : ℂ) (dH : 𝓞 K → ℂ) (y : 𝓞 K),
      A ∈ Ps.powerset → (D ≠ 0 ∧ D ∣ L ∧ ‖C₀‖ = 1 ∧ ThetaSupp Kc dH) ∧
        ∀ z (v : ℝ), 0 < v →
          ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
              (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) *
                conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) =
            C₀ * thSer (conj cH * ∏ P : A, Bloc P.1.1 (j P.1) 0)
              (fun m => conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * y)) * ∏ P : A, Bloc P.1.1 (j P.1) m)
              (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v) := by
    intro h₀ A
    by_cases hA : A ∈ Ps.powerset
    · obtain ⟨D, C₀, cH, dH, y, hD, hDL, hC, hdH, hid⟩ :=
        group_expansion hd hL h₀ A (fun P hP => hPs P (Finset.mem_powerset.1 hA hP)) j
      exact ⟨D, C₀, cH, dH, y, fun _ => ⟨⟨hD, hDL, hC, hdH⟩, hid⟩⟩
    · exact ⟨1, 1, 0, 0, 0, fun h => absurd h hA⟩
  choose D C₀ cH dH y hDATA using hex
  refine ⟨D, C₀, cH, dH, y, fun h₀ A hA => (hDATA h₀ A hA).1, fun z v hv => ?_⟩
  rw [twisted_theta_groups hd.2.2.2.2.1 hd.1 hd.2.2.2.1 hL φ₀ hφ hφ0 Ps j z hv]
  refine finsum_congr fun h₀ => ?_
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [(hDATA h₀ A hA).2 z v hv]

end Eis

end

#print axioms Eis.conj_ψc
#print axioms Eis.conj_chiP_sq
#print axioms Eis.πP_mem
#print axioms Eis.thetaSupp_mul
#print axioms Eis.sum_thSer_mul
#print axioms Eis.thSer_mul_const
#print axioms Eis.psiR_local
#print axioms Eis.group_local_sum
#print axioms Eis.phase_split
#print axioms Eis.group_sum
#print axioms Eis.group_expansion
#print axioms Eis.twisted_theta_expansion
