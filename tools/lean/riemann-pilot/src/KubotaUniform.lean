import KubotaContour

/-! # The uniformity of the group data in the active set (round 379)

S5f-6 of round 360's plan, part 2. The companion paper writes: "`To average the transformed sums over $k_0$,
we need to choose their cusp coefficients and additive characters consistently as $k_0$ varies.`" Its
Lemma 6.3 says: "`For each fixed index, the triple $(d,\psi,c_0)$ depends on $k_0$ only through its ray
class modulo a fixed ideal supported on $S$ and depending only on $\Psi_0,S$.`" This file proves the core
of it: the data of a group depend on its active set `A` only through `r = ∏_{P∈A}π_P` modulo `9L`.

* **The transfer** (`hcase_transfer`): the case hypothesis of round 370's `group_cusp` for `r` gives the one
  for every `r' ≡ r (mod 9L)`, with the same parameters.
* **One reference set** (**`group_expansion_ref`**): the parameters of round 370's `group_params` for one
  active set `A₁` give round 371's expansion of the group `(h₀, A)` for every `A` with
  `∏_{P∈A}π_P ≡ ∏_{P∈A₁}π_P (mod 9L)` and every choice of exponents, with the same `D`, `c_H`, `d_H` and `y`.
* **The expansion** (`rcls`, a definition; **`twisted_theta_expansion_unif`**): round 371's expansion of the
  twisted `θ̄`, with `D`, `c_H`, `d_H` and `y` functions of `h₀` and of the class of `∏_{P∈A}π_P` modulo
  `9L`, chosen before the twist, the primes and the exponents.
* **The dual sums** (**`twisted_theta_voronoi_unif`**): round 376's `twisted_theta_voronoi` with these data.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics UniqueFactorizationMonoid
open scoped Topology ComplexConjugate

noncomputable section

namespace Eis

/-- **The case hypothesis moves along `r mod 9L`**: the hypothesis of round 370's `group_cusp` for `r₁`
gives the one for every `r₂ ≡ r₁ (mod 9L)`, with the same parameters. -/
theorem hcase_transfer {L g₀ a₀ c₀ δ₀ r₁ r₂ : 𝓞 K} {ε : (𝓞 K)ˣ} {H : Matrix (Fin 2) (Fin 2) (𝓞 K)}
    (hLg : L = g₀ * c₀) (hr : 9 * L ∣ r₂ - r₁)
    (h : (Primary ((ε : 𝓞 K) * (a₀ * r₁)) ∧
        9 * ((ε : 𝓞 K) * c₀) ∣ (ε : 𝓞 K) * (a₀ * r₁) * δ₀ - 1 ∧
        ((3 ∣ c₀ ∧ H = 1) ∨ ∃ u₀, (u₀ = δ3 ∨ u₀ = -δ3) ∧
          3 ∣ (ε : 𝓞 K) * c₀ * r₁ - u₀ ∧ H = !![1, 0; u₀, 1])) ∨
      (Primary ((ε : 𝓞 K) * c₀ * r₁) ∧ 9 ∣ δ₀ ∧
        (ε : 𝓞 K) * c₀ ∣ (ε : 𝓞 K) * (a₀ * r₁) * δ₀ - 1 ∧
        ∃ u, 3 ∣ (ε : 𝓞 K) * (a₀ * r₁) - u ∧ H = !![u, -1; 1, 0])) :
    (Primary ((ε : 𝓞 K) * (a₀ * r₂)) ∧
        9 * ((ε : 𝓞 K) * c₀) ∣ (ε : 𝓞 K) * (a₀ * r₂) * δ₀ - 1 ∧
        ((3 ∣ c₀ ∧ H = 1) ∨ ∃ u₀, (u₀ = δ3 ∨ u₀ = -δ3) ∧
          3 ∣ (ε : 𝓞 K) * c₀ * r₂ - u₀ ∧ H = !![1, 0; u₀, 1])) ∨
      (Primary ((ε : 𝓞 K) * c₀ * r₂) ∧ 9 ∣ δ₀ ∧
        (ε : 𝓞 K) * c₀ ∣ (ε : 𝓞 K) * (a₀ * r₂) * δ₀ - 1 ∧
        ∃ u, 3 ∣ (ε : 𝓞 K) * (a₀ * r₂) - u ∧ H = !![u, -1; 1, 0]) := by
  obtain ⟨k, hk⟩ := hr
  have hr2 : r₂ = r₁ + 9 * (g₀ * c₀) * k := by rw [← hLg]; linear_combination hk
  have h3 : ∀ z : 𝓞 K, (3 : 𝓞 K) ∣ z * r₂ - z * r₁ := fun z => ⟨3 * z * g₀ * c₀ * k, by rw [hr2]; ring⟩
  rcases h with ⟨hp, hd, hH⟩ | ⟨hp, h9, hd, u, hu, hH⟩
  · left
    refine ⟨?_, ?_, ?_⟩
    · unfold Primary at hp ⊢
      have e : (ε : 𝓞 K) * (a₀ * r₂) - 1 =
          ((ε : 𝓞 K) * (a₀ * r₁) - 1) + ((ε : 𝓞 K) * a₀ * r₂ - (ε : 𝓞 K) * a₀ * r₁) := by ring
      rw [e]; exact dvd_add hp (h3 _)
    · obtain ⟨k', hk'⟩ := hd
      exact ⟨k' + a₀ * δ₀ * g₀ * k, by rw [hr2]; linear_combination hk'⟩
    · rcases hH with h | ⟨u₀, hu₀, hc, hH⟩
      · exact Or.inl h
      · refine Or.inr ⟨u₀, hu₀, ?_, hH⟩
        have e : (ε : 𝓞 K) * c₀ * r₂ - u₀ =
            ((ε : 𝓞 K) * c₀ * r₁ - u₀) + ((ε : 𝓞 K) * c₀ * r₂ - (ε : 𝓞 K) * c₀ * r₁) := by ring
        rw [e]; exact dvd_add hc (h3 _)
  · right
    refine ⟨?_, h9, ?_, u, ?_, hH⟩
    · unfold Primary at hp ⊢
      have e : (ε : 𝓞 K) * c₀ * r₂ - 1 =
          ((ε : 𝓞 K) * c₀ * r₁ - 1) + ((ε : 𝓞 K) * c₀ * r₂ - (ε : 𝓞 K) * c₀ * r₁) := by ring
      rw [e]; exact dvd_add hp (h3 _)
    · obtain ⟨k', hk'⟩ := hd
      exact ⟨k' + 9 * a₀ * δ₀ * g₀ * k, by rw [hr2]; linear_combination hk'⟩
    · have e : (ε : 𝓞 K) * (a₀ * r₂) - u =
          ((ε : 𝓞 K) * (a₀ * r₁) - u) + ((ε : 𝓞 K) * a₀ * r₂ - (ε : 𝓞 K) * a₀ * r₁) := by ring
      rw [e]; exact dvd_add hu (h3 _)

open Classical in
/-- **The data of a group from a reference set** (the uniformity of the companion paper's Lemma 6.3): the
parameters of round 370 chosen for one active set `A₁` serve every `A` with
`∏_{P∈A}π_P ≡ ∏_{P∈A₁}π_P (mod 9L)`. The expansion of the group `(h₀, A)` then has the same `D`, `c_H`,
`d_H` and `y`, for every choice of the exponents `j`. -/
theorem group_expansion_ref {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (h₀ : 𝓞 K ⧸ span {L})
    (A₁ : Finset Pr) (hA₁ : ∀ P ∈ A₁, L ∉ P.1) :
    ∃ (D : 𝓞 K) (cH : ℂ) (dH : 𝓞 K → ℂ) (y : 𝓞 K), D ≠ 0 ∧ D ∣ L ∧ ThetaSupp Kc dH ∧
      ∀ A : Finset Pr, (∀ P ∈ A, L ∉ P.1) → 9 * L ∣ ∏ P ∈ A, πP P - ∏ P ∈ A₁, πP P → ∀ j : Pr → ℕ,
      ∃ C₀ : ℂ, ‖C₀‖ = 1 ∧ ∀ z (v : ℝ), 0 < v →
        ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
            (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) *
              conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) =
          C₀ * thSer (conj cH * ∏ P : A, Bloc P.1.1 (j P.1) 0)
            (fun m => conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * y)) * ∏ P : A, Bloc P.1.1 (j P.1) m)
            (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v) := by
  obtain ⟨g₀, a₀, c₀, x, ε, H, cH, dH, δ₀, hg, hLg, hac, hx, hdH, hs, hcase⟩ :=
    group_params hd hL h₀ A₁ hA₁
  have hc₀ : c₀ ≠ 0 := by rintro rfl; exact hL (by rw [hLg, mul_zero])
  have hD : (ε : 𝓞 K) * c₀ ≠ 0 := mul_ne_zero ε.ne_zero hc₀
  have hDL : (ε : 𝓞 K) * c₀ ∣ L :=
    ⟨(↑ε⁻¹ : 𝓞 K) * g₀, by rw [hLg]; linear_combination (-(g₀ * c₀)) * ε.mul_inv⟩
  have hc : δ3 ^ 3 * ((ε : 𝓞 K) * c₀) ≠ 0 := mul_ne_zero (pow_ne_zero 3 δ3_ne_zero) hD
  have h9L : δ3 ^ 3 * ((ε : 𝓞 K) * c₀) ∣ 9 * L := by
    obtain ⟨l, hl⟩ := hDL
    exact ⟨δ3 * l, by rw [hl, nine_eq_δ3_pow]; ring⟩
  -- an inverse of `r₁ = ∏_{P∈A₁}π_P` modulo `λ³D`
  have hc₀P : ∀ P ∈ A₁, c₀ ∉ P.1 := fun P hP hm => hA₁ P hP (by rw [hLg]; exact P.1.mul_mem_left _ hm)
  have hrc : IsCoprime (∏ P ∈ A₁, πP P) c₀ :=
    IsCoprime.prod_left fun P hP => ((isCoprime_πP_iff P c₀).2 (hc₀P P hP)).symm
  have hrδ : IsCoprime (∏ P ∈ A₁, πP P) δ3 := (isCoprime_δ3 (primary_prod_πP A₁)).symm
  have hcop : IsCoprime (∏ P ∈ A₁, πP P) (δ3 ^ 3 * ((ε : 𝓞 K) * c₀)) :=
    hrδ.pow_right.mul_right ((isCoprime_mul_unit_left_right ε.isUnit _ _).2 hrc)
  obtain ⟨u₁, k₁, hu₁⟩ := hcop
  refine ⟨(ε : 𝓞 K) * c₀, cH, dH, δ₀ * u₁, hD, hDL, hdH, fun A hA hr j => ?_⟩
  obtain ⟨κ₀, hκ, hall⟩ := group_cusp hd.2.2.2.2.2.2.2.2 hL h₀ A hA hg hLg hac (fun P _ => hx P) ε hs
    (hcase_transfer hLg hr hcase)
  have hDA : ∀ P ∈ A, (ε : 𝓞 K) * c₀ ∉ P.1 := fun P hP hm => hA P hP (by
    obtain ⟨k, hk⟩ := hDL
    rw [hk]; exact P.1.mul_mem_right _ hm)
  have hsA : ∀ P ∈ A, (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P ∉ P.1 := fun P hP =>
    cuspS_not_mem ε (fun hm => hA P hP (by rw [hLg]; exact P.1.mul_mem_left _ hm))
  obtain ⟨u, e, hu, he, hsum⟩ := group_sum (s := fun P => (ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P) h₀ A j hD
    hDA hdH hsA hall
  refine ⟨conj κ₀ * ∏ P : A, (chiP P.1.1 ((ε : 𝓞 K) * c₀ * δ3 ^ 2 * rP A P.1) ^ 2)⁻¹ *
    ωloc P.1 (j P.1) (e P.1), ?_, fun z v hv => ?_⟩
  · rw [norm_mul, Complex.norm_conj, hκ, one_mul, norm_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    rw [norm_mul, norm_inv, norm_pow, norm_chiP_of_not_mem P.1 (hsA P.1 P.2), one_pow, inv_one, one_mul,
      norm_ωloc P.1 (j P.1) (he P.1 P.2)]
  · rw [hsum z v hv]
    congr 2
    funext m
    -- `u ≡ u₁ (mod λ³D)`
    have huu : δ3 ^ 3 * ((ε : 𝓞 K) * c₀) ∣ u - u₁ := by
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hr
      obtain ⟨c, hc'⟩ := h9L
      exact ⟨u * k₁ + u₁ * a - u₁ * u * b * c, by
        linear_combination (-u) * hu₁ + u₁ * ha - (u₁ * u) * hb - (u₁ * u * b) * hc'⟩
    have hψ : ψc (δ3 ^ 3 * ((ε : 𝓞 K) * c₀)) (-(m * δ₀) * u) =
        ψc (δ3 ^ 3 * ((ε : 𝓞 K) * c₀)) (-(m * (δ₀ * u₁))) := by
      refine ψc_congr _ hc ?_
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      obtain ⟨w, hw⟩ := huu
      exact ⟨-(m * δ₀) * w, by linear_combination (-(m * δ₀)) * hw⟩
    rw [hψ]

/-- The class of `r = ∏_{P∈A}π_P` modulo `9L`. -/
def rcls (L : 𝓞 K) (A : Finset Pr) : 𝓞 K ⧸ span {9 * L} := Ideal.Quotient.mk _ (∏ P ∈ A, πP P)

open Classical in
/-- **The twisted `θ̄` in cusp coordinates, with uniform data** (the companion paper's (A.4) with its
Lemma 6.3): the data `D`, `c_H`, `d_H` and `y` of round 371's `twisted_theta_expansion` can be chosen as
functions of the residue `h₀` and of the class of `∏_{P∈A}π_P` modulo `9L` alone, before the twist
`φ₀`, the primes `Ps` and the exponents `j` are given. Only the unimodular `C₀` depends on the group. -/
theorem twisted_theta_expansion_unif {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) :
    ∃ (D : (𝓞 K ⧸ span {L}) → (𝓞 K ⧸ span {9 * L}) → 𝓞 K)
      (cH : (𝓞 K ⧸ span {L}) → (𝓞 K ⧸ span {9 * L}) → ℂ)
      (dH : (𝓞 K ⧸ span {L}) → (𝓞 K ⧸ span {9 * L}) → 𝓞 K → ℂ)
      (y : (𝓞 K ⧸ span {L}) → (𝓞 K ⧸ span {9 * L}) → 𝓞 K),
      (∀ h₀ ρ, D h₀ ρ ≠ 0 ∧ D h₀ ρ ∣ L ∧ ThetaSupp Kc (dH h₀ ρ)) ∧
      ∀ φ₀ : 𝓞 K → ℂ, (∀ z u, φ₀ (z + L * u) = φ₀ z) → φ₀ 0 = 0 →
      ∀ Ps : Finset Pr, (∀ P ∈ Ps, L ∉ P.1) → ∀ j : Pr → ℕ,
      ∃ C₀ : (𝓞 K ⧸ span {L}) → Finset Pr → ℂ, (∀ h₀, ∀ A ∈ Ps.powerset, ‖C₀ h₀ A‖ = 1) ∧
      ∀ z (v : ℝ), 0 < v →
        ∑' m : 𝓞 K, twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)) * (v : ℂ) *
            besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9) =
          ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
            ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
              (C₀ h₀ A * thSer (conj (cH h₀ (rcls L A)) * ∏ P : A, Bloc P.1.1 (j P.1) 0)
                (fun m => conj (dH h₀ (rcls L A) (-m)) *
                  ψc (δ3 ^ 3 * D h₀ (rcls L A)) (-(m * y h₀ (rcls L A))) * ∏ P : A, Bloc P.1.1 (j P.1) m)
                (-cuspW (D h₀ (rcls L A) * ∏ P ∈ A, πP P) z v)
                (cuspV (D h₀ (rcls L A) * ∏ P ∈ A, πP P) z v)) := by
  have href : ∀ (h₀ : 𝓞 K ⧸ span {L}) (ρ : 𝓞 K ⧸ span {9 * L}),
      ∃ (D : 𝓞 K) (cH : ℂ) (dH : 𝓞 K → ℂ) (y : 𝓞 K), (D ≠ 0 ∧ D ∣ L ∧ ThetaSupp Kc dH) ∧
        ∀ A : Finset Pr, (∀ P ∈ A, L ∉ P.1) → rcls L A = ρ → ∀ j : Pr → ℕ,
        ∃ C₀ : ℂ, ‖C₀‖ = 1 ∧ ∀ z (v : ℝ), 0 < v →
          ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
              (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) *
                conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) =
            C₀ * thSer (conj cH * ∏ P : A, Bloc P.1.1 (j P.1) 0)
              (fun m => conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * y)) * ∏ P : A, Bloc P.1.1 (j P.1) m)
              (-cuspW (D * ∏ P ∈ A, πP P) z v) (cuspV (D * ∏ P ∈ A, πP P) z v) := by
    intro h₀ ρ
    by_cases hex : ∃ A₁ : Finset Pr, (∀ P ∈ A₁, L ∉ P.1) ∧ rcls L A₁ = ρ
    · obtain ⟨A₁, hA₁, hρ⟩ := hex
      obtain ⟨D, cH, dH, y, hD, hDL, hdH, hall⟩ := group_expansion_ref hd hL h₀ A₁ hA₁
      refine ⟨D, cH, dH, y, ⟨hD, hDL, hdH⟩, fun A hA hρA j => hall A hA ?_ j⟩
      rw [← hρ] at hρA
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hρA)
    · exact ⟨1, 0, 0, 0, ⟨one_ne_zero, one_dvd L, hd.1.1, fun m hm => (hm rfl).elim⟩,
        fun A hA hρA => absurd ⟨A, hA, hρA⟩ hex⟩
  choose D cH dH y hDATA hgrp using href
  refine ⟨D, cH, dH, y, hDATA, fun φ₀ hφ hφ0 Ps hPs j => ?_⟩
  have hC : ∀ (h₀ : 𝓞 K ⧸ span {L}) (A : Finset Pr), ∃ C₀ : ℂ, A ∈ Ps.powerset → ‖C₀‖ = 1 ∧
      ∀ z (v : ℝ), 0 < v →
        ∑ h ∈ Fintype.piFinset (fun P : A => (Finset.univ : Finset (𝓞 K ⧸ span {πP P.1})).erase 0),
            (∏ P : A, locCoef P.1 (j P.1) (repQ (πP P.1) (h P))) *
              conj (θ (z + trShift L ⟨(h₀, A), h⟩) v) =
          C₀ * thSer (conj (cH h₀ (rcls L A)) * ∏ P : A, Bloc P.1.1 (j P.1) 0)
            (fun m => conj (dH h₀ (rcls L A) (-m)) *
              ψc (δ3 ^ 3 * D h₀ (rcls L A)) (-(m * y h₀ (rcls L A))) * ∏ P : A, Bloc P.1.1 (j P.1) m)
            (-cuspW (D h₀ (rcls L A) * ∏ P ∈ A, πP P) z v)
            (cuspV (D h₀ (rcls L A) * ∏ P ∈ A, πP P) z v) := by
    intro h₀ A
    by_cases hA : A ∈ Ps.powerset
    · obtain ⟨C₀, hC₀, hid⟩ :=
        hgrp h₀ (rcls L A) A (fun P hP => hPs P (Finset.mem_powerset.1 hA hP)) rfl j
      exact ⟨C₀, fun _ => ⟨hC₀, hid⟩⟩
    · exact ⟨1, fun h => absurd h hA⟩
  choose C₀ hC₀ using hC
  refine ⟨C₀, fun h₀ A hA => (hC₀ h₀ A hA).1, fun z v hv => ?_⟩
  rw [twisted_theta_groups hd.2.2.2.2.1 hd.1 hd.2.2.2.1 hL φ₀ hφ hφ0 Ps j z hv]
  refine finsum_congr fun h₀ => ?_
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [(hC₀ h₀ A hA).2 z v hv]

open scoped ContDiff

open Classical in
/-- **The dual sums with uniform data** (the companion paper's (6.9) with its Lemma 6.3): round 376's
`twisted_theta_voronoi`, with the data `D`, `d_H` and `y` of each group functions of the residue `h₀` and
of the class of `∏_{P∈A}π_P` modulo `9L` alone, chosen before the twist, the primes and the exponents. -/
theorem twisted_theta_voronoi_unif {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) :
    ∃ (D : (𝓞 K ⧸ span {L}) → (𝓞 K ⧸ span {9 * L}) → 𝓞 K)
      (dH : (𝓞 K ⧸ span {L}) → (𝓞 K ⧸ span {9 * L}) → 𝓞 K → ℂ)
      (y : (𝓞 K ⧸ span {L}) → (𝓞 K ⧸ span {9 * L}) → 𝓞 K),
      (∀ h₀ ρ, D h₀ ρ ≠ 0 ∧ D h₀ ρ ∣ L ∧ ThetaSupp Kc (dH h₀ ρ)) ∧
      ∀ φ₀ : 𝓞 K → ℂ, (∀ z u, φ₀ (z + L * u) = φ₀ z) → φ₀ 0 = 0 →
      ∀ Ps : Finset Pr, (∀ P ∈ Ps, L ∉ P.1) → ∀ j : Pr → ℕ,
      ∃ C₀ : (𝓞 K ⧸ span {L}) → Finset Pr → ℂ, (∀ h₀, ∀ A ∈ Ps.powerset, ‖C₀ h₀ A‖ = 1) ∧
      ∀ (W : ℝ → ℂ) (α₀ β₀ : ℝ), 0 < α₀ → α₀ ≤ β₀ → (∀ y, y < α₀ ∨ β₀ < y → W y = 0) →
        ContDiff ℝ ∞ W → ∀ N : ℝ, (∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
        ∀ Z : ℝ, 0 < Z →
        ∫ u : ℝ, mellin (Vstar W) (((2 : ℝ) : ℂ) + u * I - 1 / 2) *
            Fq (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)))
              (fun m => 2 * Real.pi * I * conj (σO m) / 9) (((2 : ℝ) : ℂ) + u * I) *
            (Z : ℂ) ^ (((2 : ℝ) : ℂ) + u * I - 1 / 2) =
          ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
            ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
              (C₀ h₀ A * (-(σO (D h₀ (rcls L A) * ∏ P ∈ A, πP P) ^ 2)⁻¹ *
                ∑' m : 𝓞 K, conj (dH h₀ (rcls L A) (-m)) *
                    ψc (δ3 ^ 3 * D h₀ (rcls L A)) (-(m * y h₀ (rcls L A))) *
                    (∏ P : A, Bloc P.1.1 (j P.1) m) * (2 * Real.pi * I * σO m / 9) *
                  ((Complex.normSq (σO (D h₀ (rcls L A) * ∏ P ∈ A, πP P)) *
                    ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
                  (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
                    (4 * Complex.normSq (σO (D h₀ (rcls L A) * ∏ P ∈ A, πP P)) ^ 2) * Z)))) := by
  obtain ⟨D, cH, dH, y, hDATA, hexp⟩ := twisted_theta_expansion_unif hd hL
  refine ⟨D, dH, y, hDATA, fun φ₀ hφ hφ0 Ps hPs j => ?_⟩
  obtain ⟨C₀, hC₀, hid⟩ := hexp φ₀ hφ hφ0 Ps hPs j
  have hDA : ∀ h₀, ∀ A ∈ Ps.powerset, D h₀ (rcls L A) ≠ 0 ∧ ThetaSupp Kc (dH h₀ (rcls L A)) :=
    fun h₀ A _ => ⟨(hDATA h₀ _).1, (hDATA h₀ _).2.2⟩
  exact ⟨C₀, hC₀, fun W α₀ β₀ hα₀ hαβ₀ hW hs N hN Z hZ =>
    twisted_theta_voronoi_of hd.1 hL φ₀ hφ Ps j (fun h₀ A => D h₀ (rcls L A)) C₀
      (fun h₀ A => dH h₀ (rcls L A)) (fun h₀ A => y h₀ (rcls L A)) hDA
      (fun v hv => twisted_theta_dbar_of hd.1 hL φ₀ hφ Ps j (fun h₀ A => D h₀ (rcls L A)) C₀
        (fun h₀ A => cH h₀ (rcls L A)) (fun h₀ A => dH h₀ (rcls L A)) (fun h₀ A => y h₀ (rcls L A)) hDA
        hid hv) hα₀ hαβ₀ hW hs hN hZ⟩

end Eis

end

#print axioms Eis.hcase_transfer
#print axioms Eis.group_expansion_ref
#print axioms Eis.twisted_theta_expansion_unif
#print axioms Eis.twisted_theta_voronoi_unif
