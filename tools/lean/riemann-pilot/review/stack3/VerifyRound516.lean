import KubotaUniform
import KubotaGHolo
import KubotaEisTrunc

/-! Round 516: the three declarations removed as special cases of a lemma that stays. Each `example` is the
removed theorem's statement, copied from its source at commit 6ff3413, proved in one step from the general
lemma. Not compiled by a build script: compile it against the built stack (see the reference section of
`STRUCTURAL-REVIEW.md`). -/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics
open scoped Topology ContDiff ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

-- `KubotaContour.twisted_theta_voronoi` (round 376) from `KubotaUniform.twisted_theta_voronoi_unif`
-- (round 379), with the data of the group `(h₀, A)` taken at the class `rcls L A`.
open Classical in
example {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (hφ0 : φ₀ 0 = 0) (Ps : Finset Pr) (hPs : ∀ P ∈ Ps, L ∉ P.1)
    (j : Pr → ℕ) :
    ∃ (D : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K) (C₀ : (𝓞 K ⧸ span {L}) → Finset Pr → ℂ)
      (dH : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K → ℂ) (y : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K),
      (∀ h₀, ∀ A ∈ Ps.powerset, D h₀ A ≠ 0 ∧ D h₀ A ∣ L ∧ ‖C₀ h₀ A‖ = 1 ∧ ThetaSupp Kc (dH h₀ A)) ∧
      ∀ (W : ℝ → ℂ) (α₀ β₀ : ℝ), 0 < α₀ → α₀ ≤ β₀ → (∀ y, y < α₀ ∨ β₀ < y → W y = 0) →
        ContDiff ℝ ∞ W → ∀ N : ℝ, (∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
        ∀ Z : ℝ, 0 < Z →
        ∫ u : ℝ, mellin (Vstar W) (((2 : ℝ) : ℂ) + u * I - 1 / 2) *
            Fq (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)))
              (fun m => 2 * Real.pi * I * conj (σO m) / 9) (((2 : ℝ) : ℂ) + u * I) *
            (Z : ℂ) ^ (((2 : ℝ) : ℂ) + u * I - 1 / 2) =
          ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
            ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
              (C₀ h₀ A * (-(σO (D h₀ A * ∏ P ∈ A, πP P) ^ 2)⁻¹ *
                ∑' m : 𝓞 K, conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
                    (∏ P : A, Bloc P.1.1 (j P.1) m) * (2 * Real.pi * I * σO m / 9) *
                  ((Complex.normSq (σO (D h₀ A * ∏ P ∈ A, πP P)) *
                    ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
                  (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
                    (4 * Complex.normSq (σO (D h₀ A * ∏ P ∈ A, πP P)) ^ 2) * Z)))) := by
  obtain ⟨D, dH, y, hDATA, h⟩ := twisted_theta_voronoi_unif hd hL
  obtain ⟨C₀, hC₀, hid⟩ := h φ₀ hφ hφ0 Ps hPs j
  exact ⟨fun h₀ A => D h₀ (rcls L A), C₀, fun h₀ A => dH h₀ (rcls L A), fun h₀ A => y h₀ (rcls L A),
    fun h₀ A hA => ⟨(hDATA h₀ _).1, (hDATA h₀ _).2.1, hC₀ h₀ A hA, (hDATA h₀ _).2.2⟩, hid⟩

-- `KubotaEisTrunc.memLp_gfun` (round 423) from `KubotaGHolo.memLp_gfun_all` (round 424). The general lemma
-- needs no hypothesis on `Re s`, so `hs` goes unused; the linter is silenced for this example only.
set_option linter.unusedVariables false in
example {R : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : 0 ≤ s.re) {Y : ℝ} (hY : 0 < Y) :
    MemLp (gfun R s Y) 2 (muR rhoG) := by
  exact memLp_gfun_all hR hY s

-- `KubotaUnfold.lintegral_puLe_top_lt_top` (round 386) from `KubotaEisTrunc.lintegral_puLe_top_mul_lt_top`
-- (round 423) at `F = 1`.
example (Γ : Subgroup SL(2, 𝓞 K))
    [Finite ((⊤ : Subgroup SL(2, 𝓞 K)) ⧸ Γ.subgroupOf ⊤)] :
    ∫⁻ p, puLe ⊤ Γ rhoK p ∂uhsMeasure < ⊤ := by
  have := lintegral_puLe_top_mul_lt_top Γ (F := fun _ => 1) measurable_const
    (fun _ => ⟨1, ENNReal.one_ne_top, fun _ _ => le_rfl⟩)
  simpa using this

end Eis
