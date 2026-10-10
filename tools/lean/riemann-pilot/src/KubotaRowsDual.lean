import KubotaUniform
import KubotaCompleted

/-! # The completed sums of the rows as the dual sums (round 380)

S5f-6 of round 360's plan, part 3. The companion paper's Proposition 6.2 says: "`The quantity $T(X;\Psi)$
defined in \eqref{eq:T} is a sum of $O_{\Psi_0,S}(2^{|\mathcal P|})$ terms of the form`" (its (6.9)). This file
proves it for the rows `u₀tk₀`, in the form of round 376's dual sums, with the data of round 379, which
depend on `k₀` only through `∏_{P∈𝒜}π_P` modulo `9·72`.

* **The twist in one product** (`rowPs` and `rowJ`, definitions; **`twist_rows`**, with `chiPow_one`,
  `mem_of_mem_primeSet` and `disjoint_primeSet`): round 365's (6.17), `φ₀·∏_{P∣tg}χ_P^{j_P}·∏_{P∣k₀}χ_P`, is
  `φ₀·∏_{P∈Ps}χ_P^{j_P}` over the primes of `tg` and of `k₀`, with `j_P = 1` at those of `k₀`.
* **The dual sums** (**`compT_rows_dual`**, with `seventytwo_not_mem`): under the data and the value formula
  of `KubotaTheta`, `T(X; Ψ_{u₀tk₀,g})` is `(8π/27)/(C̄·2πiσ̄(δ₃)/9)` times the dual sums of round 379's
  `twisted_theta_voronoi_unif` at `L = 72` and `Z = 4π²X/27`.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics UniqueFactorizationMonoid
open scoped Topology ContDiff ComplexConjugate

noncomputable section

namespace Eis

theorem chiPow_one (P : Ideal (𝓞 K)) (x : 𝓞 K) : chiPow P 1 x = chiP P x := by
  unfold chiPow
  by_cases hx : x ∈ P
  · rw [ite_eq_left hx, chiP_eq_zero_of_mem hx]
  · rw [ite_eq_right hx, pow_one]

/-- `72 ∉ P` for the primes prime to `6`. -/
theorem seventytwo_not_mem (P : Pr) : (72 : 𝓞 K) ∉ P.1 := by
  intro h
  have h6 : (6 : 𝓞 K) ^ 3 ∈ P.1 := by
    rw [show (6 : 𝓞 K) ^ 3 = 72 * 3 by norm_num]
    exact P.1.mul_mem_right 3 h
  exact P.2.2 (P.2.1.isPrime.mem_of_pow_mem 3 h6)

theorem mem_of_mem_primeSet {x : 𝓞 K} {P : Pr} (h : P ∈ primeSet (span {x})) : x ∈ P.1 :=
  (Ideal.span_singleton_le_iff_mem _).1 (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors (mem_primeSet.1 h)))

/-- Coprime elements have disjoint prime sets. -/
theorem disjoint_primeSet {x y : 𝓞 K} (h : IsCoprime x y) :
    Disjoint (primeSet (span {y})) (primeSet (span {x})) := by
  rw [Finset.disjoint_left]
  intro P hy hx
  obtain ⟨a, b, hab⟩ := h
  apply P.2.1.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact P.1.add_mem (P.1.mul_mem_left _ (mem_of_mem_primeSet hx)) (P.1.mul_mem_left _ (mem_of_mem_primeSet hy))

/-- The primes of the twist of the rows: those of `tg` and those of `k₀`. -/
def rowPs (t g k₀ : 𝓞 K) : Finset Pr := primeSet (span {t * g}) ∪ primeSet (span {k₀})

open Classical in
/-- The exponents of the twist of the rows: `1` at the primes of `k₀`, and round 365's `j_P` at the
others. -/
def rowJ (t g k₀ : 𝓞 K) (P : Pr) : ℕ := if P ∈ primeSet (span {k₀}) then 1 else jFix t g P

/-- **The twist of the rows in one product** (round 365's (6.17)): `φ₀·∏_{P∣tg}χ_P^{j_P}·∏_{P∣k₀}χ_P` is
`φ₀·∏_{P∈Ps}χ_P^{j_P}` over the primes of `tg` and of `k₀`, with `j_P = 1` at those of `k₀`. -/
theorem twist_rows {φ₀ F : 𝓞 K → ℂ} {t g k₀ : 𝓞 K} (hcop : IsCoprime k₀ (t * g))
    (h : ∀ x, F x = φ₀ x * (∏ P ∈ primeSet (span {t * g}), chiPow P.1 (jFix t g P) x) *
      ∏ P ∈ primeSet (span {k₀}), chiP P.1 x) :
    F = fun x => φ₀ x * ∏ P ∈ rowPs t g k₀, chiPow P.1 (rowJ t g k₀ P) x := by
  funext x
  rw [h x, rowPs, Finset.prod_union (disjoint_primeSet hcop), mul_assoc]
  congr 2
  · refine Finset.prod_congr rfl fun P hP => ?_
    have hP' : P ∉ primeSet (span {k₀}) := Finset.disjoint_left.1 (disjoint_primeSet hcop) hP
    rw [rowJ, ite_eq_right hP']
  · refine Finset.prod_congr rfl fun P hP => ?_
    rw [rowJ, ite_eq_left hP, chiPow_one]

open Classical in
/-- **The completed sums of the rows as the dual sums** (the companion paper's Proposition 6.2 for the
rows `u₀tk₀`, with the data of its Lemma 6.3): under the display's data and value formula, with `L = 72`,
there are data `D`, `d_H`, `y` that are functions of `h₀ mod 72` and of `∏_{P∈A}π_P mod 9·72`, such that
for every row, `T(X; Ψ_{u₀tk₀,g})` is `(8π/27)/(C̄·2πiσ̄(δ₃)/9)` times the dual sums of round 379's
`twisted_theta_voronoi_unif` at `Z = 4π²X/27`, for the twist `φ₀·∏_{P∈Ps}χ_P^{j_P}` of round 365. -/
theorem compT_rows_dual {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {C : ℂ} (hC : C ≠ 0)
    (hval : ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n}))) :
    ∃ (D : (𝓞 K ⧸ span {(72 : 𝓞 K)}) → (𝓞 K ⧸ span {9 * (72 : 𝓞 K)}) → 𝓞 K)
      (dH : (𝓞 K ⧸ span {(72 : 𝓞 K)}) → (𝓞 K ⧸ span {9 * (72 : 𝓞 K)}) → 𝓞 K → ℂ)
      (y : (𝓞 K ⧸ span {(72 : 𝓞 K)}) → (𝓞 K ⧸ span {9 * (72 : 𝓞 K)}) → 𝓞 K),
      (∀ h₀ ρ, D h₀ ρ ≠ 0 ∧ D h₀ ρ ∣ 72 ∧ ThetaSupp Kc (dH h₀ ρ)) ∧
      ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (u₀ : (𝓞 K)ˣ) (t g : 𝓞 K), t ≠ 0 → g ≠ 0 →
      ∃ φ₀ : 𝓞 K → 𝓞 K → ℂ, (∀ k x u, φ₀ k (x + 72 * u) = φ₀ k x) ∧
        (∀ k k' x, (4 : 𝓞 K) ∣ k - k' → φ₀ k x = φ₀ k' x) ∧ (∀ k x, ‖φ₀ k x‖ ≤ 1) ∧ (∀ k, φ₀ k 0 = 0) ∧
      ∀ k₀ : 𝓞 K, Primary k₀ → Squarefree (span {k₀}) → (absNorm (span {k₀})).Coprime 6 →
        IsCoprime k₀ (t * g) →
      ∃ C₀ : (𝓞 K ⧸ span {(72 : 𝓞 K)}) → Finset Pr → ℂ,
        (∀ h₀, ∀ A ∈ (rowPs t g k₀).powerset, ‖C₀ h₀ A‖ = 1) ∧
      ∀ (W : ℝ → ℂ) (α β : ℝ), 0 < α → α ≤ β → (∀ y, y < α ∨ β < y → W y = 0) →
        ContDiff ℝ ∞ W → ∀ N : ℝ, (∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
        ∀ X : ℝ, 0 < X →
        compT ξ (u₀ * t * k₀) g W X =
          (((8 * Real.pi / 27 : ℝ)) : ℂ) / (conj C * (2 * Real.pi * I * conj (σO δ3) / 9)) *
          ∑ᶠ h₀ : 𝓞 K ⧸ span {(72 : 𝓞 K)}, fCoef 72 (φ₀ k₀) (repQ 72 h₀) *
            ∑ A ∈ (rowPs t g k₀).powerset, (∏ P ∈ rowPs t g k₀ \ A, locCoef P (rowJ t g k₀ P) 0) *
              (C₀ h₀ A * (-(σO (D h₀ (rcls 72 A) * ∏ P ∈ A, πP P) ^ 2)⁻¹ *
                ∑' m : 𝓞 K, conj (dH h₀ (rcls 72 A) (-m)) *
                    ψc (δ3 ^ 3 * D h₀ (rcls 72 A)) (-(m * y h₀ (rcls 72 A))) *
                    (∏ P : A, Bloc P.1.1 (rowJ t g k₀ P.1) m) * (2 * Real.pi * I * σO m / 9) *
                  ((Complex.normSq (σO (D h₀ (rcls 72 A) * ∏ P ∈ A, πP P)) *
                    ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
                  (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
                    (4 * Complex.normSq (σO (D h₀ (rcls 72 A) * ∏ P ∈ A, πP P)) ^ 2) *
                    (4 * Real.pi ^ 2 * X / 27))))) := by
  obtain ⟨D, dH, y, hDATA, hvor⟩ := twisted_theta_voronoi_unif hd (L := 72) (by norm_num)
  refine ⟨D, dH, y, hDATA, fun ξ u₀ t g ht hg => ?_⟩
  obtain ⟨φ₀, hper, hk4, hbd, hz, h617⟩ := twist_617 ξ u₀ ht hg
  refine ⟨φ₀, hper, hk4, hbd, hz, fun k₀ hk hsq h6 hcop => ?_⟩
  obtain ⟨C₀, hC₀, hid⟩ := hvor (φ₀ k₀) (fun z u => hper k₀ z u) (hz k₀) (rowPs t g k₀)
    (fun P _ => seventytwo_not_mem P) (rowJ t g k₀)
  refine ⟨C₀, hC₀, fun W α β hα hαβ hW hs N hN X hX => ?_⟩
  have hN2 : ∀ i ≤ 2, ∀ y, ‖iteratedDeriv i W y‖ ≤ N := fun i hi => hN i (by omega)
  rw [compT_theta ξ (u₀ * t * k₀) g hd.1 hval hC hα hαβ hW hs hN2 hX,
    twist_rows hcop (h617 k₀ hk hsq h6 hcop)]
  congr 1
  exact hid W α β hα hαβ hW hs N hN _ (by positivity)

end Eis

end

#print axioms Eis.chiPow_one
#print axioms Eis.seventytwo_not_mem
#print axioms Eis.mem_of_mem_primeSet
#print axioms Eis.disjoint_primeSet
#print axioms Eis.twist_rows
#print axioms Eis.compT_rows_dual
