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

Round 493 (step 2 of round 491's plan for door 5(b)): the characters `ξ` are modulo any `md ≠ 0` and
`L = 72·md`. The primes of `tg` dividing `md` contain `L`, so their factors `χ_P^{j_P}` move into `φ₀`, which
stays periodic modulo `L` (`mul_md_not_mem`); `Ps` runs over round 493's `tgPrimes md t g` and the primes of
`k₀`, now prime to `md`. At `md = 4` this is round 380's twist with `L = 288` in place of `72`.
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

/-- `72·md ∉ P` for the primes prime to `6` not containing `md`. -/
theorem mul_md_not_mem {md : 𝓞 K} {P : Pr} (h : md ∉ P.1) : 72 * md ∉ P.1 := fun hm =>
  (P.2.1.isPrime.mem_or_mem hm).elim (seventytwo_not_mem P) h

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

/-- The primes of the twist of the rows: those of `tg` not dividing `md` (`tgPrimes`) and those of `k₀`. -/
def rowPs (md t g k₀ : 𝓞 K) : Finset Pr := tgPrimes md t g ∪ primeSet (span {k₀})

open Classical in
/-- The exponents of the twist of the rows: `1` at the primes of `k₀`, and round 365's `j_P` at the
others. -/
def rowJ (t g k₀ : 𝓞 K) (P : Pr) : ℕ := if P ∈ primeSet (span {k₀}) then 1 else jFix t g P

/-- **The twist of the rows in one product** (round 365's (6.17)): `φ₀·∏_{P∈𝒫_fix}χ_P^{j_P}·∏_{P∣k₀}χ_P`
is `φ₀·∏_{P∈Ps}χ_P^{j_P}` over `𝒫_fix = tgPrimes md t g` and the primes of `k₀`, with `j_P = 1` at those of
`k₀`. -/
theorem twist_rows {φ₀ F : 𝓞 K → ℂ} {md t g k₀ : 𝓞 K} (hcop : IsCoprime k₀ (t * g))
    (h : ∀ x, F x = φ₀ x * (∏ P ∈ tgPrimes md t g, chiPow P.1 (jFix t g P) x) *
      ∏ P ∈ primeSet (span {k₀}), chiP P.1 x) :
    F = fun x => φ₀ x * ∏ P ∈ rowPs md t g k₀, chiPow P.1 (rowJ t g k₀ P) x := by
  have hdisj : Disjoint (tgPrimes md t g) (primeSet (span {k₀})) :=
    Finset.disjoint_of_subset_left (tgPrimes_subset md t g) (disjoint_primeSet hcop)
  funext x
  rw [h x, rowPs, Finset.prod_union hdisj, mul_assoc]
  congr 2
  · refine Finset.prod_congr rfl fun P hP => ?_
    have hP' : P ∉ primeSet (span {k₀}) := Finset.disjoint_left.1 hdisj hP
    rw [rowJ, ite_eq_right hP']
  · refine Finset.prod_congr rfl fun P hP => ?_
    rw [rowJ, ite_eq_left hP, chiPow_one]

open Classical in
/-- **The completed sums of the rows as the dual sums** (the companion paper's Proposition 6.2 for the
rows `u₀tk₀`, with the data of its Lemma 6.3), for the characters `ξ` modulo any `md ≠ 0` (round 493;
round 380 had `md = 4` and `L = 72`): under the display's data and value formula, with `L = 72·md`, there are
data `D`, `d_H`, `y` that are functions of `h₀ mod L` and of `∏_{P∈A}π_P mod 9L`, such that for every row with
`k₀` prime to `tg` and to `md`, `T(X; Ψ_{u₀tk₀,g})` is `(8π/27)/(C̄·2πiσ̄(δ₃)/9)` times the dual sums of round
379's `twisted_theta_voronoi_unif` at `Z = 4π²X/27`, for the twist `φ₀·∏_{P∈Ps}χ_P^{j_P}` of round 365, where
`φ₀` carries the factors `χ_P^{j_P}` at the primes `P` of `tg` dividing `md`. -/
theorem compT_rows_dual {md : 𝓞 K} [NeZero md] {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ}
    {τ tP tM : 𝓞 K → ℂ} (hd : KubotaData θ Kc c0 cP cM τ tP tM) {C : ℂ} (hC : C ≠ 0)
    (hval : ∀ n b : 𝓞 K, Primary n → Primary b → Squarefree (span {n}) →
      (absNorm (span {n * b})).Coprime 6 →
      τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
          sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n}))) :
    ∃ (D : (𝓞 K ⧸ span {72 * md}) → (𝓞 K ⧸ span {9 * (72 * md)}) → 𝓞 K)
      (dH : (𝓞 K ⧸ span {72 * md}) → (𝓞 K ⧸ span {9 * (72 * md)}) → 𝓞 K → ℂ)
      (y : (𝓞 K ⧸ span {72 * md}) → (𝓞 K ⧸ span {9 * (72 * md)}) → 𝓞 K),
      (∀ h₀ ρ, D h₀ ρ ≠ 0 ∧ D h₀ ρ ∣ 72 * md ∧ ThetaSupp Kc (dH h₀ ρ)) ∧
      ∀ (ξ : MulChar (𝓞 K ⧸ span {md}) ℂ) (u₀ : (𝓞 K)ˣ) (t g : 𝓞 K), t ≠ 0 → g ≠ 0 →
      ∃ φ₀ : 𝓞 K → 𝓞 K → ℂ, (∀ k x u, φ₀ k (x + 72 * md * u) = φ₀ k x) ∧
        (∀ k k' x, (4 : 𝓞 K) ∣ k - k' → φ₀ k x = φ₀ k' x) ∧ (∀ k x, ‖φ₀ k x‖ ≤ 1) ∧ (∀ k, φ₀ k 0 = 0) ∧
      ∀ k₀ : 𝓞 K, Primary k₀ → Squarefree (span {k₀}) → (absNorm (span {k₀})).Coprime 6 →
        IsCoprime k₀ (t * g) → IsCoprime k₀ md →
      ∃ C₀ : (𝓞 K ⧸ span {72 * md}) → Finset Pr → ℂ,
        (∀ h₀, ∀ A ∈ (rowPs md t g k₀).powerset, ‖C₀ h₀ A‖ = 1) ∧
      ∀ (W : ℝ → ℂ) (α β : ℝ), 0 < α → α ≤ β → (∀ y, y < α ∨ β < y → W y = 0) →
        ContDiff ℝ ∞ W → ∀ N : ℝ, (∀ i ≤ 14, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
        ∀ X : ℝ, 0 < X →
        compT ξ (u₀ * t * k₀) g W X =
          (((8 * Real.pi / 27 : ℝ)) : ℂ) / (conj C * (2 * Real.pi * I * conj (σO δ3) / 9)) *
          ∑ᶠ h₀ : 𝓞 K ⧸ span {72 * md}, fCoef (72 * md) (φ₀ k₀) (repQ (72 * md) h₀) *
            ∑ A ∈ (rowPs md t g k₀).powerset, (∏ P ∈ rowPs md t g k₀ \ A, locCoef P (rowJ t g k₀ P) 0) *
              (C₀ h₀ A * (-(σO (D h₀ (rcls (72 * md) A) * ∏ P ∈ A, πP P) ^ 2)⁻¹ *
                ∑' m : 𝓞 K, conj (dH h₀ (rcls (72 * md) A) (-m)) *
                    ψc (δ3 ^ 3 * D h₀ (rcls (72 * md) A)) (-(m * y h₀ (rcls (72 * md) A))) *
                    (∏ P : A, Bloc P.1.1 (rowJ t g k₀ P.1) m) * (2 * Real.pi * I * σO m / 9) *
                  ((Complex.normSq (σO (D h₀ (rcls (72 * md) A) * ∏ P ∈ A, πP P)) *
                    ((4 * Real.pi * ‖σO m‖ / 9) ^ 2)⁻¹ : ℝ) : ℂ) *
                  (2 * Real.pi * Vsharp W ((4 * Real.pi * ‖σO m‖ / 9) ^ 2 /
                    (4 * Complex.normSq (σO (D h₀ (rcls (72 * md) A) * ∏ P ∈ A, πP P)) ^ 2) *
                    (4 * Real.pi ^ 2 * X / 27))))) := by
  have hL : (72 : 𝓞 K) * md ≠ 0 := mul_ne_zero (by norm_num) (NeZero.ne md)
  obtain ⟨D, dH, y, hDATA, hvor⟩ := twisted_theta_voronoi_unif hd hL
  refine ⟨D, dH, y, hDATA, fun ξ u₀ t g ht hg => ?_⟩
  obtain ⟨φ₁, hper, hk4, hbd, hz, h617⟩ := twist_617M ξ u₀ ht hg
  -- the factors at the primes of `tg` dividing `md` move into `φ₀`
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : 𝓞 K → 𝓞 K → ℂ, ∀ k x, φ₀ k x = φ₁ k x *
      ∏ P ∈ (primeSet (span {t * g})).filter (fun P => ¬ md ∉ P.1), chiPow P.1 (jFix t g P) x :=
    ⟨_, fun _ _ => rfl⟩
  have hper₀ : ∀ k x u, φ₀ k (x + 72 * md * u) = φ₀ k x := by
    intro k x u
    rw [hφ₀, hφ₀, hper (72 * md) (dvd_mul_right _ _) (dvd_mul_left _ _) k x u]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    have hmdP : md ∈ P.1 := not_not.1 (Finset.mem_filter.1 hP).2
    have hmul : 72 * md * u ∈ P.1 := P.1.mul_mem_right u (P.1.mul_mem_left 72 hmdP)
    have hsub : x + 72 * md * u - x ∈ P.1 := by rwa [add_sub_cancel_left]
    unfold chiPow
    by_cases hx : x ∈ P.1
    · rw [ite_eq_left (P.1.add_mem hx hmul), ite_eq_left hx]
    · have hx' : x + 72 * md * u ∉ P.1 := fun h => hx (by simpa using P.1.sub_mem h hmul)
      rw [ite_eq_right hx', ite_eq_right hx, chiP_congr hsub]
  have hk4₀ : ∀ k k' x, (4 : 𝓞 K) ∣ k - k' → φ₀ k x = φ₀ k' x := fun k k' x h => by
    rw [hφ₀, hφ₀, hk4 k k' x h]
  have hbd₀ : ∀ k x, ‖φ₀ k x‖ ≤ 1 := fun k x => by
    rw [hφ₀, norm_mul, norm_prod]
    calc ‖φ₁ k x‖ * ∏ P ∈ (primeSet (span {t * g})).filter (fun P => ¬ md ∉ P.1),
          ‖chiPow P.1 (jFix t g P) x‖ ≤ 1 * 1 :=
          mul_le_mul (hbd k x) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
            fun P _ => norm_chiPow_le _ _ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hz₀ : ∀ k, φ₀ k 0 = 0 := fun k => by rw [hφ₀, hz k, zero_mul]
  refine ⟨φ₀, hper₀, hk4₀, hbd₀, hz₀, fun k₀ hk hsq h6 hcop hmd => ?_⟩
  have hPs : ∀ P ∈ rowPs md t g k₀, 72 * md ∉ P.1 := by
    intro P hP
    refine mul_md_not_mem ?_
    rcases Finset.mem_union.1 hP with h | h
    · exact (Finset.mem_filter.1 h).2
    · intro hm
      obtain ⟨a, b, hab⟩ := hmd
      apply P.2.1.ne_top
      rw [Ideal.eq_top_iff_one, ← hab]
      exact P.1.add_mem (P.1.mul_mem_left _ (mem_of_mem_primeSet h)) (P.1.mul_mem_left _ hm)
  obtain ⟨C₀, hC₀, hid⟩ := hvor (φ₀ k₀) (fun z u => hper₀ k₀ z u) (hz₀ k₀) (rowPs md t g k₀) hPs
    (rowJ t g k₀)
  refine ⟨C₀, hC₀, fun W α β hα hαβ hW hs N hN X hX => ?_⟩
  have hN2 : ∀ i ≤ 2, ∀ y, ‖iteratedDeriv i W y‖ ≤ N := fun i hi => hN i (by omega)
  have htw : ∀ x, phiTw (twistPsi ξ (u₀ * t * k₀) g) x = φ₀ k₀ x *
      (∏ P ∈ tgPrimes md t g, chiPow P.1 (jFix t g P) x) * ∏ P ∈ primeSet (span {k₀}), chiP P.1 x := by
    intro x
    rw [h617 k₀ hk hsq h6 hcop x, hφ₀, ← Finset.prod_filter_mul_prod_filter_not (primeSet (span {t * g}))
      (fun P => md ∉ P.1)]
    unfold tgPrimes
    ring
  rw [compT_theta ξ (u₀ * t * k₀) g hd.1 hval hC hα hαβ hW hs hN2 hX, twist_rows hcop htw]
  congr 1
  exact hid W α β hα hαβ hW hs N hN _ (by positivity)

end Eis

end

#print axioms Eis.chiPow_one
#print axioms Eis.seventytwo_not_mem
#print axioms Eis.mul_md_not_mem
#print axioms Eis.mem_of_mem_primeSet
#print axioms Eis.disjoint_primeSet
#print axioms Eis.twist_rows
#print axioms Eis.compT_rows_dual
