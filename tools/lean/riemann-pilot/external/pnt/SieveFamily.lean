/-
# Round 600: Type II families (milestone M4: SIEVE-ROUTE.md §10's Lemmas 4′ and 4″)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. Let `L = 2333/1000`, `f0` smooth and real with support in `[1/2, 2]`, `K₀ ≥ 0` and `e₁ > 0`. A
*family* has: a large `q`; `P` with `q^{(401/1000)L} ≤ P ≤ q^{(485/1000)L}`; `S ⊆ (P, 2P]` with coefficients `a_m`;
`K ≤ K₀` primes `x_i` of `Sp`'s ranges at the scales `Q_i ≥ q^{e₁}` (`primesTo Q_i`, the primes up to `2Q_i`), with
the weights `f0(x_i/Q_i)` and `∏_i Q_i ≤ 2^{K₀}q^L/P`; and `J` forms `ℓ_j(m, x) = φ_j(m) + Σ_i e_{ji} log x_i`. For a
unit `a` mod `q`, its `A − B/φ(q)` is `Dsum`: the sum of its weights times `1[n ≡ a] − 1[(n, q) = 1]/φ(q)` at
`n = m∏_i x_i`.

* `family_bound` (Lemma 4′ with Proposition 3′): let `J` continuous integrable `g_j` with integrable `𝓕g_j` be applied
  to the forms, with `2π(Σ_j |e_{ji}|)T₀ ≤ q^η` for each `i` and `0 < η ≤ 10⁻⁵`. The sum over `χ ≠ 1` of the family's
  twisted sums is at most `q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2} ∏_j ‖𝓕g_j‖₁`, plus the number of characters `χ ≠ 1` times
  `Σ_m |a_m| ∏_i Σ_p |f0(p/Q_i)|` times `Σ_j (∫_{|t|>T₀} |𝓕g_j(t)| dt) ∏_{i≠j} ‖𝓕g_i‖₁`.
* `typeII_sharp_explicit` (Lemma 4″): let also `0 ≤ f0 ≤ F₀`, and cut a family with at least one prime by `J` sharp
  comparisons `P_j`, where `P_j` holds when `ℓ_j > 0` and implies `ℓ_j ≥ 0`. If `0 < θ ≤ 1 ≤ Λ`, `ℓ_j ≤ Λ` on the
  family, each comparison has a pivot prime with coefficient `±1`, `T₀ ≥ 1`, `k ≥ 2` and
  `2π(Σ_j |e_{ji}|)T₀ ≤ q^{1/100000}` for each `i`, then `|A − B/φ(q)|` is at most an explicit bound in the cut-off's
  masses and tails (`massB`, `tailB`) and the pivots' counts.
* `typeII_sharp`: fix also `J₀`, `E₀ ≥ 0`, `Λ₀ ≥ 0` and `A₀ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀`,
  every such family with `|a_m| ≤ A₀` for every `m`, `J ≤ J₀`, `|e_{ji}| ≤ E₀`, `ℓ_j ≤ Λ₀ log q` on the family and
  pivots as above has `|A − B/φ(q)| ≤ A₀q^{L−δ}/φ(q)`.

The proof:

* `sum_twist_eq`, `inner_factor`: a separated family sum factors into the twisted `m`-sum and the twisted prime sums,
  which are `SieveWeight.Sp` at the heights `−2πΣ_j ξ_je_{ji}`.
* `family_bound`: `SieveSep.sum_sep` writes each character's sum as an integral over `ℝ^J`. On the box `|ξ_j| ≤ T₀`
  the heights are at most `q^η`, and `SieveTypeII.typeII_step` bounds the sum over `χ ≠ 1`; everywhere the trivial
  bound holds; `SieveSep.sep_bound` combines the two.
* `integral_norm_GC_le`, `mass_GC_le`, `tail_GC_le`: for `SieveSmooth`'s cut-off `G` with `0 < θ ≤ 2Λ`,
  `‖G‖₁ ≤ 2Λ + θ` and `‖𝓕G‖₁ ≤ π(2Λ + θ) + c₂/(2πθ)`, and for `θ > 0`, `Λ ≥ 0`, `k ≥ 2` and `T₀ ≥ 1`,
  `∫_{|ξ|>T₀} |𝓕G| ≤ 2π·2θ^{1−k}c_k(2π)^{−k}T₀^{2−k}`, with `c_k = ‖g^{(k)}‖₁`.
* `dw`, `dw_eq`, `Dsum`, `norm_Dsum_le`: orthogonality, `1[n ≡ a] − 1[(n, q) = 1]/φ(q) = φ(q)⁻¹Σ_{χ≠1} χ(a⁻¹)χ(n)` for
  a unit `a`.
* `abs_prod_sub_prod_le`, `norm_Dsum_sharp_le`: sharp against smooth, from `|∏_j I_j − ∏_j G_j| ≤ Σ_j |I_j − G_j|` for
  values in `[0, 1]`.
* `abs_ind_sub_G_le`, `card_short_le`, `pivot_sum_le`, `pivot_term_le`: near the boundary `|1[P_j] − G| ≤ G̃`, with
  `G̃(u) = G_{θ,θ}(u + θ)`, and over the pivot prime `Σ_y f0(y/Q)G̃(…) ≤ F₀((e^{3θ} − 1)2Q + 1)`.
* `Dsum_sharp_le`, `typeII_sharp_explicit`: the smoothed family and the `J` near-boundary families by `family_bound`,
  and the pivots' counts by `pivot_sum_le`.
* `typeII_sharp`: `θ = q^{−ε₂}` with `ε₂ = 1/(400000(J₀ + 1))`, `Λ = Λ₀ log q + 1`, `T₀ = q^{1/200000}` and
  `k = 1200003`. The masses are at most `Cq^{ε₂}` (`massB_le`) and the tails at most `c′q^{−3}` (`tailB_le`). The box
  and the pivots' counts are at most constants times `A₀q^L` (`box_le`, `pivot_le`). So the bound is at most
  `A₀q^L/φ(q)` times `a₁q^{−7/400000} + a₂q^{−1} + a₃(12q^{−ε₂} + q^{−e₁})`, which is at most `q^{−δ}` for large `q`,
  with `δ = min(ε₂, e₁)/2` (`bracket_le`).

The file imports `SieveSep.lean` and `SieveTypeII.lean`.
-/
import SieveSep
import SieveTypeII

open MeasureTheory Real Complex FourierTransform Finset

namespace SieveFamily

variable {q : ℕ} [NeZero q]

/-- The primes of `Sp`'s range at scale `Q`. -/
noncomputable def primesTo (Q : ℝ) : Finset ℕ := (Finset.range (⌊2 * Q⌋₊ + 1)).filter Nat.Prime

omit [NeZero q] in
/-- For `Q > 0`, a prime sum with the twist `p^{2πiH}` is `Q^{2πiH}` times `Sp` at the height `−2πH`. -/
theorem sum_twist_eq (χ : DirichletCharacter ℂ q) (f0 : ℝ → ℝ) {Q : ℝ} (hQ : 0 < Q) (H : ℝ) :
    ∑ p ∈ primesTo Q, χ p * (f0 (p / Q) : ℂ) * Complex.exp (2 * π * I * H * Real.log p) =
      Complex.exp (2 * π * I * H * Real.log Q) * SieveWeight.Sp χ f0 Q (-(2 * π * H)) := by
  rw [SieveWeight.Sp, primesTo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := (Finset.mem_filter.1 hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hz : (0 : ℝ) < (p : ℝ) / Q := div_pos hp0 hQ
  have hcpow : ((((p : ℝ) / Q : ℝ)) : ℂ) ^ (-((-(2 * π * H) : ℝ) : ℂ) * I) =
      Complex.exp (2 * π * I * H * Real.log p) * Complex.exp (-(2 * π * I * H * Real.log Q)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hz.ne'), ← Complex.ofReal_log hz.le,
      Real.log_div hp0.ne' hQ.ne', ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcpow]
  have hinv : Complex.exp (2 * π * I * H * Real.log Q) * Complex.exp (-(2 * π * I * H * Real.log Q)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (-(χ p * (f0 (p / Q) : ℂ) * Complex.exp (2 * π * I * H * Real.log p))) * hinv

omit [NeZero q] in
/-- The separated sum factors: `Σ_{m,p} w(m, p)e^{2πiΣ_jξ_jℓ_j(m,p)}` is the twisted `m`-sum times the twisted prime
sums. -/
theorem inner_factor (χ : DirichletCharacter ℂ q) (f0 : ℝ → ℝ) (S : Finset ℕ) (a : ℕ → ℂ) {K J : ℕ}
    (Q : ℕ → ℝ) (φ : Fin J → ℕ → ℝ) (e : Fin J → Fin K → ℝ) (ξ : Fin J → ℝ) :
    ∑ x ∈ S ×ˢ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        (a x.1 * χ x.1 * ∏ i : Fin K, (χ (x.2 i) * (f0 (x.2 i / Q i) : ℂ))) *
          Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * ((φ j x.1 + ∑ i : Fin K, e j i * Real.log (x.2 i) : ℝ) : ℂ)) =
      (∑ m ∈ S, a m * χ m * Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m)) *
        ∏ i : Fin K, ∑ p ∈ primesTo (Q i),
          χ p * (f0 (p / Q i) : ℂ) * Complex.exp (2 * π * I * (∑ j, ξ j * e j i) * Real.log p) := by
  rw [Finset.prod_univ_sum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => ?_
  have key : (∑ j, ξ j * (φ j m + ∑ i : Fin K, e j i * Real.log (p i)) : ℝ) =
      ∑ j, ξ j * φ j m + ∑ i : Fin K, (∑ j, ξ j * e j i) * Real.log (p i) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j (i : Fin K) => ξ j * (e j i * Real.log (p i)))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * ((φ j m + ∑ i : Fin K, e j i * Real.log (p i) : ℝ) : ℂ)) =
      Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m) *
        ∏ i : Fin K, Complex.exp (2 * π * I * (∑ j, ξ j * e j i : ℝ) * Real.log (p i)) := by
    have h1 : (∑ j, (ξ j : ℂ) * ((φ j m + ∑ i : Fin K, e j i * Real.log (p i) : ℝ) : ℂ)) =
        (((∑ j, ξ j * (φ j m + ∑ i : Fin K, e j i * Real.log (p i)) : ℝ)) : ℂ) := by push_cast; rfl
    rw [h1, key, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp]
  simp only [Finset.prod_mul_distrib]
  ring

open scoped ContDiff in
/-- **The bound for a smooth family** (SIEVE-ROUTE.md §10's Lemma 4′ with Proposition 3′, before the near-boundary
terms). Let `f0` be smooth with support in `[1/2, 2]`, `e₁ > 0` and `0 < η ≤ 10⁻⁵`. There is `q₀` such that for
`q ≥ q₀`: let `m` run over `S ⊆ (P, 2P]`, `q^{0.401L} ≤ P ≤ q^{0.485L}`, with coefficients `a_m`, and `K ≤ K₀` primes
over `Sp`'s ranges at the scales `Q_i ≥ q^{e₁}`, `∏_i Q_i ≤ 2^{K₀}q^L/P`, with the weights `f0(p_i/Q_i)`; and let `J`
continuous integrable `g_j` with integrable `𝓕g_j` be applied to the forms `ℓ_j(m, p) = φ_j(m) + Σ_i e_{ji} log p_i`.
If `2π(Σ_j |e_{ji}|)T₀ ≤ q^η` for each `i`, the sum over `χ ≠ 1` of the family's twisted sums is at most
`q^{L−1/50000}(Σ|a_m|²/P)^{1/2} ∏_j ‖𝓕g_j‖₁`, plus the number of characters `χ ≠ 1` times
`Σ_m |a_m| ∏_i Σ_p |f0(p/Q_i)|` times `Σ_j (∫_{|t|>T₀} |𝓕g_j(t)| dt) ∏_{i≠j} ‖𝓕g_i‖₁`. -/
theorem family_bound {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (a : ℕ → ℂ) (K : ℕ), K ≤ K₀ → ∀ Q : ℕ → ℝ, (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) / P →
      ∀ {J : ℕ} (g : Fin J → ℝ → ℂ), (∀ j, Continuous (g j)) → (∀ j, Integrable (g j)) →
      (∀ j, Integrable (𝓕 (g j))) → ∀ (φ : Fin J → ℕ → ℝ) (e : Fin J → Fin K → ℝ) (T₀ : ℝ),
      (∀ i : Fin K, 2 * π * (∑ j, |e j i|) * T₀ ≤ (q : ℝ) ^ η) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ m ∈ S, ∑ p ∈ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
            a m * χ m * (∏ i : Fin K, χ (p i) * (f0 (p i / Q i) : ℂ)) *
              ∏ j, g j (φ j m + ∑ i : Fin K, e j i * Real.log (p i))‖ ≤
        (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) *
            (∏ j, ∫ t, ‖𝓕 (g j) t‖) +
          (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card *
            ((∑ m ∈ S, ‖a m‖) * ∏ i : Fin K, ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|) *
            ∑ j, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (g j) t‖) t) *
              ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (g i) t‖ := by
  obtain ⟨q₀, hq₀⟩ := SieveTypeII.typeII_step hf0 hsupp K₀ he₁ hη hη1
  refine ⟨q₀, fun q _ hq P S hS hP1 hP2 a K hK Q hQ hQP J g hgc hgi hgf φ e T₀ hT => ?_⟩
  -- the separated sum
  set W : DirichletCharacter ℂ q → (Fin J → ℝ) → ℂ := fun χ ξ =>
    ∑ m ∈ S, a m * χ m * Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m) with hWdef
  set B : DirichletCharacter ℂ q → (Fin J → ℝ) → Fin K → ℂ := fun χ ξ i =>
    ∑ p ∈ primesTo (Q i), χ p * (f0 (p / Q i) : ℂ) * Complex.exp (2 * π * I * (∑ j, ξ j * e j i) * Real.log p)
    with hBdef
  set F : DirichletCharacter ℂ q → (Fin J → ℝ) → ℂ := fun χ ξ => W χ ξ * ∏ i, B χ ξ i with hFdef
  have hsep : ∀ χ : DirichletCharacter ℂ q,
      ∑ m ∈ S, ∑ p ∈ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        a m * χ m * (∏ i : Fin K, χ (p i) * (f0 (p i / Q i) : ℂ)) *
          ∏ j, g j (φ j m + ∑ i : Fin K, e j i * Real.log (p i)) =
      ∫ ξ : Fin J → ℝ, (∏ j, 𝓕 (g j) (ξ j)) * F χ ξ := by
    intro χ
    rw [← Finset.sum_product']
    rw [SieveSep.sum_sep (S ×ˢ Fintype.piFinset (fun i : Fin K => primesTo (Q i)))
      (fun x => a x.1 * χ x.1 * ∏ i : Fin K, (χ (x.2 i) * (f0 (x.2 i / Q i) : ℂ)))
      (fun j x => φ j x.1 + ∑ i : Fin K, e j i * Real.log (x.2 i)) hgc hgi hgf]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [inner_factor χ f0 S a Q φ e ξ]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hQpos : ∀ i : Fin K, 0 < Q i := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hq0 _) (hQ i i.isLt)
  -- continuity in `ξ`
  have hcont : ∀ χ : DirichletCharacter ℂ q, Continuous (F χ) := by
    intro χ
    have hW : Continuous (W χ) := continuous_finsetSum _ fun m _ => continuous_const.mul
      (Continuous.cexp (continuous_const.mul (continuous_finsetSum _ fun j _ =>
        (Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const)))
    have hB : ∀ i, Continuous fun ξ => B χ ξ i := fun i => continuous_finsetSum _ fun p _ =>
      continuous_const.mul (Continuous.cexp ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const))).mul continuous_const))
    exact hW.mul (continuous_finsetProd _ fun i _ => hB i)
  -- the norms of the factors
  have hWnorm : ∀ χ : DirichletCharacter ℂ q, ∀ ξ, ‖W χ ξ‖ ≤ ∑ m ∈ S, ‖a m‖ := by
    intro χ ξ
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := DirichletCharacter.norm_le_one χ (m : ZMod q)
    have h2 : ‖Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m)‖ = 1 := by
      have : 2 * π * I * ∑ j, (ξ j : ℂ) * φ j m = ((2 * π * ∑ j, ξ j * φ j m : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [h2, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  have hBnorm : ∀ χ : DirichletCharacter ℂ q, ∀ ξ i, ‖B χ ξ i‖ ≤ ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| := by
    intro χ ξ i
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := DirichletCharacter.norm_le_one χ (p : ZMod q)
    have h2 : ‖Complex.exp (2 * π * I * (∑ j, ξ j * e j i) * Real.log p)‖ = 1 := by
      have : 2 * π * I * (∑ j, ξ j * e j i : ℝ) * Real.log p =
          ((2 * π * (∑ j, ξ j * e j i) * Real.log p : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [h2, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  -- the trivial bound
  set B₂ : ℝ := (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card *
    ((∑ m ∈ S, ‖a m‖) * ∏ i : Fin K, ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|) with hB₂def
  have hB₂0 : 0 ≤ B₂ := by positivity
  have hB₂ : ∀ ξ, ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ ξ‖ ≤ B₂ := by
    intro ξ
    rw [hB₂def, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun χ _ => ?_
    rw [hFdef]
    simp only
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hWnorm χ ξ) (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hBnorm χ ξ i)
      (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.sum_nonneg fun m _ => norm_nonneg _)
  -- the box: M3
  set B₁ : ℝ := (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) with hB₁def
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₁ : ∀ ξ : Fin J → ℝ, (∀ j, |ξ j| ≤ T₀) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ ξ‖ ≤ B₁ := by
    intro ξ hξ
    set a' : ℕ → ℂ := fun m => a m * Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m) with ha'
    set hh : ℕ → ℝ := fun j => if hj : j < K then -(2 * π * ∑ j', ξ j' * e j' ⟨j, hj⟩) else 0 with hhh
    have hheq : ∀ i : Fin K, hh i = -(2 * π * ∑ j', ξ j' * e j' i) := fun i => by
      simp [hhh, i.isLt]
    have hexp1 : ∀ r : ℝ, ‖Complex.exp (2 * π * I * (r : ℂ))‖ = 1 := fun r => by
      have : 2 * π * I * (r : ℂ) = ((2 * π * r : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hFeq : ∀ χ : DirichletCharacter ℂ q, ‖F χ ξ‖ = ‖DirMean.dp S (fun m => a' m * χ m) 0‖ *
        ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (hh j)‖ := by
      intro χ
      rw [hFdef]
      simp only
      rw [norm_mul]
      congr 1
      · congr 1
        rw [hWdef, DirMean.dp]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [ha', zero_mul, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
        ring
      · rw [norm_prod, norm_prod,
          ← Fin.prod_univ_eq_prod_range (fun j => ‖SieveWeight.Sp χ f0 (Q j) (hh j)‖)]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hBdef]
        simp only
        have h1 := sum_twist_eq χ f0 (hQpos i) (∑ j, ξ j * e j i)
        rw [h1, norm_mul, hheq i]
        have h2 : ‖Complex.exp (2 * π * I * ((∑ j, ξ j * e j i : ℝ) : ℂ) * (Real.log (Q i) : ℂ))‖ = 1 := by
          have : 2 * π * I * ((∑ j, ξ j * e j i : ℝ) : ℂ) * (Real.log (Q i) : ℂ) =
              2 * π * I * (((∑ j, ξ j * e j i) * Real.log (Q i) : ℝ) : ℂ) := by push_cast; ring
          rw [this, hexp1]
        rw [h2, one_mul]
    have hheight : ∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |hh j| ≤ (q : ℝ) ^ η := by
      intro j hj
      refine ⟨hQ j hj, ?_⟩
      have h2π : (0 : ℝ) < 2 * π := by positivity
      have hsum : |∑ j', ξ j' * e j' ⟨j, hj⟩| ≤ (∑ j', |e j' ⟨j, hj⟩|) * T₀ := by
        rw [Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hξ j') (abs_nonneg _)
      calc |hh j| = 2 * π * |∑ j', ξ j' * e j' ⟨j, hj⟩| := by
            rw [show hh j = -(2 * π * ∑ j', ξ j' * e j' ⟨j, hj⟩) by simp [hhh, hj], abs_neg, abs_mul,
              abs_of_pos h2π]
        _ ≤ 2 * π * ((∑ j', |e j' ⟨j, hj⟩|) * T₀) := mul_le_mul_of_nonneg_left hsum h2π.le
        _ = 2 * π * (∑ j', |e j' ⟨j, hj⟩|) * T₀ := by ring
        _ ≤ (q : ℝ) ^ η := hT ⟨j, hj⟩
    have ha'n : ∑ m ∈ S, ‖a' m‖ ^ 2 = ∑ m ∈ S, ‖a m‖ ^ 2 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ha']
      simp only
      rw [norm_mul]
      have : 2 * π * I * ∑ j, (ξ j : ℂ) * φ j m = 2 * π * I * ((∑ j, ξ j * φ j m : ℝ) : ℂ) := by push_cast; ring
      rw [this, hexp1, mul_one]
    have h := hq₀ q hq P S hS hP1 hP2 a' (0 : ℝ) K hK Q hh hheight hQP
    rw [ha'n] at h
    calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ ξ‖
        = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖DirMean.dp S (fun m => a' m * χ m) 0‖ *
              ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (hh j)‖ :=
          Finset.sum_congr rfl fun χ _ => hFeq χ
      _ ≤ B₁ := h
  have hfin := SieveSep.sep_bound (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)) F hcont hgf
    hB₁0 hB₂0 hB₁ hB₂
  calc _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∫ ξ : Fin J → ℝ, (∏ j, 𝓕 (g j) (ξ j)) * F χ ξ‖ :=
        Finset.sum_congr rfl fun χ _ => by rw [hsep χ]
    _ ≤ _ := hfin

/-! ### The cut-off's Fourier transform: mass and tails -/

section Cutoff

open SieveSmooth

variable {θ Λ : ℝ}

/-- `‖G‖₁ ≤ 2Λ + θ` for `0 < θ ≤ 2Λ`. -/
theorem integral_norm_GC_le (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ) : ∫ u, ‖GC θ Λ u‖ ≤ 2 * Λ + θ := by
  have hΛ : 0 ≤ Λ := by linarith
  have hpt : ∀ u, ‖GC θ Λ u‖ ≤ Set.indicator (Set.Icc 0 (2 * Λ + θ)) (fun _ => (1 : ℝ)) u := by
    intro u
    rw [GC_eq_G, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (G_nonneg hθ hθΛ u)]
    by_cases hu : u ∈ Set.Icc 0 (2 * Λ + θ)
    · rw [Set.indicator_of_mem hu]; exact G_le_one u
    · rw [Set.indicator_of_notMem hu, G_eq_zero hθ hΛ hu]
  have hi : Integrable (Set.indicator (Set.Icc 0 (2 * Λ + θ)) (fun _ => (1 : ℝ))) :=
    (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc
  calc ∫ u, ‖GC θ Λ u‖ ≤ ∫ u, Set.indicator (Set.Icc 0 (2 * Λ + θ)) (fun _ => (1 : ℝ)) u :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi
          (Filter.Eventually.of_forall hpt)
    _ = 2 * Λ + θ := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, mul_one, Measure.real,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring

/-- The mass of `𝓕G`: `‖𝓕G‖₁ ≤ π(2Λ + θ) + c₂/(2πθ)` for `0 < θ ≤ 2Λ`, with `c₂ = ‖g″‖₁`. -/
theorem mass_GC_le (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ) :
    ∫ ξ, ‖𝓕 (GC θ Λ) ξ‖ ≤ π * (2 * Λ + θ) + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * θ) := by
  have hΛ : 0 ≤ Λ := by linarith
  set c₂ := ∫ v, ‖iteratedDeriv 2 gc v‖ with hc₂
  have hc₂0 : 0 ≤ c₂ := integral_nonneg fun _ => norm_nonneg _
  set N := (2 * Λ + θ) + c₂ / (2 * π ^ 2 * θ) with hN
  have hpt : ∀ ξ, ‖𝓕 (GC θ Λ) ξ‖ ≤ N * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have h0 := (norm_fourier_GC_le (θ := θ) (Λ := Λ) ξ).trans (integral_norm_GC_le hθ hθΛ)
    have h2 := pow_mul_norm_fourier_GC_le hθ hΛ (K := 2) (by norm_num) ξ
    rw [← hc₂] at h2
    have hsq : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * ξ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
    rw [hsq] at h2
    have hpi : 0 < 4 * π ^ 2 := by positivity
    have hF := norm_nonneg (𝓕 (GC θ Λ) ξ)
    have h2' : ξ ^ 2 * ‖𝓕 (GC θ Λ) ξ‖ ≤ c₂ / (2 * π ^ 2 * θ) := by
      have e : 2 * (θ⁻¹ ^ 2 * θ) * c₂ = 4 * π ^ 2 * (c₂ / (2 * π ^ 2 * θ)) := by
        field_simp
        ring
      rw [e] at h2
      nlinarith
    have hpos : 0 < 1 + ξ ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    nlinarith
  have hint : Integrable fun ξ : ℝ => N * (1 + ξ ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul N
  calc ∫ ξ, ‖𝓕 (GC θ Λ) ξ‖ ≤ ∫ ξ : ℝ, N * (1 + ξ ^ 2)⁻¹ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ = π * (2 * Λ + θ) + c₂ / (2 * π * θ) := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, hN]
        field_simp

/-- The tail of `𝓕G` beyond `T₀ ≥ 1`: at most `2π·2θ^{1−k}c_k(2π)^{−k}T₀^{2−k}` for `θ > 0`, `Λ ≥ 0` and `k ≥ 2`,
with `c_k = ‖g^{(k)}‖₁`. -/
theorem tail_GC_le (hθ : 0 < θ) (hΛ : 0 ≤ Λ) {k : ℕ} (hk : 2 ≤ k) {T₀ : ℝ} (hT₀ : 1 ≤ T₀) :
    ∫ ξ, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) ξ ≤
      2 * π * ((2 * (θ⁻¹ ^ k * θ) * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹ := by
  set N := 2 * (θ⁻¹ ^ k * θ) * ∫ v, ‖iteratedDeriv k gc v‖ with hN
  have hN0 : 0 ≤ N := by
    rw [hN]
    have := integral_nonneg (μ := volume) (f := fun v : ℝ => ‖iteratedDeriv k gc v‖) (fun v => norm_nonneg _)
    positivity
  set C := 2 * (N / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹ with hC
  have hpt : ∀ ξ, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) ξ ≤ C * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    by_cases hξ : ξ ∈ {t : ℝ | T₀ < |t|}
    · rw [Set.indicator_of_mem hξ]
      have hξ1 : T₀ < |ξ| := hξ
      have hξ0 : 0 < |ξ| := by linarith
      have h := pow_mul_norm_fourier_GC_le hθ hΛ (K := k) (by omega) ξ
      rw [← hN] at h
      have hpk : 0 < (2 * π * |ξ|) ^ k := by positivity
      have hF : ‖𝓕 (GC θ Λ) ξ‖ ≤ N / (2 * π * |ξ|) ^ k := by rw [le_div_iff₀ hpk]; linarith
      -- `|ξ|^k ≥ T₀^{k−2}ξ²` and `ξ² ≥ (1 + ξ²)/2`
      have hk2 : |ξ| ^ k = |ξ| ^ (k - 2) * ξ ^ 2 := by
        rw [← sq_abs ξ, ← pow_add]; congr 1; omega
      have hT : T₀ ^ (k - 2) ≤ |ξ| ^ (k - 2) := pow_le_pow_left₀ (by linarith) hξ1.le _
      have hTpos : 0 < T₀ ^ (k - 2) := by positivity
      have hsq : (1 + ξ ^ 2) / 2 ≤ ξ ^ 2 := by
        have : 1 ≤ ξ ^ 2 := by rw [← sq_abs]; nlinarith
        linarith
      have hden : T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) * (2 * π) ^ k ≤ (2 * π * |ξ|) ^ k := by
        rw [mul_pow (2 * π) |ξ| k, hk2]
        have h2pk : 0 < (2 * π) ^ k := by positivity
        have : T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) ≤ |ξ| ^ (k - 2) * ξ ^ 2 :=
          mul_le_mul hT hsq (by positivity) (by positivity)
        nlinarith
      have hdpos : 0 < T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) * (2 * π) ^ k := by positivity
      calc ‖𝓕 (GC θ Λ) ξ‖ ≤ N / (2 * π * |ξ|) ^ k := hF
        _ ≤ N / (T₀ ^ (k - 2) * ((1 + ξ ^ 2) / 2) * (2 * π) ^ k) :=
          div_le_div_of_nonneg_left hN0 hdpos hden
        _ = C * (1 + ξ ^ 2)⁻¹ := by rw [hC]; field_simp
    · rw [Set.indicator_of_notMem hξ]; positivity
  have hint : Integrable fun ξ : ℝ => C * (1 + ξ ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul C
  calc ∫ ξ, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) ξ
      ≤ ∫ ξ : ℝ, C * (1 + ξ ^ 2)⁻¹ := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _) hint
          (Filter.Eventually.of_forall hpt)
    _ = 2 * π * (N / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹ := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, hC]; ring

end Cutoff

/-! ### Orthogonality -/

section Orth

open Classical

/-- The weight of `A − B/φ(q)` at `n`: `1[n ≡ a] − 1[(n, q) = 1]/φ(q)`. -/
noncomputable def dw (q : ℕ) (a : ZMod q) (n : ℕ) : ℂ :=
  (if (n : ZMod q) = a then 1 else 0) - (if IsUnit (n : ZMod q) then 1 else 0) / q.totient

/-- **Orthogonality**: `1[n ≡ a] − 1[(n, q) = 1]/φ(q) = φ(q)⁻¹ Σ_{χ≠1} χ(a⁻¹)χ(n)` for `a` a unit. -/
theorem dw_eq {a : ZMod q} (ha : IsUnit a) (n : ℕ) :
    dw q a n = (q.totient : ℂ)⁻¹ *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), χ a⁻¹ * χ n := by
  have htot : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
  have hsplit : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n =
      (1 : DirichletCharacter ℂ q) a⁻¹ * (1 : DirichletCharacter ℂ q) n +
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), χ a⁻¹ * χ n := by
    rw [Finset.filter_ne']
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have hone : (1 : DirichletCharacter ℂ q) a⁻¹ * (1 : DirichletCharacter ℂ q) n =
      if IsUnit (n : ZMod q) then 1 else 0 := by
    rw [MulChar.one_apply (IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit a ha)), one_mul]
    by_cases hu : IsUnit (n : ZMod q)
    · simp [MulChar.one_apply hu, hu]
    · simp [MulChar.map_nonunit _ hu, hu]
  rw [hsplit, hone] at horth
  rw [dw]
  field_simp
  have hcase : (if a = (n : ZMod q) then (q.totient : ℂ) else 0) =
      q.totient * (if (n : ZMod q) = a then 1 else 0) := by
    by_cases h : (n : ZMod q) = a
    · simp [h]
    · have h' : ¬ a = (n : ZMod q) := fun h' => h h'.symm
      simp [h, h']
  rw [hcase] at horth
  rcases Classical.em (IsUnit (n : ZMod q)) with hu | hu
  · simp only [hu, ↓reduceIte] at horth ⊢
    linear_combination -horth
  · simp only [hu, ↓reduceIte] at horth ⊢
    linear_combination -horth

/-- The difference `D(w) = Σ_x w(x)(1[n(x) ≡ a] − 1[(n(x), q) = 1]/φ(q))` of a weighted finite family. -/
noncomputable def Dsum {X : Type*} (q : ℕ) (a : ZMod q) (T : Finset X) (n : X → ℕ) (w : X → ℂ) : ℂ :=
  ∑ x ∈ T, w x * dw q a (n x)

/-- For `a` a unit, `|D(w)| ≤ φ(q)⁻¹ Σ_{χ≠1} |Σ_x w(x)χ(n(x))|`. -/
theorem norm_Dsum_le {X : Type*} {a : ZMod q} (ha : IsUnit a) (T : Finset X) (n : X → ℕ) (w : X → ℂ) :
    ‖Dsum q a T n w‖ ≤ (q.totient : ℝ)⁻¹ *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ x ∈ T, w x * χ (n x)‖ := by
  have heq : Dsum q a T n w = (q.totient : ℂ)⁻¹ *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), χ a⁻¹ * ∑ x ∈ T, w x * χ (n x) := by
    rw [Dsum]
    simp_rw [dw_eq ha, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)) (by positivity)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

end Orth

/-- For `a_j, b_j ∈ [0, 1]`: `|∏ a_j − ∏ b_j| ≤ Σ |a_j − b_j|`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ 1) : |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have ha' : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hih := ih ha' hb'
    have haj := ha j (Finset.mem_insert_self j s)
    have hbs : 0 ≤ ∏ i ∈ s, b i ∧ ∏ i ∈ s, b i ≤ 1 :=
      ⟨Finset.prod_nonneg fun i hi => (hb' i hi).1, Finset.prod_le_one₀ (fun i hi => (hb' i hi).1)
        fun i hi => (hb' i hi).2⟩
    have heq : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [heq]
    calc |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i|
        ≤ |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| + |(a j - b j) * ∏ i ∈ s, b i| := abs_add_le _ _
      _ = |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * ∑ i ∈ s, |a i - b i| + |a j - b j| * 1 := by
          gcongr
          · rw [abs_of_nonneg haj.1]; exact haj.2
          · rw [abs_of_nonneg hbs.1]; exact hbs.2
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

section Sharp

open Classical

/-- **Sharp against smooth** (the shape of SIEVE-ROUTE.md §10's Lemma 4″). Let the comparisons `I_j ∈ [0, 1]` be
replaced by `G_j ∈ [0, 1]`, with `|I_j − G_j| ≤ M_j`. Then
`|D(wΠI)| ≤ |D(wΠG)| + Σ_j (2φ(q)⁻¹ Σ_x |w(x)|M_j(x) + |D(|w|M_j)|)`. -/
theorem norm_Dsum_sharp_le {X : Type*} {a : ZMod q} (T : Finset X) (n : X → ℕ) (w : X → ℂ) {J : ℕ}
    (I G M : Fin J → X → ℝ) (hI : ∀ j x, 0 ≤ I j x ∧ I j x ≤ 1) (hG : ∀ j x, 0 ≤ G j x ∧ G j x ≤ 1)
    (hM : ∀ j x, |I j x - G j x| ≤ M j x) :
    ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ))‖ ≤ ‖Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ +
      ∑ j, (2 * (q.totient : ℝ)⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x +
        ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖) := by
  set φq : ℝ := (q.totient : ℝ) with hφq
  have hφ0 : 0 < φq := by rw [hφq]; exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  -- the indicator weights
  set A : ℕ → ℝ := fun m => if (m : ZMod q) = a then 1 else 0 with hA
  set U : ℕ → ℝ := fun m => if IsUnit (m : ZMod q) then 1 else 0 with hU
  have hdw : ∀ m, dw q a m = ((A m - U m / φq : ℝ) : ℂ) := fun m => by
    rw [dw, hA, hU]; push_cast; split_ifs <;> simp [hφq]
  have hA0 : ∀ m, 0 ≤ A m := fun m => by simp only [hA]; split_ifs <;> norm_num
  have hU0 : ∀ m, 0 ≤ U m ∧ U m ≤ 1 := fun m => by simp only [hU]; split_ifs <;> norm_num
  have hdwn : ∀ m, ‖dw q a m‖ ≤ A m + U m / φq := fun m => by
    rw [hdw, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (hA0 m), abs_of_nonneg (div_nonneg (hU0 m).1 hφ0.le)]
  -- the difference of the two sums
  have hdiff : ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ)) - Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ ≤
      ∑ j, ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) := by
    rw [Dsum, Dsum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x ∈ T, ‖w x * (∏ j, (I j x : ℂ)) * dw q a (n x) - w x * (∏ j, (G j x : ℂ)) * dw q a (n x)‖
        ≤ ∑ x ∈ T, ‖w x‖ * (∑ j, M j x) * (A (n x) + U (n x) / φq) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have hprod : ‖(∏ j, (I j x : ℂ)) - ∏ j, (G j x : ℂ)‖ ≤ ∑ j, M j x := by
            rw [← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
            exact (abs_prod_sub_prod_le _ _ _ (fun j _ => hI j x) fun j _ => hG j x).trans
              (Finset.sum_le_sum fun j _ => hM j x)
          have e : w x * (∏ j, (I j x : ℂ)) * dw q a (n x) - w x * (∏ j, (G j x : ℂ)) * dw q a (n x) =
              w x * ((∏ j, (I j x : ℂ)) - ∏ j, (G j x : ℂ)) * dw q a (n x) := by ring
          rw [e, norm_mul, norm_mul]
          have hd := hdwn (n x)
          have hw := norm_nonneg (w x)
          have hMs : 0 ≤ ∑ j, M j x := Finset.sum_nonneg fun j _ => le_trans (abs_nonneg _) (hM j x)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hprod hw) hd (norm_nonneg _) (mul_nonneg hw hMs)
      _ = ∑ j, ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
  -- the `A`-part of each near-boundary sum
  have hpart : ∀ j, ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) ≤
      2 * φq⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x + ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖ := by
    intro j
    have hD : (Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))) =
        ((∑ x ∈ T, ‖w x‖ * M j x * (A (n x) - U (n x) / φq) : ℝ) : ℂ) := by
      rw [Dsum]; push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hdw]; push_cast; ring
    have hre : ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) - U (n x) / φq) ≤
        ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖ := by
      rw [hD, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    have hM0 : ∀ x, 0 ≤ M j x := fun x => le_trans (abs_nonneg _) (hM j x)
    have hU1 : ∑ x ∈ T, ‖w x‖ * M j x * (U (n x) / φq) ≤ φq⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 : U (n x) / φq ≤ φq⁻¹ := by
        rw [div_eq_mul_inv]; exact mul_le_of_le_one_left (inv_nonneg.2 hφ0.le) (hU0 (n x)).2
      have h0 : 0 ≤ ‖w x‖ * M j x := mul_nonneg (norm_nonneg _) (hM0 x)
      nlinarith
    have hsplit : ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) + U (n x) / φq) =
        ∑ x ∈ T, ‖w x‖ * M j x * (A (n x) - U (n x) / φq) + 2 * ∑ x ∈ T, ‖w x‖ * M j x * (U (n x) / φq) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hsplit]
    nlinarith
  calc ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ))‖
      ≤ ‖Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ +
        ‖Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ)) - Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ := by
        have := norm_sub_norm_le (Dsum q a T n (fun x => w x * ∏ j, (I j x : ℂ)))
          (Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ)))
        linarith
    _ ≤ ‖Dsum q a T n (fun x => w x * ∏ j, (G j x : ℂ))‖ +
        ∑ j, (2 * φq⁻¹ * ∑ x ∈ T, ‖w x‖ * M j x + ‖Dsum q a T n (fun x => ((‖w x‖ * M j x : ℝ) : ℂ))‖) := by
        gcongr
        exact hdiff.trans (Finset.sum_le_sum fun j _ => hpart j)

end Sharp

/-! ### The pivot -/

/-- Splitting a sum over a box at the coordinate `p`. -/
theorem sum_piFinset_pivot {n : ℕ} {α : Type*} (t : Fin (n + 1) → Finset α) (p : Fin (n + 1))
    (F : (Fin (n + 1) → α) → ℝ) :
    ∑ x ∈ Fintype.piFinset t, F x =
      ∑ y ∈ t p, ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)), F (p.insertNth y z) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (x p, p.removeNth x)) (fun yz => p.insertNth yz.1 yz.2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Fin.mem_piFinset_iff_pivot_removeNth p] at hx
    exact Finset.mem_product.2 ⟨hx.1, hx.2⟩
  · intro yz hyz
    rw [Finset.mem_product] at hyz
    rw [Fin.mem_piFinset_iff_pivot_removeNth p]
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
    exact hyz
  · intro x _
    simp
  · intro yz _
    simp
  · intro x _
    simp

/-- **The pivot count.** Let `u_i ≥ 0`. If for every choice `z` of the other coordinates, the pivot's sum
`Σ_{y ∈ t p} u_p(y)v(insertNth p y z)` is at most `C`, then the box sum of `∏_i u_i(x_i)·v(x)` is at most `C` times
the product of the other coordinates' sums. -/
theorem pivot_sum_le {n : ℕ} {α : Type*} (t : Fin (n + 1) → Finset α) (p : Fin (n + 1)) (u : Fin (n + 1) → α → ℝ)
    (hu : ∀ i y, 0 ≤ u i y) (v : (Fin (n + 1) → α) → ℝ) {C : ℝ}
    (hC : ∀ z : Fin n → α, ∑ y ∈ t p, u p y * v (p.insertNth y z) ≤ C) :
    ∑ x ∈ Fintype.piFinset t, (∏ i, u i (x i)) * v x ≤
      C * ∏ i : Fin n, ∑ y ∈ t (p.succAbove i), u (p.succAbove i) y := by
  rw [sum_piFinset_pivot t p, Finset.sum_comm]
  have hfac : ∀ y (z : Fin n → α), (∏ i, u i ((p.insertNth y z : Fin (n + 1) → α) i)) =
      u p y * ∏ i : Fin n, u (p.succAbove i) (z i) := by
    intro y z
    rw [Fin.prod_univ_succAbove _ p]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  calc ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)), ∑ y ∈ t p,
        (∏ i, u i ((p.insertNth y z : Fin (n + 1) → α) i)) * v (p.insertNth y z)
      = ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)),
          (∏ i : Fin n, u (p.succAbove i) (z i)) * ∑ y ∈ t p, u p y * v (p.insertNth y z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hfac]; ring
    _ ≤ ∑ z ∈ Fintype.piFinset (fun i => t (p.succAbove i)), (∏ i : Fin n, u (p.succAbove i) (z i)) * C :=
        Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hC z) (Finset.prod_nonneg fun i _ => hu _ _)
    _ = C * ∏ i : Fin n, ∑ y ∈ t (p.succAbove i), u (p.succAbove i) y := by
        rw [← Finset.sum_mul, mul_comm, Finset.prod_univ_sum]

/-- At most `(ρ − 1)R + 1` integers `y ≤ R` lie in `[Y, ρY]`, for `Y > 0`, `ρ ≥ 1` and `R ≥ 0`. -/
theorem card_short_le {Y ρ R : ℝ} (hY : 0 < Y) (hρ : 1 ≤ ρ) (hR : 0 ≤ R) (s : Finset ℕ)
    (hs : ∀ y ∈ s, Y ≤ y ∧ (y : ℝ) ≤ ρ * Y ∧ (y : ℝ) ≤ R) : (s.card : ℝ) ≤ (ρ - 1) * R + 1 := by
  set b : ℝ := min (ρ * Y) R with hb
  have hsub : s ⊆ Finset.Icc ⌈Y⌉₊ ⌊b⌋₊ := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hs y hy
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.2 h1, Nat.le_floor (le_min h2 h3)⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hcard' : (s.card : ℝ) ≤ ((⌊b⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  have hb0 : 0 ≤ b := le_min (by positivity) hR
  by_cases hle : ⌈Y⌉₊ ≤ ⌊b⌋₊ + 1
  · rw [Nat.cast_sub hle] at hcard'
    push_cast at hcard'
    have hfl : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb0
    have hce : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
    -- `b − Y ≤ (ρ − 1)R`, or else nothing is counted
    by_cases hYR : Y ≤ R
    · have : b - Y ≤ (ρ - 1) * R := by
        have h1 : b ≤ ρ * Y := min_le_left _ _
        nlinarith
      linarith
    · push Not at hYR
      have : b ≤ R := min_le_right _ _
      have hneg : (s.card : ℝ) < 1 := by linarith
      have h0 : s.card = 0 := by
        have : s.card < 1 := by exact_mod_cast hneg
        omega
      rw [h0, Nat.cast_zero]
      nlinarith
  · push Not at hle
    rw [Nat.sub_eq_zero_of_le hle.le, Nat.cast_zero] at hcard'
    nlinarith

open SieveSmooth in
/-- Let `θ > 0`, `Λ ≥ 0` and `u ≤ Λ`, and let `P` hold when `u > 0` and imply `u ≥ 0`. Then the narrow cut-off
`G̃(u) = G_{θ,θ}(u + θ)` majorizes `|1[P] − G_{θ,Λ}(u)|`. -/
theorem abs_ind_sub_G_le {θ Λ u : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ) (hu : u ≤ Λ) (P : Prop) [Decidable P]
    (hP : (0 < u → P) ∧ (P → 0 ≤ u)) :
    |(if P then (1 : ℝ) else 0) - G θ Λ u| ≤ G θ θ (u + θ) := by
  obtain ⟨h0, h1, h2⟩ := indicator_sub_G hθ hΛ hu P hP
  rw [abs_of_nonneg h0]
  by_cases hin : 0 ≤ u ∧ u < θ
  · have hG : G θ θ (u + θ) = 1 := by
      rw [G, Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hθ]; linarith),
        Real.smoothTransition.zero_of_nonpos (by
          apply div_nonpos_of_nonpos_of_nonneg _ hθ.le; linarith)]
      norm_num
    rw [hG]; exact h1
  · have hout : u < 0 ∨ θ ≤ u := by
      by_contra hc; push Not at hc; exact hin ⟨hc.1, hc.2⟩
    rw [h2 hout]
    exact G_nonneg hθ (by linarith) _

open SieveSmooth in
/-- **The pivot's sum.** If the form is `c + σ log y` in the pivot `y`, with `σ = ±1`, then for `θ > 0`, `Q > 0`
and `0 ≤ f0 ≤ F₀` the primes `y` of `Sp`'s range at scale `Q` give
`Σ_y f0(y/Q) G̃(c + σ log y) ≤ F₀((e^{3θ} − 1)2Q + 1)`. -/
theorem pivot_term_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {θ Q c σ : ℝ}
    (hθ : 0 < θ) (hQ : 0 < Q) (hσ : σ = 1 ∨ σ = -1) :
    ∑ y ∈ primesTo Q, f0 (y / Q) * G θ θ (c + σ * Real.log y + θ) ≤
      F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q) + 1) := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  -- the pivots that count lie in `[Y, e^{3θ}Y]`
  obtain ⟨Y, hY, hYb⟩ : ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, 0 < y → -θ ≤ c + σ * Real.log y →
      c + σ * Real.log y ≤ 2 * θ → Y ≤ y ∧ y ≤ Real.exp (3 * θ) * Y := by
    rcases hσ with rfl | rfl
    · refine ⟨Real.exp (-θ - c), Real.exp_pos _, fun y hy h1 h2 => ⟨?_, ?_⟩⟩
      · rw [← Real.exp_log hy]; exact Real.exp_le_exp.2 (by linarith)
      · rw [← Real.exp_log hy, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    · refine ⟨Real.exp (c - 2 * θ), Real.exp_pos _, fun y hy h1 h2 => ⟨?_, ?_⟩⟩
      · rw [← Real.exp_log hy]; exact Real.exp_le_exp.2 (by linarith)
      · rw [← Real.exp_log hy, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  set s := (primesTo Q).filter (fun y : ℕ => -θ ≤ c + σ * Real.log y ∧ c + σ * Real.log y ≤ 2 * θ) with hs
  have hterm : ∀ y ∈ primesTo Q, f0 (y / Q) * G θ θ (c + σ * Real.log y + θ) ≤
      if y ∈ s then F₀ else 0 := by
    intro y hy
    have hG1 := G_le_one (θ := θ) (Λ := θ) (c + σ * Real.log y + θ)
    have hG0 := G_nonneg hθ (by linarith : θ ≤ 2 * θ) (c + σ * Real.log y + θ)
    split_ifs with hys
    · calc f0 (y / Q) * G θ θ (c + σ * Real.log y + θ) ≤ F₀ * 1 :=
            mul_le_mul (hF₀ _) hG1 hG0 hF0
        _ = F₀ := mul_one _
    · rw [hs, Finset.mem_filter] at hys
      push Not at hys
      have hout : c + σ * Real.log y + θ ∉ Set.Icc 0 (2 * θ + θ) := by
        rintro ⟨h1, h2⟩
        exact absurd (by linarith : c + σ * Real.log y ≤ 2 * θ) (not_le.2 (hys hy (by linarith)))
      rw [G_eq_zero hθ hθ.le hout, mul_zero]
  calc ∑ y ∈ primesTo Q, f0 (y / Q) * G θ θ (c + σ * Real.log y + θ)
      ≤ ∑ y ∈ primesTo Q, (if y ∈ s then F₀ else 0) := Finset.sum_le_sum hterm
    _ = F₀ * s.card := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hfs : (primesTo Q).filter (fun y => y ∈ s) = s := by
          rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        rw [hfs]
    _ ≤ F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hF0
        refine card_short_le hY (by
          have := Real.add_one_le_exp (3 * θ); linarith) (by positivity) s fun y hy => ?_
        rw [hs, Finset.mem_filter] at hy
        obtain ⟨hyp, h1, h2⟩ := hy
        rw [primesTo, Finset.mem_filter, Finset.mem_range] at hyp
        have hy0 : (0 : ℝ) < y := by exact_mod_cast hyp.2.pos
        obtain ⟨hl, hr⟩ := hYb y hy0 h1 h2
        refine ⟨hl, hr, ?_⟩
        have hyle : y ≤ ⌊2 * Q⌋₊ := Nat.lt_succ_iff.1 hyp.1
        exact le_trans (by exact_mod_cast hyle) (Nat.floor_le (by positivity))

section SharpFamily

open SieveSmooth Classical

/-- **A sharp family, explicitly.** Let `a` be a unit, `Q_i > 0`, `0 ≤ f0 ≤ F₀` and `0 < θ ≤ 2Λ`. The tuples
`(m, x)` with `m ∈ S` and `n + 1` primes `x_i` of `Sp`'s ranges, with weight `w = a_m ∏_i f0(x_i/Q_i)`, are cut by `J`
sharp comparisons `P_j`, where `P_j` holds when `ℓ_j(m, x) = φ_j(m) + Σ_i e_{ji} log x_i > 0` and implies `ℓ_j ≥ 0`. If
each `ℓ_j ≤ Λ` on the tuples and each comparison has a pivot prime with coefficient `±1`, then `|A − B/φ(q)|` of the
family is at most `φ(q)⁻¹` times the twisted sums of the smoothed family and of the `J` near-boundary families, plus
twice `φ(q)⁻¹` times the pivots' counts. -/
theorem Dsum_sharp_le {a : ZMod q} (ha : IsUnit a) (S : Finset ℕ) (acoef : ℕ → ℂ) {n : ℕ} (Q : ℕ → ℝ)
    (hQ : ∀ i : Fin (n + 1), 0 < Q i) {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {J : ℕ}
    (φ : Fin J → ℕ → ℝ) (e : Fin J → Fin (n + 1) → ℝ) (Pr : Fin J → ℕ → (Fin (n + 1) → ℕ) → Prop)
    {θ Λ : ℝ} (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ)
    (hP : ∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
      (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i)))
    (hΛ : ∀ j, ∀ m ∈ S, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
      φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ)
    (piv : Fin J → Fin (n + 1)) (hpiv : ∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) :
    ‖Dsum q a (S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
        (fun mx => mx.1 * ∏ i, mx.2 i)
        (fun mx => (acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
            ((acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
              ∏ j, ((G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)) : ℝ) : ℂ)) * χ ((mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖ +
        ∑ j, (2 * (q.totient : ℝ)⁻¹ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ((∑ m ∈ S, ‖acoef m‖) *
              ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i)))) +
          (q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖∑ mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
              (((‖acoef mx.1‖ * ∏ i, f0 (mx.2 i / Q i)) *
                G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) : ℝ) : ℂ) * χ ((mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hsharp := norm_Dsum_sharp_le (q := q) (a := a) (S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
    (fun mx => mx.1 * ∏ i, mx.2 i) (fun mx => acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ))
    (fun j mx => if Pr j mx.1 mx.2 then 1 else 0)
    (fun j mx => G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)))
    (fun j mx => if mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)) then
      G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) else 1)
    (fun j mx => by split_ifs <;> norm_num)
    (fun j mx => ⟨G_nonneg hθ hθΛ _, G_le_one _⟩)
    (fun j mx => by
      split_ifs with hp hmx hmx
      · rw [Finset.mem_product] at hmx
        have := abs_ind_sub_G_le hθ hΛ0 (hΛ j mx.1 hmx.1 mx.2 hmx.2) (Pr j mx.1 mx.2) (hP j mx.1 mx.2)
        rwa [ite_eq_left hp] at this
      · rw [abs_le]
        have h1 := G_nonneg hθ hθΛ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        have h2 := G_le_one (θ := θ) (Λ := Λ) (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        constructor <;> linarith
      · rw [Finset.mem_product] at hmx
        have := abs_ind_sub_G_le hθ hΛ0 (hΛ j mx.1 hmx.1 mx.2 hmx.2) (Pr j mx.1 mx.2) (hP j mx.1 mx.2)
        rwa [ite_eq_right hp] at this
      · rw [abs_le]
        have h1 := G_nonneg hθ hθΛ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        have h2 := G_le_one (θ := θ) (Λ := Λ) (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        constructor <;> linarith)
  have hw : ∀ (m : ℕ) (x : Fin (n + 1) → ℕ),
      ‖acoef m * ∏ i : Fin (n + 1), (f0 (x i / Q i) : ℂ)‖ = ‖acoef m‖ * ∏ i : Fin (n + 1), f0 (x i / Q i) := by
    intro m x
    rw [norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
  refine hsharp.trans (add_le_add (norm_Dsum_le ha _ _ _) (Finset.sum_le_sum fun j _ => add_le_add ?_ ?_))
  · -- the pivot count
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.sum_product]
    calc ∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          ‖acoef (m, x).1 * ∏ i, (f0 ((m, x).2 i / Q i) : ℂ)‖ *
            (if (m, x) ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)) then
              G θ θ (φ j (m, x).1 + ∑ i, e j i * Real.log ((m, x).2 i) + θ) else 1)
        = ∑ m ∈ S, ‖acoef m‖ * ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
            (∏ i, f0 (x i / Q i)) * G θ θ (φ j m + ∑ i, e j i * Real.log (x i) + θ) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [ite_eq_left (Finset.mem_product.2 ⟨hm, hx⟩), hw]
          ring
      _ ≤ ∑ m ∈ S, ‖acoef m‖ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i))) := by
          refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine pivot_sum_le (fun i => primesTo (Q i)) (piv j) (fun i y => f0 (y / Q i)) (fun i y => hf0 _)
            (fun x => G θ θ (φ j m + ∑ i, e j i * Real.log (x i) + θ)) fun z => ?_
          have hsplit : ∀ y : ℕ, φ j m + ∑ i, e j i * Real.log (((piv j).insertNth y z : Fin (n + 1) → ℕ) i) + θ =
              (φ j m + ∑ i : Fin n, e j ((piv j).succAbove i) * Real.log (z i)) +
                e j (piv j) * Real.log y + θ := by
            intro y
            rw [Fin.sum_univ_succAbove _ (piv j)]
            simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
            ring
          simp only [hsplit]
          exact pivot_term_le hf0 hF₀ hθ (hQ (piv j)) (hpiv j)
      _ = F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ((∑ m ∈ S, ‖acoef m‖) *
              ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i))) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
  · -- the near-boundary families
    refine (norm_Dsum_le ha _ _ _).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun mx hmx => ?_
    rw [ite_eq_left hmx, hw]

end SharpFamily

omit [NeZero q] in
/-- The tuple form of a twisted family sum is the form of `family_bound`. -/
theorem tuple_sum_eq (χ : DirichletCharacter ℂ q) (S : Finset ℕ) (acoef : ℕ → ℂ) {K J : ℕ} (Q : ℕ → ℝ)
    (f0 : ℝ → ℝ) (g : Fin J → ℝ → ℂ) (ℓ : Fin J → ℕ → (Fin K → ℕ) → ℝ) :
    ∑ mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        ((acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) * ∏ j, g j (ℓ j mx.1 mx.2)) *
          χ ((mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q) =
      ∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        acoef m * χ m * (∏ i : Fin K, χ (x i) * (f0 (x i / Q i) : ℂ)) * ∏ j, g j (ℓ j m x) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.cast_mul, Nat.cast_prod, map_mul, map_prod, Finset.prod_mul_distrib]
  ring

/-- There are at most `φ(q)` characters `χ ≠ 1`. -/
theorem card_chars_le : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤ q.totient := by
  have h : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]; exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h2 := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q)) (fun χ => χ ≠ 1)
  rw [Finset.card_univ, h] at h2
  exact_mod_cast h2

/-- Products of masses: if `0 ≤ m_j ≤ M` then `∏ m_j ≤ M^J`. -/
theorem prod_masses_le {J : ℕ} (m : Fin J → ℝ) {M : ℝ} (hm0 : ∀ j, 0 ≤ m j) (hm : ∀ j, m j ≤ M) :
    ∏ j, m j ≤ M ^ J := by
  calc ∏ j, m j ≤ ∏ _j : Fin J, M := Finset.prod_le_prod₀ (fun j _ => hm0 j) fun j _ => hm j
    _ = M ^ J := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `Σ_j t_j ∏_{i≠j} m_i ≤ JτM^J` for `0 ≤ m_j ≤ M`, `0 ≤ t_j ≤ τ` and `M ≥ 1`. -/
theorem sum_tails_le {J : ℕ} [DecidableEq (Fin J)] (m t : Fin J → ℝ) {M τ : ℝ} (hM : 1 ≤ M) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m j ≤ M) (ht0 : ∀ j, 0 ≤ t j) (ht : ∀ j, t j ≤ τ) :
    ∑ j, t j * ∏ i ∈ Finset.univ.erase j, m i ≤ J * τ * M ^ J := by
  calc ∑ j, t j * ∏ i ∈ Finset.univ.erase j, m i ≤ ∑ _j : Fin J, τ * M ^ J := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hτ : 0 ≤ τ := le_trans (ht0 j) (ht j)
        have hp : ∏ i ∈ Finset.univ.erase j, m i ≤ M ^ J := by
          calc ∏ i ∈ Finset.univ.erase j, m i ≤ ∏ _i ∈ Finset.univ.erase j, M :=
                Finset.prod_le_prod₀ (fun i _ => hm0 i) fun i _ => hm i
            _ = M ^ (J - 1) := by
                rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
                  Fintype.card_fin]
            _ ≤ M ^ J := pow_le_pow_right₀ hM (Nat.sub_le J 1)
        exact mul_le_mul (ht j) hp (Finset.prod_nonneg fun i _ => hm0 i) hτ
    _ = J * τ * M ^ J := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

section Explicit

open SieveSmooth Classical
open scoped ContDiff

/-- The mass bound `M(θ, Λ) = π(2Λ + θ) + c₂/(2πθ)` of `mass_GC_le`. -/
noncomputable def massB (θ Λ : ℝ) : ℝ := π * (2 * Λ + θ) + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * θ)

/-- The tail bound of `tail_GC_le`. -/
noncomputable def tailB (θ T₀ : ℝ) (k : ℕ) : ℝ :=
  2 * π * ((2 * (θ⁻¹ ^ k * θ) * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) * (T₀ ^ (k - 2))⁻¹

/-- **A sharp family, with the Type II estimate.** Let `f0` be smooth with support in `[1/2, 2]`, `0 ≤ f0 ≤ F₀` and
`e₁ > 0`. There is `q₀` such that for `q ≥ q₀`, a unit `a`, a family as in `family_bound` with `n + 1 ≤ K₀` primes,
and `J` sharp comparisons as in `Dsum_sharp_le`, with `0 < θ ≤ 1 ≤ Λ`, `ℓ_j ≤ Λ` on the family, pivots with
coefficients `±1`, `T₀ ≥ 1`, `k ≥ 2` and `2π(Σ_j |e_{ji}|)T₀ ≤ q^{1/100000}` for each `i`: the `|A − B/φ(q)|` of the
sharp family is at most
`φ(q)⁻¹(q^{L−1/50000}(Σ|a_m|²/P)^{1/2}(M^J + J·M̃) + φ(q)·Box·Jτ(M^J + 1))` plus twice `φ(q)⁻¹` times the pivots'
counts. Here `M = massB θ Λ`, `M̃ = massB θ θ`, `τ = tailB θ T₀ k`, and `Box = Σ|a_m| ∏_i Σ_p |f0(p/Q_i)|`. -/
theorem typeII_sharp_explicit {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (hf0nn : ∀ u, 0 ≤ f0 u) {F₀ : ℝ} (hF₀ : ∀ u, f0 u ≤ F₀) (K₀ : ℕ) {e₁ : ℝ} (he₁ : 0 < e₁) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (acoef : ℕ → ℂ) (n : ℕ), n + 1 ≤ K₀ → ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) →
      ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) / P →
      ∀ {J : ℕ} (φ : Fin J → ℕ → ℝ) (e : Fin J → Fin (n + 1) → ℝ) (Pr : Fin J → ℕ → (Fin (n + 1) → ℕ) → Prop),
      (∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
        (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i))) →
      ∀ θ Λ : ℝ, 0 < θ → θ ≤ 1 → 1 ≤ Λ →
      (∀ j, ∀ m ∈ S, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ) →
      ∀ piv : Fin J → Fin (n + 1), (∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) →
      ∀ (T₀ : ℝ) (k : ℕ), 1 ≤ T₀ → 2 ≤ k →
      (∀ i : Fin (n + 1), 2 * π * (∑ j, |e j i|) * T₀ ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
      ‖Dsum q a (S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
          (fun mx => mx.1 * ∏ i, mx.2 i)
          (fun mx => (acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        (q.totient : ℝ)⁻¹ *
          ((q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) *
              (massB θ Λ ^ J + J * massB θ θ) +
            q.totient * ((∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|) *
              (J * tailB θ T₀ k * massB θ Λ ^ J + J * tailB θ T₀ k)) +
          ∑ j, 2 * (q.totient : ℝ)⁻¹ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ((∑ m ∈ S, ‖acoef m‖) *
              ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i)))) := by
  obtain ⟨q₁, hq₁⟩ := family_bound hf0 hsupp K₀ he₁ (η := 1 / 100000) (by norm_num) (by norm_num)
  refine ⟨q₁, fun q _ hq a ha P S hS hP1 hP2 acoef n hK Q hQ hQP J φ e Pr hP θ Λ hθ hθ1 hΛ1 hΛ piv hpiv
    T₀ k hT₀ hk hT => ?_⟩
  have hθΛ : θ ≤ 2 * Λ := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hQpos : ∀ i : Fin (n + 1), 0 < Q i := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hq0 _) (hQ i i.isLt)
  have hstep := Dsum_sharp_le ha S acoef Q hQpos hf0nn hF₀ φ e Pr hθ hθΛ hP hΛ piv hpiv
  refine hstep.trans ?_
  -- the bounds of the masses and tails
  set M := massB θ Λ with hMdef
  set Mt := massB θ θ with hMtdef
  set τ := tailB θ T₀ k with hτdef
  have hc₂ : 0 ≤ ∫ v, ‖iteratedDeriv 2 gc v‖ := integral_nonneg fun _ => norm_nonneg _
  have hM1 : 1 ≤ M := by
    rw [hMdef, massB]
    have : 0 ≤ (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * θ) := by positivity
    nlinarith [Real.pi_gt_three]
  have hmass : ∫ t, ‖𝓕 (GC θ Λ) t‖ ≤ M := mass_GC_le hθ hθΛ
  have hmasst : ∫ t, ‖𝓕 (GC θ θ) t‖ ≤ Mt := mass_GC_le hθ (by linarith)
  have htail : ∀ Λ' : ℝ, 0 ≤ Λ' →
      ∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ') t‖) t ≤ τ := fun Λ' hΛ' =>
    tail_GC_le hθ hΛ' hk hT₀
  have hm0 : ∀ Λ' : ℝ, 0 ≤ ∫ t, ‖𝓕 (GC θ Λ') t‖ := fun Λ' => integral_nonneg fun _ => norm_nonneg _
  have ht0 : ∀ Λ' : ℝ, 0 ≤ ∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ') t‖) t :=
    fun Λ' => integral_nonneg fun _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  set Box := (∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| with hBox
  have hBox0 : 0 ≤ Box := by positivity
  have hcard := card_chars_le (q := q)
  have hτ0 : 0 ≤ τ := le_trans (ht0 Λ) (htail Λ hΛ0)
  have hsq0 : 0 ≤ (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) := by
    positivity
  -- the smoothed family
  have hX : ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖∑ mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        ((acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
          ∏ j, ((G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)) : ℝ) : ℂ)) *
            χ ((mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖ ≤
      (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) * M ^ J +
        q.totient * Box * (J * τ * M ^ J) := by
    have hconv : ∀ χ : DirichletCharacter ℂ q,
        ∑ mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          ((acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
            ∏ j, ((G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)) : ℝ) : ℂ)) *
              χ ((mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q) =
        ∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          acoef m * χ m * (∏ i : Fin (n + 1), χ (x i) * (f0 (x i / Q i) : ℂ)) *
            ∏ j, GC θ Λ (φ j m + ∑ i : Fin (n + 1), e j i * Real.log (x i)) := by
      intro χ
      simp_rw [GC_eq_G]
      exact tuple_sum_eq χ S acoef Q f0 (fun _ u => (G θ Λ u : ℂ))
        (fun j m x => φ j m + ∑ i, e j i * Real.log (x i))
    simp_rw [hconv]
    refine (hq₁ q hq P S hS hP1 hP2 acoef (n + 1) hK Q hQ hQP (fun _ => GC θ Λ)
      (fun _ => (contDiff_GC (n := 0)).continuous) (fun _ => integrable_GC hθ hΛ0)
      (fun _ => integrable_fourier_GC hθ hΛ0) φ e T₀ hT).trans ?_
    refine add_le_add (mul_le_mul_of_nonneg_left (prod_masses_le _ (fun j => hm0 Λ) (fun j => hmass)) hsq0) ?_
    have hS' := sum_tails_le (fun _ : Fin J => ∫ t, ‖𝓕 (GC θ Λ) t‖)
      (fun _ : Fin J => ∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t)
      hM1 (fun j => hm0 Λ) (fun j => hmass) (fun j => ht0 Λ) (fun j => htail Λ hΛ0)
    have hS0 : 0 ≤ ∑ j : Fin J, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t) *
        ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (GC θ Λ) t‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ht0 Λ) (Finset.prod_nonneg fun i _ => hm0 Λ)
    calc ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) * Box *
          ∑ j : Fin J, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t) *
            ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (GC θ Λ) t‖
        ≤ q.totient * Box * ∑ j : Fin J, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t) *
            ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (GC θ Λ) t‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hBox0) hS0
      _ ≤ q.totient * Box * (J * τ * M ^ J) := mul_le_mul_of_nonneg_left hS' (by positivity)
  -- the near-boundary families
  have hY : ∀ j, ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖∑ mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        (((‖acoef mx.1‖ * ∏ i, f0 (mx.2 i / Q i)) *
          G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) : ℝ) : ℂ) *
            χ ((mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖ ≤
      (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) * Mt +
        q.totient * Box * τ := by
    intro j
    have hconv : ∀ χ : DirichletCharacter ℂ q,
        ∑ mx ∈ S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          (((‖acoef mx.1‖ * ∏ i, f0 (mx.2 i / Q i)) *
            G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) : ℝ) : ℂ) *
              χ ((mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q) =
        ∑ m ∈ S, ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          (‖acoef m‖ : ℂ) * χ m * (∏ i : Fin (n + 1), χ (x i) * (f0 (x i / Q i) : ℂ)) *
            ∏ _j' : Fin 1, GC θ θ ((φ j m + θ) + ∑ i : Fin (n + 1), e j i * Real.log (x i)) := by
      intro χ
      rw [← tuple_sum_eq χ S (fun m => (‖acoef m‖ : ℂ)) Q f0 (fun _ : Fin 1 => GC θ θ)
        (fun _ m x => (φ j m + θ) + ∑ i : Fin (n + 1), e j i * Real.log (x i))]
      refine Finset.sum_congr rfl fun mx _ => ?_
      rw [Fin.prod_univ_one, GC_eq_G]
      push_cast
      ring_nf
    simp_rw [hconv]
    have hT1 : ∀ i : Fin (n + 1), 2 * π * (∑ _j' : Fin 1, |e j i|) * T₀ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := by
      intro i
      refine le_trans ?_ (hT i)
      rw [Fin.sum_univ_one]
      have hle : |e j i| ≤ ∑ j', |e j' i| :=
        Finset.single_le_sum (f := fun j' => |e j' i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hT0' : 0 ≤ T₀ := by linarith
      have h2π : 0 ≤ 2 * π := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle h2π) hT0'
    refine (hq₁ q hq P S hS hP1 hP2 (fun m => (‖acoef m‖ : ℂ)) (n + 1) hK Q hQ hQP (fun _ : Fin 1 => GC θ θ)
      (fun _ => (contDiff_GC (n := 0)).continuous) (fun _ => integrable_GC hθ hθ.le)
      (fun _ => integrable_fourier_GC hθ hθ.le) (fun _ m => φ j m + θ) (fun _ i => e j i) T₀ hT1).trans ?_
    have hn1 : ∀ m, ‖((‖acoef m‖ : ℝ) : ℂ)‖ = ‖acoef m‖ := fun m => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    simp only [hn1, Fin.prod_univ_one, Fin.sum_univ_one]
    have herase : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
    rw [herase, Finset.prod_empty, mul_one]
    refine add_le_add (mul_le_mul_of_nonneg_left hmasst hsq0) ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right hcard hBox0) (htail θ hθ.le) (ht0 θ) (by positivity)
  -- assemble
  have hφ0 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
  calc _ ≤ (q.totient : ℝ)⁻¹ *
        ((q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) * M ^ J +
          q.totient * Box * (J * τ * M ^ J)) +
      ∑ j, (2 * (q.totient : ℝ)⁻¹ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ((∑ m ∈ S, ‖acoef m‖) *
              ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i)))) +
        (q.totient : ℝ)⁻¹ * ((q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) *
          Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) * Mt + q.totient * Box * τ)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hX hφ0)
          (Finset.sum_le_sum fun j _ => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hY j) hφ0))
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Explicit

/-! ### Elementary bounds for the asymptotic form -/

/-- For `Q ≥ 1`, `#primesTo Q ≤ 3Q`. -/
theorem card_primesTo_le {Q : ℝ} (hQ : 1 ≤ Q) : ((primesTo Q).card : ℝ) ≤ 3 * Q := by
  have h1 : (primesTo Q).card ≤ ⌊2 * Q⌋₊ + 1 := by
    rw [primesTo]; exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
  have h2 : ((⌊2 * Q⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Q + 1 := by
    push_cast; linarith [Nat.floor_le (show (0 : ℝ) ≤ 2 * Q by linarith)]
  calc ((primesTo Q).card : ℝ) ≤ ((⌊2 * Q⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ 2 * Q + 1 := h2
    _ ≤ 3 * Q := by linarith

/-- For `0 ≤ f0 ≤ F₀` and `Q ≥ 1`, `Σ_{p ∈ primesTo Q} |f0(p/Q)| ≤ 3F₀Q`. -/
theorem sum_f0_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ p ∈ primesTo Q, |f0 (p / Q)| ≤ 3 * F₀ * Q := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  calc ∑ p ∈ primesTo Q, |f0 (p / Q)| ≤ ∑ _p ∈ primesTo Q, F₀ :=
        Finset.sum_le_sum fun p _ => by rw [abs_of_nonneg (hf0 _)]; exact hF₀ _
    _ = (primesTo Q).card * F₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * Q * F₀ := mul_le_mul_of_nonneg_right (card_primesTo_le hQ) hF0
    _ = 3 * F₀ * Q := by ring

/-- For `S ⊆ (P, 2P]` and `|a_m| ≤ A₀` for every `m`, `Σ_{m∈S} |a_m| ≤ PA₀`. -/
theorem sum_norm_le {S : Finset ℕ} {P : ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) {acoef : ℕ → ℂ} {A₀ : ℝ}
    (hA : ∀ m, ‖acoef m‖ ≤ A₀) : ∑ m ∈ S, ‖acoef m‖ ≤ P * A₀ := by
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hcard : (S.card : ℝ) ≤ P := by
    have := Finset.card_le_card hS
    rw [Nat.card_Ioc] at this
    have h2 : 2 * P - P = P := by omega
    rw [h2] at this
    exact_mod_cast this
  calc ∑ m ∈ S, ‖acoef m‖ ≤ ∑ _m ∈ S, A₀ := Finset.sum_le_sum fun m _ => hA m
    _ = S.card * A₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ P * A₀ := mul_le_mul_of_nonneg_right hcard hA0

/-- For `P > 0`, `S ⊆ (P, 2P]` and `|a_m| ≤ A₀` for every `m`, `(Σ_{m∈S} |a_m|²/P)^{1/2} ≤ A₀`. -/
theorem sqrt_sum_sq_le {S : Finset ℕ} {P : ℕ} (hP : 0 < P) (hS : S ⊆ Finset.Ioc P (2 * P)) {acoef : ℕ → ℂ}
    {A₀ : ℝ} (hA : ∀ m, ‖acoef m‖ ≤ A₀) : Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) ≤ A₀ := by
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hcard : (S.card : ℝ) ≤ P := by
    have := Finset.card_le_card hS
    rw [Nat.card_Ioc] at this
    have h2 : 2 * P - P = P := by omega
    rw [h2] at this
    exact_mod_cast this
  rw [Real.sqrt_le_left hA0, div_le_iff₀ hP']
  calc ∑ m ∈ S, ‖acoef m‖ ^ 2 ≤ ∑ _m ∈ S, A₀ ^ 2 :=
        Finset.sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (hA m) 2
    _ = S.card * A₀ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ P * A₀ ^ 2 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = A₀ ^ 2 * P := by ring

/-- `e^{3θ} − 1 ≤ 6θ` for `0 ≤ θ ≤ 1/3`. -/
theorem exp_three_sub_one_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 3) : Real.exp (3 * θ) - 1 ≤ 6 * θ := by
  have hx : |3 * θ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.exp_bound hx (n := 1) (by norm_num)
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  have h' := (abs_le.1 h).2
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * θ)] at h'
  norm_num at h'
  linarith

/-! ### The asymptotic form -/

section Helpers

open SieveSmooth Filter Asymptotics

/-- For `r > 0` and `Λ₀ ≥ 0`, eventually in `x`: `π(2Λ₀ log x + 3) ≤ x^r`. -/
theorem ev_pi_log_le {r Λ₀ : ℝ} (hr : 0 < r) (hΛ₀ : 0 ≤ Λ₀) :
    ∀ᶠ x : ℝ in atTop, π * (2 * Λ₀ * Real.log x + 3) ≤ x ^ r := by
  have hpi := Real.pi_pos
  have hc : (0 : ℝ) < 1 / (4 * π * Λ₀ + 1) := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).def hc
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (6 * π)
  filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx3
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx3
  have hxr : 0 ≤ x ^ r := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hxr] at hx1
  have h4 : 2 * π * Λ₀ * Real.log x ≤ 2 * π * Λ₀ * (1 / (4 * π * Λ₀ + 1) * x ^ r) :=
    mul_le_mul_of_nonneg_left hx1 (by positivity)
  have h6 : 2 * π * Λ₀ / (4 * π * Λ₀ + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg hpi.le hΛ₀]
  have h5 : 2 * π * Λ₀ * (1 / (4 * π * Λ₀ + 1) * x ^ r) ≤ x ^ r / 2 := by
    rw [show 2 * π * Λ₀ * (1 / (4 * π * Λ₀ + 1) * x ^ r) = (2 * π * Λ₀ / (4 * π * Λ₀ + 1)) * x ^ r by ring]
    nlinarith
  nlinarith

/-- The masses at `θ = x^{−ε}` and `Λ = Λ₀ log x + 1`: for `x ≥ 1`, `Λ₀ ≥ 0` and `π(2Λ₀ log x + 3) ≤ x^ε`, both
`massB θ Λ` and `massB θ θ` are at most `Cx^ε`, `C = 1 + c₂/(2π)`. -/
theorem massB_le {x ε Λ₀ : ℝ} (hx : 1 ≤ x) (hΛ₀ : 0 ≤ Λ₀) (hlog : π * (2 * Λ₀ * Real.log x + 3) ≤ x ^ ε) :
    massB (x ^ (-ε)) (Λ₀ * Real.log x + 1) ≤ (1 + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π)) * x ^ ε ∧
      massB (x ^ (-ε)) (x ^ (-ε)) ≤ (1 + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π)) * x ^ ε := by
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_pos
  have hinv : (x ^ (-ε))⁻¹ = x ^ ε := by rw [Real.rpow_neg hx0.le, inv_inv]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxε : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hθ1 : x ^ (-ε) ≤ 1 := by
    have h3 : 3 * π ≤ x ^ ε := by nlinarith [mul_nonneg hΛ₀ hl]
    rw [Real.rpow_neg hx0.le]
    exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have htail : (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * x ^ (-ε)) =
      (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π) * x ^ ε := by
    rw [← hinv]; field_simp
  constructor
  · rw [massB, htail]
    have : π * (2 * (Λ₀ * Real.log x + 1) + x ^ (-ε)) ≤ π * (2 * Λ₀ * Real.log x + 3) := by
      apply mul_le_mul_of_nonneg_left _ hpi.le; linarith
    linarith
  · rw [massB, htail]
    have : π * (2 * x ^ (-ε) + x ^ (-ε)) ≤ π * (2 * Λ₀ * Real.log x + 3) := by
      apply mul_le_mul_of_nonneg_left _ hpi.le; nlinarith [mul_nonneg hΛ₀ hl]
    linarith

/-- The tail at `θ = x^{−ε}` and `T₀ = x^{1/200000}`: for `x ≥ 1`, `k ≥ 2` and `εk − ε − (k − 2)/200000 ≤ −3`,
`tailB θ T₀ k ≤ 2π(2c_k/(2π)^k)x^{−3}`. -/
theorem tailB_le {x ε : ℝ} {k : ℕ} (hx : 1 ≤ x) (hk : 2 ≤ k)
    (hexp : ε * k - ε - ((k : ℝ) - 2) / 200000 ≤ -3) :
    tailB (x ^ (-ε)) (x ^ (1 / 200000 : ℝ)) k ≤
      2 * π * ((2 * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) * x ^ (-3 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hinv : (x ^ (-ε))⁻¹ = x ^ ε := by rw [Real.rpow_neg hx0.le, inv_inv]
  have h1 : (x ^ (-ε))⁻¹ ^ k * x ^ (-ε) = x ^ (ε * k - ε) := by
    rw [hinv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, sub_eq_add_neg]
  have h2 : ((x ^ (1 / 200000 : ℝ)) ^ (k - 2))⁻¹ = x ^ (-(((k : ℝ) - 2) / 200000)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_neg hx0.le, Nat.cast_sub hk]
    congr 1; push_cast; ring
  rw [tailB, h1, h2]
  have hck : 0 ≤ ∫ v, ‖iteratedDeriv k gc v‖ := integral_nonneg fun _ => norm_nonneg _
  have h3 : x ^ (ε * k - ε) * x ^ (-(((k : ℝ) - 2) / 200000)) ≤ x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hpi := Real.pi_pos
  calc 2 * π * ((2 * x ^ (ε * k - ε) * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) *
        x ^ (-(((k : ℝ) - 2) / 200000)) =
      2 * π * ((2 * ∫ v, ‖iteratedDeriv k gc v‖) / (2 * π) ^ k) *
        (x ^ (ε * k - ε) * x ^ (-(((k : ℝ) - 2) / 200000))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The box: `Σ|a_m| ∏_i Σ_p |f0(p/Q_i)| ≤ A₀(3F₀ + 1)^{K₀}X`, for `0 ≤ f0 ≤ F₀`, `P > 0`, `S ⊆ (P, 2P]`,
`|a_m| ≤ A₀` for every `m`, `n + 1 ≤ K₀`, `Q_i ≥ 1` and `∏ Q_i ≤ X/P`. -/
theorem box_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {S : Finset ℕ} {P : ℕ}
    (hP : 0 < P) (hS : S ⊆ Finset.Ioc P (2 * P)) {acoef : ℕ → ℂ} {A₀ : ℝ} (hA : ∀ m, ‖acoef m‖ ≤ A₀)
    {n K₀ : ℕ} (hK : n + 1 ≤ K₀) {Q : ℕ → ℝ} (hQ : ∀ i : Fin (n + 1), 1 ≤ Q i) {X : ℝ}
    (hQP : ∏ j ∈ Finset.range (n + 1), Q j ≤ X / P) :
    (∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| ≤
      A₀ * (3 * F₀ + 1) ^ K₀ * X := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hQ0 : ∀ i : Fin (n + 1), 0 ≤ Q i := fun i => by linarith [hQ i]
  have hprodQ : ∏ i : Fin (n + 1), Q i ≤ X / P := by
    rw [Fin.prod_univ_eq_prod_range (fun j => Q j) (n + 1)]; exact hQP
  have hprod0 : 0 ≤ ∏ i : Fin (n + 1), Q i := Finset.prod_nonneg fun i _ => hQ0 i
  have hX0 : 0 ≤ X := by
    have h := mul_nonneg (hprod0.trans hprodQ) hP'.le
    rwa [div_mul_cancel₀ _ hP'.ne'] at h
  have h1 : ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| ≤ ∏ i : Fin (n + 1), (3 * F₀ * Q i) :=
    Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun p _ => abs_nonneg _)
      (fun i _ => sum_f0_le hf0 hF₀ (hQ i))
  have h2 : ∏ i : Fin (n + 1), (3 * F₀ * Q i) = (3 * F₀) ^ (n + 1) * ∏ i : Fin (n + 1), Q i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 : (3 * F₀) ^ (n + 1) ≤ (3 * F₀ + 1) ^ K₀ :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hK)
  calc (∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|
      ≤ (P * A₀) * ((3 * F₀) ^ (n + 1) * (X / P)) := by
        refine mul_le_mul (sum_norm_le hS hA) ?_ (Finset.prod_nonneg fun i _ =>
          Finset.sum_nonneg fun p _ => abs_nonneg _) (by positivity)
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left hprodQ (by positivity))
    _ = A₀ * (3 * F₀) ^ (n + 1) * X := by field_simp
    _ ≤ A₀ * (3 * F₀ + 1) ^ K₀ * X := by gcongr

/-- A pivot's count: `F₀((e^{3θ} − 1)2Q_p + 1)·Σ|a_m|·∏_{i ≠ p} Σ_y f0(y/Q_i) ≤ F₀A₀(3F₀ + 1)^{K₀}(12θ + 1/Q_min)X`,
for `0 ≤ f0 ≤ F₀`, `P > 0`, `S ⊆ (P, 2P]`, `|a_m| ≤ A₀` for every `m`, `n + 1 ≤ K₀`, `Q_i ≥ Q_min ≥ 1`,
`∏ Q_i ≤ X/P` and `0 ≤ θ ≤ 1/3`. -/
theorem pivot_le {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {S : Finset ℕ} {P : ℕ}
    (hP : 0 < P) (hS : S ⊆ Finset.Ioc P (2 * P)) {acoef : ℕ → ℂ} {A₀ : ℝ} (hA : ∀ m, ‖acoef m‖ ≤ A₀)
    {n K₀ : ℕ} (hK : n + 1 ≤ K₀) {Q : ℕ → ℝ} {Qmin : ℝ} (hQmin : 1 ≤ Qmin) (hQ : ∀ i : Fin (n + 1), Qmin ≤ Q i)
    {X : ℝ} (hQP : ∏ j ∈ Finset.range (n + 1), Q j ≤ X / P) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 3)
    (p : Fin (n + 1)) :
    F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q p) + 1) *
        ((∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i))) ≤
      F₀ * A₀ * (3 * F₀ + 1) ^ K₀ * (12 * θ + Qmin⁻¹) * X := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hQ1 : ∀ i : Fin (n + 1), 1 ≤ Q i := fun i => hQmin.trans (hQ i)
  have hQ0 : ∀ i : Fin (n + 1), 0 ≤ Q i := fun i => by linarith [hQ1 i]
  have hQp : 0 < Q p := by linarith [hQ1 p]
  have hprodQ : ∏ i : Fin (n + 1), Q i ≤ X / P := by
    rw [Fin.prod_univ_eq_prod_range (fun j => Q j) (n + 1)]; exact hQP
  have hsplit : ∏ i : Fin (n + 1), Q i = Q p * ∏ i : Fin n, Q (p.succAbove i) := Fin.prod_univ_succAbove _ p
  set R := ∏ i : Fin n, Q (p.succAbove i) with hR
  have hR0 : 0 ≤ R := Finset.prod_nonneg fun i _ => hQ0 _
  have hX0 : 0 ≤ X / P := le_trans (by rw [hsplit]; exact mul_nonneg hQp.le hR0) hprodQ
  -- the counts of the other primes
  have h1 : ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)) ≤ (3 * F₀) ^ n * R := by
    have : ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)) ≤
        ∏ i : Fin n, (3 * F₀ * Q (p.succAbove i)) :=
      Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => hf0 _) (fun i _ => by
        have := sum_f0_le hf0 hF₀ (hQ1 (p.succAbove i))
        simp only [abs_of_nonneg (hf0 _)] at this
        exact this)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have h1' : 0 ≤ ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)) :=
    Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun y _ => hf0 _
  -- the pivot's factor
  have he : (Real.exp (3 * θ) - 1) * (2 * Q p) + 1 ≤ 12 * θ * Q p + 1 := by
    have := exp_three_sub_one_le hθ0 hθ
    nlinarith
  have he0 : 0 ≤ (Real.exp (3 * θ) - 1) * (2 * Q p) + 1 := by
    have : 0 ≤ Real.exp (3 * θ) - 1 := by
      have := Real.add_one_le_exp (3 * θ); linarith
    positivity
  have hkey : (12 * θ * Q p + 1) * R ≤ (12 * θ + Qmin⁻¹) * (X / P) := by
    have hRQ : R ≤ Qmin⁻¹ * (Q p * R) := by
      rw [← mul_assoc]
      have : 1 ≤ Qmin⁻¹ * Q p := by
        rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]; linarith [hQ p]
      nlinarith
    calc (12 * θ * Q p + 1) * R = 12 * θ * (Q p * R) + R := by ring
      _ ≤ 12 * θ * (Q p * R) + Qmin⁻¹ * (Q p * R) := by linarith
      _ = (12 * θ + Qmin⁻¹) * (Q p * R) := by ring
      _ ≤ (12 * θ + Qmin⁻¹) * (X / P) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← hsplit]; exact hprodQ
  have h3 : (3 * F₀) ^ n ≤ (3 * F₀ + 1) ^ K₀ :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  calc F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q p) + 1) *
        ((∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)))
      ≤ F₀ * (12 * θ * Q p + 1) * ((P * A₀) * ((3 * F₀) ^ n * R)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left he hF0) (mul_le_mul (sum_norm_le hS hA) h1 h1'
          (by positivity)) (mul_nonneg (Finset.sum_nonneg fun m _ => norm_nonneg _) h1') (by positivity)
    _ = F₀ * A₀ * (3 * F₀) ^ n * P * ((12 * θ * Q p + 1) * R) := by ring
    _ ≤ F₀ * A₀ * (3 * F₀) ^ n * P * ((12 * θ + Qmin⁻¹) * (X / P)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = F₀ * A₀ * (3 * F₀) ^ n * (12 * θ + Qmin⁻¹) * X := by field_simp
    _ ≤ F₀ * A₀ * (3 * F₀ + 1) ^ K₀ * (12 * θ + Qmin⁻¹) * X := by
        have : 0 ≤ (12 * θ + Qmin⁻¹) * X := by
          have hXX : 0 ≤ X := by
            have h := mul_nonneg hX0 hP'.le
            rwa [div_mul_cancel₀ _ hP'.ne'] at h
          positivity
        have := mul_le_mul_of_nonneg_right h3 this
        nlinarith [mul_nonneg hF0 hA0]

/-- The bracket: `a₁x^{−7/400000} + a₂x^{−1} + a₃(12x^{−ε} + x^{−e}) ≤ x^{−δ}` when `x ≥ 1`, `a₁, a₂, a₃ ≥ 0`,
`δ > 0`, `2δ ≤ ε ≤ 1/400000`, `2δ ≤ e` and `a₁ + a₂ + 13a₃ ≤ x^δ`. -/
theorem bracket_le {x a₁ a₂ a₃ ε e δ : ℝ} (hx : 1 ≤ x) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃)
    (hδ : 0 < δ) (hδε : 2 * δ ≤ ε) (hε : ε ≤ 1 / 400000) (hδe : 2 * δ ≤ e)
    (hsum : a₁ + a₂ + 13 * a₃ ≤ x ^ δ) :
    a₁ * x ^ (-(7 / 400000) : ℝ) + a₂ * x ^ (-1 : ℝ) + a₃ * (12 * x ^ (-ε) + x ^ (-e)) ≤ x ^ (-δ) := by
  have hx0 : 0 < x := by linarith
  have hle : ∀ s : ℝ, 2 * δ ≤ s → x ^ (-s) ≤ x ^ (-(2 * δ)) := fun s hs =>
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have e1 := hle (7 / 400000) (by linarith)
  have e2 := hle 1 (by linarith)
  have e3 := hle ε hδε
  have e4 := hle e hδe
  have hsplit : x ^ (-(2 * δ)) = x ^ (-δ) * x ^ (-δ) := by rw [← Real.rpow_add hx0]; ring_nf
  have hdd : x ^ δ * x ^ (-δ) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hpos : 0 ≤ x ^ (-δ) := by positivity
  calc a₁ * x ^ (-(7 / 400000) : ℝ) + a₂ * x ^ (-1 : ℝ) + a₃ * (12 * x ^ (-ε) + x ^ (-e))
      ≤ (a₁ + a₂ + 13 * a₃) * x ^ (-(2 * δ)) := by nlinarith
    _ ≤ x ^ δ * x ^ (-(2 * δ)) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = x ^ (-δ) := by rw [hsplit, ← mul_assoc, hdd, one_mul]

end Helpers

section Asym

open SieveSmooth Classical Filter Asymptotics
open scoped ContDiff

/-- **The Type II estimate for a sharp family (Lemmas 4′ and 4″), asymptotic form.** Let `L = 2.333`, `f0` smooth
with support in `[1/2, 2]` and `0 ≤ f0 ≤ F₀`, and fix the family's shape: `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0`, `Λ₀ ≥ 0`
and `A₀ ≥ 0`. There are `δ > 0` and `q₀` with the following property. Let `q ≥ q₀`, let `a` be a unit mod `q`, let `m`
run over `S ⊆ (P, 2P]`, `q^{0.401L} ≤ P ≤ q^{0.485L}`, with coefficients `a_m`, `|a_m| ≤ A₀` for every `m`, and let
`n + 1 ≤ K₀` primes `x_i` run over `Sp`'s ranges at the scales `Q_i ≥ q^{e₁}`, `∏_i Q_i ≤ 2^{K₀}q^L/P`, with the
weights `f0(x_i/Q_i)`. Let `J ≤ J₀` sharp comparisons `P_j` hold when `ℓ_j = φ_j(m) + Σ_i e_{ji} log x_i > 0` and
imply `ℓ_j ≥ 0`, with `|e_{ji}| ≤ E₀`, `ℓ_j ≤ Λ₀ log q` on the family, and for each `j` a pivot `i` with
`e_{ji} = ±1`. Then the family's `|A − B/φ(q)|` is at most `A₀q^{L−δ}/φ(q)`. -/
theorem typeII_sharp {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (hf0nn : ∀ u, 0 ≤ f0 u) {F₀ : ℝ} (hF₀ : ∀ u, f0 u ≤ F₀) (K₀ J₀ : ℕ) {e₁ E₀ Λ₀ A₀ : ℝ} (he₁ : 0 < e₁)
    (hE₀ : 0 ≤ E₀) (hΛ₀ : 0 ≤ Λ₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (acoef : ℕ → ℂ), (∀ m, ‖acoef m‖ ≤ A₀) →
      ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) →
      ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) / P →
      ∀ {J : ℕ}, J ≤ J₀ → ∀ (φ : Fin J → ℕ → ℝ) (e : Fin J → Fin (n + 1) → ℝ)
        (Pr : Fin J → ℕ → (Fin (n + 1) → ℕ) → Prop), (∀ j i, |e j i| ≤ E₀) →
      (∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
        (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i))) →
      (∀ j, ∀ m ∈ S, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ₀ * Real.log q) →
      ∀ piv : Fin J → Fin (n + 1), (∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) →
      ‖Dsum q a (S ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
          (fun mx => mx.1 * ∏ i, mx.2 i)
          (fun mx => (acoef mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)) := by
  obtain ⟨q₁, hq₁⟩ := typeII_sharp_explicit hf0 hsupp hf0nn hF₀ K₀ he₁
  have hF0 : 0 ≤ F₀ := le_trans (hf0nn 0) (hF₀ 0)
  have hpi := Real.pi_pos
  have hJ0 : (0 : ℝ) ≤ J₀ := Nat.cast_nonneg _
  -- the exponents
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = 1 / (400000 * ((J₀ : ℝ) + 1)) := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  have hε₂1 : ε₂ ≤ 1 / 400000 := by
    rw [hε₂]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hε₂J : ε₂ * ((J₀ : ℝ) + 1) = 1 / 400000 := by rw [hε₂]; field_simp
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min ε₂ e₁ / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hε₂0 he₁)
  have hδε : 2 * δ ≤ ε₂ := by rw [hδ]; linarith [min_le_left ε₂ e₁]
  have hδe : 2 * δ ≤ e₁ := by rw [hδ]; linarith [min_le_right ε₂ e₁]
  -- the constants
  have hc₂ : 0 ≤ ∫ v, ‖iteratedDeriv 2 gc v‖ := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by
    rw [hC]; have : 0 ≤ (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π) := by positivity
    linarith
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ,
      c' = 2 * π * ((2 * ∫ v, ‖iteratedDeriv 1200003 gc v‖) / (2 * π) ^ 1200003) := ⟨_, rfl⟩
  have hc'0 : 0 ≤ c' := by rw [hc']; positivity
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℝ, a₁ = (1 + J₀) * C ^ (J₀ + 1) := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ℝ, a₂ = 2 * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ * J₀ * c' * C ^ (J₀ + 1) := ⟨_, rfl⟩
  obtain ⟨a₃, ha₃⟩ : ∃ a₃ : ℝ, a₃ = 2 * F₀ * J₀ * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ := ⟨_, rfl⟩
  have hF1 : 0 ≤ (3 * F₀ + 1) ^ K₀ := pow_nonneg (by linarith) _
  have hC0 : 0 ≤ C ^ (J₀ + 1) := pow_nonneg (by linarith) _
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; exact mul_nonneg (by linarith) hC0
  have ha₂0 : 0 ≤ a₂ := by
    rw [ha₂]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF1) (by positivity)) hJ0)
      hc'0) hC0
  have ha₃0 : 0 ≤ a₃ := by
    rw [ha₃]; exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hJ0) hF1) (by positivity)
  -- large `q`
  have hev : ∀ᶠ x : ℝ in atTop, 3 ≤ x ^ ε₂ ∧ π * (2 * Λ₀ * Real.log x + 3) ≤ x ^ ε₂ ∧
      2 * π * J₀ * E₀ ≤ x ^ (1 / 200000 : ℝ) ∧ a₁ + a₂ + 13 * a₃ ≤ x ^ δ ∧ 1 ≤ x :=
    ((tendsto_rpow_atTop hε₂0).eventually_ge_atTop 3).and ((ev_pi_log_le hε₂0 hΛ₀).and
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200000)).eventually_ge_atTop _).and
        (((tendsto_rpow_atTop hδ0).eventually_ge_atTop _).and (eventually_ge_atTop 1))))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ, hδ0, max q₁ N, fun q _ hq a ha P S hS hP1 hP2 acoef hA n hK Q hQ hQP J hJ φ e Pr he hP hΛ piv
    hpiv => ?_⟩
  obtain ⟨h3, hlog, hE, hcon, hq1⟩ := hN q (le_trans (le_max_right _ _) hq)
  have hq0 : (0 : ℝ) < q := by linarith
  have hA0 : 0 ≤ A₀ := le_trans (norm_nonneg _) (hA 0)
  have hl : 0 ≤ Real.log q := Real.log_nonneg hq1
  -- `θ = q^{−ε₂}`, `Λ = Λ₀ log q + 1`, `T₀ = q^{1/200000}` and `k = 1200003`
  have hθ0 : 0 < (q : ℝ) ^ (-ε₂) := Real.rpow_pos_of_pos hq0 _
  have hθ3 : (q : ℝ) ^ (-ε₂) ≤ 1 / 3 := by
    rw [Real.rpow_neg hq0.le, one_div]; exact inv_anti₀ (by norm_num) h3
  have hθ1 : (q : ℝ) ^ (-ε₂) ≤ 1 := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ₀ * Real.log q + 1 := by nlinarith [mul_nonneg hΛ₀ hl]
  have hΛ' : ∀ j, ∀ m ∈ S, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
      φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ₀ * Real.log q + 1 := fun j m hm x hx => by
    linarith [hΛ j m hm x hx]
  have hT₀ : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 200000 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hT : ∀ i : Fin (n + 1), 2 * π * (∑ j, |e j i|) * (q : ℝ) ^ (1 / 200000 : ℝ) ≤
      (q : ℝ) ^ (1 / 100000 : ℝ) := by
    intro i
    have hs : ∑ j, |e j i| ≤ J₀ * E₀ := by
      calc ∑ j, |e j i| ≤ ∑ _j : Fin J, E₀ := Finset.sum_le_sum fun j _ => he j i
        _ = J * E₀ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ J₀ * E₀ := mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) hE₀
    have hsplit : (q : ℝ) ^ (1 / 100000 : ℝ) = (q : ℝ) ^ (1 / 200000 : ℝ) * (q : ℝ) ^ (1 / 200000 : ℝ) := by
      rw [← Real.rpow_add hq0]; norm_num
    rw [hsplit]
    have hTnn : 0 ≤ (q : ℝ) ^ (1 / 200000 : ℝ) := by positivity
    have h2 : 2 * π * (∑ j, |e j i|) ≤ 2 * π * J₀ * E₀ := by
      rw [mul_assoc (2 * π) (J₀ : ℝ)]; exact mul_le_mul_of_nonneg_left hs (by positivity)
    exact mul_le_mul_of_nonneg_right (h2.trans hE) hTnn
  have hmain := hq₁ q (le_trans (le_max_left _ _) hq) a ha P S hS hP1 hP2 acoef n hK Q hQ hQP φ e Pr hP
    ((q : ℝ) ^ (-ε₂)) (Λ₀ * Real.log q + 1) hθ0 hθ1 hΛ1 hΛ' piv hpiv ((q : ℝ) ^ (1 / 200000 : ℝ)) 1200003 hT₀
    (by norm_num) hT
  refine hmain.trans ?_
  -- the masses and the tail
  obtain ⟨hM, hMt⟩ := massB_le (ε := ε₂) hq1 hΛ₀ hlog
  have hτ := tailB_le (ε := ε₂) (k := 1200003) hq1 (by norm_num) (by push_cast; linarith)
  rw [← hC] at hM hMt
  rw [← hc'] at hτ
  have hM0 : 0 ≤ massB ((q : ℝ) ^ (-ε₂)) (Λ₀ * Real.log q + 1) := by
    rw [massB]; exact add_nonneg (mul_nonneg hpi.le (by linarith)) (by positivity)
  have hMt0 : 0 ≤ massB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (-ε₂)) := by
    rw [massB]; exact add_nonneg (mul_nonneg hpi.le (by linarith)) (by positivity)
  have hτ0 : 0 ≤ tailB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (1 / 200000 : ℝ)) 1200003 := by
    rw [tailB]; positivity
  generalize massB ((q : ℝ) ^ (-ε₂)) (Λ₀ * Real.log q + 1) = M at hM hM0 ⊢
  generalize massB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (-ε₂)) = Mt at hMt hMt0 ⊢
  generalize tailB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (1 / 200000 : ℝ)) 1200003 = τ at hτ hτ0 ⊢
  -- elementary facts
  have hP0 : 0 < P := by
    have : (1 : ℝ) ≤ P := le_trans (Real.one_le_rpow hq1 (by norm_num)) hP1
    exact_mod_cast (show (0 : ℝ) < P by linarith)
  have hφpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφinv0 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hQ1 : ∀ i : Fin (n + 1), (q : ℝ) ^ e₁ ≤ Q i := fun i => hQ i i.isLt
  have hqe1 : (1 : ℝ) ≤ (q : ℝ) ^ e₁ := Real.one_le_rpow hq1 he₁.le
  have hqL : 0 ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := by positivity
  have hq4 : 1 ≤ (q : ℝ) ^ (1 / 400000 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hqε : 1 ≤ (q : ℝ) ^ ε₂ := Real.one_le_rpow hq1 hε₂0.le
  have hCq : 1 ≤ C * (q : ℝ) ^ ε₂ := one_le_mul_of_one_le_of_one_le hC1 hqε
  have hpowJ : (C * (q : ℝ) ^ ε₂) ^ (J₀ + 1) = C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ ε₂), ← Real.rpow_mul hq0.le]
    congr 2; push_cast; exact hε₂J
  have hMJ : M ^ J ≤ C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ) := by
    rw [← hpowJ]
    exact (pow_le_pow_left₀ hM0 hM J).trans (pow_le_pow_right₀ hCq (by omega))
  have hMt' : (J : ℝ) * Mt ≤ J₀ * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by
    rw [← hpowJ]
    have h1 : Mt ≤ (C * (q : ℝ) ^ ε₂) ^ (J₀ + 1) :=
      hMt.trans (by simpa using pow_le_pow_right₀ hCq (show 1 ≤ J₀ + 1 by omega))
    exact mul_le_mul (by exact_mod_cast hJ) h1 hMt0 hJ0
  have hCq4 : 1 ≤ C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hq4
  -- the smoothed family and its tails
  have hT1 : (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) *
        (M ^ J + J * Mt) ≤ A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) := by
    have hsq : Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) ≤ A₀ := sqrt_sum_sq_le hP0 hS hA
    have hsum : M ^ J + J * Mt ≤ (1 + J₀) * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by linarith
    have hexp : (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ) =
        (q : ℝ) ^ (2333 / 1000 : ℝ) * (q : ℝ) ^ (-(7 / 400000) : ℝ) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; norm_num
    calc (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖acoef m‖ ^ 2) / P) *
          (M ^ J + J * Mt)
        ≤ (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * A₀ *
            ((1 + J₀) * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hsum
            (add_nonneg (pow_nonneg hM0 _) (mul_nonneg (Nat.cast_nonneg _) hMt0))
            (mul_nonneg (by positivity) hA0)
      _ = A₀ * ((1 + J₀) * C ^ (J₀ + 1)) *
            ((q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by ring
      _ = A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) := by
          rw [hexp, ha₁]; ring
  have hBox := box_le hf0nn hF₀ hP0 hS hA hK (fun i => hqe1.trans (hQ1 i)) hQP
  have hBox0 : 0 ≤ (∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| := by
    positivity
  generalize (∑ m ∈ S, ‖acoef m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| = Box at hBox hBox0 ⊢
  have hT2 : (q.totient : ℝ) * Box * (J * τ * M ^ J + J * τ) ≤
      A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₂ * (q : ℝ) ^ (-1 : ℝ)) := by
    have hm1 : M ^ J + 1 ≤ 2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by linarith
    have hJτ : (J : ℝ) * τ * M ^ J + J * τ ≤
        J₀ * (c' * (q : ℝ) ^ (-3 : ℝ)) * (2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ))) := by
      calc (J : ℝ) * τ * M ^ J + J * τ = J * τ * (M ^ J + 1) := by ring
        _ ≤ J₀ * (c' * (q : ℝ) ^ (-3 : ℝ)) * (2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ))) :=
          mul_le_mul (mul_le_mul (by exact_mod_cast hJ) hτ hτ0 hJ0) hm1
            (by linarith [pow_nonneg hM0 J]) (mul_nonneg hJ0 (mul_nonneg hc'0 (by positivity)))
    have hexp : (q : ℝ) * (q : ℝ) ^ (-3 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ) ≤ (q : ℝ) ^ (-1 : ℝ) := by
      have : (q : ℝ) * (q : ℝ) ^ (-3 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ) = (q : ℝ) ^ ((1 : ℝ) + -3 + 1 / 400000) := by
        rw [Real.rpow_add hq0, Real.rpow_add hq0, Real.rpow_one]
      rw [this]; exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have hK0 : 0 ≤ A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * a₂ := mul_nonneg (mul_nonneg hA0 hqL) ha₂0
    calc (q.totient : ℝ) * Box * (J * τ * M ^ J + J * τ)
        ≤ (q : ℝ) * (A₀ * (3 * F₀ + 1) ^ K₀ * (2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ))) *
            (J₀ * (c' * (q : ℝ) ^ (-3 : ℝ)) * (2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)))) :=
          mul_le_mul (mul_le_mul hφq hBox hBox0 (by positivity)) hJτ
            (by linarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg J) hτ0) (pow_nonneg hM0 J),
              mul_nonneg (Nat.cast_nonneg J) hτ0])
            (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hA0 hF1) (by positivity)))
      _ = A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (2 * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ * J₀ * c' * C ^ (J₀ + 1)) *
            ((q : ℝ) * (q : ℝ) ^ (-3 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by ring
      _ ≤ A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (2 * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ * J₀ * c' * C ^ (J₀ + 1)) *
            (q : ℝ) ^ (-1 : ℝ) := by
          rw [← ha₂]; exact mul_le_mul_of_nonneg_left hexp hK0
      _ = A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₂ * (q : ℝ) ^ (-1 : ℝ)) := by rw [← ha₂]; ring
  -- the pivots' counts
  have hT3 := Finset.sum_le_sum fun (j : Fin J) (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pivot_le hf0nn hF₀ hP0 hS hA hK hqe1 hQ1 hQP hθ0.le hθ3 (piv j))
      (show (0 : ℝ) ≤ 2 * (q.totient : ℝ)⁻¹ by positivity)
  have hinv : ((q : ℝ) ^ e₁)⁻¹ = (q : ℝ) ^ (-e₁) := (Real.rpow_neg hq0.le e₁).symm
  have hX0 : 0 ≤ F₀ * A₀ * (3 * F₀ + 1) ^ K₀ * (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)) *
      (2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hF0 hA0) hF1) (by positivity)) (by positivity)
  calc _ ≤ (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) +
            A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₂ * (q : ℝ) ^ (-1 : ℝ))) +
          ∑ _j : Fin J, 2 * (q.totient : ℝ)⁻¹ * (F₀ * A₀ * (3 * F₀ + 1) ^ K₀ *
            (12 * (q : ℝ) ^ (-ε₂) + ((q : ℝ) ^ e₁)⁻¹) * (2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) hφinv0) hT3
    _ ≤ (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) +
            A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₂ * (q : ℝ) ^ (-1 : ℝ))) +
          (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) *
            (a₃ * (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)))) := by
        refine add_le_add le_rfl ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hinv, ha₃]
        calc (J : ℝ) * (2 * (q.totient : ℝ)⁻¹ * (F₀ * A₀ * (3 * F₀ + 1) ^ K₀ *
              (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)) * (2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ))))
            ≤ J₀ * (2 * (q.totient : ℝ)⁻¹ * (F₀ * A₀ * (3 * F₀ + 1) ^ K₀ *
              (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)) * (2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ)))) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) (mul_nonneg (by positivity) hX0)
          _ = _ := by ring
    _ = (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ) +
            a₂ * (q : ℝ) ^ (-1 : ℝ) + a₃ * (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)))) := by ring
    _ ≤ (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) * (q : ℝ) ^ (-δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (bracket_le hq1 ha₁0 ha₂0 ha₃0 hδ0 hδε hε₂1 hδe hcon) (mul_nonneg hA0 hqL)) hφinv0
    _ = (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (2333 / 1000 - δ : ℝ)) := by
        rw [mul_assoc A₀, ← Real.rpow_add hq0, sub_eq_add_neg]

end Asym

end SieveFamily
