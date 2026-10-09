import EisensteinFirstTransfer

/-! # The companion paper's Lemma 7.2, the second Poisson summation (round 321)

S5c-4 in round 316's plan. The companion paper: "The second Poisson summation turns the Möbius
coefficients back into cubic Gauss-sum coefficients." Its Lemma 7.2 is an identity for
`𝓜 = Σ_y Φ(N(y)/Y)|P(y)|²`, the inner sum of round 320's `𝒬`. Its proof expands the square, applies
Poisson summation in `y`, turns the Gauss sums around and inserts Möbius for `(z_1, z_2) = 1`
through `w`. This is round 308's direction (Möbius columns to Gauss-sum columns), with the columns
twisted by `ξ₁(n)χ_n(c)`, `c = C⁴d·t⁶`, and complex test functions.

* **The twisted paired factor** (`pairTerm_expandTw`) and **the split** (`pair_char_formTw`).
* **The expansion** (`conj_Pcol`, `Mq_expand`, `alphaQ_pair`).
* **The column factorization** (`UU_kapC`, `rcQ`, `term_factorQ`) and **the chain** (`xi_chainQ`).
* **`Mq_rowcol`**: `𝓜` in row/column form; **`zero_Mq_le`**: its zero frequency.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The paired factor with the twist of the Möbius columns -/

/-- **The pair coefficients with the twist `ξ̄₁(C₁)ξ₁(C₂)`** (the companion paper's
"`μ(z_1)μ(z_2)ξ_1(z_1)·conj(ξ_1(z_2))·γ(conj(χ_{z_1})χ_{z_2}) =Σ_{ξ'}c_{ξ'}a_{ξ'}(z_1)·conj(a_{ξ'}(z_2))`",
in round 308's orientation): for disjoint `C₁, C₂`,
`ξ̄₁(C₁)ξ₁(C₂)·ā(C₁)a(C₂)Ψ(C₁, C₂) = Σ_{ξ_a,ξ_b} ĉ(ξ_a⁻¹, ξ_b)·ā_{ξ_a}(C₁)a_{ξ_b}(C₂)`, with `ĉ` the
coefficients of `pairPsiXi ξ₁⁻¹`. -/
theorem pairTerm_expandTw (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {C1 C2 : Finset Pr}
    (hd : Disjoint C1 C2) :
    conj (ξ1 (cls4 C1)) * ξ1 (cls4 C2) *
        (conj (aF πP h6Pr C1) * aF πP h6Pr C2 * pairPsi C1 C2) =
      ∑ ξa : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff (pairPsiXi ξ1⁻¹) ξa⁻¹ ξb * (conj (aXi ξa (idl C1)) * aXi ξb (idl C2)) := by
  set x := (isUnit_cls4 C1).unit
  set y := (isUnit_cls4 C2).unit
  have hx : (x : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C1 := IsUnit.unit_spec _
  have hy : (y : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C2 := IsUnit.unit_spec _
  have hexp := pair_eq_sum_mulChar (pairPsiXi ξ1⁻¹) x y
  rw [hx, hy] at hexp
  have h1 : conj (ξ1 (cls4 C1)) = ξ1⁻¹ (cls4 C1) := conj_xi_cls4 ξ1 C1
  have h2 : ξ1 (cls4 C2) = conj (ξ1⁻¹ (cls4 C2)) := by rw [conj_xi_cls4, inv_inv]
  have hP : conj (ξ1 (cls4 C1)) * ξ1 (cls4 C2) *
      (conj (aF πP h6Pr C1) * aF πP h6Pr C2 * pairPsi C1 C2) =
      conj (aF πP h6Pr C1) * aF πP h6Pr C2 * pairPsiXi ξ1⁻¹ (cls4 C1) (cls4 C2) := by
    rw [h1, h2]
    unfold pairPsiXi
    rw [pairPsi_eq_cls hd]
    ring
  rw [hP, hexp, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.inv (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ))]
  refine Finset.sum_congr rfl fun ξa _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξb _ => ?_
  have hc : (ξa⁻¹ : MulChar _ ℂ) (cls4 C1) = conj (ξa (cls4 C1)) := (conj_xi_cls4 ξa C1).symm
  simp only [Equiv.inv_apply]
  rw [aXi_idl, aXi_idl, map_mul, hc]
  ring

open Classical in
/-- **One pair of twisted Möbius columns after Poisson summation, in characters modulo `4`**
(round 308's `pair_char_form` with the twist `ξ̄₁(C₁)ξ₁(C₂)`): for `N(A₁), N(A₂) ≤ M` and
`3R²M² ≤ 4HY`, the pair's sum is the zero frequency, present only for `A₁ = A₂`, plus
`Σ_{ξ_a,ξ_b} ĉ(ξ_a⁻¹, ξ_b)·Σ_{T⊆A₁∩A₂} τ_{ξ_aξ_b}(A₁∖A₂, A₂∖A₁, T)` over the nonzero frequencies of norm
at most `Y`. -/
theorem pair_char_formTw (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (H : ℝ) (hH : 0 < H)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {M Y : ℝ}
    (hY : 3 * R ^ 2 * M ^ 2 ≤ 4 * H * Y) {A1 A2 : Finset Pr} (h1 : nI A1 ≤ M) (h2 : nI A2 ≤ M) :
    conj (ξ1 (cls4 (A1 \ A2))) * ξ1 (cls4 (A2 \ A1)) *
      ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card *
        ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))) =
    (if A1 = A2 then ∑ T ∈ A1.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
      ∑ ξa : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff (pairPsiXi ξ1⁻¹) ξa⁻¹ ξb *
          ∑ T ∈ (A1 ∩ A2).powerset, tauXi H ((eltsLe Y).erase 0) ξa ξb (A1 \ A2) (A2 \ A1) T := by
  rw [pairSum_clean H hH A1 A2, Finset.mul_sum]
  have hd : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  have hM0 : 0 ≤ M := le_trans zero_le_one ((one_le_nI A1).trans h1)
  have hsplit : ∀ T ∈ (A1 ∩ A2).powerset,
      conj (ξ1 (cls4 (A1 \ A2))) * ξ1 (cls4 (A2 \ A1)) *
        ((-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) *
          (conj (aF πP h6Pr (A1 \ A2)) * aF πP h6Pr (A2 \ A1) * pairPsi (A1 \ A2) (A2 \ A1)) *
          (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
          ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
            dualW H (A1 \ A2) (A2 \ A1) T μ) =
      (if A1 = A2 then (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
        ∑ ξa : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff (pairPsiXi ξ1⁻¹) ξa⁻¹ ξb *
            tauXi H ((eltsLe Y).erase 0) ξa ξb (A1 \ A2) (A2 \ A1) T := by
    intro T hT
    have hTs : T ⊆ A1 ∩ A2 := Finset.mem_powerset.1 hT
    have hYT : 3 * R ^ 2 * (nI (A1 \ A2) * nI (A2 \ A1) * nI T) ≤ 4 * H * Y := by
      have hle := nI_pair_le hTs
      have hMM : nI A1 * nI A2 ≤ M ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (le_trans zero_le_one (one_le_nI A2)) hM0
      nlinarith [sq_nonneg R]
    rw [tsum_mu_eq H hH hR0 hR _ _ _ hYT, mul_add, mul_add]
    congr 1
    · by_cases he : A1 = A2
      · have he' := sdiff_eq_empty_both.2 he
        rw [ite_eq_left he, ite_eq_left he', he'.1, he'.2]
        simp only [cls4_empty, map_one, aF_empty, pairPsi_empty, chiS_empty]
        ring
      · have hn : ¬(A1 \ A2 = ∅ ∧ A2 \ A1 = ∅) := fun h => he (sdiff_eq_empty_both.1 h)
        rw [ite_eq_right he, ite_eq_right hn, mul_zero, mul_zero]
    · have e : ∀ (x y s k P F S : ℂ), x * y * (s * k * P * F * S) = (x * y * P) * (s * k * F * S) :=
        fun x y s k P F S => by ring
      rw [e, pairTerm_expandTw ξ1 hd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ξa _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun ξb _ => ?_
      unfold tauXi eS
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · split_ifs with he
    · subst he; rw [Finset.inter_self]
    · exact Finset.sum_eq_zero fun T _ => rfl
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξa _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξb _ => ?_
    rw [Finset.mul_sum]

/-! ### The conjugated column sum and its expansion -/

/-- The coefficient `conj(μ(M)ξ₁(M)χ_M(c)·U(N(M)/ℓ))` of the conjugated column sum. -/
def alphaQ (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ) (ℓ : ℝ) (c : 𝓞 K)
    (M : Finset Pr) : ℂ :=
  conj ((-1 : ℂ) ^ M.card * ξ1 (cls4 M) * chiS M c * U (nI M / ℓ))

theorem conj_Pcol (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ) (β L : ℝ)
    (b T V : Finset Pr) (y : 𝓞 K) :
    conj (Pcol ξ1 U β L b T V y) = ∑ M ∈ fsLe (2 * β * ellS L b T V),
      alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * chiS M y := by
  unfold Pcol
  rw [map_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  unfold alphaQ colP
  simp only [map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
  ring

/-- **The expansion of the second mean square** (the companion paper's "Expand the square"):
`𝓜 = Σ_y Φ(N(y)/Y)|P(y)|²` is `Σ_{A₁,A₂} α(A₁)ᾱ(A₂)·Σ_u χ_{A₁}(u)χ̄_{A₂}(u)·Φ(u/√Y)` with `α = alphaQ`. -/
theorem Mq_expand (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ) (β L : ℝ)
    (b T V : Finset Pr) {Y : ℝ} (hY : 0 < Y) :
    ∑' y : 𝓞 K, Pcol ξ1 U β L b T V y * conj (Pcol ξ1 U β L b T V y) *
        Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) =
      ∑ A1 ∈ fsLe (2 * β * ellS L b T V), ∑ A2 ∈ fsLe (2 * β * ellS L b T V),
        alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) A1 *
          conj (alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) A2) *
          ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt Y : ℂ)) := by
  have hQ : ∀ y : 𝓞 K, Pcol ξ1 U β L b T V y * conj (Pcol ξ1 U β L b T V y) *
      Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) =
      (∑ M ∈ fsLe (2 * β * ellS L b T V),
          alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * chiS M y) *
        conj (∑ M ∈ fsLe (2 * β * ellS L b T V),
          alphaQ ξ1 U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M * chiS M y) *
        Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) := fun y => by
    rw [← conj_Pcol, Complex.conj_conj]; ring
  rw [tsum_congr hQ]
  exact majorant_expand Y hY _ _

/-- The weight of a pair of twisted Möbius columns, apart from the characters modulo `4` and the
signs: `χ̄_{A₁}(c)χ_{A₂}(c)·Ū(N(A₁)/ℓ)U(N(A₂)/ℓ)`. -/
def wQ (U : ℝ → ℂ) (ℓ : ℝ) (c : 𝓞 K) (A1 A2 : Finset Pr) : ℂ :=
  conj (chiS A1 c) * chiS A2 c * (conj (U (nI A1 / ℓ)) * U (nI A2 / ℓ))

/-- **The coefficient of a pair of twisted Möbius columns**: `α(A₁)ᾱ(A₂)` is the weight `wQ` times
the signs and `ξ̄₁(A₁∖A₂)ξ₁(A₂∖A₁)` (the characters at `A₁∩A₂` cancel). -/
theorem alphaQ_pair (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : ℝ → ℂ) (ℓ : ℝ) (c : 𝓞 K)
    (A1 A2 : Finset Pr) :
    alphaQ ξ1 U ℓ c A1 * conj (alphaQ ξ1 U ℓ c A2) =
      wQ U ℓ c A1 A2 * (conj (ξ1 (cls4 (A1 \ A2))) * ξ1 (cls4 (A2 \ A1)) *
        ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card)) := by
  have hd1 : Disjoint (A1 ∩ A2) (A1 \ A2) := (Finset.disjoint_sdiff_inter A1 A2).symm
  have hd2 : Disjoint (A1 ∩ A2) (A2 \ A1) := by
    rw [Finset.inter_comm]; exact (Finset.disjoint_sdiff_inter A2 A1).symm
  have e1 : A1 = (A1 ∩ A2) ∪ (A1 \ A2) := by rw [Finset.union_comm, Finset.sdiff_union_inter]
  have e2 : A2 = (A1 ∩ A2) ∪ (A2 \ A1) := by
    rw [Finset.inter_comm, Finset.union_comm, Finset.sdiff_union_inter]
  have k1 : ξ1 (cls4 A1) = ξ1 (cls4 (A1 ∩ A2)) * ξ1 (cls4 (A1 \ A2)) := by
    conv_lhs => rw [e1]
    rw [cls4_union hd1, map_mul]
  have k2 : ξ1 (cls4 A2) = ξ1 (cls4 (A1 ∩ A2)) * ξ1 (cls4 (A2 \ A1)) := by
    conv_lhs => rw [e2]
    rw [cls4_union hd2, map_mul]
  have hB : ξ1 (cls4 (A1 ∩ A2)) * conj (ξ1 (cls4 (A1 ∩ A2))) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_xi_cls4]; simp
  unfold alphaQ wQ
  simp only [map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
  rw [k1, k2]
  simp only [map_mul]
  linear_combination ((-1 : ℂ) ^ A1.card * (-1) ^ A2.card * conj (ξ1 (cls4 (A1 \ A2))) *
    ξ1 (cls4 (A2 \ A1)) * conj (chiS A1 c) * chiS A2 c * conj (U (nI A1 / ℓ)) *
    U (nI A2 / ℓ)) * hB

/-- **The weights after the change of variables, conjugate on the first column**:
`Ū(N(bTVm₁)/ℓ)·U(N(bTVm₂)/ℓ)·2H/(√3·√(N(Vm₁)N(Vm₂))·N(T)) = 2H·N(b)/(√3·ℓ)·Ū₀(…m₁…)·U₀(…m₂…)`. -/
theorem UU_kapC (U : ℝ → ℂ) {ℓ H nb nT nV n1 n2 : ℝ} (hℓ : 0 < ℓ) (hb : 0 < nb) (hT : 0 < nT)
    (hV : 0 < nV) (h1 : 0 < n1) (h2 : 0 < n2) :
    conj (U (nb * nT * (nV * n1) / ℓ)) * U (nb * nT * (nV * n2) / ℓ) *
        ((2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT) : ℝ) : ℂ) =
      ((2 * H * nb / (Real.sqrt 3 * ℓ) : ℝ) : ℂ) *
        (conj (MellinSep.W0c U (nb * nT * nV * n1 / ℓ)) * MellinSep.W0c U (nb * nT * nV * n2 / ℓ)) := by
  have h := WW_kapC U (H := H) hℓ hb hT hV h2 h1
  rw [show nV * n2 * (nV * n1) = nV * n1 * (nV * n2) by ring] at h
  calc conj (U (nb * nT * (nV * n1) / ℓ)) * U (nb * nT * (nV * n2) / ℓ) *
        ((2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT) : ℝ) : ℂ)
      = U (nb * nT * (nV * n2) / ℓ) * conj (U (nb * nT * (nV * n1) / ℓ)) *
        ((2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT) : ℝ) : ℂ) := by ring
    _ = _ := by rw [h]; ring

/-- The term of the second dual sum at `(b, T, V, μ, M₁, M₂)` (the companion paper's `g = b ∪ T`,
`e = T`, `w = V`, `h = μ` and `n_i = M_i` in its proof of Lemma 7.2): the sign, the row factor
`ā_{ξ_a}(V)a_{ξ_b}(V)|χ_V(μ)|²` with the twist `|χ_{bT}(c)|²|χ_V(c)|²`, the normalization
`2H·N(b)/(√3·ℓ)`, the two columns `colA·χ(c)`, the weights `U₀` and the dual weight. -/
def rcQ (U : ℝ → ℂ) (ℓ H : ℝ) (c : 𝓞 K) (ξa ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (b T V : Finset Pr) (μ : 𝓞 K) (M1 M2 : Finset Pr) : ℂ :=
  ((-1 : ℂ) ^ T.card * (-1) ^ V.card) *
    (conj (aXi ξa (idl V)) * aXi ξb (idl V) * (chiS V μ * conj (chiS V μ)) *
      ((conj (chiS (b ∪ T) c) * chiS (b ∪ T) c) * (conj (chiS V c) * chiS V c))) *
    ((2 * H * nI b / (Real.sqrt 3 * ℓ) : ℝ) : ℂ) *
    (conj (colA ξa (eS T * μ) (eS T * eS V) M1 * chiS M1 c) *
      (colA ξb (eS T * μ) (eS T * eS V) M2 * chiS M2 c)) *
    (conj (MellinSep.W0c U (nI b * nI T * nI V * nI M1 / ℓ)) *
      MellinSep.W0c U (nI b * nI T * nI V * nI M2 / ℓ)) *
    dualW H (V ∪ M1) (V ∪ M2) T μ

/-- **One term of the second Möbius-expanded sum in row/column form** (round 308's `term_factor`
with complex weights and the twist `χ̄_{A₁}(c)χ_{A₂}(c)`). -/
theorem term_factorQ (U : ℝ → ℂ) {ℓ H : ℝ} (hℓ : 0 < ℓ) (c : 𝓞 K)
    (ξa ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (E : Finset (𝓞 K)) {b T V M1 M2 : Finset Pr}
    (hbT : Disjoint b T) (hbV : Disjoint b V) (hb1 : Disjoint b M1) (hb2 : Disjoint b M2)
    (hTV : Disjoint T V) (hT1 : Disjoint T M1) (hT2 : Disjoint T M2) (hV1 : Disjoint V M1)
    (hV2 : Disjoint V M2) :
    (-1 : ℂ) ^ V.card * (wQ U ℓ c ((b ∪ T) ∪ (V ∪ M1)) ((b ∪ T) ∪ (V ∪ M2)) *
        tauXi H E ξa ξb (V ∪ M1) (V ∪ M2) T) =
      ∑ μ ∈ E, rcQ U ℓ H c ξa ξb b T V μ M1 M2 := by
  have hd1 : Disjoint (b ∪ T) (V ∪ M1) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb1⟩, hTV, hT1⟩
  have hd2 : Disjoint (b ∪ T) (V ∪ M2) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb2⟩, hTV, hT2⟩
  have hn1 : nI ((b ∪ T) ∪ (V ∪ M1)) = nI b * nI T * (nI V * nI M1) := by
    rw [nI_union hd1, nI_union hbT, nI_union hV1]
  have hn2 : nI ((b ∪ T) ∪ (V ∪ M2)) = nI b * nI T * (nI V * nI M2) := by
    rw [nI_union hd2, nI_union hbT, nI_union hV2]
  have hk : kap H (V ∪ M1) (V ∪ M2) T =
      2 * H / (Real.sqrt 3 * Real.sqrt (nI V * nI M1 * (nI V * nI M2)) * nI T) := by
    unfold kap; rw [nI_union hV1, nI_union hV2]
  have hUK : conj (U (nI ((b ∪ T) ∪ (V ∪ M1)) / ℓ)) * U (nI ((b ∪ T) ∪ (V ∪ M2)) / ℓ) *
      ((kap H (V ∪ M1) (V ∪ M2) T : ℝ) : ℂ) =
      ((2 * H * nI b / (Real.sqrt 3 * ℓ) : ℝ) : ℂ) *
        (conj (MellinSep.W0c U (nI b * nI T * nI V * nI M1 / ℓ)) *
          MellinSep.W0c U (nI b * nI T * nI V * nI M2 / ℓ)) := by
    rw [hn1, hn2, hk]
    exact UU_kapC U hℓ (nI_pos b) (nI_pos T) (nI_pos V) (nI_pos M1) (nI_pos M2)
  unfold tauXi
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hcf := col_factor ξa ξb hTV.symm hT1.symm hT2.symm hV1 hV2 μ
  unfold wQ rcQ
  rw [chiS_union hd1 c, chiS_union hd2 c, chiS_union hV1 c, chiS_union hV2 c]
  calc _ = ((-1 : ℂ) ^ T.card * (-1) ^ V.card) *
        ((conj (chiS (b ∪ T) c) * chiS (b ∪ T) c) * (conj (chiS V c) * chiS V c)) *
        (conj (U (nI ((b ∪ T) ∪ (V ∪ M1)) / ℓ)) * U (nI ((b ∪ T) ∪ (V ∪ M2)) / ℓ) *
          ((kap H (V ∪ M1) (V ∪ M2) T : ℝ) : ℂ)) *
        (conj (aXi ξa (idl (V ∪ M1))) * aXi ξb (idl (V ∪ M2)) *
          (chiS (V ∪ M1) (eS T) * conj (chiS (V ∪ M2) (eS T))) *
          conj (chiS (V ∪ M1) μ * conj (chiS (V ∪ M2) μ))) *
        (conj (chiS M1 c) * chiS M2 c) * dualW H (V ∪ M1) (V ∪ M2) T μ := by
        simp only [map_mul]; ring
    _ = _ := by rw [hUK, hcf]; simp only [map_mul]; ring

/-- **The chain for one pair of characters, second direction** (round 308's `xi_chain` with the
weight `wQ`): `sum_pair_chain` with the factorization `term_factorQ`. -/
theorem xi_chainQ (U : ℝ → ℂ) {ℓ H : ℝ} (hℓ : 0 < ℓ) (c : 𝓞 K) (E : Finset (𝓞 K))
    (ξa ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U0 : Finset Pr) (𝒜 : Finset (Finset Pr))
    (h𝒜 : ∀ A ∈ 𝒜, A ⊆ U0) (hvan : ∀ A ⊆ U0, A ∉ 𝒜 → U (nI A / ℓ) = 0) :
    ∑ A1 ∈ 𝒜, ∑ A2 ∈ 𝒜, wQ U ℓ c A1 A2 *
        ∑ T ∈ (A1 ∩ A2).powerset, tauXi H E ξa ξb (A1 \ A2) (A2 \ A1) T =
      ∑ b ∈ U0.powerset, ∑ T ∈ (U0 \ b).powerset, ∑ V ∈ (U0 \ (b ∪ T)).powerset, ∑ μ ∈ E,
        ∑ M1 ∈ ((U0 \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U0 \ (b ∪ T)) \ V).powerset,
          rcQ U ℓ H c ξa ξb b T V μ M1 M2 := by
  rw [sum_family_eq_powerset U0 𝒜 h𝒜 _ (fun A1 h1 A2 h2 h => by
    rcases h with h | h
    · unfold wQ; rw [hvan A1 h1 h]; simp
    · unfold wQ; rw [hvan A2 h2 h]; simp)]
  exact sum_pair_chain U0 (wQ U ℓ c) (fun B C1 C2 => wQ U ℓ c (B ∪ C1) (B ∪ C2)) (fun _ _ _ => rfl)
    (tauXi H E ξa ξb) E (rcQ U ℓ H c ξa ξb)
    (fun hbT hbV hb1 hb2 hTV hT1 hT2 hV1 hV2 =>
      term_factorQ U hℓ c ξa ξb E hbT hbV hb1 hb2 hTV hT1 hT2 hV1 hV2)

open Classical in
/-- **The second mean square in row/column form** (the companion paper's Lemma 7.2 before its
regrouping, for one `(C, d, t)` and each pair of characters modulo `4`): with `U` vanishing beyond
`2β`, `U₀` containing the primes of norm at most `2βℓ`, `Φ̂` vanishing beyond `R` and
`3R²(2βℓ)² ≤ 4YY₂`, the smoothed mean square `𝓜 = Σ_y Φ(N(y)/Y)|P_{C,d,t}(y; U)|²` is the zero
frequency `Σ_A |χ_A(c)|²|U(N(A)/ℓ)|²·Σ_{T⊆A}(−1)^{|T|}·2Y/(√3·N(T))·Φ̂(0)` plus
`Σ_{ξ_a,ξ_b} ĉ(ξ_a⁻¹, ξ_b)·Σ_{b, T, V, μ, M₁, M₂} rcQ` over `b ⊆ U₀`, `T ⊆ U₀∖b`, `V ⊆ U₀∖(b∪T)`, the nonzero
`μ` of norm at most `Y₂` and `M₁, M₂ ⊆ U₀∖(b∪T)∖V`. -/
theorem Mq_rowcol (ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U : ℝ → ℂ} {β L : ℝ} (hβ : 0 ≤ β)
    (hL : 0 < L) (hU : ∀ x, 2 * β < x → U x = 0) (b T V : Finset Pr) {Y : ℝ} (hY : 0 < Y)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {Y2 : ℝ}
    (hY2 : 3 * R ^ 2 * (2 * β * ellS L b T V) ^ 2 ≤ 4 * Y * Y2) {U0 : Finset Pr}
    (hU0 : primesLe (2 * β * ellS L b T V) ⊆ U0) :
    ∑' y : 𝓞 K, Pcol ξ1 U β L b T V y * conj (Pcol ξ1 U β L b T V y) *
        Majorant.Phi (σO y / (Real.sqrt Y : ℂ)) =
      ∑ A ∈ fsLe (2 * β * ellS L b T V),
          wQ U (ellS L b T V) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) A A *
            ∑ T2 ∈ A.powerset, (-1 : ℂ) ^ T2.card * (kap Y ∅ ∅ T2 : ℂ) * dualG 0 +
        ∑ ξa : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff (pairPsiXi ξ1⁻¹) ξa⁻¹ ξb *
            ∑ b2 ∈ U0.powerset, ∑ T2 ∈ (U0 \ b2).powerset, ∑ V2 ∈ (U0 \ (b2 ∪ T2)).powerset,
              ∑ μ ∈ (eltsLe Y2).erase 0,
                ∑ M1 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset, ∑ M2 ∈ ((U0 \ (b2 ∪ T2)) \ V2).powerset,
                  rcQ U (ellS L b T V) Y (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) ξa ξb b2 T2 V2 μ M1 M2 := by
  set ℓ := ellS L b T V with hℓdef
  set c := eS b ^ 4 * eS T ^ 5 * eS V ^ 6 with hcdef
  set 𝒜 := fsLe (2 * β * ℓ) with h𝒜def
  have hℓ : 0 < ℓ := ellS_pos hL b T V
  have hΛ : 0 ≤ 2 * β * ℓ := by positivity
  rw [Mq_expand ξ1 U β L b T V hY]
  have hpair : ∀ A1 ∈ 𝒜, ∀ A2 ∈ 𝒜,
      alphaQ ξ1 U ℓ c A1 * conj (alphaQ ξ1 U ℓ c A2) *
        ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt Y : ℂ)) =
      (if A1 = A2 then wQ U ℓ c A1 A1 *
          ∑ T2 ∈ A1.powerset, (-1 : ℂ) ^ T2.card * (kap Y ∅ ∅ T2 : ℂ) * dualG 0 else 0) +
        ∑ ξa : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξb : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff (pairPsiXi ξ1⁻¹) ξa⁻¹ ξb *
            (wQ U ℓ c A1 A2 * ∑ T2 ∈ (A1 ∩ A2).powerset,
              tauXi Y ((eltsLe Y2).erase 0) ξa ξb (A1 \ A2) (A2 \ A1) T2) := by
    intro A1 hA1 A2 hA2
    rw [alphaQ_pair]
    have e : ∀ (w x s S : ℂ), w * (x * s) * S = w * (x * (s * S)) := fun w x s S => by ring
    rw [e, pair_char_formTw ξ1 Y hY hR0 hR hY2 (nI_le_of_mem_fsLe_real hΛ hA1)
      (nI_le_of_mem_fsLe_real hΛ hA2), mul_add]
    congr 1
    · split_ifs with he
      · subst he; rfl
      · rw [mul_zero]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξa _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξb _ => ?_
      ring
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => hpair A1 hA1 A2 hA2]
  simp only [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun A1 hA1 => ?_
    rw [Finset.sum_ite_eq, ite_eq_left hA1]
  · rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξa _ => ?_
    rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξb _ => ?_
    simp_rw [← Finset.mul_sum]
    congr 1
    refine xi_chainQ U hℓ c _ ξa ξb U0 𝒜 (fun A hA => (subset_primesLe hA).trans hU0) ?_
    intro A _ hA
    refine hU _ ?_
    have := lt_nI_of_not_mem_fsLe hA
    rw [lt_div_iff₀ hℓ]; linarith

theorem card_fsLe_le_max (Λ : ℝ) : ((fsLe Λ).card : ℝ) ≤ (2 * kappa + 5) * max Λ 1 := by
  calc ((fsLe Λ).card : ℝ) ≤ (fsLe (max Λ 1)).card := by
        exact_mod_cast Finset.card_le_card (fsLe_mono (le_max_left Λ 1))
    _ ≤ (2 * kappa + 5) * max Λ 1 := card_fsLe_le (le_max_right Λ 1)

/-- **The zero frequency of the second mean square** (the companion paper's "`|Z|≪_{I_*,Φ}Yℓ‖U‖_∞^2`"
of its Lemma 7.2): with `|U| ≤ N_U`, the zero frequency of `Mq_rowcol` over a family `𝒜` has norm at
most `#𝒜·N_U²·2Y/√3·|Φ̂(0)|`; for `𝒜 = fsLe (2βℓ)`, `#𝒜 ≤ (2κ+5)·max(2βℓ, 1)` (`card_fsLe_le_max`). -/
theorem zero_Mq_le {U : ℝ → ℂ} {NU : ℝ} (hNU : ∀ x, ‖U x‖ ≤ NU) (ℓ : ℝ) (c : 𝓞 K) {Y : ℝ}
    (hY : 0 ≤ Y) (𝒜 : Finset (Finset Pr)) :
    ‖∑ A ∈ 𝒜, wQ U ℓ c A A *
        ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap Y ∅ ∅ T : ℂ) * dualG 0‖ ≤
      𝒜.card * (NU ^ 2 * (2 * Y / Real.sqrt 3 * ‖dualG 0‖)) := by
  have hNU0 : 0 ≤ NU := (norm_nonneg _).trans (hNU 0)
  refine norm_zeroSum_le hY 𝒜 _ fun A _ => ?_
  unfold wQ
  rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, sq]
  have := norm_chiS_le A c
  calc ‖chiS A c‖ * ‖chiS A c‖ * (‖U (nI A / ℓ)‖ * ‖U (nI A / ℓ)‖) ≤ 1 * 1 * (NU * NU) := by
        gcongr <;> first | exact this | exact hNU _
    _ = NU * NU := by ring

end Eis

end

#print axioms Eis.pairTerm_expandTw
#print axioms Eis.pair_char_formTw
#print axioms Eis.conj_Pcol
#print axioms Eis.Mq_expand
#print axioms Eis.alphaQ_pair
#print axioms Eis.UU_kapC
#print axioms Eis.term_factorQ
#print axioms Eis.xi_chainQ
#print axioms Eis.Mq_rowcol
#print axioms Eis.card_fsLe_le_max
#print axioms Eis.zero_Mq_le
