import EisensteinDescent
import MellinUniform

/-! # The first Poisson summation of the transfer estimate (round 318)

S5c-2 in round 316's plan, its first part: the companion paper's Lemma 7.1 begins "Expand the square
defining `𝒜(W)`, and write `n_i=Cu_i`, where `C=(n_1,n_2)`", then applies Poisson summation in the rows
`k` and turns the Gauss sums around with (7.3), "`a_ξ(u_1)·conj(a_ξ(u_2))·γ(χ_{u_1}·conj(χ_{u_2})) =
μ(u_1)μ(u_2)(ξG)(u_1u_2^{−1})`". This file does these steps for one row `f`.

* **The dual paired identity** (`pairSum_poisson_dual`): round 307's `pairSum_poisson` multiplied by
  `μ(A₁)μ(A₂)·a(C₁)ā(C₂)`. Since `|a(C)| = 1` (`aF_mul_conj`), the factor `ā(C₁)a(C₂)Ψ(C₁, C₂)` becomes
  `μ(C₁)μ(C₂)Ψ(C₁, C₂)` (`pairPsiDual`).
* **The coefficient of a pair** (`alpha_pair`): with `B = A₁∩A₂`, `a_ξ(A₁)χ_{A₁}(f)⁴·conj(…)` is
  `a(C₁)ā(C₂)` times `ξ(C₁)ξ̄(C₂)χ_{C₁}(b)⁴conj(χ_{C₂}(b)⁴)χ_{A₁}(f)⁴conj(χ_{A₂}(f)⁴)`, through round 306's
  `aXi_mul_left` and `|a_ξ(B)| = 1` (`aXi_idl_mul_conj`).
* **The smoothed mean square of any column family** (`majorant_expand`, in
  `EisensteinMeanSquarePoisson.lean` since round 332) as a double sum over pairs, and
  **`dualMS_poisson`**: the smoothed dual mean square of one row after Poisson summation.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### Unit factors -/

theorem aF_mul_conj (C : Finset Pr) : aF πP h6Pr C * conj (aF πP h6Pr C) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_aF πP h6Pr C (hcopPr _)]; simp

theorem norm_xi_cls4 (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (C : Finset Pr) :
    ‖ξ (cls4 C)‖ = 1 := by
  rw [← (isUnit_cls4 C).unit_spec]; exact norm_mulChar_unit ξ _

theorem aXi_idl_mul_conj (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (C : Finset Pr) :
    aXi ξ (idl C) * conj (aXi ξ (idl C)) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, aXi_idl, norm_mul,
    norm_aF πP h6Pr C (hcopPr _), norm_xi_cls4, one_mul]; simp

/-! ### The paired identity in the dual direction -/

/-- The dual paired factor `μ(C₁)μ(C₂)Ψ(C₁, C₂)`, the companion paper's `μ(u₁)μ(u₂)(ξG)(u₁u₂⁻¹)` of
(7.3) before its expansion in characters. -/
def pairPsiDual (C1 C2 : Finset Pr) : ℂ := (-1 : ℂ) ^ C1.card * (-1) ^ C2.card * pairPsi C1 C2

theorem norm_pairPsiDual (C1 C2 : Finset Pr) : ‖pairPsiDual C1 C2‖ = 1 := by
  unfold pairPsiDual
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_pow, one_mul,
    one_mul, norm_pairPsi]

open Classical in
/-- **Poisson summation for one pair of columns, in the dual direction** (the companion paper's
(7.3) in its first Poisson summation): `a(C₁)ā(C₂)·Σ_u χ_{A₁}(u)χ̄_{A₂}(u)·Φ(u/√H)` is
`Σ_{T⊆A₁∩A₂} (−1)^{|T|}·2H/(√3·√N(c)·N(d_T))·μ(C₁)μ(C₂)Ψ(C₁, C₂)·F(d_T)·Σ_μ F̄(μ)·Φ̂(…)`, with
`C₁ = A₁∖A₂`, `C₂ = A₂∖A₁`. It is round 307's `pairSum_poisson` multiplied by
`μ(A₁)μ(A₂)·a(C₁)ā(C₂)`, since `|a(C)| = 1`. -/
theorem pairSum_poisson_dual (H : ℝ) (hH : 0 < H) (A1 A2 : Finset Pr) :
    aF πP h6Pr (A1 \ A2) * conj (aF πP h6Pr (A2 \ A1)) *
      ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
    ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card *
      ((2 * H / (Real.sqrt 3 * Real.sqrt (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
        (absNorm (span {∏ P ∈ T, πP P}) : ℝ)) : ℝ) : ℂ) *
      pairPsiDual (A1 \ A2) (A2 \ A1) *
      (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
      ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
        dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
          (3 * (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
            (absNorm (span {∏ P ∈ T, πP P}) : ℝ)))) := by
  set s : ℂ := (-1 : ℂ) ^ A1.card * (-1) ^ A2.card with hs
  have hp1 : ((-1 : ℂ) ^ A1.card) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hp2 : ((-1 : ℂ) ^ A2.card) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hss : s * s = 1 := by
    rw [hs]; linear_combination ((-1 : ℂ) ^ A2.card) ^ 2 * hp1 + hp2
  have h := pairSum_poisson H hH A1 A2
  have ha1 := aF_mul_conj (A1 \ A2)
  have ha2 := aF_mul_conj (A2 \ A1)
  set S := ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))
  calc aF πP h6Pr (A1 \ A2) * conj (aF πP h6Pr (A2 \ A1)) * S
      = s * aF πP h6Pr (A1 \ A2) * conj (aF πP h6Pr (A2 \ A1)) * (s * S) := by
        linear_combination (-(aF πP h6Pr (A1 \ A2) * conj (aF πP h6Pr (A2 \ A1)) * S)) * hss
    _ = s * aF πP h6Pr (A1 \ A2) * conj (aF πP h6Pr (A2 \ A1)) * (s * S) := rfl
    _ = _ := by
        rw [h, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        unfold pairPsiDual
        rw [hs, sign_sdiff A1 A2]
        set X1 := (-1 : ℂ) ^ (A1 \ A2).card * (-1) ^ (A2 \ A1).card
        set a1 := aF πP h6Pr (A1 \ A2)
        set a2 := aF πP h6Pr (A2 \ A1)
        set R := (-1 : ℂ) ^ T.card *
          ((2 * H / (Real.sqrt 3 * Real.sqrt (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
            (absNorm (span {∏ P ∈ T, πP P}) : ℝ)) : ℝ) : ℂ)
        set Fd := chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))
        set Sμ := ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
          dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
            (3 * (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
              (absNorm (span {∏ P ∈ T, πP P}) : ℝ))))
        have hprod : a1 * conj a1 * (conj a2 * a2) = 1 := by
          rw [ha1, mul_comm (conj a2), ha2, one_mul]
        linear_combination (X1 * R * pairPsi (A1 \ A2) (A2 \ A1) * Fd * Sμ) * hprod

/-! ### The coefficient of a pair of columns -/

/-- **The coefficient of a pair of columns of the dual mean square**: with `B = A₁∩A₂`, `C₁ = A₁∖A₂`,
`C₂ = A₂∖A₁`, `a_ξ(A₁)χ_{A₁}(f)⁴·conj(a_ξ(A₂)χ_{A₂}(f)⁴)` is `a(C₁)ā(C₂)` times
`ξ(C₁)ξ̄(C₂)·χ_{C₁}(b)⁴·conj(χ_{C₂}(b)⁴)·χ_{A₁}(f)⁴·conj(χ_{A₂}(f)⁴)`, `b` the primary generator of `B`
(the paper's `a_ξ(Cu) = a_ξ(C)a_ξ(u)χ_u(C)⁴`). -/
theorem alpha_pair (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (f : 𝓞 K) (A1 A2 : Finset Pr) :
    aXi ξ (idl A1) * chiS A1 f ^ 4 * conj (aXi ξ (idl A2) * chiS A2 f ^ 4) =
      (ξ (cls4 (A1 \ A2)) * conj (ξ (cls4 (A2 \ A1))) * chiS (A1 \ A2) (eS (A1 ∩ A2)) ^ 4 *
        conj (chiS (A2 \ A1) (eS (A1 ∩ A2)) ^ 4) * chiS A1 f ^ 4 * conj (chiS A2 f ^ 4)) *
      (aF πP h6Pr (A1 \ A2) * conj (aF πP h6Pr (A2 \ A1))) := by
  have hd1 : Disjoint (A1 ∩ A2) (A1 \ A2) := Finset.disjoint_sdiff_inter A1 A2 |>.symm
  have hd2 : Disjoint (A1 ∩ A2) (A2 \ A1) := by
    rw [Finset.inter_comm]; exact (Finset.disjoint_sdiff_inter A2 A1).symm
  have e1 : A1 = (A1 ∩ A2) ∪ (A1 \ A2) := by rw [Finset.union_comm, Finset.sdiff_union_inter]
  have e2 : A2 = (A1 ∩ A2) ∪ (A2 \ A1) := by
    rw [Finset.inter_comm, Finset.union_comm, Finset.sdiff_union_inter]
  have hB := aXi_idl_mul_conj ξ (A1 ∩ A2)
  have hpg : pgen (idl (A1 ∩ A2)) = eS (A1 ∩ A2) := pgen_idl _
  have k1 : aXi ξ (idl A1) = aXi ξ (idl (A1 ∩ A2)) * (aF πP h6Pr (A1 \ A2) * ξ (cls4 (A1 \ A2))) *
      chiS (A1 \ A2) (eS (A1 ∩ A2)) ^ 4 := by
    conv_lhs => rw [e1]
    rw [idl_union hd1, aXi_mul_left ξ (idl_coprime6 _) (idl_squarefree _), hpg, sym6_idl,
      aXi_idl ξ (A1 \ A2)]
  have k2 : aXi ξ (idl A2) = aXi ξ (idl (A1 ∩ A2)) * (aF πP h6Pr (A2 \ A1) * ξ (cls4 (A2 \ A1))) *
      chiS (A2 \ A1) (eS (A1 ∩ A2)) ^ 4 := by
    conv_lhs => rw [e2]
    rw [idl_union hd2, aXi_mul_left ξ (idl_coprime6 _) (idl_squarefree _), hpg, sym6_idl,
      aXi_idl ξ (A2 \ A1)]
  rw [k1, k2]
  simp only [map_mul, map_pow]
  set b := aXi ξ (idl (A1 ∩ A2))
  linear_combination (aF πP h6Pr (A1 \ A2) * ξ (cls4 (A1 \ A2)) *
      chiS (A1 \ A2) (eS (A1 ∩ A2)) ^ 4 * chiS A1 f ^ 4 * conj (aF πP h6Pr (A2 \ A1)) *
      conj (ξ (cls4 (A2 \ A1))) * conj (chiS (A2 \ A1) (eS (A1 ∩ A2))) ^ 4 *
      conj (chiS A2 f) ^ 4) * hB

/-! ### The smoothed mean square of a column family -/

/-- The column sum of the dual mean square over the subsets of `U`. -/
theorem colSum_eq_powerset_one (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β' : ℝ}
    (hW : ∀ x, β' < x → W x = 0) {X : ℝ} (hX : 0 < X) {U : Finset Pr}
    (hU : primesLe (β' * X) ⊆ U) (k f : 𝓞 K) :
    colSum ξ W X 1 k f = ∑ M ∈ U.powerset, (aXi ξ (idl M) * chiS M f ^ 4 * W (nI M / X)) *
      chiS M k := by
  have h := colSum_eq_powerset ξ hW hX (b := ∅) hU k f
  have hidl : idl (∅ : Finset Pr) = 1 := by unfold idl; rw [Finset.prod_empty]
  rw [hidl, Finset.sdiff_empty] at h
  rw [h]
  refine Finset.sum_congr rfl fun M _ => ?_
  unfold colA; ring

open Classical in
/-- **The smoothed dual mean square after Poisson summation, one row `f`** (the first step of the
companion paper's proof of its Lemma 7.1): `Σ_u |Σ_n a_ξ(n)(u/n)₆(f/n)₆⁴W(N(n)/X)|²·Φ(u/√H)` is
`Σ_{A₁,A₂⊆U}` of the pair coefficient of `alpha_pair` times the dual Poisson identity
`pairSum_poisson_dual`. -/
theorem dualMS_poisson (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β' : ℝ}
    (hW : ∀ x, β' < x → W x = 0) {X : ℝ} (hX : 0 < X) {U : Finset Pr}
    (hU : primesLe (β' * X) ⊆ U) (f : 𝓞 K) (H : ℝ) (hH : 0 < H) :
    ∑' u : 𝓞 K, colSum ξ W X 1 u f * conj (colSum ξ W X 1 u f) *
        Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ A1 ∈ U.powerset, ∑ A2 ∈ U.powerset,
        (ξ (cls4 (A1 \ A2)) * conj (ξ (cls4 (A2 \ A1))) * chiS (A1 \ A2) (eS (A1 ∩ A2)) ^ 4 *
          conj (chiS (A2 \ A1) (eS (A1 ∩ A2)) ^ 4) * chiS A1 f ^ 4 * conj (chiS A2 f ^ 4) *
          (W (nI A1 / X) * conj (W (nI A2 / X)))) *
        ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card *
          ((2 * H / (Real.sqrt 3 * Real.sqrt (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
            (absNorm (span {∏ P ∈ T, πP P}) : ℝ)) : ℝ) : ℂ) *
          pairPsiDual (A1 \ A2) (A2 \ A1) *
          (chiS (A1 \ A2) (∏ P ∈ T, πP P) * conj (chiS (A2 \ A1) (∏ P ∈ T, πP P))) *
          ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
            dualG (Real.sqrt (4 * H * (absNorm (span {μ}) : ℝ) /
              (3 * (absNorm (span {∏ P ∈ A1 \ A2 ∪ A2 \ A1, πP P}) : ℝ) *
                (absNorm (span {∏ P ∈ T, πP P}) : ℝ)))) := by
  have hcol : ∀ u : 𝓞 K, colSum ξ W X 1 u f =
      ∑ M ∈ U.powerset, (aXi ξ (idl M) * chiS M f ^ 4 * W (nI M / X)) * chiS M u :=
    fun u => colSum_eq_powerset_one ξ hW hX hU u f
  simp_rw [hcol]
  rw [majorant_expand H hH U.powerset]
  refine Finset.sum_congr rfl fun A1 _ => Finset.sum_congr rfl fun A2 _ => ?_
  rw [← pairSum_poisson_dual H hH A1 A2]
  have hal := alpha_pair ξ f A1 A2
  calc aXi ξ (idl A1) * chiS A1 f ^ 4 * W (nI A1 / X) *
        conj (aXi ξ (idl A2) * chiS A2 f ^ 4 * W (nI A2 / X)) *
        ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ))
      = (aXi ξ (idl A1) * chiS A1 f ^ 4 * conj (aXi ξ (idl A2) * chiS A2 f ^ 4)) *
          (W (nI A1 / X) * conj (W (nI A2 / X))) *
          ∑' u : 𝓞 K, chiS A1 u * conj (chiS A2 u) * Majorant.Phi (σO u / (Real.sqrt H : ℂ)) := by
        rw [map_mul (starRingEnd ℂ) (aXi ξ (idl A2) * chiS A2 f ^ 4)]; ring
    _ = _ := by rw [hal]; ring

end Eis

end

#print axioms Eis.aF_mul_conj
#print axioms Eis.norm_xi_cls4
#print axioms Eis.aXi_idl_mul_conj
#print axioms Eis.norm_pairPsiDual
#print axioms Eis.pairSum_poisson_dual
#print axioms Eis.alpha_pair
#print axioms Eis.colSum_eq_powerset_one
#print axioms Eis.dualMS_poisson
