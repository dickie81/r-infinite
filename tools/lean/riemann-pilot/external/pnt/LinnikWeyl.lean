/-
# Round 612: the integral class is empty under a pointwise bound on the critical line

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If every `L(½ + it, χ)`, `χ` mod `q`, has `|L(½ + it, χ)| ≤ CL (q(1 + |t|))^{1/6+ε}` with `0 ≤ ε ≤ 1`,
then the integral class of round 521's detector (`LinnikDetect.dichotomy`) is empty as soon as
`2 KG CL X (q(T + 2))^{1/6+ε} < δ Y^{σ−½}` (`class2_empty`): no character `χ ≠ 1` with a zero `ρ = β + iγ` of `L(·, χ)`,
`σ ≤ β < 1`, `|γ| ≤ T`, has `|I_χ(ρ)| ≥ ¼`, where `½ + δ ≤ σ`, `X ≥ 1`, `Y ≥ 1` and `T ≥ 0`. `PYWeyl` states
Petrow–Young's Weyl bound for every character as a hypothesis; `class2_empty` takes the bound at one `ε` with its
constant `CL`.

* `PYWeyl`: for every `ε > 0` there is `C ≥ 0` with `|L(½ + it, χ)| ≤ C (q(1 + |t|))^{1/6+ε}` for every `q ≥ 1`, every
  `χ` mod `q` and every real `t`.
* `class2_empty`: `|I_χ(ρ)| < ¼`, by `LinnikHuxley.class2_count_small`'s integral estimate with the pointwise bound in
  place of the convexity bound. On the line `Re w = ½ − β`, `|G_χ|(1 + |v|)⁵ ≤ A|M_X||L|` (`LinnikIngham.Gχ_left_le'`,
  `A = KG Y^{½−σ}/δ`) with `|M_X| ≤ X` (`LinnikDetect.norm_mollχ_le_X`) and, by the pointwise bound at `t = γ + v`,
  `|L| ≤ CL (q(T + 2))^{1/6+ε}(1 + |v|)²` (from `q(1 + |γ + v|) ≤ q(T + 2)(1 + |v|)` and `1/6 + ε ≤ 2`); then
  `(1 + |v|)²(1 + |v|)^{−5} ≤ (1 + v²)^{−1}` (`wt5_mul_sq_le`) and `∫ (1 + v²)^{−1} dv = π` give
  `|I_χ(ρ)| ≤ (1/2π)·A·X·CL (q(T + 2))^{1/6+ε}·π = A X CL (q(T + 2))^{1/6+ε}/2 < ¼`. The weight `(1 + |v|)^{−4}`, whose
  integral is `2/3`, would need `ε ≤ 5/6`; at `ε ≤ 1` the weight `(1 + |v|)^{1/6+ε−5}` is only `(1 + |v|)^{−23/6}`,
  so the threshold's constant is `2` here, not `4/(3π)`.
* `class2_finset_empty`, `class2_card_eq_zero`: a finite set of characters detected as in `class2_count_small`'s
  `hdet` (`χ ≠ 1`, a zero `β_χ + iγ_χ` with `σ ≤ β_χ < 1`, `|γ_χ| ≤ T`, `|I_χ(ρ_χ)| ≥ ¼`) is empty under the same
  threshold.

The file imports `LinnikHuxley`, for `LinnikIngham.Gχ_left_le'` and `wt5`, `LinnikDetect.Ivχ`, `Gχ`, `mollχ` and
`norm_mollχ_le_X`, and `InghamDensity.KG` and `integrable_real_of_le`.
-/
import LinnikHuxley

open Complex Real Filter Topology MeasureTheory Finset

noncomputable section

namespace LinnikWeyl

open InghamDensity LinnikDetect LinnikIngham DirichletCharacter

/-- **Petrow–Young's Weyl bound, for every character**, as a hypothesis: for every `ε > 0` there is `C ≥ 0` such that
for every `q ≥ 1`, every `χ` mod `q` and every real `t`, `‖L(1/2 + it, χ)‖ ≤ C (q(1 + |t|))^{1/6+ε}`. -/
def PYWeyl : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
    ‖LFunction χ (1 / 2 + t * I)‖ ≤ C * ((q : ℝ) * (1 + |t|)) ^ (1 / 6 + ε)

variable {q : ℕ} [NeZero q]

/-- **The integral class is empty under a pointwise bound.** For `0 ≤ ε ≤ 1` (`hε0`, `hε1`), `CL ≥ 0` (`hCL`) and the
bound `‖L(½ + it, χ')‖ ≤ CL (q(1 + |t|))^{1/6+ε}` for every character `χ'` mod `q` and every real `t` (`hL`); for
`X ≥ 1` (`hX`), `δ > 0` (`hδ`), `½ + δ ≤ σ` (`hσδ`), `T ≥ 0` (`hT`), `Y ≥ 1` (`hY`) and the threshold
`2 KG CL X (q(T + 2))^{1/6+ε} < δ Y^{σ−½}` (`hbig`): a character `χ ≠ 1` (`hχ`) with a zero `β + iγ` of `L(·, χ)`
(`hz`), `σ ≤ β` (`hσβ`), `β < 1` (`hβ1`) and `|γ| ≤ T` (`hγ`) has `‖I_χ(β + iγ)‖ < ¼`. The proof is
`class2_count_small`'s integral estimate with the pointwise bound in place of the convexity bound:
`|G_χ|(1 + |v|)⁵ ≤ A|M_X||L|` on the line
(`Gχ_left_le'`), `|M_X| ≤ X`, `|L| ≤ CL (q(T + 2))^{1/6+ε}(1 + |v|)²`, `(1 + |v|)²(1 + |v|)^{−5} ≤ (1 + v²)^{−1}` and
`∫ (1 + v²)^{−1} dv = π`, so `‖I_χ(β + iγ)‖ ≤ A X CL (q(T + 2))^{1/6+ε}/2`, which `hbig` makes less than `¼`. -/
theorem class2_empty {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {CL : ℝ} (hCL : 0 ≤ CL)
    (hL : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (1 + |t|)) ^ (1 / 6 + ε))
    {X : ℕ} (hX : 1 ≤ X) {σ δ T Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hT : 0 ≤ T) (hY : 1 ≤ Y)
    (hbig : KG * CL * X * ((q : ℝ) * (T + 2)) ^ (1 / 6 + ε) * 2 < δ * Y ^ (σ - 1 / 2))
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {β γ : ℝ} (hσβ : σ ≤ β) (hβ1 : β < 1) (hγ : |γ| ≤ T)
    (hz : LFunction χ ((β : ℂ) + γ * I) = 0) :
    ‖Ivχ χ X Y ((β : ℂ) + γ * I)‖ < 1 / 4 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  set A := KG * Y ^ (1 / 2 - σ) / δ with hA
  have hA0 : 0 < A := by have := KG_pos; positivity
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  set P := ((q : ℝ) * (T + 2)) ^ (1 / 6 + ε) with hP
  have hP0 : 0 ≤ P := by positivity
  set B := CL * P with hB
  have hB0 : 0 ≤ B := mul_nonneg hCL hP0
  set m : ℝ → ℝ := fun v => ‖mollχ χ X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hm
  set l : ℝ → ℝ := fun v => ‖LFunction χ (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hl
  have hmc : Continuous m := ((differentiable_mollχ χ X).continuous.comp (by fun_prop)).norm
  have hlc : Continuous l := ((differentiable_LFunction hχ).continuous.comp (by fun_prop)).norm
  have hmX : ∀ v, m v ≤ X := fun v => norm_mollχ_le_X χ X (by simp)
  have hm0 : ∀ v, 0 ≤ m v := fun v => norm_nonneg _
  have hl0 : ∀ v, 0 ≤ l v := fun v => norm_nonneg _
  -- the pointwise bound at `t = γ + v`: `q(1 + |γ + v|) ≤ q(T + 2)(1 + |v|)` and `1/6 + ε ≤ 2`
  have hlb : ∀ v, l v ≤ B * (1 + |v|) ^ 2 := by
    intro v
    have h := hL χ (γ + v)
    have h1 := abs_add_le γ v
    have hv0 := abs_nonneg v
    have hbase : (q : ℝ) * (1 + |γ + v|) ≤ (q : ℝ) * (T + 2) * (1 + |v|) := by
      have h3 : 1 + |γ + v| ≤ (T + 2) * (1 + |v|) := by nlinarith [mul_nonneg hT hv0]
      calc (q : ℝ) * (1 + |γ + v|) ≤ q * ((T + 2) * (1 + |v|)) := by gcongr
        _ = (q : ℝ) * (T + 2) * (1 + |v|) := by ring
    have hv1 : (1 : ℝ) ≤ 1 + |v| := by linarith
    calc l v ≤ CL * ((q : ℝ) * (1 + |γ + v|)) ^ (1 / 6 + ε) := h
      _ ≤ CL * ((q : ℝ) * (T + 2) * (1 + |v|)) ^ (1 / 6 + ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase (by linarith)) hCL
      _ = CL * (((q : ℝ) * (T + 2)) ^ (1 / 6 + ε) * (1 + |v|) ^ (1 / 6 + ε)) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ CL * (((q : ℝ) * (T + 2)) ^ (1 / 6 + ε) * (1 + |v|) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hv1 (by linarith)) (by positivity)) hCL
      _ = B * (1 + |v|) ^ 2 := by rw [hB, hP, Real.rpow_two]; ring
  -- the majorant `X·B·(1 + v²)^{−1}`
  have hpt : ∀ v, m v * l v * wt5 v ≤ X * B * (1 + v ^ 2)⁻¹ := by
    intro v
    calc m v * l v * wt5 v ≤ X * (B * (1 + |v|) ^ 2) * wt5 v :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hmX v) (hlb v) (hl0 v) hX0.le) (wt5_pos v).le
      _ = X * B * (wt5 v * (1 + |v|) ^ 2) := by ring
      _ ≤ X * B * (1 + v ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (wt5_mul_sq_le v) (mul_nonneg hX0.le hB0)
  have hint : Integrable fun v => m v * l v * wt5 v := by
    refine integrable_real_of_le ((hmc.mul hlc).mul continuous_wt5) (K := X * B) fun v => ?_
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hm0 v) (hl0 v)) (wt5_pos v).le)]
    exact hpt v
  -- the integral identity, bounded on the line
  have hIv : ‖Ivχ χ X Y ((β : ℂ) + γ * I)‖ ≤ A / (2 * π) * ∫ v, m v * l v * wt5 v := by
    unfold Ivχ
    rw [norm_mul]
    have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc2]
    have hle : ‖∫ v : ℝ, Gχ χ X Y ((β : ℂ) + γ * I)
        (((1 / 2 - ((β : ℂ) + γ * I).re : ℝ) : ℂ) + v * I)‖
        ≤ ∫ v, A * (m v * l v * wt5 v) := by
      refine norm_integral_le_of_norm_le (hint.const_mul A) (Eventually.of_forall fun v => ?_)
      have h := Gχ_left_le' X hδ hσδ hσβ hβ1 hY hz v
      have hp : 0 < (1 + |v|) ^ 5 := by positivity
      have e : A * (m v * l v * wt5 v) = A * (m v * l v) / (1 + |v|) ^ 5 := by
        unfold wt5; ring
      rw [e, le_div_iff₀ hp]
      exact h
    rw [integral_const_mul] at hle
    calc 1 / (2 * π) * ‖∫ v : ℝ, Gχ χ X Y ((β : ℂ) + γ * I)
          (((1 / 2 - ((β : ℂ) + γ * I).re : ℝ) : ℂ) + v * I)‖
        ≤ 1 / (2 * π) * (A * ∫ v, m v * l v * wt5 v) := by gcongr
      _ = A / (2 * π) * ∫ v, m v * l v * wt5 v := by ring
  -- integrate the majorant
  have hI2 : ∫ v, m v * l v * wt5 v ≤ X * B * π := by
    calc ∫ v, m v * l v * wt5 v ≤ ∫ v, X * B * (1 + v ^ 2)⁻¹ :=
          integral_mono hint (integrable_inv_one_add_sq.const_mul _) hpt
      _ = X * B * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hpi : 0 < π := Real.pi_pos
  have hfin : ‖Ivχ χ X Y ((β : ℂ) + γ * I)‖ ≤ A * X * B / 2 := by
    calc ‖Ivχ χ X Y ((β : ℂ) + γ * I)‖ ≤ A / (2 * π) * ∫ v, m v * l v * wt5 v := hIv
      _ ≤ A / (2 * π) * (X * B * π) := by gcongr
      _ = A * X * B / 2 := by field_simp
  -- the threshold: `A X B = KG CL X (q(T + 2))^{1/6+ε} / (δ Y^{σ−½}) < ½`
  have hYp : 0 < Y ^ (σ - 1 / 2) := Real.rpow_pos_of_pos hY0 _
  have hYinv : Y ^ (1 / 2 - σ) = (Y ^ (σ - 1 / 2))⁻¹ := by
    rw [← Real.rpow_neg hY0.le]; congr 1; ring
  have hAXB : A * X * B = KG * CL * X * P / (δ * Y ^ (σ - 1 / 2)) := by
    rw [hA, hB, hYinv]; field_simp
  have hlt : A * X * B < 1 / 2 := by
    rw [hAXB, div_lt_iff₀ (by positivity)]
    linarith
  linarith

/-- **A finite integral class is empty.** Under the hypotheses of `class2_empty` (`hε0 : 0 ≤ ε`, `hε1 : ε ≤ 1`,
`hCL : 0 ≤ CL`, the pointwise bound `hL`, `hX : 1 ≤ X`, `hδ : 0 < δ`, `hσδ : ½ + δ ≤ σ`, `hT : 0 ≤ T`, `hY : 1 ≤ Y` and
the threshold `hbig`), a finite set `Rs` of characters each with `χ ≠ 1`, a zero `β_χ + iγ_χ` of `L(·, χ)`,
`σ ≤ β_χ < 1`, `|γ_χ| ≤ T` and `‖I_χ(ρ_χ)‖ ≥ ¼` (`hdet`, as in `LinnikHuxley.class2_count_small`) is empty. -/
theorem class2_finset_empty {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {CL : ℝ} (hCL : 0 ≤ CL)
    (hL : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (1 + |t|)) ^ (1 / 6 + ε))
    {X : ℕ} (hX : 1 ≤ X) {σ δ T Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hT : 0 ≤ T) (hY : 1 ≤ Y)
    (hbig : KG * CL * X * ((q : ℝ) * (T + 2)) ^ (1 / 6 + ε) * 2 < δ * Y ^ (σ - 1 / 2))
    (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hdet : ∀ χ ∈ Rs, χ ≠ 1 ∧ σ ≤ β χ ∧ β χ < 1 ∧ |γ χ| ≤ T ∧ LFunction χ ((β χ : ℂ) + γ χ * I) = 0
      ∧ 1 / 4 ≤ ‖Ivχ χ X Y ((β χ : ℂ) + γ χ * I)‖) :
    Rs = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun χ hχ => ?_
  obtain ⟨hχ1, hσβ, hβ1, hγ, hz, hI⟩ := hdet χ hχ
  exact absurd hI (not_le.2 (class2_empty hε0 hε1 hCL hL hX hδ hσδ hT hY hbig hχ1 hσβ hβ1 hγ hz))

/-- **A finite integral class has no members**: `class2_finset_empty` as `Rs.card = 0`, under the same hypotheses
(`hε0`, `hε1`, `hCL`, `hL`, `hX`, `hδ`, `hσδ`, `hT`, `hY`, `hbig`, `hdet`). -/
theorem class2_card_eq_zero {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {CL : ℝ} (hCL : 0 ≤ CL)
    (hL : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (1 + |t|)) ^ (1 / 6 + ε))
    {X : ℕ} (hX : 1 ≤ X) {σ δ T Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hT : 0 ≤ T) (hY : 1 ≤ Y)
    (hbig : KG * CL * X * ((q : ℝ) * (T + 2)) ^ (1 / 6 + ε) * 2 < δ * Y ^ (σ - 1 / 2))
    (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hdet : ∀ χ ∈ Rs, χ ≠ 1 ∧ σ ≤ β χ ∧ β χ < 1 ∧ |γ χ| ≤ T ∧ LFunction χ ((β χ : ℂ) + γ χ * I) = 0
      ∧ 1 / 4 ≤ ‖Ivχ χ X Y ((β χ : ℂ) + γ χ * I)‖) :
    Rs.card = 0 := by
  rw [Finset.card_eq_zero]
  exact class2_finset_empty hε0 hε1 hCL hL hX hδ hσδ hT hY hbig Rs β γ hdet

end LinnikWeyl

#print axioms LinnikWeyl.class2_empty
#print axioms LinnikWeyl.class2_finset_empty
#print axioms LinnikWeyl.class2_card_eq_zero
