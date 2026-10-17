/-
# Round 524, part 3: Ingham's density estimate over the characters mod `q`, and Linnik's exponent `36/13 + η`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `0 < ε ≤ 1`, `CharDensity (36/13 + 4ε) 10 C` holds with some `C ≥ 0`
(`charDensity_ingham`): for every `q ≥ 1`, `½ ≤ σ ≤ 1` and `T ≥ 2`, at most `C(qT)^{(36/13+4ε)(1−σ)}(log qT)^{10}`
characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. With round 520's `linnik_of_charDensity`,
for every `η > 0` every reduced class mod `q` has a prime `p ≤ K q^{36/13+η}` (`linnik_thirtysix_thirteenths`), with
no hypothesis. Round 522 had `17/6 + η`; `36/13 = 3/(2 − 11/12)` is Ingham's exponent `3/(2 − σ)` at the edge of round
495's zero-free half-plane `Re s > 11/12`.

* `Gχ_left_le'`: on the line `Re w = ½ − β` of round 521's detector, `|G_χ(w)|(1 + |v|)⁵ ≤ (KG Y^{½−σ}/δ)|M_X||L|`,
  with `L` kept instead of bounded.
* `class2_count_ingham`: the integral class has at most `2AλM₁ + A²M₂/λ²` members for every `λ > 0`, with
  `A = KG Y^{½−σ}/δ`, `M₁ = MV(X)(q(T + 1) + X)` (round 521's `mean_value_mollχ`) and `M₂ = C₄(q(T + 2))^{1+ε}` (the fourth
  moment of `LinnikFourth.fourth_moment`): `ml ≤ (λ/2)m² + μl⁴/(4λ) + 1/(4λμ)` at `μ = A/λ`.
* `count_nontrivial_ingham`: round 521's two classes at one modulus, with this count for the integral class.
* `bound_class2_ingham`: at `X = ⌊Q⌋`, `Y = Q^{18/13}` (round 518's `Yw` at `c = 5/26`) and
  `λ = Q^{(6/13)(½−σ)+ε/3}`, both terms are `Q^{(24/13)(½−σ)+1+ε/3}`, at most `Q^{(36/13+4ε)(1−σ)}` for `σ ≤ 11/12`;
  round 521's `bound_class1` at `c = 5/26` gives the polynomial class `Q^{(36/13)(1−σ)}`.
* `charDensity_ingham`: below `σ = 23/36` at most `q ≤ qT ≤ (qT)^{(36/13)(1−σ)}` characters are counted; above
  `11/12` only the trivial character can be (`LinnikLindelof.LFunction_ne_zero`); between, `count_middle` at
  `Q = q(T + 6) ≤ 4qT` with `δ = 5/36`.
-/
import LinnikFourth

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikIngham

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity DirichletCharacter ShortWeil DirMean Finset

variable {q : ℕ} [NeZero q]

/-! ### The integral class with the fourth moment -/

/-- **On the line `Re w = ½ − β`, with `L` kept**: `|G(w)|(1 + |v|)⁵ ≤ KG Y^{½−σ}/δ·|M_X(½ + i(γ + v), χ)|·
|L(½ + i(γ + v), χ)|` for a zero `ρ = β + iγ` of `L(·, χ)` with `σ ≤ β < 1` and `½ + δ ≤ σ`. -/
theorem Gχ_left_le' {χ : DirichletCharacter ℂ q} (X : ℕ) {σ δ Y β γ : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ)
    (hσβ : σ ≤ β) (hβ1 : β < 1) (hY : 1 ≤ Y) (hz : LFunction χ ((β : ℂ) + γ * I) = 0) (v : ℝ) :
    ‖Gχ χ X Y ((β : ℂ) + γ * I) (((1 / 2 - ((β : ℂ) + γ * I).re : ℝ) : ℂ) + v * I)‖ * (1 + |v|) ^ 5
      ≤ KG * Y ^ (1 / 2 - σ) / δ * (‖mollχ χ X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ *
        ‖LFunction χ (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖) := by
  have hre : ((β : ℂ) + γ * I).re = β := by simp
  rw [hre]
  set w : ℂ := ((1 / 2 - β : ℝ) : ℂ) + v * I with hw
  have hwre : w.re = 1 / 2 - β := by simp [hw]
  have hwim : w.im = v := by simp [hw]
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre; linarith
  have hsum : (β : ℂ) + γ * I + w = 1 / 2 + ((γ + v : ℝ) : ℂ) * I := by
    rw [hw]; push_cast; ring
  rw [Gχ_eq_left X Y hz hw0, hsum, norm_mul, norm_mul, norm_mul, norm_div]
  have hG := norm_Gamma_le' (z := w + 1) (by simp [hwre]; linarith) (by simp [hwre]; linarith)
  have hGim : (w + 1).im = v := by simp [hwim]
  rw [hGim] at hG
  have hwn : δ ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hwre, abs_of_neg (by linarith)] at this
    linarith
  have hYw : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (1 / 2 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hwre]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  set m := ‖mollχ χ X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hm
  set l := ‖LFunction χ (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hl
  set g := ‖Complex.Gamma (w + 1)‖ with hg
  have hm0 : 0 ≤ m := norm_nonneg _
  have hl0 : 0 ≤ l := norm_nonneg _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hdiv : g / ‖w‖ ≤ g / δ := div_le_div_of_nonneg_left hg0 hδ hwn
  have hYp : 0 ≤ Y ^ (1 / 2 - σ) := Real.rpow_nonneg (by linarith) _
  calc m * l * (g / ‖w‖) * ‖(Y : ℂ) ^ w‖ * (1 + |v|) ^ 5
      ≤ m * l * (g / δ) * Y ^ (1 / 2 - σ) * (1 + |v|) ^ 5 := by gcongr
    _ = Y ^ (1 / 2 - σ) / δ * (m * l) * (g * (1 + |v|) ^ 5) := by ring
    _ ≤ Y ^ (1 / 2 - σ) / δ * (m * l) * KG := by gcongr
    _ = KG * Y ^ (1 / 2 - σ) / δ * (m * l) := by ring

/-- The weight `(1 + |v|)^{−5}`. -/
def wt5 (v : ℝ) : ℝ := ((1 + |v|) ^ 5)⁻¹

theorem wt5_pos (v : ℝ) : 0 < wt5 v := by unfold wt5; positivity

theorem continuous_wt5 : Continuous wt5 := by
  unfold wt5
  exact (by fun_prop : Continuous fun v : ℝ => (1 + |v|) ^ 5).inv₀ fun v => by positivity

theorem wt5_mul_sq_le (v : ℝ) : wt5 v * (1 + |v|) ^ 2 ≤ (1 + v ^ 2)⁻¹ := by
  have h1 : 0 < 1 + |v| := by positivity
  have e : wt5 v * (1 + |v|) ^ 2 = wt v := by
    unfold wt5 wt; field_simp
  rw [e]; exact wt_le v

theorem wt5_mul_le (v : ℝ) : wt5 v * (1 + |v|) ≤ (1 + v ^ 2)⁻¹ := by
  have h1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have h := wt5_mul_sq_le v
  have hw := (wt5_pos v).le
  calc wt5 v * (1 + |v|) ≤ wt5 v * (1 + |v|) ^ 2 := by
        gcongr; nlinarith
    _ ≤ _ := h

theorem wt5_le (v : ℝ) : wt5 v ≤ (1 + v ^ 2)⁻¹ :=
  le_trans (le_mul_of_one_le_right (wt5_pos v).le (by linarith [abs_nonneg v])) (wt5_mul_le v)

/-- **The integral class, Ingham's way.** Characters `χ ≠ 1` with a zero `ρ_χ = β_χ + iγ_χ`, `σ ≤ β_χ < 1`,
`|γ_χ| ≤ T`, and `|I_χ(ρ_χ)| ≥ ¼` number at most `2AλM₁ + A²M₂/λ²` for every `λ > 0`, with `A = KG Y^{½−σ}/δ`,
`M₁ = MV(X)(q(T + 1) + X)` and `M₂ = C₄(q(T + 2))^{1+ε}`, given the fourth moment
`Σ_χ |L(½ + it_χ, χ)|⁴ ≤ C₄(q(T' + 2))^{1+ε}` over characters `χ ≠ 1` at points `|t_χ| ≤ T'`. On the line,
`|G_χ|(1 + |v|)⁵ ≤ A|M_X||L|` (`Gχ_left_le'`); then `ml ≤ (λ/2)m² + μl⁴/(4λ) + 1/(4λμ)` at `μ = A/λ`, the mean
value of the mollifier (`mean_value_mollχ`) and the fourth moment at the points `γ_χ + v`. -/
theorem class2_count_ingham {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {X : ℕ} (hX : 1 ≤ X) {σ δ T Y lam : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hT : 0 ≤ T) (hY : 1 ≤ Y)
    (hlam : 0 < lam) (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hdet : ∀ χ ∈ Rs, χ ≠ 1 ∧ σ ≤ β χ ∧ β χ < 1 ∧ |γ χ| ≤ T ∧ LFunction χ ((β χ : ℂ) + γ χ * I) = 0
      ∧ 1 / 4 ≤ ‖Ivχ χ X Y ((β χ : ℂ) + γ χ * I)‖) :
    (Rs.card : ℝ) ≤ 2 * (KG * Y ^ (1 / 2 - σ) / δ) * lam * (MV X * ((q : ℝ) * (T + 1) + X)) +
      (KG * Y ^ (1 / 2 - σ) / δ) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) / lam ^ 2 := by
  classical
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  set A := KG * Y ^ (1 / 2 - σ) / δ with hA
  have hA0 : 0 < A := by
    have := KG_pos
    have : 0 < Y := by linarith
    positivity
  set M₁ := MV X * ((q : ℝ) * (T + 1) + X) with hM₁
  set M₂ := C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε) with hM₂
  set μ := A / lam with hμ
  have hμ0 : 0 < μ := div_pos hA0 hlam
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hMV0 : 0 ≤ MV X := by unfold MV; have := Real.log_nonneg hXr; positivity
  have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  set m : DirichletCharacter ℂ q → ℝ → ℝ := fun χ v => ‖mollχ χ X (1 / 2 + ((γ χ + v : ℝ) : ℂ) * I)‖ with hm
  set l : DirichletCharacter ℂ q → ℝ → ℝ := fun χ v => ‖LFunction χ (1 / 2 + ((γ χ + v : ℝ) : ℂ) * I)‖ with hl
  have hmc : ∀ χ, Continuous (m χ) := fun χ =>
    ((differentiable_mollχ χ X).continuous.comp (by fun_prop)).norm
  have hlc : ∀ χ ∈ Rs, Continuous (l χ) := fun χ hχ =>
    ((differentiable_LFunction (hdet χ hχ).1).continuous.comp (by fun_prop)).norm
  have hmX : ∀ χ v, m χ v ≤ X := fun χ v => norm_mollχ_le_X χ X (by simp)
  have hm0 : ∀ χ v, 0 ≤ m χ v := fun χ v => norm_nonneg _
  have hl0 : ∀ χ v, 0 ≤ l χ v := fun χ v => norm_nonneg _
  have hbase : ∀ χ ∈ Rs, ∀ v : ℝ, (q : ℝ) * (|γ χ + v| + 2) ≤ (q : ℝ) * (T + 2) * (1 + |v|) := by
    intro χ hχ v
    have h1 := abs_add_le (γ χ) v
    have h2 := (hdet χ hχ).2.2.2.1
    have h3 : |γ χ + v| + 2 ≤ (T + 2) * (1 + |v|) := by nlinarith [abs_nonneg v]
    calc (q : ℝ) * (|γ χ + v| + 2) ≤ q * ((T + 2) * (1 + |v|)) := by gcongr
      _ = (q : ℝ) * (T + 2) * (1 + |v|) := by ring
  -- `l` grows at most linearly (round 521's partial-summation bound)
  have hlb : ∀ χ ∈ Rs, ∀ v, l χ v ≤ 11 * ((q : ℝ) * (T + 2) * (1 + |v|)) := by
    intro χ hχ v
    have h := LinnikDensity.norm_LFunction_half_le (hdet χ hχ).1 (γ χ + v)
    have hb1 : 1 ≤ (q : ℝ) * (|γ χ + v| + 2) := by nlinarith [abs_nonneg (γ χ + v)]
    have hsq : ((q : ℝ) * (|γ χ + v| + 2)) ^ (1 / 2 : ℝ) ≤ (q : ℝ) * (|γ χ + v| + 2) := by
      calc ((q : ℝ) * (|γ χ + v| + 2)) ^ (1 / 2 : ℝ) ≤ ((q : ℝ) * (|γ χ + v| + 2)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
        _ = _ := Real.rpow_one _
    calc l χ v ≤ 11 * ((q : ℝ) * (|γ χ + v| + 2)) ^ (1 / 2 : ℝ) := h
      _ ≤ 11 * ((q : ℝ) * (T + 2) * (1 + |v|)) := by
          gcongr; exact hsq.trans (hbase χ hχ v)
  have hint : ∀ χ ∈ Rs, Integrable fun v => m χ v * l χ v * wt5 v := by
    intro χ hχ
    refine integrable_real_of_le (((hmc χ).mul (hlc χ hχ)).mul continuous_wt5)
      (K := X * (11 * ((q : ℝ) * (T + 2)))) fun v => ?_
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hm0 χ v) (hl0 χ v)) (wt5_pos v).le)]
    have hw := (wt5_pos v).le
    calc m χ v * l χ v * wt5 v ≤ X * (11 * ((q : ℝ) * (T + 2) * (1 + |v|))) * wt5 v := by
          gcongr
          · exact hmX χ v
          · exact hlb χ hχ v
      _ = X * (11 * ((q : ℝ) * (T + 2))) * (wt5 v * (1 + |v|)) := by ring
      _ ≤ X * (11 * ((q : ℝ) * (T + 2))) * (1 + v ^ 2)⁻¹ := by
          have : 0 ≤ (X : ℝ) * (11 * ((q : ℝ) * (T + 2))) := by positivity
          exact mul_le_mul_of_nonneg_left (wt5_mul_le v) this
  -- (i) each character
  have hIv : ∀ χ ∈ Rs, 1 / 4 ≤ A / (2 * π) * ∫ v, m χ v * l χ v * wt5 v := by
    intro χ hχ
    obtain ⟨hχ1, hσβ, hβ1, hγ, hz, hI⟩ := hdet χ hχ
    refine hI.trans ?_
    unfold Ivχ
    rw [norm_mul]
    have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc2]
    have hle : ‖∫ v : ℝ, Gχ χ X Y ((β χ : ℂ) + γ χ * I)
        (((1 / 2 - ((β χ : ℂ) + γ χ * I).re : ℝ) : ℂ) + v * I)‖
        ≤ ∫ v, A * (m χ v * l χ v * wt5 v) := by
      refine norm_integral_le_of_norm_le ((hint χ hχ).const_mul A) (Eventually.of_forall fun v => ?_)
      have h := Gχ_left_le' X hδ hσδ hσβ hβ1 hY hz v
      have hp : 0 < (1 + |v|) ^ 5 := by positivity
      have e : A * (m χ v * l χ v * wt5 v) = A * (m χ v * l χ v) / (1 + |v|) ^ 5 := by
        unfold wt5; ring
      rw [e, le_div_iff₀ hp]
      exact h
    rw [integral_const_mul] at hle
    calc 1 / (2 * π) * ‖∫ v : ℝ, Gχ χ X Y ((β χ : ℂ) + γ χ * I)
          (((1 / 2 - ((β χ : ℂ) + γ χ * I).re : ℝ) : ℂ) + v * I)‖
        ≤ 1 / (2 * π) * (A * ∫ v, m χ v * l χ v * wt5 v) := by gcongr
      _ = A / (2 * π) * ∫ v, m χ v * l χ v * wt5 v := by ring
  -- (ii) the sum over the class
  have hsum1 : (Rs.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ χ ∈ Rs, m χ v * l χ v * wt5 v := by
    rw [integral_finsetSum Rs fun χ hχ => hint χ hχ, mul_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hIv
  -- (iii) pointwise
  set K' := lam / 2 * M₁ + μ / (4 * lam) * M₂ + (Rs.card : ℝ) * (1 / (4 * lam * μ)) with hK'
  have hpt : ∀ v : ℝ, ∑ χ ∈ Rs, m χ v * l χ v * wt5 v ≤ K' * (1 + v ^ 2)⁻¹ := by
    intro v
    have hamgm : ∀ χ, m χ v * l χ v ≤ lam / 2 * m χ v ^ 2 + μ / (4 * lam) * l χ v ^ 4 +
        1 / (4 * lam * μ) := by
      intro χ
      have h1 : m χ v * l χ v ≤ lam / 2 * m χ v ^ 2 + l χ v ^ 2 / (2 * lam) := by
        have e : lam / 2 * m χ v ^ 2 + l χ v ^ 2 / (2 * lam) - m χ v * l χ v =
            (lam * m χ v - l χ v) ^ 2 / (2 * lam) := by field_simp; ring
        have : 0 ≤ (lam * m χ v - l χ v) ^ 2 / (2 * lam) := by positivity
        linarith
      have h2 : l χ v ^ 2 ≤ μ / 2 * l χ v ^ 4 + 1 / (2 * μ) := by
        have e : μ / 2 * l χ v ^ 4 + 1 / (2 * μ) - l χ v ^ 2 = (μ * l χ v ^ 2 - 1) ^ 2 / (2 * μ) := by
          field_simp; ring
        have : 0 ≤ (μ * l χ v ^ 2 - 1) ^ 2 / (2 * μ) := by positivity
        linarith
      have h3 : l χ v ^ 2 / (2 * lam) ≤ (μ / 2 * l χ v ^ 4 + 1 / (2 * μ)) / (2 * lam) := by gcongr
      have e3 : (μ / 2 * l χ v ^ 4 + 1 / (2 * μ)) / (2 * lam) =
          μ / (4 * lam) * l χ v ^ 4 + 1 / (4 * lam * μ) := by field_simp; ring
      linarith
    have hmv := mean_value_mollχ hX hT (abs_nonneg v) Rs (fun χ => γ χ + v)
      (fun χ hχ => by
        have h1 := abs_add_le (γ χ) v
        have h2 := (hdet χ hχ).2.2.2.1
        linarith)
    have hS2 : ∑ χ ∈ Rs, m χ v ^ 2 ≤ M₁ * (1 + |v|) := by
      have hb : (q : ℝ) * (T + 1 + |v|) + X ≤ ((q : ℝ) * (T + 1) + X) * (1 + |v|) := by
        nlinarith [abs_nonneg v, mul_nonneg (mul_nonneg hq0 hT) (abs_nonneg v),
          mul_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X) (abs_nonneg v)]
      calc ∑ χ ∈ Rs, m χ v ^ 2 ≤ MV X * ((q : ℝ) * (T + 1 + |v|) + X) := hmv
        _ ≤ MV X * (((q : ℝ) * (T + 1) + X) * (1 + |v|)) := by gcongr
        _ = M₁ * (1 + |v|) := by rw [hM₁]; ring
    have h4v := h4 Rs (fun χ hχ => (hdet χ hχ).1) (T + |v|) (by positivity) (fun χ => γ χ + v)
      (fun χ hχ => by
        have h1 := abs_add_le (γ χ) v
        have h2 := (hdet χ hχ).2.2.2.1
        linarith)
    have hS4 : ∑ χ ∈ Rs, l χ v ^ 4 ≤ M₂ * (1 + |v|) ^ 2 := by
      have hb : (q : ℝ) * (T + |v| + 2) ≤ (q : ℝ) * (T + 2) * (1 + |v|) := by
        nlinarith [abs_nonneg v, mul_nonneg (mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ T + 1)) (abs_nonneg v)]
      have hv1 : (1 : ℝ) ≤ 1 + |v| := by linarith [abs_nonneg v]
      have hp1 : ((q : ℝ) * (T + |v| + 2)) ^ (1 + ε) ≤ ((q : ℝ) * (T + 2)) ^ (1 + ε) * (1 + |v|) ^ 2 := by
        calc ((q : ℝ) * (T + |v| + 2)) ^ (1 + ε) ≤ ((q : ℝ) * (T + 2) * (1 + |v|)) ^ (1 + ε) :=
              Real.rpow_le_rpow (by positivity) hb (by linarith)
          _ = ((q : ℝ) * (T + 2)) ^ (1 + ε) * (1 + |v|) ^ (1 + ε) := Real.mul_rpow (by positivity) (by positivity)
          _ ≤ ((q : ℝ) * (T + 2)) ^ (1 + ε) * (1 + |v|) ^ (2 : ℝ) := by
              exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hv1 (by linarith))
                (by positivity)
          _ = ((q : ℝ) * (T + 2)) ^ (1 + ε) * (1 + |v|) ^ 2 := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc ∑ χ ∈ Rs, l χ v ^ 4 ≤ C₄ * ((q : ℝ) * (T + |v| + 2)) ^ (1 + ε) := h4v
        _ ≤ C₄ * (((q : ℝ) * (T + 2)) ^ (1 + ε) * (1 + |v|) ^ 2) := by gcongr
        _ = M₂ * (1 + |v|) ^ 2 := by rw [hM₂]; ring
    have hw0 := (wt5_pos v).le
    have hw1 := wt5_mul_le v
    have hw2 := wt5_mul_sq_le v
    have hw := wt5_le v
    have ha0 : 0 ≤ lam / 2 * M₁ := by positivity
    have hb0 : 0 ≤ μ / (4 * lam) * M₂ := by positivity
    have hc0 : 0 ≤ (Rs.card : ℝ) * (1 / (4 * lam * μ)) := by positivity
    calc ∑ χ ∈ Rs, m χ v * l χ v * wt5 v = wt5 v * ∑ χ ∈ Rs, m χ v * l χ v := by
          rw [mul_sum]; exact sum_congr rfl fun χ _ => by ring
      _ ≤ wt5 v * ∑ χ ∈ Rs, (lam / 2 * m χ v ^ 2 + μ / (4 * lam) * l χ v ^ 4 + 1 / (4 * lam * μ)) := by
          gcongr with χ hχ; exact hamgm χ
      _ = wt5 v * (lam / 2 * ∑ χ ∈ Rs, m χ v ^ 2 + μ / (4 * lam) * ∑ χ ∈ Rs, l χ v ^ 4 +
            (Rs.card : ℝ) * (1 / (4 * lam * μ))) := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ wt5 v * (lam / 2 * (M₁ * (1 + |v|)) + μ / (4 * lam) * (M₂ * (1 + |v|) ^ 2) +
            (Rs.card : ℝ) * (1 / (4 * lam * μ))) := by gcongr
      _ = lam / 2 * M₁ * (wt5 v * (1 + |v|)) + μ / (4 * lam) * M₂ * (wt5 v * (1 + |v|) ^ 2) +
            (Rs.card : ℝ) * (1 / (4 * lam * μ)) * wt5 v := by ring
      _ ≤ lam / 2 * M₁ * (1 + v ^ 2)⁻¹ + μ / (4 * lam) * M₂ * (1 + v ^ 2)⁻¹ +
            (Rs.card : ℝ) * (1 / (4 * lam * μ)) * (1 + v ^ 2)⁻¹ := by gcongr
      _ = K' * (1 + v ^ 2)⁻¹ := by rw [hK']; ring
  -- (iv) integrate
  have hint_sum : Integrable fun v => ∑ χ ∈ Rs, m χ v * l χ v * wt5 v :=
    integrable_finsetSum Rs fun χ hχ => hint χ hχ
  have hI2 : ∫ v, ∑ χ ∈ Rs, m χ v * l χ v * wt5 v ≤ K' * π := by
    calc ∫ v, ∑ χ ∈ Rs, m χ v * l χ v * wt5 v ≤ ∫ v, K' * (1 + v ^ 2)⁻¹ :=
          integral_mono hint_sum (integrable_inv_one_add_sq.const_mul K') hpt
      _ = K' * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hpi : 0 < π := Real.pi_pos
  have hfin : (Rs.card : ℝ) * (1 / 4) ≤ A / 2 * K' := by
    calc (Rs.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ χ ∈ Rs, m χ v * l χ v * wt5 v := hsum1
      _ ≤ A / (2 * π) * (K' * π) := by gcongr
      _ = A / 2 * K' := by field_simp
  rw [hK'] at hfin
  have e : A / 2 * (lam / 2 * M₁ + μ / (4 * lam) * M₂ + (Rs.card : ℝ) * (1 / (4 * lam * μ))) =
      A * lam * M₁ / 4 + (A ^ 2 * M₂ / lam ^ 2) / 8 + (Rs.card : ℝ) / 8 := by
    rw [hμ]; field_simp; ring
  rw [e] at hfin
  linarith

/-! ### One modulus -/

open scoped Classical in
/-- **The two classes at one modulus, Ingham's way**: `count_nontrivial` (round 521) with the integral class counted
by `class2_count_ingham` for any `λ > 0`. -/
theorem count_nontrivial_ingham {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {c : ℝ} (hc0 : 0 ≤ c) {σ δ T Q lam : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hσ1 : σ ≤ 1) (hT : 2 ≤ T)
    (hQ : (q : ℝ) * (T + 6) ≤ Q) (hlam : 0 < lam) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ ((Nat.log 2 (Nw c Q) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2 * (32 * Real.exp 1
          * (1 + Real.log (2 * (Xw Q : ℝ) * (Nw c Q))) ^ 6
          * (Q * ((Xw Q : ℝ)) ^ (1 - 2 * σ) + ((Xw Q : ℝ) * (Nw c Q)) ^ (2 - 2 * σ)))
        + (2 * (KG * (Yw c Q) ^ (1 / 2 - σ) / δ) * lam * (MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))) +
          (KG * (Yw c Q) ^ (1 / 2 - σ) / δ) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) / lam ^ 2) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ8 : 8 ≤ Q := by nlinarith
  have hT0 : 0 ≤ T := by linarith
  have hX : 1 ≤ Xw Q := Xw_one hQ8
  have hN : 1 ≤ Nw c Q := Nw_one
  have hY8 : 8 ≤ Yw c Q := le_trans hQ8 (Yw_ge hc0 hQ8)
  have hY0 : 0 < Yw c Q := by linarith
  have hM : 22 * Yw c Q * Real.log (Yw c Q) ≤ ((Xw Q * Nw c Q : ℕ) : ℝ) := XN_ge hQ8
  set Z := univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
    ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 with hZ
  have hch : ∀ χ ∈ Z, ∃ s : ℂ, χ ≠ 1 ∧ σ ≤ s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
    intro χ hχ
    obtain ⟨hχ1, s, hs1, hs2, hs3⟩ := (mem_filter.1 hχ).2
    refine ⟨s, hχ1, hs1, ?_, hs2, hs3⟩
    by_contra hge
    push Not at hge
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hge hs3
  choose! s0 hs0 using hch
  have hz0 : ∀ χ ∈ Z, LFunction χ (((s0 χ).re : ℂ) + (s0 χ).im * I) = 0 := fun χ hχ => by
    rw [Complex.re_add_im]; exact (hs0 χ hχ).2.2.2.2
  have hdich : ∀ χ ∈ Z, 1 / 4 ≤ ‖Pvχ χ (Xw Q) (Nw c Q) (Yw c Q) (s0 χ).re (s0 χ).im‖
      ∨ 1 / 4 ≤ ‖Ivχ χ (Xw Q) (Yw c Q) (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := by
    intro χ hχ
    obtain ⟨hχ1, h1, h2, _, _⟩ := hs0 χ hχ
    exact dichotomy hχ1 hX hN hY8 hM (by linarith) h2 (hz0 χ hχ)
  set Z1 := Z.filter fun χ => 1 / 4 ≤ ‖Pvχ χ (Xw Q) (Nw c Q) (Yw c Q) (s0 χ).re (s0 χ).im‖ with hZ1
  set Z2 := Z.filter fun χ => 1 / 4 ≤ ‖Ivχ χ (Xw Q) (Yw c Q) (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ with hZ2
  have hcover : Z ⊆ Z1 ∪ Z2 := by
    intro χ hχ
    rcases hdich χ hχ with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hχ, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hχ, h⟩)
  have hc1' := class1_count (by linarith : 1 / 2 ≤ σ) hσ1 hT0 (by nlinarith : (q : ℝ) * (2 * T + 1) ≤ 2 * Q)
    hX hN hY0 (by norm_num : (0 : ℝ) < 1 / 4) Z1 (fun χ => (s0 χ).im) (fun χ => (s0 χ).re)
    (fun χ hχ => (hs0 χ (mem_filter.1 hχ).1).2.2.2.1)
    (fun χ hχ => ⟨(hs0 χ (mem_filter.1 hχ).1).2.1, by linarith [(hs0 χ (mem_filter.1 hχ).1).2.2.1]⟩)
    (fun χ hχ => (mem_filter.1 hχ).2)
  have hc2' := class2_count_ingham hε0 hε1 hC₄ h4 hX hδ hσδ hT0 (by linarith : 1 ≤ Yw c Q) hlam Z2
    (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => by
      obtain ⟨hχ1, h1, h2, h3, _⟩ := hs0 χ (mem_filter.1 hχ).1
      exact ⟨hχ1, h1, h2, h3, hz0 χ (mem_filter.1 hχ).1, (mem_filter.1 hχ).2⟩)
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card := by exact_mod_cast card_union_le Z1 Z2
    _ ≤ _ := add_le_add hc1' hc2'

/-! ### The bound at `Q` -/

omit [NeZero q] in
/-- **The integral class at `X = ⌊Q⌋`, `Y = Q^{18/13}`, `λ = Q^{(6/13)(½−σ)+ε/3}`**, for `σ ≤ 11/12` and
`q(T + 2) ≤ Q`: at most `(3200 KG/δ₀ + (KG/δ₀)²C₄)(log Q)¹⁰ Q^{(36/13+4ε)(1−σ)}`, `δ₀ = 5/36`. Both terms carry
`Q^{(24/13)(½−σ)+1+ε/3}`, and `(24/13)(½ − σ) + 1 ≤ (36/13)(1 − σ)` exactly when `σ ≤ 11/12`. -/
theorem bound_class2_ingham {ε C₄ σ T Q : ℝ} (hε0 : 0 ≤ ε) (hC₄ : 0 ≤ C₄) (hσ1 : σ ≤ 11 / 12) (hQ : 8 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) :
    2 * (KG * (Yw (5 / 26) Q) ^ (1 / 2 - σ) / (5 / 36)) * Q ^ (6 / 13 * (1 / 2 - σ) + ε / 3) *
        (MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))) +
      (KG * (Yw (5 / 26) Q) ^ (1 / 2 - σ) / (5 / 36)) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) /
        (Q ^ (6 / 13 * (1 / 2 - σ) + ε / 3)) ^ 2
      ≤ (3200 * (KG / (5 / 36)) + (KG / (5 / 36)) ^ 2 * C₄) * Real.log Q ^ 10 *
        Q ^ ((36 / 13 + 4 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hKG := KG_pos
  set K := KG / (5 / 36) with hK
  have hK0 : 0 < K := by positivity
  set a := 18 / 13 * (1 / 2 - σ) with ha
  set e := 6 / 13 * (1 / 2 - σ) + ε / 3 with he
  set E₂ := 24 / 13 * (1 / 2 - σ) + 1 + ε / 3 with hE₂
  set E := (36 / 13 + 4 * ε) * (1 - σ) with hE
  have hY : (Yw (5 / 26) Q) ^ (1 / 2 - σ) = Q ^ a := by
    unfold Yw; rw [← Real.rpow_mul hQ0.le]; congr 1; rw [ha]; ring
  have hA : KG * (Yw (5 / 26) Q) ^ (1 / 2 - σ) / (5 / 36) = K * Q ^ a := by rw [hY, hK]; ring
  rw [hA]
  -- the mean value and the fourth-moment factor
  have hMV := bound_MV hQ
  have hMV0 : 0 ≤ MV (Xw Q) := by
    unfold MV; have := Real.log_nonneg (by exact_mod_cast Xw_one hQ : (1 : ℝ) ≤ Xw Q); positivity
  have hXQ := Xw_le hQ
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hW : (q : ℝ) * (T + 1) + (Xw Q) ≤ 2 * Q := by nlinarith
  have hW0 : 0 ≤ (q : ℝ) * (T + 1) + (Xw Q) := by positivity
  have hL2 : 2 ≤ Real.log Q := log_ge_two hQ
  have hM1 : MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q)) ≤ 1600 * Real.log Q ^ 5 * Q := by
    calc MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q)) ≤ (800 * Real.log Q ^ 5) * (2 * Q) :=
          mul_le_mul hMV hW hW0 (by positivity)
      _ = 1600 * Real.log Q ^ 5 * Q := by ring
  have hM2 : C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε) ≤ C₄ * Q ^ (1 + ε) := by
    gcongr
  -- the exponents
  have hQa : Q ^ a * Q ^ e * Q = Q ^ E₂ := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add_one hQ0.ne']; congr 1; rw [ha, he, hE₂]; ring
  have hQb : (Q ^ a) ^ 2 * Q ^ (1 + ε) / (Q ^ e) ^ 2 = Q ^ E₂ := by
    rw [← Real.rpow_natCast (Q ^ a), ← Real.rpow_natCast (Q ^ e), ← Real.rpow_mul hQ0.le,
      ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0, ← Real.rpow_sub hQ0]
    congr 1; rw [ha, he, hE₂]; push_cast; ring
  have hEE : Q ^ E₂ ≤ Q ^ E := by
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    rw [hE₂, hE]
    nlinarith
  have hL5 : Real.log Q ^ 5 ≤ Real.log Q ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL10 : 1 ≤ Real.log Q ^ 10 := one_le_pow₀ (by linarith)
  have hQe : 0 < Q ^ e := Real.rpow_pos_of_pos hQ0 e
  have hQE₂ : 0 ≤ Q ^ E₂ := by positivity
  have hpow2 : 0 ≤ (Q ^ a) ^ 2 := by positivity
  calc 2 * (K * Q ^ a) * Q ^ e * (MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))) +
        (K * Q ^ a) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) / (Q ^ e) ^ 2
      ≤ 2 * (K * Q ^ a) * Q ^ e * (1600 * Real.log Q ^ 5 * Q) +
        (K * Q ^ a) ^ 2 * (C₄ * Q ^ (1 + ε)) / (Q ^ e) ^ 2 := by gcongr
    _ = 3200 * K * Real.log Q ^ 5 * (Q ^ a * Q ^ e * Q) +
        K ^ 2 * C₄ * ((Q ^ a) ^ 2 * Q ^ (1 + ε) / (Q ^ e) ^ 2) := by ring
    _ = (3200 * K * Real.log Q ^ 5 + K ^ 2 * C₄) * Q ^ E₂ := by rw [hQa, hQb]; ring
    _ ≤ (3200 * K * Real.log Q ^ 10 + K ^ 2 * C₄ * Real.log Q ^ 10) * Q ^ E := by
        have h1 : 3200 * K * Real.log Q ^ 5 ≤ 3200 * K * Real.log Q ^ 10 :=
          mul_le_mul_of_nonneg_left hL5 (by positivity)
        have h2 : K ^ 2 * C₄ ≤ K ^ 2 * C₄ * Real.log Q ^ 10 := le_mul_of_one_le_right (by positivity) hL10
        exact mul_le_mul (add_le_add h1 h2) hEE hQE₂ (by positivity)
    _ = (3200 * K + K ^ 2 * C₄) * Real.log Q ^ 10 * Q ^ E := by ring

open scoped Classical in
/-- **The middle range `23/36 ≤ σ ≤ 11/12` at `Q = q(T + 6)`**: at most
`Mc(log Q)¹⁰Q^{(36/13+4ε)(1−σ)}` characters `χ ≠ 1` have a zero in `Re s ≥ σ`, `|Im s| ≤ T`, with
`Mc = 16·13³·96·9⁶·71 + 3200 KG/δ₀ + (KG/δ₀)²C₄`, `δ₀ = 5/36`. -/
theorem count_middle {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {σ T : ℝ} (hmid : 23 / 36 ≤ σ) (hle : σ ≤ 11 / 12) (hT : 2 ≤ T) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (5 / 36)) + (KG / (5 / 36)) ^ 2 * C₄)) *
        Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((36 / 13 + 4 * ε) * (1 - σ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ0 : 0 < (q : ℝ) * (T + 6) := by linarith
  have hQ1 : 1 ≤ (q : ℝ) * (T + 6) := by linarith
  have hlam0 : 0 < ((q : ℝ) * (T + 6)) ^ (6 / 13 * (1 / 2 - σ) + ε / 3) := Real.rpow_pos_of_pos hQ0 _
  have hcount := count_nontrivial_ingham hε.le hε1 hC₄0 h4 (c := 5 / 26) (by norm_num)
    (by norm_num : (0 : ℝ) < 5 / 36) (by linarith : 1 / 2 + 5 / 36 ≤ σ) (by linarith) hT
    (le_refl ((q : ℝ) * (T + 6))) hlam0
  have hb1 := bound_class1 (c := 5 / 26) (σ := σ) (by norm_num) (by norm_num) (by linarith) (by linarith) hQ8
  have hb2 := bound_class2_ingham (q := q) hε.le hC₄0 hle hQ8 (by linarith)
    (by nlinarith : (q : ℝ) * (T + 2) ≤ (q : ℝ) * (T + 6))
  have hE1' : ((q : ℝ) * (T + 6)) ^ ((2 + 4 * (5 / 26 : ℝ)) * (1 - σ)) ≤
      ((q : ℝ) * (T + 6)) ^ ((36 / 13 + 4 * ε) * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)
  have hL10 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by
    have := log_ge_two hQ8; positivity
  have hc : (0 : ℝ) ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 := by norm_num
  refine hcount.trans ((add_le_add hb1 hb2).trans ?_)
  have h1 : 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((2 + 4 * (5 / 26 : ℝ)) * (1 - σ)) ≤
      16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((36 / 13 + 4 * ε) * (1 - σ)) :=
    mul_le_mul_of_nonneg_left hE1' (mul_nonneg hc hL10)
  linarith

/-! ### Density over the characters -/

/-- The constant of `charDensity_ingham`. -/
def CDI (C₄ : ℝ) : ℝ :=
  2 ^ 10 + 256 * 3 ^ 10 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (5 / 36)) + (KG / (5 / 36)) ^ 2 * C₄))

open scoped Classical in
/-- **Ingham's density estimate over the characters mod `q`**: for every `0 < ε ≤ 1` there is `C ≥ 0` with
`CharDensity (36/13 + 4ε) 10 C`. Below `σ = 23/36`, where `(36/13)(1 − σ) ≥ 1`, at most `q ≤ qT` characters are
counted; above `11/12` no character `χ ≠ 1` has a zero (round 495's half-plane, `LinnikLindelof.LFunction_ne_zero`);
between, the trivial character and `count_nontrivial_ingham` at `Q = q(T + 6)`, `c = 5/26` (so `Y = Q^{18/13}` and
round 521's polynomial class carries `Q^{(36/13)(1−σ)}`, `bound_class1`) and `λ = Q^{(6/13)(½−σ)+ε/3}`
(`bound_class2_ingham`), with `Q^{ε/3} ≤ Q^{4ε(1−σ)}` since `1 − σ ≥ 1/12`. -/
theorem charDensity_ingham {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ CharDensity (36 / 13 + 4 * ε) 10 C := by
  obtain ⟨C₄', hC₄'⟩ := LinnikFourth.fourth_moment hε hε1
  set C₄ := max C₄' 0 with hC₄def
  have hC₄0 : 0 ≤ C₄ := le_max_right _ _
  have h4all : ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) →
      ∀ T' : ℝ, 0 ≤ T' → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε) := by
    intro q _ R hR T' hT' t ht
    refine (hC₄' q R hR T' hT' t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hKG := KG_pos
  have hCDI0 : 0 ≤ CDI C₄ := by unfold CDI; positivity
  refine ⟨CDI C₄, hCDI0, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  set ℓ := Real.log ((q : ℝ) * T) with hℓdef
  have hℓ : 1 / 2 ≤ ℓ := half_le_log hqT
  set E := (36 / 13 + 4 * ε) * (1 - σ) with hE
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  have hE4 : E ≤ 4 := by rw [hE]; nlinarith
  have hpowE : 0 ≤ ((q : ℝ) * T) ^ E := by positivity
  have hpowE1 : 1 ≤ ((q : ℝ) * T) ^ E := Real.one_le_rpow (by linarith) hE0
  have e10 : ℓ ^ (10 : ℝ) = ℓ ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e10]
  have hCD : 2 ^ 10 ≤ CDI C₄ := by
    unfold CDI
    have : 0 ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (5 / 36)) + (KG / (5 / 36)) ^ 2 * C₄) := by
      positivity
    nlinarith
  have h2ℓ : 1 ≤ 2 ^ 10 * ℓ ^ 10 := by
    have h1 : 1 ≤ (2 * ℓ) ^ 10 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) ≤ (2 * ℓ) ^ 10 := h1
      _ = 2 ^ 10 * ℓ ^ 10 := by ring
  have hCℓ : 1 ≤ CDI C₄ * ℓ ^ 10 := h2ℓ.trans (by gcongr)
  have hsub : (univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
      ⊆ insert 1 (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) := by
    intro χ hχ
    rw [mem_insert]
    by_cases h1 : χ = 1
    · exact Or.inl h1
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, h1, (mem_filter.1 hχ).2⟩)
  have hcard := (card_le_card hsub).trans (card_insert_le _ _)
  have hF : ((univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) + 1 := by exact_mod_cast hcard
  rcases lt_or_ge σ (23 / 36) with hsmall | hmid
  · -- below `23/36`: at most `q ≤ qT ≤ (qT)^E` characters
    have hE1 : 1 ≤ E := by rw [hE]; nlinarith
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ (q : ℝ) * T := by nlinarith
      _ = ((q : ℝ) * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((q : ℝ) * T) ^ E := Real.rpow_le_rpow_of_exponent_le (by linarith) hE1
      _ = ((q : ℝ) * T) ^ E * 1 := (mul_one _).symm
      _ ≤ ((q : ℝ) * T) ^ E * (CDI C₄ * ℓ ^ 10) := by gcongr
      _ = CDI C₄ * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
  rcases lt_or_ge (11 / 12) σ with hbig | hle
  · -- above `11/12`: no character `χ ≠ 1` has a zero
    have hZ : (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro χ - ⟨hχ1, s, hs, -, hz⟩
      exact LinnikLindelof.LFunction_ne_zero hχ1 (by linarith) hz
    rw [hZ, card_empty, Nat.cast_zero, zero_add] at hF
    calc _ ≤ (1 : ℝ) := hF
      _ ≤ ((q : ℝ) * T) ^ E * (CDI C₄ * ℓ ^ 10) := one_le_mul_of_one_le_of_one_le hpowE1 hCℓ
      _ = CDI C₄ * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
  -- between: `count_middle` at `Q = q(T + 6) ≤ 4qT`
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hZ := count_middle hε hε1 hC₄0 (h4all q) hmid hle hT
  have hL0 : 2 ≤ Real.log ((q : ℝ) * (T + 6)) := log_ge_two hQ8
  have hLQ : Real.log ((q : ℝ) * (T + 6)) ≤ 3 * ℓ := by
    have h2 : Real.log ((q : ℝ) * (T + 6)) ≤ Real.log (4 * ((q : ℝ) * T)) := Real.log_le_log (by linarith) hQ4
    rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < q * T).ne'] at h2
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h5 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hqT
    linarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 256 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by linarith) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (4 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 256 * ((q : ℝ) * T) ^ E := by norm_num
  obtain ⟨Mc, hMc⟩ : ∃ x : ℝ, x = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (5 / 36)) + (KG / (5 / 36)) ^ 2 * C₄) :=
    ⟨_, rfl⟩
  rw [← hMc] at hZ
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hCDIe : CDI C₄ = 2 ^ 10 + 256 * 3 ^ 10 * Mc := by rw [hMc]; rfl
  have hL10 : Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ 3 ^ 10 * ℓ ^ 10 := by
    calc Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ (3 * ℓ) ^ 10 := by gcongr
      _ = 3 ^ 10 * ℓ ^ 10 := by ring
  have h1 : 1 ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := one_le_mul_of_one_le_of_one_le hpowE1 h2ℓ
  have hQE0 : 0 ≤ ((q : ℝ) * (T + 6)) ^ E := by positivity
  have hlog0 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by positivity
  have hstep : Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ E ≤
      Mc * (3 ^ 10 * ℓ ^ 10) * (256 * ((q : ℝ) * T) ^ E) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hL10 hMc0) hQE hQE0 (by positivity)
  rw [hCDIe]
  calc _ ≤ _ := hF
    _ ≤ Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ E +
          ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
    _ ≤ Mc * (3 ^ 10 * ℓ ^ 10) * (256 * ((q : ℝ) * T) ^ E) + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := by
        linarith
    _ = (2 ^ 10 + 256 * 3 ^ 10 * Mc) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring

/-! ### Linnik's exponent `36/13 + η` -/

/-- **Linnik's theorem with exponent `36/13 + η`, with no hypothesis.** For every `η > 0` there is `K` such that for
every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{36/13 + η}`: round 520's
`linnik_of_charDensity` fed `charDensity_ingham` at `ε = min(η, 1)/8`. -/
theorem linnik_thirtysix_thirteenths {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (36 / 13 + η) := by
  have hmin : 0 < min η 1 := lt_min hη one_pos
  have hε0 : 0 < min η 1 / 8 := by positivity
  have hε1 : min η 1 / 8 ≤ 1 := by have := min_le_right η 1; linarith
  obtain ⟨C, hC0, hD⟩ := charDensity_ingham hε0 hε1
  obtain ⟨K, hK⟩ := linnik_of_charDensity (by nlinarith : (2 : ℝ) ≤ 36 / 13 + 4 * (min η 1 / 8))
    (by norm_num) hC0 hD (half_pos hη)
  refine ⟨max K 0, fun q _ a ha => ?_⟩
  obtain ⟨p, hp, hpa, hpK⟩ := hK q a ha
  refine ⟨p, hp, hpa, hpK.trans ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hexp : 36 / 13 + 4 * (min η 1 / 8) + η / 2 ≤ 36 / 13 + η := by
    have := min_le_left η 1; linarith
  calc K * (q : ℝ) ^ (36 / 13 + 4 * (min η 1 / 8) + η / 2)
      ≤ max K 0 * (q : ℝ) ^ (36 / 13 + 4 * (min η 1 / 8) + η / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * (q : ℝ) ^ (36 / 13 + η) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hexp) (le_max_right _ _)

end LinnikIngham

#print axioms LinnikIngham.class2_count_ingham
#print axioms LinnikIngham.count_nontrivial_ingham
#print axioms LinnikIngham.charDensity_ingham
#print axioms LinnikIngham.linnik_thirtysix_thirteenths
