/-
# Round 609: Ingham's density estimate with the detector's `c` as a parameter (a staircase below `3/4`)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`charDensity_ingham_c`). For `0 < ε ≤ 1`, `0 ≤ c ≤ 1`, `δ₀ > 0` and a right end `σ₂ ≤ 11/12` with
`(4/3)(1 + 2c)(1/2 − σ₂) + 1 ≤ (2 + 4c)(1 − σ₂)` (that is, `2 + 4c ≥ 3/(2 − σ₂)`, Ingham's curve at `σ₂`), there is
`C ≥ 0` such that for every `q ≥ 1`, `1/2 + δ₀ ≤ σ ≤ σ₂` and `T ≥ 2`, at most `C(qT)^{(2+4c+4ε)(1−σ)}(log qT)^{10}`
characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.

This is round 607's `LinnikIngham73.count_middle73` (`c = 1/12`, `δ₀ = 1/14`, `σ₂ = 5/7`; the top-level
`charDensity_ingham73` adds the trivial count below `4/7` and has its own constant) with `c`, `δ₀` and the range as
parameters (round 610: it named `LinnikIngham73` as the case; review of round 609, F7): round 524's argument
(`LinnikIngham.charDensity_ingham`) with the detector's parameter `c`. The polynomial
class is `Q^{(2+4c)(1−σ)}` (round 521's `bound_class1`), and the integral class, at `X = ⌊Q⌋`, `Y = Q^{1+2c}` and
`λ = Q^{((1+2c)/3)(½−σ)+ε/3}`, is `Q^{(4/3)(1+2c)(½−σ)+1+ε/3}`, at most `Q^{(2+4c+4ε)(1−σ)}` under the exponent
inequality. A constant `2 + 4c` on `[σ₁, σ₂]` with `σ₂ ≤ 2 − 3/(2(1 + 2c))` is then a step of a staircase above
Ingham's curve `3/(2 − σ)`, and the stack's `12/5` curve below `3/4` can be replaced by such a staircase.

* `bound_class2_c`: for `ε ≥ 0`, `C₄ ≥ 0`, `δ₀ > 0`, `σ ≤ 11/12`, the exponent inequality at `σ`, `T ≥ 0`,
  `Q ≥ 8` and `q(T + 2) ≤ Q`, the integral class's bound at those parameters is at most
  `(3200KG/δ₀ + (KG/δ₀)²C₄)(log Q)^{10}Q^{(2+4c+4ε)(1−σ)}`.
* `count_middle_c`: for `0 < ε ≤ 1`, the fourth moment with a constant `C₄ ≥ 0` (the hypothesis `h4`), `0 ≤ c ≤ 1`,
  `δ₀ > 0`, `1/2 + δ₀ ≤ σ ≤ 11/12`, the exponent inequality at `σ` and `T ≥ 2`, at most
  `Mc(log Q)^{10}Q^{(2+4c+4ε)(1−σ)}` characters `χ ≠ 1` have such a zero, `Q = q(T + 6)`.
* `charDensity_ingham_c`: `count_middle_c` with `LinnikFourth.fourth_moment` at `Q ≤ 4qT`, plus the trivial character;
  the exponent inequality at `σ₂` gives it at every `σ ≤ σ₂`, since its two sides differ by a function increasing in
  `σ`.

The file imports `LinnikIngham.lean`.
-/
import LinnikIngham

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikInghamC

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil DirMean

variable {q : ℕ}

/-- **The integral class at `X = ⌊Q⌋`, `Y = Q^{1+2c}`, `λ = Q^{((1+2c)/3)(½−σ)+ε/3}`**, for `ε ≥ 0`, `C₄ ≥ 0`,
`δ₀ > 0`, `σ ≤ 11/12`, `(4/3)(1 + 2c)(½ − σ) + 1 ≤ (2 + 4c)(1 − σ)`, `T ≥ 0`, `Q ≥ 8` and `q(T + 2) ≤ Q`:
the integral class's bound `2AλM₁ + A²M₂/λ²` of `LinnikIngham.class2_count_ingham` is at most
`(3200 KG/δ₀ + (KG/δ₀)²C₄)(log Q)¹⁰ Q^{(2+4c+4ε)(1−σ)}`. Both terms carry `Q^{(4/3)(1+2c)(½−σ)+1+ε/3}`. -/
theorem bound_class2_c {ε C₄ c δ₀ σ T Q : ℝ} (hε0 : 0 ≤ ε) (hC₄ : 0 ≤ C₄) (hδ₀ : 0 < δ₀)
    (hσ1 : σ ≤ 11 / 12) (hexp : 4 / 3 * (1 + 2 * c) * (1 / 2 - σ) + 1 ≤ (2 + 4 * c) * (1 - σ)) (hQ : 8 ≤ Q)
    (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) :
    2 * (KG * (Yw c Q) ^ (1 / 2 - σ) / δ₀) * Q ^ ((1 + 2 * c) / 3 * (1 / 2 - σ) + ε / 3) *
        (MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))) +
      (KG * (Yw c Q) ^ (1 / 2 - σ) / δ₀) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) /
        (Q ^ ((1 + 2 * c) / 3 * (1 / 2 - σ) + ε / 3)) ^ 2
      ≤ (3200 * (KG / δ₀) + (KG / δ₀) ^ 2 * C₄) * Real.log Q ^ 10 *
        Q ^ ((2 + 4 * c + 4 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hKG := KG_pos
  set K := KG / δ₀ with hK
  have hK0 : 0 < K := by positivity
  set a := (1 + 2 * c) * (1 / 2 - σ) with ha
  set e := (1 + 2 * c) / 3 * (1 / 2 - σ) + ε / 3 with he
  set E₂ := 4 / 3 * (1 + 2 * c) * (1 / 2 - σ) + 1 + ε / 3 with hE₂
  set E := (2 + 4 * c + 4 * ε) * (1 - σ) with hE
  have hY : (Yw c Q) ^ (1 / 2 - σ) = Q ^ a := by
    unfold Yw; rw [← Real.rpow_mul hQ0.le]
  have hA : KG * (Yw c Q) ^ (1 / 2 - σ) / δ₀ = K * Q ^ a := by rw [hY, hK]; ring
  rw [hA]
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
/-- **The range `1/2 + δ₀ ≤ σ ≤ 11/12` under the exponent inequality, at `Q = q(T + 6)`**: for `0 < ε ≤ 1`, the fourth
moment with a constant `C₄ ≥ 0` (`h4`), `0 ≤ c ≤ 1`, `δ₀ > 0`, `(4/3)(1 + 2c)(½ − σ) + 1 ≤ (2 + 4c)(1 − σ)` and `T ≥ 2`,
at most `Mc(log Q)¹⁰Q^{(2+4c+4ε)(1−σ)}` characters `χ ≠ 1` have a zero in `Re s ≥ σ`, `|Im s| ≤ T`, with
`Mc = 16·13³·96·9⁶·71 + 3200 KG/δ₀ + (KG/δ₀)²C₄`: `count_nontrivial_ingham` at `c`, round 521's polynomial class
`Q^{(2+4c)(1−σ)}` (`bound_class1`) and `bound_class2_c`. -/
theorem count_middle_c [NeZero q] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {c δ₀ σ T : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hδ₀ : 0 < δ₀) (hmid : 1 / 2 + δ₀ ≤ σ) (hle : σ ≤ 11 / 12)
    (hexp : 4 / 3 * (1 + 2 * c) * (1 / 2 - σ) + 1 ≤ (2 + 4 * c) * (1 - σ)) (hT : 2 ≤ T) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / δ₀) + (KG / δ₀) ^ 2 * C₄)) *
        Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((2 + 4 * c + 4 * ε) * (1 - σ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ0 : 0 < (q : ℝ) * (T + 6) := by linarith
  have hQ1 : 1 ≤ (q : ℝ) * (T + 6) := by linarith
  have hlam0 : 0 < ((q : ℝ) * (T + 6)) ^ ((1 + 2 * c) / 3 * (1 / 2 - σ) + ε / 3) := Real.rpow_pos_of_pos hQ0 _
  have hcount := count_nontrivial_ingham hε.le hε1 hC₄0 h4 (c := c) hc0 hδ₀ hmid (by linarith) hT
    (le_refl ((q : ℝ) * (T + 6))) hlam0
  have hb1 := bound_class1 (c := c) (σ := σ) hc0 hc1 (by linarith) (by linarith) hQ8
  have hb2 := bound_class2_c (q := q) (ε := ε) (C₄ := C₄) (c := c) hε.le hC₄0 hδ₀ hle hexp hQ8 (by linarith)
    (by nlinarith : (q : ℝ) * (T + 2) ≤ (q : ℝ) * (T + 6))
  have hE1' : ((q : ℝ) * (T + 6)) ^ ((2 + 4 * c) * (1 - σ)) ≤
      ((q : ℝ) * (T + 6)) ^ ((2 + 4 * c + 4 * ε) * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)
  have hL10 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by
    have := log_ge_two hQ8; positivity
  have hc : (0 : ℝ) ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 := by norm_num
  refine hcount.trans ((add_le_add hb1 hb2).trans ?_)
  have h1 : 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((2 + 4 * c) * (1 - σ)) ≤
      16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((2 + 4 * c + 4 * ε) * (1 - σ)) :=
    mul_le_mul_of_nonneg_left hE1' (mul_nonneg hc hL10)
  linarith

/-- The constant of `charDensity_ingham_c`. -/
def CDIc (δ₀ C₄ : ℝ) : ℝ :=
  2 ^ 10 + 1024 * 3 ^ 10 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / δ₀) + (KG / δ₀) ^ 2 * C₄))

open scoped Classical in
/-- **Ingham's density estimate with exponent `2 + 4c + 4ε` on `[1/2 + δ₀, σ₂]`**: for `0 < ε ≤ 1`, `0 ≤ c ≤ 1`,
`δ₀ > 0` and `σ₂ ≤ 11/12` with `(4/3)(1 + 2c)(½ − σ₂) + 1 ≤ (2 + 4c)(1 − σ₂)`, there is `C ≥ 0` such that for every
`q ≥ 1`, `1/2 + δ₀ ≤ σ ≤ σ₂` and `T ≥ 2` at most `C(qT)^{(2+4c+4ε)(1−σ)}(log qT)^{10}` characters mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`: the trivial character and `count_middle_c` at `Q = q(T + 6) ≤ 4qT`. -/
theorem charDensity_ingham_c {ε c δ₀ σ₂ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hδ₀ : 0 < δ₀)
    (hσ₂ : σ₂ ≤ 11 / 12) (hexp : 4 / 3 * (1 + 2 * c) * (1 / 2 - σ₂) + 1 ≤ (2 + 4 * c) * (1 - σ₂)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 1 / 2 + δ₀ ≤ σ → σ ≤ σ₂ → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((2 + 4 * c + 4 * ε) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
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
  have hCDI0 : 0 ≤ CDIc δ₀ C₄ := by unfold CDIc; positivity
  refine ⟨CDIc δ₀ C₄, hCDI0, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  set ℓ := Real.log ((q : ℝ) * T) with hℓdef
  have hℓ : 1 / 2 ≤ ℓ := half_le_log hqT
  set E := (2 + 4 * c + 4 * ε) * (1 - σ) with hE
  have hσhalf : 1 / 2 ≤ σ := by linarith
  have hσ11 : σ ≤ 11 / 12 := hσ1.trans hσ₂
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  have hE4 : E ≤ 5 := by rw [hE]; nlinarith
  have hpowE : 0 ≤ ((q : ℝ) * T) ^ E := by positivity
  have hpowE1 : 1 ≤ ((q : ℝ) * T) ^ E := Real.one_le_rpow (by linarith) hE0
  have e10 : ℓ ^ (10 : ℝ) = ℓ ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e10]
  have hCD : 2 ^ 10 ≤ CDIc δ₀ C₄ := by
    unfold CDIc
    have : 0 ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / δ₀) + (KG / δ₀) ^ 2 * C₄) := by
      positivity
    nlinarith
  have h2ℓ : 1 ≤ 2 ^ 10 * ℓ ^ 10 := by
    have h1 : 1 ≤ (2 * ℓ) ^ 10 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) ≤ (2 * ℓ) ^ 10 := h1
      _ = 2 ^ 10 * ℓ ^ 10 := by ring
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
  -- the exponent inequality at `σ ≤ σ₂`: the difference of its sides increases with `σ`
  have hexpσ : 4 / 3 * (1 + 2 * c) * (1 / 2 - σ) + 1 ≤ (2 + 4 * c) * (1 - σ) := by nlinarith
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hZ := count_middle_c hε hε1 hC₄0 (h4all q) hc0 hc1 hδ₀ hσ hσ11 hexpσ hT
  have hL0 : 2 ≤ Real.log ((q : ℝ) * (T + 6)) := log_ge_two hQ8
  have hLQ : Real.log ((q : ℝ) * (T + 6)) ≤ 3 * ℓ := by
    have h2 : Real.log ((q : ℝ) * (T + 6)) ≤ Real.log (4 * ((q : ℝ) * T)) := Real.log_le_log (by linarith) hQ4
    rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < q * T).ne'] at h2
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h5 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hqT
    linarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 1024 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by linarith) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (5 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 1024 * ((q : ℝ) * T) ^ E := by norm_num
  obtain ⟨Mc, hMc⟩ : ∃ x : ℝ,
      x = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / δ₀) + (KG / δ₀) ^ 2 * C₄) := ⟨_, rfl⟩
  rw [← hMc] at hZ
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hCDIe : CDIc δ₀ C₄ = 2 ^ 10 + 1024 * 3 ^ 10 * Mc := by rw [hMc]; rfl
  have hL10 : Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ 3 ^ 10 * ℓ ^ 10 := by
    calc Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ (3 * ℓ) ^ 10 := by gcongr
      _ = 3 ^ 10 * ℓ ^ 10 := by ring
  have h1 : 1 ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := one_le_mul_of_one_le_of_one_le hpowE1 h2ℓ
  have hQE0 : 0 ≤ ((q : ℝ) * (T + 6)) ^ E := by positivity
  have hlog0 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by positivity
  have hstep : Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ E ≤
      Mc * (3 ^ 10 * ℓ ^ 10) * (1024 * ((q : ℝ) * T) ^ E) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hL10 hMc0) hQE hQE0 (by positivity)
  rw [hCDIe]
  calc _ ≤ _ := hF
    _ ≤ Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ E +
          ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
    _ ≤ Mc * (3 ^ 10 * ℓ ^ 10) * (1024 * ((q : ℝ) * T) ^ E) + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := by
        linarith
    _ = (2 ^ 10 + 1024 * 3 ^ 10 * Mc) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring

end LinnikInghamC

#print axioms LinnikInghamC.charDensity_ingham_c
