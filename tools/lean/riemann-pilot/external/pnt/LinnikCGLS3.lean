/-
# Round 678: their Proposition 11.1, `CGLS3` from `CGLP81` and `CGLT101` (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Proposition 11.1: "Let (qT)^{2/3}/2 ≤ N ≤ qT. Then we have S₃ ⪅ (qT)²|W|^{3/2} + qT|W|N^{3−2σ} +
qT|W|²N^{3/2−σ} + (qT)^{9/8}|W|^{29/16}N^{3/2−σ}." (text layer lines 5522–5533.) The end of their proof: "Since
M₂ ⪅ qT/N, we get (11.2) S₃ ⪅ (qT)²|W|^{3/2} + qTN|W|^{1/2}E(W)^{1/2}." (lines 5865–5866) and "Finally, inserting
the energy bound established in Section 10 (see Proposition 10.2) into the above inequality yields the result."
(lines 5867–5868). In these, spaces are restored and the subscripts, exponents and stacked fractions transcribed.

The stack's form.
* `CGLS3` is round 639's displayed hypothesis: their Proposition 11.1 at one point per character, for sums over
  `S ⊆ [6N/5, 9N/5]`, with the factor `C(qTN)^ε`. Its condition `7/10 ≤ σ ≤ 4/5` is not used here.
* Round 667's `S3_le_112` is their (11.2) from `CGLP81`, with parameters `X`, `M` and three orders, and with the
  three errors of round 657's `prop72`, which their `⪅` absorbs. The stack takes `X = (qT)^{ε′}`,
  `ε′ = min(1/12, ε/16)`, and `M = ⌊XqT/N⌋`, their `M₂ ⪅ qT/N`: then `NM ≤ XqT` (`M_props`), and `2M ≤ (qT)^{3/4}`
  for `qT ≥ 64` (`two_M_le`), so `ϖ = 3/4`. The factor `X` enters as `X⁴ ≤ (qT)^{ε/4}`.
* The orders: `2(k₀ + 3)` with `k₀ = ⌈1/ε′⌉` for the energy's smoothing term, which is then at most `(qT)²|R|^{3/2}`
  (`term3_le`); `K₀ + 3` with `K₀ = ⌈5/(2ε′)⌉` for the first error (`E1_le`); and `k_t + 2` with `k_t = ⌈4/ε′⌉` for
  the third (`tauM_le`, `E3_le`). The second error is at most `(C_δB)³(qT)^{3δ}(qT)²|R|^{3/2}` (`E2_le`, from round
  649's `muP_sub_mu0_le_rpow`).
* The energy term. Their "inserting the energy bound" uses their Proposition 10.2 under its alternative, `|W| ≥
  (qT)^{2/3}` or `E(W)^{1/8}N ≥ (qT)^{1/2}|W|^{5/8}`; outside it, their Remark 10.3 bounds the term by `(qT)²|W|^{3/2}`.
  `energy_term` does both, with round 677's `prop102` and round 676's `remark103`.
* The small range `qT < max(Q₀, 64)`, with `Q₀` the threshold of `S3_le_112`: `S₃ ≤ |R|³(N + 1)³` (`S3_le_crude`),
  at most a constant times `(qT)²|R|^{3/2}` (`small_case`).

Plain statements, with `q ≥ 1`, `Q = qT`, `r = |R|`, `E` round 659's `energy`, `Φ = qTN`, and `W` the bracket of
`CGLS3`, `Q²r^{3/2} + QrN^{3−2σ} + Qr²N^{3/2−σ} + Q^{9/8}r^{29/16}N^{3/2−σ}`.
* `S3_le_crude`: `S₃ ≤ |R|³(N + 1)³` for `N > 0`.
* `id_one`, `id_two`, `id_three`, `energy_term`: for `r, E ≥ 0`, `Q ≥ 1`, `N ≥ Q^{2/3}/2`, `Λ ≥ 1` and `C₂ ≥ 0`, if
  their Proposition 10.2's alternative gives `E ≤ C₂Λ²(rN^{4−4σ} + r^{21/8}Q^{1/4}N^{1−2σ} + r³N^{1−2σ})`, then
  `QN√r√E ≤ (8 + √C₂)ΛW`.
* `natlog_le_rpow`, `M_props`, `two_M_le`, `rpow_le_pow_X`, `orders`: the parameters.
* `cube_le`, `natCast_le_rpow`, `E1_le`, `E2_le`, `tauM_le`, `E3_le`: the three errors.
* `sqrt_main_le`, `sqrt_Gq_le`, `term3_le`, `main_le`, `factors_le`, `main_final`, `main_part`: the main term,
  at most `K_mΦ^εW`.
* `errors_combine`, `errors_part`: the errors, at most `(K₁ + K₂ + K₃)Φ^εW`.
* `small_case`, `combine3`, `final_large`, `final_small`: the two ranges.
* `cgls3`: `CGLP81 → CGLT101 → CGLS3`.
* `prop31_pt`: round 637's `CGLProp31`, their Proposition 3.1 at one point per character, from `CGLP81` and
  `CGLT101`, through round 639's `third_of_s23` with round 644's `cgls2`, and round 638's `prop31_of_third`.
* `linnik_225c_pt`, `linnik_226c_pt`: Linnik's theorem with the exponents `9/4` and `226/100` from `CGLP81` and
  `CGLT101`, by round 644's `linnik_225c_s3` and `linnik_226c_s3`.

The file imports `LinnikCGLEps.lean`.
-/

import LinnikCGLEps

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLS3

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLS23 LinnikCGLDiag LinnikCGLTrunc LinnikCGLP71
  LinnikCGLP72 LinnikCGLRt LinnikCGLMom4 LinnikCGLJ LinnikCGL112 LinnikCGLT101 LinnikCGLCase LinnikCGLEps

/-! ### A crude bound -/

/-- `S₃ ≤ |R|³(N + 1)³` for `N > 0`: the Gram entries are at most `N + 1` (round 650's `norm_gramP_le`), and
`3μ₀‖E‖_F² ≥ 0`. -/
lemma S3_le_crude {ι : Type*} [DecidableEq ι] {q : ℕ} {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) : S3 q N R χ t ≤ (R.card : ℝ) ^ 3 * (N + 1) ^ 3 := by
  have hB : ∀ i j k : ι, ‖(if i = j ∧ j = k then 0 else
      gramP N χ t i j * gramP N χ t j k * gramP N χ t k i : ℂ)‖ ≤ (N + 1) ^ 3 := by
    intro i j k
    split_ifs
    · rw [norm_zero]; positivity
    · rw [norm_mul, norm_mul]
      have h1 := norm_gramP_le hN χ t i j
      have h2 := norm_gramP_le hN χ t j k
      have h3 := norm_gramP_le hN χ t k i
      have h12 : ‖gramP N χ t i j‖ * ‖gramP N χ t j k‖ ≤ (N + 1) * (N + 1) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
      calc ‖gramP N χ t i j‖ * ‖gramP N χ t j k‖ * ‖gramP N χ t k i‖ ≤ (N + 1) * (N + 1) * (N + 1) :=
            mul_le_mul h12 h3 (norm_nonneg _) (by positivity)
        _ = (N + 1) ^ 3 := by ring
  have h1 : X3 N R χ t ≤ (R.card : ℝ) ^ 3 * (N + 1) ^ 3 := by
    unfold X3
    refine (Complex.re_le_norm _).trans ?_
    calc ‖∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (if i = j ∧ j = k then 0 else
          gramP N χ t i j * gramP N χ t j k * gramP N χ t k i : ℂ)‖
        ≤ ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (N + 1) ^ 3 := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hB i j k)
      _ = (R.card : ℝ) ^ 3 * (N + 1) ^ 3 := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have h2 : 0 ≤ 3 * mu0 q N * frobOff N R χ t :=
    mul_nonneg (mul_nonneg (by norm_num) (mu0_nonneg q hN.le)) (frobOff_nonneg N R χ t)
  unfold S3
  linarith

/-! ### The energy term of their (11.2) -/

/-- `QN√r√(rN^{4−4σ}) = QrN^{3−2σ}` for `N > 0` and `r ≥ 0`. -/
lemma id_one {Q N r σ : ℝ} (hN : 0 < N) (hr : 0 ≤ r) :
    Q * N * √r * √(r * N ^ (4 - 4 * σ)) = Q * r * N ^ (3 - 2 * σ) := by
  rw [Real.sqrt_mul hr, Real.sqrt_eq_rpow (N ^ (4 - 4 * σ)), ← Real.rpow_mul hN.le,
    show (3 : ℝ) - 2 * σ = 1 + (4 - 4 * σ) * (1 / 2) by ring, Real.rpow_add hN, Real.rpow_one]
  have h2 : √r * √r = r := Real.mul_self_sqrt hr
  calc Q * N * √r * (√r * N ^ ((4 - 4 * σ) * (1 / 2))) =
        Q * (√r * √r) * (N * N ^ ((4 - 4 * σ) * (1 / 2))) := by ring
    _ = Q * r * (N * N ^ ((4 - 4 * σ) * (1 / 2))) := by rw [h2]

/-- `QN√r√(r^{21/8}Q^{1/4}N^{1−2σ}) = Q^{9/8}r^{29/16}N^{3/2−σ}` for `Q, N > 0` and `r ≥ 0`. -/
lemma id_two {Q N r σ : ℝ} (hQ : 0 < Q) (hN : 0 < N) (hr : 0 ≤ r) :
    Q * N * √r * √(r ^ (21 / 8 : ℝ) * Q ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ)) =
      Q ^ (9 / 8 : ℝ) * r ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) := by
  have ha : 0 ≤ r ^ (21 / 8 : ℝ) := by positivity
  have hb : 0 ≤ Q ^ (1 / 4 : ℝ) := by positivity
  rw [Real.sqrt_mul (mul_nonneg ha hb) (N ^ (1 - 2 * σ)), Real.sqrt_mul ha (Q ^ (1 / 4 : ℝ)),
    Real.sqrt_eq_rpow (r ^ (21 / 8 : ℝ)), Real.sqrt_eq_rpow (Q ^ (1 / 4 : ℝ)), Real.sqrt_eq_rpow (N ^ (1 - 2 * σ)),
    Real.sqrt_eq_rpow r, ← Real.rpow_mul hr, ← Real.rpow_mul hQ.le, ← Real.rpow_mul hN.le]
  have hQ' : Q ^ (9 / 8 : ℝ) = Q * Q ^ ((1 / 4 : ℝ) * (1 / 2)) := by
    rw [show (9 / 8 : ℝ) = 1 + (1 / 4) * (1 / 2) by norm_num, Real.rpow_add hQ, Real.rpow_one]
  have hr' : r ^ (29 / 16 : ℝ) = r ^ (1 / 2 : ℝ) * r ^ ((21 / 8 : ℝ) * (1 / 2)) := by
    rw [← Real.rpow_add' hr (by norm_num)]
    norm_num
  have hN' : N ^ (3 / 2 - σ) = N * N ^ ((1 - 2 * σ) * (1 / 2)) := by
    rw [show (3 / 2 : ℝ) - σ = 1 + (1 - 2 * σ) * (1 / 2) by ring, Real.rpow_add hN, Real.rpow_one]
  rw [hQ', hr', hN']
  ring

/-- `QN√r√(r³N^{1−2σ}) = Qr²N^{3/2−σ}` for `N > 0` and `r ≥ 0`. -/
lemma id_three {Q N r σ : ℝ} (hN : 0 < N) (hr : 0 ≤ r) :
    Q * N * √r * √(r ^ 3 * N ^ (1 - 2 * σ)) = Q * r ^ 2 * N ^ (3 / 2 - σ) := by
  rw [Real.sqrt_mul (pow_nonneg hr 3) (N ^ (1 - 2 * σ)), Real.sqrt_eq_rpow (N ^ (1 - 2 * σ)),
    ← Real.rpow_mul hN.le]
  have h1 : √r * √(r ^ 3) = r ^ 2 := by
    rw [← Real.sqrt_mul hr, show r * r ^ 3 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (pow_nonneg hr 2)]
  have hN' : N ^ (3 / 2 - σ) = N * N ^ ((1 - 2 * σ) * (1 / 2)) := by
    rw [show (3 / 2 : ℝ) - σ = 1 + (1 - 2 * σ) * (1 / 2) by ring, Real.rpow_add hN, Real.rpow_one]
  rw [hN']
  calc Q * N * √r * (√(r ^ 3) * N ^ ((1 - 2 * σ) * (1 / 2))) =
        Q * (√r * √(r ^ 3)) * (N * N ^ ((1 - 2 * σ) * (1 / 2))) := by ring
    _ = Q * r ^ 2 * (N * N ^ ((1 - 2 * σ) * (1 / 2))) := by rw [h1]

/-- **The energy term of their (11.2)**: for `r, E ≥ 0`, `Q ≥ 1`, `N ≥ Q^{2/3}/2`, `Λ ≥ 1` and `C₂ ≥ 0`, if their
Proposition 10.2's alternative gives `E ≤ C₂Λ²(rN^{4−4σ} + r^{21/8}Q^{1/4}N^{1−2σ} + r³N^{1−2σ})`, then
`QN√r√E ≤ (8 + √C₂)Λ(Q²r^{3/2} + QrN^{3−2σ} + Qr²N^{3/2−σ} + Q^{9/8}r^{29/16}N^{3/2−σ})`. Outside the alternative,
round 676's `remark103` gives `QN√r√E ≤ 8Q²r^{3/2}`. -/
lemma energy_term {r E Q N σ C₂ Λ : ℝ} (hr : 0 ≤ r) (hE : 0 ≤ E) (hQ : 1 ≤ Q) (hN : Q ^ (2 / 3 : ℝ) / 2 ≤ N)
    (hΛ : 1 ≤ Λ) (hC₂ : 0 ≤ C₂)
    (h102 : (Q ^ (2 / 3 : ℝ) ≤ r ∨ Q ^ (1 / 2 : ℝ) * r ^ (5 / 8 : ℝ) ≤ E ^ (1 / 8 : ℝ) * N) →
      E ≤ C₂ * Λ ^ 2 * (r * N ^ (4 - 4 * σ) + r ^ (21 / 8 : ℝ) * Q ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) +
        r ^ 3 * N ^ (1 - 2 * σ))) :
    Q * N * √r * √E ≤ (8 + √C₂) * Λ * (Q ^ 2 * r ^ (3 / 2 : ℝ) + Q * r * N ^ (3 - 2 * σ) +
      Q * r ^ 2 * N ^ (3 / 2 - σ) + Q ^ (9 / 8 : ℝ) * r ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hN0 : 0 < N := by
    have : 0 < Q ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hQ0 _
    linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hsC : 0 ≤ √C₂ := Real.sqrt_nonneg _
  have hW1 : 0 ≤ Q ^ 2 * r ^ (3 / 2 : ℝ) := by positivity
  have hW : 0 ≤ Λ * (Q ^ 2 * r ^ (3 / 2 : ℝ) + Q * r * N ^ (3 - 2 * σ) + Q * r ^ 2 * N ^ (3 / 2 - σ) +
      Q ^ (9 / 8 : ℝ) * r ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ)) := by positivity
  have hQNr : 0 ≤ Q * N * √r := by positivity
  by_cases halt : Q ^ (2 / 3 : ℝ) ≤ r ∨ Q ^ (1 / 2 : ℝ) * r ^ (5 / 8 : ℝ) ≤ E ^ (1 / 8 : ℝ) * N
  · have hE' := h102 halt
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = r * N ^ (4 - 4 * σ) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = r ^ (21 / 8 : ℝ) * Q ^ (1 / 4 : ℝ) * N ^ (1 - 2 * σ) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = r ^ 3 * N ^ (1 - 2 * σ) := ⟨_, rfl⟩
    rw [← ha, ← hb, ← hc] at hE'
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hsE : √E ≤ √C₂ * Λ * (√a + √b + √c) := by
      have h1 : √E ≤ √(C₂ * Λ ^ 2 * (a + b + c)) := Real.sqrt_le_sqrt hE'
      have h2 : √(C₂ * Λ ^ 2 * (a + b + c)) = √C₂ * Λ * √(a + b + c) := by
        rw [Real.sqrt_mul (by positivity) (a + b + c), Real.sqrt_mul hC₂ (Λ ^ 2), Real.sqrt_sq hΛ0]
      have h3 : √(a + b + c) ≤ √a + √b + √c := by
        refine (sqrt_add_le (by positivity) hc0).trans ?_
        have := sqrt_add_le ha0 hb0
        linarith
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    have h4 := mul_le_mul_of_nonneg_left hsE hQNr
    have e : Q * N * √r * (√C₂ * Λ * (√a + √b + √c)) =
        √C₂ * Λ * (Q * N * √r * √a + Q * N * √r * √b + Q * N * √r * √c) := by ring
    rw [e, ha, hb, hc, id_one hN0 hr, id_two hQ0 hN0 hr, id_three hN0 hr] at h4
    have h5 : 0 ≤ √C₂ * Λ * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by positivity
    nlinarith
  · push Not at halt
    obtain ⟨hr1, hr2⟩ := halt
    have h := remark103 hr hE hQ hN hr1.le hr2.le
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
    have h6 : 8 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) ≤ (8 + √C₂) * Λ * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by
      have h7 : 0 ≤ √C₂ * Λ := by positivity
      have : (8 : ℝ) ≤ (8 + √C₂) * Λ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hW1
    have h8 : 0 ≤ (8 + √C₂) * (Λ * (Q * r * N ^ (3 - 2 * σ) + Q * r ^ 2 * N ^ (3 / 2 - σ) +
        Q ^ (9 / 8 : ℝ) * r ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ))) := by positivity
    nlinarith

/-! ### The parameters -/

/-- `⌊log₂M⌋ + 1 ≤ (1/(δ log 2) + 1)Y^δ` for `1 ≤ M ≤ Y` and `δ > 0`, from `log Y ≤ Y^δ/δ`. -/
lemma natlog_le_rpow {M : ℕ} {Y δ : ℝ} (hM : 1 ≤ M) (hMY : (M : ℝ) ≤ Y) (hδ : 0 < δ) :
    (Nat.log 2 M : ℝ) + 1 ≤ (1 / (δ * Real.log 2) + 1) * Y ^ δ := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hY1 : 1 ≤ Y := hM1.trans hMY
  have hYδ : 1 ≤ Y ^ δ := Real.one_le_rpow hY1 hδ.le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 (by omega)
  have h2 : (2 : ℝ) ^ Nat.log 2 M ≤ Y := by
    have : ((2 ^ Nat.log 2 M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have h3 : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log Y := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have h4 : Real.log Y ≤ Y ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ
  have h5 : (Nat.log 2 M : ℝ) ≤ 1 / (δ * Real.log 2) * Y ^ δ := by
    rw [← le_div_iff₀ hl2] at h3
    calc (Nat.log 2 M : ℝ) ≤ Real.log Y / Real.log 2 := h3
      _ ≤ Y ^ δ / δ / Real.log 2 := by gcongr
      _ = 1 / (δ * Real.log 2) * Y ^ δ := by field_simp
  nlinarith

/-- With `M = ⌊XQ/N⌋` for `X ≥ 1` and `0 < N ≤ Q`: `1 ≤ M`, `NM ≤ XQ` and `XQ/(2N) ≤ M`. -/
lemma M_props {X Q N : ℝ} (hX : 1 ≤ X) (hN : 0 < N) (hNQ : N ≤ Q) :
    1 ≤ ⌊X * Q / N⌋₊ ∧ N * ⌊X * Q / N⌋₊ ≤ X * Q ∧ X * Q / (2 * N) ≤ ⌊X * Q / N⌋₊ := by
  have hy : 1 ≤ X * Q / N := by
    rw [le_div_iff₀ hN]
    nlinarith
  have hfl : (⌊X * Q / N⌋₊ : ℝ) ≤ X * Q / N := Nat.floor_le (by linarith)
  have hlt := Nat.lt_floor_add_one (X * Q / N)
  have hM1 : 1 ≤ ⌊X * Q / N⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hM1' : (1 : ℝ) ≤ ⌊X * Q / N⌋₊ := by exact_mod_cast hM1
  refine ⟨hM1, ?_, ?_⟩
  · have e : N * (X * Q / N) = X * Q := by field_simp
    calc N * (⌊X * Q / N⌋₊ : ℝ) ≤ N * (X * Q / N) := mul_le_mul_of_nonneg_left hfl hN.le
      _ = X * Q := e
  · have e : X * Q / (2 * N) = X * Q / N / 2 := by rw [div_div, mul_comm N 2]
    rw [e]
    linarith

/-- `2M ≤ Q^{3/4}` for `Q ≥ 64`, `N ≥ Q^{2/3}/2`, `X = Q^{ε′}` with `ε′ ≤ 1/12`, and `NM ≤ XQ`. -/
lemma two_M_le {Q N X ε' : ℝ} {M : ℕ} (hQ : 64 ≤ Q) (hN : Q ^ (2 / 3 : ℝ) / 2 ≤ N) (hX : X = Q ^ ε')
    (hε'1 : ε' ≤ 1 / 12) (hNM : N * M ≤ X * Q) : 2 * (M : ℝ) ≤ Q ^ (3 / 4 : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have h4 : 4 ≤ Q ^ (1 / 3 : ℝ) := by
    have e : ((4 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 4 := (pow_rpow_eq (by norm_num) 3 1 (by norm_num)).trans (pow_one 4)
    calc (4 : ℝ) = ((4 : ℝ) ^ 3) ^ (1 / 3 : ℝ) := e.symm
      _ ≤ Q ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hN0 : 0 < N := by
    have : 0 < Q ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hQ0 _
    linarith
  have e13 : Q ^ (1 / 3 : ℝ) * Q ^ (2 / 3 : ℝ) = Q := by
    rw [← Real.rpow_add hQ0]; norm_num
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- `2MN ≤ 2XQ ≤ 4XQ^{1/3}N`
  have h1 : 2 * (M : ℝ) * N ≤ 4 * X * Q ^ (1 / 3 : ℝ) * N := by
    have h13 : 0 ≤ Q ^ (1 / 3 : ℝ) := by positivity
    have : X * Q ≤ 2 * X * Q ^ (1 / 3 : ℝ) * N := by
      have h5 : Q ≤ 2 * Q ^ (1 / 3 : ℝ) * N := by nlinarith
      nlinarith
    nlinarith
  have h2 : 2 * (M : ℝ) ≤ 4 * X * Q ^ (1 / 3 : ℝ) := le_of_mul_le_mul_right h1 hN0
  -- `4XQ^{1/3} ≤ Q^{1/3}·Q^{1/12}·Q^{1/3} ≤ Q^{3/4}`
  have h3 : X ≤ Q ^ (1 / 12 : ℝ) := by
    rw [hX]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hε'1
  have e : Q ^ (1 / 3 : ℝ) * Q ^ (1 / 12 : ℝ) * Q ^ (1 / 3 : ℝ) = Q ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; norm_num
  have h13 : 0 ≤ Q ^ (1 / 3 : ℝ) := by positivity
  have h6 : 4 * X * Q ^ (1 / 3 : ℝ) ≤ Q ^ (1 / 3 : ℝ) * Q ^ (1 / 12 : ℝ) * Q ^ (1 / 3 : ℝ) := by
    have h7 : 4 * X ≤ Q ^ (1 / 3 : ℝ) * Q ^ (1 / 12 : ℝ) := by
      have : 0 ≤ Q ^ (1 / 12 : ℝ) := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right h7 h13
  linarith

/-- `(Q^{ε′})^n ≥ Q^a` for `Q ≥ 1` and `a ≤ ε′n`. -/
lemma rpow_le_pow_X {Q ε' a : ℝ} {n : ℕ} (hQ : 1 ≤ Q) (h : a ≤ ε' * n) : Q ^ a ≤ (Q ^ ε') ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hQ h

/-! ### The errors of their Proposition 7.2 -/

/-- `r³ ≤ Q^{3/2}r^{3/2}` for `0 ≤ r ≤ Q`. -/
lemma cube_le {r Q : ℝ} (hr : 0 ≤ r) (hrQ : r ≤ Q) : r ^ 3 ≤ Q ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) := by
  have e : r ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [← Real.rpow_add' hr (by norm_num), show (3 / 2 : ℝ) + 3 / 2 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr hrQ (by norm_num)) (by positivity)

/-- `r ≤ r^{3/2}` for `r ∈ ℕ`. -/
lemma natCast_le_rpow (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)

/-- **The first error** of round 657's `prop72`, `3(2M)³E71`: for `q, T ≥ 1`, `N, X > 0`, `NM ≤ XqT`, `|R| ≤ qT`
and `X³(qT)^{5/2} ≤ X^{K′}`, at most `54C_J(K′)(2π)^{−K′}(qT)²|R|^{3/2}`. -/
lemma E1_le {ι : Type*} {q : ℕ} (R : Finset ι) {N X T : ℝ} {M K' : ℕ} (hq : 1 ≤ (q : ℝ)) (hT : 1 ≤ T)
    (hN : 0 < N) (hX : 0 < X) (hNM : N * M ≤ X * ((q : ℝ) * T)) (hR : (R.card : ℝ) ≤ (q : ℝ) * T)
    (hXK : X ^ 3 * ((q : ℝ) * T) ^ (5 / 2 : ℝ) ≤ X ^ K') :
    3 * (2 * (M : ℝ)) ^ 3 * E71 q N R X K' ≤
      54 * (CJ K' / (2 * π) ^ K') * (((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ)) := by
  unfold E71
  have hq0 : 0 < (q : ℝ) := by linarith
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφ0 : (0 : ℝ) ≤ q.totient := by positivity
  have hCJ : 0 ≤ CJ K' / (2 * π) ^ K' := by have := CJ_nonneg K'; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) * T := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (R.card : ℝ) := ⟨_, rfl⟩
  rw [← hQ] at hNM hR hXK ⊢
  rw [← hr] at hR ⊢
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_mul_of_one_le_of_one_le hq hT
  have hQ0 : 0 < Q := by linarith
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have e : 3 * (2 * (M : ℝ)) ^ 3 * ((N / q) ^ 3 * (9 / 4 * (CJ K' / (2 * π * X) ^ K' *
      ((q.totient : ℝ) ^ 3 * r ^ 3)))) =
      54 * (CJ K' / (2 * π) ^ K') * (((M : ℝ) * N / q) ^ 3 * ((q.totient : ℝ) ^ 3 * r ^ 3) / X ^ K') := by
    rw [mul_pow (2 * π) X K']
    field_simp
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hXK0 : 0 < X ^ K' := by positivity
  rw [div_le_iff₀ hXK0]
  have h1 : (M : ℝ) * N / q ≤ X * T := by
    rw [div_le_iff₀ hq0]
    have e2 : X * Q = X * T * q := by rw [hQ]; ring
    linarith
  have hMN0 : (0 : ℝ) ≤ M * N / q := by positivity
  have h3 := cube_le hr0 hR
  have h4 : (q.totient : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ hφ0 hφ 3
  have h5 : ((M : ℝ) * N / q) ^ 3 ≤ (X * T) ^ 3 := pow_le_pow_left₀ hMN0 h1 3
  have h6 : ((M : ℝ) * N / q) ^ 3 * ((q.totient : ℝ) ^ 3 * r ^ 3) ≤
      (X * T) ^ 3 * ((q : ℝ) ^ 3 * (Q ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ))) :=
    mul_le_mul h5 (mul_le_mul h4 h3 (by positivity) (by positivity)) (by positivity) (by positivity)
  have e3 : Q ^ 3 * Q ^ (3 / 2 : ℝ) = Q ^ (5 / 2 : ℝ) * Q ^ 2 := by
    rw [← Real.rpow_natCast Q 3, ← Real.rpow_natCast Q 2, ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    norm_num
  have e4 : (X * T) ^ 3 * ((q : ℝ) ^ 3 * (Q ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ))) =
      X ^ 3 * Q ^ (5 / 2 : ℝ) * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by
    calc (X * T) ^ 3 * ((q : ℝ) ^ 3 * (Q ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ))) =
          X ^ 3 * (((q : ℝ) * T) ^ 3 * Q ^ (3 / 2 : ℝ)) * r ^ (3 / 2 : ℝ) := by ring
      _ = X ^ 3 * (Q ^ 3 * Q ^ (3 / 2 : ℝ)) * r ^ (3 / 2 : ℝ) := by rw [hQ]
      _ = X ^ 3 * Q ^ (5 / 2 : ℝ) * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by rw [e3]; ring
  have h7 : X ^ 3 * Q ^ (5 / 2 : ℝ) * (Q ^ 2 * r ^ (3 / 2 : ℝ)) ≤ X ^ K' * (Q ^ 2 * r ^ (3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hXK (by positivity)
  have e5 : X ^ K' * (Q ^ 2 * r ^ (3 / 2 : ℝ)) = Q ^ 2 * r ^ (3 / 2 : ℝ) * X ^ K' := by ring
  linarith

/-- **The second error** of round 657's `prop72`, `|R||μ − μ₀|³`: for `q ≥ 1`, `N > 0`, `0 < δ ≤ 1` and `q ≤ Q`, at most
`(C_δB)³Q^{3δ}Q²|R|^{3/2}`, by round 649's `muP_sub_mu0_le_rpow`. -/
lemma E2_le {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) {N Q δ : ℝ} (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hqQ : (q : ℝ) ≤ Q) :
    (R.card : ℝ) * |muP q N - mu0 q N| ^ 3 ≤
      (LinnikPower.Cdiv δ * Bw) ^ 3 * Q ^ (3 * δ) * (Q ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ1 : 1 ≤ Q := hq1.trans hqQ
  have hCd : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ hδ1
  have hBw : 2 ≤ Bw := two_le_Bw
  have h1 := muP_sub_mu0_le_rpow hδ hδ1 (NeZero.ne q) hN
  have h2 : |muP q N - mu0 q N| ^ 3 ≤ (LinnikPower.Cdiv δ * Bw * (q : ℝ) ^ δ) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 3
  have h3 : (q : ℝ) ^ δ ≤ Q ^ δ := Real.rpow_le_rpow (by positivity) hqQ hδ.le
  have e : (Q ^ δ) ^ 3 = Q ^ (3 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  have h4 : (LinnikPower.Cdiv δ * Bw * (q : ℝ) ^ δ) ^ 3 ≤ (LinnikPower.Cdiv δ * Bw) ^ 3 * Q ^ (3 * δ) := by
    rw [mul_pow, ← e]
    gcongr
  have h5 := natCast_le_rpow R.card
  have h6 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ1
  have h7 : 0 ≤ (LinnikPower.Cdiv δ * Bw) ^ 3 * Q ^ (3 * δ) := by positivity
  have h8 : 0 ≤ (R.card : ℝ) := by positivity
  calc (R.card : ℝ) * |muP q N - mu0 q N| ^ 3 ≤ (R.card : ℝ) * ((LinnikPower.Cdiv δ * Bw) ^ 3 * Q ^ (3 * δ)) :=
        mul_le_mul_of_nonneg_left (h2.trans h4) h8
    _ ≤ (Q ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ)) * ((LinnikPower.Cdiv δ * Bw) ^ 3 * Q ^ (3 * δ)) := by
        refine mul_le_mul_of_nonneg_right ?_ h7
        have : 0 ≤ (R.card : ℝ) ^ (3 / 2 : ℝ) := by positivity
        nlinarith
    _ = _ := by ring

/-- Round 650's tail `τ_M` for `M ≥ XQ/(2N)`, `Q = qT`, `q, T ≥ 1`, `N ≥ 1/2`, `X > 0` and `K_t = k + 2`:
`τ_M ≤ 2C_F(K_t)Z₂(9/(4π²))(3/π)^kQ²/X^k`. -/
lemma tauM_le {q : ℕ} {N T X : ℝ} {M k : ℕ} (hq : 1 ≤ (q : ℝ)) (hT : 1 ≤ T) (hN : 1 / 2 ≤ N) (hX : 0 < X)
    (hM : X * ((q : ℝ) * T) / (2 * N) ≤ M) :
    tauM N q T M (k + 2) ≤ 2 * CF (k + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ k * ((q : ℝ) * T) ^ 2 / X ^ k := by
  unfold tauM
  rw [show k + 2 - 2 = k by omega]
  have hN0 : 0 < N := by linarith
  have hq0 : 0 < (q : ℝ) := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) * T := ⟨_, rfl⟩
  rw [← hQ] at hM ⊢
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_mul_of_one_le_of_one_le hq hT
  have hQ0 : 0 < Q := by linarith
  have hCF := CF_nonneg (k + 2)
  have hZ := Z2_nonneg
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 3 / (2 * π) * (Q / N) := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have ha0 : 0 ≤ (q : ℝ) * (1 + 2 * T) / (2 * π * N) := by positivity
  have h1 : (q : ℝ) * (1 + 2 * T) / (2 * π * N) ≤ b := by
    have h2 : (q : ℝ) * (1 + 2 * T) ≤ 3 * Q := by rw [hQ]; nlinarith
    have e : b = 3 * Q / (2 * π * N) := by rw [hb]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = X * Q / (2 * N) := ⟨_, rfl⟩
  rw [← hy] at hM
  have hy0 : 0 < y := by rw [hy]; positivity
  have hby : b / y = 3 / π / X := by rw [hb, hy]; field_simp
  have h2 : ((q : ℝ) * (1 + 2 * T) / (2 * π * N)) ^ (k + 2) ≤ b ^ (k + 2) := pow_le_pow_left₀ ha0 h1 _
  have h3 : y ^ k ≤ (M : ℝ) ^ k := pow_le_pow_left₀ hy0.le hM _
  have hyk : 0 < y ^ k := by positivity
  have h4 : ((q : ℝ) * (1 + 2 * T) / (2 * π * N)) ^ (k + 2) / (M : ℝ) ^ k ≤ b ^ 2 * (3 / π) ^ k / X ^ k := by
    calc ((q : ℝ) * (1 + 2 * T) / (2 * π * N)) ^ (k + 2) / (M : ℝ) ^ k ≤ b ^ (k + 2) / y ^ k :=
          div_le_div₀ (by positivity) h2 hyk h3
      _ = b ^ 2 * (b / y) ^ k := by rw [div_pow, pow_add]; ring
      _ = b ^ 2 * (3 / π) ^ k / X ^ k := by rw [hby, div_pow]; ring
  have hNb : N * b ^ 2 ≤ 2 * (9 / (4 * π ^ 2)) * Q ^ 2 := by
    rw [hb]
    have e : N * (3 / (2 * π) * (Q / N)) ^ 2 = 9 / (4 * π ^ 2) * Q ^ 2 * (1 / N) := by field_simp; ring
    rw [e]
    have h5 : 1 / N ≤ 2 := by rw [div_le_iff₀ hN0]; linarith
    have h9 : 0 ≤ 9 / (4 * π ^ 2) * Q ^ 2 := by positivity
    nlinarith
  have hXk : 0 < X ^ k := by positivity
  calc N * CF (k + 2) * ((q : ℝ) * (1 + 2 * T) / (2 * π * N)) ^ (k + 2) / (M : ℝ) ^ k * Z2 =
        CF (k + 2) * Z2 * N * (((q : ℝ) * (1 + 2 * T) / (2 * π * N)) ^ (k + 2) / (M : ℝ) ^ k) := by ring
    _ ≤ CF (k + 2) * Z2 * N * (b ^ 2 * (3 / π) ^ k / X ^ k) := by gcongr
    _ = CF (k + 2) * Z2 * (3 / π) ^ k / X ^ k * (N * b ^ 2) := by ring
    _ ≤ CF (k + 2) * Z2 * (3 / π) ^ k / X ^ k * (2 * (9 / (4 * π ^ 2)) * Q ^ 2) := by gcongr
    _ = 2 * CF (k + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ k * Q ^ 2 / X ^ k := by ring

/-- **The third error** of round 657's `prop72`, `3|R|³τ(2N + 1 + τ)²`: for `0 ≤ r ≤ Q`, `τ ≥ 0`, `τQ^{3/2} ≤ c`,
`0 ≤ N ≤ Q` and `Q ≥ 1`, at most `3c(3 + c)²Q²r^{3/2}`. -/
lemma E3_le {r τ c N Q : ℝ} (hr : 0 ≤ r) (hrQ : r ≤ Q) (hτ : 0 ≤ τ) (hτc : τ * Q ^ (3 / 2 : ℝ) ≤ c) (hN : 0 ≤ N)
    (hNQ : N ≤ Q) (hQ : 1 ≤ Q) :
    3 * r ^ 3 * τ * (2 * N + 1 + τ) ^ 2 ≤ 3 * c * (3 + c) ^ 2 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by
  have hQ32 : 1 ≤ Q ^ (3 / 2 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hc0 : 0 ≤ c := le_trans (by positivity) hτc
  have hτ1 : τ ≤ c := by nlinarith
  have hs : 2 * N + 1 + τ ≤ (3 + c) * Q := by nlinarith
  have hs2 : (2 * N + 1 + τ) ^ 2 ≤ ((3 + c) * Q) ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  have h3 := cube_le hr hrQ
  calc 3 * r ^ 3 * τ * (2 * N + 1 + τ) ^ 2 ≤
        3 * (Q ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) * τ * ((3 + c) * Q) ^ 2 := by gcongr
    _ = 3 * (3 + c) ^ 2 * (τ * Q ^ (3 / 2 : ℝ)) * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by ring
    _ ≤ 3 * (3 + c) ^ 2 * c * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by gcongr
    _ = 3 * c * (3 + c) ^ 2 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) := by ring

/-! ### The main term of their (11.2) -/

/-- `√(12CQ^{ε₁}X³r) ≤ √(12C)Q^{ε₁/2}X²√r` for `C ≥ 0`, `Q > 0` and `X ≥ 1`. -/
lemma sqrt_main_le {C Q ε₁ X r : ℝ} (hC : 0 ≤ C) (hQ : 0 < Q) (hX : 1 ≤ X) :
    √(12 * C * Q ^ ε₁ * X ^ 3 * r) ≤ √(12 * C) * Q ^ (ε₁ / 2) * X ^ 2 * √r := by
  have hQe : 0 ≤ Q ^ ε₁ := by positivity
  rw [Real.sqrt_mul (by positivity) r, Real.sqrt_mul (by positivity) (X ^ 3), Real.sqrt_mul (by positivity) (Q ^ ε₁),
    Real.sqrt_eq_rpow (Q ^ ε₁), ← Real.rpow_mul hQ.le, show ε₁ * (1 / 2) = ε₁ / 2 by ring]
  have h1 : √(X ^ 3) ≤ X ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
    linarith [show (X ^ 2) ^ 2 = X ^ 4 by ring]
  gcongr

/-- `√(IE + r⁴D/X^{2k}) ≤ √I√E + r²√D/X^k` for `I, E, D ≥ 0` and `X > 0`. -/
lemma sqrt_Gq_le {I E r D X : ℝ} (k : ℕ) (hI : 0 ≤ I) (hE : 0 ≤ E) (hD : 0 ≤ D) (hX : 0 < X) :
    √(I * E + r ^ 4 * D / X ^ (2 * k)) ≤ √I * √E + r ^ 2 * √D / X ^ k := by
  refine (sqrt_add_le (by positivity) (by positivity)).trans (le_of_eq ?_)
  rw [Real.sqrt_mul hI E, show r ^ 4 * D / X ^ (2 * k) = (r ^ 2 / X ^ k) ^ 2 * D by rw [pow_mul]; field_simp; ring,
    Real.sqrt_mul (by positivity) D, Real.sqrt_sq (by positivity)]
  ring

/-- `X³QNr²√r/X^k ≤ Q²r^{3/2}` for `X > 0`, `0 ≤ r ≤ Q`, `N ≤ Q` and `X³Q ≤ X^k`. -/
lemma term3_le {X Q N r : ℝ} {k : ℕ} (hX : 0 < X) (hr : 0 ≤ r) (hrQ : r ≤ Q) (hNQ : N ≤ Q)
    (hXk : X ^ 3 * Q ≤ X ^ k) : X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k ≤ Q ^ 2 * r ^ (3 / 2 : ℝ) := by
  have hQ : 0 ≤ Q := hr.trans hrQ
  have hr32 : √r * r = r ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one' hr (by norm_num)]; norm_num
  have hXk0 : 0 < X ^ k := by positivity
  rw [div_le_iff₀ hXk0]
  have h4 : N * r ≤ Q * Q := mul_le_mul hNQ hrQ hr hQ
  have e1 : X ^ 3 * (Q * N * (r ^ 2 * √r)) = (X ^ 3 * Q) * ((N * r) * (√r * r)) := by ring
  rw [e1, hr32]
  have h5 : 0 ≤ r ^ (3 / 2 : ℝ) := by positivity
  have h6 : (N * r) * r ^ (3 / 2 : ℝ) ≤ (Q * Q) * r ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_right h4 h5
  have h7 : (X ^ 3 * Q) * ((N * r) * r ^ (3 / 2 : ℝ)) ≤ (X ^ 3 * Q) * ((Q * Q) * r ^ (3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  have h8 : (X ^ 3 * Q) * ((Q * Q) * r ^ (3 / 2 : ℝ)) ≤ X ^ k * ((Q * Q) * r ^ (3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hXk (by positivity)
  have e2 : X ^ k * ((Q * Q) * r ^ (3 / 2 : ℝ)) = Q ^ 2 * r ^ (3 / 2 : ℝ) * X ^ k := by ring
  linarith

/-- **The main term of their (11.2)**: for `a, D, I, C, E, D_K ≥ 0`, `Q, X ≥ 1`, `0 ≤ r ≤ Q`, `0 ≤ N ≤ Q`,
`c₂Λ ≥ 0`, `X³Q ≤ X^k`, the energy term `QN√r√E ≤ c₂ΛW` (`energy_term`) and `Q²r^{3/2} ≤ W`, round 667's main term
is at most `6aDIL²√(12C)Q^{ε₁/2}X⁴((24 + 12√D_K)W + 12√I·c₂ΛW)`. -/
lemma main_le {a D I L C Q ε₁ X r N E DK c₂ Λ W : ℝ} (k : ℕ) (ha : 0 ≤ a) (hD : 0 ≤ D) (hI : 0 ≤ I) (hC : 0 ≤ C)
    (hQ : 1 ≤ Q) (hX : 1 ≤ X) (hr : 0 ≤ r) (hrQ : r ≤ Q) (hN : 0 ≤ N) (hNQ : N ≤ Q) (hE : 0 ≤ E) (hDK : 0 ≤ DK)
    (hc₂Λ : 0 ≤ c₂ * Λ) (hXk : X ^ 3 * Q ≤ X ^ k) (hen : Q * N * √r * √E ≤ c₂ * Λ * W)
    (hW : Q ^ 2 * r ^ (3 / 2 : ℝ) ≤ W) :
    6 * a * D * I * L ^ 2 * √(12 * C * Q ^ ε₁ * X ^ 3 * r) *
        (24 * (X * Q) ^ 2 * r + 12 * (X * Q) * N * √(I * E + r ^ 4 * DK / X ^ (2 * k))) ≤
      6 * a * D * I * L ^ 2 * √(12 * C) * Q ^ (ε₁ / 2) * X ^ 4 * ((24 + 12 * √DK) * W + 12 * √I * (c₂ * Λ * W)) := by
  have hQ0 : 0 < Q := by linarith
  have hX0 : 0 < X := by linarith
  have hW0 : 0 ≤ W := le_trans (by positivity) hW
  have hpre : 0 ≤ 6 * a * D * I * L ^ 2 := by positivity
  have hP := sqrt_main_le (ε₁ := ε₁) (r := r) hC hQ0 hX
  have hG := sqrt_Gq_le k hI hE hDK hX0 (r := r)
  have hr32 : √r * r = r ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one' hr (by norm_num)]; norm_num
  have h3 := term3_le hX0 hr hrQ hNQ hXk
  have hB : 24 * (X * Q) ^ 2 * r + 12 * (X * Q) * N * √(I * E + r ^ 4 * DK / X ^ (2 * k)) ≤
      24 * (X * Q) ^ 2 * r + 12 * (X * Q) * N * (√I * √E + r ^ 2 * √DK / X ^ k) := by
    gcongr
  have hB0 : 0 ≤ 24 * (X * Q) ^ 2 * r + 12 * (X * Q) * N * √(I * E + r ^ 4 * DK / X ^ (2 * k)) := by positivity
  have hPB := mul_le_mul hP hB hB0 (by positivity)
  have e : √(12 * C) * Q ^ (ε₁ / 2) * X ^ 2 * √r *
      (24 * (X * Q) ^ 2 * r + 12 * (X * Q) * N * (√I * √E + r ^ 2 * √DK / X ^ k)) =
      √(12 * C) * Q ^ (ε₁ / 2) * (24 * X ^ 4 * (Q ^ 2 * (√r * r)) + 12 * √I * X ^ 3 * (Q * N * √r * √E) +
        12 * √DK * (X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k)) := by
    ring
  rw [e, hr32] at hPB
  have hX34 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX
  have t1 : 24 * X ^ 4 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) ≤ 24 * X ^ 4 * W := by gcongr
  have t2 : 12 * √I * X ^ 3 * (Q * N * √r * √E) ≤ 12 * √I * X ^ 4 * (c₂ * Λ * W) := by
    have h0 : 0 ≤ c₂ * Λ * W := mul_nonneg hc₂Λ hW0
    gcongr
  have t3 : 12 * √DK * (X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k) ≤ 12 * √DK * X ^ 4 * W := by
    have h4 : X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k ≤ X ^ 4 * W := by
      have : W ≤ X ^ 4 * W := le_mul_of_one_le_left hW0 hX4
      linarith
    have h5 : 0 ≤ 12 * √DK := by positivity
    calc 12 * √DK * (X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k) ≤ 12 * √DK * (X ^ 4 * W) :=
          mul_le_mul_of_nonneg_left h4 h5
      _ = 12 * √DK * X ^ 4 * W := by ring
  have hsum : 24 * X ^ 4 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) + 12 * √I * X ^ 3 * (Q * N * √r * √E) +
      12 * √DK * (X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k) ≤
      X ^ 4 * ((24 + 12 * √DK) * W + 12 * √I * (c₂ * Λ * W)) := by
    have e2 : X ^ 4 * ((24 + 12 * √DK) * W + 12 * √I * (c₂ * Λ * W)) =
        24 * X ^ 4 * W + 12 * √I * X ^ 4 * (c₂ * Λ * W) + 12 * √DK * X ^ 4 * W := by ring
    linarith
  have hc : 0 ≤ √(12 * C) * Q ^ (ε₁ / 2) := by positivity
  calc 6 * a * D * I * L ^ 2 * √(12 * C * Q ^ ε₁ * X ^ 3 * r) *
        (24 * (X * Q) ^ 2 * r + 12 * (X * Q) * N * √(I * E + r ^ 4 * DK / X ^ (2 * k)))
      = 6 * a * D * I * L ^ 2 * (√(12 * C * Q ^ ε₁ * X ^ 3 * r) *
        (24 * (X * Q) ^ 2 * r + 12 * (X * Q) * N * √(I * E + r ^ 4 * DK / X ^ (2 * k)))) := by ring
    _ ≤ 6 * a * D * I * L ^ 2 * (√(12 * C) * Q ^ (ε₁ / 2) * (24 * X ^ 4 * (Q ^ 2 * r ^ (3 / 2 : ℝ)) +
        12 * √I * X ^ 3 * (Q * N * √r * √E) + 12 * √DK * (X ^ 3 * (Q * N * (r ^ 2 * √r)) / X ^ k))) :=
        mul_le_mul_of_nonneg_left hPB hpre
    _ ≤ 6 * a * D * I * L ^ 2 * (√(12 * C) * Q ^ (ε₁ / 2) *
        (X ^ 4 * ((24 + 12 * √DK) * W + 12 * √I * (c₂ * Λ * W)))) := by
        gcongr
    _ = _ := by ring

/-! ### Their Proposition 11.1 -/

/-- **The small range**, by `S3_le_crude`: for `q ≥ 1`, `χ` injective on `R`, `T ≥ 1`, `ε > 0` and
`(qT)^{2/3}/2 ≤ N ≤ qT < Q₁`, `S₃ ≤ 2^εQ₁^{3/2}(Q₁ + 1)³(qTN)^ε(qT)²|R|^{3/2}`. -/
lemma small_case {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {T N Q₁ ε : ℝ} (hinj : Set.InjOn χ R) (hT : 1 ≤ T) (hε : 0 < ε)
    (hN : ((q : ℝ) * T) ^ (2 / 3 : ℝ) / 2 ≤ N) (hNQ : N ≤ (q : ℝ) * T) (hsmall : (q : ℝ) * T < Q₁) :
    S3 q N R χ t ≤ 2 ^ ε * Q₁ ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * ((q : ℝ) * T * N) ^ ε *
      (((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hN2 : 1 / 2 ≤ N := by
    have : 1 ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have hQ₁0 : 0 < Q₁ := by linarith
  have h1 := S3_le_crude hN0 R χ t
  have hrq : (R.card : ℝ) ≤ (q : ℝ) * T := by
    have h : R.card ≤ q := (card_le_totient R hinj).trans (Nat.totient_le q)
    have h' : (R.card : ℝ) ≤ q := by exact_mod_cast h
    nlinarith
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have h2 := cube_le hr0 (hrq.trans hsmall.le)
  have h3 : (N + 1) ^ 3 ≤ (Q₁ + 1) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h4 : 1 ≤ 2 ^ ε * ((q : ℝ) * T * N) ^ ε := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.one_le_rpow (by nlinarith) hε.le
  have h5 : 1 ≤ ((q : ℝ) * T) ^ 2 := one_le_pow₀ hQ1
  have h6 : 1 ≤ (2 ^ ε * ((q : ℝ) * T * N) ^ ε) * ((q : ℝ) * T) ^ 2 := one_le_mul_of_one_le_of_one_le h4 h5
  have h0 : 0 ≤ Q₁ ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * (R.card : ℝ) ^ (3 / 2 : ℝ) := by positivity
  calc S3 q N R χ t ≤ (R.card : ℝ) ^ 3 * (N + 1) ^ 3 := h1
    _ ≤ (Q₁ ^ (3 / 2 : ℝ) * (R.card : ℝ) ^ (3 / 2 : ℝ)) * (Q₁ + 1) ^ 3 :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = Q₁ ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * (R.card : ℝ) ^ (3 / 2 : ℝ) := by ring
    _ ≤ Q₁ ^ (3 / 2 : ℝ) * (Q₁ + 1) ^ 3 * (R.card : ℝ) ^ (3 / 2 : ℝ) *
        ((2 ^ ε * ((q : ℝ) * T * N) ^ ε) * ((q : ℝ) * T) ^ 2) := le_mul_of_one_le_right h0 h6
    _ = _ := by ring

/-- `D·L²·Q_e·X₄·Λ ≤ c_Dc_L²Φ^ε` from `D ≤ c_DΦ^δ`, `L ≤ c_LΦ^δ`, `Q_e ≤ Φ^{e₁}`, `X₄ ≤ Φ^{e′}`, `Λ ≤ Φ^{e₂}` and
`3δ + e₁ + e′ + e₂ ≤ ε`, for `Φ ≥ 1`, `c_D ≥ 0` and `L, Q_e, X₄, Λ ≥ 0`. -/
lemma factors_le {D L Qe X4 Λ cD cL Φ δ e₁ e' e₂ ε : ℝ} (hΦ : 1 ≤ Φ) (hcD : 0 ≤ cD)
    (hD : D ≤ cD * Φ ^ δ) (hL0 : 0 ≤ L) (hL : L ≤ cL * Φ ^ δ) (hQe0 : 0 ≤ Qe) (hQe : Qe ≤ Φ ^ e₁)
    (hX0 : 0 ≤ X4) (hX : X4 ≤ Φ ^ e') (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ Φ ^ e₂) (hsum : 3 * δ + e₁ + e' + e₂ ≤ ε) :
    D * L ^ 2 * Qe * X4 * Λ ≤ cD * cL ^ 2 * Φ ^ ε := by
  have hΦ0 : 0 < Φ := by linarith
  have h1 : D * L ^ 2 * Qe * X4 * Λ ≤ (cD * Φ ^ δ) * (cL * Φ ^ δ) ^ 2 * Φ ^ e₁ * Φ ^ e' * Φ ^ e₂ := by
    gcongr
  have e : (cD * Φ ^ δ) * (cL * Φ ^ δ) ^ 2 * Φ ^ e₁ * Φ ^ e' * Φ ^ e₂ =
      cD * cL ^ 2 * Φ ^ (3 * δ + e₁ + e' + e₂) := by
    rw [Real.rpow_add hΦ0, Real.rpow_add hΦ0, Real.rpow_add hΦ0, show 3 * δ = δ + δ + δ by ring,
      Real.rpow_add hΦ0, Real.rpow_add hΦ0]
    ring
  rw [e] at h1
  have h2 : Φ ^ (3 * δ + e₁ + e' + e₂) ≤ Φ ^ ε := Real.rpow_le_rpow_of_exponent_le hΦ hsum
  have h3 : 0 ≤ cD * cL ^ 2 := by positivity
  calc D * L ^ 2 * Qe * X4 * Λ ≤ cD * cL ^ 2 * Φ ^ (3 * δ + e₁ + e' + e₂) := h1
    _ ≤ cD * cL ^ 2 * Φ ^ ε := mul_le_mul_of_nonneg_left h2 h3

/-- The bound of `main_le` with `Λ ≥ 1` pulled out: at most `6aI√(12C)(24 + 12√D_K + 12√Ic₂)BW` for
`a, I, c₂, W, D, Q_e, X₄ ≥ 0`, `Λ ≥ 1` and `D·L²·Q_e·X₄·Λ ≤ B`. -/
lemma main_final {a D I L C Qe X4 DK c₂ Λ W B : ℝ} (ha : 0 ≤ a) (hI : 0 ≤ I) (hc₂ : 0 ≤ c₂)
    (hΛ : 1 ≤ Λ) (hW : 0 ≤ W) (hD : 0 ≤ D) (hQe : 0 ≤ Qe) (hX4 : 0 ≤ X4) (hB : D * L ^ 2 * Qe * X4 * Λ ≤ B) :
    6 * a * D * I * L ^ 2 * √(12 * C) * Qe * X4 * ((24 + 12 * √DK) * W + 12 * √I * (c₂ * Λ * W)) ≤
      6 * a * I * √(12 * C) * (24 + 12 * √DK + 12 * √I * c₂) * B * W := by
  have hk : 0 ≤ 6 * a * I * √(12 * C) * (24 + 12 * √DK + 12 * √I * c₂) := by positivity
  have h1 : (24 + 12 * √DK) * W ≤ (24 + 12 * √DK) * (Λ * W) := by
    have : W ≤ Λ * W := le_mul_of_one_le_left hW hΛ
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : 0 ≤ D * L ^ 2 * Qe * X4 := by positivity
  calc 6 * a * D * I * L ^ 2 * √(12 * C) * Qe * X4 * ((24 + 12 * √DK) * W + 12 * √I * (c₂ * Λ * W)) =
        6 * a * I * √(12 * C) * (D * L ^ 2 * Qe * X4) * ((24 + 12 * √DK) * W + 12 * √I * (c₂ * Λ * W)) := by
        ring
    _ ≤ 6 * a * I * √(12 * C) * (D * L ^ 2 * Qe * X4) * ((24 + 12 * √DK) * (Λ * W) + 12 * √I * (c₂ * Λ * W)) := by
        gcongr
    _ = 6 * a * I * √(12 * C) * (24 + 12 * √DK + 12 * √I * c₂) * (D * L ^ 2 * Qe * X4 * Λ) * W := by ring
    _ ≤ 6 * a * I * √(12 * C) * (24 + 12 * √DK + 12 * √I * c₂) * B * W := by gcongr

/-- `S ≤ A + B` from `S ≤ m + e₁ + e₂ + e₃`, `m ≤ A` and `e₁ + e₂ + e₃ ≤ B`. -/
lemma combine3 {S m e1 e2 e3 A B : ℝ} (hS : S ≤ m + e1 + e2 + e3) (hm : m ≤ A) (he : e1 + e2 + e3 ≤ B) :
    S ≤ A + B := by
  linarith

/-- The errors against `Φ^εW`: from `e₁ ≤ K₁P`, `e₂ ≤ K₂tP` and `e₃ ≤ K₃P` with `0 ≤ P ≤ W`, `0 ≤ t ≤ Φ^ε`,
`Φ^ε ≥ 1` and `K_i ≥ 0`, `e₁ + e₂ + e₃ ≤ (K₁ + K₂ + K₃)Φ^εW`. -/
lemma errors_combine {e1 e2 e3 K1 K2 K3 P Φε W t : ℝ} (he1 : e1 ≤ K1 * P) (he2 : e2 ≤ K2 * t * P)
    (he3 : e3 ≤ K3 * P) (hP : P ≤ W) (hP0 : 0 ≤ P) (ht : t ≤ Φε) (ht0 : 0 ≤ t) (hΦ : 1 ≤ Φε) (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) : e1 + e2 + e3 ≤ (K1 + K2 + K3) * Φε * W := by
  have hW : 0 ≤ W := hP0.trans hP
  have h1 : K1 * P ≤ K1 * W := mul_le_mul_of_nonneg_left hP hK1
  have h1' : K1 * W * 1 ≤ K1 * W * Φε := mul_le_mul_of_nonneg_left hΦ (mul_nonneg hK1 hW)
  have h2 : K2 * t * P ≤ K2 * Φε * W :=
    mul_le_mul (mul_le_mul_of_nonneg_left ht hK2) hP hP0 (mul_nonneg hK2 (ht0.trans ht))
  have h3 : K3 * P ≤ K3 * W := mul_le_mul_of_nonneg_left hP hK3
  have h3' : K3 * W * 1 ≤ K3 * W * Φε := mul_le_mul_of_nonneg_left hΦ (mul_nonneg hK3 hW)
  have e : (K1 + K2 + K3) * Φε * W = K1 * W * Φε + K2 * Φε * W + K3 * W * Φε := by ring
  rw [e]
  linarith

/-- The constants' last step: `S ≤ (a + b + c)Φ^εW` from `S ≤ aΦ^εW + bΦ^εW` and `c, Φ^ε, W ≥ 0`. -/
lemma final_large {S a b c Φε W : ℝ} (hS : S ≤ a * Φε * W + b * Φε * W) (hc : 0 ≤ c) (hΦ : 0 ≤ Φε)
    (hW : 0 ≤ W) : S ≤ (a + b + c) * Φε * W := by
  have : 0 ≤ c * Φε * W := mul_nonneg (mul_nonneg hc hΦ) hW
  have e : (a + b + c) * Φε * W = a * Φε * W + b * Φε * W + c * Φε * W := by ring
  rw [e]
  linarith

/-- The small range's last step: `S ≤ (a + b + c)Φ^εW` from `S ≤ cΦ^εP`, `0 ≤ P ≤ W` and `a, b, c, Φ^ε ≥ 0`. -/
lemma final_small {S a b c Φε P W : ℝ} (hS : S ≤ c * Φε * P) (hP : P ≤ W) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hΦ : 0 ≤ Φε) (hP0 : 0 ≤ P) : S ≤ (a + b + c) * Φε * W := by
  have hW : 0 ≤ W := hP0.trans hP
  have h1 : c * Φε * P ≤ c * Φε * W := mul_le_mul_of_nonneg_left hP (mul_nonneg hc hΦ)
  have h2 : 0 ≤ (a + b) * Φε * W := mul_nonneg (mul_nonneg (add_nonneg ha hb) hΦ) hW
  have e : (a + b + c) * Φε * W = (a + b) * Φε * W + c * Φε * W := by ring
  rw [e]
  linarith

/-- The orders against `X = Q^{ε′}`, for `Q ≥ 1`: `X³Q ≤ X^{k₀+3}` if `ε′k₀ ≥ 1`, `X³Q^{5/2} ≤ X^{K₀+3}` if
`ε′K₀ ≥ 5/2`, and `Q^{7/2} ≤ X^{k_t}` if `ε′k_t ≥ 4`. -/
lemma orders {Q ε' : ℝ} {k₀ K₀ kt : ℕ} (hQ : 1 ≤ Q) (hk₀ : 1 ≤ ε' * k₀) (hK₀ : 5 / 2 ≤ ε' * K₀)
    (hkt : 4 ≤ ε' * kt) :
    (Q ^ ε') ^ 3 * Q ≤ (Q ^ ε') ^ (k₀ + 3) ∧ (Q ^ ε') ^ 3 * Q ^ (5 / 2 : ℝ) ≤ (Q ^ ε') ^ (K₀ + 3) ∧
      Q ^ (7 / 2 : ℝ) ≤ (Q ^ ε') ^ kt := by
  have hQ0 : 0 < Q := by linarith
  have hX0 : 0 < Q ^ ε' := by positivity
  have hX3 : 0 ≤ (Q ^ ε') ^ 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h := rpow_le_pow_X (n := k₀) hQ hk₀
    rw [Real.rpow_one] at h
    rw [pow_add, mul_comm ((Q ^ ε') ^ k₀)]
    exact mul_le_mul_of_nonneg_left h hX3
  · have h := rpow_le_pow_X (n := K₀) hQ hK₀
    rw [pow_add, mul_comm ((Q ^ ε') ^ K₀)]
    exact mul_le_mul_of_nonneg_left h hX3
  · exact (Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)).trans (rpow_le_pow_X hQ hkt)

/-- **The main term** of round 667's (11.2), at the order `2(k₀ + 3)` and the exponent `ε/2`: at most `K_mΦ^εW`, with
`Φ = qTN` and `K_m = 6C_J(0)I√(12C₁)(24 + 12√D + 12√Ic₂)C_δ(1/(δ log 2) + 1)²`, for `q, T, N ≥ 1`, `N, |R| ≤ qT`,
`E ≥ 0`, `0 < δ ≤ min(1, ε/12)`, `0 < ε′ ≤ ε/16`, `X = (qT)^{ε′}` with `X³qT ≤ X^{k₀+3}`, `1 ≤ M ≤ Φ`, `C₁, c₂ ≥ 0`,
`Λ = Φ^{ε/4}`, the energy term `qTN√|R|√E ≤ c₂ΛW` and `(qT)²|R|^{3/2} ≤ W`. -/
lemma main_part {ι : Type*} {q : ℕ} (R : Finset ι) {T N X E ε δ ε' C₁ c₂ Λ W : ℝ} {M k₀ : ℕ}
    (hq1 : 1 ≤ (q : ℝ)) (hT : 1 ≤ T) (hN1 : 1 ≤ N) (hNQ : N ≤ (q : ℝ) * T) (hrq : (R.card : ℝ) ≤ (q : ℝ) * T)
    (hE : 0 ≤ E) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδε : δ ≤ ε / 12) (hε'0 : 0 < ε')
    (hε'ε : ε' ≤ ε / 16) (hX : X = ((q : ℝ) * T) ^ ε') (hXk : X ^ 3 * ((q : ℝ) * T) ≤ X ^ (k₀ + 3))
    (hM1 : 1 ≤ M) (hMΦ : (M : ℝ) ≤ (q : ℝ) * T * N) (hC₁ : 0 ≤ C₁) (hc₂ : 0 ≤ c₂)
    (hΛ : Λ = ((q : ℝ) * T * N) ^ (ε / 4)) (hen : (q : ℝ) * T * N * √(R.card : ℝ) * √E ≤ c₂ * Λ * W)
    (hW : ((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) ≤ W) :
    6 * CJ 0 * q.divisors.card * (∫ x, psi0 x) * ((Nat.log 2 M : ℝ) + 1) ^ 2 *
        √(12 * C₁ * ((q : ℝ) * T) ^ (ε / 2) * X ^ 3 * R.card) *
        (24 * (X * ((q : ℝ) * T)) ^ 2 * R.card + 12 * (X * ((q : ℝ) * T)) * N *
          √((∫ x, psi0 x) * E + (R.card : ℝ) ^ 4 * Dpsi (2 * (k₀ + 3)) / X ^ (2 * (k₀ + 3)))) ≤
      6 * CJ 0 * (∫ x, psi0 x) * √(12 * C₁) * (24 + 12 * √(Dpsi (2 * (k₀ + 3))) + 12 * √(∫ x, psi0 x) * c₂) *
        (LinnikPower.Cdiv δ * (1 / (δ * Real.log 2) + 1) ^ 2) * ((q : ℝ) * T * N) ^ ε * W := by
  have hQ1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hQ0 : 0 < (q : ℝ) * T := by linarith
  have hN0 : 0 < N := by linarith
  have hΦQ : (q : ℝ) * T ≤ (q : ℝ) * T * N := le_mul_of_one_le_right hQ0.le hN1
  have hΦ1 : 1 ≤ (q : ℝ) * T * N := hQ1.trans hΦQ
  have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_rpow hQ1 hε'0.le
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact Real.one_le_rpow hΦ1 (by positivity)
  have hW0 : 0 ≤ W := le_trans (by positivity) hW
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have hCJ := CJ_nonneg 0
  have hcD : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ0 hδ1
  have hmain := main_le (k₀ + 3) hCJ (by positivity : (0 : ℝ) ≤ q.divisors.card) hI0 hC₁ hQ1 hX1 hr0 hrq
    hN0.le hNQ hE (Dpsi_nonneg (2 * (k₀ + 3))) (mul_nonneg hc₂ (by linarith)) hXk hen hW
    (L := (Nat.log 2 M : ℝ) + 1) (ε₁ := ε / 2)
  have hD : (q.divisors.card : ℝ) ≤ LinnikPower.Cdiv δ * ((q : ℝ) * T * N) ^ δ := by
    have h := LinnikPower.card_divisors_le hδ0 hδ1 q
    have hqΦ : (q : ℝ) ≤ (q : ℝ) * T * N := by nlinarith
    have h' : (q : ℝ) ^ δ ≤ ((q : ℝ) * T * N) ^ δ := Real.rpow_le_rpow (by linarith) hqΦ hδ0.le
    calc (q.divisors.card : ℝ) ≤ LinnikPower.Cdiv δ * (q : ℝ) ^ δ := h
      _ ≤ LinnikPower.Cdiv δ * ((q : ℝ) * T * N) ^ δ := by gcongr
  have hL := natlog_le_rpow hM1 hMΦ hδ0
  have hQe : ((q : ℝ) * T) ^ (ε / 2 / 2) ≤ ((q : ℝ) * T * N) ^ (ε / 4) := by
    rw [show ε / 2 / 2 = ε / 4 by ring]
    exact Real.rpow_le_rpow hQ0.le hΦQ (by positivity)
  have hX4 : X ^ 4 ≤ ((q : ℝ) * T * N) ^ (4 * ε') := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    push_cast
    rw [mul_comm ε' 4]
    exact Real.rpow_le_rpow hQ0.le hΦQ (by positivity)
  have hfac := factors_le hΦ1 (by linarith) hD (by positivity) hL (by positivity) hQe (by positivity) hX4
    (by linarith) (le_of_eq hΛ) (ε := ε) (by linarith)
  have hfin := main_final hCJ hI0 hc₂ hΛ1 hW0 (by positivity) (by positivity) (by positivity) hfac (C := C₁)
    (DK := Dpsi (2 * (k₀ + 3)))
  calc _ ≤ _ := hmain
    _ ≤ _ := hfin
    _ = _ := by ring

/-- **The errors** of round 667's (11.2): at most `(K₁ + K₂ + K₃)Φ^εW`, with `Φ = qTN`, for `q, T, N ≥ 1`,
`N, |R| ≤ qT`, `ε > 0`, `0 < δ ≤ min(1, ε/12)`, `X > 0`, `NM ≤ XqT`, `M ≥ XqT/(2N)`, `X³(qT)^{5/2} ≤ X^{K₀+3}`,
`(qT)^{7/2} ≤ X^{k_t}` and `(qT)²|R|^{3/2} ≤ W`; by `E1_le`, `E2_le` and `E3_le` with `tauM_le`. -/
lemma errors_part {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) {T N X ε δ W : ℝ} {M K₀ kt : ℕ}
    (hq1 : 1 ≤ (q : ℝ)) (hT : 1 ≤ T) (hN1 : 1 ≤ N) (hNQ : N ≤ (q : ℝ) * T) (hrq : (R.card : ℝ) ≤ (q : ℝ) * T)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδε : δ ≤ ε / 12) (hX0 : 0 < X)
    (hNM : N * M ≤ X * ((q : ℝ) * T)) (hMlow : X * ((q : ℝ) * T) / (2 * N) ≤ M)
    (hXK : X ^ 3 * ((q : ℝ) * T) ^ (5 / 2 : ℝ) ≤ X ^ (K₀ + 3)) (hXkt : ((q : ℝ) * T) ^ (7 / 2 : ℝ) ≤ X ^ kt)
    (hW : ((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) ≤ W) :
    3 * (2 * (M : ℝ)) ^ 3 * E71 q N R X (K₀ + 3) + R.card * |muP q N - mu0 q N| ^ 3 +
        3 * (R.card : ℝ) ^ 3 * tauM N q T M (kt + 2) * (2 * N + 1 + tauM N q T M (kt + 2)) ^ 2 ≤
      (54 * (CJ (K₀ + 3) / (2 * π) ^ (K₀ + 3)) + (LinnikPower.Cdiv δ * Bw) ^ 3 +
        3 * (2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) *
          (3 + 2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) ^ 2) * ((q : ℝ) * T * N) ^ ε * W := by
  have hQ1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hQ0 : 0 < (q : ℝ) * T := by linarith
  have hN0 : 0 < N := by linarith
  have hN2 : 1 / 2 ≤ N := by linarith
  have hΦQ : (q : ℝ) * T ≤ (q : ℝ) * T * N := le_mul_of_one_le_right hQ0.le hN1
  have hΦ1 : 1 ≤ (q : ℝ) * T * N := hQ1.trans hΦQ
  have hΦε : 1 ≤ ((q : ℝ) * T * N) ^ ε := Real.one_le_rpow hΦ1 hε.le
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have hcD : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ0 hδ1
  have hBw : 2 ≤ Bw := two_le_Bw
  have hCF := CF_nonneg (kt + 2)
  have hZ2 := Z2_nonneg
  have he1 := E1_le R hq1 hT hN0 hX0 hNM hrq hXK
  have he2 := E2_le R hN0 hδ0 hδ1 (show (q : ℝ) ≤ (q : ℝ) * T by nlinarith) (Q := (q : ℝ) * T)
  have hτ := tauM_le (k := kt) hq1 hT hN2 hX0 hMlow
  obtain ⟨cτ, hcτ⟩ : ∃ cτ : ℝ, cτ = 2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt := ⟨_, rfl⟩
  rw [← hcτ] at hτ ⊢
  have hτ0 : 0 ≤ tauM N q T M (kt + 2) := by
    unfold tauM
    have : (0 : ℝ) ≤ M := by positivity
    positivity
  have hτc : tauM N q T M (kt + 2) * ((q : ℝ) * T) ^ (3 / 2 : ℝ) ≤ cτ := by
    have hXkt0 : 0 < X ^ kt := by positivity
    have hcτ0 : 0 ≤ cτ := by rw [hcτ]; positivity
    have e : ((q : ℝ) * T) ^ 2 * ((q : ℝ) * T) ^ (3 / 2 : ℝ) = ((q : ℝ) * T) ^ (7 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hQ0]; norm_num
    calc tauM N q T M (kt + 2) * ((q : ℝ) * T) ^ (3 / 2 : ℝ) ≤
          cτ * ((q : ℝ) * T) ^ 2 / X ^ kt * ((q : ℝ) * T) ^ (3 / 2 : ℝ) := by gcongr
      _ = cτ * (((q : ℝ) * T) ^ 2 * ((q : ℝ) * T) ^ (3 / 2 : ℝ)) / X ^ kt := by ring
      _ = cτ * ((q : ℝ) * T) ^ (7 / 2 : ℝ) / X ^ kt := by rw [e]
      _ ≤ cτ * X ^ kt / X ^ kt := by gcongr
      _ = cτ := by field_simp
  have hcτ0 : 0 ≤ cτ := le_trans (by positivity) hτc
  have he3 := E3_le hr0 hrq hτ0 hτc hN0.le hNQ hQ1
  have ht : ((q : ℝ) * T) ^ (3 * δ) ≤ ((q : ℝ) * T * N) ^ ε :=
    (Real.rpow_le_rpow hQ0.le hΦQ (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hΦ1 (by linarith))
  exact errors_combine he1 he2 he3 hW (by positivity) ht (by positivity) hΦε (by have := CJ_nonneg (K₀ + 3); positivity)
    (by positivity) (by positivity)

/-- **Their Proposition 11.1 at one point per character**: `CGLS3` from `CGLP81` (their Proposition 8.1) and
`CGLT101` (Heath-Brown's Theorem 10.1). For `qT ≥ Q₁ = max(Q₀, 64)`: round 667's `S3_le_112` at `ϖ = 3/4`, `ε/2`,
`X = (qT)^{ε′}` with `ε′ = min(1/12, ε/16)`, `M = ⌊XqT/N⌋` and the orders `2(k₀ + 3)`, `K₀ + 3` and `k_t + 2`; the
energy term by round 677's `prop102` at `ε/2` or round 676's `remark103` (`energy_term`); then `main_part` and
`errors_part`. For `qT < Q₁`, `small_case`. -/
theorem cgls3 (hP : CGLP81) (hT : CGLT101) : CGLS3 := by
  intro ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 12) 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_right _ _
  have hδε : δ ≤ ε / 12 := hδ ▸ min_le_left _ _
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min (1 / 12) (ε / 16) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min (by norm_num) (by positivity)
  have hε'1 : ε' ≤ 1 / 12 := hε' ▸ min_le_left _ _
  have hε'ε : ε' ≤ ε / 16 := hε' ▸ min_le_right _ _
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = ⌈1 / ε'⌉₊ := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, K₀ = ⌈5 / (2 * ε')⌉₊ := ⟨_, rfl⟩
  obtain ⟨kt, hkt⟩ : ∃ kt : ℕ, kt = ⌈4 / ε'⌉₊ := ⟨_, rfl⟩
  have hk₀ε : (1 : ℝ) ≤ ε' * k₀ := by
    have := Nat.le_ceil (1 / ε')
    rw [← hk₀, div_le_iff₀ hε'0] at this
    linarith
  have hK₀ε : (5 / 2 : ℝ) ≤ ε' * K₀ := by
    have := Nat.le_ceil (5 / (2 * ε'))
    rw [← hK₀, div_le_iff₀ (by positivity)] at this
    linarith
  have hktε : (4 : ℝ) ≤ ε' * kt := by
    have := Nat.le_ceil (4 / ε')
    rw [← hkt, div_le_iff₀ hε'0] at this
    linarith
  obtain ⟨C₁, Q₀, hC₁0, h112⟩ :=
    S3_le_112.{0} hP (ϖ := 3 / 4) (by norm_num) (by norm_num) (half_pos hε) (2 * (k₀ + 3))
  obtain ⟨C₂, hC₂0, h102⟩ := prop102 hT (half_pos hε)
  have hI0 : 0 ≤ ∫ x, psi0 x := integral_nonneg psi0_nonneg
  have hCJ0 := CJ_nonneg 0
  have hCJK := CJ_nonneg (K₀ + 3)
  have hDK0 := Dpsi_nonneg (2 * (k₀ + 3))
  have hCF := CF_nonneg (kt + 2)
  have hZ2 := Z2_nonneg
  have hBw : 2 ≤ Bw := two_le_Bw
  have hcD : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ0 hδ1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hQ₁64 : (64 : ℝ) ≤ max Q₀ 64 := le_max_right _ _
  have hQ₁0 : 0 < max Q₀ 64 := by linarith
  refine ⟨6 * CJ 0 * (∫ x, psi0 x) * √(12 * C₁) *
      (24 + 12 * √(Dpsi (2 * (k₀ + 3))) + 12 * √(∫ x, psi0 x) * (8 + √C₂)) *
      (LinnikPower.Cdiv δ * (1 / (δ * Real.log 2) + 1) ^ 2) +
    (54 * (CJ (K₀ + 3) / (2 * π) ^ (K₀ + 3)) + (LinnikPower.Cdiv δ * Bw) ^ 3 +
      3 * (2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) *
        (3 + 2 * CF (kt + 2) * Z2 * (9 / (4 * π ^ 2)) * (3 / π) ^ kt) ^ 2) +
    2 ^ ε * (max Q₀ 64) ^ (3 / 2 : ℝ) * (max Q₀ 64 + 1) ^ 3, by positivity, ?_⟩
  intro q _ ι _ R χ t T N σ S b hinj hprim hT1 _ _ hN hNQ hS hb ht hbig
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hQ1 : 1 ≤ (q : ℝ) * T := one_le_mul_of_one_le_of_one_le hq1 hT1
  have hN2 : 1 / 2 ≤ N := by
    have : 1 ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
    linarith
  have hN0 : 0 < N := by linarith
  have hrq : (R.card : ℝ) ≤ (q : ℝ) * T := by
    have h : R.card ≤ q := (card_le_totient R hinj).trans (Nat.totient_le q)
    have h' : (R.card : ℝ) ≤ q := by exact_mod_cast h
    nlinarith
  have hr0 : (0 : ℝ) ≤ R.card := by positivity
  have hE0 : (0 : ℝ) ≤ energy R χ t := by positivity
  have hW1 : ((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) ≤ ((q : ℝ) * T) ^ 2 * (R.card : ℝ) ^ (3 / 2 : ℝ) +
      (q : ℝ) * T * R.card * N ^ (3 - 2 * σ) + (q : ℝ) * T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) +
      ((q : ℝ) * T) ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) := by
    have h1 : 0 ≤ (q : ℝ) * T * R.card * N ^ (3 - 2 * σ) := by positivity
    have h2 : 0 ≤ (q : ℝ) * T * (R.card : ℝ) ^ 2 * N ^ (3 / 2 - σ) := by positivity
    have h3 : 0 ≤ ((q : ℝ) * T) ^ (9 / 8 : ℝ) * (R.card : ℝ) ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ) := by positivity
    linarith
  by_cases hsmall : (q : ℝ) * T < max Q₀ 64
  · have h := small_case R χ t hinj hT1 hε hN hNQ hsmall
    exact final_small h hW1 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  · push Not at hsmall
    have hQ64 : 64 ≤ (q : ℝ) * T := hQ₁64.trans hsmall
    have hQ0 : 0 < (q : ℝ) * T := by linarith
    have hQ₀' : Q₀ ≤ (q : ℝ) * T := (le_max_left _ _).trans hsmall
    have hN8 : 8 ≤ N := by
      have e : ((4 : ℝ) ^ 3) ^ (2 / 3 : ℝ) = 4 ^ 2 := pow_rpow_eq (by norm_num) 3 2 (by norm_num)
      have h16 : (16 : ℝ) ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := by
        calc (16 : ℝ) = ((4 : ℝ) ^ 3) ^ (2 / 3 : ℝ) := by rw [e]; norm_num
          _ ≤ ((q : ℝ) * T) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      linarith
    have hN1 : 1 ≤ N := by linarith
    have hΦQ : (q : ℝ) * T ≤ (q : ℝ) * T * N := le_mul_of_one_le_right hQ0.le hN1
    have hΦ1 : 1 ≤ (q : ℝ) * T * N := hQ1.trans hΦQ
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ((q : ℝ) * T) ^ ε' := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by rw [hX]; exact Real.one_le_rpow hQ1 hε'0.le
    have hX0 : 0 < X := by linarith
    obtain ⟨hM1, hNM, hMlow⟩ := M_props hX1 hN0 hNQ
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊X * ((q : ℝ) * T) / N⌋₊ := ⟨_, rfl⟩
    rw [← hM] at hM1 hNM hMlow
    have h2M := two_M_le hQ64 hN hX hε'1 hNM
    have hNMq : N * M / q ≤ X * T := by
      rw [div_le_iff₀ hq0]
      have e : X * ((q : ℝ) * T) = X * T * q := by ring
      linarith
    have hMΦ : (M : ℝ) ≤ (q : ℝ) * T * N := by
      have h34 : ((q : ℝ) * T) ^ (3 / 4 : ℝ) ≤ (q : ℝ) * T := by
        calc ((q : ℝ) * T) ^ (3 / 4 : ℝ) ≤ ((q : ℝ) * T) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
          _ = (q : ℝ) * T := Real.rpow_one _
      have hM0 : (0 : ℝ) ≤ M := by positivity
      linarith
    obtain ⟨hXk, hXK, hXkt⟩ := orders hQ1 hk₀ε hK₀ε hktε
    rw [← hX] at hXk hXK hXkt
    have hS3 := h112 (X := X) (T := T) (M := M) (Kt := kt + 2) t (K₀ + 3) hinj hQ₀' hT1 ht hN0 hX1 hM1
      (by omega) hNMq h2M
    unfold Gq at hS3
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = ((q : ℝ) * T * N) ^ (ε / 4) := ⟨_, rfl⟩
    have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact Real.one_le_rpow hΦ1 (by positivity)
    have hΛ2 : Λ ^ 2 = ((q : ℝ) * T * N) ^ (ε / 2) := by
      rw [hΛ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    have hS' : ∀ n ∈ S, N < n ∧ (n : ℝ) ≤ 2 * N := fun n hn =>
      ⟨by linarith [(hS n hn).1], by linarith [(hS n hn).2]⟩
    have h102' := h102 q R χ t T N σ S b hinj hprim hT1 ht hN hS' hb hbig
    rw [← hΛ2] at h102'
    have hen := energy_term hr0 hE0 hQ1 hN hΛ1 hC₂0 h102'
    have hm := main_part R hq1 hT1 hN1 hNQ hrq hE0 hε hδ0 hδ1 hδε hε'0 hε'ε hX hXk hM1 hMΦ hC₁0
      (by positivity) hΛ hen hW1
    have he := errors_part R hq1 hT1 hN1 hNQ hrq hε hδ0 hδ1 hδε hX0 hNM hMlow hXK hXkt hW1 (M := M)
    exact final_large (combine3 hS3 hm he) (by positivity) (by positivity)
      (le_trans (by positivity) hW1)

/-- **Their Proposition 3.1 at one point per character, from their Proposition 8.1 and Heath-Brown's Theorem 10.1**:
round 638's `prop31_of_third` with round 639's `third_of_s23`, round 644's `cgls2` and `cgls3`. -/
theorem prop31_pt (hP : CGLP81) (hT : CGLT101) : LinnikCGLLV.CGLProp31 :=
  prop31_of_third (third_of_s23 LinnikCGLS2.cgls2 (cgls3 hP hT))

/-! ### Linnik's theorem -/

/-- **Linnik's theorem with exponent `9/4` from their Proposition 8.1 and Heath-Brown's Theorem 10.1**: round 644's
`linnik_225c_s3` with `cgls3`. -/
theorem linnik_225c_pt (hP : CGLP81) (hT : CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (9 / 4 : ℝ) :=
  LinnikCGLS2.linnik_225c_s3 (cgls3 hP hT)

/-- **Linnik's theorem with exponent `226/100` from their Proposition 8.1 and Heath-Brown's Theorem 10.1**: round
644's `linnik_226c_s3` with `cgls3`. -/
theorem linnik_226c_pt (hP : CGLP81) (hT : CGLT101) : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (226 / 100 : ℝ) :=
  LinnikCGLS2.linnik_226c_s3 (cgls3 hP hT)

end LinnikCGLS3

#print axioms LinnikCGLS3.S3_le_crude
#print axioms LinnikCGLS3.energy_term
#print axioms LinnikCGLS3.natlog_le_rpow
#print axioms LinnikCGLS3.M_props
#print axioms LinnikCGLS3.two_M_le
#print axioms LinnikCGLS3.E1_le
#print axioms LinnikCGLS3.E2_le
#print axioms LinnikCGLS3.tauM_le
#print axioms LinnikCGLS3.E3_le
#print axioms LinnikCGLS3.main_le
#print axioms LinnikCGLS3.small_case
#print axioms LinnikCGLS3.cgls3
#print axioms LinnikCGLS3.prop31_pt
#print axioms LinnikCGLS3.linnik_225c_pt
#print axioms LinnikCGLS3.linnik_226c_pt
