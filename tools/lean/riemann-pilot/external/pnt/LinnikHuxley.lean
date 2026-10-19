/-
# Round 525, part 3: the power trick on `23/29 ≤ σ ≤ 11/12`, and Linnik's exponent `87/35 + η`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `0 < ε ≤ 1/200`, `CharDensity (87/35 + 55ε) 10 C` holds with some `C ≥ 0`
(`charDensity_huxley`): for every `q ≥ 1`, `½ ≤ σ ≤ 1` and `T ≥ 2`, at most `C(qT)^{(87/35+55ε)(1−σ)}(log qT)^{10}`
characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. With round 520's `linnik_of_charDensity`, for
every `η > 0` every reduced class mod `q` has a prime `p ≤ K q^{87/35+η}` (`linnik_eighty_seven_thirty_fifths`), with
no hypothesis. Round 524 had `36/13 + η`. On `52/87 ≤ σ ≤ 23/29` the count is round 524's Ingham argument at
`c = 17/140` (polynomial class `Q^{(2+4c)(1−σ)} = Q^{(87/35)(1−σ)}`); on `23/29 ≤ σ ≤ 11/12` it is the large-values
method: powers of the blocks of the detecting polynomial, the Halász–Montgomery inequality of part 1 and the
off-diagonal bound of part 2, with a short mollifier. Ingham's exponent `3/(2 − σ)` equals `87/35` at `σ = 23/29`.

* `power_count`: characters with `|F(χ, β_χ + iγ_χ)| ≥ V` for a block `F` on `(P, 2P]` with `|c_j| ≤ d(j)` number at
  most `2eG_mΛ/V^{2m}`, `Λ = (2P)^m`, when `2eG_mB ≤ V^{2m}` (`LinnikPower.hm_duality` for `F^m`, with the mass `G_m` of
  `mass_pow_le`).
* `class2_count_small`: the integral class has at most `27A⁴X⁴M₂` members, `A = KG Y^{½−σ}/δ`,
  `M₂ = C₄(q(T + 2))^{1+ε}` (the fourth moment of `LinnikFourth.fourth_moment`): `|M_X| ≤ X` pointwise and
  `l ≤ l⁴/(4λ³) + 3λ/4` at `λ = 1/(3AX)`.
* `block_bin_count`: one dyadic block and one bin `σ_b ≤ β_χ < σ_b + 1/96` of the polynomial class, by `power_count`
  with `LinnikOffDiag.norm_offK_le` at `T′ = 2T` (inside a bin `Re z < 1/48 ≤ (1/12 − δ)/2`).
* `class1_huxley`: the polynomial class for `Q^{1/25} ≤ 2X` and `(2XN)² ≤ Q^{87/70}`: in each block the least `m` with
  `(2P)^m ≥ Q^{29/35+10ε}` (`choose_m`) has `m ≤ 22` and `(2P)^m ≤ Q^{87/70+15ε}`; then `feas_huxley` and the count
  `Q^{(87/35+54ε)(1−σ)}` per block and bin (`count_bound_huxley`).
* `count_huxley`: `LinnikDetect.dichotomy` at `X = ⌊Q^{1/25}⌋`, `Y = Q^{3/5}` (round 518's `Xw`, `Yw`, `Nw` at
  `U = Q^{1/25}`, `c = 7`), `Q = q(T + 6)`, for all large `Q` (`eventually_huxley`); below that at most `q` characters.
* `count_middle_c17`: round 524's `count_nontrivial_ingham` at `c = 17/140`, `δ = 17/174`, with `bound_class2_c17`.
* `charDensity_huxley`: below `52/87` the trivial count; on `[52/87, 23/29]` `count_middle_c17`; on `[23/29, 11/12]`
  `count_huxley`; above `11/12` no character `χ ≠ 1` has a zero (`LinnikLindelof.LFunction_ne_zero`).
-/

import LinnikOffDiag

open Complex Real Filter Topology MeasureTheory Finset

noncomputable section

namespace LinnikHuxley

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag

variable {q : ℕ} [NeZero q]

/-! ### The power count -/

/-- The mass bound for the `m`-th power: `d(n)^{4m} ≤ C^{4m}((2P)^m)^{4mε}` on `(P^m, (2P)^m]`. -/
def Gm (εd : ℝ) (P m : ℕ) (σ : ℝ) : ℝ :=
  Cdiv εd ^ (4 * m) * (((2 * P : ℕ) : ℝ) ^ m) ^ (4 * m * εd) * ((2 * P : ℕ) : ℝ) ^ m * (((P : ℝ) ^ m) ^ (-σ)) ^ 2

/-- **The mass of the `m`-th power** of a block on `(P, 2P]` with `|c_j| ≤ d(j)`:
`Σ_n |c^{(m)}_n|²n^{−2σ} ≤ C^{4m}((2P)^m)^{4mε}(2P)^m(P^m)^{−2σ}`. -/
theorem mass_pow_le {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : S ⊆ Ioc P (2 * P)) {c : ℕ → ℂ}
    (hc : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ)) {m : ℕ} (hm : 1 ≤ m) {σ : ℝ} (hσ : 0 ≤ σ)
    {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) :
    ∑ n ∈ powSupp S m, ‖powCo S c m n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2 ≤ Gm εd P m σ := by
  have hS0 : 0 ∉ S := fun h => by have := (mem_Ioc.1 (hS h)).1; omega
  have hsub := powSupp_sub hS hm
  set L : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hL
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hPm : (0 : ℝ) < (P : ℝ) ^ m := by positivity
  have hterm : ∀ n ∈ powSupp S m, ‖powCo S c m n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2
      ≤ Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) * (((P : ℝ) ^ m) ^ (-σ)) ^ 2 := by
    intro n hn
    have hnI := mem_Ioc.1 (hsub hn)
    have hn1 : ((P ^ m : ℕ) : ℝ) < n := by exact_mod_cast hnI.1
    have hn2 : (n : ℝ) ≤ L := by rw [hL]; exact_mod_cast hnI.2
    have hnpos : (0 : ℝ) < n := by
      have : (0 : ℝ) ≤ ((P ^ m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hco := norm_powCo_le hS0 hc m hn
    have hdiv := card_divisors_le hεd hεd1 n
    have hdiv' : (n.divisors.card : ℝ) ≤ Cdiv εd * L ^ εd :=
      hdiv.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnpos.le hn2 hεd.le)
        (by have := one_le_Cdiv hεd hεd1; linarith))
    have hd0 : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
    have hco2 : ‖powCo S c m n‖ ^ 2 ≤ Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) := by
      calc ‖powCo S c m n‖ ^ 2 ≤ ((n.divisors.card : ℝ) ^ (2 * m)) ^ 2 := by gcongr
        _ = (n.divisors.card : ℝ) ^ (4 * m) := by rw [← pow_mul]; ring_nf
        _ ≤ (Cdiv εd * L ^ εd) ^ (4 * m) := by gcongr
        _ = Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) := by
            rw [mul_pow, ← Real.rpow_natCast (L ^ εd), ← Real.rpow_mul (by positivity)]
            push_cast; ring_nf
    have hns : ((n : ℝ) ^ (-σ)) ^ 2 ≤ (((P : ℝ) ^ m) ^ (-σ)) ^ 2 := by
      have h1 : ((n : ℝ) ^ (-σ)) ≤ ((P : ℝ) ^ m) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hPm (by push_cast at hn1; linarith) (by linarith)
      gcongr
    have hCd0 : 0 ≤ Cdiv εd := by have := one_le_Cdiv hεd hεd1; linarith
    have hA0 : 0 ≤ Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) :=
      mul_nonneg (pow_nonneg hCd0 _) (Real.rpow_nonneg (by rw [hL]; positivity) _)
    exact mul_le_mul hco2 hns (by positivity) hA0
  have hcard : ((powSupp S m).card : ℝ) ≤ L := by
    have h := card_le_card hsub
    rw [Nat.card_Ioc] at h
    rw [hL]
    calc ((powSupp S m).card : ℝ) ≤ (((2 * P) ^ m - P ^ m : ℕ) : ℝ) := by exact_mod_cast h
      _ ≤ (((2 * P) ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ = ((2 * P : ℕ) : ℝ) ^ m := by push_cast; ring
  calc ∑ n ∈ powSupp S m, ‖powCo S c m n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ _n ∈ powSupp S m, Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) * (((P : ℝ) ^ m) ^ (-σ)) ^ 2 :=
        sum_le_sum hterm
    _ = (powSupp S m).card * (Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) * (((P : ℝ) ^ m) ^ (-σ)) ^ 2) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ L * (Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) * (((P : ℝ) ^ m) ^ (-σ)) ^ 2) := by
        have : 0 ≤ Cdiv εd ^ (4 * m) * L ^ (4 * m * εd) * (((P : ℝ) ^ m) ^ (-σ)) ^ 2 := by
          have := one_le_Cdiv hεd hεd1; positivity
        gcongr
    _ = Gm εd P m σ := by rw [Gm, ← hL]; ring

omit [NeZero q] in
/-- **Large values of a power, one point per character**: if `|F(χ)| ≥ V > 0` at `β_χ + iγ_χ` for every
`χ ∈ R`, with `F` a block on `(P, 2P]` with `|c_j| ≤ d(j)`, `β_χ ≥ σ ≥ 0`, and the off-diagonal kernels at length
`Λ = (2P)^m` are at most `B` with `2e·G_m·B ≤ V^{2m}`, then `|R| ≤ 2e·G_m·Λ/V^{2m}` (`hm_duality` for `F^m`). -/
theorem power_count {R : Finset (DirichletCharacter ℂ q)} {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P)
    (hS : S ⊆ Ioc P (2 * P)) {c : ℕ → ℂ} (hc : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ)) {m : ℕ} (hm : 1 ≤ m)
    {σ : ℝ} (hσ : 0 ≤ σ) (β γ : DirichletCharacter ℂ q → ℝ) (hβ : ∀ χ ∈ R, σ ≤ β χ)
    {V : ℝ} (hV : 0 < V) (hbig : ∀ χ ∈ R, V ≤ ‖pv S c χ ((β χ : ℂ) + γ χ * I)‖)
    {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ χ ∈ R, ∀ χ' ∈ R, χ ≠ χ' →
      ‖∑' n : ℕ, kTerm (χ * χ'⁻¹) (((2 * P : ℕ) : ℝ) ^ m)
        (((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I) n‖ ≤ B)
    (hfeas : 2 * Real.exp 1 * Gm εd P m σ * B ≤ V ^ (2 * m)) :
    (R.card : ℝ) ≤ 2 * Real.exp 1 * Gm εd P m σ * ((2 * P : ℕ) : ℝ) ^ m / V ^ (2 * m) := by
  have hS0 : 0 ∉ powSupp S m := fun h => by
    have := mem_Ioc.1 (powSupp_sub hS hm h); omega
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛ
  have h2P : (0 : ℝ) < ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * P)
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hSΛ : ∀ n ∈ powSupp S m, (n : ℝ) ≤ Λ := fun n hn => by
    have := (mem_Ioc.1 (powSupp_sub hS hm hn)).2
    rw [hΛ]; push_cast; exact_mod_cast this
  have hdual := hm_duality hS0 hΛ0 hSΛ (powCo S c m) β γ hβ hB0 hB
  have hmass := mass_pow_le hP hS hc hm hσ hεd hεd1
  set G := Gm εd P m σ with hG
  set R0 : ℝ := (R.card : ℝ) with hR0
  have hR00 : 0 ≤ R0 := Nat.cast_nonneg _
  -- each character contributes at least `V^m`
  have hlow : R0 * V ^ m ≤ ∑ χ ∈ R, ‖pv (powSupp S m) (powCo S c m) χ ((β χ : ℂ) + γ χ * I)‖ := by
    rw [hR0, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun χ hχ => ?_
    rw [← pv_pow, norm_pow]
    exact pow_le_pow_left₀ hV.le (hbig χ hχ) m
  have hVm : 0 < V ^ m := by positivity
  have hsq : (R0 * V ^ m) ^ 2 ≤ Real.exp 1 * G * (R0 * Λ + R0 ^ 2 * B) := by
    have h1 : (R0 * V ^ m) ^ 2 ≤ (∑ χ ∈ R, ‖pv (powSupp S m) (powCo S c m) χ ((β χ : ℂ) + γ χ * I)‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    refine h1.trans (hdual.trans ?_)
    have : 0 ≤ R0 * Λ + R0 ^ 2 * B := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (Real.exp_pos 1).le) this
  -- solve for `R`
  have hV2 : V ^ (2 * m) = (V ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [le_div_iff₀ (by positivity)]
  rcases eq_or_lt_of_le hR00 with h0 | hpos
  · have hG0 : 0 ≤ G := by rw [hG, Gm]; have := one_le_Cdiv hεd hεd1; positivity
    rw [← h0, zero_mul]; positivity
  · have h2 : R0 * (V ^ m) ^ 2 ≤ Real.exp 1 * G * Λ + Real.exp 1 * G * B * R0 := by
      have e : (R0 * V ^ m) ^ 2 = R0 * (R0 * (V ^ m) ^ 2) := by ring
      rw [e] at hsq
      have e2 : Real.exp 1 * G * (R0 * Λ + R0 ^ 2 * B) = R0 * (Real.exp 1 * G * Λ + Real.exp 1 * G * B * R0) := by
        ring
      rw [e2] at hsq
      exact le_of_mul_le_mul_left hsq hpos
    have h3 : Real.exp 1 * G * B * R0 ≤ R0 * (V ^ m) ^ 2 / 2 := by
      rw [← hV2]; nlinarith
    rw [hV2]
    nlinarith

/-- `l ≤ l⁴/(4λ³) + 3λ/4` for `l ≥ 0`, `λ > 0`: `l⁴ − 4λ³l + 3λ⁴ = (l − λ)²(l² + 2λl + 3λ²)`. -/
lemma le_quartic {l lam : ℝ} (hl : 0 ≤ l) (hlam : 0 < lam) : l ≤ l ^ 4 / (4 * lam ^ 3) + 3 * lam / 4 := by
  have e : l ^ 4 / (4 * lam ^ 3) + 3 * lam / 4 - l = (l - lam) ^ 2 * (l ^ 2 + 2 * lam * l + 3 * lam ^ 2) / (4 * lam ^ 3) := by
    field_simp; ring
  have : 0 ≤ (l - lam) ^ 2 * (l ^ 2 + 2 * lam * l + 3 * lam ^ 2) / (4 * lam ^ 3) := by positivity
  linarith

/-- **The integral class with a short mollifier.** Characters `χ ≠ 1` with a zero `ρ_χ = β_χ + iγ_χ`, `σ ≤ β_χ < 1`,
`|γ_χ| ≤ T`, and `|I_χ(ρ_χ)| ≥ ¼` number at most `27A⁴X⁴M₂`, with `A = KG Y^{½−σ}/δ` and `M₂ = C₄(q(T + 2))^{1+ε}`, given
the fourth moment `Σ_χ |L(½ + it_χ, χ)|⁴ ≤ C₄(q(T' + 2))^{1+ε}` over characters `χ ≠ 1` at points `|t_χ| ≤ T'`. On the
line, `|G_χ|(1 + |v|)⁵ ≤ A|M_X||L|` (`Gχ_left_le'`) with `|M_X| ≤ X` (`norm_mollχ_le_X`); then
`l ≤ l⁴/(4λ³) + 3λ/4` at `λ = 1/(3AX)` and the fourth moment at the points `γ_χ + v`. -/
theorem class2_count_small {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {X : ℕ} (hX : 1 ≤ X) {σ δ T Y : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hT : 0 ≤ T) (hY : 1 ≤ Y)
    (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hdet : ∀ χ ∈ Rs, χ ≠ 1 ∧ σ ≤ β χ ∧ β χ < 1 ∧ |γ χ| ≤ T ∧ LFunction χ ((β χ : ℂ) + γ χ * I) = 0
      ∧ 1 / 4 ≤ ‖Ivχ χ X Y ((β χ : ℂ) + γ χ * I)‖) :
    (Rs.card : ℝ) ≤ 27 * (KG * Y ^ (1 / 2 - σ) / δ) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) := by
  classical
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  set A := KG * Y ^ (1 / 2 - σ) / δ with hA
  have hA0 : 0 < A := by
    have := KG_pos
    have : 0 < Y := by linarith
    positivity
  set M₂ := C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε) with hM₂
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  set lam := 1 / (3 * A * X) with hlam
  have hlam0 : 0 < lam := by positivity
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
  set K' := X * (M₂ / (4 * lam ^ 3)) + X * ((Rs.card : ℝ) * (3 * lam / 4)) with hK'
  have hpt : ∀ v : ℝ, ∑ χ ∈ Rs, m χ v * l χ v * wt5 v ≤ K' * (1 + v ^ 2)⁻¹ := by
    intro v
    have hamgm : ∀ χ, m χ v * l χ v ≤ X * (l χ v ^ 4 / (4 * lam ^ 3) + 3 * lam / 4) := by
      intro χ
      calc m χ v * l χ v ≤ X * l χ v := mul_le_mul_of_nonneg_right (hmX χ v) (hl0 χ v)
        _ ≤ X * (l χ v ^ 4 / (4 * lam ^ 3) + 3 * lam / 4) :=
            mul_le_mul_of_nonneg_left (le_quartic (hl0 χ v) hlam0) hX0.le
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
    have hw2 := wt5_mul_sq_le v
    have hw := wt5_le v
    have hc4 : 0 ≤ (X : ℝ) * (M₂ / (4 * lam ^ 3)) := by positivity
    have hc3 : 0 ≤ (X : ℝ) * ((Rs.card : ℝ) * (3 * lam / 4)) := by positivity
    calc ∑ χ ∈ Rs, m χ v * l χ v * wt5 v = wt5 v * ∑ χ ∈ Rs, m χ v * l χ v := by
          rw [mul_sum]; exact sum_congr rfl fun χ _ => by ring
      _ ≤ wt5 v * ∑ χ ∈ Rs, X * (l χ v ^ 4 / (4 * lam ^ 3) + 3 * lam / 4) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => hamgm χ) hw0
      _ = wt5 v * (X * ((∑ χ ∈ Rs, l χ v ^ 4) / (4 * lam ^ 3)) + X * ((Rs.card : ℝ) * (3 * lam / 4))) := by
          rw [← mul_sum, sum_add_distrib, ← sum_div, sum_const, nsmul_eq_mul]; ring
      _ ≤ wt5 v * (X * ((M₂ * (1 + |v|) ^ 2) / (4 * lam ^ 3)) + X * ((Rs.card : ℝ) * (3 * lam / 4))) := by
          gcongr
      _ = X * (M₂ / (4 * lam ^ 3)) * (wt5 v * (1 + |v|) ^ 2) + X * ((Rs.card : ℝ) * (3 * lam / 4)) * wt5 v := by
          ring
      _ ≤ X * (M₂ / (4 * lam ^ 3)) * (1 + v ^ 2)⁻¹ + X * ((Rs.card : ℝ) * (3 * lam / 4)) * (1 + v ^ 2)⁻¹ := by
          gcongr
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
  have e : A / 2 * (X * (M₂ / (4 * lam ^ 3)) + X * ((Rs.card : ℝ) * (3 * lam / 4))) =
      27 * A ^ 4 * (X : ℝ) ^ 4 * M₂ / 8 + (Rs.card : ℝ) / 8 := by
    rw [hlam]; field_simp; ring
  rw [e] at hfin
  linarith

/-! ### The polynomial class, one block and one bin -/

omit [NeZero q] in
/-- A dyadic block of the detecting polynomial is a Dirichlet polynomial `pv` at `s = β + iγ`. -/
theorem Fkχ_eq_pv (χ : DirichletCharacter ℂ q) (X N : ℕ) (Y : ℝ) (k : ℕ) (β γ : ℝ) :
    Fkχ χ X N Y k β γ = pv ((Ioc X (X * N)).filter (fun j => blk X j = k)) (b1 X Y) χ ((β : ℂ) + γ * I) := by
  unfold Fkχ dp pv
  refine sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := by have := (mem_Ioc.1 (mem_filter.1 hj).1).1; omega
  have hn0 : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hnr : (0 : ℝ) < j := by exact_mod_cast hj1
  have hc : (j : ℂ) ^ (-((β : ℂ) + γ * I))
      = (((j : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (-(I * ((γ * Real.log j : ℝ) : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Real.rpow_def_of_pos hnr]
    have hlog : Complex.log (j : ℂ) = (Real.log j : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hnr.le]
    rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hc]; ring

/-- **The mass of a power, as a power of its length**: for `1 ≤ P` and `σ ≤ σ_b`, `σ ≤ 1`,
`G_m(σ_b) ≤ (4C⁴)^m Λ^{1−2σ+4mε}` with `Λ = (2P)^m` (`P^m = Λ/2^m` and `(2^m)^σ ≤ 2^m`). -/
theorem Gm_le {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) {P : ℕ} (hP : 1 ≤ P) (m : ℕ) {σ σb : ℝ} (hσ1 : σ ≤ 1)
    (hσb : σ ≤ σb) :
    Gm εd P m σb ≤ (4 * Cdiv εd ^ 4) ^ m * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 - 2 * σ + 4 * m * εd) := by
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛ
  set Pm : ℝ := (P : ℝ) ^ m with hPm
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPm1 : 1 ≤ Pm := one_le_pow₀ hPr
  have h2m : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hΛe : Λ = 2 ^ m * Pm := by rw [hΛ, hPm]; push_cast; ring
  have hΛ0 : 0 < Λ := by rw [hΛe]; positivity
  have hCd : 1 ≤ Cdiv εd := one_le_Cdiv hεd hεd1
  -- `P_m^{−σ_b} ≤ P_m^{−σ} = Λ^{−σ}(2^m)^σ ≤ Λ^{−σ}2^m`
  have h1 : Pm ^ (-σb) ≤ Pm ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hPm1 (by linarith)
  have h2 : Pm ^ (-σ) = Λ ^ (-σ) * ((2 : ℝ) ^ m) ^ σ := by
    have e : Pm = Λ / 2 ^ m := by rw [hΛe]; field_simp
    rw [e, Real.div_rpow hΛ0.le (by positivity), Real.rpow_neg (x := (2 : ℝ) ^ m) (by positivity), div_inv_eq_mul]
  have h3 : ((2 : ℝ) ^ m) ^ σ ≤ 2 ^ m := by
    calc ((2 : ℝ) ^ m) ^ σ ≤ ((2 : ℝ) ^ m) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2m hσ1
      _ = 2 ^ m := Real.rpow_one _
  have hP0 : 0 ≤ Pm ^ (-σb) := Real.rpow_nonneg (by linarith) _
  have hb : (Pm ^ (-σb)) ^ 2 ≤ (Λ ^ (-σ) * 2 ^ m) ^ 2 := by
    have : Pm ^ (-σb) ≤ Λ ^ (-σ) * 2 ^ m :=
      h1.trans (h2 ▸ mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hΛ0.le _))
    exact pow_le_pow_left₀ hP0 this 2
  have hpow : Λ ^ (4 * (m : ℝ) * εd) * Λ * (Λ ^ (-σ)) ^ 2 = Λ ^ (1 - 2 * σ + 4 * m * εd) := by
    rw [← Real.rpow_natCast (Λ ^ (-σ)) 2, ← Real.rpow_mul hΛ0.le]
    conv_lhs => rw [show Λ ^ (4 * (m : ℝ) * εd) * Λ = Λ ^ (4 * (m : ℝ) * εd) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0, ← Real.rpow_add hΛ0]
    congr 1; push_cast; ring
  unfold Gm
  rw [← hΛ, ← hPm]
  calc Cdiv εd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ * (Pm ^ (-σb)) ^ 2
      ≤ Cdiv εd ^ (4 * m) * Λ ^ (4 * (m : ℝ) * εd) * Λ * (Λ ^ (-σ) * 2 ^ m) ^ 2 := by
        gcongr
    _ = (4 * Cdiv εd ^ 4) ^ m * (Λ ^ (4 * (m : ℝ) * εd) * Λ * (Λ ^ (-σ)) ^ 2) := by
        have h4m : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [mul_pow (Λ ^ (-σ)), h4m]; ring
    _ = (4 * Cdiv εd ^ 4) ^ m * Λ ^ (1 - 2 * σ + 4 * m * εd) := by rw [hpow]

omit [NeZero q] in
/-- **One block, one bin.** Characters `χ ∈ R` with points `β_χ + iγ_χ`, `σ_b ≤ β_χ < σ_b + 1/96`, `|γ_χ| ≤ T`, at which
a block `F = Σ_{j∈S} c_jχ(j)j^{−s}` on `(P, 2P]` with `|c_j| ≤ d(j)` is at least `V`: given the off-diagonal bound
`|K_Λ(ψ, z)| ≤ C₁Λ^{1/12−δ}(q(T' + 2))^{5/12+δ+2ε'}` (`norm_offK_le` at this modulus) and the feasibility
`2e G_m(σ_b) B ≤ V^{2m}` with `B` that bound at `Λ = (2P)^m`, `T' = 2T`, the count is at most
`2e G_m(σ_b) Λ/V^{2m}` (`power_count`). -/
theorem block_bin_count {R : Finset (DirichletCharacter ℂ q)} {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P)
    (hS : S ⊆ Ioc P (2 * P)) {c : ℕ → ℂ} (hc : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ)) {m : ℕ} (hm : 1 ≤ m)
    {σb : ℝ} (hσb : 0 ≤ σb) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σb ≤ β χ ∧ β χ < σb + 1 / 96) {T : ℝ} (hT : 0 ≤ T) (hγ : ∀ χ ∈ R, |γ χ| ≤ T)
    {V : ℝ} (hV : 0 < V) (hbig : ∀ χ ∈ R, V ≤ ‖pv S c χ ((β χ : ℂ) + γ χ * I)‖)
    {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) {δ ε' C₁ : ℝ} (hδ1 : δ ≤ 1 / 24) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ (1 / 12 - δ) / 2 →
      ∀ T' : ℝ, |z.im| ≤ T' →
        ‖∑' n, kTerm ψ Λ z n‖ ≤ C₁ * Λ ^ (1 / 12 - δ) * ((q : ℝ) * (T' + 2)) ^ (5 / 12 + δ + 2 * ε'))
    (hfeas : 2 * Real.exp 1 * Gm εd P m σb * (C₁ * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 / 12 - δ) *
      ((q : ℝ) * (2 * T + 2)) ^ (5 / 12 + δ + 2 * ε')) ≤ V ^ (2 * m)) :
    (R.card : ℝ) ≤ 2 * Real.exp 1 * Gm εd P m σb * ((2 * P : ℕ) : ℝ) ^ m / V ^ (2 * m) := by
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) ^ m := one_le_pow₀ h2P
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hB0 : 0 ≤ C₁ * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 / 12 - δ) * ((q : ℝ) * (2 * T + 2)) ^ (5 / 12 + δ + 2 * ε') := by
    positivity
  refine power_count hP hS hc hm hσb β γ (fun χ hχ => (hβ χ hχ).1) hV hbig hεd hεd1 hB0 ?_ hfeas
  intro χ hχ χ' hχ' hne
  have hψ : χ * χ'⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h)
  have hzre : (((β χ + β χ' - 2 * σb : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I).re = β χ + β χ' - 2 * σb := by simp
  have hzim : (((β χ + β χ' - 2 * σb : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I).im = γ χ - γ χ' := by simp
  have h1 := hβ χ hχ
  have h2 := hβ χ' hχ'
  have g1 := abs_le.1 (hγ χ hχ)
  have g2 := abs_le.1 (hγ χ' hχ')
  exact hC₁ (χ * χ'⁻¹) hψ _ hΛ1 _ (by rw [hzre]; linarith) (by rw [hzre]; linarith) (2 * T)
    (by rw [hzim]; exact abs_le.2 ⟨by linarith, by linarith⟩)

/-! ### The exponent bookkeeping in the range `23/29 ≤ σ ≤ 11/12` -/

/-- **The power of a block**: for `x ≥ Q^{1/25}` and `0 < a ≤ 22/25` some `m` with `Q^a ≤ x^m` has `1 ≤ m ≤ 22`
and `x^m ≤ max(x², Q^{3a/2})`; the proof takes the least such `m` (for `m ≥ 3`, `x² ≤ x^{m−1} < Q^a`). -/
lemma choose_m {Q a x : ℝ} (hQ : 1 < Q) (ha : 0 < a) (ha22 : a ≤ 22 / 25) (hx : Q ^ (1 / 25 : ℝ) ≤ x) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 22 ∧ Q ^ a ≤ x ^ m ∧ x ^ m ≤ max (x ^ 2) (Q ^ (3 * a / 2)) := by
  classical
  have hQ0 : 0 < Q := by linarith
  have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hQ.le (by norm_num)) hx
  have h22 : Q ^ a ≤ x ^ 22 := by
    calc Q ^ a ≤ Q ^ (22 / 25 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ.le ha22
      _ = (Q ^ (1 / 25 : ℝ)) ^ (22 : ℕ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
      _ ≤ x ^ 22 := pow_le_pow_left₀ (by positivity) hx 22
  have hex : ∃ m : ℕ, Q ^ a ≤ x ^ m := ⟨22, h22⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex h22, Nat.find_spec hex, ?_⟩
  · by_contra h0
    have hm0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hm0, pow_zero] at this
    exact absurd this (not_le.2 (Real.one_lt_rpow hQ ha))
  · set m := Nat.find hex with hm
    rcases le_or_gt m 2 with h2 | h3
    · exact le_max_of_le_left (pow_le_pow_right₀ hx1 h2)
    · refine le_max_of_le_right ?_
      have h1 : x ^ (m - 1) < Q ^ a := not_le.1 (Nat.find_min hex (by omega : m - 1 < m))
      have h2 : x ^ 2 ≤ x ^ (m - 1) := pow_le_pow_right₀ hx1 (by omega)
      have e1 : (x ^ m) ^ 2 = (x ^ (m - 1)) ^ 2 * x ^ 2 := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
      have e2 : (Q ^ (3 * a / 2)) ^ 2 = (Q ^ a) ^ 2 * Q ^ a := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_natCast (Q ^ a), ← Real.rpow_mul hQ0.le,
          ← Real.rpow_add hQ0]
        congr 1; push_cast; ring
      have h3 : (x ^ m) ^ 2 ≤ (Q ^ (3 * a / 2)) ^ 2 := by
        rw [e1, e2]
        have hxm0 : 0 ≤ x ^ (m - 1) := by positivity
        exact mul_le_mul (pow_le_pow_left₀ hxm0 h1.le 2) (h2.trans h1.le) (by positivity) (by positivity)
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h3

omit [NeZero q] in
/-- `⌊log₂ N⌋ + 1 ≤ 1 + 2 log Q` for `1 ≤ N ≤ Q`. -/
lemma log_blocks_le {N : ℕ} (hN : 1 ≤ N) {Q : ℝ} (hNQ : (N : ℝ) ≤ Q) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 1 + 2 * Real.log Q := by
  have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ) ^ Nat.log 2 N) ≤ Q := le_trans (by exact_mod_cast h1) hNQ
  have h3 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log Q := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2
  have h4 := Real.log_two_gt_d9
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ Nat.log 2 N)
    (by linarith : (0 : ℝ) ≤ 2 * Real.log 2 - 1)]

omit [NeZero q] in
/-- **Feasibility of the power count** in `23/29 ≤ σ ≤ σ_b`: with `Λ = (2P)^m ≥ Q^a`, `a = 29/35 + 10ε`, `m ≤ 22`,
`ε_d = ε/88`, `4K ≤ Q^{ε/528}` and `4eC₁(4C⁴)^{22} ≤ Q^ε`, `2e G_m(σ_b) B ≤ (4K)^{−2m}`. The off-diagonal bound carries
`Λ^{13/12−2σ} ≤ Λ^{−175/348} ≤ Q^{−5/12−(875/174)ε}` against `Q^{5/12+3ε}`. -/
lemma feas_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁) {σ σb Q T : ℝ}
    (hσ : 23 / 29 ≤ σ) (hσb : σ ≤ σb) (hσ1 : σ ≤ 1) (hQ1 : 1 ≤ Q) (hT : 0 ≤ T)
    (hqT : (q : ℝ) * (2 * T + 2) ≤ 2 * Q) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 22)
    (hΛ : Q ^ (29 / 35 + 10 * ε) ≤ ((2 * P : ℕ) : ℝ) ^ m) {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ Q ^ (ε / 528))
    (hfe : 4 * Real.exp 1 * C₁ * (4 * Cdiv (ε / 88) ^ 4) ^ 22 ≤ Q ^ ε) :
    2 * Real.exp 1 * Gm (ε / 88) P m σb * (C₁ * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 / 12 - ε) *
      ((q : ℝ) * (2 * T + 2)) ^ (5 / 12 + ε + 2 * ε)) ≤ (1 / (4 * K)) ^ (2 * m) := by
  have hQ0 : 0 < Q := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hεd : 0 < ε / 88 := by positivity
  have hεd1 : ε / 88 ≤ 1 := by linarith
  set A : ℝ := 4 * Cdiv (ε / 88) ^ 4 with hA
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
  have hGm : Gm (ε / 88) P m σb ≤ A ^ 22 * Λ ^ (1 - 2 * σ + ε) := by
    refine (Gm_le hεd hεd1 hP m hσ1 hσb).trans ?_
    rw [← hA, ← hΛdef]
    exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
      (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) * (2 * T + 2) := by positivity
  have hqB : ((q : ℝ) * (2 * T + 2)) ^ (5 / 12 + ε + 2 * ε) ≤ 2 * Q ^ (5 / 12 + 3 * ε) := by
    calc ((q : ℝ) * (2 * T + 2)) ^ (5 / 12 + ε + 2 * ε) ≤ (2 * Q) ^ (5 / 12 + ε + 2 * ε) :=
          Real.rpow_le_rpow hq0 hqT (by positivity)
      _ = (2 : ℝ) ^ (5 / 12 + ε + 2 * ε) * Q ^ (5 / 12 + 3 * ε) := by
          rw [Real.mul_rpow (by norm_num) hQ0.le]; ring_nf
      _ ≤ 2 * Q ^ (5 / 12 + 3 * ε) := by
          gcongr
          calc (2 : ℝ) ^ (5 / 12 + ε + 2 * ε) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have hcomb : Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 - ε) = Λ ^ (13 / 12 - 2 * σ) := by
    rw [← Real.rpow_add hΛ0]; ring_nf
  have hneg : Λ ^ (13 / 12 - 2 * σ) ≤ Q ^ (-5 / 12 - 875 / 174 * ε) := by
    calc Λ ^ (13 / 12 - 2 * σ) ≤ Λ ^ (-175 / 348 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ1 (by linarith)
      _ ≤ (Q ^ (29 / 35 + 10 * ε)) ^ (-175 / 348 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hΛ (by norm_num)
      _ = Q ^ (-5 / 12 - 875 / 174 * ε) := by rw [← Real.rpow_mul hQ0.le]; ring_nf
  have hQe : Q ^ (-5 / 12 - 875 / 174 * ε) * Q ^ (5 / 12 + 3 * ε) ≤ Q ^ (-2 * ε) := by
    rw [← Real.rpow_add hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : Q ^ (-ε) ≤ (1 / (4 * K)) ^ (2 * m) := by
    have hK0 : 0 < 4 * K := by linarith
    have h1 : Q ^ (-(ε / 528)) ≤ 1 / (4 * K) := by
      rw [Real.rpow_neg hQ0.le, one_div]
      exact inv_anti₀ hK0 hK
    calc Q ^ (-ε) ≤ Q ^ (-(ε / 528) * (2 * m : ℕ)) := by
          refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
          push_cast; nlinarith
      _ = (Q ^ (-(ε / 528))) ^ (2 * m) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ (1 / (4 * K)) ^ (2 * m) := pow_le_pow_left₀ (by positivity) h1 _
  have hΛa : 0 ≤ Λ ^ (1 / 12 - ε) := by positivity
  have hΛb : 0 ≤ Λ ^ (1 - 2 * σ + ε) := by positivity
  calc 2 * Real.exp 1 * Gm (ε / 88) P m σb * (C₁ * Λ ^ (1 / 12 - ε) *
        ((q : ℝ) * (2 * T + 2)) ^ (5 / 12 + ε + 2 * ε))
      ≤ 2 * Real.exp 1 * (A ^ 22 * Λ ^ (1 - 2 * σ + ε)) * (C₁ * Λ ^ (1 / 12 - ε) * (2 * Q ^ (5 / 12 + 3 * ε))) := by
        have hG0 : 0 ≤ Gm (ε / 88) P m σb := by unfold Gm; positivity
        gcongr
    _ = 4 * Real.exp 1 * C₁ * A ^ 22 * (Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 - ε)) * Q ^ (5 / 12 + 3 * ε) := by ring
    _ = 4 * Real.exp 1 * C₁ * A ^ 22 * Λ ^ (13 / 12 - 2 * σ) * Q ^ (5 / 12 + 3 * ε) := by rw [hcomb]
    _ ≤ 4 * Real.exp 1 * C₁ * A ^ 22 * Q ^ (-5 / 12 - 875 / 174 * ε) * Q ^ (5 / 12 + 3 * ε) := by gcongr
    _ = 4 * Real.exp 1 * C₁ * A ^ 22 * (Q ^ (-5 / 12 - 875 / 174 * ε) * Q ^ (5 / 12 + 3 * ε)) := by ring
    _ ≤ 4 * Real.exp 1 * C₁ * A ^ 22 * Q ^ (-2 * ε) := by gcongr
    _ ≤ Q ^ ε * Q ^ (-2 * ε) := by gcongr
    _ = Q ^ (-ε) := by rw [← Real.rpow_add hQ0]; ring_nf
    _ ≤ (1 / (4 * K)) ^ (2 * m) := hR

/-- **The count of one block and one bin as a power of `Q`**: with `Λ = (2P)^m ≤ Q^{87/70+15ε}`, `m ≤ 22`,
`4K ≤ Q^{ε/528}` and `σ ≤ 11/12`, `2e G_m(σ_b) Λ (4K)^{2m} ≤ 2e(4C⁴)^{22} Q^{(87/35+54ε)(1−σ)}`. -/
lemma count_bound_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {σ σb Q : ℝ}
    (hσ11 : σ ≤ 11 / 12) (hσb : σ ≤ σb) (hQ1 : 1 ≤ Q) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 22)
    (hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (87 / 70 + 15 * ε)) {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ Q ^ (ε / 528)) :
    2 * Real.exp 1 * Gm (ε / 88) P m σb * ((2 * P : ℕ) : ℝ) ^ m / (1 / (4 * K)) ^ (2 * m)
      ≤ 2 * Real.exp 1 * (4 * Cdiv (ε / 88) ^ 4) ^ 22 * Q ^ ((87 / 35 + 54 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hεd : 0 < ε / 88 := by positivity
  have hεd1 : ε / 88 ≤ 1 := by linarith
  set A : ℝ := 4 * Cdiv (ε / 88) ^ 4 with hA
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 22 := by exact_mod_cast hm
  have hGm : Gm (ε / 88) P m σb ≤ A ^ 22 * Λ ^ (1 - 2 * σ + ε) := by
    refine (Gm_le hεd hεd1 hP m (by linarith) hσb).trans ?_
    rw [← hA, ← hΛdef]
    exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
      (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (2 * m) ≤ Q ^ (ε / 12) := by
    calc (4 * K) ^ (2 * m) ≤ (Q ^ (ε / 528)) ^ (2 * m) := pow_le_pow_left₀ hK0.le hK _
      _ = Q ^ (ε / 528 * (2 * m : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
      _ ≤ Q ^ (ε / 12) := Real.rpow_le_rpow_of_exponent_le hQ1 (by push_cast; nlinarith)
  have hpow : Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (2 - 2 * σ + ε) := by
    conv_lhs => rw [show Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hΛ0]; ring_nf
  have hΛQ : Λ ^ (2 - 2 * σ + ε) ≤ Q ^ ((87 / 70 + 15 * ε) * (2 - 2 * σ + ε)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow hΛ0.le hΛ (by linarith)
  have hexp : (87 / 70 + 15 * ε) * (2 - 2 * σ + ε) + ε / 12 ≤ (87 / 35 + 54 * ε) * (1 - σ) := by nlinarith
  have hG0 : 0 ≤ Gm (ε / 88) P m σb := by unfold Gm; positivity
  calc 2 * Real.exp 1 * Gm (ε / 88) P m σb * Λ / (1 / (4 * K)) ^ (2 * m)
      = 2 * Real.exp 1 * Gm (ε / 88) P m σb * Λ * (4 * K) ^ (2 * m) := by
        rw [one_div, inv_pow, div_inv_eq_mul]
    _ ≤ 2 * Real.exp 1 * (A ^ 22 * Λ ^ (1 - 2 * σ + ε)) * Λ * Q ^ (ε / 12) := by gcongr
    _ = 2 * Real.exp 1 * A ^ 22 * (Λ ^ (1 - 2 * σ + ε) * Λ) * Q ^ (ε / 12) := by ring
    _ = 2 * Real.exp 1 * A ^ 22 * Λ ^ (2 - 2 * σ + ε) * Q ^ (ε / 12) := by rw [hpow]
    _ ≤ 2 * Real.exp 1 * A ^ 22 * Q ^ ((87 / 70 + 15 * ε) * (2 - 2 * σ + ε)) * Q ^ (ε / 12) := by gcongr
    _ = 2 * Real.exp 1 * A ^ 22 * Q ^ ((87 / 70 + 15 * ε) * (2 - 2 * σ + ε) + ε / 12) := by
        rw [mul_assoc _ (Q ^ _), ← Real.rpow_add hQ0]
    _ ≤ 2 * Real.exp 1 * A ^ 22 * Q ^ ((87 / 35 + 54 * ε) * (1 - σ)) := by
        gcongr

omit [NeZero q] in
/-- **The integral class as a power of `Q`**: with `Y = Q^{3/5}`, `X ≤ Q^{1/25}`, `q(T + 2) ≤ Q`, `δ = 1/4` and
`σ ≤ 11/12`, `27A⁴X⁴M₂ ≤ 27(4KG)⁴C₄Q^{(87/35)(1−σ)}`: the exponent `59/25 − (12/5)σ + ε` falls short of
`(87/35)(1 − σ)` by `(22 − 15σ)/175 − ε ≥ 0`. -/
lemma class2_bound_huxley {ε C₄ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hC₄ : 0 ≤ C₄) {σ T Q : ℝ}
    (hσ1 : σ ≤ 11 / 12) (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X : ℕ} (hXQ : (X : ℝ) ≤ Q ^ (1 / 25 : ℝ)) :
    27 * (KG * (Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (87 / 35 * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hY : ((Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = Q ^ (12 / 5 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ Q ^ (4 / 25 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (Q ^ (1 / 25 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXQ 4
      _ = Q ^ (4 / 25 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
  have hM : ((q : ℝ) * (T + 2)) ^ (1 + ε) ≤ Q ^ (1 + ε) := Real.rpow_le_rpow (by positivity) hqT (by linarith)
  have hexp : 12 / 5 * (1 / 2 - σ) + 4 / 25 + (1 + ε) ≤ 87 / 35 * (1 - σ) := by linarith
  calc 27 * (KG * (Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      = 27 * (4 * KG) ^ 4 * C₄ * (((Q ^ (3 / 5 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 *
          ((q : ℝ) * (T + 2)) ^ (1 + ε)) := by ring
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * (Q ^ (12 / 5 * (1 / 2 - σ)) * Q ^ (4 / 25 : ℝ) * Q ^ (1 + ε)) := by
        rw [hY]; gcongr
    _ = 27 * (4 * KG) ^ 4 * C₄ * Q ^ (12 / 5 * (1 / 2 - σ) + 4 / 25 + (1 + ε)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    _ ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (87 / 35 * (1 - σ)) := by
        gcongr

/-! ### The polynomial class in the range `23/29 ≤ σ ≤ 11/12` -/

/-- **The polynomial class with powers.** Characters with one point `β_χ + iγ_χ` each, `σ ≤ β_χ < 1`, `|γ_χ| ≤ T`,
and `|P_χ(β_χ + iγ_χ)| ≥ ¼` number at most `20K·2e(4C⁴)^{22}Q^{(87/35+54ε)(1−σ)}`, `K = ⌊log₂ N⌋ + 1`, `C = C(ε/88)`,
for `23/29 ≤ σ ≤ 11/12`: some dyadic block is at least `1/(4K)` (`Pvχ_eq_blocks`); bins of width `1/96` in `β`; in
each block and bin the least power `m` with `(2P)^m ≥ Q^{29/35+10ε}` (`choose_m`), at most `Q^{87/70+15ε}` long, and
`block_bin_count` with `feas_huxley` and `count_bound_huxley`. -/
theorem class1_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ (1 / 12 - ε) / 2 →
      ∀ T' : ℝ, |z.im| ≤ T' →
        ‖∑' n, kTerm ψ Λ z n‖ ≤ C₁ * Λ ^ (1 / 12 - ε) * ((q : ℝ) * (T' + 2)) ^ (5 / 12 + ε + 2 * ε))
    {σ T Q : ℝ} (hσ : 23 / 29 ≤ σ) (hσ1 : σ ≤ 11 / 12) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (2 * T + 2) ≤ 2 * Q)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXQ : Q ^ (1 / 25 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 528))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (87 / 70 : ℝ))
    (hfe : 4 * Real.exp 1 * C₁ * (4 * Cdiv (ε / 88) ^ 4) ^ 22 ≤ Q ^ ε)
    {Y : ℝ} (hY : 0 < Y) (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ < 1) (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T)
    (hbig : ∀ χ ∈ Rs, 1 / 4 ≤ ‖Pvχ χ X N Y (β χ) (γ χ)‖) :
    (Rs.card : ℝ) ≤ 20 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * (2 * Real.exp 1 * (4 * Cdiv (ε / 88) ^ 4) ^ 22 *
      Q ^ ((87 / 35 + 54 * ε) * (1 - σ))) := by
  classical
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set B := 2 * Real.exp 1 * (4 * Cdiv (ε / 88) ^ 4) ^ 22 * Q ^ ((87 / 35 + 54 * ε) * (1 - σ)) with hB
  -- some block of each character is at least `V`
  have hlarge : ∀ χ ∈ Rs, ∃ k ∈ range K, V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ := by
    intro χ hχ
    by_contra hcon
    push Not at hcon
    have h1 := hbig χ hχ
    rw [Pvχ_eq_blocks χ X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkχ χ X N Y k (β χ) (γ χ)‖ < ∑ _k ∈ range K, V :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * V = 1 / 4 := by rw [hV]; field_simp
    linarith [(norm_sum_le (range K) fun k => Fkχ χ X N Y k (β χ) (γ χ)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → ℕ → Finset (DirichletCharacter ℂ q) := fun k j =>
    Rs.filter fun χ => V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ ∧ ⌊96 * (β χ - σ)⌋₊ = j with hCkdef
  have hsub : Rs ⊆ (range K).biUnion fun k => (range 20).biUnion fun j => Ck k j := by
    intro χ hχ
    obtain ⟨k, hk, hbigk⟩ := hlarge χ hχ
    have h1 := hβ χ hχ
    have hj : ⌊96 * (β χ - σ)⌋₊ < 20 := by
      rw [Nat.floor_lt (by linarith)]
      push_cast
      linarith
    exact mem_biUnion.2 ⟨k, hk, mem_biUnion.2 ⟨_, mem_range.2 hj, mem_filter.2 ⟨hχ, hbigk, rfl⟩⟩⟩
  have hCk : ∀ k ∈ range K, ∀ j ∈ range 20, ((Ck k j).card : ℝ) ≤ B := by
    intro k hk j _
    set P := 2 ^ k * X with hPdef
    have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ X * N := by
      rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le (mem_range.1 hk) hN)
    have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
    have hSsub : (Ioc X (X * N)).filter (fun j => blk X j = k) ⊆ Ioc P (2 * P) := block_sub hX
    have h2Px : Q ^ (1 / 25 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
      have : (2 * (X : ℝ)) ≤ ((2 * P : ℕ) : ℝ) := by
        have h := (by omega : 2 * X ≤ 2 * P)
        have h' : ((2 * X : ℕ) : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h' ⊢; linarith
      linarith
    obtain ⟨m, hm1, hm22, hΛlo, hΛhi⟩ :=
      choose_m hQ1 (by positivity : (0 : ℝ) < 29 / 35 + 10 * ε) (by linarith) h2Px
    have hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ (87 / 70 + 15 * ε) := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ Q ^ (87 / 70 : ℝ) := hXN
          _ ≤ Q ^ (87 / 70 + 15 * ε) := Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith)
      · rw [show 3 * (29 / 35 + 10 * ε) / 2 = 87 / 70 + 15 * ε by ring]
    set σb : ℝ := σ + j / 96 with hσb
    have hσσb : σ ≤ σb := by
      have : (0 : ℝ) ≤ (j : ℝ) / 96 := by positivity
      rw [hσb]; linarith
    have hbin : ∀ χ ∈ Ck k j, σb ≤ β χ ∧ β χ < σb + 1 / 96 := by
      intro χ hχ
      obtain ⟨hχR, -, hbj⟩ := mem_filter.1 hχ
      have h0 : 0 ≤ 96 * (β χ - σ) := by have := (hβ χ hχR).1; linarith
      have h1 : ((⌊96 * (β χ - σ)⌋₊ : ℕ) : ℝ) ≤ 96 * (β χ - σ) := Nat.floor_le h0
      have h2 : 96 * (β χ - σ) < ((⌊96 * (β χ - σ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hbj] at h1 h2
      rw [hσb]
      constructor <;> linarith
    have hcount := block_bin_count (R := Ck k j) hP hSsub (c := b1 X Y) (fun i _ => norm_b1_le X hY i) hm1
      (σb := σb) (by linarith) β γ hbin hT (fun χ hχ => hγ χ (mem_filter.1 hχ).1) hV0
      (fun χ hχ => by rw [← Fkχ_eq_pv]; exact (mem_filter.1 hχ).2.1) (εd := ε / 88) (by positivity)
      (by linarith) (δ := ε) (ε' := ε) (by linarith) hC₁0 hC₁
      (feas_huxley hε hε1 hC₁0 hσ hσσb (by linarith) hQ1.le hT hqT hP hm22 hΛlo hK1 hK hfe)
    exact hcount.trans (count_bound_huxley hε hε1 hσ1 hσσb hQ1.le hP hm22 hΛ hK1 hK)
  calc (Rs.card : ℝ) ≤ ((range K).biUnion fun k => (range 20).biUnion fun j => Ck k j).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, (((range 20).biUnion fun j => Ck k j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range 20, ((Ck k j).card : ℝ) := by
        gcongr with k hk; exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range 20, B := by
        gcongr with k hk j hj; exact hCk k hk j hj
    _ = 20 * (K : ℝ) * B := by simp only [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-! ### Large `Q` -/

/-- The conditions on `Q` used in the range `23/29 ≤ σ ≤ 11/12` hold for all large `Q`: `log Q ≤ Q^η/η`
(`Real.log_le_rpow_div`) and `c ≤ Q^θ` eventually. -/
lemma eventually_huxley {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ Q : ℝ in atTop, (8 : ℝ) ^ 25 ≤ Q ∧ 4 * (1 + 2 * Real.log Q) ≤ Q ^ (ε / 528) ∧
      (2 * (23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)))) ^ 2 ≤ Q ^ (87 / 70 : ℝ) ∧
      23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)) ≤ Q ∧ A ≤ Q ^ ε := by
  have hev : ∀ c θ : ℝ, 0 < θ → ∀ᶠ Q : ℝ in atTop, c ≤ Q ^ θ := fun c θ hθ =>
    (tendsto_rpow_atTop hθ).eventually_ge_atTop c
  set r := ε / 528 with hr
  have hr0 : 0 < r := by positivity
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 25), hev (4 + 16 / r) (r / 2) (by positivity),
    hev ((138 / 5) ^ 2 * 140 ^ 2) (1 / 35) (by norm_num), hev 69 (1 / 5) (by norm_num), hev A ε hε]
    with Q h1 h2 h3 h4 h5
  have hQ1 : 1 ≤ Q := le_trans (by norm_num) h1
  have hQ0 : 0 < Q := by linarith
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlog : Real.log (Q ^ (3 / 5 : ℝ)) = 3 / 5 * Real.log Q := Real.log_rpow hQ0 _
  refine ⟨h1, ?_, ?_, ?_, h5⟩
  · have hl : Real.log Q ≤ Q ^ (r / 2) / (r / 2) := Real.log_le_rpow_div hQ0.le (by positivity)
    have hQr : 1 ≤ Q ^ (r / 2) := Real.one_le_rpow hQ1 (by positivity)
    calc 4 * (1 + 2 * Real.log Q) ≤ 4 * (1 + 2 * (Q ^ (r / 2) / (r / 2))) := by gcongr
      _ = 4 + 16 / r * Q ^ (r / 2) := by field_simp; ring
      _ ≤ (4 + 16 / r) * Q ^ (r / 2) := by
          have : 0 ≤ 16 / r := by positivity
          nlinarith
      _ ≤ Q ^ (r / 2) * Q ^ (r / 2) := by gcongr
      _ = Q ^ r := by rw [← Real.rpow_add hQ0]; ring_nf
  · have hl : Real.log Q ≤ 140 * Q ^ (1 / 140 : ℝ) := by
      have h := Real.log_le_rpow_div hQ0.le (by norm_num : (0 : ℝ) < 1 / 140)
      calc Real.log Q ≤ Q ^ (1 / 140 : ℝ) / (1 / 140) := h
        _ = 140 * Q ^ (1 / 140 : ℝ) := by ring
    calc (2 * (23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)))) ^ 2
        = (138 / 5) ^ 2 * (Q ^ (3 / 5 : ℝ)) ^ 2 * Real.log Q ^ 2 := by rw [hlog]; ring
      _ ≤ (138 / 5) ^ 2 * (Q ^ (3 / 5 : ℝ)) ^ 2 * (140 * Q ^ (1 / 140 : ℝ)) ^ 2 := by gcongr
      _ = (138 / 5) ^ 2 * 140 ^ 2 * Q ^ (85 / 70 : ℝ) := by
          rw [← Real.rpow_natCast (Q ^ (3 / 5 : ℝ)), ← Real.rpow_mul hQ0.le, mul_pow,
            ← Real.rpow_natCast (Q ^ (1 / 140 : ℝ)), ← Real.rpow_mul hQ0.le]
          have e : (Q ^ ((3 / 5 : ℝ) * ((2 : ℕ) : ℝ))) * Q ^ ((1 / 140 : ℝ) * ((2 : ℕ) : ℝ)) = Q ^ (85 / 70 : ℝ) := by
            rw [← Real.rpow_add hQ0]; norm_num
          rw [← e]; ring
      _ ≤ Q ^ (1 / 35 : ℝ) * Q ^ (85 / 70 : ℝ) := by gcongr
      _ = Q ^ (87 / 70 : ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
  · have hl : Real.log Q ≤ 5 * Q ^ (1 / 5 : ℝ) := by
      have h := Real.log_le_rpow_div hQ0.le (by norm_num : (0 : ℝ) < 1 / 5)
      calc Real.log Q ≤ Q ^ (1 / 5 : ℝ) / (1 / 5) := h
        _ = 5 * Q ^ (1 / 5 : ℝ) := by ring
    calc 23 * Q ^ (3 / 5 : ℝ) * Real.log (Q ^ (3 / 5 : ℝ)) = 69 / 5 * Q ^ (3 / 5 : ℝ) * Real.log Q := by
          rw [hlog]; ring
      _ ≤ 69 / 5 * Q ^ (3 / 5 : ℝ) * (5 * Q ^ (1 / 5 : ℝ)) := by gcongr
      _ = 69 * Q ^ (4 / 5 : ℝ) := by
          have e : Q ^ (3 / 5 : ℝ) * Q ^ (1 / 5 : ℝ) = Q ^ (4 / 5 : ℝ) := by rw [← Real.rpow_add hQ0]; norm_num
          rw [← e]; ring
      _ ≤ Q ^ (1 / 5 : ℝ) * Q ^ (4 / 5 : ℝ) := by gcongr
      _ = Q := by rw [← Real.rpow_add hQ0]; norm_num

open scoped Classical in
/-- **The range `23/29 ≤ σ ≤ 11/12` at one large `Q`.** With `X, N, Y` the detector's parameters
(`22Y log Y ≤ XN`, `Y = Q^{3/5}`, `Q^{1/25} ≤ 2X`, `X ≤ Q^{1/25}`) and the large-`Q` conditions of `eventually_huxley`,
at most `5B₁Q^E + 27(4KG)⁴C₄Q^E` characters `χ ≠ 1` mod `q` have a zero in `Re s ≥ σ`, `|Im s| ≤ T`, with
`B₁ = 2e(4C(ε/88)⁴)^{22}` and `E = (87/35 + 55ε)(1 − σ)`: `LinnikDetect.dichotomy`, `class1_huxley`, `class2_count_small`
and `class2_bound_huxley`. -/
theorem count_huxley_at {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ (1 / 12 - ε) / 2 →
      ∀ T' : ℝ, |z.im| ≤ T' →
        ‖∑' n, kTerm ψ Λ z n‖ ≤ C₁ * Λ ^ (1 / 12 - ε) * ((q : ℝ) * (T' + 2)) ^ (5 / 12 + ε + 2 * ε))
    {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {σ T Q : ℝ} (hσ : 23 / 29 ≤ σ) (hσ1 : σ ≤ 11 / 12) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q) (hqT2 : (q : ℝ) * (2 * T + 2) ≤ 2 * Q)
    {X N : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hY8 : 8 ≤ Y) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hYQ : Y = Q ^ (3 / 5 : ℝ)) (hXU : (X : ℝ) ≤ Q ^ (1 / 25 : ℝ)) (hXU2 : Q ^ (1 / 25 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 528))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (87 / 70 : ℝ))
    (hfe : 4 * Real.exp 1 * C₁ * (4 * Cdiv (ε / 88) ^ 4) ^ 22 ≤ Q ^ ε) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ 5 * (2 * Real.exp 1 * (4 * Cdiv (ε / 88) ^ 4) ^ 22) * Q ^ ((87 / 35 + 55 * ε) * (1 - σ)) +
        27 * (4 * KG) ^ 4 * C₄ * Q ^ ((87 / 35 + 55 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset (DirichletCharacter ℂ q), Z = univ.filter fun χ : DirichletCharacter ℂ q =>
      χ ≠ 1 ∧ ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := ⟨_, rfl⟩
  rw [← hZ]
  -- one zero of each counted character (round 524's `count_nontrivial_ingham`)
  have hch : ∀ χ ∈ Z, ∃ s : ℂ, χ ≠ 1 ∧ σ ≤ s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
    intro χ hχ
    rw [hZ] at hχ
    obtain ⟨hχ1, s, hs1, hs2, hs3⟩ := (mem_filter.1 hχ).2
    refine ⟨s, hχ1, hs1, ?_, hs2, hs3⟩
    by_contra hge
    push Not at hge
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hge hs3
  choose! s0 hs0 using hch
  have hz0 : ∀ χ ∈ Z, LFunction χ (((s0 χ).re : ℂ) + (s0 χ).im * I) = 0 := fun χ hχ => by
    rw [Complex.re_add_im]; exact (hs0 χ hχ).2.2.2.2
  have hdich : ∀ χ ∈ Z, 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖
      ∨ 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := by
    intro χ hχ
    obtain ⟨hχ1, h1, h2, _, _⟩ := hs0 χ hχ
    exact dichotomy hχ1 hX hN hY8 hM (by linarith) h2 (hz0 χ hχ)
  obtain ⟨Z1, hZ1⟩ : ∃ Z1 : Finset (DirichletCharacter ℂ q),
      Z1 = Z.filter fun χ => 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖ := ⟨_, rfl⟩
  obtain ⟨Z2, hZ2⟩ : ∃ Z2 : Finset (DirichletCharacter ℂ q),
      Z2 = Z.filter fun χ => 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := ⟨_, rfl⟩
  have hcover : Z ⊆ Z1 ∪ Z2 := by
    intro χ hχ
    rcases hdich χ hχ with h | h
    · exact mem_union_left _ (hZ1 ▸ mem_filter.2 ⟨hχ, h⟩)
    · exact mem_union_right _ (hZ2 ▸ mem_filter.2 ⟨hχ, h⟩)
  have hm1 : ∀ χ ∈ Z1, χ ∈ Z ∧ 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖ := fun χ hχ => by
    rw [hZ1] at hχ; exact mem_filter.1 hχ
  have hm2 : ∀ χ ∈ Z2, χ ∈ Z ∧ 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := fun χ hχ => by
    rw [hZ2] at hχ; exact mem_filter.1 hχ
  have hc1 := class1_huxley hε hε1 hC₁0 hC₁ hσ hσ1 hT hQ1 hqT2 hX hN hXU2 hK hXN hfe
    (by linarith : (0 : ℝ) < Y) Z1 (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => ⟨(hs0 χ (hm1 χ hχ).1).2.1, (hs0 χ (hm1 χ hχ).1).2.2.1⟩)
    (fun χ hχ => (hs0 χ (hm1 χ hχ).1).2.2.2.1)
    (fun χ hχ => (hm1 χ hχ).2)
  have hc2 := class2_count_small hε.le (by linarith) hC₄0 h4 hX (δ := 1 / 4) (by norm_num)
    (by linarith : 1 / 2 + 1 / 4 ≤ σ) hT (by linarith : (1 : ℝ) ≤ Y) Z2
    (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => by
      obtain ⟨hχ1, h1, h2, h3, _⟩ := hs0 χ (hm2 χ hχ).1
      exact ⟨hχ1, h1, h2, h3, hz0 χ (hm2 χ hχ).1, (hm2 χ hχ).2⟩)
  have hb2 := class2_bound_huxley (q := q) hε hε1 hC₄0 hσ1 hQ1.le hT hqT (X := X) hXU
  rw [hYQ] at hc2
  -- the two counts as powers of `Q`
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (87 / 35 + 55 * ε) * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℝ, B₁ = 2 * Real.exp 1 * (4 * Cdiv (ε / 88) ^ 4) ^ 22 := ⟨_, rfl⟩
  rw [← hB₁] at hc1 ⊢
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  have hK' : 20 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 5 * Q ^ (ε / 528) := by linarith
  have hE1 : Q ^ (ε / 528) * Q ^ ((87 / 35 + 54 * ε) * (1 - σ)) ≤ Q ^ E := by
    rw [← Real.rpow_add hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1.le (by rw [hE]; nlinarith)
  have hE2 : Q ^ (87 / 35 * (1 - σ)) ≤ Q ^ E :=
    Real.rpow_le_rpow_of_exponent_le hQ1.le (by rw [hE]; nlinarith)
  have hP0 : 0 ≤ Q ^ ((87 / 35 + 54 * ε) * (1 - σ)) := by positivity
  have hI : (Z1.card : ℝ) ≤ 5 * B₁ * Q ^ E := by
    calc (Z1.card : ℝ) ≤ 20 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * (B₁ * Q ^ ((87 / 35 + 54 * ε) * (1 - σ))) := hc1
      _ ≤ 5 * Q ^ (ε / 528) * (B₁ * Q ^ ((87 / 35 + 54 * ε) * (1 - σ))) := by gcongr
      _ = 5 * B₁ * (Q ^ (ε / 528) * Q ^ ((87 / 35 + 54 * ε) * (1 - σ))) := by ring
      _ ≤ 5 * B₁ * Q ^ E := by gcongr
  have hII : (Z2.card : ℝ) ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ E := by
    calc (Z2.card : ℝ) ≤ _ := hc2
      _ ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ (87 / 35 * (1 - σ)) := hb2
      _ ≤ 27 * (4 * KG) ^ 4 * C₄ * Q ^ E := by gcongr
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card := by exact_mod_cast card_union_le Z1 Z2
    _ ≤ 5 * B₁ * Q ^ E + 27 * (4 * KG) ^ 4 * C₄ * Q ^ E := add_le_add hI hII

omit [NeZero q] in
/-- `Y = Q^{3/5}` at `U = Q^{1/25}`, `c = 7`. -/
lemma Yw_seven {Q : ℝ} (hQ0 : 0 < Q) : Yw 7 (Q ^ (1 / 25 : ℝ)) = Q ^ (3 / 5 : ℝ) := by
  unfold Yw; rw [← Real.rpow_mul hQ0.le]; norm_num

open scoped Classical in
/-- **The range `23/29 ≤ σ ≤ 11/12`.** For every `0 < ε ≤ 1/200` there is `C ≥ 0` such that for every `q ≥ 1`,
`23/29 ≤ σ ≤ 11/12` and `T ≥ 2` at most `C Q^{(87/35+55ε)(1−σ)}`, `Q = q(T + 6)`, characters `χ ≠ 1` mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. For `Q ≥ Q₀` (`eventually_huxley`), `count_huxley_at` at `X = ⌊Q^{1/25}⌋`,
`Y = Q^{3/5}`, `N = ⌊22Y log Y/X⌋ + 1` (round 518's `Xw`, `Yw`, `Nw` at `U = Q^{1/25}`, `c = 7`); below `Q₀` at most
`q ≤ Q₀` characters are counted. -/
theorem count_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 23 / 29 ≤ σ → σ ≤ 11 / 12 → 2 ≤ T →
      ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ C * ((q : ℝ) * (T + 6)) ^ ((87 / 35 + 55 * ε) * (1 - σ)) := by
  obtain ⟨C₄', hC₄'⟩ := LinnikFourth.fourth_moment hε (by linarith : ε ≤ 1)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = max C₄' 0 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := hC₄ ▸ le_max_right _ _
  have h4all : ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) →
      ∀ T' : ℝ, 0 ≤ T' → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε) := by
    intro q _ R hR T' hT' t ht
    refine (hC₄' q R hR T' hT' t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₄ ▸ le_max_left _ _) (by positivity)
  obtain ⟨C₁, hC₁pos, hC₁⟩ := norm_offK_le (δ := ε) (ε' := ε) hε (by linarith) hε (by linarith)
  obtain ⟨Q₀, hQ₀⟩ :=
    eventually_atTop.1 (eventually_huxley hε (4 * Real.exp 1 * C₁ * (4 * Cdiv (ε / 88) ^ 4) ^ 22))
  have hKG := KG_pos
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℝ, B₁ = 2 * Real.exp 1 * (4 * Cdiv (ε / 88) ^ 4) ^ 22 := ⟨_, rfl⟩
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  refine ⟨max Q₀ 0 + 5 * B₁ + 27 * (4 * KG) ^ 4 * C₄, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) * (T + 6) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ8 : 8 ≤ Q := by
    rw [hQ]
    calc (8 : ℝ) = 1 * 8 := by norm_num
      _ ≤ (q : ℝ) * (T + 6) := mul_le_mul hq1 (by linarith) (by norm_num) (by positivity)
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (87 / 35 + 55 * ε) * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (by positivity) (by linarith)
  have hQE : 1 ≤ Q ^ E := Real.one_le_rpow hQ1 hE0
  have hS0 : 0 ≤ (5 * B₁ + 27 * (4 * KG) ^ 4 * C₄) * Q ^ E := by positivity
  rcases lt_or_ge Q Q₀ with hsmall | hlarge
  · -- below `Q₀`: at most `q ≤ Q < Q₀` characters
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ max Q₀ 0 := hsmall.le.trans (le_max_left _ _)
      _ ≤ max Q₀ 0 * Q ^ E := le_mul_of_one_le_right (le_max_right _ _) hQE
      _ ≤ (max Q₀ 0 + 5 * B₁ + 27 * (4 * KG) ^ 4 * C₄) * Q ^ E := by linarith
  obtain ⟨hQa, hQb, hQc, hQd, hQe⟩ := hQ₀ Q hlarge
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Q ^ (1 / 25 : ℝ) := ⟨_, rfl⟩
  have hU8 : 8 ≤ U := by
    rw [hU]
    calc (8 : ℝ) = ((8 : ℝ) ^ 25) ^ (1 / 25 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ Q ^ (1 / 25 : ℝ) := Real.rpow_le_rpow (by positivity) hQa (by norm_num)
  have hYQ : Yw 7 U = Q ^ (3 / 5 : ℝ) := by rw [hU]; exact Yw_seven hQ0
  have hX : 1 ≤ Xw U := Xw_one hU8
  have hN : 1 ≤ Nw 7 U := Nw_one
  have hY8 : 8 ≤ Yw 7 U := le_trans hU8 (Yw_ge (by norm_num) hU8)
  have hM : 22 * Yw 7 U * Real.log (Yw 7 U) ≤ ((Xw U * Nw 7 U : ℕ) : ℝ) := XN_ge hU8
  have hXNle : ((Xw U * Nw 7 U : ℕ) : ℝ) ≤ 23 * Yw 7 U * Real.log (Yw 7 U) := XN_le (by norm_num) hU8
  have hXU : (Xw U : ℝ) ≤ Q ^ (1 / 25 : ℝ) := hU ▸ Xw_le hU8
  have hXU2 : Q ^ (1 / 25 : ℝ) ≤ 2 * (Xw U : ℝ) := by have := Xw_half hU8; rw [← hU]; linarith
  have hXr : (1 : ℝ) ≤ Xw U := by exact_mod_cast hX
  have hNQ : (Nw 7 U : ℝ) ≤ Q := by
    have h1 : (Nw 7 U : ℝ) ≤ ((Xw U * Nw 7 U : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    rw [hYQ] at hXNle
    linarith
  have hK : 4 * ((Nat.log 2 (Nw 7 U) + 1 : ℕ) : ℝ) ≤ Q ^ (ε / 528) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNQ) (by norm_num)).trans hQb
  have hXN : (2 * ((Xw U * Nw 7 U : ℕ) : ℝ)) ^ 2 ≤ Q ^ (87 / 70 : ℝ) := by
    refine le_trans ?_ hQc
    rw [← hYQ]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hqT : (q : ℝ) * (T + 2) ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hqT2 : (q : ℝ) * (2 * T + 2) ≤ 2 * Q := by
    have : (q : ℝ) * (2 * T + 2) ≤ (q : ℝ) * (2 * T + 12) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hQ]; linarith
  have hcount := count_huxley_at (q := q) (σ := σ) (T := T) (Q := Q) hε hε1 hC₁pos.le (hC₁ q) hC₄0 (h4all q)
    hσ hσ1 (by linarith) (by linarith) hqT hqT2 hX hN hY8 hM hYQ hXU hXU2 hK hXN hQe
  rw [← hE, ← hB₁] at hcount
  calc _ ≤ 5 * B₁ * Q ^ E + 27 * (4 * KG) ^ 4 * C₄ * Q ^ E := hcount
    _ ≤ (max Q₀ 0 + 5 * B₁ + 27 * (4 * KG) ^ 4 * C₄) * Q ^ E := by
        have : 0 ≤ max Q₀ 0 * Q ^ E := by positivity
        linarith

/-! ### Ingham's method at `c = 17/140` below `σ = 23/29` -/

omit [NeZero q] in
/-- **The integral class at `X = ⌊Q⌋`, `Y = Q^{87/70}`, `λ = Q^{(29/70)(½−σ)+ε/3}`**, for `σ ≤ 23/29` and
`q(T + 2) ≤ Q`: at most `(3200 KG/δ₀ + (KG/δ₀)²C₄)(log Q)¹⁰ Q^{(87/35+4ε)(1−σ)}`, `δ₀ = 17/174` (round 524's
`bound_class2_ingham` at `c = 17/140`). Both terms carry `Q^{(58/35)(½−σ)+1+ε/3}`, and
`(58/35)(½ − σ) + 1 ≤ (87/35)(1 − σ)` exactly when `σ ≤ 23/29`. -/
theorem bound_class2_c17 {ε C₄ σ T Q : ℝ} (hε0 : 0 ≤ ε) (hC₄ : 0 ≤ C₄) (hσ1 : σ ≤ 23 / 29) (hQ : 8 ≤ Q)
    (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) :
    2 * (KG * (Yw (17 / 140) Q) ^ (1 / 2 - σ) / (17 / 174)) * Q ^ (29 / 70 * (1 / 2 - σ) + ε / 3) *
        (MV (Xw Q) * ((q : ℝ) * (T + 1) + (Xw Q))) +
      (KG * (Yw (17 / 140) Q) ^ (1 / 2 - σ) / (17 / 174)) ^ 2 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε)) /
        (Q ^ (29 / 70 * (1 / 2 - σ) + ε / 3)) ^ 2
      ≤ (3200 * (KG / (17 / 174)) + (KG / (17 / 174)) ^ 2 * C₄) * Real.log Q ^ 10 *
        Q ^ ((87 / 35 + 4 * ε) * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hKG := KG_pos
  set K := KG / (17 / 174) with hK
  have hK0 : 0 < K := by positivity
  set a := 87 / 70 * (1 / 2 - σ) with ha
  set e := 29 / 70 * (1 / 2 - σ) + ε / 3 with he
  set E₂ := 58 / 35 * (1 / 2 - σ) + 1 + ε / 3 with hE₂
  set E := (87 / 35 + 4 * ε) * (1 - σ) with hE
  have hY : (Yw (17 / 140) Q) ^ (1 / 2 - σ) = Q ^ a := by
    unfold Yw; rw [← Real.rpow_mul hQ0.le]; congr 1; rw [ha]; ring
  have hA : KG * (Yw (17 / 140) Q) ^ (1 / 2 - σ) / (17 / 174) = K * Q ^ a := by rw [hY, hK]; ring
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
/-- **The range `52/87 ≤ σ ≤ 23/29` at `Q = q(T + 6)`**: at most `Mc(log Q)¹⁰Q^{(87/35+4ε)(1−σ)}` characters `χ ≠ 1`
have a zero in `Re s ≥ σ`, `|Im s| ≤ T`, with `Mc = 16·13³·96·9⁶·71 + 3200 KG/δ₀ + (KG/δ₀)²C₄`, `δ₀ = 17/174`: round
524's `count_nontrivial_ingham` at `c = 17/140` (so `Y = Q^{87/70}` and round 521's polynomial class carries
`Q^{(2+4c)(1−σ)} = Q^{(87/35)(1−σ)}`, `bound_class1`) and `λ = Q^{(29/70)(½−σ)+ε/3}` (`bound_class2_c17`). -/
theorem count_middle_c17 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε))
    {σ T : ℝ} (hmid : 52 / 87 ≤ σ) (hle : σ ≤ 23 / 29) (hT : 2 ≤ T) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (17 / 174)) + (KG / (17 / 174)) ^ 2 * C₄)) *
        Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((87 / 35 + 4 * ε) * (1 - σ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ0 : 0 < (q : ℝ) * (T + 6) := by linarith
  have hQ1 : 1 ≤ (q : ℝ) * (T + 6) := by linarith
  have hlam0 : 0 < ((q : ℝ) * (T + 6)) ^ (29 / 70 * (1 / 2 - σ) + ε / 3) := Real.rpow_pos_of_pos hQ0 _
  have hcount := count_nontrivial_ingham hε.le hε1 hC₄0 h4 (c := 17 / 140) (by norm_num)
    (by norm_num : (0 : ℝ) < 17 / 174) (by linarith : 1 / 2 + 17 / 174 ≤ σ) (by linarith) hT
    (le_refl ((q : ℝ) * (T + 6))) hlam0
  have hb1 := bound_class1 (c := 17 / 140) (σ := σ) (by norm_num) (by norm_num) (by linarith) (by linarith) hQ8
  have hb2 := bound_class2_c17 (q := q) hε.le hC₄0 hle hQ8 (by linarith)
    (by nlinarith : (q : ℝ) * (T + 2) ≤ (q : ℝ) * (T + 6))
  have hE1' : ((q : ℝ) * (T + 6)) ^ ((2 + 4 * (17 / 140 : ℝ)) * (1 - σ)) ≤
      ((q : ℝ) * (T + 6)) ^ ((87 / 35 + 4 * ε) * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)
  have hL10 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by
    have := log_ge_two hQ8; positivity
  have hc : (0 : ℝ) ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 := by norm_num
  refine hcount.trans ((add_le_add hb1 hb2).trans ?_)
  have h1 : 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((2 + 4 * (17 / 140 : ℝ)) * (1 - σ)) ≤
      16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * Real.log ((q : ℝ) * (T + 6)) ^ 10 *
      ((q : ℝ) * (T + 6)) ^ ((87 / 35 + 4 * ε) * (1 - σ)) :=
    mul_le_mul_of_nonneg_left hE1' (mul_nonneg hc hL10)
  linarith

/-! ### Density over the characters -/

/-- The constant of `charDensity_huxley`. -/
def CDH (C₄ CH : ℝ) : ℝ :=
  2 ^ 10 + 256 * 3 ^ 10 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (17 / 174)) + (KG / (17 / 174)) ^ 2 * C₄))
    + 256 * 2 ^ 10 * CH

open scoped Classical in
/-- **A density estimate over the characters mod `q` with exponent `87/35`**: for every `0 < ε ≤ 1/200` there is
`C ≥ 0` with `CharDensity (87/35 + 55ε) 10 C`. Below `σ = 52/87`, where `(87/35)(1 − σ) ≥ 1`, at most `q ≤ qT`
characters are counted; between `52/87` and `23/29`, Ingham's method at `c = 17/140` (`count_middle_c17`); between
`23/29` and `11/12`, the power trick and the Halász–Montgomery inequality with the off-diagonal on `Re s = 1/12 − ε`
(`count_huxley`); above `11/12` no character `χ ≠ 1` has a zero (`LinnikLindelof.LFunction_ne_zero`). Both counted
ranges are measured at `Q = q(T + 6) ≤ 4qT`. -/
theorem charDensity_huxley {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ C : ℝ, 0 ≤ C ∧ CharDensity (87 / 35 + 55 * ε) 10 C := by
  obtain ⟨C₄', hC₄'⟩ := LinnikFourth.fourth_moment hε (by linarith : ε ≤ 1)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = max C₄' 0 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := hC₄ ▸ le_max_right _ _
  have h4all : ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) →
      ∀ T' : ℝ, 0 ≤ T' → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + ε) := by
    intro q _ R hR T' hT' t ht
    refine (hC₄' q R hR T' hT' t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₄ ▸ le_max_left _ _) (by positivity)
  obtain ⟨CH, hCH0, hCH⟩ := count_huxley hε hε1
  have hKG := KG_pos
  have hCDH0 : 0 ≤ CDH C₄ CH := by unfold CDH; positivity
  refine ⟨CDH C₄ CH, hCDH0, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((q : ℝ) * T) := ⟨_, rfl⟩
  rw [← hℓdef]
  have hℓ : 1 / 2 ≤ ℓ := hℓdef ▸ half_le_log hqT
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (87 / 35 + 55 * ε) * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg (by positivity) (by linarith)
  have hE4 : E ≤ 4 := by rw [hE]; nlinarith
  have hpowE : 0 ≤ ((q : ℝ) * T) ^ E := by positivity
  have hpowE1 : 1 ≤ ((q : ℝ) * T) ^ E := Real.one_le_rpow (by linarith) hE0
  have e10 : ℓ ^ (10 : ℝ) = ℓ ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e10]
  have h2ℓ : 1 ≤ 2 ^ 10 * ℓ ^ 10 := by
    have h1 : 1 ≤ (2 * ℓ) ^ 10 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) ≤ (2 * ℓ) ^ 10 := h1
      _ = 2 ^ 10 * ℓ ^ 10 := by ring
  have hℓ10 : 0 ≤ ℓ ^ 10 := by positivity
  obtain ⟨Mc, hMc⟩ : ∃ x : ℝ, x = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 + (3200 * (KG / (17 / 174)) + (KG / (17 / 174)) ^ 2 * C₄) :=
    ⟨_, rfl⟩
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hCDHe : CDH C₄ CH = 2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CH := by rw [hMc]; rfl
  rw [hCDHe]
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
  have h1 : 1 ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := one_le_mul_of_one_le_of_one_le hpowE1 h2ℓ
  have hrest : 0 ≤ (256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CH) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by positivity
  rcases lt_or_ge σ (52 / 87) with hsmall | hmid
  · -- below `52/87`: at most `q ≤ qT ≤ (qT)^E` characters
    have hE1 : 1 ≤ E := by rw [hE]; nlinarith
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ (q : ℝ) * T := by nlinarith
      _ = ((q : ℝ) * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((q : ℝ) * T) ^ E := Real.rpow_le_rpow_of_exponent_le (by linarith) hE1
      _ ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := le_mul_of_one_le_right hpowE h2ℓ
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CH) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith
  rcases lt_or_ge (11 / 12) σ with hbig | hle
  · -- above `11/12`: no character `χ ≠ 1` has a zero
    have hZ : (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro χ - ⟨hχ1, s, hs, -, hz⟩
      exact LinnikLindelof.LFunction_ne_zero hχ1 (by linarith) hz
    rw [hZ, card_empty, Nat.cast_zero, zero_add] at hF
    calc _ ≤ (1 : ℝ) := hF
      _ ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := h1
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CH) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith
  -- `Q = q(T + 6) ≤ 4qT`
  have hQ8 : 8 ≤ (q : ℝ) * (T + 6) := by nlinarith
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 256 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by linarith) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (4 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 256 * ((q : ℝ) * T) ^ E := by norm_num
  have hQE0 : 0 ≤ ((q : ℝ) * (T + 6)) ^ E := by positivity
  rcases lt_or_ge σ (23 / 29) with hlow | hhux
  · -- between `52/87` and `23/29`: Ingham's method at `c = 17/140`
    have hZ := count_middle_c17 hε (by linarith) hC₄0 (h4all q) hmid hlow.le hT
    rw [← hMc] at hZ
    have hL0 : 2 ≤ Real.log ((q : ℝ) * (T + 6)) := log_ge_two hQ8
    have hLQ : Real.log ((q : ℝ) * (T + 6)) ≤ 3 * ℓ := by
      have h2 : Real.log ((q : ℝ) * (T + 6)) ≤ Real.log (4 * ((q : ℝ) * T)) := Real.log_le_log (by linarith) hQ4
      rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < q * T).ne'] at h2
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have h5 : Real.log 2 ≤ ℓ := hℓdef ▸ Real.log_le_log (by norm_num) hqT
      rw [← hℓdef] at h2
      linarith
    have hL10 : Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ 3 ^ 10 * ℓ ^ 10 := by
      calc Real.log ((q : ℝ) * (T + 6)) ^ 10 ≤ (3 * ℓ) ^ 10 := by gcongr
        _ = 3 ^ 10 * ℓ ^ 10 := by ring
    have hQE' : ((q : ℝ) * (T + 6)) ^ ((87 / 35 + 4 * ε) * (1 - σ)) ≤ ((q : ℝ) * (T + 6)) ^ E :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hE]; nlinarith)
    have hlog0 : 0 ≤ Real.log ((q : ℝ) * (T + 6)) ^ 10 := by positivity
    have hstep : Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((87 / 35 + 4 * ε) * (1 - σ)) ≤
        Mc * (3 ^ 10 * ℓ ^ 10) * (256 * ((q : ℝ) * T) ^ E) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL10 hMc0) (hQE'.trans hQE) (by positivity) (by positivity)
    have hCH : 0 ≤ 256 * 2 ^ 10 * CH * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by positivity
    calc _ ≤ _ := hF
      _ ≤ Mc * Real.log ((q : ℝ) * (T + 6)) ^ 10 * ((q : ℝ) * (T + 6)) ^ ((87 / 35 + 4 * ε) * (1 - σ)) +
            ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
      _ ≤ Mc * (3 ^ 10 * ℓ ^ 10) * (256 * ((q : ℝ) * T) ^ E) + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := by
          linarith
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CH) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith
  · -- between `23/29` and `11/12`: the power trick and the Halász–Montgomery inequality
    have hZ := hCH q σ T hhux hle hT
    rw [← hE] at hZ
    have hstep : CH * ((q : ℝ) * (T + 6)) ^ E ≤ 256 * 2 ^ 10 * CH * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by
      calc CH * ((q : ℝ) * (T + 6)) ^ E ≤ CH * (256 * ((q : ℝ) * T) ^ E) := by gcongr
        _ = 256 * CH * ((q : ℝ) * T) ^ E * 1 := by ring
        _ ≤ 256 * CH * ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) :=
            mul_le_mul_of_nonneg_left h2ℓ (by positivity)
        _ = 256 * 2 ^ 10 * CH * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
    have hM : 0 ≤ 256 * 3 ^ 10 * Mc * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by positivity
    calc _ ≤ _ := hF
      _ ≤ CH * ((q : ℝ) * (T + 6)) ^ E + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
      _ ≤ (2 ^ 10 + 256 * 3 ^ 10 * Mc + 256 * 2 ^ 10 * CH) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith

/-! ### Linnik's exponent `87/35 + η` -/

/-- **Linnik's theorem with exponent `87/35 + η`, with no hypothesis.** For every `η > 0` there is `K` such that for
every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{87/35 + η}`: round 520's
`linnik_of_charDensity` fed `charDensity_huxley` at `ε = min(η, 1)/220`. -/
theorem linnik_eighty_seven_thirty_fifths {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (87 / 35 + η) := by
  have hmin : 0 < min η 1 := lt_min hη one_pos
  have hε0 : 0 < min η 1 / 220 := by positivity
  have hε1 : min η 1 / 220 ≤ 1 / 200 := by have := min_le_right η 1; linarith
  obtain ⟨C, hC0, hD⟩ := charDensity_huxley hε0 hε1
  obtain ⟨K, hK⟩ := linnik_of_charDensity (by nlinarith : (2 : ℝ) ≤ 87 / 35 + 55 * (min η 1 / 220))
    (by norm_num) hC0 hD (half_pos hη)
  refine ⟨max K 0, fun q _ a ha => ?_⟩
  obtain ⟨p, hp, hpa, hpK⟩ := hK q a ha
  refine ⟨p, hp, hpa, hpK.trans ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hexp : 87 / 35 + 55 * (min η 1 / 220) + η / 2 ≤ 87 / 35 + η := by
    have := min_le_left η 1; linarith
  calc K * (q : ℝ) ^ (87 / 35 + 55 * (min η 1 / 220) + η / 2)
      ≤ max K 0 * (q : ℝ) ^ (87 / 35 + 55 * (min η 1 / 220) + η / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * (q : ℝ) ^ (87 / 35 + η) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hexp) (le_max_right _ _)

end LinnikHuxley

#print axioms LinnikHuxley.power_count
#print axioms LinnikHuxley.class2_count_small
#print axioms LinnikHuxley.block_bin_count
#print axioms LinnikHuxley.class1_huxley
#print axioms LinnikHuxley.count_huxley
#print axioms LinnikHuxley.count_middle_c17
#print axioms LinnikHuxley.charDensity_huxley
#print axioms LinnikHuxley.linnik_eighty_seven_thirty_fifths
