/-
# Round 657: their Proposition 7.2 (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

This file assembles Chen–Gupta–Li's Proposition 7.2 from rounds 650, 655 and 656.

Their statement. "There is a choice of 0 < M₁ ≤ M₃ ≤ M₂ ≤ (qT)^ϵqT/N such that
S₃ ⪅_ϵ (N²/(q²M₂)) Σ_{|m_i|∼M_i, 1≤i≤3} Ĩ_{m⃗} + |W|, where Ĩ_{m⃗} := ∫_{v₁∈[1/2,2]} Σ_{b₁,b₂ mod q, (b₁b₂,q)=1}
|R(v₁,b₁) R̃_{M₂}((m₁v₁+m₃)/(m₂v₁), b₁⁻¹b₂) R̃_{M₂}((m₁v₁+m₃)/m₂, b₂)| · (b₁m₁−b₂m₂+m₃,q) dv₁" (text layer lines
2264–2290; spaces restored, the tildes, arrows, integral, sums and their ranges, large parentheses, fractions,
exponents and subscripts transcribed). The text layer drops the large bars; the PDF draws them as CMEX10 glyphs,
which pdfminer finds on page 25 at x = 219.7–223.7, just before the characters `R(v₁,b₁)`, and at x = 506.2–510.2,
just after the second `R̃`'s closing parenthesis, in the rows y = 584–606. Since `R̃ ≥ 0`, the integrand is
`|R(v₁,b₁)|R̃R̃(b₁m₁−b₂m₂+m₃, q)`, which is `Itg`; `It` is their `Ĩ` with `X` for their `(qT)^ϵ`.

Their proof. "Furthermore, by selecting dyadic scales to maximize the right-hand side, we arrive at (7.6)
|S₃| ⪅_ϵ Σ_{|m_i|∼M_i, 1≤i≤3} |I′_{m⃗}| + |W|, where M₁ ≤ M₃ ≤ M₂ ≤ (qT)^ϵqT/N" (lines 2342–2347, with the same
allowances), and, after the Cauchy–Schwarz step of round 656, "Since we are summing over m₂ with |m₂| ∼ M₂, we can
replace −m₂ with m₂ without altering the overall sum. Inserting this in (7.6) then gives the result." (lines
2429–2430; spaces restored, the subscripts transcribed).

The stack's form. `prop72` keeps every term explicit and differs from their statement in three ways.
* It sums over every dyadic scale `2^k ≤ |m₂| < 2^{k+1}`, `k ≤ log₂M`, instead of choosing the largest. Their
  `⪅` is defined by "we write A⪅B to indicate that for any ϵ > 0, there exists a constant C(ϵ) > 0, depending only on
  ϵ, such that A ≤ C(ϵ)(qT)^ϵB for all sufficiently large qT" (lines 279–281; spaces restored, the exponent
  transcribed), so the number of scales, `⌊log₂M⌋ + 1`, is `⪅ 1` for `M ≤ (qT)²`. Their `A ∼ B` "signifies the
  stronger condition B < A ≤ 2B" (lines 278–279, spaces restored); the stack's blocks give `M₂ = 2^k ≤ |m₂|`, which
  is what `Ip_le_It` needs.
* It splits only `m₂` dyadically and keeps `|m₁|, |m₃| ≤ |m₂|`, from the cyclic symmetry (round 655); their
  `M₁ ≤ M₃` is not used.
* Its constant `2C_J(0)d(q)` and its three errors are explicit: round 654's error at each triple, `3(2M)³E`; their
  `Z′`, which round 649 read as the diagonal terms, `|R||μ − μ₀|³` (it bounds `|μ − μ₀|` by `d(q)B_w`); and round
  650's truncation error.

Plain statements, with `L = NM₂/q`, `X > 0`, `q ≥ 1` and `B = {m : 0 < |m| ≤ M}`.
* `measurable_Rt`, `Rt_le`: `R̃_{M₂}(·, a)` is measurable, and `R̃_{M₂}(u, a) ≤ √((3/2)L)|R|` for `L ≥ 0`.
* `Ip_le_It`: for `N > 0`, `|m₂| ≥ M₂ > 0` and any `K`,
  `|I′(m⃗)| ≤ 2C_J(0)d(q)(N²/(q²M₂))Ĩ_{M₂}(m₁, −m₂, m₃) + E(K)`, with `E(K) = (N/q)³(9/4)C_J(K)(2πX)^{−K}φ(q)³|R|³`
  (`E71`). This is `prop71r` (round 655) with the inner integral bounded by `Vr_inner_le` (round 656) and the outer
  one integrated over `v₁ ∈ [1/2, 2]`.
* `prop72`: for `N > 0`, `χ` injective on `R`, points `|t_i| ≤ T`, `M ≥ 1`, `K ≥ 2` and any `K′`,
  `S₃ ≤ 3Σ_{k=0}^{⌊log₂M⌋}Σ_{m⃗∈B³, ⌊log₂|m₂|⌋=k, |m₁|,|m₃|≤|m₂|}2C_J(0)d(q)(N²/(q²2^k))Ĩ_{2^k}(m⃗)
  + 3(2M)³E(K′) + |R||μ − μ₀|³ + 3|R|³τ_M(2N + 1 + τ_M)²`, with round 650's `τ_M`.

* `measurable_Rt`, `Rt_le`: `R̃` in its centre.
* `Itg`, `It`, `Itg_nonneg`, `It_nonneg`, `integrableOn_Itg`, `Itg_neg`: their `Ĩ`, and `Ĩ` at `−m₂` as round 656's
  sum.
* `Ip_le_It`: their bound for `|I′(m⃗)|`.
* `mem_boxM`, `card_boxM`, `two_pow_log_le`, `sum_dyadic`, `sum_neg_m₂`: the dyadic regrouping and `m₂ ↦ −m₂`.
* `Ak`, `E71`, `sum_Ak_regroup`, `prop72`: their Proposition 7.2.

The next step is their §11: Cauchy–Schwarz in `(v₁, b₁)`, then their Proposition 8.1 as a displayed hypothesis.

The file imports `LinnikCGLRt.lean`.
-/

import LinnikCGLRt

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLP72

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag
  LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt

/-! ### `R̃` in its centre -/

/-- `R̃_{M₂}(·, a)` is measurable. -/
lemma measurable_Rt {ι : Type*} {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ : ℝ) (a : ZMod q) : Measurable fun u => Rt N R χ t X M₂ u a := by
  have hF : StronglyMeasurable fun p : ℝ × ℝ =>
      N * M₂ / q * psi0 (N * M₂ / q * (p.1 - p.2) / (2 * X)) * ‖Rf R χ t p.2 a‖ ^ 2 :=
    ((measurable_const.mul (continuous_psi0.measurable.comp (by fun_prop))).mul
      (((measurable_Rf R χ t a).comp measurable_snd).norm.pow_const 2)).stronglyMeasurable
  exact (hF.integral_prod_right' (ν := volume.restrict (Icc (1 / 2 : ℝ) 2))).measurable.sqrt

/-- `R̃_{M₂}(u, a) ≤ √((3/2)L)|R|` for `L = NM₂/q ≥ 0`. -/
lemma Rt_le {ι : Type*} {q : ℕ} {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    {X M₂ : ℝ} (hL : 0 ≤ N * M₂ / q) (u : ℝ) (a : ZMod q) :
    Rt N R χ t X M₂ u a ≤ Real.sqrt (3 / 2 * (N * M₂ / q)) * R.card := by
  set L := N * M₂ / q with hLdef
  have hmR : Measurable fun u' : ℝ => ‖Rf R χ t u' a‖ ^ 2 := ((measurable_Rf R χ t a).norm).pow_const 2
  rw [show Real.sqrt (3 / 2 * L) * R.card = Real.sqrt (3 / 2 * L * (R.card : ℝ) ^ 2) by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 / 2 * L by positivity) ((R.card : ℝ) ^ 2), Real.sqrt_sq (Nat.cast_nonneg _)]]
  refine Real.sqrt_le_sqrt ?_
  calc ∫ u' in Icc (1 / 2 : ℝ) 2, L * psi0 (L * (u - u') / (2 * X)) * ‖Rf R χ t u' a‖ ^ 2
      ≤ ∫ _ in Icc (1 / 2 : ℝ) 2, L * (R.card : ℝ) ^ 2 := by
        refine setIntegral_mono_on ?_ (integrableOn_const (C := L * (R.card : ℝ) ^ 2) (by simp))
          measurableSet_Icc fun u' hu' => ?_
        · refine integrableOn_Icc_of_le ((measurable_const.mul (continuous_psi0.measurable.comp
            (by fun_prop))).mul hmR) (C := L * (R.card : ℝ) ^ 2) fun x hx => ?_
          have h0 := psi0_nonneg (L * (u - x) / (2 * X))
          rw [abs_of_nonneg (by positivity)]
          exact mul_le_mul (mul_le_of_le_one_right hL (psi0_le_one _))
            (pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hx.1]) a) 2) (by positivity) hL
        · exact mul_le_mul (mul_le_of_le_one_right hL (psi0_le_one _))
            (pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [hu'.1]) a) 2) (by positivity) hL
    _ = 3 / 2 * L * (R.card : ℝ) ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]; ring

/-! ### Their `Ĩ` -/

/-- The integrand of their `Ĩ_{m⃗}`:
`Σ_{b₁,b₂}|R(v₁, b₁)|R̃_{M₂}((m₁v₁ + m₃)/(m₂v₁), b₁⁻¹b₂)R̃_{M₂}((m₁v₁ + m₃)/m₂, b₂)(b₁m₁ − b₂m₂ + m₃, q)`. -/
def Itg {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ : ℝ) (m₁ m₂ m₃ : ℤ) : ℝ → ℝ := fun v₁ =>
  ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ,
    ‖Rf R χ t v₁ b₁‖ * Rt N R χ t X M₂ ((m₁ * v₁ + m₃) / (m₂ * v₁)) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q) *
      Rt N R χ t X M₂ ((m₁ * v₁ + m₃) / m₂) (b₂ : ZMod q) *
      (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) - (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ)

/-- **Their `Ĩ_{m⃗}`** (Proposition 7.2), with `X` for their `(qT)^ϵ`: the integral of `Itg` over `v₁ ∈ [1/2, 2]`. -/
def It {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X M₂ : ℝ) (m₁ m₂ m₃ : ℤ) : ℝ :=
  ∫ v₁ in Icc (1 / 2 : ℝ) 2, Itg N R χ t X M₂ m₁ m₂ m₃ v₁

lemma Itg_nonneg {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (X M₂ : ℝ) (m₁ m₂ m₃ : ℤ) (v₁ : ℝ) : 0 ≤ Itg N R χ t X M₂ m₁ m₂ m₃ v₁ := by
  unfold Itg
  refine Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ => ?_
  have := Rt_nonneg N R χ t X M₂ ((m₁ * v₁ + m₃) / (m₂ * v₁)) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q)
  have := Rt_nonneg N R χ t X M₂ ((m₁ * v₁ + m₃) / m₂) (b₂ : ZMod q)
  positivity

lemma It_nonneg {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (X M₂ : ℝ) (m₁ m₂ m₃ : ℤ) : 0 ≤ It N R χ t X M₂ m₁ m₂ m₃ :=
  setIntegral_nonneg measurableSet_Icc fun v₁ _ => Itg_nonneg N R χ t X M₂ m₁ m₂ m₃ v₁

/-- The integrand is integrable on `[1/2, 2]` for `NM₂/q ≥ 0`. -/
lemma integrableOn_Itg {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X M₂ : ℝ} (hL : 0 ≤ N * M₂ / q) (m₁ m₂ m₃ : ℤ) :
    IntegrableOn (Itg N R χ t X M₂ m₁ m₂ m₃) (Icc (1 / 2 : ℝ) 2) := by
  set B := Real.sqrt (3 / 2 * (N * M₂ / q)) * R.card with hB
  have hB0 : 0 ≤ B := by positivity
  unfold Itg
  refine integrable_finsetSum _ fun b₁ _ => integrable_finsetSum _ fun b₂ _ => ?_
  refine integrableOn_Icc_of_le ?_ (C := (R.card : ℝ) * B * B * q) fun v₁ hv₁ => ?_
  · exact ((((measurable_Rf R χ t _).norm).mul ((measurable_Rt N R χ t X M₂ _).comp (by fun_prop))).mul
      ((measurable_Rt N R χ t X M₂ _).comp (by fun_prop))).mul measurable_const
  · have h2 := Rt_nonneg N R χ t X M₂ ((m₁ * v₁ + m₃) / (m₂ * v₁)) ((b₁⁻¹ * b₂ : (ZMod q)ˣ) : ZMod q)
    have h3 := Rt_nonneg N R χ t X M₂ ((m₁ * v₁ + m₃) / m₂) (b₂ : ZMod q)
    rw [abs_of_nonneg (by positivity)]
    have hg : (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) - (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ) ≤
        q := by exact_mod_cast Nat.gcd_le_right _ (Nat.pos_of_ne_zero (NeZero.ne q))
    exact mul_le_mul (mul_le_mul (mul_le_mul (norm_Rf_le R χ t (by linarith [hv₁.1]) _) (Rt_le R χ t hL _ _) h2
      (Nat.cast_nonneg _)) (Rt_le R χ t hL _ _) h3 (by positivity)) hg (Nat.cast_nonneg _) (by positivity)

/-- `Ĩ` at `−m₂` is the sum in round 656's `Vr_inner_le`. -/
lemma Itg_neg {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (X M₂ : ℝ) (m₁ m₂ m₃ : ℤ) (v₁ : ℝ) :
    Itg N R χ t X M₂ m₁ (-m₂) m₃ v₁ = ∑ b₁ : (ZMod q)ˣ, ∑ b₂ : (ZMod q)ˣ,
      (Nat.gcd ((b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q)).val q : ℝ) *
        (‖Rf R χ t v₁ b₁‖ * (Rt N R χ t X M₂ (-(m₁ * v₁ + m₃) / m₂ / v₁) ((b₂ * b₁⁻¹ : (ZMod q)ˣ) : ZMod q) *
          Rt N R χ t X M₂ (-(m₁ * v₁ + m₃) / m₂) (b₂ : ZMod q))) := by
  unfold Itg
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  have e1 : ((m₁ : ℝ) * v₁ + m₃) / (((-m₂ : ℤ) : ℝ) * v₁) = -(m₁ * v₁ + m₃) / m₂ / v₁ := by push_cast; ring
  have e2 : ((m₁ : ℝ) * v₁ + m₃) / ((-m₂ : ℤ) : ℝ) = -(m₁ * v₁ + m₃) / m₂ := by push_cast; ring
  have e3 : (b₁⁻¹ * b₂ : (ZMod q)ˣ) = b₂ * b₁⁻¹ := mul_comm _ _
  have e4 : (b₁ : ZMod q) * (m₁ : ZMod q) - (b₂ : ZMod q) * ((-m₂ : ℤ) : ZMod q) + (m₃ : ZMod q) =
      (b₁ : ZMod q) * (m₁ : ZMod q) + (b₂ : ZMod q) * (m₂ : ZMod q) + (m₃ : ZMod q) := by push_cast; ring
  rw [e1, e2, e3, e4]
  ring

/-! ### Their Proposition 7.2 at one triple -/

/-- **Their bound for `|I′(m⃗)|`** (proof of Proposition 7.2): for `|m₂| ≥ M₂ > 0`,
`|I′(m⃗)| ≤ 2C_J(0)d(q)(N²/(q²M₂))Ĩ_{M₂}(m₁, −m₂, m₃) + (N/q)³(9/4)E`, with round 654's error
`E = C_J(K)(2πX)^{−K}φ(q)³|R|³`. -/
theorem Ip_le_It {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) {X M₂ : ℝ} (hX : 0 < X) (hM₂ : 0 < M₂)
    (hm₂ : M₂ ≤ |(m₂ : ℝ)|) (K : ℕ) :
    ‖Ip N R χ t m₁ m₂ m₃‖ ≤ 2 * CJ 0 * q.divisors.card * N ^ 2 / (q ^ 2 * M₂) * It N R χ t X M₂ m₁ (-m₂) m₃ +
      (N / q) ^ 3 * (9 / 4 * (CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3))) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set L := N * M₂ / q with hLdef
  have hL : 0 < L := by positivity
  have hc₀ : 0 ≤ CJ 0 * (q.divisors.card : ℝ) := mul_nonneg (CJ_nonneg 0) (Nat.cast_nonneg _)
  have hV0 : ∀ v₁ v₂, 0 ≤ Vr N R χ t m₁ m₂ m₃ X v₁ v₂ := fun v₁ v₂ => by
    unfold Vr; split_ifs
    · exact Wm_nonneg R χ t m₁ m₂ m₃ v₁ v₂
    · exact le_rfl
  have hint : ∫ v₁ in Icc (1 / 2 : ℝ) 2, ∫ v₂ in Icc (1 / 2 : ℝ) 2, Vr N R χ t m₁ m₂ m₃ X v₁ v₂ ≤
      2 / L * It N R χ t X M₂ m₁ (-m₂) m₃ := by
    unfold It
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v₁ =>
      setIntegral_nonneg measurableSet_Icc fun v₂ _ => hV0 v₁ v₂) ((integrableOn_Itg R χ t hL.le _ _ _).const_mul _)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v₁ hv₁ => ?_))
    have h := Vr_inner_le hN R χ t m₁ m₂ m₃ hX hM₂ hm₂ hv₁
    show ∫ v₂ in Icc (1 / 2 : ℝ) 2, Vr N R χ t m₁ m₂ m₃ X v₁ v₂ ≤ 2 / L * Itg N R χ t X M₂ m₁ (-m₂) m₃ v₁
    rw [Itg_neg]
    rw [div_mul_eq_mul_div, le_div_iff₀ hL, mul_comm]
    exact h
  have h71 := prop71r hN R χ t m₁ m₂ m₃ hX K
  set E := CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3) with hE
  calc ‖Ip N R χ t m₁ m₂ m₃‖
      ≤ (N / q) ^ 3 * (CJ 0 * q.divisors.card *
          (∫ v₁ in Icc (1 / 2 : ℝ) 2, ∫ v₂ in Icc (1 / 2 : ℝ) 2, Vr N R χ t m₁ m₂ m₃ X v₁ v₂) + 9 / 4 * E) := h71
    _ ≤ (N / q) ^ 3 * (CJ 0 * q.divisors.card * (2 / L * It N R χ t X M₂ m₁ (-m₂) m₃) + 9 / 4 * E) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hint hc₀) le_rfl) (by positivity)
    _ = 2 * CJ 0 * q.divisors.card * N ^ 2 / (q ^ 2 * M₂) * It N R χ t X M₂ m₁ (-m₂) m₃ +
          (N / q) ^ 3 * (9 / 4 * E) := by
        rw [hLdef]; field_simp

/-! ### The dyadic decomposition -/

lemma mem_boxM {M : ℕ} {m : ℤ} (h : m ∈ boxM M) : m ≠ 0 ∧ m.natAbs ≤ M := by
  unfold boxM at h
  obtain ⟨h0, h1⟩ := Finset.mem_erase.1 h
  obtain ⟨h2, h3⟩ := Finset.mem_Icc.1 h1
  exact ⟨h0, by omega⟩

lemma card_boxM (M : ℕ) : (boxM M).card = 2 * M := by
  unfold boxM
  rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]
  omega

/-- The dyadic scale `2^⌊log₂|m|⌋` of `m ≠ 0` is at most `|m|`. -/
lemma two_pow_log_le {m : ℤ} (hm : m ≠ 0) : (2 : ℝ) ^ Nat.log 2 m.natAbs ≤ |(m : ℝ)| := by
  have h := Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.2 hm)
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast h

/-- Regrouping a sum over `boxM M³` by the dyadic scale of `m₂`. -/
lemma sum_dyadic (M : ℕ) (g : ℕ → ℤ → ℤ → ℤ → ℝ) :
    ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, g (Nat.log 2 m₂.natAbs) m₁ m₂ m₃ =
      ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
        (if Nat.log 2 m₂.natAbs = k then g k m₁ m₂ m₃ else 0) := by
  have hk : ∀ m₂ ∈ boxM M, Nat.log 2 m₂.natAbs ∈ Finset.range (Nat.log 2 M + 1) := fun m₂ hm₂ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.log_mono_right (mem_boxM hm₂).2))
  calc ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, g (Nat.log 2 m₂.natAbs) m₁ m₂ m₃
      = ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, ∑ k ∈ Finset.range (Nat.log 2 M + 1),
          (if Nat.log 2 m₂.natAbs = k then g k m₁ m₂ m₃ else 0) := by
        refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ hm₂ =>
          Finset.sum_congr rfl fun m₃ _ => ?_
        rw [Finset.sum_ite_eq]
        simp [hk m₂ hm₂]
    _ = ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₃ ∈ boxM M,
          (if Nat.log 2 m₂.natAbs = k then g k m₁ m₂ m₃ else 0) :=
        Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => Finset.sum_comm
    _ = ∑ m₁ ∈ boxM M, ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
          (if Nat.log 2 m₂.natAbs = k then g k m₁ m₂ m₃ else 0) :=
        Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- `m₂ ↦ −m₂` inside a dyadic block: their "we can replace −m₂ with m₂ without altering the overall sum". -/
lemma sum_neg_m₂ (M : ℕ) (k : ℕ) (f : ℤ → ℤ → ℤ → ℝ) (m₁ m₃ : ℤ) :
    ∑ m₂ ∈ boxM M, (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then f m₁ (-m₂) m₃ else 0) =
      ∑ m₂ ∈ boxM M, (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then f m₁ m₂ m₃ else 0) := by
  have hneg : ∀ m ∈ boxM M, -m ∈ boxM M := fun m hm => by
    unfold boxM at hm ⊢
    obtain ⟨h0, h1⟩ := Finset.mem_erase.1 hm
    obtain ⟨h2, h3⟩ := Finset.mem_Icc.1 h1
    exact Finset.mem_erase.2 ⟨neg_ne_zero.2 h0, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  refine Finset.sum_nbij' (fun m => -m) (fun m => -m) (fun m hm => hneg m hm) (fun m hm => hneg m hm)
    (fun m _ => neg_neg m) (fun m _ => neg_neg m) fun m _ => ?_
  simp only [Int.natAbs_neg, abs_neg]

/-! ### Their Proposition 7.2 -/

/-- The bound at the dyadic scale `2^k`: `2C_J(0)d(q)(N²/(q²2^k))Ĩ_{2^k}(m⃗)`. -/
def Ak {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (X : ℝ) (k : ℕ) (m₁ m₂ m₃ : ℤ) : ℝ :=
  2 * CJ 0 * q.divisors.card * N ^ 2 / (q ^ 2 * 2 ^ k) * It N R χ t X (2 ^ k) m₁ m₂ m₃

/-- Round 654's error at one triple: `(N/q)³(9/4)C_J(K)(2πX)^{−K}φ(q)³|R|³`. -/
def E71 {ι : Type*} (q : ℕ) (N : ℝ) (R : Finset ι) (X : ℝ) (K : ℕ) : ℝ :=
  (N / q) ^ 3 * (9 / 4 * (CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3)))

/-- Regrouping the bounds by the dyadic scale of `m₂`, with `−m₂` replaced by `m₂` in each block. -/
lemma sum_Ak_regroup {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (X : ℝ) (M : ℕ) :
    ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
      (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X (Nat.log 2 m₂.natAbs) m₁ (-m₂) m₃ else 0) =
    ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
      (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ m₂ m₃ else 0) := by
  rw [sum_dyadic M (fun k m₁ m₂ m₃ => if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ (-m₂) m₃ else 0)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m₁ _ => ?_
  simp only [← ite_and]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m₃ _ => sum_neg_m₂ M k (Ak N R χ t X k) m₁ m₃

/-- **Their Proposition 7.2 at one point per character**, with explicit errors: for `M ≥ 1`, `K ≥ 2`, points
`|t_i| ≤ T`, `X > 0` and any `K'`,
`S₃ ≤ 3Σ_{k≤log₂M}Σ_{m⃗}[⌊log₂|m₂|⌋ = k, |m₁|, |m₃| ≤ |m₂|]A_k(m⃗) + 3(2M)³E + |R||μ − μ₀|³
  + 3|R|³τ_M(2N + 1 + τ_M)²`, the sums over `0 < |m_i| ≤ M`, with `A_k = Ak` and `E = E71`. -/
theorem prop72 {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (t : ι → ℝ) {T : ℝ} (ht : ∀ i ∈ R, |t i| ≤ T)
    {M K : ℕ} (hM : 1 ≤ M) (hK : 2 ≤ K) {X : ℝ} (hX : 0 < X) (K' : ℕ) :
    S3 q N R χ t ≤ 3 * ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
        (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ m₂ m₃ else 0) +
      3 * (2 * (M : ℝ)) ^ 3 * E71 q N R X K' + R.card * |muP q N - mu0 q N| ^ 3 +
      3 * (R.card : ℝ) ^ 3 * tauM N q T M K * (2 * N + 1 + tauM N q T M K) ^ 2 := by
  set B := boxM M with hBdef
  -- the truncation (round 650)
  have htr := S3_trunc hN hinj t ht hM hK
  have hS : S3 q N R χ t ≤ ‖∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, Ip N R χ t m₁ m₂ m₃‖ +
      R.card * |muP q N - mu0 q N| ^ 3 +
      3 * (R.card : ℝ) ^ 3 * tauM N q T M K * (2 * N + 1 + tauM N q T M K) ^ 2 := by
    have h1 := (abs_le.1 htr).2
    have h2 := Complex.re_le_norm (∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, Ip N R χ t m₁ m₂ m₃)
    have h4 : -((muP q N - mu0 q N) ^ 3) ≤ |muP q N - mu0 q N| ^ 3 := by
      rw [← abs_pow]; exact neg_le_abs _
    have h3 : -(R.card * (muP q N - mu0 q N) ^ 3) ≤ R.card * |muP q N - mu0 q N| ^ 3 := by
      have := (Nat.cast_nonneg R.card : (0 : ℝ) ≤ R.card)
      nlinarith
    linarith
  -- the triangle inequality and the reduction to `|m₂|` largest (round 655)
  have hsum : ‖∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, Ip N R χ t m₁ m₂ m₃‖ ≤
      3 * ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
        (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun m₁ _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun m₂ _ => norm_sum_le _ _)) ?_
    exact sum_le_three_mul B (fun a b c => ‖Ip N R χ t a b c‖) (fun a b c => norm_nonneg _)
      fun a b c => by rw [Ip_cyc]
  -- the bound at each triple, at the dyadic scale of `m₂` (`Ip_le_It`)
  have hpt : ∀ m₁ ∈ B, ∀ m₂ ∈ B, ∀ m₃ ∈ B,
      (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0) ≤
        (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X (Nat.log 2 m₂.natAbs) m₁ (-m₂) m₃ else 0) +
          E71 q N R X K' := by
    intro m₁ _ m₂ hm₂ m₃ _
    have hE0 : 0 ≤ E71 q N R X K' := by unfold E71; have := CJ_nonneg K'; positivity
    split_ifs
    · exact Ip_le_It hN R χ t m₁ m₂ m₃ hX (M₂ := (2 : ℝ) ^ Nat.log 2 m₂.natAbs) (by positivity)
        (two_pow_log_le (mem_boxM hm₂).1) K'
    · linarith
  have hboxE : ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, E71 q N R X K' = (2 * (M : ℝ)) ^ 3 * E71 q N R X K' := by
    simp only [Finset.sum_const, hBdef, card_boxM, nsmul_eq_mul]; push_cast; ring
  have hmain : ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
      (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0) ≤
      ∑ k ∈ Finset.range (Nat.log 2 M + 1), ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
        (if Nat.log 2 m₂.natAbs = k ∧ |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X k m₁ m₂ m₃ else 0) +
        (2 * (M : ℝ)) ^ 3 * E71 q N R X K' := by
    calc ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then ‖Ip N R χ t m₁ m₂ m₃‖ else 0)
        ≤ ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
            ((if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X (Nat.log 2 m₂.natAbs) m₁ (-m₂) m₃ else 0) +
              E71 q N R X K') :=
          Finset.sum_le_sum fun m₁ h₁ => Finset.sum_le_sum fun m₂ h₂ => Finset.sum_le_sum fun m₃ h₃ =>
            hpt m₁ h₁ m₂ h₂ m₃ h₃
      _ = ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B,
            (if |m₁| ≤ |m₂| ∧ |m₃| ≤ |m₂| then Ak N R χ t X (Nat.log 2 m₂.natAbs) m₁ (-m₂) m₃ else 0) +
            ∑ m₁ ∈ B, ∑ m₂ ∈ B, ∑ m₃ ∈ B, E71 q N R X K' := by
          simp only [Finset.sum_add_distrib]
      _ = _ := by rw [hboxE, hBdef, sum_Ak_regroup]
  have hfin := hS.trans (add_le_add (add_le_add
    (hsum.trans (mul_le_mul_of_nonneg_left hmain (by norm_num))) le_rfl) le_rfl)
  refine hfin.trans (le_of_eq ?_)
  ring

end LinnikCGLP72

#print axioms LinnikCGLP72.measurable_Rt
#print axioms LinnikCGLP72.Rt_le
#print axioms LinnikCGLP72.Ip_le_It
#print axioms LinnikCGLP72.sum_Ak_regroup
#print axioms LinnikCGLP72.prop72
