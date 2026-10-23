/-
# Round 655: the support of `J` in `v₂/v₁`, and the cyclic symmetry of `I′` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

This file supplies two inputs of Chen–Gupta–Li's proof of Proposition 7.2.

The support. Their Cauchy–Schwarz step bounds an integral over `v₂` of `|R(v₂/v₁, b₁⁻¹b₂)|²` by their "R̃_{M₂}(u,a) :=
(∫_{u′∈[1/2,2]} (NM₂/q) ψ̃((NM₂/q)(u−u′)) |R(u′,a)|² du′)^{1/2}" (their (7.5), text layer lines 2246–2257; spaces
restored, the tildes, the integral and its range, the large parentheses, the fractions, the exponents and the subscripts
transcribed). That integral runs over `u′ ∈ [1/2, 2]` only, so with `u′ = v₂/v₁` the step needs `v₂/v₁ ∈ [1/2, 2]`.
Their Proposition 7.1, as stated, integrates over `v₁, v₂ ∈ [1/2, 2]` without that constraint. The kernel supplies it:
`J(v₁, v₂, λ) = 0` unless `v₂/v₁ ∈ (1/2, 2)`, since `u₁ = v₁u₃` and `u₂ = v₂u₃` lie in `(1, 2)` on the support of the
weight (`Jk_eq_zero_of_ratio`). `prop71r` is round 654's `prop71` with the integrand restricted to `v₂/v₁ ∈ [1/2, 2]`.

The symmetry. "These symmetries allow us to reduce the estimation to the case |m₁| ≤ |m₃| ≤ |m₂| at the cost of a
factor 6" (lines 2340–2341, spaces restored, the subscripts transcribed). This file takes only `|m₂|` largest, which
their proof of Proposition 7.2 uses for the length of the `v₂`-interval. That comes from the cyclic symmetry
`I′(m₁, m₂, m₃) = I′(m₂, m₃, m₁)`, a renaming of the triples of points (`Ip_cyc`), at the cost of a factor 3
(`sum_le_three_mul`). Whether §11 also needs `|m₁| ≤ |m₃|` is left to its formalization.

Plain statements.
* `Jk_eq_zero_of_ratio`: `J(v₁, v₂, λ) = 0` unless `v₂/v₁ ∈ (1/2, 2)`.
* `Ip_le_of_bound`: for `N > 0`, if `|Ψ| ≤ c₀V + E` on `[1/2, 2]²` for a measurable `V ≥ 0` bounded there, then
  `|I′(m⃗)| ≤ (N/q)³(c₀∫∫V + (9/4)E)`, the integrals over `[1/2, 2]`.
* `prop71r`: round 654's bound with `W` replaced by `W·[v₂/v₁ ∈ [1/2, 2]]` (`Vr`).
* `Ip_cyc`: `I′(m₁, m₂, m₃) = I′(m₂, m₃, m₁)`.
* `sum_le_three_mul`: for `f ≥ 0` with `f(a, b, c) = f(b, c, a)` and a finite `B ⊆ ℤ`,
  `Σ_{B³}f ≤ 3Σ_{B³}f·[|a| ≤ |b|, |c| ≤ |b|]`; at each triple one of the three cyclic shifts puts the largest absolute
  value in the middle.

* `Jk_eq_zero_of_ratio`, `Ip_le_of_bound`, `Vr`, `prop71r`: Proposition 7.1 on the support of `J` (round 654's proof,
  for any majorant).
* `Ip_cyc`, `sum_shift`, `sum_le_three_mul`: the cyclic symmetry.

The file imports `LinnikCGLP71.lean`.
-/

import LinnikCGLP71

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLSym

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact
  LinnikCGLRam LinnikCGLP71

/-! ### The support of `J` in `v₂/v₁` -/

/-- `J(v₁, v₂, λ) = 0` unless `v₂/v₁ ∈ (1/2, 2)`: on the support of the weight `u₁ = v₁u` and `u₂ = v₂u` lie in
`(1, 2)`. -/
lemma Jk_eq_zero_of_ratio {v₁ v₂ : ℝ} (h : v₂ / v₁ ∉ Ioo (1 / 2 : ℝ) 2) (lam : ℝ) : Jk v₁ v₂ lam = 0 := by
  have hg : ∀ u, gv v₁ v₂ u = 0 := by
    intro u
    unfold gv
    by_cases hu : wCGL u = 0
    · rw [hu]; ring
    by_cases h1 : wCGL (v₁ * u) = 0
    · rw [h1]; ring
    by_cases h2 : wCGL (v₂ * u) = 0
    · rw [h2]; ring
    exfalso
    obtain ⟨hu1, -⟩ := one_lt_of_wCGL_ne hu
    obtain ⟨ha1, ha2⟩ := one_lt_of_wCGL_ne h1
    obtain ⟨hb1, hb2⟩ := one_lt_of_wCGL_ne h2
    have hu0 : u ≠ 0 := by linarith
    have e : v₂ / v₁ = (v₂ * u) / (v₁ * u) := (mul_div_mul_right v₂ v₁ hu0).symm
    have hpos : 0 < v₁ * u := by linarith
    apply h
    rw [e, mem_Ioo, lt_div_iff₀ hpos, div_lt_iff₀ hpos]
    constructor <;> linarith
  unfold Jk
  simp [hg]

/-! ### Their Proposition 7.1 from any majorant -/

/-- **Proposition 7.1's assembly**: for `N > 0`, a measurable majorant `c₀V + E` of `|Ψ|` on `[1/2, 2]²`, with `V ≥ 0`
bounded there, gives `|I′(m⃗)| ≤ (N/q)³(c₀∫∫V + (9/4)E)`. -/
theorem Ip_le_of_bound {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) (V : ℝ → ℝ → ℝ) {c₀ E M : ℝ}
    (hVm : Measurable fun p : ℝ × ℝ => V p.1 p.2) (hV0 : ∀ v₁ v₂, 0 ≤ V v₁ v₂)
    (hVle : ∀ v₁ ∈ Icc (1 / 2 : ℝ) 2, ∀ v₂ ∈ Icc (1 / 2 : ℝ) 2, V v₁ v₂ ≤ M)
    (hPsi : ∀ v₁ ∈ Icc (1 / 2 : ℝ) 2, ∀ v₂ ∈ Icc (1 / 2 : ℝ) 2,
      ‖Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ ≤ c₀ * V v₁ v₂ + E) :
    ‖Ip N R χ t m₁ m₂ m₃‖ ≤
      (N / q) ^ 3 * (c₀ * (∫ v₁ in Icc (1 / 2 : ℝ) 2, ∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) + 9 / 4 * E) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hI1 : ∀ v₁ ∈ Icc (1 / 2 : ℝ) 2, IntegrableOn (fun v₂ => V v₁ v₂) (Icc (1 / 2 : ℝ) 2) := by
    intro v₁ h1
    refine Integrable.mono' (integrableOn_const (C := M) (by simp)) ?_ ?_
    · exact (hVm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v₂ h2 => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hV0 v₁ v₂)]
      exact hVle v₁ h1 v₂ h2
  have hI2 : IntegrableOn (fun v₁ => ∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) (Icc (1 / 2 : ℝ) 2) := by
    refine Integrable.mono' (integrableOn_const (C := 3 / 2 * M) (by simp)) ?_ ?_
    · exact (hVm.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Icc (1 / 2 : ℝ) 2))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v₁ h1 => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Icc fun v₂ _ => hV0 v₁ v₂)]
      calc ∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂ ≤ ∫ _ in Icc (1 / 2 : ℝ) 2, M :=
            setIntegral_mono_on (hI1 v₁ h1) (integrableOn_const (by simp)) measurableSet_Icc
              fun v₂ h2 => hVle v₁ h1 v₂ h2
        _ = 3 / 2 * M := by
            rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]; ring
  have hinner : ∀ v₁ ∈ Icc (1 / 2 : ℝ) 2,
      ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ ≤ c₀ * (∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) + 3 / 2 * E := by
    intro v₁ h1
    have e : ∫ v₂ in Icc (1 / 2 : ℝ) 2, Psi N R χ t m₁ m₂ m₃ v₁ v₂ = ∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun v₂ hv₂ => Psi_eq_zero N R χ t m₁ m₂ m₃ (Or.inr hv₂)
    rw [← e]
    have hint : IntegrableOn (fun v₂ => c₀ * V v₁ v₂ + E) (Icc (1 / 2 : ℝ) 2) :=
      ((hI1 v₁ h1).const_mul c₀).add (integrableOn_const (by simp))
    refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun v₂ h2 => hPsi v₁ h1 v₂ h2))).trans (le_of_eq ?_)
    rw [integral_add ((hI1 v₁ h1).const_mul c₀) (integrableOn_const (by simp)), integral_const_mul,
      setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]
    ring
  rw [Ip_eq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_pos hN hq).le]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : ∫ v₁ in Icc (1 / 2 : ℝ) 2, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ =
      ∫ v₁ : ℝ, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v₁ hv₁ => by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun v₂ => Psi_eq_zero N R χ t m₁ m₂ m₃ (Or.inl hv₁)),
        integral_zero, norm_zero]
  calc ‖∫ v₁ : ℝ, ∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖
      ≤ ∫ v₁ : ℝ, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ := norm_integral_le_integral_norm _
    _ = ∫ v₁ in Icc (1 / 2 : ℝ) 2, ‖∫ v₂ : ℝ, Psi N R χ t m₁ m₂ m₃ v₁ v₂‖ := e1.symm
    _ ≤ ∫ v₁ in Icc (1 / 2 : ℝ) 2, (c₀ * (∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) + 3 / 2 * E) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((hI2.const_mul c₀).add (integrableOn_const (by simp)))
          ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hinner))
    _ = c₀ * (∫ v₁ in Icc (1 / 2 : ℝ) 2, ∫ v₂ in Icc (1 / 2 : ℝ) 2, V v₁ v₂) + 9 / 4 * E := by
        rw [integral_add (hI2.const_mul c₀) (integrableOn_const (by simp)), integral_const_mul, setIntegral_const,
          smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num)]
        ring

/-- The integrand of their Proposition 7.1 on the support of `J`: `W` where `|m₁v₁ + m₂v₂ + m₃| ≤ Xq/N` and
`v₂/v₁ ∈ [1/2, 2]`, and `0` elsewhere. -/
def Vr {ι : Type*} {q : ℕ} [NeZero q] (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) (X v₁ v₂ : ℝ) : ℝ :=
  if |m₁ * v₁ + m₂ * v₂ + m₃| ≤ X * q / N ∧ v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 then Wm R χ t m₁ m₂ m₃ v₁ v₂ else 0

/-- **Their Proposition 7.1 with the support of `J` in `v₂/v₁` kept**: as round 654's `prop71` (for `N > 0`, `X > 0` and
any `K`), with the integrand restricted to `v₂/v₁ ∈ [1/2, 2]`. -/
theorem prop71r {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (R : Finset ι)
    (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (m₁ m₂ m₃ : ℤ) {X : ℝ} (hX : 0 < X) (K : ℕ) :
    ‖Ip N R χ t m₁ m₂ m₃‖ ≤ (N / q) ^ 3 * (CJ 0 * q.divisors.card *
      (∫ v₁ in Icc (1 / 2 : ℝ) 2, ∫ v₂ in Icc (1 / 2 : ℝ) 2, Vr N R χ t m₁ m₂ m₃ X v₁ v₂) +
      9 / 4 * (CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3))) := by
  have hE0 : 0 ≤ CJ K / (2 * π * X) ^ K * ((q.totient : ℝ) ^ 3 * (R.card : ℝ) ^ 3) := by
    have := CJ_nonneg K; positivity
  have hV0 : ∀ v₁ v₂, 0 ≤ Vr N R χ t m₁ m₂ m₃ X v₁ v₂ := fun v₁ v₂ => by
    unfold Vr; split_ifs
    · exact Wm_nonneg R χ t m₁ m₂ m₃ v₁ v₂
    · exact le_rfl
  refine Ip_le_of_bound hN R χ t m₁ m₂ m₃ (fun v₁ v₂ => Vr N R χ t m₁ m₂ m₃ X v₁ v₂)
    (M := (q.totient : ℝ) ^ 2 * (q * (R.card : ℝ) ^ 3)) ?_ hV0 ?_ ?_
  · have hS : MeasurableSet
        {p : ℝ × ℝ | |(m₁ : ℝ) * p.1 + m₂ * p.2 + m₃| ≤ X * q / N ∧ p.2 / p.1 ∈ Icc (1 / 2 : ℝ) 2} := by
      have h1 : MeasurableSet {p : ℝ × ℝ | |(m₁ : ℝ) * p.1 + m₂ * p.2 + m₃| ≤ X * q / N} :=
        measurableSet_le (by fun_prop) measurable_const
      have h2 : MeasurableSet {p : ℝ × ℝ | p.2 / p.1 ∈ Icc (1 / 2 : ℝ) 2} :=
        (measurable_snd.div measurable_fst) measurableSet_Icc
      exact h1.inter h2
    unfold Vr
    exact Measurable.ite hS (measurable_Wm R χ t m₁ m₂ m₃) measurable_const
  · intro v₁ h1 v₂ h2
    unfold Vr; split_ifs
    · exact Wm_le R χ t m₁ m₂ m₃ (by linarith [h1.1]) (by linarith [h2.1])
    · positivity
  · intro v₁ h1 v₂ h2
    by_cases hr : v₂ / v₁ ∈ Ioo (1 / 2 : ℝ) 2
    · have h := norm_Psi_le hN R χ t m₁ m₂ m₃ hX K h1 h2
      have hr' : v₂ / v₁ ∈ Icc (1 / 2 : ℝ) 2 := Ioo_subset_Icc_self hr
      simp only [Vr, hr', and_true]
      exact h
    · have h0 : Psi N R χ t m₁ m₂ m₃ v₁ v₂ = 0 := by
        unfold Psi; rw [Jk_eq_zero_of_ratio hr, zero_mul]
      rw [h0, norm_zero]
      exact add_nonneg (mul_nonneg (mul_nonneg (CJ_nonneg 0) (Nat.cast_nonneg _)) (hV0 v₁ v₂)) hE0

/-! ### The cyclic symmetry of `I′` -/

/-- **The cyclic symmetry**: `I′(m₁, m₂, m₃) = I′(m₂, m₃, m₁)`. -/
lemma Ip_cyc {ι : Type*} {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) : Ip N R χ t m₁ m₂ m₃ = Ip N R χ t m₂ m₃ m₁ := by
  calc Ip N R χ t m₁ m₂ m₃
      = ∑ c ∈ R, ∑ a ∈ R, ∑ b ∈ R, phi N χ t c a m₁ * phi N χ t a b m₂ * phi N χ t b c m₃ := rfl
    _ = ∑ a ∈ R, ∑ b ∈ R, ∑ c ∈ R, phi N χ t c a m₁ * phi N χ t a b m₂ * phi N χ t b c m₃ :=
        (sum_rot3 R R R fun a b c => phi N χ t c a m₁ * phi N χ t a b m₂ * phi N χ t b c m₃).symm
    _ = Ip N R χ t m₂ m₃ m₁ := by
        unfold Ip
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        ring

/-- A triple sum is unchanged by the cyclic shift of its arguments. -/
lemma sum_shift (B : Finset ℤ) (F : ℤ → ℤ → ℤ → ℝ) :
    ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, F b c a = ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, F a b c :=
  calc ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, F b c a = ∑ b ∈ B, ∑ a ∈ B, ∑ c ∈ B, F b c a := Finset.sum_comm
    _ = ∑ b ∈ B, ∑ c ∈ B, ∑ a ∈ B, F b c a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **The reduction to `|m₂|` largest**: for `f ≥ 0` invariant under the cyclic shift,
`Σ_{B³}f ≤ 3Σ_{B³, |m₁|,|m₃| ≤ |m₂|}f`. -/
lemma sum_le_three_mul (B : Finset ℤ) (f : ℤ → ℤ → ℤ → ℝ) (hf0 : ∀ a b c, 0 ≤ f a b c)
    (hcyc : ∀ a b c, f a b c = f b c a) :
    ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, f a b c ≤
      3 * ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, (if |a| ≤ |b| ∧ |c| ≤ |b| then f a b c else 0) := by
  set g : ℤ → ℤ → ℤ → ℝ := fun a b c => if |a| ≤ |b| ∧ |c| ≤ |b| then f a b c else 0 with hg
  have h0 : ∀ x y z, 0 ≤ g x y z := fun x y z => by
    simp only [hg]; split_ifs
    · exact hf0 x y z
    · exact le_rfl
  have hpt : ∀ a b c, f a b c ≤ g a b c + g b c a + g c a b := by
    intro a b c
    have e1 : f b c a = f a b c := (hcyc a b c).symm
    have e2 : f c a b = f a b c := hcyc c a b
    by_cases hb : |a| ≤ |b| ∧ |c| ≤ |b|
    · have h : g a b c = f a b c := by simp [hg, hb]
      linarith [h0 b c a, h0 c a b]
    by_cases hc : |b| ≤ |c| ∧ |a| ≤ |c|
    · have h : g b c a = f a b c := by simp [hg, hc, e1]
      linarith [h0 a b c, h0 c a b]
    have ha : |c| ≤ |a| ∧ |b| ≤ |a| := by
      generalize |a| = x at hb hc ⊢
      generalize |b| = y at hb hc ⊢
      generalize |c| = z at hb hc ⊢
      omega
    have h : g c a b = f a b c := by simp [hg, ha, e2]
    linarith [h0 a b c, h0 b c a]
  have r1 : ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g b c a = ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g a b c := sum_shift B g
  have r2 : ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g c a b = ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g a b c :=
    (sum_shift B fun x y z => g y z x).trans r1
  calc ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, f a b c
      ≤ ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, (g a b c + g b c a + g c a b) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => hpt a b c
    _ = ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g a b c + ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g b c a +
          ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g c a b := by
        simp only [Finset.sum_add_distrib]
    _ = 3 * ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, g a b c := by
        rw [r1, r2]; ring

end LinnikCGLSym

#print axioms LinnikCGLSym.Jk_eq_zero_of_ratio
#print axioms LinnikCGLSym.prop71r
#print axioms LinnikCGLSym.Ip_cyc
#print axioms LinnikCGLSym.sum_le_three_mul
