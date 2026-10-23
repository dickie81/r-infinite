/-
# Round 665: the Fourier decay of their `f_b`, in the form of their Proposition 8.1 (the CGL plan's stage M3, the `S₃`
side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 663's `f_b = ψR̃(·, −b)²` is an average of round 664's `φ_{u′} = ψK(· − u′)` against
`g_a(u′) = 1_{[1/2,2]}(u′)|R(u′, a)|²`, with `a = −b`: `f_b(u) = ∫φ_{u′}(u)g_a(u′) du′`. Fubini gives
`f̂_b(ξ) = ∫g_a(u′)φ̂_{u′}(ξ) du′`. So round 664's `(2π|ξ|)^j|φ̂_{u′}(ξ)| ≤ B_j(L, X)` and `|R(u′, a)| ≤ |R|` give
`(2π|ξ|)^jΣ_b|f̂_b(ξ)| ≤ B_j(L, X)·(3/2)φ(q)|R|²`. Their step: "Applying the convolution theorem and noting
∫ |R(u,−b)|² 1_{[1/2,2]}(u) du ≪ |W|² since |R(u,−b)| ≤ |W|, we see that Σ_{1≤b≤q, (b,q)=1} |f̂_b(ξ)| ⪅_j
ϕ(q)|W|² (NM₂/(q|ξ|))^j." (text layer lines 5786–5797; spaces restored, the integral, sum, hat, fraction, large
parentheses, subscripts and exponents transcribed).

The constants. They note "Notice that M₂ ≤ (qT)^ϵ qT/N." (line 5761; spaces restored, the subscript and exponent
transcribed), that is `L ≤ XT` with `L = NM₂/q` and `X` for their `(qT)^ϵ`. For `j ≥ 1` and `T ≥ 1` this gives
`c = L/(2X) ≤ T`, and each term of `B_j` is at most `2T^j·min(2X, L/(2T))` times a constant depending only on `j`:
`B_j(L, X) ≤ 2T^j·min(2X, L/(2T))·E_j`. With round 663's `f_{−1}(1) ≥ min(2X, L/(2T))|R|²/2`, this gives
`Σ_b|f̂_b(ξ)| ≤ (6E_j/(2π)^j)(T/|ξ|)^jφ(q)f_{−1}(1)`. Their chain: "This implies Σ_b |f̂_b(ξ)| ⪅_j
ϕ(q)|W|² (NM₂/(q|ξ|))^j ⪅ ϕ(q) (T/|ξ|^j) (NM₂/q)^{j−1} f_{q−1}(1) ⪅_j ϕ(q) (T^j/|ξ|^j) sup_{b,u} f_b(u). Namely, we
have the desired Fourier decay." (lines 5813–5829; spaces restored, the sum, hats, fractions, large parentheses,
subscripts and exponents transcribed). The stack's constant carries no power of `X`: round 664's `B_j` keeps the
factor `(2X)^{−j}` of the kernel's scaling.

For `j = 0` the stack uses `Σ_b|f̂_b(ξ)| ≤ Σ_b∫f_b ≤ 8φ(q)sup f`, since `f_b` vanishes off `[−4, 4]`; this needs no
relation between `L` and `T`. Round 663's `exists_max` supplies a largest value `f_{b₀}(u₀)`, and the two cases give
the decay premise of round 662's `CGLP81` with `D_0 = 8` and `D_j = 6E_j/(2π)^j` for `j ≥ 1`.

Plain statements, with `q ≥ 1`, `L = NM₂/q` and `a = −b`.
* `fb_eq_integral`: for `L ≥ 0`, `f_b(u) = ∫φ_{u′}(u)g_a(u′) du′`.
* `fourier_fb_eq`: for `L > 0`, `f̂_b(ξ) = ∫g_a(u′)φ̂_{u′}(ξ) du′`.
* `pow_mul_norm_fourier_fb_le`: for `L, X > 0`, `(2π|ξ|)^j|f̂_b(ξ)| ≤ B_j(L, X)∫g_a`.
* `sum_pow_mul_norm_fourier_fb_le`: for `L, X > 0`, `(2π|ξ|)^jΣ_b|f̂_b(ξ)| ≤ B_j(L, X)·(3/2)φ(q)|R|²`.
* `Bj_le`: for `L, X > 0`, `T ≥ 1`, `L ≤ XT` and `j ≥ 1`, `B_j(L, X) ≤ 2T^j·min(2X, L/(2T))·E_j`.
* `fb_decay`: for `L, X > 0`, `T ≥ 1`, points `|t_i| ≤ T`, `L ≤ XT`, `j ≥ 1` and `ξ ≠ 0`,
  `Σ_b|f̂_b(ξ)| ≤ (6E_j/(2π)^j)(T/|ξ|)^jφ(q)f_{−1}(1)`.
* `fb_decay_all`: for `L, X > 0`, `T ≥ 1`, points `|t_i| ≤ T` and `L ≤ XT`, some `f_{b₀}(u₀)` has
  `Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jφ(q)f_{b₀}(u₀)` for every `j` and `ξ ≠ 0`: the decay premise of `CGLP81`.

* `gR`, `gR_nonneg`, `gR_le`, `integrable_gR`, `integral_gR_le`: `g_a`, with `0 ≤ g_a ≤ |R|²1_{[1/2,2]}`.
* `abs_phiR_le`, `fb_eq_integral`, `fourier_fb_eq`: `f_b` and `f̂_b` as averages.
* `pow_mul_norm_fourier_fb_le`, `sum_pow_mul_norm_fourier_fb_le`: the decay with `B_j`.
* `Ej`, `Ej_nonneg`, `Bj_le`, `fb_decay`: the decay for `j ≥ 1`.
* `integral_fb_le`, `Dfb`, `fb_decay_all`: the case `j = 0` and the premise of `CGLP81`.

The file imports `LinnikCGLPhi.lean`.
-/

import LinnikCGLPhi

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLDecay

open LinnikCGLRFact LinnikCGLP71 LinnikCGLRt LinnikCGLMom LinnikCGLFb LinnikCGLPhi

/-! ### `g_a = 1_{[1/2,2]}|R(·, a)|²` -/

/-- `g_a(u′) = 1_{[1/2,2]}(u′)|R(u′, a)|²`. -/
def gR {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (a : ZMod q) (u' : ℝ) : ℝ :=
  (Icc (1 / 2 : ℝ) 2).indicator (fun v => ‖Rf R χ t v a‖ ^ 2) u'

section gR

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (a : ZMod q)

lemma gR_nonneg (u' : ℝ) : 0 ≤ gR R χ t a u' :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) u'

lemma gR_le (u' : ℝ) : gR R χ t a u' ≤ (R.card : ℝ) ^ 2 * (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) u' := by
  unfold gR
  by_cases h : u' ∈ Icc (1 / 2 : ℝ) 2
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_Rf_le R χ t (by linarith [h.1]) a) 2
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

lemma measurable_gR : Measurable (gR R χ t a) :=
  ((measurable_Rf R χ t a).norm.pow_const 2).indicator measurableSet_Icc

lemma integrable_gR : Integrable (gR R χ t a) :=
  (((integrableOn_const (C := (1 : ℝ)) (by simp)).integrable_indicator measurableSet_Icc).const_mul
    ((R.card : ℝ) ^ 2)).mono'
    (measurable_gR R χ t a).aestronglyMeasurable (Eventually.of_forall fun u' => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gR_nonneg R χ t a u')]
      exact gR_le R χ t a u')

/-- `∫g_a ≤ (3/2)|R|²`. -/
lemma integral_gR_le : ∫ u', gR R χ t a u' ≤ 3 / 2 * (R.card : ℝ) ^ 2 := by
  calc ∫ u', gR R χ t a u' ≤ ∫ u', (R.card : ℝ) ^ 2 * (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) u' :=
        integral_mono (integrable_gR R χ t a)
          (((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).const_mul _) (gR_le R χ t a)
    _ = 3 / 2 * (R.card : ℝ) ^ 2 := by
        rw [integral_const_mul, integral_indicator measurableSet_Icc, setIntegral_const,
          Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
        ring

end gR

/-! ### `f_b` and `f̂_b` as averages over `u′` -/

/-- `|φ_{u′}(u)| ≤ L·1_{[−4,4]}(u)` for `L ≥ 0`. -/
lemma abs_phiR_le {L X : ℝ} (hL : 0 ≤ L) (u' u : ℝ) :
    |phiR L X u' u| ≤ L * (Icc (-4 : ℝ) 4).indicator (fun _ => (1 : ℝ)) u := by
  unfold phiR kerL
  by_cases h : u ∈ Icc (-4 : ℝ) 4
  · set p := psi0 (L * (u - u') / (2 * X)) with hp
    have hp0 : 0 ≤ p := psi0_nonneg _
    rw [Set.indicator_of_mem h, mul_one, abs_mul, abs_mul, abs_of_nonneg (psiW_nonneg u), abs_of_nonneg hL,
      abs_of_nonneg hp0]
    calc psiW u * (L * p) ≤ 1 * (L * 1) :=
          mul_le_mul (psiW_le_one u) (mul_le_mul_of_nonneg_left (psi0_le_one _) hL) (by positivity) zero_le_one
      _ = L := by ring
  · have hu : 4 ≤ |u| := by
      by_contra h'
      push Not at h'
      exact h (abs_le.mp h'.le)
    rw [psiW_eq_zero hu, zero_mul, abs_zero, Set.indicator_of_notMem h, mul_zero]

section fb

variable {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
  {X M₂ : ℝ}

/-- `f_b(u) = ∫φ_{u′}(u)g_{−b}(u′) du′` for `L ≥ 0`. -/
lemma fb_eq_integral (hL : 0 ≤ N * M₂ / q) (b : (ZMod q)ˣ) (u : ℝ) :
    fb N R χ t X M₂ b u = ∫ u', phiR (N * M₂ / q) X u' u * gR R χ t ((-b : (ZMod q)ˣ) : ZMod q) u' := by
  unfold fb
  rw [Rt_sq R χ t hL, ← integral_indicator measurableSet_Icc, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u' => ?_)
  simp only [gR, Set.indicator, phiR, kerL]
  split_ifs <;> ring

/-- **`f̂_b` by Fubini**: for `L > 0`, `f̂_b(ξ) = ∫g_{−b}(u′)φ̂_{u′}(ξ) du′`. -/
lemma fourier_fb_eq (hL : 0 < N * M₂ / q) (b : (ZMod q)ˣ) (ξ : ℝ) :
    𝓕 (fun u => (fb N R χ t X M₂ b u : ℂ)) ξ = ∫ u', (gR R χ t ((-b : (ZMod q)ˣ) : ZMod q) u' : ℂ) *
      𝓕 (fun x => (phiR (N * M₂ / q) X u' x : ℂ)) ξ := by
  set L := N * M₂ / q with hLdef
  set g := gR R χ t ((-b : (ZMod q)ˣ) : ZMod q) with hg
  set F : ℝ × ℝ → ℂ := fun p => cexp (↑(-2 * π * p.1 * ξ) * I) • ((phiR L X p.2 p.1 * g p.2 : ℝ) : ℂ) with hF
  have hFm : Measurable F := by
    have h1 : Continuous fun p : ℝ × ℝ => cexp (↑(-2 * π * p.1 * ξ) * I) := by fun_prop
    have h2 : Continuous fun p : ℝ × ℝ => phiR L X p.2 p.1 :=
      (contDiff_psiW.continuous.comp continuous_fst).mul
        ((contDiff_kerL L X).continuous.comp (continuous_fst.sub continuous_snd))
    exact h1.measurable.smul (Complex.measurable_ofReal.comp
      (h2.measurable.mul ((measurable_gR R χ t _).comp measurable_snd)))
  have hFint : Integrable F (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => (L * (Icc (-4 : ℝ) 4).indicator (fun _ => (1 : ℝ)) p.1) *
        ((R.card : ℝ) ^ 2 * (Icc (1 / 2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.2)) (volume.prod volume) :=
      Integrable.mul_prod (((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).const_mul L)
        (((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).const_mul _)
    refine hdom.mono' hFm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [hF, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (gR_nonneg R χ t _ p.2)]
    exact mul_le_mul (abs_phiR_le hL.le p.2 p.1) (gR_le R χ t _ p.2) (gR_nonneg R χ t _ p.2)
      (mul_nonneg hL.le (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
  have hleft : ∀ u, cexp (↑(-2 * π * u * ξ) * I) • ((fb N R χ t X M₂ b u : ℝ) : ℂ) = ∫ u', F (u, u') := by
    intro u
    rw [fb_eq_integral R χ t hL.le b u, ← integral_complex_ofReal, ← integral_smul]
  have hright : ∀ u', (g u' : ℂ) * 𝓕 (fun x => (phiR L X u' x : ℂ)) ξ = ∫ u, F (u, u') := by
    intro u'
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF, smul_eq_mul]
    push_cast
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [hleft, hright]
  exact integral_integral_swap (f := fun u u' => F (u, u')) hFint

/-- `(2π|ξ|)^j|f̂_b(ξ)| ≤ B_j(L, X)∫g_{−b}` for `L, X > 0`. -/
lemma pow_mul_norm_fourier_fb_le (hL : 0 < N * M₂ / q) (hX : 0 < X) (b : (ZMod q)ˣ) (j : ℕ) (ξ : ℝ) :
    (2 * π * |ξ|) ^ j * ‖𝓕 (fun u => (fb N R χ t X M₂ b u : ℂ)) ξ‖ ≤
      Bj (N * M₂ / q) X j * ∫ u', gR R χ t ((-b : (ZMod q)ˣ) : ZMod q) u' := by
  set g := gR R χ t ((-b : (ZMod q)ˣ) : ZMod q) with hg
  set r : ℝ := (2 * π * |ξ|) ^ j with hr
  have hr0 : 0 ≤ r := by positivity
  have e : r * ‖∫ u', (g u' : ℂ) * 𝓕 (fun x => (phiR (N * M₂ / q) X u' x : ℂ)) ξ‖ =
      ‖∫ u', (r : ℂ) * ((g u' : ℂ) * 𝓕 (fun x => (phiR (N * M₂ / q) X u' x : ℂ)) ξ)‖ := by
    rw [integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [fourier_fb_eq R χ t hL b ξ, e, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_gR R χ t _).const_mul _) (Eventually.of_forall fun u' => ?_)
  have hg0 : 0 ≤ g u' := gR_nonneg R χ t _ u'
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hr0, abs_of_nonneg hg0]
  have h := fourier_phi_le hL hX u' j ξ
  calc r * (g u' * ‖𝓕 (fun x => (phiR (N * M₂ / q) X u' x : ℂ)) ξ‖)
      = g u' * (r * ‖𝓕 (fun x => (phiR (N * M₂ / q) X u' x : ℂ)) ξ‖) := by ring
    _ ≤ g u' * Bj (N * M₂ / q) X j := mul_le_mul_of_nonneg_left h hg0
    _ = Bj (N * M₂ / q) X j * g u' := by ring

/-- **The sum over `b`**: `(2π|ξ|)^jΣ_b|f̂_b(ξ)| ≤ B_j(L, X)·(3/2)φ(q)|R|²` for `L, X > 0`. -/
lemma sum_pow_mul_norm_fourier_fb_le (hL : 0 < N * M₂ / q) (hX : 0 < X) (j : ℕ) (ξ : ℝ) :
    (2 * π * |ξ|) ^ j * ∑ b, ‖𝓕 (fun u => (fb N R χ t X M₂ b u : ℂ)) ξ‖ ≤
      Bj (N * M₂ / q) X j * (3 / 2 * q.totient * (R.card : ℝ) ^ 2) := by
  have hB : 0 ≤ Bj (N * M₂ / q) X j :=
    (by positivity : (0 : ℝ) ≤ (2 * π * |(0 : ℝ)|) ^ j * ‖𝓕 (fun x => (phiR (N * M₂ / q) X 0 x : ℂ)) 0‖).trans
      (fourier_phi_le hL hX 0 j 0)
  rw [Finset.mul_sum]
  calc ∑ b, (2 * π * |ξ|) ^ j * ‖𝓕 (fun u => (fb N R χ t X M₂ b u : ℂ)) ξ‖
      ≤ ∑ _b : (ZMod q)ˣ, Bj (N * M₂ / q) X j * (3 / 2 * (R.card : ℝ) ^ 2) :=
        Finset.sum_le_sum fun b _ => (pow_mul_norm_fourier_fb_le R χ t hL hX b j ξ).trans
          (mul_le_mul_of_nonneg_left (integral_gR_le R χ t _) hB)
    _ = Bj (N * M₂ / q) X j * (3 / 2 * q.totient * (R.card : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
        ring

end fb

/-! ### The decay for `j ≥ 1` -/

/-- `E_j = Σ_{i≤j}C(j, i)e_i`, with `e_0 = I₀(j)` and `e_i = P(i)S₀(j − i)` for `i ≥ 1`: a constant depending only on
`j`. -/
def Ej (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (if i = 0 then I0 j else Pw i * S0 (j - i))

lemma Ej_nonneg (j : ℕ) : 0 ≤ Ej j := by
  unfold Ej
  refine Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) ?_
  split_ifs
  · exact I0_nonneg j
  · exact mul_nonneg (Pw_nonneg i) (S0_nonneg _)

/-- **The constants**: for `L, X > 0`, `T ≥ 1`, `L ≤ XT` and `j ≥ 1`, `B_j(L, X) ≤ 2T^j·min(2X, L/(2T))·E_j`. -/
lemma Bj_le {L X T : ℝ} (hL : 0 < L) (hX : 0 < X) (hT : 1 ≤ T) (hLX : L ≤ X * T) {j : ℕ} (hj : 1 ≤ j) :
    Bj L X j ≤ 2 * T ^ j * min (2 * X) (L / (2 * T)) * Ej j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hT0 : 0 < T := by linarith
  -- `2T^{k+1}·min(2X, L/(2T)) = min(4XT^{k+1}, LT^k)`
  have hm : 2 * T ^ (k + 1) * min (2 * X) (L / (2 * T)) = min (4 * X * T ^ (k + 1)) (L * T ^ k) := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    congr 1
    · ring
    · rw [pow_succ]
      field_simp
  unfold Bj Ej
  set c := L / (2 * X) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcT : c ≤ T := by
    rw [hc, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hX hT0]
  have hcX : 2 * X * c = L := by
    rw [hc]
    field_simp
  -- `c^n ≤ T^k` for `n ≤ k`
  have hcn : ∀ n ≤ k, c ^ n ≤ T ^ k := fun n hn =>
    (pow_le_pow_left₀ hc0 hcT n).trans (pow_le_pow_right₀ hT hn)
  rw [hm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hC : (0 : ℝ) ≤ ((k + 1).choose i : ℝ) := Nat.cast_nonneg _
  by_cases hi0 : i = 0
  · subst hi0
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have key : 2 * X * c ^ (k + 1) ≤ min (4 * X * T ^ (k + 1)) (L * T ^ k) := by
      refine le_min ?_ ?_
      · have := pow_le_pow_left₀ hc0 hcT (k + 1)
        nlinarith [pow_pos hT0 (k + 1)]
      · calc 2 * X * c ^ (k + 1) = 2 * X * c * c ^ k := by ring
          _ = L * c ^ k := by rw [hcX]
          _ ≤ L * T ^ k := mul_le_mul_of_nonneg_left (hcn k le_rfl) hL.le
    have hI := I0_nonneg (k + 1)
    calc ((k + 1).choose 0 : ℝ) * (2 * X * c ^ (k + 1) * I0 (k + 1))
        = (((k + 1).choose 0 : ℝ) * I0 (k + 1)) * (2 * X * c ^ (k + 1)) := by ring
      _ ≤ (((k + 1).choose 0 : ℝ) * I0 (k + 1)) * min (4 * X * T ^ (k + 1)) (L * T ^ k) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hC hI)
      _ = _ := by ring
  · rw [ite_eq_right hi0, ite_eq_right hi0]
    have hn : k + 1 - i ≤ k := by omega
    have h1 := hcn (k + 1 - i) hn
    have key : L * c ^ (k + 1 - i) ≤ min (4 * X * T ^ (k + 1)) (L * T ^ k) := by
      refine le_min ?_ (mul_le_mul_of_nonneg_left h1 hL.le)
      calc L * c ^ (k + 1 - i) ≤ L * T ^ k := mul_le_mul_of_nonneg_left h1 hL.le
        _ ≤ X * T * T ^ k := mul_le_mul_of_nonneg_right hLX (by positivity)
        _ = X * T ^ (k + 1) := by ring
        _ ≤ 4 * X * T ^ (k + 1) := by nlinarith [pow_pos hT0 (k + 1)]
    have hP := Pw_nonneg i
    have hS := S0_nonneg (k + 1 - i)
    calc ((k + 1).choose i : ℝ) * (Pw i * (L * c ^ (k + 1 - i) * S0 (k + 1 - i)))
        = (((k + 1).choose i : ℝ) * (Pw i * S0 (k + 1 - i))) * (L * c ^ (k + 1 - i)) := by ring
      _ ≤ (((k + 1).choose i : ℝ) * (Pw i * S0 (k + 1 - i))) * min (4 * X * T ^ (k + 1)) (L * T ^ k) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hC (mul_nonneg hP hS))
      _ = _ := by ring

section decay

variable {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
  {X M₂ T : ℝ}

/-- **The decay for `j ≥ 1`**: for `L, X > 0`, `T ≥ 1`, points `|t_i| ≤ T`, `L ≤ XT`, `j ≥ 1` and `ξ ≠ 0`,
`Σ_b|f̂_b(ξ)| ≤ (6E_j/(2π)^j)(T/|ξ|)^jφ(q)f_{−1}(1)`. -/
theorem fb_decay (hL : 0 < N * M₂ / q) (hX : 0 < X) (hT : 1 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T)
    (hLX : N * M₂ / q ≤ X * T) {j : ℕ} (hj : 1 ≤ j) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∑ b, ‖𝓕 (fun u => (fb N R χ t X M₂ b u : ℂ)) ξ‖ ≤
      6 * Ej j / (2 * π) ^ j * (T / |ξ|) ^ j * q.totient * fb N R χ t X M₂ (-1) 1 := by
  set S := ∑ b, ‖𝓕 (fun u => (fb N R χ t X M₂ b u : ℂ)) ξ‖ with hS
  set m := min (2 * X) (N * M₂ / q / (2 * T)) with hm
  set F := fb N R χ t X M₂ (-1) 1 with hF
  have hT0 : 0 < T := by linarith
  have hξ0 : 0 < |ξ| := abs_pos.mpr hξ
  have hpos : 0 < (2 * π * |ξ|) ^ j := by positivity
  have h1 := sum_pow_mul_norm_fourier_fb_le R χ t (X := X) hL hX j ξ
  have h2 := Bj_le hL hX hT hLX hj
  have h3 := fb_one_ge R χ t hL hX hT ht
  have hE := Ej_nonneg j
  have hK : 0 ≤ 3 / 2 * (q.totient : ℝ) * (R.card : ℝ) ^ 2 := by positivity
  have hA : 0 ≤ 3 * T ^ j * Ej j * q.totient :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hT0.le j)) hE) (Nat.cast_nonneg _)
  have e : 6 * Ej j / (2 * π) ^ j * (T / |ξ|) ^ j * q.totient * F =
      6 * Ej j * T ^ j * q.totient * F / (2 * π * |ξ|) ^ j := by
    rw [div_pow, mul_pow (2 * π) |ξ| j]
    field_simp
  rw [e, le_div_iff₀ hpos]
  calc S * (2 * π * |ξ|) ^ j = (2 * π * |ξ|) ^ j * S := by ring
    _ ≤ Bj (N * M₂ / q) X j * (3 / 2 * q.totient * (R.card : ℝ) ^ 2) := h1
    _ ≤ 2 * T ^ j * m * Ej j * (3 / 2 * q.totient * (R.card : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h2 hK
    _ = 3 * T ^ j * Ej j * q.totient * (m * (R.card : ℝ) ^ 2) := by ring
    _ ≤ 3 * T ^ j * Ej j * q.totient * (2 * F) := mul_le_mul_of_nonneg_left (by linarith) hA
    _ = 6 * Ej j * T ^ j * q.totient * F := by ring

/-- `∫f_b ≤ 8M` when `f_b ≤ M` everywhere, since `f_b` vanishes off `[−4, 4]`. -/
lemma integral_fb_le (hL : 0 < N * M₂ / q) (hX : 0 < X) (b : (ZMod q)ˣ) {M : ℝ}
    (hM : ∀ u, fb N R χ t X M₂ b u ≤ M) : ∫ u, fb N R χ t X M₂ b u ≤ 8 * M := by
  have hout : ∀ u, u ∉ Icc (-4 : ℝ) 4 → fb N R χ t X M₂ b u = 0 := fun u hu => fb_eq_zero R χ t b (by
    by_contra h
    push Not at h
    exact hu (abs_le.mp h))
  have hint : Integrable (fb N R χ t X M₂ b) :=
    (contDiff_fb R χ t hL hX b).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -4) (b := 4)) hout)
  have hdom : ∀ u, fb N R χ t X M₂ b u ≤ (Icc (-4 : ℝ) 4).indicator (fun _ => M) u := by
    intro u
    by_cases h : u ∈ Icc (-4 : ℝ) 4
    · rw [Set.indicator_of_mem h]
      exact hM u
    · rw [Set.indicator_of_notMem h, hout u h]
  calc ∫ u, fb N R χ t X M₂ b u ≤ ∫ u, (Icc (-4 : ℝ) 4).indicator (fun _ => M) u :=
        integral_mono hint ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc) hdom
    _ = 8 * M := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le (by norm_num),
          smul_eq_mul]
        ring

end decay

/-- `D_0 = 8` and `D_j = 6E_j/(2π)^j` for `j ≥ 1`. -/
def Dfb (j : ℕ) : ℝ := if j = 0 then 8 else 6 * Ej j / (2 * π) ^ j

/-- **The decay premise of round 662's `CGLP81` for their `f_b`**: for `L, X > 0`, `T ≥ 1`, points `|t_i| ≤ T` and
`L ≤ XT`, some value `f_{b₀}(u₀)` has `Σ_b|f̂_b(ξ)| ≤ D_j(T/|ξ|)^jφ(q)f_{b₀}(u₀)` for every `j` and `ξ ≠ 0`. -/
theorem fb_decay_all {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {X M₂ T : ℝ} (hL : 0 < N * M₂ / q) (hX : 0 < X) (hT : 1 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T)
    (hLX : N * M₂ / q ≤ X * T) : ∃ (b₀ : (ZMod q)ˣ) (u₀ : ℝ), ∀ (j : ℕ) (ξ : ℝ), ξ ≠ 0 →
      ∑ b, ‖𝓕 (fun u : ℝ => (fb N R χ t X M₂ b u : ℂ)) ξ‖ ≤
        Dfb j * (T / |ξ|) ^ j * q.totient * fb N R χ t X M₂ b₀ u₀ := by
  obtain ⟨b₀, u₀, hmax⟩ := exists_max (f := fb N R χ t X M₂) (fun b => (contDiff_fb R χ t hL hX b).continuous)
    (fun b u => fb_nonneg R χ t b u) (A := 4) (fun b _u hu => fb_eq_zero R χ t b hu)
  refine ⟨b₀, u₀, fun j ξ hξ => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Dfb, ite_eq_left rfl, pow_zero, mul_one]
    calc ∑ b, ‖𝓕 (fun u : ℝ => (fb N R χ t X M₂ b u : ℂ)) ξ‖
        ≤ ∑ _b : (ZMod q)ˣ, 8 * fb N R χ t X M₂ b₀ u₀ := by
          refine Finset.sum_le_sum fun b _ => ?_
          calc ‖𝓕 (fun u : ℝ => (fb N R χ t X M₂ b u : ℂ)) ξ‖ ≤ ∫ u, ‖(fb N R χ t X M₂ b u : ℂ)‖ :=
                VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
            _ = ∫ u, fb N R χ t X M₂ b u := by
                congr 1
                funext u
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fb_nonneg R χ t b u)]
            _ ≤ 8 * fb N R χ t X M₂ b₀ u₀ := integral_fb_le R χ t hL hX b (hmax b)
      _ = 8 * (q.totient : ℝ) * fb N R χ t X M₂ b₀ u₀ := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
          ring
  · rw [Dfb, ite_eq_right hj.ne']
    refine (fb_decay R χ t hL hX hT ht hLX hj hξ).trans (mul_le_mul_of_nonneg_left (hmax (-1) 1) ?_)
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Ej_nonneg j)) (by positivity))
      (by positivity)) (Nat.cast_nonneg _)

end LinnikCGLDecay

#print axioms LinnikCGLDecay.fourier_fb_eq
#print axioms LinnikCGLDecay.sum_pow_mul_norm_fourier_fb_le
#print axioms LinnikCGLDecay.Bj_le
#print axioms LinnikCGLDecay.fb_decay
#print axioms LinnikCGLDecay.fb_decay_all
