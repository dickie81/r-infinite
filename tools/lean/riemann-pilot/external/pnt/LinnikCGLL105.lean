/-
# Round 669: their Lemma 10.5, the energy by the third moment of `R` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Lemma 10.5: "E(W) ⪅ N^{−2σ} Σ_{n₁,n₂∼N, (n₁n₂,q)=1} |R(n₁/n₂, n₁n₂^{−1})|³," (text layer lines 4687–4698; spaces
restored; the sum, fraction, large bars, large parentheses, subscripts and exponents transcribed). Their proof bounds
each quadruple of the energy by `N^{−2σ}|D_N(t₄, χ₄)|²` (the large values), replaces `|D_N(t₄, χ₄)|²` by its average
near `t₁ + t₂ − t₃` (their Lemma 10.4), notes that "given (t_i,χ_i) ∈ W for 1 ≤ i ≤ 3, there exists at most one choice
of (t₄,χ₄) ∈ W such that |t₁+t₂−t₃−t₄| ≤ 1 and χ₁χ₂ = χ₃χ₄" (lines 4716–4718; spaces restored, the subscripts
transcribed), and expands the square over the triples.

The stack's form, at one point per character. For a coefficient function `c`, `D_c(t) = Σ_{n∈S}c(n)n^{it}` (`Dp`).
* `Dp` is a finite exponential sum with frequencies `log n`; for `S ⊆ [N, 2N]` they lie within `1` of `log N`, so round
  668 gives `|D_c(t)|² ≤ ∫|k(ξ)||D_c(t + πξ)|² dξ`. The weight is shifted, not the window: for `|τ − t| ≤ 1`,
  `|D_c(t)|² ≤ ∫κ(ξ)|D_c(τ + πξ)|² dξ` with `κ(ξ) = 4C_k/(1 + ξ²)` (`kmaj`), since `(1 + ξ²)|k(ξ)| ≤ C_k` and
  `1 + ξ² ≤ 4(1 + (ξ + η)²)` for `|η| ≤ 1`.
* The fourth point is not inverted: if `χ_iχ_j = χ_kχ_l` then `χ_l(n) = χ_i(n)χ_j(n)χ̄_k(n)` for every `n`
  (`char_eq_of_mul_eq`), so `D_N(·, χ_l)` is `D_c` with `c(n) = b_nχ_i(n)χ_j(n)χ̄_k(n)`, a function of the triple.
* With `R₂(n₁, n₂) = Σ_iχ_i(n₁)χ̄_i(n₂)e^{it_i(log n₁ − log n₂)}` (`R2`), which is their `R(n₁/n₂, n₁n₂⁻¹)` when
  `(n₁n₂, q) = 1` and `0` otherwise, the sum over the triples of `|D_c(t_i + t_j − t_k + y)|²` is
  `Σ_{n₁,n₂}b_{n₁}b̄_{n₂}e^{iy(log n₁ − log n₂)}R₂²R̄₂` (`sum_triple_eq`), at most `Σ_{n₁,n₂}|R₂|³` for `|b_n| ≤ 1`.

Plain statements, with `S` a finite set of naturals in `[N, 2N]`, `N > 0`.
* `norm_kloc_shift_le`: for `|η| ≤ 1`, `|k(ξ + η)| ≤ κ(ξ)`.
* `norm_sq_Dp_le_shift`: for `|τ − t| ≤ 1`, `|D_c(t)|² ≤ ∫κ(ξ)|D_c(τ + πξ)|² dξ`.
* `sum_triple_le`: for `|b_n| ≤ 1`, `Σ_{i,j,k∈R}|D_{c_{ijk}}(t_i + t_j − t_k + y)|² ≤ Σ_{n₁,n₂∈S}|R₂(n₁, n₂)|³`.
* `lemma105`: for `χ` injective on `R`, `|b_n| ≤ 1` and `|D_N(t_i, χ_i)| ≥ N^σ/6` on `R`,
  `E ≤ 36(N^σ)^{−2}∫κ·Σ_{n₁,n₂∈S}|R₂(n₁, n₂)|³`.

* `Ck`, `norm_kloc_mul_le`, `Ck_nonneg`, `kmaj`, `kmaj_nonneg`, `integrable_kmaj`, `norm_kloc_shift_le`: the
  majorant.
* `Dp`, `Dp_eq_esum`, `norm_Dp_le`, `continuous_Dp`, `norm_sq_Dp_le`, `norm_sq_Dp_le_shift`: Dirichlet polynomials.
* `char_eq_of_mul_eq`, `R2`, `sum3_comm`, `ct`, `sum_triple_eq`, `sum_triple_le`: the triples.
* `lemma105`: their Lemma 10.5.

The file imports `LinnikCGLLoc.lean`.
-/

import LinnikCGLLoc

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLL105

open LinnikCGLRt LinnikCGLMom4 LinnikCGLLoc

/-! ### The majorant of the shifted kernel -/

/-- `C_k = ∫ψ̃₀ + D₂/(4π²)`. -/
def Ck : ℝ := (∫ x, psi0 x) + Dpsi 2 / (4 * π ^ 2)

/-- `(1 + ξ²)|k(ξ)| ≤ C_k`. -/
lemma norm_kloc_mul_le (ξ : ℝ) : (1 + ξ ^ 2) * ‖kloc ξ‖ ≤ Ck := by
  have h0 : ‖kloc ξ‖ ≤ ∫ x, psi0 x := norm_fourier_psiC_le ξ
  have h2 : (2 * π * |ξ|) ^ 2 * ‖kloc ξ‖ ≤ Dpsi 2 := fourier_psiC_decay 2 ξ
  have hsq : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * ξ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hsq] at h2
  have hpi : 0 < 4 * π ^ 2 := by positivity
  have h2' : ξ ^ 2 * ‖kloc ξ‖ ≤ Dpsi 2 / (4 * π ^ 2) := by
    rw [le_div_iff₀ hpi]
    nlinarith [norm_nonneg (kloc ξ)]
  unfold Ck
  nlinarith

/-- The majorant `κ(ξ) = 4C_k/(1 + ξ²)`. -/
def kmaj (ξ : ℝ) : ℝ := 4 * Ck / (1 + ξ ^ 2)

lemma Ck_nonneg : 0 ≤ Ck := (mul_nonneg (by positivity) (norm_nonneg (kloc 0))).trans (norm_kloc_mul_le 0)

lemma kmaj_nonneg (ξ : ℝ) : 0 ≤ kmaj ξ := div_nonneg (mul_nonneg (by norm_num) Ck_nonneg) (by positivity)

lemma integrable_kmaj : Integrable kmaj := by
  have e : kmaj = fun ξ => 4 * Ck * (1 + ξ ^ 2)⁻¹ := funext fun ξ => by unfold kmaj; rw [div_eq_mul_inv]
  rw [e]
  exact integrable_inv_one_add_sq.const_mul _

/-- For `|η| ≤ 1`, `|k(ξ + η)| ≤ κ(ξ)`: `1 + ξ² ≤ 4(1 + (ξ + η)²)`. -/
lemma norm_kloc_shift_le {η : ℝ} (hη : |η| ≤ 1) (ξ : ℝ) : ‖kloc (ξ + η)‖ ≤ kmaj ξ := by
  have h1 := norm_kloc_mul_le (ξ + η)
  have hη2 : η ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg η]
  have hpeetre : 1 + ξ ^ 2 ≤ 4 * (1 + (ξ + η) ^ 2) := by nlinarith [sq_nonneg (ξ + 2 * η), sq_nonneg η]
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  have hpos' : 0 < 1 + (ξ + η) ^ 2 := by positivity
  unfold kmaj
  rw [le_div_iff₀ hpos]
  have hk := norm_nonneg (kloc (ξ + η))
  nlinarith

/-! ### Dirichlet polynomials -/

/-- `D_c(t) = Σ_{n∈S}c(n)n^{it}`. -/
def Dp (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ := ∑ n ∈ S, c n * (n : ℂ) ^ ((t : ℂ) * I)

section Dp

variable (S : Finset ℕ) (c : ℕ → ℂ)

lemma Dp_eq_esum (hS : ∀ n ∈ S, 0 < n) (t : ℝ) : Dp S c t = esum S c (fun n => Real.log n) t := by
  unfold Dp esum
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 2
  push_cast
  ring

lemma norm_Dp_le (t : ℝ) : ‖Dp S c t‖ ≤ ∑ n ∈ S, ‖c n‖ := by
  unfold Dp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · by_cases ht : (t : ℂ) * I = 0
    · rw [ht, Complex.cpow_zero, norm_one]
    · rw [Nat.cast_zero, Complex.zero_cpow ht, norm_zero]; norm_num
  · rw [Complex.norm_natCast_cpow_of_pos hn]
    simp

lemma continuous_Dp (hS : ∀ n ∈ S, 0 < n) : Continuous (Dp S c) := by
  have e : Dp S c = esum S c (fun n => Real.log n) := funext fun t => Dp_eq_esum S c hS t
  rw [e]
  exact continuous_esum S c _

/-- `|D_c(t)|² ≤ ∫|k(ξ)||D_c(t + πξ)|² dξ` for `S ⊆ [N, 2N]`. -/
lemma norm_sq_Dp_le {N : ℝ} (hN : 0 < N) (hS : ∀ n ∈ S, N ≤ n ∧ (n : ℝ) ≤ 2 * N) (t : ℝ) :
    ‖Dp S c t‖ ^ 2 ≤ ∫ ξ, ‖kloc ξ‖ * ‖Dp S c (t + π * ξ)‖ ^ 2 := by
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => by
    have := (hS n hn).1
    exact_mod_cast (hN.trans_le this)
  have hlam : ∀ n ∈ S, |Real.log n - Real.log N| ≤ 1 := by
    intro n hn
    have h1 := (hS n hn).1
    have h2 := (hS n hn).2
    have hn0 : (0 : ℝ) < n := hN.trans_le h1
    rw [← Real.log_div hn0.ne' hN.ne', abs_of_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hN]; linarith))]
    have h3 : (n : ℝ) / N ≤ 2 := by rw [div_le_iff₀ hN]; linarith
    have h4 : Real.log ((n : ℝ) / N) ≤ Real.log 2 := Real.log_le_log (by positivity) h3
    have h5 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have h := norm_sq_esum_le S c (fun n => Real.log n) (Λ := Real.log N) (by norm_num : (0 : ℝ) < 1) hlam t
  rw [Dp_eq_esum S c hpos t]
  refine h.trans (le_of_eq ?_)
  congr 1
  funext ξ
  rw [Dp_eq_esum S c hpos, div_one]

/-- **The shifted local average**: for `S ⊆ [N, 2N]` and `|τ − t| ≤ 1`, `|D_c(t)|² ≤ ∫κ(ξ)|D_c(τ + πξ)|² dξ`. -/
theorem norm_sq_Dp_le_shift {N : ℝ} (hN : 0 < N) (hS : ∀ n ∈ S, N ≤ n ∧ (n : ℝ) ≤ 2 * N) {t τ : ℝ}
    (hτ : |τ - t| ≤ 1) : ‖Dp S c t‖ ^ 2 ≤ ∫ ξ, kmaj ξ * ‖Dp S c (τ + π * ξ)‖ ^ 2 := by
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => by
    have := (hS n hn).1
    exact_mod_cast (hN.trans_le this)
  set δ := (τ - t) / π with hδ
  have hδ1 : |δ| ≤ 1 := by
    rw [hδ, abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hC := continuous_Dp S c hpos
  have hB : ∀ y, ‖Dp S c y‖ ^ 2 ≤ (∑ n ∈ S, ‖c n‖) ^ 2 := fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_Dp_le S c y) 2
  have e1 : ∫ ξ, ‖kloc ξ‖ * ‖Dp S c (t + π * ξ)‖ ^ 2 =
      ∫ ξ, ‖kloc (ξ + δ)‖ * ‖Dp S c (τ + π * ξ)‖ ^ 2 := by
    rw [← integral_add_right_eq_self (fun ξ => ‖kloc ξ‖ * ‖Dp S c (t + π * ξ)‖ ^ 2) δ]
    congr 1
    funext ξ
    have : t + π * (ξ + δ) = τ + π * ξ := by rw [hδ]; field_simp; ring
    rw [this]
  have hint : Integrable fun ξ => kmaj ξ * ‖Dp S c (τ + π * ξ)‖ ^ 2 := by
    refine (integrable_kmaj.mul_const ((∑ n ∈ S, ‖c n‖) ^ 2)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (continuous_const.div (by fun_prop) (fun ξ => by positivity) |>.mul
        ((hC.comp (by fun_prop)).norm.pow 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kmaj_nonneg ξ) (by positivity))]
      exact mul_le_mul_of_nonneg_left (hB _) (kmaj_nonneg ξ)
  calc ‖Dp S c t‖ ^ 2 ≤ ∫ ξ, ‖kloc ξ‖ * ‖Dp S c (t + π * ξ)‖ ^ 2 := norm_sq_Dp_le S c hN hS t
    _ = ∫ ξ, ‖kloc (ξ + δ)‖ * ‖Dp S c (τ + π * ξ)‖ ^ 2 := e1
    _ ≤ ∫ ξ, kmaj ξ * ‖Dp S c (τ + π * ξ)‖ ^ 2 := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity) hint
          (Eventually.of_forall fun ξ => ?_)
        exact mul_le_mul_of_nonneg_right (norm_kloc_shift_le hδ1 ξ) (by positivity)

end Dp

/-! ### The triples -/

/-- If `χ_iχ_j = χ_kχ_l` then `χ_l(n) = χ_i(n)χ_j(n)χ̄_k(n)` for every `n`. -/
lemma char_eq_of_mul_eq {q : ℕ} {χi χj χk χl : DirichletCharacter ℂ q} (h : χi * χj = χk * χl) (n : ℕ) :
    χl n = χi n * χj n * conj (χk n) := by
  by_cases hn : IsUnit (n : ZMod q)
  · have h1 : ‖χk n‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one χk hn.unit
      rwa [IsUnit.unit_spec] at this
    have h2 : χk n * χl n = χi n * χj n := by
      have := congrArg (fun ψ : DirichletCharacter ℂ q => ψ n) h
      simp only [MulChar.mul_apply] at this
      exact this.symm
    have hc : conj (χk n) * χk n = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
      norm_num
    calc χl n = conj (χk n) * χk n * χl n := by rw [hc, one_mul]
      _ = conj (χk n) * (χk n * χl n) := by ring
      _ = χi n * χj n * conj (χk n) := by rw [h2]; ring
  · rw [MulChar.map_nonunit _ hn, MulChar.map_nonunit _ hn, zero_mul, zero_mul]

/-- `R₂(n₁, n₂) = Σ_iχ_i(n₁)χ̄_i(n₂)e^{it_i(log n₁ − log n₂)}`, their `R(n₁/n₂, n₁n₂⁻¹)` for `(n₁n₂, q) = 1`. -/
def R2 {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (n₁ n₂ : ℕ) : ℂ :=
  ∑ i ∈ R, χ i n₁ * conj (χ i n₂) * cexp (↑(t i * (Real.log n₁ - Real.log n₂)) * I)

section triples

variable {ι : Type*} {q : ℕ} (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (S : Finset ℕ)
  (b : ℕ → ℂ)

/-- `Σ_iΣ_jΣ_k f(i, j, k) = Σ_kΣ_jΣ_i f(i, j, k)`. -/
lemma sum3_comm {κ : Type*} (s : Finset κ) (f : κ → κ → κ → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k = ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, f i j k := by
  calc ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k = ∑ i ∈ s, ∑ k ∈ s, ∑ j ∈ s, f i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i ∈ s, ∑ j ∈ s, f i j k := Finset.sum_comm
    _ = ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, f i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- The coefficients of the triple `(i, j, k)`: `c(n) = b_nχ_i(n)χ_j(n)χ̄_k(n)`. -/
def ct (i j k : ι) (n : ℕ) : ℂ := b n * (χ i n * χ j n * conj (χ k n))

/-- **The sum over the triples**: `Σ_{i,j,k}|D_{c_{ijk}}(t_i + t_j − t_k + y)|² =
Σ_{n₁,n₂}b_{n₁}b̄_{n₂}e^{iy(log n₁ − log n₂)}R₂(n₁, n₂)²R̄₂(n₁, n₂)`, for `S` of positive integers. -/
theorem sum_triple_eq (hS : ∀ n ∈ S, 0 < n) (y : ℝ) :
    ((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ‖Dp S (ct χ b i j k) (t i + t j - t k + y)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, b n₁ * conj (b n₂) * cexp (↑(y * (Real.log n₁ - Real.log n₂)) * I) *
        (R2 R χ t n₁ n₂ ^ 2 * conj (R2 R χ t n₁ n₂)) := by
  -- each `|D|²` as a double sum over `S`
  have hD : ∀ i j k, (‖Dp S (ct χ b i j k) (t i + t j - t k + y)‖ : ℂ) ^ 2 =
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, b n₁ * conj (b n₂) * cexp (↑(y * (Real.log n₁ - Real.log n₂)) * I) *
        ((χ i n₁ * conj (χ i n₂) * cexp (↑(t i * (Real.log n₁ - Real.log n₂)) * I)) *
          (χ j n₁ * conj (χ j n₂) * cexp (↑(t j * (Real.log n₁ - Real.log n₂)) * I)) *
          conj (χ k n₁ * conj (χ k n₂) * cexp (↑(t k * (Real.log n₁ - Real.log n₂)) * I))) := by
    intro i j k
    have ec : ∀ a : ℝ, conj (cexp (↑a * I)) = cexp (↑(-a) * I) := fun a => by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_ofReal]
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Dp_eq_esum S _ hS]
    unfold esum
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    unfold ct
    simp only [map_mul, Complex.conj_conj, ec]
    set L := Real.log n₁ - Real.log n₂ with hL
    have hexp : cexp (↑(Real.log n₁ * (t i + t j - t k + y)) * I) *
        cexp (↑(-(Real.log n₂ * (t i + t j - t k + y))) * I) =
        cexp (↑(y * L) * I) * cexp (↑(t i * L) * I) * cexp (↑(t j * L) * I) * cexp (↑(-(t k * L)) * I) := by
      simp only [← Complex.exp_add]
      congr 1
      rw [hL]
      push_cast
      ring
    calc b n₁ * (χ i n₁ * χ j n₁ * conj (χ k n₁)) * cexp (↑(Real.log n₁ * (t i + t j - t k + y)) * I) *
          (conj (b n₂) * (conj (χ i n₂) * conj (χ j n₂) * χ k n₂) *
            cexp (↑(-(Real.log n₂ * (t i + t j - t k + y))) * I))
        = b n₁ * conj (b n₂) * (χ i n₁ * conj (χ i n₂)) * (χ j n₁ * conj (χ j n₂)) * (conj (χ k n₁) * χ k n₂) *
            (cexp (↑(Real.log n₁ * (t i + t j - t k + y)) * I) *
              cexp (↑(-(Real.log n₂ * (t i + t j - t k + y))) * I)) := by ring
      _ = b n₁ * conj (b n₂) * (χ i n₁ * conj (χ i n₂)) * (χ j n₁ * conj (χ j n₂)) * (conj (χ k n₁) * χ k n₂) *
            (cexp (↑(y * L) * I) * cexp (↑(t i * L) * I) * cexp (↑(t j * L) * I) * cexp (↑(-(t k * L)) * I)) := by
          rw [hexp]
      _ = _ := by ring
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  simp_rw [hD]
  simp_rw [Finset.sum_comm (s := R) (t := S)]
  refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
  unfold R2
  rw [map_sum]
  simp only [sq, Finset.sum_mul, Finset.mul_sum]
  exact sum3_comm R _

/-- **The triples bounded**: for `|b_n| ≤ 1`,
`Σ_{i,j,k}|D_{c_{ijk}}(t_i + t_j − t_k + y)|² ≤ Σ_{n₁,n₂∈S}|R₂(n₁, n₂)|³`. -/
theorem sum_triple_le (hS : ∀ n ∈ S, 0 < n) (hb : ∀ n, ‖b n‖ ≤ 1) (y : ℝ) :
    ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ‖Dp S (ct χ b i j k) (t i + t j - t k + y)‖ ^ 2 ≤
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 3 := by
  have h := congrArg norm (sum_triple_eq R χ t S b hS y)
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  refine (le_abs_self _).trans (h.le.trans ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n₁ _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun n₂ _ => ?_))
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_conj,
    Complex.norm_conj, norm_pow, mul_one]
  have h1 := hb n₁
  have h2 := hb n₂
  have h3 : 0 ≤ ‖R2 R χ t n₁ n₂‖ ^ 2 * ‖R2 R χ t n₁ n₂‖ := by positivity
  calc ‖b n₁‖ * ‖b n₂‖ * (‖R2 R χ t n₁ n₂‖ ^ 2 * ‖R2 R χ t n₁ n₂‖)
      ≤ 1 * 1 * (‖R2 R χ t n₁ n₂‖ ^ 2 * ‖R2 R χ t n₁ n₂‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
    _ = ‖R2 R χ t n₁ n₂‖ ^ 3 := by ring

end triples

/-! ### Their Lemma 10.5 -/

/-- **Their Lemma 10.5, at one point per character**: for `χ` injective on `R`, `S ⊆ [N, 2N]` with `N > 0`,
`|b_n| ≤ 1` and `|Σ_{n∈S}b_nχ_i(n)n^{it_i}| ≥ N^σ/6` for `i ∈ R`, `E ≤ 36(N^σ)^{−2}∫κ·Σ_{n₁,n₂∈S}|R₂(n₁, n₂)|³`. -/
theorem lemma105 {ι : Type*} {q : ℕ} {R : Finset ι} {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R)
    (t : ι → ℝ) {S : Finset ℕ} {b : ℕ → ℂ} {N σ : ℝ} (hN : 0 < N) (hS : ∀ n ∈ S, N ≤ n ∧ (n : ℝ) ≤ 2 * N)
    (hb : ∀ n, ‖b n‖ ≤ 1)
    (hbig : ∀ i ∈ R, N ^ σ / 6 ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) :
    (energy R χ t : ℝ) ≤ 36 / (N ^ σ) ^ 2 * (∫ ξ, kmaj ξ) * ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 3 := by
  classical
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => by
    have := (hS n hn).1
    exact_mod_cast (hN.trans_le this)
  have hNσ : 0 < N ^ σ := Real.rpow_pos_of_pos hN σ
  set A := 36 / (N ^ σ) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  -- the large values: `1 ≤ A|D_l(t_l)|²`
  have hone : ∀ l ∈ R, 1 ≤ A * ‖Dp S (fun n => b n * χ l n) (t l)‖ ^ 2 := by
    intro l hl
    have h := hbig l hl
    have hD : ∑ n ∈ S, b n * χ l n * (n : ℂ) ^ ((t l : ℂ) * I) = Dp S (fun n => b n * χ l n) (t l) := rfl
    rw [hD] at h
    have h2 : (N ^ σ / 6) ^ 2 ≤ ‖Dp S (fun n => b n * χ l n) (t l)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    rw [hA, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- the energy as a sum over the quadruples
  set Q : ι × ι × ι × ι → Prop := fun p =>
    |t p.1 + t p.2.1 - t p.2.2.1 - t p.2.2.2| ≤ 1 ∧ χ p.1 * χ p.2.1 = χ p.2.2.1 * χ p.2.2.2 with hQ
  have hE : (energy R χ t : ℝ) = ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R, if Q (i, j, k, l) then (1 : ℝ) else 0 := by
    unfold energy
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_product, Finset.sum_congr rfl fun i _ => Finset.sum_product _ _ _]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_product]
  -- for each triple, at most one `l`, and its term is at most the shifted local average
  have htriple : ∀ i ∈ R, ∀ j ∈ R, ∀ k ∈ R, ∑ l ∈ R, (if Q (i, j, k, l) then (1 : ℝ) else 0) ≤
      A * ∫ ξ, kmaj ξ * ‖Dp S (ct χ b i j k) (t i + t j - t k + π * ξ)‖ ^ 2 := by
    intro i _ j _ k _
    have hI0 : 0 ≤ ∫ ξ, kmaj ξ * ‖Dp S (ct χ b i j k) (t i + t j - t k + π * ξ)‖ ^ 2 :=
      integral_nonneg fun ξ => mul_nonneg (kmaj_nonneg ξ) (by positivity)
    rw [← Finset.sum_filter]
    have hcard : (R.filter fun l => Q (i, j, k, l)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro l hl l' hl'
      rw [Finset.mem_filter] at hl hl'
      have h1 := hl.2.2
      have h2 := hl'.2.2
      rw [h1] at h2
      exact hinj hl.1 hl'.1 (mul_left_cancel h2)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]
      exact mul_nonneg hA0 hI0
    · obtain ⟨l, hl⟩ := Finset.card_eq_one.mp h1
      rw [hl, Finset.sum_singleton]
      have hlm : l ∈ R.filter fun l => Q (i, j, k, l) := by rw [hl]; exact Finset.mem_singleton_self l
      rw [Finset.mem_filter] at hlm
      have hcoef : (fun n => b n * χ l n) = ct χ b i j k := by
        funext n
        unfold ct
        rw [char_eq_of_mul_eq hlm.2.2 n]
      have hτ : |(t i + t j - t k) - t l| ≤ 1 := by
        have := hlm.2.1
        rwa [show t i + t j - t k - t l = t i + t j - t k - t l from rfl] at this
      have hshift := norm_sq_Dp_le_shift S (ct χ b i j k) hN hS hτ
      calc (1 : ℝ) ≤ A * ‖Dp S (fun n => b n * χ l n) (t l)‖ ^ 2 := hone l hlm.1
        _ = A * ‖Dp S (ct χ b i j k) (t l)‖ ^ 2 := by rw [hcoef]
        _ ≤ A * ∫ ξ, kmaj ξ * ‖Dp S (ct χ b i j k) (t i + t j - t k + π * ξ)‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hshift hA0
  -- integrability of each triple's integrand
  have hB : ∀ i j k, ∀ y, ‖Dp S (ct χ b i j k) y‖ ^ 2 ≤ (∑ n ∈ S, ‖ct χ b i j k n‖) ^ 2 := fun i j k y =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_Dp_le S _ y) 2
  have hint : ∀ i j k, Integrable fun ξ => kmaj ξ * ‖Dp S (ct χ b i j k) (t i + t j - t k + π * ξ)‖ ^ 2 := by
    intro i j k
    refine (integrable_kmaj.mul_const ((∑ n ∈ S, ‖ct χ b i j k n‖) ^ 2)).mono' ?_
      (Eventually.of_forall fun ξ => ?_)
    · have hC := continuous_Dp S (ct χ b i j k) hpos
      exact (continuous_const.div (by fun_prop) (fun ξ => by positivity) |>.mul
        ((hC.comp (by fun_prop)).norm.pow 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kmaj_nonneg ξ) (by positivity))]
      exact mul_le_mul_of_nonneg_left (hB i j k _) (kmaj_nonneg ξ)
  -- assemble
  set W := ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖R2 R χ t n₁ n₂‖ ^ 3 with hW
  rw [hE]
  calc ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ l ∈ R, (if Q (i, j, k, l) then (1 : ℝ) else 0)
      ≤ ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          A * ∫ ξ, kmaj ξ * ‖Dp S (ct χ b i j k) (t i + t j - t k + π * ξ)‖ ^ 2 :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk =>
          htriple i hi j hj k hk
    _ = A * ∫ ξ, kmaj ξ * ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
          ‖Dp S (ct χ b i j k) (t i + t j - t k + π * ξ)‖ ^ 2 := by
        simp_rw [← Finset.mul_sum]
        congr 1
        symm
        simp_rw [Finset.mul_sum]
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
          hint i j k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint i j k]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun k _ => hint i j k]
    _ ≤ A * ∫ ξ, kmaj ξ * W := by
        refine mul_le_mul_of_nonneg_left ?_ hA0
        refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => mul_nonneg (kmaj_nonneg ξ)
          (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity))
          (integrable_kmaj.mul_const W) (Eventually.of_forall fun ξ => ?_)
        exact mul_le_mul_of_nonneg_left (sum_triple_le R χ t S b hpos hb (π * ξ)) (kmaj_nonneg ξ)
    _ = A * (∫ ξ, kmaj ξ) * W := by rw [integral_mul_const, mul_assoc]

end LinnikCGLL105

#print axioms LinnikCGLL105.norm_sq_Dp_le_shift
#print axioms LinnikCGLL105.sum_triple_eq
#print axioms LinnikCGLL105.sum_triple_le
#print axioms LinnikCGLL105.lemma105
