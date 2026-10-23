/-
# Round 650: the truncation in `m` and their `I′_{m⃗}` (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li's §7 truncates the frequencies: "By Lemma 4.3 (1), we have |ĥ_t(ξ)| ≪_j (1 + |t|)^j/|ξ|^j. This
implies that I_{m⃗} is negligible unless |m_i| ≤ (qT)^ϵqT/N for 1 ≤ i ≤ 3" (text layer lines 1962–1963; spaces
restored, the exponents and subscripts transcribed). They then bound `S₃` through `I′_{m⃗}`, the sum over all triples
of points. Round 649 dropped the condition "not all equal"; this file truncates each `F(i, k)` at `0 < |m| ≤ M` and
expands the truncated cubic trace as `Σ_{0<|m_i|≤M}I′(m⃗)`, with an explicit error.

The tail. For `|m| > M ≥ 1` and `K ≥ 2`, round 645's Lemma 4.3 (1) at `K` gives
`|(N/q)ĥ_τ(Nm/q)| ≤ (N/q)CF(K)ρ^K|m|^{−K} ≤ (N/q)CF(K)ρ^K M^{2−K}|m|^{−2}`, with `ρ = q(1 + |τ|)/(2πN)`. Summed over
`|m| > M` and the `q` residues (`|χ_i(a)conj(χ_k(a))| ≤ 1`), `|F(i, k) − F_M(i, k)| ≤ N·CF(K)ρ^K M^{2−K}Z₂`, with round
649's `Z₂ = Σ_{m≠0}|m|^{−2}`. With `|F(i, k)| = |E′(i, k)| ≤ |G(i, k)| + μ₀ ≤ 2N + 1`, for round 648's
`E′(i, k) = G(i, k) − δ_{ik}μ₀`, each product of three entries moves by at most `3τ_M(2N + 1 + τ_M)²`. Taking `M` near
their `(qT)^ϵqT/N` makes `ρ/M` a negative power of `qT`, and a large `K` then makes the error negligible; the choice is
left to the assembly.

Plain statement (`S3_trunc`). For `q ≥ 1`, `N > 0`, `χ` injective on `R`, points `|t_i| ≤ T`, `M ≥ 1` and `K ≥ 2`,
`|S₃ − (Re Σ_{0<|m₁|,|m₂|,|m₃|≤M}I′(m⃗) − |R|(μ − μ₀)³)| ≤ 3|R|³τ_M(2N + 1 + τ_M)²`, where
`I′(m⃗) = Σ_{i,j,k∈R}φ_{ij}(m₁)φ_{jk}(m₂)φ_{ki}(m₃)`,
`φ_{ik}(m) = Σ_{a<q}χ_i(a)conj(χ_k(a))(N/q)ĥ_{t_i−t_k}(Nm/q)e^{2πima/q}` and
`τ_M = N·CF(K)(q(1 + 2T)/(2πN))^K M^{2−K}Z₂`.

* `phi`, `boxM`, `FmT`, `Ip`, `swap13`, `sum_FmT_cube`: the terms, the truncated entries
  `F_M(i, k) = Σ_{0<|m|≤M}φ_{ik}(m)`, their `I′`, and `Σ_{i,j,k}F_M(i, j)F_M(j, k)F_M(k, i) = Σ_{0<|m_i|≤M}I′(m⃗)`.
* `mul_le_one_of`, `norm_coef_le`, `norm_tail_term_le`, `tsum_ite_sub_sum`, `not_mem_boxM`, `norm_Fm_sub_FmT_le`:
  the tail.
* `norm_entP_le`, `norm_gramP_le`, `norm_Fm_le`: `|F(i, k)| ≤ 2N + 1` (round 648's `Em_eq`, round 639's `mu0_le`).
* `norm_cube_sub_le`, `tauM`, `S3_trunc`: the error of the truncated cubic trace.

The file imports `LinnikCGLDiag.lean`.
-/

import LinnikCGLDiag

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLTrunc

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace LinnikCGLDiag

/-! ### The terms `φ_{ik}(m)` and their `I′_{m⃗}` -/

/-- The term `m` of a Gram entry's expansion, summed over the residues:
`φ_{ik}(m) = Σ_{a<q}χ_i(a)conj(χ_k(a))(N/q)ĥ_{t_i−t_k}(Nm/q)e^{2πima/q}`. -/
def phi {ι : Type*} {q : ℕ} (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) (m : ℤ) : ℂ :=
  ∑ a ∈ Finset.range q, (χ i a * star (χ k a)) *
    (((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) * Complex.exp (2 * π * I * m * (a / q)))

/-- The frequencies `0 < |m| ≤ M`. -/
def boxM (M : ℕ) : Finset ℤ := (Finset.Icc (-(M : ℤ)) M).erase 0

/-- A Gram entry's terms `0 < |m| ≤ M`: `F_M(i, k) = Σ_{0<|m|≤M}φ_{ik}(m)`. -/
def FmT {ι : Type*} {q : ℕ} (M : ℕ) (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i k : ι) : ℂ :=
  ∑ m ∈ boxM M, phi N χ t i k m

/-- **Their `I′_{m⃗}`** at one point per character, a sum over all triples of points:
`I′(m₁, m₂, m₃) = Σ_{i,j,k∈R}φ_{ij}(m₁)φ_{jk}(m₂)φ_{ki}(m₃)`. -/
def Ip {ι : Type*} {q : ℕ} (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (m₁ m₂ m₃ : ℤ) : ℂ :=
  ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, phi N χ t i j m₁ * phi N χ t j k m₂ * phi N χ t k i m₃

lemma swap13 {α β : Type*} (A : Finset α) (B : Finset β) (g : α → β → β → β → ℂ) :
    ∑ k ∈ A, ∑ x ∈ B, ∑ y ∈ B, ∑ z ∈ B, g k x y z = ∑ x ∈ B, ∑ y ∈ B, ∑ z ∈ B, ∑ k ∈ A, g k x y z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]

/-- **The truncated cubic trace as a sum of their `I′`**:
`Σ_{i,j,k∈R}F_M(i, j)F_M(j, k)F_M(k, i) = Σ_{0<|m₁|,|m₂|,|m₃|≤M}I′(m₁, m₂, m₃)`. -/
theorem sum_FmT_cube {ι : Type*} {q : ℕ} (M : ℕ) (N : ℝ) (R : Finset ι) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) :
    ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i =
      ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, Ip N R χ t m₁ m₂ m₃ := by
  have expand : ∀ i j k, FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i =
      ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
        phi N χ t i j m₁ * phi N χ t j k m₂ * phi N χ t k i m₃ := by
    intro i j k
    unfold FmT
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [Finset.mul_sum]
  simp only [expand]
  unfold Ip
  calc ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M,
        phi N χ t i j m₁ * phi N χ t j k m₂ * phi N χ t k i m₃
      = ∑ i ∈ R, ∑ j ∈ R, ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, ∑ k ∈ R,
        phi N χ t i j m₁ * phi N χ t j k m₂ * phi N χ t k i m₃ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => swap13 R (boxM M) _
    _ = ∑ i ∈ R, ∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, ∑ j ∈ R, ∑ k ∈ R,
        phi N χ t i j m₁ * phi N χ t j k m₂ * phi N χ t k i m₃ :=
        Finset.sum_congr rfl fun i _ => swap13 R (boxM M) _
    _ = _ := swap13 R (boxM M) _

/-! ### The tail beyond `M` -/

lemma mul_le_one_of {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 := by
  nlinarith [mul_nonneg (sub_nonneg.2 ha) hb0]

lemma norm_coef_le {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (a : ℕ) : ‖χ a * star (ψ a)‖ ≤ 1 := by
  rw [norm_mul, norm_star]
  exact mul_le_one_of (DirichletCharacter.norm_le_one χ _) (norm_nonneg _) (DirichletCharacter.norm_le_one ψ _)

/-- **A term beyond `M`**: for `N > 0`, `|m| > M ≥ 1` and `K ≥ 2`,
`‖(N/q)ĥ_τ(Nm/q)e^{2πima/q}‖ ≤ (N/q)CF(K)ρ^K M^{2−K}|m|^{−2}`, with `ρ = q(1 + |τ|)/(2πN)` (round 645's `lemma43`). -/
lemma norm_tail_term_le (τ : ℝ) {N : ℝ} (hN : 0 < N) {q : ℕ} (hq : 0 < q) {M K : ℕ} (hM : 1 ≤ M) (hK : 2 ≤ K)
    {m : ℤ} (hm : (M : ℤ) < |m|) (a : ℕ) :
    ‖((N / q : ℝ) : ℂ) * 𝓕 (Wt τ) (N * m / q) * Complex.exp (2 * π * I * m * (a / q))‖ ≤
      N / q * CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K / (M : ℝ) ^ (K - 2) * |(m : ℝ)| ^ (-(2 : ℝ)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (M : ℝ) < |(m : ℝ)| := by
    have : ((M : ℤ) : ℝ) < ((|m| : ℤ) : ℝ) := by exact_mod_cast hm
    rwa [Int.cast_abs, Int.cast_natCast] at this
  have hxpos : 0 < |(m : ℝ)| := by linarith
  have hexp : ‖Complex.exp (2 * π * I * m * (a / q))‖ = 1 := by
    rw [show (2 * π * I * m * (a / q) : ℂ) = ((2 * π * m * (a / q) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h43 := lemma43 τ K (N * m / q)
  have hξ : |N * (m : ℝ) / q| = N * |(m : ℝ)| / q := by rw [abs_div, abs_mul, abs_of_pos hN, abs_of_pos hq']
  rw [hξ] at h43
  have hden : 0 < (2 * π * (N * |(m : ℝ)| / q)) ^ K := by positivity
  have hb : ‖𝓕 (Wt τ) (N * m / q)‖ ≤ CF K * (1 + |τ|) ^ K / (2 * π * (N * |(m : ℝ)| / q)) ^ K := by
    rw [le_div_iff₀ hden]; linarith [h43]
  have hρ : CF K * (1 + |τ|) ^ K / (2 * π * (N * |(m : ℝ)| / q)) ^ K =
      CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K / |(m : ℝ)| ^ K := by
    have e1 : (1 + |τ|) / (2 * π * (N * |(m : ℝ)| / q)) = q * (1 + |τ|) / (2 * π * N) / |(m : ℝ)| := by
      field_simp
    rw [mul_div_assoc (CF K), ← div_pow, e1, div_pow, mul_div_assoc (CF K)]
  have hxK : (M : ℝ) ^ (K - 2) * |(m : ℝ)| ^ 2 ≤ |(m : ℝ)| ^ K := by
    calc (M : ℝ) ^ (K - 2) * |(m : ℝ)| ^ 2 ≤ |(m : ℝ)| ^ (K - 2) * |(m : ℝ)| ^ 2 := by gcongr
      _ = |(m : ℝ)| ^ K := by rw [← pow_add, Nat.sub_add_cancel hK]
  have habs : |(m : ℝ)| ^ (-(2 : ℝ)) = (|(m : ℝ)| ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two]
  have hCF := CF_nonneg K
  have hnum : 0 ≤ CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K := by positivity
  rw [habs]
  calc N / q * ‖𝓕 (Wt τ) (N * m / q)‖
      ≤ N / q * (CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K / |(m : ℝ)| ^ K) := by
        rw [← hρ]; gcongr
    _ ≤ N / q * (CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K / ((M : ℝ) ^ (K - 2) * |(m : ℝ)| ^ 2)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hnum (by positivity) hxK) (by positivity)
    _ = N / q * CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K / (M : ℝ) ^ (K - 2) * (|(m : ℝ)| ^ 2)⁻¹ := by
        field_simp

/-- `Σ_m (if m = 0 then 0 else f(m)) − Σ_{m∈B}f(m) = Σ_m (if m = 0 or m ∈ B then 0 else f(m))` for `0 ∉ B`. -/
lemma tsum_ite_sub_sum {f : ℤ → ℂ} (hf : Summable f) (B : Finset ℤ) (hB : (0 : ℤ) ∉ B) :
    (∑' m : ℤ, if m = 0 then 0 else f m) - ∑ m ∈ B, f m = ∑' m : ℤ, if m = 0 ∨ m ∈ B then 0 else f m := by
  classical
  have h1 : Summable fun m : ℤ => if m ∈ B then f m else 0 :=
    Summable.of_norm_bounded hf.norm fun m => by split_ifs <;> simp
  have h2 : Summable fun m : ℤ => if m = 0 ∨ m ∈ B then 0 else f m :=
    Summable.of_norm_bounded hf.norm fun m => by split_ifs <;> simp
  have hsplit : (fun m : ℤ => if m = 0 then 0 else f m) =
      fun m => (if m ∈ B then f m else 0) + (if m = 0 ∨ m ∈ B then 0 else f m) := by
    funext m
    by_cases h0 : m = 0
    · subst h0; simp [hB]
    · by_cases hm : m ∈ B <;> simp [h0, hm]
  rw [hsplit, h1.tsum_add h2, tsum_eq_sum (s := B) fun m hm => by simp [hm]]
  rw [Finset.sum_congr rfl fun m hm => ite_eq_left hm]
  ring

lemma not_mem_boxM {M : ℕ} {m : ℤ} (h : ¬(m = 0 ∨ m ∈ boxM M)) : (M : ℤ) < |m| := by
  unfold boxM at h
  rw [Finset.mem_erase, Finset.mem_Icc] at h
  by_contra hc
  rw [not_lt, abs_le] at hc
  by_cases h0 : m = 0
  · exact h (Or.inl h0)
  · exact h (Or.inr ⟨h0, hc⟩)

/-- **The tail beyond `M`**: for `N > 0`, `M ≥ 1` and `K ≥ 2`, `‖F(i, k) − F_M(i, k)‖ ≤ N·CF(K)ρ^K M^{2−K}Z₂` with
`ρ = q(1 + |t_i − t_k|)/(2πN)`. -/
theorem norm_Fm_sub_FmT_le {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (i k : ι) {M K : ℕ} (hM : 1 ≤ M) (hK : 2 ≤ K) :
    ‖Fm N χ t i k - FmT M N χ t i k‖ ≤
      N * CF K * (q * (1 + |t i - t k|) / (2 * π * N)) ^ K / (M : ℝ) ^ (K - 2) * Z2 := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set τ := t i - t k with hτ
  set f : ℕ → ℤ → ℂ := fun a m =>
    ((N / q : ℝ) : ℂ) * 𝓕 (Wt τ) (N * m / q) * Complex.exp (2 * π * I * m * (a / q)) with hf
  set C₀ := N / q * CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K / (M : ℝ) ^ (K - 2) with hC₀
  have hC₀0 : 0 ≤ C₀ := by have := CF_nonneg K; positivity
  have h0B : (0 : ℤ) ∉ boxM M := by unfold boxM; exact Finset.notMem_erase 0 _
  have hdiff : Fm N χ t i k - FmT M N χ t i k = ∑ a ∈ Finset.range q, (χ i a * star (χ k a)) *
      ∑' m : ℤ, if m = 0 ∨ m ∈ boxM M then 0 else f a m := by
    have hT : FmT M N χ t i k = ∑ a ∈ Finset.range q, (χ i a * star (χ k a)) * ∑ m ∈ boxM M, f a m := by
      unfold FmT phi
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    rw [hT]
    unfold Fm
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_sub, tsum_ite_sub_sum (summable_poisson τ hN hq a) (boxM M) h0B]
  have hX : ∀ a : ℕ, ‖∑' m : ℤ, (if m = 0 ∨ m ∈ boxM M then 0 else f a m)‖ ≤ C₀ * Z2 := by
    intro a
    have hbound : ∀ m : ℤ, ‖(if m = 0 ∨ m ∈ boxM M then 0 else f a m)‖ ≤ C₀ * |(m : ℝ)| ^ (-(2 : ℝ)) := by
      intro m
      split_ifs with h
      · rw [norm_zero]; positivity
      · exact norm_tail_term_le τ hN hq hM hK (not_mem_boxM h) a
    have hsumm : Summable fun m : ℤ => C₀ * |(m : ℝ)| ^ (-(2 : ℝ)) :=
      (Real.summable_abs_int_rpow one_lt_two).mul_left _
    have hle := tsum_of_norm_bounded hsumm.hasSum hbound
    rwa [tsum_mul_left] at hle
  rw [hdiff]
  calc ‖∑ a ∈ Finset.range q, (χ i a * star (χ k a)) * ∑' m : ℤ, (if m = 0 ∨ m ∈ boxM M then 0 else f a m)‖
      ≤ ∑ a ∈ Finset.range q, ‖(χ i a * star (χ k a)) * ∑' m : ℤ, (if m = 0 ∨ m ∈ boxM M then 0 else f a m)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a ∈ Finset.range q, C₀ * Z2 := Finset.sum_le_sum fun a _ => by
        rw [norm_mul]
        calc ‖χ i a * star (χ k a)‖ * ‖∑' m : ℤ, (if m = 0 ∨ m ∈ boxM M then 0 else f a m)‖ ≤ 1 * (C₀ * Z2) :=
              mul_le_mul (norm_coef_le _ _ a) (hX a) (norm_nonneg _) zero_le_one
          _ = C₀ * Z2 := one_mul _
    _ = N * CF K * (q * (1 + |τ|) / (2 * π * N)) ^ K / (M : ℝ) ^ (K - 2) * Z2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hC₀]
        field_simp

/-! ### The entries and the truncated cubic trace -/

lemma norm_entP_le {ι : Type*} {q : ℕ} (N : ℝ) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (i : ι) {n : ℕ}
    (hn : 0 < n) : ‖entP N χ t i n‖ ≤ 1 := by
  unfold entP
  rw [norm_mul, norm_mul, norm_cpow_I hn, mul_one, Complex.norm_real, Real.norm_of_nonneg (wCGL_nonneg _)]
  exact mul_le_one_of (wCGL_le_one _) (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)

lemma norm_gramP_le {ι : Type*} {q : ℕ} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (i k : ι) : ‖gramP N χ t i k‖ ≤ N + 1 := by
  unfold gramP
  calc ‖∑ n ∈ colsP N, entP N χ t i n * star (entP N χ t k n)‖
      ≤ ∑ n ∈ colsP N, ‖entP N χ t i n * star (entP N χ t k n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ colsP N, (1 : ℝ) := Finset.sum_le_sum fun n hn => by
        have hn0 := colsP_pos hN hn
        rw [norm_mul, norm_star]
        exact mul_le_one_of (norm_entP_le N χ t i hn0) (norm_nonneg _) (norm_entP_le N χ t k hn0)
    _ = (colsP N).card := by simp
    _ ≤ N + 1 := card_colsP_le hN.le

/-- `‖F(i, k)‖ ≤ 2N + 1` for `N > 0`, `i, k ∈ R` and `χ` injective on `R` (`|F| = |E′| ≤ |G| + μ₀`, with round 648's
`E′ = G − δμ₀`). -/
lemma norm_Fm_le {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (t : ι → ℝ) {i k : ι} (hi : i ∈ R) (hk : k ∈ R) :
    ‖Fm N χ t i k‖ ≤ 2 * N + 1 := by
  have h := Em_eq hN hinj t hi hk
  have hph : ‖(N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]; simp
  have hE : ‖Em q N χ t i k‖ = ‖Fm N χ t i k‖ := by rw [h, norm_mul, hph, one_mul]
  rw [← hE]
  unfold Em
  have hmu := mu0_le q hN.le
  have hmu0 := mu0_nonneg q hN.le
  calc ‖gramP N χ t i k - (if i = k then (mu0 q N : ℂ) else 0)‖
      ≤ ‖gramP N χ t i k‖ + ‖(if i = k then (mu0 q N : ℂ) else 0)‖ := norm_sub_le _ _
    _ ≤ (N + 1) + N := by
        refine add_le_add (norm_gramP_le hN χ t i k) ?_
        split_ifs
        · rw [Complex.norm_real, Real.norm_of_nonneg hmu0]; exact hmu
        · rw [norm_zero]; exact hN.le
    _ = 2 * N + 1 := by ring

/-- `‖x₁x₂x₃ − y₁y₂y₃‖ ≤ 3τ(A + τ)²` for `‖x_i‖ ≤ A` and `‖x_i − y_i‖ ≤ τ`. -/
lemma norm_cube_sub_le {x₁ x₂ x₃ y₁ y₂ y₃ : ℂ} {A τ : ℝ} (h1 : ‖x₁ - y₁‖ ≤ τ) (h2 : ‖x₂ - y₂‖ ≤ τ)
    (h3 : ‖x₃ - y₃‖ ≤ τ) (hx1 : ‖x₁‖ ≤ A) (hx2 : ‖x₂‖ ≤ A) (hx3 : ‖x₃‖ ≤ A) (hτ : 0 ≤ τ) :
    ‖x₁ * x₂ * x₃ - y₁ * y₂ * y₃‖ ≤ 3 * τ * (A + τ) ^ 2 := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hx1
  have hy1 : ‖y₁‖ ≤ A + τ := by
    calc ‖y₁‖ = ‖x₁ - (x₁ - y₁)‖ := by ring_nf
      _ ≤ ‖x₁‖ + ‖x₁ - y₁‖ := norm_sub_le _ _
      _ ≤ A + τ := add_le_add hx1 h1
  have hy2 : ‖y₂‖ ≤ A + τ := by
    calc ‖y₂‖ = ‖x₂ - (x₂ - y₂)‖ := by ring_nf
      _ ≤ ‖x₂‖ + ‖x₂ - y₂‖ := norm_sub_le _ _
      _ ≤ A + τ := add_le_add hx2 h2
  have hx2' : ‖x₂‖ ≤ A + τ := by linarith
  have hx3' : ‖x₃‖ ≤ A + τ := by linarith
  have e : x₁ * x₂ * x₃ - y₁ * y₂ * y₃ = (x₁ - y₁) * x₂ * x₃ + y₁ * (x₂ - y₂) * x₃ + y₁ * y₂ * (x₃ - y₃) := by ring
  rw [e]
  calc ‖(x₁ - y₁) * x₂ * x₃ + y₁ * (x₂ - y₂) * x₃ + y₁ * y₂ * (x₃ - y₃)‖
      ≤ ‖(x₁ - y₁) * x₂ * x₃‖ + ‖y₁ * (x₂ - y₂) * x₃‖ + ‖y₁ * y₂ * (x₃ - y₃)‖ := norm_add₃_le
    _ ≤ τ * (A + τ) * (A + τ) + (A + τ) * τ * (A + τ) + (A + τ) * (A + τ) * τ := by
        simp only [norm_mul]
        gcongr
    _ = 3 * τ * (A + τ) ^ 2 := by ring

/-- `τ_M = N·CF(K)(q(1 + 2T)/(2πN))^K M^{2−K}Z₂`, the tail bound at `|t_i − t_k| ≤ 2T`. -/
def tauM (N : ℝ) (q : ℕ) (T : ℝ) (M K : ℕ) : ℝ :=
  N * CF K * (q * (1 + 2 * T) / (2 * π * N)) ^ K / (M : ℝ) ^ (K - 2) * Z2

/-- **Their (7.1) at one point per character, before the triangle inequality**: for `N > 0`, `χ` injective on `R`,
`M ≥ 1`, `K ≥ 2` and points `|t_i| ≤ T`, `|S₃ − (Re Σ_{0<|m_i|≤M}I′(m⃗) − |R|(μ − μ₀)³)| ≤ 3|R|³τ_M(2N + 1 + τ_M)²`. -/
theorem S3_trunc {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (t : ι → ℝ) {T : ℝ} (ht : ∀ i ∈ R, |t i| ≤ T)
    {M K : ℕ} (hM : 1 ≤ M) (hK : 2 ≤ K) :
    |S3 q N R χ t - ((∑ m₁ ∈ boxM M, ∑ m₂ ∈ boxM M, ∑ m₃ ∈ boxM M, Ip N R χ t m₁ m₂ m₃).re -
        R.card * (muP q N - mu0 q N) ^ 3)| ≤
      3 * (R.card : ℝ) ^ 3 * tauM N q T M K * (2 * N + 1 + tauM N q T M K) ^ 2 := by
  rcases R.eq_empty_or_nonempty with hR | ⟨i₀, hi₀⟩
  · subst hR; simp [S3, X3, frobOff, Ip]
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (ht i₀ hi₀)
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hτ0 : 0 ≤ tauM N q T M K := by unfold tauM; have := CF_nonneg K; have := Z2_nonneg; positivity
  have htail : ∀ i ∈ R, ∀ k ∈ R, ‖Fm N χ t i k - FmT M N χ t i k‖ ≤ tauM N q T M K := by
    intro i hi k hk
    refine (norm_Fm_sub_FmT_le hN χ t i k hM hK).trans ?_
    unfold tauM
    have hik : |t i - t k| ≤ 2 * T := by
      calc |t i - t k| ≤ |t i| + |t k| := abs_sub _ _
        _ ≤ T + T := add_le_add (ht i hi) (ht k hk)
        _ = 2 * T := by ring
    have := CF_nonneg K
    have := Z2_nonneg
    gcongr
  have hS3 := S3_eq_all hN hinj t
  rw [hS3, ← sum_FmT_cube]
  have e : (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re -
      R.card * (muP q N - mu0 q N) ^ 3 -
      ((∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i).re -
        R.card * (muP q N - mu0 q N) ^ 3) =
      (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
        FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)).re := by
    simp only [Finset.sum_sub_distrib, Complex.sub_re]; ring
  rw [e]
  have hA : ∀ i ∈ R, ∀ k ∈ R, ‖Fm N χ t i k‖ ≤ 2 * N + 1 := fun i hi k hk => norm_Fm_le hN hinj t hi hk
  calc |(∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
        FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)).re|
      ≤ ‖∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, (Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
        FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, ‖Fm N χ t i j * Fm N χ t j k * Fm N χ t k i -
        FmT M N χ t i j * FmT M N χ t j k * FmT M N χ t k i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact norm_sum_le _ _
    _ ≤ ∑ _i ∈ R, ∑ _j ∈ R, ∑ _k ∈ R, 3 * tauM N q T M K * (2 * N + 1 + tauM N q T M K) ^ 2 :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk =>
          norm_cube_sub_le (htail i hi j hj) (htail j hj k hk) (htail k hk i hi) (hA i hi j hj) (hA j hj k hk)
            (hA k hk i hi) hτ0
    _ = 3 * (R.card : ℝ) ^ 3 * tauM N q T M K * (2 * N + 1 + tauM N q T M K) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring

end LinnikCGLTrunc

#print axioms LinnikCGLTrunc.sum_FmT_cube
#print axioms LinnikCGLTrunc.norm_tail_term_le
#print axioms LinnikCGLTrunc.norm_Fm_sub_FmT_le
#print axioms LinnikCGLTrunc.norm_Fm_le
#print axioms LinnikCGLTrunc.S3_trunc
