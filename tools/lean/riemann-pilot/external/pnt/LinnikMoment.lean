import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Module

/-!
# Rounds 536–537: third-moment bounds for the largest singular value

Built on Mathlib alone; no PrimeNumberTheoremAnd file is imported.

**Round 537: Chen–Gupta–Li's Lemma 4.2** (`refined_moment`, `refined_moment_cube`, `refined_moment_chars`). Their
Lemma 4.2, which they cite as Guth–Maynard's Lemma 4.2, reads
"s₁(M) ≤ 2(tr((MM∗)³) − tr(MM∗)³/|W|²)^{1/6} + 2(tr(MM∗)/|W|)^{1/2}". Here it is proved with constant `1`, in
squared form. For a complex matrix `A` with `n` rows indexed by `ι` and columns by `κ`, put `G = AAᴴ`,
`μ = Re tr(G)/n` and `X = Re tr(G³) − nμ³`. If `‖Ab‖² ≥ μ‖b‖²`, then
`(‖Ab‖² − μ‖b‖²)²(‖Ab‖² + 2μ‖b‖²) ≤ ‖b‖⁶X`, so `(‖Ab‖² − μ‖b‖²)³ ≤ ‖b‖⁶X` and `‖Ab‖² ≤ ‖b‖²(μ + X^{1/3})`.
Over the characters mod `q` (`A_{χ,n} = c_n χ(n)` for `χ ∈ W` and `n ∈ S`, every `n ∈ S` prime to `q`) the Gram
matrix `G(χ, χ′) = Σ_{n∈S} c_n χ(n) · conj(c_n χ′(n))` has constant diagonal `N_c = Σ_{n∈S}|c_n|²`, and `X` is the
sum of `G(χ₁,χ₂)G(χ₂,χ₃)G(χ₃,χ₁)` over the triples of `W` that are not all equal. That is the sum of their
Lemma 4.5, which the rest of their argument bounds.

The proof uses no spectral theory. With `y = Ab`, `r = ‖Aᴴy‖²`, `t = ‖AᴴGy‖²` and `s = ‖y‖²`, two
Cauchy–Schwarz steps give `r³ ≤ ts²`. The polynomial `p(x) = x³ − 3μ²x + 2μ³ = (x − μ)²(x + 2μ)` has
`p(G) = (BA)(BA)ᴴ + 2μ·BBᴴ` with `B = G − μ` (`cube_decomp`), so row by row `t − 3μ²r + 2μ³s ≤ Re tr(p(G))·s`,
and `Re tr(p(G)) = X`. Together, `s³p(r/s) ≤ Xs³`. Finally `p` increases on `[μ, ∞)`, and
`r/s ≥ ‖Ab‖²/‖b‖² ≥ μ` by a third Cauchy–Schwarz step.

**Round 536: the simple bound at `r = 3`** (`moment_three`, `moment_three_chars`). `‖Ab‖⁶ ≤ ‖b‖⁶ · Re tr(G³)`;
over the characters, `(Σ_{χ∈W} |Σ_{n∈S} b_n c_n χ(n)|²)³ ≤ (Σ_{n∈S} |b_n|²)³ · Re Σ_{χ₁,χ₂,χ₃∈W}
G(χ₁,χ₂)G(χ₂,χ₃)G(χ₃,χ₁)`. This is Chen–Gupta–Li's "simple bound s₁(M) ≤ tr((MM∗)^r)^{1/2r}" at `r = 3`, which they
set aside: "this bound can be quite lossy". Since `Re tr(G³) ≥ nN_c³` when the diagonal is `N_c`, a large value
`|D(χ)| ≥ V` on all of `W` with `‖b‖² ≤ N` gives through it at best `|W|² ≤ N³N_c³/V⁶`. At their critical point for
prime moduli (`σ = 5/7`, `N = q^{7/9}`, `N_c ≍ N`) that is `|W| ≲ q^{2/3}`, the size to be beaten. Lemma 4.2
removes the all-equal triples, the source of that term. *(Round 537: this paragraph corrects round 536's
description, which called this bound the first step of their method.)* Its proof: with `y = Ab`, `u = Aᴴy`,
`z = Au` and `v = Aᴴz`, Cauchy–Schwarz gives `‖y‖⁴ ≤ ‖b‖²‖u‖²`, `‖u‖⁴ ≤ ‖z‖²‖y‖²` and `‖z‖⁴ ≤ ‖v‖²‖u‖²`; and
`v = Cy` with `C = Aᴴ(AAᴴ)`, so row by row `‖v‖² ≤ ‖C‖_F²‖y‖²`, where `‖C‖_F² = Re tr(CCᴴ) = Re tr((AAᴴ)³)` by
cyclicity of the trace.

* `norm_sum_mul_sq_le`: `|Σ a_i b_i|² ≤ (Σ|a_i|²)(Σ|b_i|²)`.
* `sum_star_mulVec`: `Σ_i conj(v_i)(Aw)_i = Σ_j conj((Aᴴv)_j)w_j`.
* `nsq_mulVec_le`: `‖Cy‖² ≤ ‖C‖_F²‖y‖²`, and `frob_eq_trace`: `‖C‖_F² = Re tr(CCᴴ)`.
* `moment_three`, `moment_three_chars`.
* `qf_le_trace`: `Re ⟨y, CCᴴy⟩ ≤ Re tr(CCᴴ)‖y‖²`; `cube_decomp`; `sum_triples_split`.
* `refined_moment`, `refined_moment_cube`, `refined_moment_chars`.
-/

open Matrix Finset

noncomputable section

namespace LinnikMoment

/-- The squared `ℓ²` norm `Σ_i |v_i|²`. -/
def nsq {α : Type*} [Fintype α] (v : α → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma nsq_nonneg {α : Type*} [Fintype α] (v : α → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Cauchy–Schwarz for finite sums of complex numbers. -/
lemma norm_sum_mul_sq_le {α : Type*} [Fintype α] (a b : α → ℂ) :
    ‖∑ i, a i * b i‖ ^ 2 ≤ nsq a * nsq b := by
  have h1 : ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
  calc ‖∑ i, a i * b i‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖b i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ nsq a * nsq b := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma nsq_star {α : Type*} [Fintype α] (v : α → ℂ) : nsq (fun i => star (v i)) = nsq v := by
  simp only [nsq, norm_star]

/-- `|Σ_i conj(v_i) w_i|² ≤ ‖v‖²‖w‖²`. -/
lemma norm_inner_sq_le {α : Type*} [Fintype α] (v w : α → ℂ) :
    ‖∑ i, star (v i) * w i‖ ^ 2 ≤ nsq v * nsq w := by
  have := norm_sum_mul_sq_le (fun i => star (v i)) w
  rwa [nsq_star] at this

/-- `‖v‖²`, as a complex number, is `Σ_i conj(v_i) v_i`. -/
lemma nsq_eq_sum {α : Type*} [Fintype α] (v : α → ℂ) : (nsq v : ℂ) = ∑ i, star (v i) * v i := by
  simp only [nsq, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- A nonnegative real equal, as a complex number, to `X` is `|X|`. -/
lemma eq_norm_of_ofReal_eq {r : ℝ} (hr : 0 ≤ r) {X : ℂ} (h : (r : ℂ) = X) : r = ‖X‖ := by
  rw [← h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `Σ_i conj(v_i)(Aw)_i = Σ_j conj((Aᴴv)_j)w_j`. -/
lemma sum_star_mulVec (A : Matrix ι κ ℂ) (v : ι → ℂ) (w : κ → ℂ) :
    ∑ i, star (v i) * (A *ᵥ w) i = ∑ j, star ((Aᴴ *ᵥ v) j) * w j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul', star_star,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- One Cauchy–Schwarz step: `‖Aw‖⁴ ≤ ‖Aᴴ(Aw)‖²‖w‖²`. -/
lemma nsq_sq_le (A : Matrix ι κ ℂ) (w : κ → ℂ) :
    nsq (A *ᵥ w) ^ 2 ≤ nsq (Aᴴ *ᵥ (A *ᵥ w)) * nsq w := by
  have h := (nsq_eq_sum (A *ᵥ w)).trans (sum_star_mulVec A (A *ᵥ w) w)
  rw [eq_norm_of_ofReal_eq (nsq_nonneg _) h]
  exact norm_inner_sq_le _ _

/-- The squared Frobenius norm `Σ_{j,i}|C_{ji}|²`. -/
def frob {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) : ℝ := ∑ j, ∑ i, ‖C j i‖ ^ 2

lemma frob_nonneg {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) : 0 ≤ frob C :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- Row by row Cauchy–Schwarz: `‖Cy‖² ≤ ‖C‖_F²‖y‖²`. -/
lemma nsq_mulVec_le {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) (y : β → ℂ) :
    nsq (C *ᵥ y) ≤ frob C * nsq y := by
  rw [frob, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => norm_sum_mul_sq_le (fun i => C j i) y

/-- `‖C‖_F² = Re tr(CCᴴ)`. -/
lemma frob_eq_trace {α β : Type*} [Fintype α] [Fintype β] (C : Matrix α β ℂ) :
    frob C = (C * Cᴴ).trace.re := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `Re tr(CCᴴ)` for `C = Aᴴ(AAᴴ)` is `Re tr((AAᴴ)³)`. -/
lemma frob_cube (A : Matrix ι κ ℂ) :
    frob (Aᴴ * (A * Aᴴ)) = (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re := by
  rw [frob_eq_trace]
  congr 2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- **The simple bound at `r = 3`**: `‖Ab‖⁶ ≤ ‖b‖⁶ · Re tr((AAᴴ)³)`. -/
theorem moment_three (A : Matrix ι κ ℂ) (b : κ → ℂ) :
    nsq (A *ᵥ b) ^ 3 ≤ nsq b ^ 3 * (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re := by
  set y := A *ᵥ b with hy
  set u := Aᴴ *ᵥ y with hu
  set z := A *ᵥ u with hz
  set v := Aᴴ *ᵥ z with hv
  set t := (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re with ht
  have h1 : nsq y ^ 2 ≤ nsq u * nsq b := nsq_sq_le A b
  have h2 : nsq u ^ 2 ≤ nsq z * nsq y := by
    have := nsq_sq_le Aᴴ y
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have h3 : nsq z ^ 2 ≤ nsq v * nsq u := nsq_sq_le A u
  have h4 : nsq v ≤ t * nsq y := by
    have hvC : v = (Aᴴ * (A * Aᴴ)) *ᵥ y := by
      rw [hv, hz, hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hvC, ht, ← frob_cube]
    exact nsq_mulVec_le _ _
  have ht0 : 0 ≤ t := by rw [ht, ← frob_cube]; exact frob_nonneg _
  have ha := nsq_nonneg y
  have hb := nsq_nonneg b
  have hg1 := nsq_nonneg u
  have hg2 := nsq_nonneg z
  have hg3 := nsq_nonneg v
  rcases ha.eq_or_lt with ha0 | hapos
  · rw [← ha0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  have hg1pos : 0 < nsq u := by
    by_contra hcon
    have : nsq u = 0 := le_antisymm (not_lt.mp hcon) hg1
    rw [this, zero_mul] at h1
    nlinarith
  -- `‖u‖⁶ ≤ t‖y‖³` from h2, h3, h4
  have k1 : nsq u ^ 4 ≤ t * nsq y ^ 3 * nsq u := by
    calc nsq u ^ 4 = (nsq u ^ 2) ^ 2 := by ring
      _ ≤ (nsq z * nsq y) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = nsq z ^ 2 * nsq y ^ 2 := by ring
      _ ≤ (nsq v * nsq u) * nsq y ^ 2 := by gcongr
      _ ≤ (t * nsq y * nsq u) * nsq y ^ 2 := by gcongr
      _ = t * nsq y ^ 3 * nsq u := by ring
  have k2 : nsq u ^ 3 ≤ t * nsq y ^ 3 := by
    have : nsq u ^ 3 * nsq u ≤ t * nsq y ^ 3 * nsq u := by
      calc nsq u ^ 3 * nsq u = nsq u ^ 4 := by ring
        _ ≤ _ := k1
    exact le_of_mul_le_mul_right this hg1pos
  have k3 : nsq y ^ 6 ≤ nsq b ^ 3 * t * nsq y ^ 3 := by
    calc nsq y ^ 6 = (nsq y ^ 2) ^ 3 := by ring
      _ ≤ (nsq u * nsq b) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = nsq u ^ 3 * nsq b ^ 3 := by ring
      _ ≤ (t * nsq y ^ 3) * nsq b ^ 3 := by gcongr
      _ = nsq b ^ 3 * t * nsq y ^ 3 := by ring
  have hy3 : 0 < nsq y ^ 3 := by positivity
  have : nsq y ^ 3 * nsq y ^ 3 ≤ nsq b ^ 3 * t * nsq y ^ 3 := by
    calc nsq y ^ 3 * nsq y ^ 3 = nsq y ^ 6 := by ring
      _ ≤ _ := k3
  exact le_of_mul_le_mul_right this hy3

/-- The Gram matrix `G(χ, χ′) = Σ_{n∈S} c_n χ(n) · conj(c_n χ′(n))` of a set of characters on `S`. -/
def gram {q : ℕ} (S : Finset ℕ) (c : ℕ → ℂ) (χ χ' : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ S, (c n * χ n) * star (c n * χ' n)

/-- **The simple bound at `r = 3` over the characters mod `q`**:
`(Σ_{χ∈W}|Σ_{n∈S} b_n c_n χ(n)|²)³ ≤ (Σ_{n∈S}|b_n|²)³ · Re Σ_{χ₁,χ₂,χ₃∈W} G(χ₁,χ₂)G(χ₂,χ₃)G(χ₃,χ₁)`. -/
theorem moment_three_chars {q : ℕ} (W : Finset (DirichletCharacter ℂ q)) (S : Finset ℕ) (b c : ℕ → ℂ) :
    (∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2) ^ 3 ≤
      (∑ n ∈ S, ‖b n‖ ^ 2) ^ 3 *
        (∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gram S c χ₁ χ₂ * gram S c χ₂ χ₃ * gram S c χ₃ χ₁).re := by
  let A : Matrix W S ℂ := fun χ n => c n * (χ : DirichletCharacter ℂ q) n
  let b' : S → ℂ := fun n => b n
  have hl : nsq (A *ᵥ b') = ∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2 := by
    simp only [nsq, Matrix.mulVec, dotProduct, A, b']
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_coe_sort S (fun n => c n * (χ : DirichletCharacter ℂ q) n * b n)]
  have hb : nsq b' = ∑ n ∈ S, ‖b n‖ ^ 2 := by
    simp only [nsq, b']
    exact Finset.sum_coe_sort S (fun n => ‖b n‖ ^ 2)
  have hG : ∀ χ χ' : W, (A * Aᴴ) χ χ' = gram S c χ.1 χ'.1 := by
    intro χ χ'
    simp only [A, gram]
    exact Finset.sum_coe_sort S (fun n => c n * (χ : DirichletCharacter ℂ q) n *
      star (c n * (χ' : DirichletCharacter ℂ q) n))
  have ht : (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace =
      ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gram S c χ₁ χ₂ * gram S c χ₂ χ₃ * gram S c χ₃ χ₁ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.sum_mul]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₁ _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₂ _ => ?_
    rw [← Finset.sum_coe_sort W]
  have := moment_three A b'
  rw [hl, hb, ht] at this
  exact this

/-! ### Round 537: Chen–Gupta–Li's Lemma 4.2 -/

/-- The quadratic form `Re Σ_i conj(y_i)(Py)_i`. -/
def qf (P : Matrix ι ι ℂ) (y : ι → ℂ) : ℝ := (∑ i, star (y i) * (P *ᵥ y) i).re

lemma qf_mul_conjTranspose {α : Type*} [Fintype α] (C : Matrix ι α ℂ) (y : ι → ℂ) :
    qf (C * Cᴴ) y = nsq (Cᴴ *ᵥ y) := by
  rw [qf, ← Matrix.mulVec_mulVec, sum_star_mulVec C y (Cᴴ *ᵥ y), ← nsq_eq_sum, Complex.ofReal_re]

lemma qf_le_trace {α : Type*} [Fintype α] (C : Matrix ι α ℂ) (y : ι → ℂ) :
    qf (C * Cᴴ) y ≤ (C * Cᴴ).trace.re * nsq y := by
  rw [qf_mul_conjTranspose]
  calc nsq (Cᴴ *ᵥ y) ≤ frob Cᴴ * nsq y := nsq_mulVec_le _ _
    _ = _ := by rw [frob_eq_trace, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

lemma qf_add (P P' : Matrix ι ι ℂ) (y : ι → ℂ) : qf (P + P') y = qf P y + qf P' y := by
  simp only [qf, Matrix.add_mulVec, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

lemma qf_smul (a : ℝ) (P : Matrix ι ι ℂ) (y : ι → ℂ) : qf ((a : ℂ) • P) y = a * qf P y := by
  simp only [qf, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

lemma qf_one [DecidableEq ι] (y : ι → ℂ) : qf 1 y = nsq y := by
  rw [qf, Matrix.one_mulVec, ← nsq_eq_sum, Complex.ofReal_re]


/-- `G³ − 3μ²G + 2μ³ = (BA)(BA)ᴴ + 2μ·BBᴴ` for `G = AAᴴ` and `B = G − μ`. -/
lemma cube_decomp [DecidableEq ι] (A : Matrix ι κ ℂ) (μ : ℝ) :
    A * Aᴴ * (A * Aᴴ) * (A * Aᴴ) + ((-3 * μ ^ 2 : ℝ) : ℂ) • (A * Aᴴ) +
        ((2 * μ ^ 3 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) =
      ((A * Aᴴ - (μ : ℂ) • 1) * A) * ((A * Aᴴ - (μ : ℂ) • 1) * A)ᴴ +
        ((2 * μ : ℝ) : ℂ) • ((A * Aᴴ - (μ : ℂ) • 1) * (A * Aᴴ - (μ : ℂ) • 1)ᴴ) := by
  set G := A * Aᴴ with hG
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hBh : (G - (μ : ℂ) • (1 : Matrix ι ι ℂ))ᴴ = G - (μ : ℂ) • 1 := by
    rw [Matrix.conjTranspose_sub, hGh, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.conjTranspose_mul, hBh]
  have h1 : (G - (μ : ℂ) • (1 : Matrix ι ι ℂ)) * A * (Aᴴ * (G - (μ : ℂ) • 1)) =
      (G - (μ : ℂ) • 1) * G * (G - (μ : ℂ) • 1) := by
    rw [hG]; simp only [Matrix.mul_assoc]
  rw [h1]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_sub, smul_smul, Matrix.mul_assoc]
  push_cast
  module


/-- **Chen–Gupta–Li's Lemma 4.2** (Guth–Maynard's Lemma 4.2), with constant `1`, in the form
`(s − μβ)²(s + 2μβ) ≤ β³X` for `s = ‖Ab‖² ≥ μβ`, where `β = ‖b‖²`, `μ = Re tr(AAᴴ)/n` and
`X = Re tr((AAᴴ)³) − nμ³`. -/
theorem refined_moment [DecidableEq ι] (A : Matrix ι κ ℂ) (b : κ → ℂ) (μ : ℝ) (hμ : 0 ≤ μ)
    (htr : (A * Aᴴ).trace.re = Fintype.card ι * μ) (hge : μ * nsq b ≤ nsq (A *ᵥ b)) :
    (nsq (A *ᵥ b) - μ * nsq b) ^ 2 * (nsq (A *ᵥ b) + 2 * μ * nsq b) ≤
      nsq b ^ 3 * ((A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re - Fintype.card ι * μ ^ 3) := by
  have hP := cube_decomp A μ
  set B := A * Aᴴ - (μ : ℂ) • (1 : Matrix ι ι ℂ) with hB
  set X := (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re - Fintype.card ι * μ ^ 3 with hX
  -- the trace of `p(G) = G³ − 3μ²G + 2μ³` is `X`
  have htrP : ((B * A) * (B * A)ᴴ).trace.re + 2 * μ * (B * Bᴴ).trace.re = X := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M.trace.re) hP
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Complex.add_re,
      Complex.re_ofReal_mul, Complex.natCast_re] at h
    rw [hX, ← h, htr]
    ring
  have hX0 : 0 ≤ X := by
    rw [← htrP]
    have k1 : 0 ≤ ((B * A) * (B * A)ᴴ).trace.re := by rw [← frob_eq_trace]; exact frob_nonneg _
    have k2 : 0 ≤ (B * Bᴴ).trace.re := by rw [← frob_eq_trace]; exact frob_nonneg _
    positivity
  set y := A *ᵥ b with hy
  set u := Aᴴ *ᵥ y with hu
  set z := A *ᵥ u with hz
  set v := Aᴴ *ᵥ z with hv
  have h1 : nsq y ^ 2 ≤ nsq u * nsq b := nsq_sq_le A b
  have h2 : nsq u ^ 2 ≤ nsq z * nsq y := by
    have := nsq_sq_le Aᴴ y
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have h3 : nsq z ^ 2 ≤ nsq v * nsq u := nsq_sq_le A u
  -- the quadratic form of `G`, `G³` and `1` at `y`
  have qG : qf (A * Aᴴ) y = nsq u := qf_mul_conjTranspose A y
  have qG3 : qf (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)) y = nsq v := by
    have e : A * Aᴴ * (A * Aᴴ) * (A * Aᴴ) = (A * Aᴴ * A) * (A * Aᴴ * A)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    have hvC : v = (A * Aᴴ * A)ᴴ *ᵥ y := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hv, hz, hu,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, qf_mul_conjTranspose, hvC]
  have q1 : qf 1 y = nsq y := qf_one y
  -- `‖Aᴴ G y‖² − 3μ²‖Aᴴy‖² + 2μ³‖y‖² ≤ X‖y‖²`, from `p(G) = (BA)(BA)ᴴ + 2μBBᴴ`
  have h5 : nsq v - 3 * μ ^ 2 * nsq u + 2 * μ ^ 3 * nsq y ≤ X * nsq y := by
    have e1 : qf (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ) + ((-3 * μ ^ 2 : ℝ) : ℂ) • (A * Aᴴ) +
        ((2 * μ ^ 3 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) y = nsq v - 3 * μ ^ 2 * nsq u + 2 * μ ^ 3 * nsq y := by
      rw [qf_add, qf_add, qf_smul, qf_smul, qG3, qG, q1]; ring
    rw [← e1, hP, qf_add, qf_smul, ← htrP]
    have k1 := qf_le_trace (B * A) y
    have k2 := mul_le_mul_of_nonneg_left (qf_le_trace B y) (by positivity : (0 : ℝ) ≤ 2 * μ)
    nlinarith
  -- `‖Aᴴy‖⁶ ≤ ‖Aᴴ G y‖²‖y‖⁴`
  have h6 : nsq u ^ 3 ≤ nsq v * nsq y ^ 2 := by
    rcases (nsq_nonneg u).eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg (nsq_nonneg v) (by positivity)
    · have k : nsq u ^ 3 * nsq u ≤ nsq v * nsq y ^ 2 * nsq u := by
        calc nsq u ^ 3 * nsq u = (nsq u ^ 2) ^ 2 := by ring
          _ ≤ (nsq z * nsq y) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ = nsq z ^ 2 * nsq y ^ 2 := by ring
          _ ≤ (nsq v * nsq u) * nsq y ^ 2 := by gcongr
          _ = nsq v * nsq y ^ 2 * nsq u := by ring
      exact le_of_mul_le_mul_right k hpos
  -- `p` at the Rayleigh quotient of `G` at `y`, homogeneously: `(r − μs)²(r + 2μs) ≤ Xs³`
  have h7 : (nsq u - μ * nsq y) ^ 2 * (nsq u + 2 * μ * nsq y) ≤ X * nsq y ^ 3 := by
    have k : nsq y ^ 2 * (nsq v - 3 * μ ^ 2 * nsq u + 2 * μ ^ 3 * nsq y) ≤ nsq y ^ 2 * (X * nsq y) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith
  -- monotonicity of `p` on `[μ, ∞)`, with `‖y‖⁴ ≤ ‖b‖²‖Aᴴy‖²`
  have h8 : nsq y ^ 3 * ((nsq y - μ * nsq b) ^ 2 * (nsq y + 2 * μ * nsq b)) ≤
      nsq b ^ 3 * ((nsq u - μ * nsq y) ^ 2 * (nsq u + 2 * μ * nsq y)) := by
    have key : nsq b ^ 3 * ((nsq u - μ * nsq y) ^ 2 * (nsq u + 2 * μ * nsq y)) -
        nsq y ^ 3 * ((nsq y - μ * nsq b) ^ 2 * (nsq y + 2 * μ * nsq b)) =
        (nsq b * nsq u - nsq y ^ 2) * (nsq b ^ 2 * nsq u ^ 2 + nsq b * nsq u * nsq y ^ 2 + nsq y ^ 4 -
          3 * μ ^ 2 * nsq y ^ 2 * nsq b ^ 2) := by ring
    have hbu : nsq y ^ 2 ≤ nsq b * nsq u := by linarith [h1]
    have hA : 0 ≤ nsq b * nsq u - nsq y ^ 2 := by linarith
    have k1 : (nsq y ^ 2) ^ 2 ≤ (nsq b * nsq u) ^ 2 := pow_le_pow_left₀ (by positivity) hbu 2
    have k2 : nsq y ^ 2 * nsq y ^ 2 ≤ nsq b * nsq u * nsq y ^ 2 :=
      mul_le_mul_of_nonneg_right hbu (by positivity)
    have k3 : (μ * nsq b) ^ 2 * nsq y ^ 2 ≤ nsq y ^ 2 * nsq y ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hμ (nsq_nonneg b)) hge 2) (by positivity)
    have hB' : 0 ≤ nsq b ^ 2 * nsq u ^ 2 + nsq b * nsq u * nsq y ^ 2 + nsq y ^ 4 -
        3 * μ ^ 2 * nsq y ^ 2 * nsq b ^ 2 := by nlinarith
    nlinarith [mul_nonneg hA hB']
  have hb0 := nsq_nonneg b
  rcases (nsq_nonneg y).eq_or_lt with h0 | hpos
  · have hμb : μ * nsq b = 0 := le_antisymm (by rw [h0]; exact hge) (mul_nonneg hμ (nsq_nonneg b))
    have e : (nsq y - μ * nsq b) ^ 2 * (nsq y + 2 * μ * nsq b) = 0 := by
      have : 2 * μ * nsq b = 2 * (μ * nsq b) := by ring
      rw [← h0, this, hμb]; ring
    rw [e]; exact mul_nonneg (by positivity) hX0
  · have k : nsq y ^ 3 * ((nsq y - μ * nsq b) ^ 2 * (nsq y + 2 * μ * nsq b)) ≤
        nsq y ^ 3 * (nsq b ^ 3 * X) := by
      calc _ ≤ nsq b ^ 3 * ((nsq u - μ * nsq y) ^ 2 * (nsq u + 2 * μ * nsq y)) := h8
        _ ≤ nsq b ^ 3 * (X * nsq y ^ 3) := mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = nsq y ^ 3 * (nsq b ^ 3 * X) := by ring
    exact le_of_mul_le_mul_left k (by positivity)

/-- Lemma 4.2 cubed: `(‖Ab‖² − μ‖b‖²)³ ≤ ‖b‖⁶ (Re tr((AAᴴ)³) − nμ³)`, that is
`‖Ab‖² ≤ ‖b‖²(μ + X^{1/3})`. -/
theorem refined_moment_cube [DecidableEq ι] (A : Matrix ι κ ℂ) (b : κ → ℂ) (μ : ℝ) (hμ : 0 ≤ μ)
    (htr : (A * Aᴴ).trace.re = Fintype.card ι * μ) (hge : μ * nsq b ≤ nsq (A *ᵥ b)) :
    (nsq (A *ᵥ b) - μ * nsq b) ^ 3 ≤
      nsq b ^ 3 * ((A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace.re - Fintype.card ι * μ ^ 3) := by
  refine le_trans ?_ (refined_moment A b μ hμ htr hge)
  have h0 : 0 ≤ nsq (A *ᵥ b) - μ * nsq b := by linarith
  have h1 : nsq (A *ᵥ b) - μ * nsq b ≤ nsq (A *ᵥ b) + 2 * μ * nsq b := by
    nlinarith [mul_nonneg hμ (nsq_nonneg b)]
  calc (nsq (A *ᵥ b) - μ * nsq b) ^ 3 =
      (nsq (A *ᵥ b) - μ * nsq b) ^ 2 * (nsq (A *ᵥ b) - μ * nsq b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)


/-- A triple sum is the sum over the triples that are not all equal plus the diagonal. -/
lemma sum_triples_split {α : Type*} [DecidableEq α] (W : Finset α) (g : α → α → α → ℂ) :
    ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, g a b c =
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, if a = b ∧ b = c then 0 else g a b c) + ∑ a ∈ W, g a a a := by
  have hd : ∀ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, (if a = b ∧ b = c then g a b c else 0) = g a a a := by
    intro a ha
    simp only [ite_and]
    rw [Finset.sum_eq_single a]
    · simp [Finset.sum_ite_eq, ha]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd ha h
  rw [← Finset.sum_congr rfl hd, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- **Chen–Gupta–Li's Lemma 4.2 over the characters mod `q`.** For `n ∈ S` prime to `q`, the Gram matrix
`G(χ, χ′) = Σ_{n∈S} c_n χ(n) · conj(c_n χ′(n))` has constant diagonal `N_c = Σ_{n∈S}|c_n|²`, and with
`D(χ) = Σ_{n∈S} c_n χ(n) b_n`, `β = Σ_{n∈S}|b_n|²`: if `Σ_{χ∈W}|D(χ)|² ≥ N_cβ`, then
`(Σ_{χ∈W}|D(χ)|² − N_cβ)³ ≤ β³ · Re Σ G(χ₁,χ₂)G(χ₂,χ₃)G(χ₃,χ₁)`, the sum over the triples of `W` that are not all
equal. -/
theorem refined_moment_chars {q : ℕ} [DecidableEq (DirichletCharacter ℂ q)]
    (W : Finset (DirichletCharacter ℂ q)) (S : Finset ℕ) (b c : ℕ → ℂ) (hS : ∀ n ∈ S, IsUnit (n : ZMod q))
    (hge : (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2) ≤ ∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2) :
    (∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2 - (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2)) ^ 3 ≤
      (∑ n ∈ S, ‖b n‖ ^ 2) ^ 3 *
        (∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W,
          if χ₁ = χ₂ ∧ χ₂ = χ₃ then 0 else gram S c χ₁ χ₂ * gram S c χ₂ χ₃ * gram S c χ₃ χ₁).re := by
  set Nc := ∑ n ∈ S, ‖c n‖ ^ 2 with hNc
  have hdiag : ∀ χ : DirichletCharacter ℂ q, gram S c χ χ = (Nc : ℂ) := by
    intro χ
    simp only [gram, hNc, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨u, hu⟩ := hS n hn
    have h1 : ‖χ n‖ = 1 := by rw [← hu]; exact DirichletCharacter.unit_norm_eq_one χ u
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, h1, mul_one,
      Complex.ofReal_pow]
  let A : Matrix W S ℂ := fun χ n => c n * (χ : DirichletCharacter ℂ q) n
  let b' : S → ℂ := fun n => b n
  have hl : nsq (A *ᵥ b') = ∑ χ ∈ W, ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2 := by
    simp only [nsq, Matrix.mulVec, dotProduct, A, b']
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_coe_sort S (fun n => c n * (χ : DirichletCharacter ℂ q) n * b n)]
  have hb : nsq b' = ∑ n ∈ S, ‖b n‖ ^ 2 := by
    simp only [nsq, b']
    exact Finset.sum_coe_sort S (fun n => ‖b n‖ ^ 2)
  have hG : ∀ χ χ' : W, (A * Aᴴ) χ χ' = gram S c χ.1 χ'.1 := by
    intro χ χ'
    simp only [A, gram]
    exact Finset.sum_coe_sort S (fun n => c n * (χ : DirichletCharacter ℂ q) n *
      star (c n * (χ' : DirichletCharacter ℂ q) n))
  have ht : (A * Aᴴ * (A * Aᴴ) * (A * Aᴴ)).trace =
      ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, gram S c χ₁ χ₂ * gram S c χ₂ χ₃ * gram S c χ₃ χ₁ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.sum_mul]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₁ _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_coe_sort W]
    refine Finset.sum_congr rfl fun χ₂ _ => ?_
    rw [← Finset.sum_coe_sort W]
  have htr1 : (A * Aᴴ).trace.re = Fintype.card W * Nc := by
    simp only [Matrix.trace, Matrix.diag, hG, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [Complex.mul_re]
  have hNc0 : 0 ≤ Nc := Finset.sum_nonneg fun _ _ => by positivity
  have key := refined_moment_cube A b' Nc hNc0 htr1 (by rw [hl, hb]; exact hge)
  rw [hl, hb, ht, sum_triples_split W, Complex.add_re] at key
  simp only [hdiag, Fintype.card_coe] at key
  have hdiag3 : (∑ a ∈ W, (Nc : ℂ) * (Nc : ℂ) * (Nc : ℂ)).re = W.card * Nc ^ 3 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have e : (W.card : ℂ) * ((Nc : ℂ) * (Nc : ℂ) * (Nc : ℂ)) = ((W.card * Nc ^ 3 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.ofReal_re]
  rw [hdiag3] at key
  simpa using key

end LinnikMoment
