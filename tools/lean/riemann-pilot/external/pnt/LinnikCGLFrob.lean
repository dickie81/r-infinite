/-
# Round 643: the off-diagonal mass of the Gram matrix, explicitly (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 642's `LinnikCGLPair.norm_gram_le` bounds one Gram entry. This file sums the squares over the pairs, with the
large polynomial put back, into an explicit bound on `‖E‖_F² = Σ_{i≠k}|G(i, k)|²` (round 639's `frobOff`), the
quantity of round 639's displayed hypothesis `CGLS2`. It is the proof of Chen–Gupta–Li's Proposition 6.1 from their
Lemma 6.2, at one point per character, before `Z` and `K` are chosen.

Plain statement (`frobOff_le`). Let `χ` be injective on `R`, `|t_i| ≤ T`, `N > 0`, `S ⊆ [2, N′]`, and
`|Σ_{n∈S}b_nχ_i(n)n^{it_i}| ≥ V > 0` for every `i ∈ R`. Let `Z, K ≥ 1`, and `d(k) ≤ τ` for `k ≤ N′Z`. Then
`‖E‖_F² ≤ N·Q₀(q)²I_H²·|R|·V^{−2}L(N′Z)·τ·Σ_{n∈S}|b_n|²·H_Z + |R|²B²`, where `I_H = ∫|H(1/2 + iu)| du`, `L(X)` is
round 526's large-sieve factor `LSX`, `H_Z = Σ_{m≤Z}1/m`, `Q₀(q)` is round 642's, and `B` is round 642's tail bound
at `|τ| = 2T` (`Bmax`).

Their proof of Proposition 6.1 says (spaces restored, the formulas transcribed): "Now we proceed with an argument
based on the mean value theorem. Notice that |Σ_{n∼N} w(n/N)b_n n^{it₂}χ₂(n)| ≥ N^σ for (t₂, χ₂) ∈ W." It multiplies
each dual sum by the large polynomial, takes "some coefficients c_l depending on (t₁, χ₁) such that
|c_l^{(t₁,χ₁)}| ⪅ 1, by the divisor bound", and applies the mean value theorem with characters. Their Remark 6.3: "In
particular, we reintroduce our large Dirichlet polynomial here whereas their proof only depended on the 1-separation
of W." The stack does the same with round 526's product trick, in its squared form. Three differences: the dual sum
is not split into dyadic ranges of `m` (its coefficients keep the weight `m^{−1/2}`, whence `H_Z`), `u` is not
truncated (it is integrated against `|H(1/2 + iu)|`, whence `I_H`), and the pairs are not split by `|t₁ − t₂|` (one
`Z` and one `K` serve every pair).

* `sq_le_mul_of_forall`, `two_mul_le_lam`, `integral_sq_le`: Cauchy–Schwarz against a weight, through
  `2hd ≤ λh + hd²/λ` for every `λ > 0`.
* `ls_points`: round 526's `ls_pv_dyadic` at the points `(χ_i, t_i)`, through the characters `χ(R)`.
* `prod_trick_points`: `|E| ≤ |FE|/V` at each point; `FE` is a polynomial on `[2, N′Z]` (round 526's `pv_mul`);
  then `ls_points` and round 526's `mass_mulCo_le`. Round 526's `huxley_core` is the same argument for a sum of
  `|E|`, with Cauchy–Schwarz over the points.
* `norm_dualS_pair`, `HZ`, `mass_dualCo_half`: `|D_{ik}(u)|` is the polynomial `Σ_{m≤Z}e_{k,u}(m)χ_i(m)m^{it_i}`
  at the point of `χ_i`, `e_{k,u}(m) = conj(χ_k(m)m^{−1/2+i(u+t_k)})` (round 526's `dualS_eq_conj_pv`), and
  `Σ_{m≤Z}|e_{k,u}(m)|² ≤ H_Z`.
* `wH`, `IH`, `Dp`, `sum_Dp_sq_le`: `Σ_{i,k∈R}|D_{ik}(u)|² ≤ |R|·V^{−2}L(N′Z)·τ·Σ|b_n|²·H_Z` at every `u`.
* `Bmax`, `gram_sq_le`: `|G(i, k)|² ≤ N·Q₀(q)²(∫|H(1/2 + iu)||D_{ik}(u)| du)² + B²` for `χ_i ≠ χ_k`.
* `frobOff_le`: Cauchy–Schwarz in `u` for each pair, and the sum over the pairs.

The file imports `LinnikCGLPair.lean`.
-/

import LinnikCGLPair

open Complex Set Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikCGLFrob

open LinnikCGLMat LinnikCGLS23 LinnikCGLMellin LinnikCGLReflect LinnikCGLPair DirichletCharacter LinnikReflect
  LinnikPower

/-! ### Cauchy–Schwarz through a free parameter -/

/-- If `2C ≤ λA + B/λ` for every `λ > 0`, with `A, B, C ≥ 0`, then `C² ≤ AB`. -/
lemma sq_le_mul_of_forall {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∀ l : ℝ, 0 < l → 2 * C ≤ l * A + B / l) : C ^ 2 ≤ A * B := by
  rcases hC.eq_or_lt with hC0 | hC0
  · rw [← hC0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  rcases hA.eq_or_lt with hA0 | hA0
  · exfalso
    have hl : 0 < (B + 1) / (2 * C) := by positivity
    have h1 := h _ hl
    rw [← hA0, mul_zero, zero_add] at h1
    have h2 : B / ((B + 1) / (2 * C)) = B * (2 * C) / (B + 1) := by field_simp
    have h3 : B * (2 * C) / (B + 1) < 2 * C := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  · have hl : 0 < C / A := div_pos hC0 hA0
    have h1 := h _ hl
    have e1 : C / A * A = C := div_mul_cancel₀ C hA0.ne'
    have e2 : B / (C / A) = B * A / C := by field_simp
    rw [e1, e2] at h1
    have h2 : C ≤ B * A / C := by linarith
    rw [le_div_iff₀ hC0] at h2
    nlinarith

/-- `2hd ≤ λh + hd²/λ` for `h ≥ 0` and `λ > 0`. -/
lemma two_mul_le_lam {h d l : ℝ} (hh : 0 ≤ h) (hl : 0 < l) : 2 * (h * d) ≤ l * h + h * d ^ 2 / l := by
  have h1 : 0 ≤ h * (d - l) ^ 2 / l := by positivity
  have h2 : h * (d - l) ^ 2 / l = l * h + h * d ^ 2 / l - 2 * (h * d) := by
    field_simp; ring
  linarith

/-- **Cauchy–Schwarz against a weight**: `(∫hd)² ≤ (∫h)(∫hd²)` for `h, d ≥ 0` with `h`, `hd` and `hd²`
integrable. -/
lemma integral_sq_le {h d : ℝ → ℝ} (hh : ∀ u, 0 ≤ h u) (hd : ∀ u, 0 ≤ d u) (i1 : Integrable h)
    (i2 : Integrable fun u => h u * d u) (i3 : Integrable fun u => h u * d u ^ 2) :
    (∫ u, h u * d u) ^ 2 ≤ (∫ u, h u) * ∫ u, h u * d u ^ 2 := by
  refine sq_le_mul_of_forall (integral_nonneg hh) (integral_nonneg fun u => mul_nonneg (hh u) (sq_nonneg _))
    (integral_nonneg fun u => mul_nonneg (hh u) (hd u)) fun l hl => ?_
  have h1 : ∫ u, 2 * (h u * d u) ≤ ∫ u, (l * h u + h u * d u ^ 2 / l) :=
    integral_mono (i2.const_mul 2) ((i1.const_mul l).add (i3.div_const l)) fun u => two_mul_le_lam (hh u) hl
  rw [integral_const_mul, integral_add (i1.const_mul l) (i3.div_const l), integral_const_mul, integral_div] at h1
  exact h1

/-! ### The large sieve and the product trick at the points -/

/-- **The large sieve at the points**: for `χ` injective on `R`, `T ≥ 0` and `|t_i| ≤ T`,
`Σ_{i∈R}|Σ_{k∈S_k}c_kχ_i(k)k^{it_i}|² ≤ L(X)Σ|c_k|²` for `S_k ⊆ [2, X]` (round 526's `ls_pv_dyadic` on the
characters `χ(R)`). -/
lemma ls_points {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι} {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) {t : ι → ℝ} {T : ℝ} (hT : 0 ≤ T) (ht : ∀ i ∈ R, |t i| ≤ T) {Sk : Finset ℕ} {X : ℕ}
    (hSk : Sk ⊆ Finset.Icc 2 X) (c : ℕ → ℂ) :
    ∑ i ∈ R, ‖pv Sk c (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ ^ 2 ≤ LSX q T X * ∑ k ∈ Sk, ‖c k‖ ^ 2 := by
  classical
  rcases R.eq_empty_or_nonempty with hR | ⟨i₀, -⟩
  · rw [hR, Finset.sum_empty]
    exact mul_nonneg (LSX_nonneg q hT X) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have : Nonempty ι := ⟨i₀⟩
  set g : DirichletCharacter ℂ q → ι := Function.invFunOn χ R with hg
  have hleft : ∀ i ∈ R, g (χ i) = i := fun i hi => hinj.leftInvOn_invFunOn (Finset.mem_coe.2 hi)
  have hγ : ∀ ψ ∈ R.image χ, |(fun ψ => -t (g ψ)) ψ| ≤ T := by
    intro ψ hψ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hψ
    simp only [hleft j hj, abs_neg]
    exact ht j hj
  have h := ls_pv_dyadic hSk c q hT (R.image χ) (fun _ => 0) (fun ψ => -t (g ψ))
    (fun _ _ => ⟨le_refl _, by norm_num⟩) hγ
  rw [Finset.sum_image (fun i hi j hj hij => hinj (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) hij)] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i hi => ?_) h
  simp only [hleft i hi]

/-- **The product trick at the points, squared**: for `χ` injective on `R`, `T ≥ 0` and `|t_i| ≤ T`, if
`|F(χ_i, −it_i)| ≥ V > 0` for every `i ∈ R`, with `F`
supported on `[2, N′]`, then for any polynomial `E` on `[1, Z]`,
`Σ_{i∈R}|E(χ_i, −it_i)|² ≤ V^{−2}L(N′Z)·τ·Σ|b_n|²·Σ|e_m|²` with `d(k) ≤ τ` for `k ≤ N′Z`
(round 526's `pv_mul`, `mass_mulCo_le` and `ls_points`). -/
lemma prod_trick_points {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) {t : ι → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ht : ∀ i ∈ R, |t i| ≤ T) {S M : Finset ℕ} {N' Z : ℕ} (hS : S ⊆ Finset.Icc 2 N') (hM : M ⊆ Finset.Icc 1 Z)
    (b e : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ i ∈ R, V ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖) {τ : ℝ}
    (hτ : ∀ k, k ≤ N' * Z → (k.divisors.card : ℝ) ≤ τ) :
    ∑ i ∈ R, ‖pv M e (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ ^ 2 ≤
      (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2))) := by
  have hS0 : 0 ∉ S := fun h => by have := (Finset.mem_Icc.1 (hS h)).1; omega
  have hM0 : 0 ∉ M := fun h => by have := (Finset.mem_Icc.1 (hM h)).1; omega
  have hsupp : mulSupp S M ⊆ Finset.Icc 2 (N' * Z) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    obtain ⟨h11, h12⟩ := Finset.mem_Icc.1 (hS h1)
    obtain ⟨h21, h22⟩ := Finset.mem_Icc.1 (hM h2)
    exact Finset.mem_Icc.2 ⟨by nlinarith, Nat.mul_le_mul h12 h22⟩
  set s : ι → ℂ := fun i => ((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I with hs
  have hpt : ∀ i ∈ R, ‖pv M e (χ i) (s i)‖ ^ 2 ≤ (V ^ 2)⁻¹ * ‖pv (mulSupp S M) (mulCo S M b e) (χ i) (s i)‖ ^ 2 := by
    intro i hi
    rw [← pv_mul, norm_mul, mul_pow, ← mul_assoc]
    have h2 : V ^ 2 ≤ ‖pv S b (χ i) (s i)‖ ^ 2 := pow_le_pow_left₀ hV.le (hbig i hi) 2
    have h3 : 1 ≤ (V ^ 2)⁻¹ * ‖pv S b (χ i) (s i)‖ ^ 2 := by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith
    have h4 : 0 ≤ ‖pv M e (χ i) (s i)‖ ^ 2 := sq_nonneg _
    nlinarith
  calc ∑ i ∈ R, ‖pv M e (χ i) (s i)‖ ^ 2
      ≤ ∑ i ∈ R, (V ^ 2)⁻¹ * ‖pv (mulSupp S M) (mulCo S M b e) (χ i) (s i)‖ ^ 2 := Finset.sum_le_sum hpt
    _ = (V ^ 2)⁻¹ * ∑ i ∈ R, ‖pv (mulSupp S M) (mulCo S M b e) (χ i) (s i)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (V ^ 2)⁻¹ * (LSX q T (N' * Z) * ∑ k ∈ mulSupp S M, ‖mulCo S M b e k‖ ^ 2) := by
        gcongr; exact ls_points hinj hT ht hsupp _
    _ ≤ (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * ∑ m ∈ M, ‖e m‖ ^ 2))) := by
        have := LSX_nonneg q hT (N' * Z)
        gcongr
        exact mass_mulCo_le hS0 hM0 b e (fun k hk => hτ k (Finset.mem_Icc.1 (hsupp hk)).2)

/-! ### The dual sums of the pairs at the points -/

/-- **The dual sum of a pair at the point of the first character**:
`|D_{ik}(u)| = |Σ_{m≤Z}e_{k,u}(m)χ_i(m)m^{it_i}|` with `e_{k,u}(m) = conj(χ_k(m)m^{−1/2+i(u+t_k)})`
(round 526's `dualS_eq_conj_pv` at `a = a′ = 0`, `g = −t_i`, `g′ = −t_k`, `κ = 1/2`, `v = u`). -/
lemma norm_dualS_pair {q : ℕ} (χi χk : DirichletCharacter ℂ q) (ti tk : ℝ) (Z : ℕ) (u : ℝ) :
    ‖dualS (χi * χk⁻¹)⁻¹ Z ((1 / 2 : ℝ) + (u - ((ti - tk : ℝ) : ℂ)) * I)‖ =
      ‖pv (Finset.Icc 1 Z) (dualCo χk (1 / 2) 0 (-tk) u) χi (((0 : ℝ) : ℂ) + ((-ti : ℝ) : ℂ) * I)‖ := by
  have e : ((1 / 2 : ℝ) : ℂ) + (u - ((ti - tk : ℝ) : ℂ)) * I =
      (((0 + 0 : ℝ) : ℂ) + ((-ti - -tk : ℝ) : ℂ) * I) + (((1 / 2 - 2 * 0 : ℝ) : ℂ) + u * I) := by
    push_cast; ring
  rw [e, dualS_eq_conj_pv χi χk Z 0 0 (-ti) (-tk) (1 / 2) u, Complex.norm_conj]

/-- `H_Z = Σ_{m≤Z} 1/m`. -/
def HZ (Z : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 Z, ((m : ℝ))⁻¹

/-- `Σ_{m≤Z}|e_{k,u}(m)|² ≤ H_Z` (round 526's `norm_dualCo_le`). -/
lemma mass_dualCo_half {q : ℕ} (χk : DirichletCharacter ℂ q) (tk u : ℝ) (Z : ℕ) :
    ∑ m ∈ Finset.Icc 1 Z, ‖dualCo χk (1 / 2) 0 (-tk) u m‖ ^ 2 ≤ HZ Z := by
  unfold HZ
  refine Finset.sum_le_sum fun m hm => ?_
  have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.1 hm).1; omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have h1 := norm_dualCo_le χk (1 / 2) 0 (-tk) u hm0
  calc ‖dualCo χk (1 / 2) 0 (-tk) u m‖ ^ 2 ≤ ((m : ℝ) ^ (1 / 2 - 1 + 0 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ((m : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmr.le, ← Real.rpow_neg_one]; norm_num

/-- The weight `|H(1/2 + iu)|`. -/
def wH (u : ℝ) : ℝ := ‖H ((1 / 2 : ℝ) + u * I)‖

lemma wH_nonneg (u : ℝ) : 0 ≤ wH u := norm_nonneg _

/-- `I_H = ∫|H(1/2 + iu)| du`. -/
def IH : ℝ := ∫ u : ℝ, wH u

lemma IH_nonneg : 0 ≤ IH := integral_nonneg wH_nonneg

lemma integrable_wH : Integrable wH := by
  unfold wH
  have h := integrable_H_line (1 / 2) 0
  refine (h.congr (Eventually.of_forall fun u => ?_)).norm
  simp

lemma integrable_wH_mul {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hgB : ∀ u, ‖g u‖ ≤ B) :
    Integrable fun u => wH u * g u := by
  have hc : Continuous wH := continuous_H_half.norm
  refine (integrable_wH.mul_const B).mono' (hc.mul hg).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Real.norm_of_nonneg (wH_nonneg u)]
  exact mul_le_mul_of_nonneg_left (hgB u) (wH_nonneg u)

/-- The dual sum of a pair, `|D_{ik}(u)|`. -/
def Dp {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) (u : ℝ) : ℝ :=
  ‖dualS (χ i * (χ k)⁻¹)⁻¹ Z ((1 / 2 : ℝ) + (u - ((t i - t k : ℝ) : ℂ)) * I)‖

lemma Dp_nonneg {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) (u : ℝ) :
    0 ≤ Dp χ t Z i k u := norm_nonneg _

lemma Dp_le {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) (u : ℝ) :
    Dp χ t Z i k u ≤ Z :=
  norm_dualS_le _ Z (by simp; norm_num)

lemma continuous_Dp {ι : Type*} {q : ℕ} (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ) (Z : ℕ) (i k : ι) :
    Continuous (Dp χ t Z i k) :=
  (continuous_dualS_line _ Z (1 / 2) (t i - t k)).norm

/-- **The mass of the dual sums over all pairs, at one height**: for `χ` injective on `R`, `|t_i| ≤ T`, `F` on
`[2, N′]` with `|F(χ_i, −it_i)| ≥ V > 0` on `R`, and `d(k) ≤ τ` for `k ≤ N′Z`,
`Σ_{i,k∈R}|D_{ik}(u)|² ≤ |R|·V^{−2}L(N′Z)·τ·Σ|b_n|²·H_Z`. -/
lemma sum_Dp_sq_le {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) {t : ι → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ht : ∀ i ∈ R, |t i| ≤ T) {S : Finset ℕ} {N' Z : ℕ} (hS : S ⊆ Finset.Icc 2 N') (b : ℕ → ℂ) {V : ℝ}
    (hV : 0 < V) (hbig : ∀ i ∈ R, V ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖) {τ : ℝ}
    (hτ : ∀ k, k ≤ N' * Z → (k.divisors.card : ℝ) ≤ τ) (u : ℝ) :
    ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤
      R.card * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z)))) := by
  have hτ0 : 0 ≤ τ := by have := hτ 0 (Nat.zero_le _); simpa using this
  have hk : ∀ k ∈ R, ∑ i ∈ R, Dp χ t Z i k u ^ 2 ≤
      (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z))) := by
    intro k _
    simp only [Dp, norm_dualS_pair]
    refine (prod_trick_points hinj hT ht hS (Finset.Subset.refl _) b _ hV hbig hτ).trans ?_
    have := LSX_nonneg q hT (N' * Z)
    have hb0 : 0 ≤ ∑ n ∈ S, ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    gcongr
    exact mass_dualCo_half (χ k) (t k) u Z
  rw [Finset.sum_comm]
  calc ∑ k ∈ R, ∑ i ∈ R, Dp χ t Z i k u ^ 2
      ≤ ∑ _k ∈ R, (V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z))) := Finset.sum_le_sum hk
    _ = R.card * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The off-diagonal mass of the Gram matrix -/

/-- The tail bound of round 642's `norm_gram_le` at `|τ| ≤ 2T`. -/
def Bmax (q : ℕ) (N T : ℝ) (Z K : ℕ) : ℝ :=
  2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
    (N * Z) ^ (-(K : ℝ)) * (1 + 2 * T) ^ (K + 1) * IK K

lemma Bmax_nonneg (q : ℕ) {N T : ℝ} (hN : 0 ≤ N) (hT : 0 ≤ T) (Z K : ℕ) : 0 ≤ Bmax q N T Z K := by
  unfold Bmax; have := CGK_pos K; have := EQh_pos q; have := IK_nonneg K; positivity

/-- **A Gram entry, squared**: for `χ_i ≠ χ_k`, `|t_i|, |t_k| ≤ T` and `Z, K ≥ 1`,
`|G(i, k)|² ≤ N·Q₀(q)²(∫|H(1/2 + iu)||D_{ik}(u)| du)² + B²` with `B` the tail bound at `|τ| ≤ 2T`
(round 642's `norm_gram_le`, `(a + b)² ≤ 2(a² + b²)` and `2(2π)^{−2} ≤ 1`). -/
lemma gram_sq_le {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {i k : ι} (hik : χ i ≠ χ k) {T : ℝ} (hti : |t i| ≤ T) (htk : |t k| ≤ T) {Z K : ℕ} (hZ : 1 ≤ Z)
    (hK : 1 ≤ K) :
    ‖gramP N χ t i k‖ ^ 2 ≤ N * Q0 q ^ 2 * (∫ u : ℝ, wH u * Dp χ t Z i k u) ^ 2 + Bmax q N T Z K ^ 2 := by
  have hT : 0 ≤ T := (abs_nonneg _).trans hti
  set J := ∫ u : ℝ, wH u * Dp χ t Z i k u with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun u => mul_nonneg (wH_nonneg u) (Dp_nonneg χ t Z i k u)
  have h : ‖gramP N χ t i k‖ ≤ (2 * Real.pi)⁻¹ * (N ^ (1 / 2 : ℝ) * Q0 q * J +
      2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N * Z) ^ (-(K : ℝ)) * (1 + |t i - t k|) ^ (K + 1) * IK K) :=
    norm_gram_le hN χ t hik hZ hK
  have htail : 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
      (N * Z) ^ (-(K : ℝ)) * (1 + |t i - t k|) ^ (K + 1) * IK K ≤ Bmax q N T Z K := by
    unfold Bmax
    have h1 : |t i - t k| ≤ 2 * T := (abs_sub _ _).trans (by linarith)
    have := CGK_pos K; have := EQh_pos q; have := IK_nonneg K
    gcongr
  set a := N ^ (1 / 2 : ℝ) * Q0 q * J with ha
  have ha0 : 0 ≤ a := by have := Q0_nonneg q; positivity
  set B := Bmax q N T Z K with hB
  have hB0 : 0 ≤ B := Bmax_nonneg q hN.le hT Z K
  have h2 : ‖gramP N χ t i k‖ ≤ (2 * Real.pi)⁻¹ * (a + B) :=
    h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity))
  have hpi : (2 * Real.pi)⁻¹ ^ 2 * 2 ≤ 1 := by
    have := Real.pi_gt_three
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]; nlinarith
  have hN2 : (N ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
  have hsq : a ^ 2 = N * Q0 q ^ 2 * J ^ 2 := by rw [ha, mul_pow, mul_pow, hN2]
  calc ‖gramP N χ t i k‖ ^ 2 ≤ ((2 * Real.pi)⁻¹ * (a + B)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = (2 * Real.pi)⁻¹ ^ 2 * (a + B) ^ 2 := by rw [mul_pow]
    _ ≤ (2 * Real.pi)⁻¹ ^ 2 * (2 * (a ^ 2 + B ^ 2)) := by gcongr; nlinarith [sq_nonneg (a - B)]
    _ = ((2 * Real.pi)⁻¹ ^ 2 * 2) * (a ^ 2 + B ^ 2) := by ring
    _ ≤ 1 * (a ^ 2 + B ^ 2) := by gcongr
    _ = N * Q0 q ^ 2 * J ^ 2 + B ^ 2 := by rw [one_mul, hsq]

/-- **The off-diagonal mass of the Gram matrix, explicitly**: for `χ` injective on `R`, `|t_i| ≤ T`, `N > 0`,
`F = Σ_{n∈S}b_nχ(n)n^{it}` on `S ⊆ [2, N′]` with `|F(χ_i, t_i)| ≥ V > 0` for every `i ∈ R`, `Z, K ≥ 1` and
`d(k) ≤ τ` for `k ≤ N′Z`,
`‖E‖_F² ≤ N·Q₀(q)²I_H²·|R|·V^{−2}L(N′Z)·τ·Σ|b_n|²·H_Z + |R|²B²`. -/
theorem frobOff_le {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {R : Finset ι} {χ : ι → DirichletCharacter ℂ q}
    (hinj : Set.InjOn χ R) {t : ι → ℝ} {T N : ℝ} (hT : 0 ≤ T) (hN : 0 < N) (ht : ∀ i ∈ R, |t i| ≤ T)
    {S : Finset ℕ} {N' : ℕ} (hS : S ⊆ Finset.Icc 2 N') (b : ℕ → ℂ) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ i ∈ R, V ≤ ‖∑ n ∈ S, b n * χ i n * (n : ℂ) ^ ((t i : ℂ) * I)‖) {Z K : ℕ} (hZ : 1 ≤ Z)
    (hK : 1 ≤ K) {τ : ℝ} (hτ : ∀ k, k ≤ N' * Z → (k.divisors.card : ℝ) ≤ τ) :
    frobOff N R χ t ≤ N * Q0 q ^ 2 * IH ^ 2 * (R.card * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) *
        (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z))))) + (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 := by
  classical
  have hbig' : ∀ i ∈ R, V ≤ ‖pv S b (χ i) (((0 : ℝ) : ℂ) + ((-t i : ℝ) : ℂ) * I)‖ := by
    intro i hi
    refine (hbig i hi).trans (le_of_eq ?_)
    unfold pv
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
    push_cast; ring
  set W := (R.card : ℝ) * ((V ^ 2)⁻¹ * (LSX q T (N' * Z) * (τ * ((∑ n ∈ S, ‖b n‖ ^ 2) * HZ Z)))) with hW
  have hWu : ∀ u, ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤ W := fun u =>
    sum_Dp_sq_le hinj hT ht hS b hV hbig' hτ u
  have hB := Bmax_nonneg q hN.le hT Z K
  have hQ := Q0_nonneg q
  have hIH := IH_nonneg
  have hi2 : ∀ i k, Integrable fun u => wH u * Dp χ t Z i k u := fun i k =>
    integrable_wH_mul (continuous_Dp χ t Z i k) fun u => by
      rw [Real.norm_of_nonneg (Dp_nonneg χ t Z i k u)]; exact Dp_le χ t Z i k u
  have hi3 : ∀ i k, Integrable fun u => wH u * Dp χ t Z i k u ^ 2 := fun i k =>
    integrable_wH_mul ((continuous_Dp χ t Z i k).pow 2) fun u => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (Dp_nonneg χ t Z i k u) (Dp_le χ t Z i k u) 2
  have hpair : ∀ i ∈ R, ∀ k ∈ R, (if i = k then 0 else ‖gramP N χ t i k‖ ^ 2) ≤
      N * Q0 q ^ 2 * IH * (∫ u, wH u * Dp χ t Z i k u ^ 2) + Bmax q N T Z K ^ 2 := by
    intro i hi k hk
    have hint0 : 0 ≤ ∫ u, wH u * Dp χ t Z i k u ^ 2 :=
      integral_nonneg fun u => mul_nonneg (wH_nonneg u) (sq_nonneg _)
    split_ifs with hik
    · positivity
    · have hχ : χ i ≠ χ k := fun h => hik (hinj (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hk) h)
      have hcs : (∫ u, wH u * Dp χ t Z i k u) ^ 2 ≤ IH * ∫ u, wH u * Dp χ t Z i k u ^ 2 :=
        integral_sq_le wH_nonneg (Dp_nonneg χ t Z i k) integrable_wH (hi2 i k) (hi3 i k)
      refine (gram_sq_le hN χ t hχ (ht i hi) (ht k hk) hZ hK).trans ?_
      have h1 := mul_le_mul_of_nonneg_left hcs (show 0 ≤ N * Q0 q ^ 2 by positivity)
      linarith [h1, show N * Q0 q ^ 2 * (IH * ∫ u, wH u * Dp χ t Z i k u ^ 2) =
        N * Q0 q ^ 2 * IH * ∫ u, wH u * Dp χ t Z i k u ^ 2 by ring]
  have hswap : ∑ i ∈ R, ∑ k ∈ R, (∫ u, wH u * Dp χ t Z i k u ^ 2) =
      ∫ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 := by
    have e : ∀ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 =
        ∑ i ∈ R, ∑ k ∈ R, wH u * Dp χ t Z i k u ^ 2 := by
      intro u; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hi3 i k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => hi3 i k)]
  have hint : ∫ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤ IH * W := by
    have hl : Integrable fun u => wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 := by
      have e : (fun u => wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2) =
          fun u => ∑ i ∈ R, ∑ k ∈ R, wH u * Dp χ t Z i k u ^ 2 := by
        funext u; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
      rw [e]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hi3 i k
    calc ∫ u, wH u * ∑ i ∈ R, ∑ k ∈ R, Dp χ t Z i k u ^ 2 ≤ ∫ u, wH u * W :=
          integral_mono hl (integrable_wH.mul_const W) fun u => mul_le_mul_of_nonneg_left (hWu u) (wH_nonneg u)
      _ = IH * W := by rw [integral_mul_const]; rfl
  calc frobOff N R χ t = ∑ i ∈ R, ∑ k ∈ R, (if i = k then 0 else ‖gramP N χ t i k‖ ^ 2) := rfl
    _ ≤ ∑ i ∈ R, ∑ k ∈ R, (N * Q0 q ^ 2 * IH * (∫ u, wH u * Dp χ t Z i k u ^ 2) + Bmax q N T Z K ^ 2) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk => hpair i hi k hk
    _ = N * Q0 q ^ 2 * IH * (∑ i ∈ R, ∑ k ∈ R, (∫ u, wH u * Dp χ t Z i k u ^ 2)) +
          (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
        ring
    _ ≤ N * Q0 q ^ 2 * IH * (IH * W) + (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 := by
        rw [hswap]; gcongr
    _ = N * Q0 q ^ 2 * IH ^ 2 * W + (R.card : ℝ) ^ 2 * Bmax q N T Z K ^ 2 := by ring

end LinnikCGLFrob

#print axioms LinnikCGLFrob.ls_points
#print axioms LinnikCGLFrob.prod_trick_points
#print axioms LinnikCGLFrob.sum_Dp_sq_le
#print axioms LinnikCGLFrob.gram_sq_le
#print axioms LinnikCGLFrob.frobOff_le
