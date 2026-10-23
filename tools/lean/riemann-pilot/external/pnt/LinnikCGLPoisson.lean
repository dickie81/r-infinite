/-
# Round 646: the Poisson expansion of the Gram entries in residue classes (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li expand the traces of `MM*` by Poisson summation in residue classes (their Lemmas 4.4 and 4.5). In the
proof of Lemma 4.5: "Performing Poisson summation in the n₁-sum gives", followed by a display that reads, on one line,
`Σ_{n₁∈ℤ}h_{t₁−t₂}(n₁/N)χ₁χ̄₂(n₁) = Σ_{a₁ mod q}Σ_{n₁∈ℤ, n₁≡a₁ mod q}h_{t₁−t₂}(n₁/N)χ₁χ̄₂(n₁) =
(N/q)Σ_{a₁ mod q}Σ_{m₁∈ℤ}ĥ_{t₁−t₂}(Nm₁/q)e_q(a₁m₁)χ₁χ̄₂(a₁)` (text layer lines 1059–1087; spaces restored, the sums and
their ranges, the hat, the large parentheses, the fractions and the subscripts transcribed). The conjugation bars over
`χ₂` are drawn rules, which the text layer drops: on page 13 pdfminer finds rules at y = 267.2 over the `χ` at
x = 208.1–215.5 and x = 415.9–423.3, and at y = 220.8 over the `χ` at x = 462.8–470.2
(`scratchpad/r661/probe/p13_210_280.txt`). This file proves that expansion for the stack's Gram entries (round 638's
`gramP`), with round 645's Lemma 4.3 (1) for the decay that Poisson summation needs. Their display carries no factor
`N^{iτ}`, which cancels in the cyclic products of the cubic trace; the stack keeps it in the entry.

Plain statement (`gram_poisson`). For `q ≥ 1`, `N > 0` and `τ = t_i − t_k`,
`G(i, k) = N^{iτ}Σ_{a<q}χ_i(a)conj(χ_k(a))Σ_{m∈ℤ}(N/q)ĥ_τ(Nm/q)e^{2πima/q}`, with `h_τ(u) = w(u)²u^{iτ}`.

Plain statement (`poisson_scaled`). For `g` continuous, vanishing outside `[A, B]`, with `ξ²|ĝ(ξ)| ≤ C` for all `ξ`,
and `c > 0`: `Σ_{m∈ℤ}g(c(x₀ + m)) = Σ_{m∈ℤ}c⁻¹ĝ(m/c)e^{2πimx₀}`.

* `fourier_comp_mul`: `𝓕(g(c·))(ξ) = c⁻¹𝓕g(ξ/c)` for `c > 0` (Mathlib's `Measure.integral_comp_mul_left`).
* `isBigO_of_vanish`, `poisson_scaled`: Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay` for `x ↦ g(cx)`.
* `Wt_vanish`, `continuous_Wt`, `sq_mul_norm_hhat_le`, `poisson_Wt`: the hypotheses for `g = h_τ` (round 645's
  `lemma43` at `K = 2` for the decay), and `Σ_m h_τ((a + qm)/N) = Σ_m (N/q)ĥ_τ(Nm/q)e^{2πima/q}`.
* `sum_colsP_residue`: a sum over `colsP N` of `ψ(n)φ(n/N)`, with `ψ` of period `q` and `φ` vanishing outside
  `[1, 2]`, regrouped by residue classes: `Σ_{a<q}ψ(a)Σ_m φ((a + qm)/N)`.
* `star_natCast_cpow`, `entP_mul_star`: `A_{i,n}conj(A_{k,n}) = N^{iτ}χ_i(n)conj(χ_k(n))h_τ(n/N)` for `n ≥ 1`.
* `gram_poisson`: the three together.

The file imports `LinnikCGLFourier.lean`.
-/

import LinnikCGLFourier

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff

noncomputable section

namespace LinnikCGLPoisson

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier

/-! ### Poisson summation, scaled -/

/-- `𝓕(g(c·))(ξ) = c⁻¹𝓕g(ξ/c)` for `c > 0`. -/
lemma fourier_comp_mul (g : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (fun x => g (c * x)) ξ = ((c⁻¹ : ℝ) : ℂ) * 𝓕 g (ξ / c) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have h := Measure.integral_comp_mul_left (fun y : ℝ => 𝐞 (-(y * (ξ / c))) • g y) c
  have e : (fun x : ℝ => 𝐞 (-(x * ξ)) • g (c * x)) = fun x : ℝ => 𝐞 (-(c * x * (ξ / c))) • g (c * x) := by
    funext x; congr 3; field_simp
  rw [e, h, abs_of_pos (inv_pos.2 hc), Complex.real_smul]

/-- A continuous function vanishing outside `[A, B]` is `O(|x|^{−2})` at infinity. -/
lemma isBigO_of_vanish {f : ℝ → ℂ} {A B : ℝ} (hf : ∀ x, x ∉ Icc A B → f x = 0) :
    f =O[cocompact ℝ] (|·| ^ (-2 : ℝ)) := by
  have hev : f =ᶠ[cocompact ℝ] fun _ => 0 := by
    filter_upwards [(isCompact_Icc (a := A) (b := B)).compl_mem_cocompact] with x hx using hf x hx
  exact hev.trans_isBigO (isBigO_zero _ _)

/-- **Poisson summation, scaled.** For `g` continuous, vanishing outside `[A, B]`, with `ξ²|𝓕g(ξ)| ≤ C`, and `c > 0`:
`Σ_m g(c(x₀ + m)) = c⁻¹Σ_m 𝓕g(m/c)e^{2πimx₀}` (Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay`). -/
theorem poisson_scaled {g : ℝ → ℂ} (hg : Continuous g) {A B : ℝ} (hsupp : ∀ x, x ∉ Icc A B → g x = 0) {C : ℝ}
    (hdec : ∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 g ξ‖ ≤ C) {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    ∑' m : ℤ, g (c * (x₀ + m)) =
      ∑' m : ℤ, ((c⁻¹ : ℝ) : ℂ) * 𝓕 g (m / c) * Complex.exp (2 * π * I * m * x₀) := by
  set f : ℝ → ℂ := fun x => g (c * x) with hfdef
  have hfc : Continuous f := hg.comp (continuous_const.mul continuous_id)
  have hfv : ∀ x, x ∉ Icc (A / c) (B / c) → f x = 0 := by
    intro x hx
    apply hsupp
    intro h
    apply hx
    rw [mem_Icc] at h ⊢
    constructor
    · rw [div_le_iff₀ hc]; linarith [h.1]
    · rw [le_div_iff₀ hc]; linarith [h.2]
  have hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-2 : ℝ)) := by
    have hC0 : 0 ≤ C := by have := hdec 0; simp at this; linarith
    refine IsBigO.of_bound (C * c) ?_
    filter_upwards [(isCompact_Icc (a := (-1 : ℝ)) (b := 1)).compl_mem_cocompact] with ξ hξ
    have hξ0 : ξ ≠ 0 := by
      intro h; apply hξ; rw [h]; constructor <;> norm_num
    have hF := fourier_comp_mul g hc ξ
    rw [← hfdef] at hF
    rw [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    have h1 := hdec (ξ / c)
    have hξ2 : 0 < ξ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]
    have e : (ξ / c) ^ 2 = ξ ^ 2 / c ^ 2 := by ring
    rw [e] at h1
    have h2 : ‖𝓕 g (ξ / c)‖ ≤ C * c ^ 2 / ξ ^ 2 := by
      rw [le_div_iff₀ hξ2]
      have : ξ ^ 2 / c ^ 2 * ‖𝓕 g (ξ / c)‖ ≤ C := h1
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
      linarith
    calc c⁻¹ * ‖𝓕 g (ξ / c)‖ ≤ c⁻¹ * (C * c ^ 2 / ξ ^ 2) := by gcongr
      _ = C * c * (ξ ^ 2)⁻¹ := by field_simp
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hfc (by norm_num : (1 : ℝ) < 2)
    (isBigO_of_vanish hfv) hFf x₀
  simp only [hfdef] at hP
  rw [hP]
  refine tsum_congr fun m => ?_
  rw [fourier_comp_mul g hc, fourier_coe_apply]
  congr 1
  congr 1; push_cast; ring

/-! ### `h_τ` in residue classes -/

lemma Wt_vanish (τ : ℝ) : ∀ x, x ∉ Icc (1 : ℝ) 2 → Wt τ x = 0 := by
  intro x hx
  rw [← F_zero]
  apply F_eq_zero
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · exact Or.inl h.le
  · exact Or.inr h.le

lemma continuous_Wt (τ : ℝ) : Continuous (Wt τ) := by rw [← F_zero]; exact continuous_F τ 0

/-- `ξ²|ĥ_τ(ξ)| ≤ C_2(1 + |τ|)²/(4π²)` (`lemma43` at `K = 2`). -/
lemma sq_mul_norm_hhat_le (τ ξ : ℝ) : ξ ^ 2 * ‖𝓕 (Wt τ) ξ‖ ≤ CF 2 * (1 + |τ|) ^ 2 / (4 * π ^ 2) := by
  have h := lemma43 τ 2 ξ
  have e : (2 * π * |ξ|) ^ 2 = 4 * π ^ 2 * ξ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
  rw [e] at h
  rw [le_div_iff₀ (by positivity)]
  calc ξ ^ 2 * ‖𝓕 (Wt τ) ξ‖ * (4 * π ^ 2) = 4 * π ^ 2 * ξ ^ 2 * ‖𝓕 (Wt τ) ξ‖ := by ring
    _ ≤ CF 2 * (1 + |τ|) ^ 2 := h

/-- **Poisson for `h_τ` along a residue class**: for `N, q > 0` and real `a`,
`Σ_m h_τ((a + qm)/N) = Σ_m (N/q)ĥ_τ(Nm/q)e^{2πima/q}`. -/
theorem poisson_Wt (τ : ℝ) {N : ℝ} (hN : 0 < N) {q : ℕ} (hq : 0 < q) (a : ℝ) :
    ∑' m : ℤ, Wt τ ((a + q * m) / N) =
      ∑' m : ℤ, ((N / q : ℝ) : ℂ) * 𝓕 (Wt τ) (N * m / q) * Complex.exp (2 * π * I * m * (a / q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : 0 < (q : ℝ) / N := by positivity
  have h := poisson_scaled (continuous_Wt τ) (Wt_vanish τ) (sq_mul_norm_hhat_le τ) hc (a / q)
  have e1 : ∀ m : ℤ, (q : ℝ) / N * (a / q + m) = (a + q * m) / N := by
    intro m; field_simp
  have e2 : ((q : ℝ) / N)⁻¹ = N / q := by rw [inv_div]
  have e3 : ∀ m : ℤ, (m : ℝ) / ((q : ℝ) / N) = N * m / q := by
    intro m; field_simp
  simp only [e1, e2, e3] at h
  refine h.trans (tsum_congr fun m => ?_)
  push_cast; ring

/-- **A finite sum over `colsP N` by residue classes**: for `φ` vanishing outside `[1, 2]`, `N, q > 0` and `ψ` of
period `q`, `Σ_{n∈colsP N}ψ(n)φ(n/N) = Σ_{a<q}ψ(a)Σ_m φ((a + qm)/N)`. -/
lemma sum_colsP_residue {φ : ℝ → ℂ} (hφ : ∀ x, x ∉ Icc (1 : ℝ) 2 → φ x = 0) {N : ℝ} (hN : 0 < N) {q : ℕ}
    (hq : 0 < q) (ψ : ℕ → ℂ) (hψ : ∀ n, ψ n = ψ (n % q)) :
    ∑ n ∈ colsP N, ψ n * φ (n / N) = ∑ a ∈ Finset.range q, ψ a * ∑' m : ℤ, φ ((a + q * m) / N) := by
  classical
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % q) (t := Finset.range q)
    (fun n _ => Finset.mem_range.2 (Nat.mod_lt _ hq))]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a < q := Finset.mem_range.1 ha
  set s := (colsP N).filter (fun n => n % q = a) with hs
  have hψa : ∀ n ∈ s, ψ n * φ (n / N) = ψ a * φ (n / N) := by
    intro n hn; rw [hψ n, (Finset.mem_filter.1 hn).2]
  rw [Finset.sum_congr rfl hψa, ← Finset.mul_sum]
  congr 1
  have hdecomp : ∀ n ∈ s, ((a : ℝ) + q * (((n / q : ℕ) : ℤ) : ℝ)) = n := by
    intro n hn
    have h1 := Nat.mod_add_div n q
    rw [(Finset.mem_filter.1 hn).2] at h1
    have h2 : ((a + q * (n / q) : ℕ) : ℝ) = n := by rw [h1]
    push_cast at h2 ⊢
    exact h2
  have hinj : Set.InjOn (fun n : ℕ => ((n / q : ℕ) : ℤ)) s := by
    intro n₁ hn₁ n₂ hn₂ h
    have h1 := hdecomp n₁ hn₁
    have h2 := hdecomp n₂ hn₂
    simp only at h
    rw [h] at h1
    exact_mod_cast h1.symm.trans h2
  have hvan : ∀ m : ℤ, m ∉ s.image (fun n : ℕ => ((n / q : ℕ) : ℤ)) → φ ((a + q * m) / N) = 0 := by
    intro m hm
    by_contra hne
    have hx : (a + q * (m : ℝ)) / N ∈ Icc (1 : ℝ) 2 := by
      by_contra h; exact hne (hφ _ h)
    rw [mem_Icc, le_div_iff₀ hN, div_le_iff₀ hN] at hx
    have hm0 : 0 ≤ m := by
      by_contra h
      have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have ha2 : (a : ℝ) < q := by exact_mod_cast ha'
      nlinarith
    apply hm
    refine Finset.mem_image.2 ⟨a + q * m.toNat, Finset.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
    · have hmr : ((m.toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_of_nonneg hm0
      have hn : ((a + q * m.toNat : ℕ) : ℝ) = a + q * m := by push_cast; rw [hmr]
      rw [colsP, Finset.mem_Icc]
      constructor
      · exact Nat.ceil_le.2 (by rw [hn]; linarith)
      · exact Nat.le_floor (by rw [hn]; linarith)
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']
    · have : (a + q * m.toNat) / q = m.toNat := by
        rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt ha', zero_add]
      rw [this]; exact Int.toNat_of_nonneg hm0
  rw [tsum_eq_sum hvan, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hdecomp n hn]

/-! ### The Gram entries -/

/-- `conj(n^{it}) = n^{−it}` for a natural number `n`. -/
lemma star_natCast_cpow (n : ℕ) (x : ℝ) : star ((n : ℂ) ^ ((x : ℂ) * I)) = (n : ℂ) ^ (-(x : ℂ) * I) := by
  have harg : (n : ℂ).arg ≠ π := by rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have h := Complex.cpow_conj (n : ℂ) ((x : ℂ) * I) harg
  rw [Complex.conj_natCast] at h
  have hc : (starRingEnd ℂ) ((x : ℂ) * I) = -(x : ℂ) * I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [hc] at h
  rw [h]; rfl

/-- **One term of a Gram entry**: `A_{i,n}conj(A_{k,n}) = N^{iτ}χ_i(n)conj(χ_k(n))h_τ(n/N)` with `τ = t_i − t_k`, for
`n ≥ 1` and `N > 0`. -/
lemma entP_mul_star {ι : Type*} {q : ℕ} {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)
    (i k : ι) {n : ℕ} (hn : 0 < n) :
    entP N χ t i n * star (entP N χ t k n) =
      (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * (χ i n * star (χ k n)) * Wt (t i - t k) (n / N) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcomb : (n : ℂ) ^ ((t i : ℂ) * I) * (n : ℂ) ^ (-(t k : ℂ) * I) =
      (n : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) := by
    rw [← Complex.cpow_add _ _ hn0]; congr 1; push_cast; ring
  have hsplit : (n : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) =
      (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * ((n / N : ℝ) : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) := by
    have h := Complex.mul_cpow_ofReal_nonneg hN.le (div_nonneg (Nat.cast_nonneg n) hN.le) (((t i - t k : ℝ) : ℂ) * I)
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have e : (N : ℂ) * ((n / N : ℝ) : ℂ) = n := by push_cast; field_simp
    rw [← h, e]
  unfold entP Wt Wc wsq
  rw [star_mul', star_mul', star_natCast_cpow, smul_eq_mul]
  have hw : star ((wCGL (n / N) : ℝ) : ℂ) = ((wCGL (n / N) : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hw]
  calc (wCGL (n / N) : ℂ) * χ i n * (n : ℂ) ^ ((t i : ℂ) * I) *
        ((wCGL (n / N) : ℂ) * star (χ k n) * (n : ℂ) ^ (-(t k : ℂ) * I))
      = ((wCGL (n / N) : ℂ) ^ 2) * (χ i n * star (χ k n)) *
          ((n : ℂ) ^ ((t i : ℂ) * I) * (n : ℂ) ^ (-(t k : ℂ) * I)) := by ring
    _ = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * (χ i n * star (χ k n)) *
          (((n / N : ℝ) : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * ((wCGL (n / N) ^ 2 : ℝ) : ℂ)) := by
        rw [hcomb, hsplit]; push_cast; ring

/-- **The Poisson expansion of a Gram entry in residue classes** (the method of Chen–Gupta–Li's Lemma 4.4 and the proof
of their Lemma 4.5): for `N > 0`, with `τ = t_i − t_k`,
`G(i, k) = N^{iτ}Σ_{a<q}χ_i(a)conj(χ_k(a))Σ_{m∈ℤ}(N/q)ĥ_τ(Nm/q)e^{2πima/q}`. -/
theorem gram_poisson {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) (i k : ι) :
    gramP N χ t i k = (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * ∑ a ∈ Finset.range q, (χ i a * star (χ k a)) *
      ∑' m : ℤ, ((N / q : ℝ) : ℂ) * 𝓕 (Wt (t i - t k)) (N * m / q) * Complex.exp (2 * π * I * m * (a / q)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold gramP
  have hpos : ∀ n ∈ colsP N, 0 < n := by
    intro n hn
    rw [colsP, Finset.mem_Icc] at hn
    exact lt_of_lt_of_le (Nat.ceil_pos.2 hN) hn.1
  rw [Finset.sum_congr rfl fun n hn => entP_mul_star hN χ t i k (hpos n hn)]
  have hre : ∀ n ∈ colsP N, (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * (χ i n * star (χ k n)) *
      Wt (t i - t k) (n / N) =
      (N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I) * ((χ i n * star (χ k n)) * Wt (t i - t k) (n / N)) :=
    fun n _ => by ring
  rw [Finset.sum_congr rfl hre, ← Finset.mul_sum]
  congr 1
  have hper : ∀ n : ℕ, χ i n * star (χ k n) = χ i (n % q : ℕ) * star (χ k (n % q : ℕ)) := by
    intro n; rw [ZMod.natCast_mod]
  rw [sum_colsP_residue (Wt_vanish _) hN hq (fun n => χ i n * star (χ k n)) hper]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [poisson_Wt _ hN hq]
  simp only [Complex.ofReal_natCast]

end LinnikCGLPoisson

#print axioms LinnikCGLPoisson.poisson_scaled
#print axioms LinnikCGLPoisson.poisson_Wt
#print axioms LinnikCGLPoisson.sum_colsP_residue
#print axioms LinnikCGLPoisson.entP_mul_star
#print axioms LinnikCGLPoisson.gram_poisson
