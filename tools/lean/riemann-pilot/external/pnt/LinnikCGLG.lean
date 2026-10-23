/-
# Round 680: the majorant of their `J(f⃗)`, Plancherel, and its Fourier transform (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li prove their Proposition 8.1 (round 662's displayed hypothesis `LinnikCGLJ.CGLP81`) from their Lemma 8.2.
Its proof first rescales `f⃗` (line 2623), then: "Let ψ₁(x) be a smooth bump function supported on |x| ≪ 1, such
that ψ₁(m₃/M₃) majorizes the summation condition |m₃| ≪ M₃. Then we can bound the inner double sum in J(f⃗) by"
(lines 2623–2625; spaces restored, the line-break hyphen removed, the subscripts transcribed, the arrow over `f`
written `f⃗`), followed by their `g_a(u)`, the sum over `b`, `|m₁| ∼ M₁`, `m₂ ∼ M₂` and `m₃ ∈ ℤ` of
`ψ₁(m₃/M₃)f_b((m₁u + m₃)/m₂)(am₁ + bm₂ + m₃, q)` (lines 2626–2643). Then: "By applying Plancherel’s theorem for the
choice of M₁, M₂, M₃ that achieves the supremum, we obtain" (lines 2644–2645; the same allowances)
`J(f⃗) ≤ Σ_a∫|g_a(u)|² du = Σ_a∫|ĝ_a(ξ)|² dξ` (lines 2646–2658), and the change of variables `u = ũ − m₃/m₁` gives
`ĝ_a` (lines 2659–2715).

The stack's form.
* `ψ₁(m₃/M₃)` is `ψ̃₀(m₃/L)` (round 656's `psi0`, `1` on `[−1, 1]` and `0` off `(−2, 2)`), for any `L` with
  `κM₃ ≤ L`. One majorant then serves every `M₃` with `κM₃ ≤ L`, which is the monotonicity their footnote 6 notes:
  "as the larger M₃ is, the greater the inner double sum in J(f⃗) is." (lines 3515–3516; the same allowances). The
  sums over `m₁`, `m₂` and `m₃` are the finite sets `P1 M₁`, `P2 M₂` and `P3 L`; for `L > 0`, `ψ̃₀(m₃/L)` vanishes
  off `P3 L`.
* `g_a` is smooth with compact support, so it is a Schwartz function (Mathlib's `HasCompactSupport.toSchwartzMap`),
  and Mathlib's `SchwartzMap.integral_norm_sq_fourier` is their Plancherel step.
* Each term's transform is an affine change of variables (`fourier_comp_affine`).

Plain statements.
* `mem_P1`, `mem_P2`: the ranges `M₁ < |m₁| ≤ 2M₁` and `M₂ < m₂ ≤ 2M₂`. `psi0_div_eq_zero`: for `L > 0`,
  `ψ̃₀(m₃/L) = 0` for `m₃ ∉ P3 L`.
* `ga`, `gJ_nonneg`, `gJ_le_ga`: for `f ≥ 0` and `κM₃ ≤ L`, `0 ≤ gJ f (setJ M₁ M₂ M₃ κ) a u ≤ g_a(u)`.
* `ga_eq_zero`, `hasCompactSupport_ga`: for `f_b` that are `0` for `|u| > A` and `M₁ > 0`, `g_a(u) = 0` for
  `|u| > (2|A|M₂ + ⌈2L⌉ + 1)/M₁`. `contDiff_ga`: `g_a` is smooth when every `f_b` is.
* `integrable_ga_sq`, `Jint_le_ga`: for smooth, nonnegative `f_b` that are `0` for `|u| > A`, `M₁ > 0` and
  `κM₃ ≤ L`, `Jint f M₁ M₂ M₃ κ ≤ Σ_a∫g_a(u)² du`.
* `integral_sq_ga`: for smooth `f_b` that are `0` for `|u| > A` and `M₁ > 0`, `∫g_a(u)² du = ∫|ĝ_a(ξ)|² dξ`.
* `integrable_exp_smul`, `fourier_finset_sum`, `fourier_const_mul'`: the linearity of `𝓕` on integrable functions.
* `fourier_comp_affine`: for `c ≠ 0` and `e > 0`, `𝓕(g((cu + d)/e))(ξ) = (e/|c|)e(dξ/c)ĝ(eξ/c)`.
* `fC`, `integrable_term`, `fourier_ga`: for smooth `f_b` that are `0` for `|u| > A` and `M₁ > 0`,
  `ĝ_a(ξ) = Σ_bΣ_{m₁,m₂}(m₂/|m₁|)f̂_b(m₂ξ/m₁)Σ_{m₃}ψ̃₀(m₃/L)(am₁ + bm₂ + m₃, q)e(m₃ξ/m₁)`.

The file imports `LinnikCGLS3.lean`.
-/

import LinnikCGLS3

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLG

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLJ

/-! ### The ranges -/

/-- Their `|m₁| ∼ M₁`: the integers with `M₁ < |m₁| ≤ 2M₁`. -/
def P1 (M₁ : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉).filter fun m => M₁ < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M₁

lemma mem_P1 {M₁ : ℝ} (m : ℤ) : m ∈ P1 M₁ ↔ M₁ < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M₁ := by
  unfold P1
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2⟩
    have c := Int.le_ceil (2 * M₁)
    have a := abs_le.mp h2
    refine ⟨⟨?_, ?_⟩, h1, h2⟩
    · have : -((⌈2 * M₁⌉ : ℤ) : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast this
    · have : (m : ℝ) ≤ ((⌈2 * M₁⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this

/-- Their `m₂ ∼ M₂`: the integers with `M₂ < m₂ ≤ 2M₂`. -/
def P2 (M₂ : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉).filter fun m => M₂ < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M₂

lemma mem_P2 {M₂ : ℝ} (m : ℤ) : m ∈ P2 M₂ ↔ M₂ < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M₂ := by
  unfold P2
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · rintro ⟨h1, h2⟩
    have c := Int.le_ceil (2 * M₂)
    refine ⟨⟨?_, ?_⟩, h1, h2⟩
    · have : -((⌈2 * M₂⌉ : ℤ) : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast this
    · have : (m : ℝ) ≤ ((⌈2 * M₂⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this

/-- The range of `m₃`: `|m₃| ≤ ⌈2L⌉`. -/
def P3 (L : ℝ) : Finset ℤ := Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉

/-- `ψ̃₀(m₃/L) = 0` off `P3 L`, for `L > 0`. -/
lemma psi0_div_eq_zero {L : ℝ} (hL : 0 < L) {m : ℤ} (hm : m ∉ P3 L) : psi0 (m / L) = 0 := by
  apply psi0_eq_zero
  unfold P3 at hm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
  have hc := Int.le_ceil (2 * L)
  rw [abs_div, abs_of_pos hL, le_div_iff₀ hL]
  rcases hm with h | h
  · have h1 : (m : ℝ) + 1 ≤ -((⌈2 * L⌉ : ℤ) : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    rw [abs_of_neg (by linarith)]
    linarith
  · have h1 : ((⌈2 * L⌉ : ℤ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    rw [abs_of_pos (by linarith)]
    linarith

/-! ### The majorant -/

/-- Their `g_a(u)`, with `ψ₁(m₃/M₃)` taken as `ψ̃₀(m₃/L)`:
`Σ_bΣ_{m₁∈P1}Σ_{m₂∈P2}Σ_{m₃∈P3}ψ̃₀(m₃/L)f_b((m₁u + m₃)/m₂)(am₁ + bm₂ + m₃, q)`. -/
def ga {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) (M₁ M₂ L : ℝ) (a : (ZMod q)ˣ) (u : ℝ) : ℝ :=
  ∑ b : (ZMod q)ˣ, ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, ∑ m₃ ∈ P3 L,
    psi0 (m₃ / L) * f b ((m₁ * u + m₃) / m₂) * gJw a b (m₁, m₂, m₃)

/-- The inner double sum of their `J(f⃗)` is nonnegative for `f ≥ 0`. -/
lemma gJ_nonneg {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) (S : Finset (ℤ × ℤ × ℤ))
    (a : (ZMod q)ˣ) (u : ℝ) : 0 ≤ gJ f S a u :=
  Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun m _ => mul_nonneg (hf b _) (gJw_nonneg a b m)

/-- **The majorant**: for `f ≥ 0` and `κM₃ ≤ L`, `gJ f (setJ M₁ M₂ M₃ κ) a u ≤ g_a(u)`. -/
lemma gJ_le_ga {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ M₃ κ L : ℝ}
    (hL : κ * M₃ ≤ L) (a : (ZMod q)ˣ) (u : ℝ) :
    gJ f (setJ M₁ M₂ M₃ κ) a u ≤ ga f M₁ M₂ L a u := by
  unfold gJ ga
  refine Finset.sum_le_sum fun b _ => ?_
  set F : ℤ × ℤ × ℤ → ℝ := fun m => psi0 (m.2.2 / L) * f b ((m.1 * u + m.2.2) / m.2.1) * gJw a b m with hF
  have hsub : setJ M₁ M₂ M₃ κ ⊆ P1 M₁ ×ˢ (P2 M₂ ×ˢ P3 L) := by
    intro m hm
    rw [mem_setJ] at hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    rw [Finset.mem_product, Finset.mem_product, mem_P1, mem_P2]
    refine ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ?_⟩
    unfold P3
    rw [Finset.mem_Icc]
    have hc := Int.le_ceil (2 * L)
    have hL0 : 0 ≤ L := le_trans (le_trans (abs_nonneg _) h5) hL
    have a5 := abs_le.mp (h5.trans hL)
    constructor
    · have : -((⌈2 * L⌉ : ℤ) : ℝ) ≤ (m.2.2 : ℝ) := by linarith
      exact_mod_cast this
    · have : (m.2.2 : ℝ) ≤ ((⌈2 * L⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  have hone : ∀ m ∈ setJ M₁ M₂ M₃ κ, psi0 (m.2.2 / L) = 1 := by
    intro m hm
    rw [mem_setJ] at hm
    apply psi0_eq_one
    have h5 := hm.2.2.2.2
    rcases eq_or_lt_of_le (le_trans (le_trans (abs_nonneg _) h5) hL) with hL0 | hL0
    · have : |(m.2.2 : ℝ)| ≤ 0 := hL0 ▸ (h5.trans hL)
      rw [abs_nonpos_iff.mp this, zero_div, abs_zero]
      norm_num
    · rw [abs_div, abs_of_pos hL0, div_le_one hL0]
      exact h5.trans hL
  calc ∑ m ∈ setJ M₁ M₂ M₃ κ, f b ((m.1 * u + m.2.2) / m.2.1) * gJw a b m
      = ∑ m ∈ setJ M₁ M₂ M₃ κ, F m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [hF]; simp only; rw [hone m hm, one_mul]
    _ ≤ ∑ m ∈ P1 M₁ ×ˢ (P2 M₂ ×ˢ P3 L), F m := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => ?_
        rw [hF]
        exact mul_nonneg (mul_nonneg (psi0_nonneg _) (hf b _)) (gJw_nonneg a b m)
    _ = ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, ∑ m₃ ∈ P3 L,
          psi0 (m₃ / L) * f b ((m₁ * u + m₃) / m₂) * gJw a b (m₁, m₂, m₃) := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Finset.sum_product]

/-! ### Support and smoothness -/

/-- `g_a(u) = 0` for `|u| > (2|A|M₂ + ⌈2L⌉ + 1)/M₁`, when every `f_b` is `0` for `|u| > A` and `M₁ > 0`. -/
lemma ga_eq_zero {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0)
    {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (a : (ZMod q)ˣ) {u : ℝ}
    (hu : (2 * |A| * M₂ + ⌈2 * L⌉ + 1) / M₁ < |u|) : ga f M₁ M₂ L a u = 0 := by
  unfold ga
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun m₁ hm₁ => Finset.sum_eq_zero fun m₂ hm₂ =>
    Finset.sum_eq_zero fun m₃ hm₃ => ?_
  rw [mem_P1] at hm₁
  rw [mem_P2] at hm₂
  unfold P3 at hm₃
  rw [Finset.mem_Icc] at hm₃
  have h3 : |(m₃ : ℝ)| ≤ ((⌈2 * L⌉ : ℤ) : ℝ) := by
    rw [abs_le]
    constructor
    · have : (-⌈2 * L⌉ : ℤ) ≤ m₃ := hm₃.1
      have : -((⌈2 * L⌉ : ℤ) : ℝ) ≤ (m₃ : ℝ) := by exact_mod_cast this
      linarith
    · exact_mod_cast hm₃.2
  have hm2 : (0 : ℝ) < m₂ := by linarith [hm₂.1]
  have hR : 2 * |A| * M₂ + ⌈2 * L⌉ + 1 < M₁ * |u| := by
    rw [div_lt_iff₀ hM₁] at hu; linarith
  have hm1u : M₁ * |u| ≤ |(m₁ : ℝ)| * |u| := mul_le_mul_of_nonneg_right hm₁.1.le (abs_nonneg _)
  have key : |A| < |((m₁ : ℝ) * u + m₃) / m₂| := by
    rw [abs_div, abs_of_pos hm2, lt_div_iff₀ hm2]
    have t1 : |(m₁ : ℝ) * u| - |(m₃ : ℝ)| ≤ |(m₁ : ℝ) * u + m₃| := by
      have := abs_sub_abs_le_abs_sub ((m₁ : ℝ) * u) (-(m₃ : ℝ))
      rwa [abs_neg, sub_neg_eq_add] at this
    rw [abs_mul] at t1
    have t2 : |A| * m₂ ≤ 2 * |A| * M₂ := by nlinarith [abs_nonneg A, hm₂.2]
    linarith
  rw [hA b _ (lt_of_le_of_lt (le_abs_self A) key), mul_zero, zero_mul]

/-- For `f_b` that are `0` for `|u| > A` and `M₁ > 0`, `g_a` has compact support. -/
lemma hasCompactSupport_ga {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (a : (ZMod q)ˣ) :
    HasCompactSupport (fun u => (ga f M₁ M₂ L a u : ℂ)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((2 * |A| * M₂ + ⌈2 * L⌉ + 1) / M₁)) fun u hu => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hu
  rw [ga_eq_zero hA hM₁ a hu, Complex.ofReal_zero]

/-- `g_a` is smooth when every `f_b` is. -/
lemma contDiff_ga {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) (M₁ M₂ L : ℝ)
    (a : (ZMod q)ˣ) : ContDiff ℝ ∞ (ga f M₁ M₂ L a) := by
  have e : ga f M₁ M₂ L a = fun u => ∑ b : (ZMod q)ˣ, ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, ∑ m₃ ∈ P3 L,
      psi0 (m₃ / L) * f b ((m₁ * u + m₃) / m₂) * gJw a b (m₁, m₂, m₃) := rfl
  rw [e]
  refine ContDiff.sum fun b _ => ContDiff.sum fun m₁ _ => ContDiff.sum fun m₂ _ => ContDiff.sum fun m₃ _ => ?_
  refine (contDiff_const.mul ((hfs b).comp ?_)).mul contDiff_const
  exact ((contDiff_const.mul contDiff_id).add contDiff_const).div_const _

/-! ### `J(f⃗) ≤ Σ_a∫g_a²` -/

/-- For smooth `f_b` that are `0` for `|u| > A` and `M₁ > 0`, `g_a²` is integrable. -/
lemma integrable_ga_sq {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (a : (ZMod q)ˣ) :
    Integrable (fun u => ga f M₁ M₂ L a u ^ 2) := by
  have hc : Continuous (fun u => ga f M₁ M₂ L a u ^ 2) := ((contDiff_ga hfs M₁ M₂ L a).continuous).pow 2
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((2 * |A| * M₂ + ⌈2 * L⌉ + 1) / M₁)) fun u hu => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hu
  rw [ga_eq_zero hA hM₁ a hu]
  norm_num

/-- **`J(f⃗) ≤ Σ_a∫g_a²`**: for smooth, nonnegative `f_b` that are `0` for `|u| > A`, `M₁ > 0` and `κM₃ ≤ L`,
`Jint f M₁ M₂ M₃ κ ≤ Σ_a∫g_a(u)² du`. -/
theorem Jint_le_ga {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b))
    (hf : ∀ b u, 0 ≤ f b u) {A : ℝ} (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ M₃ κ L : ℝ} (hM₁ : 0 < M₁)
    (hL : κ * M₃ ≤ L) :
    Jint f M₁ M₂ M₃ κ ≤ ∑ a : (ZMod q)ˣ, ∫ u, ga f M₁ M₂ L a u ^ 2 := by
  unfold Jint
  rw [← integral_finsetSum _ fun a _ => integrable_ga_sq hfs hA hM₁ a]
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => Finset.sum_nonneg fun a _ => sq_nonneg _)
    (integrable_finsetSum _ fun a _ => integrable_ga_sq hfs hA hM₁ a) (Eventually.of_forall fun u => ?_)
  refine Finset.sum_le_sum fun a _ => ?_
  exact pow_le_pow_left₀ (gJ_nonneg hf _ a u) (gJ_le_ga hf hL a u) 2

/-! ### Plancherel -/

/-- **Plancherel for `g_a`**: for smooth `f_b` that are `0` for `|u| > A` and `M₁ > 0`,
`∫g_a(u)² du = ∫|ĝ_a(ξ)|² dξ`. -/
theorem integral_sq_ga {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (a : (ZMod q)ˣ) :
    ∫ u, ga f M₁ M₂ L a u ^ 2 = ∫ ξ, ‖𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ‖ ^ 2 := by
  have hsm : ContDiff ℝ ∞ (fun u => (ga f M₁ M₂ L a u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_ga hfs M₁ M₂ L a)
  have h := SchwartzMap.integral_norm_sq_fourier ((hasCompactSupport_ga hA hM₁ a).toSchwartzMap hsm)
  rw [SchwartzMap.fourier_coe] at h
  have e : ⇑((hasCompactSupport_ga hA hM₁ a).toSchwartzMap hsm) = fun u => (ga f M₁ M₂ L a u : ℂ) := rfl
  rw [e] at h
  rw [h]
  congr 1
  funext u
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The Fourier transform of `g_a` -/

/-- The integrand of `𝓕F` is integrable when `F` is. -/
lemma integrable_exp_smul {F : ℝ → ℂ} (hF : Integrable F) (w : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * I) • F v) := by
  refine hF.norm.mono' ?_ (Eventually.of_forall fun v => le_of_eq ?_)
  · exact (Continuous.aestronglyMeasurable (f := fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * I))
      (by fun_prop)).smul hF.aestronglyMeasurable
  · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `𝓕` of a finite sum of integrable functions. -/
lemma fourier_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ) (hF : ∀ i ∈ s, Integrable (F i)) (w : ℝ) :
    𝓕 (fun v => ∑ i ∈ s, F i v) w = ∑ i ∈ s, 𝓕 (F i) w := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, Finset.smul_sum]
  exact integral_finsetSum s fun i hi => integrable_exp_smul (hF i hi) w

/-- `𝓕` of a constant multiple. -/
lemma fourier_const_mul' (c : ℂ) (F : ℝ → ℂ) (w : ℝ) : 𝓕 (fun v => c * F v) w = c * 𝓕 F w := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext v
  ring

/-- **An affine change of variables**: `𝓕(g((cu + d)/e))(ξ) = (e/|c|)e(dξ/c)ĝ(eξ/c)` for `c ≠ 0` and `e > 0`. -/
lemma fourier_comp_affine (g : ℝ → ℂ) {c e : ℝ} (hc : c ≠ 0) (he : 0 < e) (d ξ : ℝ) :
    𝓕 (fun u => g ((c * u + d) / e)) ξ =
      ((e / |c| : ℝ) : ℂ) * Complex.exp (2 * π * I * (d * ξ / c)) * 𝓕 g (e * ξ / c) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set H : ℝ → ℂ := fun w => Complex.exp (↑(-2 * π * ((e * w - d) / c) * ξ) * I) • g w with hH
  have key : (fun u : ℝ => Complex.exp (↑(-2 * π * u * ξ) * I) • g ((c * u + d) / e)) =
      fun u => H (c / e * u + d / e) := by
    funext u
    simp only [hH]
    have e1 : (c * u + d) / e = c / e * u + d / e := by field_simp
    have e2 : (e * (c / e * u + d / e) - d) / c = u := by field_simp; ring
    rw [e1, e2]
  rw [key]
  have h1 := Measure.integral_comp_mul_left (fun x : ℝ => H (x + d / e)) (c / e)
  rw [h1, integral_add_right_eq_self H (d / e)]
  have hce : |(c / e)⁻¹| = e / |c| := by rw [inv_div, abs_div, abs_of_pos he]
  rw [hce, Complex.real_smul, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext w
  simp only [hH, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp
  ring

/-- The complex-valued `f_b`. -/
def fC {q : ℕ} (f : (ZMod q)ˣ → ℝ → ℝ) (b : (ZMod q)ˣ) (u : ℝ) : ℂ := (f b u : ℂ)

/-- For smooth `f_b` that are `0` for `|u| > A`, `c ≠ 0` and `e > 0`, `u ↦ f_b((cu + d)/e)` is integrable. -/
lemma integrable_term {q : ℕ} {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) (b : (ZMod q)ˣ) {c d e : ℝ} (hc : c ≠ 0) (he : 0 < e) :
    Integrable (fun u => fC f b ((c * u + d) / e)) := by
  have hcont : Continuous (fun u => fC f b ((c * u + d) / e)) :=
    Complex.continuous_ofReal.comp ((hfs b).continuous.comp
      (((continuous_const.mul continuous_id).add continuous_const).div_const _))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((|A| * e + |d|) / |c|)) fun u hu => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le, div_lt_iff₀ (abs_pos.mpr hc)] at hu
  have t1 : |c * u| - |d| ≤ |c * u + d| := by
    have := abs_sub_abs_le_abs_sub (c * u) (-d)
    rwa [abs_neg, sub_neg_eq_add] at this
  rw [abs_mul] at t1
  have key : |A| < |(c * u + d) / e| := by
    rw [abs_div, abs_of_pos he, lt_div_iff₀ he]
    linarith
  simp only [fC]
  rw [hA b _ (lt_of_le_of_lt (le_abs_self A) key), Complex.ofReal_zero]

/-- **The Fourier transform of `g_a`**: for smooth `f_b` that are `0` for `|u| > A` and `M₁ > 0`,
`ĝ_a(ξ) = Σ_bΣ_{m₁,m₂}(m₂/|m₁|)f̂_b(m₂ξ/m₁)Σ_{m₃}ψ̃₀(m₃/L)(am₁ + bm₂ + m₃, q)e(m₃ξ/m₁)`. -/
theorem fourier_ga {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (a : (ZMod q)ˣ) (ξ : ℝ) :
    𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ =
      ∑ b : (ZMod q)ˣ, ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) *
        𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁) * ∑ m₃ ∈ P3 L, ((psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) : ℝ) : ℂ) *
          Complex.exp (2 * π * I * ((m₃ : ℝ) * ξ / (m₁ : ℝ))) := by
  have hm1 : ∀ m₁ ∈ P1 M₁, (m₁ : ℝ) ≠ 0 := fun m₁ hm₁ => by
    rw [mem_P1] at hm₁
    intro h; rw [h, abs_zero] at hm₁; linarith [hm₁.1]
  have hm2 : ∀ m₂ ∈ P2 M₂, (0 : ℝ) < m₂ := fun m₂ hm₂ => by
    rw [mem_P2] at hm₂; linarith [hm₂.1]
  have e0 : (fun u => (ga f M₁ M₂ L a u : ℂ)) = fun u => ∑ b : (ZMod q)ˣ, ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂,
      ∑ m₃ ∈ P3 L, ((psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) : ℝ) : ℂ) * fC f b ((m₁ * u + m₃) / m₂) := by
    funext u
    unfold ga fC
    push_cast
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
      Finset.sum_congr rfl fun m₃ _ => ?_
    ring
  rw [e0]
  have hI : ∀ b m₁, m₁ ∈ P1 M₁ → ∀ m₂, m₂ ∈ P2 M₂ → ∀ m₃ : ℤ,
      Integrable (fun u => ((psi0 (m₃ / L) * gJw a b (m₁, m₂, m₃) : ℝ) : ℂ) * fC f b ((m₁ * u + m₃) / m₂)) :=
    fun b m₁ hm₁ m₂ hm₂ m₃ => (integrable_term hfs hA b (hm1 m₁ hm₁) (hm2 m₂ hm₂)).const_mul _
  rw [fourier_finset_sum _ _ fun b _ => integrable_finsetSum _ fun m₁ hm₁ => integrable_finsetSum _ fun m₂ hm₂ =>
    integrable_finsetSum _ fun m₃ _ => hI b m₁ hm₁ m₂ hm₂ m₃]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [fourier_finset_sum _ _ fun m₁ hm₁ => integrable_finsetSum _ fun m₂ hm₂ =>
    integrable_finsetSum _ fun m₃ _ => hI b m₁ hm₁ m₂ hm₂ m₃]
  refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
  rw [fourier_finset_sum _ _ fun m₂ hm₂ => integrable_finsetSum _ fun m₃ _ => hI b m₁ hm₁ m₂ hm₂ m₃]
  refine Finset.sum_congr rfl fun m₂ hm₂ => ?_
  rw [fourier_finset_sum _ _ fun m₃ _ => hI b m₁ hm₁ m₂ hm₂ m₃, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m₃ _ => ?_
  rw [fourier_const_mul', fourier_comp_affine (fC f b) (hm1 m₁ hm₁) (hm2 m₂ hm₂)]
  ring

end LinnikCGLG

#print axioms LinnikCGLG.gJ_le_ga
#print axioms LinnikCGLG.Jint_le_ga
#print axioms LinnikCGLG.integral_sq_ga
#print axioms LinnikCGLG.fourier_comp_affine
#print axioms LinnikCGLG.fourier_ga
