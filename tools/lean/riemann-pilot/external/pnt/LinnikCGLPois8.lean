/-
# Round 680: the Poisson expansion of `ĝ_a` in residue classes (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li continue the proof of their Lemma 8.2: "the last sum, according to the Poisson summation formula, is"
(lines 2715–2716; spaces restored) `Σ_{d mod q}(am₁ + bm₂ + d, q)Σ_{m₃≡d (mod q)}ψ₁(m₃/M₃)e(m₃ξ/m₁) =
Σ_{d mod q}(am₁ + bm₂ + d, q)Σ_{n∈ℤ}(M₃/q)e_q(dn)ψ̂₁((n/q − ξ/m₁)M₃)` (lines 2717–2745, transcribed), and "Lastly, we
map d → d + am₁ + bm₂." (line 2746; spaces restored, the subscripts transcribed). This file proves that expansion for
round 680's `LinnikCGLG.ga`, with `ψ₁(m₃/M₃)` as `ψ̃₀(m₃/L)` and their `ψ̂₁` as `𝓕psiC`.

The stack's form.
* The residues are `d ∈ {0, …, q − 1}`, and `m₃ = d + qk` (`sum_P3_residue`, round 646's `sum_colsP_residue` over
  `ℤ`).
* Along a residue class, `Σ_kψ̃₀((d + qk)/L)e((d + qk)β) = (L/q)Σ_nψ̂₀(L(n/q − β))e(nd/q)` (`poisson_residue`):
  round 646's `poisson_scaled` for `g(z) = ψ̃₀(z)e(zLβ)`, whose transform is `ψ̂₀(η − Lβ)` (`fourier_mul_exp`).
* The map `d → d + am₁ + bm₂` turns `Σ_d(am₁ + bm₂ + d, q)e_q(dn)` into `e_q(−n(am₁ + bm₂))c_q(n)`, with
  `c_q(n) = Σ_{d∈ℤ/qℤ}(d, q)e_q(nd)` (`cqg`, `sum_gcd_shift`).

Plain statements, with `q ≥ 1` (`[NeZero q]`) and `e_q(x) = e^{2πix/q}` (Mathlib's `ZMod.stdAddChar`).
* `summable_of_decay`: `Σ_{n∈ℤ}h(n)` converges when `|h(n)|(1 + |cn + β|)² ≤ C` for every `n` and `c > 0`.
* `norm_fourier_psiC_sq_le`, `summable_psiC_lattice`: `|ψ̂₀(x)|(1 + |x|)² ≤ 2(∫ψ̃₀ + D₂/(2π)²)`, and
  `Σ_nw(n)ψ̂₀(L(n/q − β))` converges for `|w(n)| ≤ B`, `L > 0` and `q > 0`.
* `fourier_mul_exp`, `sq_mul_norm_fourier_shift_le`, `poisson_residue`: `𝓕(ψ(z)e(zβ))(η) = ψ̂(η − β)`;
  `η²|ψ̂₀(η − β)| ≤ 2D₂/(2π)² + 2β²∫ψ̃₀`; and for `L > 0` and `q > 0`,
  `Σ_kψ̃₀((a + qk)/L)e((a + qk)β) = Σ_n(L/q)ψ̂₀(L(n/q − β))e(na/q)`.
* `sum_P3_residue`: for `q > 0`, `G` vanishing off a finite `s ⊆ ℤ` and `W` with `W(m) = W(m mod q)`,
  `Σ_{m∈s}W(m)G(m) = Σ_{d<q}W(d)Σ_kG(d + qk)`.
* `cqg`, `sum_gcd_shift`, `sum_range_gcd`: `c_q(n) = Σ_{d∈ℤ/qℤ}(d, q)e_q(nd)`, and
  `Σ_{d<q}(x₀ + d, q)e(nd/q) = e_q(−nx₀)c_q(n)`.
* `poisson_S`: for `L > 0` and `x₀ ∈ ℤ/qℤ`, `Σ_{m₃∈P3 L}ψ̃₀(m₃/L)(x₀ + m₃, q)e(m₃β) =
  Σ_{n∈ℤ}(L/q)ψ̂₀(L(n/q − β))e_q(−nx₀)c_q(n)`.
* `fourier_ga_poisson`: for smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0` and `L > 0`,
  `ĝ_a(ξ) = Σ_bΣ_{m₁,m₂}(m₂/|m₁|)f̂_b(m₂ξ/m₁)Σ_{n∈ℤ}(L/q)ψ̂₀(L(n/q − ξ/m₁))e_q(−n(am₁ + bm₂))c_q(n)`.

The file imports `LinnikCGLG.lean`.
-/

import LinnikCGLG

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLPois8

open LinnikCGLPoisson LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLJ LinnikCGLG

/-! ### Summability -/

/-- `Σ_{n∈ℤ}h(n)` converges when `|h(n)|(1 + |cn + β|)² ≤ C` for every `n` and `c > 0`. -/
lemma summable_of_decay {h : ℤ → ℂ} {C c β : ℝ} (hc : 0 < c) (hh : ∀ n : ℤ, ‖h n‖ * (1 + |c * n + β|) ^ 2 ≤ C) :
    Summable h := by
  have hg : Summable fun n : ℤ => C / c ^ 2 * (1 / |(n : ℝ) + β / c| ^ (2 : ℝ)) :=
    ((Real.summable_one_div_int_add_rpow (β / c) 2).2 (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : {n : ℤ | (n : ℝ) + β / c = 0}.Finite := by
    refine Set.Subsingleton.finite fun n₁ h₁ n₂ h₂ => ?_
    have h₁' : (n₁ : ℝ) + β / c = 0 := h₁
    have h₂' : (n₂ : ℝ) + β / c = 0 := h₂
    have : (n₁ : ℝ) = n₂ := by linarith
    exact_mod_cast this
  filter_upwards [hfin.compl_mem_cofinite] with n hn
  have hn' : (n : ℝ) + β / c ≠ 0 := hn
  have hpos : 0 < |(n : ℝ) + β / c| := abs_pos.mpr hn'
  have e1 : |c * n + β| = c * |(n : ℝ) + β / c| := by
    rw [show c * (n : ℝ) + β = c * ((n : ℝ) + β / c) by field_simp, abs_mul, abs_of_pos hc]
  have h1 := hh n
  rw [e1] at h1
  have h2 : (c * |(n : ℝ) + β / c|) ^ 2 ≤ (1 + c * |(n : ℝ) + β / c|) ^ 2 := by
    have : 0 ≤ c * |(n : ℝ) + β / c| := by positivity
    nlinarith
  have h3 : ‖h n‖ * (c * |(n : ℝ) + β / c|) ^ 2 ≤ C :=
    le_trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) h1
  rw [Real.rpow_two, show C / c ^ 2 * (1 / |(n : ℝ) + β / c| ^ 2) = C / (c * |(n : ℝ) + β / c|) ^ 2 by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  exact h3

/-- `|ψ̂₀(x)|(1 + |x|)² ≤ 2(∫ψ̃₀ + D₂/(2π)²)`. -/
lemma norm_fourier_psiC_sq_le (x : ℝ) :
    ‖𝓕 psiC x‖ * (1 + |x|) ^ 2 ≤ 2 * ((∫ y, psi0 y) + Dpsi 2 / (2 * π) ^ 2) := by
  have h1 := fourier_psiC_decay 2 x
  have h2 := norm_fourier_psiC_le x
  have hpi : 0 < (2 * π) ^ 2 := by positivity
  have h1' : x ^ 2 * ‖𝓕 psiC x‖ ≤ Dpsi 2 / (2 * π) ^ 2 := by
    rw [le_div_iff₀ hpi]
    have : (2 * π * |x|) ^ 2 = (2 * π) ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
    rw [this] at h1
    linarith
  have hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_nonneg (1 - |x|), sq_abs x]
  have hn := norm_nonneg (𝓕 psiC x)
  calc ‖𝓕 psiC x‖ * (1 + |x|) ^ 2 ≤ ‖𝓕 psiC x‖ * (2 * (1 + x ^ 2)) := mul_le_mul_of_nonneg_left hsq hn
    _ = 2 * (‖𝓕 psiC x‖ + x ^ 2 * ‖𝓕 psiC x‖) := by ring
    _ ≤ 2 * ((∫ y, psi0 y) + Dpsi 2 / (2 * π) ^ 2) := by gcongr

/-- `Σ_nw(n)ψ̂₀(L(n/q − β))` converges for bounded `w`, `L > 0` and `q ≥ 1`. -/
lemma summable_psiC_lattice {L : ℝ} (hL : 0 < L) {q : ℕ} (hq : 0 < q) (β : ℝ) {B : ℝ} (w : ℤ → ℂ)
    (hw : ∀ n, ‖w n‖ ≤ B) : Summable fun n : ℤ => w n * 𝓕 psiC (L * (n / q - β)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine summable_of_decay (C := B * (2 * ((∫ y, psi0 y) + Dpsi 2 / (2 * π) ^ 2))) (c := L / q) (β := -(L * β))
    (by positivity) fun n => ?_
  have e : L / q * n + -(L * β) = L * (n / q - β) := by field_simp; ring
  rw [e, norm_mul, mul_assoc]
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hw 0)
  exact mul_le_mul (hw n) (norm_fourier_psiC_sq_le _) (by positivity) hB

/-! ### Poisson along a residue class -/

/-- `𝓕(ψ(z)e(zβ))(η) = ψ̂(η − β)`. -/
lemma fourier_mul_exp (ψ : ℝ → ℂ) (β η : ℝ) :
    𝓕 (fun z => ψ z * Complex.exp (2 * π * I * (z * β))) η = 𝓕 ψ (η - β) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext z
  simp only [smul_eq_mul]
  rw [mul_comm (ψ z), ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The decay that Poisson summation needs: `η²|ψ̂₀(η − β)| ≤ 2D₂/(2π)² + 2β²∫ψ̃₀`. -/
lemma sq_mul_norm_fourier_shift_le (β η : ℝ) :
    η ^ 2 * ‖𝓕 psiC (η - β)‖ ≤ 2 * (Dpsi 2 / (2 * π) ^ 2) + 2 * β ^ 2 * ∫ x, psi0 x := by
  have h1 := fourier_psiC_decay 2 (η - β)
  have h2 := norm_fourier_psiC_le (η - β)
  have hpi : 0 < (2 * π) ^ 2 := by positivity
  have h1' : (η - β) ^ 2 * ‖𝓕 psiC (η - β)‖ ≤ Dpsi 2 / (2 * π) ^ 2 := by
    rw [le_div_iff₀ hpi]
    have : (2 * π * |η - β|) ^ 2 = (2 * π) ^ 2 * (η - β) ^ 2 := by rw [mul_pow, sq_abs]
    rw [this] at h1
    linarith
  have hsq : η ^ 2 ≤ 2 * (η - β) ^ 2 + 2 * β ^ 2 := by nlinarith [sq_nonneg (η - 2 * β)]
  have hn := norm_nonneg (𝓕 psiC (η - β))
  calc η ^ 2 * ‖𝓕 psiC (η - β)‖ ≤ (2 * (η - β) ^ 2 + 2 * β ^ 2) * ‖𝓕 psiC (η - β)‖ :=
        mul_le_mul_of_nonneg_right hsq hn
    _ = 2 * ((η - β) ^ 2 * ‖𝓕 psiC (η - β)‖) + 2 * β ^ 2 * ‖𝓕 psiC (η - β)‖ := by ring
    _ ≤ 2 * (Dpsi 2 / (2 * π) ^ 2) + 2 * β ^ 2 * ∫ x, psi0 x := by
        gcongr

/-- **Poisson along a residue class**: for `L > 0` and `q ≥ 1`,
`Σ_kψ̃₀((a + qk)/L)e((a + qk)β) = Σ_n(L/q)ψ̂₀(L(n/q − β))e(na/q)`. -/
theorem poisson_residue {L : ℝ} (hL : 0 < L) {q : ℕ} (hq : 0 < q) (a β : ℝ) :
    ∑' k : ℤ, psiC ((a + q * k) / L) * Complex.exp (2 * π * I * ((a + q * k) * β)) =
      ∑' n : ℤ, ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - β)) * Complex.exp (2 * π * I * n * (a / q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set g : ℝ → ℂ := fun z => psiC z * Complex.exp (2 * π * I * ((z : ℂ) * ((L * β : ℝ) : ℂ))) with hg
  have hgc : Continuous g := by
    rw [hg]
    exact (Complex.continuous_ofReal.comp continuous_psi0).mul (by fun_prop)
  have hgv : ∀ x, x ∉ Icc (-2 : ℝ) 2 → g x = 0 := by
    intro x hx
    rw [hg]
    simp only
    have : 2 ≤ |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [psiC, psi0_eq_zero this, Complex.ofReal_zero, zero_mul]
  have hdec : ∀ η : ℝ, η ^ 2 * ‖𝓕 g η‖ ≤ 2 * (Dpsi 2 / (2 * π) ^ 2) + 2 * (L * β) ^ 2 * ∫ x, psi0 x := by
    intro η
    rw [hg, fourier_mul_exp]
    exact sq_mul_norm_fourier_shift_le (L * β) η
  have hc : 0 < (q : ℝ) / L := by positivity
  have h := poisson_scaled hgc hgv hdec hc (a / q)
  have e1 : ∀ k : ℤ, g ((q : ℝ) / L * (a / q + k)) =
      psiC ((a + q * k) / L) * Complex.exp (2 * π * I * ((a + q * k) * β)) := by
    intro k
    rw [hg]
    simp only
    have e : (q : ℝ) / L * (a / q + k) = (a + q * k) / L := by field_simp
    rw [e]
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    congr 2
    push_cast
    field_simp
  simp only [e1] at h
  rw [h]
  refine tsum_congr fun n => ?_
  have e3 : (n : ℝ) / ((q : ℝ) / L) - L * β = L * (n / q - β) := by field_simp
  rw [hg, fourier_mul_exp, inv_div, e3]
  push_cast
  ring

/-! ### Residue classes -/

/-- **A finite sum over `ℤ` by residue classes**: for `q > 0`, `G` vanishing off a finite set `s` and `W` of period
`q`, `Σ_{m∈s}W(m)G(m) = Σ_{d<q}W(d)Σ_kG(d + qk)`. -/
lemma sum_P3_residue {q : ℕ} (hq : 0 < q) (s : Finset ℤ) {G : ℤ → ℂ} (hG : ∀ m, m ∉ s → G m = 0) (W : ℤ → ℂ)
    (hW : ∀ m, W m = W (m % q)) :
    ∑ m ∈ s, W m * G m = ∑ d ∈ Finset.range q, W d * ∑' k : ℤ, G (d + q * k) := by
  classical
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m : ℤ => (m % q).toNat) (t := Finset.range q)
    (fun m _ => by
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg m hq'.ne'
      have h2 := Int.emod_lt_of_pos m hq'
      omega)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d < q := Finset.mem_range.1 hd
  set t := s.filter (fun m : ℤ => (m % (q : ℤ)).toNat = d) with ht
  have hres : ∀ m ∈ t, m % q = d := by
    intro m hm
    have h := (Finset.mem_filter.1 hm).2
    have h1 := Int.emod_nonneg m hq'.ne'
    omega
  have hWd : ∀ m ∈ t, W m * G m = W d * G m := by
    intro m hm; rw [hW m, hres m hm]
  rw [Finset.sum_congr rfl hWd, ← Finset.mul_sum]
  congr 1
  have hdecomp : ∀ m ∈ t, (d : ℤ) + q * (m / q) = m := by
    intro m hm
    have h := Int.emod_add_mul_ediv m q
    rw [hres m hm] at h
    exact h
  have hinj : Set.InjOn (fun m : ℤ => m / q) t := by
    intro m₁ hm₁ m₂ hm₂ h
    have h1 := hdecomp m₁ hm₁
    have h2 := hdecomp m₂ hm₂
    simp only at h
    rw [h] at h1
    exact h1.symm.trans h2
  have hvan : ∀ k : ℤ, k ∉ t.image (fun m : ℤ => m / q) → G (d + q * k) = 0 := by
    intro k hk
    by_contra hne
    apply hk
    have hmem : (d : ℤ) + q * k ∈ s := by
      by_contra h; exact hne (hG _ h)
    refine Finset.mem_image.2 ⟨d + q * k, Finset.mem_filter.2 ⟨hmem, ?_⟩, ?_⟩
    · have : ((d : ℤ) + q * k) % q = d := by
        rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hd')]
      rw [this]; simp
    · rw [Int.add_mul_ediv_left _ _ hq'.ne', Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hd'),
        zero_add]
  rw [tsum_eq_sum hvan, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hdecomp m hm]

/-! ### The shift `d → d + am₁ + bm₂` -/

/-- Their `Σ_{d mod q}(d, q)e_q(dn)`: `c_q(n) = Σ_{d∈ℤ/qℤ}(d, q)e_q(nd)`. -/
def cqg (q : ℕ) [NeZero q] (n : ZMod q) : ℂ := ∑ d : ZMod q, ((Nat.gcd d.val q : ℕ) : ℂ) * ZMod.stdAddChar (n * d)

/-- **The shift**: for `q ≥ 1`, `Σ_{y∈ℤ/qℤ}(x₀ + y, q)e_q(ny) = e_q(−nx₀)c_q(n)`. -/
lemma sum_gcd_shift {q : ℕ} [NeZero q] (x₀ n : ZMod q) :
    ∑ y : ZMod q, ((Nat.gcd (x₀ + y).val q : ℕ) : ℂ) * ZMod.stdAddChar (n * y) =
      ZMod.stdAddChar (-(n * x₀)) * cqg q n := by
  unfold cqg
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft x₀) _ _ fun y => ?_
  simp only [Equiv.coe_addLeft]
  rw [mul_left_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- For `q ≥ 1`, `Σ_{d<q}(x₀ + d, q)e(nd/q) = e_q(−nx₀)c_q(n)`. -/
lemma sum_range_gcd {q : ℕ} [NeZero q] (x₀ : ZMod q) (n : ℤ) :
    ∑ d ∈ Finset.range q, ((Nat.gcd (x₀ + (d : ZMod q)).val q : ℕ) : ℂ) *
        Complex.exp (2 * π * I * n * ((d : ℝ) / q)) =
      ZMod.stdAddChar (-((n : ZMod q) * x₀)) * cqg q n := by
  rw [← sum_gcd_shift x₀ (n : ZMod q)]
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine (Finset.sum_bij (fun d _ => (d : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_)
  · intro d₁ h₁ d₂ h₂ h
    have h1 := Finset.mem_range.1 h₁
    have h2 := Finset.mem_range.1 h₂
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this
  · intro y _
    refine ⟨y.val, Finset.mem_range.2 (ZMod.val_lt y), ZMod.natCast_zmod_val y⟩
  · intro d hd
    congr 1
    have e : (n : ZMod q) * (d : ZMod q) = ((n * d : ℤ) : ZMod q) := by push_cast; ring
    rw [e, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    field_simp

/-! ### `S` by Poisson -/

/-- **Poisson in residue classes**: for `q ≥ 1`, `L > 0` and `x₀ ∈ ℤ/qℤ`,
`Σ_{m₃∈P3 L}ψ̃₀(m₃/L)(x₀ + m₃, q)e(m₃β) = Σ_n(L/q)ψ̂₀(L(n/q − β))e_q(−nx₀)c_q(n)`. -/
theorem poisson_S {q : ℕ} [NeZero q] {L : ℝ} (hL : 0 < L) (x₀ : ZMod q) (β : ℝ) :
    ∑ m₃ ∈ P3 L, ((psi0 (m₃ / L) * (Nat.gcd (x₀ + (m₃ : ZMod q)).val q : ℕ) : ℝ) : ℂ) *
        Complex.exp (2 * π * I * ((m₃ : ℝ) * β)) =
      ∑' n : ℤ, ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - β)) *
        (ZMod.stdAddChar (-((n : ZMod q) * x₀)) * cqg q n) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set G : ℤ → ℂ := fun m => psiC (m / L) * Complex.exp (2 * π * I * ((m : ℝ) * β)) with hG
  set W : ℤ → ℂ := fun m => ((Nat.gcd (x₀ + (m : ZMod q)).val q : ℕ) : ℂ) with hW
  have e0 : ∀ m₃ : ℤ, ((psi0 (m₃ / L) * (Nat.gcd (x₀ + (m₃ : ZMod q)).val q : ℕ) : ℝ) : ℂ) *
      Complex.exp (2 * π * I * ((m₃ : ℝ) * β)) = W m₃ * G m₃ := by
    intro m₃
    rw [hW, hG]
    simp only [psiC]
    push_cast
    ring
  simp_rw [e0]
  have hGv : ∀ m, m ∉ P3 L → G m = 0 := by
    intro m hm
    rw [hG]
    simp only [psiC]
    rw [psi0_div_eq_zero hL hm, Complex.ofReal_zero, zero_mul]
  have hWp : ∀ m, W m = W (m % q) := by
    intro m
    simp only [hW, ZMod.intCast_mod]
  rw [sum_P3_residue hq (P3 L) hGv W hWp]
  have hP : ∀ d : ℕ, ∑' k : ℤ, G (d + q * k) = ∑' n : ℤ, ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - β)) *
      Complex.exp (2 * π * I * n * ((d : ℝ) / q)) := by
    intro d
    rw [← poisson_residue hL hq (d : ℝ) β]
    refine tsum_congr fun k => ?_
    simp only [hG]
    push_cast
    ring_nf
  simp_rw [hP]
  have hsum : ∀ d ∈ Finset.range q, Summable fun n : ℤ => W d * (((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - β)) *
      Complex.exp (2 * π * I * n * ((d : ℝ) / q))) := by
    intro d _
    have hB : ∀ n : ℤ, ‖W d * ((L / q : ℝ) : ℂ) * Complex.exp (2 * π * I * n * ((d : ℝ) / q))‖ ≤
        ‖W d‖ * (L / q) := by
      intro n
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have : ‖Complex.exp (2 * π * I * n * ((d : ℝ) / q))‖ = 1 := by
        rw [show (2 * π * I * n * ((d : ℝ) / q) : ℂ) = ((2 * π * n * (d / q) : ℝ) : ℂ) * I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [this, mul_one]
    refine (summable_psiC_lattice hL hq β _ hB).congr fun n => ?_
    ring
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun n => ?_
  rw [← sum_range_gcd x₀ n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [hW, Int.cast_natCast]
  ring

/-! ### `ĝ_a` by Poisson -/

/-- **`ĝ_a` by Poisson in residue classes**: for smooth `f_b` that are `0` for `|u| > A`, `M₁ > 0` and `L > 0`,
`ĝ_a(ξ) = Σ_bΣ_{m₁,m₂}(m₂/|m₁|)f̂_b(m₂ξ/m₁)Σ_n(L/q)ψ̂₀(L(n/q − ξ/m₁))e_q(−n(am₁ + bm₂))c_q(n)`. -/
theorem fourier_ga_poisson {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hfs : ∀ b, ContDiff ℝ ∞ (f b)) {A : ℝ}
    (hA : ∀ b u, A < |u| → f b u = 0) {M₁ M₂ L : ℝ} (hM₁ : 0 < M₁) (hL : 0 < L) (a : (ZMod q)ˣ) (ξ : ℝ) :
    𝓕 (fun u => (ga f M₁ M₂ L a u : ℂ)) ξ =
      ∑ b : (ZMod q)ˣ, ∑ m₁ ∈ P1 M₁, ∑ m₂ ∈ P2 M₂, (((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) *
        𝓕 (fC f b) ((m₂ : ℝ) * ξ / m₁) * ∑' n : ℤ, ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - ξ / m₁)) *
          (ZMod.stdAddChar (-((n : ZMod q) * ((a : ZMod q) * (m₁ : ZMod q) + (b : ZMod q) * (m₂ : ZMod q)))) *
            cqg q n) := by
  rw [fourier_ga hfs hA hM₁ a ξ]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
  congr 1
  rw [← poisson_S hL ((a : ZMod q) * (m₁ : ZMod q) + (b : ZMod q) * (m₂ : ZMod q)) (ξ / m₁)]
  refine Finset.sum_congr rfl fun m₃ _ => ?_
  unfold gJw
  simp only
  congr 2
  push_cast
  ring

end LinnikCGLPois8

#print axioms LinnikCGLPois8.summable_of_decay
#print axioms LinnikCGLPois8.poisson_residue
#print axioms LinnikCGLPois8.sum_P3_residue
#print axioms LinnikCGLPois8.sum_range_gcd
#print axioms LinnikCGLPois8.poisson_S
#print axioms LinnikCGLPois8.fourier_ga_poisson
