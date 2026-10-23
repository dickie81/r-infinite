/-
# Round 673: separated points, and the fractions of their Lemma 10.9 (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Their Lemma 10.9 (Small GCD terms): "We have Σ_{n₁,n₂∼N, (n₁n₂,q)=1, (n₁,n₂)≤D} |R(n₁/n₂, n₁n₂^{−1})|³ ⪅_ϵ
(DqT + N²)|W|^{1/2}E(W)^{1/2}." (text layer lines 5070–5082; spaces restored; the sum, fraction, large bars, which the
text layer encodes as four form feeds each, large parentheses, subscripts and exponents transcribed). Their proof
splits the sum by `d = (n₁, n₂)` and by the residue `a`, and "It follows from Lemma 10.8 that, for (a,q) = 1," (line
5090) the cubes over one class are bounded by an integral of `|R(v,a)|³` near the fractions, their (10.1). Then: "Hence,
the fractions n′₁/n′₂ that appear in the inner sum are qd²/N²-separated. This separation enables us to bound the inner
sum in (10.1) by ⪅ 1 + N²/(qTd²)." (lines 5186–5189; spaces restored; the subscripts and exponents transcribed). This
file proves the separation and the bound that the separation gives; their Lemma 10.8 (quoted in round 668's header) is
not formalized as stated, and its part is taken by round 668's local average without a window.

The stack's form.
* `R2_eq_Rf`: for `n₁, n₂ > 0` with `n₂` a unit modulo `q`, round 669's `R₂(n₁, n₂)` is round 652's
  `R(n₁/n₂, n₁n₂⁻¹)`, and `R(v, a) = Σ_iχ_i(a)e^{it_i log v}` is a finite exponential sum in `log v`, as in round
  668's `esum`.
* The separation: for two distinct pairs with one gcd `d` and one residue modulo `q`, with `n₁ > 0` and `n₁`, `n₂`
  and `m₂` units modulo `q`, the integer `n₁m₂ − m₁n₂` is divisible by `q`, since the residues agree, and by `d²`,
  which is prime to `q`, and it is not `0`, since the reduced fractions differ; so `qd² ≤ |n₁m₂ − m₁n₂|`
  (`sep_frac`), where they write `n′₂ = n′₁a^{−1} + qℓ′`. For `N > 0` and `n ∼ N` the fractions lie in `(1/2, 2)`,
  so `|log(n₁/n₂) − log(m₁/m₂)| ≥ qd²/(8N²)` (`log_sep`), a separation in the variable of `esum`.
* The bound: for frequencies `|λ_k| ≤ T`, `T ≥ 1`, `X ≥ 4`, `K ≥ 2` and points `|x_p| ≤ 1` that are `δ`-separated,
  `δ > 0`, `sum_cube_le` bounds `Σ_p|F(x_p)|³` by `C_k(3T + 4π/δ)∫ψ̃₀(y/X)|F(y)|³ dy` plus a tail. Round 668's
  `norm_cube_esum_le` bounds each `|F(x_p)|³` by `∫|k(ξ)||F(x_p + 2πξ/(3T))|³ dξ`; `|k(ξ)| ≤ C_k(1 + ξ²)⁻¹`, and
  the Lorentzians centred at the points sum to at most `2π + 4π/(cδ)` (`sum_lor_le`), with `c = 3T/(2π)`. With
  `δ = qd²/(8N²)` the coefficient is `C_k(3T + 32πN²/(qd²))`, their `T + N²/(d²q)` (lines 5246–5249, in the display
  ending with their (10.2)) up to constants. Where `|x_p + 2πξ/(3T)| > X`, `|x_p| ≤ 1` gives
  `|ξ| > Z = 3T(X − 1)/(2π)`, `norm_kloc_tail` bounds `k`, and the tail `|P|(Σ_k|c_k|)³·2πD_K(2π)^{−K}Z^{2−K}`
  stands for their `O(N²T^{−100})`: for `K ≥ 3` it is small for `X` large, with `T ≥ 1`; at `K = 2` it does not
  depend on `X`.

Plain statements, with `L_c(r) = (1 + c²r²)⁻¹` (`lor`), `k` round 668's `kloc`, `C_k` round 669's `Ck`, `D_K` round
659's `Dpsi` and `F = esum s c λ`.
* `integral_lor`, `lor_le_four`: `∫L_c(y − s) ds = π/c` for `c > 0`, and `L_c(y − x) ≤ 4L_c(y − s)` for `c ≥ 0` and
  `c|s − x| ≤ 1`.
* `sum_lor_le`: for `c, δ > 0` and points `x_p`, `p ∈ P`, with `|x_p − x_{p′}| ≥ δ` for `p ≠ p′`,
  `Σ_{p∈P}L_c(y − x_p) ≤ 2π + 4π/(cδ)`.
* `R2_eq_Rf`: for `n₁, n₂ > 0` with `n₂` a unit modulo `q`, `R₂(n₁, n₂) = R(n₁/n₂, n₁n₂⁻¹)`.
* `sep_frac`: for `n₁ > 0`, pairs with one gcd `d`, `n₁`, `n₂` and `m₂` units modulo `q`, and `n₁n₂⁻¹ = m₁m₂⁻¹`
  modulo `q`, `(n₁, n₂) ≠ (m₁, m₂)` gives `qd² ≤ |n₁m₂ − m₁n₂|`.
* `abs_sub_le_max_mul_abs_log`, `log_sep`: `|u − v| ≤ max(u, v)|log u − log v|` for `u, v > 0`; and for `N > 0`,
  `n₁, n₂, m₁, m₂ ∼ N` (round 670's `dyad`) and the other hypotheses of `sep_frac` but `n₁ > 0`,
  `|log(n₁/n₂) − log(m₁/m₂)| ≥ qd²/(8N²)`.
* `norm_kloc_le_lor`, `norm_kloc_tail`: `|k(ξ)| ≤ C_kL_1(ξ)`; and for `K ≥ 2`, `Z ≥ 1` and `|ξ| > Z`,
  `|k(ξ)| ≤ 2D_K(2π)^{−K}Z^{2−K}L_1(ξ)`.
* `integral_affine`: `∫f(ξ) dξ = a∫f(a(y − x)) dy` for `a > 0`.
* `sum_cube_le`: for `F(x) = Σ_kc_ke^{iλ_kx}` with every `|λ_k| ≤ T`, `T ≥ 1`, `X ≥ 4`, `K ≥ 2`, and points `x_p`,
  `p ∈ P`, with `|x_p| ≤ 1` and `|x_p − x_{p′}| ≥ δ > 0` for `p ≠ p′`,
  `Σ_{p∈P}|F(x_p)|³ ≤ C_k(3T + 4π/δ)∫ψ̃₀(y/X)|F(y)|³ dy + |P|(Σ_k|c_k|)³·2πD_K(2π)^{−K}Z^{2−K}` with
  `Z = 3T(X − 1)/(2π)`.

The file imports `LinnikCGLL107.lean`.
-/

import LinnikCGLL107

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLSep

open LinnikCGLL105 LinnikCGLRFact

/-! ### Separated points against a Lorentzian -/

/-- `L_c(r) = (1 + c²r²)⁻¹`. -/
def lor (c r : ℝ) : ℝ := (1 + c ^ 2 * r ^ 2)⁻¹

lemma lor_pos (c r : ℝ) : 0 < lor c r := by
  unfold lor
  positivity

lemma lor_eq (c y s : ℝ) : lor c (y - s) = (fun u : ℝ => (1 + u ^ 2)⁻¹) (c * (s - y)) := by
  simp only [lor]
  congr 1
  ring

lemma integrable_lor {c : ℝ} (hc : 0 < c) (y : ℝ) : Integrable fun s => lor c (y - s) := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' hc.ne').comp_sub_right y
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [lor_eq]

/-- `∫L_c(y − s) ds = π/c` for `c > 0`. -/
lemma integral_lor {c : ℝ} (hc : 0 < c) (y : ℝ) : ∫ s, lor c (y - s) = π / c := by
  simp only [lor_eq]
  rw [integral_sub_right_eq_self (fun s : ℝ => (fun u : ℝ => (1 + u ^ 2)⁻¹) (c * s)) y,
    Measure.integral_comp_mul_left (fun u : ℝ => (1 + u ^ 2)⁻¹) c, integral_univ_inv_one_add_sq, abs_inv,
    abs_of_pos hc, smul_eq_mul]
  field_simp

/-- Peetre's inequality for `L_c`: `L_c(y − x) ≤ 4L_c(y − s)` for `c ≥ 0` and `c|s − x| ≤ 1`. -/
lemma lor_le_four {c x s : ℝ} (hcs : c * |s - x| ≤ 1) (hc : 0 ≤ c) (y : ℝ) : lor c (y - x) ≤ 4 * lor c (y - s) := by
  unfold lor
  have h1 : 0 < 1 + c ^ 2 * (y - x) ^ 2 := by positivity
  have h2 : 0 < 1 + c ^ 2 * (y - s) ^ 2 := by positivity
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h1 h2]
  have hw : (c * (s - x)) ^ 2 ≤ 1 := by
    rw [mul_pow, ← sq_abs (s - x), ← mul_pow]
    have : 0 ≤ c * |s - x| := mul_nonneg hc (abs_nonneg _)
    nlinarith
  nlinarith [sq_nonneg (c * (y - x) - c * (y - s) + 2 * (c * (s - x))), sq_nonneg (c * (y - x)),
    sq_nonneg (c * (y - s))]

/-- **Separated points against a Lorentzian**: for points `x_p`, `p ∈ P`, with `|x_p − x_{p′}| ≥ δ` for `p ≠ p′`, and
`c, δ > 0`, `Σ_{p∈P}L_c(y − x_p) ≤ 2π + 4π/(cδ)`. With `2h = min(δ, 2/c)`, the intervals `[x_p − h, x_p + h)` are
disjoint, `L_c(y − x_p) ≤ 4L_c(y − s)` on each, and `∫L_c = π/c`. -/
theorem sum_lor_le {κ : Type*} (P : Finset κ) (x : κ → ℝ) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → δ ≤ |x p - x p'|) (y : ℝ) :
    ∑ p ∈ P, lor c (y - x p) ≤ 2 * π + 4 * π / (c * δ) := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = min δ (2 / c) / 2 := ⟨_, rfl⟩
  have hm0 : 0 < min δ (2 / c) := lt_min hδ (by positivity)
  have hh0 : 0 < h := by rw [hh]; linarith
  have hhδ : 2 * h ≤ δ := by rw [hh]; linarith [min_le_left δ (2 / c)]
  have hhc : c * h ≤ 1 := by
    have := min_le_right δ (2 / c)
    rw [hh]
    calc c * (min δ (2 / c) / 2) ≤ c * ((2 / c) / 2) := by gcongr
      _ = 1 := by field_simp
  obtain ⟨I, hI⟩ : ∃ I : κ → Set ℝ, I = fun p => Ico (x p - h) (x p + h) := ⟨_, rfl⟩
  have hdisj : Set.Pairwise (↑P) (Function.onFun Disjoint I) := by
    intro p hp p' hp' hne
    have hs := hsep p hp p' hp' hne
    simp only [Function.onFun, hI]
    rw [Set.Ico_disjoint_Ico]
    rcases le_total (x p) (x p') with hle | hle
    · rw [abs_of_nonpos (by linarith)] at hs
      exact (min_le_left _ _).trans (by linarith [le_max_right (x p - h) (x p' - h)])
    · rw [abs_of_nonneg (by linarith)] at hs
      exact (min_le_right _ _).trans (by linarith [le_max_left (x p - h) (x p' - h)])
  have hint := integrable_lor hc y
  have hterm : ∀ p ∈ P, 2 * h * lor c (y - x p) ≤ 4 * ∫ s in I p, lor c (y - s) := by
    intro p _
    have hvol : ∫ _s in I p, lor c (y - x p) = 2 * h * lor c (y - x p) := by
      rw [setIntegral_const, smul_eq_mul, hI]
      simp only [Measure.real, Real.volume_Ico]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [← hvol, ← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_const (by rw [hI]; exact measure_Ico_lt_top.ne) (by simp))
      (hint.integrableOn.const_mul 4) (by rw [hI]; exact measurableSet_Ico) fun s hs => ?_
    rw [hI] at hs
    have hs' : |s - x p| ≤ h := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    exact lor_le_four ((mul_le_mul_of_nonneg_left hs' hc.le).trans hhc) hc.le y
  have hsum : 2 * h * ∑ p ∈ P, lor c (y - x p) ≤ 4 * (π / c) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ P, 2 * h * lor c (y - x p) ≤ ∑ p ∈ P, 4 * ∫ s in I p, lor c (y - s) := Finset.sum_le_sum hterm
      _ = 4 * ∫ s in ⋃ p ∈ P, I p, lor c (y - s) := by
          rw [integral_biUnion_finset P (fun p _ => by rw [hI]; exact measurableSet_Ico) hdisj
            (fun p _ => hint.integrableOn), Finset.mul_sum]
      _ ≤ 4 * ∫ s, lor c (y - s) :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hint (Eventually.of_forall fun s => (lor_pos _ _).le))
            (by norm_num)
      _ = 4 * (π / c) := by rw [integral_lor hc]
  have h2h : 1 / (2 * h) ≤ 1 / δ + c / 2 := by
    have e : 2 * h = min δ (2 / c) := by rw [hh]; ring
    rw [e]
    rcases min_cases δ (2 / c) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      have : 0 ≤ c / 2 := by positivity
      linarith
    · rw [h1]
      have : 0 ≤ 1 / δ := by positivity
      have e2 : 1 / (2 / c) = c / 2 := by field_simp
      linarith
  have hS0 : 0 ≤ ∑ p ∈ P, lor c (y - x p) := Finset.sum_nonneg fun p _ => (lor_pos _ _).le
  calc ∑ p ∈ P, lor c (y - x p) = (2 * h * ∑ p ∈ P, lor c (y - x p)) * (1 / (2 * h)) := by
        field_simp
    _ ≤ 4 * (π / c) * (1 / δ + c / 2) :=
        mul_le_mul hsum h2h (by positivity) (by positivity)
    _ = 2 * π + 4 * π / (c * δ) := by
        field_simp
        ring

/-! ### `R₂` at a fraction, and the separation of fractions -/

section frac

variable {ι : Type*} {q : ℕ} [NeZero q] (R : Finset ι) (χ : ι → DirichletCharacter ℂ q) (t : ι → ℝ)

/-- For `n₁, n₂ > 0` with `n₂` a unit modulo `q`, `R₂(n₁, n₂) = R(n₁/n₂, n₁n₂⁻¹)`. -/
lemma R2_eq_Rf {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) (hu : IsUnit (n₂ : ZMod q)) :
    R2 R χ t n₁ n₂ = Rf R χ t ((n₁ : ℝ) / n₂) ((n₁ : ZMod q) * (n₂ : ZMod q)⁻¹) := by
  unfold R2 Rf
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinv : (n₂ : ZMod q)⁻¹ = ((hu.unit⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    rw [← ZMod.inv_coe_unit, IsUnit.unit_spec]
  have hn₁ : (0 : ℝ) < n₁ := by exact_mod_cast h₁
  have hn₂ : (0 : ℝ) < n₂ := by exact_mod_cast h₂
  rw [map_mul, hinv, ← star_unit, IsUnit.unit_spec, cpow_eq_exp (div_pos hn₁ hn₂),
    Real.log_div hn₁.ne' hn₂.ne', mul_comm (Real.log (n₁ : ℝ) - Real.log (n₂ : ℝ)) (t i)]
  simp only [starRingEnd_apply]
  ring

omit [NeZero q] in
/-- **Distinct fractions in one class are separated**: for `n₁ > 0`, pairs with one gcd `d`, `n₁`, `n₂` and `m₂` units
modulo `q`, and one residue `n₁n₂⁻¹ = m₁m₂⁻¹` modulo `q`, `(n₁, n₂) ≠ (m₁, m₂)` gives `qd² ≤ |n₁m₂ − m₁n₂|`. The
integer `n₁m₂ − m₁n₂` is divisible by `q` (the residues) and by `d²`, which is prime to `q`, and is not `0`, since
the reduced fractions `(n₁/d)/(n₂/d)` and `(m₁/d)/(m₂/d)` differ. -/
lemma sep_frac {n₁ n₂ m₁ m₂ : ℕ} (hn₁ : 0 < n₁) (hg : Nat.gcd n₁ n₂ = Nat.gcd m₁ m₂) (hu₁ : IsUnit (n₁ : ZMod q))
    (hu₂ : IsUnit (n₂ : ZMod q)) (hv₂ : IsUnit (m₂ : ZMod q))
    (hres : (n₁ : ZMod q) * (n₂ : ZMod q)⁻¹ = (m₁ : ZMod q) * (m₂ : ZMod q)⁻¹) (hne : (n₁, n₂) ≠ (m₁, m₂)) :
    (q : ℝ) * (Nat.gcd n₁ n₂ : ℝ) ^ 2 ≤ |(n₁ : ℝ) * m₂ - m₁ * n₂| := by
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd n₁ n₂ := ⟨_, rfl⟩
  rw [← hd]
  have hd0 : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_left _ hn₁
  have hdm : Nat.gcd m₁ m₂ = d := by rw [hd, hg]
  have hd1 : d ∣ n₁ := hd ▸ Nat.gcd_dvd_left n₁ n₂
  have hd2 : d ∣ n₂ := hd ▸ Nat.gcd_dvd_right n₁ n₂
  have hd3 : d ∣ m₁ := hdm ▸ Nat.gcd_dvd_left m₁ m₂
  have hd4 : d ∣ m₂ := hdm ▸ Nat.gcd_dvd_right m₁ m₂
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = (n₁ : ℤ) * m₂ - m₁ * n₂ := ⟨_, rfl⟩
  have hqA : (q : ℤ) ∣ A := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 : (n₁ : ZMod q) * (m₂ : ZMod q) = (m₁ : ZMod q) * (n₂ : ZMod q) := by
      have h := congrArg (· * ((n₂ : ZMod q) * (m₂ : ZMod q))) hres
      have e1 : (n₁ : ZMod q) * (n₂ : ZMod q)⁻¹ * ((n₂ : ZMod q) * (m₂ : ZMod q)) =
          (n₁ : ZMod q) * ((n₂ : ZMod q)⁻¹ * (n₂ : ZMod q)) * (m₂ : ZMod q) := by ring
      have e2 : (m₁ : ZMod q) * (m₂ : ZMod q)⁻¹ * ((n₂ : ZMod q) * (m₂ : ZMod q)) =
          (m₁ : ZMod q) * ((m₂ : ZMod q)⁻¹ * (m₂ : ZMod q)) * (n₂ : ZMod q) := by ring
      rw [e1, e2, ZMod.inv_mul_of_unit _ hu₂, ZMod.inv_mul_of_unit _ hv₂, mul_one, mul_one] at h
      exact h
    rw [hA]
    push_cast
    rw [h1, sub_self]
  have hdA : (d : ℤ) ^ 2 ∣ A := by
    rw [hA, sq]
    exact dvd_sub (mul_dvd_mul (by exact_mod_cast hd1) (by exact_mod_cast hd4))
      (mul_dvd_mul (by exact_mod_cast hd3) (by exact_mod_cast hd2))
  have hcop : Nat.Coprime q (d ^ 2) := by
    have h1 : Nat.Coprime n₁ q := (ZMod.isUnit_iff_coprime n₁ q).mp hu₁
    exact (Nat.Coprime.coprime_dvd_left hd1 h1).symm.pow_right 2
  have hqdA : (q : ℤ) * (d : ℤ) ^ 2 ∣ A := by
    have hc : IsCoprime (q : ℤ) ((d : ℤ) ^ 2) := by
      rw [← Nat.cast_pow]
      exact Nat.isCoprime_iff_coprime.mpr hcop
    exact hc.mul_dvd hqA hdA
  have hA0 : A ≠ 0 := by
    intro h0
    apply hne
    have heq : n₁ * m₂ = m₁ * n₂ := by
      have : (n₁ : ℤ) * m₂ = m₁ * n₂ := by linarith
      exact_mod_cast this
    have hab : Nat.Coprime (n₁ / d) (n₂ / d) := by rw [hd]; exact Nat.coprime_div_gcd_div_gcd (hd ▸ hd0)
    have hce : Nat.Coprime (m₁ / d) (m₂ / d) := by
      rw [← hdm]; exact Nat.coprime_div_gcd_div_gcd (hdm ▸ hd0)
    obtain ⟨a, ha⟩ : ∃ a, a = n₁ / d := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = n₂ / d := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = m₁ / d := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, e = m₂ / d := ⟨_, rfl⟩
    rw [← ha, ← hb] at hab
    rw [← hc, ← he] at hce
    have hn₁' : n₁ = d * a := by rw [ha, Nat.mul_div_cancel' hd1]
    have hn₂' : n₂ = d * b := by rw [hb, Nat.mul_div_cancel' hd2]
    have hm₁' : m₁ = d * c := by rw [hc, Nat.mul_div_cancel' hd3]
    have hm₂' : m₂ = d * e := by rw [he, Nat.mul_div_cancel' hd4]
    have hae : a * e = c * b := by
      rw [hn₁', hn₂', hm₁', hm₂'] at heq
      have hdd : 0 < d * d := Nat.mul_pos hd0 hd0
      apply Nat.eq_of_mul_eq_mul_left hdd
      calc d * d * (a * e) = d * a * (d * e) := by ring
        _ = d * c * (d * b) := heq
        _ = d * d * (c * b) := by ring
    have hac : a ∣ c := hab.dvd_of_dvd_mul_right ⟨e, by rw [hae, mul_comm]⟩
    have hca : c ∣ a := hce.dvd_of_dvd_mul_right ⟨b, by rw [← hae, mul_comm]⟩
    have hac' : a = c := Nat.dvd_antisymm hac hca
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, mul_zero] at hn₁'
        omega
      · exact h
    have hbe : b = e := by
      rw [hac'] at hae
      have hc0 : 0 < c := hac' ▸ ha0
      exact (Nat.eq_of_mul_eq_mul_left hc0 hae).symm
    rw [hn₁', hn₂', hm₁', hm₂', hac', hbe]
  have hle : (q : ℤ) * (d : ℤ) ^ 2 ≤ |A| := Int.le_of_dvd (abs_pos.mpr hA0) ((dvd_abs _ _).mpr hqdA)
  have hcast : ((|A| : ℤ) : ℝ) = |(n₁ : ℝ) * m₂ - m₁ * n₂| := by
    rw [Int.cast_abs, hA]
    push_cast
    ring_nf
  rw [← hcast]
  exact_mod_cast hle

/-- `|u − v| ≤ max(u, v)|log u − log v|` for `u, v > 0`, from `log x ≥ 1 − 1/x`. -/
lemma abs_sub_le_max_mul_abs_log {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    |u - v| ≤ max u v * |Real.log u - Real.log v| := by
  rcases le_total v u with h | h
  · have h1 : 1 - (u / v)⁻¹ ≤ Real.log (u / v) := Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [Real.log_div hu.ne' hv.ne', inv_div] at h1
    have hl : 0 ≤ Real.log u - Real.log v := by linarith [Real.log_le_log hv h]
    rw [max_eq_left h, abs_of_nonneg (by linarith), abs_of_nonneg hl]
    have h2 : (u - v) / u ≤ Real.log u - Real.log v := by
      rw [sub_div, div_self hu.ne']
      linarith
    rwa [div_le_iff₀ hu, mul_comm] at h2
  · have h1 : 1 - (v / u)⁻¹ ≤ Real.log (v / u) := Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [Real.log_div hv.ne' hu.ne', inv_div] at h1
    have hl : 0 ≤ Real.log v - Real.log u := by linarith [Real.log_le_log hu h]
    rw [max_eq_right h, abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg hl]
    have h2 : (v - u) / v ≤ Real.log v - Real.log u := by
      rw [sub_div, div_self hv.ne']
      linarith
    rwa [div_le_iff₀ hv, mul_comm] at h2

omit [NeZero q] in
/-- **The separation in `log`**: for pairs of `n ∼ N` (`N > 0`) as in `sep_frac`,
`|log(n₁/n₂) − log(m₁/m₂)| ≥ qd²/(8N²)`, since the fractions lie in `(1/2, 2)` and `n₂m₂ ≤ 4N²`. -/
lemma log_sep {N : ℝ} (hN : 0 < N) {n₁ n₂ m₁ m₂ : ℕ} (hn₁ : n₁ ∈ LinnikCGLT101.dyad N)
    (hn₂ : n₂ ∈ LinnikCGLT101.dyad N) (hm₁ : m₁ ∈ LinnikCGLT101.dyad N) (hm₂ : m₂ ∈ LinnikCGLT101.dyad N)
    (hg : Nat.gcd n₁ n₂ = Nat.gcd m₁ m₂) (hu₁ : IsUnit (n₁ : ZMod q)) (hu₂ : IsUnit (n₂ : ZMod q))
    (hv₂ : IsUnit (m₂ : ZMod q))
    (hres : (n₁ : ZMod q) * (n₂ : ZMod q)⁻¹ = (m₁ : ZMod q) * (m₂ : ZMod q)⁻¹) (hne : (n₁, n₂) ≠ (m₁, m₂)) :
    (q : ℝ) * (Nat.gcd n₁ n₂ : ℝ) ^ 2 / (8 * N ^ 2) ≤
      |Real.log ((n₁ : ℝ) / n₂) - Real.log ((m₁ : ℝ) / m₂)| := by
  rw [LinnikCGLT101.mem_dyad hN.le] at hn₁ hn₂ hm₁ hm₂
  have p₁ : (0 : ℝ) < n₁ := hN.trans hn₁.1
  have p₂ : (0 : ℝ) < n₂ := hN.trans hn₂.1
  have r₁ : (0 : ℝ) < m₁ := hN.trans hm₁.1
  have r₂ : (0 : ℝ) < m₂ := hN.trans hm₂.1
  have hsep := sep_frac (q := q) (by exact_mod_cast p₁) hg hu₁ hu₂ hv₂ hres hne
  have hu : (0 : ℝ) < (n₁ : ℝ) / n₂ := div_pos p₁ p₂
  have hv : (0 : ℝ) < (m₁ : ℝ) / m₂ := div_pos r₁ r₂
  have hmax : max ((n₁ : ℝ) / n₂) ((m₁ : ℝ) / m₂) ≤ 2 := by
    refine max_le ?_ ?_
    · rw [div_le_iff₀ p₂]; linarith [hn₁.2, hn₂.1]
    · rw [div_le_iff₀ r₂]; linarith [hm₁.2, hm₂.1]
  have hdiff : (n₁ : ℝ) / n₂ - (m₁ : ℝ) / m₂ = ((n₁ : ℝ) * m₂ - m₁ * n₂) / (n₂ * m₂) := by
    field_simp
  have hden : (n₂ : ℝ) * m₂ ≤ 4 * N ^ 2 := by nlinarith [hn₂.2, hm₂.2]
  have hfrac : (q : ℝ) * (Nat.gcd n₁ n₂ : ℝ) ^ 2 / (4 * N ^ 2) ≤ |(n₁ : ℝ) / n₂ - (m₁ : ℝ) / m₂| := by
    rw [hdiff, abs_div, abs_of_pos (mul_pos p₂ r₂)]
    calc (q : ℝ) * (Nat.gcd n₁ n₂ : ℝ) ^ 2 / (4 * N ^ 2) ≤ (q : ℝ) * (Nat.gcd n₁ n₂ : ℝ) ^ 2 / (n₂ * m₂) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos p₂ r₂) hden
      _ ≤ |(n₁ : ℝ) * m₂ - m₁ * n₂| / (n₂ * m₂) := div_le_div_of_nonneg_right hsep (mul_pos p₂ r₂).le
  have hlog := abs_sub_le_max_mul_abs_log hu hv
  have hl0 : 0 ≤ |Real.log ((n₁ : ℝ) / n₂) - Real.log ((m₁ : ℝ) / m₂)| := abs_nonneg _
  calc (q : ℝ) * (Nat.gcd n₁ n₂ : ℝ) ^ 2 / (8 * N ^ 2)
      = (q : ℝ) * (Nat.gcd n₁ n₂ : ℝ) ^ 2 / (4 * N ^ 2) / 2 := by ring
    _ ≤ |(n₁ : ℝ) / n₂ - (m₁ : ℝ) / m₂| / 2 := by gcongr
    _ ≤ max ((n₁ : ℝ) / n₂) ((m₁ : ℝ) / m₂) * |Real.log ((n₁ : ℝ) / n₂) - Real.log ((m₁ : ℝ) / m₂)| / 2 := by
        gcongr
    _ ≤ 2 * |Real.log ((n₁ : ℝ) / n₂) - Real.log ((m₁ : ℝ) / m₂)| / 2 := by gcongr
    _ = |Real.log ((n₁ : ℝ) / n₂) - Real.log ((m₁ : ℝ) / m₂)| := by ring

end frac

/-! ### A finite exponential sum at separated points -/

open LinnikCGLLoc LinnikCGLMom4 in
/-- `|k(ξ)| ≤ C_kL_1(ξ)`, from round 669's `(1 + ξ²)|k(ξ)| ≤ C_k`. -/
lemma norm_kloc_le_lor (ξ : ℝ) : ‖kloc ξ‖ ≤ Ck * lor 1 ξ := by
  have h := norm_kloc_mul_le ξ
  unfold lor
  rw [one_pow, one_mul, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

open LinnikCGLLoc LinnikCGLMom4 in
/-- **The kernel's tail**: for `K ≥ 2`, `Z ≥ 1` and `|ξ| > Z`, `|k(ξ)| ≤ 2D_K(2π)^{−K}Z^{2−K}L_1(ξ)`, from
round 659's `(2π|ξ|)^K|ψ̂₀(ξ)| ≤ D_K`. -/
lemma norm_kloc_tail {K : ℕ} (hK : 2 ≤ K) {Z : ℝ} (hZ : 1 ≤ Z) {ξ : ℝ} (hξ : Z < |ξ|) :
    ‖kloc ξ‖ ≤ 2 * (Dpsi K / (2 * π) ^ K / Z ^ (K - 2)) * lor 1 ξ := by
  have hdec : (2 * π) ^ K * |ξ| ^ K * ‖kloc ξ‖ ≤ Dpsi K := by
    rw [← mul_pow]
    exact fourier_psiC_decay K ξ
  have hA : 1 ≤ |ξ| := hZ.trans hξ.le
  have hsq : 1 + ξ ^ 2 ≤ 2 * |ξ| ^ 2 := by
    rw [sq_abs]
    have : 1 ≤ ξ ^ 2 := by rw [← sq_abs]; nlinarith
    linarith
  have hZK : Z ^ (K - 2) ≤ |ξ| ^ (K - 2) := pow_le_pow_left₀ (by linarith) hξ.le _
  have hpow : |ξ| ^ K = |ξ| ^ (K - 2) * |ξ| ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hK]
  have hZ0 : 0 < Z ^ (K - 2) := by positivity
  have e : 2 * (Dpsi K / (2 * π) ^ K / Z ^ (K - 2)) * lor 1 ξ =
      2 * Dpsi K / ((2 * π) ^ K * Z ^ (K - 2) * (1 + ξ ^ 2)) := by
    unfold lor
    rw [one_pow, one_mul]
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  have hk := norm_nonneg (kloc ξ)
  calc ‖kloc ξ‖ * ((2 * π) ^ K * Z ^ (K - 2) * (1 + ξ ^ 2))
      ≤ ‖kloc ξ‖ * ((2 * π) ^ K * |ξ| ^ (K - 2) * (2 * |ξ| ^ 2)) := by gcongr
    _ = 2 * ((2 * π) ^ K * |ξ| ^ K * ‖kloc ξ‖) := by rw [hpow]; ring
    _ ≤ 2 * Dpsi K := by linarith

/-- `∫f(ξ) dξ = a∫f(a(y − x)) dy` for `a > 0`. -/
lemma integral_affine (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) : ∫ ξ, f ξ = a * ∫ y, f (a * (y - x)) := by
  have h1 := integral_sub_right_eq_self (μ := volume) (fun y => f (a * y)) x
  rw [h1, Measure.integral_comp_mul_left f a, abs_inv, abs_of_pos ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ha.ne', one_mul]

open LinnikCGLLoc LinnikCGLMom4 LinnikCGLRt in
/-- **A finite exponential sum at separated points**: for `F(x) = Σ_kc_ke^{iλ_kx}` with every `|λ_k| ≤ T`, `T ≥ 1`,
`X ≥ 4`, `K ≥ 2`, and points `x_p`, `p ∈ P`, with `|x_p| ≤ 1` and `|x_p − x_{p′}| ≥ δ > 0` for `p ≠ p′`,
`Σ_{p∈P}|F(x_p)|³ ≤ C_k(3T + 4π/δ)∫ψ̃₀(y/X)|F(y)|³ dy + |P|(Σ_k|c_k|)³·2πD_K(2π)^{−K}Z^{2−K}` with
`Z = 3T(X − 1)/(2π)`. Each `|F(x_p)|³` is at most `∫|k(ξ)||F(x_p + 2πξ/(3T))|³ dξ` (round 668's
`norm_cube_esum_le`); where `|x_p + 2πξ/(3T)| ≤ X` the weight `ψ̃₀(·/X)` is `1`, and elsewhere `|ξ| > Z`
(`norm_kloc_tail`). The change of variables `ξ = 3T(y − x_p)/(2π)` and `sum_lor_le` count the points. -/
theorem sum_cube_le {κ ι' : Type*} (s : Finset κ) (c : κ → ℂ) (lam : κ → ℝ) {T X δ : ℝ} (hT : 1 ≤ T)
    (hlam : ∀ k ∈ s, |lam k| ≤ T) (hX : 4 ≤ X) (hδ : 0 < δ) (P : Finset ι') (x : ι' → ℝ)
    (hx : ∀ p ∈ P, |x p| ≤ 1) (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → δ ≤ |x p - x p'|) {K : ℕ} (hK : 2 ≤ K) :
    ∑ p ∈ P, ‖esum s c lam (x p)‖ ^ 3 ≤
      Ck * (3 * T + 4 * π / δ) * (∫ y, psi0 (y / X) * ‖esum s c lam y‖ ^ 3) +
        P.card * (∑ k ∈ s, ‖c k‖) ^ 3 *
          (2 * π * (Dpsi K / (2 * π) ^ K / (3 * T * (X - 1) / (2 * π)) ^ (K - 2))) := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = esum s c lam := ⟨_, rfl⟩
  rw [← hF]
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ k ∈ s, ‖c k‖ := ⟨_, rfl⟩
  rw [← hB]
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 3 * T * (X - 1) / (2 * π) := ⟨_, rfl⟩
  rw [← hZ]
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = Dpsi K / (2 * π) ^ K / Z ^ (K - 2) := ⟨_, rfl⟩
  rw [← hτ]
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = 3 * T / (2 * π) := ⟨_, rfl⟩
  have hT0 : 0 < T := by linarith
  have hc'0 : 0 < c' := by rw [hc']; positivity
  have hZ1 : 1 ≤ Z := by
    rw [hZ, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_le_four]
  have hτ0 : 0 ≤ τ := by rw [hτ]; have := Dpsi_nonneg K; positivity
  have hB0 : 0 ≤ B := by rw [hB]; exact Finset.sum_nonneg fun k _ => norm_nonneg _
  have hFB : ∀ y, ‖F y‖ ≤ B := fun y => by rw [hF, hB]; exact norm_esum_le s c lam y
  have hFc : Continuous F := by rw [hF]; exact continuous_esum s c lam
  have hX0 : 0 < X := by linarith
  -- the weighted cube `g`
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun y => psi0 (y / X) * ‖F y‖ ^ 3 := ⟨_, rfl⟩
  have hg0 : ∀ y, 0 ≤ g y := fun y => by rw [hg]; exact mul_nonneg (psi0_nonneg _) (by positivity)
  have hgB : ∀ y, g y ≤ B ^ 3 := fun y => by
    rw [hg]
    calc psi0 (y / X) * ‖F y‖ ^ 3 ≤ 1 * B ^ 3 :=
          mul_le_mul (psi0_le_one _) (pow_le_pow_left₀ (norm_nonneg _) (hFB y) 3) (by positivity) (by norm_num)
      _ = B ^ 3 := one_mul _
  have hgc : Continuous g := by
    rw [hg]
    exact (continuous_psi0.comp (continuous_id.div_const X)).mul (hFc.norm.pow 3)
  have hgi : Integrable g := by
    refine hgc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := -(2 * X)) (b := 2 * X))
      fun y hy => ?_)
    rw [hg]
    simp only
    rw [LinnikCGLMom.psi0_eq_zero, zero_mul]
    rw [abs_div, abs_of_pos hX0, le_div_iff₀ hX0]
    by_contra hc
    exact hy ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have hkc : Continuous fun ξ => ‖kloc ξ‖ := continuous_kloc.norm
  have hkb : ∀ ξ, ‖kloc ξ‖ ≤ ∫ u, psi0 u := fun ξ => norm_fourier_psiC_le ξ
  -- one point
  have hpt : ∀ p ∈ P, ‖F (x p)‖ ^ 3 ≤ c' * (∫ y, ‖kloc (c' * (y - x p))‖ * g y) + B ^ 3 * (2 * τ * π) := by
    intro p hp
    have h1 : ‖F (x p)‖ ^ 3 ≤ ∫ ξ, ‖kloc ξ‖ * ‖F (x p + 2 * π * ξ / (3 * T))‖ ^ 3 := by
      rw [hF]
      exact norm_cube_esum_le s c lam (Λ := 0) hT0 (fun k hk => by rw [sub_zero]; exact hlam k hk) (x p)
    have hpw : ∀ ξ, ‖kloc ξ‖ * ‖F (x p + 2 * π * ξ / (3 * T))‖ ^ 3 ≤
        ‖kloc ξ‖ * g (x p + 2 * π * ξ / (3 * T)) + B ^ 3 * (2 * τ * lor 1 ξ) := by
      intro ξ
      have hk0 := norm_nonneg (kloc ξ)
      by_cases hy : |x p + 2 * π * ξ / (3 * T)| ≤ X
      · have hpsi : psi0 ((x p + 2 * π * ξ / (3 * T)) / X) = 1 := by
          refine psi0_eq_one ?_
          rw [abs_div, abs_of_pos hX0, div_le_one hX0]
          exact hy
        have : g (x p + 2 * π * ξ / (3 * T)) = ‖F (x p + 2 * π * ξ / (3 * T))‖ ^ 3 := by
          rw [hg]; simp only; rw [hpsi, one_mul]
        rw [this]
        have : 0 ≤ B ^ 3 * (2 * τ * lor 1 ξ) := by have := lor_pos 1 ξ; positivity
        linarith
      · push Not at hy
        have hξ : Z < |ξ| := by
          have h2 : X - 1 < |2 * π * ξ / (3 * T)| := by
            have := abs_add_le (x p) (2 * π * ξ / (3 * T))
            linarith [hx p hp]
          rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_pos (by positivity : 0 < 3 * T),
            lt_div_iff₀ (by positivity)] at h2
          rw [hZ, div_lt_iff₀ (by positivity)]
          linarith
        have htail := norm_kloc_tail hK hZ1 hξ
        rw [← hτ] at htail
        have hFy := pow_le_pow_left₀ (norm_nonneg _) (hFB (x p + 2 * π * ξ / (3 * T))) 3
        have hgy := hg0 (x p + 2 * π * ξ / (3 * T))
        calc ‖kloc ξ‖ * ‖F (x p + 2 * π * ξ / (3 * T))‖ ^ 3 ≤ (2 * τ * lor 1 ξ) * B ^ 3 :=
              mul_le_mul htail hFy (by positivity) (by have := lor_pos 1 ξ; positivity)
          _ ≤ ‖kloc ξ‖ * g (x p + 2 * π * ξ / (3 * T)) + B ^ 3 * (2 * τ * lor 1 ξ) := by
              have := mul_nonneg hk0 hgy
              linarith
    have hint1 : Integrable fun ξ => ‖kloc ξ‖ * g (x p + 2 * π * ξ / (3 * T)) :=
      integrable_kloc.norm.mul_bdd (hgc.comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun ξ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]; exact hgB _)
    have hlor := integrable_lor (c := 1) one_pos 0
    have hint2 : Integrable fun ξ => B ^ 3 * (2 * τ * lor 1 ξ) := by
      have e : (fun ξ => B ^ 3 * (2 * τ * lor 1 ξ)) = fun ξ => B ^ 3 * (2 * τ * lor 1 (0 - ξ)) := by
        funext ξ; congr 2; unfold lor; ring_nf
      rw [e]
      exact (hlor.const_mul (2 * τ)).const_mul (B ^ 3)
    have h2 : ∫ ξ, ‖kloc ξ‖ * ‖F (x p + 2 * π * ξ / (3 * T))‖ ^ 3 ≤
        ∫ ξ, (‖kloc ξ‖ * g (x p + 2 * π * ξ / (3 * T)) + B ^ 3 * (2 * τ * lor 1 ξ)) :=
      integral_mono_of_nonneg (Eventually.of_forall fun ξ => mul_nonneg (norm_nonneg _) (by positivity))
        (hint1.add hint2) (Eventually.of_forall hpw)
    have h3 : ∫ ξ, (‖kloc ξ‖ * g (x p + 2 * π * ξ / (3 * T)) + B ^ 3 * (2 * τ * lor 1 ξ)) =
        c' * (∫ y, ‖kloc (c' * (y - x p))‖ * g y) + B ^ 3 * (2 * τ * π) := by
      rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul]
      have hl : ∫ ξ, lor 1 ξ = π := by
        have := integral_lor (c := 1) one_pos 0
        rw [div_one] at this
        rw [← this]
        congr 1
        funext ξ
        unfold lor
        ring_nf
      rw [hl]
      congr 1
      rw [integral_affine (fun ξ => ‖kloc ξ‖ * g (x p + 2 * π * ξ / (3 * T))) hc'0 (x p)]
      have e : ∀ y, x p + 2 * π * (c' * (y - x p)) / (3 * T) = y := fun y => by
        rw [hc']
        field_simp
        ring
      simp only [e]
    linarith
  -- the sum over the points
  have hint3 : ∀ p ∈ P, Integrable fun y => ‖kloc (c' * (y - x p))‖ * g y := fun p _ =>
    hgi.bdd_mul ((hkc.comp (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_norm]; exact hkb _)
  have hcount : ∀ y, ∑ p ∈ P, ‖kloc (c' * (y - x p))‖ ≤ Ck * (2 * π + 4 * π / (c' * δ)) := by
    intro y
    calc ∑ p ∈ P, ‖kloc (c' * (y - x p))‖ ≤ ∑ p ∈ P, Ck * lor c' (y - x p) := by
          refine Finset.sum_le_sum fun p _ => ?_
          have := norm_kloc_le_lor (c' * (y - x p))
          have e : lor 1 (c' * (y - x p)) = lor c' (y - x p) := by unfold lor; ring_nf
          rwa [e] at this
      _ = Ck * ∑ p ∈ P, lor c' (y - x p) := by rw [Finset.mul_sum]
      _ ≤ Ck * (2 * π + 4 * π / (c' * δ)) :=
          mul_le_mul_of_nonneg_left (sum_lor_le P x hδ hc'0 hsep y) Ck_nonneg
  have hsumint : ∑ p ∈ P, ∫ y, ‖kloc (c' * (y - x p))‖ * g y ≤
      Ck * (2 * π + 4 * π / (c' * δ)) * ∫ y, g y := by
    rw [← integral_finsetSum _ hint3, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y =>
      Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (hg0 y)) (hgi.const_mul _)
      (Eventually.of_forall fun y => ?_)
    simp only
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcount y) (hg0 y)
  have hgint : ∫ y, g y = ∫ y, psi0 (y / X) * ‖F y‖ ^ 3 := by rw [hg]
  calc ∑ p ∈ P, ‖F (x p)‖ ^ 3 ≤ ∑ p ∈ P, (c' * (∫ y, ‖kloc (c' * (y - x p))‖ * g y) + B ^ 3 * (2 * τ * π)) :=
        Finset.sum_le_sum hpt
    _ = c' * (∑ p ∈ P, ∫ y, ‖kloc (c' * (y - x p))‖ * g y) + P.card * (B ^ 3 * (2 * τ * π)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ c' * (Ck * (2 * π + 4 * π / (c' * δ)) * ∫ y, g y) + P.card * (B ^ 3 * (2 * τ * π)) := by
        have := mul_le_mul_of_nonneg_left hsumint hc'0.le
        linarith
    _ = Ck * (3 * T + 4 * π / δ) * (∫ y, psi0 (y / X) * ‖F y‖ ^ 3) + P.card * B ^ 3 * (2 * π * τ) := by
        rw [hgint, hc']
        field_simp

end LinnikCGLSep

#print axioms LinnikCGLSep.sum_lor_le
#print axioms LinnikCGLSep.sep_frac
#print axioms LinnikCGLSep.log_sep
#print axioms LinnikCGLSep.sum_cube_le
