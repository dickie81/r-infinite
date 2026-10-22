/-
# Round 681: the count of the pairs `(m₁′, n′)` in their Lemma 8.2 (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li bound a double sum over `|m₁′| ∼ M₁` and `n′` in the proof of their Lemma 8.2: "the double sum
Σ_{m₁′}Σ_{n₁′} is bounded by ⪅ 1 + M₁/M₃. To see this, write s = m₁′n′. Then s is a non-zero integer lying in a fixed
residue class modulo q, and it is contained in a ⪅ qM₁/M₃ neighborhood of qξ. Thus there are at most ⪅ 1 + M₁/M₃
possibilities for s, giving the claim." (lines 3358–3366; spaces restored, the sums and subscripts transcribed). This
file proves
the count in the form the stack's bound for `Σ_a|ĝ_a(ξ)|²` uses: the sum over `m₁′` and `n′ ≠ 0` of the weight
`|ψ̂₀(L(n′/q − ξ/m₁′))|` times the gcd `(n′m₁′ − x, q)`, over all residues at once.

The stack's form.
* Their sharp window `|ξ − n′m₁′/q| ⪅ M₁/M₃` is the decay of `ψ̂₀`: `|ψ̂₀(y)| ≤ B₄L₁(y)²` with
  `L_c(r) = (1 + c²r²)⁻¹` (round 673's `lor`) and `B₄ = 2(∫ψ̃₀ + D₄/(2π)⁴)` (`norm_fourier_psiC_le_lor`). With
  `s = n′m₁′` and `Λ = 2qM₁/L`, `L₁(L(n′/q − ξ/m₁′)) ≤ L_{1/Λ}(s − qξ)` (`lor_le_lor_prod`).
* Their "at most ⪅ 1 + M₁/M₃ possibilities for s" is round 673's `sum_lor_le` along each residue class of `s`, whose
  points are `q` apart: `Σ_sL_{1/Λ}(s − qξ) ≤ 2π + 4πΛ/q`.
* Their `⪅` in "the double sum is bounded by" absorbs the divisor function: each `s ≠ 0` comes from at most `2d(|s|)`
  pairs (`card_fiber_le`), and `d(|s|) ≤ C_δ|s|^δ` (round 525's `LinnikPower.card_divisors_le`), with
  `|s|^δL_{1/Λ}(s − qξ)² ≤ 2(1 + q|ξ|)^δ(1 + Λ)^δL_{1/Λ}(s − qξ)` (`rpow_mul_lor_sq_le`).
* The gcd `(s − x, q)` depends on the residue of `s`, and the residues are summed: `Σ_{h∈ℤ/qℤ}(h, q)`.

Plain statements, with `q ≥ 1` (`[NeZero q]`).
* `norm_fourier_psiC_le_lor`: `|ψ̂₀(y)| ≤ B₄L₁(y)²` for every real `y`.
* `lor_le_lor_prod`: for `q > 0`, `L > 0`, `M₁ > 0`, `m₁′ ∈ P1 M₁` and integers `n′`,
  `L₁(L(n′/q − ξ/m₁′)) ≤ L_{1/Λ}(n′m₁′ − qξ)` with `Λ = 2qM₁/L`.
* `card_fiber_le`: for `s ≠ 0`, the pairs `(m, n)` of a finite set with `nm = s` number at most `2d(|s|)`.
* `one_add_mul_lor_le`, `rpow_mul_lor_sq_le`: for `0 < δ ≤ 1`, `Λ > 0` and integers `s`,
  `|s|^δL_{1/Λ}(s − qξ)² ≤ 2(1 + q|ξ|)^δ(1 + Λ)^δL_{1/Λ}(s − qξ)`.
* `gw`, `sum_lor_gw_le`: `gw x = (x, q)`; for `Λ > 0` and a finite set `S` of integers,
  `Σ_{s∈S}L_{1/Λ}(s − y)(s − x, q) ≤ (Σ_{h∈ℤ/qℤ}(h, q))(2π + 4πΛ/q)`.
* `count_le`: for `L > 0`, `M₁ > 0`, `0 < δ ≤ 1`, real `ξ`, `x ∈ ℤ/qℤ` and a finite set `T` of integers,
  `Σ_{m₁′∈P1 M₁}Σ_{n′∈T, n′≠0}|ψ̂₀(L(n′/q − ξ/m₁′))|(n′m₁′ − x, q) ≤
  4C_δB₄(1 + q|ξ|)^δ(1 + 2qM₁/L)^δ(Σ_{h∈ℤ/qℤ}(h, q))(2π + 8πM₁/L)`.

The file imports `LinnikCGLPois8.lean`.
-/

import LinnikCGLPois8

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLCount

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLG LinnikCGLPois8

/-! ### The weight -/

/-- The constant `B₄ = 2(∫ψ̃₀ + D₄/(2π)⁴)`. -/
def B4 : ℝ := 2 * ((∫ y, psi0 y) + Dpsi 4 / (2 * π) ^ 4)

/-- `|ψ̂₀(y)| ≤ B₄L₁(y)²`. -/
lemma norm_fourier_psiC_le_lor (y : ℝ) : ‖𝓕 psiC y‖ ≤ B4 * lor 1 y ^ 2 := by
  have h1 := fourier_psiC_decay 4 y
  have h2 := norm_fourier_psiC_le y
  have hpi : 0 < (2 * π) ^ 4 := by positivity
  have h1' : y ^ 4 * ‖𝓕 psiC y‖ ≤ Dpsi 4 / (2 * π) ^ 4 := by
    rw [le_div_iff₀ hpi]
    have : (2 * π * |y|) ^ 4 = (2 * π) ^ 4 * y ^ 4 := by
      rw [mul_pow, show |y| ^ 4 = y ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
    rw [this] at h1
    linarith
  have hl : lor 1 y ^ 2 = ((1 + y ^ 2) ^ 2)⁻¹ := by
    unfold lor; rw [one_pow, one_mul, inv_pow]
  rw [hl, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hsq : (1 + y ^ 2) ^ 2 ≤ 2 * (1 + y ^ 4) := by nlinarith [sq_nonneg (y ^ 2 - 1)]
  have hn := norm_nonneg (𝓕 psiC y)
  calc ‖𝓕 psiC y‖ * (1 + y ^ 2) ^ 2 ≤ ‖𝓕 psiC y‖ * (2 * (1 + y ^ 4)) := mul_le_mul_of_nonneg_left hsq hn
    _ = 2 * (‖𝓕 psiC y‖ + y ^ 4 * ‖𝓕 psiC y‖) := by ring
    _ ≤ B4 := by unfold B4; gcongr

lemma B4_nonneg : 0 ≤ B4 := le_trans (norm_nonneg _) ((norm_fourier_psiC_le_lor 0).trans (by
  unfold lor; norm_num))

lemma lor_pos' (c r : ℝ) : 0 < lor c r := by unfold lor; positivity

lemma lor_le_one (c r : ℝ) : lor c r ≤ 1 := by
  unfold lor; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (c * r)])

lemma lor_neg (c r : ℝ) : lor c (-r) = lor c r := by unfold lor; rw [neg_sq]

/-- `L_c` decreases in `|r|`: `|r| ≤ |r′|` gives `L_c(r′) ≤ L_c(r)`. -/
lemma lor_anti {c r r' : ℝ} (h : |r| ≤ |r'|) : lor c r' ≤ lor c r := by
  unfold lor
  apply inv_anti₀ (by positivity)
  have : r ^ 2 ≤ r' ^ 2 := by rw [← sq_abs r, ← sq_abs r']; exact pow_le_pow_left₀ (abs_nonneg r) h 2
  nlinarith [sq_nonneg c]

/-- **The window**: for `q > 0`, `L > 0`, `M₁ > 0`, `m₁′ ∈ P1 M₁` and integers `n′`,
`L₁(L(n′/q − ξ/m₁′)) ≤ L_{1/Λ}(n′m₁′ − qξ)` with `Λ = 2qM₁/L`. -/
lemma lor_le_lor_prod {q : ℕ} (hq : 0 < q) {L M₁ : ℝ} (hL : 0 < L) (hM₁ : 0 < M₁) {m : ℤ} (hm : m ∈ P1 M₁)
    (n : ℤ) (ξ : ℝ) :
    lor 1 (L * (n / q - ξ / m)) ≤ lor (1 / (2 * q * M₁ / L)) ((n * m : ℤ) - q * ξ) := by
  rw [mem_P1] at hm
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hm0 : (m : ℝ) ≠ 0 := by intro h; rw [h, abs_zero] at hm; linarith [hm.1]
  have hma : 0 < |(m : ℝ)| := abs_pos.mpr hm0
  have e1 : L * (n / q - ξ / m) = L / (q * m) * ((n * m : ℤ) - q * ξ) := by
    push_cast; field_simp
  have e2 : lor (1 / (2 * q * M₁ / L)) ((n * m : ℤ) - q * ξ) =
      lor 1 (L / (2 * q * M₁) * ((n * m : ℤ) - q * ξ)) := by
    unfold lor; congr 1; field_simp
  rw [e1, e2]
  apply lor_anti
  rw [abs_mul, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_of_pos (by positivity : 0 < L / (2 * q * M₁)), abs_div, abs_of_pos hL, abs_mul, Nat.abs_cast]
  apply div_le_div_of_nonneg_left hL.le (by positivity)
  nlinarith [hm.2]

/-! ### The fibres of `(m, n) ↦ nm` -/

/-- **The fibres**: for `s ≠ 0`, the pairs `(m, n)` of a finite set with `nm = s` number at most `2d(|s|)`. -/
lemma card_fiber_le (P : Finset (ℤ × ℤ)) {s : ℤ} (hs : s ≠ 0) :
    ((P.filter fun p => p.2 * p.1 = s).card : ℝ) ≤ 2 * (s.natAbs.divisors.card : ℝ) := by
  classical
  set D : Finset ℤ := (s.natAbs.divisors.image fun d : ℕ => (d : ℤ)) ∪
    (s.natAbs.divisors.image fun d : ℕ => -(d : ℤ)) with hD
  have hinj : Set.InjOn (fun p : ℤ × ℤ => p.1) (P.filter fun p => p.2 * p.1 = s) := by
    intro p₁ hp₁ p₂ hp₂ h
    have h1 := (Finset.mem_filter.1 hp₁).2
    have h2 := (Finset.mem_filter.1 hp₂).2
    simp only at h
    have hm : p₁.1 ≠ 0 := by intro h0; rw [h0, mul_zero] at h1; exact hs h1.symm
    have : p₁.2 = p₂.2 := by
      rw [h] at h1 hm
      exact mul_right_cancel₀ hm (h1.trans h2.symm)
    exact Prod.ext h this
  have hmaps : ∀ p ∈ P.filter (fun p => p.2 * p.1 = s), p.1 ∈ D := by
    intro p hp
    have h1 := (Finset.mem_filter.1 hp).2
    have hdvd : p.1.natAbs ∣ s.natAbs := by
      rw [← h1, Int.natAbs_mul]; exact Dvd.intro_left _ rfl
    have hmem : p.1.natAbs ∈ s.natAbs.divisors := Nat.mem_divisors.2 ⟨hdvd, Int.natAbs_ne_zero.2 hs⟩
    rw [hD, Finset.mem_union]
    rcases Int.natAbs_eq p.1 with h | h
    · left; exact Finset.mem_image.2 ⟨_, hmem, h.symm⟩
    · right; exact Finset.mem_image.2 ⟨_, hmem, h.symm⟩
  have hcard : (P.filter fun p => p.2 * p.1 = s).card ≤ D.card :=
    Finset.card_le_card_of_injOn _ (fun p hp => hmaps p hp) hinj
  have hD2 : D.card ≤ 2 * s.natAbs.divisors.card := by
    calc D.card ≤ (s.natAbs.divisors.image fun d : ℕ => (d : ℤ)).card +
          (s.natAbs.divisors.image fun d : ℕ => -(d : ℤ)).card := Finset.card_union_le _ _
      _ ≤ s.natAbs.divisors.card + s.natAbs.divisors.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * s.natAbs.divisors.card := by ring
  exact_mod_cast hcard.trans hD2

/-! ### The divisor function against the weight -/

/-- `(1 + u)L_1(u)` is at most `2` for `u ≥ 0`, in the scaled form `(1 + |t|/Λ)L_{1/Λ}(t) ≤ 2` for `Λ > 0`. -/
lemma one_add_mul_lor_le {Λ : ℝ} (hΛ : 0 < Λ) (t : ℝ) : (1 + |t| / Λ) * lor (1 / Λ) t ≤ 2 := by
  unfold lor
  have hu : 0 ≤ |t| / Λ := by positivity
  have e : (1 / Λ) ^ 2 * t ^ 2 = (|t| / Λ) ^ 2 := by rw [div_pow, div_pow, sq_abs]; ring
  rw [e, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|t| / Λ - 1)]

/-- **The divisor growth against the weight**: for `0 < δ ≤ 1`, `Λ > 0` and integers `s`,
`|s|^δL_{1/Λ}(s − qξ)² ≤ 2(1 + q|ξ|)^δ(1 + Λ)^δL_{1/Λ}(s − qξ)`. -/
lemma rpow_mul_lor_sq_le {δ Λ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΛ : 0 < Λ) (q : ℕ) (ξ : ℝ) (s : ℤ) :
    (|(s : ℝ)|) ^ δ * lor (1 / Λ) (s - q * ξ) ^ 2 ≤
      2 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ * lor (1 / Λ) (s - q * ξ) := by
  set t : ℝ := s - q * ξ with ht
  have hl0 := lor_pos' (1 / Λ) t
  have hl1 := lor_le_one (1 / Λ) t
  have hqξ : 0 ≤ (q : ℝ) * |ξ| := by positivity
  -- |s| ≤ (1 + q|ξ|)(1 + |t|)
  have hs : |(s : ℝ)| ≤ (1 + q * |ξ|) * (1 + |t|) := by
    have : (s : ℝ) = t + q * ξ := by rw [ht]; ring
    rw [this]
    have h1 := abs_add_le t (q * ξ)
    rw [abs_mul, Nat.abs_cast] at h1
    nlinarith [abs_nonneg t]
  have hs' : |(s : ℝ)| ^ δ ≤ (1 + q * |ξ|) ^ δ * (1 + |t|) ^ δ := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (abs_nonneg _) hs hδ.le
  -- (1 + |t|)^δ ≤ (1 + Λ)^δ(1 + |t|/Λ)
  have ht1 : 1 + |t| ≤ (1 + Λ) * (1 + |t| / Λ) := by
    rw [show (1 + Λ) * (1 + |t| / Λ) = 1 + |t| / Λ + Λ + |t| by field_simp; ring]
    have : 0 ≤ |t| / Λ := by positivity
    linarith
  have ht2 : (1 + |t|) ^ δ ≤ (1 + Λ) ^ δ * (1 + |t| / Λ) := by
    calc (1 + |t|) ^ δ ≤ ((1 + Λ) * (1 + |t| / Λ)) ^ δ := Real.rpow_le_rpow (by positivity) ht1 hδ.le
      _ = (1 + Λ) ^ δ * (1 + |t| / Λ) ^ δ := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (1 + Λ) ^ δ * (1 + |t| / Λ) := by
          gcongr
          calc (1 + |t| / Λ) ^ δ ≤ (1 + |t| / Λ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (by positivity)) hδ1
            _ = 1 + |t| / Λ := Real.rpow_one _
  have h3 := one_add_mul_lor_le hΛ t
  have hA : 0 ≤ (1 + q * |ξ|) ^ δ := by positivity
  have hB : 0 ≤ (1 + Λ) ^ δ := by positivity
  calc |(s : ℝ)| ^ δ * lor (1 / Λ) t ^ 2
      ≤ (1 + q * |ξ|) ^ δ * ((1 + Λ) ^ δ * (1 + |t| / Λ)) * lor (1 / Λ) t ^ 2 := by
        gcongr
        exact hs'.trans (mul_le_mul_of_nonneg_left ht2 hA)
    _ = (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ * ((1 + |t| / Λ) * lor (1 / Λ) t) * lor (1 / Λ) t := by ring
    _ ≤ (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ * 2 * lor (1 / Λ) t := by gcongr
    _ = 2 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ * lor (1 / Λ) t := by ring

/-! ### The count -/

/-- The gcd weight `(x, q)` of a residue. -/
def gw {q : ℕ} (x : ZMod q) : ℝ := (Nat.gcd x.val q : ℝ)

lemma gw_nonneg {q : ℕ} (x : ZMod q) : 0 ≤ gw x := Nat.cast_nonneg _

/-- **The residue classes of `s`**: for `q ≥ 1`, `Λ > 0` and a finite set `S` of integers,
`Σ_{s∈S}L_{1/Λ}(s − y)(s − x, q) ≤ (Σ_{h∈ℤ/qℤ}(h, q))(2π + 4πΛ/q)`. -/
lemma sum_lor_gw_le {q : ℕ} [NeZero q] {Λ : ℝ} (hΛ : 0 < Λ) (S : Finset ℤ) (y : ℝ) (x : ZMod q) :
    ∑ s ∈ S, lor (1 / Λ) (s - y) * gw ((s : ZMod q) - x) ≤
      (∑ h : ZMod q, gw h) * (2 * π + 4 * π * Λ / q) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : ℤ => (s : ZMod q) - x) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _), Finset.sum_mul]
  refine Finset.sum_le_sum fun h _ => ?_
  have e : ∀ s ∈ S.filter (fun s : ℤ => (s : ZMod q) - x = h),
      lor (1 / Λ) (s - y) * gw ((s : ZMod q) - x) = gw h * lor (1 / Λ) (y - s) := by
    intro s hs
    rw [(Finset.mem_filter.1 hs).2, mul_comm, ← lor_neg, neg_sub]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (gw_nonneg h)
  have hsep : ∀ s ∈ S.filter (fun s : ℤ => (s : ZMod q) - x = h),
      ∀ s' ∈ S.filter (fun s : ℤ => (s : ZMod q) - x = h), s ≠ s' → (q : ℝ) ≤ |(s : ℝ) - s'| := by
    intro s hs s' hs' hne
    have h1 := (Finset.mem_filter.1 hs).2
    have h2 := (Finset.mem_filter.1 hs').2
    have hcong : ((s - s' : ℤ) : ZMod q) = 0 := by push_cast; rw [← sub_sub_sub_cancel_right _ _ x, h1, h2, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcong
    obtain ⟨k, hk⟩ := hcong
    have hk0 : k ≠ 0 := by intro h0; rw [h0, mul_zero, sub_eq_zero] at hk; exact hne hk
    have : (s : ℝ) - s' = q * k := by exact_mod_cast hk
    rw [this, abs_mul, Nat.abs_cast]
    have : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    nlinarith
  have hlor := sum_lor_le (S.filter fun s : ℤ => (s : ZMod q) - x = h) (fun s : ℤ => (s : ℝ)) hq
    (by positivity : 0 < 1 / Λ) hsep y
  calc ∑ s ∈ S.filter (fun s : ℤ => (s : ZMod q) - x = h), lor (1 / Λ) (y - s)
      ≤ 2 * π + 4 * π / (1 / Λ * q) := hlor
    _ = 2 * π + 4 * π * Λ / q := by field_simp

/-- **Their count**: for `q ≥ 1`, `L > 0`, `M₁ > 0`, `0 < δ ≤ 1`, real `ξ`, `x ∈ ℤ/qℤ` and a finite set `T` of
integers,
`Σ_{m₁′∈P1 M₁}Σ_{n′∈T, n′≠0}|ψ̂₀(L(n′/q − ξ/m₁′))|(n′m₁′ − x, q) ≤
4C_δB₄(1 + q|ξ|)^δ(1 + 2qM₁/L)^δ(Σ_{h∈ℤ/qℤ}(h, q))(2π + 8πM₁/L)`. -/
theorem count_le {q : ℕ} [NeZero q] {L M₁ δ : ℝ} (hL : 0 < L) (hM₁ : 0 < M₁) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ξ : ℝ) (x : ZMod q) (T : Finset ℤ) :
    ∑ m ∈ P1 M₁, ∑ n ∈ T.filter (· ≠ 0), ‖𝓕 psiC (L * (n / q - ξ / m))‖ * gw ((n : ZMod q) * (m : ZMod q) - x) ≤
      4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * (∑ h : ZMod q, gw h) *
        (2 * π + 8 * π * M₁ / L) := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : (0 : ℝ) < q := by exact_mod_cast hq0
  set Λ : ℝ := 2 * q * M₁ / L with hΛdef
  have hΛ : 0 < Λ := by positivity
  set H : ℤ → ℝ := fun s => B4 * lor (1 / Λ) (s - q * ξ) ^ 2 * gw ((s : ZMod q) - x) with hH
  have hH0 : ∀ s, 0 ≤ H s := fun s => by
    rw [hH]; exact mul_nonneg (mul_nonneg B4_nonneg (sq_nonneg _)) (gw_nonneg _)
  -- each term is at most `H(nm)`
  have hterm : ∀ m ∈ P1 M₁, ∀ n : ℤ, ‖𝓕 psiC (L * (n / q - ξ / m))‖ * gw ((n : ZMod q) * (m : ZMod q) - x) ≤
      H (n * m) := by
    intro m hm n
    rw [hH]
    simp only
    have e : ((n * m : ℤ) : ZMod q) = (n : ZMod q) * (m : ZMod q) := by push_cast; ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (gw_nonneg _)
    refine (norm_fourier_psiC_le_lor _).trans (mul_le_mul_of_nonneg_left ?_ B4_nonneg)
    have h1 := lor_le_lor_prod hq0 hL hM₁ hm n ξ
    have h0 := (lor_pos' 1 (L * (n / q - ξ / m))).le
    exact pow_le_pow_left₀ h0 h1 2
  set P : Finset (ℤ × ℤ) := P1 M₁ ×ˢ T.filter (· ≠ 0) with hP
  have hsum1 : ∑ m ∈ P1 M₁, ∑ n ∈ T.filter (· ≠ 0), ‖𝓕 psiC (L * (n / q - ξ / m))‖ *
      gw ((n : ZMod q) * (m : ZMod q) - x) ≤ ∑ p ∈ P, H (p.2 * p.1) := by
    rw [hP, Finset.sum_product]
    exact Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n _ => hterm m hm n
  -- group by `s = nm`
  set S : Finset ℤ := P.image fun p => p.2 * p.1 with hS
  have hsum2 : ∑ p ∈ P, H (p.2 * p.1) = ∑ s ∈ S, ((P.filter fun p => p.2 * p.1 = s).card : ℝ) * H s := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℤ × ℤ => p.2 * p.1) (t := S)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const, nsmul_eq_mul]
  have hS0 : ∀ s ∈ S, s ≠ 0 := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    rw [hP, Finset.mem_product, Finset.mem_filter] at hp
    have hm : p.1 ≠ 0 := by
      intro h0
      have := (mem_P1 p.1).1 hp.1
      rw [h0, Int.cast_zero, abs_zero] at this
      linarith [this.1]
    exact mul_ne_zero hp.2.2 hm
  -- the multiplicity and the divisor bound
  have hmult : ∀ s ∈ S, ((P.filter fun p => p.2 * p.1 = s).card : ℝ) * H s ≤
      2 * LinnikPower.Cdiv δ * (|(s : ℝ)|) ^ δ * H s := by
    intro s hs
    refine mul_le_mul_of_nonneg_right ?_ (hH0 s)
    refine (card_fiber_le P (hS0 s hs)).trans ?_
    have h := LinnikPower.card_divisors_le hδ hδ1 s.natAbs
    have e : ((s.natAbs : ℕ) : ℝ) = |(s : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e] at h
    linarith
  have hgrow : ∀ s : ℤ, 2 * LinnikPower.Cdiv δ * (|(s : ℝ)|) ^ δ * H s ≤
      4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ *
        (lor (1 / Λ) (s - q * ξ) * gw ((s : ZMod q) - x)) := by
    intro s
    rw [hH]
    simp only
    have hC : 0 ≤ LinnikPower.Cdiv δ := by unfold LinnikPower.Cdiv; positivity
    have h := rpow_mul_lor_sq_le hδ hδ1 hΛ q ξ s
    have hg := gw_nonneg ((s : ZMod q) - x)
    calc 2 * LinnikPower.Cdiv δ * |(s : ℝ)| ^ δ * (B4 * lor (1 / Λ) (s - q * ξ) ^ 2 * gw ((s : ZMod q) - x))
        = 2 * LinnikPower.Cdiv δ * B4 * gw ((s : ZMod q) - x) *
            (|(s : ℝ)| ^ δ * lor (1 / Λ) (s - q * ξ) ^ 2) := by ring
      _ ≤ 2 * LinnikPower.Cdiv δ * B4 * gw ((s : ZMod q) - x) *
            (2 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ * lor (1 / Λ) (s - q * ξ)) := by
          exact mul_le_mul_of_nonneg_left h (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) B4_nonneg) hg)
      _ = 4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ *
            (lor (1 / Λ) (s - q * ξ) * gw ((s : ZMod q) - x)) := by ring
  have hlast := sum_lor_gw_le hΛ S (q * ξ) x
  have hK : 0 ≤ 4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ := by
    have hC : 0 ≤ LinnikPower.Cdiv δ := by unfold LinnikPower.Cdiv; positivity
    have := B4_nonneg
    positivity
  calc _ ≤ ∑ p ∈ P, H (p.2 * p.1) := hsum1
    _ = ∑ s ∈ S, ((P.filter fun p => p.2 * p.1 = s).card : ℝ) * H s := hsum2
    _ ≤ ∑ s ∈ S, 2 * LinnikPower.Cdiv δ * (|(s : ℝ)|) ^ δ * H s := Finset.sum_le_sum hmult
    _ ≤ ∑ s ∈ S, 4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ *
          (lor (1 / Λ) (s - q * ξ) * gw ((s : ZMod q) - x)) := Finset.sum_le_sum fun s _ => hgrow s
    _ = 4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ *
          ∑ s ∈ S, lor (1 / Λ) (s - q * ξ) * gw ((s : ZMod q) - x) := by rw [Finset.mul_sum]
    _ ≤ 4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + Λ) ^ δ *
          ((∑ h : ZMod q, gw h) * (2 * π + 4 * π * Λ / q)) := mul_le_mul_of_nonneg_left hlast hK
    _ = _ := by
        rw [hΛdef]
        field_simp
        ring

end LinnikCGLCount

#print axioms LinnikCGLCount.norm_fourier_psiC_le_lor
#print axioms LinnikCGLCount.lor_le_lor_prod
#print axioms LinnikCGLCount.card_fiber_le
#print axioms LinnikCGLCount.rpow_mul_lor_sq_le
#print axioms LinnikCGLCount.sum_lor_gw_le
#print axioms LinnikCGLCount.count_le
