/-
# Round 689: the constants of their Lemma 8.2 (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li bound the gcd sums of their §8.2 by a divisor estimate: "when q|n, the only dependence on d is (d,q) and
we have that" (lines 2892–2893; spaces restored) `Σ_{d mod q}(d, q)/q ⪅ 1` (lines 2893–2896, transcribed). This file
bounds two constants of round 688's Lemma 8.2, round 682's `W₀` and round 683's `K_X`, with the parameters `L`, `X`
and `δ` left free under the hypotheses below; round 691 chooses them.

The stack's form.
* Their `Σ_{d mod q}(d, q)/q ⪅ 1` is `Σ_{h mod q}(h, q) ≤ q·d(q)` (`sum_gw_le`), with `d(q) ≤ C_δq^δ` round 525's
  `card_divisors_le`; the residues `h mod q` with `d ∣ h` number at most `q/d` (`card_dvd_val_le`).
* `q ≤ φ(q)d(q)` (`le_totient_mul_card_divisors`), from Euler's product (Mathlib's `Nat.totient_mul_prod_primeFactors`)
  and `d(q) ≥ 2^{ω(q)}`.
* For `M₁ < 1/2` or `M₂ < 1/2`, round 680's `P1` or `P2` is empty, and round 662's `Jint` is `0` (`Jint_eq_zero`).

Plain statements, with `q ≥ 1` (`[NeZero q]`), `d(q)` the number of divisors of `q`, `B₄` round 681's `B4`, `C_δ` round
525's `Cdiv` and `F = Σ_b∫f_b`.
* `card_Icc_ceil_le`, `card_P1_le`, `card_P2_le`, `card_P3_le`, `sum_P2_le`: for `x ≥ 0`, the integers in `[−⌈x⌉, ⌈x⌉]`
  number at most `2x + 3`; hence, for `M₁, M₂, L ≥ 0`, `#P1 M₁ ≤ 4M₁ + 3`, `#P2 M₂ ≤ 4M₂ + 3`, `#P3 L ≤ 4L + 3` and
  `Σ_{m₂∈P2 M₂}m₂ ≤ (4M₂ + 3)·2M₂`.
* `P1_eq_empty`, `P2_eq_empty`, `Jint_eq_zero`: for `M₁ < 1/2`, `P1 M₁ = ∅`; for `M₂ < 1/2`, `P2 M₂ = ∅`; and if
  `M₁ < 1/2` or `M₂ < 1/2`, `Jint(f, M₁, M₂, M₃, κ) = 0` for every `f`, `M₃` and `κ`.
* `card_dvd_val_le`, `sum_gw_le`: for `d ∣ q`, `#{h mod q : d ∣ h} ≤ q/d`; and `Σ_{h mod q}(h, q) ≤ q·d(q)`.
* `le_totient_mul_card_divisors`: `n ≤ φ(n)d(n)` for every natural number `n`.
* `W0_le`: for `f_b ≥ 0`, `M₁, M₂ ≥ 1/2` and `L ≥ 0`, round 682's `W₀ ≤ 200B₄L·d(q)M₂²F`.
* `KX_le`: for `L > 0`, `0 ≤ M₁ ≤ L`, `X ≥ 0` and `0 < δ ≤ 1`, round 683's
  `K_X ≤ 40πC_δB₄d(q)⁴L²q(1 + qX)^δ(1 + 2q)^δ`.

The file imports `LinnikCGLL82.lean`.
-/

import LinnikCGLL82

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLConst

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov LinnikCGLSig2 LinnikCGLFtil
  LinnikCGLLoc LinnikCGLJtil LinnikCGLTail LinnikCGLL82

/-! ### The sizes of `P1`, `P2` and `P3` -/

/-- For `x ≥ 0`, the integers in `[−⌈x⌉, ⌈x⌉]` number at most `2x + 3`. -/
lemma card_Icc_ceil_le {x : ℝ} (hx : 0 ≤ x) : ((Finset.Icc (-⌈x⌉) ⌈x⌉).card : ℝ) ≤ 2 * x + 3 := by
  rw [Int.card_Icc]
  have h0 : 0 ≤ ⌈x⌉ := Int.ceil_nonneg hx
  have h1 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hn : 0 ≤ ⌈x⌉ + 1 - -⌈x⌉ := by omega
  have e : (((⌈x⌉ + 1 - -⌈x⌉).toNat : ℕ) : ℝ) = 2 * (⌈x⌉ : ℝ) + 1 := by
    have : (((⌈x⌉ + 1 - -⌈x⌉).toNat : ℕ) : ℤ) = ⌈x⌉ + 1 - -⌈x⌉ := Int.toNat_of_nonneg hn
    have h2 : (((⌈x⌉ + 1 - -⌈x⌉).toNat : ℕ) : ℝ) = ((⌈x⌉ + 1 - -⌈x⌉ : ℤ) : ℝ) := by exact_mod_cast this
    rw [h2]; push_cast; ring
  rw [e]; linarith

/-- For `M₁ ≥ 0`, `#P1 M₁ ≤ 4M₁ + 3`. -/
lemma card_P1_le {M₁ : ℝ} (hM₁ : 0 ≤ M₁) : ((P1 M₁).card : ℝ) ≤ 4 * M₁ + 3 := by
  have h := card_Icc_ceil_le (x := 2 * M₁) (by positivity)
  have h' : (P1 M₁).card ≤ (Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉).card := Finset.card_filter_le _ _
  have : ((P1 M₁).card : ℝ) ≤ (Finset.Icc (-⌈2 * M₁⌉) ⌈2 * M₁⌉).card := by exact_mod_cast h'
  linarith

/-- For `M₂ ≥ 0`, `#P2 M₂ ≤ 4M₂ + 3`. -/
lemma card_P2_le {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : ((P2 M₂).card : ℝ) ≤ 4 * M₂ + 3 := by
  have h := card_Icc_ceil_le (x := 2 * M₂) (by positivity)
  have h' : (P2 M₂).card ≤ (Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉).card := Finset.card_filter_le _ _
  have : ((P2 M₂).card : ℝ) ≤ (Finset.Icc (-⌈2 * M₂⌉) ⌈2 * M₂⌉).card := by exact_mod_cast h'
  linarith

/-- For `L ≥ 0`, `#P3 L ≤ 4L + 3`. -/
lemma card_P3_le {L : ℝ} (hL : 0 ≤ L) : ((P3 L).card : ℝ) ≤ 4 * L + 3 := by
  have h := card_Icc_ceil_le (x := 2 * L) (by positivity)
  unfold P3
  linarith

/-- For `M₂ ≥ 0`, `Σ_{m₂∈P2 M₂}m₂ ≤ (4M₂ + 3)·2M₂`. -/
lemma sum_P2_le {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) ≤ (4 * M₂ + 3) * (2 * M₂) := by
  calc ∑ m₂ ∈ P2 M₂, (m₂ : ℝ) ≤ ∑ _m₂ ∈ P2 M₂, 2 * M₂ :=
        Finset.sum_le_sum fun m₂ hm₂ => ((mem_P2 m₂).1 hm₂).2
    _ = (P2 M₂).card * (2 * M₂) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * M₂ + 3) * (2 * M₂) := mul_le_mul_of_nonneg_right (card_P2_le hM₂) (by positivity)

/-- For `M₁ < 1/2`, `P1 M₁` is empty. -/
lemma P1_eq_empty {M₁ : ℝ} (h : M₁ < 1 / 2) : P1 M₁ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
  obtain ⟨h1, h2⟩ := (mem_P1 m).1 hm
  have hlt : |(m : ℝ)| < 1 := by linarith
  have hm0 : m = 0 := by
    have : |m| < 1 := by exact_mod_cast hlt
    have := abs_lt.mp this
    omega
  rw [hm0, Int.cast_zero, abs_zero] at h1 h2
  linarith

/-- For `M₂ < 1/2`, `P2 M₂` is empty. -/
lemma P2_eq_empty {M₂ : ℝ} (h : M₂ < 1 / 2) : P2 M₂ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
  obtain ⟨h1, h2⟩ := (mem_P2 m).1 hm
  have hpos : (0 : ℝ) < m := by linarith
  have hlt : (m : ℝ) < 1 := by linarith
  have h3 : (0 : ℤ) < m := by exact_mod_cast hpos
  have h4 : m < (1 : ℤ) := by exact_mod_cast hlt
  omega

/-- For `q ≥ 1` with `M₁ < 1/2` or `M₂ < 1/2`, round 662's `Jint` is `0`: `setJ` is empty. -/
lemma Jint_eq_zero {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℝ → ℝ) {M₁ M₂ : ℝ} (M₃ κ : ℝ)
    (h : M₁ < 1 / 2 ∨ M₂ < 1 / 2) : Jint f M₁ M₂ M₃ κ = 0 := by
  have hS : setJ M₁ M₂ M₃ κ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
    obtain ⟨h1, h2, h3, h4, -⟩ := (mem_setJ m).1 hm
    rcases h with h | h
    · have : m.1 ∈ P1 M₁ := (mem_P1 _).2 ⟨h1, h2⟩
      rw [P1_eq_empty h] at this
      exact Finset.notMem_empty _ this
    · have : m.2.1 ∈ P2 M₂ := (mem_P2 _).2 ⟨h3, h4⟩
      rw [P2_eq_empty h] at this
      exact Finset.notMem_empty _ this
  unfold Jint gJ
  simp [hS]

/-! ### `Σ_h(h, q)` and `q/φ(q)` -/

/-- For `q ≥ 1` and `d ∣ q`, at most `q/d` residues `h mod q` have `d ∣ h`. -/
lemma card_dvd_val_le {q : ℕ} [NeZero q] {d : ℕ} (hd : d ∣ q) :
    (Finset.univ.filter fun h : ZMod q => d ∣ h.val).card ≤ q / d := by
  calc (Finset.univ.filter fun h : ZMod q => d ∣ h.val).card ≤ (Finset.range (q / d)).card := by
        refine Finset.card_le_card_of_injOn (fun h => h.val / d) (fun h hh => ?_) (fun h₁ hh₁ h₂ hh₂ e => ?_)
        · rw [Finset.mem_coe, Finset.mem_range]
          exact Nat.div_lt_div_of_lt_of_dvd hd (ZMod.val_lt h)
        · have d₁ := (Finset.mem_filter.1 (Finset.mem_coe.1 hh₁)).2
          have d₂ := (Finset.mem_filter.1 (Finset.mem_coe.1 hh₂)).2
          have e' : h₁.val = h₂.val := by
            rw [← Nat.div_mul_cancel d₁, ← Nat.div_mul_cancel d₂]
            exact congrArg (· * d) e
          exact ZMod.val_injective q e'
    _ = q / d := Finset.card_range _

/-- For `q ≥ 1`, `Σ_{h mod q}(h, q) ≤ q·d(q)`, for round 681's `gw`. -/
lemma sum_gw_le {q : ℕ} [NeZero q] : ∑ h : ZMod q, gw h ≤ q * q.divisors.card := by
  classical
  have key : ∀ h : ZMod q, gw h ≤ ∑ d ∈ q.divisors, if d ∣ h.val then (d : ℝ) else 0 := by
    intro h
    have hg : Nat.gcd h.val q ∈ q.divisors := Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, NeZero.ne q⟩
    have := Finset.single_le_sum (f := fun d => if d ∣ h.val then (d : ℝ) else 0)
      (fun d _ => by positivity) hg
    simpa [gw, Nat.gcd_dvd_left] using this
  calc ∑ h : ZMod q, gw h ≤ ∑ h : ZMod q, ∑ d ∈ q.divisors, if d ∣ h.val then (d : ℝ) else 0 :=
        Finset.sum_le_sum fun h _ => key h
    _ = ∑ d ∈ q.divisors, ∑ h : ZMod q, if d ∣ h.val then (d : ℝ) else 0 := Finset.sum_comm
    _ = ∑ d ∈ q.divisors, (d : ℝ) * (Finset.univ.filter fun h : ZMod q => d ∣ h.val).card := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ _d ∈ q.divisors, (q : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hdq := Nat.dvd_of_mem_divisors hd
        have h1 := card_dvd_val_le (q := q) hdq
        have h2 : (d : ℝ) * ((q / d : ℕ) : ℝ) = q := by exact_mod_cast Nat.mul_div_cancel' hdq
        calc (d : ℝ) * (Finset.univ.filter fun h : ZMod q => d ∣ h.val).card ≤ d * ((q / d : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast h1) (Nat.cast_nonneg _)
          _ = q := h2
    _ = q * q.divisors.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- `n ≤ φ(n)·d(n)`: `n/φ(n) = Π_{p∣n}p/(p − 1) ≤ 2^{ω(n)} ≤ d(n)`. -/
lemma le_totient_mul_card_divisors (n : ℕ) : n ≤ n.totient * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : n ≠ 0 := hn.ne'
  have h := Nat.totient_mul_prod_primeFactors n
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have hprod : ∏ p ∈ n.primeFactors, p ≤ 2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have h2 : n ≤ n.totient * 2 ^ n.primeFactors.card := by
    have : n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n.totient * 2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
      rw [← h, mul_assoc]
      exact Nat.mul_le_mul_left _ hprod
    exact Nat.le_of_mul_le_mul_right this hpos
  have h3 : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
    rw [Nat.card_divisors hn0, ← Finset.prod_const]
    refine Finset.prod_le_prod fun p hp => ?_
    have : n.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (by rwa [Nat.support_factorization])
    omega
  exact h2.trans (Nat.mul_le_mul_left _ h3)

/-! ### `W₀` and `K_X` -/

/-- For `q ≥ 1`, `f_b ≥ 0`, `M₁, M₂ ≥ 1/2` and `L ≥ 0`, round 682's `W₀ ≤ 200B₄L·d(q)M₂²F`, with `F = Σ_b∫f_b`. -/
lemma W0_le {q : ℕ} [NeZero q] {f : (ZMod q)ˣ → ℝ → ℝ} (hf : ∀ b u, 0 ≤ f b u) {M₁ M₂ L : ℝ}
    (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) (hL : 0 ≤ L) :
    W0 f M₁ M₂ L ≤ 200 * B4 * L * q.divisors.card * M₂ ^ 2 * ∑ b, ∫ u, f b u := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hF : 0 ≤ ∑ b, ∫ u, f b u := Finset.sum_nonneg fun b _ => integral_nonneg fun u => hf b u
  have hB := B4_nonneg
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have h1 : ((P1 M₁).card : ℝ) ≤ 10 * M₁ := by linarith [card_P1_le (by linarith : (0 : ℝ) ≤ M₁)]
  have h2 : ((P2 M₂).card : ℝ) ≤ 10 * M₂ := by linarith [card_P2_le (by linarith : (0 : ℝ) ≤ M₂)]
  have h3 := sum_gw_le (q := q)
  have hM₁0 : 0 < M₁ := by linarith
  unfold W0
  calc ((P1 M₁).card : ℝ) * (L / q) * B4 * (∑ h : ZMod q, gw h) *
        ((P2 M₂).card * (2 * M₂ / M₁) * ∑ b, ∫ u, f b u)
      ≤ 10 * M₁ * (L / q) * B4 * (q * q.divisors.card) * (10 * M₂ * (2 * M₂ / M₁) * ∑ b, ∫ u, f b u) := by
        gcongr
    _ = 200 * B4 * L * q.divisors.card * M₂ ^ 2 * ∑ b, ∫ u, f b u := by
        field_simp
        ring

/-- For `q ≥ 1`, `L > 0`, `0 ≤ M₁ ≤ L`, `X ≥ 0` and `0 < δ ≤ 1`, round 683's
`K_X ≤ 40πC_δB₄d(q)⁴L²q(1 + qX)^δ(1 + 2q)^δ`. -/
lemma KX_le {q : ℕ} [NeZero q] {L M₁ X δ : ℝ} (hL : 0 < L) (hM₁ : 0 ≤ M₁) (hM₁L : M₁ ≤ L) (hX : 0 ≤ X)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    KX q L M₁ X δ ≤ 40 * π * LinnikPower.Cdiv δ * B4 * (q.divisors.card : ℝ) ^ 4 * L ^ 2 * q *
      (1 + q * X) ^ δ * (1 + 2 * q) ^ δ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hB := B4_nonneg
  have hC : 0 ≤ LinnikPower.Cdiv δ := le_trans zero_le_one (LinnikPower.one_le_Cdiv hδ hδ1)
  have hG : 0 ≤ ∑ h : ZMod q, gw h := Finset.sum_nonneg fun h _ => gw_nonneg h
  have h3 := sum_gw_le (q := q)
  have hd : (0 : ℝ) ≤ q.divisors.card := Nat.cast_nonneg _
  have hML : M₁ / L ≤ 1 := (div_le_one hL).2 hM₁L
  have hML0 : 0 ≤ M₁ / L := div_nonneg hM₁ hL.le
  have hp1 : (1 + 2 * q * M₁ / L) ^ δ ≤ (1 + 2 * q) ^ δ := by
    refine Real.rpow_le_rpow (by positivity) ?_ hδ.le
    have : 2 * q * M₁ / L = 2 * q * (M₁ / L) := by ring
    rw [this]
    nlinarith
  have hp2 : 2 * π + 8 * π * M₁ / L ≤ 10 * π := by
    have : 8 * π * M₁ / L = 8 * π * (M₁ / L) := by ring
    rw [this]
    nlinarith [Real.pi_pos]
  unfold KX
  rw [abs_of_nonneg hX]
  calc (q.divisors.card : ℝ) * (L / q) ^ 2 * (∑ h : ZMod q, gw h) ^ 2 *
        (4 * LinnikPower.Cdiv δ * B4 * (1 + q * X) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * (∑ h : ZMod q, gw h) *
          (2 * π + 8 * π * M₁ / L))
      ≤ (q.divisors.card : ℝ) * (L / q) ^ 2 * (q * q.divisors.card) ^ 2 *
        (4 * LinnikPower.Cdiv δ * B4 * (1 + q * X) ^ δ * (1 + 2 * q) ^ δ * (q * q.divisors.card) * (10 * π)) := by
        gcongr
    _ = 40 * π * LinnikPower.Cdiv δ * B4 * (q.divisors.card : ℝ) ^ 4 * L ^ 2 * q *
          (1 + q * X) ^ δ * (1 + 2 * q) ^ δ := by
        field_simp
        ring

end LinnikCGLConst

#print axioms LinnikCGLConst.Jint_eq_zero
#print axioms LinnikCGLConst.sum_gw_le
#print axioms LinnikCGLConst.le_totient_mul_card_divisors
#print axioms LinnikCGLConst.W0_le
#print axioms LinnikCGLConst.KX_le
