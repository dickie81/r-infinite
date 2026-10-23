/-
# Round 706: sums over the primes of a cell, from below

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `SieveRough.lean` bounds sums over primes from above (`abel_le`, `sum_inv_le`, `evLe_sum_inv`,
`evLe_cell_inv`); this file bounds them from below, as a refined certificate's kept shares need
(`SieveCert2Defs.keepK`).

* `abel_ge`: Abel summation against `θ`, from below. Let `g ≥ 0` decrease on `[a, b]`, `1 < a ≤ b`, with `G′ = g`, and
  let `|θ(t) − t| ≤ εt/log t` on `[a, b]`. Then `Σ_{a<p≤b} g(p) log p` is at least
  `(G(b) − G(a))(1 − ε/log a) − 2εag(a)/log a − εbg(b)/log b`.
* `sum_inv_ge`: `Σ_{a<p≤b} 1/p ≥ (log log b − log log a)(1 − ε/log a) − 3ε/log² a`, when `a ≤ b`, `log a ≥ 1`
  and `|θ(t) − t| ≤ εt/log t` on `[a, b]`.
* `EvGe`, `EvGe.mul`: `S` is eventually at least `P − δ` for every `δ > 0`; for `S, T ≥ 0` eventually and `P, Q ≥ 0`,
  the product of two such is such for `PQ`.
* `sum_primesIn_ge`: for `f ≥ 0`, a sum over `primesIn A B` is at least the sum over the primes of `(⌊A⌋, ⌊B⌋]` less
  the term at `⌊B⌋`.
* `evGe_sum_inv`: for `0 < a ≤ c`, `Σ_{x^a ≤ p < x^c} 1/p ≥ log c − log a − o(1)`.
* `evGe_cell_inv`: on a grid with `GridOK`, the cell `k`'s `Σ 1/p` is at least `H/(e_k + H)`, up to `o(1)`.

The proofs mirror `SieveRough.abel_le` and `sum_inv_le` with the inequalities reversed: `θ(t) ≥ t(1 − ε/log a)` on
`[a, b]`, and `−g′ ≥ 0`.

The file imports `SieveRough.lean`.
-/
import SieveRough

open Real Finset Filter MeasureTheory
open scoped Chebyshev

namespace SieveRoughLo

open SieveRough

/-! ### Abel summation over the primes, from below -/

/-- **Abel summation against `θ`, from below.** Let `g ≥ 0` decrease on `[a, b]`, `1 < a ≤ b`, with `G′ = g`, and let
`|θ(t) − t| ≤ εt/log t` on `[a, b]`. Then `Σ_{a<p≤b} g(p) log p` is at least
`(G(b) − G(a))(1 − ε/log a) − 2εag(a)/log a − εbg(b)/log b`. -/
theorem abel_ge {a b ε : ℝ} (ha : 1 < a) (hab : a ≤ b) {g g' G : ℝ → ℝ}
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t) (hg'c : ContinuousOn g' (Set.Icc a b))
    (hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (g t) t)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) (hg'0 : ∀ t ∈ Set.Icc a b, g' t ≤ 0)
    (hε : 0 ≤ ε) (hθ : ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε * t / Real.log t) :
    (G b - G a) * (1 - ε / Real.log a) - 2 * ε * a * g a / Real.log a - ε * b * g b / Real.log b ≤
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, g p * Real.log p := by
  have ha0 : 0 ≤ a := by linarith
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ g t := fun t ht => (hg t ht).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc a b, deriv g t = g' t := fun t ht => (hg t ht).deriv
  have hint : IntegrableOn (deriv g) (Set.Icc a b) :=
    (hg'c.integrableOn_Icc).congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul cθ ha0 hab hdiff hint
  simp only [sum_cθ] at habel
  have hlhs : ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, g k * cθ k =
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, g p * Real.log p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold cθ
    split_ifs <;> simp
  rw [← hlhs, habel]
  -- the integral as an interval integral of `g′θ`
  have hIoc : ∫ t in Set.Ioc a b, deriv g t * θ t = ∫ t in a..b, g' t * θ t := by
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hderiv t (Set.Ioc_subset_Icc_self ht)]
  rw [hIoc]
  -- integrability
  have hθint : IntegrableOn (fun t => g' t * θ t) (Set.Icc a b) := by
    have h := integrableOn_mul_sum_Icc cθ (m := 0) ha0 (hg'c.integrableOn_Icc)
    simp only [sum_cθ] at h
    exact h
  have hθii : IntervalIntegrable (fun t => g' t * θ t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hθint
  have hcont_t : ContinuousOn (fun t => g' t * t) (Set.Icc a b) := hg'c.mul continuousOn_id
  have htii : IntervalIntegrable (fun t => g' t * t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hcont_t.integrableOn_Icc
  -- `∫ g′(t) t = (g(b)b − G(b)) − (g(a)a − G(a))`
  have hFTC : ∫ t in a..b, g' t * t = (g b * b - G b) - (g a * a - G a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have h := ((hg t ht).mul (hasDerivAt_id' t)).sub (hG t ht)
      convert h using 1
      ring
    · exact htii
  -- `−g′ t (1 − ε/log a) ≤ −g′θ` on `[a, b]`
  have hpt : ∀ t ∈ Set.Icc a b, -(g' t * t) * (1 - ε / Real.log a) ≤ -(g' t * θ t) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have hlt : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    have hlt0 : 0 < Real.log t := Real.log_pos ht1
    have hθt := hθ t ht
    have hdn : t - ε * t / Real.log t ≤ θ t := by linarith [neg_abs_le (θ t - t)]
    have hη : ε * t / Real.log t ≤ ε * t / Real.log a :=
      div_le_div_of_nonneg_left (by nlinarith) hla hlt
    have hg' := hg'0 t ht
    have : t * (1 - ε / Real.log a) ≤ θ t := by
      have : t * (1 - ε / Real.log a) = t - ε * t / Real.log a := by field_simp
      linarith
    nlinarith
  have hint_le : ∫ t in a..b, -(g' t * t) * (1 - ε / Real.log a) ≤ ∫ t in a..b, -(g' t * θ t) :=
    intervalIntegral.integral_mono_on hab (htii.neg.mul_const _) hθii.neg hpt
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
    hFTC] at hint_le
  -- the endpoint terms
  have hθb := hθ b ⟨hab, le_rfl⟩
  have hθa := hθ a ⟨le_rfl, hab⟩
  have hgb := hg0 b ⟨hab, le_rfl⟩
  have hga := hg0 a ⟨le_rfl, hab⟩
  have hb_dn : b - ε * b / Real.log b ≤ θ b := by linarith [neg_abs_le (θ b - b)]
  have ha_up : θ a ≤ a + ε * a / Real.log a := by linarith [le_abs_self (θ a - a)]
  have e1 : g b * b - g b * (ε * b / Real.log b) ≤ g b * θ b := by
    have := mul_le_mul_of_nonneg_left hb_dn hgb
    linarith
  have e2 : g a * θ a ≤ g a * a + g a * (ε * a / Real.log a) := by
    have := mul_le_mul_of_nonneg_left ha_up hga
    linarith
  have e3 : 0 ≤ ε / Real.log a * (g b * b) := by
    have : 0 ≤ g b * b := mul_nonneg hgb (by linarith)
    positivity
  have hexp : -((g b * b - G b) - (g a * a - G a)) * (1 - ε / Real.log a) =
      (G b - G a) * (1 - ε / Real.log a) - (g b * b) + ε / Real.log a * (g b * b) + g a * a -
        ε / Real.log a * (g a * a) := by ring
  have hfin : g a * (ε * a / Real.log a) = ε / Real.log a * (g a * a) := by ring
  have hfin2 : 2 * ε * a * g a / Real.log a = 2 * (ε / Real.log a * (g a * a)) := by ring
  have hfin3 : ε * b * g b / Real.log b = g b * (ε * b / Real.log b) := by ring
  rw [hfin2, hfin3]
  linarith

/-! ### The sum of `1/p`, from below -/

/-- `Σ_{a<p≤b} 1/p ≥ (log log b − log log a)(1 − ε/log a) − 3ε/log² a`, when `log a ≥ 1`, `a ≤ b` and
`|θ(t) − t| ≤ εt/log t` on `[a, b]`. -/
theorem sum_inv_ge {a b ε : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε * t / Real.log t) :
    (Real.log (Real.log b) - Real.log (Real.log a)) * (1 - ε / Real.log a) - 3 * ε / Real.log a ^ 2 ≤
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
  have ha1 : 1 < a := lt_of_lt_of_le (by have := Real.add_one_le_exp 1; linarith) ha
  have hla1 : 1 ≤ Real.log a := by rw [Real.le_log_iff_exp_le (by linarith)]; exact ha
  have hla : 0 < Real.log a := by linarith
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t ∧ 0 < Real.log t := fun t ht =>
    ⟨by linarith [ht.1], Real.log_pos (by linarith [ht.1])⟩
  set g : ℝ → ℝ := fun t => (t * Real.log t)⁻¹ with hgdef
  set g' : ℝ → ℝ := fun t => -(Real.log t + 1) / (t * Real.log t) ^ 2 with hg'def
  set G : ℝ → ℝ := fun t => Real.log (Real.log t) with hGdef
  have hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    obtain ⟨ht0, hl0⟩ := hpos t ht
    have hc : HasDerivAt (fun y => y * Real.log y) (Real.log t + 1) t := by
      have h2 := (hasDerivAt_id' t).mul (Real.hasDerivAt_log ht0.ne')
      convert h2 using 1
      field_simp
    exact hc.inv (by positivity)
  have hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (g t) t := by
    intro t ht
    obtain ⟨ht0, hl0⟩ := hpos t ht
    have h := (Real.hasDerivAt_log ht0.ne').log hl0.ne'
    show HasDerivAt (fun y => Real.log (Real.log y)) ((t * Real.log t)⁻¹) t
    convert h using 1
    field_simp
  have hg'c : ContinuousOn g' (Set.Icc a b) := by
    have hl := continuousOn_log_Icc (a := a) (b := b) (by linarith)
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    obtain ⟨ht0, hl0⟩ := hpos t ht
    positivity
  have hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t := fun t ht => by
    obtain ⟨ht0, hl0⟩ := hpos t ht; simp only [hgdef]; positivity
  have hg'0 : ∀ t ∈ Set.Icc a b, g' t ≤ 0 := fun t ht => by
    obtain ⟨ht0, hl0⟩ := hpos t ht
    simp only [hg'def]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    linarith
  have habel := abel_ge ha1 hab hg hg'c hG hg0 hg'0 hε hθ
  have hterm : ∀ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, g p * Real.log p = 1 / (p : ℝ) := by
    intro p hp
    have hpp : (p : ℕ).Prime := (Finset.mem_filter.1 hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    simp only [hgdef]
    field_simp
  rw [Finset.sum_congr rfl hterm] at habel
  refine le_trans ?_ habel
  simp only [hGdef, hgdef]
  have hb0 : 0 < b := by linarith
  have hlb0 : 0 < Real.log b := by linarith
  have e2 : 2 * ε * a * (a * Real.log a)⁻¹ / Real.log a = 2 * ε / Real.log a ^ 2 := by field_simp
  have e3 : ε * b * (b * Real.log b)⁻¹ / Real.log b ≤ ε / Real.log a ^ 2 := by
    have : ε * b * (b * Real.log b)⁻¹ / Real.log b = ε / Real.log b ^ 2 := by field_simp
    rw [this]
    apply div_le_div_of_nonneg_left hε (by positivity)
    nlinarith
  have : 3 * ε / Real.log a ^ 2 = 2 * ε / Real.log a ^ 2 + ε / Real.log a ^ 2 := by ring
  linarith

/-! ### Eventually from below -/

/-- `S` is eventually at least `P − δ`, for every `δ > 0`: `liminf S ≥ P`. -/
def EvGe (S : ℝ → ℝ) (P : ℝ) : Prop := ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop, P - δ ≤ S x

/-- The product of two functions eventually nonnegative, with `EvGe` at `P` and `Q`, `P, Q ≥ 0`, has `EvGe` at `PQ`:
for every `δ > 0` it is eventually at least `PQ − δ`. -/
theorem EvGe.mul {S T : ℝ → ℝ} {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hS0 : ∀ᶠ x : ℝ in atTop, 0 ≤ S x)
    (hT0 : ∀ᶠ x : ℝ in atTop, 0 ≤ T x) (hS : EvGe S P) (hT : EvGe T Q) :
    EvGe (fun x => S x * T x) (P * Q) := by
  intro δ hδ
  obtain ⟨d, hd⟩ : ∃ d, d = δ / (P + Q + 1) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hd2 : d * (P + Q) ≤ δ := by
    calc d * (P + Q) ≤ d * (P + Q + 1) := by nlinarith
      _ = δ := by rw [hd]; field_simp
  filter_upwards [hS0, hT0, hS d hd0, hT d hd0] with x h1 h2 h3 h4
  show P * Q - δ ≤ S x * T x
  by_cases hPd : d ≤ P
  · by_cases hQd : d ≤ Q
    · calc P * Q - δ ≤ P * Q - d * (P + Q) + d * d := by nlinarith
        _ = (P - d) * (Q - d) := by ring
        _ ≤ S x * T x := mul_le_mul h3 h4 (by linarith) h1
    · push Not at hQd
      have : P * Q ≤ d * (P + Q) := by nlinarith
      nlinarith [mul_nonneg h1 h2]
  · push Not at hPd
    have : P * Q ≤ d * (P + Q) := by nlinarith
    nlinarith [mul_nonneg h1 h2]

/-- For `f ≥ 0`, a sum over `primesIn A B` is at least the sum over the primes of `(⌊A⌋₊, ⌊B⌋₊]` less the term at
`⌊B⌋₊`. -/
theorem sum_primesIn_ge {A B : ℝ} {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, f p - f ⌊B⌋₊ ≤ ∑ p ∈ primesIn A B, f p := by
  set s := (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime with hs
  have hsub : s ⊆ insert ⌊B⌋₊ (primesIn A B) := by
    intro p hp
    rw [hs, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpp⟩ := hp
    rw [Finset.mem_insert]
    by_cases h : p = ⌊B⌋₊
    · exact Or.inl h
    · have h3 : p < ⌊B⌋₊ := lt_of_le_of_ne h2 h
      have hB : (0 : ℝ) ≤ B := by
        by_contra hB
        push Not at hB
        rw [Nat.floor_of_nonpos hB.le] at h3
        omega
      refine Or.inr (mem_primesIn.2 ⟨hpp, ?_, ?_⟩)
      · have h4 : ((⌊A⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast h1
        push_cast at h4
        linarith [Nat.lt_floor_add_one A]
      · calc (p : ℝ) < ⌊B⌋₊ := by exact_mod_cast h3
          _ ≤ B := Nat.floor_le hB
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf p)
  have h' : ∑ p ∈ insert ⌊B⌋₊ (primesIn A B), f p ≤ f ⌊B⌋₊ + ∑ p ∈ primesIn A B, f p := by
    by_cases hm : ⌊B⌋₊ ∈ primesIn A B
    · rw [Finset.insert_eq_of_mem hm]; linarith [hf ⌊B⌋₊]
    · rw [Finset.sum_insert hm]
  linarith

/-- For `0 < a ≤ c`, `Σ_{x^a ≤ p < x^c} 1/p ≥ log c − log a − o(1)`. -/
theorem evGe_sum_inv {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    EvGe (fun x => ∑ p ∈ primesIn (x ^ a) (x ^ c), 1 / (p : ℝ)) (Real.log c - Real.log a) := by
  intro δ hδ
  have hP : 0 ≤ Real.log c - Real.log a := sub_nonneg.2 (Real.log_le_log ha hac)
  obtain ⟨P, hPdef⟩ : ∃ P, P = Real.log c - Real.log a := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  obtain ⟨εθ, hεθ⟩ : ∃ εθ, εθ = δ / (2 * (P + 3)) := ⟨_, rfl⟩
  have hεθ0 : 0 < εθ := by rw [hεθ]; positivity
  have hεθP : εθ * (P + 3) = δ / 2 := by rw [hεθ]; field_simp
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (theta_near hεθ0)
  have hx : ∀ᶠ x : ℝ in atTop, max (max T (Real.exp 1)) (2 / δ + 1) ≤ x ^ a :=
    (tendsto_rpow_atTop ha).eventually_ge_atTop _
  filter_upwards [hx, eventually_ge_atTop 1] with x hxa hx1
  have hA : T ≤ x ^ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxa
  have hAe : Real.exp 1 ≤ x ^ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxa
  have hAδ : 2 / δ + 1 ≤ x ^ a := le_trans (le_max_right _ _) hxa
  have hAB : x ^ a ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx1 hac
  have hA0 : 0 < x ^ a := lt_of_lt_of_le (Real.exp_pos 1) hAe
  have hx0 : 0 < x := by linarith
  have hθ : ∀ t ∈ Set.Icc (x ^ a) (x ^ c), |θ t - t| ≤ εθ * t / Real.log t :=
    fun t ht => hT t (le_trans hA ht.1)
  have h1 := sum_inv_ge hAe hAB hεθ0.le hθ
  have h2 := sum_primesIn_ge (A := x ^ a) (B := x ^ c) (f := fun p : ℕ => 1 / (p : ℝ)) (fun p => by positivity)
  have hla : 1 ≤ Real.log (x ^ a) := by rw [Real.le_log_iff_exp_le hA0]; exact hAe
  have hlx : 0 < Real.log x := by
    rw [Real.log_rpow hx0] at hla
    by_contra h
    push Not at h
    nlinarith
  have hll : Real.log (Real.log (x ^ c)) - Real.log (Real.log (x ^ a)) = P := by
    rw [Real.log_rpow hx0, Real.log_rpow hx0, Real.log_mul (by linarith) hlx.ne',
      Real.log_mul ha.ne' hlx.ne', hPdef]
    ring
  rw [hll] at h1
  have h3 : P * (1 - εθ) ≤ P * (1 - εθ / Real.log (x ^ a)) :=
    mul_le_mul_of_nonneg_left (by linarith [div_le_self hεθ0.le hla]) hP
  have h4 : 3 * εθ / Real.log (x ^ a) ^ 2 ≤ 3 * εθ :=
    div_le_self (by positivity) (one_le_pow₀ hla)
  have h5 : 1 / (⌊x ^ c⌋₊ : ℝ) ≤ δ / 2 := by
    have hfl : x ^ c - 1 < (⌊x ^ c⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have hpos : (0 : ℝ) < 2 / δ := by positivity
    have hge : 2 / δ ≤ (⌊x ^ c⌋₊ : ℝ) := by linarith
    calc 1 / (⌊x ^ c⌋₊ : ℝ) ≤ 1 / (2 / δ) := one_div_le_one_div_of_le hpos hge
      _ = δ / 2 := by rw [one_div_div]
  show P - δ ≤ ∑ p ∈ primesIn (x ^ a) (x ^ c), 1 / (p : ℝ)
  nlinarith

variable [SieveCert.Grid] [SieveCert.GridOK]

/-- **The cell's `Σ 1/p`, from below.** On a grid with `GridOK`, the cell `k`'s `Σ 1/p` is at least
`h/(a + h) = H/(e_k + H)`, up to `o(1)`. -/
theorem evGe_cell_inv (k : ℕ) :
    EvGe (fun x => ∑ p ∈ cellP x k, 1 / (p : ℝ)) ((SieveCert.H : ℝ) / ((SieveCert.e k : ℝ) + SieveCert.H)) := by
  have hek : (0 : ℝ) < SieveCert.e k := by exact_mod_cast SieveCert.e_pos k
  have hH : (0 : ℝ) < SieveCert.H := by exact_mod_cast SieveCert.H_pos
  have hD := SieveCert.DEN_pos'
  have ha : (0 : ℝ) < (SieveCert.e k : ℝ) / SieveCert.DEN := div_pos hek hD
  have hac : (SieveCert.e k : ℝ) / SieveCert.DEN ≤ ((SieveCert.e k : ℝ) + SieveCert.H) / SieveCert.DEN :=
    div_le_div_of_nonneg_right (by linarith) hD.le
  have hlog : (SieveCert.H : ℝ) / ((SieveCert.e k : ℝ) + SieveCert.H) ≤
      Real.log (((SieveCert.e k : ℝ) + SieveCert.H) / SieveCert.DEN) -
        Real.log ((SieveCert.e k : ℝ) / SieveCert.DEN) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have heq : ((SieveCert.e k : ℝ) + SieveCert.H) / SieveCert.DEN / ((SieveCert.e k : ℝ) / SieveCert.DEN) =
        ((SieveCert.e k : ℝ) + SieveCert.H) / SieveCert.e k := by field_simp
    rw [heq]
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < ((SieveCert.e k : ℝ) + SieveCert.H) / SieveCert.e k by
      positivity)
    have h2 : 1 - (((SieveCert.e k : ℝ) + SieveCert.H) / SieveCert.e k)⁻¹ =
        (SieveCert.H : ℝ) / ((SieveCert.e k : ℝ) + SieveCert.H) := by field_simp; ring
    linarith
  intro δ hδ
  filter_upwards [evGe_sum_inv ha hac δ hδ] with x hx
  exact le_trans (by linarith) hx

end SieveRoughLo

#print axioms SieveRoughLo.sum_inv_ge
#print axioms SieveRoughLo.evGe_cell_inv
