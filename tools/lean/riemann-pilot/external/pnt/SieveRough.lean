/-
# Round 597: rough numbers from above, and the shares of the certificate's cells (milestone M6)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements.

* `psi_le`: for every `U` and `ε > 0` there is `z₀` such that `Ψ(y, z) ≤ (ω*(u) + ε)y/log z` for `z ≥ z₀`, `y ≥ 1`
  and `u = log 2y/log z ≤ U`. Here `Ψ(y, z) = #{m ∈ (y, 2y] : p | m ⇒ p ≥ z}` (`Psi`), and `ω*` is the crude bound
  for Buchstab's `ω` (`SieveCert.omegaC`: `0` below `1`, `1/u` on `[1, 2)` and `0.5672` from `2` on).
* `share2`: let `cellP x k` be the primes whose exponent `log p/log x` lies in the cell `k` of `SieveCert`'s grid
  (`mem_cellP`). For a cell `(i, j)` with `e_i + 2e_j ≤ DEN`, as for a candidate cell, and every `δ > 0`, eventually
  in `x`: `Σ_{p₁ ∈ cellP x i} Σ_{p₂ ∈ cellP x j} Ψ(x/(p₁p₂), p₂) ≤ (bound2(e_i, e_j)/K + δ)x/log x`.
* `share4`: for a cell `(i, j, k, l)` with `e_i + e_j + e_k + 2e_l ≤ DEN`, as for a counted cell, and every `δ > 0`,
  eventually in `x`: the sum of `Ψ(x/(p₁p₂p₃p₄), p₄)` over the primes of the four cells is at most
  `(bound4(e_i, e_j, e_k, e_l)/K + δ)x/log x`.
* `share2_of_cand`, `share4_of_counted4`: the two on the cells that pass `SieveCert.cand` and `SieveCert.counted4`.

This is milestone M6 of `frontier/linnik/SIEVE-ROUTE.md` §13. `Ψ(x/d, p)` counts the integers `n = dm ∈ (x, 2x]`
whose cofactor `m` has no prime factor below `p`. The shares bound these counts, summed over a cell's primes, by the
certificate's own bounds `bound2/K` and `bound4/K`, from which `SieveCert.total` is summed.

The proof:

* `theta_near`: `|θ(t) − t| ≤ εt/log t` for all large `t`, from the stack's `ψ(t) − t = O(t^{23/24})`
  (`HalfPlanePNT.psi_isBigO_eleven_twelfths`) and Mathlib's `ψ − θ ≤ 2√t log t` (`Chebyshev.psi_sub_theta_le`).
* `abel_le`: Abel summation against `θ`, from above (Mathlib's `sum_mul_eq_sub_sub_integral_mul`). With it,
  `sum_inv_mul_log_le`, `sum_inv_le` and `sum_inv_mul_sub_log_le` bound `Σ 1/(p log p)`, `Σ 1/p` and
  `Σ 1/(p(L − log p))` over the primes of `(a, b]`, and `card_primes_dyadic` bounds the number of primes in
  `(y, 2y]`.
* `Psi_eq_zero`, `Psi_le_buchstab`: `Ψ(y, z) = 0` when `y ≥ 1` and `2y < z`, and for `y ≥ 2` Buchstab's inequality
  by the least prime factor, `Ψ(y, z) ≤ #{p : y < p ≤ 2y} + Σ_{z ≤ p ≤ √(2y)} Ψ(y/p, p)`.
* `one_add_log_le`, `one_add_log_two_le`, `super_M`: `ω*` is a supersolution of Buchstab's delay equation,
  `1 + ∫_1^{u−1} ω* ≤ uω*(u)` for `u ≥ 2`. On `[2, 3]` this is `1 + log(u − 1) ≤ 0.5672u`; above `3` it is
  `1 + log 2 ≤ 3·0.5672`.
* `rangeA_le`, `rangeB_le`, `sumW_le_three`, `sumW_gt_three`: with `L = log 2y`, the sum of
  `ω*((L − log p)/log p)/(p log p)` over the primes of `(z, √(2y)]`, where `ω* = 0.5672` for `log p ≤ L/3` and
  `ω* = log p/(L − log p)` above.
* `Claim`, `claim_step`, `claim_nat`, `psi_le`: the induction on the level `K` in `log 2y ≤ K log z`.
* `evLe_sum_inv`, `evLe_sum_inv_log`, `evLe_cell_inv`, `evLe_cell_inv_log`: for large `x`, the primes of
  `[x^a, x^c)` have `Σ 1/p ≤ log c − log a + δ` and `log x · Σ 1/(p log p) ≤ 1/a − 1/c + δ`; on the cell `k`, whose
  side is `h = H/DEN` and whose lower corner is `a = e_k/DEN`, these are at most `h/a + δ` and `h/a² + δ`.
* `psi_point`: at a point of a cell, `psi_le` and `SieveCert.omegaC_le` give
  `Ψ(x/(dp), p) ≤ (omK/K + ε)x/(dp log p)`.
* `evLe_finish`, `share2`, `share4`: each share is at most `(omK/K + ε)x/log x` times the product of the cells'
  prime sums (`Σ 1/p`, and `log x · Σ 1/(p log p)` for the last cell). For large `x` that product is at most the
  product of the cells' `h/a` and `h/a²`, plus `δ`, and `SieveCert.bound2_ge` and `SieveCert.bound4_ge` bound
  `omK/K` times the product by `bound2/K` and `bound4/K`.
-/
import HalfPlaneFinal
import LinnikTwelveSizes
import SieveCert

open Real Filter Finset MeasureTheory
open scoped Chebyshev

namespace SieveRough

/-! ### `θ(t) = t + o(t/log t)` -/

/-- From the stack's prime number theorem, `|θ(t) − t| ≤ εt/log t` for all large `t`. -/
theorem theta_near {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t : ℝ in atTop, |θ t - t| ≤ ε * t / Real.log t := by
  obtain ⟨C, hC⟩ := (HalfPlanePNT.psi_isBigO_eleven_twelfths (ε := 1 / 24) (by norm_num)).bound
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  filter_upwards [hC, LinnikTwelve.ev_log_pow ((C' + 2) / ε) (1 / 24) 2 (by norm_num),
    eventually_ge_atTop (2 : ℝ)] with t ht hlog ht2
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hpow : t ^ ((11 : ℝ) / 12 + 1 / 24) = t ^ ((23 : ℝ) / 24) := by norm_num
  have h1 : |ψ t - t| ≤ C' * t ^ ((23 : ℝ) / 24) := by
    simp only [Pi.sub_apply, id, Real.norm_eq_abs] at ht
    rw [abs_of_pos (Real.rpow_pos_of_pos ht0 _), hpow] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h2 : 0 ≤ ψ t - θ t := sub_nonneg.2 (Chebyshev.theta_le_psi t)
  have h3 : ψ t - θ t ≤ 2 * √t * Real.log t := Chebyshev.psi_sub_theta_le ht1
  have hsum : |θ t - t| ≤ C' * t ^ ((23 : ℝ) / 24) + 2 * √t * Real.log t := by
    calc |θ t - t| = |(ψ t - t) - (ψ t - θ t)| := by ring_nf
      _ ≤ |ψ t - t| + |ψ t - θ t| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h2]; linarith
  have hsq : √t ≤ t ^ ((23 : ℝ) / 24) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hl1 : Real.log t ≤ (1 + Real.log t) ^ 2 := by nlinarith
  have hl2 : Real.log t * Real.log t ≤ (1 + Real.log t) ^ 2 := by nlinarith
  have hT : 0 < t ^ ((23 : ℝ) / 24) := Real.rpow_pos_of_pos ht0 _
  have hsplit : t ^ ((23 : ℝ) / 24) * t ^ ((1 : ℝ) / 24) = t := by
    rw [← Real.rpow_add ht0]; norm_num
  have key : (C' * t ^ ((23 : ℝ) / 24) + 2 * √t * Real.log t) * Real.log t ≤ ε * t := by
    have e1 : (C' * t ^ ((23 : ℝ) / 24) + 2 * √t * Real.log t) * Real.log t
        ≤ (C' + 2) * t ^ ((23 : ℝ) / 24) * (1 + Real.log t) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hl1 (mul_nonneg hC'0 hT.le)
      have := mul_le_mul_of_nonneg_left hl2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hT.le)
      have := mul_le_mul_of_nonneg_right hsq (by positivity : (0:ℝ) ≤ 2 * Real.log t * Real.log t)
      nlinarith
    have e2 : (C' + 2) * (1 + Real.log t) ^ 2 ≤ ε * t ^ ((1 : ℝ) / 24) := by
      have := hlog
      rw [div_mul_eq_mul_div, div_le_iff₀ hε] at this
      linarith
    calc (C' * t ^ ((23 : ℝ) / 24) + 2 * √t * Real.log t) * Real.log t
        ≤ (C' + 2) * t ^ ((23 : ℝ) / 24) * (1 + Real.log t) ^ 2 := e1
      _ = t ^ ((23 : ℝ) / 24) * ((C' + 2) * (1 + Real.log t) ^ 2) := by ring
      _ ≤ t ^ ((23 : ℝ) / 24) * (ε * t ^ ((1 : ℝ) / 24)) := mul_le_mul_of_nonneg_left e2 hT.le
      _ = ε * (t ^ ((23 : ℝ) / 24) * t ^ ((1 : ℝ) / 24)) := by ring
      _ = ε * t := by rw [hsplit]
  rw [le_div_iff₀ hL]
  calc |θ t - t| * Real.log t ≤ (C' * t ^ ((23 : ℝ) / 24) + 2 * √t * Real.log t) * Real.log t :=
        mul_le_mul_of_nonneg_right hsum hL.le
    _ ≤ ε * t := key

/-! ### Abel summation over the primes -/

/-- `log k` at the primes and `0` elsewhere; its partial sums are `θ`. -/
noncomputable def cθ (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

theorem sum_cθ (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, cθ k = θ t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]; rfl

/-- **Abel summation against `θ`, from above.** Let `g ≥ 0` decrease on `[a, b]`, `1 < a ≤ b`, with `G′ = g`, and
let `|θ(t) − t| ≤ εt/log t` on `[a, b]`. Then `Σ_{a<p≤b} g(p) log p` is at most
`(G(b) − G(a))(1 + ε/log a) + 2εag(a)/log a + εbg(b)/log b`. -/
theorem abel_le {a b ε : ℝ} (ha : 1 < a) (hab : a ≤ b) {g g' G : ℝ → ℝ}
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t) (hg'c : ContinuousOn g' (Set.Icc a b))
    (hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (g t) t)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) (hg'0 : ∀ t ∈ Set.Icc a b, g' t ≤ 0)
    (hε : 0 ≤ ε) (hθ : ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε * t / Real.log t) :
    ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, g p * Real.log p ≤
      (G b - G a) * (1 + ε / Real.log a) + 2 * ε * a * g a / Real.log a + ε * b * g b / Real.log b := by
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
  -- `−g′θ ≤ −g′ t (1 + ε/log a)` on `[a, b]`
  have hpt : ∀ t ∈ Set.Icc a b, -(g' t * θ t) ≤ -(g' t * t) * (1 + ε / Real.log a) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have hlt : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    have hlt0 : 0 < Real.log t := Real.log_pos ht1
    have hθt := hθ t ht
    have hup : θ t ≤ t + ε * t / Real.log t := by linarith [le_abs_self (θ t - t)]
    have hη : ε * t / Real.log t ≤ ε * t / Real.log a :=
      div_le_div_of_nonneg_left (by nlinarith) hla hlt
    have hg' := hg'0 t ht
    have : θ t ≤ t * (1 + ε / Real.log a) := by
      have : t * (1 + ε / Real.log a) = t + ε * t / Real.log a := by field_simp
      linarith
    nlinarith
  have hint_le : ∫ t in a..b, -(g' t * θ t) ≤ ∫ t in a..b, -(g' t * t) * (1 + ε / Real.log a) :=
    intervalIntegral.integral_mono_on hab hθii.neg (htii.neg.mul_const _) hpt
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
    hFTC] at hint_le
  -- the endpoint terms
  have hθb := hθ b ⟨hab, le_rfl⟩
  have hθa := hθ a ⟨le_rfl, hab⟩
  have hgb := hg0 b ⟨hab, le_rfl⟩
  have hga := hg0 a ⟨le_rfl, hab⟩
  have hb_up : θ b ≤ b + ε * b / Real.log b := by linarith [le_abs_self (θ b - b)]
  have ha_dn : a - ε * a / Real.log a ≤ θ a := by linarith [neg_abs_le (θ a - a)]
  have e1 : g b * θ b ≤ g b * b + ε * b * g b / Real.log b := by
    have := mul_le_mul_of_nonneg_left hb_up hgb
    have h' : g b * (b + ε * b / Real.log b) = g b * b + ε * b * g b / Real.log b := by ring
    linarith
  have e2 : g a * a - ε * a * g a / Real.log a ≤ g a * θ a := by
    have := mul_le_mul_of_nonneg_left ha_dn hga
    have h' : g a * (a - ε * a / Real.log a) = g a * a - ε * a * g a / Real.log a := by ring
    linarith
  have e3 : 0 ≤ ε / Real.log a * (g b * b) := by
    have : 0 ≤ g b * b := mul_nonneg hgb (by linarith)
    positivity
  have hexp : -((g b * b - G b) - (g a * a - G a)) * (1 + ε / Real.log a) =
      (G b - G a) * (1 + ε / Real.log a) - (g b * b) - ε / Real.log a * (g b * b) + g a * a +
        ε / Real.log a * (g a * a) := by ring
  have hfin : ε * a * g a / Real.log a = ε / Real.log a * (g a * a) := by ring
  have hfin2 : 2 * ε * a * g a / Real.log a = 2 * (ε / Real.log a * (g a * a)) := by ring
  have hfin3 : ε * b * g b / Real.log b = g b * (ε * b / Real.log b) := by ring
  have e1' : g b * θ b ≤ g b * b + g b * (ε * b / Real.log b) := by linarith
  have e2' : g a * a - ε / Real.log a * (g a * a) ≤ g a * θ a := by linarith
  rw [hfin2, hfin3]
  linarith

/-! ### Three prime sums -/

theorem continuousOn_log_Icc {a b : ℝ} (ha : 0 < a) : ContinuousOn Real.log (Set.Icc a b) :=
  Real.continuousOn_log.mono fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]

/-- `Σ_{a<p≤b} 1/(p log p) ≤ 1/log a − 1/log b + 4ε/log² a`, when `log a ≥ 1` and `|θ(t) − t| ≤ εt/log t` on
`[a, b]`. -/
theorem sum_inv_mul_log_le {a b ε : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε * t / Real.log t) :
    ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1 / ((p : ℝ) * Real.log p) ≤
      1 / Real.log a - 1 / Real.log b + 4 * ε / Real.log a ^ 2 := by
  have ha1 : 1 < a := lt_of_lt_of_le (by have := Real.add_one_le_exp 1; linarith) ha
  have hla1 : 1 ≤ Real.log a := by rw [Real.le_log_iff_exp_le (by linarith)]; exact ha
  have hla : 0 < Real.log a := by linarith
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t ∧ 0 < Real.log t := fun t ht =>
    ⟨by linarith [ht.1], Real.log_pos (by linarith [ht.1])⟩
  set g : ℝ → ℝ := fun t => (t * Real.log t ^ 2)⁻¹ with hgdef
  set g' : ℝ → ℝ := fun t => -(Real.log t ^ 2 + 2 * Real.log t) / (t * Real.log t ^ 2) ^ 2 with hg'def
  set G : ℝ → ℝ := fun t => -(Real.log t)⁻¹ with hGdef
  have hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    obtain ⟨ht0, hl0⟩ := hpos t ht
    have hc : HasDerivAt (fun y => y * Real.log y ^ 2) (Real.log t ^ 2 + 2 * Real.log t) t := by
      have h2 := (hasDerivAt_id' t).mul ((Real.hasDerivAt_log ht0.ne').pow 2)
      convert h2 using 1
      simp only [Pi.pow_apply]
      field_simp
      ring
    exact hc.inv (by positivity)
  have hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (g t) t := by
    intro t ht
    obtain ⟨ht0, hl0⟩ := hpos t ht
    have h := ((Real.hasDerivAt_log ht0.ne').inv hl0.ne').neg
    convert h using 1
    simp only [hgdef]
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
    nlinarith
  have habel := abel_le ha1 hab hg hg'c hG hg0 hg'0 hε hθ
  have hterm : ∀ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, g p * Real.log p = 1 / ((p : ℝ) * Real.log p) := by
    intro p hp
    have hpp : (p : ℕ).Prime := (Finset.mem_filter.1 hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    simp only [hgdef]
    field_simp
  rw [Finset.sum_congr rfl hterm] at habel
  refine habel.trans ?_
  simp only [hGdef, hgdef]
  have hb1 : 1 < b := by linarith
  have hb0 : 0 < b := by linarith
  have hlb0 : 0 < Real.log b := by linarith
  have e1 : (-(Real.log b)⁻¹ - -(Real.log a)⁻¹) * (1 + ε / Real.log a) ≤
      1 / Real.log a - 1 / Real.log b + ε / Real.log a ^ 2 := by
    have h1 : 0 ≤ 1 / Real.log a - 1 / Real.log b := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hla hlb
    have h2 : (1 / Real.log a - 1 / Real.log b) * (ε / Real.log a) ≤ ε / Real.log a ^ 2 := by
      have : 1 / Real.log a - 1 / Real.log b ≤ 1 / Real.log a := by
        have : 0 ≤ 1 / Real.log b := by positivity
        linarith
      calc (1 / Real.log a - 1 / Real.log b) * (ε / Real.log a) ≤ 1 / Real.log a * (ε / Real.log a) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = ε / Real.log a ^ 2 := by ring
    have : (-(Real.log b)⁻¹ - -(Real.log a)⁻¹) = 1 / Real.log a - 1 / Real.log b := by ring
    rw [this]; nlinarith
  have e2 : 2 * ε * a * (a * Real.log a ^ 2)⁻¹ / Real.log a ≤ 2 * ε / Real.log a ^ 2 := by
    have : 2 * ε * a * (a * Real.log a ^ 2)⁻¹ / Real.log a = 2 * ε / Real.log a ^ 2 / Real.log a := by
      field_simp
    rw [this]
    exact div_le_self (by positivity) hla1
  have e3 : ε * b * (b * Real.log b ^ 2)⁻¹ / Real.log b ≤ ε / Real.log a ^ 2 := by
    have : ε * b * (b * Real.log b ^ 2)⁻¹ / Real.log b = ε / Real.log b ^ 3 := by field_simp
    rw [this]
    have hlb1 : 1 ≤ Real.log b := le_trans hla1 hlb
    calc ε / Real.log b ^ 3 ≤ ε / Real.log b ^ 2 := by
          apply div_le_div_of_nonneg_left hε (by positivity)
          nlinarith
      _ ≤ ε / Real.log a ^ 2 := by
          apply div_le_div_of_nonneg_left hε (by positivity)
          nlinarith
  have : 4 * ε / Real.log a ^ 2 = ε / Real.log a ^ 2 + 2 * ε / Real.log a ^ 2 + ε / Real.log a ^ 2 := by ring
  linarith

/-- `Σ_{a<p≤b} 1/p ≤ (log log b − log log a)(1 + ε/log a) + 3ε/log² a`, when `log a ≥ 1` and
`|θ(t) − t| ≤ εt/log t` on `[a, b]`. -/
theorem sum_inv_le {a b ε : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε * t / Real.log t) :
    ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1 / (p : ℝ) ≤
      (Real.log (Real.log b) - Real.log (Real.log a)) * (1 + ε / Real.log a) + 3 * ε / Real.log a ^ 2 := by
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
  have habel := abel_le ha1 hab hg hg'c hG hg0 hg'0 hε hθ
  have hterm : ∀ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, g p * Real.log p = 1 / (p : ℝ) := by
    intro p hp
    have hpp : (p : ℕ).Prime := (Finset.mem_filter.1 hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    simp only [hgdef]
    field_simp
  rw [Finset.sum_congr rfl hterm] at habel
  refine habel.trans ?_
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

/-- `Σ_{a<p≤b} 1/(p(L − log p)) ≤ (G(b) − G(a))(1 + ε/log a) + 6ε/(L log² a)`, where
`G(t) = (log log t − log(L − log t))/L`, when `log a ≥ 1`, `2 log b ≤ L` and `|θ(t) − t| ≤ εt/log t` on `[a, b]`. -/
theorem sum_inv_mul_sub_log_le {L a b ε : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (hbL : 2 * Real.log b ≤ L)
    (hε : 0 ≤ ε) (hθ : ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε * t / Real.log t) :
    ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1 / ((p : ℝ) * (L - Real.log p)) ≤
      ((Real.log (Real.log b) - Real.log (L - Real.log b)) / L -
        (Real.log (Real.log a) - Real.log (L - Real.log a)) / L) * (1 + ε / Real.log a) +
        6 * ε / (L * Real.log a ^ 2) := by
  have ha1 : 1 < a := lt_of_lt_of_le (by have := Real.add_one_le_exp 1; linarith) ha
  have hla1 : 1 ≤ Real.log a := by rw [Real.le_log_iff_exp_le (by linarith)]; exact ha
  have hla : 0 < Real.log a := by linarith
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hL : 0 < L := by linarith
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t ∧ 0 < Real.log t ∧ 2 * Real.log t ≤ L := fun t ht =>
    ⟨by linarith [ht.1], Real.log_pos (by linarith [ht.1]),
      by linarith [Real.log_le_log (by linarith [ht.1]) ht.2]⟩
  set g : ℝ → ℝ := fun t => (t * Real.log t * (L - Real.log t))⁻¹ with hgdef
  set g' : ℝ → ℝ := fun t => -(Real.log t * (L - Real.log t) + (L - Real.log t) - Real.log t) /
    (t * Real.log t * (L - Real.log t)) ^ 2 with hg'def
  set G : ℝ → ℝ := fun t => (Real.log (Real.log t) - Real.log (L - Real.log t)) / L with hGdef
  have hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    obtain ⟨ht0, hl0, hLt⟩ := hpos t ht
    have hLt0 : 0 < L - Real.log t := by linarith
    have hc : HasDerivAt (fun y => y * Real.log y * (L - Real.log y))
        (Real.log t * (L - Real.log t) + (L - Real.log t) - Real.log t) t := by
      have h1 := (hasDerivAt_id' t).mul (Real.hasDerivAt_log ht0.ne')
      have h2 := h1.mul ((Real.hasDerivAt_log ht0.ne').const_sub L)
      convert h2 using 1
      simp only [Pi.mul_apply]
      field_simp
      ring
    exact hc.inv (by positivity)
  have hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (g t) t := by
    intro t ht
    obtain ⟨ht0, hl0, hLt⟩ := hpos t ht
    have hLt0 : 0 < L - Real.log t := by linarith
    have h1 := (Real.hasDerivAt_log ht0.ne').log hl0.ne'
    have h2 := ((Real.hasDerivAt_log ht0.ne').const_sub L).log hLt0.ne'
    have h := (h1.sub h2).div_const L
    show HasDerivAt (fun y => (Real.log (Real.log y) - Real.log (L - Real.log y)) / L)
      ((t * Real.log t * (L - Real.log t))⁻¹) t
    convert h using 1
    field_simp
    ring
  have hg'c : ContinuousOn g' (Set.Icc a b) := by
    have hl := continuousOn_log_Icc (a := a) (b := b) (by linarith)
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    obtain ⟨ht0, hl0, hLt⟩ := hpos t ht
    have hLt0 : 0 < L - Real.log t := by linarith
    positivity
  have hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t := fun t ht => by
    obtain ⟨ht0, hl0, hLt⟩ := hpos t ht
    have hLt0 : 0 < L - Real.log t := by linarith
    simp only [hgdef]; positivity
  have hg'0 : ∀ t ∈ Set.Icc a b, g' t ≤ 0 := fun t ht => by
    obtain ⟨ht0, hl0, hLt⟩ := hpos t ht
    have hLt0 : 0 < L - Real.log t := by linarith
    simp only [hg'def]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith
  have habel := abel_le ha1 hab hg hg'c hG hg0 hg'0 hε hθ
  have hterm : ∀ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
      g p * Real.log p = 1 / ((p : ℝ) * (L - Real.log p)) := by
    intro p hp
    have hpp : (p : ℕ).Prime := (Finset.mem_filter.1 hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    simp only [hgdef]
    field_simp
  rw [Finset.sum_congr rfl hterm] at habel
  refine habel.trans ?_
  simp only [hGdef, hgdef]
  have hb0 : 0 < b := by linarith
  have hlb0 : 0 < Real.log b := by linarith
  have hLa : L / 2 ≤ L - Real.log a := by linarith
  have hLb : L / 2 ≤ L - Real.log b := by linarith
  have e2 : 2 * ε * a * (a * Real.log a * (L - Real.log a))⁻¹ / Real.log a ≤ 4 * ε / (L * Real.log a ^ 2) := by
    have h0 : 0 < L - Real.log a := by linarith
    have : 2 * ε * a * (a * Real.log a * (L - Real.log a))⁻¹ / Real.log a =
        2 * ε / (Real.log a ^ 2 * (L - Real.log a)) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.log a), mul_nonneg hε (sq_nonneg (Real.log a))]
  have e3 : ε * b * (b * Real.log b * (L - Real.log b))⁻¹ / Real.log b ≤ 2 * ε / (L * Real.log a ^ 2) := by
    have h0 : 0 < L - Real.log b := by linarith
    have : ε * b * (b * Real.log b * (L - Real.log b))⁻¹ / Real.log b =
        ε / (Real.log b ^ 2 * (L - Real.log b)) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : Real.log a ^ 2 ≤ Real.log b ^ 2 := by nlinarith
    nlinarith [mul_nonneg hε (sq_nonneg (Real.log a)), mul_le_mul_of_nonneg_left hsq hε]
  have : 6 * ε / (L * Real.log a ^ 2) = 4 * ε / (L * Real.log a ^ 2) + 2 * ε / (L * Real.log a ^ 2) := by ring
  linarith

/-! ### Rough numbers and Buchstab's inequality -/

/-- The rough numbers in a dyadic range: `m ∈ (y, 2y]` all of whose prime factors are at least `z`. -/
noncomputable def roughSet (y : ℝ) (z : ℕ) : Finset ℕ :=
  (Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter fun m => ∀ p ∈ m.primeFactors, z ≤ p

/-- `Ψ(y, z) = #{m ∈ (y, 2y] : p | m ⇒ p ≥ z}`. -/
noncomputable def Psi (y : ℝ) (z : ℕ) : ℕ := (roughSet y z).card

theorem mem_Ioc_floor {y : ℝ} (hy : 0 ≤ y) {m : ℕ} :
    m ∈ Ioc ⌊y⌋₊ ⌊2 * y⌋₊ ↔ y < m ∧ (m : ℝ) ≤ 2 * y := by
  rw [Finset.mem_Ioc, Nat.floor_lt hy, Nat.le_floor_iff (by linarith)]

/-- Below `u = 1` (`2y < z`, `y ≥ 1`) there are no rough numbers. -/
theorem Psi_eq_zero {y : ℝ} {z : ℕ} (hy : 1 ≤ y) (h : 2 * y < z) : Psi y z = 0 := by
  unfold Psi roughSet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hr
  rw [mem_Ioc_floor (by linarith)] at hm
  have hm1 : m ≠ 1 := by
    rintro rfl; norm_num at hm; linarith [hm.1]
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm; linarith [hm.1]
  have hp := Nat.minFac_prime hm1
  have hz := hr _ (Nat.mem_primeFactors.2 ⟨hp, Nat.minFac_dvd m, hm0⟩)
  have hle : (m.minFac : ℝ) ≤ m := by exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hm0)
  have : (z : ℝ) ≤ m.minFac := by exact_mod_cast hz
  linarith [hm.2]

/-- **Buchstab's inequality.** For `y ≥ 2`, a rough number in `(y, 2y]` is a prime, or `p·m′` with `p ≥ z` its least
prime factor, `p² ≤ 2y` and `m′` rough for `p` in `(y/p, 2y/p]`. -/
theorem Psi_le_buchstab {y : ℝ} {z : ℕ} (hy : 2 ≤ y) :
    (Psi y z : ℝ) ≤ ((Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime).card +
      ∑ p ∈ (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime, (Psi (y / p) p : ℝ) := by
  have hy0 : 0 ≤ y := by linarith
  set S := Ioc ⌊y⌋₊ ⌊2 * y⌋₊ with hS
  set C := (roughSet y z).filter fun m => ¬ m.Prime with hC
  have hsplit : roughSet y z ⊆ S.filter Nat.Prime ∪ C := by
    intro m hm
    by_cases hp : m.Prime
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hm).1, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hm, hp⟩)
  have hCsub : C ⊆ ((Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime).biUnion
      (fun p => (roughSet (y / p) p).image (fun m' => p * m')) := by
    intro m hm
    obtain ⟨hmR, hmp⟩ := Finset.mem_filter.1 hm
    obtain ⟨hmS, hr⟩ := Finset.mem_filter.1 hmR
    rw [mem_Ioc_floor hy0] at hmS
    have hm0 : m ≠ 0 := by rintro rfl; norm_num at hmS; linarith [hmS.1]
    have hm1 : m ≠ 1 := by rintro rfl; norm_num at hmS; linarith [hmS.1]
    set p := m.minFac with hpdef
    have hpp : p.Prime := Nat.minFac_prime hm1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpz : z ≤ p := hr _ (Nat.mem_primeFactors.2 ⟨hpp, Nat.minFac_dvd m, hm0⟩)
    have hsq : p ^ 2 ≤ m := Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hm0) hmp
    have hpsqrt : p ≤ ⌊√(2 * y)⌋₊ := by
      rw [Nat.le_floor_iff (Real.sqrt_nonneg _)]
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have : ((p ^ 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hsq
      push_cast at this
      linarith [hmS.2]
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpz, hpsqrt⟩, hpp⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨m / p, ?_, Nat.mul_div_cancel' (Nat.minFac_dvd m)⟩
    have hmeq : ((m / p : ℕ) : ℝ) = m / p := by
      rw [Nat.cast_div (Nat.minFac_dvd m) hp0.ne']
    unfold roughSet
    rw [Finset.mem_filter, mem_Ioc_floor (by positivity), hmeq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact div_lt_div_of_pos_right hmS.1 hp0
    · rw [div_le_iff₀ hp0]
      have : 2 * (y / p) * p = 2 * y := by field_simp
      linarith [hmS.2]
    · intro q hq
      obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hq
      exact Nat.minFac_le_of_dvd hqp.two_le (hqd.trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd m)))
  have h1 : (roughSet y z).card ≤ (S.filter Nat.Prime).card + C.card :=
    (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have h2 : C.card ≤ ∑ p ∈ (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime, (roughSet (y / p) p).card :=
    (Finset.card_le_card hCsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun p _ => Finset.card_image_le))
  unfold Psi
  have h3 : ((roughSet y z).card : ℝ) ≤ (S.filter Nat.Prime).card +
      ((∑ p ∈ (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime, (roughSet (y / p) p).card : ℕ) : ℝ) := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  push_cast at h3
  exact h3

/-! ### The primes in `(y, 2y]` -/

theorem sum_log_primes_dyadic {y : ℝ} (hy : 0 ≤ y) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime, Real.log p = θ (2 * y) - θ y := by
  have hle : ⌊y⌋₊ ≤ ⌊2 * y⌋₊ := Nat.floor_le_floor (by linarith)
  unfold Chebyshev.theta
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle]
  ring

/-- `#{p : y < p ≤ 2y} ≤ (1 + ε)y/log 2y` for all large `y`. -/
theorem card_primes_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, (((Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime).card : ℝ) ≤ (1 + ε) * y / Real.log (2 * y) := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (theta_near (ε := ε' / 8) (by positivity))
  refine ⟨max (max T 2) (Real.exp (4 / ε')), fun y hy => ?_⟩
  have hyT : T ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hyexp : Real.exp (4 / ε') ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : 0 < y := by linarith
  have hly : 4 / ε' ≤ Real.log y := by rwa [Real.le_log_iff_exp_le hy0]
  have hly0 : 0 < Real.log y := lt_of_lt_of_le (by positivity) hly
  have hl2y : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set N := ((Ioc ⌊y⌋₊ ⌊2 * y⌋₊).filter Nat.Prime).card with hN
  -- `N log y ≤ θ(2y) − θ(y)`
  have hNlog : (N : ℝ) * Real.log y ≤ θ (2 * y) - θ y := by
    rw [← sum_log_primes_dyadic hy0.le, hN, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).1
    rw [mem_Ioc_floor hy0.le] at hp'
    simp only [Nat.cast_one, one_mul]
    exact Real.log_le_log hy0 hp'.1.le
  have hθ2 := hT (2 * y) (by linarith)
  have hθ1 := hT y hyT
  have hl2y' : Real.log y ≤ Real.log (2 * y) := by rw [hl2y]; linarith
  have hb2 : θ (2 * y) ≤ 2 * y + ε' / 8 * (2 * y) / Real.log (2 * y) := by
    linarith [le_abs_self (θ (2 * y) - 2 * y)]
  have hb1 : y - ε' / 8 * y / Real.log y ≤ θ y := by linarith [neg_abs_le (θ y - y)]
  have hb2' : ε' / 8 * (2 * y) / Real.log (2 * y) ≤ ε' / 4 * y / Real.log y := by
    rw [div_le_div_iff₀ (by linarith) hly0]
    nlinarith [mul_pos hε'0 hy0]
  have hdiff : θ (2 * y) - θ y ≤ y * (1 + 3 * ε' / 8 / Real.log y) := by
    have : y * (1 + 3 * ε' / 8 / Real.log y) = y + ε' / 4 * y / Real.log y + ε' / 8 * y / Real.log y := by
      field_simp; ring
    linarith
  -- `N ≤ (y/log y)(1 + 3ε′/(8 log y)) ≤ (1 + ε)y/log 2y`
  have hNle : (N : ℝ) ≤ y / Real.log y * (1 + 3 * ε' / 8 / Real.log y) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hly0]
    linarith
  refine hNle.trans ?_
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hly0 (by linarith), hl2y]
  -- `y(1 + 3ε′/(8 log y))(log 2 + log y) ≤ (1 + ε)y log y`
  have hk : 3 * ε' / 8 / Real.log y ≤ 3 * ε' * ε' / 32 := by
    rw [div_le_iff₀ hly0]
    have : 3 * ε' * ε' / 32 * Real.log y ≥ 3 * ε' * ε' / 32 * (4 / ε') := by
      apply mul_le_mul_of_nonneg_left hly (by positivity)
    have h' : 3 * ε' * ε' / 32 * (4 / ε') = 3 * ε' / 8 := by field_simp; ring
    linarith
  have hk2 : Real.log 2 ≤ ε' / 4 * Real.log y := by
    have : ε' / 4 * Real.log y ≥ ε' / 4 * (4 / ε') := mul_le_mul_of_nonneg_left hly (by positivity)
    have h' : ε' / 4 * (4 / ε') = 1 := by field_simp
    linarith
  have hk0 : 0 ≤ 3 * ε' / 8 / Real.log y := by positivity
  set k := 3 * ε' / 8 / Real.log y with hkdef
  have hly4 : 4 ≤ Real.log y := le_trans (by rw [le_div_iff₀ hε'0]; linarith) hly
  have hkly : k * Real.log y = 3 * ε' / 8 := by rw [hkdef]; field_simp
  have hk3 : k ≤ 3 * ε' / 128 * Real.log y := by
    have : k ≤ 3 * ε' / 32 := by
      rw [hkdef, div_le_iff₀ hly0]; nlinarith
    nlinarith
  have hk4 : k * Real.log 2 ≤ k := by nlinarith
  have h38 : 3 * ε' / 8 ≤ 3 * ε' / 32 * Real.log y := by nlinarith
  have key : (1 + k) * (Real.log 2 + Real.log y) ≤ (1 + ε) * Real.log y := by
    have : (1 + k) * (Real.log 2 + Real.log y) = Real.log 2 + Real.log y + k * Real.log 2 + k * Real.log y := by ring
    rw [this, hkly]
    nlinarith
  calc y * (1 + k) * (Real.log 2 + Real.log y) = y * ((1 + k) * (Real.log 2 + Real.log y)) := by ring
    _ ≤ y * ((1 + ε) * Real.log y) := mul_le_mul_of_nonneg_left key hy0.le
    _ = (1 + ε) * y * Real.log y := by ring

/-! ### The crude `ω` is a supersolution of Buchstab's delay equation -/

/-- `log 0.5672 ≥ −0.5672`, from `0.5672·exp(0.5672) ≥ 1` (the exponential's series to degree `5`). -/
theorem log_c_ge : -(5672 / 10000 : ℝ) ≤ Real.log (5672 / 10000) := by
  have hc : (0 : ℝ) ≤ 5672 / 10000 := by norm_num
  have hexp := Real.sum_le_exp_of_nonneg hc 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hexp
  norm_num at hexp
  have h1 : (10000 / 5672 : ℝ) ≤ Real.exp (5672 / 10000) := by linarith
  have h2 : Real.log (10000 / 5672) ≤ 5672 / 10000 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact h1
  have h3 : Real.log (10000 / 5672 : ℝ) = -Real.log (5672 / 10000) := by
    rw [show (10000 / 5672 : ℝ) = (5672 / 10000)⁻¹ by norm_num, Real.log_inv]
  linarith

/-- `1 + log(u − 1) ≤ 0.5672u` for `u > 1`, by the tangent line of `log` at `1/0.5672`. -/
theorem one_add_log_le {u : ℝ} (hu : 1 < u) : 1 + Real.log (u - 1) ≤ 5672 / 10000 * u := by
  have hc : (0 : ℝ) < 5672 / 10000 := by norm_num
  have h1 : Real.log (5672 / 10000 * (u - 1)) ≤ 5672 / 10000 * (u - 1) - 1 :=
    Real.log_le_sub_one_of_pos (by nlinarith)
  rw [Real.log_mul hc.ne' (by linarith)] at h1
  linarith [log_c_ge]

/-- `1 + log 2 ≤ 3·0.5672`. -/
theorem one_add_log_two_le : 1 + Real.log 2 ≤ 3 * (5672 / 10000 : ℝ) := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

/-- **The supersolution property**, in the step's terms: for `u ≥ 2`, `M(u) = ∫_1^{u−1} ω*` is `log(u − 1)` up to
`u = 3` and `log 2 + 0.5672(u − 3)` above, and `1 + M(u) ≤ 0.5672u`. -/
theorem super_M {u c M : ℝ} (hu2 : 2 ≤ u) (hc : c = 5672 / 10000)
    (hM : M = if u ≤ 3 then Real.log (u - 1) else Real.log 2 + c * (u - 3)) : 1 + M ≤ c * u := by
  subst hc hM
  by_cases hu3 : u ≤ 3
  · simp only [hu3, ite_true]
    linarith [one_add_log_le (by linarith : (1 : ℝ) < u)]
  · simp only [hu3, ite_false]
    linarith [one_add_log_two_le]

/-! ### The two ranges of the Buchstab sum -/

theorem omegaC_le_one (u : ℝ) : SieveCert.omegaC u ≤ 1 := by
  unfold SieveCert.omegaC
  split_ifs with h1 h2
  · norm_num
  · rw [div_le_one (by linarith)]; linarith
  · norm_num

theorem omegaC_nonneg (u : ℝ) : 0 ≤ SieveCert.omegaC u := by
  unfold SieveCert.omegaC
  split_ifs with h1 h2
  · exact le_refl _
  · exact div_nonneg zero_le_one (by linarith)
  · norm_num

/-- Where `log p ≤ L/3`, the argument `L/log p − 1` is at least `2`, and `ω* = 0.5672`. -/
theorem omegaC_low {L l : ℝ} (hl : 0 < l) (h3 : 3 * l ≤ L) : SieveCert.omegaC ((L - l) / l) = 5672 / 10000 := by
  have : 2 ≤ (L - l) / l := by rw [le_div_iff₀ hl]; linarith
  have h1 : ¬ (L - l) / l < 1 := by linarith
  have h2 : ¬ (L - l) / l < 2 := by linarith
  simp only [SieveCert.omegaC, h1, h2, ite_false]

/-- Where `L/3 < log p ≤ L/2`, the argument lies in `[1, 2)`, and `ω* = log p/(L − log p)`. -/
theorem omegaC_mid {L l : ℝ} (hl : 0 < l) (h3 : L < 3 * l) (h2 : 2 * l ≤ L) :
    SieveCert.omegaC ((L - l) / l) = l / (L - l) := by
  have hge : 1 ≤ (L - l) / l := by rw [le_div_iff₀ hl]; linarith
  have hlt : (L - l) / l < 2 := by rw [div_lt_iff₀ hl]; linarith
  have h1 : ¬ (L - l) / l < 1 := by linarith
  simp only [SieveCert.omegaC, h1, hlt, ite_false, ite_true, one_div_div]

/-- **Range A**: the primes `z < p ≤ b` with `3 log b = L` carry `ω* = 0.5672`. -/
theorem rangeA_le {z b L ε : ℝ} (hz : Real.exp 1 ≤ z) (hzb : z ≤ b) (hL : 3 * Real.log b = L) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Set.Icc z b, |θ t - t| ≤ ε * t / Real.log t) :
    ∑ p ∈ (Ioc ⌊z⌋₊ ⌊b⌋₊).filter Nat.Prime,
        SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) ≤
      5672 / 10000 * (1 / Real.log z - 3 / L + 4 * ε / Real.log z ^ 2) := by
  have hz0 : 0 ≤ z := le_trans (Real.exp_pos 1).le hz
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) (hz.trans hzb)
  have hterm : ∀ p ∈ (Ioc ⌊z⌋₊ ⌊b⌋₊).filter Nat.Prime,
      SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) =
        5672 / 10000 * (1 / ((p : ℝ) * Real.log p)) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
    rw [Finset.mem_Ioc, Nat.le_floor_iff hb0.le] at hpI
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    have hlb : Real.log p ≤ Real.log b := Real.log_le_log (by linarith) hpI.2
    rw [omegaC_low hl (by linarith)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hS := sum_inv_mul_log_le hz hzb hε hθ
  have hLb : 1 / Real.log b = 3 / L := by rw [← hL]; field_simp
  rw [hLb] at hS
  exact mul_le_mul_of_nonneg_left hS (by norm_num)

/-- **Range B**: the primes `a < p ≤ b` with `L/3 ≤ log a` and `2 log b = L` carry `ω* = log p/(L − log p)`. -/
theorem rangeB_le {a b L ε : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) (hL : 2 * Real.log b = L)
    (ha3 : L ≤ 3 * Real.log a) (hε : 0 ≤ ε) (hθ : ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε * t / Real.log t) :
    ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
        SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) ≤
      Real.log ((L - Real.log a) / Real.log a) / L * (1 + ε / Real.log a) + 6 * ε / (L * Real.log a ^ 2) := by
  have ha0 : 0 ≤ a := le_trans (Real.exp_pos 1).le ha
  have hb0 : 0 < b := lt_of_lt_of_le (Real.exp_pos 1) (ha.trans hab)
  have hla1 : 1 ≤ Real.log a := by rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]; exact ha
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith [Real.exp_pos 1]) hab
  have hL0 : 0 < L := by linarith
  have hterm : ∀ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
      SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) =
        1 / ((p : ℝ) * (L - Real.log p)) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
    rw [Finset.mem_Ioc, Nat.floor_lt ha0, Nat.le_floor_iff hb0.le] at hpI
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    have hla : Real.log a < Real.log p := Real.log_lt_log (by linarith [Real.exp_pos 1]) hpI.1
    have hlpb : Real.log p ≤ Real.log b := Real.log_le_log (by linarith) hpI.2
    have hLp : 0 < L - Real.log p := by linarith
    rw [omegaC_mid hl (by linarith) (by linarith)]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hS := sum_inv_mul_sub_log_le (L := L) ha hab (by linarith) hε hθ
  have hGb : (Real.log (Real.log b) - Real.log (L - Real.log b)) / L = 0 := by
    have : L - Real.log b = Real.log b := by linarith
    rw [this, sub_self, zero_div]
  have hGa : 0 - (Real.log (Real.log a) - Real.log (L - Real.log a)) / L =
      Real.log ((L - Real.log a) / Real.log a) / L := by
    rw [Real.log_div (by linarith) (by linarith)]; ring
  rw [hGb, hGa] at hS
  exact hS

/-! ### The induction on `u` -/

/-- The bound at level `K`: `Ψ(y, z) ≤ (ω*(log 2y/log z) + ε)y/log z` whenever `y ≥ 1` and `log 2y ≤ K log z`, for
every `ε > 0` and all large `z`. -/
def Claim (K : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ y : ℝ, 1 ≤ y →
  Real.log (2 * y) ≤ K * Real.log z →
    (Psi y z : ℝ) ≤ (SieveCert.omegaC (Real.log (2 * y) / Real.log z) + ε) * y / Real.log z

/-- It suffices to prove the bound for `ε ≤ 1`. -/
theorem claim_of_small {K : ℝ} (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ y : ℝ, 1 ≤ y →
    Real.log (2 * y) ≤ K * Real.log z →
      (Psi y z : ℝ) ≤ (SieveCert.omegaC (Real.log (2 * y) / Real.log z) + ε) * y / Real.log z) : Claim K := by
  intro ε hε
  obtain ⟨z₀, hz₀⟩ := h (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨max z₀ 3, fun z hz y hy hlog => ?_⟩
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast le_trans (le_max_right _ _) hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  refine (hz₀ z (le_trans (le_max_left _ _) hz) y hy hlog).trans ?_
  apply div_le_div_of_nonneg_right _ hlz.le
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  linarith [min_le_left ε 1]

theorem omegaC_of_ge_two {u : ℝ} (hu : 2 ≤ u) : SieveCert.omegaC u = 5672 / 10000 := by
  have h1 : ¬ u < 1 := by linarith
  have h2 : ¬ u < 2 := by linarith
  simp only [SieveCert.omegaC, h1, h2, ite_false]

theorem omegaC_of_lt_two {u : ℝ} (hu1 : 1 ≤ u) (hu : u < 2) : SieveCert.omegaC u = 1 / u := by
  have h1 : ¬ u < 1 := by linarith
  simp only [SieveCert.omegaC, h1, hu, ite_false, ite_true]

/-- For `F ≥ 0`, the sum over the primes of `[z, n]` is at most the term at `z` plus the sum over `(z, n]`. -/
theorem sum_Icc_filter_le {z n : ℕ} {F : ℕ → ℝ} (hF : ∀ p, 0 ≤ F p) (hzn : z ≤ n) :
    ∑ p ∈ (Icc z n).filter Nat.Prime, F p ≤ F z + ∑ p ∈ (Ioc z n).filter Nat.Prime, F p := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_Ioc_add_eq_sum_Icc hzn]
  have : (if z.Prime then F z else 0) ≤ F z := by split_ifs <;> simp [hF]
  linarith

/-- Splitting the primes of `(z, n]` at `m`. -/
theorem sum_Ioc_filter_split {z m n : ℕ} (F : ℕ → ℝ) (hzm : z ≤ m) (hmn : m ≤ n) :
    ∑ p ∈ (Ioc z n).filter Nat.Prime, F p =
      ∑ p ∈ (Ioc z m).filter Nat.Prime, F p + ∑ p ∈ (Ioc m n).filter Nat.Prime, F p := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_Ioc_consecutive _ hzm hmn]


/-- The sum of `ω*((L − log p)/log p)/(p log p)` over the primes of `(z, b₂]`, with `2 log b₂ = L = u log z` and
`2 ≤ u ≤ 3` (range B only). -/
theorem sumW_le_three {z : ℕ} {b2 L u ε₃ : ℝ} (hez : Real.exp 1 ≤ z) (hzb2 : (z : ℝ) ≤ b2)
    (hlb2 : 2 * Real.log b2 = L) (hLu : L = u * Real.log z) (hu2 : 2 ≤ u) (hu3 : u ≤ 3) (hε₃0 : 0 < ε₃)
    (hθ : ∀ t ∈ Set.Icc (z : ℝ) b2, |θ t - t| ≤ ε₃ * t / Real.log t) :
    ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
        SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) ≤
      1 / L * Real.log (u - 1) + 12 * ε₃ / L + 4 * ε₃ / Real.log z := by
  have hlz : 1 ≤ Real.log z := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hez)]; exact hez
  have hlz0 : 0 < Real.log z := by linarith
  have hL0 : 0 < L := by rw [hLu]; positivity
  have h := rangeB_le hez hzb2 hlb2 (by rw [hLu]; exact mul_le_mul_of_nonneg_right hu3 hlz0.le) hε₃0.le hθ
  rw [Nat.floor_natCast] at h
  have hq : (L - Real.log z) / Real.log z = u - 1 := by rw [hLu]; field_simp
  rw [hq] at h
  have hlu : Real.log (u - 1) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < u - 1); linarith
  have hlu0 : 0 ≤ Real.log (u - 1) := Real.log_nonneg (by linarith)
  have e1 : Real.log (u - 1) / L * (1 + ε₃ / Real.log z) ≤ 1 / L * Real.log (u - 1) + ε₃ / L := by
    have : Real.log (u - 1) / L * (ε₃ / Real.log z) ≤ ε₃ / L := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hL0]
      have hmul := mul_le_mul_of_nonneg_left (hlu.trans hlz) (mul_nonneg hε₃0.le hL0.le)
      calc Real.log (u - 1) * ε₃ * L = ε₃ * L * Real.log (u - 1) := by ring
        _ ≤ ε₃ * L * Real.log z := hmul
        _ = ε₃ * (L * Real.log z) := by ring
    have e : Real.log (u - 1) / L * (1 + ε₃ / Real.log z) =
        1 / L * Real.log (u - 1) + Real.log (u - 1) / L * (ε₃ / Real.log z) := by ring
    linarith
  have e2 : 6 * ε₃ / (L * Real.log z ^ 2) ≤ 6 * ε₃ / L := by
    apply div_le_div_of_nonneg_left (by positivity) hL0
    exact le_mul_of_one_le_right hL0.le (one_le_pow₀ hlz)
  have e3 : 0 ≤ 4 * ε₃ / Real.log z := by positivity
  have e4 : ε₃ / L ≤ 6 * ε₃ / L := div_le_div_of_nonneg_right (by linarith : ε₃ ≤ 6 * ε₃) hL0.le
  have e5 : 12 * ε₃ / L = 6 * ε₃ / L + 6 * ε₃ / L := by ring
  linarith

/-- The sum of `ω*((L − log p)/log p)/(p log p)` over the primes of `(z, b₂]`, with
`2 log b₂ = 3 log b₃ = L = u log z` and `u > 3` (ranges A and B, split at `b₃`). -/
theorem sumW_gt_three {z : ℕ} {b2 b3 L u ε₃ c : ℝ} (hez : Real.exp 1 ≤ z)
    (hlb2 : 2 * Real.log b2 = L) (hlb3 : 3 * Real.log b3 = L) (hb20 : 0 < b2) (hb30 : 0 < b3)
    (hLu : L = u * Real.log z)
    (hu3 : 3 < u) (hc : c = 5672 / 10000) (hε₃0 : 0 < ε₃)
    (hθ : ∀ t ∈ Set.Icc (z : ℝ) b2, |θ t - t| ≤ ε₃ * t / Real.log t) :
    ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
        SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) ≤
      1 / L * (Real.log 2 + c * (u - 3)) + 12 * ε₃ / L + 4 * ε₃ / Real.log z := by
  subst hc
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le (Real.exp_pos 1) hez
  have hlz : 1 ≤ Real.log z := by rw [Real.le_log_iff_exp_le hz0]; exact hez
  have hlz0 : 0 < Real.log z := by linarith
  have hL0 : 0 < L := by rw [hLu]; nlinarith
  have hzb3 : (z : ℝ) ≤ b3 := by
    have : 3 * Real.log z ≤ 3 * Real.log b3 := by
      rw [hlb3]
      calc 3 * Real.log z ≤ u * Real.log z := mul_le_mul_of_nonneg_right hu3.le hlz0.le
        _ = L := hLu.symm
    exact (Real.log_le_log_iff hz0 hb30).1 (by linarith)
  have hb3b2 : b3 ≤ b2 := by
    have : Real.log b3 ≤ Real.log b2 := by linarith
    exact (Real.log_le_log_iff hb30 hb20).1 this
  have hzm : z ≤ ⌊b3⌋₊ := Nat.le_floor hzb3
  have hmn : ⌊b3⌋₊ ≤ ⌊b2⌋₊ := Nat.floor_le_floor hb3b2
  rw [sum_Ioc_filter_split _ hzm hmn]
  have hθ3 : ∀ t ∈ Set.Icc (z : ℝ) b3, |θ t - t| ≤ ε₃ * t / Real.log t :=
    fun t ht => hθ t ⟨ht.1, ht.2.trans hb3b2⟩
  have hθ32 : ∀ t ∈ Set.Icc b3 b2, |θ t - t| ≤ ε₃ * t / Real.log t :=
    fun t ht => hθ t ⟨hzb3.trans ht.1, ht.2⟩
  have hA := rangeA_le hez hzb3 hlb3 hε₃0.le hθ3
  rw [Nat.floor_natCast] at hA
  have heb3 : Real.exp 1 ≤ b3 := hez.trans hzb3
  have hB := rangeB_le heb3 hb3b2 hlb2 (by linarith) hε₃0.le hθ32
  have hq : (L - Real.log b3) / Real.log b3 = 2 := by
    have : Real.log b3 = L / 3 := by linarith
    rw [this]; field_simp; ring
  rw [hq] at hB
  have hlb3z : Real.log z ≤ Real.log b3 := Real.log_le_log hz0 hzb3
  have hlb3_1 : 1 ≤ Real.log b3 := le_trans hlz hlb3z
  have eA : 5672 / 10000 * (1 / Real.log z - 3 / L + 4 * ε₃ / Real.log z ^ 2) ≤
      1 / L * (5672 / 10000 * (u - 3)) + 4 * ε₃ / Real.log z := by
    have h1 : 1 / Real.log z = u / L := by rw [hLu]; field_simp
    have h2 : 4 * ε₃ / Real.log z ^ 2 ≤ 4 * ε₃ / Real.log z := by
      apply div_le_div_of_nonneg_left (by positivity) hlz0
      exact le_self_pow₀ hlz (by norm_num)
    have h3 : 5672 / 10000 * (u / L - 3 / L) = 1 / L * (5672 / 10000 * (u - 3)) := by ring
    have hc0 : (5672 / 10000 : ℝ) ≤ 1 := by norm_num
    have hc00 : (0 : ℝ) ≤ 5672 / 10000 := by norm_num
    have h4 : 5672 / 10000 * (4 * ε₃ / Real.log z ^ 2) ≤ 4 * ε₃ / Real.log z :=
      le_trans (mul_le_of_le_one_left (by positivity) hc0) h2
    have e : 5672 / 10000 * (1 / Real.log z - 3 / L + 4 * ε₃ / Real.log z ^ 2) =
        5672 / 10000 * (1 / Real.log z - 3 / L) + 5672 / 10000 * (4 * ε₃ / Real.log z ^ 2) := by ring
    rw [e, h1, h3]
    linarith
  have eB : Real.log 2 / L * (1 + ε₃ / Real.log b3) + 6 * ε₃ / (L * Real.log b3 ^ 2) ≤
      1 / L * Real.log 2 + 7 * ε₃ / L := by
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
    have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have k1 : Real.log 2 / L * (ε₃ / Real.log b3) ≤ ε₃ / L := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hL0]
      have hmul := mul_le_mul_of_nonneg_left (hl2.trans hlb3_1) (mul_nonneg hε₃0.le hL0.le)
      calc Real.log 2 * ε₃ * L = ε₃ * L * Real.log 2 := by ring
        _ ≤ ε₃ * L * Real.log b3 := hmul
        _ = ε₃ * (L * Real.log b3) := by ring
    have k2 : 6 * ε₃ / (L * Real.log b3 ^ 2) ≤ 6 * ε₃ / L := by
      apply div_le_div_of_nonneg_left (by positivity) hL0
      exact le_mul_of_one_le_right hL0.le (one_le_pow₀ hlb3_1)
    have e : Real.log 2 / L * (1 + ε₃ / Real.log b3) =
        1 / L * Real.log 2 + Real.log 2 / L * (ε₃ / Real.log b3) := by ring
    have e7 : 7 * ε₃ / L = ε₃ / L + 6 * ε₃ / L := by ring
    linarith
  have h7 : 7 * ε₃ / L ≤ 12 * ε₃ / L := by
    rw [div_le_div_iff_of_pos_right hL0]; linarith
  have e : 1 / L * (Real.log 2 + 5672 / 10000 * (u - 3)) =
      1 / L * (5672 / 10000 * (u - 3)) + 1 / L * Real.log 2 := by ring
  linarith [hA.trans eA, hB.trans eB]

/-- The bracket of the induction step, in units of `y/log z`. -/
theorem bracket_le {u z lz ε ε₃ c M : ℝ} (hu1 : 1 ≤ u) (hlz : 1 ≤ lz) (hz2 : 2 / z ≤ ε / 4) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hε₃ : ε₃ = ε / 100) (hsuper : 1 + M ≤ c * u) :
    (1 + ε / 4) / u + 2 / z + (M + 12 * ε₃) / u + 4 * ε₃ + (ε / 4 + ε * ε₃ / lz) ≤ c + ε := by
  subst hε₃
  have hu0 : 0 < u := by linarith
  have k1 : (1 + ε / 4) / u + (M + 12 * (ε / 100)) / u = (1 + M) / u + (ε / 4 + 12 * (ε / 100)) / u := by ring
  have k2 : (1 + M) / u ≤ c := by rw [div_le_iff₀ hu0]; linarith
  have k3 : (ε / 4 + 12 * (ε / 100)) / u ≤ ε / 4 + 12 * (ε / 100) := div_le_self (by positivity) hu1
  have k5 : ε * (ε / 100) / lz ≤ ε / 100 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : ε * (ε / 100) ≤ 1 * (ε / 100) := mul_le_mul_of_nonneg_right hε1 (by positivity)
    have h2 : 1 * (ε / 100) ≤ ε / 100 * lz := by nlinarith
    linarith
  linarith

/-- The induction step's bound, in units of `Q = y/log z`. -/
theorem units_eq {y lz L u Q z ε ε₃ M : ℝ} (hlz0 : 0 < lz) (hLu : L = u * lz) (hu0 : 0 < u) (hQ : Q = y / lz)
    (hz0 : 0 < z) :
    (1 + ε / 4) * (Q / u) + y * (2 / (z * lz) + (1 / L * M + 12 * ε₃ / L + 4 * ε₃ / lz) +
      ε / 4 * (1 / lz + 4 * ε₃ / lz ^ 2)) =
      Q * ((1 + ε / 4) / u + 2 / z + (M + 12 * ε₃) / u + 4 * ε₃ + (ε / 4 + ε * ε₃ / lz)) := by
  subst hLu hQ
  field_simp
  ring


set_option maxHeartbeats 1000000 in
/-- **The induction step**: the bound at level `K` gives it at level `K + 1`. -/
theorem claim_step {K : ℝ} (hK : 0 ≤ K) (IH : Claim K) : Claim (K + 1) := by
  apply claim_of_small
  intro ε hε hε1
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 5672 / 10000 := ⟨_, rfl⟩
  obtain ⟨ε₃, hε₃⟩ : ∃ ε₃ : ℝ, ε₃ = ε / 100 := ⟨_, rfl⟩
  have hε₃0 : 0 < ε₃ := by rw [hε₃]; positivity
  obtain ⟨y₀, hy₀⟩ := card_primes_dyadic (ε := ε / 4) (by positivity)
  obtain ⟨z₁, hz₁⟩ := IH (ε / 4) (by positivity)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (theta_near (ε := ε₃) hε₃0)
  refine ⟨max (max z₁ (⌈2 * y₀⌉₊ + 4)) (max (⌈T⌉₊ + 4) (⌈8 / ε⌉₊ + 4)), ?_⟩
  intro z hz y hy hlog
  -- facts about `z`
  have hzz₁ : z₁ ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hzA : ⌈2 * y₀⌉₊ + 4 ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hzB : ⌈T⌉₊ + 4 ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hz
  have hzC : ⌈8 / ε⌉₊ + 4 ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hz
  have hz2y₀ : 2 * y₀ ≤ z := by
    have : ((⌈2 * y₀⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzA
    push_cast at this
    linarith [Nat.le_ceil (2 * y₀)]
  have hzT : T ≤ z := by
    have : ((⌈T⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzB
    push_cast at this
    linarith [Nat.le_ceil T]
  have hz8 : 8 / ε ≤ z := by
    have : ((⌈8 / ε⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzC
    push_cast at this
    linarith [Nat.le_ceil (8 / ε)]
  have hz4 : (4 : ℝ) ≤ z := by
    have : ((⌈T⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzB
    push_cast at this
    linarith [Nat.cast_nonneg (α := ℝ) ⌈T⌉₊]
  have hez : Real.exp 1 ≤ z := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hlz : 1 ≤ Real.log z := by rw [Real.le_log_iff_exp_le (by linarith)]; exact hez
  have hlz0 : 0 < Real.log z := by linarith
  have hθ : ∀ a b : ℝ, (z : ℝ) ≤ a → ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε₃ * t / Real.log t :=
    fun a b hza t ht => hT t (by linarith [ht.1])
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (2 * y) := ⟨_, rfl⟩
  rw [← hLdef] at hlog
  rw [← hLdef]
  -- below `u = 1`
  by_cases hsmall : 2 * y < z
  · rw [Psi_eq_zero hy hsmall, Nat.cast_zero]
    have := SieveRough.omegaC_nonneg (L / Real.log z)
    positivity
  have hz2y : (z : ℝ) ≤ 2 * y := not_lt.1 hsmall
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hyy₀ : y₀ ≤ y := by linarith
  have hLz : Real.log z ≤ L := by rw [hLdef]; exact Real.log_le_log (by linarith) hz2y
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = L / Real.log z := ⟨_, rfl⟩
  rw [← hu]
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hlz0]; linarith
  have hLu : L = u * Real.log z := by rw [hu]; field_simp
  have hL0 : 0 < L := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = y / Real.log z := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hyL : y / L = Q / u := by rw [hLu, hQ]; field_simp
  -- Buchstab and the primes
  have hbuch := Psi_le_buchstab (z := z) hy2
  have hN := hy₀ y hyy₀
  -- the induction hypothesis at each prime
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ, F = fun p : ℕ => SieveCert.omegaC ((L - Real.log p) / Real.log p) /
      ((p : ℝ) * Real.log p) + ε / 4 / ((p : ℝ) * Real.log p) := ⟨_, rfl⟩
  have hIH : ∀ p ∈ (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime, (Psi (y / p) p : ℝ) ≤ y * F p := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
    obtain ⟨hzp, hpn⟩ := Finset.mem_Icc.1 hpI
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpz : (z : ℝ) ≤ p := by exact_mod_cast hzp
    have hpsq : (p : ℝ) ≤ √(2 * y) := le_trans (by exact_mod_cast hpn) (Nat.floor_le (Real.sqrt_nonneg _))
    have hpp2 : (p : ℝ) * p ≤ 2 * y := by
      calc (p : ℝ) * p ≤ √(2 * y) * √(2 * y) := mul_le_mul hpsq hpsq hp0.le (Real.sqrt_nonneg _)
        _ = 2 * y := Real.mul_self_sqrt (by linarith)
    have hyp1 : 1 ≤ y / p := by rw [le_div_iff₀ hp0]; nlinarith
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlzp : Real.log z ≤ Real.log p := Real.log_le_log (by linarith) hpz
    have hl2yp : Real.log (2 * (y / p)) = L - Real.log p := by
      rw [show 2 * (y / p) = 2 * y / p by ring, Real.log_div (by positivity) hp0.ne', hLdef]
    have hlogp : Real.log (2 * (y / p)) ≤ K * Real.log p := by
      rw [hl2yp]
      have : L ≤ (K + 1) * Real.log p := le_trans hlog (mul_le_mul_of_nonneg_left hlzp (by linarith))
      linarith
    have h := hz₁ p (le_trans hzz₁ hzp) (y / p) hyp1 hlogp
    rw [hl2yp] at h
    refine h.trans (le_of_eq ?_)
    simp only [hFdef]
    field_simp
  have hF0 : ∀ p, 0 ≤ F p := by
    intro p
    simp only [hFdef]
    have := SieveRough.omegaC_nonneg ((L - Real.log p) / Real.log p)
    rcases Nat.lt_or_ge p 2 with hp | hp
    · interval_cases p <;> simp
    · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
      have : 0 < Real.log p := Real.log_pos hp1
      positivity
  have hsumP : ∑ p ∈ (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime, (Psi (y / p) p : ℝ) ≤
      y * ∑ p ∈ (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime, F p := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hIH
  by_cases hu2 : u < 2
  · -- `1 ≤ u < 2`: no prime of the sum
    have hn : ⌊√(2 * y)⌋₊ < z := by
      have h2y : 2 * y < (z : ℝ) * z := by
        have : L < 2 * Real.log z := by rw [hLu]; nlinarith
        have : Real.log (2 * y) < Real.log ((z : ℝ) * z) := by
          have hzz : Real.log ((z : ℝ) * z) = 2 * Real.log z := by
            rw [Real.log_mul (by positivity) (by positivity)]; ring
          rw [hzz, ← hLdef]; exact this
        exact (Real.log_lt_log_iff (by linarith) (by positivity)).1 this
      have : √(2 * y) < z := by
        rw [Real.sqrt_lt' (by linarith)]; nlinarith
      exact (Nat.floor_lt (Real.sqrt_nonneg _)).2 this
    have hempty : (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime = ∅ := by
      rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty]
    rw [hempty, Finset.sum_empty, add_zero] at hbuch
    rw [omegaC_of_lt_two hu1 hu2]
    have h1 : (Psi y z : ℝ) ≤ (1 + ε / 4) * (Q / u) := by
      calc (Psi y z : ℝ) ≤ _ := hbuch
        _ ≤ (1 + ε / 4) * y / L := by rw [hLdef]; exact hN
        _ = (1 + ε / 4) * (y / L) := by ring
        _ = (1 + ε / 4) * (Q / u) := by rw [hyL]
    have h2 : (1 + ε / 4) * (Q / u) ≤ (1 / u + ε) * Q := by
      have hu0 : 0 < u := by linarith
      have : ε / 4 / u ≤ ε := by rw [div_le_iff₀ hu0]; nlinarith
      have e : (1 + ε / 4) * (Q / u) = (1 / u + ε / 4 / u) * Q := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) hQ0.le
    calc (Psi y z : ℝ) ≤ (1 / u + ε) * Q := h1.trans h2
      _ = (1 / u + ε) * y / Real.log z := by rw [hQ]; ring
  · -- `u ≥ 2`
    have hu2' : 2 ≤ u := not_lt.1 hu2
    rw [omegaC_of_ge_two hu2', ← hc]
    obtain ⟨b2, hb2⟩ : ∃ b2 : ℝ, b2 = √(2 * y) := ⟨_, rfl⟩
    have hlb2 : 2 * Real.log b2 = L := by rw [hb2, Real.log_sqrt (by linarith), hLdef]; ring
    have hzb2 : (z : ℝ) ≤ b2 := by
      have : 2 * Real.log z ≤ 2 * Real.log b2 := by
        rw [hlb2]
        calc 2 * Real.log z ≤ u * Real.log z := mul_le_mul_of_nonneg_right hu2' hlz0.le
          _ = L := hLu.symm
      have hb20 : 0 < b2 := by rw [hb2]; positivity
      exact (Real.log_le_log_iff (by linarith) hb20).1 (by linarith)
    have hzn : z ≤ ⌊b2⌋₊ := Nat.le_floor hzb2
    have hfloorz : ⌊(z : ℝ)⌋₊ = z := Nat.floor_natCast z
    -- the term at `z`
    have hFz : F z ≤ 2 / ((z : ℝ) * Real.log z) := by
      simp only [hFdef]
      have := omegaC_le_one ((L - Real.log z) / Real.log z)
      have hd : 0 < (z : ℝ) * Real.log z := by positivity
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hd.le
    -- the `ε/4` part
    have hE : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p) ≤
        ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2) := by
      have h := sum_inv_mul_log_le hez hzb2 hε₃0.le (hθ z b2 le_rfl)
      rw [hfloorz] at h
      have hb21 : 0 ≤ 1 / Real.log b2 := by
        have : 0 < Real.log b2 := by linarith only [hlb2, hL0]
        positivity
      have e : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p) =
          ε / 4 * ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, 1 / ((p : ℝ) * Real.log p) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith only [h, hb21]) (by positivity)
    -- the sum of `ω*` over `(z, √2y]`
    have hW : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
        SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) ≤
        (1 / L) * (if u ≤ 3 then Real.log (u - 1) else Real.log 2 + c * (u - 3)) + 12 * ε₃ / L +
          4 * ε₃ / Real.log z := by
      by_cases hu3 : u ≤ 3
      · simp only [hu3, ite_true]
        exact sumW_le_three hez hzb2 hlb2 hLu hu2' hu3 hε₃0 (hθ z b2 le_rfl)
      · have hu3' : 3 < u := not_le.1 hu3
        obtain ⟨b3, hb3⟩ : ∃ b3 : ℝ, b3 = (2 * y) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
        have hb30 : 0 < b3 := by rw [hb3]; positivity
        have hlb3 : 3 * Real.log b3 = L := by
          rw [hb3, Real.log_rpow (by linarith), hLdef]; ring
        simp only [hu3, ite_false]
        have hb20 : 0 < b2 := by rw [hb2]; positivity
        exact sumW_gt_three hez hlb2 hlb3 hb20 hb30 hLu hu3' hc hε₃0 (hθ z b2 le_rfl)
    -- the final count
    have hPsum := sum_Icc_filter_le hF0 hzn
    have hIocF : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, F p =
        ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
          SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) +
        ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p) := by
      simp only [hFdef, Finset.sum_add_distrib]
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = if u ≤ 3 then Real.log (u - 1) else Real.log 2 + c * (u - 3) := ⟨_, rfl⟩
    rw [← hM] at hW
    have hsuper : 1 + M ≤ c * u := super_M hu2' hc hM
    -- everything in units of `Q = y/log z`, with `y/L = Q/u`
    have hN' : (1 + ε / 4) * y / Real.log (2 * y) = (1 + ε / 4) * (Q / u) := by
      rw [← hLdef, ← hyL]; ring
    have h1 := hN.trans hN'.le
    have h2 : ∑ p ∈ (Icc z ⌊√(2 * y)⌋₊).filter Nat.Prime, F p ≤ 2 / ((z : ℝ) * Real.log z) +
        ((1 / L) * M + 12 * ε₃ / L + 4 * ε₃ / Real.log z) +
        ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2) := by
      rw [← hb2]
      calc ∑ p ∈ (Icc z ⌊b2⌋₊).filter Nat.Prime, F p
          ≤ F z + ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, F p := hPsum
        _ = F z + (∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
              SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) +
            ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p)) := by rw [hIocF]
        _ ≤ 2 / ((z : ℝ) * Real.log z) + (((1 / L) * M + 12 * ε₃ / L + 4 * ε₃ / Real.log z) +
            ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2)) := add_le_add hFz (add_le_add hW hE)
        _ = _ := by ring
    have hbound : (Psi y z : ℝ) ≤ (1 + ε / 4) * (Q / u) + y * (2 / ((z : ℝ) * Real.log z) +
        ((1 / L) * M + 12 * ε₃ / L + 4 * ε₃ / Real.log z) + ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2)) :=
      hbuch.trans (add_le_add h1 (hsumP.trans (mul_le_mul_of_nonneg_left h2 hy0.le)))
    -- the bracket
    have hu0 : 0 < u := by linarith
    have hz2 : 2 / (z : ℝ) ≤ ε / 4 := by
      rw [div_le_iff₀ (by linarith)]
      have : 8 / ε * ε = 8 := by field_simp
      nlinarith
    calc (Psi y z : ℝ) ≤ _ := hbound
      _ = _ := units_eq hlz0 hLu hu0 hQ (by linarith)
      _ ≤ Q * (c + ε) := mul_le_mul_of_nonneg_left (bracket_le hu1 hlz hz2 hε hε1 hε₃ hsuper) hQ0.le
      _ = (c + ε) * y / Real.log z := by rw [hQ]; ring

/-- The bound at level `0` is vacuous, since `log 2y > 0` for `y ≥ 1`. -/
theorem claim_zero : Claim 0 := by
  intro ε hε
  refine ⟨0, fun z _ y hy hlog => ?_⟩
  have : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  linarith [show (0 : ℝ) * Real.log z = 0 by ring]

/-- The bound at every natural level. -/
theorem claim_nat (k : ℕ) : Claim k := by
  induction k with
  | zero => simpa using claim_zero
  | succ k ih =>
    have h := claim_step (Nat.cast_nonneg k) ih
    simpa using h

/-- **Rough numbers from above.** For every `U` and `ε > 0` there is `z₀` such that for `z ≥ z₀`, `y ≥ 1` and
`log 2y ≤ U log z`: `Ψ(y, z) ≤ (ω*(log 2y/log z) + ε)y/log z`, with the crude `ω*` of `SieveCert.omegaC`. -/
theorem psi_le (U : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ y : ℝ, 1 ≤ y →
    Real.log (2 * y) ≤ U * Real.log z →
      (Psi y z : ℝ) ≤ (SieveCert.omegaC (Real.log (2 * y) / Real.log z) + ε) * y / Real.log z := by
  obtain ⟨z₀, hz₀⟩ := claim_nat ⌈U⌉₊ ε hε
  refine ⟨max z₀ 2, fun z hz y hy hlog => hz₀ z (le_trans (le_max_left _ _) hz) y hy (hlog.trans ?_)⟩
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans (le_max_right _ _) hz
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil U) hlz

section Shares

open SieveCert

/-! ### The primes of `[x^a, x^c)` -/

/-- The primes `p` with `A ≤ p < B`. -/
noncomputable def primesIn (A B : ℝ) : Finset ℕ := (Ico ⌈A⌉₊ ⌈B⌉₊).filter Nat.Prime

theorem mem_primesIn {A B : ℝ} {p : ℕ} : p ∈ primesIn A B ↔ p.Prime ∧ A ≤ p ∧ (p : ℝ) < B := by
  rw [primesIn, Finset.mem_filter, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]
  tauto

/-- For `f ≥ 0`, a sum over `primesIn A B` is at most its term at `⌈A⌉₊` plus the sum over the primes of
`(⌊A⌋₊, ⌊B⌋₊]`. -/
theorem sum_primesIn_le {A B : ℝ} {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    ∑ p ∈ primesIn A B, f p ≤ f ⌈A⌉₊ + ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, f p := by
  set s := (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime with hs
  have hsub : primesIn A B ⊆ insert ⌈A⌉₊ s := by
    intro p hp
    rw [mem_primesIn] at hp
    obtain ⟨hpp, hAp, hpB⟩ := hp
    rw [Finset.mem_insert]
    by_cases h : p = ⌈A⌉₊
    · exact Or.inl h
    · refine Or.inr ?_
      rw [hs, Finset.mem_filter, Finset.mem_Ioc]
      have h1 : ⌈A⌉₊ < p := lt_of_le_of_ne (Nat.ceil_le.2 hAp) (Ne.symm h)
      exact ⟨⟨lt_of_le_of_lt (Nat.floor_le_ceil A) h1, Nat.le_floor hpB.le⟩, hpp⟩
  calc ∑ p ∈ primesIn A B, f p ≤ ∑ p ∈ insert ⌈A⌉₊ s, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf p)
    _ ≤ f ⌈A⌉₊ + ∑ p ∈ s, f p := by
        by_cases hm : ⌈A⌉₊ ∈ s
        · rw [Finset.insert_eq_of_mem hm]; linarith [hf ⌈A⌉₊]
        · rw [Finset.sum_insert hm]

/-- `S` is eventually at most `P + δ`, for every `δ > 0`: `limsup S ≤ P`. -/
def EvLe (S : ℝ → ℝ) (P : ℝ) : Prop := ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop, S x ≤ P + δ

theorem EvLe.mul {S T : ℝ → ℝ} {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hS0 : ∀ᶠ x : ℝ in atTop, 0 ≤ S x)
    (hT0 : ∀ᶠ x : ℝ in atTop, 0 ≤ T x) (hS : EvLe S P) (hT : EvLe T Q) :
    EvLe (fun x => S x * T x) (P * Q) := by
  intro δ hδ
  obtain ⟨d, hd⟩ : ∃ d, d = min 1 (δ / (P + Q + 1)) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact lt_min one_pos (by positivity)
  have hd1 : d ≤ 1 := by rw [hd]; exact min_le_left _ _
  have hd2 : d * (P + Q + 1) ≤ δ := by
    have h := min_le_right 1 (δ / (P + Q + 1))
    rw [← hd] at h
    calc d * (P + Q + 1) ≤ δ / (P + Q + 1) * (P + Q + 1) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = δ := div_mul_cancel₀ _ (by positivity)
  filter_upwards [hS0, hT0, hS d hd0, hT d hd0] with x h1 h2 h3 h4
  calc S x * T x ≤ (P + d) * (Q + d) := mul_le_mul h3 h4 h2 (by linarith)
    _ = P * Q + d * (P + Q + d) := by ring
    _ ≤ P * Q + δ := by nlinarith [mul_nonneg hd0.le (sub_nonneg.2 hd1)]

/-- `Σ_{x^a ≤ p < x^c} 1/p ≤ log c − log a + o(1)`. -/
theorem evLe_sum_inv {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    EvLe (fun x => ∑ p ∈ primesIn (x ^ a) (x ^ c), 1 / (p : ℝ)) (Real.log c - Real.log a) := by
  intro δ hδ
  have hP : 0 ≤ Real.log c - Real.log a := sub_nonneg.2 (Real.log_le_log ha hac)
  obtain ⟨P, hPdef⟩ : ∃ P, P = Real.log c - Real.log a := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  obtain ⟨εθ, hεθ⟩ : ∃ εθ, εθ = δ / (2 * (P + 3)) := ⟨_, rfl⟩
  have hεθ0 : 0 < εθ := by rw [hεθ]; positivity
  have hεθP : εθ * (P + 3) = δ / 2 := by rw [hεθ]; field_simp
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (theta_near hεθ0)
  have hx : ∀ᶠ x : ℝ in atTop, max (max T (Real.exp 1)) (2 / δ) ≤ x ^ a :=
    (tendsto_rpow_atTop ha).eventually_ge_atTop _
  filter_upwards [hx, eventually_ge_atTop 1] with x hxa hx1
  have hA : T ≤ x ^ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxa
  have hAe : Real.exp 1 ≤ x ^ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxa
  have hAδ : 2 / δ ≤ x ^ a := le_trans (le_max_right _ _) hxa
  have hAB : x ^ a ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx1 hac
  have hA0 : 0 < x ^ a := lt_of_lt_of_le (Real.exp_pos 1) hAe
  have hx0 : 0 < x := by linarith
  have hθ : ∀ t ∈ Set.Icc (x ^ a) (x ^ c), |θ t - t| ≤ εθ * t / Real.log t :=
    fun t ht => hT t (le_trans hA ht.1)
  have h1 := sum_inv_le hAe hAB hεθ0.le hθ
  have h2 := sum_primesIn_le (A := x ^ a) (B := x ^ c) (f := fun p : ℕ => 1 / (p : ℝ)) (fun p => by positivity)
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
  have h3 : P * (1 + εθ / Real.log (x ^ a)) ≤ P * (1 + εθ) :=
    mul_le_mul_of_nonneg_left (by linarith [div_le_self hεθ0.le hla]) hP
  have h4 : 3 * εθ / Real.log (x ^ a) ^ 2 ≤ 3 * εθ :=
    div_le_self (by positivity) (one_le_pow₀ hla)
  have h5 : 1 / (⌈x ^ a⌉₊ : ℝ) ≤ δ / 2 := by
    calc 1 / (⌈x ^ a⌉₊ : ℝ) ≤ 1 / x ^ a := one_div_le_one_div_of_le hA0 (Nat.le_ceil _)
      _ ≤ 1 / (2 / δ) := one_div_le_one_div_of_le (by positivity) hAδ
      _ = δ / 2 := by rw [one_div_div]
  have h6 := h2.trans (add_le_add h5 h1)
  nlinarith

/-- `log x · Σ_{x^a ≤ p < x^c} 1/(p log p) ≤ 1/a − 1/c + o(1)`. -/
theorem evLe_sum_inv_log {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    EvLe (fun x => Real.log x * ∑ p ∈ primesIn (x ^ a) (x ^ c), 1 / ((p : ℝ) * Real.log p)) (1 / a - 1 / c) := by
  intro δ hδ
  obtain ⟨εθ, hεθ⟩ : ∃ εθ, εθ = δ * a ^ 2 / 8 := ⟨_, rfl⟩
  have hεθ0 : 0 < εθ := by rw [hεθ]; positivity
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (theta_near hεθ0)
  have hx : ∀ᶠ x : ℝ in atTop, max (max T (Real.exp 1)) (2 / (a * δ)) ≤ x ^ a :=
    (tendsto_rpow_atTop ha).eventually_ge_atTop _
  filter_upwards [hx, eventually_ge_atTop (Real.exp 1)] with x hxa hxe
  have hA : T ≤ x ^ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxa
  have hAe : Real.exp 1 ≤ x ^ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxa
  have hAδ : 2 / (a * δ) ≤ x ^ a := le_trans (le_max_right _ _) hxa
  have hx1 : 1 ≤ x := le_trans (by linarith [Real.add_one_le_exp 1]) hxe
  have hAB : x ^ a ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx1 hac
  have hA0 : 0 < x ^ a := lt_of_lt_of_le (Real.exp_pos 1) hAe
  have hx0 : 0 < x := by linarith
  have hlx1 : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hlx : 0 < Real.log x := by linarith
  have hθ : ∀ t ∈ Set.Icc (x ^ a) (x ^ c), |θ t - t| ≤ εθ * t / Real.log t :=
    fun t ht => hT t (le_trans hA ht.1)
  have h1 := sum_inv_mul_log_le hAe hAB hεθ0.le hθ
  have h2 := sum_primesIn_le (A := x ^ a) (B := x ^ c) (f := fun p : ℕ => 1 / ((p : ℝ) * Real.log p))
    (fun p => one_div_nonneg.2 (mul_nonneg (Nat.cast_nonneg p) (Real.log_natCast_nonneg p)))
  have hla : 1 ≤ Real.log (x ^ a) := by rw [Real.le_log_iff_exp_le hA0]; exact hAe
  have hlxa : Real.log (x ^ a) = a * Real.log x := Real.log_rpow hx0 a
  have hlxc : Real.log (x ^ c) = c * Real.log x := Real.log_rpow hx0 c
  -- the extra term
  have hce : x ^ a ≤ (⌈x ^ a⌉₊ : ℝ) := Nat.le_ceil _
  have hlce : Real.log (x ^ a) ≤ Real.log (⌈x ^ a⌉₊ : ℝ) := Real.log_le_log hA0 hce
  have h5 : Real.log x * (1 / ((⌈x ^ a⌉₊ : ℝ) * Real.log (⌈x ^ a⌉₊ : ℝ))) ≤ δ / 2 := by
    have hpos : 0 < x ^ a * Real.log (x ^ a) := mul_pos hA0 (by linarith)
    have hle : x ^ a * Real.log (x ^ a) ≤ (⌈x ^ a⌉₊ : ℝ) * Real.log (⌈x ^ a⌉₊ : ℝ) :=
      mul_le_mul hce hlce (by linarith) (by linarith)
    calc Real.log x * (1 / ((⌈x ^ a⌉₊ : ℝ) * Real.log (⌈x ^ a⌉₊ : ℝ)))
        ≤ Real.log x * (1 / (x ^ a * Real.log (x ^ a))) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hle) hlx.le
      _ = 1 / (a * x ^ a) := by rw [hlxa]; field_simp
      _ ≤ 1 / (a * (2 / (a * δ))) := one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hAδ ha.le)
      _ = δ / 2 := by field_simp
  -- the main terms
  have h6 : Real.log x * (1 / Real.log (x ^ a) - 1 / Real.log (x ^ c) + 4 * εθ / Real.log (x ^ a) ^ 2) ≤
      1 / a - 1 / c + δ / 2 := by
    rw [hlxa, hlxc]
    have hc : 0 < c := lt_of_lt_of_le ha hac
    have heq : Real.log x * (1 / (a * Real.log x) - 1 / (c * Real.log x) + 4 * εθ / (a * Real.log x) ^ 2) =
        1 / a - 1 / c + δ / (2 * Real.log x) := by
      rw [hεθ]; field_simp; ring
    rw [heq]
    have : δ / (2 * Real.log x) ≤ δ / 2 :=
      div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
    linarith
  have h7 := mul_le_mul_of_nonneg_left (h2.trans (add_le_add le_rfl h1)) hlx.le
  rw [mul_add] at h7
  linarith

/-! ### The cells -/

/-- The primes of the cell `k` at `x`: `x^{e_k/DEN} ≤ p < x^{(e_k + H)/DEN}`. -/
noncomputable def cellP (x : ℝ) (k : ℕ) : Finset ℕ :=
  primesIn (x ^ ((SieveCert.e k : ℝ) / DEN)) (x ^ (((SieveCert.e k : ℝ) + H) / DEN))

/-- A prime lies in `cellP x k` exactly when its exponent `log p/log x` lies in the cell `k`. -/
theorem mem_cellP {x : ℝ} (hx : 1 < x) {k p : ℕ} :
    p ∈ cellP x k ↔ p.Prime ∧ InCell k (Real.log p / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hD := DEN_pos'
  rw [cellP, mem_primesIn, InCell]
  refine and_congr_right fun hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have key : ∀ r : ℝ, x ^ r ≤ p ↔ r * DEN ≤ Real.log p / Real.log x * DEN := by
    intro r
    rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hx0 r) hp0, Real.log_rpow hx0,
      mul_le_mul_iff_of_pos_right hD, le_div_iff₀ hlx]
  have key' : ∀ r : ℝ, (p : ℝ) < x ^ r ↔ Real.log p / Real.log x * DEN < r * DEN := by
    intro r
    rw [← not_le, key, not_le]
  rw [key, key', div_mul_cancel₀ _ hD.ne', div_mul_cancel₀ _ hD.ne']

/-- The cell's `Σ 1/p` is at most `h/a = H/e_k`, up to `o(1)`. -/
theorem evLe_cell_inv (k : ℕ) : EvLe (fun x => ∑ p ∈ cellP x k, 1 / (p : ℝ)) ((H : ℝ) / SieveCert.e k) := by
  have hek : (0 : ℝ) < SieveCert.e k := by exact_mod_cast e_pos k
  have hH : (0 : ℝ) < H := by exact_mod_cast H_pos
  have hD := DEN_pos'
  have ha : (0 : ℝ) < (SieveCert.e k : ℝ) / DEN := div_pos hek hD
  have hac : (SieveCert.e k : ℝ) / DEN ≤ ((SieveCert.e k : ℝ) + H) / DEN := div_le_div_of_nonneg_right (by linarith) hD.le
  have hlog : Real.log (((SieveCert.e k : ℝ) + H) / DEN) - Real.log ((SieveCert.e k : ℝ) / DEN) ≤ (H : ℝ) / SieveCert.e k := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have heq : ((SieveCert.e k : ℝ) + H) / DEN / ((SieveCert.e k : ℝ) / DEN) = 1 + (H : ℝ) / SieveCert.e k := by field_simp
    rw [heq]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + (H : ℝ) / SieveCert.e k by positivity)
    linarith
  intro δ hδ
  filter_upwards [evLe_sum_inv ha hac δ hδ] with x hx
  exact le_trans hx (by linarith)

/-- The cell's `log x · Σ 1/(p log p)` is at most `h/a² = H·DEN/e_k²`, up to `o(1)`. -/
theorem evLe_cell_inv_log (k : ℕ) :
    EvLe (fun x => Real.log x * ∑ p ∈ cellP x k, 1 / ((p : ℝ) * Real.log p)) ((H : ℝ) * DEN / (SieveCert.e k : ℝ) ^ 2) := by
  have hek : (0 : ℝ) < SieveCert.e k := by exact_mod_cast e_pos k
  have hH : (0 : ℝ) < H := by exact_mod_cast H_pos
  have hD := DEN_pos'
  have ha : (0 : ℝ) < (SieveCert.e k : ℝ) / DEN := div_pos hek hD
  have hac : (SieveCert.e k : ℝ) / DEN ≤ ((SieveCert.e k : ℝ) + H) / DEN := div_le_div_of_nonneg_right (by linarith) hD.le
  have hle : 1 / ((SieveCert.e k : ℝ) / DEN) - 1 / (((SieveCert.e k : ℝ) + H) / DEN) ≤ (H : ℝ) * DEN / (SieveCert.e k : ℝ) ^ 2 := by
    have heq : 1 / ((SieveCert.e k : ℝ) / DEN) - 1 / (((SieveCert.e k : ℝ) + H) / DEN) = (H : ℝ) * DEN / ((SieveCert.e k : ℝ) * (SieveCert.e k + H)) := by
      field_simp; ring
    rw [heq]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  intro δ hδ
  filter_upwards [evLe_sum_inv_log ha hac δ hδ] with x hx
  exact le_trans hx (by linarith)

/-! ### A point of a cell -/

theorem four_H_le_V : 4 * H ≤ V := by decide

/-- **A point of a cell.** Let `x > 1` with `(log 2/log x)·DEN < 1`, let `d ≥ 1` be the product of the other primes
and `p ≥ 2` the last, with `s ≤ (log d/log x)DEN`, `t ≤ (log p/log x)DEN ≤ t + H` and
`((log d + log p)/log x)DEN ≤ s + t + mH ≤ DEN`. If `z₀` is `psi_le`'s for `U = 2DEN/t` and `ε`, and `p ≥ z₀`, then
`Ψ(x/(dp), p) ≤ (omK s t m/K + ε)·x/(dp log p)`. -/
theorem psi_point {s t m z₀ p : ℕ} {ε x d : ℝ} (ht : 0 < t)
    (hz₀ : ∀ z : ℕ, z₀ ≤ z → ∀ y : ℝ, 1 ≤ y → Real.log (2 * y) ≤ 2 * DEN / t * Real.log z →
      (Psi y z : ℝ) ≤ (omegaC (Real.log (2 * y) / Real.log z) + ε) * y / Real.log z)
    (hx : 1 < x) (hτ : Real.log 2 / Real.log x * DEN < 1) (hd : 1 ≤ d) (hp : 2 ≤ p) (hpz : z₀ ≤ p)
    (hs : (s : ℝ) ≤ Real.log d / Real.log x * DEN)
    (htp : (t : ℝ) ≤ Real.log p / Real.log x * DEN) (htpH : Real.log p / Real.log x * DEN ≤ t + H)
    (hsum : (Real.log d / Real.log x + Real.log p / Real.log x) * DEN ≤ s + t + m * H)
    (hDEN : (s : ℝ) + t + m * H ≤ DEN) :
    (Psi (x / (d * p)) p : ℝ) ≤ ((omK s t m : ℝ) / K + ε) * (x / (d * p * Real.log p)) := by
  have hD := DEN_pos'
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hd0 : 0 < d := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hdp : 0 < d * p := mul_pos hd0 hp0
  have hsum' : Real.log d + Real.log p ≤ Real.log x := by
    have h1 : (Real.log d / Real.log x + Real.log p / Real.log x) * DEN ≤ 1 * DEN := by
      rw [one_mul]; exact le_trans hsum hDEN
    have h2 := le_of_mul_le_mul_right h1 hD
    rwa [← add_div, div_le_one hlx] at h2
  obtain ⟨y, hy⟩ : ∃ y, y = x / (d * p) := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 0 < y := by rw [hy]; exact div_pos hx0 hdp
  have hlogy : Real.log y = Real.log x - Real.log d - Real.log p := by
    rw [hy, Real.log_div hx0.ne' hdp.ne', Real.log_mul hd0.ne' hp0.ne']; ring
  have hy1 : 1 ≤ y := by
    rw [← Real.log_nonneg_iff hy0]
    linarith
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log x - Real.log d - Real.log p := by
    rw [Real.log_mul two_ne_zero hy0.ne', hlogy]; ring
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2x : Real.log 2 < Real.log x := by
    have hD1 : (1 : ℝ) ≤ DEN := by exact_mod_cast DEN_pos
    have h : Real.log 2 / Real.log x < 1 :=
      lt_of_le_of_lt (le_mul_of_one_le_right (div_pos hl2 hlx).le hD1) hτ
    rwa [div_lt_one hlx] at h
  have hU : Real.log (2 * y) ≤ 2 * DEN / t * Real.log p := by
    rw [hlog2y]
    have h1 : (t : ℝ) * Real.log x ≤ Real.log p * DEN := by
      have h := htp
      rw [div_mul_eq_mul_div, le_div_iff₀ hlx] at h
      linarith
    have h2 : 2 * (DEN : ℝ) / t * Real.log p = 2 * (Real.log p * DEN) / t := by ring
    rw [h2, le_div_iff₀ ht']
    nlinarith [mul_pos ht' hlp, mul_nonneg ht'.le hld, mul_lt_mul_of_pos_right hl2x ht']
  have hψ := hz₀ p hpz y hy1 hU
  have harg : Real.log (2 * y) / Real.log p =
      (1 - Real.log d / Real.log x - Real.log p / Real.log x + Real.log 2 / Real.log x) /
        (Real.log p / Real.log x) := by
    rw [hlog2y]
    have := hlx.ne'
    have := hlp.ne'
    field_simp
    ring
  have hω := omegaC_le (s := s) (t := t) (m := m) (σ := Real.log d / Real.log x)
    (α := Real.log p / Real.log x) (τ := Real.log 2 / Real.log x) ht hs htp htpH hsum (div_pos hl2 hlx).le hτ
  rw [← harg] at hω
  have hyp : y / Real.log p = x / (d * p * Real.log p) := by rw [hy, div_div]
  calc (Psi y p : ℝ) ≤ (omegaC (Real.log (2 * y) / Real.log p) + ε) * y / Real.log p := hψ
    _ = (omegaC (Real.log (2 * y) / Real.log p) + ε) * (x / (d * p * Real.log p)) := by
        rw [mul_div_assoc, hyp]
    _ ≤ ((omK s t m : ℝ) / K + ε) * (x / (d * p * Real.log p)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hx0.le (by positivity))

/-- **The finish.** Let `W, P ≥ 0`. If `F ≤ (W + ε)(x/log x)R` eventually for every `ε > 0`, `limsup R ≤ P` and
`WP ≤ B`, then `F ≤ (B + δ)x/log x` eventually, for every `δ > 0`. -/
theorem evLe_finish {F R : ℝ → ℝ} {W P B : ℝ} (hW : 0 ≤ W) (hP : 0 ≤ P) (hWP : W * P ≤ B) (hR : EvLe R P)
    (hF : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, F x ≤ (W + ε) * (x / Real.log x) * R x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, F x ≤ (B + δ) * (x / Real.log x) := by
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min 1 (δ / (2 * (P + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := by rw [hε]; exact min_le_left _ _
  have hεP : ε * P ≤ δ / 2 := by
    have h := min_le_right 1 (δ / (2 * (P + 1)))
    rw [← hε] at h
    calc ε * P ≤ δ / (2 * (P + 1)) * P := mul_le_mul_of_nonneg_right h hP
      _ ≤ δ / (2 * (P + 1)) * (P + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = δ / 2 := by field_simp
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁, δ₁ = δ / (2 * (W + 1)) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  have hWδ : (W + 1) * δ₁ = δ / 2 := by rw [hδ₁]; field_simp
  filter_upwards [hF ε hε0, hR δ₁ hδ₁0, eventually_gt_atTop 1] with x hFx hRx hx1
  have hxl : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx1)
  have hk : (W + ε) * (P + δ₁) ≤ B + δ := by nlinarith
  calc F x ≤ (W + ε) * (x / Real.log x) * R x := hFx
    _ ≤ (W + ε) * (x / Real.log x) * (P + δ₁) := mul_le_mul_of_nonneg_left hRx (by positivity)
    _ = (W + ε) * (P + δ₁) * (x / Real.log x) := by ring
    _ ≤ (B + δ) * (x / Real.log x) := mul_le_mul_of_nonneg_right hk hxl.le

/-! ### The shares -/

theorem sum_inv_nonneg (s : Finset ℕ) : 0 ≤ ∑ p ∈ s, 1 / (p : ℝ) :=
  Finset.sum_nonneg fun p _ => by positivity

theorem ev_log_mul_nonneg (f : ℝ → Finset ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log x * ∑ p ∈ f x, 1 / ((p : ℝ) * Real.log p) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact mul_nonneg (Real.log_nonneg hx)
    (Finset.sum_nonneg fun p _ => one_div_nonneg.2 (mul_nonneg (Nat.cast_nonneg p) (Real.log_natCast_nonneg p)))

/-- **The share of a cell of depth 2.** For a cell `(i, j)` with `e_i + 2e_j ≤ DEN`, as for a candidate, and every
`δ > 0`: eventually `Σ_{p₁ ∈ cell i} Σ_{p₂ ∈ cell j} Ψ(x/(p₁p₂), p₂) ≤ (bound2/K + δ)·x/log x`. -/
theorem share2 {i j : ℕ} (hij : SieveCert.e i + 2 * SieveCert.e j ≤ DEN) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, (Psi (x / (p₁ * p₂)) p₂ : ℝ) ≤
      ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ) * (x / Real.log x) := by
  have hD := DEN_pos'
  have hH : (0 : ℝ) < H := by exact_mod_cast H_pos
  have hei : (0 : ℝ) < SieveCert.e i := by exact_mod_cast e_pos i
  have hej : (0 : ℝ) < SieveCert.e j := by exact_mod_cast e_pos j
  have hK := K_pos'
  have hfit : SieveCert.e i + SieveCert.e j + 2 * H ≤ DEN := by
    have h1 : V ≤ SieveCert.e j := by unfold SieveCert.e; omega
    have h2 := four_H_le_V
    omega
  have hfit' : (SieveCert.e i : ℝ) + SieveCert.e j + 2 * H ≤ DEN := by exact_mod_cast hfit
  obtain ⟨W, hW⟩ : ∃ W, W = (omK (SieveCert.e i) (SieveCert.e j) 2 : ℝ) / K := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hP1 : (0 : ℝ) ≤ (H : ℝ) / SieveCert.e i := by positivity
  have hP2 : (0 : ℝ) ≤ (H : ℝ) * DEN / (SieveCert.e j : ℝ) ^ 2 := by positivity
  have hWP : W * ((H : ℝ) / SieveCert.e i * ((H : ℝ) * DEN / (SieveCert.e j : ℝ) ^ 2)) ≤
      (bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K := by
    have h := bound2_ge (e_pos i) (e_pos j)
    have heq : W * ((H : ℝ) / SieveCert.e i * ((H : ℝ) * DEN / (SieveCert.e j : ℝ) ^ 2)) =
        ((H : ℝ) / DEN) ^ 2 * ((omK (SieveCert.e i) (SieveCert.e j) 2 : ℝ) / K) /
          (((SieveCert.e i : ℝ) / DEN) * ((SieveCert.e j : ℝ) / DEN) ^ 2) := by
      rw [hW]; field_simp
    rw [heq]; exact h
  have hR := EvLe.mul hP1 hP2 (Filter.Eventually.of_forall fun x => sum_inv_nonneg (cellP x i))
    (ev_log_mul_nonneg fun x => cellP x j) (evLe_cell_inv i) (evLe_cell_inv_log j)
  refine evLe_finish hW0 (mul_nonneg hP1 hP2) hWP hR (fun ε hε => ?_) hδ
  obtain ⟨z₀, hz₀⟩ := psi_le (2 * DEN / SieveCert.e j) hε
  have hb : (0 : ℝ) < (SieveCert.e j : ℝ) / DEN := div_pos hej hD
  filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop (DEN * Real.log 2),
    (tendsto_rpow_atTop hb).eventually_ge_atTop (z₀ : ℝ)] with x hx1 hlx2 hxz
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hτ : Real.log 2 / Real.log x * DEN < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hlx]; linarith
  have hterm : ∀ p₁ ∈ cellP x i, ∀ p₂ ∈ cellP x j,
      (Psi (x / (p₁ * p₂)) p₂ : ℝ) ≤ (W + ε) * (x / ((p₁ : ℝ) * p₂ * Real.log p₂)) := by
    intro p₁ hp₁ p₂ hp₂
    have hz : z₀ ≤ p₂ := by
      have h1 : (z₀ : ℝ) ≤ p₂ := le_trans hxz (mem_primesIn.1 hp₂).2.1
      exact_mod_cast h1
    rw [mem_cellP hx1] at hp₁ hp₂
    obtain ⟨hp₁p, hc₁l, hc₁r⟩ := hp₁
    obtain ⟨hp₂p, hc₂l, hc₂r⟩ := hp₂
    rw [hW]
    refine psi_point (s := SieveCert.e i) (t := SieveCert.e j) (m := 2) (e_pos j) hz₀ hx1 hτ
      (by exact_mod_cast hp₁p.one_lt.le) hp₂p.two_le hz hc₁l hc₂l hc₂r.le ?_ ?_
    · rw [add_mul]; push_cast; linarith
    · push_cast; linarith
  have hsum_eq : ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, (W + ε) * (x / ((p₁ : ℝ) * p₂ * Real.log p₂)) =
      (W + ε) * (x / Real.log x) * ((∑ p₁ ∈ cellP x i, 1 / (p₁ : ℝ)) *
        (Real.log x * ∑ p₂ ∈ cellP x j, 1 / ((p₂ : ℝ) * Real.log p₂))) := by
    rw [Finset.mul_sum (cellP x j), Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p₂ _ => ?_
    have := hlx.ne'
    field_simp
  calc ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, (Psi (x / (p₁ * p₂)) p₂ : ℝ)
      ≤ ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, (W + ε) * (x / ((p₁ : ℝ) * p₂ * Real.log p₂)) :=
        Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂
    _ = _ := hsum_eq

/-- A four-fold sum of a product is the product of the sums. -/
theorem sum4_mul (s₁ s₂ s₃ s₄ : Finset ℕ) (f₁ f₂ f₃ f₄ : ℕ → ℝ) :
    ∑ p₁ ∈ s₁, ∑ p₂ ∈ s₂, ∑ p₃ ∈ s₃, ∑ p₄ ∈ s₄, f₁ p₁ * f₂ p₂ * f₃ p₃ * f₄ p₄ =
      (∑ p ∈ s₁, f₁ p) * (∑ p ∈ s₂, f₂ p) * (∑ p ∈ s₃, f₃ p) * (∑ p ∈ s₄, f₄ p) := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- **The share of a cell of depth 4.** For a cell `(i, j, k, l)` with `e_i + e_j + e_k + 2e_l ≤ DEN`, as for a
counted cell, and every `δ > 0`: eventually
`Σ_{p₁ ∈ cell i} Σ_{p₂ ∈ cell j} Σ_{p₃ ∈ cell k} Σ_{p₄ ∈ cell l} Ψ(x/(p₁p₂p₃p₄), p₄) ≤ (bound4/K + δ)·x/log x`. -/
theorem share4 {i j k l : ℕ}
    (hijkl : SieveCert.e i + SieveCert.e j + SieveCert.e k + 2 * SieveCert.e l ≤ DEN) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
        (Psi (x / (p₁ * p₂ * p₃ * p₄)) p₄ : ℝ) ≤
      ((bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K + δ) *
        (x / Real.log x) := by
  have hD := DEN_pos'
  have hH : (0 : ℝ) < H := by exact_mod_cast H_pos
  have hei : (0 : ℝ) < SieveCert.e i := by exact_mod_cast e_pos i
  have hej : (0 : ℝ) < SieveCert.e j := by exact_mod_cast e_pos j
  have hek : (0 : ℝ) < SieveCert.e k := by exact_mod_cast e_pos k
  have hel : (0 : ℝ) < SieveCert.e l := by exact_mod_cast e_pos l
  have hK := K_pos'
  have hfit : SieveCert.e i + SieveCert.e j + SieveCert.e k + SieveCert.e l + 4 * H ≤ DEN := by
    have h1 : V ≤ SieveCert.e l := by unfold SieveCert.e; omega
    have h2 := four_H_le_V
    omega
  have hfit' : (SieveCert.e i : ℝ) + SieveCert.e j + SieveCert.e k + SieveCert.e l + 4 * H ≤ DEN := by
    exact_mod_cast hfit
  obtain ⟨W, hW⟩ : ∃ W, W = (omK (SieveCert.e i + SieveCert.e j + SieveCert.e k) (SieveCert.e l) 4 : ℝ) / K :=
    ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hPi : (0 : ℝ) ≤ (H : ℝ) / SieveCert.e i := by positivity
  have hPj : (0 : ℝ) ≤ (H : ℝ) / SieveCert.e j := by positivity
  have hPk : (0 : ℝ) ≤ (H : ℝ) / SieveCert.e k := by positivity
  have hPl : (0 : ℝ) ≤ (H : ℝ) * DEN / (SieveCert.e l : ℝ) ^ 2 := by positivity
  have hWP : W * ((H : ℝ) / SieveCert.e i * ((H : ℝ) / SieveCert.e j) * ((H : ℝ) / SieveCert.e k) *
      ((H : ℝ) * DEN / (SieveCert.e l : ℝ) ^ 2)) ≤
      (bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K := by
    have h := bound4_ge (e_pos i) (e_pos j) (e_pos k) (e_pos l)
    have heq : W * ((H : ℝ) / SieveCert.e i * ((H : ℝ) / SieveCert.e j) * ((H : ℝ) / SieveCert.e k) *
        ((H : ℝ) * DEN / (SieveCert.e l : ℝ) ^ 2)) =
        ((H : ℝ) / DEN) ^ 4 * ((omK (SieveCert.e i + SieveCert.e j + SieveCert.e k) (SieveCert.e l) 4 : ℝ) / K) /
          (((SieveCert.e i : ℝ) / DEN) * ((SieveCert.e j : ℝ) / DEN) * ((SieveCert.e k : ℝ) / DEN) *
            ((SieveCert.e l : ℝ) / DEN) ^ 2) := by
      rw [hW]; field_simp
    rw [heq]; exact h
  have hS : ∀ m, ∀ᶠ x : ℝ in atTop, 0 ≤ ∑ p ∈ cellP x m, 1 / (p : ℝ) :=
    fun m => Filter.Eventually.of_forall fun x => sum_inv_nonneg (cellP x m)
  have hR := EvLe.mul (mul_nonneg (mul_nonneg hPi hPj) hPk) hPl
    (by filter_upwards [hS i, hS j, hS k] with x h1 h2 h3; exact mul_nonneg (mul_nonneg h1 h2) h3)
    (ev_log_mul_nonneg fun x => cellP x l)
    (EvLe.mul (mul_nonneg hPi hPj) hPk (by filter_upwards [hS i, hS j] with x h1 h2; exact mul_nonneg h1 h2)
      (hS k) (EvLe.mul hPi hPj (hS i) (hS j) (evLe_cell_inv i) (evLe_cell_inv j)) (evLe_cell_inv k))
    (evLe_cell_inv_log l)
  refine evLe_finish hW0 (by positivity) hWP hR (fun ε hε => ?_) hδ
  obtain ⟨z₀, hz₀⟩ := psi_le (2 * DEN / SieveCert.e l) hε
  have hb : (0 : ℝ) < (SieveCert.e l : ℝ) / DEN := div_pos hel hD
  filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop (DEN * Real.log 2),
    (tendsto_rpow_atTop hb).eventually_ge_atTop (z₀ : ℝ)] with x hx1 hlx2 hxz
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hτ : Real.log 2 / Real.log x * DEN < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hlx]; linarith
  have hterm : ∀ p₁ ∈ cellP x i, ∀ p₂ ∈ cellP x j, ∀ p₃ ∈ cellP x k, ∀ p₄ ∈ cellP x l,
      (Psi (x / (p₁ * p₂ * p₃ * p₄)) p₄ : ℝ) ≤ (W + ε) * (x / ((p₁ : ℝ) * p₂ * p₃ * p₄ * Real.log p₄)) := by
    intro p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
    have hz : z₀ ≤ p₄ := by
      have h1 : (z₀ : ℝ) ≤ p₄ := le_trans hxz (mem_primesIn.1 hp₄).2.1
      exact_mod_cast h1
    rw [mem_cellP hx1] at hp₁ hp₂ hp₃ hp₄
    obtain ⟨hp₁p, hc₁l, hc₁r⟩ := hp₁
    obtain ⟨hp₂p, hc₂l, hc₂r⟩ := hp₂
    obtain ⟨hp₃p, hc₃l, hc₃r⟩ := hp₃
    obtain ⟨hp₄p, hc₄l, hc₄r⟩ := hp₄
    have h1 : (1 : ℝ) ≤ p₁ := by exact_mod_cast hp₁p.one_lt.le
    have h2 : (1 : ℝ) ≤ p₂ := by exact_mod_cast hp₂p.one_lt.le
    have h3 : (1 : ℝ) ≤ p₃ := by exact_mod_cast hp₃p.one_lt.le
    have hlogd : Real.log ((p₁ : ℝ) * p₂ * p₃) / Real.log x * DEN =
        Real.log p₁ / Real.log x * DEN + Real.log p₂ / Real.log x * DEN + Real.log p₃ / Real.log x * DEN := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]; ring
    have hd1 : (1 : ℝ) ≤ (p₁ : ℝ) * p₂ * p₃ := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
    rw [hW]
    refine psi_point (s := SieveCert.e i + SieveCert.e j + SieveCert.e k) (t := SieveCert.e l) (m := 4)
      (e_pos l) hz₀ hx1 hτ hd1 hp₄p.two_le hz ?_ hc₄l hc₄r.le ?_ ?_
    · rw [hlogd]; push_cast; linarith
    · rw [add_mul, hlogd]; push_cast; linarith
    · push_cast; linarith
  have hsum_eq : ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
      (W + ε) * (x / ((p₁ : ℝ) * p₂ * p₃ * p₄ * Real.log p₄)) =
      (W + ε) * (x / Real.log x) * ((∑ p ∈ cellP x i, 1 / (p : ℝ)) * (∑ p ∈ cellP x j, 1 / (p : ℝ)) *
        (∑ p ∈ cellP x k, 1 / (p : ℝ)) * (Real.log x * ∑ p ∈ cellP x l, 1 / ((p : ℝ) * Real.log p))) := by
    have h1 : ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
        (W + ε) * (x / ((p₁ : ℝ) * p₂ * p₃ * p₄ * Real.log p₄)) =
        ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
          (W + ε) * x * (1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ)) * (1 / (p₃ : ℝ)) * (1 / ((p₄ : ℝ) * Real.log p₄)) := by
      refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ =>
        Finset.sum_congr rfl fun p₃ _ => Finset.sum_congr rfl fun p₄ _ => ?_
      ring
    rw [h1, sum4_mul (f₁ := fun p => (W + ε) * x * (1 / (p : ℝ))), ← Finset.mul_sum]
    have := hlx.ne'
    field_simp
  calc ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
        (Psi (x / (p₁ * p₂ * p₃ * p₄)) p₄ : ℝ)
      ≤ ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
          (W + ε) * (x / ((p₁ : ℝ) * p₂ * p₃ * p₄ * Real.log p₄)) :=
        Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => Finset.sum_le_sum fun p₃ hp₃ =>
          Finset.sum_le_sum fun p₄ hp₄ => hterm p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
    _ = _ := hsum_eq

/-- `share2` on a candidate cell. -/
theorem share2_of_cand {i j : ℕ} (h : cand i j = true) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, (Psi (x / (p₁ * p₂)) p₂ : ℝ) ≤
      ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ) * (x / Real.log x) := by
  simp only [cand, Bool.and_eq_true, decide_eq_true_eq] at h
  exact share2 h.1.1.2 hδ

/-- `share4` on a counted cell. -/
theorem share4_of_counted4 {i j k l : ℕ} (h : counted4 i j k l = true) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∑ p₁ ∈ cellP x i, ∑ p₂ ∈ cellP x j, ∑ p₃ ∈ cellP x k, ∑ p₄ ∈ cellP x l,
        (Psi (x / (p₁ * p₂ * p₃ * p₄)) p₄ : ℝ) ≤
      ((bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K + δ) *
        (x / Real.log x) := by
  simp only [counted4, Bool.and_eq_true, decide_eq_true_eq] at h
  exact share4 h.1 hδ

end Shares

end SieveRough

#print axioms SieveRough.theta_near
#print axioms SieveRough.abel_le
#print axioms SieveRough.sum_inv_mul_log_le
#print axioms SieveRough.sum_inv_le
#print axioms SieveRough.sum_inv_mul_sub_log_le
#print axioms SieveRough.Psi_le_buchstab
#print axioms SieveRough.card_primes_dyadic
#print axioms SieveRough.super_M
#print axioms SieveRough.claim_step
#print axioms SieveRough.psi_le
#print axioms SieveRough.mem_cellP
#print axioms SieveRough.evLe_cell_inv
#print axioms SieveRough.evLe_cell_inv_log
#print axioms SieveRough.psi_point
#print axioms SieveRough.share2
#print axioms SieveRough.share4
#print axioms SieveRough.share2_of_cand
#print axioms SieveRough.share4_of_counted4
