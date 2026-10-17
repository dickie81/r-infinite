/-
# Round 483: squarefree numbers in a zero-free half-plane

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. If `ζ(s) ≠ 0` for `Re s > θ` (`0 ≤ θ < 1`), then the number `Q(x)` of squarefree `n ≤ x`
(`summ sqf x`) is `6x/π² + O(x^{1/(3−θ)+η})` for every `η > 0` (`squarefree_isBigO_of_zeroFree`). At
`θ = 11/12` (round 466's half-plane) the exponent is `12/25 + η` (`squarefree_isBigO_twelve_25ths`), and at
`θ = Θ` (round 469's supremum of the real parts of the nontrivial zeros) it is `1/(3 − Θ) + η`
(`squarefree_isBigO_Theta`); neither needs a hypothesis.

* `sum_sq_dvd_moebius`: `Σ_{d² ∣ n} μ(d)` is `1` for a squarefree `n ≥ 1` and `0` otherwise. With `n = b²a`, `a`
  squarefree (Mathlib's `Nat.sq_mul_squarefree_of_pos`), a `d ≥ 1` has `d² ∣ n` exactly when `d ∣ b`
  (`dvd_of_sq_dvd_sq_mul`, by factorizations), and `Σ_{d ∣ b} μ(d) = [b = 1]` (Mathlib's `ArithmeticFunction.moebius_mul_coe_zeta`). So
  `Q(N) = Σ_{d ≤ N} μ(d)⌊N/d²⌋` (`sum_sqf_eq`).
* `hasSum_moebius_div_sq`: `Σ μ(d)/d² = 1/ζ(2) = 6/π²` (round 221's `PsiOmega.LSeries_moebius_eq` and
  Mathlib's `riemannZeta_two`).
* `abs_sum_Ioc_div_sq_le`, `abs_sub_sum_le`: Abel summation (Mathlib's `sum_mul_eq_sub_sub_integral_mul'`).
  If `|M(t)| ≤ Ct^α` for `t ≥ 1`, with `C ≥ 0` and `α < 2`, then
  `|6/π² − Σ_{d ≤ D} μ(d)/d²| ≤ C(2 + 2/(2 − α))D^{α−2}` for `D ≥ 1`.
* `abs_sum_Ioc_le`: the hyperbola method. `Σ_{D < d ≤ N} μ(d)⌊N/d²⌋ = Σ_m Σ_{D < d ≤ √(N/m)} μ(d)`; each inner
  sum is empty or `M(√(N/m)) − M(D)`, and it is empty unless `m ≤ N/(D + 1)²`.
* `sum_rpow_neg_le`: `Σ_{m ≤ Z} m^{−β} ≤ Z^{1−β}/(1 − β)` for `0 ≤ β < 1` (Mathlib's
  `AntitoneOn.sum_le_integral_of_integrableOn`).
* `abs_sum_sqf_sub_le`: `|Q(N) − 6N/π²| ≤ y + CKNy^{α−2}` for `1 ≤ y ≤ N` and `0 ≤ α < 1`, with `D = ⌊y⌋` and
  `K = 4(2 + 2/(2 − α)) + 1/(1 − α/2) + 1`.
* `mertens_le_of_zeroFree`: round 472's `MertensExponent.mertens_isBigO_of_zeroFree` as `|M(t)| ≤ Ct^{θ+η}` for
  every `t ≥ 1`, with round 221's `|M(t)| ≤ t` (`PsiOmega.linBound_moebius`) below the threshold.
* `squarefree_isBigO_of_zeroFree`: `y = N^{1/(3−θ)}` and `α = θ + η′` with `η′ = min(η(3 − θ), (1 − θ)/2)`, so
  that `y` and `Ny^{α−2} = N^{(1+η′)/(3−θ)}` are at most `x^{1/(3−θ)+η}`.
-/
import MertensExponent

set_option lang.lemmaCmd true

open Real Filter Topology MeasureTheory Asymptotics

namespace SquarefreeCount

open PsiOmega MertensExponent

/-! ### `μ² = Σ_{d² ∣ n} μ(d)` and the count -/

/-- `d² ∣ b²a` with `a` squarefree forces `d ∣ b`. -/
lemma dvd_of_sq_dvd_sq_mul {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : d ^ 2 ∣ b ^ 2 * a) : d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  rw [← Nat.factorization_le_iff_dvd hd hb, Finsupp.le_def]
  have h2 := Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd)
    (mul_ne_zero (pow_ne_zero 2 hb) ha0)).2 h)
  intro p
  have hp := h2 p
  rw [Nat.factorization_pow, Nat.factorization_mul (pow_ne_zero 2 hb) ha0, Nat.factorization_pow]
    at hp
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hp
  have h1 := ha.natFactorization_le_one p
  omega

/-- `Σ_{d² ∣ n} μ(d)` is `1` if `n ≥ 1` is squarefree and `0` otherwise. -/
lemma sum_sq_dvd_moebius {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ (Finset.Ioc 0 n).filter (fun d ↦ d ^ 2 ∣ n), (ArithmeticFunction.moebius d : ℝ) =
      if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, ha0, hb0, rfl, ha⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hset : (Finset.Ioc 0 (b ^ 2 * a)).filter (fun d ↦ d ^ 2 ∣ b ^ 2 * a) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd0, -⟩, hd⟩
      exact ⟨dvd_of_sq_dvd_sq_mul ha hb0.ne' hd0.ne' hd, hb0.ne'⟩
    · rintro ⟨hdb, -⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdb hb0
      have hsq : d ^ 2 ∣ b ^ 2 * a := (pow_dvd_pow_of_dvd hdb 2).mul_right a
      refine ⟨⟨hd0, ?_⟩, hsq⟩
      calc d ≤ d ^ 2 := by nlinarith
        _ ≤ b ^ 2 * a := Nat.le_of_dvd (by positivity) hsq
  rw [hset]
  have hμ : ∑ d ∈ b.divisors, (ArithmeticFunction.moebius d : ℝ) = if b = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f b) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    rw [← Int.cast_sum, h]
    split_ifs <;> simp
  rw [hμ]
  have hiff : b = 1 ↔ Squarefree (b ^ 2 * a) := by
    constructor
    · rintro rfl
      simpa using ha
    · intro hsq
      exact Nat.isUnit_iff.1 (hsq b ⟨a, by ring⟩)
  by_cases hb1 : b = 1
  · rw [ite_eq_left hb1, ite_eq_left (hiff.1 hb1)]
  · rw [ite_eq_right hb1, ite_eq_right (fun h ↦ hb1 (hiff.2 h))]

/-- The indicator of the squarefree numbers. -/
noncomputable def sqf (n : ℕ) : ℝ := if Squarefree n then 1 else 0

/-- `{m ∈ (0, N] : mk ≤ N} = (0, N/k]` for `k > 0`. -/
lemma filter_mul_le (N k : ℕ) (hk : 0 < k) :
    (Finset.Ioc 0 N).filter (fun m ↦ m * k ≤ N) = Finset.Ioc 0 (N / k) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.le_div_iff_mul_le hk]
  constructor
  · rintro ⟨⟨hm0, -⟩, hmk⟩
    exact ⟨hm0, hmk⟩
  · rintro ⟨hm0, hmk⟩
    exact ⟨⟨hm0, le_trans (Nat.le_mul_of_pos_right m hk) hmk⟩, hmk⟩

/-- **`Q(N) = Σ_{d ≤ N} μ(d)⌊N/d²⌋`.** -/
lemma sum_sqf_eq (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, sqf n =
      ∑ d ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Finset.Ioc 0 N, sqf n =
      ∑ d ∈ Finset.Ioc 0 N, if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [sqf, ← sum_sq_dvd_moebius hn.1, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hd0, hdn⟩, hd⟩
      exact ⟨⟨hd0, hdn.trans hn.2⟩, hd⟩
    · rintro ⟨⟨hd0, -⟩, hd⟩
      refine ⟨⟨hd0, ?_⟩, hd⟩
      calc d ≤ d ^ 2 := by nlinarith
        _ ≤ n := Nat.le_of_dvd hn.1 hd
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, Nat.Ioc_filter_dvd_card_eq_div]

/-! ### The tail `Σ_{d > D} μ(d)/d²` -/

/-- `Σ μ(d)/d² = 1/ζ(2) = 6/π²`. -/
lemma hasSum_moebius_div_sq :
    HasSum (fun k : ℕ ↦ (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) (6 / π ^ 2) := by
  have hsum : Summable (fun k : ℕ ↦ (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ ↦ 1 / (k : ℝ) ^ 2)
      (Real.summable_one_div_nat_pow.2 one_lt_two) fun k ↦ ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
    gcongr
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  convert hsum.hasSum using 1
  have hL := LSeries_moebius_eq (s := 2) (by norm_num)
  rw [riemannZeta_two] at hL
  have h2 : LSeries (fun n ↦ (fμ n : ℂ)) 2 =
      ((∑' k : ℕ, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    congr 1
    ext k
    rw [LSeries.term_def]
    split_ifs with hk
    · simp [hk]
    · rw [Complex.cpow_two]
      push_cast
      rfl
  have key : ((∑' k : ℕ, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 : ℝ) : ℂ) =
      ((6 / π ^ 2 : ℝ) : ℂ) := by
    rw [← h2, hL, one_div_div]
    push_cast
    rfl
  exact (Complex.ofReal_injective key).symm

/-- **The tail by Abel summation.** If `|Σ_{k ≤ t} c(k)| ≤ Ct^α` for `t ≥ 1`, `0 ≤ α < 2`, then
`|Σ_{D < k ≤ Z} c(k)/k²| ≤ C(2 + 2/(2 − α))D^{α−2}` for `1 ≤ D ≤ Z`. -/
lemma abs_sum_Ioc_div_sq_le {c : ℕ → ℝ} {α C : ℝ} (hα2 : α < 2) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 1 ≤ t → |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k| ≤ C * t ^ α)
    {D Z : ℕ} (hD : 1 ≤ D) (hDZ : D ≤ Z) :
    |∑ k ∈ Finset.Ioc D Z, c k / (k : ℝ) ^ 2| ≤ C * (2 + 2 / (2 - α)) * (D : ℝ) ^ (α - 2) := by
  set f : ℝ → ℝ := fun t ↦ t ^ (-2 : ℝ) with hfdef
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hDZr : (D : ℝ) ≤ Z := by exact_mod_cast hDZ
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hderiv : deriv f = fun t ↦ -2 * t ^ (-3 : ℝ) := by
    funext t
    rw [hfdef, Real.deriv_rpow_const]
    norm_num
  have hdiff : ∀ t ∈ Set.Icc (D : ℝ) Z, DifferentiableAt ℝ f t := fun t ht ↦
    Real.differentiableAt_rpow_const_of_ne _ (by linarith [ht.1])
  have hint : IntegrableOn (deriv f) (Set.Icc (D : ℝ) Z) := by
    rw [hderiv]
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht ↦ Or.inl (by
      simp only [id]; linarith [ht.1]))
  have habel := sum_mul_eq_sub_sub_integral_mul' c hDZ hdiff hint
  have hlhs : ∑ k ∈ Finset.Ioc D Z, c k / (k : ℝ) ^ 2 = ∑ k ∈ Finset.Ioc D Z, f k * c k := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    show c k / (k : ℝ) ^ 2 = (k : ℝ) ^ (-2 : ℝ) * c k
    rw [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_two]
    ring
  rw [hlhs, habel]
  -- the three terms
  have hS : ∀ n : ℕ, 1 ≤ n → |∑ k ∈ Finset.Icc 0 n, c k| ≤ C * (n : ℝ) ^ α := fun n hn ↦ by
    have h := hC n (by exact_mod_cast hn)
    rwa [Nat.floor_natCast] at h
  have hpow : ∀ x : ℝ, 0 < x → x ^ (-2 : ℝ) * x ^ α = x ^ (α - 2) := fun x hx ↦ by
    rw [← Real.rpow_add hx]; ring_nf
  have hT1 : |f Z * ∑ k ∈ Finset.Icc 0 Z, c k| ≤ C * (D : ℝ) ^ (α - 2) := by
    rw [abs_mul, hfdef, abs_of_nonneg (by positivity)]
    calc (Z : ℝ) ^ (-2 : ℝ) * |∑ k ∈ Finset.Icc 0 Z, c k|
        ≤ (Z : ℝ) ^ (-2 : ℝ) * (C * (Z : ℝ) ^ α) :=
          mul_le_mul_of_nonneg_left (hS Z (hD.trans hDZ)) (by positivity)
      _ = C * (Z : ℝ) ^ (α - 2) := by rw [← hpow Z hZ0]; ring
      _ ≤ C * (D : ℝ) ^ (α - 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hD0 hDZr (by linarith)) hC0
  have hT2 : |f D * ∑ k ∈ Finset.Icc 0 D, c k| ≤ C * (D : ℝ) ^ (α - 2) := by
    rw [abs_mul, hfdef, abs_of_nonneg (by positivity)]
    calc (D : ℝ) ^ (-2 : ℝ) * |∑ k ∈ Finset.Icc 0 D, c k|
        ≤ (D : ℝ) ^ (-2 : ℝ) * (C * (D : ℝ) ^ α) :=
          mul_le_mul_of_nonneg_left (hS D hD) (by positivity)
      _ = C * (D : ℝ) ^ (α - 2) := by rw [← hpow D hD0]; ring
  have hgint : IntegrableOn (fun t : ℝ ↦ 2 * C * t ^ (α - 3)) (Set.Ioi (D : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hD0).const_mul (2 * C)
  have hT3 : |∫ t in Set.Ioc (D : ℝ) Z, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k| ≤
      C * (2 / (2 - α)) * (D : ℝ) ^ (α - 2) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in Set.Ioc (D : ℝ) Z, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖
        ≤ ∫ t in Set.Ioc (D : ℝ) Z, 2 * C * t ^ (α - 3) := by
          refine norm_integral_le_of_norm_le (hgint.mono_set Set.Ioc_subset_Ioi_self) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦ ?_)
          have ht1 : 1 ≤ t := hD1.trans ht.1.le
          have ht0 : 0 < t := by linarith
          rw [hderiv, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ (-3 : ℝ))]
          calc |(-2 : ℝ)| * t ^ (-3 : ℝ) * |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k|
              ≤ 2 * t ^ (-3 : ℝ) * (C * t ^ α) := by
                rw [show |(-2 : ℝ)| = 2 by norm_num]
                exact mul_le_mul_of_nonneg_left (hC t ht1) (by positivity)
            _ = 2 * C * t ^ (α - 3) := by
                rw [show α - 3 = -3 + α by ring, Real.rpow_add ht0]; ring
      _ ≤ ∫ t in Set.Ioi (D : ℝ), 2 * C * t ^ (α - 3) := by
          refine setIntegral_mono_set hgint ?_ (Set.Ioc_subset_Ioi_self.eventuallyLE)
          refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht ↦ ?_)
          have ht0 : (0 : ℝ) < t := hD0.trans ht
          positivity
      _ = C * (2 / (2 - α)) * (D : ℝ) ^ (α - 2) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hD0,
            show α - 3 + 1 = α - 2 by ring]
          have h2α : (2 : ℝ) - α ≠ 0 := by linarith
          have hα2' : α - 2 ≠ 0 := by linarith
          field_simp
          ring
  calc |f Z * ∑ k ∈ Finset.Icc 0 Z, c k - f D * ∑ k ∈ Finset.Icc 0 D, c k -
        ∫ t in Set.Ioc (D : ℝ) Z, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k|
      ≤ |f Z * ∑ k ∈ Finset.Icc 0 Z, c k| + |f D * ∑ k ∈ Finset.Icc 0 D, c k| +
        |∫ t in Set.Ioc (D : ℝ) Z, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k| := by
        have h1 := abs_sub (f Z * ∑ k ∈ Finset.Icc 0 Z, c k - f D * ∑ k ∈ Finset.Icc 0 D, c k)
          (∫ t in Set.Ioc (D : ℝ) Z, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        have h2 := abs_sub (f Z * ∑ k ∈ Finset.Icc 0 Z, c k) (f D * ∑ k ∈ Finset.Icc 0 D, c k)
        linarith
    _ ≤ C * (D : ℝ) ^ (α - 2) + C * (D : ℝ) ^ (α - 2) + C * (2 / (2 - α)) * (D : ℝ) ^ (α - 2) := by
        linarith
    _ = C * (2 + 2 / (2 - α)) * (D : ℝ) ^ (α - 2) := by ring

/-- **The tail of `Σ μ(d)/d²`.** If `|M(t)| ≤ Ct^α` for `t ≥ 1`, `0 ≤ α < 2`, then
`|6/π² − Σ_{d ≤ D} μ(d)/d²| ≤ C(2 + 2/(2 − α))D^{α−2}` for `D ≥ 1`. -/
lemma abs_sub_sum_le {α C : ℝ} (hα2 : α < 2) (hC0 : 0 ≤ C)
    (hM : ∀ t : ℝ, 1 ≤ t → |summ fμ t| ≤ C * t ^ α) {D : ℕ} (hD : 1 ≤ D) :
    |6 / π ^ 2 - ∑ k ∈ Finset.Ioc 0 D, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2| ≤
      C * (2 + 2 / (2 - α)) * (D : ℝ) ^ (α - 2) := by
  set a : ℕ → ℝ := fun k ↦ (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 with hadef
  have hIcc : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, (ArithmeticFunction.moebius k : ℝ) =
      ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℝ) := fun n ↦ by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
    simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
    congr 1
  have hC : ∀ t : ℝ, 1 ≤ t →
      |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * t ^ α := fun t ht ↦ by
    rw [hIcc]
    exact hM t ht
  -- the partial sums `Σ_{k ∈ (0, Z]} a k` tend to `6/π²`
  have htend : Tendsto (fun Z : ℕ ↦ ∑ k ∈ Finset.Ioc 0 Z, a k) atTop (𝓝 (6 / π ^ 2)) := by
    have h := hasSum_moebius_div_sq.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun Z ↦ ?_
    simp only [Function.comp]
    rw [Nat.range_succ_eq_Icc_zero, Finset.Icc_eq_cons_Ioc (Nat.zero_le Z), Finset.sum_cons]
    simp [hadef]
  have hlim : Tendsto (fun Z : ℕ ↦ |∑ k ∈ Finset.Ioc 0 Z, a k - ∑ k ∈ Finset.Ioc 0 D, a k|)
      atTop (𝓝 |6 / π ^ 2 - ∑ k ∈ Finset.Ioc 0 D, a k|) :=
    (htend.sub_const _).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop D] with Z hZ
  rw [← Finset.sum_Ioc_consecutive a (Nat.zero_le D) hZ, add_sub_cancel_left]
  exact abs_sum_Ioc_div_sq_le hα2 hC0 hC hD hZ

/-! ### The hyperbola method -/

/-- `Σ_{m ≤ Z} m^{−β} ≤ Z^{1−β}/(1 − β)` for `0 ≤ β < 1`. -/
lemma sum_rpow_neg_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (Z : ℕ) :
    ∑ m ∈ Finset.Ioc 0 Z, (m : ℝ) ^ (-β) ≤ (Z : ℝ) ^ (1 - β) / (1 - β) := by
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-β)) (Set.Ioc 0 (0 + (Z : ℝ))) := by
    intro s hs t ht hst
    exact Real.rpow_le_rpow_of_nonpos hs.1 hst (by linarith)
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (-β)) (Set.Icc 0 (0 + (Z : ℝ))) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := (Z : ℝ)) (r := -β)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)] at h
    simpa using h
  have h := hanti.sum_le_integral_of_integrableOn hint
  rw [integral_rpow (Or.inl (by linarith))] at h
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (0 + ((i + 1 : ℕ) : ℝ)) ^ (-β) =
      ∑ m ∈ Finset.Ioc 0 n, (m : ℝ) ^ (-β) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le n), zero_add]
  rw [hsum, zero_add, Real.zero_rpow (by linarith), sub_zero, show -β + 1 = 1 - β by ring] at h
  exact h

/-- **The hyperbola step.** If `|M(t)| ≤ Ct^α` for `t ≥ 1`, then for `1 ≤ D ≤ N`,
`|Σ_{D < d ≤ N} μ(d)⌊N/d²⌋| ≤ Σ_{m ≤ N/(D+1)²} (C(N/m)^{α/2} + CD^α)`. -/
lemma abs_sum_Ioc_le {C α : ℝ} (hC0 : 0 ≤ C) (hα0 : 0 ≤ α)
    (hM : ∀ t : ℝ, 1 ≤ t → |summ fμ t| ≤ C * t ^ α) {N D : ℕ} (hD : 1 ≤ D) :
    |∑ d ∈ Finset.Ioc D N, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ)| ≤
      ∑ m ∈ Finset.Ioc 0 (N / (D + 1) ^ 2),
        (C * ((N : ℝ) / ((m : ℕ) : ℝ)) ^ (α / 2) + C * (D : ℝ) ^ α) := by
  set μr : ℕ → ℝ := fun d ↦ (ArithmeticFunction.moebius d : ℝ) with hμr
  have hsummK : ∀ K : ℕ, summ fμ K = ∑ d ∈ Finset.Ioc 0 K, μr d := fun K ↦ by
    rw [summ, Nat.floor_natCast]
    congr 1
  -- `⌊N/d²⌋` as a count over `m`
  have hcount : ∀ d ∈ Finset.Ioc D N, μr d * ((N / d ^ 2 : ℕ) : ℝ) =
      ∑ m ∈ Finset.Ioc 0 N, if m * d ^ 2 ≤ N then μr d else 0 := by
    intro d hd
    have hd0 : 0 < d ^ 2 := by
      have : 0 < d := lt_of_lt_of_le (by omega) (Finset.mem_Ioc.1 hd).1.le
      positivity
    rw [← Finset.sum_filter, filter_mul_le N _ hd0, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero,
      nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl hcount, Finset.sum_comm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- each `m`
  have hm : ∀ m ∈ Finset.Ioc 0 N,
      |∑ d ∈ Finset.Ioc D N, if m * d ^ 2 ≤ N then μr d else 0| ≤
        if m * (D + 1) ^ 2 ≤ N then C * ((N : ℝ) / m) ^ (α / 2) + C * (D : ℝ) ^ α else 0 := by
    intro m hm
    have hm0 : 0 < m := (Finset.mem_Ioc.1 hm).1
    set K := Nat.sqrt (N / m) with hKdef
    have hset : (Finset.Ioc D N).filter (fun d ↦ m * d ^ 2 ≤ N) = Finset.Ioc D K := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      have hiff : m * d ^ 2 ≤ N ↔ d ≤ K := by
        rw [hKdef, Nat.le_sqrt, Nat.le_div_iff_mul_le hm0]
        constructor <;> intro h <;> nlinarith
      rw [hiff]
      constructor
      · rintro ⟨⟨hDd, -⟩, hdK⟩
        exact ⟨hDd, hdK⟩
      · rintro ⟨hDd, hdK⟩
        refine ⟨⟨hDd, ?_⟩, hdK⟩
        have h1 : m * d ^ 2 ≤ N := hiff.2 hdK
        nlinarith
    rw [← Finset.sum_filter, hset]
    have hnn : 0 ≤ C * ((N : ℝ) / m) ^ (α / 2) + C * (D : ℝ) ^ α := by positivity
    rcases le_or_gt K D with hKD | hDK
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero]
      split_ifs <;> simp [hnn]
    · have hcond : m * (D + 1) ^ 2 ≤ N := by
        have h1 : (D + 1) * (D + 1) ≤ N / m := Nat.le_sqrt.1 hDK
        have h2 := (Nat.le_div_iff_mul_le hm0).1 h1
        nlinarith
      have hcons := Finset.sum_Ioc_consecutive μr (Nat.zero_le D) hDK.le
      have hdiff : ∑ d ∈ Finset.Ioc D K, μr d = summ fμ K - summ fμ D := by
        rw [hsummK, hsummK]
        linarith
      rw [ite_eq_left hcond, hdiff]
      have hK1 : (1 : ℝ) ≤ K := by
        have : 1 ≤ K := by omega
        exact_mod_cast this
      have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
      have hMK := hM K hK1
      have hMD := hM D hD1
      -- `K^α ≤ (N/m)^{α/2}`
      have hK2 : ((K : ℝ) ^ 2) ≤ (N : ℝ) / m := by
        have h1 : K ^ 2 ≤ N / m := Nat.sqrt_le' _
        have h2 : ((K ^ 2 : ℕ) : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h2
        exact h2.trans Nat.cast_div_le
      have hKα : (K : ℝ) ^ α ≤ ((N : ℝ) / m) ^ (α / 2) := by
        have h1 : ((K : ℝ) ^ 2) ^ (α / 2) = (K : ℝ) ^ α := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg K)]
          congr 1
          push_cast
          ring
        rw [← h1]
        exact Real.rpow_le_rpow (by positivity) hK2 (by linarith)
      have hsub := abs_sub (summ fμ K) (summ fμ D)
      have h3 : C * (K : ℝ) ^ α ≤ C * ((N : ℝ) / m) ^ (α / 2) :=
        mul_le_mul_of_nonneg_left hKα hC0
      linarith
  refine (Finset.sum_le_sum hm).trans ?_
  rw [← Finset.sum_filter, filter_mul_le N _ (by positivity)]

/-! ### Assembly -/

/-- **The count at an integer.** If `|M(t)| ≤ Ct^α` for `t ≥ 1`, `0 ≤ α < 1`, then
`|Q(N) − 6N/π²| ≤ y + C K N y^{α−2}` for every `1 ≤ y ≤ N`, with
`K = 4(2 + 2/(2 − α)) + 1/(1 − α/2) + 1`. -/
lemma abs_sum_sqf_sub_le {C α : ℝ} (hC0 : 0 ≤ C) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hM : ∀ t : ℝ, 1 ≤ t → |summ fμ t| ≤ C * t ^ α) {N : ℕ} {y : ℝ} (hy1 : 1 ≤ y)
    (hyN : y ≤ N) :
    |∑ n ∈ Finset.Ioc 0 N, sqf n - 6 / π ^ 2 * N| ≤
      y + C * (4 * (2 + 2 / (2 - α)) + 1 / (1 - α / 2) + 1) * N * y ^ (α - 2) := by
  set D := ⌊y⌋₊ with hDdef
  have hD1 : 1 ≤ D := Nat.one_le_floor_iff _ |>.2 hy1
  have hD1r : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDy : (D : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyD : y < D + 1 := Nat.lt_floor_add_one y
  have hDN : D ≤ N := Nat.floor_le_of_le hyN
  have hN1 : (1 : ℝ) ≤ N := hy1.trans hyN
  have hN0 : (0 : ℝ) < N := by linarith
  have hy0 : 0 < y := by linarith
  set μr : ℕ → ℝ := fun d ↦ (ArithmeticFunction.moebius d : ℝ) with hμr
  rw [sum_sqf_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDN]
  -- part 1: the floor
  have hP1 : |∑ d ∈ Finset.Ioc 0 D, μr d * ((N / d ^ 2 : ℕ) : ℝ) -
      N * ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2| ≤ y := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ Finset.Ioc 0 D, |μr d * ((N / d ^ 2 : ℕ) : ℝ) - N * (μr d / (d : ℝ) ^ 2)|
        ≤ ∑ d ∈ Finset.Ioc 0 D, (1 : ℝ) := by
          refine Finset.sum_le_sum fun d hd ↦ ?_
          have hd0 : (0 : ℝ) < (d : ℝ) ^ 2 := by
            have : 0 < d := (Finset.mem_Ioc.1 hd).1
            positivity
          have hfl : ((N / d ^ 2 : ℕ) : ℝ) = ⌊(N : ℝ) / ((d ^ 2 : ℕ) : ℝ)⌋₊ := by
            rw [Nat.floor_div_eq_div]
          have hfl1 := Nat.floor_le (by positivity : (0 : ℝ) ≤ (N : ℝ) / ((d ^ 2 : ℕ) : ℝ))
          have hfl2 := Nat.lt_floor_add_one ((N : ℝ) / ((d ^ 2 : ℕ) : ℝ))
          push_cast at hfl hfl1 hfl2
          have hμ1 : |μr d| ≤ 1 := by
            simp only [hμr]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have heq : μr d * ((N / d ^ 2 : ℕ) : ℝ) - N * (μr d / (d : ℝ) ^ 2) =
              μr d * (((N / d ^ 2 : ℕ) : ℝ) - N / (d : ℝ) ^ 2) := by ring
          rw [heq, abs_mul]
          have h2 : |((N / d ^ 2 : ℕ) : ℝ) - N / (d : ℝ) ^ 2| ≤ 1 := by
            rw [hfl, abs_le]
            constructor <;> linarith
          calc |μr d| * |((N / d ^ 2 : ℕ) : ℝ) - N / (d : ℝ) ^ 2| ≤ 1 * 1 :=
                mul_le_mul hμ1 h2 (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = D := by simp
      _ ≤ y := hDy
  -- part 2: the tail
  have hP2 : |N * ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2 - 6 / π ^ 2 * N| ≤
      C * (4 * (2 + 2 / (2 - α))) * N * y ^ (α - 2) := by
    have htail := abs_sub_sum_le (by linarith) hC0 hM hD1
    have hDy2 : (D : ℝ) ^ (α - 2) ≤ 4 * y ^ (α - 2) := by
      have hyD2 : y / 2 ≤ D := by linarith
      calc (D : ℝ) ^ (α - 2) ≤ (y / 2) ^ (α - 2) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) hyD2 (by linarith)
        _ = y ^ (α - 2) / 2 ^ (α - 2) := Real.div_rpow hy0.le (by norm_num) _
        _ ≤ 4 * y ^ (α - 2) := by
            have h2 : (1 / 4 : ℝ) ≤ 2 ^ (α - 2) := by
              calc (1 / 4 : ℝ) = 2 ^ (-2 : ℝ) := by norm_num
                _ ≤ 2 ^ (α - 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            rw [div_le_iff₀ (by positivity)]
            have : 0 ≤ y ^ (α - 2) := by positivity
            nlinarith
    have heq : N * ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2 - 6 / π ^ 2 * N =
        -(N * (6 / π ^ 2 - ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2)) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hN0]
    have hK : 0 ≤ 2 + 2 / (2 - α) := by
      have : 0 < 2 - α := by linarith
      positivity
    calc (N : ℝ) * |6 / π ^ 2 - ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2|
        ≤ N * (C * (2 + 2 / (2 - α)) * (D : ℝ) ^ (α - 2)) :=
          mul_le_mul_of_nonneg_left htail hN0.le
      _ ≤ N * (C * (2 + 2 / (2 - α)) * (4 * y ^ (α - 2))) := by
          gcongr
      _ = C * (4 * (2 + 2 / (2 - α))) * N * y ^ (α - 2) := by ring
  -- part 3: the hyperbola
  have hP3 : |∑ d ∈ Finset.Ioc D N, μr d * ((N / d ^ 2 : ℕ) : ℝ)| ≤
      C * (1 / (1 - α / 2) + 1) * N * y ^ (α - 2) := by
    refine (abs_sum_Ioc_le hC0 hα0 hM hD1).trans ?_
    set Z := N / (D + 1) ^ 2 with hZdef
    have hZ : (Z : ℝ) ≤ N / y ^ 2 := by
      have h1 : (Z : ℝ) ≤ (N : ℝ) / (((D + 1) ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      have h2 : y ^ 2 ≤ (((D + 1) ^ 2 : ℕ) : ℝ) := by
        push_cast
        exact pow_le_pow_left₀ hy0.le hyD.le 2
      exact h1.trans (div_le_div_of_nonneg_left hN0.le (by positivity) h2)
    have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg Z
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    -- `Σ_{m ≤ Z} (N/m)^{α/2} = N^{α/2} Σ m^{−α/2}`
    have hs1 : ∑ m ∈ Finset.Ioc 0 Z, C * ((N : ℝ) / m) ^ (α / 2) =
        C * (N : ℝ) ^ (α / 2) * ∑ m ∈ Finset.Ioc 0 Z, (m : ℝ) ^ (-(α / 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [Real.div_rpow hN0.le (Nat.cast_nonneg m), Real.rpow_neg (Nat.cast_nonneg m)]
      ring
    have hs2 := sum_rpow_neg_le (β := α / 2) (by linarith) (by linarith) Z
    have hZpow : (Z : ℝ) ^ (1 - α / 2) ≤ ((N : ℝ) / y ^ 2) ^ (1 - α / 2) :=
      Real.rpow_le_rpow hZ0 hZ (by linarith)
    have hNy : (N : ℝ) ^ (α / 2) * ((N : ℝ) / y ^ 2) ^ (1 - α / 2) = N * y ^ (α - 2) := by
      rw [Real.div_rpow hN0.le (by positivity), ← Real.rpow_natCast y 2,
        ← Real.rpow_mul hy0.le]
      have h1 : (N : ℝ) ^ (α / 2) * (N : ℝ) ^ (1 - α / 2) = N := by
        rw [← Real.rpow_add hN0]; ring_nf; exact Real.rpow_one _
      have h2 : y ^ (((2 : ℕ) : ℝ) * (1 - α / 2)) = (y ^ (α - 2))⁻¹ := by
        rw [← Real.rpow_neg hy0.le]; congr 1; push_cast; ring
      rw [h2, mul_div_assoc', h1, div_inv_eq_mul]
    have hyα : (D : ℝ) ^ α * Z ≤ N * y ^ (α - 2) := by
      have h1 : (D : ℝ) ^ α ≤ y ^ α := Real.rpow_le_rpow (by linarith) hDy hα0
      have h2 : y ^ α * ((N : ℝ) / y ^ 2) = N * y ^ (α - 2) := by
        rw [Real.rpow_sub hy0, Real.rpow_two]; field_simp
      calc (D : ℝ) ^ α * Z ≤ y ^ α * ((N : ℝ) / y ^ 2) :=
            mul_le_mul h1 hZ hZ0 (by positivity)
        _ = N * y ^ (α - 2) := h2
    have hden : 0 < 1 - α / 2 := by linarith
    calc ∑ m ∈ Finset.Ioc 0 Z, C * ((N : ℝ) / m) ^ (α / 2) + (Z : ℝ) * (C * (D : ℝ) ^ α)
        ≤ C * (N : ℝ) ^ (α / 2) * ((Z : ℝ) ^ (1 - α / 2) / (1 - α / 2)) +
            C * (N * y ^ (α - 2)) := by
          rw [hs1]
          have h1 : C * (N : ℝ) ^ (α / 2) * ∑ m ∈ Finset.Ioc 0 Z, (m : ℝ) ^ (-(α / 2)) ≤
              C * (N : ℝ) ^ (α / 2) * ((Z : ℝ) ^ (1 - α / 2) / (1 - α / 2)) :=
            mul_le_mul_of_nonneg_left hs2 (by positivity)
          have h2 : (Z : ℝ) * (C * (D : ℝ) ^ α) ≤ C * (N * y ^ (α - 2)) := by
            have := mul_le_mul_of_nonneg_left hyα hC0
            linarith
          linarith
      _ ≤ C * (N : ℝ) ^ (α / 2) * (((N : ℝ) / y ^ 2) ^ (1 - α / 2) / (1 - α / 2)) +
            C * (N * y ^ (α - 2)) := by
          gcongr
      _ = C * (1 / (1 - α / 2) + 1) * N * y ^ (α - 2) := by
          rw [show C * (N : ℝ) ^ (α / 2) * (((N : ℝ) / y ^ 2) ^ (1 - α / 2) / (1 - α / 2)) =
            C * ((N : ℝ) ^ (α / 2) * ((N : ℝ) / y ^ 2) ^ (1 - α / 2)) / (1 - α / 2) by ring, hNy]
          field_simp
  -- assemble
  have heq : ∑ d ∈ Finset.Ioc 0 D, μr d * ((N / d ^ 2 : ℕ) : ℝ) +
      ∑ d ∈ Finset.Ioc D N, μr d * ((N / d ^ 2 : ℕ) : ℝ) - 6 / π ^ 2 * N =
      (∑ d ∈ Finset.Ioc 0 D, μr d * ((N / d ^ 2 : ℕ) : ℝ) -
        N * ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2) +
      (N * ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2 - 6 / π ^ 2 * N) +
      ∑ d ∈ Finset.Ioc D N, μr d * ((N / d ^ 2 : ℕ) : ℝ) := by ring
  rw [heq]
  have habs := abs_add_three (∑ d ∈ Finset.Ioc 0 D, μr d * ((N / d ^ 2 : ℕ) : ℝ) -
        N * ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2)
      (N * ∑ d ∈ Finset.Ioc 0 D, μr d / (d : ℝ) ^ 2 - 6 / π ^ 2 * N)
      (∑ d ∈ Finset.Ioc D N, μr d * ((N / d ^ 2 : ℕ) : ℝ))
  have hfin : C * (4 * (2 + 2 / (2 - α))) * N * y ^ (α - 2) +
      C * (1 / (1 - α / 2) + 1) * N * y ^ (α - 2) =
      C * (4 * (2 + 2 / (2 - α)) + 1 / (1 - α / 2) + 1) * N * y ^ (α - 2) := by ring
  linarith

/-- A zero-free half-plane `Re s > θ` gives `|M(t)| ≤ Ct^{θ+η}` for every `t ≥ 1`. -/
lemma mertens_le_of_zeroFree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |summ fμ t| ≤ C * t ^ (θ + η) := by
  obtain ⟨c, hc⟩ := (mertens_isBigO_of_zeroFree hθ0 hθ1 hzf hη).bound
  obtain ⟨X, hX⟩ := eventually_atTop.1 hc
  refine ⟨max c 0 + max X 1, by positivity, fun t ht ↦ ?_⟩
  have htα : 1 ≤ t ^ (θ + η) := Real.one_le_rpow ht (by linarith)
  have h0 : 0 ≤ t ^ (θ + η) := by positivity
  have hA : 0 ≤ max c 0 * t ^ (θ + η) := by positivity
  have hB : 0 ≤ max X 1 * t ^ (θ + η) := by positivity
  rw [add_mul]
  by_cases htX : X ≤ t
  · have h := hX t htX
    rw [Real.norm_eq_abs, Real.norm_of_nonneg h0] at h
    have h1 : c * t ^ (θ + η) ≤ max c 0 * t ^ (θ + η) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    linarith
  · push Not at htX
    have h1 := linBound_moebius t (by linarith)
    have h2 : t ≤ max X 1 * t ^ (θ + η) :=
      calc t ≤ max X 1 := htX.le.trans (le_max_left _ _)
        _ ≤ max X 1 * t ^ (θ + η) := le_mul_of_one_le_right (by positivity) htα
    linarith

/-- **Squarefree numbers in a zero-free half-plane.** If `ζ(s) ≠ 0` for `Re s > θ`, `0 ≤ θ < 1`, then
`#{n ≤ x : n squarefree} = 6x/π² + O(x^{1/(3−θ)+η})` for every `η > 0`. -/
theorem squarefree_isBigO_of_zeroFree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hzf : ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ sqf x - 6 / π ^ 2 * x) =O[atTop] fun x ↦ x ^ (1 / (3 - θ) + η) := by
  have h3θ : 0 < 3 - θ := by linarith
  set η' : ℝ := min (η * (3 - θ)) ((1 - θ) / 2) with hη'def
  have hη' : 0 < η' := lt_min (by positivity) (by linarith)
  have hη'1 : η' ≤ η * (3 - θ) := min_le_left _ _
  have hη'2 : η' ≤ (1 - θ) / 2 := min_le_right _ _
  set α : ℝ := θ + η' with hαdef
  have hα0 : 0 ≤ α := by linarith
  have hα1 : α < 1 := by linarith
  obtain ⟨C, hC0, hM⟩ := mertens_le_of_zeroFree hθ0 hθ1 hzf hη'
  set K : ℝ := 4 * (2 + 2 / (2 - α)) + 1 / (1 - α / 2) + 1 with hKdef
  have hK : 0 ≤ K := by
    have : 0 < 2 - α := by linarith
    have : 0 < 1 - α / 2 := by linarith
    positivity
  set e : ℝ := 1 / (3 - θ) + η with hedef
  have hpe : (1 + η') / (3 - θ) ≤ e := by
    rw [hedef, div_le_iff₀ h3θ]
    have : (1 / (3 - θ) + η) * (3 - θ) = 1 + η * (3 - θ) := by field_simp
    linarith
  refine IsBigO.of_bound (1 + C * K + 6 / π ^ 2) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.2 hx
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  set y : ℝ := (N : ℝ) ^ (1 / (3 - θ)) with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow hN1r (by positivity)
  have hyN : y ≤ N := by
    calc y ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by rw [div_le_one h3θ]; linarith)
      _ = N := Real.rpow_one _
  have hy0 : 0 < y := by linarith
  have hmain := abs_sum_sqf_sub_le hC0 hα0 hα1 hM hy1 hyN
  -- `y` and `N y^{α−2}` are powers of `N`
  have hNyα : (N : ℝ) * y ^ (α - 2) = (N : ℝ) ^ ((1 + η') / (3 - θ)) := by
    rw [hydef, ← Real.rpow_mul hN0.le]
    calc (N : ℝ) * (N : ℝ) ^ (1 / (3 - θ) * (α - 2))
        = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / (3 - θ) * (α - 2)) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (1 + 1 / (3 - θ) * (α - 2)) := by rw [← Real.rpow_add hN0]
      _ = (N : ℝ) ^ ((1 + η') / (3 - θ)) := by
          congr 1
          rw [hαdef]
          field_simp
          ring
  have hxe : 1 ≤ x ^ e := Real.one_le_rpow hx (by positivity)
  have hNe1 : (N : ℝ) ^ ((1 + η') / (3 - θ)) ≤ x ^ e :=
    (Real.rpow_le_rpow hN0.le hNx (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le hx hpe)
  have hye : y ≤ x ^ e := by
    calc y ≤ (N : ℝ) ^ ((1 + η') / (3 - θ)) :=
          Real.rpow_le_rpow_of_exponent_le hN1r (by gcongr; linarith)
      _ ≤ x ^ e := hNe1
  have hsumm : summ sqf x = ∑ n ∈ Finset.Ioc 0 N, sqf n := by
    rw [summ, ← hNdef]
    congr 1
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), hsumm]
  have hπ : 0 < 6 / π ^ 2 := by positivity
  have hfrac : |6 / π ^ 2 * (N : ℝ) - 6 / π ^ 2 * x| ≤ 6 / π ^ 2 := by
    rw [← mul_sub, abs_mul, abs_of_pos hπ]
    have : |(N : ℝ) - x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith
  have hsplit : ∑ n ∈ Finset.Ioc 0 N, sqf n - 6 / π ^ 2 * x =
      (∑ n ∈ Finset.Ioc 0 N, sqf n - 6 / π ^ 2 * N) + (6 / π ^ 2 * N - 6 / π ^ 2 * x) := by ring
  rw [hsplit]
  have htri := abs_add_le (∑ n ∈ Finset.Ioc 0 N, sqf n - 6 / π ^ 2 * N)
    (6 / π ^ 2 * N - 6 / π ^ 2 * x)
  have hCK : C * K * N * y ^ (α - 2) ≤ C * K * x ^ e := by
    rw [mul_assoc (C * K), hNyα]
    exact mul_le_mul_of_nonneg_left hNe1 (mul_nonneg hC0 hK)
  have hπe : 6 / π ^ 2 ≤ 6 / π ^ 2 * x ^ e := le_mul_of_one_le_right hπ.le hxe
  calc |∑ n ∈ Finset.Ioc 0 N, sqf n - 6 / π ^ 2 * N + (6 / π ^ 2 * N - 6 / π ^ 2 * x)|
      ≤ y + C * K * N * y ^ (α - 2) + 6 / π ^ 2 := by linarith
    _ ≤ x ^ e + C * K * x ^ e + 6 / π ^ 2 * x ^ e := by linarith
    _ = (1 + C * K + 6 / π ^ 2) * x ^ e := by ring

/-- **`Q(x) = 6x/π² + O(x^{12/25+η})`**, from round 466's half-plane `Re s > 11/12`. -/
theorem squarefree_isBigO_twelve_25ths {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ sqf x - 6 / π ^ 2 * x) =O[atTop] fun x ↦ x ^ (12 / 25 + η) := by
  have h := squarefree_isBigO_of_zeroFree (θ := 11 / 12) (by norm_num) (by norm_num)
    (fun _ hs ↦ (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1) hη
  rwa [show (1 : ℝ) / (3 - 11 / 12) = 12 / 25 by norm_num] at h

/-- **`Q(x) = 6x/π² + O(x^{1/(3−Θ)+η})`**, with round 469's `Θ`. -/
theorem squarefree_isBigO_Theta {η : ℝ} (hη : 0 < η) :
    (fun x ↦ summ sqf x - 6 / π ^ 2 * x) =O[atTop] fun x ↦ x ^ (1 / (3 - PsiExponent.Theta) + η) :=
  squarefree_isBigO_of_zeroFree (by linarith [PsiExponent.half_le_Theta])
    (by linarith [PsiExponent.Theta_le]) (fun _ hs ↦ PsiExponent.zeta_ne_zero_of_Theta_lt hs) hη

end SquarefreeCount
