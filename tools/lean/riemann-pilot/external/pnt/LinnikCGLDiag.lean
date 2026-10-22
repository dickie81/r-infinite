/-
# Round 649: the Gram matrix's diagonal against its main term (the CGL plan's stage M3, the `S₃` side)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li's §7 drops the condition that the points of a triple are not all equal: "This can be done by removing
the terms when (t₁,χ₁) = (t₂,χ₂) = (t₃,χ₃)", which cost their `Z′ = |W|((N/q)Σ_{0<|m|≤(qT)^ϵqT/N}ĥ₀(Nm/q)C_q(m))³`,
`C_q(m) = Σ_{a mod q, (a,q)=1}e_q(am)`. Then: "Fortunately, the condition m ≠ 0 makes this term small. By Lemma
4.3(1), for m ≠ 0, |ĥ₀(Nm/q)| ≪ q/(N|m|). On the other hand, the arithmetic sum is the Ramanujan sum C_q(m) and
|C_q(m)| ≤ (m,q)." (text layer lines 1992 and 2014–2017; spaces restored, the fraction and subscripts transcribed).
At one point per character the dropped terms are the diagonal ones, `F(i, i)³` with `F(i, i) = μ − μ₀` (`Fm_diag`):
the Gram diagonal `μ = Σ_{n∈colsP N, (n,q)=1}w(n/N)²` (round 638's `muP`) against its main term `μ₀ = (φ(q)/q)N∫w²`
(round 639's `mu0`). This file bounds `|μ − μ₀|` by Möbius inversion over the divisors of `q` instead of Ramanujan
sums: `μ − μ₀ = Σ_{d|q}μ(d)(Σ_{n∈colsP N, d|n}w(n/N)² − (N/d)∫w²)`, and each bracket is at most a constant `B`. For
`d ≤ N` the bracket is `Σ_{m≠0}(N/d)ĥ₀(Nm/d)` by round 646's Poisson summation along the multiples of `d`, at most
`A₂Z₂d/N` by round 645's Lemma 4.3 (1) at `K = 2`; for `d > N` at most one multiple of `d` lies in `(N, 2N)`, outside
which `w(n/N) = 0`.

Plain statement (`muP_sub_mu0_le`). For `q ≥ 1` and `N > 0`, `|μ − μ₀| ≤ d(q)B`, with `B = max(2, A₂Z₂)`,
`A₂ = CF(2)/(4π²)` and `Z₂ = Σ_{m∈ℤ}|m|^{−2}`; so `|μ − μ₀| ≤ C_δBq^δ` for `0 < δ ≤ 1` (`muP_sub_mu0_le_rpow`).

Plain statement (`S3_eq_all`). For `q ≥ 1`, `N > 0` and `χ` injective on `R`,
`S₃ = Re Σ_{i,j,k∈R}F(i, j)F(j, k)F(k, i) − |R|(μ − μ₀)³`, the sum now over all triples.

* `sum_divisors_moebius`, `sum_coprime_eq`: `Σ_{d|n}μ(d) = [n = 1]` (Mathlib's `coe_moebius_mul_coe_zeta`), and
  `Σ_{n∈S, (n,q)=1}f(n) = Σ_{d|q}μ(d)Σ_{n∈S, d|n}f(n)`.
* `totient_div_eq`: `φ(q)/q = Σ_{d|q}μ(d)/d` (Mathlib's `sum_eq_iff_sum_mul_moebius_eq` with `Nat.sum_totient`).
* `sum_multiples_eq`: `Σ_{n∈colsP N, d|n}w(n/N)² = Σ_{m∈ℤ}(N/d)ĥ₀(Nm/d)` (round 646's `sum_colsP_residue` and
  `poisson_Wt` at the residue `0` mod `d`).
* `norm_term_le`, `sum_multiples_le_one`, `bracket_le`: the bracket's bound.
* `muP_sub_mu0_le`, `muP_sub_mu0_le_rpow`: the diagonal's bound (round 525's divisor bound `card_divisors_le`).
* `Fm_diag`, `S3_eq_all`: `F(i, i) = μ − μ₀` (round 648's `Em_eq` with round 638's `gramP_diag`), and the condition
  "not all equal" dropped.

The file imports `LinnikCGLTrace.lean`.
-/

import LinnikCGLTrace

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff
open ArithmeticFunction (moebius)

noncomputable section

namespace LinnikCGLDiag

open LinnikCGLMat LinnikCGLMellin LinnikCGLFourier LinnikCGLPoisson LinnikCGLS23 LinnikCGLTrace

/-! ### Möbius over the divisors of `q` -/

/-- `Σ_{d|n} μ(d) = [n = 1]`. -/
lemma sum_divisors_moebius (n : ℕ) : ∑ d ∈ n.divisors, (moebius d : ℝ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at h
  exact h

/-- **Möbius over the divisors of `q`**: `Σ_{n∈S, (n,q)=1} f(n) = Σ_{d|q} μ(d) Σ_{n∈S, d|n} f(n)` for `q ≥ 1`. -/
lemma sum_coprime_eq {q : ℕ} (hq : q ≠ 0) (S : Finset ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ S.filter (fun n => n.Coprime q), f n =
      ∑ d ∈ q.divisors, (moebius d : ℝ) * ∑ n ∈ S.filter (fun n => d ∣ n), f n := by
  classical
  have key : ∀ n, (if n.Coprime q then (1 : ℝ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then (moebius d : ℝ) else 0 := by
    intro n
    have hg : n.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq
    have hdiv : q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h2, h1⟩, hg⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hq⟩, h1⟩
    rw [← Finset.sum_filter, hdiv, sum_divisors_moebius]
  calc ∑ n ∈ S.filter (fun n => n.Coprime q), f n
      = ∑ n ∈ S, f n * (if n.Coprime q then 1 else 0) := by
        rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun n _ => ?_; split_ifs <;> simp
    _ = ∑ n ∈ S, ∑ d ∈ q.divisors, if d ∣ n then (moebius d : ℝ) * f n else 0 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [key n, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        split_ifs <;> ring
    _ = ∑ d ∈ q.divisors, ∑ n ∈ S, if d ∣ n then (moebius d : ℝ) * f n else 0 := Finset.sum_comm
    _ = ∑ d ∈ q.divisors, (moebius d : ℝ) * ∑ n ∈ S.filter (fun n => d ∣ n), f n := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> simp

/-- `φ(q)/q = Σ_{d|q} μ(d)/d` for `q ≥ 1` (Möbius inversion of `Σ_{d|n} φ(d) = n`). -/
lemma totient_div_eq {q : ℕ} (hq : q ≠ 0) :
    (q.totient : ℝ) / q = ∑ d ∈ q.divisors, (moebius d : ℝ) / d := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ) (f := fun n => (n.totient : ℝ))
    (g := fun n => (n : ℝ))).1 (fun n _ => by exact_mod_cast Nat.sum_totient n) q (Nat.pos_of_ne_zero hq)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h2 : ∑ d ∈ q.divisors, (moebius d : ℝ) * ((q / d : ℕ) : ℝ) = q.totient := by
    rw [← h]; exact (Nat.sum_divisorsAntidiagonal (fun d e => (moebius d : ℝ) * (e : ℝ))).symm
  rw [← h2, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdq hd0]
  field_simp

/-! ### The multiples of `d` in `colsP N` -/

lemma Wt_zero_apply (u : ℝ) : Wt 0 u = ((wCGL u ^ 2 : ℝ) : ℂ) := by
  unfold Wt Wc wsq; simp

/-- **The multiples of `d` by Poisson summation**: `Σ_{n∈colsP N, d|n} w(n/N)² = Σ_{m∈ℤ}(N/d)ĥ₀(Nm/d)`, with
`h₀ = w²`. -/
lemma sum_multiples_eq {N : ℝ} (hN : 0 < N) {d : ℕ} (hd : 0 < d) :
    ((∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 : ℝ) : ℂ) =
      ∑' m : ℤ, ((N / d : ℝ) : ℂ) * 𝓕 (Wt 0) (N * m / d) := by
  classical
  have h := sum_colsP_residue (Wt_vanish 0) hN hd (fun n => if d ∣ n then (1 : ℂ) else 0)
    (fun n => by simp only [Nat.dvd_mod_iff (dvd_refl d)])
  have hR : ∑ a ∈ Finset.range d, (if d ∣ a then (1 : ℂ) else 0) * ∑' m : ℤ, Wt 0 ((a + d * m) / N) =
      ∑' m : ℤ, Wt 0 (d * m / N) := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hd)]
    · simp
    · intro a ha ha0
      have : ¬ d ∣ a := fun h' => ha0 (Nat.eq_zero_of_dvd_of_lt h' (Finset.mem_range.1 ha))
      simp [this]
  have hP := poisson_Wt 0 hN hd 0
  simp only [zero_add, Complex.ofReal_zero, zero_div, mul_zero, Complex.exp_zero, mul_one] at hP
  rw [← hP, ← hR, ← h]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Wt_zero_apply]
  split_ifs <;> simp

/-- `‖(N/d)ĥ_τ(Nm/d)‖ ≤ (C_τd/N)|m|^{−2}` for `m ≠ 0`, with `C_τ = CF(2)(1 + |τ|)²/(4π²)` (round 645's `lemma43` at
`K = 2`). -/
lemma norm_term_le (τ : ℝ) {N : ℝ} (hN : 0 < N) {d : ℕ} (hd : 0 < d) {m : ℤ} (hm : m ≠ 0) :
    ‖((N / d : ℝ) : ℂ) * 𝓕 (Wt τ) (N * m / d)‖ ≤
      CF 2 * (1 + |τ|) ^ 2 / (4 * π ^ 2) * d / N * |(m : ℝ)| ^ (-(2 : ℝ)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hN0 : N ≠ 0 := hN.ne'
  have hd0 : (d : ℝ) ≠ 0 := hd'.ne'
  obtain ⟨C, hC⟩ : ∃ C, C = CF 2 * (1 + |τ|) ^ 2 / (4 * π ^ 2) := ⟨_, rfl⟩
  rw [← hC, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h := sq_mul_norm_hhat_le τ (N * m / d)
  rw [← hC] at h
  have hξ0 : N * m / d ≠ 0 := by positivity
  have hξ : 0 < (N * m / d) ^ 2 := by positivity
  have hb : ‖𝓕 (Wt τ) (N * m / d)‖ ≤ C / (N * m / d) ^ 2 := by
    rw [le_div_iff₀ hξ]; linarith
  have habs : |(m : ℝ)| ^ (-(2 : ℝ)) = ((m : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, sq_abs]
  rw [habs]
  calc N / d * ‖𝓕 (Wt τ) (N * m / d)‖ ≤ N / d * (C / (N * m / d) ^ 2) := by gcongr
    _ = C * d / N * ((m : ℝ) ^ 2)⁻¹ := by field_simp

/-- `Z₂ = Σ_{m∈ℤ}|m|^{−2}` (its term `m = 0` is `0`). -/
def Z2 : ℝ := ∑' m : ℤ, |(m : ℝ)| ^ (-(2 : ℝ))

lemma Z2_nonneg : 0 ≤ Z2 := tsum_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _

/-- The bound of a bracket: `B = max(2, A₂Z₂)` with `A₂ = CF(2)/(4π²)`. -/
def Bw : ℝ := max 2 (CF 2 / (4 * π ^ 2) * Z2)

lemma two_le_Bw : 2 ≤ Bw := le_max_left _ _

/-- At most one multiple of `d ≥ N` lies in `(N, 2N)`, so `Σ_{n∈colsP N, d|n} w(n/N)² ≤ 1`. -/
lemma sum_multiples_le_one {N : ℝ} (hN : 0 < N) {d : ℕ} (hdN : N < d) :
    ∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 ≤ 1 := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = (colsP N).filter (fun n => d ∣ n) := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T', T' = T.filter (fun n : ℕ => N < n ∧ (n : ℝ) < 2 * N) := ⟨_, rfl⟩
  rw [← hT]
  have hsplit : ∑ n ∈ T, wCGL (n / N) ^ 2 = ∑ n ∈ T', wCGL (n / N) ^ 2 := by
    rw [hT']
    refine (Finset.sum_filter_of_ne fun n _ hn => ?_).symm
    by_contra h
    apply hn
    have h' : (n : ℝ) / N ≤ 1 ∨ 2 ≤ (n : ℝ) / N := by
      rcases not_and_or.1 h with h1 | h1
      · left; rw [div_le_one hN]; exact not_lt.1 h1
      · right; rw [le_div_iff₀ hN]; linarith [not_lt.1 h1]
    rw [wCGL_zero h']; ring
  have hcard : T'.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hT', hT, Finset.mem_filter, Finset.mem_filter] at ha hb
    obtain ⟨⟨-, hda⟩, ha1, ha2⟩ := ha
    obtain ⟨⟨-, hdb⟩, hb1, hb2⟩ := hb
    rcases le_total a b with hab | hab
    · have hsub : d ∣ b - a := Nat.dvd_sub hdb hda
      have hlt : b - a < d := by
        have : ((b - a : ℕ) : ℝ) < d := by rw [Nat.cast_sub hab]; linarith
        exact_mod_cast this
      have := Nat.eq_zero_of_dvd_of_lt hsub hlt
      omega
    · have hsub : d ∣ a - b := Nat.dvd_sub hda hdb
      have hlt : a - b < d := by
        have : ((a - b : ℕ) : ℝ) < d := by rw [Nat.cast_sub hab]; linarith
        exact_mod_cast this
      have := Nat.eq_zero_of_dvd_of_lt hsub hlt
      omega
  calc ∑ n ∈ T, wCGL (n / N) ^ 2 = ∑ n ∈ T', wCGL (n / N) ^ 2 := hsplit
    _ ≤ ∑ _n ∈ T', (1 : ℝ) := Finset.sum_le_sum fun n _ => by
        have h0 := wCGL_nonneg (n / N); have h1 := wCGL_le_one (n / N); nlinarith
    _ = T'.card := by simp
    _ ≤ 1 := by exact_mod_cast hcard

/-- **The multiples of `d` against their integral**: `|Σ_{n∈colsP N, d|n} w(n/N)² − (N/d)∫w²| ≤ B`. For `d ≤ N` by
Poisson summation: the difference is `Σ_{m≠0}(N/d)ĥ₀(Nm/d)`, at most `A₂Z₂d/N`. For `d > N` both terms lie in
`[0, 1]`. -/
lemma bracket_le {N : ℝ} (hN : 0 < N) {d : ℕ} (hd : 0 < d) :
    |∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 - N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2| ≤
      Bw := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hI0 := integral_w_sq_nonneg
  have hI1 := integral_w_sq_le_one
  have hA0 : 0 ≤ ∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  rcases le_or_gt (d : ℝ) N with hdN | hdN
  · obtain ⟨A, hA⟩ : ∃ A, A = ∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 := ⟨_, rfl⟩
    rw [← hA]
    have hS : Summable fun m : ℤ => ((N / d : ℝ) : ℂ) * 𝓕 (Wt 0) (N * m / d) := by
      refine (summable_poisson 0 hN hd 0).congr fun m => ?_
      simp
    have hT := sum_multiples_eq hN hd
    rw [← hA, hS.tsum_eq_add_tsum_ite 0] at hT
    have h0 : ((N / d : ℝ) : ℂ) * 𝓕 (Wt 0) (N * ((0 : ℤ) : ℝ) / d) =
        ((N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2 : ℝ) : ℂ) := by
      simp only [Int.cast_zero, mul_zero, zero_div, fourier_Wt_zero]; push_cast; ring
    rw [h0] at hT
    have hdiff : ((A - N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2 : ℝ) : ℂ) =
        ∑' m : ℤ, if m = 0 then 0 else ((N / d : ℝ) : ℂ) * 𝓕 (Wt 0) (N * m / d) := by
      push_cast; rw [hT]; push_cast; ring
    have hbound : ∀ m : ℤ, ‖(if m = 0 then (0 : ℂ) else ((N / d : ℝ) : ℂ) * 𝓕 (Wt 0) (N * m / d))‖ ≤
        CF 2 * (1 + |(0 : ℝ)|) ^ 2 / (4 * π ^ 2) * d / N * |(m : ℝ)| ^ (-(2 : ℝ)) := by
      intro m
      split_ifs with hm
      · rw [norm_zero]; have := CF_nonneg 2; positivity
      · exact norm_term_le 0 hN hd hm
    have hsumm : Summable fun m : ℤ =>
        CF 2 * (1 + |(0 : ℝ)|) ^ 2 / (4 * π ^ 2) * d / N * |(m : ℝ)| ^ (-(2 : ℝ)) :=
      (Real.summable_abs_int_rpow one_lt_two).mul_left _
    have hle := tsum_of_norm_bounded hsumm.hasSum hbound
    rw [← hdiff, Complex.norm_real, Real.norm_eq_abs, tsum_mul_left] at hle
    have hc : 0 ≤ CF 2 / (4 * π ^ 2) := by have := CF_nonneg 2; positivity
    have hz := Z2_nonneg
    have hdN1 : (d : ℝ) / N ≤ 1 := by rw [div_le_one hN]; exact hdN
    calc |A - N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2|
        ≤ CF 2 * (1 + |(0 : ℝ)|) ^ 2 / (4 * π ^ 2) * d / N * Z2 := hle
      _ = CF 2 / (4 * π ^ 2) * (d / N) * Z2 := by simp only [abs_zero, add_zero, one_pow, mul_one]; ring
      _ ≤ CF 2 / (4 * π ^ 2) * 1 * Z2 := by gcongr
      _ = CF 2 / (4 * π ^ 2) * Z2 := by ring
      _ ≤ Bw := le_max_right _ _
  · have h1 := sum_multiples_le_one hN hdN
    have hB1 : N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2 ≤ 1 := by
      have : N / d ≤ 1 := by rw [div_le_one hd']; exact hdN.le
      calc N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2 ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    have hB0 : 0 ≤ N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2 := by positivity
    have : |∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 - N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2|
        ≤ 1 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    linarith [two_le_Bw]

/-! ### The diagonal -/

/-- **The diagonal against its main term**: `|μ − μ₀| ≤ d(q)·B` for `q ≥ 1` and `N > 0`. -/
theorem muP_sub_mu0_le {q : ℕ} (hq : q ≠ 0) {N : ℝ} (hN : 0 < N) :
    |muP q N - mu0 q N| ≤ q.divisors.card * Bw := by
  have h1 : muP q N = ∑ d ∈ q.divisors, (moebius d : ℝ) *
      ∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 :=
    sum_coprime_eq hq (colsP N) (fun n => wCGL (n / N) ^ 2)
  have h2 : mu0 q N = ∑ d ∈ q.divisors, (moebius d : ℝ) * (N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2) := by
    unfold mu0
    rw [totient_div_eq hq, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [h1, h2, ← Finset.sum_sub_distrib]
  calc |∑ d ∈ q.divisors, ((moebius d : ℝ) * ∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 -
        (moebius d : ℝ) * (N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2))|
      ≤ ∑ d ∈ q.divisors, |(moebius d : ℝ) * ∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 -
        (moebius d : ℝ) * (N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, Bw := Finset.sum_le_sum fun d hd => by
        rw [← mul_sub, abs_mul]
        have hμ : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hb := bracket_le hN (Nat.pos_of_mem_divisors hd)
        calc |(moebius d : ℝ)| * |∑ n ∈ (colsP N).filter (fun n => d ∣ n), wCGL (n / N) ^ 2 -
              N / d * ∫ u in (1 : ℝ)..2, wCGL u ^ 2| ≤ 1 * Bw := by gcongr
          _ = Bw := one_mul _
    _ = q.divisors.card * Bw := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `|μ − μ₀| ≤ C_δBq^δ` for `0 < δ ≤ 1` (round 525's divisor bound). -/
theorem muP_sub_mu0_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {q : ℕ} (hq : q ≠ 0) {N : ℝ} (hN : 0 < N) :
    |muP q N - mu0 q N| ≤ LinnikPower.Cdiv δ * Bw * (q : ℝ) ^ δ := by
  have h := muP_sub_mu0_le hq hN
  have hc := LinnikPower.card_divisors_le hδ hδ1 q
  have hB : 0 ≤ Bw := le_trans (by norm_num) two_le_Bw
  calc |muP q N - mu0 q N| ≤ q.divisors.card * Bw := h
    _ ≤ LinnikPower.Cdiv δ * (q : ℝ) ^ δ * Bw := by gcongr
    _ = LinnikPower.Cdiv δ * Bw * (q : ℝ) ^ δ := by ring

/-- **The diagonal terms**: `F(i, i) = μ − μ₀` for `i ∈ R` and `χ` injective on `R`. -/
lemma Fm_diag {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (t : ι → ℝ) {i : ι} (hi : i ∈ R) :
    Fm N χ t i i = ((muP q N - mu0 q N : ℝ) : ℂ) := by
  have h := Em_eq hN hinj t hi hi
  unfold Em at h
  rw [ite_eq_left rfl, gramP_diag hN χ t i] at h
  simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, one_mul] at h
  rw [← h]; push_cast; ring

/-- **The condition "not all equal" removed** (their `Z′`, at one point per character):
`S₃ = Re Σ_{i,j,k∈R} F(i, j)F(j, k)F(k, i) − |R|(μ − μ₀)³`. -/
theorem S3_eq_all {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) {R : Finset ι}
    {χ : ι → DirichletCharacter ℂ q} (hinj : Set.InjOn χ R) (t : ι → ℝ) :
    S3 q N R χ t = (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i).re -
      R.card * (muP q N - mu0 q N) ^ 3 := by
  have hdiag : ∀ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
      (if i = j ∧ j = k then Fm N χ t i j * Fm N χ t j k * Fm N χ t k i else 0) =
      ((muP q N - mu0 q N : ℝ) : ℂ) ^ 3 := by
    intro i hi
    have h1 : ∀ j ∈ R, ∑ k ∈ R, (if i = j ∧ j = k then Fm N χ t i j * Fm N χ t j k * Fm N χ t k i else 0) =
        if i = j then Fm N χ t i i * Fm N χ t i i * Fm N χ t i i else 0 := by
      intro j _
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, Finset.sum_eq_single_of_mem i hi]
        · rw [ite_eq_left ⟨rfl, rfl⟩]
        · intro k _ hk; exact ite_eq_right fun h => hk h.2.symm
      · rw [ite_eq_right hij]; exact Finset.sum_eq_zero fun k _ => ite_eq_right fun h => hij h.1
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq R i, ite_eq_left hi, Fm_diag hN hinj t hi]
    ring
  have hsplit : (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R,
      if i = j ∧ j = k then 0 else Fm N χ t i j * Fm N χ t j k * Fm N χ t k i) =
      (∑ i ∈ R, ∑ j ∈ R, ∑ k ∈ R, Fm N χ t i j * Fm N χ t j k * Fm N χ t k i) -
        ∑ i ∈ R, ((muP q N - mu0 q N : ℝ) : ℂ) ^ 3 := by
    rw [← Finset.sum_congr rfl hdiag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [S3_eq_Fm hN hinj t, hsplit, Complex.sub_re, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [show (R.card : ℂ) * ((muP q N - mu0 q N : ℝ) : ℂ) ^ 3 = ((R.card * (muP q N - mu0 q N) ^ 3 : ℝ) : ℂ) by
    push_cast; ring]
  exact Complex.ofReal_re _

end LinnikCGLDiag

#print axioms LinnikCGLDiag.sum_coprime_eq
#print axioms LinnikCGLDiag.totient_div_eq
#print axioms LinnikCGLDiag.sum_multiples_eq
#print axioms LinnikCGLDiag.bracket_le
#print axioms LinnikCGLDiag.muP_sub_mu0_le
#print axioms LinnikCGLDiag.muP_sub_mu0_le_rpow
#print axioms LinnikCGLDiag.S3_eq_all
