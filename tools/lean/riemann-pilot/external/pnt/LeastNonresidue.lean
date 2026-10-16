/-
# Round 482: the least quadratic nonresidue, and the least primes with `χ(p) = ±1`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For every `A > 12` there is `C` such that every quadratic Dirichlet character `χ ≠ 1` mod `q`
has, for `ε = 1` and for `ε = −1`, a prime `p ∤ q` with `χ(p) = ε` and `p ≤ C(log(q + 2))^A`
(`exists_prime_eq`). With the Legendre symbol, every odd prime `p` has a quadratic nonresidue
`n ≤ C(log p)^A` (`exists_nonsquare_le`), so `n ≤ C_δ p^δ` for every `δ > 0` (`exists_nonsquare_le_rpow`),
Vinogradov's least quadratic nonresidue conjecture. No hypothesis. *(Round 509: every Dirichlet character `χ ≠ 1`
mod `q` has a prime `p ∤ q` with `χ(p) ≠ 1` and `p ≤ C(log(q + 2))^A` (`exists_prime_ne_one`).)*

* `re_psiChi_ge`: if `χ(p) = ε` at every prime `p ≤ x` that does not divide `q`, then
  `ε·Re ψ(x, χ) ≥ ψ(x) − 4√x log x − log q`. The primes give `θ(x) − Σ_{p ∣ q} log p ≥ θ(x) − log q`
  (`sum_log_prime_dvd_le`), and the prime powers at least `−(ψ(x) − θ(x)) ≥ −2√x log x` (Mathlib's
  `Chebyshev.psi_sub_theta_le`).
* `rpow_le_of_forall_eq`: Ankeny's argument. With `ψ(x) ≥ x/4` for `x ≥ 100` (`psi_ge_quarter`, from Mathlib's
  `Chebyshev.psi_ge'`) and round 480's `ChiUniform.psiChi_le_uniform` at `η = 1/12 − 1/A`,
  `|ψ(x, χ)| ≤ C₁ log(q + 2)·x^{1−1/A}`, the hypothesis of `re_psiChi_ge` forces
  `x^{1/A} ≤ 4(C₁ + 11) log(q + 2)`. *(Round 509: for every `χ ≠ 1`, with `psiChi_le_uniform` for every `χ ≠ 1`;
  the same for `rpow_le_of_forall_eq_of`.)*
* `exists_prime_eq`: `rpow_le_of_forall_eq` at `x = max(100, (K log(q + 2))^A) + 1`.
* `exists_prime_ne_one` (round 509): the same at `ε = 1` for every `χ ≠ 1`: if `χ(p) = 1` at every prime
  `p ≤ x` not dividing `q`, then `x^{1/A} ≤ K log(q + 2)`.
* `legendreChar`: Mathlib's `quadraticChar (ZMod p)` as a Dirichlet character mod `p`.
* `rpow_le_of_forall_eq_of`, `exists_prime_eq_of`, `exists_nonsquare_le_of`, `exists_nonsquare_le_rpow_of`
  (round 484): the same from given constants: `K = 4(C₁ + 11)` from `|ψ(x, χ)| ≤ C₁ log(N + 2)·x^{1−1/A}`, then
  `101 + K^A`, then `C₀2^A`, and `C₀(13/δ)^{13}` from `n ≤ C₀(log p)^{13}`.
-/
import Littlewood

set_option lang.lemmaCmd true

open Real Filter Asymptotics ChiPNT

open scoped Chebyshev

namespace LeastNonresidue

/-! ### Chebyshev's functions -/

/-- `ψ(x) ≥ x/4` for `x ≥ 100`, from Mathlib's `Chebyshev.psi_ge'`. -/
lemma psi_ge_quarter {x : ℝ} (hx : 100 ≤ x) : x / 4 ≤ ψ x := by
  have h := Chebyshev.psi_ge' (by linarith : (0 : ℝ) ≤ x)
  have hlog2 := Real.log_two_gt_d9
  have hy : (0 : ℝ) < x + 2 := by linarith
  have hsq : 10 ≤ √(x + 2) := by
    rw [show (10 : ℝ) = √100 by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hss : √(x + 2) * √(x + 2) = x + 2 := Real.mul_self_sqrt hy.le
  have hlog : Real.log (x + 2) ≤ 2 * √(x + 2) := by
    have h1 := Real.log_le_rpow_div hy.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h1
    linarith
  have h10 : 10 * √(x + 2) ≤ x + 2 := by nlinarith
  have h3 : (x - 1) * 0.6931471803 ≤ (x - 1) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2.le (by linarith)
  linarith

/-- `Σ_{p ∣ q} log p ≤ log q` over the primes `p ≤ N` that divide `q ≠ 0`. -/
lemma sum_log_prime_dvd_le {q : ℕ} (hq : q ≠ 0) (N : ℕ) :
    ∑ p ∈ ((Finset.Ioc 0 N).filter Nat.Prime).filter (· ∣ q), Real.log p ≤ Real.log q := by
  have hsub : ((Finset.Ioc 0 N).filter Nat.Prime).filter (· ∣ q) ⊆ q.primeFactors := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.2 ⟨hp.1.2, hp.2, hq⟩
  calc ∑ p ∈ ((Finset.Ioc 0 N).filter Nat.Prime).filter (· ∣ q), Real.log p
      ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦
          Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ Real.log q := by
        apply Real.log_le_log
        · exact Finset.prod_pos fun p hp ↦ by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
          rw [← Nat.cast_prod]
          exact_mod_cast h

/-! ### `ψ(x, χ)` when `χ` is constant on the small primes -/

/-- If `χ(p) = ε`, `ε = ±1`, at every prime `p ≤ x` that does not divide `q`, then
`ε·Re ψ(x, χ) ≥ ψ(x) − 4√x log x − log q`. -/
lemma re_psiChi_ge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {x : ℝ} (hx : 1 ≤ x)
    (h : ∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ¬ p ∣ q → χ p = ε) :
    ψ x - 4 * √x * Real.log x - Real.log q ≤ ε * (psiChi χ x).re := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  set N := ⌊x⌋₊ with hN
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    simpa using (Finset.Icc_add_one_left_eq_Ioc 0 N)
  -- `ε·Re ψ(x, χ)` as a sum over `n ≤ N`
  have hre : ε * (psiChi χ x).re =
      ∑ n ∈ Finset.Ioc 0 N, ε * ((χ n).re * ArithmeticFunction.vonMangoldt n) := by
    rw [psiChi, ← hN, hI, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [Complex.re_mul_ofReal]
  rw [hre, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) Nat.Prime]
  -- the primes
  have hprime : ∑ n ∈ (Finset.Ioc 0 N).filter Nat.Prime,
      ε * ((χ n).re * ArithmeticFunction.vonMangoldt n) =
      θ x - ∑ p ∈ ((Finset.Ioc 0 N).filter Nat.Prime).filter (· ∣ q), Real.log p := by
    have hθ : θ x = ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log p := rfl
    have hsθ := Finset.sum_filter_add_sum_filter_not ((Finset.Ioc 0 N).filter Nat.Prime) (· ∣ q)
      (fun p : ℕ ↦ Real.log p)
    have hsL := Finset.sum_filter_add_sum_filter_not ((Finset.Ioc 0 N).filter Nat.Prime) (· ∣ q)
      (fun n : ℕ ↦ ε * ((χ n).re * ArithmeticFunction.vonMangoldt n))
    have h1 : ∑ n ∈ ((Finset.Ioc 0 N).filter Nat.Prime).filter (· ∣ q),
        ε * ((χ n).re * ArithmeticFunction.vonMangoldt n) = 0 := by
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      simp only [Finset.mem_filter] at hp
      have hnu : ¬ IsUnit (p : ZMod q) := by
        intro hu
        have hcop := (ZMod.isUnit_iff_coprime p q).1 hu
        exact hp.1.2.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hp.2)
      rw [MulChar.map_nonunit _ hnu]
      simp
    have h2 : ∑ n ∈ ((Finset.Ioc 0 N).filter Nat.Prime).filter (fun p ↦ ¬ p ∣ q),
        ε * ((χ n).re * ArithmeticFunction.vonMangoldt n) =
        ∑ p ∈ ((Finset.Ioc 0 N).filter Nat.Prime).filter (fun p ↦ ¬ p ∣ q), Real.log p := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [h p hp.1.2 hp.1.1.2 hp.2, ArithmeticFunction.vonMangoldt_apply_prime hp.1.2,
        Complex.ofReal_re, ← mul_assoc, hεε, one_mul]
    rw [h1, h2, zero_add] at hsL
    rw [hθ, ← hsL]
    linarith
  -- the prime powers `p^k`, `k ≥ 2`
  have hnot : -(ψ x - θ x) ≤ ∑ n ∈ (Finset.Ioc 0 N).filter (fun n ↦ ¬ n.Prime),
      ε * ((χ n).re * ArithmeticFunction.vonMangoldt n) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, ← hN, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n _ ↦ ?_
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hre : |(χ n).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one _ _)
    have habs : |ε * ((χ n).re * ArithmeticFunction.vonMangoldt n)| ≤
        ArithmeticFunction.vonMangoldt n := by
      rw [abs_mul, abs_mul, hεabs, one_mul, abs_of_nonneg hΛ]
      exact mul_le_of_le_one_left hΛ hre
    linarith [neg_abs_le (ε * ((χ n).re * ArithmeticFunction.vonMangoldt n))]
  have hθψ := Chebyshev.psi_sub_theta_le hx
  have hlog := sum_log_prime_dvd_le (NeZero.ne q) N
  rw [hprime]
  linarith

/-! ### The least primes with `χ(p) = ±1` -/

/-- **Ankeny's argument, with its constant.** If `|ψ(x, χ)| ≤ C₁ log(N + 2)·x^{11/12+η}` with
`η = 1/12 − 1/A`, `A > 12`, for every `χ ≠ 1` mod `N` and `x > 1`, and `χ(p) = ε` at every prime
`p ≤ x` not dividing `q`, then `x^{1/A} ≤ 4(C₁ + 11) log(q + 2)`. -/
lemma rpow_le_of_forall_eq_of {A C₁ : ℝ} (hA : 12 < A)
    (hψ : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ x : ℝ, 1 < x → ‖psiChi χ x‖ ≤ C₁ * Real.log (N + 2) * x ^ (11 / 12 + (1 / 12 - 1 / A))) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) → ∀ x : ℝ, 100 ≤ x →
        (∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ¬ p ∣ q → χ p = ε) →
          x ^ (1 / A) ≤ 4 * (C₁ + 11) * Real.log (q + 2) := by
  have hA0 : 0 < A := by linarith
  have hiA : 1 / A < 1 / 12 := by
    rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  have hiA0 : 0 < 1 / A := by positivity
  set η : ℝ := 1 / 12 - 1 / A with hηdef
  have hη : 0 < η := by linarith
  intro q _ χ hχ ε hε x hx hall
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set L : ℝ := Real.log (q + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    linarith
  set e : ℝ := 11 / 12 + η with hedef
  have he : e = 1 - 1 / A := by rw [hedef, hηdef]; ring
  have hxe : 1 ≤ x ^ e := Real.one_le_rpow hx1 (by rw [he]; linarith)
  -- the upper bound
  have hup : ε * (psiChi χ x).re ≤ C₁ * L * x ^ e := by
    have h1 : ε * (psiChi χ x).re ≤ ‖psiChi χ x‖ := by
      calc ε * (psiChi χ x).re ≤ |ε * (psiChi χ x).re| := le_abs_self _
        _ = |(psiChi χ x).re| := by
            rw [abs_mul]; rcases hε with rfl | rfl <;> norm_num
        _ ≤ ‖psiChi χ x‖ := Complex.abs_re_le_norm _
    exact h1.trans (hψ q χ hχ x (by linarith))
  -- the lower bound
  have hlow := re_psiChi_ge χ hε hx1 hall
  have hψx := psi_ge_quarter hx
  -- `√x log x ≤ (12/5)x^e`
  have hsqrt : √x * Real.log x ≤ 12 / 5 * x ^ e := by
    have h1 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 5 / 12)
    have h2 : √x * (x ^ (5 / 12 : ℝ) / (5 / 12)) = 12 / 5 * x ^ (11 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc', mul_comm, ← Real.rpow_add hx0]
      ring_nf
    have h3 : x ^ (11 / 12 : ℝ) ≤ x ^ e :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hedef]; linarith)
    calc √x * Real.log x ≤ √x * (x ^ (5 / 12 : ℝ) / (5 / 12)) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = 12 / 5 * x ^ (11 / 12 : ℝ) := h2
      _ ≤ 12 / 5 * x ^ e := by gcongr
  have hlogq : Real.log q ≤ L * x ^ e := by
    have h1 : Real.log q ≤ L := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exact absurd h0 (NeZero.ne q)
      · exact Real.log_le_log (by exact_mod_cast h0) (by linarith)
    exact h1.trans (le_mul_of_one_le_right (by linarith) hxe)
  -- assemble: `x/4 ≤ (C₁ + 11)·L·x^e`
  have hmain : x / 4 ≤ (C₁ + 11) * L * x ^ e := by
    have h1 : 12 / 5 * x ^ e ≤ 12 / 5 * (L * x ^ e) := by
      have := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ x ^ e) hL
      linarith
    have h2 : (C₁ + 11) * L * x ^ e = C₁ * L * x ^ e + 11 * (L * x ^ e) := by ring
    have h3 : 0 ≤ L * x ^ e := by positivity
    nlinarith
  have hsplit : x = x ^ (1 / A) * x ^ e := by
    rw [← Real.rpow_add hx0, he, show 1 / A + (1 - 1 / A) = (1 : ℝ) by ring, Real.rpow_one]
  have hxe0 : 0 < x ^ e := by positivity
  have h5 : x ^ (1 / A) * x ^ e ≤ (4 * (C₁ + 11) * L) * x ^ e := by
    rw [← hsplit]; linarith
  exact le_of_mul_le_mul_right h5 hxe0

/-- If `χ(p) = ε` at every prime `p ≤ x` not dividing `q`, then `x^{1/A} ≤ K log(q + 2)`, for every
`A > 12`, with `K` depending on `A` only (`rpow_le_of_forall_eq_of`, with
`ChiUniform.psiChi_le_uniform`). -/
lemma rpow_le_of_forall_eq {A : ℝ} (hA : 12 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) → ∀ x : ℝ, 100 ≤ x →
        (∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ¬ p ∣ q → χ p = ε) →
          x ^ (1 / A) ≤ K * Real.log (q + 2) := by
  have hA0 : 0 < A := by linarith
  have hiA : 1 / A < 1 / 12 := by
    rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  obtain ⟨C₁, hC₁, hψ⟩ := ChiUniform.psiChi_le_uniform (η := 1 / 12 - 1 / A) (by linarith)
  exact ⟨4 * (C₁ + 11), by positivity, rpow_le_of_forall_eq_of hA hψ⟩

/-- **The least primes with `χ(p) = ±1`, with the constant.** If `x^{1/A} ≤ K log(q + 2)` whenever `χ(p) = ε`
at every prime `p ≤ x`, `x ≥ 100`, not dividing `q` (`A > 0`, `K > 0`), then every real `χ ≠ 1` mod `q`
has, for `ε = ±1`, a prime `p ∤ q` with `χ(p) = ε` and `p ≤ (101 + K^A)(log(q + 2))^A`. -/
theorem exists_prime_eq_of {A K : ℝ} (hA0 : 0 < A) (hK : 0 < K)
    (hKb : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsQuadratic → χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) → ∀ x : ℝ, 100 ≤ x →
        (∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ¬ p ∣ q → χ p = ε) →
          x ^ (1 / A) ≤ K * Real.log (q + 2)) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsQuadratic → χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) →
        ∃ p : ℕ, p.Prime ∧ ¬ p ∣ q ∧ χ p = ε ∧ (p : ℝ) ≤ (101 + K ^ A) * Real.log (q + 2) ^ A := by
  intro q _ χ hq hχ ε hε
  set L : ℝ := Real.log (q + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    linarith
  have hLA : 1 ≤ L ^ A := Real.one_le_rpow hL hA0.le
  set X : ℝ := max 100 ((K * L) ^ A) + 1 with hXdef
  have hX100 : 100 ≤ X := by
    have := le_max_left (100 : ℝ) ((K * L) ^ A); linarith
  have hXC : X ≤ (101 + K ^ A) * L ^ A := by
    have h1 : max 100 ((K * L) ^ A) ≤ 100 + K ^ A * L ^ A := by
      rw [Real.mul_rpow hK.le (by linarith)]
      have : 0 ≤ K ^ A * L ^ A := by positivity
      exact max_le (by linarith) (by linarith)
    have h2 : 101 + K ^ A * L ^ A ≤ (101 + K ^ A) * L ^ A := by nlinarith
    linarith
  by_contra hcon
  push Not at hcon
  -- every prime `p ≤ X` not dividing `q` has `χ(p) = −ε`
  have hall : ∀ p : ℕ, p.Prime → p ≤ ⌊X⌋₊ → ¬ p ∣ q → χ p = ((-ε : ℝ) : ℂ) := by
    intro p hp hpX hpq
    have hpX' : (p : ℝ) ≤ X := by
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ X)
      have h' : (p : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hpX
      linarith
    have hne : χ p ≠ ε := fun h ↦ (hcon p hp hpq h).not_ge (hpX'.trans hXC)
    have hu : IsUnit (p : ZMod q) :=
      (ZMod.isUnit_iff_coprime p q).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
    have h0 : χ p ≠ 0 := (hu.map χ).ne_zero
    rcases hq (p : ZMod q) with h | h | h
    · exact absurd h h0
    · rcases hε with rfl | rfl
      · exact absurd (by simpa using h) hne
      · simpa using h
    · rcases hε with rfl | rfl
      · simpa using h
      · exact absurd (by simpa using h) hne
  have hε' : -ε = 1 ∨ -ε = -1 := by rcases hε with rfl | rfl <;> norm_num
  have hb := hKb q χ hq hχ hε' X hX100 hall
  -- but `X^{1/A} > K L`
  have hgt : K * L < X ^ (1 / A) := by
    have h1 : (K * L) ^ A < X := by
      have := le_max_right (100 : ℝ) ((K * L) ^ A); linarith
    have h2 : ((K * L) ^ A) ^ (1 / A) = K * L := by
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hA0.ne', Real.rpow_one]
    rw [← h2]
    exact Real.rpow_lt_rpow (by positivity) h1 (by positivity)
  linarith

/-- **The least primes with `χ(p) = ±1`.** For every `A > 12` there is `C` such that every real
Dirichlet character `χ ≠ 1` mod `q` has, for `ε = 1` and for `ε = −1`, a prime `p ∤ q` with `χ(p) = ε`
and `p ≤ C(log(q + 2))^A` (`exists_prime_eq_of`, with `rpow_le_of_forall_eq`). -/
theorem exists_prime_eq {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsQuadratic → χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) →
        ∃ p : ℕ, p.Prime ∧ ¬ p ∣ q ∧ χ p = ε ∧ (p : ℝ) ≤ C * Real.log (q + 2) ^ A := by
  have hA0 : 0 < A := by linarith
  obtain ⟨K, hK, hKb⟩ := rpow_le_of_forall_eq hA
  exact ⟨101 + K ^ A, by positivity, exists_prime_eq_of hA0 hK fun q _ χ _ hχ ↦ hKb q χ hχ⟩

/-- **A prime with `χ(p) ≠ 1`, for every Dirichlet character `χ ≠ 1`.** For every `A > 12` there is `C` such that
every Dirichlet character `χ ≠ 1` mod `q` has a prime `p ∤ q` with `χ(p) ≠ 1` and `p ≤ C(log(q + 2))^A`
(`rpow_le_of_forall_eq` at `ε = 1`, `x = max(100, (K log(q + 2))^A) + 1`). -/
theorem exists_prime_ne_one {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∃ p : ℕ, p.Prime ∧ ¬ p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ C * Real.log (q + 2) ^ A := by
  have hA0 : 0 < A := by linarith
  obtain ⟨K, hK, hKb⟩ := rpow_le_of_forall_eq hA
  refine ⟨101 + K ^ A, by positivity, fun q _ χ hχ ↦ ?_⟩
  set L : ℝ := Real.log (q + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    linarith
  have hLA : 1 ≤ L ^ A := Real.one_le_rpow hL hA0.le
  set X : ℝ := max 100 ((K * L) ^ A) + 1 with hXdef
  have hX100 : 100 ≤ X := by
    have := le_max_left (100 : ℝ) ((K * L) ^ A); linarith
  have hXC : X ≤ (101 + K ^ A) * L ^ A := by
    have h1 : max 100 ((K * L) ^ A) ≤ 100 + K ^ A * L ^ A := by
      rw [Real.mul_rpow hK.le (by linarith)]
      have : 0 ≤ K ^ A * L ^ A := by positivity
      exact max_le (by linarith) (by linarith)
    have h2 : 101 + K ^ A * L ^ A ≤ (101 + K ^ A) * L ^ A := by nlinarith
    linarith
  by_contra hcon
  push Not at hcon
  -- every prime `p ≤ X` not dividing `q` has `χ(p) = 1`
  have hall : ∀ p : ℕ, p.Prime → p ≤ ⌊X⌋₊ → ¬ p ∣ q → χ p = ((1 : ℝ) : ℂ) := by
    intro p hp hpX hpq
    have hpX' : (p : ℝ) ≤ X := by
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ X)
      have h' : (p : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hpX
      linarith
    by_contra hne
    exact (hcon p hp hpq (by simpa using hne)).not_ge (hpX'.trans hXC)
  have hb := hKb q χ hχ (Or.inl rfl) X hX100 hall
  -- but `X^{1/A} > K L`
  have hgt : K * L < X ^ (1 / A) := by
    have h1 : (K * L) ^ A < X := by
      have := le_max_right (100 : ℝ) ((K * L) ^ A); linarith
    have h2 : ((K * L) ^ A) ^ (1 / A) = K * L := by
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hA0.ne', Real.rpow_one]
    rw [← h2]
    exact Real.rpow_lt_rpow (by positivity) h1 (by positivity)
  linarith

/-! ### The least quadratic nonresidue -/

/-- The Legendre symbol mod an odd prime `p`, as a Dirichlet character. -/
noncomputable def legendreChar (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

lemma legendreChar_apply (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    legendreChar p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := rfl

lemma legendreChar_isQuadratic (p : ℕ) [Fact p.Prime] : (legendreChar p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

lemma legendreChar_ne_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : legendreChar p ≠ 1 := by
  intro h
  have hch : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hch
  have ha0 : a ≠ 0 := fun h0 ↦ ha (h0 ▸ IsSquare.zero)
  have h1 : legendreChar p a = 1 := by
    rw [h]; exact MulChar.one_apply (Ne.isUnit ha0)
  rw [legendreChar_apply, quadraticChar_neg_one_iff_not_isSquare.2 ha] at h1
  norm_num at h1

/-- **The least quadratic nonresidue, with the constant.** If every real `χ ≠ 1` mod `q` has a prime
`p ∤ q` with `χ(p) = −1` and `p ≤ C₀(log(q + 2))^A` (`A > 0`, `C₀ > 0`), then every odd prime `p` has a
quadratic nonresidue `n ≤ C₀2^A(log p)^A`. -/
theorem exists_nonsquare_le_of {A C₀ : ℝ} (hA0 : 0 < A) (hC₀ : 0 < C₀)
    (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsQuadratic → χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) →
        ∃ p : ℕ, p.Prime ∧ ¬ p ∣ q ∧ χ p = ε ∧ (p : ℝ) ≤ C₀ * Real.log (q + 2) ^ A) :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C₀ * 2 ^ A * Real.log p ^ A ∧ ¬ IsSquare (n : ZMod p) := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ℓ, hℓ, -, hχℓ, hℓle⟩ := h p (legendreChar p) (legendreChar_isQuadratic p)
    (legendreChar_ne_one p hp2) (ε := -1) (Or.inr rfl)
  refine ⟨ℓ, hℓ.pos, ?_, ?_⟩
  · have hp3 : (3 : ℝ) ≤ p := by
      have := hp.two_le
      have h3 : 3 ≤ p := by omega
      exact_mod_cast h3
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlog : Real.log (p + 2) ≤ 2 * Real.log p := by
      rw [← Real.log_rpow (by linarith)]
      apply Real.log_le_log (by linarith)
      rw [show ((p : ℝ) ^ (2 : ℝ)) = p * p by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
      nlinarith
    have hlogA : Real.log (p + 2) ^ A ≤ 2 ^ A * Real.log p ^ A := by
      rw [← Real.mul_rpow (by norm_num) hlogp]
      exact Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog hA0.le
    calc (ℓ : ℝ) ≤ C₀ * Real.log (p + 2) ^ A := hℓle
      _ ≤ C₀ * (2 ^ A * Real.log p ^ A) := mul_le_mul_of_nonneg_left hlogA hC₀.le
      _ = C₀ * 2 ^ A * Real.log p ^ A := by ring
  · rw [legendreChar_apply] at hχℓ
    have h1 : quadraticChar (ZMod p) (ℓ : ZMod p) = -1 := by exact_mod_cast hχℓ
    exact quadraticChar_neg_one_iff_not_isSquare.1 h1

/-- **Vinogradov's least quadratic nonresidue conjecture, in Ankeny's form.** For every `A > 12`
there is `C` such that every odd prime `p` has a quadratic nonresidue `n ≤ C(log p)^A`
(`exists_nonsquare_le_of`, with `exists_prime_eq`). -/
theorem exists_nonsquare_le {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C * Real.log p ^ A ∧ ¬ IsSquare (n : ZMod p) := by
  have hA0 : 0 < A := by linarith
  obtain ⟨C₀, hC₀, h⟩ := exists_prime_eq hA
  exact ⟨C₀ * 2 ^ A, by positivity, exists_nonsquare_le_of hA0 hC₀ h⟩

/-- **`n(p) ≤ C₀(13/δ)^{13}p^δ` from `n(p) ≤ C₀(log p)^{13}`**, for every `δ > 0`, by
`log p ≤ p^{δ/13}/(δ/13)`. -/
theorem exists_nonsquare_le_rpow_of {C₀ : ℝ} (hC₀ : 0 < C₀)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C₀ * Real.log p ^ (13 : ℝ) ∧ ¬ IsSquare (n : ZMod p))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C₀ * (13 / δ) ^ (13 : ℝ) * (p : ℝ) ^ δ ∧ ¬ IsSquare (n : ZMod p) := by
  intro p hp hp2
  obtain ⟨n, hn0, hnle, hns⟩ := h p hp hp2
  refine ⟨n, hn0, hnle.trans ?_, hns⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
  have h1 : Real.log p ≤ (p : ℝ) ^ (δ / 13) / (δ / 13) :=
    Real.log_le_rpow_div (by linarith) (by positivity)
  have h2 : Real.log p ^ (13 : ℝ) ≤ ((p : ℝ) ^ (δ / 13) / (δ / 13)) ^ (13 : ℝ) :=
    Real.rpow_le_rpow hlogp h1 (by norm_num)
  have h3 : ((p : ℝ) ^ (δ / 13) / (δ / 13)) ^ (13 : ℝ) = (13 / δ) ^ (13 : ℝ) * (p : ℝ) ^ δ := by
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith),
      show δ / 13 * 13 = δ by ring, div_eq_mul_inv, mul_comm,
      show (δ / 13) = (13 / δ)⁻¹ by field_simp, Real.inv_rpow (by positivity), inv_inv]
  calc C₀ * Real.log p ^ (13 : ℝ) ≤ C₀ * ((13 / δ) ^ (13 : ℝ) * (p : ℝ) ^ δ) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hC₀.le
    _ = C₀ * (13 / δ) ^ (13 : ℝ) * (p : ℝ) ^ δ := by ring

/-- **`n(p) ≪_δ p^δ`**: for every `δ > 0` there is `C` such that every odd prime `p` has a quadratic
nonresidue `n ≤ Cp^δ` (`exists_nonsquare_le_rpow_of`, with `exists_nonsquare_le` at `A = 13`). -/
theorem exists_nonsquare_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C * (p : ℝ) ^ δ ∧ ¬ IsSquare (n : ZMod p) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_nonsquare_le (A := 13) (by norm_num)
  exact ⟨C₀ * (13 / δ) ^ (13 : ℝ), by positivity, exists_nonsquare_le_rpow_of hC₀ h hδ⟩

end LeastNonresidue
