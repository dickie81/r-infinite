/-
# Round 520, part 2: Linnik's theorem from a density estimate over the characters mod `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0`, and suppose that for every modulus `q ≥ 1`, `½ ≤ σ ≤ 1` and
`T ≥ 2` at most `C(qT)^{A(1−σ)}(log qT)^B` Dirichlet characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T` (`CharDensity A B C`). Then for every `η > 0` there is `K` such that for every modulus `q ≥ 1` and every
`a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{A+η}` (`linnik_of_charDensity`). The density
estimate is a displayed hypothesis; the zero-free region the argument uses beyond it is round 495's half-plane
`Eis.LFunction_ne_zero_of_re_gt`.

* `totient_mul_SAP`: `φ(q)S(x; q, a) = Σ_χ χ(a⁻¹)S_χ(x)` for `S(x; q, a) = Σ_{n ≡ a} Λ(n)e^{−n/x}` (`SAP`), from
  Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`.
* `re_Sx_one_ge`: `Re S_1(x) ≥ e^{−1}(ψ(x) − ω(q) log x)` for `x ≥ 1` (round 479's
  `PNTProgressions.sum_not_coprime_le`).
* `SAP_le_of_noPrime`: if no prime `p ≤ Y` lies in the class of `a`, then `S(x; q, a) ≤ 2√Y log Y + 96x³e^{−Y/(2x)}`
  (Mathlib's `Chebyshev.psi_sub_theta_le` and `hasSum_zeta_two`).
* `error_le`: `Σ_{χ ≠ 1} |S_χ(x)|` under `CharDensity`. Each character is bounded by `norm_Sx_le` at its level, the
  least `θ_j = min(½ + jδ/2, 11/12)` with no zero in `Re s > θ_j`, `|Im s| < T + 1` (`level`), and the characters of
  level `j + 1` are counted by `CharDensity` at `σ = θ_j` and height `T + 1`.
* `total_le`, `prime_in_class`: at `T = 2 log x + 2` and `Y = 10x log x`, with `q^{A+η₀} ≤ x`, the error terms total
  at most `Ktot x^{1−c₀}`, `c₀ = η₀/(48(A + 1))`, against the main term `e^{−1}x/4` from `ψ(x) ≥ x/4` (round 482's
  `LeastNonresidue.psi_ge_quarter`).
* `linnik_of_charDensity`: `prime_in_class` at `x = X₀q^{A+η₀}`, `η₀ = min(η, 1)/2`.
* `charDensity_twelve`, `linnik_twelve`: the half-plane alone gives `CharDensity 12 0 1` (below `σ = 11/12` at most
  `φ(q) ≤ qT` characters, above it none but the trivial one), so Linnik's theorem holds with exponent `12 + η` with
  no hypothesis.
-/
import LinnikChar
import PNTProgressions
import LeastNonresidue

open Complex Set Real Filter Topology MeasureTheory ArithmeticFunction

noncomputable section

namespace Linnik

open DirichletCharacter InghamDensity

section

/- `ψ` and `θ` are Chebyshev's functions here only; below, `θ` is a level. -/
open scoped Chebyshev

/-! ### The weighted sum over a residue class -/

/-- `S(x; q, a) = Σ_{n ≡ a (q)} Λ(n)e^{−n/x}`. -/
def SAP (q : ℕ) (a : ZMod q) (x : ℝ) : ℝ :=
  ∑' n : ℕ, if (n : ZMod q) = a then Λ n * Real.exp (-((n : ℝ) / x)) else 0

lemma vonMangoldt_le_self (n : ℕ) : Λ n ≤ n :=
  vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))

lemma summable_vonMangoldt_exp {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => Λ n * Real.exp (-((n : ℝ) / x)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 1 (by positivity : 0 < 1 / x)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le)
    (fun n => ?_) h
  have e : -(1 / x) * (n : ℝ) = -((n : ℝ) / x) := by ring
  rw [pow_one, e]
  exact mul_le_mul_of_nonneg_right (vonMangoldt_le_self n) (Real.exp_pos _).le

lemma summable_chi_term (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => χ n * (Λ n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ) := by
  refine Summable.of_norm_bounded (summable_vonMangoldt_exp hx) fun n => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have := DirichletCharacter.norm_le_one χ n
  have : 0 ≤ Λ n * Real.exp (-((n : ℝ) / x)) := mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
  nlinarith [vonMangoldt_nonneg (n := n), Real.exp_pos (-((n : ℝ) / x))]

lemma summable_SAP_term (q : ℕ) (a : ZMod q) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => if (n : ZMod q) = a then Λ n * Real.exp (-((n : ℝ) / x)) else 0 := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_vonMangoldt_exp hx)
  · split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le

/-- **Orthogonality**: `φ(q) S(x; q, a) = Σ_χ χ(a⁻¹) S_χ(x)` for a unit `a`. -/
theorem totient_mul_SAP (q : ℕ) [NeZero q] {a : ZMod q} (ha : IsUnit a) {x : ℝ} (hx : 0 < x) :
    (q.totient : ℂ) * (SAP q a x : ℂ) = ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * Sx χ x := by
  have hs : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      Summable fun n : ℕ => χ a⁻¹ * (χ n * (Λ n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ)) :=
    fun χ _ => (summable_chi_term q χ hx).mul_left _
  have hSAP : (SAP q a x : ℂ) = ∑' n : ℕ,
      ((if (n : ZMod q) = a then Λ n * Real.exp (-((n : ℝ) / x)) else 0 : ℝ) : ℂ) :=
    Complex.ofReal_tsum _
  calc (q.totient : ℂ) * (SAP q a x : ℂ)
      = ∑' n : ℕ, (q.totient : ℂ) *
          ((if (n : ZMod q) = a then Λ n * Real.exp (-((n : ℝ) / x)) else 0 : ℝ) : ℂ) := by
        rw [hSAP, tsum_mul_left]
    _ = ∑' n : ℕ, ∑ χ : DirichletCharacter ℂ q,
          χ a⁻¹ * (χ n * (Λ n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ)) := by
        congr 1
        funext n
        have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
        have hre : ∑ χ : DirichletCharacter ℂ q,
            χ a⁻¹ * (χ n * (Λ n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ)) =
            (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n) * ((Λ n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun χ _ => by ring
        rw [hre, horth]
        by_cases h : (n : ZMod q) = a
        · simp [h]
        · have h' : ¬ a = (n : ZMod q) := fun h' => h h'.symm
          simp [h, h']
    _ = ∑ χ : DirichletCharacter ℂ q, ∑' n : ℕ,
          χ a⁻¹ * (χ n * (Λ n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ)) := Summable.tsum_finsetSum hs
    _ = ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * Sx χ x := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Sx, tsum_mul_left]

/-! ### The trivial character -/

/-- **The trivial character**: `Re S_1(x) ≥ e^{−1}(ψ(x) − ω(q) log x)` for `x ≥ 1`. -/
theorem re_Sx_one_ge (q : ℕ) [NeZero q] {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-1) * (ψ x - q.primeFactors.card * Real.log x) ≤ (Sx (1 : DirichletCharacter ℂ q) x).re := by
  have hx0 : 0 < x := by linarith
  set g : ℕ → ℝ := fun n => if n.Coprime q then Λ n * Real.exp (-((n : ℝ) / x)) else 0 with hg
  have hterm : ∀ n : ℕ, ((1 : DirichletCharacter ℂ q) n * (Λ n : ℂ) * (Real.exp (-((n : ℝ) / x)) : ℂ)) =
      ((g n : ℝ) : ℂ) := by
    intro n
    by_cases hn : n.Coprime q
    · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).2 hn
      show _ = ((if n.Coprime q then Λ n * Real.exp (-((n : ℝ) / x)) else 0 : ℝ) : ℂ)
      rw [ite_eq_left hn, MulChar.one_apply hu]; push_cast; ring
    · have hu : ¬ IsUnit (n : ZMod q) := fun h => hn ((ZMod.isUnit_iff_coprime n q).1 h)
      show _ = ((if n.Coprime q then Λ n * Real.exp (-((n : ℝ) / x)) else 0 : ℝ) : ℂ)
      rw [ite_eq_right hn, MulChar.map_nonunit _ hu]; simp
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_vonMangoldt_exp hx0)
    · simp only [hg]; split_ifs
      · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
      · exact le_rfl
    · simp only [hg]; split_ifs
      · exact le_rfl
      · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg]; split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
    · exact le_rfl
  have hre : (Sx (1 : DirichletCharacter ℂ q) x).re = ∑' n, g n := by
    rw [Sx]
    simp_rw [hterm]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [hre]
  set N := ⌊x⌋₊ with hN
  have hpart : ∑ n ∈ Finset.Icc 1 N, g n ≤ ∑' n, g n := hgs.sum_le_tsum _ fun n _ => hg0 n
  have hlow : ∀ n ∈ Finset.Icc 1 N, Real.exp (-1) * (if n.Coprime q then Λ n else 0) ≤ g n := by
    intro n hn
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 (Finset.mem_Icc.1 hn).2).trans (Nat.floor_le hx0.le)
    have he : Real.exp (-1) ≤ Real.exp (-((n : ℝ) / x)) := Real.exp_le_exp.2 (by
      rw [neg_le_neg_iff, div_le_one hx0]; exact hnx)
    simp only [hg]
    split_ifs
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_left he vonMangoldt_nonneg
    · simp
  have hsplit : ∑ n ∈ Finset.Icc 1 N, (if n.Coprime q then Λ n else 0) =
      ψ x - ∑ n ∈ Finset.Icc 1 N, (if n.Coprime q then 0 else Λ n) := by
    have hI : Finset.Ioc 0 N = Finset.Icc 1 N := by
      simpa using (Finset.Icc_add_one_left_eq_Ioc 0 N).symm
    rw [Chebyshev.psi, ← hN, hI, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hnc := PNTProgressions.sum_not_coprime_le (NeZero.ne q) N
  have hlogN : Real.log N ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hx
    · exact Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le hx0.le)
  have hω : (q.primeFactors.card : ℝ) * Real.log N ≤ q.primeFactors.card * Real.log x :=
    mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg _)
  calc Real.exp (-1) * (ψ x - q.primeFactors.card * Real.log x)
      ≤ Real.exp (-1) * (ψ x - ∑ n ∈ Finset.Icc 1 N, (if n.Coprime q then 0 else Λ n)) := by
        gcongr; linarith
    _ = ∑ n ∈ Finset.Icc 1 N, Real.exp (-1) * (if n.Coprime q then Λ n else 0) := by
        rw [← hsplit, Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, g n := Finset.sum_le_sum hlow
    _ ≤ ∑' n, g n := hpart

/-! ### A class with no small prime -/

/-- `Λ(n)e^{−n/x} ≤ 48x³e^{−Y/(2x)}/n²` for `n > Y ≥ 0`: `Λ(n) ≤ n` and `y³e^{−y} ≤ 3!` at `y = n/(2x)`. -/
lemma tail_term_le {x Y : ℝ} (hx : 0 < x) (hY : 0 ≤ Y) {n : ℕ} (hn : Y < n) :
    Λ n * Real.exp (-((n : ℝ) / x)) ≤ 48 * x ^ 3 * Real.exp (-(Y / (2 * x))) * (1 / (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt hY hn
  have hy : 0 ≤ (n : ℝ) / (2 * x) := by positivity
  have h3 := pow_mul_exp_neg_le 3 hy
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h3
  have hsplit : Real.exp (-((n : ℝ) / x)) = Real.exp (-((n : ℝ) / (2 * x))) * Real.exp (-((n : ℝ) / (2 * x))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hmono : Real.exp (-((n : ℝ) / (2 * x))) ≤ Real.exp (-(Y / (2 * x))) :=
    Real.exp_le_exp.2 (by
      have : Y / (2 * x) ≤ (n : ℝ) / (2 * x) := by gcongr
      linarith)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [mul_one_div, le_div_iff₀ hn2]
  have e : (n : ℝ) ^ 3 = 8 * x ^ 3 * ((n : ℝ) / (2 * x)) ^ 3 := by field_simp; ring
  calc Λ n * Real.exp (-((n : ℝ) / x)) * (n : ℝ) ^ 2 ≤ (n : ℝ) * Real.exp (-((n : ℝ) / x)) * (n : ℝ) ^ 2 := by
        gcongr; exact vonMangoldt_le_self n
    _ = (n : ℝ) ^ 3 * Real.exp (-((n : ℝ) / (2 * x))) * Real.exp (-((n : ℝ) / (2 * x))) := by rw [hsplit]; ring
    _ = 8 * x ^ 3 * (((n : ℝ) / (2 * x)) ^ 3 * Real.exp (-((n : ℝ) / (2 * x)))) *
          Real.exp (-((n : ℝ) / (2 * x))) := by rw [e]; ring
    _ ≤ 8 * x ^ 3 * 6 * Real.exp (-(Y / (2 * x))) := by gcongr
    _ = 48 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by ring

/-- **A class with no prime up to `Y`**: if no prime `p ≤ Y` lies in the class `a`, then
`S(x; q, a) ≤ 2√Y log Y + 96x³e^{−Y/(2x)}`: the prime powers up to `Y` give at most `ψ(Y) − θ(Y)`
(Mathlib's `Chebyshev.psi_sub_theta_le`), and the terms beyond `Y` at most `Σ_n 48x³e^{−Y/(2x)}/n²`. -/
theorem SAP_le_of_noPrime (q : ℕ) (a : ZMod q) {x Y : ℝ} (hx : 0 < x) (hY : 1 ≤ Y)
    (hno : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → (p : ZMod q) ≠ a) :
    SAP q a x ≤ 2 * √Y * Real.log Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by
  set f₁ : ℕ → ℝ := fun n => if n ∈ (Finset.Ioc 0 ⌊Y⌋₊).filter (fun n => ¬ n.Prime) then Λ n else 0 with hf₁
  set f₂ : ℕ → ℝ := fun n => if Y < n then Λ n * Real.exp (-((n : ℝ) / x)) else 0 with hf₂
  set K : ℝ := 48 * x ^ 3 * Real.exp (-(Y / (2 * x))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hf₁s : Summable f₁ := summable_of_ne_finset_zero (s := (Finset.Ioc 0 ⌊Y⌋₊).filter (fun n => ¬ n.Prime))
    fun n hn => by simp only [hf₁]; rw [ite_eq_right hn]
  have hf₂le : ∀ n, f₂ n ≤ K * (1 / (n : ℝ) ^ 2) := by
    intro n
    simp only [hf₂]
    split_ifs with h
    · exact tail_term_le hx (by linarith) h
    · positivity
  have hf₂0 : ∀ n, 0 ≤ f₂ n := fun n => by
    simp only [hf₂]; split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
    · exact le_rfl
  have hzeta : HasSum (fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) (K * (π ^ 2 / 6)) := hasSum_zeta_two.mul_left K
  have hf₂s : Summable f₂ := Summable.of_nonneg_of_le hf₂0 hf₂le hzeta.summable
  have hpt : ∀ n : ℕ, (if (n : ZMod q) = a then Λ n * Real.exp (-((n : ℝ) / x)) else 0) ≤ f₁ n + f₂ n := by
    intro n
    have h10 : 0 ≤ f₁ n := by
      simp only [hf₁]; split_ifs
      · exact vonMangoldt_nonneg
      · exact le_rfl
    by_cases hnY : Y < n
    · have : f₂ n = Λ n * Real.exp (-((n : ℝ) / x)) := by simp only [hf₂]; rw [ite_eq_left hnY]
      split_ifs
      · linarith
      · linarith [hf₂0 n]
    · split_ifs with ha
      · by_cases hΛ : Λ n = 0
        · rw [hΛ, zero_mul]; linarith [hf₂0 n]
        · have hn0 : n ≠ 0 := fun h => hΛ (by rw [h]; exact ArithmeticFunction.map_zero)
          have hnp : ¬ n.Prime := fun hp => hno n hp (not_lt.1 hnY) ha
          have hmem : n ∈ (Finset.Ioc 0 ⌊Y⌋₊).filter (fun n => ¬ n.Prime) := by
            rw [Finset.mem_filter, Finset.mem_Ioc]
            exact ⟨⟨Nat.pos_of_ne_zero hn0, Nat.le_floor (not_lt.1 hnY)⟩, hnp⟩
          have : f₁ n = Λ n := by simp only [hf₁]; rw [ite_eq_left hmem]
          have he : Real.exp (-((n : ℝ) / x)) ≤ 1 := Real.exp_le_one_iff.2 (by
            have : 0 ≤ (n : ℝ) / x := by positivity
            linarith)
          have := mul_le_mul_of_nonneg_left he (vonMangoldt_nonneg (n := n))
          linarith [hf₂0 n]
      · linarith [hf₂0 n]
  have hsum1 : ∑' n, f₁ n = ψ Y - θ Y := by
    rw [tsum_eq_sum (s := (Finset.Ioc 0 ⌊Y⌋₊).filter (fun n => ¬ n.Prime)) fun n hn => by
      simp only [hf₁]; rw [ite_eq_right hn], Chebyshev.psi_sub_theta_eq_sum_not_prime]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hf₁]; rw [ite_eq_left hn]
  have hsum2 : ∑' n, f₂ n ≤ 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by
    refine (Summable.tsum_le_tsum hf₂le hf₂s hzeta.summable).trans ?_
    rw [hzeta.tsum_eq]
    have hpi : π ^ 2 / 6 ≤ 2 := by have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
    calc K * (π ^ 2 / 6) ≤ K * 2 := by gcongr
      _ = 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by rw [hK]; ring
  calc SAP q a x ≤ ∑' n, (f₁ n + f₂ n) :=
        Summable.tsum_le_tsum hpt (summable_SAP_term q a hx) (hf₁s.add hf₂s)
    _ = ∑' n, f₁ n + ∑' n, f₂ n := hf₁s.tsum_add hf₂s
    _ ≤ 2 * √Y * Real.log Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by
        rw [hsum1]; linarith [Chebyshev.psi_sub_theta_le hY]

end

/-! ### The density hypothesis -/

open scoped Classical in
/-- **`CharDensity A B C`**: for every modulus `q ≥ 1`, `½ ≤ σ ≤ 1` and `T ≥ 2`, at most
`C(qT)^{A(1−σ)}(log qT)^B` Dirichlet characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
def CharDensity (A B C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ B

/-! ### The levels -/

/-- The levels `θ_j = min(½ + jδ/2, 11/12)`. -/
def lev (δ : ℝ) (j : ℕ) : ℝ := min (1 / 2 + j * δ / 2) (11 / 12)

/-- The top level `J = ⌈5/(3δ)⌉`, where `θ_J = 11/12`. -/
def nlev (δ : ℝ) : ℕ := ⌈5 / (3 * δ)⌉₊

lemma lev_le (δ : ℝ) (j : ℕ) : lev δ j ≤ 11 / 12 := min_le_right _ _

lemma half_le_lev {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) : 1 / 2 ≤ lev δ j := by
  unfold lev
  have : 0 ≤ (j : ℝ) * δ / 2 := by positivity
  exact le_min (by linarith) (by norm_num)

lemma lev_zero (δ : ℝ) : lev δ 0 = 1 / 2 := by
  unfold lev; norm_num

lemma lev_nlev {δ : ℝ} (hδ : 0 < δ) : lev δ (nlev δ) = 11 / 12 := by
  unfold lev nlev
  apply min_eq_right
  have h := Nat.le_ceil (5 / (3 * δ))
  have h2 : 5 / (3 * δ) * δ = 5 / 3 := by field_simp
  have : (5 / 3 : ℝ) ≤ (⌈5 / (3 * δ)⌉₊ : ℝ) * δ := by
    calc (5 / 3 : ℝ) = 5 / (3 * δ) * δ := h2.symm
      _ ≤ (⌈5 / (3 * δ)⌉₊ : ℝ) * δ := by gcongr
  linarith

lemma lev_succ_le {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) : lev δ (j + 1) ≤ lev δ j + δ / 2 := by
  unfold lev
  push_cast
  rcases le_total (1 / 2 + (j : ℝ) * δ / 2) (11 / 12) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (by linarith)

/-- `L(·, χ)` has no zero in `Re s > θ`, `|Im s| < T + 1`. -/
def ZF {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → |s.im| < T + 1 → LFunction χ s ≠ 0

lemma exists_level {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ j : ℕ, χ = 1 ∨ ZF χ T (lev δ j) := by
  by_cases hχ : χ = 1
  · exact ⟨0, Or.inl hχ⟩
  · refine ⟨nlev δ, Or.inr fun s hs _ => ?_⟩
    rw [lev_nlev hδ] at hs
    exact Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)

open scoped Classical in
/-- The level of `χ`: the least `j` with no zero of `L(·, χ)` in `Re s > θ_j`, `|Im s| < T + 1`. -/
def level {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) : ℕ :=
  Nat.find (exists_level χ T hδ)

lemma level_spec {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ZF χ T (lev δ (level χ T hδ)) := by
  classical
  have h := Nat.find_spec (exists_level χ T hδ)
  rcases h with h | h
  · exact absurd h hχ
  · unfold level; convert h

lemma level_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    level χ T hδ ≤ nlev δ := by
  classical
  unfold level
  refine Nat.find_min' (exists_level χ T hδ) ?_
  by_cases hχ : χ = 1
  · exact Or.inl hχ
  · refine Or.inr fun s hs _ => ?_
    rw [lev_nlev hδ] at hs
    exact Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)

lemma not_ZF_of_level {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (T : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {j : ℕ} (hj : level χ T hδ = j + 1) : ¬ ZF χ T (lev δ j) := by
  classical
  intro h
  have hlt : j < level χ T hδ := by omega
  unfold level at hlt
  exact Nat.find_min (exists_level χ T hδ) hlt (Or.inr h)

/-! ### The characters other than the trivial one -/

/-- The constant of `error_le`: `Σ_{j ≤ J} Mc(θ_j, θ_j + δ) + Mc(11/12, 11/12 + δ)`. -/
def Mstar (δ : ℝ) : ℝ := ∑ j ∈ Finset.range (nlev δ + 1), Mc (lev δ j) (lev δ j + δ) + Mc (11 / 12) (11 / 12 + δ)

lemma Mc_le_Mstar {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) {j : ℕ} (hj : j ≤ nlev δ) :
    Mc (lev δ j) (lev δ j + δ) + Mc (11 / 12) (11 / 12 + δ) ≤ Mstar δ := by
  unfold Mstar
  have hle := lev_le δ j
  gcongr
  refine Finset.single_le_sum (f := fun j => Mc (lev δ j) (lev δ j + δ)) (fun i _ => ?_)
    (Finset.mem_range.2 (by omega))
  exact (Mc_pos (by linarith) (by linarith [lev_le δ i])).le

lemma Mstar_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) : 0 < Mstar δ := by
  have h := Mc_le_Mstar hδ hδ1 (j := 0) (Nat.zero_le _)
  have h1 := Mc_pos (θ := lev δ 0) (θ' := lev δ 0 + δ) (by linarith) (by linarith [lev_le δ 0])
  have h2 := Mc_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
  linarith

/-- **The characters other than the trivial one.** Under `CharDensity A B C`, for
`0 < δ ≤ 1/24`, `T ≥ 1` and `x ≥ 1`, with `ℓ = log(q + 2)`:
`Σ_{χ ≠ 1} |S_χ(x)| ≤ M* ℓ (q x^{1/2+δ} + Σ_{1 ≤ j ≤ J} C(q(T + 1))^{A(1−θ_{j−1})}(log q(T + 1))^B x^{θ_j+δ}
+ 2q x^{11/12+δ}e^{−T/2})`. The characters of level `j ≥ 1` have a zero in `Re s > θ_{j−1}`, `|Im s| < T + 1`, and
`norm_Sx_le` bounds each character at its level. -/
theorem error_le {A B C : ℝ} (hD : CharDensity A B C)
    (q : ℕ) [NeZero q] {δ T x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hT : 1 ≤ T) (hx : 1 ≤ x) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ≤
      Mstar δ * Real.log (q + 2) * ((q : ℝ) * x ^ (1 / 2 + δ) +
        ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) *
          Real.log ((q : ℝ) * (T + 1)) ^ B * x ^ (lev δ (j + 1) + δ) +
        2 * q * x ^ (11 / 12 + δ) * Real.exp (-T / 2)) := by
  classical
  set S := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hS
  set M := Mstar δ with hM
  set ℓ := Real.log (q + 2) with hℓ
  set E := Real.exp (-T / 2) with hE
  have hM0 : 0 < M := Mstar_pos hδ hδ1
  have hℓ0 : 0 ≤ ℓ := by have := one_le_log_add_two q; linarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hx0 : 0 < x := by linarith
  -- each character at its level
  have hchar : ∀ χ ∈ S, ‖Sx χ x‖ ≤ M * ℓ * (x ^ (lev δ (level χ T hδ) + δ) + 2 * x ^ (11 / 12 + δ) * E) := by
    intro χ hχS
    have hχ : χ ≠ 1 := (Finset.mem_filter.1 hχS).2
    have hle := level_le χ T hδ
    refine (norm_Sx_le hχ (half_le_lev hδ.le _) (lev_le δ _) hδ hδ1 (by linarith) hx
      (level_spec hχ T hδ)).trans ?_
    have hb : 0 ≤ x ^ (lev δ (level χ T hδ) + δ) + 2 * x ^ (11 / 12 + δ) * E := by positivity
    have := Mc_le_Mstar hδ hδ1 hle
    gcongr
  -- the fibres
  set F : ℕ → Finset (DirichletCharacter ℂ q) := fun j => S.filter (fun χ => level χ T hδ = j) with hF
  have hmaps : ∀ χ ∈ S, level χ T hδ ∈ Finset.range (nlev δ + 1) :=
    fun χ _ => Finset.mem_range.2 (Nat.lt_succ_of_le (level_le χ T hδ))
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun χ => ‖Sx χ x‖)
  have hcardS : (S.card : ℝ) ≤ q := by
    have h1 : S.card ≤ Fintype.card (DirichletCharacter ℂ q) := Finset.card_le_univ S
    have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]; exact card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    exact_mod_cast h1.trans (h2 ▸ Nat.totient_le q)
  have hcardF : ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) = S.card := by
    have := Finset.card_eq_sum_card_fiberwise hmaps
    exact_mod_cast this.symm
  -- the bound on each fibre
  have hfibre : ∀ j ∈ Finset.range (nlev δ + 1), ∑ χ ∈ F j, ‖Sx χ x‖ ≤
      ((F j).card : ℝ) * (M * ℓ * (x ^ (lev δ j + δ) + 2 * x ^ (11 / 12 + δ) * E)) := by
    intro j _
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun χ hχ => ?_
    have hχ' := Finset.mem_filter.1 hχ
    have := hchar χ hχ'.1
    rwa [hχ'.2] at this
  -- the count of each fibre of level `j + 1`
  have hcount : ∀ j ∈ Finset.range (nlev δ), ((F (j + 1)).card : ℝ) ≤
      C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) * Real.log ((q : ℝ) * (T + 1)) ^ B := by
    intro j _
    refine le_trans ?_ (hD q (lev δ j) (T + 1) (half_le_lev hδ.le j) (by linarith [lev_le δ j]) (by linarith))
    exact_mod_cast Finset.card_le_card fun χ hχ => by
      have hχ' := Finset.mem_filter.1 hχ
      have hnz := not_ZF_of_level T hδ hχ'.2
      simp only [ZF, not_forall, not_not, exists_prop] at hnz
      obtain ⟨s, hs1, hs2, hs3⟩ := hnz
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, s, hs1.le, hs2.le, hs3⟩
  have hF0 : ((F 0).card : ℝ) ≤ q := by
    refine le_trans ?_ hcardS
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  -- assemble
  have hsplit : ∑ j ∈ Finset.range (nlev δ + 1),
      ((F j).card : ℝ) * (M * ℓ * (x ^ (lev δ j + δ) + 2 * x ^ (11 / 12 + δ) * E)) =
      M * ℓ * (∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) * x ^ (lev δ j + δ)) +
        M * ℓ * (2 * x ^ (11 / 12 + δ) * E) * ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hfirst : ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) * x ^ (lev δ j + δ) ≤
      (q : ℝ) * x ^ (1 / 2 + δ) + ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) *
          Real.log ((q : ℝ) * (T + 1)) ^ B * x ^ (lev δ (j + 1) + δ) := by
    rw [Finset.sum_range_succ', lev_zero, add_comm]
    gcongr with j hj
    exact hcount j hj
  calc ∑ χ ∈ S, ‖Sx χ x‖ = ∑ j ∈ Finset.range (nlev δ + 1), ∑ χ ∈ F j, ‖Sx χ x‖ := hfib.symm
    _ ≤ ∑ j ∈ Finset.range (nlev δ + 1),
          ((F j).card : ℝ) * (M * ℓ * (x ^ (lev δ j + δ) + 2 * x ^ (11 / 12 + δ) * E)) :=
        Finset.sum_le_sum hfibre
    _ = M * ℓ * (∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) * x ^ (lev δ j + δ)) +
        M * ℓ * (2 * x ^ (11 / 12 + δ) * E) * ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) := hsplit
    _ ≤ M * ℓ * ((q : ℝ) * x ^ (1 / 2 + δ) + ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^
          (A * (1 - lev δ j)) * Real.log ((q : ℝ) * (T + 1)) ^ B * x ^ (lev δ (j + 1) + δ)) +
        M * ℓ * (2 * x ^ (11 / 12 + δ) * E) * q := by
        rw [hcardF]
        have : 0 ≤ M * ℓ * (2 * x ^ (11 / 12 + δ) * E) := by positivity
        gcongr
    _ = M * ℓ * ((q : ℝ) * x ^ (1 / 2 + δ) + ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^
          (A * (1 - lev δ j)) * Real.log ((q : ℝ) * (T + 1)) ^ B * x ^ (lev δ (j + 1) + δ) +
          2 * q * x ^ (11 / 12 + δ) * E) := by ring

/-! ### The sizes -/

/-- `log y ≤ y^ε/ε` (Mathlib's `Real.log_le_rpow_div`), and the shapes of logarithm used below. -/
lemma log_le_P {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log x ≤ 6 * (x ^ ε / ε) ∧ Real.log (x + 2) ≤ 6 * (x ^ ε / ε) ∧
      2 * Real.log x + 3 ≤ 6 * (x ^ ε / ε) ∧ 1 ≤ 6 * (x ^ ε / ε) := by
  have hx0 : 0 < x := by linarith
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hu : 1 ≤ x ^ ε / ε := by rw [le_div_iff₀ hε]; linarith
  have h1 := Real.log_le_rpow_div hx0.le hε
  have h2 : Real.log (x + 2) ≤ 3 * (x ^ ε / ε) := by
    have := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x + 2) hε
    refine this.trans ?_
    have h3x : (x + 2) ^ ε ≤ (3 * x) ^ ε := Real.rpow_le_rpow (by linarith) (by linarith) hε.le
    have h3 : (3 * x) ^ ε ≤ 3 * x ^ ε := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
      have : (3 : ℝ) ^ ε ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
      rw [Real.rpow_one] at this
      have := Real.rpow_nonneg hx0.le ε
      nlinarith
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hε]; linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The margin of the exponents: `c₀ = η₀/(48(A + 1))`. -/
def c0 (A η₀ : ℝ) : ℝ := η₀ / (48 * (A + 1))

/-- The width of the levels: `δ = η₀/(36(A + 1))`. -/
def dL (A η₀ : ℝ) : ℝ := η₀ / (36 * (A + 1))

/-- The exponent of the logarithms: `R = 2 + A/2 + B`. -/
def Rx (A B : ℝ) : ℝ := 2 + A / 2 + B

/-- `ε = c₀/R`. -/
def epsL (A B η₀ : ℝ) : ℝ := c0 A η₀ / Rx A B

/-- The constant of `total_le`. -/
def Ktot (A B C η₀ : ℝ) : ℝ :=
  (1 + 3 * Mstar (dL A η₀) + Mstar (dL A η₀) * nlev (dL A η₀) * (C * 2 ^ B) + 2 * √10) *
    (6 / epsL A B η₀) ^ Rx A B + 96

lemma dL_pos {A η₀ : ℝ} (hA : 2 ≤ A) (hη0 : 0 < η₀) : 0 < dL A η₀ := by
  unfold dL; exact div_pos hη0 (by linarith)

lemma dL_le {A η₀ : ℝ} (hA : 2 ≤ A) (hη1 : η₀ ≤ 1 / 2) : dL A η₀ ≤ 1 / 24 := by
  unfold dL; rw [div_le_iff₀ (by linarith)]; nlinarith

lemma c0_pos {A η₀ : ℝ} (hA : 2 ≤ A) (hη0 : 0 < η₀) : 0 < c0 A η₀ := by
  unfold c0; exact div_pos hη0 (by linarith)

lemma Rx_ge {A B : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) : 2 ≤ Rx A B := by unfold Rx; linarith

lemma epsL_pos {A B η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hη0 : 0 < η₀) : 0 < epsL A B η₀ := by
  unfold epsL; exact div_pos (c0_pos hA hη0) (by linarith [Rx_ge hA hB])

lemma epsL_le {A B η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) :
    epsL A B η₀ ≤ 1 := by
  unfold epsL c0
  have hR := Rx_ge hA hB
  rw [div_le_one (by linarith), div_le_iff₀ (by linarith)]
  nlinarith

lemma epsL_mul_Rx {A B η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) : epsL A B η₀ * Rx A B = c0 A η₀ := by
  unfold epsL; have := Rx_ge hA hB; field_simp

/-- `1/(A + η₀) + 1/2 + δ ≤ 1 − 2c₀`. -/
lemma exp_two {A η₀ : ℝ} (hA : 2 ≤ A) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) :
    1 / (A + η₀) + 1 / 2 + dL A η₀ ≤ 1 - 2 * c0 A η₀ := by
  unfold dL c0
  have h1 : 1 / (A + η₀) ≤ 1 / (2 + η₀) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have h2 : 1 / (2 + η₀) = 1 / 2 - η₀ / (2 * (2 + η₀)) := by field_simp; ring
  have h3 : η₀ / 5 ≤ η₀ / (2 * (2 + η₀)) := div_le_div_of_nonneg_left hη0.le (by positivity) (by linarith)
  have h4 : η₀ / (36 * (A + 1)) ≤ η₀ / 108 := div_le_div_of_nonneg_left hη0.le (by norm_num) (by linarith)
  have h5 : η₀ / (48 * (A + 1)) ≤ η₀ / 144 := div_le_div_of_nonneg_left hη0.le (by norm_num) (by linarith)
  linarith

/-- `A(1 − θ)/(A + η₀) + θ + 3δ/2 ≤ 1 − 2c₀` for `θ ≤ 11/12`. -/
lemma exp_three {A η₀ : ℝ} (hA : 2 ≤ A) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) {θ : ℝ} (hθ1 : θ ≤ 11 / 12) :
    A * (1 - θ) / (A + η₀) + θ + 3 / 2 * dL A η₀ ≤ 1 - 2 * c0 A η₀ := by
  unfold dL c0
  have hAη : 0 < A + η₀ := by linarith
  have key : A * (1 - θ) / (A + η₀) + θ = 1 - (1 - θ) * η₀ / (A + η₀) := by field_simp; ring
  have h1 : η₀ / (12 * (A + 1)) ≤ (1 - θ) * η₀ / (A + η₀) := by
    rw [div_le_div_iff₀ (by positivity) hAη]
    have h : A + η₀ ≤ (1 - θ) * (12 * (A + 1)) := by nlinarith
    calc η₀ * (A + η₀) ≤ η₀ * ((1 - θ) * (12 * (A + 1))) := mul_le_mul_of_nonneg_left h hη0.le
      _ = (1 - θ) * η₀ * (12 * (A + 1)) := by ring
  have e : 3 / 2 * (η₀ / (36 * (A + 1))) + 2 * (η₀ / (48 * (A + 1))) = η₀ / (12 * (A + 1)) := by
    field_simp; ring
  linarith



/-- One term of the sum over levels: with `q ≤ x^{1/(A+η₀)}`, `T + 1 ≤ P` and `log q(T + 1) ≤ 2P`,
`C(q(T + 1))^{A(1−θ_j)}(log q(T + 1))^B x^{θ_{j+1}+δ} ≤ C2^B P^{A/2+B} x^{1−2c₀}` (`exp_three`). -/
lemma level_term_le {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    {q x P T : ℝ} (hq1 : 1 ≤ q) (hx1 : 1 ≤ x) (hqx : q ≤ x ^ (1 / (A + η₀))) (hP1 : 1 ≤ P)
    (hT : 1 ≤ T + 1) (hTP : T + 1 ≤ P) (hL : Real.log (q * (T + 1)) ≤ 2 * P) (j : ℕ) :
    C * (q * (T + 1)) ^ (A * (1 - lev (dL A η₀) j)) * Real.log (q * (T + 1)) ^ B *
        x ^ (lev (dL A η₀) (j + 1) + dL A η₀) ≤
      C * 2 ^ B * P ^ (A / 2 + B) * x ^ (1 - 2 * c0 A η₀) := by
  set δ := dL A η₀ with hδ
  set θ := lev δ j with hθ
  have hδ0 : 0 < δ := dL_pos hA hη0
  have hθ1 : θ ≤ 11 / 12 := lev_le δ j
  have hθ0 : 1 / 2 ≤ θ := half_le_lev hδ0.le j
  have ha0 : 0 ≤ A * (1 - θ) := by nlinarith
  have haA : A * (1 - θ) ≤ A / 2 := by nlinarith
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T + 1 := by linarith
  have hx0 : 0 < x := by linarith
  have h1 : (q * (T + 1)) ^ (A * (1 - θ)) = q ^ (A * (1 - θ)) * (T + 1) ^ (A * (1 - θ)) :=
    Real.mul_rpow hq0.le hT0.le
  have h2 : q ^ (A * (1 - θ)) ≤ x ^ (A * (1 - θ) / (A + η₀)) := by
    calc q ^ (A * (1 - θ)) ≤ (x ^ (1 / (A + η₀))) ^ (A * (1 - θ)) := Real.rpow_le_rpow hq0.le hqx ha0
      _ = x ^ (A * (1 - θ) / (A + η₀)) := by rw [← Real.rpow_mul hx0.le]; congr 1; ring
  have h3 : (T + 1) ^ (A * (1 - θ)) ≤ P ^ (A / 2) := by
    calc (T + 1) ^ (A * (1 - θ)) ≤ P ^ (A * (1 - θ)) := Real.rpow_le_rpow hT0.le hTP ha0
      _ ≤ P ^ (A / 2) := Real.rpow_le_rpow_of_exponent_le hP1 haA
  have hL0 : 0 ≤ Real.log (q * (T + 1)) := Real.log_nonneg (by nlinarith)
  have h4 : Real.log (q * (T + 1)) ^ B ≤ 2 ^ B * P ^ B := by
    calc Real.log (q * (T + 1)) ^ B ≤ (2 * P) ^ B := Real.rpow_le_rpow hL0 hL hB
      _ = 2 ^ B * P ^ B := Real.mul_rpow (by norm_num) (by linarith)
  have hlev : lev δ (j + 1) ≤ θ + δ / 2 := lev_succ_le hδ0.le j
  have h5 : x ^ (A * (1 - θ) / (A + η₀)) * x ^ (lev δ (j + 1) + δ) ≤ x ^ (1 - 2 * c0 A η₀) := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have := exp_three hA hη0 hη1 hθ1
    linarith
  have hPAB : P ^ (A / 2) * P ^ B = P ^ (A / 2 + B) := (Real.rpow_add (by linarith) _ _).symm
  have hLB : 0 ≤ Real.log (q * (T + 1)) ^ B := Real.rpow_nonneg hL0 B
  have hqa : 0 ≤ q ^ (A * (1 - θ)) := Real.rpow_nonneg hq0.le _
  have hTa : 0 ≤ (T + 1) ^ (A * (1 - θ)) := Real.rpow_nonneg hT0.le _
  have hxl : 0 ≤ x ^ (lev δ (j + 1) + δ) := Real.rpow_nonneg hx0.le _
  have hxa : 0 ≤ x ^ (A * (1 - θ) / (A + η₀)) := Real.rpow_nonneg hx0.le _
  have hPA : 0 ≤ P ^ (A / 2) := Real.rpow_nonneg (by linarith) _
  have hPB : 0 ≤ P ^ B := Real.rpow_nonneg (by linarith) _
  calc C * (q * (T + 1)) ^ (A * (1 - θ)) * Real.log (q * (T + 1)) ^ B * x ^ (lev δ (j + 1) + δ)
      = C * (q ^ (A * (1 - θ)) * (T + 1) ^ (A * (1 - θ))) * Real.log (q * (T + 1)) ^ B *
          x ^ (lev δ (j + 1) + δ) := by rw [h1]
    _ ≤ C * (x ^ (A * (1 - θ) / (A + η₀)) * P ^ (A / 2)) * (2 ^ B * P ^ B) * x ^ (lev δ (j + 1) + δ) := by
        gcongr
    _ = C * 2 ^ B * (P ^ (A / 2) * P ^ B) * (x ^ (A * (1 - θ) / (A + η₀)) * x ^ (lev δ (j + 1) + δ)) := by ring
    _ ≤ C * 2 ^ B * (P ^ (A / 2) * P ^ B) * x ^ (1 - 2 * c0 A η₀) := by gcongr
    _ = C * 2 ^ B * P ^ (A / 2 + B) * x ^ (1 - 2 * c0 A η₀) := by rw [hPAB]

/-- `e^{−(2 log x + 2)/2} ≤ 1/x` and `e^{−(10x log x)/(2x)} = x^{−5}`. -/
lemma exp_T_le {x : ℝ} (hx : 0 < x) : Real.exp (-(2 * Real.log x + 2) / 2) ≤ x⁻¹ := by
  have e : -(2 * Real.log x + 2) / 2 = -Real.log x + -1 := by ring
  rw [e, Real.exp_add, Real.exp_neg, Real.exp_log hx]
  have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have : 0 < x⁻¹ := inv_pos.2 hx
  nlinarith

lemma exp_Y_eq {x : ℝ} (hx : 0 < x) : Real.exp (-(10 * x * Real.log x / (2 * x))) = (x ^ 5)⁻¹ := by
  have e : -(10 * x * Real.log x / (2 * x)) = -Real.log (x ^ 5) := by
    rw [Real.log_pow]; field_simp; push_cast; ring
  rw [e, Real.exp_neg, Real.exp_log (by positivity)]

/-- The term of the trivial character's prime powers: `e^{−1}q log x ≤ P x^{1−2c}`. -/
lemma size_one {q x P r : ℝ} (hq0 : 0 ≤ q) (hx1 : 1 ≤ x) (hqr : q ≤ x ^ r) (hlog : Real.log x ≤ P) :
    Real.exp (-1) * (q * Real.log x) ≤ P * x ^ r := by
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have : 0 ≤ q * Real.log x := mul_nonneg hq0 hl0
  calc Real.exp (-1) * (q * Real.log x) ≤ 1 * (q * Real.log x) := by gcongr
    _ = q * Real.log x := one_mul _
    _ ≤ x ^ r * P := mul_le_mul hqr hlog hl0 (Real.rpow_nonneg (by linarith) _)
    _ = P * x ^ r := mul_comm _ _

/-- The characters of level `0`, and the horizontal tails: `q x^{1/2+δ} ≤ x^{1−2c₀}` and
`2q x^{11/12+δ} e^{−(2 log x + 2)/2} ≤ 2x^{1−2c₀}`. -/
lemma size_two {A η₀ q x : ℝ} (hA : 2 ≤ A) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) (hx1 : 1 ≤ x)
    (hqu : q ≤ x ^ (1 / (A + η₀))) :
    q * x ^ (1 / 2 + dL A η₀) ≤ x ^ (1 - 2 * c0 A η₀) ∧
      2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2) ≤ 2 * x ^ (1 - 2 * c0 A η₀) := by
  have hx0 : 0 < x := by linarith
  have h2 := exp_two hA hη0 hη1
  have hδ1 := dL_le hA hη1
  have hδ0 := dL_pos hA hη0
  have hc0 := c0_pos hA hη0
  refine ⟨?_, ?_⟩
  · calc q * x ^ (1 / 2 + dL A η₀) ≤ x ^ (1 / (A + η₀)) * x ^ (1 / 2 + dL A η₀) := by gcongr
      _ = x ^ (1 / (A + η₀) + (1 / 2 + dL A η₀)) := (Real.rpow_add hx0 _ _).symm
      _ ≤ x ^ (1 - 2 * c0 A η₀) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · have hE := exp_T_le hx0
    have hqc : q ≤ x ^ (1 - 2 * c0 A η₀) := by
      refine hqu.trans (Real.rpow_le_rpow_of_exponent_le hx1 ?_)
      have : 1 / (A + η₀) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hx11 : x ^ (11 / 12 + dL A η₀) ≤ x := by
      calc x ^ (11 / 12 + dL A η₀) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        _ = x := Real.rpow_one x
    have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
    have h0 : 0 ≤ Real.exp (-(2 * Real.log x + 2) / 2) := (Real.exp_pos _).le
    have : 0 ≤ x ^ (11 / 12 + dL A η₀) := Real.rpow_nonneg hx0.le _
    calc 2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2)
        ≤ 2 * x ^ (1 - 2 * c0 A η₀) * x * x⁻¹ := by gcongr
      _ = 2 * x ^ (1 - 2 * c0 A η₀) := by rw [mul_assoc (2 * x ^ (1 - 2 * c0 A η₀)), hxinv, mul_one]

/-- `log(10x log x) ≤ 2 log x + 3` and `√(10x log x) ≤ √10 √x √(log x)`, for `x ≥ 3`. -/
lemma size_Y {x : ℝ} (hx : 3 ≤ x) :
    Real.log (10 * x * Real.log x) ≤ 2 * Real.log x + 3 ∧
      √(10 * x * Real.log x) = √10 * √x * √(Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlogx1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hY0 : 0 < 10 * x * Real.log x := by positivity
  refine ⟨?_, ?_⟩
  · have hlx : Real.log x ≤ x := Real.log_le_self hx0.le
    have h10 : Real.log 10 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have he := Real.exp_one_gt_d9
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h1 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
      have h2 : (10 : ℝ) < 2.7182818283 ^ 3 := by norm_num
      rw [h3]; linarith
    calc Real.log (10 * x * Real.log x) ≤ Real.log (10 * x ^ 2) :=
          Real.log_le_log hY0 (by nlinarith)
      _ = Real.log 10 + 2 * Real.log x := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 2 * Real.log x + 3 := by linarith
  · rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]

/-- The prime powers and the tail of a class with no small prime:
`q(2√Y log Y + 96x³e^{−Y/(2x)}) ≤ 2√10 P² x^{1−2c₀} + 96`, `Y = 10x log x`. -/
lemma size_five {A η₀ q x P : ℝ} (hA : 2 ≤ A) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) (hq0 : 0 ≤ q)
    (hx : 3 ≤ x) (hqu : q ≤ x ^ (1 / (A + η₀))) (hqx : q ≤ x) (hP1 : 1 ≤ P) (hTP : 2 * Real.log x + 3 ≤ P) :
    q * (2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) +
      96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x)))) ≤
      2 * √10 * P ^ 2 * x ^ (1 - 2 * c0 A η₀) + 96 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨hlY, hsqY⟩ := size_Y hx
  rw [exp_Y_eq hx0, mul_add]
  have hs1 : √(Real.log x) ≤ P := by
    have : √(Real.log x) ≤ Real.log x := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  have hqs : q * √x ≤ x ^ (1 - 2 * c0 A η₀) := by
    calc q * √x ≤ x ^ (1 / (A + η₀)) * x ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]; gcongr
      _ = x ^ (1 / (A + η₀) + 1 / 2) := (Real.rpow_add hx0 _ _).symm
      _ ≤ x ^ (1 - 2 * c0 A η₀) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [exp_two hA hη0 hη1, dL_pos hA hη0])
  have hlY0 : 0 ≤ Real.log (10 * x * Real.log x) := Real.log_nonneg (by nlinarith)
  have h1 : q * (2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x)) ≤
      2 * √10 * P ^ 2 * x ^ (1 - 2 * c0 A η₀) := by
    rw [hsqY]
    calc q * (2 * (√10 * √x * √(Real.log x)) * Real.log (10 * x * Real.log x))
        ≤ q * (2 * (√10 * √x * P) * P) := by gcongr; linarith
      _ = 2 * √10 * P ^ 2 * (q * √x) := by ring
      _ ≤ 2 * √10 * P ^ 2 * x ^ (1 - 2 * c0 A η₀) := by gcongr
  have h2 : q * (96 * x ^ 3 * (x ^ 5)⁻¹) ≤ 96 := by
    have hx5 : x ^ 3 * (x ^ 5)⁻¹ = (x ^ 2)⁻¹ := by field_simp
    have hqx2 : q ≤ x ^ 2 := hqx.trans (by nlinarith)
    calc q * (96 * x ^ 3 * (x ^ 5)⁻¹) = 96 * (q * (x ^ 2)⁻¹) := by rw [mul_assoc 96, hx5]; ring
      _ ≤ 96 * 1 := by
          gcongr
          rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact hqx2
      _ = 96 := mul_one _
  linarith

/-- The powers of `P = 6x^ε/ε`: the sum of the terms is at most `Ktot x^{1−c₀}`. -/
lemma size_final {A B C η₀ x M J : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (hx1 : 1 ≤ x) (hM : M = Mstar (dL A η₀)) (hJ : J = nlev (dL A η₀)) :
    6 * (x ^ epsL A B η₀ / epsL A B η₀) * x ^ (1 - 2 * c0 A η₀) +
      M * (6 * (x ^ epsL A B η₀ / epsL A B η₀)) * (x ^ (1 - 2 * c0 A η₀) +
        J * (C * 2 ^ B * (6 * (x ^ epsL A B η₀ / epsL A B η₀)) ^ (A / 2 + B) * x ^ (1 - 2 * c0 A η₀)) +
        2 * x ^ (1 - 2 * c0 A η₀)) +
      (2 * √10 * (6 * (x ^ epsL A B η₀ / epsL A B η₀)) ^ 2 * x ^ (1 - 2 * c0 A η₀) + 96) ≤
    Ktot A B C η₀ * x ^ (1 - c0 A η₀) := by
  set ε := epsL A B η₀ with hε
  set c := c0 A η₀ with hc
  set R := Rx A B with hR
  set P := 6 * (x ^ ε / ε) with hP
  have hx0 : 0 < x := by linarith
  have hε0 : 0 < ε := epsL_pos hA hB hη0
  have hε1 : ε ≤ 1 := epsL_le hA hB hη0 hη1
  have hc0 : 0 < c := c0_pos hA hη0
  have hc1 : c ≤ 1 / 96 := by
    rw [hc]; unfold c0; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hR2 : 2 ≤ R := Rx_ge hA hB
  have hM0 : 0 < M := hM ▸ Mstar_pos (dL_pos hA hη0) (dL_le hA hη1)
  have hJ0 : (0 : ℝ) ≤ J := hJ ▸ Nat.cast_nonneg _
  have hP1 : 1 ≤ P := (log_le_P hx1 hε0 hε1).2.2.2
  have hP0 : 0 < P := by linarith
  have hPR : ∀ r : ℝ, r ≤ R → P ^ r ≤ P ^ R := fun r hr => Real.rpow_le_rpow_of_exponent_le hP1 hr
  have hP1R : P ≤ P ^ R := by simpa using hPR 1 (by linarith)
  have hP2R : P ^ 2 ≤ P ^ R := by
    have := hPR 2 hR2
    rwa [Real.rpow_two] at this
  have hPABR : P * P ^ (A / 2 + B) ≤ P ^ R := by
    rw [← Real.rpow_one_add' hP0.le (by linarith)]
    exact hPR _ (by rw [hR]; unfold Rx; linarith)
  have hPRx : P ^ R = (6 / ε) ^ R * x ^ c := by
    rw [hP, show 6 * (x ^ ε / ε) = 6 / ε * x ^ ε by ring, Real.mul_rpow (by positivity)
      (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le, hR, hε, epsL_mul_Rx hA hB]
  have hxcx : x ^ c * x ^ (1 - 2 * c) = x ^ (1 - c) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hx1c : 1 ≤ x ^ (1 - c) := Real.one_le_rpow hx1 (by linarith)
  have hxc : 0 ≤ x ^ (1 - 2 * c) := Real.rpow_nonneg hx0.le _
  have hC2 : 0 ≤ C * 2 ^ B := mul_nonneg hC (Real.rpow_nonneg (by norm_num) B)
  have hs10 : 0 ≤ 2 * √10 := by positivity
  have hMJ : 0 ≤ M * J * (C * 2 ^ B) := by positivity
  have e1 : P * x ^ (1 - 2 * c) + M * P * (x ^ (1 - 2 * c) + J * (C * 2 ^ B * P ^ (A / 2 + B) *
      x ^ (1 - 2 * c)) + 2 * x ^ (1 - 2 * c)) + (2 * √10 * P ^ 2 * x ^ (1 - 2 * c) + 96) =
      ((1 + 3 * M) * P + M * J * (C * 2 ^ B) * (P * P ^ (A / 2 + B)) + 2 * √10 * P ^ 2) *
        x ^ (1 - 2 * c) + 96 := by ring
  have e2 : ((1 + 3 * M) * P + M * J * (C * 2 ^ B) * (P * P ^ (A / 2 + B)) + 2 * √10 * P ^ 2) ≤
      (1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10) * P ^ R := by
    nlinarith [mul_le_mul_of_nonneg_left hP1R (by linarith : (0 : ℝ) ≤ 1 + 3 * M),
      mul_le_mul_of_nonneg_left hPABR hMJ, mul_le_mul_of_nonneg_left hP2R hs10]
  have hK : Ktot A B C η₀ = (1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10) * (6 / ε) ^ R + 96 := by
    rw [Ktot, hM, hJ]
  rw [e1, hK]
  have h6 : 0 ≤ (6 / ε) ^ R := Real.rpow_nonneg (by positivity) _
  have hcoef : 0 ≤ 1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10 := by positivity
  calc ((1 + 3 * M) * P + M * J * (C * 2 ^ B) * (P * P ^ (A / 2 + B)) + 2 * √10 * P ^ 2) *
        x ^ (1 - 2 * c) + 96
      ≤ (1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10) * P ^ R * x ^ (1 - 2 * c) + 96 := by gcongr
    _ = (1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10) * (6 / ε) ^ R * (x ^ c * x ^ (1 - 2 * c)) + 96 := by
        rw [hPRx]; ring
    _ = (1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10) * (6 / ε) ^ R * x ^ (1 - c) + 96 := by rw [hxcx]
    _ ≤ (1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10) * (6 / ε) ^ R * x ^ (1 - c) + 96 * x ^ (1 - c) := by
        linarith
    _ = ((1 + 3 * M + M * J * (C * 2 ^ B) + 2 * √10) * (6 / ε) ^ R + 96) * x ^ (1 - c) := by ring

/-- **The sizes.** For `x ≥ 3` and `q^{A+η₀} ≤ x`, with `T = 2 log x + 2` and `Y = 10x log x`, the error terms
total at most `Ktot x^{1−c₀}`: `e^{−1}q log x`, the bound of `error_le`, and
`q(2√Y log Y + 96x³e^{−Y/(2x)})`. -/
theorem total_le {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (q : ℕ) [NeZero q] {x : ℝ} (hx : 3 ≤ x) (hqx : (q : ℝ) ^ (A + η₀) ≤ x) :
    Real.exp (-1) * (q * Real.log x) +
      Mstar (dL A η₀) * Real.log (q + 2) * ((q : ℝ) * x ^ (1 / 2 + dL A η₀) +
        ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
          (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
            x ^ (lev (dL A η₀) (j + 1) + dL A η₀) +
        2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2)) +
      q * (2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) +
        96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x)))) ≤
    Ktot A B C η₀ * x ^ (1 - c0 A η₀) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hε0 : 0 < epsL A B η₀ := epsL_pos hA hB hη0
  have hε1 : epsL A B η₀ ≤ 1 := epsL_le hA hB hη0 hη1
  have hc0 : 0 < c0 A η₀ := c0_pos hA hη0
  have hc1 : c0 A η₀ ≤ 1 / 96 := by unfold c0; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hδ0 : 0 < dL A η₀ := dL_pos hA hη0
  have hδ1 : dL A η₀ ≤ 1 / 24 := dL_le hA hη1
  obtain ⟨hPlog, hPlog2, hPT, hP1⟩ := log_le_P hx1 hε0 hε1
  have hfin := size_final hA hB hC hη0 hη1 hx1 (M := Mstar (dL A η₀)) (J := nlev (dL A η₀)) rfl rfl
  obtain ⟨P, hP⟩ : ∃ P, 6 * (x ^ epsL A B η₀ / epsL A B η₀) = P := ⟨_, rfl⟩
  rw [hP] at hPlog hPlog2 hPT hP1 hfin
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hAη : 0 < A + η₀ := by linarith
  have hqu : (q : ℝ) ≤ x ^ (1 / (A + η₀)) := by
    calc (q : ℝ) = ((q : ℝ) ^ (A + η₀)) ^ (1 / (A + η₀)) := by
          rw [← Real.rpow_mul hq0.le, mul_one_div_cancel hAη.ne', Real.rpow_one]
      _ ≤ x ^ (1 / (A + η₀)) := Real.rpow_le_rpow (by positivity) hqx (by positivity)
  have huh : x ^ (1 / (A + η₀)) ≤ x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hhalf : x ^ (1 / 2 : ℝ) ≤ x ^ (1 - 2 * c0 A η₀) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx12 : x ^ (1 / 2 : ℝ) ≤ x := by
    calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hqx' : (q : ℝ) ≤ x := hqu.trans (huh.trans hx12)
  have hlq : Real.log (q + 2) ≤ P := (Real.log_le_log (by positivity) (by linarith)).trans hPlog2
  have hlq0 : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
  -- the five pieces
  have hT1 := size_one hq0.le hx1 (hqu.trans (huh.trans hhalf)) hPlog
  obtain ⟨hT2, hT4⟩ := size_two hA hη0 hη1 hx1 hqu
  have hT5 := size_five hA hη0 hη1 hq0.le hx hqu hqx' hP1 hPT
  have hTt1 : 1 ≤ 2 * Real.log x + 2 + 1 := by linarith [Real.log_nonneg hx1]
  have hTP : 2 * Real.log x + 2 + 1 ≤ P := by linarith
  have hL : Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ≤ 2 * P := by
    rw [Real.log_mul hq0.ne' (by linarith)]
    have h1 : Real.log q ≤ Real.log x := Real.log_le_log hq0 hqx'
    have h2 : Real.log (2 * Real.log x + 2 + 1) ≤ 2 * Real.log x + 2 + 1 :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    linarith
  have hT3 : ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
      (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
        x ^ (lev (dL A η₀) (j + 1) + dL A η₀) ≤
      nlev (dL A η₀) * (C * 2 ^ B * P ^ (A / 2 + B) * x ^ (1 - 2 * c0 A η₀)) := by
    have := Finset.sum_le_card_nsmul (Finset.range (nlev (dL A η₀)))
      (fun j => C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ (A * (1 - lev (dL A η₀) j)) *
        Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B * x ^ (lev (dL A η₀) (j + 1) + dL A η₀))
      (C * 2 ^ B * P ^ (A / 2 + B) * x ^ (1 - 2 * c0 A η₀))
      (fun j _ => level_term_le hA hB hC hη0 hη1 hq1 hx1 hqu hP1 hTt1 hTP hL j)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have hin : 0 ≤ (q : ℝ) * x ^ (1 / 2 + dL A η₀) +
      ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
        (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
          x ^ (lev (dL A η₀) (j + 1) + dL A η₀) +
      2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2) := by
    have h1 : 0 ≤ ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
        (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
          x ^ (lev (dL A η₀) (j + 1) + dL A η₀) := by
      refine Finset.sum_nonneg fun j _ => ?_
      have hL0 : 0 ≤ Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) := Real.log_nonneg (by nlinarith)
      have := Real.rpow_nonneg hL0 B
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ q * (2 * Real.log x + 2 + 1) by positivity)
        (A * (1 - lev (dL A η₀) j))
      have := Real.rpow_nonneg hx0.le (lev (dL A η₀) (j + 1) + dL A η₀)
      positivity
    have h2 : 0 ≤ (q : ℝ) * x ^ (1 / 2 + dL A η₀) := by positivity
    have h3 : 0 ≤ 2 * (q : ℝ) * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2) := by
      positivity
    linarith
  have hM0 : 0 < Mstar (dL A η₀) := Mstar_pos hδ0 hδ1
  have hErr : Mstar (dL A η₀) * Real.log (q + 2) * ((q : ℝ) * x ^ (1 / 2 + dL A η₀) +
      ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
        (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
          x ^ (lev (dL A η₀) (j + 1) + dL A η₀) +
      2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2)) ≤
      Mstar (dL A η₀) * P * (x ^ (1 - 2 * c0 A η₀) +
        nlev (dL A η₀) * (C * 2 ^ B * P ^ (A / 2 + B) * x ^ (1 - 2 * c0 A η₀)) +
        2 * x ^ (1 - 2 * c0 A η₀)) := by
    calc _ ≤ Mstar (dL A η₀) * P * ((q : ℝ) * x ^ (1 / 2 + dL A η₀) +
          ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
            (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
              x ^ (lev (dL A η₀) (j + 1) + dL A η₀) +
          2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2)) := by gcongr
      _ ≤ _ := by gcongr
  linarith [hT1, hErr, hT5, hfin]

/-! ### The prime in the class -/

/-- `ω(q) ≤ q`. -/
lemma card_primeFactors_le (q : ℕ) : (q.primeFactors.card : ℝ) ≤ q := by
  have h : q.primeFactors ⊆ Finset.Icc 1 q := fun p hp => by
    have hp' := Nat.mem_primeFactors.1 hp
    exact Finset.mem_Icc.2 ⟨hp'.1.one_lt.le, Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1⟩
  have := Finset.card_le_card h
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  exact_mod_cast this

lemma Ktot_nonneg {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) :
    0 ≤ Ktot A B C η₀ := by
  have hM := (Mstar_pos (dL_pos hA hη0) (dL_le hA hη1)).le
  have hε := epsL_pos hA hB hη0
  have h6 : 0 ≤ (6 / epsL A B η₀) ^ Rx A B := Real.rpow_nonneg (by positivity) _
  have hC2 : 0 ≤ C * 2 ^ B := mul_nonneg hC (Real.rpow_nonneg (by norm_num) B)
  unfold Ktot
  positivity

/-- **A prime in the class up to `10x log x`.** Let `A ≥ 2`, `B ≥ 0`, `C ≥ 0`, `CharDensity A B C`,
`0 < η₀ ≤ 1/2`, and `a` prime to `q`. If `x ≥ 100`, `q^{A+η₀} ≤ x` and `x^{c₀} ≥ 4e Ktot + 1`, the class of `a`
mod `q` holds a prime `p ≤ 10x log x`. Otherwise orthogonality (`totient_mul_SAP`), the trivial character
(`re_Sx_one_ge`, Chebyshev's `ψ(x) ≥ x/4`), the other characters (`error_le`) and the class bound
(`SAP_le_of_noPrime`) give `e^{−1}x/4 ≤ Ktot x^{1−c₀}` (`total_le`). -/
theorem prime_in_class {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) (q : ℕ) [NeZero q] {a : ℕ} (ha : a.Coprime q) {x : ℝ}
    (hx100 : 100 ≤ x) (hqx : (q : ℝ) ^ (A + η₀) ≤ x)
    (hbig : 4 * Real.exp 1 * Ktot A B C η₀ + 1 ≤ x ^ c0 A η₀) :
    ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = (a : ZMod q) ∧ (p : ℝ) ≤ 10 * x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlogx1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hlogx : 0 ≤ Real.log x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hY1 : 1 ≤ 10 * x * Real.log x := by nlinarith
  by_contra hno
  push Not at hno
  have hno' : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ (a : ZMod q) :=
    fun p hp hpY heq => lt_irrefl _ ((hno p hp heq).trans_le hpY)
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have horth := totient_mul_SAP q hu hx0
  have hSAP := SAP_le_of_noPrime q (a : ZMod q) hx0 hY1 hno'
  have hSAP0 : 0 ≤ SAP q a x := tsum_nonneg fun n => by
    split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
    · exact le_rfl
  have hφ : ((q.totient : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  -- the real part of orthogonality
  have hre : (q.totient : ℝ) * SAP q a x =
      (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * Sx χ x).re := by
    rw [← horth]; simp
  have hinv : IsUnit ((a : ZMod q)⁻¹) := IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit _ hu)
  have hsplit : ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * Sx χ x =
      Sx (1 : DirichletCharacter ℂ q) x + ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        χ (a : ZMod q)⁻¹ * Sx χ x := by
    rw [Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), MulChar.one_apply hinv, one_mul]
  have hrest : -∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ≤
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        χ (a : ZMod q)⁻¹ * Sx χ x).re := by
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun χ _ => ?_
    have h1 : |(χ (a : ZMod q)⁻¹ * Sx χ x).re| ≤ ‖χ (a : ZMod q)⁻¹ * Sx χ x‖ := Complex.abs_re_le_norm _
    have h2 : ‖χ (a : ZMod q)⁻¹ * Sx χ x‖ ≤ ‖Sx χ x‖ := by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
    have h3 := neg_abs_le (χ (a : ZMod q)⁻¹ * Sx χ x).re
    linarith
  -- the trivial character
  have hone := re_Sx_one_ge q (by linarith : (1 : ℝ) ≤ x)
  have hψ := LeastNonresidue.psi_ge_quarter hx100
  have hω := card_primeFactors_le q
  have hone' : Real.exp (-1) * (x / 4 - q * Real.log x) ≤ (Sx (1 : DirichletCharacter ℂ q) x).re := by
    refine le_trans ?_ hone
    have : (q.primeFactors.card : ℝ) * Real.log x ≤ q * Real.log x := mul_le_mul_of_nonneg_right hω hlogx
    gcongr
  -- the other characters
  have herr := error_le hD q (dL_pos hA hη0) (dL_le hA hη1) (T := 2 * Real.log x + 2) (by linarith)
    (by linarith : (1 : ℝ) ≤ x)
  have htot := total_le hA hB hC hη0 hη1 q (by linarith : (3 : ℝ) ≤ x) hqx
  have hlow : (q.totient : ℝ) * SAP q a x ≤ q * SAP q a x := mul_le_mul_of_nonneg_right hφ hSAP0
  have hhigh := mul_le_mul_of_nonneg_left hSAP hq0.le
  have hsum : (Sx (1 : DirichletCharacter ℂ q) x).re -
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ≤
      (q.totient : ℝ) * SAP q a x := by
    rw [hre, hsplit, Complex.add_re]; linarith only [hrest]
  have hmain : Real.exp (-1) * (x / 4) - Real.exp (-1) * (q * Real.log x) -
      Mstar (dL A η₀) * Real.log (q + 2) * ((q : ℝ) * x ^ (1 / 2 + dL A η₀) +
        ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
          (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
            x ^ (lev (dL A η₀) (j + 1) + dL A η₀) +
        2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2)) ≤
      (q.totient : ℝ) * SAP q a x := by
    rw [← mul_sub]; linarith only [hone', herr, hsum]
  have hfinal : Real.exp (-1) * (x / 4) ≤ Ktot A B C η₀ * x ^ (1 - c0 A η₀) :=
    by linarith only [hmain, hlow, hhigh, htot]
  -- `x^{c₀} > 4e Ktot` contradicts it
  have hsplit2 : x ^ (1 - c0 A η₀) * x ^ c0 A η₀ = x := by
    rw [← Real.rpow_add hx0]; simp
  have h1 := mul_le_mul_of_nonneg_right hfinal
    (by positivity : (0 : ℝ) ≤ 4 * Real.exp 1 * x ^ c0 A η₀)
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have h2 : Real.exp (-1) * (x / 4) * (4 * Real.exp 1 * x ^ c0 A η₀) = x * x ^ c0 A η₀ := by
    calc _ = (Real.exp (-1) * Real.exp 1) * x * x ^ c0 A η₀ := by ring
      _ = x * x ^ c0 A η₀ := by rw [he, one_mul]
  have h3 : Ktot A B C η₀ * x ^ (1 - c0 A η₀) * (4 * Real.exp 1 * x ^ c0 A η₀) =
      4 * Real.exp 1 * Ktot A B C η₀ * x := by
    calc _ = 4 * Real.exp 1 * Ktot A B C η₀ * (x ^ (1 - c0 A η₀) * x ^ c0 A η₀) := by ring
      _ = 4 * Real.exp 1 * Ktot A B C η₀ * x := by rw [hsplit2]
  rw [h2, h3] at h1
  have h4 := mul_le_mul_of_nonneg_left hbig hx0.le
  linarith only [h1, h4, hx0]

/-- **Linnik's theorem from a density estimate over the characters mod `q`.** Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0`
with `CharDensity A B C`. For every `η > 0` there is `K` such that for every modulus `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{A+η}`: `prime_in_class` at `x = X₀q^{A+η₀}`,
`η₀ = min(η, 1)/2`, and `10x log x ≤ K q^{A+2η₀}` (`log q ≤ q^{η₀}/η₀`). The zero-free half-plane is the stack's
`Eis.LFunction_ne_zero_of_re_gt`, used through `error_le`. -/
theorem linnik_of_charDensity {A B C : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (A + η) := by
  set η₀ := min η 1 / 2 with hη₀
  have hmin : 0 < min η 1 := lt_min hη one_pos
  have hη0 : 0 < η₀ := by rw [hη₀]; positivity
  have hη1 : η₀ ≤ 1 / 2 := by have := min_le_right η 1; rw [hη₀]; linarith
  have hη2 : 2 * η₀ ≤ η := by have := min_le_left η 1; rw [hη₀]; linarith
  have hc0 : 0 < c0 A η₀ := c0_pos hA hη0
  have hKt0 : 0 ≤ Ktot A B C η₀ := Ktot_nonneg hA hB hC hη0 hη1
  set X₀ : ℝ := max 100 ((4 * Real.exp 1 * Ktot A B C η₀ + 1) ^ (1 / c0 A η₀)) with hX₀
  have hX100 : 100 ≤ X₀ := le_max_left _ _
  have hlX : 0 ≤ Real.log X₀ := Real.log_nonneg (by linarith)
  refine ⟨10 * X₀ * (Real.log X₀ + (A + η₀) / η₀), fun q _ a ha => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hqa1 : 1 ≤ (q : ℝ) ^ (A + η₀) := Real.one_le_rpow hq1 (by linarith)
  set x : ℝ := X₀ * (q : ℝ) ^ (A + η₀) with hx
  have hxX : X₀ ≤ x := le_mul_of_one_le_right (by linarith) hqa1
  have hx100 : 100 ≤ x := hX100.trans hxX
  have hqx : (q : ℝ) ^ (A + η₀) ≤ x := le_mul_of_one_le_left (by positivity) (by linarith)
  have hbig : 4 * Real.exp 1 * Ktot A B C η₀ + 1 ≤ x ^ c0 A η₀ := by
    have h1 : (4 * Real.exp 1 * Ktot A B C η₀ + 1) ^ (1 / c0 A η₀) ≤ x := (le_max_right _ _).trans hxX
    calc 4 * Real.exp 1 * Ktot A B C η₀ + 1 = ((4 * Real.exp 1 * Ktot A B C η₀ + 1) ^ (1 / c0 A η₀)) ^ c0 A η₀ := by
          rw [one_div, Real.rpow_inv_rpow (by positivity) hc0.ne']
      _ ≤ x ^ c0 A η₀ := Real.rpow_le_rpow (by positivity) h1 hc0.le
  obtain ⟨p, hp, hpa, hpY⟩ := prime_in_class hA hB hC hD hη0 hη1 q ha hx100 hqx hbig
  refine ⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa, hpY.trans ?_⟩
  have hlogq : Real.log q ≤ (q : ℝ) ^ η₀ / η₀ := Real.log_le_rpow_div hq0.le hη0
  have hqe1 : 1 ≤ (q : ℝ) ^ η₀ := Real.one_le_rpow hq1 hη0.le
  have hlx : Real.log x = Real.log X₀ + (A + η₀) * Real.log q := by
    rw [hx, Real.log_mul (by positivity) (by positivity), Real.log_rpow hq0]
  have hAη : 0 ≤ (A + η₀) / η₀ := div_nonneg (by linarith) hη0.le
  have hlx2 : Real.log x ≤ (Real.log X₀ + (A + η₀) / η₀) * (q : ℝ) ^ η₀ := by
    rw [hlx]
    have h1 : (A + η₀) * Real.log q ≤ (A + η₀) * ((q : ℝ) ^ η₀ / η₀) :=
      mul_le_mul_of_nonneg_left hlogq (by linarith)
    have h2 : Real.log X₀ ≤ Real.log X₀ * (q : ℝ) ^ η₀ := le_mul_of_one_le_right hlX hqe1
    have h3 : (A + η₀) * ((q : ℝ) ^ η₀ / η₀) = (A + η₀) / η₀ * (q : ℝ) ^ η₀ := by ring
    have h4 : (Real.log X₀ + (A + η₀) / η₀) * (q : ℝ) ^ η₀ =
        Real.log X₀ * (q : ℝ) ^ η₀ + (A + η₀) / η₀ * (q : ℝ) ^ η₀ := by ring
    linarith only [h1, h2, h3, h4]
  have hqpow : (q : ℝ) ^ (A + η₀) * (q : ℝ) ^ η₀ ≤ (q : ℝ) ^ (A + η) := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hK0 : 0 ≤ 10 * X₀ * (Real.log X₀ + (A + η₀) / η₀) := mul_nonneg (by positivity) (by linarith)
  have hx0 : 0 ≤ x := by positivity
  calc 10 * x * Real.log x ≤ 10 * x * ((Real.log X₀ + (A + η₀) / η₀) * (q : ℝ) ^ η₀) := by gcongr
    _ = 10 * X₀ * (Real.log X₀ + (A + η₀) / η₀) * ((q : ℝ) ^ (A + η₀) * (q : ℝ) ^ η₀) := by rw [hx]; ring
    _ ≤ 10 * X₀ * (Real.log X₀ + (A + η₀) / η₀) * (q : ℝ) ^ (A + η) := by gcongr

/-! ### The trivial density, and Linnik's theorem with exponent `12 + η` -/

open scoped Classical in
/-- **The trivial density from the half-plane**: `CharDensity 12 0 1`. Below `σ = 11/12` at most `φ(q) ≤ q ≤ qT`
characters are counted, and `qT ≤ (qT)^{12(1−σ)}`. Above it only the trivial character can have a zero
(`Eis.LFunction_ne_zero_of_re_gt`), and `1 ≤ (qT)^{12(1−σ)}`. -/
theorem charDensity_twelve : CharDensity 12 0 1 := by
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 1 ≤ (q : ℝ) * T := by nlinarith
  rw [Real.rpow_zero, one_mul, mul_one]
  by_cases hσ' : σ ≤ 11 / 12
  · have hcard : ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ q := by
      have h1 := Finset.card_le_univ (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
      have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]; exact card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      exact_mod_cast h1.trans (h2 ▸ Nat.totient_le q)
    calc _ ≤ (q : ℝ) := hcard
      _ ≤ (q : ℝ) * T := by nlinarith
      _ = ((q : ℝ) * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((q : ℝ) * T) ^ (12 * (1 - σ)) := Real.rpow_le_rpow_of_exponent_le hqT (by linarith)
  · push Not at hσ'
    have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) ⊆ {1} := by
      intro χ hχ
      rw [Finset.mem_filter] at hχ
      obtain ⟨s, hs1, _, hs3⟩ := hχ.2
      rw [Finset.mem_singleton]
      by_contra hne
      exact Eis.LFunction_ne_zero_of_re_gt χ (by linarith) (Or.inl hne) hs3
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    calc _ ≤ (1 : ℝ) := by exact_mod_cast hcard
      _ ≤ ((q : ℝ) * T) ^ (12 * (1 - σ)) := Real.one_le_rpow hqT (by linarith)

/-- **Linnik's theorem with exponent `12 + η`, from the half-plane alone**: `linnik_of_charDensity` at
`charDensity_twelve`. For every `η > 0` there is `K` such that for every modulus `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K q^{12+η}`. -/
theorem linnik_twelve {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (12 + η) :=
  linnik_of_charDensity (by norm_num) le_rfl zero_le_one charDensity_twelve hη

end Linnik

#print axioms Linnik.totient_mul_SAP
#print axioms Linnik.re_Sx_one_ge
#print axioms Linnik.SAP_le_of_noPrime
#print axioms Linnik.error_le
#print axioms Linnik.total_le
#print axioms Linnik.prime_in_class
#print axioms Linnik.linnik_of_charDensity
#print axioms Linnik.charDensity_twelve
#print axioms Linnik.linnik_twelve
