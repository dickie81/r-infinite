/-
# Round 525, part 1: the divisor bound, powers of Dirichlet polynomials and the Halász–Montgomery inequality

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement. For `0 < ε ≤ 1`, `d(n) ≤ C(ε)n^ε` with `C(ε) = (2/ε)^{⌊2^{1/ε}⌋}` (`card_divisors_le`). The `k`-th
power of a Dirichlet polynomial `F(χ, s) = Σ_{j∈S} c_jχ(j)j^{−s}` over the characters mod `q` is the Dirichlet
polynomial with the `k`-fold convolved coefficients (`pv_pow`); for `S ⊆ (P, 2P]` its support lies in `(P^k, (2P)^k]`
(`powSupp_sub`), and for `0 ∉ S`, `|c_j| ≤ d(j)` its coefficients are at most `d(n)^{2k}` (`norm_powCo_le`). With one
point `β_χ + iγ_χ` per character `χ ∈ R`, `β_χ ≥ σ`, and `S ⊆ [1, Λ]` (`hm_duality`),
`(Σ_χ |F(χ, β_χ + iγ_χ)|)² ≤ e·Σ_n |c_n|²n^{−2σ}·(|R|Λ + |R|²B)`, where `B` bounds `|K_Λ(χχ′⁻¹, z)|`,
`K_Λ(ψ, z) = Σ_{n≥1} ψ(n)n^{−z}e^{−n/Λ}`, at `z = β_χ + β_χ′ − 2σ + i(γ_χ − γ_χ′)` for `χ ≠ χ′`.

* `card_divisors_le`: `d(n) = ∏_{p^a ∥ n}(a + 1)`, with `a + 1 ≤ (p^a)^ε` when `p^ε ≥ 2` and `a + 1 ≤ (2/ε)(p^a)^ε`
  otherwise (`add_one_le_prime_pow`); the second case needs `p ≤ 2^{1/ε}`.
* `pv_pow`, `powSupp_sub`, `norm_powCo_le`: the multinomial expansion over `S^k`, grouped by the product; a product `n`
  has at most `d(n)^k` representations, each contributing at most `d(n)^k`.
* `hm_duality`: duality with the phases `η_χ = conj D_χ/|D_χ|`, Cauchy–Schwarz with the weight `e^{−n/Λ}` (at least
  `e^{−1}` on `S`), the full series `Σ_n e^{−n/Λ}|Σ_χ η_χχ(n)n^{−u_χ}|² = Σ_{χ,χ′} η_χη̄_χ′K_Λ(χχ′⁻¹, z_{χχ′})`, the
  diagonal `|K_Λ(χχ⁻¹, z)| ≤ Σ_n e^{−n/Λ} ≤ Λ` (`wt_summable_le`) and the off-diagonal `B`.
-/

import LinnikIngham

open Complex Real Finset

noncomputable section

namespace LinnikPower

/-! ### The divisor bound -/

/-- One prime power: `a + 1 ≤ c_p (p^a)^ε`, with `c_p = 1` when `p^ε ≥ 2` and `c_p = 2/ε` otherwise. -/
lemma add_one_le_prime_pow {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    ((a : ℝ) + 1) ≤ (if 2 ≤ (p : ℝ) ^ ε then 1 else 2 / ε) * ((p : ℝ) ^ a) ^ ε := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpow : ((p : ℝ) ^ a) ^ ε = ((p : ℝ) ^ ε) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le, mul_comm]
  rw [hpow]
  split_ifs with h
  · rw [one_mul]
    have h2 : ((a : ℝ) + 1) ≤ 2 ^ a := by exact_mod_cast Nat.lt_two_pow_self (n := a)
    exact h2.trans (pow_le_pow_left₀ (by norm_num) h a)
  · have h2 : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) hε.le
    have h3 : ((2 : ℝ) ^ ε) ^ a ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by positivity) h2 a
    have h4 : 1 + ε * a * Real.log 2 ≤ ((2 : ℝ) ^ ε) ^ a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      have := Real.add_one_le_exp (Real.log 2 * (ε * a))
      linarith [show Real.log 2 * (ε * a) = ε * a * Real.log 2 by ring]
    have hl : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h1 : (1 : ℝ) ≤ 2 / ε := by rw [le_div_iff₀ hε]; linarith
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    calc (a : ℝ) + 1 ≤ 2 / ε * (1 + ε * a * Real.log 2) := by
          rw [mul_add, mul_one]
          have e : 2 / ε * (ε * a * Real.log 2) = 2 * a * Real.log 2 := by field_simp
          rw [e]
          nlinarith
      _ ≤ 2 / ε * ((p : ℝ) ^ ε) ^ a := by gcongr; linarith

/-- The constant of the divisor bound. -/
def Cdiv (ε : ℝ) : ℝ := (2 / ε) ^ ⌊(2 : ℝ) ^ (1 / ε)⌋₊

lemma one_le_Cdiv {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ Cdiv ε := by
  unfold Cdiv
  exact one_le_pow₀ (by rw [le_div_iff₀ hε]; linarith)

/-- **The divisor bound**: `d(n) ≤ C_ε n^ε` with `C_ε = (2/ε)^{⌊2^{1/ε}⌋}`, for `0 < ε ≤ 1`. -/
theorem card_divisors_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    (n.divisors.card : ℝ) ≤ Cdiv ε * (n : ℝ) ^ ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hε.ne']
  have hn0 : n ≠ 0 := hn.ne'
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]; push_cast; rfl
  have hprod : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast; rfl
  set c : ℕ → ℝ := fun p => if 2 ≤ (p : ℝ) ^ ε then 1 else 2 / ε with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by
    simp only [hc]; split_ifs <;> positivity
  rw [hcard, hprod, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  have hstep : ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (c p * ((p : ℝ) ^ (n.factorization p)) ^ ε) := by
    refine prod_le_prod₀ (fun p _ => by positivity) (fun p hp => ?_)
    exact add_one_le_prime_pow hε hε1 (Nat.prime_of_mem_primeFactors hp).two_le _
  rw [prod_mul_distrib] at hstep
  refine hstep.trans (mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun p _ => by positivity))
  -- the small primes
  have hsplit : ∏ p ∈ n.primeFactors, c p = (2 / ε) ^ (n.primeFactors.filter fun p : ℕ => ¬ 2 ≤ (p : ℝ) ^ ε).card := by
    simp only [hc]
    rw [prod_ite, prod_const_one, one_mul, prod_const]
  rw [hsplit]
  unfold Cdiv
  have h2e : (1 : ℝ) ≤ 2 / ε := by rw [le_div_iff₀ hε]; linarith
  refine pow_le_pow_right₀ h2e ?_
  -- a prime with `p^ε < 2` is at most `2^{1/ε}`
  have hsub : (n.primeFactors.filter fun p : ℕ => ¬ 2 ≤ (p : ℝ) ^ ε) ⊆ Icc 1 ⌊(2 : ℝ) ^ (1 / ε)⌋₊ := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    push Not at hp2
    have hpp := (Nat.prime_of_mem_primeFactors hp1).two_le
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hle : (p : ℝ) ≤ (2 : ℝ) ^ (1 / ε) := by
      have h := Real.rpow_le_rpow (by positivity) hp2.le (by positivity : 0 ≤ 1 / ε)
      rwa [← Real.rpow_mul hp0, mul_one_div_cancel hε.ne', Real.rpow_one] at h
    exact mem_Icc.2 ⟨by omega, Nat.le_floor hle⟩
  calc (n.primeFactors.filter fun p : ℕ => ¬ 2 ≤ (p : ℝ) ^ ε).card ≤ (Icc 1 ⌊(2 : ℝ) ^ (1 / ε)⌋₊).card :=
        card_le_card hsub
    _ = ⌊(2 : ℝ) ^ (1 / ε)⌋₊ := by simp

/-! ### Powers of Dirichlet polynomials -/

variable {q : ℕ}

/-- `Σ_{j∈S} c_j χ(j) j^{−s}`. -/
def pv (S : Finset ℕ) (c : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ j ∈ S, c j * χ j * (j : ℂ) ^ (-s)

/-- The coefficients of the `k`-th power: `c^{(k)}_n = Σ_{g ∈ S^k, Π g = n} Π_i c(g_i)`. -/
def powCo (S : Finset ℕ) (c : ℕ → ℂ) (k n : ℕ) : ℂ :=
  ∑ g ∈ (Fintype.piFinset fun _ : Fin k => S).filter (fun g => ∏ i, g i = n), ∏ i, c (g i)

/-- The support of the `k`-th power: the products `Π_i g_i`, `g ∈ S^k`. -/
def powSupp (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Fintype.piFinset fun _ : Fin k => S).image fun g => ∏ i, g i

lemma natCast_prod_cpow {k : ℕ} (g : Fin k → ℕ) (s : ℂ) :
    (((∏ i, g i : ℕ) : ℂ)) ^ s = ∏ i, ((g i : ℕ) : ℂ) ^ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih]

/-- **The power of a Dirichlet polynomial** is the Dirichlet polynomial with the convolved coefficients. -/
theorem pv_pow (S : Finset ℕ) (c : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (s : ℂ) (k : ℕ) :
    pv S c χ s ^ k = pv (powSupp S k) (powCo S c k) χ s := by
  classical
  unfold pv powCo powSupp
  rw [sum_pow']
  have hterm : ∀ g : Fin k → ℕ, ∏ i, (c (g i) * χ (g i) * ((g i : ℕ) : ℂ) ^ (-s))
      = (∏ i, c (g i)) * (χ ((∏ i, g i : ℕ)) * (((∏ i, g i : ℕ) : ℂ)) ^ (-s)) := by
    intro g
    rw [natCast_prod_cpow, prod_mul_distrib, prod_mul_distrib]
    have hχ : χ ((∏ i, g i : ℕ) : ZMod q) = ∏ i, χ (g i) := by
      rw [Nat.cast_prod, map_prod]
    rw [hχ]; ring
  simp_rw [hterm]
  rw [← sum_fiberwise_of_maps_to (s := Fintype.piFinset fun _ : Fin k => S)
    (t := (Fintype.piFinset fun _ : Fin k => S).image fun g => ∏ i, g i) (g := fun g => ∏ i, g i)
    (fun g hg => mem_image_of_mem _ hg)]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, sum_mul]
  refine sum_congr rfl fun g hg => ?_
  rw [(mem_filter.1 hg).2]

/-- The support of the `k`-th power of a polynomial on `(P, 2P]` lies in `(P^k, (2P)^k]` for `k ≥ 1`. -/
theorem powSupp_sub {S : Finset ℕ} {P : ℕ} (hS : S ⊆ Ioc P (2 * P)) {k : ℕ} (hk : 1 ≤ k) :
    powSupp S k ⊆ Ioc (P ^ k) ((2 * P) ^ k) := by
  intro n hn
  obtain ⟨g, hg, rfl⟩ := mem_image.1 hn
  have hgi : ∀ i, g i ∈ Ioc P (2 * P) := fun i => hS (Fintype.mem_piFinset.1 hg i)
  refine mem_Ioc.2 ⟨?_, ?_⟩
  · have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
    have hP0 : 0 < P := by
      have := mem_Ioc.1 (hgi ⟨0, by omega⟩); omega
    calc P ^ k = ∏ _i : Fin k, P := by simp
      _ < ∏ i, g i := prod_lt_prod_of_nonempty₀ (fun i _ => hP0) (fun i _ => (mem_Ioc.1 (hgi i)).1) hne
  · calc ∏ i, g i ≤ ∏ _i : Fin k, 2 * P := prod_le_prod fun i _ => (mem_Ioc.1 (hgi i)).2
      _ = (2 * P) ^ k := by simp

/-- **The coefficient bound** `|c^{(k)}_n| ≤ d(n)^{2k}` when `|c_j| ≤ d(j)` and `0 ∉ S`. -/
theorem norm_powCo_le {S : Finset ℕ} (hS0 : 0 ∉ S) {c : ℕ → ℂ} (hc : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ))
    (k : ℕ) {n : ℕ} (hn : n ∈ powSupp S k) :
    ‖powCo S c k n‖ ≤ ((n.divisors.card : ℝ)) ^ (2 * k) := by
  classical
  obtain ⟨g₀, hg₀, hn0⟩ := mem_image.1 hn
  have hgne : ∀ g ∈ Fintype.piFinset (fun _ : Fin k => S), ∀ i, g i ≠ 0 := fun g hg i h =>
    hS0 (h ▸ Fintype.mem_piFinset.1 hg i)
  have hnne : n ≠ 0 := by
    rw [← hn0]; exact prod_ne_zero_iff.2 fun i _ => hgne g₀ hg₀ i
  set F := (Fintype.piFinset fun _ : Fin k => S).filter (fun g => ∏ i, g i = n) with hF
  have hdvd : ∀ g ∈ F, ∀ i, g i ∣ n := by
    intro g hg i
    rw [← (mem_filter.1 hg).2]
    exact dvd_prod_of_mem _ (mem_univ i)
  -- each product is at most `d(n)^k`
  have hprod : ∀ g ∈ F, ‖∏ i, c (g i)‖ ≤ (n.divisors.card : ℝ) ^ k := by
    intro g hg
    rw [norm_prod]
    calc ∏ i, ‖c (g i)‖ ≤ ∏ _i : Fin k, (n.divisors.card : ℝ) := by
          refine prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
          refine (hc _ (Fintype.mem_piFinset.1 (mem_filter.1 hg).1 i)).trans ?_
          exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hnne (hdvd g hg i))
      _ = (n.divisors.card : ℝ) ^ k := by simp
  -- at most `d(n)^k` tuples
  have hcardF : (F.card : ℝ) ≤ (n.divisors.card : ℝ) ^ k := by
    have hsub : F ⊆ Fintype.piFinset fun _ : Fin k => n.divisors := by
      intro g hg
      exact Fintype.mem_piFinset.2 fun i => Nat.mem_divisors.2 ⟨hdvd g hg i, hnne⟩
    have := card_le_card hsub
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  unfold powCo
  rw [← hF]
  calc ‖∑ g ∈ F, ∏ i, c (g i)‖ ≤ ∑ g ∈ F, ‖∏ i, c (g i)‖ := norm_sum_le _ _
    _ ≤ ∑ _g ∈ F, (n.divisors.card : ℝ) ^ k := sum_le_sum hprod
    _ = F.card * (n.divisors.card : ℝ) ^ k := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n.divisors.card : ℝ) ^ k * (n.divisors.card : ℝ) ^ k := by gcongr
    _ = ((n.divisors.card : ℝ)) ^ (2 * k) := by rw [← pow_add]; ring_nf

/-! ### The Halász–Montgomery inequality over the characters -/

/-- The `n`-th term of `K_Λ(ψ, z) = Σ_{n≥1} ψ(n) n^{−z} e^{−n/Λ}`. -/
def kTerm (ψ : DirichletCharacter ℂ q) (Λ : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else ψ n * (n : ℂ) ^ (-z) * (Real.exp (-((n : ℝ) / Λ)) : ℂ)

/-- The weight `e^{−n/Λ}` for `n ≥ 1`, and `0` at `n = 0`. -/
def wt (Λ : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else Real.exp (-((n : ℝ) / Λ))

lemma wt_nonneg (Λ : ℝ) (n : ℕ) : 0 ≤ wt Λ n := by
  unfold wt; split_ifs <;> positivity

/-- `Σ_{n≥1} e^{−n/Λ}` converges and is at most `Λ`. -/
lemma wt_summable_le {Λ : ℝ} (hΛ : 0 < Λ) : Summable (wt Λ) ∧ ∑' n : ℕ, wt Λ n ≤ Λ := by
  set r := Real.exp (-(1 / Λ)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  have hpow : ∀ n : ℕ, Real.exp (-((n : ℝ) / Λ)) = r ^ n := fun n => by
    rw [hr, ← Real.exp_nat_mul]; congr 1; ring
  have hg := summable_geometric_of_lt_one hr0.le hr1
  have hs : Summable (wt Λ) := by
    refine Summable.of_nonneg_of_le (wt_nonneg Λ) (fun n => ?_) hg
    unfold wt; split_ifs
    · positivity
    · rw [hpow]
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add]
  have h0 : wt Λ 0 = 0 := by simp [wt]
  have hsucc : ∀ n : ℕ, wt Λ (n + 1) = r * r ^ n := fun n => by
    simp only [wt, Nat.add_one_ne_zero, ite_false]
    rw [hpow, pow_succ, mul_comm]
  simp_rw [h0, hsucc, zero_add]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
  -- `r/(1 − r) ≤ Λ` from `e^{1/Λ} ≥ 1 + 1/Λ`
  have h1r : 0 < 1 - r := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ h1r]
  have he : 1 + 1 / Λ ≤ Real.exp (1 / Λ) := by have := Real.add_one_le_exp (1 / Λ); linarith
  have hre : r * Real.exp (1 / Λ) = 1 := by rw [hr, ← Real.exp_add]; simp
  have : r * (1 + 1 / Λ) ≤ 1 := by
    calc r * (1 + 1 / Λ) ≤ r * Real.exp (1 / Λ) := by gcongr
      _ = 1 := hre
  have e : r * (1 + 1 / Λ) = r + r / Λ := by ring
  rw [e] at this
  have : r / Λ * Λ = r := by field_simp
  nlinarith

/-- `‖K_Λ(ψ, z)‖`'s terms are at most the weight when `Re z ≥ 0`. -/
lemma norm_kTerm_le (ψ : DirichletCharacter ℂ q) (Λ : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ‖kTerm ψ Λ z n‖ ≤ wt Λ n := by
  unfold kTerm wt
  split_ifs with hn
  · simp
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : ‖ψ n‖ ≤ 1 := DirichletCharacter.norm_le_one ψ n
    have h2 : ‖(n : ℂ) ^ (-z)‖ ≤ 1 := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by simp; linarith)
    calc ‖ψ n‖ * ‖(n : ℂ) ^ (-z)‖ * Real.exp (-((n : ℝ) / Λ)) ≤ 1 * 1 * Real.exp (-((n : ℝ) / Λ)) := by
          gcongr
      _ = Real.exp (-((n : ℝ) / Λ)) := by ring

lemma summable_kTerm (ψ : DirichletCharacter ℂ q) {Λ : ℝ} (hΛ : 0 < Λ) {z : ℂ} (hz : 0 ≤ z.re) :
    Summable (kTerm ψ Λ z) :=
  Summable.of_norm_bounded (wt_summable_le hΛ).1 (norm_kTerm_le ψ Λ hz)

/-- The phase making `η D = |D|`. -/
def phase (D : ℂ) : ℂ := if D = 0 then 0 else (starRingEnd ℂ) D / (‖D‖ : ℂ)

lemma phase_mul (D : ℂ) : phase D * D = (‖D‖ : ℂ) := by
  unfold phase
  split_ifs with h
  · simp [h]
  · have hn : (‖D‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
    rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
    ring

lemma norm_phase_le (D : ℂ) : ‖phase D‖ ≤ 1 := by
  unfold phase
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.2 h)]

lemma cpow_split {n : ℕ} (hn : n ≠ 0) (σ β γ : ℝ) :
    (n : ℂ) ^ (-((β : ℂ) + γ * I)) = (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(((β - σ : ℝ) : ℂ) + γ * I)) := by
  rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.2 hn)]
  congr 1; push_cast; ring

/-- `n^{−u}·conj(n^{−u′}) = n^{−(u + conj u′)}` for `n ≥ 1`. -/
lemma cpow_mul_conj_cpow {n : ℕ} (hn : n ≠ 0) (u u' : ℂ) :
    (n : ℂ) ^ (-u) * (starRingEnd ℂ) ((n : ℂ) ^ (-u')) = (n : ℂ) ^ (-(u + (starRingEnd ℂ) u')) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  have hc : (starRingEnd ℂ) ((n : ℂ) ^ (-u')) = (n : ℂ) ^ (-(starRingEnd ℂ) u') := by
    have h := Complex.cpow_conj (n : ℂ) (-u') harg
    rw [Complex.conj_natCast, map_neg] at h
    exact h.symm
  rw [hc, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.2 hn)]
  congr 1; ring

/-- **The Halász–Montgomery duality inequality over the characters mod `q`**, one point `β_χ + iγ_χ` per
character, `β_χ ≥ σ`: `(Σ_χ |D_χ|)² ≤ e·G·(|R|Λ + |R|²B)`, with `G = Σ_{n∈S}|a_n|²n^{−2σ}`, for `S ⊆ [1, Λ]` and
`|K_Λ(χχ′⁻¹, z_{χχ′})| ≤ B` for `χ ≠ χ′`, `z_{χχ′} = (β_χ + β_{χ′} − 2σ) + i(γ_χ − γ_{χ′})`. -/
theorem hm_duality {R : Finset (DirichletCharacter ℂ q)} {S : Finset ℕ} (hS0 : 0 ∉ S) {Λ : ℝ} (hΛ : 0 < Λ)
    (hSΛ : ∀ n ∈ S, (n : ℝ) ≤ Λ) (a : ℕ → ℂ) {σ : ℝ} (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σ ≤ β χ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ χ ∈ R, ∀ χ' ∈ R, χ ≠ χ' →
      ‖∑' n : ℕ, kTerm (χ * χ'⁻¹) Λ (((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I) n‖ ≤ B) :
    (∑ χ ∈ R, ‖pv S a χ ((β χ : ℂ) + γ χ * I)‖) ^ 2 ≤
      Real.exp 1 * (∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) * (R.card * Λ + R.card ^ 2 * B) := by
  classical
  set u : DirichletCharacter ℂ q → ℂ := fun χ => ((β χ - σ : ℝ) : ℂ) + (γ χ : ℂ) * I with hu
  set D : DirichletCharacter ℂ q → ℂ := fun χ => pv S a χ ((β χ : ℂ) + γ χ * I) with hD
  set η : DirichletCharacter ℂ q → ℂ := fun χ => phase (D χ) with hη
  set Φ : ℕ → ℂ := fun n => ∑ χ ∈ R, η χ * χ n * (n : ℂ) ^ (-u χ) with hΦ
  set x : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-(σ : ℂ)) with hx
  -- (1) the sum of the moduli as a bilinear form
  have hηD : ∀ χ, η χ * D χ = (‖D χ‖ : ℂ) := fun χ => phase_mul (D χ)
  have h1 : ((∑ χ ∈ R, ‖D χ‖ : ℝ) : ℂ) = ∑ n ∈ S, x n * Φ n := by
    push_cast
    rw [← sum_congr rfl fun χ _ => hηD χ]
    simp only [hD, pv, hΦ, hx, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n hn => sum_congr rfl fun χ _ => ?_
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [cpow_split hn0 σ (β χ) (γ χ)]
    simp only [hu]
    ring
  -- (2) the moduli of the terms
  have hnx : ∀ n ∈ S, ‖x n‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
    intro n hn
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [hx, norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0)]
    simp
  -- (3) Cauchy–Schwarz with the weight `e^{−n/Λ}`
  set w : ℕ → ℝ := fun n => Real.exp (-((n : ℝ) / Λ)) with hw
  have hwpos : ∀ n, 0 < w n := fun n => Real.exp_pos _
  have hcs : (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := by
    have h := sum_mul_sq_le_sq_mul_sq S (fun n => ‖x n‖ * (Real.sqrt (w n))⁻¹) (fun n => Real.sqrt (w n) * ‖Φ n‖)
    have e1 : ∀ n, ‖x n‖ * (Real.sqrt (w n))⁻¹ * (Real.sqrt (w n) * ‖Φ n‖) = ‖x n‖ * ‖Φ n‖ := fun n => by
      have : Real.sqrt (w n) ≠ 0 := (Real.sqrt_pos.2 (hwpos n)).ne'
      field_simp
    have e2 : ∀ n, (‖x n‖ * (Real.sqrt (w n))⁻¹) ^ 2 = ‖x n‖ ^ 2 / w n := fun n => by
      rw [mul_pow, inv_pow, Real.sq_sqrt (hwpos n).le, div_eq_mul_inv]
    have e3 : ∀ n, (Real.sqrt (w n) * ‖Φ n‖) ^ 2 = w n * ‖Φ n‖ ^ 2 := fun n => by
      rw [mul_pow, Real.sq_sqrt (hwpos n).le]
    simp only [e1, e2, e3] at h
    exact h
  have hG : ∑ n ∈ S, ‖x n‖ ^ 2 / w n ≤ Real.exp 1 * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [hnx n hn, hw, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    have : Real.exp ((n : ℝ) / Λ) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 ((div_le_one hΛ).2 (hSΛ n hn))
    calc (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * Real.exp ((n : ℝ) / Λ)
        ≤ (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * Real.exp 1 := by gcongr
      _ = Real.exp 1 * (‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by ring
  -- (4) the weighted square sum as a double sum of kernels
  set z : DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℂ :=
    fun χ χ' => ((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I with hz
  have hzre : ∀ χ ∈ R, ∀ χ' ∈ R, 0 ≤ (z χ χ').re := by
    intro χ hχ χ' hχ'
    simp only [hz, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    linarith [hβ χ hχ, hβ χ' hχ']
  have hzu : ∀ χ χ', z χ χ' = u χ + (starRingEnd ℂ) (u χ') := by
    intro χ χ'
    simp only [hz, hu, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  set F : ℕ → ℂ := fun n => ∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * kTerm (χ * χ'⁻¹) Λ (z χ χ') n
    with hF
  have hFeq : ∀ n, n ≠ 0 → F n = (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) := by
    intro n hn
    have hterm : ∀ χ χ', kTerm (χ * χ'⁻¹) Λ (z χ χ') n
        = (w n : ℂ) * (χ n * (n : ℂ) ^ (-u χ)) * (starRingEnd ℂ) (χ' n * (n : ℂ) ^ (-u χ')) := by
      intro χ χ'
      simp only [kTerm, hn, ite_false, hw]
      rw [MulChar.mul_apply, ← MulChar.star_apply', hzu, ← cpow_mul_conj_cpow hn, map_mul, Complex.star_def]
      ring
    have hΦexp : (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) = ∑ χ ∈ R, ∑ χ' ∈ R,
        (w n : ℂ) * (η χ * χ n * (n : ℂ) ^ (-u χ)) * (starRingEnd ℂ) (η χ' * χ' n * (n : ℂ) ^ (-u χ')) := by
      simp only [hΦ, map_sum]
      rw [mul_assoc, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun χ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun χ' _ => ?_
      ring
    rw [hΦexp]
    simp only [hF]
    refine sum_congr rfl fun χ _ => sum_congr rfl fun χ' _ => ?_
    rw [hterm, map_mul, map_mul, map_mul]
    ring
  have hFre : ∀ n, (F n).re = (if n = 0 then 0 else w n * ‖Φ n‖ ^ 2) := by
    intro n
    split_ifs with hn
    · simp [hF, kTerm, hn]
    · rw [hFeq n hn, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- (5) summability and the bound on the double sum
  have hsumk : ∀ χ ∈ R, ∀ χ' ∈ R, Summable (kTerm (χ * χ'⁻¹) Λ (z χ χ')) :=
    fun χ hχ χ' hχ' => summable_kTerm _ hΛ (hzre χ hχ χ' hχ')
  have hηle : ∀ χ, ‖η χ‖ ≤ 1 := fun χ => norm_phase_le _
  have hFsum : Summable F := by
    simp only [hF]
    refine summable_sum fun χ hχ => summable_sum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _
  have hFbd : ∀ n, ‖F n‖ ≤ (R.card : ℝ) ^ 2 * wt Λ n := by
    intro n
    simp only [hF]
    calc ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
        ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ‖η χ * (starRingEnd ℂ) (η χ') * kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun χ _ => norm_sum_le _ _)
      _ ≤ ∑ _χ ∈ R, ∑ _χ' ∈ R, wt Λ n := by
          refine sum_le_sum fun χ hχ => sum_le_sum fun χ' hχ' => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          have h1 := hηle χ
          have h2 := hηle χ'
          have h3 := norm_kTerm_le (χ * χ'⁻¹) Λ (hzre χ hχ χ' hχ') n
          have h0 := norm_nonneg (kTerm (χ * χ'⁻¹) Λ (z χ χ') n)
          calc ‖η χ‖ * ‖η χ'‖ * ‖kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ ≤ 1 * 1 * wt Λ n := by gcongr
            _ = wt Λ n := by ring
      _ = (R.card : ℝ) ^ 2 * wt Λ n := by rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
  have hwt := wt_summable_le hΛ
  have hFresum : Summable fun n => (F n).re :=
    Summable.of_norm_bounded (hwt.1.mul_left ((R.card : ℝ) ^ 2))
      (fun n => (Real.norm_eq_abs _).trans_le ((Complex.abs_re_le_norm (F n)).trans (hFbd n)))
  -- (6) the finite weighted sum against the full series
  have hFre0 : ∀ n, 0 ≤ (F n).re := fun n => by
    rw [hFre n]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hwpos n).le (by positivity)
  have h6 : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := by
    have e : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 = ∑ n ∈ S, (F n).re := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
      rw [hFre n, ite_eq_right hn0]
    rw [e]
    exact hFresum.sum_le_tsum S (fun n _ => hFre0 n)
  -- (7)–(8) the series as a double sum of kernels
  have h7 : ∑' n, (F n).re ≤ ‖∑' n, F n‖ := by
    rw [← Complex.re_tsum hFsum]; exact Complex.re_le_norm _
  have h8 : ∑' n, F n = ∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') *
      ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n := by
    simp only [hF]
    rw [Summable.tsum_finsetSum fun χ hχ => summable_sum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _]
    refine sum_congr rfl fun χ hχ => ?_
    rw [Summable.tsum_finsetSum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _]
    exact sum_congr rfl fun χ' _ => tsum_mul_left
  -- (9) the diagonal and the off-diagonal
  have hdiag : ∀ χ ∈ R, ‖∑' n, kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ ≤ Λ := by
    intro χ hχ
    have hn := fun n => norm_kTerm_le (χ * χ⁻¹) Λ (hzre χ hχ χ hχ) n
    have hns : Summable fun n => ‖kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hn hwt.1
    calc ‖∑' n, kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ ≤ ∑' n, ‖kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ :=
          norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n, wt Λ n := hns.tsum_le_tsum hn hwt.1
      _ ≤ Λ := hwt.2
  have h9 : ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
      ≤ R.card * Λ + R.card ^ 2 * B := by
    have hpt : ∀ χ ∈ R, ∀ χ' ∈ R,
        ‖η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
          ≤ (if χ = χ' then Λ else 0) + B := by
      intro χ hχ χ' hχ'
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have h1 := hηle χ
      have h2 := hηle χ'
      have hK : ‖∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ ≤ (if χ = χ' then Λ else 0) + B := by
        split_ifs with h
        · subst h; linarith [hdiag χ hχ]
        · rw [zero_add]
          have := hB χ hχ χ' hχ' h
          simpa [hz] using this
      have h0 := norm_nonneg (∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n)
      calc ‖η χ‖ * ‖η χ'‖ * ‖∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
          ≤ 1 * 1 * ((if χ = χ' then Λ else 0) + B) := by gcongr
        _ = (if χ = χ' then Λ else 0) + B := by ring
    calc ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
        ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ‖η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun χ _ => norm_sum_le _ _)
      _ ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ((if χ = χ' then Λ else 0) + B) :=
          sum_le_sum fun χ hχ => sum_le_sum fun χ' hχ' => hpt χ hχ χ' hχ'
      _ = R.card * Λ + R.card ^ 2 * B := by
          simp only [sum_add_distrib, sum_ite_eq, sum_const, nsmul_eq_mul]
          rw [sum_congr rfl fun χ hχ => ite_eq_left hχ, sum_const, nsmul_eq_mul]
          ring
  -- (10) assemble
  have hDnn : 0 ≤ ∑ χ ∈ R, ‖D χ‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hmod : ∑ χ ∈ R, ‖D χ‖ ≤ ∑ n ∈ S, ‖x n‖ * ‖Φ n‖ := by
    have := congrArg norm h1
    rw [Complex.norm_real, Real.norm_of_nonneg hDnn] at this
    rw [this]
    exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => norm_mul _ _))
  have hW : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ R.card * Λ + R.card ^ 2 * B := by
    calc ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := h6
      _ ≤ ‖∑' n, F n‖ := h7
      _ = _ := by rw [h8]
      _ ≤ R.card * Λ + R.card ^ 2 * B := h9
  have hWnn : 0 ≤ ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 := sum_nonneg fun n _ => mul_nonneg (hwpos n).le (by positivity)
  have hGnn : 0 ≤ ∑ n ∈ S, ‖x n‖ ^ 2 / w n := sum_nonneg fun n _ => div_nonneg (by positivity) (hwpos n).le
  calc (∑ χ ∈ R, ‖pv S a χ ((β χ : ℂ) + γ χ * I)‖) ^ 2 = (∑ χ ∈ R, ‖D χ‖) ^ 2 := rfl
    _ ≤ (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 := pow_le_pow_left₀ hDnn hmod 2
    _ ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := hcs
    _ ≤ (Real.exp 1 * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) * (R.card * Λ + R.card ^ 2 * B) :=
        mul_le_mul hG hW hWnn (by positivity)

end LinnikPower

#print axioms LinnikPower.card_divisors_le
#print axioms LinnikPower.pv_pow
#print axioms LinnikPower.powSupp_sub
#print axioms LinnikPower.norm_powCo_le
#print axioms LinnikPower.hm_duality
