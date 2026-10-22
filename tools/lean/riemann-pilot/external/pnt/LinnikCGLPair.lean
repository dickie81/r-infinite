/-
# Round 642: the bounds of the reflected Gram entries (the CGL plan's stage M3)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Round 641's `LinnikCGLReflect.gram_reflect` writes a Gram entry as a main part on `Re s = 1/2` and a tail on
`Re s = −K`. This file bounds both, for one pair: the main part by an integral of its dual sum, and the tail by a
power `(NZ)^{−K}`. These are the bounds of Chen–Gupta–Li's Lemma 6.2, which the proof of their Proposition 6.1 then
sums over the pairs.

Plain statement (`norm_gram_le`). For `χ_i ≠ χ_k`, `τ = t_i − t_k`, `N > 0` and `Z, K ≥ 1`,
`|G(i, k)| ≤ (2π)⁻¹(N^{1/2}Q₀(q)∫|H(1/2 + iu)||D(u)| du + T_K)`, where `D(u) = Σ_{m≤Z}(χ_iχ̄_k)⁻¹(m)m^{−1/2+i(u−τ)}`,
`Q₀(q) = 2^{ω(q)}·π·CGK(0)·EQh(q)` and
`T_K = 2^{ω(q)+1}·π·CGK(K)·EQh(q)·q^{K+1/2}(NZ)^{−K}(1 + |τ|)^{K+1}I_K`, `I_K = ∫|H(−K + iu)|(1 + |u|)^{K+1} du`.

Plain statement (`norm_Eu_mul_le`). For `ψ` mod `f`, `f ∣ q`, `c ≥ 0` and `−Re s ≤ c`, the Euler factor
`E(s) = ∏_{p|q}(1 − ψ(p)p^{−s})` satisfies `|E(s)|·f^c ≤ 2^{ω(q)}q^c`.

Plain statement (`norm_dualT_le`). For `Z, K ≥ 1`, `|Σ_{m>Z}χ(m)m^{s−1}| ≤ 2Z^{−K}` on `Re s = −K`.

The proof of their Lemma 6.2 splits the dual series at `M`, "shifting the contour of the integral involving terms with
m ≤ M to Re(s) = 1/2, while shifting the integral involving terms with m > M to Re(s) = −2k for a large k ∈ N". For
`|t| ∼ T₀ ≥ (qT)^ϵ` it takes `M = (qT)^{2ϵ}qT₀/N` and bounds the tail by a display that reads, on one line,
`|I₂| ≪_k (qT)^{ϵ/2}N^{−2k}(q*T₀)^{1/2+2k}/((qT)^{2ϵ}qT₀/N)^{2k}·(q/q*)^{2k+2} + O_{ϵ,k}((qT)^{−200})`. `T_K` is its
analogue at `K = 2k`, with `Z` for `M` and no truncation of the integral. Their `(q/q*)^{2k+2}` bounds their `P`, a
ratio of two products over `p | q, p ∤ q*`; here the numerator is `E` (`norm_Eu_mul_le`: `|E| ≤ 2^{ω(q)}(q/f)^K`) and
the denominator sits inside round 641's `Φ`, which `EQh(q)` bounds.

* `apply_prime_dvd`, `norm_Eu_factor_le`, `norm_Eu_mul_le`: the Euler factor. For `p ∣ f`, `ψ(p) = 0`, and
  `f·∏_{p|q, p∤f} p` divides `q`.
* `norm_dualT_le`: each term is at most `m^{−2}Z^{1−K}`, and `Σ_{m>Z}m^{−2} ≤ 2/(Z + 1)` (Mathlib's
  `sum_Ioo_inv_sq_le`).
* `Q0`, `norm_EuPhi_half_le`, `norm_integral_Mn_le`: `|E(s)Φ(s)| ≤ Q₀(q)` on `Re s = 1/2` (round 641's
  `norm_Eu_le` at `c = 0` and `norm_Phi_le_far` at `K = 0`), and the substitution `u = v + τ`.
* `IK`, `integrable_IK`, `IK_nonneg`, `norm_integral_Tl_le`: on `Re s = −K`, `|N^s| = N^{−K}`,
  `|E|f^K ≤ 2^{ω(q)}q^K`, `|Φ| ≤ f^{1/2+K}·π·CGK(K)(1 + |Im s|)^{K+1/2}EQh(q)` and `|Σ_{m>Z}| ≤ 2Z^{−K}`; after the
  substitution `u = v + τ`, `1 + |v| ≤ (1 + |u|)(1 + |τ|)`.
* `norm_gram_le`: the two with round 641's `gram_reflect`, and `|N^{iτ}| = 1`.

The file imports `LinnikCGLReflect.lean`.
-/

import LinnikCGLReflect

open Complex Set Real Filter Topology MeasureTheory

noncomputable section

namespace LinnikCGLPair

open LinnikCGLMat LinnikCGLMellin LinnikCGLReflect DirichletCharacter LinnikReflect

/-! ### The Euler factor against the conductor, and the dual tail far left -/

/-- For a character `ψ` mod `f` and a prime `p ∣ f`, `ψ(p) = 0`. -/
lemma apply_prime_dvd {f : ℕ} (ψ : DirichletCharacter ℂ f) {p : ℕ} (hp : p.Prime) (hpf : p ∣ f) : ψ p = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  exact (Nat.Prime.dvd_iff_not_coprime hp).1 hpf

/-- `|1 − ψ(p)p^{−s}| ≤ 1 + p^c` for `−Re s ≤ c`. -/
lemma norm_Eu_factor_le {f : ℕ} (ψ : DirichletCharacter ℂ f) {p : ℕ} (hp : p.Prime) {s : ℂ} {c : ℝ}
    (hc : -s.re ≤ c) : ‖1 - ψ p * (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ c := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  calc ‖1 - ψ p * (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖ψ p * (p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ) ^ c := by
        rw [norm_one, norm_mul]
        have h1 : ‖ψ p‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
        have h2 : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
          rw [Complex.norm_natCast_cpow_of_pos hp.pos]; simp
        rw [h2]
        have h3 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hp1 hc
        have h4 : 0 ≤ (p : ℝ) ^ (-s.re) := by positivity
        nlinarith [norm_nonneg (ψ p)]

/-- **The Euler factor against the conductor**: for `ψ` mod `f`, `f ∣ q`, `c ≥ 0` and `−Re s ≤ c`,
`|E(s)|·f^c ≤ 2^{ω(q)}q^c`. The factors at `p ∣ f` are `1`, and `f·∏_{p|q, p∤f} p` divides `q`. -/
lemma norm_Eu_mul_le {q f : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ f) (hfq : f ∣ q) {s : ℂ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : -s.re ≤ c) :
    ‖Eu ψ q s‖ * (f : ℝ) ^ c ≤ 2 ^ q.primeFactors.card * (q : ℝ) ^ c := by
  classical
  set P := q.primeFactors.filter (fun p => ¬ p ∣ f) with hP
  have hE : ‖Eu ψ q s‖ ≤ ∏ p ∈ P, (2 * (p : ℝ) ^ c) := by
    unfold Eu
    rw [norm_prod, ← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => ¬ p ∣ f)]
    have h1 : ∏ p ∈ q.primeFactors.filter (fun p => ¬¬ p ∣ f), ‖1 - ψ p * (p : ℂ) ^ (-s)‖ = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      rw [not_not] at hp2
      rw [apply_prime_dvd ψ (Nat.prime_of_mem_primeFactors hp1) hp2]
      simp
    rw [h1, mul_one]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have := Real.one_le_rpow hp1 hc0
    exact (norm_Eu_factor_le ψ hpp hc).trans (by linarith)
  have hdvd : f * ∏ p ∈ P, p ∣ q := by
    have hcop : Nat.Coprime f (∏ p ∈ P, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
      exact ((Nat.Prime.coprime_iff_not_dvd hpp).2 (Finset.mem_filter.1 hp).2).symm
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hfq ?_
    refine Finset.prod_primes_dvd q (fun p hp => ?_) (fun p hp => ?_)
    · exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).prime
    · exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hp).1
  have hle : (f : ℝ) * ∏ p ∈ P, (p : ℝ) ≤ q := by
    rw [← Nat.cast_prod, ← Nat.cast_mul]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd
  have hcard : P.card ≤ q.primeFactors.card := Finset.card_filter_le _ _
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hprod0 : (0 : ℝ) ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  calc ‖Eu ψ q s‖ * (f : ℝ) ^ c ≤ (∏ p ∈ P, (2 * (p : ℝ) ^ c)) * (f : ℝ) ^ c := by gcongr
    _ = 2 ^ P.card * (((f : ℝ) * ∏ p ∈ P, (p : ℝ)) ^ c) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _),
          Real.mul_rpow hf0 hprod0]
        ring
    _ ≤ 2 ^ q.primeFactors.card * (q : ℝ) ^ c := by
        gcongr
        norm_num

/-- **The dual tail far left**: `|Σ_{m>Z}χ(m)m^{s−1}| ≤ 2Z^{−K}` on `Re s = −K`, for `Z ≥ 1` and `K ≥ 1`; each term
is at most `m^{−2}Z^{1−K}`, and `Σ_{m>Z}m^{−2} ≤ 2/(Z + 1)` (Mathlib's `sum_Ioo_inv_sq_le`). -/
lemma norm_dualT_le {q : ℕ} (χ : DirichletCharacter ℂ q) {Z K : ℕ} (hZ : 1 ≤ Z) (hK : 1 ≤ K) (v : ℝ) :
    ‖dualT χ Z (((-(K : ℝ) : ℝ) : ℂ) + v * I)‖ ≤ 2 * (Z : ℝ) ^ (-(K : ℝ)) := by
  set s : ℂ := ((-(K : ℝ) : ℝ) : ℂ) + v * I with hs
  have hsre : (s - 1).re = -(K : ℝ) - 1 := by simp [hs]
  have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set g : ℕ → ℝ := fun m => if Z < m then ((m : ℝ) ^ 2)⁻¹ * (Z : ℝ) ^ (1 - (K : ℝ)) else 0 with hg
  have hterm : ∀ m : ℕ, ‖(if Z < m then χ m * (m : ℂ) ^ (s - 1) else 0)‖ ≤ g m := by
    intro m
    simp only [hg]
    split_ifs with hm
    · have hm0 : 0 < m := by omega
      have hmR : (Z : ℝ) < m := by exact_mod_cast hm
      have hm1 : (1 : ℝ) ≤ m := by linarith
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hm0, hsre]
      have h1 : ‖χ m‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have h2 : (m : ℝ) ^ (-(K : ℝ) - 1) = ((m : ℝ) ^ 2)⁻¹ * (m : ℝ) ^ (1 - (K : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
        congr 1; push_cast; ring
      have h3 : (m : ℝ) ^ (1 - (K : ℝ)) ≤ (Z : ℝ) ^ (1 - (K : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hmR.le (by linarith)
      rw [h2]
      have h4 : 0 ≤ ((m : ℝ) ^ 2)⁻¹ * (m : ℝ) ^ (1 - (K : ℝ)) := by positivity
      calc ‖χ m‖ * (((m : ℝ) ^ 2)⁻¹ * (m : ℝ) ^ (1 - (K : ℝ)))
          ≤ 1 * (((m : ℝ) ^ 2)⁻¹ * (m : ℝ) ^ (1 - (K : ℝ))) := mul_le_mul_of_nonneg_right h1 h4
        _ ≤ ((m : ℝ) ^ 2)⁻¹ * (Z : ℝ) ^ (1 - (K : ℝ)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
    · simp
  have hg0 : ∀ m, 0 ≤ g m := fun m => by simp only [hg]; split_ifs <;> positivity
  -- the sum of `g`
  have hsum : ∀ u : Finset ℕ, ∑ m ∈ u, g m ≤ 2 / ((Z : ℝ) + 1) * (Z : ℝ) ^ (1 - (K : ℝ)) := by
    intro u
    set n := u.sup id + 1 with hn
    have hsub : u.filter (fun m => Z < m) ⊆ Finset.Ioo Z n := by
      intro m hm
      obtain ⟨hmu, hmZ⟩ := Finset.mem_filter.1 hm
      have : m ≤ u.sup id := Finset.le_sup (f := id) hmu
      exact Finset.mem_Ioo.2 ⟨hmZ, by omega⟩
    calc ∑ m ∈ u, g m = ∑ m ∈ u.filter (fun m => Z < m), ((m : ℝ) ^ 2)⁻¹ * (Z : ℝ) ^ (1 - (K : ℝ)) := by
          rw [Finset.sum_filter]
      _ ≤ ∑ m ∈ Finset.Ioo Z n, ((m : ℝ) ^ 2)⁻¹ * (Z : ℝ) ^ (1 - (K : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = (∑ m ∈ Finset.Ioo Z n, ((m : ℝ) ^ 2)⁻¹) * (Z : ℝ) ^ (1 - (K : ℝ)) := by rw [Finset.sum_mul]
      _ ≤ 2 / ((Z : ℝ) + 1) * (Z : ℝ) ^ (1 - (K : ℝ)) := by
          gcongr
          exact sum_Ioo_inv_sq_le Z n
  have hgs : Summable g := summable_of_sum_le hg0 hsum
  have htsum : ∑' m, g m ≤ 2 / ((Z : ℝ) + 1) * (Z : ℝ) ^ (1 - (K : ℝ)) := Real.tsum_le_of_sum_le hg0 hsum
  have hnorm : Summable fun m : ℕ => ‖(if Z < m then χ m * (m : ℂ) ^ (s - 1) else 0)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hgs
  unfold dualT
  calc ‖∑' m : ℕ, (if Z < m then χ m * (m : ℂ) ^ (s - 1) else 0)‖
      ≤ ∑' m : ℕ, ‖(if Z < m then χ m * (m : ℂ) ^ (s - 1) else 0)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m, g m := hnorm.tsum_le_tsum hterm hgs
    _ ≤ 2 / ((Z : ℝ) + 1) * (Z : ℝ) ^ (1 - (K : ℝ)) := htsum
    _ ≤ 2 * (Z : ℝ) ^ (-(K : ℝ)) := by
        have hZp : (0 : ℝ) < Z := by linarith
        have e : (Z : ℝ) ^ (1 - (K : ℝ)) = Z * (Z : ℝ) ^ (-(K : ℝ)) := by
          rw [Real.rpow_sub hZp, Real.rpow_one, Real.rpow_neg hZp.le]; ring
        rw [e]
        have h0 : 0 ≤ (Z : ℝ) ^ (-(K : ℝ)) := by positivity
        have h1 : 2 / ((Z : ℝ) + 1) * Z ≤ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; linarith
        calc 2 / ((Z : ℝ) + 1) * (Z * (Z : ℝ) ^ (-(K : ℝ))) = (2 / ((Z : ℝ) + 1) * Z) * (Z : ℝ) ^ (-(K : ℝ)) := by
              ring
          _ ≤ 2 * (Z : ℝ) ^ (-(K : ℝ)) := mul_le_mul_of_nonneg_right h1 h0

/-! ### The two parts of a reflected Gram entry -/

/-- `Q₀(q) = 2^{ω(q)}·π·CGK(0)·EQh(q)`, the bound of `|E(s)Φ(s)|` on `Re s = 1/2`. -/
def Q0 (q : ℕ) : ℝ := 2 ^ q.primeFactors.card * (Real.pi * CGK 0) * EQh q

lemma Q0_nonneg (q : ℕ) : 0 ≤ Q0 q := by
  unfold Q0; have := CGK_pos 0; have := EQh_pos q; positivity

/-- `|E(1/2 + iv)|·|Φ(1/2 + iv)| ≤ Q₀(q)`. -/
lemma norm_EuPhi_half_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (v : ℝ) :
    ‖Eu χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖ * ‖Phi χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖ ≤
      Q0 q := by
  have hre : (((1 / 2 : ℝ) : ℂ) + v * I).re = 1 / 2 := by simp
  have hE : ‖Eu χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖ ≤ 2 ^ q.primeFactors.card := by
    have h := norm_Eu_le χ.primitiveCharacter q (s := (1 / 2 : ℝ) + v * I) (c := 0) (by rw [hre]; norm_num)
    have e : ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (0 : ℝ)) = 2 ^ q.primeFactors.card := by
      simp only [Real.rpow_zero]; rw [Finset.prod_const]; norm_num
    rwa [e] at h
  have hP := norm_Phi_le_far χ.primitiveCharacter_isPrimitive q 0 (s := (1 / 2 : ℝ) + v * I)
    (by rw [hre]; norm_num) (by rw [hre])
  rw [hre] at hP
  simp only [sub_self, Real.rpow_zero, mul_one, one_mul] at hP
  have h2 : (0 : ℝ) ≤ 2 ^ q.primeFactors.card := by positivity
  unfold Q0
  calc ‖Eu χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖ * ‖Phi χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖
      ≤ 2 ^ q.primeFactors.card * (Real.pi * CGK 0 * EQh q) := mul_le_mul hE hP (norm_nonneg _) h2
    _ = 2 ^ q.primeFactors.card * (Real.pi * CGK 0) * EQh q := by ring

lemma continuous_H_half : Continuous fun u : ℝ => H ((1 / 2 : ℝ) + u * I) :=
  differentiable_H.continuous.comp (by fun_prop)

lemma continuous_dualS_line {q : ℕ} (χ : DirichletCharacter ℂ q) (Z : ℕ) (σ τ : ℝ) :
    Continuous fun u : ℝ => dualS χ Z (σ + (u - τ) * I) :=
  continuous_iff_continuousAt.2 fun u =>
    ((differentiableAt_dualS χ Z _).continuousAt).comp (f := fun u : ℝ => (σ : ℂ) + (u - τ) * I) (by fun_prop)

/-- **The main part, bounded by its dual sum**: with `D(u) = Σ_{m≤Z}χ⁻¹(m)m^{−1/2+i(u−τ)}`,
`|∫_{(1/2)} H(s + iτ)N^sE(s)Φ(s)D dv| ≤ N^{1/2}Q₀(q)∫|H(1/2 + iu)||D(u)| du` (the substitution `u = v + τ`). -/
lemma norm_integral_Mn_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (τ : ℝ) {N : ℝ} (hN : 0 < N) (Z : ℕ) :
    ‖∫ v : ℝ, Mn χ τ N Z ((1 / 2 : ℝ) + v * I)‖ ≤
      N ^ (1 / 2 : ℝ) * Q0 q * ∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖dualS χ⁻¹ Z ((1 / 2 : ℝ) + (u - τ) * I)‖ := by
  set g : ℝ → ℝ := fun u => ‖H ((1 / 2 : ℝ) + u * I)‖ * ‖dualS χ⁻¹ Z ((1 / 2 : ℝ) + (u - τ) * I)‖ with hg
  have hgc : Continuous g := (continuous_H_half.norm).mul (continuous_dualS_line χ⁻¹ Z (1 / 2) τ).norm
  have hHi : Integrable fun u : ℝ => H ((1 / 2 : ℝ) + u * I) := by
    have h := integrable_H_line (1 / 2) 0
    refine h.congr (Eventually.of_forall fun u => ?_)
    simp
  have hgi : Integrable g := by
    refine (hHi.norm.const_mul (Z : ℝ)).mono' hgc.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hS := norm_dualS_le χ⁻¹ Z (s := (1 / 2 : ℝ) + (u - τ) * I) (by simp; norm_num)
    calc g u ≤ ‖H ((1 / 2 : ℝ) + u * I)‖ * Z := mul_le_mul_of_nonneg_left hS (norm_nonneg _)
      _ = Z * ‖H ((1 / 2 : ℝ) + u * I)‖ := by ring
  have hpt : ∀ v : ℝ, ‖Mn χ τ N Z ((1 / 2 : ℝ) + v * I)‖ ≤ N ^ (1 / 2 : ℝ) * Q0 q * g (v + τ) := by
    intro v
    unfold Mn LinnikCGLReflect.Cf
    have hH : H ((1 / 2 : ℝ) + v * I + τ * I) = H ((1 / 2 : ℝ) + ((v + τ : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    have hD : dualS χ⁻¹ Z ((1 / 2 : ℝ) + v * I) = dualS χ⁻¹ Z ((1 / 2 : ℝ) + (((v + τ : ℝ) : ℂ) - τ) * I) := by
      congr 1; push_cast; ring
    have hNn : ‖(N : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + v * I)‖ = N ^ (1 / 2 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]; simp
    have hEP := norm_EuPhi_half_le χ v
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hH, hD, hNn]
    simp only [hg]
    have hN0 : 0 ≤ N ^ (1 / 2 : ℝ) := by positivity
    calc ‖H ((1 / 2 : ℝ) + ((v + τ : ℝ) : ℂ) * I)‖ * N ^ (1 / 2 : ℝ) *
          ‖Eu χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖ * ‖Phi χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖ *
          ‖dualS χ⁻¹ Z ((1 / 2 : ℝ) + (((v + τ : ℝ) : ℂ) - τ) * I)‖
        = N ^ (1 / 2 : ℝ) * (‖Eu χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖ *
            ‖Phi χ.primitiveCharacter q ((1 / 2 : ℝ) + v * I)‖) *
            (‖H ((1 / 2 : ℝ) + ((v + τ : ℝ) : ℂ) * I)‖ *
              ‖dualS χ⁻¹ Z ((1 / 2 : ℝ) + (((v + τ : ℝ) : ℂ) - τ) * I)‖) := by ring
      _ ≤ N ^ (1 / 2 : ℝ) * Q0 q * (‖H ((1 / 2 : ℝ) + ((v + τ : ℝ) : ℂ) * I)‖ *
              ‖dualS χ⁻¹ Z ((1 / 2 : ℝ) + (((v + τ : ℝ) : ℂ) - τ) * I)‖) := by gcongr
  calc ‖∫ v : ℝ, Mn χ τ N Z ((1 / 2 : ℝ) + v * I)‖ ≤ ∫ v : ℝ, ‖Mn χ τ N Z ((1 / 2 : ℝ) + v * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, N ^ (1 / 2 : ℝ) * Q0 q * g (v + τ) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hgi.comp_add_right τ).const_mul _) (Eventually.of_forall hpt)
    _ = N ^ (1 / 2 : ℝ) * Q0 q * ∫ u : ℝ, g u := by
        rw [integral_const_mul, integral_add_right_eq_self (fun u => g u) τ]

/-- `I_K = ∫|H(−K + iu)|(1 + |u|)^{K+1} du`. -/
def IK (K : ℕ) : ℝ := ∫ u : ℝ, ‖H (((-(K : ℝ) : ℝ) : ℂ) + u * I)‖ * (1 + |u|) ^ (K + 1)

lemma continuous_H_far (K : ℕ) : Continuous fun u : ℝ => H (((-(K : ℝ) : ℝ) : ℂ) + u * I) :=
  differentiable_H.continuous.comp (by fun_prop)

lemma integrable_IK (K : ℕ) :
    Integrable fun u : ℝ => ‖H (((-(K : ℝ) : ℝ) : ℂ) + u * I)‖ * (1 + |u|) ^ (K + 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_H_bound (K + 1) (S := K) (Nat.cast_nonneg K)
  have hc : Continuous fun u : ℝ => ‖H (((-(K : ℝ) : ℝ) : ℂ) + u * I)‖ * (1 + |u|) ^ (K + 1) :=
    (continuous_H_far K).norm.mul ((continuous_const.add continuous_abs).pow _)
  refine ((integrable_inv_one_add_sq).const_mul B).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have h := hB (-(K : ℝ)) u (by simp)
  have hu1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
  have hu0 : 0 < 1 + |u| := by linarith
  rw [Real.norm_of_nonneg (by positivity)]
  have h3 : 1 + u ^ 2 ≤ (1 + |u|) ^ 3 := by
    have hsq : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    rw [hsq]; nlinarith [abs_nonneg u, mul_nonneg (abs_nonneg u) (sq_nonneg |u|)]
  have e : (1 + |u|) ^ (K + 1 + 3) = (1 + |u|) ^ (K + 1) * (1 + |u|) ^ 3 := by ring
  rw [e] at h
  rw [show B * (1 + u ^ 2)⁻¹ = B / (1 + u ^ 2) by ring, le_div_iff₀ (by positivity)]
  calc ‖H (((-(K : ℝ) : ℝ) : ℂ) + u * I)‖ * (1 + |u|) ^ (K + 1) * (1 + u ^ 2)
      ≤ ‖H (((-(K : ℝ) : ℝ) : ℂ) + u * I)‖ * (1 + |u|) ^ (K + 1) * (1 + |u|) ^ 3 := by gcongr
    _ = (1 + |u|) ^ (K + 1) * (1 + |u|) ^ 3 * ‖H (((-(K : ℝ) : ℝ) : ℂ) + u * I)‖ := by ring
    _ ≤ B := h

lemma IK_nonneg (K : ℕ) : 0 ≤ IK K :=
  integral_nonneg fun _ => by positivity

/-- **The tail far left**: `|∫_{(−K)} H(s + iτ)N^sE(s)Φ(s)Σ_{m>Z}χ⁻¹(m)m^{s−1} dv| ≤
2^{ω(q)+1}·π·CGK(K)·EQh(q)·q^{K+1/2}(NZ)^{−K}(1 + |τ|)^{K+1}I_K` for `Z, K ≥ 1`. -/
lemma norm_integral_Tl_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (τ : ℝ) {N : ℝ} (hN : 0 < N) {Z K : ℕ}
    (hZ : 1 ≤ Z) (hK : 1 ≤ K) :
    ‖∫ v : ℝ, Tl χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I)‖ ≤
      2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N * Z) ^ (-(K : ℝ)) * (1 + |τ|) ^ (K + 1) * IK K := by
  set f := χ.conductor with hfdef
  have hf0 : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hfq : (f : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hZ0 : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set A : ℝ := 2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
    (N * Z) ^ (-(K : ℝ)) with hA
  have hA0 : 0 ≤ A := by have := CGK_pos K; have := EQh_pos q; positivity
  set g : ℝ → ℝ := fun u => ‖H (((-(K : ℝ) : ℝ) : ℂ) + u * I)‖ * (1 + |u|) ^ (K + 1) with hg
  have hpt : ∀ v : ℝ, ‖Tl χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I)‖ ≤ A * (1 + |τ|) ^ (K + 1) * g (v + τ) := by
    intro v
    set s : ℂ := ((-(K : ℝ) : ℝ) : ℂ) + v * I with hs
    have hsre : s.re = -(K : ℝ) := by simp [hs]
    have hsim : s.im = v := by simp [hs]
    have hH : H (s + τ * I) = H (((-(K : ℝ) : ℝ) : ℂ) + ((v + τ : ℝ) : ℂ) * I) := by
      congr 1; rw [hs]; push_cast; ring
    have hNn : ‖(N : ℂ) ^ s‖ = N ^ (-(K : ℝ)) := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hN, hsre]
    have hEf := norm_Eu_mul_le (q := q) χ.primitiveCharacter χ.conductor_dvd_level (s := s) (c := K) hK0
      (by rw [hsre]; simp)
    have hP := norm_Phi_le_far χ.primitiveCharacter_isPrimitive q K (s := s) (by rw [hsre]) (by rw [hsre]; linarith)
    rw [hsre, hsim, show (1 / 2 : ℝ) - -(K : ℝ) = (K : ℝ) + 1 / 2 by ring] at hP
    have hT := norm_dualT_le χ⁻¹ hZ hK v
    have hv1 : (1 : ℝ) ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hvK : (1 + |v|) ^ ((K : ℝ) + 1 / 2) ≤ (1 + |τ|) ^ (K + 1) * (1 + |v + τ|) ^ (K + 1) := by
      calc (1 + |v|) ^ ((K : ℝ) + 1 / 2) ≤ (1 + |v|) ^ (K + 1) := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le hv1 (by push_cast; linarith)
        _ ≤ ((1 + |τ|) * (1 + |v + τ|)) ^ (K + 1) :=
            pow_le_pow_left₀ (by positivity) (one_add_abs_le v τ) _
        _ = (1 + |τ|) ^ (K + 1) * (1 + |v + τ|) ^ (K + 1) := mul_pow _ _ _
    have hfK : (f : ℝ) ^ ((K : ℝ) + 1 / 2) = (f : ℝ) ^ (K : ℝ) * (f : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hf0]
    have hfh : (f : ℝ) ^ (1 / 2 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hf0.le hfq (by norm_num)
    have hqK : (q : ℝ) ^ ((K : ℝ) + 1 / 2) = (q : ℝ) ^ (K : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))]
    have hNZ : (N * Z) ^ (-(K : ℝ)) = N ^ (-(K : ℝ)) * (Z : ℝ) ^ (-(K : ℝ)) := Real.mul_rpow hN.le hZ0.le
    unfold Tl LinnikCGLReflect.Cf
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hH, hNn]
    simp only [hg]
    set eE := ‖Eu χ.primitiveCharacter q s‖ with heE
    set eP := ‖Phi χ.primitiveCharacter q s‖ with heP
    set eT := ‖dualT χ⁻¹ Z s‖ with heT
    set eH := ‖H (((-(K : ℝ) : ℝ) : ℂ) + ((v + τ : ℝ) : ℂ) * I)‖ with heH
    have heE0 : 0 ≤ eE := norm_nonneg _
    have heP0 : 0 ≤ eP := norm_nonneg _
    have heH0 : 0 ≤ eH := norm_nonneg _
    have hC := CGK_pos K
    have hEQ := EQh_pos q
    -- `eE·eP ≤ 2^ω q^K f^{1/2}·π·CGK·(1 + |v|)^{K+1/2}·EQh`
    have hEP : eE * eP ≤ 2 ^ q.primeFactors.card * (q : ℝ) ^ (K : ℝ) * (f : ℝ) ^ (1 / 2 : ℝ) *
        (Real.pi * CGK K * (1 + |v|) ^ ((K : ℝ) + 1 / 2)) * EQh q := by
      calc eE * eP ≤ eE * ((f : ℝ) ^ ((K : ℝ) + 1 / 2) * (Real.pi * CGK K * (1 + |v|) ^ ((K : ℝ) + 1 / 2)) *
            EQh q) := mul_le_mul_of_nonneg_left hP heE0
        _ = (eE * (f : ℝ) ^ (K : ℝ)) * (f : ℝ) ^ (1 / 2 : ℝ) *
            (Real.pi * CGK K * (1 + |v|) ^ ((K : ℝ) + 1 / 2)) * EQh q := by rw [hfK]; ring
        _ ≤ (2 ^ q.primeFactors.card * (q : ℝ) ^ (K : ℝ)) * (f : ℝ) ^ (1 / 2 : ℝ) *
            (Real.pi * CGK K * (1 + |v|) ^ ((K : ℝ) + 1 / 2)) * EQh q := by gcongr
    calc eH * N ^ (-(K : ℝ)) * eE * eP * eT = eH * N ^ (-(K : ℝ)) * (eE * eP) * eT := by ring
      _ ≤ eH * N ^ (-(K : ℝ)) * (2 ^ q.primeFactors.card * (q : ℝ) ^ (K : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
            (Real.pi * CGK K * ((1 + |τ|) ^ (K + 1) * (1 + |v + τ|) ^ (K + 1))) * EQh q) *
            (2 * (Z : ℝ) ^ (-(K : ℝ))) := by
          have hEP' : eE * eP ≤ 2 ^ q.primeFactors.card * (q : ℝ) ^ (K : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) *
              (Real.pi * CGK K * ((1 + |τ|) ^ (K + 1) * (1 + |v + τ|) ^ (K + 1))) * EQh q :=
            hEP.trans (by gcongr)
          have h0 : 0 ≤ eH * N ^ (-(K : ℝ)) := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hEP' h0) hT (norm_nonneg _) (by positivity)
      _ = A * (1 + |τ|) ^ (K + 1) * (eH * (1 + |v + τ|) ^ (K + 1)) := by
          rw [hA, hqK, hNZ, pow_succ]; ring
  have hgi : Integrable g := integrable_IK K
  calc ‖∫ v : ℝ, Tl χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I)‖
      ≤ ∫ v : ℝ, ‖Tl χ τ N Z (((-(K : ℝ) : ℝ) : ℂ) + v * I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, A * (1 + |τ|) ^ (K + 1) * g (v + τ) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hgi.comp_add_right τ).const_mul _) (Eventually.of_forall hpt)
    _ = A * (1 + |τ|) ^ (K + 1) * IK K := by
        rw [integral_const_mul, integral_add_right_eq_self (fun u => g u) τ]
        rfl

/-- **A Gram entry, bounded through its reflection**: for `χ_i ≠ χ_k`, with `τ = t_i − t_k` and `Z, K ≥ 1`,
`|G(i, k)| ≤ (2π)⁻¹(N^{1/2}Q₀(q)∫|H(1/2 + iu)||D(u)| du + T_K)`, where
`D(u) = Σ_{m≤Z}(χ_iχ̄_k)⁻¹(m)m^{−1/2+i(u−τ)}` and `T_K` is the bound of `norm_integral_Tl_le`
(round 641's `gram_reflect` with `norm_integral_Mn_le` and `norm_integral_Tl_le`). -/
theorem norm_gram_le {ι : Type*} {q : ℕ} [NeZero q] {N : ℝ} (hN : 0 < N) (χ : ι → DirichletCharacter ℂ q)
    (t : ι → ℝ) {i k : ι} (hik : χ i ≠ χ k) {Z K : ℕ} (hZ : 1 ≤ Z) (hK : 1 ≤ K) :
    ‖gramP N χ t i k‖ ≤ (2 * Real.pi)⁻¹ * (N ^ (1 / 2 : ℝ) * Q0 q *
        (∫ u : ℝ, ‖H ((1 / 2 : ℝ) + u * I)‖ *
          ‖dualS (χ i * (χ k)⁻¹)⁻¹ Z ((1 / 2 : ℝ) + (u - ((t i - t k : ℝ) : ℂ)) * I)‖) +
      2 ^ (q.primeFactors.card + 1) * (Real.pi * CGK K) * EQh q * (q : ℝ) ^ ((K : ℝ) + 1 / 2) *
        (N * Z) ^ (-(K : ℝ)) * (1 + |t i - t k|) ^ (K + 1) * IK K) := by
  rw [gram_reflect hN χ t hik Z hK, norm_mul, norm_mul]
  have h1 : ‖(N : ℂ) ^ (((t i - t k : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]; simp
  have h2 : ‖(1 / (2 * π) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    have e : (1 / (2 * π) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  rw [h1, h2, one_mul]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
  · exact norm_integral_Mn_le _ _ hN Z
  · exact norm_integral_Tl_le _ _ hN hZ hK

end LinnikCGLPair

#print axioms LinnikCGLPair.norm_Eu_mul_le
#print axioms LinnikCGLPair.norm_dualT_le
#print axioms LinnikCGLPair.norm_integral_Mn_le
#print axioms LinnikCGLPair.norm_integral_Tl_le
#print axioms LinnikCGLPair.norm_gram_le
