/-
# Rounds 636–637: the density step from Chen–Gupta–Li's Proposition 3.1, `7/3 + 1/2000` on `[5/7, 16/21]`

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`charDensity_cgl`). Assume `LinnikCGLLV.CGLProp31`. There is `C ≥ 0` such that for every `q ≥ 1`,
`5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most `C(qT)^{(7/3+1/2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of
`L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.

This is round 607's step (`LinnikHuxStep`) with Chen–Gupta–Li's estimate in place of Huxley's, at `parHux73`'s
parameters on `[5/7, 16/21]`. The step uses the estimate only at thresholds `N^σ/Z` with `5/7 ≤ σ ≤ 16/21` and
`Z ≤ N^{1/70}`, inside `[N^{7/10}, N^{4/5}]`, where `LinnikCGLLV.lv_range` gives it from Proposition 3.1.

* `block_bin_cgl`: one dyadic block and one bin of the polynomial class. The power `F^m` normalised at `σ_b`
  (`LinnikTwelve.pv_powCoσ`) is split into the dyadic pieces `(2^jP^m, 2^{j+1}P^m]`; on a piece where it is at least
  `V^m/(m + 1)`, its coefficients scaled by `N^{σ_b}τ₀^{−2m}` are at most `1` (`norm_powCo_le`, `d(n) ≤ τ₀`), and
  `LinnikCGLLV.cgl_shift` counts the characters at the lower threshold `V^mN^σ/((m + 1)τ₀^{2m})`, `σ ≤ σ_b`.
* `p31B_le_Q`, `piece_le`: with `Q^a ≤ N ≤ Q^λ` and `V ≥ N^σ/Z`, `p31B` is at most `Z⁴` times six powers of `Q`,
  its three terms at `x = λ` and `x = a`; under the six conditions `ParC.Good.hc` a piece is at most
  `6CE·Q^{A_i(1−σ)}`.
* `class1_cgl`: the polynomial class, as `LinnikHuxStep.class1_gen` with `block_bin_cgl` in place of
  `block_bin_hux`. The bins have width `e/200` and number `⌊60/e⌋ + 1`, since `1 − σ ≤ 3/10`. The thresholds are
  `N^σ/Z` with `Z ≤ Q^{1/105} ≤ N^{1/70}`, so `N^{7/10} ≤ N^σ/Z ≤ N^{4/5}` for `5/7 ≤ σ ≤ 4/5`.
* `class2_bound_cgl`: the integral class at `δ = 1/5`, which needs `σ ≥ 7/10`; round 607's step takes `δ = 1/4`.
* `count_cgl_at`, `eventually_cgl`, `count_cgl`: the range `[lo, hi]` at one large `Q`, then for every `q` and
  `T ≥ 2`, with `cgl_shift` at `ε = e/400`, the divisor bound `τ₀ = C(ε_d)Q^{2ε_d}`, `ε_d = e/(1600M)`, and
  `K_T = ⌈log 8Q³⌉ + 1` terms of the Taylor series.
* `charDensity_cglGen`, `parCGL`, `parCGL_good`, `charDensity_cgl`: the density estimate, at `parHux73`'s values on
  `[5/7, 16/21]`, with `e = εs`.

Round 702: the step's internal `ε`, `LinnikHuxStep.εs = 1/100000` until then, is a field of the parameters, `ParC.e`,
and `ParC.Good` asks `0 < e ≤ 1/100000`. The proofs use only those two facts of it, so the step holds at every such
`e`; `parCGL` takes `e = εs`, and `charDensity_cgl` is unchanged. Round 702's `LinnikCGLDensity` takes `e` to `0`.

Round 636 took Chen–Gupta–Li's Theorem 1.1 as the hypothesis (`LinnikCGLLV.CGLLargeValues`) and applied it at the
thresholds `N^{σ_b}/Z`, with the bound's fourth term; round 637 lowers the thresholds to `N^σ/Z` and takes
Proposition 3.1 (README round 637).

The file imports `LinnikCGLLV.lean` and `LinnikHuxStep.lean`.
-/

import LinnikCGLLV
import LinnikHuxStep

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

namespace LinnikCGLStep

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag LinnikHuxley LinnikReflect LinnikTwelve LinnikHuxStep LinnikCGLLV

variable {q : ℕ}

/-! ### One block and one bin -/

/-- **One dyadic block and one bin, by Chen–Gupta–Li's estimate.** Let `q ≥ 1` and `hLV` be `cgl_shift`'s count at `q`
with the constant `C` for `ε`. Characters with `|F(χ, β_χ + iγ_χ)| ≥ V > 0` for a block `F` on `(P, 2P]` with
`|c_j| ≤ d(j)`, `σ_b ≤ β_χ ≤ σ_b + η`, `0 ≤ σ ≤ σ_b`, `η ≤ 1/16`, `|γ_χ| ≤ T`, number at most
`Σ_{j≤m} K·Cq^ε(q(T + 1)N_j)^ε p31B(q, T + 1, N_j, W_j/2)` with `N_j = 2^jP^m` and `W_j = V^mN_j^σ/((m + 1)τ₀^{2m})`,
for `m ≥ 1`, `d(n) ≤ τ₀` for `n ≤ (2P)^m`, `(q(T + 1))^{2/3} ≤ P^m`, `K ≥ 1`, `2(2P)^m·16^{−K} ≤ V^m/((m + 1)τ₀^{2m})/4`
and `N_j^{7/10} ≤ W_j/2 ≤ N_j^{4/5}` for `j ≤ m`. -/
theorem block_bin_cgl [NeZero q] {C ε : ℝ}
    (hLV : ∀ (R : Finset (DirichletCharacter ℂ q)) (δ γ : DirichletCharacter ℂ q → ℝ) (T : ℝ) (N : ℕ) (V : ℝ)
      (a : ℕ → ℂ) (K : ℕ), 1 ≤ T → ((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ N → (N : ℝ) ^ (7 / 10 : ℝ) ≤ V / 2 →
      V / 2 ≤ (N : ℝ) ^ (4 / 5 : ℝ) → (∀ n, ‖a n‖ ≤ 1) →
      (∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ 1 / 16) → (∀ χ ∈ R, |γ χ| ≤ T) → 1 ≤ K → 2 * (N : ℝ) * (1 / 16) ^ K ≤ V / 4 →
      (∀ χ ∈ R, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ χ : ℂ) + γ χ * I))‖) →
      (R.card : ℝ) ≤ K * (C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N (V / 2)))
    {R : Finset (DirichletCharacter ℂ q)} {Sk : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : Sk ⊆ Ioc P (2 * P))
    {c : ℕ → ℂ} (hc : ∀ j ∈ Sk, ‖c j‖ ≤ (j.divisors.card : ℝ)) {m : ℕ} (hm : 1 ≤ m)
    {σ σb η : ℝ} (hσ0 : 0 ≤ σ) (hσσb : σ ≤ σb) (hη : η ≤ 1 / 16) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σb ≤ β χ ∧ β χ ≤ σb + η) {T : ℝ} (hT : 0 ≤ T) (hγ : ∀ χ ∈ R, |γ χ| ≤ T) {V : ℝ} (hV : 0 < V)
    (hbig : ∀ χ ∈ R, V ≤ ‖pv Sk c χ ((β χ : ℂ) + γ χ * I)‖) {τ₀ : ℝ}
    (hτ₀ : ∀ n, n ≤ (2 * P) ^ m → (n.divisors.card : ℝ) ≤ τ₀)
    (hPm : ((q : ℝ) * (T + 1)) ^ (2 / 3 : ℝ) ≤ ((P ^ m : ℕ) : ℝ)) {K : ℕ} (hK : 1 ≤ K)
    (htail : 2 * (((2 * P) ^ m : ℕ) : ℝ) * (1 / 16) ^ K ≤ V ^ m / ((m + 1) * τ₀ ^ (2 * m)) / 4)
    (hrange : ∀ j ≤ m, ((2 ^ j * P ^ m : ℕ) : ℝ) ^ (7 / 10 : ℝ) ≤
        V ^ m * ((2 ^ j * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2 ∧
      V ^ m * ((2 ^ j * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2 ≤ ((2 ^ j * P ^ m : ℕ) : ℝ) ^ (4 / 5 : ℝ)) :
    (R.card : ℝ) ≤ ∑ j ∈ range (m + 1), K * (C * (q : ℝ) ^ ε *
      ((q : ℝ) * (T + 1) * ((2 ^ j * P ^ m : ℕ) : ℝ)) ^ ε * p31B q (T + 1) (2 ^ j * P ^ m)
        (V ^ m * ((2 ^ j * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2)) := by
  classical
  have hσb : 0 ≤ σb := hσ0.trans hσσb
  set X : ℕ := P ^ m with hXdef
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hτ1 : 1 ≤ τ₀ := by have := hτ₀ 1 (Nat.one_le_pow _ _ (by omega)); simpa using this
  have hτ0 : 0 < τ₀ := by linarith
  have hsupp := powSupp_sub hS hm
  have h2Pm : (2 * P) ^ m = X * 2 ^ m := by rw [hXdef, mul_pow, mul_comm]
  -- the pieces
  set Sj : ℕ → Finset ℕ := fun j => (powSupp Sk m).filter fun n => blk X n = j with hSjdef
  have hmaps : ∀ n ∈ powSupp Sk m, blk X n ∈ range (m + 1) := by
    intro n hn
    have h := hsupp hn
    rw [h2Pm] at h
    have := blk_lt hX h
    rw [Nat.log_pow (by norm_num)] at this
    exact mem_range.2 this
  have hSjsub : ∀ j, Sj j ⊆ Ioc (2 ^ j * X) (2 * (2 ^ j * X)) := by
    intro j n hn
    obtain ⟨hn1, hnj⟩ := mem_filter.1 hn
    rw [← hnj]
    exact blk_mem hX (mem_Ioc.1 (hsupp hn1)).1
  -- each point's power is large
  set δ : DirichletCharacter ℂ q → ℝ := fun χ => β χ - σb with hδdef
  have hδ : ∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ 1 / 16 := fun χ hχ => ⟨by simp [hδdef]; linarith [(hβ χ hχ).1],
    by simp [hδdef]; linarith [(hβ χ hχ).2]⟩
  have hpow : ∀ χ ∈ R, V ^ m ≤ ‖pv (powSupp Sk m) (powCoσ Sk c m σb) χ ((δ χ : ℂ) + γ χ * I)‖ := by
    intro χ hχ
    rw [pv_powCoσ Sk c m σb χ hS hm, norm_pow]
    have e : σb + δ χ = β χ := by simp [hδdef]
    rw [e]
    exact pow_le_pow_left₀ hV.le (hbig χ hχ) m
  have hsplit : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), pv (powSupp Sk m) (powCoσ Sk c m σb) χ s =
      ∑ j ∈ range (m + 1), pv (Sj j) (powCoσ Sk c m σb) χ s := by
    intro χ s
    unfold pv
    exact (sum_fiberwise_of_maps_to hmaps _).symm
  -- some piece carries `V^m/(m + 1)`
  set W0 : ℝ := V ^ m / (m + 1) with hW0
  have hW00 : 0 < W0 := by positivity
  set Rj : ℕ → Finset (DirichletCharacter ℂ q) :=
    fun j => R.filter fun χ => W0 ≤ ‖pv (Sj j) (powCoσ Sk c m σb) χ ((δ χ : ℂ) + γ χ * I)‖ with hRjdef
  have hcover : R ⊆ (range (m + 1)).biUnion Rj := by
    intro χ hχ
    by_contra hno
    have hlt : ∀ j ∈ range (m + 1), ‖pv (Sj j) (powCoσ Sk c m σb) χ ((δ χ : ℂ) + γ χ * I)‖ < W0 := by
      intro j hj
      by_contra hge
      exact hno (mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hχ, not_lt.1 hge⟩⟩)
    have h1 := hpow χ hχ
    rw [hsplit] at h1
    have h2 : ∑ j ∈ range (m + 1), ‖pv (Sj j) (powCoσ Sk c m σb) χ ((δ χ : ℂ) + γ χ * I)‖ <
        ∑ _j ∈ range (m + 1), W0 := sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ hlt
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : ((m + 1 : ℕ) : ℝ) * W0 = V ^ m := by rw [hW0]; push_cast; field_simp
    linarith [(norm_sum_le _ _).trans_lt (h3 ▸ h2)]
  -- each piece by `hLV`
  have hpiece : ∀ j ∈ range (m + 1), ((Rj j).card : ℝ) ≤ K * (C * (q : ℝ) ^ ε *
      ((q : ℝ) * (T + 1) * ((2 ^ j * P ^ m : ℕ) : ℝ)) ^ ε * p31B q (T + 1) (2 ^ j * P ^ m)
        (V ^ m * ((2 ^ j * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2)) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hj)
    obtain ⟨hr1, hr2⟩ := hrange j hjm
    set N : ℕ := 2 ^ j * P ^ m with hNdef
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    have hXN : X ≤ N := by rw [hNdef, hXdef]; exact Nat.le_mul_of_pos_left _ (by positivity)
    have hN2Pm : N ≤ (2 * P) ^ m := by
      rw [hNdef, h2Pm, hXdef, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjm)
    set sc : ℝ := (N : ℝ) ^ σb / τ₀ ^ (2 * m) with hsc
    have hsc0 : 0 < sc := by positivity
    set a : ℕ → ℂ := fun n => if n ∈ Sj j then powCoσ Sk c m σb n * (sc : ℂ) else 0 with hadef
    have ha : ∀ n, ‖a n‖ ≤ 1 := by
      intro n
      simp only [hadef]
      split_ifs with hn
      · have hn' := hSjsub j hn
        rw [← hNdef] at hn'
        obtain ⟨hn1, hn2⟩ := mem_Ioc.1 hn'
        have hnS := (mem_filter.1 hn).1
        have hnle : n ≤ (2 * P) ^ m := (mem_Ioc.1 (hsupp hnS)).2
        have hnpos : (0 : ℝ) < n := by have : (0 : ℝ) < N := hNr; have : (N : ℝ) < n := by exact_mod_cast hn1
                                       linarith
        have hS0 : 0 ∉ Sk := fun h0 => by have := (mem_Ioc.1 (hS h0)).1; omega
        have hco := norm_powCo_le hS0 hc m hnS
        have hd : ((n.divisors.card : ℝ)) ^ (2 * m) ≤ τ₀ ^ (2 * m) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (hτ₀ n hnle) _
        have hNn : (N : ℝ) ^ σb ≤ (n : ℝ) ^ σb :=
          Real.rpow_le_rpow hNr.le (by exact_mod_cast hn1.le) hσb
        unfold powCoσ
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_real,
          Real.norm_of_nonneg hsc0.le, hsc]
        have hnσ : (n : ℝ) ^ (-σb) * (n : ℝ) ^ σb = 1 := by
          rw [← Real.rpow_add hnpos]; simp
        calc ‖powCo Sk c m n‖ * (n : ℝ) ^ (-σb) * ((N : ℝ) ^ σb / τ₀ ^ (2 * m))
            ≤ τ₀ ^ (2 * m) * (n : ℝ) ^ (-σb) * ((n : ℝ) ^ σb / τ₀ ^ (2 * m)) := by
              gcongr
              exact hco.trans hd
          _ = (n : ℝ) ^ (-σb) * (n : ℝ) ^ σb := by field_simp
          _ = 1 := hnσ
      · simp
    have hsum : ∀ χ : DirichletCharacter ℂ q, ∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ χ : ℂ) + γ χ * I)) =
        (sc : ℂ) * pv (Sj j) (powCoσ Sk c m σb) χ ((δ χ : ℂ) + γ χ * I) := by
      intro χ
      have hsub : Sj j ⊆ Ioc N (2 * N) := by rw [hNdef, ← hXdef]; exact hSjsub j
      rw [← sum_subset hsub (fun n _ hn => by simp only [hadef, hn, ↓reduceIte, zero_mul])]
      unfold pv
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      simp only [hadef, hn, ↓reduceIte]
      ring
    set W : ℝ := V ^ m * (N : ℝ) ^ σb / ((m + 1) * τ₀ ^ (2 * m)) with hWdef
    have hW : W = sc * W0 := by rw [hWdef, hsc, hW0]; field_simp
    have hbigj : ∀ χ ∈ Rj j, W ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ χ : ℂ) + γ χ * I))‖ := by
      intro χ hχ
      rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsc0.le, hW]
      exact mul_le_mul_of_nonneg_left (mem_filter.1 hχ).2 hsc0.le
    -- the lower threshold `V^mN^σ/((m + 1)τ₀^{2m})`
    set W' : ℝ := V ^ m * (N : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) with hW'def
    have hW'W : W' ≤ W := by
      have h1 : (N : ℝ) ^ σ ≤ (N : ℝ) ^ σb := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hσσb
      rw [hW'def, hWdef]
      gcongr
    have hbigj' : ∀ χ ∈ Rj j, W' ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ χ : ℂ) + γ χ * I))‖ :=
      fun χ hχ => hW'W.trans (hbigj χ hχ)
    have hNq : ((q : ℝ) * (T + 1)) ^ (2 / 3 : ℝ) ≤ N :=
      hPm.trans (by exact_mod_cast hXN)
    have htailj : 2 * (N : ℝ) * (1 / 16) ^ K ≤ W' / 4 := by
      have h1 : (N : ℝ) ≤ (((2 * P) ^ m : ℕ) : ℝ) := by exact_mod_cast hN2Pm
      have h2 : V ^ m / ((m + 1) * τ₀ ^ (2 * m)) ≤ W' := by
        rw [hW'def]
        have hN1' : (1 : ℝ) ≤ (N : ℝ) ^ σ := Real.one_le_rpow (by exact_mod_cast hN1) hσ0
        rw [mul_div_right_comm]
        exact le_mul_of_one_le_right (by positivity) hN1'
      calc 2 * (N : ℝ) * (1 / 16) ^ K ≤ 2 * (((2 * P) ^ m : ℕ) : ℝ) * (1 / 16) ^ K := by gcongr
        _ ≤ V ^ m / ((m + 1) * τ₀ ^ (2 * m)) / 4 := htail
        _ ≤ W' / 4 := by gcongr
    have hc' := hLV (Rj j) δ γ (T + 1) N W' a K (by linarith) hNq hr1 hr2 ha
      (fun χ hχ => hδ χ (mem_filter.1 hχ).1) (fun χ hχ => (hγ χ (mem_filter.1 hχ).1).trans (by linarith)) hK
      htailj hbigj'
    simpa only [hNdef, hW'def] using hc'
  calc (R.card : ℝ) ≤ (((range (m + 1)).biUnion Rj).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ j ∈ range (m + 1), ((Rj j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ _ := sum_le_sum hpiece

/-! ### The terms as powers of `Q` -/

/-- `N^e ≤ Q^{λe} + Q^{ae}` for `Q ≥ 1` and `Q^a ≤ N ≤ Q^λ`, whatever the sign of `e`. -/
lemma rpow_le_ends {Q N a lam : ℝ} (hQ1 : 1 ≤ Q) (hN0 : 0 < N) (hlo : Q ^ a ≤ N) (hhi : N ≤ Q ^ lam) (e : ℝ) :
    N ^ e ≤ Q ^ (lam * e) + Q ^ (a * e) := by
  have hQ0 : 0 ≤ Q := by linarith
  rcases le_or_gt 0 e with he | he
  · have h1 : N ^ e ≤ Q ^ (lam * e) := by
      calc N ^ e ≤ (Q ^ lam) ^ e := Real.rpow_le_rpow hN0.le hhi he
        _ = Q ^ (lam * e) := by rw [← Real.rpow_mul hQ0]
    have : 0 ≤ Q ^ (a * e) := by positivity
    linarith
  · have h1 : N ^ e ≤ Q ^ (a * e) := by
      calc N ^ e ≤ (Q ^ a) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) hlo he.le
        _ = Q ^ (a * e) := by rw [← Real.rpow_mul hQ0]
    have : 0 ≤ Q ^ (lam * e) := by positivity
    linarith

/-- `x/V^p ≤ x·Z^p/(N^σ)^p` for `x ≥ 0` and `0 < N^σ/Z ≤ V`. -/
lemma div_pow_le_of {x V Z Nσ : ℝ} (hx : 0 ≤ x) (hZ : 0 < Z) (hNσ : 0 < Nσ) (hV : Nσ / Z ≤ V) (p : ℕ) :
    x / V ^ p ≤ Z ^ p * (x / Nσ ^ p) := by
  have h0 : 0 < Nσ / Z := div_pos hNσ hZ
  calc x / V ^ p ≤ x / (Nσ / Z) ^ p := div_le_div_of_nonneg_left hx (by positivity) (pow_le_pow_left₀ h0.le hV p)
    _ = Z ^ p * (x / Nσ ^ p) := by rw [div_pow]; field_simp

/-- **`p31B` as powers of `Q`**: for `q ≥ 1`, `Q ≥ 1`, `T ≥ 0`, `q(T + 1) ≤ Q`, `N ≥ 1` with `Q^a ≤ N ≤ Q^λ`, `Z ≥ 1`
and `N^σ/Z ≤ V`, `p31B(q, T + 1, N, V)` is at most `Z⁴` times the sum of the six powers `Q^{x(2−2σ)}`,
`Q^{1/2+x(3−4σ)}`, `Q^{4/3+x(2−4σ)}`, `x ∈ {λ, a}`. -/
lemma p31B_le_Q {T Q a lam σ Z V : ℝ} {N : ℕ} [NeZero q] (hT : 0 ≤ T) (hQ1 : 1 ≤ Q)
    (hqT : (q : ℝ) * (T + 1) ≤ Q) (hN1 : 1 ≤ N) (hlo : Q ^ a ≤ N) (hhi : (N : ℝ) ≤ Q ^ lam) (hZ : 1 ≤ Z)
    (hV : (N : ℝ) ^ σ / Z ≤ V) :
    p31B q (T + 1) N V ≤ Z ^ 4 * ((Q ^ (lam * (2 - 2 * σ)) + Q ^ (a * (2 - 2 * σ))) +
      Q ^ (1 / 2 : ℝ) * (Q ^ (lam * (3 - 4 * σ)) + Q ^ (a * (3 - 4 * σ))) +
      Q ^ (4 / 3 : ℝ) * (Q ^ (lam * (2 - 4 * σ)) + Q ^ (a * (2 - 4 * σ)))) := by
  have hQ0 : 0 < Q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNσ : 0 < (N : ℝ) ^ σ := Real.rpow_pos_of_pos hNr σ
  have hZ0 : 0 < Z := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hE := rpow_le_ends hQ1 hNr hlo hhi
  have hZ24 : Z ^ 2 ≤ Z ^ 4 := pow_le_pow_right₀ hZ (by norm_num)
  -- the three terms
  have t1 : (N : ℝ) ^ 2 / V ^ 2 ≤ Z ^ 4 * (Q ^ (lam * (2 - 2 * σ)) + Q ^ (a * (2 - 2 * σ))) := by
    calc (N : ℝ) ^ 2 / V ^ 2 ≤ Z ^ 2 * ((N : ℝ) ^ 2 / ((N : ℝ) ^ σ) ^ 2) :=
          div_pow_le_of (by positivity) hZ0 hNσ hV 2
      _ = Z ^ 2 * (N : ℝ) ^ (2 - 2 * σ) := by
          rw [npow_div_rpow_pow hNr 2 2 σ]; norm_num
      _ ≤ Z ^ 4 * (Q ^ (lam * (2 - 2 * σ)) + Q ^ (a * (2 - 2 * σ))) := by
          gcongr
          · exact hE _
  have t2 : ((q : ℝ) * (T + 1)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ 3 / V ^ 4 ≤
      Z ^ 4 * (Q ^ (1 / 2 : ℝ) * (Q ^ (lam * (3 - 4 * σ)) + Q ^ (a * (3 - 4 * σ)))) := by
    have hq : ((q : ℝ) * (T + 1)) ^ (1 / 2 : ℝ) ≤ Q ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hqT (by norm_num)
    calc ((q : ℝ) * (T + 1)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ 3 / V ^ 4
        ≤ Z ^ 4 * (((q : ℝ) * (T + 1)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ 3 / ((N : ℝ) ^ σ) ^ 4) :=
          div_pow_le_of (by positivity) hZ0 hNσ hV 4
      _ = Z ^ 4 * (((q : ℝ) * (T + 1)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ)) := by
          rw [mul_div_assoc, npow_div_rpow_pow hNr 3 4 σ]; norm_num
      _ ≤ Z ^ 4 * (Q ^ (1 / 2 : ℝ) * (Q ^ (lam * (3 - 4 * σ)) + Q ^ (a * (3 - 4 * σ)))) := by
          gcongr
          exact hE _
  have t3 : ((q : ℝ) * (T + 1)) ^ (4 / 3 : ℝ) * (N : ℝ) ^ 2 / V ^ 4 ≤
      Z ^ 4 * (Q ^ (4 / 3 : ℝ) * (Q ^ (lam * (2 - 4 * σ)) + Q ^ (a * (2 - 4 * σ)))) := by
    have hq : ((q : ℝ) * (T + 1)) ^ (4 / 3 : ℝ) ≤ Q ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hqT (by norm_num)
    calc ((q : ℝ) * (T + 1)) ^ (4 / 3 : ℝ) * (N : ℝ) ^ 2 / V ^ 4
        ≤ Z ^ 4 * (((q : ℝ) * (T + 1)) ^ (4 / 3 : ℝ) * (N : ℝ) ^ 2 / ((N : ℝ) ^ σ) ^ 4) :=
          div_pow_le_of (by positivity) hZ0 hNσ hV 4
      _ = Z ^ 4 * (((q : ℝ) * (T + 1)) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ)) := by
          rw [mul_div_assoc, npow_div_rpow_pow hNr 2 4 σ]; norm_num
      _ ≤ Z ^ 4 * (Q ^ (4 / 3 : ℝ) * (Q ^ (lam * (2 - 4 * σ)) + Q ^ (a * (2 - 4 * σ)))) := by
          gcongr
          exact hE _
  unfold p31B
  linarith

/-- **One piece as a power of `Q`**: for `q ≥ 1`, under `p31B_le_Q`'s conditions, with `λ ≤ 2`, `C, ε ≥ 0`,
`K·Q^{4ε}Z⁴ ≤ E·Q^{e/4}` and the six exponent conditions (`hc`), `K·Cq^ε(q(T + 1)N)^ε p31B(q, T + 1, N, V)` is at most
`6CE·Q^{A_i(1−σ)}`. -/
lemma piece_le {T Q a lam Ai σ Z V C ε E e : ℝ} {N K : ℕ} [NeZero q] (hT : 0 ≤ T) (hQ1 : 1 ≤ Q)
    (hqT : (q : ℝ) * (T + 1) ≤ Q) (hN1 : 1 ≤ N) (hlo : Q ^ a ≤ N) (hhi : (N : ℝ) ≤ Q ^ lam) (hlam2 : lam ≤ 2)
    (hZ : 1 ≤ Z) (hV : (N : ℝ) ^ σ / Z ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hsmall : (K : ℝ) * Q ^ (4 * ε) * Z ^ 4 ≤ E * Q ^ (e / 4))
    (hc : lam * (2 - 2 * σ) + e / 4 ≤ Ai * (1 - σ) ∧ a * (2 - 2 * σ) + e / 4 ≤ Ai * (1 - σ) ∧
      1 / 2 + lam * (3 - 4 * σ) + e / 4 ≤ Ai * (1 - σ) ∧ 1 / 2 + a * (3 - 4 * σ) + e / 4 ≤ Ai * (1 - σ) ∧
      4 / 3 + lam * (2 - 4 * σ) + e / 4 ≤ Ai * (1 - σ) ∧ 4 / 3 + a * (2 - 4 * σ) + e / 4 ≤ Ai * (1 - σ)) :
    K * (C * (q : ℝ) ^ ε * ((q : ℝ) * (T + 1) * N) ^ ε * p31B q (T + 1) N V) ≤ 6 * C * E * Q ^ (Ai * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqQ : (q : ℝ) ≤ Q := le_trans (le_mul_of_one_le_right (by linarith) (by linarith)) hqT
  have hNQ : (N : ℝ) ≤ Q ^ 2 := hhi.trans (by
    calc Q ^ lam ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 hlam2
      _ = Q ^ 2 := by norm_num)
  have hqε : (q : ℝ) ^ ε * ((q : ℝ) * (T + 1) * N) ^ ε ≤ Q ^ (4 * ε) := by
    have h1 : (q : ℝ) ^ ε ≤ Q ^ ε := Real.rpow_le_rpow (by positivity) hqQ hε
    have h2 : ((q : ℝ) * (T + 1) * N) ^ ε ≤ (Q * Q ^ 2) ^ ε :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul hqT hNQ (by positivity) hQ0.le) hε
    have h3 : (Q * Q ^ 2) ^ ε = Q ^ (3 * ε) := by
      rw [show Q * Q ^ 2 = Q ^ (3 : ℝ) by norm_num; ring, ← Real.rpow_mul hQ0.le]
    calc (q : ℝ) ^ ε * ((q : ℝ) * (T + 1) * N) ^ ε ≤ Q ^ ε * Q ^ (3 * ε) := by
          rw [← h3]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Q ^ (4 * ε) := by rw [← Real.rpow_add hQ0]; ring_nf
  -- each of the six powers is at most `Q^{A_i(1−σ)−e/4}`
  set F := Ai * (1 - σ) - e / 4 with hF
  have hp : ∀ x : ℝ, x + e / 4 ≤ Ai * (1 - σ) → Q ^ x ≤ Q ^ F := fun x hx =>
    Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hF]; linarith)
  have hm : ∀ (u x : ℝ), u + x + e / 4 ≤ Ai * (1 - σ) → Q ^ u * Q ^ x ≤ Q ^ F := fun u x hx => by
    rw [← Real.rpow_add hQ0]; exact hp _ (by linarith)
  obtain ⟨c1, c1', c2, c2', c3, c3'⟩ := hc
  have hsum : (Q ^ (lam * (2 - 2 * σ)) + Q ^ (a * (2 - 2 * σ))) +
      Q ^ (1 / 2 : ℝ) * (Q ^ (lam * (3 - 4 * σ)) + Q ^ (a * (3 - 4 * σ))) +
      Q ^ (4 / 3 : ℝ) * (Q ^ (lam * (2 - 4 * σ)) + Q ^ (a * (2 - 4 * σ))) ≤ 6 * Q ^ F := by
    have h1 := hp _ c1
    have h2 := hp _ c1'
    have h3 := hm (1 / 2) _ c2
    have h4 := hm (1 / 2) _ c2'
    have h5 := hm (4 / 3) _ c3
    have h6 := hm (4 / 3) _ c3'
    nlinarith
  have hcg := p31B_le_Q (q := q) hT hQ1 hqT hN1 hlo hhi hZ hV
  have hcg0 : 0 ≤ p31B q (T + 1) N V := p31B_nonneg q (by linarith) N V
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hQF : Q ^ (e / 4) * Q ^ F = Q ^ (Ai * (1 - σ)) := by rw [← Real.rpow_add hQ0, hF]; ring_nf
  calc (K : ℝ) * (C * (q : ℝ) ^ ε * ((q : ℝ) * (T + 1) * N) ^ ε * p31B q (T + 1) N V)
      = C * ((K : ℝ) * ((q : ℝ) ^ ε * ((q : ℝ) * (T + 1) * N) ^ ε) * p31B q (T + 1) N V) := by ring
    _ ≤ C * ((K : ℝ) * Q ^ (4 * ε) * (Z ^ 4 * (6 * Q ^ F))) := by
        gcongr
        exact hcg.trans (by gcongr)
    _ = 6 * C * (((K : ℝ) * Q ^ (4 * ε) * Z ^ 4) * Q ^ F) := by ring
    _ ≤ 6 * C * ((E * Q ^ (e / 4)) * Q ^ F) := by gcongr
    _ = 6 * C * E * Q ^ (Ai * (1 - σ)) := by rw [mul_assoc E, hQF]; ring

/-! ### The parameters -/

/-- The parameters of the step with Chen–Gupta–Li's estimate, as `LinnikHuxStep.Par`, and the internal `ε`, `e`
(round 702). -/
structure ParC where
  M : ℕ
  a : ℝ
  lam : ℝ
  lo : ℝ
  hi : ℝ
  Ai : ℝ
  A : ℝ
  e : ℝ

/-- What the step needs of its parameters, at the internal `ε = e` (round 702; until then `εs = 1/100000`):
`0 < e ≤ 1/100000`, `M ≥ 1`, `2/3 ≤ a` and `a + e ≤ M/2000`, the bounds on `λ`, `5/7 ≤ lo`, `hi ≤ 4/5`,
`0 ≤ A ≤ 10`, and the exponent conditions: on `[lo, hi]` the six of `piece_le` and the integral class's; for every
`σ ≤ hi` the one for the number of dyadic blocks. -/
structure ParC.Good (P : ParC) : Prop where
  he : 0 < P.e
  he1 : P.e ≤ 1 / 100000
  hM : 1 ≤ P.M
  ha : 2 / 3 ≤ P.a
  hat : P.a + P.e ≤ (P.M : ℝ) / 2000
  hlam1 : 201 / 200 + P.e ≤ P.lam
  hlam2 : 3 * (P.a + P.e) / 2 ≤ P.lam
  hlam3 : P.lam ≤ 2
  hlo : 5 / 7 ≤ P.lo
  hhi : P.hi ≤ 4 / 5
  hc : ∀ σ, P.lo ≤ σ → σ ≤ P.hi →
    P.lam * (2 - 2 * σ) + P.e / 4 ≤ P.Ai * (1 - σ) ∧ P.a * (2 - 2 * σ) + P.e / 4 ≤ P.Ai * (1 - σ) ∧
      1 / 2 + P.lam * (3 - 4 * σ) + P.e / 4 ≤ P.Ai * (1 - σ) ∧ 1 / 2 + P.a * (3 - 4 * σ) + P.e / 4 ≤ P.Ai * (1 - σ) ∧
      4 / 3 + P.lam * (2 - 4 * σ) + P.e / 4 ≤ P.Ai * (1 - σ) ∧ 4 / 3 + P.a * (2 - 4 * σ) + P.e / 4 ≤ P.Ai * (1 - σ)
  h3 : ∀ σ, P.lo ≤ σ → σ ≤ P.hi → 201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + P.e) ≤ P.A * (1 - σ)
  h4 : ∀ σ, σ ≤ P.hi → P.e / (24 * P.M) + P.Ai * (1 - σ) ≤ P.A * (1 - σ)
  hA : 0 ≤ P.A
  hA10 : P.A ≤ 10

/-! ### The polynomial class -/

set_option maxHeartbeats 1000000 in
/-- **The polynomial class with Chen–Gupta–Li's estimate on `[lo, hi]`.** Let `q ≥ 1`, the parameters have `Good`, `hLV`
be `cgl_shift`'s count at `q` with the constant `C ≥ 0` for `0 ≤ ε ≤ e/400`, `lo ≤ σ ≤ hi`, `T ≥ 0`, `Q > 1` with
`q(T + 2) ≤ Q`, `X, N ≥ 1` with the sizes of `class1_gen` (`hXQ`, `hK`, `hXN`), `d(n) ≤ τ₀` for `n ≤ Q²` with
`τ₀^{8M} ≤ C_τQ^{e/100}`, `K_T ≥ 1` with `K_T ≤ Q^{e/100}` and `8Q³ ≤ 16^{K_T}`, `2^M ≤ Q^{e}` and
`16(M + 1)⁴C_τQ^{e/4} ≤ Q^{1/105}`. Characters with one point `β_χ + iγ_χ` each, `σ ≤ β_χ < 1`, `|γ_χ| ≤ T`, and
`|P_χ(β_χ + iγ_χ)| ≥ ¼` number at most `(⌊60/e⌋ + 1)K(M + 1)·6C·16(M + 1)⁴C_τ·Q^{A_i(1−σ)}`, `K = ⌊log₂ N⌋ + 1`:
`class1_gen`'s blocks, bins and powers, with `block_bin_cgl` at the thresholds `N_j^σ/Z` and `piece_le`. -/
theorem class1_cgl [NeZero q] (Pa : ParC) (G : Pa.Good) {C ε : ℝ} (hC0 : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hεs : 4 * ε ≤ Pa.e / 100)
    (hLV : ∀ (R : Finset (DirichletCharacter ℂ q)) (δ γ : DirichletCharacter ℂ q → ℝ) (T : ℝ) (N : ℕ) (V : ℝ)
      (a : ℕ → ℂ) (K : ℕ), 1 ≤ T → ((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ N → (N : ℝ) ^ (7 / 10 : ℝ) ≤ V / 2 →
      V / 2 ≤ (N : ℝ) ^ (4 / 5 : ℝ) → (∀ n, ‖a n‖ ≤ 1) →
      (∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ 1 / 16) → (∀ χ ∈ R, |γ χ| ≤ T) → 1 ≤ K → 2 * (N : ℝ) * (1 / 16) ^ K ≤ V / 4 →
      (∀ χ ∈ R, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ χ : ℂ) + γ χ * I))‖) →
      (R.card : ℝ) ≤ K * (C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N (V / 2)))
    {σ T Q : ℝ} (hσ : Pa.lo ≤ σ) (hσ1 : σ ≤ Pa.hi) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXQ : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (Pa.e / (24 * Pa.M)))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + Pa.e))
    {τ₀ Cτ : ℝ} (hτ₀ : ∀ n : ℕ, (n : ℝ) ≤ Q ^ 2 → (n.divisors.card : ℝ) ≤ τ₀)
    (hτC : τ₀ ^ (8 * Pa.M) ≤ Cτ * Q ^ (Pa.e / 100))
    {KT : ℕ} (hKT1 : 1 ≤ KT) (hKTQ : (KT : ℝ) ≤ Q ^ (Pa.e / 100)) (hKT : 8 * Q ^ 3 ≤ (16 : ℝ) ^ KT)
    (h2M : (2 : ℝ) ^ Pa.M ≤ Q ^ Pa.e) (hZQ : 16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ * Q ^ (Pa.e / 4) ≤ Q ^ (1 / 105 : ℝ))
    {Y : ℝ} (hY : 0 < Y) (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ < 1) (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T)
    (hbig : ∀ χ ∈ Rs, 1 / 4 ≤ ‖Pvχ χ X N Y (β χ) (γ χ)‖) :
    (Rs.card : ℝ) ≤ ((⌊60 / Pa.e⌋₊ + 1 : ℕ) : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
      (((Pa.M : ℝ) + 1) * (6 * C * (16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ)) * Q ^ (Pa.Ai * (1 - σ))) := by
  classical
  have hε := G.he
  have hε1 : Pa.e ≤ 1 / 100000 := G.he1
  have hQ0 : 0 < Q := by linarith
  have hlo := G.hlo
  have hhi := G.hhi
  have hMr : (1 : ℝ) ≤ Pa.M := by exact_mod_cast G.hM
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set nb := ⌊60 / Pa.e⌋₊ + 1 with hnb
  set E : ℝ := 16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ with hE
  set Bb := ((Pa.M : ℝ) + 1) * (6 * C * E) * Q ^ (Pa.Ai * (1 - σ)) with hBb
  have hτ1 : 1 ≤ τ₀ := by have := hτ₀ 1 (by rw [Nat.cast_one]; exact one_le_pow₀ hQ1.le); simpa using this
  have hCτ : 0 ≤ Cτ := by
    have h1 : 0 < τ₀ ^ (8 * Pa.M) := by positivity
    have h2 : 0 < Q ^ (Pa.e / 100) := by positivity
    nlinarith
  -- some block of each character is at least `V`
  have hlarge : ∀ χ ∈ Rs, ∃ k ∈ range K, V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ := by
    intro χ hχ
    by_contra hcon
    push Not at hcon
    have h1 := hbig χ hχ
    rw [Pvχ_eq_blocks χ X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkχ χ X N Y k (β χ) (γ χ)‖ < ∑ _k ∈ range K, V :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * V = 1 / 4 := by rw [hV]; field_simp
    linarith [(norm_sum_le (range K) fun k => Fkχ χ X N Y k (β χ) (γ χ)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → ℕ → Finset (DirichletCharacter ℂ q) := fun k j =>
    Rs.filter fun χ => V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ ∧ ⌊200 / Pa.e * (β χ - σ)⌋₊ = j with hCkdef
  have hsub : Rs ⊆ (range K).biUnion fun k => (range nb).biUnion fun j => Ck k j := by
    intro χ hχ
    obtain ⟨k, hk, hbigk⟩ := hlarge χ hχ
    have h1 := hβ χ hχ
    have hj : ⌊200 / Pa.e * (β χ - σ)⌋₊ < nb := by
      have hle : 200 / Pa.e * (β χ - σ) ≤ 60 / Pa.e := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]; linarith
      exact Nat.lt_succ_of_le (Nat.floor_le_floor hle)
    exact mem_biUnion.2 ⟨k, hk, mem_biUnion.2 ⟨_, mem_range.2 hj, mem_filter.2 ⟨hχ, hbigk, rfl⟩⟩⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT1 : (q : ℝ) * (T + 1) ≤ Q := le_trans (mul_le_mul_of_nonneg_left (by linarith) hq0) hqT
  have hCk : ∀ k ∈ range K, ∀ j ∈ range nb, ((Ck k j).card : ℝ) ≤ Bb := by
    intro k hk j _
    set P := 2 ^ k * X with hPdef
    have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ X * N := by
      rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le (mem_range.1 hk) hN)
    have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
    have hSsub : (Ioc X (X * N)).filter (fun j => blk X j = k) ⊆ Ioc P (2 * P) := block_sub hX
    have h2Px : Q ^ (1 / 2000 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
      have : (2 * (X : ℝ)) ≤ ((2 * P : ℕ) : ℝ) := by
        have h := (by omega : 2 * X ≤ 2 * P)
        have h' : ((2 * X : ℕ) : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h' ⊢; linarith
      linarith
    obtain ⟨m, hm1, hmM, hΛlo, hΛhi⟩ :=
      choose_m_gen Pa.M hQ1 (by linarith [G.ha] : (0 : ℝ) < Pa.a + Pa.e) G.hat h2Px
    have hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ Pa.lam := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ Q ^ (201 / 200 + Pa.e) := hXN
          _ ≤ Q ^ Pa.lam := Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam1
      · exact Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam2
    have hΛ2 : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ 2 := by
      calc ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ Pa.lam := hΛ
        _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam3
        _ = Q ^ 2 := by norm_num
    -- `P^m ≥ Q^a`
    have hPmQ : Q ^ Pa.a ≤ ((P ^ m : ℕ) : ℝ) := by
      have h2m : (2 : ℝ) ^ m ≤ Q ^ Pa.e := (pow_le_pow_right₀ (by norm_num) hmM).trans h2M
      have e : ((2 * P : ℕ) : ℝ) ^ m = (2 : ℝ) ^ m * ((P ^ m : ℕ) : ℝ) := by push_cast; ring
      have h1 : Q ^ Pa.a * Q ^ Pa.e ≤ (2 : ℝ) ^ m * ((P ^ m : ℕ) : ℝ) := by
        rw [← Real.rpow_add hQ0, ← e]; exact hΛlo
      have h3 : Q ^ Pa.a * (2 : ℝ) ^ m ≤ Q ^ Pa.a * Q ^ Pa.e := by gcongr
      have h4 : 0 < (2 : ℝ) ^ m := by positivity
      have h5 : Q ^ Pa.a * (2 : ℝ) ^ m ≤ ((P ^ m : ℕ) : ℝ) * (2 : ℝ) ^ m := by
        rw [mul_comm ((P ^ m : ℕ) : ℝ)]; exact h3.trans h1
      exact le_of_mul_le_mul_right h5 h4
    have hPm : ((q : ℝ) * (T + 1)) ^ (2 / 3 : ℝ) ≤ ((P ^ m : ℕ) : ℝ) := by
      calc ((q : ℝ) * (T + 1)) ^ (2 / 3 : ℝ) ≤ Q ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hqT1 (by norm_num)
        _ ≤ Q ^ Pa.a := Real.rpow_le_rpow_of_exponent_le hQ1.le G.ha
        _ ≤ ((P ^ m : ℕ) : ℝ) := hPmQ
    set σb : ℝ := σ + j * (Pa.e / 200) with hσb
    have hσσb : σ ≤ σb := by
      have : (0 : ℝ) ≤ (j : ℝ) * (Pa.e / 200) := by positivity
      rw [hσb]; linarith
    have hbin : ∀ χ ∈ Ck k j, σb ≤ β χ ∧ β χ ≤ σb + Pa.e / 200 := by
      intro χ hχ
      obtain ⟨hχR, -, hbj⟩ := mem_filter.1 hχ
      have h0 : 0 ≤ 200 / Pa.e * (β χ - σ) := by
        have h5 := (hβ χ hχR).1
        have h6 : 0 ≤ β χ - σ := by linarith
        positivity
      have h1 : ((⌊200 / Pa.e * (β χ - σ)⌋₊ : ℕ) : ℝ) ≤ 200 / Pa.e * (β χ - σ) := Nat.floor_le h0
      have h2 : 200 / Pa.e * (β χ - σ) < ((⌊200 / Pa.e * (β χ - σ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hbj] at h1 h2
      constructor
      · have h3 : (j : ℝ) * (Pa.e / 200) ≤ β χ - σ := by
          calc (j : ℝ) * (Pa.e / 200) ≤ (200 / Pa.e * (β χ - σ)) * (Pa.e / 200) := by gcongr
            _ = β χ - σ := by field_simp
        rw [hσb]; linarith
      · have h3 : β χ - σ ≤ ((j : ℝ) + 1) * (Pa.e / 200) := by
          have h4 : 200 / Pa.e * (β χ - σ) ≤ (j : ℝ) + 1 := h2.le
          calc β χ - σ = (200 / Pa.e * (β χ - σ)) * (Pa.e / 200) := by field_simp
            _ ≤ ((j : ℝ) + 1) * (Pa.e / 200) := by gcongr
        rw [hσb]; linarith
    -- the sizes of the block and its power
    have hτ₀' : ∀ n, n ≤ (2 * P) ^ m → (n.divisors.card : ℝ) ≤ τ₀ := by
      intro n hn
      refine hτ₀ n ?_
      have : (n : ℝ) ≤ (((2 * P) ^ m : ℕ) : ℝ) := by exact_mod_cast hn
      push_cast at this hΛ2 ⊢
      linarith
    set Z : ℝ := 2 * ((m : ℝ) + 1) * τ₀ ^ (2 * m) * (4 * (K : ℝ)) ^ m with hZdef
    have hZ1 : 1 ≤ Z := by
      have h1 : 1 ≤ τ₀ ^ (2 * m) := one_le_pow₀ hτ1
      have h2 : 1 ≤ (4 * (K : ℝ)) ^ m := one_le_pow₀ (by linarith)
      have h3 : (1 : ℝ) ≤ 2 * ((m : ℝ) + 1) := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ 2 * ((m : ℝ) + 1) * τ₀ ^ (2 * m) * (4 * (K : ℝ)) ^ m := by gcongr
    have hVZ : V ^ m / (((m : ℝ) + 1) * τ₀ ^ (2 * m)) / 2 = 1 / Z := by
      rw [hV, hZdef, div_pow, one_pow]; field_simp
    have h4K : (4 * (K : ℝ)) ^ (4 * m) ≤ Q ^ (Pa.e / 6) := by
      calc (4 * (K : ℝ)) ^ (4 * m) ≤ (Q ^ (Pa.e / (24 * Pa.M))) ^ (4 * m) := pow_le_pow_left₀ (by positivity) hK _
        _ = Q ^ (Pa.e / (24 * Pa.M) * (4 * m : ℕ)) := by rw [Real.rpow_mul hQ0.le, Real.rpow_natCast]
        _ ≤ Q ^ (Pa.e / 6) := by
            refine Real.rpow_le_rpow_of_exponent_le hQ1.le ?_
            have hm' : (m : ℝ) ≤ Pa.M := by exact_mod_cast hmM
            push_cast
            rw [show Pa.e / (24 * Pa.M) * (4 * m) = Pa.e / 6 * ((m : ℝ) / Pa.M) by field_simp; ring]
            have : (m : ℝ) / Pa.M ≤ 1 := by rw [div_le_one (by positivity)]; exact hm'
            nlinarith
    have hτm : τ₀ ^ (8 * m) ≤ Cτ * Q ^ (Pa.e / 100) :=
      (pow_le_pow_right₀ hτ1 (by omega)).trans hτC
    have hZ4 : Z ^ 4 ≤ E * Q ^ (Pa.e / 100) * Q ^ (Pa.e / 6) := by
      have hm' : (m : ℝ) + 1 ≤ (Pa.M : ℝ) + 1 := by have : (m : ℝ) ≤ Pa.M := by exact_mod_cast hmM
                                                    linarith
      calc Z ^ 4 = 16 * ((m : ℝ) + 1) ^ 4 * τ₀ ^ (8 * m) * (4 * (K : ℝ)) ^ (4 * m) := by
            rw [hZdef]; ring
        _ ≤ 16 * ((Pa.M : ℝ) + 1) ^ 4 * (Cτ * Q ^ (Pa.e / 100)) * Q ^ (Pa.e / 6) := by
            gcongr
        _ = E * Q ^ (Pa.e / 100) * Q ^ (Pa.e / 6) := by rw [hE]; ring
    have hsmall : (KT : ℝ) * Q ^ (4 * ε) * Z ^ 4 ≤ E * Q ^ (Pa.e / 4) := by
      have h1 : Q ^ (4 * ε) ≤ Q ^ (Pa.e / 100) := Real.rpow_le_rpow_of_exponent_le hQ1.le hεs
      have hE0 : 0 ≤ E := by rw [hE]; positivity
      calc (KT : ℝ) * Q ^ (4 * ε) * Z ^ 4
          ≤ Q ^ (Pa.e / 100) * Q ^ (Pa.e / 100) * (E * Q ^ (Pa.e / 100) * Q ^ (Pa.e / 6)) := by
            gcongr
        _ = E * (Q ^ (Pa.e / 100) * Q ^ (Pa.e / 100) * Q ^ (Pa.e / 100) * Q ^ (Pa.e / 6)) := by ring
        _ = E * Q ^ (Pa.e / 100 + Pa.e / 100 + Pa.e / 100 + Pa.e / 6) := by
            rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
        _ ≤ E * Q ^ (Pa.e / 4) := by
            gcongr
            · exact hQ1.le
            · linarith
    have hZQ' : Z ≤ Q ^ (1 / 105 : ℝ) := by
      have h1 : Z ≤ Z ^ 4 := by
        calc Z = Z ^ 1 := (pow_one Z).symm
          _ ≤ Z ^ 4 := pow_le_pow_right₀ hZ1 (by norm_num)
      have h2 : Z ^ 4 ≤ (KT : ℝ) * Q ^ (4 * ε) * Z ^ 4 := by
        have hKT' : (1 : ℝ) ≤ KT := by exact_mod_cast hKT1
        have hQe : 1 ≤ Q ^ (4 * ε) := Real.one_le_rpow hQ1.le (by linarith)
        have : 1 ≤ (KT : ℝ) * Q ^ (4 * ε) := one_le_mul_of_one_le_of_one_le hKT' hQe
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ Z) 4]
      calc Z ≤ E * Q ^ (Pa.e / 4) := h1.trans (h2.trans hsmall)
        _ ≤ Q ^ (1 / 105 : ℝ) := by rw [hE]; exact hZQ
    have hZQ1 : Z ≤ Q := hZQ'.trans (by
      calc Q ^ (1 / 105 : ℝ) ≤ Q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1.le (by norm_num)
        _ = Q := Real.rpow_one Q)
    -- the thresholds `N_i^σ/Z` lie in `[N_i^{7/10}, N_i^{4/5}]`
    have hrange : ∀ i ≤ m, ((2 ^ i * P ^ m : ℕ) : ℝ) ^ (7 / 10 : ℝ) ≤
        V ^ m * ((2 ^ i * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2 ∧
      V ^ m * ((2 ^ i * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2 ≤
        ((2 ^ i * P ^ m : ℕ) : ℝ) ^ (4 / 5 : ℝ) := by
      intro i _
      have hNa : Q ^ Pa.a ≤ ((2 ^ i * P ^ m : ℕ) : ℝ) := by
        refine hPmQ.trans ?_
        have : P ^ m ≤ 2 ^ i * P ^ m := Nat.le_mul_of_pos_left _ (by positivity)
        exact_mod_cast this
      have hN1' : (1 : ℝ) ≤ ((2 ^ i * P ^ m : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
      obtain ⟨Ni, hNi⟩ : ∃ x : ℝ, x = ((2 ^ i * P ^ m : ℕ) : ℝ) := ⟨_, rfl⟩
      rw [← hNi] at hNa hN1' ⊢
      have hNi0 : 0 < Ni := by linarith
      have hZ0 : (0 : ℝ) < Z := by linarith
      have e : V ^ m * Ni ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2 = Ni ^ σ * (1 / Z) := by rw [← hVZ]; ring
      have h1 : Q ^ (1 / 105 : ℝ) ≤ Ni ^ (1 / 70 : ℝ) := by
        calc Q ^ (1 / 105 : ℝ) = (Q ^ (2 / 3 : ℝ)) ^ (1 / 70 : ℝ) := by rw [← Real.rpow_mul hQ0.le]; norm_num
          _ ≤ (Q ^ Pa.a) ^ (1 / 70 : ℝ) :=
              Real.rpow_le_rpow (by positivity) (Real.rpow_le_rpow_of_exponent_le hQ1.le G.ha) (by norm_num)
          _ ≤ Ni ^ (1 / 70 : ℝ) := Real.rpow_le_rpow (by positivity) hNa (by norm_num)
      have h2 : Ni ^ (7 / 10 : ℝ) * Z ≤ Ni ^ σ := by
        calc Ni ^ (7 / 10 : ℝ) * Z ≤ Ni ^ (7 / 10 : ℝ) * Ni ^ (1 / 70 : ℝ) := by
              gcongr
              exact hZQ'.trans h1
          _ = Ni ^ (7 / 10 + 1 / 70 : ℝ) := (Real.rpow_add hNi0 _ _).symm
          _ ≤ Ni ^ σ := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [e]
      constructor
      · rw [mul_one_div, le_div_iff₀ hZ0]
        exact h2
      · calc Ni ^ σ * (1 / Z) ≤ Ni ^ σ * 1 := by
              gcongr
              rw [div_le_one hZ0]
              exact hZ1
          _ = Ni ^ σ := mul_one _
          _ ≤ Ni ^ (4 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have htail : 2 * (((2 * P) ^ m : ℕ) : ℝ) * (1 / 16) ^ KT ≤ V ^ m / (((m : ℝ) + 1) * τ₀ ^ (2 * m)) / 4 := by
      have e2 : V ^ m / (((m : ℝ) + 1) * τ₀ ^ (2 * m)) / 4 = 1 / (2 * Z) := by
        have : V ^ m / (((m : ℝ) + 1) * τ₀ ^ (2 * m)) = 2 / Z := by
          have h := hVZ
          rw [div_div] at h
          have hZ0 : (0 : ℝ) < Z := by linarith
          field_simp at h ⊢
          linarith
        rw [this]; field_simp; ring
      rw [e2]
      have h16 : (1 / 16 : ℝ) ^ KT = 1 / (16 : ℝ) ^ KT := by rw [div_pow, one_pow]
      have hΛ2' : (((2 * P) ^ m : ℕ) : ℝ) ≤ Q ^ 2 := by push_cast at hΛ2 ⊢; exact hΛ2
      have h16pos : (0 : ℝ) < (16 : ℝ) ^ KT := by positivity
      have hZ0 : (0 : ℝ) < Z := by linarith
      rw [h16, le_div_iff₀ (by positivity)]
      calc 2 * (((2 * P) ^ m : ℕ) : ℝ) * (1 / (16 : ℝ) ^ KT) * (2 * Z)
          ≤ 2 * Q ^ 2 * (1 / (8 * Q ^ 3)) * (2 * Q) := by
            gcongr
        _ = 1 / 2 := by field_simp; ring
        _ ≤ 1 := by norm_num
    have hcount := block_bin_cgl (C := C) (ε := ε) hLV hP hSsub (c := b1 X Y) (fun i _ => norm_b1_le X hY i) hm1
      (by linarith : (0 : ℝ) ≤ σ) hσσb (η := Pa.e / 200) (by linarith) β γ hbin hT
      (fun χ hχ => hγ χ (mem_filter.1 hχ).1) hV0
      (fun χ hχ => by rw [← Fkχ_eq_pv]; exact (mem_filter.1 hχ).2.1) hτ₀' hPm hKT1 htail hrange
    refine hcount.trans ?_
    -- each piece
    have hpiece : ∀ i ∈ range (m + 1), (KT : ℝ) * (C * (q : ℝ) ^ ε *
        ((q : ℝ) * (T + 1) * ((2 ^ i * P ^ m : ℕ) : ℝ)) ^ ε * p31B q (T + 1) (2 ^ i * P ^ m)
          (V ^ m * ((2 ^ i * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2)) ≤
        6 * C * E * Q ^ (Pa.Ai * (1 - σ)) := by
      intro i hi
      have him : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
      set Ni : ℕ := 2 ^ i * P ^ m with hNi
      have hNi1 : 1 ≤ Ni := Nat.one_le_iff_ne_zero.2 (by positivity)
      have hNir : (1 : ℝ) ≤ Ni := by exact_mod_cast hNi1
      have hNlo : Q ^ Pa.a ≤ Ni := by
        refine hPmQ.trans ?_
        have : P ^ m ≤ Ni := Nat.le_mul_of_pos_left _ (by positivity)
        exact_mod_cast this
      have hNhi : (Ni : ℝ) ≤ Q ^ Pa.lam := by
        refine le_trans ?_ hΛ
        have : Ni ≤ (2 * P) ^ m :=
          calc Ni = 2 ^ i * P ^ m := rfl
            _ ≤ 2 ^ m * P ^ m := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) him)
            _ = (2 * P) ^ m := (mul_pow 2 P m).symm
        have h' : (Ni : ℝ) ≤ (((2 * P) ^ m : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h' ⊢; exact h'
      have hVi : (Ni : ℝ) ^ σ / Z ≤ V ^ m * (Ni : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2 := by
        have e : V ^ m * (Ni : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2 = (Ni : ℝ) ^ σ * (1 / Z) := by
          rw [← hVZ]; ring
        rw [e]
        exact le_of_eq (by ring)
      exact piece_le (q := q) hT hQ1.le hqT1 hNi1 hNlo hNhi G.hlam3 hZ1 hVi hC0 hε0 hsmall (G.hc σ hσ hσ1)
    calc ∑ i ∈ range (m + 1), (KT : ℝ) * (C * (q : ℝ) ^ ε *
          ((q : ℝ) * (T + 1) * ((2 ^ i * P ^ m : ℕ) : ℝ)) ^ ε * p31B q (T + 1) (2 ^ i * P ^ m)
            (V ^ m * ((2 ^ i * P ^ m : ℕ) : ℝ) ^ σ / ((m + 1) * τ₀ ^ (2 * m)) / 2))
        ≤ ∑ _i ∈ range (m + 1), 6 * C * E * Q ^ (Pa.Ai * (1 - σ)) := sum_le_sum hpiece
      _ = ((m : ℝ) + 1) * (6 * C * E * Q ^ (Pa.Ai * (1 - σ))) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ ((Pa.M : ℝ) + 1) * (6 * C * E * Q ^ (Pa.Ai * (1 - σ))) := by
          have hE0 : 0 ≤ E := by rw [hE]; positivity
          have : (m : ℝ) ≤ Pa.M := by exact_mod_cast hmM
          gcongr
      _ = Bb := by rw [hBb]; ring
  calc (Rs.card : ℝ) ≤ ((range K).biUnion fun k => (range nb).biUnion fun j => Ck k j).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, (((range nb).biUnion fun j => Ck k j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range nb, ((Ck k j).card : ℝ) := by
        gcongr with k hk; exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range nb, Bb := by
        gcongr with k hk j hj; exact hCk k hk j hj
    _ = (nb : ℝ) * (K : ℝ) * Bb := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### The integral class below `3/4` -/

/-- **The integral class as a power of `Q` at `δ = 1/5`**: `LinnikHuxStep.class2_bound_gen` with `δ = 1/5`, for
`σ ≥ 7/10`. -/
lemma class2_bound_cgl {ε C₄ A : ℝ} (hC₄ : 0 ≤ C₄) {σ T Q : ℝ}
    (hQ1 : 1 ≤ Q) (hT : 0 ≤ T) (hqT : (q : ℝ) * (T + 2) ≤ Q) (hε : 0 < ε) {X : ℕ}
    (hXQ : (X : ℝ) ≤ Q ^ (1 / 2000 : ℝ))
    (hexp : 201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + ε) ≤ A * (1 - σ)) :
    27 * (KG * (Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ) / (1 / 5)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      ≤ 27 * (5 * KG) ^ 4 * C₄ * Q ^ (A * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hY : ((Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = Q ^ (201 / 100 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ Q ^ (1 / 500 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (Q ^ (1 / 2000 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXQ 4
      _ = Q ^ (1 / 500 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
  have hM : ((q : ℝ) * (T + 2)) ^ (1 + ε) ≤ Q ^ (1 + ε) := Real.rpow_le_rpow (by positivity) hqT (by linarith)
  calc 27 * (KG * (Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ) / (1 / 5)) ^ 4 * (X : ℝ) ^ 4 *
        (C₄ * ((q : ℝ) * (T + 2)) ^ (1 + ε))
      = 27 * (5 * KG) ^ 4 * C₄ * (((Q ^ (201 / 400 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 *
          ((q : ℝ) * (T + 2)) ^ (1 + ε)) := by ring
    _ ≤ 27 * (5 * KG) ^ 4 * C₄ * (Q ^ (201 / 100 * (1 / 2 - σ)) * Q ^ (1 / 500 : ℝ) * Q ^ (1 + ε)) := by
        rw [hY]; gcongr
    _ = 27 * (5 * KG) ^ 4 * C₄ * Q ^ (201 / 100 * (1 / 2 - σ) + 1 / 500 + (1 + ε)) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    _ ≤ 27 * (5 * KG) ^ 4 * C₄ * Q ^ (A * (1 - σ)) := by
        gcongr

/-! ### One large `Q`, then all -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The range `[lo, hi]` at one large `Q`.** For `q ≥ 1`, as `LinnikHuxStep.count_gen_at`, with `class1_cgl` for the
polynomial class (its sizes `hτ₀` … `hZQ` in place of the large sieve's) and `δ = 1/5` for the integral class: at most
`((⌊60/e⌋ + 1)(M + 1)·6C·16(M + 1)⁴C_τ + 27(5KG)⁴C₄)Q^{A(1−σ)}` characters `χ ≠ 1` mod `q` have a zero in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem count_cgl_at [NeZero q] (Pa : ParC) (G : Pa.Good) {C ε : ℝ} (hC0 : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hεs : 4 * ε ≤ Pa.e / 100)
    (hLV : ∀ (R : Finset (DirichletCharacter ℂ q)) (δ γ : DirichletCharacter ℂ q → ℝ) (T : ℝ) (N : ℕ) (V : ℝ)
      (a : ℕ → ℂ) (K : ℕ), 1 ≤ T → ((q : ℝ) * T) ^ (2 / 3 : ℝ) ≤ N → (N : ℝ) ^ (7 / 10 : ℝ) ≤ V / 2 →
      V / 2 ≤ (N : ℝ) ^ (4 / 5 : ℝ) → (∀ n, ‖a n‖ ≤ 1) →
      (∀ χ ∈ R, 0 ≤ δ χ ∧ δ χ ≤ 1 / 16) → (∀ χ ∈ R, |γ χ| ≤ T) → 1 ≤ K → 2 * (N : ℝ) * (1 / 16) ^ K ≤ V / 4 →
      (∀ χ ∈ R, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * χ n * (n : ℂ) ^ (-((δ χ : ℂ) + γ χ * I))‖) →
      (R.card : ℝ) ≤ K * (C * (q : ℝ) ^ ε * ((q : ℝ) * T * N) ^ ε * p31B q T N (V / 2)))
    {C₄ : ℝ} (hC₄0 : 0 ≤ C₄)
    (h4 : ∀ (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) → ∀ T' : ℝ, 0 ≤ T' →
      ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + Pa.e))
    {σ T Q : ℝ} (hσ : Pa.lo ≤ σ) (hσ1 : σ ≤ Pa.hi) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hY8 : 8 ≤ Y) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hYQ : Y = Q ^ (201 / 400 : ℝ)) (hXU : (X : ℝ) ≤ Q ^ (1 / 2000 : ℝ)) (hXU2 : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (Pa.e / (24 * Pa.M)))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + Pa.e))
    {τ₀ Cτ : ℝ} (hτ₀ : ∀ n : ℕ, (n : ℝ) ≤ Q ^ 2 → (n.divisors.card : ℝ) ≤ τ₀)
    (hτC : τ₀ ^ (8 * Pa.M) ≤ Cτ * Q ^ (Pa.e / 100))
    {KT : ℕ} (hKT1 : 1 ≤ KT) (hKTQ : (KT : ℝ) ≤ Q ^ (Pa.e / 100)) (hKT : 8 * Q ^ 3 ≤ (16 : ℝ) ^ KT)
    (h2M : (2 : ℝ) ^ Pa.M ≤ Q ^ Pa.e) (hZQ : 16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ * Q ^ (Pa.e / 4) ≤ Q ^ (1 / 105 : ℝ)) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ (((⌊60 / Pa.e⌋₊ + 1 : ℕ) : ℝ) * (((Pa.M : ℝ) + 1) * (6 * C * (16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ))) +
          27 * (5 * KG) ^ 4 * C₄) * Q ^ (Pa.A * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hε := G.he
  have hε1 : Pa.e ≤ 1 / 100000 := G.he1
  have hlo := G.hlo
  have hτ1 : 1 ≤ τ₀ := by have := hτ₀ 1 (by rw [Nat.cast_one]; exact one_le_pow₀ hQ1.le); simpa using this
  have hCτ : 0 ≤ Cτ := by
    have h1 : 0 < τ₀ ^ (8 * Pa.M) := by positivity
    have h2 : 0 < Q ^ (Pa.e / 100) := by positivity
    nlinarith
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset (DirichletCharacter ℂ q), Z = univ.filter fun χ : DirichletCharacter ℂ q =>
      χ ≠ 1 ∧ ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := ⟨_, rfl⟩
  rw [← hZ]
  have hch : ∀ χ ∈ Z, ∃ s : ℂ, χ ≠ 1 ∧ σ ≤ s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
    intro χ hχ
    rw [hZ] at hχ
    obtain ⟨hχ1, s, hs1, hs2, hs3⟩ := (mem_filter.1 hχ).2
    refine ⟨s, hχ1, hs1, ?_, hs2, hs3⟩
    by_contra hge
    push Not at hge
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hge hs3
  choose! s0 hs0 using hch
  have hz0 : ∀ χ ∈ Z, LFunction χ (((s0 χ).re : ℂ) + (s0 χ).im * I) = 0 := fun χ hχ => by
    rw [Complex.re_add_im]; exact (hs0 χ hχ).2.2.2.2
  have hdich : ∀ χ ∈ Z, 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖
      ∨ 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := by
    intro χ hχ
    obtain ⟨hχ1, h1, h2, _, _⟩ := hs0 χ hχ
    exact dichotomy hχ1 hX hN hY8 hM (by linarith) h2 (hz0 χ hχ)
  obtain ⟨Z1, hZ1⟩ : ∃ Z1 : Finset (DirichletCharacter ℂ q),
      Z1 = Z.filter fun χ => 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖ := ⟨_, rfl⟩
  obtain ⟨Z2, hZ2⟩ : ∃ Z2 : Finset (DirichletCharacter ℂ q),
      Z2 = Z.filter fun χ => 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := ⟨_, rfl⟩
  have hcover : Z ⊆ Z1 ∪ Z2 := by
    intro χ hχ
    rcases hdich χ hχ with h | h
    · exact mem_union_left _ (hZ1 ▸ mem_filter.2 ⟨hχ, h⟩)
    · exact mem_union_right _ (hZ2 ▸ mem_filter.2 ⟨hχ, h⟩)
  have hm1 : ∀ χ ∈ Z1, χ ∈ Z ∧ 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖ := fun χ hχ => by
    rw [hZ1] at hχ; exact mem_filter.1 hχ
  have hm2 : ∀ χ ∈ Z2, χ ∈ Z ∧ 1 / 4 ≤ ‖Ivχ χ X Y (((s0 χ).re : ℂ) + (s0 χ).im * I)‖ := fun χ hχ => by
    rw [hZ2] at hχ; exact mem_filter.1 hχ
  have hc1 := class1_cgl Pa G hC0 hε0 hεs hLV hσ hσ1 hT hQ1 hqT hX hN hXU2 hK hXN hτ₀ hτC hKT1 hKTQ hKT h2M hZQ
    (by linarith : (0 : ℝ) < Y) Z1 (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => ⟨(hs0 χ (hm1 χ hχ).1).2.1, (hs0 χ (hm1 χ hχ).1).2.2.1⟩)
    (fun χ hχ => (hs0 χ (hm1 χ hχ).1).2.2.2.1)
    (fun χ hχ => (hm1 χ hχ).2)
  have hc2 := class2_count_small hε.le (by linarith) hC₄0 h4 hX (δ := 1 / 5) (by norm_num)
    (by linarith : 1 / 2 + 1 / 5 ≤ σ) hT (by linarith : (1 : ℝ) ≤ Y) Z2
    (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => by
      obtain ⟨hχ1, h1, h2, h3, _⟩ := hs0 χ (hm2 χ hχ).1
      exact ⟨hχ1, h1, h2, h3, hz0 χ (hm2 χ hχ).1, (hm2 χ hχ).2⟩)
  have hb2 := class2_bound_cgl (q := q) (σ := σ) (A := Pa.A) hC₄0 hQ1.le hT hqT hε (X := X) hXU
    (G.h3 σ hσ hσ1)
  rw [hYQ] at hc2
  have hB0 : 0 ≤ ((Pa.M : ℝ) + 1) * (6 * C * (16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ)) := by positivity
  have hI := absorb_K_gen (Mp := Pa.M) (A := Pa.A) hQ1.le (by positivity) hB0 (Nat.cast_nonneg _) hK
    (G.h4 σ hσ1) hc1
  have hII : (Z2.card : ℝ) ≤ 27 * (5 * KG) ^ 4 * C₄ * Q ^ (Pa.A * (1 - σ)) := hc2.trans hb2
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card := by exact_mod_cast card_union_le Z1 Z2
    _ ≤ ((⌊60 / Pa.e⌋₊ + 1 : ℕ) : ℝ) * (((Pa.M : ℝ) + 1) * (6 * C * (16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ))) *
          Q ^ (Pa.A * (1 - σ)) + 27 * (5 * KG) ^ 4 * C₄ * Q ^ (Pa.A * (1 - σ)) := add_le_add hI hII
    _ = _ := by ring

/-- The conditions on `Q` that `count_cgl` uses, for all large `Q`: `eventually_gen`'s first four, `2^M ≤ Q^ε`,
`5(1 + log Q) ≤ Q^{ε/100}` and `16(M + 1)⁴C_τQ^{ε/4} ≤ Q^{1/105}`. -/
lemma eventually_cgl (Mp : ℕ) (hMp : 1 ≤ Mp) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (Cτ : ℝ) :
    ∀ᶠ Q : ℝ in atTop, (8 : ℝ) ^ 2000 ≤ Q ∧ 4 * (1 + 2 * Real.log Q) ≤ Q ^ (ε / (24 * Mp)) ∧
      (2 * (23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)))) ^ 2 ≤ Q ^ (201 / 200 + ε) ∧
      23 * Q ^ (201 / 400 : ℝ) * Real.log (Q ^ (201 / 400 : ℝ)) ≤ Q ∧ (2 : ℝ) ^ Mp ≤ Q ^ ε ∧
      5 * (1 + Real.log Q) ≤ Q ^ (ε / 100) ∧ 16 * ((Mp : ℝ) + 1) ^ 4 * Cτ * Q ^ (ε / 4) ≤ Q ^ (1 / 105 : ℝ) := by
  filter_upwards [eventually_gen Mp hMp hε (le_refl (1 : ℝ)), ev_log_pow ((2 : ℝ) ^ Mp) ε 0 hε,
    ev_log_pow 5 (ε / 100) 1 (by positivity),
    ev_log_pow (16 * ((Mp : ℝ) + 1) ^ 4 * Cτ) (1 / 105 - ε / 4) 0 (by linarith),
    eventually_ge_atTop (1 : ℝ)] with Q h h5 h6 h7 hQ1
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  simp only [pow_zero, mul_one, pow_one] at h5 h6 h7
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  calc 16 * ((Mp : ℝ) + 1) ^ 4 * Cτ * Q ^ (ε / 4) ≤ Q ^ (1 / 105 - ε / 4) * Q ^ (ε / 4) := by gcongr
    _ = Q ^ (1 / 105 : ℝ) := by rw [← Real.rpow_add hQ0]; norm_num

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The range `[lo, hi]`.** Under `CGLProp31`, for parameters with `Good`, there is `C ≥ 0` such that for every
`q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2` at most `C Q^{A(1−σ)}`, `Q = q(T + 6)`, characters `χ ≠ 1` mod `q` have a zero of
`L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. As `LinnikHuxStep.count_gen`, with `cgl_shift` at `ε = e/400`, the divisor
bound `τ₀ = C(ε_d)Q^{2ε_d}`, `ε_d = e/(1600M)`, and `K_T = ⌈log 8Q³⌉ + 1` terms of the Taylor series. -/
theorem count_cgl (hLVh : CGLProp31) (Pa : ParC) (G : Pa.Good) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), Pa.lo ≤ σ → σ ≤ Pa.hi → 2 ≤ T →
      ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ C * ((q : ℝ) * (T + 6)) ^ (Pa.A * (1 - σ)) := by
  have hε := G.he
  have hε1 : Pa.e ≤ 1 / 100000 := G.he1
  have hMr : (1 : ℝ) ≤ Pa.M := by exact_mod_cast G.hM
  obtain ⟨C, hC0, hC⟩ := cgl_shift hLVh (ε := Pa.e / 400) (div_pos hε (by norm_num))
    (by rw [div_le_one (by norm_num)]; linarith)
  obtain ⟨C₄', hC₄'⟩ := LinnikFourth.fourth_moment hε (by linarith : Pa.e ≤ 1)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = max C₄' 0 := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := hC₄ ▸ le_max_right _ _
  have h4all : ∀ (q : ℕ) [NeZero q] (R : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ R, χ ≠ 1) →
      ∀ T' : ℝ, 0 ≤ T' → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ R, |t χ| ≤ T') →
        ∑ χ ∈ R, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C₄ * ((q : ℝ) * (T' + 2)) ^ (1 + Pa.e) := by
    intro q _ R hR T' hT' t ht
    refine (hC₄' q R hR T' hT' t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₄ ▸ le_max_left _ _) (by positivity)
  -- the divisor bound's constants
  set εd : ℝ := Pa.e / (1600 * Pa.M) with hεd
  have hεd0 : 0 < εd := by positivity
  have hεd1 : εd ≤ 1 := by rw [hεd, div_le_one (by positivity)]; nlinarith
  set Cτ : ℝ := Cdiv εd ^ (8 * Pa.M) with hCτdef
  have hCτ0 : 0 ≤ Cτ := by have := one_le_Cdiv hεd0 hεd1; positivity
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (eventually_cgl Pa.M G.hM hε (by linarith) Cτ)
  have hKG := KG_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((⌊60 / Pa.e⌋₊ + 1 : ℕ) : ℝ) * (((Pa.M : ℝ) + 1) * (6 * C *
      (16 * ((Pa.M : ℝ) + 1) ^ 4 * Cτ))) + 27 * (5 * KG) ^ 4 * C₄ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨max Q₀ 0 + B, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) * (T + 6) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ8 : 8 ≤ Q := by
    rw [hQ]
    calc (8 : ℝ) = 1 * 8 := by norm_num
      _ ≤ (q : ℝ) * (T + 6) := mul_le_mul hq1 (by linarith) (by norm_num) (by positivity)
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Pa.A * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by
    rw [hE]; exact mul_nonneg G.hA (by linarith [G.hhi])
  have hQE : 1 ≤ Q ^ E := Real.one_le_rpow hQ1 hE0
  rcases lt_or_ge Q Q₀ with hsmall | hlarge
  · have hBQ : 0 ≤ B * Q ^ E := by positivity
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ max Q₀ 0 := hsmall.le.trans (le_max_left _ _)
      _ ≤ max Q₀ 0 * Q ^ E := le_mul_of_one_le_right (le_max_right _ _) hQE
      _ ≤ (max Q₀ 0 + B) * Q ^ E := by rw [add_mul]; linarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hQ₀ Q hlarge
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Q ^ (1 / 2000 : ℝ) := ⟨_, rfl⟩
  have hU8 : 8 ≤ U := by
    rw [hU]
    calc (8 : ℝ) = ((8 : ℝ) ^ 2000) ^ (1 / 2000 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ Q ^ (1 / 2000 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hYQ : Yw 502 U = Q ^ (201 / 400 : ℝ) := by rw [hU]; exact Yw_gen hQ0
  have hX : 1 ≤ Xw U := Xw_one hU8
  have hN : 1 ≤ Nw 502 U := Nw_one
  have hY8 : 8 ≤ Yw 502 U := le_trans hU8 (Yw_ge (by norm_num) hU8)
  have hM : 22 * Yw 502 U * Real.log (Yw 502 U) ≤ ((Xw U * Nw 502 U : ℕ) : ℝ) := XN_ge hU8
  have hXNle : ((Xw U * Nw 502 U : ℕ) : ℝ) ≤ 23 * Yw 502 U * Real.log (Yw 502 U) := XN_le (by norm_num) hU8
  have hXU : (Xw U : ℝ) ≤ Q ^ (1 / 2000 : ℝ) := hU ▸ Xw_le hU8
  have hXU2 : Q ^ (1 / 2000 : ℝ) ≤ 2 * (Xw U : ℝ) := by have := Xw_half hU8; rw [← hU]; linarith
  have hXr : (1 : ℝ) ≤ Xw U := by exact_mod_cast hX
  have hNQ : (Nw 502 U : ℝ) ≤ Q := by
    have h1 : (Nw 502 U : ℝ) ≤ ((Xw U * Nw 502 U : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    rw [hYQ] at hXNle
    linarith
  have hK : 4 * ((Nat.log 2 (Nw 502 U) + 1 : ℕ) : ℝ) ≤ Q ^ (Pa.e / (24 * Pa.M)) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNQ) (by norm_num)).trans h2
  have hXN : (2 * ((Xw U * Nw 502 U : ℕ) : ℝ)) ^ 2 ≤ Q ^ (201 / 200 + Pa.e) := by
    refine le_trans ?_ h3
    rw [← hYQ]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hqT : (q : ℝ) * (T + 2) ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- the divisor bound up to `Q²`
  set τ₀ : ℝ := Cdiv εd * Q ^ (2 * εd) with hτ₀def
  have hτ₀ : ∀ n : ℕ, (n : ℝ) ≤ Q ^ 2 → (n.divisors.card : ℝ) ≤ τ₀ := by
    intro n hn
    refine (card_divisors_le hεd0 hεd1 n).trans ?_
    have hCd := one_le_Cdiv hεd0 hεd1
    have : (n : ℝ) ^ εd ≤ Q ^ (2 * εd) := by
      calc (n : ℝ) ^ εd ≤ (Q ^ 2) ^ εd := Real.rpow_le_rpow (Nat.cast_nonneg n) hn hεd0.le
        _ = Q ^ (2 * εd) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
    rw [hτ₀def]; gcongr
  have hτC : τ₀ ^ (8 * Pa.M) ≤ Cτ * Q ^ (Pa.e / 100) := by
    rw [hτ₀def, mul_pow, hCτdef]
    have e : (Q ^ (2 * εd)) ^ (8 * Pa.M) = Q ^ (Pa.e / 100) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le, hεd]; congr 1; push_cast; field_simp; ring
    rw [e]
  -- the Taylor terms
  set KT : ℕ := ⌈Real.log (8 * Q ^ 3)⌉₊ + 1 with hKTdef
  have hl8 : 0 ≤ Real.log (8 * Q ^ 3) := Real.log_nonneg (by nlinarith [pow_le_pow_left₀ (by norm_num) hQ1 3])
  have hKT1 : 1 ≤ KT := by omega
  have hKTQ : (KT : ℝ) ≤ Q ^ (Pa.e / 100) := by
    have hc : (⌈Real.log (8 * Q ^ 3)⌉₊ : ℝ) < Real.log (8 * Q ^ 3) + 1 := Nat.ceil_lt_add_one hl8
    have hlog : Real.log (8 * Q ^ 3) = Real.log 8 + 3 * Real.log Q := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have hl8' : Real.log 8 ≤ 3 := by
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
      have := Real.log_two_lt_d9; linarith
    have hlQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
    calc (KT : ℝ) = (⌈Real.log (8 * Q ^ 3)⌉₊ : ℝ) + 1 := by rw [hKTdef]; push_cast; ring
      _ ≤ 5 * (1 + Real.log Q) := by linarith
      _ ≤ Q ^ (Pa.e / 100) := h6
  have hKT : 8 * Q ^ 3 ≤ (16 : ℝ) ^ KT := by
    have he : Real.exp 1 ≤ 16 := by have := Real.exp_one_lt_d9; linarith
    have h1 : Real.exp (KT : ℝ) ≤ (16 : ℝ) ^ KT := by
      rw [show (KT : ℝ) = (KT : ℝ) * 1 by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le he KT
    have h2 : Real.log (8 * Q ^ 3) ≤ KT := by
      calc Real.log (8 * Q ^ 3) ≤ ⌈Real.log (8 * Q ^ 3)⌉₊ := Nat.le_ceil _
        _ ≤ KT := by rw [hKTdef]; push_cast; linarith
    calc 8 * Q ^ 3 = Real.exp (Real.log (8 * Q ^ 3)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (KT : ℝ) := Real.exp_le_exp.2 h2
      _ ≤ (16 : ℝ) ^ KT := h1
  have hcount := count_cgl_at (q := q) Pa G hC0 (div_nonneg hε.le (by norm_num)) (le_of_eq (by ring)) (hC q) hC₄0
    (h4all q)
    (σ := σ) (T := T) (Q := Q) hσ hσ1 (le_trans (by norm_num) hT) (lt_of_lt_of_le (by norm_num) hQ8) hqT hX hN hY8 hM
    hYQ hXU hXU2 hK hXN hτ₀ hτC
    hKT1 hKTQ hKT h5 h7
  rw [← hE, ← hB] at hcount
  calc _ ≤ B * Q ^ E := hcount
    _ ≤ (max Q₀ 0 + B) * Q ^ E := by
        have : 0 ≤ max Q₀ 0 * Q ^ E := by positivity
        rw [add_mul]; linarith

open scoped Classical in
/-- **A density estimate over the characters mod `q` with exponent `A` on `[lo, hi]`, under `CGLProp31`**: for
parameters with `Good`, there is `C ≥ 0` such that for every `q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2` at most
`C(qT)^{A(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`: `count_cgl`
measured at `Q = q(T + 6) ≤ 4qT`, plus the trivial character, as `LinnikHuxStep.charDensity_gen`. -/
theorem charDensity_cglGen (hLVh : CGLProp31) (Pa : ParC) (G : Pa.Good) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), Pa.lo ≤ σ → σ ≤ Pa.hi → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (Pa.A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  obtain ⟨CT, hCT0, hCT⟩ := count_cgl hLVh Pa G
  refine ⟨2 ^ 10 + 256 * 2 ^ 10 * CT, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hlo := G.hlo
  have hhi := G.hhi
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((q : ℝ) * T) := ⟨_, rfl⟩
  rw [← hℓdef]
  have hℓ : 1 / 2 ≤ ℓ := hℓdef ▸ half_le_log hqT
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Pa.A * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg G.hA (by linarith)
  have hE4 : E ≤ 4 := by
    rw [hE]
    have h1 : 1 - σ ≤ 3 / 10 := by linarith
    have h2 := G.hA10
    nlinarith [G.hA]
  have hpowE : 0 ≤ ((q : ℝ) * T) ^ E := by positivity
  have hpowE1 : 1 ≤ ((q : ℝ) * T) ^ E := Real.one_le_rpow (by linarith) hE0
  have e10 : ℓ ^ (10 : ℝ) = ℓ ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e10]
  have h2ℓ : 1 ≤ 2 ^ 10 * ℓ ^ 10 := by
    have h1 : 1 ≤ (2 * ℓ) ^ 10 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) ≤ (2 * ℓ) ^ 10 := h1
      _ = 2 ^ 10 * ℓ ^ 10 := by ring
  have hℓ10 : 0 ≤ ℓ ^ 10 := by positivity
  have hsub : (univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
      ⊆ insert 1 (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) := by
    intro χ hχ
    rw [mem_insert]
    by_cases h1 : χ = 1
    · exact Or.inl h1
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, h1, (mem_filter.1 hχ).2⟩)
  have hcard := (card_le_card hsub).trans (card_insert_le _ _)
  have hF : ((univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) + 1 := by exact_mod_cast hcard
  have h1 : 1 ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := one_le_mul_of_one_le_of_one_le hpowE1 h2ℓ
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 256 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by positivity) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (4 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 256 * ((q : ℝ) * T) ^ E := by norm_num
  have hZ := hCT q σ T hσ hσ1 hT
  rw [← hE] at hZ
  have hstep : CT * ((q : ℝ) * (T + 6)) ^ E ≤ 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by
    calc CT * ((q : ℝ) * (T + 6)) ^ E ≤ CT * (256 * ((q : ℝ) * T) ^ E) := by gcongr
      _ = 256 * CT * ((q : ℝ) * T) ^ E * 1 := by ring
      _ ≤ 256 * CT * ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) :=
          mul_le_mul_of_nonneg_left h2ℓ (by positivity)
      _ = 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
  calc _ ≤ _ := hF
    _ ≤ CT * ((q : ℝ) * (T + 6)) ^ E + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
    _ ≤ (2 ^ 10 + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith

/-! ### The step on `[5/7, 16/21]` -/

/-- The parameters of the step `7/3 + 1/2000` on `[5/7, 16/21]`: `LinnikHuxStep.parHux73`'s power trick (target
`Q^{7/9+3ε}`, powers `m ≤ 1556`, `λ = 7/6 + 9ε/2`) and inner exponent `7/3 + 25ε`, on the range of
`LinnikCGL.CGLDensity`. -/
def parCGL : ParC where
  M := 1556
  a := 7 / 9 + 2 * εs
  lam := 7 / 6 + 9 / 2 * εs
  lo := 5 / 7
  hi := 16 / 21
  Ai := 7 / 3 + 25 * εs
  A := 7 / 3 + 1 / 2000
  e := εs

theorem parCGL_good : parCGL.Good where
  he := εs_pos
  he1 := by simp only [parCGL]; exact le_refl _
  hM := by simp [parCGL]
  ha := by simp only [parCGL, εs]; norm_num
  hat := by simp only [parCGL, εs]; norm_num
  hlam1 := by simp only [parCGL, εs]; norm_num
  hlam2 := by simp only [parCGL, εs]; norm_num
  hlam3 := by simp only [parCGL, εs]; norm_num
  hlo := by simp only [parCGL]; norm_num
  hhi := by simp only [parCGL]; norm_num
  hc := by
    intro σ h1 h2
    simp only [parCGL, εs] at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  h3 := by
    intro σ h1 h2
    simp only [parCGL, εs] at *
    linarith
  h4 := by
    intro σ h2
    simp only [parCGL, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parCGL]; norm_num
  hA10 := by simp only [parCGL]; norm_num

open scoped Classical in
/-- **Chen–Gupta–Li's density step `7/3 + 1/2000` on `[5/7, 16/21]`, from their Proposition 3.1**: under
`CGLProp31` there is `C ≥ 0` such that for every `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2` at most
`C(qT)^{(7/3+1/2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_cgl (hLVh : CGLProp31) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 7 ≤ σ → σ ≤ 16 / 21 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((7 / 3 + 1 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_cglGen hLVh parCGL parCGL_good

end LinnikCGLStep

#print axioms LinnikCGLStep.charDensity_cgl
