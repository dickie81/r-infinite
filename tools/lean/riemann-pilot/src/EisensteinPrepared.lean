import MellinRowDep
import EisensteinSquarefreeRows

/-! # The prepared sums in mean square, from the quadratic large sieve (round 340)

S5d of round 312's plan, part 2: the analytic core of the companion paper's proof of its Lemma 6.6, with its
Lemma 6.5 (Goldmakher and Louvel's quadratic large sieve) displayed as a hypothesis.

* **`QuadLargeSieve`**: the paper's Lemma 6.5, displayed, for rows `k` squarefree, primary and prime to `6`
  with `N(k) ≤ H` and columns `n` squarefree and primary with `U/2 ≤ N(n) ≤ 2U`.
* **The prepared sums** (`prepTerm`, `prepSum`): the paper's (6.15),
  `𝒮_m[A, Y](k) = Σ_{𝔫, 𝔟} 3^{−m/3}A(𝔫, 𝔟)χ_k(nb)³/(√N𝔫·N𝔟)·V^♯(3^m N𝔫N𝔟³H₀²/(Y N(k)²))`, over all pairs of
  ideals, with the transformed weight in logarithmic coordinates, `V^♯(x) = h(log x)`. It converges
  absolutely when `|h(w)| ≤ N_w(1 + e^w)^{−A}` with `A > 1/2` (`norm_prepTerm_le`, `summable_prepTerm`).
* **The dyadic blocks** (`prepBlock`, `hasSum_prepBlock`): `𝔟` in `[2^i, 2^{i+1})` and `𝔫` weighted by
  `V(N𝔫/2^j)`; the prepared sum is the sum of its blocks.
* **One block in mean square** (`prepBlock_meanSquare`, the paper's (6.20)): Cauchy–Schwarz in `𝔟`, then
  the weights that depend on the row with the large sieve at the columns of the block
  (`blockInner_meanSquare`, `blockCols_largeSieve`).
* **`prepSum_meanSquare`**: for `|c_m(k)| ≤ 1`, `|A_m| ≤ a` and `A ≥ 1/2 + σ`,
  `Σ_k |Σ_{m ≥ −4} c_m(k)𝒮_m[A_m, Y](k)|² ≤ K·a²N_w²(H₀^{1+σ}Y^{2σ} + H₀^σY^{1+2σ})`, by Minkowski's
  inequality over the blocks and three geometric series (`block_majorant`, `hasSum_geom3`).
* Ideals of norm prime to `3` have primary generators (`exists_primary_gen3`); `Σ_𝔞 N𝔞^{−s}` converges for
  `s > 1` (`summable_absNorm_rpow`); a shell `a ≤ N𝔞 ≤ ca` carries harmonic mass at most `c(2κ+5)`
  (`sum_shell_inv_le`).
-/

open Complex MeasureTheory Set NumberField Ideal UniqueFactorizationMonoid
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section

namespace Eis

/-! ### Dyadic shells of ideals -/

open Classical in
/-- **A shell carries bounded harmonic mass**: `Σ_{a ≤ N𝔞 ≤ ca} 1/N𝔞 ≤ c(2κ+5)` for `a > 0` and
`ca ≥ 1`. -/
theorem sum_shell_inv_le {a c : ℝ} (ha : 0 < a) (hca : 1 ≤ c * a) :
    ∑ I ∈ (idealsLe (c * a)).filter (fun I => a ≤ (absNorm I : ℝ)), 1 / (absNorm I : ℝ) ≤
      c * (2 * kappa + 5) := by
  have hk := kappa_pos
  have hterm : ∀ I ∈ (idealsLe (c * a)).filter (fun I => a ≤ (absNorm I : ℝ)),
      1 / (absNorm I : ℝ) ≤ 1 / a := by
    intro I hI
    rw [Finset.mem_filter] at hI
    exact one_div_le_one_div_of_le ha hI.2
  have hcard : (((idealsLe (c * a)).filter (fun I => a ≤ (absNorm I : ℝ))).card : ℝ) ≤
      (2 * kappa + 5) * (c * a) := by
    have h1 : ((idealsLe (c * a)).filter (fun I => a ≤ (absNorm I : ℝ))).card ≤
        (idealsLe (c * a)).card := Finset.card_filter_le _ _
    have h2 : ((idealsLe (c * a)).card : ℝ) ≤ (2 * kappa + 5) * (c * a) := by
      rw [card_idealsLe]; exact idealCount_le hca
    exact le_trans (by exact_mod_cast h1) h2
  calc ∑ I ∈ (idealsLe (c * a)).filter (fun I => a ≤ (absNorm I : ℝ)), 1 / (absNorm I : ℝ)
      ≤ ∑ _I ∈ (idealsLe (c * a)).filter (fun I => a ≤ (absNorm I : ℝ)), 1 / a :=
        Finset.sum_le_sum hterm
    _ = (((idealsLe (c * a)).filter (fun I => a ≤ (absNorm I : ℝ))).card : ℝ) * (1 / a) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * kappa + 5) * (c * a) * (1 / a) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = c * (2 * kappa + 5) := by field_simp

open Classical in
/-- **`Σ_𝔞 N𝔞^{−s}` converges for `s > 1`**: the partial sums over `N𝔞 ≤ 2^{L}` are at most
`2(2κ+5)/(1 − 2^{1−s})`, by dyadic shells. -/
theorem sum_idealsLe_rpow_le {s : ℝ} (hs : 1 < s) (x : ℝ) :
    ∑ I ∈ idealsLe x, (absNorm I : ℝ) ^ (-s) ≤ 2 * (2 * kappa + 5) / (1 - (2 : ℝ) ^ (1 - s)) := by
  set L := Nat.log 2 ⌊x⌋₊
  set lv : Ideal (𝓞 K) → ℕ := fun I => Nat.log 2 (absNorm I) with hlv
  have hmaps : ∀ I ∈ idealsLe x, lv I ∈ Finset.range (L + 1) := by
    intro I hI
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (mem_idealsLe.1 hI).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hk := kappa_pos
  have hr0 : 0 ≤ (2 : ℝ) ^ (1 - s) := by positivity
  have hr1 : (2 : ℝ) ^ (1 - s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : ∀ j : ℕ, (2 : ℝ) * (2 : ℝ) ^ j * ((2 : ℝ) ^ j) ^ (-s) = 2 * ((2 : ℝ) ^ (1 - s)) ^ j := by
    intro j
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_assoc, ← Real.rpow_add (by norm_num)]
    congr 2; ring
  calc ∑ j ∈ Finset.range (L + 1), ∑ I ∈ idealsLe x with lv I = j, (absNorm I : ℝ) ^ (-s)
      ≤ ∑ j ∈ Finset.range (L + 1), 2 * (2 * kappa + 5) * ((2 : ℝ) ^ (1 - s)) ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hsub : (idealsLe x).filter (fun I => lv I = j) ⊆ idealsLe ((2 : ℝ) ^ (j + 1)) := by
          intro I hI
          rw [Finset.mem_filter] at hI
          rw [mem_idealsLe]
          have h0 := (mem_idealsLe.1 hI.1).1
          have h1 : absNorm I < 2 ^ (j + 1) := by
            rw [← hI.2]; exact Nat.lt_pow_succ_log_self (by norm_num) _
          have hf : ⌊(2 : ℝ) ^ (j + 1)⌋₊ = 2 ^ (j + 1) := by
            rw [show (2 : ℝ) ^ (j + 1) = ((2 ^ (j + 1) : ℕ) : ℝ) by push_cast; ring,
              Nat.floor_natCast]
          rw [hf]; exact ⟨h0, h1.le⟩
        have hterm : ∀ I ∈ (idealsLe x).filter (fun I => lv I = j),
            (absNorm I : ℝ) ^ (-s) ≤ ((2 : ℝ) ^ j) ^ (-s) := by
          intro I hI
          rw [Finset.mem_filter] at hI
          have h0 := (mem_idealsLe.1 hI.1).1
          have h1 : 2 ^ j ≤ absNorm I := by
            rw [← hI.2]; exact Nat.pow_log_le_self 2 h0.ne'
          have h1' : (2 : ℝ) ^ j ≤ absNorm I := by exact_mod_cast h1
          exact Real.rpow_le_rpow_of_nonpos (by positivity) h1' (by linarith)
        calc ∑ I ∈ idealsLe x with lv I = j, (absNorm I : ℝ) ^ (-s)
            ≤ ∑ _I ∈ (idealsLe x).filter (fun I => lv I = j), ((2 : ℝ) ^ j) ^ (-s) :=
              Finset.sum_le_sum hterm
          _ = ((idealsLe x).filter (fun I => lv I = j)).card * ((2 : ℝ) ^ j) ^ (-s) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((2 * kappa + 5) * (2 : ℝ) ^ (j + 1)) * ((2 : ℝ) ^ j) ^ (-s) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (((idealsLe x).filter (fun I => lv I = j)).card : ℝ)
                  ≤ ((idealsLe ((2 : ℝ) ^ (j + 1))).card : ℝ) := by
                    exact_mod_cast Finset.card_le_card hsub
                _ = idealCount ((2 : ℝ) ^ (j + 1)) := by rw [card_idealsLe]
                _ ≤ (2 * kappa + 5) * (2 : ℝ) ^ (j + 1) :=
                    idealCount_le (one_le_pow₀ (by norm_num))
          _ = 2 * (2 * kappa + 5) * ((2 : ℝ) ^ (1 - s)) ^ j := by
              rw [pow_succ]; linear_combination (2 * kappa + 5) * hgeom j
    _ = 2 * (2 * kappa + 5) * ∑ j ∈ Finset.range (L + 1), ((2 : ℝ) ^ (1 - s)) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (2 * kappa + 5) * (1 - (2 : ℝ) ^ (1 - s))⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← tsum_geometric_of_lt_one hr0 hr1]
        exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun j _ => by positivity
    _ = 2 * (2 * kappa + 5) / (1 - (2 : ℝ) ^ (1 - s)) := by rw [div_eq_mul_inv]

theorem rpow_neg_absNorm_bot {s : ℝ} (hs : 0 < s) : (absNorm (⊥ : Ideal (𝓞 K)) : ℝ) ^ (-s) = 0 := by
  rw [absNorm_bot, Nat.cast_zero, Real.zero_rpow (by linarith)]

open Classical in
/-- **`Σ_𝔞 N𝔞^{−s}` converges for `s > 1`.** -/
theorem summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun I : Ideal (𝓞 K) => (absNorm I : ℝ) ^ (-s) := by
  refine summable_of_sum_le (c := 2 * (2 * kappa + 5) / (1 - (2 : ℝ) ^ (1 - s)))
    (fun I => by positivity) fun F => ?_
  set x : ℝ := ((F.sup fun I => absNorm I : ℕ) : ℝ)
  have hsub : F.filter (fun I => I ≠ ⊥) ⊆ idealsLe x := by
    intro I hI
    rw [Finset.mem_filter] at hI
    rw [mem_idealsLe]
    refine ⟨Nat.pos_of_ne_zero fun h => hI.2 (absNorm_eq_zero_iff.1 h), ?_⟩
    rw [Nat.floor_natCast]
    exact Finset.le_sup (f := fun I => absNorm I) hI.1
  calc ∑ I ∈ F, (absNorm I : ℝ) ^ (-s) = ∑ I ∈ F.filter (fun I => I ≠ ⊥), (absNorm I : ℝ) ^ (-s) := by
        rw [Finset.sum_filter_of_ne]
        intro I _ hI h
        rw [h, rpow_neg_absNorm_bot (by linarith)] at hI
        exact hI rfl
    _ ≤ ∑ I ∈ idealsLe x, (absNorm I : ℝ) ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun I _ _ => by positivity
    _ ≤ _ := sum_idealsLe_rpow_le hs x

/-! ### Primary generators of the ideals prime to `3` -/

/-- A prime factor of an ideal of norm prime to `3` does not contain `3`. -/
theorem three_not_mem_of_factor {I P : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3)
    (hP : P ∈ normalizedFactors I) : (3 : 𝓞 K) ∉ P := by
  intro h3
  have hPprime := prime_of_normalized_factor P hP
  have hPI : P ∣ I := dvd_of_mem_normalizedFactors hP
  have hNPI : absNorm P ∣ absNorm I := absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPI)
  have hNP3 : absNorm P ∣ 9 := by
    have e : absNorm (span {((3 : ℕ) : 𝓞 K)}) = 3 ^ 2 := absNorm_natCast_span_sq 3
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← e]
    refine absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    simpa using h3
  have hc : (absNorm P).Coprime 9 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact (Nat.Coprime.coprime_dvd_left hNPI hI).pow_right 2
  have h1 : absNorm P = 1 := Nat.Coprime.eq_one_of_dvd hc hNP3
  exact (Ideal.isPrime_of_prime hPprime).ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem ne_bot_of_coprime3 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) : I ≠ ⊥ := by
  intro h; rw [h, absNorm_bot] at hI; norm_num at hI

/-- Every ideal of norm prime to `3` has a primary generator. -/
theorem exists_primary_gen3 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) :
    ∃ a, Primary a ∧ span {a} = I := by
  have hspec : ∀ P ∈ normalizedFactors I, Primary (pgen P) ∧ span {pgen P} = P := by
    intro P hP
    have := isMaximal_of_factor hP
    exact pgen_maximal P (three_not_mem_of_factor hI hP)
  refine ⟨((normalizedFactors I).map pgen).prod, primary_multiset_prod fun x hx => ?_, ?_⟩
  · obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
    exact (hspec P hP).1
  · rw [← Ideal.multiset_prod_span_singleton, Multiset.map_map]
    have e : (normalizedFactors I).map ((fun x => span {x}) ∘ pgen) = normalizedFactors I := by
      conv_rhs => rw [← Multiset.map_id (normalizedFactors I)]
      exact Multiset.map_congr rfl fun P hP => (hspec P hP).2
    rw [e]
    exact Ideal.prod_normalizedFactors_eq_self (ne_bot_of_coprime3 hI)

theorem pgen_spec3 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) :
    Primary (pgen I) ∧ span {pgen I} = I := pgen_spec (exists_primary_gen3 hI)

/-! ### The quadratic large sieve (displayed) -/

/-- **The companion paper's Lemma 6.5** (Goldmakher and Louvel's quadratic large sieve), displayed:
for every `ε > 0` there is `C` such that, for `H, U ≥ 1`, rows `k` squarefree, primary, prime to `6`
with `N(k) ≤ H`, and columns `n` squarefree and primary with `U/2 ≤ N(n) ≤ 2U`,
`Σ_k |Σ_n β(n)χ_k(n)³|² ≤ C(HU)^ε(H + U)Σ_n|β(n)|²`, where `χ_k(n) = (n/k)₆`. -/
def QuadLargeSieve : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ H U : ℝ, 1 ≤ H → 1 ≤ U → ∀ (Ks Ns : Finset (𝓞 K)) (β : 𝓞 K → ℂ),
    (∀ k ∈ Ks, Primary k ∧ Squarefree (span {k}) ∧ (absNorm (span {k})).Coprime 6 ∧
      (absNorm (span {k}) : ℝ) ≤ H) →
    (∀ n ∈ Ns, Primary n ∧ Squarefree (span {n}) ∧ U / 2 ≤ (absNorm (span {n}) : ℝ) ∧
      (absNorm (span {n}) : ℝ) ≤ 2 * U) →
    ∑ k ∈ Ks, ‖∑ n ∈ Ns, β n * sym6 n (span {k}) ^ 3‖ ^ 2 ≤
      C * (H * U) ^ ε * (H + U) * ∑ n ∈ Ns, ‖β n‖ ^ 2

/-! ### The prepared sums -/

/-- The term of the prepared sum `𝒮_m[A, Y](k₀)` (the companion paper's (6.15)) at the ideals
`𝔫, 𝔟`, with the transformed weight in logarithmic coordinates, `V^♯(x) = h(log x)`:
`3^{−m/3}·A(𝔫, 𝔟)χ_{k₀}(nb)³/(√N𝔫·N𝔟)·V^♯(3^m N𝔫 N𝔟³ H₀²/(Y N(k₀)²))`. -/
def prepTerm (h : ℝ → ℂ) (Y H₀ : ℝ) (m : ℤ) (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : 𝓞 K)
    (n b : Ideal (𝓞 K)) : ℂ :=
  (((3 : ℝ) ^ (-(m : ℝ) / 3) : ℝ) : ℂ) * A n b * sym6 (pgen n * pgen b) (span {k}) ^ 3 /
      (((Real.sqrt (absNorm n) * absNorm b : ℝ)) : ℂ) *
    h (Real.log ((3 : ℝ) ^ m * absNorm n * (absNorm b : ℝ) ^ 3 * H₀ ^ 2 /
      (Y * (absNorm (span {k}) : ℝ) ^ 2)))

open Classical in
/-- The ideals `𝔟` with `2^i ≤ N𝔟 < 2^{i+1}`. -/
def shellB (i : ℕ) : Finset (Ideal (𝓞 K)) :=
  (idealsLe ((2 : ℝ) ^ (i + 1))).filter fun b => (2 : ℝ) ^ i ≤ absNorm b ∧ (absNorm b : ℝ) < 2 ^ (i + 1)

/-- **A dyadic block of the prepared sum**: `𝔟` in `[2^i, 2^{i+1})` and `𝔫` weighted by
`V(N𝔫/2^j)`. -/
def prepBlock (h : ℝ → ℂ) (Y H₀ : ℝ) (m : ℤ) (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : 𝓞 K)
    (j i : ℕ) : ℂ :=
  ∑ b ∈ shellB i, ∑ n ∈ idealsLe ((2 : ℝ) ^ (j + 1)),
    prepTerm h Y H₀ m A k n b * (MellinSep.dyadicBump ((absNorm n : ℝ) / 2 ^ j) : ℂ)

/-- The scale of the separated weight in the block `(j, i)`: `R = 3^m 2^j N𝔟³ H₀²/(Y N(k)²)`. -/
def blockScale (Y H₀ : ℝ) (m : ℤ) (k : 𝓞 K) (j : ℕ) (b : Ideal (𝓞 K)) : ℝ :=
  (3 : ℝ) ^ m * 2 ^ j * (absNorm b : ℝ) ^ 3 * H₀ ^ 2 / (Y * (absNorm (span {k}) : ℝ) ^ 2)

open Classical in
/-- The columns of the block `(j, i)` at `𝔟`: `2^{j−1} ≤ N𝔫 ≤ 2^{j+1}` with `A(𝔫, 𝔟) ≠ 0`. -/
def blockCols (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (j : ℕ) (b : Ideal (𝓞 K)) :
    Finset (Ideal (𝓞 K)) :=
  (idealsLe ((2 : ℝ) ^ (j + 1))).filter fun n => (2 : ℝ) ^ j / 2 ≤ absNorm n ∧ A n b ≠ 0

/-- The row coefficient of the block: `A(𝔫, 𝔟)χ_k(n)³/√N𝔫`. -/
def blockCoef (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (b : Ideal (𝓞 K)) (k : 𝓞 K)
    (n : Ideal (𝓞 K)) : ℂ :=
  A n b * sym6 (pgen n) (span {k}) ^ 3 / ((Real.sqrt (absNorm n) : ℝ) : ℂ)

/-- The inner sum of the block at `𝔟`: `F_𝔟(k) = Σ_𝔫 A(𝔫, 𝔟)χ_k(n)³/√N𝔫 · g_{k}(log(N𝔫/2^j))` with
`g_k = logWeight h (log R)`. -/
def blockInner (h : ℝ → ℂ) (Y H₀ : ℝ) (m : ℤ) (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : 𝓞 K)
    (j : ℕ) (b : Ideal (𝓞 K)) : ℂ :=
  ∑ n ∈ blockCols A j b, blockCoef A b k n *
    MellinSep.logWeight h (Real.log (blockScale Y H₀ m k j b)) (Real.log ((absNorm n : ℝ) / 2 ^ j))

/-- **The term identity**: `prepTerm·V(N𝔫/2^j) = 3^{−m/3}/N𝔟 · χ_k(b)³ · A χ_k(n)³/√N𝔫 · g_k(log(N𝔫/2^j))`. -/
theorem prepTerm_mul_bump (h : ℝ → ℂ) {Y H₀ : ℝ} (hY : 0 < Y) (hH : 0 < H₀) (m : ℤ)
    (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) {k : 𝓞 K} (hk : 0 < (absNorm (span {k}) : ℝ)) (j : ℕ)
    {n b : Ideal (𝓞 K)} (hn : 0 < (absNorm n : ℝ)) (hb : 0 < (absNorm b : ℝ)) :
    prepTerm h Y H₀ m A k n b * (MellinSep.dyadicBump ((absNorm n : ℝ) / 2 ^ j) : ℂ) =
      (((3 : ℝ) ^ (-(m : ℝ) / 3) / absNorm b : ℝ) : ℂ) * (sym6 (pgen b) (span {k}) ^ 3 *
        (blockCoef A b k n * MellinSep.logWeight h (Real.log (blockScale Y H₀ m k j b))
          (Real.log ((absNorm n : ℝ) / 2 ^ j)))) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hR : 0 < blockScale Y H₀ m k j b := by unfold blockScale; positivity
  have hx : 0 < (absNorm n : ℝ) / 2 ^ j := by positivity
  have harg : Real.log ((absNorm n : ℝ) / 2 ^ j) + Real.log (blockScale Y H₀ m k j b) =
      Real.log ((3 : ℝ) ^ m * absNorm n * (absNorm b : ℝ) ^ 3 * H₀ ^ 2 /
        (Y * (absNorm (span {k}) : ℝ) ^ 2)) := by
    rw [← Real.log_mul hx.ne' hR.ne']
    congr 1
    unfold blockScale
    field_simp
  unfold prepTerm blockCoef MellinSep.logWeight
  rw [Real.exp_log hx, harg, sym6_mul_left, mul_pow]
  have hsq : (Real.sqrt (absNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hn).ne'
  have hbne : ((absNorm b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast
  field_simp

theorem prepTerm_eq_zero_of (h : ℝ → ℂ) (Y H₀ : ℝ) (m : ℤ) (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : 𝓞 K) {n b : Ideal (𝓞 K)} (hA : A n b = 0) : prepTerm h Y H₀ m A k n b = 0 := by
  unfold prepTerm; rw [hA]; ring

theorem mem_shellB {i : ℕ} {b : Ideal (𝓞 K)} (hb : b ∈ shellB i) :
    (2 : ℝ) ^ i ≤ absNorm b ∧ (absNorm b : ℝ) < 2 ^ (i + 1) := by
  classical
  unfold shellB at hb
  exact (Finset.mem_filter.1 hb).2

theorem absNorm_pos_of_mem_shellB {i : ℕ} {b : Ideal (𝓞 K)} (hb : b ∈ shellB i) :
    0 < (absNorm b : ℝ) := lt_of_lt_of_le (by positivity) (mem_shellB hb).1

theorem absNorm_pos_of_mem_idealsLe {x : ℝ} {n : Ideal (𝓞 K)} (hn : n ∈ idealsLe x) :
    0 < (absNorm n : ℝ) := by exact_mod_cast (mem_idealsLe.1 hn).1

/-- **The block through its inner sums**: `prepBlock(k) = Σ_𝔟 3^{−m/3}/N𝔟 · χ_k(b)³ · F_𝔟(k)`. -/
theorem prepBlock_eq (h : ℝ → ℂ) {Y H₀ : ℝ} (hY : 0 < Y) (hH : 0 < H₀) (m : ℤ)
    (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) {k : 𝓞 K} (hk : 0 < (absNorm (span {k}) : ℝ))
    (j i : ℕ) :
    prepBlock h Y H₀ m A k j i = ∑ b ∈ shellB i,
      (((3 : ℝ) ^ (-(m : ℝ) / 3) / absNorm b : ℝ) : ℂ) *
        (sym6 (pgen b) (span {k}) ^ 3 * blockInner h Y H₀ m A k j b) := by
  classical
  unfold prepBlock
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbpos := absNorm_pos_of_mem_shellB hb
  have hsub : blockCols A j b ⊆ idealsLe ((2 : ℝ) ^ (j + 1)) := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub]
  · unfold blockInner
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact prepTerm_mul_bump h hY hH m A hk j (absNorm_pos_of_mem_idealsLe (hsub hn)) hbpos
  · intro n hn hnc
    unfold blockCols at hnc
    rw [Finset.mem_filter, not_and, not_and_or, not_ne_iff] at hnc
    rcases hnc hn with hlt | hA
    · rw [MellinSep.dyadicBump_div_eq_zero (Or.inl (not_le.1 hlt).le), Complex.ofReal_zero,
        mul_zero]
    · rw [prepTerm_eq_zero_of h Y H₀ m A k hA, zero_mul]

theorem absNorm_pos_of_coprime6 {k : 𝓞 K} (hk : (absNorm (span {k})).Coprime 6) :
    0 < (absNorm (span {k}) : ℝ) := by
  have : absNorm (span {k}) ≠ 0 := fun h0 => by rw [h0] at hk; norm_num at hk
  exact_mod_cast Nat.pos_of_ne_zero this

theorem absNorm_le_of_mem_idealsLe {x : ℝ} (hx : 0 ≤ x) {n : Ideal (𝓞 K)} (hn : n ∈ idealsLe x) :
    (absNorm n : ℝ) ≤ x :=
  le_trans (by exact_mod_cast (mem_idealsLe.1 hn).2) (Nat.floor_le hx)

/-- **The large sieve at the columns of a block**: the twisted inner sums
`Σ_𝔫 A(𝔫, 𝔟)χ_k(n)³/√N𝔫·(N𝔫/2^j)^{2πit}` have mean square over the rows at most
`C(H₀2^j)^σ(H₀ + 2^j)·4(2κ+5)a²`, uniformly in `t`. -/
theorem blockCols_largeSieve (hLS : QuadLargeSieve) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (H₀ : ℝ), 1 ≤ H₀ → ∀ (Af : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (a : ℝ),
      (∀ n b, ‖Af n b‖ ≤ a) → (∀ n b, Af n b ≠ 0 → Squarefree n ∧ (absNorm n).Coprime 3) →
      ∀ Ks : Finset (𝓞 K), (∀ k ∈ Ks, Primary k ∧ Squarefree (span {k}) ∧
        (absNorm (span {k})).Coprime 6 ∧ (absNorm (span {k}) : ℝ) ≤ H₀) →
      ∀ (j : ℕ) (b : Ideal (𝓞 K)) (t : ℝ),
      ∑ k ∈ Ks, ‖∑ n ∈ blockCols Af j b, blockCoef Af b k n *
          ((((absNorm n : ℝ) / 2 ^ j : ℝ) : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I))‖ ^ 2 ≤
        C * ((H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j)) * (a ^ 2 * (4 * (2 * kappa + 5))) := by
  classical
  obtain ⟨C, hC⟩ := hLS σ hσ
  refine ⟨max C 0, le_max_right _ _, fun H₀ hH Af a ha hAf Ks hKs j b t => ?_⟩
  set cols := blockCols Af j b with hcols
  set e : Ideal (𝓞 K) → ℂ := fun n =>
    (((absNorm n : ℝ) / 2 ^ j : ℝ) : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * I) with he
  set βI : Ideal (𝓞 K) → ℂ := fun n => Af n b / ((Real.sqrt (absNorm n) : ℝ) : ℂ) * e n with hβI
  set βE : 𝓞 K → ℂ := fun x => βI (span {x}) with hβE
  have hmem : ∀ n ∈ cols, n ∈ idealsLe ((2 : ℝ) ^ (j + 1)) ∧ (2 : ℝ) ^ j / 2 ≤ absNorm n ∧
      Af n b ≠ 0 := by
    intro n hn
    simp only [hcols, blockCols, Finset.mem_filter] at hn
    exact ⟨hn.1, hn.2.1, hn.2.2⟩
  have hspec : ∀ n ∈ cols, Primary (pgen n) ∧ span {pgen n} = n ∧ Squarefree n := by
    intro n hn
    obtain ⟨hsq, h3⟩ := hAf n b (hmem n hn).2.2
    exact ⟨(pgen_spec3 h3).1, (pgen_spec3 h3).2, hsq⟩
  have hinj : Set.InjOn pgen (cols : Set (Ideal (𝓞 K))) := by
    intro n1 hn1 n2 hn2 h12
    rw [← (hspec n1 hn1).2.1, ← (hspec n2 hn2).2.1, h12]
  have hpos : ∀ n ∈ cols, 0 < (absNorm n : ℝ) := fun n hn =>
    absNorm_pos_of_mem_idealsLe (hmem n hn).1
  have hnorm_e : ∀ n ∈ cols, ‖e n‖ = 1 := fun n hn =>
    MellinSep.norm_cpow_tI _ t (by have := hpos n hn; positivity)
  -- the twisted sums through the element columns
  have hsum : ∀ k, ∑ n ∈ cols, blockCoef Af b k n * e n =
      ∑ x ∈ cols.image pgen, βE x * sym6 x (span {k}) ^ 3 := by
    intro k
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hβE, hβI, blockCoef, (hspec n hn).2.1]
    ring
  have hU : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hrows := hKs
  have hcolsE : ∀ x ∈ cols.image pgen, Primary x ∧ Squarefree (span {x}) ∧
      (2 : ℝ) ^ j / 2 ≤ (absNorm (span {x}) : ℝ) ∧ (absNorm (span {x}) : ℝ) ≤ 2 * 2 ^ j := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hp, hsp, hsq⟩ := hspec n hn
    refine ⟨hp, by rw [hsp]; exact hsq, by rw [hsp]; exact (hmem n hn).2.1, ?_⟩
    rw [hsp]
    have := absNorm_le_of_mem_idealsLe (by positivity) (hmem n hn).1
    rwa [pow_succ, mul_comm] at this
  have hLSapp := hC H₀ (2 ^ j) hH hU Ks (cols.image pgen) βE hrows hcolsE
  -- the column mass
  have hmass : ∑ x ∈ cols.image pgen, ‖βE x‖ ^ 2 ≤ a ^ 2 * (4 * (2 * kappa + 5)) := by
    rw [Finset.sum_image hinj]
    have hterm : ∀ n ∈ cols, ‖βE (pgen n)‖ ^ 2 ≤ a ^ 2 * (1 / (absNorm n : ℝ)) := by
      intro n hn
      simp only [hβE, hβI, (hspec n hn).2.1]
      rw [norm_mul, hnorm_e n hn, mul_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (hpos n hn).le, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha n b) 2)
        (by have := hpos n hn; positivity)
    have hsub : cols ⊆ (idealsLe (4 * ((2 : ℝ) ^ j / 2))).filter
        (fun n => (2 : ℝ) ^ j / 2 ≤ (absNorm n : ℝ)) := by
      intro n hn
      rw [Finset.mem_filter]
      refine ⟨?_, (hmem n hn).2.1⟩
      have e4 : (4 : ℝ) * (2 ^ j / 2) = 2 ^ (j + 1) := by rw [pow_succ]; ring
      rw [e4]; exact (hmem n hn).1
    have hshell := sum_shell_inv_le (a := (2 : ℝ) ^ j / 2) (c := 4) (by positivity)
      (by linarith)
    calc ∑ n ∈ cols, ‖βE (pgen n)‖ ^ 2 ≤ ∑ n ∈ cols, a ^ 2 * (1 / (absNorm n : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = a ^ 2 * ∑ n ∈ cols, 1 / (absNorm n : ℝ) := by rw [Finset.mul_sum]
      _ ≤ a ^ 2 * (4 * (2 * kappa + 5)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg a)
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity)
            hshell
  have hX0 : 0 ≤ (H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j) := by positivity
  calc ∑ k ∈ Ks, ‖∑ n ∈ cols, blockCoef Af b k n * e n‖ ^ 2
      = ∑ k ∈ Ks, ‖∑ x ∈ cols.image pgen, βE x * sym6 x (span {k}) ^ 3‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => by rw [hsum k]
    _ ≤ C * (H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j) * ∑ x ∈ cols.image pgen, ‖βE x‖ ^ 2 := hLSapp
    _ ≤ max C 0 * ((H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j)) * (a ^ 2 * (4 * (2 * kappa + 5))) := by
        have hm0 : 0 ≤ ∑ x ∈ cols.image pgen, ‖βE x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
        calc C * (H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j) * ∑ x ∈ cols.image pgen, ‖βE x‖ ^ 2
            ≤ max C 0 * ((H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j)) * ∑ x ∈ cols.image pgen, ‖βE x‖ ^ 2 := by
              rw [mul_assoc C]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0) hm0
          _ ≤ _ := mul_le_mul_of_nonneg_left hmass (mul_nonneg (le_max_right _ _) hX0)

/-- The block's scale is at least `z = 3^m 2^j 8^i/Y` for rows with `N(k) ≤ H₀` and `𝔟` in the
`i`-th shell. -/
theorem le_blockScale {Y H₀ : ℝ} (hY : 0 < Y) (m : ℤ) {k : 𝓞 K}
    (hk : 0 < (absNorm (span {k}) : ℝ)) (hkH : (absNorm (span {k}) : ℝ) ≤ H₀) (j : ℕ) {i : ℕ}
    {b : Ideal (𝓞 K)} (hb : b ∈ shellB i) :
    (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y ≤ blockScale Y H₀ m k j b := by
  unfold blockScale
  have hb1 := (mem_shellB hb).1
  have h8 : (8 : ℝ) ^ i ≤ (absNorm b : ℝ) ^ 3 := by
    calc (8 : ℝ) ^ i = ((2 : ℝ) ^ i) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (absNorm b : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hb1 3
  have hH : 1 ≤ H₀ ^ 2 / (absNorm (span {k}) : ℝ) ^ 2 := by
    rw [one_le_div (by positivity)]
    exact pow_le_pow_left₀ hk.le hkH 2
  have e : (3 : ℝ) ^ m * 2 ^ j * (absNorm b : ℝ) ^ 3 * H₀ ^ 2 / (Y * (absNorm (span {k}) : ℝ) ^ 2) =
      (3 : ℝ) ^ m * 2 ^ j * (absNorm b : ℝ) ^ 3 / Y * (H₀ ^ 2 / (absNorm (span {k}) : ℝ) ^ 2) := by
    field_simp
  rw [e]
  have h1 : (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y ≤ (3 : ℝ) ^ m * 2 ^ j * (absNorm b : ℝ) ^ 3 / Y := by
    gcongr
  calc (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y ≤ (3 : ℝ) ^ m * 2 ^ j * (absNorm b : ℝ) ^ 3 / Y := h1
    _ = (3 : ℝ) ^ m * 2 ^ j * (absNorm b : ℝ) ^ 3 / Y * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hH (by positivity)

/-- **The inner sums of a block in mean square** (the companion paper's (6.19) with its Lemma 6.5):
`Σ_k |F_𝔟(k)|² ≤ K·a²N_w²(1 + z)^{−2A}(H₀2^j)^σ(H₀ + 2^j)` with `z = 3^m 2^j 8^i/Y`, when the first
two derivatives of `h` are bounded by `N_w(1 + e^w)^{−A}`. -/
theorem blockInner_meanSquare (hLS : QuadLargeSieve) {σ : ℝ} (hσ : 0 < σ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → ∀ Nw : ℝ,
      (∀ i ≤ 2, ∀ w, ‖iteratedDeriv i h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A)) →
      ∀ (Y H₀ : ℝ), 0 < Y → 1 ≤ H₀ → ∀ (m : ℤ) (Af : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (a : ℝ),
      (∀ n b, ‖Af n b‖ ≤ a) → (∀ n b, Af n b ≠ 0 → Squarefree n ∧ (absNorm n).Coprime 3) →
      ∀ Ks : Finset (𝓞 K), (∀ k ∈ Ks, Primary k ∧ Squarefree (span {k}) ∧
        (absNorm (span {k})).Coprime 6 ∧ (absNorm (span {k}) : ℝ) ≤ H₀) →
      ∀ (j i : ℕ) (b : Ideal (𝓞 K)), b ∈ shellB i →
      ∑ k ∈ Ks, ‖blockInner h Y H₀ m Af k j b‖ ^ 2 ≤
        K₁ * a ^ 2 * Nw ^ 2 * ((1 + (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y) ^ (-A)) ^ 2 *
          ((H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j)) := by
  obtain ⟨C, hC0, hC⟩ := blockCols_largeSieve hLS hσ
  obtain ⟨Cw, hCw0, hCw⟩ := MellinSep.integral_logWeight_le 2 hA
  have hk := kappa_pos
  refine ⟨Cw ^ 2 * C * (4 * (2 * kappa + 5)), by positivity, ?_⟩
  intro h hh Nw hNw Y H₀ hY hH m Af a ha hAf Ks hKs j i b hb
  set z : ℝ := (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y with hz
  have hz0 : 0 ≤ z := by positivity
  have hNw0 : 0 ≤ Nw := by
    have := (norm_nonneg _).trans (hNw 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  set Bw : ℝ := Cw * Nw * (1 + z) ^ (-A) with hBw
  have hkpos : ∀ k ∈ Ks, 0 < (absNorm (span {k}) : ℝ) := fun k hk =>
    absNorm_pos_of_coprime6 (hKs k hk).2.2.1
  have hRpos : ∀ k ∈ Ks, 0 < blockScale Y H₀ m k j b := by
    intro k hk
    have := hkpos k hk
    have := absNorm_pos_of_mem_shellB hb
    unfold blockScale
    have : (0 : ℝ) < H₀ := by linarith
    positivity
  have hW : ∀ k ∈ Ks, ∀ jj ≤ 2, ∫ v, ‖iteratedDeriv jj
      (MellinSep.logWeight h (Real.log (blockScale Y H₀ m k j b))) v‖ ≤ Bw := by
    intro k hk jj hjj
    refine (hCw h hh Nw hNw _ (hRpos k hk) jj hjj).trans ?_
    have hle := le_blockScale hY m (hkpos k hk) (hKs k hk).2.2.2 j hb
    have : (1 + blockScale Y H₀ m k j b) ^ (-A) ≤ (1 + z) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    simp only [hBw]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have key := MellinSep.rowDep_meanSquare' Ks (blockCols Af j b)
    (fun k => MellinSep.logWeight h (Real.log (blockScale Y H₀ m k j b)))
    (fun k _ => MellinSep.logWeight_contDiff hh _)
    (fun k _ => MellinSep.logWeight_hasCompactSupport h _)
    (fun k hk => by simpa using hW k hk 0 (by norm_num))
    (fun k hk => hW k hk 2 le_rfl)
    (fun k n => blockCoef Af b k n) (fun n => (absNorm n : ℝ) / 2 ^ j)
    (fun n hn => by
      have : n ∈ idealsLe ((2 : ℝ) ^ (j + 1)) := Finset.mem_of_mem_filter _ hn
      have := absNorm_pos_of_mem_idealsLe this
      positivity)
    (fun t => hC H₀ hH Af a ha hAf Ks hKs j b t)
  unfold blockInner
  refine key.trans (le_of_eq ?_)
  simp only [hBw]
  ring

open Classical in
/-- `Σ_{𝔟 ∈ shell i} 1/N𝔟 ≤ 2(2κ+5)`. -/
theorem sum_shellB_inv_le (i : ℕ) :
    ∑ b ∈ shellB i, 1 / (absNorm b : ℝ) ≤ 2 * (2 * kappa + 5) := by
  have hsub : shellB i ⊆ (idealsLe (2 * (2 : ℝ) ^ i)).filter
      (fun b => (2 : ℝ) ^ i ≤ (absNorm b : ℝ)) := by
    intro b hb
    rw [Finset.mem_filter]
    refine ⟨?_, (mem_shellB hb).1⟩
    have e : (2 : ℝ) * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ]; ring
    rw [e]
    unfold shellB at hb
    exact Finset.mem_of_mem_filter _ hb
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => by positivity) ?_
  exact sum_shell_inv_le (by positivity) (by have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num); linarith)

/-- **A dyadic block of the prepared sum in mean square** (the companion paper's (6.20) for one
block): `Σ_k |𝒮_{m;2^j,2^i}(k)|² ≤ K·a²N_w²·3^{−2m/3}(1 + 3^m2^j8^i/Y)^{−2A}(H₀2^j)^σ(H₀ + 2^j)`. -/
theorem prepBlock_meanSquare (hLS : QuadLargeSieve) {σ : ℝ} (hσ : 0 < σ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → ∀ Nw : ℝ,
      (∀ i ≤ 2, ∀ w, ‖iteratedDeriv i h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A)) →
      ∀ (Y H₀ : ℝ), 0 < Y → 1 ≤ H₀ → ∀ (m : ℤ) (Af : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (a : ℝ),
      (∀ n b, ‖Af n b‖ ≤ a) → (∀ n b, Af n b ≠ 0 → Squarefree n ∧ (absNorm n).Coprime 3) →
      ∀ Ks : Finset (𝓞 K), (∀ k ∈ Ks, Primary k ∧ Squarefree (span {k}) ∧
        (absNorm (span {k})).Coprime 6 ∧ (absNorm (span {k}) : ℝ) ≤ H₀) →
      ∀ j i : ℕ, ∑ k ∈ Ks, ‖prepBlock h Y H₀ m Af k j i‖ ^ 2 ≤
        K₀ * a ^ 2 * Nw ^ 2 * ((3 : ℝ) ^ (-(m : ℝ) / 3)) ^ 2 *
          ((1 + (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y) ^ (-A)) ^ 2 * ((H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j)) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := blockInner_meanSquare hLS hσ hA
  have hk := kappa_pos
  refine ⟨K₁ * (2 * (2 * kappa + 5)) ^ 2, by positivity, ?_⟩
  intro h hh Nw hNw Y H₀ hY hH m Af a ha hAf Ks hKs j i
  set c3 : ℝ := (3 : ℝ) ^ (-(m : ℝ) / 3) with hc3
  have hc30 : 0 ≤ c3 := by positivity
  set Bd : ℝ := K₁ * a ^ 2 * Nw ^ 2 * ((1 + (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y) ^ (-A)) ^ 2 *
      ((H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j)) with hBd
  have hH0 : (0 : ℝ) < H₀ := by linarith
  set F : Ideal (𝓞 K) → 𝓞 K → ℂ := fun b k => blockInner h Y H₀ m Af k j b with hF
  have hshell := sum_shellB_inv_le i
  have hrow : ∀ k ∈ Ks, ‖prepBlock h Y H₀ m Af k j i‖ ^ 2 ≤
      (c3 * (2 * (2 * kappa + 5))) * ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) * ‖F b k‖ ^ 2 := by
    intro k hk'
    rw [prepBlock_eq h hY hH0 m Af (absNorm_pos_of_coprime6 (hKs k hk').2.2.1) j i]
    have hw : ∀ b ∈ shellB i, 0 ≤ c3 / (absNorm b : ℝ) := fun b hb =>
      div_nonneg hc30 (absNorm_pos_of_mem_shellB hb).le
    refine (MellinSep.norm_sum_mul_sq_le (shellB i) (fun b => c3 / (absNorm b : ℝ)) hw _).trans ?_
    have hsw : ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) ≤ c3 * (2 * (2 * kappa + 5)) := by
      rw [show (∑ b ∈ shellB i, c3 / (absNorm b : ℝ)) = c3 * ∑ b ∈ shellB i, 1 / (absNorm b : ℝ) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring]
      exact mul_le_mul_of_nonneg_left hshell hc30
    have hx : ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) *
          ‖sym6 (pgen b) (span {k}) ^ 3 * blockInner h Y H₀ m Af k j b‖ ^ 2 ≤
        ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) * ‖F b k‖ ^ 2 := by
      refine Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ?_ (hw b hb)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [norm_mul, norm_pow]
      have := norm_sym6_le (pgen b) (span {k})
      have h3 : ‖sym6 (pgen b) (span {k})‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) this
      calc ‖sym6 (pgen b) (span {k})‖ ^ 3 * ‖blockInner h Y H₀ m Af k j b‖
          ≤ 1 * ‖blockInner h Y H₀ m Af k j b‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = ‖F b k‖ := one_mul _
    have hx0 : 0 ≤ ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) *
        ‖sym6 (pgen b) (span {k}) ^ 3 * blockInner h Y H₀ m Af k j b‖ ^ 2 :=
      Finset.sum_nonneg fun b hb => mul_nonneg (hw b hb) (by positivity)
    calc (∑ b ∈ shellB i, c3 / (absNorm b : ℝ)) * ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) *
          ‖sym6 (pgen b) (span {k}) ^ 3 * blockInner h Y H₀ m Af k j b‖ ^ 2
        ≤ (c3 * (2 * (2 * kappa + 5))) * ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) *
          ‖sym6 (pgen b) (span {k}) ^ 3 * blockInner h Y H₀ m Af k j b‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsw hx0
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  have hinner : ∀ b ∈ shellB i, ∑ k ∈ Ks, ‖F b k‖ ^ 2 ≤ Bd := fun b hb =>
    hK₁ h hh Nw hNw Y H₀ hY hH m Af a ha hAf Ks hKs j i b hb
  calc ∑ k ∈ Ks, ‖prepBlock h Y H₀ m Af k j i‖ ^ 2
      ≤ ∑ k ∈ Ks, (c3 * (2 * (2 * kappa + 5))) *
          ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) * ‖F b k‖ ^ 2 := Finset.sum_le_sum hrow
    _ = (c3 * (2 * (2 * kappa + 5))) * ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) *
          ∑ k ∈ Ks, ‖F b k‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
    _ ≤ (c3 * (2 * (2 * kappa + 5))) * ∑ b ∈ shellB i, c3 / (absNorm b : ℝ) * Bd := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b hb => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (hinner b hb)
          (div_nonneg hc30 (absNorm_pos_of_mem_shellB hb).le)
    _ = (c3 * (2 * (2 * kappa + 5))) * (c3 * (∑ b ∈ shellB i, 1 / (absNorm b : ℝ)) * Bd) := by
        congr 1
        rw [← Finset.sum_mul, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ (c3 * (2 * (2 * kappa + 5))) * (c3 * (2 * (2 * kappa + 5)) * Bd) := by
        have hBd0 : 0 ≤ Bd := by
          have := hinner
          rcases (shellB i).eq_empty_or_nonempty with he | ⟨b, hb⟩
          · simp only [hBd]
            have hNw0 : 0 ≤ Nw := by
              have := (norm_nonneg _).trans (hNw 0 (Nat.zero_le _) 0)
              exact nonneg_of_mul_nonneg_left this (by positivity)
            have : 0 ≤ a := le_trans (norm_nonneg _) (ha ⊥ ⊥)
            positivity
          · exact le_trans (Finset.sum_nonneg fun _ _ => by positivity) (hinner b hb)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshell hc30) hBd0
    _ = K₁ * (2 * (2 * kappa + 5)) ^ 2 * a ^ 2 * Nw ^ 2 * c3 ^ 2 *
          ((1 + (3 : ℝ) ^ m * 2 ^ j * 8 ^ i / Y) ^ (-A)) ^ 2 * ((H₀ * 2 ^ j) ^ σ * (H₀ + 2 ^ j)) := by
        simp only [hBd]; ring

/-! ### The prepared sums as series -/

/-- **The prepared sum** `𝒮_m[A, Y](k)` (the companion paper's (6.15)): the series of `prepTerm` over
all pairs of ideals. -/
def prepSum (h : ℝ → ℂ) (Y H₀ : ℝ) (m : ℤ) (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : 𝓞 K) : ℂ :=
  ∑' p : Ideal (𝓞 K) × Ideal (𝓞 K), prepTerm h Y H₀ m A k p.1 p.2

/-- `|h(log x)| ≤ N_w x^{−θ}` for `0 ≤ θ ≤ A` and `x > 0`, when `|h(w)| ≤ N_w(1 + e^w)^{−A}`. -/
theorem norm_log_comp_le {h : ℝ → ℂ} {Nw A θ : ℝ} (hNw : 0 ≤ Nw) (hθ : 0 ≤ θ) (hθA : θ ≤ A)
    (hh : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A)) {x : ℝ} (hx : 0 < x) :
    ‖h (Real.log x)‖ ≤ Nw * x ^ (-θ) := by
  refine (hh _).trans (mul_le_mul_of_nonneg_left ?_ hNw)
  rw [Real.exp_log hx]
  calc (1 + x) ^ (-A) ≤ (1 + x) ^ (-θ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ x ^ (-θ) := Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith)

theorem prepTerm_eq_zero_of_norm (h : ℝ → ℂ) (Y H₀ : ℝ) (m : ℤ)
    (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : 𝓞 K) {n b : Ideal (𝓞 K)}
    (hnb : (absNorm n : ℝ) = 0 ∨ (absNorm b : ℝ) = 0) : prepTerm h Y H₀ m A k n b = 0 := by
  unfold prepTerm
  rcases hnb with h0 | h0
  · rw [h0, Real.sqrt_zero, zero_mul, Complex.ofReal_zero, div_zero, zero_mul]
  · rw [h0, mul_zero, Complex.ofReal_zero, div_zero, zero_mul]

/-- **The terms of the prepared sum decay**: `|prepTerm| ≤ 3^{−m/3}aN_w c^{−θ}·N𝔫^{−(1/2+θ)}N𝔟^{−(1+3θ)}`
with `c = 3^m H₀²/(Y N(k)²)`. -/
theorem norm_prepTerm_le {h : ℝ → ℂ} {Nw A θ : ℝ} (hNw : 0 ≤ Nw) (hθ : 0 ≤ θ) (hθA : θ ≤ A)
    (hh : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A)) {Y H₀ : ℝ} (hY : 0 < Y) (hH : 0 < H₀)
    (m : ℤ) {Af : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} {a : ℝ} (ha : ∀ n b, ‖Af n b‖ ≤ a) {k : 𝓞 K}
    (hk : 0 < (absNorm (span {k}) : ℝ)) (n b : Ideal (𝓞 K)) :
    ‖prepTerm h Y H₀ m Af k n b‖ ≤ (3 : ℝ) ^ (-(m : ℝ) / 3) * a * Nw *
      ((3 : ℝ) ^ m * H₀ ^ 2 / (Y * (absNorm (span {k}) : ℝ) ^ 2)) ^ (-θ) *
      ((absNorm n : ℝ) ^ (-(1 / 2 + θ)) * (absNorm b : ℝ) ^ (-(1 + 3 * θ))) := by
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) (ha ⊥ ⊥)
  set c : ℝ := (3 : ℝ) ^ m * H₀ ^ 2 / (Y * (absNorm (span {k}) : ℝ) ^ 2) with hc
  have hc0 : 0 < c := by positivity
  have hR0 : 0 ≤ (3 : ℝ) ^ (-(m : ℝ) / 3) * a * Nw * c ^ (-θ) *
      ((absNorm n : ℝ) ^ (-(1 / 2 + θ)) * (absNorm b : ℝ) ^ (-(1 + 3 * θ))) := by positivity
  rcases (Nat.cast_nonneg (absNorm n) : (0 : ℝ) ≤ absNorm n).eq_or_lt with hn | hn
  · rw [prepTerm_eq_zero_of_norm h Y H₀ m Af k (Or.inl hn.symm), norm_zero]; exact hR0
  rcases (Nat.cast_nonneg (absNorm b) : (0 : ℝ) ≤ absNorm b).eq_or_lt with hb | hb
  · rw [prepTerm_eq_zero_of_norm h Y H₀ m Af k (Or.inr hb.symm), norm_zero]; exact hR0
  set x : ℝ := (3 : ℝ) ^ m * absNorm n * (absNorm b : ℝ) ^ 3 * H₀ ^ 2 /
    (Y * (absNorm (span {k}) : ℝ) ^ 2) with hx
  have hxc : x = c * ((absNorm n : ℝ) * (absNorm b : ℝ) ^ 3) := by
    simp only [hx, hc]; field_simp
  have hx0 : 0 < x := by rw [hxc]; positivity
  have hhx := norm_log_comp_le hNw hθ hθA hh hx0
  have hxθ : x ^ (-θ) = c ^ (-θ) * ((absNorm n : ℝ) ^ (-θ) * (absNorm b : ℝ) ^ (-(3 * θ))) := by
    rw [hxc, Real.mul_rpow hc0.le (by positivity), Real.mul_rpow hn.le (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 3; push_cast; ring
  have hsq : Real.sqrt (absNorm n : ℝ) = (absNorm n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have e1 : (absNorm n : ℝ) ^ (-(1 / 2 + θ)) = ((absNorm n : ℝ) ^ (1 / 2 : ℝ))⁻¹ *
      (absNorm n : ℝ) ^ (-θ) := by
    rw [← Real.rpow_neg hn.le, ← Real.rpow_add hn]; congr 1; ring
  have e2 : (absNorm b : ℝ) ^ (-(1 + 3 * θ)) = (absNorm b : ℝ)⁻¹ * (absNorm b : ℝ) ^ (-(3 * θ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb]; congr 1; ring
  unfold prepTerm
  rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  rw [← hx]
  have hs := norm_sym6_le (pgen n * pgen b) (span {k})
  have hs3 : ‖sym6 (pgen n * pgen b) (span {k})‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hs
  rw [e1, e2, hsq]
  have hpos1 : 0 < (absNorm n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  calc (3 : ℝ) ^ (-(m : ℝ) / 3) * ‖Af n b‖ * ‖sym6 (pgen n * pgen b) (span {k})‖ ^ 3 /
        ((absNorm n : ℝ) ^ (1 / 2 : ℝ) * (absNorm b : ℝ)) * ‖h (Real.log x)‖
      ≤ (3 : ℝ) ^ (-(m : ℝ) / 3) * a * 1 / ((absNorm n : ℝ) ^ (1 / 2 : ℝ) * (absNorm b : ℝ)) *
          (Nw * x ^ (-θ)) := by
        gcongr
        exact ha n b
    _ = _ := by
        rw [hxθ]
        field_simp

/-- **The prepared sum converges absolutely** for `θ > 1/2`. -/
theorem summable_prepTerm {h : ℝ → ℂ} {Nw A θ : ℝ} (hNw : 0 ≤ Nw) (hθ : 1 / 2 < θ)
    (hθA : θ ≤ A) (hh : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A)) {Y H₀ : ℝ} (hY : 0 < Y)
    (hH : 0 < H₀) (m : ℤ) {Af : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} {a : ℝ} (ha : ∀ n b, ‖Af n b‖ ≤ a)
    {k : 𝓞 K} (hk : 0 < (absNorm (span {k}) : ℝ)) :
    Summable fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => ‖prepTerm h Y H₀ m Af k p.1 p.2‖ := by
  have h1 := summable_absNorm_rpow (s := 1 / 2 + θ) (by linarith)
  have h2 := summable_absNorm_rpow (s := 1 + 3 * θ) (by linarith)
  have hprod := (Summable.mul_of_nonneg h1 h2 (fun _ => by positivity) fun _ => by positivity).mul_left
    ((3 : ℝ) ^ (-(m : ℝ) / 3) * a * Nw *
      ((3 : ℝ) ^ m * H₀ ^ 2 / (Y * (absNorm (span {k}) : ℝ) ^ 2)) ^ (-θ))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hprod
  exact norm_prepTerm_le hNw (by linarith) hθA hh hY hH m ha hk p.1 p.2

/-! ### The dyadic decomposition -/

open Classical in
/-- An ideal of norm at least `1` lies in the shell `i` exactly when `i = ⌊log₂ N𝔟⌋`. -/
theorem mem_shellB_iff {b : Ideal (𝓞 K)} (hb : 1 ≤ (absNorm b : ℝ)) (i : ℕ) :
    b ∈ shellB i ↔ i = Nat.log 2 (absNorm b) := by
  have hb0 : 0 < absNorm b := by exact_mod_cast lt_of_lt_of_le one_pos hb
  set i0 := Nat.log 2 (absNorm b) with hi0
  have hlow : 2 ^ i0 ≤ absNorm b := Nat.pow_log_le_self 2 hb0.ne'
  have hhigh : absNorm b < 2 ^ (i0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  unfold shellB
  rw [Finset.mem_filter, mem_idealsLe]
  constructor
  · rintro ⟨_, h1, h2⟩
    have h1' : 2 ^ i ≤ absNorm b := by exact_mod_cast h1
    have h2' : absNorm b < 2 ^ (i + 1) := by exact_mod_cast h2
    have a1 : i ≤ i0 := Nat.le_log_of_pow_le (by norm_num) h1'
    have a2 : i0 < i + 1 := by
      by_contra hc
      push Not at hc
      have : 2 ^ (i + 1) ≤ 2 ^ i0 := Nat.pow_le_pow_right (by norm_num) hc
      omega
    omega
  · rintro rfl
    refine ⟨⟨hb0, ?_⟩, by exact_mod_cast hlow, by exact_mod_cast hhigh⟩
    have hf : ⌊(2 : ℝ) ^ (i0 + 1)⌋₊ = 2 ^ (i0 + 1) := by
      rw [show (2 : ℝ) ^ (i0 + 1) = ((2 ^ (i0 + 1) : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    rw [hf]; exact hhigh.le

theorem not_mem_idealsLe_pow {n : Ideal (𝓞 K)} {j : ℕ} (hn : n ∉ idealsLe ((2 : ℝ) ^ (j + 1))) :
    (absNorm n : ℝ) = 0 ∨ 2 ^ (j + 1) < (absNorm n : ℝ) := by
  rw [mem_idealsLe, not_and_or, not_lt, not_le] at hn
  have hf : ⌊(2 : ℝ) ^ (j + 1)⌋₊ = 2 ^ (j + 1) := by
    rw [show (2 : ℝ) ^ (j + 1) = ((2 ^ (j + 1) : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hf] at hn
  rcases hn with h0 | h1
  · left; exact_mod_cast Nat.le_zero.1 h0
  · right; exact_mod_cast h1

theorem dyadicBump_eq_zero_of_not_mem {n : Ideal (𝓞 K)} {j : ℕ}
    (hn : n ∉ idealsLe ((2 : ℝ) ^ (j + 1))) :
    MellinSep.dyadicBump ((absNorm n : ℝ) / 2 ^ j) = 0 := by
  apply MellinSep.dyadicBump_div_eq_zero
  rcases not_mem_idealsLe_pow hn with h0 | h1
  · left; rw [h0]; positivity
  · right; rw [pow_succ] at h1; linarith

open Classical in
/-- **The prepared sum is the sum of its dyadic blocks**: `𝒮_m[A, Y](k) = Σ_{j,i ≥ 0} prepBlock(k; j, i)`,
for `θ > 1/2` with `θ ≤ A`. -/
theorem hasSum_prepBlock {h : ℝ → ℂ} {Nw A θ : ℝ} (hNw : 0 ≤ Nw) (hθ : 1 / 2 < θ) (hθA : θ ≤ A)
    (hh : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A)) {Y H₀ : ℝ} (hY : 0 < Y) (hH : 0 < H₀)
    (m : ℤ) {Af : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} {a : ℝ} (ha : ∀ n b, ‖Af n b‖ ≤ a) {k : 𝓞 K}
    (hk : 0 < (absNorm (span {k}) : ℝ)) :
    HasSum (fun ji : ℕ × ℕ => prepBlock h Y H₀ m Af k ji.1 ji.2) (prepSum h Y H₀ m Af k) := by
  set T : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ := fun p => prepTerm h Y H₀ m Af k p.1 p.2 with hT
  set w : Ideal (𝓞 K) × Ideal (𝓞 K) → ℕ × ℕ → ℝ := fun p ji =>
    MellinSep.dyadicBump ((absNorm p.1 : ℝ) / 2 ^ ji.1) * (if p.2 ∈ shellB ji.2 then 1 else 0)
    with hw
  set F : (Ideal (𝓞 K) × Ideal (𝓞 K)) × (ℕ × ℕ) → ℂ := fun q => T q.1 * (w q.1 q.2 : ℂ) with hF
  have hTs : Summable fun p => ‖T p‖ := summable_prepTerm hNw hθ hθA hh hY hH m ha hk
  have hw0 : ∀ p ji, 0 ≤ w p ji := fun p ji => by
    simp only [hw]
    refine mul_nonneg (MellinSep.dyadicBump_nonneg (by positivity)) ?_
    split_ifs <;> norm_num
  -- the weights of a pair sum to one when its term is nonzero
  have hT0 : ∀ p, T p ≠ 0 → 1 ≤ (absNorm p.1 : ℝ) ∧ 1 ≤ (absNorm p.2 : ℝ) := by
    intro p hp
    have h1 : (absNorm p.1 : ℝ) ≠ 0 := fun h0 =>
      hp (prepTerm_eq_zero_of_norm h Y H₀ m Af k (Or.inl h0))
    have h2 : (absNorm p.2 : ℝ) ≠ 0 := fun h0 =>
      hp (prepTerm_eq_zero_of_norm h Y H₀ m Af k (Or.inr h0))
    constructor
    · have : absNorm p.1 ≠ 0 := by exact_mod_cast h1
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    · have : absNorm p.2 ≠ 0 := by exact_mod_cast h2
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hwsum : ∀ p, T p ≠ 0 → HasSum (w p) 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hT0 p hp
    set i0 := Nat.log 2 (absNorm p.2) with hi0
    have hemb : Function.Injective fun j : ℕ => (j, i0) := fun j1 j2 h => (Prod.mk.inj h).1
    rw [← hemb.hasSum_iff]
    · have e : (w p ∘ fun j : ℕ => (j, i0)) =
          fun j => MellinSep.dyadicBump ((absNorm p.1 : ℝ) / 2 ^ j) := by
        funext j
        simp only [Function.comp, hw, ite_eq_left ((mem_shellB_iff h2 i0).2 rfl), mul_one]
      rw [e]; exact MellinSep.hasSum_dyadicBump h1
    · rintro ⟨j, i⟩ hji
      have hi : i ≠ i0 := fun hii => hji ⟨j, by rw [hii]⟩
      simp only [hw]
      rw [ite_eq_right (fun hmem => hi ((mem_shellB_iff h2 i).1 hmem)), mul_zero]
  -- the fibers over the pairs
  have hFn : ∀ q, ‖F q‖ = ‖T q.1‖ * w q.1 q.2 := fun q => by
    simp only [hF]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 _ _)]
  have hfib : ∀ p, HasSum (fun ji => F (p, ji)) (T p) := by
    intro p
    by_cases hp : T p = 0
    · simp only [hF, hp, zero_mul]; exact hasSum_zero
    · have h1 := (hwsum p hp).mapL Complex.ofRealCLM
      have h2 := h1.mul_left (T p)
      simpa [hF, Function.comp] using h2
  have hfibn : ∀ p, HasSum (fun ji => ‖F (p, ji)‖) ‖T p‖ := by
    intro p
    by_cases hp : T p = 0
    · simp only [hFn, hp, norm_zero, zero_mul]; exact hasSum_zero
    · have := (hwsum p hp).mul_left ‖T p‖
      simpa [hFn] using this
  have hFs : Summable fun q => ‖F q‖ := by
    rw [summable_prod_of_nonneg (fun q => norm_nonneg _)]
    refine ⟨fun p => (hfibn p).summable, ?_⟩
    have e : (fun p => ∑' ji, ‖F (p, ji)‖) = fun p => ‖T p‖ := funext fun p => (hfibn p).tsum_eq
    rw [e]; exact hTs
  have hFsum : Summable F := hFs.of_norm
  have htot : HasSum F (prepSum h Y H₀ m Af k) := by
    have h1 := hFsum.hasSum.prod_fiberwise hfib
    have h2 : HasSum T (prepSum h Y H₀ m Af k) := by
      unfold prepSum; exact hTs.of_norm.hasSum
    rw [h2.unique h1]; exact hFsum.hasSum
  -- the fibers over the blocks
  have hblock : ∀ ji : ℕ × ℕ,
      HasSum (fun p => F (p, ji)) (prepBlock h Y H₀ m Af k ji.1 ji.2) := by
    rintro ⟨j, i⟩
    have hvan : ∀ p ∉ (idealsLe ((2 : ℝ) ^ (j + 1))) ×ˢ (shellB i), F (p, (j, i)) = 0 := by
      intro p hp
      rw [Finset.mem_product, not_and_or] at hp
      simp only [hF, hw]
      rcases hp with hn | hb
      · rw [dyadicBump_eq_zero_of_not_mem hn, zero_mul, Complex.ofReal_zero, mul_zero]
      · rw [ite_eq_right hb, mul_zero, Complex.ofReal_zero, mul_zero]
    have hfin : HasSum (fun p => F (p, (j, i)))
        (∑ p ∈ (idealsLe ((2 : ℝ) ^ (j + 1))) ×ˢ (shellB i), F (p, (j, i))) :=
      hasSum_sum_of_ne_finset_zero hvan
    convert hfin using 1
    unfold prepBlock
    rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun b hb => ?_
    simp only [hF, hT, hw, ite_eq_left hb, mul_one]
  have hswap : HasSum (F ∘ Equiv.prodComm (ℕ × ℕ) (Ideal (𝓞 K) × Ideal (𝓞 K)))
      (prepSum h Y H₀ m Af k) := (Equiv.prodComm _ _).hasSum_iff.2 htot
  exact hswap.prod_fiberwise fun ji => by simpa [Function.comp] using hblock ji

/-- The triple geometric series `Σ r₁^m r₂^j r₃^i = 1/((1−r₁)(1−r₂)(1−r₃))`. -/
theorem hasSum_geom3 {r₁ r₂ r₃ : ℝ} (h1 : 0 ≤ r₁) (h1' : r₁ < 1) (h2 : 0 ≤ r₂) (h2' : r₂ < 1)
    (h3 : 0 ≤ r₃) (h3' : r₃ < 1) :
    HasSum (fun x : ℕ × (ℕ × ℕ) => r₁ ^ x.1 * (r₂ ^ x.2.1 * r₃ ^ x.2.2))
      ((1 - r₁)⁻¹ * ((1 - r₂)⁻¹ * (1 - r₃)⁻¹)) := by
  have g1 := hasSum_geometric_of_lt_one h1 h1'
  have g2 := hasSum_geometric_of_lt_one h2 h2'
  have g3 := hasSum_geometric_of_lt_one h3 h3'
  have s23 : Summable fun y : ℕ × ℕ => r₂ ^ y.1 * r₃ ^ y.2 :=
    Summable.mul_of_nonneg g2.summable g3.summable (fun _ => by positivity) fun _ => by positivity
  have g23 := g2.mul g3 s23
  have s123 : Summable fun x : ℕ × (ℕ × ℕ) => r₁ ^ x.1 * (r₂ ^ x.2.1 * r₃ ^ x.2.2) :=
    Summable.mul_of_nonneg (f := fun m : ℕ => r₁ ^ m) (g := fun y : ℕ × ℕ => r₂ ^ y.1 * r₃ ^ y.2)
      g1.summable s23 (fun _ => by positivity) fun _ => by positivity
  exact g1.mul g23 s123

/-- **The majorant of one block** (the paper's choice of decay, made explicit):
`u^{−1/3}(1 + uUV/Y)^{−A}√((H₀U)^σ(H₀ + U)) ≤ H₀^{(1+σ)/2}Y^σ·u^{−(1/3+σ)}U^{−σ/2}V^{−σ}
+ H₀^{σ/2}Y^{1/2+σ}·u^{−(5/6+σ)}U^{−σ/2}V^{−(1/2+σ)}` for `1/2 + σ ≤ A`. -/
theorem block_majorant {H₀ Y σ A : ℝ} (hH : 1 ≤ H₀) (hY : 0 < Y) (hσ : 0 < σ)
    (hA : 1 / 2 + σ ≤ A) {u U V : ℝ} (hu : 0 < u) (hU : 1 ≤ U) (hV : 0 < V) :
    u ^ (-(1 : ℝ) / 3) * (1 + u * U * V / Y) ^ (-A) * Real.sqrt ((H₀ * U) ^ σ * (H₀ + U)) ≤
      H₀ ^ ((1 + σ) / 2) * Y ^ σ * (u ^ (-(1 / 3 + σ)) * U ^ (-(σ / 2)) * V ^ (-σ)) +
      H₀ ^ (σ / 2) * Y ^ (1 / 2 + σ) *
        (u ^ (-(5 / 6 + σ)) * U ^ (-(σ / 2)) * V ^ (-(1 / 2 + σ))) := by
  have hH0 : 0 < H₀ := by linarith
  have hU0 : 0 < U := by linarith
  set z : ℝ := u * U * V / Y with hz
  have hz0 : 0 < z := by positivity
  have hdec : ∀ θ, 0 ≤ θ → θ ≤ A → (1 + z) ^ (-A) ≤ z ^ (-θ) := by
    intro θ hθ0 hθA
    calc (1 + z) ^ (-A) ≤ (1 + z) ^ (-θ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ z ^ (-θ) := Real.rpow_le_rpow_of_nonpos hz0 (by linarith) (by linarith)
  have hsqrt : Real.sqrt ((H₀ * U) ^ σ * (H₀ + U)) ≤
      (H₀ * U) ^ (σ / 2) * (H₀ ^ (1 / 2 : ℝ) + U ^ (1 / 2 : ℝ)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow ((H₀ * U) ^ σ), ← Real.rpow_mul (by positivity)]
    rw [show σ * (1 / 2) = σ / 2 by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hH0.le, Real.sq_sqrt hU0.le, Real.sqrt_nonneg H₀, Real.sqrt_nonneg U,
      mul_nonneg (Real.sqrt_nonneg H₀) (Real.sqrt_nonneg U)]
  have hzpow : ∀ θ : ℝ, z ^ (-θ) = u ^ (-θ) * U ^ (-θ) * V ^ (-θ) * Y ^ θ := by
    intro θ
    rw [hz, Real.div_rpow (by positivity) hY.le, Real.mul_rpow (by positivity) hV.le,
      Real.mul_rpow hu.le hU0.le, Real.rpow_neg hY.le, div_inv_eq_mul]
  have hHU : (H₀ * U) ^ (σ / 2) = H₀ ^ (σ / 2) * U ^ (σ / 2) := Real.mul_rpow hH0.le hU0.le
  have eu1 : u ^ (-(1 / 3 + σ)) = u ^ (-(1 : ℝ) / 3) * u ^ (-σ) := by
    rw [← Real.rpow_add hu]; congr 1; ring
  have eu2 : u ^ (-(5 / 6 + σ)) = u ^ (-(1 : ℝ) / 3) * u ^ (-(1 / 2 + σ)) := by
    rw [← Real.rpow_add hu]; congr 1; ring
  have eU1 : U ^ (-(σ / 2)) = U ^ (-σ) * U ^ (σ / 2) := by
    rw [← Real.rpow_add hU0]; congr 1; ring
  have eU2 : U ^ (-(σ / 2)) = U ^ (-(1 / 2 + σ)) * U ^ (σ / 2) * U ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]; congr 1; ring
  have eH1 : H₀ ^ ((1 + σ) / 2) = H₀ ^ (σ / 2) * H₀ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hH0]; congr 1; ring
  have hc0 : 0 ≤ u ^ (-(1 : ℝ) / 3) := by positivity
  have hS0 : 0 ≤ Real.sqrt ((H₀ * U) ^ σ * (H₀ + U)) := Real.sqrt_nonneg _
  calc u ^ (-(1 : ℝ) / 3) * (1 + u * U * V / Y) ^ (-A) * Real.sqrt ((H₀ * U) ^ σ * (H₀ + U))
      ≤ u ^ (-(1 : ℝ) / 3) * (1 + z) ^ (-A) *
          ((H₀ * U) ^ (σ / 2) * (H₀ ^ (1 / 2 : ℝ) + U ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = u ^ (-(1 : ℝ) / 3) * (1 + z) ^ (-A) * ((H₀ * U) ^ (σ / 2) * H₀ ^ (1 / 2 : ℝ)) +
        u ^ (-(1 : ℝ) / 3) * (1 + z) ^ (-A) * ((H₀ * U) ^ (σ / 2) * U ^ (1 / 2 : ℝ)) := by ring
    _ ≤ u ^ (-(1 : ℝ) / 3) * z ^ (-σ) * ((H₀ * U) ^ (σ / 2) * H₀ ^ (1 / 2 : ℝ)) +
        u ^ (-(1 : ℝ) / 3) * z ^ (-(1 / 2 + σ)) * ((H₀ * U) ^ (σ / 2) * U ^ (1 / 2 : ℝ)) := by
        gcongr
        · exact hdec σ hσ.le (by linarith)
        · exact hdec (1 / 2 + σ) (by linarith) hA
    _ = _ := by
        rw [hzpow, hzpow, hHU, eu1, eu2, eH1]
        nth_rewrite 1 [eU1]
        rw [eU2]
        ring

/-- `(a^n)^x = (a^x)^n` for `a > 0`. -/
theorem pow_rpow_comm {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) : (a ^ n) ^ x = (a ^ x) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le,
    mul_comm]

/-- The integer power `3^{m−4}` as a real power. -/
theorem three_zpow_eq (m : ℕ) : (3 : ℝ) ^ ((m : ℤ) - 4) = (3 : ℝ) ^ ((m : ℝ) - 4) := by
  rw [← Real.rpow_intCast]; push_cast; ring_nf

/-- `(3^{m−4})^{−t} = 3^{4t}·(3^{−t})^m`. -/
theorem three_pow_shift (m : ℕ) (t : ℝ) :
    ((3 : ℝ) ^ ((m : ℝ) - 4)) ^ (-t) = (3 : ℝ) ^ (4 * t) * ((3 : ℝ) ^ (-t)) ^ m := by
  rw [← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1; ring

/-- **The prepared sums in mean square** (the companion paper's (6.20) and the displays after it, with its Lemma 6.5
displayed): for `|c_m(k)| ≤ 1` and coefficients bounded by `a`,
`Σ_k |Σ_{m ≥ −4} c_m(k)𝒮_m[A_m, Y](k)|² ≤ K·a²N_w²(H₀^{1+σ}Y^{2σ} + H₀^σY^{1+2σ})`, when the first two
derivatives of `h` are bounded by `N_w(1 + e^w)^{−A}` with `A ≥ 1/2 + σ`. The index `m ∈ ℕ` stands for
the paper's `m − 4 ≥ −4`. -/
theorem prepSum_meanSquare (hLS : QuadLargeSieve) {σ : ℝ} (hσ : 0 < σ) {A : ℝ}
    (hA : 1 / 2 + σ ≤ A) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (h : ℝ → ℂ), ContDiff ℝ ∞ h → ∀ Nw : ℝ,
      (∀ i ≤ 2, ∀ w, ‖iteratedDeriv i h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A)) →
      ∀ (Y H₀ : ℝ), 0 < Y → 1 ≤ H₀ →
      ∀ (Af : ℕ → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (a : ℝ), (∀ m n b, ‖Af m n b‖ ≤ a) →
      (∀ m n b, Af m n b ≠ 0 → Squarefree n ∧ (absNorm n).Coprime 3) →
      ∀ Ks : Finset (𝓞 K), (∀ k ∈ Ks, Primary k ∧ Squarefree (span {k}) ∧
        (absNorm (span {k})).Coprime 6 ∧ (absNorm (span {k}) : ℝ) ≤ H₀) →
      ∀ c : ℕ → 𝓞 K → ℂ, (∀ m k, ‖c m k‖ ≤ 1) →
      (∀ k ∈ Ks, Summable fun m : ℕ => c m k * prepSum h Y H₀ ((m : ℤ) - 4) (Af m) k) ∧
      ∑ k ∈ Ks, ‖∑' m : ℕ, c m k * prepSum h Y H₀ ((m : ℤ) - 4) (Af m) k‖ ^ 2 ≤
        Kc * a ^ 2 * Nw ^ 2 * (H₀ ^ (1 + σ) * Y ^ (2 * σ) + H₀ ^ σ * Y ^ (1 + 2 * σ)) := by
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨K₀, hK₀0, hK₀⟩ := prepBlock_meanSquare hLS hσ hA0
  -- the geometric ratios
  set r1 : ℝ := (3 : ℝ) ^ (-(1 / 3 + σ)) with hr1
  set r1' : ℝ := (3 : ℝ) ^ (-(5 / 6 + σ)) with hr1'
  set r2 : ℝ := (2 : ℝ) ^ (-(σ / 2)) with hr2
  set r3 : ℝ := (8 : ℝ) ^ (-σ) with hr3
  set r3' : ℝ := (8 : ℝ) ^ (-(1 / 2 + σ)) with hr3'
  have hlt : ∀ (b t : ℝ), 1 < b → 0 < t → b ^ (-t) < 1 := fun b t hb ht =>
    Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  have hr1lt := hlt 3 (1 / 3 + σ) (by norm_num) (by linarith)
  have hr1'lt := hlt 3 (5 / 6 + σ) (by norm_num) (by linarith)
  have hr2lt := hlt 2 (σ / 2) (by norm_num) (by linarith)
  have hr3lt := hlt 8 σ (by norm_num) hσ
  have hr3'lt := hlt 8 (1 / 2 + σ) (by norm_num) (by linarith)
  set G1 : ℝ := (3 : ℝ) ^ (4 * (1 / 3 + σ)) * ((1 - r1)⁻¹ * ((1 - r2)⁻¹ * (1 - r3)⁻¹)) with hG1
  set G2 : ℝ := (3 : ℝ) ^ (4 * (5 / 6 + σ)) * ((1 - r1')⁻¹ * ((1 - r2)⁻¹ * (1 - r3')⁻¹)) with hG2
  have hG1h : HasSum (fun x : ℕ × (ℕ × ℕ) =>
      (3 : ℝ) ^ (4 * (1 / 3 + σ)) * (r1 ^ x.1 * (r2 ^ x.2.1 * r3 ^ x.2.2))) G1 :=
    (hasSum_geom3 (by positivity) hr1lt (by positivity) hr2lt (by positivity) hr3lt).mul_left _
  have hG2h : HasSum (fun x : ℕ × (ℕ × ℕ) =>
      (3 : ℝ) ^ (4 * (5 / 6 + σ)) * (r1' ^ x.1 * (r2 ^ x.2.1 * r3' ^ x.2.2))) G2 :=
    (hasSum_geom3 (by positivity) hr1'lt (by positivity) hr2lt (by positivity) hr3'lt).mul_left _
  refine ⟨2 * K₀ * (G1 ^ 2 + G2 ^ 2), by positivity, ?_⟩
  intro h hh Nw hNw Y H₀ hY hH Af a ha hAf Ks hKs c hc
  have hH0 : (0 : ℝ) < H₀ := by linarith
  have hNw0 : 0 ≤ Nw := by
    have := (norm_nonneg _).trans (hNw 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have ha0 : 0 ≤ a := le_trans (norm_nonneg _) (ha 0 ⊥ ⊥)
  set P1 : ℝ := H₀ ^ ((1 + σ) / 2) * Y ^ σ with hP1
  set P2 : ℝ := H₀ ^ (σ / 2) * Y ^ (1 / 2 + σ) with hP2
  set F : ℕ × (ℕ × ℕ) → 𝓞 K → ℂ := fun x k =>
    c x.1 k * prepBlock h Y H₀ ((x.1 : ℤ) - 4) (Af x.1) k x.2.1 x.2.2 with hF
  set bnd : ℕ × (ℕ × ℕ) → ℝ := fun x => Real.sqrt K₀ * a * Nw *
    ((3 : ℝ) ^ (-(((x.1 : ℤ) - 4 : ℤ) : ℝ) / 3) *
      (1 + (3 : ℝ) ^ ((x.1 : ℤ) - 4) * 2 ^ x.2.1 * 8 ^ x.2.2 / Y) ^ (-A) *
      Real.sqrt ((H₀ * 2 ^ x.2.1) ^ σ * (H₀ + 2 ^ x.2.1))) with hbnd
  have hbnd0 : ∀ x, 0 ≤ bnd x := fun x => by simp only [hbnd]; positivity
  -- the blocks in mean square
  have hFb : ∀ x, ∑ k ∈ Ks, ‖F x k‖ ^ 2 ≤ bnd x ^ 2 := by
    intro x
    have hb := hK₀ h hh Nw hNw Y H₀ hY hH ((x.1 : ℤ) - 4) (Af x.1) a (ha x.1) (hAf x.1) Ks hKs
      x.2.1 x.2.2
    have hP0 : 0 ≤ (H₀ * 2 ^ x.2.1) ^ σ * (H₀ + 2 ^ x.2.1) := by positivity
    calc ∑ k ∈ Ks, ‖F x k‖ ^ 2 ≤ ∑ k ∈ Ks, ‖prepBlock h Y H₀ ((x.1 : ℤ) - 4) (Af x.1) k x.2.1 x.2.2‖ ^ 2 := by
          refine Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          simp only [hF]
          rw [norm_mul]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hc _ _))
      _ ≤ _ := hb
      _ = bnd x ^ 2 := by
          simp only [hbnd]
          simp only [mul_pow]
          rw [Real.sq_sqrt hK₀0, Real.sq_sqrt hP0]
          push_cast
          ring
  -- the majorant
  have hmaj : ∀ x, bnd x ≤ Real.sqrt K₀ * a * Nw * (P1 * ((3 : ℝ) ^ (4 * (1 / 3 + σ)) *
      (r1 ^ x.1 * (r2 ^ x.2.1 * r3 ^ x.2.2))) + P2 * ((3 : ℝ) ^ (4 * (5 / 6 + σ)) *
      (r1' ^ x.1 * (r2 ^ x.2.1 * r3' ^ x.2.2)))) := by
    intro x
    simp only [hbnd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hu : (0 : ℝ) < (3 : ℝ) ^ ((x.1 : ℝ) - 4) := by positivity
    have key := block_majorant (A := A) (U := (2 : ℝ) ^ x.2.1) (V := (8 : ℝ) ^ x.2.2) hH hY hσ hA hu
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by positivity)
    have e1 : (3 : ℝ) ^ (-(((x.1 : ℤ) - 4 : ℤ) : ℝ) / 3) = ((3 : ℝ) ^ ((x.1 : ℝ) - 4)) ^ (-(1 : ℝ) / 3) := by
      rw [← Real.rpow_mul (by norm_num)]; push_cast; congr 1; ring
    rw [e1, three_zpow_eq]
    refine key.trans (le_of_eq ?_)
    rw [three_pow_shift, three_pow_shift, pow_rpow_comm (by norm_num), pow_rpow_comm (by norm_num),
      pow_rpow_comm (by norm_num)]
    simp only [hP1, hP2, hr1, hr1', hr2, hr3, hr3']
    ring
  have hmajs : Summable fun x : ℕ × (ℕ × ℕ) => Real.sqrt K₀ * a * Nw * (P1 * ((3 : ℝ) ^ (4 * (1 / 3 + σ)) *
      (r1 ^ x.1 * (r2 ^ x.2.1 * r3 ^ x.2.2))) + P2 * ((3 : ℝ) ^ (4 * (5 / 6 + σ)) *
      (r1' ^ x.1 * (r2 ^ x.2.1 * r3' ^ x.2.2)))) :=
    ((hG1h.summable.mul_left P1).add (hG2h.summable.mul_left P2)).mul_left _
  have hmajsum : ∑' x : ℕ × (ℕ × ℕ), Real.sqrt K₀ * a * Nw * (P1 * ((3 : ℝ) ^ (4 * (1 / 3 + σ)) *
      (r1 ^ x.1 * (r2 ^ x.2.1 * r3 ^ x.2.2))) + P2 * ((3 : ℝ) ^ (4 * (5 / 6 + σ)) *
      (r1' ^ x.1 * (r2 ^ x.2.1 * r3' ^ x.2.2)))) = Real.sqrt K₀ * a * Nw * (P1 * G1 + P2 * G2) :=
    (((hG1h.mul_left P1).add (hG2h.mul_left P2)).mul_left _).tsum_eq
  have hbs : Summable bnd := Summable.of_nonneg_of_le hbnd0 hmaj hmajs
  have hbsum : ∑' x, bnd x ≤ Real.sqrt K₀ * a * Nw * (P1 * G1 + P2 * G2) := by
    rw [← hmajsum]; exact hbs.tsum_le_tsum hmaj hmajs
  obtain ⟨hFs, hFsq⟩ := MellinSep.sum_norm_tsum_sq_le Ks F bnd hbnd0 hbs hFb
  -- the fibers over `m`
  have hfib : ∀ k ∈ Ks, ∀ m : ℕ, HasSum (fun ji : ℕ × ℕ => F (m, ji) k)
      (c m k * prepSum h Y H₀ ((m : ℤ) - 4) (Af m) k) := by
    intro k hk m
    have hkpos := absNorm_pos_of_coprime6 (hKs k hk).2.2.1
    have hdec0 : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A) := fun w => by
      simpa using hNw 0 (Nat.zero_le _) w
    have := (hasSum_prepBlock (θ := 1 / 2 + σ) hNw0 (by linarith) hA hdec0 hY hH0 ((m : ℤ) - 4)
      (ha m) hkpos).mul_left (c m k)
    simpa [hF] using this
  have hsumm : ∀ k ∈ Ks, Summable fun m : ℕ => c m k * prepSum h Y H₀ ((m : ℤ) - 4) (Af m) k := by
    intro k hk
    have := (hFs k hk).prod
    refine this.congr fun m => ?_
    exact (hfib k hk m).tsum_eq
  have htsum : ∀ k ∈ Ks, ∑' x, F x k =
      ∑' m : ℕ, c m k * prepSum h Y H₀ ((m : ℤ) - 4) (Af m) k := by
    intro k hk
    rw [(hFs k hk).tsum_prod' fun m => (hFs k hk).prod_factor m]
    exact tsum_congr fun m => (hfib k hk m).tsum_eq
  refine ⟨hsumm, ?_⟩
  calc ∑ k ∈ Ks, ‖∑' m : ℕ, c m k * prepSum h Y H₀ ((m : ℤ) - 4) (Af m) k‖ ^ 2
      = ∑ k ∈ Ks, ‖∑' x, F x k‖ ^ 2 := Finset.sum_congr rfl fun k hk => by rw [htsum k hk]
    _ ≤ (∑' x, bnd x) ^ 2 := hFsq
    _ ≤ (Real.sqrt K₀ * a * Nw * (P1 * G1 + P2 * G2)) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg hbnd0) hbsum 2
    _ ≤ 2 * K₀ * (G1 ^ 2 + G2 ^ 2) * a ^ 2 * Nw ^ 2 * (P1 ^ 2 + P2 ^ 2) := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK₀0]
        have hG10 : 0 ≤ G1 := le_of_lt (by positivity)
        have : (P1 * G1 + P2 * G2) ^ 2 ≤ 2 * (G1 ^ 2 + G2 ^ 2) * (P1 ^ 2 + P2 ^ 2) := by
          nlinarith [sq_nonneg (P1 * G1 - P2 * G2), sq_nonneg (P1 * G2), sq_nonneg (P2 * G1)]
        calc K₀ * a ^ 2 * Nw ^ 2 * (P1 * G1 + P2 * G2) ^ 2
            ≤ K₀ * a ^ 2 * Nw ^ 2 * (2 * (G1 ^ 2 + G2 ^ 2) * (P1 ^ 2 + P2 ^ 2)) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
    _ = 2 * K₀ * (G1 ^ 2 + G2 ^ 2) * a ^ 2 * Nw ^ 2 *
          (H₀ ^ (1 + σ) * Y ^ (2 * σ) + H₀ ^ σ * Y ^ (1 + 2 * σ)) := by
        congr 1
        simp only [hP1, hP2]
        rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_natCast, ← Real.rpow_mul hH0.le, ← Real.rpow_mul hY.le,
          ← Real.rpow_mul hH0.le, ← Real.rpow_mul hY.le]
        push_cast
        congr 2 <;> ring_nf

end Eis

end

#print axioms Eis.summable_absNorm_rpow
#print axioms Eis.exists_primary_gen3
#print axioms Eis.hasSum_prepBlock
#print axioms Eis.blockCols_largeSieve
#print axioms Eis.blockInner_meanSquare
#print axioms Eis.prepBlock_meanSquare
#print axioms Eis.prepSum_meanSquare
