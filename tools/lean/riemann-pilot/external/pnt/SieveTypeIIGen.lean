/-
# Round 607: the Type II estimate for a curve and a window (Proposition 3′ with parameters)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_gen`). Let `g ≤ 1` with `g(1/2) = 1` be a curve whose counts hold (`CurveCounts g`: for
some `C`, at most `C(qT)^{g(σ)}(1 + log qT)^{10}` characters mod `q` have a zero with `Re s ≥ σ` and `|Im s| ≤ T`,
for every `q ≥ 1`, `1/2 ≤ σ ≤ 1` and `T ≥ 2`), and let the window `[m₁, m₂]` keep the exponents of `g` at `L` at most
`L − 1/25000` (`WindowOK g L m₁ m₂`). Then `SieveTypeII.typeII_step` holds with `L` in place of `2333/1000` and
`q^{m₁} ≤ P ≤ q^{m₂}` in place of `q^{(401/1000)L} ≤ P ≤ q^{(485/1000)L}`.

* `CurveCounts`, `WindowOK`: the hypotheses.
* `card_bin_gen`, `bin_bound_gen`, `prod_MB_le_gen`: `SieveTypeII.card_bin_step`, `bin_bound` and `prod_MB_le` for
  `g`, `L` and the window.
* `typeII_gen`: `SieveTypeII.typeII_step`'s proof, with the scales at most `q^{1+L}`.
* The last `example` is `SieveTypeII.typeII_step` again, as the case `g = gStep`, `L = 2333/1000`,
  `m₁ = (401/1000)L` and `m₂ = (485/1000)L`.

The file imports `SieveTypeII.lean`.
-/
import SieveTypeII

open Complex Finset

noncomputable section

namespace SieveTypeIIGen

open DirMean LinnikHybrid DirichletCharacter SieveTypeII

section Gen

open scoped Classical ContDiff

/-- **The counts of a curve `g`**: there is `C ≥ 0` such that for every `q ≥ 1`, `1/2 ≤ σ ≤ 1` and `T ≥ 2` at most
`C(qT)^{g(σ)}(1 + log qT)^{10}` characters mod `q` have a zero with `Re s ≥ σ` and `|Im s| ≤ T`. -/
def CurveCounts (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10

/-- **The window's exponents** for a curve `g` at `L`: for `1/2 ≤ β ≤ 11/12`, `m₁ ≤ m ≤ m₂` and
`0 ≤ w ≤ 4·10⁻⁶`, `(L − m)(β + w) + g(β)/2 + (1 + m)/2 ≤ L − 1/25000` when `m ≤ 1`, and with `m` in place of
`(1 + m)/2` when `m ≥ 1`. -/
def WindowOK (g : ℝ → ℝ) (L m₁ m₂ : ℝ) : Prop :=
  ∀ β m w : ℝ, 1 / 2 ≤ β → β ≤ 11 / 12 → m₁ ≤ m → m ≤ m₂ → 0 ≤ w → w ≤ 4 / 10 ^ 6 →
    (m ≤ 1 → (L - m) * (β + w) + g β / 2 + (1 + m) / 2 ≤ L - 1 / 25000) ∧
    (1 ≤ m → (L - m) * (β + w) + g β / 2 + m ≤ L - 1 / 25000)

/-- **The count of a bin of the grid** for a curve `g` with `g(1/2) = 1`: with the counts `C(qT)^{g(σ)}(…)` for the
zeros, every bin `i < N` of a grid with `N > 0`, `β_0 = 1/2` and `1/2 ≤ β_i ≤ 1` holds, for `T ≥ 2`, at most
`max(C, 1)(qT)^{g(β_i)}(1 + log qT)^{10}` characters `χ ≠ 1` (`SieveTypeII.card_bin_step`). -/
lemma card_bin_gen {g : ℝ → ℝ} (hg0 : g (1 / 2) = 1) {q : ℕ} [NeZero q] {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (hβ0 : β 0 = 1 / 2) (hβ : ∀ i < N, 1 / 2 ≤ β i ∧ β i ≤ 1) {T Cd : ℝ} (hT : 2 ≤ T)
    (hCd : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          Cd * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10) {i : ℕ} (hi : i < N) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card : ℝ) ≤
      max Cd 1 * ((q : ℝ) * T) ^ g (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 1 ≤ (q : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith [Real.log_nonneg hqT])
  have hM1 : 1 ≤ max Cd 1 := le_max_right _ _
  have hMC : Cd ≤ max Cd 1 := le_max_left _ _
  have hP : 0 ≤ ((q : ℝ) * T) ^ g (β i) := Real.rpow_nonneg (by linarith) _
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have hc := LinnikDensity.card_chars_le (q := q)
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = 0)
    have hg : g (β 0) = 1 := by rw [hβ0, hg0]
    rw [hg, Real.rpow_one]
    calc _ ≤ (q : ℝ) := hc
      _ ≤ 1 * ((q : ℝ) * T) * 1 := by
          rw [one_mul, mul_one]; exact le_mul_of_one_le_right (by linarith) (by linarith)
      _ ≤ max Cd 1 * ((q : ℝ) * T) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hM1 (by linarith)) hl1 (by norm_num)
          exact mul_nonneg (by linarith) (by linarith)
  · have hc1 := card_bin_le (q := q) (β := β) (T := T) hN hpos
    have hc2 := hCd (β i) (hβ i hi).1 (hβ i hi).2
    calc _ ≤ ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          ∃ s : ℂ, β i ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) := by exact_mod_cast hc1
      _ ≤ Cd * ((q : ℝ) * T) ^ g (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := hc2
      _ ≤ max Cd 1 * ((q : ℝ) * T) ^ g (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC hP) (by linarith)

/-- **One bin** for a curve `g ≤ 1` and a window `[m₁, m₂]` with `WindowOK g L m₁ m₂`: with `q > 1`, `P = q^m`,
`m₁ ≤ m ≤ m₂`, `1 ≤ T ≤ 3q^η`, `1/2 ≤ β ≤ 11/12` and a width `0 ≤ w ≤ 4·10⁻⁶`, `C₀, C_d ≥ 0`: if the product of Lemma
1's bounds is at most `C₀(q^L/P)^{β+w}` and the bin holds at most `C_d(qT)^{g(β)}(1 + log qT)^{10}` characters, then the
bin's term is at most `2√3·C₀C_d^{1/2}(1 + log qT)^5 q^{L−1/25000+η/2}(V/P)^{1/2}` (`SieveTypeII.bin_bound`). -/
lemma bin_bound_gen {g : ℝ → ℝ} {L m₁ m₂ : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hwin : WindowOK g L m₁ m₂)
    {q P m T η β w Mp cnt V C₀ Cd : ℝ} (hq : 1 < q) (hPm : P = q ^ m) (hm1 : m₁ ≤ m) (hm2 : m ≤ m₂)
    (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 11 / 12) (hw : 0 ≤ w) (hw1 : w ≤ 4 / 10 ^ 6)
    (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (hMp : Mp ≤ C₀ * (q ^ L / P) ^ (β + w))
    (hcnt : cnt ≤ Cd * (q * T) ^ g β * (1 + Real.log (q * T)) ^ 10) :
    Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
        q ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hcomb := qpow_combine (V := V) (θ' := β + w) (L := L) hq hPm hT1 hT (hg1 β)
  have hexp := hwin β m w hβ hβ1 hm1 hm2 hw hw1
  have hsq : Real.sqrt cnt ≤ Real.sqrt Cd * Real.sqrt ((q * T) ^ g β) * (1 + Real.log (q * T)) ^ 5 := by
    have e : Real.sqrt ((1 + Real.log (q * T)) ^ 10) = (1 + Real.log (q * T)) ^ 5 := by
      rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
    calc Real.sqrt cnt ≤ Real.sqrt (Cd * (q * T) ^ g β * (1 + Real.log (q * T)) ^ 10) := Real.sqrt_le_sqrt hcnt
      _ = Real.sqrt Cd * Real.sqrt ((q * T) ^ g β) * (1 + Real.log (q * T)) ^ 5 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCd, e]
  have hA : 0 ≤ (q ^ L / P) ^ (β + w) := by
    have : 0 < P := by rw [hPm]; positivity
    positivity
  have hpow : ∀ E : ℝ, E ≤ L - 1 / 25000 → q ^ (E + η / 2) ≤ q ^ (L - 1 / 25000 + η / 2) :=
    fun E hE => Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
  have key : (q ^ L / P) ^ (β + w) * Real.sqrt ((q * T) ^ g β) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by
    have hs3 : 0 ≤ 2 * Real.sqrt 3 := by positivity
    have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
    rcases le_total m 1 with hm | hm
    · refine (hcomb.1 hm).trans ?_
      have h := hpow _ (hexp.1 hm)
      gcongr
    · refine (hcomb.2 hm).trans ?_
      have h := hpow _ (hexp.2 hm)
      gcongr
  have hs1 : 0 ≤ Real.sqrt ((q * T) ^ g β) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt ((P + q) * V) := Real.sqrt_nonneg _
  calc Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V)
      ≤ (C₀ * (q ^ L / P) ^ (β + w)) *
          (Real.sqrt Cd * Real.sqrt ((q * T) ^ g β) * (1 + Real.log (q * T)) ^ 5) *
            Real.sqrt ((P + q) * V) := by gcongr
    _ = C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
          ((q ^ L / P) ^ (β + w) * Real.sqrt ((q * T) ^ g β) * Real.sqrt ((P + q) * V)) := by
        ring
    _ ≤ C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
          (2 * Real.sqrt 3 * q ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P)) := by gcongr
    _ = _ := by ring

/-- **The product of Lemma 1's bounds** (`SieveTypeII.prod_MB_le` at `L`). For `q > 0` and `P > 0`: if each factor's
bound is at most `2Q_j^{θ′}` and nonnegative, `Q_j ≥ 1` and `∏ Q_j ≤ 2^{K₀}q^L/P` with `K ≤ K₀`, then the product is at
most `2^{K₀}·2^{K₀}(q^L/P)^{θ′}` when `0 ≤ θ′ ≤ 1`. -/
lemma prod_MB_le_gen {L : ℝ} {K K₀ : ℕ} {M Q : ℕ → ℝ} {q P θ' : ℝ} (hK : K ≤ K₀) (hq : 0 < q) (hP : 0 < P)
    (hθ0 : 0 ≤ θ') (hθ1 : θ' ≤ 1) (hM0 : ∀ j < K, 0 ≤ M j) (hM : ∀ j < K, M j ≤ 2 * Q j ^ θ')
    (hQ1 : ∀ j < K, 1 ≤ Q j) (hprod : ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * q ^ L / P) :
    ∏ j ∈ Finset.range K, M j ≤ 2 ^ K₀ * 2 ^ K₀ * (q ^ L / P) ^ θ' := by
  have hQ0 : ∀ j ∈ Finset.range K, 0 ≤ Q j := fun j hj => by linarith [hQ1 j (Finset.mem_range.1 hj)]
  have h2K : (2 : ℝ) ^ K ≤ 2 ^ K₀ := pow_le_pow_right₀ (by norm_num) hK
  have hA : 0 ≤ ∏ j ∈ Finset.range K, Q j := Finset.prod_nonneg hQ0
  have h2K₀ : (1 : ℝ) ≤ 2 ^ K₀ := one_le_pow₀ (by norm_num)
  have hqL : 0 ≤ q ^ L / P := div_nonneg (Real.rpow_nonneg hq.le _) hP.le
  calc ∏ j ∈ Finset.range K, M j ≤ ∏ j ∈ Finset.range K, (2 * Q j ^ θ') :=
        Finset.prod_le_prod₀ (fun j hj => hM0 j (Finset.mem_range.1 hj)) fun j hj => hM j (Finset.mem_range.1 hj)
    _ = 2 ^ K * (∏ j ∈ Finset.range K, Q j) ^ θ' := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Real.finsetProd_rpow _ _ hQ0]
    _ ≤ 2 ^ K₀ * (2 ^ K₀ * q ^ L / P) ^ θ' := by
        apply mul_le_mul h2K (Real.rpow_le_rpow hA hprod hθ0) (Real.rpow_nonneg hA _) (by positivity)
    _ = 2 ^ K₀ * ((2 ^ K₀) ^ θ' * (q ^ L / P) ^ θ') := by
        rw [mul_div_assoc, Real.mul_rpow (by positivity) hqL]
    _ ≤ 2 ^ K₀ * (2 ^ K₀ * (q ^ L / P) ^ θ') := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hqL _)
        calc ((2 : ℝ) ^ K₀) ^ θ' ≤ ((2 : ℝ) ^ K₀) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2K₀ hθ1
          _ = 2 ^ K₀ := Real.rpow_one _
    _ = 2 ^ K₀ * 2 ^ K₀ * (q ^ L / P) ^ θ' := by ring

/-- **Proposition 3′ for a curve and a window, pointwise in the heights.** Let `g ≤ 1` with `g(1/2) = 1` satisfy
`CurveCounts g`, let `WindowOK g L m₁ m₂` hold, let `f0` be smooth with support in `[1/2, 2]`, `K₀ ≥ 0`, `e₁ > 0` and
`0 < η ≤ 10⁻⁵`. For every large `q`, every `P` with `q^{m₁} ≤ P ≤ q^{m₂}`, `W(χ) = Σ_{m∈S} a_mχ(m)m^{−ih₀}` with
`S ⊆ (P, 2P]`, and `B(χ) = ∏_{j<K} Σ_{p ≤ 2Q_j} χ(p)(p/Q_j)^{−ih_j}f0(p/Q_j)` with `K ≤ K₀`, `Q_j ≥ q^{e₁}`,
`|h_j| ≤ q^η` and `∏_j Q_j ≤ 2^{K₀}q^L/P`: `Σ_{χ≠1} |W(χ)||B(χ)| ≤ q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2}`. -/
theorem typeII_gen {g : ℝ → ℝ} {L m₁ m₂ : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hwin : WindowOK g L m₁ m₂) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η)
    (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ m₁ ≤ P → (P : ℝ) ≤ (q : ℝ) ^ m₂ →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (L - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) := by
  -- the parameters
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 10 ^ 6 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 1 + L := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ : ∃ Kd : ℕ, Kd = ⌈5 * U / 12 / η⌉₊ := ⟨_, rfl⟩
  have hKdη : 5 * U / 12 ≤ η * Kd := by
    have h : 5 * U / 12 / η ≤ (Kd : ℝ) := hKd ▸ Nat.le_ceil (5 * U / 12 / η)
    rw [div_le_iff₀ hη] at h
    calc 5 * U / 12 ≤ (Kd : ℝ) * η := h
      _ = η * Kd := mul_comm _ _
  obtain ⟨Bc, Cc, hBc, hCc, hpt⟩ := typeII_pointwise hf0 hsupp Kd
  obtain ⟨KLmax, hKLmax⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range 500001, Linnik.KL (βg i) (βg i + δ) := ⟨_, rfl⟩
  have hKLnn : ∀ i ≤ 500000, 0 ≤ Linnik.KL (βg i) (βg i + δ) := fun i hi =>
    (Linnik.KL_pos (by rw [hδ]; linarith) (by have := (βg_range hi).2; rw [hδ]; linarith)).le
  have hKLle : ∀ i ≤ 500000, Linnik.KL (βg i) (βg i + δ) ≤ KLmax := fun i hi => hKLmax ▸
    Finset.single_le_sum (f := fun i => Linnik.KL (βg i) (βg i + δ))
      (fun j hj => hKLnn j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (Finset.mem_range.2 (by omega))
  have hKLmax0 : 0 ≤ KLmax := (hKLnn 0 (by norm_num)).trans (hKLle 0 (by norm_num))
  obtain ⟨q₁, hMB⟩ := MB_le hBc hCc hKLmax0 (δ := δ) (by rw [hδ]; norm_num) (by rw [hδ]; norm_num) he₁ hη
    (by linarith) hKdη
  obtain ⟨Cd, hCd0, hCd⟩ := hcnt
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = 2 * Real.sqrt 3 * (2 ^ K₀ * 2 ^ K₀) * Real.sqrt (max Cd 1) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by positivity))
      (Real.sqrt_nonneg _)
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.1
    (LinnikTwelve.ev_log_pow (500000 * C₁ * 3 ^ 5) (3 / 200000) 5 (by norm_num))
  have hev : ∀ᶠ q : ℕ in Filter.atTop, q₁ ≤ q ∧ (2 : ℝ) ^ K₀ ≤ q ∧ 4 ≤ (q : ℝ) ^ e₁ ∧ Q₂ ≤ (q : ℝ) ∧ 2 ≤ q :=
    (Filter.eventually_ge_atTop q₁).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop ((2 : ℝ) ^ K₀)).and
        ((((tendsto_rpow_atTop he₁).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4).and
          ((tendsto_natCast_atTop_atTop.eventually_ge_atTop Q₂).and (Filter.eventually_ge_atTop 2))))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨q₀, fun q _ hq P S hS hP1 hP2 a h₀ K hK Q h hQh hprod => ?_⟩
  obtain ⟨hq₁, hq2K, hqe, hqQ₂, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  -- `P = q^m` on the window
  have hm1pos : (0 : ℝ) < (q : ℝ) ^ m₁ := Real.rpow_pos_of_pos hq0 _
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le hm1pos hP1
  have hPge1 : (1 : ℝ) ≤ P := by
    have : 0 < P := by exact_mod_cast hP0
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.logb q P := ⟨_, rfl⟩
  have hPm : (P : ℝ) = (q : ℝ) ^ m := by rw [hm]; exact (Real.rpow_logb hq0 hq1.ne' hP0).symm
  have hm1 : m₁ ≤ m := by
    rw [hPm] at hP1; exact (Real.rpow_le_rpow_left_iff hq1).1 hP1
  have hm2 : m ≤ m₂ := by
    rw [hPm] at hP2; exact (Real.rpow_le_rpow_left_iff hq1).1 hP2
  -- the heights
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = (q : ℝ) ^ η := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := hH ▸ Real.one_le_rpow hq1.le hη.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * H + 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have hT3 : T ≤ 3 * (q : ℝ) ^ η := by rw [hT, ← hH]; linarith
  have hQh' : ∀ j < K, 4 ≤ Q j ∧ |h j| + H + 1 ≤ T := fun j hj =>
    ⟨hqe.trans (hQh j hj).1, by have := (hQh j hj).2; rw [hT, hH]; rw [hH] at hH1; linarith⟩
  -- each scale is at most `q^U`
  have hQ1 : ∀ j < K, 1 ≤ Q j := fun j hj => by linarith [(hQh' j hj).1]
  have hQU : ∀ j < K, Q j ≤ (q : ℝ) ^ U := by
    intro j hj
    have hjK : j ∈ Finset.range K := Finset.mem_range.2 hj
    have hrest : 1 ≤ ∏ k ∈ (Finset.range K).erase j, Q k := Finset.one_le_prod₀ fun k hk =>
      hQ1 k (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
    have hQj := Finset.mul_prod_erase (Finset.range K) Q hjK
    have hQj0 : 0 ≤ Q j := by linarith [hQ1 j hj]
    have hqL : 0 ≤ (q : ℝ) ^ L := Real.rpow_nonneg hq0.le _
    calc Q j ≤ Q j * ∏ k ∈ (Finset.range K).erase j, Q k := le_mul_of_one_le_right hQj0 hrest
      _ = ∏ k ∈ Finset.range K, Q k := hQj
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ L / P := hprod
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ L := div_le_self (mul_nonneg (by norm_num) hqL) hPge1
      _ ≤ (q : ℝ) * (q : ℝ) ^ L := mul_le_mul_of_nonneg_right hq2K hqL
      _ = (q : ℝ) ^ U := by rw [hU, Real.rpow_add hq0, Real.rpow_one]
  -- the pointwise bound
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hδ1 : δ ≤ 1 / 24 := by rw [hδ]; norm_num
  have hptq := hpt q βg 500000 (by norm_num) βg_top (fun i hi => βg_range hi) T δ H hδ0 hδ1 (by linarith)
    K Q h hQh' P S hS a h₀
  refine hptq.trans ?_
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∑ m ∈ S, ‖a m‖ ^ 2 := ⟨_, rfl⟩
  rw [← hV]
  have hbin : ∀ i ∈ Finset.range 500000,
      (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) *
        Real.sqrt (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin βg 500000 T χ = i).card *
          Real.sqrt ((P + q) * V) ≤
        C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 * (q : ℝ) ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by
    intro i hi
    have hi' : i < 500000 := Finset.mem_range.1 hi
    have hβi := βg_range hi'.le
    have hβi1 := βg_range (Nat.succ_le_of_lt hi')
    have hθ0 : 0 ≤ βg (i + 1) + 2 * δ := by linarith [hβi1.1]
    have hθ1 : βg (i + 1) + 2 * δ ≤ 1 := by rw [hδ]; linarith [hβi1.2]
    have hMp := prod_MB_le_gen (L := L) (M := fun j => MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) (Q := Q)
      (θ' := βg (i + 1) + 2 * δ) hK hq0 hP0 hθ0 hθ1
      (fun j hj => MB_nonneg hBc hCc hβi1.2 hδ0 hδ1 (by linarith) (by linarith [(hQh' j hj).1]))
      (fun j hj => by
        rw [hH]
        exact hMB q hq₁ _ _ _ hβi1.1 hβi1.2 (hKLle (i + 1) (by omega)) (hQh j hj).1 (hQU j hj) (hQh j hj).2)
      hQ1 hprod
    have he : βg (i + 1) + 2 * δ = βg i + (1 / 1200000 + 2 * δ) := by rw [βg_succ]; ring
    rw [he] at hMp
    have hcnt := card_bin_gen hg0 (q := q) (β := βg) (N := 500000) (by norm_num) βg_zero
      (fun k hk => ⟨(βg_range hk.le).1, by linarith [(βg_range hk.le).2]⟩) hT2
      (fun σ h1 h2 => hCd q σ T h1 h2 hT2) hi'
    have hw0 : (0 : ℝ) ≤ 1 / 1200000 + 2 * δ := by linarith
    have hw1 : 1 / 1200000 + 2 * δ ≤ 4 / 10 ^ 6 := by rw [hδ]; norm_num
    have hb := bin_bound_gen (V := V) hg1 hwin hq1 hPm hm1 hm2 hT1 hT3 hβi.1 hβi.2 hw0 hw1
      (by positivity : (0 : ℝ) ≤ 2 ^ K₀ * 2 ^ K₀) (le_trans zero_le_one (le_max_right Cd 1)) hMp hcnt
    rw [hC₁]
    exact hb
  refine (Finset.sum_le_sum hbin).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- absorbing the constants
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1.le
  have hlogT : 1 + Real.log ((q : ℝ) * T) ≤ 3 * (1 + Real.log q) := by
    have hT0 : 0 < T := by linarith
    have h1 : Real.log ((q : ℝ) * T) = Real.log q + Real.log T := Real.log_mul hq0.ne' hT0.ne'
    have h2 : Real.log T ≤ Real.log 3 + η * Real.log q := by
      rw [← Real.log_rpow hq0, ← Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hq0 η).ne']
      exact Real.log_le_log hT0 hT3
    have h3 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h4 : η * Real.log q ≤ Real.log q := by
      have : η ≤ 1 := by linarith
      exact mul_le_of_le_one_left hlq this
    linarith
  have hqT1 : 1 ≤ (q : ℝ) * T := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (q : ℝ) * T := mul_le_mul hq1.le hT1 zero_le_one hq0.le
  have hlq0 : 0 ≤ 1 + Real.log ((q : ℝ) * T) := by linarith [Real.log_nonneg hqT1]
  have habs : 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 ≤ (q : ℝ) ^ (3 / 200000 : ℝ) := by
    have h := hQ₂ (q : ℝ) hqQ₂
    calc 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 ≤ 500000 * C₁ * (3 * (1 + Real.log q)) ^ 5 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlq0 hlogT 5) (by linarith)
      _ = 500000 * C₁ * 3 ^ 5 * (1 + Real.log q) ^ 5 := by ring
      _ ≤ (q : ℝ) ^ (3 / 200000 : ℝ) := h
  have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  have hE : 0 ≤ (q : ℝ) ^ (L - 1 / 25000 + η / 2) := Real.rpow_nonneg hq0.le _
  have hfin : (q : ℝ) ^ (3 / 200000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η / 2) ≤ (q : ℝ) ^ (L - 1 / 50000) := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  calc (500000 : ℝ) * (C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 * (q : ℝ) ^ (L - 1 / 25000 + η / 2) *
        Real.sqrt (V / P)) = 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 *
        (q : ℝ) ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by ring
    _ ≤ (q : ℝ) ^ (3 / 200000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs hE) hVP
    _ ≤ (q : ℝ) ^ (L - 1 / 50000) * Real.sqrt (V / P) :=
        mul_le_mul_of_nonneg_right hfin hVP

/-- `SieveTypeII.typeII_step` as the case `g = gStep`, `L = 2333/1000`, `m₁ = (401/1000)L`, `m₂ = (485/1000)L`. -/
example {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen gStep_le_one (by unfold gStep; norm_num) card_zero_step
    (fun _ _ _ hβ hβ1 hm1 hm2 hw hw1 => exponent_le hβ hβ1 hm1 hm2 hw hw1) hf0 hsupp K₀ he₁ hη hη1

end Gen

end SieveTypeIIGen

#print axioms SieveTypeIIGen.card_bin_gen
#print axioms SieveTypeIIGen.bin_bound_gen
#print axioms SieveTypeIIGen.prod_MB_le_gen
#print axioms SieveTypeIIGen.typeII_gen
