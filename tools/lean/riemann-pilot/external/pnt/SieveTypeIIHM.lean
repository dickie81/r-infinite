/-
# Round 621: the bin bound with the Halász–Montgomery branch, and Proposition 3′ for a curve on a window

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

`bin_bound_pt`: `SieveTypeIIGen.bin_bound_gen`'s proof at one point `(β, m, w)`, with the window's two inequalities
there as the hypothesis.
`bin_bound_gen_hm`: as `SieveTypeIIGen.bin_bound_gen`, with `WindowOKHM`'s disjunction; in the Halász–Montgomery case
the bin's `binTerm` is bounded through its two terms (`√(x + y) ≤ √x + √y`), each a product of powers of `q` whose
exponent is `hmBound`'s (plus `η/2` and `η`), with the count's `(1 + log qT)^10` kept whole in the second.
`typeII_gen_hm`: `SieveTypeIIGen.typeII_gen` with `WindowOKHM` for `WindowOK`: `sum_typeII_bins_hm` for
`typeII_pointwise`, `bin_bound_gen_hm` for `bin_bound_gen`, the constants absorbed into `q^{1/100000}`.

The file imports `SieveHMBins.lean` and `SieveHMWindow.lean`.
-/
import SieveHMBins
import SieveHMWindow

namespace SieveTypeIIHM

open Finset SieveTypeII SieveTypeIIGen SieveCurveGlue

/-- **One bin by orthogonality, at one point**: `SieveTypeIIGen.bin_bound_gen`'s proof with the window's two
inequalities at `(β, m, w)` (`hexp`) for `WindowOK`. For `g β ≤ 1` (`hg1`), `q > 1` (`hq`), `P = q^m` (`hPm`),
`1 ≤ T ≤ 3q^η` (`hT1`, `hT`), `C₀, C_d ≥ 0` (`hC₀`, `hCd`), `Mp ≤ C₀(q^L/P)^{β+w}` (`hMp`) and
`cnt ≤ C_d(qT)^{g(β)}(1 + log qT)^{10}` (`hcnt`): `Mp·cnt^{1/2}((P + q)V)^{1/2}` is at most
`2√3·C₀C_d^{1/2}(1 + log qT)^5 q^{L−1/25000+η/2}(V/P)^{1/2}`. -/
lemma bin_bound_pt {g : ℝ → ℝ} {L q P m T η β w Mp cnt V C₀ Cd : ℝ} (hg1 : g β ≤ 1)
    (hexp : (m ≤ 1 → (L - m) * (β + w) + g β / 2 + (1 + m) / 2 ≤ L - 1 / 25000) ∧
      (1 ≤ m → (L - m) * (β + w) + g β / 2 + m ≤ L - 1 / 25000))
    (hq : 1 < q) (hPm : P = q ^ m) (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd)
    (hMp : Mp ≤ C₀ * (q ^ L / P) ^ (β + w))
    (hcnt : cnt ≤ Cd * (q * T) ^ g β * (1 + Real.log (q * T)) ^ 10) :
    Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
        q ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hcomb := qpow_combine (V := V) (θ' := β + w) (L := L) hq hPm hT1 hT hg1
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

/-- **One bin, with the better bound**: under `WindowOKHM g L m₁ m₂ d e` (`hwin`) for `g ≤ 1` (`hg1`) and
`e ≤ 3/4` (`he`, so that `2^{1/4+e} ≤ 2`), for `q > 1` (`hq`), `P = q^m` (`hPm`) with `m₁ ≤ m ≤ m₂` (`hm1`,
`hm2`), `1 ≤ T ≤ 3q^η` (`hT1`, `hT`), `η ≥ 0` (`hη`), `1/2 ≤ β ≤ 11/12` (`hβ`, `hβ1`), `0 ≤ w ≤ 4·10⁻⁶` (`hw`,
`hw1`), `C₀, C_d, C_K ≥ 0` (`hC₀`, `hCd`, `hCK`), `0 ≤ Mp ≤ C₀(q^L/P)^{β+w}` (`hMp0`, `hMp`),
`0 ≤ cnt ≤ C_d(qT)^{g(β)}(1 + log qT)^{10}` (`hcnt0`, `hcnt`) and `0 ≤ B ≤ C_K(2P)^{1/12−d}(2q)^{5/12+d+2e}` (`hB0`,
`hB`): `Mp · binTerm cnt P q V B ≤ C′(1 + log qT)^{10} q^{L − 1/25000 + η}(V/P)^{1/2}`, with
`C′ = 2√3·(exp 1)^{1/2}C₀C_d^{1/2} + 3(exp 1)^{1/2}C₀C_dC_K^{1/2}·2`. When `WindowOKHM` gives `WindowOK`'s
inequalities, `binTerm` is at most its first term and `bin_bound_pt` applies. Otherwise (`hmBound`) its second term
is at most `(exp 1)^{1/2}(V/P)^{1/2}(√2·cnt^{1/2}P + P^{1/2}cnt·B^{1/2})`; the first summand carries `q` to the
exponent of `hmBound`'s first inequality plus `η/2`, with `(1 + log qT)^5`, and the second to its second inequality
plus `η`, with `(1 + log qT)^{10}`. -/
theorem bin_bound_gen_hm {g : ℝ → ℝ} {L m₁ m₂ d e : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hwin : WindowOKHM g L m₁ m₂ d e)
    (he : e ≤ 3 / 4)
    {q P m T η β w Mp cnt V C₀ Cd CK B : ℝ} (hq : 1 < q) (hPm : P = q ^ m) (hm1 : m₁ ≤ m) (hm2 : m ≤ m₂)
    (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 11 / 12) (hw : 0 ≤ w)
    (hw1 : w ≤ 4 / 10 ^ 6) (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK)
    (hMp : Mp ≤ C₀ * (q ^ L / P) ^ (β + w)) (hMp0 : 0 ≤ Mp)
    (hcnt : cnt ≤ Cd * (q * T) ^ g β * (1 + Real.log (q * T)) ^ 10) (hcnt0 : 0 ≤ cnt)
    (hB : B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB0 : 0 ≤ B) :
    Mp * binTerm cnt P q V B ≤
      (2 * Real.sqrt 3 * Real.sqrt (Real.exp 1) * C₀ * Real.sqrt Cd +
          3 * Real.sqrt (Real.exp 1) * C₀ * Cd * Real.sqrt CK * 2) *
        (1 + Real.log (q * T)) ^ 10 * q ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hT0 : 0 < T := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hs : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  rcases hwin β m w hβ hβ1 hm1 hm2 hw hw1 with hexp | ⟨-, hHM1, hHM2⟩
  · -- orthogonality: `binTerm` is at most its first term, and `bin_bound_pt`
    have h1 : Mp * binTerm cnt P q V B ≤ Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) hMp0
    refine h1.trans ((bin_bound_pt (g := g) (V := V) (hg1 β) hexp hq hPm hT1 hT hC₀ hCd hMp hcnt).trans ?_)
    have hse : 1 ≤ Real.sqrt (Real.exp 1) := Real.one_le_sqrt.2 (Real.one_le_exp zero_le_one)
    have hC : 2 * Real.sqrt 3 * C₀ * Real.sqrt Cd ≤ 2 * Real.sqrt 3 * Real.sqrt (Real.exp 1) * C₀ * Real.sqrt Cd +
        3 * Real.sqrt (Real.exp 1) * C₀ * Cd * Real.sqrt CK * 2 := by
      have h0 : 0 ≤ 2 * Real.sqrt 3 * C₀ * Real.sqrt Cd := by positivity
      have h3 : 0 ≤ 3 * Real.sqrt (Real.exp 1) * C₀ * Cd * Real.sqrt CK * 2 := by positivity
      linarith [mul_le_mul_of_nonneg_left hse h0]
    have hℓ : (1 + Real.log (q * T)) ^ 5 ≤ (1 + Real.log (q * T)) ^ 10 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have hE : q ^ (L - 1 / 25000 + η / 2) ≤ q ^ (L - 1 / 25000 + η) :=
      Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
    refine mul_le_mul_of_nonneg_right ?_ hs
    refine mul_le_mul ?_ hE (by positivity) (by positivity)
    exact mul_le_mul hC hℓ (by positivity) (by positivity)
  · -- Halász–Montgomery: `binTerm` is at most its second term
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log (q * T) := ⟨_, rfl⟩
    rw [← hℓ] at hcnt ⊢
    have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
    have hsq : ∀ x : ℝ, Real.sqrt (q ^ x) = q ^ (x / 2) := fun x => by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; congr 1; ring
    -- the factors as powers of `q`
    have hMq : Mp ≤ C₀ * q ^ ((L - m) * (β + w)) := by
      rw [hPm, ← Real.rpow_sub hq0, ← Real.rpow_mul hq0.le] at hMp; exact hMp
    have hgT : (q * T) ^ g β ≤ 3 * q ^ (g β + η) := by
      have hTg : T ^ g β ≤ 3 * q ^ η :=
        ((Real.rpow_le_rpow_of_exponent_le hT1 (hg1 β)).trans (Real.rpow_one T).le).trans hT
      rw [Real.mul_rpow hq0.le hT0.le, Real.rpow_add hq0]
      calc q ^ g β * T ^ g β ≤ q ^ g β * (3 * q ^ η) := mul_le_mul_of_nonneg_left hTg (by positivity)
        _ = 3 * (q ^ g β * q ^ η) := by ring
    have hc : cnt ≤ Cd * 3 * q ^ (g β + η) * ℓ ^ 10 := by
      calc cnt ≤ Cd * (q * T) ^ g β * ℓ ^ 10 := hcnt
        _ ≤ Cd * (3 * q ^ (g β + η)) * ℓ ^ 10 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgT hCd) (by positivity)
        _ = Cd * 3 * q ^ (g β + η) * ℓ ^ 10 := by ring
    have hsc : Real.sqrt cnt ≤ Real.sqrt Cd * Real.sqrt 3 * q ^ ((g β + η) / 2) * ℓ ^ 5 := by
      have e10 : Real.sqrt (ℓ ^ 10) = ℓ ^ 5 := by
        rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
      calc Real.sqrt cnt ≤ Real.sqrt (Cd * 3 * q ^ (g β + η) * ℓ ^ 10) := Real.sqrt_le_sqrt hc
        _ = Real.sqrt Cd * Real.sqrt 3 * q ^ ((g β + η) / 2) * ℓ ^ 5 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hCd, hsq, e10]
    have hsP : Real.sqrt P = q ^ (m / 2) := by rw [hPm, hsq]
    have hB' : B ≤ CK * 4 * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) := by
      have h22 : (2 : ℝ) ^ (1 / 12 - d) * 2 ^ (5 / 12 + d + 2 * e) ≤ 4 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        calc (2 : ℝ) ^ (1 / 12 - d + (5 / 12 + d + 2 * e)) ≤ 2 ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by rw [Real.rpow_two]; norm_num
      calc B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e) := hB
        _ = CK * (2 ^ (1 / 12 - d) * 2 ^ (5 / 12 + d + 2 * e)) *
              q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) := by
            rw [Real.mul_rpow (by norm_num) hP0.le, Real.mul_rpow (by norm_num) hq0.le, hPm,
              ← Real.rpow_mul hq0.le, Real.rpow_add hq0 (m * (1 / 12 - d))]
            ring
        _ ≤ CK * 4 * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h22 hCK) (by positivity)
    have hsB : Real.sqrt B ≤ Real.sqrt CK * 2 * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2) := by
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      calc Real.sqrt B ≤ Real.sqrt (CK * 4 * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e))) :=
            Real.sqrt_le_sqrt hB'
        _ = Real.sqrt CK * 2 * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCK, h4, hsq]
    -- the second term of `binTerm`, split
    have hsplit : Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)) ≤
        Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
          (Real.sqrt 2 * Real.sqrt cnt * P + Real.sqrt P * (cnt * Real.sqrt B)) := by
      have hX : 0 ≤ cnt * (2 * P) := by positivity
      have hY : 0 ≤ cnt ^ 2 * B := by positivity
      have hsum : Real.sqrt (cnt * (2 * P) + cnt ^ 2 * B) ≤
          Real.sqrt (cnt * (2 * P)) + Real.sqrt (cnt ^ 2 * B) := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [Real.sq_sqrt hX, Real.sq_sqrt hY,
          mul_nonneg (Real.sqrt_nonneg (cnt * (2 * P))) (Real.sqrt_nonneg (cnt ^ 2 * B))]
      have e1 : Real.sqrt (cnt * (2 * P)) = Real.sqrt 2 * Real.sqrt cnt * Real.sqrt P := by
        rw [Real.sqrt_mul hcnt0, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; ring
      have e2 : Real.sqrt (cnt ^ 2 * B) = cnt * Real.sqrt B := by
        rw [Real.sqrt_mul (sq_nonneg cnt), Real.sqrt_sq hcnt0]
      have e3 : Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)) =
          Real.sqrt (Real.exp 1) * (Real.sqrt (V / P) * Real.sqrt P) *
            Real.sqrt (cnt * (2 * P) + cnt ^ 2 * B) := by
        rw [← Real.sqrt_mul' _ hP0.le, div_mul_cancel₀ V hP0.ne', ← Real.sqrt_mul (Real.exp_pos 1).le,
          ← Real.sqrt_mul' _ (by positivity)]
      have hPP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
      rw [e3]
      calc Real.sqrt (Real.exp 1) * (Real.sqrt (V / P) * Real.sqrt P) *
            Real.sqrt (cnt * (2 * P) + cnt ^ 2 * B)
          ≤ Real.sqrt (Real.exp 1) * (Real.sqrt (V / P) * Real.sqrt P) *
              (Real.sqrt (cnt * (2 * P)) + Real.sqrt (cnt ^ 2 * B)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
              (Real.sqrt 2 * Real.sqrt cnt * (Real.sqrt P * Real.sqrt P) +
                Real.sqrt P * (cnt * Real.sqrt B)) := by
            rw [e1, e2]; ring
        _ = Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
              (Real.sqrt 2 * Real.sqrt cnt * P + Real.sqrt P * (cnt * Real.sqrt B)) := by rw [hPP]
    -- the first summand: the exponent of `hmBound`'s first inequality, plus `η/2`
    have hT1b : Mp * Real.sqrt cnt * P ≤
        C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by
      have hx : q ^ ((L - m) * (β + w)) * q ^ ((g β + η) / 2) * q ^ m ≤ q ^ (L - 1 / 25000 + η) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      have hℓ5 : ℓ ^ 5 ≤ ℓ ^ 10 := pow_le_pow_right₀ hℓ1 (by norm_num)
      calc Mp * Real.sqrt cnt * P = Mp * Real.sqrt cnt * q ^ m := by rw [hPm]
        _ ≤ C₀ * q ^ ((L - m) * (β + w)) * (Real.sqrt Cd * Real.sqrt 3 * q ^ ((g β + η) / 2) * ℓ ^ 5) *
              q ^ m := by gcongr
        _ = C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 5 *
              (q ^ ((L - m) * (β + w)) * q ^ ((g β + η) / 2) * q ^ m) := by ring
        _ ≤ C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by gcongr
    -- the second summand: the exponent of `hmBound`'s second inequality, plus `η`
    have hT2b : Mp * Real.sqrt P * cnt * Real.sqrt B ≤
        C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by
      have hx : q ^ ((L - m) * (β + w)) * q ^ (m / 2) * q ^ (g β + η) *
          q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2) ≤ q ^ (L - 1 / 25000 + η) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      calc Mp * Real.sqrt P * cnt * Real.sqrt B
          ≤ C₀ * q ^ ((L - m) * (β + w)) * q ^ (m / 2) * (Cd * 3 * q ^ (g β + η) * ℓ ^ 10) *
              (Real.sqrt CK * 2 * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2)) := by
            rw [hsP]; gcongr
        _ = C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * (q ^ ((L - m) * (β + w)) * q ^ (m / 2) *
              q ^ (g β + η) * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2)) := by ring
        _ ≤ C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by gcongr
    have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc Mp * binTerm cnt P q V B ≤ Mp * Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hMp0
      _ ≤ Mp * (Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
            (Real.sqrt 2 * Real.sqrt cnt * P + Real.sqrt P * (cnt * Real.sqrt B))) :=
          mul_le_mul_of_nonneg_left hsplit hMp0
      _ = Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
            (Real.sqrt 2 * (Mp * Real.sqrt cnt * P) + Mp * Real.sqrt P * cnt * Real.sqrt B) := by ring
      _ ≤ Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
            (2 * (C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η)) +
              C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η)) := by gcongr
      _ = _ := by ring

open scoped ContDiff in
/-- **Proposition 3′ for a curve and a window with the Halász–Montgomery branch, pointwise in the heights**:
`typeII_gen`'s statement with `WindowOKHM g L m₁ m₂ (1/1000) (1/1000)` for `WindowOK g L m₁ m₂`. Hypotheses: `g ≤ 1`
(`hg1`), `g(1/2) = 1` (`hg0`), the counts `CurveCounts g` (`hcnt`), the window (`hwin`), `f0` smooth (`hf0`) with
support in `[1/2, 2]` (`hsupp`), `K₀ ≥ 0`, `e₁ > 0` (`he₁`) and `0 < η ≤ 10⁻⁵` (`hη`, `hη1`). The proof is
`typeII_gen`'s with `sum_typeII_bins_hm` for `typeII_pointwise` (each bin's `M_i` the larger of `0` and the product of
Lemma 1's bounds, the kernel's bound at `Λ = 2P` from `offK_bound`), `bin_bound_gen_hm` for `bin_bound_gen`, and the
constants absorbed into `q^{1/100000}` (`500000·C′(1 + log qT)^{10} ≤ q^{1/100000}` for large `q`, and
`L − 1/25000 + η + 1/100000 ≤ L − 1/50000`). -/
theorem typeII_gen_hm {g : ℝ → ℝ} {L m₁ m₂ : ℝ} (hg1 : ∀ σ, g σ ≤ 1) (hg0 : g (1 / 2) = 1) (hcnt : CurveCounts g)
    (hwin : WindowOKHM g L m₁ m₂ (1 / 1000) (1 / 1000)) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2) (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η)
    (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ m₁ ≤ P → (P : ℝ) ≤ (q : ℝ) ^ m₂ →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
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
  obtain ⟨Bc, Cc, hBc, hCc, hL1⟩ := SieveWeight.norm_Sp_le hf0 hsupp Kd
  obtain ⟨KLmax, hKLmax⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range 500001, Linnik.KL (βg i) (βg i + δ) := ⟨_, rfl⟩
  have hKLnn : ∀ i ≤ 500000, 0 ≤ Linnik.KL (βg i) (βg i + δ) := fun i hi =>
    (Linnik.KL_pos (by rw [hδ]; linarith) (by have := (βg_range hi).2; rw [hδ]; linarith)).le
  have hKLle : ∀ i ≤ 500000, Linnik.KL (βg i) (βg i + δ) ≤ KLmax := fun i hi => hKLmax ▸
    Finset.single_le_sum (f := fun i => Linnik.KL (βg i) (βg i + δ))
      (fun j hj => hKLnn j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (Finset.mem_range.2 (by omega))
  have hKLmax0 : 0 ≤ KLmax := (hKLnn 0 (by norm_num)).trans (hKLle 0 (by norm_num))
  -- `positivity` scans the hypotheses; the sum over `range 500001` would be unfolded there
  clear hKLmax
  obtain ⟨q₁, hMB⟩ := MB_le hBc hCc hKLmax0 (δ := δ) (by rw [hδ]; norm_num) (by rw [hδ]; norm_num) he₁ hη
    (by linarith) hKdη
  obtain ⟨Cd, hCd0, hCd⟩ := hcnt
  obtain ⟨CK, hCK0, hCK⟩ := offK_bound
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = 2 * Real.sqrt 3 * Real.sqrt (Real.exp 1) * (2 ^ K₀ * 2 ^ K₀) *
      Real.sqrt (max Cd 1) + 3 * Real.sqrt (Real.exp 1) * (2 ^ K₀ * 2 ^ K₀) * max Cd 1 * Real.sqrt CK * 2 :=
    ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.1
    (LinnikTwelve.ev_log_pow (500000 * C₁ * 3 ^ 10) (1 / 100000) 10 (by norm_num))
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
  have hPpos : 0 < P := by exact_mod_cast hP0
  have hPge1 : (1 : ℝ) ≤ P := by exact_mod_cast hPpos
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
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hδ1 : δ ≤ 1 / 24 := by rw [hδ]; norm_num
  -- the kernel's bound at `Λ = 2P` (`offK_bound`)
  obtain ⟨Bk, hBk⟩ : ∃ B : ℝ, B = CK * (2 * (P : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 3 / 1000 : ℝ) := ⟨_, rfl⟩
  have hBk0 : 0 ≤ Bk := by rw [hBk]; positivity
  have hKk : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖∑' n, LinnikPower.kTerm ψ (2 * (P : ℝ)) 0 n‖ ≤ Bk :=
    fun ψ hψ => by rw [hBk]; exact hCK q ψ hψ (2 * (P : ℝ)) (by linarith)
  have hBk' : Bk ≤ CK * (2 * (P : ℝ)) ^ (1 / 12 - 1 / 1000 : ℝ) *
      (2 * (q : ℝ)) ^ (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) := by
    have e3 : (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) = 5 / 12 + 3 / 1000 := by norm_num
    rw [hBk, e3]
  -- Lemma 1 in each bin (as in `typeII_pointwise`), with the bound's larger of it and `0`
  have hBχ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        max (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (bin βg 500000 T χ + 1)) δ H (Q j) (h j)) 0 := by
    intro χ hχ
    have hb := bin_lt (β := βg) (by norm_num : 0 < 500000) T χ
    have hθ := βg_range (i := bin βg 500000 T χ + 1) (by omega)
    refine le_trans ?_ (le_max_left _ _)
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j hj => ?_
    have hj' := hQh' j (Finset.mem_range.1 hj)
    exact hL1 q χ hχ (βg (bin βg 500000 T χ + 1)) δ H (Q j) (h j) hθ.1 hθ.2 hδ0 hδ1 (by linarith) hj'.1
      (bin_rect βg_top hχ (by norm_num) hj'.2)
  -- the pointwise bound with the better of the two bounds per bin
  have hpt := sum_typeII_bins_hm (q := q) (β := βg) (N := 500000) (by norm_num) T hPpos hS a h₀
    (fun χ => ∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j))
    (fun i => max (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) 0)
    (fun i => le_max_right _ _) hBχ hBk0 hKk
  refine hpt.trans ?_
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∑ m ∈ S, ‖a m‖ ^ 2 := ⟨_, rfl⟩
  rw [← hV]
  have hbin : ∀ i ∈ Finset.range 500000,
      max (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) 0 *
        binTerm ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin βg 500000 T χ = i).card)
          P q V Bk ≤
        C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by
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
    have hb := bin_bound_gen_hm (V := V) hg1 hwin (by norm_num) hq1 hPm hm1 hm2 hT1 hT3 hη.le hβi.1 hβi.2
      hw0 hw1 (by positivity : (0 : ℝ) ≤ 2 ^ K₀ * 2 ^ K₀) (le_trans zero_le_one (le_max_right Cd 1)) hCK0.le
      (max_le hMp (by positivity)) (le_max_right _ _) hcnt (Nat.cast_nonneg _) hBk' hBk0
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
  have habs : 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := by
    have h := hQ₂ (q : ℝ) hqQ₂
    calc 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 ≤ 500000 * C₁ * (3 * (1 + Real.log q)) ^ 10 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlq0 hlogT 10) (by linarith)
      _ = 500000 * C₁ * 3 ^ 10 * (1 + Real.log q) ^ 10 := by ring
      _ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := h
  have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  have hE : 0 ≤ (q : ℝ) ^ (L - 1 / 25000 + η) := Real.rpow_nonneg hq0.le _
  have hfin : (q : ℝ) ^ (1 / 100000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η) ≤ (q : ℝ) ^ (L - 1 / 50000) := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  calc (500000 : ℝ) * (C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 * (q : ℝ) ^ (L - 1 / 25000 + η) *
        Real.sqrt (V / P)) = 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 10 *
        (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by ring
    _ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) * (q : ℝ) ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs hE) hVP
    _ ≤ (q : ℝ) ^ (L - 1 / 50000) * Real.sqrt (V / P) :=
        mul_le_mul_of_nonneg_right hfin hVP

end SieveTypeIIHM

#print axioms SieveTypeIIHM.bin_bound_pt
#print axioms SieveTypeIIHM.bin_bound_gen_hm
#print axioms SieveTypeIIHM.typeII_gen_hm
