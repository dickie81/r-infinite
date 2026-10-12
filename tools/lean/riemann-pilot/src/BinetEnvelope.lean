import Mathlib
import DistinguishedDims

/-! # The Binet–Bose envelope to every order, and Part 0's crossings located (round 412)

BinetProof's kernel `φ(s) = 1/(1 − e^{−s}) − 1/s − 1/2` (`phiB`) is the Bose occupation less its two leading
terms (round 410's `phiB_eq_bose`), and its Mittag-Leffler series `φ(s) = Σ_{n≥0} 2s/(s² + a_n²)`
(`hasSum_phiB`) runs over the frequencies `a_n = 2π(n+1)` (`mats`). Expanding every term geometrically in
`s²/a_n²` bounds `φ` alternately to every order, the Laplace transform carries the bounds to `ψ`, and the bound
of order 2 locates the three continuous crossings of round 411.

* **The envelope of `φ`** (`phiB_envelope`, `bose_envelope`): for `s > 0` and every `K`,
  `0 ≤ (−1)^K (φ(s) − P_K(s)) ≤ c_K s^{2K+1}`, where `P_K(s) = Σ_{j<K} (−1)^j c_j s^{2j+1}` and
  `c_j = 2ζ(2j+2)/(2π)^{2j+2}` (`stirC`, with `ζ` as the series `Zs`); the same holds for
  `1/(eˢ − 1) − 1/s + 1/2`. At `K = 1` it is round 406's pair `s/12 − s³/720 ≤ φ(s) ≤ s/12` (`phiB_order_one`).
* **The coefficients** (`Zs_eq_bernoulli`, `stirC_eq_bernoulli`, `stirC_zero`, `stirC_one`, `stirC_two`):
  `c_j = (−1)^j B_{2j+2}/(2j+2)!` for every `j`, from Mathlib's `hasSum_zeta_nat`; `c₀ = 1/12`,
  `c₁ = 1/720` and `c₂ = 1/30240`, the last through `ζ(6) = π⁶/945` (`Zs_six`) and `B₆ = 1/42`
  (`bernoulli_six`).
* **The envelope of `ψ`** (`lapR_envelope`, `rpsi_envelope`, `lapP_eq_bernoulli`): for `x > 0` and every `K`,
  `0 ≤ (−1)^K (log x − 1/(2x) − S_K(x) − ψ(x)) ≤ c_K (2K+1)!/x^{2K+2}`, where `S_K(x)` (`lapP`) is the Stirling
  sum `Σ_{j<K} B_{2j+2}/((2j+2) x^{2j+2})`. At `K = 2` (`rpsi_stirling2`, `lapR_stirling2`):
  `log x − 1/(2x) − 1/(12x²) + 1/(120x⁴) − 1/(252x⁶) ≤ ψ(x) ≤ log x − 1/(2x) − 1/(12x²) + 1/(120x⁴)`.
* **Euler's constant** (`eulerMascheroni_sharp`): `0.5772156642 < γ < 0.5772156654`, from round 406's
  `γ = H₁₅ − 4 log 2 + 1/32 + L(16)`, the bound of order 2 on `L(16)` and Mathlib's `log_two_near_10`.
* **The crossings located** (`zero_loc`, `threshold_one_loc`, `threshold_two_loc`): the zero of `p` lies in
  `(6.2569, 6.25695)`, the level `½ log π` is reached in `(19.73075, 19.73085)` and the level `√π` in
  `(217.62665, 217.62675)`, each exactly once on `x > −1`. Each endpoint is certified by the shift
  `ψ(y + N) = ψ(y) + Σ_{j<N} 1/(y + j)` (`rpsi_le_shift`, `le_rpsi_shift`), the bound of order 2 at `y + N`,
  Mathlib's bounds on `π` and `e`, CascadeLepton's bounds on `√π`, and its twelve-term Taylor bounds on `exp`
  (`exp_ge_of`, `exp_le_of`).
* **One zero, three extrema** (`critical_pair`, `three_landmarks`): with `x` that zero, `log Γ_ℝ`
  (`Γ_ℝ(s) = π^{−s/2}Γ(s/2)`, `gammaR`) is stationary on `s > 0` only at `x + 1`, and `log V`
  (`V(t) = π^{t/2}/Γ(t/2 + 1)`, `ballV`) on `t > −2` only at `x − 1`; `V` is strictly maximal at `x − 1`, the
  sphere area `Ω` at `x`, and `Γ_ℝ` strictly minimal at `x + 1`. `Γ_ℝ(s) = 2/Ω(s − 1)`
  (`gammaR_eq_two_div_OmR`), and `V` is BallTower's `ballVol` at the integers (`ballV_natCast`).

Inputs: BinetProof (round 155: `phiB`, `hasSum_phiB`, `digamma_eq_lap`), DigammaGauss (round 154: `rpsi`,
`rpsi_add_nat`), EulerGammaBinet and CascadeLepton (round 406: the Laplace integrals, `eulerMascheroni_eq`,
the bounds on `exp` and `√π`), ThermalJoins (round 410: `phiB_eq_bose`), DistinguishedDims (round 411: `pR`,
`OmR`, `hasDerivAt_log_OmR`, `pR_strictMonoOn`, `exists_unique_cross`), BallTower (round 184) and Mathlib.
Not formalized: the nondegeneracy of the three extrema (second derivatives), and Part 0's arguments for which
levels and which integers count.
-/

open Real Set Finset Filter MeasureTheory

noncomputable section

namespace BinetEnvelope

/-! ## The coefficients -/

/-- `ζ(m)` as the real series `Σ_{n≥1} n^{−m}`. -/
def Zs (m : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ m

theorem summable_Zs {m : ℕ} (hm : 2 ≤ m) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ m) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < m))
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- The coefficient `c_j = 2ζ(2j+2)/(2π)^{2j+2}` of `s^{2j+1}`. -/
def stirC (j : ℕ) : ℝ := 2 * Zs (2 * j + 2) / (2 * π) ^ (2 * j + 2)

/-- The truncation `P_K(s) = Σ_{j<K} (−1)^j c_j s^{2j+1}`. -/
def envP (K : ℕ) (s : ℝ) : ℝ := ∑ j ∈ range K, (-1) ^ j * stirC j * s ^ (2 * j + 1)

/-- The Matsubara frequencies `a_n = 2π(n+1)`. -/
def mats (n : ℕ) : ℝ := 2 * π * ((n : ℝ) + 1)

theorem mats_pos (n : ℕ) : 0 < mats n := by unfold mats; positivity

/-- The `j`-th power of every Matsubara term sums to `c_j s^{2j+1}`. -/
theorem hasSum_piece (j : ℕ) (s : ℝ) :
    HasSum (fun n : ℕ => 2 * s / mats n ^ 2 * (s ^ 2 / mats n ^ 2) ^ j) (stirC j * s ^ (2 * j + 1)) := by
  have h := (summable_Zs (m := 2 * j + 2) (by omega)).hasSum.mul_left
    (2 * s ^ (2 * j + 1) / (2 * π) ^ (2 * j + 2))
  convert h using 1
  · funext n
    have e : 2 * s ^ (2 * j + 1) / (2 * π) ^ (2 * j + 2) * (1 / ((n : ℝ) + 1) ^ (2 * j + 2))
        = 2 * s ^ (2 * j + 1) / mats n ^ (2 * j + 2) := by
      rw [mats, mul_pow (2 * π) ((n : ℝ) + 1) (2 * j + 2), div_mul_div_comm, mul_one]
    rw [e, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm]
    congr 1 <;> ring
  · rw [stirC, Zs]
    ring

/-- One Matsubara term less its first `K` powers: `(−1)^K (2s/a²) x^K/(1 + x)` with `x = s²/a²`. -/
theorem matsTerm_sub (K : ℕ) (s : ℝ) {a : ℝ} (ha : 0 < a) :
    2 * s / (s ^ 2 + a ^ 2) - ∑ j ∈ range K, (-1) ^ j * (2 * s / a ^ 2 * (s ^ 2 / a ^ 2) ^ j)
      = (-1) ^ K * (2 * s / a ^ 2 * (s ^ 2 / a ^ 2) ^ K / (1 + s ^ 2 / a ^ 2)) := by
  have ha' : a ≠ 0 := ha.ne'
  have hsa : s ^ 2 + a ^ 2 ≠ 0 := by positivity
  set x := s ^ 2 / a ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : 1 + x ≠ 0 := by positivity
  have hg : (∑ i ∈ range K, (-x) ^ i) * (1 + x) = 1 - (-x) ^ K := by
    have := geom_sum_mul_neg (-x) K
    rwa [sub_neg_eq_add] at this
  have e1 : ∑ j ∈ range K, (-1) ^ j * (2 * s / a ^ 2 * x ^ j)
      = 2 * s / a ^ 2 * ∑ i ∈ range K, (-x) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [neg_pow]; ring)
  have e2 : 2 * s / (s ^ 2 + a ^ 2) = 2 * s / a ^ 2 / (1 + x) := by
    rw [hx]
    field_simp
    ring
  have e3 : ∑ i ∈ range K, (-x) ^ i = (1 - (-x) ^ K) / (1 + x) := by
    rw [eq_div_iff h1]
    exact hg
  rw [e1, e2, e3, neg_pow]
  field_simp
  ring

/-- **The Matsubara envelope to every order.** For `s > 0` and every `K`,
`0 ≤ (−1)^K (φ(s) − P_K(s)) ≤ c_K s^{2K+1}`: the truncations bound `φ` alternately. -/
theorem phiB_envelope (K : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ (-1) ^ K * (PilotDigamma.phiB s - envP K s) ∧
      (-1) ^ K * (PilotDigamma.phiB s - envP K s) ≤ stirC K * s ^ (2 * K + 1) := by
  have hφ : HasSum (fun n : ℕ => 2 * s / (s ^ 2 + mats n ^ 2)) (PilotDigamma.phiB s) :=
    PilotDigamma.hasSum_phiB hs
  have hP : HasSum (fun n : ℕ => ∑ j ∈ range K, (-1) ^ j * (2 * s / mats n ^ 2 * (s ^ 2 / mats n ^ 2) ^ j))
      (envP K s) := by
    have := hasSum_sum (fun j (_ : j ∈ range K) => (hasSum_piece j s).mul_left ((-1) ^ j))
    convert this using 1
    simp only [envP, mul_assoc]
  have hR : HasSum (fun n : ℕ => (-1) ^ K * (2 * s / mats n ^ 2 * (s ^ 2 / mats n ^ 2) ^ K
      / (1 + s ^ 2 / mats n ^ 2))) (PilotDigamma.phiB s - envP K s) := by
    convert hφ.sub hP using 1
    funext n
    exact (matsTerm_sub K s (mats_pos n)).symm
  have h1 : ((-1 : ℝ) ^ K) * (-1) ^ K = 1 := by rw [← mul_pow]; norm_num
  have hS : HasSum (fun n : ℕ => 2 * s / mats n ^ 2 * (s ^ 2 / mats n ^ 2) ^ K / (1 + s ^ 2 / mats n ^ 2))
      ((-1) ^ K * (PilotDigamma.phiB s - envP K s)) := by
    convert hR.mul_left ((-1) ^ K) using 1
    funext n
    rw [← mul_assoc, h1, one_mul]
  constructor
  · exact hS.nonneg (fun n => by have := mats_pos n; positivity)
  · refine hasSum_le (fun n => ?_) hS (hasSum_piece K s)
    have := mats_pos n
    have h0 : 0 ≤ 2 * s / mats n ^ 2 * (s ^ 2 / mats n ^ 2) ^ K := by positivity
    have hx0 : 0 ≤ s ^ 2 / mats n ^ 2 := by positivity
    exact div_le_self h0 (by linarith)

/-- **The same envelope for the Bose occupation:** `0 ≤ (−1)^K (1/(eˢ − 1) − 1/s + 1/2 − P_K(s)) ≤ c_K s^{2K+1}`. -/
theorem bose_envelope (K : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ (-1) ^ K * (ThermalZeta.bose s - 1 / s + 1 / 2 - envP K s) ∧
      (-1) ^ K * (ThermalZeta.bose s - 1 / s + 1 / 2 - envP K s) ≤ stirC K * s ^ (2 * K + 1) := by
  rw [← ThermalJoins.phiB_eq_bose hs]
  exact phiB_envelope K hs

/-! ## The digamma function -/

/-- The Laplace transform of the truncation: `Σ_{j<K} (−1)^j c_j (2j+1)!/x^{2j+2}`. -/
def lapP (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range K, (-1) ^ j * stirC j * ((1 / x) ^ (2 * j + 2) * ((2 * j + 1).factorial : ℝ))

theorem integrableOn_exp_mul_envP (K : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s => Real.exp (-(x * s)) * envP K s) (Ioi 0) := by
  simp only [envP, Finset.mul_sum]
  refine integrable_finsetSum _ (fun j _ => ?_)
  have h : IntegrableOn (fun s : ℝ => (-1) ^ j * stirC j * (s ^ (2 * j + 1) * Real.exp (-(x * s))))
      (Ioi 0) := (Electron.integrableOn_pow_mul_exp hx (2 * j + 1)).const_mul _
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  ring

theorem integral_exp_mul_envP (K : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(x * s)) * envP K s = lapP K x := by
  simp only [envP, lapP, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => ?_)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have h := Electron.integral_pow_mul_exp hx (2 * j + 1)
    calc ∫ s in Ioi (0 : ℝ), Real.exp (-(x * s)) * ((-1) ^ j * stirC j * s ^ (2 * j + 1))
        = (-1) ^ j * stirC j * ∫ s in Ioi (0 : ℝ), s ^ (2 * j + 1) * Real.exp (-(x * s)) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
          ring
      _ = (-1) ^ j * stirC j * ((1 / x) ^ (2 * j + 2) * ((2 * j + 1).factorial : ℝ)) := by
          rw [h]
  · have h : IntegrableOn (fun s : ℝ => (-1) ^ j * stirC j * (s ^ (2 * j + 1) * Real.exp (-(x * s))))
        (Ioi 0) := (Electron.integrableOn_pow_mul_exp hx (2 * j + 1)).const_mul _
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    ring

/-- **The Laplace transform of `φ` to every order:**
`0 ≤ (−1)^K (L(x) − Σ_{j<K} (−1)^j c_j (2j+1)!/x^{2j+2}) ≤ c_K (2K+1)!/x^{2K+2}` for `x > 0`. -/
theorem lapR_envelope (K : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1) ^ K * (Electron.lapR x - lapP K x) ∧
      (-1) ^ K * (Electron.lapR x - lapP K x)
        ≤ stirC K * ((1 / x) ^ (2 * K + 2) * ((2 * K + 1).factorial : ℝ)) := by
  have hφ := Electron.integrableOn_exp_mul_phiB hx
  have hP := integrableOn_exp_mul_envP K hx
  have hdiff : (-1) ^ K * (Electron.lapR x - lapP K x)
      = ∫ s in Ioi (0 : ℝ), Real.exp (-(x * s)) * ((-1) ^ K * (PilotDigamma.phiB s - envP K s)) := by
    rw [← integral_exp_mul_envP K hx, Electron.lapR, ← integral_sub hφ hP, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    ring
  have hI : IntegrableOn
      (fun s => Real.exp (-(x * s)) * ((-1) ^ K * (PilotDigamma.phiB s - envP K s))) (Ioi 0) := by
    have h : IntegrableOn (fun s => (-1) ^ K * (Real.exp (-(x * s)) * PilotDigamma.phiB s
        - Real.exp (-(x * s)) * envP K s)) (Ioi 0) := (hφ.sub hP).const_mul _
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    ring
  rw [hdiff]
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi (fun s (hs : 0 < s) => ?_)
    exact mul_nonneg (Real.exp_pos _).le (phiB_envelope K hs).1
  · have hb := (Electron.integrableOn_pow_mul_exp hx (2 * K + 1)).const_mul (stirC K)
    have hm := setIntegral_mono_on hI hb measurableSet_Ioi (fun s (hs : 0 < s) => by
      calc Real.exp (-(x * s)) * ((-1) ^ K * (PilotDigamma.phiB s - envP K s))
          ≤ Real.exp (-(x * s)) * (stirC K * s ^ (2 * K + 1)) :=
            mul_le_mul_of_nonneg_left (phiB_envelope K hs).2 (Real.exp_pos _).le
        _ = stirC K * (s ^ (2 * K + 1) * Real.exp (-(x * s))) := by ring)
    rw [integral_const_mul, Electron.integral_pow_mul_exp hx (2 * K + 1)] at hm
    exact hm

/-- `ψ(x) = log x − 1/(2x) − L(x)` on `x > 0` (round 155's `digamma_eq_lap`, real form). -/
theorem rpsi_eq_lapR {x : ℝ} (hx : 0 < x) :
    PilotDigamma.rpsi x = Real.log x - 1 / (2 * x) - Electron.lapR x := by
  have h := PilotDigamma.digamma_eq_lap (z := (x : ℂ)) (by simpa using hx)
  rw [PilotDigamma.digamma_ofReal hx, Electron.lap_ofReal, ← Complex.ofReal_log hx.le] at h
  have e : ((PilotDigamma.rpsi x : ℝ) : ℂ) = ((Real.log x - 1 / (2 * x) - Electron.lapR x : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast e

/-- **The Stirling envelope of `ψ` to every order:**
`0 ≤ (−1)^K (log x − 1/(2x) − Σ_{j<K} (−1)^j c_j (2j+1)!/x^{2j+2} − ψ(x)) ≤ c_K (2K+1)!/x^{2K+2}`. -/
theorem rpsi_envelope (K : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1) ^ K * (Real.log x - 1 / (2 * x) - lapP K x - PilotDigamma.rpsi x) ∧
      (-1) ^ K * (Real.log x - 1 / (2 * x) - lapP K x - PilotDigamma.rpsi x)
        ≤ stirC K * ((1 / x) ^ (2 * K + 2) * ((2 * K + 1).factorial : ℝ)) := by
  have h := lapR_envelope K hx
  rw [rpsi_eq_lapR hx]
  have e : Real.log x - 1 / (2 * x) - lapP K x - (Real.log x - 1 / (2 * x) - Electron.lapR x)
      = Electron.lapR x - lapP K x := by ring
  rw [e]
  exact h

/-! ## The first three coefficients -/

theorem Zs_two : Zs 2 = π ^ 2 / 6 := Electron.hasSum_inv_succ_sq.tsum_eq

theorem Zs_four : Zs 4 = π ^ 4 / 90 := Electron.hasSum_inv_succ_four.tsum_eq

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four]
  rw [bernoulli'_def 5]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four]
  norm_num [Nat.choose]

theorem Zs_six : Zs 6 = π ^ 6 / 945 := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat (k := 3) (by norm_num))
  rw [bernoulli_six] at h
  have h' : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 6) (π ^ 6 / 945) := by
    convert h using 1
    · funext n
      push_cast
      ring_nf
    · simp only [Finset.sum_range_one, Nat.cast_zero]
      norm_num [Nat.factorial]
      ring
  exact h'.tsum_eq

theorem stirC_zero : stirC 0 = 1 / 12 := by
  rw [stirC, Zs_two]
  have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem stirC_one : stirC 1 = 1 / 720 := by
  rw [stirC, Zs_four]
  have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem stirC_two : stirC 2 = 1 / 30240 := by
  rw [stirC, Zs_six]
  have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- At `K = 1` the envelope is round 406's pair `s/12 − s³/720 ≤ φ(s) ≤ s/12` (`Electron.le_phiB`,
`Electron.phiB_le`). -/
theorem phiB_order_one {s : ℝ} (hs : 0 < s) :
    s / 12 - s ^ 3 / 720 ≤ PilotDigamma.phiB s ∧ PilotDigamma.phiB s ≤ s / 12 := by
  have h := phiB_envelope 1 hs
  simp only [envP, Finset.sum_range_one, pow_zero, one_mul, mul_zero, zero_add, pow_one, stirC_zero,
    stirC_one, show 2 * 1 + 1 = 3 from rfl] at h
  constructor <;> linarith [h.1, h.2]

/-- `ζ(2j+2) = (−1)^j 2^{2j+1} π^{2j+2} B_{2j+2}/(2j+2)!` (Mathlib's `hasSum_zeta_nat`). -/
theorem Zs_eq_bernoulli (j : ℕ) : Zs (2 * j + 2)
    = (-1) ^ j * 2 ^ (2 * j + 1) * π ^ (2 * j + 2) * bernoulli (2 * j + 2) / (2 * j + 2).factorial := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat (k := j + 1) (by omega))
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 - 1 = 2 * j + 1 by omega,
    Finset.sum_range_one, Nat.cast_zero, zero_pow (by omega), div_zero, sub_zero] at h
  have h' : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * j + 2))
      ((-1) ^ j * 2 ^ (2 * j + 1) * π ^ (2 * j + 2) * bernoulli (2 * j + 2) / (2 * j + 2).factorial) := by
    convert h using 1
    · funext n
      push_cast
      ring
    · ring
  exact h'.tsum_eq

/-- **Every coefficient in closed form:** `c_j = (−1)^j B_{2j+2}/(2j+2)!`. -/
theorem stirC_eq_bernoulli (j : ℕ) :
    stirC j = (-1) ^ j * bernoulli (2 * j + 2) / (2 * j + 2).factorial := by
  rw [stirC, Zs_eq_bernoulli, mul_pow]
  have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hf : ((2 * j + 2).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **The truncation is the Stirling series:** `Σ_{j<K} (−1)^j c_j (2j+1)!/x^{2j+2} = Σ_{j<K} B_{2j+2}/((2j+2) x^{2j+2})`. -/
theorem lapP_eq_bernoulli (K : ℕ) {x : ℝ} (hx : 0 < x) :
    lapP K x = ∑ j ∈ range K, (bernoulli (2 * j + 2) : ℝ) / ((2 * j + 2) * x ^ (2 * j + 2)) := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hfac : ((2 * j + 2).factorial : ℝ) = (2 * (j : ℝ) + 2) * ((2 * j + 1).factorial : ℝ) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ]
    push_cast
    ring
  have h1 : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  have hf : ((2 * j + 1).factorial : ℝ) ≠ 0 := by positivity
  have hx0 : x ≠ 0 := hx.ne'
  have hj : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
  rw [stirC_eq_bernoulli, hfac]
  calc (-1) ^ j * ((-1) ^ j * (bernoulli (2 * j + 2) : ℝ) / ((2 * (j : ℝ) + 2) * ((2 * j + 1).factorial : ℝ)))
        * ((1 / x) ^ (2 * j + 2) * ((2 * j + 1).factorial : ℝ))
      = ((-1) ^ j * (-1) ^ j) * ((bernoulli (2 * j + 2) : ℝ) / ((2 * j + 2) * x ^ (2 * j + 2))) := by
        rw [one_div_pow]
        field_simp
    _ = (bernoulli (2 * j + 2) : ℝ) / ((2 * j + 2) * x ^ (2 * j + 2)) := by rw [h1, one_mul]

/-- **Stirling to second order, with its remainder:** for `x > 0`,
`log x − 1/(2x) − 1/(12x²) + 1/(120x⁴) − 1/(252x⁶) ≤ ψ(x) ≤ log x − 1/(2x) − 1/(12x²) + 1/(120x⁴)`. -/
theorem rpsi_stirling2 {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / (2 * x) - (1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)) - 1 / (252 * x ^ 6)
        ≤ PilotDigamma.rpsi x ∧
      PilotDigamma.rpsi x ≤ Real.log x - 1 / (2 * x) - (1 / (12 * x ^ 2) - 1 / (120 * x ^ 4)) := by
  have h := rpsi_envelope 2 hx
  have hP : lapP 2 x = 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) := by
    simp only [lapP, Finset.sum_range_succ, Finset.sum_range_zero, stirC_zero, stirC_one]
    norm_num [Nat.factorial]
    field_simp
    ring
  have hR : stirC 2 * ((1 / x) ^ (2 * 2 + 2) * ((2 * 2 + 1).factorial : ℝ)) = 1 / (252 * x ^ 6) := by
    rw [stirC_two]
    norm_num [Nat.factorial]
    field_simp
    ring
  rw [hP, hR] at h
  simp only [neg_one_sq, one_mul] at h
  constructor <;> linarith [h.1, h.2]

/-- The same for `L(x)`: `1/(12x²) − 1/(120x⁴) ≤ L(x) ≤ 1/(12x²) − 1/(120x⁴) + 1/(252x⁶)`. -/
theorem lapR_stirling2 {x : ℝ} (hx : 0 < x) :
    1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) ≤ Electron.lapR x ∧
      Electron.lapR x ≤ 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) + 1 / (252 * x ^ 6) := by
  have h := rpsi_stirling2 hx
  rw [rpsi_eq_lapR hx] at h
  constructor <;> linarith [h.1, h.2]

/-! ## Euler's constant -/

/-- **Euler's constant to within `1.2 × 10⁻⁹`:** `0.5772156642 < γ < 0.5772156654`. -/
theorem eulerMascheroni_sharp :
    (0.5772156642 : ℝ) < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < 0.5772156654 := by
  rw [Electron.eulerMascheroni_eq, Electron.harmonic_fifteen]
  have h := lapR_stirling2 (x := 16) (by norm_num)
  have hl := abs_sub_le_iff.1 Real.log_two_near_10
  norm_num at h hl ⊢
  constructor <;> linarith [h.1, h.2, hl.1, hl.2]

/-! ## Certified crossings -/

/-- An upper bound on `ψ(y₀)` through `ψ(y₀ + N) = ψ(y₀) + Σ_{j<N} 1/(y₀ + j)` and Stirling at `y₀ + N`. -/
theorem rpsi_le_shift {y0 : ℝ} (hy0 : 0 < y0) (N : ℕ) :
    PilotDigamma.rpsi y0 ≤ Real.log (y0 + N) - (1 / (2 * (y0 + N)) + (1 / (12 * (y0 + N) ^ 2)
      - 1 / (120 * (y0 + N) ^ 4)) + ∑ j ∈ range N, 1 / (y0 + j)) := by
  have hy : 0 < y0 + N := by positivity
  have h := (rpsi_stirling2 hy).2
  have hs := PilotDigamma.rpsi_add_nat hy0 N
  linarith

theorem le_rpsi_shift {y0 : ℝ} (hy0 : 0 < y0) (N : ℕ) :
    Real.log (y0 + N) - (1 / (2 * (y0 + N)) + (1 / (12 * (y0 + N) ^ 2) - 1 / (120 * (y0 + N) ^ 4))
      + 1 / (252 * (y0 + N) ^ 6) + ∑ j ∈ range N, 1 / (y0 + j)) ≤ PilotDigamma.rpsi y0 := by
  have hy : 0 < y0 + N := by positivity
  have h := (rpsi_stirling2 hy).1
  have hs := PilotDigamma.rpsi_add_nat hy0 N
  linarith

theorem log_lt_of_lt_mul_exp {y P B : ℝ} (hy : 0 < y) (hP : 0 < P) (h : y < P * Real.exp B) :
    Real.log y < Real.log P + B := by
  have := Real.log_lt_log hy h
  rwa [Real.log_mul hP.ne' (Real.exp_pos B).ne', Real.log_exp] at this

theorem lt_log_of_mul_exp_lt {y P B : ℝ} (hP : 0 < P) (h : P * Real.exp B < y) :
    Real.log P + B < Real.log y := by
  have := Real.log_lt_log (by positivity) h
  rwa [Real.log_mul hP.ne' (Real.exp_pos B).ne', Real.log_exp] at this

theorem lt_mul_exp_of {y P Plo B : ℝ} (n N : ℕ) (r : ℝ) (hB : B = n + r) (hr : 0 ≤ r)
    (hPlo : Plo ≤ P) (hPlo0 : 0 ≤ Plo)
    (h : y < Plo * ((2.7182818283 : ℝ) ^ n * ∑ i ∈ range N, r ^ i / (Nat.factorial i))) :
    y < P * Real.exp B := by
  have he := Electron.exp_ge_of n N r hB hr
  calc y < Plo * ((2.7182818283 : ℝ) ^ n * ∑ i ∈ range N, r ^ i / (Nat.factorial i)) := h
    _ ≤ P * Real.exp B := mul_le_mul hPlo he (by positivity) (le_trans hPlo0 hPlo)

theorem mul_exp_lt_of {y P Phi B : ℝ} (n N : ℕ) (hN : 0 < N) (r : ℝ) (hB : B = n + r) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hP : P ≤ Phi) (hP0 : 0 ≤ P)
    (h : Phi * ((2.7182818286 : ℝ) ^ n * ((∑ i ∈ range N, r ^ i / (Nat.factorial i))
      + r ^ N * (N + 1) / ((Nat.factorial N) * N))) < y) :
    P * Real.exp B < y := by
  have he := Electron.exp_le_of n N hN r hB hr0 hr1
  calc P * Real.exp B ≤ Phi * ((2.7182818286 : ℝ) ^ n * ((∑ i ∈ range N, r ^ i / (Nat.factorial i))
      + r ^ N * (N + 1) / ((Nat.factorial N) * N))) :=
        mul_le_mul hP he (Real.exp_pos _).le (le_trans hP0 hP)
    _ < y := h

theorem pi_sq_bounds : (3.14159265358979323846 : ℝ) ^ 2 ≤ π ^ 2 ∧ π ^ 2 ≤ (3.14159265358979323847 : ℝ) ^ 2 :=
  ⟨pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2, pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d20.le 2⟩

/-- `p(6.2569) < 0`. -/
theorem pR_lo0 : Part0.pR 6.2569 < 0 := by
  have h := rpsi_le_shift (y0 := 72569 / 20000) (by norm_num) 4
  have hlog := log_lt_of_lt_mul_exp (y := 72569 / 20000 + ((4 : ℕ) : ℝ)) (P := π) (B := 0.887162129059)
    (by norm_num) Real.pi_pos
    (lt_mul_exp_of 0 12 0.887162129059 (by norm_num) (by norm_num) Real.pi_gt_d20.le (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
  have hB : (0.887162129059 : ℝ) ≤ 1 / (2 * (72569 / 20000 + ((4 : ℕ) : ℝ)))
      + (1 / (12 * (72569 / 20000 + ((4 : ℕ) : ℝ)) ^ 2) - 1 / (120 * (72569 / 20000 + ((4 : ℕ) : ℝ)) ^ 4))
      + ∑ j ∈ range 4, 1 / ((72569 / 20000 : ℝ) + j) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  unfold Part0.pR
  rw [show ((6.2569 : ℝ) + 1) / 2 = 72569 / 20000 by norm_num]
  linarith

/-- `p(6.25695) > 0`. -/
theorem pR_hi0 : 0 < Part0.pR 6.25695 := by
  have h := le_rpsi_shift (y0 := 145139 / 40000) (by norm_num) 4
  have hlog := lt_log_of_mul_exp_lt (y := 145139 / 40000 + ((4 : ℕ) : ℝ)) (P := π) (B := 0.887157501031)
    Real.pi_pos
    (mul_exp_lt_of 0 12 (by norm_num) 0.887157501031 (by norm_num) (by norm_num) (by norm_num)
      Real.pi_lt_d20.le Real.pi_pos.le
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
  have hB : 1 / (2 * (145139 / 40000 + ((4 : ℕ) : ℝ)))
      + (1 / (12 * (145139 / 40000 + ((4 : ℕ) : ℝ)) ^ 2) - 1 / (120 * (145139 / 40000 + ((4 : ℕ) : ℝ)) ^ 4))
      + 1 / (252 * (145139 / 40000 + ((4 : ℕ) : ℝ)) ^ 6)
      + ∑ j ∈ range 4, 1 / ((145139 / 40000 : ℝ) + j) ≤ (0.887157501031 : ℝ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  unfold Part0.pR
  rw [show ((6.25695 : ℝ) + 1) / 2 = 145139 / 40000 by norm_num]
  linarith

/-- `p(19.73075) < ½ log π`. -/
theorem pR_lo1 : Part0.pR 19.73075 < Real.log π / 2 := by
  have h := rpsi_le_shift (y0 := 82923 / 8000) (by norm_num) 0
  have hlog := log_lt_of_lt_mul_exp (y := 82923 / 8000 + ((0 : ℕ) : ℝ)) (P := π ^ 2) (B := 0.049012419148)
    (by norm_num) (by positivity)
    (lt_mul_exp_of 0 12 0.049012419148 (by norm_num) (by norm_num) pi_sq_bounds.1 (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
  have hB : (0.049012419148 : ℝ) ≤ 1 / (2 * (82923 / 8000 + ((0 : ℕ) : ℝ)))
      + (1 / (12 * (82923 / 8000 + ((0 : ℕ) : ℝ)) ^ 2) - 1 / (120 * (82923 / 8000 + ((0 : ℕ) : ℝ)) ^ 4))
      + ∑ j ∈ range 0, 1 / ((82923 / 8000 : ℝ) + j) := by
    simp only [Finset.sum_range_zero]; norm_num
  rw [Real.log_pow] at hlog
  unfold Part0.pR
  rw [show ((19.73075 : ℝ) + 1) / 2 = 82923 / 8000 by norm_num]
  push_cast at hlog
  linarith

/-- `p(19.73085) > ½ log π`. -/
theorem pR_hi1 : Real.log π / 2 < Part0.pR 19.73085 := by
  have h := le_rpsi_shift (y0 := 414617 / 40000) (by norm_num) 0
  have hlog := lt_log_of_mul_exp_lt (y := 414617 / 40000 + ((0 : ℕ) : ℝ)) (P := π ^ 2)
    (B := 0.049012182195) (by positivity)
    (mul_exp_lt_of 0 12 (by norm_num) 0.049012182195 (by norm_num) (by norm_num) (by norm_num)
      pi_sq_bounds.2 (by positivity)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
  have hB : 1 / (2 * (414617 / 40000 + ((0 : ℕ) : ℝ)))
      + (1 / (12 * (414617 / 40000 + ((0 : ℕ) : ℝ)) ^ 2) - 1 / (120 * (414617 / 40000 + ((0 : ℕ) : ℝ)) ^ 4))
      + 1 / (252 * (414617 / 40000 + ((0 : ℕ) : ℝ)) ^ 6)
      + ∑ j ∈ range 0, 1 / ((414617 / 40000 : ℝ) + j) ≤ (0.049012182195 : ℝ) := by
    simp only [Finset.sum_range_zero]; norm_num
  rw [Real.log_pow] at hlog
  unfold Part0.pR
  rw [show ((19.73085 : ℝ) + 1) / 2 = 414617 / 40000 by norm_num]
  push_cast at hlog
  linarith

/-- `p(217.62665) < √π`. -/
theorem pR_lo2 : Part0.pR 217.62665 < √π := by
  have h := rpsi_le_shift (y0 := 4372533 / 40000) (by norm_num) 0
  have hlog := log_lt_of_lt_mul_exp (y := 4372533 / 40000 + ((0 : ℕ) : ℝ)) (P := π)
    (B := 3.549488683379) (by norm_num) Real.pi_pos
    (lt_mul_exp_of 3 12 0.549488683379 (by norm_num) (by norm_num) Real.pi_gt_d20.le (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
  have hB : (3.549488683379 : ℝ) ≤ 1 / (2 * (4372533 / 40000 + ((0 : ℕ) : ℝ)))
      + (1 / (12 * (4372533 / 40000 + ((0 : ℕ) : ℝ)) ^ 2) - 1 / (120 * (4372533 / 40000 + ((0 : ℕ) : ℝ)) ^ 4))
      + ∑ j ∈ range 0, 1 / ((4372533 / 40000 : ℝ) + j) + 2 * 1.7724538509 := by
    simp only [Finset.sum_range_zero]; norm_num
  have hs := Electron.sqrt_pi_gt
  unfold Part0.pR
  rw [show ((217.62665 : ℝ) + 1) / 2 = 4372533 / 40000 by norm_num]
  linarith

/-- `p(217.62675) > √π`. -/
theorem pR_hi2 : √π < Part0.pR 217.62675 := by
  have h := le_rpsi_shift (y0 := 874507 / 8000) (by norm_num) 0
  have hlog := lt_log_of_mul_exp_lt (y := 874507 / 8000 + ((0 : ℕ) : ℝ)) (P := π) (B := 3.549488681482)
    Real.pi_pos
    (mul_exp_lt_of 3 12 (by norm_num) 0.549488681482 (by norm_num) (by norm_num) (by norm_num)
      Real.pi_lt_d20.le Real.pi_pos.le
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num))
  have hB : 1 / (2 * (874507 / 8000 + ((0 : ℕ) : ℝ)))
      + (1 / (12 * (874507 / 8000 + ((0 : ℕ) : ℝ)) ^ 2) - 1 / (120 * (874507 / 8000 + ((0 : ℕ) : ℝ)) ^ 4))
      + 1 / (252 * (874507 / 8000 + ((0 : ℕ) : ℝ)) ^ 6)
      + ∑ j ∈ range 0, 1 / ((874507 / 8000 : ℝ) + j) + 2 * 1.7724538510 ≤ (3.549488681482 : ℝ) := by
    simp only [Finset.sum_range_zero]; norm_num
  have hs := Electron.sqrt_pi_lt
  unfold Part0.pR
  rw [show ((217.62675 : ℝ) + 1) / 2 = 874507 / 8000 by norm_num]
  linarith

/-- **The natural zero to four decimals:** the zero of `p` lies in `(6.2569, 6.25695)`. -/
theorem zero_loc : ∃ x ∈ Ioo (6.2569 : ℝ) 6.25695, Part0.pR x = 0 ∧ ∀ y, -1 < y → Part0.pR y = 0 → y = x :=
  Part0.exists_unique_cross (by norm_num) (by norm_num) pR_lo0 pR_hi0

/-- **The first threshold to four decimals:** `p(x) = ½ log π` at one `x`, in `(19.73075, 19.73085)`. -/
theorem threshold_one_loc :
    ∃ x ∈ Ioo (19.73075 : ℝ) 19.73085, Part0.pR x = Real.log π / 2 ∧
      ∀ y, -1 < y → Part0.pR y = Real.log π / 2 → y = x :=
  Part0.exists_unique_cross (by norm_num) (by norm_num) pR_lo1 pR_hi1

/-- **The second threshold to four decimals:** `p(x) = √π` at one `x`, in `(217.62665, 217.62675)`. -/
theorem threshold_two_loc :
    ∃ x ∈ Ioo (217.62665 : ℝ) 217.62675, Part0.pR x = √π ∧ ∀ y, -1 < y → Part0.pR y = √π → y = x :=
  Part0.exists_unique_cross (by norm_num) (by norm_num) pR_lo2 pR_hi2

/-! ## The critical pair -/

/-- `Γ_ℝ(s) = π^{−s/2}Γ(s/2)` on the real line. -/
def gammaR (s : ℝ) : ℝ := π ^ (-s / 2) * Real.Gamma (s / 2)

/-- The volume of the unit ball in a continuous dimension: `V(t) = π^{t/2}/Γ(t/2 + 1)`. -/
def ballV (t : ℝ) : ℝ := π ^ (t / 2) / Real.Gamma (t / 2 + 1)

/-- `d/ds log Γ_ℝ(s) = p(s − 1)` for `s > 0`. -/
theorem hasDerivAt_log_gammaR {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => Real.log (gammaR t)) (Part0.pR (s - 1)) s := by
  have ht : 0 < s / 2 := by linarith
  have hdG : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) (s / 2) :=
    (Real.differentiableAt_Gamma (PilotDigamma.real_ne_neg_nat ht)).log
      (Real.Gamma_pos_of_pos ht).ne'
  have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have h3 : HasDerivAt ((Real.log ∘ Real.Gamma) ∘ fun t : ℝ => t / 2)
      (PilotDigamma.rpsi (s / 2) * (1 / 2)) s := hdG.hasDerivAt.comp s h1
  have h2 : HasDerivAt (fun t : ℝ => -t / 2 * Real.log π) (-1 / 2 * Real.log π) s := by
    simpa using ((hasDerivAt_id s).neg.div_const 2).mul_const (Real.log π)
  have h4 := h2.add h3
  have hev : (fun t : ℝ => -t / 2 * Real.log π + ((Real.log ∘ Real.Gamma) ∘ fun t : ℝ => t / 2) t)
      =ᶠ[nhds s] fun t => Real.log (gammaR t) := by
    filter_upwards [lt_mem_nhds hs] with t ht
    have ht' : 0 < t / 2 := by linarith
    simp only [gammaR, Function.comp]
    rw [Real.log_mul (Real.rpow_pos_of_pos Real.pi_pos _).ne' (Real.Gamma_pos_of_pos ht').ne',
      Real.log_rpow Real.pi_pos]
  have := h4.congr_of_eventuallyEq hev.symm
  convert this using 1
  rw [Part0.pR, show (s - 1 + 1) / 2 = s / 2 by ring]
  ring

/-- `d/dt log V(t) = −p(t + 1)` for `t > −2`. -/
theorem hasDerivAt_log_ballV {t : ℝ} (ht : -2 < t) :
    HasDerivAt (fun u => Real.log (ballV u)) (-Part0.pR (t + 1)) t := by
  have hu : 0 < t / 2 + 1 := by linarith
  have hdG : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) (t / 2 + 1) :=
    (Real.differentiableAt_Gamma (PilotDigamma.real_ne_neg_nat hu)).log
      (Real.Gamma_pos_of_pos hu).ne'
  have h1 : HasDerivAt (fun u : ℝ => u / 2 + 1) (1 / 2) t := by
    simpa using ((hasDerivAt_id t).div_const 2).add_const 1
  have h3 : HasDerivAt ((Real.log ∘ Real.Gamma) ∘ fun u : ℝ => u / 2 + 1)
      (PilotDigamma.rpsi (t / 2 + 1) * (1 / 2)) t := hdG.hasDerivAt.comp t h1
  have h2 : HasDerivAt (fun u : ℝ => u / 2 * Real.log π) (1 / 2 * Real.log π) t := by
    simpa using ((hasDerivAt_id t).div_const 2).mul_const (Real.log π)
  have h4 := h2.sub h3
  have hev : (fun u : ℝ => u / 2 * Real.log π - ((Real.log ∘ Real.Gamma) ∘ fun u : ℝ => u / 2 + 1) u)
      =ᶠ[nhds t] fun u => Real.log (ballV u) := by
    filter_upwards [lt_mem_nhds ht] with u hu
    have hu' : 0 < u / 2 + 1 := by linarith
    simp only [ballV, Function.comp]
    rw [Real.log_div (Real.rpow_pos_of_pos Real.pi_pos _).ne' (Real.Gamma_pos_of_pos hu').ne',
      Real.log_rpow Real.pi_pos]
  have := h4.congr_of_eventuallyEq hev.symm
  convert this using 1
  rw [Part0.pR, show (t + 1 + 1) / 2 = t / 2 + 1 by ring]
  ring

/-- **The critical pair.** With `x` the zero of `p`, in `(6.2569, 6.25695)`: `log Γ_ℝ` is stationary exactly at
`x + 1 ∈ (7.2569, 7.25695)` on `s > 0`, and the log of the ball volume exactly at `x − 1 ∈ (5.2569, 5.25695)` on
`t > −2`. -/
theorem critical_pair : ∃ x ∈ Ioo (6.2569 : ℝ) 6.25695,
    HasDerivAt (fun t => Real.log (gammaR t)) 0 (x + 1) ∧
    HasDerivAt (fun u => Real.log (ballV u)) 0 (x - 1) ∧
    (∀ s, 0 < s → HasDerivAt (fun t => Real.log (gammaR t)) 0 s → s = x + 1) ∧
    (∀ t, -2 < t → HasDerivAt (fun u => Real.log (ballV u)) 0 t → t = x - 1) := by
  obtain ⟨x, hx, hx0, huniq⟩ := zero_loc
  refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
  · have := hasDerivAt_log_gammaR (s := x + 1) (by linarith [hx.1])
    rwa [show x + 1 - 1 = x by ring, hx0] at this
  · have := hasDerivAt_log_ballV (t := x - 1) (by linarith [hx.1])
    rwa [show x - 1 + 1 = x by ring, hx0, neg_zero] at this
  · intro s hs h
    have e := h.unique (hasDerivAt_log_gammaR hs)
    have := huniq (s - 1) (by linarith) e.symm
    linarith
  · intro t ht h
    have e := h.unique (hasDerivAt_log_ballV ht)
    have := huniq (t + 1) (by linarith) (by linarith)
    linarith

/-! ## Three extrema -/

/-- A function on `(a, ∞)` whose derivative is negative before `x₀` and positive after it is strictly minimal
at `x₀`. -/
theorem strict_min_of_deriv {f g : ℝ → ℝ} {a x0 : ℝ} (hx0 : a < x0)
    (hf : ∀ x, a < x → HasDerivAt f (g x) x) (hneg : ∀ x, a < x → x < x0 → g x < 0)
    (hpos : ∀ x, x0 < x → 0 < g x) : ∀ y, a < y → y ≠ x0 → f x0 < f y := by
  intro y hy hne
  have hcont : ∀ {u v : ℝ}, a < u → ContinuousOn f (Icc u v) := fun hu z hz =>
    (hf z (lt_of_lt_of_le hu hz.1)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with h | h
  · have hm : StrictAntiOn f (Icc y x0) := strictAntiOn_of_deriv_neg (convex_Icc y x0) (hcont hy)
      (fun z hz => by
        rw [interior_Icc] at hz
        rw [(hf z (by linarith [hz.1])).deriv]
        exact hneg z (by linarith [hz.1]) hz.2)
    exact hm ⟨le_refl y, h.le⟩ ⟨h.le, le_refl x0⟩ h
  · have hm : StrictMonoOn f (Icc x0 y) := strictMonoOn_of_deriv_pos (convex_Icc x0 y) (hcont hx0)
      (fun z hz => by
        rw [interior_Icc] at hz
        rw [(hf z (by linarith [hz.1])).deriv]
        exact hpos z hz.1)
    exact hm ⟨le_refl x0, h.le⟩ ⟨h.le, le_refl y⟩ h

theorem gammaR_pos {s : ℝ} (hs : 0 < s) : 0 < gammaR s :=
  mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))

theorem ballV_pos {t : ℝ} (ht : -2 < t) : 0 < ballV t :=
  div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))

theorem OmR_pos {x : ℝ} (hx : -1 < x) : 0 < Part0.OmR x :=
  div_pos (mul_pos two_pos (Real.rpow_pos_of_pos Real.pi_pos _)) (Real.Gamma_pos_of_pos (by linarith))

/-- `V` is BallTower's `ballVol` at the integers. -/
theorem ballV_natCast (n : ℕ) : ballV n = BallTower.ballVol n := by
  unfold ballV BallTower.ballVol
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  ring_nf

/-- `Γ_ℝ(s) = 2/Ω(s − 1)`: the area of `S^{s−1}` is `2/Γ_ℝ(s)` in every real dimension `s > 0`. -/
theorem gammaR_eq_two_div_OmR {s : ℝ} (hs : 0 < s) : gammaR s = 2 / Part0.OmR (s - 1) := by
  unfold gammaR Part0.OmR
  rw [show (s - 1 + 1) / 2 = s / 2 by ring, show -s / 2 = -(s / 2) by ring, Real.rpow_neg Real.pi_pos.le]
  have hG := (Real.Gamma_pos_of_pos (by linarith : 0 < s / 2)).ne'
  have hp := (Real.rpow_pos_of_pos Real.pi_pos (s / 2)).ne'
  field_simp

/-- **One zero, three extrema.** With `x` the zero of `p`, in `(6.2569, 6.25695)`: the ball volume `V` is strictly
maximal on `t > −2` exactly at `x − 1`, the sphere area `Ω` on `y > −1` exactly at `x`, and `Γ_ℝ = 2/Ω(· − 1)` is
strictly minimal on `s > 0` exactly at `x + 1`. -/
theorem three_landmarks : ∃ x ∈ Ioo (6.2569 : ℝ) 6.25695, Part0.pR x = 0 ∧
    (∀ t, -2 < t → t ≠ x - 1 → ballV t < ballV (x - 1)) ∧
    (∀ y, -1 < y → y ≠ x → Part0.OmR y < Part0.OmR x) ∧
    (∀ s, 0 < s → s ≠ x + 1 → gammaR (x + 1) < gammaR s) := by
  obtain ⟨x, hx, hx0, -⟩ := zero_loc
  have hxm : -1 < x := by linarith [hx.1]
  have hneg : ∀ y, -1 < y → y < x → Part0.pR y < 0 := fun y hy hyx => by
    have := Part0.pR_strictMonoOn (mem_Ioi.2 hy) (mem_Ioi.2 hxm) hyx
    rwa [hx0] at this
  have hpos : ∀ y, x < y → 0 < Part0.pR y := fun y hxy => by
    have := Part0.pR_strictMonoOn (mem_Ioi.2 hxm) (mem_Ioi.2 (by linarith)) hxy
    rwa [hx0] at this
  refine ⟨x, hx, hx0, ?_, ?_, ?_⟩
  · intro t ht hne
    have h := strict_min_of_deriv (f := fun u => -Real.log (ballV u)) (g := fun u => Part0.pR (u + 1))
      (a := -2) (x0 := x - 1) (by linarith)
      (fun u hu => by have := (hasDerivAt_log_ballV hu).neg; rwa [neg_neg] at this)
      (fun u hu hux => hneg (u + 1) (by linarith) (by linarith)) (fun u hux => hpos (u + 1) (by linarith))
      t ht hne
    simp only [neg_lt_neg_iff] at h
    exact (Real.log_lt_log_iff (ballV_pos ht) (ballV_pos (by linarith))).1 h
  · intro y hy hne
    have h := strict_min_of_deriv (f := fun u => -Real.log (Part0.OmR u)) (g := Part0.pR)
      (a := -1) (x0 := x) hxm
      (fun u hu => by have := (Part0.hasDerivAt_log_OmR hu).neg; rwa [neg_neg] at this)
      hneg hpos y hy hne
    simp only [neg_lt_neg_iff] at h
    exact (Real.log_lt_log_iff (OmR_pos hy) (OmR_pos hxm)).1 h
  · intro s hs hne
    have h := strict_min_of_deriv (f := fun u => Real.log (gammaR u)) (g := fun u => Part0.pR (u - 1))
      (a := 0) (x0 := x + 1) (by linarith) (fun u hu => hasDerivAt_log_gammaR hu)
      (fun u hu hux => hneg (u - 1) (by linarith) (by linarith)) (fun u hux => hpos (u - 1) (by linarith))
      s hs hne
    exact (Real.log_lt_log_iff (gammaR_pos (by linarith)) (gammaR_pos hs)).1 h

end BinetEnvelope
#print axioms BinetEnvelope.summable_Zs
#print axioms BinetEnvelope.mats_pos
#print axioms BinetEnvelope.hasSum_piece
#print axioms BinetEnvelope.matsTerm_sub
#print axioms BinetEnvelope.phiB_envelope
#print axioms BinetEnvelope.bose_envelope
#print axioms BinetEnvelope.integrableOn_exp_mul_envP
#print axioms BinetEnvelope.integral_exp_mul_envP
#print axioms BinetEnvelope.lapR_envelope
#print axioms BinetEnvelope.rpsi_eq_lapR
#print axioms BinetEnvelope.rpsi_envelope
#print axioms BinetEnvelope.Zs_two
#print axioms BinetEnvelope.Zs_four
#print axioms BinetEnvelope.bernoulli_six
#print axioms BinetEnvelope.Zs_six
#print axioms BinetEnvelope.stirC_zero
#print axioms BinetEnvelope.stirC_one
#print axioms BinetEnvelope.stirC_two
#print axioms BinetEnvelope.phiB_order_one
#print axioms BinetEnvelope.Zs_eq_bernoulli
#print axioms BinetEnvelope.stirC_eq_bernoulli
#print axioms BinetEnvelope.lapP_eq_bernoulli
#print axioms BinetEnvelope.rpsi_stirling2
#print axioms BinetEnvelope.lapR_stirling2
#print axioms BinetEnvelope.eulerMascheroni_sharp
#print axioms BinetEnvelope.rpsi_le_shift
#print axioms BinetEnvelope.le_rpsi_shift
#print axioms BinetEnvelope.log_lt_of_lt_mul_exp
#print axioms BinetEnvelope.lt_log_of_mul_exp_lt
#print axioms BinetEnvelope.lt_mul_exp_of
#print axioms BinetEnvelope.mul_exp_lt_of
#print axioms BinetEnvelope.pi_sq_bounds
#print axioms BinetEnvelope.pR_lo0
#print axioms BinetEnvelope.pR_hi0
#print axioms BinetEnvelope.pR_lo1
#print axioms BinetEnvelope.pR_hi1
#print axioms BinetEnvelope.pR_lo2
#print axioms BinetEnvelope.pR_hi2
#print axioms BinetEnvelope.zero_loc
#print axioms BinetEnvelope.threshold_one_loc
#print axioms BinetEnvelope.threshold_two_loc
#print axioms BinetEnvelope.hasDerivAt_log_gammaR
#print axioms BinetEnvelope.hasDerivAt_log_ballV
#print axioms BinetEnvelope.critical_pair
#print axioms BinetEnvelope.strict_min_of_deriv
#print axioms BinetEnvelope.gammaR_pos
#print axioms BinetEnvelope.ballV_pos
#print axioms BinetEnvelope.OmR_pos
#print axioms BinetEnvelope.ballV_natCast
#print axioms BinetEnvelope.gammaR_eq_two_div_OmR
#print axioms BinetEnvelope.three_landmarks
