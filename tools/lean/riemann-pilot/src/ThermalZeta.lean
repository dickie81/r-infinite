import Mathlib
import BallTower

/-! # Free radiation is the completed zeta function (round 409)

For a gas of free massless quanta in `d` space dimensions (`D = d + 1` spacetime dimensions), with one
internal state, at temperature `T` (units `ħ = c = k_B = 1`), with `Λ = completedRiemannZeta = Γ_ℝ · ζ`:

* `pressureBose_eq`: the Bose–Einstein pressure is `T^{d+1} Λ(d+1)`;
* `pressureBoltz_eq`: the Maxwell–Boltzmann pressure is `T^{d+1} Γ_ℝ(d+1)`, the archimedean factor alone;
* `pressureFermi_eq`: the Fermi–Dirac pressure is `T^{d+1} (1 − 2^{−d}) Λ(d+1)`;
* `energyBose_eq`: the Bose–Einstein energy density is `d T^{d+1} Λ(d+1)`;
* `densityBose_eq`, `densityFermi_eq` (`d ≥ 2`): the number densities are `T^d Γ_ℝ(d+1) ζ(d)` and
  `(1 − 2^{1−d})` times that.

The mechanism is Mathlib's "Mellin transform = Dirichlet series" (`hasSum_mellin`). The occupation
`1/(eᵗ − 1) = Σ_{k≥1} e^{−kt}` and the grand potential `−log(1 − e^{−t}) = Σ_{k≥1} e^{−kt}/k` have Mellin
transforms `Γ(s)ζ(s)` and `Γ(s)ζ(s+1)` (`mellin_bose`, `mellin_boseLog`); in the second, the `k`-th term
is the contribution of exchange cycles of length `k` (Feynman's cycle expansion). The fermion versions
carry the sign `(−1)^{k−1}` of a `k`-cycle (`cycleSign`), and `Σ (−1)^{k−1} k^{−s} = (1 − 2^{1−s}) ζ(s)`
(`tsum_alt_eq`). The momentum integral over `ℝ^d` reduces to the radial one with the area `|S^{d−1}|` of
the unit sphere (`integral_radial`, with BallTower's `sphereArea` and `ballVol_eq_volume`), and Legendre
duplication, in Mathlib's form `Γ_ℝ(s) Γ_ℝ(s+1) = Γ_ℂ(s)`, turns `(2π)^{−d} |S^{d−1}| Γ(d)` into
`Γ_ℝ(d+1)` (`gammaR_succ`, with BallTower's `Γ_ℝ(d) |S^{d−1}| = 2`).

The sign of a `k`-cycle (`cycleSign_eq_sign`) is multiplicative on coprime lengths (`cycleSign_mul`), equal
to `1` at every power of an odd prime and `−1` at every positive power of `2`; it is not completely
multiplicative (`cycleSign_four`).

`pressureBose_eulerProduct` and `densityBose_eulerProduct` write `ζ` as Mathlib's Euler product over the
primes, and `gammaR_eq_two_div_sphereArea` gives `Γ_ℝ(n) = 2/|S^{n−1}|`. At `d = 3`: `Λ(4) = π²/90`, and per
internal state `P = π²T⁴/90`, `ρ = π²T⁴/30`, `n = ζ(3)T³/π²`, with the fermion factors `7/8` and `3/4`
(`completedRiemannZeta_four` and the `_three` theorems). The last section computes the first two eigenvalues
of the Gaussian kernel of Part II=III's Open Question on the Hawking spectrum (`kern_ground`, `kern_first`,
`kern_ratio_value`).

Since round 410 the sphere area, the ball volume, `Γ_ℝ(n) |S^{n−1}| = 2` and `Λ = Γ_ℝ ζ` are BallTower's
(round 184); round 409's own copies are removed. ThermalJoins.lean joins this file to the rest of the pilot.
-/

open Real MeasureTheory Set

namespace ThermalZeta

noncomputable section

/-! ## Occupations and grand potentials per mode -/

/-- Bose–Einstein occupation `1/(eᵗ − 1)`. -/
def bose (t : ℝ) : ℝ := 1 / (Real.exp t - 1)

/-- Fermi–Dirac occupation `1/(eᵗ + 1)`. -/
def fermi (t : ℝ) : ℝ := 1 / (Real.exp t + 1)

/-- Bose grand potential per mode, in units of `−T`: `−log(1 − e^{−t})`. -/
def boseLog (t : ℝ) : ℝ := -Real.log (1 - Real.exp (-t))

/-- Fermi grand potential per mode, in units of `−T`: `log(1 + e^{−t})`. -/
def fermiLog (t : ℝ) : ℝ := Real.log (1 + Real.exp (-t))

lemma exp_neg_lt_one {t : ℝ} (ht : 0 < t) : Real.exp (-t) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)

lemma abs_exp_neg_lt_one {t : ℝ} (ht : 0 < t) : |Real.exp (-t)| < 1 := by
  rw [abs_of_pos (Real.exp_pos _)]; exact exp_neg_lt_one ht

lemma exp_neg_succ_mul (t : ℝ) (i : ℕ) :
    Real.exp (-((i : ℝ) + 1) * t) = Real.exp (-t) ^ (i + 1) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- `1/(eᵗ − 1) = Σ_{k≥1} e^{−kt}`. -/
lemma hasSum_bose {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℕ => Real.exp (-((i : ℝ) + 1) * t)) (bose t) := by
  have h := (hasSum_geometric_of_lt_one (Real.exp_pos (-t)).le (exp_neg_lt_one ht)).mul_left
    (Real.exp (-t))
  have h1 : 1 < Real.exp t := by simpa using Real.exp_lt_exp.mpr ht
  have h0 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have h2 : Real.exp t - 1 ≠ 0 := (sub_pos.mpr h1).ne'
  convert h using 1
  · funext i; rw [exp_neg_succ_mul, pow_succ']
  · rw [bose, Real.exp_neg]
    field_simp

/-- The cycle expansion: `−log(1 − e^{−t}) = Σ_{k≥1} e^{−kt}/k`. -/
lemma hasSum_boseLog {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℕ => 1 / ((i : ℝ) + 1) * Real.exp (-((i : ℝ) + 1) * t)) (boseLog t) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (abs_exp_neg_lt_one ht)
  convert h using 1
  · funext i; rw [exp_neg_succ_mul]; ring
  · rfl

/-- `1/(eᵗ + 1) = Σ_{k≥1} (−1)^{k−1} e^{−kt}`. -/
lemma hasSum_fermi {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℕ => (-1) ^ i * Real.exp (-((i : ℝ) + 1) * t)) (fermi t) := by
  have hr : |-Real.exp (-t)| < 1 := by rw [abs_neg]; exact abs_exp_neg_lt_one ht
  have h := (hasSum_geometric_of_abs_lt_one hr).mul_left (Real.exp (-t))
  have h0 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have h2 : Real.exp t + 1 ≠ 0 := by positivity
  have h3 : 1 + Real.exp t ≠ 0 := by positivity
  convert h using 1
  · funext i; rw [exp_neg_succ_mul, pow_succ', neg_pow (Real.exp (-t))]; ring
  · rw [fermi, Real.exp_neg, sub_neg_eq_add]
    field_simp

/-- `log(1 + e^{−t}) = Σ_{k≥1} (−1)^{k−1} e^{−kt}/k`. -/
lemma hasSum_fermiLog {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℕ => (-1) ^ i / ((i : ℝ) + 1) * Real.exp (-((i : ℝ) + 1) * t)) (fermiLog t) := by
  have hr : |-Real.exp (-t)| < 1 := by rw [abs_neg]; exact abs_exp_neg_lt_one ht
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hr).neg
  convert h using 1
  · funext i; rw [exp_neg_succ_mul, neg_pow (Real.exp (-t)), pow_succ (-1 : ℝ)]; ring
  · rw [fermiLog, sub_neg_eq_add, neg_neg]

lemma hasSum_cast {b : ℕ → ℝ} {v t : ℝ}
    (h : HasSum (fun i : ℕ => b i * Real.exp (-((i : ℝ) + 1) * t)) v) :
    HasSum (fun i : ℕ => (b i : ℂ) * (Real.exp (-((i : ℝ) + 1) * t) : ℂ)) (v : ℂ) := by
  have := Complex.hasSum_ofReal.mpr h
  simpa only [Complex.ofReal_mul] using this

lemma summable_succ_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ σ) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hσ)
  simpa [Nat.cast_add, Nat.cast_one] using this

/-! ## Mellin transforms: the Dirichlet series appear -/

/-- **Bose–Einstein number moment.** `∫₀^∞ t^{s−1}/(eᵗ − 1) dt = Γ(s) ζ(s)` for `Re s > 1`. -/
theorem mellin_bose {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => (bose t : ℂ)) s = Complex.Gamma s * riemannZeta s := by
  have key := hasSum_mellin (a := fun _ : ℕ => ((1 : ℝ) : ℂ)) (p := fun i : ℕ => (i : ℝ) + 1)
    (F := fun t => (bose t : ℂ)) (fun i => Or.inr (by positivity)) (by linarith)
    (fun t ht => hasSum_cast (b := fun _ => 1) (by simpa using hasSum_bose ht))
    (by simpa using summable_succ_rpow hs)
  rw [← key.tsum_eq, zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← tsum_mul_left]
  congr 1; funext i; push_cast; ring

/-- **The cycle expansion of the Bose grand potential.** `∫₀^∞ t^{s−1}(−log(1 − e^{−t})) dt` is the sum
over cycle lengths `k ≥ 1` of `Γ(s)/k^{s+1}`. -/
theorem hasSum_mellin_boseLog {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun i : ℕ => Complex.Gamma s / ((i : ℂ) + 1) ^ (s + 1))
      (mellin (fun t => (boseLog t : ℂ)) s) := by
  have key := hasSum_mellin (a := fun i : ℕ => ((1 / ((i : ℝ) + 1) : ℝ) : ℂ))
    (p := fun i : ℕ => (i : ℝ) + 1) (F := fun t => (boseLog t : ℂ))
    (fun i => Or.inr (by positivity)) hs
    (fun t ht => hasSum_cast (hasSum_boseLog ht))
    (by
      refine (summable_succ_rpow (σ := 1 + s.re) (by linarith)).congr (fun i => ?_)
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Real.rpow_add hi,
        Real.rpow_one]
      field_simp)
  convert key using 1
  funext i
  have h0 : ((i : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero i
  push_cast
  rw [Complex.cpow_add _ _ h0, Complex.cpow_one]
  field_simp

/-- **Bose–Einstein grand potential.** `∫₀^∞ t^{s−1}(−log(1 − e^{−t})) dt = Γ(s) ζ(s+1)` for `Re s > 0`. -/
theorem mellin_boseLog {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t => (boseLog t : ℂ)) s = Complex.Gamma s * riemannZeta (s + 1) := by
  have hs1 : 1 < (s + 1).re := by simp; linarith
  rw [← (hasSum_mellin_boseLog hs).tsum_eq, zeta_eq_tsum_one_div_nat_add_one_cpow hs1,
    ← tsum_mul_left]
  congr 1; funext i; ring

/-- **The fermion sign changes only the factor at `2`.** `Σ_{n≥0} (−1)ⁿ/(n+1)^s = (1 − 2^{1−s}) ζ(s)` for
`Re s > 1`. -/
theorem tsum_alt_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf_def
  have hnorm : ∀ n : ℕ, ‖f n‖ = 1 / ((n : ℝ) + 1) ^ s.re := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hf_def, norm_div, norm_one]
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hf : Summable f :=
    Summable.of_norm ((summable_succ_rpow hs).congr (fun n => (hnorm n).symm))
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective (fun a b h => by simpa using h)
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective (fun a b h => by simpa using h)
  have hge : ∀ k : ℕ, f (2 * k) = (-1 : ℂ) ^ (2 * k) / ((↑(2 * k) : ℂ) + 1) ^ s := by
    intro k; simp [hf_def, pow_mul]
  have hgo : ∀ k : ℕ, -f (2 * k + 1) = (-1 : ℂ) ^ (2 * k + 1) / ((↑(2 * k + 1) : ℂ) + 1) ^ s := by
    intro k; simp only [hf_def, pow_succ, pow_mul]; norm_num; ring
  have hsplit_alt : ∑' k : ℕ, (-1 : ℂ) ^ (2 * k) / ((↑(2 * k) : ℂ) + 1) ^ s +
      ∑' k : ℕ, (-1 : ℂ) ^ (2 * k + 1) / ((↑(2 * k + 1) : ℂ) + 1) ^ s =
      ∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s :=
    tsum_even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ s)
      (he.congr hge) (ho.neg.congr hgo)
  have hsplit := tsum_even_add_odd he ho
  have hodd : ∑' k, f (2 * k + 1) = 2 ^ (-s) * riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← tsum_mul_left]
    congr 1; funext k
    simp only [hf_def]
    have h2 : ((↑(2 * k + 1) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity), Complex.cpow_neg]
    push_cast
    field_simp
  have hzeta : riemannZeta s = ∑' n, f n := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have h2s : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  have hE : ∑' k : ℕ, (-1 : ℂ) ^ (2 * k) / ((↑(2 * k) : ℂ) + 1) ^ s = ∑' k, f (2 * k) :=
    tsum_congr (fun k => (hge k).symm)
  have hO : ∑' k : ℕ, (-1 : ℂ) ^ (2 * k + 1) / ((↑(2 * k + 1) : ℂ) + 1) ^ s =
      -∑' k, f (2 * k + 1) := by
    rw [← tsum_neg]; exact tsum_congr (fun k => (hgo k).symm)
  rw [← hsplit_alt, hE, hO, h2s, hzeta, ← hsplit]
  rw [hzeta, ← hsplit] at hodd
  linear_combination (-2 : ℂ) * hodd

/-- **Fermi–Dirac number moment.** `∫₀^∞ t^{s−1}/(eᵗ + 1) dt = Γ(s)(1 − 2^{1−s}) ζ(s)` for `Re s > 1`. -/
theorem mellin_fermi {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => (fermi t : ℂ)) s = Complex.Gamma s * ((1 - 2 ^ (1 - s)) * riemannZeta s) := by
  have key := hasSum_mellin (a := fun i : ℕ => (((-1) ^ i : ℝ) : ℂ))
    (p := fun i : ℕ => (i : ℝ) + 1) (F := fun t => (fermi t : ℂ))
    (fun i => Or.inr (by positivity)) (by linarith)
    (fun t ht => hasSum_cast (hasSum_fermi ht))
    (by simpa using summable_succ_rpow hs)
  rw [← key.tsum_eq, ← tsum_alt_eq hs, ← tsum_mul_left]
  congr 1; funext i; push_cast; ring

/-- **Fermi–Dirac grand potential.** `∫₀^∞ t^{s−1} log(1 + e^{−t}) dt = Γ(s)(1 − 2^{−s}) ζ(s+1)` for
`Re s > 0`. -/
theorem mellin_fermiLog {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t => (fermiLog t : ℂ)) s =
      Complex.Gamma s * ((1 - 2 ^ (-s)) * riemannZeta (s + 1)) := by
  have hs1 : 1 < (s + 1).re := by simp; linarith
  have key := hasSum_mellin (a := fun i : ℕ => (((-1) ^ i / ((i : ℝ) + 1) : ℝ) : ℂ))
    (p := fun i : ℕ => (i : ℝ) + 1) (F := fun t => (fermiLog t : ℂ))
    (fun i => Or.inr (by positivity)) hs
    (fun t ht => hasSum_cast (hasSum_fermiLog ht))
    (by
      refine (summable_succ_rpow (σ := 1 + s.re) (by linarith)).congr (fun i => ?_)
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_pos hi, Real.rpow_add hi, Real.rpow_one]
      field_simp)
  rw [show (2 : ℂ) ^ (-s) = 2 ^ (1 - (s + 1)) by ring_nf]
  rw [← key.tsum_eq, ← tsum_alt_eq hs1, ← tsum_mul_left]
  congr 1; funext i
  have h0 : ((i : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero i
  push_cast
  rw [Complex.cpow_add _ _ h0, Complex.cpow_one]
  field_simp

/-- **Maxwell–Boltzmann.** `∫₀^∞ t^{s−1} e^{−t} dt = Γ(s)`: the archimedean factor alone. -/
theorem mellin_boltz {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t => (Real.exp (-t) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [smul_eq_mul, mul_comm]

/-! ## Momentum space `ℝ^d` -/

section Space

variable (d : ℕ)

/-- **The radial reduction.** `∫_{ℝ^d} f(|k|) dk = |S^{d−1}| ∫₀^∞ y^{d−1} f(y) dy`, with BallTower's
`sphereArea d = d · ballVol d` and `ballVol_eq_volume`. -/
lemma integral_radial (hd : 1 ≤ d) (f : ℝ → ℝ) :
    ∫ k : EuclideanSpace ℝ (Fin d), f ‖k‖ =
      BallTower.sphereArea d * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * f y := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have : NeZero d := ⟨by omega⟩
  rw [integral_fun_norm_addHaar volume f, finrank_euclideanSpace_fin, measureReal_def,
    BallTower.ballVol_eq_volume, BallTower.sphereArea, nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  ring

/-- **Temperature scaling.** `∫_{ℝ^d} f(|k|/T) dk = T^d ∫_{ℝ^d} f(|k|) dk`. -/
lemma integral_scale {T : ℝ} (hT : 0 < T) (f : ℝ → ℝ) :
    ∫ k : EuclideanSpace ℝ (Fin d), f (‖k‖ / T) =
      T ^ d * ∫ k : EuclideanSpace ℝ (Fin d), f ‖k‖ := by
  have h := MeasureTheory.Measure.integral_comp_smul
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (fun k => f ‖k‖) T⁻¹
  rw [finrank_euclideanSpace_fin] at h
  have hfun : (fun k : EuclideanSpace ℝ (Fin d) => f (‖k‖ / T)) = fun k => f ‖T⁻¹ • k‖ := by
    funext k
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT, div_eq_inv_mul]
  rw [hfun, h, abs_of_pos (by positivity), inv_pow, inv_inv, smul_eq_mul]

/-- The Mellin transform at a positive integer is the radial integral. -/
lemma mellin_natCast (hd : 1 ≤ d) (f : ℝ → ℝ) :
    mellin (fun t => (f t : ℂ)) (d : ℂ) =
      ((∫ y in Ioi (0 : ℝ), y ^ (d - 1) * f y : ℝ) : ℂ) := by
  rw [mellin, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  have : (d : ℂ) - 1 = ((d - 1 : ℕ) : ℂ) := by rw [Nat.cast_sub hd, Nat.cast_one]
  rw [smul_eq_mul, this, Complex.cpow_natCast]
  push_cast
  ring

/-- **Legendre duplication, phase-space form.** `(2π)^{−d} |S^{d−1}| Γ(d) = Γ_ℝ(d+1)`, from Mathlib's
`Γ_ℝ(d) Γ_ℝ(d+1) = Γ_ℂ(d)` and BallTower's `Γ_ℝ(d) |S^{d−1}| = 2`. -/
lemma gammaR_succ (hd : 1 ≤ d) :
    ((((2 * π) ^ d)⁻¹ * BallTower.sphereArea d : ℝ) : ℂ) * Complex.Gamma d =
      Complex.Gammaℝ ((d : ℂ) + 1) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hR : Complex.Gammaℝ (d : ℂ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hdpos)
  have hS := BallTower.Gammaℝ_mul_sphereArea d hd
  apply mul_left_cancel₀ hR
  rw [Complex.Gammaℝ_mul_Gammaℝ_add_one, Complex.Gammaℂ_def, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  linear_combination (((2 * (π : ℂ)) ^ d)⁻¹ * Complex.Gamma d) * hS

/-! ### The thermodynamic quantities -/

/-- Bose–Einstein pressure, one internal state: `T ∫ d^dk/(2π)^d (−log(1 − e^{−|k|/T}))`. -/
def pressureBose (T : ℝ) : ℝ :=
  T * ((2 * π) ^ d)⁻¹ * ∫ k : EuclideanSpace ℝ (Fin d), boseLog (‖k‖ / T)

/-- Fermi–Dirac pressure, one internal state: `T ∫ d^dk/(2π)^d log(1 + e^{−|k|/T})`. -/
def pressureFermi (T : ℝ) : ℝ :=
  T * ((2 * π) ^ d)⁻¹ * ∫ k : EuclideanSpace ℝ (Fin d), fermiLog (‖k‖ / T)

/-- Maxwell–Boltzmann pressure, one internal state: `T ∫ d^dk/(2π)^d e^{−|k|/T}`. -/
def pressureBoltz (T : ℝ) : ℝ :=
  T * ((2 * π) ^ d)⁻¹ * ∫ k : EuclideanSpace ℝ (Fin d), Real.exp (-(‖k‖ / T))

/-- Bose–Einstein number density: `∫ d^dk/(2π)^d 1/(e^{|k|/T} − 1)`. -/
def densityBose (T : ℝ) : ℝ :=
  ((2 * π) ^ d)⁻¹ * ∫ k : EuclideanSpace ℝ (Fin d), bose (‖k‖ / T)

/-- Fermi–Dirac number density: `∫ d^dk/(2π)^d 1/(e^{|k|/T} + 1)`. -/
def densityFermi (T : ℝ) : ℝ :=
  ((2 * π) ^ d)⁻¹ * ∫ k : EuclideanSpace ℝ (Fin d), fermi (‖k‖ / T)

/-- Bose–Einstein energy density: `∫ d^dk/(2π)^d |k|/(e^{|k|/T} − 1)`. -/
def energyBose (T : ℝ) : ℝ :=
  ((2 * π) ^ d)⁻¹ * ∫ k : EuclideanSpace ℝ (Fin d), ‖k‖ * bose (‖k‖ / T)

/-- The common reduction: `T^a ((2π)^d)⁻¹ ∫ f(|k|/T) dk = T^{a+d} (2π)^{−d} |S^{d−1}| ∫₀^∞ y^{d−1} f(y) dy`,
cast to `ℂ` and evaluated by a Mellin transform at `s = d`. -/
lemma reduce (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) (f : ℝ → ℝ) {M : ℂ}
    (hM : mellin (fun t => (f t : ℂ)) (d : ℂ) = M) :
    ((((2 * π) ^ d)⁻¹ * ∫ k : EuclideanSpace ℝ (Fin d), f (‖k‖ / T) : ℝ) : ℂ) =
      (T : ℂ) ^ d * (((((2 * π) ^ d)⁻¹ * BallTower.sphereArea d : ℝ) : ℂ) * M) := by
  rw [mellin_natCast d hd] at hM
  rw [integral_scale d hT, integral_radial d hd, ← hM]
  push_cast
  ring

/-- **Bose–Einstein pressure is the completed zeta function:** `P = T^{d+1} Λ(d+1)`. -/
theorem pressureBose_eq (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (pressureBose d T : ℂ) = (T : ℂ) ^ (d + 1) * completedRiemannZeta ((d : ℂ) + 1) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 0 < (d : ℂ).re := by simpa using hdpos
  have hs1 : 1 < ((d : ℂ) + 1).re := by simp; linarith
  have h := reduce d hd hT boseLog (mellin_boseLog hs)
  rw [pressureBose, mul_assoc, Complex.ofReal_mul, h,
    BallTower.completed_eq_Gammaℝ_mul hs1, ← gammaR_succ d hd]
  ring

/-- **Fermi–Dirac pressure:** `P = T^{d+1} (1 − 2^{−d}) Λ(d+1)`. -/
theorem pressureFermi_eq (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (pressureFermi d T : ℂ) =
      (T : ℂ) ^ (d + 1) * ((1 - 2 ^ (-(d : ℂ))) * completedRiemannZeta ((d : ℂ) + 1)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 0 < (d : ℂ).re := by simpa using hdpos
  have hs1 : 1 < ((d : ℂ) + 1).re := by simp; linarith
  have h := reduce d hd hT fermiLog (mellin_fermiLog hs)
  rw [pressureFermi, mul_assoc, Complex.ofReal_mul, h,
    BallTower.completed_eq_Gammaℝ_mul hs1, ← gammaR_succ d hd]
  ring

/-- **Maxwell–Boltzmann pressure is the archimedean factor alone:** `P = T^{d+1} Γ_ℝ(d+1)`. -/
theorem pressureBoltz_eq (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (pressureBoltz d T : ℂ) = (T : ℂ) ^ (d + 1) * Complex.Gammaℝ ((d : ℂ) + 1) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 0 < (d : ℂ).re := by simpa using hdpos
  have h := reduce d hd hT (fun t => Real.exp (-t)) (mellin_boltz hs)
  rw [pressureBoltz, mul_assoc, Complex.ofReal_mul, h, ← gammaR_succ d hd]
  ring

/-- **Bose–Einstein number density** (`d ≥ 2`): `n = T^d Γ_ℝ(d+1) ζ(d)`. -/
theorem densityBose_eq (hd : 2 ≤ d) {T : ℝ} (hT : 0 < T) :
    (densityBose d T : ℂ) = (T : ℂ) ^ d * (Complex.Gammaℝ ((d : ℂ) + 1) * riemannZeta d) := by
  have hd1 : 1 ≤ d := by omega
  have hs : 1 < (d : ℂ).re := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    simp; linarith
  have h := reduce d hd1 hT bose (mellin_bose hs)
  rw [densityBose, h, ← gammaR_succ d hd1]
  ring

/-- **Fermi–Dirac number density** (`d ≥ 2`): `n = T^d Γ_ℝ(d+1) (1 − 2^{1−d}) ζ(d)`. -/
theorem densityFermi_eq (hd : 2 ≤ d) {T : ℝ} (hT : 0 < T) :
    (densityFermi d T : ℂ) =
      (T : ℂ) ^ d * (Complex.Gammaℝ ((d : ℂ) + 1) * ((1 - 2 ^ (1 - (d : ℂ))) * riemannZeta d)) := by
  have hd1 : 1 ≤ d := by omega
  have hs : 1 < (d : ℂ).re := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    simp; linarith
  have h := reduce d hd1 hT fermi (mellin_fermi hs)
  rw [densityFermi, h, ← gammaR_succ d hd1]
  ring

/-- **Bose–Einstein energy density:** `ρ = d T^{d+1} Λ(d+1)`. -/
theorem energyBose_eq (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (energyBose d T : ℂ) = d * ((T : ℂ) ^ (d + 1) * completedRiemannZeta ((d : ℂ) + 1)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 1 < ((d : ℂ) + 1).re := by simp; linarith
  -- `|k| bose(|k|/T) = T · g(|k|/T)` with `g y = y · bose y`, and `mellin g d = mellin bose (d+1)`.
  have hg : mellin (fun t => ((t * bose t : ℝ) : ℂ)) (d : ℂ) =
      Complex.Gamma ((d : ℂ) + 1) * riemannZeta ((d : ℂ) + 1) := by
    rw [← mellin_bose hs, mellin, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    simp only [smul_eq_mul]
    push_cast
    rw [show (d : ℂ) + 1 - 1 = ((d : ℂ) - 1) + 1 by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
    ring
  have h := reduce d hd hT (fun t => t * bose t) hg
  have hfun : (fun k : EuclideanSpace ℝ (Fin d) => ‖k‖ * bose (‖k‖ / T)) =
      fun k => T * ((‖k‖ / T) * bose (‖k‖ / T)) := by
    funext k; field_simp
  rw [energyBose, hfun, integral_const_mul, mul_left_comm, Complex.ofReal_mul, h,
    BallTower.completed_eq_Gammaℝ_mul hs, ← gammaR_succ d hd,
    Complex.Gamma_add_one _ (by exact_mod_cast hdpos.ne')]
  ring

/-- **The finite places as an Euler product** (`d ≥ 2`): `n_BE = T^d Γ_ℝ(d+1) ∏_p (1 − p^{−d})⁻¹`. -/
theorem densityBose_eulerProduct (hd : 2 ≤ d) {T : ℝ} (hT : 0 < T) :
    (densityBose d T : ℂ) = (T : ℂ) ^ d * (Complex.Gammaℝ ((d : ℂ) + 1) *
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(d : ℂ)))⁻¹) := by
  have hs : 1 < (d : ℂ).re := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    simp; linarith
  rw [densityBose_eq d hd hT, riemannZeta_eulerProduct_tprod hs]

/-- **The finite places as an Euler product:** `P_BE = T^{d+1} Γ_ℝ(d+1) ∏_p (1 − p^{−(d+1)})⁻¹`. -/
theorem pressureBose_eulerProduct (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (pressureBose d T : ℂ) = (T : ℂ) ^ (d + 1) * (Complex.Gammaℝ ((d : ℂ) + 1) *
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-((d : ℂ) + 1)))⁻¹) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 1 < ((d : ℂ) + 1).re := by simp; linarith
  rw [pressureBose_eq d hd hT, BallTower.completed_eq_Gammaℝ_mul hs,
    riemannZeta_eulerProduct_tprod hs]

/-- The real-place factor is twice the inverse area of the unit sphere: `Γ_ℝ(n) = 2/|S^{n−1}|`, BallTower's
`Gammaℝ_mul_sphereArea` divided out. -/
theorem gammaR_eq_two_div_sphereArea (n : ℕ) (hn : 1 ≤ n) :
    Complex.Gammaℝ (n : ℂ) = 2 / (BallTower.sphereArea n : ℂ) := by
  have hS : (BallTower.sphereArea n : ℂ) ≠ 0 := by exact_mod_cast (BallTower.sphereArea_pos hn).ne'
  rw [eq_div_iff hS]
  exact BallTower.Gammaℝ_mul_sphereArea n hn

end Space

/-! ## Our universe: `d = 3` -/

lemma gammaR_four : Complex.Gammaℝ 4 = 1 / (π : ℂ) ^ 2 := by
  rw [Complex.Gammaℝ_def, show -(4 : ℂ) / 2 = ((-2 : ℤ) : ℂ) by push_cast; ring,
    Complex.cpow_intCast, show (4 : ℂ) / 2 = 1 + 1 by norm_num, Complex.Gamma_add_one _ one_ne_zero,
    Complex.Gamma_one]
  simp [zpow_neg]

/-- `Λ(4) = π²/90`. -/
theorem completedRiemannZeta_four : completedRiemannZeta 4 = (π : ℂ) ^ 2 / 90 := by
  rw [BallTower.completed_eq_Gammaℝ_mul (by norm_num), gammaR_four, riemannZeta_four]
  have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  field_simp

/-- Radiation pressure per internal state: `P = π² T⁴/90`. -/
theorem pressureBose_three {T : ℝ} (hT : 0 < T) :
    (pressureBose 3 T : ℂ) = (π : ℂ) ^ 2 / 90 * (T : ℂ) ^ 4 := by
  rw [pressureBose_eq 3 (by norm_num) hT]
  norm_num [completedRiemannZeta_four]
  ring

/-- Radiation energy density per internal state: `ρ = π² T⁴/30`, the coefficient of Part V's
`(π²/30) g_eff T⁴`. -/
theorem energyBose_three {T : ℝ} (hT : 0 < T) :
    (energyBose 3 T : ℂ) = (π : ℂ) ^ 2 / 30 * (T : ℂ) ^ 4 := by
  rw [energyBose_eq 3 (by norm_num) hT]
  norm_num [completedRiemannZeta_four]
  ring

/-- The fermion factor `7/8 = 1 − 2^{−3}`: `P_FD = (7/8) π² T⁴/90`. -/
theorem pressureFermi_three {T : ℝ} (hT : 0 < T) :
    (pressureFermi 3 T : ℂ) = 7 / 8 * ((π : ℂ) ^ 2 / 90 * (T : ℂ) ^ 4) := by
  rw [pressureFermi_eq 3 (by norm_num) hT]
  have h8 : (2 : ℂ) ^ (-((3 : ℕ) : ℂ)) = 1 / 8 := by
    rw [Complex.cpow_neg, Complex.cpow_natCast]; norm_num
  rw [h8]
  norm_num [completedRiemannZeta_four]
  ring

/-- Photon number density per internal state: `n = ζ(3) T³/π²`. -/
theorem densityBose_three {T : ℝ} (hT : 0 < T) :
    (densityBose 3 T : ℂ) = riemannZeta 3 / (π : ℂ) ^ 2 * (T : ℂ) ^ 3 := by
  rw [densityBose_eq 3 (by norm_num) hT]
  norm_num [gammaR_four]
  ring

/-- The fermion number factor `3/4 = 1 − 2^{1−3}`: `n_FD = (3/4) ζ(3) T³/π²`. -/
theorem densityFermi_three {T : ℝ} (hT : 0 < T) :
    (densityFermi 3 T : ℂ) = 3 / 4 * (riemannZeta 3 / (π : ℂ) ^ 2 * (T : ℂ) ^ 3) := by
  rw [densityFermi_eq 3 (by norm_num) hT]
  have h4 : (2 : ℂ) ^ (1 - ((3 : ℕ) : ℂ)) = 1 / 4 := by
    rw [show (1 : ℂ) - ((3 : ℕ) : ℂ) = ((-2 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
    norm_num
  rw [h4]
  norm_num [gammaR_four]
  ring

/-- The mean energy of a thermal photon: `ρ/n = 3 ζ(4)/ζ(3) · T`. -/
theorem meanEnergy_three {T : ℝ} (hT : 0 < T) :
    (energyBose 3 T : ℂ) / (densityBose 3 T : ℂ) = 3 * riemannZeta 4 / riemannZeta 3 * T := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  have hz3 : riemannZeta 3 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  rw [energyBose_three hT, densityBose_three hT, riemannZeta_four]
  field_simp
  ring

/-! ## The sign of an exchange cycle -/

/-- The sign of an exchange cycle of length `k`: `−1` for even `k`, `1` for odd `k`. -/
def cycleSign (k : ℕ) : ℤ := if Even k then -1 else 1

lemma cycleSign_eq (k : ℕ) (hk : 0 < k) : cycleSign k = (-1) ^ (k - 1) := by
  rcases Nat.even_or_odd k with he | ho
  · have hodd : Odd (k - 1) := by
      obtain ⟨r, rfl⟩ := he
      exact ⟨r - 1, by omega⟩
    simp [cycleSign, he, hodd.neg_one_pow]
  · have hev : Even (k - 1) := by
      obtain ⟨r, rfl⟩ := ho
      exact ⟨r, by omega⟩
    simp [cycleSign, Nat.not_even_iff_odd.mpr ho, hev.neg_one_pow]

/-- `cycleSign k` is the sign of the cyclic permutation `finRotate k`, a `k`-cycle. -/
theorem cycleSign_eq_sign (k : ℕ) (hk : 0 < k) :
    ((Equiv.Perm.sign (finRotate k) : ℤˣ) : ℤ) = cycleSign k := by
  rw [sign_finRotate, cycleSign_eq k hk]
  push_cast
  rfl

/-- The `k`-th coefficient of the fermion series is the cycle sign: `(−1)^i = cycleSign (i+1)`. -/
lemma cycleSign_succ (i : ℕ) : ((cycleSign (i + 1) : ℤ) : ℝ) = (-1) ^ i := by
  rw [cycleSign_eq (i + 1) (Nat.succ_pos i)]
  push_cast
  simp

/-- The cycle sign is multiplicative on coprime lengths. -/
theorem cycleSign_mul {m n : ℕ} (h : Nat.Coprime m n) :
    cycleSign (m * n) = cycleSign m * cycleSign n := by
  unfold cycleSign
  by_cases hm : Even m <;> by_cases hn : Even n
  · exfalso
    have h2 : 2 ∣ Nat.gcd m n := Nat.dvd_gcd (even_iff_two_dvd.mp hm) (even_iff_two_dvd.mp hn)
    rw [Nat.Coprime.gcd_eq_one h] at h2
    omega
  · have hmn : Even (m * n) := hm.mul_right n
    simp [hm, hn, hmn]
  · have hmn : Even (m * n) := hn.mul_left m
    simp [hm, hn, hmn]
  · have hmn : ¬Even (m * n) := by rw [Nat.even_mul]; tauto
    simp [hm, hn, hmn]

/-- At every power of an odd prime the cycle sign is `1`. -/
theorem cycleSign_odd_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    cycleSign (p ^ k) = 1 := by
  have : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  simp [cycleSign, Nat.not_even_iff_odd.mpr this]

/-- At every positive power of `2` the cycle sign is `−1`. -/
theorem cycleSign_two_pow {k : ℕ} (hk : 0 < k) : cycleSign (2 ^ k) = -1 := by
  have : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk.ne'⟩
  simp [cycleSign, this]

/-- The cycle sign is not completely multiplicative: `cycleSign 4 ≠ cycleSign 2 · cycleSign 2`. -/
theorem cycleSign_four : cycleSign 4 ≠ cycleSign 2 * cycleSign 2 := by
  decide

/-! ## Part II=III's Gaussian kernel: the first two eigenvalues

Part II=III's Open Question on the Hawking spectrum states that "the cascade's Gaussian parameters
`$(a=15/4,\,b=7/4)$` give `$r=0.2476$`", for "a reduced density matrix with geometric eigenvalues
`$p_n = (1-r)r^n$`". For the kernel
`K(x, y) = exp(−a(x² + y²)/2 + bxy)` with `c = √(a² − b²)`, the functions `e^{−cx²/2}` and `x e^{−cx²/2}` are
eigenfunctions with eigenvalues `λ₀ = √(2π/(a+c))` and `λ₁ = (b/(a+c)) λ₀` (`kern_ground`, `kern_first`); the
whole spectrum `λₙ = λ₀ (b/(a+c))ⁿ` is Mehler's formula, which is not formalized here. At `(15/4, 7/4)`,
`c = √11` and `b/(a+c) = 7/(15 + 4√11) ∈ (0.24764, 0.24765)` (`kern_ratio_value`). -/

/-- `∫ exp(−αy² + βy) dy = √(π/α) e^{β²/(4α)}`. -/
lemma integral_exp_quad {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∫ y : ℝ, Real.exp (-α * y ^ 2 + β * y) = √(π / α) * Real.exp (β ^ 2 / (4 * α)) := by
  have hshift : ∀ y : ℝ, Real.exp (-α * y ^ 2 + β * y) =
      Real.exp (β ^ 2 / (4 * α)) * Real.exp (-α * (y - β / (2 * α)) ^ 2) := by
    intro y; rw [← Real.exp_add]; congr 1; field_simp; ring
  simp_rw [hshift]
  have ht := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => Real.exp (-α * y ^ 2))
    (β / (2 * α))
  rw [integral_const_mul, ht, integral_gaussian]
  ring

/-- `∫ y exp(−αy² + βy) dy = (β/(2α)) √(π/α) e^{β²/(4α)}`. -/
lemma integral_mul_exp_quad {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∫ y : ℝ, y * Real.exp (-α * y ^ 2 + β * y) =
      β / (2 * α) * (√(π / α) * Real.exp (β ^ 2 / (4 * α))) := by
  set m := β / (2 * α) with hm
  have hshift : ∀ y : ℝ, y * Real.exp (-α * y ^ 2 + β * y) =
      Real.exp (β ^ 2 / (4 * α)) *
        ((fun u : ℝ => u * Real.exp (-α * u ^ 2) + m * Real.exp (-α * u ^ 2)) (y - m)) := by
    intro y
    have h : Real.exp (-α * y ^ 2 + β * y) =
        Real.exp (β ^ 2 / (4 * α)) * Real.exp (-α * (y - m) ^ 2) := by
      rw [← Real.exp_add]; congr 1; rw [hm]; field_simp; ring
    rw [h]; ring
  simp_rw [hshift]
  rw [integral_const_mul, integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => u * Real.exp (-α * u ^ 2) + m * Real.exp (-α * u ^ 2)) m]
  have hodd : ∫ y : ℝ, y * Real.exp (-α * y ^ 2) = 0 := by
    have h := integral_neg_eq_self (fun y : ℝ => y * Real.exp (-α * y ^ 2)) volume
    simp only [neg_mul, even_two, Even.neg_pow, integral_neg] at h
    simp only [neg_mul]
    linarith
  rw [integral_add (integrable_mul_exp_neg_mul_sq hα) ((integrable_exp_neg_mul_sq hα).const_mul m),
    hodd, integral_const_mul, integral_gaussian]
  ring

/-- The Gaussian kernel `K(x, y) = exp(−a(x² + y²)/2 + bxy)`. -/
def kern (a b x y : ℝ) : ℝ := Real.exp (-a * (x ^ 2 + y ^ 2) / 2 + b * x * y)

/-- **Ground state.** With `c² = a² − b²`: `∫ K(x, y) e^{−cy²/2} dy = √(2π/(a+c)) e^{−cx²/2}`. -/
theorem kern_ground {a b c : ℝ} (hac : 0 < a + c) (hcb : c ^ 2 = a ^ 2 - b ^ 2) (x : ℝ) :
    ∫ y : ℝ, kern a b x y * Real.exp (-c * y ^ 2 / 2) =
      √(2 * π / (a + c)) * Real.exp (-c * x ^ 2 / 2) := by
  have hα : 0 < (a + c) / 2 := by linarith
  have h : ∀ y, kern a b x y * Real.exp (-c * y ^ 2 / 2) =
      Real.exp (-a * x ^ 2 / 2) * Real.exp (-((a + c) / 2) * y ^ 2 + (b * x) * y) := by
    intro y; rw [kern, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  simp_rw [h]
  rw [integral_const_mul, integral_exp_quad hα, mul_left_comm, ← Real.exp_add]
  have hs : π / ((a + c) / 2) = 2 * π / (a + c) := by field_simp
  have he : -a * x ^ 2 / 2 + (b * x) ^ 2 / (4 * ((a + c) / 2)) = -c * x ^ 2 / 2 := by
    field_simp
    linear_combination (4 * x ^ 2) * hcb
  rw [hs, he]

/-- **First excited state.** `∫ K(x, y) y e^{−cy²/2} dy = (b/(a+c)) √(2π/(a+c)) x e^{−cx²/2}`. -/
theorem kern_first {a b c : ℝ} (hac : 0 < a + c) (hcb : c ^ 2 = a ^ 2 - b ^ 2) (x : ℝ) :
    ∫ y : ℝ, kern a b x y * (y * Real.exp (-c * y ^ 2 / 2)) =
      b / (a + c) * √(2 * π / (a + c)) * (x * Real.exp (-c * x ^ 2 / 2)) := by
  have hα : 0 < (a + c) / 2 := by linarith
  have h : ∀ y, kern a b x y * (y * Real.exp (-c * y ^ 2 / 2)) =
      Real.exp (-a * x ^ 2 / 2) * (y * Real.exp (-((a + c) / 2) * y ^ 2 + (b * x) * y)) := by
    intro y
    have e : Real.exp (-a * x ^ 2 / 2) * Real.exp (-((a + c) / 2) * y ^ 2 + (b * x) * y) =
        kern a b x y * Real.exp (-c * y ^ 2 / 2) := by
      rw [kern, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc kern a b x y * (y * Real.exp (-c * y ^ 2 / 2))
        = y * (kern a b x y * Real.exp (-c * y ^ 2 / 2)) := by ring
      _ = y * (Real.exp (-a * x ^ 2 / 2) * Real.exp (-((a + c) / 2) * y ^ 2 + (b * x) * y)) := by
        rw [e]
      _ = _ := by ring
  simp_rw [h]
  rw [integral_const_mul, integral_mul_exp_quad hα]
  have hs : π / ((a + c) / 2) = 2 * π / (a + c) := by field_simp
  have he : Real.exp (-a * x ^ 2 / 2) * Real.exp ((b * x) ^ 2 / (4 * ((a + c) / 2))) =
      Real.exp (-c * x ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1
    field_simp
    linear_combination (4 * x ^ 2) * hcb
  rw [hs, ← he]
  field_simp

/-- At Part II=III's `(a, b) = (15/4, 7/4)`: `c = √11` and the eigenvalue ratio `b/(a+c)` is
`7/(15 + 4√11)`, between `0.24764` and `0.24765`. -/
theorem kern_ratio_value :
    Real.sqrt 11 ^ 2 = (15 / 4 : ℝ) ^ 2 - (7 / 4) ^ 2 ∧
      (7 / 4 : ℝ) / (15 / 4 + Real.sqrt 11) = 7 / (15 + 4 * Real.sqrt 11) ∧
      0.24764 < (7 : ℝ) / (15 + 4 * Real.sqrt 11) ∧ (7 : ℝ) / (15 + 4 * Real.sqrt 11) < 0.24765 := by
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have hlo : (3.3166 : ℝ) < Real.sqrt 11 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 11 < 3.3167 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < 15 + 4 * Real.sqrt 11 := by positivity
  refine ⟨by rw [h11]; norm_num, ?_, ?_, ?_⟩
  · field_simp
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

end

end ThermalZeta

#print axioms ThermalZeta.mellin_bose
#print axioms ThermalZeta.hasSum_mellin_boseLog
#print axioms ThermalZeta.mellin_boseLog
#print axioms ThermalZeta.tsum_alt_eq
#print axioms ThermalZeta.mellin_fermi
#print axioms ThermalZeta.mellin_fermiLog
#print axioms ThermalZeta.mellin_boltz
#print axioms ThermalZeta.integral_radial
#print axioms ThermalZeta.integral_scale
#print axioms ThermalZeta.gammaR_succ
#print axioms ThermalZeta.pressureBose_eq
#print axioms ThermalZeta.pressureFermi_eq
#print axioms ThermalZeta.pressureBoltz_eq
#print axioms ThermalZeta.densityBose_eq
#print axioms ThermalZeta.densityFermi_eq
#print axioms ThermalZeta.energyBose_eq
#print axioms ThermalZeta.densityBose_eulerProduct
#print axioms ThermalZeta.pressureBose_eulerProduct
#print axioms ThermalZeta.gammaR_eq_two_div_sphereArea
#print axioms ThermalZeta.completedRiemannZeta_four
#print axioms ThermalZeta.pressureBose_three
#print axioms ThermalZeta.energyBose_three
#print axioms ThermalZeta.pressureFermi_three
#print axioms ThermalZeta.densityBose_three
#print axioms ThermalZeta.densityFermi_three
#print axioms ThermalZeta.meanEnergy_three
#print axioms ThermalZeta.cycleSign_eq_sign
#print axioms ThermalZeta.cycleSign_succ
#print axioms ThermalZeta.cycleSign_mul
#print axioms ThermalZeta.cycleSign_odd_prime_pow
#print axioms ThermalZeta.cycleSign_two_pow
#print axioms ThermalZeta.cycleSign_four
#print axioms ThermalZeta.kern_ground
#print axioms ThermalZeta.kern_first
#print axioms ThermalZeta.kern_ratio_value
