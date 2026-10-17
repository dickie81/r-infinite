import KubotaDerivative
import KubotaBesselMellin

/-! # The Mellin transform `𝒥(s)` and its functional equation (round 374)

S5f-4c, the last part of round 360's S5f-4. The companion paper defines `𝒥(s)` as the Mellin transform of
`∂_{z̄}Θ_Ψ` at `z = 0`, integrates "`the differentiated Fourier series term by term`", and concludes: "`Thus
the integral defining $\mathcal J(s)$ converges for every $s$ and defines an entire function.`" Its functional
equation comes from "`Substituting $v\mapsto(\NK(c_{\boldsymbol h})v)^{-1}$ in each translated term`". This
file proves these for the derivative series of round 373.

* **The derivative series** (`dSer`): `G(u) = Σ_m d(m)·u·K_{1/3}(4π|m|u/9)·φ(m)`.
* **Bounds** (`dSer_le_exp`, `dSer_le_small`, with `bkR_third_le`, `small_aux` and `inv_cube_le`): under the
  support and size condition and `|φ(m)| ≤ C|m|`, `|G(u)| ≤ Ae^{−πu/18}` for `u ≥ 1` and `|G(u)| ≤ Bu^{−5}`
  for `0 < u ≤ 1`.
* **Continuity and convergence** (`continuousOn_dSer`, `mellinConvergent_dSer`): `G` is continuous on
  `(0, ∞)`, and its Mellin transform converges for `Re w > 5`.
* **Term by term** (**`mellin_dSer`**, with `integral_norm_besselK_third`, `integral_norm_ofReal_of_nonneg`
  and `besselK_third_ofReal`): for `Re w ≥ 5/3`, `∫_0^∞ G(v)v^{2w−1} dv =
  Σ_m d(m)φ(m)·2^{2w−1}Γ(w + 1/3)Γ(w + 2/3)(4π|m|/9)^{−(2w+1)}`, by round 372's (A.15).
* **The functional equation** (**`mellin_FE`**, with `mellin_cuspTerm`, `mellin_nested_sum` and
  `isBigO_inv_sq_exp_inv`): if, for every `v > 0`, the series at `∞` equals a finite combination of the cusp
  terms `−(σ(c)v)^{−2}G_c(1/(N(c)v))`, all under the support and size condition, then its Mellin transform
  converges at every `s` and is entire. For `Re s < −3/2` the transform at `2s` equals the same combination
  of `−σ(c)^{−2}N(c)^{2−2s}∫_0^∞ G_c(u)u^{1−2s} du`.
* **For the twisted `θ̄`** (**`twisted_theta_mellin`**, with `thetaSupp_twisted`, `thetaSupp_cuspCoef`,
  `norm_phiInf_le` and `norm_phiCusp_le`): `𝒥(s)` converges for every `s` and is entire. For `Re s ≥ 5/3` it
  is the Dirichlet series of the twisted coefficients. For `Re s < −3/2` it is the sum over the groups of
  `−σ(c)^{−2}N(c)^{2−2s}` times their Dirichlet series at `1 − s`.
-/

open Real Set Filter MeasureTheory Complex NumberField Ideal Asymptotics
open scoped Topology ComplexConjugate

noncomputable section

namespace Eis

/-- **The derivative series** `G(u) = Σ_m d(m)·u·K_{1/3}(4π|m|u/9)·φ(m)`. -/
def dSer (d φ : 𝓞 K → ℂ) (u : ℝ) : ℂ :=
  ∑' m : 𝓞 K, d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m

/-- `2K_{1/3}(x) ≤ Γ(1/3)(1 + 4/x)e^{−x/2}` for `x > 0`: `e^{−x(t+1/t)/2} ≤ e^{−x/2}e^{−xt/4}`, and
`∫_0^∞ t^{−2/3}e^{−xt/4} dt = Γ(1/3)(4/x)^{1/3} ≤ Γ(1/3)(1 + 4/x)`. -/
theorem bkR_third_le {x : ℝ} (hx : 0 < x) :
    bkR (1 / 3) x ≤ Real.Gamma (1 / 3) * (1 + 4 / x) * Real.exp (-(x / 2)) := by
  have hx4 : 0 < x / 4 := by positivity
  have key : ∀ t ∈ Ioi (0 : ℝ), t ^ ((1 / 3 : ℝ) - 1) * bkK x t ≤
      Real.exp (-(x / 2)) * (t ^ ((1 / 3 : ℝ) - 1) * Real.exp (-(x / 4 * t))) := by
    intro t ht
    have ht' : 0 < t := ht
    have hp : 0 ≤ t ^ ((1 / 3 : ℝ) - 1) := Real.rpow_nonneg ht'.le _
    have hb : bkK x t ≤ Real.exp (-(x / 2)) * Real.exp (-(x / 4 * t)) := by
      unfold bkK
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h3 : 0 ≤ t / 4 + t⁻¹ / 2 - 1 / 2 := by
        have e : t / 4 + t⁻¹ / 2 - 1 / 2 = ((t - 1) ^ 2 + 1) / (4 * t) := by field_simp; ring
        rw [e]; positivity
      nlinarith [mul_nonneg hx.le h3]
    calc t ^ ((1 / 3 : ℝ) - 1) * bkK x t
        ≤ t ^ ((1 / 3 : ℝ) - 1) * (Real.exp (-(x / 2)) * Real.exp (-(x / 4 * t))) :=
          mul_le_mul_of_nonneg_left hb hp
      _ = Real.exp (-(x / 2)) * (t ^ ((1 / 3 : ℝ) - 1) * Real.exp (-(x / 4 * t))) := by ring
  have hint : IntegrableOn (fun t : ℝ => t ^ ((1 / 3 : ℝ) - 1) * Real.exp (-(x / 4 * t))) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 / 3 : ℝ) - 1)
      (p := 1) (b := x / 4) (by norm_num) one_pos hx4) (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have hg : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hy : (1 / (x / 4)) ^ (1 / 3 : ℝ) ≤ 1 + 4 / x := by
    rw [show 1 / (x / 4) = 4 / x by field_simp]
    have h0 : 0 ≤ 4 / x := by positivity
    rcases le_or_gt (4 / x) 1 with h | h
    · calc (4 / x) ^ (1 / 3 : ℝ) ≤ 1 := Real.rpow_le_one h0 h (by norm_num)
        _ ≤ 1 + 4 / x := by linarith
    · calc (4 / x) ^ (1 / 3 : ℝ) ≤ (4 / x) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
        _ = 4 / x := Real.rpow_one _
        _ ≤ 1 + 4 / x := by linarith
  unfold bkR
  calc ∫ t in Ioi (0 : ℝ), t ^ ((1 / 3 : ℝ) - 1) * bkK x t
      ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(x / 2)) * (t ^ ((1 / 3 : ℝ) - 1) * Real.exp (-(x / 4 * t))) :=
        setIntegral_mono_on (integrableOn_bkR hx _) (Integrable.const_mul hint _) measurableSet_Ioi key
    _ = Real.exp (-(x / 2)) * ((1 / (x / 4)) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)) := by
        rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hx4]
    _ ≤ Real.exp (-(x / 2)) * ((1 + 4 / x) * Real.Gamma (1 / 3)) := by gcongr
    _ = Real.Gamma (1 / 3) * (1 + 4 / x) * Real.exp (-(x / 2)) := by ring

/-- The arithmetic of the bound for small `u`, with `X = knu`. -/
theorem small_aux {k n u : ℝ} (hk : 0 < k) (hn : 1 ≤ n) (hu : 0 < u) (hu1 : u ≤ 1) :
    n ^ 2 * u * ((1 + 4 / (k * n * u)) * (120 / (k * n * u / 2) ^ 5)) ≤
      3840 * (k + 4) / k ^ 6 * ((n ^ 3)⁻¹ * (u ^ 5)⁻¹) := by
  have hn0 : 0 < n := by linarith
  have hX : 0 < k * n * u := by positivity
  have e1 : n ^ 2 * u * ((1 + 4 / (k * n * u)) * (120 / (k * n * u / 2) ^ 5)) =
      3840 * (k * n * u + 4) / (k ^ 6 * n ^ 4 * u ^ 5) := by
    field_simp; ring
  have e2 : 3840 * (k + 4) / k ^ 6 * ((n ^ 3)⁻¹ * (u ^ 5)⁻¹) =
      3840 * ((k + 4) * n) / (k ^ 6 * n ^ 4 * u ^ 5) := by
    field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : k * n * u ≤ k * n := by
    have := mul_pos hk hn0
    nlinarith
  nlinarith

theorem inv_cube_le {n : ℝ} (hn : 1 ≤ n) : (n ^ 3)⁻¹ ≤ 8 * (1 + n) ^ (-3 : ℝ) := by
  have hn0 : 0 < n := by linarith
  rw [Real.rpow_neg (by positivity), show (1 + n) ^ (3 : ℝ) = (1 + n) ^ 3 by norm_cast]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  have h2 : (1 + n) ^ 3 ≤ (2 * n) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  nlinarith

/-- **Exponential decay at `∞`**: `|G(u)| ≤ A·e^{−πu/18}` for `u ≥ 1`. -/
theorem dSer_le_exp {Kc C : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d)
    (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) :
    ∃ A, 0 ≤ A ∧ ∀ u, 1 ≤ u → ‖dSer d φ u‖ ≤ A * Real.exp (-(Real.pi / 18) * u) := by
  set c := Real.pi / 9 with hc_def
  have hc : 0 < c := by positivity
  have hR : 0 ≤ bkR (1 / 3) (2 * Real.pi / 9) := bkR_nonneg _ _
  set g : 𝓞 K → ℝ := fun m => ‖σO m‖ ^ (4 / 3 : ℝ) * Real.exp (-(c * ‖σO m‖)) with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by positivity
  have hgs : Summable g := summable_O_of_le hg0 fun m => rpow_four_thirds_exp_le hc (norm_nonneg _)
  have hKc := h.1
  have hA0 : 0 ≤ Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| := by positivity
  refine ⟨Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| * (∑' m, g m) * (18 / Real.pi),
    mul_nonneg (mul_nonneg hA0 (tsum_nonneg hg0)) (by positivity), fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hterm : ∀ m : 𝓞 K, ‖d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m‖ ≤
      Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| * (u * Real.exp (-(Real.pi * u / 9))) * g m := by
    intro m
    by_cases hm : d m = 0
    · rw [hm, zero_mul, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hA0 (by positivity)) (hg0 m)
    obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
    have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
    have h1 := one_le_norm_σO hm0
    have hK := norm_besselK_le (1 / 3 : ℂ) (4 * Real.pi * ‖σO m‖ * u / 9)
    have hre : (1 / 3 : ℂ).re = 1 / 3 := by norm_num
    rw [hre] at hK
    have hx₀ : 0 < 4 * Real.pi / 9 := by positivity
    have hxx : 4 * Real.pi / 9 ≤ 4 * Real.pi * ‖σO m‖ * u / 9 := by
      have := Real.pi_pos
      rw [div_le_div_iff_of_pos_right (by norm_num)]
      have : 1 ≤ ‖σO m‖ * u := by nlinarith
      nlinarith
    have hdecay := bkR_le_exp (r := 1 / 3) hx₀ hxx
    rw [show 4 * Real.pi / 9 / 2 = 2 * Real.pi / 9 by ring] at hdecay
    have hexp : Real.exp (-(4 * Real.pi * ‖σO m‖ * u / 9 / 2)) ≤
        Real.exp (-(Real.pi * u / 9)) * Real.exp (-(c * ‖σO m‖)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [hc_def]
      have := Real.pi_pos
      have : ‖σO m‖ + u ≤ 2 * (‖σO m‖ * u) := by nlinarith
      nlinarith
    have hd := norm_le_of_thetaSupp h m
    have hφm : ‖φ m‖ ≤ |C| * ‖σO m‖ :=
      (hφ m).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
    have e43 : ‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ = ‖σO m‖ ^ (4 / 3 : ℝ) := by
      rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.rpow_add_one (by linarith)]
    have hKb : ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9)‖ ≤
        (1 / 2) * ((Real.exp (-(Real.pi * u / 9)) * Real.exp (-(c * ‖σO m‖))) *
          bkR (1 / 3) (2 * Real.pi / 9)) :=
      hK.trans (mul_le_mul_of_nonneg_left (hdecay.trans (mul_le_mul_of_nonneg_right hexp hR))
        (by norm_num))
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc ‖d m‖ * u * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9)‖ * ‖φ m‖
        ≤ (Kc * ‖σO m‖ ^ (1 / 3 : ℝ)) * u * ((1 / 2) * ((Real.exp (-(Real.pi * u / 9)) *
            Real.exp (-(c * ‖σO m‖))) * bkR (1 / 3) (2 * Real.pi / 9))) * (|C| * ‖σO m‖) := by
          gcongr
      _ = Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| * (u * Real.exp (-(Real.pi * u / 9))) *
            (‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ * Real.exp (-(c * ‖σO m‖))) := by ring
      _ = Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| * (u * Real.exp (-(Real.pi * u / 9))) *
            g m := by rw [e43]
  have hs : Summable fun m : 𝓞 K =>
      ‖d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm (hgs.mul_left _)
  have hlin : u * Real.exp (-(Real.pi * u / 9)) ≤ 18 / Real.pi * Real.exp (-(Real.pi / 18) * u) := by
    have h1 := Real.add_one_le_exp (Real.pi / 18 * u)
    have h2 : u ≤ 18 / Real.pi * Real.exp (Real.pi / 18 * u) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_pos]
    calc u * Real.exp (-(Real.pi * u / 9))
        ≤ 18 / Real.pi * Real.exp (Real.pi / 18 * u) * Real.exp (-(Real.pi * u / 9)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 18 / Real.pi * Real.exp (-(Real.pi / 18) * u) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc ‖dSer d φ u‖
      ≤ ∑' m, ‖d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' m, Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| *
          (u * Real.exp (-(Real.pi * u / 9))) * g m :=
        hs.tsum_le_tsum hterm (hgs.mul_left _)
    _ = Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| * (∑' m, g m) *
          (u * Real.exp (-(Real.pi * u / 9))) := by rw [tsum_mul_left]; ring
    _ ≤ Kc * (1 / 2) * bkR (1 / 3) (2 * Real.pi / 9) * |C| * (∑' m, g m) *
          (18 / Real.pi * Real.exp (-(Real.pi / 18) * u)) :=
        mul_le_mul_of_nonneg_left hlin (mul_nonneg hA0 (tsum_nonneg hg0))
    _ = _ := by ring

/-- **The bound for small `u`**: `|G(u)| ≤ B·u^{−5}` for `0 < u ≤ 1`. -/
theorem dSer_le_small {Kc C : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d)
    (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) :
    ∃ B, 0 ≤ B ∧ ∀ u, 0 < u → u ≤ 1 → ‖dSer d φ u‖ ≤ B * (u ^ 5)⁻¹ := by
  set k : ℝ := 4 * Real.pi / 9 with hk_def
  have hk : 0 < k := by positivity
  have hKc := h.1
  have hgam : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hA0 : 0 ≤ Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) * (3840 * (k + 4) / k ^ 6) * 8 := by
    positivity
  set g : 𝓞 K → ℝ := fun m => (1 + ‖σO m‖) ^ (-3 : ℝ) with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by positivity
  have hgs : Summable g := summable_O_of_le hg0 (A := 1) fun m => by simp [g]
  refine ⟨Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) * (3840 * (k + 4) / k ^ 6) * 8 * ∑' m, g m,
    mul_nonneg hA0 (tsum_nonneg hg0), fun u hu hu1 => ?_⟩
  have hterm : ∀ m : 𝓞 K, ‖d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m‖ ≤
      Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) * (3840 * (k + 4) / k ^ 6) * 8 * (u ^ 5)⁻¹ * g m := by
    intro m
    by_cases hm : d m = 0
    · rw [hm, zero_mul, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hA0 (by positivity)) (hg0 m)
    obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
    have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
    have h1 := one_le_norm_σO hm0
    have hn0 : 0 < ‖σO m‖ := by linarith
    have hX : 0 < k * ‖σO m‖ * u := by positivity
    have hXe : 4 * Real.pi * ‖σO m‖ * u / 9 = k * ‖σO m‖ * u := by rw [hk_def]; ring
    have hK := norm_besselK_le (1 / 3 : ℂ) (4 * Real.pi * ‖σO m‖ * u / 9)
    have hre : (1 / 3 : ℂ).re = 1 / 3 := by norm_num
    rw [hre, hXe] at hK
    have hL1 := bkR_third_le hX
    have h5 : Real.exp (-(k * ‖σO m‖ * u / 2)) ≤ 120 / (k * ‖σO m‖ * u / 2) ^ 5 := by
      have hy := Real.pow_div_factorial_le_exp (k * ‖σO m‖ * u / 2) (by positivity) 5
      have hy' : (k * ‖σO m‖ * u / 2) ^ 5 / 120 ≤ Real.exp (k * ‖σO m‖ * u / 2) := by
        simpa [Nat.factorial] using hy
      calc Real.exp (-(k * ‖σO m‖ * u / 2)) = (Real.exp (k * ‖σO m‖ * u / 2))⁻¹ := Real.exp_neg _
        _ ≤ ((k * ‖σO m‖ * u / 2) ^ 5 / 120)⁻¹ := inv_anti₀ (by positivity) hy'
        _ = 120 / (k * ‖σO m‖ * u / 2) ^ 5 := by rw [inv_div]
    have hd := norm_le_of_thetaSupp h m
    have h13 : ‖σO m‖ ^ (1 / 3 : ℝ) ≤ ‖σO m‖ := by
      calc ‖σO m‖ ^ (1 / 3 : ℝ) ≤ ‖σO m‖ ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = ‖σO m‖ := Real.rpow_one _
    have hφm : ‖φ m‖ ≤ |C| * ‖σO m‖ :=
      (hφ m).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
    have hKb : ‖besselK (1 / 3) (k * ‖σO m‖ * u)‖ ≤
        (1 / 2) * (Real.Gamma (1 / 3) * ((1 + 4 / (k * ‖σO m‖ * u)) * (120 / (k * ‖σO m‖ * u / 2) ^ 5))) := by
      refine hK.trans (mul_le_mul_of_nonneg_left (hL1.trans ?_) (by norm_num))
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (by positivity)) hgam.le
    have hsa := small_aux hk h1 hu hu1
    have hic := inv_cube_le h1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le, hXe]
    calc ‖d m‖ * u * ‖besselK (1 / 3) (k * ‖σO m‖ * u)‖ * ‖φ m‖
        ≤ (Kc * ‖σO m‖) * u * ((1 / 2) * (Real.Gamma (1 / 3) * ((1 + 4 / (k * ‖σO m‖ * u)) *
            (120 / (k * ‖σO m‖ * u / 2) ^ 5)))) * (|C| * ‖σO m‖) := by
          gcongr
          exact hd.trans (mul_le_mul_of_nonneg_left h13 hKc)
      _ = Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) *
            (‖σO m‖ ^ 2 * u * ((1 + 4 / (k * ‖σO m‖ * u)) * (120 / (k * ‖σO m‖ * u / 2) ^ 5))) := by
          ring
      _ ≤ Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) *
            (3840 * (k + 4) / k ^ 6 * ((‖σO m‖ ^ 3)⁻¹ * (u ^ 5)⁻¹)) := by gcongr
      _ ≤ Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) *
            (3840 * (k + 4) / k ^ 6 * ((8 * g m) * (u ^ 5)⁻¹)) := by gcongr
      _ = Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) * (3840 * (k + 4) / k ^ 6) * 8 * (u ^ 5)⁻¹ * g m := by
          ring
  have hs : Summable fun m : 𝓞 K =>
      ‖d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm (hgs.mul_left _)
  calc ‖dSer d φ u‖
      ≤ ∑' m, ‖d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' m, Kc * |C| * (1 / 2) * Real.Gamma (1 / 3) * (3840 * (k + 4) / k ^ 6) * 8 *
          (u ^ 5)⁻¹ * g m :=
        hs.tsum_le_tsum hterm (hgs.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- **The derivative series is continuous** on `(0, ∞)`: near each `u₀ > 0` the series has the
summable majorant of `exists_thTerm_bound`. -/
theorem continuousOn_dSer {Kc C : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d)
    (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) : ContinuousOn (dSer d φ) (Ioi 0) := by
  intro u₀ hu₀
  have hu₀' : (0 : ℝ) < u₀ := hu₀
  obtain ⟨A, hA0, hA⟩ := exists_thTerm_bound h (half_pos hu₀') (2 * u₀)
  have hcont : ContinuousOn (fun u : ℝ => ∑' m : 𝓞 K,
      d m * (u : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9) * φ m) (Ioo (u₀ / 2) (2 * u₀)) := by
    refine continuousOn_tsum (u := fun m => |C| * A * (1 + ‖σO m‖) ^ (-3 : ℝ)) (fun m => ?_)
      (summable_O_of_le (fun m => by positivity) (fun m => le_refl _)) (fun m u hu => ?_)
    · by_cases hm : d m = 0
      · simp only [hm, zero_mul]
        exact continuousOn_const
      obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
      have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
      have h1 := one_le_norm_σO hm0
      have hn0 : 0 < ‖σO m‖ := by linarith
      intro u hu
      have hupos : 0 < u := lt_trans (half_pos hu₀') hu.1
      refine ContinuousAt.continuousWithinAt ?_
      have hK : ContinuousAt (fun u : ℝ => besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9)) u :=
        (continuousAt_besselK _ (by positivity)).comp
          (by fun_prop : Continuous fun u : ℝ => 4 * Real.pi * ‖σO m‖ * u / 9).continuousAt
      exact ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).mul hK).mul
        continuousAt_const
    · have hupos : 0 < u := lt_trans (half_pos hu₀') hu.1
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hupos.le]
      have hb := hA u hu.1.le hu.2.le m
      have h2 : ‖φ m‖ ≤ |C| * ‖σO m‖ :=
        (hφ m).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
      calc ‖d m‖ * u * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9)‖ * ‖φ m‖
          ≤ ‖d m‖ * u * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9)‖ * (|C| * ‖σO m‖) := by
            gcongr
        _ = |C| * (‖d m‖ * u * ‖besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * u / 9)‖ * ‖σO m‖) := by ring
        _ ≤ |C| * (A * (1 + ‖σO m‖) ^ (-3 : ℝ)) := by gcongr
        _ = |C| * A * (1 + ‖σO m‖) ^ (-3 : ℝ) := by ring
  exact (hcont.continuousAt (Ioo_mem_nhds (half_lt_self hu₀') (by linarith))).continuousWithinAt

/-- **The Mellin transform of the derivative series converges** for `Re w > 5`. -/
theorem mellinConvergent_dSer {Kc C : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d)
    (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) {w : ℂ} (hw : 5 < w.re) : MellinConvergent (dSer d φ) w := by
  obtain ⟨A, -, hA⟩ := dSer_le_exp h hφ
  obtain ⟨B, -, hB⟩ := dSer_le_small h hφ
  refine mellinConvergent_of_isBigO_rpow_exp (a := Real.pi / 18) (b := 5) (by positivity)
    ((continuousOn_dSer h hφ).locallyIntegrableOn measurableSet_Ioi) ?_ ?_ hw
  · refine IsBigO.of_bound A ?_
    filter_upwards [eventually_ge_atTop 1] with u hu
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hA u hu
  · refine IsBigO.of_bound B ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
    have hu0 : 0 < u := hu.1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _), Real.rpow_neg hu0.le,
      show u ^ (5 : ℝ) = u ^ 5 by norm_cast]
    exact hB u hu0 hu.2.le

/-- For `g ≥ 0` on `(0, ∞)`, `∫|g| = |∫g|` for the complex cast. -/
theorem integral_norm_ofReal_of_nonneg {g : ℝ → ℝ} (hg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g x) :
    ∫ x in Ioi (0 : ℝ), ‖((g x : ℝ) : ℂ)‖ = ‖∫ x in Ioi (0 : ℝ), ((g x : ℝ) : ℂ)‖ := by
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi hg)]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg x hx)]

theorem besselK_third_ofReal (x : ℝ) : besselK (1 / 3) x = ((1 / 2 * bkR (1 / 3) x : ℝ) : ℂ) := by
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, besselK_ofReal]

/-- `∫_0^∞ v^{2σ}|K_{1/3}(av)| dv = |2^{2σ−1}Γ(σ + 1/3)Γ(σ + 2/3)|·a^{−(2σ+1)}` for `σ > −1/3`. -/
theorem integral_norm_besselK_third {σ : ℝ} (hσ : -1 / 3 < σ) {a : ℝ} (ha : 0 < a) :
    ∫ v in Ioi (0 : ℝ), ‖(v : ℂ) ^ (2 * (σ : ℂ)) * besselK (1 / 3) (a * v)‖ =
      ‖(2 : ℂ) ^ (2 * (σ : ℂ) - 1) * Gamma ((σ : ℂ) + 1 / 3) * Gamma ((σ : ℂ) + 2 / 3)‖ *
        a ^ (-(2 * σ + 1)) := by
  have e : ∀ v ∈ Ioi (0 : ℝ), (v : ℂ) ^ (2 * (σ : ℂ)) * besselK (1 / 3) (a * v) =
      ((v ^ (2 * σ) * (1 / 2 * bkR (1 / 3) (a * v)) : ℝ) : ℂ) := by
    intro v hv
    rw [besselK_third_ofReal, Complex.ofReal_mul (v ^ (2 * σ)), Complex.ofReal_cpow (le_of_lt hv)]
    push_cast
    ring
  have hg : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ v ^ (2 * σ) * (1 / 2 * bkR (1 / 3) (a * v)) := fun v hv =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt hv) _) (mul_nonneg (by norm_num) (bkR_nonneg _ _))
  have hs : -1 / 3 < (σ : ℂ).re := by rwa [Complex.ofReal_re]
  rw [setIntegral_congr_fun measurableSet_Ioi fun v hv => congrArg norm (e v hv),
    integral_norm_ofReal_of_nonneg hg, ← setIntegral_congr_fun measurableSet_Ioi e,
    integral_besselK_third hs ha, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
  congr 2
  simp

/-- **The Mellin transform of the derivative series as a Dirichlet series** (term by term, with the
companion paper's (A.15)): for `Re w ≥ 5/3`, `∫_0^∞ G(v)v^{2w−1} dv =
Σ_m d(m)φ(m)·2^{2w−1}Γ(w + 1/3)Γ(w + 2/3)(4π|m|/9)^{−(2w+1)}`. -/
theorem mellin_dSer {Kc C : ℝ} {d φ : 𝓞 K → ℂ} (h : ThetaSupp Kc d)
    (hφ : ∀ m, ‖φ m‖ ≤ C * ‖σO m‖) {w : ℂ} (hw : 5 / 3 ≤ w.re) :
    mellin (dSer d φ) (2 * w) = ∑' m : 𝓞 K, d m * φ m * (2 ^ (2 * w - 1) * Gamma (w + 1 / 3) *
      Gamma (w + 2 / 3) * (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * w + 1))) := by
  have hs : -1 / 3 < w.re := by linarith
  have hKc := h.1
  set F : 𝓞 K → ℝ → ℂ := fun m v => (v : ℂ) ^ (2 * w - 1) *
    (d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * φ m) with hF
  have hpow : ∀ v : ℝ, 0 < v → (v : ℂ) ^ (2 * w - 1) * v = (v : ℂ) ^ (2 * w) := by
    intro v hv
    have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv.ne'
    conv_rhs => rw [show 2 * w = (2 * w - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hv', Complex.cpow_one]
  have hFe : ∀ m : 𝓞 K, ∀ v : ℝ, 0 < v → F m v = d m * φ m *
      ((v : ℂ) ^ (2 * w) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ / 9 * v)) := by
    intro m v hv
    simp only [hF]
    rw [← hpow v hv, show 4 * Real.pi * ‖σO m‖ * v / 9 = 4 * Real.pi * ‖σO m‖ / 9 * v by ring]
    ring
  have hone : ∀ m : 𝓞 K, ∫ v in Ioi 0, F m v = d m * φ m * (2 ^ (2 * w - 1) * Gamma (w + 1 / 3) *
      Gamma (w + 2 / 3) * (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * w + 1))) := by
    intro m
    by_cases hm : d m = 0
    · simp [hF, hm]
    obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
    have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
    have h1 := one_le_norm_σO hm0
    have hn0 : 0 < ‖σO m‖ := by linarith
    have ha : 0 < 4 * Real.pi * ‖σO m‖ / 9 := by positivity
    rw [setIntegral_congr_fun measurableSet_Ioi fun v hv => hFe m v hv, integral_const_mul,
      integral_besselK_third hs ha]
  have hintm : ∀ m : 𝓞 K, Integrable (F m) (volume.restrict (Ioi 0)) := by
    intro m
    by_cases hz : d m * φ m = 0
    · have h0 : ∀ v ∈ Ioi (0 : ℝ), F m v = 0 := fun v hv => by rw [hFe m v hv, hz, zero_mul]
      exact (integrableOn_congr_fun h0 measurableSet_Ioi).2 (integrable_zero _ _ _)
    have hm : d m ≠ 0 := left_ne_zero_of_mul hz
    obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
    have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
    have h1 := one_le_norm_σO hm0
    have hn0 : 0 < ‖σO m‖ := by linarith
    have ha : 0 < 4 * Real.pi * ‖σO m‖ / 9 := by positivity
    refine Integrable.of_integral_ne_zero ?_
    rw [hone m]
    refine mul_ne_zero hz (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_)
    · rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
    · exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    · exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    · rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.2 ha.ne')
  set Γσ : ℝ := ‖(2 : ℂ) ^ (2 * (w.re : ℂ) - 1) * Gamma ((w.re : ℂ) + 1 / 3) *
    Gamma ((w.re : ℂ) + 2 / 3)‖ with hΓσ
  have hΓ0 : 0 ≤ Γσ := norm_nonneg _
  have hnorm : ∀ m : 𝓞 K, ∫ v in Ioi 0, ‖F m v‖ =
      ‖d m‖ * ‖φ m‖ * (Γσ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * w.re + 1))) := by
    intro m
    by_cases hm : d m = 0
    · simp [hF, hm]
    obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
    have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
    have h1 := one_le_norm_σO hm0
    have hn0 : 0 < ‖σO m‖ := by linarith
    have ha : 0 < 4 * Real.pi * ‖σO m‖ / 9 := by positivity
    have e : ∀ v ∈ Ioi (0 : ℝ), ‖F m v‖ = ‖d m‖ * ‖φ m‖ *
        ‖(v : ℂ) ^ (2 * (w.re : ℂ)) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ / 9 * v)‖ := by
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      rw [hFe m v hv']
      simp only [norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hv', Complex.norm_cpow_eq_rpow_re_of_pos hv']
      have hre : (2 * w).re = (2 * (w.re : ℂ)).re := by simp
      rw [hre]
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      integral_norm_besselK_third (by linarith) ha]
  have hsum : Summable fun m : 𝓞 K => ∫ v in Ioi 0, ‖F m v‖ := by
    rw [show (fun m : 𝓞 K => ∫ v in Ioi 0, ‖F m v‖) = fun m =>
        ‖d m‖ * ‖φ m‖ * (Γσ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * w.re + 1))) from funext hnorm]
    refine summable_O_of_le (fun m => by positivity)
      (A := Kc * |C| * Γσ * (4 * Real.pi / 9) ^ (-(2 * w.re + 1)) * 8) fun m => ?_
    by_cases hm : d m = 0
    · rw [hm, norm_zero, zero_mul, zero_mul]; positivity
    obtain ⟨q, hq, -, hn, hb, -⟩ := h.2 m hm
    have hm0 : m ≠ 0 := hq ▸ dualPt_ne_zero hn hb
    have h1 := one_le_norm_σO hm0
    have hn0 : 0 < ‖σO m‖ := by linarith
    have hd := norm_le_of_thetaSupp h m
    have hφm : ‖φ m‖ ≤ |C| * ‖σO m‖ :=
      (hφ m).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
    have hsplit : (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * w.re + 1)) =
        (4 * Real.pi / 9) ^ (-(2 * w.re + 1)) * ‖σO m‖ ^ (-(2 * w.re + 1)) := by
      rw [show 4 * Real.pi * ‖σO m‖ / 9 = 4 * Real.pi / 9 * ‖σO m‖ by ring,
        Real.mul_rpow (by positivity) hn0.le]
    have hexp : ‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ * ‖σO m‖ ^ (-(2 * w.re + 1)) ≤ (‖σO m‖ ^ 3)⁻¹ := by
      rw [show ‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ = ‖σO m‖ ^ (1 / 3 + 1 : ℝ) by
          rw [Real.rpow_add hn0, Real.rpow_one],
        ← Real.rpow_add hn0]
      calc ‖σO m‖ ^ (1 / 3 + 1 + -(2 * w.re + 1)) ≤ ‖σO m‖ ^ (-3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        _ = (‖σO m‖ ^ 3)⁻¹ := by rw [Real.rpow_neg hn0.le]; norm_cast
    have hic := inv_cube_le h1
    have hc0 : 0 ≤ (4 * Real.pi / 9) ^ (-(2 * w.re + 1)) := by positivity
    calc ‖d m‖ * ‖φ m‖ * (Γσ * (4 * Real.pi * ‖σO m‖ / 9) ^ (-(2 * w.re + 1)))
        ≤ (Kc * ‖σO m‖ ^ (1 / 3 : ℝ)) * (|C| * ‖σO m‖) *
            (Γσ * ((4 * Real.pi / 9) ^ (-(2 * w.re + 1)) * ‖σO m‖ ^ (-(2 * w.re + 1)))) := by
          rw [hsplit]; gcongr
      _ = Kc * |C| * Γσ * (4 * Real.pi / 9) ^ (-(2 * w.re + 1)) *
            (‖σO m‖ ^ (1 / 3 : ℝ) * ‖σO m‖ * ‖σO m‖ ^ (-(2 * w.re + 1))) := by ring
      _ ≤ Kc * |C| * Γσ * (4 * Real.pi / 9) ^ (-(2 * w.re + 1)) * (8 * (1 + ‖σO m‖) ^ (-3 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (hexp.trans hic) (by positivity)
      _ = Kc * |C| * Γσ * (4 * Real.pi / 9) ^ (-(2 * w.re + 1)) * 8 * (1 + ‖σO m‖) ^ (-3 : ℝ) := by
          ring
  have hmel : mellin (dSer d φ) (2 * w) = ∫ v in Ioi 0, ∑' m, F m v := by
    unfold mellin dSer
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [smul_eq_mul, ← tsum_mul_left]
  rw [hmel, ← (hasSum_integral_of_summable_integral_norm hintm hsum).tsum_eq]
  exact tsum_congr hone

/-- `t^{−2}e^{−c/t} = O(t^{−b})` as `t → 0⁺`, for every `b`. -/
theorem isBigO_inv_sq_exp_inv {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (fun t : ℝ => (t ^ 2)⁻¹ * Real.exp (-(c / t))) =O[𝓝[>] 0] (· ^ (-b)) := by
  have h1 := ((isLittleO_exp_neg_mul_rpow_atTop hc (b - 2)).comp_tendsto
    tendsto_inv_nhdsGT_zero).isBigO
  have h3 : (fun t : ℝ => (t ^ 2)⁻¹ * Real.exp (-c * t⁻¹)) =O[𝓝[>] 0]
      fun t => (t ^ 2)⁻¹ * (t⁻¹) ^ (b - 2) := (isBigO_refl _ _).mul h1
  refine h3.congr' ?_ ?_
  · filter_upwards with t
    congr 2
    ring
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Real.inv_rpow ht'.le, ← mul_inv, show t ^ 2 = t ^ (2 : ℝ) by norm_cast,
      ← Real.rpow_add ht', show (2 : ℝ) + (b - 2) = b by ring, Real.rpow_neg ht'.le]

/-- Linearity of the Mellin transform over a double finite sum. -/
theorem mellin_nested_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (α : ι → ℂ) (β : κ → ℂ)
    (γ : ι → κ → ℂ) (g : ι → κ → ℝ → ℂ) (w : ℂ)
    (hg : ∀ i ∈ s, ∀ k ∈ t, MellinConvergent (g i k) w) :
    mellin (fun v => ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * g i k v)) w =
      ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * mellin (g i k) w) := by
  unfold mellin
  have e : ∀ v : ℝ, (v : ℂ) ^ (w - 1) • ∑ i ∈ s, α i * ∑ k ∈ t, β k * (γ i k * g i k v) =
      ∑ i ∈ s, ∑ k ∈ t, (α i * β k * γ i k) * ((v : ℂ) ^ (w - 1) • g i k v) := by
    intro v
    simp only [smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun k hk =>
    Integrable.const_mul (hg i hi k hk) _]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun k hk => Integrable.const_mul (hg i hi k hk) _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

/-- **The Mellin transform of a cusp term**: `v ↦ v^{−2}G(1/(Nv))` has Mellin transform
`N^{2−2s}·𝓜G(2 − 2s)` at `2s`, where the latter converges. -/
theorem mellin_cuspTerm {G : ℝ → ℂ} {N : ℝ} (hN : 0 < N) (s : ℂ)
    (hG : MellinConvergent G (2 - 2 * s)) :
    MellinConvergent (fun v : ℝ => (v : ℂ) ^ (-2 : ℂ) • G (N * v)⁻¹) (2 * s) ∧
      mellin (fun v : ℝ => (v : ℂ) ^ (-2 : ℂ) • G (N * v)⁻¹) (2 * s) =
        (N : ℂ) ^ (2 - 2 * s) * mellin G (2 - 2 * s) := by
  have hinv : MellinConvergent (fun t : ℝ => G t⁻¹) (2 * s + -2) := by
    have h := (MellinConvergent.comp_rpow (f := G) (s := 2 * s + -2) (a := -1) (by norm_num)).2
    simp only [Real.rpow_neg_one] at h
    apply h
    convert hG using 1
    push_cast; ring
  refine ⟨MellinConvergent.cpow_smul.2 ((MellinConvergent.comp_mul_left hN).2 hinv), ?_⟩
  rw [mellin_cpow_smul, mellin_comp_mul_left (fun t : ℝ => G t⁻¹) _ hN, mellin_comp_inv,
    smul_eq_mul]
  congr 1
  · congr 1; ring
  · congr 1; ring

/-- **The functional equation of the Mellin transform**, from an expansion in cusp coordinates: if
for every `v > 0` the `∂_{z̄}`-series at `∞` equals the combination of the cusp series
`−(σ(c)v)^{−2}G_c(1/(N(c)v))` (all under the support and size condition), then its Mellin transform
converges at every `s` and is entire, and for `Re s < −3/2` it equals the combination of
`−σ(c)^{−2}N(c)^{2−2s}·𝓜G_c(2 − 2s)` at `2s`. -/
theorem mellin_FE {ι κ : Type*} (S : Finset ι) (T : Finset κ) {Ka Ca Cc : ℝ} {a φa φc : 𝓞 K → ℂ}
    (ha : ThetaSupp Ka a) (hφa : ∀ m, ‖φa m‖ ≤ Ca * ‖σO m‖) (hφc : ∀ m, ‖φc m‖ ≤ Cc * ‖σO m‖)
    (α : ι → ℂ) (β : κ → ℂ) (γ : ι → κ → ℂ) (dd : ι → κ → 𝓞 K → ℂ) (cc : ι → κ → 𝓞 K)
    (Kd : ι → κ → ℝ) (hdd : ∀ i ∈ S, ∀ k ∈ T, ThetaSupp (Kd i k) (dd i k) ∧ σO (cc i k) ≠ 0)
    (hid : ∀ v : ℝ, 0 < v → dSer a φa v = ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k *
      (-(σO (cc i k) ^ 2 * (v : ℂ) ^ 2)⁻¹ *
        dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹))) :
    (∀ s, MellinConvergent (dSer a φa) s) ∧ Differentiable ℂ (mellin (dSer a φa)) ∧
      ∀ s : ℂ, s.re < -3 / 2 → mellin (dSer a φa) (2 * s) =
        ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k * (-(σO (cc i k) ^ 2)⁻¹ *
          ((Complex.normSq (σO (cc i k)) : ℂ) ^ (2 - 2 * s) *
            mellin (dSer (dd i k) φc) (2 - 2 * s)))) := by
  -- the cusp terms as functions of `v`
  set g : ι → κ → ℝ → ℂ := fun i k v => -(σO (cc i k) ^ 2 * (v : ℂ) ^ 2)⁻¹ *
    dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹ with hg_def
  have hgform : ∀ i k v, g i k v = (-(σO (cc i k) ^ 2)⁻¹) •
      ((v : ℂ) ^ (-2 : ℂ) • dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹) := by
    intro i k v
    simp only [hg_def, smul_eq_mul]
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, mul_inv]
    ring
  -- each cusp term is `O(t^{−b})` at `0`
  have hgbot : ∀ i ∈ S, ∀ k ∈ T, ∀ b : ℝ, g i k =O[𝓝[>] 0] (· ^ (-b)) := by
    intro i hi k hk b
    obtain ⟨hd, hc⟩ := hdd i hi k hk
    have hN : 0 < Complex.normSq (σO (cc i k)) := Complex.normSq_pos.2 hc
    obtain ⟨A, hA0, hA⟩ := dSer_le_exp hd hφc
    have hcN : 0 < Real.pi / 18 / Complex.normSq (σO (cc i k)) := by positivity
    refine (IsBigO.of_bound (‖(σO (cc i k) ^ 2)⁻¹‖ * A) ?_).trans (isBigO_inv_sq_exp_inv hcN b)
    filter_upwards [Ioo_mem_nhdsGT (inv_pos.2 hN)] with v hv
    have hv0 : 0 < v := hv.1
    have hu : 1 ≤ (Complex.normSq (σO (cc i k)) * v)⁻¹ := by
      rw [one_le_inv₀ (by positivity)]
      have := hv.2
      rw [lt_inv_comm₀ hv0 hN] at this
      calc Complex.normSq (σO (cc i k)) * v ≤ v⁻¹ * v :=
            mul_le_mul_of_nonneg_right this.le hv0.le
        _ = 1 := inv_mul_cancel₀ hv0.ne'
    have hb := hA _ hu
    have hexp : Real.exp (-(Real.pi / 18) * (Complex.normSq (σO (cc i k)) * v)⁻¹) =
        Real.exp (-(Real.pi / 18 / Complex.normSq (σO (cc i k)) / v)) := by
      congr 1; field_simp
    rw [hexp] at hb
    rw [hgform, norm_smul, norm_smul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hv0,
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 (by positivity)) (Real.exp_pos _).le)]
    have hre : (-2 : ℂ).re = -2 := by norm_num
    rw [hre, Real.rpow_neg hv0.le, show v ^ (2 : ℝ) = v ^ 2 by norm_cast]
    calc ‖(σO (cc i k) ^ 2)⁻¹‖ * ((v ^ 2)⁻¹ *
          ‖dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹‖)
        ≤ ‖(σO (cc i k) ^ 2)⁻¹‖ * ((v ^ 2)⁻¹ *
          (A * Real.exp (-(Real.pi / 18 / Complex.normSq (σO (cc i k)) / v)))) := by gcongr
      _ = ‖(σO (cc i k) ^ 2)⁻¹‖ * A * ((v ^ 2)⁻¹ *
          Real.exp (-(Real.pi / 18 / Complex.normSq (σO (cc i k)) / v))) := by ring
  -- the series at `∞` is `O(t^{−b})` at `0`
  have hbot : ∀ b : ℝ, dSer a φa =O[𝓝[>] 0] (· ^ (-b)) := by
    intro b
    have hsum : (fun v => ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k * g i k v)) =O[𝓝[>] 0]
        (· ^ (-b)) := by
      have h := IsBigO.sum fun i hi => (IsBigO.sum fun k hk =>
        ((hgbot i hi k hk b).const_mul_left (γ i k)).const_mul_left (β k)).const_mul_left (α i)
      simpa only [Finset.sum_fn] using h
    refine hsum.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hid v hv).symm
  obtain ⟨A, -, hA⟩ := dSer_le_exp ha hφa
  have htop : dSer a φa =O[atTop] fun t => Real.exp (-(Real.pi / 18) * t) := by
    refine IsBigO.of_bound A ?_
    filter_upwards [eventually_ge_atTop 1] with u hu
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hA u hu
  have hloc : LocallyIntegrableOn (dSer a φa) (Ioi 0) :=
    (continuousOn_dSer ha hφa).locallyIntegrableOn measurableSet_Ioi
  refine ⟨fun s => mellinConvergent_of_isBigO_rpow_exp (by positivity) hloc htop
      (hbot (s.re - 1)) (by linarith),
    fun s => mellin_differentiableAt_of_isBigO_rpow_exp (by positivity) hloc htop
      (hbot (s.re - 1)) (by linarith), fun s hs => ?_⟩
  -- the functional equation
  have hconv : ∀ i ∈ S, ∀ k ∈ T, MellinConvergent (dSer (dd i k) φc) (2 - 2 * s) := fun i hi k hk =>
    mellinConvergent_dSer (hdd i hi k hk).1 hφc (by simp; linarith)
  have hcusp : ∀ i ∈ S, ∀ k ∈ T, MellinConvergent (g i k) (2 * s) ∧
      mellin (g i k) (2 * s) = -(σO (cc i k) ^ 2)⁻¹ *
        ((Complex.normSq (σO (cc i k)) : ℂ) ^ (2 - 2 * s) * mellin (dSer (dd i k) φc) (2 - 2 * s)) := by
    intro i hi k hk
    have hN : 0 < Complex.normSq (σO (cc i k)) := Complex.normSq_pos.2 (hdd i hi k hk).2
    obtain ⟨h1, h2⟩ := mellin_cuspTerm hN s (hconv i hi k hk)
    have hfun : g i k = fun v : ℝ => (-(σO (cc i k) ^ 2)⁻¹) •
        ((v : ℂ) ^ (-2 : ℂ) • dSer (dd i k) φc (Complex.normSq (σO (cc i k)) * v)⁻¹) :=
      funext (hgform i k)
    rw [hfun]
    exact ⟨h1.const_smul _, by rw [mellin_const_smul, h2, smul_eq_mul]⟩
  have hmel : mellin (dSer a φa) (2 * s) =
      mellin (fun v => ∑ i ∈ S, α i * ∑ k ∈ T, β k * (γ i k * g i k v)) (2 * s) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [hid v hv]
  rw [hmel, mellin_nested_sum S T α β γ g _ fun i hi k hk => (hcusp i hi k hk).1]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(hcusp i hi k hk).2]

theorem norm_phiInf_le (m : 𝓞 K) :
    ‖2 * Real.pi * I * conj (σO m) / 9‖ ≤ 2 * Real.pi / 9 * ‖σO m‖ := by
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h9 : ‖(9 : ℂ)‖ = 9 := by norm_num
  rw [h2, h9, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  apply le_of_eq; ring

theorem norm_phiCusp_le (m : 𝓞 K) : ‖2 * Real.pi * I * σO m / 9‖ ≤ 2 * Real.pi / 9 * ‖σO m‖ := by
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h9 : ‖(9 : ℂ)‖ = 9 := by norm_num
  rw [h2, h9, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  apply le_of_eq; ring

/-- The twisted coefficients `F(m/λ)·conj τ(−m)` satisfy the support and size condition, for a
bounded `F`. -/
theorem thetaSupp_twisted {Kc : ℝ} {τ : 𝓞 K → ℂ} (hτ : ThetaSupp Kc τ) {F : 𝓞 K → ℂ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ‖F x‖ ≤ B) :
    ThetaSupp (B * Kc) fun m => twAt F m * conj (τ (-m)) := by
  have h1 := thetaSupp_mul_le (thetaSupp_conj hτ) hB0 (norm_twAt_le hB0 hB)
  have e : (fun m => conj (τ (-m)) * twAt F m) = fun m => twAt F m * conj (τ (-m)) :=
    funext fun m => mul_comm _ _
  rwa [e] at h1

/-- The coefficients of a group's series at its cusp satisfy the support and size condition. -/
theorem thetaSupp_cuspCoef {Kc : ℝ} {dH : 𝓞 K → ℂ} (h : ThetaSupp Kc dH) (D y : 𝓞 K) (A : Finset Pr)
    (j : Pr → ℕ) :
    ThetaSupp ((∏ P : A, Real.sqrt (absNorm P.1.1)) * Kc) fun m =>
      conj (dH (-m)) * ψc (δ3 ^ 3 * D) (-(m * y)) * ∏ P : A, Bloc P.1.1 (j P.1) m := by
  have h1 := thetaSupp_mul (thetaSupp_conj h) (fun m => (norm_ψc (δ3 ^ 3 * D) (-(m * y))).le)
  exact thetaSupp_mul_le h1 (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) fun m => by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P _ => norm_Bloc_le_sqrt P.1 (j P.1) m

open Classical in
/-- **`𝒥(s)` for the twisted `θ̄`** (S5f-4c): with the data of round 373's `twisted_theta_dbar`, the
Mellin transform of the `∂_{z̄}`-series at `∞`, `𝒥(s) = ∫_0^∞ D(v)v^{2s−1} dv`, converges at every `s`
and is entire. For `Re s ≥ 5/3` it is the Dirichlet series of the twisted coefficients with the Gamma
factors of (A.15). For `Re s < −3/2` it is the sum over the groups of
`−σ(c)^{−2}N(c)^{2−2s}` times the Dirichlet series of the cusp coefficients at `1 − s`. -/
theorem twisted_theta_mellin {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c0 cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c0 cP cM τ tP tM) {L : 𝓞 K} (hL : L ≠ 0) (φ₀ : 𝓞 K → ℂ)
    (hφ : ∀ z u, φ₀ (z + L * u) = φ₀ z) (hφ0 : φ₀ 0 = 0) (Ps : Finset Pr) (hPs : ∀ P ∈ Ps, L ∉ P.1)
    (j : Pr → ℕ) :
    ∃ (D : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K) (C₀ : (𝓞 K ⧸ span {L}) → Finset Pr → ℂ)
      (dH : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K → ℂ) (y : (𝓞 K ⧸ span {L}) → Finset Pr → 𝓞 K),
      (∀ h₀, ∀ A ∈ Ps.powerset, D h₀ A ≠ 0 ∧ D h₀ A ∣ L ∧ ‖C₀ h₀ A‖ = 1 ∧ ThetaSupp Kc (dH h₀ A)) ∧
      (∀ s, MellinConvergent (dSer (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m *
        conj (τ (-m))) fun m => 2 * Real.pi * I * conj (σO m) / 9) s) ∧
      Differentiable ℂ (mellin (dSer (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m *
        conj (τ (-m))) fun m => 2 * Real.pi * I * conj (σO m) / 9)) ∧
      (∀ s : ℂ, 5 / 3 ≤ s.re →
        mellin (dSer (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m *
          conj (τ (-m))) fun m => 2 * Real.pi * I * conj (σO m) / 9) (2 * s) =
        ∑' m : 𝓞 K, twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m * conj (τ (-m)) *
          (2 * Real.pi * I * conj (σO m) / 9) * (2 ^ (2 * s - 1) * Gamma (s + 1 / 3) *
            Gamma (s + 2 / 3) * (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * s + 1)))) ∧
      ∀ s : ℂ, s.re < -3 / 2 →
        mellin (dSer (fun m => twAt (fun x => φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x) m *
          conj (τ (-m))) fun m => 2 * Real.pi * I * conj (σO m) / 9) (2 * s) =
        ∑ᶠ h₀ : 𝓞 K ⧸ span {L}, fCoef L φ₀ (repQ L h₀) *
          ∑ A ∈ Ps.powerset, (∏ P ∈ Ps \ A, locCoef P (j P) 0) *
            (C₀ h₀ A * (-(σO (D h₀ A * ∏ P ∈ A, πP P) ^ 2)⁻¹ *
              (((Complex.normSq (σO (D h₀ A * ∏ P ∈ A, πP P)) : ℝ) : ℂ) ^ (2 - 2 * s) *
                ∑' m : 𝓞 K, conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
                    (∏ P : A, Bloc P.1.1 (j P.1) m) * (2 * Real.pi * I * σO m / 9) *
                  (2 ^ (2 * (1 - s) - 1) * Gamma ((1 - s) + 1 / 3) * Gamma ((1 - s) + 2 / 3) *
                    (((4 * Real.pi * ‖σO m‖ / 9 : ℝ)) : ℂ) ^ (-(2 * (1 - s) + 1)))))) := by
  obtain ⟨D, C₀, dH, y, hDATA, hid⟩ := twisted_theta_dbar hd hL φ₀ hφ hφ0 Ps hPs j
  obtain ⟨B₀, hB₀⟩ := exists_bound_of_periodic L hL φ₀ hφ
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  have hF : ∀ x, ‖φ₀ x * ∏ P ∈ Ps, chiPow P.1 (j P) x‖ ≤ B₀ := by
    intro x
    rw [norm_mul, norm_prod]
    exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun P _ => norm_chiPow_le _ _ _))).trans (hB₀ x)
  have ha := thetaSupp_twisted hd.1 hB₀0 hF
  have hcne : ∀ (h₀ : 𝓞 K ⧸ span {L}), ∀ A ∈ Ps.powerset, σO (D h₀ A * ∏ P ∈ A, πP P) ≠ 0 := by
    intro h₀ A hA
    have hD := (hDATA h₀ A hA).1
    have hprod : (∏ P ∈ A, πP P) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P _ => ne_zero_of_maximal (πP P)
    have hc : D h₀ A * ∏ P ∈ A, πP P ≠ 0 := mul_ne_zero hD hprod
    exact fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  have := finite_quot L hL
  let _ : Fintype (𝓞 K ⧸ span {L}) := Fintype.ofFinite _
  obtain ⟨hconv, hdiff, hFE⟩ := mellin_FE Finset.univ Ps.powerset ha (fun m => norm_phiInf_le m)
    (fun m => norm_phiCusp_le m) (fun h₀ => fCoef L φ₀ (repQ L h₀))
    (fun A => ∏ P ∈ Ps \ A, locCoef P (j P) 0) C₀
    (fun h₀ A m => conj (dH h₀ A (-m)) * ψc (δ3 ^ 3 * D h₀ A) (-(m * y h₀ A)) *
      ∏ P : A, Bloc P.1.1 (j P.1) m)
    (fun h₀ A => D h₀ A * ∏ P ∈ A, πP P) (fun _ A => (∏ P : A, Real.sqrt (absNorm P.1.1)) * Kc)
    (fun h₀ _ A hA => ⟨thetaSupp_cuspCoef (hDATA h₀ A hA).2.2.2 _ _ A j, hcne h₀ A hA⟩)
    (fun v hv => by rw [← finsum_eq_sum_of_fintype]; exact hid v hv)
  refine ⟨D, C₀, dH, y, hDATA, hconv, hdiff, fun s hs => mellin_dSer ha (fun m => norm_phiInf_le m) hs,
    fun s hs => ?_⟩
  rw [hFE s hs, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun h₀ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have hm := mellin_dSer (thetaSupp_cuspCoef (hDATA h₀ A hA).2.2.2 (D h₀ A) (y h₀ A) A j)
    (fun m => norm_phiCusp_le m) (w := 1 - s) (by simp; linarith)
  rw [show (2 : ℂ) - 2 * s = 2 * (1 - s) by ring, hm]

end Eis

end

#print axioms Eis.bkR_third_le
#print axioms Eis.small_aux
#print axioms Eis.inv_cube_le
#print axioms Eis.dSer_le_exp
#print axioms Eis.dSer_le_small
#print axioms Eis.continuousOn_dSer
#print axioms Eis.mellinConvergent_dSer
#print axioms Eis.integral_norm_ofReal_of_nonneg
#print axioms Eis.besselK_third_ofReal
#print axioms Eis.integral_norm_besselK_third
#print axioms Eis.mellin_dSer
#print axioms Eis.isBigO_inv_sq_exp_inv
#print axioms Eis.mellin_nested_sum
#print axioms Eis.mellin_cuspTerm
#print axioms Eis.mellin_FE
#print axioms Eis.norm_phiInf_le
#print axioms Eis.norm_phiCusp_le
#print axioms Eis.thetaSupp_twisted
#print axioms Eis.thetaSupp_cuspCoef
#print axioms Eis.twisted_theta_mellin
