import Mathlib
import SpectralGap

/-! # A certified lower bound on `Q₀` orthogonally to `w`, for every `0 < a ≤ 0.35`

For every support `0 < a ≤ 0.35` (so `δ = 2a ≤ 0.7`, past the first prime `log 2`), every
normalised probe `g` with `ĝ(i/2) = ⟨g, w⟩ = 0` has `Q₀(g) = Q(g) ≥ λ₁ + 1/40`, and `≥ λ₁ + 1/10`
when `2a < log 2`. Hence the ground state of the full form `Q` is unique up to sign there.

The method is an exact Fourier representation, not an approximation.
* **A.** View `g` (supported in `[−a, a]`) on a circle of length `8a`. For `0 ≤ u ≤ 2a` the circular
  and true autocorrelations agree, so `1 − f(u) = Σ_n p_n (1 − cos(πnu/4a))` with `Σ p_n = 1`.
* **B.** Hence the near-field energy is `∫_{(0,2a]}(1 − f)K ≥ τ + Σ_{|n|≤5}(ψ_n − τ)p_n` whenever
  every mode energy `ψ_n = ∫_{(0,2a]}(1 − cos(πnu/4a))K` with `|n| ≥ 6` is at least `τ`.
* **C.** `K(u) = ½csch(u/2) + ½sech(u/2) ≥ 1/u + ½ − r(u)` (Taylor bounds for `exp`), so
  `ψ_n ≥ Cin(πn/2) + a(1 − 2 sin(πn/2)/(πn)) − err(a)`.
* **D.** `Cin(x) = ∫₀ˣ(1 − cos s)/s` is bounded below at `x = πk/2`, `k ≤ 61`, by a Taylor piece and
  tangent-line pieces `1/s ≥ 2/c − s/c²` with exact antiderivatives.
* **E.** For even `g` the mode masses are `p_n = (∫ g cos(πnt/4a))²/(8a)`; Cauchy–Schwarz against
  `cos − β_n`, with `(∫ g)² ≤ a⁵/30` from `g ⊥ w`, bounds `p_1, …, p_5`.
* **F–G.** The box has near-field energy `≤ 1 + a/2` and pole term `≤ 4a(1 + a²/24 + a⁴/1600)²`.
* **H–J.** Past `log 2`, the prime `n = 2` enters as `−√2 log 2 · f(log 2)`, and
  `f(log 2) = Σ p_n (cos(ω_n log 2) − cos(ω_n 2a))` since `f(2a) = 0`; each defect is
  `≤ min(ω_n(2a − log 2), 2)`, absorbed mode by mode with tail levels at `n = 6, 11, 21, 61`.

No semiclassical input: only the explicit formula's archimedean kernel, Parseval on a circle, and
elementary calculus. Every number is proved in Lean (the only external constants are Mathlib's
bounds on `π`, `log 2` and `e`).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## A. The exact Fourier representation on a circle of length `8a` -/

/-- `cf_shift` with support `r` and any shift keeping the support inside the window. -/
theorem cf_shift' {A r : ℝ} {g : ℝ → ℝ} (hsupp : ∀ u, r < |u| → g u = 0) {s : ℝ}
    (hr : r < 2 * A) (hs : r + |s| < 2 * A) (n : ℤ) :
    cf A (fun t => g (t + s)) n = Complex.exp (2 * π * I * n * s / (4 * A)) * cf A g n := by
  unfold cf
  set E : ℝ → ℂ := fun t => Complex.exp (-(2 * π * I * n * t / (4 * A))) with hE
  show (1 / (4 * A) : ℂ) * (∫ t in (-(2 * A))..(2 * A), E t * ((g (t + s) : ℝ) : ℂ))
    = Complex.exp (2 * π * I * n * s / (4 * A))
      * ((1 / (4 * A) : ℂ) * ∫ t in (-(2 * A))..(2 * A), E t * ((g t : ℝ) : ℂ))
  have h1 : (∫ t in (-(2 * A))..(2 * A), E t * ((g (t + s) : ℝ) : ℂ))
      = ∫ x in (-(2 * A) + s)..(2 * A + s), E (x - s) * ((g x : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_comp_add_right (fun x => E (x - s) * ((g x : ℝ) : ℂ)) s]
    simp only [add_sub_cancel_right]
  have hEs : ∀ x, E (x - s) = Complex.exp (2 * π * I * n * s / (4 * A)) * E x := by
    intro x; simp only [hE]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hsuppC : ∀ u, r < |u| → E u * ((g u : ℝ) : ℂ) = 0 := fun u hu => by
    rw [hsupp u hu]; simp
  have hs1 := le_abs_self s
  have hs2 := neg_abs_le s
  rw [h1]
  simp_rw [hEs, mul_assoc]
  rw [intervalIntegral.integral_const_mul,
    integral_eq_of_supp hsuppC (by linarith) (by linarith),
    integral_eq_of_supp hsuppC (by linarith) (by linarith)]
  ring

/-- `hasSum_shift` for support `r` and any shift with `r + |s| < 2A`. -/
theorem hasSum_shift' {A r : ℝ} (hA : 0 < A) {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    (hsupp : ∀ u, r < |u| → g u = 0) {s : ℝ} (hs : r + |s| < 2 * A) :
    HasSum (fun n : ℤ => ‖cf A g n‖ ^ 2 * (2 - 2 * Real.cos (2 * π * n * s / (4 * A))))
      ((4 * A)⁻¹ * (2 * (autocorr g 0 - autocorr g s))) := by
  have hgs : MemLp (fun t => g (t + s)) 2 volume :=
    hg.comp_measurePreserving (measurePreserving_add_right volume s)
  have hmem : MemLp (fun t => g t - g (t + s)) 2 volume := hg.sub hgs
  have hsupp2 : ∀ u, r + |s| < |u| → g u - g (u + s) = 0 := by
    intro u hu
    have h1 : r < |u| := by linarith [abs_nonneg s]
    have h2 : r < |u + s| := by
      have : |u| ≤ |u + s| + |s| := by
        have := abs_sub (u + s) s
        rwa [add_sub_cancel_right] at this
      linarith
    rw [hsupp u h1, hsupp _ h2, sub_self]
  have hP := hasSum_cf_sq hA hs hmem hsupp2
  rw [normSq_sub_shift hg s] at hP
  convert hP using 1
  funext n
  have hlin : cf A (fun t => g t - g (t + s)) n
      = cf A g n * (1 - Complex.exp (((2 * π * n * s / (4 * A) : ℝ) : ℂ) * I)) := by
    rw [cf_sub (memLp_intervalIntegrable hg _ _) (memLp_intervalIntegrable hgs _ _),
      cf_shift' hsupp (by linarith [abs_nonneg s]) hs n]
    have : Complex.exp (2 * π * I * n * s / (4 * A))
        = Complex.exp (((2 * π * n * s / (4 * A) : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    rw [this]; ring
  rw [hlin, norm_mul, mul_pow, norm_one_sub_exp_sq]

/-- The mode masses `p_n = 8a·|c_n|²` on the circle of length `8a`. -/
def pm (a : ℝ) (g : ℝ → ℝ) (n : ℤ) : ℝ := 8 * a * ‖cf (2 * a) g n‖ ^ 2

theorem pm_nonneg {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) (n : ℤ) : 0 ≤ pm a g n := by
  unfold pm; positivity

/-- `Σ p_n = ‖g‖²`. -/
theorem hasSum_pm {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) :
    HasSum (pm a g) (normSq g) := by
  have h := (hasSum_cf_sq (a := 2 * a) (r := a) (by linarith) (by linarith) hp.memL2 hp.supp).mul_left
    (8 * a)
  have e : 8 * a * ((4 * (2 * a))⁻¹ * normSq g) = normSq g := by field_simp; ring
  rw [e] at h; exact h

/-- **`1 − f(u) = Σ p_n (1 − cos(πnu/4a))`** for `0 ≤ u ≤ 2a`, `‖g‖ = 1`. -/
theorem hasSum_one_sub_autocorr {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    HasSum (fun n : ℤ => pm a g n * (1 - Real.cos (π * n * u / (4 * a)))) (1 - autocorr g u) := by
  have h := (hasSum_shift' (A := 2 * a) (r := a) (by linarith) hp.memL2 hp.supp
    (s := u) (by rw [abs_of_nonneg hu0]; linarith)).mul_left (4 * a)
  rw [autocorr_zero, hn] at h
  convert h using 1
  · funext n
    unfold pm
    rw [show 2 * π * (n : ℝ) * u / (4 * (2 * a)) = π * n * u / (4 * a) by field_simp]
    ring
  · field_simp


/-! ## B. The energy as a sum over modes -/

/-- The mode energy `ψ_n = ∫_{(0,2a]} (1 − cos(πnu/4a)) K(u) du`. -/
def modeE (a : ℝ) (n : ℤ) : ℝ := ∫ u in Ioc 0 (2 * a), (1 - Real.cos (π * n * u / (4 * a))) * kerK u

theorem modeE_integrable {a : ℝ} (ha : 0 < a) (n : ℤ) :
    IntegrableOn (fun u => (1 - Real.cos (π * n * u / (4 * a))) * kerK u) (Ioc 0 (2 * a)) := by
  set ω := π * n / (4 * a)
  have hm : Measurable (fun u => (1 - Real.cos (π * n * u / (4 * a))) * kerK u) :=
    (measurable_const.sub (Real.continuous_cos.measurable.comp (by fun_prop))).mul kerK_measurable
  refine (integrableOn_const (C := ω ^ 2 * a * Real.exp a) measure_Ioc_lt_top.ne).mono'
    hm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall
      fun u hu => ?_))
  have hu0 := hu.1
  have hK0 : 0 ≤ kerK u := (kerK_pos hu0).le
  have hc1 : 0 ≤ 1 - Real.cos (π * n * u / (4 * a)) := by linarith [Real.cos_le_one (π * n * u / (4 * a))]
  have hc2 : 1 - Real.cos (π * n * u / (4 * a)) ≤ (ω * u) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := π * n * u / (4 * a))
    have e : π * n * u / (4 * a) = ω * u := by simp only [ω]; ring
    rw [e] at this ⊢; linarith
  have hK := kerK_le hu0
  have he : Real.exp (u / 2) ≤ Real.exp a := Real.exp_le_exp.2 (by linarith [hu.2])
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc1 hK0)]
  calc (1 - Real.cos (π * n * u / (4 * a))) * kerK u ≤ (ω * u) ^ 2 / 2 * (Real.exp (u / 2) / u) :=
        mul_le_mul hc2 hK hK0 (by positivity)
    _ = ω ^ 2 * (u / 2) * Real.exp (u / 2) := by field_simp
    _ ≤ ω ^ 2 * a * Real.exp a := by
        have : u / 2 ≤ a := by linarith [hu.2]
        have := sq_nonneg ω
        gcongr

theorem modeE_nonneg {a : ℝ} (n : ℤ) : 0 ≤ modeE a n :=
  setIntegral_nonneg measurableSet_Ioc fun u hu =>
    mul_nonneg (by linarith [Real.cos_le_one (π * n * u / (4 * a))]) (kerK_pos hu.1).le

theorem modeE_neg (a : ℝ) (n : ℤ) : modeE a (-n) = modeE a n := by
  unfold modeE; congr 1; funext u; push_cast
  rw [show π * -(n : ℝ) * u / (4 * a) = -(π * n * u / (4 * a)) by ring, Real.cos_neg]

/-- **Finite partial sums of the mode expansion are below the near-field energy.** -/
theorem sum_modeE_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    (S : Finset ℤ) :
    ∑ n ∈ S, pm a g n * modeE a n ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have e : ∑ n ∈ S, pm a g n * modeE a n
      = ∫ u in Ioc 0 (2 * a), ∑ n ∈ S, pm a g n * ((1 - Real.cos (π * n * u / (4 * a))) * kerK u) := by
    rw [integral_finsetSum S fun n _ => (modeE_integrable ha n).const_mul _]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold modeE; rw [integral_const_mul]
  rw [e]
  refine setIntegral_mono_on (integrable_finsetSum S fun n _ => (modeE_integrable ha n).const_mul _)
    (hp.arch.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun u hu => ?_
  have hK0 : 0 ≤ kerK u := (kerK_pos hu.1).le
  have hs := sum_le_hasSum S (fun n _ => mul_nonneg (pm_nonneg ha g n)
    (by linarith [Real.cos_le_one (π * n * u / (4 * a))]))
    (hasSum_one_sub_autocorr ha hp hn hu.1.le hu.2)
  have e2 : archIntegrand g u = (1 - autocorr g u) * kerK u := by
    unfold archIntegrand kerK; rw [autocorr_zero, hn]
  rw [e2]
  calc ∑ n ∈ S, pm a g n * ((1 - Real.cos (π * n * u / (4 * a))) * kerK u)
      = (∑ n ∈ S, pm a g n * (1 - Real.cos (π * n * u / (4 * a)))) * kerK u := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hK0

/-- **The truncated lower bound**: if every mode outside `S₀` has energy at least `τ ≥ 0`, then
`τ + Σ_{S₀} (ψ_n − τ) p_n ≤ ∫_{(0,2a]} A_g`. -/
theorem energy_ge_trunc {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    (S₀ : Finset ℤ) {τ : ℝ} (hτ : ∀ n, n ∉ S₀ → τ ≤ modeE a n) :
    τ + ∑ n ∈ S₀, (modeE a n - τ) * pm a g n ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have hP := hasSum_pm ha hp
  rw [hn] at hP
  have hT : Tendsto (fun S : Finset ℤ => ∑ n ∈ S₀, (modeE a n - τ) * pm a g n
      + τ * ∑ n ∈ S, pm a g n) atTop (𝓝 (∑ n ∈ S₀, (modeE a n - τ) * pm a g n + τ * 1)) :=
    tendsto_const_nhds.add (hP.const_mul τ)
  rw [mul_one, add_comm] at hT
  refine le_of_tendsto hT ?_
  filter_upwards [eventually_ge_atTop S₀] with S hS
  have hsplit := Finset.sum_sdiff hS (f := pm a g)
  have hsplit2 := Finset.sum_sdiff hS (f := fun n => pm a g n * modeE a n)
  have htail : τ * ∑ n ∈ S \ S₀, pm a g n ≤ ∑ n ∈ S \ S₀, pm a g n * modeE a n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn' => ?_
    rw [Finset.mem_sdiff] at hn'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hτ n hn'.2) (pm_nonneg ha g n)
  have hlow : ∑ n ∈ S₀, (modeE a n - τ) * pm a g n
      = ∑ n ∈ S₀, pm a g n * modeE a n - τ * ∑ n ∈ S₀, pm a g n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hle := sum_modeE_le ha hp hn S
  rw [← hsplit, mul_add] at *
  rw [← hsplit2] at hle
  linarith

/-! ## C. The kernel sandwich and the mode energies -/

theorem kerK_eq {u : ℝ} (hu : 0 < u) :
    kerK u = 1 / 2 / Real.sinh (u / 2) + 1 / 2 / Real.cosh (u / 2) := by
  unfold kerK
  have hs : 0 < Real.sinh (u / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  have e1 : Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have e2 : Real.exp (u / 2) = Real.cosh (u / 2) + Real.sinh (u / 2) := (Real.cosh_add_sinh _).symm
  rw [e1, e2]; field_simp

/-- `K(u) ≤ 1/u + 1/2`. -/
theorem kerK_le' {u : ℝ} (hu : 0 < u) : kerK u ≤ 1 / u + 1 / 2 := by
  rw [kerK_eq hu]
  have hs : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.2 (by linarith)
  have hc : 1 ≤ Real.cosh (u / 2) := Real.one_le_cosh _
  have h1 : 1 / 2 / Real.sinh (u / 2) ≤ 1 / u := by
    rw [div_div, div_le_div_iff₀ (by positivity) hu]; linarith
  have h2 : 1 / 2 / Real.cosh (u / 2) ≤ 1 / 2 := div_le_self (by norm_num) hc
  linarith

theorem sinh_le_taylor {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) :
    Real.sinh y ≤ y + y ^ 3 / 6 + y ^ 5 / 100 := by
  have h1 := Real.exp_bound (x := y) (by rw [abs_of_nonneg hy0]; exact hy) (n := 5) (by norm_num)
  have h2 := Real.exp_bound (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact hy) (n := 5)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    at h1 h2
  rw [abs_neg, abs_of_nonneg hy0] at h2
  rw [abs_of_nonneg hy0] at h1
  rw [Real.sinh_eq]
  have a1 := (abs_le.1 h1).2
  have a2 := (abs_le.1 h2).1
  norm_num at a1 a2 ⊢
  nlinarith [pow_nonneg hy0 5]

theorem cosh_le_taylor {y : ℝ} (hy : |y| ≤ 1) :
    Real.cosh y ≤ 1 + y ^ 2 / 2 + 5 * y ^ 4 / 96 := by
  have h1 := Real.exp_bound (x := y) hy (n := 4) (by norm_num)
  have h2 := Real.exp_bound (x := -y) (by rwa [abs_neg]) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    at h1 h2
  rw [abs_neg] at h2
  rw [Real.cosh_eq]
  have a1 := (abs_le.1 h1).2
  have a2 := (abs_le.1 h2).2
  have hy4 : |y| ^ 4 = y ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [hy4] at a1 a2
  norm_num at a1 a2 ⊢
  nlinarith

/-- The remainder `r(u) = u/24 + u²/16 + u³/1600 + 5u⁴/3072`. -/
def remK (u : ℝ) : ℝ := u / 24 + u ^ 2 / 16 + u ^ 3 / 1600 + 5 * u ^ 4 / 3072

/-- `K(u) ≥ 1/u + 1/2 − r(u)` on `(0, 2]`. -/
theorem kerK_ge_taylor {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) : 1 / u + 1 / 2 - remK u ≤ kerK u := by
  rw [kerK_eq hu]
  set y := u / 2 with hy
  have hy0 : 0 < y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hs := sinh_le_taylor hy0.le hy1
  have hc := cosh_le_taylor (y := y) (by rw [abs_of_pos hy0]; exact hy1)
  have hsp : 0 < Real.sinh y := Real.sinh_pos_iff.2 hy0
  have hcp : 0 < Real.cosh y := Real.cosh_pos _
  -- `1/sinh y ≥ (1/y)(1 − y²/6 − y⁴/100)`, `1/cosh y ≥ 2 − cosh y`
  have i1 : (1 - y ^ 2 / 6 - y ^ 4 / 100) / y ≤ 1 / Real.sinh y := by
    rw [div_le_div_iff₀ hy0 hsp, one_mul]
    have : Real.sinh y * (1 - y ^ 2 / 6 - y ^ 4 / 100)
        ≤ (y + y ^ 3 / 6 + y ^ 5 / 100) * (1 - y ^ 2 / 6 - y ^ 4 / 100) := by
      apply mul_le_mul_of_nonneg_right hs; nlinarith [pow_le_one₀ hy0.le hy1 (n := 2),
        pow_le_one₀ hy0.le hy1 (n := 4)]
    nlinarith [pow_pos hy0 3, pow_pos hy0 5, pow_pos hy0 7, pow_pos hy0 9]
  have i2 : 2 - Real.cosh y ≤ 1 / Real.cosh y := by
    rw [le_div_iff₀ hcp]; nlinarith [sq_nonneg (Real.cosh y - 1)]
  unfold remK
  have e1 : 1 / 2 / Real.sinh y = (1 / 2) * (1 / Real.sinh y) := by ring
  have e2 : 1 / 2 / Real.cosh y = (1 / 2) * (1 / Real.cosh y) := by ring
  rw [e1, e2]
  have e3 : (1 - y ^ 2 / 6 - y ^ 4 / 100) / y = 2 / u - u / 12 - u ^ 3 / 800 := by
    rw [hy]; field_simp; ring
  rw [e3] at i1
  have e4 : 1 / u = (1 / 2) * (2 / u) := by ring
  rw [e4]
  have hy2 : y ^ 2 = u ^ 2 / 4 := by rw [hy]; ring
  have hy4 : y ^ 4 = u ^ 4 / 16 := by rw [hy]; ring
  rw [hy2, hy4] at hc
  linarith

/-- `Cin(x) = ∫₀ˣ (1 − cos s)/s ds`. -/
def Cin (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, (1 - Real.cos s) / s

theorem Cin_integrable (b : ℝ) : IntegrableOn (fun s => (1 - Real.cos s) / s) (Ioc 0 b) := by
  have := (integrableOn_weight b 1).div_const 2
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioc
  simp only [one_mul]; ring

theorem Cin_ii {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun s => (1 - Real.cos s) / s) volume 0 b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2 (Cin_integrable b)

theorem Cin_integrand_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ (1 - Real.cos s) / s :=
  div_nonneg (by linarith [Real.cos_le_one s]) hs

theorem Cin_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : Cin x ≤ Cin y := by
  unfold Cin
  have hxy_ii : IntervalIntegrable (fun s => (1 - Real.cos s) / s) volume x y :=
    (Cin_ii (hx.trans hxy)).mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le (hx.trans hxy)]; exact Icc_subset_Icc hx le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals (Cin_ii hx) hxy_ii]
  have := intervalIntegral.integral_nonneg (μ := volume) hxy (fun s hs => Cin_integrand_nonneg (hx.trans hs.1))
  linarith

/-- The error term `err(a) = 2∫₀^{2a} r`. -/
def errK (a : ℝ) : ℝ := a ^ 2 / 6 + a ^ 3 / 3 + a ^ 4 / 200 + a ^ 5 / 48

/-- **Mode energy lower bound**: `ψ_n ≥ Cin(πn/2) + a(1 − 2 sin(πn/2)/(πn)) − err(a)`. -/
theorem modeE_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 0 < n) :
    Cin (π * n / 2) + a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) - errK a ≤ modeE a n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set ω := π * n / (4 * a) with hω
  have hω0 : 0 < ω := by positivity
  have e0 : ∀ u, π * n * u / (4 * a) = ω * u := fun u => by rw [hω]; ring
  set F : ℝ → ℝ := fun u => (1 - Real.cos (ω * u)) / u + (1 - Real.cos (ω * u)) / 2 - 2 * remK u
    with hF
  have hFi1 : IntegrableOn (fun u => (1 - Real.cos (ω * u)) / u) (Ioc 0 (2 * a)) := by
    have := (integrableOn_weight (2 * a) ω).div_const 2
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioc
    ring
  have hc : Continuous (fun u => (1 - Real.cos (ω * u)) / 2 - 2 * remK u) := by
    unfold remK; fun_prop
  have hFi : IntegrableOn F (Ioc 0 (2 * a)) := by
    have := hFi1.add (hc.integrableOn_Ioc (a := 0) (b := 2 * a))
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioc
    simp only [hF, Pi.add_apply]; ring
  have hpt : ∀ u ∈ Ioc 0 (2 * a), F u ≤ (1 - Real.cos (π * n * u / (4 * a))) * kerK u := by
    intro u hu
    rw [e0]
    have hK := kerK_ge_taylor hu.1 (by linarith [hu.2])
    have hr : 0 ≤ remK u := by unfold remK; have := hu.1; positivity
    have c1 : 0 ≤ 1 - Real.cos (ω * u) := by linarith [Real.cos_le_one (ω * u)]
    have c2 : 1 - Real.cos (ω * u) ≤ 2 := by linarith [Real.neg_one_le_cos (ω * u)]
    have e1 : (1 - Real.cos (ω * u)) / u = (1 - Real.cos (ω * u)) * (1 / u) := by ring
    simp only [hF]; rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hK c1, mul_le_mul_of_nonneg_right c2 hr]
  have hmono := setIntegral_mono_on hFi (modeE_integrable ha n) measurableSet_Ioc hpt
  -- evaluate `∫ F`
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  rw [← intervalIntegral.integral_of_le h2a] at hmono
  have iA : IntervalIntegrable (fun u => (1 - Real.cos (ω * u)) / u) volume 0 (2 * a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2a).2 hFi1
  have iB : IntervalIntegrable (fun u => (1 - Real.cos (ω * u)) / 2) volume 0 (2 * a) :=
    (by fun_prop : Continuous (fun u => (1 - Real.cos (ω * u)) / 2)).intervalIntegrable _ _
  have iC : IntervalIntegrable (fun u => 2 * remK u) volume 0 (2 * a) :=
    (by unfold remK; fun_prop : Continuous (fun u => 2 * remK u)).intervalIntegrable _ _
  have hI : (∫ u in (0 : ℝ)..(2 * a), F u) = (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / u)
      + (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / 2)
      - ∫ u in (0 : ℝ)..(2 * a), 2 * remK u := by
    simp only [hF]
    rw [intervalIntegral.integral_sub (iA.add iB) iC, intervalIntegral.integral_add iA iB]
  -- the three integrals
  have hI1 : (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / u) = Cin (π * n / 2) := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * a)
      (fun s => (1 - Real.cos s) / s) hω0.ne'
    have e : (fun u => (1 - Real.cos (ω * u)) / u) = fun u => ω * ((1 - Real.cos (ω * u)) / (ω * u)) := by
      funext u
      by_cases hu : u = 0
      · simp [hu]
      · field_simp
    rw [e, intervalIntegral.integral_const_mul, h, smul_eq_mul, mul_zero,
      show ω * (2 * a) = π * n / 2 by rw [hω]; field_simp; ring]
    unfold Cin; field_simp
  have hI2 : (∫ u in (0 : ℝ)..(2 * a), (1 - Real.cos (ω * u)) / 2)
      = a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) := by
    have hcos : (∫ u in (0 : ℝ)..(2 * a), Real.cos (ω * u)) = Real.sin (π * n / 2) / ω := by
      rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hω0.ne', integral_cos,
        mul_zero, Real.sin_zero, sub_zero, smul_eq_mul,
        show ω * (2 * a) = π * n / 2 by rw [hω]; field_simp; ring]
      field_simp
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous (fun u => Real.cos (ω * u))).intervalIntegrable _ _), hcos,
      intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, hω]
    field_simp; ring
  have hI3 : (∫ u in (0 : ℝ)..(2 * a), 2 * remK u) = errK a := by
    unfold remK errK
    simp only [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow,
        integral_id]
      ring
    all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [hI, hI1, hI2, hI3] at hmono
  exact hmono

/-! ## D. Certified values of `Cin(πk/2)` -/

/-- An antiderivative of `(1 − cos s)(2/c − s/c²)`. -/
def Fk (c s : ℝ) : ℝ := 2 / c * (s - Real.sin s) - 1 / c ^ 2 * (s ^ 2 / 2 - Real.cos s - s * Real.sin s)

theorem Fk_deriv (c s : ℝ) :
    HasDerivAt (Fk c) ((1 - Real.cos s) * (2 / c - s / c ^ 2)) s := by
  have h1 : HasDerivAt (fun s => s - Real.sin s) (1 - Real.cos s) s :=
    (hasDerivAt_id s).sub (Real.hasDerivAt_sin s)
  have h2 : HasDerivAt (fun s => s ^ 2 / 2 - Real.cos s - s * Real.sin s)
      (s * (1 - Real.cos s)) s := by
    have := (((hasDerivAt_pow 2 s).div_const 2).sub (Real.hasDerivAt_cos s)).sub
      ((hasDerivAt_id s).mul (Real.hasDerivAt_sin s))
    exact this.congr_deriv (by simp; ring)
  have := (h1.const_mul (2 / c)).sub (h2.const_mul (1 / c ^ 2))
  exact this.congr_deriv (by ring)

/-- **One tangent-line step**: `Cin(β) ≥ Cin(α) + F_c(β) − F_c(α)`, from `1/s ≥ 2/c − s/c²`. -/
theorem cin_step {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hc : 0 < c) :
    Cin α + (Fk c β - Fk c α) ≤ Cin β := by
  unfold Cin
  have hii : IntervalIntegrable (fun s => (1 - Real.cos s) / s) volume α β :=
    (Cin_ii (hα.le.trans hαβ)).mono_set (by
      rw [uIcc_of_le hαβ, uIcc_of_le (hα.le.trans hαβ)]; exact Icc_subset_Icc hα.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals (Cin_ii hα.le) hii]
  have hcont : Continuous (fun s => (1 - Real.cos s) * (2 / c - s / c ^ 2)) := by fun_prop
  have hF : (∫ s in α..β, (1 - Real.cos s) * (2 / c - s / c ^ 2)) = Fk c β - Fk c α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => Fk_deriv c s)
      (hcont.intervalIntegrable _ _)
  have hmono := intervalIntegral.integral_mono_on hαβ (hcont.intervalIntegrable _ _) hii
    (fun s hs => by
      have hs0 : 0 < s := hα.trans_le hs.1
      have h1 : 0 ≤ 1 - Real.cos s := by linarith [Real.cos_le_one s]
      have h2 : 2 / c - s / c ^ 2 ≤ 1 / s := by
        rw [div_sub_div _ _ hc.ne' (by positivity), div_le_div_iff₀ (by positivity) hs0]
        nlinarith [sq_nonneg (s - c), hc]
      calc (1 - Real.cos s) * (2 / c - s / c ^ 2) ≤ (1 - Real.cos s) * (1 / s) :=
            mul_le_mul_of_nonneg_left h2 h1
        _ = (1 - Real.cos s) / s := by ring)
  rw [hF] at hmono
  linarith

theorem cin_quarter : (0.14925 : ℝ) ≤ Cin (1 * π / 4) := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  rw [one_mul]
  unfold Cin
  have h0 : (0 : ℝ) ≤ π / 4 := by positivity
  have hmono := intervalIntegral.integral_mono_on h0
    ((by fun_prop : Continuous (fun s : ℝ => s / 2 - 5 * s ^ 3 / 96)).intervalIntegrable _ _)
    (Cin_ii h0) (fun s hs => by
      rcases hs.1.eq_or_lt with h | hs0
      · rw [← h]; simp
      · have hs1 : |s| ≤ 1 := by rw [abs_of_pos hs0]; linarith [hs.2]
        have hb := (abs_le.1 (Real.cos_bound hs1)).2
        rw [abs_of_pos hs0] at hb
        rw [le_div_iff₀ hs0]
        nlinarith)
  have hval : (∫ s in (0 : ℝ)..(π / 4), (s / 2 - 5 * s ^ 3 / 96))
      = (π / 4) ^ 2 / 4 - 5 * (π / 4) ^ 4 / 384 := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_div, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    · ring
    · exact (by fun_prop : Continuous (fun s : ℝ => s / 2)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun s : ℝ => 5 * s ^ 3 / 96)).intervalIntegrable _ _
  rw [hval] at hmono
  nlinarith [sq_nonneg π, pow_pos Real.pi_pos 3, pow_pos Real.pi_pos 4]

theorem num_atoms :
    (0.3183097 : ℝ) < 1 / π ∧ 1 / π < (0.31831 : ℝ) ∧
    (1.414213 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (1.414214 : ℝ) ∧
    (0.3183097 * 1.414213 : ℝ) < 1 / π * Real.sqrt 2 ∧ 1 / π * Real.sqrt 2 < (0.31831 * 1.414214 : ℝ) ∧
    (0.3183097 ^ 2 : ℝ) < (1 / π) ^ 2 ∧ (1 / π) ^ 2 < (0.31831 ^ 2 : ℝ) ∧
    (0.3183097 ^ 2 * 1.414213 : ℝ) < (1 / π) ^ 2 * Real.sqrt 2 ∧
    (1 / π) ^ 2 * Real.sqrt 2 < (0.31831 ^ 2 * 1.414214 : ℝ) := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hx1 : (0.3183097 : ℝ) < 1 / π := by rw [lt_div_iff₀ Real.pi_pos]; nlinarith
  have hx2 : 1 / π < (0.31831 : ℝ) := by rw [div_lt_iff₀ Real.pi_pos]; nlinarith
  have hs1 : (1.414213 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 < (1.414214 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hx0 : (0 : ℝ) < 1 / π := by positivity
  refine ⟨hx1, hx2, hs1, hs2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_lt_mul'' hx1 hs1 (by norm_num) (by norm_num)
  · exact mul_lt_mul'' hx2 hs2 hx0.le (by positivity)
  · exact pow_lt_pow_left₀ hx1 (by norm_num) (by norm_num)
  · exact pow_lt_pow_left₀ hx2 hx0.le (by norm_num)
  · exact mul_lt_mul'' (pow_lt_pow_left₀ hx1 (by norm_num) (by norm_num)) hs1 (by norm_num) (by norm_num)
  · exact mul_lt_mul'' (pow_lt_pow_left₀ hx2 hx0.le (by norm_num)) hs2 (by positivity) (by positivity)

theorem sc0 : Real.sin (0 * π / 4) = 0 ∧ Real.cos (0 * π / 4) = 1 := by simp

theorem sc1 : Real.sin (1 * π / 4) = Real.sqrt 2 / 2 ∧ Real.cos (1 * π / 4) = Real.sqrt 2 / 2 := by
  rw [one_mul]; exact ⟨Real.sin_pi_div_four, Real.cos_pi_div_four⟩

theorem sc2 : Real.sin (2 * π / 4) = 1 ∧ Real.cos (2 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc0
  rw [show (2 : ℝ) * π / 4 = 0 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc3 : Real.sin (3 * π / 4) = Real.sqrt 2/2 ∧ Real.cos (3 * π / 4) = -Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc1
  rw [show (3 : ℝ) * π / 4 = 1 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc4 : Real.sin (4 * π / 4) = 0 ∧ Real.cos (4 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc2
  rw [show (4 : ℝ) * π / 4 = 2 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc5 : Real.sin (5 * π / 4) = -Real.sqrt 2/2 ∧ Real.cos (5 * π / 4) = -Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc3
  rw [show (5 : ℝ) * π / 4 = 3 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc6 : Real.sin (6 * π / 4) = -1 ∧ Real.cos (6 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc4
  rw [show (6 : ℝ) * π / 4 = 4 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc7 : Real.sin (7 * π / 4) = -Real.sqrt 2/2 ∧ Real.cos (7 * π / 4) = Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc5
  rw [show (7 : ℝ) * π / 4 = 5 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc8 : Real.sin (8 * π / 4) = 0 ∧ Real.cos (8 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc6
  rw [show (8 : ℝ) * π / 4 = 6 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc9 : Real.sin (9 * π / 4) = Real.sqrt 2/2 ∧ Real.cos (9 * π / 4) = Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc7
  rw [show (9 : ℝ) * π / 4 = 7 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc10 : Real.sin (10 * π / 4) = 1 ∧ Real.cos (10 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc8
  rw [show (10 : ℝ) * π / 4 = 8 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc11 : Real.sin (11 * π / 4) = Real.sqrt 2/2 ∧ Real.cos (11 * π / 4) = -Real.sqrt 2/2 := by
  obtain ⟨h1, h2⟩ := sc9
  rw [show (11 : ℝ) * π / 4 = 9 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc12 : Real.sin (12 * π / 4) = 0 ∧ Real.cos (12 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc10
  rw [show (12 : ℝ) * π / 4 = 10 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem piece1 : (0.391586 : ℝ) ≤ Fk (3 * π / 8) (2 * π / 4) - Fk (3 * π / 8) (1 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc1
  obtain ⟨sb, cb⟩ := sc2
  have key : Fk (3 * π / 8) (2 * π / 4) - Fk (3 * π / 8) (1 * π / 4)
      = 2 / 3 + (1 / π) * (16*Real.sqrt 2/9 - 16/9) + (1 / π) ^ 2 * (-32*Real.sqrt 2/9) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece2 : (0.53964 : ℝ) ≤ Fk (5 * π / 8) (3 * π / 4) - Fk (5 * π / 8) (2 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc2
  obtain ⟨sb, cb⟩ := sc3
  have key : Fk (5 * π / 8) (3 * π / 4) - Fk (5 * π / 8) (2 * π / 4)
      = 2 / 5 + (1 / π) * (48/25 - 16*Real.sqrt 2/25) + (1 / π) ^ 2 * (-32*Real.sqrt 2/25) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece3 : (0.540932 : ℝ) ≤ Fk (7 * π / 8) (4 * π / 4) - Fk (7 * π / 8) (3 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc3
  obtain ⟨sb, cb⟩ := sc4
  have key : Fk (7 * π / 8) (4 * π / 4) - Fk (7 * π / 8) (3 * π / 4)
      = 2 / 7 + (1 / π) * (32*Real.sqrt 2/49) + (1 / π) ^ 2 * (32*Real.sqrt 2/49 - 64/49) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece4 : (0.423508 : ℝ) ≤ Fk (9 * π / 8) (5 * π / 4) - Fk (9 * π / 8) (4 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc4
  obtain ⟨sb, cb⟩ := sc5
  have key : Fk (9 * π / 8) (5 * π / 4) - Fk (9 * π / 8) (4 * π / 4)
      = 2 / 9 + (1 / π) * (32*Real.sqrt 2/81) + (1 / π) ^ 2 * (64/81 - 32*Real.sqrt 2/81) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece5 : (0.251588 : ℝ) ≤ Fk (11 * π / 8) (6 * π / 4) - Fk (11 * π / 8) (5 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc5
  obtain ⟨sb, cb⟩ := sc6
  have key : Fk (11 * π / 8) (6 * π / 4) - Fk (11 * π / 8) (5 * π / 4)
      = 2 / 11 + (1 / π) * (80/121 - 48*Real.sqrt 2/121) + (1 / π) ^ 2 * (32*Real.sqrt 2/121) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece6 : (0.09788 : ℝ) ≤ Fk (13 * π / 8) (7 * π / 4) - Fk (13 * π / 8) (6 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc6
  obtain ⟨sb, cb⟩ := sc7
  have key : Fk (13 * π / 8) (7 * π / 4) - Fk (13 * π / 8) (6 * π / 4)
      = 2 / 13 + (1 / π) * (48*Real.sqrt 2/169 - 112/169) + (1 / π) ^ 2 * (32*Real.sqrt 2/169) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece7 : (0.013727 : ℝ) ≤ Fk (15 * π / 8) (8 * π / 4) - Fk (15 * π / 8) (7 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc7
  obtain ⟨sb, cb⟩ := sc8
  have key : Fk (15 * π / 8) (8 * π / 4) - Fk (15 * π / 8) (7 * π / 4)
      = 2 / 15 + (1 / π) * (-64*Real.sqrt 2/225) + (1 / π) ^ 2 * (64/225 - 32*Real.sqrt 2/225) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece8 : (0.011384 : ℝ) ≤ Fk (17 * π / 8) (9 * π / 4) - Fk (17 * π / 8) (8 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc8
  obtain ⟨sb, cb⟩ := sc9
  have key : Fk (17 * π / 8) (9 * π / 4) - Fk (17 * π / 8) (8 * π / 4)
      = 2 / 17 + (1 / π) * (-64*Real.sqrt 2/289) + (1 / π) ^ 2 * (32*Real.sqrt 2/289 - 64/289) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece9 : (0.065346 : ℝ) ≤ Fk (19 * π / 8) (10 * π / 4) - Fk (19 * π / 8) (9 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc9
  obtain ⟨sb, cb⟩ := sc10
  have key : Fk (19 * π / 8) (10 * π / 4) - Fk (19 * π / 8) (9 * π / 4)
      = 2 / 19 + (1 / π) * (80*Real.sqrt 2/361 - 144/361) + (1 / π) ^ 2 * (-32*Real.sqrt 2/361) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece10 : (0.130212 : ℝ) ≤ Fk (21 * π / 8) (11 * π / 4) - Fk (21 * π / 8) (10 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc10
  obtain ⟨sb, cb⟩ := sc11
  have key : Fk (21 * π / 8) (11 * π / 4) - Fk (21 * π / 8) (10 * π / 4)
      = 2 / 21 + (1 / π) * (176/441 - 80*Real.sqrt 2/441) + (1 / π) ^ 2 * (-32*Real.sqrt 2/441) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem piece11 : (0.165056 : ℝ) ≤ Fk (23 * π / 8) (12 * π / 4) - Fk (23 * π / 8) (11 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc11
  obtain ⟨sb, cb⟩ := sc12
  have key : Fk (23 * π / 8) (12 * π / 4) - Fk (23 * π / 8) (11 * π / 4)
      = 2 / 23 + (1 / π) * (96*Real.sqrt 2/529) + (1 / π) ^ 2 * (32*Real.sqrt 2/529 - 64/529) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith
-- Cin( 1 π/2) >= 0.540836
-- Cin( 2 π/2) >= 1.621408
-- Cin( 3 π/2) >= 2.296504
-- Cin( 4 π/2) >= 2.408111
-- Cin( 5 π/2) >= 2.484841
-- Cin( 6 π/2) >= 2.780109
theorem cinc1 : (0.14925 : ℝ) ≤ Cin (1 * π / 4) := cin_quarter

theorem cinc2 : (0.540836 : ℝ) ≤ Cin (2 * π / 4) := by
  have h := cin_step (α := 1 * π / 4) (β := 2 * π / 4) (c := 3 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc1, piece1]

theorem cinc3 : (1.080476 : ℝ) ≤ Cin (3 * π / 4) := by
  have h := cin_step (α := 2 * π / 4) (β := 3 * π / 4) (c := 5 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc2, piece2]

theorem cinc4 : (1.621408 : ℝ) ≤ Cin (4 * π / 4) := by
  have h := cin_step (α := 3 * π / 4) (β := 4 * π / 4) (c := 7 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc3, piece3]

theorem cinc5 : (2.044916 : ℝ) ≤ Cin (5 * π / 4) := by
  have h := cin_step (α := 4 * π / 4) (β := 5 * π / 4) (c := 9 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc4, piece4]

theorem cinc6 : (2.296504 : ℝ) ≤ Cin (6 * π / 4) := by
  have h := cin_step (α := 5 * π / 4) (β := 6 * π / 4) (c := 11 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc5, piece5]

theorem cinc7 : (2.394384 : ℝ) ≤ Cin (7 * π / 4) := by
  have h := cin_step (α := 6 * π / 4) (β := 7 * π / 4) (c := 13 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc6, piece6]

theorem cinc8 : (2.408111 : ℝ) ≤ Cin (8 * π / 4) := by
  have h := cin_step (α := 7 * π / 4) (β := 8 * π / 4) (c := 15 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc7, piece7]

theorem cinc9 : (2.419495 : ℝ) ≤ Cin (9 * π / 4) := by
  have h := cin_step (α := 8 * π / 4) (β := 9 * π / 4) (c := 17 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc8, piece8]

theorem cinc10 : (2.484841 : ℝ) ≤ Cin (10 * π / 4) := by
  have h := cin_step (α := 9 * π / 4) (β := 10 * π / 4) (c := 19 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc9, piece9]

theorem cinc11 : (2.615053 : ℝ) ≤ Cin (11 * π / 4) := by
  have h := cin_step (α := 10 * π / 4) (β := 11 * π / 4) (c := 21 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc10, piece10]

theorem cinc12 : (2.780109 : ℝ) ≤ Cin (12 * π / 4) := by
  have h := cin_step (α := 11 * π / 4) (β := 12 * π / 4) (c := 23 * π / 8)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc11, piece11]

theorem cin_val1 : (0.5408 : ℝ) ≤ Cin (π * 1 / 2) := by
  rw [show π * (1 : ℝ) / 2 = 2 * π / 4 by ring]; linarith [cinc2]

theorem cin_val2 : (1.6214 : ℝ) ≤ Cin (π * 2 / 2) := by
  rw [show π * (2 : ℝ) / 2 = 4 * π / 4 by ring]; linarith [cinc4]

theorem cin_val3 : (2.2965 : ℝ) ≤ Cin (π * 3 / 2) := by
  rw [show π * (3 : ℝ) / 2 = 6 * π / 4 by ring]; linarith [cinc6]

theorem cin_val4 : (2.4081 : ℝ) ≤ Cin (π * 4 / 2) := by
  rw [show π * (4 : ℝ) / 2 = 8 * π / 4 by ring]; linarith [cinc8]

theorem cin_val5 : (2.4848 : ℝ) ≤ Cin (π * 5 / 2) := by
  rw [show π * (5 : ℝ) / 2 = 10 * π / 4 by ring]; linarith [cinc10]

theorem cin_val6 : (2.7801 : ℝ) ≤ Cin (π * 6 / 2) := by
  rw [show π * (6 : ℝ) / 2 = 12 * π / 4 by ring]; linarith [cinc12]
theorem sc14 : Real.sin (14 * π / 4) = -1 ∧ Real.cos (14 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc12
  rw [show (14 : ℝ) * π / 4 = 12 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc16 : Real.sin (16 * π / 4) = 0 ∧ Real.cos (16 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc14
  rw [show (16 : ℝ) * π / 4 = 14 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc18 : Real.sin (18 * π / 4) = 1 ∧ Real.cos (18 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc16
  rw [show (18 : ℝ) * π / 4 = 16 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc20 : Real.sin (20 * π / 4) = 0 ∧ Real.cos (20 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc18
  rw [show (20 : ℝ) * π / 4 = 18 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc22 : Real.sin (22 * π / 4) = -1 ∧ Real.cos (22 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc20
  rw [show (22 : ℝ) * π / 4 = 20 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc24 : Real.sin (24 * π / 4) = 0 ∧ Real.cos (24 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc22
  rw [show (24 : ℝ) * π / 4 = 22 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc26 : Real.sin (26 * π / 4) = 1 ∧ Real.cos (26 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc24
  rw [show (26 : ℝ) * π / 4 = 24 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc28 : Real.sin (28 * π / 4) = 0 ∧ Real.cos (28 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc26
  rw [show (28 : ℝ) * π / 4 = 26 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc30 : Real.sin (30 * π / 4) = -1 ∧ Real.cos (30 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc28
  rw [show (30 : ℝ) * π / 4 = 28 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc32 : Real.sin (32 * π / 4) = 0 ∧ Real.cos (32 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc30
  rw [show (32 : ℝ) * π / 4 = 30 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc34 : Real.sin (34 * π / 4) = 1 ∧ Real.cos (34 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc32
  rw [show (34 : ℝ) * π / 4 = 32 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc36 : Real.sin (36 * π / 4) = 0 ∧ Real.cos (36 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc34
  rw [show (36 : ℝ) * π / 4 = 34 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc38 : Real.sin (38 * π / 4) = -1 ∧ Real.cos (38 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc36
  rw [show (38 : ℝ) * π / 4 = 36 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc40 : Real.sin (40 * π / 4) = 0 ∧ Real.cos (40 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc38
  rw [show (40 : ℝ) * π / 4 = 38 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc42 : Real.sin (42 * π / 4) = 1 ∧ Real.cos (42 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc40
  rw [show (42 : ℝ) * π / 4 = 40 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc44 : Real.sin (44 * π / 4) = 0 ∧ Real.cos (44 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc42
  rw [show (44 : ℝ) * π / 4 = 42 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc46 : Real.sin (46 * π / 4) = -1 ∧ Real.cos (46 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc44
  rw [show (46 : ℝ) * π / 4 = 44 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc48 : Real.sin (48 * π / 4) = 0 ∧ Real.cos (48 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc46
  rw [show (48 : ℝ) * π / 4 = 46 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc50 : Real.sin (50 * π / 4) = 1 ∧ Real.cos (50 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc48
  rw [show (50 : ℝ) * π / 4 = 48 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc52 : Real.sin (52 * π / 4) = 0 ∧ Real.cos (52 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc50
  rw [show (52 : ℝ) * π / 4 = 50 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc54 : Real.sin (54 * π / 4) = -1 ∧ Real.cos (54 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc52
  rw [show (54 : ℝ) * π / 4 = 52 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc56 : Real.sin (56 * π / 4) = 0 ∧ Real.cos (56 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc54
  rw [show (56 : ℝ) * π / 4 = 54 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc58 : Real.sin (58 * π / 4) = 1 ∧ Real.cos (58 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc56
  rw [show (58 : ℝ) * π / 4 = 56 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc60 : Real.sin (60 * π / 4) = 0 ∧ Real.cos (60 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc58
  rw [show (60 : ℝ) * π / 4 = 58 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc62 : Real.sin (62 * π / 4) = -1 ∧ Real.cos (62 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc60
  rw [show (62 : ℝ) * π / 4 = 60 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc64 : Real.sin (64 * π / 4) = 0 ∧ Real.cos (64 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc62
  rw [show (64 : ℝ) * π / 4 = 62 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc66 : Real.sin (66 * π / 4) = 1 ∧ Real.cos (66 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc64
  rw [show (66 : ℝ) * π / 4 = 64 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc68 : Real.sin (68 * π / 4) = 0 ∧ Real.cos (68 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc66
  rw [show (68 : ℝ) * π / 4 = 66 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc70 : Real.sin (70 * π / 4) = -1 ∧ Real.cos (70 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc68
  rw [show (70 : ℝ) * π / 4 = 68 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc72 : Real.sin (72 * π / 4) = 0 ∧ Real.cos (72 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc70
  rw [show (72 : ℝ) * π / 4 = 70 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc74 : Real.sin (74 * π / 4) = 1 ∧ Real.cos (74 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc72
  rw [show (74 : ℝ) * π / 4 = 72 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc76 : Real.sin (76 * π / 4) = 0 ∧ Real.cos (76 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc74
  rw [show (76 : ℝ) * π / 4 = 74 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc78 : Real.sin (78 * π / 4) = -1 ∧ Real.cos (78 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc76
  rw [show (78 : ℝ) * π / 4 = 76 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc80 : Real.sin (80 * π / 4) = 0 ∧ Real.cos (80 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc78
  rw [show (80 : ℝ) * π / 4 = 78 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc82 : Real.sin (82 * π / 4) = 1 ∧ Real.cos (82 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc80
  rw [show (82 : ℝ) * π / 4 = 80 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc84 : Real.sin (84 * π / 4) = 0 ∧ Real.cos (84 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc82
  rw [show (84 : ℝ) * π / 4 = 82 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc86 : Real.sin (86 * π / 4) = -1 ∧ Real.cos (86 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc84
  rw [show (86 : ℝ) * π / 4 = 84 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc88 : Real.sin (88 * π / 4) = 0 ∧ Real.cos (88 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc86
  rw [show (88 : ℝ) * π / 4 = 86 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc90 : Real.sin (90 * π / 4) = 1 ∧ Real.cos (90 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc88
  rw [show (90 : ℝ) * π / 4 = 88 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc92 : Real.sin (92 * π / 4) = 0 ∧ Real.cos (92 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc90
  rw [show (92 : ℝ) * π / 4 = 90 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc94 : Real.sin (94 * π / 4) = -1 ∧ Real.cos (94 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc92
  rw [show (94 : ℝ) * π / 4 = 92 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc96 : Real.sin (96 * π / 4) = 0 ∧ Real.cos (96 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc94
  rw [show (96 : ℝ) * π / 4 = 94 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc98 : Real.sin (98 * π / 4) = 1 ∧ Real.cos (98 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc96
  rw [show (98 : ℝ) * π / 4 = 96 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc100 : Real.sin (100 * π / 4) = 0 ∧ Real.cos (100 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc98
  rw [show (100 : ℝ) * π / 4 = 98 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc102 : Real.sin (102 * π / 4) = -1 ∧ Real.cos (102 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc100
  rw [show (102 : ℝ) * π / 4 = 100 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc104 : Real.sin (104 * π / 4) = 0 ∧ Real.cos (104 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc102
  rw [show (104 : ℝ) * π / 4 = 102 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc106 : Real.sin (106 * π / 4) = 1 ∧ Real.cos (106 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc104
  rw [show (106 : ℝ) * π / 4 = 104 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc108 : Real.sin (108 * π / 4) = 0 ∧ Real.cos (108 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc106
  rw [show (108 : ℝ) * π / 4 = 106 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc110 : Real.sin (110 * π / 4) = -1 ∧ Real.cos (110 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc108
  rw [show (110 : ℝ) * π / 4 = 108 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc112 : Real.sin (112 * π / 4) = 0 ∧ Real.cos (112 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc110
  rw [show (112 : ℝ) * π / 4 = 110 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc114 : Real.sin (114 * π / 4) = 1 ∧ Real.cos (114 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc112
  rw [show (114 : ℝ) * π / 4 = 112 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc116 : Real.sin (116 * π / 4) = 0 ∧ Real.cos (116 * π / 4) = -1 := by
  obtain ⟨h1, h2⟩ := sc114
  rw [show (116 : ℝ) * π / 4 = 114 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc118 : Real.sin (118 * π / 4) = -1 ∧ Real.cos (118 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc116
  rw [show (118 : ℝ) * π / 4 = 116 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc120 : Real.sin (120 * π / 4) = 0 ∧ Real.cos (120 * π / 4) = 1 := by
  obtain ⟨h1, h2⟩ := sc118
  rw [show (120 : ℝ) * π / 4 = 118 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem sc122 : Real.sin (122 * π / 4) = 1 ∧ Real.cos (122 * π / 4) = 0 := by
  obtain ⟨h1, h2⟩ := sc120
  rw [show (122 : ℝ) * π / 4 = 120 * π / 4 + π / 2 by ring, Real.sin_add_pi_div_two,
    Real.cos_add_pi_div_two, h1, h2]
  constructor <;> ring

theorem pieceH6 : (0.253844 : ℝ) ≤ Fk (13 * π / 4) (14 * π / 4) - Fk (13 * π / 4) (12 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc12
  obtain ⟨sb, cb⟩ := sc14
  have key : Fk (13 * π / 4) (14 * π / 4) - Fk (13 * π / 4) (12 * π / 4)
      = 2 / 13 + (1 / π) * (48/169) + (1 / π) ^ 2 * (16/169) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH7 : (0.049994 : ℝ) ≤ Fk (15 * π / 4) (16 * π / 4) - Fk (15 * π / 4) (14 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc14
  obtain ⟨sb, cb⟩ := sc16
  have key : Fk (15 * π / 4) (16 * π / 4) - Fk (15 * π / 4) (14 * π / 4)
      = 2 / 15 + (1 / π) * (-64/225) + (1 / π) ^ 2 * (16/225) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH8 : (0.041544 : ℝ) ≤ Fk (17 * π / 4) (18 * π / 4) - Fk (17 * π / 4) (16 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc16
  obtain ⟨sb, cb⟩ := sc18
  have key : Fk (17 * π / 4) (18 * π / 4) - Fk (17 * π / 4) (16 * π / 4)
      = 2 / 17 + (1 / π) * (-64/289) + (1 / π) ^ 2 * (-16/289) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH9 : (0.17131 : ℝ) ≤ Fk (19 * π / 4) (20 * π / 4) - Fk (19 * π / 4) (18 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc18
  obtain ⟨sb, cb⟩ := sc20
  have key : Fk (19 * π / 4) (20 * π / 4) - Fk (19 * π / 4) (18 * π / 4)
      = 2 / 19 + (1 / π) * (80/361) + (1 / π) ^ 2 * (-16/361) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH10 : (0.156655 : ℝ) ≤ Fk (21 * π / 4) (22 * π / 4) - Fk (21 * π / 4) (20 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc20
  obtain ⟨sb, cb⟩ := sc22
  have key : Fk (21 * π / 4) (22 * π / 4) - Fk (21 * π / 4) (20 * π / 4)
      = 2 / 21 + (1 / π) * (80/441) + (1 / π) ^ 2 * (16/441) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH11 : (0.032253 : ℝ) ≤ Fk (23 * π / 4) (24 * π / 4) - Fk (23 * π / 4) (22 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc22
  obtain ⟨sb, cb⟩ := sc24
  have key : Fk (23 * π / 4) (24 * π / 4) - Fk (23 * π / 4) (22 * π / 4)
      = 2 / 23 + (1 / π) * (-96/529) + (1 / π) ^ 2 * (16/529) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH12 : (0.028511 : ℝ) ≤ Fk (25 * π / 4) (26 * π / 4) - Fk (25 * π / 4) (24 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc24
  obtain ⟨sb, cb⟩ := sc26
  have key : Fk (25 * π / 4) (26 * π / 4) - Fk (25 * π / 4) (24 * π / 4)
      = 2 / 25 + (1 / π) * (-96/625) + (1 / π) ^ 2 * (-16/625) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH13 : (0.120751 : ℝ) ≤ Fk (27 * π / 4) (28 * π / 4) - Fk (27 * π / 4) (26 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc26
  obtain ⟨sb, cb⟩ := sc28
  have key : Fk (27 * π / 4) (28 * π / 4) - Fk (27 * π / 4) (26 * π / 4)
      = 2 / 27 + (1 / π) * (112/729) + (1 / π) ^ 2 * (-16/729) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH14 : (0.113282 : ℝ) ≤ Fk (29 * π / 4) (30 * π / 4) - Fk (29 * π / 4) (28 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc28
  obtain ⟨sb, cb⟩ := sc30
  have key : Fk (29 * π / 4) (30 * π / 4) - Fk (29 * π / 4) (28 * π / 4)
      = 2 / 29 + (1 / π) * (112/841) + (1 / π) ^ 2 * (16/841) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH15 : (0.023803 : ℝ) ≤ Fk (31 * π / 4) (32 * π / 4) - Fk (31 * π / 4) (30 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc30
  obtain ⟨sb, cb⟩ := sc32
  have key : Fk (31 * π / 4) (32 * π / 4) - Fk (31 * π / 4) (30 * π / 4)
      = 2 / 31 + (1 / π) * (-128/961) + (1 / π) ^ 2 * (16/961) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH16 : (0.021701 : ℝ) ≤ Fk (33 * π / 4) (34 * π / 4) - Fk (33 * π / 4) (32 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc32
  obtain ⟨sb, cb⟩ := sc34
  have key : Fk (33 * π / 4) (34 * π / 4) - Fk (33 * π / 4) (32 * π / 4)
      = 2 / 33 + (1 / π) * (-128/1089) + (1 / π) ^ 2 * (-16/1089) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH17 : (0.093235 : ℝ) ≤ Fk (35 * π / 4) (36 * π / 4) - Fk (35 * π / 4) (34 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc34
  obtain ⟨sb, cb⟩ := sc36
  have key : Fk (35 * π / 4) (36 * π / 4) - Fk (35 * π / 4) (34 * π / 4)
      = 2 / 35 + (1 / π) * (144/1225) + (1 / π) ^ 2 * (-16/1225) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH18 : (0.088718 : ℝ) ≤ Fk (37 * π / 4) (38 * π / 4) - Fk (37 * π / 4) (36 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc36
  obtain ⟨sb, cb⟩ := sc38
  have key : Fk (37 * π / 4) (38 * π / 4) - Fk (37 * π / 4) (36 * π / 4)
      = 2 / 37 + (1 / π) * (144/1369) + (1 / π) ^ 2 * (16/1369) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH19 : (0.018861 : ℝ) ≤ Fk (39 * π / 4) (40 * π / 4) - Fk (39 * π / 4) (38 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc38
  obtain ⟨sb, cb⟩ := sc40
  have key : Fk (39 * π / 4) (40 * π / 4) - Fk (39 * π / 4) (38 * π / 4)
      = 2 / 39 + (1 / π) * (-160/1521) + (1 / π) ^ 2 * (16/1521) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH20 : (0.017516 : ℝ) ≤ Fk (41 * π / 4) (42 * π / 4) - Fk (41 * π / 4) (40 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc40
  obtain ⟨sb, cb⟩ := sc42
  have key : Fk (41 * π / 4) (42 * π / 4) - Fk (41 * π / 4) (40 * π / 4)
      = 2 / 41 + (1 / π) * (-160/1681) + (1 / π) ^ 2 * (-16/1681) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH21 : (0.075931 : ℝ) ≤ Fk (43 * π / 4) (44 * π / 4) - Fk (43 * π / 4) (42 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc42
  obtain ⟨sb, cb⟩ := sc44
  have key : Fk (43 * π / 4) (44 * π / 4) - Fk (43 * π / 4) (42 * π / 4)
      = 2 / 43 + (1 / π) * (176/1849) + (1 / π) ^ 2 * (-16/1849) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH22 : (0.072908 : ℝ) ≤ Fk (45 * π / 4) (46 * π / 4) - Fk (45 * π / 4) (44 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc44
  obtain ⟨sb, cb⟩ := sc46
  have key : Fk (45 * π / 4) (46 * π / 4) - Fk (45 * π / 4) (44 * π / 4)
      = 2 / 45 + (1 / π) * (176/2025) + (1 / π) ^ 2 * (16/2025) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH23 : (0.015618 : ℝ) ≤ Fk (47 * π / 4) (48 * π / 4) - Fk (47 * π / 4) (46 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc46
  obtain ⟨sb, cb⟩ := sc48
  have key : Fk (47 * π / 4) (48 * π / 4) - Fk (47 * π / 4) (46 * π / 4)
      = 2 / 47 + (1 / π) * (-192/2209) + (1 / π) ^ 2 * (16/2209) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH24 : (0.014684 : ℝ) ≤ Fk (49 * π / 4) (50 * π / 4) - Fk (49 * π / 4) (48 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc48
  obtain ⟨sb, cb⟩ := sc50
  have key : Fk (49 * π / 4) (50 * π / 4) - Fk (49 * π / 4) (48 * π / 4)
      = 2 / 49 + (1 / π) * (-192/2401) + (1 / π) ^ 2 * (-16/2401) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH25 : (0.064045 : ℝ) ≤ Fk (51 * π / 4) (52 * π / 4) - Fk (51 * π / 4) (50 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc50
  obtain ⟨sb, cb⟩ := sc52
  have key : Fk (51 * π / 4) (52 * π / 4) - Fk (51 * π / 4) (50 * π / 4)
      = 2 / 51 + (1 / π) * (208/2601) + (1 / π) ^ 2 * (-16/2601) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH26 : (0.061881 : ℝ) ≤ Fk (53 * π / 4) (54 * π / 4) - Fk (53 * π / 4) (52 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc52
  obtain ⟨sb, cb⟩ := sc54
  have key : Fk (53 * π / 4) (54 * π / 4) - Fk (53 * π / 4) (52 * π / 4)
      = 2 / 53 + (1 / π) * (208/2809) + (1 / π) ^ 2 * (16/2809) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH27 : (0.013326 : ℝ) ≤ Fk (55 * π / 4) (56 * π / 4) - Fk (55 * π / 4) (54 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc54
  obtain ⟨sb, cb⟩ := sc56
  have key : Fk (55 * π / 4) (56 * π / 4) - Fk (55 * π / 4) (54 * π / 4)
      = 2 / 55 + (1 / π) * (-224/3025) + (1 / π) ^ 2 * (16/3025) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH28 : (0.012641 : ℝ) ≤ Fk (57 * π / 4) (58 * π / 4) - Fk (57 * π / 4) (56 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc56
  obtain ⟨sb, cb⟩ := sc58
  have key : Fk (57 * π / 4) (58 * π / 4) - Fk (57 * π / 4) (56 * π / 4)
      = 2 / 57 + (1 / π) * (-224/3249) + (1 / π) ^ 2 * (-16/3249) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH29 : (0.055376 : ℝ) ≤ Fk (59 * π / 4) (60 * π / 4) - Fk (59 * π / 4) (58 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc58
  obtain ⟨sb, cb⟩ := sc60
  have key : Fk (59 * π / 4) (60 * π / 4) - Fk (59 * π / 4) (58 * π / 4)
      = 2 / 59 + (1 / π) * (240/3481) + (1 / π) ^ 2 * (-16/3481) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH30 : (0.053751 : ℝ) ≤ Fk (61 * π / 4) (62 * π / 4) - Fk (61 * π / 4) (60 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc60
  obtain ⟨sb, cb⟩ := sc62
  have key : Fk (61 * π / 4) (62 * π / 4) - Fk (61 * π / 4) (60 * π / 4)
      = 2 / 61 + (1 / π) * (240/3721) + (1 / π) ^ 2 * (16/3721) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH31 : (0.011621 : ℝ) ≤ Fk (63 * π / 4) (64 * π / 4) - Fk (63 * π / 4) (62 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc62
  obtain ⟨sb, cb⟩ := sc64
  have key : Fk (63 * π / 4) (64 * π / 4) - Fk (63 * π / 4) (62 * π / 4)
      = 2 / 63 + (1 / π) * (-256/3969) + (1 / π) ^ 2 * (16/3969) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH32 : (0.011096 : ℝ) ≤ Fk (65 * π / 4) (66 * π / 4) - Fk (65 * π / 4) (64 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc64
  obtain ⟨sb, cb⟩ := sc66
  have key : Fk (65 * π / 4) (66 * π / 4) - Fk (65 * π / 4) (64 * π / 4)
      = 2 / 65 + (1 / π) * (-256/4225) + (1 / π) ^ 2 * (-16/4225) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH33 : (0.048774 : ℝ) ≤ Fk (67 * π / 4) (68 * π / 4) - Fk (67 * π / 4) (66 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc66
  obtain ⟨sb, cb⟩ := sc68
  have key : Fk (67 * π / 4) (68 * π / 4) - Fk (67 * π / 4) (66 * π / 4)
      = 2 / 67 + (1 / π) * (272/4489) + (1 / π) ^ 2 * (-16/4489) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH34 : (0.047509 : ℝ) ≤ Fk (69 * π / 4) (70 * π / 4) - Fk (69 * π / 4) (68 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc68
  obtain ⟨sb, cb⟩ := sc70
  have key : Fk (69 * π / 4) (70 * π / 4) - Fk (69 * π / 4) (68 * π / 4)
      = 2 / 69 + (1 / π) * (272/4761) + (1 / π) ^ 2 * (16/4761) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH35 : (0.010303 : ℝ) ≤ Fk (71 * π / 4) (72 * π / 4) - Fk (71 * π / 4) (70 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc70
  obtain ⟨sb, cb⟩ := sc72
  have key : Fk (71 * π / 4) (72 * π / 4) - Fk (71 * π / 4) (70 * π / 4)
      = 2 / 71 + (1 / π) * (-288/5041) + (1 / π) ^ 2 * (16/5041) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH36 : (0.009888 : ℝ) ≤ Fk (73 * π / 4) (74 * π / 4) - Fk (73 * π / 4) (72 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc72
  obtain ⟨sb, cb⟩ := sc74
  have key : Fk (73 * π / 4) (74 * π / 4) - Fk (73 * π / 4) (72 * π / 4)
      = 2 / 73 + (1 / π) * (-288/5329) + (1 / π) ^ 2 * (-16/5329) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH37 : (0.043579 : ℝ) ≤ Fk (75 * π / 4) (76 * π / 4) - Fk (75 * π / 4) (74 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc74
  obtain ⟨sb, cb⟩ := sc76
  have key : Fk (75 * π / 4) (76 * π / 4) - Fk (75 * π / 4) (74 * π / 4)
      = 2 / 75 + (1 / π) * (304/5625) + (1 / π) ^ 2 * (-16/5625) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH38 : (0.042566 : ℝ) ≤ Fk (77 * π / 4) (78 * π / 4) - Fk (77 * π / 4) (76 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc76
  obtain ⟨sb, cb⟩ := sc78
  have key : Fk (77 * π / 4) (78 * π / 4) - Fk (77 * π / 4) (76 * π / 4)
      = 2 / 77 + (1 / π) * (304/5929) + (1 / π) ^ 2 * (16/5929) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH39 : (0.009253 : ℝ) ≤ Fk (79 * π / 4) (80 * π / 4) - Fk (79 * π / 4) (78 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc78
  obtain ⟨sb, cb⟩ := sc80
  have key : Fk (79 * π / 4) (80 * π / 4) - Fk (79 * π / 4) (78 * π / 4)
      = 2 / 79 + (1 / π) * (-320/6241) + (1 / π) ^ 2 * (16/6241) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH40 : (0.008917 : ℝ) ≤ Fk (81 * π / 4) (82 * π / 4) - Fk (81 * π / 4) (80 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc80
  obtain ⟨sb, cb⟩ := sc82
  have key : Fk (81 * π / 4) (82 * π / 4) - Fk (81 * π / 4) (80 * π / 4)
      = 2 / 81 + (1 / π) * (-320/6561) + (1 / π) ^ 2 * (-16/6561) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH41 : (0.039384 : ℝ) ≤ Fk (83 * π / 4) (84 * π / 4) - Fk (83 * π / 4) (82 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc82
  obtain ⟨sb, cb⟩ := sc84
  have key : Fk (83 * π / 4) (84 * π / 4) - Fk (83 * π / 4) (82 * π / 4)
      = 2 / 83 + (1 / π) * (336/6889) + (1 / π) ^ 2 * (-16/6889) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH42 : (0.038554 : ℝ) ≤ Fk (85 * π / 4) (86 * π / 4) - Fk (85 * π / 4) (84 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc84
  obtain ⟨sb, cb⟩ := sc86
  have key : Fk (85 * π / 4) (86 * π / 4) - Fk (85 * π / 4) (84 * π / 4)
      = 2 / 85 + (1 / π) * (336/7225) + (1 / π) ^ 2 * (16/7225) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH43 : (0.008397 : ℝ) ≤ Fk (87 * π / 4) (88 * π / 4) - Fk (87 * π / 4) (86 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc86
  obtain ⟨sb, cb⟩ := sc88
  have key : Fk (87 * π / 4) (88 * π / 4) - Fk (87 * π / 4) (86 * π / 4)
      = 2 / 87 + (1 / π) * (-352/7569) + (1 / π) ^ 2 * (16/7569) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH44 : (0.008119 : ℝ) ≤ Fk (89 * π / 4) (90 * π / 4) - Fk (89 * π / 4) (88 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc88
  obtain ⟨sb, cb⟩ := sc90
  have key : Fk (89 * π / 4) (90 * π / 4) - Fk (89 * π / 4) (88 * π / 4)
      = 2 / 89 + (1 / π) * (-352/7921) + (1 / π) ^ 2 * (-16/7921) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH45 : (0.035925 : ℝ) ≤ Fk (91 * π / 4) (92 * π / 4) - Fk (91 * π / 4) (90 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc90
  obtain ⟨sb, cb⟩ := sc92
  have key : Fk (91 * π / 4) (92 * π / 4) - Fk (91 * π / 4) (90 * π / 4)
      = 2 / 91 + (1 / π) * (368/8281) + (1 / π) ^ 2 * (-16/8281) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH46 : (0.035234 : ℝ) ≤ Fk (93 * π / 4) (94 * π / 4) - Fk (93 * π / 4) (92 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc92
  obtain ⟨sb, cb⟩ := sc94
  have key : Fk (93 * π / 4) (94 * π / 4) - Fk (93 * π / 4) (92 * π / 4)
      = 2 / 93 + (1 / π) * (368/8649) + (1 / π) ^ 2 * (16/8649) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH47 : (0.007686 : ℝ) ≤ Fk (95 * π / 4) (96 * π / 4) - Fk (95 * π / 4) (94 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc94
  obtain ⟨sb, cb⟩ := sc96
  have key : Fk (95 * π / 4) (96 * π / 4) - Fk (95 * π / 4) (94 * π / 4)
      = 2 / 95 + (1 / π) * (-384/9025) + (1 / π) ^ 2 * (16/9025) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH48 : (0.007453 : ℝ) ≤ Fk (97 * π / 4) (98 * π / 4) - Fk (97 * π / 4) (96 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc96
  obtain ⟨sb, cb⟩ := sc98
  have key : Fk (97 * π / 4) (98 * π / 4) - Fk (97 * π / 4) (96 * π / 4)
      = 2 / 97 + (1 / π) * (-384/9409) + (1 / π) ^ 2 * (-16/9409) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH49 : (0.033025 : ℝ) ≤ Fk (99 * π / 4) (100 * π / 4) - Fk (99 * π / 4) (98 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc98
  obtain ⟨sb, cb⟩ := sc100
  have key : Fk (99 * π / 4) (100 * π / 4) - Fk (99 * π / 4) (98 * π / 4)
      = 2 / 99 + (1 / π) * (400/9801) + (1 / π) ^ 2 * (-16/9801) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH50 : (0.03244 : ℝ) ≤ Fk (101 * π / 4) (102 * π / 4) - Fk (101 * π / 4) (100 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc100
  obtain ⟨sb, cb⟩ := sc102
  have key : Fk (101 * π / 4) (102 * π / 4) - Fk (101 * π / 4) (100 * π / 4)
      = 2 / 101 + (1 / π) * (400/10201) + (1 / π) ^ 2 * (16/10201) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH51 : (0.007086 : ℝ) ≤ Fk (103 * π / 4) (104 * π / 4) - Fk (103 * π / 4) (102 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc102
  obtain ⟨sb, cb⟩ := sc104
  have key : Fk (103 * π / 4) (104 * π / 4) - Fk (103 * π / 4) (102 * π / 4)
      = 2 / 103 + (1 / π) * (-416/10609) + (1 / π) ^ 2 * (16/10609) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH52 : (0.006887 : ℝ) ≤ Fk (105 * π / 4) (106 * π / 4) - Fk (105 * π / 4) (104 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc104
  obtain ⟨sb, cb⟩ := sc106
  have key : Fk (105 * π / 4) (106 * π / 4) - Fk (105 * π / 4) (104 * π / 4)
      = 2 / 105 + (1 / π) * (-416/11025) + (1 / π) ^ 2 * (-16/11025) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH53 : (0.030558 : ℝ) ≤ Fk (107 * π / 4) (108 * π / 4) - Fk (107 * π / 4) (106 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc106
  obtain ⟨sb, cb⟩ := sc108
  have key : Fk (107 * π / 4) (108 * π / 4) - Fk (107 * π / 4) (106 * π / 4)
      = 2 / 107 + (1 / π) * (432/11449) + (1 / π) ^ 2 * (-16/11449) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH54 : (0.030057 : ℝ) ≤ Fk (109 * π / 4) (110 * π / 4) - Fk (109 * π / 4) (108 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc108
  obtain ⟨sb, cb⟩ := sc110
  have key : Fk (109 * π / 4) (110 * π / 4) - Fk (109 * π / 4) (108 * π / 4)
      = 2 / 109 + (1 / π) * (432/11881) + (1 / π) ^ 2 * (16/11881) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH55 : (0.006573 : ℝ) ≤ Fk (111 * π / 4) (112 * π / 4) - Fk (111 * π / 4) (110 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc110
  obtain ⟨sb, cb⟩ := sc112
  have key : Fk (111 * π / 4) (112 * π / 4) - Fk (111 * π / 4) (110 * π / 4)
      = 2 / 111 + (1 / π) * (-448/12321) + (1 / π) ^ 2 * (16/12321) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH56 : (0.006402 : ℝ) ≤ Fk (113 * π / 4) (114 * π / 4) - Fk (113 * π / 4) (112 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc112
  obtain ⟨sb, cb⟩ := sc114
  have key : Fk (113 * π / 4) (114 * π / 4) - Fk (113 * π / 4) (112 * π / 4)
      = 2 / 113 + (1 / π) * (-448/12769) + (1 / π) ^ 2 * (-16/12769) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH57 : (0.028434 : ℝ) ≤ Fk (115 * π / 4) (116 * π / 4) - Fk (115 * π / 4) (114 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc114
  obtain ⟨sb, cb⟩ := sc116
  have key : Fk (115 * π / 4) (116 * π / 4) - Fk (115 * π / 4) (114 * π / 4)
      = 2 / 115 + (1 / π) * (464/13225) + (1 / π) ^ 2 * (-16/13225) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH58 : (0.027999 : ℝ) ≤ Fk (117 * π / 4) (118 * π / 4) - Fk (117 * π / 4) (116 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc116
  obtain ⟨sb, cb⟩ := sc118
  have key : Fk (117 * π / 4) (118 * π / 4) - Fk (117 * π / 4) (116 * π / 4)
      = 2 / 117 + (1 / π) * (464/13689) + (1 / π) ^ 2 * (16/13689) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH59 : (0.006129 : ℝ) ≤ Fk (119 * π / 4) (120 * π / 4) - Fk (119 * π / 4) (118 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc118
  obtain ⟨sb, cb⟩ := sc120
  have key : Fk (119 * π / 4) (120 * π / 4) - Fk (119 * π / 4) (118 * π / 4)
      = 2 / 119 + (1 / π) * (-480/14161) + (1 / π) ^ 2 * (16/14161) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pieceH60 : (0.00598 : ℝ) ≤ Fk (121 * π / 4) (122 * π / 4) - Fk (121 * π / 4) (120 * π / 4) := by
  obtain ⟨sa, ca⟩ := sc120
  obtain ⟨sb, cb⟩ := sc122
  have key : Fk (121 * π / 4) (122 * π / 4) - Fk (121 * π / 4) (120 * π / 4)
      = 2 / 121 + (1 / π) * (-480/14641) + (1 / π) ^ 2 * (-16/14641) := by
    unfold Fk; rw [sa, ca, sb, cb]; field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem cinH7 : (3.033953 : ℝ) ≤ Cin (14 * π / 4) := by
  have h := cin_step (α := 12 * π / 4) (β := 14 * π / 4) (c := 13 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinc12, pieceH6]

theorem cinH8 : (3.083947 : ℝ) ≤ Cin (16 * π / 4) := by
  have h := cin_step (α := 14 * π / 4) (β := 16 * π / 4) (c := 15 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH7, pieceH7]

theorem cinH9 : (3.125491 : ℝ) ≤ Cin (18 * π / 4) := by
  have h := cin_step (α := 16 * π / 4) (β := 18 * π / 4) (c := 17 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH8, pieceH8]

theorem cinH10 : (3.296801 : ℝ) ≤ Cin (20 * π / 4) := by
  have h := cin_step (α := 18 * π / 4) (β := 20 * π / 4) (c := 19 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH9, pieceH9]

theorem cinH11 : (3.453456 : ℝ) ≤ Cin (22 * π / 4) := by
  have h := cin_step (α := 20 * π / 4) (β := 22 * π / 4) (c := 21 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH10, pieceH10]

theorem cinH12 : (3.485709 : ℝ) ≤ Cin (24 * π / 4) := by
  have h := cin_step (α := 22 * π / 4) (β := 24 * π / 4) (c := 23 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH11, pieceH11]

theorem cinH13 : (3.51422 : ℝ) ≤ Cin (26 * π / 4) := by
  have h := cin_step (α := 24 * π / 4) (β := 26 * π / 4) (c := 25 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH12, pieceH12]

theorem cinH14 : (3.634971 : ℝ) ≤ Cin (28 * π / 4) := by
  have h := cin_step (α := 26 * π / 4) (β := 28 * π / 4) (c := 27 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH13, pieceH13]

theorem cinH15 : (3.748253 : ℝ) ≤ Cin (30 * π / 4) := by
  have h := cin_step (α := 28 * π / 4) (β := 30 * π / 4) (c := 29 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH14, pieceH14]

theorem cinH16 : (3.772056 : ℝ) ≤ Cin (32 * π / 4) := by
  have h := cin_step (α := 30 * π / 4) (β := 32 * π / 4) (c := 31 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH15, pieceH15]

theorem cinH17 : (3.793757 : ℝ) ≤ Cin (34 * π / 4) := by
  have h := cin_step (α := 32 * π / 4) (β := 34 * π / 4) (c := 33 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH16, pieceH16]

theorem cinH18 : (3.886992 : ℝ) ≤ Cin (36 * π / 4) := by
  have h := cin_step (α := 34 * π / 4) (β := 36 * π / 4) (c := 35 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH17, pieceH17]

theorem cinH19 : (3.97571 : ℝ) ≤ Cin (38 * π / 4) := by
  have h := cin_step (α := 36 * π / 4) (β := 38 * π / 4) (c := 37 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH18, pieceH18]

theorem cinH20 : (3.994571 : ℝ) ≤ Cin (40 * π / 4) := by
  have h := cin_step (α := 38 * π / 4) (β := 40 * π / 4) (c := 39 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH19, pieceH19]

theorem cinH21 : (4.012087 : ℝ) ≤ Cin (42 * π / 4) := by
  have h := cin_step (α := 40 * π / 4) (β := 42 * π / 4) (c := 41 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH20, pieceH20]

theorem cinH22 : (4.088018 : ℝ) ≤ Cin (44 * π / 4) := by
  have h := cin_step (α := 42 * π / 4) (β := 44 * π / 4) (c := 43 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH21, pieceH21]

theorem cinH23 : (4.160926 : ℝ) ≤ Cin (46 * π / 4) := by
  have h := cin_step (α := 44 * π / 4) (β := 46 * π / 4) (c := 45 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH22, pieceH22]

theorem cinH24 : (4.176544 : ℝ) ≤ Cin (48 * π / 4) := by
  have h := cin_step (α := 46 * π / 4) (β := 48 * π / 4) (c := 47 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH23, pieceH23]

theorem cinH25 : (4.191228 : ℝ) ≤ Cin (50 * π / 4) := by
  have h := cin_step (α := 48 * π / 4) (β := 50 * π / 4) (c := 49 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH24, pieceH24]

theorem cinH26 : (4.255273 : ℝ) ≤ Cin (52 * π / 4) := by
  have h := cin_step (α := 50 * π / 4) (β := 52 * π / 4) (c := 51 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH25, pieceH25]

theorem cinH27 : (4.317154 : ℝ) ≤ Cin (54 * π / 4) := by
  have h := cin_step (α := 52 * π / 4) (β := 54 * π / 4) (c := 53 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH26, pieceH26]

theorem cinH28 : (4.33048 : ℝ) ≤ Cin (56 * π / 4) := by
  have h := cin_step (α := 54 * π / 4) (β := 56 * π / 4) (c := 55 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH27, pieceH27]

theorem cinH29 : (4.343121 : ℝ) ≤ Cin (58 * π / 4) := by
  have h := cin_step (α := 56 * π / 4) (β := 58 * π / 4) (c := 57 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH28, pieceH28]

theorem cinH30 : (4.398497 : ℝ) ≤ Cin (60 * π / 4) := by
  have h := cin_step (α := 58 * π / 4) (β := 60 * π / 4) (c := 59 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH29, pieceH29]

theorem cinH31 : (4.452248 : ℝ) ≤ Cin (62 * π / 4) := by
  have h := cin_step (α := 60 * π / 4) (β := 62 * π / 4) (c := 61 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH30, pieceH30]

theorem cinH32 : (4.463869 : ℝ) ≤ Cin (64 * π / 4) := by
  have h := cin_step (α := 62 * π / 4) (β := 64 * π / 4) (c := 63 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH31, pieceH31]

theorem cinH33 : (4.474965 : ℝ) ≤ Cin (66 * π / 4) := by
  have h := cin_step (α := 64 * π / 4) (β := 66 * π / 4) (c := 65 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH32, pieceH32]

theorem cinH34 : (4.523739 : ℝ) ≤ Cin (68 * π / 4) := by
  have h := cin_step (α := 66 * π / 4) (β := 68 * π / 4) (c := 67 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH33, pieceH33]

theorem cinH35 : (4.571248 : ℝ) ≤ Cin (70 * π / 4) := by
  have h := cin_step (α := 68 * π / 4) (β := 70 * π / 4) (c := 69 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH34, pieceH34]

theorem cinH36 : (4.581551 : ℝ) ≤ Cin (72 * π / 4) := by
  have h := cin_step (α := 70 * π / 4) (β := 72 * π / 4) (c := 71 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH35, pieceH35]

theorem cinH37 : (4.591439 : ℝ) ≤ Cin (74 * π / 4) := by
  have h := cin_step (α := 72 * π / 4) (β := 74 * π / 4) (c := 73 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH36, pieceH36]

theorem cinH38 : (4.635018 : ℝ) ≤ Cin (76 * π / 4) := by
  have h := cin_step (α := 74 * π / 4) (β := 76 * π / 4) (c := 75 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH37, pieceH37]

theorem cinH39 : (4.677584 : ℝ) ≤ Cin (78 * π / 4) := by
  have h := cin_step (α := 76 * π / 4) (β := 78 * π / 4) (c := 77 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH38, pieceH38]

theorem cinH40 : (4.686837 : ℝ) ≤ Cin (80 * π / 4) := by
  have h := cin_step (α := 78 * π / 4) (β := 80 * π / 4) (c := 79 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH39, pieceH39]

theorem cinH41 : (4.695754 : ℝ) ≤ Cin (82 * π / 4) := by
  have h := cin_step (α := 80 * π / 4) (β := 82 * π / 4) (c := 81 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH40, pieceH40]

theorem cinH42 : (4.735138 : ℝ) ≤ Cin (84 * π / 4) := by
  have h := cin_step (α := 82 * π / 4) (β := 84 * π / 4) (c := 83 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH41, pieceH41]

theorem cinH43 : (4.773692 : ℝ) ≤ Cin (86 * π / 4) := by
  have h := cin_step (α := 84 * π / 4) (β := 86 * π / 4) (c := 85 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH42, pieceH42]

theorem cinH44 : (4.782089 : ℝ) ≤ Cin (88 * π / 4) := by
  have h := cin_step (α := 86 * π / 4) (β := 88 * π / 4) (c := 87 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH43, pieceH43]

theorem cinH45 : (4.790208 : ℝ) ≤ Cin (90 * π / 4) := by
  have h := cin_step (α := 88 * π / 4) (β := 90 * π / 4) (c := 89 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH44, pieceH44]

theorem cinH46 : (4.826133 : ℝ) ≤ Cin (92 * π / 4) := by
  have h := cin_step (α := 90 * π / 4) (β := 92 * π / 4) (c := 91 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH45, pieceH45]

theorem cinH47 : (4.861367 : ℝ) ≤ Cin (94 * π / 4) := by
  have h := cin_step (α := 92 * π / 4) (β := 94 * π / 4) (c := 93 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH46, pieceH46]

theorem cinH48 : (4.869053 : ℝ) ≤ Cin (96 * π / 4) := by
  have h := cin_step (α := 94 * π / 4) (β := 96 * π / 4) (c := 95 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH47, pieceH47]

theorem cinH49 : (4.876506 : ℝ) ≤ Cin (98 * π / 4) := by
  have h := cin_step (α := 96 * π / 4) (β := 98 * π / 4) (c := 97 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH48, pieceH48]

theorem cinH50 : (4.909531 : ℝ) ≤ Cin (100 * π / 4) := by
  have h := cin_step (α := 98 * π / 4) (β := 100 * π / 4) (c := 99 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH49, pieceH49]

theorem cinH51 : (4.941971 : ℝ) ≤ Cin (102 * π / 4) := by
  have h := cin_step (α := 100 * π / 4) (β := 102 * π / 4) (c := 101 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH50, pieceH50]

theorem cinH52 : (4.949057 : ℝ) ≤ Cin (104 * π / 4) := by
  have h := cin_step (α := 102 * π / 4) (β := 104 * π / 4) (c := 103 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH51, pieceH51]

theorem cinH53 : (4.955944 : ℝ) ≤ Cin (106 * π / 4) := by
  have h := cin_step (α := 104 * π / 4) (β := 106 * π / 4) (c := 105 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH52, pieceH52]

theorem cinH54 : (4.986502 : ℝ) ≤ Cin (108 * π / 4) := by
  have h := cin_step (α := 106 * π / 4) (β := 108 * π / 4) (c := 107 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH53, pieceH53]

theorem cinH55 : (5.016559 : ℝ) ≤ Cin (110 * π / 4) := by
  have h := cin_step (α := 108 * π / 4) (β := 110 * π / 4) (c := 109 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH54, pieceH54]

theorem cinH56 : (5.023132 : ℝ) ≤ Cin (112 * π / 4) := by
  have h := cin_step (α := 110 * π / 4) (β := 112 * π / 4) (c := 111 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH55, pieceH55]

theorem cinH57 : (5.029534 : ℝ) ≤ Cin (114 * π / 4) := by
  have h := cin_step (α := 112 * π / 4) (β := 114 * π / 4) (c := 113 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH56, pieceH56]

theorem cinH58 : (5.057968 : ℝ) ≤ Cin (116 * π / 4) := by
  have h := cin_step (α := 114 * π / 4) (β := 116 * π / 4) (c := 115 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH57, pieceH57]

theorem cinH59 : (5.085967 : ℝ) ≤ Cin (118 * π / 4) := by
  have h := cin_step (α := 116 * π / 4) (β := 118 * π / 4) (c := 117 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH58, pieceH58]

theorem cinH60 : (5.092096 : ℝ) ≤ Cin (120 * π / 4) := by
  have h := cin_step (α := 118 * π / 4) (β := 120 * π / 4) (c := 119 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH59, pieceH59]

theorem cinH61 : (5.098076 : ℝ) ≤ Cin (122 * π / 4) := by
  have h := cin_step (α := 120 * π / 4) (β := 122 * π / 4) (c := 121 * π / 4)
    (by positivity) (by linarith [Real.pi_pos]) (by positivity)
  linarith [cinH60, pieceH60]

/-! ## E. The mode masses -/

theorem integrable_mul₂ {f h : ℝ → ℝ} (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    Integrable (fun t => f t * h t) := by
  simpa using integrable_mul_shift₂ hf hh 0

/-- A quadratic `A s² − 2Bs + C ≥ 0` for all `s`, with `A ≥ 0`, has `B² ≤ AC`. -/
theorem disc_le {A B C : ℝ} (hA : 0 ≤ A) (h : ∀ s : ℝ, 0 ≤ A * s ^ 2 - 2 * B * s + C) :
    B ^ 2 ≤ A * C := by
  rcases hA.lt_or_eq with hA | hA
  · have := h (B / A)
    have e : A * (B / A) ^ 2 - 2 * B * (B / A) + C = C - B ^ 2 / A := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hA] at this
    linarith
  · subst hA
    have hC : 0 ≤ C := by simpa using h 0
    by_contra hB
    have hB0 : B ≠ 0 := by intro h0; apply hB; rw [h0]; simp
    have := h ((C + 1) / (2 * B))
    have e : 0 * ((C + 1) / (2 * B)) ^ 2 - 2 * B * ((C + 1) / (2 * B)) + C = -1 := by
      field_simp; ring
    linarith

/-- **Cauchy–Schwarz against a continuous function on `[−a, a]`.** -/
theorem cs_supp {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) {h : ℝ → ℝ} (hh : Continuous h) :
    (∫ t, g t * h t) ^ 2 ≤ normSq g * ∫ t in (-a)..a, h t ^ 2 := by
  set hI := (Icc (-a) a).indicator h with hhI
  have hmem : MemLp hI 2 volume := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -a) (b := a)).exists_bound_of_continuousOn
      hh.continuousOn
    exact memLp_indicator_of_continuous hh measurableSet_Icc measure_Icc_lt_top.ne
      (C := C) fun x hx => by simpa [Real.norm_eq_abs] using hC x hx
  have e1 : (∫ t, g t * h t) = ∫ t, g t * hI t := by
    congr 1; funext t
    by_cases ht : t ∈ Icc (-a) a
    · simp [hhI, ht]
    · have : a < |t| := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with h' | h'
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h'
      simp [hp.supp t this]
  have e2 : (∫ t in (-a)..a, h t ^ 2) = ∫ t, hI t ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    congr 1; funext t
    by_cases ht : t ∈ Icc (-a) a <;> simp [hhI, ht]
  rw [e1, e2]
  have iG := hp.memL2.integrable_sq
  have iH := hmem.integrable_sq
  have iGH := integrable_mul₂ hp.memL2 hmem
  refine disc_le (normSq_nonneg g) fun s => ?_
  have hq : 0 ≤ ∫ t, (s * g t - hI t) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have e3 : (∫ t, (s * g t - hI t) ^ 2)
      = normSq g * s ^ 2 - 2 * (∫ t, g t * hI t) * s + ∫ t, hI t ^ 2 := by
    have i1 : Integrable (fun t => s ^ 2 * g t ^ 2) := iG.const_mul _
    have i2 : Integrable (fun t => 2 * s * (g t * hI t)) := iGH.const_mul _
    have i3 : Integrable (fun t => s ^ 2 * g t ^ 2 - 2 * s * (g t * hI t)) := i1.sub i2
    have ef : (fun t => (s * g t - hI t) ^ 2)
        = fun t => s ^ 2 * g t ^ 2 - 2 * s * (g t * hI t) + hI t ^ 2 := by funext t; ring
    rw [ef, integral_add i3 iH, integral_sub i1 i2, integral_const_mul, integral_const_mul]
    unfold normSq; ring
  rw [e3] at hq; exact hq

/-- For even `g`, the Fourier coefficient is real: `c_n = X_n/(8a)`, `X_n = ∫ g cos(πnt/4a)`. -/
theorem cf_even {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (n : ℤ) :
    cf (2 * a) g n = (((1 / (8 * a)) * ∫ t, g t * Real.cos (π * n * t / (4 * a)) : ℝ) : ℂ) := by
  unfold cf
  push_cast
  have hsuppC : ∀ u, a < |u| →
      Complex.exp (-(2 * π * I * n * u / (4 * (2 * a)))) * ((g u : ℝ) : ℂ) = 0 := fun u hu => by
    rw [hp.supp u hu]; simp
  rw [integral_eq_of_supp hsuppC (by linarith) (by linarith)]
  have hpt : ∀ t : ℝ, Complex.exp (-(2 * π * I * n * t / (4 * (2 * a)))) * ((g t : ℝ) : ℂ)
      = ((g t * Real.cos (π * n * t / (4 * a)) : ℝ) : ℂ)
        - I * ((g t * Real.sin (π * n * t / (4 * a)) : ℝ) : ℂ) := by
    intro t
    have e : -(2 * π * I * n * t / (4 * (2 * a))) = ((-(π * n * t / (4 * a)) : ℝ) : ℂ) * I := by
      push_cast; field_simp
    rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  simp_rw [hpt]
  have hI := probe_integrable hp
  have ic : Integrable (fun t => g t * Real.cos (π * n * t / (4 * a))) :=
    hI.mul_bdd (c := 1)
      (show Continuous (fun t : ℝ => Real.cos (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have is : Integrable (fun t => g t * Real.sin (π * n * t / (4 * a))) :=
    hI.mul_bdd (c := 1)
      (show Continuous (fun t : ℝ => Real.sin (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hsin : (∫ t, g t * Real.sin (π * n * t / (4 * a))) = 0 := by
    have h := integral_neg_eq_self (fun t => g t * Real.sin (π * n * t / (4 * a))) volume
    have e : (fun t => g (-t) * Real.sin (π * n * -t / (4 * a)))
        = fun t => -(g t * Real.sin (π * n * t / (4 * a))) := by
      funext t; rw [hp.even, show π * n * -t / (4 * a) = -(π * n * t / (4 * a)) by ring,
        Real.sin_neg]; ring
    rw [e, integral_neg] at h; linarith
  have i1 : Integrable (fun x : ℝ => ((g x * Real.cos (π * n * x / (4 * a)) : ℝ) : ℂ)) := ic.ofReal
  have i2 : Integrable (fun x : ℝ => I * ((g x * Real.sin (π * n * x / (4 * a)) : ℝ) : ℂ)) :=
    is.ofReal.const_mul I
  rw [integral_sub i1 i2, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, hsin]
  push_cast; ring

theorem pm_even {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (n : ℤ) :
    pm a g n = (∫ t, g t * Real.cos (π * n * t / (4 * a))) ^ 2 / (8 * a) := by
  unfold pm; rw [cf_even ha hp, Complex.norm_real, Real.norm_eq_abs, sq_abs]; field_simp


theorem integral_supp {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (h : ℝ → ℝ) :
    (∫ t, g t * h t) = ∫ t in (-a)..a, g t * h t := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro t ht
  simp only [mem_Icc, not_and_or, not_le] at ht
  have : a < |t| := by
    rcases ht with h' | h'
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h'
  rw [hp.supp t this, zero_mul]

/-- **Orthogonality to `w` makes `∫ g` tiny**: `(∫ g)² ≤ a⁵/30` for `a ≤ 1/2`. -/
theorem integral_sq_perp {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : (∫ t, g t) ^ 2 ≤ a ^ 5 / 30 := by
  have hI := probe_integrable hp
  have iiG := memLp_intervalIntegrable hp.memL2 (-a) a
  have iS : IntervalIntegrable (fun t => g t * Real.sinh (t / 2)) volume (-a) a :=
    iiG.mul_continuousOn (by fun_prop)
  have iC : IntervalIntegrable (fun t => g t * Real.cosh (t / 2)) volume (-a) a :=
    iiG.mul_continuousOn (by fun_prop)
  have hsinh : (∫ t in (-a)..a, g t * Real.sinh (t / 2)) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -a) (b := a)
      (fun t => g t * Real.sinh (t / 2))
    have e : (fun t => g (-t) * Real.sinh (-t / 2)) = fun t => -(g t * Real.sinh (t / 2)) := by
      funext t; rw [hp.even, neg_div, Real.sinh_neg]; ring
    rw [e, intervalIntegral.integral_neg, neg_neg] at h; linarith
  have hcosh : (∫ t in (-a)..a, g t * Real.cosh (t / 2)) = 0 := by
    have e : poleR g a = (∫ t in (-a)..a, g t * Real.cosh (t / 2))
        - ∫ t in (-a)..a, g t * Real.sinh (t / 2) := by
      unfold poleR
      rw [← intervalIntegral.integral_sub iC iS]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [show Real.exp (-(t / 2)) = Real.cosh (t / 2) - Real.sinh (t / 2) by
        rw [Real.cosh_eq, Real.sinh_eq]; ring]
      ring
    rw [h0, hsinh, sub_zero] at e; exact e.symm
  have iOne : IntervalIntegrable (fun t => g t * (1 - Real.cosh (t / 2))) volume (-a) a :=
    iiG.mul_continuousOn (by fun_prop)
  have hg1 : (∫ t, g t) = ∫ t, g t * (1 - Real.cosh (t / 2)) := by
    rw [integral_supp ha hp (fun t => 1 - Real.cosh (t / 2))]
    have e0 : (∫ t, g t) = ∫ t, g t * 1 := by simp
    rw [e0, integral_supp ha hp (fun _ => 1)]
    have e2 : (∫ t in (-a)..a, g t * 1)
        = (∫ t in (-a)..a, g t * (1 - Real.cosh (t / 2))) + ∫ t in (-a)..a, g t * Real.cosh (t / 2) := by
      rw [← intervalIntegral.integral_add iOne iC]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [e2, hcosh, add_zero]
  have hcs := cs_supp ha hp (h := fun t => 1 - Real.cosh (t / 2)) (by fun_prop)
  rw [← hg1, hn, one_mul] at hcs
  set M := a ^ 2 / 8 + 5 * a ^ 4 / 1536 with hM
  have hpt : ∀ t ∈ Icc (-a) a, (1 - Real.cosh (t / 2)) ^ 2 ≤ M ^ 2 := by
    intro t ht
    have hta : |t| ≤ a := abs_le.2 ⟨ht.1, ht.2⟩
    have ht2 : t ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    have hc1 := Real.one_le_cosh (t / 2)
    have hc2 := cosh_le_taylor (y := t / 2) (by rw [abs_div, abs_two]; linarith)
    have ht4 : t ^ 4 ≤ a ^ 4 := by nlinarith [sq_nonneg t, sq_nonneg a]
    have hup : Real.cosh (t / 2) - 1 ≤ M := by
      rw [hM]; nlinarith
    have hM0 : 0 ≤ M := by positivity
    nlinarith
  have hmono := intervalIntegral.integral_mono_on (by linarith : -a ≤ a)
    ((by fun_prop : Continuous (fun t : ℝ => (1 - Real.cosh (t / 2)) ^ 2)).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume) (c := M ^ 2)) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfin : (a - -a) * M ^ 2 ≤ a ^ 5 / 30 := by
    rw [hM]
    have h1 : 5 * a ^ 2 / 192 ≤ 5 / 768 := by nlinarith
    have e : (a - -a) * (a ^ 2 / 8 + 5 * a ^ 4 / 1536) ^ 2
        = a ^ 5 / 32 * (1 + 5 * a ^ 2 / 192) ^ 2 := by ring
    rw [e]
    have h2 : (1 + 5 * a ^ 2 / 192) ^ 2 ≤ (1 + 5 / 768) ^ 2 := by
      have : 0 ≤ 5 * a ^ 2 / 192 := by positivity
      nlinarith
    have h5 : 0 < a ^ 5 := by positivity
    nlinarith
  linarith

/-- `∫_{−a}^{a} (cos(πnt/4a) − β)² = a(1 + 2 sin(πn/2)/(πn) − 16β sin(πn/4)/(πn) + 2β²)`. -/
theorem integral_cos_sub_sq {a : ℝ} (ha : 0 < a) {n : ℤ} (hn : 0 < n) (β : ℝ) :
    (∫ t in (-a)..a, (Real.cos (π * n * t / (4 * a)) - β) ^ 2)
      = a * (1 + 2 * Real.sin (π * n / 2) / (π * n) - 16 * β * Real.sin (π * n / 4) / (π * n)
          + 2 * β ^ 2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set ω := π * n / (4 * a) with hω
  have hω0 : 0 < ω := by positivity
  have hcosint : ∀ c : ℝ, 0 < c → (∫ t in (-a)..a, Real.cos (c * t)) = 2 * Real.sin (c * a) / c := by
    intro c hc
    rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hc.ne', integral_cos,
      smul_eq_mul, show c * -a = -(c * a) by ring, Real.sin_neg]
    field_simp; ring
  have e : (fun t => (Real.cos (π * n * t / (4 * a)) - β) ^ 2)
      = fun t => 1 / 2 + Real.cos ((2 * ω) * t) / 2 - 2 * β * Real.cos (ω * t) + β ^ 2 := by
    funext t
    rw [show π * n * t / (4 * a) = ω * t by rw [hω]; ring, sub_sq, Real.cos_sq,
      show 2 * (ω * t) = (2 * ω) * t by ring]
    ring
  rw [e]
  have c1 : Continuous (fun t => Real.cos ((2 * ω) * t) / 2) := by fun_prop
  have c2 : Continuous (fun t => 2 * β * Real.cos (ω * t)) := by fun_prop
  have i0 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume (-a) a := intervalIntegrable_const
  have i3 : IntervalIntegrable (fun _ : ℝ => β ^ 2) volume (-a) a := intervalIntegrable_const
  have hsplit : (∫ t in (-a)..a, (1 / 2 + Real.cos ((2 * ω) * t) / 2 - 2 * β * Real.cos (ω * t) + β ^ 2))
      = (∫ t in (-a)..a, (1 / 2 : ℝ)) + (∫ t in (-a)..a, Real.cos ((2 * ω) * t) / 2)
        - (∫ t in (-a)..a, 2 * β * Real.cos (ω * t)) + ∫ t in (-a)..a, β ^ 2 := by
    rw [intervalIntegral.integral_add ((i0.add (c1.intervalIntegrable _ _)).sub
      (c2.intervalIntegrable _ _)) i3, intervalIntegral.integral_sub
      (i0.add (c1.intervalIntegrable _ _)) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_add i0 (c1.intervalIntegrable _ _)]
  have p1 : (∫ t in (-a)..a, Real.cos ((2 * ω) * t) / 2) = Real.sin (π * n / 2) / (2 * ω) := by
    rw [intervalIntegral.integral_div, hcosint _ (by positivity),
      show 2 * ω * a = π * n / 2 by rw [hω]; field_simp; ring]
    field_simp
  have p2 : (∫ t in (-a)..a, 2 * β * Real.cos (ω * t)) = 2 * β * (2 * Real.sin (π * n / 4) / ω) := by
    rw [intervalIntegral.integral_const_mul, hcosint _ hω0,
      show ω * a = π * n / 4 by rw [hω]; field_simp]
  rw [hsplit, p1, p2]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [hω]; field_simp; ring

/-- **Mode-mass bound**: `p_n ≤ (1.05·∫(cos − β)² + 21β²(∫g)²)/(8a)`. -/
theorem pm_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (n : ℤ)
    (β : ℝ) :
    pm a g n ≤ (1.05 * (∫ t in (-a)..a, (Real.cos (π * n * t / (4 * a)) - β) ^ 2)
      + 21 * β ^ 2 * (∫ t, g t) ^ 2) / (8 * a) := by
  rw [pm_even ha hp]
  have hI := probe_integrable hp
  have ic : Integrable (fun t => g t * Real.cos (π * n * t / (4 * a))) :=
    hI.mul_bdd (c := 1)
      (show Continuous (fun t : ℝ => Real.cos (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hY : (∫ t, g t * Real.cos (π * n * t / (4 * a)))
      = (∫ t, g t * (Real.cos (π * n * t / (4 * a)) - β)) + β * ∫ t, g t := by
    have i2 : Integrable (fun t => g t * β) := hI.mul_const β
    rw [show (fun t => g t * (Real.cos (π * n * t / (4 * a)) - β))
        = fun t => g t * Real.cos (π * n * t / (4 * a)) - g t * β by funext t; ring,
      integral_sub ic i2, integral_mul_const]
    ring
  have hcs := cs_supp ha hp (h := fun t => Real.cos (π * n * t / (4 * a)) - β) (by fun_prop)
  rw [hn, one_mul] at hcs
  rw [hY]
  set Y := ∫ t, g t * (Real.cos (π * n * t / (4 * a)) - β)
  set Z := β * ∫ t, g t
  have h8 : 0 < 8 * a := by linarith
  apply div_le_div_of_nonneg_right _ h8.le
  have hZ : Z ^ 2 = β ^ 2 * (∫ t, g t) ^ 2 := by simp only [Z]; ring
  nlinarith [sq_nonneg (Y / 20 - Z)]

theorem pm_neg {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (n : ℤ) :
    pm a g (-n) = pm a g n := by
  rw [pm_even ha hp, pm_even ha hp]; congr 3; funext t; push_cast
  rw [show π * -(n : ℝ) * t / (4 * a) = -(π * n * t / (4 * a)) by ring, Real.cos_neg]

theorem pm_zero_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 0 ≤ a ^ 4 / 240 := by
  rw [pm_even ha hp]
  simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, mul_one]
  have := integral_sq_perp ha ha2 hp hn h0
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos ha 4]

theorem modeE_zero (a : ℝ) : modeE a 0 = 0 := by
  unfold modeE; simp

/-- The generic per-mode estimate `(ψ − τ)p ≥ (ψ̲ − τ)P`. -/
theorem term_ge {ψ ψl τ p P : ℝ} (h1 : ψl ≤ ψ) (h2 : ψl - τ ≤ 0) (h3 : 0 ≤ p) (h4 : p ≤ P) :
    (ψl - τ) * P ≤ (ψ - τ) * p := by nlinarith

theorem cval1 : 1 + 2 * Real.sin (π * ((1 : ℤ) : ℝ) / 2) / (π * ((1 : ℤ) : ℝ))
    - 16 * (0.9 : ℝ) * Real.sin (π * ((1 : ℤ) : ℝ) / 4) / (π * ((1 : ℤ) : ℝ)) + 2 * (0.9 : ℝ) ^ 2
    ≤ (0.01551 : ℝ) := by
  push_cast
  rw [show π * (1 : ℝ) / 2 = 2 * π / 4 by ring, show π * (1 : ℝ) / 4 = 1 * π / 4 by ring,
    (sc2).1, (sc1).1]
  have key : 1 + 2 * (1) / (π * 1) - 16 * (0.9 : ℝ) * (Real.sqrt 2/2) / (π * 1)
      + 2 * (0.9 : ℝ) ^ 2 = 1 + 2 * (0.9 : ℝ) ^ 2 + (1 / π) * (2 - 36*Real.sqrt 2/5) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le1 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 1 ≤ (0.00306 : ℝ) := by
  have h1 := pm_le ha hp hn 1 (0.9 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0.9 : ℝ)] at h1
  have hc := cval1
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.3466 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0.9 : ℝ)]

theorem cval2 : 1 + 2 * Real.sin (π * ((2 : ℤ) : ℝ) / 2) / (π * ((2 : ℤ) : ℝ))
    - 16 * (0.6366 : ℝ) * Real.sin (π * ((2 : ℤ) : ℝ) / 4) / (π * ((2 : ℤ) : ℝ)) + 2 * (0.6366 : ℝ) ^ 2
    ≤ (0.18946 : ℝ) := by
  push_cast
  rw [show π * (2 : ℝ) / 2 = 4 * π / 4 by ring, show π * (2 : ℝ) / 4 = 2 * π / 4 by ring,
    (sc4).1, (sc2).1]
  have key : 1 + 2 * (0) / (π * 2) - 16 * (0.6366 : ℝ) * (1) / (π * 2)
      + 2 * (0.6366 : ℝ) ^ 2 = 1 + 2 * (0.6366 : ℝ) ^ 2 + (1 / π) * (-3183/625) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le2 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 2 ≤ (0.02538 : ℝ) := by
  have h1 := pm_le ha hp hn 2 (0.6366 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0.6366 : ℝ)] at h1
  have hc := cval2
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.3466 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0.6366 : ℝ)]

theorem cval3 : 1 + 2 * Real.sin (π * ((3 : ℤ) : ℝ) / 2) / (π * ((3 : ℤ) : ℝ))
    - 16 * (0.3 : ℝ) * Real.sin (π * ((3 : ℤ) : ℝ) / 4) / (π * ((3 : ℤ) : ℝ)) + 2 * (0.3 : ℝ) ^ 2
    ≤ (0.60769 : ℝ) := by
  push_cast
  rw [show π * (3 : ℝ) / 2 = 6 * π / 4 by ring, show π * (3 : ℝ) / 4 = 3 * π / 4 by ring,
    (sc6).1, (sc3).1]
  have key : 1 + 2 * (-1) / (π * 3) - 16 * (0.3 : ℝ) * (Real.sqrt 2/2) / (π * 3)
      + 2 * (0.3 : ℝ) ^ 2 = 1 + 2 * (0.3 : ℝ) ^ 2 + (1 / π) * (-4*Real.sqrt 2/5 - 2/3) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le3 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 3 ≤ (0.07988 : ℝ) := by
  have h1 := pm_le ha hp hn 3 (0.3 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0.3 : ℝ)] at h1
  have hc := cval3
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.3466 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0.3 : ℝ)]

theorem cval4 : 1 + 2 * Real.sin (π * ((4 : ℤ) : ℝ) / 2) / (π * ((4 : ℤ) : ℝ))
    - 16 * (0 : ℝ) * Real.sin (π * ((4 : ℤ) : ℝ) / 4) / (π * ((4 : ℤ) : ℝ)) + 2 * (0 : ℝ) ^ 2
    ≤ (1 : ℝ) := by
  push_cast
  rw [show π * (4 : ℝ) / 2 = 8 * π / 4 by ring, show π * (4 : ℝ) / 4 = 4 * π / 4 by ring,
    (sc8).1, (sc4).1]
  have key : 1 + 2 * (0) / (π * 4) - 16 * (0 : ℝ) * (0) / (π * 4)
      + 2 * (0 : ℝ) ^ 2 = 1 + 2 * (0 : ℝ) ^ 2 + (1 / π) * (0) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le4 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 4 ≤ (0.13125 : ℝ) := by
  have h1 := pm_le ha hp hn 4 (0 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0 : ℝ)] at h1
  have hc := cval4
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.3466 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0 : ℝ)]

theorem cval5 : 1 + 2 * Real.sin (π * ((5 : ℤ) : ℝ) / 2) / (π * ((5 : ℤ) : ℝ))
    - 16 * (-0.18 : ℝ) * Real.sin (π * ((5 : ℤ) : ℝ) / 4) / (π * ((5 : ℤ) : ℝ)) + 2 * (-0.18 : ℝ) ^ 2
    ≤ (1.0625 : ℝ) := by
  push_cast
  rw [show π * (5 : ℝ) / 2 = 10 * π / 4 by ring, show π * (5 : ℝ) / 4 = 5 * π / 4 by ring,
    (sc10).1, (sc5).1]
  have key : 1 + 2 * (1) / (π * 5) - 16 * (-0.18 : ℝ) * (-Real.sqrt 2/2) / (π * 5)
      + 2 * (-0.18 : ℝ) ^ 2 = 1 + 2 * (-0.18 : ℝ) ^ 2 + (1 / π) * (2/5 - 36*Real.sqrt 2/125) := by
    field_simp; ring
  rw [key]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  nlinarith

theorem pm_le5 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 5 ≤ (0.1395 : ℝ) := by
  have h1 := pm_le ha hp hn 5 (-0.18 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (-0.18 : ℝ)] at h1
  have hc := cval5
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.3466 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (-0.18 : ℝ)]

/-! ## F. The box, and the gap below the first prime -/

theorem nearField_box_le' {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioc 0 (2 * a), archIntegrand (box a) u) ≤ 1 + a / 2 := by
  have hpt : ∀ u ∈ Ioc 0 (2 * a), archIntegrand (box a) u ≤ 1 / (2 * a) + u / (4 * a) := by
    intro u hu
    have hK0 : 0 ≤ kerK u := (kerK_pos hu.1).le
    have h1 : archIntegrand (box a) u ≤ (1 / (2 * a) * u) * kerK u := by
      unfold archIntegrand
      rw [← box_sq ha]
      exact mul_le_mul_of_nonneg_right (box_autocorr_diff_le hu.1) hK0
    have h2 : (1 / (2 * a) * u) * kerK u ≤ (1 / (2 * a) * u) * (1 / u + 1 / 2) :=
      mul_le_mul_of_nonneg_left (kerK_le' hu.1) (by have := hu.1; positivity)
    have h3 : (1 / (2 * a) * u) * (1 / u + 1 / 2) = 1 / (2 * a) + u / (4 * a) := by
      field_simp [hu.1.ne']; ring
    linarith
  have hc : Continuous (fun u : ℝ => 1 / (2 * a) + u / (4 * a)) := by fun_prop
  have hmono := setIntegral_mono_on ((box_probe a).arch.mono_set Ioc_subset_Ioi_self)
    (hc.integrableOn_Ioc) measurableSet_Ioc hpt
  have hR : (∫ u in Ioc 0 (2 * a), (1 / (2 * a) + u / (4 * a))) = 1 + a / 2 := by
    rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_add
      intervalIntegrable_const
      ((by fun_prop : Continuous (fun u : ℝ => u / (4 * a))).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id, smul_eq_mul]
    field_simp; ring
  linarith

theorem pole_box_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    2 * poleR (box a) a ^ 2 ≤ 4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2 := by
  set c := 1 / Real.sqrt (2 * a) with hc
  have hp : poleR (box a) a = c * ∫ u in (-a)..a, Real.exp (-(u / 2)) := by
    unfold poleR
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    simp only [box_apply, abs_le.2 ⟨hu.1, hu.2⟩, ite_true, hc]
  have hint : (∫ u in (-a)..a, Real.exp (-(u / 2))) = 4 * Real.sinh (a / 2) := by
    have h := intervalIntegral.integral_comp_mul_left (a := -a) (b := a) (fun s => Real.exp s)
      (show (-(1 / 2) : ℝ) ≠ 0 by norm_num)
    rw [show (fun u => Real.exp (-(u / 2))) = fun u => Real.exp (-(1 / 2) * u) by
      funext u; ring_nf, h, integral_exp, Real.sinh_eq, smul_eq_mul]
    ring_nf
  have hs := sinh_le_taylor (y := a / 2) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sinh (a / 2) := (Real.sinh_pos_iff.2 (by linarith)).le
  have hc2 : c ^ 2 = 1 / (2 * a) := box_sq ha
  rw [hp, hint]
  have e1 : 2 * (c * (4 * Real.sinh (a / 2))) ^ 2 = 16 * Real.sinh (a / 2) ^ 2 / a := by
    rw [mul_pow, mul_pow, hc2]; field_simp; ring
  rw [e1, div_le_iff₀ ha]
  have hb : Real.sinh (a / 2) ≤ a / 2 * (1 + a ^ 2 / 24 + a ^ 4 / 1600) := by
    have : a / 2 + (a / 2) ^ 3 / 6 + (a / 2) ^ 5 / 100 = a / 2 * (1 + a ^ 2 / 24 + a ^ 4 / 1600) := by
      ring
    linarith
  have := pow_le_pow_left₀ hs0 hb 2
  nlinarith


/-- The tail level `τ(a) = 2.7801 + a(1 − 0.31831/3) − err(a)`. -/
def tauF (a : ℝ) : ℝ := 2.7801 + a * (1 - 0.31831 / 3) - errK a

theorem tail_ok {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 6 ≤ n) : tauF a ≤ modeE a n := by
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hC : Cin (π * 6 / 2) ≤ Cin (π * n / 2) :=
    Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  have hc := cin_val6
  have hπ := Real.pi_pos
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by positivity)
  have h2 : 2 / (π * n) ≤ 2 / (π * 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have h3 : 2 / (π * 6) = (1 / π) / 3 := by field_simp; ring
  obtain ⟨b1, b2, -⟩ := num_atoms
  unfold tauF
  nlinarith

theorem dlo1 : (0.36338 : ℝ) ≤ 1 - 2 * Real.sin (π * ((1 : ℤ) : ℝ) / 2) / (π * ((1 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (1 : ℝ) / 2 = 2 * π / 4 by ring, (sc2).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 1) = (2 * s / 1) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term1 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((0.5408 : ℝ) + a * 0.36338 - errK a - tauF a) * 0.00306 ≤ (modeE a 1 - tauF a) * pm a g 1 := by
  have hψ := modeE_ge ha (by linarith) (n := 1) (by norm_num)
  have hc := cin_val1
  have hd := dlo1
  have hC : Cin (π * ((1 : ℤ) : ℝ) / 2) = Cin (π * 1 / 2) := by push_cast; rfl
  rw [hC] at hψ
  refine term_ge ?_ ?_ (pm_nonneg ha g 1) (pm_le1 ha ha2 hp hn h0)
  · nlinarith
  · unfold tauF; linarith

theorem dlo2 : (1 : ℝ) ≤ 1 - 2 * Real.sin (π * ((2 : ℤ) : ℝ) / 2) / (π * ((2 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (2 : ℝ) / 2 = 4 * π / 4 by ring, (sc4).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 2) = (2 * s / 2) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term2 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((1.6214 : ℝ) + a * 1 - errK a - tauF a) * 0.02538 ≤ (modeE a 2 - tauF a) * pm a g 2 := by
  have hψ := modeE_ge ha (by linarith) (n := 2) (by norm_num)
  have hc := cin_val2
  have hd := dlo2
  have hC : Cin (π * ((2 : ℤ) : ℝ) / 2) = Cin (π * 2 / 2) := by push_cast; rfl
  rw [hC] at hψ
  refine term_ge ?_ ?_ (pm_nonneg ha g 2) (pm_le2 ha ha2 hp hn h0)
  · nlinarith
  · unfold tauF; linarith

theorem dlo3 : (1.212206 : ℝ) ≤ 1 - 2 * Real.sin (π * ((3 : ℤ) : ℝ) / 2) / (π * ((3 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (3 : ℝ) / 2 = 6 * π / 4 by ring, (sc6).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 3) = (2 * s / 3) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term3 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((2.2965 : ℝ) + a * 1.212206 - errK a - tauF a) * 0.07988 ≤ (modeE a 3 - tauF a) * pm a g 3 := by
  have hψ := modeE_ge ha (by linarith) (n := 3) (by norm_num)
  have hc := cin_val3
  have hd := dlo3
  have hC : Cin (π * ((3 : ℤ) : ℝ) / 2) = Cin (π * 3 / 2) := by push_cast; rfl
  rw [hC] at hψ
  refine term_ge ?_ ?_ (pm_nonneg ha g 3) (pm_le3 ha ha2 hp hn h0)
  · nlinarith
  · unfold tauF; linarith

theorem dlo4 : (1 : ℝ) ≤ 1 - 2 * Real.sin (π * ((4 : ℤ) : ℝ) / 2) / (π * ((4 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (4 : ℝ) / 2 = 8 * π / 4 by ring, (sc8).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 4) = (2 * s / 4) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term4 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((2.4081 : ℝ) + a * 1 - errK a - tauF a) * 0.13125 ≤ (modeE a 4 - tauF a) * pm a g 4 := by
  have hψ := modeE_ge ha (by linarith) (n := 4) (by norm_num)
  have hc := cin_val4
  have hd := dlo4
  have hC : Cin (π * ((4 : ℤ) : ℝ) / 2) = Cin (π * 4 / 2) := by push_cast; rfl
  rw [hC] at hψ
  refine term_ge ?_ ?_ (pm_nonneg ha g 4) (pm_le4 ha ha2 hp hn h0)
  · nlinarith
  · unfold tauF; linarith

theorem dlo5 : (0.872676 : ℝ) ≤ 1 - 2 * Real.sin (π * ((5 : ℤ) : ℝ) / 2) / (π * ((5 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (5 : ℝ) / 2 = 10 * π / 4 by ring, (sc10).1]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := num_atoms
  have e : ∀ s : ℝ, 2 * s / (π * 5) = (2 * s / 5) * (1 / π) := fun s => by field_simp
  rw [e]
  nlinarith

theorem term5 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    ((2.4848 : ℝ) + a * 0.872676 - errK a - tauF a) * 0.1395 ≤ (modeE a 5 - tauF a) * pm a g 5 := by
  have hψ := modeE_ge ha (by linarith) (n := 5) (by norm_num)
  have hc := cin_val5
  have hd := dlo5
  have hC : Cin (π * ((5 : ℤ) : ℝ) / 2) = Cin (π * 5 / 2) := by push_cast; rfl
  rw [hC] at hψ
  refine term_ge ?_ ?_ (pm_nonneg ha g 5) (pm_le5 ha ha2 hp hn h0)
  · nlinarith
  · unfold tauF; linarith

/-- The low modes `−5, …, 5`. -/
def lowS : Finset ℤ := {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5}

theorem not_mem_lowS {n : ℤ} (hn : n ∉ lowS) : 6 ≤ n ∨ n ≤ -6 := by
  simp only [lowS, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  omega

theorem tail_all {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℤ) (hn : n ∉ lowS) : tauF a ≤ modeE a n := by
  rcases not_mem_lowS hn with h | h
  · exact tail_ok ha ha1 h
  · have e := modeE_neg a (-n)
    rw [neg_neg] at e
    rw [e]; exact tail_ok ha ha1 (by omega)

/-- **The near-field energy of a normalised probe orthogonal to `w`, below the first prime.** -/
theorem nearField_fourier {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.3466) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    tauF a - tauF a * (a ^ 4 / 240)
      + 2 * ((0.5408 + a * 0.36338 - errK a - tauF a) * 0.00306
        + (1.6214 + a * 1 - errK a - tauF a) * 0.02538
        + (2.2965 + a * 1.212206 - errK a - tauF a) * 0.07988
        + (2.4081 + a * 1 - errK a - tauF a) * 0.13125
        + (2.4848 + a * 0.872676 - errK a - tauF a) * 0.1395)
      ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have hE := energy_ge_trunc ha hp hn lowS (tail_all ha (by linarith))
  have htau0 : 0 ≤ tauF a := by
    unfold tauF errK
    have : a ^ 2 ≤ 0.3466 * a := by nlinarith
    have : a ^ 3 ≤ 0.3466 ^ 2 * a := by nlinarith
    have : a ^ 4 ≤ 0.3466 ^ 3 * a := by nlinarith [pow_pos ha 3]
    have : a ^ 5 ≤ 0.3466 ^ 4 * a := by nlinarith [pow_pos ha 4]
    nlinarith
  have hsum : ∑ n ∈ lowS, (modeE a n - tauF a) * pm a g n
      = (modeE a 0 - tauF a) * pm a g 0
        + 2 * ((modeE a 1 - tauF a) * pm a g 1 + (modeE a 2 - tauF a) * pm a g 2
          + (modeE a 3 - tauF a) * pm a g 3 + (modeE a 4 - tauF a) * pm a g 4
          + (modeE a 5 - tauF a) * pm a g 5) := by
    have hm : ∀ k : ℤ, modeE a (-k) = modeE a k := modeE_neg a
    have hq : ∀ k : ℤ, pm a g (-k) = pm a g k := pm_neg ha hp
    simp only [lowS]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [show (-5 : ℤ) = -(5 : ℤ) from rfl, show (-4 : ℤ) = -(4 : ℤ) from rfl,
      show (-3 : ℤ) = -(3 : ℤ) from rfl, show (-2 : ℤ) = -(2 : ℤ) from rfl,
      show (-1 : ℤ) = -(1 : ℤ) from rfl, hm, hm, hm, hm, hm, hq, hq, hq, hq, hq]
    ring
  rw [hsum] at hE
  have h0t : (0 - tauF a) * (a ^ 4 / 240) ≤ (modeE a 0 - tauF a) * pm a g 0 := by
    rw [modeE_zero]
    have := pm_zero_le ha (by linarith) hp hn h0
    nlinarith [pm_nonneg ha g 0]
  have t1 := term1 ha ha2 hp hn h0
  have t2 := term2 ha ha2 hp hn h0
  have t3 := term3 ha ha2 hp hn h0
  have t4 := term4 ha ha2 hp hn h0
  have t5 := term5 ha ha2 hp hn h0
  linarith

/-- **The gap below the first prime**: for `0 < a` with `2a < log 2`, every normalised probe `g`
with `ĝ(i/2) = 0` has `Q(g) ≥ Q(box) + 1/10`. -/
theorem weilQ_perp_ge_fourier {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2) {g : ℝ → ℝ}
    (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    weilQ a (box a) + 1 / 10 ≤ weilQ a g := by
  have hl2 := Real.log_two_lt_d9
  have ha2 : a ≤ 0.3466 := by norm_num at hl2; linarith
  have hQ : ∀ h, Probe a h → normSq h = 1 →
      weilQ a h = 2 * poleR h a ^ 2 + weilConst + archE h := by
    intro h hh hhn
    rw [weilQ_eq', primeS_eq_zero hlog hh, hhn]; ring
  rw [hQ g hp hn, hQ _ (box_probe a) (normSq_box ha), h0, archE_split ha hp hn,
    archE_split ha (box_probe a) (normSq_box ha)]
  have hG := nearField_fourier ha ha2 hp hn h0
  have hB := nearField_box_le' ha
  have hP := pole_box_le ha (by linarith)
  -- numerics
  have e1 : a ^ 2 ≤ 0.3466 * a := by nlinarith
  have e2 : a ^ 3 ≤ 0.3466 ^ 2 * a := by nlinarith
  have e3 : a ^ 4 ≤ 0.3466 ^ 3 * a := by nlinarith [pow_pos ha 3]
  have e4 : a ^ 5 ≤ 0.3466 ^ 4 * a := by nlinarith [pow_pos ha 4]
  have herr : errK a ≤ 0.2837 * a ^ 2 := by
    unfold errK; nlinarith [pow_pos ha 3, pow_pos ha 4, pow_pos ha 5]
  have herr0 : 0 ≤ errK a := by unfold errK; positivity
  have hpole : 4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2 ≤ 4 * a + 0.34 * a ^ 3 := by
    have h8 : a ^ 8 ≤ 0.3466 ^ 6 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 6]
    have h6 : a ^ 6 ≤ 0.3466 ^ 4 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 4]
    nlinarith [pow_pos ha 3, pow_pos ha 5, pow_pos ha 7, pow_pos ha 9]
  have htau : tauF a ≤ 3.8 := by unfold tauF; nlinarith
  have htau0 : 0 ≤ tauF a := by unfold tauF; nlinarith
  have hsmall : tauF a * (a ^ 4 / 240) ≤ 3.8 * (0.3466 ^ 3 * a) / 240 := by
    have : 0 ≤ a ^ 4 := by positivity
    nlinarith
  unfold tauF at hG hsmall
  nlinarith

/-- **Certified lower bound orthogonally to `w`, for every `a` with `2a < log 2`**:
`Q₀(g) = Q(g) ≥ λ₁ + 1/10`. -/
theorem weilQ0_perp_ge_fourier {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2) {g : ℝ → ℝ}
    (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    lam a + 1 / 10 ≤ weilQ0 a g := by
  have hQ := weilQ_perp_ge_fourier ha hlog hp hn h0
  have hQ0 : weilQ0 a g = weilQ a g := by unfold weilQ0; rw [h0]; ring
  have hlam := lam_le (box_probe a) (normSq_box ha)
  rw [hQ0]; linarith

/-- **The ground state of `Q` is unique up to sign for every `a > 0` with `2a < log 2`.** -/
theorem groundState_unique_below_log2 {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2)
    {g h : ℝ → ℝ} (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  refine groundState_unique ha (fun v hv hv0 => ?_) hg hh
  have h1 := weilQ_perp_ge_fourier ha hlog hv.1 hv.2.1 hv0
  have h2 := hv.2.2 (box a) (box_probe a) (normSq_box ha)
  linarith

/-! ## H. Past the first prime: `log 2 ≤ 2a ≤ 0.7` -/

theorem log_three_gt : (0.7 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp 0.7 < Real.exp 1 := Real.exp_lt_exp.2 (by norm_num)
  have h2 := Real.exp_one_lt_d9
  linarith

/-- For `2a ≤ 0.7`, only `n = 2` contributes: `S(g) = (log 2/√2)·f(log 2)`. -/
theorem primeS_eq_two {a : ℝ} (ha : 2 * a ≤ 0.7) {g : ℝ → ℝ} (hg : Probe a g) :
    primeS g = Real.log 2 / Real.sqrt 2 * autocorr g (Real.log 2) := by
  unfold primeS
  rw [tsum_eq_single 2]
  · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; push_cast; ring
  · intro n hn
    rcases lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h3 : 3 ≤ n := by omega
      have hl : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h3)
      have := log_three_gt
      have hz : autocorr g (Real.log n) = 0 :=
        autocorr_eq_zero hg.supp (by rw [abs_of_pos (by linarith)]; linarith)
      simp [hz]

/-- `f(2a) = 0`. -/
theorem autocorr_two_a {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) : autocorr g (2 * a) = 0 := by
  unfold autocorr
  have : (fun t => g t * g (t + 2 * a)) =ᵐ[volume] 0 := by
    have hne : ∀ᵐ t ∂volume, t ≠ -a := by
      rw [ae_iff]; simp
    filter_upwards [hne] with t ht
    by_cases h1 : a < |t|
    · simp [hp.supp t h1]
    · have htl : -a < t := lt_of_le_of_ne (neg_le_of_abs_le (not_lt.1 h1)) (Ne.symm ht)
      have : a < |t + 2 * a| := by rw [abs_of_pos (by linarith)]; linarith
      simp [hp.supp _ this]
  rw [integral_congr_ae this]; simp

/-- `f(u) = Σ p_n cos(πnu/4a)` for `0 ≤ u ≤ 2a`. -/
theorem hasSum_autocorr {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 2 * a) :
    HasSum (fun n : ℤ => pm a g n * Real.cos (π * n * u / (4 * a))) (autocorr g u) := by
  have h1 := hasSum_pm ha hp
  rw [hn] at h1
  have h2 := hasSum_one_sub_autocorr ha hp hn hu0 hu
  convert h1.sub h2 using 1
  · funext n; ring
  · ring

/-- The prime defect of mode `n`: `δ_n = |cos(πn u₀/4a) − cos(πn·2a/4a)|`. -/
def primeD (a u₀ : ℝ) (n : ℤ) : ℝ :=
  |Real.cos (π * n * u₀ / (4 * a)) - Real.cos (π * n * (2 * a) / (4 * a))|

theorem primeD_le_two (a u₀ : ℝ) (n : ℤ) : primeD a u₀ n ≤ 2 := by
  unfold primeD
  have := abs_sub (Real.cos (π * n * u₀ / (4 * a))) (Real.cos (π * n * (2 * a) / (4 * a)))
  have h1 := Real.abs_cos_le_one (π * n * u₀ / (4 * a))
  have h2 := Real.abs_cos_le_one (π * n * (2 * a) / (4 * a))
  linarith

theorem primeD_le {a u₀ : ℝ} (ha : 0 < a) (n : ℤ) :
    primeD a u₀ n ≤ π * |(n : ℝ)| * |2 * a - u₀| / (4 * a) := by
  unfold primeD
  refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
  rw [show π * n * u₀ / (4 * a) - π * n * (2 * a) / (4 * a) = -(π * n * (2 * a - u₀) / (4 * a)) by
    ring, abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (by linarith : (0 : ℝ) < 4 * a)]

theorem primeD_neg (a u₀ : ℝ) (n : ℤ) : primeD a u₀ (-n) = primeD a u₀ n := by
  unfold primeD; push_cast
  rw [show π * -(n : ℝ) * u₀ / (4 * a) = -(π * n * u₀ / (4 * a)) by ring,
    show π * -(n : ℝ) * (2 * a) / (4 * a) = -(π * n * (2 * a) / (4 * a)) by ring,
    Real.cos_neg, Real.cos_neg]

/-- **The truncated lower bound with the prime term.** -/
theorem energy_prime_trunc {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    {u₀ : ℝ} (hu0 : 0 ≤ u₀) (hu : u₀ ≤ 2 * a) {c : ℝ} (hc : 0 ≤ c) (S₀ : Finset ℤ) {τ : ℝ}
    (hτ : ∀ n, n ∉ S₀ → τ ≤ modeE a n - c * primeD a u₀ n) :
    τ + ∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n
      ≤ (∫ u in Ioc 0 (2 * a), archIntegrand g u) - c * autocorr g u₀ := by
  have hP := hasSum_pm ha hp
  rw [hn] at hP
  -- `f(u₀) = Σ p_n (cos(ω u₀) − cos(ω 2a))`
  have hF : HasSum (fun n : ℤ => pm a g n * (Real.cos (π * n * u₀ / (4 * a))
      - Real.cos (π * n * (2 * a) / (4 * a)))) (autocorr g u₀) := by
    have := (hasSum_autocorr ha hp hn hu0 hu).sub
      (hasSum_autocorr ha hp hn (by linarith) le_rfl)
    rw [autocorr_two_a ha hp, sub_zero] at this
    convert this using 1; funext n; ring
  have hbound : ∀ S : Finset ℤ, autocorr g u₀
      ≤ ∑ n ∈ S, pm a g n * primeD a u₀ n + 2 * (1 - ∑ n ∈ S, pm a g n) := by
    intro S
    set G : ℤ → ℝ := fun n => 2 * pm a g n + if n ∈ S then pm a g n * primeD a u₀ n - 2 * pm a g n else 0
    have hG : HasSum G (2 * 1 + ∑ n ∈ S, (pm a g n * primeD a u₀ n - 2 * pm a g n)) := by
      refine (hP.mul_left 2).add ?_
      have : HasSum (fun n : ℤ => if n ∈ S then pm a g n * primeD a u₀ n - 2 * pm a g n else 0)
          (∑ n ∈ S, if n ∈ S then pm a g n * primeD a u₀ n - 2 * pm a g n else 0) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
      convert this using 1
      refine Finset.sum_congr rfl fun n hn => by simp [hn]
    have hfg : ∀ n : ℤ, pm a g n * (Real.cos (π * n * u₀ / (4 * a))
        - Real.cos (π * n * (2 * a) / (4 * a))) ≤ G n := by
      intro n
      simp only [G]
      have hp0 := pm_nonneg ha g n
      have hd := le_abs_self (Real.cos (π * n * u₀ / (4 * a)) - Real.cos (π * n * (2 * a) / (4 * a)))
      have hd2 : Real.cos (π * n * u₀ / (4 * a)) - Real.cos (π * n * (2 * a) / (4 * a)) ≤ 2 := by
        linarith [Real.cos_le_one (π * n * u₀ / (4 * a)), Real.neg_one_le_cos (π * n * (2 * a) / (4 * a))]
      split_ifs with h
      · unfold primeD; nlinarith
      · nlinarith
    have hle := hasSum_le hfg hF hG
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hle; linarith
  have hT : Tendsto (fun S : Finset ℤ => ∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n
      + τ * ∑ n ∈ S, pm a g n - 2 * c * (1 - ∑ n ∈ S, pm a g n)) atTop
      (𝓝 (∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n + τ * 1 - 2 * c * (1 - 1))) :=
    ((tendsto_const_nhds.add (hP.const_mul τ)).sub
      ((tendsto_const_nhds.sub hP).const_mul (2 * c)))
  rw [sub_self, mul_zero, sub_zero, mul_one, add_comm] at hT
  refine le_of_tendsto hT ?_
  filter_upwards [eventually_ge_atTop S₀] with S hS
  have hsplit := Finset.sum_sdiff hS (f := pm a g)
  have hsplit2 := Finset.sum_sdiff hS (f := fun n => pm a g n * (modeE a n - c * primeD a u₀ n))
  have htail : τ * ∑ n ∈ S \ S₀, pm a g n ≤ ∑ n ∈ S \ S₀, pm a g n * (modeE a n - c * primeD a u₀ n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn' => ?_
    rw [Finset.mem_sdiff] at hn'
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hτ n hn'.2) (pm_nonneg ha g n)
  have hlow : ∑ n ∈ S₀, (modeE a n - c * primeD a u₀ n - τ) * pm a g n
      = ∑ n ∈ S₀, pm a g n * (modeE a n - c * primeD a u₀ n) - τ * ∑ n ∈ S₀, pm a g n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hle := sum_modeE_le ha hp hn S
  have hb := hbound S
  have hsum : ∑ n ∈ S, pm a g n * (modeE a n - c * primeD a u₀ n)
      = ∑ n ∈ S, pm a g n * modeE a n - c * ∑ n ∈ S, pm a g n * primeD a u₀ n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [← hsplit, mul_add] at *
  rw [← hsplit2] at hsum
  nlinarith

theorem primeD_nonneg (a u₀ : ℝ) (n : ℤ) : 0 ≤ primeD a u₀ n := abs_nonneg _

theorem primeD_small {a : ℝ} (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35) (n : ℤ) :
    primeD a (Real.log 2) n ≤ 0.01553 * |(n : ℝ)| := by
  have hl1 := Real.log_two_gt_d9
  have ha : (0.34657359 : ℝ) ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  refine (primeD_le ha0 n).trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a - Real.log 2), div_le_iff₀ (by linarith)]
  have hπ := Real.pi_lt_d6
  have hn0 := abs_nonneg (n : ℝ)
  have hε : 2 * a - Real.log 2 ≤ 0.0068528197 := by linarith
  have hε0 : 0 ≤ 2 * a - Real.log 2 := by linarith
  have h1 : π * |(n : ℝ)| * (2 * a - Real.log 2) ≤ 3.141593 * |(n : ℝ)| * 0.0068528197 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right hπ.le hn0) hε hε0 (by positivity)
    linarith
  nlinarith

/-- `ψ_n ≥ Cin(πn/2) + a(1 − 0.31831/3) − err(a)` for `n ≥ 6`. -/
theorem modeE_tail_base {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 6 ≤ n) :
    Cin (π * n / 2) + a * (1 - 0.31831 / 3) - errK a ≤ modeE a n := by
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hπ := Real.pi_pos
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by positivity)
  have h2 : 2 / (π * n) ≤ 2 / (π * 6) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have h3 : 2 / (π * 6) = (1 / π) / 3 := by field_simp; ring
  obtain ⟨b1, b2, -⟩ := num_atoms
  nlinarith

theorem tailB_pos {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 0.9803) {n : ℤ} (hn : 6 ≤ n) :
    2.8 ≤ modeE a n - c * primeD a (Real.log 2) n := by
  have hl1 := Real.log_two_gt_d9
  have ha' : (0.34657 : ℝ) ≤ a := by linarith
  have hb := modeE_tail_base ha (by linarith) hn
  have herr : errK a ≤ 0.0349 := by
    unfold errK
    have h2 : a ^ 2 ≤ 0.35 ^ 2 := pow_le_pow_left₀ ha.le ha2 2
    have h3 : a ^ 3 ≤ 0.35 ^ 3 := pow_le_pow_left₀ ha.le ha2 3
    have h4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
    have h5 : a ^ 5 ≤ 0.35 ^ 5 := pow_le_pow_left₀ ha.le ha2 5
    norm_num at h2 h3 h4 h5 ⊢; linarith
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := primeD_small hlo ha2 n
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hD
  have hD2 := primeD_le_two a (Real.log 2) n
  have hπ := Real.pi_pos
  have hCm : ∀ m : ℝ, 0 ≤ m → m ≤ n → Cin (m * π / 2) ≤ Cin (π * n / 2) := fun m hm hmn =>
    Cin_mono (by positivity) (by nlinarith)
  rcases le_or_gt n 10 with h10 | h10
  · have hc6 := cin_val6
    have : Cin (π * 6 / 2) ≤ Cin (π * n / 2) := by
      have := hCm 6 (by norm_num) hnr; rwa [show (6 : ℝ) * π / 2 = π * 6 / 2 by ring] at this
    have hn10 : (n : ℝ) ≤ 10 := by exact_mod_cast h10
    nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  rcases le_or_gt n 20 with h20 | h20
  · have hc11 := cinH11
    have : Cin (22 * π / 4) ≤ Cin (π * n / 2) := by
      have := hCm 11 (by norm_num) (by exact_mod_cast (show (11 : ℤ) ≤ n by omega))
      rwa [show (11 : ℝ) * π / 2 = 22 * π / 4 by ring] at this
    have hn20 : (n : ℝ) ≤ 20 := by exact_mod_cast h20
    nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  rcases le_or_gt n 60 with h60 | h60
  · have hc21 := cinH21
    have : Cin (42 * π / 4) ≤ Cin (π * n / 2) := by
      have := hCm 21 (by norm_num) (by exact_mod_cast (show (21 : ℤ) ≤ n by omega))
      rwa [show (21 : ℝ) * π / 2 = 42 * π / 4 by ring] at this
    have hn60 : (n : ℝ) ≤ 60 := by exact_mod_cast h60
    nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  · have hc61 := cinH61
    have : Cin (122 * π / 4) ≤ Cin (π * n / 2) := by
      have := hCm 61 (by norm_num) (by exact_mod_cast (show (61 : ℤ) ≤ n by omega))
      rwa [show (61 : ℝ) * π / 2 = 122 * π / 4 by ring] at this
    nlinarith [mul_le_mul_of_nonneg_left hD2 hc0]

theorem tailB_all {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ 0.9803) (n : ℤ) (hn : n ∉ lowS) :
    2.8 ≤ modeE a n - c * primeD a (Real.log 2) n := by
  rcases not_mem_lowS hn with h | h
  · exact tailB_pos ha hlo ha2 hc0 hc h
  · have e := modeE_neg a (-n)
    have e2 := primeD_neg a (Real.log 2) (-n)
    rw [neg_neg] at e e2
    rw [e, e2]; exact tailB_pos ha hlo ha2 hc0 hc (by omega)

theorem pm_leB1 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 1 ≤ (0.0031 : ℝ) := by
  have h1 := pm_le ha hp hn 1 (0.9 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0.9 : ℝ)] at h1
  have hc := cval1
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0.9 : ℝ)]

theorem termB1 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((0.5408 : ℝ) + a * 0.36338 - errK a - c * (0.01553 * 1) - 2.8) * 0.0031
      ≤ (modeE a 1 - c * primeD a (Real.log 2) 1 - 2.8) * pm a g 1 := by
  have hψ := modeE_ge ha (by linarith) (n := 1) (by norm_num)
  have hcv := cin_val1
  have hd := dlo1
  have hC : Cin (π * ((1 : ℤ) : ℝ) / 2) = Cin (π * 1 / 2) := by push_cast; rfl
  rw [hC] at hψ
  have hD := primeD_small hlo ha2 1
  rw [show |(((1 : ℤ) : ℝ))| = 1 by norm_num] at hD
  refine term_ge ?_ ?_ (pm_nonneg ha g 1) (pm_leB1 ha ha2 hp hn h0)
  · nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  · have hl1 := Real.log_two_gt_d9
    have ha' : (0.3465 : ℝ) ≤ a := by linarith
    have : (0.02 : ℝ) ≤ errK a := by
      unfold errK
      have : (0.3465 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha' 2
      nlinarith [pow_pos ha 3, pow_pos ha 4, pow_pos ha 5]
    nlinarith [mul_nonneg hc0 (primeD_nonneg a (Real.log 2) 1)]

theorem pm_leB2 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 2 ≤ (0.0254 : ℝ) := by
  have h1 := pm_le ha hp hn 2 (0.6366 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0.6366 : ℝ)] at h1
  have hc := cval2
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0.6366 : ℝ)]

theorem termB2 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((1.6214 : ℝ) + a * 1 - errK a - c * (0.01553 * 2) - 2.8) * 0.0254
      ≤ (modeE a 2 - c * primeD a (Real.log 2) 2 - 2.8) * pm a g 2 := by
  have hψ := modeE_ge ha (by linarith) (n := 2) (by norm_num)
  have hcv := cin_val2
  have hd := dlo2
  have hC : Cin (π * ((2 : ℤ) : ℝ) / 2) = Cin (π * 2 / 2) := by push_cast; rfl
  rw [hC] at hψ
  have hD := primeD_small hlo ha2 2
  rw [show |(((2 : ℤ) : ℝ))| = 2 by norm_num] at hD
  refine term_ge ?_ ?_ (pm_nonneg ha g 2) (pm_leB2 ha ha2 hp hn h0)
  · nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  · have hl1 := Real.log_two_gt_d9
    have ha' : (0.3465 : ℝ) ≤ a := by linarith
    have : (0.02 : ℝ) ≤ errK a := by
      unfold errK
      have : (0.3465 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha' 2
      nlinarith [pow_pos ha 3, pow_pos ha 4, pow_pos ha 5]
    nlinarith [mul_nonneg hc0 (primeD_nonneg a (Real.log 2) 2)]

theorem pm_leB3 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 3 ≤ (0.07988 : ℝ) := by
  have h1 := pm_le ha hp hn 3 (0.3 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0.3 : ℝ)] at h1
  have hc := cval3
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0.3 : ℝ)]

theorem termB3 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((2.2965 : ℝ) + a * 1.212206 - errK a - c * (0.01553 * 3) - 2.8) * 0.07988
      ≤ (modeE a 3 - c * primeD a (Real.log 2) 3 - 2.8) * pm a g 3 := by
  have hψ := modeE_ge ha (by linarith) (n := 3) (by norm_num)
  have hcv := cin_val3
  have hd := dlo3
  have hC : Cin (π * ((3 : ℤ) : ℝ) / 2) = Cin (π * 3 / 2) := by push_cast; rfl
  rw [hC] at hψ
  have hD := primeD_small hlo ha2 3
  rw [show |(((3 : ℤ) : ℝ))| = 3 by norm_num] at hD
  refine term_ge ?_ ?_ (pm_nonneg ha g 3) (pm_leB3 ha ha2 hp hn h0)
  · nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  · have hl1 := Real.log_two_gt_d9
    have ha' : (0.3465 : ℝ) ≤ a := by linarith
    have : (0.02 : ℝ) ≤ errK a := by
      unfold errK
      have : (0.3465 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha' 2
      nlinarith [pow_pos ha 3, pow_pos ha 4, pow_pos ha 5]
    nlinarith [mul_nonneg hc0 (primeD_nonneg a (Real.log 2) 3)]

theorem pm_leB4 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 4 ≤ (0.13125 : ℝ) := by
  have h1 := pm_le ha hp hn 4 (0 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (0 : ℝ)] at h1
  have hc := cval4
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (0 : ℝ)]

theorem termB4 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((2.4081 : ℝ) + a * 1 - errK a - c * (0.01553 * 4) - 2.8) * 0.13125
      ≤ (modeE a 4 - c * primeD a (Real.log 2) 4 - 2.8) * pm a g 4 := by
  have hψ := modeE_ge ha (by linarith) (n := 4) (by norm_num)
  have hcv := cin_val4
  have hd := dlo4
  have hC : Cin (π * ((4 : ℤ) : ℝ) / 2) = Cin (π * 4 / 2) := by push_cast; rfl
  rw [hC] at hψ
  have hD := primeD_small hlo ha2 4
  rw [show |(((4 : ℤ) : ℝ))| = 4 by norm_num] at hD
  refine term_ge ?_ ?_ (pm_nonneg ha g 4) (pm_leB4 ha ha2 hp hn h0)
  · nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  · have hl1 := Real.log_two_gt_d9
    have ha' : (0.3465 : ℝ) ≤ a := by linarith
    have : (0.02 : ℝ) ≤ errK a := by
      unfold errK
      have : (0.3465 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha' 2
      nlinarith [pow_pos ha 3, pow_pos ha 4, pow_pos ha 5]
    nlinarith [mul_nonneg hc0 (primeD_nonneg a (Real.log 2) 4)]

theorem pm_leB5 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : pm a g 5 ≤ (0.1395 : ℝ) := by
  have h1 := pm_le ha hp hn 5 (-0.18 : ℝ)
  rw [integral_cos_sub_sq ha (by norm_num) (-0.18 : ℝ)] at h1
  have hc := cval5
  have hI := integral_sq_perp ha (by linarith) hp hn h0
  have h8 : 0 < 8 * a := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h8]
  have ha4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have ha5 : a ^ 5 = a * a ^ 4 := by ring
  nlinarith [pow_pos ha 4, sq_nonneg (-0.18 : ℝ)]

theorem termB5 {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    ((2.4848 : ℝ) + a * 0.872676 - errK a - c * (0.01553 * 5) - 2.8) * 0.1395
      ≤ (modeE a 5 - c * primeD a (Real.log 2) 5 - 2.8) * pm a g 5 := by
  have hψ := modeE_ge ha (by linarith) (n := 5) (by norm_num)
  have hcv := cin_val5
  have hd := dlo5
  have hC : Cin (π * ((5 : ℤ) : ℝ) / 2) = Cin (π * 5 / 2) := by push_cast; rfl
  rw [hC] at hψ
  have hD := primeD_small hlo ha2 5
  rw [show |(((5 : ℤ) : ℝ))| = 5 by norm_num] at hD
  refine term_ge ?_ ?_ (pm_nonneg ha g 5) (pm_leB5 ha ha2 hp hn h0)
  · nlinarith [mul_le_mul_of_nonneg_left hD hc0]
  · have hl1 := Real.log_two_gt_d9
    have ha' : (0.3465 : ℝ) ≤ a := by linarith
    have : (0.02 : ℝ) ≤ errK a := by
      unfold errK
      have : (0.3465 : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha' 2
      nlinarith [pow_pos ha 3, pow_pos ha 4, pow_pos ha 5]
    nlinarith [mul_nonneg hc0 (primeD_nonneg a (Real.log 2) 5)]

theorem pole_poly_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) :
    4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2 ≤ 4 * a + 0.34 * a ^ 3 := by
  have h6p : a ^ 6 ≤ 0.35 ^ 6 := pow_le_pow_left₀ ha.le ha2 6
  have h4p : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have h8 : a ^ 8 ≤ 0.35 ^ 6 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 6]
  have h6 : a ^ 6 ≤ 0.35 ^ 4 * a ^ 2 := by nlinarith [pow_pos ha 2, pow_pos ha 4]
  have e : 4 * a * (1 + a ^ 2 / 24 + a ^ 4 / 1600) ^ 2
      = 4 * a + a ^ 3 / 3 + a * (43 * a ^ 4 / 3600 + a ^ 6 / 4800 + a ^ 8 / 640000) := by ring
  rw [e]
  have : 43 * a ^ 4 / 3600 + a ^ 6 / 4800 + a ^ 8 / 640000 ≤ 0.0066 * a ^ 2 := by
    have h4 : a ^ 4 ≤ 0.35 ^ 2 * a ^ 2 := by nlinarith [pow_pos ha 2]
    norm_num at h4 h6 h8 ⊢; nlinarith [pow_pos ha 2]
  have h3 : a * (43 * a ^ 4 / 3600 + a ^ 6 / 4800 + a ^ 8 / 640000) ≤ a * (0.0066 * a ^ 2) :=
    mul_le_mul_of_nonneg_left this ha.le
  nlinarith

theorem autocorr_box_nonneg (a u : ℝ) : 0 ≤ autocorr (box a) u := by
  unfold autocorr
  refine integral_nonneg fun t => mul_nonneg ?_ ?_ <;>
  · rw [box_apply]; split_ifs <;> positivity

/-- **The gap past the first prime**: for `log 2 ≤ 2a ≤ 0.7`, every normalised probe `g` with
`ĝ(i/2) = 0` has `Q(g) ≥ Q(box) + 1/40`. -/
theorem weilQ_perp_ge_sliver {a : ℝ} (ha : 0 < a) (hlo : Real.log 2 ≤ 2 * a) (ha2 : a ≤ 0.35)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    weilQ a (box a) + 1 / 40 ≤ weilQ a g := by
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have ha' : (0.3465 : ℝ) ≤ a := by linarith
  set c := 2 * (Real.log 2 / Real.sqrt 2) with hcdef
  obtain ⟨-, -, hs1, hs2, -⟩ := num_atoms
  have hc0 : 0 ≤ c := by positivity
  have hc : c ≤ 0.9803 := by
    have e : c = Real.sqrt 2 * Real.log 2 := by
      rw [hcdef]; field_simp; rw [Real.sq_sqrt (by norm_num)]
    rw [e]; nlinarith
  have hQ : ∀ h, Probe a h → normSq h = 1 →
      weilQ a h = 2 * poleR h a ^ 2 + weilConst + archE h - c * autocorr h (Real.log 2) := by
    intro h hh hhn
    rw [weilQ_eq', primeS_eq_two (by linarith) hh, hhn, hcdef]; ring
  rw [hQ g hp hn, hQ _ (box_probe a) (normSq_box ha), h0, archE_split ha hp hn,
    archE_split ha (box_probe a) (normSq_box ha)]
  have hu0 : 0 ≤ Real.log 2 := by linarith
  have hE := energy_prime_trunc ha hp hn hu0 hlo hc0 lowS (tailB_all ha hlo ha2 hc0 hc)
  have hsum : ∑ n ∈ lowS, (modeE a n - c * primeD a (Real.log 2) n - 2.8) * pm a g n
      = (modeE a 0 - c * primeD a (Real.log 2) 0 - 2.8) * pm a g 0
        + 2 * ((modeE a 1 - c * primeD a (Real.log 2) 1 - 2.8) * pm a g 1
          + (modeE a 2 - c * primeD a (Real.log 2) 2 - 2.8) * pm a g 2
          + (modeE a 3 - c * primeD a (Real.log 2) 3 - 2.8) * pm a g 3
          + (modeE a 4 - c * primeD a (Real.log 2) 4 - 2.8) * pm a g 4
          + (modeE a 5 - c * primeD a (Real.log 2) 5 - 2.8) * pm a g 5) := by
    have hm : ∀ k : ℤ, modeE a (-k) = modeE a k := modeE_neg a
    have hd : ∀ k : ℤ, primeD a (Real.log 2) (-k) = primeD a (Real.log 2) k := primeD_neg a _
    have hq : ∀ k : ℤ, pm a g (-k) = pm a g k := pm_neg ha hp
    simp only [lowS]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [show (-5 : ℤ) = -(5 : ℤ) from rfl, show (-4 : ℤ) = -(4 : ℤ) from rfl,
      show (-3 : ℤ) = -(3 : ℤ) from rfl, show (-2 : ℤ) = -(2 : ℤ) from rfl,
      show (-1 : ℤ) = -(1 : ℤ) from rfl, hm, hm, hm, hm, hm, hd, hd, hd, hd, hd, hq, hq, hq, hq, hq]
    ring
  rw [hsum] at hE
  have h0t : (0 - 0 - 2.8) * (a ^ 4 / 240)
      ≤ (modeE a 0 - c * primeD a (Real.log 2) 0 - 2.8) * pm a g 0 := by
    rw [modeE_zero, show primeD a (Real.log 2) 0 = 0 by simp [primeD]]
    have := pm_zero_le ha (by linarith) hp hn h0
    nlinarith [pm_nonneg ha g 0]
  have t1 := termB1 ha hlo ha2 hp hn h0 hc0
  have t2 := termB2 ha hlo ha2 hp hn h0 hc0
  have t3 := termB3 ha hlo ha2 hp hn h0 hc0
  have t4 := termB4 ha hlo ha2 hp hn h0 hc0
  have t5 := termB5 ha hlo ha2 hp hn h0 hc0
  have hB := nearField_box_le' ha
  have hP := pole_box_le ha (by linarith)
  have hfb := autocorr_box_nonneg a (Real.log 2)
  have hcf : 0 ≤ c * autocorr (box a) (Real.log 2) := mul_nonneg hc0 hfb
  have herr : errK a ≤ 0.0349 := by
    unfold errK
    have h2 : a ^ 2 ≤ 0.35 ^ 2 := pow_le_pow_left₀ ha.le ha2 2
    have h3 : a ^ 3 ≤ 0.35 ^ 3 := pow_le_pow_left₀ ha.le ha2 3
    have h4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
    have h5 : a ^ 5 ≤ 0.35 ^ 5 := pow_le_pow_left₀ ha.le ha2 5
    norm_num at h2 h3 h4 h5 ⊢; linarith
  have ha4 : a ^ 4 ≤ 0.35 ^ 4 := pow_le_pow_left₀ ha.le ha2 4
  have hpole := pole_poly_le ha ha2
  have ha3 : a ^ 3 ≤ 0.35 ^ 3 := pow_le_pow_left₀ ha.le ha2 3
  linarith

/-- **Certified lower bound orthogonally to `w` for every `0 < a ≤ 0.35`**: `λ_⊥ ≥ λ₁ + 1/40`. -/
theorem weilQ0_perp_ge_035 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : lam a + 1 / 40 ≤ weilQ0 a g := by
  have hQ : weilQ a (box a) + 1 / 40 ≤ weilQ a g := by
    rcases lt_or_ge (2 * a) (Real.log 2) with h | h
    · have := weilQ_perp_ge_fourier ha h hp hn h0; linarith
    · exact weilQ_perp_ge_sliver ha h ha2 hp hn h0
  have hQ0 : weilQ0 a g = weilQ a g := by unfold weilQ0; rw [h0]; ring
  have hlam := lam_le (box_probe a) (normSq_box ha)
  rw [hQ0]; linarith

/-- **The ground state of `Q` is unique up to sign for every `0 < a ≤ 0.35`.** -/
theorem groundState_unique_035 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.35) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  refine groundState_unique ha (fun v hv hv0 => ?_) hg hh
  have h1 := weilQ0_perp_ge_035 ha ha2 hv.1 hv.2.1 hv0
  have h3 : weilQ0 a v = weilQ a v := by unfold weilQ0; rw [hv0]; ring
  have h2 : weilQ a v = lam a := by
    have := ((isGroundState_iff ha).1 hv).1.2; rw [this, hv.2.1, mul_one]
  linarith

end Pilot1ca

#print axioms Pilot1ca.hasSum_one_sub_autocorr
#print axioms Pilot1ca.energy_ge_trunc
#print axioms Pilot1ca.kerK_ge_taylor
#print axioms Pilot1ca.modeE_ge
#print axioms Pilot1ca.cin_val6
#print axioms Pilot1ca.cinH61
#print axioms Pilot1ca.cs_supp
#print axioms Pilot1ca.integral_sq_perp
#print axioms Pilot1ca.pm_le
#print axioms Pilot1ca.nearField_fourier
#print axioms Pilot1ca.weilQ_perp_ge_fourier
#print axioms Pilot1ca.weilQ0_perp_ge_fourier
#print axioms Pilot1ca.groundState_unique_below_log2
#print axioms Pilot1ca.primeS_eq_two
#print axioms Pilot1ca.energy_prime_trunc
#print axioms Pilot1ca.tailB_all
#print axioms Pilot1ca.weilQ_perp_ge_sliver
#print axioms Pilot1ca.weilQ0_perp_ge_035
#print axioms Pilot1ca.groundState_unique_035
