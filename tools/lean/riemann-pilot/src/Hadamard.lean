import Mathlib

/-! # Hadamard's factorisation in genus zero

An entire function `F` with `F(0) ≠ 0` and `‖F w‖ ≤ C exp(A‖w‖^α)` for some `α < 1` is the product
over its zeros (with multiplicity): `F(w) = F(0)Π(1 − w/u)`, with `Σ 1/|u| < ∞`.

The proof uses only circle averages, all available in Mathlib: Jensen's formula, the Poisson
formula for harmonic functions, harmonic conjugates on discs and Borel–Carathéodory.
* **A (`disc_estimate`).** If `G` is analytic and zero-free on `|w| ≤ R` with `G(0) = 1`, then
  `‖G − 1‖` on `|w| ≤ r` is controlled by the circle average of `log⁺|G|` on `|w| = R`.
* **B.** Jensen bounds the zero count by `O(R^α)`, so `Σ 1/|u| < ∞`.
* **C.** On each disc, `F = F(0)·P_R·G_R`, where `P_R` is the finite product over the zeros inside.
  The circle average of `log⁺|G_R|` is `O(R^α)`, so `G_R → 1` and `F/F(0) = Π(1 − w/u)`. -/

open Real Filter Topology Metric Complex MeromorphicOn

noncomputable section

namespace Pilot1ca

/-! ## A. The disc estimate -/

/-- **The disc estimate.** Let `G` be analytic and zero-free on the closed disc `|w| ≤ R`, with
`G(0) = 1`, and let the circle average of `log⁺|G|` over `|w| = R` be at most `M`. Then on
`|w| ≤ r < R/2`, `‖G w − 1‖ ≤ 2·6Mr/(R/2 − r)` whenever `6Mr/(R/2 − r) ≤ 1`.

The proof has three steps. Poisson bounds `log|G| ≤ 3M` on `|w| < R/2`. A harmonic conjugate gives
`G = e^H` with `H(0) = 0`. Borel–Carathéodory then bounds `H`. -/
theorem disc_estimate {G : ℂ → ℂ} {R r M : ℝ} (hR : 0 < R) (_hr : 0 ≤ r) (hrR : r < R / 2)
    (hG : AnalyticOnNhd ℂ G (closedBall 0 R)) (hG0 : ∀ z ∈ closedBall (0 : ℂ) R, G z ≠ 0)
    (hG1 : G 0 = 1) (hMpos : 0 < M)
    (hM : Real.circleAverage (fun z => max (Real.log ‖G z‖) 0) 0 R ≤ M)
    (hsmall : 6 * M * r / (R / 2 - r) ≤ 1) :
    ∀ w ∈ closedBall (0 : ℂ) r, ‖G w - 1‖ ≤ 2 * (6 * M * r / (R / 2 - r)) := by
  set u : ℂ → ℝ := fun z => Real.log ‖G z‖ with hu
  -- `u` is harmonic near the closed disc
  have hharm : InnerProductSpace.HarmonicOnNhd u (closedBall 0 R) :=
    fun z hz => (hG z hz).harmonicAt_log_norm (hG0 z hz)
  have hcl : InnerProductSpace.HarmonicContOnCl u (ball 0 R) := by
    apply InnerProductSpace.HarmonicOnNhd.harmonicContOnCl
    rwa [closure_ball 0 hR.ne']
  -- continuity of `u` on the circle
  have hucont : ContinuousOn u (sphere 0 R) :=
    hharm.continuousOn.mono sphere_subset_closedBall
  have hupos : ContinuousOn (fun z => max (u z) 0) (sphere 0 R) :=
    ContinuousOn.sup hucont continuousOn_const
  -- Step 1: `u ≤ 3M` on the ball of radius `R/2`
  have hup : ∀ w ∈ ball (0 : ℂ) (R / 2), u w ≤ 3 * M := by
    intro w hw
    have hwR : w ∈ ball (0 : ℂ) R := ball_subset_ball (by linarith) hw
    have hP := InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul hcl hwR
    rw [← hP]
    have hw2 : ‖w‖ < R / 2 := by simpa using hw
    have hK : ContinuousOn (fun z => (herglotzRieszKernel 0 w z).re) (sphere 0 R) := by
      intro z hz
      have hzw : z - w ≠ 0 := by
        intro h
        have : ‖z‖ = R := by simpa using hz
        rw [sub_eq_zero] at h; rw [h] at this; linarith
      apply ContinuousAt.continuousWithinAt
      apply Complex.continuous_re.continuousAt.comp
      rw [herglotzRieszKernel_fun_def]
      simp only [sub_zero]
      exact (continuousAt_id.add continuousAt_const).div (continuousAt_id.sub continuousAt_const) hzw
    calc Real.circleAverage ((re ∘ herglotzRieszKernel 0 w) • u) 0 R
        ≤ Real.circleAverage (fun z => 3 * max (u z) 0) 0 R := by
          apply Real.circleAverage_mono
          · exact (hK.smul hucont).circleIntegrable hR.le
          · exact (continuousOn_const.mul hupos).circleIntegrable hR.le
          · intro z hz
            rw [abs_of_pos hR] at hz
            have hk1 := re_herglotzRieszKernel_le (c := 0) hz hwR
            have hk0 := le_re_herglotzRieszKernel (c := 0) hz hwR
            simp only [sub_zero] at hk1 hk0
            have hwn : ‖w‖ < R / 2 := hw2
            have h3 : (R + ‖w‖) / (R - ‖w‖) ≤ 3 := by
              rw [div_le_iff₀ (by linarith)]; linarith
            have hk0' : 0 ≤ (herglotzRieszKernel 0 w z).re := by
              simp only [herglotzRieszKernel_def, sub_zero]
              exact le_trans (div_nonneg (by linarith) (by linarith [norm_nonneg w])) hk0
            have hk1' : (herglotzRieszKernel 0 w z).re ≤ 3 := by
              simp only [herglotzRieszKernel_def, sub_zero]; linarith
            simp only [smul_eq_mul]
            calc (herglotzRieszKernel 0 w z).re * u z
                ≤ (herglotzRieszKernel 0 w z).re * max (u z) 0 :=
                  mul_le_mul_of_nonneg_left (le_max_left _ _) hk0'
              _ ≤ 3 * max (u z) 0 :=
                  mul_le_mul_of_nonneg_right hk1' (le_max_right _ _)
      _ = 3 * Real.circleAverage (fun z => max (u z) 0) 0 R := by
          rw [← smul_eq_mul, ← Real.circleAverage_smul]; rfl
      _ ≤ 3 * M := by linarith
  -- Step 2: a harmonic conjugate, normalised at `0`
  obtain ⟨H₀, hH₀, hH₀re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
      (hharm.mono ball_subset_closedBall : InnerProductSpace.HarmonicOnNhd u (ball 0 R))
  set H : ℂ → ℂ := fun z => H₀ z - I * (H₀ 0).im with hHdef
  have h0R : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hH : AnalyticOnNhd ℂ H (ball 0 R) := fun z hz => (hH₀ z hz).sub analyticAt_const
  have hHre : ∀ z ∈ ball (0 : ℂ) R, (H z).re = u z := by
    intro z hz; simp [hHdef, hH₀re hz]
  have hH0 : H 0 = 0 := by
    apply Complex.ext
    · rw [hHre 0 h0R]; simp [hu, hG1]
    · simp [hHdef]
  -- Step 3: `G = e^H` on the ball (`G e^{−H}` has modulus one)
  have hGH : ∀ z ∈ ball (0 : ℂ) R, G z = Complex.exp (H z) := by
    set φ : ℂ → ℂ := fun z => G z * Complex.exp (-H z)
    have hφ : DifferentiableOn ℂ φ (ball 0 R) := fun z hz =>
      ((hG z (ball_subset_closedBall hz)).differentiableAt.mul
        (hH z hz).differentiableAt.neg.cexp).differentiableWithinAt
    have hnorm : ∀ z ∈ ball (0 : ℂ) R, ‖φ z‖ = 1 := by
      intro z hz
      have hz' := hG0 z (ball_subset_closedBall hz)
      simp only [φ, norm_mul, Complex.norm_exp, neg_re, hHre z hz, hu]
      rw [Real.exp_neg, Real.exp_log (norm_pos_iff.2 hz')]
      field_simp
    have hmax : IsMaxOn (norm ∘ φ) (ball 0 R) 0 := by
      intro z hz
      simp only [Set.mem_ofPred_eq, Function.comp_apply, hnorm z hz, hnorm 0 h0R, le_refl]
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 R).isPreconnected
      isOpen_ball hφ h0R hmax
    intro z hz
    have h1 : φ z = 1 := by
      rw [hconst hz]; simp [φ, hG1, hH0]
    have hne : Complex.exp (-H z) ≠ 0 := Complex.exp_ne_zero _
    calc G z = φ z / Complex.exp (-H z) := by simp [φ, hne]
      _ = Complex.exp (H z) := by rw [h1, Complex.exp_neg]; field_simp
  -- Step 4: Borel–Carathéodory on the ball of radius `R/2`
  intro w hw
  have hw' : ‖w‖ ≤ r := by simpa using hw
  have hwb : w ∈ ball (0 : ℂ) (R / 2) := by rw [mem_ball_zero_iff]; linarith
  have hBC := Complex.borelCaratheodory (M := 3 * M) (by linarith)
    (hH.differentiableOn.mono (ball_subset_ball (by linarith))) (fun z hz => by
      show (H z).re ≤ 3 * M
      rw [hHre z (ball_subset_ball (by linarith) hz)]; exact hup z hz) (by linarith) hwb
  rw [hH0, norm_zero, zero_mul, zero_div, add_zero] at hBC
  have hHw : ‖H w‖ ≤ 6 * M * r / (R / 2 - r) := by
    refine hBC.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have : 0 ≤ M := hMpos.le
    nlinarith [norm_nonneg w, mul_nonneg (mul_nonneg this hR.le) (sub_nonneg.2 hw')]
  rw [hGH w (ball_subset_ball (show R / 2 ≤ R by linarith) hwb)]
  calc ‖Complex.exp (H w) - 1‖ ≤ 2 * ‖H w‖ := Complex.norm_exp_sub_one_le (hHw.trans hsmall)
    _ ≤ 2 * (6 * M * r / (R / 2 - r)) := by linarith

/-! ## B. Zeros and their count -/

/-- The order of the zero of `F` at `u` (`0` off the zeros). -/
def ordN (F : ℂ → ℂ) (u : ℂ) : ℕ := (analyticOrderAt F u).toNat

theorem order_ne_top {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (u : ℂ) :
    analyticOrderAt F u ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u (fun z => hF.analyticAt z)]
  intro h; exact hF0 (by simp [h])

theorem divisor_ball_eq {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {R : ℝ} {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) R) :
    MeromorphicOn.divisor F (closedBall 0 R) u = ordN F u := by
  rw [AnalyticOnNhd.divisor_apply (fun z _ => hF.analyticAt z) hu]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (order_ne_top hF hF0 u)
  rw [ordN, ← hn]
  simp

theorem ordN_ne_zero_iff {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (u : ℂ) :
    ordN F u ≠ 0 ↔ F u = 0 := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (order_ne_top hF hF0 u)
  have h := analyticOrderAt_ne_zero (f := F) (z₀ := u)
  rw [ordN, ← hn, ENat.toNat_natCast]
  constructor
  · intro hn0
    have : analyticOrderAt F u ≠ 0 := by rw [← hn]; exact_mod_cast hn0
    exact (h.1 this).2
  · intro hz
    have := h.2 ⟨hF.analyticAt u, hz⟩
    rw [← hn] at this; exact_mod_cast this

/-- **Jensen's bound on the zero count**: for zeros `u` in `|u| ≤ R`, counted with multiplicity,
`Σ ord(u) ≤ log C + A(eR)^α − log‖F(0)‖` when `‖F w‖ ≤ C exp(A‖w‖^α)`. -/
theorem zero_count {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {C A α : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hgrowth : ∀ w, ‖F w‖ ≤ C * Real.exp (A * ‖w‖ ^ α)) {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (hS : ∀ u ∈ S, ‖u‖ ≤ R) :
    (∑ u ∈ S, (ordN F u : ℝ)) ≤ Real.log C + A * (Real.exp 1 * R) ^ α - Real.log ‖F 0‖ := by
  set M := C * Real.exp (A * (Real.exp 1 * R) ^ α) with hMdef
  have he : 1 < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hM : 1 ≤ M := by
    have : 1 ≤ Real.exp (A * (Real.exp 1 * R) ^ α) := Real.one_le_exp (by positivity)
    nlinarith
  have hJ := AnalyticOnNhd.sum_divisor_le (c := 0) (r := R) (R := Real.exp 1 * R) (M := M)
    (by rw [abs_of_pos hR]; exact hR)
    (by rw [abs_of_pos hR, abs_of_pos (by positivity)]; nlinarith)
    hM (fun z _ => hF.analyticAt z) hF0 (by
      intro z hz
      rw [abs_of_pos (by positivity)] at hz
      have hz' : ‖z‖ = Real.exp 1 * R := by simpa using hz
      rw [hMdef, ← hz']; exact hgrowth z)
  rw [abs_of_pos hR] at hJ
  have hlog : Real.log (Real.exp 1 * R / R) = 1 := by
    rw [mul_div_assoc, div_self hR.ne', mul_one, Real.log_exp]
  have hlogM : Real.log (M / ‖F 0‖) = Real.log C + A * (Real.exp 1 * R) ^ α - Real.log ‖F 0‖ := by
    rw [Real.log_div (by positivity) (norm_ne_zero_iff.2 hF0), hMdef,
      Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
  rw [hlog, div_one, hlogM] at hJ
  refine le_trans ?_ hJ
  -- the finite sum over `S` is at most the finsum over the divisor's support
  set D := MeromorphicOn.divisor F (closedBall (0 : ℂ) R)
  have hfin := D.finiteSupport (isCompact_closedBall (0 : ℂ) R)
  have hDnn : ∀ u, 0 ≤ D u := fun u => AnalyticOnNhd.divisor_nonneg (fun z _ => hF.analyticAt z) u
  have hsum : ∑ᶠ u, D u = ∑ u ∈ hfin.toFinset ∪ S, D u :=
    finsum_eq_sum_of_support_subset _ (fun u hu => by simp [hu])
  rw [hsum]
  push_cast
  calc (∑ u ∈ S, (ordN F u : ℝ)) = ∑ u ∈ S, ((D u : ℤ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [divisor_ball_eq hF hF0 (by simpa using hS u hu)]; push_cast; rfl
    _ ≤ ∑ u ∈ hfin.toFinset ∪ S, ((D u : ℤ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun u _ _ => by exact_mod_cast hDnn u)

/-- `F` has no zeros near `0`. -/
theorem exists_zero_free_ball {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) :
    ∃ m > 0, ∀ u, ‖u‖ < m → F u ≠ 0 := by
  obtain ⟨m, hm, h⟩ := Metric.eventually_nhds_iff.1 (hF.continuous.continuousAt.eventually_ne hF0)
  exact ⟨m, hm, fun u hu => h (by simpa using hu)⟩

/-- The count in the form `n(R) ≤ K + A₁R^α`, `K = |log C − log‖F(0)‖|`, `A₁ = Ae^α`. -/
theorem zero_count' {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {C A α : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (_hα0 : 0 ≤ α)
    (hgrowth : ∀ w, ‖F w‖ ≤ C * Real.exp (A * ‖w‖ ^ α)) {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (hS : ∀ u ∈ S, ‖u‖ ≤ R) :
    (∑ u ∈ S, (ordN F u : ℝ))
      ≤ |Real.log C - Real.log ‖F 0‖| + A * Real.exp 1 ^ α * R ^ α := by
  refine (zero_count hF hF0 hC hA hgrowth hR S hS).trans ?_
  rw [Real.mul_rpow (Real.exp_pos 1).le hR.le]
  have := le_abs_self (Real.log C - Real.log ‖F 0‖)
  nlinarith

/-- **`Σ ord(u)/|u| < ∞`** over the zeros, for `α < 1`: dyadic shells `2^j m ≤ |u| < 2^{j+1} m`
each carry at most `K + A₁(2^{j+1}m)^α` zeros. -/
theorem summable_ord_div {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {C A α : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hgrowth : ∀ w, ‖F w‖ ≤ C * Real.exp (A * ‖w‖ ^ α)) :
    Summable (fun u : ℂ => (ordN F u : ℝ) / ‖u‖) := by
  obtain ⟨m, hm, hmz⟩ := exists_zero_free_ball hF hF0
  set K := |Real.log C - Real.log ‖F 0‖|
  set A₁ := A * Real.exp 1 ^ α
  have hK : 0 ≤ K := abs_nonneg _
  have hA₁ : 0 ≤ A₁ := by positivity
  set term : ℕ → ℝ := fun j => (K + A₁ * (2 ^ (j + 1) * m) ^ α) / (2 ^ j * m)
  -- the dyadic series is geometric
  have hq : (2 : ℝ) ^ (α - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ (2 : ℝ) ^ (α - 1) := by positivity
  have hterm : ∀ j : ℕ, term j = K / m * (1 / 2) ^ j
      + A₁ * 2 ^ α * m ^ (α - 1) * ((2 : ℝ) ^ (α - 1)) ^ j := by
    intro j
    simp only [term]
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    rw [Real.mul_rpow (by positivity) hm.le, pow_succ, Real.mul_rpow (by positivity) (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 ^ (α - 1)) j,
      ← Real.rpow_mul (by norm_num), Real.rpow_sub hm, Real.rpow_one]
    have e1 : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ (j : ℝ) := by
      rw [div_pow, one_pow, Real.rpow_natCast]
    have e2 : (2 : ℝ) ^ ((α - 1) * j) = (2 : ℝ) ^ ((j : ℝ) * α) / (2 : ℝ) ^ (j : ℝ) := by
      rw [← Real.rpow_sub (by norm_num)]; ring_nf
    rw [e1, e2, Real.rpow_natCast]
    field_simp
  have hsum : Summable term := by
    have h1 := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left (K / m)
    have h2 := (summable_geometric_of_lt_one hq0 hq).mul_left (A₁ * 2 ^ α * m ^ (α - 1))
    exact (h1.add h2).congr fun j => (hterm j).symm
  have hterm0 : ∀ j, 0 ≤ term j := fun j => by simp only [term]; positivity
  refine summable_of_sum_le (c := ∑' j, term j) (fun u => by positivity) (fun S => ?_)
  -- drop the non-zeros
  set S' := S.filter (fun u => ordN F u ≠ 0)
  have hS' : ∑ u ∈ S, (ordN F u : ℝ) / ‖u‖ = ∑ u ∈ S', (ordN F u : ℝ) / ‖u‖ := by
    rw [Finset.sum_filter_of_ne]
    intro u _ h h0; rw [h0] at h; simp at h
  rw [hS']
  have hbig : ∀ u ∈ S', m ≤ ‖u‖ := by
    intro u hu
    have hz := (ordN_ne_zero_iff hF hF0 u).1 (Finset.mem_filter.1 hu).2
    by_contra h; exact hmz u (lt_of_not_ge h) hz
  set J : ℂ → ℕ := fun u => Nat.log 2 ⌊‖u‖ / m⌋₊
  have hJ : ∀ u ∈ S', (2 : ℝ) ^ J u * m ≤ ‖u‖ ∧ ‖u‖ < 2 ^ (J u + 1) * m := by
    intro u hu
    have hx : 1 ≤ ‖u‖ / m := by rw [le_div_iff₀ hm]; linarith [hbig u hu]
    have hn : ⌊‖u‖ / m⌋₊ ≠ 0 := by
      have := Nat.floor_pos.2 hx; omega
    have h1 : 2 ^ J u ≤ ⌊‖u‖ / m⌋₊ := Nat.pow_log_le_self 2 hn
    have h2 : ⌊‖u‖ / m⌋₊ < 2 ^ (J u + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    constructor
    · have : ((2 ^ J u : ℕ) : ℝ) ≤ ‖u‖ / m :=
        le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
      rw [le_div_iff₀ hm] at this; exact_mod_cast this
    · have h3 : ‖u‖ / m < ((2 ^ (J u + 1) : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (‖u‖ / m)
        have h4 : ((⌊‖u‖ / m⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (J u + 1) : ℕ) : ℝ) := by
          exact_mod_cast h2
        linarith
      rw [div_lt_iff₀ hm] at h3; exact_mod_cast h3
  rw [← Finset.sum_fiberwise_of_maps_to (g := J) (t := S'.image J)
    (fun u hu => Finset.mem_image_of_mem J hu)]
  calc ∑ j ∈ S'.image J, ∑ u ∈ S' with J u = j, (ordN F u : ℝ) / ‖u‖
      ≤ ∑ j ∈ S'.image J, term j := by
        apply Finset.sum_le_sum
        intro j _
        have hfib : ∀ u ∈ S'.filter (fun u => J u = j),
            (ordN F u : ℝ) / ‖u‖ ≤ (ordN F u : ℝ) / (2 ^ j * m) := by
          intro u hu
          obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
          have := (hJ u hu1).1
          rw [hu2] at this
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) this
        refine (Finset.sum_le_sum hfib).trans ?_
        rw [← Finset.sum_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply zero_count' hF hF0 hC hA hα0 hgrowth (by positivity)
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        have := (hJ u hu1).2
        rw [hu2] at this
        exact this.le
    _ ≤ ∑' j, term j := hsum.sum_le_tsum _ (fun j _ => hterm0 j)

/-! ## C. The factorisation on a disc -/

/-- The zeros of `F` in `|u| ≤ R`, as a finite set. -/
def zerosIn (F : ℂ → ℂ) (R : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor F (closedBall (0 : ℂ) R)).finiteSupport (isCompact_closedBall 0 R)).toFinset

theorem mem_zerosIn {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {R : ℝ} {u : ℂ} :
    u ∈ zerosIn F R ↔ ‖u‖ ≤ R ∧ F u = 0 := by
  rw [zerosIn, Set.Finite.mem_toFinset, Function.mem_support]
  constructor
  · intro h
    have hu : u ∈ closedBall (0 : ℂ) R := by
      by_contra hu; exact h (by simp [MeromorphicOn.divisor, hu])
    refine ⟨by simpa using hu, (ordN_ne_zero_iff hF hF0 u).1 ?_⟩
    rw [divisor_ball_eq hF hF0 hu] at h; exact_mod_cast h
  · rintro ⟨hu, hz⟩
    rw [divisor_ball_eq hF hF0 (by simpa using hu)]
    exact_mod_cast (ordN_ne_zero_iff hF hF0 u).2 hz

theorem ne_zero_of_mem_zerosIn {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {R : ℝ}
    {u : ℂ} (hu : u ∈ zerosIn F R) : u ≠ 0 := by
  rintro rfl; exact hF0 ((mem_zerosIn hF hF0).1 hu).2

/-- **The factorisation on a disc**: `F(w) = F(0)·Π_{|u|≤R}(1 − w/u)^{ord u}·G(w)` on `|w| ≤ R`,
with `G` analytic and zero-free there and `G(0) = 1` (from Mathlib's `extract_zeros_poles`). -/
theorem disc_factor {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (closedBall 0 R) ∧ (∀ z ∈ closedBall (0 : ℂ) R, G z ≠ 0) ∧
      G 0 = 1 ∧ ∀ w ∈ closedBall (0 : ℂ) R,
        F w = F 0 * (∏ u ∈ zerosIn F R, (1 - w / u) ^ ordN F u) * G w := by
  set U := closedBall (0 : ℂ) R
  have hFa : AnalyticOnNhd ℂ F U := fun z _ => hF.analyticAt z
  have h₂ : ∀ u : U, meromorphicOrderAt F u ≠ ⊤ := by
    intro u
    rw [(hF.analyticAt u).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (order_ne_top hF hF0 u)
    rw [← hn]; simp
  obtain ⟨g, hg, hg0, hgeq⟩ := hFa.meromorphicOn.extract_zeros_poles h₂
    ((MeromorphicOn.divisor F U).finiteSupport (isCompact_closedBall 0 R))
  set Q : ℂ → ℂ := fun w => ∏ u ∈ zerosIn F R, (w - u) ^ ordN F u
  -- the finprod is `Q`
  have hQ : ∀ w, (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor F U u) w = Q w := by
    intro w
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := zerosIn F R) (by
      intro u hu
      rw [Function.mem_mulSupport] at hu
      rw [Finset.mem_coe, zerosIn, Set.Finite.mem_toFinset, Function.mem_support]
      intro h; apply hu; rw [h]; simp)]
    rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro u hu
    have hu' : u ∈ U := by simpa [U] using ((mem_zerosIn hF hF0).1 hu).1
    have hd : MeromorphicOn.divisor F U u = ordN F u := divisor_ball_eq hF hF0 hu'
    simp only [Pi.pow_apply]
    rw [hd, zpow_natCast]
  have hQc : Continuous Q := by
    simp only [Q]; fun_prop
  -- equality on the open ball, then on the closed ball
  have hball : Set.EqOn F (fun w => Q w * g w) (ball 0 R) := by
    intro x hx
    have hxU : x ∈ U := ball_subset_closedBall hx
    have hmem := (mem_codiscreteWithin_iff_forall_mem_nhdsWithin.1 hgeq) x hxU
    have hnhds : U \ {x} ∈ 𝓝[≠] x :=
      sdiff_mem_nhdsWithin_compl (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall) _
    have hev : F =ᶠ[𝓝[≠] x] fun w => Q w * g w := by
      have h1 : {w | F w = ((∏ᶠ u, (· - u) ^ MeromorphicOn.divisor F U u) • g) w} ∈ 𝓝[≠] x := by
        have := nhdsWithin_le_of_mem hnhds hmem
        exact this
      filter_upwards [h1] with w hw
      rw [hw, Pi.smul_apply', hQ, smul_eq_mul]
    have hc1 : ContinuousAt F x := hF.continuous.continuousAt
    have hc2 : ContinuousAt (fun w => Q w * g w) x :=
      hQc.continuousAt.mul (hg x hxU).continuousAt
    exact tendsto_nhds_unique_of_eventuallyEq (hc1.tendsto.mono_left nhdsWithin_le_nhds)
      (hc2.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hcl : Set.EqOn F (fun w => Q w * g w) U := by
    apply hball.of_subset_closure hF.continuous.continuousOn
      (hQc.continuousOn.mul (fun z hz => (hg z hz).continuousAt.continuousWithinAt))
      ball_subset_closedBall
    rw [closure_ball 0 hR.ne']
  have h0U : (0 : ℂ) ∈ U := by simp [U, hR.le]
  have hg00 : g 0 ≠ 0 := hg0 ⟨0, h0U⟩
  refine ⟨fun w => g w / g 0, fun z hz => (hg z hz).div_const, fun z hz => ?_, ?_, ?_⟩
  · exact div_ne_zero (hg0 ⟨z, hz⟩) hg00
  · simp [hg00]
  · intro w hw
    rw [hcl hw, hcl h0U]
    simp only [Q]
    have hsplit : ∀ u ∈ zerosIn F R, (w - u) ^ ordN F u = (0 - u) ^ ordN F u * (1 - w / u) ^ ordN F u := by
      intro u hu
      have hu0 := ne_zero_of_mem_zerosIn hF hF0 hu
      rw [← mul_pow]; congr 1; field_simp; ring
    rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib]
    field_simp

/-! ### Circle-average tools -/

/-- Monotonicity of circle averages when the inequality holds off a discrete subset of the circle. -/
theorem circleAverage_mono_codiscrete {f g : ℂ → ℝ} {R : ℝ} (hR : R ≠ 0)
    (hf : CircleIntegrable f 0 R) (hg : CircleIntegrable g 0 R)
    (h : {z | z ∈ sphere (0 : ℂ) |R| → f z ≤ g z} ∈ codiscreteWithin (sphere (0 : ℂ) |R|)) :
    Real.circleAverage f 0 R ≤ Real.circleAverage g 0 R := by
  rw [Real.circleAverage_def, Real.circleAverage_def, smul_eq_mul, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (by positivity))
  apply intervalIntegral.integral_mono_ae_restrict (by positivity) hf hg
  have hpre := circleMap_preimage_codiscrete (c := 0) hR h
  have hae := ae_restrict_le_codiscreteWithin (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := 2 * π))
  have h2 : (circleMap 0 R ⁻¹' {z | z ∈ sphere (0 : ℂ) |R| → f z ≤ g z})
      ∈ codiscreteWithin (Set.Icc (0 : ℝ) (2 * π)) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hpre
  filter_upwards [hae h2] with θ hθ
  exact hθ (circleMap_mem_sphere' 0 R θ)

/-- A finite exceptional set is codiscrete. -/
theorem mem_codiscreteWithin_of_finite {P : ℂ → Prop} {T : Set ℂ} (E : Finset ℂ)
    (hE : ∀ z, z ∉ E → P z) : {z | P z} ∈ codiscreteWithin T := by
  have h1 : ((E : Set ℂ)ᶜ) ∈ codiscrete ℂ := (Finset.finite_toSet E).compl_mem_codiscrete
  have h2 : ((E : Set ℂ)ᶜ) ∈ codiscreteWithin T := Filter.codiscreteWithin_mono (Set.subset_univ _) h1
  exact Filter.mem_of_superset h2 (fun z hz => hE z hz)

theorem circleIntegrable_const_mul {f : ℂ → ℝ} {R : ℝ} (a : ℝ) (hf : CircleIntegrable f 0 R) :
    CircleIntegrable (fun z => a * f z) 0 R :=
  (circleIntegrable_def _ _ _).2 (((circleIntegrable_def _ _ _).1 hf).const_mul a)

/-- `log‖1 − ζ/u‖` is circle integrable. -/
theorem circleIntegrable_log_one_sub (u : ℂ) (R : ℝ) :
    CircleIntegrable (fun ζ => Real.log ‖1 - ζ / u‖) 0 R := by
  have : MeromorphicOn (fun ζ : ℂ => 1 - ζ / u) (sphere 0 |R|) := by
    intro z _; fun_prop
  exact this.circleIntegrable_log_norm

/-- **The per-zero average**: for `0 < ‖u‖ ≤ R`, the circle average of `max(−log‖1 − ζ/u‖, 0)` over
`|ζ| = R` is at most `log 2`. -/
theorem circleAverage_negLog_le {u : ℂ} {R : ℝ} (hR : 0 < R) (hu0 : u ≠ 0) (huR : ‖u‖ ≤ R) :
    Real.circleAverage (fun ζ => max (-Real.log ‖1 - ζ / u‖) 0) 0 R ≤ Real.log 2 := by
  set ℓ := fun ζ : ℂ => Real.log ‖1 - ζ / u‖
  have hℓ : CircleIntegrable ℓ 0 R := circleIntegrable_log_one_sub u R
  have hpos : CircleIntegrable (fun ζ => max (ℓ ζ) 0) 0 R := by
    have e : (fun ζ => max (ℓ ζ) 0) = fun ζ => (1 / 2 : ℝ) * (|ℓ ζ| + ℓ ζ) := by
      funext ζ; rcases le_total (ℓ ζ) 0 with h | h
      · rw [max_eq_right h, abs_of_nonpos h]; ring
      · rw [max_eq_left h, abs_of_nonneg h]; ring
    rw [e]; exact circleIntegrable_const_mul _ (hℓ.abs.add hℓ)
  have hu : ‖u‖ > 0 := norm_pos_iff.2 hu0
  -- `φ = max(ℓ, 0) − ℓ`
  have e1 : (fun ζ => max (-ℓ ζ) 0) = fun ζ => max (ℓ ζ) 0 - ℓ ζ := by
    funext ζ; rcases le_total (ℓ ζ) 0 with h | h
    · rw [max_eq_left (by linarith), max_eq_right h]; ring
    · rw [max_eq_right (by linarith), max_eq_left h]; ring
  show Real.circleAverage (fun ζ => max (-ℓ ζ) 0) 0 R ≤ Real.log 2
  rw [e1, Real.circleAverage_fun_sub hpos hℓ]
  -- the positive part
  have hA : Real.circleAverage (fun ζ => max (ℓ ζ) 0) 0 R ≤ Real.log (1 + R / ‖u‖) := by
    apply Real.circleAverage_mono_on_of_le_circle hpos
    intro ζ hζ
    rw [abs_of_pos hR] at hζ
    have hζn : ‖ζ‖ = R := by simpa using hζ
    have hb : ‖1 - ζ / u‖ ≤ 1 + R / ‖u‖ := by
      calc ‖1 - ζ / u‖ ≤ ‖(1 : ℂ)‖ + ‖ζ / u‖ := norm_sub_le _ _
        _ = 1 + R / ‖u‖ := by rw [norm_one, norm_div, hζn]
    have hl0 : 0 ≤ Real.log (1 + R / ‖u‖) := Real.log_nonneg (by
      have : 0 ≤ R / ‖u‖ := by positivity
      linarith)
    apply max_le _ hl0
    rcases eq_or_lt_of_le (norm_nonneg (1 - ζ / u)) with h0 | h0
    · simp only [ℓ, ← h0, Real.log_zero]; exact hl0
    · exact Real.log_le_log h0 hb
  -- the mean of `ℓ`
  have hB : Real.circleAverage ℓ 0 R = Real.log R - Real.log ‖u‖ := by
    have hcongr : Real.circleAverage ℓ 0 R
        = Real.circleAverage (fun ζ => Real.log ‖ζ - u‖ - Real.log ‖u‖) 0 R := by
      apply Real.circleAverage_congr_codiscreteWithin _ hR.ne'
      apply mem_codiscreteWithin_of_finite {u}
      intro ζ hζ
      have hζu : ζ - u ≠ 0 := sub_ne_zero.2 (by simpa using hζ)
      show ℓ ζ = Real.log ‖ζ - u‖ - Real.log ‖u‖
      simp only [ℓ]
      rw [show 1 - ζ / u = -(ζ - u) / u by field_simp; ring, norm_div, norm_neg,
        Real.log_div (norm_ne_zero_iff.2 hζu) (norm_ne_zero_iff.2 hu0)]
    rw [hcongr, Real.circleAverage_fun_sub (circleIntegrable_log_norm_sub_const R)
      (circleIntegrable_const _ _ _), Real.circleAverage_const,
      circleAverage_log_norm_sub_const_of_mem_closedBall (by
        rw [abs_of_pos hR]; simpa using huR)]
  rw [hB]
  have hkey : Real.log (1 + R / ‖u‖) - (Real.log R - Real.log ‖u‖) = Real.log ((‖u‖ + R) / R) := by
    rw [Real.log_div (by positivity) hR.ne', show 1 + R / ‖u‖ = (‖u‖ + R) / ‖u‖ by field_simp,
      Real.log_div (by positivity) hu.ne']
    ring
  have hle : Real.log ((‖u‖ + R) / R) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by rw [div_le_iff₀ hR]; linarith)
  linarith

/-- **The circle average of `log⁺|G_R|` is `O(R^α)`.** With `F = F(0)·P_R·G` on `|w| ≤ R`:
`avg log⁺|G| ≤ |log C| + AR^α + |log‖F(0)‖| + log 2·(K + A₁R^α)`. -/
theorem avg_posLog_G_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {C A α : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hα0 : 0 ≤ α)
    (hgrowth : ∀ w, ‖F w‖ ≤ C * Real.exp (A * ‖w‖ ^ α)) {R : ℝ} (hR : 0 < R) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (closedBall 0 R)) (hG0 : ∀ z ∈ closedBall (0 : ℂ) R, G z ≠ 0)
    (hfac : ∀ w ∈ closedBall (0 : ℂ) R,
      F w = F 0 * (∏ u ∈ zerosIn F R, (1 - w / u) ^ ordN F u) * G w) :
    Real.circleAverage (fun z => max (Real.log ‖G z‖) 0) 0 R
      ≤ |Real.log C| + A * R ^ α + |Real.log ‖F 0‖|
        + Real.log 2 * (|Real.log C - Real.log ‖F 0‖| + A * Real.exp 1 ^ α * R ^ α) := by
  set Z := zerosIn F R
  set c0 := |Real.log C| + A * R ^ α + |Real.log ‖F 0‖|
  set φ : ℂ → ℂ → ℝ := fun u ζ => max (-Real.log ‖1 - ζ / u‖) 0
  set ρ : ℂ → ℝ := fun ζ => c0 + ∑ u ∈ Z, (ordN F u : ℝ) * φ u ζ
  have hc0 : 0 ≤ c0 := by positivity
  have hφ0 : ∀ u ζ, 0 ≤ φ u ζ := fun u ζ => le_max_right _ _
  have hZ : ∀ u ∈ Z, u ≠ 0 ∧ ‖u‖ ≤ R := fun u hu =>
    ⟨ne_zero_of_mem_zerosIn hF hF0 hu, ((mem_zerosIn hF hF0).1 hu).1⟩
  -- pointwise bound off the zeros of `F`
  have hpt : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ 0 → max (Real.log ‖G ζ‖) 0 ≤ ρ ζ := by
    intro ζ hζ hFζ
    have hζn : ‖ζ‖ = R := by simpa using hζ
    have hζb : ζ ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hζ
    have hfz := hfac ζ hζb
    have hP : ∀ u ∈ Z, (1 - ζ / u) ≠ 0 := by
      intro u hu h0
      have : ζ = u := by
        have hu0 := (hZ u hu).1
        field_simp at h0; linear_combination -h0
      rw [this] at hFζ; exact hFζ ((mem_zerosIn hF hF0).1 hu).2
    have hPne : (∏ u ∈ Z, (1 - ζ / u) ^ ordN F u) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (hP u hu)
    have hGne := hG0 ζ hζb
    have hlog : Real.log ‖G ζ‖ = Real.log ‖F ζ‖ - Real.log ‖F 0‖
        - ∑ u ∈ Z, (ordN F u : ℝ) * Real.log ‖1 - ζ / u‖ := by
      rw [hfz, norm_mul, norm_mul, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hGne),
        Real.log_mul (norm_ne_zero_iff.2 hF0) (norm_ne_zero_iff.2 hPne), norm_prod,
        Real.log_prod (fun u hu => norm_ne_zero_iff.2 (pow_ne_zero _ (hP u hu)))]
      simp only [norm_pow, Real.log_pow]
      ring
    have hFb : Real.log ‖F ζ‖ ≤ |Real.log C| + A * R ^ α := by
      have h1 : Real.log ‖F ζ‖ ≤ Real.log (C * Real.exp (A * ‖ζ‖ ^ α)) :=
        Real.log_le_log (norm_pos_iff.2 hFζ) (hgrowth ζ)
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, hζn] at h1
      linarith [le_abs_self (Real.log C)]
    have hsum : -∑ u ∈ Z, (ordN F u : ℝ) * Real.log ‖1 - ζ / u‖ ≤ ∑ u ∈ Z, (ordN F u : ℝ) * φ u ζ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro u _
      have : -Real.log ‖1 - ζ / u‖ ≤ φ u ζ := le_max_left _ _
      have hn : (0 : ℝ) ≤ ordN F u := Nat.cast_nonneg _
      nlinarith
    have hρ0 : 0 ≤ ρ ζ := by
      simp only [ρ]
      exact add_nonneg hc0 (Finset.sum_nonneg fun u _ => mul_nonneg (Nat.cast_nonneg _) (hφ0 u ζ))
    apply max_le _ hρ0
    rw [hlog]
    simp only [ρ, c0]
    linarith [neg_abs_le (Real.log ‖F 0‖)]
  -- integrability
  have hGc : ContinuousOn (fun z => max (Real.log ‖G z‖) 0) (sphere 0 R) := by
    apply ContinuousOn.sup _ continuousOn_const
    intro z hz
    have hzb := sphere_subset_closedBall hz
    exact ((hG z hzb).continuousAt.norm.log (norm_ne_zero_iff.2 (hG0 z hzb))).continuousWithinAt
  have hfi : CircleIntegrable (fun z => max (Real.log ‖G z‖) 0) 0 R := hGc.circleIntegrable hR.le
  have hφi : ∀ u, CircleIntegrable (φ u) 0 R := by
    intro u
    have hℓ := circleIntegrable_log_one_sub u R
    have e : φ u = fun ζ => (1 / 2 : ℝ) * (|Real.log ‖1 - ζ / u‖| - Real.log ‖1 - ζ / u‖) := by
      funext ζ; simp only [φ]
      rcases le_total (Real.log ‖1 - ζ / u‖) 0 with h | h
      · rw [max_eq_left (by linarith), abs_of_nonpos h]; ring
      · rw [max_eq_right (by linarith), abs_of_nonneg h]; ring
    rw [e]; exact circleIntegrable_const_mul _ (hℓ.abs.sub hℓ)
  have hsumi : CircleIntegrable (fun ζ => ∑ u ∈ Z, (ordN F u : ℝ) * φ u ζ) 0 R := by
    have := CircleIntegrable.sum Z (fun u _ => circleIntegrable_const_mul (ordN F u : ℝ) (hφi u))
    convert this using 1; funext ζ; simp
  have hρi : CircleIntegrable ρ 0 R := (circleIntegrable_const c0 0 R).add hsumi
  -- compare the averages
  have hmono := circleAverage_mono_codiscrete hR.ne' hfi hρi (by
    apply mem_codiscreteWithin_of_finite Z
    intro ζ hζZ hζs
    rw [abs_of_pos hR] at hζs
    apply hpt ζ hζs
    intro hFζ; apply hζZ
    exact (mem_zerosIn hF hF0).2 ⟨by simpa using sphere_subset_closedBall hζs, hFζ⟩)
  refine hmono.trans ?_
  have havg : Real.circleAverage ρ 0 R = c0 + ∑ u ∈ Z, (ordN F u : ℝ) * Real.circleAverage (φ u) 0 R := by
    simp only [ρ]
    rw [Real.circleAverage_fun_add (circleIntegrable_const c0 0 R) hsumi, Real.circleAverage_const,
      Real.circleAverage_fun_sum (fun u _ => circleIntegrable_const_mul (ordN F u : ℝ) (hφi u))]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    rw [← smul_eq_mul, ← Real.circleAverage_fun_smul]; rfl
  rw [havg]
  have hcount := zero_count' hF hF0 hC hA hα0 hgrowth hR Z (fun u hu => (hZ u hu).2)
  have hper : ∑ u ∈ Z, (ordN F u : ℝ) * Real.circleAverage (φ u) 0 R
      ≤ ∑ u ∈ Z, (ordN F u : ℝ) * Real.log 2 :=
    Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left
      (circleAverage_negLog_le hR (hZ u hu).1 (hZ u hu).2) (Nat.cast_nonneg _)
  rw [← Finset.sum_mul] at hper
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-! ## The genus-zero factorisation -/

/-- The zero family of `F`: each zero `u` repeated `ord u` times. -/
abbrev ZeroIdx (F : ℂ → ℂ) : Type := Σ u : ℂ, Fin (ordN F u)

/-- The disc error tends to `0`: `6·(a + bR^α)·r/(R/2 − r) → 0` as `R → ∞`, for `α < 1`. -/
theorem tendsto_disc_error {a b r α : ℝ} (hα1 : α < 1) :
    Tendsto (fun R : ℝ => 6 * (a + b * R ^ α) * r / (R / 2 - r)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun R : ℝ => R ^ (α - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := 1 - α) (by linarith)
    simpa [neg_sub] using this
  have hnum : Tendsto (fun R : ℝ => 6 * r * (a * R⁻¹ + b * R ^ (α - 1))) atTop (𝓝 0) := by
    simpa using ((h1.const_mul a).add (h2.const_mul b)).const_mul (6 * r)
  have hden : Tendsto (fun R : ℝ => 1 / 2 - r * R⁻¹) atTop (𝓝 (1 / 2)) := by
    simpa using (h1.const_mul r).const_sub (1 / 2 : ℝ)
  have hq := hnum.div hden (by norm_num)
  rw [zero_div] at hq
  apply hq.congr'
  filter_upwards [eventually_gt_atTop (2 * |r| + 1)] with R hR
  have hR0 : 0 < R := by linarith [abs_nonneg r]
  have hRr : R / 2 - r ≠ 0 := by
    have := le_abs_self r; intro h; linarith
  have hRα : R ^ (α - 1) = R ^ α * R⁻¹ := by
    rw [Real.rpow_sub_one hR0.ne', div_eq_mul_inv]
  show 6 * r * (a * R⁻¹ + b * R ^ (α - 1)) / (1 / 2 - r * R⁻¹) = _
  rw [hRα]
  field_simp

/-- **Hadamard's factorisation, genus zero.** Let `F` be entire with `F(0) ≠ 0` and
`‖F w‖ ≤ C exp(A‖w‖^α)` for some `α < 1`. Then `Σ 1/|u| < ∞` over the zeros (with multiplicity), and
`F(w) = F(0) Π_u (1 − w/u)` for every `w`. -/
theorem hadamard_genus0 {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) {C A α : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hgrowth : ∀ w, ‖F w‖ ≤ C * Real.exp (A * ‖w‖ ^ α)) :
    Summable (fun i : ZeroIdx F => ‖i.1⁻¹‖) ∧
      ∀ w, HasProd (fun i : ZeroIdx F => 1 - w * i.1⁻¹) (F w / F 0) := by
  -- summability over the family
  have hsum : Summable (fun i : ZeroIdx F => ‖i.1⁻¹‖) := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun u => (hasSum_fintype _).summable, ?_⟩
    refine (summable_ord_div hF hF0 hC hA hα0 hα1 hgrowth).congr fun u => ?_
    rw [tsum_fintype]
    show (ordN F u : ℝ) / ‖u‖ = ∑ _b : Fin (ordN F u), ‖u⁻¹‖
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_inv,
      div_eq_mul_inv]
  refine ⟨hsum, fun w => ?_⟩
  have hsw : Summable (fun i : ZeroIdx F => ‖-(w * i.1⁻¹)‖) := by
    simpa [norm_neg, norm_mul] using hsum.mul_left ‖w‖
  have hmul := multipliable_one_add_of_summable hsw
  set P := ∏' i : ZeroIdx F, (1 + -(w * i.1⁻¹))
  have hP : HasProd (fun i : ZeroIdx F => 1 + -(w * i.1⁻¹)) P := hmul.hasProd
  -- the discs `R_n = n + 1`
  set Rn : ℕ → ℝ := fun n => n + 1
  have hRn : ∀ n, 0 < Rn n := fun n => by positivity
  choose G hG hG0 hG1 hfac using fun n => disc_factor hF hF0 (hRn n)
  -- the finite products along the exhausting finsets
  set T : ℕ → Finset (ZeroIdx F) := fun n => (zerosIn F (Rn n)).sigma fun _ => Finset.univ
  have hTmono : Monotone T := by
    intro n m hnm i hi
    simp only [T, Finset.mem_sigma, Finset.mem_univ, and_true] at hi ⊢
    obtain ⟨h1, h2⟩ := (mem_zerosIn hF hF0).1 hi
    refine (mem_zerosIn hF hF0).2 ⟨h1.trans ?_, h2⟩
    simp only [Rn]; exact_mod_cast Nat.add_le_add_right hnm 1
  have hTex : ∀ i : ZeroIdx F, ∃ n, i ∈ T n := by
    rintro ⟨u, j⟩
    have hz : F u = 0 := (ordN_ne_zero_iff hF hF0 u).1 (by
      intro h; exact (Fin.elim0 (h ▸ j)))
    obtain ⟨n, hn⟩ := exists_nat_ge ‖u‖
    refine ⟨n, ?_⟩
    simp only [T, Finset.mem_sigma, Finset.mem_univ, and_true]
    exact (mem_zerosIn hF hF0).2 ⟨by simp only [Rn]; linarith, hz⟩
  have hlimP : Tendsto (fun n => ∏ i ∈ T n, (1 + -(w * i.1⁻¹))) atTop (𝓝 P) :=
    hP.comp (tendsto_atTop_finset_of_monotone hTmono hTex)
  have hTprod : ∀ n, ∏ i ∈ T n, (1 + -(w * i.1⁻¹))
      = ∏ u ∈ zerosIn F (Rn n), (1 - w / u) ^ ordN F u := by
    intro n
    rw [Finset.prod_sigma]
    apply Finset.prod_congr rfl
    intro u _
    show ∏ _s : Fin (ordN F u), (1 + -(w * u⁻¹)) = _
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_eq_mul_inv, sub_eq_add_neg]
  -- `G_n(w) → 1`
  set a := |Real.log C| + |Real.log ‖F 0‖| + Real.log 2 * |Real.log C - Real.log ‖F 0‖| + 1
  set b := A + Real.log 2 * (A * Real.exp 1 ^ α)
  set r := ‖w‖
  have herr := (tendsto_disc_error (a := a) (b := b) (r := r) hα1).comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hGlim : Tendsto (fun n => G n w) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2err : Tendsto (fun n : ℕ => 2 * (6 * (a + b * Rn n ^ α) * r / (Rn n / 2 - r)))
        atTop (𝓝 0) := by
      simpa using herr.const_mul 2
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _ h2err
    filter_upwards [herr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      eventually_gt_atTop ⌈2 * r⌉₊] with n hn hn2
    have hrn : r < Rn n / 2 := by
      have : (⌈2 * r⌉₊ : ℝ) < n := by exact_mod_cast hn2
      have := Nat.le_ceil (2 * r)
      simp only [Rn]; linarith
    have hM : 0 < a + b * Rn n ^ α := by
      have : 0 ≤ b * Rn n ^ α := by positivity
      have : 0 < a := by positivity
      linarith
    have havg := avg_posLog_G_le hF hF0 hC hA hα0 hgrowth (hRn n) (hG n) (hG0 n) (hfac n)
    have havg' : Real.circleAverage (fun z => max (Real.log ‖G n z‖) 0) 0 (Rn n)
        ≤ a + b * Rn n ^ α := by
      refine havg.trans (le_of_eq_of_le rfl ?_)
      simp only [a, b]; nlinarith [abs_nonneg (Real.log C - Real.log ‖F 0‖)]
    have hsmall : 6 * (a + b * Rn n ^ α) * r / (Rn n / 2 - r) ≤ 1 := by
      simp only [Function.comp] at hn; exact hn.le
    exact disc_estimate (hRn n) (norm_nonneg w) hrn (hG n) (hG0 n) (hG1 n) hM havg' hsmall w
      (by simp)
  -- `P_n(w) = F(w)/(F(0) G_n(w)) → F(w)/F(0)`
  have hPn : ∀ᶠ n in atTop, ∏ u ∈ zerosIn F (Rn n), (1 - w / u) ^ ordN F u
      = F w / F 0 / G n w := by
    filter_upwards [eventually_ge_atTop ⌈r⌉₊] with n hn
    have hwb : w ∈ closedBall (0 : ℂ) (Rn n) := by
      rw [mem_closedBall_zero_iff]
      have : (⌈r⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      have := Nat.le_ceil r
      simp only [Rn]; linarith
    have hGw := hG0 n w hwb
    rw [hfac n w hwb]
    field_simp
  have hlim2 : Tendsto (fun n => ∏ u ∈ zerosIn F (Rn n), (1 - w / u) ^ ordN F u) atTop
      (𝓝 (F w / F 0 / 1)) :=
    (tendsto_const_nhds.div hGlim one_ne_zero).congr' (hPn.mono fun n h => h.symm)
  rw [div_one] at hlim2
  have hPeq : P = F w / F 0 := by
    apply tendsto_nhds_unique hlimP
    exact hlim2.congr fun n => (hTprod n).symm
  have hfun : (fun i : ZeroIdx F => 1 - w * i.1⁻¹) = fun i => 1 + -(w * i.1⁻¹) := by
    funext i; ring
  rw [hfun, ← hPeq]
  exact hP

end Pilot1ca

#print axioms Pilot1ca.disc_estimate
#print axioms Pilot1ca.zero_count
#print axioms Pilot1ca.ordN_ne_zero_iff
#print axioms Pilot1ca.summable_ord_div
#print axioms Pilot1ca.disc_factor
#print axioms Pilot1ca.circleAverage_mono_codiscrete
#print axioms Pilot1ca.circleAverage_negLog_le
#print axioms Pilot1ca.avg_posLog_G_le
#print axioms Pilot1ca.hadamard_genus0
