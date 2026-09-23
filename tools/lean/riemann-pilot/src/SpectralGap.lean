import Mathlib
import UniquenessQ

/-! # A certified lower bound on `Q₀` orthogonally to `w`, at small support

For `0 < a ≤ 1/40`, every normalised probe `g` with `ĝ(i/2) = ⟨g, w⟩ = 0` has
`Q₀(g) ≥ Q(box) + 1/40 ≥ λ₁ + 1/40`. So `λ_⊥ ≥ λ₁ + 1/40`, and the ground state of the full form `Q`
is unique up to sign at these supports (round 18's second branch is excluded).

The proof is analytic, with no computed input.
1. **No primes.** `2a < log 2`, so the prime term vanishes.
2. **The far field cancels.** For `u > 2a`, `A_g(u) = K(u)` for every normalised probe, so
   `Q(g) − Q(box) = ∫_{(0,2a]}(A_g − A_box) − 2ĝ_box(i/2)²`.
3. **Edge mass.** With `m(u) = ∫_{t > a−u} g²`: `f(u) ≤ 1 − m(u)` (AM–GM on the overlap), and
   `m(u) + m(2a − u) = 1` (evenness). So `A_g = mK + (1 − m − f)K`, both parts non-negative.
4. **Kernel bounds.** `1/(u cosh a) ≤ K(u) ≤ e^{u/2}/u` on `(0, 2a]`.
5. **Integrals.** Reflection gives `∫₀^{2a} m/u ≥ log 2` and `∫₀^{2a} m = a`; Fubini gives
   `∫₀^{2a} f = (∫g)²/2`; and `g ⊥ w` makes `(∫g)² = O(a²)`. The box has `∫_{(0,2a]} A_box ≤ e^a` and
   `2ĝ_box(i/2)² ≤ 4ae^a`.
6. **Numerics.** `(log 2 + ½)/cosh a − a(1+2a)²/16 − e^a(1 + 4a) ≥ 1/40` for `a ≤ 1/40`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## 1. The kernel, the prime term, the box -/

theorem kerK_le {u : ℝ} (hu : 0 < u) : kerK u ≤ Real.exp (u / 2) / u := by
  unfold kerK
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hu (Real.self_le_sinh_iff.2 hu.le)

theorem kerK_ge {u : ℝ} (hu : 0 < u) : 1 / (u * Real.cosh (u / 2)) ≤ kerK u := by
  unfold kerK
  have hsh : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  have e : Real.sinh u = 2 * Real.sinh (u / 2) * Real.cosh (u / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have h2 : 2 * Real.sinh (u / 2) ≤ Real.exp (u / 2) * u := by
    rw [Real.sinh_eq]
    have h1 := Real.add_one_le_exp (-u)
    have e2 : Real.exp (-(u / 2)) = Real.exp (u / 2) * Real.exp (-u) := by
      rw [← Real.exp_add]; ring_nf
    rw [e2]
    have := Real.exp_pos (u / 2)
    nlinarith
  rw [div_le_div_iff₀ (by positivity) hsh, one_mul, e]
  have := Real.exp_pos (u / 2)
  nlinarith

/-- On `(0, 2a]`: `K(u) ≥ 1/(u cosh a)`. -/
theorem kerK_ge' {a u : ℝ} (hu : 0 < u) (hua : u ≤ 2 * a) : 1 / (u * Real.cosh a) ≤ kerK u := by
  refine le_trans ?_ (kerK_ge hu)
  have hc : Real.cosh (u / 2) ≤ Real.cosh a :=
    Real.cosh_le_cosh.2 (by rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith)
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hc hu.le)

/-- Below the first prime power (`2a < log 2`) the prime term of every probe vanishes. -/
theorem primeS_eq_zero {a : ℝ} (ha : 2 * a < Real.log 2) {g : ℝ → ℝ} (hg : Probe a g) :
    primeS g = 0 := by
  unfold primeS
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hl : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : 0 < Real.log n := by linarith
    have hz : autocorr g (Real.log n) = 0 :=
      autocorr_eq_zero hg.supp (by rw [abs_of_pos hpos]; linarith)
    simp [hz]

theorem box_sq {a : ℝ} (ha : 0 < a) : (1 / Real.sqrt (2 * a)) ^ 2 = 1 / (2 * a) := by
  rw [div_pow, Real.sq_sqrt (by linarith), one_pow]

/-- `ĝ(i/2)² ≤ 2a·e^a` for the box. -/
theorem poleR_box_sq_le {a : ℝ} (ha : 0 < a) : poleR (box a) a ^ 2 ≤ 2 * a * Real.exp a := by
  set c := 1 / Real.sqrt (2 * a) with hc
  have hc0 : 0 ≤ c := by positivity
  have hp : poleR (box a) a = ∫ u in (-a)..a, c * Real.exp (-(u / 2)) := by
    unfold poleR
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    simp only [box_apply, abs_le.2 ⟨hu.1, hu.2⟩, ite_true, hc]
  have hup : poleR (box a) a ≤ 2 * a * (c * Real.exp (a / 2)) := by
    rw [hp]
    have := intervalIntegral.integral_mono_on (by linarith : -a ≤ a)
      (by exact (show Continuous (fun u : ℝ => c * Real.exp (-(u / 2))) by fun_prop).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := c * Real.exp (a / 2)))
      (fun u hu => mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by linarith [hu.1])) hc0)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hlo : 0 ≤ poleR (box a) a := by
    rw [hp]
    exact intervalIntegral.integral_nonneg (by linarith) fun u _ =>
      mul_nonneg hc0 (Real.exp_pos _).le
  have hsq : (2 * a * (c * Real.exp (a / 2))) ^ 2 = 2 * a * Real.exp a := by
    have hc2 : c ^ 2 = 1 / (2 * a) := box_sq ha
    have he : Real.exp (a / 2) ^ 2 = Real.exp a := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc (2 * a * (c * Real.exp (a / 2))) ^ 2 = 4 * a ^ 2 * c ^ 2 * Real.exp (a / 2) ^ 2 := by ring
      _ = _ := by rw [hc2, he]; field_simp; ring
  calc poleR (box a) a ^ 2 ≤ (2 * a * (c * Real.exp (a / 2))) ^ 2 := pow_le_pow_left₀ hlo hup 2
    _ = _ := hsq

theorem archIntegrand_eq_kerK {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hg : Probe a g) (hn : normSq g = 1) {u : ℝ}
    (hu : 2 * a < u) : archIntegrand g u = kerK u := by
  unfold archIntegrand kerK
  rw [autocorr_zero, hn, autocorr_eq_zero hg.supp (by rwa [abs_of_pos (by linarith)])]
  ring

/-! ## 2. The edge mass -/

/-- The edge mass `m(u) = ∫_{t > a − u} g²`. -/
def edge (a : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := ∫ t, (Ioi (a - u)).indicator (fun t => g t ^ 2) t

theorem integrable_ind_sq {g : ℝ → ℝ} (hg : MemLp g 2 volume) (s : Set ℝ) (hs : MeasurableSet s) :
    Integrable (s.indicator fun t => g t ^ 2) :=
  hg.integrable_sq.indicator hs

theorem ind_sq_nonneg (g : ℝ → ℝ) (s : Set ℝ) (t : ℝ) : 0 ≤ s.indicator (fun t => g t ^ 2) t :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) t

theorem edge_nonneg (a : ℝ) (g : ℝ → ℝ) (u : ℝ) : 0 ≤ edge a g u :=
  integral_nonneg (ind_sq_nonneg g _)

theorem edge_mono {a : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume) : Monotone (edge a g) := by
  intro u u' h
  refine integral_mono (integrable_ind_sq hg _ measurableSet_Ioi)
    (integrable_ind_sq hg _ measurableSet_Ioi) fun t => ?_
  exact Set.indicator_le_indicator_of_subset (Ioi_subset_Ioi (by linarith))
    (fun _ => sq_nonneg _) t

theorem edge_le_one {a : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume) (hn : normSq g = 1) (u : ℝ) :
    edge a g u ≤ 1 := by
  rw [← hn]
  exact integral_mono (integrable_ind_sq hg _ measurableSet_Ioi) hg.integrable_sq
    fun t => Set.indicator_le_self' (fun _ _ => sq_nonneg _) t

theorem integral_Iic_ind {g : ℝ → ℝ} (hg : MemLp g 2 volume) (hn : normSq g = 1) (c : ℝ) :
    (∫ t, (Iic c).indicator (fun t => g t ^ 2) t) = 1 - ∫ t, (Ioi c).indicator (fun t => g t ^ 2) t := by
  have h := Set.indicator_self_add_compl (Ioi c) (fun t => g t ^ 2)
  rw [compl_Ioi] at h
  have hs := integral_add (integrable_ind_sq hg (Ioi c) measurableSet_Ioi)
    (integrable_ind_sq hg (Iic c) measurableSet_Iic)
  have e : (∫ t, ((Ioi c).indicator (fun t => g t ^ 2) t + (Iic c).indicator (fun t => g t ^ 2) t))
      = normSq g := by
    unfold normSq; exact integral_congr_ae (Eventually.of_forall fun t => congrFun h t)
  rw [e, hn] at hs
  linarith

/-- Reflection: `∫_{t > c} g² = ∫_{t < −c} g²` for even `g`. -/
theorem integral_Ioi_ind_even {g : ℝ → ℝ} (heven : ∀ u, g (-u) = g u) (c : ℝ) :
    (∫ t, (Ioi c).indicator (fun t => g t ^ 2) t) = ∫ t, (Iio (-c)).indicator (fun t => g t ^ 2) t := by
  rw [← integral_neg_eq_self]
  congr 1; funext t
  by_cases ht : c < -t
  · have : t < -c := by linarith
    simp [ht, this, heven]
  · have : ¬ t < -c := by intro h; exact ht (by linarith)
    simp [ht, this]

/-- **`m(u) + m(2a − u) = 1`** for an even normalised `g`. -/
theorem edge_reflect {a : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume) (hn : normSq g = 1)
    (heven : ∀ u, g (-u) = g u) (u : ℝ) : edge a g u + edge a g (2 * a - u) = 1 := by
  unfold edge
  rw [integral_Ioi_ind_even heven (a - u), show -(a - u) = u - a by ring,
    show a - (2 * a - u) = u - a by ring]
  have hae : (Iio (u - a)).indicator (fun t => g t ^ 2) =ᵐ[volume]
      (Iic (u - a)).indicator (fun t => g t ^ 2) :=
    indicator_ae_eq_of_ae_eq_set Iio_ae_eq_Iic
  rw [integral_congr_ae hae, integral_Iic_ind hg hn]
  ring

/-- **`f(u) ≤ 1 − m(u)`**: the overlap of `g` with its shift is at most the mass away from the edge. -/
theorem autocorr_le_edge {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    (u : ℝ) : autocorr g u ≤ 1 - edge a g u := by
  set F := (Iic (a - u)).indicator (fun t => g t ^ 2) with hF
  have hFi : Integrable F := integrable_ind_sq hp.memL2 _ measurableSet_Iic
  have hFn : Integrable (fun t => F (-t)) := hFi.comp_neg
  have hFs : Integrable (fun t => F (-(t + u))) := by
    simpa using hFn.comp_add_right u
  have hpt : ∀ t, g t * g (t + u) ≤ (F t + F (-(t + u))) / 2 := by
    intro t
    have h0 := ind_sq_nonneg g (Iic (a - u)) t
    have h1 := ind_sq_nonneg g (Iic (a - u)) (-(t + u))
    by_cases h1t : a - u < t
    · rw [hp.supp (t + u) (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
      simp only [hF] at h0 h1 ⊢; linarith
    by_cases h2t : t < -a
    · rw [hp.supp t (by rw [abs_of_neg (by linarith)]; linarith), zero_mul]
      simp only [hF] at h0 h1 ⊢; linarith
    have e1 : F t = g t ^ 2 := by
      rw [hF, Set.indicator_of_mem (show t ∈ Iic (a - u) from not_lt.1 h1t)]
    have e2 : F (-(t + u)) = g (t + u) ^ 2 := by
      have : -(t + u) ∈ Iic (a - u) := by
        show -(t + u) ≤ a - u; linarith [not_lt.1 h2t]
      rw [hF, Set.indicator_of_mem this, hp.even]
    rw [e1, e2]; nlinarith [sq_nonneg (g t - g (t + u))]
  have hsh : (∫ t, F (-(t + u))) = ∫ t, F t := by
    rw [integral_add_right_eq_self (fun t => F (-t)) u, integral_neg_eq_self]
  have hsum : Integrable (fun t => (F t + F (-(t + u))) / 2) := (hFi.add hFs).div_const 2
  have hmono := integral_mono (integrable_mul_shift hp.memL2 u) hsum hpt
  rw [integral_div, integral_add hFi hFs, hsh] at hmono
  have hc := integral_Iic_ind hp.memL2 hn (a - u)
  unfold autocorr edge
  rw [← hF] at hc
  linarith

/-! ## 3. The mean of the autocorrelation (Fubini) -/

theorem autocorr_neg (g : ℝ → ℝ) (u : ℝ) : autocorr g (-u) = autocorr g u := by
  unfold autocorr
  rw [← integral_add_right_eq_self (fun t => g t * g (t + -u)) u]
  congr 1; funext t
  rw [show t + u + -u = t by ring, mul_comm]

theorem integrable_autocorr_prod {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) :
    Integrable (Function.uncurry fun t u => g t * g (t + u)) (volume.prod volume) := by
  have hI := probe_integrable hp
  have hH : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2) (volume.prod volume) := hI.mul_prod hI
  have := ((measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)).integrable_comp
    hH.aestronglyMeasurable).2 hH
  exact this

/-- **`∫ f = (∫ g)²`.** -/
theorem integral_autocorr {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) :
    (∫ u, autocorr g u) = (∫ t, g t) ^ 2 := by
  have hsw := integral_integral_swap (integrable_autocorr_prod hp)
  unfold autocorr
  rw [← hsw]
  have e : ∀ t, (∫ u, g t * g (t + u)) = g t * ∫ s, g s := by
    intro t; rw [integral_const_mul, integral_add_left_eq_self]
  simp_rw [e]
  rw [integral_mul_const, sq]

theorem integrable_autocorr {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) : Integrable (autocorr g) :=
  (integrable_autocorr_prod hp).integral_prod_right

/-- **`∫_{(0,2a]} f = (∫ g)²/2`.** -/
theorem integral_autocorr_Ioc {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) :
    (∫ u in Ioc 0 (2 * a), autocorr g u) = (∫ t, g t) ^ 2 / 2 := by
  have hi := integrable_autocorr hp
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hi.integrableOn hi.integrableOn
  have hneg : (∫ u in Iic (0 : ℝ), autocorr g u) = ∫ u in Ioi (0 : ℝ), autocorr g u := by
    calc (∫ u in Iic (0 : ℝ), autocorr g u) = ∫ u in Iic (0 : ℝ), autocorr g (-u) := by
          congr 1; funext u; rw [autocorr_neg]
      _ = ∫ u in Ioi (-0 : ℝ), autocorr g u := integral_comp_neg_Iic 0 _
      _ = _ := by rw [neg_zero]
  have htail : (∫ u in Ioi (2 * a), autocorr g u) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
      autocorr_eq_zero hp.supp (by rw [abs_of_pos (by linarith [mem_Ioi.1 hu])]; exact hu)
  have hu := setIntegral_union (Ioc_disjoint_Ioi (le_refl (2 * a))) measurableSet_Ioi
    (hi.integrableOn (s := Ioc 0 (2 * a))) (hi.integrableOn (s := Ioi (2 * a)))
  rw [Ioc_union_Ioi_eq_Ioi (by linarith), htail, add_zero] at hu
  rw [integral_autocorr hp] at hsplit
  linarith

/-! ## 4. The near-field energy of a probe -/

/-- The truncated comparison kernel `ℓ(u) = 1/(max(u, a/2)·cosh a)`. -/
def ellK (a u : ℝ) : ℝ := 1 / (max u (a / 2) * Real.cosh a)

/-- The folded kernel `h(u) = 1/(max(u, 2a − u)·cosh a)`. -/
def foldK (a u : ℝ) : ℝ := 1 / (max u (2 * a - u) * Real.cosh a)

theorem ellK_continuous {a : ℝ} (ha : 0 < a) : Continuous (ellK a) := by
  unfold ellK
  refine continuous_const.div (by fun_prop) fun u => ?_
  have : a / 2 ≤ max u (a / 2) := le_max_right _ _
  have := Real.cosh_pos a
  positivity

theorem foldK_continuous {a : ℝ} (ha : 0 < a) : Continuous (foldK a) := by
  unfold foldK
  refine continuous_const.div (by fun_prop) fun u => ?_
  have : a ≤ max u (2 * a - u) := by
    rcases le_total u a with h | h
    · exact le_trans (by linarith) (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
  have := Real.cosh_pos a
  have : 0 < max u (2 * a - u) := by linarith
  positivity

theorem ellK_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ ellK a u := by
  unfold ellK
  have : a / 2 ≤ max u (a / 2) := le_max_right _ _
  have := Real.cosh_pos a
  have : 0 < max u (a / 2) := by linarith
  positivity

theorem ellK_le {a : ℝ} (ha : 0 < a) (u : ℝ) : ellK a u ≤ 2 / a := by
  unfold ellK
  have h1 : a / 2 ≤ max u (a / 2) := le_max_right _ _
  have h2 := Real.one_le_cosh a
  rw [div_le_div_iff₀ (by nlinarith) ha]
  nlinarith

theorem foldK_le {a : ℝ} (ha : 0 < a) (u : ℝ) :
    foldK a u ≤ ellK a u ∧ foldK a u ≤ ellK a (2 * a - u) := by
  have hc := Real.cosh_pos a
  have hM : a ≤ max u (2 * a - u) := by
    rcases le_total u a with h | h
    · exact le_trans (by linarith) (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
  unfold foldK ellK
  constructor
  · refine one_div_le_one_div_of_le (by
      have : a / 2 ≤ max u (a / 2) := le_max_right _ _
      have : 0 < max u (a / 2) := by linarith
      positivity) (mul_le_mul_of_nonneg_right ?_ hc.le)
    exact max_le (le_max_left _ _) (by linarith)
  · refine one_div_le_one_div_of_le (by
      have : a / 2 ≤ max (2 * a - u) (a / 2) := le_max_right _ _
      have : 0 < max (2 * a - u) (a / 2) := by linarith
      positivity) (mul_le_mul_of_nonneg_right ?_ hc.le)
    exact max_le (le_max_right _ _) (by linarith)

/-- `∫₀^{2a} h = 2 log 2 / cosh a`. -/
theorem integral_foldK {a : ℝ} (ha : 0 < a) :
    (∫ u in (0 : ℝ)..(2 * a), foldK a u) = 2 * (Real.log 2 / Real.cosh a) := by
  have hc := Real.cosh_pos a
  have hi : ∀ x y, IntervalIntegrable (foldK a) volume x y :=
    fun x y => (foldK_continuous ha).intervalIntegrable x y
  have hR : (∫ u in a..(2 * a), foldK a u) = Real.log 2 / Real.cosh a := by
    have e : (∫ u in a..(2 * a), foldK a u) = ∫ u in a..(2 * a), u⁻¹ / Real.cosh a := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le (by linarith)] at hu
      unfold foldK
      rw [max_eq_left (by linarith [hu.1]), one_div, mul_inv, div_eq_mul_inv]
    rw [e, intervalIntegral.integral_div, integral_inv_of_pos ha (by linarith),
      show 2 * a / a = 2 by field_simp]
  have hL : (∫ u in (0 : ℝ)..a, foldK a u) = Real.log 2 / Real.cosh a := by
    have e : (∫ u in (0 : ℝ)..a, foldK a u) = ∫ u in (0 : ℝ)..a, foldK a (2 * a - u) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      unfold foldK; rw [max_comm, show 2 * a - (2 * a - u) = u by ring]
    rw [e, intervalIntegral.integral_comp_sub_left (fun u => foldK a u) (2 * a),
      show 2 * a - a = a by ring, sub_zero, hR]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a (2 * a)), hL, hR]
  ring

/-- **`∫₀^{2a} m·ℓ ≥ log 2 / cosh a`**: the edge mass is reflection-complementary, `m(2a−u) = 1 − m(u)`. -/
theorem integral_edge_ellK {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) :
    Real.log 2 / Real.cosh a ≤ ∫ u in (0 : ℝ)..(2 * a), edge a g u * ellK a u := by
  have hmI : ∀ x y, IntervalIntegrable (edge a g) volume x y :=
    fun x y => (edge_mono hp.memL2).intervalIntegrable
  have hℓ := ellK_continuous ha
  have hA : IntervalIntegrable (fun u => edge a g u * ellK a u) volume 0 (2 * a) :=
    (hmI 0 (2 * a)).mul_continuousOn hℓ.continuousOn
  have hB : IntervalIntegrable (fun u => (1 - edge a g u) * ellK a (2 * a - u)) volume 0 (2 * a) :=
    ((intervalIntegrable_const.sub (hmI 0 (2 * a))).mul_continuousOn
      (hℓ.comp (continuous_const.sub continuous_id)).continuousOn)
  have hrefl : (∫ u in (0 : ℝ)..(2 * a), edge a g u * ellK a u)
      = ∫ u in (0 : ℝ)..(2 * a), (1 - edge a g u) * ellK a (2 * a - u) := by
    have hs := intervalIntegral.integral_comp_sub_left (fun u => edge a g u * ellK a u)
      (a := 0) (b := 2 * a) (2 * a)
    simp only [sub_self, sub_zero] at hs
    rw [← hs]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [show edge a g (2 * a - u) = 1 - edge a g u by
        linarith [edge_reflect (a := a) hp.memL2 hn hp.even u]]
  have hmono : (∫ u in (0 : ℝ)..(2 * a), foldK a u)
      ≤ ∫ u in (0 : ℝ)..(2 * a), (edge a g u * ellK a u + (1 - edge a g u) * ellK a (2 * a - u)) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((foldK_continuous ha).intervalIntegrable _ _) (hA.add hB) fun u hu => ?_
    obtain ⟨h1, h2⟩ := foldK_le ha u
    have m0 := edge_nonneg a g u
    have m1 := edge_le_one (a := a) hp.memL2 hn u
    nlinarith
  rw [intervalIntegral.integral_add hA hB, ← hrefl, integral_foldK ha] at hmono
  linarith

/-- **`∫₀^{2a} m = a`.** -/
theorem integral_edge {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) :
    (∫ u in (0 : ℝ)..(2 * a), edge a g u) = a := by
  have hmI : IntervalIntegrable (edge a g) volume 0 (2 * a) := (edge_mono hp.memL2).intervalIntegrable
  have hrefl : (∫ u in (0 : ℝ)..(2 * a), edge a g u) = ∫ u in (0 : ℝ)..(2 * a), (1 - edge a g u) := by
    have hs := intervalIntegral.integral_comp_sub_left (fun u => edge a g u)
      (a := 0) (b := 2 * a) (2 * a)
    simp only [sub_self, sub_zero] at hs
    rw [← hs]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show edge a g (2 * a - u) = 1 - edge a g u
    linarith [edge_reflect (a := a) hp.memL2 hn hp.even u]
  rw [intervalIntegral.integral_sub intervalIntegrable_const hmI, intervalIntegral.integral_const,
    smul_eq_mul, mul_one, sub_zero] at hrefl
  linarith

/-- **The near-field energy**: `∫_{(0,2a]} A_g ≥ log 2/cosh a + (a − (∫g)²/2)/(2a cosh a)` for a
measurable normalised probe. -/
theorem nearField_ge {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hm : Measurable g)
    (hn : normSq g = 1) :
    Real.log 2 / Real.cosh a + (a - (∫ t, g t) ^ 2 / 2) / (2 * a * Real.cosh a)
      ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have hc := Real.cosh_pos a
  set L₀ := 1 / (2 * a * Real.cosh a) with hL₀
  have hL₀0 : 0 ≤ L₀ := by positivity
  have hfm : Measurable (autocorr g) := (autocorr_stronglyMeasurable hm).measurable
  have hmm : Measurable (edge a g) := (edge_mono hp.memL2).measurable
  have hfb : ∀ u, |autocorr g u| ≤ 1 := fun u => hn ▸ abs_autocorr_le hp.memL2 u
  set φ : ℝ → ℝ := fun u => edge a g u * ellK a u + (1 - edge a g u - autocorr g u) * L₀ with hφ
  have hφm : Measurable φ :=
    (hmm.mul (ellK_continuous ha).measurable).add
      (((measurable_const.sub hmm).sub hfm).mul measurable_const)
  have hφb : ∀ u, |φ u| ≤ 2 / a + 3 * L₀ := by
    intro u
    have m0 := edge_nonneg a g u
    have m1 := edge_le_one (a := a) hp.memL2 hn u
    have l0 := ellK_nonneg ha u
    have l1 := ellK_le ha u
    have f1 := abs_le.1 (hfb u)
    rw [abs_le]; constructor <;> simp only [hφ] <;> nlinarith
  have hφi : IntegrableOn φ (Ioc 0 (2 * a)) :=
    (integrableOn_const (C := 2 / a + 3 * L₀) measure_Ioc_lt_top.ne).mono' hφm.aestronglyMeasurable
      (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hφb u)
  have hpt : ∀ u ∈ Ioc 0 (2 * a), φ u ≤ archIntegrand g u := by
    intro u hu
    have hK := kerK_ge' (a := a) hu.1 hu.2
    have hKℓ : ellK a u ≤ kerK u := by
      refine le_trans ?_ hK
      unfold ellK
      exact one_div_le_one_div_of_le (by have := hu.1; positivity)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hc.le)
    have hKL : L₀ ≤ kerK u := by
      refine le_trans ?_ hK
      exact one_div_le_one_div_of_le (by have := hu.1; positivity)
        (mul_le_mul_of_nonneg_right hu.2 hc.le)
    have m0 := edge_nonneg a g u
    have hF := autocorr_le_edge ha hp hn u
    have e : archIntegrand g u = (edge a g u + (1 - edge a g u - autocorr g u)) * kerK u := by
      unfold archIntegrand kerK; rw [autocorr_zero, hn]; ring
    rw [e]; simp only [hφ]
    have h1 : 0 ≤ 1 - edge a g u - autocorr g u := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hKℓ m0, mul_le_mul_of_nonneg_left hKL h1]
  have hmono := setIntegral_mono_on hφi (hp.arch.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
  -- evaluate `∫ φ`
  have hmI : IntervalIntegrable (edge a g) volume 0 (2 * a) := (edge_mono hp.memL2).intervalIntegrable
  have hmℓ : IntervalIntegrable (fun u => edge a g u * ellK a u) volume 0 (2 * a) :=
    hmI.mul_continuousOn (ellK_continuous ha).continuousOn
  have hfI : IntervalIntegrable (autocorr g) volume 0 (2 * a) :=
    (integrable_autocorr hp).intervalIntegrable
  have h1mf : IntervalIntegrable (fun u => (1 - edge a g u - autocorr g u) * L₀) volume 0 (2 * a) :=
    ((intervalIntegrable_const.sub hmI).sub hfI).mul_const L₀
  have hφint : (∫ u in Ioc 0 (2 * a), φ u)
      = (∫ u in (0 : ℝ)..(2 * a), edge a g u * ellK a u)
        + (2 * a - a - (∫ t, g t) ^ 2 / 2) * L₀ := by
    rw [← intervalIntegral.integral_of_le (by linarith)]
    simp only [hφ]
    rw [intervalIntegral.integral_add hmℓ h1mf, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (intervalIntegrable_const.sub hmI) hfI,
      intervalIntegral.integral_sub intervalIntegrable_const hmI, integral_edge hp hn,
      intervalIntegral.integral_const, intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 2 * a)
        (f := autocorr g), integral_autocorr_Ioc ha hp]
    simp
  have hJ := integral_edge_ellK ha hp hn
  rw [hφint] at hmono
  have e2 : (a - (∫ t, g t) ^ 2 / 2) / (2 * a * Real.cosh a) = (2 * a - a - (∫ t, g t) ^ 2 / 2) * L₀ := by
    rw [hL₀]; ring
  rw [e2]; linarith

/-! ## 5. The gap -/

/-- The box's near-field energy: `∫_{(0,2a]} A_box ≤ e^a`. -/
theorem nearField_box_le {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioc 0 (2 * a), archIntegrand (box a) u) ≤ Real.exp a := by
  have hpt : ∀ u ∈ Ioc 0 (2 * a), archIntegrand (box a) u ≤ Real.exp a / (2 * a) := by
    intro u hu
    have hK0 : 0 ≤ kerK u := (kerK_pos hu.1).le
    have h1 : archIntegrand (box a) u ≤ (1 / (2 * a) * u) * kerK u := by
      unfold archIntegrand
      rw [← box_sq ha]
      exact mul_le_mul_of_nonneg_right (box_autocorr_diff_le hu.1) hK0
    have h2 : (1 / (2 * a) * u) * kerK u ≤ (1 / (2 * a) * u) * (Real.exp (u / 2) / u) :=
      mul_le_mul_of_nonneg_left (kerK_le hu.1) (by have := hu.1; positivity)
    have h3 : (1 / (2 * a) * u) * (Real.exp (u / 2) / u) = Real.exp (u / 2) / (2 * a) := by
      field_simp [hu.1.ne']
    have h4 : Real.exp (u / 2) ≤ Real.exp a := Real.exp_le_exp.2 (by linarith [hu.2])
    rw [h3] at h2
    calc archIntegrand (box a) u ≤ _ := h1.trans h2
      _ ≤ Real.exp a / (2 * a) := div_le_div_of_nonneg_right h4 (by linarith)
  have hmono := setIntegral_mono_on ((box_probe a).arch.mono_set Ioc_subset_Ioi_self)
    (integrableOn_const (C := Real.exp a / (2 * a)) measure_Ioc_lt_top.ne) measurableSet_Ioc hpt
  rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, sub_zero] at hmono
  have e : 2 * a * (Real.exp a / (2 * a)) = Real.exp a := by field_simp
  linarith

/-- `archE g = ∫_{(0,2a]} A_g + ∫_{u > 2a} K` for a normalised probe. -/
theorem archE_split {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) :
    archE g = (∫ u in Ioc 0 (2 * a), archIntegrand g u) + ∫ u in Ioi (2 * a), kerK u := by
  unfold archE
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ 2 * a),
    setIntegral_union (Ioc_disjoint_Ioi (le_refl _)) measurableSet_Ioi
      (hp.arch.mono_set Ioc_subset_Ioi_self) (hp.arch.mono_set (Ioi_subset_Ioi (by linarith)))]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu =>
    archIntegrand_eq_kerK ha.le hp hn hu

/-- `(∫ g)² ≤ a²(1 + 2a)²/4` for a normalised probe orthogonal to `w`. -/
theorem integral_sq_le_of_perp {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) : (∫ t, g t) ^ 2 ≤ (a * (1 + 2 * a) / 2) ^ 2 := by
  have hI := probe_integrable hp
  have hwhole : (∫ t, g t) = ∫ t in Ioc (-a) a, g t := by
    rw [← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    refine hp.supp t ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  have hpole : (∫ t in Ioc (-a) a, g t * Real.exp (-(t / 2))) = 0 := by
    rw [← intervalIntegral.integral_of_le (by linarith)]; exact h0
  have hgi : IntegrableOn g (Ioc (-a) a) := hI.integrableOn
  have hwi : IntegrableOn (fun t => g t * Real.exp (-(t / 2))) (Ioc (-a) a) :=
    (poleR_integrable hp.memL2 a).1
  have hdiff : (∫ t in Ioc (-a) a, g t) = ∫ t in Ioc (-a) a, (g t - g t * Real.exp (-(t / 2))) := by
    rw [integral_sub hgi hwi, hpole, sub_zero]
  have hsq : IntegrableOn (fun t => g t ^ 2) (Ioc (-a) a) := hp.memL2.integrable_sq.integrableOn
  have hbd : IntegrableOn (fun t => a * ((g t ^ 2 + 1) / 2)) (Ioc (-a) a) :=
    ((hsq.add (integrableOn_const measure_Ioc_lt_top.ne)).div_const 2).const_mul a
  have hpt : ∀ t ∈ Ioc (-a) a, |g t - g t * Real.exp (-(t / 2))| ≤ a * ((g t ^ 2 + 1) / 2) := by
    intro t ht
    have hta : |t| ≤ a := abs_le.2 ⟨ht.1.le, ht.2⟩
    have hx : |-(t / 2)| ≤ 1 := by rw [abs_neg, abs_div]; norm_num; linarith
    have he := Real.abs_exp_sub_one_le hx
    rw [abs_neg, abs_div, abs_two] at he
    have hw : |1 - Real.exp (-(t / 2))| ≤ a := by rw [abs_sub_comm]; linarith
    have hg : |g t| ≤ (g t ^ 2 + 1) / 2 := by nlinarith [sq_abs (g t), sq_nonneg (|g t| - 1)]
    rw [show g t - g t * Real.exp (-(t / 2)) = g t * (1 - Real.exp (-(t / 2))) by ring, abs_mul]
    calc |g t| * |1 - Real.exp (-(t / 2))| ≤ |g t| * a :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ ≤ (g t ^ 2 + 1) / 2 * a := mul_le_mul_of_nonneg_right hg ha.le
      _ = _ := by ring
  have habs := (abs_integral_le_integral_abs (μ := volume.restrict (Ioc (-a) a))
    (f := fun t => g t - g t * Real.exp (-(t / 2)))).trans
    (setIntegral_mono_on (hgi.sub hwi).abs hbd measurableSet_Ioc hpt)
  have hval : (∫ t in Ioc (-a) a, a * ((g t ^ 2 + 1) / 2)) ≤ a * (1 + 2 * a) / 2 := by
    rw [integral_const_mul, integral_div, integral_add hsq (integrableOn_const measure_Ioc_lt_top.ne),
      setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul, mul_one]
    have : (∫ t in Ioc (-a) a, g t ^ 2) ≤ 1 := by
      rw [← hn]
      exact setIntegral_le_integral hp.memL2.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
    nlinarith
  rw [hwhole, hdiff]
  have h := habs.trans hval
  exact sq_le_sq' (by linarith [neg_abs_le (∫ t in Ioc (-a) a, (g t - g t * Real.exp (-(t / 2))))])
    ((le_abs_self _).trans h)

/-- **The gap for a measurable probe.** -/
theorem weilQ_perp_ge_meas {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 40) {g : ℝ → ℝ} (hp : Probe a g)
    (hm : Measurable g) (hn : normSq g = 1) (h0 : poleR g a = 0) :
    weilQ a (box a) + 1 / 40 ≤ weilQ a g := by
  have hlog2 : 2 * a < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hQ : ∀ h, Probe a h → normSq h = 1 →
      weilQ a h = 2 * poleR h a ^ 2 + weilConst + archE h := by
    intro h hh hhn
    rw [weilQ_eq', primeS_eq_zero hlog2 hh, hhn]; ring
  rw [hQ g hp hn, hQ _ (box_probe a) (normSq_box ha), h0, archE_split ha hp hn,
    archE_split ha (box_probe a) (normSq_box ha)]
  have hG := nearField_ge ha hp hm hn
  have hB := nearField_box_le ha
  have hP := poleR_box_sq_le ha
  have hS := integral_sq_le_of_perp ha (by linarith) hp hn h0
  -- numerics
  have hc1 := Real.one_le_cosh a
  have hc2 : Real.cosh a ≤ 1 + a ^ 2 := by
    have h1 := Real.cosh_le_exp_half_sq a
    have hx0 : (0 : ℝ) ≤ a ^ 2 / 2 := by positivity
    have h2 := Real.abs_exp_sub_one_le (x := a ^ 2 / 2) (by
      rw [abs_of_nonneg hx0]; nlinarith)
    have h3 := (le_abs_self _).trans h2
    rw [abs_of_nonneg hx0] at h3
    linarith
  have he : Real.exp a ≤ 1 + 2 * a := by
    have h2 := Real.abs_exp_sub_one_le (x := a) (by rw [abs_of_pos ha]; linarith)
    have h3 := (le_abs_self _).trans h2
    rw [abs_of_pos ha] at h3
    linarith
  set I := (∫ t, g t) ^ 2 with hI
  set c := Real.cosh a with hc
  have hcp : 0 < c := by linarith
  -- `log 2/c + (a − I/2)/(2ac) ≥ (log 2 + 1/2)/c − I/(4a)`
  have k1 : (a - I / 2) / (2 * a * c) = 1 / (2 * c) - I / (4 * a * c) := by field_simp; ring
  have k2 : I / (4 * a * c) ≤ a * (1 + 2 * a) ^ 2 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    have : I ≤ (a * (1 + 2 * a) / 2) ^ 2 := hS
    have hI0 : 0 ≤ I := sq_nonneg _
    nlinarith
  have k3 : 1.1931471803 / (1 + 1 / 1600) ≤ (Real.log 2 + 1 / 2) / c := by
    rw [div_le_div_iff₀ (by norm_num) hcp]
    have : c ≤ 1 + 1 / 1600 := by nlinarith
    nlinarith [Real.log_two_gt_d9]
  have k4 : Real.log 2 / c + 1 / (2 * c) = (Real.log 2 + 1 / 2) / c := by field_simp
  have k5 : a * (1 + 2 * a) ^ 2 / 16 ≤ (1 / 40) * (1 + 2 / 40) ^ 2 / 16 := by
    have : (1 + 2 * a) ^ 2 ≤ (1 + 2 / 40) ^ 2 := by nlinarith
    have : a * (1 + 2 * a) ^ 2 ≤ (1 / 40) * (1 + 2 / 40) ^ 2 := by nlinarith
    linarith
  have k6 : Real.exp a * (1 + 4 * a) ≤ (1 + 2 / 40) * (1 + 4 / 40) := by
    have := Real.exp_pos a
    nlinarith
  have k7 : 2 * poleR (box a) a ^ 2 ≤ 4 * a * Real.exp a := by linarith
  rw [k1] at hG
  nlinarith [Real.exp_pos a]

/-- **Certified lower bound on `Q₀` orthogonally to `w`, for `0 < a ≤ 1/40`.** Every normalised probe
`g` with `ĝ(i/2) = 0` has `Q₀(g) = Q(g) ≥ Q(box) + 1/40 ≥ λ₁ + 1/40`. -/
theorem weilQ0_perp_ge {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 40) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (h0 : poleR g a = 0) :
    lam a + 1 / 40 ≤ weilQ0 a g ∧ weilQ a (box a) + 1 / 40 ≤ weilQ0 a g := by
  -- a measurable version
  have hge := hp.memL2.aestronglyMeasurable.ae_eq_mk
  set g' := hp.memL2.aestronglyMeasurable.mk g
  have hg'm : Measurable g' := hp.memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  set g₁ := symCut a g' with hg₁
  have h₁ : g₁ =ᵐ[volume] g := by
    have := symCut_congr_ae a hge
    rw [symCut_probe hp] at this
    exact this.symm
  have hp₁ : Probe a g₁ :=
    ⟨symCut_even a _, symCut_supp a _, MemLp.ae_eq h₁.symm hp.memL2, by
      rw [archIntegrand_congr_ae h₁]; exact hp.arch⟩
  have hQ := weilQ_perp_ge_meas ha ha' hp₁ (symCut_measurable a hg'm)
    (by rw [normSq_congr_ae h₁]; exact hn) (by rw [poleR_congr_ae h₁]; exact h0)
  rw [weilQ_congr_ae h₁] at hQ
  have hQ0 : weilQ0 a g = weilQ a g := by unfold weilQ0; rw [h0]; ring
  have hlam := lam_le (box_probe a) (normSq_box ha)
  rw [hQ0]
  exact ⟨by linarith, hQ⟩

/-- **The ground state of `Q` is unique up to sign for `0 < a ≤ 1/40`.** -/
theorem groundState_unique_small {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 40) {g h : ℝ → ℝ}
    (hg : IsGroundState a g) (hh : IsGroundState a h) :
    g =ᵐ[volume] h ∨ g =ᵐ[volume] fun t => -h t := by
  refine groundState_unique ha (fun v hv hv0 => ?_) hg hh
  have h1 := (weilQ0_perp_ge ha ha' hv.1 hv.2.1 hv0).2
  have h2 := hv.2.2 (box a) (box_probe a) (normSq_box ha)
  have h3 : weilQ0 a v = weilQ a v := by unfold weilQ0; rw [hv0]; ring
  linarith

end Pilot1ca

#print axioms Pilot1ca.kerK_ge
#print axioms Pilot1ca.primeS_eq_zero
#print axioms Pilot1ca.poleR_box_sq_le
#print axioms Pilot1ca.edge_reflect
#print axioms Pilot1ca.autocorr_le_edge
#print axioms Pilot1ca.integral_autocorr
#print axioms Pilot1ca.integral_autocorr_Ioc
#print axioms Pilot1ca.integral_edge_ellK
#print axioms Pilot1ca.nearField_ge
#print axioms Pilot1ca.nearField_box_le
#print axioms Pilot1ca.integral_sq_le_of_perp
#print axioms Pilot1ca.weilQ0_perp_ge
#print axioms Pilot1ca.groundState_unique_small
