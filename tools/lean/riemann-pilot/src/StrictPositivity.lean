import Mathlib
import Positivity

/-! # The ground state of `Q₀` is strictly positive

`exists_unique_groundState0` gives a ground state `φ ≥ 0` of the pole-free form, unique up to sign.
Here `φ > 0` a.e. on `[−a, a]`.

1. **Euler–Lagrange.** `Q₀(φ + sψ) = Q₀(φ) + 2sB(φ, ψ) + s²Q₀(ψ)`, so at a ground state
   `B(φ, ψ) = λ₀⟨φ, ψ⟩` for every probe `ψ`.
2. **Truncated test functions.** `η_ε = (1 − φ/ε)⁺` on `[−a, a]` is a probe:
   `η_ε = c⁻¹·box − ε⁻¹·min(φ, ε)`, and `min(φ, ε)` is a contraction of `φ`. As a decreasing
   function of `φ`, `η_ε` makes the archimedean cross term `≤ 0` on interior pairs and `≤ ε/4` at the
   boundary. The Euler–Lagrange equation bounds the cross term below by `−O(ε)`.
3. **Fatou.** As `ε → 0`, `η_ε → 1_Z` with `Z = {φ = 0} ∩ [−a, a]`. In the limit,
   `∫_{u>0} K(u) ∫ (1_Z(t)φ(t+u) + φ(t)1_Z(t+u)) dt du = 0`.
4. **Tonelli.** `|Z|·∫φ = 0`, so `|Z| = 0`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## 1. The quadratic expansion and the Euler–Lagrange equation -/

/-- The symmetrised cross-correlation `x(u) = (∫φ(t)ψ(t+u) dt + ∫ψ(t)φ(t+u) dt)/2`. -/
def xcorr (φ ψ : ℝ → ℝ) (u : ℝ) : ℝ := ((∫ t, φ t * ψ (t + u)) + ∫ t, ψ t * φ (t + u)) / 2

/-- `K(u) = e^{u/2}/sinh u`. -/
def kerK (u : ℝ) : ℝ := Real.exp (u / 2) / Real.sinh u

theorem kerK_pos {u : ℝ} (hu : 0 < u) : 0 < kerK u :=
  div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu)

theorem autocorr_add_smul {φ ψ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (s u : ℝ) : autocorr (fun t => φ t + s * ψ t) u
      = autocorr φ u + 2 * s * xcorr φ ψ u + s ^ 2 * autocorr ψ u := by
  have i1 : Integrable (fun t => φ t * φ (t + u)) := integrable_mul_shift hφ u
  have i2 : Integrable (fun t => s * (φ t * ψ (t + u))) :=
    (integrable_mul_shift₂ hφ hψ u).const_mul s
  have i3 : Integrable (fun t => s * (ψ t * φ (t + u))) :=
    (integrable_mul_shift₂ hψ hφ u).const_mul s
  have i4 : Integrable (fun t => s ^ 2 * (ψ t * ψ (t + u))) :=
    (integrable_mul_shift hψ u).const_mul (s ^ 2)
  have j1 : Integrable (fun t => φ t * φ (t + u) + s * (φ t * ψ (t + u))) := i1.add i2
  have j2 : Integrable (fun t => s * (ψ t * φ (t + u)) + s ^ 2 * (ψ t * ψ (t + u))) := i3.add i4
  unfold autocorr xcorr
  calc (∫ t, (φ t + s * ψ t) * (φ (t + u) + s * ψ (t + u)))
      = ∫ t, ((φ t * φ (t + u) + s * (φ t * ψ (t + u)))
          + (s * (ψ t * φ (t + u)) + s ^ 2 * (ψ t * ψ (t + u)))) := by
        congr 1; funext t; ring
    _ = ((∫ t, φ t * φ (t + u)) + s * ∫ t, φ t * ψ (t + u))
          + (s * (∫ t, ψ t * φ (t + u)) + s ^ 2 * ∫ t, ψ t * ψ (t + u)) := by
        rw [integral_add j1 j2, integral_add i1 i2, integral_add i3 i4,
          integral_const_mul, integral_const_mul, integral_const_mul]
    _ = _ := by ring

/-- The archimedean cross integrand `(x(0) − x(u))K(u)`. -/
def archX (φ ψ : ℝ → ℝ) (u : ℝ) : ℝ := (xcorr φ ψ 0 - xcorr φ ψ u) * kerK u

theorem archIntegrand_add_smul {φ ψ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (s u : ℝ) : archIntegrand (fun t => φ t + s * ψ t) u
      = archIntegrand φ u + 2 * s * archX φ ψ u + s ^ 2 * archIntegrand ψ u := by
  have e0 := autocorr_add_smul hφ hψ s 0
  have eu := autocorr_add_smul hφ hψ s u
  unfold archIntegrand archX kerK
  rw [e0, eu]; ring

theorem probe_add_smul {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (s : ℝ) :
    Probe a (fun t => φ t + s * ψ t) :=
  (probe_add_sub hφ (probe_smul hψ s)).1

theorem archX_integrable {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) :
    IntegrableOn (archX φ ψ) (Ioi 0) := by
  have hp := (probe_add_smul hφ hψ 1).arch
  have hm := (probe_add_smul hφ hψ (-1)).arch
  have e : archX φ ψ = fun u => (archIntegrand (fun t => φ t + 1 * ψ t) u
      - archIntegrand (fun t => φ t + -1 * ψ t) u) / 4 := by
    funext u
    rw [archIntegrand_add_smul hφ.memL2 hψ.memL2, archIntegrand_add_smul hφ.memL2 hψ.memL2]
    ring
  rw [e]; exact (hp.sub hm).div_const 4

/-- The prime cross term `Σ_{n ≤ e^δ} Λ(n)/√n · x(log n)`. -/
def primeX (a : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (primeCut a), ArithmeticFunction.vonMangoldt n / Real.sqrt n
    * xcorr φ ψ (Real.log n)

/-- The bilinear form of `Q₀`. -/
def bil0 (a : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  weilConst * xcorr φ ψ 0 + (∫ u in Ioi 0, archX φ ψ u) - 2 * primeX a φ ψ

theorem normSq_add_smul {φ ψ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) (s : ℝ) :
    normSq (fun t => φ t + s * ψ t) = normSq φ + 2 * s * xcorr φ ψ 0 + s ^ 2 * normSq ψ := by
  rw [← autocorr_zero, ← autocorr_zero, ← autocorr_zero]; exact autocorr_add_smul hφ hψ s 0

theorem weilQ0_add_smul {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (s : ℝ) :
    weilQ0 a (fun t => φ t + s * ψ t)
      = weilQ0 a φ + 2 * s * bil0 a φ ψ + s ^ 2 * weilQ0 a ψ := by
  have hA : archE (fun t => φ t + s * ψ t)
      = archE φ + 2 * s * (∫ u in Ioi 0, archX φ ψ u) + s ^ 2 * archE ψ := by
    have jX : IntegrableOn (fun u => 2 * s * archX φ ψ u) (Ioi 0) :=
      (archX_integrable hφ hψ).const_mul _
    have jA : IntegrableOn (fun u => archIntegrand φ u + 2 * s * archX φ ψ u) (Ioi 0) :=
      hφ.arch.add jX
    have jB : IntegrableOn (fun u => s ^ 2 * archIntegrand ψ u) (Ioi 0) := hψ.arch.const_mul _
    unfold archE
    calc (∫ u in Ioi 0, archIntegrand (fun t => φ t + s * ψ t) u)
        = ∫ u in Ioi 0, ((archIntegrand φ u + 2 * s * archX φ ψ u)
            + s ^ 2 * archIntegrand ψ u) := by
          congr 1; funext u; rw [archIntegrand_add_smul hφ.memL2 hψ.memL2]
      _ = _ := by
          rw [integral_add jA jB, integral_add hφ.arch jX, integral_const_mul, integral_const_mul]
  have hS : primeS (fun t => φ t + s * ψ t) = primeS φ + 2 * s * primeX a φ ψ + s ^ 2 * primeS ψ := by
    unfold primeS primeX
    rw [prime_sum_eq (probe_add_smul hφ hψ s).supp, prime_sum_eq hφ.supp, prime_sum_eq hψ.supp,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [autocorr_add_smul hφ.memL2 hψ.memL2]; ring
  rw [weilQ0_eq', weilQ0_eq', weilQ0_eq', normSq_add_smul hφ.memL2 hψ.memL2, hA, hS]
  unfold bil0; ring

/-- A real quadratic `2sb + s²c` that is non-negative for every `s` has `b = 0`. -/
theorem quad_zero {b c : ℝ} (h : ∀ s : ℝ, 0 ≤ 2 * s * b + s ^ 2 * c) : b = 0 := by
  have hc : 0 ≤ c := by have h1 := h 1; have h2 := h (-1); nlinarith
  by_contra hb
  have hb' : b ≠ 0 := hb
  have h1 := h (-b / (c + 1))
  have hc1 : 0 < c + 1 := by linarith
  have hb2 : 0 < b ^ 2 := by positivity
  have e : 2 * (-b / (c + 1)) * b + (-b / (c + 1)) ^ 2 * c
      = -(b ^ 2 * (c + 2) / (c + 1) ^ 2) := by field_simp; ring
  rw [e] at h1
  have h2 : 0 < b ^ 2 * (c + 2) / (c + 1) ^ 2 := by positivity
  linarith

/-- **The Euler–Lagrange equation**: at a ground state of `Q₀`, `B(φ, ψ) = λ₀⟨φ, ψ⟩`. -/
theorem euler_lagrange0 {a : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hψ : Probe a ψ) : bil0 a φ ψ = lam0 a * xcorr φ ψ 0 := by
  have hq : weilQ0 a φ = lam0 a * normSq φ := ((isGroundState0_iff ha).1 hφ).1.2
  apply sub_eq_zero.1
  refine quad_zero (c := weilQ0 a ψ - lam0 a * normSq ψ) fun s => ?_
  have := lam0_mul_le (probe_add_smul hφ.1 hψ s)
  rw [weilQ0_add_smul hφ.1 hψ, normSq_add_smul hφ.1.memL2 hψ.memL2, hq] at this
  nlinarith [this]

/-! ## 2. The cross term as a pairwise difference -/

theorem xcorr_sub_eq {φ ψ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) (u : ℝ) :
    xcorr φ ψ 0 - xcorr φ ψ u
      = (∫ t, (φ t - φ (t + u)) * (ψ t - ψ (t + u))) / 2 := by
  have i0 : Integrable (fun t => φ t * ψ t) := by
    simpa using integrable_mul_shift₂ hφ hψ 0
  have i1 := integrable_mul_shift₂ hφ hψ u
  have i2 := integrable_mul_shift₂ hψ hφ u
  have i3 : Integrable (fun t => φ (t + u) * ψ (t + u)) := i0.comp_add_right u
  have hsh : (∫ t, φ (t + u) * ψ (t + u)) = ∫ t, φ t * ψ t :=
    integral_add_right_eq_self (fun t => φ t * ψ t) u
  have hx0 : xcorr φ ψ 0 = ∫ t, φ t * ψ t := by
    unfold xcorr; simp only [add_zero]
    rw [show (fun t => ψ t * φ t) = fun t => φ t * ψ t by funext t; ring]; ring
  have j1 : Integrable (fun t => φ t * ψ t - φ t * ψ (t + u)) := i0.sub i1
  have j2 : Integrable (fun t => φ t * ψ t - φ t * ψ (t + u) - ψ t * φ (t + u)) := j1.sub i2
  have hsum : (∫ t, (φ t * ψ t - φ t * ψ (t + u) - ψ t * φ (t + u) + φ (t + u) * ψ (t + u)))
      = (∫ t, φ t * ψ t) - (∫ t, φ t * ψ (t + u)) - (∫ t, ψ t * φ (t + u))
        + ∫ t, φ (t + u) * ψ (t + u) := by
    rw [integral_add j2 i3, integral_sub j1 i2, integral_sub i0 i1]
  have hfun : (fun t => (φ t - φ (t + u)) * (ψ t - ψ (t + u)))
      = fun t => φ t * ψ t - φ t * ψ (t + u) - ψ t * φ (t + u) + φ (t + u) * ψ (t + u) := by
    funext t; ring
  rw [hfun, hsum, hsh, hx0]
  unfold xcorr
  ring

/-! ## 3. The truncated test functions -/

/-- `min(φ, ε)`. -/
def trunc (φ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ := fun x => min (φ x) ε

/-- `η_ε = (1 − φ/ε)⁺` on `[−a, a]`, `0` outside. -/
def etaF (a : ℝ) (φ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x => if |x| ≤ a then max (1 - φ x / ε) 0 else 0

/-- The archimedean integrand is half the squared difference norm against `kerK`. -/
theorem archIntegrand_eq {g : ℝ → ℝ} (hg : MemLp g 2 volume) (u : ℝ) :
    archIntegrand g u = normSq (fun t => g t - g (t + u)) / 2 * kerK u := by
  rw [normSq_sub_shift hg u]; unfold archIntegrand kerK; ring

theorem trunc_probe {a : ℝ} {φ : ℝ → ℝ} (hp : Probe a φ) (hm : Measurable φ)
    (h0 : ∀ t, 0 ≤ φ t) {ε : ℝ} (hε : 0 < ε) : Probe a (trunc φ ε) := by
  have htm : Measurable (trunc φ ε) := hm.min measurable_const
  have hL : MemLp (trunc φ ε) 2 volume := by
    refine hp.memL2.of_le htm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    simp only [trunc, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_min (h0 t) hε.le), abs_of_nonneg (h0 t)]
    exact min_le_left _ _
  refine ⟨fun u => by simp only [trunc, hp.even], fun u hu => by
    simp only [trunc, hp.supp u hu]; exact min_eq_left hε.le, hL, ?_⟩
  refine hp.arch.mono' (measurable_archIntegrand hL).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (archIntegrand_nonneg hL hu),
    archIntegrand_eq hL, archIntegrand_eq hp.memL2]
  refine mul_le_mul_of_nonneg_right ?_ (kerK_pos hu).le
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  refine integral_mono (hL.sub (memLp_shift hL u)).integrable_sq
    (hp.memL2.sub (memLp_shift hp.memL2 u)).integrable_sq fun t => ?_
  simp only [trunc]
  have := abs_min_sub_min_le_max (φ t) ε (φ (t + u)) ε
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at this
  exact sq_le_sq.2 this

theorem max_one_sub_eq {x ε : ℝ} (hε : 0 < ε) : max (1 - x / ε) 0 = 1 - min x ε / ε := by
  rcases le_total x ε with h | h
  · rw [min_eq_left h, max_eq_left]
    rw [sub_nonneg, div_le_one hε]; exact h
  · rw [min_eq_right h, div_self hε.ne', sub_self, max_eq_right]
    rw [sub_nonpos, le_div_iff₀ hε, one_mul]; exact h

theorem etaF_probe {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hp : Probe a φ) (hm : Measurable φ)
    (h0 : ∀ t, 0 ≤ φ t) {ε : ℝ} (hε : 0 < ε) : Probe a (etaF a φ ε) := by
  set c := 1 / Real.sqrt (2 * a) with hc
  have hc0 : 0 < c := by positivity
  have e : etaF a φ ε = fun t => (1 / c) * box a t - (1 / ε) * trunc φ ε t := by
    funext x
    unfold etaF
    rw [box_apply]
    by_cases hx : |x| ≤ a
    · simp only [hx, ite_true]; rw [← hc, max_one_sub_eq hε]; unfold trunc; field_simp
    · simp only [hx, ite_false]
      simp only [trunc, hp.supp x (lt_of_not_ge hx), min_eq_left hε.le]; ring
  rw [e]
  exact (probe_add_sub (probe_smul (box_probe a) (1 / c))
    (probe_smul (trunc_probe hp hm h0 hε) (1 / ε))).2

theorem etaF_nonneg (a : ℝ) (φ : ℝ → ℝ) (ε : ℝ) (x : ℝ) : 0 ≤ etaF a φ ε x := by
  unfold etaF; split_ifs <;> simp

theorem mul_etaF_le {a : ℝ} {φ : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    φ x * etaF a φ ε x ≤ ε / 4 := by
  unfold etaF
  split_ifs
  · rcases le_total (1 - φ x / ε) 0 with h | h
    · rw [max_eq_right h, mul_zero]; positivity
    · rw [max_eq_left h]
      have : φ x * (1 - φ x / ε) = ε / 4 - (φ x - ε / 2) ^ 2 / ε := by field_simp; ring
      rw [this]
      have : 0 ≤ (φ x - ε / 2) ^ 2 / ε := by positivity
      linarith
  · rw [mul_zero]; positivity

/-! ## 4. The Euler–Lagrange lower bound -/

theorem xcorr_nonneg {φ ψ : ℝ → ℝ} (hφ : ∀ t, 0 ≤ φ t) (hψ : ∀ t, 0 ≤ ψ t) (u : ℝ) :
    0 ≤ xcorr φ ψ u := by
  unfold xcorr
  have h1 : 0 ≤ ∫ t, φ t * ψ (t + u) := integral_nonneg fun t => mul_nonneg (hφ t) (hψ _)
  have h2 : 0 ≤ ∫ t, ψ t * φ (t + u) := integral_nonneg fun t => mul_nonneg (hψ t) (hφ _)
  positivity

theorem xcorr_zero_eq (φ ψ : ℝ → ℝ) : xcorr φ ψ 0 = ∫ t, φ t * ψ t := by
  unfold xcorr; simp only [add_zero]
  rw [show (fun t => ψ t * φ t) = fun t => φ t * ψ t by funext t; ring]; ring

/-- **`∫_{u>0} archX(φ, η_ε) ≥ −|λ₀ − C|·(a/2)·ε`** at a non-negative ground state. -/
theorem archX_eta_ge {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hgs : IsGroundState0 a φ)
    (hm : Measurable φ) (h0 : ∀ t, 0 ≤ φ t) {ε : ℝ} (hε : 0 < ε) :
    -(|lam0 a - weilConst| * (a / 2) * ε) ≤ ∫ u in Ioi 0, archX φ (etaF a φ ε) u := by
  have hη := etaF_probe ha hgs.1 hm h0 hε
  have hel := euler_lagrange0 ha hgs hη
  have hP : 0 ≤ primeX a φ (etaF a φ ε) :=
    Finset.sum_nonneg fun n _ => mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (xcorr_nonneg h0 (etaF_nonneg a φ ε) _)
  set x0 := xcorr φ (etaF a φ ε) 0 with hx0
  have hx0nn : 0 ≤ x0 := xcorr_nonneg h0 (etaF_nonneg a φ ε) 0
  have hx0le : x0 ≤ a / 2 * ε := by
    rw [hx0, xcorr_zero_eq]
    have hb : Integrable ((Icc (-a) a).indicator fun _ => ε / 4) :=
      (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
    calc (∫ t, φ t * etaF a φ ε t) ≤ ∫ t, (Icc (-a) a).indicator (fun _ => ε / 4) t := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t =>
            mul_nonneg (h0 t) (etaF_nonneg a φ ε t)) hb (Eventually.of_forall fun t => ?_)
          by_cases ht : t ∈ Icc (-a) a
          · rw [Set.indicator_of_mem ht]; exact mul_etaF_le hε t
          · rw [Set.indicator_of_notMem ht]
            have : ¬ |t| ≤ a := fun h => ht (abs_le.1 h)
            simp [etaF, this]
      _ = a / 2 * ε := by
          rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring
  unfold bil0 at hel
  have habs := neg_abs_le (lam0 a - weilConst)
  have : ∫ u in Ioi 0, archX φ (etaF a φ ε) u = (lam0 a - weilConst) * x0
      + 2 * primeX a φ (etaF a φ ε) := by linarith
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hx0le (abs_nonneg (lam0 a - weilConst)),
    abs_mul_abs_self (lam0 a - weilConst), neg_abs_le ((lam0 a - weilConst) * x0),
    abs_mul (lam0 a - weilConst) x0, abs_of_nonneg hx0nn]

/-! ## 5. The pairwise bound -/

/-- The boundary strips of width `u`. -/
def strip (a u : ℝ) : ℝ → ℝ :=
  fun t => (Icc (a - u) a).indicator 1 t + (Icc (-a - u) (-a)).indicator 1 t

/-- **`(φ(t) − φ(t+u))(η(t) − η(t+u)) ≤ (ε/4)·strip(t)`** for `u > 0`: `η` decreases in `φ` inside
`[−a, a]`, and at the boundary the product is `φ·η ≤ ε/4`. -/
theorem pair_le {a : ℝ} {φ : ℝ → ℝ} (hp : Probe a φ) {ε : ℝ} (hε : 0 < ε)
    {u : ℝ} (hu : 0 < u) (t : ℝ) :
    (φ t - φ (t + u)) * (etaF a φ ε t - etaF a φ ε (t + u)) ≤ ε / 4 * strip a u t := by
  have hs0 : 0 ≤ strip a u t := by
    unfold strip; simp only [Set.indicator_apply, Pi.one_apply]; split_ifs <;> norm_num
  by_cases h1 : |t| ≤ a <;> by_cases h2 : |t + u| ≤ a
  · -- interior: `η` is a decreasing function of `φ`
    have : (φ t - φ (t + u)) * (etaF a φ ε t - etaF a φ ε (t + u)) ≤ 0 := by
      simp only [etaF, h1, h2, ite_true]
      rcases le_total (φ t) (φ (t + u)) with h | h
      · refine mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.2 ?_)
        exact max_le_max (by linarith [div_le_div_of_nonneg_right h hε.le]) le_rfl
      · refine mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.2 ?_)
        exact max_le_max (by linarith [div_le_div_of_nonneg_right h hε.le]) le_rfl
    nlinarith
  · -- `t` inside, `t + u` outside: `t ∈ [a − u, a]`
    have hφs : φ (t + u) = 0 := hp.supp _ (lt_of_not_ge h2)
    have hηs : etaF a φ ε (t + u) = 0 := by simp [etaF, h2]
    rw [hφs, hηs, sub_zero, sub_zero]
    have hmem : t ∈ Icc (a - u) a := by
      rw [abs_le] at h1; rw [not_le, lt_abs] at h2
      refine ⟨?_, h1.2⟩
      rcases h2 with h2 | h2 <;> linarith
    have : 1 ≤ strip a u t := by
      unfold strip; rw [Set.indicator_of_mem hmem]
      have := Set.indicator_nonneg (s := Icc (-a - u) (-a)) (f := (1 : ℝ → ℝ))
        (fun _ _ => zero_le_one) t
      simp only [Pi.one_apply] at this ⊢; linarith
    nlinarith [mul_etaF_le (a := a) (φ := φ) hε t]
  · -- `t` outside, `t + u` inside: `t ∈ [−a − u, −a]`
    have hφt : φ t = 0 := hp.supp _ (lt_of_not_ge h1)
    have hηt : etaF a φ ε t = 0 := by simp [etaF, h1]
    rw [hφt, hηt, zero_sub, zero_sub, neg_mul_neg]
    have hmem : t ∈ Icc (-a - u) (-a) := by
      rw [abs_le] at h2; rw [not_le, lt_abs] at h1
      constructor
      · linarith [h2.1]
      · rcases h1 with h1 | h1
        · linarith [h2.2]
        · linarith
    have : 1 ≤ strip a u t := by
      unfold strip; rw [Set.indicator_of_mem hmem]
      have := Set.indicator_nonneg (s := Icc (a - u) a) (f := (1 : ℝ → ℝ))
        (fun _ _ => zero_le_one) t
      simp only [Pi.one_apply] at this ⊢; linarith
    nlinarith [mul_etaF_le (a := a) (φ := φ) hε (t + u)]
  · have hφt : φ t = 0 := hp.supp _ (lt_of_not_ge h1)
    have hφs : φ (t + u) = 0 := hp.supp _ (lt_of_not_ge h2)
    rw [hφt, hφs, sub_zero, zero_mul]
    positivity

/-! ## 6. The limit `ε → 0` -/

/-- The indicator of `Z = {φ = 0} ∩ [−a, a]`. -/
def zind (a : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => if |x| ≤ a ∧ φ x = 0 then 1 else 0

theorem zind_mul (a : ℝ) (φ : ℝ → ℝ) (x : ℝ) : zind a φ x * φ x = 0 := by
  unfold zind; split_ifs with h
  · rw [h.2, mul_zero]
  · rw [zero_mul]

theorem zind_nonneg (a : ℝ) (φ : ℝ → ℝ) (x : ℝ) : 0 ≤ zind a φ x := by
  unfold zind; split_ifs <;> norm_num

/-- `ε_k = 1/(k+1)`. -/
def epsk (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem epsk_pos (k : ℕ) : 0 < epsk k := by unfold epsk; positivity

theorem epsk_tendsto : Tendsto epsk atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- `η_{ε_k}(x) → 1_Z(x)`. -/
theorem eta_tendsto {a : ℝ} {φ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ φ t) (x : ℝ) :
    Tendsto (fun k => etaF a φ (epsk k) x) atTop (𝓝 (zind a φ x)) := by
  by_cases hx : |x| ≤ a
  · by_cases hφ : φ x = 0
    · have : ∀ k, etaF a φ (epsk k) x = 1 := fun k => by simp [etaF, hx, hφ]
      simp only [this, zind, hx, hφ, and_self, ite_true]; exact tendsto_const_nhds
    · have hpos : 0 < φ x := lt_of_le_of_ne (h0 x) (Ne.symm hφ)
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
      have hz : zind a φ x = 0 := by simp [zind, hφ]
      rw [hz]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      have hek : epsk k < φ x := by
        unfold epsk
        refine lt_of_le_of_lt ?_ hN
        gcongr
      have : 1 - φ x / epsk k ≤ 0 := by
        rw [sub_nonpos, le_div_iff₀ (epsk_pos k), one_mul]; exact hek.le
      simp [etaF, hx, max_eq_right this]
  · have : ∀ k, etaF a φ (epsk k) x = 0 := fun k => by simp [etaF, hx]
    have hz : zind a φ x = 0 := by simp [zind, hx]
    simp only [this, hz]; exact tendsto_const_nhds

/-- The non-negative gap `H_k(u, t) = (ε_k/4)·strip − (φ(t) − φ(t+u))(η(t) − η(t+u))`. -/
def gapH (a : ℝ) (φ : ℝ → ℝ) (k : ℕ) (u t : ℝ) : ℝ :=
  epsk k / 4 * strip a u t
    - (φ t - φ (t + u)) * (etaF a φ (epsk k) t - etaF a φ (epsk k) (t + u))

/-- The limit gap `H(u, t) = 1_Z(t)φ(t+u) + φ(t)1_Z(t+u)`. -/
def gapInf (a : ℝ) (φ : ℝ → ℝ) (u t : ℝ) : ℝ :=
  zind a φ t * φ (t + u) + φ t * zind a φ (t + u)

theorem gapH_nonneg {a : ℝ} {φ : ℝ → ℝ} (hp : Probe a φ) (k : ℕ) {u : ℝ} (hu : 0 < u)
    (t : ℝ) : 0 ≤ gapH a φ k u t := by
  unfold gapH; linarith [pair_le hp (epsk_pos k) hu t]

theorem gapH_tendsto {a : ℝ} {φ : ℝ → ℝ} (h0 : ∀ t, 0 ≤ φ t) (u t : ℝ) :
    Tendsto (fun k => gapH a φ k u t) atTop (𝓝 (gapInf a φ u t)) := by
  have h1 : Tendsto (fun k => epsk k / 4 * strip a u t) atTop (𝓝 (0 / 4 * strip a u t)) :=
    (epsk_tendsto.div_const 4).mul_const _
  have h2 := ((eta_tendsto (a := a) h0 t).sub (eta_tendsto (a := a) h0 (t + u))).const_mul (φ t - φ (t + u))
  have e : gapInf a φ u t = 0 / 4 * strip a u t
      - (φ t - φ (t + u)) * (zind a φ t - zind a φ (t + u)) := by
    unfold gapInf
    have := zind_mul a φ t
    have := zind_mul a φ (t + u)
    linear_combination this + (zind_mul a φ t)
  rw [e]
  exact h1.sub h2

theorem integral_strip {a u : ℝ} (hu : 0 < u) : ∫ t, strip a u t = 2 * u := by
  unfold strip
  have i1 : Integrable ((Icc (a - u) a).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have i2 : Integrable ((Icc (-a - u) (-a)).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  rw [integral_add i1 i2, integral_indicator_one measurableSet_Icc,
    integral_indicator_one measurableSet_Icc, Measure.real, Measure.real, Real.volume_Icc,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

theorem strip_integrable (a u : ℝ) : Integrable (strip a u) :=
  ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)).add
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne))

theorem pair_integrable {φ ψ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) (u : ℝ) :
    Integrable (fun t => (φ t - φ (t + u)) * (ψ t - ψ (t + u))) := by
  have := integrable_mul_shift₂ (hφ.sub (memLp_shift hφ u)) (hψ.sub (memLp_shift hψ u)) 0
  simpa using this

/-- **`K(u)∫H_k(u, ·) = ε_k·uK(u)/2 − 2·archX(u)`** for `u > 0`. -/
theorem integral_gapH {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hp : Probe a φ) (hm : Measurable φ)
    (h0 : ∀ t, 0 ≤ φ t) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    kerK u * ∫ t, gapH a φ k u t
      = epsk k * (u * kerK u) / 2 - 2 * archX φ (etaF a φ (epsk k)) u := by
  have hη := etaF_probe ha hp hm h0 (epsk_pos k)
  have hs := (strip_integrable a u).const_mul (epsk k / 4)
  have hd := pair_integrable hp.memL2 hη.memL2 u
  unfold gapH
  rw [integral_sub hs hd, integral_const_mul, integral_strip hu]
  unfold archX
  rw [xcorr_sub_eq hp.memL2 hη.memL2 u]
  ring

/-! ## 7. Fatou and Tonelli -/

theorem kerK_measurable : Measurable kerK :=
  (Real.measurable_exp.comp (measurable_id.div_const 2)).div Real.measurable_sinh

theorem uK_integrable : IntegrableOn (fun u => u * kerK u) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 16).mono'
    (measurable_id.mul kerK_measurable).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
  have hu0 : (0 : ℝ) < u := hu
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu0.le (kerK_pos hu0).le)]
  exact u_archK_le hu0

theorem archX_measurable {φ ψ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) :
    Measurable (archX φ ψ) := by
  have e : archX φ ψ = fun u => (archIntegrand (fun t => φ t + 1 * ψ t) u
      - archIntegrand (fun t => φ t + -1 * ψ t) u) / 4 := by
    funext u
    rw [archIntegrand_add_smul hφ hψ, archIntegrand_add_smul hφ hψ]
    ring
  rw [e]
  exact ((measurable_archIntegrand (hφ.add (hψ.const_mul 1))).sub
    (measurable_archIntegrand (hφ.add (hψ.const_mul (-1))))).div_const 4

theorem zind_measurable {a : ℝ} {φ : ℝ → ℝ} (hm : Measurable φ) : Measurable (zind a φ) := by
  unfold zind
  exact Measurable.ite ((measurableSet_le continuous_abs.measurable measurable_const).inter
    (measurableSet_eq_fun hm measurable_const)) measurable_const measurable_const

/-- **The limit gap vanishes**: `∫ gapInf(u, t) dt = 0` for a.e. `u > 0`. -/
theorem gapInf_zero {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hgs : IsGroundState0 a φ)
    (hm : Measurable φ) (h0 : ∀ t, 0 ≤ φ t) :
    ∀ᵐ u ∂(volume.restrict (Ioi 0)), ∫⁻ t, ENNReal.ofReal (gapInf a φ u t) = 0 := by
  have hp := hgs.1
  set κ := |lam0 a - weilConst| * (a / 2) with hκ
  set M := ∫ u in Ioi 0, u * kerK u with hM
  have hZm := zind_measurable (a := a) hm
  have hGm : Measurable (Function.uncurry fun (u t : ℝ) =>
      ENNReal.ofReal (kerK u * gapInf a φ u t)) := by
    unfold gapInf
    refine ENNReal.measurable_ofReal.comp ((kerK_measurable.comp measurable_fst).mul ?_)
    exact ((hZm.comp measurable_snd).mul (hm.comp (measurable_snd.add measurable_fst))).add
      ((hm.comp measurable_snd).mul (hZm.comp (measurable_snd.add measurable_fst)))
  set Φ : ℝ → ENNReal := fun u => ∫⁻ t, ENNReal.ofReal (kerK u * gapInf a φ u t) with hΦ
  have hΦm : Measurable Φ := hGm.lintegral_prod_right' (ν := volume)
  set Ψ : ℕ → ℝ → ℝ := fun k u => epsk k * (u * kerK u) / 2
    - 2 * archX φ (etaF a φ (epsk k)) u with hΨ
  have hηp : ∀ k, Probe a (etaF a φ (epsk k)) := fun k => etaF_probe ha hp hm h0 (epsk_pos k)
  have hΨm : ∀ k, Measurable (Ψ k) := fun k =>
    ((measurable_const.mul (measurable_id.mul kerK_measurable)).div_const 2).sub
      (measurable_const.mul (archX_measurable hp.memL2 (hηp k).memL2))
  have hΨint : ∀ k, IntegrableOn (Ψ k) (Ioi 0) := fun k =>
    ((uK_integrable.const_mul (epsk k)).div_const 2).sub
      ((archX_integrable hp (hηp k)).const_mul 2)
  have hgi : ∀ k u, Integrable (fun t => gapH a φ k u t) := fun k u =>
    ((strip_integrable a u).const_mul _).sub (pair_integrable hp.memL2 (hηp k).memL2 u)
  have hΨeq : ∀ k, ∀ u ∈ Ioi (0 : ℝ),
      Ψ k u = ∫ t, kerK u * gapH a φ k u t := by
    intro k u hu
    rw [integral_const_mul, integral_gapH ha hp hm h0 k hu]
  have hΨnn : ∀ k, ∀ u ∈ Ioi (0 : ℝ), 0 ≤ Ψ k u := by
    intro k u hu
    rw [hΨeq k u hu]
    exact integral_nonneg fun t => mul_nonneg (kerK_pos hu).le (gapH_nonneg hp k hu t)
  -- Fatou in `t`, for each `u > 0`
  have hpt : ∀ u ∈ Ioi (0 : ℝ), Φ u ≤ liminf (fun k => ENNReal.ofReal (Ψ k u)) atTop := by
    intro u hu
    have hlim : ∀ t, Tendsto (fun k => ENNReal.ofReal (kerK u * gapH a φ k u t)) atTop
        (𝓝 (ENNReal.ofReal (kerK u * gapInf a φ u t))) := fun t =>
      (ENNReal.continuous_ofReal.tendsto _).comp ((gapH_tendsto (a := a) h0 u t).const_mul _)
    calc Φ u = ∫⁻ t, liminf (fun k => ENNReal.ofReal (kerK u * gapH a φ k u t)) atTop :=
          lintegral_congr fun t => (hlim t).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ t, ENNReal.ofReal (kerK u * gapH a φ k u t)) atTop :=
          lintegral_liminf_le' fun k => ((hgi k u).const_mul (kerK u)).aemeasurable.ennreal_ofReal
      _ = liminf (fun k => ENNReal.ofReal (Ψ k u)) atTop := by
          congr 1; funext k
          rw [hΨeq k u hu, ofReal_integral_eq_lintegral_ofReal ((hgi k u).const_mul (kerK u))
            (Eventually.of_forall fun t => mul_nonneg (kerK_pos hu).le (gapH_nonneg hp k hu t))]
  -- Fatou in `u`
  have hbound : ∀ k, ∫⁻ u in Ioi 0, ENNReal.ofReal (Ψ k u)
      ≤ ENNReal.ofReal (epsk k * (M / 2 + 2 * κ)) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hΨint k)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hΨnn k)))]
    apply ENNReal.ofReal_le_ofReal
    have hX := archX_eta_ge ha hgs hm h0 (epsk_pos k)
    have e : ∫ u in Ioi 0, Ψ k u
        = epsk k * M / 2 - 2 * ∫ u in Ioi 0, archX φ (etaF a φ (epsk k)) u := by
      simp only [hΨ]
      rw [integral_sub ((uK_integrable.const_mul (epsk k)).div_const 2)
        ((archX_integrable hp (hηp k)).const_mul 2), integral_div, integral_const_mul,
        integral_const_mul]
    rw [e]
    have := epsk_pos k
    nlinarith
  have hlimit : Tendsto (fun k => ENNReal.ofReal (epsk k * (M / 2 + 2 * κ))) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto _).comp (epsk_tendsto.mul_const (M / 2 + 2 * κ))
    rw [zero_mul, ENNReal.ofReal_zero] at this
    exact this
  have hint0 : ∫⁻ u in Ioi 0, Φ u = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ u in Ioi 0, Φ u
        ≤ ∫⁻ u in Ioi 0, liminf (fun k => ENNReal.ofReal (Ψ k u)) atTop :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ ≤ liminf (fun k => ∫⁻ u in Ioi 0, ENNReal.ofReal (Ψ k u)) atTop :=
          lintegral_liminf_le' fun k => (hΨm k).ennreal_ofReal.aemeasurable
      _ ≤ liminf (fun k => ENNReal.ofReal (epsk k * (M / 2 + 2 * κ))) atTop :=
          liminf_le_liminf (Eventually.of_forall hbound)
      _ = 0 := hlimit.liminf_eq
  have hae := (lintegral_eq_zero_iff hΦm).1 hint0
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with u hu hu0
  have hK := kerK_pos hu0
  simp only [hΦ, Pi.zero_apply] at hu
  simp_rw [ENNReal.ofReal_mul hK.le] at hu
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hu
  rcases mul_eq_zero.1 hu with h | h
  · exact absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 hK)
  · exact h

/-! ## 8. Strict positivity -/

/-- **A non-negative measurable ground state of `Q₀` is positive a.e. on `[−a, a]`.** -/
theorem groundState0_pos_of_nonneg {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hgs : IsGroundState0 a φ)
    (hm : Measurable φ) (h0 : ∀ t, 0 ≤ φ t) : ∀ᵐ t, |t| ≤ a → 0 < φ t := by
  have hZm := zind_measurable (a := a) hm
  have hsplit : ∀ᵐ u ∂(volume.restrict (Ioi 0)),
      (∫⁻ t, ENNReal.ofReal (zind a φ t * φ (t + u))) = 0 ∧
        (∫⁻ t, ENNReal.ofReal (φ t * zind a φ (t + u))) = 0 := by
    filter_upwards [gapInf_zero ha hgs hm h0] with u hu
    unfold gapInf at hu
    have e : ∀ t, ENNReal.ofReal (zind a φ t * φ (t + u) + φ t * zind a φ (t + u))
        = ENNReal.ofReal (zind a φ t * φ (t + u)) + ENNReal.ofReal (φ t * zind a φ (t + u)) :=
      fun t => ENNReal.ofReal_add (mul_nonneg (zind_nonneg a φ t) (h0 _))
        (mul_nonneg (h0 t) (zind_nonneg a φ _))
    simp_rw [e] at hu
    have hA : Measurable fun t => ENNReal.ofReal (zind a φ t * φ (t + u)) :=
      (hZm.mul (hm.comp (measurable_id.add measurable_const))).ennreal_ofReal
    rw [lintegral_add_left hA] at hu
    exact add_eq_zero.1 hu
  have hprod := tonelli_zero hZm hm (zind_nonneg a φ) hsplit
  have hφne : (∫⁻ t, ENNReal.ofReal (φ t)) ≠ 0 := by
    intro h
    have hz : φ =ᵐ[volume] 0 := by
      filter_upwards [(lintegral_eq_zero_iff hm.ennreal_ofReal).1 h] with t ht
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht ⊢
      linarith [h0 t]
    have := normSq_congr_ae hz
    rw [hgs.2.1] at this
    simp [normSq] at this
  have hZ : (∫⁻ t, ENNReal.ofReal (zind a φ t)) = 0 := (mul_eq_zero.1 hprod).resolve_right hφne
  filter_upwards [(lintegral_eq_zero_iff hZm.ennreal_ofReal).1 hZ] with t ht hta
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht
  by_contra hneg
  have hφt : φ t = 0 := le_antisymm (not_lt.1 hneg) (h0 t)
  have : zind a φ t = 1 := by simp [zind, hta, hφt]
  linarith

theorem symCut_measurable (a : ℝ) {f : ℝ → ℝ} (hf : Measurable f) : Measurable (symCut a f) := by
  unfold symCut
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    ((hf.add (hf.comp measurable_neg)).div_const 2) measurable_const

theorem symCut_congr_ae (a : ℝ) {f f' : ℝ → ℝ} (h : f =ᵐ[volume] f') :
    symCut a f =ᵐ[volume] symCut a f' := by
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h, hn] with t h1 h2
  simp only [Function.comp_apply] at h2
  unfold symCut; rw [h1, h2]

/-- **The pole-free form `Q₀` has a ground state `φ` that is positive a.e. on `[−a, a]`, and every
ground state is `±φ` a.e.** -/
theorem exists_positive_groundState0 {a : ℝ} (ha : 0 < a) :
    ∃ φ, IsGroundState0 a φ ∧ (∀ t, 0 ≤ φ t) ∧ (∀ᵐ t, |t| ≤ a → 0 < φ t) ∧
      ∀ g, IsGroundState0 a g → g =ᵐ[volume] φ ∨ g =ᵐ[volume] fun t => -φ t := by
  obtain ⟨φ₀, hgs₀, hnn₀, huniq⟩ := exists_unique_groundState0 ha
  have hp₀ := hgs₀.1
  have hge : φ₀ =ᵐ[volume] hp₀.memL2.aestronglyMeasurable.mk φ₀ :=
    hp₀.memL2.aestronglyMeasurable.ae_eq_mk
  set g' := hp₀.memL2.aestronglyMeasurable.mk φ₀
  have hg'm : Measurable g' := hp₀.memL2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  set φ := symCut a (fun t => |g' t|) with hφ
  have habs : (fun t => |g' t|) =ᵐ[volume] φ₀ := by
    filter_upwards [hge, hnn₀] with t h1 h2
    rw [← h1, abs_of_nonneg h2]
  have hφφ₀ : φ =ᵐ[volume] φ₀ := by
    have := symCut_congr_ae a habs
    rwa [symCut_probe hp₀] at this
  have hφm : Measurable φ := symCut_measurable a hg'm.abs
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => by
    simp only [hφ, symCut]; split_ifs
    · positivity
    · exact le_rfl
  have hgs : IsGroundState0 a φ := by
    refine ⟨⟨symCut_even a _, symCut_supp a _, MemLp.ae_eq hφφ₀.symm hp₀.memL2, ?_⟩, ?_, ?_⟩
    · rw [archIntegrand_congr_ae hφφ₀]; exact hp₀.arch
    · rw [normSq_congr_ae hφφ₀]; exact hgs₀.2.1
    · intro h hph hnh; rw [weilQ0_congr_ae hφφ₀]; exact hgs₀.2.2 h hph hnh
  refine ⟨φ, hgs, hφ0, groundState0_pos_of_nonneg ha hgs hφm hφ0, fun g hg => ?_⟩
  rcases huniq g hg with h | h
  · left; exact h.trans hφφ₀.symm
  · right
    filter_upwards [h, hφφ₀] with t h1 h2
    rw [h1, h2]
end Pilot1ca

#print axioms Pilot1ca.weilQ0_add_smul
#print axioms Pilot1ca.quad_zero
#print axioms Pilot1ca.euler_lagrange0
#print axioms Pilot1ca.xcorr_sub_eq
#print axioms Pilot1ca.etaF_probe
#print axioms Pilot1ca.archX_eta_ge
#print axioms Pilot1ca.pair_le
#print axioms Pilot1ca.gapH_tendsto
#print axioms Pilot1ca.integral_gapH
#print axioms Pilot1ca.gapInf_zero
#print axioms Pilot1ca.groundState0_pos_of_nonneg
#print axioms Pilot1ca.exists_positive_groundState0
