import Mathlib
import SmallPositivity2

/-! # Weil positivity in the odd sector: `Q(g) ≥ 1/20` for every odd probe, `0 < a ≤ 1/4` (round 122, part 3)

The pilot's `weilQ` is Theorem 1bn(i)'s form for **even** `g`. For a general real `g` supported in
`[−a, a]`, Weil's functional of `F = g ⋆ g̃` has pole term `F̂(i/2) + F̂(−i/2) = 2 ĝ(i/2) ĝ(−i/2)`, where
`ĝ(±i/2) = ∫ g e^{∓u/2}`. The rest (the constant, the archimedean integral of `F(0) − F(u)` and the prime
sum of `F(log n)`) is unchanged, since `F = autocorr g`. So

`weilQg a g = 2 poleR·poleL + c₀‖g‖² + E_arch − 2S`, with `poleL = ∫ g e^{u/2}`,

and `weilQg = weilQ` for even `g` (`weilQg_even`). For **odd** `g`, `poleL = −poleR`, so the pole term is
`−2 poleR² ≤ 0`: it hurts. It is small, though, because `poleR = −∫ g sinh(u/2)` and
`poleR² ≤ ∫_{−a}^{a} sinh²(u/2) = sinh a − a`.

**Result.** `weilQodd_ge`: for `0 < a ≤ 1/4` (no prime, since `2a < log 2`), every normalised odd probe has
`Q(g) ≥ 1/20`. The proof has these pieces:
* the circle-mode machinery of round 20, replayed for a parity-free probe `OProbe`;
* odd mode masses `p_n = (∫ g sin(πnt/4a))²/(8a)`, so `p₀ = 0`, with caps
  `p_n ≤ (1 − 2 sin(πn/2)/(πn))/8` for `n = 1..4`;
* the tail level `ψ₅ ≥ Cin(5π/2) + 0.87267a − err`;
* `Near ≥ 2.016 + 0.99a − err(a)`.

The budget is split at `a = 1/8`:
* on `(0, 1/8]`: `−5.4301 + 4.218 + 2.013 − 0.001 ≈ 0.80`;
* on `[1/8, 1/4]`: `−5.4301 + 3.3976 + 2.1245 − 0.0053 ≈ 0.087`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-- `ĝ(−i/2) = ∫_{−a}^{a} g(u) e^{u/2} du`. -/
def poleL (g : ℝ → ℝ) (a : ℝ) : ℝ := ∫ u in (-a)..a, g u * Real.exp (u / 2)

/-- **Weil's form for a general real `g`**: pole term `2 ĝ(i/2) ĝ(−i/2)`. -/
def weilQg (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  2 * poleR g a * poleL g a + weilConst * normSq g + archE g - 2 * primeS g

/-- A probe of either parity: supported in `[−a, a]`, in `L²`, with convergent archimedean integral. -/
structure OProbe (a : ℝ) (g : ℝ → ℝ) : Prop where
  odd : ∀ u, g (-u) = -g u
  supp : ∀ u, a < |u| → g u = 0
  memL2 : MemLp g 2 volume
  arch : IntegrableOn (archIntegrand g) (Set.Ioi 0)

/-- For even probes the general form is the pilot's `weilQ`. -/
theorem weilQg_even {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g) : weilQg a g = weilQ a g := by
  have h : poleL g a = poleR g a := by
    unfold poleL poleR
    have hc := intervalIntegral.integral_comp_neg (a := -a) (b := a) (fun u => g u * Real.exp (-(u / 2)))
    simp only [neg_neg] at hc
    rw [← hc]; congr 1; funext u; rw [hp.even]; ring_nf
  rw [weilQg, weilQ_eq', h]; ring

/-! ## The mode machinery for an `OProbe` (round 20's proofs; only `supp`, `memL2`, `arch` are used) -/

theorem oprobe_integrable {a : ℝ} {g : ℝ → ℝ} (hg : OProbe a g) : Integrable g := by
  have hfin : IsFiniteMeasure (volume.restrict (Icc (-a) a)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have h1 : IntegrableOn g (Icc (-a) a) := (hg.memL2.restrict _).integrable (by norm_num)
  refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).1 h1
  rw [Function.mem_support] at hu
  have : |u| ≤ a := by
    by_contra h'; exact hu (hg.supp u (lt_of_not_ge h'))
  exact abs_le.1 this

theorem primeS_eq_zeroO {a : ℝ} (ha : 2 * a < Real.log 2) {g : ℝ → ℝ} (hg : OProbe a g) :
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

theorem archE_splitO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) :
    archE g = (∫ u in Ioc 0 (2 * a), archIntegrand g u) + ∫ u in Ioi (2 * a), kerK u := by
  unfold archE
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ 2 * a),
    setIntegral_union (Ioc_disjoint_Ioi (le_refl _)) measurableSet_Ioi
      (hp.arch.mono_set Ioc_subset_Ioi_self) (hp.arch.mono_set (Ioi_subset_Ioi (by linarith)))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  unfold archIntegrand kerK
  rw [autocorr_zero, hn, autocorr_eq_zero hp.supp (by rw [abs_of_pos (by linarith [mem_Ioi.mp hu])]; exact hu)]
  ring

theorem hasSum_pmO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) :
    HasSum (pm a g) (normSq g) := by
  have h := (hasSum_cf_sq (a := 2 * a) (r := a) (by linarith) (by linarith) hp.memL2 hp.supp).mul_left
    (8 * a)
  have e : 8 * a * ((4 * (2 * a))⁻¹ * normSq g) = normSq g := by field_simp; ring
  rw [e] at h; exact h

theorem hasSum_one_sub_autocorrO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g)
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

theorem sum_modeE_leO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1)
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
    (hasSum_one_sub_autocorrO ha hp hn hu.1.le hu.2)
  have e2 : archIntegrand g u = (1 - autocorr g u) * kerK u := by
    unfold archIntegrand kerK; rw [autocorr_zero, hn]
  rw [e2]
  calc ∑ n ∈ S, pm a g n * ((1 - Real.cos (π * n * u / (4 * a))) * kerK u)
      = (∑ n ∈ S, pm a g n * (1 - Real.cos (π * n * u / (4 * a)))) * kerK u := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hK0

theorem energy_ge_truncO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1)
    (S₀ : Finset ℤ) {τ : ℝ} (hτ : ∀ n, n ∉ S₀ → τ ≤ modeE a n) :
    τ + ∑ n ∈ S₀, (modeE a n - τ) * pm a g n ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  have hP := hasSum_pmO ha hp
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
  have hle := sum_modeE_leO ha hp hn S
  rw [← hsplit, mul_add] at *
  rw [← hsplit2] at hle
  linarith

theorem cs_suppO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) {h : ℝ → ℝ} (hh : Continuous h) :
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

theorem integral_suppO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (h : ℝ → ℝ) :
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

/-- An odd function against an even continuous bounded weight integrates to zero. -/
theorem integral_odd_even {g : ℝ → ℝ} (hodd : ∀ u, g (-u) = -g u) {h : ℝ → ℝ} (heven : ∀ u, h (-u) = h u) :
    (∫ t, g t * h t) = 0 := by
  have hI := integral_neg_eq_self (fun t => g t * h t) volume
  have e : (fun t => g (-t) * h (-t)) = fun t => -(g t * h t) := by
    funext t; rw [hodd, heven]; ring
  rw [e, integral_neg] at hI; linarith

/-- For odd `g`, the circle coefficient is `c_n = −i Y_n/(8a)` with `Y_n = ∫ g sin(πnt/4a)`, so
`p_n = Y_n²/(8a)`. -/
theorem pm_odd {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (n : ℤ) :
    pm a g n = (∫ t, g t * Real.sin (π * n * t / (4 * a))) ^ 2 / (8 * a) := by
  have hcf : cf (2 * a) g n = -I * (((1 / (8 * a)) * ∫ t, g t * Real.sin (π * n * t / (4 * a)) : ℝ) : ℂ) := by
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
    have hI := oprobe_integrable hp
    have ic : Integrable (fun t => g t * Real.cos (π * n * t / (4 * a))) :=
      hI.mul_bdd (c := 1)
        (show Continuous (fun t : ℝ => Real.cos (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    have is : Integrable (fun t => g t * Real.sin (π * n * t / (4 * a))) :=
      hI.mul_bdd (c := 1)
        (show Continuous (fun t : ℝ => Real.sin (π * n * t / (4 * a))) by fun_prop).aestronglyMeasurable
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    have hcos : (∫ t, g t * Real.cos (π * n * t / (4 * a))) = 0 :=
      integral_odd_even hp.odd (fun u => by rw [show π * n * -u / (4 * a) = -(π * n * u / (4 * a)) by ring,
        Real.cos_neg])
    have i1 : Integrable (fun x : ℝ => ((g x * Real.cos (π * n * x / (4 * a)) : ℝ) : ℂ)) := ic.ofReal
    have i2 : Integrable (fun x : ℝ => I * ((g x * Real.sin (π * n * x / (4 * a)) : ℝ) : ℂ)) :=
      is.ofReal.const_mul I
    rw [integral_sub i1 i2, integral_const_mul, integral_complex_ofReal,
      integral_complex_ofReal, hcos]
    push_cast; ring
  unfold pm
  rw [hcf, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp

theorem pm_negO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (n : ℤ) :
    pm a g (-n) = pm a g n := by
  rw [pm_odd ha hp, pm_odd ha hp]
  have e : (fun t => g t * Real.sin (π * ((-n : ℤ) : ℝ) * t / (4 * a)))
      = fun t => -(g t * Real.sin (π * n * t / (4 * a))) := by
    funext t; push_cast
    rw [show π * -(n : ℝ) * t / (4 * a) = -(π * n * t / (4 * a)) by ring, Real.sin_neg]; ring
  rw [e, integral_neg, neg_sq]

theorem pm_zeroO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) : pm a g 0 = 0 := by
  rw [pm_odd ha hp]; simp

/-- Cauchy–Schwarz cap for odd probes: `p_k ≤ (1 − 2 sin(πk/2)/(πk))/8`. -/
theorem pm_capO {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) {k : ℤ} (hk : 0 < k) :
    pm a g k ≤ (1 - 2 * Real.sin (π * k / 2) / (π * k)) / 8 := by
  rw [pm_odd ha hp]
  have hcs := cs_suppO ha hp (h := fun t => Real.sin (π * k * t / (4 * a))) (by fun_prop)
  rw [hn, one_mul] at hcs
  have e := integral_cos_sub_sq ha hk 0
  simp only [sub_zero, mul_zero, zero_mul, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero] at e
  have hsin : (∫ t in (-a)..a, Real.sin (π * k * t / (4 * a)) ^ 2)
      = 2 * a - ∫ t in (-a)..a, Real.cos (π * k * t / (4 * a)) ^ 2 := by
    have : (fun t => Real.sin (π * k * t / (4 * a)) ^ 2) = fun t => 1 - Real.cos (π * k * t / (4 * a)) ^ 2 := by
      funext t; rw [Real.sin_sq]
    rw [this, intervalIntegral.integral_sub (by simp)
      ((by fun_prop : Continuous fun t => Real.cos (π * k * t / (4 * a)) ^ 2).intervalIntegrable _ _)]
    simp; ring
  rw [hsin, e] at hcs
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ## The odd near field -/

def lowS4 : Finset ℤ := {-4, -3, -2, -1, 0, 1, 2, 3, 4}

theorem not_mem_lowS4 {n : ℤ} (hn : n ∉ lowS4) : 5 ≤ n ∨ n ≤ -5 := by
  simp only [lowS4, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  omega

theorem sum_lowS4_even {f : ℤ → ℝ} (hf : ∀ k, f (-k) = f k) :
    ∑ n ∈ lowS4, f n = f 0 + 2 * (f 1 + f 2 + f 3 + f 4) := by
  simp only [lowS4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (-4 : ℤ) = -(4 : ℤ) from rfl, show (-3 : ℤ) = -(3 : ℤ) from rfl,
    show (-2 : ℤ) = -(2 : ℤ) from rfl, show (-1 : ℤ) = -(1 : ℤ) from rfl, hf, hf, hf, hf]
  ring

/-- The tail level `τ₅ = 2.4848 + 0.87267a − err(a)` bounds every mode `|n| ≥ 5`. -/
theorem tail5_ok {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℤ} (hn : 5 ≤ n) :
    2.4848 + 0.87267 * a - errK a ≤ modeE a n := by
  have hnr : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hC : Cin (π * 5 / 2) ≤ Cin (π * n / 2) := Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  have hc := cin_val5
  have hπ := Real.pi_pos
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by positivity)
  have h2 : 2 / (π * n) ≤ 2 / (π * 5) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have h3 : 2 / (π * 5) = (1 / π) * (2 / 5) := by field_simp
  obtain ⟨-, b2, -⟩ := num_atoms
  have hD : 0.87267 ≤ 1 - 2 * Real.sin (π * n / 2) / (π * n) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hD ha.le]

theorem tail5_all {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℤ) (hn : n ∉ lowS4) :
    2.4848 + 0.87267 * a - errK a ≤ modeE a n := by
  rcases not_mem_lowS4 hn with h | h
  · exact tail5_ok ha ha1 h
  · have e := modeE_neg a (-n)
    rw [neg_neg] at e
    rw [e]; exact tail5_ok ha ha1 (by omega)

theorem capO1 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) : pm a g 1 ≤ 0.04543 := by
  have h := pm_capO ha hp hn (k := 1) (by norm_num)
  push_cast at h
  rw [show π * (1 : ℝ) / 2 = π / 2 by ring, Real.sin_pi_div_two] at h
  obtain ⟨b1, -⟩ := num_atoms
  have e : 2 * 1 / (π * 1) = 2 * (1 / π) := by field_simp
  rw [e] at h; linarith

theorem capO2 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) : pm a g 2 ≤ 1 / 8 := by
  have h := pm_capO ha hp hn (k := 2) (by norm_num)
  push_cast at h
  rw [show π * (2 : ℝ) / 2 = π by ring, Real.sin_pi] at h
  simpa using h

theorem capO3 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) : pm a g 3 ≤ 0.15153 := by
  have h := pm_capO ha hp hn (k := 3) (by norm_num)
  push_cast at h
  rw [show π * (3 : ℝ) / 2 = 6 * π / 4 by ring, (sc6).1] at h
  obtain ⟨-, b2, -⟩ := num_atoms
  have e : 2 * (-1) / (π * 3) = -(2 / 3) * (1 / π) := by field_simp
  rw [e] at h; linarith

theorem capO4 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) : pm a g 4 ≤ 1 / 8 := by
  have h := pm_capO ha hp hn (k := 4) (by norm_num)
  push_cast at h
  rw [show π * (4 : ℝ) / 2 = 2 * π by ring, Real.sin_two_pi] at h
  simpa using h

/-- **The odd near field**: `Near ≥ 2.016 + 0.99a − err(a)` for `0 < a ≤ 1/4`. -/
theorem nearField_odd {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) {g : ℝ → ℝ} (hp : OProbe a g)
    (hn : normSq g = 1) : 2.016 + 0.99 * a - errK a ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
  set τ := 2.4848 + 0.87267 * a - errK a with hτ
  have hE := energy_ge_truncO ha hp hn lowS4 (τ := τ) (tail5_all ha (by linarith))
  have hsum : ∑ n ∈ lowS4, (modeE a n - τ) * pm a g n
      = (modeE a 0 - τ) * pm a g 0
        + 2 * ((modeE a 1 - τ) * pm a g 1 + (modeE a 2 - τ) * pm a g 2
          + (modeE a 3 - τ) * pm a g 3 + (modeE a 4 - τ) * pm a g 4) :=
    sum_lowS4_even fun k => by simp only [modeE_neg, pm_negO ha hp]
  rw [hsum, pm_zeroO ha hp, mul_zero, zero_add] at hE
  have t1 := term_mode ha (by linarith) (g := g) (k := 1) (by norm_num) (Cv := 0.5408) (D := 0.36338) (X := 0)
    (Y := 0) (τ := τ) (P := 0.04543) (by simpa using cin_val1) dlo1 le_rfl
    (by rw [hτ]; nlinarith) (capO1 ha hp hn)
  have t2 := term_mode ha (by linarith) (g := g) (k := 2) (by norm_num) (Cv := 1.6214) (D := 1) (X := 0)
    (Y := 0) (τ := τ) (P := 1 / 8) (by simpa using cin_val2) dlo2 le_rfl
    (by rw [hτ]; nlinarith) (capO2 ha hp hn)
  have t3 := term_mode ha (by linarith) (g := g) (k := 3) (by norm_num) (Cv := 2.2965) (D := 1.212206) (X := 0)
    (Y := 0) (τ := τ) (P := 0.15153) (by simpa using cin_val3) dlo3 le_rfl
    (by rw [hτ]; nlinarith) (capO3 ha hp hn)
  have t4 := term_mode ha (by linarith) (g := g) (k := 4) (by norm_num) (Cv := 2.4081) (D := 1) (X := 0)
    (Y := 0) (τ := τ) (P := 1 / 8) (by simpa using cin_val4) dlo4 le_rfl
    (by rw [hτ]; nlinarith) (capO4 ha hp hn)
  simp only [sub_zero] at t1 t2 t3 t4
  rw [hτ] at t1 t2 t3 t4 hE
  have herr0 : 0 ≤ errK a := errK_nonneg ha.le
  nlinarith

/-! ## The odd pole term -/

theorem poleL_odd {a : ℝ} {g : ℝ → ℝ} (hp : OProbe a g) : poleL g a = -poleR g a := by
  unfold poleL poleR
  have hc := intervalIntegral.integral_comp_neg (a := -a) (b := a) (fun u => g u * Real.exp (-(u / 2)))
  simp only [neg_neg] at hc
  rw [← hc, ← intervalIntegral.integral_neg]; congr 1; funext u; rw [hp.odd]; ring_nf

theorem integral_sinh_sq_half {a : ℝ} :
    (∫ t in (-a)..a, Real.sinh (t / 2) ^ 2) = Real.sinh a - a := by
  have hd : ∀ t ∈ Set.uIcc (-a) a, HasDerivAt (fun t => (Real.sinh t - t) / 2) (Real.sinh (t / 2) ^ 2) t := by
    intro t _
    have := ((Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)).div_const 2
    convert this using 1
    · rfl
    have h1 : Real.cosh t = Real.cosh (2 * (t / 2)) := by ring_nf
    rw [h1, Real.cosh_two_mul, Real.cosh_sq]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t => Real.sinh (t / 2) ^ 2).intervalIntegrable _ _), Real.sinh_neg]
  ring

/-- The odd pole term is small: `poleR² ≤ sinh a − a` for a normalised odd probe. -/
theorem poleR_sq_odd {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : OProbe a g) (hn : normSq g = 1) :
    poleR g a ^ 2 ≤ Real.sinh a - a := by
  have hI := oprobe_integrable hp
  have hgi : IntervalIntegrable g volume (-a) a := hI.intervalIntegrable
  have ic : IntervalIntegrable (fun t => g t * Real.cosh (t / 2)) volume (-a) a :=
    hgi.mul_continuousOn (by fun_prop)
  have is : IntervalIntegrable (fun t => g t * Real.sinh (t / 2)) volume (-a) a :=
    hgi.mul_continuousOn (by fun_prop)
  have hcosh0 : (∫ t in (-a)..a, g t * Real.cosh (t / 2)) = 0 := by
    have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) (fun t => g t * Real.cosh (t / 2))
    simp only [neg_neg] at h
    have e : (fun t => g (-t) * Real.cosh (-t / 2)) = fun t => -(g t * Real.cosh (t / 2)) := by
      funext t; rw [hp.odd, show -t / 2 = -(t / 2) by ring, Real.cosh_neg]; ring
    rw [e, intervalIntegral.integral_neg] at h
    linarith
  have hsplit : poleR g a = -∫ t in (-a)..a, g t * Real.sinh (t / 2) := by
    unfold poleR
    have e : (fun u => g u * Real.exp (-(u / 2)))
        = fun u => g u * Real.cosh (u / 2) - g u * Real.sinh (u / 2) := by
      funext u; rw [← Real.cosh_sub_sinh]; ring
    rw [e, intervalIntegral.integral_sub ic is, hcosh0]; ring
  have hcs := cs_suppO ha hp (h := fun t => Real.sinh (t / 2)) (by fun_prop)
  rw [hn, one_mul, integral_sinh_sq_half, integral_suppO ha hp] at hcs
  rw [hsplit, neg_sq]; exact hcs

/-! ## Positivity -/

/-- **Weil positivity in the odd sector**: for `0 < a ≤ 1/4`, every normalised odd probe has
`Q(g) ≥ 1/20` (with the correct pole term `2ĝ(i/2)ĝ(−i/2) = −2 poleR²`). -/
theorem weilQodd_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) {g : ℝ → ℝ} (hp : OProbe a g)
    (hn : normSq g = 1) : (1 / 20 : ℝ) ≤ weilQg a g := by
  have hlog : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  rw [weilQg, poleL_odd hp, primeS_eq_zeroO hlog hp, hn, archE_splitO ha hp hn, farField_eq ha]
  have hC := weilConst_ge'
  have hN := nearField_odd ha ha1 hp hn
  have hP := poleR_sq_odd ha hp hn
  -- far field pieces
  have hE : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hratio : 2 / a ≤ (Real.exp a + 1) / (Real.exp a - 1) := by
    rw [div_le_div_iff₀ ha (by linarith)]
    nlinarith [two_exp_sub_le ha.le]
  have hneg : -Real.log ((Real.exp a - 1) / (Real.exp a + 1)) = Real.log ((Real.exp a + 1) / (Real.exp a - 1)) := by
    rw [← Real.log_inv, inv_div]
  have hlogr : Real.log (2 / a) ≤ Real.log ((Real.exp a + 1) / (Real.exp a - 1)) :=
    Real.log_le_log (by positivity) hratio
  have hat : Real.arctan (Real.sinh a) ≤ Real.sinh a := Real.arctan_le_self (Real.sinh_nonneg_iff.mpr ha.le)
  have hsh : Real.sinh a ≤ a + a ^ 3 / 6 + a ^ 5 / 100 := sinh_le_taylor ha.le (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hπ := Real.pi_gt_d6
  rw [hneg]
  norm_num at hl2 hπ
  rcases le_or_gt a (1 / 8) with hs | hs
  · -- (0, 1/8]: far ≥ log 16 + π/2 − sinh(1/8)
    have h16 : Real.log 16 ≤ Real.log (2 / a) := Real.log_le_log (by norm_num) (by
      rw [le_div_iff₀ ha]; linarith)
    have hl16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have h3 : a ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ ha.le hs 3
    have h5 : a ^ 5 ≤ (1 / 8) ^ 5 := pow_le_pow_left₀ ha.le hs 5
    have herr : errK a ≤ 0.0034 := by
      unfold errK
      have h2 : a ^ 2 ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ ha.le hs 2
      have h4 : a ^ 4 ≤ (1 / 8) ^ 4 := pow_le_pow_left₀ ha.le hs 4
      norm_num at h2 h3 h4 h5 ⊢; linarith
    norm_num at h3 h5
    nlinarith
  · -- [1/8, 1/4]: far ≥ log 8 + π/2 − sinh(1/4)
    have h8 : Real.log 8 ≤ Real.log (2 / a) := Real.log_le_log (by norm_num) (by
      rw [le_div_iff₀ ha]; linarith)
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h3 : a ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ ha.le ha1 3
    have h5 : a ^ 5 ≤ (1 / 4) ^ 5 := pow_le_pow_left₀ ha.le ha1 5
    have herr : errK a ≤ 0.0157 := by
      unfold errK
      have h2 : a ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ ha.le ha1 2
      have h4 : a ^ 4 ≤ (1 / 4) ^ 4 := pow_le_pow_left₀ ha.le ha1 4
      norm_num at h2 h3 h4 h5 ⊢; linarith
    norm_num at h3 h5
    nlinarith

end Pilot1ca

#print axioms Pilot1ca.weilQg_even
#print axioms Pilot1ca.pm_odd
#print axioms Pilot1ca.nearField_odd
#print axioms Pilot1ca.poleR_sq_odd
#print axioms Pilot1ca.weilQodd_ge
