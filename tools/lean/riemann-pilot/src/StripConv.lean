import Mathlib
import GapBound

/-! # (a) on the critical strip, and an `L²` route to it

**The strip suffices.** The RH chain uses (a) only through Hurwitz's theorem at the zeros of `Ξ`,
which lie in the open strip `|Im z| < ½`. So convergence of `ĝ_n/ĝ_n(0)` to `Ξ/Ξ(0)` locally
uniformly on that strip alone gives RH for the top-of-chain ground states
(`hurwitz_closed_on`, `rh_of_strip_cross`, `rh_of_hypConvStrip_top`).

**An `L²` criterion.** `|ĝ(z) − φ̂(z)| ≤ √(2a) e^{a|Im z|} ‖g − φ‖` (`norm_ghatC_sub_le`). So if
comparison functions `φ_n` have transforms converging to `cΞ` on the strip (`KernelApprox`; for
Riemann's kernel `Φ·1_{[−a,a]}` this is Riemann's formula `Ξ(t) = 2∫₀^∞ Φ(u) cos(ut) du`, which is not
formalised), then

  `‖σ_n·topGS(a_n) − φ_n‖ = o(e^{−b a_n}/√a_n)` for every `b < ½`   ⇒   RH   (`rh_of_close_top`).

The threshold `½` is the half-width of the critical strip.

**From a spectral gap.** Min–max gives `‖g − φ‖² ≤ 2(Q(φ) − λ₁)/(λ₂ − λ₁)` for a normalised
probe `φ` with `⟨g, φ⟩ ≥ 0` (`normSq_sub_le_of_gap`), hence `rh_of_relgap`. For `φ = Φ_a` its
hypothesis is false numerically (`frontier/strip/`): `λ₂` is itself double-exponentially small,
far below `Q(Φ_a)`.

**The moment conditions.** (a) on the strip makes every Taylor coefficient of `ĝ_n/ĝ_n(0)` at `0`
converge (`moments_of_hypConvStrip`); `k = 2` is the second-moment condition `κ(a) → 0`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

open Pilot1bt

/-! ## Hurwitz on an open set, and RH from convergence on the strip -/

/-- **Hurwitz for a closed set, on an open set `U`.** -/
theorem hurwitz_closed_on {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ n, Differentiable ℂ (F n)) (hf : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hnz : ∃ w, f w ≠ 0) {S : Set ℂ} (hS : IsClosed S) (hzeros : ∀ n z, F n z = 0 → z ∈ S) :
    ∀ z₀ ∈ U, f z₀ = 0 → z₀ ∈ S := by
  intro z₀ hU0 hz₀
  by_contra hS0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hS.isOpen_compl.inter hU) z₀ ⟨hS0, hU0⟩
  have hiso : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
    rcases (hf.analyticAt z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hnz
      have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z₀) (h.mono fun z hz => by simp [hz])
      exact hw (by simpa using hall (Set.mem_univ w))
    · exact h
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hiso)
  set r := min (ε / 2) (ρ / 2) with hr_def
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hne : (Metric.sphere z₀ r).Nonempty := ⟨z₀ + r, by simp [abs_of_pos hr]⟩
  obtain ⟨w, hwS, hwmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn hne
    (hf.continuous.norm.continuousOn)
  have hfS : ∀ z ∈ Metric.sphere z₀ r, f z ≠ 0 := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    apply hεf (by rw [dist_eq_norm, hz]; exact hrε)
    intro h; rw [h, sub_self, norm_zero] at hz; exact hr.ne hz
  set m := ‖f w‖ with hm_def
  have hm : 0 < m := norm_pos_iff.2 (hfS w hwS)
  have hsub : Metric.closedBall z₀ r ⊆ U := fun z hz =>
    (hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hrρ)).2
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hsub
    (isCompact_closedBall z₀ r)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif (m / 2) (by linarith)).exists
  have hnoz : ∀ z ∈ Metric.closedBall z₀ r, F n z ≠ 0 := by
    intro z hz h
    have hzS := hzeros n z h
    exact (hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) hrρ)).1 hzS
  have hbound : ∀ z ∈ frontier (Metric.ball z₀ r), ‖(F n z)⁻¹‖ ≤ (m / 2)⁻¹ := by
    intro z hz
    rw [frontier_ball z₀ hr.ne'] at hz
    have h1 := hn z (Metric.sphere_subset_closedBall hz)
    have h2 : m ≤ ‖f z‖ := hwmin hz
    rw [dist_eq_norm] at h1
    have h3 : m / 2 ≤ ‖F n z‖ := by
      have := norm_sub_norm_le (f z) (F n z)
      linarith
    rw [norm_inv]
    exact inv_anti₀ (by linarith) h3
  have hdiff : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (Metric.ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact ((hF n).differentiableOn).inv hnoz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff hbound
    (subset_closure (Metric.mem_ball_self hr))
  have hz0 := hn z₀ (Metric.mem_closedBall_self hr.le)
  rw [hz₀, dist_eq_norm, zero_sub, norm_neg] at hz0
  have hFz0 : F n z₀ ≠ 0 := hnoz z₀ (Metric.mem_closedBall_self hr.le)
  rw [norm_inv] at hmax
  have hpos : 0 < ‖F n z₀‖ := norm_pos_iff.2 hFz0
  have := (inv_le_inv₀ hpos (by linarith)).1 hmax
  linarith

/-- The open strip `|Im z| < ½`, which contains every zero of `Ξ`. -/
def stripSet : Set ℂ := {z | |z.im| < 1 / 2}

theorem isOpen_stripSet : IsOpen stripSet :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

theorem zero_mem_stripSet : (0 : ℂ) ∈ stripSet := by simp [stripSet]

/-- **(a) on the critical strip**: the normalised transforms converge to `Ξ/Ξ(0)` locally
uniformly on `|Im z| < ½` only. -/
def HypConvStrip (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) : Prop :=
  TendstoLocallyUniformlyOn (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
    (fun z => Xi z / Xi 0) atTop stripSet

theorem hypConvStrip_of_hypConv {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (h : HypConv a g) :
    HypConvStrip a g :=
  h.tendstoLocallyUniformlyOn

theorem ordinate_mem_strip {s : ℂ} (hs : IsNontrivialZero s) : (s - 1 / 2) / I ∈ stripSet := by
  have e : (s - 1 / 2) / I = -I * (s - 1 / 2) := by field_simp; rw [I_sq]; ring
  obtain ⟨h0, h1⟩ := hs.mem_strip
  show |((s - 1 / 2) / I).im| < 1 / 2
  rw [e]; simp
  rw [abs_lt]; constructor <;> linarith

/-- **The chain with zeros on the cross, from convergence on the strip.** -/
theorem rh_of_strip_cross {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hgs : ∀ n, IsGroundState (a n) (g n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0)
    (hconv : HypConvStrip a g) (hζ : ZetaNoZeroInUnitInterval) : RiemannHypothesis := by
  have hX0 := Xi_zero_ne_zero
  have h0 : ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 := by
    have hu := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_stripSet).1 hconv {0}
        (singleton_subset_iff.2 zero_mem_stripSet) isCompact_singleton) 1 one_pos
    filter_upwards [hu] with n hn h
    have := hn 0 rfl
    simp only [div_self hX0, h, div_zero, dist_zero_right, norm_one] at this
    exact lt_irrefl _ this
  obtain ⟨N, hN⟩ := (hcross.and h0).exists_forall_of_atTop
  have hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n) :=
    fun n => (probe_integrable (hgs n).1).intervalIntegrable
  have hconvN : TendstoLocallyUniformlyOn
      (fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      (fun z => Xi z / Xi 0) atTop stripSet := fun u hu x hx => by
    obtain ⟨t, ht, hev⟩ := hconv u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩
  have hXc : ∀ z ∈ stripSet, Xi z / Xi 0 = 0 → z ∈ crossSet :=
    hurwitz_closed_on (F := fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      isOpen_stripSet
      (fun m => (ghatC_differentiable (hint _)).div_const _)
      (differentiable_Xi.div_const _) hconvN
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩ isClosed_crossSet
      (fun m z h => (hN (m + N) (by omega)).1 z
        ((div_eq_zero_iff.1 h).resolve_right (hN (m + N) (by omega)).2))
  intro s hz htriv _
  have hs : IsNontrivialZero s := ⟨hz, htriv⟩
  have hc := hXc ((s - 1 / 2) / I) (ordinate_mem_strip hs)
    (by rw [Xi_at_ordinate, xi_eq_zero_of_nontrivial hs, zero_div])
  rcases hc with hre | him
  · exfalso
    rw [re_ordinate] at hre
    obtain ⟨h0', h1'⟩ := hs.mem_strip
    have hsr : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre])
    apply hζ s.re h0' h1'
    rw [← hsr]; exact hz
  · exact re_eq_half_of_Xi_real him

/-- **RH from (a) on the strip, for the top-of-chain ground states.** -/
theorem rh_of_hypConvStrip_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConvStrip a fun n => topGS (a n)) : RiemannHypothesis :=
  rh_of_strip_cross (fun n => topGS_isGroundState (ha n))
    (Eventually.of_forall fun n z hz => topGS_cross (ha n) z hz) hconv zetaNoZeroInUnitInterval

/-! ## The transform is `L²`-Lipschitz on strips -/

/-- `(∫_{−a}^{a} |h|)² ≤ 2a‖h‖²`. -/
theorem sq_intervalL1_le {a : ℝ} (ha : 0 < a) {h : ℝ → ℝ} (hh : MemLp h 2 volume) :
    (∫ u in (-a)..a, |h u|) ^ 2 ≤ 2 * a * normSq h := by
  have hle : -a ≤ a := by linarith
  have hi : IntervalIntegrable h volume (-a) a := memLp_intervalIntegrable hh (-a) a
  have hi2 : IntervalIntegrable (fun u => h u ^ 2) volume (-a) a :=
    hh.integrable_sq.intervalIntegrable
  set I1 := ∫ u in (-a)..a, |h u|
  set I2 := ∫ u in (-a)..a, h u ^ 2
  set m := I1 / (2 * a)
  have hvar : 0 ≤ ∫ u in (-a)..a, (|h u| - m) ^ 2 :=
    intervalIntegral.integral_nonneg hle fun _ _ => sq_nonneg _
  have hexp : (∫ u in (-a)..a, (|h u| - m) ^ 2) = I2 - 2 * m * I1 + m ^ 2 * (2 * a) := by
    have e : (fun u => (|h u| - m) ^ 2) = fun u => (h u ^ 2 - 2 * m * |h u|) + m ^ 2 := by
      funext u; rw [← sq_abs (h u)]; ring
    rw [e, intervalIntegral.integral_add (hi2.sub (hi.abs.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hi2 (hi.abs.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]; ring
  have hI2 : I2 ≤ normSq h := by
    unfold normSq
    simp only [I2]
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral hh.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
  rw [hexp] at hvar
  have hm : m ^ 2 * (2 * a) - 2 * m * I1 = -(I1 ^ 2 / (2 * a)) := by
    simp only [m]; field_simp; ring
  have : I1 ^ 2 / (2 * a) ≤ I2 := by linarith
  rw [div_le_iff₀ (by positivity)] at this
  nlinarith

/-- **`|ĝ(z) − φ̂(z)| ≤ √(2a) e^{a|Im z|} ‖g − φ‖`.** -/
theorem norm_ghatC_sub_le {a : ℝ} (ha : 0 < a) {g φ : ℝ → ℝ} (hg : MemLp g 2 volume)
    (hφ : MemLp φ 2 volume) (z : ℂ) :
    ‖ghatC g a z - ghatC φ a z‖
      ≤ Real.sqrt (2 * a) * Real.exp (a * |z.im|) * Real.sqrt (normSq fun t => g t - φ t) := by
  have hle : -a ≤ a := by linarith
  have hd : MemLp (fun t => g t - φ t) 2 volume := hg.sub hφ
  have ii : ∀ {h : ℝ → ℝ}, MemLp h 2 volume →
      IntervalIntegrable (fun u => ((h u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)) volume (-a) a := by
    intro h hh
    have hr := memLp_intervalIntegrable hh (-a) a
    exact (show IntervalIntegrable (fun u => ((h u : ℝ) : ℂ)) volume (-a) a from
      ⟨hr.1.ofReal, hr.2.ofReal⟩).mul_continuousOn (by fun_prop)
  have e : ghatC g a z - ghatC φ a z
      = ∫ u in (-a)..a, (((g u - φ u : ℝ)) : ℂ) * Complex.exp (Complex.I * z * u) := by
    unfold ghatC
    rw [← intervalIntegral.integral_sub (ii hg) (ii hφ)]
    congr 1; funext u; push_cast; ring
  have hpt : ∀ u ∈ Set.Ioc (-a) a,
      ‖(((g u - φ u : ℝ)) : ℂ) * Complex.exp (Complex.I * z * u)‖
        ≤ Real.exp (a * |z.im|) * |g u - φ u| := by
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Real.exp_le_exp.2
    have e2 : (Complex.I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re]
    rw [e2]
    have hu' : |u| ≤ a := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
    calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ |z.im| * a := mul_le_mul_of_nonneg_left hu' (abs_nonneg _)
      _ = a * |z.im| := mul_comm _ _
  have hdi : IntervalIntegrable (fun u => g u - φ u) volume (-a) a :=
    memLp_intervalIntegrable hd (-a) a
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hle
    (Filter.Eventually.of_forall hpt) (hdi.abs.const_mul (Real.exp (a * |z.im|)))
  rw [intervalIntegral.integral_const_mul] at h1
  have hL1 : (∫ u in (-a)..a, |g u - φ u|)
      ≤ Real.sqrt (2 * a) * Real.sqrt (normSq fun t => g t - φ t) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le (sq_intervalL1_le ha hd)
  rw [e]
  calc _ ≤ Real.exp (a * |z.im|) * ∫ u in (-a)..a, |g u - φ u| := h1
    _ ≤ Real.exp (a * |z.im|) * (Real.sqrt (2 * a) * Real.sqrt (normSq fun t => g t - φ t)) :=
        mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = _ := by ring

/-! ## Strip convergence from `L²` closeness -/

/-- A compact subset of the open strip lies in a closed strip `|Im z| ≤ b` with `b < ½`. -/
theorem compact_in_strip {K : Set ℂ} (hK : IsCompact K) (hKs : K ⊆ stripSet) :
    ∃ b, 0 ≤ b ∧ b < 1 / 2 ∧ ∀ z ∈ K, |z.im| ≤ b := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨0, le_rfl, by norm_num, by simp [he]⟩
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn hne (continuous_abs.comp continuous_im).continuousOn
  exact ⟨|w.im|, abs_nonneg _, hKs hw, fun z hz => hmax hz⟩

/-- **Transforms converge on the strip when the functions do in `L²`, fast enough.** If the
comparison transforms `φ̂_n` converge to `F` locally uniformly on `|Im z| < ½`, and
`√(2a_n) e^{b a_n} ‖g_n − φ_n‖ → 0` for every `b < ½`, then `ĝ_n → F` there too. -/
theorem tendstoLocallyUniformlyOn_of_close {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {g φ : ℕ → ℝ → ℝ}
    (hg : ∀ n, MemLp (g n) 2 volume) (hφ : ∀ n, MemLp (φ n) 2 volume) {F : ℂ → ℂ}
    (hker : TendstoLocallyUniformlyOn (fun n z => ghatC (φ n) (a n) z) F atTop stripSet)
    (hclose : ∀ b < 1 / 2, Tendsto (fun n => Real.sqrt (2 * a n) * Real.exp (a n * b)
      * Real.sqrt (normSq fun t => g n t - φ n t)) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun n z => ghatC (g n) (a n) z) F atTop stripSet := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_stripSet] at hker ⊢
  intro K hKs hK
  obtain ⟨b, hb0, hb, hbK⟩ := compact_in_strip hK hKs
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h1 := Metric.tendstoUniformlyOn_iff.1 (hker K hKs hK) (ε / 2) (by linarith)
  have h2 := (hclose b hb).eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [h1, h2] with n hn1 hn2 z hz
  have hd := norm_ghatC_sub_le (ha n) (hg n) (hφ n) z
  have hexp : Real.exp (a n * |z.im|) ≤ Real.exp (a n * b) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hbK z hz) (ha n).le)
  have hd' : ‖ghatC (g n) (a n) z - ghatC (φ n) (a n) z‖ < ε / 2 := by
    refine lt_of_le_of_lt (hd.trans ?_) hn2
    gcongr
  have := hn1 z hz
  rw [dist_eq_norm] at this ⊢
  calc ‖F z - ghatC (g n) (a n) z‖
      = ‖(F z - ghatC (φ n) (a n) z) - (ghatC (g n) (a n) z - ghatC (φ n) (a n) z)‖ := by
        congr 1; ring
    _ ≤ ‖F z - ghatC (φ n) (a n) z‖ + ‖ghatC (g n) (a n) z - ghatC (φ n) (a n) z‖ :=
        norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add this hd'
    _ = ε := by ring

/-- Normalising at `0`: if `G_n → F` locally uniformly on the strip with `F` continuous and
`F(0) ≠ 0`, then `G_n/G_n(0) → F/F(0)` there. -/
theorem tendstoLocallyUniformlyOn_ratio {G : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hF : Continuous F)
    (hF0 : F 0 ≠ 0) (hconv : TendstoLocallyUniformlyOn G F atTop stripSet) :
    TendstoLocallyUniformlyOn (fun n z => G n z / G n 0) (fun z => F z / F 0) atTop stripSet := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_stripSet] at hconv ⊢
  intro K hKs hK
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  set d := F 0
  have hd : 0 < ‖d‖ := norm_pos_iff.2 hF0
  have hB0 : ∀ z ∈ K, ‖F z‖ ≤ max B 0 := fun z hz => (hB z hz).trans (le_max_left _ _)
  set B' := max B 0
  have h0 := Metric.tendstoUniformlyOn_iff.1 (hconv {0} (singleton_subset_iff.2 zero_mem_stripSet)
    isCompact_singleton)
  have hK' := Metric.tendstoUniformlyOn_iff.1 (hconv K hKs hK)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- choose `η` with `2(η‖d‖ + B'η)/‖d‖² < ε` and `η ≤ ‖d‖/2`
  set η := min (‖d‖ / 2) (ε * ‖d‖ ^ 2 / (4 * (‖d‖ + B' + 1))) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  filter_upwards [h0 η hη0, hK' η hη0] with n hn0 hnK z hz
  have e0 := hn0 0 rfl
  have eK := hnK z hz
  rw [dist_eq_norm] at e0 eK ⊢
  have hdn : ‖d‖ / 2 ≤ ‖G n 0‖ := by
    have := norm_sub_norm_le d (G n 0)
    have : η ≤ ‖d‖ / 2 := min_le_left _ _
    linarith
  have hGn0 : G n 0 ≠ 0 := norm_pos_iff.1 (by linarith)
  have key : F z / d - G n z / G n 0
      = ((F z - G n z) * d - F z * (d - G n 0)) / (d * G n 0) := by
    field_simp; ring
  rw [key, norm_div, norm_mul]
  have hnum : ‖(F z - G n z) * d - F z * (d - G n 0)‖ ≤ η * ‖d‖ + B' * η := by
    calc _ ≤ ‖(F z - G n z) * d‖ + ‖F z * (d - G n 0)‖ := norm_sub_le _ _
      _ = ‖F z - G n z‖ * ‖d‖ + ‖F z‖ * ‖d - G n 0‖ := by rw [norm_mul, norm_mul]
      _ ≤ η * ‖d‖ + B' * η :=
          add_le_add (mul_le_mul_of_nonneg_right eK.le (norm_nonneg _))
            (mul_le_mul (hB0 z hz) e0.le (norm_nonneg _) (le_max_right _ _))
  have hden : ‖d‖ * (‖d‖ / 2) ≤ ‖d‖ * ‖G n 0‖ := mul_le_mul_of_nonneg_left hdn hd.le
  rw [div_lt_iff₀ (by positivity)]
  have hηε : η ≤ ε * ‖d‖ ^ 2 / (4 * (‖d‖ + B' + 1)) := min_le_right _ _
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have : η * (‖d‖ + B') < ε * (‖d‖ * (‖d‖ / 2)) := by
    have h4 : 0 < 4 * (‖d‖ + B' + 1) := by positivity
    have := mul_le_mul_of_nonneg_right hηε (by positivity : (0 : ℝ) ≤ ‖d‖ + B')
    have e : ε * ‖d‖ ^ 2 / (4 * (‖d‖ + B' + 1)) * (‖d‖ + B') < ε * (‖d‖ * (‖d‖ / 2)) := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ h4]
      nlinarith [sq_nonneg ‖d‖, mul_pos hε (mul_pos hd hd)]
    linarith
  nlinarith

/-! ## The angle to a trial function, from a second-eigenvalue bound -/

theorem xcorr_add_smul_right {φ ψ χ : ℝ → ℝ} (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (hχ : MemLp χ 2 volume) (r : ℝ) :
    xcorr χ (fun t => φ t + r * ψ t) 0 = xcorr χ φ 0 + r * xcorr χ ψ 0 := by
  have i1 : Integrable (fun t => χ t * φ t) := by simpa using integrable_mul_shift₂ hχ hφ 0
  have i2 : Integrable (fun t => χ t * ψ t) := by simpa using integrable_mul_shift₂ hχ hψ 0
  rw [xcorr_zero_eq, xcorr_zero_eq, xcorr_zero_eq, ← integral_const_mul, ← integral_add i1 (i2.const_mul r)]
  congr 1; funext t; ring

/-- **The angle bound.** If `λ₂ ≥ s > λ₁` (in min–max form) and `φ` is a normalised probe with
`⟨g, φ⟩ ≥ 0` for a ground state `g`, then `‖g − φ‖² ≤ 2(Q(φ) − λ₁)/(s − λ₁)`. -/
theorem normSq_sub_le_of_gap {a s : ℝ} (ha : 0 < a) {g φ : ℝ → ℝ} (hg : IsGroundState a g)
    (hφ : Probe a φ) (hφ1 : normSq φ = 1) (hs : Lam2Ge a s) (hsl : lam a < s)
    (hc : 0 ≤ xcorr g φ 0) :
    normSq (fun t => g t - φ t) ≤ 2 * (weilQ a φ - lam a) / (s - lam a) := by
  have hgp : Probe a g := hg.1
  have hg1 : normSq g = 1 := hg.2.1
  have hq : weilQ a g = lam a * normSq g := ((isGroundState_iff ha).1 hg).1.2
  have hQg : weilQ a g - lam a * normSq g = 0 := by linarith
  -- `B(ψ, g) = 0` for every probe `ψ` (Euler–Lagrange)
  have hB : ∀ ψ, Probe a ψ →
      bil0 a ψ g + 2 * poleR ψ a * poleR g a - lam a * xcorr ψ g 0 = 0 := by
    intro ψ hψ
    have := euler_lagrange_Q ha hg hψ
    rw [bil0_comm, xcorr_comm]; linarith
  have hgg : xcorr g g 0 = 1 := by rw [← normSq_eq_xcorr hgp.memL2, hg1]
  set c := xcorr g φ 0 with hcdef
  set h : ℝ → ℝ := fun t => φ t + (-c) * g t with hhdef
  have hh : Probe a h := probe_add_smul hφ hgp (-c)
  -- `Q_λ(φ) = Q_λ(h)`
  have eφ : φ = fun t => h t + c * g t := by funext t; simp only [hhdef]; ring
  have hQφ : weilQ a φ - lam a * normSq φ = weilQ a h - lam a * normSq h := by
    have e := Qlam_add_smul hh hgp c
    rw [← eφ, hB h hh, hQg] at e
    linarith
  -- `⟨g, h⟩ = 0` and `‖h‖² = 1 − c²`
  have hgh : xcorr g h 0 = 0 := by
    rw [xcorr_add_smul_right hφ.memL2 hgp.memL2 hgp.memL2, hgg]; ring
  have hNh : normSq h = 1 - c ^ 2 := by
    rw [normSq_add_smul hφ.memL2 hgp.memL2, hφ1, hg1, xcorr_comm]; ring
  -- `Q_λ(h) ≥ (s − λ)‖h‖²`
  have hkey : (s - lam a) * normSq h ≤ weilQ a h - lam a * normSq h := by
    rcases (normSq_nonneg h).lt_or_eq with hpos | h0
    · set N := normSq h
      set k := 1 / Real.sqrt N
      have hk : k ^ 2 * N = 1 := by
        simp only [k]; rw [div_pow, Real.sq_sqrt hpos.le]; field_simp
      set hh' : ℝ → ℝ := fun t => k * h t
      have php : Probe a hh' := probe_smul hh k
      have hn1 : normSq hh' = 1 := by simp only [hh']; rw [normSq_smul, hk]
      have hx : xcorr g hh' 0 = 0 := by
        have e := xcorr_add_smul_right (φ := fun _ => (0 : ℝ)) (probe_zero a).memL2 hh.memL2
          hgp.memL2 k
        simp only [zero_add] at e
        rw [e, hgh]
        simp [xcorr]
      obtain ⟨α, β, hαβ, hsQ⟩ := hs g hh' hgp php hg1 hn1 hx
      -- `Q(αg + βĥ) = λ + β² Q_λ(ĥ)`
      have e1 := Qlam_add_smul (probe_smul php β) hgp α
      have hBβ := hB _ (probe_smul php β)
      have hfun : (fun t => β * hh' t + α * g t) = fun t => α * g t + β * hh' t := by
        funext t; ring
      rw [hfun, hBβ, hQg, normSq_smul, weilQ_smul] at e1
      have hn : normSq (fun t => α * g t + β * hh' t) = 1 := by
        have e2 := normSq_add_smul (φ := fun t => α * g t) (hgp.memL2.const_mul α) php.memL2 β
        have hx' : xcorr (fun t => α * g t) hh' 0 = 0 := by
          rw [xcorr_zero_eq]
          simp only [mul_assoc]
          rw [integral_const_mul, ← xcorr_zero_eq, hx, mul_zero]
        rw [e2, hx', normSq_smul, hg1, hn1]; linarith
      rw [hn] at e1
      have hQh' : 0 ≤ weilQ a hh' - lam a * normSq hh' := Qlam_nonneg php
      have hβ : β ^ 2 ≤ 1 := by nlinarith [sq_nonneg α]
      have hlow : s - lam a ≤ weilQ a hh' - lam a * normSq hh' := by
        have : s - lam a ≤ β ^ 2 * (weilQ a hh' - lam a * normSq hh') := by nlinarith
        nlinarith
      -- scale back: `Q_λ(ĥ) = Q_λ(h)/N`
      have hsc : weilQ a hh' - lam a * normSq hh' = k ^ 2 * (weilQ a h - lam a * normSq h) := by
        simp only [hh']; rw [weilQ_smul, normSq_smul]; ring
      rw [hsc] at hlow
      have := mul_le_mul_of_nonneg_right hlow hpos.le
      calc (s - lam a) * N ≤ k ^ 2 * (weilQ a h - lam a * N) * N := this
        _ = (weilQ a h - lam a * N) * (k ^ 2 * N) := by ring
        _ = weilQ a h - lam a * N := by rw [hk, mul_one]
    · have := Qlam_nonneg hh; rw [← h0] at this ⊢; linarith
  -- assemble
  have hsl' : 0 < s - lam a := by linarith
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [normSq_nonneg h]
  have hc1 : c ≤ 1 := by nlinarith
  have hsub : normSq (fun t => g t - φ t) = 2 - 2 * c := by
    have e := normSq_add_smul hgp.memL2 hφ.memL2 (-1)
    have hf : (fun t => g t + (-1) * φ t) = fun t => g t - φ t := by funext t; ring
    rw [hf, hg1, hφ1] at e
    rw [e]; ring
  rw [hsub, le_div_iff₀ hsl']
  rw [hφ1, mul_one] at hQφ
  rw [hNh] at hkey hQφ
  nlinarith [mul_nonneg (mul_nonneg hc (sub_nonneg.2 hc1)) hsl'.le]

/-! ## RH from `L²` closeness to a kernel, and from a relative spectral gap -/

/-- **The kernel hypothesis.** Comparison functions `φ_n ∈ L²` whose transforms on `[−a_n, a_n]`
converge to a nonzero multiple of `Ξ`, locally uniformly on the strip `|Im z| < ½`. Riemann's
formula `Ξ(t) = 2∫₀^∞ Φ(u) cos(ut) du` (Titchmarsh §2.16) gives this for the truncations
`Φ·1_{[−a_n, a_n]}` whenever `a_n → ∞`, since `Φ` decays like `exp(−πe^{2|u|})`. That classical
identity is not formalised here. -/
def KernelApprox (a : ℕ → ℝ) (φ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, MemLp (φ n) 2 volume) ∧ ∃ c : ℂ, c ≠ 0 ∧
    TendstoLocallyUniformlyOn (fun n z => ghatC (φ n) (a n) z) (fun z => c * Xi z) atTop stripSet

/-- **(a) on the strip from `L²` closeness.** -/
theorem hypConvStrip_of_close {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {g φ : ℕ → ℝ → ℝ}
    (hg : ∀ n, MemLp (g n) 2 volume) (hk : KernelApprox a φ)
    (hclose : ∀ b < 1 / 2, Tendsto (fun n => Real.sqrt (2 * a n) * Real.exp (a n * b)
      * Real.sqrt (normSq fun t => g n t - φ n t)) atTop (𝓝 0)) :
    HypConvStrip a g := by
  obtain ⟨hφ, c, hc, hconv⟩ := hk
  have h1 := tendstoLocallyUniformlyOn_of_close ha hg hφ hconv hclose
  have h2 := tendstoLocallyUniformlyOn_ratio (F := fun z => c * Xi z)
    (continuous_const.mul differentiable_Xi.continuous) (mul_ne_zero hc Xi_zero_ne_zero) h1
  have e : (fun z => c * Xi z / (c * Xi 0)) = fun z => Xi z / Xi 0 :=
    funext fun z => mul_div_mul_left _ _ hc
  rw [e] at h2
  exact h2

/-- (a) on the strip is unchanged by nonzero real rescalings `g_n ↦ σ_n g_n`. -/
theorem hypConvStrip_of_smul {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {σ : ℕ → ℝ} (hσ : ∀ n, σ n ≠ 0)
    (h : HypConvStrip a fun n t => σ n * g n t) : HypConvStrip a g := by
  have e : (fun n z => ghatC (fun t => σ n * g n t) (a n) z / ghatC (fun t => σ n * g n t) (a n) 0)
      = fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0 := by
    funext n z
    rw [ghatC_smul, ghatC_smul]
    exact mul_div_mul_left _ _ (by exact_mod_cast hσ n)
  unfold HypConvStrip at h ⊢
  rw [e] at h
  exact h

/-- **RH from `L²` closeness of the top-of-chain ground states to a kernel.** If
`√(2a_n) e^{b a_n} ‖σ_n·topGS(a_n) − φ_n‖ → 0` for every `b < ½`, with signs `σ_n ≠ 0` and
`φ_n` as in `KernelApprox`, then the Riemann hypothesis holds. -/
theorem rh_of_close_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {φ : ℕ → ℝ → ℝ} (hk : KernelApprox a φ)
    {σ : ℕ → ℝ} (hσ : ∀ n, σ n ≠ 0)
    (hclose : ∀ b < 1 / 2, Tendsto (fun n => Real.sqrt (2 * a n) * Real.exp (a n * b)
      * Real.sqrt (normSq fun t => σ n * topGS (a n) t - φ n t)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  rh_of_hypConvStrip_top ha (hypConvStrip_of_smul hσ (hypConvStrip_of_close ha
    (fun n => ((topGS_isGroundState (ha n)).1.memL2).const_mul (σ n)) hk hclose))

/-- A sign flip of a ground state is a ground state. -/
theorem isGroundState_neg {a : ℝ} {g : ℝ → ℝ} (hg : IsGroundState a g) :
    IsGroundState a fun t => (-1) * g t := by
  refine ⟨probe_smul hg.1 (-1), ?_, fun h hh hn => ?_⟩
  · rw [normSq_smul, hg.2.1]; norm_num
  · rw [weilQ_smul]; have := hg.2.2 h hh hn; linarith

/-- **RH from a relative spectral gap.** Let `φ_n` be normalised probes as in `KernelApprox`, and
`λ₂(a_n) ≥ s_n > λ₁(a_n)` (min–max form). If
`a_n e^{2b a_n} (Q(φ_n) − λ₁)/(s_n − λ₁) → 0` for every `b < ½`, the Riemann hypothesis holds. -/
theorem rh_of_relgap {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {φ : ℕ → ℝ → ℝ} (hk : KernelApprox a φ)
    (hφp : ∀ n, Probe (a n) (φ n)) (hφ1 : ∀ n, normSq (φ n) = 1)
    {s : ℕ → ℝ} (hs : ∀ n, Lam2Ge (a n) (s n)) (hsl : ∀ n, lam (a n) < s n)
    (hrel : ∀ b < 1 / 2, Tendsto (fun n => a n * Real.exp (2 * b * a n)
      * ((weilQ (a n) (φ n) - lam (a n)) / (s n - lam (a n)))) atTop (𝓝 0)) :
    RiemannHypothesis := by
  set g : ℕ → ℝ → ℝ := fun n => topGS (a n)
  set σ : ℕ → ℝ := fun n => if 0 ≤ xcorr (g n) (φ n) 0 then 1 else -1
  have hσ : ∀ n, σ n ≠ 0 := fun n => by simp only [σ]; split_ifs <;> norm_num
  have hgs : ∀ n, IsGroundState (a n) fun t => σ n * g n t := by
    intro n
    simp only [σ]
    split_ifs
    · simpa using topGS_isGroundState (ha n)
    · exact isGroundState_neg (topGS_isGroundState (ha n))
  have hpos : ∀ n, 0 ≤ xcorr (fun t => σ n * g n t) (φ n) 0 := by
    intro n
    rw [xcorr_zero_eq]
    simp only [mul_assoc]
    rw [integral_const_mul, ← xcorr_zero_eq]
    simp only [σ]
    split_ifs with h
    · linarith
    · push Not at h; nlinarith
  have hbd : ∀ n, normSq (fun t => σ n * g n t - φ n t)
      ≤ 2 * ((weilQ (a n) (φ n) - lam (a n)) / (s n - lam (a n))) := by
    intro n
    have := normSq_sub_le_of_gap (ha n) (hgs n) (hφp n) (hφ1 n) (hs n) (hsl n) (hpos n)
    rwa [mul_div_assoc] at this
  refine rh_of_close_top ha hk hσ fun b hb => ?_
  -- `√(2a) e^{ab} √N ≤ √(4 a e^{2ab} R)` with `R → 0`
  have hR := (hrel b hb).const_mul 4
  rw [mul_zero] at hR
  have hsq := hR.sqrt
  rw [Real.sqrt_zero] at hsq
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hsq
  have hN := hbd n
  have hN0 := normSq_nonneg (fun t => σ n * g n t - φ n t)
  have hlhs : Real.sqrt (2 * a n) * Real.exp (a n * b)
      * Real.sqrt (normSq fun t => σ n * g n t - φ n t)
      = Real.sqrt (2 * a n * Real.exp (a n * b) ^ 2 * normSq fun t => σ n * g n t - φ n t) := by
    have h2a : 0 ≤ 2 * a n := by have := ha n; positivity
    rw [Real.sqrt_mul (show 0 ≤ 2 * a n * Real.exp (a n * b) ^ 2 by positivity)
      (normSq fun t => σ n * g n t - φ n t), Real.sqrt_mul h2a (Real.exp (a n * b) ^ 2),
      Real.sqrt_sq (Real.exp_pos _).le]
  show Real.sqrt (2 * a n) * Real.exp (a n * b) * Real.sqrt (normSq fun t => σ n * g n t - φ n t) ≤ _
  rw [hlhs]
  apply Real.sqrt_le_sqrt
  have he : Real.exp (a n * b) ^ 2 = Real.exp (2 * b * a n) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he]
  have hpos' : 0 ≤ 2 * a n * Real.exp (2 * b * a n) := by have := ha n; positivity
  calc 2 * a n * Real.exp (2 * b * a n) * normSq (fun t => σ n * g n t - φ n t)
      ≤ 2 * a n * Real.exp (2 * b * a n)
          * (2 * ((weilQ (a n) (φ n) - lam (a n)) / (s n - lam (a n)))) :=
        mul_le_mul_of_nonneg_left hN hpos'
    _ = 4 * (a n * Real.exp (2 * b * a n)
          * ((weilQ (a n) (φ n) - lam (a n)) / (s n - lam (a n)))) := by ring

/-! ## Every moment condition follows from (a) on the strip -/

/-- Locally uniform convergence of entire functions on an open set carries over to every
iterated derivative. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ n, Differentiable ℂ (F n))
    (h : TendstoLocallyUniformlyOn F f atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n)) (iteratedDeriv k f) atTop U := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      simp only [iteratedDeriv_succ]
      refine ih.deriv (Eventually.of_forall fun n => ?_) hU
      have hd : Differentiable ℂ (iteratedDeriv k (F n)) :=
        ((hF n).contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)
      exact hd.differentiableOn

/-- **The moment conditions.** (a) on the strip makes every Taylor coefficient at `0` of
`ĝ_n/ĝ_n(0)` converge to that of `Ξ/Ξ(0)`. For `k = 2` this is the second-moment condition
`m₂(g_n) → M₂(Φ)`, i.e. `κ(a_n) → 0` (round 40), since `ĝ(z)/ĝ(0) = 1 − (m₂/2)z² + O(z⁴)`. -/
theorem moments_of_hypConvStrip {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hg : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n)) (h : HypConvStrip a g) (k : ℕ) :
    Tendsto (fun n => iteratedDeriv k (fun z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0) 0)
      atTop (𝓝 (iteratedDeriv k (fun z => Xi z / Xi 0) 0)) := by
  have hk := tendstoLocallyUniformlyOn_iteratedDeriv isOpen_stripSet
    (fun n => (ghatC_differentiable (hg n)).div_const _) h k
  exact hk.tendsto_at zero_mem_stripSet

end Pilot1ca

#print axioms Pilot1ca.hurwitz_closed_on
#print axioms Pilot1ca.rh_of_strip_cross
#print axioms Pilot1ca.rh_of_hypConvStrip_top
#print axioms Pilot1ca.hypConvStrip_of_hypConv
#print axioms Pilot1ca.norm_ghatC_sub_le
#print axioms Pilot1ca.tendstoLocallyUniformlyOn_of_close
#print axioms Pilot1ca.tendstoLocallyUniformlyOn_ratio
#print axioms Pilot1ca.normSq_sub_le_of_gap
#print axioms Pilot1ca.hypConvStrip_of_close
#print axioms Pilot1ca.rh_of_close_top
#print axioms Pilot1ca.rh_of_relgap
#print axioms Pilot1ca.tendstoLocallyUniformlyOn_iteratedDeriv
#print axioms Pilot1ca.moments_of_hypConvStrip
