import Mathlib
import HurwitzCross
import StripConv
import Curvature
import Limit
import HadamardApply
import ExplicitBridge
import DHZeros
import DHBridge
import DHCertificate
import DHOffCross

/-! # The dh column of the substitution matrix, part 1

Pilot theorems about `ζ`/`Ξ`, restated for the Davenport–Heilbronn function `dh` and
`Ξ_dh = XiDH chi5`. Where the ζ statement takes `Ξ`'s Hadamard factorisation, `Ξ(0) ≠ 0` or the
entireness of `Ξ` as a named input or proves it from facts about `ζ`, the dh statement uses the landed
dh facts `hadamard_dh'`, `XiDH_chi5_zero_ne'`, `differentiable_XiDH_chi5` (except `hypConvDH_of_D`, which keeps the factorisation as its input `hX`, as `hypConv_of_D` does; `dhRH_of_D_and_realRooted_proved` discharges it with `hadamard_dh'`). The `not_…` theorems then
refute the dh hypotheses with the certificate (`dh_offline_zero`, `QDHu_packet_neg`, and
`dh_offline_nonreal_zero` of DHOffCross.lean): for `dh`, each of those sets of hypotheses is
unsatisfiable.

Each declaration (left) and the pilot declaration it is the dh column of (right):

* zero-free half-plane and strip
  - `dh_ne_zero_of_two_le` — `dh_ne_zero_of_two_lt` (DHPrime.lean:580), with `≤` in place of `<`
  - `XiDH_ne_zero_of_le` — `XiDH_ne_zero_of_lt` (DHExplicit.lean:128), with `≤` in place of `<`
  - `tau3_im_lt` — `tau_im` (WeilAssemble.lean:32); the strict form of `tau3_im` (DHExplicit.lean:138)
* the ordinate map; the certificate in `Ξ`-coordinates
  - `XiDH_at_ordinate` — `Xi_at_ordinate` (Roadmap.lean:113)
  - `XiDH_nonreal_zero` — no ζ counterpart (for `ζ` it would be `¬ RiemannHypothesis`):
    `dh_offline_zero` carried through `XiDH_at_ordinate` and `re_eq_half_of_Xi_real` (Roadmap.lean:146)
* the prime-side chains (Hurwitz at `Ξ_dh`)
  - `HypConvDH` — `HypConv` (PrimeSide.lean:37)
  - `eventually_ne_on` — `eventually_ghatC_zero_ne` (PrimeSide.lean:49)
  - `HypConvDH.eventually_ne` — `HypConv.eventually_ne` (PrimeSide.lean:57)
  - `dhRH_of_realRooted`, `not_hypConvDH_of_realRooted` — `rh_of_prime_side` (HurwitzCross.lean:78),
    with the ground-state hypothesis replaced by the integrability it is used for
    (HurwitzCross.lean:52–53)
  - `DHRHcross` — the χ-side `GRHCross` (CrossCriteria.lean:131); for `ζ` the cross occurs only
    inside `rh_of_prime_side_cross`
  - `dhRHcross_of_cross`, `dhRH_of_cross`, `not_hypConvDH_of_cross` — `rh_of_prime_side_cross`
    (HurwitzCross.lean:45); `dhRHcross_of_cross` has no real-zero input and concludes the cross,
    `dhRH_of_cross` takes the real-zero exclusion as `hreal` (the column of
    `hζ : ZetaNoZeroInUnitInterval`, over all `σ > 0`)
  - `stripW`, `isOpen_stripW` — `stripSet`, `isOpen_stripSet` (StripConv.lean:39, 41)
  - `HypConvStripDH` — `HypConvStrip` (StripConv.lean:48)
  - `ordinate_mem_stripW` — `ordinate_mem_strip` (StripConv.lean:56)
  - `dhRHcross_of_strip`, `not_hypConvStripDH_of_cross` — `rh_of_strip_cross` (StripConv.lean:64)
  - `not_realRooted_limit_XiDH` — `rh_of_realRooted_limit` (Roadmap.lean:260)
* the pairing / Hypothesis D route
  - `tendstoLocallyUniformly_of_pairing_gen` — `tendstoLocallyUniformly_of_pairing` (Limit.lean:135)
  - `real_of_pairing` — `rh_of_pairing_and_realRooted` (Limit.lean:191)
  - `hypConvDH_of_D` — `hypConv_of_D` (PrimeSide.lean:63)
  - `dhRH_of_D_and_realRooted_proved`, `not_D_and_realRooted`, `not_D_dh` —
    `rh_of_D_and_realRooted_proved` (HadamardApply.lean:177); its named inputs `XiGrowth` and
    `Xi 0 ≠ 0` are replaced by `hadamard_dh'`
* the dodging route
  - `real_of_params` — `rh_of_Xi_params` (Curvature.lean:53)
  - `real_of_dodging` — `rh_of_dodging` (Curvature.lean:86)
  - `not_dodging_dh` — `rh_of_dodging_final` (Curvature.lean:415)
* Weil positivity
  - `tau3_cross_of_DHRHcross` — the cross form of `tau3_real_of_DHRH` (DHExplicit.lean:387)
  - `QDHu_nonneg_of_DHRHcross` — the χ-side `QC_nonneg_of_cross` (CrossCriteria.lean:43); the
    every-probe form of `QDHu_packet_nonneg_of_line_or_real` (DHOffCross.lean:35)
  - `not_weil_positivity_dh` — `rh_of_weil` (WeilLandau.lean:153)
  - `weil_criterion_dh` — `weil_criterion_zeta` (WeilRH.lean:157)
  - `not_GRH_dh` — `GRHMemberZero` / `rh_of_member_zero` (AngularFamily.lean:97, 102)
* the Weil index
  - `nonneg_of_hasSum_sq`, `finrank_le_quadruples_gen`, `finrank_le_quadruples'` —
    `finrank_le_quadruples` (ExplicitBridge.lean:282), with the form and the zero-sum identity
    abstracted; `finrank_le_quadruples'` re-derives the ζ statement from the abstract one
  - `finrank_le_quadruples_dh`, `finrank_le_quadruples_dh_scaled` — `finrank_le_quadruples_zeta`
    (WeilIndexZeta.lean:52), for `Q_dh`

Both sides of `weil_criterion_dh` are false (`not_weil_positivity_dh`, `dh_offline_zero`); it is
proved by refuting each side and so needs no strip-test hypothesis on the probes. -/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## `dh ≠ 0` on `Re s ≥ 2`; the zeros of `Ξ₃` in the open strip -/

/-- `dh` has no zeros on `Re s ≥ 2`: the proof of `dh_ne_zero_of_two_lt`, which uses `2 < Re s` only
through `2 ≤ Re s` and `1 < Re s`. -/
theorem dh_ne_zero_of_two_le {s : ℂ} (hs : 2 ≤ s.re) : dh s ≠ 0 := by
  have ha1 := aDH_one_ne_zero chi5_ne_one chi5_isPrimitive one_add_rootNumber_chi5_ne_zero
  have hinv := DInv.LSeries_mul_dinv (uDH chi5) uDH_zero uDH_one (σ := 2) (K := 7 / 9) (by norm_num)
    (by norm_num) sum_norm_uDH_chi5_le hs (LSeriesSummable_uDH (by linarith))
  show dhL chi5 s ≠ 0
  rw [dhL_eq_LSeries (by linarith), LSeries_aDH_eq ha1]
  exact mul_ne_zero ha1 (left_ne_zero_of_mul_eq_one hinv)

/-- `Ξ_dh(t) ≠ 0` when `Re(½ + it) ≥ 2`. -/
theorem XiDH_ne_zero_of_le {t : ℂ} (ht : t.im ≤ -(3 / 2)) : XiDH chi5 t ≠ 0 := by
  have hs : 2 ≤ (1 / 2 + I * t).re := by simp; linarith
  have h0 : 0 < (1 / 2 + I * t).re := by linarith
  show dhLam chi5 (1 / 2 + I * t) ≠ 0
  rw [dhLam_eq chi5 chi5_odd h0]
  refine mul_ne_zero (mul_ne_zero ?_ (Gammaℝ_ne_zero_of_re_pos (by simp; linarith))) ?_
  · rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
  · exact dh_ne_zero_of_two_le hs

/-- **The zeros of `Ξ₃` lie in the open strip `|Im τ| < ½`.** -/
theorem tau3_im_lt (i : ZeroIdx (sqF XiDH3)) : |(tau3 i).im| < 1 / 2 := by
  rw [abs_lt]
  constructor
  · by_contra h
    push Not at h
    have := XiDH3_tau i
    unfold XiDH3 at this
    exact XiDH_ne_zero_of_le (by simp; linarith) this
  · by_contra h
    push Not at h
    have := XiDH3_tau i
    rw [← XiDH3_even] at this
    unfold XiDH3 at this
    exact XiDH_ne_zero_of_le (by simp; linarith) this

/-! ## The ordinate map; the certificate in `Ξ`-coordinates -/

theorem XiDH_at_ordinate (s : ℂ) : XiDH chi5 ((s - 1 / 2) / I) = dhLam chi5 s := by
  unfold XiDH; congr 1; field_simp; ring

/-- `Ξ_dh` has a non-real zero (from `dh_offline_zero`). -/
theorem XiDH_nonreal_zero : ∃ z, XiDH chi5 z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  refine ⟨(s - 1 / 2) / I, ?_, fun h => hne (re_eq_half_of_Xi_real h)⟩
  rw [XiDH_at_ordinate]; exact (dh_eq_zero_iff h0).1 hs

/-! ## The prime-side chains with `Ξ_dh` as the target -/

/-- `HypConv` with `dh`'s `Ξ` as the target. -/
def HypConvDH (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) : Prop :=
  TendstoLocallyUniformly (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
    (fun z => XiDH chi5 z / XiDH chi5 0) atTop

theorem eventually_ne_on {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {U : Set ℂ} (hU : (0 : ℂ) ∈ U)
    (h : TendstoLocallyUniformlyOn (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
      (fun z => XiDH chi5 z / XiDH chi5 0) atTop U) : ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 := by
  have ht := h.tendsto_at hU
  simp only [div_self XiDH_chi5_zero_ne'] at ht
  filter_upwards [ht.eventually_ne one_ne_zero] with n hn h0
  rw [h0, div_zero] at hn; exact hn rfl

theorem HypConvDH.eventually_ne {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (h : HypConvDH a g) :
    ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 :=
  eventually_ne_on (Set.mem_univ 0) (tendstoLocallyUniformlyOn_univ.2 h)

/-- **dh instance of `rh_of_prime_side`** (real-rooted case, by `hurwitz_real`): no ground-state
hypothesis, only integrability; no real-zero input needed. -/
theorem dhRH_of_realRooted {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hRR : ∀ᶠ n in atTop, RealRooted (a n) (g n)) (hconv : HypConvDH a g) : DHRH := by
  have hX0 := XiDH_chi5_zero_ne'
  obtain ⟨N, hN⟩ := (hRR.and hconv.eventually_ne).exists_forall_of_atTop
  have hXr : ∀ z, XiDH chi5 z / XiDH chi5 0 = 0 → z.im = 0 :=
    hurwitz_real (F := fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      (fun m => (ghatC_differentiable (hint _)).div_const _)
      (differentiable_XiDH_chi5.div_const _) (tendstoLocallyUniformly_shift hconv N)
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩
      (fun m z h => (hN (m + N) (by omega)).1 z
        ((div_eq_zero_iff.1 h).resolve_right (hN (m + N) (by omega)).2))
  intro s hs h0
  apply re_eq_half_of_Xi_real
  apply hXr
  rw [XiDH_at_ordinate, (dh_eq_zero_iff h0).1 hs, zero_div]

/-- **The refutation**: for every integrable sequence with eventually real-rooted transforms,
`HypConvDH` fails (kernel-checked off-line zero). -/
theorem not_hypConvDH_of_realRooted {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hRR : ∀ᶠ n in atTop, RealRooted (a n) (g n)) : ¬ HypConvDH a g := fun h => by
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  exact hne (dhRH_of_realRooted hint hRR h s hs h0)

/-- RH for `dh` weakened to the cross: every zero with `Re s > 0` is on the line or real. -/
def DHRHcross : Prop := ∀ s : ℂ, dh s = 0 → 0 < s.re → s.re = 1 / 2 ∨ s.im = 0

/-- **dh instance of `rh_of_prime_side_cross`**, with no real-zero input (conclusion: the cross). -/
theorem dhRHcross_of_cross {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0)
    (hconv : HypConvDH a g) : DHRHcross := by
  have hX0 := XiDH_chi5_zero_ne'
  obtain ⟨N, hN⟩ := (hcross.and hconv.eventually_ne).exists_forall_of_atTop
  have hXc : ∀ z, XiDH chi5 z / XiDH chi5 0 = 0 → z ∈ crossSet :=
    hurwitz_closed (F := fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      (fun m => (ghatC_differentiable (hint _)).div_const _)
      (differentiable_XiDH_chi5.div_const _) (tendstoLocallyUniformly_shift hconv N)
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩ isClosed_crossSet
      (fun m z h => (hN (m + N) (by omega)).1 z
        ((div_eq_zero_iff.1 h).resolve_right (hN (m + N) (by omega)).2))
  intro s hs h0
  rcases hXc ((s - 1 / 2) / I) (by rw [XiDH_at_ordinate, (dh_eq_zero_iff h0).1 hs, zero_div])
    with hre | him
  · right; rwa [re_ordinate] at hre
  · left; exact re_eq_half_of_Xi_real him

/-- **dh instance of `rh_of_prime_side_cross`**, with the real-zero exclusion as a named input. -/
theorem dhRH_of_cross {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0)
    (hconv : HypConvDH a g) (hreal : ∀ σ : ℝ, 0 < σ → dh (σ : ℂ) ≠ 0) : DHRH := by
  intro s hs h0
  refine (dhRHcross_of_cross hint hcross hconv s hs h0).resolve_right fun him => ?_
  have hsr : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  exact hreal s.re h0 (by rw [← hsr]; exact hs)

/-- **Refutation of the cross chain for dh**: no integrable sequence with transforms eventually
vanishing only on `ℝ ∪ iℝ` satisfies `HypConvDH`. -/
theorem not_hypConvDH_of_cross {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0) :
    ¬ HypConvDH a g := fun h => by
  obtain ⟨s, hs, h0, hne, him⟩ := dh_offline_nonreal_zero
  rcases dhRHcross_of_cross hint hcross h s hs h0 with h1 | h1
  · exact hne h1
  · exact him h1

/-! ### The strip version, at the width that contains every zero of `Ξ_dh` -/

def stripW (w : ℝ) : Set ℂ := {z | |z.im| < w}

theorem isOpen_stripW (w : ℝ) : IsOpen (stripW w) :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

def HypConvStripDH (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (w : ℝ) : Prop :=
  TendstoLocallyUniformlyOn (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
    (fun z => XiDH chi5 z / XiDH chi5 0) atTop (stripW w)

theorem ordinate_mem_stripW {s : ℂ} (hs : dh s = 0) (h0 : 0 < s.re) :
    (s - 1 / 2) / I ∈ stripW 2 := by
  have h2 : s.re ≤ 2 := by
    by_contra h; exact dh_ne_zero_of_two_lt (lt_of_not_ge h) hs
  have e : (s - 1 / 2) / I = -I * (s - 1 / 2) := by field_simp; rw [I_sq]; ring
  show |((s - 1 / 2) / I).im| < 2
  rw [e]; simp
  rw [abs_lt]; constructor <;> linarith

/-- **dh instance of `rh_of_strip_cross`** at width `2`. -/
theorem dhRHcross_of_strip {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0)
    (hconv : HypConvStripDH a g 2) : DHRHcross := by
  have hX0 := XiDH_chi5_zero_ne'
  have h0 := eventually_ne_on (show (0 : ℂ) ∈ stripW 2 by simp [stripW]) hconv
  obtain ⟨N, hN⟩ := (hcross.and h0).exists_forall_of_atTop
  have hconvN : TendstoLocallyUniformlyOn
      (fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      (fun z => XiDH chi5 z / XiDH chi5 0) atTop (stripW 2) := fun u hu x hx => by
    obtain ⟨t, ht, hev⟩ := hconv u hu x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩
  have hXc : ∀ z ∈ stripW 2, XiDH chi5 z / XiDH chi5 0 = 0 → z ∈ crossSet :=
    hurwitz_closed_on (F := fun m z => ghatC (g (m + N)) (a (m + N)) z / ghatC (g (m + N)) (a (m + N)) 0)
      (isOpen_stripW 2)
      (fun m => (ghatC_differentiable (hint _)).div_const _)
      (differentiable_XiDH_chi5.div_const _) hconvN
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩ isClosed_crossSet
      (fun m z h => (hN (m + N) (by omega)).1 z
        ((div_eq_zero_iff.1 h).resolve_right (hN (m + N) (by omega)).2))
  intro s hs hpos
  rcases hXc ((s - 1 / 2) / I) (ordinate_mem_stripW hs hpos)
    (by rw [XiDH_at_ordinate, (dh_eq_zero_iff hpos).1 hs, zero_div]) with hre | him
  · right; rwa [re_ordinate] at hre
  · left; exact re_eq_half_of_Xi_real him

theorem not_hypConvStripDH_of_cross {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0) :
    ¬ HypConvStripDH a g 2 := fun h => by
  obtain ⟨s, hs, h0, hne, him⟩ := dh_offline_nonreal_zero
  rcases dhRHcross_of_strip hint hcross h s hs h0 with h1 | h1
  · exact hne h1
  · exact him h1

/-! ### Real-rooted limits -/

/-- **The dh column of `rh_of_realRooted_limit`**: no real-rooted entire functions `F n` with nonzero
scalars `c n` satisfy `c n · F n → Ξ_dh` locally uniformly. -/
theorem not_realRooted_limit_XiDH {F : ℕ → ℂ → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (hreal : ∀ n z, F n z = 0 → z.im = 0) {c : ℕ → ℂ} (hc : ∀ n, c n ≠ 0)
    (hconv : TendstoLocallyUniformly (fun n z => c n * F n z) (XiDH chi5) atTop) : False := by
  have hX : ∀ z, XiDH chi5 z = 0 → z.im = 0 :=
    hurwitz_real (fun n => (differentiable_const _).mul (hF n)) differentiable_XiDH_chi5 hconv
      ⟨0, XiDH_chi5_zero_ne'⟩
      (fun n z h => hreal n z ((mul_eq_zero.1 h).resolve_left (hc n)))
  obtain ⟨z, hz, him⟩ := XiDH_nonreal_zero
  exact him (hX z hz)

/-! ## The pairing / Hypothesis D route -/

/-- `tendstoLocallyUniformly_of_pairing` (Limit.lean:135) with `Ξ` replaced by any `f`. -/
theorem tendstoLocallyUniformly_of_pairing_gen {ι : ℕ → Type*} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {w v : ∀ n, ι n → ℂ} (hF : ∀ n, HadamardW (F n) (w n)) (hX : ∀ n, HadamardW f (v n))
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {θ : ℕ → ℝ}
    (hθ : ∀ n, (∑' i, ‖w n i - v n i‖) ≤ θ n) (hθ0 : Tendsto θ atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun n z => F n z / F n 0) (fun z => f z / f 0) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hR' : ∀ z ∈ K, ‖z‖ ≤ max R 0 := fun z hz => by
    have := hR hz; rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set R0 := max R 0
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  -- the bound `R0² e^{R0²(2B + θ + 1)} θ n → 0`
  set c := R0 ^ 2 * Real.exp (R0 ^ 2 * (2 * B + 1 + 1))
  have hc : 0 ≤ c := by positivity
  have hlim : Tendsto (fun n => c * θ n) atTop (𝓝 0) := by simpa using hθ0.const_mul c
  have hev1 := hlim.eventually (gt_mem_nhds hη)
  have hev2 := hθ0.eventually (gt_mem_nhds one_pos)
  filter_upwards [hev1, hev2] with n h1 h2 z hz
  have hzR := hR' z hz
  have hsw : 0 ≤ ∑' i, ‖w n i‖ := tsum_nonneg fun _ => norm_nonneg _
  have hsv : (∑' i, ‖v n i‖) ≤ B + θ n := by
    have hs : Summable fun i => ‖w n i - v n i‖ :=
      ((hF n).summ.add (hX n).summ).of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun i => norm_sub_le _ _)
    calc (∑' i, ‖v n i‖) ≤ ∑' i, (‖w n i‖ + ‖w n i - v n i‖) :=
          (hX n).summ.tsum_le_tsum (fun i => by
            have := norm_sub_norm_le (v n i) (w n i)
            rw [norm_sub_rev (v n i)] at this; linarith) ((hF n).summ.add hs)
      _ = (∑' i, ‖w n i‖) + ∑' i, ‖w n i - v n i‖ := (hF n).summ.tsum_add hs
      _ ≤ B + θ n := add_le_add (hB n) (hθ n)
  have hθn : 0 ≤ θ n := le_trans (tsum_nonneg fun _ => norm_nonneg _) (hθ n)
  have hcmp := hadamard_compare (hF n) (hX n) z
  rw [dist_comm, dist_eq_norm]
  calc ‖F n z / F n 0 - f z / f 0‖
      ≤ ‖z‖ ^ 2 * Real.exp (‖z‖ ^ 2 * ((∑' i, ‖w n i‖) + ∑' i, ‖v n i‖)) * ∑' i, ‖w n i - v n i‖ :=
        hcmp
    _ ≤ R0 ^ 2 * Real.exp (R0 ^ 2 * (2 * B + 1 + 1)) * θ n := by
        have hz2 : ‖z‖ ^ 2 ≤ R0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR 2
        have hsum : (∑' i, ‖w n i‖) + ∑' i, ‖v n i‖ ≤ 2 * B + 1 + 1 := by
          linarith [hB n]
        have hs0 : 0 ≤ (∑' i, ‖w n i‖) + ∑' i, ‖v n i‖ :=
          add_nonneg hsw (tsum_nonneg fun _ => norm_nonneg _)
        gcongr
        exact hθ n
    _ < η := h1

/-- `rh_of_pairing_and_realRooted` (Limit.lean:191) for any entire `G`: all zeros real. The
nonvanishing witness is `0` (`G 0 / G 0 = 1`), not `ξ(2) ≠ 0`. -/
theorem real_of_pairing {G : ℂ → ℂ} (hG : Differentiable ℂ G) {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) MeasureTheory.volume (-(a n)) (a n))
    (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type*} {w v : ∀ n, ι n → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : ∀ n, HadamardW G (v n))
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {θ : ℕ → ℝ}
    (hθ : ∀ n, (∑' i, ‖w n i - v n i‖) ≤ θ n) (hθ0 : Tendsto θ atTop (𝓝 0)) :
    ∀ z, G z = 0 → z.im = 0 := by
  have hconv := tendstoLocallyUniformly_of_pairing_gen hF hX hB hθ hθ0
  have hX0 : G 0 ≠ 0 := (hX 0).f0
  have hreal : ∀ z, G z / G 0 = 0 → z.im = 0 :=
    hurwitz_real (F := fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
      (fun n => (ghatC_differentiable (hint n)).div_const _)
      (hG.div_const _) hconv
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩
      (fun n z h => hRR n z ((div_eq_zero_iff.1 h).resolve_right (hF n).f0))
  intro z hz
  exact hreal z (by rw [hz, zero_div])

/-- **dh instance of `hypConv_of_D`**. -/
theorem hypConvDH_of_D {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW (XiDH chi5) v)
    {B : ℝ} (hB : ∀ n, (∑' i, ‖w n i‖) ≤ B) {t : ℕ → ℝ} (hD : ∀ n, DFamW (w n) v (t n))
    (hε : Tendsto (fun n => tailEps (w n) v (t n)) atTop (𝓝 0)) : HypConvDH a g := by
  choose P w' v' hw' hv' hsw hθ using fun n => pairing_of_D (hF n) hX (hD n)
  exact tendstoLocallyUniformly_of_pairing_gen hw' hv' (fun n => (hsw n).le.trans (hB n)) hθ hε

/-- **dh instance of `rh_of_D_and_realRooted_proved`**: every named input of the ζ version is
already discharged for `dh` (`hadamard_dh'`). -/
theorem dhRH_of_D_and_realRooted_proved {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (heven : ∀ n u, g n (-u) = g n u) (hg0 : ∀ n, ghatC (g n) (a n) 0 ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n))
    {B : ℝ} (hB : ∀ n, (∑' i : ZeroIdx (sqF (ghatC (g n) (a n))), ‖i.1⁻¹‖) ≤ B)
    {t : ℕ → ℝ}
    (hD : ∀ n, DFamW (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) (t n))
    (hε : Tendsto (fun n => tailEps (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) (t n)) atTop (𝓝 0)) : DHRH :=
  dhRH_of_realRooted hint (Eventually.of_forall hRR)
    (hypConvDH_of_D (fun n => hadamardW_ghat (ha n) (hint n) (heven n) (hg0 n)) hadamard_dh' hB hD hε)

/-- **The refutation of the D route**: for every real-rooted family as in
`dhRH_of_D_and_realRooted_proved`, the tails `ε` do not tend to `0`. -/
theorem not_D_and_realRooted {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (heven : ∀ n u, g n (-u) = g n u) (hg0 : ∀ n, ghatC (g n) (a n) 0 ≠ 0)
    (hRR : ∀ n, RealRooted (a n) (g n))
    {B : ℝ} (hB : ∀ n, (∑' i : ZeroIdx (sqF (ghatC (g n) (a n))), ‖i.1⁻¹‖) ≤ B)
    {t : ℕ → ℝ}
    (hD : ∀ n, DFamW (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) (t n)) :
    ¬ Tendsto (fun n => tailEps (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) (t n)) atTop (𝓝 0) := fun hε => by
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  exact hne (dhRH_of_D_and_realRooted_proved ha hint heven hg0 hRR hB hD hε s hs h0)

/-- **The dh column of `rh_of_D_and_realRooted_proved`**, existential form: exact Hypothesis D against
`Ξ_dh`'s own zero list with tails `ε → 0` fails for every real-rooted family. -/
theorem not_D_dh : ¬ ∃ (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (B : ℝ) (t : ℕ → ℝ),
    (∀ n, 0 ≤ a n) ∧ (∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n)) ∧
    (∀ n u, g n (-u) = g n u) ∧ (∀ n, ghatC (g n) (a n) 0 ≠ 0) ∧
    (∀ n, RealRooted (a n) (g n)) ∧
    (∀ n, (∑' i : ZeroIdx (sqF (ghatC (g n) (a n))), ‖i.1⁻¹‖) ≤ B) ∧
    (∀ n, DFamW (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) (t n)) ∧
    Tendsto (fun n => tailEps (fun i : ZeroIdx (sqF (ghatC (g n) (a n))) => i.1⁻¹)
      (fun i : ZeroIdx (sqF (XiDH chi5)) => i.1⁻¹) (t n)) atTop (𝓝 0) := by
  rintro ⟨a, g, B, t, ha, hint, heven, hg0, hRR, hB, hD, hε⟩
  exact not_D_and_realRooted ha hint heven hg0 hRR hB hD hε

/-! ## The dodging route -/

/-- `rh_of_Xi_params`'s `hreal` step, for any `F` with a Hadamard factorisation. -/
theorem real_of_params {κ : Type*} {F : ℂ → ℂ} {v : κ → ℂ} (hX : HadamardW F v)
    (hv : ∀ j, (v j).im = 0 ∧ 0 ≤ (v j).re) : ∀ z, F z = 0 → z.im = 0 := by
  intro z hz
  by_contra him
  have hne : ∀ j, 1 + -(z ^ 2 * v j) ≠ 0 := by
    intro j hj
    have h1 : z ^ 2 * v j = 1 := by linear_combination -hj
    have hvr : v j = ((v j).re : ℂ) := Complex.ext rfl (by simp [(hv j).1])
    rw [hvr] at h1
    have hre := congrArg Complex.re h1
    have him' := congrArg Complex.im h1
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, mul_zero, sub_zero] at hre him'
    have hr : (v j).re ≠ 0 := fun h => by rw [h, mul_zero] at hre; exact zero_ne_one hre
    have hzre : z.re = 0 := by
      have : (z.re * z.im) * (2 * (v j).re) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact (mul_eq_zero.1 h).resolve_right him
      · exact absurd (by linarith : (v j).re = 0) hr
    rw [hzre] at hre
    nlinarith [sq_nonneg z.im, (hv j).2]
  have := tprod_one_add_ne_zero_of_summable hne (summable_scaled hX.summ z)
  rw [← hX.eq_tprod z, hz, zero_div] at this
  exact this rfl

/-- `rh_of_dodging` with `Ξ` replaced by any `F` with a Hadamard factorisation: the proof text of
Curvature.lean:94–116, with `real_of_params` in place of `rh_of_Xi_params` in its opening `refine`. -/
theorem real_of_dodging {F : ℂ → ℂ} {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (hRR : ∀ n, RealRooted (a n) (g n))
    {ι : ℕ → Type} {κ : Type} {w : ∀ n, ι n → ℂ} {v : κ → ℂ}
    (hF : ∀ n, HadamardW (ghatC (g n) (a n)) (w n)) (hX : HadamardW F v)
    {t η : ℕ → ℝ}
    (hD : ∀ n, ∃ (p : ι n → Prop) (e : {i // p i} ≃ {j // t n < ‖v j‖}),
      (∑' i : {i // p i}, ‖w n i - v (e i)‖) ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0)) :
    ∀ z, F z = 0 → z.im = 0 := by
  refine real_of_params hX fun j => ?_
  by_cases hj : v j = 0
  · simp [hj]
  set C : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}
  have hC : IsClosed C := (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)
  have hev : ∀ᶠ n in atTop, ∃ x ∈ C, dist (v j) x ≤ η n := by
    filter_upwards [ht.eventually (gt_mem_nhds (norm_pos_iff.2 hj))] with n hn
    obtain ⟨p, e, he⟩ := hD n
    set i := e.symm ⟨j, hn⟩
    have hei : (e i : κ) = j := by simp [i]
    have hs : Summable fun i : {i // p i} => ‖w n i - v (e i)‖ := by
      have h2 : Summable fun i : {i // p i} => ‖v (e i)‖ :=
        (e.summable_iff (f := fun j : {j // t n < ‖v j‖} => ‖v j‖)).2 (hX.summ.subtype _)
      exact (((hF n).summ.subtype _).add h2).of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun _ => norm_sub_le _ _)
    refine ⟨w n i, (hF n).nonneg_real (hRR n) i, ?_⟩
    rw [dist_eq_norm, norm_sub_rev, ← hei]
    exact (hs.le_tsum i fun _ _ => norm_nonneg _).trans he
  have hmem : v j ∈ closure C := Metric.mem_closure_iff.2 fun ε hε => by
    obtain ⟨n, ⟨x, hx, hd⟩, hn⟩ := (hev.and (hη.eventually (gt_mem_nhds hε))).exists
    exact ⟨x, hx, hd.trans_lt hn⟩
  rwa [hC.closure_eq] at hmem

/-- **The dh column of `rh_of_dodging_final`**: no sequence of real-rooted even transforms dodges
`Ξ_dh`'s zeros in the sense of `hD`. -/
theorem not_dodging_dh : ¬ ∃ (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (t η : ℕ → ℝ),
    (∀ n, 0 ≤ a n) ∧ (∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n)) ∧
    (∀ n u, g n (-u) = g n u) ∧ (∀ n, (∫ u in (-(a n))..(a n), g n u) ≠ 0) ∧
    (∀ n, RealRooted (a n) (g n)) ∧
    (∀ n, ∃ (p : ZeroIdx (sqF (ghatC (g n) (a n))) → Prop)
      (e : {i // p i} ≃ {j : ZeroIdx (sqF (XiDH chi5)) // t n < ‖j.1⁻¹‖}),
      (∑' i : {i // p i}, ‖i.1.1⁻¹ - (e i).1.1⁻¹‖) ≤ η n) ∧
    Tendsto η atTop (𝓝 0) ∧ Tendsto t atTop (𝓝 0) := by
  rintro ⟨a, g, t, η, ha, hint, heven, hg0, hRR, hD, hη, ht⟩
  have h0 : ∀ n, ghatC (g n) (a n) 0 ≠ 0 := fun n => by
    rw [ghatC_zero]; exact_mod_cast hg0 n
  have hreal := real_of_dodging hRR
    (w := fun n (i : ZeroIdx (sqF (ghatC (g n) (a n)))) => i.1⁻¹)
    (v := fun j : ZeroIdx (sqF (XiDH chi5)) => j.1⁻¹)
    (fun n => hadamardW_ghat (ha n) (hint n) (heven n) (h0 n)) hadamard_dh' hD hη ht
  obtain ⟨z, hz, him⟩ := XiDH_nonreal_zero
  exact him (hreal z hz)

/-! ## Weil positivity -/

/-- Under `DHRHcross` every `τ_u` is real or purely imaginary. -/
theorem tau3_cross_of_DHRHcross (hRH : DHRHcross) (i : ZeroIdx (sqF XiDH3)) :
    (tau3 i).im = 0 ∨ (tau3 i).re = 0 := by
  have hz := XiDH3_tau i
  have key : ∀ τ : ℂ, XiDH3 τ = 0 → τ.im ≤ 0 → τ.im = 0 ∨ τ.re = 0 := by
    intro τ hτ hle
    obtain ⟨hd, h0⟩ := dh_zero_of_XiDH3 hτ hle
    rcases hRH _ hd h0 with h | h
    · left
      have hre : (1 / 2 + I * (3 * τ)).re = 1 / 2 - 3 * τ.im := by simp; ring
      rw [hre] at h; linarith
    · right
      have him : (1 / 2 + I * (3 * τ)).im = 3 * τ.re := by simp
      rw [him] at h; linarith
  rcases le_or_gt (tau3 i).im 0 with h | h
  · exact key _ hz h
  · have := key (-(tau3 i)) (by rw [XiDH3_even]; exact hz) (by simp; linarith)
    simpa using this

/-- **`DHRHcross ⟹ Q_dh ≥ 0`**: a real or purely imaginary `τ` contributes `Re 2ĝ(3τ)² ≥ 0`
(`ĝ` is real on `ℝ` and on `iℝ`, `hsq_ofReal` and `ghatC_I_mul_im`). -/
theorem QDHu_nonneg_of_DHRHcross (hRH : DHRHcross) {a : ℝ} {g : ℝ → ℝ} (hp : Probe a g)
    (ha : 0 < a) {K : ℝ} (hK : StripTest (fun z => ghatC g a (3 * z) ^ 2) K) : 0 ≤ QDHu g := by
  have h := (QDHu_hasSum hp ha hK).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, ofReal_re] at h
  refine h.nonneg fun i => ?_
  rcases tau3_cross_of_DHRHcross hRH i with hi | hi
  · have e : (3 : ℂ) * tau3 i = ((3 * (tau3 i).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [hi])
    rw [e, hsq_ofReal hp ha.le]
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by norm_num) (hsq_nonneg _)
  · have e : (3 : ℂ) * tau3 i = I * ((3 * (tau3 i).im : ℝ) : ℂ) :=
      Complex.ext (by simp [hi]) (by simp)
    rw [e]
    have hw := ghatC_I_mul_im g a (3 * (tau3 i).im)
    set w := ghatC g a (I * ((3 * (tau3 i).im : ℝ) : ℂ))
    have : (2 * w ^ 2).re = 2 * w.re ^ 2 := by simp [sq, mul_re, hw]
    rw [this]; positivity

/-- **Weil positivity fails for `dh`**: the packet `packet (12/5) (169/2)` is a probe with
`Q_dh < 0`. -/
theorem not_weil_positivity_dh :
    ¬ ∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QDHu g := fun h =>
  absurd (h _ _ (by norm_num) (packet_probe (a := 12 / 5) (ω := 169 / 2) (by norm_num) (by norm_num)))
    (not_le.2 QDHu_packet_neg)

/-- **The dh column of `weil_criterion_zeta`.** Both sides are false (`not_weil_positivity_dh`,
`dh_offline_zero`), so the equivalence holds with no strip-test hypothesis on the probes. -/
theorem weil_criterion_dh :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QDHu g) ↔ DHRH := by
  refine ⟨fun h => absurd h not_weil_positivity_dh, fun hRH => ?_⟩
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  exact absurd (hRH s hs h0) hne

/-- **GRH fails for `dh`**: not every zero of `dh` other than `−1, −3, −5, …` lies on `Re s = ½`.
The shape is `GRHMemberZero`'s with two clauses dropped: `dh` is entire (`differentiable_dh`), so there
is no `s ≠ 1` clause, and `χ₅` is odd (the factor `Gammaℝ (s + 1)` of `dhLam_eq`), so the excluded
points are the `−(2n + 1)` of `GRHMemberZero`'s second clause rather than `ζ`'s `−2(n + 1)`. The
refutation uses a zero with `Re s > 0`, so it holds for any excluded set inside `Re s ≤ 0`. -/
theorem not_GRH_dh : ¬ ∀ s : ℂ, dh s = 0 → (¬ ∃ n : ℕ, s = -(2 * n + 1)) → s.re = 1 / 2 := by
  intro h
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  refine hne (h s hs ?_)
  rintro ⟨n, rfl⟩
  have e : (-(2 * (n : ℂ) + 1)).re = -(2 * n + 1) := by simp
  rw [e] at h0
  have := n.cast_nonneg (α := ℝ)
  linarith

/-! ## The Weil index -/

/-- Generic nonnegativity: a `HasSum` of nonnegatively weighted squares of real numbers. -/
theorem nonneg_of_hasSum_sq {ι : Type*} {c : ι → ℝ} {z : ι → ℂ} {q : ℝ}
    (hc : ∀ i, 0 ≤ c i) (h : HasSum (fun i => (c i : ℂ) * z i ^ 2) (q : ℂ))
    (hreal : ∀ i, (z i).im = 0) : 0 ≤ q := by
  have h' := Complex.hasSum_re h
  rw [Complex.ofReal_re] at h'
  refine HasSum.nonneg (fun i => ?_) h'
  have hi := hreal i
  rw [sq, Complex.mul_re, Complex.mul_re, Complex.mul_im, hi]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
  exact mul_nonneg (hc i) (mul_self_nonneg _)

/-- `finrank_le_quadruples` with the form and the zero-sum identity abstracted. -/
theorem finrank_le_quadruples_gen {a : ℝ} {ι : Type*} {t : ι → ℂ} {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) (Q : (ℝ → ℝ) → ℝ) (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (ha : 0 < a) (hV : ∀ v ∈ V, Probe a v) (hneg : ∀ v ∈ V, v ≠ 0 → Q v < 0)
    (hsum : ∀ v ∈ V, HasSum (fun i => (c i : ℂ) * ghatC v a (t i) ^ 2) (Q v : ℂ))
    (R : Finset ι)
    (hR : ∀ i, (t i).im = 0 ∨ ∃ r ∈ R,
      t i = t r ∨ t i = -t r ∨ t i = (starRingEnd ℂ) (t r) ∨ t i = -(starRingEnd ℂ) (t r)) :
    Module.finrank ℝ V ≤ R.card := by
  let L : V →ₗ[ℝ] (R → ℝ) :=
    { toFun := fun v r => (ghatC (v : ℝ → ℝ) a (t r)).im
      map_add' := fun x y => by
        funext r
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [ghatC_add (hV x x.2).memL2 (hV y y.2).memL2, Complex.add_im]
      map_smul' := fun c x => by
        funext r
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        show (ghatC (fun s => c * (x : ℝ → ℝ) s) a _).im = _
        rw [ghatC_smul]; simp }
  by_contra hlt
  push Not at hlt
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hb
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    rw [hb, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_le (LinearMap.range L)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
    omega
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv0' : (v : ℝ → ℝ) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hq := hneg v v.2 hv0'
  have hnn : 0 ≤ Q v := nonneg_of_hasSum_sq hc (hsum v v.2) fun i => by
    rcases hR i with hi | ⟨r, hr, horb⟩
    · exact im_ghat_of_real (hV v v.2) ha hi
    · have hw := congrFun (LinearMap.mem_ker.1 hvk) ⟨r, hr⟩
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hw
      exact im_ghat_of_orbit (hV v v.2) ha hw horb
  linarith

/-- The ζ statement is the instance `c = 1`, `t = (ρ − ½)/i`, `Q = weilQ a`. -/
theorem finrank_le_quadruples' {a : ℝ} {ι : Type*} {ρ : ι → ℂ} (V : Submodule ℝ (ℝ → ℝ))
    [FiniteDimensional ℝ V] (ha : 0 < a)
    (hV : ∀ v ∈ V, Probe a v) (hneg : ∀ v ∈ V, v ≠ 0 → weilQ a v < 0)
    (hEF : ∀ v ∈ V, WeilExplicit ρ (fun z => ghatC v a z ^ 2) (hsq v a))
    (R : Finset ι)
    (hR : ∀ i, (ρ i).re = 1 / 2 ∨ ∃ r ∈ R,
      let t := (ρ i - 1 / 2) / Complex.I
      let w := (ρ r - 1 / 2) / Complex.I
      t = w ∨ t = -w ∨ t = (starRingEnd ℂ) w ∨ t = -(starRingEnd ℂ) w) :
    Module.finrank ℝ V ≤ R.card :=
  finrank_le_quadruples_gen (t := fun i => (ρ i - 1 / 2) / Complex.I) (c := fun _ => 1)
    (fun _ => zero_le_one) (weilQ a) V ha hV hneg
    (fun v hv => by simpa using weilQ_eq_zero_sum (hV v hv) ha (hEF v hv)) R
    (fun i => (hR i).imp_left ordinate_im_zero)

/-- **The Davenport–Heilbronn instance**: `Q_dh` negative definite on `V` (probes with the width-3
strip test) gives `dim V ≤ |R|` for every representative set `R` of the off-line zeros of `dh`. -/
theorem finrank_le_quadruples_dh {a : ℝ} (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (ha : 0 < a) (hV : ∀ v ∈ V, Probe a v)
    (hS : ∀ v ∈ V, ∃ K, StripTest (fun z => ghatC v a (3 * z) ^ 2) K)
    (hneg : ∀ v ∈ V, v ≠ 0 → QDHu v < 0)
    (R : Finset (ZeroIdx (sqF XiDH3)))
    (hR : ∀ i, (3 * tau3 i).im = 0 ∨ ∃ r ∈ R,
      3 * tau3 i = 3 * tau3 r ∨ 3 * tau3 i = -(3 * tau3 r)
        ∨ 3 * tau3 i = (starRingEnd ℂ) (3 * tau3 r) ∨ 3 * tau3 i = -(starRingEnd ℂ) (3 * tau3 r)) :
    Module.finrank ℝ V ≤ R.card :=
  finrank_le_quadruples_gen (t := fun i => 3 * tau3 i) (c := fun _ => 2) (fun _ => by norm_num)
    QDHu V ha hV hneg (fun v hv => by
      obtain ⟨K, hK⟩ := hS v hv
      simpa using QDHu_hasSum (hV v hv) ha hK) R hR

/-- The scaled instance: `QDH a`, test point `tau3 i`, width-1 strip test. -/
theorem finrank_le_quadruples_dh_scaled {a : ℝ} (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (ha : 0 < a) (hV : ∀ v ∈ V, Probe a v)
    (hS : ∀ v ∈ V, ∃ K, StripTest (fun z => ghatC v a z ^ 2) K)
    (hneg : ∀ v ∈ V, v ≠ 0 → QDH a v < 0)
    (R : Finset (ZeroIdx (sqF XiDH3)))
    (hR : ∀ i, (tau3 i).im = 0 ∨ ∃ r ∈ R,
      tau3 i = tau3 r ∨ tau3 i = -tau3 r ∨ tau3 i = (starRingEnd ℂ) (tau3 r)
        ∨ tau3 i = -(starRingEnd ℂ) (tau3 r)) :
    Module.finrank ℝ V ≤ R.card :=
  finrank_le_quadruples_gen (t := tau3) (c := fun _ => 2) (fun _ => by norm_num)
    (QDH a) V ha hV hneg (fun v hv => by
      obtain ⟨K, hK⟩ := hS v hv
      simpa using QDH_hasSum (hV v hv) ha hK) R hR

end PsiOmega

#print axioms PsiOmega.dh_ne_zero_of_two_le
#print axioms PsiOmega.tau3_im_lt
#print axioms PsiOmega.XiDH_nonreal_zero
#print axioms PsiOmega.dhRH_of_realRooted
#print axioms PsiOmega.not_hypConvDH_of_realRooted
#print axioms PsiOmega.dhRHcross_of_cross
#print axioms PsiOmega.dhRH_of_cross
#print axioms PsiOmega.not_hypConvDH_of_cross
#print axioms PsiOmega.dhRHcross_of_strip
#print axioms PsiOmega.not_hypConvStripDH_of_cross
#print axioms PsiOmega.not_realRooted_limit_XiDH
#print axioms PsiOmega.tendstoLocallyUniformly_of_pairing_gen
#print axioms PsiOmega.real_of_pairing
#print axioms PsiOmega.hypConvDH_of_D
#print axioms PsiOmega.dhRH_of_D_and_realRooted_proved
#print axioms PsiOmega.not_D_and_realRooted
#print axioms PsiOmega.not_D_dh
#print axioms PsiOmega.real_of_params
#print axioms PsiOmega.real_of_dodging
#print axioms PsiOmega.not_dodging_dh
#print axioms PsiOmega.QDHu_nonneg_of_DHRHcross
#print axioms PsiOmega.not_weil_positivity_dh
#print axioms PsiOmega.weil_criterion_dh
#print axioms PsiOmega.not_GRH_dh
#print axioms PsiOmega.finrank_le_quadruples_gen
#print axioms PsiOmega.finrank_le_quadruples'
#print axioms PsiOmega.finrank_le_quadruples_dh
#print axioms PsiOmega.finrank_le_quadruples_dh_scaled
