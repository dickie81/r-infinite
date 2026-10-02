import Mathlib
import KaiserPrefactor

/-! # The prefactor with the zeros split by height (round 234)

`lam_le_kappa` (round 164) weights every zero `τ` by one bound `κ ≥ e^{2a|Im τ|}`, and without a zero-free
region the only uniform choice is `κ = eᵃ`. A zero-free region that shrinks with the height, such as
Korobov–Vinogradov's, gives a better weight only below a height `T`. This file splits the zeros there.

* **Far zeros barely see the window** (`Vz_le_int`, `sum_high_le`). For `|Re τ| > T ≥ 2` and `|x| ≤ T/2`,
  the Poisson pair satisfies `V_τ(x) ≤ (45/2)∫ g_T V_τ`, with `g_T(u) = 1/u²` on `|u| ≥ T/2`. Summing over far
  zeros and using the zero weight `Σ_τ V_τ ≤ W` gives `Σ_{far} V_τ(x) ≤ (45/2)∫ g_T W`, which is `O(T^{−1/4})`
  (`integral_gT_Wf_le`).
* **`weilQ_le_split`**: `Q(g) ≤ 4κ₁J + 4κ₂R(T)I₅₈((45/2)J + B²)`, where `κ₁` bounds the weight of the zeros
  below `T`, `κ₂` that of all zeros, `J = ∫ W‖F‖²`, `‖F(x − i)‖ ≤ B/|x|`, and
  `R(T) = 2((8 + Λ)/π)(1 + (T/2)²)^{−1/8}`.
* **`lam_le_split`**: at `T = 2e^{40a}`, `λ₁(a) ≤ K(a + 1)κ₁e^{9a − 4πe^{2a}}` for every `κ₁ ≥ 1` bounding the
  weight of the zeros with `|Re τ| ≤ 2e^{40a}`. The far zeros keep the trivial weight `eᵃ`.

`external/pnt/KaiserKV.lean` feeds the Korobov–Vinogradov region into `lam_le_split`.
-/

open Complex Filter Topology MeasureTheory Real Set

noncomputable section

namespace Kaiser

open Pilot1ca Pilot1bt

/-! ## The weight `1/u²` beyond `T/2` -/

/-- `g_T(u) = 1/u²` for `|u| ≥ T/2`, else `0`. -/
def gT (T u : ℝ) : ℝ := if T / 2 ≤ |u| then 1 / u ^ 2 else 0

theorem gT_nonneg (T u : ℝ) : 0 ≤ gT T u := by unfold gT; split_ifs <;> positivity

theorem gT_le {T : ℝ} (hT : 0 < T) (u : ℝ) : gT T u ≤ 4 / T ^ 2 := by
  unfold gT; split_ifs with h
  · have hu : 0 < |u| := by linarith
    rw [← sq_abs u, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · positivity

theorem measurable_gT (T : ℝ) : Measurable (gT T) := by
  unfold gT
  exact Measurable.ite (measurableSet_le measurable_const continuous_abs.measurable) (by fun_prop)
    measurable_const

theorem continuous_Wf : Continuous Wf := by
  unfold Wf
  exact (continuous_const.add ((Continuous.log (by fun_prop) fun x => by positivity).div_const _)).div_const _

theorem one_le_Wf (x : ℝ) : 1 ≤ Wf x := by
  unfold Wf
  have := kLam_nonneg
  have : 0 ≤ Real.log (|x| + 2) := Real.log_nonneg (by linarith [abs_nonneg x])
  rw [le_div_iff₀ pi_pos]
  linarith [pi_lt_four]

theorem integrable_gT_pk {y : ℝ} (hy : 0 < y) {T : ℝ} (hT : 0 < T) (c : ℝ) :
    Integrable fun u => gT T u * pk y (u - c) := by
  refine ((integrable_pk hy).comp_sub_right c).bdd_mul (c := 4 / T ^ 2)
    (measurable_gT T).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_of_nonneg (gT_nonneg T u)]; exact gT_le hT u

/-! ## One far zero -/

/-- **Far from its centre the Poisson kernel is small**: `P_y(x − c) ≤ 6/(πc²)` for `|x| ≤ T/2 ≤ |c|/2`. -/
theorem pk_far_le {y c x T : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 3 / 2) (hT : 0 < T) (hx : |x| ≤ T / 2)
    (hc : T ≤ |c|) : pk y (x - c) ≤ 6 / (π * c ^ 2) := by
  unfold pk
  have hc0 : c ≠ 0 := fun h => by rw [h, abs_zero] at hc; linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h1 : |c| / 2 ≤ |x - c| := by
    have := abs_sub_abs_le_abs_sub c x; rw [abs_sub_comm] at this; linarith
  have h2 : c ^ 2 / 4 ≤ (x - c) ^ 2 := by
    rw [← sq_abs (x - c), ← sq_abs c]; nlinarith [abs_nonneg c]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : y * (π * c ^ 2) ≤ 3 / 2 * (π * c ^ 2) := mul_le_mul_of_nonneg_right hy1 (by positivity)
  have h4 : π * c ^ 2 / 4 ≤ π * (x - c) ^ 2 := by nlinarith [pi_pos]
  nlinarith [pi_pos, sq_nonneg y]

/-- **The kernel's mass near its centre**: `∫ g_T(u)P_y(u − c) du ≥ 4/(15πc²)` for `|c| ≥ T ≥ 2`. -/
theorem pk_int_lower {y c T : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 3 / 2) (hT : 2 ≤ T) (hc : T ≤ |c|) :
    4 / (15 * π * c ^ 2) ≤ ∫ u, gT T u * pk y (u - c) := by
  have hy : 0 < y := by linarith
  have hc0 : c ≠ 0 := fun h => by rw [h, abs_zero] at hc; linarith
  have hc2 : 0 < c ^ 2 := by positivity
  set s := Icc (c - 1 / 2) (c + 1 / 2)
  have hint := integrable_gT_pk hy (by linarith : (0 : ℝ) < T) c
  have hlow : ∀ u ∈ s, 4 / (15 * π * c ^ 2) ≤ gT T u * pk y (u - c) := by
    intro u hu
    have hu1 : |u - c| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hua : T / 2 ≤ |u| := by
      have := abs_sub_abs_le_abs_sub c u; rw [abs_sub_comm c u] at this; linarith
    have hu0 : 0 < |u| := by linarith
    have hu2 : u ^ 2 ≤ 9 / 4 * c ^ 2 := by
      have : |u| ≤ |c| + 1 / 2 := by have := abs_sub_abs_le_abs_sub u c; linarith
      rw [← sq_abs u, ← sq_abs c]; nlinarith
    have hup : 0 < u ^ 2 := by rw [← sq_abs]; positivity
    have hg : gT T u = 1 / u ^ 2 := by simp [gT, hua]
    have hq : (u - c) ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg (u - c)]
    have hpk : 3 / (5 * π) ≤ pk y (u - c) := by
      unfold pk
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hyy : 0 ≤ (y - 1 / 6) * (3 / 2 - y) := mul_nonneg (by linarith) (by linarith)
      nlinarith [pi_pos]
    rw [hg]
    calc 4 / (15 * π * c ^ 2) = 4 / (9 * c ^ 2) * (3 / (5 * π)) := by field_simp; ring
      _ ≤ 1 / u ^ 2 * pk y (u - c) := by
          refine mul_le_mul ?_ hpk (by positivity) (by positivity)
          rw [div_le_div_iff₀ (by positivity) hup]; nlinarith
  have hs : volume s = 1 := by
    simp only [s, Real.volume_Icc]; norm_num
  have hsr : volume.real s = 1 := by rw [Measure.real, hs]; simp
  calc 4 / (15 * π * c ^ 2) = 4 / (15 * π * c ^ 2) * volume.real s := by rw [hsr, mul_one]
    _ ≤ ∫ u in s, gT T u * pk y (u - c) :=
        setIntegral_ge_of_const_le_real measurableSet_Icc (by rw [hs]; exact ENNReal.one_ne_top) hlow
          hint.integrableOn
    _ ≤ ∫ u, gT T u * pk y (u - c) :=
        setIntegral_le_integral hint
          (Eventually.of_forall fun u => mul_nonneg (gT_nonneg T u) (pk_nonneg hy.le _))

/-- **A far zero's Poisson pair on the window** is at most `45/2` times its `g_T`-average. -/
theorem Vz_le_int {τ : ℂ} (hτ : |τ.im| < 1 / 2) {T x : ℝ} (hT : 2 ≤ T) (hx : |x| ≤ T / 2)
    (hσ : T < |τ.re|) : Vz τ x ≤ 45 / 2 * ∫ u, gT T u * Vz τ u := by
  have hs := abs_lt.1 hτ
  have hσ' : T ≤ |τ.re| := hσ.le
  have hσn : T ≤ |-τ.re| := by rwa [abs_neg]
  have h1 := pk_far_le (y := 1 + τ.im) (c := τ.re) (by linarith) (by linarith) (by linarith) hx hσ'
  have h2 := pk_far_le (y := 1 - τ.im) (c := -τ.re) (by linarith) (by linarith) (by linarith) hx hσn
  have l1 := pk_int_lower (y := 1 + τ.im) (c := τ.re) (by linarith) (by linarith) hT hσ'
  have l2 := pk_int_lower (y := 1 - τ.im) (c := -τ.re) (by linarith) (by linarith) hT hσn
  simp only [sub_neg_eq_add, neg_sq] at h2 l2
  have i1 := integrable_gT_pk (y := 1 + τ.im) (by linarith) (by linarith : (0 : ℝ) < T) τ.re
  have i2 := integrable_gT_pk (y := 1 - τ.im) (by linarith) (by linarith : (0 : ℝ) < T) (-τ.re)
  simp only [sub_neg_eq_add] at i2
  have e : ∫ u, gT T u * Vz τ u = (∫ u, gT T u * pk (1 + τ.im) (u - τ.re))
      + ∫ u, gT T u * pk (1 - τ.im) (u + τ.re) := by
    rw [← integral_add i1 i2]; congr 1; funext u; simp only [Vz]; ring
  rw [e]
  have hc0 : τ.re ≠ 0 := fun h => by rw [h, abs_zero] at hσ; linarith
  have e2 : 45 / 2 * (4 / (15 * π * τ.re ^ 2)) = 6 / (π * τ.re ^ 2) := by field_simp; ring
  unfold Vz
  linarith

/-! ## All far zeros -/

theorem integrable_gT_Wf {T : ℝ} (hT : 2 ≤ T) : Integrable fun u => gT T u * Wf u := by
  refine (integrable_rho58.const_mul (2 * ((8 + kLam) / π) * (1 + (T / 2) ^ 2) ^ (-(1 / 8 : ℝ)))).mono'
    ((measurable_gT T).aestronglyMeasurable.mul continuous_Wf.aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (gT_nonneg T u) (Wf_nonneg u))]
  unfold gT
  split_ifs with h
  · rw [one_div_mul_eq_div]; exact Wf_tail_le (by linarith) h
  · rw [zero_mul]
    have := kLam_nonneg
    have : 0 ≤ rho58 u := by unfold rho58; positivity
    positivity

/-- `∫ g_T W ≤ 2((8 + Λ)/π)(1 + (T/2)²)^{−1/8} I₅₈`. -/
theorem integral_gT_Wf_le {T : ℝ} (hT : 2 ≤ T) :
    ∫ u, gT T u * Wf u ≤ 2 * ((8 + kLam) / π) * (1 + (T / 2) ^ 2) ^ (-(1 / 8 : ℝ)) * I58 := by
  rw [I58, ← integral_const_mul]
  refine integral_mono (integrable_gT_Wf hT) (integrable_rho58.const_mul _) fun u => ?_
  unfold gT
  split_ifs with h
  · rw [one_div_mul_eq_div]; exact Wf_tail_le (by linarith) h
  · rw [zero_mul]
    have := kLam_nonneg
    have : 0 ≤ rho58 u := by unfold rho58; positivity
    positivity

/-- The far-zero constant `E_T = (45/2)·2((8 + Λ)/π)(1 + (T/2)²)^{−1/8} I₅₈`. -/
def ET (T : ℝ) : ℝ := 45 / 2 * (2 * ((8 + kLam) / π) * (1 + (T / 2) ^ 2) ^ (-(1 / 8 : ℝ)) * I58)

theorem ET_nonneg (T : ℝ) : 0 ≤ ET T := by
  unfold ET; have := kLam_nonneg; have := I58_nonneg; positivity

/-- **The far zeros on the window**: for any finite set `S` of zeros with `|Re τ| > T` and `|x| ≤ T/2`,
`Σ_S V_τ(x) ≤ E_T`. -/
theorem sum_high_le {T x : ℝ} (hT : 2 ≤ T) (hx : |x| ≤ T / 2) (S : Finset (ZeroIdx (sqF Xi)))
    (hS : ∀ i ∈ S, T < |(tau i).re|) : ∑ i ∈ S, Vz (tau i) x ≤ ET T := by
  have hint : ∀ i ∈ S, Integrable fun u => gT T u * Vz (tau i) u := by
    intro i _
    have hs := abs_lt.1 (tau_im i)
    have i1 := integrable_gT_pk (y := 1 + (tau i).im) (by linarith) (by linarith : (0 : ℝ) < T) (tau i).re
    have i2 := integrable_gT_pk (y := 1 - (tau i).im) (by linarith) (by linarith : (0 : ℝ) < T) (-(tau i).re)
    simp only [sub_neg_eq_add] at i2
    refine (i1.add i2).congr (ae_of_all _ fun u => ?_)
    simp only [Pi.add_apply, Vz, mul_add]
  calc ∑ i ∈ S, Vz (tau i) x ≤ ∑ i ∈ S, 45 / 2 * ∫ u, gT T u * Vz (tau i) u :=
        Finset.sum_le_sum fun i hi => Vz_le_int (tau_im i) hT hx (hS i hi)
    _ = 45 / 2 * ∫ u, gT T u * ∑ i ∈ S, Vz (tau i) u := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ hint]
        congr 2; funext u; rw [Finset.mul_sum]
    _ ≤ 45 / 2 * ∫ u, gT T u * Wf u := by
        refine mul_le_mul_of_nonneg_left (integral_mono ?_ (integrable_gT_Wf hT) fun u => ?_) (by norm_num)
        · exact (integrable_finsetSum _ hint).congr (ae_of_all _ fun u => by
            simp only [Finset.mul_sum])
        · refine mul_le_mul_of_nonneg_left ?_ (gT_nonneg T u)
          refine le_trans ?_ (tsum_Vz_le u)
          exact (hasSum_Vz u).summable.sum_le_tsum S (fun i _ => Vz_nonneg (tau_im i) u)
    _ ≤ ET T := by
        unfold ET; exact mul_le_mul_of_nonneg_left (integral_gT_Wf_le hT) (by norm_num)

/-! ## The split bound on `Q` -/

section Split

variable {L η α : ℝ} (ht : Tail L η α) {a : ℝ} (hLa : Real.exp a = L)
include ht hLa

theorem integrable_Vz_F (i : ZeroIdx (sqF Xi)) :
    Integrable fun x => Vz (tau i) x * ‖FT (PsiK L η α a) x‖ ^ 2 := by
  have hs := abs_lt.1 (tau_im i)
  have i1 := integrable_pk_FT ht hLa (by linarith : 0 < 1 + (tau i).im) (tau i).re
  have i2 := integrable_pk_FT ht hLa (by linarith : 0 < 1 - (tau i).im) (-(tau i).re)
  simp only [sub_neg_eq_add] at i2
  refine (i1.add i2).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Vz, add_mul]

theorem sum_int_Vz (S : Finset (ZeroIdx (sqF Xi))) :
    ∑ i ∈ S, ∫ x, Vz (tau i) x * ‖FT (PsiK L η α a) x‖ ^ 2
      = ∫ x, (∑ i ∈ S, Vz (tau i) x) * ‖FT (PsiK L η α a) x‖ ^ 2 := by
  rw [← integral_finsetSum _ fun i _ => integrable_Vz_F ht hLa i]
  congr 1; funext x; rw [Finset.sum_mul]

/-- **The zero side with the zeros split at height `T`.** -/
theorem weilQ_le_split (hint : ∫ x, Hr L η α x = 0) (ha : 0 < a) {κ₁ κ₂ T B : ℝ} (hκ₁0 : 0 ≤ κ₁)
    (hκ₂0 : 0 ≤ κ₂) (hT : 2 ≤ T)
    (hκ₁ : ∀ i : ZeroIdx (sqF Xi), |(tau i).re| ≤ T → Real.exp (2 * a * |(tau i).im|) ≤ κ₁)
    (hκ₂ : ∀ i : ZeroIdx (sqF Xi), Real.exp (2 * a * |(tau i).im|) ≤ κ₂)
    (hW : Integrable fun x => Wf x * ‖FT (PsiK L η α a) x‖ ^ 2)
    (hB : ∀ x : ℝ, x ≠ 0 → ‖FT (PsiK L η α a) x‖ ≤ B / |x|) :
    weilQ a (gK L η α a) ≤ 4 * κ₁ * (∫ x, Wf x * ‖FT (PsiK L η α a) x‖ ^ 2)
      + 4 * κ₂ * (ET T * (∫ x, Wf x * ‖FT (PsiK L η α a) x‖ ^ 2)
        + B ^ 2 * (2 * ((8 + kLam) / π) * (1 + (T / 2) ^ 2) ^ (-(1 / 8 : ℝ))) * I58) := by
  classical
  have hp := ht.par
  set F := FT (PsiK L η α a)
  set J := ∫ x, Wf x * ‖F x‖ ^ 2
  set R := 2 * ((8 + kLam) / π) * (1 + (T / 2) ^ 2) ^ (-(1 / 8 : ℝ))
  have hR : 0 ≤ R := by have := kLam_nonneg; positivity
  have hE := ET_nonneg T
  have H := weilQ_eq_zero_sum (probe_gK hp hint ha.le) ha (weilExplicit_gK hp hint ha)
  have Hre := Complex.hasSum_re H
  simp only [Complex.ofReal_re] at Hre
  set Iz : ZeroIdx (sqF Xi) → ℝ := fun i => ∫ x, Vz (tau i) x * ‖F x‖ ^ 2
  have hV0 : ∀ i x, 0 ≤ Vz (tau i) x * ‖F x‖ ^ 2 := fun i x =>
    mul_nonneg (Vz_nonneg (tau_im i) x) (sq_nonneg _)
  have hI0 : ∀ i, 0 ≤ Iz i := fun i => integral_nonneg fun x => hV0 i x
  set c : ZeroIdx (sqF Xi) → ℝ := fun i =>
    2 * κ₁ * Iz i + 2 * κ₂ * (if T < |(tau i).re| then Iz i else 0)
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    have := hI0 i; simp only [c]; split_ifs <;> positivity
  -- each term
  have hterm : ∀ p : Bool × ZeroIdx (sqF Xi),
      (ghatC (gK L η α a) a ((rhoXi p - 1 / 2) / I) ^ 2).re ≤ c p.2 := by
    intro p
    set t := (rhoXi p - 1 / 2) / I
    have hpair := ghat_sq_le_pair ht hLa hint ha (im_rhoXi p) (Xi_rhoXi p)
    have hV : (fun x => Vz t x * ‖F x‖ ^ 2) = fun x => Vz (tau p.2) x * ‖F x‖ ^ 2 := by
      funext x; simp only [t, ordinate_rhoXi]; split_ifs
      · rfl
      · rw [Vz_neg]
    have hIm : |t.im| = |(tau p.2).im| := by
      simp only [t, ordinate_rhoXi]; split_ifs
      · rfl
      · rw [neg_im, abs_neg]
    rw [hV, hIm] at hpair
    have hk : Real.exp (2 * a * |(tau p.2).im|) * Iz p.2 ≤ κ₁ * Iz p.2
        + κ₂ * (if T < |(tau p.2).re| then Iz p.2 else 0) := by
      have := hI0 p.2
      split_ifs with h
      · nlinarith [hκ₂ p.2]
      · nlinarith [hκ₁ p.2 (not_lt.1 h)]
    calc (ghatC (gK L η α a) a t ^ 2).re ≤ ‖ghatC (gK L η α a) a t ^ 2‖ := Complex.re_le_norm _
      _ = ‖ghatC (gK L η α a) a t‖ ^ 2 := norm_pow _ _
      _ ≤ 2 * Real.exp (2 * a * |(tau p.2).im|) * Iz p.2 := hpair
      _ ≤ c p.2 := by simp only [c]; nlinarith
  -- the far zeros, pointwise and integrated
  have hfar : ∀ S : Finset (ZeroIdx (sqF Xi)), (∀ i ∈ S, T < |(tau i).re|) →
      ∑ i ∈ S, Iz i ≤ ET T * J + B ^ 2 * R * I58 := by
    intro S hS
    rw [sum_int_Vz ht hLa]
    have hpt : ∀ x, (∑ i ∈ S, Vz (tau i) x) * ‖F x‖ ^ 2 ≤ ET T * (Wf x * ‖F x‖ ^ 2) + B ^ 2 * R * rho58 x := by
      intro x
      have hF := sq_nonneg ‖F x‖
      have hr : 0 ≤ rho58 x := by unfold rho58; positivity
      have hS0' : 0 ≤ ∑ i ∈ S, Vz (tau i) x := Finset.sum_nonneg fun i _ => Vz_nonneg (tau_im i) x
      rcases le_or_gt |x| (T / 2) with hx | hx
      · have h1 := sum_high_le hT hx S hS
        have h2 : ET T ≤ ET T * Wf x := le_mul_of_one_le_right hE (one_le_Wf x)
        have : (∑ i ∈ S, Vz (tau i) x) * ‖F x‖ ^ 2 ≤ ET T * Wf x * ‖F x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hF
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg B) hR) hr]
      · have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
        have hxa : 0 < |x| := abs_pos.2 hx0
        have hSW : ∑ i ∈ S, Vz (tau i) x ≤ Wf x :=
          ((hasSum_Vz x).summable.sum_le_tsum S (fun i _ => Vz_nonneg (tau_im i) x)).trans (tsum_Vz_le x)
        have hFB : ‖F x‖ ^ 2 ≤ B ^ 2 / x ^ 2 := by
          rw [← sq_abs x, ← div_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hB x hx0) 2
        have hWt := Wf_tail_le (x := x) (M := T / 2) (by linarith) hx.le
        have h3 : (∑ i ∈ S, Vz (tau i) x) * ‖F x‖ ^ 2 ≤ B ^ 2 * R * rho58 x :=
          calc (∑ i ∈ S, Vz (tau i) x) * ‖F x‖ ^ 2 ≤ Wf x * (B ^ 2 / x ^ 2) :=
                mul_le_mul hSW hFB hF (Wf_nonneg x)
            _ = B ^ 2 * (Wf x / x ^ 2) := by ring
            _ ≤ B ^ 2 * (R * rho58 x) := mul_le_mul_of_nonneg_left hWt (sq_nonneg B)
            _ = B ^ 2 * R * rho58 x := by ring
        nlinarith [mul_nonneg hE (mul_nonneg (Wf_nonneg x) hF)]
    calc ∫ x, (∑ i ∈ S, Vz (tau i) x) * ‖F x‖ ^ 2
        ≤ ∫ x, (ET T * (Wf x * ‖F x‖ ^ 2) + B ^ 2 * R * rho58 x) := by
          refine integral_mono ?_ ((hW.const_mul _).add (integrable_rho58.const_mul _)) hpt
          refine (integrable_finsetSum S fun i _ => integrable_Vz_F ht hLa i).congr
            (ae_of_all _ fun x => ?_)
          simp only [Finset.sum_mul]
          rfl
      _ = ET T * J + B ^ 2 * R * I58 := by
          rw [integral_add (hW.const_mul _) (integrable_rho58.const_mul _), integral_const_mul,
            integral_const_mul, I58]
  -- all zeros
  have hall : ∀ S : Finset (ZeroIdx (sqF Xi)), ∑ i ∈ S, Iz i ≤ J := by
    intro S
    rw [sum_int_Vz ht hLa]
    refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hW (ae_of_all _ fun x => ?_)
    · exact mul_nonneg (Finset.sum_nonneg fun i _ => Vz_nonneg (tau_im i) x) (sq_nonneg _)
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact ((hasSum_Vz x).summable.sum_le_tsum S (fun i _ => Vz_nonneg (tau_im i) x)).trans (tsum_Vz_le x)
  have hfin : ∀ S : Finset (ZeroIdx (sqF Xi)),
      ∑ i ∈ S, c i ≤ 2 * κ₁ * J + 2 * κ₂ * (ET T * J + B ^ 2 * R * I58) := by
    intro S
    have e : ∑ i ∈ S, c i = 2 * κ₁ * ∑ i ∈ S, Iz i
        + 2 * κ₂ * ∑ i ∈ S.filter (fun i => T < |(tau i).re|), Iz i := by
      simp only [c, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter]
    rw [e]
    have h1 := hall S
    have h2 := hfar (S.filter fun i => T < |(tau i).re|) fun i hi => (Finset.mem_filter.1 hi).2
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * κ₁)
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * κ₂)
    linarith
  rw [← Hre.tsum_eq]
  refine Hre.summable.tsum_le_of_sum_le fun S => ?_
  set T' := S.image Prod.snd
  calc ∑ p ∈ S, (ghatC (gK L η α a) a ((rhoXi p - 1 / 2) / I) ^ 2).re ≤ ∑ p ∈ S, c p.2 :=
        Finset.sum_le_sum fun p _ => hterm p
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ T', c p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => by
          simp only [Finset.mem_product, Finset.mem_univ, true_and, T']
          exact Finset.mem_image_of_mem _ hp) (fun p _ _ => hc0 p.2)
    _ = 2 * ∑ i ∈ T', c i := by
        rw [Finset.sum_product]; simp [Finset.sum_const]
    _ ≤ 2 * (2 * κ₁ * J + 2 * κ₂ * (ET T * J + B ^ 2 * R * I58)) := by gcongr; exact hfin T'
    _ = _ := by ring

end Split

/-! ## The ground energy -/

/-- **`λ₁` with the zeros split at `2e^{40a}`**: if `κ₁ ≥ 1` bounds `e^{2a|Im τ|}` at every zero with
`|Re τ| ≤ 2e^{40a}`, then `λ₁(a) ≤ K(a + 1)κ₁e^{9a − 4πe^{2a}}`; the zeros above keep weight `eᵃ`. -/
theorem lam_le_split : ∃ K, 0 ≤ K ∧ ∀ a, 4 ≤ a → ∀ κ₁, 1 ≤ κ₁ →
    (∀ i : ZeroIdx (sqF Xi), |(tau i).re| ≤ 2 * Real.exp (40 * a) →
      Real.exp (2 * a * |(tau i).im|) ≤ κ₁) →
    lam a ≤ K * (a + 1) * κ₁ * Real.exp (9 * a - 4 * π * Real.exp (2 * a)) := by
  obtain ⟨C, hC, hlam⟩ := lam_le_of_weilQ
  have hKz := Kz_nonneg
  have hk := kLam_nonneg
  have hI := I58_nonneg
  obtain ⟨c₁, hc₁def⟩ : ∃ c : ℝ, c = 2 * ((8 + kLam) / π) := ⟨_, rfl⟩
  have hc₁ : 0 ≤ c₁ := by rw [hc₁def]; positivity
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = 4 * (45 / 2 * c₁ * I58 * 4 * Kz) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = 4 * (1638400 * c₁ * I58) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  refine ⟨C * (16 * Kz + X + Y), by positivity, fun a ha κ₁ hκ₁1 hκ₁ => ?_⟩
  have ha0 : 0 < a := by linarith
  obtain ⟨ht, hint, hW, hJ, B, hB2, hB⟩ := prefactor_data ha
  have hT2 : (2 : ℝ) ≤ 2 * Real.exp (40 * a) := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 40 * a); linarith
  have hκ₂ : ∀ i : ZeroIdx (sqF Xi), Real.exp (2 * a * |(tau i).im|) ≤ Real.exp a := fun i =>
    Real.exp_le_exp.2 (by nlinarith [tau_im i, abs_nonneg (tau i).im])
  have hQ := weilQ_le_split ht rfl hint ha0 (by linarith) (Real.exp_pos a).le hT2 hκ₁ hκ₂ hW hB
  rw [← hc₁def] at hQ
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ, J = ∫ x, Wf x * ‖FT (PsiK (Real.exp a) (1 / Real.exp a) (kα (Real.exp a)) a) x‖ ^ 2 :=
    ⟨_, rfl⟩
  rw [← hJdef] at hQ hJ
  have hJ0 : 0 ≤ J := by rw [hJdef]; exact integral_nonneg fun x => mul_nonneg (Wf_nonneg x) (sq_nonneg _)
  obtain ⟨rp, hrpdef⟩ : ∃ r : ℝ, r = (1 + (2 * Real.exp (40 * a) / 2) ^ 2) ^ (-(1 / 8 : ℝ)) := ⟨_, rfl⟩
  have hrp0 : 0 ≤ rp := by rw [hrpdef]; positivity
  have hrp : rp ≤ Real.exp (-(10 * a)) := by
    rw [hrpdef, show 2 * Real.exp (40 * a) / 2 = Real.exp (40 * a) by ring]
    have h1 : (1 + Real.exp (40 * a) ^ 2) ^ (-(1 / 8 : ℝ)) ≤ (Real.exp (40 * a) ^ 2) ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have h2 : (Real.exp (40 * a) ^ 2) ^ (-(1 / 8 : ℝ)) = Real.exp (-(10 * a)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_mul]; congr 1; push_cast; ring
    rw [← h2]; exact h1
  have hET : ET (2 * Real.exp (40 * a)) = 45 / 2 * (c₁ * rp * I58) := by
    rw [ET, hc₁def, hrpdef]
  rw [hET, ← hrpdef] at hQ
  -- exponentials
  set E := Real.exp (-(10 * a))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hea : Real.exp a * E * Real.exp (9 * a) = 1 := by
    simp only [E]; rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  have hea2 : Real.exp a * E * Real.exp (18 * a) = Real.exp (9 * a) := by
    simp only [E]; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have he9 : 1 ≤ Real.exp (9 * a) := Real.one_le_exp (by linarith)
  have hea0 : 0 ≤ Real.exp a := (Real.exp_pos a).le
  -- the far part
  have hfar1 : Real.exp a * (45 / 2 * (c₁ * rp * I58) * J)
      ≤ 45 / 2 * c₁ * I58 * 4 * Kz * (a + 1) * (Real.exp a * E * Real.exp (9 * a)) := by
    have h1 : c₁ * rp * I58 ≤ c₁ * E * I58 := by gcongr
    have h2 : 45 / 2 * (c₁ * rp * I58) * J ≤ 45 / 2 * (c₁ * E * I58) * (4 * Kz * (a + 1) * Real.exp (9 * a)) := by
      gcongr
    calc Real.exp a * (45 / 2 * (c₁ * rp * I58) * J)
        ≤ Real.exp a * (45 / 2 * (c₁ * E * I58) * (4 * Kz * (a + 1) * Real.exp (9 * a))) := by gcongr
      _ = _ := by ring
  have hfar2 : Real.exp a * (B ^ 2 * (c₁ * rp) * I58)
      ≤ 1638400 * c₁ * I58 * (Real.exp a * E * Real.exp (18 * a)) := by
    calc Real.exp a * (B ^ 2 * (c₁ * rp) * I58)
        ≤ Real.exp a * (1638400 * Real.exp (18 * a) * (c₁ * E) * I58) := by gcongr
      _ = _ := by ring
  rw [hea] at hfar1
  rw [hea2] at hfar2
  have hmain : 4 * κ₁ * J ≤ 16 * Kz * (κ₁ * ((a + 1) * Real.exp (9 * a))) := by
    have := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ 4 * κ₁)
    calc 4 * κ₁ * J ≤ 4 * κ₁ * (4 * Kz * (a + 1) * Real.exp (9 * a)) := this
      _ = _ := by ring
  have ha1 : 0 ≤ a + 1 := by linarith
  have hA : 0 ≤ (a + 1) * Real.exp (9 * a) := by positivity
  have hXb : 4 * (45 / 2 * c₁ * I58 * 4 * Kz * (a + 1) * 1) ≤ X * (κ₁ * ((a + 1) * Real.exp (9 * a))) := by
    have h1 : a + 1 ≤ κ₁ * ((a + 1) * Real.exp (9 * a)) :=
      (le_mul_of_one_le_right ha1 he9).trans (le_mul_of_one_le_left hA hκ₁1)
    calc 4 * (45 / 2 * c₁ * I58 * 4 * Kz * (a + 1) * 1) = X * (a + 1) := by rw [hXdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hX0
  have hYb : 4 * (1638400 * c₁ * I58 * Real.exp (9 * a)) ≤ Y * (κ₁ * ((a + 1) * Real.exp (9 * a))) := by
    have h1 : Real.exp (9 * a) ≤ κ₁ * ((a + 1) * Real.exp (9 * a)) :=
      (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith : (1 : ℝ) ≤ a + 1)).trans
        (le_mul_of_one_le_left hA hκ₁1)
    calc 4 * (1638400 * c₁ * I58 * Real.exp (9 * a)) = Y * Real.exp (9 * a) := by rw [hYdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hY0
  have hq : weilQ a (gK (Real.exp a) (1 / Real.exp a) (kα (Real.exp a)) a)
      ≤ (16 * Kz + X + Y) * (κ₁ * ((a + 1) * Real.exp (9 * a))) := by
    have e : 4 * Real.exp a * (45 / 2 * (c₁ * rp * I58) * J + B ^ 2 * (c₁ * rp) * I58)
        = 4 * (Real.exp a * (45 / 2 * (c₁ * rp * I58) * J)) + 4 * (Real.exp a * (B ^ 2 * (c₁ * rp) * I58)) := by
      ring
    rw [e] at hQ
    linarith
  have hq0 : 0 ≤ (16 * Kz + X + Y) * (κ₁ * ((a + 1) * Real.exp (9 * a))) := by
    have : 0 ≤ κ₁ := by linarith
    positivity
  refine (hlam a ha _ hq0 hq).trans (le_of_eq ?_)
  rw [sub_eq_add_neg, Real.exp_add]; ring

end Kaiser

#print axioms Kaiser.Vz_le_int
#print axioms Kaiser.sum_high_le
#print axioms Kaiser.weilQ_le_split
#print axioms Kaiser.lam_le_split
