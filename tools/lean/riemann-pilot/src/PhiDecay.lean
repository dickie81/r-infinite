import Mathlib
import PhiNull
import CosTrunc

/-! # The ground energy of Weil's form decays faster than every exponential (round 133)

Riemann's kernel `Φ` is a null vector of the explicit formula (round 132, `Φ̂ = Ξ/2`). Its truncation
`Φ_a = 1_{[−a,a]}Φ` is an admissible probe, and its transform at a zero `t` of `Ξ` is minus a tail:

* **A–B**: `Φ` is `C¹` with `Φ' = Σ φ_n'` (`hasDerivAt_RPhi`), `Φ'` is odd and decays at every
  exponential rate (`RPhi1_decay`);
* **C**: `Φ_a` is a probe (`probe_PhiA`, via `ind_energy` and the Lipschitz bound `RPhi_lip`);
* **D**: on `|Im t| ≤ ½`, `∫f e^{itu} = ĝ_a(t) + tail` and `‖tail‖ ≤ C e^{−(D−3/2)a}∫e^{−|u|}`;
* **E**: at `Ξ(t) = 0`: `ĝ(t) = −tail Φ` and, integrating by parts on `[−a, a]` and on `ℝ`
  (`∫Φ'e^{itu} = −itΦ̂(t) = 0`), `‖t‖‖ĝ(t)‖ ≤ 2|Φ(a)|e^{a/2} + ‖tail Φ'‖` (`zero_bounds`);
* **F**: summing with the weight `‖1/(t² + 4)‖`: `Q(Φ_a) ≤ (τ₁² + 4τ₀²) Σ_ρ ‖1/(t_ρ² + 4)‖`;
* **G**: `λ₁(a)‖Φ_a‖² ≤ Q(Φ_a)`, `‖Φ_a‖² ≥ ‖Φ_1‖² > 0`, so **`λ₁(a) ≤ K_B e^{−Ba}` for every `B`**
  (`lam_decay`; over the zeros of `ζ`, `lam_decay_zeta`).

Named input: `WeilExplicit` for each `Φ_a` and for `1/(z² + 4)` (`DigammaDiff` is proved, round
154). The bound holds for every zero family on which `Ξ` vanishes inside the strip, on or off the critical line: it is an
upper bound on `λ₁`, and RH is the lower bound `λ₁ ≥ 0`. No bearing on RH.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace Pilot1ca

open Pilot1bt

/-! ## A. The derivative of Riemann's kernel -/

/-- `φ_n'(u) = (−4q³ + 15q² − 15q/2) e^{u/2 − q}`, `q = πn²e^{2u}`. -/
def phiT1 (n : ℕ) (u : ℝ) : ℝ :=
  (-4 * (thC n * Real.exp (2 * u)) ^ 3 + 15 * (thC n * Real.exp (2 * u)) ^ 2
    - 15 / 2 * (thC n * Real.exp (2 * u))) * thF n u

theorem hasDerivAt_phiT (n : ℕ) (u : ℝ) : HasDerivAt (phiT n) (phiT1 n u) u := by
  have hq := (hasDerivAt_exp_two u).const_mul (thC n)
  have hp := ((hq.pow 2).const_mul 2).sub (hq.const_mul 3)
  have := hp.mul (hasDerivAt_thF n u)
  have e : phiT n = fun v => (2 * (thC n * Real.exp (2 * v)) ^ 2 - 3 * (thC n * Real.exp (2 * v)))
      * thF n v := by
    funext v; unfold phiT thF
    rw [show Real.exp (4 * v) = Real.exp (2 * v) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]; ring
  rw [e]
  convert this using 1
  simp only [Pi.sub_apply, Pi.pow_apply]; unfold phiT1 thF1; ring

theorem phiT1_zero (u : ℝ) : phiT1 0 u = 0 := by simp [phiT1, thC]

/-- The majorant `K (1 + n²)³ e^{−rn}`. -/
def thMaj3 (K r : ℝ) (n : ℕ) : ℝ := K * ((1 + (n : ℝ) ^ 2) ^ 3 * Real.exp (-r * n))

theorem summable_thMaj3 (K : ℝ) {r : ℝ} (hr : 0 < r) : Summable (thMaj3 K r) := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hr
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 hr
  have h4 := Real.summable_pow_mul_exp_neg_nat_mul 4 hr
  have h6 := Real.summable_pow_mul_exp_neg_nat_mul 6 hr
  refine ((((h0.add (h2.mul_left 3)).add (h4.mul_left 3)).add h6).mul_left K).congr fun n => ?_
  simp only [thMaj3, pow_zero, one_mul]; ring

theorem phiT1_le {R u : ℝ} (hu : |u| ≤ R) (n : ℕ) :
    |phiT1 n u| ≤ thMaj3 (27 * (1 + π * Real.exp (2 * R)) ^ 3 * Real.exp (R / 2))
      (π * Real.exp (-2 * R)) n := by
  set q := thC n * Real.exp (2 * u)
  set Q := π * Real.exp (2 * R)
  obtain ⟨hq0, hq⟩ := thq_le hu n
  have hQ : 0 ≤ Q := by positivity
  have hf := thF_le hu n
  have hf0 : 0 ≤ thF n u := (Real.exp_pos _).le
  have h1 : 1 + q ≤ (1 + Q) * (1 + (n : ℝ) ^ 2) := by nlinarith [sq_nonneg (n : ℝ)]
  have h3 : (1 + q) ^ 3 ≤ ((1 + Q) * (1 + (n : ℝ) ^ 2)) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
  have hp : |-4 * q ^ 3 + 15 * q ^ 2 - 15 / 2 * q| ≤ 27 * (1 + q) ^ 3 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg q, mul_nonneg hq0 (sq_nonneg q)]
  unfold phiT1
  rw [abs_mul, abs_of_nonneg hf0]
  calc |-4 * q ^ 3 + 15 * q ^ 2 - 15 / 2 * q| * thF n u
      ≤ (27 * ((1 + Q) * (1 + (n : ℝ) ^ 2)) ^ 3)
        * (Real.exp (R / 2) * Real.exp (-(π * Real.exp (-2 * R)) * n)) :=
        mul_le_mul (hp.trans (by linarith)) hf hf0 (by positivity)
    _ = _ := by simp only [thMaj3, Q]; ring

theorem thMaj3_summable_at (y : ℝ) :
    Summable (thMaj3 (27 * (1 + π * Real.exp (2 * (|y| + 1))) ^ 3 * Real.exp ((|y| + 1) / 2))
      (π * Real.exp (-2 * (|y| + 1)))) :=
  summable_thMaj3 _ (by positivity)

theorem summable_phiT1 (u : ℝ) : Summable fun n => phiT1 n u :=
  Summable.of_norm_bounded (thMaj3_summable_at u) fun n => by
    rw [Real.norm_eq_abs]; exact phiT1_le (show |u| ≤ |u| + 1 by linarith) n

/-- `Φ'`. -/
def RPhi1 (u : ℝ) : ℝ := ∑' n : ℕ, phiT1 n u

theorem hasDerivAt_RPhi (y : ℝ) : HasDerivAt RPhi (RPhi1 y) y :=
  hasDerivAt_tsum_of_isPreconnected (thMaj3_summable_at y) isOpen_Ioo isPreconnected_Ioo
    (fun n v _ => hasDerivAt_phiT n v)
    (fun n v hv => by rw [Real.norm_eq_abs]; exact phiT1_le (abs_le_of_mem_Ioo hv) n)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith) (summable_phiT y)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)

theorem continuous_RPhi1 : Continuous RPhi1 := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc : ContinuousOn RPhi1 (Ioo (y - 1) (y + 1)) :=
    continuousOn_tsum (fun n => by unfold phiT1 thF; fun_prop) (thMaj3_summable_at y)
      (fun n v hv => by rw [Real.norm_eq_abs]; exact phiT1_le (abs_le_of_mem_Ioo hv) n)
  exact hc.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

theorem RPhi1_odd (u : ℝ) : RPhi1 (-u) = -RPhi1 u := by
  have h1 : HasDerivAt (fun v => RPhi (-v)) (-RPhi1 (-u)) u := by
    have := (hasDerivAt_RPhi (-u)).comp u (hasDerivAt_neg u)
    convert this using 1
    · funext v; simp [Function.comp]
    · ring
  have e : (fun v => RPhi (-v)) = RPhi := funext RPhi_even
  rw [e] at h1
  have := h1.unique (hasDerivAt_RPhi u)
  linarith

/-! ## B. Decay of `Φ'` -/

/-- `X^k e^{u/2} e^{−πX/2} ≤ K e^{−Bu}` for `X = e^{2u}`, `u ≥ 0`. -/
theorem exp_poly_decay (k : ℕ) (B : ℝ) : ∃ K, 0 ≤ K ∧ ∀ u, 0 ≤ u →
    Real.exp (2 * u) ^ k * Real.exp (u / 2) * Real.exp (-(π / 2) * Real.exp (2 * u))
      ≤ K * Real.exp (-B * u) := by
  set m' := ⌈B / 2⌉₊
  set m := k + 1 + m'
  set K : ℝ := (m.factorial : ℝ) * (2 / π) ^ m
  refine ⟨K, by positivity, fun u hu => ?_⟩
  set X := Real.exp (2 * u)
  have hX : 1 ≤ X := by simp only [X]; exact Real.one_le_exp (by linarith)
  have hu2 : Real.exp (u / 2) ≤ X := Real.exp_le_exp.2 (by linarith)
  have hBu : Real.exp (B * u) ≤ X ^ m' := by
    have hm : B ≤ 2 * m' := by
      have := Nat.le_ceil (B / 2); linarith
    simp only [X]; rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hE : X ^ m * Real.exp (-(π / 2) * X) ≤ K := by
    have h4 := Real.pow_div_factorial_le_exp (π / 2 * X) (by positivity) m
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hf] at h4
    have hpe : Real.exp (-(π / 2) * X) * Real.exp (π / 2 * X) = 1 := by
      rw [← Real.exp_add]; simp
    have hq : X ^ m = (π / 2 * X) ^ m * (2 / π) ^ m := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hq]
    calc (π / 2 * X) ^ m * (2 / π) ^ m * Real.exp (-(π / 2) * X)
        ≤ Real.exp (π / 2 * X) * m.factorial * (2 / π) ^ m * Real.exp (-(π / 2) * X) := by
          gcongr
      _ = (m.factorial : ℝ) * (2 / π) ^ m * (Real.exp (-(π / 2) * X) * Real.exp (π / 2 * X)) := by
          ring
      _ = K := by rw [hpe, mul_one]
  have hBd : X ^ k * Real.exp (u / 2) * Real.exp (-(π / 2) * X) * Real.exp (B * u) ≤ K := by
    have e : X ^ m = X ^ k * X * X ^ m' := by simp only [m]; ring
    calc X ^ k * Real.exp (u / 2) * Real.exp (-(π / 2) * X) * Real.exp (B * u)
        = X ^ k * Real.exp (u / 2) * Real.exp (B * u) * Real.exp (-(π / 2) * X) := by ring
      _ ≤ X ^ k * X * X ^ m' * Real.exp (-(π / 2) * X) := by gcongr
      _ = X ^ m * Real.exp (-(π / 2) * X) := by rw [e]
      _ ≤ K := hE
  have hinv : Real.exp (B * u) * Real.exp (-B * u) = 1 := by rw [← Real.exp_add]; simp
  calc X ^ k * Real.exp (u / 2) * Real.exp (-(π / 2) * X)
      = X ^ k * Real.exp (u / 2) * Real.exp (-(π / 2) * X) * Real.exp (B * u) * Real.exp (-B * u) := by
        rw [mul_assoc _ (Real.exp (B * u)), hinv, mul_one]
    _ ≤ K * Real.exp (-B * u) := mul_le_mul_of_nonneg_right hBd (Real.exp_pos _).le

/-- The coefficient of the per-term bound for `φ_n'`. -/
def coef1 (n : ℕ) : ℝ :=
  (4 * π ^ 3 * (n : ℝ) ^ 6 + 15 * π ^ 2 * (n : ℝ) ^ 4 + 8 * π * (n : ℝ) ^ 2)
    * Real.exp (-(π / 2) * (n : ℝ) ^ 2)

theorem phiT1_le_pos {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |phiT1 n u| ≤ coef1 n
      * (Real.exp (2 * u) ^ 3 * Real.exp (u / 2) * Real.exp (-(π / 2) * Real.exp (2 * u))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [phiT1_zero, coef1]
  set X := Real.exp (2 * u)
  have hX : 1 ≤ X := by simp only [X]; exact Real.one_le_exp (by linarith)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  unfold phiT1 thF thC coef1
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (u / 2 - π * (n : ℝ) ^ 2 * X)
      ≤ Real.exp (u / 2) * (Real.exp (-(π / 2) * (n : ℝ) ^ 2) * Real.exp (-(π / 2) * X)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : ((n : ℝ) ^ 2 - 1 / 2) * (X - 1 / 2) ≥ 1 / 4 := by nlinarith
    nlinarith [pi_pos]
  set c := π * (n : ℝ) ^ 2
  have hc : 0 ≤ c := by positivity
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hpoly : |-4 * (c * X) ^ 3 + 15 * (c * X) ^ 2 - 15 / 2 * (c * X)|
      ≤ (4 * c ^ 3 + 15 * c ^ 2 + 8 * c) * X ^ 3 := by
    have a1 : 0 ≤ c * X := by positivity
    have a2 : c * X ≤ c * X ^ 3 := mul_le_mul_of_nonneg_left (hX2.trans hX3) hc
    have a3 : c ^ 2 * X ^ 2 ≤ c ^ 2 * X ^ 3 := mul_le_mul_of_nonneg_left hX3 (sq_nonneg c)
    rw [abs_le]; constructor <;> nlinarith [pow_nonneg a1 3, pow_nonneg a1 2]
  have hpc : (4 * c ^ 3 + 15 * c ^ 2 + 8 * c)
      = 4 * π ^ 3 * (n : ℝ) ^ 6 + 15 * π ^ 2 * (n : ℝ) ^ 4 + 8 * π * (n : ℝ) ^ 2 := by
    simp only [c]; ring
  have hA : 0 ≤ (4 * c ^ 3 + 15 * c ^ 2 + 8 * c) * X ^ 3 := by positivity
  calc |-4 * (c * X) ^ 3 + 15 * (c * X) ^ 2 - 15 / 2 * (c * X)| * Real.exp (u / 2 - c * X)
      ≤ ((4 * c ^ 3 + 15 * c ^ 2 + 8 * c) * X ^ 3)
        * (Real.exp (u / 2) * (Real.exp (-(π / 2) * (n : ℝ) ^ 2) * Real.exp (-(π / 2) * X))) :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le hA
    _ = _ := by rw [hpc]; ring

theorem summable_coef1 : Summable coef1 := by
  have r : (0 : ℝ) < π / 2 := by positivity
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 r
  have h4 := Real.summable_pow_mul_exp_neg_nat_mul 4 r
  have h6 := Real.summable_pow_mul_exp_neg_nat_mul 6 r
  refine Summable.of_nonneg_of_le (fun n => by unfold coef1; positivity) (fun n => ?_)
    (((h6.mul_left (4 * π ^ 3)).add (h4.mul_left (15 * π ^ 2))).add (h2.mul_left (8 * π)))
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  have he : Real.exp (-(π / 2) * (n : ℝ) ^ 2) ≤ Real.exp (-(π / 2) * n) :=
    Real.exp_le_exp.2 (by nlinarith [pi_pos])
  unfold coef1
  calc _ ≤ (4 * π ^ 3 * (n : ℝ) ^ 6 + 15 * π ^ 2 * (n : ℝ) ^ 4 + 8 * π * (n : ℝ) ^ 2)
        * Real.exp (-(π / 2) * n) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- **Decay of `Φ'` at every exponential rate.** -/
theorem RPhi1_decay (B : ℝ) : ∃ C, 0 ≤ C ∧ ∀ u, |RPhi1 u| ≤ C * Real.exp (-B * |u|) := by
  obtain ⟨K, hK0, hK⟩ := exp_poly_decay 3 B
  set S := ∑' n, coef1 n
  have hS : 0 ≤ S := tsum_nonneg fun n => by unfold coef1; positivity
  refine ⟨S * K, by positivity, ?_⟩
  have hpos : ∀ u, 0 ≤ u → |RPhi1 u| ≤ S * K * Real.exp (-B * u) := by
    intro u hu
    set Bd := Real.exp (2 * u) ^ 3 * Real.exp (u / 2) * Real.exp (-(π / 2) * Real.exp (2 * u))
    have habs := (summable_phiT1 u).abs
    calc |RPhi1 u| ≤ ∑' n, |phiT1 n u| := by
          unfold RPhi1; rw [← Real.norm_eq_abs]
          exact (norm_tsum_le_tsum_norm (by simpa using habs)).trans (le_of_eq (by simp))
      _ ≤ ∑' n, coef1 n * Bd := habs.tsum_le_tsum (fun n => phiT1_le_pos hu n)
          (summable_coef1.mul_right Bd)
      _ = S * Bd := tsum_mul_right
      _ ≤ S * (K * Real.exp (-B * u)) := mul_le_mul_of_nonneg_left (hK u hu) hS
      _ = S * K * Real.exp (-B * u) := by ring
  intro u
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact hpos u hu
  · rw [abs_of_neg hu, ← abs_neg, ← RPhi1_odd]; exact hpos (-u) (by linarith)

/-! ## C. The truncation `Φ_a` is a probe -/

/-- `Φ_a = 1_{[−a,a]}Φ`. -/
def PhiA (a : ℝ) : ℝ → ℝ := (Icc (-a) a).indicator RPhi

theorem RPhi_lip : ∃ L, 0 ≤ L ∧ ∀ t s, |RPhi t - RPhi s| ≤ L * |t - s| := by
  obtain ⟨L, hL0, hL⟩ := RPhi1_decay 0
  refine ⟨L, hL0, fun t s => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := RPhi) (f' := RPhi1) (C := L)
    (s := univ) (fun x _ => (hasDerivAt_RPhi x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs]; simpa using hL x) convex_univ (mem_univ s) (mem_univ t)
  simpa [Real.norm_eq_abs] using this

/-- **A probe from an even continuous profile that is Lipschitz on the window** `[−a, a]` (round 336;
`probe_PhiA` below and `KaiserWindow.lean`'s `probe_gK` are its cases). -/
theorem probe_indicator_of_lip {a L : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hev : ∀ u, φ (-u) = φ u)
    (hL : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, |φ t - φ s| ≤ L * |t - s|) :
    Probe a ((Icc (-a) a).indicator φ) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc (-a) a))
  have hMb : ∀ t ∈ Icc (-a) a, φ t ^ 2 ≤ M ^ 2 := fun t ht => by
    have := hM t ht; rw [Real.norm_eq_abs] at this
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hD : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, (φ t - φ s) ^ 2 ≤ (L ^ 2 * (2 * a)) * |t - s| := by
    intro t ht s hs
    have h2 : |t - s| ≤ 2 * a := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
    have h3 : (φ t - φ s) ^ 2 ≤ (L * |t - s|) ^ 2 := by
      rw [← sq_abs]
      calc |φ t - φ s| ^ 2 ≤ (|L| * |t - s|) ^ 2 := by
            gcongr; exact (hL t ht s hs).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _))
        _ = (L * |t - s|) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
    calc (φ t - φ s) ^ 2 ≤ (L * |t - s|) ^ 2 := h3
      _ = L ^ 2 * |t - s| * |t - s| := by ring
      _ ≤ L ^ 2 * |t - s| * (2 * a) := by gcongr
      _ = _ := by ring
  obtain ⟨hm, harch, -, -⟩ := ind_energy ha hc hMb hD (by positivity)
  refine ⟨fun u => ?_, fun u hu => ?_, hm, harch⟩
  · by_cases h : u ∈ Icc (-a) a
    · have h' : -u ∈ Icc (-a) a := ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [indicator_of_mem h, indicator_of_mem h', hev]
    · have h' : -u ∉ Icc (-a) a := fun h' => h ⟨by linarith [h'.2], by linarith [h'.1]⟩
      rw [indicator_of_notMem h, indicator_of_notMem h']
  · apply indicator_of_notMem
    intro h; have := abs_le.2 ⟨h.1, h.2⟩; linarith

theorem probe_PhiA {a : ℝ} (ha : 0 ≤ a) : Probe a (PhiA a) := by
  obtain ⟨L, -, hL⟩ := RPhi_lip
  exact probe_indicator_of_lip ha continuous_RPhi RPhi_even fun t _ s _ => hL t s

theorem ghatC_PhiA {a : ℝ} (ha : 0 ≤ a) (t : ℂ) : ghatC (PhiA a) a t = ghatC RPhi a t := by
  unfold ghatC
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (by linarith)] at hu
  simp only [PhiA, indicator_of_mem hu]

/-! ## D. Fourier transforms on the strip, and their tails -/

theorem norm_cexp_le {t : ℂ} (ht : |t.im| ≤ 1 / 2) (u : ℝ) :
    ‖Complex.exp (Complex.I * t * u)‖ ≤ Real.exp (|u| / 2) := by
  rw [Complex.norm_exp]
  have e : (Complex.I * t * (u : ℂ)).re = -(t.im * u) := by simp [Complex.mul_re]
  rw [e]
  apply Real.exp_le_exp.2
  calc -(t.im * u) ≤ |t.im * u| := neg_le_abs _
    _ = |t.im| * |u| := abs_mul _ _
    _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    _ = |u| / 2 := by ring

/-- The tail `∫_{|u|>a} f(u) e^{itu} du`. -/
def tailT (f : ℝ → ℝ) (a : ℝ) (t : ℂ) : ℂ :=
  ∫ u, (((Icc (-a) a)ᶜ.indicator f u : ℝ) : ℂ) * Complex.exp (Complex.I * t * u)

variable {f : ℝ → ℝ} {C D : ℝ}

theorem integrable_decay_exp (hf : Continuous f) (hC : ∀ u, |f u| ≤ C * Real.exp (-D * |u|))
    (hD : 1 ≤ D) {t : ℂ} (ht : |t.im| ≤ 1 / 2) (S : Set ℝ) (hS : MeasurableSet S) :
    Integrable fun u : ℝ => ((S.indicator f u : ℝ) : ℂ) * Complex.exp (Complex.I * t * u) := by
  refine ((integrable_exp_neg_abs (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul C).mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    have : Measurable (S.indicator f) := hf.measurable.indicator hS
    fun_prop
  · refine Eventually.of_forall fun u => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |S.indicator f u| ≤ C * Real.exp (-D * |u|) := by
      by_cases h : u ∈ S
      · rw [indicator_of_mem h]; exact hC u
      · rw [indicator_of_notMem h, abs_zero]; exact le_trans (abs_nonneg _) (hC u)
    calc |S.indicator f u| * ‖Complex.exp (Complex.I * t * u)‖
        ≤ (C * Real.exp (-D * |u|)) * Real.exp (|u| / 2) :=
          mul_le_mul h1 (norm_cexp_le ht u) (norm_nonneg _) (le_trans (abs_nonneg _) (hC u))
      _ = C * Real.exp (-(D - 1 / 2) * |u|) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ C * Real.exp (-(1 / 2) * |u|) := by
          have hC0 : 0 ≤ C := by
            have := le_trans (abs_nonneg _) (hC 0); simpa using this
          gcongr; nlinarith [abs_nonneg u]

/-- **The Fourier split**: `∫ f e^{itu} = ĝ_a(t) + tail`. -/
theorem fourier_split (hf : Continuous f) (hC : ∀ u, |f u| ≤ C * Real.exp (-D * |u|))
    (hD : 1 ≤ D) {t : ℂ} (ht : |t.im| ≤ 1 / 2) {a : ℝ} (ha : 0 ≤ a) :
    ∫ u, (f u : ℂ) * Complex.exp (Complex.I * t * u) = ghatC f a t + tailT f a t := by
  have e : (fun u : ℝ => (f u : ℂ) * Complex.exp (Complex.I * t * u))
      = fun u => (((Icc (-a) a).indicator f u : ℝ) : ℂ) * Complex.exp (Complex.I * t * u)
        + (((Icc (-a) a)ᶜ.indicator f u : ℝ) : ℂ) * Complex.exp (Complex.I * t * u) := by
    funext u
    by_cases h : u ∈ Icc (-a) a
    · rw [indicator_of_mem h, indicator_of_notMem (by simpa using h)]; simp
    · rw [indicator_of_notMem h, indicator_of_mem (by simpa using h)]; simp
  rw [e, integral_add (integrable_decay_exp hf hC hD ht _ measurableSet_Icc)
    (integrable_decay_exp hf hC hD ht _ measurableSet_Icc.compl)]
  congr 1
  unfold ghatC
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  congr 1; funext u
  by_cases h : u ∈ Icc (-a) a
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h]; simp

/-- **The tail bound**: `‖tail‖ ≤ C e^{−(D − 3/2)a} ∫e^{−|u|}`. -/
theorem norm_tailT_le (hC : ∀ u, |f u| ≤ C * Real.exp (-D * |u|)) (hD : 3 / 2 ≤ D) {t : ℂ}
    (ht : |t.im| ≤ 1 / 2) (a : ℝ) :
    ‖tailT f a t‖ ≤ C * Real.exp (-(D - 3 / 2) * a) * ∫ u, Real.exp (-1 * |u|) := by
  have hC0 : 0 ≤ C := by have := le_trans (abs_nonneg _) (hC 0); simpa using this
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_exp_neg_abs one_pos).const_mul _)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases h : u ∈ (Icc (-a) a)ᶜ
  · rw [indicator_of_mem h]
    have hu : a ≤ |u| := by
      by_contra hc; push Not at hc
      exact h (abs_le.1 hc.le)
    calc |f u| * ‖Complex.exp (Complex.I * t * u)‖
        ≤ (C * Real.exp (-D * |u|)) * Real.exp (|u| / 2) :=
          mul_le_mul (hC u) (norm_cexp_le ht u) (norm_nonneg _) (le_trans (abs_nonneg _) (hC u))
      _ = C * Real.exp (-D * |u| + |u| / 2) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ C * Real.exp (-(D - 3 / 2) * a + -1 * |u|) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          apply Real.exp_le_exp.2
          nlinarith [mul_nonneg (show 0 ≤ D - 3 / 2 by linarith) (show 0 ≤ |u| - a by linarith)]
      _ = C * Real.exp (-(D - 3 / 2) * a) * Real.exp (-1 * |u|) := by rw [Real.exp_add]; ring
  · rw [indicator_of_notMem h]; simp only [abs_zero, zero_mul]; positivity

theorem integrable_decay_exp' (hf : Continuous f) (hC : ∀ u, |f u| ≤ C * Real.exp (-D * |u|))
    (hD : 1 ≤ D) {t : ℂ} (ht : |t.im| ≤ 1 / 2) :
    Integrable fun u : ℝ => (f u : ℂ) * Complex.exp (Complex.I * t * u) := by
  simpa using integrable_decay_exp hf hC hD ht univ MeasurableSet.univ

/-! ## E. At a zero of `Ξ` -/

theorem hasDerivAt_cexp_mul (t : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * t * y))
      (Complex.I * t * Complex.exp (Complex.I * t * x)) x := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * t * w))
      (Complex.exp (Complex.I * t * x) * (Complex.I * t)) (x : ℂ) := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul (Complex.I * t)).cexp
  rw [mul_comm (Complex.I * t)]
  exact h1.comp_ofReal

/-- **Integration by parts on the window** `[−a, a]`: `it·ĝ_u(t) = u(a)e^{ita} − u(−a)e^{−ita} − ĝ_{u′}(t)`
(round 336; `ibp_window` below and `WeilRH.lean`'s `ibp_C2` are its cases). -/
theorem ibp_ghatC {a : ℝ} {u u' : ℝ → ℝ} (hu : ∀ x ∈ uIcc (-a) a, HasDerivAt u (u' x) x)
    (hu' : IntervalIntegrable u' volume (-a) a) (t : ℂ) :
    Complex.I * t * ghatC u a t = (u a : ℂ) * Complex.exp (Complex.I * t * a)
      - (u (-a) : ℂ) * Complex.exp (-(Complex.I * t * a)) - ghatC u' a t := by
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -a) (b := a)
    (u := fun x : ℝ => (u x : ℂ)) (u' := fun x : ℝ => (u' x : ℂ))
    (v := fun y : ℝ => Complex.exp (Complex.I * t * y))
    (v' := fun x : ℝ => Complex.I * t * Complex.exp (Complex.I * t * x))
    (fun x hx => (hu x hx).ofReal_comp) (fun x _ => hasDerivAt_cexp_mul t x)
    ⟨hu'.1.ofReal, hu'.2.ofReal⟩
    ((by fun_prop : Continuous fun x : ℝ =>
      Complex.I * t * Complex.exp (Complex.I * t * x)).intervalIntegrable _ _)
  unfold ghatC
  rw [← intervalIntegral.integral_const_mul]
  have e : (fun x : ℝ => Complex.I * t * ((u x : ℂ) * Complex.exp (Complex.I * t * x)))
      = fun x => (u x : ℂ) * (Complex.I * t * Complex.exp (Complex.I * t * x)) := by
    funext x; ring
  rw [e, H]
  push_cast
  ring_nf

/-- **`∫Φ' e^{itu} = −it Φ̂(t)`** (integration by parts on the line). -/
theorem RPhi1_hat {t : ℂ} (ht : |t.im| ≤ 1 / 2) :
    ∫ u, (RPhi1 u : ℂ) * Complex.exp (Complex.I * t * u) = -(Complex.I * t) * RPhiHat t := by
  obtain ⟨C, -, hC⟩ := RPhi_decay_gen 2
  obtain ⟨C1, -, hC1⟩ := RPhi1_decay 2
  have i0 := integrable_decay_exp' continuous_RPhi hC (by norm_num) ht
  have i1 := integrable_decay_exp' continuous_RPhi1 hC1 (by norm_num) ht
  have H := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => (RPhi x : ℂ)) (u' := fun x : ℝ => (RPhi1 x : ℂ))
    (v := fun y : ℝ => Complex.exp (Complex.I * t * y))
    (v' := fun x : ℝ => Complex.I * t * Complex.exp (Complex.I * t * x))
    (fun x _ => (hasDerivAt_RPhi x).ofReal_comp) (fun x _ => hasDerivAt_cexp_mul t x)
    (by
      refine (i0.const_mul (Complex.I * t)).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    i1 i0
  unfold RPhiHat
  rw [← integral_const_mul]
  have e : (fun x : ℝ => -(Complex.I * t) * ((RPhi x : ℂ) * Complex.exp (Complex.I * t * x)))
      = fun x => -((RPhi x : ℂ) * (Complex.I * t * Complex.exp (Complex.I * t * x))) := by
    funext x; ring
  rw [e, integral_neg, H, neg_neg]

/-- **Integration by parts on `[−a, a]`**:
`it ĝ(t) = Φ(a)(e^{ita} − e^{−ita}) − ĝ'(t)`, `ĝ'` the transform of `Φ'` over the window. -/
theorem ibp_window (a : ℝ) (t : ℂ) :
    Complex.I * t * ghatC RPhi a t
      = (RPhi a : ℂ) * (Complex.exp (Complex.I * t * a) - Complex.exp (-(Complex.I * t * a)))
        - ghatC RPhi1 a t := by
  rw [ibp_ghatC (fun x _ => hasDerivAt_RPhi x) (continuous_RPhi1.intervalIntegrable _ _) t, RPhi_even]
  ring

theorem norm_cexp_sub_le {t : ℂ} (ht : |t.im| ≤ 1 / 2) (a : ℝ) :
    ‖Complex.exp (Complex.I * t * a) - Complex.exp (-(Complex.I * t * a))‖ ≤ 2 * Real.exp (|a| / 2) := by
  have h2 : ‖Complex.exp (-(Complex.I * t * a))‖ ≤ Real.exp (|a| / 2) := by
    have := norm_cexp_le ht (-a)
    rw [show Complex.I * t * ((-a : ℝ) : ℂ) = -(Complex.I * t * a) by push_cast; ring,
      abs_neg] at this
    exact this
  calc _ ≤ ‖Complex.exp (Complex.I * t * a)‖ + ‖Complex.exp (-(Complex.I * t * a))‖ := norm_sub_le _ _
    _ ≤ Real.exp (|a| / 2) + Real.exp (|a| / 2) := add_le_add (norm_cexp_le ht a) h2
    _ = _ := by ring

/-- **The two bounds at a zero of `Ξ`**: `‖ĝ(t)‖ ≤ ‖tail Φ‖` and
`‖t‖‖ĝ(t)‖ ≤ 2|Φ(a)|e^{a/2} + ‖tail Φ'‖`. -/
theorem zero_bounds {t : ℂ} (ht : |t.im| ≤ 1 / 2) (hz : Xi t = 0) {a : ℝ} (ha : 0 ≤ a) :
    ‖ghatC RPhi a t‖ ≤ ‖tailT RPhi a t‖ ∧
      ‖t‖ * ‖ghatC RPhi a t‖ ≤ 2 * |RPhi a| * Real.exp (a / 2) + ‖tailT RPhi1 a t‖ := by
  obtain ⟨C, -, hC⟩ := RPhi_decay_gen 2
  obtain ⟨C1, -, hC1⟩ := RPhi1_decay 2
  have h0 : RPhiHat t = 0 := by rw [RPhiHat_eq, hz, zero_div]
  have s0 := fourier_split continuous_RPhi hC (by norm_num) ht ha
  have s1 := fourier_split continuous_RPhi1 hC1 (by norm_num) ht ha
  have e0 : RPhiHat t = ∫ u, (RPhi u : ℂ) * Complex.exp (Complex.I * t * u) := rfl
  rw [← e0, h0] at s0
  rw [RPhi1_hat ht, h0, mul_zero] at s1
  have g0 : ghatC RPhi a t = -tailT RPhi a t := by linear_combination -s0
  have g1 : ghatC RPhi1 a t = -tailT RPhi1 a t := by linear_combination -s1
  refine ⟨by rw [g0, norm_neg], ?_⟩
  have hi := ibp_window a t
  rw [g1, sub_neg_eq_add] at hi
  have hn : ‖t‖ * ‖ghatC RPhi a t‖ = ‖Complex.I * t * ghatC RPhi a t‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  rw [hn, hi]
  calc _ ≤ ‖(RPhi a : ℂ) * (Complex.exp (Complex.I * t * a) - Complex.exp (-(Complex.I * t * a)))‖
        + ‖tailT RPhi1 a t‖ := norm_add_le _ _
    _ ≤ |RPhi a| * (2 * Real.exp (a / 2)) + ‖tailT RPhi1 a t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        simpa [abs_of_nonneg ha] using norm_cexp_sub_le ht a
    _ = _ := by ring

/-! ## F. Summing over the zeros -/

theorem norm_sq_add_four_pos {t : ℂ} (ht : |t.im| ≤ 1 / 2) : 0 < ‖t ^ 2 + 4‖ := by
  refine norm_pos_iff.2 fun h => ?_
  have := congrArg Complex.re h
  simp only [Complex.add_re, sq, Complex.mul_re, Complex.zero_re] at this
  have h1 : t.im * t.im ≤ 1 / 4 := by
    have := abs_le.1 ht; nlinarith
  norm_num at this
  nlinarith [mul_self_nonneg t.re]

/-- **Per-term bound**: `‖ĝ‖ ≤ τ₀`, `‖t‖‖ĝ‖ ≤ τ₁` give `‖ĝ‖² ≤ (τ₁² + 4τ₀²)‖1/(t² + 4)‖`. -/
theorem term_le {t : ℂ} (ht : |t.im| ≤ 1 / 2) {x τ₀ τ₁ : ℝ} (hx : 0 ≤ x) (h0 : x ≤ τ₀)
    (h1 : ‖t‖ * x ≤ τ₁) : x ^ 2 ≤ (τ₁ ^ 2 + 4 * τ₀ ^ 2) * ‖1 / (t ^ 2 + 4)‖ := by
  have hp := norm_sq_add_four_pos ht
  have hn : ‖t ^ 2 + 4‖ ≤ ‖t‖ ^ 2 + 4 := by
    calc ‖t ^ 2 + 4‖ ≤ ‖t ^ 2‖ + ‖(4 : ℂ)‖ := norm_add_le _ _
      _ = ‖t‖ ^ 2 + 4 := by rw [norm_pow]; norm_num
  rw [norm_div, norm_one, mul_one_div, le_div_iff₀ hp]
  have a1 : (‖t‖ * x) ^ 2 ≤ τ₁ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have a2 : x ^ 2 ≤ τ₀ ^ 2 := pow_le_pow_left₀ hx h0 2
  calc x ^ 2 * ‖t ^ 2 + 4‖ ≤ x ^ 2 * (‖t‖ ^ 2 + 4) := mul_le_mul_of_nonneg_left hn (sq_nonneg x)
    _ = (‖t‖ * x) ^ 2 + 4 * x ^ 2 := by ring
    _ ≤ _ := by linarith

/-- **Weil's energy of `Φ_a` over the zeros**: for any family on which `Ξ` vanishes, in the strip
`|Im t| ≤ ½`, with `Σ‖1/(t² + 4)‖ = S` and the explicit formula for `Φ_a`,
`Q(Φ_a) ≤ (τ₁² + 4τ₀²) S` with `τ₀ = sup‖tail Φ‖`, `τ₁ = 2|Φ(a)|e^{a/2} + sup‖tail Φ'‖`. -/
theorem weilQ_PhiA_le {ι : Type*} {ρ : ι → ℂ} (hz : ∀ i, Xi ((ρ i - 1 / 2) / Complex.I) = 0)
    (hs : ∀ i, |((ρ i - 1 / 2) / Complex.I).im| ≤ 1 / 2)
    (hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖)
    {a : ℝ} (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC (PhiA a) a z ^ 2) (hsq (PhiA a) a))
    {τ₀ τ₁ : ℝ} (h0 : ∀ i, ‖tailT RPhi a ((ρ i - 1 / 2) / Complex.I)‖ ≤ τ₀)
    (h1 : ∀ i, 2 * |RPhi a| * Real.exp (a / 2) + ‖tailT RPhi1 a ((ρ i - 1 / 2) / Complex.I)‖ ≤ τ₁) :
    weilQ a (PhiA a) ≤ (τ₁ ^ 2 + 4 * τ₀ ^ 2) * ∑' i, ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖ := by
  have H := weilQ_eq_zero_sum (probe_PhiA ha.le) ha hEF
  have Hre := Complex.reCLM.hasSum H
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at Hre
  refine hasSum_le (fun i => ?_) Hre (hS.hasSum.mul_left _)
  set t := (ρ i - 1 / 2) / Complex.I
  obtain ⟨b0, b1⟩ := zero_bounds (hs i) (hz i) ha.le
  rw [ghatC_PhiA ha.le]
  calc (ghatC RPhi a t ^ 2).re ≤ ‖ghatC RPhi a t ^ 2‖ := Complex.re_le_norm _
    _ = ‖ghatC RPhi a t‖ ^ 2 := norm_pow _ _
    _ ≤ _ := term_le (hs i) (norm_nonneg _) (b0.trans (h0 i)) (b1.trans (h1 i))

/-! ## G. The ground energy is `O(e^{−Ba})` for every `B` -/

theorem normSq_PhiA_mono {a : ℝ} (ha : 1 ≤ a) : normSq (PhiA 1) ≤ normSq (PhiA a) := by
  unfold normSq
  refine integral_mono (probe_PhiA zero_le_one).memL2.integrable_sq
    (probe_PhiA (by linarith)).memL2.integrable_sq fun t => ?_
  by_cases h : t ∈ Icc (-1 : ℝ) 1
  · have h' : t ∈ Icc (-a) a := ⟨by linarith [h.1], by linarith [h.2]⟩
    simp only [PhiA, indicator_of_mem h, indicator_of_mem h', le_refl]
  · simp only [PhiA, indicator_of_notMem h]
    rw [zero_pow two_ne_zero]; exact sq_nonneg _

theorem normSq_PhiA_one_pos : 0 < normSq (PhiA 1) := by
  unfold normSq
  refine (integral_pos_iff_support_of_nonneg (fun t => sq_nonneg (PhiA 1 t))
    (probe_PhiA zero_le_one).memL2.integrable_sq).2 ?_
  have hsub : Ioo (-1 : ℝ) 1 ⊆ Function.support fun t => PhiA 1 t ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self ht
    simp only [Function.mem_support, PhiA, indicator_of_mem ht']
    exact pow_ne_zero 2 (RPhi_pos t).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]; norm_num

/-- **The quantitative corollary**: over any family on which `Ξ` vanishes, lying in the strip, with
`Σ‖1/(t² + 4)‖ < ∞`, and given the explicit formula for every `Φ_a`, the ground energy of Weil's form
decays faster than every exponential: `λ₁(a) ≤ K e^{−Ba}` for `a ≥ 1`. -/
theorem lam_decay {ι : Type*} {ρ : ι → ℂ} (hz : ∀ i, Xi ((ρ i - 1 / 2) / Complex.I) = 0)
    (hs : ∀ i, |((ρ i - 1 / 2) / Complex.I).im| ≤ 1 / 2)
    (hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖)
    (hEF : ∀ a, 1 ≤ a → WeilExplicit ρ (fun z => ghatC (PhiA a) a z ^ 2) (hsq (PhiA a) a))
    (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lam a ≤ K * Real.exp (-B * a) := by
  set Dd := |B| / 2 + 2
  obtain ⟨C0, hC00, hC0⟩ := RPhi_decay_gen Dd
  obtain ⟨C1, hC10, hC1⟩ := RPhi1_decay Dd
  set I1 := ∫ u, Real.exp (-1 * |u|)
  have hI1 : 0 ≤ I1 := integral_nonneg fun u => (Real.exp_pos _).le
  set S := ∑' i, ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  set N1 := normSq (PhiA 1)
  have hN1 := normSq_PhiA_one_pos
  set K' := (2 * C0 + C1 * I1) ^ 2 + 4 * (C0 * I1) ^ 2
  have hK' : 0 ≤ K' := by positivity
  refine ⟨K' * S / N1, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  set E := Real.exp (-(Dd - 3 / 2) * a)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hDd : 3 / 2 ≤ Dd := by have := abs_nonneg B; simp only [Dd]; linarith
  have h0 : ∀ i, ‖tailT RPhi a ((ρ i - 1 / 2) / Complex.I)‖ ≤ C0 * I1 * E := fun i => by
    have := norm_tailT_le hC0 hDd (hs i) a; linarith [show C0 * E * I1 = C0 * I1 * E by ring]
  have h1 : ∀ i, 2 * |RPhi a| * Real.exp (a / 2) + ‖tailT RPhi1 a ((ρ i - 1 / 2) / Complex.I)‖
      ≤ (2 * C0 + C1 * I1) * E := fun i => by
    have t1 := norm_tailT_le hC1 hDd (hs i) a
    have t0 := hC0 a
    rw [abs_of_pos ha0] at t0
    have hb : |RPhi a| * Real.exp (a / 2) ≤ C0 * E := by
      calc |RPhi a| * Real.exp (a / 2) ≤ C0 * Real.exp (-Dd * a) * Real.exp (a / 2) :=
            mul_le_mul_of_nonneg_right t0 (Real.exp_pos _).le
        _ = C0 * Real.exp (-Dd * a + a / 2) := by rw [mul_assoc, ← Real.exp_add]
        _ ≤ C0 * E := by
            apply mul_le_mul_of_nonneg_left _ hC00
            exact Real.exp_le_exp.2 (by nlinarith)
    nlinarith
  have hQ := weilQ_PhiA_le hz hs hS ha0 (hEF a ha) h0 h1
  have hlam := lam_mul_le (probe_PhiA ha0.le)
  have hE2 : E ^ 2 ≤ Real.exp (-B * a) := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.2
    have := le_abs_self B
    simp only [Dd]; push_cast; nlinarith
  have hQ' : weilQ a (PhiA a) ≤ K' * S * Real.exp (-B * a) := by
    calc weilQ a (PhiA a) ≤ (((2 * C0 + C1 * I1) * E) ^ 2 + 4 * (C0 * I1 * E) ^ 2) * S := hQ
      _ = K' * S * E ^ 2 := by simp only [K']; ring
      _ ≤ K' * S * Real.exp (-B * a) := mul_le_mul_of_nonneg_left hE2 (by positivity)
  have hmono := normSq_PhiA_mono ha
  rcases le_or_gt (lam a) 0 with hl | hl
  · exact hl.trans (by positivity)
  · rw [div_mul_eq_mul_div, le_div_iff₀ hN1]
    nlinarith [mul_le_mul_of_nonneg_left hmono hl.le]

/-- **The quantitative corollary over the zeros of `ζ`.** Named input: Weil's explicit formula for
each `Φ_a` and for `h(z) = 1/(z² + 4)` (which gives `Σ_ρ ‖1/(t_ρ² + 4)‖ < ∞`). Gauss's digamma
integral is proved (`digammaDiff`). Then `λ₁(a) ≤ K e^{−Ba}` for every `B`. -/
theorem lam_decay_zeta
    (hEF : ∀ a, 1 ≤ a →
      WeilExplicit zetaZeroFamily (fun z => ghatC (PhiA a) a z ^ 2) (hsq (PhiA a) a))
    (h4 : WeilExplicit zetaZeroFamily (fun z => 1 / (z ^ 2 + 4)) (fun r => 1 / (r ^ 2 + 4)))
    (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lam a ≤ K * Real.exp (-B * a) := by
  refine lam_decay Xi_zeta_zero (fun p => ?_) ?_ hEF B
  · rw [im_ordinate, abs_neg, abs_le]
    obtain ⟨h1, h2⟩ := p.1.2.mem_strip
    exact ⟨by simp only [zetaZeroFamily]; linarith, by simp only [zetaZeroFamily]; linarith⟩
  · exact summable_norm_iff.2 h4.2.summable

end Pilot1ca

#print axioms Pilot1ca.hasDerivAt_RPhi
#print axioms Pilot1ca.RPhi1_decay
#print axioms Pilot1ca.probe_PhiA
#print axioms Pilot1ca.RPhi1_hat
#print axioms Pilot1ca.zero_bounds
#print axioms Pilot1ca.weilQ_PhiA_le
#print axioms Pilot1ca.lam_decay
#print axioms Pilot1ca.lam_decay_zeta
#print axioms Pilot1ca.ibp_ghatC
#print axioms Pilot1ca.probe_indicator_of_lip
