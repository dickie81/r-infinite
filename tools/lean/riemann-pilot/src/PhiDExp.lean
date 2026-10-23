import Mathlib
import WeilZeta

/-! # Double-exponential upper bounds on the first three rungs (round 159)

Rounds 133 and 153 bound rungs 0–2 of the ladder by `K e^{−Ba}` for every `B`, using only
`|Φ(u)| ≤ C e^{−B|u|}`. Riemann's kernel actually decays double-exponentially,
`|Φ(u)| ≤ C e^{9|u|/2 − πe^{2|u|}}`, and feeding that into the same zero-side argument gives
double-exponential bounds, with no RH input (over the zeros of `Ξ`, all in the strip):

* `lam_dexp`:  `λ₁(a) ≤ K e^{16a − 2πe^{2a}}` for `a ≥ 1`;
* `lamO_dexp`: `λ₁^odd(a) ≤ K e^{16a − 2πe^{a − 1/4}}` for `a ≥ 1` (antitwin of `Φ_{a/2−1/8}`);
* `lam2_dexp`: every `s` with `λ₂(a) ≥ s` has `s ≤ K e^{16a − 2πe^{a/2 − 1/4}}` for `a ≥ 3/2`
  (two disjoint twins of `Φ_{a/4−1/8}`).

The measured rungs are `exp(−(2π²N(T*)/log N(T*))(1 + o(1)))`, `T* = 2πe^{2a}` (Zhu's Landau–Widom
scale), so `lam_dexp` has the right double-exponential form with an exponent `2πe^{2a}` that is
smaller than the truth by a factor tending to `π`. Upper bounds only: the lower halves are
RH-strength (round 152). No bearing on RH.
-/

open Real MeasureTheory Set Filter Topology Complex

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## A. Sharp pointwise decay of `Φ` and `Φ'` -/

theorem exp_sharp_split {n : ℕ} (hn : 1 ≤ n) {X u : ℝ} (hX : 1 ≤ X) :
    Real.exp (u / 2 - π * (n : ℝ) ^ 2 * X)
      ≤ Real.exp (u / 2) * (Real.exp (-(π * ((n : ℝ) ^ 2 - 1))) * Real.exp (-(π * X))) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ ((n : ℝ) ^ 2 - 1) * (X - 1) := mul_nonneg (by nlinarith) (by linarith)
  nlinarith [mul_nonneg pi_pos.le h0]

/-- The coefficient `(2π²n⁴ + 3πn²)e^{−π(n² − 1)}`. -/
def coefS (n : ℕ) : ℝ :=
  (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * Real.exp (-(π * ((n : ℝ) ^ 2 - 1)))

/-- The coefficient `(4π³n⁶ + 15π²n⁴ + 8πn²)e^{−π(n² − 1)}`. -/
def coefS1 (n : ℕ) : ℝ :=
  (4 * π ^ 3 * (n : ℝ) ^ 6 + 15 * π ^ 2 * (n : ℝ) ^ 4 + 8 * π * (n : ℝ) ^ 2)
    * Real.exp (-(π * ((n : ℝ) ^ 2 - 1)))

theorem exp_sq_le (n : ℕ) : Real.exp (-(π * ((n : ℝ) ^ 2 - 1))) ≤ Real.exp π * Real.exp (-π * n) := by
  rw [← Real.exp_add]; apply Real.exp_le_exp.2
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  nlinarith [pi_pos]

theorem summable_coefS : Summable coefS := by
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 pi_pos
  have h4 := Real.summable_pow_mul_exp_neg_nat_mul 4 pi_pos
  refine Summable.of_nonneg_of_le (fun n => by unfold coefS; positivity) (fun n => ?_)
    (((h4.mul_left (2 * π ^ 2)).add (h2.mul_left (3 * π))).mul_left (Real.exp π))
  unfold coefS
  calc _ ≤ (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * (Real.exp π * Real.exp (-π * n)) :=
        mul_le_mul_of_nonneg_left (exp_sq_le n) (by positivity)
    _ = _ := by ring

theorem summable_coefS1 : Summable coefS1 := by
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 pi_pos
  have h4 := Real.summable_pow_mul_exp_neg_nat_mul 4 pi_pos
  have h6 := Real.summable_pow_mul_exp_neg_nat_mul 6 pi_pos
  refine Summable.of_nonneg_of_le (fun n => by unfold coefS1; positivity) (fun n => ?_)
    ((((h6.mul_left (4 * π ^ 3)).add (h4.mul_left (15 * π ^ 2))).add (h2.mul_left (8 * π))).mul_left
      (Real.exp π))
  unfold coefS1
  calc _ ≤ (4 * π ^ 3 * (n : ℝ) ^ 6 + 15 * π ^ 2 * (n : ℝ) ^ 4 + 8 * π * (n : ℝ) ^ 2)
        * (Real.exp π * Real.exp (-π * n)) := mul_le_mul_of_nonneg_left (exp_sq_le n) (by positivity)
    _ = _ := by ring

theorem phiT_le_sharp {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |phiT n u| ≤ coefS n
      * (Real.exp (2 * u) ^ 2 * Real.exp (u / 2) * Real.exp (-(π * Real.exp (2 * u)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [phiT_zero, coefS]
  set X := Real.exp (2 * u)
  have hX : 1 ≤ X := by simp only [X]; exact Real.one_le_exp (by linarith)
  have e4 : Real.exp (4 * u) = X ^ 2 := by simp only [X]; rw [← Real.exp_nat_mul]; ring_nf
  unfold phiT thC
  rw [e4, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp := exp_sharp_split hn (u := u) hX
  have hpoly : |2 * (π * (n : ℝ) ^ 2) ^ 2 * X ^ 2 - 3 * (π * (n : ℝ) ^ 2) * X|
      ≤ (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * X ^ 2 := by
    have hX2 : X ≤ X ^ 2 := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [pi_pos, sq_nonneg (n : ℝ), mul_nonneg pi_pos.le
      (sq_nonneg (n : ℝ)), mul_le_mul_of_nonneg_left hX2 (mul_nonneg pi_pos.le (sq_nonneg (n : ℝ)))]
  have hA : 0 ≤ (2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * X ^ 2 := by positivity
  calc |2 * (π * (n : ℝ) ^ 2) ^ 2 * X ^ 2 - 3 * (π * (n : ℝ) ^ 2) * X|
        * Real.exp (u / 2 - π * (n : ℝ) ^ 2 * X)
      ≤ ((2 * π ^ 2 * (n : ℝ) ^ 4 + 3 * π * (n : ℝ) ^ 2) * X ^ 2)
        * (Real.exp (u / 2) * (Real.exp (-(π * ((n : ℝ) ^ 2 - 1))) * Real.exp (-(π * X)))) :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le hA
    _ = _ := by unfold coefS; ring

theorem phiT1_le_sharp {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    |phiT1 n u| ≤ coefS1 n
      * (Real.exp (2 * u) ^ 3 * Real.exp (u / 2) * Real.exp (-(π * Real.exp (2 * u)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [phiT1_zero, coefS1]
  set X := Real.exp (2 * u)
  have hX : 1 ≤ X := by simp only [X]; exact Real.one_le_exp (by linarith)
  unfold phiT1 thF thC
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp := exp_sharp_split hn (u := u) hX
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
        * (Real.exp (u / 2) * (Real.exp (-(π * ((n : ℝ) ^ 2 - 1))) * Real.exp (-(π * X)))) :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le hA
    _ = _ := by rw [hpc]; unfold coefS1; ring

theorem exp_pow_combine (u : ℝ) (k : ℕ) (r : ℝ) (hr : r = 2 * k + 1 / 2) :
    Real.exp (2 * u) ^ k * Real.exp (u / 2) * Real.exp (-(π * Real.exp (2 * u)))
      = Real.exp (r * u - π * Real.exp (2 * u)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hr]; ring

/-- **`|Φ(u)| ≤ C e^{9|u|/2 − πe^{2|u|}}`.** -/
theorem RPhi_dexp : ∃ C, 0 ≤ C ∧ ∀ u, |RPhi u| ≤ C * Real.exp (9 / 2 * |u| - π * Real.exp (2 * |u|)) := by
  set S := ∑' n, coefS n
  refine ⟨S, tsum_nonneg fun n => by unfold coefS; positivity, fun u => ?_⟩
  have key : ∀ v, 0 ≤ v → |RPhi v| ≤ S * Real.exp (9 / 2 * v - π * Real.exp (2 * v)) := by
    intro v hv
    have habs := (summable_phiT v).abs
    calc |RPhi v| ≤ ∑' n, |phiT n v| := by
          unfold RPhi; rw [← Real.norm_eq_abs]
          exact (norm_tsum_le_tsum_norm (by simpa using habs)).trans (le_of_eq (by simp))
      _ ≤ ∑' n, coefS n * (Real.exp (2 * v) ^ 2 * Real.exp (v / 2)
            * Real.exp (-(π * Real.exp (2 * v)))) :=
          habs.tsum_le_tsum (fun n => phiT_le_sharp hv n) (summable_coefS.mul_right _)
      _ = S * (Real.exp (2 * v) ^ 2 * Real.exp (v / 2) * Real.exp (-(π * Real.exp (2 * v)))) :=
          tsum_mul_right
      _ = _ := by rw [exp_pow_combine v 2 (9 / 2) (by norm_num)]
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact key u hu
  · rw [abs_of_neg hu, ← RPhi_even]; exact key (-u) (by linarith)

/-- **`|Φ'(u)| ≤ C e^{13|u|/2 − πe^{2|u|}}`.** -/
theorem RPhi1_dexp : ∃ C, 0 ≤ C ∧ ∀ u, |RPhi1 u| ≤ C * Real.exp (13 / 2 * |u| - π * Real.exp (2 * |u|)) := by
  set S := ∑' n, coefS1 n
  refine ⟨S, tsum_nonneg fun n => by unfold coefS1; positivity, fun u => ?_⟩
  have key : ∀ v, 0 ≤ v → |RPhi1 v| ≤ S * Real.exp (13 / 2 * v - π * Real.exp (2 * v)) := by
    intro v hv
    have habs := (summable_phiT1 v).abs
    calc |RPhi1 v| ≤ ∑' n, |phiT1 n v| := by
          unfold RPhi1; rw [← Real.norm_eq_abs]
          exact (norm_tsum_le_tsum_norm (by simpa using habs)).trans (le_of_eq (by simp))
      _ ≤ ∑' n, coefS1 n * (Real.exp (2 * v) ^ 3 * Real.exp (v / 2)
            * Real.exp (-(π * Real.exp (2 * v)))) :=
          habs.tsum_le_tsum (fun n => phiT1_le_sharp hv n) (summable_coefS1.mul_right _)
      _ = S * (Real.exp (2 * v) ^ 3 * Real.exp (v / 2) * Real.exp (-(π * Real.exp (2 * v)))) :=
          tsum_mul_right
      _ = _ := by rw [exp_pow_combine v 3 (13 / 2) (by norm_num)]
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact key u hu
  · rw [abs_of_neg hu, ← abs_neg, ← RPhi1_odd]; exact key (-u) (by linarith)

/-! ## B. The tail bound -/

/-- **Tails of a double-exponentially decaying function**: if `|f(u)| ≤ C e^{k|u| − πe^{2|u|}}` and
`k + 3/2 ≤ 2πe^{2a}`, then on `|Im t| ≤ ½`, `‖tail‖ ≤ C e^{(k + 3/2)a − πe^{2a}} ∫e^{−|u|}`. -/
theorem norm_tailT_dexp {f : ℝ → ℝ} {C k : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u, |f u| ≤ C * Real.exp (k * |u| - π * Real.exp (2 * |u|)))
    {a : ℝ} (hka : k + 3 / 2 ≤ 2 * π * Real.exp (2 * a)) {t : ℂ} (ht : |t.im| ≤ 1 / 2) :
    ‖tailT f a t‖ ≤ C * Real.exp ((k + 3 / 2) * a - π * Real.exp (2 * a)) * ∫ u, Real.exp (-1 * |u|) := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_exp_neg_abs one_pos).const_mul _)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases h : u ∈ (Icc (-a) a)ᶜ
  · rw [indicator_of_mem h]
    have hu : a ≤ |u| := by
      by_contra hc; push Not at hc
      exact h (abs_le.1 hc.le)
    set v := |u|
    have hconv : Real.exp (2 * a) * (1 + 2 * (v - a)) ≤ Real.exp (2 * v) := by
      have := Real.add_one_le_exp (2 * (v - a))
      calc _ ≤ Real.exp (2 * a) * Real.exp (2 * (v - a)) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; ring_nf
    have h1 : (k + 3 / 2) * (v - a) ≤ 2 * π * Real.exp (2 * a) * (v - a) :=
      mul_le_mul_of_nonneg_right hka (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hconv pi_pos.le
    have hexp : k * v - π * Real.exp (2 * v) + v / 2
        ≤ (k + 3 / 2) * a - π * Real.exp (2 * a) + -1 * v := by nlinarith
    calc |f u| * ‖Complex.exp (Complex.I * t * u)‖
        ≤ (C * Real.exp (k * v - π * Real.exp (2 * v))) * Real.exp (v / 2) :=
          mul_le_mul (hC u) (norm_cexp_le ht u) (norm_nonneg _) (by positivity)
      _ = C * Real.exp (k * v - π * Real.exp (2 * v) + v / 2) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ C * Real.exp ((k + 3 / 2) * a - π * Real.exp (2 * a) + -1 * v) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hC0
      _ = _ := by rw [Real.exp_add]; ring
  · rw [indicator_of_notMem h]; simp only [abs_zero, zero_mul]; positivity

/-! ## C. The per-zero bound -/

theorem eight_le {b : ℝ} (hb : 1 / 4 ≤ b) : (8 : ℝ) ≤ 2 * π * Real.exp (2 * b) := by
  have h1 : (3 / 2 : ℝ) ≤ Real.exp (2 * b) := by
    have := Real.add_one_le_exp (2 * b); linarith
  nlinarith [pi_gt_three]

/-- **At a zero of `Ξ`**: `‖Φ̂_b(t)‖² ≤ K e^{16b − 2πe^{2b}}‖1/(t² + 4)‖` for `b ≥ 1/4`. -/
theorem ghat_PhiA_sq_dexp : ∃ K, 0 ≤ K ∧ ∀ {b : ℝ}, 1 / 4 ≤ b → ∀ {t : ℂ}, |t.im| ≤ 1 / 2 →
    Xi t = 0 → ‖ghatC (PhiA b) b t‖ ^ 2
      ≤ K * Real.exp (16 * b - 2 * π * Real.exp (2 * b)) * ‖1 / (t ^ 2 + 4)‖ := by
  obtain ⟨C0, hC00, hC0⟩ := RPhi_dexp
  obtain ⟨C1, hC10, hC1⟩ := RPhi1_dexp
  set I1 := ∫ u, Real.exp (-1 * |u|)
  have hI1 : 0 ≤ I1 := integral_nonneg fun u => (Real.exp_pos _).le
  refine ⟨(2 * C0 + C1 * I1) ^ 2 + 4 * (C0 * I1) ^ 2, by positivity, fun {b} hb {t} ht hz => ?_⟩
  have hb0 : 0 < b := by linarith
  have h8 := eight_le hb
  set E := π * Real.exp (2 * b)
  obtain ⟨b0, b1⟩ := zero_bounds ht hz hb0.le
  have t0 := norm_tailT_dexp hC00 hC0 (k := 9 / 2) (by linarith) ht (a := b)
  have t1 := norm_tailT_dexp hC10 hC1 (k := 13 / 2) (by linarith) ht (a := b)
  set τ₀ := C0 * I1 * Real.exp (6 * b - E)
  set τ₁ := (2 * C0 + C1 * I1) * Real.exp (8 * b - E)
  have h0 : ‖tailT RPhi b t‖ ≤ τ₀ := by
    have e : (9 / 2 + 3 / 2) * b - π * Real.exp (2 * b) = 6 * b - E := by simp only [E]; ring
    rw [e] at t0; linarith [show C0 * Real.exp (6 * b - E) * I1 = τ₀ by simp only [τ₀]; ring]
  have h1 : 2 * |RPhi b| * Real.exp (b / 2) + ‖tailT RPhi1 b t‖ ≤ τ₁ := by
    have e : (13 / 2 + 3 / 2) * b - π * Real.exp (2 * b) = 8 * b - E := by simp only [E]; ring
    rw [e] at t1
    have p0 := hC0 b
    rw [abs_of_pos hb0] at p0
    have hp : |RPhi b| * Real.exp (b / 2) ≤ C0 * Real.exp (8 * b - E) := by
      calc |RPhi b| * Real.exp (b / 2) ≤ C0 * Real.exp (9 / 2 * b - E) * Real.exp (b / 2) :=
            mul_le_mul_of_nonneg_right p0 (Real.exp_pos _).le
        _ = C0 * Real.exp (9 / 2 * b - E + b / 2) := by rw [mul_assoc, ← Real.exp_add]
        _ ≤ C0 * Real.exp (8 * b - E) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hC00
    have : C1 * Real.exp (8 * b - E) * I1 = C1 * I1 * Real.exp (8 * b - E) := by ring
    simp only [τ₁]; nlinarith
  rw [ghatC_PhiA hb0.le]
  have hT := term_le ht (norm_nonneg _) (b0.trans h0) (b1.trans h1)
  have e1 : τ₁ ^ 2 = (2 * C0 + C1 * I1) ^ 2 * Real.exp (16 * b - 2 * π * Real.exp (2 * b)) := by
    simp only [τ₁, E]; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have e0 : τ₀ ^ 2 = (C0 * I1) ^ 2 * Real.exp (12 * b - 2 * π * Real.exp (2 * b)) := by
    simp only [τ₀, E]; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have m : Real.exp (12 * b - 2 * π * Real.exp (2 * b)) ≤ Real.exp (16 * b - 2 * π * Real.exp (2 * b)) :=
    Real.exp_le_exp.2 (by linarith)
  have hw := norm_nonneg (1 / (t ^ 2 + 4))
  calc _ ≤ (τ₁ ^ 2 + 4 * τ₀ ^ 2) * ‖1 / (t ^ 2 + 4)‖ := hT
    _ ≤ _ := by
        rw [e1, e0]
        have : (C0 * I1) ^ 2 * Real.exp (12 * b - 2 * π * Real.exp (2 * b))
            ≤ (C0 * I1) ^ 2 * Real.exp (16 * b - 2 * π * Real.exp (2 * b)) :=
          mul_le_mul_of_nonneg_left m (sq_nonneg _)
        nlinarith

/-! ## D. Rung 0 -/

theorem weilQ_PhiA_le_M {ι : Type*} {ρ : ι → ℂ}
    (hS : Summable fun i => ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖) {a : ℝ} (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC (PhiA a) a z ^ 2) (hsq (PhiA a) a))
    {M : ℝ} (hM : ∀ i, ‖ghatC (PhiA a) a ((ρ i - 1 / 2) / Complex.I)‖ ^ 2
      ≤ M * ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖) :
    weilQ a (PhiA a) ≤ M * ∑' i, ‖1 / (((ρ i - 1 / 2) / Complex.I) ^ 2 + 4)‖ := by
  have H := weilQ_eq_zero_sum (probe_PhiA ha.le) ha hEF
  have Hre := Complex.reCLM.hasSum H
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at Hre
  refine hasSum_le (fun i => ?_) Hre (hS.hasSum.mul_left _)
  calc _ ≤ ‖ghatC (PhiA a) a ((ρ i - 1 / 2) / Complex.I) ^ 2‖ := Complex.re_le_norm _
    _ = _ := norm_pow _ _
    _ ≤ _ := hM i

/-- **Rung 0, double-exponential**: `λ₁(a) ≤ K e^{16a − 2πe^{2a}}` for `a ≥ 1`, over the zeros of
`Ξ` (no RH input, no named input). -/
theorem lam_dexp : ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lam a ≤ K * Real.exp (16 * a - 2 * π * Real.exp (2 * a)) := by
  obtain ⟨K0, hK0, hM⟩ := ghat_PhiA_sq_dexp
  set S := ∑' p : Bool × ZeroIdx (sqF Xi), ‖1 / (((rhoXi p - 1 / 2) / Complex.I) ^ 2 + 4)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  set N1 := normSq (PhiA 1)
  have hN1 := normSq_PhiA_one_pos
  refine ⟨K0 * S / N1, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  set F := Real.exp (16 * a - 2 * π * Real.exp (2 * a))
  have hQ := weilQ_PhiA_le_M summable_four_Xi ha0 (weilExplicit_PhiA ha0) (M := K0 * F)
    (fun p => hM (by linarith) (im_rhoXi p).le (Xi_rhoXi p))
  have hlam := lam_mul_le (probe_PhiA ha0.le)
  have hmono := normSq_PhiA_mono ha
  rcases le_or_gt (lam a) 0 with hl | hl
  · exact hl.trans (by positivity)
  · rw [div_mul_eq_mul_div, le_div_iff₀ hN1]
    nlinarith [mul_le_mul_of_nonneg_left hmono hl.le]

/-! ## E. Rung 1 -/

/-- **Rung 1, double-exponential**: `λ₁^odd(a) ≤ K e^{16a − 2πe^{a − 1/4}}` for `a ≥ 1`. -/
theorem lamO_dexp :
    ∃ K, 0 ≤ K ∧ ∀ a, 1 ≤ a → lamO a ≤ K * Real.exp (16 * a - 2 * π * Real.exp (a - 1 / 4)) := by
  obtain ⟨K0, hK0, hM0⟩ := ghat_PhiA_sq_dexp
  set S := ∑' p : Bool × ZeroIdx (sqF Xi), ‖1 / (((rhoXi p - 1 / 2) / Complex.I) ^ 2 + 4)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  set N1 := normSq (PhiA (3 / 8))
  have hN1 : 0 < N1 := normSq_PhiA_pos (by norm_num)
  refine ⟨2 * K0 * S / N1, by positivity, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  set b := a / 2 - 1 / 8
  set l := a / 2
  have hb : 0 < b := by simp only [b]; linarith
  have hb4 : 1 / 4 ≤ b := by simp only [b]; linarith
  set F := Real.exp (16 * b - 2 * π * Real.exp (2 * b))
  have hM := fun p => hM0 hb4 (im_rhoXi p).le (Xi_rhoXi p)
  have hQ := weilQg_atwin_le (fun p => (im_rhoXi p).le) summable_four_Xi hb (l := l) (a := a)
    (by positivity) (by simp only [b, l]; linarith) (weilExplicit_PhiA hb)
    (weilExplicit_twin hb (by positivity)) (M := K0 * F) hM
  set N := normSq (PhiA b)
  have hN : N1 ≤ N := normSq_PhiA_mono' (by norm_num) (by simp only [b]; linarith)
  have hNpos : 0 < N := hN1.trans_le hN
  have hnA := (normSq_twin_atwin hb.le (probe_PhiA hb.le) (show b < l by simp only [b, l]; linarith)).2
  set c := 1 / Real.sqrt (2 * N)
  have hc2 : c ^ 2 = 1 / (2 * N) := by rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hop := (oprobe_atwin (probe_PhiA hb.le) (a := a) (l := l)
    (by rw [abs_of_pos (by positivity)]; simp only [b, l]; linarith)).smul c
  have hn : normSq (fun t => c * atwin (PhiA b) l t) = 1 := by
    rw [normSq_smul, hnA, hc2]; change 1 / (2 * N) * (2 * N) = 1; field_simp
  have hl := lamO_le ha0 hop hn
  rw [weilQg_smul, hc2] at hl
  have h2b : 2 * b = a - 1 / 4 := by simp only [b]; ring
  have hexp : Real.exp l * F ≤ Real.exp (16 * a - 2 * π * Real.exp (a - 1 / 4)) := by
    simp only [F]; rw [← Real.exp_add, h2b]; apply Real.exp_le_exp.2; simp only [b, l]; nlinarith
  have hX : weilQg a (atwin (PhiA b) l) ≤ 4 * K0 * S * Real.exp (16 * a - 2 * π * Real.exp (a - 1 / 4)) := by
    calc _ ≤ 4 * Real.exp l * (K0 * F) * S := hQ
      _ = 4 * K0 * S * (Real.exp l * F) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  calc lamO a ≤ 1 / (2 * N) * weilQg a (atwin (PhiA b) l) := hl
    _ ≤ 1 / (2 * N) * (4 * K0 * S * Real.exp (16 * a - 2 * π * Real.exp (a - 1 / 4))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ 1 / (2 * N1) * (4 * K0 * S * Real.exp (16 * a - 2 * π * Real.exp (a - 1 / 4))) :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) (by linarith))
          (by positivity)
    _ = 2 * K0 * S / N1 * Real.exp (16 * a - 2 * π * Real.exp (a - 1 / 4)) := by field_simp; ring

/-! ## F. Rung 2 -/

/-- The explicit formula for `pT_l + qT_m` built from `Φ_b`, `l ≤ m`, `m + b ≤ a`, over the zeros of `Ξ`. -/
theorem weilExplicit_combo_gen {a b l m : ℝ} (hb : 0 < b) (hl : 0 ≤ l) (hlm : l ≤ m) (hma : m + b ≤ a)
    (p q : ℝ) :
    WeilExplicit rhoXi
      (fun z => ghatC (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) a z ^ 2)
      (hsq (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) a) := by
  have hp := probe_PhiA hb.le
  have hm : 0 ≤ m := hl.trans hlm
  have hpl := twin_probe hp hl
  have hpm := twin_probe hp hm
  have hpv : Probe a (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) :=
    (probe_add_sub (probe_smul (hpl.mono (by linarith)) p) (probe_smul (hpm.mono (by linarith)) q)).1
  have e : ∀ t : ℂ, ghatC (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) a t
      = (p * (2 * Complex.cos (↑l * t)) + q * (2 * Complex.cos (↑m * t))) * ghatC (PhiA b) b t := by
    intro t
    rw [show (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t)
      = (fun t => p * twin (PhiA b) l t) + (fun t => q * twin (PhiA b) m t) from rfl,
      ghatC_add (hpl.memL2.const_mul p) (hpm.memL2.const_mul q), ghatC_smul, ghatC_smul,
      ghatC_window (by linarith) (by linarith) hpl.supp,
      ghatC_window (by linarith) (by linarith) hpm.supp, ghatC_twin hb hp hl, ghatC_twin hb hp hm]
    ring
  obtain ⟨K, hK⟩ := ghat_PhiA_strip hb
  have hT := striptest_mul_sq (G := ghatC (PhiA b) b)
    (m := fun z => (p : ℂ) * (2 * Complex.cos (↑l * z)) + q * (2 * Complex.cos (↑m * z)))
    (M := |p| * (2 * Real.exp l) + |q| * (2 * Real.exp m))
    (ghatC_differentiable hp.intervalIntegrable) (by fun_prop) hK (fun t ht => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_two_cos_strip hl ht) (abs_nonneg _)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_two_cos_strip hm ht) (abs_nonneg _))
  have hfun : (fun z => ghatC (fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) a z ^ 2)
      = fun z => (((p : ℂ) * (2 * Complex.cos (↑l * z)) + q * (2 * Complex.cos (↑m * z)))
          * ghatC (PhiA b) b z) ^ 2 := by
    funext z; rw [e]
  rw [hfun]
  refine weilExplicit_Xi hT (fun t => ?_) (fun r => ?_)
  · have := even_ghat_sq (g := fun t => p * twin (PhiA b) l t + q * twin (PhiA b) m t) hpv.even a t
    rw [e, e] at this
    exact this
  · have := hsq_ofReal hpv (by linarith) r
    rw [e] at this
    exact this

/-- **Rung 2, double-exponential**: every `s` with `λ₂(a) ≥ s` has
`s ≤ K e^{16a − 2πe^{a/2 − 1/4}}` for `a ≥ 3/2`. -/
theorem lam2_dexp : ∃ K, 0 ≤ K ∧ ∀ a, 3 / 2 ≤ a → ∀ s, Lam2Ge a s →
    s ≤ K * Real.exp (16 * a - 2 * π * Real.exp (a / 2 - 1 / 4)) := by
  obtain ⟨K0, hK0, hM0⟩ := ghat_PhiA_sq_dexp
  set S := ∑' p : Bool × ZeroIdx (sqF Xi), ‖1 / (((rhoXi p - 1 / 2) / Complex.I) ^ 2 + 4)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  set N1 := normSq (PhiA (1 / 4))
  have hN1 : 0 < N1 := normSq_PhiA_pos (by norm_num)
  refine ⟨4 * K0 * S / N1, by positivity, fun a ha s Hs => ?_⟩
  have ha0 : 0 < a := by linarith
  set b := a / 4 - 1 / 8
  set l := a / 4
  set m := 3 * a / 4 - 1 / 8
  have hb4 : 1 / 4 ≤ b := by simp only [b]; linarith
  have hb : 0 < b := by linarith
  set F := Real.exp (16 * b - 2 * π * Real.exp (2 * b))
  have hM := fun p => hM0 hb4 (im_rhoXi p).le (Xi_rhoXi p)
  have hp := probe_PhiA hb.le
  set N := normSq (PhiA b)
  have hN : N1 ≤ N := normSq_PhiA_mono' (by norm_num) hb4
  have hNpos : 0 < N := hN1.trans_le hN
  have n1 := (normSq_twin_atwin hb.le hp (show b < l by simp only [b, l]; linarith)).1
  have n2 := (normSq_twin_atwin hb.le hp (show b < m by simp only [b, m]; linarith)).1
  set c := 1 / Real.sqrt (2 * N)
  have hc2 : c ^ 2 = 1 / (2 * N) := by rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have pg := probe_smul ((twin_probe hp (by positivity : (0 : ℝ) ≤ l)).mono
    (by simp only [b, l]; linarith : l + b ≤ a)) c
  have ph := probe_smul ((twin_probe hp (by simp only [m]; linarith : (0 : ℝ) ≤ m)).mono
    (by simp only [b, m]; linarith : m + b ≤ a)) c
  have ng : normSq (fun t => c * twin (PhiA b) l t) = 1 := by
    rw [normSq_smul, n1, hc2]; change 1 / (2 * N) * (2 * N) = 1; field_simp
  have nh : normSq (fun t => c * twin (PhiA b) m t) = 1 := by
    rw [normSq_smul, n2, hc2]; change 1 / (2 * N) * (2 * N) = 1; field_simp
  have hx : xcorr (fun t => c * twin (PhiA b) l t) (fun t => c * twin (PhiA b) m t) 0 = 0 := by
    rw [xcorr_zero_eq]
    have e : (fun t => c * twin (PhiA b) l t * (c * twin (PhiA b) m t)) = fun _ => (0 : ℝ) :=
      funext fun t => by
        rw [mul_mul_mul_comm, twin_mul_twin_zero hp.supp (by positivity)
          (by simp only [b, l, m]; linarith) t, mul_zero]
    rw [e, integral_zero]
  obtain ⟨α, β, hαβ, hsv⟩ := Hs _ _ pg ph ng nh hx
  have ev : (fun t => α * (c * twin (PhiA b) l t) + β * (c * twin (PhiA b) m t))
      = fun t => (α * c) * twin (PhiA b) l t + (β * c) * twin (PhiA b) m t := by funext t; ring
  rw [ev] at hsv
  have hQ := weilQ_pair_le (fun p => (im_rhoXi p).le) summable_four_Xi hb (by positivity : (0 : ℝ) ≤ l)
    (by simp only [l, m]; linarith : l ≤ m) (by simp only [b, m]; linarith : m + b ≤ a) (α * c) (β * c)
    (weilExplicit_combo_gen hb (by positivity) (by simp only [l, m]; linarith)
      (by simp only [b, m]; linarith) _ _) (M := K0 * F) hM
  have hP : (|α * c| + |β * c|) ^ 2 ≤ 1 / N := by
    have h2 : (α * c) ^ 2 + (β * c) ^ 2 = 1 / (2 * N) := by
      rw [mul_pow, mul_pow, hc2, ← add_mul, hαβ, one_mul]
    have : (|α * c| + |β * c|) ^ 2 ≤ 2 * ((α * c) ^ 2 + (β * c) ^ 2) := by
      nlinarith [sq_abs (α * c), sq_abs (β * c), sq_nonneg (|α * c| - |β * c|)]
    rw [h2] at this
    calc _ ≤ 2 * (1 / (2 * N)) := this
      _ = 1 / N := by field_simp
  have h2b : 2 * b = a / 2 - 1 / 4 := by simp only [b]; ring
  have hexp : Real.exp m * F ≤ Real.exp (16 * a - 2 * π * Real.exp (a / 2 - 1 / 4)) := by
    simp only [F]; rw [← Real.exp_add, h2b]; apply Real.exp_le_exp.2; simp only [b, m]; nlinarith
  set P := (|α * c| + |β * c|) ^ 2
  have hP0 : 0 ≤ P := by positivity
  calc s ≤ _ := hsv
    _ ≤ 4 * P * Real.exp m * (K0 * F) * S := hQ
    _ = (4 * K0 * S) * P * (Real.exp m * F) := by ring
    _ ≤ (4 * K0 * S) * (1 / N) * Real.exp (16 * a - 2 * π * Real.exp (a / 2 - 1 / 4)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP (by positivity)) hexp (by positivity)
          (by positivity)
    _ ≤ (4 * K0 * S) * (1 / N1) * Real.exp (16 * a - 2 * π * Real.exp (a / 2 - 1 / 4)) := by
        gcongr
    _ = 4 * K0 * S / N1 * Real.exp (16 * a - 2 * π * Real.exp (a / 2 - 1 / 4)) := by ring

end Pilot1ca

#print axioms Pilot1ca.RPhi_dexp
#print axioms Pilot1ca.RPhi1_dexp
#print axioms Pilot1ca.norm_tailT_dexp
#print axioms Pilot1ca.ghat_PhiA_sq_dexp
#print axioms Pilot1ca.lam_dexp
#print axioms Pilot1ca.lamO_dexp
#print axioms Pilot1ca.lam2_dexp
