import Mathlib
import BohrSphere
import CubeBall
import Orthogonality
import BallTower
import DirMean
import PsiOmega
import HalfPlaneS0
import KubotaRows

/-! # The geometric strand joined to the pilot (round 398)

The owner asked whether rounds 391–397 can be plugged into the theorems of the pilot. This file proves the joins that
exist. Each runs from the pilot's results into the geometric picture, or between two tools. None of them proves a
hypothesis that the open-targets register (`STRUCTURAL-REVIEW.md` §6) lists as open.

* **Zero-free regions are shells around the sphere** (**`shell_of_zeroFree`**, with `norm_vF_le_norm_vF`): if `ζ ≠ 0`
  on `Re s > θ`, every nontrivial zero `ρ` has `‖v_F(θ)‖ ≤ ‖v_F(ρ)‖ ≤ ‖v_F(1 − θ)‖` for every nonempty finite set `F`
  of primes, through `PsiOmega.band_of_zeroFree`. Instances: unconditionally, strictly between the radii at `1` and
  `0` (**`shell_unconditional`**); from S0's hypothesis (**`shell_of_smoothBound`**); from the Kubota–Patterson
  display, between the radii at `11/12` and `1/12` (**`shell_of_kubotaTheta`**). At `θ = ½` the shell is the sphere
  (**`sphere_of_zeroFree_half`**, through `PsiOmega.rh_of_zeroFree_half`).
* **In the limit no shell short of the sphere constrains the radius** (**`shell_radii_tendsto`**): for every `θ > ½`
  the radius at `θ` tends to `0` and the radius at `1 − θ` to `∞` over the primes below `N`. If RH fails, some zero
  pair has one Bohr vector strictly inside the sphere and one strictly outside, in every dimension, with radii
  tending to `0` and `∞` (**`zero_pair_of_not_RH`**); round 392 proved this for the Davenport–Heilbronn function.
* **The ball tower** (**`tendsto_ballVol`**, **`tendsto_sphereArea`**, **`tendsto_volume_unitBall`**,
  **`ball_div_cube_eq`** and **`completed_eq_sphereArea_bohr`**, with `ballVol_add_two_le` and `ballVol_le_geom`):
  `BallTower.ballVol n`, the volume of the unit ball of `ℝⁿ`, is at most `C·rⁿ` with `r² = 7/10` for `n ≥ 7`, so it
  tends to `0`; so do the area of the unit sphere and Mathlib's volume of the unit ball, the latter through
  `BallTower.ballVol_eq_volume`, which had no users. Round 397's ratio of the ball to the cube is `ballVol n/2ⁿ`.
  For every integer `n ≥ 2`, `Λ(n) = (2/|S^{n−1}|)·exp(Σ_p p^{−n})·D₂(n)`, which joins
  `BallTower.Gammaℝ_mul_sphereArea` to round 391's Euler split.
* **The mean value theorem, both sides** (**`abs_mean_value_sub_le`** and **`mean_value_ge`**, with `dp_eq_trig`,
  `injOn_neg_log_nat` and `gap_sum_le`): for a Dirichlet polynomial `D` supported on `(P, 2P]`,
  `|∫₀ᵀ |D|² − T·Σ|c_j|²| ≤ 8P(1 + log P)·Σ|c_j|²`. Round 235's `DirMean.mean_value` states the upper half; round
  395's `Orthogonality.abs_integral_sub_le` supplies the lower. The two files prove the same oscillatory bound
  separately (`DirMean.norm_integral_exp_le`, `Orthogonality.norm_integral_exp_mul_I_le`).
-/

open Filter Topology BohrSphere MeasureTheory Metric

namespace BohrJoins

/-! ## Part A: zero-free regions as shells around the sphere -/

/-- The radius is antitone in `Re s`. -/
lemma norm_vF_le_norm_vF {F : Finset Nat.Primes} (hF : F.Nonempty) {s s' : ℂ} (h : s.re ≤ s'.re) :
    ‖vF F s'‖ ≤ ‖vF F s‖ := by
  rcases h.lt_or_eq with h | h
  · exact (norm_vF_lt_norm_vF hF h).le
  · exact (norm_vF_eq_of_re_eq F h).ge

/-- **A zero-free half-plane is a shell around the sphere.** -/
theorem shell_of_zeroFree {θ : ℝ} (hzf : ∀ ρ : ℂ, θ < ρ.re → riemannZeta ρ ≠ 0)
    {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ} (hρ : Pilot1bt.IsNontrivialZero ρ) :
    ‖vF F θ‖ ≤ ‖vF F ρ‖ ∧ ‖vF F ρ‖ ≤ ‖vF F ((1 - θ : ℝ) : ℂ)‖ := by
  have hb := PsiOmega.band_of_zeroFree hzf hρ
  rw [abs_le] at hb
  constructor
  · exact norm_vF_le_norm_vF hF (by rw [Complex.ofReal_re]; linarith)
  · exact norm_vF_le_norm_vF hF (by rw [Complex.ofReal_re]; linarith)

/-- **Unconditionally** the nontrivial zeros lie strictly between the radii at `Re s = 1` and `Re s = 0`
(`Pilot1bt.IsNontrivialZero.re_lt_one`, `re_pos`). -/
theorem shell_unconditional {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ}
    (hρ : Pilot1bt.IsNontrivialZero ρ) : ‖vF F 1‖ < ‖vF F ρ‖ ∧ ‖vF F ρ‖ < ‖vF F 0‖ :=
  ⟨norm_vF_lt_norm_vF hF (by simpa using hρ.re_lt_one), norm_vF_lt_norm_vF hF (by simpa using hρ.re_pos)⟩

/-- From S0's hypothesis `SmoothBound θ` (round 278). -/
theorem shell_of_smoothBound {θ : ℝ} (h : HalfPlaneS0.SmoothBound θ) {F : Finset Nat.Primes}
    (hF : F.Nonempty) {ρ : ℂ} (hρ : Pilot1bt.IsNontrivialZero ρ) :
    ‖vF F θ‖ ≤ ‖vF F ρ‖ ∧ ‖vF F ρ‖ ≤ ‖vF F ((1 - θ : ℝ) : ℂ)‖ :=
  shell_of_zeroFree (fun _ hs => (HalfPlaneS0.ne_zero_of_smoothBound h hs).1) hF hρ

/-- From the Kubota–Patterson display (round 381's `Eis.ne_zero_of_kubotaTheta`): between the radii at `11/12`
and `1/12`. -/
theorem shell_of_kubotaTheta (hK : Eis.KubotaTheta) {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ}
    (hρ : Pilot1bt.IsNontrivialZero ρ) :
    ‖vF F ((11 / 12 : ℝ) : ℂ)‖ ≤ ‖vF F ρ‖ ∧ ‖vF F ρ‖ ≤ ‖vF F ((1 / 12 : ℝ) : ℂ)‖ := by
  have h := shell_of_zeroFree (θ := 11 / 12) (fun _ hs => (Eis.ne_zero_of_kubotaTheta hK hs).1) hF hρ
  norm_num at h ⊢
  exact h

/-- **In the limit no shell short of the sphere constrains the radius**: for `θ > ½` the radius at `θ` tends to
`0` and the radius at `1 − θ` to `∞` over the primes below `N`. -/
theorem shell_radii_tendsto {θ : ℝ} (hθ : 1 / 2 < θ) :
    Tendsto (fun N => ‖vF (primesLT N) (θ : ℂ)‖) atTop (𝓝 0) ∧
      Tendsto (fun N => ‖vF (primesLT N) ((1 - θ : ℝ) : ℂ)‖) atTop atTop :=
  ⟨tendsto_norm_vF_of_half_lt (by rw [Complex.ofReal_re]; exact hθ),
    tendsto_norm_vF_of_lt_half (by rw [Complex.ofReal_re]; linarith)⟩

/-- At `θ = ½` the shell is the sphere (through `PsiOmega.rh_of_zeroFree_half`). -/
theorem sphere_of_zeroFree_half (hzf : ∀ ρ : ℂ, 1 / 2 < ρ.re → riemannZeta ρ ≠ 0)
    {F : Finset Nat.Primes} (hF : F.Nonempty) {ρ : ℂ} (hρ : Pilot1bt.IsNontrivialZero ρ) :
    vF F ρ ∈ Metric.sphere 0 1 :=
  (riemannHypothesis_iff_mem_sphere hF).1 (PsiOmega.rh_of_zeroFree_half hzf) ρ hρ.1 hρ.2
    (fun h => riemannZeta_one_ne_zero (h ▸ hρ.1))

/-- **If RH fails, some zero pair straddles the sphere**: one Bohr vector strictly inside and one strictly outside
in every dimension, with radii tending to `0` and `∞`; round 392 proved this for the Davenport–Heilbronn function. -/
theorem zero_pair_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, Pilot1bt.IsNontrivialZero ρ ∧ Pilot1bt.IsNontrivialZero (1 - ρ) ∧ 1 / 2 < ρ.re ∧
      (∀ F : Finset Nat.Primes, F.Nonempty → ‖vF F ρ‖ < 1 ∧ 1 < ‖vF F (1 - ρ)‖) ∧
      Tendsto (fun N => ‖vF (primesLT N) ρ‖) atTop (𝓝 0) ∧
      Tendsto (fun N => ‖vF (primesLT N) (1 - ρ)‖) atTop atTop := by
  obtain ⟨ρ, hre, hz⟩ : ∃ ρ : ℂ, 1 / 2 < ρ.re ∧ riemannZeta ρ = 0 := by
    by_contra hcon
    exact hRH (PsiOmega.rh_of_zeroFree_half fun ρ hρ hz => hcon ⟨ρ, hρ, hz⟩)
  have hnt : Pilot1bt.IsNontrivialZero ρ := by
    refine ⟨hz, ?_⟩
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re < 0 := by simp; linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have hre' : (1 - ρ).re < 1 / 2 := by rw [Complex.sub_re, Complex.one_re]; linarith
  exact ⟨ρ, hnt, PsiOmega.IsNontrivialZero.one_sub hnt, hre,
    fun F hF => ⟨(norm_vF_lt_one_iff hF).2 hre, (one_lt_norm_vF_iff hF).2 hre'⟩,
    tendsto_norm_vF_of_half_lt hre, tendsto_norm_vF_of_lt_half hre'⟩

/-! ## Part B: the ball tower -/

/-- For `n ≥ 7` the two-step factor `2π/(n + 2)` of the tower is below `7/10`. -/
lemma ballVol_add_two_le {n : ℕ} (hn : 7 ≤ n) :
    BallTower.ballVol (n + 2) ≤ 7 / 10 * BallTower.ballVol n := by
  rw [BallTower.ballVol_add_two]
  refine mul_le_mul_of_nonneg_right ?_ (BallTower.ballVol_pos n).le
  have h9 : (9 : ℝ) ≤ n + 2 := by have : (7 : ℝ) ≤ n := by exact_mod_cast hn
                                  linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.pi_lt_d2]

/-- `ballVol n ≤ C·rⁿ` for `n ≥ 7`, with `r² = 7/10`. -/
theorem ballVol_le_geom : ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n, 7 ≤ n → BallTower.ballVol n ≤ C * r ^ n := by
  set r : ℝ := Real.sqrt (7 / 10) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr1 : r < 1 := by rw [hr, Real.sqrt_lt' one_pos]; norm_num
  have hr2 : r ^ 2 = 7 / 10 := by rw [hr, Real.sq_sqrt (by norm_num)]
  set C := max (BallTower.ballVol 7 / r ^ 7) (BallTower.ballVol 8 / r ^ 8)
  refine ⟨C, r, hr0.le, hr1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k using Nat.twoStepInduction with
  | zero =>
    have := le_max_left (BallTower.ballVol 7 / r ^ 7) (BallTower.ballVol 8 / r ^ 8)
    rw [div_le_iff₀ (by positivity)] at this
    simpa using this
  | one =>
    have := le_max_right (BallTower.ballVol 7 / r ^ 7) (BallTower.ballVol 8 / r ^ 8)
    rw [div_le_iff₀ (by positivity)] at this
    simpa using this
  | more k ih _ =>
    have h1 := ih (by omega)
    calc BallTower.ballVol (7 + (k + 2)) = BallTower.ballVol ((7 + k) + 2) := by ring_nf
      _ ≤ 7 / 10 * BallTower.ballVol (7 + k) := ballVol_add_two_le (by omega)
      _ ≤ 7 / 10 * (C * r ^ (7 + k)) := by gcongr
      _ = C * r ^ (7 + (k + 2)) := by rw [← hr2]; ring

/-- **The volume of the unit ball of `ℝⁿ` tends to `0`.** -/
theorem tendsto_ballVol : Tendsto BallTower.ballVol atTop (𝓝 0) := by
  obtain ⟨C, r, hr0, hr1, hb⟩ := ballVol_le_geom
  have hlim : Tendsto (fun n : ℕ => C * r ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun n => (BallTower.ballVol_pos n).le) ?_ hlim
  filter_upwards [eventually_ge_atTop 7] with n hn
  exact hb n hn

/-- The area of the unit sphere `S^{n−1}` tends to `0` too. -/
theorem tendsto_sphereArea : Tendsto BallTower.sphereArea atTop (𝓝 0) := by
  obtain ⟨C, r, hr0, hr1, hb⟩ := ballVol_le_geom
  have hlim : Tendsto (fun n : ℕ => C * (n * r ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hlim
  · unfold BallTower.sphereArea; exact mul_nonneg (Nat.cast_nonneg n) (BallTower.ballVol_pos n).le
  · filter_upwards [eventually_ge_atTop 7] with n hn
    unfold BallTower.sphereArea
    calc (n : ℝ) * BallTower.ballVol n ≤ n * (C * r ^ n) :=
          mul_le_mul_of_nonneg_left (hb n hn) (Nat.cast_nonneg n)
      _ = C * (n * r ^ n) := by ring

/-- The same for Mathlib's volume of the unit ball of `EuclideanSpace ℝ (Fin n)`, through
`BallTower.ballVol_eq_volume`. -/
theorem tendsto_volume_unitBall :
    Tendsto (fun n : ℕ => (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) atTop (𝓝 0) := by
  refine tendsto_ballVol.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : NeZero n := ⟨by omega⟩
  exact (BallTower.ballVol_eq_volume n).symm

/-- Round 397's ratio of the Euclidean ball to the cube is `ballVol n/2ⁿ`. -/
theorem ball_div_cube_eq (n : ℕ) [NeZero n] :
    (volume {x : Fin n → ℝ | ‖WithLp.toLp 2 x‖ < 1}).toReal / (volume (ball (0 : Fin n → ℝ) 1)).toReal =
      BallTower.ballVol n / 2 ^ n := by
  rw [CubeBall.volume_euclideanBall, BallTower.ballVol_eq_volume, Real.volume_pi_ball _ one_pos,
    ENNReal.toReal_ofReal (by positivity)]
  simp

/-- **The ball tower and the Bohr lift in one identity**: for every integer `n ≥ 2`,
`Λ(n) = (2/|S^{n−1}|)·exp(Σ_p p^{−n})·D₂(n)`, from `BallTower.Gammaℝ_mul_sphereArea` and round 391's Euler split. -/
theorem completed_eq_sphereArea_bohr {n : ℕ} (hn : 2 ≤ n) :
    completedRiemannZeta n = 2 / (BallTower.sphereArea n : ℂ) *
      (Complex.exp (∑' p : Nat.Primes, bohr n p) * Complex.exp (∑' p, regTerm n p)) := by
  have hre : 1 < (n : ℂ).re := by
    rw [Complex.natCast_re]; exact_mod_cast (by omega : 1 < n)
  have hS : (BallTower.sphereArea n : ℂ) ≠ 0 := by
    exact_mod_cast (BallTower.sphereArea_pos (by omega)).ne'
  have hG : Complex.Gammaℝ (n : ℂ) = 2 / (BallTower.sphereArea n : ℂ) := by
    rw [eq_div_iff hS]; exact BallTower.Gammaℝ_mul_sphereArea n (by omega)
  rw [BallTower.completed_eq_Gammaℝ_mul hre, riemannZeta_eq_exp_mul_exp hre, hG]

/-! ## Part C: the mean value theorem, both sides -/

/-- `DirMean.dp` is `Orthogonality.trig` with the frequencies `−log j`. -/
lemma dp_eq_trig (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    DirMean.dp S c t = Orthogonality.trig S c (fun j : ℕ => -Real.log j) t := by
  unfold DirMean.dp Orthogonality.trig
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  push_cast
  ring

/-- The frequencies `−log j` are distinct on `(P, 2P]`. -/
lemma injOn_neg_log_nat {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) :
    Set.InjOn (fun j : ℕ => -Real.log j) S := by
  intro j hj k hk h
  have hj0 : (0 : ℝ) < j := by
    have := (Finset.mem_Ioc.1 (hS hj)).1; exact_mod_cast (by omega : 0 < j)
  have hk0 : (0 : ℝ) < k := by
    have := (Finset.mem_Ioc.1 (hS hk)).1; exact_mod_cast (by omega : 0 < k)
  have hlog : Real.log j = Real.log k := by simpa using h
  exact_mod_cast Real.log_injOn_pos hj0 hk0 hlog

/-- The frequency-gap sum of `Orthogonality` is at most `8P(1 + log P)·Σ‖c_j‖²` on `(P, 2P]`. -/
lemma gap_sum_le {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ) :
    ∑ j ∈ S, ∑ k ∈ S, ‖c j‖ * ‖c k‖ * Orthogonality.freqGapBound (fun j : ℕ => -Real.log j) j k
      ≤ 8 * P * (1 + Real.log P) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  set K : ℕ → ℕ → ℝ := fun j j' => if j' = j then 0 else 1 / |(j : ℝ) - j'| with hK
  have hK0 : ∀ j j', 0 ≤ K j j' := fun j j' => by simp only [hK]; split_ifs <;> positivity
  have hKsym : ∀ j j', K j' j = K j j' := fun j j' => by
    simp only [hK]; rw [abs_sub_comm]; split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  have hrow : ∀ j ∈ S, ∑ j' ∈ S, K j j' ≤ 2 * (1 + Real.log P) :=
    fun j hj => (Finset.sum_le_sum_of_subset_of_nonneg hS fun j' _ _ => hK0 j j').trans
      (DirMean.sum_inv_dist_le (hS hj))
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hterm : ∀ j ∈ S, ∀ k ∈ S,
      ‖c j‖ * ‖c k‖ * Orthogonality.freqGapBound (fun j : ℕ => -Real.log j) j k
        ≤ 2 * P * (‖c j‖ ^ 2 * K j k + ‖c k‖ ^ 2 * K j k) := by
    intro j hj k hk
    unfold Orthogonality.freqGapBound
    by_cases h : j = k
    · subst h; simp [hK]
    · simp only [h, ↓reduceIte, hK, Ne.symm h]
      have hlog := DirMean.abs_log_sub_ge (hS hj) (hS hk) h
      have hjk : (0 : ℝ) < |(j : ℝ) - k| := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast h))
      have hP1 : (0 : ℝ) < 2 * P := by
        have := (Finset.mem_Ioc.1 (hS hj)).2
        have : 1 ≤ P := by have := (Finset.mem_Ioc.1 (hS hj)).1; omega
        positivity
      have hl0 : 0 < |Real.log j - Real.log k| := lt_of_lt_of_le (div_pos hjk hP1) hlog
      have e : |-Real.log j - -Real.log k| = |Real.log j - Real.log k| := by
        rw [show -Real.log j - -Real.log k = -(Real.log j - Real.log k) by ring, abs_neg]
      rw [e]
      have h2 : 2 / |Real.log j - Real.log k| ≤ 4 * P / |(j : ℝ) - k| := by
        rw [div_le_div_iff₀ hl0 hjk]
        have := (div_le_iff₀ hP1).1 hlog
        nlinarith
      have hab := two_mul_le_add_sq ‖c j‖ ‖c k‖
      calc ‖c j‖ * ‖c k‖ * (2 / |Real.log j - Real.log k|)
          ≤ ‖c j‖ * ‖c k‖ * (4 * P / |(j : ℝ) - k|) := by gcongr
        _ = 2 * P * (2 * ‖c j‖ * ‖c k‖) * (1 / |(j : ℝ) - k|) := by ring
        _ ≤ 2 * P * (‖c j‖ ^ 2 + ‖c k‖ ^ 2) * (1 / |(j : ℝ) - k|) := by gcongr
        _ = 2 * P * (‖c j‖ ^ 2 * (1 / |(j : ℝ) - k|) + ‖c k‖ ^ 2 * (1 / |(j : ℝ) - k|)) := by ring
  calc ∑ j ∈ S, ∑ k ∈ S, ‖c j‖ * ‖c k‖ * Orthogonality.freqGapBound (fun j : ℕ => -Real.log j) j k
      ≤ ∑ j ∈ S, ∑ k ∈ S, 2 * P * (‖c j‖ ^ 2 * K j k + ‖c k‖ ^ 2 * K j k) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm j hj k hk
    _ = 2 * P * (∑ j ∈ S, ‖c j‖ ^ 2 * ∑ k ∈ S, K j k + ∑ j ∈ S, ∑ k ∈ S, ‖c k‖ ^ 2 * K j k) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 2 * P * (2 * ∑ j ∈ S, ‖c j‖ ^ 2 * ∑ k ∈ S, K j k) := by
        congr 1
        rw [Finset.sum_comm (f := fun j k => ‖c k‖ ^ 2 * K j k)]
        have : ∑ k ∈ S, ∑ j ∈ S, ‖c k‖ ^ 2 * K j k = ∑ k ∈ S, ‖c k‖ ^ 2 * ∑ j ∈ S, K k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hKsym]
        rw [this]; ring
    _ ≤ 2 * P * (2 * ∑ j ∈ S, ‖c j‖ ^ 2 * (2 * (1 + Real.log P))) := by
        gcongr with j hj
        exact hrow j hj
    _ = 8 * P * (1 + Real.log P) * ∑ j ∈ S, ‖c j‖ ^ 2 := by rw [← Finset.sum_mul]; ring

/-- **The mean value theorem, both sides**: `|∫₀ᵀ |D|² − T·Σ|c_j|²| ≤ 8P(1 + log P)·Σ|c_j|²`. -/
theorem abs_mean_value_sub_le {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖DirMean.dp S c t‖ ^ 2) - T * ∑ j ∈ S, ‖c j‖ ^ 2|
      ≤ 8 * P * (1 + Real.log P) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  have h := Orthogonality.abs_integral_sub_le S c (fun j : ℕ => -Real.log j) (injOn_neg_log_nat hS) T
  simp only [← dp_eq_trig] at h
  exact h.trans (gap_sum_le hS c)

/-- The lower half, which round 235's `DirMean.mean_value` does not state. -/
theorem mean_value_ge {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ) (T : ℝ) :
    (T - 8 * P * (1 + Real.log P)) * ∑ j ∈ S, ‖c j‖ ^ 2 ≤ ∫ t in (0 : ℝ)..T, ‖DirMean.dp S c t‖ ^ 2 := by
  have h := abs_mean_value_sub_le hS c T
  rw [abs_le] at h
  linarith

end BohrJoins

#print axioms BohrJoins.norm_vF_le_norm_vF
#print axioms BohrJoins.shell_of_zeroFree
#print axioms BohrJoins.shell_unconditional
#print axioms BohrJoins.shell_of_smoothBound
#print axioms BohrJoins.shell_of_kubotaTheta
#print axioms BohrJoins.shell_radii_tendsto
#print axioms BohrJoins.sphere_of_zeroFree_half
#print axioms BohrJoins.zero_pair_of_not_RH
#print axioms BohrJoins.ballVol_add_two_le
#print axioms BohrJoins.ballVol_le_geom
#print axioms BohrJoins.tendsto_ballVol
#print axioms BohrJoins.tendsto_sphereArea
#print axioms BohrJoins.tendsto_volume_unitBall
#print axioms BohrJoins.ball_div_cube_eq
#print axioms BohrJoins.completed_eq_sphereArea_bohr
#print axioms BohrJoins.dp_eq_trig
#print axioms BohrJoins.injOn_neg_log_nat
#print axioms BohrJoins.gap_sum_le
#print axioms BohrJoins.abs_mean_value_sub_le
#print axioms BohrJoins.mean_value_ge
