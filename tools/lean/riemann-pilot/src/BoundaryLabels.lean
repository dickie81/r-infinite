import Mathlib
import BinetEnvelope

/-! # The integer labels of Part 0's landmarks, derived (round 413)

Part 0's four distinguished dimensions come from four continuous landmarks (round 412): the volume maximum at
`x₀ − 1 ≈ 5.2569` and the three crossings `p(x) = c` at `x₀ ≈ 6.2569` (`c = 0`), `x₁ ≈ 19.7308` (`c = ½ log π`) and
`x₂ ≈ 217.6267` (`c = √π`). Each landmark is the maximum of one function. This file proves which integer each of the
same functions picks out, and what the other labelling rules give.

* **The crossings as maxima** (`tilt`, `hasDerivAt_tilt`, `tilt_max`, `crossings_maximize`): with
  `F_c(x) = log Ω(x) + c·x` we have `F_c′ = c − p`, so the crossing `p(x_c) = c` is the strict maximum of `F_c` on
  `x > −1`.
* **The same functions on the integers** (`lattice_zero`, `lattice_one`, `lattice_two`, `lattice_dimensions`):
  `V_n` is largest at `n = 5` (BallTower), `F₀ = log Ω` at `d = 6`, `F_{½ log π}` at `d = 20` and `F_{√π}` at
  `d = 218`, each uniquely. `F_c` rises strictly up to its crossing and falls strictly after it
  (`tilt_strictMonoOn`, `tilt_strictAntiOn`, `tilt_lattice_max_up`, `tilt_lattice_max_down`), so only the two
  neighbours of the crossing compete. The deciding comparisons are `Ω₁₉ < √π·Ω₂₀` (`step_19_20`) and
  `Ω₂₁₇ < e^{√π}·Ω₂₁₈` (`step_217_218`), through `Ω_{2m} = 2^{2m+1}π^m m!/(2m)!` (`Om_even`).
* **Floor, ceiling and nearest integer** (`roundings`): the landmarks' floors are `5, 6, 19, 217`, their ceilings
  `6, 7, 20, 218`, and their nearest integers `5, 6, 20, 218`.
* **The mirror weights** (`mirrorW`, `mirrorW_ne_zero_iff`, `mirror_selects`): round 98's branch-swapped weight
  `2/Γ_ℝ(−d)` is nonzero exactly at odd `d`, so that per-label clause picks `5, 7, 19, 217` from the four pairs.
* **The invariant** (`cascadeInv_lattice_closed`, `cascadeInv_lattice_bounds`, `paper_over_lattice`): at
  `(6, 20, 218)`, `(Ω₅/Ω₆)²Ω₂₀Ω₂₁₈` lies between `1.0216 × 10⁻¹²¹` and `1.0218 × 10⁻¹²¹`, and Part 0's value at
  `(7, 19, 217)` is between `10.75` and `10.76` times it.
* `max_boundary_is_six`: the ball with the largest boundary is `B⁷`, and its boundary's area is `Ω₆`, which exceeds
  `Ω₇`.

Inputs: round 411 (`pR`, `OmR`, `Om`, `hasDerivAt_log_OmR`, `pR_strictMonoOn`, `Om_odd`, `Om_lt_six`, `cascadeInv`,
`cascadeInv_bounds`), round 412 (`zero_loc`, `threshold_one_loc`, `threshold_two_loc`, `gammaR`), round 406
(`exp_ge_of`, `sqrt_pi_gt`), BallTower (round 184), and Mathlib (`Real.Gamma_neg_nat_eq_zero`,
`Real.Gamma_ne_zero`, the bounds on `π`). The theorems say what each rule gives; they do not say which rule is the
cascade's.
-/

open Real Set

noncomputable section

namespace BoundaryLabels

/-! ## The tilted log-area -/

/-- `F_c(x) = log Ω(x) + c·x` on the continuous sphere dimension; its derivative is `c − p(x)`. -/
def tilt (c x : ℝ) : ℝ := Real.log (Part0.OmR x) + c * x

theorem hasDerivAt_tilt (c : ℝ) {x : ℝ} (hx : -1 < x) :
    HasDerivAt (tilt c) (c - Part0.pR x) x := by
  have h := (Part0.hasDerivAt_log_OmR hx).add ((hasDerivAt_id x).const_mul c)
  have e : ((fun y => Real.log (Part0.OmR y)) + fun y => c * id y) = tilt c := by
    funext y
    simp [tilt]
  rw [e] at h
  convert h using 1
  ring

theorem tilt_strictMonoOn {c x0 : ℝ} (hx0 : -1 < x0) (h0 : Part0.pR x0 = c) :
    StrictMonoOn (tilt c) (Ioc (-1) x0) := by
  have hcont : ContinuousOn (tilt c) (Ioc (-1) x0) := fun z hz =>
    (hasDerivAt_tilt c hz.1).continuousAt.continuousWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Ioc (-1) x0) hcont (fun z hz => ?_)
  rw [interior_Ioc] at hz
  rw [(hasDerivAt_tilt c hz.1).deriv]
  have := Part0.pR_strictMonoOn (mem_Ioi.2 hz.1) (mem_Ioi.2 hx0) hz.2
  linarith

theorem tilt_strictAntiOn {c x0 : ℝ} (hx0 : -1 < x0) (h0 : Part0.pR x0 = c) :
    StrictAntiOn (tilt c) (Ici x0) := by
  have hcont : ContinuousOn (tilt c) (Ici x0) := fun z hz =>
    (hasDerivAt_tilt c (lt_of_lt_of_le hx0 hz)).continuousAt.continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ici x0) hcont (fun z hz => ?_)
  rw [interior_Ici] at hz
  have hz' : -1 < z := lt_trans hx0 hz
  rw [(hasDerivAt_tilt c hz').deriv]
  have := Part0.pR_strictMonoOn (mem_Ioi.2 hx0) (mem_Ioi.2 hz') hz
  linarith

/-- **Each crossing maximizes its tilted log-area:** if `p(x₀) = c`, then `F_c(y) < F_c(x₀)` for every other
`y > −1`. -/
theorem tilt_max {c x0 : ℝ} (hx0 : -1 < x0) (h0 : Part0.pR x0 = c) :
    ∀ y, -1 < y → y ≠ x0 → tilt c y < tilt c x0 := by
  intro y hy hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact tilt_strictMonoOn hx0 h0 ⟨hy, h.le⟩ ⟨hx0, le_refl x0⟩ h
  · exact tilt_strictAntiOn hx0 h0 (mem_Ici.2 (le_refl x0)) (mem_Ici.2 h.le) h

theorem tilt_natCast (c : ℝ) (d : ℕ) : tilt c d = Real.log (Part0.Om d) + c * d := by
  rw [tilt, Part0.OmR_natCast]

/-- On the integers, `F_c` is largest at the upper neighbour `m + 1` of the crossing when `F_c(m) < F_c(m + 1)`. -/
theorem tilt_lattice_max_up {c x0 : ℝ} {m : ℕ} (hx0 : -1 < x0) (h0 : Part0.pR x0 = c)
    (hlo : (m : ℝ) < x0) (hhi : x0 < m + 1) (hstep : tilt c m < tilt c (m + 1)) :
    ∀ d : ℕ, d ≠ m + 1 → tilt c d < tilt c (m + 1) := by
  intro d hd
  rcases Nat.lt_or_gt_of_ne hd with h | h
  · have hdm : (d : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp h
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : tilt c d ≤ tilt c m :=
      (tilt_strictMonoOn hx0 h0).monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, hlo.le⟩ hdm
    linarith
  · have hdm : (m : ℝ) + 1 < d := by exact_mod_cast h
    exact tilt_strictAntiOn hx0 h0 (mem_Ici.2 hhi.le) (mem_Ici.2 (by linarith)) hdm

/-- The same at the lower neighbour `m` when `F_c(m + 1) < F_c(m)`. -/
theorem tilt_lattice_max_down {c x0 : ℝ} {m : ℕ} (hx0 : -1 < x0) (h0 : Part0.pR x0 = c)
    (hlo : (m : ℝ) < x0) (hhi : x0 < m + 1) (hstep : tilt c (m + 1) < tilt c m) :
    ∀ d : ℕ, d ≠ m → tilt c d < tilt c m := by
  intro d hd
  rcases Nat.lt_or_gt_of_ne hd with h | h
  · have hdm : (d : ℝ) < m := by exact_mod_cast h
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact (tilt_strictMonoOn hx0 h0) ⟨by linarith, by linarith⟩ ⟨by linarith, hlo.le⟩ hdm
  · have hdm : (m : ℝ) + 1 ≤ d := by exact_mod_cast Nat.succ_le_of_lt h
    have h1 : tilt c d ≤ tilt c (m + 1) := by
      rcases eq_or_lt_of_le hdm with he | hlt
      · exact (congrArg (tilt c) he).symm.le
      · exact (tilt_strictAntiOn hx0 h0 (mem_Ici.2 hhi.le) (mem_Ici.2 (by linarith)) hlt).le
    linarith

/-! ## The sphere areas at even dimensions -/

/-- `Ω_{2m} = |S^{2m}| = 2^{2m+1} π^m m!/(2m)!`. -/
theorem Om_even (m : ℕ) :
    Part0.Om (2 * m) = 2 ^ (2 * m + 1) * π ^ m * (Nat.factorial m) / (Nat.factorial (2 * m)) := by
  induction m with
  | zero =>
    show BallTower.sphereArea (2 * 0 + 1) = _
    simp [BallTower.sphereArea, BallTower.ballVol_one]
  | succ k ih =>
    have h : Part0.Om (2 * (k + 1)) = 2 * π / ((2 * k + 1 : ℕ) : ℝ) * Part0.Om (2 * k) := by
      show BallTower.sphereArea (2 * (k + 1) + 1)
        = 2 * π / ((2 * k + 1 : ℕ) : ℝ) * BallTower.sphereArea (2 * k + 1)
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring]
      exact BallTower.sphereArea_add_two (by omega)
    have hf : (Nat.factorial (2 * (k + 1)) : ℝ) = (2 * k + 2) * (2 * k + 1) * Nat.factorial (2 * k) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [h, ih, hf, Nat.factorial_succ k]
    have h2 : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem Om_nineteen : Part0.Om 19 = 2 * π ^ 10 / (Nat.factorial 9) := by
  have := Part0.Om_odd 9
  rwa [show 2 * 9 + 1 = 19 from rfl, show 9 + 1 = 10 from rfl] at this

theorem Om_twenty : Part0.Om 20 = 2 ^ 21 * π ^ 10 * (Nat.factorial 10) / (Nat.factorial 20) := by
  have := Om_even 10
  rwa [show 2 * 10 = 20 from rfl, show 20 + 1 = 21 from rfl] at this

theorem Om_two_seventeen : Part0.Om 217 = 2 * π ^ 109 / (Nat.factorial 108) := by
  have := Part0.Om_odd 108
  rwa [show 2 * 108 + 1 = 217 from rfl, show 108 + 1 = 109 from rfl] at this

theorem Om_two_eighteen :
    Part0.Om 218 = 2 ^ 219 * π ^ 109 * (Nat.factorial 109) / (Nat.factorial 218) := by
  have := Om_even 109
  rwa [show 2 * 109 = 218 from rfl, show 218 + 1 = 219 from rfl] at this

/-! ## The two decisive steps -/

/-- `Ω₁₉ < √π·Ω₂₀`. -/
theorem step_19_20 : Part0.Om 19 < Part0.Om 20 * √π := by
  rw [Om_nineteen, Om_twenty]
  have hs := Electron.sqrt_pi_gt
  have hp : (0 : ℝ) < π ^ 10 := by positivity
  have hc : (0 : ℝ) ≤ 2 ^ 21 * (Nat.factorial 10) / (Nat.factorial 20) := by positivity
  have key : (2 : ℝ) / (Nat.factorial 9)
      < 2 ^ 21 * (Nat.factorial 10) / (Nat.factorial 20) * 1.7724538509 := by
    simp only [Nat.factorial]; norm_num
  calc 2 * π ^ 10 / (Nat.factorial 9 : ℝ) = π ^ 10 * (2 / (Nat.factorial 9)) := by ring
    _ < π ^ 10 * (2 ^ 21 * (Nat.factorial 10) / (Nat.factorial 20) * 1.7724538509) :=
        mul_lt_mul_of_pos_left key hp
    _ ≤ π ^ 10 * (2 ^ 21 * (Nat.factorial 10) / (Nat.factorial 20) * √π) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs.le hc) hp.le
    _ = 2 ^ 21 * π ^ 10 * (Nat.factorial 10) / (Nat.factorial 20) * √π := by ring

/-- `Ω₂₁₇ < e^{√π}·Ω₂₁₈`. -/
theorem step_217_218 : Part0.Om 217 < Part0.Om 218 * Real.exp √π := by
  rw [Om_two_seventeen, Om_two_eighteen]
  have he : (2.7182818283 : ℝ) ^ 1 * ∑ i ∈ Finset.range 12, (0.7724538509 : ℝ) ^ i / (Nat.factorial i)
      ≤ Real.exp √π :=
    (Electron.exp_ge_of (x := 1.7724538509) 1 12 0.7724538509 (by norm_num) (by norm_num)).trans
      (Real.exp_le_exp.mpr Electron.sqrt_pi_gt.le)
  have key : (2 : ℝ) / (Nat.factorial 108) < 2 ^ 219 * (Nat.factorial 109) / (Nat.factorial 218)
      * ((2.7182818283 : ℝ) ^ 1 * ∑ i ∈ Finset.range 12, (0.7724538509 : ℝ) ^ i / (Nat.factorial i)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num
  have hp : (0 : ℝ) < π ^ 109 := by positivity
  have hc : (0 : ℝ) ≤ 2 ^ 219 * (Nat.factorial 109) / (Nat.factorial 218) := by positivity
  calc 2 * π ^ 109 / (Nat.factorial 108 : ℝ) = π ^ 109 * (2 / (Nat.factorial 108)) := by ring
    _ < π ^ 109 * (2 ^ 219 * (Nat.factorial 109) / (Nat.factorial 218)
        * ((2.7182818283 : ℝ) ^ 1 * ∑ i ∈ Finset.range 12, (0.7724538509 : ℝ) ^ i / (Nat.factorial i))) :=
        mul_lt_mul_of_pos_left key hp
    _ ≤ π ^ 109 * (2 ^ 219 * (Nat.factorial 109) / (Nat.factorial 218) * Real.exp √π) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hc) hp.le
    _ = 2 ^ 219 * π ^ 109 * (Nat.factorial 109) / (Nat.factorial 218) * Real.exp √π := by ring

/-! ## The lattice maxima -/

/-- `F₀ = log Ω` is largest on the lattice at `d = 6`. -/
theorem lattice_zero : ∀ d : ℕ, d ≠ 6 → tilt 0 d < tilt 0 6 := by
  intro d hd
  have h := Real.log_lt_log (Part0.Om_pos d) (Part0.Om_lt_six d hd)
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, tilt_natCast, tilt_natCast]
  simpa using h

/-- `F_{½ log π}` is largest on the lattice at `d = 20`. -/
theorem lattice_one : ∀ d : ℕ, d ≠ 20 → tilt (Real.log π / 2) d < tilt (Real.log π / 2) 20 := by
  obtain ⟨x, hx, hpx, -⟩ := BinetEnvelope.threshold_one_loc
  have hstep : tilt (Real.log π / 2) ((19 : ℕ) : ℝ) < tilt (Real.log π / 2) (((19 : ℕ) : ℝ) + 1) := by
    rw [show ((19 : ℕ) : ℝ) + 1 = ((20 : ℕ) : ℝ) by norm_num, tilt_natCast, tilt_natCast]
    have hl := Real.log_lt_log (Part0.Om_pos 19) step_19_20
    rw [Real.log_mul (Part0.Om_pos 20).ne' (Real.sqrt_pos.2 Real.pi_pos).ne',
      Real.log_sqrt Real.pi_pos.le] at hl
    push_cast
    linarith
  have h := tilt_lattice_max_up (m := 19) (by linarith [hx.1]) hpx (by push_cast; linarith [hx.1])
    (by push_cast; linarith [hx.2]) hstep
  intro d hd
  have := h d hd
  rwa [show ((19 : ℕ) : ℝ) + 1 = 20 by norm_num] at this

/-- `F_{√π}` is largest on the lattice at `d = 218`. -/
theorem lattice_two : ∀ d : ℕ, d ≠ 218 → tilt √π d < tilt √π 218 := by
  obtain ⟨x, hx, hpx, -⟩ := BinetEnvelope.threshold_two_loc
  have hstep : tilt √π ((217 : ℕ) : ℝ) < tilt √π (((217 : ℕ) : ℝ) + 1) := by
    rw [show ((217 : ℕ) : ℝ) + 1 = ((218 : ℕ) : ℝ) by norm_num, tilt_natCast, tilt_natCast]
    have hl := Real.log_lt_log (Part0.Om_pos 217) step_217_218
    rw [Real.log_mul (Part0.Om_pos 218).ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    push_cast
    linarith
  have h := tilt_lattice_max_up (m := 217) (by linarith [hx.1]) hpx (by push_cast; linarith [hx.1])
    (by push_cast; linarith [hx.2]) hstep
  intro d hd
  have := h d hd
  rwa [show ((217 : ℕ) : ℝ) + 1 = 218 by norm_num] at this

/-- **The landmarks on the lattice.** Each continuous landmark is the maximum of one function (`V` for the volume
landmark, `F₀ = log Ω`, `F_{½ log π}` and `F_{√π}` for the three crossings); the integer maxima of the same four
functions are `5`, `6`, `20` and `218`. -/
theorem lattice_dimensions :
    (∀ n : ℕ, n ≠ 5 → BallTower.ballVol n < BallTower.ballVol 5) ∧
    (∀ d : ℕ, d ≠ 6 → tilt 0 d < tilt 0 6) ∧
    (∀ d : ℕ, d ≠ 20 → tilt (Real.log π / 2) d < tilt (Real.log π / 2) 20) ∧
    (∀ d : ℕ, d ≠ 218 → tilt √π d < tilt √π 218) :=
  ⟨BallTower.ballVol_lt_five, lattice_zero, lattice_one, lattice_two⟩

/-- **The continuous crossings maximize the same functions** on `x > −1`. -/
theorem crossings_maximize :
    (∃ x ∈ Ioo (6.2569 : ℝ) 6.25695, Part0.pR x = 0 ∧ ∀ y, -1 < y → y ≠ x → tilt 0 y < tilt 0 x) ∧
    (∃ x ∈ Ioo (19.73075 : ℝ) 19.73085, Part0.pR x = Real.log π / 2 ∧
      ∀ y, -1 < y → y ≠ x → tilt (Real.log π / 2) y < tilt (Real.log π / 2) x) ∧
    (∃ x ∈ Ioo (217.62665 : ℝ) 217.62675, Part0.pR x = √π ∧
      ∀ y, -1 < y → y ≠ x → tilt √π y < tilt √π x) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, h0, -⟩ := BinetEnvelope.zero_loc
    exact ⟨x, hx, h0, tilt_max (by linarith [hx.1]) h0⟩
  · obtain ⟨x, hx, h0, -⟩ := BinetEnvelope.threshold_one_loc
    exact ⟨x, hx, h0, tilt_max (by linarith [hx.1]) h0⟩
  · obtain ⟨x, hx, h0, -⟩ := BinetEnvelope.threshold_two_loc
    exact ⟨x, hx, h0, tilt_max (by linarith [hx.1]) h0⟩

/-- Part 0's characterisation (b) of `d₀` names the sphere `S⁶`: `B⁷` is the ball with the largest boundary, and that
boundary's area is `Ω₆`, which exceeds `Ω₇`. -/
theorem max_boundary_is_six :
    BallTower.sphereArea 7 = Part0.Om 6 ∧ (∀ n : ℕ, n ≠ 7 → BallTower.sphereArea n < Part0.Om 6) ∧
      Part0.Om 7 < Part0.Om 6 :=
  ⟨rfl, BallTower.sphereArea_lt_seven, Part0.Om_five_lt_seven_lt_six.2⟩

/-! ## Rounding -/

/-- **Floor, ceiling and nearest integer of the four landmarks.** With `x` the zero of `p` and `x₁`, `x₂` the two
threshold crossings (the volume maximum sits at `x − 1`, round 412's `three_landmarks`). -/
theorem roundings : ∃ x x1 x2 : ℝ, Part0.pR x = 0 ∧ Part0.pR x1 = Real.log π / 2 ∧ Part0.pR x2 = √π ∧
    (⌊x - 1⌋₊ = 5 ∧ ⌊x⌋₊ = 6 ∧ ⌊x1⌋₊ = 19 ∧ ⌊x2⌋₊ = 217) ∧
    (⌈x - 1⌉₊ = 6 ∧ ⌈x⌉₊ = 7 ∧ ⌈x1⌉₊ = 20 ∧ ⌈x2⌉₊ = 218) ∧
    (round (x - 1) = 5 ∧ round x = 6 ∧ round x1 = 20 ∧ round x2 = 218) := by
  obtain ⟨x, ⟨a, b⟩, h0, -⟩ := BinetEnvelope.zero_loc
  obtain ⟨x1, ⟨a1, b1⟩, h1, -⟩ := BinetEnvelope.threshold_one_loc
  obtain ⟨x2, ⟨a2, b2⟩, h2, -⟩ := BinetEnvelope.threshold_two_loc
  refine ⟨x, x1, x2, h0, h1, h2, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  all_goals first
    | (rw [Nat.floor_eq_iff (by linarith)]; constructor <;> norm_num <;> linarith)
    | (rw [Nat.ceil_eq_iff (by norm_num)]; constructor <;> norm_num <;> linarith)
    | (rw [round_eq, Int.floor_eq_iff]; constructor <;> norm_num <;> linarith)

/-! ## The mirror weights -/

/-- The mirror weight `2/Γ_ℝ(−d)` of layer `d`: round 98's branch-swapped weight. At even `d`, `1/Γ` vanishes at
`Γ`'s pole, so the true value is `0`; Mathlib's `Γ(−n) = 0` and `x/0 = 0` give the same value. -/
def mirrorW (d : ℕ) : ℝ := 2 / BinetEnvelope.gammaR (-(d : ℝ))

/-- The mirror weight of layer `d` is nonzero exactly when `d` is odd. -/
theorem mirrorW_ne_zero_iff (d : ℕ) : mirrorW d ≠ 0 ↔ Odd d := by
  unfold mirrorW BinetEnvelope.gammaR
  constructor
  · intro h
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨k, rfl⟩ := hodd
    apply h
    have hG : Real.Gamma (-(((k + k : ℕ) : ℝ)) / 2) = 0 := by
      rw [show -(((k + k : ℕ) : ℝ)) / 2 = -((k : ℕ) : ℝ) by push_cast; ring]
      exact Real.Gamma_neg_nat_eq_zero k
    rw [hG, mul_zero, div_zero]
  · rintro ⟨k, rfl⟩
    have hG : Real.Gamma (-(((2 * k + 1 : ℕ) : ℝ)) / 2) ≠ 0 := by
      apply Real.Gamma_ne_zero
      intro m hm
      push_cast at hm
      have h2 : ((2 * k + 1 : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; linarith
      have h3 : 2 * k + 1 = 2 * m := by exact_mod_cast h2
      omega
    have hp : (0 : ℝ) < π ^ (-(-(((2 * k + 1 : ℕ) : ℝ))) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    exact div_ne_zero two_ne_zero (mul_ne_zero hp.ne' hG)

/-- **The per-label clause picks the odd member of each pair:** among `{5, 6}`, `{6, 7}`, `{19, 20}` and
`{217, 218}`, the members with nonzero mirror weight are `5`, `7`, `19` and `217`. -/
theorem mirror_selects :
    (mirrorW 5 ≠ 0 ∧ mirrorW 6 = 0) ∧ (mirrorW 7 ≠ 0 ∧ mirrorW 6 = 0) ∧
      (mirrorW 19 ≠ 0 ∧ mirrorW 20 = 0) ∧ (mirrorW 217 ≠ 0 ∧ mirrorW 218 = 0) := by
  have z : ∀ d : ℕ, Even d → mirrorW d = 0 := fun d hd => by
    by_contra h
    exact (Nat.not_odd_iff_even.2 hd) ((mirrorW_ne_zero_iff d).1 h)
  have nz : ∀ d : ℕ, Odd d → mirrorW d ≠ 0 := fun d hd => (mirrorW_ne_zero_iff d).2 hd
  refine ⟨⟨nz 5 ?_, z 6 ?_⟩, ⟨nz 7 ?_, z 6 ?_⟩, ⟨nz 19 ?_, z 20 ?_⟩, ⟨nz 217 ?_, z 218 ?_⟩⟩ <;> decide

/-! ## The invariant at the lattice labels -/

theorem cascadeInv_lattice_closed : Part0.cascadeInv 6 20 218
    = (225 * 2 ^ 232 * (Nat.factorial 10 : ℝ) * (Nat.factorial 109 : ℝ)) * π ^ 119
      / ((Nat.factorial 20 : ℝ) * (Nat.factorial 218 : ℝ)) := by
  unfold Part0.cascadeInv
  rw [Part0.Om_five, Part0.Om_six, Om_twenty, Om_two_eighteen]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The invariant at the lattice labels** `(6, 20, 218)`: `1.0216 × 10⁻¹²¹ < (Ω₅/Ω₆)²Ω₂₀Ω₂₁₈ < 1.0218 × 10⁻¹²¹`. -/
theorem cascadeInv_lattice_bounds :
    (1.0216e-121 : ℝ) < Part0.cascadeInv 6 20 218 ∧ Part0.cascadeInv 6 20 218 < 1.0218e-121 := by
  rw [cascadeInv_lattice_closed]
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hl : (3.141592 : ℝ) ^ 119 < π ^ 119 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hu : π ^ 119 < (3.141593 : ℝ) ^ 119 := pow_lt_pow_left₀ h2 Real.pi_pos.le (by norm_num)
  have hF : (0 : ℝ) < (Nat.factorial 20 : ℝ) * (Nat.factorial 218 : ℝ) := by positivity
  have hK : (0 : ℝ) < 225 * 2 ^ 232 * (Nat.factorial 10 : ℝ) * (Nat.factorial 109 : ℝ) := by positivity
  constructor
  · rw [lt_div_iff₀ hF]
    have : (1.0216e-121 : ℝ) * ((Nat.factorial 20 : ℝ) * (Nat.factorial 218 : ℝ))
        < (225 * 2 ^ 232 * (Nat.factorial 10 : ℝ) * (Nat.factorial 109 : ℝ)) * 3.141592 ^ 119 := by
      norm_num
    have := mul_lt_mul_of_pos_left hl hK
    linarith
  · rw [div_lt_iff₀ hF]
    have : (225 * 2 ^ 232 * (Nat.factorial 10 : ℝ) * (Nat.factorial 109 : ℝ)) * 3.141593 ^ 119
        < (1.0218e-121 : ℝ) * ((Nat.factorial 20 : ℝ) * (Nat.factorial 218 : ℝ)) := by
      norm_num
    have := mul_lt_mul_of_pos_left hu hK
    linarith

/-- **Part 0's value over the lattice value:** `10.75 < I(7, 19, 217)/I(6, 20, 218) < 10.76`. -/
theorem paper_over_lattice :
    10.75 * Part0.cascadeInv 6 20 218 < Part0.cascadeInv 7 19 217 ∧
      Part0.cascadeInv 7 19 217 < 10.76 * Part0.cascadeInv 6 20 218 := by
  have h1 := Part0.cascadeInv_bounds
  have h2 := cascadeInv_lattice_bounds
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end BoundaryLabels
#print axioms BoundaryLabels.hasDerivAt_tilt
#print axioms BoundaryLabels.tilt_strictMonoOn
#print axioms BoundaryLabels.tilt_strictAntiOn
#print axioms BoundaryLabels.tilt_max
#print axioms BoundaryLabels.tilt_natCast
#print axioms BoundaryLabels.tilt_lattice_max_up
#print axioms BoundaryLabels.tilt_lattice_max_down
#print axioms BoundaryLabels.Om_even
#print axioms BoundaryLabels.Om_nineteen
#print axioms BoundaryLabels.Om_twenty
#print axioms BoundaryLabels.Om_two_seventeen
#print axioms BoundaryLabels.Om_two_eighteen
#print axioms BoundaryLabels.step_19_20
#print axioms BoundaryLabels.step_217_218
#print axioms BoundaryLabels.lattice_zero
#print axioms BoundaryLabels.lattice_one
#print axioms BoundaryLabels.lattice_two
#print axioms BoundaryLabels.lattice_dimensions
#print axioms BoundaryLabels.crossings_maximize
#print axioms BoundaryLabels.max_boundary_is_six
#print axioms BoundaryLabels.roundings
#print axioms BoundaryLabels.mirrorW_ne_zero_iff
#print axioms BoundaryLabels.mirror_selects
#print axioms BoundaryLabels.cascadeInv_lattice_closed
#print axioms BoundaryLabels.cascadeInv_lattice_bounds
#print axioms BoundaryLabels.paper_over_lattice
