import Mathlib
import SwapRealize
import ParabolaGap

/-! # Simplicity of the ground state: small supports, and covering intervals of supports

Round 46 reduced the chain to `(a) + eventual simplicity ⇒ RH`. This file does two things.

1. **Every support `0 < a ≤ 0.36` has a simple ground state** (`simpleGround_036`), from the certified
   gap of ParabolaGap.lean and the passage "unique up to sign ⇒ simple" (`simpleGround_of_unique`).
2. **Monotone covering.** Enlarging the support enlarges the probe class. So `λ₁(a)` is nonincreasing
   (`lam_antitone`), and so is every lower bound on the second min–max value (`Lam2Ge.mono`). Hence a
   single inequality `λ₁(a₀) < s ≤ λ₂(a₁)` gives simplicity at **every** `a ∈ [a₀, a₁]`
   (`simpleGround_of_cover`). Finitely many point certificates therefore cover an interval.

`Lam2Ge a s` is the min–max statement `λ₂(a) ≥ s` in the even sector: every orthonormal pair of
probes spans a unit vector with `Q ≥ s`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## Unique up to sign ⇒ simple -/

theorem simpleGround_of_unique {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hu : ∀ h, IsGroundState a h → h =ᵐ[volume] g ∨ h =ᵐ[volume] fun t => -g t) :
    SimpleGround a g := by
  refine ⟨hg, fun h hh => ?_⟩
  have hp : Probe a h := hh.1
  by_cases h0 : normSq h = 0
  · refine ⟨0, ?_⟩
    filter_upwards [ae_zero_of_normSq hp.memL2 h0] with t ht
    simp [ht]
  · have hpos : 0 < normSq h := lt_of_le_of_ne (normSq_nonneg h) (Ne.symm h0)
    set c := Real.sqrt (normSq h) with hc
    have hc0 : 0 < c := Real.sqrt_pos.2 hpos
    have hcsq : c ^ 2 = normSq h := Real.sq_sqrt hpos.le
    set h' : ℝ → ℝ := fun t => c⁻¹ * h t with hh'
    have hmem : h' ∈ groundSpace a := groundSpace_fun hh c⁻¹
    have hn : normSq h' = 1 := by
      rw [hh', normSq_smul, inv_pow, hcsq, inv_mul_cancel₀ h0]
    have hgs : IsGroundState a h' := (isGroundState_iff ha).2 ⟨hmem, hn⟩
    have hback : h = fun t => c * h' t := by
      funext t; simp only [hh']; field_simp
    rcases hu h' hgs with e | e
    · refine ⟨c, ?_⟩
      rw [hback]; filter_upwards [e] with t ht; rw [ht]
    · refine ⟨-c, ?_⟩
      rw [hback]; filter_upwards [e] with t ht; rw [ht]; ring

/-- **Every support `0 < a ≤ 0.36` has simple ground states.** -/
theorem simpleGround_036 {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 0.36) {g : ℝ → ℝ}
    (hg : IsGroundState a g) : SimpleGround a g :=
  simpleGround_of_unique ha hg fun _ hh => groundState_unique_036 ha ha2 hh hg

/-! ## Monotonicity in the support -/

/-- **`λ₁` is nonincreasing in the support.** -/
theorem lam_antitone {a a₁ : ℝ} (ha : 0 < a) (h : a ≤ a₁) : lam a₁ ≤ lam a := by
  refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
  rintro q ⟨g, hp, hn, rfl⟩
  rw [← weilQ_mono ha.le h hp]
  exact lam_le (hp.mono h) hn

/-- `λ₂(a) ≥ s` in min–max form (even sector): every orthonormal pair of probes spans a unit vector
with `Q ≥ s`. -/
def Lam2Ge (a s : ℝ) : Prop :=
  ∀ g h : ℝ → ℝ, Probe a g → Probe a h → normSq g = 1 → normSq h = 1 → xcorr g h 0 = 0 →
    ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧ s ≤ weilQ a (fun t => α * g t + β * h t)

theorem Lam2Ge.mono {a a₁ s : ℝ} (ha : 0 ≤ a) (hle : a ≤ a₁) (H : Lam2Ge a₁ s) : Lam2Ge a s := by
  intro g h hg hh hng hnh hx
  obtain ⟨α, β, hab, hs⟩ := H g h (hg.mono hle) (hh.mono hle) hng hnh hx
  refine ⟨α, β, hab, ?_⟩
  have hc : Probe a (fun t => α * g t + β * h t) := by
    have := probe_add_smul (probe_smul hg α) hh β
    simpa using this
  rwa [← weilQ_mono ha hle hc]

/-! ## The covering criterion -/

theorem normSq_comb {g h : ℝ → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (α β : ℝ) :
    normSq (fun t => α * g t + β * h t)
      = α ^ 2 * normSq g + 2 * α * β * xcorr g h 0 + β ^ 2 * normSq h := by
  have e := normSq_add_smul (hg.const_mul α) (hh.const_mul β) 1
  have ex : xcorr (fun t => α * g t) (fun t => β * h t) 0 = α * β * xcorr g h 0 := by
    rw [xcorr_zero_eq, xcorr_zero_eq, ← integral_const_mul]
    congr 1; funext t; ring
  simp only [one_mul] at e
  rw [e, ex, normSq_smul, normSq_smul]; ring

/-- **Simplicity from `λ₁ < s ≤ λ₂`.** -/
theorem simpleGround_of_lam2 {a s : ℝ} (ha : 0 < a) (hl : lam a < s) (H : Lam2Ge a s)
    {g : ℝ → ℝ} (hg : IsGroundState a g) : SimpleGround a g := by
  refine ⟨hg, fun h hh => ?_⟩
  have hgm : g ∈ groundSpace a := ((isGroundState_iff ha).1 hg).1
  have hp : Probe a h := hh.1
  obtain ⟨c, hc⟩ : ∃ c, c = xcorr h g 0 := ⟨_, rfl⟩
  set h' : ℝ → ℝ := fun t => h t + (-c) * g t with hh'
  have hmem' : h' ∈ groundSpace a := by
    have := (groundSpace a).add_mem hh ((groundSpace a).smul_mem (-c) hgm)
    convert this using 1
  -- `h' ⊥ g`, from two instances of `normSq_add_smul`
  have n0 := normSq_add_smul hp.memL2 hg.1.memL2 (-c)
  have hp' : Probe a h' := hmem'.1
  have n1 := normSq_add_smul hp'.memL2 hg.1.memL2 1
  have n2 := normSq_add_smul hp.memL2 hg.1.memL2 (1 - c)
  have eqf : (fun t => h' t + 1 * g t) = fun t => h t + (1 - c) * g t := by
    funext t; simp only [hh']; ring
  rw [eqf, n2] at n1
  rw [← hh'] at n0
  have hgn := hg.2.1
  rw [← hc] at n0 n1
  have hx' : xcorr h' g 0 = 0 := by
    rw [hgn] at n0 n1; linear_combination (-(1 : ℝ) / 2) * n1 + (-(1 : ℝ) / 2) * n0
  by_cases h0 : normSq h' = 0
  · refine ⟨c, ?_⟩
    filter_upwards [ae_zero_of_normSq hp'.memL2 h0] with t ht
    have : h t + (-c) * g t = 0 := by simpa [hh'] using ht
    linarith
  · exfalso
    have hpos : 0 < normSq h' := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
    set k := (Real.sqrt (normSq h'))⁻¹
    have hk : k ^ 2 * normSq h' = 1 := by
      simp only [k, inv_pow, Real.sq_sqrt hpos.le]; exact inv_mul_cancel₀ h0
    set h'' : ℝ → ℝ := fun t => k * h' t
    have hm'' : h'' ∈ groundSpace a := groundSpace_fun hmem' k
    have hn'' : normSq h'' = 1 := by simp only [h'', normSq_smul]; exact hk
    have hx'' : xcorr g h'' 0 = 0 := by
      rw [xcorr_zero_eq]; simp only [h'']
      have : (fun t => g t * (k * h' t)) = fun t => k * (h' t * g t) := by funext t; ring
      rw [this, integral_const_mul, ← xcorr_zero_eq, hx', mul_zero]
    obtain ⟨α, β, hab, hs⟩ := H g h'' hg.1 hm''.1 hgn hn'' hx''
    have hcomb : (fun t => α * g t + β * h'' t) ∈ groundSpace a := by
      have := (groundSpace a).add_mem ((groundSpace a).smul_mem α hgm)
        ((groundSpace a).smul_mem β hm'')
      convert this using 1
    have hq := hcomb.2
    have hN : normSq (fun t => α * g t + β * h'' t) = 1 := by
      rw [normSq_comb hg.1.memL2 hm''.1.memL2, hgn, hn'', hx'']; linarith
    rw [hq, hN, mul_one] at hs
    linarith

/-- **Monotone covering.** `λ₁(a₀) < s` and `λ₂(a₁) ≥ s` give simple ground states at every
support in `[a₀, a₁]`. -/
theorem simpleGround_of_cover {a₀ a₁ s : ℝ} (ha₀ : 0 < a₀) (hl : lam a₀ < s) (H : Lam2Ge a₁ s)
    {a : ℝ} (h0 : a₀ ≤ a) (h1 : a ≤ a₁) {g : ℝ → ℝ} (hg : IsGroundState a g) :
    SimpleGround a g :=
  simpleGround_of_lam2 (ha₀.trans_le h0) ((lam_antitone ha₀ h0).trans_lt hl)
    (H.mono (ha₀.le.trans h0) h1) hg

/-- **A chain of cells.** If the nodes `a₀, a₁, …, a_{m+1}` are positive and consecutive nodes satisfy
`λ₁(a_i) < s_i ≤ λ₂(a_{i+1})`, every support in `[a₀, a_{m+1}]` has simple ground states. -/
theorem simpleGround_of_chain (node s : ℕ → ℝ) (hpos : ∀ i, 0 < node i) (m : ℕ)
    (hl : ∀ i ≤ m, lam (node i) < s i) (H : ∀ i ≤ m, Lam2Ge (node (i + 1)) (s i))
    {a : ℝ} (h0 : node 0 ≤ a) (h1 : a ≤ node (m + 1)) {g : ℝ → ℝ} (hg : IsGroundState a g) :
    SimpleGround a g := by
  induction m generalizing a with
  | zero => exact simpleGround_of_cover (hpos 0) (hl 0 le_rfl) (H 0 le_rfl) h0 h1 hg
  | succ m ih =>
    by_cases hc : a ≤ node (m + 1)
    · exact ih (fun i hi => hl i (by omega)) (fun i hi => H i (by omega)) h0 hc hg
    · exact simpleGround_of_cover (hpos (m + 1)) (hl (m + 1) le_rfl) (H (m + 1) le_rfl)
        (le_of_lt (not_le.mp hc)) h1 hg

/-! ## Round 47's certificates, and simplicity for every support `0 < a ≤ 1.035`

The nodes are `a = 0.36, 0.51, 0.64, 0.75, 0.85, 0.935, 1.01, 1.035` (support `δ = 2a` up to `2.07`).
`Round47Certs` lists the fourteen computer-assisted inequalities of `frontier/simplicity_cover/`:
* upper bounds `λ₁(a_i) < s_i` are ball Rayleigh quotients of cosine trial vectors, computed at a support
  slightly below the node (valid at the node by `lam_antitone`);
* lower bounds `λ₂(a_{i+1}) ≥ s_i` are Zhu's one-stroke reduction with a ball-arithmetic inertia count.

They are stated as a hypothesis: Lean checks the logic, not the numerics. -/

/-- The certified inequalities of round 47 (computer-assisted, not checked in Lean). -/
def Round47Certs : Prop :=
  lam 0.36 < 1 / 100 ∧ Lam2Ge 0.51 (1 / 100) ∧
  lam 0.51 < 6e-6 ∧ Lam2Ge 0.64 6e-6 ∧
  lam 0.64 < 1e-9 ∧ Lam2Ge 0.75 1e-9 ∧
  lam 0.75 < 2.7e-14 ∧ Lam2Ge 0.85 2.7e-14 ∧
  lam 0.85 < 4.9e-19 ∧ Lam2Ge 0.935 4.9e-19 ∧
  lam 0.935 < 3e-24 ∧ Lam2Ge 1.01 3e-24 ∧
  lam 1.01 < 4e-26 ∧ Lam2Ge 1.035 4e-26

/-- **Simplicity at every support `0 < a ≤ 1.035`** (`δ ≤ 2.07`), given round 47's certificates:
`a ≤ 0.36` is `simpleGround_036` (proved in Lean); the rest is seven covering cells. -/
theorem simpleGround_le_1035 (hc : Round47Certs) {a : ℝ} (ha : 0 < a) (h : a ≤ 1.035)
    {g : ℝ → ℝ} (hg : IsGroundState a g) : SimpleGround a g := by
  obtain ⟨c0, d0, c1, d1, c2, d2, c3, d3, c4, d4, c5, d5, c6, d6⟩ := hc
  by_cases h0 : a ≤ 0.36
  · exact simpleGround_036 ha h0 hg
  push Not at h0
  by_cases h1 : a ≤ 0.51
  · exact simpleGround_of_cover (by norm_num) c0 d0 h0.le h1 hg
  push Not at h1
  by_cases h2 : a ≤ 0.64
  · exact simpleGround_of_cover (by norm_num) c1 d1 h1.le h2 hg
  push Not at h2
  by_cases h3 : a ≤ 0.75
  · exact simpleGround_of_cover (by norm_num) c2 d2 h2.le h3 hg
  push Not at h3
  by_cases h4 : a ≤ 0.85
  · exact simpleGround_of_cover (by norm_num) c3 d3 h3.le h4 hg
  push Not at h4
  by_cases h5 : a ≤ 0.935
  · exact simpleGround_of_cover (by norm_num) c4 d4 h4.le h5 hg
  push Not at h5
  by_cases h6 : a ≤ 1.01
  · exact simpleGround_of_cover (by norm_num) c5 d5 h5.le h6 hg
  push Not at h6
  exact simpleGround_of_cover (by norm_num) c6 d6 h6.le h hg

end Pilot1ca

#print axioms Pilot1ca.simpleGround_of_unique
#print axioms Pilot1ca.simpleGround_036
#print axioms Pilot1ca.lam_antitone
#print axioms Pilot1ca.simpleGround_of_lam2
#print axioms Pilot1ca.simpleGround_of_cover
#print axioms Pilot1ca.simpleGround_of_chain
#print axioms Pilot1ca.simpleGround_le_1035
