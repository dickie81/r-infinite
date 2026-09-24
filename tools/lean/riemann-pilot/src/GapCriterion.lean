import Mathlib
import SimpleStructure

/-! # The energy-gap criterion, the pole-overlap identity, and the Jacobi lemma (rounds 49–50, formal)

* `euler_lagrange_Q`: a ground state `g` of `Q` satisfies `B₀(g, ψ) + 2 ĝ(i/2) ψ̂(i/2) = λ₁⟨g, ψ⟩`
  for every probe `ψ`.
* `pole_overlap_identity` (round 49): if `ψ` solves `Q₀`'s weak eigen-equation at level `μ`, then
  `2 ĝ(i/2) ψ̂(i/2) = (λ₁ − μ)⟨g, ψ⟩`.
* `lam_le_of_perp` (interlacing): `λ₁(Q) ≤ Q₀(ψ)` for every normalised probe `ψ ⊥ φ₀`, so
  `λ₁(Q) ≤ μ₂(Q₀)`.
* `simpleGround_of_gap`: the strict energy gap `λ₁(Q) < Q₀(ψ)` on the unit sphere of `φ₀^⊥` gives a
  simple ground state. `not_simple_gap` is the converse information: without simplicity, `λ₁(Q)` is
  attained by `Q₀` on `φ₀^⊥`, so it equals `μ₂(Q₀)`.
* `jacobi_eigvec_unique` (round 50): for a Jacobi recurrence with nonzero off-diagonals, the
  eigen-solutions at a given level form a line. This is the finite-dimensional fact behind the
  rotation to the pole's Krylov basis.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## Euler–Lagrange for `Q`, and the overlap identity -/

theorem euler_lagrange_Q {a : ℝ} (ha : 0 < a) {g ψ : ℝ → ℝ} (hg : IsGroundState a g)
    (hψ : Probe a ψ) : bil0 a g ψ + 2 * poleR g a * poleR ψ a = lam a * xcorr g ψ 0 :=
  euler_lagrange_mem ⟨hg.1, ((isGroundState_iff ha).1 hg).1.2⟩ hψ

/-- **The pole-overlap identity** (round 49). -/
theorem pole_overlap_identity {a μ : ℝ} (ha : 0 < a) {g ψ : ℝ → ℝ} (hg : IsGroundState a g)
    (hψ : Probe a ψ) (heig : ∀ k, Probe a k → bil0 a ψ k = μ * xcorr ψ k 0) :
    2 * poleR g a * poleR ψ a = (lam a - μ) * xcorr g ψ 0 := by
  have e1 := euler_lagrange_Q ha hg hψ
  have e2 := heig g hg.1
  rw [bil0_comm, xcorr_comm] at e2
  linear_combination e1 - e2

/-! ## Interlacing and the gap criterion -/

/-- **The pole-free trial** `ψ + sφ`, `s = −ψ̂(i/2)/φ̂(i/2)`, for a normalised probe `ψ ⊥ φ₀`:
`λ₁(1 + s²) ≤ Q₀(ψ) + s²λ₀`. -/
theorem lam_le_perp_trial {a : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hφp : poleR φ a ≠ 0) (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) :
    lam a * (1 + (poleR ψ a / poleR φ a) ^ 2)
      ≤ weilQ0 a ψ + (poleR ψ a / poleR φ a) ^ 2 * lam0 a := by
  set s := -(poleR ψ a / poleR φ a)
  have hf := probe_add_smul hψ hφ.1 s
  have hpole : poleR (fun t => ψ t + s * φ t) a = 0 := by
    rw [poleR_add hψ.memL2 (hφ.1.memL2.const_mul s) a, poleR_smul]
    simp only [s]; field_simp; ring
  have hB : bil0 a ψ φ = 0 := by
    rw [bil0_comm, euler_lagrange0 ha hφ hψ, xcorr_comm, hx, mul_zero]
  have hQf : weilQ a (fun t => ψ t + s * φ t) = weilQ0 a ψ + s ^ 2 * lam0 a := by
    have : weilQ a (fun t => ψ t + s * φ t) = weilQ0 a (fun t => ψ t + s * φ t) := by
      unfold weilQ0; rw [hpole]; ring
    rw [this, weilQ0_add_smul hψ hφ.1, hB]
    have hq0 : weilQ0 a φ = lam0 a := by
      have := ((isGroundState0_iff ha).1 hφ).1.2; rw [this, hφ.2.1, mul_one]
    rw [hq0]; ring
  have hNf : normSq (fun t => ψ t + s * φ t) = 1 + s ^ 2 := by
    rw [normSq_add_smul hψ.memL2 hφ.1.memL2, hn, hx, hφ.2.1]; ring
  have h := lam_mul_le hf
  rw [hQf, hNf] at h
  have e : s ^ 2 = (poleR ψ a / poleR φ a) ^ 2 := by simp only [s]; ring
  rwa [e] at h

/-- **Interlacing**: `λ₁(Q) ≤ Q₀(ψ)` for every normalised probe orthogonal to a ground state of `Q₀`
with nonzero pole value. -/
theorem lam_le_of_perp {a : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hφp : poleR φ a ≠ 0) (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) :
    lam a ≤ weilQ0 a ψ := by
  have h := lam_le_perp_trial ha hφ hφp hψ hn hx
  have h0 := lam0_le_lam ha
  nlinarith [sq_nonneg (poleR ψ a / poleR φ a)]

/-- The strict energy gap at support `2a`: `Q₀ > λ₁(Q)` on the unit sphere of `φ₀^⊥`. -/
def EnergyGap (a : ℝ) : Prop :=
  ∀ φ, IsGroundState0 a φ → ∀ v, Probe a v → normSq v = 1 → xcorr v φ 0 = 0 → lam a < weilQ0 a v

/-- **Energy gap ⇒ simplicity.** -/
theorem simpleGround_of_gap {a : ℝ} (ha : 0 < a) (hgap : EnergyGap a) {g : ℝ → ℝ}
    (hg : IsGroundState a g) : SimpleGround a g := by
  obtain ⟨-, φ, hφ, -, -, -, hcase⟩ := groundState_unique_or_excited ha
  rcases hcase with huniq | ⟨v, hv, -, hvφ, hq0, -⟩
  · refine simpleGround_of_unique ha hg fun h hh => ?_
    rcases huniq h g hh hg with e | e
    · exact Or.inl e
    · exact Or.inr e
  · exfalso
    have hx : xcorr v φ 0 = 0 := by rw [xcorr_zero_eq]; exact hvφ
    have := hgap φ hφ v hv.1 hv.2.1 hx
    linarith

/-- **Without simplicity, the gap closes exactly**: there is a positive ground state `φ₀` of `Q₀` and a
normalised `v ⊥ φ₀` with `Q₀(v) = λ₁(Q)`, while `λ₁(Q) ≤ Q₀(ψ)` for every normalised `ψ ⊥ φ₀`. So
`λ₁(Q) = min_{φ₀^⊥} Q₀ = μ₂(Q₀)`, attained. -/
theorem not_simple_gap {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hns : ¬ SimpleGround a g) :
    ∃ φ, IsGroundState0 a φ ∧ (∀ t, 0 ≤ φ t) ∧ 0 < poleR φ a ∧
      (∃ v, Probe a v ∧ normSq v = 1 ∧ xcorr v φ 0 = 0 ∧ weilQ0 a v = lam a) ∧
      ∀ ψ, Probe a ψ → normSq ψ = 1 → xcorr ψ φ 0 = 0 → lam a ≤ weilQ0 a ψ := by
  obtain ⟨-, φ, hφ, h0, -, hpos, hcase⟩ := groundState_unique_or_excited ha
  refine ⟨φ, hφ, h0, hpos, ?_, fun ψ hψ hn hx => lam_le_of_perp ha hφ hpos.ne' hψ hn hx⟩
  rcases hcase with huniq | ⟨v, hv, -, hvφ, hq0, -⟩
  · exfalso; apply hns
    refine simpleGround_of_unique ha hg fun h hh => ?_
    rcases huniq h g hh hg with e | e
    · exact Or.inl e
    · exact Or.inr e
  · exact ⟨v, hv.1, hv.2.1, by rw [xcorr_zero_eq]; exact hvφ, hq0⟩

/-! ## The Jacobi lemma -/

/-- `v` solves the eigen-recurrence of the `n × n` Jacobi matrix with diagonal `d` and off-diagonal
`b` at level `l`. -/
def JacobiEig (n : ℕ) (d b : ℕ → ℝ) (l : ℝ) (v : ℕ → ℝ) : Prop :=
  (1 < n → d 0 * v 0 + b 0 * v 1 = l * v 0) ∧
    ∀ k, k + 2 < n → b k * v k + d (k + 1) * v (k + 1) + b (k + 1) * v (k + 2) = l * v (k + 1)

theorem jacobi_zero {n : ℕ} {d b : ℕ → ℝ} {l : ℝ} {v : ℕ → ℝ} (hb : ∀ k, k + 1 < n → b k ≠ 0)
    (h : JacobiEig n d b l v) (h0 : v 0 = 0) : ∀ k, k < n → v k = 0 := by
  have step : ∀ k, k + 1 < n → v k = 0 ∧ v (k + 1) = 0 := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨h0, ?_⟩
      have e := h.1 hk
      rw [h0, mul_zero, zero_add, mul_zero] at e
      exact (mul_eq_zero.1 e).resolve_left (hb 0 hk)
    | succ k ih =>
      intro hk
      obtain ⟨e0, e1⟩ := ih (by omega)
      refine ⟨e1, ?_⟩
      have e := h.2 k (by omega)
      rw [e0, e1] at e
      simp only [mul_zero, zero_add] at e
      exact (mul_eq_zero.1 e).resolve_left (hb (k + 1) hk)
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact h0
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact (step j hk).2

/-- **Eigen-solutions of a Jacobi recurrence with nonzero off-diagonals form a line**: any two
satisfy `w₀·u = u₀·w`. -/
theorem jacobi_eigvec_unique {n : ℕ} {d b : ℕ → ℝ} {l : ℝ} {u w : ℕ → ℝ}
    (hb : ∀ k, k + 1 < n → b k ≠ 0) (hu : JacobiEig n d b l u) (hw : JacobiEig n d b l w) :
    ∀ k, k < n → w 0 * u k = u 0 * w k := by
  have hz : JacobiEig n d b l (fun k => w 0 * u k - u 0 * w k) := by
    refine ⟨fun h1 => ?_, fun k hk => ?_⟩
    · have e1 := hu.1 h1; have e2 := hw.1 h1
      linear_combination w 0 * e1 - u 0 * e2
    · have e1 := hu.2 k hk; have e2 := hw.2 k hk
      linear_combination w 0 * e1 - u 0 * e2
  intro k hk
  have := jacobi_zero hb hz (by ring) k hk
  linarith

end Pilot1ca

#print axioms Pilot1ca.euler_lagrange_Q
#print axioms Pilot1ca.pole_overlap_identity
#print axioms Pilot1ca.lam_le_of_perp
#print axioms Pilot1ca.simpleGround_of_gap
#print axioms Pilot1ca.not_simple_gap
#print axioms Pilot1ca.jacobi_eigvec_unique
