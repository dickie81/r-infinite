import HybridCertificate

/-! # Concrete instances of the hybrid certificate (round 276)

Small `ZeroBlockData` instances on which every hypothesis of `hybrid_cert`, `hybrid_cert_pairs`,
`hybrid_cert_of_moments`, `hybrid_cert_of_no_offline` and `hybrid_cert_eta_zero` is discharged, so none of them is
vacuous; and one instance on which the off-line term of `hybrid_cert` cannot be dropped.

* `D0`: one simple on-line zero (index 0) and one off-line pair (1 ↔ 2), `d = 1`, `v = 2 w0`. Instances of
  `hybrid_cert`, `hybrid_cert_pairs` and `hybrid_cert_of_moments` with `η = 1`, `g ≡ 1`, `u = w0`; of
  `hybrid_cert` with a base family `w1` that is not reflection-symmetric (`w1_not_symm`); of
  `hybrid_cert_eta_zero` at `c = 4`.
* `D1`: one on-line zero of multiplicity 2 and nothing else; an instance of `hybrid_cert_of_no_offline`.
* `D2`: one off-line pair and no on-line zero, `v ≡ 1 = w + η g u` with `w ≡ 10`, `u ≡ g ≡ 1`, `η = −9`, `c = 1`.
  `last_term_needed`: the bound of `hybrid_cert` WITHOUT its off-line term is false here (396 > 0 = s₁ + s₂);
  `with_last_term_value`: with it, the left side is exactly 0 = s₁ + s₂, so the bound is attained.
-/

noncomputable section

open Matrix Finset RHLinalg Zeta23.ZeroSide HybridCert

namespace HybridExamples

/-! ## `D0`: one on-line zero and one off-line pair -/

def w0 : Fin 3 → Fin 1 → ℂ := fun z _ => ![(1 : ℂ), Complex.I, -Complex.I] z
def σ0 : Fin 3 → Fin 3 := ![0, 2, 1]

lemma σ0_invol : Function.Involutive σ0 := by intro z; fin_cases z <;> rfl

lemma w0_σ : ∀ z, w0 (σ0 z) = star (w0 z) := by
  intro z; funext k; fin_cases z <;> simp [w0, σ0, Complex.conj_I]

def D0 : ZeroBlockData (Fin 3) (Fin 1) where
  m := fun _ => 1
  one_le_m := fun _ => le_rfl
  v := fun z => w0 z + w0 z
  σ := σ0
  σ_invol := σ0_invol
  m_σ := fun _ => rfl
  v_σ := fun z => by rw [w0_σ z, star_add]

def P0 : D0.PairReps where
  R := {1}
  off := by intro z hz; rw [Finset.mem_singleton] at hz; subst hz; decide
  σ_not_mem := by intro z hz; rw [Finset.mem_singleton] at hz; subst hz; decide
  cover := by decide

example : D0.s₁ + D0.s₂ = 1 := by decide
example : D0.Ncount = 3 := by decide
example : D0.onLineᶜ = {1, 2} := by decide

def g0 : Fin 3 → ℂ := fun _ => 1

lemma hv0 : ∀ z, D0.v z = w0 z + (((1 : ℝ) : ℂ) * g0 z) • w0 z := by
  intro z; simp [D0, g0]

lemma hPois0 : ∀ z ∈ D0.onLine, ∑ k, ‖w0 z k‖ ^ 2 ≤ (1 : ℝ) := by
  intro z hz
  rw [ZeroBlockData.mem_onLine] at hz
  fin_cases z
  · simp [w0]
  · exact absurd hz (by decide)
  · exact absurd hz (by decide)

theorem instance_hybrid :
    4 * (1 : ℝ)⁻¹ * Aw D0 w0 + 2 * (1 : ℝ)⁻¹ * Ag D0 w0 w0 g0 1 - 2 * (D0.Ncount : ℝ)
      - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D0.blockA)
      + 2 * (1 : ℝ)⁻¹ * ∑ z ∈ D0.onLineᶜ, (D0.m z : ℝ) * (G w0 w0 g0 1 z).re
      ≤ ((D0.s₁ + D0.s₂ : ℕ) : ℝ) :=
  hybrid_cert D0 (c := 1) one_pos hv0 hPois0

theorem instance_pairs :
    4 * (1 : ℝ)⁻¹ * Aw D0 w0 + 2 * (1 : ℝ)⁻¹ * Ag D0 w0 w0 g0 1 - 2 * (D0.Ncount : ℝ)
      - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D0.blockA)
      + 4 * (1 : ℝ)⁻¹ * ∑ z ∈ P0.R, (D0.m z : ℝ) * (G w0 w0 g0 1 z).re
      ≤ ((D0.s₁ + D0.s₂ : ℕ) : ℝ) :=
  hybrid_cert_pairs D0 P0 (c := 1) one_pos hv0 w0_σ hPois0

/-- The first-order input of `hybrid_cert_of_moments`, taken with equality. -/
def E1v : ℝ := -(2 * (1 : ℝ) * ∑ z ∈ D0.onLineᶜ, (D0.m z : ℝ) * (g0 z * (w0 z ⬝ᵥ w0 z)).re)

/-- The second-order input of `hybrid_cert_of_moments`, taken with equality. -/
def E2v : ℝ := -∑ z ∈ D0.onLineᶜ, (D0.m z : ℝ) * (g0 z ^ 2 * (w0 z ⬝ᵥ w0 z)).re

theorem instance_moments :
    4 * (1 : ℝ)⁻¹ * Aw D0 w0 + 2 * (1 : ℝ)⁻¹ * Ag D0 w0 w0 g0 1 - 2 * (1 : ℝ)⁻¹ * (E1v + (1 : ℝ) ^ 2 * E2v)
      - 2 * (D0.Ncount : ℝ) - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D0.blockA) ≤ ((D0.s₁ + D0.s₂ : ℕ) : ℝ) :=
  hybrid_cert_of_moments D0 (c := 1) one_pos hv0 hPois0 (by simp [E1v]) (by simp [E2v])

/-- A base family that is not reflection-symmetric: `hybrid_cert` assumes no symmetry. -/
def w1 : Fin 3 → Fin 1 → ℂ := fun z _ => ![(1 : ℂ), 1, 0] z
def u1 : Fin 3 → Fin 1 → ℂ := fun z => D0.v z - w1 z

lemma w1_not_symm : ¬ ∀ z, w1 (D0.σ z) = star (w1 z) := by
  intro h
  have := congrFun (h 1) 0
  simp [w1, D0, σ0] at this

lemma hv1 : ∀ z, D0.v z = w1 z + (((1 : ℝ) : ℂ) * g0 z) • u1 z := by
  intro z; simp [u1, g0]

lemma hPois1 : ∀ z ∈ D0.onLine, ∑ k, ‖w1 z k‖ ^ 2 ≤ (1 : ℝ) := by
  intro z hz
  rw [ZeroBlockData.mem_onLine] at hz
  fin_cases z
  · simp [w1]
  · exact absurd hz (by decide)
  · exact absurd hz (by decide)

theorem instance_nonsymm :
    4 * (1 : ℝ)⁻¹ * Aw D0 w1 + 2 * (1 : ℝ)⁻¹ * Ag D0 w1 u1 g0 1 - 2 * (D0.Ncount : ℝ)
      - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D0.blockA)
      + 2 * (1 : ℝ)⁻¹ * ∑ z ∈ D0.onLineᶜ, (D0.m z : ℝ) * (G w1 u1 g0 1 z).re
      ≤ ((D0.s₁ + D0.s₂ : ℕ) : ℝ) :=
  hybrid_cert D0 (c := 1) one_pos hv1 hPois1

theorem instance_eta_zero :
    4 * (4 : ℝ)⁻¹ * Aw D0 D0.v - 2 * (D0.Ncount : ℝ) - frobSq ((((4 : ℝ)⁻¹ : ℝ) : ℂ) • D0.blockA)
      ≤ ((D0.s₁ + D0.s₂ : ℕ) : ℝ) :=
  hybrid_cert_eta_zero D0 (c := 4) (by norm_num) (fun _ => rfl) (by
    intro z hz
    rw [ZeroBlockData.mem_onLine] at hz
    fin_cases z
    · simp [D0, w0]; norm_num
    · exact absurd hz (by decide)
    · exact absurd hz (by decide))

/-! ## `D1`: every zero on the line -/

def D1 : ZeroBlockData (Fin 1) (Fin 1) where
  m := fun _ => 2
  one_le_m := fun _ => by norm_num
  v := fun _ _ => 1
  σ := id
  σ_invol := fun _ => rfl
  m_σ := fun _ => rfl
  v_σ := fun _ => by funext k; simp

def wD1 : Fin 1 → Fin 1 → ℂ := fun _ _ => 1
def uD1 : Fin 1 → Fin 1 → ℂ := fun _ _ => 0
def gD1 : Fin 1 → ℂ := fun _ => 0

lemma hvD1 : ∀ z, D1.v z = wD1 z + (((0 : ℝ) : ℂ) * gD1 z) • uD1 z := by
  intro z; funext k; simp [D1, wD1]

lemma hPoisD1 : ∀ z ∈ D1.onLine, ∑ k, ‖wD1 z k‖ ^ 2 ≤ (1 : ℝ) := by
  intro z _; simp [wD1]

theorem instance_no_offline :
    4 * (1 : ℝ)⁻¹ * Aw D1 wD1 + 2 * (1 : ℝ)⁻¹ * Ag D1 wD1 uD1 gD1 0 - 2 * (D1.Ncount : ℝ)
      - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D1.blockA) ≤ ((D1.s₁ + D1.s₂ : ℕ) : ℝ) :=
  hybrid_cert_of_no_offline D1 (c := 1) one_pos hvD1 hPoisD1 (fun _ => rfl)

/-! ## `D2`: the off-line term cannot be dropped -/

def σ2 : Fin 2 → Fin 2 := ![1, 0]

def D2 : ZeroBlockData (Fin 2) (Fin 1) where
  m := fun _ => 1
  one_le_m := fun _ => le_rfl
  v := fun _ _ => 1
  σ := σ2
  σ_invol := by intro z; fin_cases z <;> rfl
  m_σ := fun _ => rfl
  v_σ := fun _ => by funext k; simp

def w2 : Fin 2 → Fin 1 → ℂ := fun _ _ => 10
def u2 : Fin 2 → Fin 1 → ℂ := fun _ _ => 1
def g2 : Fin 2 → ℂ := fun _ => 1

lemma hv2 : ∀ z, D2.v z = w2 z + (((-9 : ℝ) : ℂ) * g2 z) • u2 z := by
  intro z; funext k; simp [D2, w2, u2, g2]; norm_num

lemma hPois2 : ∀ z ∈ D2.onLine, ∑ k, ‖w2 z k‖ ^ 2 ≤ (1 : ℝ) := by
  intro z hz
  rw [ZeroBlockData.mem_onLine] at hz
  fin_cases z <;> exact absurd hz (by decide)

theorem instance_tight :
    4 * (1 : ℝ)⁻¹ * Aw D2 w2 + 2 * (1 : ℝ)⁻¹ * Ag D2 w2 u2 g2 (-9) - 2 * (D2.Ncount : ℝ)
      - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D2.blockA)
      + 2 * (1 : ℝ)⁻¹ * ∑ z ∈ D2.onLineᶜ, (D2.m z : ℝ) * (G w2 u2 g2 (-9) z).re
      ≤ ((D2.s₁ + D2.s₂ : ℕ) : ℝ) :=
  hybrid_cert D2 (c := 1) one_pos hv2 hPois2

lemma D2_onLine : D2.onLine = ∅ := by decide
lemma D2_s : D2.s₁ + D2.s₂ = 0 := by decide
lemma D2_N : D2.Ncount = 2 := by decide

lemma D2_Aw : Aw D2 w2 = 200 := by
  simp [Aw, D2, w2, dotProduct]; norm_num

lemma D2_Ag : Ag D2 w2 u2 g2 (-9) = -198 := by
  simp [Ag, G, D2, w2, u2, g2, dotProduct]; norm_num

lemma D2_scaled : ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D2.blockA) = Matrix.of (fun (_ _ : Fin 1) => (2 : ℂ)) := by
  funext k l; rw [Matrix.smul_apply, ZeroBlockData.blockA_apply]; simp [D2]

lemma D2_frob : frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D2.blockA) = 4 := by
  rw [D2_scaled]
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Finset.univ_unique]
  norm_num

lemma D2_off : ∑ z ∈ D2.onLineᶜ, (D2.m z : ℝ) * (G w2 u2 g2 (-9) z).re = -198 := by
  rw [D2_onLine, Finset.compl_empty]
  simp [G, D2, w2, u2, g2, dotProduct]; norm_num

/-- Without its off-line term, the bound of `hybrid_cert` is false on `D2`: 4·200 + 2·(−198) − 2·2 − 4 = 396 > 0. -/
theorem last_term_needed :
    ¬ (4 * (1 : ℝ)⁻¹ * Aw D2 w2 + 2 * (1 : ℝ)⁻¹ * Ag D2 w2 u2 g2 (-9) - 2 * (D2.Ncount : ℝ)
        - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D2.blockA) ≤ ((D2.s₁ + D2.s₂ : ℕ) : ℝ)) := by
  rw [D2_Aw, D2_Ag, D2_N, D2_frob, D2_s]; norm_num

/-- With it, the left side is 396 + 2·(−198) = 0 = s₁ + s₂: the bound is attained. -/
theorem with_last_term_value :
    4 * (1 : ℝ)⁻¹ * Aw D2 w2 + 2 * (1 : ℝ)⁻¹ * Ag D2 w2 u2 g2 (-9) - 2 * (D2.Ncount : ℝ)
        - frobSq ((((1 : ℝ)⁻¹ : ℝ) : ℂ) • D2.blockA)
        + 2 * (1 : ℝ)⁻¹ * ∑ z ∈ D2.onLineᶜ, (D2.m z : ℝ) * (G w2 u2 g2 (-9) z).re = 0 := by
  rw [D2_Aw, D2_Ag, D2_N, D2_frob, D2_off]; norm_num

end HybridExamples
