import Mathlib

/-! # Spin ½ and `g = 2`: the algebra (round 408)

Part IVb's Corollary `cor:g-equals-two` derives `g = 2` by squaring the Dirac operator: the Clifford relation
splits `γ^μγ^ν` into its symmetric part `η^{μν}` and its commutator, the commutator pairs with
`[D_μ, D_ν] = −ieF_{μν}` into the Pauli term, and `σ^{ij}F_{ij} = 2σ·B` with `S = σ/2` gives `g = 2`.

* `dirac_square`: in any ring, if `γ_μγ_ν + γ_νγ_μ = 2η_{μν}` and every `D_ν` commutes with every `γ_μ`, then
  `4(Σ_μ γ_μD_μ)² = 4Σ_{μν} η_{μν}D_μD_ν + Σ_{μν} [γ_μ, γ_ν][D_μ, D_ν]`.
* `pauli_mul`: the Pauli matrices satisfy `σ_iσ_j = δ_{ij} + iε_{ijk}σ_k`, so the spin `S = σ/2` has
  `[S_x, S_y] = iS_z` and `S² = ¾ = ½(½ + 1)` (`spin_commutator`, `spin_casimir`), with `S_z = diag(½, −½)`.
* `levi_civita_contract`: `Σ_{ij} ε_{ijk}ε_{ijl} = 2δ_{kl}`, the `2` in `σ^{ij}F_{ij} = 2σ·B` when
  `σ^{ij} = ε^{ijk}σ_k` and `F_{ij} = ε_{ijl}B_l`.
* `g_eq_two`: matching `(e/2m)σ·B` with `(g/2)(e/m)S·B`, `S = σ/2`, gives `g = 2`.

That the cascade supplies the Clifford algebra and the electron's Dirac operator is the series' claim (Part IVb
cites the Bott classification); this file proves the algebra only.
-/

open Matrix Complex

namespace Electron

/-! ## The square of the Dirac operator -/

/-- **The Dirac square.** If `γ_μγ_ν + γ_νγ_μ = 2η_{μν}` and the `D`'s commute with the `γ`'s, then
`4(Σγ_μD_μ)² = 4Σ η_{μν}D_μD_ν + Σ [γ_μ, γ_ν][D_μ, D_ν]`. -/
theorem dirac_square {A : Type*} [Ring A] {n : ℕ} (γ D : Fin n → A) (η : Fin n → Fin n → ℤ)
    (hcl : ∀ μ ν, γ μ * γ ν + γ ν * γ μ = 2 * (η μ ν : A))
    (hc : ∀ μ ν, D ν * γ μ = γ μ * D ν) :
    4 * (∑ μ, γ μ * D μ) ^ 2 = 4 * ∑ μ, ∑ ν, (η μ ν : A) * (D μ * D ν)
      + ∑ μ, ∑ ν, (γ μ * γ ν - γ ν * γ μ) * (D μ * D ν - D ν * D μ) := by
  have hsq : (∑ μ, γ μ * D μ) ^ 2 = ∑ μ, ∑ ν, γ μ * γ ν * (D μ * D ν) := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
    rw [mul_assoc, ← mul_assoc (D μ), hc ν μ]
    noncomm_ring
  have hsplit : ∀ μ ν, 4 * (γ μ * γ ν * (D μ * D ν)) = 4 * ((η μ ν : A) * (D μ * D ν))
      + 2 * ((γ μ * γ ν - γ ν * γ μ) * (D μ * D ν)) := by
    intro μ ν
    have h2 : 2 * (γ μ * γ ν) = 2 * (η μ ν : A) + (γ μ * γ ν - γ ν * γ μ) := by
      rw [← hcl μ ν]; noncomm_ring
    calc 4 * (γ μ * γ ν * (D μ * D ν)) = 2 * (2 * (γ μ * γ ν)) * (D μ * D ν) := by noncomm_ring
      _ = 2 * (2 * (η μ ν : A) + (γ μ * γ ν - γ ν * γ μ)) * (D μ * D ν) := by rw [h2]
      _ = _ := by noncomm_ring
  have hanti : ∑ μ, ∑ ν, 2 * ((γ μ * γ ν - γ ν * γ μ) * (D μ * D ν))
      = ∑ μ, ∑ ν, (γ μ * γ ν - γ ν * γ μ) * (D μ * D ν - D ν * D μ) := by
    have hswap : ∑ μ, ∑ ν, (γ μ * γ ν - γ ν * γ μ) * (D μ * D ν)
        = ∑ μ, ∑ ν, -((γ μ * γ ν - γ ν * γ μ) * (D ν * D μ)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
      noncomm_ring
    calc ∑ μ, ∑ ν, 2 * ((γ μ * γ ν - γ ν * γ μ) * (D μ * D ν))
        = ∑ μ, ∑ ν, (γ μ * γ ν - γ ν * γ μ) * (D μ * D ν)
          + ∑ μ, ∑ ν, (γ μ * γ ν - γ ν * γ μ) * (D μ * D ν) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun μ _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun ν _ => ?_)
          noncomm_ring
      _ = ∑ μ, ∑ ν, (γ μ * γ ν - γ ν * γ μ) * (D μ * D ν)
          + ∑ μ, ∑ ν, -((γ μ * γ ν - γ ν * γ μ) * (D ν * D μ)) := by rw [hswap]
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun μ _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun ν _ => ?_)
          noncomm_ring
  rw [hsq, Finset.mul_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← hanti, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ν _ => hsplit μ ν)

/-! ## The Pauli algebra and spin ½ -/

/-- The Pauli matrices. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -I; I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The Levi-Civita symbol on `Fin 3`. -/
def eps (i j k : Fin 3) : ℤ :=
  if (i, j, k) = (0, 1, 2) ∨ (i, j, k) = (1, 2, 0) ∨ (i, j, k) = (2, 0, 1) then 1
  else if (i, j, k) = (0, 2, 1) ∨ (i, j, k) = (2, 1, 0) ∨ (i, j, k) = (1, 0, 2) then -1 else 0

/-- `Σ_{ij} ε_{ijk}ε_{ijl} = 2δ_{kl}`. -/
theorem levi_civita_contract (k l : Fin 3) :
    ∑ i, ∑ j, eps i j k * eps i j l = if k = l then 2 else 0 := by
  fin_cases k <;> fin_cases l <;> decide

/-- `σ_iσ_j = δ_{ij} + i Σ_k ε_{ijk}σ_k`. -/
theorem pauli_mul (i j : Fin 3) :
    pauli i * pauli j = (if i = j then 1 else 0) + I • ∑ k, (eps i j k : ℂ) • pauli k := by
  fin_cases i <;> fin_cases j <;>
    (ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, eps, Matrix.mul_apply, Fin.sum_univ_two])

/-- The spin `S = σ/2`. -/
noncomputable def spin (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • pauli i

/-- `[S_x, S_y] = iS_z`. -/
theorem spin_commutator : spin 0 * spin 1 - spin 1 * spin 0 = I • spin 2 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [spin, pauli] <;> ring_nf

/-- **Spin ½**: `S² = S_x² + S_y² + S_z² = ¾ = ½(½ + 1)`. -/
theorem spin_casimir : spin 0 * spin 0 + spin 1 * spin 1 + spin 2 * spin 2
    = ((1 / 2 : ℂ) * (1 / 2 + 1)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [spin, pauli] <;> ring_nf <;> simp [Complex.ext_iff] <;>
    norm_num

/-- `S_z = diag(½, −½)`: the two spin states. -/
theorem spin_z : spin 2 = Matrix.diagonal ![(1 / 2 : ℂ), -1 / 2] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [spin, pauli, Matrix.diagonal]; ring

/-! ## `g = 2` -/

/-- Matching the Pauli term `(e/2m)σ·B` with `(g/2)(e/m)S·B` at `S = σ/2` gives `g = 2`. -/
theorem g_eq_two {e m g : ℝ} (he : e ≠ 0) (hm : m ≠ 0)
    (h : e / (2 * m) = g / 2 * (e / m) * (1 / 2)) : g = 2 := by
  field_simp at h
  linarith

end Electron

#print axioms Electron.dirac_square
#print axioms Electron.levi_civita_contract
#print axioms Electron.pauli_mul
#print axioms Electron.spin_commutator
#print axioms Electron.spin_casimir
#print axioms Electron.spin_z
#print axioms Electron.g_eq_two
