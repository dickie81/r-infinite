/-
# Round 621: Halász–Montgomery for one bin of characters at one height

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

The bridge `dp S (aχ) h₀ = pv S a χ (ih₀)` for `0 ∉ S` (`dp_eq_pv`), and the per-bin inequality from
`LinnikPower.hm_duality` (round 525) at `σ = 0`, `β_χ ≡ 0`, `γ_χ ≡ h₀` and `Λ = 2P` (`sum_bin_hm`): for `S ⊆ (P, 2P]`
with `P ≥ 1`, a set `R` of characters mod `q` and `B ≥ 0` with `|K_{2P}(ψ, 0)| ≤ B` for every `ψ ≠ 1`,
`(Σ_{χ∈R} |dp S (aχ) h₀|)² ≤ e·Σ_{j∈S}|a_j|²·(|R|·2P + |R|²B)`. `LinnikOffDiag.norm_offK_le` supplies such a `B`,
`C(2P)^{1/12−δ}(2q)^{5/12+δ+2ε′}` (`SieveHMBins.offK_bound`).

The file imports `SieveTypeIIGen.lean` and `LinnikOffDiag.lean`.
-/
import SieveTypeIIGen
import LinnikOffDiag

namespace SieveTypeIIHM

open Finset DirMean LinnikPower Complex

variable {q : ℕ}

/-- The bridge: `dp S (aχ) h₀ = pv S a χ (ih₀)` for `0 ∉ S` (`hS0`). -/
theorem dp_eq_pv {S : Finset ℕ} (hS0 : 0 ∉ S) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (h₀ : ℝ) :
    dp S (fun j => a j * χ j) h₀ = pv S a χ (I * h₀) := by
  unfold dp pv
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hS0 (h ▸ hj)
  congr 1
  rw [Complex.cpow_def_of_ne_zero hj0, ← Complex.natCast_log]
  push_cast
  ring_nf

/-- **Halász–Montgomery for one bin at one height.** For `S ⊆ (P, 2P]` with `P ≥ 1`, a set `R` of characters and a
bound `B ≥ 0` on `|K_{2P}(ψ, 0)|` for every `ψ ≠ 1`:
`(Σ_{χ∈R} |dp S (aχ) h₀|)² ≤ e·(Σ_{j∈S} |a_j|²)·(|R|·2P + |R|²B)` (`hP`, `hS`, `hB0`, `hB`). -/
theorem sum_bin_hm {P : ℕ} (hP : 0 < P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ) (h₀ : ℝ)
    (R : Finset (DirichletCharacter ℂ q)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P) 0 n‖ ≤ B) :
    (∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖) ^ 2 ≤
      Real.exp 1 * (∑ j ∈ S, ‖a j‖ ^ 2) * (R.card * (2 * P) + R.card ^ 2 * B) := by
  have hS0 : 0 ∉ S := fun h => by have := (Finset.mem_Ioc.1 (hS h)).1; omega
  have hSΛ : ∀ n ∈ S, (n : ℝ) ≤ 2 * P := fun n hn => by exact_mod_cast (Finset.mem_Ioc.1 (hS hn)).2
  have hΛ : (0 : ℝ) < 2 * P := by positivity
  have h := hm_duality (q := q) (R := R) hS0 hΛ hSΛ a (σ := 0) (fun _ => 0) (fun _ => h₀) (fun _ _ => le_rfl) hB0
    (fun χ _ χ' _ hne => by
      have hψ : χ * χ'⁻¹ ≠ 1 := by rwa [Ne, mul_inv_eq_one]
      convert hB (χ * χ'⁻¹) hψ using 3
      simp)
  have hG : ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-(0 : ℝ))) ^ 2 = ∑ j ∈ S, ‖a j‖ ^ 2 := by
    simp [Real.rpow_zero]
  have hsum : ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ =
      ∑ χ ∈ R, ‖pv S a χ ((((fun _ : DirichletCharacter ℂ q => (0 : ℝ)) χ : ℝ) : ℂ) +
        ((fun _ : DirichletCharacter ℂ q => h₀) χ : ℝ) * I)‖ := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [dp_eq_pv hS0]
    congr 2
    push_cast
    ring
  rw [hsum, ← hG]
  exact h

end SieveTypeIIHM

#print axioms SieveTypeIIHM.dp_eq_pv
#print axioms SieveTypeIIHM.sum_bin_hm
