/-
# Round 621: Proposition 3′ pointwise, by bins, with the Halász–Montgomery bound per bin

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

`binTerm cnt P q V B` is the smaller of orthogonality's bound for a bin of `cnt` characters,
`cnt^{1/2}((P + q)V)^{1/2}`, and the Halász–Montgomery bound of `SieveHMBin.sum_bin_hm`,
`(e·V·(cnt·2P + cnt²·B))^{1/2}`, with `V = Σ|a|²` and `B` a bound on `|K_{2P}(ψ, 0)|` for `ψ ≠ 1`.
`sum_typeII_bins_hm` is `SieveTypeII.sum_typeII_bins` with `binTerm` for each bin's `(#bin)^{1/2}(Σ_χ|W(χ)|²)^{1/2}`
after its orthogonality step (`typeII_pointwise`'s T1, `Σ_χ|W(χ)|² ≤ (P + q)Σ|a|²`, inlined; round 622: it read
"`SieveTypeII.typeII_pointwise` with `binTerm`", review of round 621, F5; round 623: the factor it named was
`typeII_pointwise`'s, review of round 622, finding 2); `offK_bound` is such a `B`, from `LinnikOffDiag.norm_offK_le`
at `δ = ε′ = 1/1000` and `z = 0`: `C·Λ^{1/12 − 1/1000}·(2q)^{5/12 + 3/1000}` for every `q`, `ψ ≠ 1` and `Λ ≥ 1`.

The file imports `SieveHMBin.lean`.
-/
import SieveHMBin

namespace SieveTypeIIHM

open Finset DirMean LinnikPower SieveTypeII

variable {q : ℕ} [NeZero q]

/-- The bins' bound with the better of orthogonality and Halász–Montgomery for each bin. -/
noncomputable def binTerm (cnt P q V B : ℝ) : ℝ :=
  min (Real.sqrt cnt * Real.sqrt ((P + q) * V)) (Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)))

/-- **Proposition 3′ pointwise, by bins, with the better bound per bin.** For `N > 0` bins (`hN`), `S ⊆ (P, 2P]`
(`hS`) with `P ≥ 1` (`hP`), bounds `M_i ≥ 0` (`hM`) with `|B(χ)| ≤ M_i` for `χ ≠ 1` in bin `i` (`hB`), and `B ≥ 0`
(`hB0`) with `|K_{2P}(ψ, 0)| ≤ B` for `ψ ≠ 1` (`hK`):
`Σ_{χ≠1} |W(χ)||B(χ)| ≤ Σ_{i<N} M_i · binTerm (#bin i) P q (Σ|a|²) B`, `W(χ) = dp S (aχ) h₀`. -/
theorem sum_typeII_bins_hm {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (T : ℝ) {P : ℕ} (hP : 0 < P) {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ) (h₀ : ℝ) (Bf : DirichletCharacter ℂ q → ℂ) (M : ℕ → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖Bf χ‖ ≤ M (bin β N T χ))
    {B : ℝ} (hB0 : 0 ≤ B) (hK : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P) 0 n‖ ≤ B) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖dp S (fun j => a j * χ j) h₀‖ * ‖Bf χ‖ ≤
      ∑ i ∈ Finset.range N, M i *
        binTerm ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card) P q
          (∑ j ∈ S, ‖a j‖ ^ 2) B := by
  classical
  set W : DirichletCharacter ℂ q → ℂ := fun χ => dp S (fun j => a j * χ j) h₀ with hW
  set V : ℝ := ∑ j ∈ S, ‖a j‖ ^ 2 with hV
  -- split the sum over the bins: `Σ_{χ≠1} |W||Bf| ≤ Σ_i M_i Σ_{χ ∈ bin i} |W χ|`
  have hsplit : ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖W χ‖ * ‖Bf χ‖ ≤
      ∑ i ∈ Finset.range N, M i *
        ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i), ‖W χ‖ := by
    calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖W χ‖ * ‖Bf χ‖
        ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖W χ‖ * M (bin β N T χ) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          exact mul_le_mul_of_nonneg_left (hB χ (Finset.mem_filter.1 hχ).2) (norm_nonneg _)
      _ = ∑ i ∈ Finset.range N, ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
            bin β N T χ = i), ‖W χ‖ * M i := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := bin β N T) (t := Finset.range N)
            (fun χ _ => Finset.mem_range.2 (bin_lt hN T χ))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.filter_filter]
          exact Finset.sum_congr rfl fun χ hχ => by rw [(Finset.mem_filter.1 hχ).2.2]
      _ = ∑ i ∈ Finset.range N, M i *
            ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i), ‖W χ‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine hsplit.trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hM i))
  set R := (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i) with hR
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => by positivity
  -- the bin's sum is at most each of the two bounds
  have hT1 : ∑ χ ∈ R, ‖W χ‖ ≤ Real.sqrt R.card * Real.sqrt ((P + q) * V) := by
    -- Cauchy–Schwarz over the bin, then orthogonality over all characters (`sum_chars_dp_sq_le`)
    have hcs : (∑ χ ∈ R, ‖W χ‖) ^ 2 ≤ R.card * ∑ χ ∈ R, ‖W χ‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1 : ℝ)) (fun χ => ‖W χ‖)
      simpa using this
    have hle : ∑ χ ∈ R, ‖W χ‖ ^ 2 ≤ (P + q) * V :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) fun _ _ _ => by positivity).trans
        (sum_chars_dp_sq_le hS a q h₀)
    have h0 : 0 ≤ ∑ χ ∈ R, ‖W χ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_left hle (by positivity)))
  have hHM : ∑ χ ∈ R, ‖W χ‖ ≤ Real.sqrt (Real.exp 1 * V * (R.card * (2 * P) + R.card ^ 2 * B)) := by
    have h := sum_bin_hm hP hS a h₀ R hB0 hK
    have h0 : 0 ≤ ∑ χ ∈ R, ‖W χ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt h
  exact le_min hT1 hHM

/-- **A uniform kernel bound at `z = 0`** from `LinnikOffDiag.norm_offK_le` at `δ′ = ε′ = 1/1000`: there is `C` with
`|Σ_n kTerm ψ Λ 0 n| ≤ C·Λ^{1/12 − 1/1000}·(2q)^{5/12 + 3/1000}` for every `q`, `ψ ≠ 1` and `Λ ≥ 1`. -/
theorem offK_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
    ∀ Λ : ℝ, 1 ≤ Λ → ‖∑' n, kTerm ψ Λ 0 n‖ ≤
      C * Λ ^ (1 / 12 - 1 / 1000 : ℝ) * (2 * (q : ℝ)) ^ (5 / 12 + 3 / 1000 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := LinnikOffDiag.norm_offK_le (δ := 1 / 1000) (ε' := 1 / 1000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun q _ ψ hψ Λ hΛ => ?_⟩
  have h := hC q ψ hψ Λ hΛ 0 le_rfl (by norm_num) 0 (by simp)
  rw [show ((q : ℝ) * (0 + 2)) = 2 * (q : ℝ) by ring,
    show (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) = 5 / 12 + 3 / 1000 by norm_num] at h
  exact h

end SieveTypeIIHM

#print axioms SieveTypeIIHM.sum_typeII_bins_hm
#print axioms SieveTypeIIHM.offK_bound
