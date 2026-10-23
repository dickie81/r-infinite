import EisensteinQuadSieveCor
import EisensteinThetaAssembly

/-! # The quadratic large sieve, part 8: Theorem 2, `(E_1)` and Lemma 6.5 (round 359)

S5e of round 312's plan, completed: Goldmakher and Louvel's Theorem 2, the iteration from round
345's `(E_2)` to `(E_1)`, and with round 344's reduction the companion paper's Lemma 6.5. The
zero-free half-plane `Re s > 11/12` then rests on the displayed theta transformation alone.

* **Theorem 2** (`fBound_improve`, `qExp_improve`, with `rpow_beta_identity`): `(E_α)` with
  `α ≥ 1` gives `(E_{2−1/α})`. For `M ≥ N^{2−1/α}`, Theorem cor's third term is at most `M`; for
  `M < N^{2−1/α}`, the rows are enlarged to `N^{2−1/α}`, where it equals `N^{2−1/α}`. Round 344's
  symmetry turns the rows' orientation into `QExp`'s.
* **`(E_1)`** (`qExp_seq`, `qExp_one`): `(E_{(j+2)/(j+1)})` for every `j` by induction from
  `(E_2)`, and `(E_1)` from `N^{1/(j+1)} ≤ (MN)^{ε/2}`.
* **Lemma 6.5** (`quadLargeSieve`) from round 344's `quadLargeSieve_of_exp`, and the half-plane
  from `Eis.ThetaRows` alone (`ne_zero_of_thetaRows`, round 342's `ne_zero_of_theta`).
-/

open Complex NumberField Ideal
open scoped Classical

noncomputable section

namespace Eis

/-- `N^{2α−1}·(N^β)^{1−α} = N^β` for `β = 2 − 1/α`. -/
theorem rpow_beta_identity {N α : ℝ} (hN : 0 < N) (hα : 0 < α) :
    N ^ (2 * α - 1) * (N ^ (2 - 1 / α)) ^ (1 - α) = N ^ (2 - 1 / α) := by
  rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  congr 1
  field_simp
  ring

/-- **Goldmakher and Louvel's Theorem 2, in the rows' orientation**: `(E_α)` with `α ≥ 1` gives
`FBound (admW M) N (C·(MN)^ε·(M + N^{2−1/α}))`. -/
theorem fBound_improve {α : ℝ} (hα : 1 ≤ α) (hE : QExp α) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      FBound (admW M) N (C * (M * N) ^ ε * (M + N ^ (2 - 1 / α))) := by
  obtain ⟨C, hC0, hC⟩ := fBound_cor hα hE (ε := ε / 3) (by positivity)
  refine ⟨3 * C, by positivity, fun M N hM hN => ?_⟩
  set β : ℝ := 2 - 1 / α with hβ
  have hα0 : 0 < α := by linarith
  have hβ1 : 1 ≤ β := by
    have : 1 / α ≤ 1 := by rw [div_le_one hα0]; exact hα
    linarith
  have hβ2 : β ≤ 2 := by have : 0 ≤ 1 / α := by positivity
                         linarith
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hQ1 : 1 ≤ M * N := by nlinarith
  have hNβ : N ≤ N ^ β := by
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ β := Real.rpow_le_rpow_of_exponent_le hN hβ1
  have hNβ0 : 0 < N ^ β := Real.rpow_pos_of_pos hN0 _
  have hpow : (M * N) ^ (ε / 3) ≤ (M * N) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hQε : 0 ≤ (M * N) ^ ε := by positivity
  by_cases hMβ : N ^ β ≤ M
  · refine (hC M N hM hN).mono le_rfl ?_
    have hr : N ^ (2 * α - 1) * M ^ (1 - α) ≤ N ^ β := by
      calc N ^ (2 * α - 1) * M ^ (1 - α) ≤ N ^ (2 * α - 1) * (N ^ β) ^ (1 - α) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hNβ0 hMβ (by linarith))
              (by positivity)
        _ = N ^ β := rpow_beta_identity hN0 hα0
    have hs : sizeE α M N ≤ 3 * (M + N ^ β) := by
      unfold sizeE; linarith
    have hs0 : 0 ≤ sizeE α M N := le_trans zero_le_one (sizeE_ge (α := α) hM hN).2.2.2
    calc C * (M * N) ^ (ε / 3) * sizeE α M N ≤ C * (M * N) ^ ε * (3 * (M + N ^ β)) := by
          gcongr
      _ = 3 * C * (M * N) ^ ε * (M + N ^ β) := by ring
  · push Not at hMβ
    have hM' : 1 ≤ N ^ β := le_trans hN hNβ
    have h := (hC (N ^ β) N hM' hN)
    have h' : FBound (admW M) N (C * (N ^ β * N) ^ (ε / 3) * sizeE α (N ^ β) N) :=
      FBound.of_le (admW_nonneg M) (admW_mono hMβ.le) (summable_admW _) h
    refine h'.mono le_rfl ?_
    have hs : sizeE α (N ^ β) N ≤ 3 * N ^ β := by
      unfold sizeE
      rw [rpow_beta_identity hN0 hα0]
      linarith
    have hp : (N ^ β * N) ^ (ε / 3) ≤ (M * N) ^ ε := by
      have h1 : N ^ β * N ≤ N ^ 3 := by
        have : N ^ β ≤ N ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hβ2
        rw [Real.rpow_two] at this
        nlinarith
      calc (N ^ β * N) ^ (ε / 3) ≤ (N ^ 3) ^ (ε / 3) :=
            Real.rpow_le_rpow (by positivity) h1 (by positivity)
        _ = N ^ ε := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
        _ ≤ (M * N) ^ ε := Real.rpow_le_rpow hN0.le (by nlinarith) hε.le
    have hs0 : 0 ≤ sizeE α (N ^ β) N := le_trans zero_le_one (sizeE_ge (α := α) hM' hN).2.2.2
    calc C * (N ^ β * N) ^ (ε / 3) * sizeE α (N ^ β) N ≤ C * (M * N) ^ ε * (3 * N ^ β) := by
          gcongr
      _ ≤ C * (M * N) ^ ε * (3 * (M + N ^ β)) := by gcongr; linarith
      _ = 3 * C * (M * N) ^ ε * (M + N ^ β) := by ring

/-- **Goldmakher and Louvel's Theorem 2**: `(E_α)` with `α ≥ 1` gives `(E_{2−1/α})`. -/
theorem qExp_improve {α : ℝ} (hα : 1 ≤ α) (hE : QExp α) : QExp (2 - 1 / α) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := fBound_improve hα hE hε
  refine ⟨(absNorm (span {(4 : 𝓞 K)}) : ℝ) * C, by positivity, fun M N hM hN => ?_⟩
  have hΔ : 0 ≤ C * (M * N) ^ ε * (M + N ^ (2 - 1 / α)) := by
    have : 0 ≤ N ^ (2 - 1 / α) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ M * N := by nlinarith
    positivity
  have hs := (qBound_of_fBound hΔ (hC M N hM hN)).symm hΔ
  exact hs.mono le_rfl le_rfl (le_of_eq (by ring))

/-- **The iteration**: `(E_{(j+2)/(j+1)})` for every `j`, from round 345's `(E_2)`. -/
theorem qExp_seq (j : ℕ) : QExp (((j : ℝ) + 2) / ((j : ℝ) + 1)) := by
  induction j with
  | zero => norm_num; exact qExp_two
  | succ j ih =>
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hα : 1 ≤ ((j : ℝ) + 2) / ((j : ℝ) + 1) := by rw [le_div_iff₀ hj]; linarith
    have h := qExp_improve hα ih
    have e : (2 : ℝ) - 1 / (((j : ℝ) + 2) / ((j : ℝ) + 1)) =
        (((j + 1 : ℕ) : ℝ) + 2) / (((j + 1 : ℕ) : ℝ) + 1) := by
      push_cast; field_simp; ring
    rwa [e] at h

/-- **`(E_1)`**: Goldmakher and Louvel's Theorem 1.1 over `ℤ[ω]`, in the ball form of round 344. -/
theorem qExp_one : QExp 1 := by
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 2 by positivity)
  obtain ⟨C, hC0, hC⟩ := qExp_seq j (ε / 2) (by positivity)
  refine ⟨C, hC0, fun M N hM hN => (hC M N hM hN).mono le_rfl le_rfl ?_⟩
  have hQ1 : 1 ≤ M * N := by nlinarith
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have he : ((j : ℝ) + 2) / ((j : ℝ) + 1) = 1 + 1 / ((j : ℝ) + 1) := by field_simp; ring
  have hNe : N ^ (((j : ℝ) + 2) / ((j : ℝ) + 1)) ≤ N * (M * N) ^ (ε / 2) := by
    rw [he, Real.rpow_add (by linarith), Real.rpow_one]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc N ^ (1 / ((j : ℝ) + 1)) ≤ N ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hN hj.le
      _ ≤ (M * N) ^ (ε / 2) := Real.rpow_le_rpow (by linarith) (by nlinarith) (by positivity)
  have hQe1 : 1 ≤ (M * N) ^ (ε / 2) := Real.one_le_rpow hQ1 (by positivity)
  have hsplit : (M * N) ^ ε = (M * N) ^ (ε / 2) * (M * N) ^ (ε / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  rw [Real.rpow_one, hsplit]
  have hP : 0 ≤ C * (M * N) ^ (ε / 2) := by positivity
  calc C * (M * N) ^ (ε / 2) * (M + N ^ (((j : ℝ) + 2) / ((j : ℝ) + 1)))
      ≤ C * (M * N) ^ (ε / 2) * (M * (M * N) ^ (ε / 2) + N * (M * N) ^ (ε / 2)) := by
        gcongr
        nlinarith
    _ = C * ((M * N) ^ (ε / 2) * (M * N) ^ (ε / 2)) * (M + N) := by ring

/-- **The companion paper's Lemma 6.5 is proved**: the quadratic large sieve over `ℤ[ω]`. -/
theorem quadLargeSieve : QuadLargeSieve := quadLargeSieve_of_exp qExp_one

/-- **The half-plane from the theta transformation alone**: `ζ(s)L(s, χ₋₃) ≠ 0` on
`Re s > 11/12` from the displayed `Eis.ThetaRows`. -/
theorem ne_zero_of_thetaRows (hθ : ThetaRows) {s : ℂ} (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_theta hθ quadLargeSieve hs

end Eis

end

#print axioms Eis.rpow_beta_identity
#print axioms Eis.fBound_improve
#print axioms Eis.qExp_improve
#print axioms Eis.qExp_seq
#print axioms Eis.qExp_one
#print axioms Eis.quadLargeSieve
#print axioms Eis.ne_zero_of_thetaRows
