import EisensteinCubeReduction

/-! # The descent: Proposition 5.1 and the third conditional milestone (round 315)

S5b in round 312's plan: the companion paper's Proposition 5.1, by its induction on `j` under
`𝓗 ≤ D^{jη}`, with its Proposition 5.4 (the transfer estimate) displayed as a hypothesis beside round
314's `CompletedMeanSquare`; then `DualMeanSquare ϑ` for every `ϑ > 0` and, through round 310, the
half-plane `Re s > 11/12`.

* **Counting** (`colSum_eq_zero_of_lt`, `norm_colSum_le`, `rowE_le_count`, `rowE_eq_zero_of_lt`; in
  `EisensteinCubeReduction.lean` since round 332): a column sum at scale `X` is empty when `βX < 1`
  and has at most `(2κ+5)βX` terms otherwise.
* **`TransferEstimate`**, the paper's Proposition 5.4, displayed in the form its proof of
  Proposition 5.1 uses (`E(𝓗, L, F; ξ, W) ≤ 𝒜(W)`).
* **The induction** (`CanonicalAt`, `canonicalAt_zero`, `canonicalAt_succ`): the base `j = 0` by
  counting; the step by `cube_reduction` (round 314), whose long scales go to the transfer estimate,
  whose transferred rows lie one level down (`transferred_level`, `transferred_gap`).
* **`canonical_bound`** (the paper's Proposition 5.1); **`dualMeanSquare_of_completed_transfer`**
  (`DualMeanSquare ϑ` for every `ϑ > 0`, as in the paper's proof of its Proposition 3.1, with the
  scales `X < 1` and the bounded `D` by counting); **`ne_zero_of_completed_transfer`**:
  `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > 11/12`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The displayed transfer estimate and the canonical bounds -/

/-- **The transfer estimate** (the companion paper's Proposition 5.4), displayed as a hypothesis, in
the form its proof of Proposition 5.1 uses (`E(𝓗, L, F; ξ, W) ≤ 𝒜(W)`): for `C₀ ≥ 1`, every
derivative order `m`, `ε > 0` and interval `[α, β] ⊂ (0, ∞)` there is a constant `K` such that,
uniformly in `ξ` and the smooth weight `W` supported in `[α, β]` with its first `4m+12` derivatives
bounded by `N`, for `1 ≤ 𝓗, L, F, Σ ≤ D^{C₀}` with `max(𝓗, LF) ≤ Σ` and every `M ≥ 0`: if the row
sums of the dual mean squares at all `𝓗′, X′, F′ ≥ 1` with `𝓗′ ≤ 𝓗L/(ΣF)`, `𝓗′/Σ′ ≤ 𝓗/Σ` and
`Σ′ = X′F′ ≤ L`, for all characters `ξ′` and tests `U` supported in `[α/16, 4β]` with their first
`m` derivatives bounded by `1`, are at most `M·Σ′²`, then every finite set of rows at `(𝓗, F)` has
row sum at `L` at most `K·D^ε·Σ·N²·(1 + M)·LF`. -/
def TransferEstimate : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ α β : ℝ, 0 < α → ∃ Kt : ℝ,
    ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ,
        (∀ i ≤ 4 * m + 12, ∀ x, ‖iteratedDeriv i W x‖ ≤ N) →
      ∀ D Hh L F S : ℝ, 1 ≤ D → 1 ≤ Hh → 1 ≤ L → 1 ≤ F → 1 ≤ S → Hh ≤ D ^ C₀ → L ≤ D ^ C₀ →
        F ≤ D ^ C₀ → S ≤ D ^ C₀ → Hh ≤ S → L * F ≤ S →
      ∀ M : ℝ, 0 ≤ M →
        (∀ Hh' X' F' : ℝ, 1 ≤ Hh' → 1 ≤ X' → 1 ≤ F' → Hh' ≤ Hh * L / (S * F) →
          Hh' / (X' * F') ≤ Hh / S → X' * F' ≤ L →
          ∀ ξ' : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ U : ℝ → ℂ, ContDiff ℝ ∞ U →
            (∀ x, x < α / 16 ∨ 4 * β < x → U x = 0) →
            (∀ i ≤ m, ∀ x, ‖iteratedDeriv i U x‖ ≤ 1) →
          ∀ (Fs' : Finset (Ideal (𝓞 K))) (T' : Finset (𝓞 K)),
            (∀ f ∈ Fs', (absNorm f).Coprime 6 ∧ Squarefree f ∧ F' ≤ (absNorm f : ℝ) ∧
              (absNorm f : ℝ) < 2 * F') →
            (∀ k ∈ T', k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh') →
            rowE ξ' U X' Fs' T' ≤ M * (X' * F') ^ 2) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) →
        rowE ξ W L Fs T ≤ Kt * D ^ ε * S * N ^ 2 * (1 + M) * (L * F)

/-- **The canonical bound at level `j`** (the induction hypothesis in the proof of the companion
paper's Proposition 5.1): at gap `η` and range `C₀`, under `𝓗 ≤ D^{jη}`, the row sum at `X` is
at most `K·N²·D^ε·(XF)²`, that is `E(𝓗, X, F; ξ, W) ≪ ‖W‖²_{C^J}D^εΣ`. -/
def CanonicalAt (η C₀ : ℝ) (j : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ α β : ℝ, 0 < α → ∃ Kc : ℝ,
    ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ, (∀ i ≤ J, ∀ x, ‖iteratedDeriv i W x‖ ≤ N) →
      ∀ D Hh X F : ℝ, 1 ≤ D → 1 ≤ Hh → 1 ≤ X → 1 ≤ F → X * F ≤ D ^ C₀ →
        Hh * D ^ η ≤ X * F → Hh ≤ D ^ ((j : ℝ) * η) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) →
        rowE ξ W X Fs T ≤ Kc * N ^ 2 * D ^ ε * (X * F) ^ 2

/-- **The base of the induction**: at `j = 0`, `𝓗 ≤ 1`, and counting gives the bound. -/
theorem canonicalAt_zero (η C₀ : ℝ) : CanonicalAt η C₀ 0 := by
  intro ε hε
  refine ⟨0, fun α β hα => ?_⟩
  set β₁ := max β 1 with hβ₁def
  have hβ₁ : 1 ≤ β₁ := le_max_right _ _
  refine ⟨98 * (2 * kappa + 5) ^ 3 * β₁ ^ 2, ?_⟩
  intro ξ W hWs hWsupp N hN D Hh X F hD hH hX hF hXF hgap hHj Fs T hFs hT
  have hk := kappa_pos
  have hW₁ : ∀ x, β₁ < x → W x = 0 := fun x hx =>
    hWsupp x (Or.inr (lt_of_le_of_lt (le_max_left _ _) hx))
  have hN' : ∀ x, ‖W x‖ ≤ N := fun x => by
    have := hN 0 (Nat.zero_le _) x
    rwa [iteratedDeriv_zero] at this
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN' 0)
  have hX0 : 0 < X := by linarith
  have hH1 : Hh ≤ 1 := by
    have : D ^ (((0 : ℕ) : ℝ) * η) = 1 := by simp
    rw [this] at hHj; exact hHj
  have h1 : 1 ≤ β₁ * X := one_le_mul_of_one_le_of_one_le hβ₁ hX
  have hcount := rowE_le_count ξ hW₁ hN' hH hF hX0 h1 hFs hT
  have hDe : 1 ≤ D ^ ε := Real.one_le_rpow hD hε.le
  calc rowE ξ W X Fs T ≤ 98 * (2 * kappa + 5) ^ 3 * (β₁ * X) ^ 2 * N ^ 2 * F * Hh := hcount
    _ ≤ 98 * (2 * kappa + 5) ^ 3 * (β₁ * X) ^ 2 * N ^ 2 * F ^ 2 * 1 := by
        gcongr
        nlinarith
    _ = 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 2 * N ^ 2 * 1 * (X * F) ^ 2 := by ring
    _ ≤ 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 2 * N ^ 2 * D ^ ε * (X * F) ^ 2 := by gcongr

/-- **The transferred rows lie one level down**: from `𝓗′·XF·F ≤ 𝓗L`, `LX < 𝓗²`, `𝓗·D^η ≤ XF`
and `𝓗 ≤ D^{(j+1)η}` follows `𝓗′ ≤ D^{jη}` (the paper's `𝓗′ < 𝓗(𝓗/Σ)² ≤ D^{−2κ}𝓗`, its `κ` being
`η` here). -/
theorem transferred_level {η : ℝ} {j : ℕ} {D Hh X F L Hh' : ℝ} (hD : 1 ≤ D) (hH : 1 ≤ Hh)
    (hX : 0 < X) (hF : 0 < F) (hgap : Hh * D ^ η ≤ X * F)
    (hHj : Hh ≤ D ^ (((j + 1 : ℕ) : ℝ) * η)) (hLX : L * X < Hh ^ 2)
    (h4 : Hh' ≤ Hh * L / (X * F * F)) (hH' : 0 ≤ Hh') (hη : 0 ≤ η) :
    Hh' ≤ D ^ ((j : ℝ) * η) := by
  set d := D ^ η with hd
  have hd1 : 1 ≤ d := Real.one_le_rpow hD hη
  have hD0 : 0 < D := by linarith
  have hsplit : D ^ (((j + 1 : ℕ) : ℝ) * η) = D ^ ((j : ℝ) * η) * d := by
    rw [hd, ← Real.rpow_add hD0]; push_cast; ring_nf
  rw [hsplit] at hHj
  have hS : 0 < X * F := mul_pos hX hF
  have h5 : Hh' * (X * F) ^ 2 ≤ Hh ^ 3 := by
    rw [le_div_iff₀ (by positivity)] at h4
    calc Hh' * (X * F) ^ 2 = Hh' * (X * F * F) * X := by ring
      _ ≤ Hh * L * X := mul_le_mul_of_nonneg_right h4 hX.le
      _ = Hh * (L * X) := by ring
      _ ≤ Hh * Hh ^ 2 := mul_le_mul_of_nonneg_left hLX.le (by linarith)
      _ = Hh ^ 3 := by ring
  have h6 : Hh' * d ^ 2 ≤ Hh := by
    have hHd0 : 0 ≤ Hh * d := by positivity
    have h7 : (Hh * d) ^ 2 ≤ (X * F) ^ 2 := pow_le_pow_left₀ hHd0 hgap 2
    have h8 : Hh' * d ^ 2 * (X * F) ^ 2 ≤ Hh * (X * F) ^ 2 := by
      calc Hh' * d ^ 2 * (X * F) ^ 2 = (Hh' * (X * F) ^ 2) * d ^ 2 := by ring
        _ ≤ Hh ^ 3 * d ^ 2 := mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = Hh * (Hh * d) ^ 2 := by ring
        _ ≤ Hh * (X * F) ^ 2 := mul_le_mul_of_nonneg_left h7 (by linarith)
    exact le_of_mul_le_mul_right h8 (by positivity)
  have h9 : Hh' * d ≤ D ^ ((j : ℝ) * η) := by
    have h10 : Hh' * d * d ≤ D ^ ((j : ℝ) * η) * d := by nlinarith
    exact le_of_mul_le_mul_right h10 (by linarith)
  calc Hh' = Hh' * 1 := (mul_one _).symm
    _ ≤ Hh' * d := mul_le_mul_of_nonneg_left hd1 hH'
    _ ≤ _ := h9

/-- **The transferred rows keep the gap**: `𝓗′/Σ′ ≤ 𝓗/Σ` and `𝓗·D^η ≤ Σ` give `𝓗′·D^η ≤ Σ′`. -/
theorem transferred_gap {η D Hh S Hh' S' : ℝ} (hgap : Hh * D ^ η ≤ S) (hS : 0 < S)
    (hS' : 0 < S') (h5 : Hh' / S' ≤ Hh / S) (hD : 0 ≤ D ^ η) : Hh' * D ^ η ≤ S' := by
  rw [div_le_div_iff₀ hS' hS] at h5
  have h1 : Hh' * D ^ η * S ≤ S' * S := by
    calc Hh' * D ^ η * S = (Hh' * S) * D ^ η := by ring
      _ ≤ (Hh * S') * D ^ η := mul_le_mul_of_nonneg_right h5 hD
      _ = (Hh * D ^ η) * S' := by ring
      _ ≤ S * S' := mul_le_mul_of_nonneg_right hgap hS'.le
      _ = S' * S := by ring
  exact le_of_mul_le_mul_right h1 hS

/-- **The induction step of the companion paper's Proposition 5.1**: Lemma 5.3 (`cube_reduction`),
with the long scales bounded by the transfer estimate and the level-`j` bound. -/
theorem canonicalAt_succ (hC : CompletedMeanSquare) (hT : TransferEstimate) {η C₀ : ℝ}
    (hη : 0 < η) (hC₀ : 1 ≤ C₀) {j : ℕ} (h : CanonicalAt η C₀ j) :
    CanonicalAt η C₀ (j + 1) := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨m, hm⟩ := h (ε / 3) hε3
  obtain ⟨J₁, hJ₁⟩ := cube_reduction hC (ε / 3) hε3 C₀ hC₀
  refine ⟨max J₁ (4 * m + 12), fun α β hα => ?_⟩
  obtain ⟨Kj, hKj⟩ := hm (α / 16) (4 * β) (by positivity)
  obtain ⟨Kcr, hKcr⟩ := hJ₁ α β hα
  obtain ⟨Kt, hKt⟩ := hT C₀ hC₀ m (ε / 3) hε3 α β hα
  set Kj' := max Kj 0 with hKj'
  set Kt' := max Kt 0 with hKt'
  set Kc' := max Kcr 0 with hKc'
  have hKj0 : 0 ≤ Kj' := le_max_right _ _
  have hKt0 : 0 ≤ Kt' := le_max_right _ _
  have hKc0 : 0 ≤ Kc' := le_max_right _ _
  refine ⟨Kc' * (1 + Kt' + Kt' * Kj'), ?_⟩
  intro ξ W hWs hWsupp N hN D Hh X F hD hH hX hF hXF hgap hHj Fs T hFs hT
  have hN₁ : ∀ i ≤ J₁, ∀ x, ‖iteratedDeriv i W x‖ ≤ N := fun i hi =>
    hN i (le_trans hi (le_max_left _ _))
  have hN₂ : ∀ i ≤ 4 * m + 12, ∀ x, ‖iteratedDeriv i W x‖ ≤ N := fun i hi =>
    hN i (le_trans hi (le_max_right _ _))
  have hN0 : 0 ≤ N := by
    have := hN 0 (Nat.zero_le _) 0
    rw [iteratedDeriv_zero] at this
    exact (norm_nonneg _).trans this
  have hD0 : 0 < D := by linarith
  have hX0 : 0 < X := by linarith
  have hF0 : 0 < F := by linarith
  have hS1 : 1 ≤ X * F := one_le_mul_of_one_le_of_one_le hX hF
  have hS0 : 0 < X * F := by linarith
  have hdη : 1 ≤ D ^ η := Real.one_le_rpow hD hη.le
  have hHS : Hh ≤ X * F := le_trans (le_mul_of_one_le_right (by linarith) hdη) hgap
  have hXS : X ≤ X * F := le_mul_of_one_le_right hX0.le hF
  have hFS : F ≤ X * F := le_mul_of_one_le_left hF0.le hX
  set u := D ^ (ε / 3) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hD hε3.le
  set Esup := Kt' * u * (X * F) * N ^ 2 * (1 + Kj' * u) with hEsup
  have hE0 : 0 ≤ Esup := by positivity
  have hlong : ∀ L : ℝ, 1 < L → L ≤ X → L * min X (X ^ 2 / Hh ^ 2) < X →
      rowE ξ W L Fs T ≤ Esup * (L * F) := by
    intro L hL1 hLX hLc
    have hH0 : 0 < Hh := by linarith
    have hmin : X ^ 2 / Hh ^ 2 < X := by
      have hm0 : 0 ≤ min X (X ^ 2 / Hh ^ 2) := le_min hX0.le (by positivity)
      have h1 : min X (X ^ 2 / Hh ^ 2) < X := by nlinarith
      rcases min_lt_iff.1 h1 with h | h
      · exact absurd h (lt_irrefl _)
      · exact h
    rw [min_eq_right hmin.le] at hLc
    have hLXH : L * X < Hh ^ 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)] at hLc
      nlinarith
    have hM : ∀ Hh' X' F' : ℝ, 1 ≤ Hh' → 1 ≤ X' → 1 ≤ F' → Hh' ≤ Hh * L / ((X * F) * F) →
        Hh' / (X' * F') ≤ Hh / (X * F) → X' * F' ≤ L →
        ∀ ξ' : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ U : ℝ → ℂ, ContDiff ℝ ∞ U →
          (∀ x, x < α / 16 ∨ 4 * β < x → U x = 0) →
          (∀ i ≤ m, ∀ x, ‖iteratedDeriv i U x‖ ≤ 1) →
        ∀ (Fs' : Finset (Ideal (𝓞 K))) (T' : Finset (𝓞 K)),
          (∀ f ∈ Fs', (absNorm f).Coprime 6 ∧ Squarefree f ∧ F' ≤ (absNorm f : ℝ) ∧
            (absNorm f : ℝ) < 2 * F') →
          (∀ k ∈ T', k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh') →
          rowE ξ' U X' Fs' T' ≤ Kj' * u * (X' * F') ^ 2 := by
      intro Hh' X' F' h1 h2 h3 h4 h5 h6 ξ' U hU hUs hUd Fs' T' hFs' hT'
      have hS' : 0 < X' * F' := by positivity
      have hXF' : X' * F' ≤ D ^ C₀ := h6.trans (hLX.trans (hXS.trans hXF))
      have hgap' : Hh' * D ^ η ≤ X' * F' := transferred_gap hgap hS0 hS' h5 (by linarith)
      have hlev : Hh' ≤ D ^ ((j : ℝ) * η) :=
        transferred_level hD hH hX0 hF0 hgap hHj hLXH h4 (by linarith) hη.le
      have h7 := hKj ξ' U hU hUs 1 hUd D Hh' X' F' hD h1 h2 h3 hXF' hgap' hlev Fs' T' hFs' hT'
      calc rowE ξ' U X' Fs' T' ≤ Kj * 1 ^ 2 * D ^ (ε / 3) * (X' * F') ^ 2 := h7
        _ ≤ Kj' * u * (X' * F') ^ 2 := by
            rw [one_pow, mul_one]
            gcongr
            exact le_max_left _ _
    have hLF : L * F ≤ X * F := mul_le_mul_of_nonneg_right hLX hF0.le
    have hTr := hKt ξ W hWs hWsupp N hN₂ D Hh L F (X * F) hD hH hL1.le hF hS1 (hHS.trans hXF)
      (hLX.trans (hXS.trans hXF)) (hFS.trans hXF) hXF hHS hLF (Kj' * u) (by positivity) hM
      Fs T hFs hT
    have hP : 0 ≤ D ^ (ε / 3) * (X * F) * N ^ 2 * (1 + Kj' * u) * (L * F) := by positivity
    calc rowE ξ W L Fs T ≤ Kt * D ^ (ε / 3) * (X * F) * N ^ 2 * (1 + Kj' * u) * (L * F) := hTr
      _ = Kt * (D ^ (ε / 3) * (X * F) * N ^ 2 * (1 + Kj' * u) * (L * F)) := by ring
      _ ≤ Kt' * (D ^ (ε / 3) * (X * F) * N ^ 2 * (1 + Kj' * u) * (L * F)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hP
      _ = Esup * (L * F) := by rw [hEsup]; ring
  have hcr := hKcr ξ W hWs hWsupp N hN₁ D Hh X F hD hH hX hF (hHS.trans hXF) (hXS.trans hXF)
    (hFS.trans hXF) hHS Fs T hFs hT Esup hE0 hlong
  have hDε : D ^ ε = u ^ 3 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    congr 1; push_cast; ring
  have hQ : 0 ≤ N ^ 2 * (X * F) ^ 2 + X * F * Esup := by positivity
  have hu3 : u ≤ u ^ 3 := le_self_pow₀ hu1 (by norm_num)
  have hu2 : u ^ 2 ≤ u ^ 3 := pow_le_pow_right₀ hu1 (by norm_num)
  calc rowE ξ W X Fs T ≤ Kcr * D ^ (ε / 3) * (N ^ 2 * (X * F) ^ 2 + X * F * Esup) := hcr
    _ = Kcr * (u * (N ^ 2 * (X * F) ^ 2 + X * F * Esup)) := by rw [hu]; ring
    _ ≤ Kc' * (u * (N ^ 2 * (X * F) ^ 2 + X * F * Esup)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ Kc' * (1 + Kt' + Kt' * Kj') * N ^ 2 * D ^ ε * (X * F) ^ 2 := by
        rw [hDε, hEsup]
        have key : Kc' * (1 + Kt' + Kt' * Kj') * N ^ 2 * u ^ 3 * (X * F) ^ 2 -
            Kc' * (u * (N ^ 2 * (X * F) ^ 2 +
              X * F * (Kt' * u * (X * F) * N ^ 2 * (1 + Kj' * u)))) =
            Kc' * N ^ 2 * (X * F) ^ 2 * ((u ^ 3 - u) + Kt' * (u ^ 3 - u ^ 2)) := by ring
        have hpos : 0 ≤ Kc' * N ^ 2 * (X * F) ^ 2 * ((u ^ 3 - u) + Kt' * (u ^ 3 - u ^ 2)) := by
          apply mul_nonneg (by positivity)
          have : 0 ≤ u ^ 3 - u := by linarith
          have : 0 ≤ Kt' * (u ^ 3 - u ^ 2) := mul_nonneg hKt0 (by linarith)
          linarith
        linarith

/-- **The companion paper's Proposition 5.1** (the canonical bound), from the displayed completed
mean-square and transfer estimates: for `η > 0` and `C₀ ≥ 1`, `E(𝓗, X, F; ξ, W) ≪ ‖W‖²_{C^J}D^εΣ`
whenever `𝓗, X, F ≥ 1`, `Σ = XF ≤ D^{C₀}` and `𝓗·D^η ≤ Σ`. -/
theorem canonical_bound (hC : CompletedMeanSquare) (hT : TransferEstimate) {η C₀ : ℝ}
    (hη : 0 < η) (hC₀ : 1 ≤ C₀) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ α β : ℝ, 0 < α → ∃ Kc : ℝ,
      ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
        (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ, (∀ i ≤ J, ∀ x, ‖iteratedDeriv i W x‖ ≤ N) →
        ∀ D Hh X F : ℝ, 1 ≤ D → 1 ≤ Hh → 1 ≤ X → 1 ≤ F → X * F ≤ D ^ C₀ →
          Hh * D ^ η ≤ X * F →
        ∀ (Fs : Finset (Ideal (𝓞 K))) (T : Finset (𝓞 K)),
          (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
            (absNorm f : ℝ) < 2 * F) →
          (∀ k ∈ T, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hh) →
          rowE ξ W X Fs T ≤ Kc * N ^ 2 * D ^ ε * (X * F) ^ 2 := by
  have hall : ∀ j, CanonicalAt η C₀ j := fun j =>
    Nat.rec (canonicalAt_zero η C₀) (fun _ ih => canonicalAt_succ hC hT hη hC₀ ih) j
  intro ε hε
  obtain ⟨J, hJ⟩ := hall ⌈C₀ / η⌉₊ ε hε
  refine ⟨J, fun α β hα => ?_⟩
  obtain ⟨Kc, hKc⟩ := hJ α β hα
  refine ⟨Kc, fun ξ W hWs hWsupp N hN D Hh X F hD hH hX hF hXF hgap Fs T hFs hT => ?_⟩
  refine hKc ξ W hWs hWsupp N hN D Hh X F hD hH hX hF hXF hgap ?_ Fs T hFs hT
  have hdη : 1 ≤ D ^ η := Real.one_le_rpow hD hη.le
  have hHS : Hh ≤ X * F := le_trans (le_mul_of_one_le_right (by linarith) hdη) hgap
  have hjη : C₀ ≤ (⌈C₀ / η⌉₊ : ℝ) * η := by
    have := Nat.le_ceil (C₀ / η)
    rw [div_le_iff₀ hη] at this
    exact this
  exact hHS.trans (hXF.trans (Real.rpow_le_rpow_of_exponent_le hD hjη))

/-- **The dual mean square at every `ϑ > 0`** from the displayed estimates: the companion paper's
proof of its Proposition 3.1 ("For large `D`, Proposition 5.1 applies with `κ=ϑ/2` and `C_0=2`"), here
with `C₀ = 1` since `Σ = D/B ≤ D`; the scales `X < 1` and the bounded `D` go by counting. -/
theorem dualMeanSquare_of_completed_transfer (hC : CompletedMeanSquare) (hT : TransferEstimate)
    {ϑ : ℝ} (hϑ : 0 < ϑ) : DualMeanSquare ϑ := by
  intro ε hε
  obtain ⟨J, hJ⟩ := canonical_bound hC hT (η := ϑ / 2) (C₀ := 1) (by positivity) le_rfl ε hε
  refine ⟨J, fun α β hα C hC1 => ?_⟩
  obtain ⟨K, hK⟩ := hJ α β hα
  set β₁ := max β 1 with hβ₁def
  have hβ₁ : 1 ≤ β₁ := le_max_right _ _
  have hk := kappa_pos
  set K₁ := 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 3 * C with hK₁
  set K₂ := 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 2 * C ^ (1 + 2 / ϑ) with hK₂
  have hC0 : 0 < C := by linarith
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  refine ⟨max K 0 + K₁ + K₂, ?_⟩
  intro ξ W hWs hWsupp N hN D B F Hc hD hB hF hHc hHcle Fs T hFs hT
  show rowE ξ W (D / (B * F)) Fs T ≤ (max K 0 + K₁ + K₂) * N ^ 2 * D ^ ε * (D / B) ^ 2
  have hW₁ : ∀ x, β₁ < x → W x = 0 := fun x hx =>
    hWsupp x (Or.inr (lt_of_le_of_lt (le_max_left _ _) hx))
  have hN' : ∀ x, ‖W x‖ ≤ N := fun x => by
    have := hN 0 (Nat.zero_le _) x
    rwa [iteratedDeriv_zero] at this
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN' 0)
  have hD0 : 0 < D := by linarith
  have hB0 : 0 < B := by linarith
  have hF0 : 0 < F := by linarith
  have hDe : 1 ≤ D ^ ε := Real.one_le_rpow hD hε.le
  set X := D / (B * F) with hXdef
  have hX0 : 0 < X := by positivity
  have hXF : X * F = D / B := by rw [hXdef]; field_simp
  have hDB : 0 < D / B := by positivity
  have hRHS : ∀ c : ℝ, 0 ≤ c → c ≤ max K 0 + K₁ + K₂ →
      c * N ^ 2 * (D / B) ^ 2 ≤ (max K 0 + K₁ + K₂) * N ^ 2 * D ^ ε * (D / B) ^ 2 := by
    intro c hc0 hc
    calc c * N ^ 2 * (D / B) ^ 2 = c * N ^ 2 * 1 * (D / B) ^ 2 := by ring
      _ ≤ (max K 0 + K₁ + K₂) * N ^ 2 * D ^ ε * (D / B) ^ 2 := by gcongr
  have hR0 : 0 ≤ (max K 0 + K₁ + K₂) * N ^ 2 * D ^ ε * (D / B) ^ 2 := by positivity
  -- `𝓗 < 1`: no rows `k`
  by_cases hH1 : 1 ≤ Hc
  swap
  · have hTe : T = ∅ := Finset.eq_empty_of_forall_notMem fun k hk =>
      hH1 ((one_le_absNorm_span (hT k hk).1).trans (hT k hk).2)
    rw [hTe]
    unfold rowE
    simpa using hR0
  -- the bound on `𝓗`: `𝓗 ≤ C·D/(D^ϑ·B²)`
  have hDϑ : D ^ (1 + ϑ) = D * D ^ ϑ := by rw [Real.rpow_add hD0, Real.rpow_one]
  have hDϑ1 : 1 ≤ D ^ ϑ := Real.one_le_rpow hD hϑ.le
  have hHc2 : Hc ≤ C * D / (D ^ ϑ * B ^ 2) := by
    calc Hc ≤ C * D ^ 2 / (D ^ (1 + ϑ) * B ^ 2) := hHcle
      _ = C * D / (D ^ ϑ * B ^ 2) := by rw [hDϑ]; field_simp
  have hB2 : B ≤ B ^ 2 := le_self_pow₀ hB (by norm_num)
  have hDB2 : 1 ≤ D ^ ϑ * B ^ 2 := one_le_mul_of_one_le_of_one_le hDϑ1 (hB.trans hB2)
  have hHcS : Hc ≤ C * (D / B) := by
    refine hHc2.trans ?_
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_left (by positivity) hB0
    calc B = 1 * B := (one_mul B).symm
      _ ≤ D ^ ϑ * B := mul_le_mul_of_nonneg_right hDϑ1 hB0.le
      _ ≤ D ^ ϑ * B ^ 2 := mul_le_mul_of_nonneg_left hB2 (by positivity)
  rcases lt_or_ge (β₁ * X) 1 with hβX | hβX
  · -- empty column sums
    rw [rowE_eq_zero_of_lt ξ hW₁ hX0 hβX]
    exact hR0
  have hcount := rowE_le_count ξ hW₁ hN' hH1 hF hX0 hβX hFs hT
  rcases lt_or_ge X 1 with hX1 | hX1
  · -- `X < 1`: `F ≤ β·Σ` and `𝓗 ≤ C·Σ`
    have hFle : F ≤ β₁ * (D / B) := by
      rw [← hXF]
      calc F = 1 * F := (one_mul F).symm
        _ ≤ (β₁ * X) * F := mul_le_mul_of_nonneg_right hβX hF0.le
        _ = β₁ * (X * F) := by ring
    refine le_trans hcount (le_trans ?_ (hRHS K₁ hK₁0 (by linarith)))
    have hβX2 : (β₁ * X) ^ 2 ≤ β₁ ^ 2 := by
      have : β₁ * X ≤ β₁ := mul_le_of_le_one_right (by linarith) hX1.le
      exact pow_le_pow_left₀ (by positivity) this 2
    calc 98 * (2 * kappa + 5) ^ 3 * (β₁ * X) ^ 2 * N ^ 2 * F * Hc
        ≤ 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 2 * N ^ 2 * (β₁ * (D / B)) * (C * (D / B)) := by
          gcongr
      _ = K₁ * N ^ 2 * (D / B) ^ 2 := by rw [hK₁]; ring
  rcases le_or_gt C (D ^ (ϑ / 2)) with hCD | hCD
  · -- large `D`: the canonical bound at gap `ϑ/2`
    have hgap : Hc * D ^ (ϑ / 2) ≤ X * F := by
      rw [hXF]
      have hsq : D ^ ϑ = D ^ (ϑ / 2) * D ^ (ϑ / 2) := by
        rw [← Real.rpow_add hD0]; ring_nf
      have hd2 : 0 < D ^ (ϑ / 2) := Real.rpow_pos_of_pos hD0 _
      calc Hc * D ^ (ϑ / 2) ≤ C * D / (D ^ ϑ * B ^ 2) * D ^ (ϑ / 2) :=
            mul_le_mul_of_nonneg_right hHc2 hd2.le
        _ = C * D / (D ^ (ϑ / 2) * B ^ 2) := by rw [hsq]; field_simp
        _ ≤ D ^ (ϑ / 2) * D / (D ^ (ϑ / 2) * B ^ 2) := by gcongr
        _ = D / B ^ 2 := by field_simp
        _ ≤ D / B := div_le_div_of_nonneg_left hD0.le hB0 hB2
    have hXFD : X * F ≤ D ^ (1 : ℝ) := by
      rw [hXF, Real.rpow_one]
      exact div_le_self hD0.le hB
    have h := hK ξ W hWs hWsupp N hN D Hc X F hD hH1 hX1 hF hXFD hgap Fs T hFs hT
    rw [hXF] at h
    refine h.trans ?_
    gcongr
    linarith [le_max_left K 0]
  · -- bounded `D`: `D ≤ C^{2/ϑ}`, counting
    have hDle : D ≤ C ^ (2 / ϑ) := by
      have h1 : (D ^ (ϑ / 2)) ^ (2 / ϑ) ≤ C ^ (2 / ϑ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hD0.le _) hCD.le (by positivity)
      rwa [← Real.rpow_mul hD0.le, show ϑ / 2 * (2 / ϑ) = 1 by field_simp, Real.rpow_one] at h1
    have hHcC : Hc ≤ C ^ (1 + 2 / ϑ) := by
      have h1 : Hc ≤ C * D := hHc2.trans (div_le_self (by positivity) hDB2)
      calc Hc ≤ C * D := h1
        _ ≤ C * C ^ (2 / ϑ) := mul_le_mul_of_nonneg_left hDle hC0.le
        _ = C ^ (1 + 2 / ϑ) := by rw [Real.rpow_add hC0, Real.rpow_one]
    refine le_trans hcount (le_trans ?_ (hRHS K₂ hK₂0 (by linarith)))
    have hF2 : F ≤ F ^ 2 := le_self_pow₀ hF (by norm_num)
    calc 98 * (2 * kappa + 5) ^ 3 * (β₁ * X) ^ 2 * N ^ 2 * F * Hc
        ≤ 98 * (2 * kappa + 5) ^ 3 * (β₁ * X) ^ 2 * N ^ 2 * F ^ 2 * C ^ (1 + 2 / ϑ) := by
          gcongr
      _ = 98 * (2 * kappa + 5) ^ 3 * β₁ ^ 2 * C ^ (1 + 2 / ϑ) * N ^ 2 * (X * F) ^ 2 := by ring
      _ = K₂ * N ^ 2 * (D / B) ^ 2 := by rw [hXF, hK₂]

/-- **The third conditional milestone**: the companion paper's Propositions 5.2 and 5.4, displayed as
`CompletedMeanSquare` and `TransferEstimate`, give `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` on `Re s > 11/12`
(round 310's `ne_zero_of_dualMeanSquare` at `ϑ = (12·Re s − 11)/10`). -/
theorem ne_zero_of_completed_transfer (hC : CompletedMeanSquare) (hT : TransferEstimate) {s : ℂ}
    (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 := by
  have hϑ : 0 < (12 * s.re - 11) / 10 := by linarith
  exact ne_zero_of_dualMeanSquare hϑ (dualMeanSquare_of_completed_transfer hC hT hϑ)
    (by linarith)

end Eis

end

#print axioms Eis.canonicalAt_zero
#print axioms Eis.transferred_level
#print axioms Eis.transferred_gap
#print axioms Eis.canonicalAt_succ
#print axioms Eis.canonical_bound
#print axioms Eis.dualMeanSquare_of_completed_transfer
#print axioms Eis.ne_zero_of_completed_transfer
