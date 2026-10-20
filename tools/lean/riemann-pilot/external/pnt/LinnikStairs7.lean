/-
# Round 612: the staircase of the Weyl-conditional route (Ingham steps on `[4/7, 5/7]`, Huxley's on `[16/21, 11/12]`)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Sixty density estimates, each an instance of a parametric argument of the stack, and the count above `11/12`:

* `charDensity_in7_0` … `charDensity_in7_19`: `LinnikInghamC.charDensity_ingham_c` at `ε = 1/8000` on twenty equal
  steps `[σ₁, σ₂]` from `4/7` to `5/7`, with the exponent `3/(2 − σ₂) + 1/2000`, Ingham's curve at the right end plus
  `1/2000`.
* `parHx7_0` … `parHx7_19`, `charDensity_hx7_0` … `charDensity_hx7_19`: `LinnikHuxStep.charDensity_gen` at parameters
  found by a linear program and checked in rational arithmetic (scratch) on twenty equal steps from `16/21` to `5/6`,
  with the exponent `3/(3σ₁ − 1) + 1/2000`, Huxley's curve at the left end plus `1/2000`.
* `parHy_0` … `parHy_19`, `charDensity_hy_0` … `charDensity_hy_19`: `LinnikHuxStepY.charDensity_genY`, under
  `LinnikWeyl.PYWeyl`, on twenty equal steps from `5/6` to `11/12`, with the exponent `3/(3σ₁ − 1) + 1/2000` on steps
  `1` to `19` and the least the step allows, `50159 / 25000`, on step `0` (where `3/(3σ₁ − 1) + 1/2000 = 4001/2000` is
  not reachable: the height `y ≥ 3(1/6 + 2ε + 1/2000)` and the first Huxley term force `A ≥ 4y + 2ε`).
* `card_le_one_of_gt`: above `11/12` at most one character is counted (the zero-free half-plane); `charDensity_hy_top`:
  the last step's exponent on `[73 / 80, 1]`, under `PYWeyl`.

The file imports `LinnikInghamC.lean`, `LinnikHuxStep.lean` and `LinnikHuxStepY.lean`.
-/
import LinnikInghamC
import LinnikHuxStep
import LinnikHuxStepY

open Complex Real Finset

noncomputable section

namespace LinnikStairs7

open DirichletCharacter LinnikHuxStep LinnikHuxStepY

/-! ### Ingham's steps on `[4/7, 5/7]` -/

open scoped Classical in
/-- **Ingham's step `0`**: the exponent `840199 / 398000` on `[4 / 7, 81 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 81 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 11 / 398`, `δ₀ = 1 / 14`. -/
theorem charDensity_in7_0 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 4 / 7 ≤ σ → σ ≤ 81 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840199 / 398000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 11 / 398)
    (δ₀ := 1 / 14) (σ₂ := 81 / 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (11 / 398 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (840199 / 398000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `1`**: the exponent `140033 / 66000` on `[81 / 140, 41 / 70]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 41 / 70`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 33`, `δ₀ = 11 / 140`. -/
theorem charDensity_in7_1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 81 / 140 ≤ σ → σ ≤ 41 / 70 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((140033 / 66000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 33)
    (δ₀ := 11 / 140) (σ₂ := 41 / 70)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 33 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (140033 / 66000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `2`**: the exponent `840197 / 394000` on `[41 / 70, 83 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 83 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 13 / 394`, `δ₀ = 3 / 35`. -/
theorem charDensity_in7_2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 41 / 70 ≤ σ → σ ≤ 83 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840197 / 394000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 13 / 394)
    (δ₀ := 3 / 35) (σ₂ := 83 / 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (13 / 394 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (840197 / 394000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `3`**: the exponent `30007 / 14000` on `[83 / 140, 3 / 5]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 3 / 5`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 28`, `δ₀ = 13 / 140`. -/
theorem charDensity_in7_3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 83 / 140 ≤ σ → σ ≤ 3 / 5 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((30007 / 14000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 28)
    (δ₀ := 13 / 140) (σ₂ := 3 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 28 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (30007 / 14000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `4`**: the exponent `56013 / 26000` on `[3 / 5, 17 / 28]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 17 / 28`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 26`, `δ₀ = 1 / 10`. -/
theorem charDensity_in7_4 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 3 / 5 ≤ σ → σ ≤ 17 / 28 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((56013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 26)
    (δ₀ := 1 / 10) (σ₂ := 17 / 28)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 26 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (56013 / 26000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `5`**: the exponent `420097 / 194000` on `[17 / 28, 43 / 70]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 43 / 70`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 4 / 97`, `δ₀ = 3 / 28`. -/
theorem charDensity_in7_5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 17 / 28 ≤ σ → σ ≤ 43 / 70 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((420097 / 194000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 4 / 97)
    (δ₀ := 3 / 28) (σ₂ := 43 / 70)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (4 / 97 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (420097 / 194000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `6`**: the exponent `840193 / 386000` on `[43 / 70, 87 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 87 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 17 / 386`, `δ₀ = 4 / 35`. -/
theorem charDensity_in7_6 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 43 / 70 ≤ σ → σ ≤ 87 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840193 / 386000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 17 / 386)
    (δ₀ := 4 / 35) (σ₂ := 87 / 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (17 / 386 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (840193 / 386000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `7`**: the exponent `547 / 250` on `[87 / 140, 22 / 35]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 22 / 35`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 3 / 64`, `δ₀ = 17 / 140`. -/
theorem charDensity_in7_7 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 87 / 140 ≤ σ → σ ≤ 22 / 35 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((547 / 250) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 3 / 64)
    (δ₀ := 17 / 140) (σ₂ := 22 / 35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (3 / 64 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (547 / 250) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `8`**: the exponent `840191 / 382000` on `[22 / 35, 89 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 89 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 19 / 382`, `δ₀ = 9 / 70`. -/
theorem charDensity_in7_8 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 22 / 35 ≤ σ → σ ≤ 89 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840191 / 382000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 19 / 382)
    (δ₀ := 9 / 70) (σ₂ := 89 / 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (19 / 382 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (840191 / 382000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `9`**: the exponent `84019 / 38000` on `[89 / 140, 9 / 14]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 9 / 14`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 19`, `δ₀ = 19 / 140`. -/
theorem charDensity_in7_9 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 89 / 140 ≤ σ → σ ≤ 9 / 14 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((84019 / 38000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 19)
    (δ₀ := 19 / 140) (σ₂ := 9 / 14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 19 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (84019 / 38000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `10`**: the exponent `40009 / 18000` on `[9 / 14, 13 / 20]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 13 / 20`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 18`, `δ₀ = 1 / 7`. -/
theorem charDensity_in7_10 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 9 / 14 ≤ σ → σ ≤ 13 / 20 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((40009 / 18000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 18)
    (δ₀ := 1 / 7) (σ₂ := 13 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 18 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (40009 / 18000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `11`**: the exponent `210047 / 94000` on `[13 / 20, 23 / 35]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 23 / 35`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 11 / 188`, `δ₀ = 3 / 20`. -/
theorem charDensity_in7_11 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 13 / 20 ≤ σ → σ ≤ 23 / 35 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((210047 / 94000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 11 / 188)
    (δ₀ := 3 / 20) (σ₂ := 23 / 35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (11 / 188 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (210047 / 94000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `12`**: the exponent `840187 / 374000` on `[23 / 35, 93 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 93 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 23 / 374`, `δ₀ = 11 / 70`. -/
theorem charDensity_in7_12 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 23 / 35 ≤ σ → σ ≤ 93 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840187 / 374000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 23 / 374)
    (δ₀ := 11 / 70) (σ₂ := 93 / 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (23 / 374 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (840187 / 374000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `13`**: the exponent `140031 / 62000` on `[93 / 140, 47 / 70]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 47 / 70`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 2 / 31`, `δ₀ = 23 / 140`. -/
theorem charDensity_in7_13 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 93 / 140 ≤ σ → σ ≤ 47 / 70 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((140031 / 62000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 2 / 31)
    (δ₀ := 23 / 140) (σ₂ := 47 / 70)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (2 / 31 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (140031 / 62000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `14`**: the exponent `168037 / 74000` on `[47 / 70, 19 / 28]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 19 / 28`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 5 / 74`, `δ₀ = 6 / 35`. -/
theorem charDensity_in7_14 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 47 / 70 ≤ σ → σ ≤ 19 / 28 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((168037 / 74000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 5 / 74)
    (δ₀ := 6 / 35) (σ₂ := 19 / 28)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (5 / 74 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (168037 / 74000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `15`**: the exponent `105023 / 46000` on `[19 / 28, 24 / 35]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 24 / 35`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 13 / 184`, `δ₀ = 5 / 28`. -/
theorem charDensity_in7_15 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 19 / 28 ≤ σ → σ ≤ 24 / 35 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((105023 / 46000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 13 / 184)
    (δ₀ := 5 / 28) (σ₂ := 24 / 35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (13 / 184 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (105023 / 46000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `16`**: the exponent `280061 / 122000` on `[24 / 35, 97 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 97 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 9 / 122`, `δ₀ = 13 / 70`. -/
theorem charDensity_in7_16 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 24 / 35 ≤ σ → σ ≤ 97 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((280061 / 122000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 9 / 122)
    (δ₀ := 13 / 70) (σ₂ := 97 / 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (9 / 122 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (280061 / 122000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `17`**: the exponent `60013 / 26000` on `[97 / 140, 7 / 10]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 7 / 10`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 13`, `δ₀ = 27 / 140`. -/
theorem charDensity_in7_17 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 97 / 140 ≤ σ → σ ≤ 7 / 10 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((60013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 13)
    (δ₀ := 27 / 140) (σ₂ := 7 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 13 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (60013 / 26000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `18`**: the exponent `840181 / 362000` on `[7 / 10, 99 / 140]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 99 / 140`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 29 / 362`, `δ₀ = 1 / 5`. -/
theorem charDensity_in7_18 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 7 / 10 ≤ σ → σ ≤ 99 / 140 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((840181 / 362000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 29 / 362)
    (δ₀ := 1 / 5) (σ₂ := 99 / 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (29 / 362 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (840181 / 362000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `19`**: the exponent `14003 / 6000` on `[99 / 140, 5 / 7]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 5 / 7`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 12`, `δ₀ = 29 / 140`. -/
theorem charDensity_in7_19 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 99 / 140 ≤ σ → σ ≤ 5 / 7 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((14003 / 6000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 12)
    (δ₀ := 29 / 140) (σ₂ := 5 / 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 12 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (14003 / 6000) * (1 - σ) by ring] at this

/-! ### Huxley's steps on `[16/21, 5/6]`, with the fourth moment -/

/-- The parameters of Huxley's step `0` on `[16 / 21, 643 / 840]`: the exponent `14003 / 6000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_0 : Par where
  M := 1557
  a := 77779 / 100000
  lam := 116671 / 100000
  lo := 16 / 21
  hi := 643 / 840
  Ai := 233383 / 100000
  A := 14003 / 6000

theorem parHx7_0_good : parHx7_0.Good where
  hM := by simp [parHx7_0]
  ha := by simp only [parHx7_0]; norm_num
  hat := by simp only [parHx7_0, εs]; norm_num
  hlam1 := by simp only [parHx7_0, εs]; norm_num
  hlam2 := by simp only [parHx7_0, εs]; norm_num
  hlam3 := by simp only [parHx7_0]; norm_num
  hlo := by simp only [parHx7_0]; norm_num
  hhi := by simp only [parHx7_0]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_0, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_0, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_0, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_0, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_0]; norm_num
  hA16 := by simp only [parHx7_0]; norm_num

open scoped Classical in
/-- **Huxley's step `0`**: there is `C ≥ 0` such that for every `q ≥ 1`, `16 / 21 ≤ σ ≤ 643 / 840` and `T ≥ 2` at most
`C(qT)^{(14003 / 6000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_0 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 16 / 21 ≤ σ → σ ≤ 643 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((14003 / 6000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_0 parHx7_0_good

/-- The parameters of Huxley's step `1` on `[643 / 840, 323 / 420]`: the exponent `560121 / 242000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_1 : Par where
  M := 1544
  a := 4821 / 6250
  lam := 231413 / 200000
  lo := 643 / 840
  hi := 323 / 420
  Ai := 115727 / 50000
  A := 560121 / 242000

theorem parHx7_1_good : parHx7_1.Good where
  hM := by simp [parHx7_1]
  ha := by simp only [parHx7_1]; norm_num
  hat := by simp only [parHx7_1, εs]; norm_num
  hlam1 := by simp only [parHx7_1, εs]; norm_num
  hlam2 := by simp only [parHx7_1, εs]; norm_num
  hlam3 := by simp only [parHx7_1]; norm_num
  hlo := by simp only [parHx7_1]; norm_num
  hhi := by simp only [parHx7_1]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_1, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_1, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_1, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_1, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_1]; norm_num
  hA16 := by simp only [parHx7_1]; norm_num

open scoped Classical in
/--  **Huxley's step `1`**: there is `C ≥ 0` such that for every `q ≥ 1`, `643 / 840 ≤ σ ≤ 323 / 420` and `T ≥ 2` at
most `C(qT)^{(560121 / 242000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 643 / 840 ≤ σ → σ ≤ 323 / 420 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560121 / 242000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_1 parHx7_1_good

/-- The parameters of Huxley's step `2` on `[323 / 420, 649 / 840]`: the exponent `280061 / 122000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_2 : Par where
  M := 1532
  a := 9563 / 12500
  lam := 229517 / 200000
  lo := 323 / 420
  hi := 649 / 840
  Ai := 114779 / 50000
  A := 280061 / 122000

theorem parHx7_2_good : parHx7_2.Good where
  hM := by simp [parHx7_2]
  ha := by simp only [parHx7_2]; norm_num
  hat := by simp only [parHx7_2, εs]; norm_num
  hlam1 := by simp only [parHx7_2, εs]; norm_num
  hlam2 := by simp only [parHx7_2, εs]; norm_num
  hlam3 := by simp only [parHx7_2]; norm_num
  hlo := by simp only [parHx7_2]; norm_num
  hhi := by simp only [parHx7_2]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_2, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_2, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_2, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_2, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_2]; norm_num
  hA16 := by simp only [parHx7_2]; norm_num

open scoped Classical in
/--  **Huxley's step `2`**: there is `C ≥ 0` such that for every `q ≥ 1`, `323 / 420 ≤ σ ≤ 649 / 840` and `T ≥ 2` at
most `C(qT)^{(280061 / 122000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 323 / 420 ≤ σ → σ ≤ 649 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((280061 / 122000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_2 parHx7_2_good

/-- The parameters of Huxley's step `3` on `[649 / 840, 163 / 210]`: the exponent `560123 / 246000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_3 : Par where
  M := 1519
  a := 37941 / 50000
  lam := 227651 / 200000
  lo := 649 / 840
  hi := 163 / 210
  Ai := 56923 / 25000
  A := 560123 / 246000

theorem parHx7_3_good : parHx7_3.Good where
  hM := by simp [parHx7_3]
  ha := by simp only [parHx7_3]; norm_num
  hat := by simp only [parHx7_3, εs]; norm_num
  hlam1 := by simp only [parHx7_3, εs]; norm_num
  hlam2 := by simp only [parHx7_3, εs]; norm_num
  hlam3 := by simp only [parHx7_3]; norm_num
  hlo := by simp only [parHx7_3]; norm_num
  hhi := by simp only [parHx7_3]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_3, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_3, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_3, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_3, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_3]; norm_num
  hA16 := by simp only [parHx7_3]; norm_num

open scoped Classical in
/--  **Huxley's step `3`**: there is `C ≥ 0` such that for every `q ≥ 1`, `649 / 840 ≤ σ ≤ 163 / 210` and `T ≥ 2` at
most `C(qT)^{(560123 / 246000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 649 / 840 ≤ σ → σ ≤ 163 / 210 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560123 / 246000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_3 parHx7_3_good

/-- The parameters of Huxley's step `4` on `[163 / 210, 131 / 168]`: the exponent `140031 / 62000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_4 : Par where
  M := 1507
  a := 7527 / 10000
  lam := 45163 / 40000
  lo := 163 / 210
  hi := 131 / 168
  Ai := 7058 / 3125
  A := 140031 / 62000

theorem parHx7_4_good : parHx7_4.Good where
  hM := by simp [parHx7_4]
  ha := by simp only [parHx7_4]; norm_num
  hat := by simp only [parHx7_4, εs]; norm_num
  hlam1 := by simp only [parHx7_4, εs]; norm_num
  hlam2 := by simp only [parHx7_4, εs]; norm_num
  hlam3 := by simp only [parHx7_4]; norm_num
  hlo := by simp only [parHx7_4]; norm_num
  hhi := by simp only [parHx7_4]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_4, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_4, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_4, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_4, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_4]; norm_num
  hA16 := by simp only [parHx7_4]; norm_num

open scoped Classical in
/-- **Huxley's step `4`**: there is `C ≥ 0` such that for every `q ≥ 1`, `163 / 210 ≤ σ ≤ 131 / 168` and `T ≥ 2` at most
`C(qT)^{(140031 / 62000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_4 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 163 / 210 ≤ σ → σ ≤ 131 / 168 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((140031 / 62000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_4 parHx7_4_good

/-- The parameters of Huxley's step `5` on `[131 / 168, 47 / 60]`: the exponent `4481 / 2000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_5 : Par where
  M := 1495
  a := 18667 / 25000
  lam := 224009 / 200000
  lo := 131 / 168
  hi := 47 / 60
  Ai := 224049 / 100000
  A := 4481 / 2000

theorem parHx7_5_good : parHx7_5.Good where
  hM := by simp [parHx7_5]
  ha := by simp only [parHx7_5]; norm_num
  hat := by simp only [parHx7_5, εs]; norm_num
  hlam1 := by simp only [parHx7_5, εs]; norm_num
  hlam2 := by simp only [parHx7_5, εs]; norm_num
  hlam3 := by simp only [parHx7_5]; norm_num
  hlo := by simp only [parHx7_5]; norm_num
  hhi := by simp only [parHx7_5]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_5, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_5, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_5, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_5, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_5]; norm_num
  hA16 := by simp only [parHx7_5]; norm_num

open scoped Classical in
/-- **Huxley's step `5`**: there is `C ≥ 0` such that for every `q ≥ 1`, `131 / 168 ≤ σ ≤ 47 / 60` and `T ≥ 2` at most
`C(qT)^{(4481 / 2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 131 / 168 ≤ σ → σ ≤ 47 / 60 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((4481 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_5 parHx7_5_good

/-- The parameters of Huxley's step `6` on `[47 / 60, 661 / 840]`: the exponent `40009 / 18000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_6 : Par where
  M := 1483
  a := 2963 / 4000
  lam := 22223 / 20000
  lo := 47 / 60
  hi := 661 / 840
  Ai := 6946 / 3125
  A := 40009 / 18000

theorem parHx7_6_good : parHx7_6.Good where
  hM := by simp [parHx7_6]
  ha := by simp only [parHx7_6]; norm_num
  hat := by simp only [parHx7_6, εs]; norm_num
  hlam1 := by simp only [parHx7_6, εs]; norm_num
  hlam2 := by simp only [parHx7_6, εs]; norm_num
  hlam3 := by simp only [parHx7_6]; norm_num
  hlo := by simp only [parHx7_6]; norm_num
  hhi := by simp only [parHx7_6]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_6, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_6, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_6, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_6, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_6]; norm_num
  hA16 := by simp only [parHx7_6]; norm_num

open scoped Classical in
/-- **Huxley's step `6`**: there is `C ≥ 0` such that for every `q ≥ 1`, `47 / 60 ≤ σ ≤ 661 / 840` and `T ≥ 2` at most
`C(qT)^{(40009 / 18000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_6 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 47 / 60 ≤ σ → σ ≤ 661 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((40009 / 18000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_6 parHx7_6_good

/-- The parameters of Huxley's step `7` on `[661 / 840, 83 / 105]`: the exponent `560127 / 254000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_7 : Par where
  M := 1471
  a := 18373 / 25000
  lam := 220481 / 200000
  lo := 661 / 840
  hi := 83 / 105
  Ai := 110261 / 50000
  A := 560127 / 254000

theorem parHx7_7_good : parHx7_7.Good where
  hM := by simp [parHx7_7]
  ha := by simp only [parHx7_7]; norm_num
  hat := by simp only [parHx7_7, εs]; norm_num
  hlam1 := by simp only [parHx7_7, εs]; norm_num
  hlam2 := by simp only [parHx7_7, εs]; norm_num
  hlam3 := by simp only [parHx7_7]; norm_num
  hlo := by simp only [parHx7_7]; norm_num
  hhi := by simp only [parHx7_7]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_7, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_7, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_7, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_7, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_7]; norm_num
  hA16 := by simp only [parHx7_7]; norm_num

open scoped Classical in
/--  **Huxley's step `7`**: there is `C ≥ 0` such that for every `q ≥ 1`, `661 / 840 ≤ σ ≤ 83 / 105` and `T ≥ 2` at most
`C(qT)^{(560127 / 254000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx7_7 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 661 / 840 ≤ σ → σ ≤ 83 / 105 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560127 / 254000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_7 parHx7_7_good

/-- The parameters of Huxley's step `8` on `[83 / 105, 667 / 840]`: the exponent `547 / 250`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_8 : Par where
  M := 1460
  a := 36459 / 50000
  lam := 218759 / 200000
  lo := 83 / 105
  hi := 667 / 840
  Ai := 218799 / 100000
  A := 547 / 250

theorem parHx7_8_good : parHx7_8.Good where
  hM := by simp [parHx7_8]
  ha := by simp only [parHx7_8]; norm_num
  hat := by simp only [parHx7_8, εs]; norm_num
  hlam1 := by simp only [parHx7_8, εs]; norm_num
  hlam2 := by simp only [parHx7_8, εs]; norm_num
  hlam3 := by simp only [parHx7_8]; norm_num
  hlo := by simp only [parHx7_8]; norm_num
  hhi := by simp only [parHx7_8]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_8, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_8, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_8, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_8, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_8]; norm_num
  hA16 := by simp only [parHx7_8]; norm_num

open scoped Classical in
/-- **Huxley's step `8`**: there is `C ≥ 0` such that for every `q ≥ 1`, `83 / 105 ≤ σ ≤ 667 / 840` and `T ≥ 2` at most
`C(qT)^{(547 / 250)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_8 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 83 / 105 ≤ σ → σ ≤ 667 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((547 / 250) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_8 parHx7_8_good

/-- The parameters of Huxley's step `9` on `[667 / 840, 67 / 84]`: the exponent `560129 / 258000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_9 : Par where
  M := 1449
  a := 72353 / 100000
  lam := 27133 / 25000
  lo := 667 / 840
  hi := 67 / 84
  Ai := 13569 / 6250
  A := 560129 / 258000

theorem parHx7_9_good : parHx7_9.Good where
  hM := by simp [parHx7_9]
  ha := by simp only [parHx7_9]; norm_num
  hat := by simp only [parHx7_9, εs]; norm_num
  hlam1 := by simp only [parHx7_9, εs]; norm_num
  hlam2 := by simp only [parHx7_9, εs]; norm_num
  hlam3 := by simp only [parHx7_9]; norm_num
  hlo := by simp only [parHx7_9]; norm_num
  hhi := by simp only [parHx7_9]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_9, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_9, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_9, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_9, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_9]; norm_num
  hA16 := by simp only [parHx7_9]; norm_num

open scoped Classical in
/--  **Huxley's step `9`**: there is `C ≥ 0` such that for every `q ≥ 1`, `667 / 840 ≤ σ ≤ 67 / 84` and `T ≥ 2` at most
`C(qT)^{(560129 / 258000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx7_9 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 667 / 840 ≤ σ → σ ≤ 67 / 84 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560129 / 258000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_9 parHx7_9_good

/-- The parameters of Huxley's step `10` on `[67 / 84, 673 / 840]`: the exponent `56013 / 26000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_10 : Par where
  M := 1437
  a := 17949 / 25000
  lam := 215393 / 200000
  lo := 67 / 84
  hi := 673 / 840
  Ai := 107717 / 50000
  A := 56013 / 26000

theorem parHx7_10_good : parHx7_10.Good where
  hM := by simp [parHx7_10]
  ha := by simp only [parHx7_10]; norm_num
  hat := by simp only [parHx7_10, εs]; norm_num
  hlam1 := by simp only [parHx7_10, εs]; norm_num
  hlam2 := by simp only [parHx7_10, εs]; norm_num
  hlam3 := by simp only [parHx7_10]; norm_num
  hlo := by simp only [parHx7_10]; norm_num
  hhi := by simp only [parHx7_10]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_10, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_10, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_10, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_10, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_10]; norm_num
  hA16 := by simp only [parHx7_10]; norm_num

open scoped Classical in
/-- **Huxley's step `10`**: there is `C ≥ 0` such that for every `q ≥ 1`, `67 / 84 ≤ σ ≤ 673 / 840` and `T ≥ 2` at most
`C(qT)^{(56013 / 26000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_10 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 67 / 84 ≤ σ → σ ≤ 673 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((56013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_10 parHx7_10_good

/-- The parameters of Huxley's step `11` on `[673 / 840, 169 / 210]`: the exponent `560131 / 262000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_11 : Par where
  M := 1426
  a := 4453 / 6250
  lam := 213749 / 200000
  lo := 673 / 840
  hi := 169 / 210
  Ai := 21379 / 10000
  A := 560131 / 262000

theorem parHx7_11_good : parHx7_11.Good where
  hM := by simp [parHx7_11]
  ha := by simp only [parHx7_11]; norm_num
  hat := by simp only [parHx7_11, εs]; norm_num
  hlam1 := by simp only [parHx7_11, εs]; norm_num
  hlam2 := by simp only [parHx7_11, εs]; norm_num
  hlam3 := by simp only [parHx7_11]; norm_num
  hlo := by simp only [parHx7_11]; norm_num
  hhi := by simp only [parHx7_11]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_11, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_11, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_11, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_11, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_11]; norm_num
  hA16 := by simp only [parHx7_11]; norm_num

open scoped Classical in
/--  **Huxley's step `11`**: there is `C ≥ 0` such that for every `q ≥ 1`, `673 / 840 ≤ σ ≤ 169 / 210` and `T ≥ 2` at
most `C(qT)^{(560131 / 262000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_11 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 673 / 840 ≤ σ → σ ≤ 169 / 210 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560131 / 262000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_11 parHx7_11_good

/-- The parameters of Huxley's step `12` on `[169 / 210, 97 / 120]`: the exponent `140033 / 66000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_12 : Par where
  M := 1416
  a := 17677 / 25000
  lam := 212129 / 200000
  lo := 169 / 210
  hi := 97 / 120
  Ai := 212171 / 100000
  A := 140033 / 66000

theorem parHx7_12_good : parHx7_12.Good where
  hM := by simp [parHx7_12]
  ha := by simp only [parHx7_12]; norm_num
  hat := by simp only [parHx7_12, εs]; norm_num
  hlam1 := by simp only [parHx7_12, εs]; norm_num
  hlam2 := by simp only [parHx7_12, εs]; norm_num
  hlam3 := by simp only [parHx7_12]; norm_num
  hlo := by simp only [parHx7_12]; norm_num
  hhi := by simp only [parHx7_12]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_12, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_12, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_12, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_12, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_12]; norm_num
  hA16 := by simp only [parHx7_12]; norm_num

open scoped Classical in
/-- **Huxley's step `12`**: there is `C ≥ 0` such that for every `q ≥ 1`, `169 / 210 ≤ σ ≤ 97 / 120` and `T ≥ 2` at most
`C(qT)^{(140033 / 66000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_12 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 169 / 210 ≤ σ → σ ≤ 97 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((140033 / 66000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_12 parHx7_12_good

/-- The parameters of Huxley's step `13` on `[97 / 120, 341 / 420]`: the exponent `80019 / 38000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_13 : Par where
  M := 1405
  a := 70177 / 100000
  lam := 26317 / 25000
  lo := 97 / 120
  hi := 341 / 420
  Ai := 13161 / 6250
  A := 80019 / 38000

theorem parHx7_13_good : parHx7_13.Good where
  hM := by simp [parHx7_13]
  ha := by simp only [parHx7_13]; norm_num
  hat := by simp only [parHx7_13, εs]; norm_num
  hlam1 := by simp only [parHx7_13, εs]; norm_num
  hlam2 := by simp only [parHx7_13, εs]; norm_num
  hlam3 := by simp only [parHx7_13]; norm_num
  hlo := by simp only [parHx7_13]; norm_num
  hhi := by simp only [parHx7_13]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_13, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_13, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_13, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_13, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_13]; norm_num
  hA16 := by simp only [parHx7_13]; norm_num

open scoped Classical in
/-- **Huxley's step `13`**: there is `C ≥ 0` such that for every `q ≥ 1`, `97 / 120 ≤ σ ≤ 341 / 420` and `T ≥ 2` at most
`C(qT)^{(80019 / 38000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_13 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 97 / 120 ≤ σ → σ ≤ 341 / 420 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((80019 / 38000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_13 parHx7_13_good

/-- The parameters of Huxley's step `14` on `[341 / 420, 137 / 168]`: the exponent `280067 / 134000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_14 : Par where
  M := 1395
  a := 69653 / 100000
  lam := 52241 / 50000
  lo := 341 / 420
  hi := 137 / 168
  Ai := 41801 / 20000
  A := 280067 / 134000

theorem parHx7_14_good : parHx7_14.Good where
  hM := by simp [parHx7_14]
  ha := by simp only [parHx7_14]; norm_num
  hat := by simp only [parHx7_14, εs]; norm_num
  hlam1 := by simp only [parHx7_14, εs]; norm_num
  hlam2 := by simp only [parHx7_14, εs]; norm_num
  hlam3 := by simp only [parHx7_14]; norm_num
  hlo := by simp only [parHx7_14]; norm_num
  hhi := by simp only [parHx7_14]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_14, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_14, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_14, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_14, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_14]; norm_num
  hA16 := by simp only [parHx7_14]; norm_num

open scoped Classical in
/--  **Huxley's step `14`**: there is `C ≥ 0` such that for every `q ≥ 1`, `341 / 420 ≤ σ ≤ 137 / 168` and `T ≥ 2` at
most `C(qT)^{(280067 / 134000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_14 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 341 / 420 ≤ σ → σ ≤ 137 / 168 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((280067 / 134000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_14 parHx7_14_good

/-- The parameters of Huxley's step `15` on `[137 / 168, 86 / 105]`: the exponent `112027 / 54000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_15 : Par where
  M := 1384
  a := 69137 / 100000
  lam := 25927 / 25000
  lo := 137 / 168
  hi := 86 / 105
  Ai := 207457 / 100000
  A := 112027 / 54000

theorem parHx7_15_good : parHx7_15.Good where
  hM := by simp [parHx7_15]
  ha := by simp only [parHx7_15]; norm_num
  hat := by simp only [parHx7_15, εs]; norm_num
  hlam1 := by simp only [parHx7_15, εs]; norm_num
  hlam2 := by simp only [parHx7_15, εs]; norm_num
  hlam3 := by simp only [parHx7_15]; norm_num
  hlo := by simp only [parHx7_15]; norm_num
  hhi := by simp only [parHx7_15]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_15, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_15, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_15, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_15, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_15]; norm_num
  hA16 := by simp only [parHx7_15]; norm_num

open scoped Classical in
/-- **Huxley's step `15`**: there is `C ≥ 0` such that for every `q ≥ 1`, `137 / 168 ≤ σ ≤ 86 / 105` and `T ≥ 2` at most
`C(qT)^{(112027 / 54000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_15 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 137 / 168 ≤ σ → σ ≤ 86 / 105 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((112027 / 54000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_15 parHx7_15_good

/-- The parameters of Huxley's step `16` on `[86 / 105, 691 / 840]`: the exponent `70017 / 34000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_16 : Par where
  M := 1374
  a := 17157 / 25000
  lam := 205889 / 200000
  lo := 86 / 105
  hi := 691 / 840
  Ai := 51483 / 25000
  A := 70017 / 34000

theorem parHx7_16_good : parHx7_16.Good where
  hM := by simp [parHx7_16]
  ha := by simp only [parHx7_16]; norm_num
  hat := by simp only [parHx7_16, εs]; norm_num
  hlam1 := by simp only [parHx7_16, εs]; norm_num
  hlam2 := by simp only [parHx7_16, εs]; norm_num
  hlam3 := by simp only [parHx7_16]; norm_num
  hlo := by simp only [parHx7_16]; norm_num
  hhi := by simp only [parHx7_16]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_16, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_16, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_16, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_16, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_16]; norm_num
  hA16 := by simp only [parHx7_16]; norm_num

open scoped Classical in
/-- **Huxley's step `16`**: there is `C ≥ 0` such that for every `q ≥ 1`, `86 / 105 ≤ σ ≤ 691 / 840` and `T ≥ 2` at most
`C(qT)^{(70017 / 34000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7_16 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 86 / 105 ≤ σ → σ ≤ 691 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((70017 / 34000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_16 parHx7_16_good

/-- The parameters of Huxley's step `17` on `[691 / 840, 347 / 420]`: the exponent `560137 / 274000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_17 : Par where
  M := 1364
  a := 2129 / 3125
  lam := 204389 / 200000
  lo := 691 / 840
  hi := 347 / 420
  Ai := 204429 / 100000
  A := 560137 / 274000

theorem parHx7_17_good : parHx7_17.Good where
  hM := by simp [parHx7_17]
  ha := by simp only [parHx7_17]; norm_num
  hat := by simp only [parHx7_17, εs]; norm_num
  hlam1 := by simp only [parHx7_17, εs]; norm_num
  hlam2 := by simp only [parHx7_17, εs]; norm_num
  hlam3 := by simp only [parHx7_17]; norm_num
  hlo := by simp only [parHx7_17]; norm_num
  hhi := by simp only [parHx7_17]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_17, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_17, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_17, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_17, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_17]; norm_num
  hA16 := by simp only [parHx7_17]; norm_num

open scoped Classical in
/--  **Huxley's step `17`**: there is `C ≥ 0` such that for every `q ≥ 1`, `691 / 840 ≤ σ ≤ 347 / 420` and `T ≥ 2` at
most `C(qT)^{(560137 / 274000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_17 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 691 / 840 ≤ σ → σ ≤ 347 / 420 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560137 / 274000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_17 parHx7_17_good

/-- The parameters of Huxley's step `18` on `[347 / 420, 697 / 840]`: the exponent `280069 / 138000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_18 : Par where
  M := 1354
  a := 33817 / 50000
  lam := 202907 / 200000
  lo := 347 / 420
  hi := 697 / 840
  Ai := 50737 / 25000
  A := 280069 / 138000

theorem parHx7_18_good : parHx7_18.Good where
  hM := by simp [parHx7_18]
  ha := by simp only [parHx7_18]; norm_num
  hat := by simp only [parHx7_18, εs]; norm_num
  hlam1 := by simp only [parHx7_18, εs]; norm_num
  hlam2 := by simp only [parHx7_18, εs]; norm_num
  hlam3 := by simp only [parHx7_18]; norm_num
  hlo := by simp only [parHx7_18]; norm_num
  hhi := by simp only [parHx7_18]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_18, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_18, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_18, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_18, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_18]; norm_num
  hA16 := by simp only [parHx7_18]; norm_num

open scoped Classical in
/--  **Huxley's step `18`**: there is `C ≥ 0` such that for every `q ≥ 1`, `347 / 420 ≤ σ ≤ 697 / 840` and `T ≥ 2` at
most `C(qT)^{(280069 / 138000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hx7_18 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 347 / 420 ≤ σ → σ ≤ 697 / 840 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((280069 / 138000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_18 parHx7_18_good

/-- The parameters of Huxley's step `19` on `[697 / 840, 5 / 6]`: the exponent `560139 / 278000`
(`3/(3σ₁ − 1) + 1/2000` at the left end). -/
def parHx7_19 : Par where
  M := 1344
  a := 67147 / 100000
  lam := 100723 / 100000
  lo := 697 / 840
  hi := 5 / 6
  Ai := 12593 / 6250
  A := 560139 / 278000

theorem parHx7_19_good : parHx7_19.Good where
  hM := by simp [parHx7_19]
  ha := by simp only [parHx7_19]; norm_num
  hat := by simp only [parHx7_19, εs]; norm_num
  hlam1 := by simp only [parHx7_19, εs]; norm_num
  hlam2 := by simp only [parHx7_19, εs]; norm_num
  hlam3 := by simp only [parHx7_19]; norm_num
  hlo := by simp only [parHx7_19]; norm_num
  hhi := by simp only [parHx7_19]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7_19, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7_19, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7_19, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7_19, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7_19]; norm_num
  hA16 := by simp only [parHx7_19]; norm_num

open scoped Classical in
/--  **Huxley's step `19`**: there is `C ≥ 0` such that for every `q ≥ 1`, `697 / 840 ≤ σ ≤ 5 / 6` and `T ≥ 2` at most
`C(qT)^{(560139 / 278000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx7_19 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 697 / 840 ≤ σ → σ ≤ 5 / 6 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((560139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7_19 parHx7_19_good

/-! ### The steps on `[5/6, 11/12]`, under the pointwise bound -/

/-- The parameters of the step `0` above `5/6`, on `[5 / 6, 67 / 80]`: the exponent `50159 / 25000`, the
height `y = 12539 / 25000` (`cy = 25053 / 50`), under the pointwise bound. -/
def parHy_0 : ParY where
  M := 1333
  a := 16641 / 25000
  lam := 50157 / 50000
  lo := 5 / 6
  hi := 67 / 80
  Ai := 40127 / 20000
  A := 50159 / 25000
  cy := 25053 / 50

theorem parHy_0_good : parHy_0.Good where
  hM := by simp [parHy_0]
  ha := by simp only [parHy_0]; norm_num
  hat := by simp only [parHy_0, εs]; norm_num
  hlam1 := by simp only [parHy_0, εs]; norm_num
  hlam2 := by simp only [parHy_0, εs]; norm_num
  hlam3 := by simp only [parHy_0]; norm_num
  hlo := by simp only [parHy_0]; norm_num
  hhi := by simp only [parHy_0]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_0, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_0, εs] at *
    nlinarith
  h5 := by simp only [parHy_0, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_0, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_0]; norm_num
  hA16 := by simp only [parHy_0]; norm_num

open scoped Classical in
/-- **The step `0` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `5 / 6 ≤ σ ≤ 67 / 80`
and `T ≥ 2` at most `C(qT)^{(50159 / 25000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_0 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 6 ≤ σ → σ ≤ 67 / 80 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((50159 / 25000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_0 parHy_0_good hPY

/-- The parameters of the step `1` above `5/6`, on `[67 / 80, 101 / 120]`: the exponent `480121 / 242000`, the
height `y = 49537 / 100000` (`cy = 49487 / 100`), under the pointwise bound. -/
def parHy_1 : ParY where
  M := 1324
  a := 66117 / 100000
  lam := 49589 / 50000
  lo := 67 / 80
  hi := 101 / 120
  Ai := 198397 / 100000
  A := 480121 / 242000
  cy := 49487 / 100

theorem parHy_1_good : parHy_1.Good where
  hM := by simp [parHy_1]
  ha := by simp only [parHy_1]; norm_num
  hat := by simp only [parHy_1, εs]; norm_num
  hlam1 := by simp only [parHy_1, εs]; norm_num
  hlam2 := by simp only [parHy_1, εs]; norm_num
  hlam3 := by simp only [parHy_1]; norm_num
  hlo := by simp only [parHy_1]; norm_num
  hhi := by simp only [parHy_1]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_1, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_1, εs] at *
    nlinarith
  h5 := by simp only [parHy_1, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_1, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_1]; norm_num
  hA16 := by simp only [parHy_1]; norm_num

open scoped Classical in
/--  **The step `1` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`67 / 80 ≤ σ ≤ 101 / 120` and `T ≥ 2` at most `C(qT)^{(480121 / 242000)(1−σ)}(log qT)^{10}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_1 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 67 / 80 ≤ σ → σ ≤ 101 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480121 / 242000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_1 parHy_1_good hPY

/-- The parameters of the step `2` above `5/6`, on `[101 / 120, 203 / 240]`: the exponent `240061 / 122000`, the
height `y = 48933 / 100000` (`cy = 48883 / 100`), under the pointwise bound. -/
def parHy_2 : ParY where
  M := 1313
  a := 2623 / 4000
  lam := 19673 / 20000
  lo := 101 / 120
  hi := 203 / 240
  Ai := 196771 / 100000
  A := 240061 / 122000
  cy := 48883 / 100

theorem parHy_2_good : parHy_2.Good where
  hM := by simp [parHy_2]
  ha := by simp only [parHy_2]; norm_num
  hat := by simp only [parHy_2, εs]; norm_num
  hlam1 := by simp only [parHy_2, εs]; norm_num
  hlam2 := by simp only [parHy_2, εs]; norm_num
  hlam3 := by simp only [parHy_2]; norm_num
  hlo := by simp only [parHy_2]; norm_num
  hhi := by simp only [parHy_2]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_2, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_2, εs] at *
    nlinarith
  h5 := by simp only [parHy_2, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_2, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_2]; norm_num
  hA16 := by simp only [parHy_2]; norm_num

open scoped Classical in
/--  **The step `2` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`101 / 120 ≤ σ ≤ 203 / 240` and `T ≥ 2` at most `C(qT)^{(240061 / 122000)(1−σ)}(log qT)^{10}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_2 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 101 / 120 ≤ σ → σ ≤ 203 / 240 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((240061 / 122000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_2 parHy_2_good hPY

/-- The parameters of the step `3` above `5/6`, on `[203 / 240, 17 / 20]`: the exponent `160041 / 82000`, the
height `y = 6043 / 12500` (`cy = 24147 / 50`), under the pointwise bound. -/
def parHy_3 : ParY where
  M := 1302
  a := 32521 / 50000
  lam := 195131 / 200000
  lo := 203 / 240
  hi := 17 / 20
  Ai := 195171 / 100000
  A := 160041 / 82000
  cy := 24147 / 50

theorem parHy_3_good : parHy_3.Good where
  hM := by simp [parHy_3]
  ha := by simp only [parHy_3]; norm_num
  hat := by simp only [parHy_3, εs]; norm_num
  hlam1 := by simp only [parHy_3, εs]; norm_num
  hlam2 := by simp only [parHy_3, εs]; norm_num
  hlam3 := by simp only [parHy_3]; norm_num
  hlo := by simp only [parHy_3]; norm_num
  hhi := by simp only [parHy_3]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_3, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_3, εs] at *
    nlinarith
  h5 := by simp only [parHy_3, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_3, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_3]; norm_num
  hA16 := by simp only [parHy_3]; norm_num

open scoped Classical in
/--  **The step `3` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`203 / 240 ≤ σ ≤ 17 / 20` and `T ≥ 2` at most `C(qT)^{(160041 / 82000)(1−σ)}(log qT)^{10}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_3 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 203 / 240 ≤ σ → σ ≤ 17 / 20 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((160041 / 82000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_3 parHy_3_good hPY

/-- The parameters of the step `4` above `5/6`, on `[17 / 20, 41 / 48]`: the exponent `120031 / 62000`, the
height `y = 5971 / 12500` (`cy = 23859 / 50`), under the pointwise bound. -/
def parHy_4 : ParY where
  M := 1292
  a := 64517 / 100000
  lam := 48389 / 50000
  lo := 17 / 20
  hi := 41 / 48
  Ai := 96799 / 50000
  A := 120031 / 62000
  cy := 23859 / 50

theorem parHy_4_good : parHy_4.Good where
  hM := by simp [parHy_4]
  ha := by simp only [parHy_4]; norm_num
  hat := by simp only [parHy_4, εs]; norm_num
  hlam1 := by simp only [parHy_4, εs]; norm_num
  hlam2 := by simp only [parHy_4, εs]; norm_num
  hlam3 := by simp only [parHy_4]; norm_num
  hlo := by simp only [parHy_4]; norm_num
  hhi := by simp only [parHy_4]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_4, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_4, εs] at *
    nlinarith
  h5 := by simp only [parHy_4, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_4, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_4]; norm_num
  hA16 := by simp only [parHy_4]; norm_num

open scoped Classical in
/-- **The step `4` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `17 / 20 ≤ σ ≤ 41 / 48`
and `T ≥ 2` at most `C(qT)^{(120031 / 62000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_4 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 17 / 20 ≤ σ → σ ≤ 41 / 48 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((120031 / 62000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_4 parHy_4_good hPY

/-- The parameters of the step `5` above `5/6`, on `[41 / 48, 103 / 120]`: the exponent `3841 / 2000`, the
height `y = 23603 / 50000` (`cy = 11789 / 25`), under the pointwise bound. -/
def parHy_5 : ParY where
  M := 1282
  a := 64001 / 100000
  lam := 24001 / 25000
  lo := 41 / 48
  hi := 103 / 120
  Ai := 192049 / 100000
  A := 3841 / 2000
  cy := 11789 / 25

theorem parHy_5_good : parHy_5.Good where
  hM := by simp [parHy_5]
  ha := by simp only [parHy_5]; norm_num
  hat := by simp only [parHy_5, εs]; norm_num
  hlam1 := by simp only [parHy_5, εs]; norm_num
  hlam2 := by simp only [parHy_5, εs]; norm_num
  hlam3 := by simp only [parHy_5]; norm_num
  hlo := by simp only [parHy_5]; norm_num
  hhi := by simp only [parHy_5]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_5, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_5, εs] at *
    nlinarith
  h5 := by simp only [parHy_5, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_5, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_5]; norm_num
  hA16 := by simp only [parHy_5]; norm_num

open scoped Classical in
/--  **The step `5` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`41 / 48 ≤ σ ≤ 103 / 120` and `T ≥ 2` at most `C(qT)^{(3841 / 2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_5 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 41 / 48 ≤ σ → σ ≤ 103 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((3841 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_5 parHy_5_good hPY

/-- The parameters of the step `6` above `5/6`, on `[103 / 120, 69 / 80]`: the exponent `80021 / 42000`, the
height `y = 46657 / 100000` (`cy = 46607 / 100`), under the pointwise bound. -/
def parHy_6 : ParY where
  M := 1271
  a := 63493 / 100000
  lam := 47621 / 50000
  lo := 103 / 120
  hi := 69 / 80
  Ai := 95263 / 50000
  A := 80021 / 42000
  cy := 46607 / 100

theorem parHy_6_good : parHy_6.Good where
  hM := by simp [parHy_6]
  ha := by simp only [parHy_6]; norm_num
  hat := by simp only [parHy_6, εs]; norm_num
  hlam1 := by simp only [parHy_6, εs]; norm_num
  hlam2 := by simp only [parHy_6, εs]; norm_num
  hlam3 := by simp only [parHy_6]; norm_num
  hlo := by simp only [parHy_6]; norm_num
  hhi := by simp only [parHy_6]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_6, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_6, εs] at *
    nlinarith
  h5 := by simp only [parHy_6, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_6, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_6]; norm_num
  hA16 := by simp only [parHy_6]; norm_num

open scoped Classical in
/--  **The step `6` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`103 / 120 ≤ σ ≤ 69 / 80` and `T ≥ 2` at most `C(qT)^{(80021 / 42000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_6 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 103 / 120 ≤ σ → σ ≤ 69 / 80 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((80021 / 42000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_6 parHy_6_good hPY

/-- The parameters of the step `7` above `5/6`, on `[69 / 80, 13 / 15]`: the exponent `480127 / 254000`, the
height `y = 46121 / 100000` (`cy = 46071 / 100`), under the pointwise bound. -/
def parHy_7 : ParY where
  M := 1261
  a := 62993 / 100000
  lam := 23623 / 25000
  lo := 69 / 80
  hi := 13 / 15
  Ai := 94513 / 50000
  A := 480127 / 254000
  cy := 46071 / 100

theorem parHy_7_good : parHy_7.Good where
  hM := by simp [parHy_7]
  ha := by simp only [parHy_7]; norm_num
  hat := by simp only [parHy_7, εs]; norm_num
  hlam1 := by simp only [parHy_7, εs]; norm_num
  hlam2 := by simp only [parHy_7, εs]; norm_num
  hlam3 := by simp only [parHy_7]; norm_num
  hlo := by simp only [parHy_7]; norm_num
  hhi := by simp only [parHy_7]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_7, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_7, εs] at *
    nlinarith
  h5 := by simp only [parHy_7, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_7, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_7]; norm_num
  hA16 := by simp only [parHy_7]; norm_num

open scoped Classical in
/-- **The step `7` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `69 / 80 ≤ σ ≤ 13 / 15`
and `T ≥ 2` at most `C(qT)^{(480127 / 254000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_7 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 69 / 80 ≤ σ → σ ≤ 13 / 15 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480127 / 254000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_7 parHy_7_good hPY

/-- The parameters of the step `8` above `5/6`, on `[13 / 15, 209 / 240]`: the exponent `3751 / 2000`, the
height `y = 45597 / 100000` (`cy = 45547 / 100`), under the pointwise bound. -/
def parHy_8 : ParY where
  M := 1252
  a := 62501 / 100000
  lam := 46877 / 50000
  lo := 13 / 15
  hi := 209 / 240
  Ai := 187549 / 100000
  A := 3751 / 2000
  cy := 45547 / 100

theorem parHy_8_good : parHy_8.Good where
  hM := by simp [parHy_8]
  ha := by simp only [parHy_8]; norm_num
  hat := by simp only [parHy_8, εs]; norm_num
  hlam1 := by simp only [parHy_8, εs]; norm_num
  hlam2 := by simp only [parHy_8, εs]; norm_num
  hlam3 := by simp only [parHy_8]; norm_num
  hlo := by simp only [parHy_8]; norm_num
  hhi := by simp only [parHy_8]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_8, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_8, εs] at *
    nlinarith
  h5 := by simp only [parHy_8, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_8, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_8]; norm_num
  hA16 := by simp only [parHy_8]; norm_num

open scoped Classical in
/--  **The step `8` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`13 / 15 ≤ σ ≤ 209 / 240` and `T ≥ 2` at most `C(qT)^{(3751 / 2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_8 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 13 / 15 ≤ σ → σ ≤ 209 / 240 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((3751 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_8 parHy_8_good hPY

/-- The parameters of the step `9` above `5/6`, on `[209 / 240, 7 / 8]`: the exponent `160043 / 86000`, the
height `y = 9017 / 20000` (`cy = 9007 / 20`), under the pointwise bound. -/
def parHy_9 : ParY where
  M := 1242
  a := 1938 / 3125
  lam := 186053 / 200000
  lo := 209 / 240
  hi := 7 / 8
  Ai := 11631 / 6250
  A := 160043 / 86000
  cy := 9007 / 20

theorem parHy_9_good : parHy_9.Good where
  hM := by simp [parHy_9]
  ha := by simp only [parHy_9]; norm_num
  hat := by simp only [parHy_9, εs]; norm_num
  hlam1 := by simp only [parHy_9, εs]; norm_num
  hlam2 := by simp only [parHy_9, εs]; norm_num
  hlam3 := by simp only [parHy_9]; norm_num
  hlo := by simp only [parHy_9]; norm_num
  hhi := by simp only [parHy_9]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_9, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_9, εs] at *
    nlinarith
  h5 := by simp only [parHy_9, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_9, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_9]; norm_num
  hA16 := by simp only [parHy_9]; norm_num

open scoped Classical in
/-- **The step `9` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `209 / 240 ≤ σ ≤ 7 / 8`
and `T ≥ 2` at most `C(qT)^{(160043 / 86000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_9 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 209 / 240 ≤ σ → σ ≤ 7 / 8 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((160043 / 86000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_9 parHy_9_good hPY

/-- The parameters of the step `10` above `5/6`, on `[7 / 8, 211 / 240]`: the exponent `48013 / 26000`, the
height `y = 5573 / 12500` (`cy = 22267 / 50`), under the pointwise bound. -/
def parHy_10 : ParY where
  M := 1232
  a := 61539 / 100000
  lam := 92311 / 100000
  lo := 7 / 8
  hi := 211 / 240
  Ai := 36933 / 20000
  A := 48013 / 26000
  cy := 22267 / 50

theorem parHy_10_good : parHy_10.Good where
  hM := by simp [parHy_10]
  ha := by simp only [parHy_10]; norm_num
  hat := by simp only [parHy_10, εs]; norm_num
  hlam1 := by simp only [parHy_10, εs]; norm_num
  hlam2 := by simp only [parHy_10, εs]; norm_num
  hlam3 := by simp only [parHy_10]; norm_num
  hlo := by simp only [parHy_10]; norm_num
  hhi := by simp only [parHy_10]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_10, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_10, εs] at *
    nlinarith
  h5 := by simp only [parHy_10, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_10, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_10]; norm_num
  hA16 := by simp only [parHy_10]; norm_num

open scoped Classical in
/-- **The step `10` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `7 / 8 ≤ σ ≤ 211 / 240`
and `T ≥ 2` at most `C(qT)^{(48013 / 26000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_10 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 7 / 8 ≤ σ → σ ≤ 211 / 240 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((48013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_10 parHy_10_good hPY

/-- The parameters of the step `11` above `5/6`, on `[211 / 240, 53 / 60]`: the exponent `480131 / 262000`, the
height `y = 22047 / 50000` (`cy = 11011 / 25`), under the pointwise bound. -/
def parHy_11 : ParY where
  M := 1223
  a := 61069 / 100000
  lam := 45803 / 50000
  lo := 211 / 240
  hi := 53 / 60
  Ai := 22907 / 12500
  A := 480131 / 262000
  cy := 11011 / 25

theorem parHy_11_good : parHy_11.Good where
  hM := by simp [parHy_11]
  ha := by simp only [parHy_11]; norm_num
  hat := by simp only [parHy_11, εs]; norm_num
  hlam1 := by simp only [parHy_11, εs]; norm_num
  hlam2 := by simp only [parHy_11, εs]; norm_num
  hlam3 := by simp only [parHy_11]; norm_num
  hlo := by simp only [parHy_11]; norm_num
  hhi := by simp only [parHy_11]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_11, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_11, εs] at *
    nlinarith
  h5 := by simp only [parHy_11, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_11, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_11]; norm_num
  hA16 := by simp only [parHy_11]; norm_num

open scoped Classical in
/--  **The step `11` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`211 / 240 ≤ σ ≤ 53 / 60` and `T ≥ 2` at most `C(qT)^{(480131 / 262000)(1−σ)}(log qT)^{10}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_11 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 211 / 240 ≤ σ → σ ≤ 53 / 60 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480131 / 262000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_11 parHy_11_good hPY

/-- The parameters of the step `12` above `5/6`, on `[53 / 60, 71 / 80]`: the exponent `40011 / 22000`, the
height `y = 21807 / 50000` (`cy = 10891 / 25`), under the pointwise bound. -/
def parHy_12 : ParY where
  M := 1214
  a := 60607 / 100000
  lam := 90913 / 100000
  lo := 53 / 60
  hi := 71 / 80
  Ai := 45467 / 25000
  A := 40011 / 22000
  cy := 10891 / 25

theorem parHy_12_good : parHy_12.Good where
  hM := by simp [parHy_12]
  ha := by simp only [parHy_12]; norm_num
  hat := by simp only [parHy_12, εs]; norm_num
  hlam1 := by simp only [parHy_12, εs]; norm_num
  hlam2 := by simp only [parHy_12, εs]; norm_num
  hlam3 := by simp only [parHy_12]; norm_num
  hlo := by simp only [parHy_12]; norm_num
  hhi := by simp only [parHy_12]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_12, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_12, εs] at *
    nlinarith
  h5 := by simp only [parHy_12, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_12, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_12]; norm_num
  hA16 := by simp only [parHy_12]; norm_num

open scoped Classical in
/-- **The step `12` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `53 / 60 ≤ σ ≤ 71 / 80`
and `T ≥ 2` at most `C(qT)^{(40011 / 22000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_12 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 53 / 60 ≤ σ → σ ≤ 71 / 80 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((40011 / 22000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_12 parHy_12_good hPY

/-- The parameters of the step `13` above `5/6`, on `[71 / 80, 107 / 120]`: the exponent `480133 / 266000`, the
height `y = 8629 / 20000` (`cy = 8619 / 20`), under the pointwise bound. -/
def parHy_13 : ParY where
  M := 1205
  a := 60151 / 100000
  lam := 90229 / 100000
  lo := 71 / 80
  hi := 107 / 120
  Ai := 180501 / 100000
  A := 480133 / 266000
  cy := 8619 / 20

theorem parHy_13_good : parHy_13.Good where
  hM := by simp [parHy_13]
  ha := by simp only [parHy_13]; norm_num
  hat := by simp only [parHy_13, εs]; norm_num
  hlam1 := by simp only [parHy_13, εs]; norm_num
  hlam2 := by simp only [parHy_13, εs]; norm_num
  hlam3 := by simp only [parHy_13]; norm_num
  hlo := by simp only [parHy_13]; norm_num
  hhi := by simp only [parHy_13]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_13, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_13, εs] at *
    nlinarith
  h5 := by simp only [parHy_13, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_13, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_13]; norm_num
  hA16 := by simp only [parHy_13]; norm_num

open scoped Classical in
/--  **The step `13` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`71 / 80 ≤ σ ≤ 107 / 120` and `T ≥ 2` at most `C(qT)^{(480133 / 266000)(1−σ)}(log qT)^{10}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_13 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 71 / 80 ≤ σ → σ ≤ 107 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480133 / 266000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_13 parHy_13_good hPY

/-- The parameters of the step `14` above `5/6`, on `[107 / 120, 43 / 48]`: the exponent `240067 / 134000`, the
height `y = 21343 / 50000` (`cy = 10659 / 25`), under the pointwise bound. -/
def parHy_14 : ParY where
  M := 1196
  a := 29851 / 50000
  lam := 179111 / 200000
  lo := 107 / 120
  hi := 43 / 48
  Ai := 89577 / 50000
  A := 240067 / 134000
  cy := 10659 / 25

theorem parHy_14_good : parHy_14.Good where
  hM := by simp [parHy_14]
  ha := by simp only [parHy_14]; norm_num
  hat := by simp only [parHy_14, εs]; norm_num
  hlam1 := by simp only [parHy_14, εs]; norm_num
  hlam2 := by simp only [parHy_14, εs]; norm_num
  hlam3 := by simp only [parHy_14]; norm_num
  hlo := by simp only [parHy_14]; norm_num
  hhi := by simp only [parHy_14]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_14, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_14, εs] at *
    nlinarith
  h5 := by simp only [parHy_14, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_14, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_14]; norm_num
  hA16 := by simp only [parHy_14]; norm_num

open scoped Classical in
/--  **The step `14` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`107 / 120 ≤ σ ≤ 43 / 48` and `T ≥ 2` at most `C(qT)^{(240067 / 134000)(1−σ)}(log qT)^{10}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_14 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 107 / 120 ≤ σ → σ ≤ 43 / 48 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((240067 / 134000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_14 parHy_14_good hPY

/-- The parameters of the step `15` above `5/6`, on `[43 / 48, 9 / 10]`: the exponent `32009 / 18000`, the
height `y = 42237 / 100000` (`cy = 42187 / 100`), under the pointwise bound. -/
def parHy_15 : ParY where
  M := 1187
  a := 2963 / 5000
  lam := 35557 / 40000
  lo := 43 / 48
  hi := 9 / 10
  Ai := 177827 / 100000
  A := 32009 / 18000
  cy := 42187 / 100

theorem parHy_15_good : parHy_15.Good where
  hM := by simp [parHy_15]
  ha := by simp only [parHy_15]; norm_num
  hat := by simp only [parHy_15, εs]; norm_num
  hlam1 := by simp only [parHy_15, εs]; norm_num
  hlam2 := by simp only [parHy_15, εs]; norm_num
  hlam3 := by simp only [parHy_15]; norm_num
  hlo := by simp only [parHy_15]; norm_num
  hhi := by simp only [parHy_15]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_15, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_15, εs] at *
    nlinarith
  h5 := by simp only [parHy_15, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_15, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_15]; norm_num
  hA16 := by simp only [parHy_15]; norm_num

open scoped Classical in
/-- **The step `15` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `43 / 48 ≤ σ ≤ 9 / 10`
and `T ≥ 2` at most `C(qT)^{(32009 / 18000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_15 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 43 / 48 ≤ σ → σ ≤ 9 / 10 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((32009 / 18000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_15 parHy_15_good hPY

/-- The parameters of the step `16` above `5/6`, on `[9 / 10, 217 / 240]`: the exponent `60017 / 34000`, the
height `y = 41797 / 100000` (`cy = 41747 / 100`), under the pointwise bound. -/
def parHy_16 : ParY where
  M := 1178
  a := 7353 / 12500
  lam := 176477 / 200000
  lo := 9 / 10
  hi := 217 / 240
  Ai := 4413 / 2500
  A := 60017 / 34000
  cy := 41747 / 100

theorem parHy_16_good : parHy_16.Good where
  hM := by simp [parHy_16]
  ha := by simp only [parHy_16]; norm_num
  hat := by simp only [parHy_16, εs]; norm_num
  hlam1 := by simp only [parHy_16, εs]; norm_num
  hlam2 := by simp only [parHy_16, εs]; norm_num
  hlam3 := by simp only [parHy_16]; norm_num
  hlo := by simp only [parHy_16]; norm_num
  hhi := by simp only [parHy_16]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_16, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_16, εs] at *
    nlinarith
  h5 := by simp only [parHy_16, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_16, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_16]; norm_num
  hA16 := by simp only [parHy_16]; norm_num

open scoped Classical in
/--  **The step `16` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`9 / 10 ≤ σ ≤ 217 / 240` and `T ≥ 2` at most `C(qT)^{(60017 / 34000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_16 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 9 / 10 ≤ σ → σ ≤ 217 / 240 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((60017 / 34000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_16 parHy_16_good hPY

/-- The parameters of the step `17` above `5/6`, on `[217 / 240, 109 / 120]`: the exponent `480137 / 274000`, the
height `y = 20683 / 50000` (`cy = 10329 / 25`), under the pointwise bound. -/
def parHy_17 : ParY where
  M := 1169
  a := 11679 / 20000
  lam := 17519 / 20000
  lo := 217 / 240
  hi := 109 / 120
  Ai := 5476 / 3125
  A := 480137 / 274000
  cy := 10329 / 25

theorem parHy_17_good : parHy_17.Good where
  hM := by simp [parHy_17]
  ha := by simp only [parHy_17]; norm_num
  hat := by simp only [parHy_17, εs]; norm_num
  hlam1 := by simp only [parHy_17, εs]; norm_num
  hlam2 := by simp only [parHy_17, εs]; norm_num
  hlam3 := by simp only [parHy_17]; norm_num
  hlo := by simp only [parHy_17]; norm_num
  hhi := by simp only [parHy_17]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_17, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_17, εs] at *
    nlinarith
  h5 := by simp only [parHy_17, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_17, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_17]; norm_num
  hA16 := by simp only [parHy_17]; norm_num

open scoped Classical in
/--  **The step `17` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`217 / 240 ≤ σ ≤ 109 / 120` and `T ≥ 2` at most `C(qT)^{(480137 / 274000)(1−σ)}(log qT)^{10}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_17 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 217 / 240 ≤ σ → σ ≤ 109 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480137 / 274000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_17 parHy_17_good hPY

/-- The parameters of the step `18` above `5/6`, on `[109 / 120, 73 / 80]`: the exponent `80023 / 46000`, the
height `y = 2559 / 6250` (`cy = 20447 / 50`), under the pointwise bound. -/
def parHy_18 : ParY where
  M := 1161
  a := 14493 / 25000
  lam := 173921 / 200000
  lo := 109 / 120
  hi := 73 / 80
  Ai := 173963 / 100000
  A := 80023 / 46000
  cy := 20447 / 50

theorem parHy_18_good : parHy_18.Good where
  hM := by simp [parHy_18]
  ha := by simp only [parHy_18]; norm_num
  hat := by simp only [parHy_18, εs]; norm_num
  hlam1 := by simp only [parHy_18, εs]; norm_num
  hlam2 := by simp only [parHy_18, εs]; norm_num
  hlam3 := by simp only [parHy_18]; norm_num
  hlo := by simp only [parHy_18]; norm_num
  hhi := by simp only [parHy_18]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_18, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_18, εs] at *
    nlinarith
  h5 := by simp only [parHy_18, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_18, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_18]; norm_num
  hA16 := by simp only [parHy_18]; norm_num

open scoped Classical in
/--  **The step `18` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`109 / 120 ≤ σ ≤ 73 / 80` and `T ≥ 2` at most `C(qT)^{(80023 / 46000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero
of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_18 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 109 / 120 ≤ σ → σ ≤ 73 / 80 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((80023 / 46000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_18 parHy_18_good hPY

/-- The parameters of the step `19` above `5/6`, on `[73 / 80, 11 / 12]`: the exponent `480139 / 278000`, the
height `y = 40531 / 100000` (`cy = 40481 / 100`), under the pointwise bound. -/
def parHy_19 : ParY where
  M := 1153
  a := 11511 / 20000
  lam := 17267 / 20000
  lo := 73 / 80
  hi := 11 / 12
  Ai := 172711 / 100000
  A := 480139 / 278000
  cy := 40481 / 100

theorem parHy_19_good : parHy_19.Good where
  hM := by simp [parHy_19]
  ha := by simp only [parHy_19]; norm_num
  hat := by simp only [parHy_19, εs]; norm_num
  hlam1 := by simp only [parHy_19, εs]; norm_num
  hlam2 := by simp only [parHy_19, εs]; norm_num
  hlam3 := by simp only [parHy_19]; norm_num
  hlo := by simp only [parHy_19]; norm_num
  hhi := by simp only [parHy_19]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHy_19, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHy_19, εs] at *
    nlinarith
  h5 := by simp only [parHy_19, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parHy_19, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHy_19]; norm_num
  hA16 := by simp only [parHy_19]; norm_num

open scoped Classical in
/-- **The step `19` above `5/6`, under `PYWeyl`**: there is `C ≥ 0` such that for every `q ≥ 1`, `73 / 80 ≤ σ ≤ 11 / 12`
and `T ≥ 2` at most `C(qT)^{(480139 / 278000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hy_19 (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 73 / 80 ≤ σ → σ ≤ 11 / 12 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_genY parHy_19 parHy_19_good hPY

/-! ### Above `11/12` -/

open scoped Classical in
/-- **Above `11/12` the count is at most `1`**: by the zero-free half-plane `Re s > 11/12`
(`LinnikLindelof.LFunction_ne_zero`), only the trivial character can be counted. -/
theorem card_le_one_of_gt {q : ℕ} [NeZero q] {σ T : ℝ} (hσ : 11 / 12 < σ) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ 1 := by
  have hsub : (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) ⊆ {1} := by
    intro χ hχ
    rw [Finset.mem_singleton]
    by_contra h1
    obtain ⟨-, s, hs, -, hz⟩ := Finset.mem_filter.1 hχ
    exact LinnikLindelof.LFunction_ne_zero h1 (by linarith) hz
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_singleton _).le

open scoped Classical in
/--  **The last step, extended to `σ ≤ 1`, under `PYWeyl`**: the exponent `480139 / 278000` on `[73 / 80, 1]`; above
`11/12` the count is at most `1` (`card_le_one_of_gt`), and `1 ≤ 2^{10}(qT)^{E}(log qT)^{10}` since `log qT ≥ 1/2`. -/
theorem charDensity_hy_top (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 73 / 80 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := charDensity_hy_19 hPY
  refine ⟨C + 2 ^ 10, by positivity, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * T) := Real.log_le_log (by norm_num) hqT
  have hℓ : 1 / 2 ≤ Real.log ((q : ℝ) * T) := by have := Real.log_two_gt_d9; linarith
  have hE0 : 0 ≤ (480139 / 278000) * (1 - σ) := by nlinarith
  have hP1 : 1 ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) := Real.one_le_rpow (by linarith) hE0
  have hℓ10 : 1 ≤ 2 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hℓ (by norm_num : (0 : ℝ) ≤ 10)
    have h2 : (2 : ℝ) ^ 10 * (1 / 2 : ℝ) ^ (10 : ℝ) = 1 := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    nlinarith
  have hP : 0 ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by positivity
  have h1 : 1 ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * (2 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hP1 hℓ10
  rcases le_or_gt σ (11 / 12) with hle | hgt
  · calc _ ≤ C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
          hC q σ T hσ hle hT
      _ ≤ (C + 2 ^ 10) * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
          nlinarith
  · have hrest : 0 ≤ C * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
      positivity
    calc _ ≤ (1 : ℝ) := card_le_one_of_gt hgt
      _ ≤ ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * (2 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ)) := h1
      _ ≤ (C + 2 ^ 10) * ((q : ℝ) * T) ^ ((480139 / 278000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
          linarith

end LinnikStairs7

#print axioms LinnikStairs7.charDensity_in7_0
#print axioms LinnikStairs7.charDensity_hx7_0
#print axioms LinnikStairs7.charDensity_hy_0
#print axioms LinnikStairs7.charDensity_hy_top
