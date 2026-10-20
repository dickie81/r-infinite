/-
# Round 609: the staircases of the stack's density arguments (Ingham below `3/4`, Huxley's step on `[3/4, 5/6]`)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Twenty density estimates, each an instance of a parametric argument of the stack, that together lie just above the
curve `min(3/(2 − σ), 3/(3σ − 1))` on `[1 − 1/A_U, 5/6]`, `A_U = 12/5 + 1/2000`:

* `charDensity_in0` … `charDensity_in9`: `LinnikInghamC.charDensity_ingham_c` at `ε = 1/8000` and
  `c = (3/(2 − σ₂) − 2)/4` on the ten equal steps `[σ₁, σ₂]` from `1 − 1/A_U` to `3/4`: the exponent
  `3/(2 − σ₂) + 1/2000`, Ingham's curve at the step's right end plus `1/2000`.
* `parHx0` … `parHx9`, `charDensity_hx0` … `charDensity_hx9`: `LinnikHuxStep.charDensity_gen` at parameters found
  by a linear program (scratch) for the ten equal steps from `3/4` to `5/6`: the exponent `3/(3σ₁ − 1) + 1/2000`,
  Huxley's curve at the step's left end plus `1/2000`.

The file imports `LinnikInghamC.lean` and `LinnikHuxStep.lean`.
-/
import LinnikInghamC
import LinnikHuxStep

open Complex Real Finset

noncomputable section

namespace LinnikStairs

open DirichletCharacter LinnikHuxStep

/-! ### Ingham's steps below `3/4` -/

open scoped Classical in
/--  **Ingham's step `0`**: the exponent `1152508841 / 537682000` on `[2801 / 4801, 115239 / 192040]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 115239 / 192040`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 19219 / 537682`, `δ₀ = 801 / 9602`. -/
theorem charDensity_in0 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 2801 / 4801 ≤ σ → σ ≤ 115239 / 192040 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((1152508841 / 537682000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 19219 / 537682)
    (δ₀ := 801 / 9602) (σ₂ := 115239 / 192040)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (19219 / 537682 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (1152508841 / 537682000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `1`**: the exponent `576252821 / 265642000` on `[115239 / 192040, 59219 / 96020]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 59219 / 96020`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 11209 / 265642`, `δ₀ = 19219 / 192040`. -/
theorem charDensity_in1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 115239 / 192040 ≤ σ → σ ≤ 59219 / 96020 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((576252821 / 265642000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 11209 / 265642)
    (δ₀ := 19219 / 192040) (σ₂ := 59219 / 96020)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (11209 / 265642 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (576252821 / 265642000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `2`**: the exponent `384167481 / 174962000` on `[59219 / 96020, 121637 / 192040]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 121637 / 192040`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 8539 / 174962`, `δ₀ = 11209 / 96020`. -/
theorem charDensity_in2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 59219 / 96020 ≤ σ → σ ≤ 121637 / 192040 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((384167481 / 174962000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 8539 / 174962)
    (δ₀ := 11209 / 96020) (σ₂ := 121637 / 192040)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (8539 / 174962 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (384167481 / 174962000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `3`**: the exponent `288124811 / 129622000` on `[121637 / 192040, 31209 / 48010]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 31209 / 48010`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 3602 / 64811`, `δ₀ = 25617 / 192040`. -/
theorem charDensity_in3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 121637 / 192040 ≤ σ → σ ≤ 31209 / 48010 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((288124811 / 129622000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 3602 / 64811)
    (δ₀ := 25617 / 192040) (σ₂ := 31209 / 48010)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (3602 / 64811 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (288124811 / 129622000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `4`**: the exponent `230499209 / 102418000` on `[31209 / 48010, 25607 / 38408]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 25607 / 38408`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 6403 / 102418`, `δ₀ = 3602 / 24005`. -/
theorem charDensity_in4 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 31209 / 48010 ≤ σ → σ ≤ 25607 / 38408 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((230499209 / 102418000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 6403 / 102418)
    (δ₀ := 3602 / 24005) (σ₂ := 25607 / 38408)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (6403 / 102418 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (230499209 / 102418000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `5`**: the exponent `192082141 / 84282000` on `[25607 / 38408, 65617 / 96020]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 65617 / 96020`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 5869 / 84282`, `δ₀ = 6403 / 38408`. -/
theorem charDensity_in5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 25607 / 38408 ≤ σ → σ ≤ 65617 / 96020 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((192082141 / 84282000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 5869 / 84282)
    (δ₀ := 6403 / 38408) (σ₂ := 65617 / 96020)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (5869 / 84282 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (192082141 / 84282000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `6`**: the exponent `1152489647 / 499294000` on `[65617 / 96020, 134433 / 192040]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 134433 / 192040`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 38413 / 499294`, `δ₀ = 17607 / 96020`. -/
theorem charDensity_in6 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 65617 / 96020 ≤ σ → σ ≤ 134433 / 192040 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((1152489647 / 499294000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 38413 / 499294)
    (δ₀ := 17607 / 96020) (σ₂ := 134433 / 192040)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (38413 / 499294 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (1152489647 / 499294000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `7`**: the exponent `72030403 / 30806000` on `[134433 / 192040, 17204 / 24005]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 17204 / 24005`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 10403 / 123224`, `δ₀ = 38413 / 192040`. -/
theorem charDensity_in7 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 134433 / 192040 ≤ σ → σ ≤ 17204 / 24005 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((72030403 / 30806000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 10403 / 123224)
    (δ₀ := 38413 / 192040) (σ₂ := 17204 / 24005)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (10403 / 123224 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (72030403 / 30806000) * (1 - σ) by ring] at this

open scoped Classical in
/--  **Ingham's step `8`**: the exponent `384161083 / 162166000` on `[17204 / 24005, 140831 / 192040]`
(`3/(2 − σ₂) + 1/2000` at the right end `σ₂ = 140831 / 192040`): `charDensity_ingham_c` at `ε = 1/8000`,
`c = 14937 / 162166`, `δ₀ = 10403 / 48010`. -/
theorem charDensity_in8 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 17204 / 24005 ≤ σ → σ ≤ 140831 / 192040 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((384161083 / 162166000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 14937 / 162166)
    (δ₀ := 10403 / 48010) (σ₂ := 140831 / 192040)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (14937 / 162166 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (384161083 / 162166000) * (1 - σ) by ring] at this

open scoped Classical in
/-- **Ingham's step `9`**: the exponent `4801 / 2000` on `[140831 / 192040, 3 / 4]` (`3/(2 − σ₂) + 1/2000` at the
right end `σ₂ = 3 / 4`): `charDensity_ingham_c` at `ε = 1/8000`, `c = 1 / 10`, `δ₀ = 44811 / 192040`. -/
theorem charDensity_in9 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 140831 / 192040 ≤ σ → σ ≤ 3 / 4 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((4801 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 8000) (c := 1 / 10)
    (δ₀ := 44811 / 192040) (σ₂ := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 10 : ℝ) + 4 * (1 / 8000)) * (1 - σ) =
      (4801 / 2000) * (1 - σ) by ring] at this

/-! ### Huxley's steps on `[3/4, 5/6]` -/

/-- The parameters of Huxley's step `0`: the exponent `4801 / 2000` on `[3 / 4, 91 / 120]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx0 : Par where
  M := 1601
  a := 15999 / 20000
  lam := 23999 / 20000
  lo := 3 / 4
  hi := 91 / 120
  Ai := 60007 / 25000
  A := 4801 / 2000

theorem parHx0_good : parHx0.Good where
  hM := by simp [parHx0]
  ha := by simp only [parHx0]; norm_num
  hat := by simp only [parHx0, εs]; norm_num
  hlam1 := by simp only [parHx0, εs]; norm_num
  hlam2 := by simp only [parHx0, εs]; norm_num
  hlam3 := by simp only [parHx0]; norm_num
  hlo := by simp only [parHx0]; norm_num
  hhi := by simp only [parHx0]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx0, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx0, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx0, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx0, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx0]; norm_num
  hA16 := by simp only [parHx0]; norm_num

open scoped Classical in
/-- **Huxley's step `0`**: there is `C ≥ 0` such that for every `q ≥ 1`, `3 / 4 ≤ σ ≤ 91 / 120` and `T ≥ 2` at most
`C(qT)^{(4801 / 2000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx0 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 3 / 4 ≤ σ → σ ≤ 91 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((4801 / 2000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx0 parHx0_good

/-- The parameters of Huxley's step `1`: the exponent `80017 / 34000` on `[91 / 120, 23 / 30]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx1 : Par where
  M := 1570
  a := 39213 / 50000
  lam := 235283 / 200000
  lo := 91 / 120
  hi := 23 / 30
  Ai := 235323 / 100000
  A := 80017 / 34000

theorem parHx1_good : parHx1.Good where
  hM := by simp [parHx1]
  ha := by simp only [parHx1]; norm_num
  hat := by simp only [parHx1, εs]; norm_num
  hlam1 := by simp only [parHx1, εs]; norm_num
  hlam2 := by simp only [parHx1, εs]; norm_num
  hlam3 := by simp only [parHx1]; norm_num
  hlo := by simp only [parHx1]; norm_num
  hhi := by simp only [parHx1]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx1, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx1, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx1, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx1, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx1]; norm_num
  hA16 := by simp only [parHx1]; norm_num

open scoped Classical in
/-- **Huxley's step `1`**: there is `C ≥ 0` such that for every `q ≥ 1`, `91 / 120 ≤ σ ≤ 23 / 30` and `T ≥ 2` at most
`C(qT)^{(80017 / 34000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 91 / 120 ≤ σ → σ ≤ 23 / 30 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((80017 / 34000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx1 parHx1_good

/-- The parameters of Huxley's step `2`: the exponent `60013 / 26000` on `[23 / 30, 31 / 40]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx2 : Par where
  M := 1540
  a := 38459 / 50000
  lam := 230759 / 200000
  lo := 23 / 30
  hi := 31 / 40
  Ai := 230799 / 100000
  A := 60013 / 26000

theorem parHx2_good : parHx2.Good where
  hM := by simp [parHx2]
  ha := by simp only [parHx2]; norm_num
  hat := by simp only [parHx2, εs]; norm_num
  hlam1 := by simp only [parHx2, εs]; norm_num
  hlam2 := by simp only [parHx2, εs]; norm_num
  hlam3 := by simp only [parHx2]; norm_num
  hlo := by simp only [parHx2]; norm_num
  hhi := by simp only [parHx2]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx2, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx2, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx2, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx2, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx2]; norm_num
  hA16 := by simp only [parHx2]; norm_num

open scoped Classical in
/-- **Huxley's step `2`**: there is `C ≥ 0` such that for every `q ≥ 1`, `23 / 30 ≤ σ ≤ 31 / 40` and `T ≥ 2` at most
`C(qT)^{(60013 / 26000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx2 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 23 / 30 ≤ σ → σ ≤ 31 / 40 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((60013 / 26000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx2 parHx2_good

/-- The parameters of Huxley's step `3`: the exponent `240053 / 106000` on `[31 / 40, 47 / 60]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx3 : Par where
  M := 1511
  a := 75467 / 100000
  lam := 113203 / 100000
  lo := 31 / 40
  hi := 47 / 60
  Ai := 45289 / 20000
  A := 240053 / 106000

theorem parHx3_good : parHx3.Good where
  hM := by simp [parHx3]
  ha := by simp only [parHx3]; norm_num
  hat := by simp only [parHx3, εs]; norm_num
  hlam1 := by simp only [parHx3, εs]; norm_num
  hlam2 := by simp only [parHx3, εs]; norm_num
  hlam3 := by simp only [parHx3]; norm_num
  hlo := by simp only [parHx3]; norm_num
  hhi := by simp only [parHx3]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx3, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx3, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx3, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx3, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx3]; norm_num
  hA16 := by simp only [parHx3]; norm_num

open scoped Classical in
/--  **Huxley's step `3`**: there is `C ≥ 0` such that for every `q ≥ 1`, `31 / 40 ≤ σ ≤ 47 / 60` and `T ≥ 2` at most
`C(qT)^{(240053 / 106000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 31 / 40 ≤ σ → σ ≤ 47 / 60 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((240053 / 106000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx3 parHx3_good

/-- The parameters of Huxley's step `4`: the exponent `40009 / 18000` on `[47 / 60, 19 / 24]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx4 : Par where
  M := 1483
  a := 74069 / 100000
  lam := 55553 / 50000
  lo := 47 / 60
  hi := 19 / 24
  Ai := 44451 / 20000
  A := 40009 / 18000

theorem parHx4_good : parHx4.Good where
  hM := by simp [parHx4]
  ha := by simp only [parHx4]; norm_num
  hat := by simp only [parHx4, εs]; norm_num
  hlam1 := by simp only [parHx4, εs]; norm_num
  hlam2 := by simp only [parHx4, εs]; norm_num
  hlam3 := by simp only [parHx4]; norm_num
  hlo := by simp only [parHx4]; norm_num
  hhi := by simp only [parHx4]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx4, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx4, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx4, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx4, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx4]; norm_num
  hA16 := by simp only [parHx4]; norm_num

open scoped Classical in
/-- **Huxley's step `4`**: there is `C ≥ 0` such that for every `q ≥ 1`, `47 / 60 ≤ σ ≤ 19 / 24` and `T ≥ 2` at most
`C(qT)^{(40009 / 18000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx4 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 47 / 60 ≤ σ → σ ≤ 19 / 24 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((40009 / 18000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx4 parHx4_good

/-- The parameters of Huxley's step `5`: the exponent `48011 / 22000` on `[19 / 24, 4 / 5]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx5 : Par where
  M := 1456
  a := 36361 / 50000
  lam := 218171 / 200000
  lo := 19 / 24
  hi := 4 / 5
  Ai := 109109 / 50000
  A := 48011 / 22000

theorem parHx5_good : parHx5.Good where
  hM := by simp [parHx5]
  ha := by simp only [parHx5]; norm_num
  hat := by simp only [parHx5, εs]; norm_num
  hlam1 := by simp only [parHx5, εs]; norm_num
  hlam2 := by simp only [parHx5, εs]; norm_num
  hlam3 := by simp only [parHx5]; norm_num
  hlo := by simp only [parHx5]; norm_num
  hhi := by simp only [parHx5]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx5, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx5, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx5, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx5, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx5]; norm_num
  hA16 := by simp only [parHx5]; norm_num

open scoped Classical in
/-- **Huxley's step `5`**: there is `C ≥ 0` such that for every `q ≥ 1`, `19 / 24 ≤ σ ≤ 4 / 5` and `T ≥ 2` at most
`C(qT)^{(48011 / 22000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx5 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 19 / 24 ≤ σ → σ ≤ 4 / 5 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((48011 / 22000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx5 parHx5_good

/-- The parameters of Huxley's step `6`: the exponent `30007 / 14000` on `[4 / 5, 97 / 120]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx6 : Par where
  M := 1430
  a := 2232 / 3125
  lam := 214277 / 200000
  lo := 4 / 5
  hi := 97 / 120
  Ai := 214321 / 100000
  A := 30007 / 14000

theorem parHx6_good : parHx6.Good where
  hM := by simp [parHx6]
  ha := by simp only [parHx6]; norm_num
  hat := by simp only [parHx6, εs]; norm_num
  hlam1 := by simp only [parHx6, εs]; norm_num
  hlam2 := by simp only [parHx6, εs]; norm_num
  hlam3 := by simp only [parHx6]; norm_num
  hlo := by simp only [parHx6]; norm_num
  hhi := by simp only [parHx6]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx6, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx6, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx6, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx6, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx6]; norm_num
  hA16 := by simp only [parHx6]; norm_num

open scoped Classical in
/-- **Huxley's step `6`**: there is `C ≥ 0` such that for every `q ≥ 1`, `4 / 5 ≤ σ ≤ 97 / 120` and `T ≥ 2` at most
`C(qT)^{(30007 / 14000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx6 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 4 / 5 ≤ σ → σ ≤ 97 / 120 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((30007 / 14000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx6 parHx6_good

/-- The parameters of Huxley's step `7`: the exponent `80019 / 38000` on `[97 / 120, 49 / 60]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx7 : Par where
  M := 1405
  a := 70171 / 100000
  lam := 105259 / 100000
  lo := 97 / 120
  hi := 49 / 60
  Ai := 210563 / 100000
  A := 80019 / 38000

theorem parHx7_good : parHx7.Good where
  hM := by simp [parHx7]
  ha := by simp only [parHx7]; norm_num
  hat := by simp only [parHx7, εs]; norm_num
  hlam1 := by simp only [parHx7, εs]; norm_num
  hlam2 := by simp only [parHx7, εs]; norm_num
  hlam3 := by simp only [parHx7]; norm_num
  hlo := by simp only [parHx7]; norm_num
  hhi := by simp only [parHx7]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx7, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx7, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx7, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx7, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx7]; norm_num
  hA16 := by simp only [parHx7]; norm_num

open scoped Classical in
/-- **Huxley's step `7`**: there is `C ≥ 0` such that for every `q ≥ 1`, `97 / 120 ≤ σ ≤ 49 / 60` and `T ≥ 2` at most
`C(qT)^{(80019 / 38000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx7 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 97 / 120 ≤ σ → σ ≤ 49 / 60 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((80019 / 38000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx7 parHx7_good

/-- The parameters of Huxley's step `8`: the exponent `120029 / 58000` on `[49 / 60, 33 / 40]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx8 : Par where
  M := 1381
  a := 34481 / 50000
  lam := 206891 / 200000
  lo := 49 / 60
  hi := 33 / 40
  Ai := 51733 / 25000
  A := 120029 / 58000

theorem parHx8_good : parHx8.Good where
  hM := by simp [parHx8]
  ha := by simp only [parHx8]; norm_num
  hat := by simp only [parHx8, εs]; norm_num
  hlam1 := by simp only [parHx8, εs]; norm_num
  hlam2 := by simp only [parHx8, εs]; norm_num
  hlam3 := by simp only [parHx8]; norm_num
  hlo := by simp only [parHx8]; norm_num
  hhi := by simp only [parHx8]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx8, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx8, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx8, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx8, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx8]; norm_num
  hA16 := by simp only [parHx8]; norm_num

open scoped Classical in
/-- **Huxley's step `8`**: there is `C ≥ 0` such that for every `q ≥ 1`, `49 / 60 ≤ σ ≤ 33 / 40` and `T ≥ 2` at most
`C(qT)^{(120029 / 58000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. -/
theorem charDensity_hx8 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 49 / 60 ≤ σ → σ ≤ 33 / 40 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((120029 / 58000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx8 parHx8_good

/-- The parameters of Huxley's step `9`: the exponent `240059 / 118000` on `[33 / 40, 5 / 6]` (`3/(3σ₁ − 1) + 1/2000`
at the left end). -/
def parHx9 : Par where
  M := 1357
  a := 67793 / 100000
  lam := 25423 / 25000
  lo := 33 / 40
  hi := 5 / 6
  Ai := 50857 / 25000
  A := 240059 / 118000

theorem parHx9_good : parHx9.Good where
  hM := by simp [parHx9]
  ha := by simp only [parHx9]; norm_num
  hat := by simp only [parHx9, εs]; norm_num
  hlam1 := by simp only [parHx9, εs]; norm_num
  hlam2 := by simp only [parHx9, εs]; norm_num
  hlam3 := by simp only [parHx9]; norm_num
  hlo := by simp only [parHx9]; norm_num
  hhi := by simp only [parHx9]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parHx9, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parHx9, εs] at *
    nlinarith
  h3 := by
    intro σ h1 h2
    simp only [parHx9, εs] at *
    nlinarith
  h4 := by
    intro σ h2
    simp only [parHx9, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parHx9]; norm_num
  hA16 := by simp only [parHx9]; norm_num

open scoped Classical in
/--  **Huxley's step `9`**: there is `C ≥ 0` such that for every `q ≥ 1`, `33 / 40 ≤ σ ≤ 5 / 6` and `T ≥ 2` at most
`C(qT)^{(240059 / 118000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`.
-/
theorem charDensity_hx9 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 33 / 40 ≤ σ → σ ≤ 5 / 6 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((240059 / 118000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHx9 parHx9_good

end LinnikStairs

#print axioms LinnikStairs.charDensity_in0
#print axioms LinnikStairs.charDensity_hx0
#print axioms LinnikStairs.charDensity_hx9
