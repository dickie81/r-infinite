import DoorUnif
import LeastNonresidue

/-! # Stack review 3, door D3: a prime with `χ(p) ≠ 1` below `C_A(log(q + 2))^A`, every character `χ ≠ 1`

Round 482's Ankeny argument (`LeastNonresidue.rpow_le_of_forall_eq_of`) uses `IsQuadratic` only to pass round 480's
uniform bound through: its lower bound `re_psiChi_ge` holds for every character. With the every-character uniform
bound (`DoorUnif.lean`), at `ε = 1`: every Dirichlet character `χ ≠ 1` mod `q` has a prime `p ∤ q` with `χ(p) ≠ 1`
and `p ≤ C_A(log(q + 2))^A`, for every `A > 12`.

Not compiled by any build script. It imports `DoorUnif`: compile that to an olean first, from a built Mathlib checkout,
`LEAN_PATH="$(lake env printenv LEAN_PATH):<pilot>/build:<dir>" lean -R <dir> -o <dir>/DoorUnif.olean <dir>/DoorUnif.lean`
with `<dir>` a copy of `review/stack3`, then this file with the same `LEAN_PATH` and `-R <dir>` (12 s at round 508's
head; both printed axiom lists are `[propext, Classical.choice, Quot.sound]`). -/

open Real Filter Asymptotics ChiPNT

namespace StackReview3

open LeastNonresidue

theorem rpow_le_of_forall_eq_all {A C₁ : ℝ} (hA : 12 < A)
    (hψ : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ x : ℝ, 1 < x → ‖psiChi χ x‖ ≤ C₁ * Real.log (N + 2) * x ^ (11 / 12 + (1 / 12 - 1 / A))) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) → ∀ x : ℝ, 100 ≤ x →
        (∀ p : ℕ, p.Prime → p ≤ ⌊x⌋₊ → ¬ p ∣ q → χ p = ε) →
          x ^ (1 / A) ≤ 4 * (C₁ + 11) * Real.log (q + 2) := by
  have hA0 : 0 < A := by linarith
  have hiA : 1 / A < 1 / 12 := by
    rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  have hiA0 : 0 < 1 / A := by positivity
  set η : ℝ := 1 / 12 - 1 / A with hηdef
  have hη : 0 < η := by linarith
  intro q _ χ hχ ε hε x hx hall
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set L : ℝ := Real.log (q + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    linarith
  set e : ℝ := 11 / 12 + η with hedef
  have he : e = 1 - 1 / A := by rw [hedef, hηdef]; ring
  have hxe : 1 ≤ x ^ e := Real.one_le_rpow hx1 (by rw [he]; linarith)
  -- the upper bound
  have hup : ε * (psiChi χ x).re ≤ C₁ * L * x ^ e := by
    have h1 : ε * (psiChi χ x).re ≤ ‖psiChi χ x‖ := by
      calc ε * (psiChi χ x).re ≤ |ε * (psiChi χ x).re| := le_abs_self _
        _ = |(psiChi χ x).re| := by
            rw [abs_mul]; rcases hε with rfl | rfl <;> norm_num
        _ ≤ ‖psiChi χ x‖ := Complex.abs_re_le_norm _
    exact h1.trans (hψ q χ hχ x (by linarith))
  -- the lower bound
  have hlow := re_psiChi_ge χ hε hx1 hall
  have hψx := psi_ge_quarter hx
  -- `√x log x ≤ (12/5)x^e`
  have hsqrt : √x * Real.log x ≤ 12 / 5 * x ^ e := by
    have h1 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 5 / 12)
    have h2 : √x * (x ^ (5 / 12 : ℝ) / (5 / 12)) = 12 / 5 * x ^ (11 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc', mul_comm, ← Real.rpow_add hx0]
      ring_nf
    have h3 : x ^ (11 / 12 : ℝ) ≤ x ^ e :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hedef]; linarith)
    calc √x * Real.log x ≤ √x * (x ^ (5 / 12 : ℝ) / (5 / 12)) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = 12 / 5 * x ^ (11 / 12 : ℝ) := h2
      _ ≤ 12 / 5 * x ^ e := by gcongr
  have hlogq : Real.log q ≤ L * x ^ e := by
    have h1 : Real.log q ≤ L := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exact absurd h0 (NeZero.ne q)
      · exact Real.log_le_log (by exact_mod_cast h0) (by linarith)
    exact h1.trans (le_mul_of_one_le_right (by linarith) hxe)
  -- assemble: `x/4 ≤ (C₁ + 11)·L·x^e`
  have hmain : x / 4 ≤ (C₁ + 11) * L * x ^ e := by
    have h1 : 12 / 5 * x ^ e ≤ 12 / 5 * (L * x ^ e) := by
      have := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ x ^ e) hL
      linarith
    have h2 : (C₁ + 11) * L * x ^ e = C₁ * L * x ^ e + 11 * (L * x ^ e) := by ring
    have h3 : 0 ≤ L * x ^ e := by positivity
    nlinarith
  have hsplit : x = x ^ (1 / A) * x ^ e := by
    rw [← Real.rpow_add hx0, he, show 1 / A + (1 - 1 / A) = (1 : ℝ) by ring, Real.rpow_one]
  have hxe0 : 0 < x ^ e := by positivity
  have h5 : x ^ (1 / A) * x ^ e ≤ (4 * (C₁ + 11) * L) * x ^ e := by
    rw [← hsplit]; linarith
  exact le_of_mul_le_mul_right h5 hxe0

/-- **A prime with `χ(p) ≠ 1` below `C_A(log(q + 2))^A`, for every Dirichlet character `χ ≠ 1`.** -/
theorem exists_prime_ne_one {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∃ p : ℕ, p.Prime ∧ ¬ p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ C * Real.log (q + 2) ^ A := by
  have hA0 : 0 < A := by linarith
  obtain ⟨C₁, hC₁, hψ⟩ := ChiUniformAll.psiChi_le_uniform (η := 1 / 12 - 1 / A)
    (by rw [sub_pos, div_lt_div_iff₀ hA0 (by norm_num)]; linarith)
  set K : ℝ := 4 * (C₁ + 11) with hKdef
  have hK : 0 < K := by positivity
  refine ⟨101 + K ^ A, by positivity, fun q _ χ hχ ↦ ?_⟩
  set L : ℝ := Real.log (q + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
    linarith
  have hLA : 1 ≤ L ^ A := Real.one_le_rpow hL hA0.le
  set X : ℝ := max 100 ((K * L) ^ A) + 1 with hXdef
  have hX100 : 100 ≤ X := by
    have := le_max_left (100 : ℝ) ((K * L) ^ A); linarith
  have hXC : X ≤ (101 + K ^ A) * L ^ A := by
    have h1 : max 100 ((K * L) ^ A) ≤ 100 + K ^ A * L ^ A := by
      rw [Real.mul_rpow hK.le (by linarith)]
      have : 0 ≤ K ^ A * L ^ A := by positivity
      exact max_le (by linarith) (by linarith)
    have h2 : 101 + K ^ A * L ^ A ≤ (101 + K ^ A) * L ^ A := by nlinarith
    linarith
  by_contra hcon
  push Not at hcon
  have hall : ∀ p : ℕ, p.Prime → p ≤ ⌊X⌋₊ → ¬ p ∣ q → χ p = ((1 : ℝ) : ℂ) := by
    intro p hp hpX hpq
    have hpX' : (p : ℝ) ≤ X := by
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ X)
      have h' : (p : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hpX
      linarith
    by_contra hne
    exact (hcon p hp hpq (by simpa using hne)).not_ge (hpX'.trans hXC)
  have hb := rpow_le_of_forall_eq_all hA hψ q χ hχ (Or.inl rfl) X hX100 hall
  have hgt : K * L < X ^ (1 / A) := by
    have h1 : (K * L) ^ A < X := by
      have := le_max_right (100 : ℝ) ((K * L) ^ A); linarith
    have h2 : ((K * L) ^ A) ^ (1 / A) = K * L := by
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hA0.ne', Real.rpow_one]
    rw [← h2]
    exact Real.rpow_lt_rpow (by positivity) h1 (by positivity)
  linarith

end StackReview3

#print axioms StackReview3.rpow_le_of_forall_eq_all
#print axioms StackReview3.exists_prime_ne_one
