import Mathlib

/-! # The mean square of the divisor function (round 235)

`sum_card_divisors_sq_le`: `Σ_{j≤M} d(j)² ≤ M(1 + log M)³`. The proof counts pairs of divisors:
`Σ_j d(j)² = Σ_{a,b≤M} #{j ≤ M : lcm(a,b) | j} ≤ M Σ_{a,b} gcd(a,b)/(ab)`, and
`gcd(a,b) ≤ Σ_{g|a, g|b} g` gives `Σ_{a,b} gcd(a,b)/(ab) ≤ Σ_g g(Σ_{g|a} 1/a)² ≤ Σ_g (1 + log M)²/g`.
-/

open Real Finset

noncomputable section

namespace DivSq

theorem harmonic_le (M : ℕ) : ∑ h ∈ Ioc 0 M, (1 : ℝ) / h ≤ 1 + Real.log M := by
  have := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  have e : Ioc 0 M = Icc 1 M := by ext x; simp [Nat.lt_iff_add_one_le]
  rw [e]; simpa [one_div] using this

/-- `Σ_{a≤M, g|a} 1/a ≤ (1 + log M)/g`. -/
theorem sum_multiples_inv_le {M g : ℕ} (hg : 0 < g) :
    ∑ a ∈ (Ioc 0 M).filter (g ∣ ·), (1 : ℝ) / a ≤ (1 + Real.log M) / g := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have e : ∑ a ∈ (Ioc 0 M).filter (g ∣ ·), (1 : ℝ) / a
      = (1 / g) * ∑ a ∈ (Ioc 0 M).filter (g ∣ ·), (1 : ℝ) / ((a / g : ℕ) : ℝ) := by
    rw [mul_sum]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨k, rfl⟩ := (mem_filter.1 ha).2
    rw [Nat.mul_div_cancel_left k hg]
    push_cast
    field_simp
  rw [e]
  have hinj : ∀ x ∈ (Ioc 0 M).filter (g ∣ ·), ∀ y ∈ (Ioc 0 M).filter (g ∣ ·), x / g = y / g → x = y := by
    intro x hx y hy hxy
    obtain ⟨k, rfl⟩ := (mem_filter.1 hx).2
    obtain ⟨l, rfl⟩ := (mem_filter.1 hy).2
    rw [Nat.mul_div_cancel_left k hg, Nat.mul_div_cancel_left l hg] at hxy
    rw [hxy]
  have himg : ((Ioc 0 M).filter (g ∣ ·)).image (· / g) ⊆ Ioc 0 M := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hh
    obtain ⟨hx1, k, rfl⟩ := mem_filter.1 hx
    obtain ⟨hx2, hx3⟩ := mem_Ioc.1 hx1
    rw [Nat.mul_div_cancel_left k hg]
    refine mem_Ioc.2 ⟨Nat.pos_of_ne_zero fun h0 => by simp [h0] at hx2, ?_⟩
    calc k ≤ g * k := Nat.le_mul_of_pos_left k hg
      _ ≤ M := hx3
  have h2 : ∑ a ∈ (Ioc 0 M).filter (g ∣ ·), (1 : ℝ) / ((a / g : ℕ) : ℝ) ≤ 1 + Real.log M := by
    rw [← sum_image (f := fun h : ℕ => (1 : ℝ) / h) hinj]
    exact (sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity).trans (harmonic_le M)
  calc 1 / (g : ℝ) * ∑ a ∈ (Ioc 0 M).filter (g ∣ ·), (1 : ℝ) / ((a / g : ℕ) : ℝ)
      ≤ 1 / g * (1 + Real.log M) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1 + Real.log M) / g := by ring

/-- **`Σ_{j≤M} d(j)² ≤ M(1 + log M)³`.** -/
theorem sum_card_divisors_sq_le (M : ℕ) :
    ∑ j ∈ Ioc 0 M, ((j.divisors.card : ℕ) : ℝ) ^ 2 ≤ M * (1 + Real.log M) ^ 3 := by
  set I := Ioc 0 M with hI
  have hlog : 0 ≤ Real.log M := Real.log_natCast_nonneg M
  have hfilt : ∀ j ∈ I, I.filter (· ∣ j) = j.divisors := by
    intro j hj
    obtain ⟨hj0, hjM⟩ := mem_Ioc.1 hj
    ext a
    simp only [mem_filter, Nat.mem_divisors, hI, mem_Ioc]
    constructor
    · rintro ⟨_, ha⟩; exact ⟨ha, hj0.ne'⟩
    · rintro ⟨ha, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos ha hj0, (Nat.le_of_dvd hj0 ha).trans hjM⟩, ha⟩
  -- `d(j)² = #{(a, b) ∈ I² : a | j, b | j}`
  have h1 : ∀ j ∈ I, ((j.divisors.card : ℕ) : ℝ) ^ 2
      = ∑ a ∈ I, ∑ b ∈ I, if a ∣ j ∧ b ∣ j then (1 : ℝ) else 0 := by
    intro j hj
    have e : ∀ a ∈ I, (∑ b ∈ I, if a ∣ j ∧ b ∣ j then (1 : ℝ) else 0)
        = if a ∣ j then (j.divisors.card : ℝ) else 0 := by
      intro a _
      by_cases ha : a ∣ j
      · simp only [ha, true_and, ↓reduceIte]
        rw [sum_boole, hfilt j hj]
      · simp [ha]
    rw [sum_congr rfl e, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, sq,
      hfilt j hj]
  rw [sum_congr rfl h1]
  have hswap : ∑ j ∈ I, ∑ a ∈ I, ∑ b ∈ I, (if a ∣ j ∧ b ∣ j then (1 : ℝ) else 0)
      = ∑ a ∈ I, ∑ b ∈ I, ∑ j ∈ I, (if a ∣ j ∧ b ∣ j then (1 : ℝ) else 0) := by
    rw [sum_comm]; exact sum_congr rfl fun a _ => sum_comm
  rw [hswap]
  -- count multiples of `lcm(a, b)`
  have h2 : ∀ a ∈ I, ∀ b ∈ I, (∑ j ∈ I, if a ∣ j ∧ b ∣ j then (1 : ℝ) else 0)
      ≤ M * ((Nat.gcd a b : ℝ) / (a * b)) := by
    intro a ha b hb
    obtain ⟨ha0, _⟩ := mem_Ioc.1 ha
    obtain ⟨hb0, _⟩ := mem_Ioc.1 hb
    have e : (∑ j ∈ I, if a ∣ j ∧ b ∣ j then (1 : ℝ) else 0) = ((M / Nat.lcm a b : ℕ) : ℝ) := by
      rw [sum_boole, ← Nat.Ioc_filter_dvd_card_eq_div]
      congr 2
      exact filter_congr fun j _ => (Nat.lcm_dvd_iff).symm
    rw [e]
    have hgl : (Nat.gcd a b : ℝ) * Nat.lcm a b = a * b := by exact_mod_cast Nat.gcd_mul_lcm a b
    have hl0 : (0 : ℝ) < Nat.lcm a b := by exact_mod_cast Nat.lcm_pos ha0 hb0
    calc ((M / Nat.lcm a b : ℕ) : ℝ) ≤ (M : ℝ) / Nat.lcm a b := Nat.cast_div_le
      _ = M * ((Nat.gcd a b : ℝ) / (a * b)) := by rw [← hgl]; field_simp
  -- `gcd(a, b) ≤ Σ_{g | a, g | b} g`, written with `u_g(a) = [g | a]/a`
  set u : ℕ → ℕ → ℝ := fun g a => if g ∣ a then (1 : ℝ) / a else 0 with hu
  have h3 : ∀ a ∈ I, ∀ b ∈ I, (Nat.gcd a b : ℝ) / (a * b) ≤ ∑ g ∈ I, (g : ℝ) * (u g a * u g b) := by
    intro a ha b hb
    obtain ⟨ha0, haM⟩ := mem_Ioc.1 ha
    have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
    have hb0' : (0 : ℝ) < b := by exact_mod_cast (mem_Ioc.1 hb).1
    have hgI : Nat.gcd a b ∈ I :=
      mem_Ioc.2 ⟨Nat.gcd_pos_of_pos_left b ha0, (Nat.gcd_le_left b ha0).trans haM⟩
    rw [← add_sum_erase I _ hgI]
    have hterm : (Nat.gcd a b : ℝ) * (u (Nat.gcd a b) a * u (Nat.gcd a b) b)
        = (Nat.gcd a b : ℝ) / (a * b) := by
      simp only [hu, Nat.gcd_dvd_left, Nat.gcd_dvd_right, ↓reduceIte]
      field_simp
    have : 0 ≤ ∑ g ∈ I.erase (Nat.gcd a b), (g : ℝ) * (u g a * u g b) :=
      sum_nonneg fun g _ => by simp only [hu]; split_ifs <;> positivity
    linarith
  have hu_sum : ∀ g ∈ I, ∑ a ∈ I, u g a ≤ (1 + Real.log M) / g := by
    intro g hg
    have := sum_multiples_inv_le (M := M) (mem_Ioc.1 hg).1
    rwa [sum_filter] at this
  have hu0 : ∀ g a, 0 ≤ u g a := fun g a => by simp only [hu]; split_ifs <;> positivity
  calc ∑ a ∈ I, ∑ b ∈ I, ∑ j ∈ I, (if a ∣ j ∧ b ∣ j then (1 : ℝ) else 0)
      ≤ ∑ a ∈ I, ∑ b ∈ I, M * ∑ g ∈ I, (g : ℝ) * (u g a * u g b) :=
        sum_le_sum fun a ha => sum_le_sum fun b hb =>
          (h2 a ha b hb).trans (mul_le_mul_of_nonneg_left (h3 a ha b hb) (Nat.cast_nonneg M))
    _ = M * ∑ g ∈ I, (g : ℝ) * ((∑ a ∈ I, u g a) * (∑ b ∈ I, u g b)) := by
        simp_rw [← mul_sum]
        congr 1
        rw [sum_comm]
        simp_rw [sum_mul_sum, mul_sum]
        refine (sum_congr rfl fun b _ => sum_comm).trans ?_
        rw [sum_comm]
        exact sum_congr rfl fun g _ => sum_comm
    _ ≤ M * ∑ g ∈ I, (g : ℝ) * ((1 + Real.log M) / g * ((1 + Real.log M) / g)) := by
        gcongr with g hg <;> exact hu_sum g hg
    _ = M * ((1 + Real.log M) ^ 2 * ∑ g ∈ I, (1 : ℝ) / g) := by
        congr 1; rw [mul_sum]
        refine sum_congr rfl fun g hg => ?_
        have : (0 : ℝ) < g := by exact_mod_cast (mem_Ioc.1 hg).1
        field_simp
    _ ≤ M * ((1 + Real.log M) ^ 2 * (1 + Real.log M)) := by
        gcongr; exact harmonic_le M
    _ = M * (1 + Real.log M) ^ 3 := by ring

end DivSq

#print axioms DivSq.sum_card_divisors_sq_le
