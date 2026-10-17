import LinnikLines

/-!
# Round 539: the zero frequency and the degenerate lines

Built on Mathlib, `LinnikMoment` and `LinnikLines`; no PrimeNumberTheoremAnd file is imported.

Round 538 wrote the folded third moment as `q⁻²Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃)L(k)` over `k ∈ (ZMod q)³`. Chen–Gupta–Li split their
frequencies in §5: "S1 consists of terms with exactly one nonzero mi, S2 consists of terms with exactly two nonzero
mi and S3 consists of terms with all three mi being nonzero" (from the PDF's text layer, spaces restored). This file
evaluates the line sums off the generic lines exactly, for a prime `q`.

* `sum_mul_star`: `Σ_u χ(u)conj(χ′(u)) = (q − 1)·[χ = χ′]`.
* `lineSum_zero`: the zero frequency, `L(0) = (q − 1)²|W|`.
* `lineSum_only_k₁`, `lineSum_only_k₂`, `lineSum_only_k₃`: a line with exactly one nonzero coordinate has `L = 0`.
* `lineSum_k₁_zero`, `lineSum_k₂_zero`, `lineSum_k₃_zero`: a line with exactly two nonzero coordinates has
  `L = (q − 1)|R(c)|²` at one point, `c = −k₂/k₃`, `−k₁/k₃` or `−k₁/k₂`.
* `sum_lines_split`: `Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃)L(k) = ŵ(0)³(q − 1)²|W| + S₂ + S₃`, with `S₂` (`S2part`) the three families
  of degenerate lines in closed form and `S₃` (`S3part`) the sum over the `k` with all coordinates nonzero.
* `large_values_split`: with round 538's `large_values_lines`, `(|W|V² − N_cβ)³ ≤ β³·Re q⁻²(S₂ + S₃)`. Here
  `ŵ(0) = N_c`, and the zero frequency `q⁻²N_c³(q − 1)²|W|` is at most the `|W|N_c³` that Lemma 4.2 removes.
-/

open Finset

noncomputable section

namespace LinnikSplit

open LinnikLines

variable {q : ℕ} [hq : Fact q.Prime] [DecidableEq (DirichletCharacter ℂ q)]

/-- Orthogonality of the characters mod a prime: `Σ_u χ(u) conj(χ′(u)) = (q − 1)·[χ = χ′]`. -/
lemma sum_mul_star (χ χ' : DirichletCharacter ℂ q) :
    ∑ u : ZMod q, χ u * star (χ' u) = if χ = χ' then ((q : ℂ) - 1) else 0 := by
  have e : ∀ u : ZMod q, χ u * star (χ' u) = (χ * χ'⁻¹) u := fun u => by
    rw [MulChar.star_apply', MulChar.mul_apply]
  simp only [e]
  split_ifs with h
  · subst h
    rw [mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units]
    have : 1 ≤ q := hq.out.one_lt.le
    push_cast [Nat.cast_sub this]
    ring
  · exact MulChar.sum_eq_zero_of_ne_one fun h1 => h (mul_inv_eq_one.1 h1)

/-- `Σ_u R(u) R(c/u) = (q − 1) R(c)`. -/
lemma sum_R_R_div (W : Finset (DirichletCharacter ℂ q)) (c : ZMod q) :
    ∑ u : ZMod q, Rsum W u * Rsum W (c * u⁻¹) = ((q : ℂ) - 1) * Rsum W c := by
  calc ∑ u : ZMod q, Rsum W u * Rsum W (c * u⁻¹)
        = ∑ u : ZMod q, ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, χ₂ c * (χ₁ u * star (χ₂ u)) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Rsum, Rsum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun χ₁ _ => Finset.sum_congr rfl fun χ₂ _ => ?_
          rw [map_mul, star_apply_eq]; ring
    _ = ∑ χ₁ ∈ W, ∑ χ₂ ∈ W, χ₂ c * ∑ u : ZMod q, χ₁ u * star (χ₂ u) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ₁ _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun χ₂ _ => by rw [Finset.mul_sum]
    _ = ∑ χ₁ ∈ W, ((q : ℂ) - 1) * χ₁ c := by
          refine Finset.sum_congr rfl fun χ₁ hχ₁ => ?_
          simp only [sum_mul_star, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp [hχ₁, mul_comm]
    _ = ((q : ℂ) - 1) * Rsum W c := by rw [Rsum, Finset.mul_sum]

/-- `Σ_v R(v) conj(R(v)) = (q − 1)|W|`. -/
lemma sum_R_star_R (W : Finset (DirichletCharacter ℂ q)) :
    ∑ v : ZMod q, Rsum W v * star (Rsum W v) = ((q : ℂ) - 1) * W.card := by
  calc ∑ v : ZMod q, Rsum W v * star (Rsum W v) = ∑ v : ZMod q, ∑ χ ∈ W, ∑ χ' ∈ W, χ v * star (χ' v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Rsum, star_sum, Finset.sum_mul_sum]
    _ = ∑ χ ∈ W, ∑ χ' ∈ W, ∑ v : ZMod q, χ v * star (χ' v) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun χ _ => Finset.sum_comm
    _ = ∑ χ ∈ W, ((q : ℂ) - 1) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        simp only [sum_mul_star]
        rw [Finset.sum_ite_eq]
        simp [hχ]
    _ = ((q : ℂ) - 1) * W.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The zero frequency: `L(0) = (q − 1)²|W|`. -/
lemma lineSum_zero (W : Finset (DirichletCharacter ℂ q)) :
    lineSum W 0 0 0 = ((q : ℂ) - 1) ^ 2 * W.card := by
  have h1 : lineSum W 0 0 0 = ∑ v : ZMod q, star (Rsum W v) * ∑ u : ZMod q, Rsum W u * Rsum W (v * u⁻¹) := by
    simp only [lineSum, zero_mul, add_zero, ite_true, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
  rw [h1]
  simp only [sum_R_R_div]
  calc ∑ v : ZMod q, star (Rsum W v) * (((q : ℂ) - 1) * Rsum W v)
      = ((q : ℂ) - 1) * ∑ v : ZMod q, Rsum W v * star (Rsum W v) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    _ = ((q : ℂ) - 1) ^ 2 * W.card := by rw [sum_R_star_R]; ring

/-- `Σ_u R(u) conj(R(cu)) = (q − 1) conj(R(c))`. -/
lemma sum_R_star_R_mul (W : Finset (DirichletCharacter ℂ q)) (c : ZMod q) :
    ∑ u : ZMod q, Rsum W u * star (Rsum W (c * u)) = ((q : ℂ) - 1) * star (Rsum W c) := by
  calc ∑ u : ZMod q, Rsum W u * star (Rsum W (c * u))
        = ∑ u : ZMod q, ∑ χ₁ ∈ W, ∑ χ₃ ∈ W, star (χ₃ c) * (χ₁ u * star (χ₃ u)) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Rsum, Rsum, star_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun χ₁ _ => Finset.sum_congr rfl fun χ₃ _ => ?_
          rw [map_mul, star_mul']; ring
    _ = ∑ χ₁ ∈ W, ∑ χ₃ ∈ W, star (χ₃ c) * ∑ u : ZMod q, χ₁ u * star (χ₃ u) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ₁ _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun χ₃ _ => by rw [Finset.mul_sum]
    _ = ∑ χ₁ ∈ W, ((q : ℂ) - 1) * star (χ₁ c) := by
          refine Finset.sum_congr rfl fun χ₁ hχ₁ => ?_
          simp only [sum_mul_star, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp [hχ₁, mul_comm]
    _ = ((q : ℂ) - 1) * star (Rsum W c) := by rw [Rsum, star_sum, Finset.mul_sum]

/-- `Σ_v R(v/c) conj(R(v)) = (q − 1) conj(R(c))`. -/
lemma sum_R_div_star_R (W : Finset (DirichletCharacter ℂ q)) (c : ZMod q) :
    ∑ v : ZMod q, Rsum W (v * c⁻¹) * star (Rsum W v) = ((q : ℂ) - 1) * star (Rsum W c) := by
  calc ∑ v : ZMod q, Rsum W (v * c⁻¹) * star (Rsum W v)
        = ∑ v : ZMod q, ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, χ₂ c⁻¹ * (χ₂ v * star (χ₃ v)) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Rsum, Rsum, star_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun χ₂ _ => Finset.sum_congr rfl fun χ₃ _ => ?_
          rw [map_mul]; ring
    _ = ∑ χ₂ ∈ W, ∑ χ₃ ∈ W, χ₂ c⁻¹ * ∑ v : ZMod q, χ₂ v * star (χ₃ v) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ₂ _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun χ₃ _ => by rw [Finset.mul_sum]
    _ = ∑ χ₂ ∈ W, ((q : ℂ) - 1) * χ₂ c⁻¹ := by
          refine Finset.sum_congr rfl fun χ₂ hχ₂ => ?_
          simp only [sum_mul_star, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp [hχ₂, mul_comm]
    _ = ((q : ℂ) - 1) * star (Rsum W c) := by rw [← Rsum_inv, Rsum, Finset.mul_sum]


/-- `|R(c)|²` as `R(c)·conj(R(c))`. -/
def RR (W : Finset (DirichletCharacter ℂ q)) (c : ZMod q) : ℂ := Rsum W c * star (Rsum W c)

/-- A line with `k₂ = 0`, `k₃ ≠ 0`: `L(k₁, 0, k₃) = (q − 1)|R(−k₁/k₃)|²`. -/
lemma lineSum_k₂_zero (W : Finset (DirichletCharacter ℂ q)) (k₁ : ZMod q) {k₃ : ZMod q} (hk₃ : k₃ ≠ 0) :
    lineSum W k₁ 0 k₃ = ((q : ℂ) - 1) * RR W (-k₁ * k₃⁻¹) := by
  have hc : ∀ u v : ZMod q, (k₁ + 0 * u + k₃ * v = 0 ↔ v = -k₁ * k₃⁻¹) := by
    intro u v
    constructor
    · intro h
      rw [eq_comm, ← div_eq_mul_inv, div_eq_iff hk₃]
      linear_combination -h
    · rintro rfl
      field_simp
      ring
  simp only [lineSum, hc, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul, sum_R_R_div, RR]
  ring

/-- A line with `k₃ = 0`, `k₂ ≠ 0`: `L(k₁, k₂, 0) = (q − 1)|R(−k₁/k₂)|²`. -/
lemma lineSum_k₃_zero (W : Finset (DirichletCharacter ℂ q)) (k₁ : ZMod q) {k₂ : ZMod q} (hk₂ : k₂ ≠ 0) :
    lineSum W k₁ k₂ 0 = ((q : ℂ) - 1) * RR W (-k₁ * k₂⁻¹) := by
  have hc : ∀ u v : ZMod q, (k₁ + k₂ * u + 0 * v = 0 ↔ u = -k₁ * k₂⁻¹) := by
    intro u v
    constructor
    · intro h
      rw [eq_comm, ← div_eq_mul_inv, div_eq_iff hk₂]
      linear_combination -h
    · rintro rfl
      field_simp
      ring
  simp only [lineSum, hc]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [sum_R_div_star_R, RR]
  ring

/-- A line with `k₁ = 0`, `k₂, k₃ ≠ 0`: `L(0, k₂, k₃) = (q − 1)|R(−k₂/k₃)|²`. -/
lemma lineSum_k₁_zero (W : Finset (DirichletCharacter ℂ q)) {k₂ k₃ : ZMod q} (hk₃ : k₃ ≠ 0) :
    lineSum W 0 k₂ k₃ = ((q : ℂ) - 1) * RR W (-k₂ * k₃⁻¹) := by
  set c := -k₂ * k₃⁻¹ with hcdef
  have hc : ∀ u v : ZMod q, (0 + k₂ * u + k₃ * v = 0 ↔ v = c * u) := by
    intro u v
    constructor
    · intro h
      rw [hcdef, eq_comm, mul_comm, ← mul_assoc, ← div_eq_mul_inv, div_eq_iff hk₃]
      linear_combination -h
    · rintro rfl
      rw [hcdef]
      field_simp
      ring
  simp only [lineSum, hc, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have e : ∀ u : ZMod q, Rsum W u * Rsum W (c * u * u⁻¹) * star (Rsum W (c * u)) =
      Rsum W c * (Rsum W u * star (Rsum W (c * u))) := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp [Rsum_zero]
    · rw [mul_assoc c u, mul_inv_cancel₀ hu, mul_one]; ring
  simp only [e, ← Finset.mul_sum, sum_R_star_R_mul, RR]
  ring

omit [DecidableEq (DirichletCharacter ℂ q)] in
lemma lineSum_only_k₁ (W : Finset (DirichletCharacter ℂ q)) {k₁ : ZMod q} (hk₁ : k₁ ≠ 0) :
    lineSum W k₁ 0 0 = 0 := by
  simp [lineSum, hk₁]

omit [DecidableEq (DirichletCharacter ℂ q)] in
lemma lineSum_only_k₂ (W : Finset (DirichletCharacter ℂ q)) {k₂ : ZMod q} (hk₂ : k₂ ≠ 0) :
    lineSum W 0 k₂ 0 = 0 := by
  simp [lineSum, hk₂, Rsum_zero]

omit [DecidableEq (DirichletCharacter ℂ q)] in
lemma lineSum_only_k₃ (W : Finset (DirichletCharacter ℂ q)) {k₃ : ZMod q} (hk₃ : k₃ ≠ 0) :
    lineSum W 0 0 k₃ = 0 := by
  simp [lineSum, hk₃, Rsum_zero]

omit [DecidableEq (DirichletCharacter ℂ q)] in
/-- Splitting a sum over `(ZMod q)³` by the zero coordinates, when the terms with exactly one nonzero coordinate
vanish. -/
lemma sum_split (f : ZMod q → ZMod q → ZMod q → ℂ) (h1 : ∀ k ≠ 0, f k 0 0 = 0) (h2 : ∀ k ≠ 0, f 0 k 0 = 0)
    (h3 : ∀ k ≠ 0, f 0 0 k = 0) :
    ∑ k₁, ∑ k₂, ∑ k₃, f k₁ k₂ k₃ = f 0 0 0 +
      (∑ k₂ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, f 0 k₂ k₃ + ∑ k₁ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, f k₁ 0 k₃ +
        ∑ k₁ ∈ univ.erase 0, ∑ k₂ ∈ univ.erase 0, f k₁ k₂ 0) +
      ∑ k₁ ∈ univ.erase 0, ∑ k₂ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, f k₁ k₂ k₃ := by
  have hs : ∀ g : ZMod q → ℂ, ∑ k, g k = g 0 + ∑ k ∈ univ.erase 0, g k :=
    fun g => (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have z1 : ∑ k ∈ univ.erase (0 : ZMod q), f k 0 0 = 0 :=
    Finset.sum_eq_zero fun k hk => h1 k (Finset.ne_of_mem_erase hk)
  have z2 : ∑ k ∈ univ.erase (0 : ZMod q), f 0 k 0 = 0 :=
    Finset.sum_eq_zero fun k hk => h2 k (Finset.ne_of_mem_erase hk)
  have z3 : ∑ k ∈ univ.erase (0 : ZMod q), f 0 0 k = 0 :=
    Finset.sum_eq_zero fun k hk => h3 k (Finset.ne_of_mem_erase hk)
  have step : ∀ k₁, ∑ k₂, ∑ k₃, f k₁ k₂ k₃ = (f k₁ 0 0 + ∑ k₃ ∈ univ.erase 0, f k₁ 0 k₃) +
      ∑ k₂ ∈ univ.erase 0, (f k₁ k₂ 0 + ∑ k₃ ∈ univ.erase 0, f k₁ k₂ k₃) := by
    intro k₁
    rw [hs, hs (f k₁ 0)]
    congr 1
    exact Finset.sum_congr rfl fun k₂ _ => hs (f k₁ k₂)
  rw [Finset.sum_congr rfl fun k₁ _ => step k₁, hs]
  simp only [Finset.sum_add_distrib, z1, z2, z3]
  ring

/-- The part of the folded third moment on the lines with exactly two nonzero coordinates (Chen–Gupta–Li's `S₂`),
in closed form. -/
def S2part (W : Finset (DirichletCharacter ℂ q)) (ŵ : ZMod q → ℂ) : ℂ :=
  ((q : ℂ) - 1) * (∑ k₂ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, ŵ 0 * ŵ k₂ * ŵ k₃ * RR W (-k₂ * k₃⁻¹) +
    ∑ k₁ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, ŵ k₁ * ŵ 0 * ŵ k₃ * RR W (-k₁ * k₃⁻¹) +
    ∑ k₁ ∈ univ.erase 0, ∑ k₂ ∈ univ.erase 0, ŵ k₁ * ŵ k₂ * ŵ 0 * RR W (-k₁ * k₂⁻¹))

/-- The part of the folded third moment on the lines with all coordinates nonzero (Chen–Gupta–Li's `S₃`). -/
def S3part (W : Finset (DirichletCharacter ℂ q)) (ŵ : ZMod q → ℂ) : ℂ :=
  ∑ k₁ ∈ univ.erase 0, ∑ k₂ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, ŵ k₁ * ŵ k₂ * ŵ k₃ * lineSum W k₁ k₂ k₃

/-- **The split**: `Σ_k ŵ(k₁)ŵ(k₂)ŵ(k₃)L(k) = ŵ(0)³(q − 1)²|W| + S₂ + S₃`; the lines with exactly one nonzero
coordinate contribute nothing. -/
theorem sum_lines_split (W : Finset (DirichletCharacter ℂ q)) (ŵ : ZMod q → ℂ) :
    ∑ k₁, ∑ k₂, ∑ k₃, ŵ k₁ * ŵ k₂ * ŵ k₃ * lineSum W k₁ k₂ k₃ =
      ŵ 0 ^ 3 * (((q : ℂ) - 1) ^ 2 * W.card) + S2part W ŵ + S3part W ŵ := by
  rw [sum_split (fun k₁ k₂ k₃ => ŵ k₁ * ŵ k₂ * ŵ k₃ * lineSum W k₁ k₂ k₃)
    (fun k hk => by simp [lineSum_only_k₁ W hk]) (fun k hk => by simp [lineSum_only_k₂ W hk])
    (fun k hk => by simp [lineSum_only_k₃ W hk])]
  have e1 : ∑ k₂ ∈ univ.erase (0 : ZMod q), ∑ k₃ ∈ univ.erase 0, ŵ 0 * ŵ k₂ * ŵ k₃ * lineSum W 0 k₂ k₃ =
      ((q : ℂ) - 1) * ∑ k₂ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, ŵ 0 * ŵ k₂ * ŵ k₃ * RR W (-k₂ * k₃⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₃ hk₃ => ?_
    rw [lineSum_k₁_zero W (Finset.ne_of_mem_erase hk₃)]; ring
  have e2 : ∑ k₁ ∈ univ.erase (0 : ZMod q), ∑ k₃ ∈ univ.erase 0, ŵ k₁ * ŵ 0 * ŵ k₃ * lineSum W k₁ 0 k₃ =
      ((q : ℂ) - 1) * ∑ k₁ ∈ univ.erase 0, ∑ k₃ ∈ univ.erase 0, ŵ k₁ * ŵ 0 * ŵ k₃ * RR W (-k₁ * k₃⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₃ hk₃ => ?_
    rw [lineSum_k₂_zero W k₁ (Finset.ne_of_mem_erase hk₃)]; ring
  have e3 : ∑ k₁ ∈ univ.erase (0 : ZMod q), ∑ k₂ ∈ univ.erase 0, ŵ k₁ * ŵ k₂ * ŵ 0 * lineSum W k₁ k₂ 0 =
      ((q : ℂ) - 1) * ∑ k₁ ∈ univ.erase 0, ∑ k₂ ∈ univ.erase 0, ŵ k₁ * ŵ k₂ * ŵ 0 * RR W (-k₁ * k₂⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₂ hk₂ => ?_
    rw [lineSum_k₃_zero W k₁ (Finset.ne_of_mem_erase hk₂)]; ring
  rw [e1, e2, e3, lineSum_zero, S2part, S3part]
  ring


omit [DecidableEq (DirichletCharacter ℂ q)] in
/-- `ŵ(0)` for the residue weights of `c` on `S` is `N_c = Σ_{n∈S}|c_n|²`. -/
lemma what_resW_zero (S : Finset ℕ) (c : ℕ → ℂ) :
    what (resW (q := q) S c) 0 = ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
  simp only [what, mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, resW]
  rw [Finset.sum_fiberwise S (fun n => (n : ZMod q)) (fun n => ((‖c n‖ ^ 2 : ℝ) : ℂ))]
  push_cast
  rfl

/-- **Large values through `S₂` and `S₃`.** Under the hypotheses of `LinnikLines.large_values_lines`,
`(|W|V² − N_cβ)³ ≤ β³ Re q⁻²(S₂ + S₃)`: the zero frequency, `q⁻²N_c³(q − 1)²|W|`, is at most the `|W|N_c³` that
round 537's Lemma 4.2 removes, and the lines with exactly one nonzero coordinate carry nothing. -/
theorem large_values_split (W : Finset (DirichletCharacter ℂ q)) (S : Finset ℕ) (b c : ℕ → ℂ)
    (hS : ∀ n ∈ S, IsUnit (n : ZMod q)) {V : ℝ}
    (hV : ∀ χ ∈ W, V ^ 2 ≤ ‖∑ n ∈ S, c n * χ n * b n‖ ^ 2)
    (hge : (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2) ≤ W.card * V ^ 2) :
    (W.card * V ^ 2 - (∑ n ∈ S, ‖c n‖ ^ 2) * (∑ n ∈ S, ‖b n‖ ^ 2)) ^ 3 ≤
      (∑ n ∈ S, ‖b n‖ ^ 2) ^ 3 *
        ((q : ℂ)⁻¹ ^ 2 * (S2part W (what (resW S c)) + S3part W (what (resW S c)))).re := by
  set Nc := ∑ n ∈ S, ‖c n‖ ^ 2 with hNc
  set β := ∑ n ∈ S, ‖b n‖ ^ 2 with hβ
  have key := large_values_lines W S b c hS hV hge
  rw [sum_lines_split, what_resW_zero, ← hNc] at key
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.out.one_lt.le
  have hNc0 : 0 ≤ Nc := Finset.sum_nonneg fun _ _ => by positivity
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun _ _ => by positivity
  have hre : ((q : ℂ)⁻¹ ^ 2 * ((Nc : ℂ) ^ 3 * (((q : ℂ) - 1) ^ 2 * W.card) + S2part W (what (resW S c)) +
      S3part W (what (resW S c)))).re = Nc ^ 3 * ((q - 1) ^ 2 / q ^ 2) * W.card +
      ((q : ℂ)⁻¹ ^ 2 * (S2part W (what (resW S c)) + S3part W (what (resW S c)))).re := by
    rw [show (q : ℂ)⁻¹ ^ 2 * ((Nc : ℂ) ^ 3 * (((q : ℂ) - 1) ^ 2 * W.card) + S2part W (what (resW S c)) +
        S3part W (what (resW S c))) = ((Nc ^ 3 * ((q - 1) ^ 2 / q ^ 2) * W.card : ℝ) : ℂ) +
        (q : ℂ)⁻¹ ^ 2 * (S2part W (what (resW S c)) + S3part W (what (resW S c))) by push_cast; ring]
    rw [Complex.add_re, Complex.ofReal_re]
  rw [hre] at key
  have hfrac : (q - 1 : ℝ) ^ 2 / q ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hcorr : Nc ^ 3 * ((q - 1) ^ 2 / q ^ 2) * W.card - W.card * Nc ^ 3 ≤ 0 := by
    have : Nc ^ 3 * ((q - 1) ^ 2 / q ^ 2) * W.card ≤ Nc ^ 3 * 1 * W.card := by gcongr
    linarith
  calc (W.card * V ^ 2 - Nc * β) ^ 3
      ≤ β ^ 3 * (Nc ^ 3 * ((q - 1) ^ 2 / q ^ 2) * W.card +
          ((q : ℂ)⁻¹ ^ 2 * (S2part W (what (resW S c)) + S3part W (what (resW S c)))).re - W.card * Nc ^ 3) := key
    _ ≤ β ^ 3 * ((q : ℂ)⁻¹ ^ 2 * (S2part W (what (resW S c)) + S3part W (what (resW S c)))).re := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end LinnikSplit
