import Mathlib
import BohrSphere

/-! # The infinite cube and the infinite ball are different objects (round 397)

The owner wrote: "The infinite unit ball & the infinite unit cube is the same object in the limit". This file proves
that they are not the same object as metric spaces, nor up to any linear map of bounded distortion, and that the
Euclidean ball inside the cube holds a vanishing share of its volume. It proves facts about one sense in which they
are the same, the topological one, and it records what the Bohr lift `z(s) = (p^{−s})_p` does in each. The cube is the unit ball of the sup norm: `[−1, 1]ⁿ` in `ℝⁿ`, and
the closed unit ball of `ℓ^∞(ℕ)` in the limit.

* **No isometric copy** (**`no_isometry_square`**, **`no_isometry_cube`**, **`no_isometry_infCube`** and
  **`not_isometry_infCube`**, with `sub_eq_sub_of_dist_eq_half`, `eq_of_midpoints_inner`, `norm_vec2`,
  `no_isometry_of_square`, `sqInf`, `sqInf_apply`, `norm_sqInf`, `sqInf_sub`, `sqFin`, `norm_sqFin` and
  `sqFin_sub`): in an inner product space at most one point lies at distance `1` from both ends of a segment of
  length `2` (the parallelogram law). In the square `[−1, 1]²` with the sup distance, `(0, 0)` and `(0, 1)` are two
  such points for `(−1, 0)` and `(1, 0)`, at distance `1` from each other. So no distance-preserving map takes the
  square, the cube `[−1, 1]ⁿ` for any `n ≥ 2`, or the infinite cube into an inner product space, the infinite ball
  included.
* **The distortion is at least `√n`** (**`exists_signs_sum_sq_le`**, **`card_mul_sq_le_of_signs`**,
  **`cube_distortion`**, **`euclidean_sandwich`**, **`infCube_not_ball`** and **`not_continuousLinearEquiv`**): if
  an additive map `T` from `ℝⁿ` with the sup norm into an inner product space satisfies `c‖x‖ ≤ ‖T x‖ ≤ C‖x‖` with
  `c ≥ 0`, then `n c² ≤ C²`. The proof picks signs one vector at a time so that `‖Σ ±T e_i‖² ≥ Σ ‖T e_i‖²`, again
  by the parallelogram law. The identity into Euclidean `ℝⁿ` has `c = 1` and `C = √n`, so the least distortion is
  exactly `√n`, which tends to infinity. For the infinite cube no additive map into an inner product space has
  `c > 0` and a finite `C`; in particular no isomorphism of normed spaces identifies `ℓ^∞(ℕ)` with one.
* **The Euclidean ball's share of the cube tends to `0`** (**`ball_subset_cube`**, **`volume_euclideanBall`** and
  **`tendsto_ball_div_cube`**): the Euclidean unit ball of `ℝⁿ` lies inside the cube `(−1, 1)ⁿ`, and the ratio of
  their volumes tends to `0`.
* **The Bohr lift tells them apart** (`zCube`, a definition; **`memℓp_top_bohr_iff`**, **`norm_zCube`**,
  **`norm_zCube_eq_one_iff`** and **`line_inside_cube_not_in_ell2`**): `z(s)` is a point of `ℓ^∞` if and only if
  `Re s ≥ 0`, with sup norm `2^{−Re s}`. So `z(s)` lies on the cube's unit sphere exactly on the line `Re s = 0`,
  and the critical line lies strictly inside the cube, at sup norm `2^{−1/2}`, while there `z(s)` is not a point of
  `ℓ²` at all (round 391's `memℓp_two_bohr_iff`).
* **After normalisation every `ℓ^r` sphere is the critical line** (`zLp` and `vLp`, definitions;
  **`vLp_mem_sphere_iff`**, **`norm_zLp_eq_of_re_eq`** and **`norm_zLp_lt_of_re_lt`**, with `norm_piLp_le_of_forall`,
  `norm_zLp_apply` and `norm_zLp_pos`): for every `1 ≤ r ≤ ∞` and every nonempty finite set `F` of primes,
  `z_F(s)/‖z_F(½)‖_r` lies on the unit sphere of `ℓ^r(F)` if and only if `Re s = ½`, because `‖z_F(s)‖_r` depends
  only on `Re s` and strictly decreases in it. Round 391 proved the Euclidean case `r = 2` (`vF_mem_sphere_iff`);
  the cube, `r = ∞`, gives the same line. For these balls the normalisation at `s = ½`, not the choice of ball, puts
  the line on the sphere.
* **The topological sense** (`ellUnit`, a definition; **`exists_unit_seq_tendsto_inner`**,
  **`tendsto_inner_ellUnit`**, **`not_isCompact_closedBall_ell2`**, **`isCompact_hilbertCube`** and
  **`isEmpty_homeomorph_ball_hilbertCube`**, with `norm_ellUnit`, `inner_ellUnit_left`, `inner_ellUnit_right`,
  `tendsto_ell2_apply_zero` and `dist_ellUnit`): with the norm topology the closed unit ball of `ℓ²(ℕ)` is not
  compact, the unit vectors being pairwise at distance `√2`, so it is not homeomorphic to the Hilbert cube
  `[−1, 1]^ℕ` with the product topology, which is compact. With the weak topology the ball is homeomorphic to the
  Hilbert cube (Keller, 1931; not proved here). In that topology every point of the ball is a limit of points of
  the unit sphere, and the unit vectors, of norm `1`, converge to the centre, of norm `0`: a limit of points of the
  sphere need not lie on it.

Nothing here constrains the zeros of `ζ`.
-/

open Metric Filter Topology ENNReal MeasureTheory BohrSphere

namespace CubeBall

/-! ## Part A: no isometric copy of the cube in an inner product space -/

section Metric

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

include 𝕜 in
/-- In an inner product space, a point at half the distance from both ends of a segment satisfies
`x − z = z − y`. -/
lemma sub_eq_sub_of_dist_eq_half {x y z : E} (hx : dist x z = dist x y / 2)
    (hy : dist z y = dist x y / 2) : x - z = z - y := by
  have h := parallelogram_law_with_norm 𝕜 (x - z) (z - y)
  have h1 : ‖x - z‖ = dist x y / 2 := by rw [← dist_eq_norm]; exact hx
  have h2 : ‖z - y‖ = dist x y / 2 := by rw [← dist_eq_norm]; exact hy
  have h3 : ‖x - z + (z - y)‖ = dist x y := by rw [dist_eq_norm]; congr 1; abel
  rw [h1, h2, h3] at h
  have h0 : ‖x - z - (z - y)‖ ^ 2 = 0 := by linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))

include 𝕜 in
/-- **Midpoints are unique in an inner product space**: two points at distance `1` from both ends of a
segment of length `2` coincide. -/
theorem eq_of_midpoints_inner {X Y Z₁ Z₂ : E} (hXY : dist X Y = 2) (h₁ : dist X Z₁ = 1) (h₁' : dist Z₁ Y = 1)
    (h₂ : dist X Z₂ = 1) (h₂' : dist Z₂ Y = 1) : Z₁ = Z₂ := by
  have e₁ := sub_eq_sub_of_dist_eq_half (𝕜 := 𝕜) (x := X) (y := Y) (z := Z₁) (by rw [h₁, hXY]; norm_num)
    (by rw [h₁', hXY]; norm_num)
  have e₂ := sub_eq_sub_of_dist_eq_half (𝕜 := 𝕜) (x := X) (y := Y) (z := Z₂) (by rw [h₂, hXY]; norm_num)
    (by rw [h₂', hXY]; norm_num)
  rw [sub_eq_sub_iff_add_eq_add] at e₁ e₂
  have h : (2 : 𝕜) • Z₁ = (2 : 𝕜) • Z₂ := by rw [two_smul, two_smul, ← e₁, ← e₂]
  exact smul_right_injective E two_ne_zero h

/-- The sup norm of a vector of `ℝ²`. -/
lemma norm_vec2 (a b : ℝ) : ‖(![a, b] : Fin 2 → ℝ)‖ = max |a| |b| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).2 ?_
    intro i
    fin_cases i
    · simp [Real.norm_eq_abs]
    · simp [Real.norm_eq_abs]
  · refine max_le ?_ ?_
    · simpa [Real.norm_eq_abs] using norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 0
    · simpa [Real.norm_eq_abs] using norm_le_pi_norm (![a, b] : Fin 2 → ℝ) 1

include 𝕜 in
/-- **The unit square has no isometric copy in an inner product space.** In the square `[−1, 1]²` with the
sup distance, the points `(−1, 0)` and `(1, 0)` are at distance `2`, and `(0, 0)` and `(0, 1)` are both at
distance `1` from each of them and at distance `1` from each other. -/
theorem no_isometry_square (f : (Fin 2 → ℝ) → E)
    (hf : ∀ x ∈ closedBall (0 : Fin 2 → ℝ) 1, ∀ y ∈ closedBall (0 : Fin 2 → ℝ) 1,
      dist (f x) (f y) = dist x y) : False := by
  have hd : ∀ a b c d : ℝ, dist (![a, b] : Fin 2 → ℝ) ![c, d] = max |a - c| |b - d| := by
    intro a b c d
    rw [dist_eq_norm, ← norm_vec2]
    congr 1
    ext i
    fin_cases i <;> simp
  have hm : ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 → (![a, b] : Fin 2 → ℝ) ∈ closedBall (0 : Fin 2 → ℝ) 1 := by
    intro a b ha hb
    rw [mem_closedBall, dist_zero_right, norm_vec2]
    exact max_le ha hb
  have hX := hm (-1) 0 (by norm_num) (by norm_num)
  have hY := hm 1 0 (by norm_num) (by norm_num)
  have h₁ := hm 0 0 (by norm_num) (by norm_num)
  have h₂ := hm 0 1 (by norm_num) (by norm_num)
  have e := eq_of_midpoints_inner (𝕜 := 𝕜)
    (by rw [hf _ hX _ hY, hd]; norm_num) (by rw [hf _ hX _ h₁, hd]; norm_num)
    (by rw [hf _ h₁ _ hY, hd]; norm_num) (by rw [hf _ hX _ h₂, hd]; norm_num)
    (by rw [hf _ h₂ _ hY, hd]; norm_num)
  have := hf _ h₁ _ h₂
  rw [e, dist_self, hd] at this
  norm_num at this

include 𝕜 in
/-- If a normed group `V` contains the square isometrically, by an additive map, then the unit ball of `V` has
no isometric copy in an inner product space. -/
theorem no_isometry_of_square {V : Type*} [SeminormedAddCommGroup V] (g : (Fin 2 → ℝ) → V)
    (hg : ∀ x, ‖g x‖ = ‖x‖) (hsub : ∀ x y, g x - g y = g (x - y)) (f : V → E)
    (hf : ∀ x ∈ closedBall (0 : V) 1, ∀ y ∈ closedBall (0 : V) 1, dist (f x) (f y) = dist x y) :
    False := by
  have hm : ∀ x ∈ closedBall (0 : Fin 2 → ℝ) 1, g x ∈ closedBall (0 : V) 1 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    rwa [hg]
  refine no_isometry_square (𝕜 := 𝕜) (f ∘ g) fun x hx y hy => ?_
  rw [Function.comp_apply, Function.comp_apply, hf _ (hm x hx) _ (hm y hy), dist_eq_norm, hsub, hg,
    ← dist_eq_norm]

/-- The square on the first two coordinates of the infinite cube's space `ℓ^∞(ℕ)`. -/
noncomputable def sqInf (x : Fin 2 → ℝ) : lp (fun _ : ℕ => ℝ) ∞ :=
  lp.single ∞ 0 (x 0) + lp.single ∞ 1 (x 1)

lemma sqInf_apply (x : Fin 2 → ℝ) (j : ℕ) :
    sqInf x j = (if j = 0 then x 0 else 0) + (if j = 1 then x 1 else 0) := by
  simp [sqInf, Pi.single_apply]

lemma norm_sqInf (x : Fin 2 → ℝ) : ‖sqInf x‖ = ‖x‖ := by
  apply le_antisymm
  · refine lp.norm_le_of_forall_le (norm_nonneg x) fun j => ?_
    rw [sqInf_apply]
    by_cases h0 : j = 0
    · subst h0; simpa using norm_le_pi_norm x 0
    · by_cases h1 : j = 1
      · subst h1; simpa using norm_le_pi_norm x 1
      · simp [h0, h1]
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    fin_cases i
    · simpa [sqInf_apply] using lp.norm_apply_le_norm (by simp) (sqInf x) 0
    · simpa [sqInf_apply] using lp.norm_apply_le_norm (by simp) (sqInf x) 1

lemma sqInf_sub (x y : Fin 2 → ℝ) : sqInf x - sqInf y = sqInf (x - y) := by
  ext j
  simp only [lp.coeFn_sub, Pi.sub_apply, sqInf_apply]
  split_ifs <;> ring

include 𝕜 in
/-- **The infinite cube has no isometric copy in an inner product space**: no map of the closed unit ball of
`ℓ^∞(ℕ)` into an inner product space preserves distances. -/
theorem no_isometry_infCube (f : lp (fun _ : ℕ => ℝ) ∞ → E)
    (hf : ∀ x ∈ closedBall (0 : lp (fun _ : ℕ => ℝ) ∞) 1, ∀ y ∈ closedBall (0 : lp (fun _ : ℕ => ℝ) ∞) 1,
      dist (f x) (f y) = dist x y) : False :=
  no_isometry_of_square (𝕜 := 𝕜) sqInf norm_sqInf sqInf_sub f hf

/-- The square on the first two coordinates of the cube's space `ℝⁿ`, `n ≥ 2`. -/
def sqFin {n : ℕ} (x : Fin 2 → ℝ) : Fin n → ℝ := fun i =>
  (if (i : ℕ) = 0 then x 0 else 0) + (if (i : ℕ) = 1 then x 1 else 0)

lemma norm_sqFin {n : ℕ} (hn : 2 ≤ n) (x : Fin 2 → ℝ) : ‖(sqFin x : Fin n → ℝ)‖ = ‖x‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
    simp only [sqFin]
    by_cases h0 : (i : ℕ) = 0
    · simpa [h0] using norm_le_pi_norm x 0
    · by_cases h1 : (i : ℕ) = 1
      · simpa [h1] using norm_le_pi_norm x 1
      · simp [h0, h1]
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    fin_cases i
    · simpa [sqFin] using norm_le_pi_norm (sqFin x : Fin n → ℝ) ⟨0, by omega⟩
    · simpa [sqFin] using norm_le_pi_norm (sqFin x : Fin n → ℝ) ⟨1, by omega⟩

lemma sqFin_sub {n : ℕ} (x y : Fin 2 → ℝ) :
    (sqFin x : Fin n → ℝ) - sqFin y = sqFin (x - y) := by
  ext i
  simp only [sqFin, Pi.sub_apply]
  split_ifs <;> ring

include 𝕜 in
/-- **For every `n ≥ 2` the cube `[−1, 1]ⁿ` has no isometric copy in an inner product space.** -/
theorem no_isometry_cube {n : ℕ} (hn : 2 ≤ n) (f : (Fin n → ℝ) → E)
    (hf : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ∀ y ∈ closedBall (0 : Fin n → ℝ) 1,
      dist (f x) (f y) = dist x y) : False :=
  no_isometry_of_square (𝕜 := 𝕜) sqFin (norm_sqFin hn) sqFin_sub f hf

include 𝕜 in
/-- No isometry, onto or not, from the infinite cube's space `ℓ^∞(ℕ)` into an inner product space. -/
theorem not_isometry_infCube (f : lp (fun _ : ℕ => ℝ) ∞ → E) (hf : Isometry f) : False :=
  no_isometry_infCube (𝕜 := 𝕜) f fun x _ y _ => hf.dist_eq x y

end Metric

/-! ## Part B: the distortion is at least `√n` -/

section Distortion

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

include 𝕜 in
/-- **Greedy signs.** For vectors `w_i`, `i ∈ s`, of an inner product space, some choice of signs gives
`‖Σ ±w_i‖² ≥ Σ ‖w_i‖²`: by the parallelogram law, one of `‖v + w‖²` and `‖v − w‖²` is at least
`‖v‖² + ‖w‖²`, so the signs can be chosen one vector at a time. -/
theorem exists_signs_sum_sq_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → E) :
    ∃ ε : ι → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∑ i ∈ s, ‖w i‖ ^ 2 ≤ ‖∑ i ∈ s, ε i • w i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ε, hε, hle⟩ := ih
    set v := ∑ i ∈ s, ε i • w i with hv
    have hpar := parallelogram_law_with_norm 𝕜 v (w a)
    have key : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ‖v‖ ^ 2 + ‖w a‖ ^ 2 ≤ ‖v + σ • w a‖ ^ 2 →
        ∃ ε' : ι → ℤ, (∀ i, ε' i = 1 ∨ ε' i = -1) ∧
          ∑ i ∈ insert a s, ‖w i‖ ^ 2 ≤ ‖∑ i ∈ insert a s, ε' i • w i‖ ^ 2 := by
      intro σ hσ h
      refine ⟨Function.update ε a σ, fun i => ?_, ?_⟩
      · by_cases hi : i = a
        · subst hi; simpa using hσ
        · rw [Function.update_of_ne hi]; exact hε i
      · rw [Finset.sum_insert ha, Finset.sum_insert ha, Function.update_self]
        have hs : ∑ i ∈ s, Function.update ε a σ i • w i = v :=
          Finset.sum_congr rfl fun i hi => by
            rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
        rw [hs, add_comm (σ • w a) v]
        linarith
    by_cases h : ‖v‖ ^ 2 + ‖w a‖ ^ 2 ≤ ‖v + w a‖ ^ 2
    · exact key 1 (Or.inl rfl) (by simpa using h)
    · refine key (-1) (Or.inr rfl) ?_
      rw [neg_smul, one_smul, ← sub_eq_add_neg]
      linarith

include 𝕜 in
/-- **The core inequality.** If `‖w_i‖ ≥ c ≥ 0` for `i ∈ s` and every signed sum `Σ ±w_i` has norm at most `C`,
then `|s| c² ≤ C²`. -/
theorem card_mul_sq_le_of_signs {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → E) {c C : ℝ} (hc : 0 ≤ c)
    (hw : ∀ i ∈ s, c ≤ ‖w i‖)
    (hC : ∀ ε : ι → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) → ‖∑ i ∈ s, ε i • w i‖ ≤ C) :
    s.card * c ^ 2 ≤ C ^ 2 := by
  obtain ⟨ε, hε, hle⟩ := exists_signs_sum_sq_le (𝕜 := 𝕜) s w
  have h1 : (s.card : ℝ) * c ^ 2 ≤ ∑ i ∈ s, ‖w i‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => pow_le_pow_left₀ hc (hw i hi) 2
  have h3 : ‖∑ i ∈ s, ε i • w i‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC ε hε) 2
  linarith

include 𝕜 in
/-- **The cube against any ball, in dimension `n`.** If an additive map `T` from the cube's space `ℝⁿ` (sup norm,
unit ball `[−1, 1]ⁿ`) into an inner product space satisfies `c‖x‖ ≤ ‖T x‖ ≤ C‖x‖` with `c ≥ 0`, then
`n c² ≤ C²`: the distortion `C/c` is at least `√n`. -/
theorem cube_distortion {n : ℕ} (T : (Fin n → ℝ) →+ E) {c C : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x, c * ‖x‖ ≤ ‖T x‖) (hup : ∀ x, ‖T x‖ ≤ C * ‖x‖) : n * c ^ 2 ≤ C ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, zero_mul]; positivity
  have he : ∀ i : Fin n, ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := fun i => by
    rw [Pi.norm_single, norm_one]
  have hC0 : 0 ≤ C := by
    have := hup (Pi.single ⟨0, hn⟩ 1)
    rw [he, mul_one] at this
    exact (norm_nonneg _).trans this
  have key := card_mul_sq_le_of_signs (𝕜 := 𝕜) Finset.univ (fun i : Fin n => T (Pi.single i 1)) hc
    (fun i _ => by simpa [he] using hlow (Pi.single i 1)) fun ε hε => by
      have hsum : ∑ i, ε i • T (Pi.single i (1 : ℝ)) = T (∑ i, ε i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
        rw [map_sum]; simp only [map_zsmul]
      have hvec : ‖∑ i, ε i • (Pi.single i (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
        rw [Finset.sum_apply]
        rcases hε j with h | h <;> simp [Pi.single_apply, h]
      rw [hsum]
      calc ‖T _‖ ≤ C * ‖∑ i, ε i • (Pi.single i (1 : ℝ) : Fin n → ℝ)‖ := hup _
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hvec hC0
        _ = C := mul_one C
  simpa using key

/-- **The bound is attained**: the identity from the cube's space to Euclidean `ℝⁿ` has `c = 1` and `C = √n`. -/
theorem euclidean_sandwich {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖ ≤ ‖WithLp.toLp 2 x‖ ∧ ‖WithLp.toLp 2 x‖ ≤ √n * ‖x‖ := by
  constructor
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
      simpa using PiLp.norm_apply_le (WithLp.toLp 2 x) i
  · rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg n)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖(WithLp.toLp 2 x) i‖ ^ 2 ≤ ∑ _i : Fin n, ‖x‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (by simpa using norm_le_pi_norm x i) 2
      _ = n * ‖x‖ ^ 2 := by simp

include 𝕜 in
/-- **The infinite cube is not the infinite ball, up to any bounded distortion.** No additive map `T` from the
cube's space `ℓ^∞(ℕ)` into an inner product space satisfies `c‖x‖ ≤ ‖T x‖ ≤ C‖x‖` with `c > 0`. -/
theorem infCube_not_ball (T : lp (fun _ : ℕ => ℝ) ∞ →+ E) {c C : ℝ} (hc : 0 < c)
    (hlow : ∀ x, c * ‖x‖ ≤ ‖T x‖) (hup : ∀ x, ‖T x‖ ≤ C * ‖x‖) : False := by
  classical
  have he : ∀ i : ℕ, ‖lp.single (E := fun _ : ℕ => ℝ) ∞ i (1 : ℝ)‖ = 1 := fun i => by
    rw [lp.norm_single (by simp), norm_one]
  have hC0 : 0 ≤ C := by
    have := hup (lp.single (E := fun _ : ℕ => ℝ) ∞ 0 1)
    rw [he, mul_one] at this
    exact (norm_nonneg _).trans this
  have key : ∀ n : ℕ, (n : ℝ) * c ^ 2 ≤ C ^ 2 := by
    intro n
    have := card_mul_sq_le_of_signs (𝕜 := 𝕜) (Finset.range n)
      (fun i => T (lp.single (E := fun _ : ℕ => ℝ) ∞ i 1)) hc.le
      (fun i _ => by simpa [he] using hlow (lp.single (E := fun _ : ℕ => ℝ) ∞ i 1)) fun ε hε => by
        have hsum : ∑ i ∈ Finset.range n, ε i • T (lp.single (E := fun _ : ℕ => ℝ) ∞ i (1 : ℝ)) =
            T (∑ i ∈ Finset.range n, lp.single (E := fun _ : ℕ => ℝ) ∞ i ((ε i : ℤ) : ℝ)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← map_zsmul, ← lp.singleAddMonoidHom_apply, ← lp.singleAddMonoidHom_apply, ← map_zsmul,
            zsmul_eq_mul, mul_one]
        have hvec : ‖∑ i ∈ Finset.range n, lp.single (E := fun _ : ℕ => ℝ) ∞ i ((ε i : ℤ) : ℝ)‖ ≤ 1 := by
          refine lp.norm_le_of_forall_le zero_le_one fun j => ?_
          rw [lp.coeFn_sum, Finset.sum_apply]
          simp only [lp.coeFn_single, Pi.single_apply]
          rw [Finset.sum_ite_eq]
          split_ifs
          · rcases hε j with h | h <;> simp [h]
          · simp
        rw [hsum]
        calc ‖T _‖ ≤ C * ‖∑ i ∈ Finset.range n, lp.single (E := fun _ : ℕ => ℝ) ∞ i ((ε i : ℤ) : ℝ)‖ := hup _
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left hvec hC0
          _ = C := mul_one C
    simpa using this
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2 / c ^ 2)
  rw [div_lt_iff₀ (by positivity)] at hn
  linarith [key n]

include 𝕜 in
/-- In particular no isomorphism of normed spaces (continuous linear equivalence) identifies `ℓ^∞(ℕ)` with an
inner product space. -/
theorem not_continuousLinearEquiv [NormedSpace ℝ E] (e : lp (fun _ : ℕ => ℝ) ∞ ≃L[ℝ] E) : False := by
  set x₀ : lp (fun _ : ℕ => ℝ) ∞ := lp.single ∞ 0 1
  have hx₀ : ‖x₀‖ = 1 := by rw [lp.norm_single (by simp), norm_one]
  have hs : 0 < ‖(e.symm : E →L[ℝ] lp (fun _ : ℕ => ℝ) ∞)‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have h1 : e.symm (e x₀) = x₀ := e.symm_apply_apply x₀
    have h2 : (e.symm : E →L[ℝ] lp (fun _ : ℕ => ℝ) ∞) (e x₀) = 0 := by rw [h]; rfl
    rw [ContinuousLinearEquiv.coe_coe, h1] at h2
    rw [h2, norm_zero] at hx₀
    exact zero_ne_one hx₀
  refine infCube_not_ball (𝕜 := 𝕜) (e : lp (fun _ : ℕ => ℝ) ∞ →L[ℝ] E).toLinearMap.toAddMonoidHom
    (inv_pos.2 hs) (C := ‖(e : lp (fun _ : ℕ => ℝ) ∞ →L[ℝ] E)‖) (fun x => ?_) fun x => ?_
  · have := (e.symm : E →L[ℝ] lp (fun _ : ℕ => ℝ) ∞).le_opNorm (e x)
    rw [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] at this
    rw [inv_mul_le_iff₀ hs]
    exact this
  · exact (e : lp (fun _ : ℕ => ℝ) ∞ →L[ℝ] E).le_opNorm x

end Distortion

/-! ## Part C: the Euclidean ball's share of the cube -/

/-- The Euclidean unit ball of `ℝⁿ`, as a subset of the cube's space, lies inside the cube `(−1, 1)ⁿ`. -/
theorem ball_subset_cube (n : ℕ) :
    {x : Fin n → ℝ | ‖WithLp.toLp 2 x‖ < 1} ⊆ ball (0 : Fin n → ℝ) 1 := fun x hx => by
  rw [mem_ball, dist_zero_right]
  exact (euclidean_sandwich x).1.trans_lt hx

/-- Its volume is that of the unit ball of `EuclideanSpace ℝ (Fin n)`. -/
theorem volume_euclideanBall (n : ℕ) :
    volume {x : Fin n → ℝ | ‖WithLp.toLp 2 x‖ < 1} =
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have h : {x : Fin n → ℝ | ‖WithLp.toLp 2 x‖ < 1} =
      (WithLp.toLp 2) ⁻¹' ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    ext x; simp
  rw [h, (PiLp.volume_preserving_toLp (Fin n)).measure_preimage measurableSet_ball.nullMeasurableSet]

/-- **The Euclidean ball's share of the cube tends to `0`**: by Mathlib's volume formulas the ratio is
`π^{n/2}/(Γ(n/2 + 1) 2ⁿ)`, at most `(√π/2)ⁿ` for `n ≥ 2`. -/
theorem tendsto_ball_div_cube :
    Tendsto (fun n : ℕ => (volume {x : Fin n → ℝ | ‖WithLp.toLp 2 x‖ < 1}).toReal /
      (volume (ball (0 : Fin n → ℝ) 1)).toReal) atTop (𝓝 0) := by
  have hq : √Real.pi / 2 < 1 := by
    rw [div_lt_one two_pos, Real.sqrt_lt' two_pos]
    linarith [Real.pi_lt_four]
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [volume_euclideanBall, EuclideanSpace.volume_ball, Real.volume_pi_ball _ one_pos]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin, mul_one]
  have hG : 1 ≤ Real.Gamma (n / 2 + 1) := by
    have := Real.Gamma_strictMonoOn_Ici.monotoneOn (a := 2) (b := n / 2 + 1) (by simp)
      (by simp only [Set.mem_Ici]; have : (2 : ℝ) ≤ n := by exact_mod_cast hn
          linarith) (by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                        linarith)
    rwa [Real.Gamma_two] at this
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), div_pow]
  gcongr ?_ / _
  exact div_le_self (by positivity) hG

/-! ## Part D: the Bohr lift in the cube and in the ball -/

/-- `z(s)` is a bounded sequence, a point of the infinite cube's space `ℓ^∞(primes)`, if and only if
`Re s ≥ 0`. -/
theorem memℓp_top_bohr_iff (s : ℂ) : Memℓp (bohr s) ∞ ↔ 0 ≤ s.re := by
  rw [memℓp_infty_iff]
  constructor
  · rintro ⟨B, hB⟩
    by_contra h'
    have h : s.re < 0 := lt_of_not_ge h'
    set a := -s.re with ha
    have ha0 : 0 < a := by linarith
    have hpB : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ a ≤ B := fun p => by
      have h1 : ‖bohr s p‖ ≤ B := hB ⟨p, rfl⟩
      rwa [norm_bohr] at h1
    have hB0 : 0 ≤ B := le_trans (by positivity) (hpB ⟨2, Nat.prime_two⟩)
    obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (⌈B ^ a⁻¹⌉₊ + 1)
    have h1 : B ^ a⁻¹ < (p : ℝ) := by
      calc B ^ a⁻¹ ≤ ⌈B ^ a⁻¹⌉₊ := Nat.le_ceil _
        _ < ⌈B ^ a⁻¹⌉₊ + 1 := by linarith
        _ ≤ p := by exact_mod_cast hp_ge
    have h2 : (B ^ a⁻¹) ^ a < (p : ℝ) ^ a := Real.rpow_lt_rpow (by positivity) h1 ha0
    rw [Real.rpow_inv_rpow hB0 ha0.ne'] at h2
    exact absurd (hpB ⟨p, hp⟩) (not_le.2 h2)
  · intro h
    refine ⟨1, ?_⟩
    rintro _ ⟨p, rfl⟩
    change ‖bohr s p‖ ≤ 1
    rw [norm_bohr]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.prop.one_lt.le) (by linarith)

/-- The point `z(s)` of the infinite cube's space `ℓ^∞(primes)`, for `Re s ≥ 0`. -/
noncomputable def zCube (s : ℂ) (hs : 0 ≤ s.re) : lp (fun _ : Nat.Primes => ℂ) ∞ :=
  ⟨bohr s, (memℓp_top_bohr_iff s).2 hs⟩

/-- **The sup norm of `z(s)` is `2^{−Re s}`**, attained at the prime `2`. -/
theorem norm_zCube {s : ℂ} (hs : 0 ≤ s.re) : ‖zCube s hs‖ = 2 ^ (-s.re) := by
  apply le_antisymm
  · refine lp.norm_le_of_forall_le (by positivity) fun p => ?_
    change ‖bohr s p‖ ≤ _
    rw [norm_bohr]
    exact Real.rpow_le_rpow_of_nonpos two_pos (by exact_mod_cast p.prop.two_le) (by linarith)
  · let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
    have h := lp.norm_apply_le_norm (by simp) (zCube s hs) p₂
    have h2 : ‖(zCube s hs) p₂‖ = 2 ^ (-s.re) := by
      change ‖bohr s p₂‖ = _
      rw [norm_bohr]
      norm_num [p₂]
    rwa [h2] at h

/-- **The cube's surface is the line `Re s = 0`**: for `Re s ≥ 0`, `‖z(s)‖_∞ = 1` if and only if `Re s = 0`. -/
theorem norm_zCube_eq_one_iff {s : ℂ} (hs : 0 ≤ s.re) : ‖zCube s hs‖ = 1 ↔ s.re = 0 := by
  rw [norm_zCube hs]
  constructor
  · intro h
    by_contra hne
    have hneg : -s.re < 0 := by
      rcases lt_or_eq_of_le hs with h' | h'
      · linarith
      · exact absurd h'.symm hne
    exact (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hneg).ne h
  · intro h
    rw [h, neg_zero, Real.rpow_zero]

/-- **The critical line lies strictly inside the infinite cube, and outside `ℓ²`.** For `Re s = ½`, `z(s)` is a
point of `ℓ^∞` with sup norm `2^{−1/2} < 1`, and it is not a point of `ℓ²` (round 391's `memℓp_two_bohr_iff`). -/
theorem line_inside_cube_not_in_ell2 {s : ℂ} (hs : s.re = 1 / 2) :
    ‖zCube s (by rw [hs]; norm_num)‖ < 1 ∧ ¬ Memℓp (bohr s) 2 := by
  refine ⟨?_, ?_⟩
  · rw [norm_zCube, hs]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  · rw [memℓp_two_bohr_iff, hs]
    exact lt_irrefl _

/-! ## The normalised sphere for every `ℓ^r` norm -/

/-- The Bohr vector of `s` over a finite set `F` of primes, in `ℂ^F` with the `ℓ^r` norm: for `r = 2` the
Euclidean norm of round 391, for `r = ∞` the sup norm, whose unit ball is the cube. -/
noncomputable def zLp (r : ℝ≥0∞) (F : Finset Nat.Primes) (s : ℂ) : PiLp r (fun _ : F => ℂ) :=
  WithLp.toLp r fun p => bohr s p

/-- The `ℓ^r` norm is monotone in the coordinate norms. -/
lemma norm_piLp_le_of_forall {r : ℝ≥0∞} [Fact (1 ≤ r)] {ι : Type*} [Fintype ι]
    {x y : PiLp r (fun _ : ι => ℂ)} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases r.dichotomy with rfl | hr
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ciSup_mono (Set.finite_range _).bddAbove h
  · have hr0 : 0 < r.toReal := by linarith
    rw [PiLp.norm_eq_sum hr0, PiLp.norm_eq_sum hr0]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hr0.le) (by positivity)

lemma norm_zLp_apply (r : ℝ≥0∞) (F : Finset Nat.Primes) (s : ℂ) (p : F) :
    ‖zLp r F s p‖ = ((p : Nat.Primes) : ℕ) ^ (-s.re) := by
  simp [zLp, norm_bohr]

/-- `‖z_F(s)‖_r` depends only on `Re s`. -/
theorem norm_zLp_eq_of_re_eq (r : ℝ≥0∞) [Fact (1 ≤ r)] (F : Finset Nat.Primes) {s s' : ℂ} (h : s.re = s'.re) :
    ‖zLp r F s‖ = ‖zLp r F s'‖ :=
  le_antisymm (norm_piLp_le_of_forall fun p => by rw [norm_zLp_apply, norm_zLp_apply, h])
    (norm_piLp_le_of_forall fun p => by rw [norm_zLp_apply, norm_zLp_apply, h])

lemma norm_zLp_pos (r : ℝ≥0∞) [Fact (1 ≤ r)] {F : Finset Nat.Primes} (hF : F.Nonempty) (s : ℂ) :
    0 < ‖zLp r F s‖ := by
  obtain ⟨p, hp⟩ := hF
  have h := PiLp.norm_apply_le (zLp r F s) ⟨p, hp⟩
  rw [norm_zLp_apply] at h
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _) h

/-- `‖z_F(s)‖_r` is strictly decreasing in `Re s`. -/
theorem norm_zLp_lt_of_re_lt (r : ℝ≥0∞) [Fact (1 ≤ r)] {F : Finset Nat.Primes} (hF : F.Nonempty)
    {s s' : ℂ} (h : s.re < s'.re) : ‖zLp r F s'‖ < ‖zLp r F s‖ := by
  set d := s'.re - s.re with hd_def
  have hd : 0 < d := by linarith
  have hle : ‖zLp r F s'‖ ≤ ‖((2 : ℝ) ^ (-d)) • zLp r F s‖ := norm_piLp_le_of_forall fun p => by
    rw [PiLp.smul_apply, norm_smul, norm_zLp_apply, norm_zLp_apply,
      Real.norm_of_nonneg (by positivity)]
    have hp : (0 : ℝ) < ((p : Nat.Primes) : ℕ) := by exact_mod_cast (p : Nat.Primes).prop.pos
    have h2 : (((p : Nat.Primes) : ℕ) : ℝ) ^ (-d) ≤ (2 : ℝ) ^ (-d) :=
      Real.rpow_le_rpow_of_nonpos two_pos (by exact_mod_cast (p : Nat.Primes).prop.two_le) (by linarith)
    calc (((p : Nat.Primes) : ℕ) : ℝ) ^ (-s'.re)
        = (((p : Nat.Primes) : ℕ) : ℝ) ^ (-d) * (((p : Nat.Primes) : ℕ) : ℝ) ^ (-s.re) := by
          rw [← Real.rpow_add hp]; congr 1; rw [hd_def]; ring
      _ ≤ (2 : ℝ) ^ (-d) * (((p : Nat.Primes) : ℕ) : ℝ) ^ (-s.re) := by gcongr
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hle
  have h1 : (2 : ℝ) ^ (-d) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hpos := norm_zLp_pos r hF s
  nlinarith

/-- The Bohr vector normalised to `ℓ^r` norm `1` at `s = ½`. -/
noncomputable def vLp (r : ℝ≥0∞) (F : Finset Nat.Primes) (s : ℂ) : PiLp r (fun _ : F => ℂ) :=
  (‖zLp r F (1 / 2)‖⁻¹ : ℝ) • zLp r F s

/-- **For every `ℓ^r` norm, `1 ≤ r ≤ ∞`, the cube's included, the normalised Bohr vector lies on the unit sphere if
and only if `Re s = ½`.** -/
theorem vLp_mem_sphere_iff (r : ℝ≥0∞) [Fact (1 ≤ r)] {F : Finset Nat.Primes} (hF : F.Nonempty) (s : ℂ) :
    vLp r F s ∈ sphere 0 1 ↔ s.re = 1 / 2 := by
  have hpos := norm_zLp_pos r hF (1 / 2)
  rw [mem_sphere_zero_iff_norm, vLp, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le),
    inv_mul_eq_one₀ hpos.ne']
  have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := norm_zLp_lt_of_re_lt r hF (s := s) (s' := 1 / 2) (by rw [hhalf]; exact hlt)
      linarith
    · have := norm_zLp_lt_of_re_lt r hF (s := 1 / 2) (s' := s) (by rw [hhalf]; exact hgt)
      linarith
  · intro h
    exact norm_zLp_eq_of_re_eq r F (by rw [hhalf, h])

/-! ## Part E: the topological sense -/

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

/-- The `n`-th unit vector of `ℓ²(ℕ)`. -/
noncomputable def ellUnit (n : ℕ) : ℓ² := lp.single 2 n 1

lemma norm_ellUnit (n : ℕ) : ‖ellUnit n‖ = 1 := by
  rw [ellUnit, lp.norm_single (by simp), norm_one]

lemma inner_ellUnit_left (n : ℕ) (y : ℓ²) : inner ℂ (ellUnit n) y = y n := by
  rw [ellUnit, lp.inner_single_left]
  simp

lemma inner_ellUnit_right (x : ℓ²) (n : ℕ) : inner ℂ x (ellUnit n) = (starRingEnd ℂ) (x n) := by
  rw [ellUnit, lp.inner_single_right]
  simp

/-- The coordinates of a point of `ℓ²` tend to `0`. -/
lemma tendsto_ell2_apply_zero (y : ℓ²) : Tendsto (fun n => y n) atTop (𝓝 0) := by
  have hs : Summable fun n => ‖y n‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by simp)).1 (lp.memℓp y)
  have h0 := hs.tendsto_atTop_zero
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h0
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 := h0.sqrt
  simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at h1
  exact h1

/-- **In infinite dimension every point of the closed unit ball is a weak limit of points of the unit sphere.**
For `x ∈ ℓ²(ℕ)` with `‖x‖ ≤ 1` there are unit vectors `u_n` with `⟪u_n, y⟫ → ⟪x, y⟫` for every `y`: take
`u_n = x + t_n e_n` with `t_n ≥ 0` chosen so that `‖u_n‖ = 1`. -/
theorem exists_unit_seq_tendsto_inner (x : ℓ²) (hx : ‖x‖ ≤ 1) :
    ∃ u : ℕ → ℓ², (∀ n, ‖u n‖ = 1) ∧ ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y)) := by
  set a : ℕ → ℝ := fun n => (x n).re with ha
  have hrad : ∀ n, 0 ≤ a n ^ 2 + (1 - ‖x‖ ^ 2) := fun n => by nlinarith [norm_nonneg x]
  set t : ℕ → ℝ := fun n => -a n + √(a n ^ 2 + (1 - ‖x‖ ^ 2)) with ht
  have hsq : ∀ n, (t n + a n) ^ 2 = a n ^ 2 + (1 - ‖x‖ ^ 2) := fun n => by
    simp only [ht, neg_add_cancel_comm]
    exact Real.sq_sqrt (hrad n)
  have hxn : ∀ n, |a n| ≤ 1 := fun n =>
    ((RCLike.abs_re_le_norm (x n)).trans (lp.norm_apply_le_norm (by simp) x n)).trans hx
  have ht0 : ∀ n, 0 ≤ t n := fun n => by
    have : |a n| ≤ √(a n ^ 2 + (1 - ‖x‖ ^ 2)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
    simp only [ht]
    linarith [le_abs_self (a n)]
  have ht3 : ∀ n, t n ≤ 3 := fun n => by
    have h1 : √(a n ^ 2 + (1 - ‖x‖ ^ 2)) ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [abs_le.1 (hxn n), norm_nonneg x])
    simp only [ht]
    linarith [abs_le.1 (hxn n)]
  refine ⟨fun n => x + ((t n : ℝ) : ℂ) • ellUnit n, fun n => ?_, fun y => ?_⟩
  · have h := norm_add_sq (𝕜 := ℂ) x (((t n : ℝ) : ℂ) • ellUnit n)
    rw [inner_smul_right, inner_ellUnit_right, norm_smul, norm_ellUnit, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (ht0 n)] at h
    have hre : RCLike.re (((t n : ℝ) : ℂ) * (starRingEnd ℂ) (x n)) = t n * a n := by
      simp [ha]
    rw [hre] at h
    have h1 : ‖x + ((t n : ℝ) : ℂ) • ellUnit n‖ ^ 2 = 1 := by rw [h]; nlinarith [hsq n]
    have h2 := norm_nonneg (x + ((t n : ℝ) : ℂ) • ellUnit n)
    nlinarith [h1, h2]
  · have hsplit : ∀ n, inner ℂ (x + ((t n : ℝ) : ℂ) • ellUnit n) y = inner ℂ x y + (t n : ℂ) * y n := by
      intro n
      rw [inner_add_left, inner_smul_left, inner_ellUnit_left, Complex.conj_ofReal]
    simp_rw [hsplit]
    rw [show 𝓝 (inner ℂ x y) = 𝓝 (inner ℂ x y + 0) by rw [add_zero]]
    refine tendsto_const_nhds.add ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n => 3 * ‖y n‖) (fun n => norm_nonneg _) (fun n => ?_) ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ht0 n)]
      exact mul_le_mul_of_nonneg_right (ht3 n) (norm_nonneg _)
    · have := ((tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_ell2_apply_zero y)).const_mul 3)
      simpa using this

/-- **The norm is not weakly continuous**: the unit vectors `e_n` lie on the sphere and converge weakly to the
centre, `⟪e_n, y⟫ → 0` for every `y`. -/
theorem tendsto_inner_ellUnit (y : ℓ²) : Tendsto (fun n => inner ℂ (ellUnit n) y) atTop (𝓝 0) := by
  simp_rw [inner_ellUnit_left]
  exact tendsto_ell2_apply_zero y

lemma dist_ellUnit {m n : ℕ} (h : m ≠ n) : dist (ellUnit m) (ellUnit n) = √2 := by
  rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), norm_sub_sq (𝕜 := ℂ), norm_ellUnit, norm_ellUnit,
    inner_ellUnit_left]
  simp [ellUnit, h]
  norm_num

/-- **In the norm topology the infinite ball is not compact**: the unit vectors are pairwise at distance `√2`. -/
theorem not_isCompact_closedBall_ell2 : ¬ IsCompact (closedBall (0 : ℓ²) 1) := by
  intro hK
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := ellUnit) fun n => by
    rw [mem_closedBall, dist_zero_right, norm_ellUnit]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (1 / 2) (by norm_num)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (by omega)
  have h3 : dist (ellUnit (φ N)) (ellUnit (φ (N + 1))) < 1 := by
    calc _ ≤ dist (ellUnit (φ N)) a + dist a (ellUnit (φ (N + 1))) := dist_triangle _ _ _
      _ < 1 / 2 + 1 / 2 := by
        rw [dist_comm a]
        exact add_lt_add h1 h2
      _ = 1 := by norm_num
  rw [dist_ellUnit (hφ.injective.ne (by omega))] at h3
  have : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- The cube `[−1, 1]^ℕ` with the product topology (the Hilbert cube) is compact (Tychonoff). -/
theorem isCompact_hilbertCube : IsCompact (Set.pi Set.univ fun _ : ℕ => Set.Icc (-1 : ℝ) 1) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- **So, with the norm topology, the infinite ball is not homeomorphic to the Hilbert cube.** -/
theorem isEmpty_homeomorph_ball_hilbertCube :
    IsEmpty (closedBall (0 : ℓ²) 1 ≃ₜ Set.pi Set.univ fun _ : ℕ => Set.Icc (-1 : ℝ) 1) := by
  refine ⟨fun h => not_isCompact_closedBall_ell2 ?_⟩
  have : CompactSpace (Set.pi Set.univ fun _ : ℕ => Set.Icc (-1 : ℝ) 1) :=
    isCompact_iff_compactSpace.1 isCompact_hilbertCube
  have : CompactSpace (closedBall (0 : ℓ²) 1) := h.symm.compactSpace
  exact isCompact_iff_compactSpace.2 this

end CubeBall

#print axioms CubeBall.sub_eq_sub_of_dist_eq_half
#print axioms CubeBall.eq_of_midpoints_inner
#print axioms CubeBall.norm_vec2
#print axioms CubeBall.no_isometry_square
#print axioms CubeBall.no_isometry_of_square
#print axioms CubeBall.sqInf_apply
#print axioms CubeBall.norm_sqInf
#print axioms CubeBall.sqInf_sub
#print axioms CubeBall.no_isometry_infCube
#print axioms CubeBall.norm_sqFin
#print axioms CubeBall.sqFin_sub
#print axioms CubeBall.no_isometry_cube
#print axioms CubeBall.not_isometry_infCube
#print axioms CubeBall.exists_signs_sum_sq_le
#print axioms CubeBall.card_mul_sq_le_of_signs
#print axioms CubeBall.cube_distortion
#print axioms CubeBall.euclidean_sandwich
#print axioms CubeBall.infCube_not_ball
#print axioms CubeBall.not_continuousLinearEquiv
#print axioms CubeBall.ball_subset_cube
#print axioms CubeBall.volume_euclideanBall
#print axioms CubeBall.tendsto_ball_div_cube
#print axioms CubeBall.memℓp_top_bohr_iff
#print axioms CubeBall.norm_zCube
#print axioms CubeBall.norm_zCube_eq_one_iff
#print axioms CubeBall.line_inside_cube_not_in_ell2
#print axioms CubeBall.norm_piLp_le_of_forall
#print axioms CubeBall.norm_zLp_apply
#print axioms CubeBall.norm_zLp_eq_of_re_eq
#print axioms CubeBall.norm_zLp_pos
#print axioms CubeBall.norm_zLp_lt_of_re_lt
#print axioms CubeBall.vLp_mem_sphere_iff
#print axioms CubeBall.norm_ellUnit
#print axioms CubeBall.inner_ellUnit_left
#print axioms CubeBall.inner_ellUnit_right
#print axioms CubeBall.tendsto_ell2_apply_zero
#print axioms CubeBall.exists_unit_seq_tendsto_inner
#print axioms CubeBall.tendsto_inner_ellUnit
#print axioms CubeBall.dist_ellUnit
#print axioms CubeBall.not_isCompact_closedBall_ell2
#print axioms CubeBall.isCompact_hilbertCube
#print axioms CubeBall.isEmpty_homeomorph_ball_hilbertCube
