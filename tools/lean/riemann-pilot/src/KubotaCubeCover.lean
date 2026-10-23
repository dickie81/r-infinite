import KubotaCubeDecomp

/-! # The cover of level `p³` (round 447)

S5f-12 of round 360's plan, part 8. Round 446's next step planned the cover and the traces for round 439's
`translates_eq_zero`, applied to `D = N(p)⁻³Σ_{q mod p³} θ̃∘M_q − N(p)⁻¹θ̃`. That theorem takes a group
`H ≤ Γ_1(3)` and, for each translate `g`, a group `H′ ≤ Γ_1(3)` of finite index with an equivalence
`e : H ≃ H′` such that `e(γ)·(g·P) = g·(γ·P)` and `κ(e(γ)) = κ(γ)`. This round supplies them, for `p ≠ 0`,
with `H = Γ(3p³)`; the translates are `I`, with `H′ = H`, and the `M_q`, with `H′ = Γ′(p)`:

* **Principal congruence subgroups** (`gamPrin`, a definition, and `gamPrin_normal`, an instance;
  **`finiteIndex_gamPrin`**, with `mem_gamPrin`, `mem_gamPrin_iff`, `gamPrin_le_Gam3` and
  `finite_quot_gamPrin`): `Γ(N)`, the kernel of reduction modulo `N`, is normal in `SL_2(ℤ[ω])`, lies in
  `Γ_1(3)` for `3 ∣ N` and has finite index for `N ≠ 0`.
* **The twisted group** (`gamTw`, a definition; **`finiteIndex_gamTw`**, with `gamTw_le_Gam3`,
  `gamPrin_le_gamTw` and `finite_quot_gamTw`): `Γ′(p)`, the matrices `(a, b; c, d)` with
  `a ≡ d ≡ 1 (mod 3p³)`, `3 ∣ b` and `3p⁶ ∣ c`, is a subgroup of `Γ_1(3)` containing `Γ(3p⁶)`, so of finite
  index.
* **The twist** (`dvdQuo`, `twistM`, `untwistM` and `twistEquiv`, definitions, with `dvdQuo_spec`,
  `dvdQuo_mul`, `det_twistM`, `det_untwistM`, `untwistM_twistM`, `twistM_untwistM`, `twistM_mem` and
  `untwistM_mem`): `(a, b; c, d) ↦ (a, b/p³; cp³, d)` is an equivalence `Γ(3p³) ≃ Γ′(p)`, with inverse
  `(a, b; c, d) ↦ (a, bp³; c/p³, d)`.
* **The equivalences `γ ↦ M_qγM_q⁻¹`** (`conjPrin` and `cubeEquiv`, definitions; **`slAct_cubeEquiv`** and
  **`kub_cubeEquiv`**, with `twistM_mul_cubeMat`, `cubeMat_eq_mul`, `slAct_twistM` and `kubC_mul_pow_three`):
  `M_q = M_0·T_{3q}` with `M_0 = diag(ρ⁻¹, ρ)` (round 446's `cubeMat`), conjugation by `M_0` is the twist, and
  conjugation by `T_{3q}` preserves `Γ(3p³)`. So `e_q(γ) = M_qγM_q⁻¹` maps `Γ(3p³)` onto `Γ′(p)`, with
  `e_q(γ)·(M_q·P) = M_q·(γ·P)`. It preserves `κ`: `κ(T_{3q}γT_{3q}⁻¹) = κ(γ)` (round 382's `kub_mul_Gam3`,
  round 426's `kub_slT`), and `(cp³/a)₃ = (c/a)₃` (round 362's `cub_pow_three`).
-/

open Ideal NumberField MeasureTheory
open scoped BigOperators MatrixGroups

noncomputable section

namespace Eis

/-! ### Principal congruence subgroups -/

/-- **`Γ(N)`**: the kernel of reduction modulo `N` on `SL_2(ℤ[ω])`. -/
def gamPrin (N : 𝓞 K) : Subgroup SL(2, 𝓞 K) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (span {N}))).ker

/-- `Γ(N)` is normal in `SL_2(ℤ[ω])`, as a kernel. -/
instance gamPrin_normal (N : 𝓞 K) : (gamPrin N).Normal := MonoidHom.normal_ker _

/-- Membership in `Γ(N)`: every entry of `γ − I` is divisible by `N`. -/
theorem mem_gamPrin {N : 𝓞 K} {γ : SL(2, 𝓞 K)} :
    γ ∈ gamPrin N ↔
      ∀ i j, N ∣ (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j - (1 : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j := by
  rw [gamPrin, MonoidHom.mem_ker, Matrix.SpecialLinearGroup.ext_iff]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one]
  refine forall₂_congr fun i j => ?_
  have key : (1 : Matrix (Fin 2) (Fin 2) (𝓞 K ⧸ span {N})) i j =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j) := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [key, Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- Membership in `Γ(N)`, entry by entry. -/
theorem mem_gamPrin_iff {N : 𝓞 K} {γ : SL(2, 𝓞 K)} :
    γ ∈ gamPrin N ↔ N ∣ γ 0 0 - 1 ∧ N ∣ γ 0 1 ∧ N ∣ γ 1 0 ∧ N ∣ γ 1 1 - 1 := by
  rw [mem_gamPrin]
  constructor
  · intro h
    exact ⟨by simpa using h 0 0, by simpa using h 0 1, by simpa using h 1 0, by simpa using h 1 1⟩
  · rintro ⟨h00, h01, h10, h11⟩ i j
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11

/-- `Γ(N) ≤ Γ_1(3)` for `3 ∣ N`. -/
theorem gamPrin_le_Gam3 {N : 𝓞 K} (h : (3 : 𝓞 K) ∣ N) : gamPrin N ≤ Gam3 := fun _ hγ =>
  mem_Gam3.2 fun i j => h.trans (mem_gamPrin.1 hγ i j)

/-- **`Γ(N)` has finite index** for `N ≠ 0`, as the kernel of reduction to the finite group `SL_2(ℤ[ω]/N)`. -/
theorem finiteIndex_gamPrin {N : 𝓞 K} (hN : N ≠ 0) : (gamPrin N).FiniteIndex := by
  have := finite_quot N hN
  unfold gamPrin
  infer_instance

/-! ### The twisted group -/

/-- **`Γ′(p)`**: the matrices `(a, b; c, d)` with `a ≡ d ≡ 1 (mod 3p³)`, `3 ∣ b` and `3p⁶ ∣ c`. -/
def gamTw (p : 𝓞 K) : Subgroup SL(2, 𝓞 K) where
  carrier := {γ | 3 * p ^ 3 ∣ γ 0 0 - 1 ∧ 3 ∣ γ 0 1 ∧ 3 * p ^ 6 ∣ γ 1 0 ∧ 3 * p ^ 3 ∣ γ 1 1 - 1}
  mul_mem' := by
    rintro γ γ' ⟨a1, b1, c1, d1⟩ ⟨a2, b2, c2, d2⟩
    have h63 : 3 * p ^ 3 ∣ 3 * p ^ 6 := ⟨p ^ 3, by ring⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e : γ 0 0 * γ' 0 0 + γ 0 1 * γ' 1 0 - 1 =
          (γ 0 0 - 1) * (γ' 0 0 - 1) + (γ 0 0 - 1) + (γ' 0 0 - 1) + γ 0 1 * γ' 1 0 := by ring
      rw [e]
      exact dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_left a1 _) a1) a2)
        (dvd_mul_of_dvd_right (h63.trans c2) _)
    · exact dvd_add (dvd_mul_of_dvd_right b2 _) (dvd_mul_of_dvd_left b1 _)
    · exact dvd_add (dvd_mul_of_dvd_left c1 _) (dvd_mul_of_dvd_right c2 _)
    · have e : γ 1 0 * γ' 0 1 + γ 1 1 * γ' 1 1 - 1 =
          γ 1 0 * γ' 0 1 + ((γ 1 1 - 1) * (γ' 1 1 - 1) + (γ 1 1 - 1) + (γ' 1 1 - 1)) := by ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_left (h63.trans c1) _)
        (dvd_add (dvd_add (dvd_mul_of_dvd_left d1 _) d1) d2)
  one_mem' := by simp
  inv_mem' := by
    rintro γ ⟨a1, b1, c1, d1⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ⟨d1, (dvd_neg).2 b1, (dvd_neg).2 c1, a1⟩

/-- `Γ′(p) ≤ Γ_1(3)`. -/
theorem gamTw_le_Gam3 (p : 𝓞 K) : gamTw p ≤ Gam3 := by
  rintro γ ⟨a1, b1, c1, d1⟩
  rw [mem_Gam3]
  refine fun i j => ?_
  have h3 : ∀ x : 𝓞 K, (3 : 𝓞 K) ∣ 3 * x := fun x => dvd_mul_right 3 x
  fin_cases i <;> fin_cases j
  · simpa using (h3 _).trans a1
  · simpa using b1
  · simpa using (h3 _).trans c1
  · simpa using (h3 _).trans d1

/-- `Γ(3p⁶) ≤ Γ′(p)`. -/
theorem gamPrin_le_gamTw (p : 𝓞 K) : gamPrin (3 * p ^ 6) ≤ gamTw p := by
  intro γ hγ
  obtain ⟨a1, b1, c1, d1⟩ := mem_gamPrin_iff.1 hγ
  have h63 : 3 * p ^ 3 ∣ 3 * p ^ 6 := ⟨p ^ 3, by ring⟩
  exact ⟨h63.trans a1, (dvd_mul_right 3 _).trans b1, c1, h63.trans d1⟩

/-- **`Γ′(p)` has finite index** for `p ≠ 0`, since it contains `Γ(3p⁶)`. -/
theorem finiteIndex_gamTw {p : 𝓞 K} (hp : p ≠ 0) : (gamTw p).FiniteIndex := by
  have h3 : (3 : 𝓞 K) ≠ 0 := fun h => by
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have := finiteIndex_gamPrin (mul_ne_zero h3 (pow_ne_zero 6 hp))
  exact Subgroup.finiteIndex_of_le (gamPrin_le_gamTw p)

/-! ### The twist -/

open Classical in
/-- The quotient `x/m` when `m ∣ x`, and `0` otherwise. -/
def dvdQuo (m x : 𝓞 K) : 𝓞 K := if h : m ∣ x then h.choose else 0

/-- `x = m·(x/m)` for `m ∣ x`. -/
theorem dvdQuo_spec {m x : 𝓞 K} (h : m ∣ x) : x = m * dvdQuo m x := by
  unfold dvdQuo
  simp only [h, dite_true]
  exact h.choose_spec

/-- `(my)/m = y` for `m ≠ 0`. -/
theorem dvdQuo_mul {m : 𝓞 K} (hm : m ≠ 0) (y : 𝓞 K) : dvdQuo m (m * y) = y :=
  mul_left_cancel₀ hm (dvdQuo_spec (dvd_mul_right m y)).symm

/-- **The twist** `(a, b; c, d) ↦ (a, b/p³; cp³, d)`. -/
def twistM (p : 𝓞 K) (A : Matrix (Fin 2) (Fin 2) (𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K) :=
  !![A 0 0, dvdQuo (p ^ 3) (A 0 1); A 1 0 * p ^ 3, A 1 1]

/-- **The inverse twist** `(a, b; c, d) ↦ (a, bp³; c/p³, d)`. -/
def untwistM (p : 𝓞 K) (A : Matrix (Fin 2) (Fin 2) (𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K) :=
  !![A 0 0, A 0 1 * p ^ 3; dvdQuo (p ^ 3) (A 1 0), A 1 1]

/-- The twist of a matrix of determinant `1` with `p³ ∣ b` has determinant `1`. -/
theorem det_twistM {p : 𝓞 K} {A : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hA : A.det = 1) (h : p ^ 3 ∣ A 0 1) :
    (twistM p A).det = 1 := by
  rw [Matrix.det_fin_two] at hA
  rw [twistM, Matrix.det_fin_two_of]
  linear_combination hA + A 1 0 * dvdQuo_spec h

/-- The inverse twist of a matrix of determinant `1` with `p³ ∣ c` has determinant `1`. -/
theorem det_untwistM {p : 𝓞 K} {A : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hA : A.det = 1) (h : p ^ 3 ∣ A 1 0) :
    (untwistM p A).det = 1 := by
  rw [Matrix.det_fin_two] at hA
  rw [untwistM, Matrix.det_fin_two_of]
  linear_combination hA + A 0 1 * dvdQuo_spec h

/-- The inverse twist undoes the twist, for `p³ ∣ b`. -/
theorem untwistM_twistM {p : 𝓞 K} (hp : p ≠ 0) {A : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : p ^ 3 ∣ A 0 1) :
    untwistM p (twistM p A) = A := by
  have e1 : dvdQuo (p ^ 3) (A 0 1) * p ^ 3 = A 0 1 := (mul_comm _ _).trans (dvdQuo_spec h).symm
  have e2 : dvdQuo (p ^ 3) (A 1 0 * p ^ 3) = A 1 0 := by rw [mul_comm, dvdQuo_mul (pow_ne_zero 3 hp)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistM, untwistM, e1, e2]

/-- The twist undoes the inverse twist, for `p³ ∣ c`. -/
theorem twistM_untwistM {p : 𝓞 K} (hp : p ≠ 0) {A : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : p ^ 3 ∣ A 1 0) :
    twistM p (untwistM p A) = A := by
  have e1 : dvdQuo (p ^ 3) (A 0 1 * p ^ 3) = A 0 1 := by rw [mul_comm, dvdQuo_mul (pow_ne_zero 3 hp)]
  have e2 : dvdQuo (p ^ 3) (A 1 0) * p ^ 3 = A 1 0 := (mul_comm _ _).trans (dvdQuo_spec h).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistM, untwistM, e1, e2]

/-- The twist of a matrix `≡ I (mod 3p³)` satisfies the congruences of `Γ′(p)`. -/
theorem twistM_mem {p : 𝓞 K} (hp : p ≠ 0) {A : Matrix (Fin 2) (Fin 2) (𝓞 K)} (a1 : 3 * p ^ 3 ∣ A 0 0 - 1)
    (b1 : 3 * p ^ 3 ∣ A 0 1) (c1 : 3 * p ^ 3 ∣ A 1 0) (d1 : 3 * p ^ 3 ∣ A 1 1 - 1) :
    3 * p ^ 3 ∣ twistM p A 0 0 - 1 ∧ 3 ∣ twistM p A 0 1 ∧ 3 * p ^ 6 ∣ twistM p A 1 0 ∧
      3 * p ^ 3 ∣ twistM p A 1 1 - 1 := by
  obtain ⟨k, hk⟩ := b1
  obtain ⟨j, hj⟩ := c1
  refine ⟨by simpa [twistM] using a1, ⟨k, ?_⟩, ⟨j, ?_⟩, by simpa [twistM] using d1⟩
  · simp only [twistM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hk, show 3 * p ^ 3 * k = p ^ 3 * (3 * k) by ring, dvdQuo_mul (pow_ne_zero 3 hp)]
  · simp only [twistM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hj]
    ring

/-- The inverse twist of a matrix with the congruences of `Γ′(p)` is `≡ I (mod 3p³)`. -/
theorem untwistM_mem {p : 𝓞 K} (hp : p ≠ 0) {A : Matrix (Fin 2) (Fin 2) (𝓞 K)} (a1 : 3 * p ^ 3 ∣ A 0 0 - 1)
    (b1 : 3 ∣ A 0 1) (c1 : 3 * p ^ 6 ∣ A 1 0) (d1 : 3 * p ^ 3 ∣ A 1 1 - 1) :
    3 * p ^ 3 ∣ untwistM p A 0 0 - 1 ∧ 3 * p ^ 3 ∣ untwistM p A 0 1 ∧ 3 * p ^ 3 ∣ untwistM p A 1 0 ∧
      3 * p ^ 3 ∣ untwistM p A 1 1 - 1 := by
  obtain ⟨k, hk⟩ := b1
  obtain ⟨j, hj⟩ := c1
  refine ⟨by simpa [untwistM] using a1, ⟨k, ?_⟩, ⟨j, ?_⟩, by simpa [untwistM] using d1⟩
  · simp only [untwistM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hk]
    ring
  · simp only [untwistM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hj, show 3 * p ^ 6 * j = p ^ 3 * (3 * p ^ 3 * j) by ring, dvdQuo_mul (pow_ne_zero 3 hp)]

/-- **The twist as an equivalence** `Γ(3p³) ≃ Γ′(p)`. -/
def twistEquiv {p : 𝓞 K} (hp : p ≠ 0) : gamPrin (3 * p ^ 3) ≃ gamTw p where
  toFun γ := ⟨⟨twistM p γ.1.1, det_twistM γ.1.2 ((dvd_mul_left _ 3).trans (mem_gamPrin_iff.1 γ.2).2.1)⟩, by
    obtain ⟨a1, b1, c1, d1⟩ := mem_gamPrin_iff.1 γ.2
    exact twistM_mem hp a1 b1 c1 d1⟩
  invFun γ := ⟨⟨untwistM p γ.1.1, det_untwistM γ.1.2
      (dvd_trans (Dvd.intro (3 * p ^ 3) (by ring)) γ.2.2.2.1)⟩, by
    obtain ⟨a1, b1, c1, d1⟩ := γ.2
    exact mem_gamPrin_iff.2 (untwistM_mem hp a1 b1 c1 d1)⟩
  left_inv γ := Subtype.ext (Subtype.ext
    (untwistM_twistM hp ((dvd_mul_left _ 3).trans (mem_gamPrin_iff.1 γ.2).2.1)))
  right_inv γ := Subtype.ext (Subtype.ext
    (twistM_untwistM hp (dvd_trans (Dvd.intro (3 * p ^ 3) (by ring)) γ.2.2.2.1)))

/-! ### The equivalences `γ ↦ M_qγM_q⁻¹` -/

/-- Conjugation by `g ∈ SL_2(ℤ[ω])`, as a permutation of `Γ(N)`. -/
def conjPrin (g : SL(2, 𝓞 K)) (N : 𝓞 K) : gamPrin N ≃ gamPrin N where
  toFun γ := ⟨g * γ * g⁻¹, (gamPrin_normal N).conj_mem _ γ.2 g⟩
  invFun γ := ⟨g⁻¹ * γ * g, by simpa using (gamPrin_normal N).conj_mem _ γ.2 g⁻¹⟩
  left_inv γ := Subtype.ext (by simp [mul_assoc])
  right_inv γ := Subtype.ext (by simp [mul_assoc])

/-- **`γ ↦ M_qγM_q⁻¹`** from `Γ(3p³)` onto `Γ′(p)`: conjugation by the translation `T_{3q}`, then the twist.
-/
def cubeEquiv {p : 𝓞 K} (hp : p ≠ 0) (q : 𝓞 K) : gamPrin (3 * p ^ 3) ≃ gamTw p :=
  (conjPrin (slT (3 * q)) _).trans (twistEquiv hp)

/-- `M_0 = diag(ρ⁻¹, ρ)` intertwines a matrix and its twist. -/
theorem twistM_mul_cubeMat {p : 𝓞 K} (hp : p ≠ 0) {A : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : p ^ 3 ∣ A 0 1) :
    (twistM p A).map σO * cubeMat p 0 = cubeMat p 0 * A.map σO := by
  have hρ := cubeRho_ne_zero hp
  have e0 : σO (A 0 1) = cubeRho p ^ 2 * σO (dvdQuo (p ^ 3) (A 0 1)) := by
    rw [cubeRho_sq, ← map_pow, ← map_mul, ← dvdQuo_spec h]
  have e : σ (algebraMap (𝓞 K) K (A 0 1)) =
      cubeRho p ^ 2 * σ (algebraMap (𝓞 K) K (dvdQuo (p ^ 3) (A 0 1))) := e0
  have e' : σ (algebraMap (𝓞 K) K p) ^ 3 = cubeRho p ^ 2 := (cubeRho_sq p).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistM, cubeMat, Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · rw [e]
    field_simp
  · rw [e']
    field_simp
  · ring

/-- `M_q = M_0·T_{3q}`. -/
theorem cubeMat_eq_mul (p q : 𝓞 K) :
    cubeMat p q = cubeMat p 0 * ((slT (3 * q) : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeMat, slT, Matrix.mul_apply, Fin.sum_univ_two]

/-- The twist of `η` acts on `M_0·Q` as `M_0·η` acts on `Q`. -/
theorem slAct_twistM {p : 𝓞 K} (hp : p ≠ 0) {η η' : SL(2, 𝓞 K)}
    (h : p ^ 3 ∣ (η : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 1)
    (he : (η' : Matrix (Fin 2) (Fin 2) (𝓞 K)) = twistM p η) {Q : ℂ × ℝ} (hQ : Q ∈ UHS) :
    slAct η' (actP (cubeMat p 0) Q) = actP (cubeMat p 0) (slAct η Q) := by
  unfold slAct
  rw [he, ← actP_mul (det_map_σO (det_twistM η.2 h)) (det_cubeMat hp 0) hQ, twistM_mul_cubeMat hp h,
    actP_mul (det_cubeMat hp 0) (det_map_σO η.2) hQ]

/-- **The intertwining**: `(M_qγM_q⁻¹)·(M_q·P) = M_q·(γ·P)`. -/
theorem slAct_cubeEquiv {p : 𝓞 K} (hp : p ≠ 0) (q : 𝓞 K) (γ : gamPrin (3 * p ^ 3)) {P : ℂ × ℝ}
    (hP : P ∈ UHS) :
    slAct (cubeEquiv hp q γ : SL(2, 𝓞 K)) (actP (cubeMat p q) P) =
      actP (cubeMat p q) (slAct (γ : SL(2, 𝓞 K)) P) := by
  set T : SL(2, 𝓞 K) := slT (3 * q) with hT
  have hη : T * (γ : SL(2, 𝓞 K)) * T⁻¹ ∈ gamPrin (3 * p ^ 3) := (gamPrin_normal _).conj_mem _ γ.2 T
  have h01 : p ^ 3 ∣ ((T * (γ : SL(2, 𝓞 K)) * T⁻¹ : SL(2, 𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 1 :=
    (dvd_mul_left _ 3).trans (mem_gamPrin_iff.1 hη).2.1
  have e1 : ∀ Q ∈ UHS, actP (cubeMat p q) Q = actP (cubeMat p 0) (slAct T Q) := fun Q hQ => by
    rw [cubeMat_eq_mul, actP_mul (det_cubeMat hp 0) (det_map_σO T.2) hQ]
    rfl
  rw [e1 P hP, e1 _ (slAct_mem _ hP), slAct_twistM hp h01 rfl (slAct_mem _ hP), ← slAct_mul _ _ hP,
    ← slAct_mul _ _ hP]
  congr 2
  group

/-- `(cp³/a)₃ = (c/a)₃` for `a` primary and prime to `p`. -/
theorem kubC_mul_pow_three {p a : 𝓞 K} (hp : p ≠ 0) (ha : Primary a) (hpa : IsCoprime p a) (c : 𝓞 K) :
    kubC a (c * p ^ 3) = kubC a c := by
  by_cases hc : c = 0
  · simp [kubC, hc]
  have hc3 : c * p ^ 3 ≠ 0 := mul_ne_zero hc (pow_ne_zero 3 hp)
  simp only [kubC, hc, hc3, ↓reduceIte]
  rw [cub_mul_left, cub_pow_left ha, cub_pow_three ha hpa, mul_one]

/-- **`κ` is preserved**: `κ(M_qγM_q⁻¹) = κ(γ)` on `Γ(3p³)`, since `(cp³/a)₃ = (c/a)₃`. -/
theorem kub_cubeEquiv {p : 𝓞 K} (hp : p ≠ 0) (q : 𝓞 K) (γ : gamPrin (3 * p ^ 3)) :
    kub ↑(cubeEquiv hp q γ : SL(2, 𝓞 K)) = kub ↑(γ : SL(2, 𝓞 K)) := by
  set T : SL(2, 𝓞 K) := slT (3 * q) with hT
  have hη : T * (γ : SL(2, 𝓞 K)) * T⁻¹ ∈ gamPrin (3 * p ^ 3) := (gamPrin_normal _).conj_mem _ γ.2 T
  obtain ⟨a1, -, -, -⟩ := mem_gamPrin_iff.1 hη
  set η : SL(2, 𝓞 K) := T * (γ : SL(2, 𝓞 K)) * T⁻¹ with hηdef
  have ha : Primary ((η : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0) := (dvd_mul_right 3 _).trans a1
  obtain ⟨k, hk⟩ := a1
  have hpa : IsCoprime p ((η : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0) :=
    ⟨-(3 * p ^ 2 * k), 1, by linear_combination hk⟩
  have hT3 : T ∈ Gam3 := slT_mem_Gam3 (dvd_mul_right 3 q)
  have hγ3 : (γ : SL(2, 𝓞 K)) ∈ Gam3 := gamPrin_le_Gam3 (dvd_mul_right 3 _) γ.2
  have e1 : kub ↑(cubeEquiv hp q γ : SL(2, 𝓞 K)) = kub ↑η := by
    show kub (twistM p η) = kub ↑η
    rw [kub_eq_kubC, kub_eq_kubC]
    simp only [twistM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact kubC_mul_pow_three hp ha hpa _
  rw [e1, hηdef, kub_mul_Gam3 (mul_mem hT3 hγ3) (inv_mem hT3), kub_mul_Gam3 hT3 hγ3, hT, slT_inv, kub_slT,
    kub_slT, one_mul, mul_one]

/-- `Γ(3p³)` has finitely many cosets in `Γ_1(3)`. -/
theorem finite_quot_gamPrin {p : 𝓞 K} (hp : p ≠ 0) :
    Finite (Gam3 ⧸ (gamPrin (3 * p ^ 3)).subgroupOf Gam3) := by
  have h3 : (3 : 𝓞 K) ≠ 0 := fun h => by
    have := congrArg σO h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  have := finiteIndex_gamPrin (mul_ne_zero h3 (pow_ne_zero 3 hp))
  infer_instance

/-- `Γ′(p)` has finitely many cosets in `Γ_1(3)`. -/
theorem finite_quot_gamTw {p : 𝓞 K} (hp : p ≠ 0) : Finite (Gam3 ⧸ (gamTw p).subgroupOf Gam3) := by
  have := finiteIndex_gamTw hp
  infer_instance

end Eis

end

#print axioms Eis.mem_gamPrin
#print axioms Eis.mem_gamPrin_iff
#print axioms Eis.gamPrin_le_Gam3
#print axioms Eis.finiteIndex_gamPrin
#print axioms Eis.gamTw_le_Gam3
#print axioms Eis.gamPrin_le_gamTw
#print axioms Eis.finiteIndex_gamTw
#print axioms Eis.dvdQuo_spec
#print axioms Eis.dvdQuo_mul
#print axioms Eis.det_twistM
#print axioms Eis.det_untwistM
#print axioms Eis.untwistM_twistM
#print axioms Eis.twistM_untwistM
#print axioms Eis.twistM_mem
#print axioms Eis.untwistM_mem
#print axioms Eis.twistM_mul_cubeMat
#print axioms Eis.cubeMat_eq_mul
#print axioms Eis.slAct_twistM
#print axioms Eis.slAct_cubeEquiv
#print axioms Eis.kubC_mul_pow_three
#print axioms Eis.kub_cubeEquiv
#print axioms Eis.finite_quot_gamPrin
#print axioms Eis.finite_quot_gamTw
