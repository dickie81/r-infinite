import KubotaCubeSum

/-! # The decomposition of the cube translates (round 446)

S5f-12 of round 360's plan, part 7. Round 445's next step planned the decomposition `M_rγ = γ_rβ_r` and the
constant terms of the traces. For a primary prime `p`, `M_r = (ρ⁻¹, ρ⁻¹σ(3r); 0, ρ)` with `ρ² = σ(p)³` acts by
`(z, v) ↦ ((z + 3r)/p³, v/|p|³)` (the release's `cubeAverageMatrix`). Round 439's `translates_eq_zero` needs
the constant term of the trace of `D∘g⁻¹` for each translate `g`, so for the inverses `M_r⁻¹` too. This round
writes `M_r·γ` and `M_r⁻¹·γ`, for `γ ∈ Γ_1(3)`, as an element of `Γ_1(3)` times an upper triangular matrix,
and proves that the means over `3P` of `D∘γ` and of `D∘M_r⁻¹∘γ` along `z ↦ μz + t` vanish under the conditions
below, for `D = N(p)⁻³Σ_{q mod p³} θ̃∘M_q − N(p)⁻¹θ̃`:

* **Upper triangular matrices** (**`actP_of_lower_zero`**, with `uhsAct_upper_inv`): a matrix `β` of
  determinant `1` with `β₁₀ = 0` acts by `(z, v) ↦ (β₀₀²z + β₀₀β₀₁, |β₀₀|²v)`.
* **The matrices `M_r`** (`cubeRho` and `cubeMat`, definitions; **`actP_cubeMat`**, with `cubeRho_sq`,
  `cubeRho_ne_zero`, `normSq_cubeRho`, `det_cubeMat`, `cubeMat_inv`, `cubeMat_mul_apply_zero`,
  `cubeMat_mul_apply_one`, `cubeMat_inv_mul_apply_zero` and `cubeMat_inv_mul_apply_one`).
* **A matrix of `Γ_1(3)` with a given first column** (`colMat`, a definition; **`colMat_mem_Gam3`**, with
  `colMat_col`): for `ua + wc = 1`, `(a, w(a − 1); c, u + wc)` has determinant `1`. It lies in `Γ_1(3)` for
  `a` primary and `3 ∣ c`, since `u + wc − 1 = −u(a − 1)` (round 370's `modThree_of`).
* **Decomposition through a first column** (**`decomp_col`** and **`slAct_decomp`**, with `cubeL_sq` and
  `normSq_cubeL`): if the first column of `X·γ` is `l` times that of `γ′`, then `γ′⁻¹Xγ` has determinant `1`,
  lower left entry `0` and top left entry `l`, so `X·(γ·P) = γ′·(l²z + t, |l|²v)` for some `t` (round 383's
  `actP_mul`).
* **The two decompositions** (**`cubeMat_slAct`** and **`cubeMat_inv_slAct`**): for `γ ∈ Γ_1(3)` with first
  column `(a, c)`, the first column of `M_r·γ` is `ρ⁻¹p^k·((a + 3rc)/p^k, cp^{3−k})`, with `p^k` the greatest
  common divisor of `a + 3rc` and `p³`, and that of `M_r⁻¹·γ` is `ρ⁻¹p^m·(p^{3−m}a − 3(c/p^m)r, c/p^m)`, with
  `p^m` the greatest common divisor of `c` and `p³`. Both columns are coprime pairs `≡ (1, 0) (mod 3)`, so
  they complete to elements of `Γ_1(3)`, and `l² = p^{2k−3}` (resp. `p^{2m−3}`). The first one's `κ` times
  `w_k` is round 445's `cubeTerm`.
* **The affine means** (`thetaCT` and `cubeDiff`, definitions; **`integral_cubeDiff_slAct`** and
  **`integral_cubeDiff_inv_slAct`**, with `integral_thetaF_affine`): for `γ ∈ Γ_1(3)`, `μ ∈ ℤ[ω]` nonzero with
  `p³ ∣ μ` (resp. `p⁶ ∣ μ`), `t ∈ ℂ` and `w > 0` such that θ̃ has its constant term (round 433) at the heights
  that occur, `∫_{3P} D(γ·(μz + t, w)) dz = 0` (resp. `∫_{3P} D(M_r⁻¹·γ·(μz + t, w)) dz = 0`). Each `θ̃∘M_q∘γ`
  is `κ(γ_q)·θ̃` along an affine image of `3P` (round 425's `isAut_thetaF`), whose mean is θ̃'s constant term
  (round 437's `thetaF_add_period`, round 444's `integral_fundP3_affine`). So the mean of the `q`-th term is
  round 445's `cubeTerm` times `thetaCT w`, and round 445's `tsum_cubeTerm_gam3` sums these to
  `N(p)²·κ(γ)·thetaCT w`. For `M_r⁻¹·γ` the second decomposition reduces the mean to the first case at `γ″`.
-/

open Ideal NumberField MeasureTheory
open scoped BigOperators MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Upper triangular matrices -/

/-- `(a, b; 0, a⁻¹)` acts by `(z, v) ↦ (a²z + ab, |a|²v)`. -/
theorem uhsAct_upper_inv {a : ℂ} (ha : a ≠ 0) (b z : ℂ) (v : ℝ) :
    uhsAct !![a, b; 0, a⁻¹] z v = (a ^ 2 * z + a * b, Complex.normSq a * v) := by
  have hn : Complex.normSq a ≠ 0 := (Complex.normSq_pos.2 ha).ne'
  have hc : conj a ≠ 0 := (map_ne_zero _).2 ha
  simp only [uhsAct, uhsZ, uhsV, uhsDen, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, zero_add, add_zero,
    mul_zero, map_zero, map_inv₀]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Complex.ofReal_inv, Complex.normSq_eq_conj_mul_self]
    field_simp
  · simp only
    field_simp

/-- A matrix of determinant `1` with `β₁₀ = 0` acts by `(z, v) ↦ (β₀₀²z + β₀₀β₀₁, |β₀₀|²v)`. -/
theorem actP_of_lower_zero {β : Matrix (Fin 2) (Fin 2) ℂ} (hβ : β.det = 1) (h10 : β 1 0 = 0) (p : ℂ × ℝ) :
    actP β p = (β 0 0 ^ 2 * p.1 + β 0 0 * β 0 1, Complex.normSq (β 0 0) * p.2) := by
  have hd := det_two_eq_one β hβ
  rw [h10, mul_zero, sub_zero] at hd
  have h0 : β 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have h11 : β 1 1 = (β 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hd
  have e : β = !![β 0 0, β 0 1; 0, (β 0 0)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h11]
  unfold actP
  conv_lhs => rw [e]
  exact uhsAct_upper_inv h0 _ _ _

/-! ### The matrices `M_r` -/

/-- `ρ = σ(p)·σ(p)^{1/2}`, a square root of `σ(p)³`. -/
def cubeRho (p : 𝓞 K) : ℂ := σO p * σO p ^ (2⁻¹ : ℂ)

/-- `ρ² = σ(p)³`. -/
theorem cubeRho_sq (p : 𝓞 K) : cubeRho p ^ 2 = σO p ^ 3 := by
  unfold cubeRho
  rw [mul_pow, Complex.cpow_ofNat_inv_pow]
  ring

/-- `ρ ≠ 0` for `p ≠ 0`. -/
theorem cubeRho_ne_zero {p : 𝓞 K} (hp : p ≠ 0) : cubeRho p ≠ 0 := by
  intro h
  have := cubeRho_sq p
  rw [h, zero_pow two_ne_zero] at this
  exact pow_ne_zero 3 (σO_ne_zero hp) this.symm

/-- `|ρ|² = |p|³`. -/
theorem normSq_cubeRho (p : 𝓞 K) : Complex.normSq (cubeRho p) = ‖σO p‖ ^ 3 := by
  rw [Complex.normSq_eq_norm_sq, ← norm_pow, cubeRho_sq, norm_pow]

/-- **The matrix `M_r`** (the release's `cubeAverageMatrix`): `(ρ⁻¹, ρ⁻¹σ(3r); 0, ρ)`. -/
def cubeMat (p r : 𝓞 K) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(cubeRho p)⁻¹, (cubeRho p)⁻¹ * σO (3 * r); 0, cubeRho p]

/-- `M_r` has determinant `1`. -/
theorem det_cubeMat {p : 𝓞 K} (hp : p ≠ 0) (r : 𝓞 K) : (cubeMat p r).det = 1 := by
  rw [cubeMat, Matrix.det_fin_two_of, mul_zero, sub_zero, inv_mul_cancel₀ (cubeRho_ne_zero hp)]

/-- **`M_r` acts by `(z, v) ↦ ((z + 3r)/p³, v/|p|³)`.** -/
theorem actP_cubeMat {p : 𝓞 K} (hp : p ≠ 0) (r : 𝓞 K) (P : ℂ × ℝ) :
    actP (cubeMat p r) P = ((P.1 + σO (3 * r)) / σO p ^ 3, P.2 / ‖σO p‖ ^ 3) := by
  have hρ := cubeRho_ne_zero hp
  rw [actP_of_lower_zero (det_cubeMat hp r) (by simp [cubeMat])]
  simp only [cubeMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  refine Prod.ext ?_ ?_
  · simp only
    rw [← cubeRho_sq]
    field_simp
  · simp only
    rw [map_inv₀, normSq_cubeRho]
    field_simp

/-! ### A matrix of `Γ_1(3)` with a given first column -/

/-- **The completion of a column**: for `ua + wc = 1`, `(a, w(a − 1); c, u + wc)`. -/
def colMat (a c : 𝓞 K) (h : IsCoprime a c) : SL(2, 𝓞 K) :=
  ⟨!![a, h.choose_spec.choose * (a - 1); c, h.choose + h.choose_spec.choose * c], by
    rw [Matrix.det_fin_two_of]
    linear_combination h.choose_spec.choose_spec⟩

/-- The first column of the completion is `(a, c)`. -/
theorem colMat_col (a c : 𝓞 K) (h : IsCoprime a c) :
    (colMat a c h : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0 = a ∧
      (colMat a c h : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = c := by
  simp [colMat]

/-- **The completion lies in `Γ_1(3)`** for `a` primary and `3 ∣ c`. -/
theorem colMat_mem_Gam3 {a c : 𝓞 K} (ha : Primary a) (hc : (3 : 𝓞 K) ∣ c) (h : IsCoprime a c) :
    colMat a c h ∈ Gam3 := by
  rw [mem_Gam3]
  have hs := h.choose_spec.choose_spec
  refine modThree_of ha (dvd_mul_of_dvd_right ha _) hc ?_
  have e : h.choose + h.choose_spec.choose * c - 1 = -(h.choose * (a - 1)) := by
    linear_combination hs
  rw [e]
  exact (dvd_mul_of_dvd_right ha _).neg_right

/-! ### Decomposition through a first column -/

/-- **Decomposition through a first column**: if the first column of `X` (of determinant `1`) is `l` times
the first column of `γ`, then `β = γ⁻¹X` has determinant `1`, `β₁₀ = 0` and `β₀₀ = l`, and
`X·P = γ·(β·P)`. -/
theorem decomp_col {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.det = 1) (γ : SL(2, 𝓞 K)) {l : ℂ}
    (h0 : X 0 0 = l * σO ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0))
    (h1 : X 1 0 = l * σO ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0)) :
    (((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)⁻¹ * X).det = 1 ∧
      (((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)⁻¹ * X) 1 0 = 0 ∧
      (((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)⁻¹ * X) 0 0 = l ∧
      ∀ P ∈ UHS, actP X P = slAct γ (actP (((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)⁻¹ * X) P) := by
  set G := (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO with hG
  have hGd : G.det = 1 := det_map_σO γ.2
  have hd := det_two_eq_one G hGd
  have hinv : G⁻¹ = !![G 1 1, -G 0 1; -G 1 0, G 0 0] := by
    rw [Matrix.inv_def, hGd, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  have hβd : (G⁻¹ * X).det = 1 := by rw [Matrix.det_mul, det_inv_eq_one hGd, hX, one_mul]
  refine ⟨hβd, ?_, ?_, fun P hP => ?_⟩
  · rw [hinv, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, h0, h1, hG, Matrix.map_apply]
    ring
  · rw [hinv, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, h0, h1]
    rw [show G 1 1 * (l * σO ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0)) +
        -G 0 1 * (l * σO ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0)) =
        l * (G 0 0 * G 1 1 - G 0 1 * G 1 0) by simp only [hG, Matrix.map_apply]; ring, hd, mul_one]
  · unfold slAct
    rw [← hG, ← actP_mul hGd hβd hP, ← mul_assoc, Matrix.mul_nonsing_inv _ (by rw [hGd]; exact isUnit_one),
      one_mul]

/-- **From a first-column decomposition to the action**: if the first column of `X·γ` is `l` times that of
`γ′`, then `X·(γ·P) = γ′·(l²z + t, |l|²v)` for some `t` and every `P = (z, v)` in upper half-space. -/
theorem slAct_decomp {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.det = 1) (γ γ' : SL(2, 𝓞 K)) {l : ℂ}
    (h0 : (X * (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) 0 0 =
      l * σO ((γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0))
    (h1 : (X * (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) 1 0 =
      l * σO ((γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0)) :
    ∃ t : ℂ, ∀ P ∈ UHS, actP X (slAct γ P) = slAct γ' (l ^ 2 * P.1 + t, Complex.normSq l * P.2) := by
  set G := (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO with hG
  have hGd : G.det = 1 := det_map_σO γ.2
  have hYd : (X * G).det = 1 := by rw [Matrix.det_mul, hX, hGd, one_mul]
  obtain ⟨hβd, hβ10, hβ00, hact⟩ := decomp_col hYd γ' h0 h1
  refine ⟨l * (((γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)⁻¹ * (X * G)) 0 1, fun P hP => ?_⟩
  have e1 : actP X (slAct γ P) = actP (X * G) P := by
    unfold slAct
    rw [← hG, actP_mul hX hGd hP]
  rw [e1, hact P hP, actP_of_lower_zero hβd hβ10, hβ00]

/-- `M_r⁻¹ = (ρ, −ρ⁻¹σ(3r); 0, ρ⁻¹)`. -/
theorem cubeMat_inv {p : 𝓞 K} (hp : p ≠ 0) (r : 𝓞 K) :
    (cubeMat p r)⁻¹ = !![cubeRho p, -((cubeRho p)⁻¹ * σO (3 * r)); 0, (cubeRho p)⁻¹] := by
  rw [Matrix.inv_def, det_cubeMat hp r, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeMat]

/-- The first column of `M_r·G`: `(ρ⁻¹σ(G₀₀ + 3G₁₀r), ρσ(G₁₀))`. -/
theorem cubeMat_mul_apply_zero (p r : 𝓞 K) (G : Matrix (Fin 2) (Fin 2) (𝓞 K)) :
    (cubeMat p r * G.map σO) 0 0 = (cubeRho p)⁻¹ * σO (G 0 0 + 3 * G 1 0 * r) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [cubeMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.map_apply, map_add, map_mul, map_ofNat]
  ring

/-- The lower left entry of `M_r·G`. -/
theorem cubeMat_mul_apply_one (p r : 𝓞 K) (G : Matrix (Fin 2) (Fin 2) (𝓞 K)) :
    (cubeMat p r * G.map σO) 1 0 = cubeRho p * σO (G 1 0) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [cubeMat]

/-- The first column of `M_r⁻¹·G`: `(ρ⁻¹σ(p³G₀₀ − 3G₁₀r), ρ⁻¹σ(G₁₀))`. -/
theorem cubeMat_inv_mul_apply_zero {p : 𝓞 K} (hp : p ≠ 0) (r : 𝓞 K) (G : Matrix (Fin 2) (Fin 2) (𝓞 K)) :
    ((cubeMat p r)⁻¹ * G.map σO) 0 0 = (cubeRho p)⁻¹ * σO (p ^ 3 * G 0 0 - 3 * G 1 0 * r) := by
  rw [cubeMat_inv hp, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.map_apply, map_sub, map_mul, map_pow, map_ofNat]
  rw [← cubeRho_sq]
  field_simp [cubeRho_ne_zero hp]
  ring

/-- The lower left entry of `M_r⁻¹·G`. -/
theorem cubeMat_inv_mul_apply_one {p : 𝓞 K} (hp : p ≠ 0) (r : 𝓞 K) (G : Matrix (Fin 2) (Fin 2) (𝓞 K)) :
    ((cubeMat p r)⁻¹ * G.map σO) 1 0 = (cubeRho p)⁻¹ * σO (G 1 0) := by
  rw [cubeMat_inv hp, Matrix.mul_apply, Fin.sum_univ_two]
  simp

/-- For `l = ρ⁻¹σ(p)^j`, `l² = σ(p)^{2j}/σ(p)³`. -/
theorem cubeL_sq (p : 𝓞 K) (j : ℕ) : ((cubeRho p)⁻¹ * σO p ^ j) ^ 2 = σO p ^ (2 * j) / σO p ^ 3 := by
  rw [mul_pow, inv_pow, cubeRho_sq, ← pow_mul, mul_comm j 2, div_eq_inv_mul]

/-- For `l = ρ⁻¹σ(p)^j`, `|l|² = |p|^{2j}/|p|³`. -/
theorem normSq_cubeL (p : 𝓞 K) (j : ℕ) :
    Complex.normSq ((cubeRho p)⁻¹ * σO p ^ j) = ‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 := by
  rw [map_mul, map_inv₀, normSq_cubeRho, map_pow, Complex.normSq_eq_norm_sq, ← pow_mul, div_eq_inv_mul]

/-- **The forward decomposition**: for `γ ∈ Γ_1(3)` with first column `(a, c)`, `x = a + 3cr` and `p^k` the
greatest common divisor of `x` and `p³`, `M_r·(γ·P) = γ_r·(p^{2k−3}z + t, |p|^{2k−3}v)` for some `t`, with
`γ_r ∈ Γ_1(3)` of first column `(x/p^k, cp^{3−k})`; so `κ(γ_r)·w_k` is round 445's `cubeTerm`. -/
theorem cubeMat_slAct {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3)
    (r : 𝓞 K) : ∃ γ' ∈ Gam3, kub ↑γ' * (cubeW p (ordP3 p (γ 0 0 + 3 * γ 1 0 * r)) : ℂ) =
        cubeTerm p (γ 0 0) (γ 1 0) r ∧
      ∃ t : ℂ, ∀ P ∈ UHS, actP (cubeMat p r) (slAct γ P) =
        slAct γ' (σO p ^ (2 * ordP3 p (γ 0 0 + 3 * γ 1 0 * r)) / σO p ^ 3 * P.1 + t,
          ‖σO p‖ ^ (2 * ordP3 p (γ 0 0 + 3 * γ 1 0 * r)) / ‖σO p‖ ^ 3 * P.2) := by
  have hp0 := hp.ne_zero
  have h3 := mem_Gam3.1 hγ
  have hdet := γ.2
  rw [Matrix.det_fin_two] at hdet
  have ha : Primary (γ 0 0) := by simpa [Primary] using h3 0 0
  have hc : (3 : 𝓞 K) ∣ γ 1 0 := by simpa using h3 1 0
  have hac : IsCoprime (γ 0 0) (γ 1 0) := ⟨γ 1 1, -γ 0 1, by linear_combination hdet⟩
  set a := γ 0 0 with ha_def
  set c := γ 1 0 with hc_def
  set x := a + 3 * c * r with hx
  set k := ordP3 p x with hk
  have hxk : x = p ^ k * quoP3 p x := quoP3_spec p x
  have hxp : Primary x := by
    have e : x - 1 = (a - 1) + 3 * (c * r) := by rw [hx]; ring
    unfold Primary
    rw [e]
    exact dvd_add ha (dvd_mul_right 3 _)
  have hxc : IsCoprime x c := by
    have h := hac.add_mul_left_left (3 * r)
    rwa [show a + c * (3 * r) = x by rw [hx]; ring] at h
  have hx'c : IsCoprime (quoP3 p x) c := by
    rw [hxk] at hxc
    exact hxc.of_mul_left_right
  have hx'pk : IsCoprime (quoP3 p x) (p ^ (3 - k)) := by
    rcases (ordP3_le p x).lt_or_eq with hlt | heq
    · exact (isCoprime_of_not_dvd hp (not_dvd_quoP3 hlt)).pow_right
    · rw [show k = 3 from heq, Nat.sub_self, pow_zero]
      exact isCoprime_one_right
  have hcop : IsCoprime (quoP3 p x) (c * p ^ (3 - k)) := hx'c.mul_right hx'pk
  refine ⟨colMat _ _ hcop, colMat_mem_Gam3 (primary_quoP3 hpp hxp) (dvd_mul_of_dvd_left hc _) hcop, ?_, ?_⟩
  · rw [kub_eq_kubC, (colMat_col _ _ hcop).1, (colMat_col _ _ hcop).2]
    rfl
  have hρ := cubeRho_ne_zero hp0
  have hk3 : k + (3 - k) = 3 := Nat.add_sub_cancel' (ordP3_le p x)
  have h0 : (cubeMat p r * (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) 0 0 = (cubeRho p)⁻¹ * σO p ^ k *
      σO ((colMat _ _ hcop : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0) := by
    have e : (cubeRho p)⁻¹ * σO p ^ k * σO (quoP3 p x) = (cubeRho p)⁻¹ * σO x := by
      rw [mul_assoc, ← map_pow, ← map_mul, ← hxk]
    rw [cubeMat_mul_apply_zero, (colMat_col _ _ hcop).1]
    refine Eq.trans ?_ e.symm
    rfl
  have h1 : (cubeMat p r * (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) 1 0 = (cubeRho p)⁻¹ * σO p ^ k *
      σO ((colMat _ _ hcop : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0) := by
    rw [cubeMat_mul_apply_one, (colMat_col _ _ hcop).2]
    show cubeRho p * σO c = _
    rw [map_mul, map_pow, show (cubeRho p)⁻¹ * σO p ^ k * (σO c * σO p ^ (3 - k)) =
        (cubeRho p)⁻¹ * σO p ^ (k + (3 - k)) * σO c by ring, hk3, ← cubeRho_sq]
    field_simp
  obtain ⟨t, ht⟩ := slAct_decomp (det_cubeMat hp0 r) γ (colMat _ _ hcop) h0 h1
  exact ⟨t, fun P hP => by rw [ht P hP, cubeL_sq, normSq_cubeL]⟩

/-- **The inverse decomposition**: for `γ ∈ Γ_1(3)` with first column `(a, c)` and `p^m` the greatest common
divisor of `c` and `p³`, `M_r⁻¹·(γ·P) = γ″·(p^{2m−3}z + t, |p|^{2m−3}v)` for some `t`, with `γ″ ∈ Γ_1(3)` of
first column `(p^{3−m}a − 3(c/p^m)r, c/p^m)`. -/
theorem cubeMat_inv_slAct {p : 𝓞 K} (hp : Prime p) (hpp : Primary p) {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3)
    (r : 𝓞 K) : ∃ γ' ∈ Gam3, ∃ t : ℂ, ∀ P ∈ UHS, actP (cubeMat p r)⁻¹ (slAct γ P) =
      slAct γ' (σO p ^ (2 * ordP3 p (γ 1 0)) / σO p ^ 3 * P.1 + t,
        ‖σO p‖ ^ (2 * ordP3 p (γ 1 0)) / ‖σO p‖ ^ 3 * P.2) := by
  have hp0 := hp.ne_zero
  have h3 := mem_Gam3.1 hγ
  have hdet := γ.2
  rw [Matrix.det_fin_two] at hdet
  have ha : Primary (γ 0 0) := by simpa [Primary] using h3 0 0
  have hc : (3 : 𝓞 K) ∣ γ 1 0 := by simpa using h3 1 0
  have huw : γ 1 1 * γ 0 0 + -γ 0 1 * γ 1 0 = 1 := by linear_combination hdet
  set a := γ 0 0 with ha_def
  set c := γ 1 0 with hc_def
  set m := ordP3 p c with hm
  have hcm : c = p ^ m * quoP3 p c := quoP3_spec p c
  have hm3 : m ≤ 3 := ordP3_le p c
  set c' := quoP3 p c with hc'
  set y' := p ^ (3 - m) * a - 3 * c' * r with hy'
  have hpm : p ^ m * p ^ (3 - m) = p ^ 3 := by rw [← pow_add, Nat.add_sub_cancel' hm3]
  have h3p : IsCoprime (3 : 𝓞 K) (p ^ m) :=
    (isCoprime_of_not_dvd hp fun h => three_not_mem_span hp hpp (Ideal.mem_span_singleton.2 h)).pow_right
  have hc'3 : (3 : 𝓞 K) ∣ c' := by
    rw [hcm] at hc
    exact h3p.dvd_of_dvd_mul_left hc
  have hy'p : Primary y' := by
    have h1 : Primary (p ^ (3 - m) * a) := (primary_pow hpp _).mul ha
    unfold Primary at h1 ⊢
    have e : y' - 1 = (p ^ (3 - m) * a - 1) - 3 * (c' * r) := by rw [hy']; ring
    rw [e]
    exact dvd_sub h1 (dvd_mul_right 3 _)
  have hz : IsCoprime (p ^ (3 - m)) c' := by
    rcases hm3.lt_or_eq with hlt | heq
    · exact (isCoprime_of_not_dvd hp (not_dvd_quoP3 hlt)).symm.pow_left
    · rw [heq, Nat.sub_self, pow_zero]
      exact isCoprime_one_left
  have hrel : γ 1 1 * y' + (3 * γ 1 1 * r + -γ 0 1 * (p ^ m * p ^ (3 - m))) * c' = p ^ (3 - m) := by
    apply mul_left_cancel₀ (pow_ne_zero m hp0)
    have e : γ 1 1 * a + -γ 0 1 * (p ^ m * c') = 1 := by rw [← hcm]; exact huw
    rw [hy']
    linear_combination (p ^ m * p ^ (3 - m)) * e
  have hcop : IsCoprime y' c' := by
    obtain ⟨s, t, hst⟩ := hz
    exact ⟨s * γ 1 1, s * (3 * γ 1 1 * r + -γ 0 1 * (p ^ m * p ^ (3 - m))) + t, by
      linear_combination s * hrel + hst⟩
  refine ⟨colMat _ _ hcop, colMat_mem_Gam3 hy'p hc'3 hcop, ?_⟩
  have hρ := cubeRho_ne_zero hp0
  have hy : p ^ m * y' = p ^ 3 * a - 3 * c * r := by
    rw [hy', hcm]
    linear_combination a * hpm
  have h0 : ((cubeMat p r)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) 0 0 = (cubeRho p)⁻¹ * σO p ^ m *
      σO ((colMat _ _ hcop : Matrix (Fin 2) (Fin 2) (𝓞 K)) 0 0) := by
    have e : (cubeRho p)⁻¹ * σO p ^ m * σO y' = (cubeRho p)⁻¹ * σO (p ^ 3 * a - 3 * c * r) := by
      rw [mul_assoc, ← map_pow, ← map_mul, hy]
    rw [cubeMat_inv_mul_apply_zero hp0, (colMat_col _ _ hcop).1]
    refine Eq.trans ?_ e.symm
    rfl
  have h1 : ((cubeMat p r)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) 1 0 = (cubeRho p)⁻¹ * σO p ^ m *
      σO ((colMat _ _ hcop : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0) := by
    have e : (cubeRho p)⁻¹ * σO p ^ m * σO c' = (cubeRho p)⁻¹ * σO c := by
      rw [mul_assoc, ← map_pow, ← map_mul, ← hcm]
    rw [cubeMat_inv_mul_apply_one hp0, (colMat_col _ _ hcop).2]
    refine Eq.trans ?_ e.symm
    rfl
  obtain ⟨t, ht⟩ := slAct_decomp (det_inv_eq_one (det_cubeMat hp0 r)) γ (colMat _ _ hcop) h0 h1
  exact ⟨t, fun P hP => by rw [ht P hP, cubeL_sq, normSq_cubeL]⟩

/-! ### The affine means of `D∘γ` -/

/-- θ's constant term at height `v`: `(9√3/2)·Res φ·v^{2/3}` (rounds 433 and 436). -/
def thetaCT (v : ℝ) : ℂ :=
  ((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (phiG (4 / 3) / 3) * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)

/-- **θ's mean along an affine image of `3P`**, at a height `w` where θ̃'s constant term is `thetaCT w`:
`∫_{3P} θ̃(μz + t, w) dz = thetaCT w` for `μ ∈ ℤ[ω]` nonzero and `t ∈ ℂ`. -/
theorem integral_thetaF_affine {r : ℝ} {Y : ℝ} (hY : 0 < Y) {w : ℝ} (hw : 0 < w)
    (hc : ∫ z in fundP3, thetaF r Y hY (z, w) = thetaCT w) {μ : 𝓞 K} (hμ : μ ≠ 0) (t : ℂ) :
    ∫ z in fundP3, thetaF r Y hY (σO μ * z + t, w) = thetaCT w := by
  have hm : Measurable fun z => thetaF r Y hY (z, w) :=
    (measurable_thetaF r Y hY).comp (measurable_id.prodMk measurable_const)
  have hi : IntegrableOn (fun z => thetaF r Y hY (z, w)) fundP3 :=
    Integrable.of_integral_ne_zero (by rw [hc]; exact const_theta_ne_zero hw)
  rw [integral_fundP3_affine (f := fun z => thetaF r Y hY (z, w)) hm
    (fun z u => thetaF_add_period r Y hY z u hw) hμ hi t, hc]

/-- **The cube difference** `D = N(p)⁻³ Σ_{q mod p³} θ̃∘M_q − N(p)⁻¹θ̃`. -/
def cubeDiff (r Y : ℝ) (hY : 0 < Y) (p : 𝓞 K) (P : ℂ × ℝ) : ℂ :=
  ((absNorm (span {p}) : ℂ) ^ 3)⁻¹ *
      ∑' q : 𝓞 K ⧸ span {p ^ 3}, thetaF r Y hY (actP (cubeMat p (repQ (p ^ 3) q)) P) -
    (absNorm (span {p}) : ℂ)⁻¹ * thetaF r Y hY P

/-- **The affine means of `D∘γ` vanish**: for `γ ∈ Γ_1(3)`, `μ ∈ ℤ[ω]` nonzero with `p³ ∣ μ`, `t ∈ ℂ` and a
height `w > 0` at which θ̃ has its constant term, and also at `|p|^{2k−3}w` for `k ≤ 3`,
`∫_{3P} D(γ·(μz + t, w)) dz = 0`. Each `θ̃∘M_q∘γ` is `κ(γ_q)·θ̃` along an affine image of `3P`
(`cubeMat_slAct`), so its mean is round 445's `cubeTerm` times `thetaCT w`, and round 445's
`tsum_cubeTerm_gam3` sums these to `N(p)²·κ(γ)·thetaCT w`. -/
theorem integral_cubeDiff_slAct {r : ℝ} {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) {μ : 𝓞 K} (hμ : μ ≠ 0) (hpμ : p ^ 3 ∣ μ) (t : ℂ) {w : ℝ} (hw : 0 < w)
    (hc0 : ∫ z in fundP3, thetaF r Y hY (z, w) = thetaCT w)
    (hc : ∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * w) =
      thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * w)) :
    ∫ z in fundP3, cubeDiff r Y hY p (slAct γ (σO μ * z + t, w)) = 0 := by
  classical
  have hp0 := hp.ne_zero
  have hσp : σO p ≠ 0 := σO_ne_zero hp0
  have hnp : 0 < ‖σO p‖ := norm_pos_iff.2 hσp
  obtain ⟨μ₀, rfl⟩ := hpμ
  have hμ₀ : μ₀ ≠ 0 := right_ne_zero_of_mul hμ
  have := finite_quot_pow3 hp0
  have := Fintype.ofFinite (𝓞 K ⧸ span {p ^ 3})
  have hN : (absNorm (span {p}) : ℂ) ≠ 0 := absNorm_span_ne_zero hp0
  have key : ∀ q : 𝓞 K ⧸ span {p ^ 3},
      Integrable (fun z => thetaF r Y hY (actP (cubeMat p (repQ (p ^ 3) q))
        (slAct γ (σO (p ^ 3 * μ₀) * z + t, w)))) (volume.restrict fundP3) ∧
      ∫ z in fundP3, thetaF r Y hY (actP (cubeMat p (repQ (p ^ 3) q))
        (slAct γ (σO (p ^ 3 * μ₀) * z + t, w))) =
        cubeTerm p (γ 0 0) (γ 1 0) (repQ (p ^ 3) q) * thetaCT w := by
    intro q
    obtain ⟨γ', hγ', hκ, t', hact⟩ := cubeMat_slAct hp hpp hγ (repQ (p ^ 3) q)
    set k := ordP3 p (γ 0 0 + 3 * γ 1 0 * repQ (p ^ 3) q) with hk
    have hk3 : k ≤ 3 := ordP3_le _ _
    have hh : 0 < ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 := by positivity
    have e : ∀ z : ℂ, thetaF r Y hY (actP (cubeMat p (repQ (p ^ 3) q))
        (slAct γ (σO (p ^ 3 * μ₀) * z + t, w))) =
        kub ↑γ' * thetaF r Y hY (σO (p ^ (2 * k) * μ₀) * z + (σO p ^ (2 * k) / σO p ^ 3 * t + t'),
          ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * w) := by
      intro z
      rw [hact _ hw, isAut_thetaF r Y hY γ' hγ' _ (show (0 : ℝ) < _ from mul_pos hh hw)]
      congr 2
      simp only [Prod.mk.injEq, and_true, map_mul, map_pow]
      field_simp
      ring
    have hint := integral_thetaF_affine hY (mul_pos hh hw) (hc k hk3)
      (mul_ne_zero (pow_ne_zero (2 * k) hp0) hμ₀)
      (σO p ^ (2 * k) / σO p ^ 3 * t + t')
    simp_rw [e]
    refine ⟨(Integrable.of_integral_ne_zero ?_).const_mul _, ?_⟩
    · rw [hint]
      exact const_theta_ne_zero (mul_pos hh hw)
    · rw [integral_const_mul, hint, ← hκ]
      unfold thetaCT cubeW
      rw [Real.mul_rpow hh.le hw.le]
      push_cast
      ring
  have e0 : ∀ z : ℂ, thetaF r Y hY (slAct γ (σO (p ^ 3 * μ₀) * z + t, w)) =
      kub ↑γ * thetaF r Y hY (σO (p ^ 3 * μ₀) * z + t, w) := fun z => isAut_thetaF r Y hY γ hγ _ hw
  have hint0 := integral_thetaF_affine hY hw hc0 hμ t
  have hi0 : Integrable (fun z => thetaF r Y hY (slAct γ (σO (p ^ 3 * μ₀) * z + t, w)))
      (volume.restrict fundP3) := by
    simp_rw [e0]
    exact (Integrable.of_integral_ne_zero (by rw [hint0]; exact const_theta_ne_zero hw)).const_mul _
  have hsum := tsum_cubeTerm_gam3 hp hpp hγ
  rw [tsum_fintype] at hsum
  unfold cubeDiff
  simp_rw [tsum_fintype]
  rw [integral_sub ((integrable_finsetSum _ fun q _ => (key q).1).const_mul _) (hi0.const_mul _),
    integral_const_mul, integral_finsetSum _ fun q _ => (key q).1, integral_const_mul]
  simp_rw [fun q => (key q).2, e0]
  rw [integral_const_mul, hint0, ← Finset.sum_mul, hsum]
  field_simp
  ring

/-- **The affine means of `D∘M_q⁻¹∘γ` vanish**: for `γ ∈ Γ_1(3)`, `μ ∈ ℤ[ω]` nonzero with `p⁶ ∣ μ`, `t ∈ ℂ`
and a height `w > 0` such that θ̃ has its constant term at `|p|^{2j−3}w` and at `|p|^{2k−3}|p|^{2j−3}w` for
`j, k ≤ 3`, `∫_{3P} D(M_q⁻¹·γ·(μz + t, w)) dz = 0`. By `cubeMat_inv_slAct`,
`M_q⁻¹·γ·(μz + t, w) = γ″·(μ′z + t′, |p|^{2m−3}w)` with `p³ ∣ μ′`, and `integral_cubeDiff_slAct` applies at
`γ″`. -/
theorem integral_cubeDiff_inv_slAct {r : ℝ} {Y : ℝ} (hY : 0 < Y) {p : 𝓞 K} (hp : Prime p) (hpp : Primary p)
    {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) (q : 𝓞 K) {μ : 𝓞 K} (hμ : μ ≠ 0) (hpμ : p ^ 6 ∣ μ) (t : ℂ) {w : ℝ}
    (hw : 0 < w)
    (hc0 : ∀ j ≤ 3, ∫ z in fundP3, thetaF r Y hY (z, ‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w) =
      thetaCT (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w))
    (hc : ∀ j ≤ 3, ∀ k ≤ 3, ∫ z in fundP3, thetaF r Y hY
        (z, ‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w)) =
      thetaCT (‖σO p‖ ^ (2 * k) / ‖σO p‖ ^ 3 * (‖σO p‖ ^ (2 * j) / ‖σO p‖ ^ 3 * w))) :
    ∫ z in fundP3, cubeDiff r Y hY p (actP (cubeMat p q)⁻¹ (slAct γ (σO μ * z + t, w))) = 0 := by
  have hp0 := hp.ne_zero
  have hσp : σO p ≠ 0 := σO_ne_zero hp0
  have hnp : 0 < ‖σO p‖ := norm_pos_iff.2 hσp
  obtain ⟨μ₁, rfl⟩ := hpμ
  have hμ₁ : μ₁ ≠ 0 := right_ne_zero_of_mul hμ
  obtain ⟨γ', hγ', t', hact⟩ := cubeMat_inv_slAct hp hpp hγ q
  set m := ordP3 p (γ 1 0) with hm
  have hm3 : m ≤ 3 := ordP3_le _ _
  have hh : 0 < ‖σO p‖ ^ (2 * m) / ‖σO p‖ ^ 3 := by positivity
  have e : ∀ z : ℂ, actP (cubeMat p q)⁻¹ (slAct γ (σO (p ^ 6 * μ₁) * z + t, w)) =
      slAct γ' (σO (p ^ (2 * m + 3) * μ₁) * z + (σO p ^ (2 * m) / σO p ^ 3 * t + t'),
        ‖σO p‖ ^ (2 * m) / ‖σO p‖ ^ 3 * w) := by
    intro z
    rw [hact _ hw]
    congr 1
    simp only [Prod.mk.injEq, and_true, map_mul, map_pow]
    field_simp
    ring
  simp_rw [e]
  exact integral_cubeDiff_slAct hY hp hpp hγ' (mul_ne_zero (pow_ne_zero _ hp0) hμ₁)
    (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) μ₁) _ (mul_pos hh hw) (hc0 m hm3) (hc m hm3)

end Eis

end

#print axioms Eis.uhsAct_upper_inv
#print axioms Eis.actP_of_lower_zero
#print axioms Eis.cubeRho_sq
#print axioms Eis.cubeRho_ne_zero
#print axioms Eis.normSq_cubeRho
#print axioms Eis.det_cubeMat
#print axioms Eis.actP_cubeMat
#print axioms Eis.colMat_col
#print axioms Eis.colMat_mem_Gam3
#print axioms Eis.decomp_col
#print axioms Eis.slAct_decomp
#print axioms Eis.cubeMat_inv
#print axioms Eis.cubeMat_mul_apply_zero
#print axioms Eis.cubeMat_mul_apply_one
#print axioms Eis.cubeMat_inv_mul_apply_zero
#print axioms Eis.cubeMat_inv_mul_apply_one
#print axioms Eis.cubeL_sq
#print axioms Eis.normSq_cubeL
#print axioms Eis.cubeMat_slAct
#print axioms Eis.cubeMat_inv_slAct
#print axioms Eis.integral_thetaF_affine
#print axioms Eis.integral_cubeDiff_slAct
#print axioms Eis.integral_cubeDiff_inv_slAct
