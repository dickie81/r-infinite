import KubotaGroups

/-! # The cusp expansions of the translates (round 368)

S5f-3c, the third part of round 360's S5f-3. The companion paper's Appendix A.2 writes each translate
`θ̄(z + a/c, v)` through a cusp matrix `g = g₁H`. Its invariances
"`reduce $\overline\theta(Hw)$ to one of the three functions $\overline{\theta(\gamma_\sigma w)}$`", the automorphy law gives
"`\overline{\theta(z+a/c,v)} =\overline{\kappa(g_1)}\,\overline{\theta\bigl(Hg^{-1}(z+a/c,v)\bigr)},`"
(its (A.8)), and `g⁻¹(z + a/c, v)` is explicit (its (A.9)). This file proves these from the data of round
361's display (`KubotaData`).

* **Rotated and shifted coordinates** (`norm_σO_unit`, **`thSer_affine`**, `thetaSupp_affine`): for a unit
  `ε` and any `b`, `thSer(c, d)(εz + b) = thSer(c, d′)(z)` with `d′(m) = d(ε⁻¹m)ĕ(σ(ε⁻¹m)b/9)`, and `d′` keeps
  the support and size condition.
* **The display's data** (`KubotaData`, `kubotaData_of`): the expansions, the invariance under `SL_2(ℤ)` and
  the automorphy on `Γ_1(3)`, extracted from `KubotaTheta`.
* **Matrices** (`det_map_σO`, `atG_mul`, `map_int_σO`, `det_map_int`, `atG_int_left`, `atG_kub_left`,
  `lowerThree`, `upperThree`, `uhsAct_one`, `atG_one`, `uhsAct_upper`, `TωJ`, `Tω2J`, `lowerδ3_eq`,
  `lowerNegδ3_eq`, `shapeT_zero`, `shapeT_one`, `shapeT_two`): the action of products, the invariances at any
  point, `(1, 0; 3t, 1)` and `(1, 3t; 0, 1)` with Kubota factor `1`, and the factorizations
  `(1, 0; λ, 1) = (1, 0; 2, 1)(1, 0; 3ω, 1)γ_−`, `(1, 0; −λ, 1) = (1, 0; −1, 1)(1, 0; −3ω, 1)γ_+`,
  `T(ω)J = γ_−(ω, −1; 0, ω²)` and `T(ω²)J = γ_+(ω², −1; 0, ω)`.
* **The cusp table** (**`cusp_table`**): for `H` the identity, `(1, 0; ±λ, 1)` or `(u, −1; 1, 0)`, `θ(Hw)` is a
  theta-type series under the support and size condition with the display's constant.
* **(A.9)** (**`uhsAct_cusp`**): `g⁻¹(z + a/c, v) = (−d/c − z̄/(c²(|z|² + v²)), v/(|c|²(|z|² + v²)))`.
* **(A.8)** (**`theta_at_cusp`**): for `g = (a, b; c, d) = g₁H` of determinant `1` with `g₁ ≡ I (mod 3)`,
  `θ(z + a/c, v) = κ(g₁)·θ(H·g⁻¹(z + a/c, v))`.
* **The cusp shift as a phase** (`thSer_cusp_shift`): at `−δ′/c − W` the coefficient `d(m)` becomes
  `d(m)ψ_{λ³c}(−mδ′)`, with round 366's `ebr_cusp_phase`.
-/

open NumberField Ideal UniqueFactorizationMonoid Complex
open scoped ComplexConjugate

noncomputable section

namespace Eis

theorem norm_σO_unit (u : (𝓞 K)ˣ) : ‖σO (u : 𝓞 K)‖ = 1 := by
  have h : σO (u : 𝓞 K) ^ 6 = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, units_pow_six, Units.val_one, map_one]
  have h2 := congrArg norm h
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

/-- **A theta-type series in rotated and shifted coordinates**: for a unit `ε` and any `b`,
`thSer(c, d)(εz + b) = thSer(c, d′)(z)` with `d′(m) = d(ε⁻¹m)·ĕ(σ(ε⁻¹m)b/9)`. -/
theorem thSer_affine (c : ℂ) (d : 𝓞 K → ℂ) (ε : (𝓞 K)ˣ) (b z : ℂ) (v : ℝ) :
    thSer c d (σO (ε : 𝓞 K) * z + b) v =
      thSer c (fun m => d ((ε⁻¹ : (𝓞 K)ˣ) * m) * ebr (σO ((ε⁻¹ : (𝓞 K)ˣ) * m) * b / 9)) z v := by
  unfold thSer
  congr 1
  rw [← (Units.mulLeft (ε⁻¹ : (𝓞 K)ˣ)).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Units.mulLeft_apply]
  have hn : ‖σO ((ε⁻¹ : (𝓞 K)ˣ) * n)‖ = ‖σO n‖ := by
    rw [map_mul, norm_mul, norm_σO_unit, one_mul]
  have he : σO ((ε⁻¹ : (𝓞 K)ˣ) * n) * (σO (ε : 𝓞 K) * z + b) / 9 =
      σO n * z / 9 + σO ((ε⁻¹ : (𝓞 K)ˣ) * n) * b / 9 := by
    have hu : σO ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * σO (ε : 𝓞 K) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [map_mul]
    linear_combination (σO n * z / 9) * hu
  rw [hn, he, ebr_add]
  ring

/-- The support and size condition survives the rotation and the phase. -/
theorem thetaSupp_affine {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) (ε : (𝓞 K)ˣ) (b : ℂ) :
    ThetaSupp Kc fun m => d ((ε⁻¹ : (𝓞 K)ˣ) * m) * ebr (σO ((ε⁻¹ : (𝓞 K)ˣ) * m) * b / 9) := by
  refine ⟨h.1, fun m hm => ?_⟩
  have hm' : d ((ε⁻¹ : (𝓞 K)ˣ) * m) ≠ 0 := fun h0 => hm (by beta_reduce; rw [h0, zero_mul])
  obtain ⟨q, hq, h1, h2, h3, h4⟩ := h.2 _ hm'
  refine ⟨(ε * q.1, q.2), ?_, h1, h2, h3, ?_⟩
  · unfold dualPt at hq ⊢
    simp only [Units.val_mul]
    have : (m : 𝓞 K) = ε * ((ε⁻¹ : (𝓞 K)ˣ) * m) := by
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [this, ← hq]; ring
  · rw [norm_mul, norm_ebr, mul_one]; exact h4

/-- **The data of the Kubota–Patterson display** used by the transformation: the three expansions under
the support and size condition (at `∞` supported on `δ₃𝒪`), the invariance under `SL_2(ℤ)` and the
automorphy on `Γ_1(3)` with Kubota's character. -/
def KubotaData (θ : ℂ → ℝ → ℂ) (Kc : ℝ) (c₀ cP cM : ℂ) (τ tP tM : 𝓞 K → ℂ) : Prop :=
  ThetaSupp Kc τ ∧ ThetaSupp Kc tP ∧ ThetaSupp Kc tM ∧ (∀ m, τ m ≠ 0 → δ3 ∣ m) ∧
    (∀ z v, 0 < v → θ z v = thSer c₀ τ z v) ∧
    (∀ z v, 0 < v → atG θ (gamPlus.map σO) z v = thSer cP tP z v) ∧
    (∀ z v, 0 < v → atG θ (gamMinus.map σO) z v = thSer cM tM z v) ∧
    (∀ γ : Matrix (Fin 2) (Fin 2) ℤ, γ.det = 1 → ∀ z v, 0 < v →
      atG θ (γ.map (Int.castRingHom ℂ)) z v = θ z v) ∧
    (∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)

theorem kubotaData_of (hK : KubotaTheta) :
    ∃ (θ : ℂ → ℝ → ℂ) (Kc : ℝ) (c₀ cP cM : ℂ) (τ tP tM : 𝓞 K → ℂ),
      KubotaData θ Kc c₀ cP cM τ tP tM := by
  obtain ⟨θ, Kc, C, c₀, cP, cM, τ, tP, tM, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := hK
  exact ⟨θ, Kc, c₀, cP, cM, τ, tP, tM, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem det_map_σO {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : γ.det = 1) : (γ.map σO).det = 1 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_one]

theorem atG_mul (θ : ℂ → ℝ → ℂ) {g h : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det = 1) (hh : h.det = 1)
    (z : ℂ) {v : ℝ} (hv : 0 < v) :
    atG θ (g * h) z v = atG θ g (uhsAct h z v).1 (uhsAct h z v).2 := by
  unfold atG; rw [uhsAct_mul hg hh z hv]

theorem map_int_σO (γ : Matrix (Fin 2) (Fin 2) ℤ) :
    (γ.map (Int.castRingHom (𝓞 K))).map σO = γ.map (Int.castRingHom ℂ) := by
  rw [Matrix.map_map]
  congr 1
  funext x
  simp

theorem det_map_int {γ : Matrix (Fin 2) (Fin 2) ℤ} (h : γ.det = 1) :
    (γ.map (Int.castRingHom (𝓞 K))).det = 1 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_one]

/-- The display's invariance under an integral matrix, at any point of upper half-space. -/
theorem atG_int_left {θ : ℂ → ℝ → ℂ}
    (hZ : ∀ γ : Matrix (Fin 2) (Fin 2) ℤ, γ.det = 1 → ∀ z v, 0 < v →
      atG θ (γ.map (Int.castRingHom ℂ)) z v = θ z v)
    {γ : Matrix (Fin 2) (Fin 2) ℤ} (hγ : γ.det = 1) {h : Matrix (Fin 2) (Fin 2) (𝓞 K)}
    (hh : h.det = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    atG θ ((γ.map (Int.castRingHom (𝓞 K)) * h).map σO) z v = atG θ (h.map σO) z v := by
  rw [Matrix.map_mul, atG_mul θ (det_map_σO (det_map_int hγ)) (det_map_σO hh) z hv, map_int_σO]
  exact hZ γ hγ _ _ (uhsAct_pos (det_map_σO hh) z hv)

/-- The display's automorphy under a matrix `≡ I (mod 3)` with Kubota factor `1`, at any point. -/
theorem atG_kub_left {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hγ : γ.det = 1) (h3 : ModThree γ) (hk : kub γ = 1)
    {h : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hh : h.det = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    atG θ ((γ * h).map σO) z v = atG θ (h.map σO) z v := by
  rw [Matrix.map_mul, atG_mul θ (det_map_σO hγ) (det_map_σO hh) z hv,
    hK3 γ hγ h3 _ _ (uhsAct_pos (det_map_σO hh) z hv), hk, one_mul]
  rfl

/-- A lower unipotent matrix `(1, 0; 3t, 1)` is `≡ I (mod 3)` with Kubota factor `1`. -/
theorem lowerThree (t : 𝓞 K) :
    (!![1, 0; 3 * t, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 ∧
      ModThree (!![1, 0; 3 * t, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) ∧
        kub (!![1, 0; 3 * t, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) = 1 := by
  refine ⟨by simp [Matrix.det_fin_two_of], fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp
  · have h1 : cub (3 * t) ⊤ = 1 := by rw [← Ideal.span_singleton_one]; exact cub_one_right _
    unfold kub
    split_ifs
    · rfl
    · simp [h1]

/-- An upper unipotent matrix `(1, 3t; 0, 1)` is `≡ I (mod 3)` with Kubota factor `1`. -/
theorem upperThree (t : 𝓞 K) :
    (!![1, 3 * t; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 ∧
      ModThree (!![1, 3 * t; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) ∧
        kub (!![1, 3 * t; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) = 1 := by
  refine ⟨by simp [Matrix.det_fin_two_of], fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp
  · unfold kub; simp

theorem uhsAct_one (z : ℂ) (v : ℝ) : uhsAct (1 : Matrix (Fin 2) (Fin 2) ℂ) z v = (z, v) := by
  simp [uhsAct, uhsZ, uhsV, uhsDen]

theorem atG_one (θ : ℂ → ℝ → ℂ) (z : ℂ) (v : ℝ) :
    atG θ ((1 : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO) z v = θ z v := by
  unfold atG
  rw [Matrix.map_one (σO : 𝓞 K →+* ℂ) (map_zero σO) (map_one σO), uhsAct_one]

/-- An upper triangular matrix `(a, b; 0, d)` with `|d| = 1` acts by `z ↦ (az + b)·conj d`. -/
theorem uhsAct_upper (a b d : ℂ) (hd : Complex.normSq d = 1) (z : ℂ) (v : ℝ) :
    uhsAct !![a, b; 0, d] z v = ((a * z + b) * conj d, v) := by
  simp [uhsAct, uhsZ, uhsV, uhsDen, hd]

theorem normSq_varpi : Complex.normSq (σO ω) = 1 := by
  rw [Complex.normSq_eq_norm_sq, ← coe_ωu, norm_σO_unit]; norm_num

theorem conj_σO_ω : conj (σO ω) = σO ω ^ 2 := by
  rw [← σO_cj, cj_ω, map_pow]

theorem conj_σO_ω_sq : conj (σO ω ^ 2) = σO ω := by
  rw [map_pow, conj_σO_ω, ← pow_mul, ← map_pow, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_add,
    ω_cube, one_mul, pow_one]

theorem σO_ω_cube : σO ω ^ 3 = 1 := by rw [← map_pow, ω_cube, map_one]

/-- `T(ω)J = γ_−·(ω, −1; 0, ω²)`. -/
theorem TωJ : (!![ω, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)) = gamMinus * !![ω, -1; 0, ω ^ 2] := by
  unfold gamMinus
  ext i j
  have h3 : (algebraMap (𝓞 K) K) ω ^ 3 = 1 := by rw [← map_pow, ω_cube, map_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -h3

/-- `T(ω²)J = γ_+·(ω², −1; 0, ω)`. -/
theorem Tω2J : (!![ω ^ 2, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)) = gamPlus * !![ω ^ 2, -1; 0, ω] := by
  unfold gamPlus
  ext i j
  have h3 : (algebraMap (𝓞 K) K) ω ^ 3 = 1 := by rw [← map_pow, ω_cube, map_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -h3

theorem algω_sq_add : (algebraMap (𝓞 K) K) ω ^ 2 + (algebraMap (𝓞 K) K) ω + 1 = 0 := by
  have := congrArg (algebraMap (𝓞 K) K) ω_sq_add
  simpa using this

theorem det_gamMinus : (gamMinus : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
  simp [gamMinus, Matrix.det_fin_two_of]

theorem det_gamPlus : (gamPlus : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
  simp [gamPlus, Matrix.det_fin_two_of]

theorem det_upper_unit (a : 𝓞 K) {e f : 𝓞 K} (h : e * f = 1) :
    (!![e, a; 0, f] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
  simp [Matrix.det_fin_two_of, h]

/-- `(1, 0; λ, 1) = (1, 0; 2, 1)·(1, 0; 3ω, 1)·γ_−`. -/
theorem lowerδ3_eq : (!![1, 0; δ3, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
    (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (𝓞 K)) *
      (!![1, 0; 3 * ω, 1] * gamMinus) := by
  unfold gamMinus δ3
  ext i j
  have h := algω_sq_add
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  linear_combination -h

/-- `(1, 0; −λ, 1) = (1, 0; −1, 1)·(1, 0; −3ω, 1)·γ_+`. -/
theorem lowerNegδ3_eq : (!![1, 0; -δ3, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
    (!![1, 0; -1, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (𝓞 K)) *
      (!![1, 0; 3 * -ω, 1] * gamPlus) := by
  unfold gamPlus δ3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  ring

theorem intT_map (x : ℤ) : (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (𝓞 K)) =
    !![1, (x : 𝓞 K); 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem intJ_map : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (𝓞 K)) =
    !![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem shapeT_zero (m q : ℤ) :
    (!![(m : 𝓞 K) + ((3 * q + 0 : ℤ) : 𝓞 K) * ω, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      !![1, (m : 𝓞 K); 0, 1] * (!![1, 3 * ((q : 𝓞 K) * ω); 0, 1] * !![0, -1; 1, 0]) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem shapeT_one (m q : ℤ) :
    (!![(m : 𝓞 K) + ((3 * q + 1 : ℤ) : 𝓞 K) * ω, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      !![1, (m : 𝓞 K); 0, 1] * (!![1, 3 * ((q : 𝓞 K) * ω); 0, 1] * !![ω, -1; 1, 0]) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem shapeT_two (m q : ℤ) :
    (!![(m : 𝓞 K) + ((3 * q + 2 : ℤ) : 𝓞 K) * ω, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      !![1, ((m + 1 : ℤ) : 𝓞 K); 0, 1] * (!![1, 3 * (((q : 𝓞 K) + 1) * ω); 0, 1] * !![ω ^ 2, -1; 1, 0]) := by
  have h := algω_sq_add
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, map_ofNat]
  all_goals first | ring1 | linear_combination -h

/-- **The cusp table**: for each shape of `H`, `θ(Hw)` is a theta-type series under the support and size
condition with the display's constant `K`: `H = I` gives the expansion at `∞`, `(1, 0; ±λ, 1)` the
expansions at `γ_∓`, and `(u, −1; 1, 0)` one of the three in rotated and shifted coordinates, according to
`u` modulo `ℤ + 3𝒪`. -/
theorem cusp_table {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c₀ cP cM : ℂ} {τ tP tM : 𝓞 K → ℂ}
    (hd : KubotaData θ Kc c₀ cP cM τ tP tM) (H : Matrix (Fin 2) (Fin 2) (𝓞 K))
    (hH : H = 1 ∨ H = !![1, 0; δ3, 1] ∨ H = !![1, 0; -δ3, 1] ∨ ∃ u, H = !![u, -1; 1, 0]) :
    ∃ (c : ℂ) (d : 𝓞 K → ℂ), ThetaSupp Kc d ∧
      ∀ z v, 0 < v → atG θ (H.map σO) z v = thSer c d z v := by
  obtain ⟨hτ, hP, hM, -, h0, hθP, hθM, hZ, hK3⟩ := hd
  have hdetZ : ∀ x : ℤ, (!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := fun x => by
    simp [Matrix.det_fin_two_of]
  have hdetT : ∀ x : ℤ, (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := fun x => by
    simp [Matrix.det_fin_two_of]
  rcases hH with rfl | rfl | rfl | ⟨u, rfl⟩
  · exact ⟨c₀, τ, hτ, fun z v hv => by rw [atG_one, h0 z v hv]⟩
  · refine ⟨cM, tM, hM, fun z v hv => ?_⟩
    obtain ⟨d1, m1, k1⟩ := lowerThree ω
    rw [lowerδ3_eq, atG_int_left hZ (hdetZ 2) (by rw [Matrix.det_mul, d1, det_gamMinus, one_mul]) z hv,
      atG_kub_left hK3 d1 m1 k1 det_gamMinus z hv, hθM z v hv]
  · refine ⟨cP, tP, hP, fun z v hv => ?_⟩
    obtain ⟨d1, m1, k1⟩ := lowerThree (-ω)
    rw [lowerNegδ3_eq, atG_int_left hZ (hdetZ (-1)) (by rw [Matrix.det_mul, d1, det_gamPlus, one_mul]) z hv,
      atG_kub_left hK3 d1 m1 k1 det_gamPlus z hv, hθP z v hv]
  · obtain ⟨m, n, rfl⟩ := exists_coords u
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2) ∧ n = 3 * q + r :=
      ⟨n / 3, n % 3, by omega, by omega⟩
    have hJ : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by simp [Matrix.det_fin_two_of]
    rcases hr with rfl | rfl | rfl
    · -- `u ≡ 0`: the expansion at `∞`
      refine ⟨c₀, τ, hτ, fun z v hv => ?_⟩
      obtain ⟨d1, m1, k1⟩ := upperThree ((q : 𝓞 K) * ω)
      have hJ' := det_map_int hJ
      rw [shapeT_zero, ← intT_map, ← intJ_map,
        atG_int_left hZ (hdetT m) (by rw [Matrix.det_mul, d1, hJ', one_mul]) z hv,
        atG_kub_left hK3 d1 m1 k1 hJ' z hv, map_int_σO, hZ _ hJ z v hv, h0 z v hv]
    · -- `u ≡ ω`: the expansion at `γ_−`, rotated by `ω²` and shifted by `−ω`
      refine ⟨cM, fun x => tM (((ωu ^ 2)⁻¹ : (𝓞 K)ˣ) * x) *
        ebr (σO (((ωu ^ 2)⁻¹ : (𝓞 K)ˣ) * x) * (-σO ω) / 9),
        thetaSupp_affine hM (ωu ^ 2) (-σO ω), fun z v hv => ?_⟩
      have hB : (!![ω, -1; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 :=
        det_upper_unit _ (by rw [← pow_succ', ω_cube])
      obtain ⟨d1, m1, k1⟩ := upperThree ((q : 𝓞 K) * ω)
      have hMB : (gamMinus * !![ω, -1; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
        rw [Matrix.det_mul, det_gamMinus, hB, one_mul]
      have hmap : (!![ω, -1; 0, ω ^ 2] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO =
          !![σO ω, -1; 0, σO ω ^ 2] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      have hn2 : Complex.normSq (σO ω ^ 2) = 1 := by rw [map_pow, normSq_varpi, one_pow]
      rw [shapeT_one, TωJ, ← intT_map,
        atG_int_left hZ (hdetT m) (by rw [Matrix.det_mul, d1, hMB, one_mul]) z hv,
        atG_kub_left hK3 d1 m1 k1 hMB z hv, Matrix.map_mul,
        atG_mul θ (det_map_σO det_gamMinus) (det_map_σO hB) z hv,
        hθM _ _ (uhsAct_pos (det_map_σO hB) z hv), hmap, uhsAct_upper _ _ _ hn2 z v, conj_σO_ω_sq,
        ← thSer_affine]
      congr 1
      rw [Units.val_pow_eq_pow_val, coe_ωu, map_pow]
      ring
    · -- `u ≡ 2ω`: the expansion at `γ_+`, rotated by `ω` and shifted by `−ω²`
      refine ⟨cP, fun x => tP ((ωu⁻¹ : (𝓞 K)ˣ) * x) * ebr (σO ((ωu⁻¹ : (𝓞 K)ˣ) * x) * (-σO ω ^ 2) / 9),
        thetaSupp_affine hP ωu (-σO ω ^ 2), fun z v hv => ?_⟩
      have hB : (!![ω ^ 2, -1; 0, ω] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 :=
        det_upper_unit _ (by rw [← pow_succ, ω_cube])
      obtain ⟨d1, m1, k1⟩ := upperThree (((q : 𝓞 K) + 1) * ω)
      have hPB : (gamPlus * !![ω ^ 2, -1; 0, ω] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
        rw [Matrix.det_mul, det_gamPlus, hB, one_mul]
      have hmap : (!![ω ^ 2, -1; 0, ω] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO =
          !![σO ω ^ 2, -1; 0, σO ω] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      rw [shapeT_two, Tω2J, ← intT_map,
        atG_int_left hZ (hdetT (m + 1)) (by rw [Matrix.det_mul, d1, hPB, one_mul]) z hv,
        atG_kub_left hK3 d1 m1 k1 hPB z hv, Matrix.map_mul,
        atG_mul θ (det_map_σO det_gamPlus) (det_map_σO hB) z hv,
        hθP _ _ (uhsAct_pos (det_map_σO hB) z hv), hmap, uhsAct_upper _ _ _ normSq_varpi z v, conj_σO_ω,
        ← thSer_affine]
      congr 1
      rw [coe_ωu]
      have h3 := σO_ω_cube
      linear_combination (z * σO ω) * h3

/-- **The coordinates at the cusp** (the companion paper's (A.9)): for `ad − bc = 1` and `c ≠ 0`,
`g⁻¹(z + a/c, v) = (−d/c − z̄/(c²(|z|² + v²)), v/(|c|²(|z|² + v²)))`. -/
theorem uhsAct_cusp {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (hc : c ≠ 0) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    uhsAct (!![d, -b; -c, a].map σO) (z + σO a / σO c) v =
      (-(σO d / σO c) - conj z / (σO c ^ 2 * ((Complex.normSq z + v ^ 2 : ℝ) : ℂ)),
        v / (Complex.normSq (σO c) * (Complex.normSq z + v ^ 2))) := by
  have hC : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  have hdet' : σO a * σO d - σO b * σO c = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
  have hlin : -σO c * (z + σO a / σO c) + σO a = -σO c * z := by field_simp; ring
  have hden : uhsDen (-σO c) (σO a) (z + σO a / σO c) v =
      Complex.normSq (σO c) * (Complex.normSq z + v ^ 2) := by
    unfold uhsDen; rw [hlin, Complex.normSq_mul, Complex.normSq_neg]; ring
  have hq : 0 < Complex.normSq z + v ^ 2 := by have := Complex.normSq_nonneg z; positivity
  have hnC : Complex.normSq (σO c) ≠ 0 := (Complex.normSq_pos.2 hC).ne'
  have hmap : (!![d, -b; -c, a] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO = !![σO d, -σO b; -σO c, σO a] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hs : σO d * (z + σO a / σO c) + -σO b = σO d * z + 1 / σO c := by
    field_simp; linear_combination hdet'
  have hcast : ((Complex.normSq z + v ^ 2 : ℝ) : ℂ) = z * conj z + (v : ℂ) ^ 2 := by
    push_cast; rw [Complex.mul_conj]
  have hN : ((Complex.normSq (σO c) * (Complex.normSq z + v ^ 2) : ℝ) : ℂ) =
      σO c * conj (σO c) * (z * conj z + (v : ℂ) ^ 2) := by
    rw [Complex.ofReal_mul, hcast, ← Complex.mul_conj (σO c)]
  have hq' : z * conj z + (v : ℂ) ^ 2 ≠ 0 := by rw [← hcast]; exact_mod_cast hq.ne'
  have hcC : conj (σO c) ≠ 0 := (map_ne_zero _).2 hC
  rw [hmap]
  unfold uhsAct uhsZ uhsV
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [hden, hlin]
  refine Prod.ext ?_ rfl
  simp only
  rw [hs, hN, hcast]
  push_cast
  field_simp
  simp only [map_neg, map_mul]
  ring

/-- **The automorphy at a cusp** (the companion paper's (A.8), before conjugation): for `g = (a, b; c, d)`
of determinant `1` with `c ≠ 0`, and `g = g₁H` with `g₁ ≡ I (mod 3)`,
`θ(z + a/c, v) = κ(g₁)·θ(H·g⁻¹(z + a/c, v))`, with `g⁻¹(z + a/c, v)` as in (A.9). -/
theorem theta_at_cusp {θ : ℂ → ℝ → ℂ}
    (hK3 : ∀ γ : Matrix (Fin 2) (Fin 2) (𝓞 K), γ.det = 1 → ModThree γ → ∀ z v, 0 < v →
      atG θ (γ.map σO) z v = kub γ * θ z v)
    {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    {g₁ H : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hg : !![a, b; c, d] = g₁ * H) (hg₁ : g₁.det = 1)
    (h3 : ModThree g₁) (hH : H.det = 1) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    θ (z + σO a / σO c) v = kub g₁ * atG θ (H.map σO)
      (-(σO d / σO c) - conj z / (σO c ^ 2 * ((Complex.normSq z + v ^ 2 : ℝ) : ℂ)))
      (v / (Complex.normSq (σO c) * (Complex.normSq z + v ^ 2))) := by
  have hg' : (!![d, -b; -c, a] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet
  have hgdet : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)).det = 1 := by
    rw [Matrix.det_fin_two_of]; exact hdet
  have hinv : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)) * !![d, -b; -c, a] = 1 := by
    have hK : (algebraMap (𝓞 K) K) a * (algebraMap (𝓞 K) K) d -
        (algebraMap (𝓞 K) K) b * (algebraMap (𝓞 K) K) c = 1 := by
      have := congrArg (algebraMap (𝓞 K) K) hdet
      simpa using this
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | linear_combination hK
  have hw := uhsAct_cusp hdet hc z v hv
  have hV' := uhsAct_pos (det_map_σO hg') (z + σO a / σO c) hv
  rw [hw] at hV'
  have hback : uhsAct ((!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)
      (-(σO d / σO c) - conj z / (σO c ^ 2 * ((Complex.normSq z + v ^ 2 : ℝ) : ℂ)))
      (v / (Complex.normSq (σO c) * (Complex.normSq z + v ^ 2))) = (z + σO a / σO c, v) := by
    have e := uhsAct_mul (det_map_σO hgdet) (det_map_σO hg') (z + σO a / σO c) hv
    rw [← Matrix.map_mul, hinv, Matrix.map_one (σO : 𝓞 K →+* ℂ) (map_zero σO) (map_one σO), uhsAct_one,
      hw] at e
    exact e.symm
  calc θ (z + σO a / σO c) v
      = atG θ ((!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (𝓞 K)).map σO)
          (-(σO d / σO c) - conj z / (σO c ^ 2 * ((Complex.normSq z + v ^ 2 : ℝ) : ℂ)))
          (v / (Complex.normSq (σO c) * (Complex.normSq z + v ^ 2))) := by
        unfold atG; rw [hback]
    _ = _ := by
        rw [hg, Matrix.map_mul, atG_mul θ (det_map_σO hg₁) (det_map_σO hH) _ hV',
          hK3 g₁ hg₁ h3 _ _ (uhsAct_pos (det_map_σO hH) _ hV')]
        rfl

/-- **The cusp shift as a phase**: a theta-type series at `−δ′/c − W` is the theta-type series at `−W`
with coefficients `d(m)ψ_{λ³c}(−mδ′)`. -/
theorem thSer_cusp_shift (c₀ : ℂ) (d : 𝓞 K → ℂ) (δ' c : 𝓞 K) (W : ℂ) (V : ℝ) :
    thSer c₀ d (-(σO δ' / σO c) - W) V =
      thSer c₀ (fun m => d m * ψc (δ3 ^ 3 * c) (-(m * δ'))) (-W) V := by
  unfold thSer
  congr 1
  refine tsum_congr fun m => ?_
  rw [show σO m * (-(σO δ' / σO c) - W) / 9 = σO m * (-σO δ' / σO c) / 9 + σO m * -W / 9 by ring,
    ebr_add, ebr_cusp_phase]
  ring

end Eis

end

#print axioms Eis.norm_σO_unit
#print axioms Eis.thSer_affine
#print axioms Eis.thetaSupp_affine
#print axioms Eis.kubotaData_of
#print axioms Eis.det_map_σO
#print axioms Eis.atG_mul
#print axioms Eis.map_int_σO
#print axioms Eis.det_map_int
#print axioms Eis.atG_int_left
#print axioms Eis.atG_kub_left
#print axioms Eis.lowerThree
#print axioms Eis.upperThree
#print axioms Eis.uhsAct_one
#print axioms Eis.atG_one
#print axioms Eis.uhsAct_upper
#print axioms Eis.normSq_varpi
#print axioms Eis.conj_σO_ω
#print axioms Eis.conj_σO_ω_sq
#print axioms Eis.σO_ω_cube
#print axioms Eis.TωJ
#print axioms Eis.Tω2J
#print axioms Eis.algω_sq_add
#print axioms Eis.det_gamMinus
#print axioms Eis.det_gamPlus
#print axioms Eis.det_upper_unit
#print axioms Eis.lowerδ3_eq
#print axioms Eis.lowerNegδ3_eq
#print axioms Eis.intT_map
#print axioms Eis.intJ_map
#print axioms Eis.shapeT_zero
#print axioms Eis.shapeT_one
#print axioms Eis.shapeT_two
#print axioms Eis.cusp_table
#print axioms Eis.uhsAct_cusp
#print axioms Eis.theta_at_cusp
#print axioms Eis.thSer_cusp_shift
