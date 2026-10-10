import KubotaUnfold

/-! # The cubic Eisenstein series on `Γ_1(3)`: convergence, automorphy, holomorphy (round 387)

S5f-9 of round 360's plan, part 1 (S5f-9a). The series is
`E(w, s) = Σ_{(c, d)} (c/d)₃·(v/(|cz + d|² + |c|²v²))^s` over the bottom rows of `Γ_1(3)`: the coprime
`(c, d)` with `3 ∣ c` and `d ≡ 1 (mod 3)`. Its term at the bottom row of `γ` is `conj κ(γ)·v(γ·w)^s`.

* **The bottom rows** (`BRow`, a definition; `exists_Gam3_of_BRow` and `bRow_of_Gam3`): `(c, d)` is the
  bottom row of an element of `Γ_1(3)` exactly when `BRow (c, d)`. For `uc + wd = 1`,
  `(w + uc, u(d − 1); c, d)` is one.
* **The character** (**`kub_eq_conj_cub`**, with `cub_b_mul_cub_c`, `norm_kub` and `kub_inv_Gam3`):
  `κ(γ) = conj((c/d)₃)` on `Γ_1(3)`, from round 382's `(b/d)₃ = (c/a)₃` and `(b/d)₃(c/d)₃ = 1`.
* **Along `Γ_1(3)`** (`rowMul` and `rowEquiv`, definitions; **`cub_rowMul`** and **`height_rowMul`**, with
  `rowMul_bottom`, `rowMul_mul`, `rowMul_one`, `bRow_rowMul` and `bRow_rowMul_iff`): `(c, d) ↦ (c, d)g`
  permutes the bottom rows for `g ∈ Γ_1(3)`, with `((c, d)g)₃ = (c/d)₃·conj κ(g)` and
  `v(g·w)/Q_{g·w}(c, d) = v(w)/Q_w((c, d)g)`, `Q_w(c, d) = |cz + d|² + |c|²v²`.
* **Convergence** (`eisTerm` and `eis1`, definitions; **`summable_eisTerm`**, with
  `summable_lattice_rpow`, `summable_O_rpow`, `uhsDen_ge`, `uhsDen_pos_of_BRow`, `height_le_lattice`,
  `norm_eisTerm_le` and `summable_height_rpow`): `Q_w(c, d) ≥ m(|c|² + |d|²)` with
  `m = v²/(2v² + 4|z|² + 2)`, and `(1 + |σc|)(1 + |σd|) ≤ 9(|σc|² + |σd|²)` for `(c, d) ≠ 0`, so the series
  converges absolutely for `Re s > 2`.
* **Automorphy** (**`eis1_slAct`**, with `eisTerm_rowMul`; `eis1_transl`, with `slT_mem_Gam3`):
  `E(γ·w, s) = κ(γ)E(w, s)` for `γ ∈ Γ_1(3)`, and `E` has period `3ℤ[ω]` in `z`.
* **The term `v^s`** (**`eis1_eq`**, with `bRow_zero_iff` and `eisTerm_zero_one`): the only bottom row with
  `c = 0` is `(0, 1)`, and its term is `v^s`.
* **Holomorphy** (**`differentiableOn_eis1`**, with `rpow_le_add_rpow`): `s ↦ E(w, s)` is holomorphic on
  `Re s > 2`.
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

/-- **The bottom rows of `Γ_1(3)`**: coprime `(c, d)` with `3 ∣ c` and `d ≡ 1 (mod 3)`. -/
def BRow (cd : 𝓞 K × 𝓞 K) : Prop := IsCoprime cd.1 cd.2 ∧ (3 : 𝓞 K) ∣ cd.1 ∧ Primary cd.2

/-- `(b/d)₃(c/d)₃ = 1` when `ad − bc = 1` and `d` is primary. -/
theorem cub_b_mul_cub_c {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (hd : Primary d) :
    cub b (span {d}) * cub c (span {d}) = 1 := by
  rw [← cub_mul_left, cub_congr (show d ∣ b * c - (-1) from ⟨a, by linear_combination -hdet⟩),
    cub_neg hd, cub_one hd]

/-- **`κ` through the bottom row** (Dunn and Radziwiłł's remark that derives their (5.5)):
`κ(γ) = conj((c/d)₃)` on `Γ_1(3)`. -/
theorem kub_eq_conj_cub {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hdet : γ.det = 1) (h3 : ModThree γ) :
    kub γ = conj (σO (cub (γ 1 0) (span {γ 1 1}))) := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_fin_two_eq γ
  rw [modThree_iff] at h3
  obtain ⟨ha, hb, hc, hd⟩ := h3
  have hdet' : a * d - b * c = 1 := by rw [Matrix.det_fin_two_of] at hdet; exact hdet
  rw [kub_eq_cub hdet]
  change σO (cub c (span {a})) = conj (σO (cub c (span {d})))
  rw [← cub_bd_eq_ca hdet' ha hb hc hd]
  have hcd : IsCoprime c d := ⟨-b, a, by linear_combination hdet'⟩
  have hn := norm_σO_cub hd hcd
  have hσ : σO (cub b (span {d})) * σO (cub c (span {d})) = 1 := by
    rw [← map_mul, cub_b_mul_cub_c hdet' hd, map_one]
  rw [eq_inv_of_mul_eq_one_left hσ, Complex.inv_eq_conj hn]

theorem norm_kub {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hdet : γ.det = 1) (h3 : ModThree γ) :
    ‖kub γ‖ = 1 := by
  rw [kub_eq_conj_cub hdet h3, Complex.norm_conj]
  obtain ⟨a, b, c, d, rfl⟩ := exists_fin_two_eq γ
  rw [modThree_iff] at h3
  have hdet' : a * d - b * c = 1 := by rw [Matrix.det_fin_two_of] at hdet; exact hdet
  change ‖σO (cub c (span {d}))‖ = 1
  exact norm_σO_cub h3.2.2.2 ⟨-b, a, by linear_combination hdet'⟩

/-- The bottom row of an element of `Γ_1(3)` is a bottom row in the sense of `BRow`. -/
theorem bRow_of_Gam3 {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) : BRow (γ 1 0, γ 1 1) := by
  have h3 := mem_Gam3.1 hγ
  have hdet := γ.2
  obtain ⟨a, b, c, d, hγe⟩ := exists_fin_two_eq (γ : Matrix (Fin 2) (Fin 2) (𝓞 K))
  rw [hγe] at h3 hdet
  rw [modThree_iff] at h3
  have hdet' : a * d - b * c = 1 := by rw [Matrix.det_fin_two_of] at hdet; exact hdet
  have e10 : γ 1 0 = c := by rw [show γ 1 0 = (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 from rfl, hγe]; rfl
  have e11 : γ 1 1 = d := by rw [show γ 1 1 = (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 1 from rfl, hγe]; rfl
  rw [e10, e11]
  exact ⟨⟨-b, a, by linear_combination hdet'⟩, h3.2.2.1, h3.2.2.2⟩

/-- **Every bottom row comes from `Γ_1(3)`**: for `uc + wd = 1`, `(w + uc, u(d − 1); c, d)`. -/
theorem exists_Gam3_of_BRow {cd : 𝓞 K × 𝓞 K} (h : BRow cd) :
    ∃ γ : SL(2, 𝓞 K), γ ∈ Gam3 ∧ γ 1 0 = cd.1 ∧ γ 1 1 = cd.2 := by
  obtain ⟨⟨u, w, huw⟩, hc, hd⟩ := h
  have hdet : (w + u * cd.1) * cd.2 - u * (cd.2 - 1) * cd.1 = 1 := by linear_combination huw
  let γ : SL(2, 𝓞 K) := ⟨!![w + u * cd.1, u * (cd.2 - 1); cd.1, cd.2],
    by rw [Matrix.det_fin_two_of]; exact hdet⟩
  refine ⟨γ, mem_Gam3.2 ?_, rfl, rfl⟩
  change ModThree !![w + u * cd.1, u * (cd.2 - 1); cd.1, cd.2]
  rw [modThree_iff]
  obtain ⟨k, hk⟩ := hd
  refine ⟨⟨-(w * k), ?_⟩, ⟨u * k, by rw [hk]; ring⟩, hc, ⟨k, hk⟩⟩
  linear_combination huw - w * hk

/-- The bottom row of `γg`: `(c, d)·g`. -/
def rowMul (g : SL(2, 𝓞 K)) (cd : 𝓞 K × 𝓞 K) : 𝓞 K × 𝓞 K :=
  (cd.1 * g 0 0 + cd.2 * g 1 0, cd.1 * g 0 1 + cd.2 * g 1 1)

theorem rowMul_bottom (γ g : SL(2, 𝓞 K)) :
    rowMul g (γ 1 0, γ 1 1) = ((γ * g) 1 0, (γ * g) 1 1) := by
  simp only [rowMul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem rowMul_mul (g h : SL(2, 𝓞 K)) (cd : 𝓞 K × 𝓞 K) :
    rowMul (g * h) cd = rowMul h (rowMul g cd) := by
  simp only [rowMul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Prod.mk.injEq]
  constructor <;> ring

theorem rowMul_one (cd : 𝓞 K × 𝓞 K) : rowMul 1 cd = cd := by
  simp [rowMul]

/-- `(c, d) ↦ (c, d)·g`, a bijection. -/
def rowEquiv (g : SL(2, 𝓞 K)) : 𝓞 K × 𝓞 K ≃ 𝓞 K × 𝓞 K where
  toFun := rowMul g
  invFun := rowMul g⁻¹
  left_inv cd := by rw [← rowMul_mul, mul_inv_cancel, rowMul_one]
  right_inv cd := by rw [← rowMul_mul, inv_mul_cancel, rowMul_one]

theorem bRow_rowMul {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) {cd : 𝓞 K × 𝓞 K} (h : BRow cd) :
    BRow (rowMul g cd) := by
  obtain ⟨γ, hγ, h1, h2⟩ := exists_Gam3_of_BRow h
  have e : cd = (γ 1 0, γ 1 1) := by rw [h1, h2]
  rw [e, rowMul_bottom]
  exact bRow_of_Gam3 (Gam3.mul_mem hγ hg)

theorem bRow_rowMul_iff {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (cd : 𝓞 K × 𝓞 K) :
    BRow (rowMul g cd) ↔ BRow cd := by
  refine ⟨fun h => ?_, bRow_rowMul hg⟩
  have := bRow_rowMul (Gam3.inv_mem hg) h
  rwa [← rowMul_mul, mul_inv_cancel, rowMul_one] at this

/-- **The symbol along `Γ_1(3)`**: `((c, d)g)₃ = (c/d)₃·conj κ(g)`. -/
theorem cub_rowMul {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) {cd : 𝓞 K × 𝓞 K} (h : BRow cd) :
    σO (cub (rowMul g cd).1 (span {(rowMul g cd).2})) =
      σO (cub cd.1 (span {cd.2})) * conj (kub g) := by
  obtain ⟨γ, hγ, h1, h2⟩ := exists_Gam3_of_BRow h
  have e : cd = (γ 1 0, γ 1 1) := by rw [h1, h2]
  have hk := kub_mul_Gam3 hγ hg
  rw [kub_eq_conj_cub (γ * g).2 (mem_Gam3.1 (Gam3.mul_mem hγ hg)),
    kub_eq_conj_cub γ.2 (mem_Gam3.1 hγ)] at hk
  have hk' := congrArg (starRingEnd ℂ) hk
  rw [map_mul, Complex.conj_conj, Complex.conj_conj] at hk'
  rw [e, rowMul_bottom]
  exact hk'

/-- `κ(g⁻¹) = conj κ(g)` on `Γ_1(3)`. -/
theorem kub_inv_Gam3 {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) : kub ↑(g⁻¹) = conj (kub ↑g) := by
  have h := kub_mul_Gam3 hg (Gam3.inv_mem hg)
  rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, kub_one] at h
  have hn := norm_kub g.2 (mem_Gam3.1 hg)
  have h0 : kub ↑g ≠ 0 := by intro h0; rw [h0] at hn; simp at hn
  rw [eq_inv_of_mul_eq_one_right h.symm, Complex.inv_eq_conj hn]

/-- **The height along `Γ_1(3)`**: `v(g·w)/Q_{g·w}(c, d) = v(w)/Q_w((c, d)g)`. -/
theorem height_rowMul (g : SL(2, 𝓞 K)) {cd : 𝓞 K × 𝓞 K} (h : BRow cd) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    (slAct g p).2 / uhsDen (σO cd.1) (σO cd.2) (slAct g p).1 (slAct g p).2 =
      p.2 / uhsDen (σO (rowMul g cd).1) (σO (rowMul g cd).2) p.1 p.2 := by
  obtain ⟨γ, -, h1, h2⟩ := exists_Gam3_of_BRow h
  have e : cd = (γ 1 0, γ 1 1) := by rw [h1, h2]
  rw [e, rowMul_bottom, ← slAct_snd, ← slAct_snd, slAct_mul _ _ hp]

/-- `Σ_{n ∈ ℤ²} (1 + |n|)^{−τ} < ∞` for `τ > 2`. -/
theorem summable_lattice_rpow {τ : ℝ} (hτ : 2 < τ) :
    Summable fun n : Fin 2 → ℤ => (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-τ) := by
  have h1 := summable_one_add_abs_rpow (b := τ / 2) (by linarith)
  have h2 := Summable.mul_of_nonneg h1 h1 (fun _ => by positivity) (fun _ => by positivity)
  have h3 : Summable fun n : Fin 2 → ℤ =>
      (1 + |((n 0 : ℤ) : ℝ)|) ^ (-(τ / 2)) * (1 + |((n 1 : ℤ) : ℝ)|) ^ (-(τ / 2)) :=
    (finTwoArrowEquiv ℤ).summable_iff.2 h2
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) h3
  set x : Fin 2 → ℝ := fun i => (n i : ℝ)
  have hx := prod_le_sq_cpt x
  have hA : 0 < 1 + |x 0| := by positivity
  have hB : 0 < 1 + |x 1| := by positivity
  have hN : 0 < 1 + ‖cpt x‖ := by positivity
  rw [← Real.mul_rpow hA.le hB.le]
  calc (1 + ‖cpt x‖) ^ (-τ) = ((1 + ‖cpt x‖) ^ (2 : ℝ)) ^ (-(τ / 2)) := by
        rw [← Real.rpow_mul hN.le]; congr 1; ring
    _ ≤ ((1 + |x 0|) * (1 + |x 1|)) ^ (-(τ / 2)) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
        rw [Real.rpow_two]; exact hx

/-- `Σ_{x ∈ ℤ[ω]} (1 + |σx|)^{−τ} < ∞` for `τ > 2`. -/
theorem summable_O_rpow {τ : ℝ} (hτ : 2 < τ) :
    Summable fun x : 𝓞 K => (1 + ‖σO x‖) ^ (-τ) := by
  rw [← crdEquiv.summable_iff]
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _) (fun n => ?_)
    ((summable_lattice_rpow hτ).mul_left ((2 : ℝ) ^ τ))
  show (1 + ‖σO (crd n)‖) ^ (-τ) ≤ (2 : ℝ) ^ τ * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-τ)
  have hc := norm_cpt_le_two_norm_σO n
  have hle : 1 + ‖cpt (fun i => (n i : ℝ))‖ ≤ 2 * (1 + ‖σO (crd n)‖) := by
    have : ‖cpt (fun i => (n i : ℝ))‖ = ‖cpt (nR n)‖ := rfl
    rw [this]; linarith [norm_nonneg (σO (crd n))]
  have hpos : 0 < 1 + ‖cpt (fun i => (n i : ℝ))‖ := by positivity
  calc (1 + ‖σO (crd n)‖) ^ (-τ) = (2 : ℝ) ^ τ * (2 * (1 + ‖σO (crd n)‖)) ^ (-τ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity), ← mul_assoc,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ (2 : ℝ) ^ τ * (1 + ‖cpt (fun i => (n i : ℝ))‖) ^ (-τ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hle (by linarith))
          (by positivity)

/-- **The denominator bounds the row**: `|cz + d|² + |c|²v² ≥ m(|c|² + |d|²)`,
`m = v²/(2v² + 4|z|² + 2)`. -/
theorem uhsDen_ge (c d z : ℂ) {v : ℝ} (hv : 0 < v) :
    v ^ 2 / (2 * v ^ 2 + 4 * Complex.normSq z + 2) * (Complex.normSq c + Complex.normSq d) ≤
      uhsDen c d z v := by
  unfold uhsDen
  set A := Complex.normSq (c * z + d)
  set B := Complex.normSq c
  set D := Complex.normSq d
  set Z := Complex.normSq z
  have hA : 0 ≤ A := Complex.normSq_nonneg _
  have hB : 0 ≤ B := Complex.normSq_nonneg _
  have hZ : 0 ≤ Z := Complex.normSq_nonneg _
  have hD : D ≤ 2 * A + 2 * (B * Z) := by
    have e : d = (c * z + d) - c * z := by ring
    have h1 : ‖d‖ ≤ ‖c * z + d‖ + ‖c‖ * ‖z‖ := by
      calc ‖d‖ = ‖(c * z + d) - c * z‖ := by rw [← e]
        _ ≤ ‖c * z + d‖ + ‖c * z‖ := norm_sub_le _ _
        _ = ‖c * z + d‖ + ‖c‖ * ‖z‖ := by rw [norm_mul]
    have h2 : ‖d‖ ^ 2 ≤ 2 * ‖c * z + d‖ ^ 2 + 2 * (‖c‖ ^ 2 * ‖z‖ ^ 2) := by
      nlinarith [norm_nonneg d, norm_nonneg (c * z + d), mul_nonneg (norm_nonneg c) (norm_nonneg z),
        sq_nonneg (‖c * z + d‖ - ‖c‖ * ‖z‖)]
    simpa only [A, B, D, Z, Complex.normSq_eq_norm_sq] using h2
  have hN : 0 < 2 * v ^ 2 + 4 * Z + 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hN]
  have hv2 : 0 ≤ v ^ 2 := by positivity
  nlinarith [mul_nonneg hv2 hB, mul_nonneg hv2 hA, mul_nonneg (mul_nonneg hv2 hB) hZ,
    mul_nonneg hA hZ, mul_nonneg (mul_nonneg hv2 hv2) hB]

/-- A bottom row has a positive denominator. -/
theorem uhsDen_pos_of_BRow {cd : 𝓞 K × 𝓞 K} (h : BRow cd) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    0 < uhsDen (σO cd.1) (σO cd.2) p.1 p.2 := by
  obtain ⟨γ, -, h1, h2⟩ := exists_Gam3_of_BRow h
  have := slDen_pos γ hp
  rwa [h1, h2] at this

/-- **The height of a bottom row is controlled by the lattice**:
`v/Q ≤ (9v/m)·(1 + |σc|)^{−1}(1 + |σd|)^{−1}`. -/
theorem height_le_lattice {cd : 𝓞 K × 𝓞 K} (h : BRow cd) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 ≤
      9 * p.2 / (p.2 ^ 2 / (2 * p.2 ^ 2 + 4 * Complex.normSq p.1 + 2)) *
        ((1 + ‖σO cd.1‖) * (1 + ‖σO cd.2‖))⁻¹ := by
  have hv : 0 < p.2 := hp
  set m := p.2 ^ 2 / (2 * p.2 ^ 2 + 4 * Complex.normSq p.1 + 2) with hm
  have hm0 : 0 < m := div_pos (pow_pos hv 2) (by nlinarith [Complex.normSq_nonneg p.1])
  set a := ‖σO cd.1‖
  set b := ‖σO cd.2‖
  have hQ := uhsDen_ge (σO cd.1) (σO cd.2) p.1 hv
  have hQpos := uhsDen_pos_of_BRow h hp
  -- `(1 + a)(1 + b) ≤ 9(a² + b²)`, since `max(a, b) ≥ 1`
  have hab : (1 + a) * (1 + b) ≤ 9 * (Complex.normSq (σO cd.1) + Complex.normSq (σO cd.2)) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    change (1 + a) * (1 + b) ≤ 9 * (a ^ 2 + b ^ 2)
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hmax : 1 ≤ a ∨ 1 ≤ b := by
      by_cases hc : cd.1 = 0
      · right
        have hd : cd.2 ≠ 0 := by
          intro hd
          obtain ⟨u, w, huw⟩ := h.1
          rw [hc, hd] at huw; simp at huw
        exact one_le_norm_σO hd
      · exact Or.inl (one_le_norm_σO hc)
    rcases hmax with h1 | h1 <;>
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - 1), sq_nonneg (a - 1), mul_nonneg ha0 hb0]
  have hpos : 0 < (1 + a) * (1 + b) := by positivity
  rw [div_le_iff₀ hQpos]
  have hne : (1 + a) * (1 + b) ≠ 0 := hpos.ne'
  calc p.2 = 9 * p.2 / m * ((1 + a) * (1 + b))⁻¹ * (m * ((1 + a) * (1 + b)) / 9) := by
        rw [show (9 : ℝ) * p.2 / m * ((1 + a) * (1 + b))⁻¹ * (m * ((1 + a) * (1 + b)) / 9) =
          p.2 * (m / m) * (((1 + a) * (1 + b))⁻¹ * ((1 + a) * (1 + b))) by ring,
          div_self hm0.ne', inv_mul_cancel₀ hne]
        ring
    _ ≤ 9 * p.2 / m * ((1 + a) * (1 + b))⁻¹ * uhsDen (σO cd.1) (σO cd.2) p.1 p.2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc m * ((1 + a) * (1 + b)) / 9 ≤ m * (9 * (Complex.normSq (σO cd.1) +
              Complex.normSq (σO cd.2))) / 9 := by gcongr
          _ = m * (Complex.normSq (σO cd.1) + Complex.normSq (σO cd.2)) := by ring
          _ ≤ _ := hQ

open Classical in
/-- The terms of the Eisenstein series: `(c/d)₃·(v/(|cz + d|² + |c|²v²))^s` on the bottom rows. -/
def eisTerm (s : ℂ) (p : ℂ × ℝ) (cd : 𝓞 K × 𝓞 K) : ℂ :=
  if BRow cd then σO (cub cd.1 (span {cd.2})) *
    ((p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 : ℝ) : ℂ) ^ s else 0

/-- **The cubic Eisenstein series** on `Γ_1(3)` at the cusp `∞`:
`E(w, s) = Σ_{(c, d)} (c/d)₃·(v/(|cz + d|² + |c|²v²))^s` over the bottom rows of `Γ_1(3)`. -/
def eis1 (s : ℂ) (p : ℂ × ℝ) : ℂ := ∑' cd : 𝓞 K × 𝓞 K, eisTerm s p cd

open Classical in
theorem norm_eisTerm_le (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : 𝓞 K × 𝓞 K) :
    ‖eisTerm s p cd‖ ≤ if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ s.re else 0 := by
  unfold eisTerm
  split_ifs with h
  · have hpos : 0 < p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 :=
      div_pos hp (uhsDen_pos_of_BRow h hp)
    rw [norm_mul, norm_σO_cub h.2.2 h.1, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  · simp

open Classical in
/-- **The majorant**: `Σ_{(c, d)} (v/Q)^σ < ∞` over the bottom rows, for `σ > 2`. -/
theorem summable_height_rpow {σ : ℝ} (hσ : 2 < σ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    Summable fun cd : 𝓞 K × 𝓞 K =>
      if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ σ else 0 := by
  have hv : 0 < p.2 := hp
  set C := 9 * p.2 / (p.2 ^ 2 / (2 * p.2 ^ 2 + 4 * Complex.normSq p.1 + 2))
  have hC : 0 < C := div_pos (by positivity) (div_pos (pow_pos hv 2)
    (by nlinarith [Complex.normSq_nonneg p.1]))
  have hS := Summable.mul_of_nonneg (summable_O_rpow hσ) (summable_O_rpow hσ)
    (fun _ => by positivity) (fun _ => by positivity)
  refine Summable.of_nonneg_of_le (fun cd => by
      split_ifs
      exacts [Real.rpow_nonneg (div_nonneg hv.le (uhsDen_nonneg _ _ _ _)) _, le_rfl]) (fun cd => ?_)
    (hS.mul_left (C ^ σ))
  split_ifs with h
  · have hle := height_le_lattice h hp
    have h0 : 0 ≤ p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 :=
      (div_pos hv (uhsDen_pos_of_BRow h hp)).le
    calc (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ σ
        ≤ (C * ((1 + ‖σO cd.1‖) * (1 + ‖σO cd.2‖))⁻¹) ^ σ :=
          Real.rpow_le_rpow h0 hle (by linarith)
      _ = C ^ σ * ((1 + ‖σO cd.1‖) ^ (-σ) * (1 + ‖σO cd.2‖) ^ (-σ)) := by
          rw [Real.mul_rpow hC.le (by positivity), Real.inv_rpow (by positivity),
            ← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  · positivity

/-- **Absolute convergence** for `Re s > 2`. -/
theorem summable_eisTerm {s : ℂ} (hs : 2 < s.re) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    Summable fun cd => eisTerm s p cd :=
  Summable.of_norm_bounded (summable_height_rpow hs hp) (norm_eisTerm_le s hp)

open Classical in
theorem eisTerm_rowMul {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS)
    (cd : 𝓞 K × 𝓞 K) :
    eisTerm s (slAct g p) (rowMul g⁻¹ cd) = kub ↑g * eisTerm s p cd := by
  unfold eisTerm
  by_cases h : BRow cd
  · have h' : BRow (rowMul g⁻¹ cd) := bRow_rowMul (Gam3.inv_mem hg) h
    simp only [h, h', ↓reduceIte]
    rw [cub_rowMul (Gam3.inv_mem hg) h, kub_inv_Gam3 hg, Complex.conj_conj, height_rowMul g h' hp,
      ← rowMul_mul, inv_mul_cancel, rowMul_one]
    ring
  · have h' : ¬ BRow (rowMul g⁻¹ cd) := fun h'' => h ((bRow_rowMul_iff (Gam3.inv_mem hg) cd).1 h'')
    simp only [h, h', ↓reduceIte, mul_zero]

/-- **Automorphy**: `E(γ·w, s) = κ(γ)·E(w, s)` for `γ ∈ Γ_1(3)`. -/
theorem eis1_slAct {g : SL(2, 𝓞 K)} (hg : g ∈ Gam3) (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eis1 s (slAct g p) = kub ↑g * eis1 s p := by
  unfold eis1
  calc ∑' cd, eisTerm s (slAct g p) cd = ∑' cd, eisTerm s (slAct g p) (rowMul g⁻¹ cd) :=
        ((rowEquiv g⁻¹).tsum_eq (eisTerm s (slAct g p))).symm
    _ = ∑' cd, kub ↑g * eisTerm s p cd := tsum_congr (eisTerm_rowMul hg s hp)
    _ = kub ↑g * ∑' cd, eisTerm s p cd := tsum_mul_left

theorem slT_mem_Gam3 {t : 𝓞 K} (ht : (3 : 𝓞 K) ∣ t) : slT t ∈ Gam3 := by
  rw [mem_Gam3, coe_slT, modThree_iff]
  exact ⟨primary_one, ht, dvd_zero _, primary_one⟩

/-- **Periodicity**: `E(z + t, v; s) = E(z, v; s)` for `t ∈ 3ℤ[ω]`. -/
theorem eis1_transl {t : 𝓞 K} (ht : (3 : 𝓞 K) ∣ t) (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eis1 s (p.1 + σO t, p.2) = eis1 s p := by
  have h := eis1_slAct (slT_mem_Gam3 ht) s hp
  rw [slAct_slT, coe_slT] at h
  rw [h]
  unfold kub
  simp

theorem bRow_zero_iff {d : 𝓞 K} : BRow (0, d) ↔ d = 1 := by
  constructor
  · rintro ⟨h1, -, h3⟩
    exact primary_eq_one_of_isUnit h3 (isCoprime_zero_left.1 h1)
  · rintro rfl
    exact ⟨isCoprime_zero_left.2 isUnit_one, dvd_zero _, primary_one⟩

theorem eisTerm_zero_one (s : ℂ) (p : ℂ × ℝ) :
    eisTerm s p (0, 1) = ((p.2 : ℝ) : ℂ) ^ s := by
  have h : BRow ((0 : 𝓞 K), (1 : 𝓞 K)) := bRow_zero_iff.2 rfl
  unfold eisTerm
  simp only [h, ↓reduceIte]
  change σO (cub 0 (span {1})) * (((p.2 / uhsDen (σO 0) (σO 1) p.1 p.2 : ℝ) : ℂ)) ^ s = _
  rw [cub_one_right]
  simp [uhsDen]

open Classical in
/-- **The term `v^s`**: `E(w, s) = v^s + Σ_{c ≠ 0}`, the bottom rows with `c = 0` being `(0, 1)` alone. -/
theorem eis1_eq {s : ℂ} (hs : 2 < s.re) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eis1 s p = ((p.2 : ℝ) : ℂ) ^ s + ∑' cd : 𝓞 K × 𝓞 K, if cd.1 = 0 then 0 else eisTerm s p cd := by
  unfold eis1
  rw [(summable_eisTerm hs hp).tsum_eq_add_tsum_ite ((0 : 𝓞 K), (1 : 𝓞 K)), eisTerm_zero_one]
  congr 1
  refine tsum_congr fun cd => ?_
  by_cases h2 : cd = (0, 1)
  · subst h2; simp
  · by_cases h1 : cd.1 = 0
    · have e : eisTerm s p cd = 0 := by
        unfold eisTerm
        simp only [ite_eq_right_iff]
        intro hb
        obtain ⟨c, d⟩ := cd
        simp only at h1
        subst h1
        exact absurd (by rw [bRow_zero_iff.1 hb]) h2
      simp only [h2, h1, ↓reduceIte, e]
    · simp only [h2, h1, ↓reduceIte]

/-- `x^t ≤ x^a + x^b` for `x > 0` and `a ≤ t ≤ b`. -/
theorem rpow_le_add_rpow {x a b t : ℝ} (hx : 0 < x) (ha : a ≤ t) (hb : t ≤ b) :
    x ^ t ≤ x ^ a + x ^ b := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hx h ha
    linarith [Real.rpow_nonneg hx.le b]
  · have := Real.rpow_le_rpow_of_exponent_le h hb
    linarith [Real.rpow_nonneg hx.le a]

open Classical in
/-- **Holomorphy in `s`** on `Re s > 2`. -/
theorem differentiableOn_eis1 {p : ℂ × ℝ} (hp : p ∈ UHS) :
    DifferentiableOn ℂ (fun s => eis1 s p) {s | 2 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 2 < s₀.re := hs₀
  set a := (2 + s₀.re) / 2
  set b := s₀.re + 1
  have ha : 2 < a := by simp only [a]; linarith
  have hb : 2 < b := by simp only [b]; linarith
  set U := {s : ℂ | a < s.re ∧ s.re < b}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hs₀U : s₀ ∈ U := ⟨by simp only [a]; linarith, by simp only [b]; linarith⟩
  have hD : DifferentiableOn ℂ (fun s => eis1 s p) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun cd => (if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ a else 0) +
        (if BRow cd then (p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2) ^ b else 0))
      ((summable_height_rpow ha hp).add (summable_height_rpow hb hp)) (fun cd => ?_) hU
      (fun cd s hs => ?_)
    · unfold eisTerm
      split_ifs with h
      · have hx : ((p.2 / uhsDen (σO cd.1) (σO cd.2) p.1 p.2 : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (div_pos hp (uhsDen_pos_of_BRow h hp)).ne'
        exact fun s _ => ((differentiableAt_id.const_cpow (Or.inl hx)).const_mul _).differentiableWithinAt
      · exact differentiableOn_const _
    · refine (norm_eisTerm_le s hp cd).trans ?_
      split_ifs with h
      · exact rpow_le_add_rpow (div_pos hp (uhsDen_pos_of_BRow h hp)) hs.1.le hs.2.le
      · simp
  exact (hD.differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

end Eis

end

#print axioms Eis.cub_b_mul_cub_c
#print axioms Eis.kub_eq_conj_cub
#print axioms Eis.norm_kub
#print axioms Eis.bRow_of_Gam3
#print axioms Eis.exists_Gam3_of_BRow
#print axioms Eis.rowMul_bottom
#print axioms Eis.rowMul_mul
#print axioms Eis.rowMul_one
#print axioms Eis.bRow_rowMul
#print axioms Eis.bRow_rowMul_iff
#print axioms Eis.cub_rowMul
#print axioms Eis.kub_inv_Gam3
#print axioms Eis.height_rowMul
#print axioms Eis.summable_lattice_rpow
#print axioms Eis.summable_O_rpow
#print axioms Eis.uhsDen_ge
#print axioms Eis.uhsDen_pos_of_BRow
#print axioms Eis.height_le_lattice
#print axioms Eis.norm_eisTerm_le
#print axioms Eis.summable_height_rpow
#print axioms Eis.summable_eisTerm
#print axioms Eis.eisTerm_rowMul
#print axioms Eis.eis1_slAct
#print axioms Eis.slT_mem_Gam3
#print axioms Eis.eis1_transl
#print axioms Eis.bRow_zero_iff
#print axioms Eis.eisTerm_zero_one
#print axioms Eis.eis1_eq
#print axioms Eis.rpow_le_add_rpow
#print axioms Eis.differentiableOn_eis1
