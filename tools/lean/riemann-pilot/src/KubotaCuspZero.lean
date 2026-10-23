import KubotaCTCover

/-! # The constant term of the Eisenstein series at the cusp `0` (round 440)

S5f-12 of round 360's plan, part 1. Round 439's next step planned θ at the cusp `0 = S∞`, starting from the
constant term of `E(S·w, s)` at `∞` for `Re s > 2`. This round computes it, with `S = (0, −1; 1, 0)`, round
387's `E(w, s) = Σ_{(c, d)} (c/d)₃·(v/Q_w(c, d))^s` over the bottom rows of `Γ_1(3)`, and `3P` round 389's
period parallelogram of `3ℤ[ω]`:

* **The terms at `S·w`** (`sS` and `eisTermS`, definitions; **`eisTerm_slAct_sS`**, with `sS_coe`, `rowMul_sS`
  and `eis1_slAct_sS`): the term of `(c, d)` at `S·w` is `(c/d)₃·(v/Q_w(d, −c))^s`, since `(c, d)S = (d, −c)`
  (round 387's `height_rowMul`).
* **Periodicity in `c`** (**`eisTermS_add`**, with `bRow_add_fst_iff`, `norm_eisTermS_le` and
  `measurable_eisTermS`): the term at `(c + 3dx, d)` and `w` is the term at `(c, d)` and `w − 3σ(x)`, since
  `(c/d)₃` depends on `c` modulo `d` (round 362's `cub_congr`).
* **The sum over `c`** (`cuspS0`, a definition; **`hasSum_integral_eisTermS_d`**, with
  `tsum_lintegral_height_neg`): for `d ≠ 0`,
  `Σ_c ∫_{3P} (term at (c, d)) dz = S₀(d)·πv^{2−s}N(d)^{−s}/(s − 1)`, with `S₀(d) = Σ_{c mod 3d} (c/d)₃` over
  the classes of the `c` with `(c, d)` a bottom row.
* **The constant term at the cusp `0`** (`eisPhi0`, a definition; **`integral_eis1_sS_fundP3`** and
  **`constTerm_eis1_sS`**, with `eisTermS_zero_snd` and `tsum_lintegral_eisTermS_ne_top`): for `Re s > 2` and
  `v > 0`, `(9√3/2)⁻¹∫_{3P} E(S·(z + vj), s) dz = φ₀(s)v^{2−s}` with
  `φ₀(s) = π/((9√3/2)(s − 1))·Σ_d S₀(d)N(d)^{−s}`. There is no term `v^s`: every bottom row `(c, d)` has
  `d ≠ 0`.
* **`S₀(d)` vanishes off the cubes** (`cuspF0`, a definition; **`cuspS0_twist`**,
  **`cuspS0_eq_zero_of_not_cube`** and **`cuspS0_cube`**, with `cuspS0_eq_tsum`, `cuspF0_add`, `cuspF0_congr`,
  `bRow_mul_fst_iff`, `cuspF0_mul` and `isUnit_mk_three_mul`): for `x` prime to `3d`, `S₀(d) = (x/d)₃·S₀(d)`,
  by `c ↦ cx` on the classes modulo `3d`. So `S₀(d) = 0` for `d` primary and not the cube of a primary element
  (round 414's `cube_of_cub_trivial`), and `S₀(m³)` counts the classes of the bottom rows `(c, m³)`.
-/

open MeasureTheory Set Module Filter NumberField Ideal PlanePoisson
open scoped ENNReal ComplexConjugate MatrixGroups Pointwise

noncomputable section

namespace Eis

/-! ### The terms at `S·w` -/

/-- `S = (0, −1; 1, 0)` in `SL_2(ℤ[ω])`. -/
def sS : SL(2, 𝓞 K) := toSL ModularGroup.S

theorem sS_coe : (sS : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![0, -1; 1, 0] := coe_toSL_S

theorem rowMul_sS (c d : 𝓞 K) : rowMul sS (c, d) = (d, -c) := by
  simp [rowMul, sS_coe]

open Classical in
/-- **The term of `E(S·w, s)` at the bottom row `(c, d)`**: `(c/d)₃·(v/Q_w(d, −c))^s`. -/
def eisTermS (s : ℂ) (p : ℂ × ℝ) (cd : 𝓞 K × 𝓞 K) : ℂ :=
  if BRow cd then
    σO (cub cd.1 (span {cd.2})) * ((p.2 / uhsDen (σO cd.2) (σO (-cd.1)) p.1 p.2 : ℝ) : ℂ) ^ s
  else 0

/-- **The terms at `S·p`**: the term of `(c, d)` at `S·p` is the term of the row `(d, −c)` at `p`. -/
theorem eisTerm_slAct_sS (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : 𝓞 K × 𝓞 K) :
    eisTerm s (slAct sS p) cd = eisTermS s p cd := by
  unfold eisTerm eisTermS
  split_ifs with h
  · rw [height_rowMul sS h hp, rowMul_sS]
  · rfl

theorem eis1_slAct_sS (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) :
    eis1 s (slAct sS p) = ∑' cd, eisTermS s p cd :=
  tsum_congr fun cd => eisTerm_slAct_sS s hp cd

/-! ### Periodicity in `c` modulo `3d` -/

theorem bRow_add_fst_iff {c d : 𝓞 K} (x : 𝓞 K) : BRow (c + 3 * d * x, d) ↔ BRow (c, d) := by
  have e : c + 3 * d * x = c + d * (3 * x) := by ring
  have h3 : (3 : 𝓞 K) ∣ d * (3 * x) := ⟨d * x, by ring⟩
  simp only [BRow, e, IsCoprime.add_mul_left_left_iff, dvd_add_left h3]

/-- **Periodicity**: the term at `(c + 3dx, d)` and `w` is the term at `(c, d)` and `w − 3σ(x)`. -/
theorem eisTermS_add (s : ℂ) (p : ℂ × ℝ) (c d x : 𝓞 K) :
    eisTermS s p (c + 3 * d * x, d) = eisTermS s (p.1 - σO (3 * x), p.2) (c, d) := by
  unfold eisTermS
  by_cases h : BRow (c, d)
  · rw [ite_eq_left ((bRow_add_fst_iff x).2 h), ite_eq_left h,
      cub_congr (show d ∣ (c + 3 * d * x) - c from ⟨3 * x, by ring⟩)]
    have e : σO (-(c + 3 * d * x)) = σO (-c) + σO d * -σO (3 * x) := by
      simp only [map_neg, map_add, map_mul]
      ring
    simp only
    rw [e, uhsDen_add, sub_eq_add_neg]
  · rw [ite_eq_right (fun h' => h ((bRow_add_fst_iff x).1 h')), ite_eq_right h]

open Classical in
theorem norm_eisTermS_le (s : ℂ) {p : ℂ × ℝ} (hp : p ∈ UHS) (cd : 𝓞 K × 𝓞 K) :
    ‖eisTermS s p cd‖ ≤ (p.2 / uhsDen (σO cd.2) (σO (-cd.1)) p.1 p.2) ^ s.re := by
  unfold eisTermS
  split_ifs with h
  · have hd : σO cd.2 ≠ 0 := σO_ne_zero (primary_ne_zero h.2.2)
    have hpos : 0 < p.2 / uhsDen (σO cd.2) (σO (-cd.1)) p.1 p.2 :=
      div_pos hp (uhsDen_pos hp (Or.inl hd))
    rw [norm_mul, norm_σO_cub h.2.2 h.1, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  · rw [norm_zero]
    exact Real.rpow_nonneg (div_nonneg (le_of_lt hp) (uhsDen_nonneg _ _ _ _)) _

theorem measurable_eisTermS (s : ℂ) (v : ℝ) (cd : 𝓞 K × 𝓞 K) :
    Measurable fun z : ℂ => eisTermS s (z, v) cd := by
  unfold eisTermS
  split_ifs
  · refine measurable_const.mul ?_
    have : Measurable fun z : ℂ => (v / uhsDen (σO cd.2) (σO (-cd.1)) z v) := by
      unfold uhsDen
      fun_prop
    exact (Complex.measurable_ofReal.comp this).pow_const s
  · exact measurable_const

/-! ### The sum over `c` -/

open Classical in
/-- **The character sum at the cusp `0`**: `S₀(d) = Σ_{c mod 3d} (c/d)₃` over the classes of the `c` with
`(c, d)` a bottom row of `Γ_1(3)`. -/
def cuspS0 (d : 𝓞 K) : ℂ :=
  ∑' r : 𝓞 K ⧸ span {3 * d},
    if BRow (repQ (3 * d) r, d) then σO (cub (repQ (3 * d) r) (span {d})) else 0

/-- `Σ_c ∫_{3P} (v/Q_w(d, −c))^σ dz = 9πv^{2−σ}N(d)^{1−σ}/(σ − 1)` for `d ≠ 0`, `v > 0` and `σ > 1`. -/
theorem tsum_lintegral_height_neg {d : 𝓞 K} (hd : d ≠ 0) {v σ : ℝ} (hv : 0 < v) (hσ : 1 < σ) :
    ∑' c : 𝓞 K, ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO d) (σO (-c)) z v) ^ σ) =
      ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) * Complex.normSq (σO d) ^ (1 - σ) / (σ - 1)) := by
  rw [← tsum_lintegral_height_c hd hv hσ]
  exact (Equiv.neg (𝓞 K)).tsum_eq
    (fun c => ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO d) (σO c) z v) ^ σ))

open Classical in
/-- **The sum over `c` of the integrals over `3P`**: for `d ≠ 0`, `v > 0` and `Re s > 1`,
`Σ_c ∫_{3P} (term at (c, d)) dz = S₀(d)·πv^{2−s}N(d)^{−s}/(s − 1)`. -/
theorem hasSum_integral_eisTermS_d {d : 𝓞 K} (hd : d ≠ 0) {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun c : 𝓞 K => ∫ z in fundP3, eisTermS s (z, v) (c, d))
      (cuspS0 d * (Real.pi * (v : ℂ) ^ (2 - s) * ((Complex.normSq (σO d) : ℝ) : ℂ) ^ (-s) /
        (s - 1))) := by
  have := finite_quot_three_mul hd
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * d})
  set F := fun c : 𝓞 K => ∫ z in fundP3, eisTermS s (z, v) (c, d) with hF
  set G := fun c : 𝓞 K =>
    ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO d) (σO (-c)) z v) ^ s.re) with hG
  have hGtop : ∑' c, G c ≠ ⊤ := by
    rw [hG, tsum_lintegral_height_neg hd hv hs]
    exact ENNReal.ofReal_ne_top
  have hB : ∀ c, ‖F c‖ ≤ (G c).toReal := by
    intro c
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.ne_top_of_tsum_ne_top hGtop c) (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_))
    exact norm_eisTermS_le s (p := (z, v)) hv (c, d)
  have hsum : Summable F := Summable.of_norm_bounded (ENNReal.summable_toReal hGtop) hB
  have hsum' : Summable fun p => F (resClassEquiv hd p) := (resClassEquiv hd).summable_iff.2 hsum
  rw [hsum.hasSum_iff, ← (resClassEquiv hd).tsum_eq, hsum'.tsum_prod' hsum'.prod_factor, tsum_fintype]
  unfold cuspS0
  rw [tsum_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  set f : ℂ → ℂ := fun z => eisTermS s (z, v) (repQ (3 * d) r, d) with hf_def
  have hf : Integrable f := by
    simp only [hf_def]
    unfold eisTermS
    split_ifs
    · exact (integrable_height_cpow (σO_ne_zero hd) _ hv hs).const_mul _
    · exact integrable_zero _ _ _
  have h1 : ∀ u : 𝓞 K, F (resClassEquiv hd (r, u)) = ∫ y in fundP3, f (y - σO (3 * u)) := by
    intro u
    simp only [hF, resClassEquiv_apply, hf_def]
    refine setIntegral_congr_fun measurableSet_fundP3 fun z _ => ?_
    rw [eisTermS_add]
  rw [tsum_congr h1, ← integral_tile3 hf]
  simp only [hf_def]
  unfold eisTermS
  split_ifs with hb
  · rw [integral_const_mul, integral_height_cpow (σO_ne_zero hd) _ hv hs]
  · simp

/-! ### The constant term at the cusp `0` -/

theorem eisTermS_zero_snd (s : ℂ) (p : ℂ × ℝ) (c : 𝓞 K) : eisTermS s p (c, 0) = 0 := by
  unfold eisTermS
  exact ite_eq_right fun h => primary_ne_zero h.2.2 rfl

open Classical in
/-- **The majorant of the integrals over `3P`**, in `[0, ∞]`: finite for `σ = Re s > 2` and `v > 0`. -/
theorem tsum_lintegral_eisTermS_ne_top {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∑' cd : 𝓞 K × 𝓞 K, ∫⁻ z in fundP3, ‖eisTermS s (z, v) cd‖ₑ ≠ ⊤ := by
  set σ := s.re with hσdef
  have hσ1 : 1 < σ := by linarith
  have hσ1' : 0 < σ - 1 := by linarith
  set B : ℝ≥0∞ := ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) / (σ - 1))
  have hslice : ∀ d : 𝓞 K, ∑' c : 𝓞 K, ∫⁻ z in fundP3, ‖eisTermS s (z, v) (c, d)‖ₑ ≤
      B * (if d = 0 then 0 else ENNReal.ofReal (‖σO d‖ ^ (-(2 * σ - 2)))) := by
    intro d
    by_cases hd : d = 0
    · subst hd
      simp only [eisTermS_zero_snd, enorm_zero, lintegral_zero, tsum_zero, ↓reduceIte, mul_zero,
        le_refl]
    · simp only [hd, ↓reduceIte]
      calc ∑' c : 𝓞 K, ∫⁻ z in fundP3, ‖eisTermS s (z, v) (c, d)‖ₑ
          ≤ ∑' c : 𝓞 K, ∫⁻ z in fundP3, ENNReal.ofReal ((v / uhsDen (σO d) (σO (-c)) z v) ^ σ) := by
            refine ENNReal.tsum_le_tsum fun c => lintegral_mono fun z => ?_
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (norm_eisTermS_le s (p := (z, v)) hv (c, d))
        _ = ENNReal.ofReal (9 * Real.pi * v ^ (2 - σ) * Complex.normSq (σO d) ^ (1 - σ) / (σ - 1)) :=
            tsum_lintegral_height_neg hd hv hσ1
        _ = B * ENNReal.ofReal (‖σO d‖ ^ (-(2 * σ - 2))) := by
            rw [← ENNReal.ofReal_mul (by positivity), rpow_normSq_eq]
            congr 1
            ring
  have e : ∑' cd : 𝓞 K × 𝓞 K, ∫⁻ z in fundP3, ‖eisTermS s (z, v) cd‖ₑ =
      ∑' d : 𝓞 K, ∑' c : 𝓞 K, ∫⁻ z in fundP3, ‖eisTermS s (z, v) (c, d)‖ₑ := by
    rw [← (Equiv.prodComm (𝓞 K) (𝓞 K)).tsum_eq, ENNReal.tsum_prod']
    rfl
  rw [e]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hslice)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsum_norm_σO_rpow_le (by linarith)))

open Classical in
/-- **The integral of `E(S·w, s)` over a period**: for `Re s > 2` and `v > 0`,
`∫_{3P} E(S·(z + vj), s) dz = πv^{2−s}/(s − 1)·Σ_d S₀(d)N(d)^{−s}`. -/
theorem integral_eis1_sS_fundP3 {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    ∫ z in fundP3, eis1 s (slAct sS (z, v)) =
      Real.pi * (v : ℂ) ^ (2 - s) / (s - 1) *
        ∑' d : 𝓞 K, cuspS0 d * ((Complex.normSq (σO d) : ℝ) : ℂ) ^ (-s) := by
  have hfin := tsum_lintegral_eisTermS_ne_top hs hv
  set I := fun cd : 𝓞 K × 𝓞 K => ∫ z in fundP3, eisTermS s (z, v) cd with hI
  have hI_le : ∀ cd, ‖I cd‖ ≤ (∫⁻ z in fundP3, ‖eisTermS s (z, v) cd‖ₑ).toReal := by
    intro cd
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    simp_rw [ofReal_norm]
  have hIsum : Summable I := Summable.of_norm_bounded (ENNReal.summable_toReal hfin) hI_le
  have h1 : ∫ z in fundP3, eis1 s (slAct sS (z, v)) = ∑' cd, I cd := by
    have e : ∫ z in fundP3, eis1 s (slAct sS (z, v)) = ∫ z in fundP3, ∑' cd, eisTermS s (z, v) cd :=
      setIntegral_congr_fun measurableSet_fundP3 fun z _ => eis1_slAct_sS s (p := (z, v)) hv
    rw [e]
    exact integral_tsum (fun cd => (measurable_eisTermS s v cd).aestronglyMeasurable) hfin
  have hIsum' : Summable (I ∘ (Equiv.prodComm (𝓞 K) (𝓞 K))) :=
    (Equiv.prodComm (𝓞 K) (𝓞 K)).summable_iff.2 hIsum
  set J := fun d : 𝓞 K => ∑' c : 𝓞 K, I (c, d) with hJ
  have hJd : ∀ d : 𝓞 K, J d = Real.pi * (v : ℂ) ^ (2 - s) / (s - 1) *
      (cuspS0 d * ((Complex.normSq (σO d) : ℝ) : ℂ) ^ (-s)) := by
    intro d
    by_cases hd : d = 0
    · have hs0 : -s ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      simp only [hJ, hI, hd, eisTermS_zero_snd, integral_zero, tsum_zero, map_zero,
        Complex.ofReal_zero, Complex.zero_cpow hs0, mul_zero]
    · show ∑' c : 𝓞 K, ∫ z in fundP3, eisTermS s (z, v) (c, d) = _
      rw [(hasSum_integral_eisTermS_d hd hv (by linarith)).tsum_eq]
      ring
  rw [h1, ← (Equiv.prodComm (𝓞 K) (𝓞 K)).tsum_eq]
  show ∑' p, (I ∘ (Equiv.prodComm (𝓞 K) (𝓞 K))) p = _
  rw [hIsum'.tsum_prod' hIsum'.prod_factor, ← tsum_mul_left]
  exact tsum_congr fun d => hJd d

/-- **The scattering coefficient at the cusp `0`**: `φ₀(s) = π/((9√3/2)(s − 1))·Σ_d S₀(d)N(d)^{−s}`. -/
def eisPhi0 (s : ℂ) : ℂ :=
  Real.pi / (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (s - 1)) *
    ∑' d : 𝓞 K, cuspS0 d * ((Complex.normSq (σO d) : ℝ) : ℂ) ^ (-s)

/-- **The constant term at the cusp `0`**: the mean of `E(S·(·, v), s)` over a period of `3ℤ[ω]` is
`φ₀(s)v^{2−s}`, for `Re s > 2` and `v > 0`. -/
theorem constTerm_eis1_sS {s : ℂ} (hs : 2 < s.re) {v : ℝ} (hv : 0 < v) :
    (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ))⁻¹ * ∫ z in fundP3, eis1 s (slAct sS (z, v)) =
      eisPhi0 s * ((v : ℝ) : ℂ) ^ (2 - s) := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h9 : (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 9 * (Real.sqrt 3 / 2) := by positivity
    exact_mod_cast this.ne'
  rw [integral_eis1_sS_fundP3 hs hv]
  unfold eisPhi0
  field_simp

/-! ### `S₀(d)` vanishes off the cubes -/

open Classical in
/-- The summand of `S₀(d)` at `c`: `(c/d)₃` if `(c, d)` is a bottom row of `Γ_1(3)`, else `0`. -/
def cuspF0 (d c : 𝓞 K) : ℂ := if BRow (c, d) then σO (cub c (span {d})) else 0

theorem cuspS0_eq_tsum (d : 𝓞 K) :
    cuspS0 d = ∑' r : 𝓞 K ⧸ span {3 * d}, cuspF0 d (repQ (3 * d) r) := rfl

theorem cuspF0_add (d c x : 𝓞 K) : cuspF0 d (c + 3 * d * x) = cuspF0 d c := by
  unfold cuspF0
  by_cases h : BRow (c, d)
  · rw [ite_eq_left ((bRow_add_fst_iff x).2 h), ite_eq_left h,
      cub_congr (show d ∣ (c + 3 * d * x) - c from ⟨3 * x, by ring⟩)]
  · rw [ite_eq_right (fun h' => h ((bRow_add_fst_iff x).1 h')), ite_eq_right h]

theorem cuspF0_congr {d c c' : 𝓞 K} (h : 3 * d ∣ c' - c) : cuspF0 d c' = cuspF0 d c := by
  obtain ⟨x, hx⟩ := h
  rw [show c' = c + 3 * d * x by linear_combination hx, cuspF0_add]

/-- For `x` prime to `3` and to `d`, `(cx, d)` is a bottom row if and only if `(c, d)` is. -/
theorem bRow_mul_fst_iff {c d x : 𝓞 K} (hx3 : IsCoprime x 3) (hxd : IsCoprime x d) :
    BRow (c * x, d) ↔ BRow (c, d) := by
  simp only [BRow]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.of_mul_left_left, hx3.symm.dvd_of_dvd_mul_right h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.mul_left hxd, dvd_mul_of_dvd_left h2 x, h3⟩

theorem cuspF0_mul {d c x : 𝓞 K} (hx3 : IsCoprime x 3) (hxd : IsCoprime x d) :
    cuspF0 d (c * x) = σO (cub x (span {d})) * cuspF0 d c := by
  unfold cuspF0
  by_cases h : BRow (c, d)
  · rw [ite_eq_left ((bRow_mul_fst_iff hx3 hxd).2 h), ite_eq_left h, cub_mul_left, map_mul, mul_comm]
  · rw [ite_eq_right (fun h' => h ((bRow_mul_fst_iff hx3 hxd).1 h')), ite_eq_right h, mul_zero]

theorem isUnit_mk_three_mul {d x : 𝓞 K} (hx3 : IsCoprime x 3) (hxd : IsCoprime x d) :
    IsUnit (Ideal.Quotient.mk (span {3 * d}) x) := by
  obtain ⟨u, v, huv⟩ := IsCoprime.mul_right hx3 hxd
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ u) ?_
  rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨-v, by linear_combination huv⟩

/-- **Twisting**: for `x` prime to `3` and to `d`, `S₀(d) = (x/d)₃·S₀(d)`, by `r ↦ r·x` on the classes modulo
`3d`. -/
theorem cuspS0_twist {d x : 𝓞 K} (hx3 : IsCoprime x 3) (hxd : IsCoprime x d) :
    cuspS0 d = σO (cub x (span {d})) * cuspS0 d := by
  rw [cuspS0_eq_tsum]
  set u := (isUnit_mk_three_mul hx3 hxd).unit
  have key : ∀ r : 𝓞 K ⧸ span {3 * d},
      cuspF0 d (repQ (3 * d) (r * u)) = σO (cub x (span {d})) * cuspF0 d (repQ (3 * d) r) := by
    intro r
    rw [← cuspF0_mul hx3 hxd]
    apply cuspF0_congr
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, repQ_mk, map_mul, repQ_mk, IsUnit.unit_spec]
  calc ∑' r : 𝓞 K ⧸ span {3 * d}, cuspF0 d (repQ (3 * d) r)
      = ∑' r : 𝓞 K ⧸ span {3 * d}, cuspF0 d (repQ (3 * d) (r * u)) :=
        ((Units.mulRight u).tsum_eq (fun r => cuspF0 d (repQ (3 * d) r))).symm
    _ = ∑' r : 𝓞 K ⧸ span {3 * d}, σO (cub x (span {d})) * cuspF0 d (repQ (3 * d) r) :=
        tsum_congr key
    _ = _ := tsum_mul_left

/-- **`S₀(d)` vanishes off the cubes**: for `d` primary and not the cube of a primary element, `S₀(d) = 0`. -/
theorem cuspS0_eq_zero_of_not_cube {d : 𝓞 K} (hd : Primary d)
    (h : ¬ ∃ m : 𝓞 K, Primary m ∧ d = m ^ 3) : cuspS0 d = 0 := by
  by_contra hS
  apply h
  refine cube_of_cub_trivial _ d rfl hd fun x hx hdx => ?_
  by_contra hne
  apply hS
  have hx3 : IsCoprime x 3 :=
    (isCoprime_of_dvd_sub_one (dvd_trans ⟨3, by norm_num⟩ hx : (3 : 𝓞 K) ∣ x - 1)).symm
  have ht := cuspS0_twist hx3 hdx.symm
  have h1 : σO (cub x (span {d})) ≠ 1 := fun h' => hne (σO_injective (by
    change σO _ = σO 1; rw [h', map_one]))
  have h2 : (1 - σO (cub x (span {d}))) * cuspS0 d = 0 := by
    rw [sub_mul, one_mul, ← ht, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm h1))

open Classical in
/-- **At the cubes, `S₀(d)` counts the classes**: for `m` primary, `S₀(m³)` is the number of classes `c`
modulo `3m³` with `(c, m³)` a bottom row of `Γ_1(3)`. -/
theorem cuspS0_cube {m : 𝓞 K} (hm : Primary m) :
    cuspS0 (m ^ 3) = ∑' r : 𝓞 K ⧸ span {3 * m ^ 3},
      if BRow (repQ (3 * m ^ 3) r, m ^ 3) then (1 : ℂ) else 0 := by
  rw [cuspS0_eq_tsum]
  refine tsum_congr fun r => ?_
  unfold cuspF0
  by_cases hb : BRow (repQ (3 * m ^ 3) r, m ^ 3)
  · rw [ite_eq_left hb, ite_eq_left hb, cub_pow_span _ (primary_ne_zero hm),
      cub_pow_three hm (hb.1.of_isCoprime_of_dvd_right (dvd_pow_self m three_ne_zero)), map_one]
  · rw [ite_eq_right hb, ite_eq_right hb]

end Eis

end

#print axioms Eis.sS_coe
#print axioms Eis.rowMul_sS
#print axioms Eis.eisTerm_slAct_sS
#print axioms Eis.eis1_slAct_sS
#print axioms Eis.bRow_add_fst_iff
#print axioms Eis.eisTermS_add
#print axioms Eis.norm_eisTermS_le
#print axioms Eis.measurable_eisTermS
#print axioms Eis.tsum_lintegral_height_neg
#print axioms Eis.hasSum_integral_eisTermS_d
#print axioms Eis.eisTermS_zero_snd
#print axioms Eis.tsum_lintegral_eisTermS_ne_top
#print axioms Eis.integral_eis1_sS_fundP3
#print axioms Eis.constTerm_eis1_sS
#print axioms Eis.cuspS0_eq_tsum
#print axioms Eis.cuspF0_add
#print axioms Eis.cuspF0_congr
#print axioms Eis.bRow_mul_fst_iff
#print axioms Eis.cuspF0_mul
#print axioms Eis.isUnit_mk_three_mul
#print axioms Eis.cuspS0_twist
#print axioms Eis.cuspS0_eq_zero_of_not_cube
#print axioms Eis.cuspS0_cube
