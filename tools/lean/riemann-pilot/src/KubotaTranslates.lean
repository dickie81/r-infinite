import KubotaTheta

/-! # The companion paper's Lemma 6.1 from the Kubota–Patterson display (round 363)

S5f-2b of round 360's plan, part 1. The twisted theta function of the companion paper's (6.2) and
(A.2) is a finite sum of translates of `θ̄` (its (6.4) and (A.4)), and its coefficients at `λnb³` are the
coefficients of the completed sum (the identity in the proof of its (6.3)).

* **Primitivity** (`dvd_of_ψc_mul_eq_one`, **`ψQ_isPrimitive_of_ne_zero`**): round 295's trace
  character `ψ_c` is primitive modulo every `c ≠ 0`, not only at primes: if `ψ_c(hx) = 1` for all `x`,
  then `N(c)` divides both coordinates of `h c̄`, so `c ∣ h`.
* **Finite Fourier inversion modulo `c`** (`fCoef`, `sum_ψc_mul`, **`fourier_inv`**, `sum_fCoef`,
  `norm_fCoef_le`): for `F` periodic modulo `c`, `F(x) = Σ_{h mod c} F̂(h)ψ_c(hx)` with
  `F̂(h) = N(c)⁻¹Σ_{y mod c} F(y)ψ_c(−hy)`; `Σ_h F̂(h) = F(0)`; `|F̂| ≤ sup|F|`.
* **The shift in the phase** (`ebr_add`, **`ebr_shift`**): `ĕ(σ(δ₃x)·σ(δ₃²h)/(9σ(q))) = ψ_q(hx)`, since
  `σ(δ₃)⁴ = 9`: multiplying the mode `m = λx` by `e(xh/q)` translates `z` by `λ²h/q`.
* **Translates** (**`thSer_translates`**): for any finite family, if `G(m) = Σ_i a_i ĕ(mw_i/9)` on the
  support of `d`, then `Σ_i a_i·thSer(c, d)(z + w_i) = (Σ_i a_i)·c·v^{2/3} + Σ_m G(m)d(m)·vK_{1/3}·ĕ(mz/9)`.
* **`K_{1/3}` is real and `θ̄` is a theta-type series** (`besselK_ofReal`, `conj_besselK_third`,
  `conj_ebr`, **`conj_thSer`**, `thetaSupp_conj`): the coefficient of `θ̄` at `m` is `conj τ(−m)`, the
  paper's `d_0(ℓ) = conj τ(−ℓ)`, and it satisfies the same support and size condition.
* **The twisted series as translates** (`twAt`, **`thSer_twist`**, **`conj_theta_translates`**): for
  `F` periodic modulo `q ≠ 0` and `θ = thSer(c₀, τ)` with `τ` supported on `δ₃𝒪`,
  `Σ_{h mod q} F̂(h)·θ̄(z + λ²h/q, v) = F(0)·conj c₀·v^{2/3} + Σ_m F(m/λ)·conj τ(−m)·vK_{1/3}(4π|m|v/9)·ĕ(mz/9)`;
  the constant terms cancel when `F(0) = 0`.
* **The coefficient identity** (`phiTw`, **`coef_realization`**): with `φ(x) = χ_x(λ)²Ψ(x)` on primary
  `x` of norm prime to `6`, `conj τ(−λnb³)·φ(nb³) = conj C·N(b)^{1/2}γ₂(n)Ψ(n)Ψ(b)³` for completely
  multiplicative `Ψ`, from the display's values (the paper's `c_θ(nb³)φ_k(nb³) = 3^{5/2}|b|γ₂(n)Ψ_k(n)Ψ_k(b)³`).
* **Lemma 6.1 from the display** (**`lemma61_of_kubotaTheta`**).
-/

open Complex Set NumberField Ideal MeasureTheory UniqueFactorizationMonoid
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-! ### Primitivity -/

/-- If `ψ_c(hx) = 1` for every `x`, then `c ∣ h`: `N(c)` divides both coordinates of `h c̄`. -/
theorem dvd_of_ψc_mul_eq_one (c h : 𝓞 K) (hc : c ≠ 0) (hall : ∀ x, ψc c (h * x) = 1) : c ∣ h := by
  obtain ⟨a, b, hab⟩ := exists_coords (h * cj c)
  set N : ℕ := absNorm (span {c}) with hNdef
  have h1 : trPhase c h * N = b := by
    rw [trPhase_mul_absNorm c h hc, hab, re_two_σO_div_δ3]
  have h2 : trPhase c (h * ω) * N = ((a - b : ℤ) : ℝ) := by
    rw [trPhase_mul_absNorm c (h * ω) hc]
    have : h * ω * cj c = ((-b : ℤ) : 𝓞 K) + ((a - b : ℤ) : 𝓞 K) * ω := by
      rw [mul_right_comm, hab]; push_cast; linear_combination (b : 𝓞 K) * ω_sq_add
    rw [this, re_two_σO_div_δ3]
  have e1 := hall 1
  rw [mul_one] at e1
  obtain ⟨n1, hn1⟩ := (fourierChar_eq_one_iff _).1 e1
  obtain ⟨n2, hn2⟩ := (fourierChar_eq_one_iff _).1 (hall ω)
  rw [hn1] at h1
  rw [hn2] at h2
  have hb : b = n1 * N := by exact_mod_cast h1.symm
  have ha : a - b = n2 * N := by exact_mod_cast h2.symm
  have hcj : h * cj c = (N : 𝓞 K) * (((n1 + n2 : ℤ) : 𝓞 K) + (n1 : 𝓞 K) * ω) := by
    rw [hab]
    have ha' : a = (n1 + n2) * N := by linarith
    rw [ha', hb]; push_cast; ring
  have hcj0 : cj c ≠ 0 := fun h0 => hc (by simpa using congrArg cj.symm h0)
  have hN := mul_cj_eq_absNorm c
  rw [← hNdef] at hN
  rw [← hN] at hcj
  refine ⟨((n1 + n2 : ℤ) : 𝓞 K) + (n1 : 𝓞 K) * ω, ?_⟩
  apply mul_right_cancel₀ hcj0
  rw [hcj]; ring

/-- **The trace character is primitive modulo every `c ≠ 0`.** -/
theorem ψQ_isPrimitive_of_ne_zero (c : 𝓞 K) (hc : c ≠ 0) : (ψQ c hc).IsPrimitive := by
  intro a ha h1
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply ha
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine dvd_of_ψc_mul_eq_one c h hc fun x => ?_
  have := DFunLike.congr_fun h1 (Ideal.Quotient.mk _ x)
  rw [AddChar.mulShift_apply, AddChar.one_apply, ← map_mul, ψQ_mk] at this
  exact this

/-! ### Finite Fourier inversion modulo `c` -/

theorem finite_quot (c : 𝓞 K) (hc : c ≠ 0) : Finite (𝓞 K ⧸ span {c}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])

theorem card_quot (c : 𝓞 K) [Fintype (𝓞 K ⧸ span {c})] :
    Fintype.card (𝓞 K ⧸ span {c}) = absNorm (span {c}) := by
  rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem absNorm_span_ne_zero {c : 𝓞 K} (hc : c ≠ 0) : (absNorm (span {c}) : ℂ) ≠ 0 := by
  have : absNorm (span {c}) ≠ 0 := by
    rw [Ne, absNorm_eq_zero_iff, span_singleton_eq_bot]; exact hc
  exact_mod_cast this

theorem norm_ψc (c x : 𝓞 K) : ‖ψc c x‖ = 1 := by
  unfold ψc; exact Circle.norm_coe _

/-- The character sums: `Σ_{h mod c} ψ_c(hb) = N(c)·1_{c ∣ b}`. -/
theorem sum_ψc_mul (c : 𝓞 K) (hc : c ≠ 0) [Fintype (𝓞 K ⧸ span {c})]
    [DecidableEq (𝓞 K ⧸ span {c})] (b : 𝓞 K) :
    ∑ h : 𝓞 K ⧸ span {c}, ψc c (repQ c h * b) =
      if Ideal.Quotient.mk (span {c}) b = 0 then (absNorm (span {c}) : ℂ) else 0 := by
  have := AddChar.sum_mulShift (Ideal.Quotient.mk (span {c}) b) (ψQ_isPrimitive_of_ne_zero c hc)
  rw [card_quot c, Nat.cast_ite, Nat.cast_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← ψQ_mk c hc, map_mul, repQ_mk]

/-- The finite Fourier coefficient `F̂(h) = N(c)⁻¹·Σ_{y mod c} F(y)ψ_c(−hy)`. -/
def fCoef (c : 𝓞 K) (F : 𝓞 K → ℂ) (h : 𝓞 K) : ℂ :=
  (absNorm (span {c}) : ℂ)⁻¹ * ∑ᶠ y : 𝓞 K ⧸ span {c}, F (repQ c y) * ψc c (-(h * repQ c y))

/-- **Finite Fourier inversion modulo `c`**: `F(x) = Σ_{h mod c} F̂(h)ψ_c(hx)` for `F` periodic
modulo `c`. -/
theorem fourier_inv (c : 𝓞 K) (hc : c ≠ 0) (F : 𝓞 K → ℂ) (hF : ∀ z u, F (z + c * u) = F z)
    (x : 𝓞 K) :
    ∑ᶠ h : 𝓞 K ⧸ span {c}, fCoef c F (repQ c h) * ψc c (repQ c h * x) = F x := by
  have := finite_quot c hc
  classical
  let : Fintype (𝓞 K ⧸ span {c}) := Fintype.ofFinite _
  have hN := absNorm_span_ne_zero hc
  simp only [fCoef, finsum_eq_sum_of_fintype]
  have e : ∀ h y : 𝓞 K ⧸ span {c}, F (repQ c y) * ψc c (-(repQ c h * repQ c y)) * ψc c (repQ c h * x) =
      F (repQ c y) * ψc c (repQ c h * (x - repQ c y)) := by
    intro h y; rw [mul_assoc, ← ψc_add]; congr 2; ring
  calc ∑ h, (absNorm (span {c}) : ℂ)⁻¹ * (∑ y, F (repQ c y) * ψc c (-(repQ c h * repQ c y))) *
          ψc c (repQ c h * x)
      = (absNorm (span {c}) : ℂ)⁻¹ * ∑ y, F (repQ c y) * ∑ h, ψc c (repQ c h * (x - repQ c y)) := by
        simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul, e, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = (absNorm (span {c}) : ℂ)⁻¹ * (F x * absNorm (span {c})) := by
        simp_rw [sum_ψc_mul c hc]
        congr 1
        rw [Finset.sum_eq_single (Ideal.Quotient.mk _ x)]
        · rw [map_sub, repQ_mk, sub_self, ite_eq_left rfl,
            periodic_congr c F hF (repQ_mk c (Ideal.Quotient.mk (span {c}) x))]
        · intro y _ hy
          rw [map_sub, repQ_mk, ite_eq_right (fun h0 => hy (sub_eq_zero.1 h0).symm), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = F x := by field_simp

/-- `Σ_{h mod c} F̂(h) = F(0)`. -/
theorem sum_fCoef (c : 𝓞 K) (hc : c ≠ 0) (F : 𝓞 K → ℂ) (hF : ∀ z u, F (z + c * u) = F z) :
    ∑ᶠ h : 𝓞 K ⧸ span {c}, fCoef c F (repQ c h) = F 0 := by
  have := fourier_inv c hc F hF 0
  simp only [mul_zero, ψc_zero, mul_one] at this
  exact this

/-- `|F̂(h)| ≤ B` when `|F| ≤ B`. -/
theorem norm_fCoef_le (c : 𝓞 K) (hc : c ≠ 0) (F : 𝓞 K → ℂ) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B)
    (h : 𝓞 K) : ‖fCoef c F h‖ ≤ B := by
  have := finite_quot c hc
  classical
  let : Fintype (𝓞 K ⧸ span {c}) := Fintype.ofFinite _
  have hN := absNorm_span_ne_zero hc
  have hNpos : (0 : ℝ) < absNorm (span {c}) := by
    have : absNorm (span {c}) ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff, span_singleton_eq_bot]; exact hc
    exact_mod_cast Nat.pos_of_ne_zero this
  unfold fCoef
  rw [finsum_eq_sum_of_fintype, norm_mul, norm_inv, Complex.norm_natCast]
  calc (absNorm (span {c}) : ℝ)⁻¹ * ‖∑ y, F (repQ c y) * ψc c (-(h * repQ c y))‖
      ≤ (absNorm (span {c}) : ℝ)⁻¹ * ∑ _y : 𝓞 K ⧸ span {c}, B := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
        rw [norm_mul, norm_ψc, mul_one]; exact hB _
    _ = B := by
        rw [Finset.sum_const, Finset.card_univ, card_quot c, nsmul_eq_mul]
        field_simp

/-! ### The phases `ĕ` and the translates -/

theorem ebr_add (x y : ℂ) : ebr (x + y) = ebr x * ebr y := by
  unfold ebr
  rw [← Complex.exp_add]
  congr 1
  simp only [Complex.add_re]
  push_cast; ring

/-- **The shift `λ²h/q` in the phase**: for `m = δ₃x`,
`ĕ(σ(δ₃x)·σ(δ₃²h)/(9σ(q))) = ψ_q(hx)`. -/
theorem ebr_shift (q h x : 𝓞 K) :
    ebr (σO (δ3 * x) * (σO (δ3 ^ 2 * h) / σO q) / 9) = ψc q (h * x) := by
  unfold ebr ψc trPhase
  rw [Real.fourierChar_apply]
  congr 1
  have h4 : σO δ3 ^ 4 = 9 := by
    have : σO δ3 ^ 2 = -3 := by rw [← map_pow, δ3_sq, map_neg, map_ofNat]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, this]; norm_num
  have hd := σO_δ3_ne_zero
  have e : 2 * (σO (δ3 * x) * (σO (δ3 ^ 2 * h) / σO q) / 9) = 2 * σO (h * x) / σO (δ3 * q) := by
    simp only [map_mul, map_pow]
    by_cases hq : σO q = 0
    · rw [hq]; simp
    · field_simp
      linear_combination σO x * σO h * h4
  have e2 : ((2 * (σO (δ3 * x) * (σO (δ3 ^ 2 * h) / σO q) / 9)).re : ℝ) =
      (2 * σO (h * x) / σO (δ3 * q)).re := by rw [e]
  rw [show (2 * (σO (δ3 * x) * (σO (δ3 ^ 2 * h) / σO q) / 9)).re =
      2 * (σO (δ3 * x) * (σO (δ3 ^ 2 * h) / σO q) / 9).re by simp [Complex.mul_re]] at e2
  rw [← e2]
  push_cast; ring

/-- **Translates of a theta-type series**: if `G(m) = Σ_i a_i·ĕ(m w_i/9)` on the support of `d`, then
`Σ_i a_i·thSer(c, d)(z + w_i) = (Σ_i a_i)·c·v^{2/3} + Σ_m G(m)d(m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)`. -/
theorem thSer_translates {ι : Type*} (s : Finset ι) (a : ι → ℂ) (w : ι → ℂ) (c₀ : ℂ)
    (d G : 𝓞 K → ℂ) (z : ℂ) (v : ℝ)
    (hs : ∀ i ∈ s, Summable fun m : 𝓞 K =>
      d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * (z + w i) / 9))
    (hG : ∀ m, d m ≠ 0 → G m = ∑ i ∈ s, a i * ebr (σO m * w i / 9)) :
    ∑ i ∈ s, a i * thSer c₀ d (z + w i) v =
      (∑ i ∈ s, a i) * (c₀ * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) +
        ∑' m : 𝓞 K, G m * d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) *
          ebr (σO m * z / 9) := by
  unfold thSer
  have e1 : ∀ i ∈ s, a i * (c₀ * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ) + ∑' m : 𝓞 K, d m * (v : ℂ) *
      besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * (z + w i) / 9)) =
      a i * (c₀ * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) + ∑' m : 𝓞 K, a i * (d m * (v : ℂ) *
      besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * (z + w i) / 9)) := by
    intro i _
    rw [mul_add, tsum_mul_left]
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Summable.tsum_finsetSum fun i hi => (hs i hi).mul_left (a i)]
  congr 1
  refine tsum_congr fun m => ?_
  by_cases hm : d m = 0
  · simp [hm]
  rw [hG m hm, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show σO m * (z + w i) / 9 = σO m * z / 9 + σO m * w i / 9 by ring, ebr_add]
  ring

/-! ### `K_ν` is real for real `ν` -/

theorem besselK_ofReal (r x : ℝ) : besselK (r : ℂ) x = ((1 / 2 * bkR r x : ℝ) : ℂ) := by
  unfold besselK mellin bkR
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  · push_cast; ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht)]
    push_cast; ring

theorem conj_besselK_third (x : ℝ) : conj (besselK (1 / 3) x) = besselK (1 / 3) x := by
  have : (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) := by push_cast; ring
  rw [this, besselK_ofReal, Complex.conj_ofReal]

theorem conj_ebr (w : ℂ) : conj (ebr w) = ebr (-w) := by
  unfold ebr
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.neg_re]
  push_cast; ring

/-! ### `θ̄` as a theta-type series -/

/-- **The conjugate of a theta-type series** is the theta-type series with coefficients `conj d(−m)`:
the coefficient of `θ̄` at `m` is `conj τ(−m)`, the companion paper's `d_0(ℓ) = conj τ(−ℓ)`. -/
theorem conj_thSer (c : ℂ) (d : 𝓞 K → ℂ) (z : ℂ) (v : ℝ) :
    conj (thSer c d z v) = thSer (conj c) (fun m => conj (d (-m))) z v := by
  unfold thSer
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_tsum]
  congr 1
  rw [← (Equiv.neg (𝓞 K)).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply, map_mul, Complex.conj_ofReal, conj_besselK_third, conj_ebr,
    map_neg, norm_neg]
  congr 2
  ring

theorem thetaSupp_conj {Kc : ℝ} {d : 𝓞 K → ℂ} (h : ThetaSupp Kc d) :
    ThetaSupp Kc fun m => conj (d (-m)) := by
  refine ⟨h.1, fun m hm => ?_⟩
  have hm' : d (-m) ≠ 0 := fun h0 => hm (by simp [h0])
  obtain ⟨q, hq, h1, h2, h3, h4⟩ := h.2 (-m) hm'
  refine ⟨(-q.1, q.2), ?_, h1, h2, h3, ?_⟩
  · unfold dualPt at hq ⊢
    simp only [Units.val_neg]
    linear_combination (-1 : 𝓞 K) * hq
  · rw [Complex.norm_conj]; exact h4

/-! ### The twisted series as translates -/

theorem δ3_ne_zero : (δ3 : 𝓞 K) ≠ 0 := by
  intro h
  have := δ3_sq
  rw [h, zero_pow two_ne_zero] at this
  norm_num at this

open Classical in
/-- The twist at the frequency `m = δ₃x` is `F(x)`, and `0` off `δ₃𝒪`. -/
def twAt (F : 𝓞 K → ℂ) (m : 𝓞 K) : ℂ := if h : δ3 ∣ m then F h.choose else 0

theorem twAt_mul (F : 𝓞 K → ℂ) (x : 𝓞 K) : twAt F (δ3 * x) = F x := by
  unfold twAt
  have h : δ3 ∣ δ3 * x := dvd_mul_right _ _
  rw [dite_eq_left h]
  congr 1
  exact (mul_left_cancel₀ δ3_ne_zero h.choose_spec).symm

/-- **The twisted series as translates** (the companion paper's (6.4) and (A.4)): for `F` periodic
modulo `q` and `d` supported on `δ₃𝒪`, `Σ_{h mod q} F̂(h)·thSer(c, d)(z + λ²h/q) = F(0)·c·v^{2/3} +
Σ_m F(m/λ)·d(m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)`. -/
theorem thSer_twist (q : 𝓞 K) (hq : q ≠ 0) (F : 𝓞 K → ℂ) (hF : ∀ z u, F (z + q * u) = F z)
    (c₀ : ℂ) (d : 𝓞 K → ℂ) (hd : ∀ m, d m ≠ 0 → δ3 ∣ m) (z : ℂ) (v : ℝ)
    (hs : ∀ w : ℂ, Summable fun m : 𝓞 K =>
      d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * w / 9)) :
    ∑ᶠ h : 𝓞 K ⧸ span {q}, fCoef q F (repQ q h) *
        thSer c₀ d (z + σO (δ3 ^ 2 * repQ q h) / σO q) v =
      F 0 * (c₀ * ((v ^ (2 / 3 : ℝ) : ℝ) : ℂ)) +
        ∑' m : 𝓞 K, twAt F m * d m * (v : ℂ) * besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) *
          ebr (σO m * z / 9) := by
  have := finite_quot q hq
  classical
  let : Fintype (𝓞 K ⧸ span {q}) := Fintype.ofFinite _
  have h0 := sum_fCoef q hq F hF
  rw [finsum_eq_sum_of_fintype] at h0
  rw [finsum_eq_sum_of_fintype, thSer_translates Finset.univ (fun h => fCoef q F (repQ q h))
    (fun h => σO (δ3 ^ 2 * repQ q h) / σO q) c₀ d (twAt F) z v (fun i _ => hs _), h0]
  intro m hm
  obtain ⟨x, rfl⟩ := hd m hm
  rw [twAt_mul, ← fourier_inv q hq F hF x, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [ebr_shift]

/-- **Lemma 6.1's translates for `θ̄`**: if `θ = thSer(c₀, τ)` with `τ` under the support and size
condition and supported on `δ₃𝒪`, then for `F` periodic modulo `q` with `F(0) = 0`,
`Σ_{h mod q} F̂(h)·θ̄(z + λ²h/q, v) = Σ_m F(m/λ)·conj τ(−m)·v·K_{1/3}(4π|m|v/9)·ĕ(mz/9)`. -/
theorem conj_theta_translates {θ : ℂ → ℝ → ℂ} {Kc : ℝ} {c₀ : ℂ} {τ : 𝓞 K → ℂ}
    (hθ : ∀ z v, 0 < v → θ z v = thSer c₀ τ z v) (hτ : ThetaSupp Kc τ)
    (hτd : ∀ m, τ m ≠ 0 → δ3 ∣ m) (q : 𝓞 K) (hq : q ≠ 0) (F : 𝓞 K → ℂ)
    (hF : ∀ z u, F (z + q * u) = F z) (hF0 : F 0 = 0) (z : ℂ) {v : ℝ} (hv : 0 < v) :
    ∑ᶠ h : 𝓞 K ⧸ span {q}, fCoef q F (repQ q h) * conj (θ (z + σO (δ3 ^ 2 * repQ q h) / σO q) v) =
      ∑' m : 𝓞 K, twAt F m * conj (τ (-m)) * (v : ℂ) *
        besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9) := by
  have e : ∀ h : 𝓞 K ⧸ span {q}, fCoef q F (repQ q h) *
      conj (θ (z + σO (δ3 ^ 2 * repQ q h) / σO q) v) =
      fCoef q F (repQ q h) * thSer (conj c₀) (fun m => conj (τ (-m)))
        (z + σO (δ3 ^ 2 * repQ q h) / σO q) v := by
    intro h; rw [hθ _ _ hv, conj_thSer]
  rw [finsum_congr e, thSer_twist q hq F hF _ _ ?_ z v
    (fun w => summable_thSer (thetaSupp_conj hτ) w hv), hF0, zero_mul, zero_add]
  intro m hm
  have hm' : τ (-m) ≠ 0 := fun h0 => hm (by simp [h0])
  exact (dvd_neg.1 (hτd _ hm'))

/-! ### The coefficient identity of Lemma 6.1 -/

theorem primary_pow {a : 𝓞 K} (ha : Primary a) (k : ℕ) : Primary (a ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact primary_one
  | succ k ih => rw [pow_succ]; exact ih.mul ha

open Classical in
/-- The twist of the companion paper's Lemma 6.1: `φ(x) = χ_x(λ)²Ψ(x)` on primary `x` of norm prime
to `6`, and `0` otherwise. -/
def phiTw (Ψ : Ideal (𝓞 K) → ℂ) (x : 𝓞 K) : ℂ :=
  if Primary x ∧ (absNorm (span {x})).Coprime 6 then sym6 δ3 (span {x}) ^ 2 * Ψ (span {x}) else 0

theorem δ3_not_mem_of_factor {I P : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6)
    (hP : P ∈ normalizedFactors I) : δ3 ∉ P := by
  intro h
  have h3 : (3 : 𝓞 K) ∈ P := by
    have : (3 : 𝓞 K) = -(δ3 * δ3) := by rw [← sq, δ3_sq]; ring
    rw [this]; exact P.neg_mem (P.mul_mem_left _ h)
  apply six_not_mem_of_factor hI hP
  rw [show (6 : 𝓞 K) = 2 * 3 by norm_num]
  exact P.mul_mem_left _ h3

theorem sym6_δ3_pow_six {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) : sym6 δ3 I ^ 6 = 1 := by
  rw [← sym6_pow_succ δ3 I 5, sym6_pow_six hI, ite_eq_left fun P hP => δ3_not_mem_of_factor hI hP]

theorem norm_sym6_δ3 {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) : ‖sym6 δ3 I‖ = 1 := by
  have h := congrArg norm (sym6_δ3_pow_six hI)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h

theorem coprime6_left {a b : ℕ} (h : (a * b).Coprime 6) : a.Coprime 6 :=
  Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) h

theorem coprime6_right {a b : ℕ} (h : (a * b).Coprime 6) : b.Coprime 6 :=
  Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) h

theorem span_ne_zero_of_coprime6 {x : 𝓞 K} (h : (absNorm (span {x})).Coprime 6) :
    span {x} ≠ (0 : Ideal (𝓞 K)) := by
  intro h0
  rw [h0, Ideal.zero_eq_bot, absNorm_bot] at h
  norm_num at h

/-- **The coefficient identity of Lemma 6.1**: for `n, b` primary with `N(nb)` prime to `6` and `Ψ`
completely multiplicative, the coefficient of `θ̄` at `λnb³` times the twist `φ(nb³)` is
`conj C·N(b)^{1/2}·γ₂(n)·Ψ(n)Ψ(b)³` (the paper's `c_θ(nb³)φ_k(nb³) = 3^{5/2}|b|γ₂(n)Ψ_k(n)Ψ_k(b)³`). -/
theorem coef_realization {τ : 𝓞 K → ℂ} {C : ℂ} (Ψ : Ideal (𝓞 K) → ℂ)
    (hΨ : ∀ I J, Ψ (I * J) = Ψ I * Ψ J) {n b : 𝓞 K} (hn : Primary n) (hb : Primary b)
    (h6 : (absNorm (span {n * b})).Coprime 6)
    (hτ : τ (-(δ3 * n * b ^ 3)) = C * (Real.sqrt (absNorm (span {b})) : ℂ) *
      sym6 δ3 (span {n}) ^ 2 * conj (gamI 2 (span {n}))) :
    conj (τ (-(δ3 * (n * b ^ 3)))) * phiTw Ψ (n * b ^ 3) =
      conj C * (Real.sqrt (absNorm (span {b})) : ℂ) * gamI 2 (span {n}) * Ψ (span {n}) *
        Ψ (span {b}) ^ 3 := by
  rw [← mul_assoc, hτ]
  have hsp : span {n * b} = span {n} * span {b} := (Ideal.span_singleton_mul_span_singleton n b).symm
  rw [hsp, map_mul] at h6
  have hn6 := coprime6_left h6
  have hb6 := coprime6_right h6
  have hb36 : (absNorm (span {b ^ 3})).Coprime 6 := by
    rw [← Ideal.span_singleton_pow, map_pow]; exact Nat.Coprime.pow_left 3 hb6
  have hnb : span {n * b ^ 3} = span {n} * span {b} ^ 3 := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  have h6' : (absNorm (span {n * b ^ 3})).Coprime 6 := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]; exact Nat.coprime_mul_iff_left.2 ⟨hn6, hb36⟩
  have hprim : Primary (n * b ^ 3) := hn.mul (primary_pow hb 3)
  have hn0 := span_ne_zero_of_coprime6 hn6
  have hb0 := span_ne_zero_of_coprime6 hb6
  have hb3 : span {b} ^ 3 = span {b} * span {b} * span {b} := by ring
  unfold phiTw
  rw [ite_eq_left ⟨hprim, h6'⟩, hnb, hb3, sym6_mul_right δ3 hn0 (mul_ne_zero (mul_ne_zero hb0 hb0) hb0),
    sym6_mul_right δ3 (mul_ne_zero hb0 hb0) hb0, sym6_mul_right δ3 hb0 hb0, hΨ, hΨ, hΨ]
  have hx : conj (sym6 δ3 (span {n})) * sym6 δ3 (span {n}) = 1 := by
    rw [Complex.conj_mul', norm_sym6_δ3 hn6]; norm_num
  have hy := sym6_δ3_pow_six hb6
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj, map_pow]
  set x := sym6 δ3 (span {n})
  set y := sym6 δ3 (span {b})
  linear_combination (conj C * (Real.sqrt (absNorm (span {b})) : ℂ) * gamI 2 (span {n}) *
    Ψ (span {n}) * Ψ (span {b}) ^ 3) * ((conj x * x + 1) * y ^ 6 * hx + hy)

/-- **The companion paper's Lemma 6.1, from the display**: `θ̄` twisted by any `F` periodic modulo
`q ≠ 0` with `F(0) = 0` is the sum of the translates `F̂(h)·θ̄(z + λ²h/q, v)` (its (6.4)), and the
twisted coefficient at `λnb³` is `conj C·N(b)^{1/2}γ₂(n)Ψ(n)Ψ(b)³` (its (6.3), with `C = 3^{5/2}`). -/
theorem lemma61_of_kubotaTheta (hK : KubotaTheta) :
    ∃ (θ : ℂ → ℝ → ℂ) (Kc : ℝ) (C : ℂ) (τ : 𝓞 K → ℂ), C ≠ 0 ∧ ThetaSupp Kc τ ∧
      (∀ q : 𝓞 K, q ≠ 0 → ∀ F : 𝓞 K → ℂ, (∀ z u, F (z + q * u) = F z) → F 0 = 0 →
        ∀ (z : ℂ) (v : ℝ), 0 < v →
        ∑ᶠ h : 𝓞 K ⧸ span {q}, fCoef q F (repQ q h) *
            conj (θ (z + σO (δ3 ^ 2 * repQ q h) / σO q) v) =
          ∑' m : 𝓞 K, twAt F m * conj (τ (-m)) * (v : ℂ) *
            besselK (1 / 3) (4 * Real.pi * ‖σO m‖ * v / 9) * ebr (σO m * z / 9)) ∧
      (∀ Ψ : Ideal (𝓞 K) → ℂ, (∀ I J, Ψ (I * J) = Ψ I * Ψ J) → ∀ n b : 𝓞 K, Primary n → Primary b →
        Squarefree (span {n}) → (absNorm (span {n * b})).Coprime 6 →
        conj (τ (-(δ3 * (n * b ^ 3)))) * phiTw Ψ (n * b ^ 3) =
          conj C * (Real.sqrt (absNorm (span {b})) : ℂ) * gamI 2 (span {n}) * Ψ (span {n}) *
            Ψ (span {b}) ^ 3) := by
  obtain ⟨θ, Kc, C, c₀, -, -, τ, -, -, hC, hτ, -, -, hτd, hθ, -, -, -, -, hval⟩ := hK
  refine ⟨θ, Kc, C, τ, hC, hτ, fun q hq F hF hF0 z v hv =>
    conj_theta_translates hθ hτ hτd q hq F hF hF0 z hv, fun Ψ hΨ n b hn hb hsq h6 =>
    coef_realization Ψ hΨ hn hb h6 (hval n b hn hb hsq h6).2⟩

end Eis

end

#print axioms Eis.dvd_of_ψc_mul_eq_one
#print axioms Eis.ψQ_isPrimitive_of_ne_zero
#print axioms Eis.finite_quot
#print axioms Eis.card_quot
#print axioms Eis.absNorm_span_ne_zero
#print axioms Eis.norm_ψc
#print axioms Eis.sum_ψc_mul
#print axioms Eis.fourier_inv
#print axioms Eis.sum_fCoef
#print axioms Eis.norm_fCoef_le
#print axioms Eis.ebr_add
#print axioms Eis.ebr_shift
#print axioms Eis.thSer_translates
#print axioms Eis.besselK_ofReal
#print axioms Eis.conj_besselK_third
#print axioms Eis.conj_ebr
#print axioms Eis.conj_thSer
#print axioms Eis.thetaSupp_conj
#print axioms Eis.δ3_ne_zero
#print axioms Eis.twAt_mul
#print axioms Eis.thSer_twist
#print axioms Eis.conj_theta_translates
#print axioms Eis.primary_pow
#print axioms Eis.δ3_not_mem_of_factor
#print axioms Eis.sym6_δ3_pow_six
#print axioms Eis.norm_sym6_δ3
#print axioms Eis.coprime6_left
#print axioms Eis.coprime6_right
#print axioms Eis.span_ne_zero_of_coprime6
#print axioms Eis.coef_realization
#print axioms Eis.lemma61_of_kubotaTheta
