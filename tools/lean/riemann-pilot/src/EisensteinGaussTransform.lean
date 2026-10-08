import EisensteinPoisson

/-! # The Gauss transform modulo squarefree moduli (round 295)

S3 of round 291's plan, part 2: the inner sums of round 294's Poisson formula. For `c ∈ ℤ[ω]` and
`g` periodic modulo `c`, the **Gauss transform** is `G_c(g, μ) = Σ_{r∈ℤ[ω]/c} g(r)·ψ_c(rμ)` (`gaussTr`),
with round 294's trace character `ψ_c(x) = e(Re(2σ(x)/σ(δc)))`.

* **The trace character on `ℤ[ω]/c`** (`ψQ`): `ψ_c` descends to an additive character of `ℤ[ω]/c`.
  `trPhase_mul_absNorm`: `N(c)·Re(2σ(x)/σ(δc)) = Re(2σ(xc̄)/σ(δ))`, the `ω`-coordinate of `xc̄`. So
  `ψ_c ≢ 1` for a non-unit `c` (`ψc_ne_one`), and at a prime `π` it is primitive (`ψQ_isPrimitive`).
* **At a prime** (`inner_sum_prime`): `Σ_{r mod π} χ(r)ψ_π(rμ) = χ⁻¹(μ)·g(χ, ψ_π)` for `χ ≠ 1`, by
  Mathlib's `gaussSum_mulShift_eq`. Hence **`eis_poisson_char`**:
  `Σ_z χ(z)F(σz) = 2/(√3·N(π))·g(χ, ψ_π)·Σ_{μ∈ℤ[ω]} χ⁻¹(μ)·𝓕F(conj(2σ(μ)/σ(δπ)))`.
* **The Gauss transform** is a sum over any complete residue system (`gaussTr_eq_sum`), and
  **`eis_poisson_gaussTr`**: `Σ_z f(z)F(σz) = 2/(√3·N(c))·Σ_{μ∈ℤ[ω]} G_c(f, μ)·𝓕F(conj(2σ(μ)/σ(δc)))`.
* **Chinese remainders** (`crt_rep_bijective`): for coprime `a, b`, the elements `b·r + a·s` run over
  the residues modulo `ab`. With `ψ_{ab}(by) = ψ_a(y)` (`ψc_mul_right`) this gives **`gaussTr_mul`**:
  `G_{ab}(f_a f_b, μ) = G_a(f_a(b·), μ)·G_b(f_b(a·), μ)`, and by induction **`gaussTr_prod`** over any
  finite family of pairwise coprime moduli.
* **Squarefree moduli** (`gaussTr_prime`, **`gaussTr_prod_primes`**): for distinct primes `π_i` and
  characters `χ_i ≠ 1` modulo `π_i`, with `c = ∏ π_i`,
  `G_c(∏ χ_i, μ) = ∏_i χ_i(c/π_i)·χ_i⁻¹(μ)·g(χ_i, ψ_{π_i})`. The factor `∏_i χ_i(c/π_i)` is the cross
  phase.
-/

open NumberField Complex Ideal
open scoped ComplexConjugate FourierTransform RealInnerProductSpace

noncomputable section

namespace Eis

/-- `e(t) = 1` iff `t ∈ ℤ`. -/
theorem fourierChar_eq_one_iff (t : ℝ) : (𝐞 t : ℂ) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Real.fourierChar_apply, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi : ℂ) * I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h := hn
    push_cast at h
    have : (t : ℂ) = n := by
      apply mul_right_cancel₀ h2
      linear_combination h
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

/-- `ψ_c` depends only on the residue modulo `c`. -/
theorem ψc_congr (c : 𝓞 K) (hc : c ≠ 0) {x y : 𝓞 K}
    (h : Ideal.Quotient.mk (span {c}) x = Ideal.Quotient.mk (span {c}) y) : ψc c x = ψc c y := by
  obtain ⟨u, hu⟩ := mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have hx : x = y + c * u := by linear_combination -hu
  rw [hx, ψc_add_mul c hc]

theorem ψc_zero (c : 𝓞 K) : ψc c 0 = 1 := by
  simp [ψc, trPhase]

/-- **The trace character of `ℤ[ω]/c`**, `r ↦ e(Tr(r/(δc)))`. -/
def ψQ (c : 𝓞 K) (hc : c ≠ 0) : AddChar (𝓞 K ⧸ span {c}) ℂ where
  toFun r := ψc c (repQ c r)
  map_zero_eq_one' := by
    rw [ψc_congr c hc (show Ideal.Quotient.mk (span {c}) (repQ c 0) = Ideal.Quotient.mk _ 0 by
      rw [repQ_mk, map_zero]), ψc_zero]
  map_add_eq_mul' r s := by
    rw [← ψc_add]
    apply ψc_congr c hc
    rw [map_add, repQ_mk, repQ_mk, repQ_mk]

theorem ψQ_mk (c : 𝓞 K) (hc : c ≠ 0) (x : 𝓞 K) :
    ψQ c hc (Ideal.Quotient.mk (span {c}) x) = ψc c x :=
  ψc_congr c hc (repQ_mk c _)

/-- `trPhase c x·N(c) = Re(2σ(x c̄)/σ(δ))`. -/
theorem trPhase_mul_absNorm (c x : 𝓞 K) (hc : c ≠ 0) :
    trPhase c x * (absNorm (span {c}) : ℝ) = (2 * σO (x * cj c) / σO δ3).re := by
  have hc' : σO c ≠ 0 := fun h => hc (σO_injective (h.trans (map_zero σO).symm))
  have hN := congrArg σO (mul_cj_eq_absNorm c)
  rw [map_mul, map_natCast] at hN
  have hcj : σO (cj c) ≠ 0 := by
    intro h; rw [h, mul_zero] at hN
    have : (absNorm (span {c}) : ℕ) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
    exact this (by exact_mod_cast hN.symm)
  rw [trPhase, map_mul, map_mul]
  have : 2 * σO x / (σO δ3 * σO c) =
      2 * (σO x * σO (cj c)) / σO δ3 / ((absNorm (span {c}) : ℕ) : ℂ) := by
    rw [← hN]; field_simp
  rw [this, Complex.div_natCast_re]
  have hN0 : ((absNorm (span {c}) : ℕ) : ℝ) ≠ 0 := by
    have : (absNorm (span {c}) : ℕ) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
    exact_mod_cast this
  field_simp

/-- For a non-unit `c ≠ 0`, `ψ_c` is not identically `1`: otherwise `N(c)` divides both
coordinates of `c̄`, so `c c̄ ∣ c̄` and `c` is a unit. -/
theorem ψc_ne_one (c : 𝓞 K) (hc : c ≠ 0) (hu : ¬ IsUnit c) : ∃ x, ψc c x ≠ 1 := by
  by_contra hall
  push Not at hall
  obtain ⟨a, b, hab⟩ := exists_coords (cj c)
  set N : ℕ := absNorm (span {c}) with hNdef
  have h1 : trPhase c 1 * N = b := by
    rw [trPhase_mul_absNorm c 1 hc, one_mul, hab, re_two_σO_div_δ3]
  have h2 : trPhase c ω * N = ((a - b : ℤ) : ℝ) := by
    rw [trPhase_mul_absNorm c ω hc, hab]
    have : ω * ((a : 𝓞 K) + (b : 𝓞 K) * ω) = ((-b : ℤ) : 𝓞 K) + ((a - b : ℤ) : 𝓞 K) * ω := by
      push_cast; linear_combination (b : 𝓞 K) * ω_sq_add
    rw [this, re_two_σO_div_δ3]
  obtain ⟨n1, hn1⟩ := (fourierChar_eq_one_iff _).1 (hall 1)
  obtain ⟨n2, hn2⟩ := (fourierChar_eq_one_iff _).1 (hall ω)
  rw [hn1] at h1
  rw [hn2] at h2
  have hb : b = n1 * N := by exact_mod_cast h1.symm
  have ha : a - b = n2 * N := by exact_mod_cast h2.symm
  have hcj : cj c = (N : 𝓞 K) * (((n1 + n2 : ℤ) : 𝓞 K) + (n1 : 𝓞 K) * ω) := by
    rw [hab]
    have ha' : a = (n1 + n2) * N := by linarith
    rw [ha', hb]; push_cast; ring
  have hcj0 : cj c ≠ 0 := fun h => hc (by simpa using congrArg cj.symm h)
  have hN := mul_cj_eq_absNorm c
  rw [← hNdef] at hN
  rw [← hN, mul_comm c, mul_assoc] at hcj
  apply hu
  refine isUnit_iff_exists_inv.2 ⟨((n1 + n2 : ℤ) : 𝓞 K) + (n1 : 𝓞 K) * ω, ?_⟩
  apply mul_left_cancel₀ hcj0
  rw [mul_one]
  exact hcj.symm

theorem ψQ_ne_one (c : 𝓞 K) (hc : c ≠ 0) (hu : ¬ IsUnit c) : ψQ c hc ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := ψc_ne_one c hc hu
  apply hx
  rw [← ψQ_mk c hc, h, AddChar.one_apply]

section Prime

variable (π : 𝓞 K) [hP : (span {π} : Ideal (𝓞 K)).IsMaximal]

theorem ne_zero_of_maximal : π ≠ 0 := by
  have := ne_bot (span {π})
  rwa [Ne, Ideal.span_singleton_eq_bot] at this

theorem not_isUnit_of_maximal : ¬ IsUnit π := fun h =>
  hP.ne_top (Ideal.span_singleton_eq_top.2 h)

/-- At a prime, the trace character is primitive. -/
theorem ψQ_isPrimitive : (ψQ π (ne_zero_of_maximal π)).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one (ψQ_ne_one π _ (not_isUnit_of_maximal π))

/-- **The inner sums at a prime are Gauss sums**: `Σ_{r mod π} χ(r)ψ_π(rμ) = χ⁻¹(μ)·g(χ, ψ_π)`
for `χ ≠ 1`. -/
theorem inner_sum_prime (χ : MulChar (𝓞 K ⧸ span {π}) ℂ) (hχ : χ ≠ 1) (μ : 𝓞 K) :
    ∑ r, χ r * ψc π (repQ π r * μ) =
      χ⁻¹ (Ideal.Quotient.mk (span {π}) μ) * gaussSum χ (ψQ π (ne_zero_of_maximal π)) := by
  have hterm : ∀ r, ψc π (repQ π r * μ) =
      (ψQ π (ne_zero_of_maximal π)).mulShift (Ideal.Quotient.mk (span {π}) μ) r := by
    intro r
    rw [AddChar.mulShift_apply, ← ψQ_mk π (ne_zero_of_maximal π), map_mul, repQ_mk, mul_comm]
  simp_rw [hterm]
  change gaussSum χ _ = _
  by_cases hμ : Ideal.Quotient.mk (span {π}) μ = 0
  · rw [hμ, AddChar.mulShift_zero, gaussSum_one_right hχ, MulChar.map_zero, zero_mul]
  · have hu : IsUnit (Ideal.Quotient.mk (span {π}) μ) := isUnit_iff_ne_zero.2 hμ
    have := gaussSum_mulShift_eq χ (ψQ π (ne_zero_of_maximal π)) hu.unit
    rwa [IsUnit.unit_spec] at this

/-- **Poisson summation twisted by a character modulo a prime**: for `χ ≠ 1`,
`Σ_z χ(z)F(σz) = 2/(√3·N(π))·g(χ, ψ_π)·Σ_{μ∈ℤ[ω]} χ⁻¹(μ)·𝓕F(conj(2σ(μ)/σ(δπ)))`. -/
theorem eis_poisson_char (F : SchwartzMap ℂ ℂ) (χ : MulChar (𝓞 K ⧸ span {π}) ℂ) (hχ : χ ≠ 1) :
    ∑' z : 𝓞 K, χ (Ideal.Quotient.mk (span {π}) z) * F (σO z) =
      ((2 / (Real.sqrt 3 * (absNorm (span {π}) : ℝ)) : ℝ) : ℂ) *
        gaussSum χ (ψQ π (ne_zero_of_maximal π)) *
        ∑' μ : 𝓞 K, χ⁻¹ (Ideal.Quotient.mk (span {π}) μ) *
          𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * π))) := by
  rw [eis_poisson_quot F π (ne_zero_of_maximal π) (fun r => χ r)]
  simp_rw [inner_sum_prime π χ hχ]
  have h : ∀ μ : 𝓞 K, χ⁻¹ (Ideal.Quotient.mk (span {π}) μ) *
      gaussSum χ (ψQ π (ne_zero_of_maximal π)) * 𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * π))) =
      gaussSum χ (ψQ π (ne_zero_of_maximal π)) * (χ⁻¹ (Ideal.Quotient.mk (span {π}) μ) *
        𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * π)))) := fun μ => by ring
  rw [tsum_congr h, tsum_mul_left, mul_assoc]

end Prime

/-- `ψ_{ab}(b y) = ψ_a(y)`. -/
theorem ψc_mul_right (a b y : 𝓞 K) (hb : b ≠ 0) : ψc (a * b) (b * y) = ψc a y := by
  have hb' : σO b ≠ 0 := fun h => hb (σO_injective (h.trans (map_zero σO).symm))
  have h : 2 * σO (b * y) / σO (δ3 * (a * b)) = 2 * σO y / σO (δ3 * a) := by
    rw [map_mul, map_mul, map_mul, map_mul,
      show 2 * (σO b * σO y) / (σO δ3 * (σO a * σO b)) =
        (σO b * (2 * σO y)) / (σO b * (σO δ3 * σO a)) by ring, mul_div_mul_left _ _ hb']
  simp only [ψc, trPhase, h]

/-- A function periodic modulo `c` takes equal values on congruent arguments. -/
theorem periodic_congr (c : 𝓞 K) (g : 𝓞 K → ℂ) (hg : ∀ z u, g (z + c * u) = g z) {x y : 𝓞 K}
    (h : Ideal.Quotient.mk (span {c}) x = Ideal.Quotient.mk (span {c}) y) : g x = g y := by
  obtain ⟨u, hu⟩ := mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have hx : x = y + c * u := by linear_combination -hu
  rw [hx, hg]

/-- A complete residue system modulo `c` maps bijectively onto `ℤ[ω]/c`. -/
theorem rep_mk_bijective {ι : Type*} (c : 𝓞 K) (rep : ι → 𝓞 K)
    (hR : Function.Bijective (fun p : ι × 𝓞 K => rep p.1 + c * p.2)) :
    Function.Bijective (fun i => Ideal.Quotient.mk (span {c}) (rep i)) := by
  constructor
  · intro i j h
    obtain ⟨u, hu⟩ := mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
    have := hR.1 (a₁ := (i, 0)) (a₂ := (j, u)) (by simp only; linear_combination -hu)
    exact (Prod.mk.inj this).1
  · intro r
    obtain ⟨⟨i, u⟩, hiu⟩ := hR.2 (repQ c r)
    refine ⟨i, ?_⟩
    simp only at hiu
    rw [← repQ_mk c r, ← hiu, map_add, mk_mul_left, add_zero]

/-- **The Gauss transform modulo `c`**: `G_c(g, μ) = Σ_{r ∈ ℤ[ω]/c} g(r)ψ_c(rμ)`. -/
def gaussTr (c : 𝓞 K) (g : 𝓞 K → ℂ) (μ : 𝓞 K) : ℂ :=
  ∑ᶠ r : 𝓞 K ⧸ span {c}, g (repQ c r) * ψc c (repQ c r * μ)

/-- `G_c(g, μ)` is the sum over any complete residue system, for `g` periodic modulo `c`. -/
theorem gaussTr_eq_sum {ι : Type*} [Fintype ι] (c : 𝓞 K) (hc : c ≠ 0) (g : 𝓞 K → ℂ)
    (hg : ∀ z u, g (z + c * u) = g z) (rep : ι → 𝓞 K)
    (hR : Function.Bijective (fun p : ι × 𝓞 K => rep p.1 + c * p.2)) (μ : 𝓞 K) :
    gaussTr c g μ = ∑ i, g (rep i) * ψc c (rep i * μ) := by
  have : Finite (𝓞 K ⧸ span {c}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {c}) := Fintype.ofFinite _
  rw [gaussTr, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_bijective _ (rep_mk_bijective c rep hR) _ _ fun i => ?_
  have h : Ideal.Quotient.mk (span {c}) (repQ c (Ideal.Quotient.mk (span {c}) (rep i))) =
      Ideal.Quotient.mk (span {c}) (rep i) := repQ_mk c _
  have h' : Ideal.Quotient.mk (span {c}) (repQ c (Ideal.Quotient.mk (span {c}) (rep i)) * μ) =
      Ideal.Quotient.mk (span {c}) (rep i * μ) := by rw [map_mul, map_mul, h]
  rw [periodic_congr c g hg h.symm, ψc_congr c hc h'.symm]

/-- **The Chinese remainder parametrization**: for coprime `a, b` and residue systems `repa`,
`repb`, the elements `b·repa i + a·repb j` form a residue system modulo `ab`. -/
theorem crt_rep_bijective {ιa ιb : Type*} (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) (repa : ιa → 𝓞 K) (repb : ιb → 𝓞 K)
    (hRa : Function.Bijective (fun p : ιa × 𝓞 K => repa p.1 + a * p.2))
    (hRb : Function.Bijective (fun p : ιb × 𝓞 K => repb p.1 + b * p.2)) :
    Function.Bijective (fun p : (ιa × ιb) × 𝓞 K =>
      (b * repa p.1.1 + a * repb p.1.2) + (a * b) * p.2) := by
  constructor
  · rintro ⟨⟨i, j⟩, u⟩ ⟨⟨i', j'⟩, u'⟩ h
    simp only at h
    -- reduce modulo `a`, then modulo `b`
    have hi : i = i' := by
      have hd : a ∣ b * (repa i - repa i') := ⟨repb j' - repb j + b * (u' - u), by
        linear_combination h⟩
      obtain ⟨w, hw⟩ := hab.dvd_of_dvd_mul_left hd
      have := hRa.1 (a₁ := (i, 0)) (a₂ := (i', w)) (by simp only; linear_combination hw)
      exact (Prod.mk.inj this).1
    have hj : j = j' := by
      have hd : b ∣ a * (repb j - repb j') := ⟨repa i' - repa i + a * (u' - u), by
        linear_combination h⟩
      obtain ⟨w, hw⟩ := hab.symm.dvd_of_dvd_mul_left hd
      have := hRb.1 (a₁ := (j, 0)) (a₂ := (j', w)) (by simp only; linear_combination hw)
      exact (Prod.mk.inj this).1
    subst hi hj
    have hu : u = u' := mul_left_cancel₀ (mul_ne_zero ha hb) (add_left_cancel h)
    rw [hu]
  · intro z
    obtain ⟨x, y, hxy⟩ := hab
    obtain ⟨⟨i, u₁⟩, h₁⟩ := hRa.2 (z * y)
    obtain ⟨⟨j, u₂⟩, h₂⟩ := hRb.2 (z * x)
    refine ⟨((i, j), u₁ + u₂), ?_⟩
    simp only at h₁ h₂ ⊢
    linear_combination b * h₁ + a * h₂ + z * hxy

/-- **The Gauss transform factors over coprime moduli**:
`G_{ab}(f_a f_b, μ) = G_a(f_a(b·), μ)·G_b(f_b(a·), μ)`. -/
theorem gaussTr_mul (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsCoprime a b)
    (fa fb : 𝓞 K → ℂ) (hfa : ∀ z u, fa (z + a * u) = fa z) (hfb : ∀ z u, fb (z + b * u) = fb z)
    (μ : 𝓞 K) :
    gaussTr (a * b) (fun z => fa z * fb z) μ =
      gaussTr a (fun z => fa (b * z)) μ * gaussTr b (fun z => fb (a * z)) μ := by
  have : Finite (𝓞 K ⧸ span {a}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {a}) := Fintype.ofFinite _
  have : Finite (𝓞 K ⧸ span {b}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {b}) := Fintype.ofFinite _
  have hf : ∀ z u, fa (z + a * b * u) * fb (z + a * b * u) = fa z * fb z := by
    intro z u
    rw [mul_assoc a b u, hfa, mul_left_comm a b u, hfb]
  have hcrt := crt_rep_bijective a b ha hb hab (repQ a) (repQ b) (repQ_bijective a ha)
    (repQ_bijective b hb)
  have e1 := gaussTr_eq_sum (ι := (𝓞 K ⧸ span {a}) × (𝓞 K ⧸ span {b})) (a * b) (mul_ne_zero ha hb)
    (fun z => fa z * fb z) hf (fun q => b * repQ a q.1 + a * repQ b q.2) hcrt μ
  have hpa : ∀ z u, fa (b * (z + a * u)) = fa (b * z) := fun z u => by
    rw [mul_add, mul_left_comm, hfa]
  have hpb : ∀ z u, fb (a * (z + b * u)) = fb (a * z) := fun z u => by
    rw [mul_add, mul_left_comm, hfb]
  have e2 := gaussTr_eq_sum a ha (fun z => fa (b * z)) hpa (repQ a) (repQ_bijective a ha) μ
  have e3 := gaussTr_eq_sum b hb (fun z => fb (a * z)) hpb (repQ b) (repQ_bijective b hb) μ
  rw [e1, e2, e3, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : fa (b * repQ a i + a * repQ b j) = fa (b * repQ a i) := hfa _ _
  have h2 : fb (b * repQ a i + a * repQ b j) = fb (a * repQ b j) := by
    rw [add_comm]; exact hfb _ _
  have h3 : ψc (a * b) ((b * repQ a i + a * repQ b j) * μ) =
      ψc a (repQ a i * μ) * ψc b (repQ b j * μ) := by
    rw [add_mul, ψc_add, mul_assoc b, ψc_mul_right a b _ hb, mul_assoc a, mul_comm a b,
      ψc_mul_right b a _ ha]
  rw [h1, h2, h3]
  ring

/-- `G_1(a, μ) = a` for a constant `a`. -/
theorem gaussTr_one_const (a : ℂ) (μ : 𝓞 K) : gaussTr 1 (fun _ => a) μ = a := by
  have hR : Function.Bijective
      (fun p : Unit × 𝓞 K => (fun _ : Unit => (0 : 𝓞 K)) p.1 + 1 * p.2) := by
    constructor
    · rintro ⟨⟨⟩, u⟩ ⟨⟨⟩, u'⟩ h
      simp only [zero_add, one_mul] at h
      rw [h]
    · intro z; exact ⟨((), z), by simp⟩
  rw [gaussTr_eq_sum 1 one_ne_zero (fun _ => a) (fun _ _ => rfl) (fun _ => 0) hR μ]
  simp [ψc_zero]

/-- **The Gauss transform over pairwise coprime moduli**: for `f i` periodic modulo `c i`,
`G_{∏c}(∏ f_i, μ) = ∏_i G_{c_i}(f_i((∏_{j≠i} c_j)·), μ)`. -/
theorem gaussTr_prod {ι : Type*} [DecidableEq ι] (c : ι → 𝓞 K) (μ : 𝓞 K) (S : Finset ι)
    (hc0 : ∀ i ∈ S, c i ≠ 0) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (c i) (c j))
    (f : ι → 𝓞 K → ℂ) (hf : ∀ i ∈ S, ∀ z u, f i (z + c i * u) = f i z) :
    gaussTr (∏ i ∈ S, c i) (fun z => ∏ i ∈ S, f i z) μ =
      ∏ i ∈ S, gaussTr (c i) (fun z => f i ((∏ j ∈ S.erase i, c j) * z)) μ := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp only [Finset.prod_empty]; exact gaussTr_one_const 1 μ
  | @insert k S hk ih =>
    have hc0' : ∀ i ∈ S, c i ≠ 0 := fun i hi => hc0 i (Finset.mem_insert_of_mem hi)
    have hcop' : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (c i) (c j) := fun i hi j hj =>
      hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hk0 : c k ≠ 0 := hc0 k (Finset.mem_insert_self k S)
    have hS0 : ∏ i ∈ S, c i ≠ 0 := Finset.prod_ne_zero_iff.2 hc0'
    have hkS : IsCoprime (c k) (∏ i ∈ S, c i) := IsCoprime.prod_right fun i hi =>
      hcop k (Finset.mem_insert_self k S) i (Finset.mem_insert_of_mem hi)
        (fun h => hk (h ▸ hi))
    -- periodicity of the two factors
    have hfk : ∀ z u, f k (z + c k * u) = f k z := hf k (Finset.mem_insert_self k S)
    have hfS : ∀ z u, (∏ i ∈ S, f i (z + (∏ j ∈ S, c j) * u)) = ∏ i ∈ S, f i z := by
      intro z u
      refine Finset.prod_congr rfl fun i hi => ?_
      obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem c hi
      rw [hw, mul_assoc]
      exact hf i (Finset.mem_insert_of_mem hi) _ _
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    have hsplit : (fun z => ∏ i ∈ insert k S, f i z) = fun z => f k z * ∏ i ∈ S, f i z := by
      funext z; rw [Finset.prod_insert hk]
    rw [hsplit, gaussTr_mul (c k) (∏ i ∈ S, c i) hk0 hS0 hkS (f k) (fun z => ∏ i ∈ S, f i z) hfk hfS μ]
    -- the induction hypothesis, for the shifted family `f i (c k ·)`
    have ih' := ih hc0' hcop' (fun i z => f i (c k * z)) (fun i hi z u => by
      rw [mul_add, mul_left_comm]; exact hf i (Finset.mem_insert_of_mem hi) _ _)
    simp only at ih'
    rw [ih']
    congr 1
    · congr 1
      funext z
      rw [Finset.erase_insert hk]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hik : i ≠ k := fun h => hk (h ▸ hi)
      congr 1
      funext z
      rw [Finset.erase_insert_of_ne hik.symm, Finset.prod_insert (fun h => hk (Finset.mem_of_mem_erase h)),
        mul_assoc]

/-- **Poisson summation with the Gauss transform**: for `f` periodic modulo `c ≠ 0`,
`Σ_z f(z)F(σz) = 2/(√3·N(c))·Σ_{μ∈ℤ[ω]} G_c(f, μ)·𝓕F(conj(2σ(μ)/σ(δc)))`. -/
theorem eis_poisson_gaussTr (F : SchwartzMap ℂ ℂ) (c : 𝓞 K) (hc : c ≠ 0) (f : 𝓞 K → ℂ)
    (hf : ∀ z u, f (z + c * u) = f z) :
    ∑' z : 𝓞 K, f z * F (σO z) =
      ((2 / (Real.sqrt 3 * (absNorm (span {c}) : ℝ)) : ℝ) : ℂ) *
        ∑' μ : 𝓞 K, gaussTr c f μ * 𝓕 (F : ℂ → ℂ) (conj (2 * σO μ / σO (δ3 * c))) := by
  have : Finite (𝓞 K ⧸ span {c}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let : Fintype (𝓞 K ⧸ span {c}) := Fintype.ofFinite _
  rw [eis_poisson_trace F c hc f hf (repQ c) (repQ_bijective c hc)]
  congr 1
  refine tsum_congr fun μ => ?_
  rw [gaussTr_eq_sum c hc f hf (repQ c) (repQ_bijective c hc) μ]

section Prime

variable (π : 𝓞 K) [hP : (span {π} : Ideal (𝓞 K)).IsMaximal]

/-- **The local Gauss transform**: `G_π(χ(m·), μ) = χ(m)·χ⁻¹(μ)·g(χ, ψ_π)` for `χ ≠ 1`. -/
theorem gaussTr_prime (χ : MulChar (𝓞 K ⧸ span {π}) ℂ) (hχ : χ ≠ 1) (m μ : 𝓞 K) :
    gaussTr π (fun z => χ (Ideal.Quotient.mk (span {π}) (m * z))) μ =
      χ (Ideal.Quotient.mk (span {π}) m) * χ⁻¹ (Ideal.Quotient.mk (span {π}) μ) *
        gaussSum χ (ψQ π (ne_zero_of_maximal π)) := by
  have hper : ∀ z u, χ (Ideal.Quotient.mk (span {π}) (m * (z + π * u))) =
      χ (Ideal.Quotient.mk (span {π}) (m * z)) := by
    intro z u
    rw [mul_add, mul_left_comm, map_add, mk_mul_left, add_zero]
  rw [gaussTr_eq_sum π (ne_zero_of_maximal π) _ hper (repQ π) (repQ_bijective π (ne_zero_of_maximal π)) μ]
  simp_rw [map_mul (Ideal.Quotient.mk (span {π})) m, repQ_mk, map_mul χ, mul_assoc]
  rw [← Finset.mul_sum, inner_sum_prime π χ hχ μ]

end Prime

/-- **The Gauss transform of a product of characters modulo a squarefree `c = ∏ π_i`**:
`G_c(∏ χ_i, μ) = ∏_i χ_i(c/π_i)·χ_i⁻¹(μ)·g(χ_i, ψ_{π_i})`. The factor `∏_i χ_i(c/π_i)` is the
cross phase. -/
theorem gaussTr_prod_primes {ι : Type*} [DecidableEq ι] (π : ι → 𝓞 K)
    [hP : ∀ i, (span {π i} : Ideal (𝓞 K)).IsMaximal] (S : Finset ι)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (π i) (π j))
    (χ : ∀ i, MulChar (𝓞 K ⧸ span {π i}) ℂ) (hχ : ∀ i ∈ S, χ i ≠ 1) (μ : 𝓞 K) :
    gaussTr (∏ i ∈ S, π i) (fun z => ∏ i ∈ S, χ i (Ideal.Quotient.mk (span {π i}) z)) μ =
      ∏ i ∈ S, (χ i (Ideal.Quotient.mk (span {π i}) (∏ j ∈ S.erase i, π j)) *
        (χ i)⁻¹ (Ideal.Quotient.mk (span {π i}) μ) *
          gaussSum (χ i) (ψQ (π i) (ne_zero_of_maximal (π i)))) := by
  rw [gaussTr_prod π μ S (fun i _ => ne_zero_of_maximal (π i)) hcop
    (fun i z => χ i (Ideal.Quotient.mk (span {π i}) z))
    (fun i _ z u => by rw [map_add, mk_mul_left, add_zero])]
  exact Finset.prod_congr rfl fun i hi => gaussTr_prime (π i) (χ i) (hχ i hi) _ μ

end Eis

end

#print axioms Eis.fourierChar_eq_one_iff
#print axioms Eis.ψQ_mk
#print axioms Eis.trPhase_mul_absNorm
#print axioms Eis.ψc_ne_one
#print axioms Eis.ψQ_isPrimitive
#print axioms Eis.inner_sum_prime
#print axioms Eis.eis_poisson_char
#print axioms Eis.ψc_mul_right
#print axioms Eis.gaussTr_eq_sum
#print axioms Eis.crt_rep_bijective
#print axioms Eis.gaussTr_mul
#print axioms Eis.gaussTr_prod
#print axioms Eis.eis_poisson_gaussTr
#print axioms Eis.gaussTr_prime
#print axioms Eis.gaussTr_prod_primes
