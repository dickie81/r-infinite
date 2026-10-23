import KubotaCuspCoef

/-! # The Kubota sums at the cusps `γ_t` and `0` (round 463)

S5f-15 of round 360's plan, part 4. Round 462's next step planned the relation between round 462's Kubota sums
at the cusps `γ_t` and `0`, and θ's coefficients at `γ_t`. This round proves the relation, and the relation
between the two pairings with `ũ_s` it gives, for `tt′ = 1`, `m` in the class of the cusp `γ_t` (round 461's
`CuspClass`), `λ = ω − 1` and `m′ = δ₃ω²tλ²m = −tλ³m`:

* **Sums of a periodic function over the classes** (**`tsum_repQ_eq_of_span`** and **`tsum_repQ_affine`**,
  with `eq_of_mk_eq_of_periodic`): for `G` periodic modulo `c`, the sum of `G` over the classes modulo `c` is
  the sum over the classes modulo `c′` when `(c) = (c′)` (Mathlib's `Ideal.quotEquivOfEq`), and is unchanged
  by `r ↦ αr + β` for `α` prime to `c`.
* **The summands** (`kubTermT` and `kubTerm0`, definitions; **`kubTermT_periodic`**, **`kubTerm0_periodic`**,
  **`cuspSmT_eq_zero`** and **`cuspSm0_eq_zero`**, with `cuspSmT_eq` and `cuspSm0_eq`): the summand of
  `S^t_m(c)` is periodic modulo `3c` (round 462's `wtCuspT_add` and `conj_chiT_of_class`), and that of
  `S⁰_m(c)` for `m = δ₃x` (round 428's `ebr_period`); `S^t_m(c) = 0` unless `c ≡ t (mod 3)`, and `S⁰_m(c) = 0`
  unless `c` is primary.
* **The termwise identity** (`kubPoly`, a definition; **`kubTermT_affine`**, with `δ3_eq_lam_neg` and
  `kubota_sum_poly`): for `a` primary, `3u + va = 1` and every `b`, the summand of `S^t_m(ta)` at
  `d = (va − 3uλ³t²)b + va` is `ĕ(mt′/9)` times the summand of `S⁰_{m′}(a)` at `b`. The supports agree, since
  `d − 1 ≡ b (mod 3)` and `d ≡ −λ³t²b (mod a)`. On them `((ta − dt)/d)₃ = (t/d)₃(d/a)₃` (round 362's
  `cub_congr` and `cub_mul_left`, round 290's `cub_recip`), `(d/a)₃ = (t/a)₃²(b/a)₃` (round 362's `cub_neg`
  and `cub_pow_three`, round 369's `cub_pow_left`), and the class gives `(t/d)₃` and `(t/a)₃` as values of `ĕ`
  (round 460's `chiT`). What remains is a polynomial identity in `𝒪` (`kubota_sum_poly`), and a multiple of
  `ĕ(m·3λy/9) = 1` (round 460's `ebr_lam_mul`).
* **The sums and the Dirichlet series** (**`cuspSmT_mul_primary`**, **`cuspSmT_mul`** and
  **`tsum_cuspSmT_eq`**): `S^t_m(ta) = ĕ(mt′/9)·S⁰_{m′}(a)` for every `a`, the map `b ↦ (va − 3uλ³t²)b + va`
  being a bijection of the classes modulo `3a`, and `Σ_c S^t_m(c)N(c)^{−s} = ĕ(mt′/9)·Σ_a S⁰_{m′}(a)N(a)^{−s}`
  for every `s` (round 361's `normSq_σO_unit`).
* **The pairings** (`sclPsi`, a definition; **`norm_σO_cuspIdx`**, **`jPsi_comp_mul`** and
  **`inner_pmSerC_uL_eq`**, with `sqrt27_pos`, `measurable_sclPsi`, `norm_sclPsi_le` and `sclPsi_eq_zero`):
  `|m′| = 3√3·|m|`, `J` of `ψ(c·)` at `ca` is `c·J_ψ` at `a`, and so for `ψ` measurable and bounded, vanishing
  outside `[α, β]` with `0 < α ≤ β`, `ψ̃(v) = ψ(3√3·v)`, `Re s > 2` and `Im ĥ(s) ≠ 0`, the pairing of `Q_t(ψ)`
  with `ũ_s` plus its band term is `ĕ(mt′/9)·(3√3)^{−s}` times the same for `P_{m′}(ψ̃)∘S⁻¹` (round 462's
  `inner_pmSerC_uL` and `inner_pmSerS_uL`).
-/

open MeasureTheory Set Filter NumberField Complex Ideal Asymptotics
open scoped ENNReal Topology MatrixGroups ComplexConjugate

noncomputable section

namespace Eis

/-! ### Sums of a periodic function over the classes -/

/-- A function periodic modulo `c` takes one value on a class. -/
theorem eq_of_mk_eq_of_periodic {c : 𝓞 K} {G : 𝓞 K → ℂ} (hG : ∀ x y, G (x + c * y) = G x) {x x' : 𝓞 K}
    (h : Ideal.Quotient.mk (span {c}) x = Ideal.Quotient.mk (span {c}) x') : G x = G x' := by
  rw [Ideal.Quotient.eq, mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  rw [show x = x' + c * y by linear_combination hy, hG]

/-- **Equal ideals**: for `G` periodic modulo `c` and `(c) = (c′)`, the sums of `G` over the classes agree. -/
theorem tsum_repQ_eq_of_span {c c' : 𝓞 K} (h : span {c} = span {c'}) {G : 𝓞 K → ℂ}
    (hG : ∀ x y, G (x + c * y) = G x) :
    ∑' r : 𝓞 K ⧸ span {c}, G (repQ c r) = ∑' r : 𝓞 K ⧸ span {c'}, G (repQ c' r) := by
  set e := Ideal.quotEquivOfEq h
  rw [← e.symm.toEquiv.tsum_eq (fun r => G (repQ c r))]
  refine tsum_congr fun r => eq_of_mk_eq_of_periodic hG ?_
  rw [repQ_mk]
  apply e.injective
  show e (e.symm r) = e (Ideal.Quotient.mk (span {c}) (repQ c' r))
  rw [RingEquiv.apply_symm_apply, Ideal.quotEquivOfEq_mk, repQ_mk]

/-- **An affine change of class**: for `G` periodic modulo `c` and `α` prime to `c`,
`Σ_r G(αr + β) = Σ_r G(r)` over the classes modulo `c`. -/
theorem tsum_repQ_affine {c α : 𝓞 K} (hα : IsCoprime α c) (β : 𝓞 K) {G : 𝓞 K → ℂ}
    (hG : ∀ x y, G (x + c * y) = G x) :
    ∑' r : 𝓞 K ⧸ span {c}, G (α * repQ c r + β) = ∑' r : 𝓞 K ⧸ span {c}, G (repQ c r) := by
  obtain ⟨u, v, huv⟩ := hα
  have hu : Ideal.Quotient.mk (span {c}) u * Ideal.Quotient.mk (span {c}) α = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (span {c})), Ideal.Quotient.eq, mem_span_singleton]
    exact ⟨-v, by linear_combination huv⟩
  let U : (𝓞 K ⧸ span {c})ˣ :=
    ⟨Ideal.Quotient.mk (span {c}) α, Ideal.Quotient.mk (span {c}) u, by rw [mul_comm]; exact hu, hu⟩
  let e : 𝓞 K ⧸ span {c} ≃ 𝓞 K ⧸ span {c} :=
    U.mulLeft.trans (Equiv.addRight (Ideal.Quotient.mk (span {c}) β))
  rw [← e.tsum_eq (fun r => G (repQ c r))]
  refine tsum_congr fun r => eq_of_mk_eq_of_periodic hG ?_
  rw [repQ_mk]
  simp only [e, U, Equiv.trans_apply, Units.mulLeft_apply, Equiv.coe_addRight, map_add,
    map_mul, repQ_mk]

/-! ### The summands -/

/-- The summand of `S^t_m(c)` at `d`. -/
def kubTermT (t m c d : 𝓞 K) : ℂ := wtCuspT t c d * ebr (σO m / 9 * (σO d / σO c))

/-- The summand of `S⁰_m(c)` at `d`. -/
def kubTerm0 (m c d : 𝓞 K) : ℂ := wtCusp0 c d * ebr (σO m / 9 * (σO d / σO c))

theorem cuspSmT_eq (t m c : 𝓞 K) :
    cuspSmT t m c = ∑' r : 𝓞 K ⧸ span {3 * c}, kubTermT t m c (repQ (3 * c) r) := rfl

theorem cuspSm0_eq (m c : 𝓞 K) :
    cuspSm0 m c = ∑' r : 𝓞 K ⧸ span {3 * c}, kubTerm0 m c (repQ (3 * c) r) := rfl

/-- **The summand of `S^t_m(c)` is periodic modulo `3c`** for `m` in the class of the cusp. -/
theorem kubTermT_periodic {t m : 𝓞 K} (hm : CuspClass t m) {c : 𝓞 K} (hc : c ≠ 0) (d y : 𝓞 K) :
    kubTermT t m c (d + 3 * c * y) = kubTermT t m c d := by
  unfold kubTermT
  rw [wtCuspT_add, conj_chiT_of_class hm]
  have hc' : σO c ≠ 0 := σO_ne_zero hc
  have e : σO m / 9 * (σO (d + 3 * c * y) / σO c) =
      σO m / 9 * (σO d / σO c) + σO m / 9 * σO (3 * y) := by
    simp only [map_add, map_mul]
    field_simp
  rw [e, ebr_add]
  have h1 : ebr (-(σO m / 9 * σO (3 * y))) * ebr (σO m / 9 * σO (3 * y)) = 1 := by
    rw [← ebr_add, neg_add_cancel, ebr_zero]
  linear_combination (wtCuspT t c d * ebr (σO m / 9 * (σO d / σO c))) * h1

/-- **The summand of `S⁰_m(c)` is periodic modulo `3c`** for `m = δ₃x`. -/
theorem kubTerm0_periodic (x : 𝓞 K) {c : 𝓞 K} (hc : c ≠ 0) (d y : 𝓞 K) :
    kubTerm0 (δ3 * x) c (d + 3 * c * y) = kubTerm0 (δ3 * x) c d := by
  unfold kubTerm0
  rw [wtCusp0_add]
  have hc' : σO c ≠ 0 := σO_ne_zero hc
  have e : σO (δ3 * x) / 9 * (σO (d + 3 * c * y) / σO c) =
      σO (δ3 * x) / 9 * (σO d / σO c) + σO (δ3 * x) * σO (3 * y) / 9 := by
    simp only [map_add, map_mul]
    field_simp
  rw [e, ebr_add, ebr_period, mul_one]

/-- **`S^t_m(c)` vanishes unless `c ≡ t (mod 3)`**: a nonzero summand needs `(c − dt, d)` to be a bottom
row, so `3 ∣ c − dt` and `d ≡ 1 (mod 3)`. -/
theorem cuspSmT_eq_zero {t m c : 𝓞 K} (h : ¬ (3 : 𝓞 K) ∣ c - t) : cuspSmT t m c = 0 := by
  rw [cuspSmT_eq]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  have hnb : ¬ BRow (c - repQ (3 * c) r * t, repQ (3 * c) r) := by
    rintro ⟨-, h3, hd⟩
    refine h ?_
    rw [show c - t = (c - repQ (3 * c) r * t) + t * (repQ (3 * c) r - 1) by ring]
    exact dvd_add h3 (dvd_mul_of_dvd_right hd t)
  unfold kubTermT wtCuspT cuspF
  rw [ite_eq_right hnb, zero_mul]

/-- **`S⁰_m(c)` vanishes unless `c` is primary.** -/
theorem cuspSm0_eq_zero {m c : 𝓞 K} (h : ¬ Primary c) : cuspSm0 m c = 0 := by
  rw [cuspSm0_eq]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  unfold kubTerm0 wtCusp0 cuspF
  rw [ite_eq_right (fun hb => h hb.2.2), zero_mul]

/-! ### The termwise identity -/

/-- `δ₃ = (ω − 1)·(−ω)`. -/
theorem δ3_eq_lam_neg : δ3 = (ω - 1) * -ω := by
  unfold δ3; linear_combination ω_sq_add

/-- The polynomial behind the exponents of the termwise identity. -/
def kubPoly (t t' u v a b a₁ b₁ : 𝓞 K) : 𝓞 K :=
  t * a * (3 * (-t' * ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ - u))) +
    t * a * (2 * (3 * (-t' * a₁))) + ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b + v * a) -
    t' * t * a - δ3 * (ω ^ 2 * t * (ω - 1) ^ 2) * t * b -
    3 * ((ω - 1) * (-ω * (-t' * ((ω - 1) * ω) * a₁ * (v * b₁ - u - v * a₁ + 1) +
      3 * t * b₁ * (3 * u + v)))) * t * a

/-- **The polynomial identity behind the exponents**, for `a = 1 + 3a₁`, `b = 3b₁`, `3u + va = 1` and
`tt′ = 1`. -/
theorem kubota_sum_poly {t t' u v a b a₁ b₁ : 𝓞 K} (huv : u * 3 + v * a = 1) (htt : t * t' = 1)
    (ha₁ : a - 1 = 3 * a₁) (hb₁ : b = 3 * b₁) :
    kubPoly t t' u v a b a₁ b₁ = 0 := by
  unfold kubPoly
  obtain rfl : a = 1 + 3 * a₁ := by linear_combination ha₁
  subst hb₁
  rw [δ3_eq_lam_neg]
  linear_combination (3*a₁^2*ω^4*t*t' - 6*a₁^2*ω^3*t*t' + 3*a₁^2*ω^2*t*t' + 9*a₁*b₁*ω^3*t^3*t'
    - 27*a₁*b₁*ω^2*t^3*t' + 27*a₁*b₁*ω^2*t^2 + 27*a₁*b₁*ω*t^3*t' - 27*a₁*b₁*ω*t^2 - 9*a₁*b₁*t^3*t'
    + a₁*ω^4*t*t' - 2*a₁*ω^3*t*t' + a₁*ω^2*t*t' + 3*a₁*t*t' + 3*b₁*ω^3*t^3*t' - 3*b₁*ω^3*t^2
    - 9*b₁*ω^2*t^3*t' + 18*b₁*ω^2*t^2 + 9*b₁*ω*t^3*t' - 18*b₁*ω*t^2 - 3*b₁*t^3*t' + 3*b₁*t^2 + t*t') * huv
    + (-9*a₁^2*b₁*ω^4*v - 27*a₁^2*b₁*ω^3*t^2*v + 18*a₁^2*b₁*ω^3*v + 81*a₁^2*b₁*ω^2*t^2*v - 9*a₁^2*b₁*ω^2*v
    - 81*a₁^2*b₁*ω*t^2*v + 27*a₁^2*b₁*t^2*v - 27*a₁^2*b₁*v - 3*a₁^2*ω^4*v - 6*a₁^2*ω^4 + 6*a₁^2*ω^3*v
    + 12*a₁^2*ω^3 - 3*a₁^2*ω^2*v - 6*a₁^2*ω^2 - 9*a₁^2*v - 18*a₁^2 - 3*a₁*b₁*ω^4*v - 18*a₁*b₁*ω^3*t^2*v
    + 9*a₁*b₁*ω^3*t^2 + 6*a₁*b₁*ω^3*v + 54*a₁*b₁*ω^2*t^2*v - 27*a₁*b₁*ω^2*t^2 - 3*a₁*b₁*ω^2*v
    - 54*a₁*b₁*ω*t^2*v + 27*a₁*b₁*ω*t^2 + 18*a₁*b₁*t^2*v - 9*a₁*b₁*t^2 - 18*a₁*b₁*v - a₁*ω^4*v - 2*a₁*ω^4
    + 2*a₁*ω^3*v + 4*a₁*ω^3 - a₁*ω^2*v - 2*a₁*ω^2 - 6*a₁*v - 6*a₁ - 3*b₁*ω^3*t^2*v + 3*b₁*ω^3*t^2
    + 9*b₁*ω^2*t^2*v - 9*b₁*ω^2*t^2 - 9*b₁*ω*t^2*v + 9*b₁*ω*t^2 + 3*b₁*t^2*v - 3*b₁*t^2 - 3*b₁*v - v) * htt
    + (-9*a₁^2*b₁*ω^2*v - 27*a₁^2*b₁*ω*t^2*v + 27*a₁^2*b₁*ω*v + 27*a₁^2*b₁*t^2*v - 27*a₁^2*b₁*v
    - 3*a₁^2*ω^2*v - 6*a₁^2*ω^2 + 9*a₁^2*ω*v + 18*a₁^2*ω - 9*a₁^2*v - 18*a₁^2 - 3*a₁*b₁*ω^2*v
    - 9*a₁*b₁*ω*t^2*v + 9*a₁*b₁*ω*t^2 + 9*a₁*b₁*ω*v + 9*a₁*b₁*t^2*v - 9*a₁*b₁*t^2 - 9*a₁*b₁*v - a₁*ω^2*v
    - 2*a₁*ω^2 + 3*a₁*ω*v + 6*a₁*ω - 3*a₁*v - 6*a₁ + 3*b₁*ω^4*t^2 - 12*b₁*ω^3*t^2 + 18*b₁*ω^2*t^2
    - 9*b₁*ω*t^2) * ω_sq_add

/-- **The termwise identity**: for `tt′ = 1`, `m` in the class of the cusp `γ_t`, `a` primary, `3u + va = 1`
and every `b`, the summand of `S^t_m(ta)` at `d = (va − 3uλ³t²)b + va` is `ĕ(mt′/9)` times the summand of
`S⁰_{m′}(a)` at `b`, with `m′ = δ₃ω²tλ²m = −tλ³m`. -/
theorem kubTermT_affine {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) {a : 𝓞 K}
    (ha : Primary a) {u v : 𝓞 K} (huv : u * 3 + v * a = 1) (b : 𝓞 K) :
    kubTermT t m (t * a) ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b + v * a) =
      ebr (σO m * σO t' / 9) * kubTerm0 (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) a b := by
  set d := (v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b + v * a with hd
  have hcopt : ∀ x : 𝓞 K, IsCoprime t x := fun x =>
    ⟨t', 0, by rw [zero_mul, add_zero, mul_comm]; exact htt⟩
  have hda : d + (ω - 1) ^ 3 * t ^ 2 * b = a * (v * (b + 1 + (ω - 1) ^ 3 * t ^ 2 * b)) := by
    simp only [hd]
    linear_combination (-((ω - 1) ^ 3 * t ^ 2 * b)) * huv
  have hd1 : d - 1 = b - 3 * (u + u * b + u * (ω - 1) ^ 3 * t ^ 2 * b) := by
    simp only [hd]
    linear_combination (b + 1) * huv
  have hlam : IsCoprime a ((ω - 1) ^ 3 * t ^ 2) :=
    ((isCoprime_lam_of_primary ha).symm.pow_right).mul_right ((hcopt a).symm.pow_right)
  have hcop_iff : IsCoprime a d ↔ IsCoprime a b := by
    constructor
    · intro h
      have h2 := h.neg_right.add_mul_left_right (v * (b + 1 + (ω - 1) ^ 3 * t ^ 2 * b))
      rw [show -d + a * (v * (b + 1 + (ω - 1) ^ 3 * t ^ 2 * b)) = (ω - 1) ^ 3 * t ^ 2 * b by
        linear_combination -hda] at h2
      exact h2.of_mul_right_right
    · intro h
      have h2 := ((hlam.mul_right h).neg_right).add_mul_left_right
        (v * (b + 1 + (ω - 1) ^ 3 * t ^ 2 * b))
      rwa [show -((ω - 1) ^ 3 * t ^ 2 * b) + a * (v * (b + 1 + (ω - 1) ^ 3 * t ^ 2 * b)) = d by
        linear_combination -hda] at h2
  have hbrow : BRow (t * a - d * t, d) ↔ BRow (-b, a) := by
    constructor
    · rintro ⟨hcop, -, hpd⟩
      have h1 : IsCoprime a d := by
        have h := hcop.add_mul_right_left t
        rw [show t * a - d * t + t * d = t * a by ring] at h
        exact h.of_mul_left_right
      refine ⟨(hcop_iff.1 h1).symm.neg_left, ?_, ha⟩
      rw [dvd_neg]
      rw [show b = (d - 1) + 3 * (u + u * b + u * (ω - 1) ^ 3 * t ^ 2 * b) by linear_combination -hd1]
      exact dvd_add hpd (dvd_mul_right _ _)
    · rintro ⟨hcop, h3, -⟩
      have h3b : (3 : 𝓞 K) ∣ b := (dvd_neg).1 h3
      have hpd : Primary d := by
        show (3 : 𝓞 K) ∣ d - 1
        rw [hd1]
        exact dvd_sub h3b (dvd_mul_right _ _)
      have h1 : IsCoprime a d := hcop_iff.2 (by simpa using hcop.symm.neg_right)
      refine ⟨?_, ?_, hpd⟩
      · have h5 := ((hcopt d).mul_left h1).add_mul_right_left (-t)
        rwa [show t * a + -t * d = t * a - d * t by ring] at h5
      · rw [show t * a - d * t = t * ((a - 1) - (d - 1)) by ring]
        exact dvd_mul_of_dvd_right (dvd_sub ha hpd) t
  unfold kubTermT kubTerm0 wtCuspT wtCusp0 cuspF
  by_cases hb : BRow (-b, a)
  · have hb' := hbrow.2 hb
    rw [ite_eq_left hb', ite_eq_left hb]
    have hpd : Primary d := hb'.2.2
    have h1 : IsCoprime a d := hcop_iff.2 (by simpa using hb.1.symm.neg_right)
    have e1 : cub (t * a - d * t) (span {d}) = cub t (span {d}) * cub d (span {a}) := by
      rw [cub_congr (show d ∣ (t * a - d * t) - t * a from ⟨-t, by ring⟩), cub_mul_left,
        cub_recip ha hpd h1]
    have e2 : cub d (span {a}) = cub t (span {a}) ^ 2 * cub b (span {a}) := by
      rw [cub_congr (show a ∣ d - -((ω - 1) ^ 3 * t ^ 2 * b) from
          ⟨v * (b + 1 + (ω - 1) ^ 3 * t ^ 2 * b), by linear_combination hda⟩), cub_neg ha,
        cub_mul_left, cub_mul_left, cub_pow_left ha, cub_pow_left ha,
        cub_pow_three ha (isCoprime_lam_of_primary ha), one_mul]
    rw [e1, e2, cub_neg ha]
    obtain ⟨a₁, ha₁⟩ := ha
    obtain ⟨b₁, hb₁⟩ := (dvd_neg).1 hb.2.1
    have hσa : σO a ≠ 0 := σO_ne_zero (primary_ne_zero ⟨a₁, ha₁⟩)
    have hσt : σO t ≠ 0 := σO_ne_zero (left_ne_zero_of_mul_eq_one htt)
    have hdD : 1 - 3 * t * (-t' * ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ - u)) = d := by
      rw [hd]
      linear_combination (3 * (v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ - 3 * u) * htt -
        (v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * hb₁ - huv
    have hcd : σO (cub t (span {d})) =
        ebr (σO m * σO (3 * (-t' * ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ - u))) / 9) := by
      rw [hm, chiT, hdD]
    have hca : σO (cub t (span {a})) = ebr (σO m * σO (3 * (-t' * a₁)) / 9) := by
      rw [hm, chiT, show 1 - 3 * t * (-t' * a₁) = a by linear_combination 3 * a₁ * htt - ha₁]
    have hP := kubota_sum_poly huv htt ha₁ hb₁
    have key : σO m * σO (3 * (-t' * ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ - u))) / 9 +
        σO m * σO (3 * (-t' * a₁)) / 9 + σO m * σO (3 * (-t' * a₁)) / 9 +
        σO m / 9 * (σO d / σO (t * a)) =
        σO m * σO t' / 9 + σO (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) / 9 * (σO b / σO a) +
          σO m * σO (3 * ((ω - 1) * (-ω * (-t' * ((ω - 1) * ω) * a₁ * (v * b₁ - u - v * a₁ + 1) +
            3 * t * b₁ * (3 * u + v))))) / 9 := by
      have e : σO m * σO (3 * (-t' * ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ - u))) / 9 +
          σO m * σO (3 * (-t' * a₁)) / 9 + σO m * σO (3 * (-t' * a₁)) / 9 +
          σO m / 9 * (σO d / σO (t * a)) -
          (σO m * σO t' / 9 + σO (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) / 9 * (σO b / σO a) +
            σO m * σO (3 * ((ω - 1) * (-ω * (-t' * ((ω - 1) * ω) * a₁ * (v * b₁ - u - v * a₁ + 1) +
              3 * t * b₁ * (3 * u + v))))) / 9) =
          σO m / (9 * (σO t * σO a)) * σO (kubPoly t t' u v a b a₁ b₁) := by
        rw [hd]
        unfold kubPoly
        simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
        field_simp
        ring
      rw [hP, map_zero, mul_zero, sub_eq_zero] at e
      exact e
    rw [map_mul, map_mul, map_pow, hcd, hca]
    have hZ := ebr_lam_mul m (-ω * (-t' * ((ω - 1) * ω) * a₁ * (v * b₁ - u - v * a₁ + 1) +
      3 * t * b₁ * (3 * u + v)))
    rw [show ebr (σO m * σO (3 * (-t' * ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ - u))) / 9) *
        (ebr (σO m * σO (3 * (-t' * a₁)) / 9) ^ 2 * σO (cub b (span {a}))) *
          ebr (σO m / 9 * (σO d / σO (t * a))) =
        σO (cub b (span {a})) * ebr (σO m * σO (3 * (-t' * ((v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) * b₁ -
          u))) / 9 + σO m * σO (3 * (-t' * a₁)) / 9 + σO m * σO (3 * (-t' * a₁)) / 9 +
          σO m / 9 * (σO d / σO (t * a))) by
      rw [ebr_add, ebr_add, ebr_add]; ring, key, ebr_add, ebr_add, hZ]
    ring
  · rw [ite_eq_right (fun h => hb (hbrow.1 h)), ite_eq_right hb, zero_mul, zero_mul, mul_zero]

/-! ### The identity of the Kubota sums -/

/-- **The Kubota sums at `γ_t` and at `0`**, for `a` primary: `S^t_m(ta) = ĕ(mt′/9)·S⁰_{m′}(a)` with
`m′ = δ₃ω²tλ²m`, through the affine change of class `b ↦ (va − 3uλ³t²)b + va` modulo `3a`. -/
theorem cuspSmT_mul_primary {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) {a : 𝓞 K}
    (ha : Primary a) :
    cuspSmT t m (t * a) = ebr (σO m * σO t' / 9) * cuspSm0 (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) a := by
  obtain ⟨u, v, huv⟩ := isCoprime_three_of_primary ha
  have ha0 : a ≠ 0 := primary_ne_zero ha
  have ht0 : t ≠ 0 := left_ne_zero_of_mul_eq_one htt
  have hta : t * a ≠ 0 := mul_ne_zero ht0 ha0
  have hcopt : ∀ x : 𝓞 K, IsCoprime t x := fun x =>
    ⟨t', 0, by rw [zero_mul, add_zero, mul_comm]; exact htt⟩
  have hspan : span {3 * (t * a)} = span {3 * a} := by
    rw [show 3 * (t * a) = 3 * a * t by ring]
    exact span_singleton_mul_right_unit (Units.mkOfMulEqOne t t' htt).isUnit _
  have hα : IsCoprime (v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2) (3 * a) := by
    refine IsCoprime.mul_right ⟨1, u + u * (ω - 1) ^ 3 * t ^ 2, by linear_combination huv⟩ ?_
    have hl : IsCoprime ((ω - 1) ^ 3 * t ^ 2) a :=
      (isCoprime_lam_of_primary ha).pow_left.mul_left (hcopt a).pow_left
    have h2 := hl.neg_left.add_mul_left_left (v * (1 + (ω - 1) ^ 3 * t ^ 2))
    rwa [show -((ω - 1) ^ 3 * t ^ 2) + a * (v * (1 + (ω - 1) ^ 3 * t ^ 2)) =
      v * a - 3 * u * (ω - 1) ^ 3 * t ^ 2 by linear_combination ((ω - 1) ^ 3 * t ^ 2) * huv] at h2
  have hper : ∀ x y, kubTermT t m (t * a) (x + 3 * a * y) = kubTermT t m (t * a) x := by
    intro x y
    have h := kubTermT_periodic hm hta x (t' * y)
    rwa [show x + 3 * (t * a) * (t' * y) = x + 3 * a * y by linear_combination 3 * a * y * htt] at h
  rw [cuspSmT_eq, tsum_repQ_eq_of_span hspan (kubTermT_periodic hm hta),
    ← tsum_repQ_affine hα (v * a) hper, cuspSm0_eq, ← tsum_mul_left]
  exact tsum_congr fun r => kubTermT_affine htt hm ha huv _

/-- **The Kubota sums at `γ_t` and at `0`**, for every `a`: both sides vanish when `a` is not primary. -/
theorem cuspSmT_mul {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (a : 𝓞 K) :
    cuspSmT t m (t * a) = ebr (σO m * σO t' / 9) * cuspSm0 (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) a := by
  by_cases ha : Primary a
  · exact cuspSmT_mul_primary htt hm ha
  · rw [cuspSm0_eq_zero ha, mul_zero]
    refine cuspSmT_eq_zero fun h => ha ?_
    have h2 : (3 : 𝓞 K) ∣ t' * (t * a - t) := dvd_mul_of_dvd_right h t'
    rwa [show t' * (t * a - t) = a - 1 by linear_combination (a - 1) * htt] at h2

/-- **The Dirichlet series at `γ_t` and at `0`**: for `tt′ = 1` and `m` in the class of the cusp,
`Σ_c S^t_m(c)N(c)^{−s} = ĕ(mt′/9)·Σ_a S⁰_{m′}(a)N(a)^{−s}` for every `s`, `m′ = δ₃ω²tλ²m`. -/
theorem tsum_cuspSmT_eq {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (s : ℂ) :
    ∑' c : 𝓞 K, cuspSmT t m c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) =
      ebr (σO m * σO t' / 9) * ∑' a : 𝓞 K,
        cuspSm0 (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) a * ((Complex.normSq (σO a) : ℝ) : ℂ) ^ (-s) := by
  set U := Units.mkOfMulEqOne t t' htt
  have hU : (U : 𝓞 K) = t := rfl
  rw [← U.mulLeft.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun a => ?_
  rw [Units.mulLeft_apply, hU, cuspSmT_mul htt hm, map_mul, Complex.normSq_mul, ← hU, normSq_σO_unit,
    one_mul]
  ring

/-! ### The pairings at `γ_t` and at `0` -/

/-- **The size of the index at the cusp `0`**: `|m′/9| = 3√3·|m/9|` for `m′ = δ₃ω²tλ²m`, `t` a unit. -/
theorem norm_σO_cuspIdx {t t' : 𝓞 K} (htt : t * t' = 1) (m : 𝓞 K) :
    ‖σO (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) / 9‖ = 3 * Real.sqrt 3 * ‖σO m / 9‖ := by
  have hω : Complex.normSq (σO ω) = 1 := by rw [← coe_ωu]; exact normSq_σO_unit ωu
  have ht : Complex.normSq (σO t) = 1 := normSq_σO_unit (Units.mkOfMulEqOne t t' htt)
  have hδ : Complex.normSq (σO δ3) = 3 := by
    rw [δ3_eq_lam_neg, map_mul, map_neg, Complex.normSq_mul, Complex.normSq_neg, hω, normSq_σO_lam,
      mul_one]
  have h1 : Complex.normSq (σO (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m))) = 27 * Complex.normSq (σO m) := by
    simp only [map_mul, map_pow, hω, ht, hδ, normSq_σO_lam]
    ring
  have h27 : Real.sqrt 27 = 3 * Real.sqrt 3 := by
    rw [show (27 : ℝ) = 3 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [norm_div, norm_div, Complex.norm_def (σO (δ3 * _)), h1, Real.sqrt_mul (by norm_num), h27,
    ← Complex.norm_def]
  ring

/-- **`J_ψ` rescaled**: for `c > 0`, `J` of `v ↦ ψ(cv)` at `c·a` is `c` times `J_ψ` at `a` (round 430's
`jPsi`). -/
theorem jPsi_comp_mul {c : ℝ} (hc : 0 < c) (a : ℝ) (ψ : ℝ → ℂ) (s : ℂ) :
    jPsi (c * a) (fun v => ψ (c * v)) s = c * jPsi a ψ s := by
  unfold jPsi
  set g : ℝ → ℂ := fun w => conj (ψ w) * (((w ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (s - 1) (a * w)) with hg
  have hcc : (c ^ 2 : ℝ) * c ^ (-2 : ℤ) = 1 := by
    rw [zpow_neg, zpow_ofNat]
    field_simp
  have e : ∀ v : ℝ, conj (ψ (c * v)) * (((v ^ (-2 : ℤ) : ℝ) : ℂ) * besselK (s - 1) (c * a * v)) =
      ((c ^ 2 : ℝ) : ℂ) * g (c * v) := by
    intro v
    simp only [hg]
    rw [show c * a * v = a * (c * v) by ring, mul_zpow]
    have h2 : ((c ^ 2 : ℝ) : ℂ) * ((c ^ (-2 : ℤ) * v ^ (-2 : ℤ) : ℝ) : ℂ) = ((v ^ (-2 : ℤ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← mul_assoc, hcc, one_mul]
    rw [show ((c ^ 2 : ℝ) : ℂ) * (conj (ψ (c * v)) * (((c ^ (-2 : ℤ) * v ^ (-2 : ℤ) : ℝ) : ℂ) *
        besselK (s - 1) (a * (c * v)))) = conj (ψ (c * v)) * ((((c ^ 2 : ℝ) : ℂ) *
        ((c ^ (-2 : ℤ) * v ^ (-2 : ℤ) : ℝ) : ℂ)) * besselK (s - 1) (a * (c * v))) by ring, h2]
  simp_rw [e]
  rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hc, mul_zero, Complex.real_smul]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

/-- `v ↦ ψ(3√3·v)`. -/
def sclPsi (ψ : ℝ → ℂ) (v : ℝ) : ℂ := ψ (3 * Real.sqrt 3 * v)

theorem sqrt27_pos : (0 : ℝ) < 3 * Real.sqrt 3 := by positivity

theorem measurable_sclPsi {ψ : ℝ → ℂ} (hψ : Measurable ψ) : Measurable (sclPsi ψ) :=
  hψ.comp (measurable_const_mul _)

theorem norm_sclPsi_le {ψ : ℝ → ℂ} {M : ℝ} (hM : ∀ v, ‖ψ v‖ ≤ M) (v : ℝ) : ‖sclPsi ψ v‖ ≤ M := hM _

theorem sclPsi_eq_zero {ψ : ℝ → ℂ} {α β : ℝ} (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (v : ℝ)
    (hv : v ∉ Icc (α / (3 * Real.sqrt 3)) (β / (3 * Real.sqrt 3))) : sclPsi ψ v = 0 := by
  refine hψ0 _ fun h => hv ⟨?_, ?_⟩
  · rw [div_le_iff₀ sqrt27_pos]; linarith [h.1]
  · rw [le_div_iff₀ sqrt27_pos]; linarith [h.2]

/-- **The pairings at `γ_t` and at `0`**: for `tt′ = 1`, `m ≠ 0` in the class of the cusp `γ_t`, `ψ`
measurable and bounded, vanishing outside `[α, β]` with `0 < α ≤ β`, `ψ̃(v) = ψ(3√3·v)`, `Re s > 2` and
`Im ĥ(s) ≠ 0`, the pairing of `Q_t(ψ)` with `ũ_s` plus its band term is `ĕ(mt′/9)·(3√3)^{−s}` times the same
for `P_{m′}(ψ̃)∘S⁻¹`, `m′ = δ₃ω²tλ²m`. -/
theorem inner_pmSerC_uL_eq {t t' m : 𝓞 K} (htt : t * t' = 1) (hm : CuspClass t m) (hm0 : m ≠ 0)
    {R : ℝ} (hR : 0 ≤ R) {Y : ℝ} (hY : 0 < Y) {ψ : ℝ → ℂ} (hψ : Measurable ψ) {M α β : ℝ}
    (hM : ∀ v, ‖ψ v‖ ≤ M) (hψ0 : ∀ v, v ∉ Icc α β → ψ v = 0) (hα : 0 < α) (hαβ : α ≤ β) {s : ℂ}
    (hs : 2 < s.re) (him : (hhat R s).im ≠ 0) :
    inner ℂ ((memLp_pmSerC_Icc t m hψ hM hψ0 hα).toLp (pmSerC t m ψ)) (uL R hR Y hY s) +
        inner ℂ ((memLp_pmSerC_Icc t m hψ hM hψ0 hα).toLp (pmSerC t m ψ))
          (bandL hY (le_band hα hαβ) s) =
      ebr (σO m * σO t' / 9) * ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (-s) *
        (inner ℂ ((memLp_pmSerS (measurable_sclPsi hψ) (memLp_pmSer_Icc (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m))
            (measurable_sclPsi hψ) (norm_sclPsi_le hM) (sclPsi_eq_zero hψ0)
            (div_pos hα sqrt27_pos))).toLp (pmSerS (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) (sclPsi ψ)))
            (uL R hR Y hY s) +
          inner ℂ ((memLp_pmSerS (measurable_sclPsi hψ) (memLp_pmSer_Icc (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m))
            (measurable_sclPsi hψ) (norm_sclPsi_le hM) (sclPsi_eq_zero hψ0)
            (div_pos hα sqrt27_pos))).toLp (pmSerS (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) (sclPsi ψ)))
            (bandL hY (le_band (div_pos hα sqrt27_pos)
              (div_le_div_of_nonneg_right hαβ sqrt27_pos.le)) s)) := by
  have ht : IsUnit t := (Units.mkOfMulEqOne t t' htt).isUnit
  have ht0 : t ≠ 0 := left_ne_zero_of_mul_eq_one htt
  have hx : ω ^ 2 * t * (ω - 1) ^ 2 * m ≠ 0 := by
    have hω0 : ω ≠ 0 := by rw [← coe_ωu]; exact ωu.ne_zero
    have hl0 : (ω - 1 : 𝓞 K) ≠ 0 := fun h => by
      have := normSq_σO_lam; rw [h, map_zero, Complex.normSq_zero] at this; norm_num at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hω0) ht0) (pow_ne_zero 2 hl0)) hm0
  rw [inner_pmSerC_uL ht hm hm0 hR hY hψ _ hM hψ0 hα hαβ hs him,
    inner_pmSerS_uL hx hR hY (measurable_sclPsi hψ) (memLp_pmSer_Icc (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m))
      (measurable_sclPsi hψ) (norm_sclPsi_le hM) (sclPsi_eq_zero hψ0) (div_pos hα sqrt27_pos))
      (norm_sclPsi_le hM)
      (sclPsi_eq_zero hψ0)
      (div_pos hα sqrt27_pos) (div_le_div_of_nonneg_right hαβ sqrt27_pos.le) hs him,
    sub_add_cancel, sub_add_cancel, tsum_cuspSmT_eq htt hm, norm_σO_cuspIdx htt,
    show 4 * Real.pi * (3 * Real.sqrt 3 * ‖σO m / 9‖) = 3 * Real.sqrt 3 * (4 * Real.pi * ‖σO m / 9‖) by ring,
    show sclPsi ψ = fun v => ψ (3 * Real.sqrt 3 * v) from rfl, jPsi_comp_mul sqrt27_pos,
    show 2 * Real.pi * (3 * Real.sqrt 3 * ‖σO m / 9‖) = (3 * Real.sqrt 3) * (2 * Real.pi * ‖σO m / 9‖) by
      ring, Complex.ofReal_mul (3 * Real.sqrt 3),
    Complex.mul_cpow_ofReal_nonneg sqrt27_pos.le (by positivity)]
  have hc0 : ((3 * Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sqrt27_pos.ne'
  have hcp : ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (-s) * ((3 * Real.sqrt 3 : ℝ) : ℂ) ^ (s - 1) *
      ((3 * Real.sqrt 3 : ℝ) : ℂ) = 1 := by
    rw [← Complex.cpow_add _ _ hc0, show -s + (s - 1) = -1 by ring, Complex.cpow_neg_one,
      inv_mul_cancel₀ hc0]
  linear_combination (-(2 * Real.pi / Complex.Gamma s *
    ((2 * Real.pi * ‖σO m / 9‖ : ℝ) : ℂ) ^ (s - 1) * (ebr (σO m * σO t' / 9) *
      ∑' a : 𝓞 K, cuspSm0 (δ3 * (ω ^ 2 * t * (ω - 1) ^ 2 * m)) a *
        ((Complex.normSq (σO a) : ℝ) : ℂ) ^ (-s)) *
      jPsi (4 * Real.pi * ‖σO m / 9‖) ψ s)) * hcp

end Eis

end

#print axioms Eis.eq_of_mk_eq_of_periodic
#print axioms Eis.tsum_repQ_eq_of_span
#print axioms Eis.tsum_repQ_affine
#print axioms Eis.cuspSmT_eq
#print axioms Eis.cuspSm0_eq
#print axioms Eis.kubTermT_periodic
#print axioms Eis.kubTerm0_periodic
#print axioms Eis.cuspSmT_eq_zero
#print axioms Eis.cuspSm0_eq_zero
#print axioms Eis.δ3_eq_lam_neg
#print axioms Eis.kubota_sum_poly
#print axioms Eis.kubTermT_affine
#print axioms Eis.cuspSmT_mul_primary
#print axioms Eis.cuspSmT_mul
#print axioms Eis.tsum_cuspSmT_eq
#print axioms Eis.norm_σO_cuspIdx
#print axioms Eis.jPsi_comp_mul
#print axioms Eis.sqrt27_pos
#print axioms Eis.measurable_sclPsi
#print axioms Eis.norm_sclPsi_le
#print axioms Eis.sclPsi_eq_zero
#print axioms Eis.inner_pmSerC_uL_eq
