import EisensteinCubicRecip
import EisensteinPoisson
import EisensteinGaussPrime
import HalfPlaneMeanSquare
import EisensteinGaussSum

/-! # The supplementary laws of cubic reciprocity, as periodicity modulo `9` (round 362)

S5f-2a of round 360's plan. The twist `φ` of the companion paper's Appendix A.2 contains `χ_n(λ)²`, and
its finite Fourier expansion needs `φ` periodic: "`The supplementary law of cubic reciprocity for
$\lambda$ \cite[(1.5)]{DR}, which evaluates $\chi_n(\lambda)^2=(\lambda/n)_3$, makes $\phi$ periodic modulo
$L$`". This file proves that periodicity from cubic reciprocity alone, by the release's comparison
(its `ramified_comparison`) with `1` and `−2` as comparison points, and the multiplicativity of the
symbol in the inert prime `2`. It does not evaluate the supplementary laws.

* **The cubic symbol** (`cub_mul_left`, `cub_congr`, `cub_neg`, `cub_one`, `cub_one_right`,
  `cub_pow_three`, `cub_ne_zero`): multiplicative in the numerator, depends on it modulo the
  denominator, and takes cube roots of unity on coprime arguments.
* **The comparison** (`cub_compare`): if `p − q = δ₃²·u·r` with `p, q, r` primary and `p, q` coprime,
  then `(δ₃/p)₃²(u/p)₃ = (δ₃/q)₃²(u/q)₃`. Both sides of `((p − q)/p)₃ = ((p − q)/q)₃` expand, and
  `(r/p)₃ = (p/r)₃ = (q/r)₃ = (r/q)₃` cancels.
* **The supplement for `ω`** (`chi3_omega`, `cub_omega`): `(ω/b)₃ = ω^{(N(b)−1)/3}` for primary `b`; so
  it depends only on `b mod 9` (`absNorm_congr_nine`, `cub_omega_congr`), and so do the symbols of all
  units (`cub_unit_congr`).
* **The supplement for `λ`** (`cub_δ3_congr_odd`, `cub_δ3_congr`): for primary `p, p'` with
  `p ≡ p' (mod 9)`, `(δ₃/p)₃ = (δ₃/p')₃`. For `p, p'` prime to `2`, write `p − 1 = 3t`. If `λ ∤ t`, the
  comparison with `q = 1` applies; if `λ ∣ t`, the comparison with `q = −2` does. The unit `u` and the
  right-hand side are the same for `p` and `p'`, and two cube roots of unity with equal squares are
  equal. For `p` divisible by `2`: `(δ₃/−2)₃ = 1` because `δ₃ ≡ 1 (mod 2)` (`cub_δ3_neg_two`), and
  `(δ₃/7)₃ = 1` by the comparison of `7` with `1` (`cub_δ3_seven`); dividing out `−2` and multiplying
  by `7 ≡ −2 (mod 9)` reaches an element prime to `2` with the same symbol and the same class modulo
  `9` (`exists_odd_rep`, by induction on the norm).
* **At `x ≡ 1 (mod 9)`** (`cub_δ3_of_nine`, `cub_unit_of_nine`): `(δ₃/x)₃ = 1` and `(u/x)₃ = 1` for every
  unit `u`, the vanishing of the supplementary factors that the paper's (A.10) uses.
* **In the sextic symbol** (`chiP_sq`, `sym6_sq_eq_cub`, `sym6_sq_δ3_congr`, `sym6_sq_omega_congr`):
  `(a/𝔫)₆² = σ((a/𝔫)₃)` for `N(𝔫)` prime to `6`, so `χ_n(δ₃)²` and `χ_n(ω)²` depend only on `n mod 9`.
-/

open NumberField Ideal UniqueFactorizationMonoid

noncomputable section

namespace Eis

theorem cub_mul_left (x y : 𝓞 K) (I : Ideal (𝓞 K)) : cub (x * y) I = cub x I * cub y I := by
  unfold cub
  rw [← Multiset.prod_map_mul]
  congr 1
  exact Multiset.map_congr rfl fun P _ => chi3_mul P x y

theorem cub_congr {x y b : 𝓞 K} (h : b ∣ x - y) : cub x (span {b}) = cub y (span {b}) := by
  unfold cub
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  have hb : b ∈ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP) (Ideal.mem_span_singleton_self b)
  have hxy : x - y ∈ P := by
    obtain ⟨c, hc⟩ := h; rw [hc]; exact P.mul_mem_right c hb
  have : x = y + (x - y) := by ring
  rw [this, chi3_add_mem y hxy]

theorem cub_one_right (x : 𝓞 K) : cub x (span {(1 : 𝓞 K)}) = 1 := by
  unfold cub
  rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, normalizedFactors_one]
  simp

theorem cub_neg {x b : 𝓞 K} (hb : Primary b) : cub (-x) (span {b}) = cub x (span {b}) := by
  unfold cub
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  have := isMaximal_of_mem_nf hP
  exact chi3_neg (three_not_mem_nf hb hP) x

theorem chi3_cube_of_coprime {x b : 𝓞 K} (hb : Primary b) (hxb : IsCoprime x b) {P : Ideal (𝓞 K)}
    (hP : P ∈ normalizedFactors (span {b})) : chi3 P x ^ 3 = 1 := by
  have := isMaximal_of_mem_nf hP
  refine chi3_pow_three (three_not_mem_nf hb hP) fun hx => ?_
  have hbP : b ∈ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP) (Ideal.mem_span_singleton_self b)
  obtain ⟨u, v, huv⟩ := hxb
  apply IsMaximal.ne_top ‹P.IsMaximal›
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left u hx) (P.mul_mem_left v hbP)

theorem cub_pow_three {x b : 𝓞 K} (hb : Primary b) (hxb : IsCoprime x b) : cub x (span {b}) ^ 3 = 1 := by
  unfold cub
  rw [← Multiset.prod_map_pow]
  exact Multiset.prod_eq_one fun y hy => by
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hy
    exact chi3_cube_of_coprime hb hxb hP

theorem cub_ne_zero {x b : 𝓞 K} (hb : Primary b) (hxb : IsCoprime x b) : cub x (span {b}) ≠ 0 := by
  intro h
  have := cub_pow_three hb hxb
  rw [h] at this; norm_num at this

/-- Two cube roots of unity with the same square are equal. -/
theorem eq_of_sq_eq_cube {x y : 𝓞 K} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (h : x ^ 2 = y ^ 2) : x = y := by
  calc x = x * x ^ 3 := by rw [hx, mul_one]
    _ = (x ^ 2) ^ 2 := by ring
    _ = (y ^ 2) ^ 2 := by rw [h]
    _ = y * y ^ 3 := by ring
    _ = y := by rw [hy, mul_one]

theorem isCoprime_of_sub {p q r s : 𝓞 K} (hpq : IsCoprime p q) (h : p - q = r * s) :
    IsCoprime r p ∧ IsCoprime r q := by
  obtain ⟨a, b, hab⟩ := hpq
  refine ⟨⟨-(b * s), a + b, ?_⟩, ⟨a * s, a + b, ?_⟩⟩
  · have hq : q = p - r * s := by rw [← h]; ring
    rw [hq] at hab; linear_combination hab
  · have hp : p = q + r * s := by rw [← h]; ring
    rw [hp] at hab; linear_combination hab

/-- **The comparison** (the release's `ramified_comparison`, for elements): if `p − q = δ₃²·u·r` with
`p, q, r` primary and `p, q` coprime, then `(δ₃/p)₃²(u/p)₃ = (δ₃/q)₃²(u/q)₃`. -/
theorem cub_compare {p q r u : 𝓞 K} (hp : Primary p) (hq : Primary q) (hr : Primary r)
    (hpq : IsCoprime p q) (h : p - q = δ3 ^ 2 * u * r) :
    cub δ3 (span {p}) ^ 2 * cub u (span {p}) = cub δ3 (span {q}) ^ 2 * cub u (span {q}) := by
  have hrs : p - q = r * (δ3 ^ 2 * u) := by rw [h]; ring
  obtain ⟨hrp, hrq⟩ := isCoprime_of_sub hpq hrs
  have e1 : cub (p - q) (span {p}) = cub (p - q) (span {q}) := by
    have a1 : cub (p - q) (span {p}) = cub (-q) (span {p}) := cub_congr ⟨1, by ring⟩
    have a2 : cub p (span {q}) = cub (p - q) (span {q}) := cub_congr ⟨1, by ring⟩
    rw [a1, cub_neg hp, cub_recip hq hp hpq.symm, a2]
  have e2 : cub r (span {p}) = cub r (span {q}) := by
    rw [cub_recip hr hp hrp, cub_congr (b := r) (x := p) (y := q) ⟨δ3 ^ 2 * u, hrs⟩,
      cub_recip hq hr hrq.symm]
  have hne : cub r (span {q}) ≠ 0 := cub_ne_zero hq hrq
  rw [h, cub_mul_left, cub_mul_left, sq, cub_mul_left, cub_mul_left, cub_mul_left, cub_mul_left,
    e2] at e1
  have e3 := mul_right_cancel₀ hne e1
  rw [sq, sq]
  exact e3

/-- `(ω/P)₃ = ω^{(N(P)−1)/3}` at a maximal ideal prime to `3`. -/
theorem chi3_omega {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) :
    chi3 P ω = ω ^ m3 P := by
  rw [chi3_eq hP3]
  have hu : IsUnit (Ideal.Quotient.mk P ω) := ωu.isUnit.map _
  obtain ⟨x, hx⟩ := hu
  have hs := cubChar_spec P hP3 x
  rw [hx] at hs
  have h1 : (ω ^ m3 P) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ω_cube, one_pow]
  refine cube_eq_of_mk_eq P hP3 hs.2 h1 ?_
  rw [hs.1, map_pow]

theorem absNorm_mod_three {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P) :
    absNorm P % 3 = 1 ∧ m3 P = (absNorm P - 1) / 3 := by
  have h := three_dvd_card_sub_one P hP3
  rw [← absNorm_eq_card] at h
  have h1 : 1 ≤ absNorm P := by
    have : absNorm P ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff]; exact ne_bot P
    omega
  refine ⟨by omega, ?_⟩
  rw [m3, absNorm_eq_card]

theorem omega_pow_mod (n : ℕ) : (ω : 𝓞 K) ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ω_cube, one_pow, one_mul]

/-- The product formula behind `(ω/b)₃ = ω^{(N(b)−1)/3}`. -/
theorem prod_chi3_omega (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ P ∈ s, P.IsMaximal ∧ (3 : 𝓞 K) ∉ P) :
    (s.map fun P => chi3 P ω).prod = ω ^ (((s.map absNorm).prod - 1) / 3) ∧
      (s.map absNorm).prod % 3 = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    have hP := hs P (Multiset.mem_cons_self P s)
    have := hP.1
    obtain ⟨ih1, ih2⟩ := ih fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hN, hm⟩ := absNorm_mod_three hP.2
    simp only [Multiset.map_cons, Multiset.prod_cons]
    set a := absNorm P
    set b := (s.map absNorm).prod
    refine ⟨?_, by rw [Nat.mul_mod, hN, ih2]⟩
    rw [ih1, chi3_omega hP.2, hm, ← pow_add, omega_pow_mod, omega_pow_mod (((a * b) - 1) / 3)]
    congr 1
    obtain ⟨k, hk⟩ : ∃ k, a = 3 * k + 1 := ⟨a / 3, by omega⟩
    obtain ⟨l, hl⟩ : ∃ l, b = 3 * l + 1 := ⟨b / 3, by omega⟩
    rw [hk, hl]
    have e1 : (3 * k + 1 - 1) / 3 = k := by omega
    have e2 : (3 * l + 1 - 1) / 3 = l := by omega
    have e3 : ((3 * k + 1) * (3 * l + 1) - 1) / 3 = 3 * k * l + k + l := by
      have : (3 * k + 1) * (3 * l + 1) = 3 * (3 * k * l + k + l) + 1 := by ring
      rw [this, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e1, e2, e3, show 3 * k * l + k + l = (k + l) + 3 * (k * l) by ring,
      Nat.add_mul_mod_self_left]

theorem nf_spec {b : 𝓞 K} (hb : Primary b) :
    ∀ P ∈ normalizedFactors (span {b}), P.IsMaximal ∧ (3 : 𝓞 K) ∉ P :=
  fun _ hP => ⟨isMaximal_of_mem_nf hP, three_not_mem_nf hb hP⟩

theorem absNorm_span_eq_prod {b : 𝓞 K} (hb : b ≠ 0) :
    absNorm (span {b}) = ((normalizedFactors (span {b})).map absNorm).prod := by
  have h0 : span {b} ≠ ⊥ := by rwa [Ne, span_singleton_eq_bot]
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
  rw [Multiset.prod_hom]

theorem primary_ne_zero {b : 𝓞 K} (hb : Primary b) : b ≠ 0 := by
  rintro rfl
  exact Primary.not_lam_dvd hb (dvd_zero _)

/-- **The supplement for `ω`**: `(ω/b)₃ = ω^{(N(b)−1)/3}` for primary `b`. -/
theorem cub_omega {b : 𝓞 K} (hb : Primary b) :
    cub ω (span {b}) = ω ^ ((absNorm (span {b}) - 1) / 3) := by
  rw [absNorm_span_eq_prod (primary_ne_zero hb)]
  exact (prod_chi3_omega _ (nf_spec hb)).1

theorem absNorm_primary_mod {b : 𝓞 K} (hb : Primary b) : absNorm (span {b}) % 3 = 1 := by
  rw [absNorm_span_eq_prod (primary_ne_zero hb)]
  exact (prod_chi3_omega _ (nf_spec hb)).2

theorem cub_one {b : 𝓞 K} (hb : Primary b) : cub 1 (span {b}) = 1 := by
  unfold cub
  exact Multiset.prod_eq_one fun y hy => by
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hy
    have := isMaximal_of_mem_nf hP
    exact chi3_one (three_not_mem_nf hb hP)

/-- An integer divisible in `ℤ[ω]` is divisible in `ℤ`. -/
theorem int_dvd_of_dvd {a n : ℤ} (h : (a : 𝓞 K) ∣ (n : 𝓞 K)) : a ∣ n := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨x, y, rfl⟩ := exists_coords z
  have e : crd ![n, 0] = crd ![a * x, a * y] := by
    simp only [crd, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast; rw [hz]; ring
  have := congrFun (crd_injective e) 0
  simp only [Matrix.cons_val_zero] at this
  exact ⟨x, this⟩

/-- `b ≡ b' (mod 9)` gives `N(b) ≡ N(b') (mod 9)`. -/
theorem absNorm_congr_nine {b b' : 𝓞 K} (h : (9 : 𝓞 K) ∣ b - b') :
    ((absNorm (span {b}) : ℤ) - absNorm (span {b'})) % 9 = 0 := by
  have h1 := mul_cj_eq_absNorm b
  have h2 := mul_cj_eq_absNorm b'
  have hc : (9 : 𝓞 K) ∣ cj b - cj b' := by
    obtain ⟨z, hz⟩ := h
    exact ⟨cj z, by rw [← map_sub, hz, map_mul, map_ofNat]⟩
  have h3 : (9 : 𝓞 K) ∣ b * cj b - b' * cj b' := by
    have : b * cj b - b' * cj b' = b * (cj b - cj b') + (b - b') * cj b' := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hc _) (dvd_mul_of_dvd_left h _)
  rw [h1, h2] at h3
  have h4 : ((9 : ℤ) : 𝓞 K) ∣ (((absNorm (span {b}) : ℤ) - absNorm (span {b'}) : ℤ) : 𝓞 K) := by
    push_cast; exact_mod_cast h3
  exact Int.emod_eq_zero_of_dvd (int_dvd_of_dvd h4)

/-- **Periodicity of `(ω/b)₃`** modulo `9`. -/
theorem cub_omega_congr {b b' : 𝓞 K} (hb : Primary b) (hb' : Primary b') (h : (9 : 𝓞 K) ∣ b - b') :
    cub ω (span {b}) = cub ω (span {b'}) := by
  rw [cub_omega hb, cub_omega hb', omega_pow_mod, omega_pow_mod ((absNorm (span {b'}) - 1) / 3)]
  congr 1
  have h1 := absNorm_primary_mod hb
  have h2 := absNorm_primary_mod hb'
  have h3 := absNorm_congr_nine h
  omega

/-- Units: `(u/b)₃` depends on `b` only through `(ω/b)₃`. -/
theorem cub_unit_congr (u : (𝓞 K)ˣ) {b b' : 𝓞 K} (hb : Primary b) (hb' : Primary b')
    (h : cub ω (span {b}) = cub ω (span {b'})) : cub (u : 𝓞 K) (span {b}) = cub (u : 𝓞 K) (span {b'}) := by
  have key : ∀ j : ℕ, cub (ω ^ j) (span {b}) = cub (ω ^ j) (span {b'}) := by
    intro j
    induction j with
    | zero => rw [pow_zero, cub_one hb, cub_one hb']
    | succ j ih => rw [pow_succ, cub_mul_left, cub_mul_left, ih, h]
  rcases List.mem_cons.1 (units_mem u) with rfl | hu
  · simpa using key 0
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_neg, Units.val_one, cub_neg hb, cub_neg hb']; simpa using key 0
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [coe_ωu]; simpa using key 1
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_neg, coe_ωu, cub_neg hb, cub_neg hb']; simpa using key 1
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_pow_eq_pow_val, coe_ωu]; exact key 2
  rcases List.mem_cons.1 hu with rfl | hu
  · rw [Units.val_neg, Units.val_pow_eq_pow_val, coe_ωu, cub_neg hb, cub_neg hb']; exact key 2
  simp at hu

theorem isCoprime_δ3 {p : 𝓞 K} (hp : Primary p) : IsCoprime δ3 p := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨δ3 * t, 1, ?_⟩
  have h3 := δ3_sq
  linear_combination t * h3 + ht

theorem cub_δ3_cube {p : 𝓞 K} (hp : Primary p) : cub δ3 (span {p}) ^ 3 = 1 :=
  cub_pow_three hp (isCoprime_δ3 hp)

/-- The reduction for one `p`: with `p − q = 3s`, `s` not divisible by `λ`, and `v·(−s)` primary, the
comparison gives `(δ₃/p)²(v⁻¹/p) = (δ₃/q)²(v⁻¹/q)`. -/
theorem cub_compare_s {p q s : 𝓞 K} (v : (𝓞 K)ˣ) (hp : Primary p) (hq : Primary q)
    (hpq : IsCoprime p q) (hs : p - q = 3 * s) (hv : Primary ((v : 𝓞 K) * -s)) :
    cub δ3 (span {p}) ^ 2 * cub ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) (span {p}) =
      cub δ3 (span {q}) ^ 2 * cub ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) (span {q}) := by
  refine cub_compare hp hq hv hpq ?_
  rw [δ3_sq, hs]
  have : ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination (-(3 : 𝓞 K)) * s * this

/-- The supplement for `λ`, as periodicity, on elements prime to `2`: for primary `p, p'` prime to `2`
with `p ≡ p' (mod 9)`, `(δ₃/p)₃ = (δ₃/p')₃`. -/
theorem cub_δ3_congr_odd {p p' : 𝓞 K} (hp : Primary p) (hp' : Primary p') (h2 : IsCoprime p 2)
    (h2' : IsCoprime p' 2) (h9 : (9 : 𝓞 K) ∣ p - p') :
    cub δ3 (span {p}) = cub δ3 (span {p'}) := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨t', ht'⟩ := hp'
  have hp0 : Primary p := ⟨t, ht⟩
  have hp0' : Primary p' := ⟨t', ht'⟩
  obtain ⟨k, hk⟩ := h9
  have htt : t - t' = 3 * k := by
    have h3 : (3 : 𝓞 K) * (t - t') = 3 * (3 * k) := by linear_combination -ht + ht' + hk
    exact mul_left_cancel₀ (by norm_num) h3
  have hlam3 : (ω - 1 : 𝓞 K) ∣ 3 := lam_dvd_three
  apply eq_of_sq_eq_cube (cub_δ3_cube hp0) (cub_δ3_cube hp0')
  have hω' := cub_omega_congr hp0 hp0' ⟨k, hk⟩
  by_cases hA : (ω - 1 : 𝓞 K) ∣ t
  · -- p ≡ 1 (mod λ³): compare with q = −2
    have hns : ¬ (ω - 1 : 𝓞 K) ∣ -(t + 1) := by
      intro h
      have h1 : (ω - 1 : 𝓞 K) ∣ t + 1 := dvd_neg.1 h
      have h2 : (ω - 1 : 𝓞 K) ∣ 1 := by simpa using dvd_sub h1 hA
      exact lam_not_unit (isUnit_of_dvd_one h2)
    obtain ⟨v, hv⟩ := exists_primary hns
    have hv' : Primary ((v : 𝓞 K) * -(t' + 1)) := by
      obtain ⟨w, hw⟩ := hv
      exact ⟨w + v * k, by linear_combination hw + (v : 𝓞 K) * htt⟩
    have hq2 : IsCoprime p (-2) := by simpa using h2.neg_right
    have hq2' : IsCoprime p' (-2) := by simpa using h2'.neg_right
    have e1 := cub_compare_s v hp0 primary_neg_two hq2 (by linear_combination ht) hv
    have e2 := cub_compare_s v hp0' primary_neg_two hq2' (by linear_combination ht') hv'
    have hu := cub_unit_congr v⁻¹ hp0 hp0' hω'
    have hne : cub ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) (span {p'}) ≠ 0 :=
      cub_ne_zero hp0' ⟨(v : 𝓞 K), 0, by rw [zero_mul, add_zero, Units.mul_inv]⟩
    have := e1.trans e2.symm
    rw [hu] at this
    exact mul_right_cancel₀ hne this
  · -- p ≢ 1 (mod λ³): compare with q = 1
    have hns : ¬ (ω - 1 : 𝓞 K) ∣ -t := fun h => hA (dvd_neg.1 h)
    obtain ⟨v, hv⟩ := exists_primary hns
    have hv' : Primary ((v : 𝓞 K) * -t') := by
      obtain ⟨w, hw⟩ := hv
      exact ⟨w + v * k, by linear_combination hw + (v : 𝓞 K) * htt⟩
    have e1 := cub_compare_s v hp0 primary_one isCoprime_one_right (by linear_combination ht) hv
    have e2 := cub_compare_s v hp0' primary_one isCoprime_one_right (by linear_combination ht') hv'
    have hu := cub_unit_congr v⁻¹ hp0 hp0' hω'
    have hne : cub ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) (span {p'}) ≠ 0 :=
      cub_ne_zero hp0' ⟨(v : 𝓞 K), 0, by rw [zero_mul, add_zero, Units.mul_inv]⟩
    have := e1.trans e2.symm
    rw [hu] at this
    exact mul_right_cancel₀ hne this

/-- The cubic symbol is multiplicative in the denominator. -/
theorem cub_mul_right (a : 𝓞 K) {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
    cub a (I * J) = cub a I * cub a J := by
  simp only [cub, normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

theorem cub_mul_span (a : 𝓞 K) {x y : 𝓞 K} (hx : x ≠ 0) (hy : y ≠ 0) :
    cub a (span {x * y}) = cub a (span {x}) * cub a (span {y}) := by
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact cub_mul_right a (by rwa [Ne, Ideal.zero_eq_bot, span_singleton_eq_bot])
    (by rwa [Ne, Ideal.zero_eq_bot, span_singleton_eq_bot])

/-- `(δ₃/−2)₃ = 1`, since `δ₃ = 1 + 2ω ≡ 1 (mod 2)`. -/
theorem cub_δ3_neg_two : cub δ3 (span {(-2 : 𝓞 K)}) = 1 := by
  rw [cub_congr (y := 1) ⟨-ω, by rw [δ3]; ring⟩, cub_one primary_neg_two]

/-- `(δ₃/7)₃ = 1`: the comparison of `7` with `1`, as `7 − 1 = δ₃²·1·(−2)`. -/
theorem cub_δ3_seven : cub δ3 (span {(7 : 𝓞 K)}) = 1 := by
  have h7 : Primary (7 : 𝓞 K) := ⟨2, by norm_num⟩
  have h := cub_compare (u := 1) h7 primary_one primary_neg_two isCoprime_one_right
    (by rw [δ3_sq]; norm_num)
  simp only [cub_one_right, cub_one h7, one_pow, mul_one] at h
  exact eq_of_sq_eq_cube (cub_δ3_cube h7) (one_pow 3) (by rw [h, one_pow])

theorem prime_O_two : Prime (2 : 𝓞 K) :=
  (Ideal.span_singleton_prime two_ne_zero).1 span_two_isMaximal.isPrime

theorem absNorm_span_two : absNorm (span {(2 : 𝓞 K)}) = 4 := by
  rw [absNorm_eq_card]; exact card_quot_two

/-- Every primary element agrees modulo `9` with a primary element prime to `2` with the same
`(δ₃/·)₃`: divide out `−2`, which has `(δ₃/−2)₃ = 1`, and multiply back by `7 ≡ −2 (mod 9)`, which has
`(δ₃/7)₃ = 1`. -/
theorem exists_odd_rep (N : ℕ) : ∀ p : 𝓞 K, absNorm (span {p}) = N → Primary p →
    ∃ y : 𝓞 K, Primary y ∧ IsCoprime y 2 ∧ (9 : 𝓞 K) ∣ p - y ∧
      cub δ3 (span {p}) = cub δ3 (span {y}) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p hN hp
    by_cases h2 : (2 : 𝓞 K) ∣ p
    · obtain ⟨z, hz⟩ := h2
      obtain ⟨t, ht⟩ := hp
      have hw : p = -2 * -z := by rw [hz]; ring
      have hwp : Primary (-z) := ⟨-z + t, by linear_combination ht - hw⟩
      have hw0 : (-z : 𝓞 K) ≠ 0 := primary_ne_zero hwp
      have hNw : absNorm (span {-z}) < N := by
        have hmul : absNorm (span {p}) = absNorm (span {(-2 : 𝓞 K)}) * absNorm (span {-z}) := by
          rw [hw, ← Ideal.span_singleton_mul_span_singleton, map_mul]
        rw [Ideal.span_singleton_neg, absNorm_span_two] at hmul
        have hpos : absNorm (span {-z}) ≠ 0 := by
          rw [Ne, absNorm_eq_zero_iff, span_singleton_eq_bot]; exact hw0
        omega
      obtain ⟨y, hy, hy2, hy9, hyc⟩ := ih _ hNw (-z) rfl hwp
      have h7 : Primary (7 : 𝓞 K) := ⟨2, by norm_num⟩
      have h72 : IsCoprime (7 : 𝓞 K) 2 := ⟨1, -3, by norm_num⟩
      refine ⟨7 * y, h7.mul hy, h72.mul_left hy2, ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hy9
        exact ⟨7 * k + z, by linear_combination hw + 7 * hk⟩
      · rw [hw, cub_mul_span _ (by norm_num) hw0, cub_δ3_neg_two, one_mul, hyc,
          cub_mul_span _ (by norm_num) (primary_ne_zero hy), cub_δ3_seven, one_mul]
    · exact ⟨p, hp, ((prime_O_two.irreducible.coprime_iff_not_dvd).2 h2).symm, by simp, rfl⟩

/-- **The supplement for `λ`, as periodicity, on every primary element**: `(δ₃/p)₃ = (δ₃/p')₃` for
primary `p ≡ p' (mod 9)`. -/
theorem cub_δ3_congr {p p' : 𝓞 K} (hp : Primary p) (hp' : Primary p') (h9 : (9 : 𝓞 K) ∣ p - p') :
    cub δ3 (span {p}) = cub δ3 (span {p'}) := by
  obtain ⟨y, hy, hy2, hy9, hyc⟩ := exists_odd_rep _ p rfl hp
  obtain ⟨y', hy', hy2', hy9', hyc'⟩ := exists_odd_rep _ p' rfl hp'
  rw [hyc, hyc']
  refine cub_δ3_congr_odd hy hy' hy2 hy2' ?_
  have e : y - y' = -(p - y) + (p - p') + (p' - y') := by ring
  rw [e]
  exact dvd_add (dvd_add (dvd_neg.2 hy9) h9) hy9'

theorem primary_of_nine {x : 𝓞 K} (h9 : (9 : 𝓞 K) ∣ x - 1) : Primary x :=
  dvd_trans ⟨3, by norm_num⟩ h9

/-- **The supplementary factors vanish at `x ≡ 1 (mod 9)`**: `(δ₃/x)₃ = 1`. -/
theorem cub_δ3_of_nine {x : 𝓞 K} (h9 : (9 : 𝓞 K) ∣ x - 1) : cub δ3 (span {x}) = 1 := by
  rw [cub_δ3_congr (primary_of_nine h9) primary_one h9, cub_one_right]

/-- `(u/x)₃ = 1` for every unit `u` at `x ≡ 1 (mod 9)`. -/
theorem cub_unit_of_nine (u : (𝓞 K)ˣ) {x : 𝓞 K} (h9 : (9 : 𝓞 K) ∣ x - 1) :
    cub (u : 𝓞 K) (span {x}) = 1 := by
  have hx := primary_of_nine h9
  rw [cub_unit_congr u hx primary_one (cub_omega_congr hx primary_one h9), cub_one_right]

/-- `χ_P(a)² = σ(χ_P(a))` (sextic squared is cubic) at a maximal `P` with `6 ∉ P`. -/
theorem chiP_sq {P : Ideal (𝓞 K)} [hP : P.IsMaximal] (hP6 : (6 : 𝓞 K) ∉ P) (a : 𝓞 K) :
    chiP P a ^ 2 = σO (chi3 P a) := by
  have hP3 := three_not_mem_of_six P hP6
  unfold chiP
  rw [dite_eq_left ⟨hP, hP6⟩, ← MulChar.pow_apply' _ (by norm_num), chi6_sq P hP6, chi3_eq hP3]
  rfl

/-- **`(a/𝔫)₆² = σ((a/𝔫)₃)`** for an ideal of norm prime to `6`. -/
theorem sym6_sq_eq_cub {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (a : 𝓞 K) :
    sym6 a I ^ 2 = σO (cub a I) := by
  unfold sym6 cub
  rw [← Multiset.prod_map_pow, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  have := isMaximal_of_factor hP
  exact chiP_sq (six_not_mem_of_factor hI hP) a

/-- **Periodicity of `χ_n(δ₃)²`**: for primary `n, n'` of norm prime to `6` with `n ≡ n' (mod 9)`,
`(δ₃/n)₆² = (δ₃/n')₆²`. -/
theorem sym6_sq_δ3_congr {n n' : 𝓞 K} (hn : Primary n) (hn' : Primary n')
    (h6 : (absNorm (span {n})).Coprime 6) (h6' : (absNorm (span {n'})).Coprime 6)
    (h9 : (9 : 𝓞 K) ∣ n - n') : sym6 δ3 (span {n}) ^ 2 = sym6 δ3 (span {n'}) ^ 2 := by
  rw [sym6_sq_eq_cub h6, sym6_sq_eq_cub h6', cub_δ3_congr hn hn' h9]

/-- **Periodicity of `χ_n(ω)²`** modulo `9`. -/
theorem sym6_sq_omega_congr {n n' : 𝓞 K} (hn : Primary n) (hn' : Primary n')
    (h6 : (absNorm (span {n})).Coprime 6) (h6' : (absNorm (span {n'})).Coprime 6)
    (h9 : (9 : 𝓞 K) ∣ n - n') : sym6 ω (span {n}) ^ 2 = sym6 ω (span {n'}) ^ 2 := by
  rw [sym6_sq_eq_cub h6, sym6_sq_eq_cub h6', cub_omega_congr hn hn' h9]

end Eis

end

#print axioms Eis.cub_mul_left
#print axioms Eis.cub_congr
#print axioms Eis.cub_one_right
#print axioms Eis.cub_neg
#print axioms Eis.chi3_cube_of_coprime
#print axioms Eis.cub_pow_three
#print axioms Eis.cub_ne_zero
#print axioms Eis.eq_of_sq_eq_cube
#print axioms Eis.isCoprime_of_sub
#print axioms Eis.cub_compare
#print axioms Eis.chi3_omega
#print axioms Eis.absNorm_mod_three
#print axioms Eis.omega_pow_mod
#print axioms Eis.prod_chi3_omega
#print axioms Eis.nf_spec
#print axioms Eis.absNorm_span_eq_prod
#print axioms Eis.primary_ne_zero
#print axioms Eis.cub_omega
#print axioms Eis.absNorm_primary_mod
#print axioms Eis.cub_one
#print axioms Eis.int_dvd_of_dvd
#print axioms Eis.absNorm_congr_nine
#print axioms Eis.cub_omega_congr
#print axioms Eis.cub_unit_congr
#print axioms Eis.isCoprime_δ3
#print axioms Eis.cub_δ3_cube
#print axioms Eis.cub_compare_s
#print axioms Eis.cub_δ3_congr_odd
#print axioms Eis.cub_mul_right
#print axioms Eis.cub_mul_span
#print axioms Eis.cub_δ3_neg_two
#print axioms Eis.cub_δ3_seven
#print axioms Eis.prime_O_two
#print axioms Eis.absNorm_span_two
#print axioms Eis.exists_odd_rep
#print axioms Eis.cub_δ3_congr
#print axioms Eis.primary_of_nine
#print axioms Eis.cub_δ3_of_nine
#print axioms Eis.cub_unit_of_nine
#print axioms Eis.chiP_sq
#print axioms Eis.sym6_sq_eq_cub
#print axioms Eis.sym6_sq_δ3_congr
#print axioms Eis.sym6_sq_omega_congr
