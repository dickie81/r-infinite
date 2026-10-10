import KubotaCuspData

/-! # Kubota's character (round 382)

S5f-7 of round 360's plan, the first step of its Part II. Dunn and Radziwiłł define Kubota's cubic
character on `Γ_1(3) = {γ ∈ SL_2(ℤ[ω]) : γ ≡ I (mod 3)}` by their (5.4), `χ(γ) = (c/a)₃` for `c ≠ 0` and
`1` otherwise (round 361's `kub`), and write: "`It was shown by Patterson \cite[\S 2]{Pat1} that $\chi$
extends to a well-defined homomorphism`" on `Γ_2 = SL_2(ℤ)Γ_1(3)` "`when one defines
$\chi \lvert_{\operatorname{SL}_2(\mathbb{Z})} \equiv 1$`". This file proves both from cubic reciprocity
(round 290) and the supplementary laws as periodicity modulo `9` (round 362).

* **No case split** (`kub_eq_cub`): `κ(γ) = σ((c/a)₃)` for every `γ` of determinant `1`, since `a` is a
  unit when `c = 0`.
* **The comparison identity** (`cub_sub_comp`): `((p − q)/p)₃ = ((p − q)/q)₃` for coprime primary `p, q`,
  the first step of round 362's `cub_compare`.
* **The column identity** (**`cub_col_mul`**, with `cub_col_mul_of_coprime`, `cub_add_three_mul` and
  `exists_isCoprime_add_mul`): for `ad − bc = 1` and `a′d′ − b′c′ = 1` with `a, a′` primary and
  `3 ∣ b, c, c′`, `((ca′ + dc′)/(aa′ + bc′))₃ = (c/a)₃(c′/a′)₃`. When `a` is prime to `c′`, `a(ca′ + dc′) ≡ c′`
  modulo `A = aa′ + bc′` gives `(a/A)₃(C/A)₃ = (c′/A)₃`; reciprocity gives `(a/A)₃ = (b/a)₃(c′/a)₃`, the
  periodicity modulo `9` and `c′` gives `(c′/A)₃ = (c′/a)₃(c′/a′)₃`, and `(b/a)₃(c/a)₃ = (−1/a)₃ = 1`. The
  general case moves `a` to `a + 3cx`, prime to `c′`, which changes neither side.
* **The homomorphism** (**`kub_mul`**, with `modThree_mul`): `κ(γγ′) = κ(γ)κ(γ′)` on `Γ_1(3)`.
* **Conjugation by `SL_2(ℤ)`** (`cub_bd_eq_ca`, `kub_conj_S_raw`, `kub_conj_T_raw`, **`kub_conj_toSL`**):
  `κ(S⁻¹γS) = κ(γ)` is `(b/d)₃ = (c/a)₃`, Dunn and Radziwiłł's (5.5); `κ(T⁻¹γT) = κ(γ)` is the comparison
  identity at `p = a`, `q = a − c`; Mathlib's `SL2Z_generators` gives every `h ∈ SL_2(ℤ)`.
* **Trivial on `SL_2(ℤ) ∩ Γ_1(3)`** (**`kub_int`**, with `cub_cj`, `eq_one_of_cube_of_cj` and
  `cub_intCast`): `(x̄/ā)₃ = conj((x/a)₃)` from round 290's `chi3_map_cj`, so the symbol of rational integers
  is a cube root of unity fixed by conjugation.
* **The extension** (`Gam3`, `Gam2`, `kub2` and `kubHom`, definitions; **`kub2_mul`**, with `mem_Gam3`,
  `mem_Gam2`, `kub2_eq`, `kub2_toSL` and `kub2_Gam3`): `κ(hγ) = κ(γ)` for `h ∈ SL_2(ℤ)`, `γ ∈ Γ_1(3)` is
  well defined and a homomorphism on `Γ_2`, `1` on `SL_2(ℤ)` and `κ` on `Γ_1(3)`.
* **The cusps** (`mul_inv_mem_Gam3_of_cong`, Dunn and Radziwiłł's (5.3); **`gamPlus_not_mem_Gam2`**,
  `gamMinus_not_mem_Gam2`, `gamPlus_mul_inv_gamMinus_not_mem_Gam2`): `Γ_2`, `Γ_2γ_+` and `Γ_2γ_−` are three
  distinct cosets of `Γ_2\Γ`.
-/

open NumberField Ideal UniqueFactorizationMonoid Complex
open scoped ComplexConjugate MatrixGroups

noncomputable section

namespace Eis

/-- **The comparison identity**: `((p − q)/p)₃ = ((p − q)/q)₃` for coprime primary `p, q`. -/
theorem cub_sub_comp {p q : 𝓞 K} (hp : Primary p) (hq : Primary q) (hpq : IsCoprime p q) :
    cub (p - q) (span {p}) = cub (p - q) (span {q}) := by
  have a1 : cub (p - q) (span {p}) = cub (-q) (span {p}) := cub_congr ⟨1, by ring⟩
  have a2 : cub p (span {q}) = cub (p - q) (span {q}) := cub_congr ⟨1, by ring⟩
  rw [a1, cub_neg hp, cub_recip hq hp hpq.symm, a2]

/-- A primary unit is `1`. -/
theorem primary_eq_one_of_isUnit {a : 𝓞 K} (ha : Primary a) (hu : IsUnit a) : a = 1 :=
  primary_unique ha primary_one (by rw [span_singleton_eq_top.2 hu, span_singleton_one])

theorem cub_isUnit_right (x : 𝓞 K) {u : 𝓞 K} (hu : IsUnit u) : cub x (span {u}) = 1 := by
  rw [span_singleton_eq_top.2 hu, ← span_singleton_one, cub_one_right]

/-- **`κ` without its case split**: `κ(γ) = σ((c/a)₃)` for every `γ` of determinant `1`; at `c = 0`, `a` is
a unit. -/
theorem kub_eq_cub {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hdet : γ.det = 1) :
    kub γ = σO (cub (γ 1 0) (span {γ 0 0})) := by
  by_cases hc : γ 1 0 = 0
  · have hk : kub γ = 1 := by unfold kub; exact ite_eq_left hc
    have hu : IsUnit (γ 0 0) := by
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      exact IsUnit.of_mul_eq_one _ hdet
    rw [hk, cub_isUnit_right _ hu, map_one]
  · exact kub_of_ne hc

/-- **Avoidance**: for coprime `a, b` and `m ≠ 0` there is `x` with `a + bx` prime to `m`. -/
theorem exists_isCoprime_add_mul {a b : 𝓞 K} (hab : IsCoprime a b) {m : 𝓞 K} (hm : m ≠ 0) :
    ∃ x, IsCoprime (a + b * x) m := by
  induction m using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hm
  | h₂ u hu => exact ⟨0, isCoprime_one_right.of_isCoprime_of_dvd_right hu.dvd⟩
  | h₃ m p hm0 hp ih =>
    obtain ⟨x, hx⟩ := ih hm0
    rcases dvd_or_isCoprime p (b * m) hp.irreducible with hpd | hcop
    · refine ⟨x, IsCoprime.mul_right ?_ hx⟩
      rcases hp.dvd_or_dvd hpd with hpb | hpm
      · have hap : IsCoprime a p := hab.of_isCoprime_of_dvd_right hpb
        obtain ⟨k, rfl⟩ := hpb
        have := hap.add_mul_left_left (k * x)
        rwa [← mul_assoc] at this
      · exact hx.of_isCoprime_of_dvd_right hpm
    · obtain ⟨u, v, huv⟩ := hcop
      refine ⟨x + m * v * (1 - (a + b * x)), IsCoprime.mul_right ?_ ?_⟩
      · exact ⟨1, u * (1 - (a + b * x)), by linear_combination (1 - (a + b * x)) * huv⟩
      · have := hx.add_mul_left_left (b * v * (1 - (a + b * x)))
        convert this using 1; ring

/-- `(c/a)₃` is unchanged by `a ↦ a + 3cx`, for `a` primary and prime to `c`, `3 ∣ c`. -/
theorem cub_add_three_mul {a c : 𝓞 K} (ha : Primary a) (hac : IsCoprime a c) (hc : (3 : 𝓞 K) ∣ c)
    (x : 𝓞 K) : cub c (span {a + 3 * c * x}) = cub c (span {a}) := by
  by_cases hc0 : c = 0
  · rw [hc0]; simp
  have hA : Primary (a + 3 * c * x) := by
    obtain ⟨t, ht⟩ := ha
    exact ⟨t + c * x, by linear_combination ht⟩
  have hAc : IsCoprime (a + 3 * c * x) c := by
    have := hac.add_mul_left_left (3 * x)
    convert this using 2; ring
  obtain ⟨k, hk⟩ := hc
  exact cub_left_congr hc0 hA ha hAc hac ⟨k * x, by rw [hk]; ring⟩ ⟨3 * x, by ring⟩

/-- **The column identity, coprime case**: for `ad − bc = 1` with `a` primary and `3 ∣ b`, and a
column `(a′, c′)` with `a′` primary, `3 ∣ c′ ≠ 0` and `a′, c′` coprime, if `a` is prime to `c′`, then
`((ca′ + dc′)/(aa′ + bc′))₃ = (c/a)₃(c′/a′)₃`. -/
theorem cub_col_mul_of_coprime {a b c d a' c' : 𝓞 K} (hdet : a * d - b * c = 1) (ha : Primary a)
    (hb : (3 : 𝓞 K) ∣ b) (ha' : Primary a') (hc' : (3 : 𝓞 K) ∣ c') (hc'0 : c' ≠ 0)
    (hac' : IsCoprime a' c') (hcop : IsCoprime a c') :
    cub (c * a' + d * c') (span {a * a' + b * c'}) = cub c (span {a}) * cub c' (span {a'}) := by
  set A := a * a' + b * c' with hAdef
  set C := c * a' + d * c' with hCdef
  have hA : Primary A := by
    obtain ⟨t, ht⟩ := ha
    obtain ⟨t', ht'⟩ := ha'
    obtain ⟨k, hk⟩ := hb
    exact ⟨t * a' + t' + k * c', by rw [hAdef]; linear_combination a' * ht + ht' + c' * hk⟩
  have hab : IsCoprime a b := ⟨d, -c, by linear_combination hdet⟩
  have haA : IsCoprime a A := by
    have := (hab.mul_right hcop).add_mul_left_right a'
    convert this using 1; rw [hAdef]; ring
  have hAc' : IsCoprime A c' := by
    have := (hcop.mul_left hac').add_mul_right_left b
    convert this using 1
  have h1 : cub a (span {A}) * cub C (span {A}) = cub c' (span {A}) := by
    rw [← cub_mul_left]; exact cub_congr ⟨c, by rw [hAdef, hCdef]; linear_combination c' * hdet⟩
  have h2 : cub a (span {A}) = cub b (span {a}) * cub c' (span {a}) := by
    rw [cub_recip ha hA haA, ← cub_mul_left]
    exact cub_congr ⟨a', by rw [hAdef]; ring⟩
  have h3 : cub c' (span {A}) = cub c' (span {a}) * cub c' (span {a'}) := by
    have h9 : (9 : 𝓞 K) ∣ A - a * a' := by
      obtain ⟨k, hk⟩ := hb
      obtain ⟨k', hk'⟩ := hc'
      exact ⟨k * k', by rw [hAdef, hk, hk']; ring⟩
    rw [cub_left_congr hc'0 hA (ha.mul ha') hAc' (hcop.mul_left hac') h9
      ⟨b, by rw [hAdef]; ring⟩, cub_mul_span c' (primary_ne_zero ha) (primary_ne_zero ha')]
  have h4 : cub b (span {a}) * cub c (span {a}) = 1 := by
    rw [← cub_mul_left, cub_congr (show a ∣ b * c - (-1) from ⟨d, by linear_combination -hdet⟩),
      cub_neg ha, cub_one ha]
  have hX : cub c' (span {a}) ≠ 0 := cub_ne_zero ha hcop.symm
  have hBW : cub b (span {a}) * cub C (span {A}) = cub c' (span {a'}) := by
    apply mul_left_cancel₀ hX
    rw [← h3, ← h1, h2]; ring
  calc cub C (span {A}) = cub C (span {A}) * (cub b (span {a}) * cub c (span {a})) := by
        rw [h4, mul_one]
    _ = (cub b (span {a}) * cub C (span {A})) * cub c (span {a}) := by ring
    _ = cub c (span {a}) * cub c' (span {a'}) := by rw [hBW, mul_comm]

/-- `γ ≡ I (mod 3)`, entrywise. -/
theorem modThree_iff {a b c d : 𝓞 K} :
    ModThree !![a, b; c, d] ↔ Primary a ∧ (3 : 𝓞 K) ∣ b ∧ (3 : 𝓞 K) ∣ c ∧ Primary d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Primary] using h 0 0
    · simpa using h 0 1
    · simpa using h 1 0
    · simpa [Primary] using h 1 1
  · rintro ⟨ha, hb, hc, hd⟩ i j
    fin_cases i <;> fin_cases j
    · simpa [Primary] using ha
    · simpa using hb
    · simpa using hc
    · simpa [Primary] using hd

theorem exists_fin_two_eq (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) : ∃ a b c d, γ = !![a, b; c, d] :=
  ⟨_, _, _, _, Matrix.eta_fin_two γ⟩

/-- **The column identity**: for `ad − bc = 1` with `a` primary and `3 ∣ b, c`, and `a′d′ − b′c′ = 1`
with `a′` primary and `3 ∣ c′`, `((ca′ + dc′)/(aa′ + bc′))₃ = (c/a)₃(c′/a′)₃`. -/
theorem cub_col_mul {a b c d a' b' c' d' : 𝓞 K} (hdet : a * d - b * c = 1) (ha : Primary a)
    (hb : (3 : 𝓞 K) ∣ b) (hc : (3 : 𝓞 K) ∣ c) (hdet' : a' * d' - b' * c' = 1) (ha' : Primary a')
    (hc' : (3 : 𝓞 K) ∣ c') :
    cub (c * a' + d * c') (span {a * a' + b * c'}) = cub c (span {a}) * cub c' (span {a'}) := by
  by_cases hc'0 : c' = 0
  · subst hc'0
    have hu : IsUnit a' := IsUnit.of_mul_eq_one d' (by linear_combination hdet')
    obtain rfl := primary_eq_one_of_isUnit ha' hu
    simp only [mul_one, mul_zero, add_zero]
    rw [cub_isUnit_right _ isUnit_one, mul_one]
  have hac : IsCoprime a c := ⟨d, -b, by linear_combination hdet⟩
  have h3c : IsCoprime a (3 * c) := (isCoprime_three_of_primary ha).symm.mul_right hac
  obtain ⟨x, hx⟩ := exists_isCoprime_add_mul h3c hc'0
  have hac' : IsCoprime a' c' := ⟨d', -b', by linear_combination hdet'⟩
  have hdet1 : (a + 3 * c * x) * d - (b + 3 * d * x) * c = 1 := by linear_combination hdet
  have ha1 : Primary (a + 3 * c * x) := by
    obtain ⟨t, ht⟩ := ha
    exact ⟨t + c * x, by linear_combination ht⟩
  have hb1 : (3 : 𝓞 K) ∣ b + 3 * d * x := dvd_add hb ⟨d * x, by ring⟩
  have key := cub_col_mul_of_coprime hdet1 ha1 hb1 ha' hc' hc'0 hac' hx
  have hA : Primary (a * a' + b * c') := by
    obtain ⟨t, ht⟩ := ha
    obtain ⟨t', ht'⟩ := ha'
    obtain ⟨k, hk⟩ := hb
    exact ⟨t * a' + t' + k * c', by linear_combination a' * ht + ht' + c' * hk⟩
  have hAC : IsCoprime (a * a' + b * c') (c * a' + d * c') :=
    ⟨c * b' + d * d', -(a * b' + b * d'), by linear_combination (a' * d' - b' * c') * hdet + hdet'⟩
  have hC : (3 : 𝓞 K) ∣ c * a' + d * c' :=
    dvd_add (dvd_mul_of_dvd_left hc _) (dvd_mul_of_dvd_right hc' _)
  have e : (a + 3 * c * x) * a' + (b + 3 * d * x) * c' =
      (a * a' + b * c') + 3 * (c * a' + d * c') * x := by ring
  rw [e, cub_add_three_mul hA hAC hC, cub_add_three_mul ha hac hc] at key
  exact key

theorem det_mul_eq_one {γ γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : γ.det = 1) (h' : γ'.det = 1) :
    (γ * γ').det = 1 := by rw [Matrix.det_mul, h, h', mul_one]

theorem modThree_mul {γ γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)} (h : ModThree γ) (h' : ModThree γ') :
    ModThree (γ * γ') := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_fin_two_eq γ
  obtain ⟨a', b', c', d', rfl⟩ := exists_fin_two_eq γ'
  rw [modThree_iff] at h h'
  obtain ⟨⟨t, ht⟩, ⟨k, hk⟩, ⟨l, hl⟩, ⟨s, hs⟩⟩ := h
  obtain ⟨⟨t', ht'⟩, ⟨k', hk'⟩, ⟨l', hl'⟩, ⟨s', hs'⟩⟩ := h'
  rw [Matrix.mul_fin_two, modThree_iff]
  refine ⟨⟨t * a' + t' + k * c', ?_⟩, ⟨a * k' + k * d', ?_⟩, ⟨l * a' + d * l', ?_⟩,
    ⟨l * b' + s * d' + s', ?_⟩⟩
  · linear_combination a' * ht + ht' + c' * hk
  · linear_combination a * hk' + d' * hk
  · linear_combination a' * hl + d * hl'
  · linear_combination b' * hl + d' * hs + hs'

/-- **Kubota's character is a homomorphism on `Γ_1(3)`**: `κ(γγ′) = κ(γ)κ(γ′)` for round 361's `kub`,
Dunn and Radziwiłł's (5.4). -/
theorem kub_mul {γ γ' : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hdet : γ.det = 1) (h3 : ModThree γ)
    (hdet' : γ'.det = 1) (h3' : ModThree γ') : kub (γ * γ') = kub γ * kub γ' := by
  rw [kub_eq_cub (det_mul_eq_one hdet hdet'), kub_eq_cub hdet, kub_eq_cub hdet', ← map_mul]
  obtain ⟨a, b, c, d, rfl⟩ := exists_fin_two_eq γ
  obtain ⟨a', b', c', d', rfl⟩ := exists_fin_two_eq γ'
  rw [modThree_iff] at h3 h3'
  rw [Matrix.det_fin_two_of] at hdet hdet'
  congr 1
  simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  exact cub_col_mul hdet h3.1 h3.2.1 h3.2.2.1 hdet' h3'.1 h3'.2.2.1

/-- **`(b/d)₃ = (c/a)₃`** for `ad − bc = 1`, `≡ I (mod 3)` (Dunn and Radziwiłł's (5.5)):
`(c/a)₃(c/d)₃ = (c/ad)₃ = (c/(1 + bc))₃ = 1` and `(b/d)₃(c/d)₃ = (−1/d)₃ = 1`. -/
theorem cub_bd_eq_ca {a b c d : 𝓞 K} (hdet : a * d - b * c = 1) (ha : Primary a) (hb : (3 : 𝓞 K) ∣ b)
    (hc : (3 : 𝓞 K) ∣ c) (hd : Primary d) : cub b (span {d}) = cub c (span {a}) := by
  by_cases hc0 : c = 0
  · subst hc0
    have hu : IsUnit d := IsUnit.of_mul_eq_one a (by linear_combination hdet)
    have hu' : IsUnit a := IsUnit.of_mul_eq_one d (by linear_combination hdet)
    rw [cub_isUnit_right _ hu, cub_isUnit_right _ hu']
  have ha0 := primary_ne_zero ha
  have hd0 := primary_ne_zero hd
  have hcd : IsCoprime c d := ⟨-b, a, by linear_combination hdet⟩
  have h1 : cub c (span {a}) * cub c (span {d}) = 1 := by
    rw [← cub_mul_span c ha0 hd0]
    have hadc : IsCoprime (a * d) c := ⟨1, -b, by linear_combination hdet⟩
    obtain ⟨k, hk⟩ := hb
    obtain ⟨l, hl⟩ := hc
    rw [cub_left_congr hc0 (ha.mul hd) primary_one hadc isCoprime_one_left
      ⟨k * l, by linear_combination hdet + c * hk + 3 * k * hl⟩
      ⟨b, by linear_combination hdet⟩, cub_one_right]
  have h2 : cub b (span {d}) * cub c (span {d}) = 1 := by
    rw [← cub_mul_left, cub_congr (show d ∣ b * c - (-1) from ⟨a, by linear_combination -hdet⟩),
      cub_neg hd, cub_one hd]
  have hX : cub c (span {d}) ≠ 0 := cub_ne_zero hd hcd
  apply mul_right_cancel₀ hX
  rw [h1, h2]

/-- **Invariance under conjugation by `S`**: `κ(S⁻¹γS) = κ(γ)` on `Γ_1(3)`. -/
theorem kub_conj_S_raw {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hdet : γ.det = 1) (h3 : ModThree γ) :
    kub (!![0, 1; -1, 0] * γ * !![0, -1; 1, 0]) = kub γ := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_fin_two_eq γ
  rw [modThree_iff] at h3
  rw [Matrix.det_fin_two_of] at hdet
  have hp : (!![0, 1; -1, 0] * !![a, b; c, d] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      !![d, -c; -b, a] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hp, kub_eq_cub (by rw [Matrix.det_fin_two_of]; linear_combination hdet),
    kub_eq_cub (by rw [Matrix.det_fin_two_of]; exact hdet)]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [cub_neg h3.2.2.2, cub_bd_eq_ca hdet h3.1 h3.2.1 h3.2.2.1 h3.2.2.2]

/-- **Invariance under conjugation by `T`**: `κ(T⁻¹γT) = κ(γ)` on `Γ_1(3)`, from the comparison
identity `((p − q)/p)₃ = ((p − q)/q)₃` at `p = a`, `q = a − c`. -/
theorem kub_conj_T_raw {γ : Matrix (Fin 2) (Fin 2) (𝓞 K)} (hdet : γ.det = 1) (h3 : ModThree γ) :
    kub (!![1, -1; 0, 1] * γ * !![1, 1; 0, 1]) = kub γ := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_fin_two_eq γ
  rw [modThree_iff] at h3
  rw [Matrix.det_fin_two_of] at hdet
  have hp : (!![1, -1; 0, 1] * !![a, b; c, d] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      !![a - c, a - c + (b - d); c, c + d] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hp, kub_eq_cub (by rw [Matrix.det_fin_two_of]; linear_combination hdet),
    kub_eq_cub (by rw [Matrix.det_fin_two_of]; exact hdet)]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have hac : IsCoprime a c := ⟨d, -b, by linear_combination hdet⟩
  have hq : Primary (a - c) := by
    obtain ⟨t, ht⟩ := h3.1
    obtain ⟨l, hl⟩ := h3.2.2.1
    exact ⟨t - l, by linear_combination ht - hl⟩
  have hcop : IsCoprime a (a - c) := by
    have := hac.neg_right.add_mul_left_right 1
    convert this using 1; ring
  have := cub_sub_comp h3.1 hq hcop
  rw [sub_sub_cancel] at this
  rw [this]

/-- **Conjugation equivariance of the cubic symbol**: `(x̄/ā)₃ = conj((x/a)₃)` for `a` prime to `3`. -/
theorem cub_cj (x : 𝓞 K) {a : 𝓞 K} (ha : IsCoprime a 3) :
    cub (cj x) (span {cj a}) = cj (cub x (span {a})) := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    exact absurd (isCoprime_zero_left.1 ha) fun h => lam_not_unit (isUnit_of_dvd_unit lam_dvd_three h)
  | h₂ u hu => rw [cub_isUnit_right _ hu, cub_isUnit_right _ (hu.map cj), map_one]
  | h₃ a p ha0 hp ih =>
    have hp3 : IsCoprime p 3 := ha.of_mul_left_left
    have ha3 : IsCoprime a 3 := ha.of_mul_left_right
    have hp0 := hp.ne_zero
    have hcp0 : cj p ≠ 0 := fun h => hp0 (cj.injective (by rw [h, map_zero]))
    have hca0 : cj a ≠ 0 := fun h => ha0 (cj.injective (by rw [h, map_zero]))
    rw [map_mul, cub_mul_span _ hcp0 hca0, cub_mul_span _ hp0 ha0, map_mul, ih ha3]
    congr 1
    have : (span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have h3 : (3 : 𝓞 K) ∉ span {p} := fun h =>
      hp.not_isUnit (hp3.isUnit_of_dvd' dvd_rfl (mem_span_singleton.1 h))
    rw [← map_cj_span, cub_prime, cub_prime, chi3_map_cj h3]

/-- A cube root of unity fixed by conjugation is `1`. -/
theorem eq_one_of_cube_of_cj {x : 𝓞 K} (h3 : x ^ 3 = 1) (hc : cj x = x) : x = 1 := by
  have hu : IsUnit x := IsUnit.of_mul_eq_one (x ^ 2) (by rw [← pow_succ']; exact h3)
  have hω1 : (ω : 𝓞 K) ≠ 1 := by
    intro h
    have := ω_sq_add
    rw [h] at this
    norm_num at this
  have hωω : (ω : 𝓞 K) ^ 2 ≠ ω := by
    intro h
    apply hω1
    have h0 : (ω : 𝓞 K) ≠ 0 := fun h0 => by have := ω_cube; rw [h0] at this; norm_num at this
    have : ω * (ω - 1) = (0 : 𝓞 K) := by linear_combination h
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0))
  rcases cube_root_cases (u := hu.unit) (Units.ext (by simpa using h3)) with h | h | h
  · simpa using congrArg Units.val h
  · have e : x = ω := by simpa [coe_ωu] using congrArg Units.val h
    rw [e, cj_ω] at hc
    exact absurd hc hωω
  · have e : x = ω ^ 2 := by simpa [coe_ωu] using congrArg Units.val h
    rw [e, map_pow, cj_ω] at hc
    exfalso; apply hωω
    calc (ω : 𝓞 K) ^ 2 = (ω ^ 2) ^ 2 := hc.symm
      _ = ω ^ 3 * ω := by ring
      _ = ω := by rw [ω_cube, one_mul]

/-- **Rational integers**: `(m/n)₃ = 1` for coprime rational integers with `n ≡ 1 (mod 3)`. -/
theorem cub_intCast {m n : ℤ} (hn : Primary (n : 𝓞 K)) (hmn : IsCoprime (m : 𝓞 K) (n : 𝓞 K)) :
    cub (m : 𝓞 K) (span {(n : 𝓞 K)}) = 1 := by
  have h := cub_cj (m : 𝓞 K) (isCoprime_three_of_primary hn).symm
  rw [map_intCast, map_intCast] at h
  exact eq_one_of_cube_of_cj (cub_pow_three hn hmn) h.symm

/-- **`κ` is trivial on `SL_2(ℤ) ∩ Γ_1(3)`**. -/
theorem kub_int {h : Matrix (Fin 2) (Fin 2) ℤ} (hdet : h.det = 1)
    (h3 : ModThree (h.map (Int.castRingHom (𝓞 K)))) : kub (h.map (Int.castRingHom (𝓞 K))) = 1 := by
  have hd : (h.map (Int.castRingHom (𝓞 K))).det = 1 := by
    have := RingHom.map_det (Int.castRingHom (𝓞 K)) h
    rw [hdet, map_one] at this
    exact this.symm
  rw [kub_eq_cub hd]
  simp only [Matrix.map_apply, eq_intCast]
  have h00 : Primary ((h 0 0 : ℤ) : 𝓞 K) := by simpa [Primary] using h3 0 0
  have hdet' : (h 0 0 : 𝓞 K) * (h 1 1 : 𝓞 K) - (h 0 1 : 𝓞 K) * (h 1 0 : 𝓞 K) = 1 := by
    rw [Matrix.det_fin_two] at hdet; exact_mod_cast hdet
  rw [cub_intCast h00 ⟨-(h 0 1 : 𝓞 K), h 1 1, by linear_combination hdet'⟩, map_one]

/-- **`Γ_1(3)`**: the kernel of reduction modulo `3` on `SL_2(𝓞)`. -/
def Gam3 : Subgroup SL(2, 𝓞 K) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (span {(3 : 𝓞 K)}))).ker

instance gam3_normal : Gam3.Normal := MonoidHom.normal_ker _

theorem mem_Gam3 {γ : SL(2, 𝓞 K)} : γ ∈ Gam3 ↔ ModThree (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) := by
  rw [Gam3, MonoidHom.mem_ker, Matrix.SpecialLinearGroup.ext_iff]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one, ModThree]
  refine forall₂_congr fun i j => ?_
  have key : (1 : Matrix (Fin 2) (Fin 2) (𝓞 K ⧸ span {(3 : 𝓞 K)})) i j =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j) := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [key, Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- The inclusion `SL_2(ℤ) → SL_2(𝓞)`. -/
def toSL : SL(2, ℤ) →* SL(2, 𝓞 K) := Matrix.SpecialLinearGroup.map (Int.castRingHom (𝓞 K))

theorem coe_toSL (h : SL(2, ℤ)) :
    (toSL h : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      (h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (𝓞 K)) :=
  Matrix.SpecialLinearGroup.map_apply_coe _ _

theorem kub_mul_Gam3 {γ γ' : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) (hγ' : γ' ∈ Gam3) :
    kub ↑(γ * γ') = kub ↑γ * kub ↑γ' := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact kub_mul γ.2 (mem_Gam3.1 hγ) γ'.2 (mem_Gam3.1 hγ')

theorem kub_toSL {h : SL(2, ℤ)} (hh : toSL h ∈ Gam3) : kub ↑(toSL h) = 1 := by
  have h3 := mem_Gam3.1 hh
  rw [coe_toSL] at h3 ⊢
  exact kub_int h.2 h3

theorem kub_one : kub (1 : Matrix (Fin 2) (Fin 2) (𝓞 K)) = 1 := by
  unfold kub; exact ite_eq_left (by simp)

theorem conj_mem_Gam3 {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) (g : SL(2, 𝓞 K)) : g⁻¹ * γ * g ∈ Gam3 := by
  have := gam3_normal.conj_mem γ hγ g⁻¹
  rwa [inv_inv] at this

theorem coe_toSL_S : (toSL ModularGroup.S : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![0, -1; 1, 0] := by
  rw [coe_toSL, ModularGroup.coe_S]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem coe_toSL_T : (toSL ModularGroup.T : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, 1; 0, 1] := by
  rw [coe_toSL, ModularGroup.coe_T]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **`κ` is invariant under conjugation by `SL_2(ℤ)`**, the invariance behind Patterson's extension
(his §2, as Dunn and Radziwiłł cite it): `κ(h⁻¹γh) = κ(γ)` for `h ∈ SL_2(ℤ)` and `γ ∈ Γ_1(3)`, from the
generators `S`, `T` of `SL_2(ℤ)`. -/
theorem kub_conj_toSL (h : SL(2, ℤ)) {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) :
    kub ↑((toSL h)⁻¹ * γ * toSL h) = kub ↑γ := by
  have hall : h ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top h
  induction hall using Subgroup.closure_induction generalizing γ with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, coe_toSL_S, Matrix.adjugate_fin_two_of, neg_neg]
      exact kub_conj_S_raw γ.2 (mem_Gam3.1 hγ)
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, coe_toSL_T, Matrix.adjugate_fin_two_of, neg_zero]
      exact kub_conj_T_raw γ.2 (mem_Gam3.1 hγ)
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : (toSL (x * y))⁻¹ * γ * toSL (x * y) =
        (toSL y)⁻¹ * ((toSL x)⁻¹ * γ * toSL x) * toSL y := by
      rw [map_mul]; group
    rw [e, ihy (conj_mem_Gam3 hγ _), ihx hγ]
  | inv x hx ih =>
    have hγ' : toSL x * γ * (toSL x)⁻¹ ∈ Gam3 := by
      have := conj_mem_Gam3 hγ (toSL x)⁻¹
      rwa [inv_inv] at this
    have := ih hγ'
    rw [show (toSL x)⁻¹ * (toSL x * γ * (toSL x)⁻¹) * toSL x = γ by group] at this
    rw [map_inv, inv_inv]
    exact this.symm

/-- **`Γ_2 = SL_2(ℤ)Γ_1(3)`** (Dunn and Radziwiłł's (5.2)), as the subgroup generated by both. -/
def Gam2 : Subgroup SL(2, 𝓞 K) := toSL.range ⊔ Gam3

theorem mem_Gam2 {g : SL(2, 𝓞 K)} : g ∈ Gam2 ↔ ∃ h : SL(2, ℤ), (toSL h)⁻¹ * g ∈ Gam3 := by
  rw [← SetLike.mem_coe, Gam2, Subgroup.mul_normal, Set.mem_mul]
  constructor
  · rintro ⟨x, ⟨h, rfl⟩, y, hy, rfl⟩
    exact ⟨h, by rwa [inv_mul_cancel_left]⟩
  · rintro ⟨h, hh⟩
    exact ⟨toSL h, ⟨h, rfl⟩, _, hh, mul_inv_cancel_left _ _⟩

open Classical in
/-- **Kubota's character on `Γ_2`** (Patterson's extension): `κ(hγ) = κ(γ)` for `h ∈ SL_2(ℤ)` and
`γ ∈ Γ_1(3)`; `1` off `Γ_2`. -/
def kub2 (g : SL(2, 𝓞 K)) : ℂ :=
  if hg : ∃ h : SL(2, ℤ), (toSL h)⁻¹ * g ∈ Gam3 then kub ↑((toSL hg.choose)⁻¹ * g) else 1

/-- The extension is well defined: any decomposition `g = hγ` gives `κ(γ)`. -/
theorem kub2_eq {g : SL(2, 𝓞 K)} (h : SL(2, ℤ)) (hh : (toSL h)⁻¹ * g ∈ Gam3) :
    kub2 g = kub ↑((toSL h)⁻¹ * g) := by
  have hg : ∃ h : SL(2, ℤ), (toSL h)⁻¹ * g ∈ Gam3 := ⟨h, hh⟩
  rw [kub2, dite_eq_left hg]
  have hh' := hg.choose_spec
  set h' := hg.choose
  have hm : toSL (h⁻¹ * h') ∈ Gam3 := by
    have e : toSL (h⁻¹ * h') = ((toSL h)⁻¹ * g) * ((toSL h')⁻¹ * g)⁻¹ := by
      rw [map_mul, map_inv]; group
    rw [e]; exact mul_mem hh (inv_mem hh')
  have e : (toSL h)⁻¹ * g = toSL (h⁻¹ * h') * ((toSL h')⁻¹ * g) := by rw [map_mul, map_inv]; group
  rw [e, kub_mul_Gam3 hm hh', kub_toSL hm, one_mul]

/-- **`κ` is a homomorphism on `Γ_2`**. -/
theorem kub2_mul {g g' : SL(2, 𝓞 K)} (hg : g ∈ Gam2) (hg' : g' ∈ Gam2) :
    kub2 (g * g') = kub2 g * kub2 g' := by
  obtain ⟨h, hh⟩ := mem_Gam2.1 hg
  obtain ⟨h', hh'⟩ := mem_Gam2.1 hg'
  have hc : (toSL h')⁻¹ * ((toSL h)⁻¹ * g) * toSL h' ∈ Gam3 := conj_mem_Gam3 hh _
  have e : (toSL (h * h'))⁻¹ * (g * g') =
      (toSL h')⁻¹ * ((toSL h)⁻¹ * g) * toSL h' * ((toSL h')⁻¹ * g') := by
    rw [map_mul]; group
  rw [kub2_eq (h * h') (by rw [e]; exact mul_mem hc hh'), kub2_eq h hh, kub2_eq h' hh', e,
    kub_mul_Gam3 hc hh', kub_conj_toSL h' hh]

theorem kub2_toSL (h : SL(2, ℤ)) : kub2 (toSL h) = 1 := by
  rw [kub2_eq h (by rw [inv_mul_cancel]; exact one_mem _), inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, kub_one]

theorem kub2_Gam3 {γ : SL(2, 𝓞 K)} (hγ : γ ∈ Gam3) : kub2 γ = kub ↑γ := by
  rw [kub2_eq 1 (by rwa [map_one, inv_one, one_mul]), map_one, inv_one, one_mul]

/-- **Kubota's character as a homomorphism `Γ_2 → ℂ`**. -/
def kubHom : Gam2 →* ℂ where
  toFun g := kub2 g
  map_one' := by
    show kub2 1 = 1
    rw [← map_one toSL]; exact kub2_toSL 1
  map_mul' g g' := kub2_mul g.2 g'.2

/-- **Dunn and Radziwiłł's (5.3)**: `g ≡ g′ (mod 3)` gives `g′g⁻¹ ∈ Γ_1(3) ⊆ Γ_2`, so `Γ_2g = Γ_2g′`. -/
theorem mul_inv_mem_Gam3_of_cong {g g' : SL(2, 𝓞 K)}
    (h : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (span {(3 : 𝓞 K)})) g =
      Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (span {(3 : 𝓞 K)})) g') :
    g' * g⁻¹ ∈ Gam3 := by
  rw [Gam3, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

theorem Gam3_le_Gam2 : Gam3 ≤ Gam2 := le_sup_right

/-- `3 ∣ m + nω` forces `3 ∣ n`. -/
theorem three_dvd_of_dvd_coords {m n : ℤ} (h : (3 : 𝓞 K) ∣ (m : 𝓞 K) + n * ω) : (3 : ℤ) ∣ n := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨x, y, rfl⟩ := exists_coords z
  have e : crd ![m, n] = crd ![3 * x, 3 * y] := by
    simp only [crd, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast; rw [hz]; ring
  have := congrFun (crd_injective e) 1
  simp only [Matrix.cons_val_one] at this
  exact ⟨y, this⟩

/-- An element of `Γ_2` has its lower-left entry congruent to a rational integer modulo `3`. -/
theorem exists_int_of_mem_Gam2 {g : SL(2, 𝓞 K)} (hg : g ∈ Gam2) :
    ∃ n : ℤ, (3 : 𝓞 K) ∣ (g : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 - n := by
  obtain ⟨h, hh⟩ := mem_Gam2.1 hg
  have e : g = toSL h * ((toSL h)⁻¹ * g) := by group
  have h3 := mem_Gam3.1 hh
  set γ := (toSL h)⁻¹ * g
  refine ⟨(h : Matrix (Fin 2) (Fin 2) ℤ) 1 0, ?_⟩
  rw [e, Matrix.SpecialLinearGroup.coe_mul, coe_toSL]
  obtain ⟨a, b, c, d, hγ⟩ := exists_fin_two_eq (γ : Matrix (Fin 2) (Fin 2) (𝓞 K))
  rw [hγ] at h3 ⊢
  rw [modThree_iff] at h3
  obtain ⟨⟨t, ht⟩, -, ⟨l, hl⟩, -⟩ := h3
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, eq_intCast, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  exact ⟨(h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * t + (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * l, by
    linear_combination ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : 𝓞 K) * ht +
      ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : 𝓞 K) * hl⟩

/-- The cusp representative `γ_+` as an element of `SL_2(𝓞)`. -/
def gamPlusSL : SL(2, 𝓞 K) := ⟨gamPlus, by simp [gamPlus, Matrix.det_fin_two_of]⟩
/-- The cusp representative `γ_−` as an element of `SL_2(𝓞)`. -/
def gamMinusSL : SL(2, 𝓞 K) := ⟨gamMinus, by simp [gamMinus, Matrix.det_fin_two_of]⟩

theorem not_mem_Gam2_of_entry {g : SL(2, 𝓞 K)} {m k : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 = (m : 𝓞 K) + k * ω) (hk : ¬ (3 : ℤ) ∣ k) :
    g ∉ Gam2 := by
  intro hmem
  obtain ⟨n, hn⟩ := exists_int_of_mem_Gam2 hmem
  rw [hg] at hn
  apply hk
  apply three_dvd_of_dvd_coords (m := m - n)
  convert hn using 1; push_cast; ring

/-- **The three cusps of the display lie in distinct cosets of `Γ_2\Γ`**: `γ_+`, `γ_−` and `γ_+γ_−⁻¹`
are not in `Γ_2`, so `Γ_2`, `Γ_2γ_+` and `Γ_2γ_−` are distinct. -/
theorem gamPlus_not_mem_Gam2 : gamPlusSL ∉ Gam2 :=
  not_mem_Gam2_of_entry (m := 0) (k := 1) (by simp [gamPlusSL, gamPlus]) (by norm_num)

theorem gamMinus_not_mem_Gam2 : gamMinusSL ∉ Gam2 :=
  not_mem_Gam2_of_entry (m := -1) (k := -1)
    (by simp [gamMinusSL, gamMinus]; linear_combination ω_sq_add) (by norm_num)

theorem gamPlus_mul_inv_gamMinus_not_mem_Gam2 : gamPlusSL * gamMinusSL⁻¹ ∉ Gam2 := by
  refine not_mem_Gam2_of_entry (m := 1) (k := 2) ?_ (by norm_num)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  simp [gamPlusSL, gamMinusSL, gamPlus, gamMinus, Matrix.adjugate_fin_two_of, Matrix.mul_apply,
    Fin.sum_univ_two]
  linear_combination (-1 : 𝓞 K) * ω_sq_add

end Eis

#print axioms Eis.cub_sub_comp
#print axioms Eis.primary_eq_one_of_isUnit
#print axioms Eis.cub_isUnit_right
#print axioms Eis.kub_eq_cub
#print axioms Eis.exists_isCoprime_add_mul
#print axioms Eis.cub_add_three_mul
#print axioms Eis.cub_col_mul_of_coprime
#print axioms Eis.modThree_iff
#print axioms Eis.exists_fin_two_eq
#print axioms Eis.cub_col_mul
#print axioms Eis.det_mul_eq_one
#print axioms Eis.modThree_mul
#print axioms Eis.kub_mul
#print axioms Eis.cub_bd_eq_ca
#print axioms Eis.kub_conj_S_raw
#print axioms Eis.kub_conj_T_raw
#print axioms Eis.cub_cj
#print axioms Eis.eq_one_of_cube_of_cj
#print axioms Eis.cub_intCast
#print axioms Eis.kub_int
#print axioms Eis.mem_Gam3
#print axioms Eis.coe_toSL
#print axioms Eis.kub_mul_Gam3
#print axioms Eis.kub_toSL
#print axioms Eis.kub_one
#print axioms Eis.conj_mem_Gam3
#print axioms Eis.coe_toSL_S
#print axioms Eis.coe_toSL_T
#print axioms Eis.kub_conj_toSL
#print axioms Eis.mem_Gam2
#print axioms Eis.kub2_eq
#print axioms Eis.kub2_mul
#print axioms Eis.kub2_toSL
#print axioms Eis.kub2_Gam3
#print axioms Eis.mul_inv_mem_Gam3_of_cong
#print axioms Eis.Gam3_le_Gam2
#print axioms Eis.three_dvd_of_dvd_coords
#print axioms Eis.exists_int_of_mem_Gam2
#print axioms Eis.not_mem_Gam2_of_entry
#print axioms Eis.gamPlus_not_mem_Gam2
#print axioms Eis.gamMinus_not_mem_Gam2
#print axioms Eis.gamPlus_mul_inv_gamMinus_not_mem_Gam2
