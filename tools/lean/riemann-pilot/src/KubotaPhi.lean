import KubotaPhiSeries

/-! # The scattering coefficient in closed form (round 416)

S5f-9b of round 360's plan, part 3b, second half. Round 389's `φ(s) = π/((9√3/2)(s − 1))·Σ_c S(c)N(c)^{−s}`
is, for `Re s > 2`,
`φ(s) = π/((9√3/2)(s − 1))·2·3^{3−3s}·ζ_K(3s − 3)/((1 − 3^{2−3s})·ζ_K(3s − 2))`, with `ζ_K = ζ·L(·, χ₋₃)`.

* **Units and cube roots** (**`card_units_O`** and **`cube_eq_cube_iff`**, with `ω_ne_one`, `ω_ne_zero` and
  `three_cube_roots_ne`): `ℤ[ω]` has six units (Mathlib's `IsCyclotomicExtension.Rat.torsionOrder_eq`), and
  `a³ = b³` exactly when `a ∈ {b, ωb, ω²b}`.
* **The elements of norm `n`** (`eltsN`, a definition; **`mem_eltsN`** and **`sum_eltsN`**, with
  `span_unit_mul`): the generators of the ideals of norm `n`, six to an ideal.
* **The shift by `δ₃`** (**`totP_δ3_mul`**, with `absNorm_δ3_mul`, `three_mem_of_δ3_mem` and
  `primesOff3_δ3_mul`): `N(δ₃m) = 3N(m)`, and `δ₃m` and `m` have the same primes off `3`.
* **Summability** (`phiTerm`, a definition; **`summable_phiTerm`**, with `norm_one_sub_inv_natCast_le`,
  `norm_totP_le`, `norm_cuspS_le` and `normSq_σO_cast`): `|S(c)| ≤ N(c)` for `c ≠ 0`, so the series of round
  389 converges absolutely for `Re s > 2`.
* **Grouping by norm** (`normA`, a definition; **`LSeries_normA`**, with `normFiber_eq`,
  `ne_zero_of_mem_eltsN` and `tsum_fiber_phiTerm`): with `A(n) = Σ_{N(c)=n} S(c)`,
  `Σ_c S(c)N(c)^{−s} = Σ_n A(n)n^{−s}` (Mathlib's `HasSum.tsum_fiberwise`).
* **The values of `A`** (**`normA_cube`**, with `normA_eq_zero_of_not_cube`, `mem_filter_cube`,
  `three_mul_normA`, `sum_cuspS_cube` and `sum_totP_filter`): `A(n) = 0` unless `n = k³`, and
  `A(k³) = 2k³·Σ_{N𝔞=k/3} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P))` if `3 ∣ k`, `0` otherwise. Each cube `m³` comes from
  three `m`, `m = δ₃m′` shifts the norm by `3`, and each ideal has six generators.
* **The closed form** (`phiC`, a definition; **`LSeries_normA_eq`**, **`tsum_phiTerm_mul`** and
  **`eisPhi_eq_phiC`**, with `normA_eq_zero_of_not`, `cpow_ne_zero_of_ne`, `cpow_cube`, `term_normA_cube`,
  `tsum_phiTerm_eq`, `zetaK_ne_zero`, `one_sub_three_cpow_ne_zero` and `phiC_den_ne_zero`): reindexing the
  `L`-series of `A` onto `n = (3j)³` gives `2·3^{3−3s}` times round 415's series at `3s − 3`, and round 415's
  `LSeries_normSum_totP_mul` finishes. The denominator `(1 − 3^{2−3s})ζ_K(3s − 2)` is nonzero on `Re s ≥ 1`.
-/

open NumberField Ideal UniqueFactorizationMonoid
open scoped LSeries.notation

noncomputable section

namespace Eis

/-! ### Units and cube roots -/

/-- `ℤ[ω]` has six units. -/
theorem card_units_O : Fintype.card (𝓞 K)ˣ = 6 := by
  have h := IsCyclotomicExtension.Rat.torsionOrder_eq (n := 3) (K := K)
  rw [ite_eq_right (by decide)] at h
  have htop : NumberField.Units.torsion K = ⊤ := by
    ext u
    simp only [Subgroup.mem_top, iff_true]
    exact (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨6, by norm_num, units_pow_six u⟩)
  rw [NumberField.Units.torsionOrder, htop, Subgroup.card_top] at h
  rw [← Nat.card_eq_fintype_card, h]

theorem ω_ne_one : ω ≠ 1 := fun h => by
  have := ω_sq_add
  rw [h] at this
  norm_num at this

theorem ω_ne_zero : ω ≠ 0 := fun h => by
  have := ω_cube
  rw [h] at this
  norm_num at this

/-- **Cube roots**: `a³ = b³` exactly when `a ∈ {b, ωb, ω²b}`. -/
theorem cube_eq_cube_iff {a b : 𝓞 K} : a ^ 3 = b ^ 3 ↔ a = b ∨ a = ω * b ∨ a = ω ^ 2 * b := by
  constructor
  · intro h
    have e : (a - b) * (a - ω * b) * (a - ω ^ 2 * b) = 0 := by
      linear_combination h + (a * b ^ 2 - a ^ 2 * b) * ω_sq_add + (a * b ^ 2 - b ^ 3) * ω_cube
    rcases mul_eq_zero.1 e with h1 | h3
    · rcases mul_eq_zero.1 h1 with h1 | h2
      · exact Or.inl (sub_eq_zero.1 h1)
      · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h3))
  · rintro (rfl | rfl | rfl)
    · rfl
    · rw [mul_pow, ω_cube, one_mul]
    · rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ω_cube, one_pow, one_mul]

theorem three_cube_roots_ne {b : 𝓞 K} (hb : b ≠ 0) :
    b ≠ ω * b ∧ b ≠ ω ^ 2 * b ∧ ω * b ≠ ω ^ 2 * b := by
  refine ⟨fun h => ω_ne_one ?_, fun h => ?_, fun h => ?_⟩
  · exact (mul_right_cancel₀ hb (by rw [one_mul]; exact h.symm))
  · have h2 : ω ^ 2 = 1 := mul_right_cancel₀ hb (by rw [one_mul]; exact h.symm)
    exact ω_ne_one (by
      calc ω = ω ^ 2 * ω := by rw [h2, one_mul]
        _ = 1 := by rw [← pow_succ, ω_cube])
  · have h2 : ω = ω ^ 2 := mul_right_cancel₀ hb h
    exact ω_ne_one (by
      have h3 : ω * 1 = ω * ω := by rw [mul_one, ← sq]; exact h2
      exact (mul_left_cancel₀ ω_ne_zero h3).symm)

/-! ### The elements of norm `n` -/

open Classical in
/-- The elements of norm `n`: the generators of the ideals of norm `n`. -/
def eltsN (n : ℕ) : Finset (𝓞 K) :=
  (ofNorm n).biUnion fun I => Finset.univ.image fun u : (𝓞 K)ˣ => (u : 𝓞 K) * gen I

theorem span_unit_mul (u : (𝓞 K)ˣ) (x : 𝓞 K) : span {(u : 𝓞 K) * x} = span {x} := by
  rw [← span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.top_mul]

theorem mem_eltsN {n : ℕ} {c : 𝓞 K} : c ∈ eltsN n ↔ absNorm (span {c}) = n := by
  classical
  rw [eltsN, Finset.mem_biUnion]
  constructor
  · rintro ⟨I, hI, hc⟩
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hc
    rw [span_unit_mul, span_gen, mem_ofNorm.1 hI]
  · intro h
    refine ⟨span {c}, mem_ofNorm.2 h, Finset.mem_image.2 ?_⟩
    obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.1 (span_gen (span {c})))
    exact ⟨u, Finset.mem_univ _, by rw [mul_comm]; exact hu⟩

/-- **Six generators per ideal**: `Σ_{N(c)=n} h((c)) = 6·Σ_{N𝔞=n} h(𝔞)` for `n ≥ 1`. -/
theorem sum_eltsN {n : ℕ} (hn : n ≠ 0) (h : Ideal (𝓞 K) → ℂ) :
    ∑ c ∈ eltsN n, h (span {c}) = 6 * ∑ I ∈ ofNorm n, h I := by
  classical
  rw [eltsN, Finset.sum_biUnion]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I hI => ?_
    have hI0 : I ≠ ⊥ := ne_bot_of_norm hn (mem_ofNorm.1 hI)
    rw [Finset.sum_image fun u _ v _ huv => Units.ext (mul_right_cancel₀ (gen_ne_zero hI0) huv)]
    simp only [span_unit_mul, span_gen]
    rw [Finset.sum_const, Finset.card_univ, card_units_O, nsmul_eq_mul]
    norm_num
  · intro I _ J _ hIJ
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hcI hcJ
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hcI
    obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hcJ
    apply hIJ
    have e1 : span {(u : 𝓞 K) * gen I} = I := by rw [span_unit_mul, span_gen]
    have e2 : span {(v : 𝓞 K) * gen J} = J := by rw [span_unit_mul, span_gen]
    rw [← e1, ← e2, hv]

/-! ### The shift by `δ₃` -/

theorem absNorm_δ3_mul (m : 𝓞 K) : absNorm (span {δ3 * m}) = 3 * absNorm (span {m}) := by
  rw [← span_singleton_mul_span_singleton, map_mul, absNorm_span_δ3]

theorem three_mem_of_δ3_mem {P : Ideal (𝓞 K)} (h : δ3 ∈ P) : (3 : 𝓞 K) ∈ P := by
  have e : (3 : 𝓞 K) = -(δ3 * δ3) := by rw [← sq, δ3_sq]; ring
  rw [e]; exact P.neg_mem (P.mul_mem_left _ h)

open Classical in
theorem primesOff3_δ3_mul {m : 𝓞 K} (hm : m ≠ 0) :
    primesOff3 (span {δ3 * m}) = primesOff3 (span {m}) := by
  have hδ : span {δ3} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact δ3_ne_zero
  have hm' : span {m} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hm
  rw [primesOff3, primesOff3, ← span_singleton_mul_span_singleton, normalizedFactors_mul hδ hm',
    Multiset.toFinset_add, Finset.filter_union]
  have h0 : (normalizedFactors (span {δ3})).toFinset.filter (fun P => (3 : 𝓞 K) ∉ P) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro P hP h3
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff (by simpa using hδ)] at hP
    exact h3 (three_mem_of_δ3_mem (hP.2 (Ideal.mem_span_singleton_self _)))
  rw [h0, Finset.empty_union]

theorem totP_δ3_mul {m : 𝓞 K} (hm : m ≠ 0) : totP (span {δ3 * m}) = totP (span {m}) := by
  rw [totP, totP, primesOff3_δ3_mul hm]

/-! ### Bounds and summability -/

theorem norm_one_sub_inv_natCast_le (n : ℕ) : ‖(1 : ℂ) - 1 / (n : ℂ)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have e : (1 : ℂ) - 1 / (n : ℂ) = ((1 - 1 / (n : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hn1
      linarith
    · have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith

theorem norm_totP_le (I : Ideal (𝓞 K)) : ‖totP I‖ ≤ 1 := by
  rw [totP, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun P _ => norm_one_sub_inv_natCast_le _

/-- `|S(c)| ≤ N(c)` for `c ≠ 0`. -/
theorem norm_cuspS_le {c : 𝓞 K} (hc : c ≠ 0) : ‖cuspS c‖ ≤ absNorm (span {c}) := by
  by_cases h : ∃ m : 𝓞 K, δ3 ∣ m ∧ c = m ^ 3
  · obtain ⟨m, hδ, rfl⟩ := h
    have hm : m ≠ 0 := fun h0 => hc (by rw [h0]; ring)
    rw [cuspS_cube_eq hm hδ, norm_mul, ← Ideal.span_singleton_pow, map_pow, Nat.cast_pow, norm_pow,
      Complex.norm_natCast]
    calc ((absNorm (span {m}) : ℝ)) ^ 3 * ‖totP (span {m})‖
        ≤ (absNorm (span {m}) : ℝ) ^ 3 * 1 := by
          gcongr; exact norm_totP_le _
      _ = _ := by rw [mul_one]
  · rw [cuspS_eq_zero_of_not_cube hc h, norm_zero]; positivity

theorem normSq_σO_cast (c : 𝓞 K) :
    ((Complex.normSq (σO c) : ℝ) : ℂ) = ((absNorm (span {c}) : ℕ) : ℂ) := by
  rw [normSq_σO]; push_cast; rfl

/-- The summand of round 389's `φ`: `S(c)N(c)^{−s}`. -/
def phiTerm (s : ℂ) (c : 𝓞 K) : ℂ := cuspS c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)

theorem summable_phiTerm {s : ℂ} (hs : 2 < s.re) : Summable (phiTerm s) := by
  set τ : ℝ := 2 * s.re - 2 with hτ
  have hτ2 : 2 < τ := by rw [hτ]; linarith
  refine Summable.of_norm_bounded ((summable_O_rpow hτ2).mul_left ((2 : ℝ) ^ τ)) fun c => ?_
  by_cases hc : c = 0
  · subst hc
    have hs0 : -s ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [phiTerm, map_zero, Complex.normSq_zero, Complex.ofReal_zero, Complex.zero_cpow hs0, mul_zero,
      norm_zero]
    positivity
  · have hN : (0 : ℝ) < absNorm (span {c}) := by
      have : absNorm (span {c}) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
      exact_mod_cast Nat.pos_of_ne_zero this
    have h1 := one_le_norm_σO hc
    rw [phiTerm, normSq_σO, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re]
    have h0 : 0 < ‖σO c‖ := by linarith
    calc ‖cuspS c‖ * (absNorm (span {c}) : ℝ) ^ (-s.re)
        ≤ (absNorm (span {c}) : ℝ) * (absNorm (span {c}) : ℝ) ^ (-s.re) := by
          gcongr; exact norm_cuspS_le hc
      _ = Complex.normSq (σO c) ^ (1 - s.re) := by
          rw [normSq_σO, sub_eq_add_neg, Real.rpow_add hN, Real.rpow_one]
      _ = ‖σO c‖ ^ (-τ) := by rw [rpow_normSq_eq]
      _ ≤ (2 : ℝ) ^ τ * (1 + ‖σO c‖) ^ (-τ) := by
          calc ‖σO c‖ ^ (-τ) = 2 ^ τ * (2 * ‖σO c‖) ^ (-τ) := by
                rw [Real.mul_rpow (by norm_num) h0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
                  ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
            _ ≤ 2 ^ τ * (1 + ‖σO c‖) ^ (-τ) :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith))
                  (by positivity)

/-! ### Grouping by norm -/

/-- `A(n) = Σ_{N(c)=n} S(c)`. -/
def normA (n : ℕ) : ℂ := ∑ c ∈ eltsN n, cuspS c

theorem normFiber_eq (n : ℕ) : ((fun c : 𝓞 K => absNorm (span {c})) ⁻¹' {n}) = ↑(eltsN n) := by
  ext c; simp [mem_eltsN]

theorem ne_zero_of_mem_eltsN {n : ℕ} (hn : n ≠ 0) {c : 𝓞 K} (hc : c ∈ eltsN n) : c ≠ 0 := by
  rintro rfl
  have := mem_eltsN.1 hc
  rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at this
  exact hn this.symm

theorem tsum_fiber_phiTerm {s : ℂ} (hs : 2 < s.re) (n : ℕ) :
    ∑' c : ↑((fun c : 𝓞 K => absNorm (span {c})) ⁻¹' {n}), phiTerm s c = LSeries.term normA s n := by
  rw [normFiber_eq, Finset.tsum_subtype' (eltsN n) (phiTerm s)]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    have hs0 : -s ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc0 : c = 0 := by
      have := mem_eltsN.1 hc
      rwa [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at this
    subst hc0
    rw [phiTerm, map_zero, Complex.normSq_zero, Complex.ofReal_zero, Complex.zero_cpow hs0, mul_zero]
  · rw [LSeries.term_of_ne_zero hn, normA, Finset.sum_div]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [phiTerm, normSq_σO_cast, mem_eltsN.1 hc, Complex.cpow_neg, div_eq_mul_inv]

/-- **Grouping by norm**: `Σ_c S(c)N(c)^{−s} = Σ_n A(n)n^{−s}` for `Re s > 2`. -/
theorem LSeries_normA {s : ℂ} (hs : 2 < s.re) : LSeries normA s = ∑' c, phiTerm s c := by
  have h := (summable_phiTerm hs).hasSum.tsum_fiberwise (fun c : 𝓞 K => absNorm (span {c}))
  have e : (fun n : ℕ => ∑' c : ↑((fun c : 𝓞 K => absNorm (span {c})) ⁻¹' {n}), phiTerm s c) =
      LSeries.term normA s := funext (tsum_fiber_phiTerm hs)
  rw [e] at h
  exact h.tsum_eq

theorem normA_eq_zero_of_not_cube {n : ℕ} (hn : n ≠ 0) (h : ∀ k : ℕ, n ≠ k ^ 3) : normA n = 0 := by
  refine Finset.sum_eq_zero fun c hc => ?_
  refine cuspS_eq_zero_of_not_cube (ne_zero_of_mem_eltsN hn hc) ?_
  rintro ⟨m, -, rfl⟩
  apply h (absNorm (span {m}))
  rw [← mem_eltsN.1 hc, ← Ideal.span_singleton_pow, map_pow]

open Classical in
theorem mem_filter_cube {k : ℕ} {m a : 𝓞 K} (hm : m ∈ (eltsN k).filter (δ3 ∣ ·))
    (ha : a = m ∨ a = ω * m ∨ a = ω ^ 2 * m) : a ∈ (eltsN k).filter (δ3 ∣ ·) := by
  obtain ⟨hmk, hδ⟩ := Finset.mem_filter.1 hm
  refine Finset.mem_filter.2 ⟨mem_eltsN.2 ?_, ?_⟩
  · rcases ha with rfl | rfl | rfl
    · exact mem_eltsN.1 hmk
    · rw [show ω * m = (ωu : 𝓞 K) * m from rfl, span_unit_mul]; exact mem_eltsN.1 hmk
    · rw [show ω ^ 2 * m = ((ωu ^ 2 : (𝓞 K)ˣ) : 𝓞 K) * m by rw [Units.val_pow_eq_pow_val]; rfl,
        span_unit_mul]
      exact mem_eltsN.1 hmk
  · rcases ha with rfl | rfl | rfl
    · exact hδ
    · exact dvd_mul_of_dvd_right hδ _
    · exact dvd_mul_of_dvd_right hδ _

open Classical in
/-- **Cubes three to one**: `3·A(k³) = Σ_{N(m)=k, δ₃ ∣ m} S(m³)` for `k ≥ 1`. -/
theorem three_mul_normA {k : ℕ} (hk : k ≠ 0) :
    3 * normA (k ^ 3) = ∑ m ∈ (eltsN k).filter (δ3 ∣ ·), cuspS (m ^ 3) := by
  set M := (eltsN k).filter (δ3 ∣ ·) with hM
  rw [Finset.sum_comp (fun c => cuspS c) (fun m => m ^ 3)]
  have hfib : ∀ b ∈ M.image (fun m => m ^ 3), (M.filter fun a => a ^ 3 = b).card = 3 := by
    intro b hb
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hb
    have hm0 : m ≠ 0 := ne_zero_of_mem_eltsN hk (Finset.mem_filter.1 hm).1
    obtain ⟨h1, h2, h3⟩ := three_cube_roots_ne hm0
    rw [Finset.card_eq_three]
    refine ⟨m, ω * m, ω ^ 2 * m, h1, h2, h3, ?_⟩
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, ha⟩; exact cube_eq_cube_iff.1 ha
    · intro ha; exact ⟨mem_filter_cube hm ha, cube_eq_cube_iff.2 ha⟩
  rw [Finset.sum_congr rfl fun b hb => by rw [hfib b hb], Finset.sum_nsmul]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  congr 1
  symm
  refine Finset.sum_subset ?_ ?_
  · intro c hc
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hc
    rw [mem_eltsN, ← Ideal.span_singleton_pow, map_pow, mem_eltsN.1 (Finset.mem_filter.1 hm).1]
  · intro c hc hcn
    by_contra hS
    have hc0 : c ≠ 0 := ne_zero_of_mem_eltsN (pow_ne_zero 3 hk) hc
    obtain ⟨m, hδ, rfl⟩ : ∃ m : 𝓞 K, δ3 ∣ m ∧ c = m ^ 3 := by
      by_contra h; exact hS (cuspS_eq_zero_of_not_cube hc0 h)
    apply hcn
    refine Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨mem_eltsN.2 ?_, hδ⟩, rfl⟩
    have := mem_eltsN.1 hc
    rw [← Ideal.span_singleton_pow, map_pow] at this
    exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) this

open Classical in
theorem sum_cuspS_cube {k : ℕ} (hk : k ≠ 0) :
    ∑ m ∈ (eltsN k).filter (δ3 ∣ ·), cuspS (m ^ 3) =
      (k : ℂ) ^ 3 * ∑ m ∈ (eltsN k).filter (δ3 ∣ ·), totP (span {m}) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hmk, hδ⟩ := Finset.mem_filter.1 hm
  rw [cuspS_cube_eq (ne_zero_of_mem_eltsN hk hmk) hδ, mem_eltsN.1 hmk]
  rfl

open Classical in
theorem sum_totP_filter {k : ℕ} (hk : k ≠ 0) :
    ∑ m ∈ (eltsN k).filter (δ3 ∣ ·), totP (span {m}) =
      if 3 ∣ k then 6 * normSum totP (k / 3) else 0 := by
  split_ifs with h3
  · obtain ⟨j, rfl⟩ := h3
    have hj : j ≠ 0 := by omega
    have himg : (eltsN (3 * j)).filter (δ3 ∣ ·) = (eltsN j).image (δ3 * ·) := by
      ext m
      constructor
      · intro hm
        obtain ⟨hmk, m', rfl⟩ := Finset.mem_filter.1 hm
        refine Finset.mem_image.2 ⟨m', mem_eltsN.2 ?_, rfl⟩
        have := mem_eltsN.1 hmk
        rw [absNorm_δ3_mul] at this
        omega
      · intro hm
        obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_filter.2 ⟨mem_eltsN.2 (by rw [absNorm_δ3_mul, mem_eltsN.1 hm']),
          dvd_mul_right _ _⟩
    rw [himg, Finset.sum_image fun a _ b _ h => mul_left_cancel₀ δ3_ne_zero h,
      show 3 * j / 3 = j by omega, normSum, ← sum_eltsN hj totP]
    exact Finset.sum_congr rfl fun m hm => totP_δ3_mul (ne_zero_of_mem_eltsN hj hm)
  · refine Finset.sum_eq_zero fun m hm => absurd ?_ h3
    obtain ⟨hmk, m', rfl⟩ := Finset.mem_filter.1 hm
    have := mem_eltsN.1 hmk
    rw [absNorm_δ3_mul] at this
    exact ⟨_, this.symm⟩

open Classical in
/-- **`A(k³)`**: `2k³·Σ_{N𝔞=k/3} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P))` if `3 ∣ k`, and `0` otherwise. -/
theorem normA_cube {k : ℕ} (hk : k ≠ 0) :
    normA (k ^ 3) = if 3 ∣ k then 2 * (k : ℂ) ^ 3 * normSum totP (k / 3) else 0 := by
  have h := three_mul_normA hk
  rw [sum_cuspS_cube hk, sum_totP_filter hk] at h
  split_ifs at h ⊢ with h3
  · linear_combination h / 3
  · linear_combination h / 3

/-! ### The closed form -/

section ClosedForm

open DirichletCharacter

theorem normA_eq_zero_of_not {n : ℕ} (hn : n ≠ 0) (h : ∀ j : ℕ, n ≠ (3 * j) ^ 3) : normA n = 0 := by
  by_cases hc : ∃ k : ℕ, n = k ^ 3
  · obtain ⟨k, rfl⟩ := hc
    have hk : k ≠ 0 := by rintro rfl; simp at hn
    rw [normA_cube hk, ite_eq_right]
    rintro ⟨j, rfl⟩
    exact h j rfl
  · push Not at hc
    exact normA_eq_zero_of_not_cube hn hc

theorem cpow_ne_zero_of_ne {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hx]; exact Complex.exp_ne_zero _

theorem cpow_cube (j : ℕ) (s : ℂ) :
    ((((3 * j) ^ 3 : ℕ) : ℂ)) ^ s = (3 : ℂ) ^ (3 * s) * (j : ℂ) ^ (3 * s) := by
  have h1 : ((((3 * j) ^ 3 : ℕ) : ℂ)) ^ s = (((3 * j : ℕ) : ℂ)) ^ (((3 : ℕ) : ℂ) * s) := by
    rw [Complex.natCast_cpow_natCast_mul, Nat.cast_pow]
  rw [h1, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  norm_num

theorem term_normA_cube (s : ℂ) (j : ℕ) :
    LSeries.term normA s ((3 * j) ^ 3) =
      2 * 3 ^ (3 - 3 * s) * LSeries.term (normSum totP) (3 * s - 3) j := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  have hk : 3 * j ≠ 0 := by omega
  have hn : (3 * j) ^ 3 ≠ 0 := pow_ne_zero 3 hk
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hj, normA_cube hk,
    ite_eq_left (dvd_mul_right 3 j), show 3 * j / 3 = j by omega, cpow_cube]
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hj' : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hj
  rw [Complex.cpow_sub _ _ h3, Complex.cpow_sub _ _ hj']
  have e3 : (3 : ℂ) ^ (3 : ℂ) = 27 := by
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; norm_num
  have ej : (j : ℂ) ^ (3 : ℂ) = (j : ℂ) ^ 3 := by
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have hA := cpow_ne_zero_of_ne h3 (3 * s)
  have hJ := cpow_ne_zero_of_ne hj' (3 * s)
  rw [e3, ej]
  push_cast
  field_simp
  ring

/-- **Reindexing onto the cubes `(3j)³`**: `Σ_n A(n)n^{−s} = 2·3^{3−3s}·Σ_j (Σ_{N𝔞=j} ⋯)·j^{3−3s}`, as
`L`-series (for every `s`). -/
theorem LSeries_normA_eq (s : ℂ) :
    LSeries normA s = 2 * 3 ^ (3 - 3 * s) * LSeries (normSum totP) (3 * s - 3) := by
  have hinj : Function.Injective (fun j : ℕ => (3 * j) ^ 3) := fun a b h => by
    have := Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
    omega
  have hsupp : Function.support (LSeries.term normA s) ⊆ Set.range (fun j : ℕ => (3 * j) ^ 3) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hn0 : n ≠ 0 := fun h => hn (by rw [h, LSeries.term_zero])
    by_contra hr
    apply hn
    rw [LSeries.term_of_ne_zero hn0, normA_eq_zero_of_not hn0 (fun j hj => hr ⟨j, hj.symm⟩),
      zero_div]
  rw [LSeries, ← hinj.tsum_eq hsupp, LSeries, ← tsum_mul_left]
  exact tsum_congr fun j => term_normA_cube s j

/-- **Round 389's sum, regrouped**: `Σ_c S(c)N(c)^{−s} = 2·3^{3−3s}·Σ_n (Σ_{N𝔞=n} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P)))
·n^{3−3s}` for `Re s > 2`. -/
theorem tsum_phiTerm_eq {s : ℂ} (hs : 2 < s.re) :
    ∑' c, phiTerm s c = 2 * 3 ^ (3 - 3 * s) * LSeries (normSum totP) (3 * s - 3) := by
  rw [← LSeries_normA hs, LSeries_normA_eq]

/-- `Σ_c S(c)N(c)^{−s}·(1 − 3^{2−3s})·ζ_K(3s − 2) = 2·3^{3−3s}·ζ_K(3s − 3)` for `Re s > 2`, with
`ζ_K = ζ·L(·, χ₋₃)`. -/
theorem tsum_phiTerm_mul {s : ℂ} (hs : 2 < s.re) :
    (∑' c, phiTerm s c) * ((1 - 3 ^ (2 - 3 * s)) *
      (riemannZeta (3 * s - 2) * LFunction PsiOmega.chi3 (3 * s - 2))) =
      2 * 3 ^ (3 - 3 * s) * (riemannZeta (3 * s - 3) * LFunction PsiOmega.chi3 (3 * s - 3)) := by
  have hu : 1 < (3 * s - 3).re := by simp; linarith
  have h := LSeries_normSum_totP_mul hu
  rw [show 3 * s - 3 + 1 = 3 * s - 2 by ring, show -(3 * s - 2) = 2 - 3 * s by ring] at h
  rw [tsum_phiTerm_eq hs]
  linear_combination (2 * 3 ^ (3 - 3 * s)) * h

/-- `ζ_K(w) = ζ(w)L(w, χ₋₃) ≠ 0` on `Re w ≥ 1`. -/
theorem zetaK_ne_zero {w : ℂ} (hw : 1 ≤ w.re) : riemannZeta w * LFunction PsiOmega.chi3 w ≠ 0 :=
  mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hw)
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl PsiOmega.chi3_ne_one) hw)

/-- `1 − 3^{−w} ≠ 0` on `Re w > 0`. -/
theorem one_sub_three_cpow_ne_zero {w : ℂ} (hw : 0 < w.re) : 1 - (3 : ℂ) ^ (-w) ≠ 0 := by
  intro h
  have h1 : ‖(3 : ℂ) ^ (-w)‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
  rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
    Complex.neg_re] at h1
  have : (3 : ℝ) ^ (-w.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

/-- **The closed form of `φ`**:
`π/((9√3/2)(s − 1))·2·3^{3−3s}·ζ_K(3s − 3)/((1 − 3^{2−3s})·ζ_K(3s − 2))`. -/
def phiC (s : ℂ) : ℂ :=
  Real.pi / (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (s - 1)) *
    (2 * 3 ^ (3 - 3 * s) * (riemannZeta (3 * s - 3) * LFunction PsiOmega.chi3 (3 * s - 3)) /
      ((1 - 3 ^ (2 - 3 * s)) * (riemannZeta (3 * s - 2) * LFunction PsiOmega.chi3 (3 * s - 2))))

theorem phiC_den_ne_zero {s : ℂ} (hs : 1 ≤ s.re) :
    (1 - (3 : ℂ) ^ (2 - 3 * s)) * (riemannZeta (3 * s - 2) * LFunction PsiOmega.chi3 (3 * s - 2)) ≠ 0 := by
  refine mul_ne_zero ?_ (zetaK_ne_zero (by simp; linarith))
  have := one_sub_three_cpow_ne_zero (w := 3 * s - 2) (by simp; linarith)
  rwa [show -(3 * s - 2) = 2 - 3 * s by ring] at this

/-- **Round 389's `φ` in closed form**: `φ(s) = π/((9√3/2)(s − 1))·2·3^{3−3s}·ζ_K(3s − 3)/((1 − 3^{2−3s})·
ζ_K(3s − 2))` for `Re s > 2`. -/
theorem eisPhi_eq_phiC {s : ℂ} (hs : 2 < s.re) : eisPhi s = phiC s := by
  have hden := phiC_den_ne_zero (s := s) (by linarith)
  unfold eisPhi phiC
  congr 1
  show ∑' c, phiTerm s c = _
  rw [eq_div_iff hden]
  exact tsum_phiTerm_mul hs

end ClosedForm

end Eis

end

#print axioms Eis.card_units_O
#print axioms Eis.ω_ne_one
#print axioms Eis.ω_ne_zero
#print axioms Eis.cube_eq_cube_iff
#print axioms Eis.three_cube_roots_ne
#print axioms Eis.span_unit_mul
#print axioms Eis.mem_eltsN
#print axioms Eis.sum_eltsN
#print axioms Eis.absNorm_δ3_mul
#print axioms Eis.three_mem_of_δ3_mem
#print axioms Eis.primesOff3_δ3_mul
#print axioms Eis.totP_δ3_mul
#print axioms Eis.norm_one_sub_inv_natCast_le
#print axioms Eis.norm_totP_le
#print axioms Eis.norm_cuspS_le
#print axioms Eis.normSq_σO_cast
#print axioms Eis.summable_phiTerm
#print axioms Eis.normFiber_eq
#print axioms Eis.ne_zero_of_mem_eltsN
#print axioms Eis.tsum_fiber_phiTerm
#print axioms Eis.LSeries_normA
#print axioms Eis.normA_eq_zero_of_not_cube
#print axioms Eis.mem_filter_cube
#print axioms Eis.three_mul_normA
#print axioms Eis.sum_cuspS_cube
#print axioms Eis.sum_totP_filter
#print axioms Eis.normA_cube
#print axioms Eis.normA_eq_zero_of_not
#print axioms Eis.cpow_ne_zero_of_ne
#print axioms Eis.cpow_cube
#print axioms Eis.term_normA_cube
#print axioms Eis.LSeries_normA_eq
#print axioms Eis.tsum_phiTerm_eq
#print axioms Eis.tsum_phiTerm_mul
#print axioms Eis.zetaK_ne_zero
#print axioms Eis.one_sub_three_cpow_ne_zero
#print axioms Eis.phiC_den_ne_zero
#print axioms Eis.eisPhi_eq_phiC
