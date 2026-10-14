import KubotaCuspZero

/-! # The scattering coefficient at the cusp `0` in closed form, and its pole (round 441)

S5f-12 of round 360's plan, part 2. Round 440's next step planned `S₀(m³)`, the closed form of round 440's
`φ₀(s) = π/((9√3/2)(s − 1))·Σ_d S₀(d)N(d)^{−s}` and its pole at `4/3`. This round proves them, with
`ζ_K = ζ·L(·, χ₋₃)`:

* **The count at the cubes** (**`count_bRow_fst`** and **`cuspS0_cube_eq`**, with `bRow_iff_fst` and
  `count_three_mem`): for `d` primary, `(c, d)` is a bottom row exactly when `3 ∣ c` and `c` lies in no prime
  of `d` off `3`. The classes `c` modulo `3d` of these rows number `N(d)·Π_{P ∣ d, 3 ∉ P}(1 − 1/N(P))`, by
  inclusion–exclusion and the Chinese remainder theorem, as in round 414's `count_bRow`. So
  `S₀(m³) = N(m)³·Π_{P ∣ m, 3 ∉ P}(1 − 1/N(P))` for `m` primary.
* **Grouping by norm** (`eltSum`, a definition; **`LSeries_eltSum`**, with `cuspS0_eq_zero_of_not_primary`,
  `norm_cuspS0_le` and `summable_mul_normSq_cpow`): `|S₀(d)| ≤ N(d)`, and for every `f` with `|f(c)| ≤ N(c)`
  and `Re s > 2`, `Σ_c f(c)N(c)^{−s} = Σ_n (Σ_{N(c)=n} f(c))n^{−s}`, as in round 416.
* **The values of `A₀(n) = Σ_{N(d)=n} S₀(d)`** (`normSum3`, a definition; **`eltSum_cuspS0_cube_eq`**, with
  `eltSum_cuspS0_eq_zero_of_not_cube`, `eq_of_cube_eq_primary`, `eltSum_cuspS0_cube` and `sum_primary_eltsN`):
  `A₀(n) = 0` unless `n` is a cube, and `A₀(k³) = k³·Σ_{N𝔞=k} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P))` for `3 ∤ k`, `0`
  for `3 ∣ k`. Primary elements with the same cube are equal (round 416's `cube_eq_cube_iff`, round 290's
  `primary_unique`), and an ideal of norm prime to `3` has exactly one primary generator (round 340's
  `pgen_spec3`, round 290's `pgen_eq`); a primary element has norm `≡ 1 (mod 3)` (round 362's
  `absNorm_primary_mod`).
* **The factor at `3`** (**`normSum_totP_three_mul`** and **`LSeries_normSum3`**, with `δ3_dvd_of_three_dvd`,
  `LSeriesSummable_normSum_totP` and `normSum3_eq_conv`): an element whose norm is divisible by `3` is
  divisible by `δ₃`, so round 416's `sum_totP_filter` gives
  `Σ_{N𝔞=3k} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P)) = Σ_{N𝔞=k} ⋯`. Hence
  `Σ_{3 ∤ k} (Σ_{N𝔞=k} ⋯)k^{−u} = (1 − 3^{−u})·Σ_k (Σ_{N𝔞=k} ⋯)k^{−u}` for `Re u > 1`, through round 415's
  `eul3`.
* **The closed form** (`phi0C`, a definition; **`tsum_cuspS0_mul`** and **`eisPhi0_eq_phi0C`**, with
  `term_eltSum_cuspS0_cube` and `LSeries_eltSum_cuspS0`): for `Re s > 2`,
  `φ₀(s) = π/((9√3/2)(s − 1))·(1 − 3^{3−3s})·ζ_K(3s − 3)/((1 − 3^{2−3s})·ζ_K(3s − 2))`, through round 415's
  `LSeries_normSum_totP_mul` at `u = 3s − 3`.
* **The pole** (**`differentiableAt_phi0C`** and **`tendsto_phi0C_residue`**, with `phi0C_eq`):
  `φ₀ = φ·(1 − 3^{3−3s})/(2·3^{3−3s})` with round 416's closed form of `φ`. So `φ₀` is complex-differentiable
  at every `s ≠ 4/3` with `Re s > 1`, and `(s − 4/3)·φ₀(s)` tends to round 417's residue of `φ`, which is not
  `0`: the factor is `1` at `4/3`.
-/

open NumberField Ideal UniqueFactorizationMonoid Filter Topology DirichletCharacter
open scoped LSeries.notation

noncomputable section

namespace Eis

/-! ### The count at the cubes -/

/-- For `d` primary, `(c, d)` is a bottom row exactly when `3 ∣ c` and `c` lies in no prime of `d`. -/
theorem bRow_iff_fst {c d : 𝓞 K} (hd : Primary d) :
    BRow (c, d) ↔ (3 : 𝓞 K) ∣ c ∧ ∀ P ∈ primesOff3 (span {d}), c ∉ P := by
  have hd0 := primary_ne_zero hd
  constructor
  · rintro ⟨hcd, h3, -⟩
    refine ⟨h3, fun P hP hcP => ?_⟩
    obtain ⟨hPmax, hdP, -⟩ := mem_primesOff3 hd0 hP
    obtain ⟨u, v, huv⟩ := hcd
    exact hPmax.ne_top (P.eq_top_of_isUnit_mem
      (huv ▸ P.add_mem (P.mul_mem_left u hcP) (P.mul_mem_left v hdP)) isUnit_one)
  · rintro ⟨h3, hS⟩
    refine ⟨?_, h3, hd⟩
    by_contra hcd
    have hsup : span {c} ⊔ span {d} ≠ ⊤ := fun h =>
      hcd ((Ideal.isCoprime_span_singleton_iff c d).1 (Ideal.isCoprime_iff_sup_eq.2 h))
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hsup
    have hcP : c ∈ P := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))
    have hdP : d ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self d))
    by_cases h3P : (3 : 𝓞 K) ∈ P
    · obtain ⟨k, hk⟩ := hd
      have h1 : (1 : 𝓞 K) ∈ P := by
        rw [show (1 : 𝓞 K) = d - 3 * k by linear_combination (-1 : 𝓞 K) * hk]
        exact P.sub_mem hdP (P.mul_mem_right k h3P)
      exact hPmax.ne_top (P.eq_top_of_isUnit_mem h1 isUnit_one)
    · exact hS P (mem_primesOff3_of hd0 hPmax.isPrime hdP h3P) hcP

open Classical in
/-- **Classes in an ideal** (CRT): for `𝔡 ∣ (d)` prime to `3`, the classes modulo `3d` whose representative
is divisible by `3` and lies in `𝔡` number `N(d)/N(𝔡)`. -/
theorem count_three_mem {d : 𝓞 K} (hd : d ≠ 0) {D : Ideal (𝓞 K)} (hDd : D ∣ span {d})
    (hD3 : D ⊔ span {(3 : 𝓞 K)} = ⊤) :
    (∑' r : 𝓞 K ⧸ span {3 * d},
      if (3 : 𝓞 K) ∣ repQ (3 * d) r ∧ repQ (3 * d) r ∈ D then (1 : ℂ) else 0) * absNorm D =
      absNorm (span {d}) := by
  set B : Ideal (𝓞 K) := span {(3 : 𝓞 K)} * D with hB
  have hBinf : B = span {(3 : 𝓞 K)} ⊓ D := Ideal.mul_eq_inf_of_coprime (by rwa [sup_comm])
  have hdD : d ∈ D := by rw [← Ideal.span_singleton_le_iff_mem]; exact Ideal.le_of_dvd hDd
  have hAB : span {3 * d} ≤ B := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self 3) hdD
  have hcond : ∀ x : 𝓞 K, ((3 : 𝓞 K) ∣ x ∧ x ∈ D) ↔
      Ideal.Quotient.mk B x = Ideal.Quotient.mk B 0 := by
    intro x
    rw [Ideal.Quotient.eq, sub_zero, hBinf, Submodule.mem_inf, Ideal.mem_span_singleton]
  have hfin := finite_quot_three_mul hd
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * d})
  have hB0 : B ≠ ⊥ := fun h => by
    have := hAB (Ideal.mem_span_singleton_self (3 * d))
    rw [h, Ideal.mem_bot] at this
    exact three_mul_ne_zero hd this
  have : Finite (𝓞 K ⧸ B) := Ideal.finiteQuotientOfFreeOfNeBot _ hB0
  let := Fintype.ofFinite (𝓞 K ⧸ B)
  have key : (Finset.univ.filter fun r : 𝓞 K ⧸ span {3 * d} =>
      (3 : 𝓞 K) ∣ repQ (3 * d) r ∧ repQ (3 * d) r ∈ D) =
      Finset.univ.filter fun r => Ideal.Quotient.factor hAB r = Ideal.Quotient.mk B 0 := by
    refine Finset.filter_congr fun r _ => ?_
    rw [hcond, ← Ideal.Quotient.factor_mk hAB (repQ (3 * d) r), repQ_mk]
  have hfib := card_fiber_mul (Ideal.Quotient.factor hAB).toAddMonoidHom
    (Ideal.Quotient.factor_surjective hAB) (Ideal.Quotient.mk B 0)
  have hNB : absNorm B = 9 * absNorm D := by rw [hB, map_mul, absNorm_span_three]
  have hNA : absNorm (span {3 * d}) = 9 * absNorm (span {d}) := by
    rw [← span_singleton_mul_span_singleton, map_mul, absNorm_span_three]
  rw [card_quot_eq_absNorm, card_quot_eq_absNorm, hNB, hNA] at hfib
  have hN : (Finset.univ.filter fun r => Ideal.Quotient.factor hAB r = Ideal.Quotient.mk B 0).card *
      absNorm D = absNorm (span {d}) := by
    have hfib' : (Finset.univ.filter fun r => Ideal.Quotient.factor hAB r =
        Ideal.Quotient.mk B 0).card * (9 * absNorm D) = 9 * absNorm (span {d}) := hfib
    have h9 : 9 * ((Finset.univ.filter fun r => Ideal.Quotient.factor hAB r =
        Ideal.Quotient.mk B 0).card * absNorm D) = 9 * absNorm (span {d}) := by
      rw [← hfib']; ring
    omega
  rw [tsum_fintype, Finset.sum_boole, key]
  exact_mod_cast hN

open Classical in
/-- **The count of bottom rows `(c, d)`**: for `d` primary, the classes `c` modulo `3d` with `(c, d)` a bottom
row number `N(d)·Π_{P ∣ d}(1 − 1/N(P))`, by inclusion–exclusion over the primes of `d` (round 332's
`indicator_forall_not`) and the CRT count `count_three_mem`. -/
theorem count_bRow_fst {d : 𝓞 K} (hd : Primary d) :
    (∑' r : 𝓞 K ⧸ span {3 * d}, if BRow (repQ (3 * d) r, d) then (1 : ℂ) else 0) =
      absNorm (span {d}) * ∏ P ∈ primesOff3 (span {d}), (1 - 1 / (absNorm P : ℂ)) := by
  have hd0 := primary_ne_zero hd
  have hfin := finite_quot_three_mul hd0
  let := Fintype.ofFinite (𝓞 K ⧸ span {3 * d})
  set S := primesOff3 (span {d}) with hSdef
  have hSP : ∀ P ∈ S, P.IsMaximal ∧ d ∈ P ∧ (3 : 𝓞 K) ∉ P := fun P hP => mem_primesOff3 hd0 hP
  have hind : ∀ c : 𝓞 K, (if BRow (c, d) then (1 : ℂ) else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        (if (3 : 𝓞 K) ∣ c ∧ c ∈ ∏ P ∈ T, P then 1 else 0) := by
    intro c
    have e1 : (if BRow (c, d) then (1 : ℂ) else 0) =
        (if (3 : 𝓞 K) ∣ c then (1 : ℂ) else 0) * (if ∀ P ∈ S, ¬ c ∈ P then 1 else 0) := by
      rw [ite_zero_mul_ite_zero, one_mul]
      exact if_congr (bRow_iff_fst hd) rfl rfl
    rw [e1, indicator_forall_not S (fun P => c ∈ P), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTmax : ∀ P ∈ T, P.IsMaximal := fun P hP => (hSP P (Finset.mem_powerset.1 hT hP)).1
    have hmem : (c ∈ ∏ P ∈ T, P) ↔ ∀ P ∈ T, c ∈ P := by
      rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, prod_dvd_iff hTmax]
      exact forall₂_congr fun P _ => by rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    rw [mul_left_comm, ite_zero_mul_ite_zero, one_mul]
    exact congrArg _ (if_congr (and_congr_right fun _ => hmem.symm) rfl rfl)
  have hcount : ∀ T ∈ S.powerset, (∑' r : 𝓞 K ⧸ span {3 * d},
      if (3 : 𝓞 K) ∣ repQ (3 * d) r ∧ repQ (3 * d) r ∈ ∏ P ∈ T, P then (1 : ℂ) else 0) =
      absNorm (span {d}) / ∏ P ∈ T, (absNorm P : ℂ) := by
    intro T hT
    have hTP : ∀ P ∈ T, P.IsMaximal ∧ d ∈ P ∧ (3 : 𝓞 K) ∉ P :=
      fun P hP => hSP P (Finset.mem_powerset.1 hT hP)
    have hDd : (∏ P ∈ T, P) ∣ span {d} := (prod_dvd_iff (fun P hP => (hTP P hP).1) _).2
      fun P hP => by rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact (hTP P hP).2.1
    have hD3 := sup_three_eq_top (T := T) fun P hP => ⟨(hTP P hP).1, (hTP P hP).2.2⟩
    have h := count_three_mem hd0 hDd hD3
    have hN0 : (∏ P ∈ T, (absNorm P : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P hP => by
      have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField (hTP P hP).1
        (RingOfIntegers.not_isField K)
      exact_mod_cast fun h0 => hP0 (Ideal.absNorm_eq_zero_iff.1 h0)
    rw [map_prod, Nat.cast_prod] at h
    rw [eq_div_iff hN0, h]
  calc (∑' r : 𝓞 K ⧸ span {3 * d}, if BRow (repQ (3 * d) r, d) then (1 : ℂ) else 0)
      = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * ∑' r : 𝓞 K ⧸ span {3 * d},
          (if (3 : 𝓞 K) ∣ repQ (3 * d) r ∧ repQ (3 * d) r ∈ ∏ P ∈ T, P then 1 else 0) := by
        simp_rw [hind, tsum_fintype]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun T _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (absNorm (span {d}) / ∏ P ∈ T, (absNorm P : ℂ)) :=
        Finset.sum_congr rfl fun T hT => by rw [hcount T hT]
    _ = absNorm (span {d}) * ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card / ∏ P ∈ T, (absNorm P : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun T _ => by ring
    _ = _ := by
        congr 1
        have h := congrArg (fun x : ℝ => (x : ℂ)) (sum_powerset_inv S)
        push_cast at h
        exact h

/-- **`S₀` at the cubes**: for `m` primary, `S₀(m³) = N(m)³·Π_{P ∣ m}(1 − 1/N(P))`. -/
theorem cuspS0_cube_eq {m : 𝓞 K} (hm : Primary m) :
    cuspS0 (m ^ 3) = (absNorm (span {m}) : ℂ) ^ 3 * totP (span {m}) := by
  rw [cuspS0_cube hm, count_bRow_fst (primary_pow hm 3), ← Ideal.span_singleton_pow, map_pow,
    primesOff3_pow _ three_ne_zero, Nat.cast_pow]
  rfl

theorem cuspS0_eq_zero_of_not_primary {d : 𝓞 K} (hd : ¬ Primary d) : cuspS0 d = 0 := by
  rw [cuspS0_eq_tsum]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  unfold cuspF0
  exact ite_eq_right fun h => hd h.2.2

/-- `|S₀(d)| ≤ N(d)`. -/
theorem norm_cuspS0_le (d : 𝓞 K) : ‖cuspS0 d‖ ≤ absNorm (span {d}) := by
  by_cases hd : Primary d
  · by_cases h : ∃ m : 𝓞 K, Primary m ∧ d = m ^ 3
    · obtain ⟨m, hm, rfl⟩ := h
      rw [cuspS0_cube_eq hm, norm_mul, ← Ideal.span_singleton_pow, map_pow, Nat.cast_pow, norm_pow,
        Complex.norm_natCast]
      calc ((absNorm (span {m}) : ℝ)) ^ 3 * ‖totP (span {m})‖
          ≤ (absNorm (span {m}) : ℝ) ^ 3 * 1 := by
            gcongr; exact norm_totP_le _
        _ = _ := by rw [mul_one]
    · rw [cuspS0_eq_zero_of_not_cube hd h, norm_zero]; positivity
  · rw [cuspS0_eq_zero_of_not_primary hd, norm_zero]; positivity

/-! ### Grouping by norm -/

/-- For `|f(c)| ≤ N(c)`, `Σ_c f(c)N(c)^{−s}` converges absolutely for `Re s > 2` (as round 416's
`summable_phiTerm`). -/
theorem summable_mul_normSq_cpow {f : 𝓞 K → ℂ} (hf : ∀ c, ‖f c‖ ≤ absNorm (span {c})) {s : ℂ}
    (hs : 2 < s.re) : Summable fun c => f c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  set τ : ℝ := 2 * s.re - 2 with hτ
  have hτ2 : 2 < τ := by rw [hτ]; linarith
  refine Summable.of_norm_bounded ((summable_O_rpow hτ2).mul_left ((2 : ℝ) ^ τ)) fun c => ?_
  by_cases hc : c = 0
  · subst hc
    have hs0 : -s ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [map_zero, Complex.normSq_zero, Complex.ofReal_zero, Complex.zero_cpow hs0, mul_zero, norm_zero]
    positivity
  · have hN : (0 : ℝ) < absNorm (span {c}) := by
      have : absNorm (span {c}) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
      exact_mod_cast Nat.pos_of_ne_zero this
    have h1 := one_le_norm_σO hc
    rw [normSq_σO, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re]
    have h0 : 0 < ‖σO c‖ := by linarith
    calc ‖f c‖ * (absNorm (span {c}) : ℝ) ^ (-s.re)
        ≤ (absNorm (span {c}) : ℝ) * (absNorm (span {c}) : ℝ) ^ (-s.re) := by
          gcongr; exact hf c
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

/-- `Σ_{N(c)=n} f(c)`. -/
def eltSum (f : 𝓞 K → ℂ) (n : ℕ) : ℂ := ∑ c ∈ eltsN n, f c

/-- **Grouping by norm**: for `|f(c)| ≤ N(c)` and `Re s > 2`,
`Σ_c f(c)N(c)^{−s} = Σ_n (Σ_{N(c)=n} f(c))n^{−s}` (as round 416's `LSeries_normA`). -/
theorem LSeries_eltSum {f : 𝓞 K → ℂ} (hf : ∀ c, ‖f c‖ ≤ absNorm (span {c})) {s : ℂ} (hs : 2 < s.re) :
    LSeries (eltSum f) s = ∑' c, f c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s) := by
  have h := (summable_mul_normSq_cpow hf hs).hasSum.tsum_fiberwise (fun c : 𝓞 K => absNorm (span {c}))
  have e : (fun n : ℕ => ∑' c : ↑((fun c : 𝓞 K => absNorm (span {c})) ⁻¹' {n}),
      f c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s)) = LSeries.term (eltSum f) s := by
    funext n
    rw [normFiber_eq,
      Finset.tsum_subtype' (eltsN n) (fun c => f c * ((Complex.normSq (σO c) : ℝ) : ℂ) ^ (-s))]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      have hs0 : -s ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc0 : c = 0 := by
        have := mem_eltsN.1 hc
        rwa [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at this
      subst hc0
      rw [map_zero, Complex.normSq_zero, Complex.ofReal_zero, Complex.zero_cpow hs0, mul_zero]
    · rw [LSeries.term_of_ne_zero hn, eltSum, Finset.sum_div]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [normSq_σO_cast, mem_eltsN.1 hc, Complex.cpow_neg, div_eq_mul_inv]
  rw [e] at h
  exact h.tsum_eq

/-! ### The values of `A₀(n) = Σ_{N(d)=n} S₀(d)` -/

theorem eltSum_cuspS0_eq_zero_of_not_cube {n : ℕ} (h : ∀ k : ℕ, n ≠ k ^ 3) : eltSum cuspS0 n = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  by_cases hp : Primary d
  · refine cuspS0_eq_zero_of_not_cube hp ?_
    rintro ⟨m, -, rfl⟩
    apply h (absNorm (span {m}))
    rw [← mem_eltsN.1 hd, ← Ideal.span_singleton_pow, map_pow]
  · exact cuspS0_eq_zero_of_not_primary hp

/-- Primary elements with the same cube are equal. -/
theorem eq_of_cube_eq_primary {a b : 𝓞 K} (ha : Primary a) (hb : Primary b) (h : a ^ 3 = b ^ 3) :
    a = b := by
  rcases cube_eq_cube_iff.1 h with h | h | h
  · exact h
  · exact primary_unique ha hb (by rw [h, show ω * b = (ωu : 𝓞 K) * b from rfl, span_unit_mul])
  · exact primary_unique ha hb (by
      rw [h, show ω ^ 2 * b = ((ωu ^ 2 : (𝓞 K)ˣ) : 𝓞 K) * b by rw [Units.val_pow_eq_pow_val]; rfl,
        span_unit_mul])

open Classical in
/-- **`A₀` at the cubes**: `A₀(k³) = k³·Σ_{N(m)=k, m primary} Π_{P ∣ m}(1 − 1/N(P))`. -/
theorem eltSum_cuspS0_cube (k : ℕ) :
    eltSum cuspS0 (k ^ 3) = (k : ℂ) ^ 3 * ∑ m ∈ (eltsN k).filter Primary, totP (span {m}) := by
  set M := (eltsN k).filter Primary with hM
  have hinj : ∀ a ∈ M, ∀ b ∈ M, a ^ 3 = b ^ 3 → a = b := fun a ha b hb hab =>
    eq_of_cube_eq_primary (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 hab
  have e1 : eltSum cuspS0 (k ^ 3) = ∑ m ∈ M, cuspS0 (m ^ 3) := by
    calc eltSum cuspS0 (k ^ 3) = ∑ d ∈ M.image (fun m => m ^ 3), cuspS0 d := by
          refine (Finset.sum_subset ?_ ?_).symm
          · intro d hd
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hd
            rw [mem_eltsN, ← Ideal.span_singleton_pow, map_pow,
              mem_eltsN.1 (Finset.mem_filter.1 hm).1]
          · intro d hd hdn
            by_contra hS
            have hp : Primary d := by
              by_contra hp; exact hS (cuspS0_eq_zero_of_not_primary hp)
            obtain ⟨m, hm, rfl⟩ : ∃ m : 𝓞 K, Primary m ∧ d = m ^ 3 := by
              by_contra h; exact hS (cuspS0_eq_zero_of_not_cube hp h)
            apply hdn
            refine Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨mem_eltsN.2 ?_, hm⟩, rfl⟩
            have := mem_eltsN.1 hd
            rw [← Ideal.span_singleton_pow, map_pow] at this
            exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) this
      _ = ∑ m ∈ M, cuspS0 (m ^ 3) := Finset.sum_image hinj
  rw [e1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hmk, hp⟩ := Finset.mem_filter.1 hm
  rw [cuspS0_cube_eq hp, mem_eltsN.1 hmk]

open Classical in
/-- **One primary generator per ideal prime to `3`**: `Σ_{N(m)=k, m primary} h((m))` is `0` for `3 ∣ k`, and
`Σ_{N𝔞=k} h(𝔞)` otherwise. -/
theorem sum_primary_eltsN (k : ℕ) (h : Ideal (𝓞 K) → ℂ) :
    ∑ m ∈ (eltsN k).filter Primary, h (span {m}) = if 3 ∣ k then 0 else normSum h k := by
  split_ifs with h3
  · refine Finset.sum_eq_zero fun m hm => absurd h3 ?_
    obtain ⟨hmk, hp⟩ := Finset.mem_filter.1 hm
    have := absNorm_primary_mod hp
    rw [mem_eltsN.1 hmk] at this
    omega
  · have hcop : ∀ I ∈ ofNorm k, (absNorm I).Coprime 3 := fun I hI => by
      rw [mem_ofNorm.1 hI]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    rw [normSum]
    refine Finset.sum_nbij' (fun m => span {m}) pgen ?_ ?_ ?_ ?_ ?_
    · intro m hm
      exact mem_ofNorm.2 (mem_eltsN.1 (Finset.mem_filter.1 hm).1)
    · intro I hI
      obtain ⟨hp, hs⟩ := pgen_spec3 (hcop I hI)
      exact Finset.mem_filter.2 ⟨mem_eltsN.2 (by rw [hs]; exact mem_ofNorm.1 hI), hp⟩
    · intro m hm
      exact pgen_eq (Finset.mem_filter.1 hm).2
    · intro I hI
      exact (pgen_spec3 (hcop I hI)).2
    · intro m _
      rfl

open Classical in
/-- The weight with the ideals over `3` removed: `Σ_{N𝔞=k} Π_{P ∣ 𝔞}(1 − 1/N(P))` for `3 ∤ k`, else `0`. -/
def normSum3 (k : ℕ) : ℂ := if 3 ∣ k then 0 else normSum totP k

theorem eltSum_cuspS0_cube_eq (k : ℕ) : eltSum cuspS0 (k ^ 3) = (k : ℂ) ^ 3 * normSum3 k := by
  rw [eltSum_cuspS0_cube, sum_primary_eltsN, normSum3]

/-! ### The factor at `3` -/

/-- An element whose norm is divisible by `3` is divisible by `δ₃`. -/
theorem δ3_dvd_of_three_dvd {c : 𝓞 K} (h : 3 ∣ absNorm (span {c})) : δ3 ∣ c := by
  by_contra hδ
  have hlam : ¬ (ω - 1) ∣ c := by
    rintro ⟨t, rfl⟩
    exact hδ ⟨-ω ^ 2 * t, by unfold δ3; linear_combination t * ω_sq_add + 2 * t * ω_cube⟩
  obtain ⟨u, hu⟩ := exists_primary hlam
  have := absNorm_primary_mod hu
  rw [span_unit_mul] at this
  omega

open Classical in
/-- **The ideals of norm `3k`** are the `(δ₃)𝔟` with `N𝔟 = k`, and the weight does not see `(δ₃)`:
`Σ_{N𝔞=3k} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P)) = Σ_{N𝔞=k} Π_{P ∣ 𝔞, 3 ∉ P}(1 − 1/N(P))`. -/
theorem normSum_totP_three_mul (k : ℕ) : normSum totP (3 * k) = normSum totP k := by
  rcases eq_or_ne k 0 with rfl | hk
  · rfl
  have h3k : 3 * k ≠ 0 := by omega
  have hall : (eltsN (3 * k)).filter (δ3 ∣ ·) = eltsN (3 * k) :=
    Finset.filter_true_of_mem fun c hc =>
      δ3_dvd_of_three_dvd (by rw [mem_eltsN.1 hc]; exact dvd_mul_right 3 k)
  have h := sum_totP_filter h3k
  rw [hall, sum_eltsN h3k totP, ite_eq_left (dvd_mul_right 3 k), show 3 * k / 3 = k by omega] at h
  rw [normSum]
  linear_combination h / 6

theorem LSeriesSummable_normSum_totP {u : ℂ} (hu : 1 < u.re) : LSeriesSummable (normSum totP) u := by
  have hu1 : 1 < (u + 1).re := by simp; linarith
  have hsum : LSeriesSummable (fun a : ℕ => mu3 a / a) u := by
    have := LSeriesSummable_mu3 hu1
    unfold LSeriesSummable at this ⊢
    rwa [term_div_natCast]
  refine (LSeriesSummable_congr u fun hn => ?_).2 (hsum.convolution (LSeriesSummable_rK hu))
  rw [normSum_totP_eq_conv hn]
  rfl

theorem normSum3_eq_conv {n : ℕ} (hn : n ≠ 0) : normSum3 n = (normSum totP ⍟ eul3) n := by
  rw [LSeries.convolution_def]
  simp only
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => normSum totP a * eul3 b)]
  by_cases h3 : 3 ∣ n
  · rw [Finset.sum_eq_add 1 3 (by norm_num) ?_ ?_ ?_]
    · obtain ⟨m, rfl⟩ := h3
      rw [Nat.div_one, Nat.mul_div_cancel_left m (by norm_num), normSum_totP_three_mul]
      simp [eul3, normSum3]
    · intro c _ hc
      rw [eul3, ite_eq_right hc.1, ite_eq_right hc.2, mul_zero]
    · intro h; exact absurd (Nat.one_mem_divisors.2 hn) h
    · intro h; exact absurd (Nat.mem_divisors.2 ⟨h3, hn⟩) h
  · rw [Finset.sum_eq_single 1 ?_ ?_]
    · rw [Nat.div_one, eul3, ite_eq_left rfl, mul_one, normSum3, ite_eq_right h3]
    · intro c hc hc1
      have hc3 : c ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_divisors hc)
      rw [eul3, ite_eq_right hc1, ite_eq_right hc3, mul_zero]
    · intro h; exact absurd (Nat.one_mem_divisors.2 hn) h

/-- **The Euler factor at `3` removed**: `Σ_{3 ∤ k} (Σ_{N𝔞=k} ⋯)k^{−u} = (1 − 3^{−u})·Σ_k (Σ_{N𝔞=k} ⋯)k^{−u}`
for `Re u > 1`. -/
theorem LSeries_normSum3 {u : ℂ} (hu : 1 < u.re) :
    LSeries normSum3 u = (1 - 3 ^ (-u)) * LSeries (normSum totP) u := by
  rw [LSeries_congr (fun hn => normSum3_eq_conv hn) u,
    LSeries_convolution' (LSeriesSummable_normSum_totP hu) (LSeriesSummable_eul3 u), LSeries_eul3,
    mul_comm]

/-! ### The closed form -/

theorem term_eltSum_cuspS0_cube (s : ℂ) (k : ℕ) :
    LSeries.term (eltSum cuspS0) s (k ^ 3) = LSeries.term normSum3 (3 * s - 3) k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hn : k ^ 3 ≠ 0 := pow_ne_zero 3 hk
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hk, eltSum_cuspS0_cube_eq]
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have h1 : (((k ^ 3 : ℕ) : ℂ)) ^ s = ((k : ℕ) : ℂ) ^ (((3 : ℕ) : ℂ) * s) := by
    rw [Complex.natCast_cpow_natCast_mul, Nat.cast_pow]
  have ej : (k : ℂ) ^ (3 : ℂ) = (k : ℂ) ^ 3 := by
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have hJ := cpow_ne_zero_of_ne hk' (3 * s)
  rw [h1, Complex.cpow_sub _ _ hk', ej]
  push_cast
  field_simp

/-- **Reindexing onto the cubes**: `Σ_n A₀(n)n^{−s} = Σ_k A₀(k³)k^{−3s}`, as `L`-series (for every `s`). -/
theorem LSeries_eltSum_cuspS0 (s : ℂ) :
    LSeries (eltSum cuspS0) s = LSeries normSum3 (3 * s - 3) := by
  have hinj : Function.Injective (fun k : ℕ => k ^ 3) := Nat.pow_left_injective (by norm_num)
  have hsupp : Function.support (LSeries.term (eltSum cuspS0) s) ⊆ Set.range (fun k : ℕ => k ^ 3) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hn0 : n ≠ 0 := fun h => hn (by rw [h, LSeries.term_zero])
    by_contra hr
    apply hn
    rw [LSeries.term_of_ne_zero hn0,
      eltSum_cuspS0_eq_zero_of_not_cube (fun k hk => hr ⟨k, hk.symm⟩), zero_div]
  rw [LSeries, ← hinj.tsum_eq hsupp, LSeries]
  exact tsum_congr fun k => term_eltSum_cuspS0_cube s k

/-- `Σ_d S₀(d)N(d)^{−s}·(1 − 3^{2−3s})·ζ_K(3s − 2) = (1 − 3^{3−3s})·ζ_K(3s − 3)` for `Re s > 2`, with
`ζ_K = ζ·L(·, χ₋₃)`. -/
theorem tsum_cuspS0_mul {s : ℂ} (hs : 2 < s.re) :
    (∑' d : 𝓞 K, cuspS0 d * ((Complex.normSq (σO d) : ℝ) : ℂ) ^ (-s)) * ((1 - 3 ^ (2 - 3 * s)) *
      (riemannZeta (3 * s - 2) * LFunction PsiOmega.chi3 (3 * s - 2))) =
      (1 - 3 ^ (3 - 3 * s)) * (riemannZeta (3 * s - 3) * LFunction PsiOmega.chi3 (3 * s - 3)) := by
  have hu : 1 < (3 * s - 3).re := by simp; linarith
  have h := LSeries_normSum_totP_mul hu
  rw [show 3 * s - 3 + 1 = 3 * s - 2 by ring, show -(3 * s - 2) = 2 - 3 * s by ring] at h
  rw [← LSeries_eltSum norm_cuspS0_le hs, LSeries_eltSum_cuspS0, LSeries_normSum3 hu,
    show -(3 * s - 3) = 3 - 3 * s by ring]
  linear_combination (1 - 3 ^ (3 - 3 * s)) * h

/-- **The closed form of `φ₀`**:
`π/((9√3/2)(s − 1))·(1 − 3^{3−3s})·ζ_K(3s − 3)/((1 − 3^{2−3s})·ζ_K(3s − 2))`. -/
def phi0C (s : ℂ) : ℂ :=
  Real.pi / (((9 * (Real.sqrt 3 / 2) : ℝ) : ℂ) * (s - 1)) *
    ((1 - 3 ^ (3 - 3 * s)) * (riemannZeta (3 * s - 3) * LFunction PsiOmega.chi3 (3 * s - 3)) /
      ((1 - 3 ^ (2 - 3 * s)) * (riemannZeta (3 * s - 2) * LFunction PsiOmega.chi3 (3 * s - 2))))

/-- **Round 440's `φ₀` in closed form**: `φ₀(s) = π/((9√3/2)(s − 1))·(1 − 3^{3−3s})·ζ_K(3s − 3)/((1 −
3^{2−3s})·ζ_K(3s − 2))` for `Re s > 2`. -/
theorem eisPhi0_eq_phi0C {s : ℂ} (hs : 2 < s.re) : eisPhi0 s = phi0C s := by
  have hden := phiC_den_ne_zero (s := s) (by linarith)
  unfold eisPhi0 phi0C
  congr 1
  rw [eq_div_iff hden]
  exact tsum_cuspS0_mul hs

/-! ### The pole at `4/3` -/

/-- `φ₀ = φ·(1 − 3^{3−3s})/(2·3^{3−3s})`. -/
theorem phi0C_eq (s : ℂ) : phi0C s = phiC s * ((1 - 3 ^ (3 - 3 * s)) / (2 * 3 ^ (3 - 3 * s))) := by
  have h3 : (3 : ℂ) ^ (3 - 3 * s) ≠ 0 := cpow_ne_zero_of_ne (by norm_num) _
  unfold phi0C phiC
  field_simp

/-- **`φ₀` continues**: `phi0C` is complex-differentiable at every `s` with `Re s > 1` and `s ≠ 4/3`. -/
theorem differentiableAt_phi0C {s : ℂ} (hs : 1 < s.re) (h43 : s ≠ 4 / 3) :
    DifferentiableAt ℂ phi0C s := by
  have hc : DifferentiableAt ℂ (fun s : ℂ => (3 : ℂ) ^ (3 - 3 * s)) s :=
    ((differentiableAt_id.const_mul 3).const_sub 3).const_cpow (Or.inl (by norm_num))
  have hr : DifferentiableAt ℂ (fun s : ℂ => (1 - (3 : ℂ) ^ (3 - 3 * s)) / (2 * 3 ^ (3 - 3 * s))) s :=
    (hc.const_sub 1).div (hc.const_mul 2)
      (mul_ne_zero two_ne_zero (cpow_ne_zero_of_ne (by norm_num) _))
  have e : phi0C = fun s => phiC s * ((1 - (3 : ℂ) ^ (3 - 3 * s)) / (2 * 3 ^ (3 - 3 * s))) :=
    funext phi0C_eq
  rw [e]
  exact (differentiableAt_phiC hs h43).mul hr

/-- **The pole of `φ₀` at `4/3`**: `(s − 4/3)·φ₀(s) → phiG(4/3)/3`, round 417's residue of `φ`. -/
theorem tendsto_phi0C_residue :
    Tendsto (fun s : ℂ => (s - 4 / 3) * phi0C s) (𝓝[≠] (4 / 3)) (𝓝 (phiG (4 / 3) / 3)) := by
  have hc : ContinuousAt (fun s : ℂ => (3 : ℂ) ^ (3 - 3 * s)) (4 / 3) :=
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).const_cpow (Or.inl (by norm_num))
  have hr : ContinuousAt (fun s : ℂ => (1 - (3 : ℂ) ^ (3 - 3 * s)) / (2 * 3 ^ (3 - 3 * s))) (4 / 3) :=
    (continuousAt_const.sub hc).div (continuousAt_const.mul hc)
      (mul_ne_zero two_ne_zero (cpow_ne_zero_of_ne (by norm_num) _))
  have hr1 : (1 - (3 : ℂ) ^ (3 - 3 * (4 / 3 : ℂ))) / (2 * 3 ^ (3 - 3 * (4 / 3 : ℂ))) = 1 := by
    rw [show (3 : ℂ) - 3 * (4 / 3) = -1 by norm_num, Complex.cpow_neg_one]
    norm_num
  have h := tendsto_phiC_residue.mul (hr.tendsto.mono_left nhdsWithin_le_nhds)
  rw [hr1, mul_one] at h
  refine h.congr fun s => ?_
  rw [phi0C_eq]
  ring

end Eis

end

#print axioms Eis.bRow_iff_fst
#print axioms Eis.count_three_mem
#print axioms Eis.count_bRow_fst
#print axioms Eis.cuspS0_cube_eq
#print axioms Eis.cuspS0_eq_zero_of_not_primary
#print axioms Eis.norm_cuspS0_le
#print axioms Eis.summable_mul_normSq_cpow
#print axioms Eis.LSeries_eltSum
#print axioms Eis.eltSum_cuspS0_eq_zero_of_not_cube
#print axioms Eis.eq_of_cube_eq_primary
#print axioms Eis.eltSum_cuspS0_cube
#print axioms Eis.sum_primary_eltsN
#print axioms Eis.eltSum_cuspS0_cube_eq
#print axioms Eis.δ3_dvd_of_three_dvd
#print axioms Eis.normSum_totP_three_mul
#print axioms Eis.LSeriesSummable_normSum_totP
#print axioms Eis.normSum3_eq_conv
#print axioms Eis.LSeries_normSum3
#print axioms Eis.term_eltSum_cuspS0_cube
#print axioms Eis.LSeries_eltSum_cuspS0
#print axioms Eis.tsum_cuspS0_mul
#print axioms Eis.eisPhi0_eq_phi0C
#print axioms Eis.phi0C_eq
#print axioms Eis.differentiableAt_phi0C
#print axioms Eis.tendsto_phi0C_residue
