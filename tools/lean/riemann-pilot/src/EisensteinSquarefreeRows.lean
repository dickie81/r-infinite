import EisensteinTransferEstimate

/-! # Proposition 5.2 from the squarefree rows (round 339)

S5d of round 312's plan, part 1: the companion paper's proof of its Proposition 5.2 (the completed mean
square) from its Lemma 6.6 (the squarefree rows), with Lemma 6.6 displayed as a hypothesis.

* **`compT_mul_sq`**: `T(X; s m², f) = T(X; s, f m²)`, the paper's `T(X;u₀sv²,f) = T(X;u₀s,fv²)`. On the ideals
  of norm prime to `6`, `(m/𝔫)₆⁶` is `0` or `1` (`sym6_pow_six`), so `(m/𝔫)₆² = (m/𝔫)₆⁸`
  (`sym6_sq_eq_pow_eight`).
* **`exists_sq_mul_sqfree`**: every nonzero `k` is `d·e²` with `(d)` squarefree and `e` the chosen generator of
  an ideal `𝔈` (Mathlib's `exists_sq_mul_squarefree` in the ideals of `ℤ[ω]`).
* **`sum_idealsLe_inv_sq_le`**: `Σ_{N𝔞 ≤ x} 1/N𝔞² ≤ 4(2κ+5)`, by dyadic shells; the paper's `ζ_K(2)`.
* **`SquarefreeCompleted`**: the paper's Lemma 6.6, displayed, for any auxiliary twist `g ≠ 0`.
* **`completedMeanSquare_of_squarefree`**: `SquarefreeCompleted → CompletedMeanSquare`, and with round 326,
  **`ne_zero_of_squarefree`**: `SquarefreeCompleted → 11/12 < Re s → ζ(s) ≠ 0 ∧ L(s, χ₋₃) ≠ 0`.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### A square in the row moves to the auxiliary twist -/

/-- `(m/𝔫)₆² = (m/𝔫)₆⁸` for `𝔫` of norm prime to `6`: the sixth power is `0` or `1`. -/
theorem sym6_sq_eq_pow_eight {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (m : 𝓞 K) :
    sym6 m I ^ 2 = sym6 m I ^ 8 := by
  have h6 : sym6 m I ^ 6 = 0 ∨ sym6 m I ^ 6 = 1 := by
    have := sym6_pow_six hI m
    rw [show m ^ 6 = m ^ (5 + 1) from rfl, sym6_pow_succ] at this
    split_ifs at this
    · exact Or.inr this
    · exact Or.inl this
  rcases h6 with h | h
  · have h0 : sym6 m I = 0 := (pow_eq_zero_iff (by norm_num)).1 h
    rw [h0]; norm_num
  · calc sym6 m I ^ 2 = sym6 m I ^ 2 * sym6 m I ^ 6 := by rw [h, mul_one]
      _ = sym6 m I ^ 8 := by ring

section Squares

variable (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)

/-- `Ψ_{s m², f} = Ψ_{s, f m²}`, since `(m/𝔫)₆² = (m/𝔫)₆⁸`. -/
theorem twistPsi_mul_sq (s m f : 𝓞 K) (I : Ideal (𝓞 K)) :
    twistPsi ξ (s * m ^ 2) f I = twistPsi ξ s (f * m ^ 2) I := by
  unfold twistPsi
  split_ifs with hI
  · simp only [pow_two m, sym6_mul_left]
    linear_combination (ξ (Ideal.Quotient.mk _ (pgen I)) * sym6 s I * sym6 f I ^ 4) *
      sym6_sq_eq_pow_eight hI m
  · rfl

theorem gCoef_mul_sq (s m f : 𝓞 K) (I : Ideal (𝓞 K)) :
    gCoef ξ (s * m ^ 2) f I = gCoef ξ s (f * m ^ 2) I := by
  unfold gCoef; rw [twistPsi_mul_sq]

theorem dCoef_mul_sq (s m f : 𝓞 K) (J : Ideal (𝓞 K)) :
    dCoef ξ (s * m ^ 2) f J = dCoef ξ s (f * m ^ 2) J := by
  unfold dCoef; rw [twistPsi_mul_sq]

/-- **`T(X; s m², f) = T(X; s, f m²)`** (the paper's `T(X;u₀sv²,f) = T(X;u₀s,fv²)`). -/
theorem compT_mul_sq (s m f : 𝓞 K) (W : ℝ → ℂ) (X : ℝ) :
    compT ξ (s * m ^ 2) f W X = compT ξ s (f * m ^ 2) W X := by
  unfold compT
  simp only [gCoef_mul_sq, dCoef_mul_sq]

end Squares

/-! ### The squarefree part of a row -/

/-- Every nonzero `k` is `d·e²` with `(d)` squarefree and `e` the chosen generator of an ideal `𝔈`. -/
theorem exists_sq_mul_sqfree {k : 𝓞 K} (hk : k ≠ 0) :
    ∃ E : Ideal (𝓞 K), ∃ d : 𝓞 K, k = d * gen E ^ 2 ∧ Squarefree (span {d}) ∧ E ≠ ⊥ ∧
      span {k} = span {d} * E ^ 2 := by
  obtain ⟨E, Dd, hED, hsq⟩ := exists_sq_mul_squarefree (span {k})
  have hk0 : span {k} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hE : E ≠ ⊥ := by
    rintro rfl
    rw [← hED] at hk0
    simp at hk0
  have hdvd : gen E ^ 2 ∣ k := by
    rw [← Ideal.span_singleton_dvd_span_singleton_iff_dvd, ← Ideal.span_singleton_pow, span_gen,
      ← hED]
    exact dvd_mul_right _ _
  obtain ⟨d, hd⟩ := hdvd
  have hspan : span {k} = E ^ 2 * span {d} := by
    rw [hd, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, span_gen]
  have hDd : Dd = span {d} := by
    have h2 : E ^ 2 ≠ 0 := pow_ne_zero 2 hE
    exact mul_left_cancel₀ h2 (hED.trans hspan)
  refine ⟨E, d, by rw [hd, mul_comm], hDd ▸ hsq, hE, by rw [hspan, mul_comm]⟩

/-! ### The inverse-square sum over ideals -/

open Classical in
/-- **`Σ_{N𝔞 ≤ x} 1/N𝔞² ≤ 4(2κ+5)`**, by dyadic shells as in `sum_idealsLe_inv_le`. -/
theorem sum_idealsLe_inv_sq_le (x : ℝ) :
    ∑ I ∈ idealsLe x, 1 / (absNorm I : ℝ) ^ 2 ≤ 4 * (2 * kappa + 5) := by
  set L := Nat.log 2 ⌊x⌋₊
  set lv : Ideal (𝓞 K) → ℕ := fun I => Nat.log 2 (absNorm I) with hlv
  have hmaps : ∀ I ∈ idealsLe x, lv I ∈ Finset.range (L + 1) := by
    intro I hI
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (mem_idealsLe.1 hI).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hk := kappa_pos
  calc ∑ j ∈ Finset.range (L + 1), ∑ I ∈ idealsLe x with lv I = j, 1 / (absNorm I : ℝ) ^ 2
      ≤ ∑ j ∈ Finset.range (L + 1), 2 * (2 * kappa + 5) * (1 / 2 : ℝ) ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hsub : (idealsLe x).filter (fun I => lv I = j) ⊆ idealsLe ((2 : ℝ) ^ (j + 1)) := by
          intro I hI
          rw [Finset.mem_filter] at hI
          rw [mem_idealsLe]
          have h0 := (mem_idealsLe.1 hI.1).1
          have h1 : absNorm I < 2 ^ (j + 1) := by
            rw [← hI.2]; exact Nat.lt_pow_succ_log_self (by norm_num) _
          have hf : ⌊(2 : ℝ) ^ (j + 1)⌋₊ = 2 ^ (j + 1) := by
            rw [show (2 : ℝ) ^ (j + 1) = ((2 ^ (j + 1) : ℕ) : ℝ) by push_cast; ring,
              Nat.floor_natCast]
          rw [hf]; exact ⟨h0, h1.le⟩
        have hterm : ∀ I ∈ (idealsLe x).filter (fun I => lv I = j),
            1 / (absNorm I : ℝ) ^ 2 ≤ 1 / ((2 : ℝ) ^ j) ^ 2 := by
          intro I hI
          rw [Finset.mem_filter] at hI
          have h0 := (mem_idealsLe.1 hI.1).1
          have h1 : 2 ^ j ≤ absNorm I := by
            rw [← hI.2]; exact Nat.pow_log_le_self 2 h0.ne'
          have h1' : (2 : ℝ) ^ j ≤ absNorm I := by exact_mod_cast h1
          exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) h1' 2)
        calc ∑ I ∈ idealsLe x with lv I = j, 1 / (absNorm I : ℝ) ^ 2
            ≤ ∑ _I ∈ (idealsLe x).filter (fun I => lv I = j), 1 / ((2 : ℝ) ^ j) ^ 2 :=
              Finset.sum_le_sum hterm
          _ = ((idealsLe x).filter (fun I => lv I = j)).card * (1 / ((2 : ℝ) ^ j) ^ 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((2 * kappa + 5) * (2 : ℝ) ^ (j + 1)) * (1 / ((2 : ℝ) ^ j) ^ 2) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (((idealsLe x).filter (fun I => lv I = j)).card : ℝ)
                  ≤ (idealsLe ((2 : ℝ) ^ (j + 1))).card := by
                    exact_mod_cast Finset.card_le_card hsub
                _ = idealCount ((2 : ℝ) ^ (j + 1)) := by rw [card_idealsLe]
                _ ≤ _ := idealCount_le (one_le_pow₀ (by norm_num))
          _ = 2 * (2 * kappa + 5) * (1 / 2 : ℝ) ^ j := by
              have h2 : (0 : ℝ) < 2 ^ j := by positivity
              rw [one_div_pow, pow_succ]
              field_simp
    _ = 2 * (2 * kappa + 5) * ∑ j ∈ Finset.range (L + 1), (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (2 * kappa + 5) * 2 := by
        gcongr
        exact sum_geometric_two_le _
    _ = 4 * (2 * kappa + 5) := by ring

/-! ### Lemma 6.6, displayed, and Proposition 5.2 from it -/

/-- **The squarefree rows** (the companion paper's Lemma 6.6), displayed as a hypothesis: for every
`ε > 0` and `C₀ ≥ 1` there is a derivative order `J` such that, for every interval `[α, β] ⊂ (0, ∞)`,
uniformly in `ξ` and the smooth weight `W` supported in `[α, β]` with its first `J` derivatives bounded
by `N`, the scales `1 ≤ 𝓗, X ≤ D^{C₀}` and the auxiliary twist `g ≠ 0` with `N(g) ≤ D^{C₀}`, every finite
set of nonzero `s` with `(s)` squarefree and `N(s) ≤ 𝓗` satisfies
`Σ_s |T(X; s, g)|² ≤ K·N²·D^ε·(𝓗 + 𝓗²N(g)/X)`. The paper sums over one unit `u₀` times the chosen
generators of the squarefree ideals; each `s` here is such a product for exactly one `u₀`, so the
paper's lemma gives this one with `6K` in place of `K`. -/
def SquarefreeCompleted : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ J : ℕ, ∀ α β : ℝ, 0 < α → ∃ Kc : ℝ,
    ∀ ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W →
      (∀ x, x < α ∨ β < x → W x = 0) → ∀ N : ℝ, (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W x‖ ≤ N) →
      ∀ D Hh X : ℝ, 1 ≤ D → 1 ≤ Hh → 1 ≤ X → Hh ≤ D ^ C₀ → X ≤ D ^ C₀ →
      ∀ g : 𝓞 K, g ≠ 0 → (absNorm (span {g}) : ℝ) ≤ D ^ C₀ →
      ∀ Ss : Finset (𝓞 K),
        (∀ s ∈ Ss, s ≠ 0 ∧ Squarefree (span {s}) ∧ (absNorm (span {s}) : ℝ) ≤ Hh) →
        ∑ s ∈ Ss, ‖compT ξ s g W X‖ ^ 2 ≤
          Kc * N ^ 2 * D ^ ε * (Hh + Hh ^ 2 * (absNorm (span {g}) : ℝ) / X)

/-- **Proposition 5.2 from Lemma 6.6** (the companion paper's proof of Proposition 5.2): write each row
as `k = s·e²` with `(s)` squarefree and `e` the chosen generator of `𝔈`, so that
`T(X; k, f) = T(X; s, f e²)` (`compT_mul_sq`); apply Lemma 6.6 to the rows with the same `𝔈`, at the
row bound `𝓗/N𝔈²` and the twist `f e²` of norm at most `D^{2C₀}`; and sum `1/N𝔈² ≤ 4(2κ+5)`
(`sum_idealsLe_inv_sq_le`; the paper's `ζ_K(2)`). -/
theorem completedMeanSquare_of_squarefree (h : SquarefreeCompleted) : CompletedMeanSquare := by
  intro ε hε C₀ hC₀
  obtain ⟨J, hJ⟩ := h ε hε (2 * C₀) (by linarith)
  refine ⟨J, fun α β hα => ?_⟩
  obtain ⟨Kc, hK⟩ := hJ α β hα
  refine ⟨max Kc 0 * (4 * (2 * kappa + 5)), fun ξ W hW hsupp N hN D Hh X hD hH hX hHD hXD f hf6
    hfsq hfD T hT => ?_⟩
  classical
  have hD0 : 0 < D := by linarith
  have hDC : D ^ C₀ ≤ D ^ (2 * C₀) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hDDC : D ^ C₀ * D ^ C₀ = D ^ (2 * C₀) := by
    rw [← Real.rpow_add hD0]; ring_nf
  -- the decomposition of each row
  have hdec : ∀ k ∈ T, ∃ E : Ideal (𝓞 K), ∃ d : 𝓞 K, k = d * gen E ^ 2 ∧
      Squarefree (span {d}) ∧ E ≠ ⊥ ∧ span {k} = span {d} * E ^ 2 :=
    fun k hk => exists_sq_mul_sqfree (hT k hk).1
  choose! E d hEd using hdec
  set fg := pgen f with hfg
  have hfspan : span {fg} = f := (pgen_spec6 hf6).2
  have hf0 : fg ≠ 0 := by
    intro h0
    have : f = ⊥ := by rw [← hfspan, h0, Ideal.span_singleton_eq_bot.2 rfl]
    exact ne_bot_of_coprime6 hf6 this
  have hk0 : ∀ k ∈ T, k ≠ 0 := fun k hk => (hT k hk).1
  -- norms
  have hnorm : ∀ k ∈ T, (absNorm (span {k}) : ℝ) =
      (absNorm (span {d k}) : ℝ) * (absNorm (E k) : ℝ) ^ 2 := by
    intro k hk
    rw [(hEd k hk).2.2.2, map_mul, map_pow]; push_cast; ring
  have hd0 : ∀ k ∈ T, d k ≠ 0 := by
    intro k hk h0
    apply hk0 k hk
    rw [(hEd k hk).1, h0, zero_mul]
  have hE1 : ∀ k ∈ T, (1 : ℝ) ≤ absNorm (E k) := by
    intro k hk
    have : absNorm (E k) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (hEd k hk).2.2.1
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hEH : ∀ k ∈ T, (absNorm (E k) : ℝ) ^ 2 ≤ Hh := by
    intro k hk
    have h1 := one_le_absNorm_span (hd0 k hk)
    have h2 := (hT k hk).2
    rw [hnorm k hk] at h2
    have h3 : (0 : ℝ) ≤ (absNorm (E k) : ℝ) ^ 2 := by positivity
    nlinarith
  -- rewrite each row through its squarefree part
  have hrow : ∀ k ∈ T, compT ξ k fg W X = compT ξ (d k) (fg * gen (E k) ^ 2) W X := by
    intro k hk
    rw [← compT_mul_sq, ← (hEd k hk).1]
  rw [Finset.sum_congr rfl fun k hk => by rw [hrow k hk]]
  -- group the rows by `𝔈`
  have hmaps : ∀ k ∈ T, E k ∈ T.image E := fun k hk => Finset.mem_image_of_mem E hk
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set B := N ^ 2 * D ^ ε * (Hh + Hh ^ 2 * (absNorm f : ℝ) / X) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Hh ^ 2 * (absNorm f : ℝ) / X := by positivity
    have : 0 ≤ D ^ ε := by positivity
    positivity
  have hfib : ∀ E₀ ∈ T.image E,
      ∑ k ∈ T with E k = E₀, ‖compT ξ (d k) (fg * gen (E k) ^ 2) W X‖ ^ 2 ≤
        max Kc 0 * B * (1 / (absNorm E₀ : ℝ) ^ 2) := by
    intro E₀ hE₀
    obtain ⟨k₁, hk₁, rfl⟩ := Finset.mem_image.1 hE₀
    set g₀ := fg * gen (E k₁) ^ 2 with hg₀
    set nE := (absNorm (E k₁) : ℝ) with hnE
    have hnE1 : 1 ≤ nE := hE1 k₁ hk₁
    have hnE0 : 0 < nE := by linarith
    -- the fiber as a sum over the squarefree parts
    have hcongr : ∀ k ∈ T.filter (fun k => E k = E k₁),
        ‖compT ξ (d k) (fg * gen (E k) ^ 2) W X‖ ^ 2 = ‖compT ξ (d k) g₀ W X‖ ^ 2 := by
      intro k hk
      rw [(Finset.mem_filter.1 hk).2]
    rw [Finset.sum_congr rfl hcongr]
    have hinj : Set.InjOn d (T.filter (fun k => E k = E k₁)) := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.1 ha
      have hb' := Finset.mem_filter.1 hb
      rw [(hEd a ha'.1).1, (hEd b hb'.1).1, hab, ha'.2, hb'.2]
    rw [← Finset.sum_image (f := fun s => ‖compT ξ s g₀ W X‖ ^ 2) hinj]
    -- Lemma 6.6 at the row bound `𝓗/N𝔈²` and the twist `f e²`
    set Hh' := Hh / nE ^ 2 with hHh'
    have hH'1 : 1 ≤ Hh' := by
      rw [hHh', le_div_iff₀ (by positivity), one_mul]; exact hEH k₁ hk₁
    have hH'le : Hh' ≤ Hh := div_le_self (by linarith) (one_le_pow₀ hnE1)
    have hg0 : g₀ ≠ 0 := mul_ne_zero hf0 (pow_ne_zero 2 (fun h0 => (hEd k₁ hk₁).2.2.1 (by
      rw [← span_gen (E k₁), h0, Ideal.span_singleton_eq_bot.2 rfl])))
    have hng : (absNorm (span {g₀}) : ℝ) = (absNorm f : ℝ) * nE ^ 2 := by
      rw [hg₀, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, span_gen,
        hfspan, map_mul, map_pow]; push_cast; ring
    have hngD : (absNorm (span {g₀}) : ℝ) ≤ D ^ (2 * C₀) := by
      rw [hng, ← hDDC]
      exact mul_le_mul hfD ((hEH k₁ hk₁).trans hHD) (by positivity) (by positivity)
    have hSs : ∀ s ∈ (T.filter (fun k => E k = E k₁)).image d,
        s ≠ 0 ∧ Squarefree (span {s}) ∧ (absNorm (span {s}) : ℝ) ≤ Hh' := by
      intro s hs
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hs
      have hk' := Finset.mem_filter.1 hk
      refine ⟨hd0 k hk'.1, (hEd k hk'.1).2.1, ?_⟩
      rw [hHh', le_div_iff₀ (by positivity)]
      have h2 := (hT k hk'.1).2
      rw [hnorm k hk'.1, hk'.2] at h2
      exact h2
    have hbound := hK ξ W hW hsupp N hN D Hh' X hD hH'1 hX (hH'le.trans (hHD.trans hDC))
      (hXD.trans hDC) g₀ hg0 hngD _ hSs
    refine hbound.trans ?_
    have hval : Hh' + Hh' ^ 2 * (absNorm (span {g₀}) : ℝ) / X =
        (Hh + Hh ^ 2 * (absNorm f : ℝ) / X) * (1 / nE ^ 2) := by
      rw [hng, hHh']; field_simp
    rw [hval, hB]
    have hS0 : 0 ≤ N ^ 2 * D ^ ε * ((Hh + Hh ^ 2 * (absNorm f : ℝ) / X) * (1 / nE ^ 2)) := by
      have : 0 ≤ Hh ^ 2 * (absNorm f : ℝ) / X := by positivity
      have : 0 ≤ D ^ ε := by positivity
      positivity
    calc Kc * N ^ 2 * D ^ ε * ((Hh + Hh ^ 2 * (absNorm f : ℝ) / X) * (1 / nE ^ 2))
        = Kc * (N ^ 2 * D ^ ε * ((Hh + Hh ^ 2 * (absNorm f : ℝ) / X) * (1 / nE ^ 2))) := by ring
      _ ≤ max Kc 0 * (N ^ 2 * D ^ ε * ((Hh + Hh ^ 2 * (absNorm f : ℝ) / X) * (1 / nE ^ 2))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
      _ = max Kc 0 * (N ^ 2 * D ^ ε * (Hh + Hh ^ 2 * (absNorm f : ℝ) / X)) * (1 / nE ^ 2) := by
          ring
  -- sum over `𝔈`
  have hsub : T.image E ⊆ idealsLe Hh := by
    intro E₀ hE₀
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hE₀
    refine mem_idealsLe_of (hE1 k hk) ?_
    have := hEH k hk
    have h1 := hE1 k hk
    nlinarith
  calc ∑ E₀ ∈ T.image E, ∑ k ∈ T with E k = E₀, ‖compT ξ (d k) (fg * gen (E k) ^ 2) W X‖ ^ 2
      ≤ ∑ E₀ ∈ T.image E, max Kc 0 * B * (1 / (absNorm E₀ : ℝ) ^ 2) := Finset.sum_le_sum hfib
    _ = max Kc 0 * B * ∑ E₀ ∈ T.image E, 1 / (absNorm E₀ : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ max Kc 0 * B * ∑ E₀ ∈ idealsLe Hh, 1 / (absNorm E₀ : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ => by positivity) (mul_nonneg (le_max_right _ _) hB0)
    _ ≤ max Kc 0 * B * (4 * (2 * kappa + 5)) :=
        mul_le_mul_of_nonneg_left (sum_idealsLe_inv_sq_le Hh) (mul_nonneg (le_max_right _ _) hB0)
    _ = max Kc 0 * (4 * (2 * kappa + 5)) * N ^ 2 * D ^ ε *
          (Hh + Hh ^ 2 * (absNorm f : ℝ) / X) := by rw [hB]; ring

/-- **The third conditional milestone with Lemma 6.6 displayed**:
`SquarefreeCompleted → 11/12 < Re s → ζ(s) ≠ 0 ∧ L(s, χ₋₃) ≠ 0`. -/
theorem ne_zero_of_squarefree (h : SquarefreeCompleted) {s : ℂ} (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_completed (completedMeanSquare_of_squarefree h) hs

end Eis

end

#print axioms Eis.compT_mul_sq
#print axioms Eis.sum_idealsLe_inv_sq_le
#print axioms Eis.completedMeanSquare_of_squarefree
#print axioms Eis.ne_zero_of_squarefree
