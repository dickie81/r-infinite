/-
# Round 593: the Type II estimate of the sieve route at small heights (Proposition 3′, pointwise in the heights)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`typeII_step`). Let `L = 2333/1000`, `f0` smooth and real with support in `[1/2, 2]`, `K₀ ≥ 0`,
`e₁ > 0` and `0 < η ≤ 10⁻⁵`. For every large `q`, every `P` with `q^{(401/1000)L} ≤ P ≤ q^{(485/1000)L}`, every
`S ⊆ (P, 2P]`, `a_m` and `h₀`, every `K ≤ K₀`, and every `Q_j ≥ q^{e₁}` and `|h_j| ≤ q^η` (`j < K`) with
`∏_j Q_j ≤ 2^{K₀}q^L/P`:
`Σ_{χ≠1} |Σ_{m∈S} a_mχ(m)m^{−ih₀}||∏_{j<K} Σ_{p≤2Q_j} χ(p)(p/Q_j)^{−ih_j}f0(p/Q_j)|` is at most
`q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2}`.

This is `frontier/linnik/SIEVE-ROUTE.md` §10's Proposition 3′ for the curve step of §12, on the window
`[401/1000, 485/1000]` inside step's proved window, pointwise in the heights. The bins of the characters do not depend
on the heights. In each bin Lemma 1 (`SieveWeight.norm_Sp_le`) bounds the prime sums, (H2′) counts the characters
(`LinnikTwelve.charDensity_twelve_fifths`, `LinnikStep.charDensity_step`, and at most `q` characters), and
Cauchy–Schwarz with orthogonality (T1) bounds the sum.

* `card_class_le`, `sum_chars_dp_sq_le`: (T1), `Σ_χ |Σ_{j∈S} c_jχ(j)j^{−it}|² ≤ (P + q)Σ_{j∈S} |c_j|²` for
  `S ⊆ (P, 2P]` (`LinnikHybrid.sum_chars_norm_sq_le` with `dp_twist_eq`, and Cauchy–Schwarz in each class).
* `sum_bins_le`: if `|B(a)| ≤ M_i` on the bin `i` of a partition of `s`, then
  `Σ_{a∈s} |W(a)||B(a)| ≤ Σ_i M_i(#bin i)^{1/2}(Σ_{a∈s} |W(a)|²)^{1/2}`.
* `bin`, `bin_rect`, `card_bin_le`, `sum_typeII_bins`: the bin of `χ` is the largest `i` with a zero in
  `Re s > β_i`, `|Im s| ≤ T`; above it lies the zero-free rectangle of Lemma 1, and in it a zero counted by (H2′).
* `typeII_pointwise`: the bound by bins, with Lemma 1 and (T1).
* `card_zero_step`: the counts of the curve step, `C(qT)^{g(σ)}(1 + log qT)^{10}`.
* `MB_le`: for all large `q`, Lemma 1's bound is at most `2Q^{θ+2δ}`.
* `exponent_le`: the exponents on the window, at most `L − 1/25000`. Before the width they lie at least `5.5·10⁻⁵`
  below `L` and `1.5·10⁻⁵` below `L − 1/25000`, least at `β = 11/12`.
* `qpow_combine`, `bin_bound`, `prod_MB_le`, `card_bin_step`: one bin.
* `typeII_step`: the sum over the 500000 bins of width `1/1200000`.
-/
import LinnikStep
import SieveWeight

open Complex Finset

noncomputable section

namespace SieveTypeII

open DirMean LinnikHybrid DirichletCharacter

/-! ### Orthogonality (T1) -/

/-- **A residue class in `(P, 2P]`**: at most `P/q + 1` elements. The map `j ↦ ⌊(j − P − 1)/q⌋` is injective on
the class and takes values in `[0, P/q]`. -/
lemma card_class_le {P q : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ZMod q) :
    ((S.filter fun j : ℕ => (j : ZMod q) = a).card : ℝ) ≤ P / q + 1 := by
  have hmaps : Set.MapsTo (fun j => (j - (P + 1)) / q) (S.filter fun j : ℕ => (j : ZMod q) = a)
      (Finset.range (P / q + 1)) := by
    intro j hj
    have hjS := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 (hS hjS)
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun j => (j - (P + 1)) / q) (S.filter fun j : ℕ => (j : ZMod q) = a) := by
    intro j hj j' hj' hjj'
    have hj1 := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
    have hj1' := Finset.mem_filter.1 (Finset.mem_coe.1 hj')
    have hlo := (Finset.mem_Ioc.1 (hS hj1.1)).1
    have hlo' := (Finset.mem_Ioc.1 (hS hj1'.1)).1
    have hmod : j % q = j' % q := by
      have h : ((j : ℕ) : ZMod q) = ((j' : ℕ) : ZMod q) := hj1.2.trans hj1'.2.symm
      exact (ZMod.natCast_eq_natCast_iff' j j' q).1 h
    have hmod' : (j - (P + 1)) % q = (j' - (P + 1)) % q := by
      have e1 : j = (j - (P + 1)) + (P + 1) := by omega
      have e2 : j' = (j' - (P + 1)) + (P + 1) := by omega
      have h : (j - (P + 1)) + (P + 1) ≡ (j' - (P + 1)) + (P + 1) [MOD q] := by
        rw [← e1, ← e2]; exact hmod
      exact Nat.ModEq.add_right_cancel' (P + 1) h
    have hdiv : (j - (P + 1)) / q = (j' - (P + 1)) / q := hjj'
    have e : j - (P + 1) = j' - (P + 1) := by
      rw [← Nat.div_add_mod (j - (P + 1)) q, ← Nat.div_add_mod (j' - (P + 1)) q, hdiv, hmod']
    omega
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hc
  calc ((S.filter fun j : ℕ => (j : ZMod q) = a).card : ℝ) ≤ ((P / q + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ((P / q : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ P / q + 1 := by gcongr; exact Nat.cast_div_le

/-- **Orthogonality (T1)**: `Σ_χ |Σ_{j∈S} c_jχ(j)j^{−it}|² ≤ (P + q)Σ_{j∈S} |c_j|²` for `S ⊆ (P, 2P]`. The sum
over `χ` is at most `φ(q)Σ_a |D_a|²` over the classes `a` mod `q` (`sum_chars_norm_sq_le`, `dp_twist_eq`), and
`|D_a|² ≤ (P/q + 1)Σ_{j≡a} |c_j|²` by Cauchy–Schwarz (`card_class_le`). -/
theorem sum_chars_dp_sq_le {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] (t : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2 ≤ (P + q) * ∑ j ∈ S, ‖c j‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set Sa : ZMod q → Finset ℕ := fun a => S.filter (fun j : ℕ => (j : ZMod q) = a) with hSa
  have h1 : ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2 ≤
      q.totient * ∑ a, ‖dp (Sa a) c t‖ ^ 2 := by
    have e : ∀ χ : DirichletCharacter ℂ q, dp S (fun j => c j * χ j) t = ∑ a, χ a * dp (Sa a) c t :=
      fun χ => dp_twist_eq q S c χ t
    simp_rw [e]
    exact sum_chars_norm_sq_le q (fun a => dp (Sa a) c t)
  have h2 : ∀ a, ‖dp (Sa a) c t‖ ^ 2 ≤ (P / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
    intro a
    have hn : ‖dp (Sa a) c t‖ ≤ ∑ j ∈ Sa a, ‖c j‖ := by
      unfold dp
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [norm_mul, norm_exp_neg_I_mul, mul_one]
    have hcs : (∑ j ∈ Sa a, ‖c j‖) ^ 2 ≤ (Sa a).card * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    have hcard := card_class_le (q := q) hS a
    calc ‖dp (Sa a) c t‖ ^ 2 ≤ (∑ j ∈ Sa a, ‖c j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (Sa a).card * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := hcs
      _ ≤ (P / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
          gcongr
  have hfib : ∑ a : ZMod q, ∑ j ∈ Sa a, ‖c j‖ ^ 2 = ∑ j ∈ S, ‖c j‖ ^ 2 :=
    Finset.sum_fiberwise S (fun j => (j : ZMod q)) fun j => ‖c j‖ ^ 2
  have htot : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hS0 : 0 ≤ ∑ j ∈ S, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  calc ∑ χ : DirichletCharacter ℂ q, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ q.totient * ∑ a, ‖dp (Sa a) c t‖ ^ 2 := h1
    _ ≤ q.totient * ∑ a, (P / q + 1) * ∑ j ∈ Sa a, ‖c j‖ ^ 2 := by
        gcongr with a; exact h2 a
    _ = q.totient * (P / q + 1) * ∑ j ∈ S, ‖c j‖ ^ 2 := by rw [← Finset.mul_sum, hfib]; ring
    _ ≤ q * (P / q + 1) * ∑ j ∈ S, ‖c j‖ ^ 2 := by gcongr
    _ = (P + q) * ∑ j ∈ S, ‖c j‖ ^ 2 := by field_simp

/-! ### Bins -/

/-- `Σ_{a∈T} x_a ≤ (#T)^{1/2}(Σ_{a∈T} x_a²)^{1/2}` (Cauchy–Schwarz). -/
lemma sum_le_sqrt_card_mul_sqrt {α : Type*} (T : Finset α) (x : α → ℝ) :
    ∑ a ∈ T, x a ≤ Real.sqrt T.card * Real.sqrt (∑ a ∈ T, x a ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  have h := sq_sum_le_card_mul_sum_sq (s := T) (f := x)
  calc ∑ a ∈ T, x a ≤ |∑ a ∈ T, x a| := le_abs_self _
    _ = Real.sqrt ((∑ a ∈ T, x a) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (T.card * ∑ a ∈ T, x a ^ 2) := Real.sqrt_le_sqrt h

/-- **Bins.** Let `ι` send `s` into `I`, and `|B(a)| ≤ M(ι a)` on `s`. Then
`Σ_{a∈s} |W(a)||B(a)| ≤ Σ_{i∈I} M_i(#{a ∈ s : ι a = i})^{1/2}(Σ_{a∈s} |W(a)|²)^{1/2}`. -/
theorem sum_bins_le {α β : Type*} [DecidableEq β] (s : Finset α) (I : Finset β) (ι : α → β)
    (hι : ∀ a ∈ s, ι a ∈ I) (W B : α → ℂ) (M : β → ℝ) (hB : ∀ a ∈ s, ‖B a‖ ≤ M (ι a)) :
    ∑ a ∈ s, ‖W a‖ * ‖B a‖ ≤
      ∑ i ∈ I, M i * Real.sqrt (s.filter fun a => ι a = i).card * Real.sqrt (∑ a ∈ s, ‖W a‖ ^ 2) := by
  rw [← Finset.sum_fiberwise_of_maps_to hι]
  refine Finset.sum_le_sum fun i _ => ?_
  set F := s.filter fun a => ι a = i with hF
  rcases F.eq_empty_or_nonempty with hFe | ⟨a₀, ha₀⟩
  · rw [hFe, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul]
  have hM : 0 ≤ M i := by
    have h := Finset.mem_filter.1 ha₀
    exact (norm_nonneg _).trans (h.2 ▸ hB a₀ h.1)
  have h1 : ∑ a ∈ F, ‖W a‖ * ‖B a‖ ≤ M i * ∑ a ∈ F, ‖W a‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    have h := Finset.mem_filter.1 ha
    have hb := h.2 ▸ hB a h.1
    rw [mul_comm (M i)]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have h2 : ∑ a ∈ F, ‖W a‖ ^ 2 ≤ ∑ a ∈ s, ‖W a‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ => by positivity
  calc ∑ a ∈ F, ‖W a‖ * ‖B a‖ ≤ M i * ∑ a ∈ F, ‖W a‖ := h1
    _ ≤ M i * (Real.sqrt F.card * Real.sqrt (∑ a ∈ F, ‖W a‖ ^ 2)) := by
        gcongr; exact sum_le_sqrt_card_mul_sqrt F fun a => ‖W a‖
    _ ≤ M i * (Real.sqrt F.card * Real.sqrt (∑ a ∈ s, ‖W a‖ ^ 2)) := by
        gcongr
    _ = M i * Real.sqrt F.card * Real.sqrt (∑ a ∈ s, ‖W a‖ ^ 2) := by ring

/-! ### The bins of characters -/

section Bins

open scoped Classical ContDiff

variable {q : ℕ} [NeZero q]

/-- **The bin of `χ`**: the largest `i < N` such that `i = 0` or `L(·, χ)` has a zero with `Re s > β i` and
`|Im s| ≤ T`. It depends on `T`, not on the heights of the prime sums. -/
noncomputable def bin (β : ℕ → ℝ) (N : ℕ) (T : ℝ) (χ : DirichletCharacter ℂ q) : ℕ :=
  ((Finset.range N).filter (fun i => i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)).sup id

lemma mem_binSet {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} {i : ℕ} :
    i ∈ (Finset.range N).filter (fun i => i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) ↔
      i < N ∧ (i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) := by
  rw [Finset.mem_filter, Finset.mem_range]

lemma bin_lt {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (T : ℝ) (χ : DirichletCharacter ℂ q) : bin β N T χ < N := by
  unfold bin
  exact (Finset.sup_lt_iff (by simpa using hN)).2 fun i hi => (mem_binSet.1 hi).1

lemma le_bin {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} {i : ℕ} (hi : i < N)
    (hz : ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) : i ≤ bin β N T χ :=
  Finset.le_sup (f := id) (mem_binSet.2 ⟨hi, Or.inr hz⟩)

/-- Above its bin, `χ` has no zero: none with `Re s > β (bin + 1)` and `|Im s| ≤ T`. -/
lemma bin_zeroFree {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} (h : bin β N T χ + 1 < N) :
    ∀ s : ℂ, β (bin β N T χ + 1) < s.re → |s.im| ≤ T → LFunction χ s ≠ 0 := by
  intro s hs hT h0
  have := le_bin h ⟨s, hs, hT, h0⟩
  omega

/-- In a bin `i > 0`, `χ` has a zero with `Re s > β i` and `|Im s| ≤ T`. -/
lemma bin_zero {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} (hN : 0 < N) (h : 0 < bin β N T χ) :
    ∃ s : ℂ, β (bin β N T χ) < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
  have hne : ((Finset.range N).filter
      (fun i => i = 0 ∨ ∃ s : ℂ, β i < s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)).Nonempty :=
    ⟨0, mem_binSet.2 ⟨hN, Or.inl rfl⟩⟩
  obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup _ hne id
  have hb : bin β N T χ = i := by unfold bin; rw [hieq]; rfl
  rw [hb] at h ⊢
  rcases (mem_binSet.1 hi).2 with h0 | hz
  · omega
  · exact hz

/-- **The rectangle of Lemma 1.** If `β N = 11/12`, `χ ≠ 1` and `|y| + H + 1 ≤ T`, then `L(·, χ)` has no zero with
`Re s > β (bin + 1)` and `|Im s − y| < H + 1`: below `N` by `bin_zeroFree`, and at `N` by the zero-free half-plane
`Re s > 11/12` (`Eis.LFunction_ne_zero_of_re_gt`). -/
lemma bin_rect {β : ℕ → ℝ} {N : ℕ} {T : ℝ} {χ : DirichletCharacter ℂ q} (hβN : β N = 11 / 12) (hχ : χ ≠ 1)
    (hN : 0 < N) {y H : ℝ} (hyT : |y| + H + 1 ≤ T) :
    ∀ s : ℂ, β (bin β N T χ + 1) < s.re → |s.im - y| < H + 1 → LFunction χ s ≠ 0 := by
  intro s hs him
  have hb := bin_lt (β := β) hN T χ
  rcases Nat.lt_or_ge (bin β N T χ + 1) N with h | h
  · refine bin_zeroFree h s hs ?_
    have h1 : |s.im| ≤ |s.im - y| + |y| := by
      have := abs_add_le (s.im - y) y
      rwa [sub_add_cancel] at this
    linarith
  · have e : bin β N T χ + 1 = N := by omega
    rw [e, hβN] at hs
    exact Eis.LFunction_ne_zero_of_re_gt χ hs (Or.inl hχ)

/-- **The count of a bin `i > 0`**: its characters have a zero with `Re s ≥ β i` and `|Im s| ≤ T`. -/
lemma card_bin_le {β : ℕ → ℝ} {N : ℕ} {T : ℝ} (hN : 0 < N) {i : ℕ} (hi : 0 < i) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card ≤
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, β i ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card := by
  refine Finset.card_le_card fun χ hχ => ?_
  have h := (Finset.mem_filter.1 hχ).2
  obtain ⟨s, hs, hT, h0⟩ := bin_zero (χ := χ) hN (h.2 ▸ hi)
  rw [h.2] at hs
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, s, hs.le, hT, h0⟩

/-- **Proposition 3′ pointwise, by bins.** If `|B(χ)| ≤ M_i` for `χ ≠ 1` in bin `i`, then
`Σ_{χ≠1} |W(χ)||B(χ)| ≤ Σ_{i<N} M_i(#bin i)^{1/2}(Σ_χ |W(χ)|²)^{1/2}`. -/
theorem sum_typeII_bins {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (T : ℝ) (W B : DirichletCharacter ℂ q → ℂ)
    (M : ℕ → ℝ) (hB : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖B χ‖ ≤ M (bin β N T χ)) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖W χ‖ * ‖B χ‖ ≤
      ∑ i ∈ Finset.range N, M i *
        Real.sqrt (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card *
          Real.sqrt (∑ χ, ‖W χ‖ ^ 2) := by
  have h := sum_bins_le (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1) (Finset.range N)
    (bin β N T) (fun χ _ => Finset.mem_range.2 (bin_lt hN T χ)) W B M
    (fun χ hχ => hB χ (Finset.mem_filter.1 hχ).2)
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.filter_filter]
  have hM : 0 ≤ M i * Real.sqrt (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      χ ≠ 1 ∧ bin β N T χ = i).card ∨
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i) = ∅ := by
    rcases (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).eq_empty_or_nonempty
      with he | ⟨χ, hχ⟩
    · exact Or.inr he
    · left
      have hm := Finset.mem_filter.1 hχ
      have := (norm_nonneg _).trans (hm.2.2 ▸ hB χ hm.2.1)
      positivity
  rcases hM with hM | he
  · gcongr
    exact Finset.filter_subset _ _
  · rw [he, Finset.card_empty, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul, zero_mul]

/-- The bound of `SieveWeight.norm_Sp_le` for one prime sum at scale `Q` and height `y`, with `θ`, `δ`, `H`, the
decay `Kd` and its constants `Bc`, `Cc`. -/
noncomputable def MB (q : ℕ) (Bc Cc : ℝ) (Kd : ℕ) (θ δ H Q y : ℝ) : ℝ :=
  (Linnik.KL θ (θ + δ) + Linnik.KL (11 / 12) (11 / 12 + δ)) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * Bc *
      (Q ^ (θ + δ) + Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹) / Real.log Q +
    Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1))

/-- **Proposition 3′ pointwise, with Lemma 1 and (T1).** For a smooth `f0` with support in `[1/2, 2]` and a decay
`Kd` there are constants such that, for `W(χ) = Σ_{m∈S} a_mχ(m)m^{−ih₀}`, `S ⊆ (P, 2P]`, and
`B(χ) = ∏_{j<K} Σ_{p ≤ 2Q_j} χ(p)(p/Q_j)^{−ih_j}f0(p/Q_j)` with `Q_j ≥ 4` and `|h_j| + H + 1 ≤ T`,
`Σ_{χ≠1} |W(χ)||B(χ)| ≤ Σ_{i<N} (∏_j MB_j(β_{i+1}))(#bin i)^{1/2}((P + q)Σ|a_m|²)^{1/2}`. -/
theorem typeII_pointwise {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (Kd : ℕ) : ∃ Bc Cc : ℝ, 0 ≤ Bc ∧ 0 ≤ Cc ∧ ∀ (q : ℕ) [NeZero q] (β : ℕ → ℝ) (N : ℕ), 0 < N → β N = 11 / 12 →
      (∀ i ≤ N, 1 / 2 ≤ β i ∧ β i ≤ 11 / 12) → ∀ T δ H : ℝ, 0 < δ → δ ≤ 1 / 24 → 0 ≤ H →
      ∀ (K : ℕ) (Q h : ℕ → ℝ), (∀ j < K, 4 ≤ Q j ∧ |h j| + H + 1 ≤ T) →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) → ∀ (a : ℕ → ℂ) (h₀ : ℝ),
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        ∑ i ∈ Finset.range N, (∏ j ∈ Finset.range K, MB q Bc Cc Kd (β (i + 1)) δ H (Q j) (h j)) *
          Real.sqrt (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card *
            Real.sqrt ((P + q) * ∑ m ∈ S, ‖a m‖ ^ 2) := by
  obtain ⟨Bc, Cc, hBc, hCc, hL1⟩ := SieveWeight.norm_Sp_le hf0 hsupp Kd
  refine ⟨Bc, Cc, hBc, hCc, fun q _ β N hN hβN hβ T δ H hδ hδ1 hH K Q h hQh P S hS a h₀ => ?_⟩
  have hB : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        ∏ j ∈ Finset.range K, MB q Bc Cc Kd (β (bin β N T χ + 1)) δ H (Q j) (h j) := by
    intro χ hχ
    have hb := bin_lt (β := β) hN T χ
    have hθ := hβ (bin β N T χ + 1) (by omega)
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j hj => ?_
    have hj' := hQh j (Finset.mem_range.1 hj)
    exact hL1 q χ hχ (β (bin β N T χ + 1)) δ H (Q j) (h j) hθ.1 hθ.2 hδ hδ1 hH hj'.1
      (bin_rect hβN hχ hN hj'.2)
  have hsum := sum_typeII_bins (β := β) hN T (fun χ => dp S (fun m => a m * χ m) h₀)
    (fun χ => ∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j))
    (fun i => ∏ j ∈ Finset.range K, MB q Bc Cc Kd (β (i + 1)) δ H (Q j) (h j)) hB
  refine hsum.trans (Finset.sum_le_sum fun i hi => ?_)
  have hT1 := sum_chars_dp_sq_le hS a q h₀
  rcases (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).eq_empty_or_nonempty
    with he | ⟨χ, hχ⟩
  · rw [he, Finset.card_empty, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul, zero_mul]
  · have hm := Finset.mem_filter.1 hχ
    have hM : 0 ≤ ∏ j ∈ Finset.range K, MB q Bc Cc Kd (β (i + 1)) δ H (Q j) (h j) :=
      (norm_nonneg _).trans (hm.2.2 ▸ hB χ hm.2.1)
    gcongr

/-! ### The counts of the curve step -/

/-- The exponent `A(σ)(1 − σ)` of the curve step: `1` below `2801/4801` (the trivial count), `(4801/2000)(1 − σ)`
below `5/6` and `(101/50)(1 − σ)` from `5/6` on. -/
noncomputable def gStep (σ : ℝ) : ℝ :=
  if σ < 2801 / 4801 then 1 else if σ < 5 / 6 then 4801 / 2000 * (1 - σ) else 101 / 50 * (1 - σ)

/-- **The counts of the curve step**: at most `C(qT)^{g(σ)}(1 + log qT)^{10}` characters have a zero with
`Re s ≥ σ` and `|Im s| ≤ T` (`LinnikTwelve.charDensity_twelve_fifths` at `ε = 1/108000`,
`LinnikStep.charDensity_step`, and at most `q` characters). -/
theorem card_zero_step : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ gStep σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := LinnikTwelve.charDensity_twelve_fifths (ε := 1 / 108000) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂0, hC₂⟩ := LinnikStep.charDensity_step
  refine ⟨max 1 (max C₁ C₂), by positivity, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
  have hqT0 : 0 < (q : ℝ) * T := by linarith
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((q : ℝ) * T) ^ (10 : ℝ) ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ hl (by linarith) 10
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith)
  have hM1 : 1 ≤ max 1 (max C₁ C₂) := le_max_left _ _
  have hMC₁ : C₁ ≤ max 1 (max C₁ C₂) := (le_max_left _ _).trans (le_max_right _ _)
  have hMC₂ : C₂ ≤ max 1 (max C₁ C₂) := (le_max_right _ _).trans (le_max_right _ _)
  unfold gStep
  split_ifs with h1 h2
  · have hc := LinnikDensity.card_chars_le (q := q) (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
    rw [Real.rpow_one]
    calc _ ≤ (q : ℝ) := hc
      _ ≤ 1 * ((q : ℝ) * T) * 1 := by nlinarith
      _ ≤ max 1 (max C₁ C₂) * ((q : ℝ) * T) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr
  · have hc := hC₁ q σ T hσ hσ1 hT
    have e : (12 / 5 + 54 * (1 / 108000) : ℝ) = 4801 / 2000 := by norm_num
    rw [e] at hc
    calc _ ≤ C₁ * ((q : ℝ) * T) ^ (4801 / 2000 * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hc
      _ ≤ max 1 (max C₁ C₂) * ((q : ℝ) * T) ^ (4801 / 2000 * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          gcongr
  · have hc := hC₂ q σ T (not_lt.1 h2) hσ1 hT
    calc _ ≤ C₂ * ((q : ℝ) * T) ^ (101 / 50 * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hc
      _ ≤ max 1 (max C₁ C₂) * ((q : ℝ) * T) ^ (101 / 50 * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          gcongr

/-! ### Lemma 1's bound, eventually -/

/-- `log(q + 2) + log(|y| + 4) + 1 ≤ 4 + 2 log q` for `q ≥ 1`, `|y| ≤ q^η`, `0 < η ≤ 1`. -/
lemma logs_le {q : ℕ} {y η : ℝ} (hq : 1 ≤ (q : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1) (hy : |y| ≤ (q : ℝ) ^ η) :
    Real.log (q + 2) + Real.log (|y| + 4) + 1 ≤ 4 + 2 * Real.log q := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hl0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have h1 : Real.log (q + 2) ≤ Real.log 3 + Real.log q := by
    rw [← Real.log_mul (by norm_num) hq0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hqη : 1 ≤ (q : ℝ) ^ η := Real.one_le_rpow hq hη.le
  have h2 : Real.log (|y| + 4) ≤ Real.log 5 + η * Real.log q := by
    rw [← Real.log_rpow hq0, ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have h15 : Real.log 3 + Real.log 5 ≤ 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [e]; nlinarith
  have hηl : η * Real.log q ≤ Real.log q := by nlinarith
  linarith

/-- `⌊√⌊2Q⌋⌋ + 1 ≤ 3√Q` for `Q ≥ 1`. -/
lemma sqrt_floor_le {Q : ℝ} (hQ : 1 ≤ Q) : (Nat.sqrt ⌊2 * Q⌋₊ : ℝ) + 1 ≤ 3 * Real.sqrt Q := by
  have hfl : (⌊2 * Q⌋₊ : ℝ) ≤ 2 * Q := Nat.floor_le (by positivity)
  have h1 : (Nat.sqrt ⌊2 * Q⌋₊ : ℝ) ≤ Real.sqrt (⌊2 * Q⌋₊ : ℝ) := Real.nat_sqrt_le_real_sqrt
  have h2 : Real.sqrt (⌊2 * Q⌋₊ : ℝ) ≤ Real.sqrt (2 * Q) := Real.sqrt_le_sqrt hfl
  have h3 : Real.sqrt (2 * Q) = Real.sqrt 2 * Real.sqrt Q := Real.sqrt_mul (by norm_num) Q
  have h4 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h5 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.2 hQ
  have h7 : Real.sqrt 2 * Real.sqrt Q ≤ 2 * Real.sqrt Q := mul_le_mul_of_nonneg_right h4 (by linarith)
  linarith

/-- `⌊log₂⌊2Q⌋⌋ + 1 ≤ 3(1 + log Q)` for `Q ≥ 1`. -/
lemma log_floor_le {Q : ℝ} (hQ : 1 ≤ Q) : (Nat.log 2 ⌊2 * Q⌋₊ : ℝ) + 1 ≤ 3 * (1 + Real.log Q) := by
  have hQ0 : 0 < Q := by linarith
  have hfl : (⌊2 * Q⌋₊ : ℝ) ≤ 2 * Q := Nat.floor_le (by positivity)
  have hfl1 : (1 : ℝ) ≤ ⌊2 * Q⌋₊ := by exact_mod_cast Nat.le_floor (by push_cast; linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (Nat.log 2 ⌊2 * Q⌋₊ : ℝ) ≤ Real.logb 2 (⌊2 * Q⌋₊ : ℝ) := by
    have h := Real.natLog_le_logb ⌊2 * Q⌋₊ 2
    simpa using h
  have h2 : Real.logb 2 (⌊2 * Q⌋₊ : ℝ) ≤ Real.logb 2 (2 * Q) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hfl
  have h3 : Real.logb 2 (2 * Q) = 1 + Real.log Q / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num) hQ0.ne', add_div, div_self hl2.ne']
  have hlQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hl2' : 1 / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h4 : Real.log Q / Real.log 2 ≤ 2 * Real.log Q := by
    rw [div_le_iff₀ hl2]
    have : Real.log Q * (1 / 2) ≤ Real.log Q * Real.log 2 := mul_le_mul_of_nonneg_left hl2' hlQ
    linarith
  linarith

/-- The prime powers' term of `SieveWeight.norm_Sp_le`: at most `Q^{1/2+δ}` once `9C(1 + log Q) ≤ Q^δ`. -/
lemma primePow_term_le {Cc δ Q : ℝ} (hCc : 0 ≤ Cc) (hQ : 1 ≤ Q) (hev : 9 * Cc * (1 + Real.log Q) ≤ Q ^ δ) :
    Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1)) ≤ Q ^ (1 / 2 + δ) := by
  have hQ0 : 0 < Q := by linarith
  have hs := sqrt_floor_le hQ
  have hl := log_floor_le hQ
  have h0 : (0 : ℝ) ≤ Nat.log 2 ⌊2 * Q⌋₊ + 1 := by positivity
  have h0' : (0 : ℝ) ≤ Nat.sqrt ⌊2 * Q⌋₊ + 1 := by positivity
  calc Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1))
      ≤ Cc * (3 * Real.sqrt Q * (3 * (1 + Real.log Q))) := by
        apply mul_le_mul_of_nonneg_left _ hCc
        exact mul_le_mul hs hl h0 (by positivity)
    _ = 9 * Cc * (1 + Real.log Q) * Real.sqrt Q := by ring
    _ ≤ Q ^ δ * Q ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_right hev (by positivity)
    _ = Q ^ (1 / 2 + δ) := by rw [← Real.rpow_add hQ0]; ring_nf

/-- **Lemma 1's bound, eventually.** Let `η·Kd ≥ 5U/12`. For all large `q`, every `θ ∈ [1/2, 11/12]` with
`KL(θ, θ + δ) ≤ KLmax`, every scale `q^{e₁} ≤ Q ≤ q^U` and every height `|y| ≤ q^η`, the bound of
`SieveWeight.norm_Sp_le` with `H = q^η` is at most `2Q^{θ+2δ}`. -/
lemma MB_le {Bc Cc KLmax δ e₁ η U : ℝ} {Kd : ℕ} (hBc : 0 ≤ Bc) (hCc : 0 ≤ Cc) (hKL : 0 ≤ KLmax) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 24) (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1) (hKd : 5 * U / 12 ≤ η * Kd) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ θ Q y : ℝ, 1 / 2 ≤ θ → θ ≤ 11 / 12 → Linnik.KL θ (θ + δ) ≤ KLmax →
      (q : ℝ) ^ e₁ ≤ Q → Q ≤ (q : ℝ) ^ U → |y| ≤ (q : ℝ) ^ η →
      MB q Bc Cc Kd θ δ ((q : ℝ) ^ η) Q y ≤ 2 * Q ^ (θ + 2 * δ) := by
  set KLg := Linnik.KL (11 / 12) (11 / 12 + δ) with hKLg
  have hKLg0 : 0 ≤ KLg := (Linnik.KL_pos (by linarith) (by linarith)).le
  set c₀ := (KLmax + KLg) * Bc * 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c₃ := c₀ * (4 / Real.log 2 + 2) / e₁ + 1 with hc₃
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.1 (LinnikTwelve.ev_log_pow (9 * Cc) δ 1 hδ)
  have hev : ∀ᶠ q : ℕ in Filter.atTop, c₃ ≤ (q : ℝ) ^ (e₁ * δ) ∧ max Q₁ 1 ≤ (q : ℝ) ^ e₁ ∧ 2 ≤ q :=
    (((tendsto_rpow_atTop (by positivity : 0 < e₁ * δ)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      c₃).and ((((tendsto_rpow_atTop he₁).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (max Q₁ 1)).and (Filter.eventually_ge_atTop 2))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨q₀, fun q hq θ Q y hθ hθ1 hKLθ hQ1 hQ2 hy => ?_⟩
  obtain ⟨hc₃q, hQ₁q, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2'
  have hlq0 : 0 < Real.log q := by linarith
  have hQge1 : 1 ≤ Q := le_trans (le_max_right _ _) (hQ₁q.trans hQ1)
  have hQ0 : 0 < Q := by linarith
  have hlQ : e₁ * Real.log q ≤ Real.log Q := by
    rw [← Real.log_rpow hq0]; exact Real.log_le_log (by positivity) hQ1
  have hlQ0 : 0 < Real.log Q := lt_of_lt_of_le (by positivity) hlQ
  -- the tail term
  set H := (q : ℝ) ^ η with hH
  have hH1 : 1 ≤ H := Real.one_le_rpow hq1 hη.le
  have htail : Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹ ≤ Q ^ (θ + δ) := by
    have hpos : 0 < (1 + H) ^ Kd := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have e : Q ^ (11 / 12 + δ) = Q ^ (θ + δ) * Q ^ (11 / 12 - θ) := by
      rw [← Real.rpow_add hQ0]; ring_nf
    rw [e]
    gcongr
    calc Q ^ (11 / 12 - θ) ≤ Q ^ (5 / 12 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQge1 (by linarith)
      _ ≤ ((q : ℝ) ^ U) ^ (5 / 12 : ℝ) := Real.rpow_le_rpow hQ0.le hQ2 (by norm_num)
      _ = (q : ℝ) ^ (5 * U / 12) := by rw [← Real.rpow_mul hq0.le]; ring_nf
      _ ≤ (q : ℝ) ^ (η * Kd) := Real.rpow_le_rpow_of_exponent_le hq1 hKd
      _ = H ^ Kd := by rw [hH, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      _ ≤ (1 + H) ^ Kd := pow_le_pow_left₀ (by linarith) (by linarith) Kd
  -- the first term
  have hlogs := logs_le hq1 hη hη1 hy
  have hl0 : 0 ≤ Real.log (q + 2) + Real.log (|y| + 4) + 1 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ q + 2)
    have := Real.log_nonneg (by linarith [abs_nonneg y] : (1 : ℝ) ≤ |y| + 4)
    linarith
  have hfirst : (Linnik.KL θ (θ + δ) + KLg) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * Bc *
      (Q ^ (θ + δ) + Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹) / Real.log Q ≤ Q ^ (θ + 2 * δ) := by
    have hKLθ0 : 0 ≤ Linnik.KL θ (θ + δ) := (Linnik.KL_pos (by linarith) (by linarith)).le
    have hQθ : 0 ≤ Q ^ (θ + δ) := by positivity
    have hstep1 : (Linnik.KL θ (θ + δ) + KLg) * (Real.log (q + 2) + Real.log (|y| + 4) + 1) * Bc *
        (Q ^ (θ + δ) + Q ^ (11 / 12 + δ) * ((1 + H) ^ Kd)⁻¹) ≤ c₀ * (4 + 2 * Real.log q) * Q ^ (θ + δ) := by
      calc _ ≤ (KLmax + KLg) * (4 + 2 * Real.log q) * Bc * (Q ^ (θ + δ) + Q ^ (θ + δ)) := by gcongr
        _ = c₀ * (4 + 2 * Real.log q) * Q ^ (θ + δ) := by rw [hc₀]; ring
    have hstep2 : c₀ * (4 + 2 * Real.log q) / Real.log Q ≤ c₃ := by
      rw [div_le_iff₀ hlQ0]
      have h1 : c₀ * (4 + 2 * Real.log q) ≤ c₀ * (4 / Real.log 2 + 2) * Real.log q := by
        have : 4 ≤ 4 / Real.log 2 * Real.log q := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; nlinarith
        nlinarith
      have h2 : c₀ * (4 / Real.log 2 + 2) * Real.log q = c₀ * (4 / Real.log 2 + 2) / e₁ * (e₁ * Real.log q) := by
        field_simp
      have h3 : 0 ≤ c₀ * (4 / Real.log 2 + 2) / e₁ := by positivity
      calc c₀ * (4 + 2 * Real.log q) ≤ c₀ * (4 / Real.log 2 + 2) / e₁ * (e₁ * Real.log q) := by linarith
        _ ≤ c₀ * (4 / Real.log 2 + 2) / e₁ * Real.log Q := by gcongr
        _ ≤ c₃ * Real.log Q := by gcongr; rw [hc₃]; linarith
    have hstep3 : c₃ ≤ Q ^ δ := by
      calc c₃ ≤ (q : ℝ) ^ (e₁ * δ) := hc₃q
        _ = ((q : ℝ) ^ e₁) ^ δ := by rw [← Real.rpow_mul hq0.le]
        _ ≤ Q ^ δ := Real.rpow_le_rpow (by positivity) hQ1 hδ.le
    calc _ ≤ c₀ * (4 + 2 * Real.log q) * Q ^ (θ + δ) / Real.log Q := by gcongr
      _ = c₀ * (4 + 2 * Real.log q) / Real.log Q * Q ^ (θ + δ) := by ring
      _ ≤ Q ^ δ * Q ^ (θ + δ) := by gcongr; exact hstep2.trans hstep3
      _ = Q ^ (θ + 2 * δ) := by rw [← Real.rpow_add hQ0]; ring_nf
  -- the prime powers
  have hsecond : Cc * ((Nat.sqrt ⌊2 * Q⌋₊ + 1) * (Nat.log 2 ⌊2 * Q⌋₊ + 1)) ≤ Q ^ (θ + 2 * δ) := by
    have hQQ₁ : Q₁ ≤ Q := le_trans (le_max_left _ _) (hQ₁q.trans hQ1)
    have hev := hQ₁ Q hQQ₁
    rw [pow_one] at hev
    calc _ ≤ Q ^ (1 / 2 + δ) := primePow_term_le hCc hQge1 hev
      _ ≤ Q ^ (θ + 2 * δ) := Real.rpow_le_rpow_of_exponent_le hQge1 (by linarith)
  unfold MB
  have hKLθ : Linnik.KL θ (θ + δ) + Linnik.KL (11 / 12) (11 / 12 + δ) = Linnik.KL θ (θ + δ) + KLg := by rw [hKLg]
  rw [hKLθ]
  linarith

/-! ### The exponents on the window -/

/-- **The window's exponents** for the curve step at `L = 2333/1000` on `m ∈ [401/1000, 485/1000]·L`: for
`1/2 ≤ β ≤ 11/12` and `0 ≤ w ≤ 4·10⁻⁶`,
`(L − m)(β + w) + g(β)/2 + (1 + m)/2 ≤ L − 1/25000` when `m ≤ 1`, and with `m` in place of `(1 + m)/2` when `m ≥ 1`.
The left sides are linear in `β` on each piece of `g`, so their largest values lie at the pieces' ends. Before the
width they lie at least `5.5·10⁻⁵` below `L` and `1.5·10⁻⁵` below `L − 1/25000`, least at `β = 11/12` and
`m = (401/1000)L`; at `w = 4·10⁻⁶`, at least `9.8·10⁻⁶` below `L − 1/25000`. -/
theorem exponent_le {β m w : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 11 / 12) (hm : 401 / 1000 * (2333 / 1000) ≤ m)
    (hm1 : m ≤ 485 / 1000 * (2333 / 1000)) (hw : 0 ≤ w) (hw1 : w ≤ 4 / 10 ^ 6) :
    (m ≤ 1 → (2333 / 1000 - m) * (β + w) + gStep β / 2 + (1 + m) / 2 ≤ 2333 / 1000 - 1 / 25000) ∧
    (1 ≤ m → (2333 / 1000 - m) * (β + w) + gStep β / 2 + m ≤ 2333 / 1000 - 1 / 25000) := by
  have hwm : (2333 / 1000 - m) * w ≤ 6 / 10 ^ 6 := by
    calc (2333 / 1000 - m) * w ≤ (3 / 2) * (4 / 10 ^ 6) := by
          apply mul_le_mul (by linarith) hw1 hw (by norm_num)
      _ = 6 / 10 ^ 6 := by norm_num
  unfold gStep
  constructor
  · intro hm2
    split_ifs with h1 h2
    · nlinarith [mul_nonneg (sub_nonneg.2 hβ) (sub_nonneg.2 hm)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h1)) (sub_nonneg.2 hm),
        mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 hm)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h2)) (sub_nonneg.2 hm),
        mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hm)]
  · intro hm2
    split_ifs with h1 h2
    · nlinarith [mul_nonneg (sub_nonneg.2 hβ) (sub_nonneg.2 hm1), mul_nonneg (sub_nonneg.2 h1.le) (sub_nonneg.2 hm1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h1)) (sub_nonneg.2 hm1),
        mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 hm1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 (not_lt.1 h2)) (sub_nonneg.2 hm1),
        mul_nonneg (sub_nonneg.2 hβ1) (sub_nonneg.2 hm1)]

/-- **The factors as powers of `q`.** With `P = q^m`, `1 ≤ T ≤ 3q^η` and `g ≤ 1`:
`(q^L/P)^{θ′}((qT)^g)^{1/2}((P + q)V)^{1/2} ≤ 2√3·q^{(L−m)θ′ + g/2 + t + η/2}(V/P)^{1/2}`, where `t = (1 + m)/2` if
`m ≤ 1` and `t = m` if `m ≥ 1`, for `q > 1`. -/
lemma qpow_combine {q P V T η g θ' L m : ℝ} (hq : 1 < q) (hPm : P = q ^ m) (hT1 : 1 ≤ T)
    (hT : T ≤ 3 * q ^ η) (hg1 : g ≤ 1) :
    (m ≤ 1 → (q ^ L / P) ^ θ' * Real.sqrt ((q * T) ^ g) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ ((L - m) * θ' + g / 2 + (1 + m) / 2 + η / 2) * Real.sqrt (V / P)) ∧
    (1 ≤ m → (q ^ L / P) ^ θ' * Real.sqrt ((q * T) ^ g) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ ((L - m) * θ' + g / 2 + m + η / 2) * Real.sqrt (V / P)) := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hT0 : 0 < T := by linarith
  -- the first factor
  have h1 : (q ^ L / P) ^ θ' = q ^ ((L - m) * θ') := by
    rw [hPm, ← Real.rpow_sub hq0, ← Real.rpow_mul hq0.le]
  -- the second factor
  have h2 : Real.sqrt ((q * T) ^ g) ≤ Real.sqrt 3 * q ^ (g / 2 + η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.mul_rpow hq0.le hT0.le]
    have hTg : T ^ (g * (1 / 2)) ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
    have hT3 : T ^ (1 / 2 : ℝ) ≤ (3 * q ^ η) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hT0.le hT (by norm_num)
    have e3 : (3 * q ^ η) ^ (1 / 2 : ℝ) = Real.sqrt 3 * q ^ (η / 2) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; ring_nf
    have eq : q ^ (g * (1 / 2)) * q ^ (η / 2) = q ^ (g / 2 + η / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    calc q ^ (g * (1 / 2)) * T ^ (g * (1 / 2)) ≤ q ^ (g * (1 / 2)) * (Real.sqrt 3 * q ^ (η / 2)) := by
          gcongr; exact (hTg.trans hT3).trans e3.le
      _ = Real.sqrt 3 * q ^ (g / 2 + η / 2) := by rw [← eq]; ring
  -- the third factor
  have hsplit : Real.sqrt ((P + q) * V) = Real.sqrt ((P + q) * P) * Real.sqrt (V / P) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hA : 0 ≤ q ^ ((L - m) * θ') := by positivity
  have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  constructor
  · intro hm1
    have hPq : P ≤ q := by
      rw [hPm]; calc q ^ m ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le hm1
        _ = q := Real.rpow_one q
    have h3 : Real.sqrt ((P + q) * P) ≤ 2 * q ^ ((1 + m) / 2) := by
      have hb : (P + q) * P ≤ 2 * q ^ (1 + m) := by
        rw [Real.rpow_add hq0, Real.rpow_one, ← hPm]; nlinarith
      calc Real.sqrt ((P + q) * P) ≤ Real.sqrt (2 * q ^ (1 + m)) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt 2 * q ^ ((1 + m) / 2) := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (q ^ (1 + m)), ← Real.rpow_mul hq0.le]; ring_nf
        _ ≤ 2 * q ^ ((1 + m) / 2) := by gcongr
    have eq : q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ ((1 + m) / 2) =
        q ^ ((L - m) * θ' + g / 2 + (1 + m) / 2 + η / 2) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
    rw [h1, hsplit]
    calc q ^ ((L - m) * θ') * Real.sqrt ((q * T) ^ g) * (Real.sqrt ((P + q) * P) * Real.sqrt (V / P))
        ≤ q ^ ((L - m) * θ') * (Real.sqrt 3 * q ^ (g / 2 + η / 2)) * (2 * q ^ ((1 + m) / 2) * Real.sqrt (V / P)) := by
          gcongr
      _ = 2 * Real.sqrt 3 * (q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ ((1 + m) / 2)) * Real.sqrt (V / P) := by
          ring
      _ = _ := by rw [eq]
  · intro hm1
    have hPq : q ≤ P := by
      rw [hPm]; calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
        _ ≤ q ^ m := Real.rpow_le_rpow_of_exponent_le hq.le hm1
    have h3 : Real.sqrt ((P + q) * P) ≤ 2 * q ^ m := by
      have hb : (P + q) * P ≤ 2 * (q ^ m) ^ 2 := by rw [← hPm]; nlinarith
      calc Real.sqrt ((P + q) * P) ≤ Real.sqrt (2 * (q ^ m) ^ 2) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt 2 * q ^ m := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
        _ ≤ 2 * q ^ m := by gcongr
    have eq : q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ m =
        q ^ ((L - m) * θ' + g / 2 + m + η / 2) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
    rw [h1, hsplit]
    calc q ^ ((L - m) * θ') * Real.sqrt ((q * T) ^ g) * (Real.sqrt ((P + q) * P) * Real.sqrt (V / P))
        ≤ q ^ ((L - m) * θ') * (Real.sqrt 3 * q ^ (g / 2 + η / 2)) * (2 * q ^ m * Real.sqrt (V / P)) := by
          gcongr
      _ = 2 * Real.sqrt 3 * (q ^ ((L - m) * θ') * q ^ (g / 2 + η / 2) * q ^ m) * Real.sqrt (V / P) := by ring
      _ = _ := by rw [eq]

lemma gStep_le_one (σ : ℝ) : gStep σ ≤ 1 := by
  unfold gStep
  split_ifs with h1 h2
  · exact le_rfl
  · have : 4801 / 2000 * (1 - σ) ≤ 4801 / 2000 * (1 - 2801 / 4801) := by
      have := not_lt.1 h1; nlinarith
    linarith
  · have := not_lt.1 h2; nlinarith

lemma gStep_nonneg {σ : ℝ} (hσ1 : σ ≤ 1) : 0 ≤ gStep σ := by
  unfold gStep
  split_ifs <;> nlinarith

/-- **One bin.** With `P = q^m` on the window, `1 ≤ T ≤ 3q^η`, `1/2 ≤ β ≤ 11/12` and a width `w ≤ 4·10⁻⁶`: if the
product of Lemma 1's bounds is at most `C₀(q^L/P)^{β+w}` and the bin holds at most `C_d(qT)^{g(β)}(1 + log qT)^{10}`
characters, then the bin's term is at most `2√3·C₀C_d^{1/2}(1 + log qT)^5 q^{L−1/25000+η/2}(V/P)^{1/2}`. -/
lemma bin_bound {q P m T η β w Mp cnt V C₀ Cd : ℝ} (hq : 1 < q) (hPm : P = q ^ m)
    (hm1 : 401 / 1000 * (2333 / 1000) ≤ m) (hm2 : m ≤ 485 / 1000 * (2333 / 1000)) (hT1 : 1 ≤ T)
    (hT : T ≤ 3 * q ^ η) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 11 / 12) (hw : 0 ≤ w) (hw1 : w ≤ 4 / 10 ^ 6)
    (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (hMp : Mp ≤ C₀ * (q ^ (2333 / 1000 : ℝ) / P) ^ (β + w))
    (hcnt : cnt ≤ Cd * (q * T) ^ gStep β * (1 + Real.log (q * T)) ^ 10) :
    Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
        q ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) * Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hg1 := gStep_le_one β
  have hcomb := qpow_combine (V := V) (θ' := β + w) (L := 2333 / 1000) hq hPm hT1 hT hg1
  have hexp := exponent_le hβ hβ1 hm1 hm2 hw hw1
  have hsq : Real.sqrt cnt ≤ Real.sqrt Cd * Real.sqrt ((q * T) ^ gStep β) * (1 + Real.log (q * T)) ^ 5 := by
    have e : Real.sqrt ((1 + Real.log (q * T)) ^ 10) = (1 + Real.log (q * T)) ^ 5 := by
      rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
    calc Real.sqrt cnt ≤ Real.sqrt (Cd * (q * T) ^ gStep β * (1 + Real.log (q * T)) ^ 10) := Real.sqrt_le_sqrt hcnt
      _ = Real.sqrt Cd * Real.sqrt ((q * T) ^ gStep β) * (1 + Real.log (q * T)) ^ 5 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCd, e]
  have hA : 0 ≤ (q ^ (2333 / 1000 : ℝ) / P) ^ (β + w) := by
    have : 0 < P := by rw [hPm]; positivity
    positivity
  have hpow : ∀ E : ℝ, E ≤ 2333 / 1000 - 1 / 25000 → q ^ (E + η / 2) ≤ q ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) :=
    fun E hE => Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
  have key : (q ^ (2333 / 1000 : ℝ) / P) ^ (β + w) * Real.sqrt ((q * T) ^ gStep β) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) * Real.sqrt (V / P) := by
    have hs3 : 0 ≤ 2 * Real.sqrt 3 := by positivity
    have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
    rcases le_total m 1 with hm | hm
    · refine (hcomb.1 hm).trans ?_
      have h := hpow _ (hexp.1 hm)
      have e : (2333 / 1000 - m) * (β + w) + gStep β / 2 + (1 + m) / 2 + η / 2 =
          ((2333 / 1000 - m) * (β + w) + gStep β / 2 + (1 + m) / 2) + η / 2 := by ring
      rw [e]; gcongr
    · refine (hcomb.2 hm).trans ?_
      have h := hpow _ (hexp.2 hm)
      have e : (2333 / 1000 - m) * (β + w) + gStep β / 2 + m + η / 2 =
          ((2333 / 1000 - m) * (β + w) + gStep β / 2 + m) + η / 2 := by ring
      rw [e]; gcongr
  have hs1 : 0 ≤ Real.sqrt ((q * T) ^ gStep β) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt ((P + q) * V) := Real.sqrt_nonneg _
  calc Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V)
      ≤ (C₀ * (q ^ (2333 / 1000 : ℝ) / P) ^ (β + w)) *
          (Real.sqrt Cd * Real.sqrt ((q * T) ^ gStep β) * (1 + Real.log (q * T)) ^ 5) *
            Real.sqrt ((P + q) * V) := by gcongr
    _ = C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
          ((q ^ (2333 / 1000 : ℝ) / P) ^ (β + w) * Real.sqrt ((q * T) ^ gStep β) * Real.sqrt ((P + q) * V)) := by
        ring
    _ ≤ C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
          (2 * Real.sqrt 3 * q ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) * Real.sqrt (V / P)) := by gcongr
    _ = _ := by ring

/-- **The product of Lemma 1's bounds.** If each factor's bound is at most `2Q_j^{θ+2δ}`, `Q_j ≥ 1` and
`∏ Q_j ≤ 2^{K₀}q^L/P` with `K ≤ K₀`, then the product is at most `2^{K₀}·2^{K₀}(q^L/P)^{θ+2δ}` when
`0 ≤ θ + 2δ ≤ 1`. -/
lemma prod_MB_le {K K₀ : ℕ} {M Q : ℕ → ℝ} {q P θ' : ℝ} (hK : K ≤ K₀) (hq : 0 < q) (hP : 0 < P)
    (hθ0 : 0 ≤ θ') (hθ1 : θ' ≤ 1) (hM0 : ∀ j < K, 0 ≤ M j) (hM : ∀ j < K, M j ≤ 2 * Q j ^ θ')
    (hQ1 : ∀ j < K, 1 ≤ Q j) (hprod : ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * q ^ (2333 / 1000 : ℝ) / P) :
    ∏ j ∈ Finset.range K, M j ≤ 2 ^ K₀ * 2 ^ K₀ * (q ^ (2333 / 1000 : ℝ) / P) ^ θ' := by
  have hQ0 : ∀ j ∈ Finset.range K, 0 ≤ Q j := fun j hj => by linarith [hQ1 j (Finset.mem_range.1 hj)]
  have h2K : (2 : ℝ) ^ K ≤ 2 ^ K₀ := pow_le_pow_right₀ (by norm_num) hK
  have hA : 0 ≤ ∏ j ∈ Finset.range K, Q j := Finset.prod_nonneg hQ0
  have h2K₀ : (1 : ℝ) ≤ 2 ^ K₀ := one_le_pow₀ (by norm_num)
  have hqL : 0 ≤ q ^ (2333 / 1000 : ℝ) / P := div_nonneg (Real.rpow_nonneg hq.le _) hP.le
  calc ∏ j ∈ Finset.range K, M j ≤ ∏ j ∈ Finset.range K, (2 * Q j ^ θ') :=
        Finset.prod_le_prod₀ (fun j hj => hM0 j (Finset.mem_range.1 hj)) fun j hj => hM j (Finset.mem_range.1 hj)
    _ = 2 ^ K * (∏ j ∈ Finset.range K, Q j) ^ θ' := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Real.finsetProd_rpow _ _ hQ0]
    _ ≤ 2 ^ K₀ * (2 ^ K₀ * q ^ (2333 / 1000 : ℝ) / P) ^ θ' := by
        apply mul_le_mul h2K (Real.rpow_le_rpow hA hprod hθ0) (Real.rpow_nonneg hA _) (by positivity)
    _ = 2 ^ K₀ * ((2 ^ K₀) ^ θ' * (q ^ (2333 / 1000 : ℝ) / P) ^ θ') := by
        rw [mul_div_assoc, Real.mul_rpow (by positivity) hqL]
    _ ≤ 2 ^ K₀ * (2 ^ K₀ * (q ^ (2333 / 1000 : ℝ) / P) ^ θ') := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hqL _)
        calc ((2 : ℝ) ^ K₀) ^ θ' ≤ ((2 : ℝ) ^ K₀) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2K₀ hθ1
          _ = 2 ^ K₀ := Real.rpow_one _
    _ = 2 ^ K₀ * 2 ^ K₀ * (q ^ (2333 / 1000 : ℝ) / P) ^ θ' := by ring

/-- **The count of a bin of the grid.** With `card_zero_step`'s bound for the zeros, every bin `i < N` of a grid
with `β_0 = 1/2` (where `g = 1`) holds at most `max(C, 1)(qT)^{g(β_i)}(1 + log qT)^{10}` characters `χ ≠ 1`. -/
lemma card_bin_step {q : ℕ} [NeZero q] {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (hβ0 : β 0 = 1 / 2)
    (hβ : ∀ i < N, 1 / 2 ≤ β i ∧ β i ≤ 1) {T Cd : ℝ} (hT : 2 ≤ T)
    (hCd : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          Cd * ((q : ℝ) * T) ^ gStep σ * (1 + Real.log ((q : ℝ) * T)) ^ 10) {i : ℕ} (hi : i < N) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card : ℝ) ≤
      max Cd 1 * ((q : ℝ) * T) ^ gStep (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 1 ≤ (q : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith [Real.log_nonneg hqT])
  have hM1 : 1 ≤ max Cd 1 := le_max_right _ _
  have hMC : Cd ≤ max Cd 1 := le_max_left _ _
  have hP : 0 ≤ ((q : ℝ) * T) ^ gStep (β i) := Real.rpow_nonneg (by linarith) _
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have hc := LinnikDensity.card_chars_le (q := q)
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = 0)
    have hg : gStep (β 0) = 1 := by rw [hβ0]; unfold gStep; norm_num
    rw [hg, Real.rpow_one]
    calc _ ≤ (q : ℝ) := hc
      _ ≤ 1 * ((q : ℝ) * T) * 1 := by
          rw [one_mul, mul_one]; exact le_mul_of_one_le_right (by linarith) (by linarith)
      _ ≤ max Cd 1 * ((q : ℝ) * T) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hM1 (by linarith)) hl1 (by norm_num)
          exact mul_nonneg (by linarith) (by linarith)
  · have hc1 := card_bin_le (q := q) (β := β) (T := T) hN hpos
    have hc2 := hCd (β i) (hβ i hi).1 (hβ i hi).2
    have hc2' : 0 ≤ Cd * ((q : ℝ) * T) ^ gStep (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 :=
      le_trans (Nat.cast_nonneg _) hc2
    calc _ ≤ ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          ∃ s : ℂ, β i ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) := by exact_mod_cast hc1
      _ ≤ Cd * ((q : ℝ) * T) ^ gStep (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := hc2
      _ ≤ max Cd 1 * ((q : ℝ) * T) ^ gStep (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC hP) (by linarith)

/-! ### Proposition 3′ for the curve step -/

/-- The grid of the bins: `β_i = 1/2 + (5/12)(i/500000)`, of width `1/1200000`. -/
noncomputable def βg (i : ℕ) : ℝ := 1 / 2 + 5 / 12 * ((i : ℝ) / 500000)

lemma βg_range {i : ℕ} (hi : i ≤ 500000) : 1 / 2 ≤ βg i ∧ βg i ≤ 11 / 12 := by
  have h : (i : ℝ) ≤ 500000 := by exact_mod_cast hi
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold βg
  constructor
  · have : 0 ≤ 5 / 12 * ((i : ℝ) / 500000) := by positivity
    linarith
  · have : (i : ℝ) / 500000 ≤ 1 := by rw [div_le_one (by norm_num)]; exact h
    nlinarith

lemma βg_top : βg 500000 = 11 / 12 := by unfold βg; norm_num

lemma βg_zero : βg 0 = 1 / 2 := by unfold βg; norm_num

lemma βg_succ (i : ℕ) : βg (i + 1) = βg i + 1 / 1200000 := by unfold βg; push_cast; ring

lemma MB_nonneg {q : ℕ} {Bc Cc : ℝ} {Kd : ℕ} {θ δ H Q y : ℝ} (hBc : 0 ≤ Bc) (hCc : 0 ≤ Cc)
    (hθ1 : θ ≤ 11 / 12) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hH : 0 ≤ H) (hQ : 1 < Q) :
    0 ≤ MB q Bc Cc Kd θ δ H Q y := by
  unfold MB
  have h1 := Linnik.KL_pos (θ := θ) (θ' := θ + δ) (by linarith) (by linarith)
  have h2 := Linnik.KL_pos (θ := 11 / 12) (θ' := 11 / 12 + δ) (by linarith) (by linarith)
  have h3 : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
  have h4 : 0 ≤ Real.log (|y| + 4) := Real.log_nonneg (by have := abs_nonneg y; linarith)
  have h5 : 0 < Real.log Q := Real.log_pos hQ
  have hQ0 : 0 < Q := by linarith
  positivity

/-- **Proposition 3′ for the curve step at `L = 2333/1000`, pointwise in the heights.** Let `f0` be smooth with
support in `[1/2, 2]`, `K₀ ≥ 0`, `e₁ > 0` and `0 < η ≤ 10⁻⁵`. For every large `q`, every `P` with
`q^{(401/1000)L} ≤ P ≤ q^{(485/1000)L}`, `W(χ) = Σ_{m∈S} a_mχ(m)m^{−ih₀}` with `S ⊆ (P, 2P]`, and
`B(χ) = ∏_{j<K} Σ_{p ≤ 2Q_j} χ(p)(p/Q_j)^{−ih_j}f0(p/Q_j)` with `K ≤ K₀`, `Q_j ≥ q^{e₁}`, `|h_j| ≤ q^η` and
`∏_j Q_j ≤ 2^{K₀}q^L/P`:
`Σ_{χ≠1} |W(χ)||B(χ)| ≤ q^{L−1/50000}(Σ_m |a_m|²/P)^{1/2}`. -/
theorem typeII_step {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0) (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) ≤ P → (P : ℝ) ≤ (q : ℝ) ^ (485 / 1000 * (2333 / 1000) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) := by
  -- the parameters
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 10 ^ 6 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 3333 / 1000 := ⟨_, rfl⟩
  obtain ⟨Kd, hKd⟩ : ∃ Kd : ℕ, Kd = ⌈5 * U / 12 / η⌉₊ := ⟨_, rfl⟩
  have hKdη : 5 * U / 12 ≤ η * Kd := by
    have h : 5 * U / 12 / η ≤ (Kd : ℝ) := hKd ▸ Nat.le_ceil (5 * U / 12 / η)
    rw [div_le_iff₀ hη] at h
    calc 5 * U / 12 ≤ (Kd : ℝ) * η := h
      _ = η * Kd := mul_comm _ _
  obtain ⟨Bc, Cc, hBc, hCc, hpt⟩ := typeII_pointwise hf0 hsupp Kd
  obtain ⟨KLmax, hKLmax⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range 500001, Linnik.KL (βg i) (βg i + δ) := ⟨_, rfl⟩
  have hKLnn : ∀ i ≤ 500000, 0 ≤ Linnik.KL (βg i) (βg i + δ) := fun i hi =>
    (Linnik.KL_pos (by rw [hδ]; linarith) (by have := (βg_range hi).2; rw [hδ]; linarith)).le
  have hKLle : ∀ i ≤ 500000, Linnik.KL (βg i) (βg i + δ) ≤ KLmax := fun i hi => hKLmax ▸
    Finset.single_le_sum (f := fun i => Linnik.KL (βg i) (βg i + δ))
      (fun j hj => hKLnn j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (Finset.mem_range.2 (by omega))
  have hKLmax0 : 0 ≤ KLmax := (hKLnn 0 (by norm_num)).trans (hKLle 0 (by norm_num))
  obtain ⟨q₁, hMB⟩ := MB_le hBc hCc hKLmax0 (δ := δ) (by rw [hδ]; norm_num) (by rw [hδ]; norm_num) he₁ hη
    (by linarith) hKdη
  obtain ⟨Cd, hCd0, hCd⟩ := card_zero_step
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, C = 2 * Real.sqrt 3 * (2 ^ K₀ * 2 ^ K₀) * Real.sqrt (max Cd 1) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by positivity))
      (Real.sqrt_nonneg _)
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.1
    (LinnikTwelve.ev_log_pow (500000 * C₁ * 3 ^ 5) (3 / 200000) 5 (by norm_num))
  have hev : ∀ᶠ q : ℕ in Filter.atTop, q₁ ≤ q ∧ (2 : ℝ) ^ K₀ ≤ q ∧ 4 ≤ (q : ℝ) ^ e₁ ∧ Q₂ ≤ (q : ℝ) ∧ 2 ≤ q :=
    (Filter.eventually_ge_atTop q₁).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop ((2 : ℝ) ^ K₀)).and
        ((((tendsto_rpow_atTop he₁).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4).and
          ((tendsto_natCast_atTop_atTop.eventually_ge_atTop Q₂).and (Filter.eventually_ge_atTop 2))))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨q₀, fun q _ hq P S hS hP1 hP2 a h₀ K hK Q h hQh hprod => ?_⟩
  obtain ⟨hq₁, hq2K, hqe, hqQ₂, hq2⟩ := hq₀ q hq
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) < q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  -- `P = q^m` on the window
  have hm1pos : (0 : ℝ) < (q : ℝ) ^ (401 / 1000 * (2333 / 1000) : ℝ) := Real.rpow_pos_of_pos hq0 _
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le hm1pos hP1
  have hPge1 : (1 : ℝ) ≤ P := le_trans (Real.one_le_rpow hq1.le (by norm_num)) hP1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.logb q P := ⟨_, rfl⟩
  have hPm : (P : ℝ) = (q : ℝ) ^ m := by rw [hm]; exact (Real.rpow_logb hq0 hq1.ne' hP0).symm
  have hm1 : 401 / 1000 * (2333 / 1000) ≤ m := by
    rw [hPm] at hP1; exact (Real.rpow_le_rpow_left_iff hq1).1 hP1
  have hm2 : m ≤ 485 / 1000 * (2333 / 1000) := by
    rw [hPm] at hP2; exact (Real.rpow_le_rpow_left_iff hq1).1 hP2
  -- the heights
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = (q : ℝ) ^ η := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := hH ▸ Real.one_le_rpow hq1.le hη.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * H + 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have hT3 : T ≤ 3 * (q : ℝ) ^ η := by rw [hT, ← hH]; linarith
  have hQh' : ∀ j < K, 4 ≤ Q j ∧ |h j| + H + 1 ≤ T := fun j hj =>
    ⟨hqe.trans (hQh j hj).1, by have := (hQh j hj).2; rw [hT, hH]; rw [hH] at hH1; linarith⟩
  -- each scale is at most `q^U`
  have hQ1 : ∀ j < K, 1 ≤ Q j := fun j hj => by linarith [(hQh' j hj).1]
  have hQU : ∀ j < K, Q j ≤ (q : ℝ) ^ U := by
    intro j hj
    have hjK : j ∈ Finset.range K := Finset.mem_range.2 hj
    have hrest : 1 ≤ ∏ k ∈ (Finset.range K).erase j, Q k := Finset.one_le_prod₀ fun k hk =>
      hQ1 k (Finset.mem_range.1 (Finset.mem_of_mem_erase hk))
    have hQj := Finset.mul_prod_erase (Finset.range K) Q hjK
    have hQj0 : 0 ≤ Q j := by linarith [hQ1 j hj]
    have hqL : 0 ≤ (q : ℝ) ^ (2333 / 1000 : ℝ) := Real.rpow_nonneg hq0.le _
    calc Q j ≤ Q j * ∏ k ∈ (Finset.range K).erase j, Q k := le_mul_of_one_le_right hQj0 hrest
      _ = ∏ k ∈ Finset.range K, Q k := hQj
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) / P := hprod
      _ ≤ 2 ^ K₀ * (q : ℝ) ^ (2333 / 1000 : ℝ) := div_le_self (mul_nonneg (by norm_num) hqL) hPge1
      _ ≤ (q : ℝ) * (q : ℝ) ^ (2333 / 1000 : ℝ) := mul_le_mul_of_nonneg_right hq2K hqL
      _ = (q : ℝ) ^ U := by
          rw [hU, show (3333 / 1000 : ℝ) = 1 + 2333 / 1000 by norm_num, Real.rpow_add hq0, Real.rpow_one]
  -- the pointwise bound
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hδ1 : δ ≤ 1 / 24 := by rw [hδ]; norm_num
  have hptq := hpt q βg 500000 (by norm_num) βg_top (fun i hi => βg_range hi) T δ H hδ0 hδ1 (by linarith)
    K Q h hQh' P S hS a h₀
  refine hptq.trans ?_
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∑ m ∈ S, ‖a m‖ ^ 2 := ⟨_, rfl⟩
  rw [← hV]
  have hbin : ∀ i ∈ Finset.range 500000,
      (∏ j ∈ Finset.range K, MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) *
        Real.sqrt (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin βg 500000 T χ = i).card *
          Real.sqrt ((P + q) * V) ≤
        C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 * (q : ℝ) ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) *
          Real.sqrt (V / P) := by
    intro i hi
    have hi' : i < 500000 := Finset.mem_range.1 hi
    have hβi := βg_range hi'.le
    have hβi1 := βg_range (Nat.succ_le_of_lt hi')
    have hθ0 : 0 ≤ βg (i + 1) + 2 * δ := by linarith [hβi1.1]
    have hθ1 : βg (i + 1) + 2 * δ ≤ 1 := by rw [hδ]; linarith [hβi1.2]
    have hMp := prod_MB_le (M := fun j => MB q Bc Cc Kd (βg (i + 1)) δ H (Q j) (h j)) (Q := Q)
      (θ' := βg (i + 1) + 2 * δ) hK hq0 hP0 hθ0 hθ1
      (fun j hj => MB_nonneg hBc hCc hβi1.2 hδ0 hδ1 (by linarith) (by linarith [(hQh' j hj).1]))
      (fun j hj => by
        rw [hH]
        exact hMB q hq₁ _ _ _ hβi1.1 hβi1.2 (hKLle (i + 1) (by omega)) (hQh j hj).1 (hQU j hj) (hQh j hj).2)
      hQ1 hprod
    have he : βg (i + 1) + 2 * δ = βg i + (1 / 1200000 + 2 * δ) := by rw [βg_succ]; ring
    rw [he] at hMp
    have hcnt := card_bin_step (q := q) (β := βg) (N := 500000) (by norm_num) βg_zero
      (fun k hk => ⟨(βg_range hk.le).1, by linarith [(βg_range hk.le).2]⟩) hT2
      (fun σ h1 h2 => hCd q σ T h1 h2 hT2) hi'
    have hw0 : (0 : ℝ) ≤ 1 / 1200000 + 2 * δ := by linarith
    have hw1 : 1 / 1200000 + 2 * δ ≤ 4 / 10 ^ 6 := by rw [hδ]; norm_num
    have hb := bin_bound (V := V) hq1 hPm hm1 hm2 hT1 hT3 hβi.1 hβi.2 hw0 hw1
      (by positivity : (0 : ℝ) ≤ 2 ^ K₀ * 2 ^ K₀) (le_trans zero_le_one (le_max_right Cd 1)) hMp hcnt
    rw [hC₁]
    exact hb
  refine (Finset.sum_le_sum hbin).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- absorbing the constants
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1.le
  have hlogT : 1 + Real.log ((q : ℝ) * T) ≤ 3 * (1 + Real.log q) := by
    have hT0 : 0 < T := by linarith
    have h1 : Real.log ((q : ℝ) * T) = Real.log q + Real.log T := Real.log_mul hq0.ne' hT0.ne'
    have h2 : Real.log T ≤ Real.log 3 + η * Real.log q := by
      rw [← Real.log_rpow hq0, ← Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hq0 η).ne']
      exact Real.log_le_log hT0 hT3
    have h3 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h4 : η * Real.log q ≤ Real.log q := by
      have : η ≤ 1 := by linarith
      exact mul_le_of_le_one_left hlq this
    linarith
  have hqT1 : 1 ≤ (q : ℝ) * T := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (q : ℝ) * T := mul_le_mul hq1.le hT1 zero_le_one hq0.le
  have hlq0 : 0 ≤ 1 + Real.log ((q : ℝ) * T) := by linarith [Real.log_nonneg hqT1]
  have habs : 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 ≤ (q : ℝ) ^ (3 / 200000 : ℝ) := by
    have h := hQ₂ (q : ℝ) hqQ₂
    calc 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 ≤ 500000 * C₁ * (3 * (1 + Real.log q)) ^ 5 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlq0 hlogT 5) (by linarith)
      _ = 500000 * C₁ * 3 ^ 5 * (1 + Real.log q) ^ 5 := by ring
      _ ≤ (q : ℝ) ^ (3 / 200000 : ℝ) := h
  have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  have hE : 0 ≤ (q : ℝ) ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) := Real.rpow_nonneg hq0.le _
  have hfin : (q : ℝ) ^ (3 / 200000 : ℝ) * (q : ℝ) ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) ≤
      (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  calc (500000 : ℝ) * (C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 * (q : ℝ) ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) *
        Real.sqrt (V / P)) = 500000 * C₁ * (1 + Real.log ((q : ℝ) * T)) ^ 5 *
        (q : ℝ) ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) * Real.sqrt (V / P) := by ring
    _ ≤ (q : ℝ) ^ (3 / 200000 : ℝ) * (q : ℝ) ^ (2333 / 1000 - 1 / 25000 + η / 2 : ℝ) * Real.sqrt (V / P) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs hE) hVP
    _ ≤ (q : ℝ) ^ (2333 / 1000 - 1 / 50000 : ℝ) * Real.sqrt (V / P) :=
        mul_le_mul_of_nonneg_right hfin hVP

end Bins

end SieveTypeII

#print axioms SieveTypeII.card_class_le
#print axioms SieveTypeII.sum_chars_dp_sq_le
#print axioms SieveTypeII.sum_bins_le
#print axioms SieveTypeII.bin_rect
#print axioms SieveTypeII.card_bin_le
#print axioms SieveTypeII.sum_typeII_bins
#print axioms SieveTypeII.typeII_pointwise
#print axioms SieveTypeII.card_zero_step
#print axioms SieveTypeII.MB_le
#print axioms SieveTypeII.exponent_le
#print axioms SieveTypeII.qpow_combine
#print axioms SieveTypeII.bin_bound
#print axioms SieveTypeII.typeII_step
