import EisensteinQuadSieveLattice

/-! # The quadratic large sieve, part 4c: square parts, squarefree rows and `B(M, N, K)` (round 349)

S5e of round 312's plan, the third piece of S5e-4 as replanned in round 348.

* **The square part is unique** (`sqfree_sq_unique`, `elt_sqfree_sq_unique`): `D·E² = D'·E'²` with
  `D, D'` squarefree ideals and `E ≠ ⊥` gives `D = D'`, `E = E'`; for elements, `d·e² = d'·e'²`
  with `(d), (d')` squarefree and `e ≠ 0` gives `e' = u·e`, `d = u²·d'` for a unit `u`. With round
  339's `exists_sq_mul_sqfree` this defines the squarefree kernel and square part of a nonzero
  element (`sqk`, `sqe`, `sqk_spec`) and `s(m) = N(sqk m)` (`sqN`), with `s(d·e²) = N(d)`
  (`sqN_sqf_mul_sq`).
* **Sums over `d·e²`** (`sum_sqf_sq`, `sum_sqf_sq_iter`): for `f` summable with `f(0) = 0`,
  `Σ_{(d,e) : (d) squarefree} f(d·e²) = w·Σ_μ f(μ)` with `w` the number of units, by the injection
  `(u, μ) ↦ (u⁻²·sqk μ, u·sqe μ)` from units and nonzero elements onto the pairs with `e ≠ 0`
  (`sqParam`).
* **Squarefree rows from admissible rows** (`exists_sqf_split`, `fBound_sqf_of_adm`): every
  squarefree `d` is `u·gen 𝔱·k` with `𝔱` among round 342's `tIdeals 1` and `k` admissible of norm at
  most `N(d)` (round 342's `exists_row_split`), so the norm over the squarefree rows of norm at
  most `Y` (`sqfW`) is at most `w·|tIdeals 1|` times the norm over the admissible ones.
* **Heath-Brown's (11) over balls** (`bw`, `fBound_admW_split`): the rows of `B(M, N, K)` carry the
  majorant `Φ(σm/√M)` on the arguments with `s(m) > K`. Every admissible row of norm at most `M` is
  either of norm at most `K` or such a row with weight at least `1`, so
  `FBound (admW K) N Δ₁` and `FBound (bw M K) N Δ₂` give `FBound (admW M) N (Δ₁ + Δ₂)` (through
  `FBound.of_le_add`).
-/

open Complex NumberField Ideal UniqueFactorizationMonoid
open scoped Classical

noncomputable section

namespace Eis

/-- **The square part of an ideal is unique**: `D·E² = D'·E'²` with `D, D'` squarefree and `E ≠ ⊥`
gives `D = D'` and `E = E'`. -/
theorem sqfree_sq_unique {D D' E E' : Ideal (𝓞 K)} (hD : Squarefree D) (hD' : Squarefree D')
    (hE : E ≠ ⊥) (h : D * E ^ 2 = D' * E' ^ 2) : D = D' ∧ E = E' := by
  have hD0 : D ≠ ⊥ := hD.ne_zero
  have hD'0 : D' ≠ ⊥ := hD'.ne_zero
  have hE2 : E ^ 2 ≠ ⊥ := pow_ne_zero 2 hE
  have hE' : E' ≠ ⊥ := by
    rintro rfl
    have h0 : D' * (⊥ : Ideal (𝓞 K)) ^ 2 = ⊥ := by simp
    rw [h0, Ideal.mul_eq_bot] at h
    rcases h with h | h
    · exact hD0 h
    · exact hE2 h
  have hE'2 : E' ^ 2 ≠ ⊥ := pow_ne_zero 2 hE'
  have hnf := congrArg normalizedFactors h
  rw [normalizedFactors_mul hD0 hE2, normalizedFactors_mul hD'0 hE'2, normalizedFactors_pow,
    normalizedFactors_pow] at hnf
  have hnd := (squarefree_iff_nodup_normalizedFactors hD0).1 hD
  have hnd' := (squarefree_iff_nodup_normalizedFactors hD'0).1 hD'
  have hc : ∀ P, Multiset.count P (normalizedFactors D) = Multiset.count P (normalizedFactors D') ∧
      Multiset.count P (normalizedFactors E) = Multiset.count P (normalizedFactors E') := by
    intro P
    have h1 := congrArg (Multiset.count P) hnf
    simp only [Multiset.count_add, Multiset.count_nsmul] at h1
    have a1 := Multiset.nodup_iff_count_le_one.1 hnd P
    have a2 := Multiset.nodup_iff_count_le_one.1 hnd' P
    omega
  have hDD : normalizedFactors D = normalizedFactors D' := Multiset.ext.2 fun P => (hc P).1
  have hEE : normalizedFactors E = normalizedFactors E' := Multiset.ext.2 fun P => (hc P).2
  exact ⟨associated_iff_eq.1 ((associated_iff_normalizedFactors_eq_normalizedFactors hD0 hD'0).2 hDD),
    associated_iff_eq.1 ((associated_iff_normalizedFactors_eq_normalizedFactors hE hE').2 hEE)⟩

/-- **The square part of an element is unique up to a unit**: `d·e² = d'·e'²` with `(d), (d')`
squarefree and `e ≠ 0` gives `e' = u·e` and `d = u²·d'` for a unit `u`. -/
theorem elt_sqfree_sq_unique {d d' e e' : 𝓞 K} (hd : Squarefree (span {d}))
    (hd' : Squarefree (span {d'})) (he : e ≠ 0) (h : d * e ^ 2 = d' * e' ^ 2) :
    ∃ u : (𝓞 K)ˣ, e' = u * e ∧ d = u ^ 2 * d' := by
  have hspan : span {d} * span {e} ^ 2 = span {d'} * span {e'} ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, h]
  have hE : span {e} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨_, hEE⟩ := sqfree_sq_unique hd hd' hE hspan
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.1 hEE)
  refine ⟨u, by rw [← hu, mul_comm], ?_⟩
  have he2 : e ^ 2 ≠ 0 := pow_ne_zero 2 he
  rw [← hu, mul_pow] at h
  apply mul_right_cancel₀ he2
  rw [h]; ring

/-- The square part: `sqe m` with `m = sqk m · sqe m²` and `(sqk m)` squarefree, for `m ≠ 0`. -/
def sqe (m : 𝓞 K) : 𝓞 K :=
  if h : m = 0 then 0 else gen (Classical.choose (exists_sq_mul_sqfree h))

/-- The squarefree kernel: `m = sqk m · sqe m²` with `(sqk m)` squarefree, for `m ≠ 0`. -/
def sqk (m : 𝓞 K) : 𝓞 K :=
  if h : m = 0 then 0 else Classical.choose (Classical.choose_spec (exists_sq_mul_sqfree h))

theorem sqk_spec {m : 𝓞 K} (hm : m ≠ 0) :
    m = sqk m * sqe m ^ 2 ∧ Squarefree (span {sqk m}) ∧ sqe m ≠ 0 := by
  have hs := Classical.choose_spec (Classical.choose_spec (exists_sq_mul_sqfree hm))
  simp only [sqk, sqe, hm, ↓reduceDIte]
  exact ⟨hs.1, hs.2.1, gen_ne_zero hs.2.2.1⟩

/-- The norm of the squarefree kernel, `s(m) = N(sqk m)`. -/
def sqN (m : 𝓞 K) : ℝ := (absNorm (span {sqk m}) : ℝ)

/-- **`s(d·e²) = N(d)`** for `(d)` squarefree and `e ≠ 0`. -/
theorem sqN_sqf_mul_sq {d e : 𝓞 K} (hd : Squarefree (span {d})) (he : e ≠ 0) :
    sqN (d * e ^ 2) = (absNorm (span {d}) : ℝ) := by
  have hd0 : d ≠ 0 := by
    intro h; rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hd; exact hd.ne_zero rfl
  have hm : d * e ^ 2 ≠ 0 := mul_ne_zero hd0 (pow_ne_zero 2 he)
  obtain ⟨h1, h2, h3⟩ := sqk_spec hm
  obtain ⟨u, _, hu⟩ := elt_sqfree_sq_unique h2 hd h3 h1.symm
  simp only [sqN]
  rw [hu, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    Ideal.span_singleton_eq_top.2 (u.isUnit.pow 2), absNorm_top, one_mul]

/-- The parametrization `(u, μ) ↦ (u⁻²·sqk μ, u·sqe μ)` of the pairs `(d, e)` with `(d)` squarefree
and `e ≠ 0`, by a unit and the nonzero element `d·e²`. -/
def sqParam (x : (𝓞 K)ˣ × {μ : 𝓞 K // μ ≠ 0}) : 𝓞 K × 𝓞 K :=
  (((x.1⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 2 * sqk x.2.1, (x.1 : 𝓞 K) * sqe x.2.1)

theorem sqParam_prod (x : (𝓞 K)ˣ × {μ : 𝓞 K // μ ≠ 0}) :
    (sqParam x).1 * (sqParam x).2 ^ 2 = x.2.1 := by
  obtain ⟨u, μ, hμ⟩ := x
  have hu : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [sqParam]
  conv_rhs => rw [(sqk_spec hμ).1]
  calc ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 2 * sqk μ * ((u : 𝓞 K) * sqe μ) ^ 2
      = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (u : 𝓞 K)) ^ 2 * (sqk μ * sqe μ ^ 2) := by ring
    _ = sqk μ * sqe μ ^ 2 := by rw [hu, one_pow, one_mul]

theorem sqParam_sqf (x : (𝓞 K)ˣ × {μ : 𝓞 K // μ ≠ 0}) : Squarefree (span {(sqParam x).1}) := by
  obtain ⟨u, μ, hμ⟩ := x
  simp only [sqParam]
  rw [← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.2 ((u⁻¹).isUnit.pow 2), Ideal.top_mul]
  exact (sqk_spec hμ).2.1

theorem sqParam_injective : Function.Injective sqParam := by
  rintro ⟨u, μ, hμ⟩ ⟨v, ν, hν⟩ h
  have hμν : μ = ν := by
    have h1 := sqParam_prod ⟨u, μ, hμ⟩
    have h2 := sqParam_prod ⟨v, ν, hν⟩
    rw [h] at h1
    exact h1.symm.trans h2
  subst hμν
  have h2 := congrArg Prod.snd h
  simp only [sqParam] at h2
  have huv : (u : 𝓞 K) = v := mul_right_cancel₀ (sqk_spec hμ).2.2 h2
  rw [Units.ext huv]

theorem sqParam_range {p : 𝓞 K × 𝓞 K} (hp : Squarefree (span {p.1})) (h : p.1 * p.2 ^ 2 ≠ 0) :
    p ∈ Set.range sqParam := by
  set μ := p.1 * p.2 ^ 2 with hμdef
  have he : p.2 ≠ 0 := fun h0 => h (by rw [hμdef, h0]; ring)
  obtain ⟨h1, h2, h3⟩ := sqk_spec h
  obtain ⟨u, hu1, hu2⟩ := elt_sqfree_sq_unique h2 hp h3 h1.symm
  refine ⟨⟨u, μ, h⟩, ?_⟩
  simp only [sqParam]
  refine Prod.ext ?_ ?_
  · show ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 2 * sqk μ = p.1
    rw [hu2, ← mul_assoc, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow,
      one_mul]
  · exact hu1.symm

/-- **Sums over `d·e²`**: for `f` summable with `f(0) = 0`, the pairs `(d, e)` with `(d)` squarefree
give `Σ_{(d,e)} f(d·e²) = w·Σ_μ f(μ)`, `w` the number of units, and the family is summable. -/
theorem sum_sqf_sq (f : 𝓞 K → ℂ) (hf : Summable f) (h0 : f 0 = 0) :
    Summable (fun p : 𝓞 K × 𝓞 K => if Squarefree (span {p.1}) then f (p.1 * p.2 ^ 2) else 0) ∧
      ∑' p : 𝓞 K × 𝓞 K, (if Squarefree (span {p.1}) then f (p.1 * p.2 ^ 2) else 0) =
        (Fintype.card (𝓞 K)ˣ : ℂ) * ∑' μ, f μ := by
  set g : 𝓞 K × 𝓞 K → ℂ := fun p => if Squarefree (span {p.1}) then f (p.1 * p.2 ^ 2) else 0
    with hg
  have hcomp : ∀ x, g (sqParam x) = f x.2.1 := fun x => by
    simp only [hg, sqParam_sqf x, ite_true, sqParam_prod]
  have hsupp : ∀ p ∉ Set.range sqParam, g p = 0 := by
    intro p hp
    simp only [hg]
    split_ifs with hs
    · by_contra hne
      exact hp (sqParam_range hs fun h => hne (by rw [h, h0]))
    · rfl
  -- the sum over units × nonzero elements
  set A := {μ : 𝓞 K // μ ≠ 0}
  have hfA : Summable fun a : A => f a.1 := hf.subtype _
  have hprodS : Summable fun x : (𝓞 K)ˣ × A => f x.2.1 := by
    refine Summable.of_norm ?_
    refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨fun _ => hfA.norm, ?_⟩
    exact Summable.of_finite
  have hgc : Summable (g ∘ sqParam) := hprodS.congr fun x => (hcomp x).symm
  have hgS : Summable g := (sqParam_injective.summable_iff hsupp).1 hgc
  refine ⟨hgS, ?_⟩
  rw [← sqParam_injective.tsum_eq (fun p hp => by
    by_contra h; exact hp (hsupp p h))]
  rw [tsum_congr hcomp, hprodS.tsum_prod' (fun _ => hfA), tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact tsum_subtype_eq_of_support_subset (s := {μ : 𝓞 K | μ ≠ 0})
    (fun μ hμ hz => hμ (by rw [hz]; exact h0))

/-- **Sums over `d·e²`, iterated**: `Σ_{(d) squarefree} Σ_e f(d·e²) = w·Σ_μ f(μ)`. -/
theorem sum_sqf_sq_iter (f : 𝓞 K → ℂ) (hf : Summable f) (h0 : f 0 = 0) :
    (∀ d : 𝓞 K, Squarefree (span {d}) → Summable fun e : 𝓞 K => f (d * e ^ 2)) ∧
    ∑' d : 𝓞 K, (if Squarefree (span {d}) then ∑' e : 𝓞 K, f (d * e ^ 2) else 0) =
      (Fintype.card (𝓞 K)ˣ : ℂ) * ∑' μ, f μ := by
  obtain ⟨hs, heq⟩ := sum_sqf_sq f hf h0
  refine ⟨fun d hd => ?_, ?_⟩
  · refine (hs.prod_factor d).congr fun e => ?_
    simp only [hd, ite_true]
  · rw [hs.tsum_prod' (fun d => hs.prod_factor d)] at heq
    rw [← heq]
    refine tsum_congr fun d => ?_
    split_ifs with hd
    · rfl
    · simp

/-- The squarefree rows of norm at most `Y`. -/
def sqfW (Y : ℝ) (d : 𝓞 K) : ℝ :=
  if Squarefree (span {d}) ∧ (absNorm (span {d}) : ℝ) ≤ Y then 1 else 0

theorem sqfW_nonneg (Y : ℝ) (d : 𝓞 K) : 0 ≤ sqfW Y d := by
  unfold sqfW; split_ifs <;> norm_num

/-- **Every squarefree row is a bounded multiple of an admissible row**: `d = c·k` with `c` among
the `w·|tIdeals 1|` elements `u·gen 𝔱` and `k` admissible of norm at most `N(d)`. -/
theorem exists_sqf_split {d : 𝓞 K} (hd : Squarefree (span {d})) :
    ∃ (u : (𝓞 K)ˣ) (T : tIdeals 1) (k : 𝓞 K), d = u * gen T.1 * k ∧ QAdm k ∧
      (absNorm (span {k}) : ℝ) ≤ absNorm (span {d}) := by
  have hd0 : d ≠ 0 := by
    intro h; rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hd; exact hd.ne_zero rfl
  obtain ⟨u, T, k, hdk, hT, hT0, -, hk1, hk2, hk3, -, hN⟩ := exists_row_split hd0 hd one_ne_zero
  refine ⟨u, ⟨T, hT⟩, k, hdk, ⟨hk1, hk2, hk3⟩, ?_⟩
  have hT1 : 1 ≤ absNorm T := Nat.one_le_iff_ne_zero.2 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  rw [hN]
  exact_mod_cast Nat.le_mul_of_pos_left _ hT1

/-- **The norm over squarefree rows from the norm over admissible rows**: with the admissible
arguments of norm at most `Y` as rows, `Δ` serves for every column family; with the squarefree
ones, `w·|tIdeals 1|·Δ` does. -/
theorem fBound_sqf_of_adm {Y N Δ : ℝ} (hΔ : 0 ≤ Δ) (h : FBound (admW Y) N Δ) :
    FBound (sqfW Y) N ((Fintype.card (𝓞 K)ˣ * Fintype.card (tIdeals 1) : ℕ) * Δ) := by
  intro 𝒩 α h𝒩
  set F : 𝓞 K → ℝ := fun m => ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 with hF
  have hF0 : ∀ m, 0 ≤ F m := fun m => sq_nonneg _
  have hFb : ∀ m, F m ≤ (∑ A ∈ 𝒩, ‖α A‖) ^ 2 := fun m => by
    simp only [hF]; gcongr; exact norm_q2Sum_le 𝒩 α m
  -- the index set and its weight
  set ι := (𝓞 K)ˣ × tIdeals 1 × 𝓞 K
  set G : ι → ℝ := fun x => admW Y x.2.2 * F ((x.1 : 𝓞 K) * gen x.2.1.1 * x.2.2) with hG
  have hG0 : ∀ x, 0 ≤ G x := fun x => mul_nonneg (admW_nonneg _ _) (hF0 _)
  have hGs : Summable G := by
    have hslice : ∀ c : (𝓞 K)ˣ × tIdeals 1, Summable fun k : 𝓞 K =>
        admW Y k * F ((c.1 : 𝓞 K) * gen c.2.1 * k) := fun c =>
      ((summable_admW Y).mul_right ((∑ A ∈ 𝒩, ‖α A‖) ^ 2)).of_nonneg_of_le
        (fun k => mul_nonneg (admW_nonneg _ _) (hF0 _))
        (fun k => mul_le_mul_of_nonneg_left (hFb _) (admW_nonneg _ _))
    rw [← (Equiv.prodAssoc (𝓞 K)ˣ (tIdeals 1) (𝓞 K)).summable_iff]
    refine (summable_prod_of_nonneg (fun x => hG0 _)).2 ⟨fun c => (hslice c).congr fun k => rfl,
      Summable.of_finite⟩
  -- the rows in the support, injected into the index set
  set Sup := ↥({d : 𝓞 K | Squarefree (span {d}) ∧ (absNorm (span {d}) : ℝ) ≤ Y} : Set (𝓞 K))
  have hsplit : ∀ d : Sup, ∃ x : ι, d.1 = (x.1 : 𝓞 K) * gen x.2.1.1 * x.2.2 ∧ QAdm x.2.2 ∧
      (absNorm (span {x.2.2}) : ℝ) ≤ Y := by
    intro d
    obtain ⟨u, T, k, hdk, hk, hN⟩ := exists_sqf_split d.2.1
    exact ⟨(u, T, k), hdk, hk, hN.trans d.2.2⟩
  choose e he using hsplit
  have he_inj : Function.Injective e := by
    intro d d' hdd
    apply Subtype.ext
    rw [(he d).1, (he d').1, hdd]
  have hle : ∀ d : Sup, F d.1 ≤ G (e d) := by
    intro d
    simp only [hG, admW, (he d).2.1, (he d).2.2, and_self, ite_true, one_mul]
    rw [← (he d).1]
  -- the sum over the squarefree rows
  have hLHS : ∑' m : 𝓞 K, sqfW Y m * F m = ∑' d : Sup, F d.1 := by
    rw [← tsum_subtype_eq_of_support_subset (s := {d : 𝓞 K | Squarefree (span {d}) ∧
      (absNorm (span {d}) : ℝ) ≤ Y}) (fun m hm => by
        by_contra hc
        apply hm
        have hc' : ¬ (Squarefree (span {m}) ∧ (absNorm (span {m}) : ℝ) ≤ Y) := hc
        simp only [sqfW, hc', ite_false, zero_mul])]
    refine tsum_congr fun d => ?_
    have hd : Squarefree (span {d.1}) ∧ (absNorm (span {d.1}) : ℝ) ≤ Y := d.2
    simp only [sqfW, hd, and_self, ite_true, one_mul]
  have hSs : Summable fun d : Sup => F d.1 :=
    (hGs.comp_injective he_inj).of_nonneg_of_le (fun d => hF0 _) hle
  show ∑' m : 𝓞 K, sqfW Y m * F m ≤ _
  rw [hLHS]
  refine (hSs.tsum_le_tsum_of_inj e he_inj (fun c _ => hG0 c) hle hGs).trans ?_
  -- the sum over the index set, slice by slice
  let e3 := Equiv.prodAssoc (𝓞 K)ˣ (tIdeals 1) (𝓞 K)
  rw [← e3.tsum_eq]
  have hGs' : Summable (G ∘ e3) := (e3.summable_iff).2 hGs
  show ∑' c, (G ∘ e3) c ≤ _
  rw [hGs'.tsum_prod' (fun c => (hGs'.prod_factor c)), tsum_fintype]
  have hslice : ∀ c : (𝓞 K)ˣ × tIdeals 1,
      ∑' k : 𝓞 K, (G ∘ e3) (c, k) ≤ Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := by
    intro c
    have hb := h 𝒩 (fun A => α A * q2 A ((c.1 : 𝓞 K) * gen c.2.1)) h𝒩
    calc ∑' k : 𝓞 K, (G ∘ e3) (c, k)
        = ∑' k : 𝓞 K, admW Y k *
            ‖∑ A ∈ 𝒩, α A * q2 A ((c.1 : 𝓞 K) * gen c.2.1) * q2 A k‖ ^ 2 := by
          refine tsum_congr fun k => ?_
          simp only [Function.comp_apply, hG, hF, e3, Equiv.prodAssoc_apply, q2_mul, mul_assoc]
      _ ≤ Δ * ∑ A ∈ 𝒩, ‖α A * q2 A ((c.1 : 𝓞 K) * gen c.2.1)‖ ^ 2 := hb
      _ ≤ Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := by
          gcongr with A
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (norm_q2_le _ _)
  calc ∑ c : (𝓞 K)ˣ × tIdeals 1, ∑' k : 𝓞 K, (G ∘ e3) (c, k)
      ≤ ∑ _c : (𝓞 K)ˣ × tIdeals 1, Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := Finset.sum_le_sum fun c _ => hslice c
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast; ring

/-- **Weights add**: if `0 ≤ w ≤ w₁ + w₂` with `w₁, w₂` summable, the norms add. -/
theorem FBound.of_le_add {w w₁ w₂ : 𝓞 K → ℝ} {N Δ₁ Δ₂ : ℝ} (h0 : ∀ m, 0 ≤ w m)
    (hle : ∀ m, w m ≤ w₁ m + w₂ m)
    (hs₁ : Summable w₁) (hs₂ : Summable w₂) (hb₁ : FBound w₁ N Δ₁) (hb₂ : FBound w₂ N Δ₂) :
    FBound w N (Δ₁ + Δ₂) := by
  intro 𝒩 α h𝒩
  have hs : Summable w := (hs₁.add hs₂).of_nonneg_of_le h0 hle
  have hS1 := summable_w_colSum hs₁ 𝒩 α
  have hS2 := summable_w_colSum hs₂ 𝒩 α
  calc ∑' m, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2
      ≤ ∑' m, (w₁ m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 + w₂ m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2) :=
        (summable_w_colSum hs 𝒩 α).tsum_le_tsum (fun m => by
          rw [← add_mul]; exact mul_le_mul_of_nonneg_right (hle m) (sq_nonneg _)) (hS1.add hS2)
    _ = ∑' m, w₁ m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 + ∑' m, w₂ m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 :=
        hS1.tsum_add hS2
    _ ≤ Δ₁ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 + Δ₂ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 :=
        add_le_add (hb₁ 𝒩 α h𝒩) (hb₂ 𝒩 α h𝒩)
    _ = (Δ₁ + Δ₂) * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := by ring

/-- **The rows of Heath-Brown's `B(M, N, K)`**: the majorant `Φ(σm/√M)` on the arguments whose
squarefree kernel has norm above `K`. -/
def bw (M Kt : ℝ) (m : 𝓞 K) : ℝ :=
  if Kt < sqN m then (Majorant.Phi (σO m / (Real.sqrt M : ℂ))).re else 0

theorem bw_nonneg (M Kt : ℝ) (m : 𝓞 K) : 0 ≤ bw M Kt m := by
  unfold bw; split_ifs
  · exact Majorant.Phi_re_nonneg _
  · exact le_rfl

theorem summable_bw {M : ℝ} (hM : 0 < M) (Kt : ℝ) : Summable (bw M Kt) := by
  have hb : ((Real.sqrt M)⁻¹ : ℂ) ≠ 0 := by
    rw [ne_eq, inv_eq_zero]; exact_mod_cast (Real.sqrt_pos.2 hM).ne'
  have hs := summable_σO (affS Majorant.Phi 0 ((Real.sqrt M)⁻¹ : ℂ) hb)
  refine Summable.of_norm_bounded hs.norm fun m => ?_
  rw [affS_apply, zero_add, ← div_eq_inv_mul, Real.norm_of_nonneg (bw_nonneg _ _ _)]
  unfold bw; split_ifs
  · exact Complex.re_le_norm _
  · exact norm_nonneg _

/-- `s(k) = N(k)` for `(k)` squarefree. -/
theorem sqN_of_sqf {k : 𝓞 K} (hk : Squarefree (span {k})) : sqN k = (absNorm (span {k}) : ℝ) := by
  have h := sqN_sqf_mul_sq hk one_ne_zero
  rwa [one_pow, mul_one] at h

/-- **Heath-Brown's (11) over balls**: the admissible arguments of norm at most `M` are those of
norm at most `K` together with rows of `B(M, N, K)`, so
`FBound (admW K) N Δ₁ → FBound (bw M K) N Δ₂ → FBound (admW M) N (Δ₁ + Δ₂)`. -/
theorem fBound_admW_split {M Kt N Δ₁ Δ₂ : ℝ} (hM : 0 < M) (h₁ : FBound (admW Kt) N Δ₁)
    (h₂ : FBound (bw M Kt) N Δ₂) : FBound (admW M) N (Δ₁ + Δ₂) := by
  refine FBound.of_le_add (admW_nonneg M) (fun m => ?_)
    (summable_admW Kt) (summable_bw hM Kt) h₁ h₂
  unfold admW
  split_ifs with hm hK hK
  · linarith [bw_nonneg M Kt m]
  · rw [zero_add]
    have hlt : Kt < (absNorm (span {m}) : ℝ) := lt_of_not_ge fun h => hK ⟨hm.1, h⟩
    unfold bw
    rw [sqN_of_sqf hm.1.2.1]
    split_ifs
    refine Majorant.one_le_Phi_re _ ?_
    have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, div_le_one hs,
      ← Real.sqrt_sq (norm_nonneg _), sq_norm_σO]
    exact Real.sqrt_le_sqrt hm.2
  · linarith [bw_nonneg M Kt m]
  · linarith [bw_nonneg M Kt m]

end Eis

end

#print axioms Eis.sqfree_sq_unique
#print axioms Eis.elt_sqfree_sq_unique
#print axioms Eis.sqk_spec
#print axioms Eis.sqN_sqf_mul_sq
#print axioms Eis.sqParam_injective
#print axioms Eis.sum_sqf_sq
#print axioms Eis.sum_sqf_sq_iter
#print axioms Eis.exists_sqf_split
#print axioms Eis.fBound_sqf_of_adm
#print axioms Eis.FBound.of_le_add
#print axioms Eis.summable_bw
#print axioms Eis.fBound_admW_split
