import EisensteinMeanSquareRowCol

/-! # The bilinear bound for one block of rows (round 309)

S4 of round 291's plan, part 9: the analytic step of the companion paper's proof of its
Proposition 4.5 for one excluded ideal `b` and one dyadic range of `N(f)`. Round 308's row/column
form meets round 306's two-family bilinear bound and its Lemma 4.4 under (4.12).

* **The column sums over subsets** (`colSum_eq_powerset`): round 305's `colSum ξ W X (idl b) k f`, a
  sum over all ideals, is `Σ_{M⊆U∖b} colA ξ k f M · W(N(M)/X)` when `W` vanishes beyond `β'` and `U`
  contains the primes of norm at most `β'X` (`dvd_idl_iff`, `isRelPrime_idl`).
* **Conjugated test functions** (`contDiff_conj_comp`, `norm_iteratedDeriv_conj_comp`):
  `x ↦ conj U(x)` is smooth with the same derivative norms (Mathlib's
  `LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`).
* **Rows** (`Row`, `rowF`, `rowK`, `rowFe`): a row is `(T, V, μ)`, the paper's `(e, v, h)`, with
  `f = T ∪ V` and `k = d_T μ`. **`row_injective`**: for disjoint `T, V` and `μ` prime to the primes of
  `V`, the row is determined by `(f, k)`, since `T` is the set of primes of `f` dividing `k`. This is
  the part of the paper's "bijective change of variables" that the bound uses.
* **The column mean squares** (`rows_colMeanSquare`): from round 306's `dualMeanSquare_excl`,
  supplied as a hypothesis in the form it takes at fixed `D, B, F`, every test function in the
  support of `V` with its first `J` derivatives bounded by `N` satisfies
  `Σ_r |Σ_n conj(colA ξ k_r f_r n)·U(N(n)/X)|² ≤ 4^{|b|}·K·Z^ε·(Z/B)²·N²`. The rows map injectively
  into the dual mean square's rows `(f, k)`.
* **The bilinear form** (`rcTerm_eq_bilinear`, `rowSum_eq_bilinear`): with `X = Z/(N(b)F)`,
  `ρ_r = N(f)/F` and `x_n = N(n)/X`, a row's double column sum is
  `2H·N(b)/(√3·Z)·w_r·Σ_{n₁,n₂⊆U∖b} …`, the shape of round 306's `bilinear_dual_bound₂`. The columns
  that meet `T ∪ V` contribute `0` (`colA_eq_zero_of_not_good`); `|w_r| ≤ 1` (`norm_wRow_le`) and
  `A_r ≥ H·N(b)²/(3Z²)` (`ARow_ge`).
* **`rowBlock_bound`**: `|Σ_{rows} Σ_{M₁,M₂} rcTerm| ≤ 2H·N(b)/(√3·Z)·K·A_min^{−σ}·M_b`, given the
  conclusion of `bilinear_dual_bound₂` and the two column mean squares.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### The column sums over subsets -/

theorem prime_Pr (P : Pr) : Prime P.1 := Ideal.prime_of_isPrime (Pr_ne_bot P) P.2.1.isPrime

theorem dvd_idl_iff (P : Pr) (M : Finset Pr) : P.1 ∣ idl M ↔ P ∈ M := by
  constructor
  · intro h
    obtain ⟨Q, hQ, hd⟩ := (prime_Pr P).dvd_finsetProd_iff _ |>.1 h
    have hle : Q.1 ≤ P.1 := Ideal.le_of_dvd hd
    have : Q.1 = P.1 := Q.2.1.eq_of_le P.2.1.ne_top hle
    rwa [Subtype.ext this] at hQ
  · intro h; exact Finset.dvd_prod_of_mem _ h

theorem isRelPrime_idl {M b : Finset Pr} (h : Disjoint M b) : IsRelPrime (idl M) (idl b) := by
  rw [isRelPrime_iff_primeSet (idl_ne_bot M) (idl_coprime6 b) (idl_squarefree b), primeSet_idl]
  intro P hP hPM
  exact Finset.disjoint_left.1 h ((dvd_idl_iff P M).1 hPM) hP

/-- A column coefficient vanishes when a prime of the column divides `f`. -/
theorem colA_eq_zero (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (k f : 𝓞 K) {M : Finset Pr}
    {P : Pr} (hP : P ∈ M) (hf : πP P ∣ f) : colA ξ k f M = 0 := by
  unfold colA
  have h0 : chiS M f = 0 := by
    unfold chiS
    refine Finset.prod_eq_zero hP ?_
    rw [(mk_πP_eq_zero_iff P f).2 hf, MulChar.map_zero]
  rw [h0]; ring

theorem sym6_idl_eq (u : 𝓞 K) (M : Finset Pr) : sym6 u (idl M) = chiS M u := sym6_idl M u

open Classical in
/-- **The column sum as a sum over subsets**: if `W` vanishes beyond `β'`, `X > 0`, and `U` contains the
primes of norm at most `β'X`, then for `b ⊆ U`,
`colSum ξ W X (idl b) k f = Σ_{M⊆U∖b} colA ξ k f M · W(N(M)/X)`. -/
theorem colSum_eq_powerset (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β' : ℝ}
    (hW : ∀ x, β' < x → W x = 0) {X : ℝ} (hX : 0 < X) {U b : Finset Pr}
    (hU : primesLe (β' * X) ⊆ U) (k f : 𝓞 K) :
    colSum ξ W X (idl b) k f = ∑ M ∈ (U \ b).powerset, colA ξ k f M * W (nI M / X) := by
  unfold colSum
  rw [tsum_eq_sum (s := (U \ b).powerset.image idl)]
  · rw [Finset.sum_image (fun M _ M' _ h => by rw [← primeSet_idl M, h, primeSet_idl])]
    refine Finset.sum_congr rfl fun M hM => ?_
    have hd : Disjoint M b :=
      Finset.disjoint_of_subset_left (Finset.mem_powerset.1 hM) Finset.sdiff_disjoint
    rw [ite_eq_left (isRelPrime_idl hd), sym6_idl, sym6_idl]
    unfold colA nI; ring
  · intro I hI
    by_cases ha : (absNorm I).Coprime 6 ∧ Squarefree I
    · by_cases hrel : IsRelPrime I (idl b)
      · by_cases hw : W ((absNorm I : ℝ) / X) = 0
        · rw [hw, mul_zero]
        · exfalso
          apply hI
          have hle : (absNorm I : ℝ) ≤ β' * X := by
            by_contra hc; push Not at hc
            exact hw (hW _ (by rw [lt_div_iff₀ hX]; linarith))
          refine Finset.mem_image.2 ⟨primeSet I, Finset.mem_powerset.2 fun P hP => ?_,
            idl_primeSet ha.1 ha.2⟩
          rw [Finset.mem_sdiff]
          constructor
          · refine hU (mem_primesLe.2 ?_)
            have hPI : P.1 ∣ I := dvd_of_mem_normalizedFactors (mem_primeSet.1 hP)
            have h1 : absNorm P.1 ≤ absNorm I := Nat.le_of_dvd
              (Nat.pos_of_ne_zero (by rw [Ne, absNorm_eq_zero_iff]; exact ha.2.ne_zero))
              (absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hPI))
            exact Nat.le_floor (le_trans (by exact_mod_cast h1) hle)
          · intro hPb
            have hPI : P.1 ∣ I := dvd_of_mem_normalizedFactors (mem_primeSet.1 hP)
            have hPb' : P.1 ∣ idl b := (dvd_idl_iff P b).2 hPb
            exact P.2.1.ne_top (Ideal.isUnit_iff.1 (hrel hPI hPb'))
      · rw [ite_eq_right hrel]; ring
    · have h0 : aXi ξ I = 0 := by unfold aXi; rw [ite_eq_right ha]
      rw [h0]; split_ifs <;> ring

/-! ### Conjugated test functions -/

theorem contDiff_conj_comp {U : ℝ → ℂ} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ fun x => conj (U x) :=
  Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp hU

theorem norm_iteratedDeriv_conj_comp (U : ℝ → ℂ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j (fun x => conj (U x)) y‖ = ‖iteratedDeriv j U y‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left Complex.conjLIE U y j

/-! ### Rows -/

/-- A row `(T, V, μ)`: the paper's `(e, v, h)`. -/
abbrev Row := Finset Pr × Finset Pr × 𝓞 K

/-- The row's `f = ev` as a set of primes. -/
def rowF (r : Row) : Finset Pr := r.1 ∪ r.2.1

/-- The row's `k = eh`. -/
def rowK (r : Row) : 𝓞 K := eS r.1 * r.2.2

/-- The row's `f` as an element, `d_T·v`. -/
def rowFe (r : Row) : 𝓞 K := eS r.1 * eS r.2.1

theorem eS_union {A B : Finset Pr} (h : Disjoint A B) : eS (A ∪ B) = eS A * eS B := by
  unfold eS; rw [Finset.prod_union h]

theorem eS_ne_zero (A : Finset Pr) : eS A ≠ 0 := prod_πP_ne_zero A

theorem pgen_idl_rowF {r : Row} (h : Disjoint r.1 r.2.1) : pgen (idl (rowF r)) = rowFe r := by
  rw [pgen_idl]; unfold rowF rowFe; rw [← eS_union h]; rfl

open Classical in
/-- **The rows are determined by `(f, k)`** (the paper's "bijective change of variables",
used here only as an injection): for `T, V` disjoint and `μ` prime to the primes of `V`, `T` is the
set of primes of `f = T ∪ V` dividing `k = d_T μ`. -/
theorem row_injective {r r' : Row} (hd : Disjoint r.1 r.2.1) (hd' : Disjoint r'.1 r'.2.1)
    (hc : ∀ P ∈ r.2.1, ¬ πP P ∣ r.2.2) (hc' : ∀ P ∈ r'.2.1, ¬ πP P ∣ r'.2.2)
    (hf : idl (rowF r) = idl (rowF r')) (hk : rowK r = rowK r') : r = r' := by
  have hF : rowF r = rowF r' := by rw [← primeSet_idl (rowF r), hf, primeSet_idl]
  have key : ∀ (s : Row), Disjoint s.1 s.2.1 → (∀ P ∈ s.2.1, ¬ πP P ∣ s.2.2) →
      s.1 = (rowF s).filter (fun P => πP P ∣ rowK s) := by
    intro s hds hcs
    ext P
    rw [Finset.mem_filter]
    constructor
    · intro hP
      exact ⟨Finset.mem_union_left _ hP, dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hP) _⟩
    · rintro ⟨hP, hdvd⟩
      by_contra hPT
      have hPV : P ∈ s.2.1 := by
        rcases Finset.mem_union.1 hP with h | h
        · exact absurd h hPT
        · exact h
      rcases (prime_πP P).dvd_or_dvd hdvd with h | h
      · exact not_dvd_eS hPT h
      · exact hcs P hPV h
  have hT : r.1 = r'.1 := by
    rw [key r hd hc, key r' hd' hc', hF, hk]
  have hV : r.2.1 = r'.2.1 := by
    have e1 : r.2.1 = rowF r \ r.1 := by
      unfold rowF; rw [Finset.union_sdiff_left, hd.symm.sdiff_eq_left]
    have e2 : r'.2.1 = rowF r' \ r'.1 := by
      unfold rowF; rw [Finset.union_sdiff_left, hd'.symm.sdiff_eq_left]
    rw [e1, e2, hF, hT]
  have hμ : r.2.2 = r'.2.2 := by
    unfold rowK at hk
    rw [hT] at hk
    exact mul_left_cancel₀ (eS_ne_zero _) hk
  obtain ⟨T, V, μ⟩ := r
  obtain ⟨T', V', μ'⟩ := r'
  simp only at hT hV hμ
  rw [hT, hV, hμ]

open Classical in
/-- **The mean square of the column sums over the rows** (the hypothesis of round 306's
`bilinear_dual_bound₂`), from the dual mean square with the exclusion `b` removed (round 306's
`dualMeanSquare_excl`, supplied as `hexcl`): for every test function `U'` supported in the support of
`V ⊆ [α_V, β_V]` with its first `J` derivatives bounded by `N`,
`Σ_r |Σ_{n⊆U∖b} conj(colA ξ k_r f_r n)·U'(N(n)/X)|² ≤ 4^{|b|}·K·Z^ε·(Z/B)²·N²`. -/
theorem rows_colMeanSquare (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (J : ℕ) {αV βV : ℝ}
    (Kc ε1 Z B F Hc : ℝ) {b U : Finset Pr} {X : ℝ} (hX : X = Z / (B * F)) (hXpos : 0 < X)
    (hU : primesLe (βV * X) ⊆ U)
    (hexcl : ∀ W' : ℝ → ℂ, ContDiff ℝ ∞ W' → (∀ x, x < αV ∨ βV < x → W' x = 0) → ∀ N : ℝ,
      (∀ j ≤ J, ∀ x, ‖iteratedDeriv j W' x‖ ≤ N) →
      ∀ (Fs : Finset (Ideal (𝓞 K))) (Ks : Finset (𝓞 K)),
        (∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
          (absNorm f : ℝ) < 2 * F) →
        (∀ k ∈ Ks, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hc) →
        ∑ f ∈ Fs, ∑ k ∈ Ks, ‖colSum ξ W' (Z / (B * F)) (idl b) k (pgen f)‖ ^ 2 ≤
          4 ^ b.card * (Kc * N ^ 2 * Z ^ ε1 * (Z / B) ^ 2))
    (V : ℝ → ℂ) (hVs : tsupport V ⊆ Set.Icc αV βV) (rows : Finset Row)
    (hrows : ∀ r ∈ rows, Disjoint r.1 r.2.1 ∧ (∀ P ∈ r.2.1, ¬ πP P ∣ r.2.2) ∧ r.2.2 ≠ 0 ∧
      F ≤ nI (rowF r) ∧ nI (rowF r) < 2 * F ∧ (absNorm (span {rowK r}) : ℝ) ≤ Hc) :
    ∀ U' : ℝ → ℂ, ContDiff ℝ ∞ U' → tsupport U' ⊆ tsupport V → ∀ N : ℝ,
      (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U' y‖ ≤ N) →
      ∑ r ∈ rows, ‖∑ n ∈ (U \ b).powerset, conj (colA ξ (rowK r) (rowFe r) n) * U' (nI n / X)‖ ^ 2 ≤
        (4 ^ b.card * (Kc * Z ^ ε1 * (Z / B) ^ 2)) * N ^ 2 := by
  intro U' hU' hsupp N hN
  set W' : ℝ → ℂ := fun x => conj (U' x) with hW'def
  have hW'0 : ∀ x, x < αV ∨ βV < x → W' x = 0 := by
    intro x hx
    have hxV : x ∉ tsupport U' := fun h => by
      have := hVs (hsupp h)
      rcases hx with h1 | h1
      · exact absurd this.1 (not_le.2 h1)
      · exact absurd this.2 (not_le.2 h1)
    simp only [hW'def, image_eq_zero_of_notMem_tsupport hxV, map_zero]
  have hW'β : ∀ x, βV < x → W' x = 0 := fun x hx => hW'0 x (Or.inr hx)
  have hrow : ∀ r ∈ rows, ‖∑ n ∈ (U \ b).powerset, conj (colA ξ (rowK r) (rowFe r) n) *
      U' (nI n / X)‖ = ‖colSum ξ W' X (idl b) (rowK r) (rowFe r)‖ := by
    intro r _
    rw [colSum_eq_powerset ξ hW'β hXpos hU, ← RCLike.norm_conj, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hW'def, map_mul, Complex.conj_conj]
  rw [Finset.sum_congr rfl fun r hr => by rw [hrow r hr]]
  set φ : Row → Ideal (𝓞 K) × 𝓞 K := fun r => (idl (rowF r), rowK r) with hφ
  have hinj : ∀ r ∈ rows, ∀ r' ∈ rows, φ r = φ r' → r = r' := by
    intro r hr r' hr' h
    obtain ⟨hd, hc, -⟩ := hrows r hr
    obtain ⟨hd', hc', -⟩ := hrows r' hr'
    exact row_injective hd hd' hc hc' (congrArg Prod.fst h) (congrArg Prod.snd h)
  have e1 : ∑ r ∈ rows, ‖colSum ξ W' X (idl b) (rowK r) (rowFe r)‖ ^ 2 =
      ∑ p ∈ rows.image φ, ‖colSum ξ W' X (idl b) p.2 (pgen p.1)‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [hφ]
    rw [pgen_idl_rowF (hrows r hr).1]
  set Fs := rows.image fun r => idl (rowF r) with hFs
  set Ks := rows.image rowK with hKs
  have hsub : rows.image φ ⊆ Fs ×ˢ Ks := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hr, Finset.mem_image_of_mem _ hr⟩
  have e2 : ∑ p ∈ rows.image φ, ‖colSum ξ W' X (idl b) p.2 (pgen p.1)‖ ^ 2 ≤
      ∑ f ∈ Fs, ∑ k ∈ Ks, ‖colSum ξ W' X (idl b) k (pgen f)‖ ^ 2 := by
    rw [← Finset.sum_product' (f := fun f k => ‖colSum ξ W' X (idl b) k (pgen f)‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hFs' : ∀ f ∈ Fs, (absNorm f).Coprime 6 ∧ Squarefree f ∧ F ≤ (absNorm f : ℝ) ∧
      (absNorm f : ℝ) < 2 * F := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨-, -, -, h1, h2, -⟩ := hrows r hr
    exact ⟨idl_coprime6 _, idl_squarefree _, h1, h2⟩
  have hKs' : ∀ k ∈ Ks, k ≠ 0 ∧ (absNorm (span {k}) : ℝ) ≤ Hc := by
    intro k hk
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨-, -, hμ, -, -, hH⟩ := hrows r hr
    exact ⟨mul_ne_zero (eS_ne_zero _) hμ, hH⟩
  have hN' : ∀ j ≤ J, ∀ x, ‖iteratedDeriv j W' x‖ ≤ N := fun j hj x => by
    rw [hW'def, norm_iteratedDeriv_conj_comp]; exact hN j hj x
  have h3 := hexcl W' (contDiff_conj_comp hU') hW'0 N hN' Fs Ks hFs' hKs'
  rw [← hX] at h3
  calc ∑ r ∈ rows, ‖colSum ξ W' X (idl b) (rowK r) (rowFe r)‖ ^ 2
      ≤ 4 ^ b.card * (Kc * N ^ 2 * Z ^ ε1 * (Z / B) ^ 2) := e1 ▸ e2.trans h3
    _ = (4 ^ b.card * (Kc * Z ^ ε1 * (Z / B) ^ 2)) * N ^ 2 := by ring

/-! ### The bilinear form of a block of rows -/

/-- The weight of a row: the sign `(−1)^{|T|+|V|}` and the factor `ā_{ξ₁}(V)a_{ξ₂}(V)|χ_V(μ)|²`. -/
def wRow (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (r : Row) : ℂ :=
  ((-1 : ℂ) ^ r.1.card * (-1) ^ r.2.1.card) *
    (conj (aXi ξ1 (idl r.2.1)) * aXi ξ2 (idl r.2.1) * (chiS r.2.1 r.2.2 * conj (chiS r.2.1 r.2.2)))

theorem norm_wRow_le (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (r : Row) :
    ‖wRow ξ1 ξ2 r‖ ≤ 1 := by
  unfold wRow
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_pow, one_mul,
    one_mul, norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have h1 := norm_aXi_le ξ1 (idl r.2.1)
  have h2 := norm_aXi_le ξ2 (idl r.2.1)
  have h3 := norm_chiS_le r.2.1 r.2.2
  calc ‖aXi ξ1 (idl r.2.1)‖ * ‖aXi ξ2 (idl r.2.1)‖ * (‖chiS r.2.1 r.2.2‖ * ‖chiS r.2.1 r.2.2‖)
      ≤ 1 * 1 * (1 * 1) := by gcongr
    _ = 1 := by ring

/-- The parameter `A_r = 4HN(μ)/(3N(V)²N(T)X²)` of the dual weight of a row. -/
def ARow (H X : ℝ) (r : Row) : ℝ :=
  4 * H * (absNorm (span {r.2.2}) : ℝ) / (3 * nI r.2.1 ^ 2 * nI r.1 * X ^ 2)

theorem dvd_rowFe_of_mem {r : Row} {P : Pr} (hP : P ∈ r.1 ∪ r.2.1) : πP P ∣ rowFe r := by
  unfold rowFe
  rcases Finset.mem_union.1 hP with h | h
  · exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ h) _
  · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ h) _

/-- The columns of a row outside `U∖(b∪T)∖V` meet `T ∪ V`, so their coefficients vanish. -/
theorem colA_eq_zero_of_not_good (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U b : Finset Pr}
    (r : Row) {n : Finset Pr} (hn : n ∈ (U \ b).powerset)
    (hng : n ∉ ((U \ (b ∪ r.1)) \ r.2.1).powerset) : colA ξ (rowK r) (rowFe r) n = 0 := by
  rw [Finset.mem_powerset] at hn hng
  rw [Finset.not_subset] at hng
  obtain ⟨P, hPn, hPg⟩ := hng
  have hPU := hn hPn
  rw [Finset.mem_sdiff] at hPU
  have hTV : P ∈ r.1 ∪ r.2.1 := by
    by_contra hc
    apply hPg
    rw [Finset.mem_union, not_or] at hc
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_union, not_or]
    exact ⟨⟨hPU.1, hPU.2, hc.1⟩, hc.2⟩
  exact colA_eq_zero ξ _ _ hPn (dvd_rowFe_of_mem hTV)

/-- **One term in the shape of round 306's bilinear form**: with `X = Z/(N(b)F)`, `ρ = N(f)/F` and
`x_n = N(n)/X`, `rcTerm = 2HN(b)/(√3Z)·w_r·ā_r(n₁)·conj(b̄_r(n₂))·W₀(ρx_{n₁})·conj W₀(ρx_{n₂})·Φ̂(√(A_r/(x_{n₁}x_{n₂})))`
for columns disjoint from `V`. -/
theorem rcTerm_eq_bilinear (W : ℝ → ℝ) {Z H F : ℝ} (hZ : 0 < Z) (hF : 0 < F)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (b : Finset Pr) (r : Row) {M1 M2 : Finset Pr}
    (hTV : Disjoint r.1 r.2.1) (hV1 : Disjoint r.2.1 M1) (hV2 : Disjoint r.2.1 M2) :
    rcTerm W Z H ξ1 ξ2 b r.1 r.2.1 r.2.2 M1 M2 =
      ((2 * H * nI b / (Real.sqrt 3 * Z) : ℝ) : ℂ) *
        (wRow ξ1 ξ2 r * (conj (colA ξ1 (rowK r) (rowFe r) M1) *
          conj (conj (colA ξ2 (rowK r) (rowFe r) M2)) *
          (((W0f W (nI (rowF r) / F * (nI M1 / (Z / (nI b * F)))) : ℝ) : ℂ) *
            conj ((W0f W (nI (rowF r) / F * (nI M2 / (Z / (nI b * F)))) : ℝ) : ℂ) *
            dualG (Real.sqrt (ARow H (Z / (nI b * F)) r /
              (nI M1 / (Z / (nI b * F)) * (nI M2 / (Z / (nI b * F))))))))) := by
  have hb := nI_pos b
  have hT := nI_pos r.1
  have hV := nI_pos r.2.1
  have h1 := nI_pos M1
  have h2 := nI_pos M2
  have hf : nI (rowF r) = nI r.1 * nI r.2.1 := nI_union hTV
  have hw1 : nI b * nI r.1 * nI r.2.1 * nI M1 / Z =
      nI (rowF r) / F * (nI M1 / (Z / (nI b * F))) := by
    rw [hf]; field_simp
  have hw2 : nI b * nI r.1 * nI r.2.1 * nI M2 / Z =
      nI (rowF r) / F * (nI M2 / (Z / (nI b * F))) := by
    rw [hf]; field_simp
  have hg : 4 * H * (absNorm (span {r.2.2}) : ℝ) /
      (3 * (nI (r.2.1 ∪ M1) * nI (r.2.1 ∪ M2)) * nI r.1) =
      ARow H (Z / (nI b * F)) r / (nI M1 / (Z / (nI b * F)) * (nI M2 / (Z / (nI b * F)))) := by
    unfold ARow
    rw [nI_union hV1, nI_union hV2]
    field_simp
  unfold rcTerm wRow dualW
  rw [hw1, hw2, hg, Complex.conj_conj, Complex.conj_ofReal]
  unfold rowK rowFe
  push_cast
  ring

/-- **A row's double column sum as the bilinear form**: the columns `M ⊆ U∖(b∪T)∖V` of round 308 are
completed to all `n ⊆ U∖b`, whose extra coefficients vanish (`colA_eq_zero_of_not_good`). -/
theorem rowSum_eq_bilinear (W : ℝ → ℝ) {Z H F : ℝ} (hZ : 0 < Z) (hF : 0 < F)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U b : Finset Pr} (r : Row)
    (hV : r.2.1 ⊆ U \ (b ∪ r.1)) :
    ∑ M1 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, ∑ M2 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset,
        rcTerm W Z H ξ1 ξ2 b r.1 r.2.1 r.2.2 M1 M2 =
      ((2 * H * nI b / (Real.sqrt 3 * Z) : ℝ) : ℂ) *
        (wRow ξ1 ξ2 r * ∑ n1 ∈ (U \ b).powerset, ∑ n2 ∈ (U \ b).powerset,
          conj (colA ξ1 (rowK r) (rowFe r) n1) * conj (conj (colA ξ2 (rowK r) (rowFe r) n2)) *
          (((W0f W (nI (rowF r) / F * (nI n1 / (Z / (nI b * F)))) : ℝ) : ℂ) *
            conj ((W0f W (nI (rowF r) / F * (nI n2 / (Z / (nI b * F)))) : ℝ) : ℂ) *
            dualG (Real.sqrt (ARow H (Z / (nI b * F)) r /
              (nI n1 / (Z / (nI b * F)) * (nI n2 / (Z / (nI b * F)))))))) := by
  have hTV : Disjoint r.1 r.2.1 := by
    have := (Finset.subset_sdiff.1 hV).2
    rw [Finset.disjoint_union_right] at this
    exact this.2.symm
  set t : Finset Pr → Finset Pr → ℂ := fun n1 n2 =>
    conj (colA ξ1 (rowK r) (rowFe r) n1) * conj (conj (colA ξ2 (rowK r) (rowFe r) n2)) *
      (((W0f W (nI (rowF r) / F * (nI n1 / (Z / (nI b * F)))) : ℝ) : ℂ) *
        conj ((W0f W (nI (rowF r) / F * (nI n2 / (Z / (nI b * F)))) : ℝ) : ℂ) *
        dualG (Real.sqrt (ARow H (Z / (nI b * F)) r /
          (nI n1 / (Z / (nI b * F)) * (nI n2 / (Z / (nI b * F))))))) with ht
  have hsubG : ((U \ (b ∪ r.1)) \ r.2.1).powerset ⊆ (U \ b).powerset := by
    intro n hn
    rw [Finset.mem_powerset] at hn ⊢
    intro P hP
    have := hn hP
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_union, not_or] at this
    exact Finset.mem_sdiff.2 ⟨this.1.1, this.1.2.1⟩
  have hgood : ∀ n ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, Disjoint r.2.1 n := fun n hn =>
    disjoint_of_mem_powerset_sdiff hn
  calc ∑ M1 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, ∑ M2 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset,
        rcTerm W Z H ξ1 ξ2 b r.1 r.2.1 r.2.2 M1 M2
      = ∑ M1 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, ∑ M2 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset,
          ((2 * H * nI b / (Real.sqrt 3 * Z) : ℝ) : ℂ) * (wRow ξ1 ξ2 r * t M1 M2) := by
        refine Finset.sum_congr rfl fun M1 hM1 => Finset.sum_congr rfl fun M2 hM2 => ?_
        rw [rcTerm_eq_bilinear W hZ hF ξ1 ξ2 b r hTV (hgood M1 hM1) (hgood M2 hM2)]
    _ = ((2 * H * nI b / (Real.sqrt 3 * Z) : ℝ) : ℂ) * (wRow ξ1 ξ2 r *
          ∑ n1 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset,
            ∑ n2 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, t n1 n2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n1 _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
        congr 2
        have hin : ∀ n1 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset,
            ∑ n2 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, t n1 n2 =
              ∑ n2 ∈ (U \ b).powerset, t n1 n2 := by
          intro n1 _
          refine Finset.sum_subset hsubG fun n2 hn2 hng => ?_
          simp only [ht]
          rw [colA_eq_zero_of_not_good ξ2 r hn2 hng]; simp
        rw [Finset.sum_congr rfl hin]
        refine Finset.sum_subset hsubG fun n1 hn1 hng => ?_
        refine Finset.sum_eq_zero fun n2 _ => ?_
        simp only [ht]
        rw [colA_eq_zero_of_not_good ξ1 r hn1 hng]; simp

/-- **The bound for one block of rows** (the paper's application of Lemma B.2 for one `b` and one
dyadic range of `N(f)`): round 306's `bilinear_dual_bound₂` (its conclusion supplied as `hK`), fed with
the column mean squares `hcol1`, `hcol2` of the two families, gives
`|Σ_{rows} Σ_{M₁,M₂} rcTerm| ≤ 2HN(b)/(√3Z)·K·A_min^{−σ}·M_b` when `1 ≤ N(f)/F ≤ 2` and
`A_min ≤ A_r` on the rows. -/
theorem rowBlock_bound (W : ℝ → ℝ) {Z H F : ℝ} (hZ : 0 < Z) (hF : 0 < F) (hH : 0 ≤ H)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {U b : Finset Pr} (rows : Finset Row)
    {K σ Amin Mb : ℝ} (hAmin : 0 < Amin) (hMb : 0 ≤ Mb)
    (hrows : ∀ r ∈ rows, r.2.1 ⊆ U \ (b ∪ r.1) ∧ 1 ≤ nI (rowF r) / F ∧ nI (rowF r) / F ≤ 2 ∧
      Amin ≤ ARow H (Z / (nI b * F)) r)
    (V : ℝ → ℂ) (J : ℕ)
    (hK : ∀ {ι κ : Type} (T : Finset ι) (C : Finset κ) (a b : ι → κ → ℂ) (x : κ → ℝ),
      (∀ n ∈ C, 0 < x n) → ∀ M : ℝ, 0 ≤ M →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, a r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      (∀ U : ℝ → ℂ, ContDiff ℝ ∞ U → tsupport U ⊆ tsupport V → ∀ N : ℝ,
        (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U y‖ ≤ N) →
        ∑ r ∈ T, ‖∑ n ∈ C, b r n * U (x n)‖ ^ 2 ≤ M * N ^ 2) →
      ∀ ρ : ι → ℝ, (∀ r ∈ T, 1 ≤ ρ r ∧ ρ r ≤ 2) →
      ∀ w : ι → ℂ, (∀ r ∈ T, ‖w r‖ ≤ 1) → ∀ (Ar : ι → ℝ) (Amin : ℝ), 0 < Amin →
      (∀ r ∈ T, Amin ≤ Ar r) →
      ‖∑ r ∈ T, w r * ∑ n1 ∈ C, ∑ n2 ∈ C, a r n1 * conj (b r n2) *
          ((((W0f W (ρ r * x n1)) : ℝ) : ℂ) * conj (((W0f W (ρ r * x n2)) : ℝ) : ℂ) *
            dualG (Real.sqrt (Ar r / (x n1 * x n2))))‖ ≤ K * Amin ^ (-σ) * M)
    (hcol1 : ∀ U' : ℝ → ℂ, ContDiff ℝ ∞ U' → tsupport U' ⊆ tsupport V → ∀ N : ℝ,
      (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U' y‖ ≤ N) →
      ∑ r ∈ rows, ‖∑ n ∈ (U \ b).powerset, conj (colA ξ1 (rowK r) (rowFe r) n) *
        U' (nI n / (Z / (nI b * F)))‖ ^ 2 ≤ Mb * N ^ 2)
    (hcol2 : ∀ U' : ℝ → ℂ, ContDiff ℝ ∞ U' → tsupport U' ⊆ tsupport V → ∀ N : ℝ,
      (∀ j ≤ J, ∀ y, ‖iteratedDeriv j U' y‖ ≤ N) →
      ∑ r ∈ rows, ‖∑ n ∈ (U \ b).powerset, conj (colA ξ2 (rowK r) (rowFe r) n) *
        U' (nI n / (Z / (nI b * F)))‖ ^ 2 ≤ Mb * N ^ 2) :
    ‖∑ r ∈ rows, ∑ M1 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset,
        ∑ M2 ∈ ((U \ (b ∪ r.1)) \ r.2.1).powerset, rcTerm W Z H ξ1 ξ2 b r.1 r.2.1 r.2.2 M1 M2‖ ≤
      2 * H * nI b / (Real.sqrt 3 * Z) * (K * Amin ^ (-σ) * Mb) := by
  rw [Finset.sum_congr rfl fun r hr => rowSum_eq_bilinear W hZ hF ξ1 ξ2 r (hrows r hr).1,
    ← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
      have := nI_pos b; positivity)]
  have hX : 0 < Z / (nI b * F) := by have := nI_pos b; positivity
  refine mul_le_mul_of_nonneg_left ?_ (by have := nI_pos b; positivity)
  exact hK rows (U \ b).powerset (fun r n => conj (colA ξ1 (rowK r) (rowFe r) n))
    (fun r n => conj (colA ξ2 (rowK r) (rowFe r) n)) (fun n => nI n / (Z / (nI b * F)))
    (fun n _ => div_pos (nI_pos n) hX) Mb hMb hcol1 hcol2 (fun r => nI (rowF r) / F)
    (fun r hr => ⟨(hrows r hr).2.1, (hrows r hr).2.2.1⟩) (wRow ξ1 ξ2)
    (fun r _ => norm_wRow_le ξ1 ξ2 r) (ARow H (Z / (nI b * F))) Amin hAmin
    (fun r hr => (hrows r hr).2.2.2)

theorem one_le_absNorm_span {μ : 𝓞 K} (hμ : μ ≠ 0) : (1 : ℝ) ≤ (absNorm (span {μ}) : ℝ) := by
  have : absNorm (span {μ}) ≠ 0 := by
    rw [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hμ
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

/-- **The lower bound for the dual weight's parameter** (the paper's `a ≤ C_{I,Φ}` read from below):
for `μ ≠ 0` and `N(f) < 2F`, `A_r ≥ H·N(b)²/(3Z²)` at `X = Z/(N(b)F)`. -/
theorem ARow_ge {H Z F : ℝ} (hH : 0 ≤ H) (hZ : 0 < Z) (hF : 0 < F) (b : Finset Pr) (r : Row)
    (hTV : Disjoint r.1 r.2.1) (hμ : r.2.2 ≠ 0) (hf : nI (rowF r) < 2 * F) :
    H * nI b ^ 2 / (3 * Z ^ 2) ≤ ARow H (Z / (nI b * F)) r := by
  have hb := nI_pos b
  have hT := one_le_nI r.1
  have hV := nI_pos r.2.1
  have hN := one_le_absNorm_span hμ
  rw [rowF, nI_union hTV] at hf
  unfold ARow
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : nI r.2.1 ^ 2 * nI r.1 ≤ 4 * F ^ 2 * (absNorm (span {r.2.2}) : ℝ) := by
    have h1 : nI r.2.1 ^ 2 * nI r.1 ≤ (nI r.1 * nI r.2.1) ^ 2 := by nlinarith
    have h2 : (nI r.1 * nI r.2.1) ^ 2 ≤ (2 * F) ^ 2 := by
      have := mul_pos (lt_of_lt_of_le one_pos hT) hV
      exact pow_le_pow_left₀ this.le hf.le 2
    nlinarith
  have e : H * nI b ^ 2 * (3 * nI r.2.1 ^ 2 * nI r.1 * (Z / (nI b * F)) ^ 2) =
      3 * H * Z ^ 2 * (nI r.2.1 ^ 2 * nI r.1) / F ^ 2 := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h3 : 0 ≤ 3 * H * Z ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hkey h3
  nlinarith

end Eis

end

#print axioms Eis.prime_Pr
#print axioms Eis.dvd_idl_iff
#print axioms Eis.isRelPrime_idl
#print axioms Eis.colA_eq_zero
#print axioms Eis.sym6_idl_eq
#print axioms Eis.colSum_eq_powerset
#print axioms Eis.contDiff_conj_comp
#print axioms Eis.norm_iteratedDeriv_conj_comp
#print axioms Eis.eS_union
#print axioms Eis.eS_ne_zero
#print axioms Eis.pgen_idl_rowF
#print axioms Eis.row_injective
#print axioms Eis.rows_colMeanSquare
#print axioms Eis.norm_wRow_le
#print axioms Eis.dvd_rowFe_of_mem
#print axioms Eis.colA_eq_zero_of_not_good
#print axioms Eis.rcTerm_eq_bilinear
#print axioms Eis.rowSum_eq_bilinear
#print axioms Eis.rowBlock_bound
#print axioms Eis.one_le_absNorm_span
#print axioms Eis.ARow_ge
