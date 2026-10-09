import EisensteinTransferPoisson

/-! # The transfer's first Poisson summation in row/column form (round 319)

S5c-2 in round 316's plan, its second part. After round 318's `dualMS_poisson`, the companion paper's
proof of its Lemma 7.1 continues, with its LaTeX rendered as text: "Expand
`(ξG)(z)=Σ_{ξ_1}ℓ_{ξ_1}ξ_1(z)` on the fixed ray class group. Insert
`1_{(u_1,u_2)=1}=Σ_{t∣u_1, t∣u_2}μ(t)` and put `u_i=tx_i`." This file does these steps for one row
`f`, in round 308's bookkeeping by sets of primes.

* **The column coefficients** (`colP`): `μ(M)ξ(M)·χ_M(c)·conj(χ_M(y))`, the paper's `p_y` of (7.1)
  with `y = hf²` and `c = C⁴d·t⁶`; the factor `χ_M(t)⁶` is its indicator `1_{(n,t)=1}`.
* **The paired factor in characters modulo `4`** (`dualPair_expand`):
  `ξ(C₁)ξ̄(C₂)·μ(C₁)μ(C₂)Ψ(C₁, C₂) = Σ_{ξ₁,ξ₂} ĉ(ξ₁, ξ₂⁻¹)·μ(C₁)ξ₁(C₁)·conj(μ(C₂)ξ₂(C₂))`, through round
  306's expansion of a function of two classes.
* **The zero frequency and the nonzero frequencies** (`pair_char_form_dual`), through round 308's
  `tsum_mu_eq`.
* **The insertion of `t`** (`xi_chain_dual`), through round 308's `sum_pair_T_split` and
  `sum_disjoint_mobius` (since round 332 through their composite `sum_pair_chain`), and **the column
  factorization** (`term_factor_dual`, with `colP_natural` and `WW_kapC`).
* **`dualMS_rowcol`**: the smoothed dual mean square of one row in row/column form.
-/

open NumberField Complex Ideal UniqueFactorizationMonoid
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Eis

/-! ### Symbols -/

/-- `χ_M(f)⁴ = conj(χ_M(f²))`: the paper's `χ_n(f)⁴` with the frequency `h` gives `conj(χ_n(hf²))`. -/
theorem chiS_pow_four (M : Finset Pr) (f : 𝓞 K) : chiS M f ^ 4 = conj (chiS M (f ^ 2)) := by
  rw [chiS_conj_eq_pow_five, chiS_pow, ← pow_mul]
  unfold chiS
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun P _ => ?_
  by_cases hx : Ideal.Quotient.mk (span {πP P}) f = 0
  · rw [hx]; simp [chiF, MulChar.map_zero]
  · have h6 := chi6_pow_six_of_ne_zero (span {πP P}) (h6Pr P) hx
    set z := chiF πP h6Pr P (Ideal.Quotient.mk (span {πP P}) f)
    have hz6 : z ^ 6 = 1 := h6
    calc z ^ 4 = z ^ 4 * (z ^ 6) := by rw [hz6, mul_one]
      _ = z ^ (2 * 5) := by ring

theorem cls4_union {V M : Finset Pr} (h : Disjoint V M) : cls4 (V ∪ M) = cls4 V * cls4 M := by
  unfold cls4; rw [Finset.prod_union h, map_mul]

/-! ### The column coefficients of the transfer -/

/-- The column coefficient `μ(M)ξ(M)·χ_M(c)·conj(χ_M(y))`: the companion paper's `p_y` of (7.1) with
`y` its `hf²` and `c` its `C⁴d·t⁶`, the factor `χ_M(t)⁶` giving its indicator `1_{(n,t)=1}`
(`chiS_eS_pow_six_eq_one`, `colP_eq_zero_of_dvd`). -/
def colP (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (y c : 𝓞 K) (M : Finset Pr) : ℂ :=
  (-1 : ℂ) ^ M.card * ξ (cls4 M) * chiS M c * conj (chiS M y)

theorem colP_union (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (y c : 𝓞 K) {V M : Finset Pr}
    (h : Disjoint V M) : colP ξ y c (V ∪ M) = colP ξ y c V * colP ξ y c M := by
  unfold colP
  rw [Finset.card_union_of_disjoint h, pow_add, cls4_union h, map_mul, chiS_union h,
    chiS_union h, map_mul]
  ring

theorem norm_colP_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (y c : 𝓞 K) (M : Finset Pr) :
    ‖colP ξ y c M‖ ≤ 1 := by
  unfold colP
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_xi_cls4, one_mul, RCLike.norm_conj]
  calc ‖chiS M c‖ * ‖chiS M y‖ ≤ 1 * 1 :=
        mul_le_mul (norm_chiS_le M c) (norm_chiS_le M y) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-! ### The paired factor in characters modulo `4` -/

/-- `ξ(x)ξ̄(y)·Ψ(x, y)` on classes modulo `4`. -/
def pairPsiXi (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (x y : 𝓞 K ⧸ span {(4 : 𝓞 K)}) : ℂ :=
  ξ x * conj (ξ y) * pairPsiCls x y

theorem norm_pairPsiXi_le (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (x y : 𝓞 K ⧸ span {(4 : 𝓞 K)})
    (hx : IsUnit x) (hy : IsUnit y) : ‖pairPsiXi ξ x y‖ ≤ 1 := by
  unfold pairPsiXi
  have h1 : ‖ξ x‖ = 1 := by obtain ⟨u, rfl⟩ := hx; exact norm_mulChar_unit ξ u
  have h2 : ‖ξ y‖ = 1 := by obtain ⟨u, rfl⟩ := hy; exact norm_mulChar_unit ξ u
  rw [norm_mul, norm_mul, RCLike.norm_conj, h1, h2, one_mul, one_mul]
  exact norm_pairPsiCls_le x y

theorem conj_xi_cls4 (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (C : Finset Pr) :
    conj (ξ (cls4 C)) = ξ⁻¹ (cls4 C) := MulChar.star_apply' ξ (cls4 C)

/-- **The dual pair factor in characters modulo `4`**: for disjoint `C₁, C₂`,
`ξ(C₁)ξ̄(C₂)·μ(C₁)μ(C₂)Ψ(C₁, C₂) = Σ_{ξ₁,ξ₂} ĉ(ξ₁, ξ₂⁻¹)·(μ(C₁)ξ₁(C₁))·conj(μ(C₂)ξ₂(C₂))`. -/
theorem dualPair_expand (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {C1 C2 : Finset Pr}
    (hd : Disjoint C1 C2) :
    ξ (cls4 C1) * conj (ξ (cls4 C2)) * pairPsiDual C1 C2 =
      ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ *
          (((-1 : ℂ) ^ C1.card * ξ1 (cls4 C1)) * conj ((-1 : ℂ) ^ C2.card * ξ2 (cls4 C2))) := by
  set x := (isUnit_cls4 C1).unit
  set y := (isUnit_cls4 C2).unit
  have hx : (x : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C1 := IsUnit.unit_spec _
  have hy : (y : 𝓞 K ⧸ span {(4 : 𝓞 K)}) = cls4 C2 := IsUnit.unit_spec _
  have hexp := pair_eq_sum_mulChar (pairPsiXi ξ) x y
  rw [hx, hy] at hexp
  have hP : ξ (cls4 C1) * conj (ξ (cls4 C2)) * pairPsiDual C1 C2 =
      (-1 : ℂ) ^ C1.card * (-1) ^ C2.card * pairPsiXi ξ (cls4 C1) (cls4 C2) := by
    unfold pairPsiDual pairPsiXi; rw [pairPsi_eq_cls hd]; ring
  rw [hP, hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ1 _ => ?_
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.inv (MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ))]
  refine Finset.sum_congr rfl fun ξ2 _ => ?_
  simp only [Equiv.inv_apply]
  rw [map_mul, map_pow, map_neg, map_one, conj_xi_cls4]
  ring

/-! ### Small facts -/

theorem cls4_empty : cls4 ∅ = 1 := by
  unfold cls4; rw [Finset.prod_empty, map_one]

theorem pairPsiDual_empty : pairPsiDual ∅ ∅ = 1 := by
  unfold pairPsiDual; rw [Finset.card_empty, pow_zero, pairPsi_empty]; ring

/-- `χ_M(t⁶) = 1` for `M` prime to `t`. -/
theorem chiS_eS_pow_six_eq_one {M V : Finset Pr} (h : Disjoint M V) : chiS M (eS V ^ 6) = 1 := by
  rw [chiS_pow, chiS_eS_pow_six h]

/-- A column coefficient vanishes on the columns containing a prime dividing `c`. -/
theorem colP_eq_zero_of_dvd (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (y c : 𝓞 K) {M : Finset Pr}
    {P : Pr} (hP : P ∈ M) (h : πP P ∣ c) : colP ξ y c M = 0 := by
  unfold colP; rw [chiS_eq_zero_of_dvd hP h]; ring

/-- **The transfer's column coefficient in natural form**: for `b, T` disjoint and `M` prime to `V`,
the coefficient at the frequency `μ` (the paper's `h`), `y = μf²` and `c = b⁴T⁵V⁶` is
`(−1)^{|M|}ξ(M)·χ_M(bT)⁴χ_M(T)·χ_M(f)⁴·conj(χ_M(μ))`. -/
theorem colP_natural (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {b T V M : Finset Pr}
    (hbT : Disjoint b T) (hVM : Disjoint V M) (μ f : 𝓞 K) :
    colP ξ (μ * f ^ 2) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M =
      (-1 : ℂ) ^ M.card * ξ (cls4 M) * (chiS M (eS (b ∪ T)) ^ 4 * chiS M (eS T)) *
        (chiS M f ^ 4 * conj (chiS M μ)) := by
  unfold colP
  rw [eS_union hbT, chiS_pow_four M f]
  simp only [chiS_mul, chiS_pow, chiS_eS_pow_six hVM.symm, map_mul, map_pow]
  ring

/-- **The weights after the change of variables, for complex `W`**:
`W(N(bTVm₁)/X)·conj(W(N(bTVm₂)/X))·2H/(√3·√(N(Vm₁)N(Vm₂))·N(T)) = 2H·N(b)/(√3·X)·W₀(…m₁…)·conj(W₀(…m₂…))`. -/
theorem WW_kapC (W : ℝ → ℂ) {X H nb nT nV n1 n2 : ℝ} (hX : 0 < X) (hb : 0 < nb) (hT : 0 < nT)
    (hV : 0 < nV) (h1 : 0 < n1) (h2 : 0 < n2) :
    W (nb * nT * (nV * n1) / X) * conj (W (nb * nT * (nV * n2) / X)) *
        ((2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT) : ℝ) : ℂ) =
      ((2 * H * nb / (Real.sqrt 3 * X) : ℝ) : ℂ) *
        (MellinSep.W0c W (nb * nT * nV * n1 / X) * conj (MellinSep.W0c W (nb * nT * nV * n2 / X))) := by
  have hx1 : 0 < nb * nT * nV * n1 / X := by positivity
  have hx2 : 0 < nb * nT * nV * n2 / X := by positivity
  have e1 : nb * nT * (nV * n1) / X = nb * nT * nV * n1 / X := by ring
  have e2 : nb * nT * (nV * n2) / X = nb * nT * nV * n2 / X := by ring
  have hW1 : W (nb * nT * nV * n1 / X) = MellinSep.W0c W (nb * nT * nV * n1 / X) *
      ((Real.sqrt (nb * nT * nV * n1 / X) : ℝ) : ℂ) := by
    unfold MellinSep.W0c
    rw [div_mul_cancel₀]
    exact_mod_cast (Real.sqrt_pos.2 hx1).ne'
  have hW2 : W (nb * nT * nV * n2 / X) = MellinSep.W0c W (nb * nT * nV * n2 / X) *
      ((Real.sqrt (nb * nT * nV * n2 / X) : ℝ) : ℂ) := by
    unfold MellinSep.W0c
    rw [div_mul_cancel₀]
    exact_mod_cast (Real.sqrt_pos.2 hx2).ne'
  have hs : Real.sqrt (nb * nT * nV * n1 / X) * Real.sqrt (nb * nT * nV * n2 / X) =
      nb * nT * nV * Real.sqrt (n1 * n2) / X := by
    rw [← Real.sqrt_mul hx1.le, show nb * nT * nV * n1 / X * (nb * nT * nV * n2 / X) =
      (nb * nT * nV / X) ^ 2 * (n1 * n2) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    ring
  have hs2 : Real.sqrt (nV * n1 * (nV * n2)) = nV * Real.sqrt (n1 * n2) := by
    rw [show nV * n1 * (nV * n2) = nV ^ 2 * (n1 * n2) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hV.le]
  have hq : 0 < Real.sqrt (n1 * n2) := Real.sqrt_pos.2 (by positivity)
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hr : Real.sqrt (nb * nT * nV * n1 / X) * Real.sqrt (nb * nT * nV * n2 / X) *
      (2 * H / (Real.sqrt 3 * Real.sqrt (nV * n1 * (nV * n2)) * nT)) =
      2 * H * nb / (Real.sqrt 3 * X) := by
    rw [hs, hs2]; field_simp
  rw [e1, e2, hW1, hW2, map_mul, Complex.conj_ofReal, ← hr]
  push_cast
  ring

/-! ### The dual mean square in clean form -/

/-- The weight of a pair of columns `(A₁, A₂)` in the dual mean square of a row `f`, apart from the
characters modulo `4`: `χ_{C₁}(b)⁴conj(χ_{C₂}(b)⁴)·χ_{A₁}(f)⁴conj(χ_{A₂}(f)⁴)·W(N(A₁)/X)conj(W(N(A₂)/X))`,
with `b` the primary generator `eS(A₁∩A₂)`, `C₁ = A₁∖A₂` and `C₂ = A₂∖A₁`. -/
def wPair (W : ℝ → ℂ) (X : ℝ) (f : 𝓞 K) (A1 A2 : Finset Pr) : ℂ :=
  chiS (A1 \ A2) (eS (A1 ∩ A2)) ^ 4 * conj (chiS (A2 \ A1) (eS (A1 ∩ A2)) ^ 4) * chiS A1 f ^ 4 *
    conj (chiS A2 f ^ 4) * (W (nI A1 / X) * conj (W (nI A2 / X)))

theorem regroup7 (a b c d e g h S : ℂ) :
    a * b * c * d * e * g * h * S = c * d * e * g * h * (a * b * S) := by ring

open Classical in
/-- `dualMS_poisson` with the norms written through `nI`, `kap` and `dualW`, and the characters of
`C₁, C₂` modulo `4` moved next to the paired factor. -/
theorem dualMS_clean (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β' : ℝ}
    (hW : ∀ x, β' < x → W x = 0) {X : ℝ} (hX : 0 < X) {U : Finset Pr}
    (hU : primesLe (β' * X) ⊆ U) (f : 𝓞 K) (H : ℝ) (hH : 0 < H) :
    ∑' u : 𝓞 K, colSum ξ W X 1 u f * conj (colSum ξ W X 1 u f) *
        Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ A1 ∈ U.powerset, ∑ A2 ∈ U.powerset, wPair W X f A1 A2 *
        (ξ (cls4 (A1 \ A2)) * conj (ξ (cls4 (A2 \ A1))) *
          ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) *
            pairPsiDual (A1 \ A2) (A2 \ A1) *
            (chiS (A1 \ A2) (eS T) * conj (chiS (A2 \ A1) (eS T))) *
            ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
              dualW H (A1 \ A2) (A2 \ A1) T μ) := by
  rw [dualMS_poisson ξ hW hX hU f H hH]
  refine Finset.sum_congr rfl fun A1 _ => Finset.sum_congr rfl fun A2 _ => ?_
  have hd : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  unfold wPair
  rw [regroup7]
  congr 2
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [absNorm_span_prod_πP, absNorm_span_prod_πP, nI_union hd]
  rfl

/-! ### One pair in characters, frequencies split -/

/-- The term of `(C₁, C₂, T)` for the characters `ξ₁, ξ₂` and the frequencies in `E`, in the dual
direction: the signs and characters `μ(C₁)ξ₁(C₁)·conj(μ(C₂)ξ₂(C₂))` in place of round 308's
`ā_{ξ₁}(C₁)a_{ξ₂}(C₂)`. -/
def tauDual (H : ℝ) (E : Finset (𝓞 K)) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (C1 C2 T : Finset Pr) : ℂ :=
  (-1 : ℂ) ^ T.card * (kap H C1 C2 T : ℂ) *
    (((-1 : ℂ) ^ C1.card * ξ1 (cls4 C1)) * conj ((-1 : ℂ) ^ C2.card * ξ2 (cls4 C2))) *
    (chiS C1 (eS T) * conj (chiS C2 (eS T))) *
    ∑ μ ∈ E, conj (chiS C1 μ * conj (chiS C2 μ)) * dualW H C1 C2 T μ

open Classical in
/-- **One pair after Poisson summation, in the dual direction, in characters modulo `4`**: for
`N(A₁), N(A₂) ≤ M` and `3R²M² ≤ 4HY` (with `Φ̂` vanishing beyond `R`), `ξ(C₁)ξ̄(C₂)` times the pair's
sum after Poisson summation is the zero frequency, present only for `A₁ = A₂`, plus `Σ_{ξ₁,ξ₂} ĉ(ξ₁, ξ₂⁻¹)·Σ_{T⊆A₁∩A₂} τ_{ξ₁ξ₂}(A₁∖A₂, A₂∖A₁, T)`
over the nonzero frequencies of norm at most `Y`. -/
theorem pair_char_form_dual (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (H : ℝ) (hH : 0 < H)
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {M Y : ℝ}
    (hY : 3 * R ^ 2 * M ^ 2 ≤ 4 * H * Y) {A1 A2 : Finset Pr} (h1 : nI A1 ≤ M) (h2 : nI A2 ≤ M) :
    ξ (cls4 (A1 \ A2)) * conj (ξ (cls4 (A2 \ A1))) *
      ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) *
        pairPsiDual (A1 \ A2) (A2 \ A1) *
        (chiS (A1 \ A2) (eS T) * conj (chiS (A2 \ A1) (eS T))) *
        ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
          dualW H (A1 \ A2) (A2 \ A1) T μ =
    (if A1 = A2 then ∑ T ∈ A1.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
      ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
        pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ *
          ∑ T ∈ (A1 ∩ A2).powerset, tauDual H ((eltsLe Y).erase 0) ξ1 ξ2 (A1 \ A2) (A2 \ A1) T := by
  have hd : Disjoint (A1 \ A2) (A2 \ A1) := disjoint_sdiff_sdiff
  have hM0 : 0 ≤ M := le_trans zero_le_one ((one_le_nI A1).trans h1)
  have hexp := dualPair_expand ξ hd
  rw [Finset.mul_sum]
  have hsplit : ∀ T ∈ (A1 ∩ A2).powerset,
      ξ (cls4 (A1 \ A2)) * conj (ξ (cls4 (A2 \ A1))) *
        ((-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) * pairPsiDual (A1 \ A2) (A2 \ A1) *
          (chiS (A1 \ A2) (eS T) * conj (chiS (A2 \ A1) (eS T))) *
          ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
            dualW H (A1 \ A2) (A2 \ A1) T μ) =
      (if A1 = A2 then (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
        ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ *
            tauDual H ((eltsLe Y).erase 0) ξ1 ξ2 (A1 \ A2) (A2 \ A1) T := by
    intro T hT
    have hTs : T ⊆ A1 ∩ A2 := Finset.mem_powerset.1 hT
    have hYT : 3 * R ^ 2 * (nI (A1 \ A2) * nI (A2 \ A1) * nI T) ≤ 4 * H * Y := by
      have hle := nI_pair_le hTs
      have hMM : nI A1 * nI A2 ≤ M ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (le_trans zero_le_one (one_le_nI A2)) hM0
      nlinarith [sq_nonneg R]
    rw [tsum_mu_eq H hH hR0 hR _ _ _ hYT, mul_add, mul_add]
    congr 1
    · by_cases he : A1 = A2
      · have he' := sdiff_eq_empty_both.2 he
        rw [ite_eq_left he, ite_eq_left he', he'.1, he'.2]
        simp only [cls4_empty, map_one, pairPsiDual_empty, chiS_empty]
        ring
      · have hn : ¬(A1 \ A2 = ∅ ∧ A2 \ A1 = ∅) := fun h => he (sdiff_eq_empty_both.1 h)
        rw [ite_eq_right he, ite_eq_right hn, mul_zero, mul_zero]
    · have e : ∀ (x y s k P F S : ℂ), x * y * (s * k * P * F * S) = (x * y * P) * (s * k * F * S) :=
        fun x y s k P F S => by ring
      rw [e, hexp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ξ1 _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun ξ2 _ => ?_
      unfold tauDual
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · split_ifs with he
    · subst he; rw [Finset.inter_self]
    · exact Finset.sum_eq_zero fun T _ => rfl
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ2 _ => ?_
    rw [Finset.mul_sum]

/-! ### The row/column form -/

/-- The weight of a pair `(B ∪ C₁, B ∪ C₂)` written through `B, C₁, C₂`, which equals `wPair` when
`B, C₁, C₂` are pairwise disjoint (`wPair_split`) and is the natural extension of it to the pairs of
the Möbius inversion. -/
def wNat (W : ℝ → ℂ) (X : ℝ) (f : 𝓞 K) (B C1 C2 : Finset Pr) : ℂ :=
  chiS C1 (eS B) ^ 4 * conj (chiS C2 (eS B) ^ 4) * chiS (B ∪ C1) f ^ 4 *
    conj (chiS (B ∪ C2) f ^ 4) * (W (nI (B ∪ C1) / X) * conj (W (nI (B ∪ C2) / X)))

theorem wPair_split (W : ℝ → ℂ) (X : ℝ) (f : 𝓞 K) {B C1 C2 : Finset Pr} (h1 : Disjoint C1 B)
    (h2 : Disjoint C2 B) (h12 : Disjoint C1 C2) :
    wPair W X f (B ∪ C1) (B ∪ C2) = wNat W X f B C1 C2 := by
  obtain ⟨e1, e2, e3⟩ := pair_split_facts h1 h2 h12
  unfold wPair wNat
  rw [e1, e2, e3]

/-- The term of the dual sum at `(b, T, V, μ, M₁, M₂)`: the sign `μ(T)μ(V)`, the row factor
`ξ₁(V)ξ̄₂(V)·|χ_V(f)⁴|²|χ_V(μ)|²|χ_{bT}(f)⁴|²`, the normalization `2H·N(b)/(√3·X)`, the two column
coefficients `p_{μf²}` with `c = b⁴T⁵V⁶`, the weights `W₀` and the dual weight. -/
def rcDual (W : ℝ → ℂ) (X H : ℝ) (f : 𝓞 K) (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ)
    (b T V : Finset Pr) (μ : 𝓞 K) (M1 M2 : Finset Pr) : ℂ :=
  ((-1 : ℂ) ^ T.card * (-1) ^ V.card) *
    (ξ1 (cls4 V) * conj (ξ2 (cls4 V)) * (chiS V f ^ 4 * conj (chiS V f ^ 4)) *
      (chiS V μ * conj (chiS V μ)) * (chiS (b ∪ T) f ^ 4 * conj (chiS (b ∪ T) f ^ 4))) *
    ((2 * H * nI b / (Real.sqrt 3 * X) : ℝ) : ℂ) *
    (colP ξ1 (μ * f ^ 2) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M1 *
      conj (colP ξ2 (μ * f ^ 2) (eS b ^ 4 * eS T ^ 5 * eS V ^ 6) M2)) *
    (MellinSep.W0c W (nI b * nI T * nI V * nI M1 / X) *
      conj (MellinSep.W0c W (nI b * nI T * nI V * nI M2 / X))) *
    dualW H (V ∪ M1) (V ∪ M2) T μ

/-- **One term of the Möbius-expanded dual sum in row/column form**: for pairwise disjoint
`b, T, V, M_j` (`M₁, M₂` may meet), `(−1)^{|V|}·w(bT; V∪M₁, V∪M₂)·τ(V∪M₁, V∪M₂, T)` is
`Σ_{μ∈E} rcDual(b, T, V, μ, M₁, M₂)`. -/
theorem term_factor_dual (W : ℝ → ℂ) {X H : ℝ} (hX : 0 < X) (f : 𝓞 K)
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (E : Finset (𝓞 K)) {b T V M1 M2 : Finset Pr}
    (hbT : Disjoint b T) (hbV : Disjoint b V) (hb1 : Disjoint b M1) (hb2 : Disjoint b M2)
    (hTV : Disjoint T V) (hT1 : Disjoint T M1) (hT2 : Disjoint T M2) (hV1 : Disjoint V M1)
    (hV2 : Disjoint V M2) :
    (-1 : ℂ) ^ V.card * (wNat W X f (b ∪ T) (V ∪ M1) (V ∪ M2) *
        tauDual H E ξ1 ξ2 (V ∪ M1) (V ∪ M2) T) =
      ∑ μ ∈ E, rcDual W X H f ξ1 ξ2 b T V μ M1 M2 := by
  have hd1 : Disjoint (b ∪ T) (V ∪ M1) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb1⟩, hTV, hT1⟩
  have hd2 : Disjoint (b ∪ T) (V ∪ M2) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hbV, hb2⟩, hTV, hT2⟩
  have hVB : Disjoint V (b ∪ T) := Finset.disjoint_union_right.2 ⟨hbV.symm, hTV.symm⟩
  have hn1 : nI ((b ∪ T) ∪ (V ∪ M1)) = nI b * nI T * (nI V * nI M1) := by
    rw [nI_union hd1, nI_union hbT, nI_union hV1]
  have hn2 : nI ((b ∪ T) ∪ (V ∪ M2)) = nI b * nI T * (nI V * nI M2) := by
    rw [nI_union hd2, nI_union hbT, nI_union hV2]
  have hk : kap H (V ∪ M1) (V ∪ M2) T =
      2 * H / (Real.sqrt 3 * Real.sqrt (nI V * nI M1 * (nI V * nI M2)) * nI T) := by
    unfold kap; rw [nI_union hV1, nI_union hV2]
  have hWK : W (nI ((b ∪ T) ∪ (V ∪ M1)) / X) * conj (W (nI ((b ∪ T) ∪ (V ∪ M2)) / X)) *
      ((kap H (V ∪ M1) (V ∪ M2) T : ℝ) : ℂ) =
      ((2 * H * nI b / (Real.sqrt 3 * X) : ℝ) : ℂ) *
        (MellinSep.W0c W (nI b * nI T * nI V * nI M1 / X) *
          conj (MellinSep.W0c W (nI b * nI T * nI V * nI M2 / X))) := by
    rw [hn1, hn2, hk]
    exact WW_kapC W hX (nI_pos b) (nI_pos T) (nI_pos V) (nI_pos M1) (nI_pos M2)
  have e1 : chiS V (eS (b ∪ T)) * conj (chiS V (eS (b ∪ T))) = 1 := chiS_mul_conj_eS hVB
  have e2 : chiS V (eS T) * conj (chiS V (eS T)) = 1 := chiS_mul_conj_eS hTV.symm
  have e3 : ((-1 : ℂ) ^ V.card) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  unfold tauDual
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  unfold wNat rcDual
  rw [colP_natural ξ1 hbT hV1 μ f, colP_natural ξ2 hbT hV2 μ f]
  simp only [chiS_union hd1, chiS_union hd2, chiS_union hV1, chiS_union hV2, cls4_union hV1,
    cls4_union hV2, Finset.card_union_of_disjoint hV1, Finset.card_union_of_disjoint hV2, pow_add,
    map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
  set w1 := W (nI ((b ∪ T) ∪ (V ∪ M1)) / X)
  set w2 := W (nI ((b ∪ T) ∪ (V ∪ M2)) / X)
  set kC : ℂ := ((kap H (V ∪ M1) (V ∪ M2) T : ℝ) : ℂ)
  set D := dualW H (V ∪ M1) (V ∪ M2) T μ
  set cV := chiS V (eS (b ∪ T))
  set c1 := chiS M1 (eS (b ∪ T))
  set c2 := chiS M2 (eS (b ∪ T))
  set fB := chiS (b ∪ T) f
  set fV := chiS V f
  set f1 := chiS M1 f
  set f2 := chiS M2 f
  set tV := chiS V (eS T)
  set t1 := chiS M1 (eS T)
  set t2 := chiS M2 (eS T)
  set uV := chiS V μ
  set u1 := chiS M1 μ
  set u2 := chiS M2 μ
  set x1V := ξ1 (cls4 V)
  set x1M := ξ1 (cls4 M1)
  set x2V := ξ2 (cls4 V)
  set x2M := ξ2 (cls4 M2)
  set sV := (-1 : ℂ) ^ V.card
  set sT := (-1 : ℂ) ^ T.card
  set s1 := (-1 : ℂ) ^ M1.card
  set s2 := (-1 : ℂ) ^ M2.card
  calc _ = (sT * sV) * (x1V * conj x2V * (fV ^ 4 * conj fV ^ 4) * (uV * conj uV) *
          (fB ^ 4 * conj fB ^ 4)) *
        ((s1 * x1M * (c1 ^ 4 * t1) * (f1 ^ 4 * conj u1)) *
          (s2 * conj x2M * (conj c2 ^ 4 * conj t2) * (conj f2 ^ 4 * u2))) *
        (w1 * conj w2 * kC) * D * ((cV * conj cV) ^ 4 * (tV * conj tV) * sV ^ 2) := by ring
    _ = _ := by rw [hWK, e1, e2, e3]; ring

/-- **The chain for one pair of characters**: from the sum over pairs of sets of primes to the
row/column form, by `sum_pair_chain` with the natural form `wPair_split` and the factorization
`term_factor_dual`. -/
theorem xi_chain_dual (W : ℝ → ℂ) {X H : ℝ} (hX : 0 < X) (f : 𝓞 K) (E : Finset (𝓞 K))
    (ξ1 ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (U : Finset Pr) :
    ∑ A1 ∈ U.powerset, ∑ A2 ∈ U.powerset, wPair W X f A1 A2 *
        ∑ T ∈ (A1 ∩ A2).powerset, tauDual H E ξ1 ξ2 (A1 \ A2) (A2 \ A1) T =
      ∑ b ∈ U.powerset, ∑ T ∈ (U \ b).powerset, ∑ V ∈ (U \ (b ∪ T)).powerset, ∑ μ ∈ E,
        ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
          rcDual W X H f ξ1 ξ2 b T V μ M1 M2 :=
  sum_pair_chain U (wPair W X f) (wNat W X f) (fun h1 h2 h12 => wPair_split W X f h1 h2 h12)
    (tauDual H E ξ1 ξ2) E (rcDual W X H f ξ1 ξ2)
    (fun hbT hbV hb1 hb2 hTV hT1 hT2 hV1 hV2 =>
      term_factor_dual W hX f ξ1 ξ2 E hbT hbV hb1 hb2 hTV hT1 hT2 hV1 hV2)

open Classical in
/-- **The dual mean square of a row in row/column form** (the companion paper's display for
`𝒜(W) − Z` in its proof of Lemma 7.1, for one row `f`, before the sum over `f` and the normalization
`1/(LF)` of (5.10), with a pair of characters modulo `4` in place of its one `ξ_1`): with
`W` vanishing beyond `β'`, `U` containing the primes of norm at most `β'X`, `Φ̂` vanishing beyond `R`
and `3R²(β'X)² ≤ 4HY`, the smoothed dual mean square of the row is the zero frequency
`Σ_A |χ_A(f)⁴|²|W(N(A)/X)|²·Σ_{T⊆A} (−1)^{|T|}·2H/(√3·N(T))·Φ̂(0)` plus
`Σ_{ξ₁,ξ₂} ĉ(ξ₁, ξ₂⁻¹)·Σ_{b, T, V, μ, M₁, M₂} rcDual`, over `b ⊆ U`, `T ⊆ U∖b`, `V ⊆ U∖(b∪T)`, the
nonzero `μ` of norm at most `Y`, and `M₁, M₂ ⊆ U∖(b∪T)∖V`. -/
theorem dualMS_rowcol (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) {W : ℝ → ℂ} {β' : ℝ}
    (hW : ∀ x, β' < x → W x = 0) {X : ℝ} (hX : 0 < X) {U : Finset Pr}
    (hU : primesLe (β' * X) ⊆ U) (f : 𝓞 K) {H : ℝ} (hH : 0 < H) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ ρ, R ≤ ρ → dualG ρ = 0) {Y : ℝ} (hY : 3 * R ^ 2 * (β' * X) ^ 2 ≤ 4 * H * Y) :
    ∑' u : 𝓞 K, colSum ξ W X 1 u f * conj (colSum ξ W X 1 u f) *
        Majorant.Phi (σO u / (Real.sqrt H : ℂ)) =
      ∑ A ∈ U.powerset, (chiS A f ^ 4 * conj (chiS A f ^ 4)) * (W (nI A / X) * conj (W (nI A / X))) *
          ∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 +
        ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ *
            ∑ b ∈ U.powerset, ∑ T ∈ (U \ b).powerset, ∑ V ∈ (U \ (b ∪ T)).powerset,
              ∑ μ ∈ (eltsLe Y).erase 0,
                ∑ M1 ∈ ((U \ (b ∪ T)) \ V).powerset, ∑ M2 ∈ ((U \ (b ∪ T)) \ V).powerset,
                  rcDual W X H f ξ1 ξ2 b T V μ M1 M2 := by
  rw [dualMS_clean ξ hW hX hU f H hH]
  have hle : ∀ A : Finset Pr, W (nI A / X) ≠ 0 → nI A ≤ β' * X := fun A hA => by
    by_contra hc
    push Not at hc
    exact hA (hW _ (by rw [lt_div_iff₀ hX]; linarith))
  have hpair : ∀ A1 ∈ U.powerset, ∀ A2 ∈ U.powerset,
      wPair W X f A1 A2 * (ξ (cls4 (A1 \ A2)) * conj (ξ (cls4 (A2 \ A1))) *
          ∑ T ∈ (A1 ∩ A2).powerset, (-1 : ℂ) ^ T.card * (kap H (A1 \ A2) (A2 \ A1) T : ℂ) *
            pairPsiDual (A1 \ A2) (A2 \ A1) *
            (chiS (A1 \ A2) (eS T) * conj (chiS (A2 \ A1) (eS T))) *
            ∑' μ : 𝓞 K, conj (chiS (A1 \ A2) μ * conj (chiS (A2 \ A1) μ)) *
              dualW H (A1 \ A2) (A2 \ A1) T μ) =
      (if A1 = A2 then (chiS A1 f ^ 4 * conj (chiS A1 f ^ 4)) *
          (W (nI A1 / X) * conj (W (nI A1 / X))) *
          ∑ T ∈ A1.powerset, (-1 : ℂ) ^ T.card * (kap H ∅ ∅ T : ℂ) * dualG 0 else 0) +
        ∑ ξ1 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ, ∑ ξ2 : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ,
          pairCoeff (pairPsiXi ξ) ξ1 ξ2⁻¹ *
            (wPair W X f A1 A2 * ∑ T ∈ (A1 ∩ A2).powerset,
              tauDual H ((eltsLe Y).erase 0) ξ1 ξ2 (A1 \ A2) (A2 \ A1) T) := by
    intro A1 _ A2 _
    by_cases hz : W (nI A1 / X) = 0 ∨ W (nI A2 / X) = 0
    · have h0 : wPair W X f A1 A2 = 0 := by
        unfold wPair; rcases hz with h | h <;> rw [h] <;> simp
      simp only [h0, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
      split_ifs with he
      · subst he
        rcases hz with h | h <;> rw [h] <;> simp
      · rfl
    · push Not at hz
      rw [pair_char_form_dual ξ H hH hR0 hR hY (hle A1 hz.1) (hle A2 hz.2), mul_add]
      congr 1
      · split_ifs with he
        · subst he
          unfold wPair
          simp only [Finset.sdiff_self, chiS_empty, one_pow, map_one, one_mul]
        · rw [mul_zero]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ξ1 _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ξ2 _ => ?_
        ring
  rw [Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 hA2 => hpair A1 hA1 A2 hA2]
  simp only [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun A1 hA1 => ?_
    rw [Finset.sum_ite_eq, ite_eq_left hA1]
  · rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ1 _ => ?_
    rw [Finset.sum_congr rfl fun A1 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ2 _ => ?_
    simp_rw [← Finset.mul_sum]
    congr 1
    exact xi_chain_dual W hX f _ ξ1 ξ2 U

end Eis

end

#print axioms Eis.chiS_pow_four
#print axioms Eis.cls4_union
#print axioms Eis.colP_union
#print axioms Eis.norm_colP_le
#print axioms Eis.norm_pairPsiXi_le
#print axioms Eis.conj_xi_cls4
#print axioms Eis.dualPair_expand
#print axioms Eis.cls4_empty
#print axioms Eis.pairPsiDual_empty
#print axioms Eis.chiS_eS_pow_six_eq_one
#print axioms Eis.colP_eq_zero_of_dvd
#print axioms Eis.colP_natural
#print axioms Eis.WW_kapC
#print axioms Eis.regroup7
#print axioms Eis.dualMS_clean
#print axioms Eis.pair_char_form_dual
#print axioms Eis.wPair_split
#print axioms Eis.term_factor_dual
#print axioms Eis.xi_chain_dual
#print axioms Eis.dualMS_rowcol
