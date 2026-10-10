import EisensteinPrepared

/-! # The theta transformation for the rows, and the transformed terms as prepared sums (round 341)

S5d of round 312's plan, part 3: the representation in the companion paper's proof of its Lemma 6.6, with its
Proposition 6.2 and Lemmas 6.3 and 6.4 (the theta transformation, its uniformity in the twist, and the support
and size of the cusp coefficients and of the transformed weight) displayed as one hypothesis.

* **The local factors** `B_{P,j}` (`Bloc`, the paper's (6.5)): `B_{P,1} = χ_P³` (`Bloc_one`),
  `B_{P,4} = −N(P)^{−1/2} + N(P)^{1/2}1_{P∣x}` (`Bloc_four`), `|B_{P,j}| ≤ 1` at `j ≢ 0, 4` and
  `|B_{P,0}| ≤ N(P)^{−1/2}`.
* **The dual parameters** `x = λ⁴ℓ = uλ^m n b³` (`DualIdx`, `dualPt`, `dualNorm`: the paper's Lemma 6.4, its
  `m ≥ −4` written as `m + 4 ∈ ℕ`) and **a transformed term** (`dualTerm`: the paper's (6.9) in these
  parameters, with `c = c₀∏_{P∈𝒜}P·k₀`).
* **`ThetaRows`**: the theta transformation for the rows `u₀tk₀`, displayed. `T(X; u₀tk₀, g)` is a sum over
  `i < K_H` and the admissible active sets `𝒜` of `C·dualTerm` with `|C| ≤ 1`; the data `(d, c₀)` depend on
  `k₀` only through `k₀ mod M`; `|d| ≤ K_d 3^{m/6}N(𝔟)^{1/2}`, supported on squarefree `𝔫` with `N𝔫, N𝔟`
  prime to `3`; the first two derivatives of `h(w) = V^♯(e^w)` are at most `C_w N(1 + e^w)^{−1}`.
  The display also contains the paper's (6.17), which it derives from sextic reciprocity, and the
  uniqueness of the parametrization of `ℓ`.
* **The term identity** (`dualTerm_summand_eq`): each summand is `(uλ^m/k₀)₆³` times a term of the prepared sum
  `𝒮_{m−4}[A_{u,m}, Y](k₀)` with `Y = N(c₀)²N(𝒜)²H₀²/X` (the paper's display after its (6.18)).
* **Regrouping** (`summable_dualSummand`, `dualTerm_eq_sum`): the transformed series converges absolutely and
  equals `Σ_u Σ_{m ≥ 0} (uλ^m/k₀)₆³ 𝒮_{m−4}[A_{u,m}, Y](k₀)`.
* **The factors at `j_P ≡ 4`, reindexed** (`prod_B4_eq`, `prepTerm_reindex`, `prepSum_B4`): the paper's identity
  for `B_{p,4}` after its (6.18), at every `P ∈ Q` at once: a sum over `T₁ ⊆ T ⊆ Q` of
  `(𝔯₁𝔯₂/k)₆³ 𝒮_m[reCoef, Y/(N𝔯₁N𝔯₂³)](k)`, `𝔯₁ = ∏_{T₁}P`, `𝔯₂ = ∏_{T∖T₁}P`, through the injective
  reindexing `(𝔫′, 𝔟′) ↦ (𝔯₁𝔫′, 𝔯₂𝔟′)`.
-/

open Complex MeasureTheory Set NumberField Ideal UniqueFactorizationMonoid
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section

namespace Eis

/-! ### The local factors `B_{P,j}` -/

open Classical in
/-- `χ_P^e(x)`: the `e`-th power of the sextic character at `P`, extended by zero on `P`. -/
def chiPow (P : Ideal (𝓞 K)) (e : ℕ) (x : 𝓞 K) : ℂ := if x ∈ P then 0 else chiP P x ^ e

open Classical in
/-- **The local factor** `B_{P,j}` of the companion paper's (6.5): `χ_P(x)^{−j−2}` for `j ≠ 0, 4`,
`N(P)^{−1/2}(−1 + N(P)·1_{P∣x})` for `j = 4`, and `N(P)^{−1/2}χ_P(x)^{−2}` for `j = 0`, with `j` read
modulo `6`, the negative powers through `χ_P⁶ = 1`, and the zero extension on `P`. -/
def Bloc (P : Ideal (𝓞 K)) (j : ℕ) (x : 𝓞 K) : ℂ :=
  if j % 6 = 4 then
    ((Real.sqrt (absNorm P) : ℝ) : ℂ)⁻¹ * (-1 + (absNorm P : ℂ) * if x ∈ P then 1 else 0)
  else if j % 6 = 0 then ((Real.sqrt (absNorm P) : ℝ) : ℂ)⁻¹ * chiPow P 4 x
  else chiPow P ((12 - (j % 6 + 2)) % 6) x

theorem norm_chiPow_le (P : Ideal (𝓞 K)) (e : ℕ) (x : 𝓞 K) : ‖chiPow P e x‖ ≤ 1 := by
  unfold chiPow
  split_ifs
  · simp
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_chiP_le P x)

/-- `|B_{P,j}| ≤ 1` for `j ≢ 0, 4`. -/
theorem norm_Bloc_le_one {P : Ideal (𝓞 K)} {j : ℕ} (h4 : j % 6 ≠ 4) (h0 : j % 6 ≠ 0) (x : 𝓞 K) :
    ‖Bloc P j x‖ ≤ 1 := by
  unfold Bloc; rw [ite_eq_right h4, ite_eq_right h0]; exact norm_chiPow_le _ _ _

/-- `|B_{P,0}| ≤ N(P)^{−1/2}`. -/
theorem norm_Bloc_zero_le {P : Ideal (𝓞 K)} {j : ℕ} (h0 : j % 6 = 0) (x : 𝓞 K) :
    ‖Bloc P j x‖ ≤ (Real.sqrt (absNorm P))⁻¹ := by
  have h4 : j % 6 ≠ 4 := by omega
  unfold Bloc; rw [ite_eq_right h4, ite_eq_left h0, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) (norm_chiPow_le _ _ _)

/-- `B_{P,4}(x) = −N(P)^{−1/2} + N(P)^{1/2}·1_{P∣x}`. -/
theorem Bloc_four {P : Ideal (𝓞 K)} {j : ℕ} (h4 : j % 6 = 4) (hP : 0 < (absNorm P : ℝ)) (x : 𝓞 K) :
    Bloc P j x = -((Real.sqrt (absNorm P) : ℝ) : ℂ)⁻¹ +
      ((Real.sqrt (absNorm P) : ℝ) : ℂ) * (by classical exact if x ∈ P then 1 else 0) := by
  classical
  unfold Bloc
  rw [ite_eq_left h4]
  have hs : ((Real.sqrt (absNorm P) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hP).ne'
  have hsq : ((absNorm P : ℕ) : ℂ) = ((Real.sqrt (absNorm P) : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hP.le]; push_cast; rfl
  split_ifs
  · rw [hsq]; field_simp
  · rw [hsq]; field_simp

/-- `B_{P,1}(x) = χ_P(x)³`. -/
theorem Bloc_one (P : Ideal (𝓞 K)) (x : 𝓞 K) : Bloc P 1 x = chiP P x ^ 3 := by
  classical
  unfold Bloc chiPow
  rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
  by_cases h : x ∈ P
  · rw [ite_eq_left h, chiP_eq_zero_of_mem h]; norm_num
  · rw [ite_eq_right h]

/-! ### The data of the display -/

/-- The exponent `j_P ≡ v_P(t) + 4v_P(g) (mod 6)` of the companion paper's (6.17). -/
def jFix (t g : 𝓞 K) (P : Pr) : ℕ :=
  ((normalizedFactors (span {t})).count P.1 + 4 * (normalizedFactors (span {g})).count P.1) % 6

open Classical in
/-- The admissible active sets: `{P ∈ 𝒫_fix : j_P ≠ 0} ⊆ 𝒜 ⊆ 𝒫_fix`, where `𝒫_fix` is the set of
primes prime to `6` dividing `tg`. -/
def admissible (t g : 𝓞 K) : Finset (Finset Pr) :=
  (primeSet (span {t * g})).powerset.filter fun A =>
    ∀ P ∈ primeSet (span {t * g}), jFix t g P ≠ 0 → P ∈ A

/-- The parameters `(u, m, 𝔫, 𝔟)` of the dual sums. -/
abbrev DualIdx : Type := (𝓞 K)ˣ × ℕ × Ideal (𝓞 K) × Ideal (𝓞 K)

/-- The point `x = u·λ^m·n·b³` of the dual sums, `λ = ω − 1`, with `n, b` the primary generators. -/
def dualPt (q : DualIdx) : 𝓞 K := (q.1 : 𝓞 K) * (Eis.ω - 1) ^ q.2.1 * pgen q.2.2.1 * pgen q.2.2.2 ^ 3

/-- `N(x) = 3^m N𝔫 N𝔟³`, in the parameters. -/
def dualNorm (q : DualIdx) : ℝ := (3 : ℝ) ^ q.2.1 * (absNorm q.2.2.1 : ℝ) * (absNorm q.2.2.2 : ℝ) ^ 3

/-- **A transformed term** (the companion paper's (6.9) in the parameters `x = λ⁴ℓ = uλ^m n b³` of its
Lemma 6.4): `Σ_{u,m,𝔫,𝔟} d·Π_{P∈𝒜}B_{P,j_P}(x)·Π_{P∣k₀}B_{P,1}(x)·V^♯(N(ℓ)X/N(c)²)/√N(x)`, with
`N(ℓ) = N(x)/81`, `N(c) = N(c₀)·N(𝒜)·N(k₀)` and `V^♯(y) = h(log y)`. -/
def dualTerm (h : ℝ → ℂ) (d : DualIdx → ℂ) (c₀ : 𝓞 K) (A : Finset Pr) (j : Pr → ℕ) (k₀ : 𝓞 K)
    (X : ℝ) : ℂ :=
  ∑' q : DualIdx,
    d q * (∏ P ∈ A, Bloc P.1 (j P) (dualPt q)) *
      (∏ P ∈ primeSet (span {k₀}), Bloc P.1 1 (dualPt q)) *
      h (Real.log (dualNorm q / 81 * X /
        ((absNorm (span {c₀}) : ℝ) ^ 2 * nI A ^ 2 * (absNorm (span {k₀}) : ℝ) ^ 2))) /
      ((Real.sqrt (dualNorm q) : ℝ) : ℂ)

/-- **The theta transformation for the rows `u₀tk₀`, displayed**: the companion paper's Proposition 6.2
with its Lemmas 6.3 and 6.4, for the twists `Ψ_{u₀tk₀}` written as in its (6.17). -/
def ThetaRows : Prop :=
  ∃ J : ℕ, ∀ α β : ℝ, 0 < α → α ≤ β →
  ∃ (Cw : ℝ) (M : 𝓞 K) (KH : ℕ) (Kd Kc : ℝ), M ≠ 0 ∧
  ∀ W : ℝ → ℂ, ContDiff ℝ ∞ W → (∀ y, y < α ∨ β < y → W y = 0) →
  ∀ N : ℝ, (∀ i ≤ J, ∀ y, ‖iteratedDeriv i W y‖ ≤ N) →
  ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧
    (∀ i ≤ 2, ∀ w, ‖iteratedDeriv i h w‖ ≤ Cw * N * (1 + Real.exp w) ^ (-(1 : ℝ))) ∧
  ∀ (ξ : MulChar (𝓞 K ⧸ span {(4 : 𝓞 K)}) ℂ) (u₀ : (𝓞 K)ˣ) (t g : 𝓞 K), t ≠ 0 → g ≠ 0 →
    Squarefree (span {t}) →
  ∃ (d : (𝓞 K ⧸ span {M}) → ℕ → Finset Pr → DualIdx → ℂ)
    (c₀ : (𝓞 K ⧸ span {M}) → ℕ → Finset Pr → 𝓞 K),
    (∀ ρ i A, c₀ ρ i A ≠ 0 ∧ (absNorm (span {c₀ ρ i A}) : ℝ) ≤ Kc) ∧
    (∀ ρ i A q, d ρ i A q ≠ 0 →
      Squarefree q.2.2.1 ∧ (absNorm q.2.2.1).Coprime 3 ∧ (absNorm q.2.2.2).Coprime 3) ∧
    (∀ ρ i A q, ‖d ρ i A q‖ ≤ Kd * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2)) ∧
  ∀ k₀ : 𝓞 K, Primary k₀ → Squarefree (span {k₀}) → (absNorm (span {k₀})).Coprime 6 →
    IsCoprime k₀ (t * g) →
  ∀ X : ℝ, 0 < X → ∃ C : ℕ → Finset Pr → ℂ, (∀ i A, ‖C i A‖ ≤ 1) ∧
    compT ξ (u₀ * t * k₀) g W X = ∑ i ∈ Finset.range KH, ∑ A ∈ admissible t g,
      C i A * dualTerm h (d (Ideal.Quotient.mk _ k₀) i A) (c₀ (Ideal.Quotient.mk _ k₀) i A) A
        (jFix t g) k₀ X

/-! ### The dual points -/

theorem pgen_mul3 {I J : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) (hJ : (absNorm J).Coprime 3) :
    pgen (I * J) = pgen I * pgen J := by
  obtain ⟨h1, h2⟩ := pgen_spec3 hI
  obtain ⟨h1', h2'⟩ := pgen_spec3 hJ
  have e : span {pgen I * pgen J} = I * J := by
    rw [← Ideal.span_singleton_mul_span_singleton, h2, h2']
  rw [← e]; exact pgen_eq (h1.mul h1')

theorem lam_not_mem (P : Pr) : (Eis.ω - 1 : 𝓞 K) ∉ P.1 := by
  intro h
  obtain ⟨y, hy⟩ := lam_dvd_three
  have h3 : (3 : 𝓞 K) ∈ P.1 := by rw [hy]; exact P.1.mul_mem_right _ h
  have h6 : (2 : 𝓞 K) * 3 ∈ P.1 := P.1.mul_mem_left _ h3
  norm_num at h6
  exact P.2.2 h6

theorem unit_not_mem (P : Pr) (u : (𝓞 K)ˣ) : (u : 𝓞 K) ∉ P.1 := fun h =>
  P.2.1.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)

theorem pgen_mem_iff {P : Pr} {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 3) :
    pgen I ∈ P.1 ↔ P.1 ∣ I := by
  have e := (pgen_spec3 hI).2
  rw [Ideal.dvd_iff_le]
  conv_rhs => rw [← e]
  rw [Ideal.span_singleton_le_iff_mem]

/-- `x = uλ^m n b³ ∈ P` iff `P ∣ 𝔫` or `P ∣ 𝔟`, for `P` prime to `6`. -/
theorem dualPt_mem_iff (P : Pr) {q : DualIdx} (hn : (absNorm q.2.2.1).Coprime 3)
    (hb : (absNorm q.2.2.2).Coprime 3) :
    dualPt q ∈ P.1 ↔ P.1 ∣ q.2.2.1 ∨ P.1 ∣ q.2.2.2 := by
  have hP := P.2.1.isPrime
  unfold dualPt
  constructor
  · intro h
    rcases hP.mem_or_mem h with h1 | h1
    · rcases hP.mem_or_mem h1 with h2 | h2
      · rcases hP.mem_or_mem h2 with h3 | h3
        · exact absurd h3 (unit_not_mem P q.1)
        · exact absurd (hP.mem_of_pow_mem _ h3) (lam_not_mem P)
      · exact Or.inl ((pgen_mem_iff hn).1 h2)
    · exact Or.inr ((pgen_mem_iff hb).1 (hP.mem_of_pow_mem _ h1))
  · rintro (h | h)
    · exact P.1.mul_mem_right _ (P.1.mul_mem_left _ ((pgen_mem_iff hn).2 h))
    · exact P.1.mul_mem_left _ (P.1.pow_mem_of_mem ((pgen_mem_iff hb).2 h) 3 (by norm_num))

/-- `Π_{P ∣ k₀} B_{P,1}(x) = (x/k₀)₆³` for `k₀` squarefree of norm prime to `6`. -/
theorem prod_Bloc_one {k₀ : 𝓞 K} (h6 : (absNorm (span {k₀})).Coprime 6)
    (hsq : Squarefree (span {k₀})) (x : 𝓞 K) :
    ∏ P ∈ primeSet (span {k₀}), Bloc P.1 1 x = sym6 x (span {k₀}) ^ 3 := by
  rw [sym6, normalizedFactors_eq_map h6 hsq, Multiset.map_map, ← Finset.prod_eq_multiset_prod,
    ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun P _ => Bloc_one P.1 x

/-- `(m/𝔞)₆⁹ = (m/𝔞)₆³` for `𝔞` of norm prime to `6`. -/
theorem sym6_pow_nine {I : Ideal (𝓞 K)} (hI : (absNorm I).Coprime 6) (m : 𝓞 K) :
    sym6 m I ^ 9 = sym6 m I ^ 3 := by
  have h2 := sym6_sq_eq_pow_eight hI m
  calc sym6 m I ^ 9 = sym6 m I ^ 8 * sym6 m I := by ring
    _ = sym6 m I ^ 2 * sym6 m I := by rw [h2]
    _ = sym6 m I ^ 3 := by ring

/-- `(x/k₀)₆³ = (uλ^m/k₀)₆³·(nb/k₀)₆³` for `x = uλ^m n b³`. -/
theorem sym6_dualPt {k₀ : 𝓞 K} (h6 : (absNorm (span {k₀})).Coprime 6) (q : DualIdx) :
    sym6 (dualPt q) (span {k₀}) ^ 3 =
      sym6 ((q.1 : 𝓞 K) * (Eis.ω - 1) ^ q.2.1) (span {k₀}) ^ 3 *
        sym6 (pgen q.2.2.1 * pgen q.2.2.2) (span {k₀}) ^ 3 := by
  unfold dualPt
  rw [sym6_mul_left, sym6_mul_left, sym6_mul_left (pgen q.2.2.1),
    show pgen q.2.2.2 ^ 3 = pgen q.2.2.2 ^ (2 + 1) from rfl, sym6_pow_succ]
  have := sym6_pow_nine h6 (pgen q.2.2.2)
  calc (sym6 (↑q.1 * (Eis.ω - 1) ^ q.2.1) (span {k₀}) * sym6 (pgen q.2.2.1) (span {k₀}) *
        sym6 (pgen q.2.2.2) (span {k₀}) ^ (2 + 1)) ^ 3
      = sym6 (↑q.1 * (Eis.ω - 1) ^ q.2.1) (span {k₀}) ^ 3 * sym6 (pgen q.2.2.1) (span {k₀}) ^ 3 *
          sym6 (pgen q.2.2.2) (span {k₀}) ^ 9 := by ring
    _ = _ := by rw [this]; ring

instance : Finite (𝓞 K)ˣ :=
  Set.finite_univ_iff.1 ((List.finite_toSet _).subset fun u _ => units_mem u)

/-- The coefficient of the prepared sums of a transformed term at `(u, m)`:
`A(𝔫, 𝔟) = 3^{−m/6−4/3}·d(u, m, 𝔫, 𝔟)·Π_{P∈𝒜}B_{P,j_P}(x)/√N𝔟`. -/
def dualCoef (d : DualIdx → ℂ) (A : Finset Pr) (j : Pr → ℕ) (u : (𝓞 K)ˣ) (m : ℕ)
    (n b : Ideal (𝓞 K)) : ℂ :=
  (((3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) : ℝ) : ℂ) * d (u, m, n, b) *
    ∏ P ∈ A, Bloc P.1 (j P) (dualPt (u, m, n, b))

/-- The row phase `(uλ^m/k₀)₆³`. -/
def dualPhase (u : (𝓞 K)ˣ) (m : ℕ) (k₀ : 𝓞 K) : ℂ :=
  sym6 ((u : 𝓞 K) * (Eis.ω - 1) ^ m) (span {k₀}) ^ 3

/-- The scale `Y = N(c₀)²N(𝒜)²H₀²/X` of a transformed term. -/
def dualY (c₀ : 𝓞 K) (A : Finset Pr) (H₀ X : ℝ) : ℝ :=
  (absNorm (span {c₀}) : ℝ) ^ 2 * nI A ^ 2 * H₀ ^ 2 / X

theorem norm_dualPhase_le (u : (𝓞 K)ˣ) (m : ℕ) (k₀ : 𝓞 K) : ‖dualPhase u m k₀‖ ≤ 1 := by
  unfold dualPhase; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_sym6_le _ _)

theorem three_zpow_sub_four (m : ℕ) : (3 : ℝ) ^ ((m : ℤ) - 4) = (3 : ℝ) ^ m / 81 := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast]; norm_num

/-- `√(3^m a b³) = 3^{m/2}·√a·b·√b`. -/
theorem sqrt_dualNorm (m : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((3 : ℝ) ^ m * a * b ^ 3) =
      (3 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt a * (b * Real.sqrt b) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    show b ^ 3 = b ^ 2 * b by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hb,
    Real.sqrt_eq_rpow ((3 : ℝ) ^ m), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 2; ring_nf

/-- **The term identity**: the summand of a transformed term at `(u, m, 𝔫, 𝔟)` is the row phase
`(uλ^m/k₀)₆³` times the term of the prepared sum `𝒮_{m−4}[A_{u,m}, Y](k₀)` at `(𝔫, 𝔟)`. -/
theorem dualTerm_summand_eq (h : ℝ → ℂ) (d : DualIdx → ℂ) {c₀ : 𝓞 K} (hc₀ : c₀ ≠ 0)
    (A : Finset Pr) (j : Pr → ℕ) {k₀ : 𝓞 K} (h6 : (absNorm (span {k₀})).Coprime 6)
    (hsq : Squarefree (span {k₀})) {H₀ X : ℝ} (hH : 0 < H₀) (hX : 0 < X) (q : DualIdx) :
    d q * (∏ P ∈ A, Bloc P.1 (j P) (dualPt q)) *
        (∏ P ∈ primeSet (span {k₀}), Bloc P.1 1 (dualPt q)) *
        h (Real.log (dualNorm q / 81 * X /
          ((absNorm (span {c₀}) : ℝ) ^ 2 * nI A ^ 2 * (absNorm (span {k₀}) : ℝ) ^ 2))) /
        ((Real.sqrt (dualNorm q) : ℝ) : ℂ) =
      dualPhase q.1 q.2.1 k₀ * prepTerm h (dualY c₀ A H₀ X) H₀ ((q.2.1 : ℤ) - 4)
        (dualCoef d A j q.1 q.2.1) k₀ q.2.2.1 q.2.2.2 := by
  obtain ⟨u, m, n, b⟩ := q
  have hk : 0 < (absNorm (span {k₀}) : ℝ) := absNorm_pos_of_coprime6 h6
  have hc : 0 < (absNorm (span {c₀}) : ℝ) := by
    have : absNorm (span {c₀}) ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc₀
    exact_mod_cast Nat.pos_of_ne_zero this
  have hnI := nI_pos A
  rw [prod_Bloc_one h6 hsq, sym6_dualPt h6]
  -- the arguments of the weight agree
  have harg : dualNorm (u, m, n, b) / 81 * X /
      ((absNorm (span {c₀}) : ℝ) ^ 2 * nI A ^ 2 * (absNorm (span {k₀}) : ℝ) ^ 2) =
      (3 : ℝ) ^ ((m : ℤ) - 4) * absNorm n * (absNorm b : ℝ) ^ 3 * H₀ ^ 2 /
        (dualY c₀ A H₀ X * (absNorm (span {k₀}) : ℝ) ^ 2) := by
    rw [three_zpow_sub_four]
    unfold dualNorm dualY
    field_simp
  rw [harg]
  unfold prepTerm dualCoef dualPhase dualNorm
  simp only
  rcases (Nat.cast_nonneg (absNorm n) : (0 : ℝ) ≤ absNorm n).eq_or_lt with hn | hn
  · rw [← hn]; simp
  rcases (Nat.cast_nonneg (absNorm b) : (0 : ℝ) ≤ absNorm b).eq_or_lt with hb | hb
  · rw [← hb]; simp
  rw [sqrt_dualNorm m hn.le hb.le]
  have hs1 : 0 < Real.sqrt (absNorm n : ℝ) := Real.sqrt_pos.2 hn
  have hs2 : 0 < Real.sqrt (absNorm b : ℝ) := Real.sqrt_pos.2 hb
  have e3 : (3 : ℝ) ^ (-(((m : ℤ) - 4 : ℤ) : ℝ) / 3) * (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) =
      ((3 : ℝ) ^ ((m : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; push_cast; ring
  have h3pos : 0 < (3 : ℝ) ^ ((m : ℝ) / 2) := by positivity
  have key : ((((3 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt (absNorm n) *
      ((absNorm b : ℝ) * Real.sqrt (absNorm b)) : ℝ)) : ℂ)⁻¹ =
      (((3 : ℝ) ^ (-(((m : ℤ) - 4 : ℤ) : ℝ) / 3) : ℝ) : ℂ) *
        ((((3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) : ℝ) : ℂ) /
          ((Real.sqrt (absNorm n) * absNorm b : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_div, ← Complex.ofReal_mul]
    congr 1
    rw [mul_div_assoc', ← mul_div_assoc, e3]
    field_simp
  rw [div_eq_mul_inv _ ((((3 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt (absNorm n) *
      ((absNorm b : ℝ) * Real.sqrt (absNorm b)) : ℝ)) : ℂ), key]
  ring_nf

noncomputable instance : Fintype (𝓞 K)ˣ := Fintype.ofFinite _

/-- `|B_{P,j}(x)| ≤ N(P)^{1/2}` for every `j`. -/
theorem norm_Bloc_le_sqrt (P : Pr) (j : ℕ) (x : 𝓞 K) :
    ‖Bloc P.1 j x‖ ≤ Real.sqrt (absNorm P.1) := by
  have h1 : (1 : ℝ) ≤ absNorm P.1 := by exact_mod_cast one_le_absNorm_Pr P
  have hs1 : 1 ≤ Real.sqrt (absNorm P.1 : ℝ) := Real.one_le_sqrt.2 h1
  have hsinv : (Real.sqrt (absNorm P.1 : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  by_cases h4 : j % 6 = 4
  · classical
    rw [Bloc_four h4 (by linarith) x]
    by_cases hx : x ∈ P.1
    · rw [ite_eq_left hx, mul_one, show -((Real.sqrt (absNorm P.1) : ℝ) : ℂ)⁻¹ +
          ((Real.sqrt (absNorm P.1) : ℝ) : ℂ) =
          ((-(Real.sqrt (absNorm P.1))⁻¹ + Real.sqrt (absNorm P.1) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have : 0 ≤ (Real.sqrt (absNorm P.1 : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      linarith
    · rw [ite_eq_right hx, mul_zero, add_zero, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      linarith
  by_cases h0 : j % 6 = 0
  · exact (norm_Bloc_zero_le h0 x).trans (hsinv.trans hs1)
  · exact (norm_Bloc_le_one h4 h0 x).trans hs1

theorem norm_prod_Bloc_le (A : Finset Pr) (j : Pr → ℕ) (x : 𝓞 K) :
    ‖∏ P ∈ A, Bloc P.1 (j P) x‖ ≤ ∏ P ∈ A, Real.sqrt (absNorm P.1) := by
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P _ => norm_Bloc_le_sqrt P (j P) x

/-- `|A_{u,m}(𝔫, 𝔟)| ≤ K_d 3^{−4/3} ∏_{P∈𝒜} N(P)^{1/2}`, uniformly in `u, m, 𝔫, 𝔟`. -/
theorem norm_dualCoef_le {d : DualIdx → ℂ} {Kd : ℝ} (hKd : 0 ≤ Kd)
    (hd : ∀ q : DualIdx, ‖d q‖ ≤ Kd * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2))
    (A : Finset Pr) (j : Pr → ℕ) (u : (𝓞 K)ˣ) (m : ℕ) (n b : Ideal (𝓞 K)) :
    ‖dualCoef d A j u m n b‖ ≤ Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A, Real.sqrt (absNorm P.1) := by
  unfold dualCoef
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hPB := norm_prod_Bloc_le A j (dualPt (u, m, n, b))
  have hP0 : 0 ≤ ∏ P ∈ A, Real.sqrt (absNorm P.1 : ℝ) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have h3 : 0 ≤ Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) := mul_nonneg hKd (Real.rpow_nonneg (by norm_num) _)
  rcases (Real.sqrt_nonneg (absNorm b : ℝ)).eq_or_lt with hb | hb
  · rw [← hb, div_zero, abs_zero, zero_mul, zero_mul]; exact mul_nonneg h3 hP0
  · have hpos : 0 ≤ (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) hb.le
    rw [abs_of_nonneg hpos]
    have hdq := hd (u, m, n, b)
    have hR0 : 0 ≤ Kd * (3 : ℝ) ^ ((m : ℝ) / 6) * Real.sqrt (absNorm b) :=
      mul_nonneg (mul_nonneg hKd (Real.rpow_nonneg (by norm_num) _)) hb.le
    have e1 : (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) * (3 : ℝ) ^ ((m : ℝ) / 6) = (3 : ℝ) ^ (-(4 : ℝ) / 3) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    calc (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) * ‖d (u, m, n, b)‖ *
          ‖∏ P ∈ A, Bloc P.1 (j P) (dualPt (u, m, n, b))‖
        ≤ (3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) / Real.sqrt (absNorm b) *
            (Kd * (3 : ℝ) ^ ((m : ℝ) / 6) * Real.sqrt (absNorm b)) *
            ∏ P ∈ A, Real.sqrt (absNorm P.1) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdq hpos) hPB (norm_nonneg _) (mul_nonneg hpos hR0)
      _ = Kd * ((3 : ℝ) ^ (-(m : ℝ) / 6 - 4 / 3) * (3 : ℝ) ^ ((m : ℝ) / 6)) *
            (Real.sqrt (absNorm b) / Real.sqrt (absNorm b)) * ∏ P ∈ A, Real.sqrt (absNorm P.1) := by
          ring
      _ = Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A, Real.sqrt (absNorm P.1) := by
          rw [e1, div_self hb.ne', mul_one]

/-- `3^{−(m−4)/3}(3^{m−4}c)^{−3/4} = 3^{13/3}c^{−3/4}(3^{−13/12})^m`. -/
theorem three_geom (m : ℕ) {c : ℝ} (hc : 0 < c) :
    (3 : ℝ) ^ (-(((m : ℤ) - 4 : ℤ) : ℝ) / 3) * ((3 : ℝ) ^ ((m : ℤ) - 4) * c) ^ (-(3 / 4 : ℝ)) =
      (3 : ℝ) ^ ((13 : ℝ) / 3) * c ^ (-(3 / 4 : ℝ)) * ((3 : ℝ) ^ (-(13 / 12 : ℝ))) ^ m := by
  rw [Real.mul_rpow (by positivity) hc.le, three_zpow_eq, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((3 : ℝ) ^ (-(13 / 12 : ℝ))), ← Real.rpow_mul (by norm_num)]
  push_cast
  have e : (3 : ℝ) ^ (-((m : ℝ) - 4) / 3) * (3 : ℝ) ^ (((m : ℝ) - 4) * -(3 / 4 : ℝ)) =
      (3 : ℝ) ^ ((13 : ℝ) / 3) * (3 : ℝ) ^ (-(13 / 12 : ℝ) * (m : ℝ)) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; congr 1; ring
  calc (3 : ℝ) ^ (-((m : ℝ) - 4) / 3) * ((3 : ℝ) ^ (((m : ℝ) - 4) * -(3 / 4 : ℝ)) * c ^ (-(3 / 4 : ℝ)))
      = ((3 : ℝ) ^ (-((m : ℝ) - 4) / 3) * (3 : ℝ) ^ (((m : ℝ) - 4) * -(3 / 4 : ℝ))) *
          c ^ (-(3 / 4 : ℝ)) := by ring
    _ = _ := by rw [e]; ring

/-- The summand of a transformed term in prepared form, `(uλ^m/k₀)₆³` times a term of `𝒮_{m−4}`. -/
def dualSummand (h : ℝ → ℂ) (Y H₀ : ℝ) (d : DualIdx → ℂ) (A : Finset Pr) (j : Pr → ℕ) (k₀ : 𝓞 K)
    (q : DualIdx) : ℂ :=
  dualPhase q.1 q.2.1 k₀ *
    prepTerm h Y H₀ ((q.2.1 : ℤ) - 4) (dualCoef d A j q.1 q.2.1) k₀ q.2.2.1 q.2.2.2

/-- The majorant of the transformed series: `C r^m N(𝔫)^{−s₁} N(𝔟)^{−s₂}` is summable over the dual
parameters for `0 ≤ r < 1` and `s₁, s₂ > 1`. -/
theorem summable_dualMajorant {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) {s₁ s₂ : ℝ}
    (h1 : 1 < s₁) (h2 : 1 < s₂) :
    Summable fun q : DualIdx =>
      C * r ^ q.2.1 * ((absNorm q.2.2.1 : ℝ) ^ (-s₁) * (absNorm q.2.2.2 : ℝ) ^ (-s₂)) := by
  have a1 := summable_absNorm_rpow h1
  have a2 := summable_absNorm_rpow h2
  have hHn := Summable.mul_of_nonneg a1 a2 (fun _ => by positivity) fun _ => by positivity
  have hG := (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hGH := Summable.mul_of_nonneg hG hHn (fun m => mul_nonneg hC (pow_nonneg hr0 m))
    fun _ => by positivity
  have hM := Summable.mul_of_nonneg (f := fun _ : (𝓞 K)ˣ => (1 : ℝ)) Summable.of_finite hGH
    (fun _ => zero_le_one) fun x => mul_nonneg (mul_nonneg hC (pow_nonneg hr0 x.1))
      (mul_nonneg (by positivity) (by positivity))
  exact hM.congr fun q => by simp only [one_mul]

/-- **The transformed series converges absolutely.** -/
theorem summable_dualSummand {h : ℝ → ℂ} {Nw : ℝ} (hNw : 0 ≤ Nw)
    (hh : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-(1 : ℝ))) {d : DualIdx → ℂ} {Kd : ℝ}
    (hKd : 0 ≤ Kd)
    (hd : ∀ q : DualIdx, ‖d q‖ ≤ Kd * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2))
    (A : Finset Pr) (j : Pr → ℕ) {k₀ : 𝓞 K} (hk : 0 < (absNorm (span {k₀}) : ℝ)) {Y H₀ : ℝ}
    (hY : 0 < Y) (hH : 0 < H₀) : Summable (dualSummand h Y H₀ d A j k₀) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A, Real.sqrt (absNorm P.1) :=
    ⟨_, rfl⟩
  have hcoef : ∀ u m, ∀ n b, ‖dualCoef d A j u m n b‖ ≤ a := fun u m n b => by
    rw [ha]; exact norm_dualCoef_le hKd hd A j u m n b
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (hcoef 1 0 ⊥ ⊥)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = H₀ ^ 2 / (Y * (absNorm (span {k₀}) : ℝ) ^ 2) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; exact div_pos (pow_pos hH 2) (mul_pos hY (pow_pos hk 2))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (3 : ℝ) ^ (-(13 / 12 : ℝ)) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = a * Nw * ((3 : ℝ) ^ ((13 : ℝ) / 3) * c ^ (-(3 / 4 : ℝ))) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg ha0 hNw)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hc0.le _))
  have hMs := summable_dualMajorant hC0 hr0 hr1 (s₁ := 1 / 2 + 3 / 4) (s₂ := 1 + 3 * (3 / 4))
    (by norm_num) (by norm_num)
  refine Summable.of_norm_bounded hMs fun q => ?_
  have h1 := norm_dualPhase_le q.1 q.2.1 k₀
  have h2 := norm_prepTerm_le hNw (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) hh
    hY hH ((q.2.1 : ℤ) - 4) (hcoef q.1 q.2.1) hk q.2.2.1 q.2.2.2
  have e : (3 : ℝ) ^ ((q.2.1 : ℤ) - 4) * H₀ ^ 2 / (Y * (absNorm (span {k₀}) : ℝ) ^ 2) =
      (3 : ℝ) ^ ((q.2.1 : ℤ) - 4) * c := by rw [hcdef, mul_div_assoc]
  rw [e] at h2
  have hgeom := three_geom q.2.1 hc0
  unfold dualSummand
  rw [norm_mul]
  calc ‖dualPhase q.1 q.2.1 k₀‖ *
        ‖prepTerm h Y H₀ ((q.2.1 : ℤ) - 4) (dualCoef d A j q.1 q.2.1) k₀ q.2.2.1 q.2.2.2‖
      ≤ 1 * ((3 : ℝ) ^ (-(((q.2.1 : ℤ) - 4 : ℤ) : ℝ) / 3) * a * Nw *
          ((3 : ℝ) ^ ((q.2.1 : ℤ) - 4) * c) ^ (-(3 / 4 : ℝ)) *
          ((absNorm q.2.2.1 : ℝ) ^ (-(1 / 2 + 3 / 4 : ℝ)) *
            (absNorm q.2.2.2 : ℝ) ^ (-(1 + 3 * (3 / 4) : ℝ)))) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = C * r ^ q.2.1 * ((absNorm q.2.2.1 : ℝ) ^ (-(1 / 2 + 3 / 4 : ℝ)) *
            (absNorm q.2.2.2 : ℝ) ^ (-(1 + 3 * (3 / 4) : ℝ))) := by
        rw [hC, hr]
        calc 1 * ((3 : ℝ) ^ (-(((q.2.1 : ℤ) - 4 : ℤ) : ℝ) / 3) * a * Nw *
              ((3 : ℝ) ^ ((q.2.1 : ℤ) - 4) * c) ^ (-(3 / 4 : ℝ)) *
              ((absNorm q.2.2.1 : ℝ) ^ (-(1 / 2 + 3 / 4 : ℝ)) *
                (absNorm q.2.2.2 : ℝ) ^ (-(1 + 3 * (3 / 4) : ℝ))))
            = 1 * (a * Nw * ((3 : ℝ) ^ (-(((q.2.1 : ℤ) - 4 : ℤ) : ℝ) / 3) *
                ((3 : ℝ) ^ ((q.2.1 : ℤ) - 4) * c) ^ (-(3 / 4 : ℝ))) *
              ((absNorm q.2.2.1 : ℝ) ^ (-(1 / 2 + 3 / 4 : ℝ)) *
                (absNorm q.2.2.2 : ℝ) ^ (-(1 + 3 * (3 / 4) : ℝ)))) := by ring
          _ = _ := by rw [hgeom]; ring

/-- **A transformed term regrouped**: summing its series first over `(𝔫, 𝔟)`, then over `m`, then over
the units gives `Σ_u Σ_{m ≥ 0} (uλ^m/k₀)₆³ 𝒮_{m−4}[A_{u,m}, Y](k₀)` with `Y = N(c₀)²N(𝒜)²H₀²/X`. -/
theorem dualTerm_eq_sum {h : ℝ → ℂ} {Nw : ℝ} (hNw : 0 ≤ Nw)
    (hh : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-(1 : ℝ))) {d : DualIdx → ℂ} {Kd : ℝ}
    (hKd : 0 ≤ Kd)
    (hd : ∀ q : DualIdx, ‖d q‖ ≤ Kd * (3 : ℝ) ^ ((q.2.1 : ℝ) / 6) * Real.sqrt (absNorm q.2.2.2))
    {c₀ : 𝓞 K} (hc₀ : c₀ ≠ 0) (A : Finset Pr) (j : Pr → ℕ) {k₀ : 𝓞 K}
    (h6 : (absNorm (span {k₀})).Coprime 6) (hsq : Squarefree (span {k₀})) {H₀ X : ℝ}
    (hH : 0 < H₀) (hX : 0 < X) :
    (∀ u : (𝓞 K)ˣ, Summable fun m : ℕ => dualPhase u m k₀ *
        prepSum h (dualY c₀ A H₀ X) H₀ ((m : ℤ) - 4) (dualCoef d A j u m) k₀) ∧
    dualTerm h d c₀ A j k₀ X = ∑ u : (𝓞 K)ˣ, ∑' m : ℕ, dualPhase u m k₀ *
        prepSum h (dualY c₀ A H₀ X) H₀ ((m : ℤ) - 4) (dualCoef d A j u m) k₀ := by
  have hk : 0 < (absNorm (span {k₀}) : ℝ) := absNorm_pos_of_coprime6 h6
  have hc : 0 < (absNorm (span {c₀}) : ℝ) := by
    have : absNorm (span {c₀}) ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc₀
    exact_mod_cast Nat.pos_of_ne_zero this
  have hY : 0 < dualY c₀ A H₀ X := by
    unfold dualY
    exact div_pos (mul_pos (mul_pos (pow_pos hc 2) (pow_pos (nI_pos A) 2)) (pow_pos hH 2)) hX
  have hcoef : ∀ u m, ∀ n b, ‖dualCoef d A j u m n b‖ ≤
      Kd * (3 : ℝ) ^ (-(4 : ℝ) / 3) * ∏ P ∈ A, Real.sqrt (absNorm P.1) :=
    fun u m n b => norm_dualCoef_le hKd hd A j u m n b
  have hFs := summable_dualSummand hNw hh hKd hd A j hk hY hH
  have hfib : ∀ u : (𝓞 K)ˣ, HasSum (fun m : ℕ => dualPhase u m k₀ *
      prepSum h (dualY c₀ A H₀ X) H₀ ((m : ℤ) - 4) (dualCoef d A j u m) k₀)
      (∑' p, dualSummand h (dualY c₀ A H₀ X) H₀ d A j k₀ (u, p)) := by
    intro u
    refine (hFs.prod_factor u).hasSum.prod_fiberwise fun m => ?_
    have hs := (summable_prepTerm hNw (by norm_num : (1 / 2 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) ≤ 1) hh hY hH ((m : ℤ) - 4) (hcoef u m) hk).of_norm
    exact hs.hasSum.mul_left (dualPhase u m k₀)
  refine ⟨fun u => (hfib u).summable, ?_⟩
  have htot : HasSum (fun u : (𝓞 K)ˣ => ∑' p, dualSummand h (dualY c₀ A H₀ X) H₀ d A j k₀ (u, p))
      (∑' q, dualSummand h (dualY c₀ A H₀ X) H₀ d A j k₀ q) :=
    hFs.hasSum.prod_fiberwise fun u => (hFs.prod_factor u).hasSum
  have hdual : dualTerm h d c₀ A j k₀ X = ∑' q, dualSummand h (dualY c₀ A H₀ X) H₀ d A j k₀ q := by
    unfold dualTerm
    exact tsum_congr fun q => dualTerm_summand_eq h d hc₀ A j h6 hsq hH hX q
  rw [hdual, htot.unique (hasSum_fintype _)]
  exact Finset.sum_congr rfl fun u _ => ((hfib u).tsum_eq).symm

/-- `N(P)^{1/2}` as a complex number. -/
abbrev rtN (P : Pr) : ℂ := ((Real.sqrt (absNorm P.1) : ℝ) : ℂ)

open Classical in
/-- `B_{P,4}` in the parameters `(𝔫, 𝔟)`: `−N(P)^{−1/2} + N(P)^{1/2}·1_{P ∣ 𝔫 or P ∣ 𝔟}`. -/
def B4 (P : Pr) (n b : Ideal (𝓞 K)) : ℂ :=
  -(rtN P)⁻¹ + rtN P * (if P.1 ∣ n ∨ P.1 ∣ b then 1 else 0)

theorem absNorm_Pr_pos (P : Pr) : (0 : ℝ) < absNorm P.1 := by
  exact_mod_cast lt_of_lt_of_le zero_lt_one (one_le_absNorm_Pr P)

/-- At `j_P ≡ 4`, `B_{P,j_P}(uλ^m n b³) = B4 P 𝔫 𝔟`. -/
theorem Bloc_dualPt_four (P : Pr) {j : ℕ} (h4 : j % 6 = 4) {q : DualIdx}
    (hn : (absNorm q.2.2.1).Coprime 3) (hb : (absNorm q.2.2.2).Coprime 3) :
    Bloc P.1 j (dualPt q) = B4 P q.2.2.1 q.2.2.2 := by
  classical
  rw [Bloc_four h4 (absNorm_Pr_pos P) (dualPt q)]
  unfold B4
  have hiff := dualPt_mem_iff P hn hb
  by_cases hx : dualPt q ∈ P.1
  · rw [ite_eq_left hx, ite_eq_left (hiff.1 hx)]
  · rw [ite_eq_right hx, ite_eq_right fun h => hx (hiff.2 h)]

open Classical in
/-- **The expansion of `∏_{P∈Q} B_{P,4}`**: a sum over `T₁ ⊆ T ⊆ Q` of
`(∏_{Q∖T} −N(P)^{−1/2})(∏_T N(P)^{1/2})·∏_{T₁} 1_{P∣𝔫}·∏_{T∖T₁} 1_{P∤𝔫, P∣𝔟}`. -/
theorem prod_B4_eq (Q : Finset Pr) (n b : Ideal (𝓞 K)) :
    ∏ P ∈ Q, B4 P n b = ∑ T ∈ Q.powerset, ∑ T₁ ∈ T.powerset,
      (∏ P ∈ Q \ T, -(rtN P)⁻¹) * (∏ P ∈ T, rtN P) *
        ((∏ P ∈ T₁, if P.1 ∣ n then (1 : ℂ) else 0) *
          ∏ P ∈ T \ T₁, if P.1 ∣ n then (0 : ℂ) else if P.1 ∣ b then 1 else 0) := by
  have e1 : ∀ P ∈ Q, B4 P n b = rtN P * ((if P.1 ∣ n then (1 : ℂ) else 0) +
      (if P.1 ∣ n then (0 : ℂ) else if P.1 ∣ b then 1 else 0)) + -(rtN P)⁻¹ := by
    intro P _
    unfold B4
    by_cases h1 : P.1 ∣ n
    · rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_left h1]; ring
    · by_cases h2 : P.1 ∣ b
      · rw [ite_eq_left (Or.inr h2), ite_eq_right h1, ite_eq_right h1, ite_eq_left h2]; ring
      · rw [ite_eq_right (by tauto), ite_eq_right h1, ite_eq_right h1, ite_eq_right h2]; ring
  rw [Finset.prod_congr rfl e1, Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_add, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T₁ _ => ?_
  ring

/-- The prepared term is linear in its coefficient. -/
theorem prepTerm_mul_coef (h : ℝ → ℂ) (Y H₀ : ℝ) (m : ℤ) (A E : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : 𝓞 K) (n b : Ideal (𝓞 K)) :
    prepTerm h Y H₀ m (fun n b => A n b * E n b) k n b = E n b * prepTerm h Y H₀ m A k n b := by
  unfold prepTerm; ring

theorem absNorm_pos_of_coprime3 {I : Ideal (𝓞 K)} (h : (absNorm I).Coprime 3) :
    (0 : ℝ) < absNorm I := by
  have : absNorm I ≠ 0 := by
    intro h0; rw [h0] at h; norm_num at h
  exact_mod_cast Nat.pos_of_ne_zero this

/-- **Reindexing a prepared term**: at `(𝔯₁𝔫, 𝔯₂𝔟)` the term is `(𝔯₁𝔯₂/k)₆³` times the term at
`(𝔫, 𝔟)` of the scale `Y/(N𝔯₁ N𝔯₂³)` and the coefficient `A(𝔯₁𝔫, 𝔯₂𝔟)/(N𝔯₁^{1/2} N𝔯₂)`. -/
theorem prepTerm_reindex (h : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (H₀ : ℝ) (m : ℤ)
    (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) {k : 𝓞 K} (hk : 0 < (absNorm (span {k}) : ℝ))
    {r₁ r₂ : Ideal (𝓞 K)} (hr₁ : (absNorm r₁).Coprime 3) (hr₂ : (absNorm r₂).Coprime 3)
    (n b : Ideal (𝓞 K))
    (hA : A (r₁ * n) (r₂ * b) ≠ 0 → (absNorm (r₁ * n)).Coprime 3 ∧ (absNorm (r₂ * b)).Coprime 3) :
    prepTerm h Y H₀ m A k (r₁ * n) (r₂ * b) =
      sym6 (pgen r₁ * pgen r₂) (span {k}) ^ 3 *
        prepTerm h (Y / ((absNorm r₁ : ℝ) * (absNorm r₂ : ℝ) ^ 3)) H₀ m
          (fun n b => A (r₁ * n) (r₂ * b) / ((Real.sqrt (absNorm r₁) * absNorm r₂ : ℝ) : ℂ)) k n b := by
  by_cases h0 : A (r₁ * n) (r₂ * b) = 0
  · unfold prepTerm; simp [h0]
  obtain ⟨h1, h2⟩ := hA h0
  rw [map_mul] at h1 h2
  have hn3 : (absNorm n).Coprime 3 := Nat.Coprime.coprime_mul_left h1
  have hb3 : (absNorm b).Coprime 3 := Nat.Coprime.coprime_mul_left h2
  have hr₁0 := absNorm_pos_of_coprime3 hr₁
  have hr₂0 := absNorm_pos_of_coprime3 hr₂
  have hn0 := absNorm_pos_of_coprime3 hn3
  have hb0 := absNorm_pos_of_coprime3 hb3
  unfold prepTerm
  rw [pgen_mul3 hr₁ hn3, pgen_mul3 hr₂ hb3,
    show pgen r₁ * pgen n * (pgen r₂ * pgen b) = (pgen r₁ * pgen r₂) * (pgen n * pgen b) by ring,
    sym6_mul_left, map_mul, map_mul]
  have harg : (3 : ℝ) ^ m * ((absNorm r₁ * absNorm n : ℕ) : ℝ) * ((absNorm r₂ * absNorm b : ℕ) : ℝ) ^ 3 *
      H₀ ^ 2 / (Y * (absNorm (span {k}) : ℝ) ^ 2) =
      (3 : ℝ) ^ m * absNorm n * (absNorm b : ℝ) ^ 3 * H₀ ^ 2 /
        (Y / ((absNorm r₁ : ℝ) * (absNorm r₂ : ℝ) ^ 3) * (absNorm (span {k}) : ℝ) ^ 2) := by
    push_cast; field_simp
  rw [harg]
  have hs : Real.sqrt ((absNorm r₁ * absNorm n : ℕ) : ℝ) =
      Real.sqrt (absNorm r₁) * Real.sqrt (absNorm n) := by
    push_cast; exact Real.sqrt_mul hr₁0.le _
  rw [hs]
  have hs1 : 0 < Real.sqrt (absNorm r₁ : ℝ) := Real.sqrt_pos.2 hr₁0
  have hs2 : 0 < Real.sqrt (absNorm n : ℝ) := Real.sqrt_pos.2 hn0
  push_cast
  field_simp

open Classical in
/-- The coefficient of the piece `(T, T₁)` after reindexing `𝔫 = 𝔯₁𝔫′`, `𝔟 = 𝔯₂𝔟′`,
`𝔯₁ = ∏_{T₁} P`, `𝔯₂ = ∏_{T∖T₁} P`. -/
def reCoef (A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (Q T T₁ : Finset Pr) (n b : Ideal (𝓞 K)) : ℂ :=
  (∏ P ∈ Q \ T, -(rtN P)⁻¹) * (∏ P ∈ T, rtN P) * (∏ P ∈ T \ T₁, if P.1 ∣ n then (0 : ℂ) else 1) *
    (A (idl T₁ * n) (idl (T \ T₁) * b) /
      ((Real.sqrt (absNorm (idl T₁)) * absNorm (idl (T \ T₁)) : ℝ) : ℂ))

theorem coprime3_idl (T : Finset Pr) : (absNorm (idl T)).Coprime 3 :=
  Nat.Coprime.coprime_dvd_right (by norm_num) (idl_coprime6 T)

theorem sqrt_absNorm_idl (T : Finset Pr) :
    Real.sqrt (absNorm (idl T) : ℝ) = ∏ P ∈ T, Real.sqrt (absNorm P.1 : ℝ) := by
  rw [absNorm_idl, Nat.cast_prod, Real.sqrt_prod _ fun _ _ => Nat.cast_nonneg _]

open Classical in
/-- `|reCoef| ≤ a ∏_{Q∖T} N(P)^{−1/2} · N(𝔯₂)^{−1/2}`. -/
theorem norm_reCoef_le {A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} {a : ℝ} (ha : ∀ n b, ‖A n b‖ ≤ a)
    {Q T T₁ : Finset Pr} (hT₁ : T₁ ⊆ T) (n b : Ideal (𝓞 K)) :
    ‖reCoef A Q T T₁ n b‖ ≤
      a * (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) * (Real.sqrt (absNorm (idl (T \ T₁))))⁻¹ := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha ⊥ ⊥)
  have h1 : ‖∏ P ∈ Q \ T, -(rtN P)⁻¹‖ = ∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : ‖∏ P ∈ T, rtN P‖ = Real.sqrt (absNorm (idl T₁)) * Real.sqrt (absNorm (idl (T \ T₁))) := by
    rw [norm_prod, sqrt_absNorm_idl, sqrt_absNorm_idl, ← Finset.prod_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hT₁]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h3 : ‖∏ P ∈ T \ T₁, (if P.1 ∣ n then (0 : ℂ) else 1)‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun P _ => ?_
    split_ifs <;> simp
  have hr₁ := absNorm_pos_of_coprime3 (coprime3_idl T₁)
  have hr₂ := absNorm_pos_of_coprime3 (coprime3_idl (T \ T₁))
  have hs1 : 0 < Real.sqrt (absNorm (idl T₁) : ℝ) := Real.sqrt_pos.2 hr₁
  have hs2 : 0 < Real.sqrt (absNorm (idl (T \ T₁)) : ℝ) := Real.sqrt_pos.2 hr₂
  have hP0 : 0 ≤ ∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹ :=
    Finset.prod_nonneg fun _ _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  unfold reCoef
  rw [norm_mul, norm_mul, norm_mul, h1, h2, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have hsq2 : (absNorm (idl (T \ T₁)) : ℝ) = Real.sqrt (absNorm (idl (T \ T₁))) ^ 2 :=
    (Real.sq_sqrt hr₂.le).symm
  calc (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
        (Real.sqrt (absNorm (idl T₁)) * Real.sqrt (absNorm (idl (T \ T₁)))) *
        ‖∏ P ∈ T \ T₁, (if P.1 ∣ n then (0 : ℂ) else 1)‖ *
        (‖A (idl T₁ * n) (idl (T \ T₁) * b)‖ /
          (Real.sqrt (absNorm (idl T₁)) * absNorm (idl (T \ T₁))))
      ≤ (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
        (Real.sqrt (absNorm (idl T₁)) * Real.sqrt (absNorm (idl (T \ T₁)))) * 1 *
        (a / (Real.sqrt (absNorm (idl T₁)) * absNorm (idl (T \ T₁)))) := by
        have hD : 0 < Real.sqrt (absNorm (idl T₁) : ℝ) * absNorm (idl (T \ T₁)) := mul_pos hs1 hr₂
        have hX : 0 ≤ (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
            (Real.sqrt (absNorm (idl T₁)) * Real.sqrt (absNorm (idl (T \ T₁)))) :=
          mul_nonneg hP0 (mul_nonneg hs1.le hs2.le)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hX)
          (div_le_div_of_nonneg_right (ha _ _) hD.le) (div_nonneg (norm_nonneg _) hD.le)
          (mul_nonneg hX zero_le_one)
    _ = a * (∏ P ∈ Q \ T, (Real.sqrt (absNorm P.1 : ℝ))⁻¹) *
          (Real.sqrt (absNorm (idl (T \ T₁))))⁻¹ := by
        rw [hsq2]; field_simp; rw [Real.sqrt_sq hs2.le]

/-- The support of `reCoef` is that of `A` moved by `𝔫 ↦ 𝔯₁𝔫`. -/
theorem reCoef_support {A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}
    (hA : ∀ n b, A n b ≠ 0 → Squarefree n ∧ (absNorm n).Coprime 3) {Q T T₁ : Finset Pr}
    {n b : Ideal (𝓞 K)} (h : reCoef A Q T T₁ n b ≠ 0) : Squarefree n ∧ (absNorm n).Coprime 3 := by
  have hA0 : A (idl T₁ * n) (idl (T \ T₁) * b) ≠ 0 := by
    intro h0; apply h; unfold reCoef; rw [h0]; simp
  obtain ⟨hs, hc⟩ := hA _ _ hA0
  rw [map_mul] at hc
  exact ⟨Squarefree.of_mul_right hs, Nat.Coprime.coprime_mul_left hc⟩

open Classical in
/-- The indicator of the piece `(T, T₁)`: `∏_{T₁} 1_{P∣𝔫} · ∏_{T∖T₁} 1_{P∤𝔫, P∣𝔟}`. -/
def pieceInd (T T₁ : Finset Pr) (n b : Ideal (𝓞 K)) : ℂ :=
  (∏ P ∈ T₁, if P.1 ∣ n then (1 : ℂ) else 0) *
    ∏ P ∈ T \ T₁, if P.1 ∣ n then (0 : ℂ) else if P.1 ∣ b then 1 else 0

open Classical in
theorem pieceInd_reindex {T T₁ : Finset Pr} (n b : Ideal (𝓞 K)) :
    pieceInd T T₁ (idl T₁ * n) (idl (T \ T₁) * b) =
      ∏ P ∈ T \ T₁, if P.1 ∣ n then (0 : ℂ) else 1 := by
  unfold pieceInd
  have e1 : ∏ P ∈ T₁, (if P.1 ∣ idl T₁ * n then (1 : ℂ) else 0) = 1 :=
    Finset.prod_eq_one fun P hP =>
      ite_eq_left (dvd_mul_of_dvd_left ((dvd_idl_iff P T₁).2 hP) n)
  rw [e1, one_mul]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hPT₁ : P ∉ T₁ := (Finset.mem_sdiff.1 hP).2
  have hiff : P.1 ∣ idl T₁ * n ↔ P.1 ∣ n := by
    constructor
    · intro h
      rcases (prime_Pr P).dvd_or_dvd h with h' | h'
      · exact absurd ((dvd_idl_iff P T₁).1 h') hPT₁
      · exact h'
    · exact fun h => dvd_mul_of_dvd_right h _
  have hb : P.1 ∣ idl (T \ T₁) * b := dvd_mul_of_dvd_left ((dvd_idl_iff P _).2 hP) b
  by_cases hn : P.1 ∣ n
  · rw [ite_eq_left (hiff.2 hn), ite_eq_left hn]
  · rw [ite_eq_right fun h => hn (hiff.1 h), ite_eq_left hb, ite_eq_right hn]

/-- A nonzero piece lives on `𝔯₁ ∣ 𝔫` and `𝔯₂ ∣ 𝔟`. -/
theorem dvd_of_pieceInd_ne_zero {T T₁ : Finset Pr} {n b : Ideal (𝓞 K)}
    (h : pieceInd T T₁ n b ≠ 0) : idl T₁ ∣ n ∧ idl (T \ T₁) ∣ b := by
  classical
  unfold pieceInd at h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  constructor
  · refine (prod_Pr_dvd_iff T₁ n).2 fun P hP => ?_
    have := Finset.prod_ne_zero_iff.1 h1 P hP
    by_contra hc
    exact this (ite_eq_right hc)
  · refine (prod_Pr_dvd_iff _ b).2 fun P hP => ?_
    have := Finset.prod_ne_zero_iff.1 h2 P hP
    by_contra hc
    apply this
    by_cases hn : P.1 ∣ n
    · exact ite_eq_left hn
    · rw [ite_eq_right hn, ite_eq_right hc]

/-- **The prepared sum with the factors `B_{P,4}` (`P ∈ Q`), reindexed** (the companion paper's
identity after its (6.18), at every `P ∈ Q` at once): the sum over `T₁ ⊆ T ⊆ Q` of
`(𝔯₁𝔯₂/k)₆³ 𝒮_m[reCoef, Y/(N𝔯₁ N𝔯₂³)](k)` with `𝔯₁ = ∏_{T₁} P`, `𝔯₂ = ∏_{T∖T₁} P`. -/
theorem prepSum_B4 {h : ℝ → ℂ} {Nw A' θ : ℝ} (hNw : 0 ≤ Nw) (hθ : 1 / 2 < θ) (hθA : θ ≤ A')
    (hh : ∀ w, ‖h w‖ ≤ Nw * (1 + Real.exp w) ^ (-A')) {Y H₀ : ℝ} (hY : 0 < Y) (hH : 0 < H₀)
    (m : ℤ) {A : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} {a : ℝ} (ha : ∀ n b, ‖A n b‖ ≤ a)
    (hA3 : ∀ n b, A n b ≠ 0 → (absNorm n).Coprime 3 ∧ (absNorm b).Coprime 3)
    {k : 𝓞 K} (hk : 0 < (absNorm (span {k}) : ℝ)) (Q : Finset Pr) :
    prepSum h Y H₀ m (fun n b => A n b * ∏ P ∈ Q, B4 P n b) k =
      ∑ T ∈ Q.powerset, ∑ T₁ ∈ T.powerset,
        sym6 (pgen (idl T₁) * pgen (idl (T \ T₁))) (span {k}) ^ 3 *
          prepSum h (Y / ((absNorm (idl T₁) : ℝ) * (absNorm (idl (T \ T₁)) : ℝ) ^ 3)) H₀ m
            (reCoef A Q T T₁) k := by
  have hpiece : ∀ T ∈ Q.powerset, ∀ T₁ ∈ T.powerset,
      HasSum (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) =>
        (∏ P ∈ Q \ T, -(rtN P)⁻¹) * (∏ P ∈ T, rtN P) * pieceInd T T₁ p.1 p.2 *
          prepTerm h Y H₀ m A k p.1 p.2)
      (sym6 (pgen (idl T₁) * pgen (idl (T \ T₁))) (span {k}) ^ 3 *
          prepSum h (Y / ((absNorm (idl T₁) : ℝ) * (absNorm (idl (T \ T₁)) : ℝ) ^ 3)) H₀ m
            (reCoef A Q T T₁) k) := by
    intro T _ T₁ hT₁
    unfold prepSum
    have hT₁' : T₁ ⊆ T := Finset.mem_powerset.1 hT₁
    have hY' : 0 < Y / ((absNorm (idl T₁) : ℝ) * (absNorm (idl (T \ T₁)) : ℝ) ^ 3) :=
      div_pos hY (mul_pos (absNorm_pos_of_coprime3 (coprime3_idl _))
        (pow_pos (absNorm_pos_of_coprime3 (coprime3_idl _)) 3))
    have hs := (summable_prepTerm hNw hθ hθA hh hY' hH m (norm_reCoef_le (Q := Q) ha hT₁') hk).of_norm
    have hsum := hs.hasSum.mul_left (sym6 (pgen (idl T₁) * pgen (idl (T \ T₁))) (span {k}) ^ 3)
    have hinj : Function.Injective fun p : Ideal (𝓞 K) × Ideal (𝓞 K) =>
        (idl T₁ * p.1, idl (T \ T₁) * p.2) := by
      intro p p' hp
      simp only [Prod.mk.injEq] at hp
      exact Prod.ext (mul_left_cancel₀ (idl_ne_bot T₁) hp.1) (mul_left_cancel₀ (idl_ne_bot _) hp.2)
    refine (hinj.hasSum_iff fun x hx => ?_).1 ?_
    · by_contra hne
      have hind : pieceInd T T₁ x.1 x.2 ≠ 0 := fun h0 => hne (by rw [h0]; ring)
      obtain ⟨⟨n', hn'⟩, ⟨b', hb'⟩⟩ := dvd_of_pieceInd_ne_zero hind
      exact hx ⟨(n', b'), Prod.ext hn'.symm hb'.symm⟩
    · convert hsum using 1
      funext p
      simp only [Function.comp_apply]
      rw [pieceInd_reindex, prepTerm_reindex h hY H₀ m A hk (coprime3_idl _) (coprime3_idl _)
        p.1 p.2 (hA3 _ _)]
      unfold prepTerm reCoef
      ring
  have htot := hasSum_sum fun T hT => hasSum_sum fun T₁ hT₁ => hpiece T hT T₁ hT₁
  rw [prepSum]
  refine HasSum.tsum_eq ?_
  convert htot using 1
  funext p
  rw [prepTerm_mul_coef, prod_B4_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun T₁ _ => ?_
  unfold pieceInd
  ring

end Eis

end

#print axioms Eis.Bloc_four
#print axioms Eis.Bloc_one
#print axioms Eis.dualPt_mem_iff
#print axioms Eis.prod_Bloc_one
#print axioms Eis.sym6_dualPt
#print axioms Eis.dualTerm_summand_eq
#print axioms Eis.summable_dualSummand
#print axioms Eis.dualTerm_eq_sum
#print axioms Eis.prod_B4_eq
#print axioms Eis.prepTerm_reindex
#print axioms Eis.prepSum_B4
