import EisensteinQuadSieveMain

/-! # The quadratic large sieve, part 7a: the surviving main term over disjoint pairs (round 355)

S5e of round 312's plan, the first piece of S5e-7: round 354's surviving main term, summed over
the disjoint pairs of columns with arbitrary coefficients, is bounded by the bilinear bound of
round 350 with rows weighted by `N(d)^{−1/2}`.

* **Weighted rows in dyadic pieces** (`fBound_wR`, with `wR`, `FBound.of_le`, `FBound.sum`): if
  every squarefree-row weight `sqfW Y` has `FBound` constant `F(Y)`, then the weight `N(d)^{−1/2}`
  on the squarefree rows with `Y₁ < N(d) ≤ Y₂ ≤ 2^J·Y₁` has constant
  `Σ_{j<J}(2^jY₁)^{−1/2}·F(2^{j+1}Y₁)`.
* **The main term expanded** (`phiS_pairMain`, with `phiS`, `pairMain`, `cU`, `FD_union`): for
  `D = B₁ ⊔ B₂`, `φ*(D)·pairMain(G, D)` is a sum over `T, U ⊆ G` of
  `(−1)^{|T|}(N(T)N(U))^{−1/2}·Σ_d c_U(d)·(φ*(B₁)ρ_{B₁}(π_Tπ_U))(φ*(B₂)ρ_{B₂}(π_Tπ_U))·ρ_{B₁}(d)ρ_{B₂}(d)`,
  with `c_U(d) = N(d)^{−1/2}` on the squarefree rows prime to `G` with `K₁ < N(U)N(d)`,
  `N(d) ≤ K`.
* **The bilinear bound** (`main_bilin`, with `norm_cU_le`, `summable_cU`): with
  `FBound (wR (K₁/N(G)) K) X Δ`, for column sets of norm at most `X` and any coefficients,
  `|Σ_{B₁,B₂ disjoint} a(B₁)b(B₂)φ*(B₁ ∪ B₂)·pairMain(G, B₁ ∪ B₂)|
    ≤ 4^{|G|}·Δ·√(Σ_B 2^{|B|}|a(B)|²)·√(Σ_B 2^{|B|}|b(B)|²)`.
-/

open Complex NumberField Ideal
open scoped Classical

noncomputable section

namespace Eis

/-- The squarefree rows with `Y₁ < N(d) ≤ Y₂`, weighted by `N(d)^{−1/2}`. -/
def wR (Y₁ Y₂ : ℝ) (d : 𝓞 K) : ℝ :=
  if Squarefree (span {d}) ∧ Y₁ < (absNorm (span {d}) : ℝ) ∧ (absNorm (span {d}) : ℝ) ≤ Y₂ then
    (Real.sqrt (absNorm (span {d}) : ℝ))⁻¹ else 0

theorem wR_nonneg (Y₁ Y₂ : ℝ) (d : 𝓞 K) : 0 ≤ wR Y₁ Y₂ d := by
  unfold wR; split_ifs
  · exact inv_nonneg.2 (Real.sqrt_nonneg _)
  · exact le_rfl

theorem summable_wR (Y₁ Y₂ : ℝ) : Summable (wR Y₁ Y₂) := by
  refine summable_of_ne_finset_zero (s := eltsLe Y₂) fun d hd => ?_
  unfold wR
  rw [mem_eltsLe] at hd
  exact ite_eq_right fun h => hd h.2.2

/-- **A smaller weight**: `0 ≤ w ≤ w'` with `w'` summable carries `FBound w' X Δ` to `w`. -/
theorem FBound.of_le {w w' : 𝓞 K → ℝ} {X Δ : ℝ} (h0 : ∀ m, 0 ≤ w m) (hle : ∀ m, w m ≤ w' m)
    (hs : Summable w') (h : FBound w' X Δ) : FBound w X Δ := by
  have hz : FBound (fun _ : 𝓞 K => (0 : ℝ)) X 0 := fun 𝒩 α _ => by simp
  have := FBound.of_le_add h0 (fun m => by simpa using hle m) hs summable_zero h hz
  simpa using this

/-- **Weights add over a finite family**. -/
theorem FBound.sum {ι : Type*} (s : Finset ι) {w : ι → 𝓞 K → ℝ} {Δ : ι → ℝ} {X : ℝ}
    (h0 : ∀ i ∈ s, ∀ m, 0 ≤ w i m) (hs : ∀ i ∈ s, Summable (w i))
    (h : ∀ i ∈ s, FBound (w i) X (Δ i)) :
    FBound (fun m => ∑ i ∈ s, w i m) X (∑ i ∈ s, Δ i) := by
  induction s using Finset.induction_on with
  | empty => exact fun 𝒩 α _ => by simp
  | insert i s his ih =>
    have h0' : ∀ j ∈ s, ∀ m, 0 ≤ w j m := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have hs' : ∀ j ∈ s, Summable (w j) := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have h' : ∀ j ∈ s, FBound (w j) X (Δ j) := fun j hj => h j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert his]
    exact FBound.of_le_add
      (fun m => add_nonneg (h0 i (Finset.mem_insert_self i s) m)
        (Finset.sum_nonneg fun j hj => h0' j hj m))
      (fun m => le_rfl) (hs i (Finset.mem_insert_self i s)) (summable_sum fun j hj => hs' j hj)
      (h i (Finset.mem_insert_self i s)) (ih h0' hs' h')

/-- **Rows weighted by `N(d)^{−1/2}`, in dyadic pieces**: if `FBound (sqfW Y) X (F(Y))` for every
`Y` and `Y₂ ≤ 2^J·Y₁` with `Y₁ > 0`, then the weight `N(d)^{−1/2}` on the squarefree rows with
`Y₁ < N(d) ≤ Y₂` has `FBound` constant `Σ_{j<J}(2^jY₁)^{−1/2}·F(2^{j+1}Y₁)`. -/
theorem fBound_wR {Y₁ Y₂ X : ℝ} (hY : 0 < Y₁) (J : ℕ) (hJ : Y₂ ≤ 2 ^ J * Y₁) (Fn : ℝ → ℝ)
    (hF : ∀ Y, FBound (sqfW Y) X (Fn Y)) :
    FBound (wR Y₁ Y₂) X
      (∑ j ∈ Finset.range J, (Real.sqrt (2 ^ j * Y₁))⁻¹ * Fn (2 ^ (j + 1) * Y₁)) := by
  set w : ℕ → 𝓞 K → ℝ := fun j m => (Real.sqrt (2 ^ j * Y₁))⁻¹ * sqfW (2 ^ (j + 1) * Y₁) m
    with hw
  have hw0 : ∀ j ∈ Finset.range J, ∀ m, 0 ≤ w j m := fun j _ m =>
    mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (sqfW_nonneg _ _)
  have hws : ∀ j ∈ Finset.range J, Summable (w j) := fun j _ =>
    (summable_sqfW _).mul_left _
  have hwF : ∀ j ∈ Finset.range J, FBound (w j) X
      ((Real.sqrt (2 ^ j * Y₁))⁻¹ * Fn (2 ^ (j + 1) * Y₁)) := fun j _ =>
    (hF _).const_mul (inv_nonneg.2 (Real.sqrt_nonneg _))
  refine FBound.of_le (wR_nonneg Y₁ Y₂) (fun d => ?_) (summable_sum hws)
    (FBound.sum _ hw0 hws hwF)
  -- the dyadic piece containing `N(d)`
  unfold wR
  split_ifs with hd
  · obtain ⟨hsq, h1, h2⟩ := hd
    set n : ℝ := (absNorm (span {d}) : ℝ) with hn
    have hex : ∃ j : ℕ, n ≤ 2 ^ (j + 1) * Y₁ := by
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (n / Y₁) (by norm_num : (1 : ℝ) < 2)
      refine ⟨j, ?_⟩
      rw [div_lt_iff₀ hY] at hj
      have : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
      nlinarith
    set j₀ := Nat.find hex with hj₀
    have hj₀s : n ≤ 2 ^ (j₀ + 1) * Y₁ := Nat.find_spec hex
    have hj₀l : 2 ^ j₀ * Y₁ < n := by
      rcases Nat.eq_zero_or_pos j₀ with h | h
      · rw [h, pow_zero, one_mul]; exact h1
      · have := Nat.find_min hex (Nat.sub_lt h one_pos)
        rw [← hj₀, Nat.sub_add_cancel (show 1 ≤ j₀ from h)] at this
        exact not_le.1 this
    have hJpos : j₀ < J := by
      by_contra hc
      push Not at hc
      have : (2 : ℝ) ^ J ≤ 2 ^ j₀ := pow_le_pow_right₀ (by norm_num) hc
      nlinarith
    have hterm : (Real.sqrt n)⁻¹ ≤ w j₀ d := by
      simp only [hw, sqfW]
      rw [ite_eq_left ⟨hsq, hj₀s⟩, mul_one]
      have hp : 0 < 2 ^ j₀ * Y₁ := by positivity
      exact inv_anti₀ (Real.sqrt_pos.2 hp) (Real.sqrt_le_sqrt hj₀l.le)
    calc (Real.sqrt n)⁻¹ ≤ w j₀ d := hterm
      _ ≤ ∑ j ∈ Finset.range J, w j d :=
        Finset.single_le_sum (f := fun j => w j d) (fun j hj => hw0 j hj d)
          (Finset.mem_range.2 hJpos)
  · exact Finset.sum_nonneg fun j hj => hw0 j hj d

/-- `φ*(D) = ∏_{Q∈D}(1 − N(Q)⁻¹)`. -/
def phiS (D : Finset Pr) : ℂ := ∏ Q ∈ D, (1 - (((absNorm Q.1 : ℝ) : ℂ))⁻¹)

theorem norm_phiS_le (D : Finset Pr) : ‖phiS D‖ ≤ 1 := by
  unfold phiS
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun Q _ => ?_
  have hQ := absNorm_Pr_pos Q
  have h1 : (1 : ℝ) ≤ absNorm Q.1 := by
    have := one_le_nI {Q}
    rwa [nI_eq_prod, Finset.prod_singleton] at this
  have hi : (absNorm Q.1 : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hi0 : 0 ≤ (absNorm Q.1 : ℝ)⁻¹ := inv_nonneg.2 hQ.le
  rw [show (1 : ℂ) - (((absNorm Q.1 : ℝ) : ℂ))⁻¹ = ((1 - (absNorm Q.1 : ℝ)⁻¹ : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  linarith

theorem phiS_union {B1 B2 : Finset Pr} (h : Disjoint B1 B2) :
    phiS (B1 ∪ B2) = phiS B1 * phiS B2 := by
  unfold phiS; rw [Finset.prod_union h]

/-- The surviving main term of round 354's `pair_eq`, without its constant. -/
def pairMain (K₁ Kt : ℝ) (G D : Finset Pr) : ℂ :=
  (∑ T ∈ G.powerset, (-1 : ℂ) ^ T.card * FD D (∏ P ∈ T, πP P)) *
    ∑ U ∈ G.powerset, FD D (∏ P ∈ U, πP P) * sqfR (FD D) G (nI U) K₁ Kt

/-- The row coefficient of the `U`-piece: `N(d)^{−1/2}` on the squarefree rows prime to `G` with
`K₁ < N(U)N(d) ≤ N(U)K`. -/
def cU (G U : Finset Pr) (K₁ Kt : ℝ) (d : 𝓞 K) : ℂ :=
  if Squarefree (span {d}) ∧ (∀ P ∈ G, ¬ πP P ∣ d) ∧
    K₁ < nI U * (absNorm (span {d}) : ℝ) ∧ (absNorm (span {d}) : ℝ) ≤ Kt then
    (((Real.sqrt (absNorm (span {d}) : ℝ))⁻¹ : ℝ) : ℂ) else 0

theorem FD_union {B1 B2 : Finset Pr} (h : Disjoint B1 B2) (x : 𝓞 K) :
    FD (B1 ∪ B2) x = q2 B1 x * q2 B2 x * (((Real.sqrt (absNorm (span {x}) : ℝ))⁻¹ : ℝ) : ℂ) := by
  unfold FD; rw [q2_union h]

/-- **The main term of a pair, expanded**: `φ*(D)·pairMain = Σ_{T,U⊆G}(−1)^{|T|}(N(T)N(U))^{−1/2}
  Σ_d c_U(d)·(φ*(B₁)ρ_{B₁}(π_Tπ_U))·(φ*(B₂)ρ_{B₂}(π_Tπ_U))·ρ_{B₁}(d)ρ_{B₂}(d)`. -/
theorem phiS_pairMain {K₁ Kt : ℝ} (G : Finset Pr) {B1 B2 : Finset Pr} (h : Disjoint B1 B2) :
    phiS (B1 ∪ B2) * pairMain K₁ Kt G (B1 ∪ B2) =
      ∑ T ∈ G.powerset, ∑ U ∈ G.powerset, (-1 : ℂ) ^ T.card *
        ((((Real.sqrt (nI T))⁻¹ * (Real.sqrt (nI U))⁻¹ : ℝ)) : ℂ) *
        ∑' d : 𝓞 K, cU G U K₁ Kt d *
          ((phiS B1 * q2 B1 ((∏ P ∈ T, πP P) * ∏ P ∈ U, πP P)) *
            (phiS B2 * q2 B2 ((∏ P ∈ T, πP P) * ∏ P ∈ U, πP P)) * (q2 B1 d * q2 B2 d)) := by
  unfold pairMain
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  unfold sqfR
  simp only [← tsum_mul_left]
  refine tsum_congr fun d => ?_
  unfold cU
  rw [phiS_union h, FD_union h, FD_union h, absNorm_span_prod_πP, absNorm_span_prod_πP, q2_mul,
    q2_mul]
  split_ifs with hd
  · rw [FD_union h]
    push_cast
    ring
  · simp

theorem norm_cU_le {G U : Finset Pr} (hU : U ⊆ G) {K₁ Kt : ℝ} (d : 𝓞 K) :
    ‖cU G U K₁ Kt d‖ ≤ wR (K₁ / nI G) Kt d := by
  unfold cU wR
  split_ifs with h1 h2
  · rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  · exfalso
    apply h2
    refine ⟨h1.1, ?_, h1.2.2.2⟩
    have hG := nI_pos G
    have hUG := nI_mono hU
    have hN : (0 : ℝ) ≤ absNorm (span {d}) := Nat.cast_nonneg _
    rw [div_lt_iff₀ hG]
    nlinarith [h1.2.2.1]
  · rw [norm_zero]; exact inv_nonneg.2 (Real.sqrt_nonneg _)
  · rw [norm_zero]

theorem summable_cU (G U : Finset Pr) (K₁ Kt : ℝ) (f : 𝓞 K → ℂ) :
    Summable fun d => cU G U K₁ Kt d * f d := by
  refine summable_of_ne_finset_zero (s := eltsLe Kt) fun d hd => ?_
  unfold cU
  rw [mem_eltsLe] at hd
  rw [ite_eq_right fun h => hd h.2.2.2, zero_mul]

/-- **The bilinear bound for the surviving main term**: with `FBound (wR (K₁/N(G)) K) X Δ`, for a
family of column sets of norm at most `X` and any coefficients,
`|Σ_{B₁,B₂ disjoint} a(B₁)b(B₂)φ*(B₁ ∪ B₂)·pairMain(G, B₁ ∪ B₂)|
  ≤ 4^{|G|}·Δ·√(Σ_B 2^{|B|}|a(B)|²)·√(Σ_B 2^{|B|}|b(B)|²)`. -/
theorem main_bilin {K₁ Kt X Δ : ℝ} (hΔ : 0 ≤ Δ) {G : Finset Pr}
    (hF : FBound (wR (K₁ / nI G) Kt) X Δ) (𝒩 : Finset (Finset Pr)) (h𝒩 : ∀ B ∈ 𝒩, nI B ≤ X)
    (a b : Finset Pr → ℂ) :
    ‖∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 *
        (phiS (B1 ∪ B2) * pairMain K₁ Kt G (B1 ∪ B2)) else 0‖ ≤
      (4 : ℝ) ^ G.card * (Δ * (Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖a B‖ ^ 2) *
        Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖b B‖ ^ 2))) := by
  set c : Finset Pr → Finset Pr → ℂ := fun T U => (-1 : ℂ) ^ T.card *
    ((((Real.sqrt (nI T))⁻¹ * (Real.sqrt (nI U))⁻¹ : ℝ)) : ℂ) with hc
  set e : Finset Pr → Finset Pr → 𝓞 K := fun T U => (∏ P ∈ T, πP P) * ∏ P ∈ U, πP P with he
  set α : Finset Pr → Finset Pr → Finset Pr → ℂ := fun T U B => a B * (phiS B * q2 B (e T U))
    with hα
  set β : Finset Pr → Finset Pr → Finset Pr → ℂ := fun T U B => b B * (phiS B * q2 B (e T U))
    with hβ
  set Y : Finset Pr → Finset Pr → Finset Pr → Finset Pr → 𝓞 K → ℂ := fun B1 B2 T U d =>
    if Disjoint B1 B2 then α T U B1 * β T U B2 * (q2 B1 d * q2 B2 d) else 0 with hY
  set f : Finset Pr → Finset Pr → Finset Pr → Finset Pr → ℂ := fun B1 B2 T U =>
    c T U * ∑' d : 𝓞 K, cU G U K₁ Kt d * Y B1 B2 T U d with hf
  -- the rearrangement
  have h1 : ∀ B1 B2, (if Disjoint B1 B2 then a B1 * b B2 *
      (phiS (B1 ∪ B2) * pairMain K₁ Kt G (B1 ∪ B2)) else 0) =
      ∑ T ∈ G.powerset, ∑ U ∈ G.powerset, f B1 B2 T U := by
    intro B1 B2
    by_cases h12 : Disjoint B1 B2
    · rw [ite_eq_left h12, phiS_pairMain G h12, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun U _ => ?_
      simp only [hf, hc, hY, hα, hβ, he, ite_eq_left h12]
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
      refine tsum_congr fun d => ?_
      ring
    · rw [ite_eq_right h12]
      symm
      refine Finset.sum_eq_zero fun T _ => Finset.sum_eq_zero fun U _ => ?_
      simp only [hf, hY, ite_eq_right h12, mul_zero, tsum_zero]
  have h2 : ∀ T U, ∑' d : 𝓞 K, cU G U K₁ Kt d * ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, Y B1 B2 T U d =
      ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, ∑' d : 𝓞 K, cU G U K₁ Kt d * Y B1 B2 T U d := by
    intro T U
    simp only [Finset.mul_sum]
    rw [Summable.tsum_finsetSum fun B1 _ => summable_sum fun B2 _ => summable_cU G U K₁ Kt _]
    refine Finset.sum_congr rfl fun B1 _ => ?_
    rw [Summable.tsum_finsetSum fun B2 _ => summable_cU G U K₁ Kt _]
  have hre : (∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, if Disjoint B1 B2 then a B1 * b B2 *
      (phiS (B1 ∪ B2) * pairMain K₁ Kt G (B1 ∪ B2)) else 0) =
      ∑ T ∈ G.powerset, ∑ U ∈ G.powerset, c T U *
        ∑' d : 𝓞 K, cU G U K₁ Kt d * ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, Y B1 B2 T U d := by
    simp only [h1]
    simp only [h2]
    simp only [Finset.mul_sum]
    calc ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, ∑ T ∈ G.powerset, ∑ U ∈ G.powerset, f B1 B2 T U
        = ∑ B1 ∈ 𝒩, ∑ T ∈ G.powerset, ∑ U ∈ G.powerset, ∑ B2 ∈ 𝒩, f B1 B2 T U := by
          refine Finset.sum_congr rfl fun B1 _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ T ∈ G.powerset, ∑ U ∈ G.powerset, ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, f B1 B2 T U := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.sum_comm]
  -- the bound on each `(T, U)`-piece
  set Bd : ℝ := Δ * (Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖a B‖ ^ 2) *
    Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖b B‖ ^ 2)) with hBd
  have hpiece : ∀ T ∈ G.powerset, ∀ U ∈ G.powerset,
      ‖c T U * ∑' d : 𝓞 K, cU G U K₁ Kt d * ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, Y B1 B2 T U d‖ ≤ Bd := by
    intro T _ U hU
    have hUG := Finset.mem_powerset.1 hU
    have hcn : ‖c T U‖ ≤ 1 := by
      simp only [hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real]
      have hT := one_le_nI T
      have hU' := one_le_nI U
      have h1T : (Real.sqrt (nI T))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hT)
      have h1U : (Real.sqrt (nI U))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hU')
      rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)),
        Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      nlinarith [inv_nonneg.2 (Real.sqrt_nonneg (nI T)), inv_nonneg.2 (Real.sqrt_nonneg (nI U))]
    have hb := bilin_disj_le_c (wR_nonneg _ _) (summable_wR (K₁ / nI G) Kt) hΔ hF 𝒩 h𝒩
      (α T U) (β T U) (cU G U K₁ Kt) (norm_cU_le hUG)
    have hsa : Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖α T U B‖ ^ 2) ≤
        Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖a B‖ ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun B _ => ?_)
      have : ‖α T U B‖ ≤ ‖a B‖ := by
        simp only [hα, norm_mul]
        have h1 := norm_phiS_le B
        have h2 := norm_q2_le B (e T U)
        have := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        rw [one_mul] at this
        nlinarith [norm_nonneg (a B), norm_nonneg (phiS B), norm_nonneg (q2 B (e T U))]
      have h0 := norm_nonneg (α T U B)
      have hp : (0 : ℝ) ≤ 2 ^ B.card := by positivity
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 this 2) hp
    have hsb : Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖β T U B‖ ^ 2) ≤
        Real.sqrt (∑ B ∈ 𝒩, (2 : ℝ) ^ B.card * ‖b B‖ ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun B _ => ?_)
      have : ‖β T U B‖ ≤ ‖b B‖ := by
        simp only [hβ, norm_mul]
        have h1 := norm_phiS_le B
        have h2 := norm_q2_le B (e T U)
        have := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        rw [one_mul] at this
        nlinarith [norm_nonneg (b B), norm_nonneg (phiS B), norm_nonneg (q2 B (e T U))]
      have h0 := norm_nonneg (β T U B)
      have hp : (0 : ℝ) ≤ 2 ^ B.card := by positivity
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 this 2) hp
    have hb' : ‖∑' d : 𝓞 K, cU G U K₁ Kt d * ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, Y B1 B2 T U d‖ ≤ Bd := by
      refine hb.trans ?_
      rw [hBd]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hsa hsb (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)) hΔ
    rw [norm_mul]
    have hBd0 : 0 ≤ Bd := le_trans (norm_nonneg _) hb'
    calc ‖c T U‖ * _ ≤ 1 * Bd := mul_le_mul hcn hb' (norm_nonneg _) zero_le_one
      _ = Bd := one_mul Bd
  rw [hre]
  calc _ ≤ ∑ T ∈ G.powerset, ∑ U ∈ G.powerset,
        ‖c T U * ∑' d : 𝓞 K, cU G U K₁ Kt d * ∑ B1 ∈ 𝒩, ∑ B2 ∈ 𝒩, Y B1 B2 T U d‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun T _ => norm_sum_le _ _)
    _ ≤ ∑ T ∈ G.powerset, ∑ U ∈ G.powerset, Bd :=
        Finset.sum_le_sum fun T hT => Finset.sum_le_sum fun U hU => hpiece T hT U hU
    _ = (4 : ℝ) ^ G.card * Bd := by
        simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        push_cast
        rw [← mul_assoc, ← pow_two, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
          mul_comm 2 G.card]

end Eis

end

#print axioms Eis.wR_nonneg
#print axioms Eis.summable_wR
#print axioms Eis.FBound.of_le
#print axioms Eis.FBound.sum
#print axioms Eis.fBound_wR
#print axioms Eis.norm_phiS_le
#print axioms Eis.phiS_union
#print axioms Eis.FD_union
#print axioms Eis.phiS_pairMain
#print axioms Eis.norm_cU_le
#print axioms Eis.summable_cU
#print axioms Eis.main_bilin
