import EisensteinQuadSieveGcdPart

/-! # The quadratic large sieve, part 7c: shells, the recursion and the norms of the rows (round 357)

S5e of round 312's plan, the third piece of S5e-7: the machinery of Goldmakher and Louvel's proof of
their Theorem cor, before the bound for one gcd part (round 356) is fed into it.

* **Columns restricted by a predicate** (`FBoundP`, `FBoundP.of_fBound`, `FBoundP.mono`) and
  Heath-Brown's Lemma 2 for them (`fBoundP_gcd`): round 346's `fBound_gcd` with the columns of
  the norm restricted by a predicate, a constant uniform in the weight and the predicate.
* **Shells** (`fBound_of_shells`): the norm on a ball `N(A) ≤ X < 2^L` is at most `L` times the
  largest norm on the shells `X/2^{k+1} < N(A) ≤ X/2^k`, by Cauchy–Schwarz over the shells.
* **The trivial bound** (`fBound_triv`, `card_fsLe_mono`):
  `FBound w X ((Σ_m w(m))·#{A : N(A) ≤ X})`.
* **The recursion** (`fBound_rec`): if a norm `Δ` at `N'/g₀` gives the norm `aΔ + F` on the shell
  of `N'` for `2g₀ < N' ≤ N`, then for `N ≤ g₀^r` and `N < 2^L` the norm at `N` is at most
  `(La + 1)^r·(D_t + rL(D_t + F))`, with `D_t` the trivial bound at `2g₀`.
* **The rows from `(E_α)`** (`fBound_sqfW_of_qExp`, `fBound_wR_of_qExp`, with
  `nat_le_rpow_of_two_pow_le`, `sqfW_mono`): the squarefree rows up to `Y` have norm
  `C(X·max(Y, 1))^ε(X + max(Y, 1)^α)` at `X`, and round 355's rows `N(d)^{−1/2}` on `(Y₁, Y₂]`
  have norm at most `(1 + (Y₂/Y₁)^δ/(δ log 2))·C(X·max(2Y₂, 1))^ε(Y₁^{−1/2}(X + 1)
  + 2^α max(Y₂, 1)^{α−1/2})`.
* **The sizes** (`sizeE`, `sqrtM_bracket_le`, `err3_size_le`, `err4_size_le`, with
  `rpow_cx2Z_div`, `K_rpow_le`, `sqrt_mul_K_rpow`, `M_K1_rpow_div`, `sizeE_ge`,
  `rpow_le_rpow_Q`, `max_one_rpow_le`): for `K = C_K N²Q^ε/M ≤ M`, `Q = MN`, `K₁ = c₀N'²/M` and
  `X = N'/N(G)`, the three terms of round 356's bound are at most constants times
  `Q^{θ}·g₀·E`, with Goldmakher and Louvel's size `E = M + N + N^{2α−1}M^{1−α}`.
-/

open Complex NumberField Ideal
open scoped Classical ComplexConjugate

noncomputable section

namespace Eis

/-- **The weighted norm on the columns satisfying `S`**: `FBound` restricted to the column families
whose members satisfy `S`. -/
def FBoundP (w : 𝓞 K → ℝ) (S : Finset Pr → Prop) (N Δ : ℝ) : Prop :=
  ∀ (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ), (∀ A ∈ 𝒩, S A ∧ nI A ≤ N) →
    ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 ≤ Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2

/-- **Heath-Brown's Lemma 2 on the columns satisfying `S`**: round 346's `fBound_gcd` with the
columns restricted by a predicate. -/
theorem fBoundP_gcd {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : 𝓞 K → ℝ), (∀ m, 0 ≤ w m) → Summable w →
      ∀ (S : Finset Pr → Prop) (N g0 Δ : ℝ) (F3 : Finset Pr → ℝ), 1 ≤ N → 0 < g0 → 0 ≤ Δ →
      (∀ G, 0 ≤ F3 G) → FBound w (N / g0) Δ →
      (∀ G ∈ fsLe g0, ∀ (𝒩 : Finset (Finset Pr)) (α : Finset Pr → ℂ),
        (∀ A ∈ 𝒩, S A ∧ nI A ≤ N) → (gcdPart w G 𝒩 α).re ≤ F3 G * ∑ A ∈ 𝒩, ‖α A‖ ^ 2) →
      FBoundP w S N (C * N ^ δ * Δ + ∑ G ∈ fsLe g0, F3 G) := by
  obtain ⟨C4, hC4pos, hC4⟩ := four_pow_card_le hδ
  refine ⟨C4, hC4pos.le, fun w hw0 hw S N g0 Δ F3 hN hg0 hΔ hF3 hF h3 𝒩 α h𝒩 => ?_⟩
  set U : Finset Pr := 𝒩.sup id with hU
  have h𝒩U : ∀ A ∈ 𝒩, A ⊆ U := fun A hA => Finset.le_sup (f := id) hA
  set S2 : ℝ := ∑ A ∈ 𝒩, ‖α A‖ ^ 2 with hS2
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the expansion, sorted by the greatest common divisor
  have hexp : ((∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 : ℝ) : ℂ) =
      ∑ G ∈ U.powerset, gcdPart w G 𝒩 α := by
    rw [tsum_w_colSum_eq hw]
    unfold gcdPart
    symm
    calc ∑ G ∈ U.powerset, ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩,
          (if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0)
        = ∑ A1 ∈ 𝒩, ∑ G ∈ U.powerset, ∑ A2 ∈ 𝒩,
          (if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0) := Finset.sum_comm
      _ = ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, ∑ G ∈ U.powerset,
          (if A1 ∩ A2 = G then α A1 * conj (α A2) * pW w A1 A2 else 0) :=
          Finset.sum_congr rfl fun A1 _ => Finset.sum_comm
      _ = ∑ A1 ∈ 𝒩, ∑ A2 ∈ 𝒩, α A1 * conj (α A2) * pW w A1 A2 := by
          refine Finset.sum_congr rfl fun A1 hA1 => Finset.sum_congr rfl fun A2 _ => ?_
          have hmem : A1 ∩ A2 ∈ U.powerset :=
            Finset.mem_powerset.2 (Finset.inter_subset_left.trans (h𝒩U A1 hA1))
          rw [Finset.sum_ite_eq, ite_eq_left hmem]
  have hre : (∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2) =
      ∑ G ∈ U.powerset, (gcdPart w G 𝒩 α).re := by
    have := congrArg Complex.re hexp
    rw [Complex.ofReal_re, Complex.re_sum] at this
    exact this
  rw [hre, ← Finset.sum_filter_add_sum_filter_not U.powerset (· ∈ fsLe g0)]
  -- the small greatest common divisors
  have hsmall : ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), (gcdPart w G 𝒩 α).re ≤
      (∑ G ∈ fsLe g0, F3 G) * S2 := by
    calc ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), (gcdPart w G 𝒩 α).re
        ≤ ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), F3 G * S2 :=
          Finset.sum_le_sum fun G hG => h3 G (Finset.mem_filter.1 hG).2 𝒩 α h𝒩
      _ ≤ ∑ G ∈ fsLe g0, F3 G * S2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun G hG => (Finset.mem_filter.1 hG).2)
            fun G _ _ => mul_nonneg (hF3 G) hS20
      _ = (∑ G ∈ fsLe g0, F3 G) * S2 := by rw [Finset.sum_mul]
  -- the large greatest common divisors
  have hpiece : ∀ G ∈ U.powerset.filter (· ∉ fsLe g0), ∀ E : Finset Pr,
      ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), α A * q2 A m‖ ^ 2 ≤
        Δ * ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 := by
    intro G hG E
    have hGl : g0 < nI G := lt_nI_of_not_mem_fsLe (Finset.mem_filter.1 hG).2
    refine hF.sub hw0 hw 𝒩 α (G ∪ E) fun A hA _ => ?_
    have h1 : g0 ≤ nI (G ∪ E) := hGl.le.trans (nI_mono Finset.subset_union_left)
    have h2 := (h𝒩 A hA).2
    rw [div_mul_eq_mul_div, le_div_iff₀ hg0]
    nlinarith
  have hlarge : ∀ G ∈ U.powerset.filter (· ∉ fsLe g0), (gcdPart w G 𝒩 α).re ≤
      ∑ E ∈ (U \ G).powerset, Δ * ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 := by
    intro G hG
    refine (Complex.re_le_norm _).trans ?_
    rw [gcdPart_eq hw U 𝒩 h𝒩U G α]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun E _ => ?_)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun m => mul_nonneg (hw0 m) (sq_nonneg _))]
    exact hpiece G hG E
  have hcount : ∑ G ∈ U.powerset.filter (· ∉ fsLe g0), ∑ E ∈ (U \ G).powerset,
      ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 ≤ C4 * N ^ δ * S2 := by
    refine (sum_triple_le U 𝒩 _ (Finset.filter_subset _ _) (fun G => (U \ G).powerset)
      (fun G => Finset.powerset_mono.2 Finset.sdiff_subset) (fun A => ‖α A‖ ^ 2)
      fun A => sq_nonneg _).trans ?_
    rw [hS2, Finset.mul_sum]
    refine Finset.sum_le_sum fun A hA => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc (4 : ℝ) ^ A.card ≤ C4 * nI A ^ δ := hC4 A
      _ ≤ C4 * N ^ δ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (nI_pos A).le (h𝒩 A hA).2 hδ.le) hC4pos.le
  calc ∑ G ∈ U.powerset.filter (· ∈ fsLe g0), (gcdPart w G 𝒩 α).re +
        ∑ G ∈ U.powerset.filter (· ∉ fsLe g0), (gcdPart w G 𝒩 α).re
      ≤ (∑ G ∈ fsLe g0, F3 G) * S2 + ∑ G ∈ U.powerset.filter (· ∉ fsLe g0),
          ∑ E ∈ (U \ G).powerset, Δ * ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 :=
        add_le_add hsmall (Finset.sum_le_sum hlarge)
    _ = (∑ G ∈ fsLe g0, F3 G) * S2 + Δ * ∑ G ∈ U.powerset.filter (· ∉ fsLe g0),
          ∑ E ∈ (U \ G).powerset, ∑ A ∈ 𝒩.filter (fun A => G ∪ E ⊆ A), ‖α A‖ ^ 2 := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ ≤ (∑ G ∈ fsLe g0, F3 G) * S2 + Δ * (C4 * N ^ δ * S2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hΔ)
    _ = (C4 * N ^ δ * Δ + ∑ G ∈ fsLe g0, F3 G) * S2 := by ring


/-- **A ball from its shells**: if the norm on each shell `X/2^{k+1} < N(A) ≤ X/2^k`, `k < L`, is
at most `Δ`, and `X < 2^L`, the norm on the ball `N(A) ≤ X` is at most `L·Δ`. -/
theorem fBound_of_shells {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {X Δ : ℝ}
    (L : ℕ) (hL : X < 2 ^ L)
    (h : ∀ k < L, FBoundP w (fun A => X / 2 ^ (k + 1) < nI A) (X / 2 ^ k) Δ) :
    FBound w X (L * Δ) := by
  intro 𝒩 α h𝒩
  have ex : ∀ A : Finset Pr, ∃ k : ℕ, X / 2 ^ (k + 1) < nI A := fun A => by
    refine ⟨L, ?_⟩
    have h1 := one_le_nI A
    have h2 : (0 : ℝ) < 2 ^ (L + 1) := by positivity
    rw [div_lt_iff₀ h2, pow_succ]
    have h3 : (0 : ℝ) < 2 ^ L := by positivity
    nlinarith
  set kf : Finset Pr → ℕ := fun A => Nat.find (ex A) with hkf
  have hk1 : ∀ A, X / 2 ^ (kf A + 1) < nI A := fun A => Nat.find_spec (ex A)
  have hk2 : ∀ A ∈ 𝒩, nI A ≤ X / 2 ^ kf A := fun A hA => by
    rcases Nat.eq_zero_or_pos (kf A) with h0 | h0
    · rw [h0, pow_zero, div_one]; exact h𝒩 A hA
    · have := Nat.find_min (ex A) (Nat.sub_lt h0 one_pos)
      rw [Nat.sub_add_cancel (show 1 ≤ kf A from h0)] at this
      exact not_lt.1 this
  have hk3 : ∀ A ∈ 𝒩, kf A ∈ Finset.range L := fun A hA => by
    rw [Finset.mem_range]
    have h1 := one_le_nI A
    have hA := h𝒩 A hA
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, pow_zero] at hL; linarith
    · have hmin : kf A ≤ L - 1 := Nat.find_min' (ex A) (by
        rw [Nat.sub_add_cancel (show 1 ≤ L from h0)]
        have h2 : (0 : ℝ) < 2 ^ L := by positivity
        rw [div_lt_iff₀ h2]
        nlinarith)
      omega
  set fib : ℕ → Finset (Finset Pr) := fun k => 𝒩.filter (fun A => kf A = k) with hfib
  have hsplit : ∀ (f : Finset Pr → ℂ), ∑ A ∈ 𝒩, f A = ∑ k ∈ Finset.range L, ∑ A ∈ fib k, f A :=
    fun f => (Finset.sum_fiberwise_of_maps_to hk3 f).symm
  have hsplitR : ∀ (f : Finset Pr → ℝ), ∑ A ∈ 𝒩, f A = ∑ k ∈ Finset.range L, ∑ A ∈ fib k, f A :=
    fun f => (Finset.sum_fiberwise_of_maps_to hk3 f).symm
  have hfibS : ∀ k ∈ Finset.range L, ∀ A ∈ fib k, X / 2 ^ (k + 1) < nI A ∧ nI A ≤ X / 2 ^ k := by
    intro k _ A hA
    rw [Finset.mem_filter] at hA
    rw [← hA.2]
    exact ⟨hk1 A, hk2 A hA.1⟩
  -- Cauchy–Schwarz over the shells
  have hcs : ∀ m : 𝓞 K, ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 ≤
      L * ∑ k ∈ Finset.range L, ‖∑ A ∈ fib k, α A * q2 A m‖ ^ 2 := fun m => by
    rw [hsplit]
    have h1 := norm_sum_le (Finset.range L) fun k => ∑ A ∈ fib k, α A * q2 A m
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range L)
      (f := fun k => ‖∑ A ∈ fib k, α A * q2 A m‖)
    rw [Finset.card_range] at h2
    calc ‖∑ k ∈ Finset.range L, ∑ A ∈ fib k, α A * q2 A m‖ ^ 2
        ≤ (∑ k ∈ Finset.range L, ‖∑ A ∈ fib k, α A * q2 A m‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hsum : ∀ k ∈ Finset.range L, Summable fun m : 𝓞 K =>
      w m * ‖∑ A ∈ fib k, α A * q2 A m‖ ^ 2 := fun k _ => summable_w_colSum hw _ α
  calc ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2
      ≤ ∑' m : 𝓞 K, (L : ℝ) * ∑ k ∈ Finset.range L, w m * ‖∑ A ∈ fib k, α A * q2 A m‖ ^ 2 := by
        refine (summable_w_colSum hw 𝒩 α).tsum_le_tsum (fun m => ?_)
          ((summable_sum hsum).mul_left _)
        rw [← Finset.mul_sum, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hcs m) (hw0 m)
    _ = (L : ℝ) * ∑ k ∈ Finset.range L, ∑' m : 𝓞 K, w m * ‖∑ A ∈ fib k, α A * q2 A m‖ ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum hsum]
    _ ≤ (L : ℝ) * ∑ k ∈ Finset.range L, Δ * ∑ A ∈ fib k, ‖α A‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (Nat.cast_nonneg _)
        exact h k (Finset.mem_range.1 hk) (fib k) α fun A hA => hfibS k hk A hA
    _ = (L : ℝ) * Δ * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := by
        rw [hsplitR, mul_assoc, ← Finset.mul_sum]

/-- **The trivial bound**: `Σ_m w(m)|Σ_A α(A)ρ_A(m)|² ≤ (Σ_m w(m))·#{A : N(A) ≤ X}·Σ_A|α(A)|²`. -/
theorem fBound_triv {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) (X : ℝ) :
    FBound w X ((∑' m, w m) * (fsLe X).card) := by
  intro 𝒩 α h𝒩
  have hsub : 𝒩 ⊆ fsLe X := fun A hA => mem_fsLe_of_nI_le (h𝒩 A hA)
  have hcard : (𝒩.card : ℝ) ≤ (fsLe X).card := by exact_mod_cast Finset.card_le_card hsub
  have hrow : ∀ m, ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 ≤ 𝒩.card * ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := fun m => by
    have h1 := norm_q2Sum_le 𝒩 α m
    have h2 := sq_sum_le_card_mul_sum_sq (s := 𝒩) (f := fun A => ‖α A‖)
    calc ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2 ≤ (∑ A ∈ 𝒩, ‖α A‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hS0 : 0 ≤ ∑ A ∈ 𝒩, ‖α A‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑' m : 𝓞 K, w m * ‖∑ A ∈ 𝒩, α A * q2 A m‖ ^ 2
      ≤ ∑' m : 𝓞 K, w m * (𝒩.card * ∑ A ∈ 𝒩, ‖α A‖ ^ 2) :=
        (summable_w_colSum hw 𝒩 α).tsum_le_tsum
          (fun m => mul_le_mul_of_nonneg_left (hrow m) (hw0 m)) (hw.mul_right _)
    _ = (∑' m, w m) * (𝒩.card * ∑ A ∈ 𝒩, ‖α A‖ ^ 2) := tsum_mul_right
    _ ≤ (∑' m, w m) * ((fsLe X).card * ∑ A ∈ 𝒩, ‖α A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hS0) (tsum_nonneg hw0)
    _ = _ := by ring

/-- **A count from a power of two**: `2^n ≤ x` gives `n ≤ x^δ/(δ log 2)`. -/
theorem nat_le_rpow_of_two_pow_le {n : ℕ} {x δ : ℝ} (hδ : 0 < δ) (h : (2 : ℝ) ^ n ≤ x) :
    (n : ℝ) ≤ x ^ δ / (δ * Real.log 2) := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (n : ℝ) * Real.log 2 ≤ Real.log x := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h
  have h2 := Real.log_le_rpow_div hx.le hδ
  rw [le_div_iff₀ (mul_pos hδ hl2)]
  have h3 : Real.log x * δ ≤ x ^ δ := by rwa [le_div_iff₀ hδ] at h2
  nlinarith

theorem sqfW_mono {Y Y' : ℝ} (h : Y ≤ Y') (d : 𝓞 K) : sqfW Y d ≤ sqfW Y' d := by
  unfold sqfW
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.trans h⟩ h2
  · exact zero_le_one
  · exact le_rfl

/-- **The squarefree rows from `(E_α)`**: with `C` from the exponent, for `X ≥ 1` and every `Y`,
`FBound (sqfW Y) X (C·(X·max(Y, 1))^ε·(X + max(Y, 1)^α))`. -/
theorem fBound_sqfW_of_qExp {α : ℝ} (h : QExp α) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 1 ≤ X →
      FBound (sqfW Y) X (C * (X * max Y 1) ^ ε * (X + max Y 1 ^ α)) := by
  obtain ⟨C, hC0, hC⟩ := h ε hε
  set c : ℝ := ((Fintype.card (𝓞 K)ˣ * Fintype.card (tIdeals 1) : ℕ) : ℝ) with hc
  refine ⟨c * C, mul_nonneg (Nat.cast_nonneg _) hC0, fun X Y hX => ?_⟩
  set Y' := max Y 1 with hY'
  have hY1 : 1 ≤ Y' := le_max_right _ _
  have hΔ : 0 ≤ C * (X * Y') ^ ε * (X + Y' ^ α) := by
    have : 0 ≤ X + Y' ^ α := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y') α
      linarith
    positivity
  have hq := hC X Y' hX hY1
  have hf := fBound_sqf_of_adm hΔ (fBound_of_qBound hΔ hq)
  have hle : FBound (sqfW Y) X (c * (C * (X * Y') ^ ε * (X + Y' ^ α))) :=
    FBound.of_le (sqfW_nonneg Y) (sqfW_mono (le_max_left Y 1)) (summable_sqfW Y') hf
  have e : c * (C * (X * Y') ^ ε * (X + Y' ^ α)) = c * C * (X * Y') ^ ε * (X + Y' ^ α) := by ring
  rwa [e] at hle

/-- **The rows `N(d)^{−1/2}` on `(Y₁, Y₂]` from `(E_α)`**, for `α ≥ 1/2`: round 355's dyadic pieces
with at most `1 + (Y₂/Y₁)^δ/(δ log 2)` pieces, each at most
`C·(X·max(2Y₂, 1))^ε·(Y₁^{−1/2}(X + 1) + 2^α·max(Y₂, 1)^{α−1/2})`. -/
theorem fBound_wR_of_qExp {α : ℝ} (hα : 1 / 2 ≤ α) (h : QExp α) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y₁ Y₂ : ℝ, 1 ≤ X → 0 < Y₁ → Y₁ ≤ Y₂ →
      FBound (wR Y₁ Y₂) X ((1 + (Y₂ / Y₁) ^ δ / (δ * Real.log 2)) *
        (C * (X * max (2 * Y₂) 1) ^ ε *
          ((Real.sqrt Y₁)⁻¹ * (X + 1) + 2 ^ α * max Y₂ 1 ^ (α - 1 / 2)))) := by
  obtain ⟨C, hC0, hC⟩ := fBound_sqfW_of_qExp h hε
  refine ⟨C, hC0, fun X Y₁ Y₂ hX hY₁ hY => ?_⟩
  have hex : ∃ J : ℕ, Y₂ ≤ 2 ^ J * Y₁ := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (Y₂ / Y₁) (by norm_num : (1 : ℝ) < 2)
    refine ⟨J, ?_⟩
    rw [div_lt_iff₀ hY₁] at hJ
    exact hJ.le
  set J := Nat.find hex with hJdef
  have hJ : Y₂ ≤ 2 ^ J * Y₁ := Nat.find_spec hex
  have hlt : ∀ j < J, 2 ^ j * Y₁ < Y₂ := fun j hj => not_le.1 (Nat.find_min hex hj)
  have hFn : ∀ Y, FBound (sqfW Y) X (C * (X * max Y 1) ^ ε * (X + max Y 1 ^ α)) :=
    fun Y => hC X Y hX
  have hw := fBound_wR hY₁ J hJ _ hFn
  -- the bracket
  set T : ℝ := C * (X * max (2 * Y₂) 1) ^ ε *
    ((Real.sqrt Y₁)⁻¹ * (X + 1) + 2 ^ α * max Y₂ 1 ^ (α - 1 / 2)) with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ (Real.sqrt Y₁)⁻¹ * (X + 1) + 2 ^ α * max Y₂ 1 ^ (α - 1 / 2) := by
      have h1 : 0 ≤ (Real.sqrt Y₁)⁻¹ * (X + 1) := by positivity
      have h2 : 0 ≤ (2 : ℝ) ^ α * max Y₂ 1 ^ (α - 1 / 2) := by
        have := Real.rpow_nonneg (le_trans zero_le_one (le_max_right Y₂ 1)) (α - 1 / 2)
        positivity
      linarith
    positivity
  have hterm : ∀ j < J, (Real.sqrt (2 ^ j * Y₁))⁻¹ *
      (C * (X * max (2 ^ (j + 1) * Y₁) 1) ^ ε * (X + max (2 ^ (j + 1) * Y₁) 1 ^ α)) ≤ T := by
    intro j hj
    set t : ℝ := 2 ^ j * Y₁ with ht
    have ht0 : 0 < t := by positivity
    have htY : Y₁ ≤ t := le_mul_of_one_le_left hY₁.le (one_le_pow₀ (by norm_num))
    have ht2 : t < Y₂ := hlt j hj
    have h2t : 2 ^ (j + 1) * Y₁ = 2 * t := by rw [ht, pow_succ]; ring
    rw [h2t]
    have hs : (Real.sqrt t)⁻¹ ≤ (Real.sqrt Y₁)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 hY₁) (Real.sqrt_le_sqrt htY)
    have hs0 : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hpow : (X * max (2 * t) 1) ^ ε ≤ (X * max (2 * Y₂) 1) ^ ε := by
      refine Real.rpow_le_rpow (by positivity) ?_ hε.le
      refine mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (by linarith)
    have hmax : (Real.sqrt t)⁻¹ * max (2 * t) 1 ^ α ≤
        (Real.sqrt Y₁)⁻¹ + 2 ^ α * max Y₂ 1 ^ (α - 1 / 2) := by
      have hpos : 0 ≤ (2 : ℝ) ^ α * max Y₂ 1 ^ (α - 1 / 2) := by
        have := Real.rpow_nonneg (le_trans zero_le_one (le_max_right Y₂ 1)) (α - 1 / 2)
        positivity
      rcases le_total (2 * t) 1 with h1 | h1
      · rw [max_eq_right h1, Real.one_rpow, mul_one]; linarith
      · rw [max_eq_left h1, Real.mul_rpow (by norm_num) ht0.le, Real.sqrt_eq_rpow,
          ← Real.rpow_neg ht0.le]
        have e : t ^ (-(1 / 2 : ℝ)) * (2 ^ α * t ^ α) = 2 ^ α * t ^ (α - 1 / 2) := by
          rw [mul_left_comm, ← Real.rpow_add ht0]; ring_nf
        rw [e]
        have : t ^ (α - 1 / 2) ≤ max Y₂ 1 ^ (α - 1 / 2) :=
          Real.rpow_le_rpow ht0.le (ht2.le.trans (le_max_left _ _)) (by linarith)
        have h2a : (0 : ℝ) ≤ 2 ^ α := by positivity
        have := mul_le_mul_of_nonneg_left this h2a
        have : 0 ≤ (Real.sqrt Y₁)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
        linarith
    have hin : (Real.sqrt t)⁻¹ * (X + max (2 * t) 1 ^ α) ≤
        (Real.sqrt Y₁)⁻¹ * (X + 1) + 2 ^ α * max Y₂ 1 ^ (α - 1 / 2) := by
      have := mul_le_mul_of_nonneg_right hs (by linarith : (0 : ℝ) ≤ X)
      nlinarith
    have hP0 : 0 ≤ (X * max (2 * t) 1) ^ ε := by positivity
    calc (Real.sqrt t)⁻¹ * (C * (X * max (2 * t) 1) ^ ε * (X + max (2 * t) 1 ^ α))
        = C * (X * max (2 * t) 1) ^ ε * ((Real.sqrt t)⁻¹ * (X + max (2 * t) 1 ^ α)) := by ring
      _ ≤ C * (X * max (2 * Y₂) 1) ^ ε *
          ((Real.sqrt Y₁)⁻¹ * (X + 1) + 2 ^ α * max Y₂ 1 ^ (α - 1 / 2)) := by
        have hb0 : 0 ≤ (Real.sqrt t)⁻¹ * (X + max (2 * t) 1 ^ α) := by
          have := Real.rpow_nonneg (le_trans zero_le_one (le_max_right (2 * t) 1)) α
          positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC0) hin hb0 (by positivity)
  -- the count of pieces
  have hJb : (J : ℝ) ≤ 1 + (Y₂ / Y₁) ^ δ / (δ * Real.log 2) := by
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · rw [h0, Nat.cast_zero]
      have : 0 ≤ (Y₂ / Y₁) ^ δ / (δ * Real.log 2) := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        have : 0 ≤ (Y₂ / Y₁) ^ δ := Real.rpow_nonneg (div_nonneg (hY₁.le.trans hY) hY₁.le) δ
        positivity
      linarith
    · have h1 := hlt (J - 1) (Nat.sub_lt h0 one_pos)
      have h2 : (2 : ℝ) ^ (J - 1) ≤ Y₂ / Y₁ := by
        rw [le_div_iff₀ hY₁]; exact h1.le
      have h3 := nat_le_rpow_of_two_pow_le hδ h2
      rw [Nat.cast_sub (show 1 ≤ J from h0), Nat.cast_one] at h3
      linarith
  refine hw.mono le_rfl ?_
  calc ∑ j ∈ Finset.range J, (Real.sqrt (2 ^ j * Y₁))⁻¹ *
        (C * (X * max (2 ^ (j + 1) * Y₁) 1) ^ ε * (X + max (2 ^ (j + 1) * Y₁) 1 ^ α))
      ≤ ∑ _j ∈ Finset.range J, T :=
        Finset.sum_le_sum fun j hj => hterm j (Finset.mem_range.1 hj)
    _ = J * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hJb hT0

theorem FBoundP.of_fBound {w : 𝓞 K → ℝ} {N Δ : ℝ} (S : Finset Pr → Prop) (h : FBound w N Δ) :
    FBoundP w S N Δ := fun 𝒩 α h𝒩 => h 𝒩 α fun A hA => (h𝒩 A hA).2

theorem FBoundP.mono {w : 𝓞 K → ℝ} {S : Finset Pr → Prop} {N Δ Δ' : ℝ} (h : FBoundP w S N Δ)
    (hΔ : Δ ≤ Δ') : FBoundP w S N Δ' := fun 𝒩 α h𝒩 =>
  (h 𝒩 α h𝒩).trans (mul_le_mul_of_nonneg_right hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem card_fsLe_mono {x y : ℝ} (h : x ≤ y) : ((fsLe x).card : ℝ) ≤ (fsLe y).card := by
  have : fsLe x ⊆ fsLe y := fun A hA => by
    rw [mem_fsLe] at hA ⊢; exact hA.trans (Nat.floor_le_floor h)
  exact_mod_cast Finset.card_le_card this

/-- **The recursion** (the proof of Goldmakher and Louvel's Theorem cor): suppose that on each
shell `N'/2 < N(A) ≤ N'` with `2g₀ < N' ≤ N` a norm `Δ` at `N'/g₀` gives the norm `aΔ + F`.
Let `N ≤ g₀^r`, `N < 2^L`, and `D_t = (Σ_m w(m))·#{A : N(A) ≤ 2g₀}`. Then the norm at `N` is at most
`(La + 1)^r·(D_t + rL(D_t + F))`. -/
theorem fBound_rec {w : 𝓞 K → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {N g0 a F : ℝ}
    (hg0 : 1 ≤ g0) (r : ℕ) (hr : N ≤ g0 ^ r) (L : ℕ) (hL : N < 2 ^ L) (ha : 0 ≤ a) (hF : 0 ≤ F)
    (hsh : ∀ N', 2 * g0 < N' → N' ≤ N → ∀ Δ, 0 ≤ Δ → FBound w (N' / g0) Δ →
      FBoundP w (fun A => N' / 2 < nI A) N' (a * Δ + F)) :
    FBound w N ((L * a + 1) ^ r * ((∑' m, w m) * (fsLe (2 * g0)).card +
      r * (L * ((∑' m, w m) * (fsLe (2 * g0)).card + F)))) := by
  set Dt : ℝ := (∑' m, w m) * (fsLe (2 * g0)).card with hDt
  have hDt0 : 0 ≤ Dt := mul_nonneg (tsum_nonneg hw0) (Nat.cast_nonneg _)
  have hg0p : 0 < g0 := by linarith
  set B : ℕ → ℝ := fun i => (L * a + 1) ^ i * (Dt + i * (L * (Dt + F))) with hB
  have hB0 : ∀ i, 0 ≤ B i := fun i => by
    have : 0 ≤ (L : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
    positivity
  -- the trivial bound below `2g₀`
  have htriv : ∀ X, X ≤ 2 * g0 → FBound w X Dt := fun X hX =>
    (fBound_triv hw0 hw X).mono le_rfl
      (mul_le_mul_of_nonneg_left (card_fsLe_mono hX) (tsum_nonneg hw0))
  have key : ∀ i : ℕ, i ≤ r → ∀ X, X ≤ g0 ^ i → X ≤ N → FBound w X (B i) := by
    intro i
    induction i with
    | zero =>
      intro _ X hX _
      rw [pow_zero] at hX
      refine (htriv X (by linarith)).mono le_rfl (le_of_eq ?_)
      simp [hB]
    | succ i ih =>
      intro hi X hX hXN
      have hBi := hB0 i
      set S : ℝ := Dt + (a * B i + F) with hS
      have hshell : ∀ k < L, FBoundP w (fun A => X / 2 ^ (k + 1) < nI A) (X / 2 ^ k) S := by
        intro k _
        set N' := X / 2 ^ k with hN'
        have hpred : (fun A => X / 2 ^ (k + 1) < nI A) = (fun A => N' / 2 < nI A) := by
          funext A; rw [hN', pow_succ, div_div]
        rw [hpred]
        have hN'X : N' ≤ X ∨ X < 0 := by
          rcases le_or_gt 0 X with h | h
          · left; exact div_le_self h (one_le_pow₀ (by norm_num))
          · right; exact h
        rcases le_or_gt N' (2 * g0) with h1 | h1
        · exact (FBoundP.of_fBound _ (htriv N' h1)).mono (by linarith [mul_nonneg ha hBi])
        · have hXpos : N' ≤ X := by
            rcases hN'X with h | h
            · exact h
            · exfalso
              have : N' < 0 := div_neg_of_neg_of_pos h (by positivity)
              linarith
          have hN'N : N' ≤ N := hXpos.trans hXN
          have hlev : N' / g0 ≤ g0 ^ i := by
            rw [div_le_iff₀ hg0p, ← pow_succ]; exact hXpos.trans hX
          have hlevN : N' / g0 ≤ N := (div_le_self (by linarith) hg0).trans hN'N
          have := hsh N' h1 hN'N (B i) hBi (ih (by omega) (N' / g0) hlev hlevN)
          exact this.mono (by linarith)
      have hball := fBound_of_shells hw0 hw L (lt_of_le_of_lt hXN hL) hshell
      refine hball.mono le_rfl ?_
      -- `L·S ≤ B(i+1)`
      have hLa : 0 ≤ (L : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
      have hpow : (1 : ℝ) ≤ (L * a + 1) ^ (i + 1) := one_le_pow₀ (by linarith)
      have hpow' : (L : ℝ) * a * (L * a + 1) ^ i ≤ (L * a + 1) ^ (i + 1) := by
        rw [pow_succ]
        have : 0 ≤ ((L : ℝ) * a + 1) ^ i := by positivity
        nlinarith
      have hE : 0 ≤ Dt + i * (L * (Dt + F)) := by positivity
      have hLDF : 0 ≤ (L : ℝ) * (Dt + F) := by positivity
      simp only [hB, hS]
      push_cast
      calc (L : ℝ) * (Dt + (a * ((L * a + 1) ^ i * (Dt + i * (L * (Dt + F)))) + F))
          = L * a * (L * a + 1) ^ i * (Dt + i * (L * (Dt + F))) + L * (Dt + F) := by ring
        _ ≤ (L * a + 1) ^ (i + 1) * (Dt + i * (L * (Dt + F))) +
            (L * a + 1) ^ (i + 1) * (L * (Dt + F)) :=
          add_le_add (mul_le_mul_of_nonneg_right hpow' hE) (le_mul_of_one_le_left hLDF hpow)
        _ = (L * a + 1) ^ (i + 1) * (Dt + (i + 1) * (L * (Dt + F))) := by ring
  exact key r le_rfl N hr le_rfl

/-- `(c·x²·Z/y)^e = c^e·x^{2e}·Z^e·y^{−e}`. -/
theorem rpow_cx2Z_div {c x Z y e : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hZ : 0 ≤ Z) (hy : 0 < y) :
    (c * x ^ 2 * Z / y) ^ e = c ^ e * x ^ (2 * e) * Z ^ e * y ^ (-e) := by
  rw [Real.div_rpow (by positivity) hy.le, Real.mul_rpow (by positivity) hZ,
    Real.mul_rpow hc (by positivity), Real.rpow_neg hy.le, div_eq_mul_inv]
  congr 3
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- **`K^α` in case 1**: for `K = C_K N² Q^ε/M` with `N ≤ M`,
`K^α ≤ C_K^α·Q^{εα}·N^{2α−1}M^{1−α}`. -/
theorem K_rpow_le {CK M N Q ε α : ℝ} (hCK : 0 ≤ CK) (hM : 1 ≤ M) (hN : 1 ≤ N) (hQ : 0 ≤ Q)
    (hNM : N ≤ M) :
    (CK * N ^ 2 * Q ^ ε / M) ^ α ≤ CK ^ α * Q ^ (ε * α) * (N ^ (2 * α - 1) * M ^ (1 - α)) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  rw [rpow_cx2Z_div hCK hN0.le (Real.rpow_nonneg hQ ε) hM0, ← Real.rpow_mul hQ]
  have e1 : N ^ (2 * α) = N ^ (2 * α - 1) * N := by
    rw [← Real.rpow_add_one hN0.ne']; ring_nf
  have e2 : M ^ (-α) = M ^ (1 - α) * M⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hM0]; ring_nf
  rw [e1, e2]
  have hNM' : N * M⁻¹ ≤ 1 := by rw [← div_eq_mul_inv]; exact (div_le_one hM0).2 hNM
  have h0 : 0 ≤ CK ^ α * Q ^ (ε * α) * (N ^ (2 * α - 1) * M ^ (1 - α)) := by positivity
  calc CK ^ α * (N ^ (2 * α - 1) * N) * Q ^ (ε * α) * (M ^ (1 - α) * M⁻¹)
      = CK ^ α * Q ^ (ε * α) * (N ^ (2 * α - 1) * M ^ (1 - α)) * (N * M⁻¹) := by ring
    _ ≤ CK ^ α * Q ^ (ε * α) * (N ^ (2 * α - 1) * M ^ (1 - α)) * 1 :=
        mul_le_mul_of_nonneg_left hNM' h0
    _ = _ := mul_one _

/-- **`√M·K^{α−1/2}`**: for `K = C_K N² Q^ε/M`,
`√M·K^{α−1/2} = C_K^{α−1/2}·Q^{ε(α−1/2)}·N^{2α−1}M^{1−α}`. -/
theorem sqrt_mul_K_rpow {CK M N Q ε α : ℝ} (hCK : 0 ≤ CK) (hM : 0 < M) (hN : 0 ≤ N)
    (hQ : 0 ≤ Q) :
    Real.sqrt M * (CK * N ^ 2 * Q ^ ε / M) ^ (α - 1 / 2) =
      CK ^ (α - 1 / 2) * Q ^ (ε * (α - 1 / 2)) * (N ^ (2 * α - 1) * M ^ (1 - α)) := by
  rw [rpow_cx2Z_div hCK hN (Real.rpow_nonneg hQ ε) hM, ← Real.rpow_mul hQ, Real.sqrt_eq_rpow]
  have e : M ^ (1 / 2 : ℝ) * M ^ (-(α - 1 / 2)) = M ^ (1 - α) := by
    rw [← Real.rpow_add hM]; ring_nf
  have e2 : (2 : ℝ) * (α - 1 / 2) = 2 * α - 1 := by ring
  rw [e2]
  calc M ^ (1 / 2 : ℝ) * (CK ^ (α - 1 / 2) * N ^ (2 * α - 1) * Q ^ (ε * (α - 1 / 2)) *
        M ^ (-(α - 1 / 2)))
      = CK ^ (α - 1 / 2) * Q ^ (ε * (α - 1 / 2)) *
        (N ^ (2 * α - 1) * (M ^ (1 / 2 : ℝ) * M ^ (-(α - 1 / 2)))) := by ring
    _ = _ := by rw [e]

/-- **`M·K₁^α/N'`**: for `K₁ = c₀N'²/M` and `0 < N' ≤ N`, `α ≥ 1/2`,
`M·K₁^α/N' ≤ c₀^α·N^{2α−1}M^{1−α}`. -/
theorem M_K1_rpow_div {c0 M N N' α : ℝ} (hc : 0 ≤ c0) (hM : 0 < M) (hN' : 0 < N')
    (hNN : N' ≤ N) (hα : 1 / 2 ≤ α) :
    M * (c0 * N' ^ 2 / M) ^ α / N' ≤ c0 ^ α * (N ^ (2 * α - 1) * M ^ (1 - α)) := by
  have h := rpow_cx2Z_div (e := α) hc hN'.le zero_le_one hM
  rw [mul_one] at h
  rw [h, Real.one_rpow, mul_one]
  have e1 : N' ^ (2 * α) = N' ^ (2 * α - 1) * N' := by
    rw [← Real.rpow_add_one hN'.ne']; ring_nf
  have e2 : M * M ^ (-α) = M ^ (1 - α) := by
    rw [sub_eq_add_neg, Real.rpow_add hM, Real.rpow_one]
  rw [e1]
  have hle : N' ^ (2 * α - 1) ≤ N ^ (2 * α - 1) :=
    Real.rpow_le_rpow hN'.le hNN (by linarith)
  have hMa : 0 ≤ M ^ (1 - α) := Real.rpow_nonneg hM.le _
  have hca : 0 ≤ c0 ^ α := Real.rpow_nonneg hc _
  calc M * (c0 ^ α * (N' ^ (2 * α - 1) * N') * M ^ (-α)) / N'
      = c0 ^ α * (N' ^ (2 * α - 1) * (M * M ^ (-α))) := by field_simp
    _ = c0 ^ α * (N' ^ (2 * α - 1) * M ^ (1 - α)) := by rw [e2]
    _ ≤ c0 ^ α * (N ^ (2 * α - 1) * M ^ (1 - α)) := by gcongr

/-- Goldmakher and Louvel's size `M + N + N^{2α−1}M^{1−α}`. -/
def sizeE (α M N : ℝ) : ℝ := M + N + N ^ (2 * α - 1) * M ^ (1 - α)

theorem sizeE_ge {α M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    M ≤ sizeE α M N ∧ N ≤ sizeE α M N ∧ N ^ (2 * α - 1) * M ^ (1 - α) ≤ sizeE α M N ∧
      1 ≤ sizeE α M N := by
  have h : 0 ≤ N ^ (2 * α - 1) * M ^ (1 - α) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N) (2 * α - 1)
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ M) (1 - α)
    positivity
  unfold sizeE
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rpow_le_rpow_Q {Q a b : ℝ} (hQ : 1 ≤ Q) (hab : a ≤ b) : Q ^ a ≤ Q ^ b :=
  Real.rpow_le_rpow_of_exponent_le hQ hab

/-- **The main term's size**: `√M·Δ_m ≤ (2/√c₀ + 2^α(1 + C_K^{α−1/2}))·Q^{εα}·E` per piece. -/
theorem sqrtM_bracket_le {M N Q N' g K K₁ α ε CK c0 X : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hQ : Q = M * N) (hα : 1 ≤ α) (hε : 0 ≤ ε) (hc0 : 0 < c0) (hCK : 0 ≤ CK)
    (hK : K = CK * N ^ 2 * Q ^ ε / M) (hg : 1 ≤ g) (hN' : 0 < N') (hX : X = N' / g)
    (hX1 : 1 ≤ X) (hK1 : K₁ = c0 * N' ^ 2 / M) :
    Real.sqrt M * ((Real.sqrt (K₁ / g))⁻¹ * (X + 1) + 2 ^ α * max K 1 ^ (α - 1 / 2)) ≤
      (2 / Real.sqrt c0 + 2 ^ α * (1 + CK ^ (α - 1 / 2))) * Q ^ (ε * α) * sizeE α M N := by
  obtain ⟨hEM, hEN, hEr, hE1⟩ := sizeE_ge (α := α) hM hN
  have hM0 : 0 < M := by linarith
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 ≤ Q := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- the first piece: `√M·√(g/K₁)·(X + 1) ≤ 2M/√c₀`
  have h1 : Real.sqrt M * ((Real.sqrt (K₁ / g))⁻¹ * (X + 1)) ≤ 2 / Real.sqrt c0 * M := by
    have hg0 : 0 < g := by linarith
    have hK10 : 0 < K₁ := by rw [hK1]; positivity
    have hsK : Real.sqrt K₁ = Real.sqrt c0 * N' / Real.sqrt M := by
      rw [hK1, Real.sqrt_div' _ hM0.le, Real.sqrt_mul hc0.le, Real.sqrt_sq hN'.le]
    have hsc : 0 < Real.sqrt c0 := Real.sqrt_pos.2 hc0
    have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
    have hsg : 1 ≤ Real.sqrt g := by rw [Real.one_le_sqrt]; exact hg
    rw [Real.sqrt_div' _ hg0.le, inv_div, hsK, hX]
    have hX2 : N' / g + 1 ≤ 2 * (N' / g) := by rw [hX] at hX1; linarith
    have hmain : Real.sqrt M * (Real.sqrt g / (Real.sqrt c0 * N' / Real.sqrt M) * (2 * (N' / g)))
        = 2 / Real.sqrt c0 * M * (Real.sqrt g / g) := by
      have hMM : M = Real.sqrt M * Real.sqrt M := (Real.mul_self_sqrt hM0.le).symm
      set s := Real.sqrt M with hs
      rw [hMM]
      field_simp
    have hgg : Real.sqrt g / g ≤ 1 := by
      rw [div_le_one hg0]
      calc Real.sqrt g ≤ Real.sqrt g * Real.sqrt g := le_mul_of_one_le_right (by linarith) hsg
        _ = g := Real.mul_self_sqrt hg0.le
    calc Real.sqrt M * (Real.sqrt g / (Real.sqrt c0 * N' / Real.sqrt M) * (N' / g + 1))
        ≤ Real.sqrt M * (Real.sqrt g / (Real.sqrt c0 * N' / Real.sqrt M) * (2 * (N' / g))) := by
          gcongr
      _ = 2 / Real.sqrt c0 * M * (Real.sqrt g / g) := hmain
      _ ≤ 2 / Real.sqrt c0 * M * 1 := by gcongr
      _ = 2 / Real.sqrt c0 * M := mul_one _
  -- the second piece
  have h2 : Real.sqrt M * (2 ^ α * max K 1 ^ (α - 1 / 2)) ≤
      2 ^ α * (1 + CK ^ (α - 1 / 2)) * Q ^ (ε * α) * sizeE α M N := by
    have hmx : max K 1 ^ (α - 1 / 2) ≤ 1 + K ^ (α - 1 / 2) := by
      rcases le_total K 1 with h | h
      · rw [max_eq_right h, Real.one_rpow]
        have := Real.rpow_nonneg hK0 (α - 1 / 2); linarith
      · rw [max_eq_left h]; linarith
    have hsq := sqrt_mul_K_rpow (α := α) hCK hM0 (by linarith : (0 : ℝ) ≤ N) hQ0 (ε := ε)
    rw [← hK] at hsq
    have hsM : Real.sqrt M ≤ M := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hQe : Q ^ (ε * (α - 1 / 2)) ≤ Q ^ (ε * α) :=
      rpow_le_rpow_Q hQ1 (by nlinarith)
    have hQe1 : 1 ≤ Q ^ (ε * α) := Real.one_le_rpow hQ1 (by positivity)
    have hCKp : 0 ≤ CK ^ (α - 1 / 2) := Real.rpow_nonneg hCK _
    have h2a : (0 : ℝ) ≤ 2 ^ α := by positivity
    have hr0 : 0 ≤ N ^ (2 * α - 1) * M ^ (1 - α) := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N) (2 * α - 1)
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ M) (1 - α)
      positivity
    have hE0 : 0 ≤ sizeE α M N := by linarith
    calc Real.sqrt M * (2 ^ α * max K 1 ^ (α - 1 / 2))
        ≤ 2 ^ α * (Real.sqrt M * (1 + K ^ (α - 1 / 2))) := by
          rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmx (Real.sqrt_nonneg _)) h2a
      _ = 2 ^ α * (Real.sqrt M + CK ^ (α - 1 / 2) * Q ^ (ε * (α - 1 / 2)) *
            (N ^ (2 * α - 1) * M ^ (1 - α))) := by rw [mul_add, mul_one, hsq]
      _ ≤ 2 ^ α * (Q ^ (ε * α) * sizeE α M N + CK ^ (α - 1 / 2) * Q ^ (ε * α) *
            sizeE α M N) := by
          gcongr
          · calc Real.sqrt M ≤ M := hsM
              _ ≤ sizeE α M N := hEM
              _ ≤ Q ^ (ε * α) * sizeE α M N := le_mul_of_one_le_left hE0 hQe1
      _ = _ := by ring
  have hQe1 : 1 ≤ Q ^ (ε * α) := Real.one_le_rpow hQ1 (by positivity)
  have hE0 : 0 ≤ sizeE α M N := by linarith
  have h1' : 2 / Real.sqrt c0 * M ≤ 2 / Real.sqrt c0 * Q ^ (ε * α) * sizeE α M N := by
    have : 0 ≤ 2 / Real.sqrt c0 := by positivity
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hEM.trans (le_mul_of_one_le_left hE0 hQe1)) this
  rw [mul_add]
  calc _ ≤ 2 / Real.sqrt c0 * M + 2 ^ α * (1 + CK ^ (α - 1 / 2)) * Q ^ (ε * α) * sizeE α M N :=
        add_le_add h1 h2
    _ ≤ 2 / Real.sqrt c0 * Q ^ (ε * α) * sizeE α M N +
        2 ^ α * (1 + CK ^ (α - 1 / 2)) * Q ^ (ε * α) * sizeE α M N := add_le_add h1' le_rfl
    _ = _ := by ring

theorem max_one_rpow_le {Y a : ℝ} (hY : 0 ≤ Y) : max Y 1 ^ a ≤ 1 + Y ^ a := by
  rcases le_total Y 1 with h | h
  · rw [max_eq_right h, Real.one_rpow]; have := Real.rpow_nonneg hY a; linarith
  · rw [max_eq_left h]; linarith

/-- **`Σ_3`'s error size**: on a shell, `(2M/√3)(4MK₁/3)^{ε/2}·(X·max(K₁, 1))^ε(X + max(K₁, 1)^α)/X_lo
  ≤ (2/√3)2^ε(3 + 2c₀^α)·Q^{2ε}·g₀·E`. -/
theorem err3_size_le {M N Q N' g g0 K₁ X Xlo α ε c0 : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hQ : Q = M * N) (hα : 1 ≤ α) (hε : 0 ≤ ε) (hc0 : 0 ≤ c0) (hg : 1 ≤ g) (hgg0 : g ≤ g0)
    (h2g : 2 * g ≤ N') (hN'N : N' ≤ N) (hX : X = N' / g) (hXlo : Xlo = N' / (2 * g))
    (hK1 : K₁ = c0 * N' ^ 2 / M) (hK1M : K₁ ≤ M) :
    2 * M / Real.sqrt 3 * (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) *
        ((X * max K₁ 1) ^ ε * (X + max K₁ 1 ^ α)) / Xlo ≤
      2 / Real.sqrt 3 * 2 ^ ε * (3 + 2 * c0 ^ α) * Q ^ (2 * ε) * g0 * sizeE α M N := by
  obtain ⟨hEM, hEN, hEr, hE1⟩ := sizeE_ge (α := α) hM hN
  have hM0 : 0 < M := by linarith
  have hg0' : 0 < g := by linarith
  have hN'0 : 0 < N' := by linarith
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 ≤ Q := by linarith
  have hK10 : 0 ≤ K₁ := by rw [hK1]; positivity
  have hX1 : 1 ≤ X := by rw [hX, le_div_iff₀ hg0']; linarith
  have hXN : X ≤ N := by
    rw [hX, div_le_iff₀ hg0']; nlinarith
  -- the powers
  have hp1 : Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε ≤ 2 ^ ε * Q ^ ε := by
    rw [← Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      ← Real.mul_rpow (by norm_num) hQ0]
    refine Real.rpow_le_rpow (by positivity) ?_ hε
    rw [← Real.sqrt_mul (by positivity)]
    have : 4 * M / 3 * K₁ ≤ (2 * Q) ^ 2 := by
      have : M ≤ Q := by rw [hQ]; nlinarith
      nlinarith
    calc Real.sqrt (4 * M / 3 * K₁) ≤ Real.sqrt ((2 * Q) ^ 2) := Real.sqrt_le_sqrt this
      _ = 2 * Q := Real.sqrt_sq (by linarith)
  have hp2 : (X * max K₁ 1) ^ ε ≤ Q ^ ε := by
    refine Real.rpow_le_rpow (by positivity) ?_ hε
    rw [hQ]
    have : max K₁ 1 ≤ M := max_le hK1M hM
    calc X * max K₁ 1 ≤ N * M := mul_le_mul hXN this (by positivity) (by linarith)
      _ = M * N := mul_comm _ _
  -- the bracket
  have hbr : M * (X + max K₁ 1 ^ α) / Xlo ≤ (3 + 2 * c0 ^ α) * g0 * sizeE α M N := by
    have hmx := max_one_rpow_le (a := α) hK10
    have hXlo0 : 0 < Xlo := by rw [hXlo]; positivity
    have hk := M_K1_rpow_div (α := α) hc0 hM0 hN'0 hN'N (by linarith)
    rw [← hK1] at hk
    have hg1 : 1 ≤ g0 := hg.trans hgg0
    have hE0 : 0 ≤ sizeE α M N := by linarith
    have hca : 0 ≤ c0 ^ α := Real.rpow_nonneg hc0 _
    have e : M * (X + max K₁ 1 ^ α) / Xlo =
        2 * M + 2 * g * M * max K₁ 1 ^ α / N' := by
      rw [hX, hXlo]; field_simp
    rw [e]
    have h1 : 2 * g * M * max K₁ 1 ^ α / N' ≤ 2 * g * M * (1 + K₁ ^ α) / N' := by gcongr
    have h2 : 2 * g * M * (1 + K₁ ^ α) / N' = 2 * g * M / N' + 2 * g * (M * K₁ ^ α / N') := by
      ring
    have h3 : 2 * g * M / N' ≤ M := by
      rw [div_le_iff₀ hN'0]; nlinarith
    have h4 : 2 * g * (M * K₁ ^ α / N') ≤ 2 * g0 * (c0 ^ α * sizeE α M N) := by
      have : M * K₁ ^ α / N' ≤ c0 ^ α * sizeE α M N :=
        hk.trans (mul_le_mul_of_nonneg_left hEr hca)
      have h0 : 0 ≤ M * K₁ ^ α / N' := by positivity
      exact mul_le_mul (by linarith) this h0 (by linarith)
    nlinarith
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hXlo0 : 0 < Xlo := by rw [hXlo]; positivity
  have hQε : 0 ≤ Q ^ ε := Real.rpow_nonneg hQ0 ε
  have hA0 : 0 ≤ X + max K₁ 1 ^ α := by
    have := Real.rpow_nonneg (le_trans zero_le_one (le_max_right K₁ 1)) α; linarith
  calc 2 * M / Real.sqrt 3 * (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) *
        ((X * max K₁ 1) ^ ε * (X + max K₁ 1 ^ α)) / Xlo
      = 2 / Real.sqrt 3 * (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) *
        (X * max K₁ 1) ^ ε * (M * (X + max K₁ 1 ^ α) / Xlo) := by ring
    _ ≤ 2 / Real.sqrt 3 * (2 ^ ε * Q ^ ε) * Q ^ ε * ((3 + 2 * c0 ^ α) * g0 * sizeE α M N) := by
        gcongr
    _ = 2 / Real.sqrt 3 * 2 ^ ε * (3 + 2 * c0 ^ α) * (Q ^ ε * Q ^ ε) * g0 * sizeE α M N := by
        ring
    _ = _ := by
        rw [← Real.rpow_add (by linarith : (0 : ℝ) < Q)]; ring_nf

/-- **`Σ_4`'s error size**: `(X·max(K, 1))^ε(X + max(K, 1)^α) ≤ (2 + C_K^α)·Q^{ε + εα}·E`. -/
theorem err4_size_le {M N Q K X α ε CK : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hQ : Q = M * N)
    (hα : 1 ≤ α) (hε : 0 ≤ ε) (hCK : 0 ≤ CK) (hK : K = CK * N ^ 2 * Q ^ ε / M) (hKM : K ≤ M)
    (hNM : N ≤ M) (hX1 : 1 ≤ X) (hXN : X ≤ N) :
    (X * max K 1) ^ ε * (X + max K 1 ^ α) ≤ (2 + CK ^ α) * Q ^ (ε + ε * α) * sizeE α M N := by
  obtain ⟨hEM, hEN, hEr, hE1⟩ := sizeE_ge (α := α) hM hN
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 ≤ Q := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; have := Real.rpow_nonneg hQ0 ε; positivity
  have hp : (X * max K 1) ^ ε ≤ Q ^ ε := by
    refine Real.rpow_le_rpow (by positivity) ?_ hε
    rw [hQ]
    calc X * max K 1 ≤ N * M := mul_le_mul hXN (max_le hKM hM) (by positivity) (by linarith)
      _ = M * N := mul_comm _ _
  have hKa := K_rpow_le (α := α) hCK hM hN hQ0 hNM (ε := ε)
  rw [← hK] at hKa
  have hmx := max_one_rpow_le (a := α) hK0
  have hQe1 : 1 ≤ Q ^ (ε * α) := Real.one_le_rpow hQ1 (by positivity)
  have hCKa : 0 ≤ CK ^ α := Real.rpow_nonneg hCK _
  have hE0 : 0 ≤ sizeE α M N := by linarith
  have hin : X + max K 1 ^ α ≤ (2 + CK ^ α) * Q ^ (ε * α) * sizeE α M N := by
    have h1 : X + max K 1 ^ α ≤ N + 1 + CK ^ α * Q ^ (ε * α) * (N ^ (2 * α - 1) * M ^ (1 - α)) := by
      linarith
    have h2 : N + 1 + CK ^ α * Q ^ (ε * α) * (N ^ (2 * α - 1) * M ^ (1 - α)) ≤
        Q ^ (ε * α) * sizeE α M N + Q ^ (ε * α) * sizeE α M N +
          CK ^ α * Q ^ (ε * α) * sizeE α M N := by
      have a1 : N ≤ Q ^ (ε * α) * sizeE α M N := hEN.trans (le_mul_of_one_le_left hE0 hQe1)
      have a2 : 1 ≤ Q ^ (ε * α) * sizeE α M N := hE1.trans (le_mul_of_one_le_left hE0 hQe1)
      have a3 : CK ^ α * Q ^ (ε * α) * (N ^ (2 * α - 1) * M ^ (1 - α)) ≤
          CK ^ α * Q ^ (ε * α) * sizeE α M N :=
        mul_le_mul_of_nonneg_left hEr (by positivity)
      linarith
    linarith
  have hA0 : 0 ≤ X + max K 1 ^ α := by
    have := Real.rpow_nonneg (le_trans zero_le_one (le_max_right K 1)) α; linarith
  calc (X * max K 1) ^ ε * (X + max K 1 ^ α)
      ≤ Q ^ ε * ((2 + CK ^ α) * Q ^ (ε * α) * sizeE α M N) :=
        mul_le_mul hp hin hA0 (Real.rpow_nonneg hQ0 ε)
    _ = (2 + CK ^ α) * (Q ^ ε * Q ^ (ε * α)) * sizeE α M N := by ring
    _ = _ := by rw [← Real.rpow_add (by linarith : (0 : ℝ) < Q)]

end Eis

end

#print axioms Eis.fBoundP_gcd
#print axioms Eis.fBound_of_shells
#print axioms Eis.fBound_triv
#print axioms Eis.nat_le_rpow_of_two_pow_le
#print axioms Eis.sqfW_mono
#print axioms Eis.fBound_sqfW_of_qExp
#print axioms Eis.fBound_wR_of_qExp
#print axioms Eis.FBoundP.of_fBound
#print axioms Eis.FBoundP.mono
#print axioms Eis.card_fsLe_mono
#print axioms Eis.fBound_rec
#print axioms Eis.rpow_cx2Z_div
#print axioms Eis.K_rpow_le
#print axioms Eis.sqrt_mul_K_rpow
#print axioms Eis.M_K1_rpow_div
#print axioms Eis.sizeE_ge
#print axioms Eis.rpow_le_rpow_Q
#print axioms Eis.sqrtM_bracket_le
#print axioms Eis.max_one_rpow_le
#print axioms Eis.err3_size_le
#print axioms Eis.err4_size_le
