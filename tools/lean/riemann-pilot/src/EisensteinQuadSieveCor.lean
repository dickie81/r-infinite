import EisensteinQuadSieveRecursion

/-! # The quadratic large sieve, part 7d: Goldmakher and Louvel's Theorem cor (round 358)

S5e of round 312's plan, the fourth piece of S5e-7: round 356's bound for one gcd part, fed with
the norms of the rows from `(E_α)` (round 357), gives the shell hypothesis of round 357's
recursion, and the recursion gives Goldmakher and Louvel's Theorem cor.

* **The column factor and the shell facts** (`eulB_le`, `colP_le`, `four_pow_le_Q`, `sieveCK`,
  `one_le_sieveCK`, `c0_le_sieveCK`, `shell_facts`, `shellJ_le`, `XK_le`, `bracket_le`).
* **The shell bound for one gcd part** (`gcdPart_shell_le`): for `(E_α)` with `α ≥ 1`,
  `K = C_K N²(MN)^ε/M ≤ M`, a shell `N'/2 < N(A) ≤ N'` with `2g₀ < N' ≤ N` and `N(G) ≤ g₀`,
  `Re gcdPart ≤ A·(MN)^{5δ+4ε+εα}·g₀·E·Σ|α(A)|²`, with `E = M + N + N^{2α−1}M^{1−α}`.
* **The rows of `B(M, N, K)`** (`admW_mono`, `bw_le_re`, `tsum_bw_le`, `N_le_M_of_K_le`,
  `combine_rec`, `fBound_bw_le`): `Σ_m w(m) ≤ (2M + 49R²)B` by round 345's `norm_pS_diag`, and
  round 357's `fBound_rec` with `g₀ = N^{1/r}` bounds the norm of `B(M, N, K)` at `N`.
* **Theorem cor** (`fBound_cor`, with `case2_le`): `(E_α)` with `α ≥ 1` gives, for every
  `ε > 0`, `FBound (admW M) N (C·(MN)^ε·(M + N + N^{2α−1}M^{1−α}))`.
-/

open Complex NumberField Ideal
open scoped Classical

noncomputable section

namespace Eis

theorem eulB_le {ε : ℝ} (hε : 0 ≤ ε) (B : Finset Pr) :
    ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) ≤ 2 ^ B.card * nI B ^ ε := by
  have h1 : ∀ Q ∈ B, 1 + (absNorm Q.1 : ℝ) ^ ε ≤ 2 * (absNorm Q.1 : ℝ) ^ ε := fun Q _ => by
    have : (1 : ℝ) ≤ (absNorm Q.1 : ℝ) ^ ε :=
      Real.one_le_rpow (by exact_mod_cast one_le_absNorm_Pr Q) hε
    linarith
  calc ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) ≤ ∏ Q ∈ B, (2 * (absNorm Q.1 : ℝ) ^ ε) :=
        Finset.prod_le_prod₀ (fun Q _ => by positivity) h1
    _ = 2 ^ B.card * nI B ^ ε := by
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Real.finsetProd_rpow _ _ (fun Q _ => Nat.cast_nonneg _), nI_eq_prod]

/-- **The column factor** `2^{|B|}Π_B² ≤ C₄²N^{2δ+2ε}` for `N(B) ≤ N`, with `C₄` from
`4^{|B|} ≤ C₄N(B)^δ`. -/
theorem colP_le {ε δ C4 N : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (h4 : ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ C4 * nI b ^ δ) (B : Finset Pr) (hB : nI B ≤ N) :
    (2 : ℝ) ^ B.card * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 ≤
      C4 ^ 2 * N ^ (2 * δ + 2 * ε) := by
  have hn := nI_pos B
  have hP0 : 0 ≤ ∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε) :=
    le_trans zero_le_one (one_le_eulB ε B)
  have h1 := eulB_le hε B
  have hb := h4 B
  have h40 : (0 : ℝ) ≤ 4 ^ B.card := by positivity
  calc (2 : ℝ) ^ B.card * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2
      ≤ 2 ^ B.card * (2 ^ B.card * nI B ^ ε) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 h1 2) (by positivity)
    _ = 2 ^ B.card * 4 ^ B.card * (nI B ^ ε) ^ 2 := by
        rw [mul_pow, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
    _ ≤ (4 ^ B.card) ^ 2 * (nI B ^ ε) ^ 2 := by
        have : (2 : ℝ) ^ B.card ≤ 4 ^ B.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have h0 : 0 ≤ (nI B ^ ε) ^ 2 := sq_nonneg _
        rw [sq (4 ^ B.card : ℝ)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this h40) h0
    _ ≤ (C4 * nI B ^ δ) ^ 2 * (nI B ^ ε) ^ 2 := by gcongr
    _ = C4 ^ 2 * nI B ^ (2 * δ + 2 * ε) := by
        have e1 : (nI B ^ δ) ^ 2 = nI B ^ (2 * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; ring_nf
        have e2 : (nI B ^ ε) ^ 2 = nI B ^ (2 * ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; ring_nf
        rw [Real.rpow_add hn, ← e1, ← e2]; ring
    _ ≤ C4 ^ 2 * N ^ (2 * δ + 2 * ε) := by gcongr

/-- The constant `C_K = max(1, 3R²/4)` of `K = C_K N²(MN)^ε/M`. -/
def sieveCK : ℝ := max 1 (3 * RΦ ^ 2 / 4)

theorem one_le_sieveCK : 1 ≤ sieveCK := le_max_left _ _

theorem c0_le_sieveCK : 3 * RΦ ^ 2 / 4 ≤ sieveCK := le_max_right _ _

theorem four_pow_le_Q {C4 δ Q : ℝ} (hδ : 0 ≤ δ)
    (h4 : ∀ b : Finset Pr, (4 : ℝ) ^ b.card ≤ C4 * nI b ^ δ) {G : Finset Pr} (hG : nI G ≤ Q) :
    (4 : ℝ) ^ G.card ≤ C4 * Q ^ δ := by
  have h := h4 G
  have hC : 0 ≤ C4 := by
    have : (0 : ℝ) < 4 ^ G.card := by positivity
    have : 0 < nI G ^ δ := Real.rpow_pos_of_pos (nI_pos G) δ
    by_contra hc; push Not at hc; nlinarith
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (nI_pos G).le hG hδ) hC)

/-- The elementary facts on a shell. -/
theorem shell_facts {M N g0 N' g ε c0 CK : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hc0 : 0 < c0)
    (hcK1 : 1 ≤ CK) (hc0K : c0 ≤ CK) (hKM : CK * N ^ 2 * (M * N) ^ ε / M ≤ M) (hε : 0 ≤ ε)
    (hN'g : 2 * g0 < N') (hN'N : N' ≤ N) (hg1 : 1 ≤ g) (hgg0 : g ≤ g0) :
    N ≤ M ∧ c0 * N' ^ 2 / M ≤ CK * N ^ 2 * (M * N) ^ ε / M ∧ 1 ≤ N' / g ∧ N' / g ≤ N ∧
      1 < N' / (2 * g) ∧ 2 * g ≤ N' ∧ 0 < N' ∧ g ≤ M * N ∧
      4 * c0 * (N' / g) ^ 2 * g ≤ 4 * M * (c0 * N' ^ 2 / M) ∧ 1 ≤ M * N := by
  have hM0 : 0 < M := by linarith
  have hg0' : 0 < g := by linarith
  have hQ1 : 1 ≤ M * N := by nlinarith
  have hQe1 : 1 ≤ (M * N) ^ ε := Real.one_le_rpow hQ1 hε
  have h2g : 2 * g ≤ N' := by linarith
  have hN'0 : 0 < N' := by linarith
  have hNM : N ≤ M := by
    have h1 : CK * N ^ 2 * (M * N) ^ ε ≤ M ^ 2 := by
      have := hKM; rw [div_le_iff₀ hM0] at this; nlinarith
    have h2 : N ^ 2 ≤ CK * N ^ 2 * (M * N) ^ ε := by
      have : 0 ≤ N ^ 2 := sq_nonneg _
      calc N ^ 2 = 1 * N ^ 2 * 1 := by ring
        _ ≤ CK * N ^ 2 * (M * N) ^ ε := by gcongr
    nlinarith
  have hK1K : c0 * N' ^ 2 / M ≤ CK * N ^ 2 * (M * N) ^ ε / M := by
    apply div_le_div_of_nonneg_right _ hM0.le
    have : N' ^ 2 ≤ N ^ 2 := by nlinarith
    have h1 : c0 * N' ^ 2 ≤ CK * N ^ 2 := mul_le_mul hc0K this (sq_nonneg _) (by linarith)
    calc c0 * N' ^ 2 ≤ CK * N ^ 2 * 1 := by rw [mul_one]; exact h1
      _ ≤ CK * N ^ 2 * (M * N) ^ ε := by gcongr
  have hX1 : 1 ≤ N' / g := by rw [le_div_iff₀ hg0']; linarith
  have hXN : N' / g ≤ N := by rw [div_le_iff₀ hg0']; nlinarith
  have hXlo1 : 1 < N' / (2 * g) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hgQ : g ≤ M * N := by nlinarith
  have hcond : 4 * c0 * (N' / g) ^ 2 * g ≤ 4 * M * (c0 * N' ^ 2 / M) := by
    have e : 4 * M * (c0 * N' ^ 2 / M) = 4 * c0 * N' ^ 2 := by field_simp
    rw [e, div_pow]
    have : N' ^ 2 / g ^ 2 * g ≤ N' ^ 2 := by
      rw [sq g, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg N')
    calc 4 * c0 * (N' ^ 2 / g ^ 2) * g = 4 * c0 * (N' ^ 2 / g ^ 2 * g) := by ring
      _ ≤ 4 * c0 * N' ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
  exact ⟨hNM, hK1K, hX1, hXN, hXlo1, h2g, hN'0, hgQ, hcond, hQ1⟩

/-- The count of round 355's dyadic pieces on a shell. -/
theorem shellJ_le {M N Q N' g K K₁ c0 δ : ℝ} (hM : 1 ≤ M) (hQ : Q = M * N) (hQ1 : 1 ≤ Q)
    (hKM : K ≤ M) (hc0 : 0 < c0) (hg1 : 1 ≤ g) (hgN : g ≤ N) (hN' : 1 ≤ N')
    (hK1 : K₁ = c0 * N' ^ 2 / M) (hδ : 0 < δ) (hY : K₁ / g ≤ K) :
    1 + (K / (K₁ / g)) ^ δ / (δ * Real.log 2) ≤
      (1 + c0⁻¹ ^ δ / (δ * Real.log 2)) * Q ^ (2 * δ) := by
  have hM0 : 0 < M := by linarith
  have hg0' : 0 < g := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hY₁ : 0 < K₁ / g := by rw [hK1]; positivity
  have hKr : K / (K₁ / g) ≤ Q ^ 2 * c0⁻¹ := by
    rw [div_le_iff₀ hY₁]
    have e : Q ^ 2 * c0⁻¹ * (K₁ / g) = M * N ^ 2 * N' ^ 2 / g := by
      rw [hK1, hQ]; field_simp
    rw [e]
    have hN1 : 1 ≤ N := hg1.trans hgN
    have h1 : 1 ≤ N ^ 2 * N' ^ 2 / g := by
      rw [le_div_iff₀ hg0']
      have : 1 ≤ N' ^ 2 := by nlinarith
      nlinarith
    calc K ≤ M := hKM
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * (N ^ 2 * N' ^ 2 / g) := mul_le_mul_of_nonneg_left h1 hM0.le
      _ = M * N ^ 2 * N' ^ 2 / g := by ring
  have hp : (K / (K₁ / g)) ^ δ ≤ Q ^ (2 * δ) * c0⁻¹ ^ δ := by
    calc (K / (K₁ / g)) ^ δ ≤ (Q ^ 2 * c0⁻¹) ^ δ :=
          Real.rpow_le_rpow (div_nonneg (hY₁.le.trans hY) hY₁.le) hKr hδ.le
      _ = Q ^ (2 * δ) * c0⁻¹ ^ δ := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (by linarith)]; norm_num
  have hQ2 : 1 ≤ Q ^ (2 * δ) := Real.one_le_rpow hQ1 (by positivity)
  have hdl : 0 < δ * Real.log 2 := mul_pos hδ hl2
  have h3 : (K / (K₁ / g)) ^ δ / (δ * Real.log 2) ≤
      Q ^ (2 * δ) * (c0⁻¹ ^ δ / (δ * Real.log 2)) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hp hdl.le
  have h0 : 0 ≤ c0⁻¹ ^ δ / (δ * Real.log 2) := by
    have := Real.rpow_nonneg (inv_nonneg.2 hc0.le) δ; positivity
  calc 1 + (K / (K₁ / g)) ^ δ / (δ * Real.log 2)
      ≤ Q ^ (2 * δ) + Q ^ (2 * δ) * (c0⁻¹ ^ δ / (δ * Real.log 2)) := add_le_add hQ2 h3
    _ = _ := by ring

theorem XK_le {M N Q X K ε : ℝ} (hM : 1 ≤ M) (hQ : Q = M * N) (hX0 : 0 ≤ X) (hXN : X ≤ N)
    (hKM : K ≤ M) (hε : 0 ≤ ε) : (X * max (2 * K) 1) ^ ε ≤ 2 ^ ε * Q ^ ε := by
  have hQ0 : 0 ≤ Q := by rw [hQ]; nlinarith
  rw [← Real.mul_rpow (by norm_num) hQ0]
  refine Real.rpow_le_rpow (by positivity) ?_ hε
  have : max (2 * K) 1 ≤ 2 * M := max_le (by linarith) (by linarith)
  calc X * max (2 * K) 1 ≤ N * (2 * M) := mul_le_mul hXN this (by positivity) (by linarith)
    _ = 2 * Q := by rw [hQ]; ring

/-- **The bracket of round 356, combined**: abstract factors with their bounds. -/
theorem bracket_le {c t4 J Cw xk sb t2 C3 Cs e3 C4 pg e4 P C₄ Q δ ε α g0 E cj A₁ k3 k4 : ℝ}
    (hc : 0 ≤ c) (hCw : 0 ≤ Cw) (hC3 : 0 ≤ C3) (hCs : 0 ≤ Cs) (hC4 : 0 ≤ C4) (hC₄ : 0 ≤ C₄)
    (hQ1 : 1 ≤ Q) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hα : 0 ≤ α) (hg0 : 1 ≤ g0) (hE : 0 ≤ E)
    (hJ : 0 ≤ J) (hxk : 0 ≤ xk) (hsb : 0 ≤ sb) (he3 : 0 ≤ e3)
    (he4 : 0 ≤ e4) (hP : 0 ≤ P) (hcj : 0 ≤ cj) (hA₁ : 0 ≤ A₁) (hk3 : 0 ≤ k3)
    (hk4 : 0 ≤ k4)
    (bt4 : t4 ≤ C₄ * Q ^ δ) (bJ : J ≤ cj * Q ^ (2 * δ)) (bxk : xk ≤ 2 ^ ε * Q ^ ε)
    (bsb : sb ≤ A₁ * Q ^ (ε * α) * E) (bt2 : t2 ≤ C₄ * Q ^ δ)
    (be3 : e3 ≤ k3 * Q ^ (2 * ε) * g0 * E) (bpg : pg ≤ C₄ * Q ^ (δ + ε))
    (be4 : e4 ≤ k4 * Q ^ (ε + ε * α) * E) (bP : P ≤ C₄ ^ 2 * Q ^ (2 * δ + 2 * ε)) :
    (c * t4 * J * Cw * xk * sb + t2 * C3 * Cs * e3 + C4 * pg * Cs * e4) * P ≤
      ((c * C₄ * cj * Cw * 2 ^ ε * A₁ + C₄ * C3 * Cs * k3 + C4 * C₄ * Cs * k4) * C₄ ^ 2) *
        Q ^ (5 * δ + 4 * ε + ε * α) * g0 * E := by
  have hQ0 : 0 < Q := by linarith
  set θ := 5 * δ + 4 * ε + ε * α with hθ
  have hQθ : 0 ≤ Q ^ θ := Real.rpow_nonneg hQ0.le _
  have pw : ∀ x y : ℝ, Q ^ x * Q ^ y = Q ^ (x + y) := fun x y => (Real.rpow_add hQ0 x y).symm
  have le : ∀ x : ℝ, x ≤ θ → Q ^ x ≤ Q ^ θ := fun x h => Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hEg : E ≤ g0 * E := le_mul_of_one_le_left hE hg0
  -- the first term
  have h1 : c * t4 * J * Cw * xk * sb ≤
      c * C₄ * cj * Cw * 2 ^ ε * A₁ * Q ^ (3 * δ + ε + ε * α) * E := by
    calc c * t4 * J * Cw * xk * sb
        ≤ c * (C₄ * Q ^ δ) * (cj * Q ^ (2 * δ)) * Cw * (2 ^ ε * Q ^ ε) *
            (A₁ * Q ^ (ε * α) * E) := by gcongr
      _ = c * C₄ * cj * Cw * 2 ^ ε * A₁ * (Q ^ δ * Q ^ (2 * δ) * Q ^ ε * Q ^ (ε * α)) * E := by
          ring
      _ = _ := by rw [pw, pw, pw]; ring_nf
  have h2 : t2 * C3 * Cs * e3 ≤ C₄ * C3 * Cs * k3 * Q ^ (δ + 2 * ε) * g0 * E := by
    calc t2 * C3 * Cs * e3 ≤ (C₄ * Q ^ δ) * C3 * Cs * (k3 * Q ^ (2 * ε) * g0 * E) := by gcongr
      _ = C₄ * C3 * Cs * k3 * (Q ^ δ * Q ^ (2 * ε)) * g0 * E := by ring
      _ = _ := by rw [pw]
  have h3 : C4 * pg * Cs * e4 ≤ C4 * C₄ * Cs * k4 * Q ^ (δ + 2 * ε + ε * α) * E := by
    calc C4 * pg * Cs * e4 ≤ C4 * (C₄ * Q ^ (δ + ε)) * Cs * (k4 * Q ^ (ε + ε * α) * E) := by
          gcongr
      _ = C4 * C₄ * Cs * k4 * (Q ^ (δ + ε) * Q ^ (ε + ε * α)) * E := by ring
      _ = _ := by rw [pw]; ring_nf
  set K1 := c * C₄ * cj * Cw * 2 ^ ε * A₁ with hK1
  set K2 := C₄ * C3 * Cs * k3 with hK2
  set K3 := C4 * C₄ * Cs * k4 with hK3
  have hK1' : 0 ≤ K1 := by positivity
  have hK2' : 0 ≤ K2 := by positivity
  have hK3' : 0 ≤ K3 := by positivity
  have hsum : c * t4 * J * Cw * xk * sb + t2 * C3 * Cs * e3 + C4 * pg * Cs * e4 ≤
      (K1 + K2 + K3) * Q ^ (3 * δ + 2 * ε + ε * α) * g0 * E := by
    have a1 : K1 * Q ^ (3 * δ + ε + ε * α) * E ≤ K1 * Q ^ (3 * δ + 2 * ε + ε * α) * g0 * E := by
      have := Real.rpow_le_rpow_of_exponent_le hQ1 (show 3 * δ + ε + ε * α ≤
        3 * δ + 2 * ε + ε * α by linarith)
      calc K1 * Q ^ (3 * δ + ε + ε * α) * E ≤ K1 * Q ^ (3 * δ + 2 * ε + ε * α) * E := by gcongr
        _ ≤ K1 * Q ^ (3 * δ + 2 * ε + ε * α) * (g0 * E) := by gcongr
        _ = _ := by ring
    have a2 : K2 * Q ^ (δ + 2 * ε) * g0 * E ≤ K2 * Q ^ (3 * δ + 2 * ε + ε * α) * g0 * E := by
      have := Real.rpow_le_rpow_of_exponent_le hQ1 (show δ + 2 * ε ≤
        3 * δ + 2 * ε + ε * α by nlinarith)
      gcongr
    have a3 : K3 * Q ^ (δ + 2 * ε + ε * α) * E ≤ K3 * Q ^ (3 * δ + 2 * ε + ε * α) * g0 * E := by
      have := Real.rpow_le_rpow_of_exponent_le hQ1 (show δ + 2 * ε + ε * α ≤
        3 * δ + 2 * ε + ε * α by linarith)
      calc K3 * Q ^ (δ + 2 * ε + ε * α) * E ≤ K3 * Q ^ (3 * δ + 2 * ε + ε * α) * E := by gcongr
        _ ≤ K3 * Q ^ (3 * δ + 2 * ε + ε * α) * (g0 * E) := by gcongr
        _ = _ := by ring
    calc _ ≤ K1 * Q ^ (3 * δ + ε + ε * α) * E + K2 * Q ^ (δ + 2 * ε) * g0 * E +
          K3 * Q ^ (δ + 2 * ε + ε * α) * E := add_le_add (add_le_add h1 h2) h3
      _ ≤ _ := by linarith
  have hS0 : 0 ≤ (K1 + K2 + K3) * Q ^ (3 * δ + 2 * ε + ε * α) * g0 * E := by positivity
  calc (c * t4 * J * Cw * xk * sb + t2 * C3 * Cs * e3 + C4 * pg * Cs * e4) * P
      ≤ ((K1 + K2 + K3) * Q ^ (3 * δ + 2 * ε + ε * α) * g0 * E) *
          (C₄ ^ 2 * Q ^ (2 * δ + 2 * ε)) := by
        apply mul_le_mul hsum bP hP hS0
    _ = (K1 + K2 + K3) * C₄ ^ 2 * (Q ^ (3 * δ + 2 * ε + ε * α) * Q ^ (2 * δ + 2 * ε)) * g0 * E := by
        ring
    _ = _ := by
        rw [pw, show 3 * δ + 2 * ε + ε * α + (2 * δ + 2 * ε) = θ by rw [hθ]; ring]

set_option maxHeartbeats 800000 in
/-- **The shell bound for one gcd part**: for `(E_α)` with `α ≥ 1`, rows of `B(M, N, K)` with
`K = C_K N²(MN)^ε/M ≤ M`, a shell `N'/2 < N(A) ≤ N'` with `2g₀ < N' ≤ N`, and `N(G) ≤ g₀`,
`Re gcdPart ≤ A·(MN)^{5δ+4ε+εα}·g₀·E·Σ|α(A)|²`. -/
theorem gcdPart_shell_le {α : ℝ} (hα : 1 ≤ α) (hE : QExp α) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (M N g0 N' : ℝ), 1 ≤ M → 1 ≤ N →
      sieveCK * N ^ 2 * (M * N) ^ ε / M ≤ M → 1 ≤ g0 → 2 * g0 < N' → N' ≤ N →
      ∀ G ∈ fsLe g0, ∀ (𝒩 : Finset (Finset Pr)) (β : Finset Pr → ℂ),
        (∀ A ∈ 𝒩, N' / 2 < nI A ∧ nI A ≤ N') →
        (gcdPart (bw M (sieveCK * N ^ 2 * (M * N) ^ ε / M)) G 𝒩 β).re ≤
          A * (M * N) ^ (5 * δ + 4 * ε + ε * α) * g0 * sizeE α M N *
            ∑ A ∈ 𝒩, ‖β A‖ ^ 2 := by
  obtain ⟨C3, C4, hC3, hC4, hgp⟩ := gcdPart_bw_le hε
  obtain ⟨Cw, hCw, hw⟩ := fBound_wR_of_qExp (by linarith : (1 : ℝ) / 2 ≤ α) hE hε hδ
  obtain ⟨Cs, hCs, hs⟩ := fBound_sqfW_of_qExp hE hε
  obtain ⟨C₄, hC₄, h4⟩ := four_pow_card_le hδ
  set c0 : ℝ := 3 * RΦ ^ 2 / 4 with hc0
  have hc0p : 0 < c0 := by have := RΦ_pos; positivity
  have hcK1 := one_le_sieveCK
  have hcK0 : 0 ≤ sieveCK := le_trans zero_le_one hcK1
  set A₁ : ℝ := 2 / Real.sqrt c0 + 2 ^ α * (1 + sieveCK ^ (α - 1 / 2)) with hA₁
  have hA₁0 : 0 ≤ A₁ := by
    have := Real.rpow_nonneg hcK0 (α - 1 / 2); positivity
  set u : ℝ := (Fintype.card (𝓞 K)ˣ : ℝ)⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  set cj : ℝ := 1 + c0⁻¹ ^ δ / (δ * Real.log 2) with hcj
  have hcj0 : 0 ≤ cj := by
    have := Real.rpow_nonneg (inv_nonneg.2 hc0p.le) δ
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  set k3 : ℝ := 2 / Real.sqrt 3 * 2 ^ ε * (3 + 2 * c0 ^ α) with hk3
  have hk30 : 0 ≤ k3 := by have := Real.rpow_nonneg hc0p.le α; positivity
  set k4 : ℝ := 2 + sieveCK ^ α with hk4
  have hk40 : 0 ≤ k4 := by have := Real.rpow_nonneg hcK0 α; positivity
  refine ⟨u * ((‖cMain‖ * C₄ * cj * Cw * 2 ^ ε * A₁ + C₄ * C3 * Cs * k3 + C4 * C₄ * Cs * k4) *
    C₄ ^ 2), by positivity, fun M N g0 N' hM hN hKM hg0 hN'g hN'N G hG 𝒩 β h𝒩 => ?_⟩
  have hg1 : 1 ≤ nI G := one_le_nI G
  have hgg0 : nI G ≤ g0 := nI_le_of_mem_fsLe_real (le_trans zero_le_one hg0) hG
  obtain ⟨hNM, hK1K, hX1, hXN, hXlo1, h2g, hN'0, hgQ, hcond, hQ1⟩ :=
    shell_facts (c0 := c0) hM hN hc0p hcK1 c0_le_sieveCK hKM hε.le hN'g hN'N hg1 hgg0
  set Q : ℝ := M * N with hQ
  set K : ℝ := sieveCK * N ^ 2 * Q ^ ε / M with hK
  set K₁ : ℝ := c0 * N' ^ 2 / M with hK₁
  set g : ℝ := nI G with hgdef
  set X : ℝ := N' / g with hX
  set Xlo : ℝ := N' / (2 * g) with hXlo
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hg0' : 0 < g := lt_of_lt_of_le zero_lt_one hg1
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hX0 : 0 ≤ X := le_trans zero_le_one hX1
  have hK1pos : 0 < K₁ := by rw [hK₁]; positivity
  have hKM' : K ≤ M := hKM
  have hcond' : 3 * RΦ ^ 2 * X ^ 2 * g ≤ 4 * M * K₁ := by
    have e : 3 * RΦ ^ 2 = 4 * c0 := by rw [hc0]; ring
    rw [e]; exact hcond
  -- the norms of the rows
  have hY₁ : 0 < K₁ / g := div_pos hK1pos hg0'
  have hY₁K : K₁ / g ≤ K := (div_le_self hK1pos.le hg1).trans hK1K
  have hFm := hw X (K₁ / g) K hX1 hY₁ hY₁K
  have hF3 := hs X K₁ hX1
  have hF4 := hs X K hX1
  set P : ℝ := C₄ ^ 2 * N ^ (2 * δ + 2 * ε) with hP
  have hP0 : 0 ≤ P := by positivity
  have h𝒞 : ∀ B ∈ colG 𝒩 G, Xlo ≤ nI B ∧ nI B ≤ X ∧
      (2 : ℝ) ^ B.card * (∏ Q ∈ B, (1 + (absNorm Q.1 : ℝ) ^ ε)) ^ 2 ≤ P := by
    intro B hB
    obtain ⟨hd, hGB⟩ := mem_colG.1 hB
    have hn := h𝒩 (G ∪ B) hGB
    rw [nI_union hd] at hn
    have hBX : nI B ≤ X := by
      rw [hX, le_div_iff₀ hg0', mul_comm]; exact hn.2
    refine ⟨?_, hBX, colP_le hε.le hδ.le h4 B (hBX.trans hXN)⟩
    rw [hXlo, div_le_iff₀ (by positivity)]
    have h1 : N' < g * nI B * 2 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).1 hn.1
    calc N' ≤ g * nI B * 2 := h1.le
      _ = nI B * (2 * g) := by ring
  have hrow1 := Real.rpow_nonneg (le_trans zero_le_one (le_max_right K 1)) (α - 1 / 2)
  have hrow2 := Real.rpow_nonneg (le_trans zero_le_one (le_max_right K₁ 1)) α
  have hrow3 := Real.rpow_nonneg (le_trans zero_le_one (le_max_right K 1)) α
  have hJ0 : 0 ≤ 1 + (K / (K₁ / g)) ^ δ / (δ * Real.log 2) := by
    have := Real.rpow_nonneg (div_nonneg (hY₁.le.trans hY₁K) hY₁.le) δ
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hxk0 : 0 ≤ (X * max (2 * K) 1) ^ ε := by positivity
  have hbr0 : 0 ≤ (Real.sqrt (K₁ / g))⁻¹ * (X + 1) + 2 ^ α * max K 1 ^ (α - 1 / 2) := by
    positivity
  have hΔm0 : 0 ≤ (1 + (K / (K₁ / g)) ^ δ / (δ * Real.log 2)) *
      (Cw * (X * max (2 * K) 1) ^ ε *
        ((Real.sqrt (K₁ / g))⁻¹ * (X + 1) + 2 ^ α * max K 1 ^ (α - 1 / 2))) := by positivity
  have hΔ30 : 0 ≤ Cs * (X * max K₁ 1) ^ ε * (X + max K₁ 1 ^ α) := by positivity
  have hΔ40 : 0 ≤ Cs * (X * max K 1) ^ ε * (X + max K 1 ^ α) := by positivity
  have hmain := hgp M K₁ K X Xlo _ _ _ P G 𝒩 β hM0 hKM' hK1K hXlo1 hΔm0 hΔ30 hΔ40 hP0 hcond'
    hFm hF3 hF4 h𝒞
  -- the sizes
  obtain ⟨hEM, hEN, hEr, hE1⟩ := sizeE_ge (α := α) hM hN
  have hE0 : 0 ≤ sizeE α M N := le_trans zero_le_one hE1
  have hg0N : g0 ≤ N := le_trans (by linarith : g0 ≤ 2 * g0) (le_trans hN'g.le hN'N)
  have hgN : g ≤ N := hgg0.trans hg0N
  have hN'1 : 1 ≤ N' := le_trans (by linarith : (1 : ℝ) ≤ 2 * g0) hN'g.le
  have hXlo0 : 0 < Xlo := lt_trans zero_lt_one hXlo1
  have hK1M : K₁ ≤ M := hK1K.trans hKM'
  have bt4 : (4 : ℝ) ^ G.card ≤ C₄ * Q ^ δ := four_pow_le_Q hδ.le h4 hgQ
  have bt2 : (2 : ℝ) ^ G.card ≤ C₄ * Q ^ δ :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) _).trans bt4
  have bJ := shellJ_le hM hQ hQ1 hKM' hc0p hg1 hgN hN'1 hK₁ hδ hY₁K
  have bxk := XK_le hM hQ hX0 hXN hKM' hε.le
  have bsb := sqrtM_bracket_le (α := α) (ε := ε) (CK := sieveCK) (c0 := c0) hM hN hQ hα hε.le hc0p
    hcK0 hK hg1 hN'0 hX hX1 hK₁
  have be3 := err3_size_le (α := α) (ε := ε) hM hN hQ hα hε.le hc0p.le hg1 hgg0 h2g hN'N hX hXlo
    hK₁ hK1M
  have be4 := err4_size_le (α := α) (ε := ε) hM hN hQ hα hε.le hcK0 hK hKM' hNM hX1 hXN
  have bpg : ∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε) ≤ C₄ * Q ^ (δ + ε) := by
    have h2 : g ^ ε ≤ Q ^ ε := Real.rpow_le_rpow hg0'.le hgQ hε.le
    calc ∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε) ≤ 2 ^ G.card * g ^ ε := eulB_le hε.le G
      _ ≤ (C₄ * Q ^ δ) * Q ^ ε :=
          mul_le_mul bt2 h2 (Real.rpow_nonneg hg0'.le _) (by positivity)
      _ = C₄ * Q ^ (δ + ε) := by rw [Real.rpow_add hQ0]; ring
  have bP : P ≤ C₄ ^ 2 * Q ^ (2 * δ + 2 * ε) := by
    have hNQ : N ≤ Q := by rw [hQ]; exact le_mul_of_one_le_left (by linarith) hM
    have : N ^ (2 * δ + 2 * ε) ≤ Q ^ (2 * δ + 2 * ε) :=
      Real.rpow_le_rpow (by linarith) hNQ (by positivity)
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have he30 : 0 ≤ 2 * M / Real.sqrt 3 * (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) *
      ((X * max K₁ 1) ^ ε * (X + max K₁ 1 ^ α)) / Xlo := by positivity
  have he40 : 0 ≤ (X * max K 1) ^ ε * (X + max K 1 ^ α) := by positivity
  have hsb0 : 0 ≤ Real.sqrt M *
      ((Real.sqrt (K₁ / g))⁻¹ * (X + 1) + 2 ^ α * max K 1 ^ (α - 1 / 2)) := by positivity
  have hcomb := bracket_le (norm_nonneg cMain) hCw hC3 hCs hC4 hC₄.le hQ1 hδ.le hε.le
    (by linarith : (0 : ℝ) ≤ α) hg0 hE0 hJ0 hxk0 hsb0 he30 he40 hP0 hcj0 hA₁0 hk30 hk40 bt4 bJ
    bxk bsb bt2 be3 bpg be4 bP
  have hbr : (‖cMain‖ * Real.sqrt M * (4 : ℝ) ^ G.card *
        ((1 + (K / (K₁ / g)) ^ δ / (δ * Real.log 2)) * (Cw * (X * max (2 * K) 1) ^ ε *
          ((Real.sqrt (K₁ / g))⁻¹ * (X + 1) + 2 ^ α * max K 1 ^ (α - 1 / 2)))) +
      (2 : ℝ) ^ G.card * (2 * M / Real.sqrt 3) * C3 *
        (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) *
          (Cs * (X * max K₁ 1) ^ ε * (X + max K₁ 1 ^ α)) / Xlo +
      C4 * (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) *
        (Cs * (X * max K 1) ^ ε * (X + max K 1 ^ α))) * P =
      (‖cMain‖ * (4 : ℝ) ^ G.card * (1 + (K / (K₁ / g)) ^ δ / (δ * Real.log 2)) * Cw *
          (X * max (2 * K) 1) ^ ε * (Real.sqrt M *
            ((Real.sqrt (K₁ / g))⁻¹ * (X + 1) + 2 ^ α * max K 1 ^ (α - 1 / 2))) +
        (2 : ℝ) ^ G.card * C3 * Cs * (2 * M / Real.sqrt 3 *
          (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) *
            ((X * max K₁ 1) ^ ε * (X + max K₁ 1 ^ α)) / Xlo) +
        C4 * (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Cs *
          ((X * max K 1) ^ ε * (X + max K 1 ^ α))) * P := by ring
  have hS0 : 0 ≤ ∑ A ∈ 𝒩, ‖β A‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine (Complex.re_le_norm _).trans (hmain.trans ?_)
  rw [hbr]
  calc u * ((‖cMain‖ * (4 : ℝ) ^ G.card * (1 + (K / (K₁ / g)) ^ δ / (δ * Real.log 2)) * Cw *
          (X * max (2 * K) 1) ^ ε * (Real.sqrt M *
            ((Real.sqrt (K₁ / g))⁻¹ * (X + 1) + 2 ^ α * max K 1 ^ (α - 1 / 2))) +
        (2 : ℝ) ^ G.card * C3 * Cs * (2 * M / Real.sqrt 3 *
          (Real.sqrt (4 * M / 3) ^ ε * Real.sqrt K₁ ^ ε) *
            ((X * max K₁ 1) ^ ε * (X + max K₁ 1 ^ α)) / Xlo) +
        C4 * (∏ Q ∈ G, (1 + (absNorm Q.1 : ℝ) ^ ε)) * Cs *
          ((X * max K 1) ^ ε * (X + max K 1 ^ α))) * P) * ∑ A ∈ 𝒩, ‖β A‖ ^ 2
      ≤ u * (((‖cMain‖ * C₄ * cj * Cw * 2 ^ ε * A₁ + C₄ * C3 * Cs * k3 + C4 * C₄ * Cs * k4) *
          C₄ ^ 2) * Q ^ (5 * δ + 4 * ε + ε * α) * g0 * sizeE α M N) * ∑ A ∈ 𝒩, ‖β A‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomb hu0) hS0
    _ = _ := by ring

theorem admW_mono {Y Y' : ℝ} (h : Y ≤ Y') (m : 𝓞 K) : admW Y m ≤ admW Y' m := by
  unfold admW
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.trans h⟩ h2
  · exact zero_le_one
  · exact le_rfl

theorem bw_le_re {M Kt : ℝ} (m : 𝓞 K) :
    bw M Kt m ≤ (Majorant.Phi (σO m / (Real.sqrt M : ℂ))).re := by
  unfold bw; split_ifs
  · exact le_rfl
  · exact Majorant.Phi_re_nonneg _

/-- **The rows of `B(M, N, K)` sum to `O(M)`**: `Σ_m w(m) ≤ (2M + 49R²)B` (round 345's
`norm_pS_diag` at `A = ∅`). -/
theorem tsum_bw_le {M : ℝ} (hM : 0 < M) (Kt : ℝ) {B : ℝ} (hB : ∀ ρ, ‖dualG ρ‖ ≤ B) :
    ∑' m, bw M Kt m ≤ (2 * M + 49 * RΦ ^ 2) * B := by
  have hs : Summable fun u : 𝓞 K => (1 : ℂ) * Majorant.Phi (σO u / (Real.sqrt M : ℂ)) :=
    summable_mul_Phi M hM (fun _ => 1) (B := 1) (fun _ => by simp)
  simp only [one_mul] at hs
  have hre : Summable fun u : 𝓞 K => (Majorant.Phi (σO u / (Real.sqrt M : ℂ))).re :=
    (Complex.reCLM.summable hs)
  have hp : pS M ∅ ∅ = ∑' u : 𝓞 K, Majorant.Phi (σO u / (Real.sqrt M : ℂ)) := by
    unfold pS; simp [q2]
  have hd := norm_pS_diag hM hB (∅ : Finset Pr)
  rw [Finset.card_empty, pow_zero, one_mul] at hd
  calc ∑' m, bw M Kt m ≤ ∑' m : 𝓞 K, (Majorant.Phi (σO m / (Real.sqrt M : ℂ))).re :=
        (summable_bw hM Kt).tsum_le_tsum (fun m => bw_le_re m) hre
    _ = (pS M ∅ ∅).re := by rw [hp, Complex.re_tsum hs]
    _ ≤ ‖pS M ∅ ∅‖ := Complex.re_le_norm _
    _ ≤ _ := hd

/-- **Case 2 of Theorem cor**: if `M < C_K N²Q^ε/M` then `N + M^α ≤ (1 + C_K^{α−1/2})Q^{εα}E`. -/
theorem case2_le {M N Q ε α CK : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hQ : Q = M * N) (hα : 1 ≤ α)
    (hε : 0 ≤ ε) (hCK : 0 ≤ CK) (h : M < CK * N ^ 2 * Q ^ ε / M) :
    N + M ^ α ≤ (1 + CK ^ (α - 1 / 2)) * Q ^ (ε * α) * sizeE α M N := by
  obtain ⟨hEM, hEN, hEr, hE1⟩ := sizeE_ge (α := α) hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hE0 : 0 ≤ sizeE α M N := by linarith
  have hQe1 : 1 ≤ Q ^ (ε * α) := Real.one_le_rpow hQ1 (by positivity)
  -- `M ≤ √C_K·N·Q^{ε/2}`
  have hM2 : M ^ 2 ≤ CK * N ^ 2 * Q ^ ε := by
    rw [lt_div_iff₀ hM0] at h; nlinarith
  have hMb : M ≤ CK ^ (1 / 2 : ℝ) * N * Q ^ (ε / 2) := by
    have e : (CK ^ (1 / 2 : ℝ) * N * Q ^ (ε / 2)) ^ 2 = CK * N ^ 2 * Q ^ ε := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (Q ^ (ε / 2)),
        ← Real.rpow_mul hCK, ← Real.rpow_mul hQ0.le]
      norm_num
    have h0 : 0 ≤ CK ^ (1 / 2 : ℝ) * N * Q ^ (ε / 2) := by positivity
    nlinarith [sq_nonneg (M - CK ^ (1 / 2 : ℝ) * N * Q ^ (ε / 2))]
  -- `M^α = M^{2α−1}M^{1−α}`
  have e1 : M ^ α = M ^ (2 * α - 1) * M ^ (1 - α) := by
    rw [← Real.rpow_add hM0]; ring_nf
  have h2 : M ^ (2 * α - 1) ≤ CK ^ (α - 1 / 2) * Q ^ (ε * (α - 1 / 2)) * N ^ (2 * α - 1) := by
    calc M ^ (2 * α - 1) ≤ (CK ^ (1 / 2 : ℝ) * N * Q ^ (ε / 2)) ^ (2 * α - 1) :=
          Real.rpow_le_rpow hM0.le hMb (by linarith)
      _ = CK ^ (α - 1 / 2) * Q ^ (ε * (α - 1 / 2)) * N ^ (2 * α - 1) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hN0.le,
            ← Real.rpow_mul hCK, ← Real.rpow_mul hQ0.le]
          ring_nf
  have hMa : 0 ≤ M ^ (1 - α) := Real.rpow_nonneg hM0.le _
  have hQe : Q ^ (ε * (α - 1 / 2)) ≤ Q ^ (ε * α) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)
  have hCKa : 0 ≤ CK ^ (α - 1 / 2) := Real.rpow_nonneg hCK _
  have h3 : M ^ α ≤ CK ^ (α - 1 / 2) * Q ^ (ε * α) * sizeE α M N := by
    rw [e1]
    calc M ^ (2 * α - 1) * M ^ (1 - α)
        ≤ CK ^ (α - 1 / 2) * Q ^ (ε * (α - 1 / 2)) * N ^ (2 * α - 1) * M ^ (1 - α) :=
          mul_le_mul_of_nonneg_right h2 hMa
      _ = CK ^ (α - 1 / 2) * Q ^ (ε * (α - 1 / 2)) * (N ^ (2 * α - 1) * M ^ (1 - α)) := by ring
      _ ≤ CK ^ (α - 1 / 2) * Q ^ (ε * α) * sizeE α M N := by gcongr
  have h4 : N ≤ Q ^ (ε * α) * sizeE α M N := hEN.trans (le_mul_of_one_le_left hE0 hQe1)
  calc N + M ^ α ≤ Q ^ (ε * α) * sizeE α M N + CK ^ (α - 1 / 2) * Q ^ (ε * α) * sizeE α M N :=
        add_le_add h4 h3
    _ = _ := by ring

/-- **The combination of the recursion**: `P(D + R(D + F)) ≤ c_P(c_D + c_R(c_D + c_F))Q^{x₁+x₄+x₃}E`
when `P ≤ c_PQ^{x₁}`, `D ≤ c_DQ^{x₂}E`, `F ≤ c_FQ^{x₃}E`, `R ≤ c_RQ^{x₄}`, `x₂ ≤ x₃`, `x₄ ≥ 0`. -/
theorem combine_rec {Q E P D F R cP cD cF cR x1 x2 x3 x4 : ℝ} (hQ : 1 ≤ Q) (hE : 0 ≤ E)
    (hD0 : 0 ≤ D) (hF0 : 0 ≤ F) (hR0 : 0 ≤ R) (hcD : 0 ≤ cD) (hcF : 0 ≤ cF)
    (hcR : 0 ≤ cR) (hcP : 0 ≤ cP) (h23 : x2 ≤ x3) (hx4 : 0 ≤ x4)
    (hP : P ≤ cP * Q ^ x1) (hD : D ≤ cD * Q ^ x2 * E) (hF : F ≤ cF * Q ^ x3 * E)
    (hR : R ≤ cR * Q ^ x4) :
    P * (D + R * (D + F)) ≤ cP * (cD + cR * (cD + cF)) * Q ^ (x1 + x4 + x3) * E := by
  have hQ0 : 0 < Q := by linarith
  have q23 : Q ^ x2 ≤ Q ^ x3 := Real.rpow_le_rpow_of_exponent_le hQ h23
  have q34 : Q ^ x3 ≤ Q ^ (x4 + x3) := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  have hD' : D ≤ cD * Q ^ (x4 + x3) * E := hD.trans (by gcongr; linarith)
  have hF' : F ≤ cF * Q ^ (x4 + x3) * E := hF.trans (by gcongr)
  have hR' : R * (D + F) ≤ cR * (cD + cF) * Q ^ (x4 + x3) * E := by
    calc R * (D + F) ≤ (cR * Q ^ x4) * (cD * Q ^ x3 * E + cF * Q ^ x3 * E) :=
          mul_le_mul hR (add_le_add (hD.trans (by gcongr)) hF) (by positivity) (by positivity)
      _ = cR * (cD + cF) * (Q ^ x4 * Q ^ x3) * E := by ring
      _ = _ := by rw [← Real.rpow_add hQ0]
  have hin : D + R * (D + F) ≤ (cD + cR * (cD + cF)) * Q ^ (x4 + x3) * E := by
    have := add_le_add hD' hR'; linarith
  calc P * (D + R * (D + F)) ≤ (cP * Q ^ x1) * ((cD + cR * (cD + cF)) * Q ^ (x4 + x3) * E) :=
        mul_le_mul hP hin (by positivity) (by positivity)
    _ = cP * (cD + cR * (cD + cF)) * (Q ^ x1 * Q ^ (x4 + x3)) * E := by ring
    _ = _ := by rw [← Real.rpow_add hQ0]; ring_nf

theorem N_le_M_of_K_le {M N Q ε CK : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hε : 0 ≤ ε)
    (hCK : 1 ≤ CK) (hKM : CK * N ^ 2 * Q ^ ε / M ≤ M) : N ≤ M := by
  have hM0 : 0 < M := by linarith
  have hQe1 : 1 ≤ Q ^ ε := Real.one_le_rpow hQ hε
  have h1 : CK * N ^ 2 * Q ^ ε ≤ M ^ 2 := by
    rw [div_le_iff₀ hM0] at hKM; nlinarith
  have h2 : N ^ 2 ≤ CK * N ^ 2 * Q ^ ε := by
    have : 0 ≤ N ^ 2 := sq_nonneg _
    calc N ^ 2 = 1 * N ^ 2 * 1 := by ring
      _ ≤ CK * N ^ 2 * Q ^ ε := by gcongr
  nlinarith

set_option maxHeartbeats 800000 in
/-- **The norm of `B(M, N, K)` by the recursion** (case 1 of Theorem cor): for `(E_α)`, `ε₀ > 0`
and `r ≥ 1/ε₀`, with `δ = ε₀/r`, `K = C_K N²(MN)^{ε₀}/M ≤ M`,
`FBound (bw M K) N (C·(MN)^{2ε₀+δ+θ+2ε₀}·E)`, `θ = 5δ + 4ε₀ + ε₀α`. -/
theorem fBound_bw_le {α : ℝ} (hα : 1 ≤ α) (hE : QExp α) {e0 : ℝ} (he0 : 0 < e0) (r : ℕ)
    (hr : 1 ≤ r) (hre : 1 / (r : ℝ) ≤ e0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → sieveCK * N ^ 2 * (M * N) ^ e0 / M ≤ M →
      FBound (bw M (sieveCK * N ^ 2 * (M * N) ^ e0 / M)) N
        (C * (M * N) ^ (2 * e0 + e0 / r + (5 * (e0 / r) + 4 * e0 + e0 * α + 2 * e0)) *
          sizeE α M N) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  set δ : ℝ := e0 / r with hδdef
  have hδ : 0 < δ := div_pos he0 hr0
  have hδr : δ * r = e0 := by rw [hδdef]; field_simp
  obtain ⟨A, hA0, hA⟩ := gcdPart_shell_le hα hE he0 hδ
  obtain ⟨C₁, hC₁0, hC₁⟩ := fBoundP_gcd hδ
  obtain ⟨B, hB0, hB⟩ := exists_norm_dualG_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κc : ℝ := 2 * kappa + 5 with hκc
  have hκc0 : 0 ≤ κc := by have := kappa_pos; positivity
  set Ltc : ℝ := 1 + 1 / (δ * Real.log 2) with hLtc
  have hLtc0 : 0 ≤ Ltc := by positivity
  set ca : ℝ := Ltc * C₁ + 1 with hca
  have hca0 : 0 ≤ ca := by positivity
  set cD : ℝ := (2 + 49 * RΦ ^ 2) * B * κc * 2 with hcD
  have hcD0 : 0 ≤ cD := by positivity
  set θ : ℝ := 5 * δ + 4 * e0 + e0 * α with hθ
  refine ⟨ca ^ r * (cD + (r * Ltc) * (cD + κc * A)), by positivity,
    fun M N hM hN hKM => ?_⟩
  set Q : ℝ := M * N with hQ
  set K : ℝ := sieveCK * N ^ 2 * Q ^ e0 / M with hK
  set E : ℝ := sizeE α M N with hEdef
  obtain ⟨hEM, hEN, hEr, hE1⟩ := sizeE_ge (α := α) hM hN
  have hE0 : 0 ≤ E := le_trans zero_le_one hE1
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hNQ : N ≤ Q := by rw [hQ]; exact le_mul_of_one_le_left (by linarith) hM
  have hw0 : ∀ m, 0 ≤ bw M K m := bw_nonneg M K
  have hw : Summable (bw M K) := summable_bw hM0 K
  -- the level `g₀ = N^{1/r}`
  set g0 : ℝ := N ^ ((1 : ℝ) / r) with hg0def
  have hg0 : 1 ≤ g0 := Real.one_le_rpow hN (by positivity)
  have hg0r : N ≤ g0 ^ r := by
    rw [hg0def, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    rw [show (1 : ℝ) / r * r = 1 by field_simp, Real.rpow_one]
  have hg0Q : g0 ≤ Q ^ e0 :=
    (Real.rpow_le_rpow_of_exponent_le hN hre).trans
      (Real.rpow_le_rpow (by linarith) hNQ he0.le)
  -- the number of shells
  have hexL : ∃ L : ℕ, N < 2 ^ L := pow_unbounded_of_one_lt N (by norm_num)
  set L : ℕ := Nat.find hexL with hLdef
  have hL : N < 2 ^ L := Nat.find_spec hexL
  have hLb : (L : ℝ) ≤ Ltc * Q ^ δ := by
    have hQd : 1 ≤ Q ^ δ := Real.one_le_rpow hQ1 hδ.le
    have hNd : N ^ δ ≤ Q ^ δ := Real.rpow_le_rpow (by linarith) hNQ hδ.le
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0, Nat.cast_zero]; positivity
    · have h1 : (2 : ℝ) ^ (L - 1) ≤ N := not_lt.1 (Nat.find_min hexL (Nat.sub_lt h0 one_pos))
      have h2 := nat_le_rpow_of_two_pow_le hδ h1
      rw [Nat.cast_sub (show 1 ≤ L from h0), Nat.cast_one] at h2
      have h3 : N ^ δ / (δ * Real.log 2) ≤ Q ^ δ * (1 / (δ * Real.log 2)) := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hNd (by positivity)
      rw [hLtc]
      nlinarith
  -- the shell hypothesis
  set a : ℝ := C₁ * N ^ δ with hadef
  have ha0 : 0 ≤ a := by positivity
  set F3 : ℝ := A * Q ^ θ * g0 * E with hF3
  have hF30 : 0 ≤ F3 := by positivity
  set F : ℝ := (fsLe g0).card * F3 with hFdef
  have hF0 : 0 ≤ F := by positivity
  have hsh : ∀ N', 2 * g0 < N' → N' ≤ N → ∀ Δ, 0 ≤ Δ → FBound (bw M K) (N' / g0) Δ →
      FBoundP (bw M K) (fun A => N' / 2 < nI A) N' (a * Δ + F) := by
    intro N' hN'g hN'N Δ hΔ hFB
    have hN'1 : 1 ≤ N' := by linarith
    have h := hC₁ (bw M K) hw0 hw (fun A => N' / 2 < nI A) N' g0 Δ (fun _ => F3) hN'1
      (by linarith) hΔ (fun _ => hF30) hFB
      (fun G hG 𝒩 β h𝒩 => hA M N g0 N' hM hN hKM hg0 hN'g hN'N G hG 𝒩 β h𝒩)
    refine h.mono ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : N' ^ δ ≤ N ^ δ := Real.rpow_le_rpow (by linarith) hN'N hδ.le
    have : C₁ * N' ^ δ * Δ ≤ a * Δ := by
      rw [hadef]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC₁0) hΔ
    linarith
  have hrec := fBound_rec hw0 hw hg0 r hg0r L hL ha0 hF0 hsh
  refine hrec.mono le_rfl ?_
  -- the sizes
  set Dt : ℝ := (∑' m, bw M K m) * (fsLe (2 * g0)).card with hDt
  have hDt0 : 0 ≤ Dt := mul_nonneg (tsum_nonneg hw0) (Nat.cast_nonneg _)
  have e : ((L : ℝ) * a + 1) ^ r * (Dt + r * (L * (Dt + F))) =
      ((L : ℝ) * a + 1) ^ r * (Dt + ((r : ℝ) * L) * (Dt + F)) := by ring
  rw [e]
  have hP : ((L : ℝ) * a + 1) ^ r ≤ ca ^ r * Q ^ (2 * e0) := by
    have hQ2 : 1 ≤ Q ^ (2 * δ) := Real.one_le_rpow hQ1 (by positivity)
    have hNd : N ^ δ ≤ Q ^ δ := Real.rpow_le_rpow (by linarith) hNQ hδ.le
    have h1 : (L : ℝ) * a + 1 ≤ ca * Q ^ (2 * δ) := by
      have hQdd : Q ^ δ * Q ^ δ = Q ^ (2 * δ) := by
        rw [← Real.rpow_add hQ0]; ring_nf
      have : (L : ℝ) * a ≤ Ltc * C₁ * Q ^ (2 * δ) := by
        calc (L : ℝ) * a ≤ (Ltc * Q ^ δ) * (C₁ * Q ^ δ) := by
              rw [hadef]
              exact mul_le_mul hLb (mul_le_mul_of_nonneg_left hNd hC₁0) (by positivity)
                (by positivity)
          _ = Ltc * C₁ * (Q ^ δ * Q ^ δ) := by ring
          _ = _ := by rw [hQdd]
      rw [hca]; nlinarith
    calc ((L : ℝ) * a + 1) ^ r ≤ (ca * Q ^ (2 * δ)) ^ r :=
          pow_le_pow_left₀ (by positivity) h1 r
      _ = ca ^ r * Q ^ (2 * e0) := by
          rw [mul_pow, ← Real.rpow_natCast (Q ^ (2 * δ)), ← Real.rpow_mul hQ0.le]
          congr 2; rw [← hδr]; ring
  have hDb : Dt ≤ cD * Q ^ e0 * E := by
    have h1 := tsum_bw_le hM0 K hB
    have h2 := card_fsLe_le' (by positivity : (0 : ℝ) ≤ 2 * g0)
    have h3 : (2 * M + 49 * RΦ ^ 2) * B ≤ (2 + 49 * RΦ ^ 2) * M * B := by
      have : 49 * RΦ ^ 2 ≤ 49 * RΦ ^ 2 * M := le_mul_of_one_le_right (by positivity) hM
      nlinarith
    calc Dt ≤ ((2 + 49 * RΦ ^ 2) * M * B) * ((2 * kappa + 5) * (2 * g0)) := by
          rw [hDt]
          exact mul_le_mul (h1.trans h3) h2 (Nat.cast_nonneg _) (by positivity)
      _ = cD * M * g0 := by rw [hcD, hκc]; ring
      _ ≤ cD * E * Q ^ e0 := by
          gcongr
      _ = cD * Q ^ e0 * E := by ring
  have hFb : F ≤ κc * A * Q ^ (θ + 2 * e0) * E := by
    have h2 := card_fsLe_le' (by positivity : (0 : ℝ) ≤ g0)
    have hgg : g0 * g0 ≤ Q ^ (2 * e0) := by
      calc g0 * g0 ≤ Q ^ e0 * Q ^ e0 := mul_le_mul hg0Q hg0Q (by positivity) (by positivity)
        _ = _ := by rw [← Real.rpow_add hQ0]; ring_nf
    calc F ≤ ((2 * kappa + 5) * g0) * F3 := mul_le_mul_of_nonneg_right h2 hF30
      _ = κc * A * Q ^ θ * (g0 * g0) * E := by rw [hF3, hκc]; ring
      _ ≤ κc * A * Q ^ θ * Q ^ (2 * e0) * E := by gcongr
      _ = κc * A * Q ^ (θ + 2 * e0) * E := by rw [mul_assoc (κc * A), ← Real.rpow_add hQ0]
  have hRb : (r : ℝ) * L ≤ (r * Ltc) * Q ^ δ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hLb (Nat.cast_nonneg _)
  have hc := combine_rec hQ1 hE0 hDt0 hF0 (by positivity) hcD0 (by positivity) (by positivity)
    (by positivity) (show e0 ≤ θ + 2 * e0 by rw [hθ]; nlinarith) hδ.le hP hDb hFb hRb
  refine hc.trans (le_of_eq ?_)
  rw [hθ]

/-- **Goldmakher and Louvel's Theorem cor**: `(E_α)` with `α ≥ 1` gives, for every `ε > 0`,
`FBound (admW M) N (C·(MN)^ε·(M + N + N^{2α−1}M^{1−α}))`. -/
theorem fBound_cor {α : ℝ} (hα : 1 ≤ α) (hE : QExp α) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      FBound (admW M) N (C * (M * N) ^ ε * sizeE α M N) := by
  set e0 : ℝ := ε / (α + 20) with he0def
  have he0 : 0 < e0 := div_pos hε (by linarith)
  have hεe : e0 * (α + 20) = ε := by rw [he0def]; field_simp
  set r : ℕ := ⌈1 / e0⌉₊ with hrdef
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 (by positivity)))
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hre : 1 / (r : ℝ) ≤ e0 := by
    have h1 : 1 / e0 ≤ r := Nat.le_ceil _
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < r)]
    rw [div_le_iff₀ he0] at h1
    linarith
  obtain ⟨Cb, hCb0, hCb⟩ := fBound_bw_le hα hE he0 r hr hre
  obtain ⟨Ce, hCe0, hCe⟩ := hE e0 he0
  have hcK0 : 0 ≤ sieveCK := le_trans zero_le_one one_le_sieveCK
  have hcKa : 0 ≤ sieveCK ^ α := Real.rpow_nonneg hcK0 _
  have hcKb : 0 ≤ sieveCK ^ (α - 1 / 2) := Real.rpow_nonneg hcK0 _
  set C1 : ℝ := Ce * (2 + sieveCK ^ α) with hC1
  set C2 : ℝ := Ce * (1 + sieveCK ^ (α - 1 / 2)) with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨C1 + Cb + C2, by positivity, fun M N hM hN => ?_⟩
  set Q : ℝ := M * N with hQ
  set E : ℝ := sizeE α M N with hEdef
  obtain ⟨hEM, hEN, hEr, hE1⟩ := sizeE_ge (α := α) hM hN
  have hE0 : 0 ≤ E := le_trans zero_le_one hE1
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hQε : 0 ≤ Q ^ ε := Real.rpow_nonneg hQ0.le _
  have hδ : e0 / r ≤ e0 := div_le_self he0.le hrR
  have hx1 : e0 + e0 * α ≤ ε := by rw [← hεe]; nlinarith
  have hx2 : 2 * e0 + e0 / r + (5 * (e0 / r) + 4 * e0 + e0 * α + 2 * e0) ≤ ε := by
    rw [← hεe]; nlinarith
  have hQ1x : Q ^ (e0 + e0 * α) ≤ Q ^ ε := Real.rpow_le_rpow_of_exponent_le hQ1 hx1
  have hQ2x : Q ^ (2 * e0 + e0 / r + (5 * (e0 / r) + 4 * e0 + e0 * α + 2 * e0)) ≤ Q ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hQ1 hx2
  by_cases hKM : sieveCK * N ^ 2 * Q ^ e0 / M ≤ M
  · -- case 1: the recursion
    set K : ℝ := sieveCK * N ^ 2 * Q ^ e0 / M with hK
    have hNM : N ≤ M := N_le_M_of_K_le hM hN hQ1 he0.le one_le_sieveCK hKM
    have hK1 : 1 ≤ max K 1 := le_max_right _ _
    have hΔ1n : 0 ≤ Ce * (N * max K 1) ^ e0 * (N + max K 1 ^ α) := by
      have := Real.rpow_nonneg (le_trans zero_le_one hK1) α
      have : 0 ≤ N * max K 1 := by positivity
      positivity
    have hq := hCe N (max K 1) hN hK1
    have h1 : FBound (admW K) N (Ce * (N * max K 1) ^ e0 * (N + max K 1 ^ α)) :=
      FBound.of_le (admW_nonneg K) (admW_mono (le_max_left K 1)) (summable_admW _)
        (fBound_of_qBound hΔ1n hq)
    have h2 := hCb M N hM hN hKM
    refine (fBound_admW_split hM0 h1 h2).mono le_rfl ?_
    have hs := err4_size_le (α := α) (ε := e0) hM hN hQ hα he0.le hcK0 hK hKM hNM hN le_rfl
    have b1 : Ce * (N * max K 1) ^ e0 * (N + max K 1 ^ α) ≤ C1 * Q ^ ε * E := by
      calc Ce * (N * max K 1) ^ e0 * (N + max K 1 ^ α)
          = Ce * ((N * max K 1) ^ e0 * (N + max K 1 ^ α)) := by ring
        _ ≤ Ce * ((2 + sieveCK ^ α) * Q ^ (e0 + e0 * α) * E) := mul_le_mul_of_nonneg_left hs hCe0
        _ ≤ Ce * ((2 + sieveCK ^ α) * Q ^ ε * E) := by gcongr
        _ = C1 * Q ^ ε * E := by rw [hC1]; ring
    have b2 : Cb * Q ^ (2 * e0 + e0 / r + (5 * (e0 / r) + 4 * e0 + e0 * α + 2 * e0)) * E ≤
        Cb * Q ^ ε * E := by gcongr
    have b3 : 0 ≤ C2 * Q ^ ε * E := by positivity
    calc _ ≤ C1 * Q ^ ε * E + Cb * Q ^ ε * E := add_le_add b1 b2
      _ ≤ C1 * Q ^ ε * E + Cb * Q ^ ε * E + C2 * Q ^ ε * E := le_add_of_nonneg_right b3
      _ = (C1 + Cb + C2) * Q ^ ε * E := by ring
  · -- case 2: `(E_α)` directly
    push Not at hKM
    have hΔn : 0 ≤ Ce * (N * M) ^ e0 * (N + M ^ α) := by
      have := Real.rpow_nonneg hM0.le α
      have : 0 ≤ N * M := by positivity
      positivity
    have hf := fBound_of_qBound hΔn (hCe N M hN hM)
    refine hf.mono le_rfl ?_
    have hs := case2_le (α := α) (ε := e0) hM hN hQ hα he0.le hcK0 hKM
    have hNM : N * M = Q := by rw [hQ, mul_comm]
    rw [hNM]
    have b : Ce * Q ^ e0 * (N + M ^ α) ≤ C2 * Q ^ ε * E := by
      calc Ce * Q ^ e0 * (N + M ^ α)
          ≤ Ce * Q ^ e0 * ((1 + sieveCK ^ (α - 1 / 2)) * Q ^ (e0 * α) * E) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = Ce * (1 + sieveCK ^ (α - 1 / 2)) * (Q ^ e0 * Q ^ (e0 * α)) * E := by ring
        _ = Ce * (1 + sieveCK ^ (α - 1 / 2)) * Q ^ (e0 + e0 * α) * E := by
            rw [← Real.rpow_add hQ0]
        _ ≤ Ce * (1 + sieveCK ^ (α - 1 / 2)) * Q ^ ε * E := by gcongr
        _ = C2 * Q ^ ε * E := by rw [hC2]
    have b1 : 0 ≤ C1 * Q ^ ε * E := by positivity
    have b2 : 0 ≤ Cb * Q ^ ε * E := by positivity
    calc _ ≤ C2 * Q ^ ε * E := b
      _ ≤ C1 * Q ^ ε * E + Cb * Q ^ ε * E + C2 * Q ^ ε * E := by linarith
      _ = (C1 + Cb + C2) * Q ^ ε * E := by ring

end Eis

end

#print axioms Eis.eulB_le
#print axioms Eis.colP_le
#print axioms Eis.one_le_sieveCK
#print axioms Eis.c0_le_sieveCK
#print axioms Eis.four_pow_le_Q
#print axioms Eis.shell_facts
#print axioms Eis.shellJ_le
#print axioms Eis.XK_le
#print axioms Eis.bracket_le
#print axioms Eis.gcdPart_shell_le
#print axioms Eis.admW_mono
#print axioms Eis.bw_le_re
#print axioms Eis.tsum_bw_le
#print axioms Eis.case2_le
#print axioms Eis.combine_rec
#print axioms Eis.N_le_M_of_K_le
#print axioms Eis.fBound_bw_le
#print axioms Eis.fBound_cor
