/-
# Round 681: the sum over `a` in their Lemma 8.2, by the Ramanujan sum (the CGL plan's stage M4)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Chen–Gupta–Li bound `Σ_a|ĝ_{a,1}(ξ)|²` in the proof of their Lemma 8.2: "For the a-sum, we apply the basic estimate
|C_q(m)| ≤ (m,q) for Ramanujan’s sum" (line 3114; spaces restored, the subscript transcribed), then "Next, by
Cauchy-Schwarz" (line 3214) and "upon mapping (m₁,n,m₁′,n′) → (−m₁′,n′,−m₁,n), we have G₂(ξ) = G₁(−ξ)" (lines
3324–3327; spaces restored, the subscripts transcribed), and the count of the pairs `(m₁′, n′)` (round 681's
`LinnikCGLCount.count_le`). This file gives that bound for a finite range of `n`, with any coefficients `F(m₁, n)` in
place of their inner sums over `m₂` and `b`.

The stack's form.
* `|Σ_ae_q(ax)| ≤ d(q)(x, q)` is round 653's `norm_Cq_le`, whose `d(q)` their `⪅` absorbs.
* Their Cauchy–Schwarz and the symmetry `G₂(ξ) = G₁(−ξ)` are replaced by `|u_kv_k||u_{k′}v_{k′}| ≤
  ½u_ku_{k′}(v_k² + v_{k′}²)` and the symmetry of `(s_{k′} − s_k, q)` in `k` and `k′` (`sum_sum_amgm_le`), which keeps
  every sum finite.
* Their `Σ_{d mod q}(d, q)/q ⪅ 1` is `|c_q(n)| ≤ Σ_{h∈ℤ/qℤ}(h, q)` (`norm_cqg_le`).

Plain statements, with `q ≥ 1` (`[NeZero q]`) and `e_q` Mathlib's `ZMod.stdAddChar`.
* `conj_stdAddChar`: `conj(e_q(y)) = e_q(−y)`.
* `sum_units_norm_sq_le`: for a finite set `K`, points `s_k ∈ ℤ/qℤ` and coefficients `X_k ∈ ℂ`,
  `Σ_{a∈(ℤ/qℤ)ˣ}|Σ_{k∈K}X_ke_q(−as_k)|² ≤ d(q)Σ_{k,k′∈K}|X_k||X_{k′}|(s_{k′} − s_k, q)`.
* `sum_sum_amgm_le`: for `u ≥ 0` and `g ≥ 0` symmetric,
  `Σ_{k,k′}u_ku_{k′}v_kv_{k′}g(k, k′) ≤ Σ_ku_kv_k²Σ_{k′}u_{k′}g(k, k′)`.
* `norm_stdAddChar`, `norm_cqg_le`, `gw_neg`: `|e_q(y)| = 1`; `|c_q(n)| ≤ Σ_{h∈ℤ/qℤ}(h, q)`; `(−x, q) = (x, q)`.
* `sum_a_finite_le`: for `L > 0`, `M₁ > 0`, `0 < δ ≤ 1`, real `ξ`, a finite set `T` of integers and any
  `F : ℤ → ℤ → ℂ`, with `Ψ(m, n) = ψ̂₀(L(n/q − ξ/m))`,
  `Σ_a|Σ_{m∈P1 M₁}Σ_{n∈T, n≠0}(L/q)Ψ(m, n)c_q(n)F(m, n)e_q(−anm)|² ≤
  d(q)(L/q)²(Σ_h(h, q))²N_δΣ_{m∈P1 M₁}Σ_{n∈T, n≠0}|Ψ(m, n)||F(m, n)|²`, with `N_δ` the bound of `count_le`.

The file imports `LinnikCGLCount.lean`.
-/

import LinnikCGLCount

open Complex Set Real Filter Topology MeasureTheory FourierTransform Asymptotics
open scoped ContDiff ComplexConjugate

noncomputable section

namespace LinnikCGLAsum

open LinnikCGLRt LinnikCGLMom LinnikCGLMom4 LinnikCGLSep LinnikCGLRFact LinnikCGLRam LinnikCGLJ LinnikCGLG
  LinnikCGLPois8 LinnikCGLCount

/-! ### The characters -/

lemma norm_stdAddChar {q : ℕ} [NeZero q] (y : ZMod q) : ‖ZMod.stdAddChar y‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- For `q ≥ 1`, `conj(e_q(y)) = e_q(−y)`. -/
lemma conj_stdAddChar {q : ℕ} [NeZero q] (y : ZMod q) : conj (ZMod.stdAddChar y) = ZMod.stdAddChar (-y) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (norm_stdAddChar y)]

/-! ### The sum over `a` -/

/-- **The sum over `a`**: for `q ≥ 1`, a finite set `K`, points `s_k ∈ ℤ/qℤ` and coefficients `X_k`,
`Σ_a|Σ_kX_ke_q(−as_k)|² ≤ d(q)Σ_{k,k′}|X_k||X_{k′}|(s_{k′} − s_k, q)`. -/
lemma sum_units_norm_sq_le {q : ℕ} [NeZero q] {κ : Type*} (K : Finset κ) (s : κ → ZMod q) (X : κ → ℂ) :
    ∑ a : (ZMod q)ˣ, ‖∑ k ∈ K, X k * ZMod.stdAddChar (-((a : ZMod q) * s k))‖ ^ 2 ≤
      (q.divisors.card : ℝ) * ∑ k ∈ K, ∑ k' ∈ K, ‖X k‖ * ‖X k'‖ * gw (s k' - s k) := by
  have hsq : ∀ z : ℂ, (‖z‖ ^ 2 : ℝ) = (z * conj z).re := by
    intro z; rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hsq]
  rw [← Complex.re_sum]
  have hexp : ∀ a : (ZMod q)ˣ, (∑ k ∈ K, X k * ZMod.stdAddChar (-((a : ZMod q) * s k))) *
      conj (∑ k ∈ K, X k * ZMod.stdAddChar (-((a : ZMod q) * s k))) =
      ∑ k ∈ K, ∑ k' ∈ K, X k * conj (X k') * ZMod.stdAddChar ((a : ZMod q) * (s k' - s k)) := by
    intro a
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul, conj_stdAddChar, neg_neg]
    have : ZMod.stdAddChar ((a : ZMod q) * (s k' - s k)) =
        ZMod.stdAddChar (-((a : ZMod q) * s k)) * ZMod.stdAddChar ((a : ZMod q) * s k') := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : ∑ k ∈ K, ∑ a : (ZMod q)ˣ, ∑ k' ∈ K, X k * conj (X k') *
      ZMod.stdAddChar ((a : ZMod q) * (s k' - s k)) =
      ∑ k ∈ K, ∑ k' ∈ K, X k * conj (X k') * Cq q (s k' - s k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Cq, Finset.mul_sum]
  rw [hswap]
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k' _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h := norm_Cq_le q (s k' - s k)
  have hX : 0 ≤ ‖X k‖ * ‖X k'‖ := by positivity
  calc ‖X k‖ * ‖X k'‖ * ‖Cq q (s k' - s k)‖ ≤ ‖X k‖ * ‖X k'‖ * ((q.divisors.card : ℝ) * gw (s k' - s k)) :=
        mul_le_mul_of_nonneg_left h hX
    _ = (q.divisors.card : ℝ) * (‖X k‖ * ‖X k'‖ * gw (s k' - s k)) := by ring

/-- **AM-GM and symmetry**: for `u ≥ 0` and `g ≥ 0` symmetric,
`Σ_{k,k′}u_ku_{k′}v_kv_{k′}g(k, k′) ≤ Σ_ku_kv_k²Σ_{k′}u_{k′}g(k, k′)`. -/
lemma sum_sum_amgm_le {κ : Type*} (K : Finset κ) (u v : κ → ℝ) (g : κ → κ → ℝ) (hu : ∀ k, 0 ≤ u k)
    (hg : ∀ k k', 0 ≤ g k k') (hgs : ∀ k k', g k k' = g k' k) :
    ∑ k ∈ K, ∑ k' ∈ K, u k * u k' * v k * v k' * g k k' ≤ ∑ k ∈ K, u k * v k ^ 2 * ∑ k' ∈ K, u k' * g k k' := by
  have h1 : ∀ k k', u k * u k' * v k * v k' * g k k' ≤
      (u k * u k' * v k ^ 2 * g k k' + u k * u k' * v k' ^ 2 * g k k') / 2 := by
    intro k k'
    have hw : 0 ≤ u k * u k' * g k k' := mul_nonneg (mul_nonneg (hu k) (hu k')) (hg k k')
    nlinarith [mul_nonneg hw (sq_nonneg (v k - v k'))]
  have h2 : ∑ k ∈ K, ∑ k' ∈ K, u k * u k' * v k' ^ 2 * g k k' =
      ∑ k ∈ K, ∑ k' ∈ K, u k * u k' * v k ^ 2 * g k k' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    rw [hgs]; ring
  calc ∑ k ∈ K, ∑ k' ∈ K, u k * u k' * v k * v k' * g k k'
      ≤ ∑ k ∈ K, ∑ k' ∈ K, (u k * u k' * v k ^ 2 * g k k' + u k * u k' * v k' ^ 2 * g k k') / 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun k' _ => h1 k k'
    _ = (∑ k ∈ K, ∑ k' ∈ K, u k * u k' * v k ^ 2 * g k k' +
          ∑ k ∈ K, ∑ k' ∈ K, u k * u k' * v k' ^ 2 * g k k') / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ k ∈ K, ∑ k' ∈ K, u k * u k' * v k ^ 2 * g k k' := by rw [h2]; ring
    _ = ∑ k ∈ K, u k * v k ^ 2 * ∑ k' ∈ K, u k' * g k k' := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k' _ => ?_
        ring

/-- For `q ≥ 1`, `|c_q(n)| ≤ Σ_{h∈ℤ/qℤ}(h, q)`. -/
lemma norm_cqg_le {q : ℕ} [NeZero q] (n : ZMod q) : ‖cqg q n‖ ≤ ∑ h : ZMod q, gw h := by
  unfold cqg
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [norm_mul, norm_stdAddChar, mul_one, gw, Complex.norm_natCast]

lemma gw_neg {q : ℕ} [NeZero q] (x : ZMod q) : gw (-x) = gw x := by
  unfold gw; rw [gcd_val_neg]

/-! ### The finite form of the bound -/

/-- **The sum over `a`, finite form**: for `q ≥ 1`, `L > 0`, `M₁ > 0`, `0 < δ ≤ 1`, real `ξ`, a finite set `T` of
integers and any `F : ℤ → ℤ → ℂ`, with `Ψ(m, n) = ψ̂₀(L(n/q − ξ/m))`,
`Σ_a|Σ_{m∈P1}Σ_{n∈T, n≠0}(L/q)Ψ(m, n)c_q(n)F(m, n)e_q(−anm)|² ≤
d(q)(L/q)²(Σ_h(h, q))²N_δΣ_{m∈P1}Σ_{n∈T, n≠0}|Ψ(m, n)||F(m, n)|²`, with `N_δ` the bound of round 681's `count_le`. -/
theorem sum_a_finite_le {q : ℕ} [NeZero q] {L M₁ δ : ℝ} (hL : 0 < L) (hM₁ : 0 < M₁) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ξ : ℝ) (T : Finset ℤ) (F : ℤ → ℤ → ℂ) :
    ∑ a : (ZMod q)ˣ, ‖∑ m ∈ P1 M₁, ∑ n ∈ T.filter (· ≠ 0), ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (n / q - ξ / m)) *
        cqg q n * F m n * ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m : ZMod q))))‖ ^ 2 ≤
      (q.divisors.card : ℝ) * (L / q) ^ 2 * (∑ h : ZMod q, gw h) ^ 2 *
        (4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * (∑ h : ZMod q, gw h) *
          (2 * π + 8 * π * M₁ / L)) *
        ∑ m ∈ P1 M₁, ∑ n ∈ T.filter (· ≠ 0), ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖F m n‖ ^ 2 := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set K : Finset (ℤ × ℤ) := P1 M₁ ×ˢ T.filter (· ≠ 0) with hK
  set s : ℤ × ℤ → ZMod q := fun k => (k.2 : ZMod q) * (k.1 : ZMod q) with hs
  set Ψ : ℤ × ℤ → ℝ := fun k => ‖𝓕 psiC (L * (k.2 / q - ξ / k.1))‖ with hΨ
  set G : ℝ := ∑ h : ZMod q, gw h with hG
  set Nb : ℝ := 4 * LinnikPower.Cdiv δ * B4 * (1 + q * |ξ|) ^ δ * (1 + 2 * q * M₁ / L) ^ δ * G *
    (2 * π + 8 * π * M₁ / L) with hNb
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun h _ => gw_nonneg h
  set X : ℤ × ℤ → ℂ := fun k => ((L / q : ℝ) : ℂ) * 𝓕 psiC (L * (k.2 / q - ξ / k.1)) * cqg q k.2 * F k.1 k.2
    with hX
  -- the left side as a sum over `K`
  have hL1 : ∀ a : (ZMod q)ˣ, ∑ m ∈ P1 M₁, ∑ n ∈ T.filter (· ≠ 0), ((L / q : ℝ) : ℂ) *
      𝓕 psiC (L * (n / q - ξ / m)) * cqg q n * F m n *
        ZMod.stdAddChar (-((a : ZMod q) * ((n : ZMod q) * (m : ZMod q)))) =
      ∑ k ∈ K, X k * ZMod.stdAddChar (-((a : ZMod q) * s k)) := by
    intro a
    rw [hK, Finset.sum_product]
  simp_rw [hL1]
  refine (sum_units_norm_sq_le K s X).trans ?_
  -- `|X_k| ≤ (L/q)GΨ_k|F_k|`
  have hXk : ∀ k, ‖X k‖ ≤ L / q * G * Ψ k * ‖F k.1 k.2‖ := by
    intro k
    rw [hX, hΨ]
    simp only
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 := norm_cqg_le (q := q) (k.2 : ZMod q)
    have h2 := norm_nonneg (𝓕 psiC (L * (k.2 / q - ξ / k.1)))
    have h3 := norm_nonneg (F k.1 k.2)
    calc L / q * ‖𝓕 psiC (L * (k.2 / q - ξ / k.1))‖ * ‖cqg q k.2‖ * ‖F k.1 k.2‖
        ≤ L / q * ‖𝓕 psiC (L * (k.2 / q - ξ / k.1))‖ * G * ‖F k.1 k.2‖ := by gcongr
      _ = L / q * G * ‖𝓕 psiC (L * (k.2 / q - ξ / k.1))‖ * ‖F k.1 k.2‖ := by ring
  have hdq : (0 : ℝ) ≤ q.divisors.card := Nat.cast_nonneg _
  have hstep1 : ∑ k ∈ K, ∑ k' ∈ K, ‖X k‖ * ‖X k'‖ * gw (s k' - s k) ≤
      (L / q * G) ^ 2 * ∑ k ∈ K, ∑ k' ∈ K, Ψ k * Ψ k' * ‖F k.1 k.2‖ * ‖F k'.1 k'.2‖ * gw (s k' - s k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k' _ => ?_
    have hgw := gw_nonneg (s k' - s k)
    calc ‖X k‖ * ‖X k'‖ * gw (s k' - s k)
        ≤ (L / q * G * Ψ k * ‖F k.1 k.2‖) * (L / q * G * Ψ k' * ‖F k'.1 k'.2‖) * gw (s k' - s k) := by
          gcongr
          · exact hXk k
          · exact hXk k'
      _ = (L / q * G) ^ 2 * (Ψ k * Ψ k' * ‖F k.1 k.2‖ * ‖F k'.1 k'.2‖ * gw (s k' - s k)) := by ring
  have hΨ0 : ∀ k, 0 ≤ Ψ k := fun k => norm_nonneg _
  have hstep2 := sum_sum_amgm_le K Ψ (fun k => ‖F k.1 k.2‖) (fun k k' => gw (s k' - s k)) hΨ0
    (fun k k' => gw_nonneg _) (fun k k' => by rw [← neg_sub, gw_neg])
  -- the count
  have hcount : ∀ k ∈ K, ∑ k' ∈ K, Ψ k' * gw (s k' - s k) ≤ Nb := by
    intro k _
    have h := count_le (q := q) hL hM₁ hδ hδ1 ξ (s k) T
    rw [hK, Finset.sum_product]
    exact h
  have hstep3 : ∑ k ∈ K, Ψ k * ‖F k.1 k.2‖ ^ 2 * ∑ k' ∈ K, Ψ k' * gw (s k' - s k) ≤
      Nb * ∑ k ∈ K, Ψ k * ‖F k.1 k.2‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have : 0 ≤ Ψ k * ‖F k.1 k.2‖ ^ 2 := mul_nonneg (hΨ0 k) (sq_nonneg _)
    calc Ψ k * ‖F k.1 k.2‖ ^ 2 * ∑ k' ∈ K, Ψ k' * gw (s k' - s k) ≤ Ψ k * ‖F k.1 k.2‖ ^ 2 * Nb :=
          mul_le_mul_of_nonneg_left (hcount k hk) this
      _ = Nb * (Ψ k * ‖F k.1 k.2‖ ^ 2) := by ring
  have hR : ∑ k ∈ K, Ψ k * ‖F k.1 k.2‖ ^ 2 =
      ∑ m ∈ P1 M₁, ∑ n ∈ T.filter (· ≠ 0), ‖𝓕 psiC (L * (n / q - ξ / m))‖ * ‖F m n‖ ^ 2 := by
    rw [hK, Finset.sum_product]
  have hpos : 0 ≤ (L / q * G) ^ 2 := sq_nonneg _
  calc (q.divisors.card : ℝ) * ∑ k ∈ K, ∑ k' ∈ K, ‖X k‖ * ‖X k'‖ * gw (s k' - s k)
      ≤ (q.divisors.card : ℝ) * ((L / q * G) ^ 2 *
          ∑ k ∈ K, ∑ k' ∈ K, Ψ k * Ψ k' * ‖F k.1 k.2‖ * ‖F k'.1 k'.2‖ * gw (s k' - s k)) :=
        mul_le_mul_of_nonneg_left hstep1 hdq
    _ ≤ (q.divisors.card : ℝ) * ((L / q * G) ^ 2 *
          ∑ k ∈ K, Ψ k * ‖F k.1 k.2‖ ^ 2 * ∑ k' ∈ K, Ψ k' * gw (s k' - s k)) := by
        gcongr
    _ ≤ (q.divisors.card : ℝ) * ((L / q * G) ^ 2 * (Nb * ∑ k ∈ K, Ψ k * ‖F k.1 k.2‖ ^ 2)) := by
        gcongr
    _ = (q.divisors.card : ℝ) * (L / q) ^ 2 * G ^ 2 * Nb * ∑ k ∈ K, Ψ k * ‖F k.1 k.2‖ ^ 2 := by ring
    _ = _ := by rw [hR]

end LinnikCGLAsum

#print axioms LinnikCGLAsum.conj_stdAddChar
#print axioms LinnikCGLAsum.sum_units_norm_sq_le
#print axioms LinnikCGLAsum.sum_sum_amgm_le
#print axioms LinnikCGLAsum.norm_cqg_le
#print axioms LinnikCGLAsum.sum_a_finite_le
