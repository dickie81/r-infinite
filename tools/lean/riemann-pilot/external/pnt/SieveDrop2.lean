/-
# Round 709: the dropped terms less the kept parts

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK` and `Fits`); `x = q^L` and
`X = x/log x`. `SieveDrop.drop_ev_of` bounds the dropped terms' `B`-count by the certificate's total; less the kept
parts of `SieveBuch2.lean`, the bound is the refined certificate's total (`SieveCert2Defs.total2`).

* `not_inW_of_cand`: the cell `i` of a candidate cell `(i, j)` does not lie inside the window.
* `cost2_eq_cost`: off the dropped candidate cells of `reg2`, the refined cost is the certificate's cost.
* `Kp2_gB_ge`: for a cell `(i, j)` of `reg2` and `δ > 0`, eventually in `q`, `LargeQ q` gives
  `φ(q)⁻¹(sub2/K − nδ)X ≤ Kp2(g_B)`: `sub2` is the sum of the kept shares over the cells `k` that `keep` passes, and
  each share less `δ`, times `φ(q)⁻¹X`, is at most its part's count (`SieveKeptB.Kk_gB_ge`).
* `dropS_sub_le_cost2`: given the shares at `x` within `δ' ≥ 0`, a cell's dropped sums, less `(sub2/K − nδ')X` on a
  dropped candidate cell of `reg2`, are at most `(cost2/K)X + δ'(1 + n + n²)X`.
* `sum_cost2_div_of`: if `total2/K ≤ c` in the reals, then `Σ_{i,j} (cost2/K)X ≤ cX` for `X ≥ 0`.
* `drop_ev2`: if `total2/K ≤ c` in the reals (`htot`), then for `ε > 0`, eventually `LargeQ q` gives
  `D1(g_B) − Kp(g_B) ≤ φ(q)⁻¹(c + ε)X`.

The file imports `SieveKeptB.lean`.
-/
import SieveKeptB

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveRoute SieveDrop
open SieveCert (V DEN H U1 U2 cand dec keep reg2 keepK sub2 cost2 total2 bound2 bound4 counted4 K cost)

namespace SieveDrop2

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The cell `i` of a candidate cell `(i, j)` does not lie inside the window (`SieveBuch.Par.inW`). -/
theorem not_inW_of_cand {i j : ℕ} (hc : cand i j = true) : ¬ Par.inW i := by
  rintro ⟨h1, h2⟩
  simp [SieveCert.cand, h1, h2] at hc

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- Off the dropped candidate cells of `reg2`, the refined cost is the certificate's cost. -/
theorem cost2_eq_cost {i j : ℕ} (h : ¬(cand i j = true ∧ dec i j = false ∧ reg2 i j = true)) :
    cost2 i j = cost i j := by
  by_cases hc : cand i j = true
  · by_cases hd : dec i j = true
    · simp [SieveCert.cost2, SieveCert.cost, hc, hd]
    · have hd' : dec i j = false := by simpa using hd
      have hr : reg2 i j = false := by
        by_contra hr
        exact h ⟨hc, hd', by simpa using hr⟩
      simp [SieveCert.cost2, SieveCert.cost, SieveCert.sub2, hc, hd', hr]
  · have hc' : cand i j = false := by simpa using hc
    simp [SieveCert.cost2, SieveCert.cost, hc']

omit [Fits] in
/-- **A dropped cell's kept parts, from below.** For a cell `(i, j)` of `reg2` and `δ > 0`, eventually in `q`: if
`LargeQ q`, then `φ(q)⁻¹(sub2/K − nδ)X ≤ Kp2(g_B)`. -/
theorem Kp2_gB_ge {i j : ℕ} (hr : reg2 i j = true) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, LargeQ q →
      (q.totient : ℝ)⁻¹ * (((sub2 i j : ℝ) / K - SieveCert.n * δ) * (xq q / Real.log (xq q))) ≤
        (parQ q).Kp2 (gB q) i j := by
  have hall : ∀ᶠ q : ℕ in atTop, ∀ k ∈ range SieveCert.n, keep i j k = true → LargeQ q →
      (q.totient : ℝ)⁻¹ * (((keepK i j k : ℝ) / K - δ) * (xq q / Real.log (xq q))) ≤ (parQ q).Kk (gB q) i j k := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases hk : keep i j k = true
    · filter_upwards [SieveKeptB.Kk_gB_ge hr hk hδ] with q hq _
      exact hq
    · exact Filter.Eventually.of_forall fun q h => absurd h hk
  filter_upwards [hall] with q hq hL
  have hx1 : (1 : ℝ) < xq q := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by have := hL.q3; omega))
    (by route_num)
  have hx0 : (0 : ℝ) < xq q := by linarith
  have hlx : 0 < Real.log (xq q) := Real.log_pos hx1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = xq q / Real.log (xq q) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  rw [← hX]
  rw [← hX] at hq
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hsub : (sub2 i j : ℝ) / K =
      ∑ k ∈ range SieveCert.n, (if keep i j k = true then (keepK i j k : ℝ) / K else 0) := by
    rw [SieveCert.sub2_eq, ite_eq_left hr]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hnδ : (SieveCert.n : ℝ) * δ = ∑ _k ∈ range SieveCert.n, δ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsub, hnδ, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  unfold Par.Kp2
  refine Finset.sum_le_sum fun k hk => ?_
  split_ifs with hkp
  · exact hq k hk hkp hL
  · have h0 : (0 - δ) * X ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hφ h0

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- **A cell's dropped sums less its kept shares, against its refined cost**, given the shares at `x`, for `δ' ≥ 0`
and `X ≥ 0`: `dropS − [cand ∧ ¬dec ∧ reg2](sub2/K − nδ')X ≤ (cost2/K)X + δ'(1 + n + n²)X`. -/
theorem dropS_sub_le_cost2 {x δ' X : ℝ} (hδ' : 0 ≤ δ') (hX : 0 ≤ X) {i j : ℕ}
    (h2 : cand i j = true → S2 x i j ≤ ((bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K + δ') * X)
    (h4 : ∀ k < SieveCert.n, ∀ l < SieveCert.n, counted4 i j k l = true →
      S4 x i j k l ≤ ((bound4 (SieveCert.e i) (SieveCert.e j) (SieveCert.e k) (SieveCert.e l) : ℝ) / K + δ') * X) :
    dropS x i j - (if cand i j = true ∧ dec i j = false ∧ reg2 i j = true then
        ((sub2 i j : ℝ) / K - SieveCert.n * δ') * X else 0) ≤
      (cost2 i j : ℝ) / K * X + δ' * (1 + SieveCert.n + SieveCert.n * SieveCert.n) * X := by
  have hK : (0 : ℝ) < K := SieveCert.K_pos'
  have hd := dropS_le_cost hδ' hX h2 h4
  have hnδ : 0 ≤ (SieveCert.n : ℝ) * δ' * X := by positivity
  have hexp : δ' * (1 + SieveCert.n + SieveCert.n * SieveCert.n) * X =
      δ' * (1 + SieveCert.n * SieveCert.n) * X + SieveCert.n * δ' * X := by ring
  by_cases h : cand i j = true ∧ dec i j = false ∧ reg2 i j = true
  · rw [ite_eq_left h, hexp]
    rw [SieveCert.cost_of_not_dec h.1 h.2.1] at hd
    have hc := SieveCert.cost2_ge h.1 h.2.1
    have hc' : (bound2 (SieveCert.e i) (SieveCert.e j) : ℝ) / K * X - (sub2 i j : ℝ) / K * X ≤
        (cost2 i j : ℝ) / K * X := by
      have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc hK.le) hX
      rwa [sub_div, sub_mul] at this
    have hs : ((sub2 i j : ℝ) / K - SieveCert.n * δ') * X = (sub2 i j : ℝ) / K * X - SieveCert.n * δ' * X := by
      ring
    rw [hs]
    linarith
  · rw [ite_eq_right h, sub_zero, cost2_eq_cost h, hexp]
    linarith

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
/-- The refined total in the reals: if `total2/K ≤ c` in the reals (`htot`), then for `X ≥ 0`,
`Σ_{i,j} (cost2/K)X ≤ cX`. -/
theorem sum_cost2_div_of {c : ℝ} (htot : (total2 : ℝ) / K ≤ c) (X : ℝ) (hX : 0 ≤ X) :
    ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (cost2 i j : ℝ) / K * X ≤ c * X := by
  have hsum : ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (cost2 i j : ℝ) / K * X =
      (total2 : ℝ) / K * X := by
    rw [SieveCert.total2_eq]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
  rw [hsum]
  exact mul_le_mul_of_nonneg_right htot hX

/-- **The dropped terms less the kept parts, for large `q`**: for a route with `RouteOK` and a grid with `GridOK` that
fit (`Fits`), if `total2/K ≤ c` in the reals (`htot`), then for `ε > 0`,
`D1(g_B) − Kp(g_B) ≤ φ(q)⁻¹(c + ε)x/log x`. -/
theorem drop_ev2 {c : ℝ} (htot : (total2 : ℝ) / K ≤ c) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop, LargeQ q →
    (parQ q).D1 (gB q) - (parQ q).Kp (gB q) ≤ (q.totient : ℝ)⁻¹ * ((c + ε) * (xq q / Real.log (xq q))) := by
  have hn : (0 : ℝ) < SieveCert.n := by exact_mod_cast SieveCert.n_pos
  set M : ℝ := (SieveCert.n : ℝ) * SieveCert.n * (1 + SieveCert.n + SieveCert.n * SieveCert.n) with hM
  have hM0 : 0 < M := by positivity
  set δ' : ℝ := ε / (2 * M) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hKev : ∀ᶠ q : ℕ in atTop, ∀ i ∈ range SieveCert.n, ∀ j ∈ range SieveCert.n, reg2 i j = true →
      LargeQ q → (q.totient : ℝ)⁻¹ * (((sub2 i j : ℝ) / K - SieveCert.n * δ') * (xq q / Real.log (xq q))) ≤
        (parQ q).Kp2 (gB q) i j := by
    rw [Filter.eventually_all_finset]
    intro i _
    rw [Filter.eventually_all_finset]
    intro j _
    by_cases hr : reg2 i j = true
    · filter_upwards [Kp2_gB_ge hr hδ'0] with q hq _
      exact hq
    · exact Filter.Eventually.of_forall fun q h => absurd h hr
  filter_upwards [tendsto_xq.eventually (shares_ev hδ'0), corner_ev (half_pos hε), eventually_ge_atTop 1, hKev]
    with q hS hC hq1 hKq hL
  have G := good_of_large hL
  set X := xq q / Real.log (xq q) with hX
  have hx1 : 1 < xq q := G.hx
  have hX0 : 0 ≤ X := div_nonneg (by linarith) (Real.log_nonneg hx1.le)
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  -- the kept parts, from below
  have hKp : (q.totient : ℝ)⁻¹ * ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n,
      (if cand i j = true ∧ dec i j = false ∧ reg2 i j = true then ((sub2 i j : ℝ) / K - SieveCert.n * δ') * X
        else 0) ≤ (parQ q).Kp (gB q) := by
    rw [Finset.mul_sum]
    unfold Par.Kp
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    by_cases hW : Par.inW i
    · rw [ite_eq_left hW]
      refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_)
      rw [ite_eq_right (show ¬(cand i j = true ∧ dec i j = false ∧ reg2 i j = true) from
        fun h => not_inW_of_cand h.1 hW), mul_zero]
    · rw [ite_eq_right hW]
      refine Finset.sum_le_sum fun j hj => ?_
      split_ifs with h
      · exact hKq i hi j hj h.2.2 hL
      · rw [mul_zero]
  -- each cell against its refined cost
  have hdrop : ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (dropS (xq q) i j -
      (if cand i j = true ∧ dec i j = false ∧ reg2 i j = true then ((sub2 i j : ℝ) / K - SieveCert.n * δ') * X
        else 0)) ≤ c * X + ε / 2 * X := by
    calc _ ≤ ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n,
            ((cost2 i j : ℝ) / K * X + δ' * (1 + SieveCert.n + SieveCert.n * SieveCert.n) * X) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          obtain ⟨h2, h4⟩ := hS i hi j hj
          exact dropS_sub_le_cost2 hδ'0.le hX0 h2 fun k hk l hl hc => h4 k (Finset.mem_range.2 hk) l
            (Finset.mem_range.2 hl) hc
      _ = ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (cost2 i j : ℝ) / K * X +
            SieveCert.n * SieveCert.n * (δ' * (1 + SieveCert.n + SieveCert.n * SieveCert.n) * X) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ c * X + ε / 2 * X := by
          have h1 := sum_cost2_div_of htot X hX0
          have h2 : (SieveCert.n : ℝ) * SieveCert.n * (δ' * (1 + SieveCert.n + SieveCert.n * SieveCert.n) * X) =
              ε / 2 * X := by
            rw [hδ']
            field_simp
            rw [hM]
            ring
          linarith
  calc (parQ q).D1 (gB q) - (parQ q).Kp (gB q)
      ≤ (q.totient : ℝ)⁻¹ * (∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, dropS (xq q) i j +
          (SieveCert.n : ℝ) ^ 2 * ((cornerP (parQ q).ztop).card : ℝ) ^ 2) -
        (q.totient : ℝ)⁻¹ * ∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n,
          (if cand i j = true ∧ dec i j = false ∧ reg2 i j = true then ((sub2 i j : ℝ) / K - SieveCert.n * δ') * X
            else 0) := sub_le_sub (D1_le G hC.1 hq1) hKp
    _ = (q.totient : ℝ)⁻¹ * (∑ i ∈ range SieveCert.n, ∑ j ∈ range SieveCert.n, (dropS (xq q) i j -
          (if cand i j = true ∧ dec i j = false ∧ reg2 i j = true then ((sub2 i j : ℝ) / K - SieveCert.n * δ') * X
            else 0)) + (SieveCert.n : ℝ) ^ 2 * ((cornerP (parQ q).ztop).card : ℝ) ^ 2) := by
        simp only [Finset.sum_sub_distrib]
        ring
    _ ≤ (q.totient : ℝ)⁻¹ * ((c * X + ε / 2 * X) + ε / 2 * X) :=
        mul_le_mul_of_nonneg_left (add_le_add hdrop hC.2) hφ
    _ = (q.totient : ℝ)⁻¹ * ((c + ε) * X) := by ring

end SieveDrop2

#print axioms SieveDrop2.Kp2_gB_ge
#print axioms SieveDrop2.dropS_sub_le_cost2
#print axioms SieveDrop2.drop_ev2
