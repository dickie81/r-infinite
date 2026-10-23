/-
# Round 707: the decomposition with the kept parts of the dropped cells

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. `SieveBuch.Par.decomp` bounds `S(A, z_top)` from below by `S(B, z_top)` less the dropped `B`-terms
`D1(g_B)` and the leaves' errors; at a dropped candidate cell of depth 2 its proof uses only `A ≥ 0`. Here a dropped
candidate cell `(i, j)` of the region `SieveCert.reg2` uses `A ≥ Kp2(g_A)` instead (`SieveBuch.Par.Kp2_le`), and the
kept parts' `A` and `B` agree within the leaves' errors, so the kept parts' `B`-count comes off the dropped terms.

* `Kp`: all kept parts, below the dropped candidate cells of `reg2` and the cells `i` of `p₁` outside the window.
* `KLeaves`: every kept part `Kk(i, j, k)` of a cell `k` that `keep` passes below such a cell has its `A` and `B`
  within `3·Err` (three sorted families, `SieveBuch.Par.Kk_eq`).
* `lvl2k`, `lvl1k`, `decompk`: `SieveBuch.Par.lvl2`, `lvl1` and `decomp` with the kept parts: for a grid with
  `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, leaves within `Err ≥ 0` and kept leaves within `3·Err`,
  `S_{g_A}(z_top) ≥ S_{g_B}(z_top) − (D1(g_B) − Kp(g_B)) − (1 + n(1 + n(n(n + 2) + 2 + 3n)))·Err`.

The file imports `SieveKept.lean`.
-/
import SieveKept

open Real Finset SieveFamily SieveChain SieveDecomp
open SieveCert (V DEN H U1 U2 cand dec inKK ne3 counted4 surelyEval cell keep reg2)

namespace SieveBuch

namespace Par

open Classical

variable (P : Par) [SieveCert.Grid]

/-- All kept parts: below the dropped candidate cells `(i, j)` of `reg2`, for the cells `i` of `p₁` outside the
window. -/
noncomputable def Kp (g : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range SieveCert.n, if inW i then 0 else ∑ j ∈ range SieveCert.n,
    (if cand i j = true ∧ dec i j = false ∧ reg2 i j = true then P.Kp2 g i j else 0)

/-- The kept leaves: each kept part's `A` and `B` within `3·Err`. -/
def KLeaves (gA gB : ℕ → ℝ) (Err : ℝ) : Prop :=
  ∀ i < SieveCert.n, ∀ j < SieveCert.n, cand i j = true → dec i j = false → reg2 i j = true →
    ∀ k < SieveCert.n, keep i j k = true → |P.Kk gA i j k - P.Kk gB i j k| ≤ 3 * Err

variable {P}

/-- A dropped candidate cell's kept parts: `Kp2(g_B) − 3n·Err ≤ Kp2(g_A)`. -/
theorem Kp2_ge {gA gB : ℕ → ℝ} {Err : ℝ} (hErr : 0 ≤ Err) (KL : P.KLeaves gA gB Err) {i j : ℕ}
    (hi : i < SieveCert.n) (hj : j < SieveCert.n) (hc : cand i j = true) (hd : dec i j = false)
    (hr : reg2 i j = true) :
    P.Kp2 gB i j - 3 * SieveCert.n * Err ≤ P.Kp2 gA i j := by
  unfold Kp2
  have hErrs : 3 * (SieveCert.n : ℝ) * Err = ∑ _k ∈ range SieveCert.n, 3 * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun k hk => ?_
  split_ifs with hkp
  · have := abs_le.1 (KL i hi j hj hc hd hr k (Finset.mem_range.1 hk) hkp)
    linarith [this.1]
  · linarith

/-- **Level 2 with the kept parts**, for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, leaves within
`Err ≥ 0`, kept leaves within `3·Err`, and a cell `i < n` of `p₁` not inside the window:
`A ≥ B − (dropped) + (kept) − n(n(n + 2) + 2 + 3n)Err`. -/
theorem lvl2k [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    (Lv : P.Leaves gA gB Err) (KL : P.KLeaves gA gB Err) {i : ℕ} (hi : i < SieveCert.n) (hW : ¬ inW i) :
    P.I gB (P.S2 i) - P.D2 gB i + ∑ j ∈ range SieveCert.n,
        (if cand i j = true ∧ dec i j = false ∧ reg2 i j = true then P.Kp2 gB i j else 0) -
      SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2 + 3 * SieveCert.n) * Err ≤ P.I gA (P.S2 i) := by
  rw [P.I_S2 G gA, P.I_S2 G gB]
  unfold D2
  set c3 : ℝ := SieveCert.n * (SieveCert.n + 2) with hc3
  have hc30 : 0 ≤ c3 := by positivity
  have hn0 : (0 : ℝ) ≤ SieveCert.n := Nat.cast_nonneg _
  have hErrs : (SieveCert.n : ℝ) * (c3 + 2 + 3 * SieveCert.n) * Err =
      ∑ _j ∈ range SieveCert.n, (c3 + 2 + 3 * SieveCert.n) * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hA0 := famI_nonneg hgA P.N₁ P.N₂ (famSet 2 P.N₂ (P.S2c i j))
  have hE0 : 0 ≤ (c3 + 2 + 3 * SieveCert.n) * Err := by positivity
  have hE1 : (c3 + 2) * Err ≤ (c3 + 2 + 3 * SieveCert.n) * Err := by nlinarith
  by_cases hc : cand i j = true
  · by_cases hd : dec i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false)) by
          simp [hc, hd]),
        ite_eq_left (show cand i j = true ∧ dec i j = true from ⟨hc, hd⟩),
        ite_eq_right (show ¬(cand i j = true ∧ dec i j = false ∧ reg2 i j = true) by simp [hd]),
        P.I_S2c gA, P.I_S2c gB, P.I_S2le gA, P.I_S2le gB]
      have h3 := lvl3 G hgA hErr Lv hi hj' ⟨hc, hd⟩
      have hJ := abs_le.1 (Lv.p2 i hi j hj' hc hd)
      have hE := abs_le.1 (Lv.e2 i hi j hj' hc hd)
      rw [← hc3] at h3
      have : (c3 + 2) * Err = c3 * Err + 2 * Err := by ring
      linarith [hJ.1, hE.1]
    · have hd' : dec i j = false := by simpa using hd
      rw [ite_eq_left (show (cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inl ⟨hc, hd'⟩),
        ite_eq_right (show ¬(cand i j = true ∧ dec i j = true) from fun h => hd h.2)]
      by_cases hr : reg2 i j = true
      · rw [ite_eq_left (show cand i j = true ∧ dec i j = false ∧ reg2 i j = true from ⟨hc, hd', hr⟩)]
        have hK := Kp2_ge hErr KL hi hj' hc hd' hr
        have hle := P.Kp2_le G.hx hgA i j
        have : 3 * (SieveCert.n : ℝ) * Err ≤ (c3 + 2 + 3 * SieveCert.n) * Err := by nlinarith
        linarith
      · rw [ite_eq_right (show ¬(cand i j = true ∧ dec i j = false ∧ reg2 i j = true) from fun h => hr h.2.2)]
        unfold I at hA0 ⊢
        linarith
  · rw [ite_eq_right (show ¬(cand i j = true ∧ dec i j = true) from fun h => hc h.1),
      ite_eq_right (show ¬(cand i j = true ∧ dec i j = false ∧ reg2 i j = true) from fun h => hc h.1)]
    by_cases hs : sE2 i j = true
    · rw [ite_eq_right (show ¬((cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false)) by
          simp [hc, hs])]
      have hE := abs_le.1 (Lv.e2' i hi hW j hj' (by simpa using hc) hs)
      have : Err ≤ (c3 + 2 + 3 * SieveCert.n) * Err := le_mul_of_one_le_left hErr (by linarith)
      linarith [hE.1]
    · rw [ite_eq_left (show (cand i j = true ∧ dec i j = false) ∨ (cand i j = false ∧ sE2 i j = false) from
          Or.inr ⟨by simpa using hc, by simpa using hs⟩)]
      unfold I at hA0 ⊢
      linarith

/-- **Level 1 with the kept parts**, for a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and `g_B`, leaves within
`Err ≥ 0` and kept leaves within `3·Err`: `A ≤ B + (dropped) − (kept) + n(1 + n(n(n + 2) + 2 + 3n))Err`. -/
theorem lvl1k [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    (Lv : P.Leaves gA gB Err) (KL : P.KLeaves gA gB Err) :
    P.I gA P.S1 ≤ P.I gB P.S1 + P.D1 gB - P.Kp gB +
      SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2 + 3 * SieveCert.n)) * Err := by
  rw [P.I_S1 G gA, P.I_S1 G gB]
  unfold D1 Kp
  set c2 : ℝ := SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2 + 3 * SieveCert.n) with hc2
  have hc20 : 0 ≤ c2 := by positivity
  have hErrs : (SieveCert.n : ℝ) * (1 + c2) * Err = ∑ _i ∈ range SieveCert.n, (1 + c2) * Err := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hErrs, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  by_cases hW : inW i
  · rw [ite_eq_left hW, ite_eq_left hW]
    have hE := abs_le.1 (Lv.e1 i hi' hW)
    have : Err ≤ (1 + c2) * Err := le_mul_of_one_le_left hErr (by linarith)
    linarith [hE.2]
  · rw [ite_eq_right hW, ite_eq_right hW, P.I_S1c gA, P.I_S1c gB]
    have h2 := lvl2k G hgA hErr Lv KL hi' hW
    have hJ := abs_le.1 (Lv.p1 i hi' hW)
    rw [← hc2] at h2
    have : (1 + c2) * Err = Err + c2 * Err := by ring
    linarith [hJ.2]

/-- **The decomposition's inequality with the kept parts.** For a grid with `GridOK`, `P.Good`, weights `g_A ≥ 0` and
`g_B`, leaves within `Err ≥ 0` and kept leaves within `3·Err`:
`S(A, z_top) ≥ S(B, z_top) − (D1(g_B) − Kp(g_B)) − C·Err`, `C = 1 + n(1 + n(n(n + 2) + 2 + 3n))`. -/
theorem decompk [SieveCert.GridOK] (G : P.Good) {gA gB : ℕ → ℝ} (hgA : ∀ m, 0 ≤ gA m) {Err : ℝ} (hErr : 0 ≤ Err)
    (Lv : P.Leaves gA gB Err) (KL : P.KLeaves gA gB Err) :
    P.T gB - (P.D1 gB - P.Kp gB) -
        (1 + SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2 + 3 * SieveCert.n))) * Err ≤
      P.T gA := by
  rw [P.T_eq G gA, P.T_eq G gB]
  have h1 := lvl1k G hgA hErr Lv KL
  have hJ := abs_le.1 Lv.j0
  set c1 : ℝ := SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2 + 3 * SieveCert.n)) with hc1
  have : (1 + c1) * Err = Err + c1 * Err := by ring
  linarith [hJ.1]

end Par

end SieveBuch

#print axioms SieveBuch.Par.decompk
