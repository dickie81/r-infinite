/-
# Round 709: Linnik's theorem by the sieve route, under the refined certificate

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK` and `Fits`).

* `route_of_large`: if for large `q` every unit `a` mod `q` has a prime `p ≡ a (mod q)` with `q^L < p ≤ 2q^L`, there
  is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^L`.
* `linnik_large2`: given the route's Type II estimate (`hII`) and the refined certificate's total `total2/K ≤ c` in the
  reals for some `c < 1` (`htot`), there is `q₀` such that for `q ≥ q₀` and `a` a unit mod `q` there is a prime
  `p ≡ a (mod q)` with `q^L < p ≤ 2q^L`.
* `linnik_route2`: given `hII` and `htot`, there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there
  is a prime `p ≡ a (mod q)` with `p ≤ K·q^L`; `linnik_route_lt2`: the same for `total2 < K`.

The proof is `SieveMain.linnik_large_of`'s, with `SieveBuch.Par.decompk` (the decomposition with the kept parts) for
`SieveBuch.Par.decomp`, `SieveKeptLeaf.leaves_ev2` (with the kept leaves) for `SieveQ.leaves_ev`,
`SieveDrop2.drop_ev2` (the dropped terms less the kept parts) for `SieveDrop.drop_ev_of`, and the decomposition's
constant `Ck = 1 + n(1 + n(n(n + 2) + 2 + 3n))` for `Cdec`; `route_of_large` is `SieveMain.linnik_route_of`'s step
for the small moduli (Mathlib's `Nat.forall_exists_prime_gt_and_modEq`, Dirichlet's theorem).

The file imports `SieveDrop2.lean`.
-/
import SieveDrop2

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveDrop SieveRoute

namespace SieveMain2

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-- The decomposition's constant with the kept parts, `1 + n(1 + n(n(n + 2) + 2 + 3n))`. -/
noncomputable def Ck : ℝ :=
  1 + SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2 + 3 * SieveCert.n))

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem Ck_pos : 0 < Ck := by unfold Ck; positivity

omit [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- **The small moduli.** If for large `q` every unit `a` mod `q` has a prime `p ≡ a (mod q)` with `q^L < p ≤ 2q^L`
(`hlarge`), there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
`p ≤ K·q^L`: Dirichlet's theorem gives a prime for each of the finitely many smaller `q` and residues, and `K` is the
larger of `2` and their maximum. -/
theorem route_of_large (hL0 : 0 ≤ L) (hlarge : ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L := by
  obtain ⟨q₀, hq₀⟩ := hlarge
  -- small moduli: one prime per residue, by Dirichlet's theorem
  let f : ℕ × ℕ → ℕ := fun x =>
    if h : x.1 ≠ 0 ∧ x.2.Coprime x.1 then Classical.choose (Nat.forall_exists_prime_gt_and_modEq 0 h.1 h.2)
    else 0
  have hf : ∀ x : ℕ × ℕ, ∀ h : x.1 ≠ 0 ∧ x.2.Coprime x.1, (f x).Prime ∧ f x ≡ x.2 [MOD x.1] := by
    intro x h
    have hs := Classical.choose_spec (Nat.forall_exists_prime_gt_and_modEq 0 h.1 h.2)
    simp only [f, dite_eq_left h]
    exact ⟨hs.2.1, hs.2.2⟩
  set M : ℕ := (Finset.range q₀ ×ˢ Finset.range q₀).sup f with hM
  refine ⟨max 2 (M : ℝ), fun q _ a ha => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqL : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 hL0
  by_cases hq : q₀ ≤ q
  · have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
    obtain ⟨p, hp, hpa, -, hpx⟩ := hq₀ q hq (a : ZMod q) hu
    refine ⟨p, hp, (ZMod.natCast_eq_natCast_iff p a q).1 hpa, hpx.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push Not at hq
    set r := a % q with hr
    have hq0 : q ≠ 0 := NeZero.ne q
    have hrc : r.Coprime q := by
      rw [hr]
      unfold Nat.Coprime
      rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact ha
    have hrq : r < q := Nat.mod_lt a (Nat.pos_of_ne_zero hq0)
    obtain ⟨hp, hpr⟩ := hf (q, r) ⟨hq0, hrc⟩
    refine ⟨f (q, r), hp, hpr.trans (Nat.mod_modEq a q), ?_⟩
    have hmem : (q, r) ∈ Finset.range q₀ ×ˢ Finset.range q₀ :=
      Finset.mem_product.2 ⟨Finset.mem_range.2 hq, Finset.mem_range.2 (by omega)⟩
    have hle : f (q, r) ≤ M := Finset.le_sup (f := f) hmem
    have hle' : (f (q, r) : ℝ) ≤ max 2 (M : ℝ) := by
      have : (f (q, r) : ℝ) ≤ M := by exact_mod_cast hle
      exact this.trans (le_max_right _ _)
    calc (f (q, r) : ℝ) ≤ max 2 (M : ℝ) := hle'
      _ = max 2 (M : ℝ) * 1 := (mul_one _).symm
      _ ≤ max 2 (M : ℝ) * (q : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left hqL (le_trans (by norm_num) (le_max_left _ _))

/-- **Linnik's theorem at `x = q^L`, for large `q`, under the refined certificate.** For a route with `RouteOK` and a
grid with `GridOK` that fit (`Fits`), given the route's Type II estimate (`hII`) and `total2/K ≤ c` in the reals for
some `c < 1` (`htot`), there is `q₀` such that for `q ≥ q₀` and `a` a unit mod `q` there is a prime `p ≡ a (mod q)`
with `q^L < p ≤ 2q^L`. The losses are `SieveMain.linnik_large_of`'s five shares `ε = (1 − c)/10` of `X = x/log x`,
leaving `(1 − c)X/2` of `S(A, z_top)`. -/
theorem linnik_large2 (hII : TypeIIAt) {c : ℝ} (hc : c < 1) (htot : (SieveCert.total2 : ℝ) / SieveCert.K ≤ c) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L := by
  have hC := Ck_pos
  have hL0 : 0 < L := L_pos
  set ε : ℝ := (1 - c) / 10 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set η : ℝ := ε / (Ck * L) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ, hδ, q₁, hlv⟩ := SieveKeptLeaf.leaves_ev2 hII hη0
  have hev1 := SieveMain.ev_log_le (c := ε / (Ck * L)) (by positivity) hδ
  have hev2 := SieveMain.ev_log_le (c := ε / L) (by positivity) (show (0 : ℝ) < L - 1 by linarith [two_lt_L])
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 ((SieveMain.TB_ev hε).and
    ((SieveDrop2.drop_ev2 htot hε).and (hev1.and (hev2.and (eventually_ge_atTop 3)))))
  refine ⟨q₁ + q₂, fun q _ hq a ha => ?_⟩
  obtain ⟨hTB, hD, h1, h2, hq3⟩ := hq₂ q (by omega)
  obtain ⟨hL, Lv, KL⟩ := hlv q (by omega) a ha
  have G := good_of_large hL
  have hq3' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  have hdec := (parQ q).decompk G (gA_nonneg q a) (Err_nonneg hη0 δ q (by omega)) Lv KL
  have hTB := hTB hL
  have hD := hD hL
  -- `X = x/log x = q^L/(L log q)`
  set Q := (q : ℝ) ^ L with hQ
  have hQ0 : 0 < Q := by positivity
  have hlogx : Real.log (xq q) = L * Real.log q := Real.log_rpow hq0 _
  set X := xq q / Real.log (xq q) with hXdef
  have hX : X = Q / (L * Real.log q) := by rw [hXdef, hlogx]
  have hX0 : 0 < X := by rw [hX]; positivity
  -- the leaves' error: `Ck·Err ≤ φ⁻¹(εX + εX)`
  have hErr : Ck * Err η δ q ≤ (q.totient : ℝ)⁻¹ * (ε * X + ε * X) := by
    have hsplit : (q : ℝ) ^ (L - δ) * (q : ℝ) ^ δ = Q := by
      rw [← Real.rpow_add hq0, sub_add_cancel]
    have hd0 : 0 < (q : ℝ) ^ δ := by positivity
    have hA : Ck * (η * Q / (q.totient * Real.log q)) = (q.totient : ℝ)⁻¹ * (ε * X) := by
      rw [hX, hη]
      field_simp
    have hB : Ck * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) ≤ (q.totient : ℝ)⁻¹ * (ε * X) := by
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ hφ.le
      rw [hX, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      have h1' : Ck * L * Real.log q ≤ ε * (q : ℝ) ^ δ := by
        have := h1
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
        linarith
      calc Ck * (q : ℝ) ^ (L - δ) * (L * Real.log q)
          = (q : ℝ) ^ (L - δ) * (Ck * L * Real.log q) := by ring
        _ ≤ (q : ℝ) ^ (L - δ) * (ε * (q : ℝ) ^ δ) := mul_le_mul_of_nonneg_left h1' (by positivity)
        _ = ε * Q := by rw [← hsplit]; ring
    unfold SieveQ.Err
    rw [mul_add]
    linarith
  -- `q ≤ εX`
  have hqX : (q : ℝ) ≤ ε * X := by
    rw [hX, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have h2' : L * Real.log q ≤ ε * (q : ℝ) ^ (L - 1) := by
      have := h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
      linarith
    have hsplit : (q : ℝ) * (q : ℝ) ^ (L - 1) = Q := by
      rw [← Real.rpow_one_add' hq0.le (by rw [add_sub_cancel]; exact hL0.ne'), add_sub_cancel]
    calc (q : ℝ) * (L * Real.log q) ≤ (q : ℝ) * (ε * (q : ℝ) ^ (L - 1)) := mul_le_mul_of_nonneg_left h2' hq0.le
      _ = ε * Q := by rw [← hsplit]; ring
  -- `S(A, z_top) > 0`: what is left is `(1 − c − 5ε)X = (1 − c)X/2`
  have hpos : 0 < (parQ q).T (gA q a) := by
    have : (q.totient : ℝ)⁻¹ * ((1 - c) / 2 * X) ≤ (parQ q).T (gA q a) := by
      have e1 : (q.totient : ℝ)⁻¹ * ((1 - ε) * X - q) - (q.totient : ℝ)⁻¹ * ((c + ε) * X) -
          (q.totient : ℝ)⁻¹ * (ε * X + ε * X) ≤ (parQ q).T (gA q a) := by
        unfold Ck at hErr
        linarith
      have e2 : (q.totient : ℝ)⁻¹ * ((1 - c) / 2 * X) ≤ (q.totient : ℝ)⁻¹ * ((1 - ε) * X - q) -
          (q.totient : ℝ)⁻¹ * ((c + ε) * X) - (q.totient : ℝ)⁻¹ * (ε * X + ε * X) := by
        have : (1 - c) / 2 * X ≤ ((1 - ε) * X - q) - ((c + ε) * X) - (ε * X + ε * X) := by
          rw [hεdef] at hqX ⊢
          linarith
        nlinarith
      linarith
    have : 0 < (q.totient : ℝ)⁻¹ * ((1 - c) / 2 * X) := by
      have : 0 < (1 - c) / 2 * X := mul_pos (by linarith) hX0
      positivity
    linarith
  -- a term of `S(A, z_top)` is positive: a prime `≡ a`
  unfold Par.T at hpos
  obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  have hmA : (m : ZMod q) = a := by
    by_contra h
    simp [gA, h] at hm0
  have hmr : SieveTree.rough (parQ q).ztop m := by
    by_contra h
    simp [h] at hm0
  rw [Finset.mem_Ioc] at hm
  have hN1 : 1 ≤ N1 q := Nat.le_floor (by simpa using (Real.one_le_rpow hq1.le hL0.le : (1 : ℝ) ≤ xq q))
  have hm2 : 2 ≤ m := by have := hm.1; change N1 q < m at this; omega
  refine ⟨m, ?_, hmA, Nat.lt_of_floor_lt hm.1, ?_⟩
  · by_contra hnp
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hmin := (SieveStops2.rough_iff_le_minFac hm2).1 hmr
    have hz : N2 q < ((parQ q).ztop) ^ 2 := by
      show N2 q < (Nat.sqrt (N2 q) + 1) ^ 2
      exact Nat.lt_succ_sqrt' _
    have : (parQ q).ztop ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hmin 2
    have := hm.2
    change m ≤ N2 q at this
    omega
  · have : (m : ℝ) ≤ N2 q := by exact_mod_cast hm.2
    exact this.trans (N2_le q)

/-- **Linnik's theorem with exponent `L`, under the refined certificate.** For a route with `RouteOK` and a grid with
`GridOK` that fit (`Fits`), given the route's Type II estimate (`hII`) and `total2/K ≤ c` in the reals for some `c < 1`
(`htot`), there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
`p ≤ K·q^L`. -/
theorem linnik_route2 (hII : TypeIIAt) {c : ℝ} (hc : c < 1) (htot : (SieveCert.total2 : ℝ) / SieveCert.K ≤ c) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L :=
  route_of_large L_pos.le (linnik_large2 hII hc htot)

/-- **Linnik's theorem with exponent `L`, under a refined certificate whose total is below `K`.** For a route with
`RouteOK` and a grid with `GridOK` that fit (`Fits`), given the route's Type II estimate (`hII`) and the refined
certificate's total less than `K` (`htot`), there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there
is a prime `p ≡ a (mod q)` with `p ≤ K·q^L`. -/
theorem linnik_route_lt2 (hII : TypeIIAt) (htot : SieveCert.total2 < SieveCert.K) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L :=
  linnik_route2 hII (SieveCert.total2_div_lt htot) le_rfl

end SieveMain2

#print axioms SieveMain2.route_of_large
#print axioms SieveMain2.linnik_route_lt2
