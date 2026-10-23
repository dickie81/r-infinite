/-
# Round 604: Linnik's theorem by the sieve route, and with exponent `2333/1000` (milestones M8 and §0)

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statements. The route and the grid are as in `SieveQ` (`RouteOK`, `GridOK` and `Fits`).

* `primes_dyadic_ge`: for `ε > 0`, the primes of `(⌊x⌋, ⌊2x⌋]` number at least `(1 − ε)x/log x` for large `x`.
* `TB_ev`: for `ε > 0`, `S(B, z_top) ≥ φ(q)⁻¹((1 − ε)x/log x − q)` for large `q`, at `x = q^L`.
* `linnik_large`: given the route's Type II estimate (`hII`) and the certificate's total at most `0.88K` (`htot`), there
  is `q₀` such that for `q ≥ q₀` and `a` a unit mod `q` there is a prime `p ≡ a (mod q)` with `q^L < p ≤ 2q^L`.
* `linnik_route`: given `hII` and `htot`, there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a
  prime `p ≡ a (mod q)` with `p ≤ K·q^L`.
* `linnik_large_of`, `linnik_route_of` (round 619): the same with the certificate's loss as a parameter, `total/K ≤ c`
  in the reals for some `c < 1`; `linnik_route_lt`: `linnik_route_of` at `c = total/K` for `total < K`.
* `linnik_2333`: `linnik_route` at `SieveRoute.route2333` and `SieveCert.grid2333`, which fit (`fits2333`), with
  `SieveRoute.typeII2333` and `SieveCert.total_le_2333`: there is `K` such that for every `q ≥ 1` and every `a` prime to
  `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{2333/1000}`.

This is the theorem of `frontier/linnik/SIEVE-ROUTE.md` §0 at `x = q^L`, assembled as §13's M8 plans.

The proof:

* `primes_dyadic_ge`: `SieveRough.theta_near` at `x` and `2x`. `TB_ev`: `z_top = ⌊√N₂⌋ + 1`, so the `z_top`-rough
  `n ∈ (N₁, N₂]` are the primes there, and at most `ω(q) ≤ q` of them divide `q`.
* `linnik_large_of` (round 619; `linnik_large` is its case `c = 0.88`): `SieveBuch.Par.decomp` with
  `SieveQ.leaves_ev`, `SieveDrop.drop_ev_of` and `TB_ev`, with `ε = (1 − c)/10` and `η = ε/(Cdec·L)`. For large `q` the
  leaves' error `Cdec·Err` is at most `2εx/(φ(q) log x)` and `q ≤ εx/log x`, so
  `S(A, z_top) ≥ (1 − c)x/(2φ(q) log x) > 0` (until round 619 the proof set `ε = 1/100` and `η = 1/(100·Cdec·L)` at
  `c = 0.88` and kept `0.07x/(φ(q) log x)`). A `z_top`-rough `n ∈ (N₁, N₂]` is prime.
* `linnik_route`: for `q < q₀`, Mathlib's `Nat.forall_exists_prime_gt_and_modEq` (Dirichlet's theorem) gives a prime for
  each of the finitely many `q` and residues, and `K` is the larger of `2` and their maximum.

Round 607 made the route's numbers and the certificate's grid parameters, and the Type II estimate and the
certificate's total hypotheses; round 604's theorem is their case `linnik_2333`.


The file imports `SieveDrop.lean`.
-/
import SieveDrop

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveRough SieveDrop SieveRoute
open scoped Chebyshev

namespace SieveMain

open Classical

variable [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits]

/-! ### `S(B, z_top)`: the primes of `(x, 2x]` prime to `q` -/

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- For `ε > 0`, the primes of `(⌊x⌋, ⌊2x⌋]` number at least `(1 − ε)x/log x` for large `x`. -/
theorem primes_dyadic_ge {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop,
    (1 - ε) * (x / Real.log x) ≤ (((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime).card : ℝ) := by
  have hT := theta_near (ε := 1) one_pos
  have hT2 : ∀ᶠ x : ℝ in atTop, |θ (2 * x) - 2 * x| ≤ 1 * (2 * x) / Real.log (2 * x) :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually hT
  filter_upwards [hT, hT2, eventually_ge_atTop (Real.exp (4 / ε)), eventually_ge_atTop (Real.exp 1)]
    with x h1 h2 h3 h4
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) h4
  have hlx1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) h4
  have hlx : 4 / ε ≤ Real.log x := by
    rw [← Real.log_exp (4 / ε)]
    exact Real.log_le_log (Real.exp_pos _) h3
  have hl2 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2x : Real.log x ≤ Real.log (2 * x) := by linarith
  -- `Σ log p = θ(2x) − θ(x) ≥ x − 3x/log x`
  have hsum := sum_log_primes_dyadic hx0.le
  set P := (Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime with hP
  have hθ : x - 3 * x / Real.log x ≤ θ (2 * x) - θ x := by
    have e1 := (abs_le.1 h1).2
    have e2 := (abs_le.1 h2).1
    have e3 : 1 * (2 * x) / Real.log (2 * x) ≤ 2 * x / Real.log x := by
      rw [one_mul]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) hl2x
    have e4 : 1 * x / Real.log x = x / Real.log x := by ring
    have e5 : 3 * x / Real.log x = 2 * x / Real.log x + x / Real.log x := by ring
    linarith
  have hle : ∑ p ∈ P, Real.log p ≤ (P.card : ℝ) * Real.log (2 * x) := by
    have : ∀ p ∈ P, Real.log p ≤ Real.log (2 * x) := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      exact Real.log_le_log hp0 ((Nat.cast_le.2 hp.1.2).trans (Nat.floor_le (by linarith)))
    calc ∑ p ∈ P, Real.log p ≤ ∑ _p ∈ P, Real.log (2 * x) := Finset.sum_le_sum this
      _ = (P.card : ℝ) * Real.log (2 * x) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlx0 : 0 < Real.log x := by linarith
  have h2x0 : 0 < Real.log (2 * x) := by linarith
  -- `(1 − ε)(x/log x)·log 2x ≤ x − 3x/log x`
  have hkey : (1 - ε) * (x / Real.log x) * Real.log (2 * x) ≤ x - 3 * x / Real.log x := by
    rw [hl2]
    have h5 : (1 - ε) * (x / Real.log x) * (Real.log 2 + Real.log x) =
        (1 - ε) * x + (1 - ε) * x * Real.log 2 / Real.log x := by
      field_simp
      ring
    rw [h5]
    have h6 : ε * Real.log x ≥ 4 := by
      rw [div_le_iff₀ hε] at hlx
      linarith
    have h7 : (1 - ε) * x * Real.log 2 / Real.log x + 3 * x / Real.log x ≤ ε * x := by
      rw [← add_div, div_le_iff₀ hlx0]
      have hA : x * 4 ≤ x * (ε * Real.log x) := mul_le_mul_of_nonneg_left h6 hx0.le
      have hB : (1 - ε) * Real.log 2 ≤ 1 := by
        by_cases hε1 : ε ≤ 1
        · have : (1 - ε) * Real.log 2 ≤ 1 * Real.log 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hlog20.le
          linarith
        · have : (1 - ε) * Real.log 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog20.le
          linarith
      have hC : x * ((1 - ε) * Real.log 2) ≤ x * 1 := mul_le_mul_of_nonneg_left hB hx0.le
      nlinarith
    linarith
  rw [hsum] at hle
  rw [← div_le_iff₀ h2x0] at hle
  have : (1 - ε) * (x / Real.log x) ≤ (x - 3 * x / Real.log x) / Real.log (2 * x) := by
    rw [le_div_iff₀ h2x0]
    exact hkey
  linarith [this, (div_le_div_of_nonneg_right hθ h2x0.le)]

/-- For a route with `RouteOK` and a grid with `GridOK` that fit (`Fits`), and `ε > 0`:
`S(B, z_top) ≥ φ(q)⁻¹((1 − ε)x/log x − q)` for large `q`. -/
theorem TB_ev {ε : ℝ} (hε : 0 < ε) : ∀ᶠ q : ℕ in atTop, LargeQ q →
    (q.totient : ℝ)⁻¹ * ((1 - ε) * (xq q / Real.log (xq q)) - q) ≤ (parQ q).T (gB q) := by
  filter_upwards [tendsto_xq.eventually (primes_dyadic_ge hε)] with q hq hL
  have hq3 := hL.q3
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have G := good_of_large hL
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  set P := (Ioc (N1 q) (N2 q)).filter Nat.Prime with hP
  set Pc := P.filter (fun p => Nat.Coprime p q) with hPc
  -- the primes of `(N₁, N₂]` prime to `q` are rough and prime to `q`
  have hztopN : (parQ q).ztop ≤ N1 q + 1 := by
    have h1 : ((parQ q).ztop : ℝ) ≤ Real.sqrt (2 * xq q) + 1 := (ztop_bounds q (by omega)).2
    have hx16 : (16 : ℝ) ≤ xq q := by
      have h4 : (4 : ℝ) ≤ (q : ℝ) ^ (L / 2 : ℝ) := hL.hhalf
      have : xq q = ((q : ℝ) ^ (L / 2 : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        push_cast
        ring_nf
      rw [this]
      nlinarith
    have h2 : Real.sqrt (2 * xq q) ≤ xq q - 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h3 : xq q - 1 < (N1 q : ℝ) := Nat.sub_one_lt_floor _
    have : ((parQ q).ztop : ℝ) < (N1 q : ℝ) + 1 := by linarith
    exact_mod_cast this.le
  have hT : (q.totient : ℝ)⁻¹ * (Pc.card : ℝ) ≤ (parQ q).T (gB q) := by
    unfold Par.T
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    have hsub : Pc ⊆ Ioc (N1 q) (N2 q) := fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
      mul_nonneg (gB_nonneg q m) (by split_ifs <;> norm_num))
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hPc, hP, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨h1, -⟩, hpp⟩, hcop⟩ := hp
    have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).2 hcop
    have hr : SieveTree.rough (parQ q).ztop p := by
      intro ℓ hℓ hℓp hd
      have := (Nat.prime_dvd_prime_iff_eq hℓp hpp).1 hd
      omega
    simp only [gB, hu, ite_true, hr, Nat.cast_one, mul_one]
  -- the primes dividing `q` are at most `q`
  have hcount : (P.card : ℝ) - q ≤ Pc.card := by
    have h1 : P.filter (fun p => ¬ Nat.Coprime p q) ⊆ q.primeFactors := by
      intro p hp
      rw [Finset.mem_filter, hP, Finset.mem_filter] at hp
      rw [Nat.mem_primeFactors]
      exact ⟨hp.1.2, (Nat.Prime.dvd_iff_not_coprime hp.1.2).2 hp.2, by omega⟩
    have h2 : q.primeFactors.card ≤ q := by
      calc q.primeFactors.card ≤ (Finset.Icc 1 q).card := Finset.card_le_card fun p hp => by
            rw [Finset.mem_Icc]
            exact ⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le,
              Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)⟩
        _ = q := by simp
    have h3 := Finset.card_filter_add_card_filter_not (s := P) (fun p => Nat.Coprime p q)
    have h4 := (Finset.card_le_card h1).trans h2
    have : (P.card : ℝ) ≤ Pc.card + q := by
      rw [hPc]
      exact_mod_cast (show P.card ≤ (P.filter fun p => Nat.Coprime p q).card + q by omega)
    linarith
  have hP' : (1 - ε) * (xq q / Real.log (xq q)) ≤ (P.card : ℝ) := hq
  calc (q.totient : ℝ)⁻¹ * ((1 - ε) * (xq q / Real.log (xq q)) - q)
      ≤ (q.totient : ℝ)⁻¹ * (Pc.card : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hφ.le
    _ ≤ (parQ q).T (gB q) := hT

/-! ### The count, and the theorem -/

/-- The decomposition's constant `1 + n(1 + n(n(n + 2) + 2))`. -/
noncomputable def Cdec : ℝ := 1 + SieveCert.n * (1 + SieveCert.n * (SieveCert.n * (SieveCert.n + 2) + 2))

omit [Route] [RouteOK] [SieveCert.GridOK] [Fits] in
theorem Cdec_pos : 0 < Cdec := by unfold Cdec; positivity

omit [Route] [RouteOK] [SieveCert.Grid] [SieveCert.GridOK] [Fits] in
/-- `log q ≤ c q^r` for large `q`, any `c > 0`, `r > 0`. -/
theorem ev_log_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) : ∀ᶠ q : ℕ in atTop, Real.log q ≤ c * (q : ℝ) ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with q hq hq1
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  rw [Real.norm_of_nonneg (Real.log_nonneg hq0), Real.norm_of_nonneg (by positivity)] at hq
  exact hq

/-- **Linnik's theorem at `x = q^L`, for large `q`, with the certificate's loss as a parameter.** For a route with
`RouteOK` and a grid with `GridOK` that fit (`Fits`), given the route's Type II estimate (`hII`) and `total/K ≤ c` in
the reals for some `c < 1` (`htot`), there is `q₀` such that for `q ≥ q₀` and `a` a unit mod `q` there is a prime
`p ≡ a (mod q)` with `q^L < p ≤ 2q^L`. The losses the proof sets are shares `ε = (1 − c)/10` of `X = x/log x`:
`TB_ev`'s, `drop_ev_of`'s, two for the leaves' error (through `η` and `ev_log_le`) and `q ≤ εX`, five in all, leaving
`(1 − c − 5ε)X = (1 − c)X/2` of `S(A, z_top)` (round 619; `linnik_large` is the case `c = 0.88`, where until round 619
the proof set `1/100` for each share). -/
theorem linnik_large_of (hII : TypeIIAt) {c : ℝ} (hc : c < 1) (htot : (SieveCert.total : ℝ) / SieveCert.K ≤ c) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L := by
  have hC := Cdec_pos
  have hL0 : 0 < L := L_pos
  set ε : ℝ := (1 - c) / 10 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set η : ℝ := ε / (Cdec * L) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ, hδ, q₁, hlv⟩ := SieveQ.leaves_ev hII hη0
  have hev1 := ev_log_le (c := ε / (Cdec * L)) (by positivity) hδ
  have hev2 := ev_log_le (c := ε / L) (by positivity) (show (0 : ℝ) < L - 1 by linarith [two_lt_L])
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 ((TB_ev hε).and
    ((drop_ev_of htot hε).and (hev1.and (hev2.and (eventually_ge_atTop 3)))))
  refine ⟨q₁ + q₂, fun q _ hq a ha => ?_⟩
  obtain ⟨hTB, hD, h1, h2, hq3⟩ := hq₂ q (by omega)
  obtain ⟨hL, Lv⟩ := hlv q (by omega) a ha
  have G := good_of_large hL
  have hq3' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hφ : (0 : ℝ) < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.2 (by omega)
    positivity
  have hdec := (parQ q).decomp G (gA_nonneg q a) (Err_nonneg hη0 δ q (by omega)) Lv
  have hTB := hTB hL
  have hD := hD hL
  -- `X = x/log x = q^L/(L log q)`
  set Q := (q : ℝ) ^ L with hQ
  have hQ0 : 0 < Q := by positivity
  have hlogx : Real.log (xq q) = L * Real.log q := Real.log_rpow hq0 _
  set X := xq q / Real.log (xq q) with hXdef
  have hX : X = Q / (L * Real.log q) := by rw [hXdef, hlogx]
  have hX0 : 0 < X := by rw [hX]; positivity
  -- the leaves' error: `C·Err ≤ φ⁻¹(εX + εX)`
  have hErr : Cdec * Err η δ q ≤ (q.totient : ℝ)⁻¹ * (ε * X + ε * X) := by
    have hsplit : (q : ℝ) ^ (L - δ) * (q : ℝ) ^ δ = Q := by
      rw [← Real.rpow_add hq0, sub_add_cancel]
    have hd0 : 0 < (q : ℝ) ^ δ := by positivity
    have hA : Cdec * (η * Q / (q.totient * Real.log q)) = (q.totient : ℝ)⁻¹ * (ε * X) := by
      rw [hX, hη]
      field_simp
    have hB : Cdec * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) ≤ (q.totient : ℝ)⁻¹ * (ε * X) := by
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ hφ.le
      rw [hX, ← mul_div_assoc, le_div_iff₀ (by positivity)]
      have h1' : Cdec * L * Real.log q ≤ ε * (q : ℝ) ^ δ := by
        have := h1
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
        linarith
      calc Cdec * (q : ℝ) ^ (L - δ) * (L * Real.log q)
          = (q : ℝ) ^ (L - δ) * (Cdec * L * Real.log q) := by ring
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
        unfold Cdec at hErr
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

/-- **Linnik's theorem at `x = q^L`, for large `q`.** For a route with `RouteOK` and a grid with `GridOK` that fit
(`Fits`), given the route's Type II estimate (`hII`) and the certificate's total at most `0.88K` (`htot`), there is `q₀`
such that for `q ≥ q₀` and `a` a unit mod `q` there is a prime `p ≡ a (mod q)` with `q^L < p ≤ 2q^L`. -/
theorem linnik_large (hII : TypeIIAt) (htot : SieveCert.total ≤ 88 * SieveCert.K / 100) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ (q : ℝ) ^ L < p ∧ (p : ℝ) ≤ 2 * (q : ℝ) ^ L :=
  linnik_large_of hII (by norm_num) (SieveCert.total_div_le htot)

/-- **Linnik's theorem with exponent `L`, with the certificate's loss as a parameter.** For a route with `RouteOK` and a
grid with `GridOK` that fit (`Fits`), given the route's Type II estimate (`hII`) and `total/K ≤ c` in the reals for
some `c < 1` (`htot`), there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^L` (round 619; `linnik_route` is the case `c = 0.88`, `linnik_route_lt` the case
`c = total/K` for `total < K`). -/
theorem linnik_route_of (hII : TypeIIAt) {c : ℝ} (hc : c < 1) (htot : (SieveCert.total : ℝ) / SieveCert.K ≤ c) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L := by
  obtain ⟨q₀, hq₀⟩ := linnik_large_of hII hc htot
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
  have hqL : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 L_pos.le
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

/-- **Linnik's theorem with exponent `L`.** For a route with `RouteOK` and a grid with `GridOK` that fit (`Fits`), given
the route's Type II estimate (`hII`) and the certificate's total at most `0.88K` (`htot`), there is `K` such that for
every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^L`. -/
theorem linnik_route (hII : TypeIIAt) (htot : SieveCert.total ≤ 88 * SieveCert.K / 100) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L :=
  linnik_route_of hII (by norm_num) (SieveCert.total_div_le htot)

/-- **Linnik's theorem with exponent `L`, under a certificate whose total is below `K`.** For a route with `RouteOK` and
a grid with `GridOK` that fit (`Fits`), given the route's Type II estimate (`hII`) and the certificate's total less than
`K` (`htot`), there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with
`p ≤ K·q^L` (round 619). -/
theorem linnik_route_lt (hII : TypeIIAt) (htot : SieveCert.total < SieveCert.K) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ L :=
  linnik_route_of hII (SieveDrop.total_div_lt htot) le_rfl

end SieveMain

namespace SieveMain

open SieveCert SieveRoute SieveQ

/-- `grid2333` fits `route2333`: `0.401·DEN < U1`, `U2 < 0.485·DEN` and `DEN < 2.333·U2`. -/
theorem fits2333 : @Fits route2333 grid2333 := by
  refine @Fits.mk route2333 grid2333 ?_ ?_ ?_
  · have h : (401 * DEN : ℕ) < 1000 * ((401 * DEN + 999) / 1000) := by decide
    have h' : (401 : ℝ) * DEN < 1000 * (((401 * DEN + 999) / 1000 : ℕ) : ℝ) := by exact_mod_cast h
    show (401 / 1000 : ℝ) * DEN < (((401 * DEN + 999) / 1000 : ℕ) : ℝ)
    linarith
  · have h : 1000 * (485 * DEN / 1000) < 485 * DEN := by decide
    have h' : (1000 : ℝ) * ((485 * DEN / 1000 : ℕ) : ℝ) < 485 * DEN := by exact_mod_cast h
    show ((485 * DEN / 1000 : ℕ) : ℝ) < 485 / 1000 * DEN
    linarith
  · have h : 1000 * DEN < 2333 * (485 * DEN / 1000) := by decide
    have h' : (1000 : ℝ) * DEN < 2333 * ((485 * DEN / 1000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < 2333 / 1000 * ((485 * DEN / 1000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `2333/1000`.** There is `K` such that for every `q ≥ 1` and every `a` prime to
`q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{2333/1000}`. -/
theorem linnik_2333 : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (2333 / 1000 : ℝ) :=
  @linnik_route route2333 routeOK2333 grid2333 gridOK2333 fits2333 typeII2333 total_le_2333

end SieveMain

#print axioms SieveMain.linnik_2333
#print axioms SieveMain.linnik_route_lt
