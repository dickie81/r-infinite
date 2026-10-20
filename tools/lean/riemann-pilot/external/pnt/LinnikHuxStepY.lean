/-
# Round 612: the step of Huxley's bound with the detector's height as a parameter, class II empty under the Weyl bound

Built against PrimeNumberTheoremAnd at commit 650d312 (see README.md here).

Plain statement (`charDensity_genY`). For parameters `Pa : ParY` with `Pa.Good`, under `LinnikWeyl.PYWeyl`
(Petrow–Young's Weyl bound for every character, a displayed hypothesis), there is `C ≥ 0` such that for every
`q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2`, at most `C(qT)^{A(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)`
in `Re s ≥ σ`, `|Im s| ≤ T`.

This is round 607's step (`LinnikHuxStep.charDensity_gen`) with the detector's height `Y = Q^y` as a parameter:
`ParY` is `Par` with a field `cy`, `y = (1 + 2cy)/2000` (`Y = Yw cy U` at `U = Q^{1/2000}`; round 607 has `cy = 502`,
`y = 201/400`). `ParY.Good` is `Par.Good` with `hlam1 : 2y + ε ≤ lam` in place of `201/200 + ε ≤ lam`, `3/4 ≤ lo`, and,
in place of the fourth-moment condition `h3`, the emptiness condition `h5 : 1/6 + 2ε + 1/2000 ≤ y(lo − 1/2)`: under
the pointwise bound `‖L(1/2 + it, χ)‖ ≤ CL(q(1 + |t|))^{1/6+ε}`, `LinnikWeyl.class2_empty` makes the integral class
empty once `2·KG·CL·X·(q(T + 2))^{1/6+ε} < δ·Y^{σ−1/2}`, `δ = lo − 1/2 ≥ 1/4`; with `X ≤ Q^{1/2000}`,
`q(T + 2) ≤ Q` and `Y = Q^y` this follows from `h5` once `8KG·CL + 1 ≤ Q^ε` (a conjunct of `eventually_genY`).

* `ParY`, `ParY.Good`, `ParY.Good.cy_nonneg`: the parameters, and `cy ≥ 0` when the range is non-empty.
* `class1_genY`: `LinnikHuxStep.class1_gen` with `(2XN)² ≤ Q^{2y+ε}` (`choose_m_gen`, `term1_gen`, `term2_gen` and
  `block_bin_hux` reused by name).
* `eventually_genY`: `LinnikHuxStep.eventually_gen` with the height `Q^y` and a conjunct `c₀ ≤ Q^ε`.
* `count_gen_atY`: the range `[lo, hi]` at one large `Q`: `LinnikDetect.dichotomy`, `class1_genY` and
  `LinnikWeyl.class2_empty` (no character is of the integral class).
* `Yw_genY`, `count_genY`, `charDensity_genY`: as round 607's `Yw_gen`, `count_gen` and `charDensity_gen`.
* `parY_example`, `parY_example_good`: a worked instance on `[5/6, 101/120]` with `A = 5021/2500`; at `lo = 5/6`,
  `h5`, `hlam1` and `h1` force `A ≥ 4y + 2ε ≥ 2.00626`, so the exponent `3/(3σ₁ − 1) + 1/2000 = 2.0005` is not
  attainable there. `parY_example'`, `parY_example'_good`: on `[17/20, 11/12]` with `A = 60/31 + 1/2000`, which is
  `3/(3σ₁ − 1) + 1/2000`.

The file imports `LinnikHuxStep.lean` and `LinnikWeyl.lean`.
-/
import LinnikHuxStep
import LinnikWeyl

open Complex Real Finset MeasureTheory Filter Topology

noncomputable section

set_option exponentiation.threshold 3000

namespace LinnikHuxStepY

open InghamDensity Linnik LinnikDetect LinnikHybrid LinnikDensity LinnikIngham DirichletCharacter ShortWeil
  DirMean LinnikPower LinnikOffDiag LinnikHuxley LinnikReflect LinnikTwelve LinnikHuxStep

variable {q : ℕ}

/-! ### The parameters -/

/-- The parameters of a step of Huxley's bound with the detector's height as a parameter: the largest power `M`,
the power trick's target `Q^a`, the exponent `lam` of the powers' lengths, the range `[lo, hi]` of `σ`, the inner
exponent `Ai`, the exponent `A`, and the height's parameter `cy` (`Y = Yw cy U = Q^{(1+2cy)/2000}` at
`U = Q^{1/2000}`). -/
structure ParY where
  M : ℕ
  a : ℝ
  lam : ℝ
  lo : ℝ
  hi : ℝ
  Ai : ℝ
  A : ℝ
  cy : ℝ

/-- What a step with class II empty needs of its parameters, at the internal `ε = 1/100000`: as
`LinnikHuxStep.Par.Good` with `hlam1 : 2y + ε ≤ lam`, `y = (1 + 2cy)/2000`, and the emptiness condition `h5` in place
of the fourth-moment condition `h3`. -/
structure ParY.Good (P : ParY) : Prop where
  hM : 1 ≤ P.M
  ha : 0 < P.a
  hat : P.a + εs ≤ (P.M : ℝ) / 2000
  hlam1 : (1 + 2 * P.cy) / 1000 + εs ≤ P.lam
  hlam2 : 3 * (P.a + εs) / 2 ≤ P.lam
  hlam3 : P.lam ≤ 2
  hlo : 3 / 4 ≤ P.lo
  hhi : P.hi ≤ 11 / 12
  h1 : ∀ σ, P.lo ≤ σ → σ ≤ P.hi → P.lam * (2 - 2 * σ + εs) + εs / 12 ≤ P.Ai * (1 - σ)
  h2 : ∀ σ, P.lo ≤ σ → σ ≤ P.hi →
    (P.a + εs) * (4 - 6 * σ + 3 * εs) + (εs / 4 + (1 + 3 / 2 * εs) + εs / 4) ≤ P.Ai * (1 - σ)
  h5 : 1 / 6 + 2 * εs + 1 / 2000 ≤ (1 + 2 * P.cy) / 2000 * (P.lo - 1 / 2)
  h4 : ∀ σ, σ ≤ P.hi → εs / (24 * P.M) + P.Ai * (1 - σ) ≤ P.A * (1 - σ)
  hA : 0 ≤ P.A
  hA16 : P.A ≤ 16

/-- `cy ≥ 0` for parameters with `Good` (`G`) whose range is non-empty (`hlh : lo ≤ hi`): `h5` with
`0 < lo − 1/2 ≤ 5/12`. -/
theorem ParY.Good.cy_nonneg {P : ParY} (G : P.Good) (hlh : P.lo ≤ P.hi) : 0 ≤ P.cy := by
  have h5 := G.h5
  have hhi := G.hhi
  have hlo := G.hlo
  simp only [εs] at h5
  by_contra hneg
  push Not at hneg
  have h1 : P.lo - 1 / 2 ≤ 5 / 12 := by linarith
  have h2 : 0 < P.lo - 1 / 2 := by linarith
  have h3 : (1 + 2 * P.cy) / 2000 < 1 / 2000 := by linarith
  nlinarith

/-! ### The polynomial class -/

/-- **The polynomial class with Huxley's estimate on `[lo, hi]`** (`LinnikHuxStep.class1_gen` with the height's
parameter). Let the parameters have `Good`, `lo ≤ σ ≤ hi`, `T ≥ 0`, `Q > 1` with `q(T + 2) ≤ Q`, `X, N ≥ 1`, `Y > 0`,
and the large-sieve range `X_l`, `J` and `τ` with the size conditions its hypotheses list (`hK` … `hfar`).
Characters with one point `β_χ + iγ_χ` each, `σ ≤ β_χ < 1`, `|γ_χ| ≤ T`, and `|P_χ(β_χ + iγ_χ)| ≥ ¼` number at most
`(⌊50/ε⌋ + 1)K(B₁ + B₂)Q^{Ai(1−σ)}`, `K = ⌊log₂ N⌋ + 1`, `ε = εs`, for `Q^{1/2000} ≤ 2X` and
`(2XN)² ≤ Q^{(1+2cy)/1000+ε}`: some dyadic block is at least `1/(4K)`; bins of width `ε/200` in `β`; in each block and
bin a power `m ≤ M` with `(2P)^m ≥ Q^{a+ε}` (`choose_m_gen`), at most `Q^{lam}` long, and `block_bin_hux` with
`term1_gen` and `term2_gen`. -/
theorem class1_genY [NeZero q] (Pa : ParY) (G : Pa.Good)
    {σ T Q : ℝ} (hσ : Pa.lo ≤ σ) (hσ1 : σ ≤ Pa.hi) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXQ : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (εs / (24 * Pa.M)))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ ((1 + 2 * Pa.cy) / 1000 + εs))
    {Xl J : ℕ} {τ : ℝ} (hXl1 : 1 ≤ Xl) (hXlQ : (Xl : ℝ) ≤ Q ^ (25 : ℝ))
    (hXl : Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Xl)
    (hτd : ∀ n, n ≤ Xl → (n.divisors.card : ℝ) ≤ τ) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (εs / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (εs / 8)) (hL : LSmax Xl ≤ Q ^ (εs / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (εs / 8)) (hEQ : EQ q ≤ Q ^ (εs / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (εs / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1)
    {Y : ℝ} (hY : 0 < Y) (Rs : Finset (DirichletCharacter ℂ q)) (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ Rs, σ ≤ β χ ∧ β χ < 1) (hγ : ∀ χ ∈ Rs, |γ χ| ≤ T)
    (hbig : ∀ χ ∈ Rs, 1 / 4 ≤ ‖Pvχ χ X N Y (β χ) (γ χ)‖) :
    (Rs.card : ℝ) ≤ ((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * ((Nat.log 2 N + 1 : ℕ) : ℝ) * ((B1g Pa.M εs + B2g Pa.M εs) *
      Q ^ (Pa.Ai * (1 - σ))) := by
  classical
  have hε := εs_pos
  have hε1 : εs ≤ 1 / 100000 := le_refl _
  have hQ0 : 0 < Q := by linarith
  have hlo := G.hlo
  have hhi := G.hhi
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set nb := ⌊50 / εs⌋₊ + 1 with hnb
  set Bb := (B1g Pa.M εs + B2g Pa.M εs) * Q ^ (Pa.Ai * (1 - σ)) with hBb
  -- some block of each character is at least `V`
  have hlarge : ∀ χ ∈ Rs, ∃ k ∈ range K, V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ := by
    intro χ hχ
    by_contra hcon
    push Not at hcon
    have h1 := hbig χ hχ
    rw [Pvχ_eq_blocks χ X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkχ χ X N Y k (β χ) (γ χ)‖ < ∑ _k ∈ range K, V :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * V = 1 / 4 := by rw [hV]; field_simp
    linarith [(norm_sum_le (range K) fun k => Fkχ χ X N Y k (β χ) (γ χ)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → ℕ → Finset (DirichletCharacter ℂ q) := fun k j =>
    Rs.filter fun χ => V ≤ ‖Fkχ χ X N Y k (β χ) (γ χ)‖ ∧ ⌊200 / εs * (β χ - σ)⌋₊ = j with hCkdef
  have hsub : Rs ⊆ (range K).biUnion fun k => (range nb).biUnion fun j => Ck k j := by
    intro χ hχ
    obtain ⟨k, hk, hbigk⟩ := hlarge χ hχ
    have h1 := hβ χ hχ
    have hj : ⌊200 / εs * (β χ - σ)⌋₊ < nb := by
      have hle : 200 / εs * (β χ - σ) ≤ 50 / εs := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]; linarith
      exact Nat.lt_succ_of_le (Nat.floor_le_floor hle)
    exact mem_biUnion.2 ⟨k, hk, mem_biUnion.2 ⟨_, mem_range.2 hj, mem_filter.2 ⟨hχ, hbigk, rfl⟩⟩⟩
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqQ : (q : ℝ) ≤ Q := (le_mul_of_one_le_right hq0 (by linarith : (1 : ℝ) ≤ T + 2)).trans hqT
  have hq2T : (q : ℝ) * (1 + 2 * T) ≤ 2 * Q := by
    have : (q : ℝ) * (1 + 2 * T) ≤ q * (2 * (T + 2)) := mul_le_mul_of_nonneg_left (by linarith) hq0
    linarith
  have hCk : ∀ k ∈ range K, ∀ j ∈ range nb, ((Ck k j).card : ℝ) ≤ Bb := by
    intro k hk j _
    set P := 2 ^ k * X with hPdef
    have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ X * N := by
      rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le (mem_range.1 hk) hN)
    have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
    have hSsub : (Ioc X (X * N)).filter (fun j => blk X j = k) ⊆ Ioc P (2 * P) := block_sub hX
    have h2Px : Q ^ (1 / 2000 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
      have : (2 * (X : ℝ)) ≤ ((2 * P : ℕ) : ℝ) := by
        have h := (by omega : 2 * X ≤ 2 * P)
        have h' : ((2 * X : ℕ) : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h' ⊢; linarith
      linarith
    obtain ⟨m, hm1, hmM, hΛlo, hΛhi⟩ :=
      choose_m_gen Pa.M hQ1 (by linarith [G.ha] : (0 : ℝ) < Pa.a + εs) G.hat h2Px
    have hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ Pa.lam := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ Q ^ ((1 + 2 * Pa.cy) / 1000 + εs) := hXN
          _ ≤ Q ^ Pa.lam := Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam1
      · exact Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam2
    have hΛ2 : ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ 2 := by
      calc ((2 * P : ℕ) : ℝ) ^ m ≤ Q ^ Pa.lam := hΛ
        _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1.le G.hlam3
        _ = Q ^ 2 := by norm_num
    set σb : ℝ := σ + j * (εs / 200) with hσb
    have hσσb : σ ≤ σb := by
      have : (0 : ℝ) ≤ (j : ℝ) * (εs / 200) := by positivity
      rw [hσb]; linarith
    have hbin : ∀ χ ∈ Ck k j, σb ≤ β χ ∧ β χ ≤ σb + εs / 200 := by
      intro χ hχ
      obtain ⟨hχR, -, hbj⟩ := mem_filter.1 hχ
      have h0 : 0 ≤ 200 / εs * (β χ - σ) := by
        have h5 := (hβ χ hχR).1
        have h6 : 0 ≤ β χ - σ := by linarith
        positivity
      have h1 : ((⌊200 / εs * (β χ - σ)⌋₊ : ℕ) : ℝ) ≤ 200 / εs * (β χ - σ) := Nat.floor_le h0
      have h2 : 200 / εs * (β χ - σ) < ((⌊200 / εs * (β χ - σ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hbj] at h1 h2
      constructor
      · have h3 : (j : ℝ) * (εs / 200) ≤ β χ - σ := by
          calc (j : ℝ) * (εs / 200) ≤ (200 / εs * (β χ - σ)) * (εs / 200) := by gcongr
            _ = β χ - σ := by field_simp
        rw [hσb]; linarith
      · have h3 : β χ - σ ≤ ((j : ℝ) + 1) * (εs / 200) := by
          have h4 : 200 / εs * (β χ - σ) ≤ (j : ℝ) + 1 := h2.le
          calc β χ - σ = (200 / εs * (β χ - σ)) * (εs / 200) := by field_simp
            _ ≤ ((j : ℝ) + 1) * (εs / 200) := by gcongr
        rw [hσb]; linarith
    have hXD : (((2 * P) ^ m : ℕ) : ℝ) * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J ≤ Xl := by
      have e : (((2 * P) ^ m : ℕ) : ℝ) = ((2 * P : ℕ) : ℝ) ^ m := by push_cast; ring
      rw [e]
      have h1 : 2 * ((q : ℝ) * (1 + 2 * T)) * q + 1 ≤ 4 * Q ^ 2 + 1 := by
        have h1' : (q : ℝ) * (1 + 2 * T) * q ≤ 2 * Q * Q := mul_le_mul hq2T hqQ hq0 (by linarith)
        have hsq : Q ^ 2 = Q * Q := sq Q
        linarith
      have h0 : 0 ≤ 2 * ((q : ℝ) * (1 + 2 * T)) * q + 1 := by positivity
      calc ((2 * P : ℕ) : ℝ) ^ m * (2 * (q * (1 + 2 * T)) * q + 1) * 2 ^ J
          ≤ Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J := by gcongr
        _ ≤ Xl := hXl
    have hMr : (1 : ℝ) ≤ Pa.M := by exact_mod_cast G.hM
    have hcount := block_bin_hux (q := q) (R := Ck k j) hP hSsub (c := b1 X Y) (fun i _ => norm_b1_le X hY i) hm1
      (σb := σb) (η := εs / 200) (by linarith) (by linarith) β γ hbin hT
      (fun χ hχ => hγ χ (mem_filter.1 hχ).1) hV0
      (fun χ hχ => by rw [← Fkχ_eq_pv]; exact (mem_filter.1 hχ).2.1) (εd := εs / (4 * Pa.M)) (by positivity)
      (by rw [div_le_one (by positivity)]; linarith) J hXl1 hXD hτd
    have ht1 := term1_gen G.hM hε (by linarith) (by linarith) hσσb hQ1.le hP hmM hΛ hK1 hK
      (G.h1 σ hσ hσ1)
    have ht2 := term2_gen (q := q) G.hM hε (by linarith) (by linarith) hσσb hQ1.le hT hqT hP hmM hΛlo
      (by linarith) (G.h2 σ hσ hσ1) hK1 hK hXl1 hXlQ hτ1 hτQ hJ hL hB hEQ hPs hfar
    refine hcount.trans ?_
    rw [hBb, add_mul]
    exact add_le_add ht1 ht2
  calc (Rs.card : ℝ) ≤ ((range K).biUnion fun k => (range nb).biUnion fun j => Ck k j).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, (((range nb).biUnion fun j => Ck k j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range nb, ((Ck k j).card : ℝ) := by
        gcongr with k hk; exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range nb, Bb := by
        gcongr with k hk j hj; exact hCk k hk j hj
    _ = (nb : ℝ) * (K : ℝ) * Bb := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### Large `Q` -/

/-- For `M_p ≥ 1`, `ε > 0`, `M ≥ 1`, `0 ≤ y` with `y + ε/2 ≤ 1`, and any real `c₀`, the conditions on `Q` used by a
step with the height `Q^y` hold for all large `Q` (`ev_log_pow`); as `LinnikHuxStep.eventually_gen`, with
`(2·23Q^y log Q^y)² ≤ Q^{2y+ε}`, `23Q^y log Q^y ≤ Q` and the conjunct `c₀ ≤ Q^ε`. -/
lemma eventually_genY (Mp : ℕ) (hMp : 1 ≤ Mp) {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM : 1 ≤ M) {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y + ε / 2 ≤ 1) (c₀ : ℝ) :
    ∀ᶠ Q : ℝ in atTop, (8 : ℝ) ^ 2000 ≤ Q ∧ 4 * (1 + 2 * Real.log Q) ≤ Q ^ (ε / (24 * Mp)) ∧
      (2 * (23 * Q ^ y * Real.log (Q ^ y))) ^ 2 ≤ Q ^ (2 * y + ε) ∧
      23 * Q ^ y * Real.log (Q ^ y) ≤ Q ∧ Cdiv (ε / 200) ≤ Q ^ (ε / 8) ∧
      16 * (2 * Real.log (4 * M * Q) + 1) + 2 ≤ Q ^ (ε / 8) ∧ (8 * M * Q) ^ 16 ≤ Q ^ 20 ∧
      8 * Real.exp 1 * 25 * 627 * 50 * (1 + Real.log Q) ^ 4 ≤ Q ^ (ε / 8) ∧
      2 * Real.log (4 * Q) + 1 ≤ Q ^ (ε / 8) ∧ CEQ ε ≤ Q ^ (ε / 16) ∧ Cdiv (ε / 16) ≤ Q ^ (ε / 16) ∧
      c₀ ≤ Q ^ ε := by
  have hlM : 0 ≤ Real.log (4 * M) := Real.log_nonneg (by linarith)
  have hMp' : (0 : ℝ) < Mp := by exact_mod_cast hMp
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 2000), ev_log_pow 8 (ε / (24 * Mp)) 1 (by positivity),
    ev_log_pow ((46 * y) ^ 2) ε 2 hε, ev_log_pow (23 * y) (ε / 2) 1 (by positivity),
    ev_log_pow (Cdiv (ε / 200)) (ε / 8) 0 (by positivity),
    ev_log_pow (32 * Real.log (4 * M) + 50) (ε / 8) 1 (by positivity),
    ev_log_pow ((8 * M) ^ 16) 4 0 (by norm_num),
    ev_log_pow (8 * Real.exp 1 * 25 * 627 * 50) (ε / 8) 4 (by positivity),
    ev_log_pow (2 * Real.log 4 + 3) (ε / 8) 1 (by positivity),
    ev_log_pow (CEQ ε) (ε / 16) 0 (by positivity), ev_log_pow (Cdiv (ε / 16)) (ε / 16) 0 (by positivity),
    ev_log_pow c₀ ε 0 hε]
    with Q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hQ1 : 1 ≤ Q := le_trans (by norm_num) h1
  have hQ0 : 0 < Q := by linarith
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlog : Real.log (Q ^ y) = y * Real.log Q := Real.log_rpow hQ0 _
  have hQy0 : 0 ≤ Q ^ y := by positivity
  simp only [pow_zero, mul_one, pow_one] at h2 h4 h5 h6 h7 h9 h10 h11 h12
  refine ⟨h1, ?_, ?_, ?_, h5, ?_, ?_, h8, ?_, h10, h11, h12⟩
  · linarith
  · have hQY : (Q ^ y) ^ 2 = Q ^ (2 * y) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
    calc (2 * (23 * Q ^ y * Real.log (Q ^ y))) ^ 2
        = (46 * y) ^ 2 * Real.log Q ^ 2 * (Q ^ y) ^ 2 := by rw [hlog]; ring
      _ ≤ (46 * y) ^ 2 * (1 + Real.log Q) ^ 2 * Q ^ (2 * y) := by
          rw [hQY]; gcongr; linarith
      _ ≤ Q ^ ε * Q ^ (2 * y) := by gcongr
      _ = Q ^ (2 * y + ε) := by rw [← Real.rpow_add hQ0]; ring_nf
  · calc 23 * Q ^ y * Real.log (Q ^ y) = 23 * y * Real.log Q * Q ^ y := by rw [hlog]; ring
      _ ≤ 23 * y * (1 + Real.log Q) * Q ^ y := by gcongr; linarith
      _ ≤ Q ^ (ε / 2) * Q ^ y := by gcongr
      _ ≤ Q ^ (1 - y) * Q ^ y :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)) hQy0
      _ = Q := by rw [← Real.rpow_add hQ0, sub_add_cancel, Real.rpow_one]
  · have e : Real.log (4 * M * Q) = Real.log (4 * M) + Real.log Q := Real.log_mul (by positivity) hQ0.ne'
    rw [e]
    nlinarith
  · have e4 : Q ^ (4 : ℝ) = Q ^ 4 := by norm_num
    rw [e4] at h7
    calc (8 * M * Q) ^ 16 = (8 * M) ^ 16 * Q ^ 16 := by ring
      _ ≤ Q ^ 4 * Q ^ 16 := by gcongr
      _ = Q ^ 20 := by ring
  · have e : Real.log (4 * Q) = Real.log 4 + Real.log Q := Real.log_mul (by norm_num) hQ0.ne'
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [e]
    nlinarith

/-! ### The range at one large `Q`, and the step -/

open scoped Classical in
/-- **The range `[lo, hi]` at one large `Q`.** Let the parameters have `Good`, let the pointwise bound hold with a
constant `CL ≥ 0` (`hCL`, `hLw`), and let `lo ≤ σ ≤ hi`, `T ≥ 0` and `Q > 1` with `q(T + 2) ≤ Q` and
`8KG·CL + 1 ≤ Q^ε` (`hQL`). With the detector's `X, N, Y` (`X, N ≥ 1`, `Y ≥ 8`, `22Y log Y ≤ XN`,
`Y = Q^{(1+2cy)/2000}`, `X ≤ Q^{1/2000}`, `Q^{1/2000} ≤ 2X`, `4K ≤ Q^{ε/(24M)}` with `K = ⌊log₂ N⌋ + 1`, and
`(2XN)² ≤ Q^{(1+2cy)/1000+ε}`), the large-sieve range `X_l`, `J` and `τ` of `class1_genY` (`hXl1` … `hfar`), at most
`(⌊50/ε⌋ + 1)(B₁ + B₂)Q^E` characters `χ ≠ 1` mod `q` have a zero in `Re s ≥ σ`, `|Im s| ≤ T`, `E = A(1 − σ)`,
`ε = εs`: `LinnikDetect.dichotomy`, `class1_genY`, and `LinnikWeyl.class2_empty` at `δ = lo − 1/2` (no character is
of the integral class, since `h5` and `hQL` give its `hbig`). -/
theorem count_gen_atY [NeZero q] (Pa : ParY) (G : Pa.Good) {CL : ℝ} (hCL : 0 ≤ CL)
    (hLw : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖LFunction χ (1 / 2 + t * I)‖ ≤ CL * ((q : ℝ) * (1 + |t|)) ^ (1 / 6 + εs))
    {σ T Q : ℝ} (hσ : Pa.lo ≤ σ) (hσ1 : σ ≤ Pa.hi) (hT : 0 ≤ T) (hQ1 : 1 < Q)
    (hqT : (q : ℝ) * (T + 2) ≤ Q) (hQL : 8 * KG * CL + 1 ≤ Q ^ εs)
    {X N : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hY8 : 8 ≤ Y) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hYQ : Y = Q ^ ((1 + 2 * Pa.cy) / 2000)) (hXU : (X : ℝ) ≤ Q ^ (1 / 2000 : ℝ))
    (hXU2 : Q ^ (1 / 2000 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ Q ^ (εs / (24 * Pa.M)))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ Q ^ ((1 + 2 * Pa.cy) / 1000 + εs))
    {Xl J : ℕ} {τ : ℝ} (hXl1 : 1 ≤ Xl) (hXlQ : (Xl : ℝ) ≤ Q ^ (25 : ℝ))
    (hXl : Q ^ 2 * (4 * Q ^ 2 + 1) * 2 ^ J ≤ Xl)
    (hτd : ∀ n, n ≤ Xl → (n.divisors.card : ℝ) ≤ τ) (hτ1 : 1 ≤ τ) (hτQ : τ ≤ Q ^ (εs / 4))
    (hJ : (J : ℝ) + 2 ≤ Q ^ (εs / 8)) (hL : LSmax Xl ≤ Q ^ (εs / 8))
    (hB : (bkt (q * (1 + 2 * T)) : ℝ) + 1 ≤ Q ^ (εs / 8)) (hEQ : EQ q ≤ Q ^ (εs / 8))
    (hPs : (q.primeFactors.powerset.card : ℝ) ≤ Q ^ (εs / 8))
    (hfar : (q : ℝ) ^ (1 / 4 : ℝ) * (2 * (q * (1 + 2 * T))) ^ (3 / 4 : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ (-(1 / 16 : ℝ)) *
      zeta98 ≤ 1) :
    ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ ((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * (B1g Pa.M εs + B2g Pa.M εs) * Q ^ (Pa.A * (1 - σ)) := by
  have hQ0 : 0 < Q := by linarith
  have hKG := KG_pos
  have hε := εs_pos
  have hε1 : εs ≤ 1 / 100000 := le_refl _
  have hlo := G.hlo
  have hhi := G.hhi
  have hY1 : 1 ≤ Y := by linarith
  -- the emptiness condition of `class2_empty` at `δ = lo − 1/2`
  have hbig : KG * CL * X * ((q : ℝ) * (T + 2)) ^ (1 / 6 + εs) * 2 <
      (Pa.lo - 1 / 2) * Y ^ (σ - 1 / 2) := by
    have hπ := Real.pi_pos
    have hδ : 1 / 4 ≤ Pa.lo - 1 / 2 := by linarith
    have hqTp : ((q : ℝ) * (T + 2)) ^ (1 / 6 + εs) ≤ Q ^ (1 / 6 + εs) :=
      Real.rpow_le_rpow (by positivity) hqT (by positivity)
    have hYσ : Y ^ (Pa.lo - 1 / 2) ≤ Y ^ (σ - 1 / 2) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have hYlo : Y ^ (Pa.lo - 1 / 2) = Q ^ ((1 + 2 * Pa.cy) / 2000 * (Pa.lo - 1 / 2)) := by
      rw [hYQ, ← Real.rpow_mul hQ0.le]
    have hQ5 : Q ^ (1 / 6 + 2 * εs + 1 / 2000) ≤ Q ^ ((1 + 2 * Pa.cy) / 2000 * (Pa.lo - 1 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hQ1.le G.h5
    have hQsplit : Q ^ (1 / 6 + 2 * εs + 1 / 2000) = Q ^ εs * (Q ^ (1 / 2000 : ℝ) * Q ^ (1 / 6 + εs)) := by
      rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
    have hc : KG * CL * 2 * 4 < Q ^ εs := by
      have : 8 * KG * CL = KG * CL * 2 * 4 := by ring
      linarith
    have hP1 : 0 < Q ^ (1 / 2000 : ℝ) * Q ^ (1 / 6 + εs) := by positivity
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    calc KG * CL * X * ((q : ℝ) * (T + 2)) ^ (1 / 6 + εs) * 2
        = KG * CL * 2 * ((X : ℝ) * ((q : ℝ) * (T + 2)) ^ (1 / 6 + εs)) := by ring
      _ ≤ KG * CL * 2 * (Q ^ (1 / 2000 : ℝ) * Q ^ (1 / 6 + εs)) := by
          gcongr
      _ < Q ^ εs / 4 * (Q ^ (1 / 2000 : ℝ) * Q ^ (1 / 6 + εs)) := by
          apply mul_lt_mul_of_pos_right _ hP1; linarith
      _ = 1 / 4 * Q ^ (1 / 6 + 2 * εs + 1 / 2000) := by rw [hQsplit]; ring
      _ ≤ (Pa.lo - 1 / 2) * Y ^ (Pa.lo - 1 / 2) := by
          rw [hYlo]; exact mul_le_mul hδ hQ5 (Real.rpow_nonneg hQ0.le _) (by linarith)
      _ ≤ (Pa.lo - 1 / 2) * Y ^ (σ - 1 / 2) := mul_le_mul_of_nonneg_left hYσ (by linarith)
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset (DirichletCharacter ℂ q), Z = univ.filter fun χ : DirichletCharacter ℂ q =>
      χ ≠ 1 ∧ ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := ⟨_, rfl⟩
  rw [← hZ]
  have hch : ∀ χ ∈ Z, ∃ s : ℂ, χ ≠ 1 ∧ σ ≤ s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
    intro χ hχ
    rw [hZ] at hχ
    obtain ⟨hχ1, s, hs1, hs2, hs3⟩ := (mem_filter.1 hχ).2
    refine ⟨s, hχ1, hs1, ?_, hs2, hs3⟩
    by_contra hge
    push Not at hge
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hge hs3
  choose! s0 hs0 using hch
  have hz0 : ∀ χ ∈ Z, LFunction χ (((s0 χ).re : ℂ) + (s0 χ).im * I) = 0 := fun χ hχ => by
    rw [Complex.re_add_im]; exact (hs0 χ hχ).2.2.2.2
  -- every character is of the polynomial class: the integral class is empty
  have hdich : ∀ χ ∈ Z, 1 / 4 ≤ ‖Pvχ χ X N Y (s0 χ).re (s0 χ).im‖ := by
    intro χ hχ
    obtain ⟨hχ1, h1, h2, h3, _⟩ := hs0 χ hχ
    rcases dichotomy hχ1 hX hN hY8 hM (by linarith) h2 (hz0 χ hχ) with h | h
    · exact h
    · exfalso
      have hlt := LinnikWeyl.class2_empty (q := q) hε.le (by linarith) hCL hLw hX (δ := Pa.lo - 1 / 2)
        (by linarith) (by linarith) hT hY1 hbig hχ1 h1 h2 h3 (hz0 χ hχ)
      linarith
  have hc1 := class1_genY Pa G hσ hσ1 hT hQ1 hqT hX hN hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hB hEQ
    hPs hfar (by linarith : (0 : ℝ) < Y) Z (fun χ => (s0 χ).re) (fun χ => (s0 χ).im)
    (fun χ hχ => ⟨(hs0 χ hχ).2.1, (hs0 χ hχ).2.2.1⟩)
    (fun χ hχ => (hs0 χ hχ).2.2.2.1)
    hdich
  exact absorb_K_gen (Mp := Pa.M) (A := Pa.A) hQ1.le (by positivity)
    (add_nonneg (B1g_nonneg Pa.M εs) (B2g_nonneg Pa.M εs)) (Nat.cast_nonneg _) hK (G.h4 σ hσ1) hc1

/-- For `Q > 0` and any `c`, `Y = Q^{(1+2c)/2000}` for the detector at `U = Q^{1/2000}`. -/
lemma Yw_genY {Q c : ℝ} (hQ0 : 0 < Q) : Yw c (Q ^ (1 / 2000 : ℝ)) = Q ^ ((1 + 2 * c) / 2000) := by
  unfold Yw; rw [← Real.rpow_mul hQ0.le]; congr 1; ring

open scoped Classical in
/-- **The range `[lo, hi]`.** For parameters with `Good` (`G`) and under `PYWeyl` (`hPY`), there is `C ≥ 0` such that
for every `q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2` at most `C Q^{A(1−σ)}`, `Q = q(T + 6)`, characters `χ ≠ 1` mod `q` have
a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. When `hi < lo` there is nothing to count. Otherwise `cy ≥ 0`
(`cy_nonneg`), `PYWeyl` at `ε = εs` gives `CL`, and for `Q ≥ Q₀` (`eventually_genY`) `count_gen_atY` at the detector
`X = ⌊Q^{1/2000}⌋`, `Y = Q^{(1+2cy)/2000}` and the large-sieve range of `sieve_range`; below `Q₀` at most `q ≤ Q₀`
characters are counted. -/
theorem count_genY (Pa : ParY) (G : Pa.Good) (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), Pa.lo ≤ σ → σ ≤ Pa.hi → 2 ≤ T →
      ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
        ≤ C * ((q : ℝ) * (T + 6)) ^ (Pa.A * (1 - σ)) := by
  rcases lt_or_ge Pa.hi Pa.lo with hlh | hlh
  · exact ⟨0, le_rfl, fun q _ σ T hσ hσ1 _ => absurd (hσ.trans hσ1) (not_le.2 hlh)⟩
  have hε := εs_pos
  have hε1 : εs ≤ 1 / 100000 := le_refl _
  have hε200 : εs ≤ 1 / 200 := by linarith
  have hcy := G.cy_nonneg hlh
  obtain ⟨CL, hCL0, hCL⟩ := hPY εs hε
  have hM1 : (1 : ℝ) ≤ max zeta98 1 := le_max_right _ _
  have hy0 : 0 ≤ (1 + 2 * Pa.cy) / 2000 := by positivity
  have hy1 : (1 + 2 * Pa.cy) / 2000 + εs / 2 ≤ 1 := by
    have := G.hlam1; have := G.hlam3; linarith
  have hKG := KG_pos
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1
    (eventually_genY Pa.M G.hM hε hM1 hy0 hy1 (8 * KG * CL + 1))
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((⌊50 / εs⌋₊ + 1 : ℕ) : ℝ) * (B1g Pa.M εs + B2g Pa.M εs) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; have := B1g_nonneg Pa.M εs; have := B2g_nonneg Pa.M εs; positivity
  refine ⟨max Q₀ 0 + B, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hlo := G.hlo
  have hhi := G.hhi
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (q : ℝ) * (T + 6) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ8 : 8 ≤ Q := by
    rw [hQ]
    calc (8 : ℝ) = 1 * 8 := by norm_num
      _ ≤ (q : ℝ) * (T + 6) := mul_le_mul hq1 (by linarith) (by norm_num) (by positivity)
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Pa.A * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg G.hA (by linarith)
  have hQE : 1 ≤ Q ^ E := Real.one_le_rpow hQ1 hE0
  rcases lt_or_ge Q Q₀ with hsmall | hlarge
  · have hBQ : 0 ≤ B * Q ^ E := by positivity
    calc _ ≤ (q : ℝ) := card_chars_le _
      _ ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ max Q₀ 0 := hsmall.le.trans (le_max_left _ _)
      _ ≤ max Q₀ 0 * Q ^ E := le_mul_of_one_le_right (le_max_right _ _) hQE
      _ ≤ (max Q₀ 0 + B) * Q ^ E := by rw [add_mul]; linarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hQ₀ Q hlarge
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = Q ^ (1 / 2000 : ℝ) := ⟨_, rfl⟩
  have hU8 : 8 ≤ U := by
    rw [hU]
    calc (8 : ℝ) = ((8 : ℝ) ^ 2000) ^ (1 / 2000 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ Q ^ (1 / 2000 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hYQ : Yw Pa.cy U = Q ^ ((1 + 2 * Pa.cy) / 2000) := by rw [hU]; exact Yw_genY hQ0
  have hX : 1 ≤ Xw U := Xw_one hU8
  have hN : 1 ≤ Nw Pa.cy U := Nw_one
  have hY8 : 8 ≤ Yw Pa.cy U := le_trans hU8 (Yw_ge hcy hU8)
  have hM : 22 * Yw Pa.cy U * Real.log (Yw Pa.cy U) ≤ ((Xw U * Nw Pa.cy U : ℕ) : ℝ) := XN_ge hU8
  have hXNle : ((Xw U * Nw Pa.cy U : ℕ) : ℝ) ≤ 23 * Yw Pa.cy U * Real.log (Yw Pa.cy U) := XN_le hcy hU8
  have hXU : (Xw U : ℝ) ≤ Q ^ (1 / 2000 : ℝ) := hU ▸ Xw_le hU8
  have hXU2 : Q ^ (1 / 2000 : ℝ) ≤ 2 * (Xw U : ℝ) := by have := Xw_half hU8; rw [← hU]; linarith
  have hXr : (1 : ℝ) ≤ Xw U := by exact_mod_cast hX
  have hNQ : (Nw Pa.cy U : ℝ) ≤ Q := by
    have h1 : (Nw Pa.cy U : ℝ) ≤ ((Xw U * Nw Pa.cy U : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    rw [hYQ] at hXNle
    linarith
  have hK : 4 * ((Nat.log 2 (Nw Pa.cy U) + 1 : ℕ) : ℝ) ≤ Q ^ (εs / (24 * Pa.M)) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNQ) (by norm_num)).trans h2
  have hXN : (2 * ((Xw U * Nw Pa.cy U : ℕ) : ℝ)) ^ 2 ≤ Q ^ ((1 + 2 * Pa.cy) / 1000 + εs) := by
    have e : (1 + 2 * Pa.cy) / 1000 + εs = 2 * ((1 + 2 * Pa.cy) / 2000) + εs := by ring
    rw [e]
    refine le_trans ?_ h3
    rw [← hYQ]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hqT : (q : ℝ) * (T + 2) ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hqQ : (q : ℝ) ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by positivity) (by linarith)
  have h1' : (8 : ℝ) ^ 25 ≤ Q := le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) h1
  obtain ⟨Xl, J, τ, hXl1, hXlQ, hXl, hτd, hτ1, hτQ, hJ, hL, hfar⟩ :=
    sieve_range (q := q) hε hε200 (by linarith : (0 : ℝ) ≤ T) h1' hqT h5 h6 h7 h8
  have hBk := bkt_le_Q (q := q) (ε := εs) (by linarith : (0 : ℝ) ≤ T) hqT h9
  have hEQ := EQ_le_Q (q := q) hε hQ1 hqQ h10
  have hPs := powerset_le_Q (q := q) hε hε200 hQ1 hqQ h11
  have hcount := count_gen_atY (q := q) Pa G hCL0 (hCL q) (σ := σ) (T := T) (Q := Q) hσ hσ1 (by linarith)
    (by linarith) hqT h12 hX hN hY8 hM hYQ hXU hXU2 hK hXN hXl1 hXlQ hXl hτd hτ1 hτQ hJ hL hBk hEQ hPs hfar
  rw [← hE, ← hB] at hcount
  calc _ ≤ B * Q ^ E := hcount
    _ ≤ (max Q₀ 0 + B) * Q ^ E := by
        have : 0 ≤ max Q₀ 0 * Q ^ E := by positivity
        rw [add_mul]; linarith

open scoped Classical in
/-- **A density estimate over the characters mod `q` with exponent `A` on `[lo, hi]`, class II empty under the Weyl
bound**: for parameters with `Good` (`G`) and under `PYWeyl` (`hPY`), there is `C ≥ 0` such that for every `q ≥ 1`,
`lo ≤ σ ≤ hi` and `T ≥ 2` at most `C(qT)^{A(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`: `count_genY` measured at `Q = q(T + 6) ≤ 4qT`, plus the trivial character. -/
theorem charDensity_genY (Pa : ParY) (G : Pa.Good) (hPY : LinnikWeyl.PYWeyl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), Pa.lo ≤ σ → σ ≤ Pa.hi → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (Pa.A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  obtain ⟨CT, hCT0, hCT⟩ := count_genY Pa G hPY
  refine ⟨2 ^ 10 + 256 * 2 ^ 10 * CT, by positivity, ?_⟩
  intro q _ σ T hσ hσ1 hT
  have hlo := G.hlo
  have hhi := G.hhi
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ q * T := by nlinarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log ((q : ℝ) * T) := ⟨_, rfl⟩
  rw [← hℓdef]
  have hℓ : 1 / 2 ≤ ℓ := hℓdef ▸ half_le_log hqT
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Pa.A * (1 - σ) := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg G.hA (by linarith)
  have hE4 : E ≤ 4 := by
    rw [hE]
    have h1 : 1 - σ ≤ 1 / 4 := by linarith
    have h2 := G.hA16
    nlinarith [G.hA]
  have hpowE : 0 ≤ ((q : ℝ) * T) ^ E := by positivity
  have hpowE1 : 1 ≤ ((q : ℝ) * T) ^ E := Real.one_le_rpow (by linarith) hE0
  have e10 : ℓ ^ (10 : ℝ) = ℓ ^ (10 : ℕ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e10]
  have h2ℓ : 1 ≤ 2 ^ 10 * ℓ ^ 10 := by
    have h1 : 1 ≤ (2 * ℓ) ^ 10 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) ≤ (2 * ℓ) ^ 10 := h1
      _ = 2 ^ 10 * ℓ ^ 10 := by ring
  have hℓ10 : 0 ≤ ℓ ^ 10 := by positivity
  have hsub : (univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
      ⊆ insert 1 (univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0) := by
    intro χ hχ
    rw [mem_insert]
    by_cases h1 : χ = 1
    · exact Or.inl h1
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, h1, (mem_filter.1 hχ).2⟩)
  have hcard := (card_le_card hsub).trans (card_insert_le _ _)
  have hF : ((univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ)
      ≤ ((univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) + 1 := by exact_mod_cast hcard
  have h1 : 1 ≤ ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := one_le_mul_of_one_le_of_one_le hpowE1 h2ℓ
  have hQ4 : (q : ℝ) * (T + 6) ≤ 4 * ((q : ℝ) * T) := by nlinarith
  have hQE : ((q : ℝ) * (T + 6)) ^ E ≤ 256 * ((q : ℝ) * T) ^ E := by
    calc ((q : ℝ) * (T + 6)) ^ E ≤ (4 * ((q : ℝ) * T)) ^ E := Real.rpow_le_rpow (by positivity) hQ4 hE0
      _ = 4 ^ E * ((q : ℝ) * T) ^ E := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 4 ^ (4 : ℝ) * ((q : ℝ) * T) ^ E :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE4) hpowE
      _ = 256 * ((q : ℝ) * T) ^ E := by norm_num
  have hZ := hCT q σ T hσ hσ1 hT
  rw [← hE] at hZ
  have hstep : CT * ((q : ℝ) * (T + 6)) ^ E ≤ 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by
    calc CT * ((q : ℝ) * (T + 6)) ^ E ≤ CT * (256 * ((q : ℝ) * T) ^ E) := by gcongr
      _ = 256 * CT * ((q : ℝ) * T) ^ E * 1 := by ring
      _ ≤ 256 * CT * ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) :=
          mul_le_mul_of_nonneg_left h2ℓ (by positivity)
      _ = 256 * 2 ^ 10 * CT * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by ring
  calc _ ≤ _ := hF
    _ ≤ CT * ((q : ℝ) * (T + 6)) ^ E + ((q : ℝ) * T) ^ E * (2 ^ 10 * ℓ ^ 10) := add_le_add hZ h1
    _ ≤ (2 ^ 10 + 256 * 2 ^ 10 * CT) * ((q : ℝ) * T) ^ E * ℓ ^ 10 := by linarith

/-! ### Two worked instances -/

/-- A worked instance on `[5/6, 101/120]`: `y = 251/500` (`cy = 1003/2`, from `h5`), `lam = 10041/10000`
(`2y + ε` rounded up), `a = 6693/10000` (`3(a + ε)/2 ≤ lam`), `m ≤ 1339`, `Ai = 20083/10000` and `A = 5021/2500`.
At `lo = 5/6`, `h5`, `hlam1` and `h1` force `A ≥ 4y + 2ε ≥ 2.00626`. -/
def parY_example : ParY where
  M := 1339
  a := 6693 / 10000
  lam := 10041 / 10000
  lo := 5 / 6
  hi := 101 / 120
  Ai := 20083 / 10000
  A := 5021 / 2500
  cy := 1003 / 2

theorem parY_example_good : parY_example.Good where
  hM := by simp [parY_example]
  ha := by simp only [parY_example]; norm_num
  hat := by simp only [parY_example, εs]; norm_num
  hlam1 := by simp only [parY_example, εs]; norm_num
  hlam2 := by simp only [parY_example, εs]; norm_num
  hlam3 := by simp only [parY_example]; norm_num
  hlo := by simp only [parY_example]; norm_num
  hhi := by simp only [parY_example]; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parY_example, εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parY_example, εs] at *
    nlinarith
  h5 := by simp only [parY_example, εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parY_example, εs] at *
    push_cast
    nlinarith
  hA := by simp only [parY_example]; norm_num
  hA16 := by simp only [parY_example]; norm_num

/-- A worked instance on `[17/20, 11/12]` with the exponent `A = 3/(3σ₁ − 1) + 1/2000 = 60/31 + 1/2000` at
`σ₁ = 17/20`: `y = 239/500` (`cy = 955/2`), `lam = 96777/100000`, `a = 64517/100000`, `m ≤ 1291` and
`Ai = 1935667/1000000`. -/
def parY_example' : ParY where
  M := 1291
  a := 64517 / 100000
  lam := 96777 / 100000
  lo := 17 / 20
  hi := 11 / 12
  Ai := 1935667 / 1000000
  A := 60 / 31 + 1 / 2000
  cy := 955 / 2

theorem parY_example'_good : parY_example'.Good where
  hM := by simp [parY_example']
  ha := by simp only [parY_example']; norm_num
  hat := by simp only [parY_example', εs]; norm_num
  hlam1 := by simp only [parY_example', εs]; norm_num
  hlam2 := by simp only [parY_example', εs]; norm_num
  hlam3 := by simp only [parY_example']; norm_num
  hlo := by simp only [parY_example']; norm_num
  hhi := by simp only [parY_example']; norm_num
  h1 := by
    intro σ h1 h2
    simp only [parY_example', εs] at *
    nlinarith
  h2 := by
    intro σ h1 h2
    simp only [parY_example', εs] at *
    nlinarith
  h5 := by simp only [parY_example', εs]; norm_num
  h4 := by
    intro σ h2
    simp only [parY_example', εs] at *
    push_cast
    nlinarith
  hA := by simp only [parY_example']; norm_num
  hA16 := by simp only [parY_example']; norm_num

end LinnikHuxStepY

#print axioms LinnikHuxStepY.charDensity_genY
#print axioms LinnikHuxStepY.parY_example_good
#print axioms LinnikHuxStepY.parY_example'_good
