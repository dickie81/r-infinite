import Mathlib
import DegenerateFlat

/-! # Round 48's Theorem D, formal

1. **Finite dimension.** The image `W` of the ground space in `L²` is finite-dimensional
   (`finiteDimensional_groundL2`): a Riesz-separated sequence in an infinite-dimensional `W` would be
   a bounded-energy sequence of probes with no `L²`-convergent subsequence, against
   `exists_convergent_subseq`.
2. **The Green chain spans.** With `G` the Green operator of the pole (DegenerateFlat.lean), a
   filtration argument gives a nonzero `w` whose iterates `w, Gw, …, G^{m−1}w` all lie in the ground
   space; they are independent (`Ĝ` multiplies by `−1/(z² + ¼)`), so they span it.
3. **Zeros on the cross.** The last iterate `h = G^{m−1}w` has `ĥ` vanishing only on `ℝ ∪ iℝ`.

In `z`-language: `V_ℂ = ĥ · {polynomials of degree < m in z²}`, round 48's Theorem D.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## The ground space in `L²` -/

/-- The ground space mapped into `L²`. -/
def iotaGS (a : ℝ) : groundSpace a →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun x := x.2.1.memL2.toLp x.1
  map_add' x y := MemLp.toLp_add x.2.1.memL2 y.2.1.memL2
  map_smul' c x := MemLp.toLp_const_smul c x.2.1.memL2

theorem norm_iotaGS_sq {a : ℝ} (x : groundSpace a) : ‖iotaGS a x‖ ^ 2 = normSq x.1 := by
  show ‖x.2.1.memL2.toLp x.1‖ ^ 2 = _
  rw [L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [x.2.1.memL2.coeFn_toLp] with t ht
  rw [ht]

/-- The archimedean energy of a ground-space element is controlled by its norm. -/
theorem archE_le_of_mem {a : ℝ} {g : ℝ → ℝ} (hg : g ∈ groundSpace a) :
    archE g ≤ (|lam a| + |weilConst| + 2 * primeWeight a) * normSq g := by
  have hq : weilQ a g = lam a * normSq g := hg.2
  have hN := normSq_nonneg g
  have hS := abs_prime_sum_le hg.1
  have e : archE g = lam a * normSq g - 2 * poleR g a ^ 2 - weilConst * normSq g + 2 * primeS g := by
    rw [← hq, weilQ_eq']; ring
  have hS' : primeS g ≤ primeWeight a * normSq g := (le_abs_self _).trans hS
  have h1 : lam a * normSq g ≤ |lam a| * normSq g := mul_le_mul_of_nonneg_right (le_abs_self _) hN
  have h2 : -(weilConst * normSq g) ≤ |weilConst| * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs _) hN
  nlinarith [sq_nonneg (poleR g a)]

/-- **The ground space is finite-dimensional** (its image in `L²`). -/
theorem finiteDimensional_groundL2 {a : ℝ} (ha : 0 < a) :
    FiniteDimensional ℝ (LinearMap.range (iotaGS a)) := by
  by_contra hfin
  obtain ⟨R, f, hR, hfR, hsep⟩ :=
    exists_seq_norm_le_one_le_norm_sub (𝕜 := ℝ) (E := LinearMap.range (iotaGS a)) hfin
  have hx : ∀ n, ∃ x : groundSpace a, iotaGS a x = (f n : Lp ℝ 2 volume) :=
    fun n => LinearMap.mem_range.1 (f n).2
  choose x hxf using hx
  set h : ℕ → ℝ → ℝ := fun n => (x n).1
  have hp : ∀ n, Probe a (h n) := fun n => (x n).2.1
  have hN : ∀ n, normSq (h n) ≤ R ^ 2 := by
    intro n
    rw [← norm_iotaGS_sq, hxf n, Submodule.norm_coe]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfR n) 2
  set K := |lam a| + |weilConst| + 2 * primeWeight a
  have hK : 0 ≤ K := by
    have : 0 ≤ primeWeight a := by
      unfold primeWeight
      exact Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.sqrt_nonneg _)
    positivity
  have hC : ∀ n, archE (h n) ≤ K * R ^ 2 :=
    fun n => (archE_le_of_mem (x n).2).trans (mul_le_mul_of_nonneg_left (hN n) hK)
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha hp hN hC
  have hconv := tendsto_toLp (fun j => (hp (φ j)).memL2) hG hlim
  have hcau := hconv.cauchySeq
  obtain ⟨N, hN'⟩ := Metric.cauchySeq_iff'.1 hcau 1 one_pos
  have hd := hN' (N + 1) (by omega)
  have hsep' := hsep (show φ (N + 1) ≠ φ N from (hφ (Nat.lt_succ_self N)).ne')
  have e1 : ((hp (φ (N + 1))).memL2.toLp (h (φ (N + 1)))) = (f (φ (N + 1)) : Lp ℝ 2 volume) :=
    hxf _
  have e2 : ((hp (φ N)).memL2.toLp (h (φ N))) = (f (φ N) : Lp ℝ 2 volume) := hxf _
  rw [dist_eq_norm, e1, e2, ← Submodule.coe_sub, Submodule.norm_coe] at hd
  linarith

/-! ## Green chains -/

/-- The iterates `G^i f` of the Green operator of the pole. -/
def Gi (a : ℝ) (i : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (fun φ => Gpole φ a)^[i] f

theorem Gi_succ (a : ℝ) (i : ℕ) (f : ℝ → ℝ) : Gi a (i + 1) f = Gpole (Gi a i f) a :=
  Function.iterate_succ_apply' _ _ _

theorem Gpole_smul' (c : ℝ) (f : ℝ → ℝ) (a : ℝ) : Gpole (c • f) a = c • Gpole f a := by
  funext x
  unfold Gpole
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext y; ring

theorem Gpole_add' {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (a : ℝ) :
    Gpole (f + g) a = Gpole f a + Gpole g a := by
  funext x
  have := Gpole_lin (a := a) hf hg 1 1 x
  simp only [one_mul] at this
  exact this

theorem Gi_smul (a : ℝ) (c : ℝ) (f : ℝ → ℝ) : ∀ i, Gi a i (c • f) = c • Gi a i f
  | 0 => rfl
  | i + 1 => by rw [Gi_succ, Gi_succ, Gi_smul a c f i, Gpole_smul']

theorem Gi_zero_fun (a : ℝ) (i : ℕ) : Gi a i 0 = 0 := by
  have := Gi_smul a 0 0 i
  simpa using this

theorem poleR_zero_fun (a : ℝ) : poleR 0 a = 0 := by simp [poleR]

/-- `f` starts a Green chain of length `j`: `f, Gf, …, G^j f` lie in the ground space and all but
the last are pole-free. -/
def IsChain (a : ℝ) (j : ℕ) (f : ℝ → ℝ) : Prop :=
  (∀ i ≤ j, Gi a i f ∈ groundSpace a) ∧ ∀ i < j, poleR (Gi a i f) a = 0

theorem Gi_add {a : ℝ} {j : ℕ} {f g : ℝ → ℝ} (hf : IsChain a j f) (hg : IsChain a j g) :
    ∀ i ≤ j + 1, Gi a i (f + g) = Gi a i f + Gi a i g
  | 0, _ => rfl
  | i + 1, hi => by
    rw [Gi_succ, Gi_succ, Gi_succ, Gi_add hf hg i (by omega),
      Gpole_add' (hf.1 i (by omega)).1.memL2 (hg.1 i (by omega)).1.memL2]

/-- The chains of length `j` form a subspace. -/
def chainSpace (a : ℝ) (j : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsChain a j f}
  zero_mem' := by
    refine ⟨fun i _ => ?_, fun i _ => ?_⟩
    · rw [Gi_zero_fun]; exact (groundSpace a).zero_mem
    · rw [Gi_zero_fun]; exact poleR_zero_fun a
  add_mem' := by
    intro f g hf hg
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [Gi_add hf hg i (by omega)]; exact (groundSpace a).add_mem (hf.1 i hi) (hg.1 i hi)
    · rw [Gi_add hf hg i (by omega)]
      rw [show Gi a i f + Gi a i g = fun t => Gi a i f t + Gi a i g t from rfl,
        poleR_add (hf.1 i hi.le).1.memL2 (hg.1 i hi.le).1.memL2, hf.2 i hi, hg.2 i hi, add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [Gi_smul]; exact (groundSpace a).smul_mem c (hf.1 i hi)
    · rw [Gi_smul, show c • Gi a i f = fun t => c * Gi a i f t from rfl, poleR_smul, hf.2 i hi,
        mul_zero]

theorem chainSpace_zero (a : ℝ) {f : ℝ → ℝ} : f ∈ chainSpace a 0 ↔ f ∈ groundSpace a := by
  constructor
  · intro h; exact h.1 0 le_rfl
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    rw [Nat.le_zero.1 hi]; exact h

/-- **One step of the filtration.** A single linear condition on `chainSpace j` puts `f` in
`chainSpace (j + 1)`: `(G^j f)^(i/2) = 0` if some ground-space element has a pole, and
`(G^{j+1} f)^(i/2) = 0` if none does. -/
theorem chain_step {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    ∃ φ : (ℝ → ℝ) → ℝ,
      (∀ f ∈ chainSpace a j, ∀ g ∈ chainSpace a j, ∀ c : ℝ, φ (f + c • g) = φ f + c * φ g) ∧
      ∀ f ∈ chainSpace a j, φ f = 0 → f ∈ chainSpace a (j + 1) := by
  have lin : ∀ n ≤ j + 1, ∀ f ∈ chainSpace a j, ∀ g ∈ chainSpace a j, ∀ c : ℝ,
      Gi a n (f + c • g) = fun t => Gi a n f t + c * Gi a n g t := by
    intro n hn f hf g hg c
    have hcg : c • g ∈ chainSpace a j := (chainSpace a j).smul_mem c hg
    rw [Gi_add hf hcg n hn, Gi_smul]; rfl
  by_cases hk : ∃ k ∈ groundSpace a, poleR k a ≠ 0
  · obtain ⟨k, hkV, hkp⟩ := hk
    refine ⟨fun f => poleR (Gi a j f) a, fun f hf g hg c => ?_, fun f hf h0 => ?_⟩
    · simp only
      rw [lin j (by omega) f hf g hg c, poleR_add (hf.1 j le_rfl).1.memL2
        ((hg.1 j le_rfl).1.memL2.const_mul c), poleR_smul]
    · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hf.1 i (by omega)
        · rw [show i = j + 1 by omega, Gi_succ]
          exact G_mem_partner ha (hf.1 j le_rfl) h0 hkV hkp
      · rcases Nat.lt_or_ge i j with h | h
        · exact hf.2 i h
        · rw [show i = j by omega]; exact h0
  · push Not at hk
    refine ⟨fun f => poleR (Gi a (j + 1) f) a, fun f hf g hg c => ?_, fun f hf h0 => ?_⟩
    · simp only
      have m1 : MemLp (Gi a (j + 1) f) 2 volume := by
        rw [Gi_succ]; exact Gpole_memLp (hf.1 j le_rfl).1 (hk _ (hf.1 j le_rfl))
      have m2 : MemLp (Gi a (j + 1) g) 2 volume := by
        rw [Gi_succ]; exact Gpole_memLp (hg.1 j le_rfl).1 (hk _ (hg.1 j le_rfl))
      rw [lin (j + 1) le_rfl f hf g hg c, poleR_add m1 (m2.const_mul c), poleR_smul]
    · refine ⟨fun i hi => ?_, fun i _ => hk _ (hf.1 i (by omega))⟩
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact hf.1 i (by omega)
      · rw [show i = j + 1 by omega, Gi_succ]
        have h0' : poleR (Gpole (Gi a j f) a) a = 0 := by rw [← Gi_succ]; exact h0
        exact G_mem_pole_free ha (hf.1 j le_rfl) (hk _ (hf.1 j le_rfl)) h0'

/-! ## Counting dimensions -/

/-- A subspace cut out of `A` by one linear condition loses at most one dimension in the image. -/
theorem finrank_map_le_succ {M W : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup W]
    [Module ℝ W] [FiniteDimensional ℝ W] (ι : M →ₗ[ℝ] W) {A B : Submodule ℝ M} (φ : M → ℝ)
    (hlin : ∀ x ∈ A, ∀ y ∈ A, ∀ c : ℝ, φ (x + c • y) = φ x + c * φ y)
    (hker : ∀ x ∈ A, φ x = 0 → x ∈ B) :
    Module.finrank ℝ (A.map ι) ≤ Module.finrank ℝ (B.map ι) + 1 := by
  by_cases h : ∃ x0 ∈ A, φ x0 ≠ 0
  · obtain ⟨x0, hx0, hφ⟩ := h
    have hle : A.map ι ≤ B.map ι ⊔ Submodule.span ℝ {ι x0} := by
      rintro _ ⟨x, hx, rfl⟩
      set r := φ x / φ x0
      have hxB : x + (-r) • x0 ∈ B := by
        refine hker _ (A.add_mem hx (A.smul_mem _ hx0)) ?_
        rw [hlin x hx x0 hx0]; simp only [r]; field_simp; ring
      have e : ι x = ι (x + (-r) • x0) + r • ι x0 := by
        rw [map_add, map_smul]; module
      rw [e]
      exact Submodule.add_mem_sup ⟨_, hxB, rfl⟩ (Submodule.mem_span_singleton.2 ⟨r, rfl⟩)
    calc Module.finrank ℝ (A.map ι)
        ≤ Module.finrank ℝ (B.map ι ⊔ Submodule.span ℝ {ι x0} : Submodule ℝ W) :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank ℝ (B.map ι) + Module.finrank ℝ (Submodule.span ℝ {ι x0}) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ _ := by
          gcongr
          exact (finrank_span_le_card _).trans (by simp)
  · push Not at h
    have : A.map ι ≤ B.map ι := Submodule.map_mono fun x hx => hker x hx (h x hx)
    exact (Submodule.finrank_mono this).trans (Nat.le_succ _)

/-- The dimension of the ground space. -/
def gdim (a : ℝ) : ℕ := Module.finrank ℝ (LinearMap.range (iotaGS a))

/-- The chain subspaces, inside the ground space. -/
def chainSub (a : ℝ) (j : ℕ) : Submodule ℝ (groundSpace a) :=
  (chainSpace a j).comap (groundSpace a).subtype

theorem finrank_chain {a : ℝ} (ha : 0 < a) (j : ℕ) :
    gdim a ≤ Module.finrank ℝ ((chainSub a j).map (iotaGS a).rangeRestrict) + j := by
  have := finiteDimensional_groundL2 ha
  induction j with
  | zero =>
    have htop : chainSub a 0 = ⊤ := by
      ext x; simp only [Submodule.mem_top, iff_true]
      exact (chainSpace_zero a).2 x.2
    rw [htop, Submodule.map_top, LinearMap.range_rangeRestrict, finrank_top, add_zero]; rfl
  | succ j ih =>
    obtain ⟨φ, hlin, hker⟩ := chain_step ha.le j
    have := finrank_map_le_succ (iotaGS a).rangeRestrict (A := chainSub a j)
      (B := chainSub a (j + 1)) (fun x => φ x.1)
      (fun x hx y hy c => hlin x.1 hx y.1 hy c) (fun x hx h0 => hker x.1 hx h0)
    omega

theorem gdim_pos {a : ℝ} (ha : 0 < a) : 0 < gdim a := by
  have := finiteDimensional_groundL2 ha
  obtain ⟨g, hg⟩ := exists_groundState ha
  have hgV := ((isGroundState_iff ha).1 hg)
  apply Module.finrank_pos_iff_exists_ne_zero.2
  refine ⟨⟨iotaGS a ⟨g, hgV.1⟩, ⟨_, rfl⟩⟩, fun h0 => ?_⟩
  have h1 : iotaGS a ⟨g, hgV.1⟩ = 0 := congrArg Subtype.val h0
  have := norm_iotaGS_sq (a := a) ⟨g, hgV.1⟩
  rw [h1, norm_zero] at this
  simp only at this
  rw [hgV.2] at this; norm_num at this

/-- **A Green chain of full length.** With `m` the dimension of the ground space, some nonzero `w`
has `w, Gw, …, G^{m−1}w` in the ground space, all but the last pole-free. -/
theorem exists_long_chain {a : ℝ} (ha : 0 < a) :
    ∃ w, IsChain a (gdim a - 1) w ∧ 0 < normSq w := by
  have := finiteDimensional_groundL2 ha
  have h1 := finrank_chain ha (gdim a - 1)
  have h2 := gdim_pos ha
  have hpos : 0 < Module.finrank ℝ ((chainSub a (gdim a - 1)).map (iotaGS a).rangeRestrict) := by
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := (chainSub a (gdim a - 1)).map (iotaGS a).rangeRestrict)
    (fun h => by rw [h, finrank_bot] at hpos; exact lt_irrefl _ hpos)
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x.1, hx, ?_⟩
  rcases (normSq_nonneg x.1).lt_or_eq with h | h
  · exact h
  · exfalso; apply hy0
    have := norm_iotaGS_sq x
    rw [← h] at this
    have h0 : iotaGS a x = 0 := by
      have : ‖iotaGS a x‖ = 0 := by nlinarith [norm_nonneg (iotaGS a x)]
      exact norm_eq_zero.1 this
    exact Subtype.ext h0

/-! ## Fourier transforms along a chain -/

/-- `Ĝ` multiplies by `q(t) = −1/(t² + ¼)` on the real line. -/
def qr (t : ℝ) : ℝ := -1 / (t ^ 2 + 1 / 4)

theorem den_ne (t : ℝ) : ((t : ℂ)) ^ 2 - (Complex.I / 2) ^ 2 = (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) := by
  rw [div_pow, Complex.I_sq]; push_cast; ring

theorem Gi_hat {a : ℝ} (ha : 0 ≤ a) {j : ℕ} {w : ℝ → ℝ} (hc : IsChain a j w) :
    ∀ i ≤ j, ∀ t : ℝ, ghatC (Gi a i w) a t = ((qr t : ℝ) : ℂ) ^ i * ghatC w a t
  | 0, _, t => by simp [Gi]
  | i + 1, hi, t => by
    have hq : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
    have hz : ((t : ℂ)) ^ 2 ≠ (Complex.I / 2) ^ 2 := by
      intro e
      have h0 : (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) = 0 := by rw [← den_ne, e, sub_self]
      rw [Complex.ofReal_eq_zero] at h0; linarith
    have h := Gpole_hat (hc.1 i (by omega)).1 ha (hc.2 i (by omega)) hz
    rw [Gi_succ, show ghatC (Gpole (Gi a i w) a) a t
      = ∫ x in (-a)..a, ((Gpole (Gi a i w) a x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x) from rfl,
      h, den_ne, Gi_hat ha hc i (by omega) t, pow_succ]
    have hq' : (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    unfold qr; push_cast
    field_simp
    ring

theorem ghatC_add {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (a : ℝ) (z : ℂ) :
    ghatC (f + g) a z = ghatC f a z + ghatC g a z := by
  have ii : ∀ {h : ℝ → ℝ}, MemLp h 2 volume →
      IntervalIntegrable (fun u => ((h u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)) volume (-a) a := by
    intro h hh
    have hr := memLp_intervalIntegrable hh (-a) a
    exact (show IntervalIntegrable (fun u => ((h u : ℝ) : ℂ)) volume (-a) a from
      ⟨hr.1.ofReal, hr.2.ofReal⟩).mul_continuousOn (by fun_prop)
  unfold ghatC
  rw [← intervalIntegral.integral_add (ii hf) (ii hg)]
  congr 1; funext u; simp only [Pi.add_apply]; push_cast; ring

/-- The transform at a real point, as a linear functional on the ground space. -/
def ghatL (a t : ℝ) : groundSpace a →ₗ[ℝ] ℂ where
  toFun x := ghatC x.1 a t
  map_add' x y := ghatC_add x.2.1.memL2 y.2.1.memL2 a t
  map_smul' c x := by
    show ghatC (fun u => c * x.1 u) a t = _
    rw [ghatC_smul]; simp [Complex.real_smul]

theorem iota_zero_ae {a : ℝ} {x : groundSpace a} (h : iotaGS a x = 0) : x.1 =ᵐ[volume] 0 :=
  ae_zero_of_normSq x.2.1.memL2 (by rw [← norm_iotaGS_sq, h, norm_zero]; ring)

theorem ghatL_of_iota {a : ℝ} (t : ℝ) {x : groundSpace a} (h : iotaGS a x = 0) :
    ghatL a t x = 0 := by
  show ghatC x.1 a t = 0
  rw [ghatC_congr_ae (iota_zero_ae h)]
  simp [ghatC]

/-- The chain as ground-space vectors. -/
def chainVec {a : ℝ} {j : ℕ} {w : ℝ → ℝ} (hc : IsChain a j w) (i : Fin (j + 1)) : groundSpace a :=
  ⟨Gi a i w, hc.1 i (Nat.lt_succ_iff.1 i.2)⟩

theorem ghatL_comb {a : ℝ} (ha : 0 ≤ a) {j : ℕ} {w : ℝ → ℝ} (hc : IsChain a j w)
    (c : Fin (j + 1) → ℝ) (t : ℝ) :
    ghatL a t (∑ i, c i • chainVec hc i)
      = (∑ i : Fin (j + 1), (c i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul]
  show (c i : ℂ) * ghatC (Gi a i w) a t = _
  rw [Gi_hat ha hc i (Nat.lt_succ_iff.1 i.2) t]; ring

/-! ## Polynomials in `q` -/

def polyOf {n : ℕ} (c : Fin n → ℂ) : Polynomial ℂ := ∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

theorem polyOf_eval {n : ℕ} (c : Fin n → ℂ) (x : ℂ) :
    (polyOf c).eval x = ∑ i, c i * x ^ (i : ℕ) := by
  simp [polyOf, Polynomial.eval_finsetSum]

theorem polyOf_coeff {n : ℕ} (c : Fin n → ℂ) (i : Fin n) : (polyOf c).coeff i = c i := by
  rw [polyOf, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul_X_pow]; simp
  · intro j _ hji
    rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff]
    intro h; exact absurd (Fin.ext h.symm) hji
  · intro h; exact absurd (Finset.mem_univ i) h

theorem polyOf_coeff_ge {n : ℕ} (c : Fin n → ℂ) {k : ℕ} (hk : n ≤ k) : (polyOf c).coeff k = 0 := by
  rw [polyOf, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff]
  intro h; have := j.2; omega

/-- A polynomial vanishing at `q(t)` for all `t` in an interval of positive reals is zero. -/
theorem poly_eq_zero_of_interval (P : Polynomial ℂ) {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε)
    (h : ∀ t ∈ Ioo α (α + ε), P.eval ((qr t : ℝ) : ℂ) = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : InjOn (fun t : ℝ => ((qr t : ℝ) : ℂ)) (Ioo α (α + ε)) := by
    intro s hs t ht hst
    have e : qr s = qr t := Complex.ofReal_injective hst
    have hs0 : 0 < s := hα.trans_lt hs.1
    have ht0 : 0 < t := hα.trans_lt ht.1
    unfold qr at e
    have hs' : (0 : ℝ) < s ^ 2 + 1 / 4 := by positivity
    have ht' : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
    rw [div_eq_div_iff hs'.ne' ht'.ne'] at e
    have : (s - t) * (s + t) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  exact ((Set.Ioo_infinite (by linarith)).image hinj).mono
    (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)

/-- A nonzero probe has a transform that is nonzero on an interval of positive reals. -/
theorem exists_interval_ghat {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hp : Probe a w)
    (hpos : 0 < normSq w) :
    ∃ α ε : ℝ, 0 ≤ α ∧ 0 < ε ∧ ∀ t ∈ Ioo α (α + ε), ghatC w a t ≠ 0 := by
  set c := 1 / Real.sqrt (normSq w)
  have hsq : Real.sqrt (normSq w) ^ 2 = normSq w := Real.sq_sqrt hpos.le
  have hs0 : 0 < Real.sqrt (normSq w) := Real.sqrt_pos.2 hpos
  have hn : normSq (fun t => c * w t) = 1 := by
    rw [normSq_smul]; simp only [c]; rw [div_pow, hsq]; field_simp
  obtain ⟨t₁, ht₁⟩ := exists_real_ghatC_ne ha (probe_smul hp c) hn
  rw [ghatC_smul] at ht₁
  have ht₁' : ghatC w a t₁ ≠ 0 := fun h => ht₁ (by rw [h, mul_zero])
  have habs : ghatC w a (|t₁| : ℝ) ≠ 0 := by
    rcases le_or_gt 0 t₁ with h | h
    · rw [abs_of_nonneg h]; exact ht₁'
    · rw [abs_of_neg h, Complex.ofReal_neg, ghatC_neg_of_even hp.memL2 hp.even]; exact ht₁'
  have hcont : Continuous fun t : ℝ => ghatC w a t :=
    (ghatC_differentiable (probe_integrable hp).intervalIntegrable).continuous.comp
      continuous_ofReal
  have hopen : IsOpen {t : ℝ | ghatC w a t ≠ 0} := hcont.isOpen_preimage _ isOpen_compl_singleton
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen _ habs
  refine ⟨|t₁|, ε, abs_nonneg _, hε, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [ht.1])]
  linarith [ht.2]

/-! ## Independence and spanning -/

/-- **The Green chain is independent.** -/
theorem chain_linearIndependent {a : ℝ} (ha : 0 < a) {j : ℕ} {w : ℝ → ℝ} (hc : IsChain a j w)
    (hpos : 0 < normSq w) :
    LinearIndependent ℝ (fun i => (iotaGS a).rangeRestrict (chainVec hc i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  have hS : iotaGS a (∑ i, c i • chainVec hc i) = 0 := by
    have h2 : (iotaGS a).rangeRestrict (∑ i, c i • chainVec hc i) = 0 := by
      simpa [map_sum, map_smul] using hsum
    exact congrArg Subtype.val h2
  have hw : Probe a w := (hc.1 0 (Nat.zero_le _)).1
  obtain ⟨α, ε, hα, hε, hne⟩ := exists_interval_ghat ha hw hpos
  have hP : polyOf (fun i => (c i : ℂ)) = 0 := poly_eq_zero_of_interval _ hα hε fun t ht => by
    have h1 := ghatL_comb ha.le hc c t
    rw [ghatL_of_iota t hS] at h1
    rw [polyOf_eval]
    exact (mul_eq_zero.1 h1.symm).resolve_right (hne t ht)
  have := polyOf_coeff (fun i => (c i : ℂ)) i
  rw [hP, Polynomial.coeff_zero] at this
  exact_mod_cast this.symm

/-- **The Green chain spans the ground space** (in `L²`), once it has full length. -/
theorem chain_span {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : IsChain a (gdim a - 1) w)
    (hpos : 0 < normSq w) (v : groundSpace a) :
    ∃ c : Fin (gdim a - 1 + 1) → ℝ, iotaGS a (∑ i, c i • chainVec hc i - v) = 0 := by
  have := finiteDimensional_groundL2 ha
  have hcard : Fintype.card (Fin (gdim a - 1 + 1)) = Module.finrank ℝ (LinearMap.range (iotaGS a)) := by
    rw [Fintype.card_fin]; have := gdim_pos ha; unfold gdim at this ⊢; omega
  have htop := (chain_linearIndependent ha hc hpos).span_eq_top_of_card_eq_finrank' hcard
  have hv : (iotaGS a).rangeRestrict v ∈ Submodule.span ℝ
      (Set.range fun i => (iotaGS a).rangeRestrict (chainVec hc i)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hcv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  refine ⟨c, ?_⟩
  have h2 : (iotaGS a).rangeRestrict (∑ i, c i • chainVec hc i - v) = 0 := by
    rw [map_sub, map_sum]; simp only [map_smul]; rw [hcv, sub_self]
  exact congrArg Subtype.val h2

/-- **Theorem D, spanning (pointwise a.e. form).** Every ground-space element is a.e. a combination
of the chain `w, Gw, …, G^{m−1}w`. -/
theorem chain_span_ae {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : IsChain a (gdim a - 1) w)
    (hpos : 0 < normSq w) {v : ℝ → ℝ} (hv : v ∈ groundSpace a) :
    ∃ c : Fin (gdim a - 1 + 1) → ℝ, v =ᵐ[volume] fun x => ∑ i, c i * Gi a i w x := by
  obtain ⟨c, hc0⟩ := chain_span ha hc hpos ⟨v, hv⟩
  refine ⟨c, ?_⟩
  filter_upwards [iota_zero_ae hc0] with x hx
  have : (∑ i, c i • chainVec hc i : groundSpace a).1 x - v x = 0 := hx
  rw [Submodule.coe_sum, Finset.sum_apply] at this
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, chainVec] at this
  linarith

/-- **Theorem D, spanning (Fourier form).** Every ground-space element has `v̂ = P(q)·ŵ` on the real
line, `P` a polynomial of degree `< m` in `q = −1/(t² + ¼)`. -/
theorem chain_span_hat {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : IsChain a (gdim a - 1) w)
    (hpos : 0 < normSq w) {v : ℝ → ℝ} (hv : v ∈ groundSpace a) :
    ∃ c : Fin (gdim a - 1 + 1) → ℝ, ∀ t : ℝ,
      ghatC v a t = (∑ i : Fin (gdim a - 1 + 1), (c i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t := by
  obtain ⟨c, hc0⟩ := chain_span ha hc hpos ⟨v, hv⟩
  refine ⟨c, fun t => ?_⟩
  have h1 := ghatL_of_iota t hc0
  rw [map_sub, ghatL_comb ha.le hc c t, sub_eq_zero] at h1
  exact h1.symm

/-! ## Zeros on the cross -/

/-- **Each off-cross zero of `v̂` is a root of `P_v`.** -/
theorem offcross_root {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : IsChain a (gdim a - 1) w)
    (hwpos : 0 < normSq w) {v : ℝ → ℝ} (hv : v ∈ groundSpace a)
    {ev : Fin (gdim a - 1 + 1) → ℝ}
    (hev : ∀ t : ℝ, ghatC v a t
      = (∑ i : Fin (gdim a - 1 + 1), (ev i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t)
    {ω : ℂ} (hω : ghatC v a ω = 0) (hσ : (ω ^ 2).im ≠ 0) :
    (polyOf fun i : Fin (gdim a - 1 + 1) => (ev i : ℂ)).IsRoot (-1 / (1 / 4 + ω ^ 2)) := by
  have hω0 : ω ≠ 0 := by rintro rfl; apply hσ; simp
  obtain ⟨hu, hv'⟩ := green_mem_groundSpace ha hv hω hσ
  obtain ⟨c, hcu⟩ := chain_span_hat ha hc hwpos hu
  obtain ⟨d, hdv⟩ := chain_span_hat ha hc hwpos hv'
  have hw : Probe a w := (hc.1 0 (Nat.zero_le _)).1
  obtain ⟨α, ε, hα, hε, hne⟩ := exists_interval_ghat ha hw hwpos
  have hcont := hSw_continuous hv.1.memL2 a ω
  set P := polyOf (fun i : Fin (gdim a - 1 + 1) => (c i : ℂ) + Complex.I * d i)
  set Pv := polyOf (fun i : Fin (gdim a - 1 + 1) => (ev i : ℂ))
  set β : ℂ := 1 / 4 + ω ^ 2
  have hR : P * (1 + Polynomial.C β * Polynomial.X) - Polynomial.X * Pv = 0 := by
    refine poly_eq_zero_of_interval _ hα hε fun t ht => ?_
    obtain ⟨Q, hQe⟩ : ∃ Q : ℂ, Q = ((qr t : ℝ) : ℂ) := ⟨_, rfl⟩
    rw [← hQe]
    set D : ℂ := (t : ℂ) ^ 2 + 1 / 4
    have hD : D ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
      have : ((t ^ 2 + 1 / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      simpa [D] using this
    have hQ : Q = -1 / D := by rw [hQe]; simp only [D, qr]; push_cast; ring
    have hz : ((t : ℂ)) ^ 2 ≠ ω ^ 2 := by
      intro e; apply hσ; rw [← e]; norm_cast
    have hden : (t : ℂ) ^ 2 - ω ^ 2 ≠ 0 := sub_ne_zero.2 hz
    have hsplit : (∫ x in (-a)..a, hSw v a ω x * Complex.exp (Complex.I * t * x))
        = ghatC (fun x => (hSw v a ω x).re) a t + Complex.I * ghatC (fun x => (hSw v a ω x).im) a t := by
      have ci : ∀ F : ℝ → ℝ, Continuous F →
          IntervalIntegrable (fun x => ((F x : ℝ) : ℂ) * Complex.exp (Complex.I * t * x)) volume (-a) a :=
        fun F hF => ((continuous_ofReal.comp hF).mul (by fun_prop)).intervalIntegrable _ _
      unfold ghatC
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (ci (fun x => (hSw v a ω x).re) (Complex.continuous_re.comp hcont))
        ((ci (fun x => (hSw v a ω x).im) (Complex.continuous_im.comp hcont)).const_mul _)]
      congr 1; funext x
      conv_lhs => rw [← Complex.re_add_im (hSw v a ω x)]
      ring
    have hhat := hSw_hat' hv.1 ha.le hω hω0 hz
    rw [hsplit, hcu t, hdv t, hev t, ← hQe] at hhat
    have hwt := hne t ht
    have hP : P.eval Q = (∑ i : Fin (gdim a - 1 + 1), (c i : ℂ) * Q ^ (i : ℕ))
        + Complex.I * ∑ i : Fin (gdim a - 1 + 1), (d i : ℂ) * Q ^ (i : ℕ) := by
      rw [polyOf_eval, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    have hPv : Pv.eval Q = ∑ i : Fin (gdim a - 1 + 1), (ev i : ℂ) * Q ^ (i : ℕ) := polyOf_eval _ _
    have e : P.eval Q * ((t : ℂ) ^ 2 - ω ^ 2) = -Pv.eval Q := by
      have h2 := congrArg (· * ((t : ℂ) ^ 2 - ω ^ 2)) hhat
      rw [neg_mul, div_mul_cancel₀ _ hden] at h2
      have h3 : (P.eval Q * ((t : ℂ) ^ 2 - ω ^ 2) + Pv.eval Q) * ghatC w a t = 0 := by
        rw [hP, hPv]; linear_combination h2
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 h3).resolve_right hwt)
    have h1 : 1 + β * Q = ((t : ℂ) ^ 2 - ω ^ 2) * (-Q) := by
      have hDi : ((t : ℂ) ^ 2 + 1 / 4) * ((t : ℂ) ^ 2 + 1 / 4)⁻¹ = 1 := mul_inv_cancel₀ hD
      rw [hQ, div_eq_mul_inv]; simp only [β, D]
      linear_combination -hDi
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [h1]
    linear_combination (-Q) * e
  -- evaluate the identity at `X = −1/β`
  have hβ : β ≠ 0 := by
    intro h; apply hσ
    have : (ω ^ 2).im = β.im := by simp [β]
    rw [this, h, Complex.zero_im]
  have hx0 : (-1 / β) ≠ 0 := by
    rw [neg_div]; exact neg_ne_zero.2 (one_div_ne_zero hβ)
  have hev0 := congrArg (Polynomial.eval (-1 / β)) hR
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero] at hev0
  have h1 : 1 + β * (-1 / β) = 0 := by field_simp; ring
  rw [h1, mul_zero, zero_sub, neg_eq_zero] at hev0
  exact (mul_eq_zero.1 hev0).resolve_left hx0

theorem sum_indicator_pow (n : ℕ) (x : ℂ) :
    (∑ i : Fin (n + 1), (((if (i : ℕ) = n then (1 : ℝ) else 0 : ℝ)) : ℂ) * x ^ (i : ℕ)) = x ^ n := by
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro i _ hi
    have : (i : ℕ) ≠ n := fun h => hi (Fin.ext (by simp [h]))
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Theorem D, zeros on the cross.** With `h = G^{m−1}w` the top of a full Green chain, every zero
`ω` of `ĥ` has `ω² ∈ ℝ`, i.e. `ω ∈ ℝ ∪ iℝ`: `ĥ = q^{m−1}ŵ`, so `P_h = X^{m−1}`, which has no root at
`−1/(¼ + ω²) ≠ 0` (`offcross_root`). -/
theorem chain_top_zeros {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : IsChain a (gdim a - 1) w)
    (hpos : 0 < normSq w) {ω : ℂ} (hω : ghatC (Gi a (gdim a - 1) w) a ω = 0) :
    (ω ^ 2).im = 0 := by
  by_contra hσ
  set n := gdim a - 1
  set ev : Fin (n + 1) → ℝ := fun i => if (i : ℕ) = n then 1 else 0
  have hev : ∀ t : ℝ, ghatC (Gi a n w) a t
      = (∑ i : Fin (n + 1), (ev i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t := by
    intro t
    rw [Gi_hat ha.le hc n le_rfl t, sum_indicator_pow]
  have hroot := offcross_root ha hc hpos (hc.1 n le_rfl) hev hω hσ
  rw [Polynomial.IsRoot, polyOf_eval, sum_indicator_pow] at hroot
  have hβ : (1 / 4 + ω ^ 2 : ℂ) ≠ 0 := by
    intro h; apply hσ
    have : (ω ^ 2).im = (1 / 4 + ω ^ 2 : ℂ).im := by simp
    rw [this, h, Complex.zero_im]
  exact pow_ne_zero n (div_ne_zero (neg_ne_zero.2 one_ne_zero) hβ) hroot

/-- **Round 48's Theorem D, formal.** With `m = dim V` (finite, `finiteDimensional_groundL2`), there
is a nonzero `w` whose Green chain `w, Gw, …, G^{m−1}w` lies in the ground space (all but the last
pole-free), is linearly independent, and spans it a.e. Every zero `ω` of `ĥ`, `h = G^{m−1}w`, has
`ω² ∈ ℝ`. Since `(G^i w)^ = q^i ŵ` (`Gi_hat`, `q = −1/(t² + ¼)`), the spanning statement is
`V_ℂ = ĥ · {polynomials of degree < m in z²}` on the real line. -/
theorem theoremD {a : ℝ} (ha : 0 < a) :
    ∃ w, IsChain a (gdim a - 1) w ∧ 0 < normSq w ∧
      (∃ hc : IsChain a (gdim a - 1) w,
        LinearIndependent ℝ (fun i => (iotaGS a).rangeRestrict (chainVec hc i))) ∧
      (∀ v ∈ groundSpace a, ∃ c : Fin (gdim a - 1 + 1) → ℝ,
        v =ᵐ[volume] fun x => ∑ i, c i * Gi a i w x) ∧
      ∀ ω : ℂ, ghatC (Gi a (gdim a - 1) w) a ω = 0 → (ω ^ 2).im = 0 := by
  obtain ⟨w, hc, hpos⟩ := exists_long_chain ha
  exact ⟨w, hc, hpos, ⟨hc, chain_linearIndependent ha hc hpos⟩,
    fun v hv => chain_span_ae ha hc hpos hv, fun ω hω => chain_top_zeros ha hc hpos hω⟩

/-! ## Consequence for the RH chain: simplicity is no longer a separate input -/

/-- A nonzero `w` with a full-length Green chain at support `2a` (`exists_long_chain`). -/
def chainBase (a : ℝ) : ℝ → ℝ :=
  if ha : 0 < a then (exists_long_chain ha).choose else 0

/-- **The top-of-chain ground state**: `G^{m−1}w`, normalised. -/
def topGS (a : ℝ) : ℝ → ℝ :=
  fun x => (Real.sqrt (normSq (Gi a (gdim a - 1) (chainBase a))))⁻¹ * Gi a (gdim a - 1) (chainBase a) x

theorem chainBase_spec {a : ℝ} (ha : 0 < a) :
    IsChain a (gdim a - 1) (chainBase a) ∧ 0 < normSq (chainBase a) := by
  unfold chainBase; simp only [ha, ↓reduceDIte]; exact (exists_long_chain ha).choose_spec

/-- The top of a full chain is not a.e. zero (the chain is independent). -/
theorem top_normSq_pos {a : ℝ} (ha : 0 < a) : 0 < normSq (Gi a (gdim a - 1) (chainBase a)) := by
  obtain ⟨hc, hpos⟩ := chainBase_spec ha
  rcases (normSq_nonneg (Gi a (gdim a - 1) (chainBase a))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hli := chain_linearIndependent ha hc hpos
    set top : Fin (gdim a - 1 + 1) := Fin.last _
    have h0 : (iotaGS a).rangeRestrict (chainVec hc top) = 0 := by
      apply Subtype.ext
      show iotaGS a (chainVec hc top) = 0
      have := norm_iotaGS_sq (chainVec hc top)
      have e : (chainVec hc top).1 = Gi a (gdim a - 1) (chainBase a) := by
        simp [chainVec, top]
      rw [e, ← h] at this
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg (iotaGS a (chainVec hc top))])
    exact hli.ne_zero top h0

theorem topGS_isGroundState {a : ℝ} (ha : 0 < a) : IsGroundState a (topGS a) := by
  obtain ⟨hc, _⟩ := chainBase_spec ha
  set h := Gi a (gdim a - 1) (chainBase a)
  have hV : h ∈ groundSpace a := hc.1 _ le_rfl
  have hN := top_normSq_pos ha
  refine (isGroundState_iff ha).2 ⟨groundSpace_fun hV _, ?_⟩
  show normSq (fun x => (Real.sqrt (normSq h))⁻¹ * h x) = 1
  rw [normSq_smul, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']

/-- **Every zero of the top-of-chain ground state's transform lies on `ℝ ∪ iℝ`**, at every support,
with no simplicity assumption. -/
theorem topGS_cross {a : ℝ} (ha : 0 < a) (z : ℂ) (hz : ghatC (topGS a) a z = 0) :
    z.re = 0 ∨ z.im = 0 := by
  obtain ⟨hc, hpos⟩ := chainBase_spec ha
  have hN := top_normSq_pos ha
  have hs : (Real.sqrt (normSq (Gi a (gdim a - 1) (chainBase a))))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.2 hN).ne'
  unfold topGS at hz
  rw [ghatC_smul] at hz
  have h0 := (mul_eq_zero.1 hz).resolve_left (by exact_mod_cast hs)
  have him := chain_top_zeros ha hc hpos h0
  have : 2 * z.re * z.im = 0 := by rw [← him]; simp [pow_two]; ring
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; exact h

/-- **The RH chain with simplicity removed.** Convergence (a) for the top-of-chain ground states
alone gives Mathlib's `RiemannHypothesis`. -/
theorem rh_of_hypConv_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConv a fun n => topGS (a n)) : RiemannHypothesis :=
  rh_of_prime_side_cross (fun n => topGS_isGroundState (ha n))
    (Eventually.of_forall fun n z hz => topGS_cross (ha n) z hz) hconv zetaNoZeroInUnitInterval

/-- The new hypothesis is implied by the old pair: if the ground states `g n` are eventually simple
and satisfy (a), then so do the top-of-chain ground states. -/
theorem hypConv_top_of_simple {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hsimple : ∀ᶠ n in atTop, SimpleGround (a n) (g n)) (hconv : HypConv a g) :
    HypConv a fun n => topGS (a n) := by
  have heq : ∀ᶠ n in atTop, ∀ z : ℂ,
      ghatC (topGS (a n)) (a n) z / ghatC (topGS (a n)) (a n) 0
        = ghatC (g n) (a n) z / ghatC (g n) (a n) 0 := by
    filter_upwards [hsimple] with n hs z
    obtain ⟨c, hcg⟩ := hs.2 _ ((isGroundState_iff (ha n)).1 (topGS_isGroundState (ha n))).1
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := normSq_congr_ae hcg
      rw [(topGS_isGroundState (ha n)).2.1] at this
      simp [normSq] at this
    rw [ghatC_congr_ae hcg, ghatC_congr_ae hcg, ghatC_smul, ghatC_smul,
      mul_div_mul_left _ _ (by exact_mod_cast hc0)]
  intro u hu x
  obtain ⟨t, ht, hev⟩ := hconv u hu x
  refine ⟨t, ht, ?_⟩
  filter_upwards [hev, heq] with n hn he y hy
  rw [he y]; exact hn y hy

end Pilot1ca

#print axioms Pilot1ca.finiteDimensional_groundL2
#print axioms Pilot1ca.exists_long_chain
#print axioms Pilot1ca.chain_linearIndependent
#print axioms Pilot1ca.chain_span_ae
#print axioms Pilot1ca.chain_span_hat
#print axioms Pilot1ca.offcross_root
#print axioms Pilot1ca.chain_top_zeros
#print axioms Pilot1ca.theoremD
#print axioms Pilot1ca.topGS_cross
#print axioms Pilot1ca.rh_of_hypConv_top
#print axioms Pilot1ca.hypConv_top_of_simple
