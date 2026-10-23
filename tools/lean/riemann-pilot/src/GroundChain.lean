import Mathlib
import DegenerateFlat

/-! # Theorem D for any ground-state family (round 274)

Round 48's Theorem D (`StructureD.lean`) uses five facts about the ground space `V_a` of the form:
it is the ground-state space of a `ProbeForm`; it is closed under the two Green steps
(`partner`, `poleFree`) and under the swap of an off-cross zero (`green`); its image in `L²` is
finite-dimensional (`fd`); and it is nonzero (`nonzero`). `GroundData` bundles them, and everything
from the Green chains to Theorem D is proved once here. `StructureD` (Weil's form for `ζ`) and
`DHGround` (the Davenport–Heilbronn form) are the two instances.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-- A family of probe forms mapped into `L²`: the ground space at support `a`. -/
def iotaOf {Q : ℝ → (ℝ → ℝ) → ℝ} (form : ∀ a, ProbeForm a (Q a)) (a : ℝ) :
    (form a).space →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun x := x.2.1.memL2.toLp x.1
  map_add' x y := MemLp.toLp_add x.2.1.memL2 y.2.1.memL2
  map_smul' c x := MemLp.toLp_const_smul c x.2.1.memL2

/-- **A ground-state family**: the ground spaces of a family of probe forms, closed under the Green
steps and the swap of off-cross zeros, finite-dimensional in `L²` and nonzero. -/
structure GroundData where
  Q : ℝ → (ℝ → ℝ) → ℝ
  form : ∀ a, ProbeForm a (Q a)
  partner : ∀ {a : ℝ} {w k : ℝ → ℝ}, 0 ≤ a → w ∈ (form a).space → poleR w a = 0 →
    k ∈ (form a).space → poleR k a ≠ 0 → Gpole w a ∈ (form a).space
  poleFree : ∀ {a : ℝ} {w : ℝ → ℝ}, 0 ≤ a → w ∈ (form a).space → poleR w a = 0 →
    poleR (Gpole w a) a = 0 → Gpole w a ∈ (form a).space
  green : ∀ {a : ℝ} {g : ℝ → ℝ} {w : ℂ}, 0 < a → g ∈ (form a).space → ghatC g a w = 0 →
    (w ^ 2).im ≠ 0 → (fun x => (hSw g a w x).re) ∈ (form a).space ∧
      (fun x => (hSw g a w x).im) ∈ (form a).space
  fd : ∀ {a : ℝ}, 0 < a → FiniteDimensional ℝ (LinearMap.range (iotaOf form a))
  nonzero : ∀ {a : ℝ}, 0 < a → ∃ g ∈ (form a).space, normSq g = 1

/-- The ground space mapped into `L²`. -/
abbrev GroundData.iota (D : GroundData) (a : ℝ) : (D.form a).space →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  iotaOf D.form a

theorem GroundData.norm_iota_sq (D : GroundData) {a : ℝ} (x : (D.form a).space) :
    ‖D.iota a x‖ ^ 2 = normSq x.1 := by
  show ‖x.2.1.memL2.toLp x.1‖ ^ 2 = _
  rw [L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [x.2.1.memL2.coeFn_toLp] with t ht
  rw [ht]

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
def GroundData.IsChain (D : GroundData) (a : ℝ) (j : ℕ) (f : ℝ → ℝ) : Prop :=
  (∀ i ≤ j, Gi a i f ∈ (D.form a).space) ∧ ∀ i < j, poleR (Gi a i f) a = 0

theorem GroundData.Gi_add (D : GroundData) {a : ℝ} {j : ℕ} {f g : ℝ → ℝ} (hf : D.IsChain a j f) (hg : D.IsChain a j g) :
    ∀ i ≤ j + 1, Gi a i (f + g) = Gi a i f + Gi a i g
  | 0, _ => rfl
  | i + 1, hi => by
    rw [Gi_succ, Gi_succ, Gi_succ, D.Gi_add hf hg i (by omega),
      Gpole_add' (hf.1 i (by omega)).1.memL2 (hg.1 i (by omega)).1.memL2]

/-- The chains of length `j` form a subspace. -/
def GroundData.chainSpace (D : GroundData) (a : ℝ) (j : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | D.IsChain a j f}
  zero_mem' := by
    refine ⟨fun i _ => ?_, fun i _ => ?_⟩
    · rw [Gi_zero_fun]; exact ((D.form a).space).zero_mem
    · rw [Gi_zero_fun]; exact poleR_zero_fun a
  add_mem' := by
    intro f g hf hg
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [D.Gi_add hf hg i (by omega)]; exact ((D.form a).space).add_mem (hf.1 i hi) (hg.1 i hi)
    · rw [D.Gi_add hf hg i (by omega)]
      rw [show Gi a i f + Gi a i g = fun t => Gi a i f t + Gi a i g t from rfl,
        poleR_add (hf.1 i hi.le).1.memL2 (hg.1 i hi.le).1.memL2, hf.2 i hi, hg.2 i hi, add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [Gi_smul]; exact ((D.form a).space).smul_mem c (hf.1 i hi)
    · rw [Gi_smul, show c • Gi a i f = fun t => c * Gi a i f t from rfl, poleR_smul, hf.2 i hi,
        mul_zero]

theorem GroundData.chainSpace_zero (D : GroundData) (a : ℝ) {f : ℝ → ℝ} : f ∈ D.chainSpace a 0 ↔ f ∈ (D.form a).space := by
  constructor
  · intro h; exact h.1 0 le_rfl
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    rw [Nat.le_zero.1 hi]; exact h

/-- **One step of the filtration.** A single linear condition on `D.chainSpace j` puts `f` in
`D.chainSpace (j + 1)`: `(G^j f)^(i/2) = 0` if some ground-space element has a pole, and
`(G^{j+1} f)^(i/2) = 0` if none does. -/
theorem GroundData.chain_step (D : GroundData) {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    ∃ φ : (ℝ → ℝ) → ℝ,
      (∀ f ∈ D.chainSpace a j, ∀ g ∈ D.chainSpace a j, ∀ c : ℝ, φ (f + c • g) = φ f + c * φ g) ∧
      ∀ f ∈ D.chainSpace a j, φ f = 0 → f ∈ D.chainSpace a (j + 1) := by
  have lin : ∀ n ≤ j + 1, ∀ f ∈ D.chainSpace a j, ∀ g ∈ D.chainSpace a j, ∀ c : ℝ,
      Gi a n (f + c • g) = fun t => Gi a n f t + c * Gi a n g t := by
    intro n hn f hf g hg c
    have hcg : c • g ∈ D.chainSpace a j := (D.chainSpace a j).smul_mem c hg
    rw [D.Gi_add hf hcg n hn, Gi_smul]; rfl
  by_cases hk : ∃ k ∈ (D.form a).space, poleR k a ≠ 0
  · obtain ⟨k, hkV, hkp⟩ := hk
    refine ⟨fun f => poleR (Gi a j f) a, fun f hf g hg c => ?_, fun f hf h0 => ?_⟩
    · simp only
      rw [lin j (by omega) f hf g hg c, poleR_add (hf.1 j le_rfl).1.memL2
        ((hg.1 j le_rfl).1.memL2.const_mul c), poleR_smul]
    · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hf.1 i (by omega)
        · rw [show i = j + 1 by omega, Gi_succ]
          exact D.partner ha (hf.1 j le_rfl) h0 hkV hkp
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
        exact D.poleFree ha (hf.1 j le_rfl) (hk _ (hf.1 j le_rfl)) h0'

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
def GroundData.gdim (D : GroundData) (a : ℝ) : ℕ := Module.finrank ℝ (LinearMap.range (D.iota a))

/-- The chain subspaces, inside the ground space. -/
def GroundData.chainSub (D : GroundData) (a : ℝ) (j : ℕ) : Submodule ℝ ((D.form a).space) :=
  (D.chainSpace a j).comap ((D.form a).space).subtype

theorem GroundData.finrank_chain (D : GroundData) {a : ℝ} (ha : 0 < a) (j : ℕ) :
    D.gdim a ≤ Module.finrank ℝ ((D.chainSub a j).map (D.iota a).rangeRestrict) + j := by
  have := D.fd ha
  induction j with
  | zero =>
    have htop : D.chainSub a 0 = ⊤ := by
      ext x; simp only [Submodule.mem_top, iff_true]
      exact (D.chainSpace_zero a).2 x.2
    rw [htop, Submodule.map_top, LinearMap.range_rangeRestrict, finrank_top, add_zero]; rfl
  | succ j ih =>
    obtain ⟨φ, hlin, hker⟩ := D.chain_step ha.le j
    have := finrank_map_le_succ (D.iota a).rangeRestrict (A := D.chainSub a j)
      (B := D.chainSub a (j + 1)) (fun x => φ x.1)
      (fun x hx y hy c => hlin x.1 hx y.1 hy c) (fun x hx h0 => hker x.1 hx h0)
    omega

theorem GroundData.gdim_pos (D : GroundData) {a : ℝ} (ha : 0 < a) : 0 < D.gdim a := by
  have := D.fd ha
  obtain ⟨g, hgm, hgn⟩ := D.nonzero ha
  have hgV : g ∈ (D.form a).space ∧ normSq g = 1 := ⟨hgm, hgn⟩
  apply Module.finrank_pos_iff_exists_ne_zero.2
  refine ⟨⟨D.iota a ⟨g, hgV.1⟩, ⟨_, rfl⟩⟩, fun h0 => ?_⟩
  have h1 : D.iota a ⟨g, hgV.1⟩ = 0 := congrArg Subtype.val h0
  have := D.norm_iota_sq (a := a) ⟨g, hgV.1⟩
  rw [h1, norm_zero] at this
  simp only at this
  rw [hgV.2] at this; norm_num at this

/-- **A Green chain of full length.** With `m` the dimension of the ground space, some nonzero `w`
has `w, Gw, …, G^{m−1}w` in the ground space, all but the last pole-free. -/
theorem GroundData.exists_long_chain (D : GroundData) {a : ℝ} (ha : 0 < a) :
    ∃ w, D.IsChain a (D.gdim a - 1) w ∧ 0 < normSq w := by
  have := D.fd ha
  have h1 := D.finrank_chain ha (D.gdim a - 1)
  have h2 := D.gdim_pos ha
  have hpos : 0 < Module.finrank ℝ ((D.chainSub a (D.gdim a - 1)).map (D.iota a).rangeRestrict) := by
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := (D.chainSub a (D.gdim a - 1)).map (D.iota a).rangeRestrict)
    (fun h => by rw [h, finrank_bot] at hpos; exact lt_irrefl _ hpos)
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x.1, hx, ?_⟩
  rcases (normSq_nonneg x.1).lt_or_eq with h | h
  · exact h
  · exfalso; apply hy0
    have := D.norm_iota_sq x
    rw [← h] at this
    have h0 : D.iota a x = 0 := by
      have : ‖D.iota a x‖ = 0 := by nlinarith [norm_nonneg (D.iota a x)]
      exact norm_eq_zero.1 this
    exact Subtype.ext h0

/-! ## Fourier transforms along a chain -/

/-- `Ĝ` multiplies by `q(t) = −1/(t² + ¼)` on the real line. -/
def qr (t : ℝ) : ℝ := -1 / (t ^ 2 + 1 / 4)

theorem den_ne (t : ℝ) : ((t : ℂ)) ^ 2 - (Complex.I / 2) ^ 2 = (((t ^ 2 + 1 / 4 : ℝ)) : ℂ) := by
  rw [div_pow, Complex.I_sq]; push_cast; ring

theorem GroundData.Gi_hat (D : GroundData) {a : ℝ} (ha : 0 ≤ a) {j : ℕ} {w : ℝ → ℝ} (hc : D.IsChain a j w) :
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
      h, den_ne, D.Gi_hat ha hc i (by omega) t, pow_succ]
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
def GroundData.ghatL (D : GroundData) (a t : ℝ) : (D.form a).space →ₗ[ℝ] ℂ where
  toFun x := ghatC x.1 a t
  map_add' x y := ghatC_add x.2.1.memL2 y.2.1.memL2 a t
  map_smul' c x := by
    show ghatC (fun u => c * x.1 u) a t = _
    rw [ghatC_smul]; simp [Complex.real_smul]

theorem GroundData.iota_zero_ae (D : GroundData) {a : ℝ} {x : (D.form a).space} (h : D.iota a x = 0) : x.1 =ᵐ[volume] 0 :=
  ae_zero_of_normSq x.2.1.memL2 (by rw [← D.norm_iota_sq, h, norm_zero]; ring)

theorem GroundData.ghatL_of_iota (D : GroundData) {a : ℝ} (t : ℝ) {x : (D.form a).space} (h : D.iota a x = 0) :
    D.ghatL a t x = 0 := by
  show ghatC x.1 a t = 0
  rw [ghatC_congr_ae (D.iota_zero_ae h)]
  simp [ghatC]

/-- The chain as ground-space vectors. -/
def GroundData.chainVec (D : GroundData) {a : ℝ} {j : ℕ} {w : ℝ → ℝ} (hc : D.IsChain a j w) (i : Fin (j + 1)) : (D.form a).space :=
  ⟨Gi a i w, hc.1 i (Nat.lt_succ_iff.1 i.2)⟩

theorem GroundData.ghatL_comb (D : GroundData) {a : ℝ} (ha : 0 ≤ a) {j : ℕ} {w : ℝ → ℝ} (hc : D.IsChain a j w)
    (c : Fin (j + 1) → ℝ) (t : ℝ) :
    D.ghatL a t (∑ i, c i • D.chainVec hc i)
      = (∑ i : Fin (j + 1), (c i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul]
  show (c i : ℂ) * ghatC (Gi a i w) a t = _
  rw [D.Gi_hat ha hc i (Nat.lt_succ_iff.1 i.2) t]; ring

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
theorem GroundData.chain_linearIndependent (D : GroundData) {a : ℝ} (ha : 0 < a) {j : ℕ} {w : ℝ → ℝ} (hc : D.IsChain a j w)
    (hpos : 0 < normSq w) :
    LinearIndependent ℝ (fun i => (D.iota a).rangeRestrict (D.chainVec hc i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  have hS : D.iota a (∑ i, c i • D.chainVec hc i) = 0 := by
    have h2 : (D.iota a).rangeRestrict (∑ i, c i • D.chainVec hc i) = 0 := by
      simpa [map_sum, map_smul] using hsum
    exact congrArg Subtype.val h2
  have hw : Probe a w := (hc.1 0 (Nat.zero_le _)).1
  obtain ⟨α, ε, hα, hε, hne⟩ := exists_interval_ghat ha hw hpos
  have hP : polyOf (fun i => (c i : ℂ)) = 0 := poly_eq_zero_of_interval _ hα hε fun t ht => by
    have h1 := D.ghatL_comb ha.le hc c t
    rw [D.ghatL_of_iota t hS] at h1
    rw [polyOf_eval]
    exact (mul_eq_zero.1 h1.symm).resolve_right (hne t ht)
  have := polyOf_coeff (fun i => (c i : ℂ)) i
  rw [hP, Polynomial.coeff_zero] at this
  exact_mod_cast this.symm

/-- **The Green chain spans the ground space** (in `L²`), once it has full length. -/
theorem GroundData.chain_span (D : GroundData) {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : D.IsChain a (D.gdim a - 1) w)
    (hpos : 0 < normSq w) (v : (D.form a).space) :
    ∃ c : Fin (D.gdim a - 1 + 1) → ℝ, D.iota a (∑ i, c i • D.chainVec hc i - v) = 0 := by
  have := D.fd ha
  have hcard : Fintype.card (Fin (D.gdim a - 1 + 1)) = Module.finrank ℝ (LinearMap.range (D.iota a)) := by
    rw [Fintype.card_fin]; have := D.gdim_pos ha; unfold GroundData.gdim at this ⊢; omega
  have htop := (D.chain_linearIndependent ha hc hpos).span_eq_top_of_card_eq_finrank' hcard
  have hv : (D.iota a).rangeRestrict v ∈ Submodule.span ℝ
      (Set.range fun i => (D.iota a).rangeRestrict (D.chainVec hc i)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hcv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  refine ⟨c, ?_⟩
  have h2 : (D.iota a).rangeRestrict (∑ i, c i • D.chainVec hc i - v) = 0 := by
    rw [map_sub, map_sum]; simp only [map_smul]; rw [hcv, sub_self]
  exact congrArg Subtype.val h2

/-- **Theorem D, spanning (pointwise a.e. form).** Every ground-space element is a.e. a combination
of the chain `w, Gw, …, G^{m−1}w`. -/
theorem GroundData.chain_span_ae (D : GroundData) {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : D.IsChain a (D.gdim a - 1) w)
    (hpos : 0 < normSq w) {v : ℝ → ℝ} (hv : v ∈ (D.form a).space) :
    ∃ c : Fin (D.gdim a - 1 + 1) → ℝ, v =ᵐ[volume] fun x => ∑ i, c i * Gi a i w x := by
  obtain ⟨c, hc0⟩ := D.chain_span ha hc hpos ⟨v, hv⟩
  refine ⟨c, ?_⟩
  filter_upwards [D.iota_zero_ae hc0] with x hx
  have : (∑ i, c i • D.chainVec hc i : (D.form a).space).1 x - v x = 0 := hx
  rw [Submodule.coe_sum, Finset.sum_apply] at this
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GroundData.chainVec] at this
  linarith

/-- **Theorem D, spanning (Fourier form).** Every ground-space element has `v̂ = P(q)·ŵ` on the real
line, `P` a polynomial of degree `< m` in `q = −1/(t² + ¼)`. -/
theorem GroundData.chain_span_hat (D : GroundData) {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : D.IsChain a (D.gdim a - 1) w)
    (hpos : 0 < normSq w) {v : ℝ → ℝ} (hv : v ∈ (D.form a).space) :
    ∃ c : Fin (D.gdim a - 1 + 1) → ℝ, ∀ t : ℝ,
      ghatC v a t = (∑ i : Fin (D.gdim a - 1 + 1), (c i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t := by
  obtain ⟨c, hc0⟩ := D.chain_span ha hc hpos ⟨v, hv⟩
  refine ⟨c, fun t => ?_⟩
  have h1 := D.ghatL_of_iota t hc0
  rw [map_sub, D.ghatL_comb ha.le hc c t, sub_eq_zero] at h1
  exact h1.symm

/-! ## Zeros on the cross -/

/-- **Each off-cross zero of `v̂` is a root of `P_v`.** -/
theorem GroundData.offcross_root (D : GroundData) {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : D.IsChain a (D.gdim a - 1) w)
    (hwpos : 0 < normSq w) {v : ℝ → ℝ} (hv : v ∈ (D.form a).space)
    {ev : Fin (D.gdim a - 1 + 1) → ℝ}
    (hev : ∀ t : ℝ, ghatC v a t
      = (∑ i : Fin (D.gdim a - 1 + 1), (ev i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t)
    {ω : ℂ} (hω : ghatC v a ω = 0) (hσ : (ω ^ 2).im ≠ 0) :
    (polyOf fun i : Fin (D.gdim a - 1 + 1) => (ev i : ℂ)).IsRoot (-1 / (1 / 4 + ω ^ 2)) := by
  have hω0 : ω ≠ 0 := by rintro rfl; apply hσ; simp
  obtain ⟨hu, hv'⟩ := D.green ha hv hω hσ
  obtain ⟨c, hcu⟩ := D.chain_span_hat ha hc hwpos hu
  obtain ⟨d, hdv⟩ := D.chain_span_hat ha hc hwpos hv'
  have hw : Probe a w := (hc.1 0 (Nat.zero_le _)).1
  obtain ⟨α, ε, hα, hε, hne⟩ := exists_interval_ghat ha hw hwpos
  have hcont := hSw_continuous hv.1.memL2 a ω
  set P := polyOf (fun i : Fin (D.gdim a - 1 + 1) => (c i : ℂ) + Complex.I * d i)
  set Pv := polyOf (fun i : Fin (D.gdim a - 1 + 1) => (ev i : ℂ))
  set β : ℂ := 1 / 4 + ω ^ 2
  have hR : P * (1 + Polynomial.C β * Polynomial.X) - Polynomial.X * Pv = 0 := by
    refine poly_eq_zero_of_interval _ hα hε fun t ht => ?_
    obtain ⟨Q, hQe⟩ : ∃ Q : ℂ, Q = ((qr t : ℝ) : ℂ) := ⟨_, rfl⟩
    rw [← hQe]
    set Dt : ℂ := (t : ℂ) ^ 2 + 1 / 4
    have hD : Dt ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + 1 / 4 := by positivity
      have : ((t ^ 2 + 1 / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      simpa [Dt] using this
    have hQ : Q = -1 / Dt := by rw [hQe]; simp only [Dt, qr]; push_cast; ring
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
    have hP : P.eval Q = (∑ i : Fin (D.gdim a - 1 + 1), (c i : ℂ) * Q ^ (i : ℕ))
        + Complex.I * ∑ i : Fin (D.gdim a - 1 + 1), (d i : ℂ) * Q ^ (i : ℕ) := by
      rw [polyOf_eval, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    have hPv : Pv.eval Q = ∑ i : Fin (D.gdim a - 1 + 1), (ev i : ℂ) * Q ^ (i : ℕ) := polyOf_eval _ _
    have e : P.eval Q * ((t : ℂ) ^ 2 - ω ^ 2) = -Pv.eval Q := by
      have h2 := congrArg (· * ((t : ℂ) ^ 2 - ω ^ 2)) hhat
      rw [neg_mul, div_mul_cancel₀ _ hden] at h2
      have h3 : (P.eval Q * ((t : ℂ) ^ 2 - ω ^ 2) + Pv.eval Q) * ghatC w a t = 0 := by
        rw [hP, hPv]; linear_combination h2
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 h3).resolve_right hwt)
    have h1 : 1 + β * Q = ((t : ℂ) ^ 2 - ω ^ 2) * (-Q) := by
      have hDi : ((t : ℂ) ^ 2 + 1 / 4) * ((t : ℂ) ^ 2 + 1 / 4)⁻¹ = 1 := mul_inv_cancel₀ hD
      rw [hQ, div_eq_mul_inv]; simp only [β, Dt]
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
`−1/(¼ + ω²) ≠ 0` (`D.offcross_root`). -/
theorem GroundData.chain_top_zeros (D : GroundData) {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hc : D.IsChain a (D.gdim a - 1) w)
    (hpos : 0 < normSq w) {ω : ℂ} (hω : ghatC (Gi a (D.gdim a - 1) w) a ω = 0) :
    (ω ^ 2).im = 0 := by
  by_contra hσ
  set n := D.gdim a - 1
  set ev : Fin (n + 1) → ℝ := fun i => if (i : ℕ) = n then 1 else 0
  have hev : ∀ t : ℝ, ghatC (Gi a n w) a t
      = (∑ i : Fin (n + 1), (ev i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t := by
    intro t
    rw [D.Gi_hat ha.le hc n le_rfl t, sum_indicator_pow]
  have hroot := D.offcross_root ha hc hpos (hc.1 n le_rfl) hev hω hσ
  rw [Polynomial.IsRoot, polyOf_eval, sum_indicator_pow] at hroot
  have hβ : (1 / 4 + ω ^ 2 : ℂ) ≠ 0 := by
    intro h; apply hσ
    have : (ω ^ 2).im = (1 / 4 + ω ^ 2 : ℂ).im := by simp
    rw [this, h, Complex.zero_im]
  exact pow_ne_zero n (div_ne_zero (neg_ne_zero.2 one_ne_zero) hβ) hroot

/-- **Round 48's Theorem D, formal.** With `m = dim V` (finite, `finiteDimensional_groundL2`), there
is a nonzero `w` whose Green chain `w, Gw, …, G^{m−1}w` lies in the ground space (all but the last
pole-free), is linearly independent, and spans it a.e. Every zero `ω` of `ĥ`, `h = G^{m−1}w`, has
`ω² ∈ ℝ`. Since `(G^i w)^ = q^i ŵ` (`D.Gi_hat`, `q = −1/(t² + ¼)`), the spanning statement is
`V_ℂ = ĥ · {polynomials of degree < m in z²}` on the real line. -/
theorem GroundData.theoremD (D : GroundData) {a : ℝ} (ha : 0 < a) :
    ∃ w, D.IsChain a (D.gdim a - 1) w ∧ 0 < normSq w ∧
      (∃ hc : D.IsChain a (D.gdim a - 1) w,
        LinearIndependent ℝ (fun i => (D.iota a).rangeRestrict (D.chainVec hc i))) ∧
      (∀ v ∈ (D.form a).space, ∃ c : Fin (D.gdim a - 1 + 1) → ℝ,
        v =ᵐ[volume] fun x => ∑ i, c i * Gi a i w x) ∧
      ∀ ω : ℂ, ghatC (Gi a (D.gdim a - 1) w) a ω = 0 → (ω ^ 2).im = 0 := by
  obtain ⟨w, hc, hpos⟩ := D.exists_long_chain ha
  exact ⟨w, hc, hpos, ⟨hc, D.chain_linearIndependent ha hc hpos⟩,
    fun v hv => D.chain_span_ae ha hc hpos hv, fun ω hω => D.chain_top_zeros ha hc hpos hω⟩
/-! ## The top-of-chain ground state -/

/-- A nonzero `w` with a full-length Green chain (`exists_long_chain`). -/
def GroundData.chainBase (D : GroundData) (a : ℝ) : ℝ → ℝ :=
  if ha : 0 < a then (D.exists_long_chain ha).choose else 0

/-- **The top-of-chain ground state**: `G^{m−1}w`, normalised. -/
def GroundData.topGS (D : GroundData) (a : ℝ) : ℝ → ℝ :=
  fun x => (Real.sqrt (normSq (Gi a (D.gdim a - 1) (D.chainBase a))))⁻¹
    * Gi a (D.gdim a - 1) (D.chainBase a) x

theorem GroundData.chainBase_spec (D : GroundData) {a : ℝ} (ha : 0 < a) :
    D.IsChain a (D.gdim a - 1) (D.chainBase a) ∧ 0 < normSq (D.chainBase a) := by
  unfold GroundData.chainBase; simp only [ha, ↓reduceDIte]; exact (D.exists_long_chain ha).choose_spec

/-- The top of a full chain is not a.e. zero (the chain is independent). -/
theorem GroundData.top_normSq_pos (D : GroundData) {a : ℝ} (ha : 0 < a) :
    0 < normSq (Gi a (D.gdim a - 1) (D.chainBase a)) := by
  obtain ⟨hc, hpos⟩ := D.chainBase_spec ha
  rcases (normSq_nonneg (Gi a (D.gdim a - 1) (D.chainBase a))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hli := D.chain_linearIndependent ha hc hpos
    set top : Fin (D.gdim a - 1 + 1) := Fin.last _
    have h0 : (D.iota a).rangeRestrict (D.chainVec hc top) = 0 := by
      apply Subtype.ext
      show D.iota a (D.chainVec hc top) = 0
      have := D.norm_iota_sq (D.chainVec hc top)
      have e : (D.chainVec hc top).1 = Gi a (D.gdim a - 1) (D.chainBase a) := rfl
      rw [e, ← h] at this
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg (D.iota a (D.chainVec hc top))])
    exact hli.ne_zero top h0

/-- The top of the chain is a unit vector of the ground space. -/
theorem GroundData.topGS_mem (D : GroundData) {a : ℝ} (ha : 0 < a) :
    D.topGS a ∈ (D.form a).space ∧ normSq (D.topGS a) = 1 := by
  obtain ⟨hc, _⟩ := D.chainBase_spec ha
  set h := Gi a (D.gdim a - 1) (D.chainBase a)
  have hV : h ∈ (D.form a).space := hc.1 _ le_rfl
  have hN := D.top_normSq_pos ha
  refine ⟨(D.form a).space.smul_mem _ hV, ?_⟩
  show normSq (fun x => (Real.sqrt (normSq h))⁻¹ * h x) = 1
  rw [normSq_smul, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']

/-- **Every zero of the top-of-chain ground state's transform lies on `ℝ ∪ iℝ`**, at every
support `a > 0`, with no simplicity assumption. -/
theorem GroundData.topGS_cross (D : GroundData) {a : ℝ} (ha : 0 < a) (z : ℂ)
    (hz : ghatC (D.topGS a) a z = 0) : z.re = 0 ∨ z.im = 0 := by
  obtain ⟨hc, hpos⟩ := D.chainBase_spec ha
  have hN := D.top_normSq_pos ha
  have hs : (Real.sqrt (normSq (Gi a (D.gdim a - 1) (D.chainBase a))))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.2 hN).ne'
  unfold GroundData.topGS at hz
  rw [ghatC_smul] at hz
  have h0 := (mul_eq_zero.1 hz).resolve_left (by exact_mod_cast hs)
  have him := D.chain_top_zeros ha hc hpos h0
  have : 2 * z.re * z.im = 0 := by rw [← him]; simp [pow_two]; ring
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; exact h

end Pilot1ca
#print axioms Pilot1ca.GroundData.finrank_chain
#print axioms Pilot1ca.GroundData.exists_long_chain
#print axioms Pilot1ca.GroundData.chain_linearIndependent
#print axioms Pilot1ca.GroundData.chain_span_ae
#print axioms Pilot1ca.GroundData.chain_span_hat
#print axioms Pilot1ca.GroundData.offcross_root
#print axioms Pilot1ca.GroundData.chain_top_zeros
#print axioms Pilot1ca.GroundData.theoremD
#print axioms Pilot1ca.GroundData.topGS_mem
#print axioms Pilot1ca.GroundData.topGS_cross
