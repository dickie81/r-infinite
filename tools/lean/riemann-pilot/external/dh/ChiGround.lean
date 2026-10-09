import Mathlib
import DHGround
import DHJoins
import CrossCriteria

/-! # The ground-state stack for `L(s, χ)` (round 330)

DHGround builds the ground-state stack of the Davenport–Heilbronn form `QDHu`. Its proofs see `QDHu`
only through its shape: a u-space form `Q(g) = c‖g‖² + E_q(g) − 2Σ_n f(n)n^{−1/2} f_g(log n)`,
`f_g = autocorr g`, with no pole term. Here they are proved once for every such form with
`q ∈ {¼, ¾}` (`UData`), and instantiated at Weil's form `QCu χ` for `L(s, χ)`: `chiU χ` has
`c = cChi χ`, `q = qC χ` (`¼` for even `χ`, `¾` for odd, `qC_cases`) and `f = fχ χ`, for every Dirichlet
character `χ`. DHGround's form is the instance `c = constDH`, `q = ¾`, `f = fDH` (`dhU`).

**Stage 1 (existence).** `UData.exists_min`, `UData.exists_groundState`: DHGround's compactness
argument. At `q = ¾` it uses DHGround's transfer `archE_le_DH` (`E ≤ e^{2a}E_{3/4} + ‖g‖²T(a)`); at
`q = ¼`, `E_q = E` (`archEQ_quarter`) (`UData.archE_le`, `UData.arch_of_archQU`).

**Stage 2 (Euler–Lagrange).** `UData.bil`, `UData.Q_add_smul`, `UData.euler_lagrange_mem`.

**Stage 3 (swap closure, simple ground states).** `UData.split_mem`, `UData.zero_swap_false`,
`UData.zeros_real_or_imag'`, `UData.green_mem`.

**Stage 4 (the ground-state family).** `UData.G_mem_pole_free`, `UData.G_mem_partner`,
`UData.finiteDimensional_groundL2` and `UData.gd : GroundData`; GroundChain.lean then gives Theorem D
and the top-of-chain ground state with every zero of its transform on `ℝ ∪ iℝ` (`UData.topGS_cross`).

**The χ column.** `(chiU χ).Q = QCu χ` and `(chiU χ).lam = lamC χ` by definition (`chiU_Q`,
`chiU_lam`). `chiGD χ : GroundData`, `exists_groundStateC`, `theoremDC`, `topGSC_cross`.

**The chain to GRH(χ).** `HypConvC χ` is `HypConv` (PrimeSide.lean:37) with `Ξ_χ = XiC χ` as the
target. For `GoodChar χ`, `grhCross_of_cross` is the Hurwitz step of `rh_of_prime_side_cross`
(HurwitzCross.lean:45) for `L(s, χ)`: integrable `g_n` whose transforms eventually have every zero on
`ℝ ∪ iℝ`, with `HypConvC χ`, give GRH for `χ` off the real axis (`CrossCriteria.GRHCross`). So
`HypConvC χ` for the top-of-chain ground states gives `GRHCross χ` (`grhCross_of_hypConvC_top`), and
with no real zero in `(0, 1)`, GRH for `χ` (`grh_of_hypConvC_top`, the χ column of `rh_of_hypConv_top`,
StructureD.lean:192). The same for eventually simple ground states (`grh_of_eventually_simpleC`).
Instances: `χ₋₃`, `χ₋₄`, `χ₋₈`, `χ₋₇`.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## u-space forms -/

/-- **A u-space form with no pole term**: a constant `c`, an archimedean shift `q ∈ {¼, ¾}` and
prime-side coefficients `f`. -/
structure UData where
  c : ℝ
  q : ℝ
  f : ℕ → ℝ
  hq : q = 1 / 4 ∨ q = 3 / 4

namespace UData

variable (U : UData) {a : ℝ} {g h : ℝ → ℝ}

/-- `Q(g) = c‖g‖² + E_q(g) − 2Σ_n f(n)n^{−1/2} f_g(log n)`. -/
def Q (g : ℝ → ℝ) : ℝ :=
  U.c * normSq g + archEQ U.q g - 2 * ∑' n : ℕ, U.f n / Real.sqrt n * autocorr g (Real.log n)

theorem quarter_le : (1 / 4 : ℝ) ≤ U.q := by
  rcases U.hq with h | h
  · rw [h]
  · rw [h]; norm_num

/-- Only `n < ⌊e^{2a}⌋ + 1` enter the prime sum of a probe at support `a`. -/
theorem Q_eq_range (hsupp : ∀ u, a < |u| → g u = 0) :
    U.Q g = U.c * normSq g + archEQ U.q g
      - 2 * ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr g (Real.log n) := by
  unfold UData.Q; rw [tsum_autocorr_eq (fun n => U.f n / Real.sqrt n) hsupp]

theorem Q_zero : U.Q (fun _ => 0) = 0 := by
  simp [UData.Q, Pilot1ca.normSq, archEQ, archIntegrandQ, autocorr]

theorem Q_smul (g : ℝ → ℝ) (c : ℝ) : U.Q (fun t => c * g t) = c ^ 2 * U.Q g := by
  have hS : ∑' n : ℕ, U.f n / Real.sqrt n * autocorr (fun t => c * g t) (Real.log n)
      = c ^ 2 * ∑' n : ℕ, U.f n / Real.sqrt n * autocorr g (Real.log n) := by
    rw [← tsum_mul_left]; congr 1; funext n; rw [autocorr_smul]; ring
  unfold UData.Q
  rw [normSq_smul, archEQ_smul, hS]; ring

/-- The parallelogram law for `Q`. -/
theorem Q_add_sub (hg : Probe a g) (hh : Probe a h) :
    U.Q (fun t => g t + h t) + U.Q (fun t => g t - h t) = 2 * U.Q g + 2 * U.Q h := by
  obtain ⟨hp, hm⟩ := probe_add_sub hg hh
  have hN := normSq_add_sub hg.memL2 hh.memL2
  have hA := archEQ_add_sub U.quarter_le hg hh
  have hS : ∑ n ∈ Finset.range (primeCut a),
        U.f n / Real.sqrt n * autocorr (fun t => g t + h t) (Real.log n)
      + ∑ n ∈ Finset.range (primeCut a),
        U.f n / Real.sqrt n * autocorr (fun t => g t - h t) (Real.log n)
      = 2 * ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr g (Real.log n)
        + 2 * ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr h (Real.log n) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have := autocorr_add_sub hg.memL2 hh.memL2 (Real.log n)
    linear_combination (U.f n / Real.sqrt n) * this
  rw [U.Q_eq_range hp.supp, U.Q_eq_range hm.supp, U.Q_eq_range hg.supp, U.Q_eq_range hh.supp]
  linear_combination U.c * hN + hA - 2 * hS

theorem Q_congr_ae {g g' : ℝ → ℝ} (hgg : g =ᵐ[volume] g') : U.Q g = U.Q g' := by
  unfold UData.Q
  rw [normSq_congr_ae hgg, archEQ_congr_ae U.q hgg]
  simp_rw [autocorr_congr_ae hgg]

/-- `M(a) = |c| + 2Σ_{n ≤ e^{2a}} |f(n)|/√n`. -/
def M (a : ℝ) : ℝ := |U.c| + 2 * ∑ n ∈ Finset.range (primeCut a), |U.f n / Real.sqrt n|

theorem M_nonneg (a : ℝ) : 0 ≤ U.M a := by
  unfold UData.M
  have : 0 ≤ ∑ n ∈ Finset.range (primeCut a), |U.f n / Real.sqrt n| :=
    Finset.sum_nonneg fun n _ => abs_nonneg _
  positivity

theorem abs_prime_le (hp : Probe a g) :
    |∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr g (Real.log n)|
      ≤ (∑ n ∈ Finset.range (primeCut a), |U.f n / Real.sqrt n|) * normSq g := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_autocorr_le hp.memL2 _) (abs_nonneg _)

/-- **`Q(g) ≥ −M(a)‖g‖²`** on probes at support `a`. -/
theorem Q_ge (hp : Probe a g) : -(U.M a * normSq g) ≤ U.Q g := by
  rw [U.Q_eq_range hp.supp]
  have hN := normSq_nonneg g
  have hE := archEQ_nonneg U.q hp.memL2
  have hP := U.abs_prime_le hp
  have hc : -(|U.c| * normSq g) ≤ U.c * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hN
  unfold UData.M
  nlinarith [le_abs_self (∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n
    * autocorr g (Real.log n))]

/-- **`Q` is a `ProbeForm`** at every support. -/
theorem form (a : ℝ) : ProbeForm a U.Q where
  zero := U.Q_zero
  smul := U.Q_smul
  add_sub := U.Q_add_sub
  congr_ae := U.Q_congr_ae
  bdd := ⟨-U.M a, by
    rintro x ⟨h, hp, hn, rfl⟩
    have := U.Q_ge hp; rwa [hn, mul_one] at this⟩

/-- **The ground energy** `λ(a) = inf {Q(g) : g a probe at support a, ‖g‖ = 1}`. -/
def lam (a : ℝ) : ℝ := (U.form a).inf

theorem lam_le (hp : Probe a h) (hn : normSq h = 1) : U.lam a ≤ U.Q h :=
  (U.form a).inf_le hp hn

theorem lam_mul_le (hg : Probe a g) : U.lam a * normSq g ≤ U.Q g :=
  (U.form a).inf_mul_le hg

/-- **The ground-state space**: probes with `Q(g) = λ(a)‖g‖²`. -/
abbrev groundSpace (a : ℝ) : Submodule ℝ (ℝ → ℝ) := (U.form a).space

/-- **A ground state**: a normalised probe at the ground energy. -/
def IsGroundState (a : ℝ) (g : ℝ → ℝ) : Prop := Probe a g ∧ normSq g = 1 ∧ U.Q g = U.lam a

theorem isGroundState_iff : U.IsGroundState a g ↔ g ∈ U.groundSpace a ∧ normSq g = 1 := by
  constructor
  · rintro ⟨hp, hn, hq⟩
    refine ⟨⟨hp, ?_⟩, hn⟩
    show U.Q g = (U.form a).inf * normSq g
    rw [hn, mul_one]; exact hq
  · rintro ⟨⟨hp, hq⟩, hn⟩
    refine ⟨hp, hn, ?_⟩
    rw [hq, hn, mul_one]; rfl

/-- The ground states are exactly the normalised minimisers. -/
theorem isGroundState_iff_min (ha : 0 < a) :
    U.IsGroundState a g ↔
      Probe a g ∧ normSq g = 1 ∧ ∀ h, Probe a h → normSq h = 1 → U.Q g ≤ U.Q h := by
  rw [U.isGroundState_iff]; exact ((U.form a).isMin_iff ha).symm

/-! ### Stage 1: existence -/

/-- **`E(g) ≤ e^{2a}E_q(g) + ‖g‖²·T(a)`** on probes at support `a`: DHGround's `archE_le_DH` at
`q = ¾`; at `q = ¼`, `E_q = E`. -/
theorem archE_le (ha : 0 < a) (hp : Probe a g) :
    archE g ≤ Real.exp (2 * a) * archEQ U.q g + normSq g * tailDH a := by
  rcases U.hq with h | h
  · rw [h, archEQ_quarter]
    have h1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
    have h2 : 0 ≤ archE g := by rw [← archEQ_quarter]; exact archEQ_nonneg (1 / 4) hp.memL2
    have h3 : 0 ≤ normSq g * tailDH a := mul_nonneg (normSq_nonneg g) (tailDH_nonneg a)
    nlinarith
  · rw [h]; exact archE_le_DH ha hp

/-- **The archimedean condition of a probe from the `q`-integrand** (DHGround's `arch_of_archQ` at
`q = ¾`; at `q = ¼` the integrands are equal). -/
theorem arch_of_archQU (ha : 0 < a) (hsupp : ∀ u, a < |u| → g u = 0) (hg : MemLp g 2 volume)
    (hQ : IntegrableOn (archIntegrandQ U.q g) (Ioi 0)) : IntegrableOn (archIntegrand g) (Ioi 0) := by
  rcases U.hq with h | h
  · rw [h, archIntegrandQ_quarter] at hQ; exact hQ
  · rw [h] at hQ; exact arch_of_archQ ha hsupp hg hQ

/-- The non-archimedean part of `Q` at support `a`: the constant and the finite prime sum. -/
def nonArch (a : ℝ) (g : ℝ → ℝ) : ℝ :=
  U.c * normSq g
    - 2 * ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr g (Real.log n)

theorem Q_eq_nonArch (hsupp : ∀ u, a < |u| → g u = 0) : U.Q g = U.nonArch a g + archEQ U.q g := by
  rw [U.Q_eq_range hsupp]; unfold UData.nonArch; ring

theorem nonArch_ge (hp : Probe a g) (hn : normSq g = 1) : -U.M a ≤ U.nonArch a g := by
  have hP := U.abs_prime_le hp
  rw [hn, mul_one] at hP
  have h1 := neg_abs_le U.c
  have h2 := le_abs_self
    (∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr g (Real.log n))
  unfold UData.nonArch UData.M; rw [hn, mul_one]; linarith

/-- **A minimiser of `Q` exists at every support `a > 0`** (DHGround's `exists_min_QDHu`, with `E_q` in
place of `E_{3/4}`). -/
theorem exists_min (ha : 0 < a) : ∃ g, Probe a g ∧ normSq g = 1 ∧
    ∀ h, Probe a h → normSq h = 1 → U.Q g ≤ U.Q h := by
  set Sv : Set ℝ := {x | ∃ h, Probe a h ∧ normSq h = 1 ∧ U.Q h = x} with hSv
  have hne : Sv.Nonempty := ⟨_, box a, box_probe a, normSq_box ha, rfl⟩
  have hbdd : BddBelow Sv := (U.form a).bdd
  obtain ⟨qs, hqa, hqs, hqS⟩ := exists_seq_tendsto_sInf hne hbdd
  choose h hp hn hQ using hqS
  set lam := sInf Sv with hlam
  -- the non-archimedean part is bounded below, so `E_q` is bounded above
  have hC3 : ∀ j, archEQ U.q (h j) ≤ qs 0 + U.M a := by
    intro j
    have e := U.Q_eq_nonArch (hp j).supp
    have := U.nonArch_ge (hp j) (hn j)
    have hqj : qs j ≤ qs 0 := hqa (Nat.zero_le j)
    rw [hQ j] at e
    linarith
  -- and so is `E = E_{1/4}`, which the compactness theorem takes
  have hC : ∀ j, archE (h j) ≤ Real.exp (2 * a) * (qs 0 + U.M a) + tailDH a := by
    intro j
    have h1 := U.archE_le ha (hp j)
    rw [hn j, one_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hC3 j) (Real.exp_pos (2 * a)).le
    linarith
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq ha hp (B := 1) (fun j => (hn j).le) hC
  set G' := symCut a G with hG'def
  have hG' : MemLp G' 2 volume := memLp_symCut a hG
  have hlim' : Tendsto (fun j => normSq (fun t => h (φ j) t - G' t)) atTop (𝓝 0) :=
    squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _)
      (fun j => normSq_sub_symCut_le (hp (φ j)) hG) hlim
  have hmem : ∀ j, MemLp (h (φ j)) 2 volume := fun j => (hp (φ j)).memL2
  -- continuity of the non-archimedean terms
  have hnorm : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 (normSq G')) := by
    simp_rw [normSq_eq_mul]
    exact tendsto_integral_mul hmem hmem hG' hG' hlim' hlim'
  have hnormG : normSq G' = 1 := by
    have h1 : Tendsto (fun j => normSq (h (φ j))) atTop (𝓝 1) := by
      simp only [hn]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hnorm h1
  have hauto : ∀ u, Tendsto (fun j => autocorr (h (φ j)) u) atTop (𝓝 (autocorr G' u)) := by
    intro u
    have hsh : ∀ j, normSq (fun t => h (φ j) (t + u) - G' (t + u))
        = normSq (fun t => h (φ j) t - G' t) :=
      fun j => normSq_shift (fun t => h (φ j) t - G' t) u
    unfold autocorr
    exact tendsto_integral_mul hmem (fun j => memLp_shift (hmem j) u) hG' (memLp_shift hG' u)
      hlim' (hlim'.congr fun j => (hsh j).symm)
  have hsuppG' : ∀ u, a < |u| → G' u = 0 := symCut_supp a G
  have hnonArch : Tendsto (fun j => U.nonArch a (h (φ j))) atTop (𝓝 (U.nonArch a G')) := by
    unfold UData.nonArch
    exact (hnorm.const_mul _).sub
      ((tendsto_finsetSum _ fun n _ => (hauto _).const_mul _).const_mul 2)
  -- the `q`-energies converge to `λ − nonArch(G')`
  have hqφ : Tendsto (fun j => qs (φ j)) atTop (𝓝 lam) := hqs.comp hφ.tendsto_atTop
  have hA : Tendsto (fun j => archEQ U.q (h (φ j))) atTop (𝓝 (lam - U.nonArch a G')) := by
    have e : ∀ j, archEQ U.q (h (φ j)) = qs (φ j) - U.nonArch a (h (φ j)) := by
      intro j; rw [← hQ (φ j), U.Q_eq_nonArch (hp (φ j)).supp]; ring
    simp_rw [e]
    exact hqφ.sub hnonArch
  -- Fatou on the `q`-integrand
  obtain ⟨hint, hle⟩ := fatou_real measurableSet_Ioi
    (f := fun j => archIntegrandQ U.q (h (φ j))) (F := archIntegrandQ U.q G')
    (fun j => archIntegrandQ_integrable (hp (φ j)) U.quarter_le)
    (fun j u hu => archIntegrandQ_nonneg U.q (hmem j) hu)
    (fun u _ => by
      unfold archIntegrandQ
      exact ((hauto 0).sub (hauto u)).mul_const _) hA
  have hPG : Probe a G' := ⟨symCut_even a G, hsuppG', hG', U.arch_of_archQU ha hsuppG' hG' hint⟩
  refine ⟨G', hPG, hnormG, fun h' hp' hn' => ?_⟩
  have hQG : U.Q G' ≤ lam := by
    rw [U.Q_eq_nonArch hsuppG']; unfold archEQ; linarith
  exact hQG.trans (csInf_le hbdd ⟨h', hp', hn', rfl⟩)

/-- **A ground state exists at every support `a > 0`.** -/
theorem exists_groundState (ha : 0 < a) : ∃ g, U.IsGroundState a g := by
  obtain ⟨g, hp, hn, hmin⟩ := U.exists_min ha
  exact ⟨g, (U.isGroundState_iff_min ha).2 ⟨hp, hn, hmin⟩⟩

/-! ### Stage 2: the bilinear form and the Euler–Lagrange equation -/

/-- **The bilinear form of `Q`**:
`B(φ, ψ) = c·x(0) + ∫_0^∞ (x(0) − x(u))K_q(u) du − 2Σ_{n < N(a)} f(n)n^{−1/2} x(log n)`, `x = xcorr φ ψ`. -/
def bil (a : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  U.c * xcorr φ ψ 0 + (∫ u in Ioi 0, archXQ U.q φ ψ u)
    - 2 * ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * xcorr φ ψ (Real.log n)

/-- `Q(φ + sψ) = Q(φ) + 2sB(φ, ψ) + s²Q(ψ)` on probes. -/
theorem Q_add_smul {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (s : ℝ) :
    U.Q (fun t => φ t + s * ψ t) = U.Q φ + 2 * s * U.bil a φ ψ + s ^ 2 * U.Q ψ := by
  have hA := archEQ_add_smul hφ hψ U.quarter_le s
  have hS : ∑ n ∈ Finset.range (primeCut a),
        U.f n / Real.sqrt n * autocorr (fun t => φ t + s * ψ t) (Real.log n)
      = ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr φ (Real.log n)
        + 2 * s * ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * xcorr φ ψ (Real.log n)
        + s ^ 2 * ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr ψ (Real.log n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [autocorr_add_smul hφ.memL2 hψ.memL2]; ring
  rw [U.Q_eq_range (probe_add_smul hφ hψ s).supp, U.Q_eq_range hφ.supp, U.Q_eq_range hψ.supp,
    normSq_add_smul hφ.memL2 hψ.memL2, hA, hS]
  unfold UData.bil; ring

/-- `Q(k) = B(k, k)`. -/
theorem Q_eq_bil {k : ℝ → ℝ} (hk : Probe a k) : U.Q k = U.bil a k k := by
  have e := U.Q_add_smul hk hk 1
  have e2 : (fun t => k t + 1 * k t) = fun t => (2 : ℝ) * k t := by funext t; ring
  rw [e2, U.Q_smul] at e
  linarith

/-- **Euler–Lagrange for any element of the ground space**: `B(w, ψ) = λ⟨w, ψ⟩` for every probe `ψ`. -/
theorem euler_lagrange_mem {w ψ : ℝ → ℝ} (hw : w ∈ U.groundSpace a) (hψ : Probe a ψ) :
    U.bil a w ψ = U.lam a * xcorr w ψ 0 := by
  have hq : U.Q w = U.lam a * normSq w := hw.2
  apply sub_eq_zero.1
  refine quad_zero (c := U.Q ψ - U.lam a * normSq ψ) fun s => ?_
  have h := U.lam_mul_le (probe_add_smul hw.1 hψ s)
  rw [U.Q_add_smul hw.1 hψ, normSq_add_smul hw.1.memL2 hψ.memL2, hq] at h
  nlinarith [h]

/-! ### Stage 3: the swap closure and simple ground states -/

/-- A ground state is **simple** when the ground-state space is spanned by it. -/
def SimpleGround (a : ℝ) (g : ℝ → ℝ) : Prop :=
  U.IsGroundState a g ∧ ∀ h ∈ U.groundSpace a, ∃ c : ℝ, h =ᵐ[volume] fun t => c * g t

/-- **Splitting a ground-space element**: probes `u, v` whose autocorrelations add up to those of `g`
in the ground space lie in it (no pole term). -/
theorem split_mem {g u v : ℝ → ℝ} (hg : g ∈ U.groundSpace a)
    (hu : Probe a u) (hv : Probe a v) (hac : ∀ x, autocorr u x + autocorr v x = autocorr g x) :
    u ∈ U.groundSpace a ∧ v ∈ U.groundSpace a := by
  have hp : Probe a g := hg.1
  have hN : normSq u + normSq v = normSq g := by
    rw [normSq_eq_autocorr, normSq_eq_autocorr, normSq_eq_autocorr]; exact hac 0
  have hA : archEQ U.q u + archEQ U.q v = archEQ U.q g := by
    unfold archEQ
    rw [← integral_add (archIntegrandQ_integrable hu U.quarter_le)
      (archIntegrandQ_integrable hv U.quarter_le)]
    congr 1; funext x
    unfold archIntegrandQ
    linear_combination (archKer U.q x) * (hac 0 - hac x)
  have hS : ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr u (Real.log n)
      + ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr v (Real.log n)
      = ∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr g (Real.log n) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    linear_combination (U.f n / Real.sqrt n) * hac (Real.log n)
  have hQ : U.Q u + U.Q v = U.Q g := by
    rw [U.Q_eq_range hu.supp, U.Q_eq_range hv.supp, U.Q_eq_range hp.supp]
    linear_combination U.c * hN + hA - 2 * hS
  have ru := U.lam_mul_le hu
  have rv := U.lam_mul_le hv
  have hgq : U.Q g = U.lam a * normSq g := hg.2
  have hsplit : U.lam a * normSq g = U.lam a * normSq u + U.lam a * normSq v := by
    rw [← hN]; ring
  exact ⟨⟨hu, show U.Q u = U.lam a * normSq u by linarith⟩,
    ⟨hv, show U.Q v = U.lam a * normSq v by linarith⟩⟩

/-- **The zero-swap lemma, core**: a simple ground state admits no realised swap of a zero with
non-real square. -/
theorem zero_swap_false (ha : 0 < a) {g : ℝ → ℝ} (hs : U.SimpleGround a g) {σ : ℂ}
    (hσ : σ.im ≠ 0) (hR : SwapRealization a g σ) : False := by
  obtain ⟨hgs, hsimp⟩ := hs
  obtain ⟨u, v, hu, hv, hB, hac⟩ := hR
  obtain ⟨⟨-, eu⟩, ⟨-, ev⟩⟩ := U.split_mem (U.isGroundState_iff.1 hgs).1 hu hv hac
  obtain ⟨α, hα⟩ := hsimp u ⟨hu, eu⟩
  obtain ⟨β, hβ⟩ := hsimp v ⟨hv, ev⟩
  set c : ℂ := (α : ℂ) + Complex.I * β
  set B : ℂ → ℂ := fun z => (z ^ 2 - (starRingEnd ℂ) σ) / (z ^ 2 - σ)
  have key : ∀ t : ℝ, ghatC g a t ≠ 0 → c = B t := by
    intro t ht
    have h := hB t (sq_ne_of_im hσ t)
    rw [ghatC_congr_ae hα, ghatC_smul, ghatC_congr_ae hβ, ghatC_smul] at h
    apply mul_left_cancel₀ ht
    rw [← h]; simp only [c]; ring
  obtain ⟨t₁, t₂, h₁, ht₂, hsq⟩ := exists_two_real_ghatC_ne ha hgs.1 hgs.2.1
  have c1 := key t₁ h₁
  have c2 := key t₂ ht₂
  have hd1 : ((t₁ : ℂ)) ^ 2 - σ ≠ 0 := sub_ne_zero.2 (sq_ne_of_im hσ t₁)
  have hd2 : ((t₂ : ℂ)) ^ 2 - σ ≠ 0 := sub_ne_zero.2 (sq_ne_of_im hσ t₂)
  have heq : B t₁ = B t₂ := c1.symm.trans c2
  simp only [B] at heq
  rw [div_eq_div_iff hd1 hd2] at heq
  have hprod : (((t₂ ^ 2 - t₁ ^ 2 : ℝ)) : ℂ) * (σ - (starRingEnd ℂ) σ) = 0 := by
    push_cast; linear_combination heq
  rcases mul_eq_zero.1 hprod with h | h
  · rw [Complex.ofReal_eq_zero] at h; linarith
  · rw [Complex.sub_conj] at h
    apply hσ
    have := congrArg Complex.im h
    simp at this
    exact this

/-- **Zeros of a simple ground state lie on `ℝ ∪ iℝ`**, given the swap realisation for every zero
off the cross. -/
theorem zeros_real_or_imag (ha : 0 < a) {g : ℝ → ℝ} (hs : U.SimpleGround a g)
    (hPW : ∀ w : ℂ, ghatC g a w = 0 → (w ^ 2).im ≠ 0 → SwapRealization a g (w ^ 2)) :
    ∀ w : ℂ, ghatC g a w = 0 → w.re = 0 ∨ w.im = 0 := by
  intro w hw
  by_contra hne
  push Not at hne
  have him : (w ^ 2).im ≠ 0 := by
    rw [sq, Complex.mul_im]
    have := mul_ne_zero hne.1 hne.2
    intro h; apply this; linarith
  exact U.zero_swap_false ha hs him (hPW w hw him)

/-- **Zeros of a simple ground state lie on `ℝ ∪ iℝ`**, no further input (`swapRealization_of_zero`
holds for every probe). -/
theorem zeros_real_or_imag' (ha : 0 < a) {g : ℝ → ℝ} (hs : U.SimpleGround a g) :
    ∀ w : ℂ, ghatC g a w = 0 → w.re = 0 ∨ w.im = 0 :=
  U.zeros_real_or_imag ha hs fun _ hw hσ => swapRealization_of_zero ha hs.1.1 hw hσ

/-- The swapped pair of a ground-space element lies in the ground space. -/
theorem swap_pair_mem {g : ℝ → ℝ} {w : ℂ} (ha : 0 < a) (hg : g ∈ U.groundSpace a)
    (hw : ghatC g a w = 0) (hσ : (w ^ 2).im ≠ 0) :
    uSw g a w ∈ U.groundSpace a ∧ vSw g a w ∈ U.groundSpace a := by
  have hp : Probe a g := hg.1
  have hw0 : w ≠ 0 := by rintro rfl; apply hσ; simp
  have hac := swap_autocorr hp ha hw hw0 hσ
  have hac' : ∀ s, autocorr (vSw g a w) s + autocorr (uSw g a w) s = autocorr g s :=
    fun s => by rw [add_comm]; exact hac s
  have hu : Probe a (uSw g a w) := ⟨uSw_even hp hw, uSw_supp hp hw, memLp_uSw hp hw,
    arch_dom (memLp_uSw hp hw) (memLp_vSw hp hw) hac hp.arch⟩
  have hv : Probe a (vSw g a w) := ⟨vSw_even hp hw, vSw_supp hp hw, memLp_vSw hp hw,
    arch_dom (memLp_vSw hp hw) (memLp_uSw hp hw) hac' hp.arch⟩
  exact U.split_mem hg hu hv hac

/-- **Swap closure**: if `g` is in the ground space and `ĝ(w) = 0` with `w²` non-real, the real and
imaginary parts of the Green solution `h = (∂² + w²)⁻¹ g` lie in the ground space. -/
theorem green_mem {g : ℝ → ℝ} {w : ℂ} (ha : 0 < a)
    (hg : g ∈ U.groundSpace a) (hw : ghatC g a w = 0) (hσ : (w ^ 2).im ≠ 0) :
    (fun x => (hSw g a w x).re) ∈ U.groundSpace a ∧
      (fun x => (hSw g a w x).im) ∈ U.groundSpace a := by
  obtain ⟨hu, hv⟩ := U.swap_pair_mem ha hg hw hσ
  set s := (w ^ 2).im
  have hc : ∀ x, ((starRingEnd ℂ) (w ^ 2) - w ^ 2) * hSw g a w x
      = ((2 * s * (hSw g a w x).im : ℝ) : ℂ)
        + ((-2 * s * (hSw g a w x).re : ℝ) : ℂ) * Complex.I := by
    intro x
    have e1 : ((starRingEnd ℂ) (w ^ 2) - w ^ 2).re = 0 := by
      simp only [Complex.sub_re, Complex.conj_re, sub_self]
    have e2 : ((starRingEnd ℂ) (w ^ 2) - w ^ 2).im = -2 * s := by
      simp only [Complex.sub_im, Complex.conj_im, s]; ring
    apply Complex.ext
    · rw [Complex.mul_re, e1, e2]; simp
    · rw [Complex.mul_im, e1, e2]; simp
  have hre : (fun x => (hSw g a w x).re) = fun x => (-(2 * s)⁻¹) * vSw g a w x := by
    funext x
    have : vSw g a w x = -2 * s * (hSw g a w x).re := by
      rw [vSw_eq]; simp only; rw [hc x]; simp
    rw [this]; field_simp
  have him : (fun x => (hSw g a w x).im)
      = fun x => (2 * s)⁻¹ * (uSw g a w x + (-1) * g x) := by
    funext x
    have : uSw g a w x = g x + 2 * s * (hSw g a w x).im := by
      rw [uSw_eq]; simp only; rw [hc x]; simp
    rw [this]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hre]; exact (U.groundSpace a).smul_mem _ hv
  · rw [him]
    have := (U.groundSpace a).add_mem hu ((U.groundSpace a).smul_mem (-1) hg)
    exact (U.groundSpace a).smul_mem _ (by convert this using 1)

/-! ### Stage 4: the Green steps and finite dimension -/

/-- **`Q − λ` pairs `G v` with every pole-free probe to zero**, for `v` in the ground space (no pole
term, so no pole hypothesis on `v`). -/
theorem Gpole_annihilates (ha : 0 ≤ a) {v m : ℝ → ℝ} (hv : v ∈ U.groundSpace a)
    (hm : Probe a m) (hmpole : poleR m a = 0) :
    U.bil a (Gpole v a) m - U.lam a * xcorr (Gpole v a) m 0 = 0 := by
  have el := U.euler_lagrange_mem hv (Gpole_probe hm ha hmpole)
  have hsw : U.bil a (Gpole v a) m = U.bil a v (Gpole m a) := by
    unfold UData.bil archXQ
    simp only [xcorr_G_swap ha hv.1 hm hmpole]
  rw [hsw, xcorr_G_swap ha hv.1 hm hmpole, el, sub_self]

/-- `Q_λ(φ + rψ) = Q_λ(φ) + 2r B_λ(φ, ψ) + r² Q_λ(ψ)` for `Q_λ = Q − λ‖·‖²`. -/
theorem Qlam_add_smul {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (r : ℝ) :
    U.Q (fun t => φ t + r * ψ t) - U.lam a * normSq (fun t => φ t + r * ψ t)
      = (U.Q φ - U.lam a * normSq φ) + 2 * r * (U.bil a φ ψ - U.lam a * xcorr φ ψ 0)
        + r ^ 2 * (U.Q ψ - U.lam a * normSq ψ) := by
  rw [U.Q_add_smul hφ hψ, normSq_add_smul hφ.memL2 hψ.memL2]; ring

theorem Qlam_nonneg {k : ℝ → ℝ} (hk : Probe a k) : 0 ≤ U.Q k - U.lam a * normSq k := by
  have := U.lam_mul_le hk; linarith

/-- If `w` is pole-free in the ground space and `G w` is pole-free, `G w` is in the ground space. -/
theorem G_mem_pole_free (ha : 0 ≤ a) {w : ℝ → ℝ} (hw : w ∈ U.groundSpace a)
    (hwp : poleR w a = 0) (hGp : poleR (Gpole w a) a = 0) : Gpole w a ∈ U.groundSpace a := by
  have hP := Gpole_probe hw.1 ha hwp
  refine ⟨hP, ?_⟩
  have key := U.Gpole_annihilates ha hw hP hGp
  show U.Q (Gpole w a) = U.lam a * normSq (Gpole w a)
  rw [U.Q_eq_bil hP, normSq_eq_xcorr hP.memL2]
  linarith

/-- **Rank-one step**: if `w` is pole-free in the ground space and some ground-space element `k` has
`k̂(i/2) ≠ 0`, then `G w` is in the ground space. -/
theorem G_mem_partner (ha : 0 ≤ a) {w k : ℝ → ℝ} (hw : w ∈ U.groundSpace a)
    (hwp : poleR w a = 0) (hk : k ∈ U.groundSpace a) (hkp : poleR k a ≠ 0) :
    Gpole w a ∈ U.groundSpace a := by
  set H := Gpole w a
  have hP : Probe a H := Gpole_probe hw.1 ha hwp
  set s := -(poleR H a / poleR k a)
  set f : ℝ → ℝ := fun t => H t + s * k t
  have hf : Probe a f := probe_add_smul hP hk.1 s
  have hfp : poleR f a = 0 := by
    simp only [f]
    rw [poleR_add hP.memL2 (hk.1.memL2.const_mul s) a, poleR_smul]
    simp only [s]; field_simp; ring
  have hB : U.bil a H f - U.lam a * xcorr H f 0 = 0 := U.Gpole_annihilates ha hw hf hfp
  have hexp := U.Qlam_add_smul hP hf (-1)
  have hfun : (fun t => H t + (-1) * f t) = fun t => (-s) * k t := by
    funext t; simp only [f]; ring
  rw [hfun, U.Q_smul, normSq_smul, hB] at hexp
  have hk0 : U.Q k - U.lam a * normSq k = 0 := by
    have : U.Q k = U.lam a * normSq k := hk.2
    rw [this]; ring
  have e0 : (-s) ^ 2 * U.Q k - U.lam a * ((-s) ^ 2 * normSq k) = 0 := by
    linear_combination (-s) ^ 2 * hk0
  have n1 := U.Qlam_nonneg hP
  have n2 := U.Qlam_nonneg hf
  exact ⟨hP, show U.Q H = U.lam a * normSq H by nlinarith⟩

/-- The ground space mapped into `L²`. -/
abbrev iotaGS (a : ℝ) : U.groundSpace a →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) := iotaOf U.form a

theorem norm_iotaGS_sq {a : ℝ} (x : U.groundSpace a) : ‖U.iotaGS a x‖ ^ 2 = normSq x.1 := by
  show ‖x.2.1.memL2.toLp x.1‖ ^ 2 = _
  rw [L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [x.2.1.memL2.coeFn_toLp] with t ht
  rw [ht]

theorem nonArch_ge' (hp : Probe a g) : -(U.M a * normSq g) ≤ U.nonArch a g := by
  have hP := U.abs_prime_le hp
  have hN := normSq_nonneg g
  have hc : -(|U.c| * normSq g) ≤ U.c * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hN
  have h2 := le_abs_self
    (∑ n ∈ Finset.range (primeCut a), U.f n / Real.sqrt n * autocorr g (Real.log n))
  unfold UData.nonArch UData.M
  nlinarith

/-- The archimedean energy of a ground-space element is controlled by its norm. -/
theorem archE_le_of_mem (ha : 0 < a) (hg : g ∈ U.groundSpace a) :
    archE g ≤ (Real.exp (2 * a) * (|U.lam a| + U.M a) + tailDH a) * normSq g := by
  have hq : U.Q g = U.lam a * normSq g := hg.2
  have hN := normSq_nonneg g
  have h1 := U.archE_le ha hg.1
  have e := U.Q_eq_nonArch (a := a) hg.1.supp
  have hA : archEQ U.q g ≤ (|U.lam a| + U.M a) * normSq g := by
    have hl : U.lam a * normSq g ≤ |U.lam a| * normSq g :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hN
    have := U.nonArch_ge' hg.1
    rw [hq] at e
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left hA (Real.exp_pos (2 * a)).le
  nlinarith

/-- **The ground space is finite-dimensional** (its image in `L²`). -/
theorem finiteDimensional_groundL2 (ha : 0 < a) :
    FiniteDimensional ℝ (LinearMap.range (U.iotaGS a)) := by
  by_contra hfin
  obtain ⟨R, f, hR, hfR, hsep⟩ :=
    exists_seq_norm_le_one_le_norm_sub (𝕜 := ℝ) (E := LinearMap.range (U.iotaGS a)) hfin
  have hx : ∀ n, ∃ x : U.groundSpace a, U.iotaGS a x = (f n : Lp ℝ 2 volume) :=
    fun n => LinearMap.mem_range.1 (f n).2
  choose x hxf using hx
  set h : ℕ → ℝ → ℝ := fun n => (x n).1
  have hp : ∀ n, Probe a (h n) := fun n => (x n).2.1
  have hN : ∀ n, normSq (h n) ≤ R ^ 2 := by
    intro n
    rw [← U.norm_iotaGS_sq, hxf n, Submodule.norm_coe]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfR n) 2
  set K := Real.exp (2 * a) * (|U.lam a| + U.M a) + tailDH a
  have hK : 0 ≤ K := by
    have := U.M_nonneg a
    have := tailDH_nonneg a
    positivity
  have hC : ∀ n, archE (h n) ≤ K * R ^ 2 :=
    fun n => (U.archE_le_of_mem ha (x n).2).trans (mul_le_mul_of_nonneg_left (hN n) hK)
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

/-- **The u-space form as a ground-state family** (GroundChain.lean's `GroundData`). -/
def gd : GroundData where
  Q := fun _ => U.Q
  form := U.form
  partner := fun ha hw hwp hk hkp => U.G_mem_partner ha hw hwp hk hkp
  poleFree := fun ha hw hwp hGp => U.G_mem_pole_free ha hw hwp hGp
  green := fun ha hg hw hσ => U.green_mem ha hg hw hσ
  fd := fun ha => U.finiteDimensional_groundL2 ha
  nonzero := fun ha => by
    obtain ⟨g, hg⟩ := U.exists_groundState ha
    exact ⟨g, (U.isGroundState_iff.1 hg).1, (U.isGroundState_iff.1 hg).2⟩

/-- **The top-of-chain ground state**: `G^{m−1}w`, normalised (GroundChain.lean's `topGS`). -/
abbrev topGS (a : ℝ) : ℝ → ℝ := U.gd.topGS a

theorem topGS_isGroundState (ha : 0 < a) : U.IsGroundState a (U.topGS a) :=
  U.isGroundState_iff.2 (U.gd.topGS_mem ha)

/-- **Every zero of the top-of-chain ground state's transform lies on `ℝ ∪ iℝ`**, at every support
`a > 0`, with no simplicity assumption. -/
theorem topGS_cross (ha : 0 < a) (z : ℂ) (hz : ghatC (U.topGS a) a z = 0) : z.re = 0 ∨ z.im = 0 :=
  U.gd.topGS_cross ha z hz

end UData

/-- **The Davenport–Heilbronn form is the instance `q = ¾`.** -/
def dhU : UData := ⟨constDH, 3 / 4, fDH, Or.inr rfl⟩

theorem dhU_Q : dhU.Q = QDHu := rfl

theorem dhU_lam (a : ℝ) : dhU.lam a = lamDH a := rfl

/-! ## The χ column -/

section Chi

open DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {a : ℝ} {g : ℝ → ℝ}

omit [NeZero N] in
/-- `q_χ = ¼` for even `χ` and `¾` for odd `χ`. -/
theorem qC_cases (χ : DirichletCharacter ℂ N) : qC χ = 1 / 4 ∨ qC χ = 3 / 4 := by
  unfold qC
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (parity_le χ) with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

/-- **Weil's form for `L(s, χ)` as a u-space form**: `c = cChi χ`, `q = qC χ`, `f = fχ χ`. -/
def chiU (χ : DirichletCharacter ℂ N) : UData := ⟨cChi χ, qC χ, fχ χ, qC_cases χ⟩

theorem chiU_Q (χ : DirichletCharacter ℂ N) : (chiU χ).Q = QCu χ := rfl

theorem chiU_lam (χ : DirichletCharacter ℂ N) (a : ℝ) : (chiU χ).lam a = lamC χ a := rfl

/-- **The ground-state family of `QCu χ`**, for every Dirichlet character `χ`. -/
def chiGD (χ : DirichletCharacter ℂ N) : GroundData := (chiU χ).gd

/-- The ground-state space of `QCu χ`: probes with `Q_χ(g) = λ_χ(a)‖g‖²`. -/
abbrev groundSpaceC (χ : DirichletCharacter ℂ N) (a : ℝ) : Submodule ℝ (ℝ → ℝ) :=
  (chiU χ).groundSpace a

/-- **A ground state of `QCu χ`**: a normalised probe with `Q_χ(g) = λ_χ(a)`. -/
def IsGroundStateC (χ : DirichletCharacter ℂ N) (a : ℝ) (g : ℝ → ℝ) : Prop :=
  Probe a g ∧ normSq g = 1 ∧ QCu χ g = lamC χ a

theorem isGroundStateC_iff : IsGroundStateC χ a g ↔ g ∈ groundSpaceC χ a ∧ normSq g = 1 :=
  (chiU χ).isGroundState_iff

/-- **A ground state of `QCu χ` exists at every support `a > 0`.** -/
theorem exists_groundStateC (ha : 0 < a) : ∃ g, IsGroundStateC χ a g :=
  (chiU χ).exists_groundState ha

/-- **Euler–Lagrange for `QCu χ`**: `B_χ(w, ψ) = λ_χ⟨w, ψ⟩` on the ground space. -/
theorem euler_lagrangeC_mem {w ψ : ℝ → ℝ} (hw : w ∈ groundSpaceC χ a) (hψ : Probe a ψ) :
    (chiU χ).bil a w ψ = lamC χ a * xcorr w ψ 0 :=
  (chiU χ).euler_lagrange_mem hw hψ

/-- `f` starts a Green chain of length `j` in the ground space of `QCu χ`. -/
abbrev IsChainC (χ : DirichletCharacter ℂ N) (a : ℝ) (j : ℕ) (f : ℝ → ℝ) : Prop :=
  (chiGD χ).IsChain a j f

/-- The dimension of the ground space of `QCu χ`. -/
abbrev gdimC (χ : DirichletCharacter ℂ N) (a : ℝ) : ℕ := (chiGD χ).gdim a

omit [NeZero N] in
/-- **Round 48's Theorem D for `QCu χ`.** With `m = dim V_χ` (finite), there is a nonzero `w` whose
Green chain `w, Gw, …, G^{m−1}w` lies in the ground space (all but the last pole-free), is linearly
independent, and spans it a.e.; every zero `ω` of `ĥ`, `h = G^{m−1}w`, has `ω² ∈ ℝ`. -/
theorem theoremDC (ha : 0 < a) :
    ∃ w, IsChainC χ a (gdimC χ a - 1) w ∧ 0 < normSq w ∧
      (∃ hc : IsChainC χ a (gdimC χ a - 1) w,
        LinearIndependent ℝ (fun i => ((chiGD χ).iota a).rangeRestrict ((chiGD χ).chainVec hc i))) ∧
      (∀ v ∈ groundSpaceC χ a, ∃ c : Fin (gdimC χ a - 1 + 1) → ℝ,
        v =ᵐ[volume] fun x => ∑ i, c i * Gi a i w x) ∧
      ∀ ω : ℂ, ghatC (Gi a (gdimC χ a - 1) w) a ω = 0 → (ω ^ 2).im = 0 :=
  (chiGD χ).theoremD ha

/-- **The top-of-chain ground state of `QCu χ`.** -/
abbrev topGSC (χ : DirichletCharacter ℂ N) (a : ℝ) : ℝ → ℝ := (chiGD χ).topGS a

theorem topGSC_isGroundState (ha : 0 < a) : IsGroundStateC χ a (topGSC χ a) :=
  (chiU χ).topGS_isGroundState ha

omit [NeZero N] in
/-- **Every zero of `ĝ` for the top-of-chain ground state of `QCu χ` lies on `ℝ ∪ iℝ`**, at every
support `a > 0`, with no simplicity assumption. -/
theorem topGSC_cross (ha : 0 < a) (z : ℂ) (hz : ghatC (topGSC χ a) a z = 0) :
    z.re = 0 ∨ z.im = 0 :=
  (chiU χ).topGS_cross ha z hz

/-- A ground state of `QCu χ` is **simple** when the ground-state space is spanned by it. -/
abbrev SimpleGroundC (χ : DirichletCharacter ℂ N) (a : ℝ) (g : ℝ → ℝ) : Prop :=
  (chiU χ).SimpleGround a g

/-! ### The chain to GRH(χ) -/

/-- **`HypConv` with `Ξ_χ` as the target** (PrimeSide.lean:37 with `XiC χ` in place of `Xi`). -/
def HypConvC (χ : DirichletCharacter ℂ N) (a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) : Prop :=
  TendstoLocallyUniformly (fun n z => ghatC (g n) (a n) z / ghatC (g n) (a n) 0)
    (fun z => XiC χ z / XiC χ 0) atTop

theorem HypConvC.eventually_ne (hG : GoodChar χ) {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (h : HypConvC χ a g) : ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 := by
  have ht := (tendstoLocallyUniformlyOn_univ.2 h).tendsto_at (Set.mem_univ (0 : ℂ))
  simp only [div_self (XiC_zero_ne hG)] at ht
  filter_upwards [ht.eventually_ne one_ne_zero] with n hn h0
  rw [h0, div_zero] at hn; exact hn rfl

/-- `Ξ_χ` at the ordinate of `s` is `Λ*(s, χ)`. -/
theorem XiC_at_ordinate (s : ℂ) : XiC χ ((s - 1 / 2) / Complex.I) = LamG χ s := by
  unfold XiC; congr 1; field_simp; ring

/-- A zero of `L(s, χ)` with `Re s > 0` is a zero of `Λ*(s, χ)`. -/
theorem LamG_eq_zero_of {s : ℂ} (hs : 0 < s.re) (hL : LFunction χ s = 0) : LamG χ s = 0 := by
  unfold LamG; rw [completed_eq_mul hs, hL, mul_zero, mul_zero]

/-- **The Hurwitz step of `rh_of_prime_side_cross`** (HurwitzCross.lean:45) **for `L(s, χ)`**:
integrable `g_n` whose transforms eventually have every zero on `ℝ ∪ iℝ`, with `HypConvC χ`, give GRH
for `χ` off the real axis. -/
theorem grhCross_of_cross (hG : GoodChar χ) {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0)
    (hconv : HypConvC χ a g) : CrossCriteria.GRHCross χ := by
  have hX0 := XiC_zero_ne hG
  obtain ⟨N0, hN0⟩ := (hcross.and (hconv.eventually_ne hG)).exists_forall_of_atTop
  have hXc : ∀ z, XiC χ z / XiC χ 0 = 0 → z ∈ crossSet :=
    hurwitz_closed
      (F := fun m z => ghatC (g (m + N0)) (a (m + N0)) z / ghatC (g (m + N0)) (a (m + N0)) 0)
      (fun m => (ghatC_differentiable (hint _)).div_const _)
      ((differentiable_XiC hG).div_const _) (tendstoLocallyUniformly_shift hconv N0)
      ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩ isClosed_crossSet
      (fun m z h => (hN0 (m + N0) (by omega)).1 z
        ((div_eq_zero_iff.1 h).resolve_right (hN0 (m + N0) (by omega)).2))
  intro s hs h0 _
  rcases hXc ((s - 1 / 2) / Complex.I)
      (by rw [XiC_at_ordinate, LamG_eq_zero_of h0 hs, zero_div]) with hre | him
  · right; rwa [re_ordinate] at hre
  · left; exact re_eq_half_of_Xi_real him

/-- **GRH for `χ` off the real axis from `HypConvC χ` for the top-of-chain ground states**, at every
sequence of positive supports, with no simplicity assumption. -/
theorem grhCross_of_hypConvC_top (hG : GoodChar χ) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConvC χ a fun n => topGSC χ (a n)) : CrossCriteria.GRHCross χ :=
  grhCross_of_cross hG
    (fun n => (probe_integrable (topGSC_isGroundState (ha n)).1).intervalIntegrable)
    (Eventually.of_forall fun n z hz => topGSC_cross (ha n) z hz) hconv

/-- **GRH for `χ` from `HypConvC χ` for the top-of-chain ground states**, given no zero of `L(σ, χ)` in
`(0, 1)` (the χ column of `rh_of_hypConv_top`, StructureD.lean:192). -/
theorem grh_of_hypConvC_top (hG : GoodChar χ) (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hconv : HypConvC χ a fun n => topGSC χ (a n)) : GRH χ :=
  CrossCriteria.grh_of_cross (grhCross_of_hypConvC_top hG ha hconv) hS

/-- **GRH for `χ` from eventually simple ground states with `HypConvC χ`** (the χ column of
`rh_of_eventually_simple`, SwapRealize.lean:412: the chain of HurwitzCross.lean with the swap
realisation proved). -/
theorem grh_of_eventually_simpleC (hG : GoodChar χ)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (ha : ∀ n, 0 < a n) (hgs : ∀ n, IsGroundStateC χ (a n) (g n))
    (hsimple : ∀ᶠ n in atTop, SimpleGroundC χ (a n) (g n)) (hconv : HypConvC χ a g) : GRH χ :=
  CrossCriteria.grh_of_cross
    (grhCross_of_cross hG (fun n => (probe_integrable (hgs n).1).intervalIntegrable)
      (hsimple.mono fun n hs => (chiU χ).zeros_real_or_imag' (ha n) hs) hconv) hS

/-- If the ground states `g n` of `QCu χ` are eventually simple, they agree with the top-of-chain
ground states up to scalars, so `HypConvC χ` transfers (the χ column of `hypConv_top_of_simple`,
StructureD.lean:199). -/
theorem hypConvC_top_of_simple {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hsimple : ∀ᶠ n in atTop, SimpleGroundC χ (a n) (g n)) (hconv : HypConvC χ a g) :
    HypConvC χ a fun n => topGSC χ (a n) := by
  have heq : ∀ᶠ n in atTop, ∀ z : ℂ,
      ghatC (topGSC χ (a n)) (a n) z / ghatC (topGSC χ (a n)) (a n) 0
        = ghatC (g n) (a n) z / ghatC (g n) (a n) 0 := by
    filter_upwards [hsimple] with n hs z
    obtain ⟨c, hcg⟩ := hs.2 _ (isGroundStateC_iff.1 (topGSC_isGroundState (ha n))).1
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := normSq_congr_ae hcg
      rw [(topGSC_isGroundState (ha n)).2.1] at this
      simp [Pilot1ca.normSq] at this
    rw [ghatC_congr_ae hcg, ghatC_congr_ae hcg, ghatC_smul, ghatC_smul,
      mul_div_mul_left _ _ (by exact_mod_cast hc0)]
  intro u hu x
  obtain ⟨t, ht, hev⟩ := hconv u hu x
  refine ⟨t, ht, ?_⟩
  filter_upwards [hev, heq] with n hn he y hy
  rw [he y]; exact hn y hy

end Chi

/-! ### Instances -/

/-- **GRH for `χ₋₃` from `HypConvC` for its top-of-chain ground states.** -/
theorem grh_chi3_of_hypConvC_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConvC chi3 a fun n => topGSC chi3 (a n)) : GRH chi3 :=
  grh_of_hypConvC_top good_chi3 (fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi3_ne_one chi3_isQuadratic sums_chi3 hσ) ha hconv

/-- **GRH for `χ₋₄` from `HypConvC` for its top-of-chain ground states.** -/
theorem grh_chi4_of_hypConvC_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConvC chi4 a fun n => topGSC chi4 (a n)) : GRH chi4 :=
  grh_of_hypConvC_top good_chi4 (fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi4_ne_one chi4_isQuadratic sums_chi4 hσ) ha hconv

/-- **GRH for `χ₋₈` from `HypConvC` for its top-of-chain ground states.** -/
theorem grh_chi8_of_hypConvC_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConvC chi8 a fun n => topGSC chi8 (a n)) : GRH chi8 :=
  grh_of_hypConvC_top good_chi8 (fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi8_ne_one chi8_isQuadratic sums_chi8 hσ) ha hconv

/-- **GRH for `χ₋₇` from `HypConvC` for its top-of-chain ground states.** -/
theorem grh_chi7_of_hypConvC_top {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hconv : HypConvC WeilTwinGeneral.chi7 a fun n => topGSC WeilTwinGeneral.chi7 (a n)) :
    GRH WeilTwinGeneral.chi7 :=
  grh_of_hypConvC_top WeilTwinGeneral.good_chi7 WeilTwinGeneral.hS7 ha hconv

end PsiOmega

#print axioms PsiOmega.UData.form
#print axioms PsiOmega.UData.exists_groundState
#print axioms PsiOmega.UData.euler_lagrange_mem
#print axioms PsiOmega.UData.zeros_real_or_imag'
#print axioms PsiOmega.UData.green_mem
#print axioms PsiOmega.UData.G_mem_partner
#print axioms PsiOmega.UData.finiteDimensional_groundL2
#print axioms PsiOmega.UData.topGS_cross
#print axioms PsiOmega.dhU_lam
#print axioms PsiOmega.chiU_lam
#print axioms PsiOmega.exists_groundStateC
#print axioms PsiOmega.theoremDC
#print axioms PsiOmega.topGSC_cross
#print axioms PsiOmega.grhCross_of_cross
#print axioms PsiOmega.grhCross_of_hypConvC_top
#print axioms PsiOmega.grh_of_hypConvC_top
#print axioms PsiOmega.grh_of_eventually_simpleC
#print axioms PsiOmega.hypConvC_top_of_simple
#print axioms PsiOmega.grh_chi3_of_hypConvC_top
#print axioms PsiOmega.grh_chi4_of_hypConvC_top
#print axioms PsiOmega.grh_chi8_of_hypConvC_top
#print axioms PsiOmega.grh_chi7_of_hypConvC_top
