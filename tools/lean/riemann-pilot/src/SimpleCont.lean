import Mathlib
import ParityCont
import DegenerateFlat

/-! # Round 148: continuation for simplicity

Round 146's continuation lemma does not transfer literally: `λ₁ ≤ λ₂` always, so "`λ₁ ≠ λ₂` for all
`a ≥ a₀`" *is* simplicity on `[a₀, ∞)`, and a continuation argument adds nothing. What does transfer,
and is not a tautology, is **closedness of the degeneracy set**, which is what continuity of `λ₂` would
be used for:

* **S1.** `λ₁` (even sector) is continuous on `(0, ∞)`: right-continuity by compactness and lower
  semicontinuity (`lsc_even`), left-continuity by dilation (round 146's `dil`, now for either parity).
* **S2.** `Degenerate a` (two orthonormal ground states) is equivalent to non-simplicity, and the set of
  degenerate supports is closed in `(0, ∞)` (`degenerate_of_tendsto`): orthonormal ground pairs at
  `bₙ → a` have `L²` limits that are an orthonormal ground pair at `a`.
* **S3. The first degeneracy** (`first_degeneracy`). If the ground state is simple at `a₀` but not at
  some `a₁ > a₀`, there is a least degenerate support `m ∈ (a₀, a₁]`. Ground states are simple on
  `[a₀, m)`, and at `m` Theorem D supplies a nonzero pole-free ground state `w` whose Green solution
  `G w` is also a ground state. With `a₀ = 0.36` (`simpleGround_036`) this is unconditional.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## S1: continuity of `λ₁` -/

/-- `o − S_a o` is the part of an even probe outside `[−a, a]`. -/
theorem symCut_probe' {b : ℝ} {o : ℝ → ℝ} (hp : Probe b o) (a : ℝ) (u : ℝ) :
    o u - symCut a o u = if |u| ≤ a then 0 else o u := by
  unfold symCut; split_ifs
  · rw [hp.even]; ring
  · ring

/-- **The shell estimate, even sector.** `‖o − S_a G‖² ≤ 6‖o − G‖² + 4∫_{a<|u|≤b} G²`. -/
theorem normSq_sub_symCut_shell {a b : ℝ} {o G : ℝ → ℝ} (hp : Probe b o) (hG : MemLp G 2 volume) :
    normSq (fun t => o t - symCut a G t) ≤ 6 * normSq (fun t => o t - G t) + 4 * shellSq G a b := by
  have hoG := hp.memL2.sub hG
  set x : ℝ → ℝ := fun t => o t - symCut a o t with hx
  set y : ℝ → ℝ := symCut a (fun t => o t - G t) with hy
  have hxm : MemLp x 2 volume := hp.memL2.sub (memLp_symCut a hp.memL2)
  have hym : MemLp y 2 volume := memLp_symCut a hoG
  have hsplit : (fun t => o t - symCut a G t) = fun t => x t + y t := by
    funext t; simp only [hx, hy, symCut_sub]; ring
  have hy2 : normSq y ≤ normSq (fun t => o t - G t) := normSq_symCut_le a hoG
  have hx2 : normSq x ≤ 2 * normSq (fun t => o t - G t) + 2 * shellSq G a b := by
    set ind := Set.indicator {u | a < |u| ∧ |u| ≤ b} (fun u => G u ^ 2) with hind
    have hI1 : Integrable (fun t => (o t - G t) ^ 2) := hoG.integrable_sq
    have hI2 : Integrable ind := hG.integrable_sq.indicator (measurableSet_shell a b)
    have hsum : (∫ t, (2 * (o t - G t) ^ 2 + 2 * ind t))
        = 2 * normSq (fun t => o t - G t) + 2 * shellSq G a b := by
      rw [integral_add (hI1.const_mul 2) (hI2.const_mul 2), integral_const_mul, integral_const_mul]; rfl
    rw [← hsum]
    refine integral_mono hxm.integrable_sq ((hI1.const_mul 2).add (hI2.const_mul 2)) fun t => ?_
    simp only [hx, symCut_probe' hp a t]
    have hind0 : 0 ≤ ind t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
    split_ifs with h1
    · nlinarith [sq_nonneg (o t - G t)]
    · by_cases h2 : |t| ≤ b
      · rw [hind, Set.indicator_of_mem (show t ∈ {u | a < |u| ∧ |u| ≤ b} from ⟨lt_of_not_ge h1, h2⟩)]
        nlinarith [sq_nonneg (o t - 2 * G t)]
      · rw [hp.supp t (lt_of_not_ge h2)]
        nlinarith [sq_nonneg (G t)]
  rw [hsplit]
  linarith [normSq_add_le hxm hym]

/-- **Lower semicontinuity along shrinking supports.** Normalised even probes at `bₙ ↓ a` whose
energies converge to `L` have an `L²`-convergent subsequence whose limit is a normalised probe at `a`
with `Q ≤ L`. -/
theorem lsc_even {a a₁ : ℝ} (ha : 0 < a) {b : ℕ → ℝ} (hb : ∀ n, a ≤ b n) (hb1 : ∀ n, b n ≤ a₁)
    (hbt : Tendsto b atTop (𝓝 a)) {h : ℕ → ℝ → ℝ} (hp : ∀ n, Probe (b n) (h n))
    (hn : ∀ n, normSq (h n) = 1) {L : ℝ} (hq : Tendsto (fun n => weilQ a₁ (h n)) atTop (𝓝 L)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G, Probe a G ∧ normSq G = 1 ∧ weilQ a G ≤ L ∧
      Tendsto (fun j => normSq (fun t => h (φ j) t - G t)) atTop (𝓝 0) := by
  have ha₁ : 0 < a₁ := ha.trans_le ((hb 0).trans (hb1 0))
  have hp1 : ∀ n, Probe a₁ (h n) := fun n => (hp n).mono (hb1 n)
  obtain ⟨M, hM⟩ := hq.bddAbove_range
  have hQM : ∀ n, weilQ a₁ (h n) ≤ M := fun n => hM ⟨n, rfl⟩
  have hC : ∀ n, archE (h n) ≤ M - (weilConst - 2 * primeWeight a₁) := by
    intro n
    have e := weilQ_eq' a₁ (h n)
    have h1 := (le_abs_self _).trans (abs_prime_sum_le (hp1 n))
    have h2 : 0 ≤ 2 * poleR (h n) a₁ ^ 2 := by positivity
    rw [hn n, mul_one] at h1
    have h3 := hQM n
    unfold primeS at e
    rw [hn n, mul_one] at e
    linarith
  obtain ⟨φ, hφ, G, hG, hlim⟩ := exists_convergent_subseq_S ha₁ (fun n => (hp1 n).toS)
    (B := 1) (fun n => (hn n).le) hC
  refine ⟨φ, hφ, symCut a G, ?_⟩
  set G' := symCut a G with hG'def
  have hG' : MemLp G' 2 volume := memLp_symCut a hG
  set hh : ℕ → ℝ → ℝ := fun j => h (φ j) with hhdef
  have hmem : ∀ j, MemLp (hh j) 2 volume := fun j => (hp (φ j)).memL2
  have hlim' : Tendsto (fun j => normSq (fun t => hh j t - G' t)) atTop (𝓝 0) := by
    have hsh := tendsto_shellSq hG (hbt.comp hφ.tendsto_atTop)
    have hup : Tendsto (fun j => 6 * normSq (fun t => hh j t - G t) + 4 * shellSq G a (b (φ j)))
        atTop (𝓝 0) := by
      have := (hlim.const_mul 6).add (hsh.const_mul 4)
      rw [mul_zero, mul_zero, add_zero] at this
      exact this
    exact squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _)
      (fun j => normSq_sub_symCut_shell (hp (φ j)) hG) hup
  have hnorm : Tendsto (fun j => normSq (hh j)) atTop (𝓝 (normSq G')) := by
    simp_rw [normSq_eq_mul]
    exact tendsto_integral_mul hmem hmem hG' hG' hlim' hlim'
  have hnormG : normSq G' = 1 :=
    tendsto_nhds_unique hnorm (tendsto_const_nhds.congr fun j => (hn (φ j)).symm)
  have hw0 : Tendsto (fun _ : ℕ => normSq (fun t => poleW a₁ t - poleW a₁ t)) atTop (𝓝 0) := by
    simp only [sub_self]; simp [normSq]
  have hpoleT : Tendsto (fun j => poleR (hh j) a₁) atTop (𝓝 (poleR G' a₁)) := by
    simp_rw [poleR_eq ha₁.le]
    exact tendsto_integral_mul hmem (fun _ => poleW_memLp a₁) hG' (poleW_memLp a₁) hlim' hw0
  have hauto : ∀ u, Tendsto (fun j => autocorr (hh j) u) atTop (𝓝 (autocorr G' u)) := by
    intro u
    have hsh : ∀ j, normSq (fun t => hh j (t + u) - G' (t + u)) = normSq (fun t => hh j t - G' t) :=
      fun j => normSq_shift (fun t => hh j t - G' t) u
    unfold autocorr
    exact tendsto_integral_mul hmem (fun j => memLp_shift (hmem j) u) hG' (memLp_shift hG' u)
      hlim' (hlim'.congr fun j => (hsh j).symm)
  have hsuppG' : ∀ u, a < |u| → G' u = 0 := symCut_supp a G
  have haa₁ : a ≤ a₁ := (hb 0).trans (hb1 0)
  have hsuppG1 : ∀ u, a₁ < |u| → G' u = 0 := fun u hu => hsuppG' u (by linarith)
  have hprimeT : Tendsto (fun j => primeS (hh j)) atTop (𝓝 (primeS G')) := by
    unfold primeS
    have e1 : ∀ j, (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * autocorr (hh j) (Real.log n))
        = ∑ n ∈ Finset.range (primeCut a₁), ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * autocorr (hh j) (Real.log n) := fun j => prime_sum_eq (hp1 (φ j)).supp
    simp_rw [e1]
    rw [prime_sum_eq hsuppG1]
    exact tendsto_finsetSum _ fun n _ => (hauto _).const_mul _
  set nA : ℝ → ℝ → ℝ := fun P S => 2 * P ^ 2 + weilConst * 1 - 2 * S with hnA
  have hnon : Tendsto (fun j => nA (poleR (hh j) a₁) (primeS (hh j))) atTop
      (𝓝 (nA (poleR G' a₁) (primeS G'))) := by
    simp only [hnA]
    exact (((hpoleT.pow 2).const_mul 2).add tendsto_const_nhds).sub (hprimeT.const_mul 2)
  have hqφ : Tendsto (fun j => weilQ a₁ (hh j)) atTop (𝓝 L) := hq.comp hφ.tendsto_atTop
  have hA : Tendsto (fun j => archE (hh j)) atTop (𝓝 (L - nA (poleR G' a₁) (primeS G'))) := by
    have e : ∀ j, archE (hh j) = weilQ a₁ (hh j) - nA (poleR (hh j) a₁) (primeS (hh j)) := by
      intro j
      simp only [hnA]; rw [weilQ_eq', hn (φ j)]; ring
    simp_rw [e]
    exact hqφ.sub hnon
  obtain ⟨hint, hle⟩ := fatou_real measurableSet_Ioi
    (f := fun j => archIntegrand (hh j)) (F := archIntegrand G')
    (fun j => (hp (φ j)).arch) (fun j u hu => archIntegrand_nonneg (hmem j) hu)
    (fun u _ => by
      unfold archIntegrand
      exact ((hauto 0).sub (hauto u)).mul_const _) hA
  have hPG : Probe a G' := ⟨symCut_even a G, hsuppG', hG', hint⟩
  refine ⟨hPG, hnormG, ?_, hlim'⟩
  rw [← weilQ_mono ha.le haa₁ hPG, weilQ_eq', hnormG]
  have : archE G' ≤ L - nA (poleR G' a₁) (primeS G') := hle
  simp only [hnA] at this
  linarith

theorem lam_nonempty {a : ℝ} (ha : 0 < a) :
    {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ weilQ a h = q}.Nonempty :=
  ⟨_, box a, box_probe a, normSq_box ha, rfl⟩

/-- **Right-continuity of `λ₁`.** -/
theorem lam_right {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b, a ≤ b → b < a + δ → lam a - ε < lam b := by
  by_contra H
  push Not at H
  choose b hab hbδ hbl using fun n : ℕ => H (1 / ((n : ℝ) + 1)) (by positivity)
  set a₁ := a + 1 with ha₁
  have ha₁0 : 0 < a₁ := by linarith
  have hb1 : ∀ n, b n ≤ a₁ := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [hbδ n]
  have hb0 : ∀ n, 0 < b n := fun n => ha.trans_le (hab n)
  have hbt : Tendsto b atTop (𝓝 a) := by
    have hu : Tendsto (fun n : ℕ => a + 1 / ((n : ℝ) + 1)) atTop (𝓝 a) := by
      have := (tendsto_const_nhds (x := a)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu hab fun n => (hbδ n).le
  have hnear : ∀ n, ∃ g, Probe (b n) g ∧ normSq g = 1 ∧ weilQ (b n) g < lam (b n) + ε / 2 := by
    intro n
    obtain ⟨q, ⟨g, hp, hn, rfl⟩, hq⟩ :=
      exists_lt_of_csInf_lt (lam_nonempty (hb0 n)) (by linarith : lam (b n) < lam (b n) + ε / 2)
    exact ⟨g, hp, hn, hq⟩
  choose g hgp hgn hgq using hnear
  have hQ1 : ∀ n, weilQ a₁ (g n) = weilQ (b n) (g n) := fun n =>
    weilQ_mono (hb0 n).le (hb1 n) (hgp n)
  set F₁ := weilConst - 2 * primeWeight a₁ with hF₁
  have hqI : ∀ n, weilQ a₁ (g n) ∈ Icc F₁ (lam a - ε / 2) := fun n =>
    ⟨by have := weilQ_ge ((hgp n).mono (hb1 n)); rwa [hgn n, mul_one] at this,
      by rw [hQ1 n]; linarith [hgq n, hbl n]⟩
  obtain ⟨L, hLI, φ, hφ, hqφ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc F₁ (lam a - ε / 2)) hqI
  rw [closure_Icc] at hLI
  obtain ⟨-, -, G, hPG, hnG, hQG, -⟩ := lsc_even ha (fun n => hab (φ n)) (fun n => hb1 (φ n))
    (hbt.comp hφ.tendsto_atTop) (fun n => hgp (φ n)) (fun n => hgn (φ n)) hqφ
  have := lam_le hPG hnG
  linarith [hLI.2]

/-- **Left-continuity of `λ₁`** (dilation). -/
theorem lam_left {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b, a - δ < b → b ≤ a → lam b < lam a + ε := by
  obtain ⟨q, ⟨o, hp, hn, rfl⟩, hq⟩ :=
    exists_lt_of_csInf_lt (lam_nonempty ha) (by linarith : lam a < lam a + ε / 2)
  have hev0 : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), s ∈ Icc (1 : ℝ) 2 := self_mem_nhdsWithin
  have hT : Tendsto (fun s => weilQ a (dil s o)) (𝓝[Icc 1 2] 1) (𝓝 (weilQ a o)) := by
    have hlim := ((((tendsto_pole_dil ha hp.toS).pow 2).const_mul 2).add
      (tendsto_const_nhds (x := weilConst * normSq o))).add (tendsto_archE_dilS hp.toS) |>.sub
      ((tendsto_primeS_dil ha hp.toS).const_mul 2)
    rw [weilQ_eq']
    refine hlim.congr' (hev0.mono fun s hs => ?_)
    have hs0 : 0 < s := by linarith [hs.1]
    dsimp only
    rw [weilQ_eq', normSq_dilS hs0]
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), weilQ a (dil s o) < lam a + ε :=
    hT.eventually (gt_mem_nhds (by linarith))
  obtain ⟨U, hUo, h1U, hUs⟩ := mem_nhdsWithin.1 hev
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hUo 1 h1U
  set s₀ := 1 + min (η / 2) 1 with hs₀
  have hs₀1 : 1 < s₀ := by have := lt_min (half_pos hη) one_pos; linarith
  refine ⟨a - a / s₀, sub_pos.2 (div_lt_self ha hs₀1), fun b hb hba => ?_⟩
  have hb0 : 0 < b := by
    have : 0 < a / s₀ := by positivity
    linarith
  set s := a / b with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, le_div_iff₀ hb0]; linarith
  have hss₀ : s ≤ s₀ := by
    rw [hsdef, div_le_iff₀ hb0]
    have : a / s₀ < b := by linarith
    rw [div_lt_iff₀ (by linarith)] at this; linarith
  have hs2 : s ≤ 2 := hss₀.trans (by linarith [min_le_right (η / 2) 1])
  have hsU : s ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith [min_le_left (η / 2) 1])
  have hQ : weilQ a (dil s o) < lam a + ε := hUs ⟨hsU, hs1, hs2⟩
  have hbs : a / s = b := by rw [hsdef]; field_simp
  have hpb : Probe b (dil s o) :=
    hbs ▸ ⟨fun u => by unfold dil; rw [show s * -u = -(s * u) by ring, hp.even],
      dil_supp (by linarith) hp.supp, memLp_dilS (by linarith) hp.memL2, arch_dil hp.toS hs1 hs2⟩
  have hnb : normSq (dil s o) = 1 := by rw [normSq_dilS (by linarith), hn]
  have := lam_le hpb hnb
  rw [← weilQ_mono hb0.le hba hpb] at this
  linarith

/-- **`λ₁` is continuous on `(0, ∞)`.** -/
theorem continuousOn_lam : ContinuousOn lam (Ioi 0) := by
  intro a ha
  have ha : 0 < a := ha
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, h₁⟩ := lam_right ha hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := lam_left ha hε
  refine ⟨min δ₁ (min δ₂ a), by positivity, fun {b} hb hd => ?_⟩
  have hb0 : 0 < b := hb
  rw [Real.dist_eq, abs_lt] at hd ⊢
  have hm1 := min_le_left δ₁ (min δ₂ a)
  have hm2 := (min_le_right δ₁ (min δ₂ a)).trans (min_le_left δ₂ a)
  rcases le_total a b with hab | hba
  · have := h₁ b hab (by linarith [hd.2])
    have := lam_antitone ha hab
    constructor <;> linarith
  · have := h₂ b (by linarith [hd.1]) hba
    have := lam_antitone hb0 hba
    constructor <;> linarith

/-! ## S2: degeneracy -/

/-- **Degeneracy**: two orthonormal ground states. -/
def Degenerate (a : ℝ) : Prop :=
  ∃ g h, IsGroundState a g ∧ IsGroundState a h ∧ xcorr g h 0 = 0

theorem isGroundState_of_le {a : ℝ} {G : ℝ → ℝ} (hp : Probe a G) (hn : normSq G = 1)
    (hle : weilQ a G ≤ lam a) : IsGroundState a G :=
  ⟨hp, hn, fun _ hh hnh => hle.trans (lam_le hh hnh)⟩

/-- A non-simple ground state gives an orthonormal pair of ground states (Gram–Schmidt). -/
theorem degenerate_of_not_simple {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hns : ¬ SimpleGround a g) : Degenerate a := by
  have hgm : g ∈ groundSpace a := ((isGroundState_iff ha).1 hg).1
  obtain ⟨h, hh, hnot⟩ : ∃ h ∈ groundSpace a, ∀ c : ℝ, ¬ h =ᵐ[volume] fun t => c * g t := by
    by_contra H
    push Not at H
    exact hns ⟨hg, H⟩
  have hp : Probe a h := hh.1
  set c := xcorr h g 0 with hc
  set h' : ℝ → ℝ := fun t => h t + (-c) * g t with hh'
  have hmem' : h' ∈ groundSpace a := by
    have := (groundSpace a).add_mem hh ((groundSpace a).smul_mem (-c) hgm)
    convert this using 1
  have hp' : Probe a h' := hmem'.1
  have n0 := normSq_add_smul hp.memL2 hg.1.memL2 (-c)
  have n1 := normSq_add_smul hp'.memL2 hg.1.memL2 1
  have n2 := normSq_add_smul hp.memL2 hg.1.memL2 (1 - c)
  have eqf : (fun t => h' t + 1 * g t) = fun t => h t + (1 - c) * g t := by
    funext t; simp only [hh']; ring
  rw [eqf, n2] at n1
  rw [← hh'] at n0
  have hgn := hg.2.1
  have hx' : xcorr h' g 0 = 0 := by
    rw [hgn] at n0 n1; rw [← hc] at n0 n1
    linear_combination (-(1 : ℝ) / 2) * n1 + (-(1 : ℝ) / 2) * n0
  have h0 : normSq h' ≠ 0 := by
    intro h0
    apply hnot c
    filter_upwards [ae_zero_of_normSq hp'.memL2 h0] with t ht
    have : h t + (-c) * g t = 0 := by simpa [hh'] using ht
    linarith
  have hpos : 0 < normSq h' := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
  set k := (Real.sqrt (normSq h'))⁻¹
  have hk : k ^ 2 * normSq h' = 1 := by
    simp only [k, inv_pow, Real.sq_sqrt hpos.le]; exact inv_mul_cancel₀ h0
  refine ⟨g, fun t => k * h' t, hg, (isGroundState_iff ha).2 ⟨groundSpace_fun hmem' k, ?_⟩, ?_⟩
  · rw [normSq_smul]; exact hk
  · rw [xcorr_zero_eq]
    have : (fun t => g t * (k * h' t)) = fun t => k * (h' t * g t) := by funext t; ring
    rw [this, integral_const_mul, ← xcorr_zero_eq, hx', mul_zero]

/-- A degenerate support has no simple ground state. -/
theorem not_simple_of_degenerate {a : ℝ} (ha : 0 < a) (hd : Degenerate a) {g : ℝ → ℝ}
    (hg : IsGroundState a g) : ¬ SimpleGround a g := by
  rintro ⟨-, hs⟩
  obtain ⟨g₁, h₁, hg₁, hh₁, hx⟩ := hd
  obtain ⟨c₁, e₁⟩ := hs g₁ ((isGroundState_iff ha).1 hg₁).1
  obtain ⟨c₂, e₂⟩ := hs h₁ ((isGroundState_iff ha).1 hh₁).1
  have hn1 : normSq g₁ = c₁ ^ 2 := by
    rw [normSq_congr_ae e₁, normSq_smul, hg.2.1, mul_one]
  have hn2 : normSq h₁ = c₂ ^ 2 := by
    rw [normSq_congr_ae e₂, normSq_smul, hg.2.1, mul_one]
  have hx' : xcorr g₁ h₁ 0 = c₁ * c₂ := by
    rw [xcorr_zero_eq]
    have : (fun t => g₁ t * h₁ t) =ᵐ[volume] fun t => (c₁ * c₂) * (g t * g t) := by
      filter_upwards [e₁, e₂] with t h1 h2; rw [h1, h2]; ring
    rw [integral_congr_ae this, integral_const_mul, ← normSq_eq_mul, hg.2.1, mul_one]
  rw [hg₁.2.1] at hn1; rw [hh₁.2.1] at hn2
  rw [hx'] at hx
  rcases mul_eq_zero.1 hx with h | h
  · rw [h] at hn1; norm_num at hn1
  · rw [h] at hn2; norm_num at hn2

theorem degenerate_iff {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g) :
    Degenerate a ↔ ¬ SimpleGround a g :=
  ⟨fun hd => not_simple_of_degenerate ha hd hg, degenerate_of_not_simple ha hg⟩

/-- **Degeneracy is closed**: if `bₙ → a > 0` and every `bₙ` is degenerate, so is `a`. -/
theorem degenerate_of_tendsto {a : ℝ} (ha : 0 < a) {b : ℕ → ℝ} (hbt : Tendsto b atTop (𝓝 a))
    (hd : ∀ n, Degenerate (b n)) : Degenerate a := by
  -- pass to a tail with `a/2 < bₙ < a + 1`
  obtain ⟨N, hN⟩ := (hbt.eventually (Ioo_mem_nhds (by linarith : a / 2 < a)
    (by linarith : a < a + 1))).exists_forall_of_atTop
  set b' : ℕ → ℝ := fun n => b (n + N) with hb'
  have hb't : Tendsto b' atTop (𝓝 a) := hbt.comp (tendsto_add_atTop_nat N)
  have hbI : ∀ n, b' n ∈ Ioo (a / 2) (a + 1) := fun n => hN _ (by omega)
  have hb'0 : ∀ n, 0 < b' n := fun n => by linarith [(hbI n).1]
  choose g h hg hh hx using fun n => hd (n + N)
  set c : ℕ → ℝ := fun n => max (b' n) a with hcdef
  have hc : ∀ n, a ≤ c n := fun n => le_max_right _ _
  have hc1 : ∀ n, c n ≤ a + 1 := fun n => max_le (hbI n).2.le (by linarith)
  have hct : Tendsto c atTop (𝓝 a) := by
    have := hb't.max (tendsto_const_nhds (x := a)); simpa [hcdef] using this
  have hpc : ∀ n, Probe (c n) (g n) := fun n => (hg n).1.mono (le_max_left _ _)
  have hqc : ∀ n, Probe (c n) (h n) := fun n => (hh n).1.mono (le_max_left _ _)
  -- energies converge to `λ₁(a)`
  have hlam : Tendsto (fun n => lam (b' n)) atTop (𝓝 (lam a)) := by
    have hw : Tendsto b' atTop (𝓝[Ioi 0] a) :=
      tendsto_nhdsWithin_iff.2 ⟨hb't, Eventually.of_forall hb'0⟩
    exact (continuousOn_lam a ha).tendsto.comp hw
  have hQg : ∀ n, weilQ (a + 1) (g n) = lam (b' n) := fun n => by
    rw [weilQ_mono (hb'0 n).le (hbI n).2.le (hg n).1, weilQ_eq_lam (hb'0 n) (hg n)]
  have hQh : ∀ n, weilQ (a + 1) (h n) = lam (b' n) := fun n => by
    rw [weilQ_mono (hb'0 n).le (hbI n).2.le (hh n).1, weilQ_eq_lam (hb'0 n) (hh n)]
  obtain ⟨φ, hφ, G, hPG, hnG, hQG, hlimG⟩ := lsc_even ha hc hc1 hct hpc (fun n => (hg n).2.1)
    (hlam.congr fun n => (hQg n).symm)
  obtain ⟨ψ, hψ, H, hPH, hnH, hQH, hlimH⟩ := lsc_even ha (fun n => hc (φ n)) (fun n => hc1 (φ n))
    (hct.comp hφ.tendsto_atTop) (fun n => hqc (φ n)) (fun n => (hh (φ n)).2.1)
    ((hlam.comp hφ.tendsto_atTop).congr fun n => (hQh (φ n)).symm)
  refine ⟨G, H, isGroundState_of_le hPG hnG hQG, isGroundState_of_le hPH hnH hQH, ?_⟩
  -- orthogonality passes to the limit
  have hmg : ∀ j, MemLp (g (φ (ψ j))) 2 volume := fun j => (hg _).1.memL2
  have hmh : ∀ j, MemLp (h (φ (ψ j))) 2 volume := fun j => (hh _).1.memL2
  have hT := tendsto_integral_mul hmg hmh hPG.memL2 hPH.memL2 (hlimG.comp hψ.tendsto_atTop) hlimH
  simp_rw [← xcorr_zero_eq] at hT
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr fun j => (hx _).symm)

/-! ## S3: the first degeneracy -/

/-- **The first degeneracy.** If `a₀ > 0` is not degenerate but some `a₁ ≥ a₀` is, there is a least
degenerate support `m ∈ (a₀, a₁]`: every support in `[a₀, m)` is non-degenerate, and at `m` the ground
space contains a nonzero pole-free `w` with its Green solution `G w` (Theorem D). -/
theorem first_degeneracy {a₀ a₁ : ℝ} (h0 : 0 < a₀) (hs0 : ¬ Degenerate a₀) (h01 : a₀ ≤ a₁)
    (hd : Degenerate a₁) :
    ∃ m, a₀ < m ∧ m ≤ a₁ ∧ Degenerate m ∧ (∀ a, a₀ ≤ a → a < m → ¬ Degenerate a) ∧
      ∃ w, w ∈ groundSpace m ∧ poleR w m = 0 ∧ 0 < normSq w ∧ Gpole w m ∈ groundSpace m := by
  set V := {b | b ∈ Icc a₀ a₁ ∧ Degenerate b} with hV
  have hne : V.Nonempty := ⟨a₁, ⟨h01, le_rfl⟩, hd⟩
  have hbdd : BddBelow V := ⟨a₀, fun b hb => hb.1.1⟩
  set m := sInf V with hm
  have ha₀m : a₀ ≤ m := le_csInf hne fun b hb => hb.1.1
  have hm0 : 0 < m := h0.trans_le ha₀m
  obtain ⟨u, -, hut, huV⟩ := exists_seq_tendsto_sInf hne hbdd
  have hdm : Degenerate m := degenerate_of_tendsto hm0 hut fun n => (huV n).2
  have hmne : a₀ ≠ m := fun e => hs0 (e ▸ hdm)
  refine ⟨m, lt_of_le_of_ne ha₀m hmne, csInf_le hbdd ⟨⟨h01, le_rfl⟩, hd⟩, hdm,
    fun a ha hlt hda => ?_, ?_⟩
  · have : m ≤ a := csInf_le hbdd ⟨⟨ha, hlt.le.trans (csInf_le hbdd ⟨⟨h01, le_rfl⟩, hd⟩)⟩, hda⟩
    linarith
  · obtain ⟨g, hg⟩ := exists_groundState hm0
    obtain ⟨w, hw, hwp, hpos, hG⟩ := degenerate_flat hm0 hg (not_simple_of_degenerate hm0 hdm hg)
    exact ⟨w, hw, hwp, hpos, hG⟩

/-- **Simplicity route, with its start discharged.** If some support `a₁ ≥ 0.36` is degenerate, there
is a least one `m ∈ (0.36, a₁]`, preceded by non-degenerate supports on `[0.36, m)` and carrying a
Green pair at `m`. -/
theorem first_degeneracy_036 {a₁ : ℝ} (h01 : 0.36 ≤ a₁) (hd : Degenerate a₁) :
    ∃ m, 0.36 < m ∧ m ≤ a₁ ∧ Degenerate m ∧ (∀ a, 0.36 ≤ a → a < m → ¬ Degenerate a) ∧
      ∃ w, w ∈ groundSpace m ∧ poleR w m = 0 ∧ 0 < normSq w ∧ Gpole w m ∈ groundSpace m := by
  have h0 : (0 : ℝ) < 0.36 := by norm_num
  have hs0 : ¬ Degenerate 0.36 := by
    intro hd0
    obtain ⟨g, hg⟩ := exists_groundState h0
    exact not_simple_of_degenerate h0 hd0 hg (simpleGround_036 h0 le_rfl hg)
  exact first_degeneracy h0 hs0 h01 hd

/-! ## S4: the secular reduction, completed

Rounds 49–50 (`GapCriterion.lean`) proved interlacing (`lam_le_of_perp`), the gap criterion
(`simpleGround_of_gap`) and `not_simple_gap`: without simplicity, `λ₁(Q) = min_{φ₀^⊥} Q₀`, attained.
The two missing links: the attaining function is automatically pole-free, hence a ground state of `Q`
and an eigenfunction of `Q₀` at level `λ₁`; and, when the ground state has a nonzero pole value, this
is an exact characterisation of non-simplicity. -/

/-- **A `φ₀^⊥` minimiser at level `λ₁(Q)` is pole-free.** From the pole-free trial
`λ₁(1 + r²) ≤ Q₀(v) + r²λ₀` with `Q₀(v) = λ₁` and `λ₀ < λ₁`, the ratio `r = v̂(i/2)/φ̂₀(i/2)` vanishes. -/
theorem poleR_zero_of_perp_min {a : ℝ} (ha : 0 < a) {φ v : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hφp : poleR φ a ≠ 0) (hv : Probe a v) (hn : normSq v = 1) (hx : xcorr v φ 0 = 0)
    (hq : weilQ0 a v = lam a) : poleR v a = 0 := by
  have h := lam_le_perp_trial ha hφ hφp hv hn hx
  have hlt := lam0_lt_lam ha
  rw [hq] at h
  set r := poleR v a / poleR φ a with hr
  have hr2 : r ^ 2 * (lam a - lam0 a) ≤ 0 := by nlinarith
  have hr0 : r ^ 2 = 0 :=
    le_antisymm (by
      by_contra hc; push Not at hc
      have := mul_pos hc (sub_pos.2 hlt); linarith) (sq_nonneg r)
  have : r = 0 := pow_eq_zero_iff two_ne_zero |>.1 hr0
  exact (div_eq_zero_iff.1 this).resolve_right hφp

/-- **The secular reduction.** If the ground state is not simple, then with `φ₀ ≥ 0` the (positive-pole)
ground state of `Q₀` there is a normalised `w ⊥ φ₀` that is
* pole-free (`ŵ(i/2) = 0`),
* a ground state of `Q`,
* an eigenfunction of `Q₀` at level `λ₁(Q)`: `B₀(w, ψ) = λ₁⟨w, ψ⟩` for every probe `ψ`,
and `λ₁(Q) = Q₀(w) = min_{φ₀^⊥} Q₀`, i.e. `λ₁(Q) = μ₂(Q₀)`, attained by a pole-free eigenfunction. -/
theorem secular_of_not_simple {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hns : ¬ SimpleGround a g) :
    ∃ φ, IsGroundState0 a φ ∧ (∀ t, 0 ≤ φ t) ∧ 0 < poleR φ a ∧
      (∃ w, IsGroundState a w ∧ poleR w a = 0 ∧ xcorr w φ 0 = 0 ∧ weilQ0 a w = lam a ∧
        ∀ ψ, Probe a ψ → bil0 a w ψ = lam a * xcorr w ψ 0) ∧
      ∀ ψ, Probe a ψ → normSq ψ = 1 → xcorr ψ φ 0 = 0 → lam a ≤ weilQ0 a ψ := by
  obtain ⟨φ, hφ, h0, hpos, ⟨v, hv, hn, hx, hq⟩, hmin⟩ := not_simple_gap ha hg hns
  have hvp := poleR_zero_of_perp_min ha hφ hpos.ne' hv hn hx hq
  have hQ : weilQ a v = lam a := by unfold weilQ0 at hq; rw [hvp] at hq; linarith
  have hvg : IsGroundState a v := isGroundState_of_le hv hn hQ.le
  refine ⟨φ, hφ, h0, hpos, ⟨v, hvg, hvp, hx, hq, fun ψ hψ => ?_⟩, hmin⟩
  have el := euler_lagrange_mem ((isGroundState_iff ha).1 hvg).1 hψ
  rwa [hvp, mul_zero, zero_mul, add_zero] at el

/-- **The exact secular characterisation.** For a ground state `g` with nonzero pole value, `g` fails to
be simple iff some normalised `w ⊥ φ₀` has `Q₀(w) = λ₁(Q)` — i.e. iff `μ₂(Q₀)` comes down to `λ₁(Q)`
and is attained on `φ₀^⊥`. -/
theorem not_simple_iff_secular {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : IsGroundState a g)
    (hgp : poleR g a ≠ 0) :
    ¬ SimpleGround a g ↔ ∃ φ, IsGroundState0 a φ ∧ 0 < poleR φ a ∧
      ∃ w, Probe a w ∧ normSq w = 1 ∧ xcorr w φ 0 = 0 ∧ weilQ0 a w = lam a := by
  constructor
  · intro hns
    obtain ⟨φ, hφ, -, hpos, ⟨w, hwg, -, hx, hq, -⟩, -⟩ := secular_of_not_simple ha hg hns
    exact ⟨φ, hφ, hpos, w, hwg.1, hwg.2.1, hx, hq⟩
  · rintro ⟨φ, hφ, hpos, w, hw, hn, hx, hq⟩ ⟨-, hs⟩
    have hwp := poleR_zero_of_perp_min ha hφ hpos.ne' hw hn hx hq
    have hQ : weilQ a w = lam a := by unfold weilQ0 at hq; rw [hwp] at hq; linarith
    have hwg : IsGroundState a w := isGroundState_of_le hw hn hQ.le
    obtain ⟨c, hc⟩ := hs w ((isGroundState_iff ha).1 hwg).1
    have hpc : poleR w a = c * poleR g a := by rw [poleR_congr_ae hc, poleR_smul]
    rw [hwp] at hpc
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 hpc.symm with h | h
      · exact h
      · exact absurd h hgp
    have : normSq w = 0 := by
      rw [normSq_congr_ae hc, hc0]; simp [normSq]
    linarith

end Pilot1ca

#print axioms Pilot1ca.lsc_even
#print axioms Pilot1ca.continuousOn_lam
#print axioms Pilot1ca.degenerate_iff
#print axioms Pilot1ca.degenerate_of_tendsto
#print axioms Pilot1ca.first_degeneracy
#print axioms Pilot1ca.first_degeneracy_036
#print axioms Pilot1ca.poleR_zero_of_perp_min
#print axioms Pilot1ca.secular_of_not_simple
#print axioms Pilot1ca.not_simple_iff_secular
