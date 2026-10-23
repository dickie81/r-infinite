import Mathlib
import ParityGap
import SimpleCover

/-! # Round 146: the parity gap by continuation in the support

`lamO a` is the odd ground energy, the infimum of Weil's form over normalised odd probes at
half-support `a`. The even ground energy `lam` and `lamO` are both nonincreasing in `a`.

* **C1 (the continuation lemma).** If `lamO` is continuous on `[a₀, a₁]`, `lam a₀ < lamO a₀`, and the
  two energies never coincide on `[a₀, a₁]`, then `lam a < lamO a` throughout, hence `ParityGap a`.
  Only `lamO` needs to be continuous: `lam` is antitone, and that is the direction both halves of the
  argument need.
* **C2 (right-continuity of `lamO`).** Near-minimisers at `aₙ ↓ a` are precompact in `L²`
  (`exists_convergent_subseq_S`). Their mass in the shell `a < |t| ≤ aₙ` tends to `0`, so the odd cut
  of the limit is an odd probe at `a`, and lower semicontinuity (Fatou) bounds its energy.
* **C3 (left-continuity of `lamO`).** Dilation `o_s(t) = √s·o(st)` maps odd probes at `a` to odd probes
  at `a/s` with the same norm, and `Q(o_s) → Q(o)` as `s → 1⁺`.

So the eventual parity gap is *equivalent* to: no crossing `lam a = lamO a` beyond a certified `a₀`.
No zero of `ζ` enters.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## The odd ground energy -/

theorem abs_primeS_le_S {a : ℝ} {g : ℝ → ℝ} (hp : SProbe a g) :
    |primeS g| ≤ primeWeight a * normSq g := by
  unfold primeS
  rw [prime_sum_eq hp.supp, primeWeight, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_autocorr_le hp.memL2 _) hc

/-- **An `a`-dependent floor for the odd sector**: `Q(o) ≥ ψ(¼) − log π − 2P(a) − 2(sinh a − a)`. -/
theorem weilQg_odd_ge {a : ℝ} (ha : 0 < a) {o : ℝ → ℝ} (hp : OProbe a o) (hn : normSq o = 1) :
    weilConst - 2 * primeWeight a - 2 * (Real.sinh a - a) ≤ weilQg a o := by
  have h1 := poleR_sq_odd ha hp hn
  have h2 := (le_abs_self _).trans (abs_primeS_le_S hp.toS)
  have h3 := archE_nonneg_S hp.toS
  rw [hn, mul_one] at h2
  rw [weilQg, poleL_odd hp, hn]
  nlinarith

/-- The normalised odd ground energy `λ_odd(a) = inf {Q(o) : o an odd probe, ‖o‖ = 1}`. -/
def lamO (a : ℝ) : ℝ := sInf {q | ∃ o, OProbe a o ∧ normSq o = 1 ∧ weilQg a o = q}

theorem lamO_bdd {a : ℝ} (ha : 0 < a) :
    BddBelow {q | ∃ o, OProbe a o ∧ normSq o = 1 ∧ weilQg a o = q} :=
  ⟨_, by rintro q ⟨o, hp, hn, rfl⟩; exact weilQg_odd_ge ha hp hn⟩

theorem lamO_le {a : ℝ} (ha : 0 < a) {o : ℝ → ℝ} (hp : OProbe a o) (hn : normSq o = 1) :
    lamO a ≤ weilQg a o :=
  csInf_le (lamO_bdd ha) ⟨o, hp, hn, rfl⟩

/-! ### An odd probe at every support -/

/-- The quarter box moved to `[a/4, 3a/4]`; it and its reflection have disjoint supports. -/
def qbox (a : ℝ) (t : ℝ) : ℝ := box (a / 4) (t - a / 2)

theorem qbox_supp {a : ℝ} {t : ℝ} (ht : qbox a t ≠ 0) : a / 4 ≤ t ∧ t ≤ 3 * a / 4 := by
  unfold qbox at ht; rw [box_apply] at ht
  split_ifs at ht with h
  · rw [abs_le] at h; constructor <;> linarith [h.1, h.2]
  · exact absurd rfl ht

theorem qbox_mul_reflect {a : ℝ} (ha : 0 < a) (t : ℝ) : qbox a t * qbox a (-t) = 0 := by
  by_contra h
  have h1 := qbox_supp (left_ne_zero_of_mul h)
  have h2 := qbox_supp (right_ne_zero_of_mul h)
  linarith [h1.1, h2.1]

theorem qbox_sprobe {a : ℝ} (ha : 0 < a) : SProbe a (qbox a) := by
  have hb := box_probe (a / 4)
  refine ⟨fun u hu => ?_, ?_, ?_⟩
  · by_contra h
    have := qbox_supp h
    rcases lt_abs.1 hu with hu | hu <;> linarith [this.1, this.2]
  · have := hb.memL2.comp_measurePreserving (measurePreserving_add_right volume (-(a / 2)))
    convert this using 1; funext t; simp [qbox, sub_eq_add_neg]
  · have e : archIntegrand (qbox a) = archIntegrand (box (a / 4)) := by
      funext u; unfold archIntegrand autocorr qbox
      have k : ∀ v, (∫ t, box (a / 4) (t - a / 2) * box (a / 4) (t + v - a / 2))
          = ∫ t, box (a / 4) t * box (a / 4) (t + v) := fun v => by
        have := integral_add_right_eq_self (μ := volume)
          (fun t => box (a / 4) t * box (a / 4) (t + v)) (-(a / 2))
        rw [← this]; congr 1; funext t; ring_nf
      rw [k 0, k u]
    rw [e]; exact hb.arch

theorem normSq_qbox {a : ℝ} (ha : 0 < a) : normSq (qbox a) = 1 := by
  have := integral_add_right_eq_self (μ := volume) (fun t => box (a / 4) t ^ 2) (-(a / 2))
  unfold normSq qbox; simp only [sub_eq_add_neg]; rw [this]
  exact normSq_box (by positivity)

/-- **Odd probes exist at every support**: `√2 · oddPart(qbox)`. -/
theorem exists_oprobe {a : ℝ} (ha : 0 < a) : ∃ o, OProbe a o ∧ normSq o = 1 := by
  set o := oddPart (qbox a)
  have hp : OProbe a o := oprobe_oddPart (qbox_sprobe ha)
  have hn : normSq o = 1 / 2 := by
    have e : (fun t => o t ^ 2) = fun t => (qbox a t ^ 2 + qbox a (-t) ^ 2) / 4 := by
      funext t; simp only [o, oddPart]
      have := qbox_mul_reflect ha t
      nlinarith [this]
    have hm := (qbox_sprobe ha).memL2
    have i1 : Integrable (fun t => qbox a t ^ 2) := hm.integrable_sq
    have i2 : Integrable (fun t => qbox a (-t) ^ 2) := (memLp_neg hm).integrable_sq
    unfold normSq; rw [e, integral_div, integral_add i1 i2, integral_neg_eq_self (fun t => qbox a t ^ 2)]
    have := normSq_qbox ha; unfold normSq at this; rw [this]; norm_num
  refine ⟨fun t => Real.sqrt 2 * o t, hp.smul _, ?_⟩
  rw [normSq_smul, hn, Real.sq_sqrt (by norm_num)]; norm_num

theorem lamO_nonempty {a : ℝ} (ha : 0 < a) :
    {q | ∃ o, OProbe a o ∧ normSq o = 1 ∧ weilQg a o = q}.Nonempty := by
  obtain ⟨o, hp, hn⟩ := exists_oprobe ha
  exact ⟨_, o, hp, hn, rfl⟩

/-- **`λ_odd` is nonincreasing in the support.** -/
theorem lamO_antitone {a a₁ : ℝ} (ha : 0 < a) (h : a ≤ a₁) : lamO a₁ ≤ lamO a := by
  refine le_csInf (lamO_nonempty ha) ?_
  rintro q ⟨o, hp, hn, rfl⟩
  rw [← weilQg_mono ha.le h hp.supp]
  exact lamO_le (ha.trans_le h) (hp.mono h) hn

/-- `lam a < lamO a` gives the parity gap of round 137. -/
theorem parityGap_of_lt {a : ℝ} (ha : 0 < a) (h : lam a < lamO a) : ParityGap a :=
  fun _ hp hn => h.trans_le (lamO_le ha hp hn)

/-! ## C1: the continuation lemma -/

/-- **The continuation lemma.** If `λ_odd` is continuous on `[a₀, a₁]`, the gap holds at `a₀`, and the
two ground energies never coincide on `[a₀, a₁]`, the gap holds on all of `[a₀, a₁]`. -/
theorem gap_of_no_crossing {a₀ a₁ : ℝ} (h0 : 0 < a₀) (hgap : lam a₀ < lamO a₀)
    (hcont : ContinuousOn lamO (Icc a₀ a₁)) (hnc : ∀ a ∈ Icc a₀ a₁, lam a ≠ lamO a) :
    ∀ a ∈ Icc a₀ a₁, lam a < lamO a := by
  by_contra hne
  push Not at hne
  obtain ⟨a, ha, hle⟩ := hne
  set V := {b | b ∈ Icc a₀ a₁ ∧ lamO b < lam b} with hV
  have haV : a ∈ V := ⟨ha, lt_of_le_of_ne hle (fun e => hnc a ha e.symm)⟩
  have hbdd : BddBelow V := ⟨a₀, fun b hb => hb.1.1⟩
  set m := sInf V with hm
  have hmV : m ≤ a := csInf_le hbdd haV
  have ha₀m : a₀ ≤ m := le_csInf ⟨a, haV⟩ fun b hb => hb.1.1
  have hmI : m ∈ Icc a₀ a₁ := ⟨ha₀m, hmV.trans ha.2⟩
  have hm0 : 0 < m := h0.trans_le ha₀m
  rcases lt_or_gt_of_ne (hnc m hmI) with hlt | hgt
  · -- the gap holds at `m`: it persists to the right, so `V` starts beyond `m`
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousOn_iff.1 hcont m hmI (lamO m - lam m) (by linarith)
    have : m + δ ≤ m := by
      refine le_csInf ⟨a, haV⟩ fun b hb => ?_
      by_contra hbδ; push Not at hbδ
      have hmb : m ≤ b := csInf_le hbdd hb
      have hd : dist b m < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have h1 := hball b hb.1 hd
      rw [Real.dist_eq, abs_lt] at h1
      have h2 := lam_antitone hm0 hmb
      linarith [hb.2, h1.1]
    linarith
  · -- the gap fails at `m`: it fails slightly to the left too
    have hm₀ : a₀ < m := by
      rcases ha₀m.lt_or_eq with h | h
      · exact h
      · rw [← h] at hgt; linarith
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousOn_iff.1 hcont m hmI (lam m - lamO m) (by linarith)
    set b := max a₀ (m - δ / 2)
    have hbm : b < m := max_lt hm₀ (by linarith)
    have hbI : b ∈ Icc a₀ a₁ := ⟨le_max_left _ _, hbm.le.trans hmI.2⟩
    have hd : dist b m < δ := by
      rw [Real.dist_eq, abs_lt]; constructor
      · linarith [le_max_right a₀ (m - δ / 2)]
      · linarith
    have h1 := hball b hbI hd
    rw [Real.dist_eq, abs_lt] at h1
    have h2 := lam_antitone (h0.trans_le hbI.1) hbm.le
    have hbV : b ∈ V := ⟨hbI, by linarith [h1.2]⟩
    linarith [csInf_le hbdd hbV]

/-- The continuation lemma on a half-line. -/
theorem gap_of_no_crossing_Ici {a₀ : ℝ} (h0 : 0 < a₀) (hgap : lam a₀ < lamO a₀)
    (hcont : ContinuousOn lamO (Ici a₀)) (hnc : ∀ a, a₀ ≤ a → lam a ≠ lamO a) :
    ∀ a, a₀ ≤ a → ParityGap a := fun a ha =>
  parityGap_of_lt (h0.trans_le ha)
    (gap_of_no_crossing h0 hgap (hcont.mono Icc_subset_Ici_self) (fun b hb => hnc b hb.1) a ⟨ha, le_rfl⟩)

/-! ## C2: right-continuity of `λ_odd` -/

/-- `A f (u) = 1_{|u| ≤ a}·(f(u) − f(−u))/2`: antisymmetrise and cut off. -/
def antiCut (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := if |u| ≤ a then (f u - f (-u)) / 2 else 0

theorem antiCut_odd (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : antiCut a f (-u) = -antiCut a f u := by
  unfold antiCut; rw [abs_neg, neg_neg]; split_ifs <;> ring

theorem antiCut_supp (a : ℝ) (f : ℝ → ℝ) (u : ℝ) (hu : a < |u|) : antiCut a f u = 0 := by
  unfold antiCut; simp [not_le.2 hu]

theorem memLp_antiCut (a : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (antiCut a f) 2 volume := by
  have h1 : MemLp (fun u => (f u - f (-u)) / 2) 2 volume := by
    have := (hf.sub (memLp_neg hf)).const_mul (1 / 2 : ℝ)
    convert this using 1
    funext u; simp only [Pi.sub_apply]; ring
  have : antiCut a f = Set.indicator {u | |u| ≤ a} (fun u => (f u - f (-u)) / 2) := by
    funext u; unfold antiCut; simp [Set.indicator_apply]
  rw [this]
  exact h1.indicator (measurableSet_le continuous_abs.measurable measurable_const).nullMeasurableSet

theorem normSq_antiCut_le (a : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    normSq (antiCut a f) ≤ normSq f := by
  have hI := hf.integrable_sq
  have hJ : Integrable (fun t => f (-t) ^ 2) := (memLp_neg hf).integrable_sq
  have hK : Integrable (fun t => (f t ^ 2 + f (-t) ^ 2) / 2) := (hI.add hJ).div_const 2
  unfold normSq
  calc (∫ t, antiCut a f t ^ 2) ≤ ∫ t, (f t ^ 2 + f (-t) ^ 2) / 2 := by
        refine integral_mono (memLp_antiCut a hf).integrable_sq hK fun t => ?_
        unfold antiCut
        split_ifs
        · nlinarith [sq_nonneg (f t + f (-t))]
        · nlinarith [sq_nonneg (f t), sq_nonneg (f (-t))]
    _ = ∫ t, f t ^ 2 := by
        rw [integral_div, integral_add hI hJ, integral_neg_eq_self (fun t => f t ^ 2)]
        ring

theorem antiCut_sub (a : ℝ) (f g : ℝ → ℝ) :
    antiCut a (fun t => f t - g t) = fun t => antiCut a f t - antiCut a g t := by
  funext u; unfold antiCut; split_ifs <;> ring

theorem antiCut_oprobe {b : ℝ} {o : ℝ → ℝ} (hp : OProbe b o) (a : ℝ) (u : ℝ) :
    o u - antiCut a o u = if |u| ≤ a then 0 else o u := by
  unfold antiCut; split_ifs
  · rw [hp.odd]; ring
  · ring

/-- The mass of `G` in the shell `a < |u| ≤ b`. -/
def shellSq (G : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ u, Set.indicator {u | a < |u| ∧ |u| ≤ b} (fun u => G u ^ 2) u

theorem measurableSet_shell (a b : ℝ) : MeasurableSet {u : ℝ | a < |u| ∧ |u| ≤ b} :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

/-- **Shells shrink**: `∫_{a<|u|≤bⱼ} G² → 0` as `bⱼ → a`. -/
theorem tendsto_shellSq {G : ℝ → ℝ} (hG : MemLp G 2 volume) {a : ℝ} {b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 a)) : Tendsto (fun j => shellSq G a (b j)) atTop (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun u => G u ^ 2)
    (fun j => (hG.integrable_sq.indicator (measurableSet_shell a (b j))).aestronglyMeasurable)
    hG.integrable_sq (fun j => Eventually.of_forall fun u => ?_) (Eventually.of_forall fun u => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)]
    exact Set.indicator_le_self' (fun _ _ => sq_nonneg _) u
  · by_cases hu : a < |u|
    · have hev : ∀ᶠ j in atTop, b j < |u| := hb.eventually (gt_mem_nhds hu)
      refine tendsto_const_nhds.congr' (hev.mono fun j hj => ?_)
      dsimp only
      rw [Set.indicator_of_notMem (fun h : u ∈ {u | a < |u| ∧ |u| ≤ b j} => absurd h.2 (not_le.2 hj))]
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
      dsimp only
      rw [Set.indicator_of_notMem (fun h : u ∈ {u | a < |u| ∧ |u| ≤ b j} => hu h.1)]

/-- **The shell estimate**, for any cut `c` that is an `L²` contraction, linear, and changes `o` only
outside `[−a, a]`: for `o` supported in `[−b, b]` and any `G ∈ L²`,
`‖o − c G‖² ≤ 6‖o − G‖² + 4∫_{a<|u|≤b} G²`. -/
theorem normSq_sub_cut_le {a b : ℝ} {o G : ℝ → ℝ} (c : (ℝ → ℝ) → ℝ → ℝ)
    (hmem : ∀ f, MemLp f 2 volume → MemLp (c f) 2 volume)
    (hle : ∀ f, MemLp f 2 volume → normSq (c f) ≤ normSq f)
    (hsub : ∀ f g, c (fun t => f t - g t) = fun t => c f t - c g t)
    (hcut : ∀ u, o u - c o u = if |u| ≤ a then 0 else o u)
    (hsupp : ∀ u, b < |u| → o u = 0) (ho : MemLp o 2 volume) (hG : MemLp G 2 volume) :
    normSq (fun t => o t - c G t) ≤ 6 * normSq (fun t => o t - G t) + 4 * shellSq G a b := by
  have hoG := ho.sub hG
  set x : ℝ → ℝ := fun t => o t - c o t with hx
  set y : ℝ → ℝ := c (fun t => o t - G t) with hy
  have hxm : MemLp x 2 volume := ho.sub (hmem o ho)
  have hym : MemLp y 2 volume := hmem _ hoG
  have hsplit : (fun t => o t - c G t) = fun t => x t + y t := by
    funext t; simp only [hx, hy, hsub]; ring
  have hy2 : normSq y ≤ normSq (fun t => o t - G t) := hle _ hoG
  have hx2 : normSq x ≤ 2 * normSq (fun t => o t - G t) + 2 * shellSq G a b := by
    set ind := Set.indicator {u | a < |u| ∧ |u| ≤ b} (fun u => G u ^ 2) with hind
    have hI1 : Integrable (fun t => (o t - G t) ^ 2) := hoG.integrable_sq
    have hI2 : Integrable ind := hG.integrable_sq.indicator (measurableSet_shell a b)
    have hsum : (∫ t, (2 * (o t - G t) ^ 2 + 2 * ind t)) = 2 * normSq (fun t => o t - G t) + 2 * shellSq G a b := by
      rw [integral_add (hI1.const_mul 2) (hI2.const_mul 2), integral_const_mul, integral_const_mul]; rfl
    rw [← hsum]
    refine integral_mono hxm.integrable_sq ((hI1.const_mul 2).add (hI2.const_mul 2)) fun t => ?_
    simp only [hx, hcut t]
    have hind0 : 0 ≤ ind t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
    split_ifs with h1
    · nlinarith [sq_nonneg (o t - G t)]
    · by_cases h2 : |t| ≤ b
      · rw [hind, Set.indicator_of_mem (show t ∈ {u | a < |u| ∧ |u| ≤ b} from ⟨lt_of_not_ge h1, h2⟩)]
        nlinarith [sq_nonneg (o t - 2 * G t)]
      · rw [hsupp t (lt_of_not_ge h2)]
        nlinarith [sq_nonneg (G t)]
  rw [hsplit]
  linarith [normSq_add_le hxm hym]

/-- **The shell estimate, odd sector.** -/
theorem normSq_sub_antiCut_le {a b : ℝ} {o G : ℝ → ℝ} (hp : OProbe b o) (hG : MemLp G 2 volume) :
    normSq (fun t => o t - antiCut a G t) ≤ 6 * normSq (fun t => o t - G t) + 4 * shellSq G a b :=
  normSq_sub_cut_le (antiCut a) (fun _ hf => memLp_antiCut a hf) (fun _ hf => normSq_antiCut_le a hf)
    (antiCut_sub a) (antiCut_oprobe hp a) hp.supp hp.memL2 hG

/-- For odd probes, Weil's form with the pole folded in. -/
theorem weilQg_odd_eq {a : ℝ} {o : ℝ → ℝ} (hp : OProbe a o) :
    weilQg a o = -2 * poleR o a ^ 2 + weilConst * normSq o + archE o - 2 * primeS o := by
  rw [weilQg, poleL_odd hp]; ring

/-- **Right-continuity of `λ_odd`** (compactness + lower semicontinuity). -/
theorem lamO_right {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b, a ≤ b → b < a + δ → lamO a - ε < lamO b := by
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
  -- near-minimisers
  have hnear : ∀ n, ∃ o, OProbe (b n) o ∧ normSq o = 1 ∧ weilQg (b n) o < lamO (b n) + ε / 2 := by
    intro n
    obtain ⟨q, ⟨o, hp, hn, rfl⟩, hq⟩ :=
      exists_lt_of_csInf_lt (lamO_nonempty (hb0 n)) (by linarith : lamO (b n) < lamO (b n) + ε / 2)
    exact ⟨o, hp, hn, hq⟩
  choose o hop hon hoq using hnear
  have hop1 : ∀ n, OProbe a₁ (o n) := fun n => (hop n).mono (hb1 n)
  have hQ1 : ∀ n, weilQg a₁ (o n) = weilQg (b n) (o n) := fun n =>
    weilQg_mono (hb0 n).le (hb1 n) (hop n).supp
  set F₁ := weilConst - 2 * primeWeight a₁ - 2 * (Real.sinh a₁ - a₁) with hF₁
  set q : ℕ → ℝ := fun n => weilQg a₁ (o n) with hq
  have hqI : ∀ n, q n ∈ Icc F₁ (lamO a - ε / 2) := fun n =>
    ⟨weilQg_odd_ge ha₁0 (hop1 n) (hon n), by
      simp only [hq]; rw [hQ1 n]; linarith [hoq n, hbl n]⟩
  obtain ⟨L, hLI, φ, hφ, hqφ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc F₁ (lamO a - ε / 2)) hqI
  rw [closure_Icc] at hLI
  -- bounded archimedean energy
  have hP : ∀ n, primeS (o n) ≤ primeWeight a₁ := fun n => by
    have := (le_abs_self _).trans (abs_primeS_le_S (hop1 n).toS); rwa [hon n, mul_one] at this
  have hC : ∀ j, archE (o (φ j)) ≤ lamO a + 2 * (Real.sinh a₁ - a₁) - weilConst + 2 * primeWeight a₁ := by
    intro j
    have e := weilQg_odd_eq (hop1 (φ j))
    have h1 := poleR_sq_odd ha₁0 (hop1 (φ j)) (hon (φ j))
    have h2 := (hqI (φ j)).2
    simp only [hq] at h2
    rw [e, hon (φ j)] at h2
    nlinarith [hP (φ j)]
  obtain ⟨ψ, hψ, G, hG, hlim⟩ := exists_convergent_subseq_S ha₁0 (fun j => (hop1 (φ j)).toS)
    (B := 1) (fun j => (hon (φ j)).le) hC
  set σ := φ ∘ ψ with hσ
  have hσm : StrictMono σ := hφ.comp hψ
  set h : ℕ → ℝ → ℝ := fun j => o (σ j) with hh
  set G' := antiCut a G with hG'def
  have hG' : MemLp G' 2 volume := memLp_antiCut a hG
  have hmem : ∀ j, MemLp (h j) 2 volume := fun j => (hop (σ j)).memL2
  have hlim' : Tendsto (fun j => normSq (fun t => h j t - G' t)) atTop (𝓝 0) := by
    have hsh := tendsto_shellSq hG (hbt.comp hσm.tendsto_atTop)
    have hup : Tendsto (fun j => 6 * normSq (fun t => h j t - G t) + 4 * shellSq G a (b (σ j)))
        atTop (𝓝 0) := by
      have := (hlim.const_mul 6).add (hsh.const_mul 4)
      rw [mul_zero, mul_zero, add_zero] at this
      exact this
    exact squeeze_zero (fun j => integral_nonneg fun t => sq_nonneg _)
      (fun j => normSq_sub_antiCut_le (hop (σ j)) hG) hup
  -- the limit is a normalised odd probe at `a`
  have hnorm : Tendsto (fun j => normSq (h j)) atTop (𝓝 (normSq G')) := by
    simp_rw [normSq_eq_mul]
    exact tendsto_integral_mul hmem hmem hG' hG' hlim' hlim'
  have hnormG : normSq G' = 1 :=
    tendsto_nhds_unique hnorm (tendsto_const_nhds.congr fun j => (hon (σ j)).symm)
  have hw0 : Tendsto (fun _ : ℕ => normSq (fun t => poleW a₁ t - poleW a₁ t)) atTop (𝓝 0) := by
    simp only [sub_self]; simp [normSq]
  have hpoleT : Tendsto (fun j => poleR (h j) a₁) atTop (𝓝 (poleR G' a₁)) := by
    simp_rw [poleR_eq ha₁0.le]
    exact tendsto_integral_mul hmem (fun _ => poleW_memLp a₁) hG' (poleW_memLp a₁) hlim' hw0
  have hauto : ∀ u, Tendsto (fun j => autocorr (h j) u) atTop (𝓝 (autocorr G' u)) := by
    intro u
    have hsh : ∀ j, normSq (fun t => h j (t + u) - G' (t + u)) = normSq (fun t => h j t - G' t) :=
      fun j => normSq_shift (fun t => h j t - G' t) u
    unfold autocorr
    exact tendsto_integral_mul hmem (fun j => memLp_shift (hmem j) u) hG' (memLp_shift hG' u)
      hlim' (hlim'.congr fun j => (hsh j).symm)
  have hsuppG' : ∀ u, a < |u| → G' u = 0 := antiCut_supp a G
  have hsuppG1 : ∀ u, a₁ < |u| → G' u = 0 := fun u hu => hsuppG' u (by linarith)
  have hprimeT : Tendsto (fun j => primeS (h j)) atTop (𝓝 (primeS G')) := by
    unfold primeS
    have e1 : ∀ j, (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n
        * autocorr (h j) (Real.log n))
        = ∑ n ∈ Finset.range (primeCut a₁), ArithmeticFunction.vonMangoldt n / Real.sqrt n
          * autocorr (h j) (Real.log n) := fun j => prime_sum_eq (hop1 (σ j)).supp
    simp_rw [e1]
    rw [prime_sum_eq hsuppG1]
    exact tendsto_finsetSum _ fun n _ => (hauto _).const_mul _
  set nA : ℝ → ℝ → ℝ := fun P S => -2 * P ^ 2 + weilConst * 1 - 2 * S with hnA
  have hnon : Tendsto (fun j => nA (poleR (h j) a₁) (primeS (h j))) atTop
      (𝓝 (nA (poleR G' a₁) (primeS G'))) := by
    simp only [hnA]
    exact (((hpoleT.pow 2).const_mul (-2)).add tendsto_const_nhds).sub (hprimeT.const_mul 2)
  have hqσ : Tendsto (fun j => q (σ j)) atTop (𝓝 L) := hqφ.comp hψ.tendsto_atTop
  have hA : Tendsto (fun j => archE (h j)) atTop (𝓝 (L - nA (poleR G' a₁) (primeS G'))) := by
    have e : ∀ j, archE (h j) = q (σ j) - nA (poleR (h j) a₁) (primeS (h j)) := by
      intro j
      simp only [hq, hh, hnA]; rw [weilQg_odd_eq (hop1 (σ j)), hon (σ j)]; ring
    simp_rw [e]
    exact hqσ.sub hnon
  obtain ⟨hint, hle⟩ := fatou_real measurableSet_Ioi
    (f := fun j => archIntegrand (h j)) (F := archIntegrand G')
    (fun j => (hop (σ j)).arch) (fun j u hu => archIntegrand_nonneg (hmem j) hu)
    (fun u _ => by
      unfold archIntegrand
      exact ((hauto 0).sub (hauto u)).mul_const _) hA
  have hPG : OProbe a G' := ⟨antiCut_odd a G, hsuppG', hG', hint⟩
  have hQG : weilQg a G' ≤ L := by
    rw [← weilQg_mono ha.le (by linarith : a ≤ a₁) hsuppG', weilQg_odd_eq (hPG.mono (by linarith)),
      hnormG]
    have : archE G' ≤ L - nA (poleR G' a₁) (primeS G') := hle
    simp only [hnA] at this
    linarith
  have := lamO_le ha hPG hnormG
  linarith [hLI.2]

/-! ## C3: left-continuity of `λ_odd` (dilation) -/

/-- The dilation `o_s(t) = √s·o(st)`: support `[−a/s, a/s]`, same norm. -/
def dil (s : ℝ) (o : ℝ → ℝ) (t : ℝ) : ℝ := Real.sqrt s * o (s * t)

theorem kerK_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ kerK u := (kerK_pos hu).le

/-- `K(u) ≤ (1/u + 2)e^{−u/2}`: equivalent to `1 + 2u ≤ e^{2u}`. -/
theorem kerK_le_exp {u : ℝ} (hu : 0 < u) : kerK u ≤ (1 / u + 2) * Real.exp (-(u / 2)) := by
  have hsh : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  unfold kerK
  rw [div_le_iff₀ hsh, Real.sinh_eq]
  have h1 := Real.add_one_le_exp (2 * u)
  have e1 : Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(u / 2)) * Real.exp (-u) = Real.exp (u / 2) * Real.exp (-(2 * u)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e3 : Real.exp (2 * u) * Real.exp (-(2 * u)) = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (u / 2)
  have hq := Real.exp_pos (-(2 * u))
  -- `(1/u + 2)(e^{u/2} − e^{u/2}e^{−2u})/2 ≥ e^{u/2}` ⟺ `(1 + 2u)(1 − e^{−2u}) ≥ 2u`
  have key : 2 * u ≤ (1 + 2 * u) * (1 - Real.exp (-(2 * u))) := by
    have : (1 + 2 * u) * Real.exp (-(2 * u)) ≤ 1 := by
      calc (1 + 2 * u) * Real.exp (-(2 * u)) ≤ Real.exp (2 * u) * Real.exp (-(2 * u)) :=
            mul_le_mul_of_nonneg_right (by linarith) hq.le
        _ = 1 := e3
    linarith
  have hexp : (1 / u + 2) * Real.exp (-(u / 2)) * ((Real.exp u - Real.exp (-u)) / 2)
      = Real.exp (u / 2) * ((1 + 2 * u) * (1 - Real.exp (-(2 * u)))) / (2 * u) := by
    calc (1 / u + 2) * Real.exp (-(u / 2)) * ((Real.exp u - Real.exp (-u)) / 2)
        = (1 / u + 2) / 2 * (Real.exp (-(u / 2)) * Real.exp u - Real.exp (-(u / 2)) * Real.exp (-u)) := by
          ring
      _ = (1 / u + 2) / 2 * (Real.exp (u / 2) - Real.exp (u / 2) * Real.exp (-(2 * u))) := by rw [e1, e2]
      _ = Real.exp (u / 2) * ((1 + 2 * u) * (1 - Real.exp (-(2 * u)))) / (2 * u) := by
          field_simp
  rw [hexp, le_div_iff₀ (by positivity)]
  nlinarith

/-- `G_s(v) = (f(0) − f(v))·K(v/s)`, so that `A(o_s)(u) = G_s(su)`. -/
def Gs (o : ℝ → ℝ) (s v : ℝ) : ℝ := (autocorr o 0 - autocorr o v) * kerK (v / s)

theorem dil_odd {s : ℝ} {o : ℝ → ℝ} (ho : ∀ u, o (-u) = -o u) (u : ℝ) : dil s o (-u) = -dil s o u := by
  unfold dil; rw [show s * -u = -(s * u) by ring, ho]; ring

theorem dil_supp {a s : ℝ} (hs : 0 < s) {o : ℝ → ℝ} (hsupp : ∀ u, a < |u| → o u = 0) (u : ℝ)
    (hu : a / s < |u|) : dil s o u = 0 := by
  unfold dil
  rw [hsupp (s * u) (by rw [abs_mul, abs_of_pos hs]; rwa [div_lt_iff₀' hs] at hu), mul_zero]

theorem memLp_dilS {s : ℝ} (hs : 0 < s) {o : ℝ → ℝ} (ho : MemLp o 2 volume) : MemLp (dil s o) 2 volume := by
  have hm : AEStronglyMeasurable (fun t => o (s * t)) volume := by
    have := ho.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume hs.ne')
    simpa [Function.comp_def, smul_eq_mul] using this
  have hi : Integrable (fun t => o (s * t) ^ 2) :=
    Integrable.comp_mul_left' ho.integrable_sq hs.ne'
  exact ((memLp_two_iff_integrable_sq hm).2 hi).const_mul _

theorem autocorr_dil {s : ℝ} (hs : 0 < s) (o : ℝ → ℝ) (u : ℝ) :
    autocorr (dil s o) u = autocorr o (s * u) := by
  unfold autocorr dil
  have e : ∀ t, Real.sqrt s * o (s * t) * (Real.sqrt s * o (s * (t + u)))
      = s * (fun v => o v * o (v + s * u)) (s * t) := by
    intro t; simp only
    rw [mul_add]
    calc Real.sqrt s * o (s * t) * (Real.sqrt s * o (s * t + s * u))
        = (Real.sqrt s * Real.sqrt s) * (o (s * t) * o (s * t + s * u)) := by ring
      _ = s * (o (s * t) * o (s * t + s * u)) := by rw [Real.mul_self_sqrt hs.le]
  have hc := Measure.integral_comp_mul_left (fun v => o v * o (v + s * u)) s
  simp_rw [e]
  rw [integral_const_mul, hc, abs_of_pos (inv_pos.2 hs), smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

theorem normSq_dilS {s : ℝ} (hs : 0 < s) (o : ℝ → ℝ) : normSq (dil s o) = normSq o := by
  rw [← autocorr_zero, ← autocorr_zero, autocorr_dil hs, mul_zero]

theorem archIntegrand_dilS {s : ℝ} (hs : 0 < s) (o : ℝ → ℝ) (u : ℝ) :
    archIntegrand (dil s o) u = Gs o s (s * u) := by
  unfold archIntegrand Gs kerK
  rw [autocorr_dil hs, autocorr_dil hs, mul_zero, mul_div_cancel_left₀ _ hs.ne']

/-- The dominating function `D(v) = 8·A(o)(v) + 8 f(0) e^{−v/4}`. -/
def domD (o : ℝ → ℝ) (v : ℝ) : ℝ := 8 * archIntegrand o v + 8 * autocorr o 0 * Real.exp (-(1 / 4) * v)

theorem Gs_nonneg {o : ℝ → ℝ} (ho : MemLp o 2 volume) {s v : ℝ} (hs : 0 < s) (hv : 0 < v) :
    0 ≤ Gs o s v := by
  refine mul_nonneg ?_ (kerK_nonneg (div_pos hv hs))
  rw [autocorr_zero, sub_nonneg]; exact (le_abs_self _).trans (abs_autocorr_le ho v)

theorem Gs_le_domD {o : ℝ → ℝ} (ho : MemLp o 2 volume) {s v : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hv : 0 < v) : Gs o s v ≤ domD o v := by
  have hs : 0 < s := by linarith
  have hf : 0 ≤ autocorr o 0 - autocorr o v := by
    rw [autocorr_zero, sub_nonneg]; exact (le_abs_self _).trans (abs_autocorr_le ho v)
  have hf0 : 0 ≤ autocorr o 0 := by rw [autocorr_zero]; exact normSq_nonneg o
  have hf2 : autocorr o 0 - autocorr o v ≤ 2 * autocorr o 0 := by
    have := abs_autocorr_le ho v; rw [← autocorr_zero] at this; linarith [neg_abs_le (autocorr o v)]
  have hA0 : 0 ≤ archIntegrand o v := archIntegrand_nonneg ho hv
  have hE0 : 0 ≤ Real.exp (-(1 / 4) * v) := (Real.exp_pos _).le
  -- `K(v/s) ≤ (s/v + 2)e^{−v/(2s)} ≤ (2/v + 2)e^{−v/4}`
  have hK : kerK (v / s) ≤ (2 / v + 2) * Real.exp (-(1 / 4) * v) := by
    refine (kerK_le_exp (div_pos hv hs)).trans ?_
    have h1 : 1 / (v / s) ≤ 2 / v := by
      rw [one_div_div, div_le_div_iff_of_pos_right hv]; linarith
    have h2 : Real.exp (-(v / s / 2)) ≤ Real.exp (-(1 / 4) * v) := by
      apply Real.exp_le_exp.2
      have : v / 4 ≤ v / s / 2 := by
        rw [div_div, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      linarith
    exact mul_le_mul (by linarith) h2 (Real.exp_pos _).le (by positivity)
  unfold Gs domD
  rcases le_or_gt v 1 with hv1 | hv1
  · -- near `0`: `(2/v + 2) e^{−v/4} ≤ 4/v ≤ 8 K(v)`
    have hKv := archK_ge hv hv1
    have h3 : (2 / v + 2) * Real.exp (-(1 / 4) * v) ≤ 8 * (Real.exp (v / 2) / Real.sinh v) := by
      have hexp1 : Real.exp (-(1 / 4) * v) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have : 2 / v + 2 ≤ 4 / v := by rw [div_add' _ _ _ hv.ne', div_le_div_iff_of_pos_right hv]; linarith
      calc (2 / v + 2) * Real.exp (-(1 / 4) * v) ≤ (4 / v) * 1 :=
            mul_le_mul this hexp1 hE0 (by positivity)
        _ = 8 * (1 / (2 * v)) := by field_simp; ring
        _ ≤ 8 * (Real.exp (v / 2) / Real.sinh v) := by linarith
    calc (autocorr o 0 - autocorr o v) * kerK (v / s)
        ≤ (autocorr o 0 - autocorr o v) * (8 * (Real.exp (v / 2) / Real.sinh v)) :=
          mul_le_mul_of_nonneg_left (hK.trans h3) hf
      _ = 8 * archIntegrand o v := by unfold archIntegrand; ring
      _ ≤ _ := by nlinarith
  · -- far: `(2/v + 2) ≤ 4` and `f(0) − f(v) ≤ 2 f(0)`
    have h4 : 2 / v + 2 ≤ 4 := by
      have : 2 / v ≤ 2 := by rw [div_le_iff₀ hv]; linarith
      linarith
    calc (autocorr o 0 - autocorr o v) * kerK (v / s)
        ≤ (2 * autocorr o 0) * (4 * Real.exp (-(1 / 4) * v)) :=
          mul_le_mul hf2 (hK.trans (mul_le_mul_of_nonneg_right h4 hE0)) (kerK_nonneg (div_pos hv hs))
            (by linarith)
      _ = 8 * autocorr o 0 * Real.exp (-(1 / 4) * v) := by ring
      _ ≤ _ := by nlinarith

theorem integrableOn_domD {a : ℝ} {o : ℝ → ℝ} (hp : SProbe a o) : IntegrableOn (domD o) (Ioi 0) :=
  (hp.arch.const_mul 8).add
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul (8 * autocorr o 0))

theorem measurable_Gs {o : ℝ → ℝ} (ho : MemLp o 2 volume) (s : ℝ) : Measurable (Gs o s) := by
  unfold Gs
  exact (measurable_const.sub (continuous_autocorr ho).measurable).mul
    (kerK_measurable.comp (measurable_id.div_const s))

theorem integrableOn_Gs {a : ℝ} {o : ℝ → ℝ} (hp : SProbe a o) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    IntegrableOn (Gs o s) (Ioi 0) := by
  refine (integrableOn_domD hp).mono' (measurable_Gs hp.memL2 s).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Gs_nonneg hp.memL2 (by linarith) hv)]
  exact Gs_le_domD hp.memL2 hs1 hs2 hv

theorem arch_dil {a : ℝ} {o : ℝ → ℝ} (hp : SProbe a o) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    IntegrableOn (archIntegrand (dil s o)) (Ioi 0) := by
  have hs : 0 < s := by linarith
  have e : archIntegrand (dil s o) = fun u => Gs o s (s * u) := funext (archIntegrand_dilS hs o)
  rw [e, integrableOn_Ioi_comp_mul_left_iff (Gs o s) 0 hs, mul_zero]
  exact integrableOn_Gs hp hs1 hs2

theorem archE_dil {o : ℝ → ℝ} {s : ℝ} (hs : 0 < s) :
    archE (dil s o) = s⁻¹ * ∫ v in Ioi 0, Gs o s v := by
  unfold archE
  simp_rw [archIntegrand_dilS hs o]
  rw [integral_comp_mul_left_Ioi (Gs o s) 0 hs, mul_zero, smul_eq_mul]

/-- **Odd probes dilate to odd probes** (for `1 ≤ s ≤ 2`). -/
theorem oprobe_dil {a : ℝ} {o : ℝ → ℝ} (hp : OProbe a o) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    OProbe (a / s) (dil s o) :=
  ⟨dil_odd hp.odd, dil_supp (by linarith) hp.supp, memLp_dilS (by linarith) hp.memL2,
    arch_dil hp.toS hs1 hs2⟩

/-- The archimedean energy is continuous under dilation at `s = 1`. -/
theorem tendsto_archE_dilS {a : ℝ} {o : ℝ → ℝ} (hp : SProbe a o) :
    Tendsto (fun s => archE (dil s o)) (𝓝[Icc 1 2] 1) (𝓝 (archE o)) := by
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), s ∈ Icc (1 : ℝ) 2 := self_mem_nhdsWithin
  have hI : Tendsto (fun s => ∫ v in Ioi 0, Gs o s v) (𝓝[Icc 1 2] 1) (𝓝 (∫ v in Ioi 0, Gs o 1 v)) := by
    refine tendsto_integral_filter_of_dominated_convergence (domD o)
      (Eventually.of_forall fun s => (measurable_Gs hp.memL2 s).aestronglyMeasurable)
      (hev.mono fun s hs => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
      (integrableOn_domD hp) ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
    · rw [Real.norm_eq_abs, abs_of_nonneg (Gs_nonneg hp.memL2 (by linarith [hs.1]) hv)]
      exact Gs_le_domD hp.memL2 hs.1 hs.2 hv
    · have hv0 : (0 : ℝ) < v := hv
      have hc : ContinuousAt (fun s => Gs o s v) 1 := by
        unfold Gs kerK
        refine continuousAt_const.mul (ContinuousAt.div
          (Real.continuous_exp.continuousAt.comp
            ((continuousAt_const.div continuousAt_id one_ne_zero).div_const 2)) ?_ ?_)
        · exact (Real.continuous_sinh.continuousAt).comp (continuousAt_const.div continuousAt_id one_ne_zero)
        · simp only [div_one]; exact (Real.sinh_pos_iff.2 hv0).ne'
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hGs1 : (∫ v in Ioi 0, Gs o 1 v) = archE o := by
    unfold archE Gs kerK archIntegrand; simp only [div_one]
  have hinv : Tendsto (fun s : ℝ => s⁻¹) (𝓝[Icc 1 2] 1) (𝓝 1) := by
    have := (tendsto_inv₀ (one_ne_zero' ℝ)).mono_left (nhdsWithin_le_nhds (s := Icc (1 : ℝ) 2))
    rw [inv_one] at this; exact this
  have := hinv.mul hI
  rw [one_mul, hGs1] at this
  refine this.congr' (hev.mono fun s hs => ?_)
  dsimp only
  rw [archE_dil (by linarith [hs.1])]

/-- `ĝ_s(i/2)` in terms of `o`: `poleR(o_s) = √s·s⁻¹·∫ o(v)e^{−v/(2s)} dv`. -/
theorem sprobe_integrable {a : ℝ} {g : ℝ → ℝ} (hg : SProbe a g) : Integrable g :=
  integrable_of_supp hg.supp hg.memL2

theorem poleR_dil {a : ℝ} {o : ℝ → ℝ} (hp : SProbe a o) {s : ℝ} (hs1 : 1 ≤ s) (ha : 0 ≤ a) :
    poleR (dil s o) a = Real.sqrt s * s⁻¹ * ∫ v, o v * Real.exp (-(v / s / 2)) := by
  have hs : 0 < s := by linarith
  have hsupp : ∀ u, a < |u| → dil s o u = 0 := fun u hu =>
    dil_supp hs hp.supp u (lt_of_le_of_lt (div_le_self ha hs1) hu)
  rw [poleR_eq_integral ha hsupp]
  have e : ∀ t, dil s o t * Real.exp (-(t / 2))
      = Real.sqrt s * (fun v => o v * Real.exp (-(v / s / 2))) (s * t) := by
    intro t; simp only [dil]; rw [mul_div_cancel_left₀ _ hs.ne']; ring
  have hc := Measure.integral_comp_mul_left (fun v => o v * Real.exp (-(v / s / 2))) s
  simp_rw [e]
  rw [integral_const_mul, hc, abs_of_pos (inv_pos.2 hs), smul_eq_mul]; ring

theorem tendsto_pole_dil {a : ℝ} (ha : 0 < a) {o : ℝ → ℝ} (hp : SProbe a o) :
    Tendsto (fun s => poleR (dil s o) a) (𝓝[Icc 1 2] 1) (𝓝 (poleR o a)) := by
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), s ∈ Icc (1 : ℝ) 2 := self_mem_nhdsWithin
  have hI := sprobe_integrable hp
  have hT : Tendsto (fun s => ∫ v, o v * Real.exp (-(v / s / 2))) (𝓝[Icc 1 2] 1)
      (𝓝 (∫ v, o v * Real.exp (-(v / 1 / 2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => |o v| * Real.exp a)
      (Eventually.of_forall fun s => (hI.aestronglyMeasurable.mul
        (by fun_prop : Continuous fun v : ℝ => Real.exp (-(v / s / 2))).aestronglyMeasurable))
      (hev.mono fun s hs => Eventually.of_forall fun v => ?_) (hI.abs.mul_const _)
      (Eventually.of_forall fun v => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      by_cases hv : a < |v|
      · rw [hp.supp v hv, abs_zero, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
        have hs0 : 0 < s := by linarith [hs.1]
        have : |v / s / 2| ≤ a := by
          rw [abs_div, abs_div, abs_of_pos hs0, abs_two]
          have : |v| / s ≤ |v| := div_le_self (abs_nonneg v) hs.1
          linarith [not_lt.1 hv, abs_nonneg v]
        linarith [neg_abs_le (v / s / 2)]
    · have hc : ContinuousAt (fun s : ℝ => o v * Real.exp (-(v / s / 2))) 1 :=
        continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
          ((continuousAt_const.div continuousAt_id one_ne_zero).div_const 2).neg)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun s : ℝ => Real.sqrt s * s⁻¹) (𝓝[Icc 1 2] 1) (𝓝 1) := by
    have h1 := (Real.continuous_sqrt.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Icc (1 : ℝ) 2))
    have h2 := (tendsto_inv₀ (one_ne_zero' ℝ)).mono_left (nhdsWithin_le_nhds (s := Icc (1 : ℝ) 2))
    have := h1.mul h2
    rw [Real.sqrt_one, inv_one, one_mul] at this; exact this
  have hlimit : (∫ v, o v * Real.exp (-(v / 1 / 2))) = poleR o a := by
    rw [poleR_eq_integral ha.le hp.supp]; simp only [div_one]
  have := hsq.mul hT
  rw [one_mul, hlimit] at this
  refine this.congr' (hev.mono fun s hs => ?_)
  dsimp only
  rw [poleR_dil hp hs.1 ha.le]

theorem tendsto_primeS_dil {a : ℝ} (ha : 0 < a) {o : ℝ → ℝ} (hp : SProbe a o) :
    Tendsto (fun s => primeS (dil s o)) (𝓝[Icc 1 2] 1) (𝓝 (primeS o)) := by
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), s ∈ Icc (1 : ℝ) 2 := self_mem_nhdsWithin
  have hc : Continuous fun s : ℝ => ∑ n ∈ Finset.range (primeCut a),
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr o (s * Real.log n) :=
    continuous_finsetSum _ fun n _ => continuous_const.mul
      ((continuous_autocorr hp.memL2).comp (continuous_id.mul continuous_const))
  have h1 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Icc (1 : ℝ) 2))
  simp only [one_mul] at h1
  have e1 : primeS o = ∑ n ∈ Finset.range (primeCut a),
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * autocorr o (Real.log n) := by
    unfold primeS; exact prime_sum_eq hp.supp
  rw [e1]
  refine h1.congr' (hev.mono fun s hs => ?_)
  have hs0 : 0 < s := by linarith [hs.1]
  dsimp only
  unfold primeS
  rw [prime_sum_eq (a := a) (fun u hu => dil_supp hs0 hp.supp u
    (lt_of_le_of_lt (div_le_self ha.le hs.1) hu))]
  simp_rw [autocorr_dil hs0]

/-- **Weil's form is continuous under dilation** at `s = 1⁺`. -/
theorem tendsto_weilQg_dil {a : ℝ} (ha : 0 < a) {o : ℝ → ℝ} (hp : OProbe a o) :
    Tendsto (fun s => weilQg a (dil s o)) (𝓝[Icc 1 2] 1) (𝓝 (weilQg a o)) := by
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), s ∈ Icc (1 : ℝ) 2 := self_mem_nhdsWithin
  have hlim := ((((tendsto_pole_dil ha hp.toS).pow 2).const_mul (-2)).add
    (tendsto_const_nhds (x := weilConst * normSq o))).add (tendsto_archE_dilS hp.toS) |>.sub
    ((tendsto_primeS_dil ha hp.toS).const_mul 2)
  rw [weilQg_odd_eq hp]
  refine hlim.congr' (hev.mono fun s hs => ?_)
  have hs0 : 0 < s := by linarith [hs.1]
  dsimp only
  rw [weilQg_odd_eq ((oprobe_dil hp hs.1 hs.2).mono (div_le_self ha.le hs.1)), normSq_dilS hs0]

/-- **Left-continuity by dilation**, for any class of probes `Pr` that dilation maps into itself:
if `o` nearly attains `l a`, its dilations nearly attain `l b` for `b` just below `a`. -/
theorem left_cont_of_dil {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) {Pr : ℝ → (ℝ → ℝ) → Prop}
    {Q : ℝ → (ℝ → ℝ) → ℝ} {l : ℝ → ℝ} {o : ℝ → ℝ} (hn : normSq o = 1) (hq : Q a o < l a + ε / 2)
    (hT : Tendsto (fun s => Q a (dil s o)) (𝓝[Icc 1 2] 1) (𝓝 (Q a o)))
    (hdil : ∀ s, 1 ≤ s → s ≤ 2 → Pr (a / s) (dil s o))
    (hmono : ∀ b g, 0 < b → b ≤ a → Pr b g → Q a g = Q b g)
    (hle : ∀ b g, 0 < b → Pr b g → normSq g = 1 → l b ≤ Q b g) :
    ∃ δ > 0, ∀ b, a - δ < b → b ≤ a → l b < l a + ε := by
  have hev : ∀ᶠ s in 𝓝[Icc 1 2] (1 : ℝ), Q a (dil s o) < l a + ε :=
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
  have hQ : Q a (dil s o) < l a + ε := hUs ⟨hsU, hs1, hs2⟩
  have hbs : a / s = b := by rw [hsdef]; field_simp
  have hpb : Pr b (dil s o) := hbs ▸ hdil s hs1 hs2
  have hnb : normSq (dil s o) = 1 := by rw [normSq_dilS (by linarith), hn]
  have := hle b _ hb0 hpb hnb
  rw [← hmono b _ hb0 hba hpb] at this
  linarith

/-- **Left-continuity of `λ_odd`.** -/
theorem lamO_left {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b, a - δ < b → b ≤ a → lamO b < lamO a + ε := by
  obtain ⟨q, ⟨o, hp, hn, rfl⟩, hq⟩ :=
    exists_lt_of_csInf_lt (lamO_nonempty ha) (by linarith : lamO a < lamO a + ε / 2)
  exact left_cont_of_dil (Pr := OProbe) ha hε hn hq (tendsto_weilQg_dil ha hp)
    (fun s h1 h2 => oprobe_dil hp h1 h2) (fun b g hb hba hg => weilQg_mono hb.le hba hg.supp)
    (fun b g hb hg hgn => lamO_le hb hg hgn)

/-- A function that is right- and left-continuous in the sense below and antitone is continuous
on `(0, ∞)`. -/
theorem continuousOn_of_right_left {l : ℝ → ℝ}
    (hr : ∀ a, 0 < a → ∀ ε, 0 < ε → ∃ δ > 0, ∀ b, a ≤ b → b < a + δ → l a - ε < l b)
    (hl : ∀ a, 0 < a → ∀ ε, 0 < ε → ∃ δ > 0, ∀ b, a - δ < b → b ≤ a → l b < l a + ε)
    (hanti : ∀ a b, 0 < a → a ≤ b → l b ≤ l a) : ContinuousOn l (Ioi 0) := by
  intro a ha
  have ha : 0 < a := ha
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, h₁⟩ := hr a ha ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hl a ha ε hε
  refine ⟨min δ₁ (min δ₂ a), by positivity, fun {b} hb hd => ?_⟩
  have hb0 : 0 < b := hb
  rw [Real.dist_eq, abs_lt] at hd ⊢
  have hm1 := min_le_left δ₁ (min δ₂ a)
  have hm2 := (min_le_right δ₁ (min δ₂ a)).trans (min_le_left δ₂ a)
  rcases le_total a b with hab | hba
  · have := h₁ b hab (by linarith [hd.2])
    have := hanti a b ha hab
    constructor <;> linarith
  · have := h₂ b (by linarith [hd.1]) hba
    have := hanti b a hb0 hba
    constructor <;> linarith

/-- **`λ_odd` is continuous on `(0, ∞)`.** -/
theorem continuousOn_lamO : ContinuousOn lamO (Ioi 0) :=
  continuousOn_of_right_left (fun _ ha _ hε => lamO_right ha hε) (fun _ ha _ hε => lamO_left ha hε)
    (fun _ _ ha hab => lamO_antitone ha hab)

/-! ## The continuation theorem -/

/-- **Round 146, the continuation theorem.** If the parity gap holds strictly at `a₀ > 0`
(`lam a₀ < lamO a₀`) and the even and odd ground energies never coincide for `a ≥ a₀`, the parity
gap holds at every `a ≥ a₀`. -/
theorem parityGap_of_no_crossing {a₀ : ℝ} (h0 : 0 < a₀) (hgap : lam a₀ < lamO a₀)
    (hnc : ∀ a, a₀ ≤ a → lam a ≠ lamO a) : ∀ a, a₀ ≤ a → ParityGap a :=
  gap_of_no_crossing_Ici h0 hgap (continuousOn_lamO.mono fun _ h => h0.trans_le h) hnc

/-! ## C4: the certified start at `a₀ = 1/4` -/

/-- **The odd floor at `a = 1/4`**: every normalised odd probe has `Q ≥ 1/5`. (Round 20's odd
bound, evaluated at the endpoint instead of minimised over `(0, 1/4]`.) -/
theorem weilQodd_quarter {g : ℝ → ℝ} (hp : OProbe (1 / 4) g) (hn : normSq g = 1) :
    (1 / 5 : ℝ) ≤ weilQg (1 / 4) g := by
  have ha : (0 : ℝ) < 1 / 4 := by norm_num
  have hlog : 2 * (1 / 4 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  rw [weilQg, poleL_odd hp, primeS_eq_zeroS hlog hp.toS, hn, archE_splitS ha hp.toS hn, farField_eq ha]
  have hC := weilConst_ge
  have hN := nearField_odd ha le_rfl hp hn
  have hP := poleR_sq_odd ha hp hn
  have hE : 1 < Real.exp (1 / 4) := Real.one_lt_exp_iff.mpr ha
  have hratio : 2 / (1 / 4) ≤ (Real.exp (1 / 4) + 1) / (Real.exp (1 / 4) - 1) := by
    rw [div_le_div_iff₀ ha (by linarith)]
    nlinarith [two_exp_sub_le ha.le]
  have hneg : -Real.log ((Real.exp (1 / 4) - 1) / (Real.exp (1 / 4) + 1))
      = Real.log ((Real.exp (1 / 4) + 1) / (Real.exp (1 / 4) - 1)) := by
    rw [← Real.log_inv, inv_div]
  have hlogr := Real.log_le_log (by norm_num) hratio
  have hl8 : Real.log (2 / (1 / 4)) = 3 * Real.log 2 := by
    rw [show (2 : ℝ) / (1 / 4) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hat : Real.arctan (Real.sinh (1 / 4)) ≤ Real.sinh (1 / 4) :=
    Real.arctan_le_self (Real.sinh_nonneg_iff.mpr ha.le)
  have hsh : Real.sinh (1 / 4) ≤ 1 / 4 + (1 / 4) ^ 3 / 6 + (1 / 4) ^ 5 / 100 :=
    sinh_le_taylor ha.le (by norm_num)
  have herr : errK (1 / 4) ≤ 0.0157 := by unfold errK; norm_num
  have hl2 := Real.log_two_gt_d9
  have hπ := Real.pi_gt_d6
  rw [hneg]
  norm_num at hl2 hπ hsh herr hN hl8 ⊢
  nlinarith

/-- `γ > 0.5456`, from Mathlib's `H_n − log(n + 1) < γ` at `n = 16`. -/
theorem gamma_gt : (0.5456 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 16
  have e : Real.eulerMascheroniSeq 16 = 2436559 / 720720 - Real.log 17 := by
    rw [Real.eulerMascheroniSeq]; norm_num [harmonic, Finset.sum_range_succ]
  have h17 : Real.log 17 ≤ 4 * Real.log 2 + 1 / 16 := by
    have h1 : Real.log 17 = Real.log 16 + Real.log (17 / 16) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 17 / 16 by norm_num)
    linarith
  have hl2 := Real.log_two_lt_d9
  rw [e] at h
  norm_num at hl2 h ⊢
  linarith

/-- `ψ(¼) − log π ≤ −5.3`. -/
theorem weilConst_le : weilConst ≤ (-5.3 : ℝ) := by
  rw [weilConst_eq]
  have hγ := gamma_gt
  have hπ := Real.pi_gt_d6
  have hl2 := Real.log_two_gt_d9
  have hlogπ : 2 * Real.log 2 + (1 - (π / 4)⁻¹) ≤ Real.log π := by
    have h4 : Real.log π = Real.log 4 + Real.log (π / 4) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
    have h44 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.one_sub_inv_le_log_of_pos (show 0 < π / 4 by positivity)
    linarith
  have hinv : (π / 4)⁻¹ ≤ 1.2733 := by
    rw [inv_div, div_le_iff₀ Real.pi_pos]; norm_num at hπ ⊢; linarith
  norm_num at hl2 hπ
  linarith

/-- **The even ceiling at `a = 1/4`**: the parabola has `Q < 1/5`. -/
theorem lam_quarter_lt : lam (1 / 4) < 1 / 5 := by
  have ha : (0 : ℝ) < 1 / 4 := by norm_num
  have hlog : 2 * (1 / 4 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hpp := par_probe ha
  have hnp := normSq_par ha
  refine (lam_le hpp hnp).trans_lt ?_
  rw [weilQ_eq', primeS_eq_zero hlog hpp, archE_split ha hpp hnp, farField_eq ha, hnp]
  have hP := pole_par_le ha (by norm_num)
  have hN := nearField_par_le ha
  have hC := weilConst_le
  -- the log term: `(e^{1/4} + 1)/(e^{1/4} − 1) ≤ 8.07`, from `e^{1/4} ≥ 1 + x + x²/2 + x³/6`
  have hE3 : (1 : ℝ) + 1 / 4 + (1 / 4) ^ 2 / 2 + (1 / 4) ^ 3 / 6 ≤ Real.exp (1 / 4) := by
    have := Real.sum_le_exp_of_nonneg ha.le 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this ⊢; linarith
  have hratio : (Real.exp (1 / 4) + 1) / (Real.exp (1 / 4) - 1) ≤ 8.07 := by
    rw [div_le_iff₀ (by norm_num at hE3; linarith)]; norm_num at hE3 ⊢; linarith
  have hneg : -Real.log ((Real.exp (1 / 4) - 1) / (Real.exp (1 / 4) + 1))
      = Real.log ((Real.exp (1 / 4) + 1) / (Real.exp (1 / 4) - 1)) := by
    rw [← Real.log_inv, inv_div]
  have hpos : 0 < (Real.exp (1 / 4) + 1) / (Real.exp (1 / 4) - 1) := by
    have := Real.one_lt_exp_iff.mpr ha; apply div_pos <;> linarith
  have hlog807 : Real.log 8.07 ≤ 3 * Real.log 2 + (8.07 / 8 - 1) := by
    have h1 : Real.log 8.07 = Real.log 8 + Real.log (8.07 / 8) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8.07 / 8 by norm_num)
    linarith
  have hlogr := Real.log_le_log hpos hratio
  -- the arctan term: `arctan(sinh a) ≥ sin(arctan(sinh a)) = tanh a ≥ a/(1 + a²/2 + 5a⁴/96)`
  have hsh0 : 0 ≤ Real.sinh (1 / 4) := Real.sinh_nonneg_iff.mpr ha.le
  have hθ0 : 0 ≤ Real.arctan (Real.sinh (1 / 4)) := Real.arctan_nonneg.2 hsh0
  have hsin := Real.sin_le hθ0
  rw [Real.sin_arctan] at hsin
  have hsq : √(1 + Real.sinh (1 / 4) ^ 2) = Real.cosh (1 / 4) := by
    rw [add_comm, ← Real.cosh_sq, Real.sqrt_sq (Real.cosh_pos _).le]
  rw [hsq] at hsin
  have hch := cosh_le_taylor (y := 1 / 4) (by norm_num)
  have hsh1 : (1 / 4 : ℝ) ≤ Real.sinh (1 / 4) := Real.self_le_sinh_iff.2 ha.le
  have htanh : (1 / 4 : ℝ) / (1 + (1 / 4) ^ 2 / 2 + 5 * (1 / 4) ^ 4 / 96) ≤
      Real.sinh (1 / 4) / Real.cosh (1 / 4) := by
    rw [div_le_div_iff₀ (by norm_num) (Real.cosh_pos _)]
    nlinarith [Real.cosh_pos (1 / 4 : ℝ)]
  have hl2 := Real.log_two_lt_d9
  have hπ := Real.pi_lt_d6
  rw [hneg]
  norm_num at hP hN hl2 hπ hlog807 htanh ⊢
  linarith

/-- **The certified start**: `λ_even(1/4) < 1/5 ≤ λ_odd(1/4)`. -/
theorem gap_quarter : lam (1 / 4) < lamO (1 / 4) :=
  lam_quarter_lt.trans_le (le_csInf (lamO_nonempty (by norm_num))
    fun _ ⟨_, hp, hn, hq⟩ => hq ▸ weilQodd_quarter hp hn)

/-- **Round 146's reduction, with its start discharged.** If the even and odd ground energies never
coincide for `a ≥ 1/4`, the parity gap holds at every `a ≥ 1/4`. -/
theorem parityGap_of_no_crossing_quarter (hnc : ∀ a, 1 / 4 ≤ a → lam a ≠ lamO a) :
    ∀ a, 1 / 4 ≤ a → ParityGap a :=
  parityGap_of_no_crossing (by norm_num) gap_quarter hnc

/-- **RH from no crossing.** If the even and odd ground energies never coincide for `a ≥ 1/4`, then
ground states along any supports `aₙ → ∞` satisfying `HypConv` give Mathlib's `RiemannHypothesis`. -/
theorem rh_of_no_crossing {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hinf : Tendsto a atTop atTop)
    (hnc : ∀ b, 1 / 4 ≤ b → lam b ≠ lamO b) (hconv : HypConv a g) : RiemannHypothesis :=
  rh_of_parity_gap ha hgs ((hinf.eventually_ge_atTop (1 / 4)).mono fun n hn =>
    parityGap_of_no_crossing_quarter hnc (a n) hn) hconv

end Pilot1ca

#print axioms Pilot1ca.lamO_antitone
#print axioms Pilot1ca.gap_of_no_crossing
#print axioms Pilot1ca.gap_of_no_crossing_Ici
#print axioms Pilot1ca.lamO_right
#print axioms Pilot1ca.lamO_left
#print axioms Pilot1ca.continuousOn_lamO
#print axioms Pilot1ca.parityGap_of_no_crossing
#print axioms Pilot1ca.weilQodd_quarter
#print axioms Pilot1ca.lam_quarter_lt
#print axioms Pilot1ca.gap_quarter
#print axioms Pilot1ca.parityGap_of_no_crossing_quarter
#print axioms Pilot1ca.rh_of_no_crossing
