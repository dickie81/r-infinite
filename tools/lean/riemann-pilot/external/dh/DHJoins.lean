import Mathlib
import DHColumn
import DHRealAxis
import DHChannels
import DHOddPacket
import DHLocateFour
import WeilChiDensity
import WeilTwinGeneral

/-! # Joins in the Davenport–Heilbronn layer (rounds 328–329)

Results whose parts the layer already had, but which no file stated. None needs new analysis.

**`DHRH ↔ DHRHcross`** (`dhRH_iff_cross`). `dhRH_of_cross` (DHColumn, round 263) takes the exclusion of
positive real zeros as a named input `hreal`, and `dh_ne_zero_of_real` (DHRealAxis, the same round)
proves it; DHColumn does not import DHRealAxis. So RH for `dh` and its cross form are equivalent, and
`dhRH_of_cross'` is `dhRH_of_cross` with `hreal` discharged. Both propositions are false:
`dh_offline_zero` (round 261) refutes `DHRH`, and `dh_offline_nonreal_zero` (DHOffCross, round 262)
refutes `DHRHcross`.

**Conjugation symmetry** (`dh_conj`, `dh_conj_zero`): `dh(s̄) = conj dh(s)` for every `s`. Round 253
listed it first among its walls, as needing the Gauss-sum identity `ε_{χ⁻¹} = conj ε_χ`. Round 256 has
that identity for `χ₅` without a Gauss sum (`rootNumber_chi5_inv_eq_conj`, from `εε′ = 1` and
`‖ε‖ = 1`), and round 273 has `conj L(s, χ) = L(s̄, χ⁻¹)` for `χ ≠ 1` (`conj_LFunction`).

**The parity split of `Q_dh`** (`QDHu_add_even_odd`): `Q_dh(φ + ψ) = Q_dh(φ) + Q_dh(ψ)` for an even probe
`φ` and an odd probe `ψ` at the same support, the `dh` column of `ParitySplit.weilQg_parity` (round 125).
`QDHu` sees `g` only through its autocorrelation, whose cross terms cancel for `φ` even and `ψ` odd
(`autocorr_parity`), and `QDHu` has no pole term. Hence the cosine and sine packets at `(12/5, 169/2)`
(rounds 261 and 269) span a plane on which `Q_dh` is negative definite (`QDHu_packet_plane_neg`).

**The index on probes of either parity is at least `5`** (`DHNegIndex.negIndex_ge_five`): the four even
directions of `negIndex_ge_four` (round 270) and the odd sine packet span a `5`-dimensional space of
`SProbe`s (`sprobe_add_even_odd`) on which `Q_dh` is negative definite. An even and an odd function meet
only in `0`, and `Q_dh` adds across the two parities.

**`QCu χ` is a `ProbeForm`** (`QCu_form`) for every Dirichlet character `χ` (modulus `N ≠ 0`) at every
support: DHForm's proof of `QDHu_form`, with `fχ` (DirichletOmega), `qC χ` (WeilChiBridge), `cChi χ` and
`MC χ a` (WeilChiDensity) in place of `fDH`, `3/4`, `constDH` and `MDH a`. It uses DHForm's `archEQ_smul`
and `archEQ_congr_ae`, which hold for every `q` but live in this layer, so it is stated here and not in
`src/`. It defines the χ ground energy `λ_χ(a)` (`lamC`), non-increasing in the support
(`lamC_antitone`), the first piece of the ground-state layer for `χ` that round 227 lists as not ported.

**GRH(χ) iff `λ_χ ≥ 0` at every support** (`grh_iff_lamC_nonneg`, round 329). `Q_χ ≥ 0` on every probe at
every support iff `λ_χ ≥ 0` at every support, for every `χ` (`probe_nonneg_iff_lamC_nonneg`), so round 227's
`weil_criterion_chi` (for `GoodChar χ` with `L(σ, χ) ≠ 0` on `(0, 1)`) becomes a statement about `λ_χ`.
Since `λ_χ` is non-increasing, GRH(χ) also holds iff `λ_χ ≥ 0` at all large supports
(`grh_iff_lamC_eventually_nonneg`), and its failure makes `λ_χ` negative from some support on
(`exists_lamC_neg_of_not_GRH`). Instances: `χ₋₃`, `χ₋₄`, `χ₋₈` and `χ₋₇`, the characters whose Weil
criterion the stack proves.
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

/-! ## `DHRH ↔ DHRHcross` -/

/-- **`DHRH ↔ DHRHcross`**: on `Re s > 0`, `dh` has no real zero (`dh_ne_zero_of_real`), so a zero on
the cross is on the line. -/
theorem dhRH_iff_cross : DHRH ↔ DHRHcross := by
  constructor
  · intro h s hs h0; exact Or.inl (h s hs h0)
  · intro h s hs h0
    refine (h s hs h0).resolve_right fun him => ?_
    have hsr : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    exact dh_ne_zero_of_real h0 (by rw [← hsr]; exact hs)

/-- `dhRH_of_cross` with its named input `hreal` discharged by `dh_ne_zero_of_real`. -/
theorem dhRH_of_cross' {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hint : ∀ n, IntervalIntegrable (g n) volume (-(a n)) (a n))
    (hcross : ∀ᶠ n in atTop, ∀ z, ghatC (g n) (a n) z = 0 → z.re = 0 ∨ z.im = 0)
    (hconv : HypConvDH a g) : DHRH :=
  dhRH_of_cross hint hcross hconv fun _ hσ => dh_ne_zero_of_real hσ

/-! ## Conjugation symmetry -/

section Conj

open DirichletCharacter

/-- **`dh(s̄) = conj dh(s)`** for every `s`. -/
theorem dh_conj (s : ℂ) : dh ((starRingEnd ℂ) s) = (starRingEnd ℂ) (dh s) := by
  have h1 := conj_LFunction chi5 chi5_ne_one s
  have h2 := conj_LFunction chi5⁻¹ (inv_ne_one.2 chi5_ne_one) s
  rw [inv_inv] at h2
  simp only [dh, dhL, map_add, map_mul, map_one, h1, h2, rootNumber_chi5_inv_eq_conj,
    Complex.conj_conj]
  ring

/-- The zeros of `dh` are symmetric under conjugation. -/
theorem dh_conj_zero {ρ : ℂ} (h : dh ρ = 0) : dh ((starRingEnd ℂ) ρ) = 0 := by
  rw [dh_conj, h, map_zero]

end Conj

/-! ## The parity split of `Q_dh` -/

/-- **The parity split of `Q_dh`**: `Q_dh(φ + ψ) = Q_dh(φ) + Q_dh(ψ)` for `φ` an even and `ψ` an odd
probe at the same support (the `dh` column of `weilQg_parity`; `QDHu` has no pole term). -/
theorem QDHu_add_even_odd {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : OProbe a ψ) :
    QDHu (fun t => φ t + ψ t) = QDHu φ + QDHu ψ := by
  set g : ℝ → ℝ := fun t => φ t + ψ t with hg
  have hgm : MemLp g 2 volume := hφ.memL2.add hψ.memL2
  have he : evenPart g = φ := by
    funext t; simp only [evenPart, hg, hφ.even, hψ.odd]; ring
  have ho : oddPart g = ψ := by
    funext t; simp only [oddPart, hg, hφ.even, hψ.odd]; ring
  have hac : ∀ u, autocorr g u = autocorr φ u + autocorr ψ u := fun u => by
    rw [autocorr_parity hgm u, he, ho]
  have hsupp : ∀ u, a < |u| → g u = 0 := fun u hu => by
    simp only [hg, hφ.supp u hu, hψ.supp u hu, add_zero]
  have hAφ := archIntegrandQ_integrable hφ (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)
  have hAψ := oprobe_archIntegrandQ_integrable hψ (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)
  have hA : archEQ (3 / 4) g = archEQ (3 / 4) φ + archEQ (3 / 4) ψ := by
    unfold archEQ
    rw [← integral_add hAφ hAψ]
    congr 1; funext u
    simp only [archIntegrandQ, hac]; ring
  have hN : normSq g = normSq φ + normSq ψ := by
    simp only [← autocorr_zero, hac]
  rw [QDHu_eq_range hsupp, QDHu_eq_range hφ.supp, QDHu_eq_range hψ.supp, hA, hN]
  simp only [hac, mul_add, Finset.sum_add_distrib]
  ring

/-- **A negative-definite plane of `Q_dh` from the two packet certificates**: every nonzero
combination `c₁·packet + c₂·sinPacket` at `(12/5, 169/2)` has `Q_dh < 0`. -/
theorem QDHu_packet_plane_neg {c₁ c₂ : ℝ} (h : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    QDHu (fun t => c₁ * packet (12 / 5) (169 / 2) t + c₂ * sinPacket (12 / 5) (169 / 2) t) < 0 := by
  have hp := (packet_probe (a := 12 / 5) (ω := 169 / 2) (by norm_num) (by norm_num))
  have hs := (sinPacket_oprobe (a := 12 / 5) (ω := 169 / 2) (by norm_num) (by norm_num))
  have hpc : Probe (12 / 5) (fun t => c₁ * packet (12 / 5) (169 / 2) t) := probe_smul hp c₁
  have hsc : OProbe (12 / 5) (fun t => c₂ * sinPacket (12 / 5) (169 / 2) t) := hs.smul c₂
  rw [QDHu_add_even_odd hpc hsc, QDHu_smul, QDHu_smul]
  have n1 := QDHu_packet_neg
  have n2 := QDHu_sinPacket_neg
  rcases h with h | h
  · have : 0 < c₁ ^ 2 := by positivity
    nlinarith [sq_nonneg c₂]
  · have : 0 < c₂ ^ 2 := by positivity
    nlinarith [sq_nonneg c₁]

/-- An even probe plus an odd probe at the same support is an `SProbe`: the cross terms of the
archimedean integrand cancel (`archIntegrand_parity`). -/
theorem sprobe_add_even_odd {a : ℝ} {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : OProbe a ψ) :
    SProbe a (fun t => φ t + ψ t) := by
  set g : ℝ → ℝ := fun t => φ t + ψ t with hg
  have hgm : MemLp g 2 volume := hφ.memL2.add hψ.memL2
  have he : evenPart g = φ := by
    funext t; simp only [evenPart, hg, hφ.even, hψ.odd]; ring
  have ho : oddPart g = ψ := by
    funext t; simp only [oddPart, hg, hφ.even, hψ.odd]; ring
  refine ⟨fun u hu => by simp only [hg, hφ.supp u hu, hψ.supp u hu, add_zero], hgm, ?_⟩
  have e : archIntegrand g = fun u => archIntegrand φ u + archIntegrand ψ u := by
    funext u; rw [archIntegrand_parity hgm u, he, ho]
  rw [e]; exact hφ.arch.add hψ.arch

/-! ## `QCu χ` is a `ProbeForm`; the χ ground energy -/

section ChiForm

open DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {a : ℝ} {g h : ℝ → ℝ}

theorem QCu_zero : QCu χ (fun _ => 0) = 0 := by
  simp [QCu, Pilot1ca.normSq, archEQ, archIntegrandQ, autocorr]

theorem QCu_smul (g : ℝ → ℝ) (c : ℝ) : QCu χ (fun t => c * g t) = c ^ 2 * QCu χ g := by
  have hS : ∑' n : ℕ, fχ χ n / Real.sqrt n * autocorr (fun t => c * g t) (Real.log n)
      = c ^ 2 * ∑' n : ℕ, fχ χ n / Real.sqrt n * autocorr g (Real.log n) := by
    rw [← tsum_mul_left]; congr 1; funext n; rw [autocorr_smul]; ring
  unfold QCu
  rw [normSq_smul, archEQ_smul, hS]; ring

theorem QCu_add_sub (hg : Probe a g) (hh : Probe a h) :
    QCu χ (fun t => g t + h t) + QCu χ (fun t => g t - h t) = 2 * QCu χ g + 2 * QCu χ h := by
  have e1 := QCu_add_smul (χ := χ) hg hh 1
  have e2 := QCu_add_smul (χ := χ) hg hh (-1)
  have f1 : (fun t => g t + 1 * h t) = fun t => g t + h t := by funext t; ring
  have f2 : (fun t => g t + -1 * h t) = fun t => g t - h t := by funext t; ring
  rw [f1] at e1
  rw [f2] at e2
  rw [e1, e2]; ring

theorem QCu_congr_ae {g g' : ℝ → ℝ} (hgg : g =ᵐ[volume] g') : QCu χ g = QCu χ g' := by
  unfold QCu
  rw [normSq_congr_ae hgg, archEQ_congr_ae (qC χ) hgg]
  simp_rw [autocorr_congr_ae hgg]

/-- **`QCu χ` is a `ProbeForm`** at every support. -/
theorem QCu_form (χ : DirichletCharacter ℂ N) (a : ℝ) : ProbeForm a (QCu χ) where
  zero := QCu_zero
  smul := QCu_smul
  add_sub := QCu_add_sub
  congr_ae := QCu_congr_ae
  bdd := ⟨-MC χ a, by
    rintro q ⟨h, hp, hn, rfl⟩
    have := QCu_ge (χ := χ) hp; rwa [hn, mul_one] at this⟩

/-- **The χ ground energy** `λ_χ(a) = inf {Q_χ(g) : g a probe at support a, ‖g‖ = 1}`. -/
def lamC (χ : DirichletCharacter ℂ N) (a : ℝ) : ℝ := (QCu_form χ a).inf

theorem lamC_le (hp : Probe a h) (hn : normSq h = 1) : lamC χ a ≤ QCu χ h :=
  (QCu_form χ a).inf_le hp hn

/-- `Q_χ(g) − λ_χ‖g‖² ≥ 0` on probes. -/
theorem lamC_mul_le (hg : Probe a g) : lamC χ a * normSq g ≤ QCu χ g :=
  (QCu_form χ a).inf_mul_le hg

/-- **`λ_χ` is non-increasing in the support** (`QCu χ` does not depend on the window). -/
theorem lamC_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : lamC χ b ≤ lamC χ a := by
  show lamC χ b ≤ sInf {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ QCu χ h = q}
  refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
  rintro q ⟨g, hp, hn, rfl⟩
  exact lamC_le (hp.mono hab) hn

end ChiForm

/-! ## GRH(χ) and the χ ground energy (round 329) -/

section ChiGRH

open DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **`Q_χ ≥ 0` on every probe at every support iff `λ_χ ≥ 0` at every support**, for every `χ`
(`QC_eq_QCu`, `lamC_mul_le`). -/
theorem probe_nonneg_iff_lamC_nonneg (χ : DirichletCharacter ℂ N) :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC χ a g) ↔ ∀ a : ℝ, 0 < a → 0 ≤ lamC χ a := by
  constructor
  · intro h a ha
    show 0 ≤ sInf {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ QCu χ h = q}
    refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
    rintro q ⟨g, hp, -, rfl⟩
    rw [← QC_eq_QCu (χ := χ) hp ha]
    exact h a g ha hp
  · intro h a g ha hp
    rw [QC_eq_QCu (χ := χ) hp ha]
    exact (mul_nonneg (h a ha) (normSq_nonneg g)).trans (lamC_mul_le hp)

/-- **Under GRH(χ), `λ_χ ≥ 0` at every support** (the χ column of `lam_nonneg_of_RH`). -/
theorem lamC_nonneg_of_GRH (hG : GoodChar χ) (hGRH : GRH χ) {a : ℝ} (ha : 0 < a) : 0 ≤ lamC χ a :=
  (probe_nonneg_iff_lamC_nonneg χ).1 (fun _ _ ha hp => QC_nonneg_of_GRH_all hG hGRH hp ha) a ha

/-- **GRH(χ) iff `λ_χ ≥ 0` at every support**, given `L(σ, χ) ≠ 0` on `(0, 1)`: round 227's
`weil_criterion_chi` through `probe_nonneg_iff_lamC_nonneg`. -/
theorem grh_iff_lamC_nonneg (hG : GoodChar χ) (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    GRH χ ↔ ∀ a : ℝ, 0 < a → 0 ≤ lamC χ a :=
  (weil_criterion_chi hG hS).symm.trans (probe_nonneg_iff_lamC_nonneg χ)

/-- **GRH(χ) iff `λ_χ ≥ 0` at all large supports**: `λ_χ` is non-increasing (`lamC_antitone`). -/
theorem grh_iff_lamC_eventually_nonneg (hG : GoodChar χ)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    GRH χ ↔ ∀ᶠ a in atTop, 0 ≤ lamC χ a := by
  rw [grh_iff_lamC_nonneg hG hS]
  constructor
  · intro h
    filter_upwards [eventually_gt_atTop 0] with a ha using h a ha
  · intro h a ha
    obtain ⟨A, hA⟩ := eventually_atTop.1 h
    exact (hA (max a A) (le_max_right _ _)).trans (lamC_antitone ha (le_max_left _ _))

/-- **If GRH(χ) fails, `λ_χ` is negative from some support on** (the χ column of
`exists_lam_neg_of_not_RH`; every larger support by `lamC_antitone`). -/
theorem exists_lamC_neg_of_not_GRH (hG : GoodChar χ)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) (h : ¬ GRH χ) :
    ∃ a, 0 < a ∧ ∀ b, a ≤ b → lamC χ b < 0 := by
  rw [grh_iff_lamC_nonneg hG hS] at h
  push Not at h
  obtain ⟨a, ha, hneg⟩ := h
  exact ⟨a, ha, fun b hb => (lamC_antitone ha hb).trans_lt hneg⟩

end ChiGRH

/-! The instances: the characters whose Weil criterion the stack proves (`weil_criterion_chi3`,
`weil_criterion_chi4`, `weil_criterion_chi8`, `WeilTwinGeneral.weil_criterion_chi7`). -/

/-- **GRH for `χ₋₃` iff `λ_{χ₋₃} ≥ 0` at every support.** -/
theorem grh_iff_lamC_nonneg_chi3 : GRH chi3 ↔ ∀ a : ℝ, 0 < a → 0 ≤ lamC chi3 a :=
  weil_criterion_chi3.symm.trans (probe_nonneg_iff_lamC_nonneg chi3)

/-- **GRH for `χ₋₄` iff `λ_{χ₋₄} ≥ 0` at every support.** -/
theorem grh_iff_lamC_nonneg_chi4 : GRH chi4 ↔ ∀ a : ℝ, 0 < a → 0 ≤ lamC chi4 a :=
  weil_criterion_chi4.symm.trans (probe_nonneg_iff_lamC_nonneg chi4)

/-- **GRH for `χ₋₈` iff `λ_{χ₋₈} ≥ 0` at every support.** -/
theorem grh_iff_lamC_nonneg_chi8 : GRH chi8 ↔ ∀ a : ℝ, 0 < a → 0 ≤ lamC chi8 a :=
  weil_criterion_chi8.symm.trans (probe_nonneg_iff_lamC_nonneg chi8)

/-- **GRH for `χ₋₇` iff `λ_{χ₋₇} ≥ 0` at every support.** -/
theorem grh_iff_lamC_nonneg_chi7 :
    GRH WeilTwinGeneral.chi7 ↔ ∀ a : ℝ, 0 < a → 0 ≤ lamC WeilTwinGeneral.chi7 a :=
  WeilTwinGeneral.weil_criterion_chi7.symm.trans (probe_nonneg_iff_lamC_nonneg _)

end PsiOmega

namespace DHNegIndex

open Pilot1ca Pilot1bt PilotWeil PsiOmega

/-- **The Weil index of `Q_dh` on probes of either parity is at least `5`**: a support `b` and a
`5`-dimensional space of `SProbe`s at `b` on which `QDHu` is negative definite. It is the `4`-dimensional
even space of `negIndex_ge_four` plus the sine packet at `(12/5, 169/2)`. -/
theorem negIndex_ge_five : ∃ b, 0 < b ∧ ∃ W : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ W = 5 ∧
    (∀ w ∈ W, SProbe b w) ∧ ∀ w ∈ W, w ≠ 0 → QDHu w < 0 := by
  obtain ⟨a, ha, V, hV, hpr, hneg⟩ := negIndex_ge_four
  set b := max a (12 / 5) with hb
  set s := sinPacket (12 / 5) (169 / 2) with hs_def
  have hs : OProbe b s := (sinPacket_oprobe (by norm_num) (by norm_num)).mono (le_max_right _ _)
  have hsneg : QDHu s < 0 := QDHu_sinPacket_neg
  have hVb : ∀ v ∈ V, Probe b v := fun v hv => (hpr v hv).1.mono (le_max_left _ _)
  have hs0 : s ≠ 0 := by
    intro h
    have h0 : QDHu s = 0 := by rw [h]; exact QDHu_zero
    linarith
  have hsplit : ∀ v ∈ V, ∀ c : ℝ, QDHu (v + c • s) = QDHu v + c ^ 2 * QDHu s := by
    intro v hv c
    have e : v + c • s = fun t => v t + c * s t := by
      funext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, QDHu_add_even_odd (hVb v hv) (hs.smul c), QDHu_smul]
  refine ⟨b, lt_max_of_lt_left ha, V ⊔ Submodule.span ℝ {s}, ?_, ?_, ?_⟩
  · have hdisj : V ⊓ Submodule.span ℝ {s} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      obtain ⟨hwV, hws⟩ := Submodule.mem_inf.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hws
      funext t
      have h1 := (hVb _ hwV).even t
      have h2 := hs.odd t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
      rw [h2] at h1
      linarith
    have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
    have := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span ℝ {s})
    rw [hdisj, finrank_bot, hV, finrank_span_singleton hs0] at this
    omega
  · intro w hw
    obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have e : v + c • s = fun t => v t + c * s t := by
      funext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]; exact sprobe_add_even_odd (hVb v hv) (hs.smul c)
  · intro w hw hw0
    obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [hsplit v hv c]
    by_cases hv0 : v = 0
    · have hc : c ≠ 0 := by
        rintro rfl; apply hw0; rw [hv0, zero_smul, add_zero]
      have hq0 : QDHu v = 0 := by rw [hv0]; exact QDHu_zero
      have : 0 < c ^ 2 := by positivity
      nlinarith
    · have := hneg v hv hv0
      nlinarith [sq_nonneg c]

end DHNegIndex

#print axioms PsiOmega.dhRH_iff_cross
#print axioms PsiOmega.dhRH_of_cross'
#print axioms PsiOmega.dh_conj
#print axioms PsiOmega.dh_conj_zero
#print axioms PsiOmega.QDHu_add_even_odd
#print axioms PsiOmega.QDHu_packet_plane_neg
#print axioms PsiOmega.sprobe_add_even_odd
#print axioms PsiOmega.QCu_form
#print axioms PsiOmega.lamC_antitone
#print axioms DHNegIndex.negIndex_ge_five
#print axioms PsiOmega.probe_nonneg_iff_lamC_nonneg
#print axioms PsiOmega.lamC_nonneg_of_GRH
#print axioms PsiOmega.grh_iff_lamC_nonneg
#print axioms PsiOmega.grh_iff_lamC_eventually_nonneg
#print axioms PsiOmega.exists_lamC_neg_of_not_GRH
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi3
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi4
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi8
#print axioms PsiOmega.grh_iff_lamC_nonneg_chi7
