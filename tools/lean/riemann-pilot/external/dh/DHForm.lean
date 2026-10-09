import Mathlib
import DHCertificate
import Uniqueness
import FourierGap

/-! # Weil's u-space form for `dh` is a `ProbeForm`; the DH ground energy

`QDHu` (DHBridge.lean) is a quadratic form on probes in the sense of Uniqueness.lean's `ProbeForm`:
`Q(0) = 0`, `Q(cg) = c²Q(g)`, the parallelogram law, invariance under a.e. equality, and the lower
bound `Q_dh(g) ≥ −M_dh(a)‖g‖²` with `M_dh(a) = |Re ψ(¾) + log(5/π)| + 2Σ_{n ≤ e^{2a}} |c(n)|/√n`
(`QDHu_ge`: `E_{3/4} ≥ 0`, `|f(log n)| ≤ ‖g‖²`, and `f(log n) = 0` for `n > e^{2a}`). So the
ground energy `λ_dh(a) = inf {Q_dh(g) : g a probe at support a, ‖g‖ = 1}` is defined (`lamDH`),
non-increasing in the support (`lamDH_antitone`: `Q_dh` does not depend on the window), and negative
from `a = 12/5` on (`lamDH_neg`, from the certificate `QDHu_packet_neg`). This is the `dh` column of
`exists_lam_neg_of_not_RH`, unconditional here.
-/

open Real Complex MeasureTheory Set Filter Topology

noncomputable section

namespace PsiOmega

open LandauLaplace Pilot1ca Pilot1bt PilotWeil

variable {a : ℝ} {g h : ℝ → ℝ}

/-- The constant `Re ψ(¾) + log(5/π)` of `QDHu`. -/
def constDH : ℝ := (Complex.digamma (3 / 4 : ℂ)).re + Real.log 5 - Real.log π

/-- Only `n < ⌊e^{2a}⌋ + 1` enter the prime sum of a probe at support `a`. -/
theorem tsum_fDH_eq_range (hsupp : ∀ u, a < |u| → g u = 0) :
    ∑' n : ℕ, fDH n / Real.sqrt n * autocorr g (Real.log n)
      = ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n) :=
  tsum_autocorr_eq (fun n => fDH n / Real.sqrt n) hsupp

/-- `QDHu` with its prime sum made finite. -/
theorem QDHu_eq_range (hsupp : ∀ u, a < |u| → g u = 0) :
    QDHu g = constDH * normSq g + archEQ (3 / 4) g
      - 2 * ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n) := by
  unfold QDHu constDH; rw [tsum_fDH_eq_range hsupp]

/-! ## `QDHu` is a quadratic form on probes -/

theorem QDHu_zero : QDHu (fun _ => 0) = 0 := by
  simp [QDHu, Pilot1ca.normSq, archEQ, archIntegrandQ, autocorr]

theorem archIntegrandQ_smul (q : ℝ) (g : ℝ → ℝ) (c u : ℝ) :
    archIntegrandQ q (fun t => c * g t) u = c ^ 2 * archIntegrandQ q g u := by
  unfold archIntegrandQ; rw [autocorr_smul, autocorr_smul]; ring

theorem archEQ_smul (q : ℝ) (g : ℝ → ℝ) (c : ℝ) :
    archEQ q (fun t => c * g t) = c ^ 2 * archEQ q g := by
  unfold archEQ; rw [← integral_const_mul]; congr 1; funext u; exact archIntegrandQ_smul q g c u

theorem QDHu_smul (g : ℝ → ℝ) (c : ℝ) : QDHu (fun t => c * g t) = c ^ 2 * QDHu g := by
  have hS : ∑' n : ℕ, fDH n / Real.sqrt n * autocorr (fun t => c * g t) (Real.log n)
      = c ^ 2 * ∑' n : ℕ, fDH n / Real.sqrt n * autocorr g (Real.log n) := by
    rw [← tsum_mul_left]; congr 1; funext n; rw [autocorr_smul]; ring
  unfold QDHu
  rw [normSq_smul, archEQ_smul, hS]; ring

/-- The parallelogram law for `E_q`, `q ≥ ¼`. -/
theorem archEQ_add_sub {q : ℝ} (hq : 1 / 4 ≤ q) (hg : Probe a g) (hh : Probe a h) :
    archEQ q (fun t => g t + h t) + archEQ q (fun t => g t - h t)
      = 2 * archEQ q g + 2 * archEQ q h := by
  have e1 := archEQ_add_smul hg hh hq 1
  have e2 := archEQ_add_smul hg hh hq (-1)
  have f1 : (fun t => g t + 1 * h t) = fun t => g t + h t := by funext t; ring
  have f2 : (fun t => g t + -1 * h t) = fun t => g t - h t := by funext t; ring
  rw [f1] at e1
  rw [f2] at e2
  rw [e1, e2]; ring

/-- **The parallelogram law for `QDHu`.** -/
theorem QDHu_add_sub (hg : Probe a g) (hh : Probe a h) :
    QDHu (fun t => g t + h t) + QDHu (fun t => g t - h t) = 2 * QDHu g + 2 * QDHu h := by
  obtain ⟨hp, hm⟩ := probe_add_sub hg hh
  have hN := normSq_add_sub hg.memL2 hh.memL2
  have hA := archEQ_add_sub (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4) hg hh
  have hS : ∑ n ∈ Finset.range (primeCut a),
        fDH n / Real.sqrt n * autocorr (fun t => g t + h t) (Real.log n)
      + ∑ n ∈ Finset.range (primeCut a),
        fDH n / Real.sqrt n * autocorr (fun t => g t - h t) (Real.log n)
      = 2 * ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n)
        + 2 * ∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr h (Real.log n) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have := autocorr_add_sub hg.memL2 hh.memL2 (Real.log n)
    linear_combination (fDH n / Real.sqrt n) * this
  rw [QDHu_eq_range hp.supp, QDHu_eq_range hm.supp, QDHu_eq_range hg.supp, QDHu_eq_range hh.supp]
  linear_combination constDH * hN + hA - 2 * hS

theorem archEQ_congr_ae (q : ℝ) {g g' : ℝ → ℝ} (hgg : g =ᵐ[volume] g') :
    archEQ q g = archEQ q g' := by
  have e : archIntegrandQ q g = archIntegrandQ q g' := by
    funext u; unfold archIntegrandQ; rw [autocorr_congr_ae hgg 0, autocorr_congr_ae hgg u]
  unfold archEQ; rw [e]

theorem QDHu_congr_ae {g g' : ℝ → ℝ} (hgg : g =ᵐ[volume] g') : QDHu g = QDHu g' := by
  unfold QDHu
  rw [normSq_congr_ae hgg, archEQ_congr_ae (3 / 4) hgg]
  simp_rw [autocorr_congr_ae hgg]

/-! ## The lower bound -/

/-- `M_dh(a) = |Re ψ(¾) + log(5/π)| + 2Σ_{n ≤ e^{2a}} |c(n)|/√n`. -/
def MDH (a : ℝ) : ℝ := |constDH| + 2 * ∑ n ∈ Finset.range (primeCut a), |fDH n / Real.sqrt n|

/-- `|Σ c(n) n^{−1/2} f(log n)| ≤ (Σ |c(n)|/√n)‖g‖²` for any square-integrable `g`. -/
theorem abs_primeDH_le_of_memLp {a : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    |∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n)|
      ≤ (∑ n ∈ Finset.range (primeCut a), |fDH n / Real.sqrt n|) * normSq g := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_autocorr_le hg _) (abs_nonneg _)

theorem abs_primeDH_le (hp : Probe a g) :
    |∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n * autocorr g (Real.log n)|
      ≤ (∑ n ∈ Finset.range (primeCut a), |fDH n / Real.sqrt n|) * normSq g :=
  abs_primeDH_le_of_memLp hp.memL2

/-- **`Q_dh(g) ≥ −M_dh(a)‖g‖²`** for every square-integrable `g` vanishing outside `[−a, a]` (round
333): probes, odd probes and the `SProbe`s alike. -/
theorem QDHu_ge_of_supp (hsupp : ∀ u, a < |u| → g u = 0) (hg : MemLp g 2 volume) :
    -(MDH a * normSq g) ≤ QDHu g := by
  rw [QDHu_eq_range hsupp]
  have hN := normSq_nonneg g
  have hE := archEQ_nonneg (3 / 4) hg
  have hP := abs_primeDH_le_of_memLp (a := a) hg
  have hc : -(|constDH| * normSq g) ≤ constDH * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hN
  unfold MDH
  nlinarith [le_abs_self (∑ n ∈ Finset.range (primeCut a), fDH n / Real.sqrt n
    * autocorr g (Real.log n))]

/-- **`Q_dh(g) ≥ −M_dh(a)‖g‖²`** on probes at support `a` (`QDHu_ge_of_supp`). -/
theorem QDHu_ge (hp : Probe a g) : -(MDH a * normSq g) ≤ QDHu g := QDHu_ge_of_supp hp.supp hp.memL2

/-! ## The ground energy -/

/-- **`QDHu` is a `ProbeForm`** at every support. -/
theorem QDHu_form (a : ℝ) : ProbeForm a QDHu where
  zero := QDHu_zero
  smul := QDHu_smul
  add_sub := QDHu_add_sub
  congr_ae := QDHu_congr_ae
  bdd := ⟨-MDH a, by
    rintro q ⟨h, hp, hn, rfl⟩
    have := QDHu_ge hp; rwa [hn, mul_one] at this⟩

/-- **The DH ground energy** `λ_dh(a) = inf {Q_dh(g) : g a probe at support a, ‖g‖ = 1}`. -/
noncomputable def lamDH (a : ℝ) : ℝ := (QDHu_form a).inf

theorem lamDH_le {a : ℝ} {h : ℝ → ℝ} (hp : Probe a h) (hn : normSq h = 1) : lamDH a ≤ QDHu h :=
  (QDHu_form a).inf_le hp hn

/-- `Q_dh(g) − λ_dh‖g‖² ≥ 0` on probes. -/
theorem lamDH_mul_le {a : ℝ} {g : ℝ → ℝ} (hg : Probe a g) : lamDH a * normSq g ≤ QDHu g :=
  (QDHu_form a).inf_mul_le hg

/-- **`λ_dh` is non-increasing in the support.** -/
theorem lamDH_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : lamDH b ≤ lamDH a := by
  show lamDH b ≤ sInf {q | ∃ h, Probe a h ∧ normSq h = 1 ∧ QDHu h = q}
  refine le_csInf ⟨_, box a, box_probe a, normSq_box ha, rfl⟩ ?_
  rintro q ⟨g, hp, hn, rfl⟩
  exact lamDH_le (hp.mono hab) hn

/-- **`λ_dh(b) < 0` for every `b ≥ 12/5`**, from the certificate `Q_dh(packet 12/5 169/2) < 0`. -/
theorem lamDH_neg {b : ℝ} (hb : 12 / 5 ≤ b) : lamDH b < 0 := by
  have hp := packet_probe (a := 12 / 5) (ω := 169 / 2) (by norm_num) (by norm_num)
  have h1 := lamDH_mul_le hp
  have hneg := QDHu_packet_neg
  have h2 : lamDH (12 / 5) < 0 := by
    by_contra hc
    have := mul_nonneg (not_lt.1 hc) (normSq_nonneg (packet (12 / 5) (169 / 2)))
    linarith
  exact (lamDH_antitone (by norm_num) hb).trans_lt h2

theorem not_lamDH_nonneg : ¬ ∀ a : ℝ, 0 < a → 0 ≤ lamDH a := fun h =>
  absurd (h (12 / 5) (by norm_num)) (not_le.2 (lamDH_neg le_rfl))

/-- **The `dh` column of `exists_lam_neg_of_not_RH`, unconditional.** -/
theorem exists_lamDH_neg : ∃ a, 0 < a ∧ lamDH a < 0 :=
  ⟨12 / 5, by norm_num, lamDH_neg le_rfl⟩

end PsiOmega

#print axioms PsiOmega.QDHu_form
#print axioms PsiOmega.lamDH_antitone
#print axioms PsiOmega.lamDH_neg
#print axioms PsiOmega.exists_lamDH_neg
