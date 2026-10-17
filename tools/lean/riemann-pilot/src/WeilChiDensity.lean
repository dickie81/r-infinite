import Mathlib
import WeilChiBridge
import WeilRH

/-! # GRH(χ) gives `Q_χ ≥ 0` on every probe (round 227)

Round 225's `QC_nonneg_of_GRH` needs the explicit formula for the probe at hand, so it covers only
probes whose `ĝ²` is a strip test function. Here the gap is closed by density, as round 157 closed it
for ζ, but without ground states:

* `QCu_add_smul`: `Q_χ` (in u-space, round 226) is a quadratic form with bilinear form `BC`.
* `QCu_ge`, `QCu_le`: `−M‖g‖² ≤ Q_χ(g) ≤ M‖g‖² + E(g)`, where `M` is `|Re ψ(q_χ) + log(N/π)|` plus
  twice the prime weights up to `e^{2a}`. The upper bound uses `E_{q_χ} ≤ E` (`q_χ ≥ ¼`).
* `RC_add_le`: Cauchy–Schwarz for the nonnegative form `R = Q_χ + M‖·‖²`.
* `QC_nonneg_of_GRH_all`: if `Q_χ(g) = −η < 0`, round 55's `av3_dense` gives a `C²` probe `h` with
  `‖h − g‖² + E(h − g)` small. Then `ĝ_h²` is a strip test function (`striptest_C2`), so GRH gives
  `Q_χ(h) ≥ 0`, while continuity gives `Q_χ(h) ≤ −η/4`.
* `weil_criterion_chi`: with `L(σ, χ) ≠ 0` on `(0, 1)`, GRH(χ) holds iff `Q_χ ≥ 0` on every probe at
  every support. Instances for `χ₋₃`, `χ₋₄`, `χ₋₈`.
* `grh_iff_QC_subexp_all`: round 225's rate form, over all probes.

Weil's criterion is an equivalence: no bearing on GRH.
-/

open Real Complex MeasureTheory Filter Set

noncomputable section

namespace PsiOmega

open DirichletCharacter Pilot1ca Pilot1bt

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {a : ℝ}

/-! ## `Q_χ` as a quadratic form -/

/-- The constant `Re ψ(q_χ) + log(N/π)`. -/
def cChi (χ : DirichletCharacter ℂ N) : ℝ := (Complex.digamma (qC χ)).re + Real.log N - Real.log π

/-- `Q_χ^u` with its prime sum made finite. -/
theorem QCu_eq {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0) :
    QCu χ g = cChi χ * normSq g + archEQ (qC χ) g
      - 2 * ∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n * autocorr g (Real.log n) := by
  unfold QCu cChi; rw [tsum_autocorr_eq (fun n => fχ χ n / Real.sqrt n) hsupp]

/-- The bilinear form of `Q_χ`. -/
def BC (χ : DirichletCharacter ℂ N) (a : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  cChi χ * xcorr φ ψ 0 + (∫ u in Ioi 0, archXQ (qC χ) φ ψ u)
    - 2 * ∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n * xcorr φ ψ (Real.log n)

theorem QCu_add_smul {φ ψ : ℝ → ℝ} (hφ : Probe a φ) (hψ : Probe a ψ) (s : ℝ) :
    QCu χ (fun t => φ t + s * ψ t) = QCu χ φ + 2 * s * BC χ a φ ψ + s ^ 2 * QCu χ ψ := by
  rw [QCu_eq (probe_add_smul hφ hψ s).supp, QCu_eq hφ.supp, QCu_eq hψ.supp,
    normSq_add_smul hφ.memL2 hψ.memL2, archEQ_add_smul hφ hψ quarter_le_qC]
  have hS : ∑ n ∈ Finset.range (primeCut a),
        fχ χ n / Real.sqrt n * autocorr (fun t => φ t + s * ψ t) (Real.log n)
      = ∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n * autocorr φ (Real.log n)
        + 2 * s * ∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n * xcorr φ ψ (Real.log n)
        + s ^ 2 * ∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n * autocorr ψ (Real.log n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [autocorr_add_smul hφ.memL2 hψ.memL2]; ring
  rw [hS]; unfold BC; ring

/-! ## Bounds by `L²` norm and archimedean energy -/

/-- `M = |c_χ| + 2Σ_{n ≤ e^{2a}} |Λ(n)χ(n)|/√n`. -/
def MC (χ : DirichletCharacter ℂ N) (a : ℝ) : ℝ :=
  |cChi χ| + 2 * ∑ n ∈ Finset.range (primeCut a), |fχ χ n / Real.sqrt n|

omit [NeZero N] in
theorem MC_nonneg : 0 ≤ MC χ a := by
  unfold MC
  have := Finset.sum_nonneg fun n (_ : n ∈ Finset.range (primeCut a)) => abs_nonneg (fχ χ n / Real.sqrt n)
  positivity

omit [NeZero N] in
theorem abs_primeC_le {g : ℝ → ℝ} (hp : Probe a g) :
    |∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n * autocorr g (Real.log n)|
      ≤ (∑ n ∈ Finset.range (primeCut a), |fχ χ n / Real.sqrt n|) * normSq g := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_autocorr_le hp.memL2 _) (abs_nonneg _)

/-- `Q_χ(g) ≥ −M‖g‖²`. -/
theorem QCu_ge {g : ℝ → ℝ} (hp : Probe a g) : -(MC χ a * normSq g) ≤ QCu χ g := by
  rw [QCu_eq hp.supp]
  have hN := normSq_nonneg g
  have hE := archEQ_nonneg (qC χ) hp.memL2
  have hP := abs_primeC_le (χ := χ) hp
  have hc : -(|cChi χ| * normSq g) ≤ cChi χ * normSq g := by
    rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hN
  unfold MC
  nlinarith [le_abs_self (∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n
    * autocorr g (Real.log n))]

/-- `Q_χ(g) ≤ M‖g‖² + E(g)`. -/
theorem QCu_le {g : ℝ → ℝ} (hp : Probe a g) : QCu χ g ≤ MC χ a * normSq g + archE g := by
  rw [QCu_eq hp.supp]
  have hN := normSq_nonneg g
  have hE := archEQ_le_archE hp (quarter_le_qC (χ := χ))
  have hP := abs_primeC_le (χ := χ) hp
  have hc : cChi χ * normSq g ≤ |cChi χ| * normSq g := mul_le_mul_of_nonneg_right (le_abs_self _) hN
  unfold MC
  nlinarith [le_abs_self (∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n
    * autocorr g (Real.log n)), neg_abs_le (∑ n ∈ Finset.range (primeCut a), fχ χ n / Real.sqrt n
    * autocorr g (Real.log n))]

/-- `R(x + y) ≤ (1 + t)R(x) + (1 + 1/t)R(y)` for `R = Q_χ + M‖·‖² ≥ 0` (Cauchy–Schwarz). -/
theorem RC_add_le {x y : ℝ → ℝ} (hx : Probe a x) (hy : Probe a y) {t : ℝ} (ht : 0 < t) :
    QCu χ (fun u => x u + 1 * y u) + MC χ a * normSq (fun u => x u + 1 * y u)
      ≤ (1 + t) * (QCu χ x + MC χ a * normSq x) + (1 + 1 / t) * (QCu χ y + MC χ a * normSq y) := by
  set M := MC χ a
  have eR : ∀ s : ℝ, QCu χ (fun u => x u + s * y u) + M * normSq (fun u => x u + s * y u)
      = (QCu χ x + M * normSq x) + 2 * s * (BC χ a x y + M * xcorr x y 0)
        + s ^ 2 * (QCu χ y + M * normSq y) := fun s => by
    rw [QCu_add_smul hx hy, normSq_add_smul hx.memL2 hy.memL2]; ring
  have n2 := QCu_ge (χ := χ) (probe_add_smul hx hy (-(1 / t)))
  have hRx : 0 ≤ QCu χ x + M * normSq x := by linarith [QCu_ge (χ := χ) hx]
  have hRy : 0 ≤ QCu χ y + M * normSq y := by linarith [QCu_ge (χ := χ) hy]
  have e2 := eR (-(1 / t))
  set B := BC χ a x y + M * xcorr x y 0
  set Rx := QCu χ x + M * normSq x
  set Ry := QCu χ y + M * normSq y
  have h0 : 0 ≤ Rx + 2 * -(1 / t) * B + (-(1 / t)) ^ 2 * Ry := by rw [← e2]; linarith
  have hB : 2 * B ≤ t * Rx + Ry / t := by
    have h1 : 0 ≤ t * (Rx + 2 * -(1 / t) * B + (-(1 / t)) ^ 2 * Ry) := mul_nonneg ht.le h0
    have : t * (Rx + 2 * -(1 / t) * B + (-(1 / t)) ^ 2 * Ry) = t * Rx - 2 * B + Ry / t := by
      field_simp; ring
    linarith
  have : (1 + 1 / t) * Ry = Ry + Ry / t := by field_simp
  rw [eR 1]; nlinarith

/-! ## Density -/

/-- The arithmetic of the density step. With `t(P + η) = η/6`, `t ≤ 1`, and the approximation error
`A` small, the two continuity bounds force `Q < 0`. -/
theorem density_arith {η M P t A Q X : ℝ} (hη : 0 < η) (hM : 0 ≤ M) (hP : 0 ≤ P) (ht : 0 < t)
    (ht1 : t ≤ 1) (htP : t * (P + η) = η / 6) (hA0 : 0 ≤ A)
    (hA4 : (1 + t) * (3 * M + 1) * A ≤ η / 4)
    (k1 : Q + X ≤ (1 + t) * (-η + P) + (2 * M + 1) * A) (k2 : P ≤ (1 + t) * X + M * A) : Q < 0 := by
  have e1 : (1 + t) * Q ≤ (1 + t) * ((1 + t) * (-η + P) + (2 * M + 1) * A - X) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have f1 : 0 ≤ t * η := mul_nonneg ht.le hη.le
  have f2 : 0 ≤ t * t * η := mul_nonneg (mul_nonneg ht.le ht.le) hη.le
  have e3 : t * t * P ≤ t * P := by
    nlinarith [mul_nonneg (mul_nonneg ht.le hP) (sub_nonneg.2 ht1)]
  have f3 : 0 ≤ t * M * A := mul_nonneg (mul_nonneg ht.le hM) hA0
  have key : (1 + t) * Q ≤ -η / 4 := by nlinarith
  nlinarith

variable (hG : GoodChar χ)
include hG

/-- **GRH(χ) ⟹ `Q_χ ≥ 0` on every probe.** -/
theorem QC_nonneg_of_GRH_all (hGRH : GRH χ) {g : ℝ → ℝ} (hp : Probe a g) (ha : 0 < a) :
    0 ≤ QC χ a g := by
  rw [QC_eq_QCu hp ha]
  by_contra hneg
  push Not at hneg
  have hN0 := normSq_nonneg g
  obtain ⟨M, hMd⟩ : ∃ M, M = MC χ a := ⟨_, rfl⟩
  have hM : 0 ≤ M := hMd ▸ MC_nonneg
  obtain ⟨η, hηd⟩ : ∃ η, η = -QCu χ g := ⟨_, rfl⟩
  have hη : 0 < η := by linarith
  obtain ⟨P, hPd⟩ : ∃ P, P = M * normSq g := ⟨_, rfl⟩
  have hP : 0 ≤ P := hPd ▸ mul_nonneg hM hN0
  have hPη : 0 < 6 * (P + η) := by linarith
  obtain ⟨t, htd⟩ : ∃ t, t = η / (6 * (P + η)) := ⟨_, rfl⟩
  have ht : 0 < t := htd ▸ div_pos hη hPη
  have htP : t * (P + η) = η / 6 := by rw [htd]; field_simp
  have ht1 : t ≤ 1 := by rw [htd, div_le_one hPη]; linarith
  have h1t : (1 + t) ≠ 0 := by linarith
  have h5M : (5 * M + 4) ≠ 0 := by linarith
  have hden : 0 < 8 * (1 + t) * (5 * M + 4) := by positivity
  obtain ⟨ε, hεd⟩ : ∃ ε, ε = η * t / (8 * (1 + t) * (5 * M + 4)) := ⟨_, rfl⟩
  have hε : 0 < ε := hεd ▸ div_pos (mul_pos hη ht) hden
  obtain ⟨ρ, δ, ψ, hρ0, hδ, hρ, hψ, h1, h2⟩ := av3_dense ha hp ε hε
  have hph : Probe a (Av δ (Av δ (Av δ ψ))) :=
    (probe_Av (probe_Av (probe_Av hψ hδ) hδ) hδ).mono (by linarith)
  obtain ⟨K, hK⟩ := striptest_C2 ha hph (av3_C2 hδ hψ) (by positivity) hρ
  have hQh : 0 ≤ QCu χ (Av δ (Av δ (Av δ ψ))) := by
    rw [← QC_eq_QCu hph ha]; exact QC_nonneg_of_GRH hG hGRH hph ha hK
  generalize Av δ (Av δ (Av δ ψ)) = h at hph hQh h1 h2
  have pe : Probe a (fun u => h u - g u) := (probe_add_sub hph hp).2
  have hfun : (fun u => g u + 1 * (h u - g u)) = h := by funext u; ring
  have hR := RC_add_le (χ := χ) hp pe ht
  rw [hfun, ← hMd] at hR
  have hRe : QCu χ (fun u => h u - g u) + M * normSq (fun u => h u - g u) ≤ (2 * M + 1) * ε := by
    have hq := QCu_le (χ := χ) pe
    rw [← hMd] at hq
    have := mul_le_mul_of_nonneg_left h1 hM
    nlinarith
  -- `‖g‖² ≤ (1 + t)‖h‖² + (1 + 1/t)‖h − g‖²`
  have hN := normSq_add_le_t (x := h) (y := fun u => g u - h u) hph.memL2
    (hp.memL2.sub hph.memL2) ht
  have hfun2 : (fun u => h u + (g u - h u)) = g := by funext u; ring
  rw [hfun2, normSq_sub_comm] at hN
  obtain ⟨A, hAd⟩ : ∃ A, A = (1 + 1 / t) * ε := ⟨_, rfl⟩
  have hs : 0 ≤ 1 + 1 / t := by positivity
  have hA : A = η / (8 * (5 * M + 4)) := by
    rw [hAd, hεd]; field_simp; ring
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA4 : (1 + t) * (3 * M + 1) * A ≤ η / 4 := by
    have hb : (1 + t) * (3 * M + 1) ≤ 2 * (5 * M + 4) := by nlinarith
    rw [hA, show (1 + t) * (3 * M + 1) * (η / (8 * (5 * M + 4)))
      = (1 + t) * (3 * M + 1) * η / (8 * (5 * M + 4)) by ring, div_le_iff₀ (by positivity)]
    nlinarith
  have k1 : QCu χ h + M * normSq h ≤ (1 + t) * (-η + P) + (2 * M + 1) * A := by
    have hm := mul_le_mul_of_nonneg_left hRe hs
    have e1 : (1 + 1 / t) * ((2 * M + 1) * ε) = (2 * M + 1) * A := by rw [hAd]; ring
    have e2 : QCu χ g + M * normSq g = -η + P := by rw [hηd, hPd]; ring
    rw [e2] at hR
    linarith
  have k2 : P ≤ (1 + t) * (M * normSq h) + M * A := by
    have hm := mul_le_mul_of_nonneg_left h1 hs
    have hN' : normSq g ≤ (1 + t) * normSq h + (1 + 1 / t) * ε := by linarith
    have hm2 := mul_le_mul_of_nonneg_left hN' hM
    have e1 : M * ((1 + t) * normSq h + (1 + 1 / t) * ε) = (1 + t) * (M * normSq h) + M * A := by
      rw [hAd]; ring
    rw [hPd]; linarith
  exact absurd hQh (not_le.2 (density_arith hη hM hP ht ht1 htP hA0 hA4 k1 k2))

omit hG in
theorem probe_twin_box {l : ℝ} (hl : 0 ≤ l) : Probe (l + 1) (twin (box 1) l) :=
  twin_probe (box_probe 1) hl

/-- **Weil's criterion for `L(s, χ)`, over every probe.** With `L(σ, χ) ≠ 0` on `(0, 1)`: GRH for `χ`
holds iff `Q_χ ≥ 0` on every probe at every support. -/
theorem weil_criterion_chi (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC χ a g) ↔ GRH χ :=
  ⟨fun h => (grh_iff_twins hG hS).2 fun l hl => h _ _ (by linarith) (probe_twin_box hl),
    fun hGRH _ _ ha hp => QC_nonneg_of_GRH_all hG hGRH hp ha⟩

/-- **The rate form over every probe**: GRH(χ) ⟺ for every `σ > 0`,
`Q_χ(g) ≥ −C_σe^{σa}‖g‖²` for every probe at every support `a ≥ 1`. -/
theorem grh_iff_QC_subexp_all (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    GRH χ ↔ ∀ σ > 0, ∃ C, ∀ a, 1 ≤ a → ∀ g, Probe a g →
      -(C * Real.exp (σ * a)) * normSq g ≤ QC χ a g := by
  constructor
  · intro hGRH σ _
    exact ⟨0, fun a ha g hg => by simpa using QC_nonneg_of_GRH_all hG hGRH hg (by linarith)⟩
  · intro h
    refine (grh_iff_QC_subexp hG hS).2 fun σ hσ => ?_
    obtain ⟨C, hC⟩ := h σ hσ
    exact ⟨C, fun a ha g hg => hC a ha g hg.1⟩

omit hG in
theorem weil_criterion_chi3 :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC chi3 a g) ↔ GRH chi3 :=
  weil_criterion_chi good_chi3 fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi3_ne_one chi3_isQuadratic sums_chi3 hσ

omit hG in
theorem weil_criterion_chi4 :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC chi4 a g) ↔ GRH chi4 :=
  weil_criterion_chi good_chi4 fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi4_ne_one chi4_isQuadratic sums_chi4 hσ

omit hG in
theorem weil_criterion_chi8 :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC chi8 a g) ↔ GRH chi8 :=
  weil_criterion_chi good_chi8 fun _ hσ _ =>
    LFunction_ne_zero_of_sums_nonneg chi8_ne_one chi8_isQuadratic sums_chi8 hσ

end PsiOmega

#print axioms PsiOmega.QCu_add_smul
#print axioms PsiOmega.QCu_ge
#print axioms PsiOmega.QCu_le
#print axioms PsiOmega.RC_add_le
#print axioms PsiOmega.QC_nonneg_of_GRH_all
#print axioms PsiOmega.weil_criterion_chi
#print axioms PsiOmega.grh_iff_QC_subexp_all
#print axioms PsiOmega.weil_criterion_chi3
#print axioms PsiOmega.weil_criterion_chi4
#print axioms PsiOmega.weil_criterion_chi8
