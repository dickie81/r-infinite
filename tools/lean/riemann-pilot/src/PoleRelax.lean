import Mathlib
import SmallPositivity2
import WindowForm

/-! # Past `λ₀ = 0`: the pole term through a finite relaxation (round 122, part 2)

Round 121's method uses `Q ≥ Q₀` and stops at `a ≈ 0.105`, where `Q₀` turns negative. Past that point, Weil
positivity depends on the pole term. This file proves a **full-space** lower bound that keeps it.

**The relaxation (exact on the full space).** For a normalised even probe `g`, with `2a < log 2`, round 20's mode
expansion gives
`Q(g) ≥ κ + Σᵢ sᵢ xᵢ²`, where:
* `κ = c₀ + Far(a) + τ`;
* `x₀ = ∫ g cosh(t/2) = ĝ(i/2)`, with `s₀ = 2` (the pole term);
* `x_{k+1} = ∫ g cos(πkt/4a)`, with `s₁ = −τ/(8a)` and `s_{k+1} = 2(ψ̲_k − τ)/(8a)`.

`κ‖g‖² + xᵀ diag(s) x ≥ 0` is guaranteed by a **finite** matrix condition (`quad_lower`). If the Gram matrix
`G` of `(cosh(t/2), cos(πkt/4a))` on `[−a, a]` is positive definite and
`M = (κ − ε)G + G diag(s) G ⪰ 0`, then `Q(g) ≥ ε`. This is because Bessel's inequality (`bessel_gram`) gives
`yᵀGy ≤ ‖g‖²` for `y = G⁻¹x`. No truncation of `g` is involved.

**What is proved here, and what is computed.**
* Proved in Lean:
  - the reduction `weilQ_ge_of_cert`, for any number of modes;
  - closed forms for every Gram entry;
  - the explicit rational tail and low-mode data (`N = 6`).
* Certified by arb interval arithmetic (`frontier/nullvec/kpole_cert.py`): the hypotheses `G ≻ 0` and `M ⪰ 0`
  at the single point `a = 1/4` (`Cert14`). Monotonicity in the support (`weilQ_mono`) carries the bound to
  every `0 < a ≤ 1/4`. Every quantity arb evaluates is defined in this file by a closed form
  proved here, or proved in `SmallPositivity*.lean` (`weilConst_eq`, `farField_eq`).
-/

open Real Filter Topology Complex MeasureTheory Set Matrix

noncomputable section

namespace Pilot1ca

open WindowForm

/-! ## A. The finite-dimensional step -/

/-- **From a Gram certificate to a lower bound.** If `G ≻ 0`, the Bessel inequality
`2 yᵀx − yᵀGy ≤ nrm` holds for every `y`, `ε ≤ κ`, and `(κ − ε)G + G diag(s) G ⪰ 0`, then
`ε·nrm ≤ κ·nrm + Σ sᵢ xᵢ²`. -/
theorem quad_lower {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosDef) (s x : Fin m → ℝ)
    {κ ε nrm : ℝ} (hbessel : ∀ y : Fin m → ℝ, 2 * (y ⬝ᵥ x) - y ⬝ᵥ (G *ᵥ y) ≤ nrm) (hκ : ε ≤ κ)
    (hM : ((κ - ε) • G + G * diagonal s * G).PosSemidef) :
    ε * nrm ≤ κ * nrm + x ⬝ᵥ (diagonal s *ᵥ x) := by
  have hu : IsUnit G.det := (isUnit_iff_isUnit_det G).mp hG.isUnit
  set y := G⁻¹ *ᵥ x with hy
  have hx : G *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hsym : Gᵀ = G := by
    have := hG.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hyGy : y ⬝ᵥ (G *ᵥ y) = y ⬝ᵥ x := by rw [hx]
  have hb := hbessel y
  rw [hyGy] at hb
  -- x ⬝ D x = y ⬝ (G D G) y
  have hq : y ⬝ᵥ ((G * diagonal s * G) *ᵥ y) = x ⬝ᵥ (diagonal s *ᵥ x) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← mulVec_transpose, hsym, hx]
  have h0 := hM.dotProduct_mulVec_nonneg y
  simp only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at h0
  rw [hq, hyGy] at h0
  nlinarith

/-! ## B. Bessel's inequality for the window vectors -/

/-- The window vectors: `v₀ = cosh(t/2)`, `v_{k+1} = cos(πkt/4a)`. -/
def vv (a : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => Real.cosh (t / 2)
  | k + 1 => fun t => Real.cos (π * k * t / (4 * a))

theorem vv_cont (a : ℝ) (i : ℕ) : Continuous (vv a i) := by
  cases i with
  | zero => simp only [vv]; fun_prop
  | succ k => simp only [vv]; fun_prop

/-- The Gram matrix on `[−a, a]`. -/
def gramM (a : ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∫ t in (-a)..a, vv a i t * vv a j t

/-- The coefficients `xᵢ = ∫ g vᵢ`. -/
def xv (a : ℝ) (g : ℝ → ℝ) (m : ℕ) : Fin m → ℝ := fun i => ∫ t, g t * vv a i t

theorem memLp_ind (a : ℝ) (i : ℕ) : MemLp ((Icc (-a) a).indicator (vv a i)) 2 volume := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -a) (b := a)).exists_bound_of_continuousOn (vv_cont a i).continuousOn
  exact memLp_indicator_of_continuous (vv_cont a i) measurableSet_Icc measure_Icc_lt_top.ne
    (C := C) fun x hx => by simpa [Real.norm_eq_abs] using hC x hx

theorem ind_eq_of_supp {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hsupp : ∀ u, a < |u| → g u = 0) (h : ℝ → ℝ) (t : ℝ) :
    g t * (Icc (-a) a).indicator h t = g t * h t := by
  by_cases ht : t ∈ Icc (-a) a
  · simp [ht]
  · have : a < |t| := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h' | h'
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h'
    simp [ht, hsupp t this]

theorem ind_mul_ind (a : ℝ) (i j : ℕ) (ha : 0 ≤ a) :
    (∫ t, (Icc (-a) a).indicator (vv a i) t * (Icc (-a) a).indicator (vv a j) t)
      = ∫ t in (-a)..a, vv a i t * vv a j t := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  congr 1; funext t
  by_cases ht : t ∈ Icc (-a) a <;> simp [ht]

/-- **Bessel's inequality**: `2 yᵀx − yᵀGy ≤ ‖g‖²` for every `y`, from `∫(g − Σ yᵢ vᵢ)² ≥ 0`. -/
theorem bessel_gram {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    (hsupp : ∀ u, a < |u| → g u = 0) (m : ℕ) (y : Fin m → ℝ) :
    2 * (y ⬝ᵥ xv a g m) - y ⬝ᵥ (gramM a m *ᵥ y) ≤ normSq g := by
  set hI : Fin m → ℝ → ℝ := fun i => (Icc (-a) a).indicator (vv a i) with hhI
  have hmem : ∀ i, MemLp (hI i) 2 volume := fun i => memLp_ind a i
  set H : ℝ → ℝ := fun t => ∑ i, y i * hI i t with hH
  have hHmem : MemLp H 2 volume := memLp_finsetSum _ fun i _ => (hmem i).const_mul (y i)
  have hq : 0 ≤ ∫ t, (g t - H t) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have iG := hg.integrable_sq
  have iH := hHmem.integrable_sq
  have iGH := integrable_mul₂ hg hHmem
  have hgH : (∫ t, g t * H t) = y ⬝ᵥ xv a g m := by
    have : (fun t => g t * H t) = fun t => ∑ i, y i * (g t * hI i t) := by
      funext t; simp only [hH, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, integral_finsetSum _ fun i _ => (integrable_mul₂ hg (hmem i)).const_mul (y i)]
    simp only [integral_const_mul, dotProduct, xv]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; congr 1; funext t; exact ind_eq_of_supp ha hsupp _ t
  have hHH : (∫ t, H t ^ 2) = y ⬝ᵥ (gramM a m *ᵥ y) := by
    have : (fun t => H t ^ 2) = fun t => ∑ i, ∑ j, y i * y j * (hI i t * hI j t) := by
      funext t; simp only [hH, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_mul₂ (hmem i) (hmem j)).const_mul _]
    simp only [dotProduct, mulVec, gramM, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (integrable_mul₂ (hmem i) (hmem j)).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, ind_mul_ind a i j ha]; ring
  have e3 : (∫ t, (g t - H t) ^ 2) = normSq g - 2 * (∫ t, g t * H t) + ∫ t, H t ^ 2 := by
    have i2 : Integrable (fun t => 2 * (g t * H t)) := iGH.const_mul _
    have ef : (fun t => (g t - H t) ^ 2) = fun t => g t ^ 2 - 2 * (g t * H t) + H t ^ 2 := by
      funext t; ring
    have i3 : Integrable (fun t => g t ^ 2 - 2 * (g t * H t)) := iG.sub i2
    rw [ef, integral_add i3 iH, integral_sub iG i2, integral_const_mul]
    unfold normSq; ring
  rw [e3, hgH, hHH] at hq
  linarith

/-! ## C. The exact lower bound `Q ≥ κ + xᵀ diag(s) x` -/

theorem sum_Icc_even (N : ℕ) {f : ℤ → ℝ} (hf : ∀ k, f (-k) = f k) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f n = f 0 + 2 * ∑ k ∈ Finset.range N, f ((k : ℤ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)
        = insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hs, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ, hf]
    ring

/-- The weights: `s₀ = 2` (pole), `s₁ = −τ/(8a)` (mode 0), `s_{k+2} = 2(ψ̲_{k+1} − τ)/(8a)`. -/
def sfun (a τ : ℝ) (ψl : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 2 else if k = 1 then -τ / (8 * a) else 2 * (ψl (k - 1) - τ) / (8 * a)

theorem poleR_eq_xv0 {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) :
    poleR g a = ∫ t, g t * Real.cosh (t / 2) := by
  rw [poleR_eq_cosh_sub_sinh (probe_integrable hp).intervalIntegrable,
    intervalIntegral_odd (f := fun t => g t * Real.sinh (t / 2))
      (fun t => by rw [hp.even, show -t / 2 = -(t / 2) by ring, Real.sinh_neg]; ring),
    sub_zero, integral_supp ha hp]

/-- The effective mode energy `E_m = ψ_m − c·cos(πm u₀/4a)`. -/
def modeEP (a c u₀ : ℝ) (m : ℤ) : ℝ := modeE a m - c * Real.cos (π * m * u₀ / (4 * a))

theorem modeEP_neg (a c u₀ : ℝ) (m : ℤ) : modeEP a c u₀ (-m) = modeEP a c u₀ m := by
  unfold modeEP; rw [modeE_neg]; push_cast
  rw [show π * -(m : ℝ) * u₀ / (4 * a) = -(π * m * u₀ / (4 * a)) by ring, Real.cos_neg]

/-- **Truncation with the prime, exactly**: `τ + Σ_{S₀} (E_m − τ) p_m ≤ Near − c·f(u₀)`. -/
theorem prime_trunc {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    {u₀ c : ℝ} (hu0 : 0 ≤ u₀) (hu : u₀ ≤ 2 * a) (S₀ : Finset ℤ) {τ : ℝ}
    (hτ : ∀ m, m ∉ S₀ → τ ≤ modeEP a c u₀ m) :
    τ + ∑ m ∈ S₀, (modeEP a c u₀ m - τ) * pm a g m
      ≤ (∫ u in Ioc 0 (2 * a), archIntegrand g u) - c * autocorr g u₀ := by
  have hP := hasSum_pm ha hp
  rw [hn] at hP
  have hF := hasSum_autocorr ha hp hn hu0 hu
  have hT : Tendsto (fun S : Finset ℤ => ∑ m ∈ S₀, (modeEP a c u₀ m - τ) * pm a g m
      + τ * ∑ m ∈ S, pm a g m + c * ∑ m ∈ S, pm a g m * Real.cos (π * m * u₀ / (4 * a))) atTop
      (𝓝 (∑ m ∈ S₀, (modeEP a c u₀ m - τ) * pm a g m + τ * 1 + c * autocorr g u₀)) :=
    (tendsto_const_nhds.add (hP.const_mul τ)).add (hF.const_mul c)
  have hle : ∑ m ∈ S₀, (modeEP a c u₀ m - τ) * pm a g m + τ * 1 + c * autocorr g u₀
      ≤ ∫ u in Ioc 0 (2 * a), archIntegrand g u := by
    refine le_of_tendsto hT ?_
    filter_upwards [eventually_ge_atTop S₀] with S hS
    have hsplit := Finset.sum_sdiff hS (f := pm a g)
    have hsplit2 := Finset.sum_sdiff hS (f := fun m => pm a g m * modeEP a c u₀ m)
    have htail : τ * ∑ m ∈ S \ S₀, pm a g m ≤ ∑ m ∈ S \ S₀, pm a g m * modeEP a c u₀ m := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m hm' => ?_
      rw [Finset.mem_sdiff] at hm'
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hτ m hm'.2) (pm_nonneg ha g m)
    have hlow : ∑ m ∈ S₀, (modeEP a c u₀ m - τ) * pm a g m
        = ∑ m ∈ S₀, pm a g m * modeEP a c u₀ m - τ * ∑ m ∈ S₀, pm a g m := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hE : ∑ m ∈ S, pm a g m * modeEP a c u₀ m
        = ∑ m ∈ S, pm a g m * modeE a m - c * ∑ m ∈ S, pm a g m * Real.cos (π * m * u₀ / (4 * a)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => by unfold modeEP; ring
    have hmode := sum_modeE_le ha hp hn S
    rw [← hsplit, mul_add] at *
    rw [← hsplit2] at hE
    linarith
  linarith

/-- The weights with the prime: `s₀ = 2`, `s₁ = (−c − τ)/(8a)`, `s_{k+2} = 2(ψ̲_{k+1} − c cos_{k+1} − τ)/(8a)`. -/
def sfunP (a τ c u₀ : ℝ) (ψl : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 2 else if k = 1 then (-c - τ) / (8 * a)
  else 2 * (ψl (k - 1) - c * Real.cos (π * ((k - 1 : ℕ) : ℝ) * u₀ / (4 * a)) - τ) / (8 * a)

/-- **The relaxation with the prime.** -/
theorem weilQ_ge_relaxP {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1)
    {c u₀ : ℝ} (hu0 : 0 ≤ u₀) (hu : u₀ ≤ 2 * a) (hprime : 2 * primeS g = c * autocorr g u₀)
    (N : ℕ) (τ : ℝ) (ψl : ℕ → ℝ)
    (htail : ∀ n : ℤ, (N : ℤ) < n → τ ≤ modeEP a c u₀ n)
    (hlow : ∀ k : ℕ, k < N → ψl (k + 1) ≤ modeE a ((k : ℤ) + 1)) :
    weilConst + (∫ u in Ioi (2 * a), kerK u) + τ
      + xv a g (N + 2) ⬝ᵥ (diagonal (fun i : Fin (N + 2) => sfunP a τ c u₀ ψl i) *ᵥ xv a g (N + 2))
      ≤ weilQ a g := by
  have hτ : ∀ n, n ∉ Finset.Icc (-(N : ℤ)) N → τ ≤ modeEP a c u₀ n := by
    intro n hn'
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn'
    rcases hn' with h | h
    · have e := modeEP_neg a c u₀ (-n); rw [neg_neg] at e; rw [e]; exact htail _ (by omega)
    · exact htail n h
  have hE := prime_trunc ha hp hn hu0 hu (Finset.Icc (-(N : ℤ)) N) hτ
  rw [sum_Icc_even N (fun k => by simp only [modeEP_neg, pm_neg ha hp])] at hE
  set X : ℕ → ℝ := fun k => ∫ t, g t * Real.cos (π * k * t / (4 * a)) with hX
  have hpm1 : ∀ k : ℕ, pm a g ((k : ℤ) + 1) = X (k + 1) ^ 2 / (8 * a) := by
    intro k; rw [pm_even ha hp]; simp only [hX]; push_cast; rfl
  have hpm0 : pm a g 0 = X 0 ^ 2 / (8 * a) := by
    rw [pm_even ha hp]; simp only [hX]; push_cast; rfl
  have hE0 : modeEP a c u₀ 0 = -c := by unfold modeEP; simp [modeE_zero]
  rw [hE0, hpm0] at hE
  simp only [hpm1] at hE
  have hcos : ∀ k : ℕ, modeEP a c u₀ ((k : ℤ) + 1)
      = modeE a ((k : ℤ) + 1) - c * Real.cos (π * ((k + 1 : ℕ) : ℝ) * u₀ / (4 * a)) := by
    intro k; unfold modeEP; push_cast; ring
  simp only [hcos] at hE
  have hlowsum : ∑ k ∈ Finset.range N, (ψl (k + 1) - c * Real.cos (π * ((k + 1 : ℕ) : ℝ) * u₀ / (4 * a)) - τ)
        * (X (k + 1) ^ 2 / (8 * a))
      ≤ ∑ k ∈ Finset.range N, (modeE a ((k : ℤ) + 1) - c * Real.cos (π * ((k + 1 : ℕ) : ℝ) * u₀ / (4 * a)) - τ)
        * (X (k + 1) ^ 2 / (8 * a)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have := hlow k (Finset.mem_range.mp hk)
    have : 0 ≤ X (k + 1) ^ 2 / (8 * a) := by positivity
    nlinarith
  have hquad : xv a g (N + 2) ⬝ᵥ (diagonal (fun i : Fin (N + 2) => sfunP a τ c u₀ ψl i) *ᵥ xv a g (N + 2))
      = 2 * (∫ t, g t * Real.cosh (t / 2)) ^ 2 + ((-c - τ) / (8 * a)) * X 0 ^ 2
        + ∑ k ∈ Finset.range N, 2 * (ψl (k + 1) - c * Real.cos (π * ((k + 1 : ℕ) : ℝ) * u₀ / (4 * a)) - τ)
          / (8 * a) * X (k + 1) ^ 2 := by
    simp only [dotProduct, mulVec_diagonal]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    rw [← Fin.sum_univ_eq_sum_range (fun k => 2 * (ψl (k + 1)
      - c * Real.cos (π * ((k + 1 : ℕ) : ℝ) * u₀ / (4 * a)) - τ) / (8 * a) * X (k + 1) ^ 2) N]
    simp only [xv, vv, sfunP, hX, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, ite_true, Nat.cast_zero, zero_mul,
      mul_zero, zero_div, Nat.add_one_sub_one]
    have hne : ∀ x : ℕ, x + 1 + 1 ≠ 1 := fun x => by omega
    have key : ∀ u v : ℝ, u * (v * u) = v * u ^ 2 := fun u v => by ring
    simp only [hne, ite_false, key]
    push_cast; ring
  have hQ : weilQ a g = 2 * poleR g a ^ 2 + weilConst
      + ((∫ u in Ioc 0 (2 * a), archIntegrand g u) + ∫ u in Ioi (2 * a), kerK u) - c * autocorr g u₀ := by
    rw [weilQ_eq', hn, archE_split ha hp hn]; linarith
  have hs2 : ∑ k ∈ Finset.range N, 2 * (ψl (k + 1) - c * Real.cos (π * ((k + 1 : ℕ) : ℝ) * u₀ / (4 * a)) - τ)
        / (8 * a) * X (k + 1) ^ 2
      = 2 * ∑ k ∈ Finset.range N, (ψl (k + 1) - c * Real.cos (π * ((k + 1 : ℕ) : ℝ) * u₀ / (4 * a)) - τ)
        * (X (k + 1) ^ 2 / (8 * a)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h0 : (-c - τ) * (X 0 ^ 2 / (8 * a)) = (-c - τ) / (8 * a) * X 0 ^ 2 := by ring
  rw [hquad, hQ, poleR_eq_xv0 ha hp, hs2]
  linarith

/-- **The relaxation.** For a normalised even probe below `log 2`, a tail level `τ` for the modes `|n| > N`
and lower bounds `ψ̲_k ≤ ψ_k` for `1 ≤ k ≤ N`:
`c₀ + Far(a) + τ + xᵀ diag(s) x ≤ Q(g)`. The case `c = 0` of `weilQ_ge_relaxP`. -/
theorem weilQ_ge_relax {a : ℝ} (ha : 0 < a) (hlog : 2 * a < Real.log 2) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) (N : ℕ) (τ : ℝ) (ψl : ℕ → ℝ)
    (htail : ∀ n : ℤ, (N : ℤ) < n → τ ≤ modeE a n)
    (hlow : ∀ k : ℕ, k < N → ψl (k + 1) ≤ modeE a ((k : ℤ) + 1)) :
    weilConst + (∫ u in Ioi (2 * a), kerK u) + τ
      + xv a g (N + 2) ⬝ᵥ (diagonal (fun i : Fin (N + 2) => sfun a τ ψl i) *ᵥ xv a g (N + 2))
      ≤ weilQ a g := by
  have h := weilQ_ge_relaxP ha hp hn (c := 0) le_rfl (by linarith) (by rw [primeS_eq_zero hlog hp]; ring)
    N τ ψl (fun n hn => by simpa [modeEP] using htail n hn) hlow
  have e : (fun i : Fin (N + 2) => sfunP a τ 0 0 ψl i) = fun i : Fin (N + 2) => sfun a τ ψl i := by
    funext i; simp only [sfunP, sfun]; split_ifs <;> ring
  rwa [e] at h

/-! ## D. The Gram entries in closed form -/

/-- `ω_k = πk/(4a)`. -/
def omk (a : ℝ) (k : ℕ) : ℝ := π * k / (4 * a)

/-- **The Gram entries in closed form.** -/
def gC (a : ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then
    (if j = 0 then a + Real.sinh a else
      (Real.cos (omk a (j - 1) * a) * Real.sinh (a / 2) + 2 * omk a (j - 1) * Real.sin (omk a (j - 1) * a)
        * Real.cosh (a / 2)) / (omk a (j - 1) ^ 2 + 1 / 4))
  else if j = 0 then
    (Real.cos (omk a (i - 1) * a) * Real.sinh (a / 2) + 2 * omk a (i - 1) * Real.sin (omk a (i - 1) * a)
      * Real.cosh (a / 2)) / (omk a (i - 1) ^ 2 + 1 / 4)
  else if i = j then
    (if i = 1 then 2 * a else a + Real.sin (2 * omk a (i - 1) * a) / (2 * omk a (i - 1)))
  else
    Real.sin ((omk a (i - 1) - omk a (j - 1)) * a) / (omk a (i - 1) - omk a (j - 1))
      + Real.sin ((omk a (i - 1) + omk a (j - 1)) * a) / (omk a (i - 1) + omk a (j - 1))

theorem vv_succ (a : ℝ) (k : ℕ) (t : ℝ) : vv a (k + 1) t = Real.cos (omk a k * t) := by
  simp only [vv, omk]; ring_nf

theorem gramM_eq {a : ℝ} (ha : 0 < a) (m : ℕ) (i j : Fin m) : gramM a m i j = gC a i j := by
  simp only [gramM, Matrix.of_apply, gC]
  have hω : ∀ k : ℕ, 0 < k → 0 < omk a k := fun k hk => by
    unfold omk; have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hω0 : omk a 0 = 0 := by simp [omk]
  have hωinj : ∀ p q : ℕ, omk a p = omk a q → p = q := by
    intro p q h; unfold omk at h
    have : (p : ℝ) = q := by
      have hπ := Real.pi_pos
      field_simp at h; nlinarith [h]
    exact_mod_cast this
  obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
  simp only
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [vv, int_coshsq]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simp only [ite_true, show k + 1 ≠ 0 from by omega, ite_false, Nat.add_sub_cancel]
      simp only [vv]
      rw [show (fun t => Real.cosh (t / 2) * Real.cos (π * k * t / (4 * a)))
        = fun t => Real.cosh (t / 2) * Real.cos (omk a k * t) by
          funext t; rw [show π * k * t / (4 * a) = omk a k * t by unfold omk; ring]]
      exact int_cosh_cos _
  · obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [show p + 1 ≠ 0 from by omega, ite_false, ite_true, Nat.add_sub_cancel]
      simp only [vv]
      rw [show (fun t => Real.cos (π * p * t / (4 * a)) * Real.cosh (t / 2))
        = fun t => Real.cosh (t / 2) * Real.cos (omk a p * t) by
          funext t; rw [show π * p * t / (4 * a) = omk a p * t by unfold omk; ring, mul_comm]]
      exact int_cosh_cos _
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      simp only [show p + 1 ≠ 0 from by omega, show q + 1 ≠ 0 from by omega, ite_false, Nat.add_sub_cancel]
      simp only [vv_succ]
      by_cases hpq : p = q
      · subst hpq
        simp only [ite_true]
        by_cases hp0 : p = 0
        · subst hp0; simp [hω0]; ring
        · simp only [show p + 1 ≠ 1 from by omega, ite_false]
          exact int_cos_sq (hω p (by omega)).ne'
      · simp only [show p + 1 ≠ q + 1 from by omega, ite_false]
        have hm : omk a p - omk a q ≠ 0 := fun h => hpq (hωinj p q (by linarith))
        have hpl : omk a p + omk a q ≠ 0 := by
          rcases Nat.eq_zero_or_pos p with h0 | h0
          · subst h0; rw [hω0, zero_add]; exact (hω q (by omega)).ne'
          · have := hω p h0
            have : 0 ≤ omk a q := by unfold omk; positivity
            linarith
        exact int_cos_cos hm hpl

/-! ## E. The instance `N = 6` with rational data, and the certificate theorem -/

/-- Tail level for `|n| ≥ 7`: `Cin(7π/2) ≥ 3.033953` (`cinH7`). -/
def tau6 (a : ℝ) : ℝ := 3.033953 - errK a

/-- Certified `Cin(πk/2)` lower bounds (`cin_val1`–`cin_val6`). -/
def cv6 (k : ℕ) : ℝ :=
  if k = 1 then 0.5408 else if k = 2 then 1.6214 else if k = 3 then 2.2965 else if k = 4 then 2.4081
  else if k = 5 then 2.4848 else if k = 6 then 2.7801 else 0

/-- Certified lower bounds on `1 − 2 sin(πk/2)/(πk)` (`dlo1`–`dlo6`). -/
def dd6 (k : ℕ) : ℝ :=
  if k = 1 then 0.36338 else if k = 2 then 1 else if k = 3 then 1.212206 else if k = 4 then 1
  else if k = 5 then 0.872676 else if k = 6 then 1 else 0

def psil6 (a : ℝ) (k : ℕ) : ℝ := cv6 k + a * dd6 k - errK a

/-- `κ(a) = c₀ + Far(a) + τ(a)`, with `Far` in its closed form (`farField_eq`). -/
def kappa6 (a : ℝ) : ℝ :=
  weilConst + (-Real.log ((Real.exp a - 1) / (Real.exp a + 1)) + (π / 2 - Real.arctan (Real.sinh a))) + tau6 a

def gram6 (a : ℝ) : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of fun i j => gC a i j

def s6 (a : ℝ) : Fin 8 → ℝ := fun i => sfun a (tau6 a) (psil6 a) i

theorem dlo6 : (1 : ℝ) ≤ 1 - 2 * Real.sin (π * ((6 : ℤ) : ℝ) / 2) / (π * ((6 : ℤ) : ℝ)) := by
  push_cast
  rw [show π * (6 : ℝ) / 2 = (3 : ℕ) * π by push_cast; ring, Real.sin_nat_mul_pi]; simp

theorem htail6 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℤ) (hn : (6 : ℤ) < n) : tau6 a ≤ modeE a n := by
  have hnr : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hC : Cin (14 * π / 4) ≤ Cin (π * n / 2) := Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  have hc := cinH7
  have hπ := Real.pi_gt_three
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by positivity)
  have h2 : 2 / (π * n) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hD : 0 ≤ a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) := mul_nonneg ha.le (by linarith)
  unfold tau6; linarith

theorem hlow6 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (k : ℕ) (hk : k < 6) :
    psil6 a (k + 1) ≤ modeE a ((k : ℤ) + 1) := by
  have key : ∀ (m : ℤ) (hm : 0 < m) (Cv D : ℝ), Cv ≤ Cin (π * m / 2) →
      D ≤ 1 - 2 * Real.sin (π * m / 2) / (π * m) → Cv + a * D - errK a ≤ modeE a m := by
    intro m hm Cv D hc hd
    have := modeE_ge ha ha1 hm
    nlinarith [mul_le_mul_of_nonneg_left hd ha.le]
  unfold psil6 cv6 dd6
  interval_cases k
  · exact key 1 (by norm_num) _ _ (by simpa using cin_val1) dlo1
  · exact key 2 (by norm_num) _ _ (by simpa using cin_val2) dlo2
  · exact key 3 (by norm_num) _ _ (by simpa using cin_val3) dlo3
  · exact key 4 (by norm_num) _ _ (by simpa using cin_val4) dlo4
  · exact key 5 (by norm_num) _ _ (by simpa using cin_val5) dlo5
  · exact key 6 (by norm_num) _ _ (by simpa using cin_val6) dlo6

/-- **The certificate theorem.** For `0 < a ≤ 1/4`: if the `8×8` Gram matrix `gram6 a` (closed forms `gC`) is
positive definite, `ε ≤ κ(a)`, and `(κ(a) − ε)·G + G·diag(s)·G ⪰ 0`, then **every** normalised even probe has
`Q(g) ≥ ε`. The three hypotheses are finite, explicit, and checked by interval arithmetic. -/
theorem weilQ_ge_of_cert {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) (hG : (gram6 a).PosDef)
    (hκ : ε ≤ kappa6 a)
    (hM : ((kappa6 a - ε) • gram6 a + gram6 a * diagonal (s6 a) * gram6 a).PosSemidef)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) : ε ≤ weilQ a g := by
  have hlog : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  have hgram : gram6 a = gramM a 8 := by
    ext i j; simp only [gram6, Matrix.of_apply]; exact (gramM_eq ha 8 i j).symm
  rw [hgram] at hG hM
  have hq := quad_lower (gramM a 8) hG (s6 a) (xv a g 8) (nrm := normSq g)
    (bessel_gram ha.le hp.memL2 hp.supp 8) hκ hM
  have hr := weilQ_ge_relax ha hlog hp hn 6 (tau6 a) (psil6 a) (htail6 ha (by linarith))
    (hlow6 ha (by linarith))
  rw [farField_eq ha] at hr
  rw [hn] at hq
  unfold kappa6 at hq
  have hs : s6 a = fun i : Fin 8 => sfun a (tau6 a) (psil6 a) i := rfl
  rw [hs, mul_one, mul_one] at hq
  exact le_trans hq hr


/-! ## F. Monotonicity in the support, and the certified range -/

/-- The certificate at `a = 1/4`, `ε = 1/1000` (checked by `frontier/nullvec/kpole_cert.py` in arb). -/
def Cert14 : Prop :=
  (gram6 (1 / 4)).PosDef ∧ (1 / 1000 : ℝ) ≤ kappa6 (1 / 4) ∧
    ((kappa6 (1 / 4) - 1 / 1000) • gram6 (1 / 4) + gram6 (1 / 4) * diagonal (s6 (1 / 4)) * gram6 (1 / 4)).PosSemidef

/-- **Weil positivity with the pole term, for every support `0 < a ≤ 1/4`**: granted the finite certificate
`Cert14` (three explicit `8×8` matrix facts at the single point `a = 1/4`), every normalised even probe has
`Q(g) ≥ 1/1000`. The range extends past `a ≈ 0.105`, where the pole-free form `Q₀` is already negative. -/
theorem weilQ_ge_pole {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) (hc : Cert14) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : (1 / 1000 : ℝ) ≤ weilQ a g := by
  obtain ⟨hG, hκ, hM⟩ := hc
  rw [← weilQ_mono ha.le ha1 hp]
  exact weilQ_ge_of_cert (by norm_num) le_rfl hG hκ hM (hp.mono ha1) hn

end Pilot1ca

#print axioms Pilot1ca.quad_lower
#print axioms Pilot1ca.bessel_gram
#print axioms Pilot1ca.prime_trunc
#print axioms Pilot1ca.weilQ_ge_relaxP
#print axioms Pilot1ca.weilQ_ge_relax
#print axioms Pilot1ca.gramM_eq
#print axioms Pilot1ca.weilQ_ge_of_cert
#print axioms Pilot1ca.weilQ_ge_pole
