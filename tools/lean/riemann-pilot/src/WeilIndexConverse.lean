import Mathlib
import WeilIndexZeta

/-! # Off-line zero quadruples force negative directions of `Q` (round 230)

The converse of `finrank_le_quadruples_zeta` (round 229), and so the exact count: if the off-line zeros
of ζ are finitely many and form `m` quadruples `{ρ, 1 − ρ, ρ̄, 1 − ρ̄}`, the largest dimension of a space
of strip-test probes on which Weil's form is negative definite, over all supports, is `m`
(`negIndex_eq_quadruples`).

The construction (`negDirections_of_quadruples`):

* **Polynomial probes** (A). Iterated twins of the box, `T_Λ^k box = box(· − Λ) + box(· + Λ)` applied
  `k` times, have `ĝ = (2 cos Λt)^k ĝ₀`. So `Σ q_k T_Λ^k box` has transform `M(t) = q(2 cos Λt)·ĝ₀(t)`
  for a real polynomial `q` (`ghatC_polyProbe_box`), and it is a strip-test probe.
* **The frequency** (D). With `t_r = (ρ_r − ½)/i` for one representative per quadruple, `Λ` avoids a
  countable set so that the nodes `x_r = 2 cos(Λ t_r)` are non-real and separated from each other and
  from each other's conjugates, and `|x_r| > 2` (from `|2 cos w| ≥ e^{|Im w|} − e^{−|Im w|}`).
* **Interpolation** (C). Real polynomials `B_r = Π_{s≠r}(X − x_s)(X − x̄_s)·(αX + β)` take any prescribed
  complex value at `x_r` and vanish at the other nodes (`basisP`).
* **The space.** `q_s = X^N Σ_r s_r B_r` with `q_s(x_r) = s_r·i/ĝ₀(t_r)`. On the orbit of `t_r` the
  transform is `±i s_r`, so every off-line zero contributes `−s_r²` to `Q` (`Mz_sq_orb`). On the line
  `|2 cos Λt| ≤ 2 < |x_r|`, so the factor `X^N` makes the on-line contribution at most
  `(2/|x_r|)^N`-small (`Mz_sq_re_le`). For `N` large, `Q(q_s) ≤ −Σ s_r² + o(1)·Σ s_r² < 0`.

No bearing on RH: this is the counting form of Weil's criterion under a finiteness hypothesis. -/

open Real Complex MeasureTheory Polynomial

noncomputable section

namespace Pilot1ca

open Pilot1bt PilotWeil

/-! ## A. Polynomial probes: combinations of iterated twins -/

/-- The iterated twin `T_Λ^k g`. -/
def twinPow (g : ℝ → ℝ) (Λ : ℝ) : ℕ → ℝ → ℝ
  | 0 => g
  | k + 1 => twin (twinPow g Λ k) Λ

theorem twinPow_probe {b : ℝ} {g : ℝ → ℝ} (hp : Probe b g) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∀ k : ℕ, Probe (k * Λ + b) (twinPow g Λ k)
  | 0 => by simpa [twinPow] using hp
  | k + 1 => by
    have e : ((k + 1 : ℕ) : ℝ) * Λ + b = Λ + (k * Λ + b) := by push_cast; ring
    rw [e]; exact twin_probe (twinPow_probe hp hΛ k) hΛ

theorem ghatC_twinPow {b : ℝ} (hb : 0 < b) {g : ℝ → ℝ} (hp : Probe b g) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (z : ℂ) : ∀ k : ℕ,
    ghatC (twinPow g Λ k) (k * Λ + b) z = (2 * Complex.cos (Λ * z)) ^ k * ghatC g b z
  | 0 => by simp [twinPow]
  | k + 1 => by
    have e : ((k + 1 : ℕ) : ℝ) * Λ + b = Λ + (k * Λ + b) := by push_cast; ring
    have hkb : 0 < (k : ℝ) * Λ + b := by positivity
    show ghatC (twin (twinPow g Λ k) Λ) _ z = _
    rw [e, ghatC_twin hkb (twinPow_probe hp hΛ k) hΛ, ghatC_twinPow hb hp hΛ z k]
    ring

/-- `ĝ` does not depend on the support parameter beyond the support. -/
theorem ghatC_mono {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') {f : ℝ → ℝ}
    (hsupp : ∀ u, a < |u| → f u = 0) (z : ℂ) : ghatC f a' z = ghatC f a z := by
  rw [ghatC_eq_integral (by linarith) (fun u hu => hsupp u (by linarith)), ghatC_eq_integral ha hsupp]

theorem probe_finset_sum {A : ℝ} (s : Finset ℕ) {f : ℕ → ℝ → ℝ} (h : ∀ k ∈ s, Probe A (f k)) :
    Probe A (fun u => ∑ k ∈ s, f k u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using probe_zero A
  | insert a s ha ih =>
    have := (probe_add_sub (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).1
    simpa [Finset.sum_insert ha] using this

theorem ghatC_finset_sum {A : ℝ} (s : Finset ℕ) {f : ℕ → ℝ → ℝ} (h : ∀ k ∈ s, Probe A (f k))
    (z : ℂ) : ghatC (fun u => ∑ k ∈ s, f k u) A z = ∑ k ∈ s, ghatC (f k) A z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ghatC]
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := probe_finset_sum s fun k hk => h k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert ha]
    rw [← ih fun k hk => h k (Finset.mem_insert_of_mem hk)]
    exact ghatC_add h1.memL2 h2.memL2 A z

/-- The probe `Σ_{k<K} q_k T_Λ^k g` of a real polynomial `q`. Its transform is `ĝ(t)·q(2 cos Λt)`. -/
def polyProbe (g : ℝ → ℝ) (Λ : ℝ) (K : ℕ) (q : ℝ[X]) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, q.coeff k * twinPow g Λ k u

variable {b Λ : ℝ} {g : ℝ → ℝ}

theorem twinPow_probe' (hp : Probe b g) (hΛ : 0 ≤ Λ) {K k : ℕ} (hk : k ∈ Finset.range K) :
    Probe (K * Λ + b) (twinPow g Λ k) := by
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_range.1 hk).le
  exact (twinPow_probe hp hΛ k).mono (by nlinarith)

theorem polyProbe_probe (hp : Probe b g) (hΛ : 0 ≤ Λ) (K : ℕ) (q : ℝ[X]) :
    Probe (K * Λ + b) (polyProbe g Λ K q) :=
  probe_finset_sum _ fun _ hk => probe_smul (twinPow_probe' hp hΛ hk) _

theorem ghatC_polyProbe (hb : 0 < b) (hp : Probe b g) (hΛ : 0 ≤ Λ) (K : ℕ) (q : ℝ[X]) (z : ℂ) :
    ghatC (polyProbe g Λ K q) (K * Λ + b) z
      = (∑ k ∈ Finset.range K, (q.coeff k : ℂ) * (2 * Complex.cos (Λ * z)) ^ k) * ghatC g b z := by
  unfold polyProbe
  rw [ghatC_finset_sum _ (fun k hk => probe_smul (twinPow_probe' hp hΛ hk) _), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_range.1 hk).le
  rw [ghatC_smul, ghatC_mono (by positivity) (by nlinarith) (twinPow_probe hp hΛ k).supp,
    ghatC_twinPow hb hp hΛ z k]
  ring

/-- The multiplier `Σ_{k<K} q_k (2 cos Λz)^k` is `q(2 cos Λz)` when `deg q < K`. -/
theorem mult_eq_aeval {K : ℕ} {q : ℝ[X]} (hq : q.natDegree < K) (w : ℂ) :
    (∑ k ∈ Finset.range K, (q.coeff k : ℂ) * w ^ k) = aeval w q := by
  rw [aeval_eq_sum_range' hq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.real_smul]

/-- **Polynomial probes of the box are strip-test probes.** -/
theorem striptest_polyProbe (hΛ : 0 ≤ Λ) (K : ℕ) (q : ℝ[X]) :
    ∃ C, StripTest (fun z => ghatC (polyProbe (box 1) Λ K q) (K * Λ + 1) z ^ 2) C := by
  have hp := box_probe 1
  obtain ⟨C, hC⟩ := ghat_antitone_strip one_pos hp.even box_antitone box_nonneg hp.intervalIntegrable
  set M : ℝ := ∑ k ∈ Finset.range K, |q.coeff k| * (2 * Real.exp Λ) ^ k
  have hm : ∀ t ∈ PilotWeil.strip (-1) 1,
      ‖∑ k ∈ Finset.range K, (q.coeff k : ℂ) * (2 * Complex.cos (Λ * t)) ^ k‖ ≤ M := by
    intro t ht
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ k) (abs_nonneg _)
    exact norm_two_cos_strip hΛ ht
  have hT := striptest_mul_sq (G := ghatC (box 1) 1)
    (m := fun z => ∑ k ∈ Finset.range K, (q.coeff k : ℂ) * (2 * Complex.cos (Λ * z)) ^ k)
    (ghatC_differentiable hp.intervalIntegrable) (by fun_prop) hC hm
  have e : (fun z => ghatC (polyProbe (box 1) Λ K q) (K * Λ + 1) z ^ 2)
      = fun z => ((∑ k ∈ Finset.range K, (q.coeff k : ℂ) * (2 * Complex.cos (Λ * z)) ^ k)
          * ghatC (box 1) 1 z) ^ 2 := by
    funext z; rw [ghatC_polyProbe one_pos hp hΛ K q z]
  exact ⟨_, e ▸ hT⟩

/-! ## B. `|2 cos w| ≥ e^{|Im w|} − e^{−|Im w|}` -/

theorem norm_two_cos_ge (w : ℂ) :
    Real.exp |w.im| - Real.exp (-|w.im|) ≤ ‖2 * Complex.cos w‖ := by
  have e : 2 * Complex.cos w = Complex.exp (w * I) + Complex.exp (-w * I) := by
    rw [Complex.cos]; ring
  have n1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp]; simp
  have n2 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by rw [Complex.norm_exp]; simp
  have t1 : ‖Complex.exp (w * I)‖ - ‖Complex.exp (-w * I)‖ ≤ ‖2 * Complex.cos w‖ := by
    rw [e]
    have := norm_sub_le (Complex.exp (w * I) + Complex.exp (-w * I)) (Complex.exp (-w * I))
    rw [add_sub_cancel_right] at this
    linarith
  have t2 : ‖Complex.exp (-w * I)‖ - ‖Complex.exp (w * I)‖ ≤ ‖2 * Complex.cos w‖ := by
    rw [e]
    have := norm_sub_le (Complex.exp (w * I) + Complex.exp (-w * I)) (Complex.exp (w * I))
    rw [add_sub_cancel_left] at this
    linarith
  rw [n1, n2] at t1 t2
  rcases le_total 0 w.im with h | h
  · rw [abs_of_nonneg h]; exact t2
  · rw [abs_of_nonpos h, neg_neg]; exact t1

/-- `|2 cos w| > 2` once `|Im w| ≥ 1`. -/
theorem two_lt_norm_two_cos {w : ℂ} (hw : 1 ≤ |w.im|) : 2 < ‖2 * Complex.cos w‖ := by
  refine lt_of_lt_of_le ?_ (norm_two_cos_ge w)
  have h1 : Real.exp 1 ≤ Real.exp |w.im| := Real.exp_le_exp.2 hw
  have h2 : Real.exp (-|w.im|) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  have h4 : (5 / 2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  linarith

/-! ## C. Real polynomials with prescribed values at conjugate pairs -/

section Interp

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ → ℂ)

/-- `(X − x_r)(X − x̄_r)`, a real quadratic. -/
def quadP (r : κ) : ℝ[X] := X ^ 2 - C (2 * (x r).re) * X + C (Complex.normSq (x r))

omit [Fintype κ] [DecidableEq κ] in
theorem aeval_quadP (r : κ) (y : ℂ) :
    aeval y (quadP x r) = (y - x r) * (y - (starRingEnd ℂ) (x r)) := by
  simp only [quadP, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    Complex.coe_algebraMap]
  have h1 : ((x r).re : ℂ) * 2 = x r + (starRingEnd ℂ) (x r) := by
    rw [Complex.add_conj]; push_cast; ring
  have h2 : ((Complex.normSq (x r) : ℝ) : ℂ) = x r * (starRingEnd ℂ) (x r) := by
    rw [Complex.mul_conj]
  rw [h2]
  push_cast
  linear_combination (-y) * h1

omit [Fintype κ] [DecidableEq κ] in
theorem natDegree_quadP_le (r : κ) : (quadP x r).natDegree ≤ 2 := by
  unfold quadP
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  · simp
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
  · simp

/-- `D_r = Π_{s ≠ r} (X − x_s)(X − x̄_s)`. -/
def prodP (r : κ) : ℝ[X] := ∏ s ∈ Finset.univ.erase r, quadP x s

theorem aeval_prodP (r : κ) (y : ℂ) :
    aeval y (prodP x r) = ∏ s ∈ Finset.univ.erase r, (y - x s) * (y - (starRingEnd ℂ) (x s)) := by
  simp only [prodP, map_prod, aeval_quadP]

theorem natDegree_prodP_le (r : κ) : (prodP x r).natDegree ≤ 2 * Fintype.card κ := by
  unfold prodP
  refine (natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun s _ => natDegree_quadP_le x s).trans ?_)
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ]
  omega

variable {x}

/-- The node conditions: every node is non-real, and nodes of different indices differ from each
other and from each other's conjugates. -/
structure Nodes (x : κ → ℂ) : Prop where
  im_ne : ∀ r, (x r).im ≠ 0
  sep : ∀ r s, r ≠ s → x s ≠ x r ∧ x s ≠ (starRingEnd ℂ) (x r)

theorem aeval_prodP_self (hx : Nodes x) (r : κ) : aeval (x r) (prodP x r) ≠ 0 := by
  rw [aeval_prodP, Finset.prod_ne_zero_iff]
  intro s hs
  have hsr : s ≠ r := Finset.ne_of_mem_erase hs
  obtain ⟨h1, h2⟩ := hx.sep s r hsr
  exact mul_ne_zero (sub_ne_zero.2 h1) (sub_ne_zero.2 h2)

theorem aeval_prodP_other {r s : κ} (hsr : s ≠ r) : aeval (x s) (prodP x r) = 0 := by
  rw [aeval_prodP]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hsr, Finset.mem_univ s⟩) (by ring)

/-- The coefficients `α, β` with `α x + β = v` (`x` non-real). -/
def coefA (x v : ℂ) : ℝ := v.im / x.im
def coefB (x v : ℂ) : ℝ := v.re - coefA x v * x.re

theorem coef_eq {x v : ℂ} (hx : x.im ≠ 0) : (coefA x v : ℂ) * x + coefB x v = v := by
  apply Complex.ext
  · simp [coefA, coefB]
  · simp [coefA, coefB]; field_simp

/-- The real polynomial `B_r(v) = D_r·(αX + β)`: value `v` at `x_r`, zero at the other nodes. -/
def basisP (x : κ → ℂ) (r : κ) (v : ℂ) : ℝ[X] :=
  prodP x r * (C (coefA (x r) (v / aeval (x r) (prodP x r))) * X
    + C (coefB (x r) (v / aeval (x r) (prodP x r))))

theorem aeval_basisP_self (hx : Nodes x) (r : κ) (v : ℂ) : aeval (x r) (basisP x r v) = v := by
  have h0 := aeval_prodP_self hx r
  have hc := coef_eq (v := v / aeval (x r) (prodP x r)) (hx.im_ne r)
  simp only [basisP, map_mul, map_add, aeval_X, aeval_C, Complex.coe_algebraMap]
  rw [hc]; field_simp

theorem aeval_basisP_other {r s : κ} (hsr : s ≠ r) (v : ℂ) : aeval (x s) (basisP x r v) = 0 := by
  simp only [basisP, map_mul, aeval_prodP_other hsr, zero_mul]

theorem natDegree_basisP_le (r : κ) (v : ℂ) :
    (basisP x r v).natDegree ≤ 2 * Fintype.card κ + 1 := by
  unfold basisP
  refine (natDegree_mul_le).trans (add_le_add (natDegree_prodP_le x r) ?_)
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) ?_)
  simp

/-- **Size on `[−2, 2]`**: `|B_r(v)(ξ)| ≤ Kr·|v|` with `Kr` independent of `v`. -/
theorem abs_basisP_le (hx : Nodes x) (r : κ) :
    ∃ Kr : ℝ, 0 ≤ Kr ∧ ∀ (v : ℂ) (ξ : ℝ), |ξ| ≤ 2 → ‖aeval (ξ : ℂ) (basisP x r v)‖ ≤ Kr * ‖v‖ := by
  set P0 := aeval (x r) (prodP x r)
  have hP0 : P0 ≠ 0 := aeval_prodP_self hx r
  set Dm : ℝ := ∏ s ∈ Finset.univ.erase r, (2 + ‖x s‖) ^ 2
  have hDm : 0 ≤ Dm := Finset.prod_nonneg fun _ _ => by positivity
  have him : 0 < |(x r).im| := abs_pos.2 (hx.im_ne r)
  set c0 : ℝ := (2 + |(x r).re|) / |(x r).im| + 1
  refine ⟨Dm * (c0 / ‖P0‖), by positivity, fun v ξ hξ => ?_⟩
  set w := v / P0
  have hD : ‖aeval (ξ : ℂ) (prodP x r)‖ ≤ Dm := by
    rw [aeval_prodP, norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun s _ => ?_
    rw [norm_mul, sq]
    have hξ' : ‖(ξ : ℂ)‖ ≤ 2 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hξ
    have a1 : ‖(ξ : ℂ) - x s‖ ≤ 2 + ‖x s‖ := (norm_sub_le _ _).trans (by linarith)
    have a2 : ‖(ξ : ℂ) - (starRingEnd ℂ) (x s)‖ ≤ 2 + ‖x s‖ :=
      (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; linarith)
    exact mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
  have hA : |coefA (x r) w| ≤ ‖w‖ / |(x r).im| := by
    unfold coefA; rw [abs_div]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm w) (abs_nonneg _)
  have hB : |coefB (x r) w| ≤ ‖w‖ + ‖w‖ / |(x r).im| * |(x r).re| := by
    unfold coefB
    refine (abs_sub _ _).trans (add_le_add (Complex.abs_re_le_norm w) ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
  have hL : ‖(coefA (x r) w : ℂ) * ξ + coefB (x r) w‖ ≤ ‖w‖ * c0 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h2 : |coefA (x r) w| * |ξ| ≤ ‖w‖ / |(x r).im| * 2 :=
      mul_le_mul hA hξ (abs_nonneg _) (by positivity)
    have : ‖w‖ * c0 = ‖w‖ / |(x r).im| * 2 + (‖w‖ + ‖w‖ / |(x r).im| * |(x r).re|) := by
      simp only [c0]; field_simp; ring
    rw [this]; linarith
  have hw : ‖w‖ = ‖v‖ / ‖P0‖ := by simp [w]
  simp only [basisP, map_mul, map_add, aeval_X, aeval_C, Complex.coe_algebraMap]
  rw [norm_mul]
  calc ‖aeval (ξ : ℂ) (prodP x r)‖ * ‖(coefA (x r) w : ℂ) * ξ + coefB (x r) w‖
      ≤ Dm * (‖w‖ * c0) := mul_le_mul hD hL (norm_nonneg _) hDm
    _ = Dm * (c0 / ‖P0‖) * ‖v‖ := by rw [hw]; field_simp

end Interp

/-! ## D. Choosing the frequency `Λ` -/

/-- The real `Λ` with `Λ·d ∈ 2πℤ`. -/
def badSet (d : ℂ) : Set ℝ := {Λ | ∃ k : ℤ, (Λ : ℂ) * d = 2 * k * π}

theorem badSet_countable {d : ℂ} (hd : d ≠ 0) : (badSet d).Countable := by
  refine (Set.countable_range fun k : ℤ => ((2 * k * π : ℂ) / d).re).mono ?_
  rintro Λ ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simp only
  rw [← hk, mul_div_assoc, div_self hd, mul_one, Complex.ofReal_re]

/-- `cos(Λ y) = cos(Λ w)` forces `Λ ∈ badSet (w − y) ∪ badSet (w + y)`. -/
theorem mem_bad_of_cos_eq {Λ : ℝ} {y w : ℂ} (h : Complex.cos (Λ * y) = Complex.cos (Λ * w)) :
    Λ ∈ badSet (w - y) ∪ badSet (w + y) := by
  obtain ⟨k, hk | hk⟩ := Complex.cos_eq_cos_iff.1 h
  · left; exact ⟨k, by rw [mul_sub, hk]; ring⟩
  · right; exact ⟨k, by rw [mul_add, hk]; ring⟩

/-- The orbit relation `t ∈ {w, −w, w̄, −w̄}`. -/
def Orb (t w : ℂ) : Prop :=
  t = w ∨ t = -w ∨ t = (starRingEnd ℂ) w ∨ t = -(starRingEnd ℂ) w

/-- **A good frequency.** For finitely many points `t_r` with `Re t_r ≠ 0 ≠ Im t_r`, pairwise in
different orbits, there is `Λ > Λ₀` making `x_r = 2 cos(Λ t_r)` a node set with `|x_r| > 2`. -/
theorem exists_good_Λ {κ : Type*} [Fintype κ] (t : κ → ℂ) (hre : ∀ r, (t r).re ≠ 0)
    (him : ∀ r, (t r).im ≠ 0) (hdist : ∀ r s, r ≠ s → ¬Orb (t s) (t r)) :
    ∃ Λ : ℝ, 0 < Λ ∧ Nodes (fun r => 2 * Complex.cos (Λ * t r)) ∧
      ∀ r, 2 < ‖2 * Complex.cos (Λ * t r)‖ := by
  classical
  set conj := starRingEnd ℂ
  set B1 : κ → Set ℝ := fun r => badSet (conj (t r) - t r) ∪ badSet (conj (t r) + t r)
  set B2 : κ → κ → Set ℝ := fun r s => if r = s then ∅ else
    (badSet (t r - t s) ∪ badSet (t r + t s)) ∪ (badSet (conj (t r) - t s) ∪ badSet (conj (t r) + t s))
  have hne1 : ∀ r, conj (t r) - t r ≠ 0 := fun r h => him r (by
    have := congrArg Complex.im h; simp [conj] at this; linarith)
  have hne2 : ∀ r, conj (t r) + t r ≠ 0 := fun r h => hre r (by
    have := congrArg Complex.re h; simp [conj] at this; linarith)
  have hB1 : ∀ r, (B1 r).Countable := fun r =>
    (badSet_countable (hne1 r)).union (badSet_countable (hne2 r))
  have hB2 : ∀ r s, (B2 r s).Countable := by
    intro r s
    by_cases hrs : r = s
    · simp [B2, hrs]
    · have d := hdist r s hrs
      simp only [Orb, not_or] at d
      obtain ⟨d1, d2, d3, d4⟩ := d
      rw [show B2 r s = _ from ite_eq_right hrs]
      refine ((badSet_countable ?_).union (badSet_countable ?_)).union
        ((badSet_countable ?_).union (badSet_countable ?_))
      · exact sub_ne_zero.2 (Ne.symm d1)
      · intro h; exact d2 (by linear_combination h)
      · exact sub_ne_zero.2 (Ne.symm d3)
      · intro h; exact d4 (by linear_combination h)
  set Bad : Set ℝ := (⋃ r, B1 r) ∪ ⋃ r, ⋃ s, B2 r s
  have hBad : Bad.Countable :=
    (Set.countable_iUnion hB1).union (Set.countable_iUnion fun r => Set.countable_iUnion (hB2 r))
  set Λ₀ : ℝ := 1 + ∑ r, 1 / |(t r).im|
  obtain ⟨Λ, hΛB, hΛ₀⟩ := (hBad.dense_compl ℝ).exists_mem_open isOpen_Ioi (Set.nonempty_Ioi (a := Λ₀))
  have hΛ₀1 : 1 ≤ Λ₀ := by
    have : 0 ≤ ∑ r, 1 / |(t r).im| := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have hΛpos : 0 < Λ := by have : Λ₀ < Λ := hΛ₀; linarith
  refine ⟨Λ, hΛpos, ⟨fun r => ?_, fun r s hrs => ⟨fun h => ?_, fun h => ?_⟩⟩, fun r => ?_⟩
  · -- non-real
    intro h
    have hc : Complex.cos (Λ * t r) = Complex.cos (Λ * conj (t r)) := by
      have e1 : (2 * Complex.cos (Λ * t r)) = conj (2 * Complex.cos (Λ * t r)) :=
        (Complex.conj_eq_iff_im.2 h).symm
      rw [map_mul, ← Complex.cos_conj, map_mul, Complex.conj_ofReal, map_ofNat] at e1
      exact mul_left_cancel₀ two_ne_zero e1
    exact hΛB (Or.inl (Set.mem_iUnion.2 ⟨r, mem_bad_of_cos_eq hc⟩))
  · -- x_s ≠ x_r
    have hc : Complex.cos (Λ * t s) = Complex.cos (Λ * t r) := mul_left_cancel₀ two_ne_zero h
    refine hΛB (Or.inr (Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨s, ?_⟩⟩))
    rw [show B2 r s = _ from ite_eq_right hrs]
    exact Or.inl (mem_bad_of_cos_eq hc)
  · -- x_s ≠ conj x_r
    have hc : Complex.cos (Λ * t s) = Complex.cos (Λ * conj (t r)) := by
      have e1 := h
      rw [map_mul, ← Complex.cos_conj, map_mul, Complex.conj_ofReal, map_ofNat] at e1
      exact mul_left_cancel₀ two_ne_zero e1
    refine hΛB (Or.inr (Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨s, ?_⟩⟩))
    rw [show B2 r s = _ from ite_eq_right hrs]
    exact Or.inr (mem_bad_of_cos_eq hc)
  · -- size
    refine two_lt_norm_two_cos ?_
    have e : ((Λ : ℂ) * t r).im = Λ * (t r).im := by simp
    rw [e, abs_mul, abs_of_pos hΛpos]
    have hti : 0 < |(t r).im| := abs_pos.2 (him r)
    have h1 : 1 / |(t r).im| ≤ ∑ r, 1 / |(t r).im| :=
      Finset.single_le_sum (f := fun r => 1 / |(t r).im|) (fun _ _ => by positivity)
        (Finset.mem_univ r)
    have h2 : 1 / |(t r).im| ≤ Λ := by have : Λ₀ < Λ := hΛ₀; linarith
    rw [div_le_iff₀ hti] at h2; linarith

/-! ## E. The transform `M(z) = q(2 cos Λz)·ĝ₀(z)` on orbits and on the line -/

/-- The transform of a polynomial probe of the box. -/
def Mz (Λ : ℝ) (q : ℝ[X]) (z : ℂ) : ℂ := aeval (2 * Complex.cos (Λ * z)) q * ghatC (box 1) 1 z

theorem ghatC_polyProbe_box {Λ : ℝ} (hΛ : 0 ≤ Λ) {K : ℕ} {q : ℝ[X]} (hq : q.natDegree < K) (z : ℂ) :
    ghatC (polyProbe (box 1) Λ K q) (K * Λ + 1) z = Mz Λ q z := by
  rw [ghatC_polyProbe one_pos (box_probe 1) hΛ K q z, mult_eq_aeval hq]; rfl

theorem Mz_neg (Λ : ℝ) (q : ℝ[X]) (z : ℂ) : Mz Λ q (-z) = Mz Λ q z := by
  unfold Mz
  rw [mul_neg, Complex.cos_neg, ghatC_even (box_probe 1).even]

theorem Mz_conj (Λ : ℝ) (q : ℝ[X]) (z : ℂ) :
    Mz Λ q ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Mz Λ q z) := by
  unfold Mz
  have h1 : 2 * Complex.cos (Λ * (starRingEnd ℂ) z)
      = Complex.conjAe (2 * Complex.cos (Λ * z)) := by
    rw [Complex.conjAe_coe, map_mul, ← Complex.cos_conj, map_mul, Complex.conj_ofReal, map_ofNat]
  rw [h1, aeval_algHom_apply, Complex.conjAe_coe, ghatC_conj (box_probe 1).even zero_le_one, map_mul]

/-- On an orbit, `M²` is `M(w)²` or its conjugate. -/
theorem Mz_sq_orb (Λ : ℝ) (q : ℝ[X]) {t w : ℂ} (h : Orb t w) :
    Mz Λ q t ^ 2 = Mz Λ q w ^ 2 ∨ Mz Λ q t ^ 2 = (starRingEnd ℂ) (Mz Λ q w ^ 2) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl (by rw [Mz_neg])
  · exact Or.inr (by rw [Mz_conj, map_pow])
  · exact Or.inr (by rw [Mz_neg, Mz_conj, map_pow])

/-- At a real ordinate: `Re M² ≤ B²·Re ĝ₀²` when `|q| ≤ B` on `[−2, 2]`. -/
theorem Mz_sq_re_le (Λ : ℝ) (q : ℝ[X]) {B : ℝ} (hB : ∀ ξ : ℝ, |ξ| ≤ 2 → |q.eval ξ| ≤ B) {t : ℂ}
    (ht : t.im = 0) : (Mz Λ q t ^ 2).re ≤ B ^ 2 * (ghatC (box 1) 1 t ^ 2).re := by
  have et : t = ((t.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [ht])
  set τ := t.re
  set ξ : ℝ := 2 * Real.cos (Λ * τ)
  have hξ : |ξ| ≤ 2 := by
    simp only [ξ, abs_mul, abs_two]; nlinarith [Real.abs_cos_le_one (Λ * τ)]
  have hc : 2 * Complex.cos (Λ * t) = ((ξ : ℝ) : ℂ) := by
    rw [et]; simp only [ξ]; push_cast; rfl
  have hq : aeval (2 * Complex.cos (Λ * t)) q = ((q.eval ξ : ℝ) : ℂ) := by
    rw [hc, ← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval]
  have hG : ghatC (box 1) 1 t = (((ghatC (box 1) 1 t).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by rw [et]; simp [ghatC_im_zero (box_probe 1).even zero_le_one])
  set G := (ghatC (box 1) 1 t).re
  unfold Mz
  rw [hq, hG]
  have e1 : (((q.eval ξ : ℝ) : ℂ) * (G : ℂ)) ^ 2 = (((q.eval ξ * G) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((G : ℂ) ^ 2) = ((G ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Complex.ofReal_re, Complex.ofReal_re, mul_pow]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ξ hξ)
  have : (q.eval ξ) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB ξ hξ) 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-! ## F. The converse count -/

theorem polyProbe_add (g : ℝ → ℝ) (Λ : ℝ) (K : ℕ) (p q : ℝ[X]) :
    polyProbe g Λ K (p + q) = polyProbe g Λ K p + polyProbe g Λ K q := by
  funext u
  simp only [polyProbe, coeff_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]

theorem polyProbe_smul (g : ℝ → ℝ) (Λ : ℝ) (K : ℕ) (c : ℝ) (p : ℝ[X]) :
    polyProbe g Λ K (c • p) = c • polyProbe g Λ K p := by
  funext u
  simp only [polyProbe, coeff_smul, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The ordinate `t_i = (ρ_i − ½)/i` of a zero of ζ. -/
abbrev tz (i : Σ w : NontrivialZero, Fin (zeroMult w)) : ℂ := (zetaZeroFamily i - 1 / 2) / Complex.I

theorem ghatC_zero_fun (a : ℝ) (z : ℂ) : ghatC (fun _ => 0) a z = 0 := by simp [ghatC]

/-- **Off-line zero quadruples force negative directions of Weil's form.** Suppose the off-line zeros of
ζ are finitely many (all in `F`) and fall into the orbits of representatives `R`, pairwise in different
quadruples. Then at some support `a` there is a space `V` of strip-test probes with `dim V = |R|` on
which `Q` is negative definite. -/
theorem negDirections_of_quadruples (R F : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hF : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → i ∈ F)
    (hRoff : ∀ r ∈ R, (zetaZeroFamily r).re ≠ 1 / 2)
    (hR : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → ∃ r ∈ R, Orb (tz i) (tz r))
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tz s) (tz r)) :
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 := by
  classical
  -- the nodes
  set tt : R → ℂ := fun r => tz r.1 with htt
  have hre : ∀ r, (tt r).re ≠ 0 := fun r => by
    simp only [tt, tz, re_ordinate]; exact im_zetaZeroFamily_ne r.1
  have him : ∀ r, (tt r).im ≠ 0 := fun r => by
    simp only [tt, tz, im_ordinate]; intro h; exact hRoff r.1 r.2 (by linarith)
  have hd : ∀ r s : R, r ≠ s → ¬Orb (tt s) (tt r) := fun r s hrs =>
    hdist r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
  obtain ⟨Λ, hΛ, hN, hbig⟩ := exists_good_Λ tt hre him hd
  set x : R → ℂ := fun r => 2 * Complex.cos (Λ * tt r) with hx
  set G₀ := ghatC (box 1) 1
  have hG0 : ∀ r, G₀ (tt r) ≠ 0 := fun r => ghat_box_ne (him r)
  set ζ : R → ℂ := fun r => Complex.I / G₀ (tt r)
  choose Kr hKr0 hKr using abs_basisP_le hN
  set c : R → ℝ := fun r => Kr r * ‖ζ r‖
  set Cc : ℝ := ∑ r, c r ^ 2
  have hCc : 0 ≤ Cc := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the box zero sum
  have hbox := Complex.hasSum_re (weilQ_eq_zero_sum (box_probe 1) one_pos weilExplicit_box_zeta)
  rw [Complex.ofReal_re] at hbox
  set g0 : (Σ w : NontrivialZero, Fin (zeroMult w)) → ℝ := fun i => (G₀ (tz i) ^ 2).re
  set Foff := F.filter (fun i => (zetaZeroFamily i).re ≠ 1 / 2)
  set S₀ : ℝ := weilQ 1 (box 1) - ∑ i ∈ Foff, g0 i
  set S₀p := max S₀ 0
  have hS₀p : 0 ≤ S₀p := le_max_right _ _
  set δ : ℝ := 1 / (Cc * S₀p + 1)
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hδC : δ * (Cc * S₀p) < 1 := by
    have h0 : 0 < Cc * S₀p + 1 := by positivity
    simp only [δ]; rw [div_mul_eq_mul_div, one_mul, div_lt_one h0]; linarith
  -- the power `N`
  have hxpos : ∀ r, 0 < ‖x r‖ := fun r => by linarith [hbig r]
  have hθ : ∀ r, 0 ≤ 2 / ‖x r‖ ∧ 2 / ‖x r‖ < 1 := fun r =>
    ⟨by positivity, by rw [div_lt_one (hxpos r)]; exact hbig r⟩
  choose n hn using fun r => exists_pow_lt_of_lt_one hδ (hθ r).2
  set N := Finset.univ.sup n
  have hNr : ∀ r, (2 / ‖x r‖) ^ N ≤ δ := fun r =>
    (pow_le_pow_of_le_one (hθ r).1 (hθ r).2.le (Finset.le_sup (Finset.mem_univ r))).trans (hn r).le
  set K : ℕ := N + 2 * Fintype.card R + 2
  set a : ℝ := K * Λ + 1
  have ha : 0 < a := by positivity
  -- the polynomials
  set w : R → ℂ := fun r => ζ r / x r ^ N
  set Qp : (R → ℝ) → ℝ[X] := fun s => X ^ N * ∑ r, s r • basisP x r (w r)
  have hdeg : ∀ s, (Qp s).natDegree < K := by
    intro s
    have h1 : (∑ r, s r • basisP x r (w r)).natDegree ≤ 2 * Fintype.card R + 1 :=
      natDegree_sum_le_of_forall_le _ _ fun r _ =>
        (natDegree_smul_le _ _).trans (natDegree_basisP_le r _)
    calc (Qp s).natDegree ≤ (X ^ N : ℝ[X]).natDegree + (∑ r, s r • basisP x r (w r)).natDegree :=
          natDegree_mul_le
      _ ≤ N + (2 * Fintype.card R + 1) := add_le_add (natDegree_X_pow_le N) h1
      _ < K := by omega
  have hval : ∀ s r, aeval (x r) (Qp s) = s r * ζ r := by
    intro s r
    have hx0 : x r ≠ 0 := norm_pos_iff.1 (hxpos r)
    simp only [Qp, map_mul, map_pow, aeval_X, map_sum, map_smul]
    rw [Finset.sum_eq_single r (fun r' _ hr' => by rw [aeval_basisP_other (Ne.symm hr'), smul_zero])
      (fun h => absurd (Finset.mem_univ r) h), aeval_basisP_self hN, Complex.real_smul]
    simp only [w]; field_simp
  -- the linear map
  let L : (R → ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
    { toFun := fun s => polyProbe (box 1) Λ K (Qp s)
      map_add' := fun s s' => by
        rw [← polyProbe_add]; congr 1
        simp only [Qp, Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c s => by
        rw [RingHom.id_apply, ← polyProbe_smul]; congr 1
        simp only [Qp, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, mul_smul_comm] }
  have hLp : ∀ s, Probe a (L s) := fun s => polyProbe_probe (box_probe 1) hΛ.le K (Qp s)
  have hLg : ∀ s z, ghatC (L s) a z = Mz Λ (Qp s) z := fun s z =>
    ghatC_polyProbe_box hΛ.le (hdeg s) z
  have hMr : ∀ s (r : R), Mz Λ (Qp s) (tt r) = s r * Complex.I := by
    intro s r
    show aeval (x r) (Qp s) * G₀ (tt r) = _
    rw [hval]; simp only [ζ]; field_simp [hG0 r]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    funext r
    have h := congrArg (fun f => ghatC f a (tt r)) hs
    simp only [hLg, hMr] at h
    have h0 : ghatC (0 : ℝ → ℝ) a (tt r) = 0 := ghatC_zero_fun a _
    rw [h0] at h
    have : ((s r : ℝ) : ℂ) = 0 := by
      have := mul_eq_zero.1 h; rcases this with h1 | h1; exact h1; exact absurd h1 Complex.I_ne_zero
    exact_mod_cast this
  refine ⟨a, ha, LinearMap.range L, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  · rintro v ⟨s, rfl⟩
    exact ⟨hLp s, striptest_polyProbe hΛ.le K (Qp s)⟩
  · rintro v ⟨s, rfl⟩ hv
    have hs0 : s ≠ 0 := fun h => hv (by rw [h, map_zero])
    -- the zero sum for `L s`
    obtain ⟨Kt, hKt⟩ := striptest_polyProbe hΛ.le K (Qp s)
    have hsum := Complex.hasSum_re (weilQ_eq_zero_sum (hLp s) ha
      (weilExplicit_of_strip ha (hLp s) hKt))
    rw [Complex.ofReal_re] at hsum
    set fv : (Σ w : NontrivialZero, Fin (zeroMult w)) → ℝ := fun i => (ghatC (L s) a (tz i) ^ 2).re
    -- the bound on the line
    set B : ℝ := δ * ∑ r, |s r| * c r
    have hB : ∀ ξ : ℝ, |ξ| ≤ 2 → |(Qp s).eval ξ| ≤ B := by
      intro ξ hξ
      have e1 : ∀ p : ℝ[X], |p.eval ξ| = ‖aeval (ξ : ℂ) p‖ := fun p => by
        rw [← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval,
          Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
      simp only [Qp, eval_mul, eval_pow, eval_X, eval_finsetSum, eval_smul, smul_eq_mul]
      rw [abs_mul, abs_pow]
      have hterm : ∀ r, |s r * (basisP x r (w r)).eval ξ| * |ξ| ^ N ≤ δ * (|s r| * c r) := by
        intro r
        rw [abs_mul, e1]
        have hb := hKr r (w r) ξ hξ
        have hw : ‖w r‖ = ‖ζ r‖ / ‖x r‖ ^ N := by simp [w, norm_pow]
        have hxi : |ξ| ^ N ≤ 2 ^ N := pow_le_pow_left₀ (abs_nonneg _) hξ N
        have hpow : 2 ^ N / ‖x r‖ ^ N ≤ δ := by rw [← div_pow]; exact hNr r
        calc |s r| * ‖aeval (ξ : ℂ) (basisP x r (w r))‖ * |ξ| ^ N
            ≤ |s r| * (Kr r * (‖ζ r‖ / ‖x r‖ ^ N)) * 2 ^ N := by
              rw [← hw]
              exact mul_le_mul (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) hxi
                (by positivity) (mul_nonneg (abs_nonneg _) (mul_nonneg (hKr0 r) (norm_nonneg _)))
          _ = |s r| * c r * (2 ^ N / ‖x r‖ ^ N) := by simp only [c]; ring
          _ ≤ |s r| * c r * δ :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) (mul_nonneg (hKr0 r) (norm_nonneg _)))
          _ = δ * (|s r| * c r) := by ring
      calc |ξ| ^ N * |∑ r, s r * (basisP x r (w r)).eval ξ|
          ≤ |ξ| ^ N * ∑ r, |s r * (basisP x r (w r)).eval ξ| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ = ∑ r, |s r * (basisP x r (w r)).eval ξ| * |ξ| ^ N := by rw [Finset.mul_sum]; ring_nf
        _ ≤ ∑ r, δ * (|s r| * c r) := Finset.sum_le_sum fun r _ => hterm r
        _ = B := by rw [← Finset.mul_sum]
    -- termwise bounds
    have hoff : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → ∃ r : R, fv i = -(s r) ^ 2 := by
      intro i hi
      obtain ⟨r, hr, hor⟩ := hR i hi
      refine ⟨⟨r, hr⟩, ?_⟩
      have hM := hMr s ⟨r, hr⟩
      have hsq : Mz Λ (Qp s) (tt ⟨r, hr⟩) ^ 2 = ((-(s ⟨r, hr⟩) ^ 2 : ℝ) : ℂ) := by
        rw [hM, mul_pow, Complex.I_sq]; push_cast; ring
      simp only [fv, hLg]
      rcases Mz_sq_orb Λ (Qp s) hor with h | h
      · rw [h]; exact (congrArg Complex.re hsq).trans (Complex.ofReal_re _)
      · rw [h, hsq, Complex.conj_ofReal, Complex.ofReal_re]
    have hon : ∀ i, (zetaZeroFamily i).re = 1 / 2 → fv i ≤ B ^ 2 * g0 i := by
      intro i hi
      have him0 : (tz i).im = 0 := by rw [im_ordinate, hi]; ring
      simp only [fv, g0, hLg]
      exact Mz_sq_re_le Λ (Qp s) hB him0
    -- compare with the dominating family
    set hv' : (Σ w : NontrivialZero, Fin (zeroMult w)) → ℝ :=
      fun i => if i ∈ Foff then fv i else B ^ 2 * g0 i
    have hle : ∀ i, fv i ≤ hv' i := by
      intro i
      by_cases hi : i ∈ Foff
      · simp [hv', hi]
      · simp only [hv', hi, ite_false]
        refine hon i ?_
        by_contra hne
        exact hi (Finset.mem_filter.2 ⟨hF i hne, hne⟩)
    have hsum2 : HasSum hv' (∑ i ∈ Foff, fv i + B ^ 2 * S₀) := by
      have h1 : HasSum (fun i => if i ∈ Foff then fv i - B ^ 2 * g0 i else 0)
          (∑ i ∈ Foff, (fv i - B ^ 2 * g0 i)) := by
        have h0 : HasSum (fun i => if i ∈ Foff then fv i - B ^ 2 * g0 i else 0)
            (∑ i ∈ Foff, (if i ∈ Foff then fv i - B ^ 2 * g0 i else 0)) :=
          hasSum_sum_of_ne_finset_zero fun i hi => ite_eq_right hi
        have e : ∑ i ∈ Foff, (if i ∈ Foff then fv i - B ^ 2 * g0 i else 0)
            = ∑ i ∈ Foff, (fv i - B ^ 2 * g0 i) := Finset.sum_congr rfl fun i hi => ite_eq_left hi
        rwa [e] at h0
      have h2 := h1.add (hbox.mul_left (B ^ 2))
      convert h2 using 1
      · funext i; by_cases hi : i ∈ Foff <;> simp [hv', hi, g0]
      · simp only [S₀, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
    have hQ := hasSum_le hle hsum hsum2
    -- the off-line sum is at most `−Σ s²`
    have hRsub : R ⊆ Foff := fun r hr =>
      Finset.mem_filter.2 ⟨hF r (hRoff r hr), hRoff r hr⟩
    have hfR : ∀ r : R, fv r.1 = -(s r) ^ 2 := by
      intro r
      have hM := hMr s r
      simp only [fv, hLg]
      show (Mz Λ (Qp s) (tt r) ^ 2).re = _
      rw [hM, mul_pow, Complex.I_sq, mul_neg_one, Complex.neg_re, ← Complex.ofReal_pow,
        Complex.ofReal_re]
    have hoffle : ∑ i ∈ Foff, fv i ≤ -∑ r, (s r) ^ 2 := by
      rw [← Finset.sum_sdiff hRsub]
      have h1 : ∑ i ∈ Foff \ R, fv i ≤ 0 := Finset.sum_nonpos fun i hi => by
        have hi' : (zetaZeroFamily i).re ≠ 1 / 2 := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hi).1).2
        obtain ⟨r, hr⟩ := hoff i hi'
        rw [hr]; exact neg_nonpos.2 (sq_nonneg _)
      have h2 : ∑ i ∈ R, fv i = -∑ r, (s r) ^ 2 := by
        rw [← Finset.sum_coe_sort R, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun r _ => hfR r
      linarith
    -- Cauchy–Schwarz and the choice of `δ`
    have hS : 0 < ∑ r, (s r) ^ 2 := by
      obtain ⟨r, hr⟩ := Function.ne_iff.1 hs0
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨r, Finset.mem_univ r, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hr))⟩
    have hCS : (∑ r, |s r| * c r) ^ 2 ≤ (∑ r, (s r) ^ 2) * Cc := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r => |s r|) c
      simp only [sq_abs] at this
      exact this
    have hB2 : B ^ 2 ≤ δ ^ 2 * ((∑ r, (s r) ^ 2) * Cc) := by
      simp only [B]; rw [mul_pow]; exact mul_le_mul_of_nonneg_left hCS (by positivity)
    have hBS : B ^ 2 * S₀ ≤ B ^ 2 * S₀p := mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
    have hkey : B ^ 2 * S₀p < ∑ r, (s r) ^ 2 := by
      have e1 : B ^ 2 * S₀p ≤ δ ^ 2 * ((∑ r, (s r) ^ 2) * Cc) * S₀p :=
        mul_le_mul_of_nonneg_right hB2 hS₀p
      have e2 : δ ^ 2 * ((∑ r, (s r) ^ 2) * Cc) * S₀p
          = δ * (δ * (Cc * S₀p)) * ∑ r, (s r) ^ 2 := by ring
      have e3 : δ * (δ * (Cc * S₀p)) < 1 := by
        calc δ * (δ * (Cc * S₀p)) ≤ 1 * (δ * (Cc * S₀p)) :=
              mul_le_mul_of_nonneg_right hδ1 (by positivity)
          _ < 1 := by rw [one_mul]; exact hδC
      nlinarith
    linarith

/-- **The negative index of Weil's form counts the off-line quadruples.** Suppose the off-line zeros
of ζ are finitely many and form the quadruples of the representatives `R`. Then every space of
strip-test probes on which `Q` is negative definite has dimension at most `|R|`, and at some support
there is one of dimension exactly `|R|`. -/
theorem negIndex_eq_quadruples (R F : Finset (Σ w : NontrivialZero, Fin (zeroMult w)))
    (hF : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → i ∈ F)
    (hRoff : ∀ r ∈ R, (zetaZeroFamily r).re ≠ 1 / 2)
    (hR : ∀ i, (zetaZeroFamily i).re ≠ 1 / 2 → ∃ r ∈ R, Orb (tz i) (tz r))
    (hdist : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ¬Orb (tz s) (tz r)) :
    (∀ (a : ℝ), 0 < a → ∀ (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V],
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) →
      (∀ v ∈ V, v ≠ 0 → weilQ a v < 0) → Module.finrank ℝ V ≤ R.card) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ V : Submodule ℝ (ℝ → ℝ), Module.finrank ℝ V = R.card ∧
      (∀ v ∈ V, Probe a v ∧ ∃ K, StripTest (fun z => ghatC v a z ^ 2) K) ∧
      ∀ v ∈ V, v ≠ 0 → weilQ a v < 0 := by
  refine ⟨fun a ha V _ hV hneg => ?_, negDirections_of_quadruples R F hF hRoff hR hdist⟩
  refine finrank_le_quadruples_zeta V ha (fun v hv => (hV v hv).1) (fun v hv => (hV v hv).2) hneg R
    fun i => ?_
  by_cases hi : (zetaZeroFamily i).re = 1 / 2
  · exact Or.inl hi
  · obtain ⟨r, hr, ho⟩ := hR i hi
    exact Or.inr ⟨r, hr, ho⟩

end Pilot1ca

#print axioms Pilot1ca.ghatC_polyProbe
#print axioms Pilot1ca.striptest_polyProbe
#print axioms Pilot1ca.two_lt_norm_two_cos
#print axioms Pilot1ca.aeval_basisP_self
#print axioms Pilot1ca.abs_basisP_le
#print axioms Pilot1ca.exists_good_Λ
#print axioms Pilot1ca.Mz_sq_orb
#print axioms Pilot1ca.Mz_sq_re_le
#print axioms Pilot1ca.negDirections_of_quadruples
#print axioms Pilot1ca.negIndex_eq_quadruples
