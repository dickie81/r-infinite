import Mathlib
import DimTwo

/-! # Counting off-line zeros by the dimension of the ground space

For `v` in a ground space of dimension `m`, every off-cross zero `ω` of `v̂` gives a root
`−1/(¼ + ω²)` of one fixed nonzero real polynomial `P_v` of degree `< m`
(`offcross_root`). So `v̂` has at most `m − 1` distinct off-cross values of `ω²`
(`card_offcross_le`). Hurwitz's theorem carries the count to the limit: under (a) with eventually
`dim V ≤ M`, `Ξ` has at most `M − 1` distinct off-cross values of `z²` (`xi_offcross_card_le`), and
`ζ` has at most `M − 1` zeros with `Re s > ½` (`zeta_offline_card_le`).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

open Pilot1bt

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

/-- `P_v ≠ 0` for nonzero `v`, and its degree is `< m`. -/
theorem polyOf_ne_zero_of_hat {a : ℝ} (ha : 0 < a) {w v : ℝ → ℝ} (hv : v ∈ groundSpace a)
    (hpos : 0 < normSq v) {k : ℕ} {ev : Fin k → ℝ}
    (hev : ∀ t : ℝ, ghatC v a t
      = (∑ i : Fin k, (ev i : ℂ) * ((qr t : ℝ) : ℂ) ^ (i : ℕ)) * ghatC w a t) :
    (polyOf fun i : Fin k => (ev i : ℂ)) ≠ 0 := by
  intro h0
  obtain ⟨α, ε, _, hε, hne⟩ := exists_interval_ghat ha hv.1 hpos
  apply hne (α + ε / 2) ⟨by linarith, by linarith⟩
  rw [hev, ← polyOf_eval, h0, Polynomial.eval_zero, zero_mul]

theorem polyOf_natDegree_le {k : ℕ} (c : Fin (k + 1) → ℂ) : (polyOf c).natDegree ≤ k :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun j hj => polyOf_coeff_ge _ (by
    have : k < j := by exact_mod_cast hj
    omega)

/-- **At most `m − 1` off-cross values of `ω²`** for a nonzero ground-space element. -/
theorem card_offcross_le {a : ℝ} (ha : 0 < a) {v : ℝ → ℝ} (hv : v ∈ groundSpace a)
    (hpos : 0 < normSq v) (s : Finset ℂ)
    (hs : ∀ σ ∈ s, σ.im ≠ 0 ∧ ∃ ω, ω ^ 2 = σ ∧ ghatC v a ω = 0) : s.card ≤ gdim a - 1 := by
  obtain ⟨w, hc, hwpos⟩ := exists_long_chain ha
  obtain ⟨ev, hev⟩ := chain_span_hat ha hc hwpos hv
  set Pv := polyOf fun i : Fin (gdim a - 1 + 1) => (ev i : ℂ)
  have hPv0 : Pv ≠ 0 := polyOf_ne_zero_of_hat ha hv hpos hev
  set f : ℂ → ℂ := fun σ => -1 / (1 / 4 + σ)
  have hinj : Set.InjOn f s := by
    intro σ hσ τ hτ h
    have h1 : (1 / 4 + σ) ≠ 0 := by
      intro e; apply (hs σ hσ).1
      have : σ = -(1 / 4) := by linear_combination e
      rw [this]; simp
    have h2 : (1 / 4 + τ) ≠ 0 := by
      intro e; apply (hs τ hτ).1
      have : τ = -(1 / 4) := by linear_combination e
      rw [this]; simp
    simp only [f] at h
    rw [div_eq_div_iff h1 h2] at h
    linear_combination h
  have hsub : s.image f ⊆ Pv.roots.toFinset := by
    intro r hr
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨him, ω, hω2, hω⟩ := hs σ hσ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPv0]
    have := offcross_root ha hc hwpos hv hev hω (by rw [hω2]; exact him)
    rw [hω2] at this; exact this
  calc s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Pv.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Pv.roots.card := Multiset.toFinset_card_le _
    _ ≤ Pv.natDegree := Polynomial.card_roots' _
    _ ≤ gdim a - 1 := polyOf_natDegree_le _

/-! ## Hurwitz: zeros of the limit attract zeros of the approximants -/

theorem hurwitz_attract {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (hf : Differentiable ℂ f) (hconv : TendstoLocallyUniformly F f atTop) (hnz : ∃ w, f w ≠ 0)
    {z₀ : ℂ} (hz₀ : f z₀ = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ n in atTop, ∃ z, dist z z₀ < ρ ∧ F n z = 0 := by
  by_contra h
  rw [Filter.not_eventually] at h
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop h
  have hconv' : TendstoLocallyUniformly (fun n => F (φ n)) f atTop := fun u hu x => by
    obtain ⟨t, ht, hev⟩ := hconv u hu x
    exact ⟨t, ht, hφ.tendsto_atTop.eventually hev⟩
  have hS : IsClosed {z : ℂ | ρ ≤ dist z z₀} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have := hurwitz_closed (fun n => hF (φ n)) hf hconv' hnz hS (fun n z hz => by
    by_contra hc
    simp only [Set.mem_ofPred_eq, not_le] at hc
    exact hP n ⟨z, hc, hz⟩) z₀ hz₀
  simp only [Set.mem_ofPred_eq, dist_self] at this
  linarith

/-! ## The count in the limit -/

/-- **Off-cross zeros of `Ξ`, counted by `z²`, number at most `M − 1`**, if (a) holds for ground
states whose ground spaces eventually have dimension `≤ M`. -/
theorem xi_offcross_card_le {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) (s : Finset ℂ)
    (hs : ∀ σ ∈ s, σ.im ≠ 0 ∧ ∃ z, z ^ 2 = σ ∧ Xi z = 0) : s.card ≤ M - 1 := by
  classical
  choose! z hz2 hzX using fun σ (hσ : σ ∈ s) => (hs σ hσ).2
  -- a uniform separation `η`
  set D : Finset ℝ := (((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).image (fun p => ‖p.1 - p.2‖))
    ∪ s.image (fun σ => |σ.im|) ∪ {1}
  have hDne : D.Nonempty := ⟨1, by simp [D]⟩
  set η := D.min' hDne
  have hDpos : ∀ x ∈ D, 0 < x := by
    intro x hx
    simp only [D, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_singleton] at hx
    rcases hx with (⟨p, ⟨_, hne⟩, rfl⟩ | ⟨σ, hσ, rfl⟩) | rfl
    · exact norm_pos_iff.2 (sub_ne_zero.2 hne)
    · exact abs_pos.2 (hs σ hσ).1
    · norm_num
  have hη : 0 < η := hDpos _ (Finset.min'_mem D hDne)
  have hηsep : ∀ σ ∈ s, ∀ τ ∈ s, σ ≠ τ → η ≤ ‖σ - τ‖ := fun σ hσ τ hτ h =>
    Finset.min'_le D _ (by simp only [D, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product]; exact Or.inl (Or.inl ⟨(σ, τ), ⟨⟨hσ, hτ⟩, h⟩, rfl⟩))
  have hηim : ∀ σ ∈ s, η ≤ |σ.im| := fun σ hσ =>
    Finset.min'_le D _ (by simp only [D, Finset.mem_union, Finset.mem_image]
                           exact Or.inl (Or.inr ⟨σ, hσ, rfl⟩))
  set ρ : ℂ → ℝ := fun σ => min 1 (η / (4 * (‖z σ‖ + 1)))
  have hρ : ∀ σ, 0 < ρ σ := fun σ => lt_min one_pos (by positivity)
  -- squares of nearby points stay within `η/2`
  have hsq : ∀ σ ∈ s, ∀ ζ, dist ζ (z σ) < ρ σ → ‖ζ ^ 2 - σ‖ < η / 2 := by
    intro σ hσ ζ hζ
    rw [← hz2 σ hσ, show ζ ^ 2 - z σ ^ 2 = (ζ - z σ) * (ζ + z σ) by ring, norm_mul]
    rw [dist_eq_norm] at hζ
    have h1 : ‖ζ + z σ‖ ≤ 2 * (‖z σ‖ + 1) := by
      have := norm_add_le (ζ - z σ) (2 * z σ)
      rw [show ζ - z σ + 2 * z σ = ζ + z σ by ring, norm_mul] at this
      have : ‖ζ - z σ‖ < 1 := lt_of_lt_of_le hζ (min_le_left _ _)
      simp only [Complex.norm_ofNat] at *; linarith
    have h2 : ‖ζ - z σ‖ < η / (4 * (‖z σ‖ + 1)) := lt_of_lt_of_le hζ (min_le_right _ _)
    calc ‖ζ - z σ‖ * ‖ζ + z σ‖ ≤ ‖ζ - z σ‖ * (2 * (‖z σ‖ + 1)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ < η / (4 * (‖z σ‖ + 1)) * (2 * (‖z σ‖ + 1)) :=
          mul_lt_mul_of_pos_right h2 (by positivity)
      _ = η / 2 := by field_simp; ring
  -- Hurwitz
  have hX0 := Xi_zero_ne_zero
  have hFd : ∀ n, Differentiable ℂ (fun w => ghatC (g n) (a n) w / ghatC (g n) (a n) 0) := fun n =>
    (ghatC_differentiable (probe_integrable (hgs n).1).intervalIntegrable).div_const _
  have hfd : Differentiable ℂ (fun w => Xi w / Xi 0) := differentiable_Xi.div_const _
  have hnz : ∃ w, Xi w / Xi 0 ≠ 0 := ⟨0, by rw [div_self hX0]; exact one_ne_zero⟩
  have hatt : ∀ᶠ n in atTop, ∀ σ ∈ s, ∃ ζ, dist ζ (z σ) < ρ σ ∧
      ghatC (g n) (a n) ζ / ghatC (g n) (a n) 0 = 0 :=
    (Filter.eventually_all_finset s).2 fun σ hσ =>
      hurwitz_attract hFd hfd hconv hnz (by simp [hzX σ hσ]) (hρ σ)
  have h0 : ∀ᶠ n in atTop, ghatC (g n) (a n) 0 ≠ 0 := by
    have hu := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) {0} isCompact_singleton) 1 one_pos
    filter_upwards [hu] with n hn h
    have := hn 0 rfl
    simp only [div_self hX0, h, div_zero, dist_zero_right, norm_one] at this
    exact lt_irrefl _ this
  obtain ⟨n, hn, hn1, hn0⟩ := (hdim.and (hatt.and h0)).exists
  choose! ζ hζd hζ0 using hn1
  have hζz : ∀ σ ∈ s, ghatC (g n) (a n) (ζ σ) = 0 := fun σ hσ =>
    (div_eq_zero_iff.1 (hζ0 σ hσ)).resolve_right hn0
  have hinj : Set.InjOn (fun σ => ζ σ ^ 2) s := by
    intro σ hσ τ hτ h
    by_contra hne
    have h1 := hsq σ hσ _ (hζd σ hσ)
    have h2 := hsq τ hτ _ (hζd τ hτ)
    simp only at h
    rw [h] at h1
    have t1 : ‖σ - τ‖ ≤ ‖σ - ζ τ ^ 2‖ + ‖ζ τ ^ 2 - τ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have t2 : ‖σ - ζ τ ^ 2‖ = ‖ζ τ ^ 2 - σ‖ := norm_sub_rev _ _
    have t3 := hηsep σ hσ τ hτ hne
    linarith
  obtain ⟨hV, hN⟩ := (isGroundState_iff (ha n)).1 (hgs n)
  have hcount := card_offcross_le (ha n) hV (by rw [hN]; norm_num) (s.image fun σ => ζ σ ^ 2)
    (by
      intro σ' hσ'
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hσ'
      refine ⟨fun him => ?_, ζ σ, rfl, hζz σ hσ⟩
      have h1 := hsq σ hσ _ (hζd σ hσ)
      have h2 : |(ζ σ ^ 2 - σ).im| ≤ ‖ζ σ ^ 2 - σ‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im, him, zero_sub, abs_neg] at h2
      linarith [hηim σ hσ])
  rw [Finset.card_image_of_injOn hinj] at hcount
  omega

/-- **At most `M − 1` zeros of `ζ` with `Re s > ½`**, under (a) for ground states whose ground
spaces eventually have dimension `≤ M`. -/
theorem zeta_offline_card_le {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) (T : Finset ℂ)
    (hT : ∀ s ∈ T, riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ 1 / 2 < s.re) :
    T.card ≤ M - 1 := by
  classical
  set f : ℂ → ℂ := fun s => ((s - 1 / 2) / I) ^ 2
  have hf : ∀ s, f s = -(s - 1 / 2) ^ 2 := fun s => by
    simp only [f]; rw [div_pow, I_sq]; ring
  have hinj : Set.InjOn f T := by
    intro s hs s' hs' h
    rw [hf, hf, neg_inj] at h
    have hre : (s + s' - 1).re ≠ 0 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith [(hT s hs).2.2, (hT s' hs').2.2]
    have hne : s + s' - 1 ≠ 0 := fun h0 => hre (by rw [h0, Complex.zero_re])
    have : (s - s') * (s + s' - 1) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)
  have hcard := xi_offcross_card_le ha hgs hdim hconv (T.image f) (by
    intro σ hσ
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hσ
    obtain ⟨hz, htriv, hre⟩ := hT s hs
    have hnt : IsNontrivialZero s := ⟨hz, htriv⟩
    refine ⟨?_, (s - 1 / 2) / I, rfl, by rw [Xi_at_ordinate, xi_eq_zero_of_nontrivial hnt]⟩
    -- `Im f(s) = −2(Re s − ½)·Im s`, and `Im s ≠ 0` since `ζ ≠ 0` on `(0, 1)`
    have him : s.im ≠ 0 := by
      intro h0
      have hs1 := hnt.re_lt_one
      apply zetaNoZeroInUnitInterval s.re (by linarith) hs1
      have : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
      rw [← this]; exact hz
    rw [hf]
    simp only [Complex.neg_im, pow_two, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    norm_num
    intro h
    have h' : (s.re - 1 / 2) * s.im = 0 := by linarith
    rcases mul_eq_zero.1 h' with h1 | h1
    · linarith
    · exact him h1)
  rwa [Finset.card_image_of_injOn hinj] at hcard

end Pilot1ca

#print axioms Pilot1ca.offcross_root
#print axioms Pilot1ca.card_offcross_le
#print axioms Pilot1ca.hurwitz_attract
#print axioms Pilot1ca.xi_offcross_card_le
#print axioms Pilot1ca.zeta_offline_card_le
