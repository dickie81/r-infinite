import Mathlib
import StructureD

/-! # Off-line zeros counted by the dimension of the ground space

For `v` in a ground space of dimension `m`, every off-cross zero `ω` of `v̂` gives a root
`−1/(¼ + ω²)` of one fixed nonzero real polynomial `P_v` of degree `< m` (`offcross_root`,
StructureD.lean). Conjugate zeros pair up, so `v̂` has at most `2⌊(m − 1)/2⌋` distinct off-cross
values of `ω²` (`card_offcross_le_even`); for `m ≤ 2` there are none (`zeros_cross_of_dim_le_two`).

Hurwitz carries the count to the limit: under (a) with eventually `dim V ≤ M`, `Ξ` has at most
`2⌊(M − 1)/2⌋` off-cross values of `z²` (`xi_offcross_card_le`) and `ζ` at most `2⌊(M − 1)/2⌋`
nontrivial zeros with `Re s > ½` (`zeta_offline_card_le`). For `M ≤ 2` this is RH
(`rh_of_dim_le_two`); eventual simplicity is the case `M = 1` (`gdim_le_one_of_simple`), which
recovers `rh_of_eventually_simple` (SwapRealize.lean) by a second route.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

open Pilot1bt

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

/-- A finite set of non-real numbers closed under conjugation has even cardinality. -/
theorem card_even_of_conj (S : Finset ℂ) (hcl : ∀ σ ∈ S, (starRingEnd ℂ) σ ∈ S)
    (hnr : ∀ σ ∈ S, σ.im ≠ 0) : Even S.card := by
  classical
  set Sp := S.filter (fun σ => 0 < σ.im)
  set Sn := S.filter (fun σ => ¬ 0 < σ.im)
  have hsplit : Sp.card + Sn.card = S.card := Finset.card_filter_add_card_filter_not _
  have himg : Sp.image (starRingEnd ℂ) = Sn := by
    ext τ
    simp only [Sp, Sn, Finset.mem_image, Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨σ, ⟨hσ, hpos⟩, rfl⟩
      exact ⟨hcl σ hσ, by rw [Complex.conj_im]; linarith⟩
    · rintro ⟨hτ, hle⟩
      refine ⟨(starRingEnd ℂ) τ, ⟨hcl τ hτ, ?_⟩, Complex.conj_conj τ⟩
      rw [Complex.conj_im]
      have := hnr τ hτ
      exact neg_pos.2 (lt_of_le_of_ne hle this)
  have hinj : Set.InjOn (starRingEnd ℂ) Sp := fun x _ y _ h => (starRingEnd ℂ).injective h
  rw [← himg, Finset.card_image_of_injOn hinj] at hsplit
  exact ⟨Sp.card, hsplit.symm⟩

/-- **Per support, with parity: at most `2⌊(m − 1)/2⌋` off-cross values of `ω²`.** -/
theorem card_offcross_le_even {a : ℝ} (ha : 0 < a) {v : ℝ → ℝ} (hv : v ∈ groundSpace a)
    (hpos : 0 < normSq v) (s : Finset ℂ)
    (hs : ∀ σ ∈ s, σ.im ≠ 0 ∧ ∃ ω, ω ^ 2 = σ ∧ ghatC v a ω = 0) :
    s.card ≤ 2 * ((gdim a - 1) / 2) := by
  classical
  set S := s ∪ s.image (starRingEnd ℂ)
  have hS : ∀ σ ∈ S, σ.im ≠ 0 ∧ ∃ ω, ω ^ 2 = σ ∧ ghatC v a ω = 0 := by
    intro σ hσ
    rcases Finset.mem_union.1 hσ with h | h
    · exact hs σ h
    · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨him, ω, hω2, hω⟩ := hs τ hτ
      refine ⟨by rw [Complex.conj_im]; exact neg_ne_zero.2 him, (starRingEnd ℂ) ω, ?_, ?_⟩
      · rw [← map_pow, hω2]
      · rw [ghatC_conj hv.1.even ha.le, hω, map_zero]
  have hcl : ∀ σ ∈ S, (starRingEnd ℂ) σ ∈ S := by
    intro σ hσ
    rcases Finset.mem_union.1 hσ with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 h
      rw [Complex.conj_conj]; exact Finset.mem_union_left _ hτ
  have hev := card_even_of_conj S hcl fun σ hσ => (hS σ hσ).1
  have hle := card_offcross_le ha hv hpos S hS
  have hsub : s.card ≤ S.card := Finset.card_le_card Finset.subset_union_left
  obtain ⟨k, hk⟩ := hev
  omega

/-- **`dim V ≤ 2` ⇒ zeros on the cross**, now as the case "no exceptions" of the parity count. -/
theorem zeros_cross_of_dim_le_two {a : ℝ} (ha : 0 < a) (hm : gdim a ≤ 2) {v : ℝ → ℝ}
    (hv : v ∈ groundSpace a) (hpos : 0 < normSq v) {ω : ℂ} (hω : ghatC v a ω = 0) :
    (ω ^ 2).im = 0 := by
  by_contra hσ
  have := card_offcross_le_even ha hv hpos {ω ^ 2} (by
    intro σ hσ; rw [Finset.mem_singleton] at hσ; subst hσ; exact ⟨hσ, ω, rfl, hω⟩)
  rw [Finset.card_singleton] at this
  omega

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

/-- **Off-cross zeros of `Ξ`, counted by `z²`, number at most `2⌊(M − 1)/2⌋`**, if (a) holds for ground
states whose ground spaces eventually have dimension `≤ M`. -/
theorem xi_offcross_card_le {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) (s : Finset ℂ)
    (hs : ∀ σ ∈ s, σ.im ≠ 0 ∧ ∃ z, z ^ 2 = σ ∧ Xi z = 0) : s.card ≤ 2 * ((M - 1) / 2) := by
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
  have h0 := hconv.eventually_ne
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
  have hcount := card_offcross_le_even (ha n) hV (by rw [hN]; norm_num) (s.image fun σ => ζ σ ^ 2)
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

/-- **At most `2⌊(M − 1)/2⌋` zeros of `ζ` with `Re s > ½`**, under (a) for ground states whose ground
spaces eventually have dimension `≤ M`. -/
theorem zeta_offline_card_le {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} {M : ℕ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ M)
    (hconv : HypConv a g) (T : Finset ℂ)
    (hT : ∀ s ∈ T, riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ 1 / 2 < s.re) :
    T.card ≤ 2 * ((M - 1) / 2) := by
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

/-- A simple ground state has a one-dimensional ground space. -/
theorem gdim_le_one_of_simple {a : ℝ} {g : ℝ → ℝ} (ha : 0 < a) (hs : SimpleGround a g) :
    gdim a ≤ 1 := by
  have hgV : g ∈ groundSpace a := ((isGroundState_iff ha).1 hs.1).1
  set y := iotaGS a ⟨g, hgV⟩
  have hle : LinearMap.range (iotaGS a) ≤ Submodule.span ℝ {y} := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := hs.2 x.1 x.2
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    show c • hgV.1.memL2.toLp g = x.2.1.memL2.toLp x.1
    rw [← MemLp.toLp_const_smul]
    have h1 : (c • g) =ᵐ[volume] (fun t => c * g t) := Eventually.of_forall fun t => rfl
    exact MemLp.toLp_congr _ _ (EventuallyEq.trans h1 hc.symm)
  unfold gdim
  exact (Submodule.finrank_mono hle).trans ((finrank_span_le_card _).trans (by simp))

/-- **RH from (a) for any ground states with eventually `dim V ≤ 2`.** -/
theorem rh_of_dim_le_two {a : ℕ → ℝ} {g : ℕ → ℝ → ℝ} (ha : ∀ n, 0 < a n)
    (hgs : ∀ n, IsGroundState (a n) (g n)) (hdim : ∀ᶠ n in atTop, gdim (a n) ≤ 2)
    (hconv : HypConv a g) : RiemannHypothesis := by
  refine rh_of_prime_side_cross hgs ?_ hconv zetaNoZeroInUnitInterval
  filter_upwards [hdim] with n hn z hz
  obtain ⟨hV, hN⟩ := (isGroundState_iff (ha n)).1 (hgs n)
  have him := zeros_cross_of_dim_le_two (ha n) hn hV (by rw [hN]; norm_num) hz
  have : 2 * z.re * z.im = 0 := by rw [← him]; simp [pow_two]; ring
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; exact h

end Pilot1ca

#print axioms Pilot1ca.card_offcross_le
#print axioms Pilot1ca.card_offcross_le_even
#print axioms Pilot1ca.zeros_cross_of_dim_le_two
#print axioms Pilot1ca.gdim_le_one_of_simple
#print axioms Pilot1ca.rh_of_dim_le_two
#print axioms Pilot1ca.hurwitz_attract
#print axioms Pilot1ca.xi_offcross_card_le
#print axioms Pilot1ca.zeta_offline_card_le
