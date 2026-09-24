import Mathlib
import TheoremC

/-! # The pole-overlap gap bound, and the Galerkin transfer

**Gap bound (operator level, no spectral decomposition).** Let `φ₀` be the ground state of the
pole-free form `Q₀` (`μ₁ = λ₀`), and `ψ` a normalised probe `⊥ φ₀` attaining
`μ₂ = inf {Q₀(χ)/‖χ‖² : χ ⊥ φ₀}`. With `c₁ = φ̂₀(i/2)`, `c₂ = ψ̂(i/2)`:

  `λ₂(Q) − λ₁(Q) ≥ c₂²(μ₂ − μ₁)/(c₁² + c₂²)`   (`lam2Ge_gap`).

* Upper bound on `λ₁`: the trial function `ψ − (c₂/c₁)φ₀` has zero pole term (`lam_le_trial`).
* Lower bound on `λ₂`: every 2-dimensional span has a unit vector `⊥ φ₀`, where `Q ≥ Q₀ ≥ μ₂`
  (`lam2Ge_of_Q0`).

So `c₂ ≠ 0` and `μ₂ > μ₁` give simplicity with an explicit gap (`simple_of_pole_overlap`).

**Galerkin transfer.** If truncation spaces `T K` (of probes) approximate every probe in `L²` and
archimedean energy, and the truncated forms have `λ₂(T K) ≥ λ₁(T K) + γ` eventually, then
`λ₂(Q) ≥ λ₁(Q) + γ` and the ground state is simple (`simple_of_trunc_gap`). The truncated `λ₂` is in
min–max form (`Lam2GeT`).
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace Pilot1ca

/-! ## The operator-level gap bound -/

theorem poleR_ne_zero_of_groundState0 {a : ℝ} (ha : 0 < a) {φ : ℝ → ℝ} (hφ : IsGroundState0 a φ) :
    poleR φ a ≠ 0 := by
  intro h0
  have hq0 : weilQ0 a φ = lam0 a := by
    have := ((isGroundState0_iff ha).1 hφ).1.2; rw [this, hφ.2.1, mul_one]
  have hq : weilQ a φ = lam0 a := by
    have : weilQ a φ = weilQ0 a φ + 2 * poleR φ a ^ 2 := by unfold weilQ0; ring
    rw [this, hq0, h0]; ring
  have := lam_le hφ.1 hφ.2.1
  have := lam0_lt_lam ha
  linarith

/-- **The trial bound**: `λ₁(c₁² + c₂²) ≤ Q₀(ψ)c₁² + μ₁c₂²`. -/
theorem lam_le_trial {a : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) :
    lam a * (poleR φ a ^ 2 + poleR ψ a ^ 2)
      ≤ weilQ0 a ψ * poleR φ a ^ 2 + lam0 a * poleR ψ a ^ 2 := by
  have hc₁ := poleR_ne_zero_of_groundState0 ha hφ
  set s := -(poleR ψ a / poleR φ a)
  have hf := probe_add_smul hψ hφ.1 s
  have hpole : poleR (fun t => ψ t + s * φ t) a = 0 := by
    rw [poleR_add hψ.memL2 (hφ.1.memL2.const_mul s) a, poleR_smul]
    simp only [s]; field_simp; ring
  have hB : bil0 a ψ φ = 0 := by
    rw [bil0_comm, euler_lagrange0 ha hφ hψ, xcorr_comm, hx, mul_zero]
  have hQf : weilQ a (fun t => ψ t + s * φ t) = weilQ0 a ψ + s ^ 2 * lam0 a := by
    have : weilQ a (fun t => ψ t + s * φ t) = weilQ0 a (fun t => ψ t + s * φ t) := by
      unfold weilQ0; rw [hpole]; ring
    rw [this, weilQ0_add_smul hψ hφ.1, hB]
    have hq0 : weilQ0 a φ = lam0 a := by
      have := ((isGroundState0_iff ha).1 hφ).1.2; rw [this, hφ.2.1, mul_one]
    rw [hq0]; ring
  have hNf : normSq (fun t => ψ t + s * φ t) = 1 + s ^ 2 := by
    rw [normSq_add_smul hψ.memL2 hφ.1.memL2, hn, hx, hφ.2.1]; ring
  have h := lam_mul_le hf
  rw [hQf, hNf] at h
  have hc2 : 0 < poleR φ a ^ 2 := by positivity
  have hs2 : s ^ 2 * poleR φ a ^ 2 = poleR ψ a ^ 2 := by
    simp only [s]; field_simp
  have hm := mul_le_mul_of_nonneg_right h hc2.le
  have e1 : lam a * (1 + s ^ 2) * poleR φ a ^ 2 = lam a * (poleR φ a ^ 2 + poleR ψ a ^ 2) := by
    rw [← hs2]; ring
  have e2 : (weilQ0 a ψ + s ^ 2 * lam0 a) * poleR φ a ^ 2
      = weilQ0 a ψ * poleR φ a ^ 2 + lam0 a * poleR ψ a ^ 2 := by
    rw [← hs2]; ring
  linarith

theorem Lam2Ge.anti {a s s' : ℝ} (h : Lam2Ge a s) (hs : s' ≤ s) : Lam2Ge a s' := by
  intro g k hg hk hng hnk hx
  obtain ⟨α, β, hab, h1⟩ := h g k hg hk hng hnk hx
  exact ⟨α, β, hab, hs.trans h1⟩

/-- **Interlacing in min–max form**: `λ₂(Q) ≥ μ₂(Q₀)`. -/
theorem lam2Ge_of_Q0 {a μ₂ : ℝ} {φ : ℝ → ℝ} (hφ : Probe a φ)
    (hμ : ∀ χ, Probe a χ → xcorr χ φ 0 = 0 → μ₂ * normSq χ ≤ weilQ0 a χ) : Lam2Ge a μ₂ := by
  intro g k hg hk hng hnk hx
  set p := xcorr g φ 0
  set q := xcorr k φ 0
  have hlin : ∀ α β : ℝ, xcorr (fun t => α * g t + β * k t) φ 0 = α * p + β * q := by
    intro α β
    rw [xcorr_zero_eq]
    show _ = α * xcorr g φ 0 + β * xcorr k φ 0
    rw [xcorr_zero_eq, xcorr_zero_eq]
    have e : (fun t => (α * g t + β * k t) * φ t) = fun t => α * (g t * φ t) + β * (k t * φ t) := by
      funext t; ring
    have i1 : Integrable (fun t => α * (g t * φ t)) :=
      (hg.memL2.integrable_mul hφ.memL2).const_mul α
    have i2 : Integrable (fun t => β * (k t * φ t)) :=
      (hk.memL2.integrable_mul hφ.memL2).const_mul β
    rw [e, integral_add i1 i2, integral_const_mul, integral_const_mul]
  have hN : ∀ α β : ℝ, normSq (fun t => α * g t + β * k t) = α ^ 2 + β ^ 2 := by
    intro α β; rw [normSq_comb hg.memL2 hk.memL2, hng, hnk, hx]; ring
  have hfin : ∀ α β : ℝ, α ^ 2 + β ^ 2 = 1 → α * p + β * q = 0 →
      ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧ μ₂ ≤ weilQ a (fun t => α * g t + β * k t) := by
    intro α β hab h0
    refine ⟨α, β, hab, ?_⟩
    have hc : Probe a (fun t => α * g t + β * k t) := by
      have := probe_add_smul (probe_smul hg α) hk β; simpa using this
    have := hμ _ hc (by rw [hlin]; exact h0)
    rw [hN, hab, mul_one] at this
    exact this.trans (weilQ0_le a _)
  by_cases hr : p ^ 2 + q ^ 2 = 0
  · have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    exact hfin 1 0 (by norm_num) (by rw [hp, hq]; ring)
  · have hpos : 0 < p ^ 2 + q ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hr)
    set r := Real.sqrt (p ^ 2 + q ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt hpos.le
    refine hfin (q / r) (-(p / r)) ?_ ?_
    · rw [div_pow, neg_sq, div_pow, ← add_div, hr2]; field_simp; ring
    · field_simp; ring

/-- **The pole-overlap gap bound**: `λ₂(Q) ≥ λ₁(Q) + c₂²(μ₂ − μ₁)/(c₁² + c₂²)`. -/
theorem lam2Ge_gap {a μ₂ : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) (hψμ : weilQ0 a ψ = μ₂)
    (hμ : ∀ χ, Probe a χ → xcorr χ φ 0 = 0 → μ₂ * normSq χ ≤ weilQ0 a χ) :
    Lam2Ge a (lam a + poleR ψ a ^ 2 * (μ₂ - lam0 a) / (poleR φ a ^ 2 + poleR ψ a ^ 2)) := by
  have hc₁ := poleR_ne_zero_of_groundState0 ha hφ
  have hden : 0 < poleR φ a ^ 2 + poleR ψ a ^ 2 := by positivity
  have ht := lam_le_trial ha hφ hψ hn hx
  rw [hψμ] at ht
  refine (lam2Ge_of_Q0 hφ.1 hμ).anti ?_
  have : poleR ψ a ^ 2 * (μ₂ - lam0 a) / (poleR φ a ^ 2 + poleR ψ a ^ 2) ≤ μ₂ - lam a := by
    rw [div_le_iff₀ hden]; nlinarith [ht]
  linarith

/-- **Simplicity from a nonzero pole overlap**, with the explicit gap above. -/
theorem simple_of_pole_overlap {a μ₂ : ℝ} (ha : 0 < a) {φ ψ : ℝ → ℝ} (hφ : IsGroundState0 a φ)
    (hψ : Probe a ψ) (hn : normSq ψ = 1) (hx : xcorr ψ φ 0 = 0) (hψμ : weilQ0 a ψ = μ₂)
    (hμ : ∀ χ, Probe a χ → xcorr χ φ 0 = 0 → μ₂ * normSq χ ≤ weilQ0 a χ)
    (hc₂ : poleR ψ a ≠ 0) (hgap : lam0 a < μ₂) {g : ℝ → ℝ} (hg : IsGroundState a g) :
    SimpleGround a g := by
  have hc₁ := poleR_ne_zero_of_groundState0 ha hφ
  have hden : 0 < poleR φ a ^ 2 + poleR ψ a ^ 2 := by positivity
  have hκ : 0 < poleR ψ a ^ 2 * (μ₂ - lam0 a) / (poleR φ a ^ 2 + poleR ψ a ^ 2) := by
    apply div_pos _ hden
    exact mul_pos (by positivity) (by linarith)
  exact simpleGround_of_lam2 ha (by linarith) (lam2Ge_gap ha hφ hψ hn hx hψμ hμ) hg

/-! ## Continuity of `Q_λ` in `L²` plus archimedean energy -/

/-- `Q_λ(x + y) ≤ (1 + t)Q_λ(x) + (1 + 1/t)Q_λ(y)` (Cauchy–Schwarz for the nonnegative `Q_λ`). -/
theorem Qlam_add_le {a : ℝ} {x y : ℝ → ℝ} (hx : Probe a x) (hy : Probe a y) {t : ℝ} (ht : 0 < t) :
    Qlam a (fun u => x u + y u) ≤ (1 + t) * Qlam a x + (1 + 1 / t) * Qlam a y := by
  have e1 := Qlam_add_smul hx hy 1
  have e2 := Qlam_add_smul hx hy (-(1 / t))
  have n2 := Qlam_nonneg (probe_add_smul hx hy (-(1 / t)))
  simp only [one_mul] at e1
  unfold Qlam
  set B := bil0 a x y + 2 * poleR x a * poleR y a - lam a * xcorr x y 0
  set Qx := weilQ a x - lam a * normSq x
  set Qy := weilQ a y - lam a * normSq y
  have hQx : 0 ≤ Qx := Qlam_nonneg hx
  have hQy : 0 ≤ Qy := Qlam_nonneg hy
  rw [e2] at n2
  have hB : 2 * B ≤ t * Qx + Qy / t := by
    have h1 : 0 ≤ Qx - 2 * B / t + Qy / t ^ 2 := by
      have : Qx + 2 * -(1 / t) * B + (-(1 / t)) ^ 2 * Qy = Qx - 2 * B / t + Qy / t ^ 2 := by
        field_simp; ring
      linarith
    have h2 : 0 ≤ t * (Qx - 2 * B / t + Qy / t ^ 2) := mul_nonneg ht.le h1
    have : t * (Qx - 2 * B / t + Qy / t ^ 2) = t * Qx - 2 * B + Qy / t := by field_simp
    linarith
  have : (1 + 1 / t) * Qy = Qy + Qy / t := by field_simp
  rw [e1]; nlinarith

/-- `‖x + y‖² ≤ (1 + t)‖x‖² + (1 + 1/t)‖y‖²`. -/
theorem normSq_add_le_t {x y : ℝ → ℝ} (hx : MemLp x 2 volume) (hy : MemLp y 2 volume) {t : ℝ}
    (ht : 0 < t) : normSq (fun u => x u + y u) ≤ (1 + t) * normSq x + (1 + 1 / t) * normSq y := by
  have e1 := normSq_add_smul hx hy 1
  have e2 := normSq_add_smul hx hy (-(1 / t))
  have n2 := normSq_nonneg (fun u => x u + -(1 / t) * y u)
  simp only [one_mul] at e1
  rw [e2] at n2
  set X := xcorr x y 0
  have hB : 2 * X ≤ t * normSq x + normSq y / t := by
    have h2 : 0 ≤ t * (normSq x + 2 * -(1 / t) * X + (-(1 / t)) ^ 2 * normSq y) :=
      mul_nonneg ht.le n2
    have : t * (normSq x + 2 * -(1 / t) * X + (-(1 / t)) ^ 2 * normSq y)
        = t * normSq x - 2 * X + normSq y / t := by field_simp; ring
    linarith
  have : (1 + 1 / t) * normSq y = normSq y + normSq y / t := by field_simp
  rw [e1]; nlinarith [normSq_nonneg x, normSq_nonneg y]

theorem Qlam_smul (a c : ℝ) (f : ℝ → ℝ) : Qlam a (fun u => c * f u) = c ^ 2 * Qlam a f := by
  unfold Qlam; rw [weilQ_smul, normSq_smul]; ring

/-- `Q_λ` is dominated by `L²` norm plus archimedean energy. -/
theorem Qlam_le_d {a : ℝ} (ha : 0 < a) : ∃ C, 0 < C ∧ ∀ f, Probe a f →
    Qlam a f ≤ C * (normSq f + archE f) := by
  set K := 2 * (∫ u in (-a)..a, Real.exp (-u)) + |weilConst| + |lam a| + 2 * primeWeight a
  have hK : 0 ≤ K := by
    have : 0 ≤ primeWeight a := Finset.sum_nonneg fun n _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have : 0 ≤ ∫ u in (-a)..a, Real.exp (-u) :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => (exp_pos _).le
    positivity
  refine ⟨K + 1, by linarith, fun f hf => ?_⟩
  have h := Qlam_le ha hf
  have hN := normSq_nonneg f
  have hE := archE_nonneg hf
  nlinarith

/-! ## The Galerkin transfer -/

/-- **Galerkin density.** Every probe is the limit, in `L²` and archimedean energy, of vectors from
the truncation spaces. -/
def TruncDense (a : ℝ) (T : ℕ → Submodule ℝ (ℝ → ℝ)) : Prop :=
  ∀ f, Probe a f → ∃ F : ℕ → ℝ → ℝ, (∀ᶠ K in atTop, F K ∈ T K) ∧
    Tendsto (fun K => normSq (fun t => F K t - f t) + archE (fun t => F K t - f t)) atTop (𝓝 0)

/-- **`λ₂(Q|S) ≥ s`** in min–max form: every span of two vectors of `S` contains a vector with
`Q ≥ s‖·‖²`. -/
def Lam2GeT (a : ℝ) (S : Submodule ℝ (ℝ → ℝ)) (s : ℝ) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧
    s * normSq (fun t => α * g t + β * h t) ≤ weilQ a (fun t => α * g t + β * h t)

/-- **Transfer of `λ₂` lower bounds from truncations to the operator.** -/
theorem lam2Ge_of_trunc {a : ℝ} (ha : 0 < a) {T : ℕ → Submodule ℝ (ℝ → ℝ)}
    (hsub : ∀ K f, f ∈ T K → Probe a f) (hdense : TruncDense a T) {s : ℕ → ℝ} {s₀ : ℝ}
    (hs : Tendsto s atTop (𝓝 s₀)) (hT : ∀ᶠ K in atTop, Lam2GeT a (T K) (s K)) {ε : ℝ}
    (hε : 0 < ε) : Lam2Ge a (s₀ - ε) := by
  intro g h hg hh hng hnh hx
  have hNx : ∀ α β : ℝ, α ^ 2 + β ^ 2 = 1 → normSq (fun t => α * g t + β * h t) = 1 := by
    intro α β hab; rw [normSq_comb hg.memL2 hh.memL2, hng, hnh, hx]; linarith
  set l := lam a
  set σ := s₀ - l
  by_cases hσ : σ - ε ≤ 0
  · refine ⟨1, 0, by norm_num, ?_⟩
    have h1 := Qlam_nonneg (a := a) (f := fun t => 1 * g t + 0 * h t) (by
      have := probe_add_smul (probe_smul hg 1) hh 0; simpa using this)
    rw [hNx 1 0 (by norm_num), mul_one] at h1
    linarith
  push Not at hσ
  obtain ⟨G, hGT, hGd⟩ := hdense g hg
  obtain ⟨H, hHT, hHd⟩ := hdense h hh
  obtain ⟨C, hC, hCle⟩ := Qlam_le_d ha
  set t := min 1 (ε / (6 * σ))
  have hσ0 : 0 < σ := by linarith
  have ht : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htσ : t * σ ≤ ε / 6 := by
    have := min_le_right 1 (ε / (6 * σ))
    calc t * σ ≤ ε / (6 * σ) * σ := mul_le_mul_of_nonneg_right this hσ0.le
      _ = ε / 6 := by field_simp
  set u := 1 + t
  set v := 1 + 1 / t
  have hu : 0 < u := by positivity
  have hv : 0 < v := by positivity
  set D : ℕ → ℝ := fun K => (normSq (fun x => G K x - g x) + archE (fun x => G K x - g x))
    + (normSq (fun x => H K x - h x) + archE (fun x => H K x - h x))
  have hD : Tendsto D atTop (𝓝 0) := by simpa using hGd.add hHd
  set L : ℕ → ℝ := fun K => ((s K - l) * (1 - v * (2 * D K)) - u * v * (2 * C * D K)) / u ^ 2
  have hL : Tendsto L atTop (𝓝 (σ / u ^ 2)) := by
    have := ((((hs.sub_const l).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub ((hD.const_mul 2).const_mul v))).sub
      (((hD.const_mul C).const_mul 2).const_mul (u * v))).div_const (u ^ 2))
    convert this using 2
    · simp only [L]; ring
    · simp [σ]
  have hlim : σ - ε < σ / u ^ 2 := by
    have hu2 : u ^ 2 ≤ 1 + 3 * t := by simp only [u]; nlinarith
    have : σ * (1 - 3 * t) ≤ σ / u ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hu2 hσ0.le, sq_nonneg t]
    nlinarith
  have hsK : ∀ᶠ K in atTop, 0 < s K - l := by
    have := hs.eventually (Ioi_mem_nhds (show l < s₀ by linarith))
    filter_upwards [this] with K hK; linarith [show l < s K from hK]
  obtain ⟨K, hLK, hsK', hGK, hHK, hTK⟩ :=
    ((hL.eventually (Ioi_mem_nhds hlim)).and (hsK.and (hGT.and (hHT.and hT)))).exists
  have hLK' : σ - ε < L K := hLK
  obtain ⟨α, β, hab, hQy⟩ := hTK (G K) hGK (H K) hHK
  refine ⟨α, β, hab, ?_⟩
  -- the probes involved
  have pG := hsub K _ hGK
  have pH := hsub K _ hHK
  have pdG : Probe a (fun x => G K x - g x) := (probe_add_sub pG hg).2
  have pdH : Probe a (fun x => H K x - h x) := (probe_add_sub pH hh).2
  have comb : ∀ {p q : ℝ → ℝ}, Probe a p → Probe a q → Probe a (fun x => α * p x + β * q x) :=
    fun hp hq => by have := probe_add_smul (probe_smul hp α) hq β; simpa using this
  have px := comb hg hh
  have py := comb pG pH
  have pe := comb pdG pdH
  have hα : α ^ 2 ≤ 1 := by nlinarith [sq_nonneg β]
  have hβ : β ^ 2 ≤ 1 := by nlinarith [sq_nonneg α]
  -- names for the quantities involved
  set x : ℝ → ℝ := fun x => α * g x + β * h x with hxdef
  set y : ℝ → ℝ := fun x => α * G K x + β * H K x with hydef
  set e : ℝ → ℝ := fun x => α * (G K x - g x) + β * (H K x - h x) with hedef
  set Qx := Qlam a x
  set Qy := Qlam a y
  set Qe := Qlam a e
  set Ny := normSq y
  set Ne := normSq e
  set d1 := normSq (fun x => G K x - g x) + archE (fun x => G K x - g x)
  set d2 := normSq (fun x => H K x - h x) + archE (fun x => H K x - h x)
  have hDK : D K = d1 + d2 := rfl
  -- size of the error `e = y − x`
  have hQe : Qe ≤ 2 * C * D K := by
    have h1 := Qlam_add_le (probe_smul pdG α) (probe_smul pdH β) one_pos
    rw [Qlam_smul, Qlam_smul] at h1
    have q1 : Qlam a (fun x => G K x - g x) ≤ C * d1 := hCle _ pdG
    have q2 : Qlam a (fun x => H K x - h x) ≤ C * d2 := hCle _ pdH
    have n1 : 0 ≤ Qlam a (fun x => G K x - g x) := Qlam_nonneg pdG
    have n2 : 0 ≤ Qlam a (fun x => H K x - h x) := Qlam_nonneg pdH
    have m1 := mul_le_mul_of_nonneg_right hα n1
    have m2 := mul_le_mul_of_nonneg_right hβ n2
    have : Qe ≤ (1 + 1) * (α ^ 2 * Qlam a (fun x => G K x - g x))
        + (1 + 1 / 1) * (β ^ 2 * Qlam a (fun x => H K x - h x)) := h1
    rw [hDK]; norm_num at this; linarith
  have hNe : Ne ≤ 2 * D K := by
    have h1 := normSq_add_le (pdG.memL2.const_mul α) (pdH.memL2.const_mul β)
    have e1 : normSq (fun x => α * (G K x - g x)) = α ^ 2 * normSq (fun x => G K x - g x) :=
      normSq_smul _ _
    have e2 : normSq (fun x => β * (H K x - h x)) = β ^ 2 * normSq (fun x => H K x - h x) :=
      normSq_smul _ _
    rw [e1, e2] at h1
    have n1 := normSq_nonneg (fun x => G K x - g x)
    have n2 := normSq_nonneg (fun x => H K x - h x)
    have a1 := archE_nonneg pdG
    have a2 := archE_nonneg pdH
    have m1 := mul_le_mul_of_nonneg_right hα n1
    have m2 := mul_le_mul_of_nonneg_right hβ n2
    have : Ne ≤ 2 * (α ^ 2 * normSq (fun x => G K x - g x))
        + 2 * (β ^ 2 * normSq (fun x => H K x - h x)) := h1
    rw [hDK]; linarith
  -- `y = x + e` and `x = y + (x − y)`
  have hy : Qy ≤ u * Qx + v * Qe := by
    have := Qlam_add_le px pe ht
    have eq : (fun t => x t + e t) = y := by funext t; simp only [x, y, e]; ring
    rw [eq] at this; exact this
  have hxN : 1 ≤ u * Ny + v * Ne := by
    have := normSq_add_le_t (x := y) (y := fun t => x t - y t) py.memL2
      (by exact px.memL2.sub py.memL2) ht
    have eq : (fun t => y t + (x t - y t)) = x := by funext t; ring
    have en : normSq (fun t => x t - y t) = Ne := by
      unfold Ne normSq; congr 1; funext t; simp only [x, y, e]; ring
    rw [eq, hNx α β hab, en] at this
    exact this
  -- the truncated inequality in `Q_λ` form
  have hyQ : (s K - l) * Ny ≤ Qy := by
    have : Qy = weilQ a y - l * Ny := rfl
    linarith
  have hQx0 : 0 ≤ Qx := Qlam_nonneg px
  have hQe0 : 0 ≤ Qe := Qlam_nonneg pe
  have hNe0 : 0 ≤ Ne := normSq_nonneg _
  -- combine
  have hNy : 1 - v * (2 * D K) ≤ u * Ny := by
    have := mul_le_mul_of_nonneg_left hNe hv.le
    linarith
  have k1 : (s K - l) * (1 - v * (2 * D K)) ≤ (s K - l) * (u * Ny) :=
    mul_le_mul_of_nonneg_left hNy hsK'.le
  have k2 : u * ((s K - l) * Ny) ≤ u * Qy := mul_le_mul_of_nonneg_left hyQ hu.le
  have k3 : u * Qy ≤ u * (u * Qx + v * Qe) := mul_le_mul_of_nonneg_left hy hu.le
  have k4 : u * v * Qe ≤ u * v * (2 * C * D K) :=
    mul_le_mul_of_nonneg_left hQe (mul_nonneg hu.le hv.le)
  have hmain : (s K - l) * (1 - v * (2 * D K)) - u * v * (2 * C * D K) ≤ u ^ 2 * Qx := by
    have e1 : (s K - l) * (u * Ny) = u * ((s K - l) * Ny) := by ring
    have e2 : u * (u * Qx + v * Qe) = u ^ 2 * Qx + u * v * Qe := by ring
    linarith
  have hQx : L K ≤ Qx := by
    simp only [L]; rw [div_le_iff₀ (by positivity)]; linarith
  have : weilQ a x = Qx + l := by
    show weilQ a x = Qlam a x + l
    unfold Qlam; rw [hNx α β hab]; ring
  rw [this]; linarith

/-- **Galerkin: a uniform truncated gap gives simplicity.** If truncation spaces are dense (in `L²` and
energy) and eventually `λ₂(T K) ≥ Q(f)/‖f‖² + γ` for every nonzero `f ∈ T K` (i.e.
`λ₂(T K) ≥ λ₁(T K) + γ`), then `λ₂(Q) ≥ λ₁(Q) + γ/2` and every ground state is simple. -/
theorem simple_of_trunc_gap {a : ℝ} (ha : 0 < a) {T : ℕ → Submodule ℝ (ℝ → ℝ)}
    (hsub : ∀ K f, f ∈ T K → Probe a f) (hdense : TruncDense a T) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ᶠ K in atTop, ∀ f ∈ T K, 0 < normSq f →
      Lam2GeT a (T K) (weilQ a f / normSq f + γ))
    {g : ℝ → ℝ} (hg : IsGroundState a g) : SimpleGround a g := by
  obtain ⟨F, hFT, hFd⟩ := hdense g hg.1
  obtain ⟨C, hC, hCle⟩ := Qlam_le_d ha
  have hgV := ((isGroundState_iff ha).1 hg)
  have hQg : Qlam a g = 0 := by unfold Qlam; rw [hgV.1.2, hgV.2]; ring
  -- `‖F K − g‖² → 0` and `Q_λ(F K − g) → 0`
  have hNd : Tendsto (fun K => normSq (fun t => F K t - g t)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hFd
      (Eventually.of_forall fun K => normSq_nonneg _) ?_
    filter_upwards [hFT] with K hK
    have := archE_nonneg (probe_add_sub (hsub K _ hK) hg.1).2
    linarith
  have hQd : Tendsto (fun K => Qlam a (fun t => F K t - g t)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hFd.const_mul C) ?_ ?_
    · filter_upwards [hFT] with K hK
      exact Qlam_nonneg (probe_add_sub (hsub K _ hK) hg.1).2
    · filter_upwards [hFT] with K hK
      exact hCle _ (probe_add_sub (hsub K _ hK) hg.1).2
  -- the Rayleigh quotient of `F K` tends to `λ₁`
  have hsmall : ∀ᶠ K in atTop, normSq (fun t => F K t - g t) < 1 / 4 :=
    hNd.eventually (Iio_mem_nhds (by norm_num))
  have hR : Tendsto (fun K => weilQ a (F K) / normSq (F K)) atTop (𝓝 (lam a)) := by
    have hbound : ∀ᶠ K in atTop, 1 / 4 ≤ normSq (F K) ∧ Qlam a (F K) ≤ 2 * Qlam a (fun t => F K t - g t) := by
      filter_upwards [hFT, hsmall] with K hK hs
      have pF := hsub K _ hK
      have pd := (probe_add_sub pF hg.1).2
      constructor
      · have := normSq_add_le_t (x := F K) (y := fun t => g t - F K t) pF.memL2
          (by exact hg.1.memL2.sub pF.memL2) one_pos
        have e : (fun u => F K u + (g u - F K u)) = g := by funext u; ring
        rw [e, hg.2.1, normSq_neg_sub] at this
        norm_num at this; linarith
      · have := Qlam_add_le hg.1 pd one_pos
        have e : (fun u => g u + (F K u - g u)) = F K := by funext u; ring
        rw [e, hQg] at this; norm_num at this; linarith
    have hq : Tendsto (fun K => Qlam a (F K) / normSq (F K)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using hQd.const_mul 8) ?_ ?_
      · filter_upwards [hbound, hFT] with K ⟨h1, _⟩ hK
        exact div_nonneg (Qlam_nonneg (hsub K _ hK)) (by linarith)
      · filter_upwards [hbound, hFT] with K ⟨h1, h2⟩ hK
        have hQd0 : 0 ≤ Qlam a (fun t => F K t - g t) :=
          Qlam_nonneg (probe_add_sub (hsub K _ hK) hg.1).2
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left h1 hQd0]
    have := hq.const_add (lam a)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hbound] with K ⟨h1, _⟩
    unfold Qlam; field_simp; ring
  have hT : ∀ᶠ K in atTop, Lam2GeT a (T K) (weilQ a (F K) / normSq (F K) + γ) := by
    filter_upwards [hgap, hFT, hsmall] with K hK hFK hs
    have hpos : 0 < normSq (F K) := by
      have pF := hsub K _ hFK
      have pd := (probe_add_sub pF hg.1).2
      have := normSq_add_le_t (x := F K) (y := fun t => g t - F K t) pF.memL2
        (by exact hg.1.memL2.sub pF.memL2) one_pos
      have e : (fun u => F K u + (g u - F K u)) = g := by funext u; ring
      rw [e, hg.2.1, normSq_neg_sub] at this
      norm_num at this; linarith
    exact hK (F K) hFK hpos
  have h2 := lam2Ge_of_trunc ha hsub hdense (hR.add_const γ) hT (half_pos hγ)
  exact simpleGround_of_lam2 ha (s := lam a + γ / 2) (by linarith) (h2.anti (by linarith)) hg

end Pilot1ca

#print axioms Pilot1ca.lam_le_trial
#print axioms Pilot1ca.lam2Ge_of_Q0
#print axioms Pilot1ca.lam2Ge_gap
#print axioms Pilot1ca.simple_of_pole_overlap
#print axioms Pilot1ca.lam2Ge_of_trunc
#print axioms Pilot1ca.simple_of_trunc_gap
