import WeilDedekind
import WeilChiDensity
import PrimeRaces

/-! # The twin criterion for every real-rooted base and every good character (round 245)

Round 220's twin-box criterion with `box 1` replaced by any even, antitone, nonnegative, real-rooted base `g₀` (`twinData_g`, `rh_iff_twins_realRooted`, `twins_rate_realRooted`; Pólya's theorem supplies real-rootedness for concave bases, `rh_iff_twins_concave`), and round 236's Dedekind criterion for every `GoodChar χ` with no real zero (`twinAdd`, `twinData_Kχ`, `rh_grh_iff_QKχ_twins`), with the instance `χ₋₇` (`good_chi7`) and `χ₋₃`, `χ₋₈`.
-/

open Complex Set
open Pilot1ca Pilot1bt PilotWeil PsiOmega TwinLandau DirichletCharacter

noncomputable section

namespace WeilTwinGeneral

/-! ## Part 1: real-rooted base probes -/

def cwg (g₀ : ℝ → ℝ) (b : ℝ) (q : ZIdx) : ℂ := ghatC g₀ b (ordi zetaZeroFamily q) ^ 2

def Gg (g₀ : ℝ → ℝ) (b : ℝ) (p : ℂ) : ℂ := ghatC g₀ b (p / (2 * I)) ^ 2

theorem weilExplicit_twin_antitone {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Icc 0 b)) (hnn : ∀ u ∈ Icc 0 b, 0 ≤ g₀ u) {l : ℝ} (hl : 0 ≤ l) :
    WeilExplicit zetaZeroFamily (fun z => ghatC (twin g₀ l) (l + b) z ^ 2)
      (hsq (twin g₀ l) (l + b)) := by
  have hpt := twin_probe hp hl
  obtain ⟨K, hK⟩ := ghat_antitone_strip hb hp.even hmono hnn hp.intervalIntegrable
  have hT := striptest_mul_sq (G := ghatC g₀ b) (m := fun z => 2 * Complex.cos (l * z))
    (ghatC_differentiable hp.intervalIntegrable) (by fun_prop) hK (fun t ht => norm_two_cos_strip hl ht)
  have e : (fun z => ghatC (twin g₀ l) (l + b) z ^ 2)
      = fun z => (2 * Complex.cos (l * z) * ghatC g₀ b z) ^ 2 := by
    funext z; rw [ghatC_twin hb hp hl]
  rw [e]
  refine weilExplicit_zeta hT (fun t => ?_) (fun r => ?_)
  · have := even_ghat_sq hpt.even (l + b) t
    rw [ghatC_twin hb hp hl, ghatC_twin hb hp hl] at this
    exact this
  · have := hsq_ofReal hpt (by linarith) r
    rw [ghatC_twin hb hp hl] at this
    exact this

theorem hasSum_wq_g {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Icc 0 b)) (hnn : ∀ u ∈ Icc 0 b, 0 ≤ g₀ u) {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun q => cwg g₀ b q * (2 + cexp (l * poleP q) + cexp (-(l * poleP q))))
      (weilQ (l + b) (twin g₀ l) : ℂ) := by
  have h := weilQ_eq_zero_sum (twin_probe hp hl) (by linarith)
    (weilExplicit_twin_antitone hb hp hmono hnn hl)
  convert h using 1
  funext q
  rw [ghatC_twin hb hp hl, TwinLandau.twin_sq, two_I_ordi]
  rfl

/-- **The twin data for any antitone, nonnegative, real-rooted base probe.** -/
theorem twinData_g {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Icc 0 b)) (hnn : ∀ u ∈ Icc 0 b, 0 ≤ g₀ u) (hRR : RealRooted b g₀) :
    TwinData poleP (cwg g₀ b) (Gg g₀ b) (fun l => weilQ (l + b) (twin g₀ l)) where
  summ := summable_norm_iff.2
    (weilQ_eq_zero_sum hp hb (weilExplicit_antitone_zeta hb hp hmono hnn)).summable
  re_lt := abs_re_poleP
  im_ne := im_poleP_ne
  finite := finite_poleP
  c_eq q := by unfold cwg Gg; rw [← two_I_ordi]; congr 2; field_simp
  G_even p := by
    unfold Gg; rw [show -p / (2 * I) = -(p / (2 * I)) by ring, ghatC_even hp.even]
  G_ne p hpr := by
    refine pow_ne_zero 2 fun h0 => ?_
    have h1 := hRR _ h0
    have e : (p / (2 * I)).im = -p.re / 2 := by simp [Complex.div_im]; ring
    rw [e] at h1; linarith
  hasSum l hl := hasSum_wq_g hb hp hmono hnn hl

theorem line_of_twins_g {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Icc 0 b)) (hnn : ∀ u ∈ Icc 0 b, 0 ≤ g₀ u) (hRR : RealRooted b g₀)
    (hQ : ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + b) (twin g₀ l)) (q0 : ZIdx) :
    (zetaZeroFamily q0).re = 1 / 2 := by
  have h := TwinLandau.abs_re_le (twinData_g hb hp hmono hnn hRR) (C := 0) le_rfl
    (fun l hl => by simpa using hQ l hl) q0
  rw [re_poleP] at h
  have := abs_nonpos_iff.1 h
  linarith

/-- **Weil's twin criterion with any real-rooted monotone base probe.** -/
theorem rh_iff_twins_realRooted {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Icc 0 b)) (hnn : ∀ u ∈ Icc 0 b, 0 ≤ g₀ u) (hRR : RealRooted b g₀) :
    RiemannHypothesis ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + b) (twin g₀ l) := by
  constructor
  · intro hRH l hl
    exact weilQ_nonneg_of_RH hRH (by linarith) (twin_probe hp hl)
  · intro hQ s hs htriv _
    exact line_of_twins_g hb hp hmono hnn hRR hQ ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

/-- **The graded form**, for any real-rooted monotone base probe. -/
theorem twins_rate_realRooted {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hmono : AntitoneOn g₀ (Icc 0 b)) (hnn : ∀ u ∈ Icc 0 b, 0 ≤ g₀ u) (hRR : RealRooted b g₀)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ weilQ (l + b) (twin g₀ l)) ↔
      ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ := by
  constructor
  · rintro ⟨C, h⟩ s hs
    have := TwinLandau.abs_re_le (twinData_g hb hp hmono hnn hRR) hσ h ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩
    rwa [re_poleP] at this
  · intro h
    exact (TwinLandau.rate_iff (twinData_g hb hp hmono hnn hRR) hσ).2 fun q => by
      rw [re_poleP]; exact h _ (nontrivial_zZF q)

/-- **Every even concave monotone profile is an admissible base probe** (Pólya, `Concave.lean`). -/
theorem rh_iff_twins_concave {b : ℝ} (hb : 0 < b) {g₀ : ℝ → ℝ} (hp : Probe b g₀)
    (hc : ConcaveOn ℝ (Ioo (-b) b) g₀) (h0 : 0 < g₀ 0)
    (hmono : AntitoneOn g₀ (Icc 0 b)) (hnn : ∀ u ∈ Icc 0 b, 0 ≤ g₀ u) :
    RiemannHypothesis ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + b) (twin g₀ l) := by
  refine rh_iff_twins_realRooted hb hp hmono hnn (realRooted_of_concaveOn hb hc hp.even ?_ h0)
  intro t ht
  rcases le_total 0 t with h | h
  · exact hnn t ⟨h, ht.2.le⟩
  · rw [← hp.even t]; exact hnn (-t) ⟨by linarith, by linarith [ht.1]⟩


/-! ## Part 1b: the box is an instance; `ghat_box_ne` is Pólya's theorem -/

theorem box_concave : ConcaveOn ℝ (Ioo (-1) 1) (box 1) := by
  refine (concaveOn_const (1 / Real.sqrt (2 * 1)) (convex_Ioo (-1) 1)).congr ?_
  intro u hu
  show 1 / Real.sqrt (2 * 1) = box 1 u
  rw [box_apply, if_pos (abs_le.2 ⟨hu.1.le, hu.2.le⟩)]

theorem box_realRooted : RealRooted 1 (box 1) :=
  realRooted_of_concaveOn one_pos box_concave (box_probe 1).even
    (fun t ht => by rw [box_apply]; split_ifs <;> positivity)
    (by rw [box_apply, if_pos (by norm_num)]; positivity)

/-- Round 131's `ghat_box_ne`, as an instance of `realRooted_of_concaveOn`. -/
theorem ghat_box_ne' {z : ℂ} (hz : z.im ≠ 0) : ghatC (box 1) 1 z ≠ 0 := fun h => hz (box_realRooted z h)

/-- Round 220's `rh_of_weil_twins` (both directions), as the box instance. -/
theorem rh_iff_twins_box : RiemannHypothesis ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ weilQ (l + 1) (twin (box 1) l) :=
  rh_iff_twins_realRooted one_pos (box_probe 1) box_antitone box_nonneg box_realRooted

/-! ## Part 2: `χ₋₇` -/

/-- `χ₋₇ = (·/7)`: residues `1, 2, 4 ↦ 1`, non-residues `3, 5, 6 ↦ −1`. -/
def χ₇ : MulChar (ZMod 7) ℤ where
  toFun a :=
    match a with
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | 3 => -1
    | 4 => 1
    | 5 => -1
    | 6 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

theorem isQuadratic_χ₇ : χ₇.IsQuadratic := by unfold MulChar.IsQuadratic; decide

theorem χ₇_nat (n : ℕ) :
    χ₇ n = if n % 7 = 0 then 0 else if n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4 then 1 else -1 := by
  have help : ∀ m : ℕ, m < 7 →
      χ₇ m = if m % 7 = 0 then 0 else if m % 7 = 1 ∨ m % 7 = 2 ∨ m % 7 = 4 then 1 else -1 := by
    decide
  rw [← ZMod.natCast_mod n 7, help _ (Nat.mod_lt _ (by norm_num)), Nat.mod_mod]

def chi7 : DirichletCharacter ℂ 7 := χ₇.ringHomComp (Int.castRingHom ℂ)

theorem chi7_nat (n : ℕ) : chi7 n = ((χ₇ n : ℤ) : ℂ) := rfl

theorem chi7_isQuadratic : chi7.IsQuadratic := isQuadratic_χ₇.comp _

theorem chi7_ne_one : chi7 ≠ 1 := fun h => by
  have h3 : IsUnit ((3 : ℕ) : ZMod 7) := by
    rw [← ZMod.coe_unitOfCoprime 3 (by norm_num : Nat.Coprime 3 7)]; exact Units.isUnit _
  have := congrArg (fun χ : DirichletCharacter ℂ 7 => χ (3 : ℕ)) h
  simp only [MulChar.one_apply h3, chi7_nat, χ₇_nat] at this
  norm_num at this

theorem chi7_isPrimitive : chi7.IsPrimitive := by
  rw [isPrimitive_def]
  have hd := conductor_dvd_level chi7
  have hle : conductor chi7 ≤ 7 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 1 ≤ conductor chi7 := Nat.pos_of_ne_zero (conductor_ne_zero chi7)
  interval_cases h : conductor chi7
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) chi7_ne_one
  all_goals first | rfl | exact absurd hd (by decide)

theorem sum_chi7 (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cR chi7 k =
    if n % 7 = 1 ∨ n % 7 = 3 ∨ n % 7 = 5 then 1 else if n % 7 = 2 ∨ n % 7 = 4 then 2 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, cR, chi7_nat, χ₇_nat]
    have e1 : (n + 1) % 7 = (n % 7 + 1) % 7 := by omega
    rw [e1]
    have h7 := Nat.mod_lt n (show 0 < 7 by norm_num)
    interval_cases n % 7 <;> norm_num

theorem sums_chi7 : ∀ x, 0 ≤ summ (cR chi7) x :=
  summ_nonneg_of_sum fun n => by rw [sum_chi7]; split_ifs <;> norm_num

theorem good_chi7 : GoodChar chi7 :=
  goodChar_of_sums chi7_ne_one chi7_isQuadratic chi7_isPrimitive sums_chi7

theorem hS7 : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction chi7 σ ≠ 0 := fun _ hσ _ =>
  LFunction_ne_zero_of_sums_nonneg chi7_ne_one chi7_isQuadratic sums_chi7 hσ

theorem grh_iff_twins_chi7 : GRH chi7 ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QC chi7 (l + 1) (twin (box 1) l) :=
  grh_iff_twins good_chi7 hS7

theorem weil_criterion_chi7 :
    (∀ (a : ℝ) (g : ℝ → ℝ), 0 < a → Probe a g → 0 ≤ QC chi7 a g) ↔ GRH chi7 :=
  weil_criterion_chi good_chi7 hS7

/-- The race mod 7 (quadratic residues against non-residues), unconditional `Ω±(x^θ)`, `θ < ½`. -/
theorem race_seven_half {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 1 / 2) (c X : ℝ) :
    (∃ x, X < x ∧ c * x ^ θ < summ (fχ chi7) x) ∧ (∃ x, X < x ∧ summ (fχ chi7) x < -(c * x ^ θ)) :=
  psiChi_omega_of_sums_nonneg chi7_ne_one chi7_isQuadratic chi7_isPrimitive sums_chi7 hθ hθ2 c X

/-! ## Part 3: the sum of twin data, and round 236 for every good character -/

/-- **Twin data add.** -/
theorem twinAdd {ι κ : Type*} {P₁ c₁ : ι → ℂ} {P₂ c₂ : κ → ℂ} {G : ℂ → ℂ} {Q₁ Q₂ : ℝ → ℝ}
    (D₁ : TwinData P₁ c₁ G Q₁) (D₂ : TwinData P₂ c₂ G Q₂) :
    TwinData (Sum.elim P₁ P₂) (Sum.elim c₁ c₂) G (fun l => Q₁ l + Q₂ l) where
  summ := Summable.sum _ D₁.summ D₂.summ
  re_lt := by
    rintro (q | i)
    · exact D₁.re_lt q
    · exact D₂.re_lt i
  im_ne := by
    rintro (q | i)
    · exact D₁.im_ne q
    · exact D₂.im_ne i
  finite R := by
    refine (((D₁.finite R).image Sum.inl).union ((D₂.finite R).image Sum.inr)).subset ?_
    rintro (q | i) hq
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨i, hq, rfl⟩
  c_eq := by
    rintro (q | i)
    · exact D₁.c_eq q
    · exact D₂.c_eq i
  G_even := D₁.G_even
  G_ne := D₁.G_ne
  hasSum l hl := by
    have h := HasSum.sum (f := fun q => Sum.elim c₁ c₂ q *
      (2 + cexp (l * Sum.elim P₁ P₂ q) + cexp (-(l * Sum.elim P₁ P₂ q)))) (D₁.hasSum l hl) (D₂.hasSum l hl)
    convert h using 1
    push_cast; ring

/-- `ζ`'s twin data in the normalisation of `GboxC` (weights doubled). -/
theorem twinData_zeta2 : TwinData poleP (fun q => 2 * cw q) GboxC
    (fun l => 2 * weilQ (l + 1) (twin (box 1) l)) where
  summ := (twinData_zeta.summ.mul_left 2).congr fun q => by simp
  re_lt := twinData_zeta.re_lt
  im_ne := twinData_zeta.im_ne
  finite := twinData_zeta.finite
  c_eq q := by
    show 2 * cw q = GboxC (poleP q)
    rw [twinData_zeta.c_eq q]; simp only [GboxC, Gbox]
  G_even := Dedekind4.twinData_chi4.G_even
  G_ne := Dedekind4.twinData_chi4.G_ne
  hasSum l hl := by
    have h1 := (twinData_zeta.hasSum l hl).mul_left 2
    convert h1 using 1
    · funext q; ring
    · push_cast; ring

section Ded

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

abbrev IdxKχ (χ : DirichletCharacter ℂ N) : Type := ZIdx ⊕ ZeroIdx (sqF (XiC χ))

def PKχ (χ : DirichletCharacter ℂ N) : IdxKχ χ → ℂ := Sum.elim poleP (fun i => 2 * I * tauC i)

def cKχ (χ : DirichletCharacter ℂ N) : IdxKχ χ → ℂ :=
  Sum.elim (fun q => 2 * cw q) (fun i => 2 * ghatC (box 1) 1 (tauC i) ^ 2)

/-- The Weil form of `ζ(s)L(s, χ)` on twin boxes (ζ-zeros doubled, as in round 236). -/
def QKχ (χ : DirichletCharacter ℂ N) (a : ℝ) (g : ℝ → ℝ) : ℝ := 2 * weilQ a g + QC χ a g

theorem twinData_Kχ (hG : GoodChar χ) (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    TwinData (PKχ χ) (cKχ χ) GboxC (fun l => QKχ χ (l + 1) (twin (box 1) l)) :=
  twinAdd twinData_zeta2 (twinData_chi hG hS)

theorem abs_re_PKχ (hG : GoodChar χ) (σ : ℝ) :
    (∀ q : IdxKχ χ, |(PKχ χ q).re| ≤ σ) ↔
      (∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ) ∧
        (∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → |2 * s.re - 1| ≤ σ) := by
  have e : ∀ i : ZeroIdx (sqF (XiC χ)),
      |(2 * I * tauC i).re| = |2 * (1 / 2 + I * tauC i).re - 1| := by
    intro i; congr 1; simp; ring
  constructor
  · intro h
    refine ⟨fun s hs => ?_, fun s hs h0 _ => ?_⟩
    · have hb := h (Sum.inl ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩)
      change |(poleP _).re| ≤ σ at hb
      rwa [re_poleP] at hb
    · obtain ⟨i, hi⟩ := tau_of_zero hG hs h0
      have hb := h (Sum.inr i)
      change |(2 * I * tauC i).re| ≤ σ at hb
      rw [e] at hb
      have hst : (1 / 2 + I * ((s - 1 / 2) / I)) = s := by field_simp; ring
      rcases hi with hi | hi
      · rwa [hi, hst] at hb
      · rw [hi] at hb
        have : (1 / 2 + I * -((s - 1 / 2) / I)).re = 1 - s.re := by
          rw [show 1 / 2 + I * -((s - 1 / 2) / I) = 1 - (1 / 2 + I * ((s - 1 / 2) / I)) by ring, hst]
          simp
        rw [this, show 2 * (1 - s.re) - 1 = -(2 * s.re - 1) by ring, abs_neg] at hb
        exact hb
  · rintro ⟨hz, hL⟩ (q | i)
    · change |(poleP q).re| ≤ σ
      rw [re_poleP]; exact hz _ (nontrivial_zZF q)
    · change |(2 * I * tauC i).re| ≤ σ
      obtain ⟨h0, h1, h2⟩ := zero_of_tau hG i
      rw [e]; exact hL _ h0 h1 h2

/-- **The graded criterion for `ζ·L(χ)`**, every good character. -/
theorem QKχ_twins_rate (hG : GoodChar χ) (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QKχ χ (l + 1) (twin (box 1) l)) ↔
      (∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ) ∧
        (∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → |2 * s.re - 1| ≤ σ) := by
  have := countable_ZeroIdxC hG
  rw [TwinLandau.rate_iff (twinData_Kχ hG hS) hσ, abs_re_PKχ hG]

/-- **Round 236 for every good character**: `RH ∧ GRH(χ) ⟺ 2Q_ζ + Q_χ ≥ 0` on twin boxes. -/
theorem rh_grh_iff_QKχ_twins (hG : GoodChar χ) (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) :
    (RiemannHypothesis ∧ GRH χ) ↔ ∀ l : ℝ, 0 ≤ l → 0 ≤ QKχ χ (l + 1) (twin (box 1) l) := by
  constructor
  · rintro ⟨hRH, hGRH⟩ l hl
    obtain ⟨K, hK⟩ := striptest_twin_box hl
    have h1 := weilQ_nonneg_of_RH hRH (by linarith : (0 : ℝ) < l + 1) (twin_probe (box_probe 1) hl)
    have h2 := QC_nonneg_of_GRH hG hGRH (twin_probe (box_probe 1) hl) (by linarith) hK
    unfold QKχ; linarith
  · intro hQ
    have h := (QKχ_twins_rate hG hS le_rfl).1 ⟨0, fun l hl => by simpa using hQ l hl⟩
    constructor
    · intro s hs htriv _
      have := abs_nonpos_iff.1 (h.1 s ⟨hs, htriv⟩)
      linarith
    · intro s hs h0 h1
      have := abs_nonpos_iff.1 (h.2 s hs h0 h1)
      linarith

end Ded

theorem hS3 : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction chi3 σ ≠ 0 := fun _ hσ _ =>
  LFunction_ne_zero_of_sums_nonneg chi3_ne_one chi3_isQuadratic sums_chi3 hσ
theorem hS8 : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction chi8 σ ≠ 0 := fun _ hσ _ =>
  LFunction_ne_zero_of_sums_nonneg chi8_ne_one chi8_isQuadratic sums_chi8 hσ

/-- `ζ_{ℚ(√−3)}`. -/
theorem rh_grh_iff_twins_Q3 : (RiemannHypothesis ∧ GRH chi3) ↔
    ∀ l : ℝ, 0 ≤ l → 0 ≤ 2 * weilQ (l + 1) (twin (box 1) l) + QC chi3 (l + 1) (twin (box 1) l) :=
  rh_grh_iff_QKχ_twins good_chi3 hS3
/-- `ζ_{ℚ(√−2)}`. -/
theorem rh_grh_iff_twins_Q8 : (RiemannHypothesis ∧ GRH chi8) ↔
    ∀ l : ℝ, 0 ≤ l → 0 ≤ 2 * weilQ (l + 1) (twin (box 1) l) + QC chi8 (l + 1) (twin (box 1) l) :=
  rh_grh_iff_QKχ_twins good_chi8 hS8
/-- `ζ_{ℚ(√−7)}`. -/
theorem rh_grh_iff_twins_Q7 : (RiemannHypothesis ∧ GRH chi7) ↔
    ∀ l : ℝ, 0 ≤ l → 0 ≤ 2 * weilQ (l + 1) (twin (box 1) l) + QC chi7 (l + 1) (twin (box 1) l) :=
  rh_grh_iff_QKχ_twins good_chi7 hS7
/-- Round 236's theorem recovered as an instance. -/
theorem rh_grh_iff_twins_Q4 : (RiemannHypothesis ∧ GRH chi4) ↔
    ∀ l : ℝ, 0 ≤ l → 0 ≤ Dedekind4.QK (l + 1) (twin (box 1) l) :=
  rh_grh_iff_QKχ_twins good_chi4 Dedekind4.hS4

end WeilTwinGeneral

#print axioms WeilTwinGeneral.twinData_g
#print axioms WeilTwinGeneral.rh_iff_twins_realRooted
#print axioms WeilTwinGeneral.twins_rate_realRooted
#print axioms WeilTwinGeneral.rh_iff_twins_concave
#print axioms WeilTwinGeneral.box_realRooted
#print axioms WeilTwinGeneral.ghat_box_ne'
#print axioms WeilTwinGeneral.rh_iff_twins_box
#print axioms WeilTwinGeneral.good_chi7
#print axioms WeilTwinGeneral.grh_iff_twins_chi7
#print axioms WeilTwinGeneral.weil_criterion_chi7
#print axioms WeilTwinGeneral.race_seven_half
#print axioms WeilTwinGeneral.twinAdd
#print axioms WeilTwinGeneral.QKχ_twins_rate
#print axioms WeilTwinGeneral.rh_grh_iff_QKχ_twins
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q3
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q8
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q7
#print axioms WeilTwinGeneral.rh_grh_iff_twins_Q4
