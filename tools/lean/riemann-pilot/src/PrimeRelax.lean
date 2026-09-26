import Mathlib
import PoleRelax

/-! # Weil positivity past the first prime: every support `2a ≤ 0.8` (round 123)

Round 122's relaxation stopped at `a = 1/4`, because every mode bound paid the kernel remainder `err(a)`. Here:
* **The primes are diagonal in the circle modes.** For `0 ≤ u₀ = log n ≤ 2a`, `f(u₀) = Σ_m p_m cos(πm u₀/4a)`
  (`hasSum_autocorr`). For `2a < log 3` only `n = 2` enters, with `−2S(g) = −√2 log 2 · f(log 2)`. So every mode
  carries the exact weight `ψ_m − √2 log 2 · cos(πm log 2/4a)` (`prime_trunc`, `weilQ_ge_relaxP`).
* **The low modes are exact.** The certificate supplies rigorous lower bounds `psiC m ≤ ψ_m` for `m ≤ 60`, from
  arb quadrature. The tail `|m| > 60` uses the Lean-proved `Cin(61π/2) ≥ 5.098076` (`cinH61`), with the crude
  `err(a)` and `√2 log 2` losses. Those cost little, because the tail level enters only through the tail mass.
* **One certificate at `a* = 2/5` covers `(0, 2/5]`**, by monotonicity (`weilQ_mono`).

`weilQ_ge_prime`: granted `CertP`, every normalised even probe at any support `0 < a ≤ 2/5` has
`Q(g) ≥ 1/10000`. The range is past `2a = log 2`, where the prime `2` enters. There the true `λ₁` falls from
`1.3·10⁻³` to `1.8·10⁻⁴`.
-/

open Real Filter Topology Complex MeasureTheory Set Matrix

noncomputable section

namespace Pilot1ca

/-- For `2a < log 3`, only `n = 2` contributes: `S(g) = (log 2/√2)·f(log 2)`. -/
theorem primeS_eq_two' {a : ℝ} (ha : 2 * a < Real.log 3) {g : ℝ → ℝ} (hg : Probe a g) :
    primeS g = Real.log 2 / Real.sqrt 2 * autocorr g (Real.log 2) := by
  unfold primeS
  rw [tsum_eq_single 2]
  · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; push_cast; ring
  · intro n hn
    rcases lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h3 : 3 ≤ n := by omega
      have hl : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h3)
      have hz : autocorr g (Real.log n) = 0 :=
        autocorr_eq_zero hg.supp (by
          have : 0 < Real.log n := by linarith [Real.log_pos (by norm_num : (1:ℝ) < 3)]
          rw [abs_of_pos this]; linarith)
      simp [hz]

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

/-! ## The instance `a* = 2/5`, `N = 60` -/

/-- The certified low-mode energies `psiC m ≤ ψ_m` at `a = 2/5`, `m = 1..60` (arb quadrature,
`kprime_cert_result.json`). -/
def psiCq : List ℚ := [0.688568794300, 2.013331473896, 2.774484591478, 2.815596337748, 2.846702991061, 3.185245856055, 3.471881729962, 3.491235788331, 3.508020588441, 3.703514231535, 3.880542594592, 3.893159698229, 3.904630380514, 4.042119704689, 4.170218366909, 4.179573312059, 4.188282542908, 4.294323958399, 4.394692119389, 4.402124206762, 4.409142788809, 4.495447885342, 4.577957722802, 4.584122301706, 4.589999631299, 4.662763521485, 4.732811140061, 4.738077415190, 4.743132609078, 4.806028796089, 4.866885252868, 4.871481662250, 4.875916442279, 4.931301974497, 4.985099737058, 4.989177428578, 4.993127401990, 5.042604833142, 5.090811312339, 5.094475471465, 5.098036172580, 5.142744557515, 5.186412634134, 5.189739401798, 5.192980663098, 5.233758592322, 5.273669323662, 5.276715587034, 5.279689998833, 5.317172739806, 5.353921519320, 5.356730898119, 5.359479052637, 5.394159367395, 5.428210451972, 5.430817126225, 5.433371009032, 5.465638813516, 5.497361201701, 5.499792452047]

def psiC (k : ℕ) : ℝ := ((psiCq.getD (k - 1) 0 : ℚ) : ℝ)

def cP : ℝ := Real.sqrt 2 * Real.log 2
def tauP (a : ℝ) : ℝ := 5.098076 - errK a - cP
def kappaP (a : ℝ) : ℝ :=
  weilConst + (-Real.log ((Real.exp a - 1) / (Real.exp a + 1)) + (π / 2 - Real.arctan (Real.sinh a))) + tauP a
def gramP (a : ℝ) : Matrix (Fin 62) (Fin 62) ℝ := Matrix.of fun i j => gC a i j
def sP (a : ℝ) : Fin 62 → ℝ := fun i => sfunP a (tauP a) cP (Real.log 2) psiC i

theorem cP_nonneg : 0 ≤ cP := by unfold cP; have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity

theorem htailP {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℤ) (hn : (60 : ℤ) < n) :
    tauP a ≤ modeEP a cP (Real.log 2) n := by
  have hnr : (61 : ℝ) ≤ n := by exact_mod_cast hn
  have hψ := modeE_ge ha ha1 (n := n) (by omega)
  have hC : Cin (122 * π / 4) ≤ Cin (π * n / 2) := Cin_mono (by positivity) (by nlinarith [Real.pi_pos])
  have hc := cinH61
  have hπ := Real.pi_gt_three
  have h1 : 2 * Real.sin (π * n / 2) / (π * n) ≤ 2 / (π * n) :=
    div_le_div_of_nonneg_right (by linarith [Real.sin_le_one (π * n / 2)]) (by positivity)
  have h2 : 2 / (π * n) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hD : 0 ≤ a * (1 - 2 * Real.sin (π * n / 2) / (π * n)) := mul_nonneg ha.le (by linarith)
  have hcos : cP * Real.cos (π * n * Real.log 2 / (4 * a)) ≤ cP :=
    by nlinarith [Real.cos_le_one (π * n * Real.log 2 / (4 * a)), cP_nonneg]
  unfold tauP modeEP; linarith

/-- **The certificate at `a* = 2/5`** (checked by `frontier/nullvec/kprime_cert.py`): the 60 quadrature bounds, the
Gram matrix, `ε ≤ κ`, and `(κ − ε)G + G diag(s) G ⪰ 0`, with `ε = 1/10000`. -/
def CertP : Prop :=
  (∀ k : ℕ, k < 60 → psiC (k + 1) ≤ modeE (2 / 5) ((k : ℤ) + 1)) ∧ (gramP (2 / 5)).PosDef ∧
    (1 / 10000 : ℝ) ≤ kappaP (2 / 5) ∧
    ((kappaP (2 / 5) - 1 / 10000) • gramP (2 / 5) + gramP (2 / 5) * diagonal (sP (2 / 5)) * gramP (2 / 5)).PosSemidef

/-- **Weil positivity through the first prime**: granted `CertP`, every normalised even probe at every support
`0 < a ≤ 2/5` (`2a ≤ 0.8`, past `log 2`) has `Q(g) ≥ 1/10000`. -/
theorem weilQ_ge_prime {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 2 / 5) (hc : CertP) {g : ℝ → ℝ} (hp : Probe a g)
    (hn : normSq g = 1) : (1 / 10000 : ℝ) ≤ weilQ a g := by
  obtain ⟨hlow, hG, hκ, hM⟩ := hc
  rw [← weilQ_mono ha ha1 hp]
  have hp' := probe_mono ha1 hp
  set b : ℝ := 2 / 5 with hb
  have hb0 : (0 : ℝ) < b := by norm_num
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_gt'
  have hprime : 2 * primeS g = cP * autocorr g (Real.log 2) := by
    rw [primeS_eq_two' (by rw [hb]; norm_num; linarith) hp']
    unfold cP
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 2 := by positivity
    have e : Real.log 2 / Real.sqrt 2 = Real.sqrt 2 * Real.log 2 / 2 := by
      rw [div_eq_div_iff hs0.ne' (by norm_num)]; rw [mul_comm (Real.sqrt 2), mul_assoc, ← sq, hs]
    rw [e]; ring
  have hgram : gramP b = gramM b 62 := by
    ext i j; simp only [gramP, Matrix.of_apply]; exact (gramM_eq hb0 62 i j).symm
  rw [hgram] at hG hM
  have hq := quad_lower (gramM b 62) hG (sP b) (xv b g 62) (nrm := normSq g)
    (bessel_gram hb0.le hp'.memL2 hp'.supp 62) hκ hM
  have hr := weilQ_ge_relaxP hb0 hp' hn (Real.log_nonneg (by norm_num)) (by rw [hb]; norm_num at hl2 ⊢; linarith)
    hprime 60 (tauP b) psiC (htailP hb0 (by rw [hb]; norm_num)) hlow
  rw [farField_eq hb0] at hr
  rw [hn] at hq
  unfold kappaP at hq
  have hs : sP b = fun i : Fin 62 => sfunP b (tauP b) cP (Real.log 2) psiC i := rfl
  rw [hs, mul_one, mul_one] at hq
  exact le_trans hq hr

end Pilot1ca

#print axioms Pilot1ca.prime_trunc
#print axioms Pilot1ca.weilQ_ge_relaxP
#print axioms Pilot1ca.weilQ_ge_prime
