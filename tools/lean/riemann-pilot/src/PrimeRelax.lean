import Mathlib
import PoleRelax

/-! # Weil positivity past the first prime: every support `2a ≤ 0.8` (round 123)

Round 122's relaxation stopped at `a = 1/4`, because every mode bound paid the kernel remainder `err(a)`. Here:
* **The primes are diagonal in the circle modes.** For `0 ≤ u₀ = log n ≤ 2a`, `f(u₀) = Σ_m p_m cos(πm u₀/4a)`
  (`hasSum_autocorr`). For `2a < log 3` only `n = 2` enters, with `−2S(g) = −√2 log 2 · f(log 2)`. So every mode
  carries the exact weight `ψ_m − √2 log 2 · cos(πm log 2/4a)` (`prime_trunc`, `weilQ_ge_relaxP`, now in PoleRelax.lean).
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
  rw [← weilQ_mono ha.le ha1 hp]
  have hp' := hp.mono ha1
  set b : ℝ := 2 / 5 with hb
  have hb0 : (0 : ℝ) < b := by norm_num
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_gt
  have hprime : 2 * primeS g = cP * autocorr g (Real.log 2) := by
    rw [primeS_eq_two (by rw [hb]; norm_num; linarith) hp']
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

#print axioms Pilot1ca.weilQ_ge_prime
