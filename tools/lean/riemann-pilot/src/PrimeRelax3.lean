import Mathlib
import PrimeRelax

/-! # Weil positivity up to the second prime: every support `2a ≤ 1.0986 < log 3` (round 134)

Round 123's construction (`PrimeRelax.lean`), re-run at the last support before the prime `n = 3` enters:
`a* = 0.5493`, so `2a* = 1.0986 < log 3 ≈ 1.098612` (`log_three_gt`). Below `log 3` the prime side is still the
single term `n = 2` (`primeS_eq_two`), diagonal in the circle modes, so the whole relaxation (`weilQ_ge_relaxP`,
`bessel_gram`, `quad_lower`) and the tail (`htailP`, from `cinH61`) are reused unchanged. Only the 60 certified
mode energies change (`psiCq3`, arb quadrature at `a*`, `kprime3_cert_result.json`).

`weilQ_ge_prime3`: granted `CertP3`, every normalised even probe at every support `0 < a ≤ 0.5493` has
`Q(g) ≥ 2·10⁻⁸`. A Ritz estimate of the true `λ₁(a*)` is `≈ 5.6·10⁻⁸`; the relaxation's bound is `4.199·10⁻⁸` (the certificate
passes at `ε = 4.1·10⁻⁸` and fails at `4.3·10⁻⁸`).
-/

open Real Filter Topology Complex MeasureTheory Set Matrix

noncomputable section

namespace Pilot1ca

/-! ## The instance `a* = 0.5493`, `N = 60` -/

/-- The certified low-mode energies `psiC3 m ≤ ψ_m` at `a = 0.5493`, `m = 1..60` (arb quadrature,
`kprime3_cert_result.json`). -/
def psiCq3 : List ℚ := [0.726993499410, 2.121999227586, 2.913621204192, 2.939808998694, 2.958016663734, 3.306253646618, 3.601631319111, 3.614040111523, 3.624352934205, 3.825385599896, 4.007641151067, 4.015711618649, 4.022843011621, 4.164226851199, 4.296065136389, 4.302037480083, 4.307480152929, 4.416527869196, 4.519809666155, 4.524547860041, 4.528946642290, 4.617700719821, 4.702597855627, 4.706523973920, 4.710214231249, 4.785044476640, 4.857114430502, 4.860465842661, 4.863643899241, 4.928327387784, 4.990938149716, 4.993861497051, 4.996652084316, 5.053612350120, 5.108959192115, 5.111551373942, 5.114038640149, 5.164923470038, 5.214516830110, 5.216845204985, 5.219088587337, 5.265069209100, 5.309992738469, 5.312106019475, 5.314149052086, 5.356087758518, 5.397145282375, 5.399079835112, 5.400955355441, 5.439505380875, 5.477309612985, 5.479093302244, 5.480826688888, 5.516494740003, 5.551523420237, 5.553178067324, 5.554789339314, 5.587976372167, 5.620609200738, 5.622152212913]

def psiC3 (k : ℕ) : ℝ := ((psiCq3.getD (k - 1) 0 : ℚ) : ℝ)

def sP3 (a : ℝ) : Fin 62 → ℝ := fun i => sfunP a (tauP a) cP (Real.log 2) psiC3 i

/-- **The certificate at `a* = 0.5493`** (checked by `frontier/nullvec/kprime3_cert.py`): the 60 quadrature bounds,
the Gram matrix, `ε ≤ κ`, and `(κ − ε)G + G diag(s) G ⪰ 0`, with `ε = 2·10⁻⁸`. -/
def CertP3 : Prop :=
  (∀ k : ℕ, k < 60 → psiC3 (k + 1) ≤ modeE (5493 / 10000) ((k : ℤ) + 1)) ∧ (gramP (5493 / 10000)).PosDef ∧
    (1 / 50000000 : ℝ) ≤ kappaP (5493 / 10000) ∧
    ((kappaP (5493 / 10000) - 1 / 50000000) • gramP (5493 / 10000)
      + gramP (5493 / 10000) * diagonal (sP3 (5493 / 10000)) * gramP (5493 / 10000)).PosSemidef

/-- **Weil positivity up to the second prime**: granted `CertP3`, every normalised even probe at every support
`0 < a ≤ 0.5493` (`2a ≤ 1.0986 < log 3`) has `Q(g) ≥ 2·10⁻⁸`. -/
theorem weilQ_ge_prime3 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 5493 / 10000) (hc : CertP3) {g : ℝ → ℝ}
    (hp : Probe a g) (hn : normSq g = 1) : (1 / 50000000 : ℝ) ≤ weilQ a g :=
  weilQ_ge_of_certP (by norm_num) (by norm_num)
    (by have := Real.log_two_lt_d9; norm_num at this ⊢; linarith) (by have := log_three_gt; linarith)
    psiC3 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 ha ha1 hp hn

end Pilot1ca

#print axioms Pilot1ca.weilQ_ge_prime3
