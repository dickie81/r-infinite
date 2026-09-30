import PrimeRelax3
import ParityRelax

/-! # The certificate theorems as instances of the weighted certificate (round 250)

`PrimeRelax3`'s and `ParityRelax`'s certificate theorems are the `P = 2` and `P = 3` instances of `ParityRelax`'s weighted form (`wP`, `tauW`, `kappaW`, `sfunW`).
-/

open Real Filter Topology Complex MeasureTheory Set Matrix

namespace CertInstances

open Pilot1ca

theorem cw_zero : cw 0 = 0 := by simp [cw]

theorem cw_one : cw 1 = 0 := by simp [cw]

theorem cw_two : cw 2 = cP := by
  unfold cw cP
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  push_cast
  field_simp
  first
  | linear_combination (-1 : ℝ) * h
  | linear_combination (-Real.log 2) * h
  | linear_combination h

theorem wP_two (b : ℝ) (m : ℤ) : wP b 2 m = 0 := by
  simp [wP, Finset.sum_range_succ, cw_zero, cw_one]

theorem wP_three (b : ℝ) (m : ℤ) : wP b 3 m = cP * Real.cos (π * m * Real.log 2 / (4 * b)) := by
  simp [wP, Finset.sum_range_succ, cw_zero, cw_one, cw_two]

theorem tauW_two (b : ℝ) : tauW b 3.033953 2 = tau6 b := by
  simp [tauW, tau6, Finset.sum_range_succ, cw_zero, cw_one]

theorem tauW_three (b : ℝ) : tauW b 5.098076 3 = tauP b := by
  simp [tauW, tauP, Finset.sum_range_succ, cw_zero, cw_one, cw_two]

theorem kappaW_two (b : ℝ) : kappaW b 3.033953 2 = kappa6 b := by
  simp only [kappaW, kappa6, tauW_two]

theorem kappaW_three (b : ℝ) : kappaW b 5.098076 3 = kappaP b := by
  simp only [kappaW, kappaP, tauW_three]

theorem sfunW_two (b τ : ℝ) (ψl : ℕ → ℝ) (k : ℕ) : sfunW b τ (wP b 2) ψl k = sfun b τ ψl k := by
  unfold sfunW sfun
  simp [wP_two]

theorem sfunW_three (b τ : ℝ) (ψl : ℕ → ℝ) (k : ℕ) :
    sfunW b τ (wP b 3) ψl k = sfunP b τ cP (Real.log 2) ψl k := by
  unfold sfunW sfunP
  split_ifs <;> simp [wP_three]

/-- `PoleRelax.weilQ_ge_of_cert`, verbatim statement, as the `(K, N, T) = (2, 6, 3.033953)` instance. -/
theorem weilQ_ge_of_cert' {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 4) (hG : (gram6 a).PosDef)
    (hκ : ε ≤ kappa6 a)
    (hM : ((kappa6 a - ε) • gram6 a + gram6 a * diagonal (s6 a) * gram6 a).PosSemidef)
    {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) : ε ≤ weilQ a g := by
  have hlog : 2 * a < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  refine weilQ_ge_of_certW (K := 2) (N := 6) (T := 3.033953) ha (by linarith) (by norm_num)
    (by norm_num; linarith) (by simpa using hlog) ?_ (psil6 a) (fun k hk => hlow6 ha (by linarith) k hk)
    hG (by rwa [kappaW_two]) ?_ ha le_rfl hp hn
  · have := cinH7
    convert this using 2; push_cast; ring
  · rw [kappaW_two, tauW_two]
    have e : (fun i : Fin (6 + 2) => sfunW a (tau6 a) (wP a 2) (psil6 a) i) = s6 a := by
      funext i; exact sfunW_two a _ _ i
    rw [e]; exact hM

/-- `PrimeRelax.weilQ_ge_of_certP`, verbatim statement, as the `(K, N, T) = (3, 60, 5.098076)` instance. -/
theorem weilQ_ge_of_certP' {b ε : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (h2 : Real.log 2 ≤ 2 * b)
    (h3 : 2 * b < Real.log 3) (ψl : ℕ → ℝ)
    (hlow : ∀ k : ℕ, k < 60 → ψl (k + 1) ≤ modeE b ((k : ℤ) + 1)) (hG : (gramP b).PosDef)
    (hκ : ε ≤ kappaP b)
    (hM : ((kappaP b - ε) • gramP b
      + gramP b * diagonal (fun i : Fin 62 => sfunP b (tauP b) cP (Real.log 2) ψl i) * gramP b).PosSemidef)
    {a : ℝ} (ha : 0 < a) (hab : a ≤ b) {g : ℝ → ℝ} (hp : Probe a g) (hn : normSq g = 1) :
    ε ≤ weilQ a g := by
  refine weilQ_ge_of_certW (K := 3) (N := 60) (T := 5.098076) hb0 hb1 (by norm_num)
    (by norm_num; exact h2) (by simpa using h3) ?_ ψl hlow hG (by rwa [kappaW_three]) ?_ ha hab hp hn
  · have := cinH61
    convert this using 2; push_cast; ring
  · rw [kappaW_three, tauW_three]
    have e : (fun i : Fin (60 + 2) => sfunW b (tauP b) (wP b 3) ψl i)
        = fun i : Fin 62 => sfunP b (tauP b) cP (Real.log 2) ψl i := by
      funext i; exact sfunW_three b _ _ i
    rw [e]; exact hM

end CertInstances

#print axioms CertInstances.weilQ_ge_of_cert'
#print axioms CertInstances.weilQ_ge_of_certP'
