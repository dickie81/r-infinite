/-
# Bounding the wander, rung 0 (round 190)

Plain statement. The prime drift `ψ(x) − x` eventually stays within `±(2/5)·x`
(`wander_rung0`), i.e. `ψ(x)/x` is eventually trapped in `[0.6, 1.4]`. This is Chebyshev's
level (1850), built from Mathlib's explicit bounds `ψ(x) ≤ log 4·x + 2√x·log x` and
`ψ(x) ≥ (x−1)·log 2 − log(x+2)`.

The ladder above this rung (none formalised here):
* rung 1, PNT: `ψ(x) − x = o(x)` (needs ζ ≠ 0 on `Re s = 1`, which Mathlib has, plus a Tauberian step);
* rung 2, de la Vallée Poussin: `O(x·e^{−c√log x})` (quantitative zero-free region + truncated
  explicit formula);
* rung 3, Korobov–Vinogradov: `O(x·e^{−c(log x)^{3/5}(log log x)^{−1/5}})` (the best known, 1958);
* RH: `O(√x·log² x)`.
-/
import Mathlib

open Real Filter Asymptotics Chebyshev

namespace WanderBound

lemma sqrt_log_small : ∀ᶠ x : ℝ in atTop, 2 * √x * log x ≤ (1 / 100) * x := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound (c := 1 / 200) (by norm_num)
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  have hl : 0 ≤ log x := log_nonneg hx1
  have hs : √x = x ^ (1 / 2 : ℝ) := sqrt_eq_rpow x
  rw [norm_of_nonneg hl, norm_of_nonneg (by positivity)] at hx
  have hsq : √x * √x = x := mul_self_sqrt (by linarith)
  rw [← hs] at hx
  have hs0 : 0 ≤ √x := sqrt_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left hx hs0]

lemma log_small : ∀ᶠ x : ℝ in atTop, log 2 + log (x + 2) ≤ (1 / 100) * x := by
  have h := isLittleO_log_id_atTop.bound (c := 1 / 400) (by norm_num)
  filter_upwards [h, eventually_ge_atTop 2000] with x hx hx2
  have hl : 0 ≤ log x := log_nonneg (by linarith)
  rw [norm_of_nonneg hl, id, norm_of_nonneg (by linarith)] at hx
  have h1 : log (x + 2) ≤ log 2 + log x := by
    rw [← log_mul (by norm_num) (by linarith)]
    exact log_le_log (by linarith) (by linarith)
  have h2 : log 2 < 1 := by have := log_two_lt_d9; linarith
  nlinarith

/-- **Rung 0 (Chebyshev level):** eventually `|ψ(x) − x| ≤ (2/5)·x`. -/
theorem wander_rung0 : ∀ᶠ x : ℝ in atTop, |ψ x - x| ≤ (2 / 5) * x := by
  filter_upwards [sqrt_log_small, log_small, eventually_ge_atTop 1] with x h1 h2 hx
  have hup := psi_le hx
  have hlo := psi_ge' (by linarith : (0 : ℝ) ≤ x)
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have l4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  rw [abs_le]
  constructor <;> nlinarith

end WanderBound
