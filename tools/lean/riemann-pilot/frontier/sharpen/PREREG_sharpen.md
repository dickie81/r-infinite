# Pre-registration: sharpening rung 3 towards the Korobov–Vinogradov exponent (round 213)

Written before `ksharpen.py` was run and before the Lean steps S1b–S2 were written.

## Plan
- **S1 (layer II, many good coordinates).**
  - Write `N = u^20`, `M = ⌊u⁸⌋`, `u^R ≤ |t| < u^{R+1}`, `K = ⌊R/4⌋ + 6`.
  - Use every coordinate `j` with `12j ≥ R+5` and `24j + 6 ≤ 5R`, the window `G`.
  - Each `j ∈ G` is no-wrap and saves `u^{−(R−4j−1)} ≤ u^{−R/6}`.
  - Total saving `u^{−R·#G/6}`, against the loss `u²` from `M^{2η}` (`η ≤ 1/8`).
- **Generic growth.** If VMVT holds at `ℓ(K) ≤ B₀K^q` with `η ≤ 1/8` and `log C = O(ℓ²)`, then the per-block saving is `N^{−c/λ^{2q−2}}`. That gives `PolylogGrowth a` for `a ≥ (2q−2)/(2q−1)`.
  - `q = 3` (current weak VMVT): `a = 4/5`.
- **S2 (layer I, bad tuples by class Hölder).**
  - Bound bad tuples by `T_BB ≤ C(p,k−1)²(k−1)^{2(s+k)} J_{s+k}(⌈P/p⌉)`.
  - Close by induction on `P`, with a trivial bound below `P₀ = (4k)^{8k}`.
  - This gives `η_m = (1−1/k)^m k(k−1)/2` with no second branch. So `η ≤ 1/8` at `m = ⌈k log(4k²)⌉`, and `ℓ = k(m+1) ≤ B₀(ε)K^{2+ε}`.
  - Every `a > 2/3` follows, i.e. every exponent below `3/5`.

## Predictions (checked by `ksharpen.py`)
- **P1.** `#G ≥ 1` and `R·#G/6 − 2 ≥ R²/100` for every `16 ≤ R ≤ 10⁵`.
- **P2.** With `q = 3` (weak VMVT, `ℓ = K + 2K³`), the required threshold `Λ(L)` satisfies `Λ·L^{−4/5} ≤ A` uniformly. That is, the chain closes at `a = 4/5` and fails for `a = 0.79`.
- **P3.** Under S2's recursion, `log C_m / ℓ²` stays below `3` for `2 ≤ k ≤ 200` at `m = ⌈k log(4k²)⌉`, and `ℓ = k(m+1) ≤ 3k² log(4k)`.
- **P4.** Under S2, the per-block exponent `ρ(λ) = (R#G/6 − 2)/(40ℓ²)` satisfies `ρ·λ²·log²(λ+2) ≥ c > 0` over `λ ∈ [0.8, 10⁴]`, with `c` stated in the output.

A failure of P1–P4 stops the corresponding Lean step and is reported.
