# Pre-registration: fake gear sets (round 178)

Written and committed before `kfakegears.py` is run.

## The owner's hypothesis (G, "locked gears")

If a gear set matches our densities (`1/log`), speeds (`log q`) and tooth amplitudes, then how
far its prime count drifts is limited by how regular its integers ("the floor") are:

> θ_D ≤ max(½, θ_F) + 0.10 for every system tested.

Here `θ_F` is the growth exponent of the floor error and `θ_D` that of the prime drift, both
on the ζ scale (defined below). **G is falsified** if any system has
`θ_D − max(½, θ_F) > 0.10`.

## Systems

All are integer-supported, run to `X = 10⁷`. "Tilted" means the gears are higher-dimensional:
one prime norm carries several teeth at different angles.

| id | dim | gears | tilt |
|---|---|---|---|
| R1 | 1 | real primes | parallel |
| C1 | 1 | Cramér fakes: each `n ≥ 2` is a prime with probability `min(1, 1/log n)` | parallel |
| R2 | 2 | Gaussian ideals of ℤ[i]: `p ≡ 1 (4)` gives two tilted gears of norm `p`; `p ≡ 3 (4)` gives one gear of norm `p²`; one gear of norm 2 | tilted pairs |
| T2 | 2 | real primes, each split (two tilted gears) or inert with probability ½ | random tilts |
| CT2 | 2 | Cramér primes with random split/inert | fake primes, random tilts |
| R4 | 4 | `ζ(s)ζ(s−1)` (ℤ⁴ up to the 2-factor): each prime is a plain gear plus a weight-`p` gear, i.e. `p + 1` teeth per norm | many tilts |
| C4 | 4 | Cramér primes with the same two-gear structure | fake primes, many tilts |
| Z1 | 1 | real primes, greedily modified so the drift gains `−2 Re(x^ρ/ρ)`, `ρ = ¾ + 5i` ("zero-phase" plant) | parallel |
| P1 | 1 | as Z1 with the opposite sign, `+2 Re(x^ρ/ρ)` ("pole-phase" plant) | parallel |

- The fake families C1, T2, CT2, C4 use 3 seeds each.
- **Plants.** The plant is ramped in smoothly over `10³ ≤ x ≤ 10⁴`. Realisation is greedy over
  `n = 2, 3, …`: `n` is made a gear iff `T(n) − θ_P(n−1) > (log n)/2`, where `T` is the real
  `θ` plus the plant. Composites may be promoted to gears and real primes may be dropped.

## Measurements

- **Floor error** `F(x) = N(x) − A x^k`.
  - `N(x)` counts the generalised integers `≤ x` (ideals by norm, with multiplicity).
  - `k = 1` for dims 1 and 2, `k = 2` for dim 4.
  - `A` is known for real systems (1, π/4, π²/12) and fitted by least squares on `[X/100, X]` for fakes and plants.
- **Drift** `D(x) = θ_P(x) − main`, where `θ_P` is the log-weighted gear count.
  - Mains: `x`; for R4/C4 `x + x²/2` with gear weight `(1 + q)`.
  - Inert gears in dim 2 count `log(p²)` at `p²`.
- **Exponent.** Least-squares slope of `log max|·|` over dyadic blocks `[2^j, 2^{j+1})`, `j = 14…22`,
  minus `(k − 1)` to put dim 4 on the ζ scale.

## Predictions (mine, recorded to be scored)

- **E1** Real systems R1, R2, R4: `θ_D ∈ [0.40, 0.60]`. `θ_F ≤ 0.10` (R1), `∈ [0.15, 0.45]` (R2, circle problem), `≤ 0.20` (R4).
- **E2** Unplanted fakes C1, T2, CT2, C4: `θ_D ∈ [0.40, 0.60]` and `θ_F ∈ [0.35, 0.65]`. The fakes' √x prime noise leaks into their integers; the real systems' does not.
  - T2 caveat: its primes are real, so its noise comes only from the random tilts.
- **E3** Pole plant P1: `θ_D ∈ [0.65, 0.85]` and `θ_F ∈ [0.65, 0.85]`. A pole of the gear zeta shows up in both.
- **E4** Zero plant Z1: `θ_D ∈ [0.65, 0.85]` and `θ_F ≤ 0.60`.
  - This is the discriminating case. Beurling theory puts zeros of the gear zeta into the drift but not into the integer count, so **I predict G fails on Z1**.
  - If instead Z1's floor comes out `≥ 0.65`, G survives this test.

## Caveats

- These are finite-range slope estimates over ~1.5 decades of block maxima. They are
  evidence, not theorems, and cannot bear on RH either way.
- A Z1 floor below ½ at `10⁷` would be a finite-range observation, not a construction of a
  Beurling system with `θ_N < ½` and an off-line zero; that is open as far as I know (round 166, [unverified]).
