# Pre-registration 27: a second blind test of the tone law, on two even characters, `χ₅` and `χ₁₂` (round 116)

Committed before any zero, kernel, chain or response of `L(s, χ₅)` or `L(s, χ₁₂)` is computed. The scoring script `kLblind.py` is round 115's `kL8score.py` with only three changes: the character, the conductor, and the choice of primary primes. It is committed with this file.

**The law (unchanged from round 114).** `ω_n = 2π(n − 1/n)/q`, with nothing fitted. Round 115 (`χ₋₈`, odd) passed it once, blind.

**What is new.**
- Both characters are **even**, so the Γ factor is `Γ(¼ + it/2)` and `θ_χ = (t/2)ln(q/π) + Im log Γ(¼ + it/2)` (`kLzeros.py`/`kLlens.py`, env `LGA=0.25`). The law's derivation used ζ's Stirling phase, whose leading `r(ln 2r − 1)` term does not depend on the shift ¼ vs ¾. So the law predicts **no parity effect**.
- `χ₁₂`'s smallest prime not dividing `q` is `p = 5`, so the dominant line comes from a prime never yet dominant.

**Characters.**
- `χ₅(n) = (n/5)`: `+1` for `n ≡ ±1`, `−1` for `n ≡ ±2 (mod 5)`.
- `χ₁₂ = χ₋₃χ₋₄`: `+1` for `n ≡ ±1`, `−1` for `n ≡ ±5 (mod 12)`.

**Predictions (fixed now).**

| `L` | `p` | `χ(p)` | `ρ*` | `ω_p` |
|---|---|---|---|---|
| `χ₅` | 2 | −1 | 1.250 | **1.885** (= 3π/5) |
| `χ₅` | 3 | −1 | 1.667 | **3.351** (= 16π/15) |
| `χ₅` | 7 | −1 | 3.571 (far) | 8.617 |
| `χ₅` | 11 | +1 | 5.545 (far) | 13.709 |
| `χ₅` | 13 | −1 | 6.538 (far) | 16.240 |
| `χ₁₂` | 5 | −1 | 2.600 | **2.513** (= 4π/5) |
| `χ₁₂` | 7 | −1 | 3.571 (far) | 3.590 (= 4π/7) |
| `χ₁₂` | 11 | +1 | 5.545 (far) | 5.712 |
| `χ₁₂` | 13 | +1 | 6.538 (far) | 6.767 |

**Pipeline.** Identical to round 115 (`x = 3.00, 3.04, …, 12.00`; zeros to 1000; `LCOND = q`), with `LGA=0.25` in the zero and quantile stages.

**Criteria (±0.3).**
- **`χ₅`:**
  - **B2:** the chain's strongest line lies within ±0.3 of 1.885.
  - **B1:** `p = 3`'s strongest first-order line lies within ±0.3 of 3.351.
  - *Caveat, declared now:* 1.885 lies inside the 1.6–2.0 zone where earlier `L` responses showed a spurious low line, so B2 on `χ₅` is weak evidence even if it hits. B1 (3.351) is the clean test.
  - `p = 2`'s per-prime line is reported.
- **`χ₁₂`:**
  - **B2:** the chain's strongest line lies within ±0.3 of 2.513.
  - **B1:** `p = 5`'s strongest first-order line lies within ±0.3 of 2.513.
- **The law passes round 116 if B1 and B2 hold on both characters (4/4).** If only some of them hold, the result is reported as partial, naming which ones failed.
- **Secondary:**
  - far primes (`ρ* > 3`) scored as in round 115 (expected to be unreliable at first order);
  - kernel `λ` vs `1/q` (round 115 found `λ = 0.874/q` while the tones followed `1/q`);
  - the chain's top-4 distances to the nearest law line, unscored.
- **Declared risk for `χ₁₂`.** Its kernel edge `r_e ≈ 0.86/12` sits at `γ ≈ 0.9x`, i.e. at 3–11. That may fall below or at the first zero for many windows, a regime not tested before (round 115 already excluded 37 windows at `q = 8`). If the kernel stage cannot find an edge in most windows, this is reported in an amendment before the chain, and the `χ₁₂` test still runs as registered.

## Amendment 1: kernel stage (committed after the zeros and kernel dumps, before either chain, base chain or any per-prime response)

**Zeros.**
- `χ₅`: 904 up to 1000, starting 6.6485, 9.8314, 11.9588, 16.0338.
- `χ₁₂`: 1043, starting 3.8046, 6.6922, 8.8906, 11.1884.
- In both cases max `|N − smooth|` is ≤ 0.73 (no missed zeros) and `|Im Z|/|Z| ≤ 3.8·10⁻¹⁸`.

**`λ` vs `1/q`: both pass.** This is unlike `χ₋₈`.
- `χ₅`: `r_e = 0.1730 ± 0.0072`, 8 windows excluded, so `λ = 0.2009 = 1/4.98` (0.5% off).
- `χ₁₂`: `r_e = 0.0711 ± 0.0031`, 43 windows excluded, so `λ = 0.0826 = 1/12.1` (1% off).

The declared `χ₁₂` edge risk: 183 of 226 windows found an edge, so the test runs as registered.

**Narrow-method competitor (measured `K̃`), recorded before any tone.**
- **`χ₅`:** stable, with `β′` segments −0.86, −0.48, −0.46 and variance captured 0.95.
  - Predictions: **`p = 2` → 1.75** (range 1.49–1.89) and **`p = 3` → 3.25** (range 2.98–3.39).
  - The law and the competitor differ by only 0.10–0.13, so, both at ±0.3, the `χ₅` result cannot discriminate between them. The per-prime and chain errors are reported against both.
- **`χ₁₂`:** unstable (`β′` segments 2.93, −0.68, 0.23), and it finds **no stationary point in range**, so it makes no prediction.

The law's registered predictions and criteria are unchanged.
