# Pre-registration 26: a blind test of the parameter-free tone law on `L(s, χ₋₈)` (round 115)

Committed before any zero, kernel, chain or response of `L(s, χ₋₈)` is computed. The scoring script `kL8score.py` is committed with this file and is not changed afterwards (any change will be an amendment with the reason).

**The law under test (round 114).** `ω_n = 2π(n − 1/n)/q`, from `K̃(r) = r ln 2r − r + √(r²−1) − r arccosh r` with the stationary point `ρ* = qr* = cosh(ln n)`. No parameter is fitted to `χ₋₈`. All of the law's previous agreements were post hoc; this is its first blind test.

**Why `χ₋₈`.** It is the first odd real character not yet examined whose predicted lines sit above the `x ∈ [3,12]` low-frequency floor (peak search starts at 1.5):
- `χ₋₇` would put its dominant `p = 2` line at 1.35, which is not resolvable.
- Even characters would need a different Γ factor (`Γ(¼ + it/2)`), meaning a pipeline change.

`χ₋₈` is odd, has conductor 8 and `θ_χ = (t/2)ln(8/π) + Im log Γ(¾ + it/2)`. It takes `χ(2) = 0`, `χ(p) = +1` for `p ≡ 1, 3 (mod 8)` and `−1` for `p ≡ 5, 7 (mod 8)`. A new feature: the dominant prime `p = 3` has `χ = +1`, whereas both previous `L` tests read a `χ = −1` prime.

**Predictions (fixed now).**

| `p` | `χ(p)` | `ρ* = (p + 1/p)/2` | `ω_p = 2π(p − 1/p)/8` |
|---|---|---|---|
| 3 | +1 | 1.667 | **2.094** (= 2π/3) |
| 5 | −1 | 2.600 | **3.770** (= 6π/5) |
| 7 | −1 | 3.571 | 5.386 (= 12π/7) |
| 11 | +1 | 5.545 | 8.568 (= 30π/11) |
| 13 | −1 | 6.538 | 10.150 (= 42π/13) |

**Pipeline (identical to rounds 111/112).**
1. Zeros to 1000 (`LQ=8 kLzeros.py`, 4 height segments).
2. Merge, count check and quantile base (`LQ=8 LTAG=L8 kLlens.py zeros`).
3. Kernel dumps (`LCOND=8 klinkernel.py 1000 L8quant.json true=true 15`) on `x = 3.00, 3.04, …, 12.00` (226 points).
4. The chain on the true zeros and on the quantile base (`LCOND=8 kzeroside2.py … 1000 15`).
5. Per-prime first-order responses and the chain's lines (`kL8score.py`).

**Criteria (tolerance ±0.3, tighter than rounds 111/112's ±0.5, because the law has nothing fitted).**
- **B1 (primary):** the strongest first-order line of `p = 3` lies within ±0.3 of 2.094, **and** that of `p = 5` within ±0.3 of 3.770.
- **B2 (primary):** the `χ₋₈` chain's strongest line lies within ±0.3 of 2.094. This assumes the empirical rule that the smallest prime not dividing `q` dominates. That rule held for ζ, `χ₋₃` and `χ₋₄`, but it is not derived.
- **The law passes if B1 and B2 both hold, and fails otherwise.**
- **B3 (secondary, reported):** per-prime hits for `p = 7, 11, 13`. Expected risk: in round 112 part B, `χ₋₄`'s per-prime `p = 7` gave 2.70 (law 10.77) and `p = 11` gave 5.76 (law 17.14). The far primes (`ρ* > 3`) have already failed at first order once, so misses here are anticipated and do not by themselves fail the law.
- **B4 (secondary):**
  - the kernel's `λ = mean(r_e)/0.8613` lies within 10% of `1/8 = 0.125`;
  - the round-111 narrow (measured-`K̃`) method's prediction is committed as an amendment after the kernel dumps and before the chain or any response, as a competitor.
- **Unscored:** the distance of each of the chain's top-4 lines to the nearest law value (`n = 3, 5, …, 15`).

**Chance level.** A uniformly placed strongest peak in [1.5, 40] lands within ±0.3 of a given value with probability ≈ 1.6%. If it is uniform on [1.5, 12] instead, the probability is ≈ 5.7%. Known risk: earlier `L` per-prime responses carried a secondary low-frequency line near 1.6–2.0. That line lies inside B1's `p = 3` window (1.79–2.39); if it is what `p = 3`'s response returns, the hit is weak evidence. `p = 5` (3.47–4.07) is clear of it.

## Amendment 1: kernel stage (committed after the `χ₋₈` zeros and kernel dumps, before the chain, the base chain or any per-prime response)

**Zeros.** 979 up to 1000, starting 3.5762, 7.4345, 9.5032, 12.3405. Max `|N − smooth|` is 0.72 (no missed zeros), the count offset is 0.0001, and `|Im Z|/|Z| ≤ 3.9·10⁻¹⁸`.

**B4 (a), `λ`: fails.** `r_e = 0.0941 ± 0.0100`, with 37 windows excluded (no crossing found), which gives `λ = 0.1092 = 1/9.16`. That is 12.6% below `1/8`, outside the registered 10%. The law assumes `λ = 1/q` exactly, so this is a strike against the law's `/q` step at the kernel level. It is recorded before any tone is seen. The law's predictions are **not** changed. For reference only, rescaling by the measured `λ` instead of `1/q` would multiply every predicted `ω` by `8λ = 0.874` (2.094 → 1.83, 3.770 → 3.29); this rescaled set is not scored.

**B4 (b), narrow-method competitor: uninformative.**
- Chirp variance captured 0.97, but the `β′` segments are −6.21, −0.16, −0.34, which is unstable.
- Only `p = 3` is read in range: `ω = 0.31`, range −3.67 to 2.39.
- This is the same failure mode as round 112's A1. It makes no usable prediction and is not scored.

The registered law predictions and criteria B1–B3 stand unchanged.
