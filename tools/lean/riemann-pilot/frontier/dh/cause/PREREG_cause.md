# Pre-registration: the cause of the Davenport–Heilbronn off-line zeros

**Committed before this programme computes any zero of the Davenport–Heilbronn function above height 200.**
The four zeros with Re ρ > ½ below height 200 are known (located in the kernel by rounds 267 and 270), and the
census instrument was validated on [1, 200] only (`val_1_200.jsonl`: exactly those four, no flags). Every number
predicted below comes from the random-model scripts committed here (`model/model_rate.py`, `model/model_phases.py`, their
JSON outputs in `model/`) or from exact arithmetic. The scoring will report every prediction, pass or fail; no threshold,
range or definition will be changed after the census.

## The objects

f(s) = Σ u(n mod 5) n^(−s), u = (0, 1, κ, −κ, −1), κ = (√(10−2√5) − 2)/(√5 − 1); the pilot's `dh` is a(1)·f.
χ = χ₅ with χ(2) = i, ε = e^(2iθ) its root number, θ = arctan κ. f = c₁L(s, χ) + c₂L(s, χ̄) with
c₁ = (1 − iκ)/2, c₂ = (1 + iκ)/2 = εc₁. The two channels L(s, χ) and L(s, χ̄) share one gamma factor
(odd character, conductor 5). R(s) = L(s, χ)/L(s, χ̄). On the critical line, ϑ(t) = (t/2)log(5/π) + Im log Γ(¾ + it/2),
Z_f = Re(e^(iϑ)f), Z_χ = Re(e^(iϑ)e^(−iθ)L(·, χ)), Z_χ̄ = Re(e^(iϑ)e^(iθ)L(·, χ̄)); Z_f = (Z_χ + Z_χ̄)/(2 cos θ).
Mean spacing of f's zeros at height t: λ(t) = 2π/log(5t/2π).

## The claim under test

Exact facts, all four kernel-checked in two new pilot files compiled in scratch at this commit and landing with this
round (`DHChannels.lean`: `dh_eq_zero_iff_channel`, `chi5_channel_fe`, `chi5_phase_lock`; `DHInert.lean`: `cDH_chi5_eq_of_dvd`,
`cDH_chi5_decomp`):

- (E1) f(s) = 0 ⟺ L(s, χ) = −ε L(s, χ̄): the zeros of f are the solutions of R = −ε (away from common zeros).
- (E2) L(s, χ)L(1 − s, χ) = ε² L(s, χ̄)L(1 − s, χ̄): the gamma factor cancels from the channel ratio, and the
  reflection acts on R by pure reciprocation, R(1 − s) = ε²/R(s), with no archimedean weight.
- (E3) On the critical line ε̄·L(s, χ)·conj L(s, χ̄) is real: R(½ + it) ∈ εℝ (phase lock).
- (E4) For Re s > 1, R(s) = Π_{p ≡ ±2 (mod 5)} (1 + χ(p)p^(−s))/(1 − χ(p)p^(−s)): the split primes p ≡ ±1 (mod 5)
  are a common Euler factor of both channels and cancel. Equivalently the coefficients c(n) of −f′/f equal
  Λ(n)χ(n) at every n with a prime factor ≢ ±2 (mod 5).

Hypothesis: the off-line zeros are produced by the inert primes (p ≡ ±2 mod 5) alone, through R, at statistics
fixed by the inert random Euler product (Bohr–Jessen); the archimedean factor, common to both channels, plays no
part off the line. On the line, the phase lock reduces R = −ε to one real equation; f has one zero per antiphase
beat of its two channels, on the line when the beat is bounded by one zero of each channel, and off the line
(paired with its mirror at a neighbouring beat) when the beat is bounded by two zeros of the same channel.

## The census

`instrument/dh_census.py` (committed here with `README_instrument.md`, `validate.sh`, `val_extra.py` and its [1, 200]
validation) on (200, 10000], windows of nominal length 25 (ends shifted down by at most 0.5), three processes on
[200, 5825], [5825, 8200], [8200, 10000]; scored by `score_cause.py` (committed here, tested on [1, 200] only). Per window: N_f, N_χ, N_χ̄
at the window ends by continuous argument; the on-line zeros of Z_f, Z_χ, Z_χ̄; K = (ΔN_f − n_f)/2 zeros with
Re > ½, each located. A window is complete when its N's are within 0.05 of integers, ΔN_χ and ΔN_χ̄ equal the
counted channel zeros, and K is a non-negative integer whose zeros were all located. Incomplete windows are
excluded and listed; if more than 1% of the windows are incomplete the census is reported as failed.

## Predictions

**P1 — the phase signature (primary).** Ω = the zeros ρ = σ + iγ with σ ≥ 0.6 and 200 < γ ≤ 10000; K = |Ω|.
For a prime q, m₁(q) = (1/K) Σ_Ω exp(−iγ log q).
Random-model values of m₁ (inert primes; `model_phases.py`, Kac–Rice weighting, real parts; imaginary parts ≈ 0):

| σ, cutoff | q = 2 | 3 | 7 | 13 | 17 | 23 |
|---|---|---|---|---|---|---|
| 0.6, X = 300 | −0.40 | +0.33 | −0.16 | +0.11 | −0.08 | +0.09 |
| 0.6, X = 3000 | −0.34 | +0.22 | −0.05 | +0.08 | −0.06 | +0.08 |
| 0.6, X = ∞ | −0.29 | +0.20 | −0.08 | +0.04 | −0.02 | +0.05 |
| 0.7, X = ∞ | −0.76 | +0.70 | −0.46 | +0.30 | −0.27 | +0.23 |
| 0.8, X = ∞ | −0.91 | +0.88 | −0.78 | +0.55 | −0.48 | +0.37 |

(The mechanism: at a zero, χ(p)p^(−iγ) is pulled towards −i for the inert primes, so each inert Euler factor of R
becomes nearly a pure rotation; hence p^(−iγ) → −1 for p ≡ 2 and → +1 for p ≡ 3 mod 5.) In the model the split primes
enter neither R nor its derivative, so their phases at the zeros are uniform; on the actual zeros a Landau-type
modulation of size about (log q)/(√q log(5γ/2π)) ≈ 0.1, shared with the channels' own zero trains, may appear.
Predictions: (a) Re m₁(2) ≤ −0.30 and |Im m₁(2)| ≤ 0.10; (b) Re m₁(3) ≥ +0.20 and |Im m₁(3)| ≤ 0.10;
(c) Re m₁(7) ≤ −0.10; (d) the sign of Re m₁(q) is − for q ≡ 2 and + for q ≡ 3 (mod 5) for at least 4 of
q ∈ {13, 17, 23, 37, 43}; (e) for each split prime q ∈ {11, 19, 29, 31, 41, 59, 61, 71}: |m₁(q)| ≤ 0.20, and
|m₁(q) − m₁ᴬ(q)| ≤ 0.15 where m₁ᴬ(q) is the same mean over the on-line zeros of L(½ + it, χ) in (200, 10000].
P1 passes when (a), (b), (c), (e) all hold and (d) holds.

**P2 — the beat law (primary).** Merge the on-line zeros of Z_χ (A) and Z_χ̄ (B) in order. An antiphase beat is
an interval between consecutive merged zeros on which Z_χ·Z_χ̄ < 0 (the sign decided by evaluating at the midpoint);
it is mixed if its ends belong to different channels and same-type otherwise. Theorems (instrument checks): no
on-line zero of f lies outside an antiphase beat; a mixed beat contains an odd number of on-line zeros of f, a
same-type beat an even number. The predictions:
(a) at least 99.5% of the mixed beats contain exactly one on-line zero of f;
(b) at every window end, N_f equals the number of antiphase beats below it, within ±1, at at least 99% of the ends —
    one zero of f per beat, on the line or off it;
(c) consequently, over the complete windows, 2·(number of zeros with Re > ½) = S₀ − S₂ − 2E within ±2, where S₀ and S₂
    count the same-type beats with no and with two on-line zeros of f, and E the extra pairs in mixed beats;
(d) at least 95% of the zeros with Re > ½ have a same-type beat with no on-line zero of f within 2λ(γ) below their
    height and another within 2λ(γ) above it, and at least 95% of those beats have a zero with Re > ½ within 2λ of
    their midpoint.
The split S₀ : S₂ (a reversal of the channel ratio that falls short of −ε, sending a pair of zeros off the line,
against one that overshoots, giving two extra on-line zeros) is reported without a prediction.
On [1, 200]: 129 beats, 121 mixed with exactly one zero each, 8 same-type with none (S₀ = 8, S₂ = E = 0), flanking
the four off-line zeros in pairs, one below and one above each; N_f(200) = 129. P2 passes when (a)–(d) all hold.

**P3 — the rates (secondary).** Counts of zeros with Re ρ ≥ σ₀, by window, against the random model with the
inert primes up to an effective cutoff X(t), bracketed by X = √(5t/2π) (low) and X = t (high) (`model/model_rate.py`):

| σ₀ | (200, 2000] | (2000, 5000] | (5000, 10000] |
|---|---|---|---|
| 0.60 | 57.9 – 115.3 | 116.6 – 214.5 | 215.0 – 374.1 |
| 0.65 | 39.4 – 69.9 | 78.7 – 124.5 | 143.2 – 215.4 |
| 0.70 | 21.8 – 40.8 | 46.7 – 72.3 | 87.2 – 122.4 |
| 0.80 | 2.9 – 7.7 | 7.6 – 13.4 | 15.0 – 22.3 |

A cell passes when the count lies between the 2.5% Poisson quantile of its low value and the 97.5% Poisson quantile
of its high value. P3 passes when at least 10 of the 12 cells pass. (Below 200 the four known zeros give 4, 3, 2, 1
for σ₀ = 0.55, 0.6, 0.7, 0.8 against brackets 5.8–12.6, 3.5–8.6, 0.5–3.3, 0.0–0.6: the low end.)
The asymptotic (X = ∞) rates per unit height are 0.096, 0.050, 0.026, 0.0049 for σ₀ = 0.6, 0.65, 0.7, 0.8.

**P4 — the Weil-form control (primary).** On the certificate packet g = cos(ωu)·1_[−a,a], (a, ω) = (12/5, 169/2),
Q_dh(g) = −1.2094 (round 259). The Weil form of the channel L(s, χ₅), with the same archimedean part exactly and
prime coefficients Λ(n)Re χ₅(n): Q_χ(g) > 0. The difference Q_dh − Q_χ receives no contribution from any n ≤ 121
with a prime factor ≢ ±2 (mod 5) (`weil_channels.py`).

**P5 — exploratory (no thresholds).** The distribution of Re ρ; zeros with Re ρ > 1 (the model gives none to
expect at these heights); the anatomy of the four kernel-located zeros through partial inert Euler products; the
stationarity in height of the value distribution of log|R(0.7 + it)|.

## Reporting

Every item above is reported with its numbers; failures are stated as failures and their bearing on the
hypothesis discussed. The census output, the scoring script and its log are committed with the result.
