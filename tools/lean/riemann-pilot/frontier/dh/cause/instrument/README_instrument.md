# `dh_census.py` — a resumable zero census for the Davenport–Heilbronn function

This instrument counts and locates, on a height range `[t0, t1]`, the zeros of the
Davenport–Heilbronn function `f` and of its two Dirichlet channels `L(s, χ)`, `L(s, χ̄)`:
the on-line zeros of all three, the total counts from the argument principle, and every zero
of `f` with `Re s > 1/2`. It was built for a pre-registered census. **It has been run only on
`t ≤ 200`.** Its own ceiling guard stops a census from evaluating anything above the run's `t1`.

Files:

| file | role |
|---|---|
| `dh_census.py` | the instrument (census, `--selftest`, `--timing`, `--summary`, `--plan`) |
| `val_extra.py` | independent cross-checks and sabotage variants (all at `t ≤ 200`) |
| `validate.sh` | the full validation battery, about 50 s; writes `validation/` |
| `validation/` | outputs of the battery (reference census `val_1_200.jsonl`, its summary, variants) |
| `timing.json` | evaluator timing and accuracy at t = 200, 1000, 3000, 5000, 10000 |

Requirements: python ≥ 3.9 and python-flint 0.9 (`acb.zeta`, `acb.lgamma`, `acb.dirichlet_l`).
Nothing else is needed.

---

## 1. Objects and conventions

* `κ = (√(10 − 2√5) − 2)/(√5 − 1) = 0.2840790438…`, `θ = arctan κ = 0.276787179…`.
* `χ = χ₅`, with `χ(1..4) = (1, i, −i, −1)` and `χ(0) = 0` (flint `dirichlet_char(5, 2)`).
* `u = (0, 1, κ, −κ, −1)` by `n mod 5`, and `f(s) = Σ u(n mod 5) n^{−s}`.
* `f = c₁ L(s,χ) + c₂ L(s,χ̄)` with `c₁ = (1 − iκ)/2` and `c₂ = (1 + iκ)/2`.
  Check: for `n = 1, 2, 3, 4`, `c₁χ(n) + c₂χ̄(n)` is `1`, `i(c₁ − c₂) = κ`, `−i(c₁ − c₂) = −κ` and `−1`.

**Evaluation.** One evaluation computes the four Hurwitz values `H_a(s) = ζ(s, a/5)` for
`a = 1..4` with `acb.zeta`, at working precision `prec` (default 53 bits). Set `A = H₁ − H₄` and
`B = H₂ − H₃`. Then

    f(s) = 5^{−s}(A + κB),   L(s,χ) = 5^{−s}(A + iB),   L(s,χ̄) = 5^{−s}(A − iB).

All three functions come from the same four values. On the line `s = 1/2 + it`, with

    ϑ(t) = (t/2) log(5/π) + Im lgamma(3/4 + it/2)      (acb.lgamma, principal branch; continuous for Re > 0)

the instrument forms the rotated values

    R_f = e^{iϑ} f,   R_χ = e^{iϑ} e^{−iθ} L(s,χ),   R_χ̄ = e^{iϑ} e^{+iθ} L(s,χ̄)

and sets `Z_f = Re R_f`, `Z_χ = Re R_χ` and `Z_χ̄ = Re R_χ̄`. It computes `e^{iϑ} 5^{−s}` as
`5^{−1/2} e^{i(ϑ − t log 5)}`.

## 2. Derivations

**Root number.** `χ` is odd. Its completed function is
`Λ(s,χ) = (5/π)^{(s+1)/2} Γ((s+1)/2) L(s,χ)`, and it satisfies `Λ(s,χ) = ε Λ(1−s, χ̄)` with
`ε = τ(χ)/(i√5)`. Here
`τ(χ) = e(1/5) + i e(2/5) − i e(3/5) − e(4/5) = −2 sin(π/5) + 2i sin(2π/5)`. This gives
`ε = 0.850651 + 0.525731 i = e^{2iθ}`, because `tan 2θ = 2κ/(1 − κ²) = 0.618034`. Also
`ε(χ̄) = ε̄`.

**Functional equation of f.** Write `Λ_f = (5/π)^{(s+1)/2} Γ((s+1)/2) f`. Then
`Λ_f(s) = c₁εΛ(1−s,χ̄) + c₂ε̄Λ(1−s,χ)`. Since `c₂/c₁ = (1+iκ)/(1−iκ) = e^{2iθ} = ε`, this
equals `Λ_f(1−s)`. The coefficients `u` are real, so `Λ_f(s̄)` is the complex conjugate of
`Λ_f(s)`. On `Re s = 1/2` the two facts make `Λ_f` real. There
`Λ_f(1/2+it) = (5/π)^{3/4} |Γ(3/4+it/2)| e^{iϑ(t)} f(1/2+it)`, so `R_f` is real and `Z_f` has
the sign of `Λ_f`.

**Channels.** On the line, `Λ(s,χ) = ε · conj Λ(s,χ)`, so `Λ(s,χ)` has phase `θ mod π`. Hence
`e^{−iθ}Λ(s,χ)` is real, and so is `R_χ`. Likewise `e^{+iθ}Λ(s,χ̄)` and `R_χ̄` are real. Note
also that `Z_χ̄(t) = Z_χ(−t)`.

**Identity.** `c₁ = e^{−iθ}/(2cos θ)` and `c₂ = e^{iθ}/(2cos θ)`, so
`Z_f = (Z_χ + Z_χ̄)/(2cos θ)`. This is algebraically exact for the correct sign of θ. With
`θ → −θ` it would instead pair the channels into `A − κB`.

**Zero-free region.** For `Re s ≥ 2`,

    |f(s) − 1|, |L(s,χ) − 1| ≤ Σ_{n≥2, 5∤n} n^{−2} = (24/25)ζ(2) − 1 = 0.5791 < 1.

So there are no zeros there, `Re F(2+it) > 0` for all three functions, and the principal
argument on `Re s = 2` is the continuous one. Every zero of `f` with `Re s > 1/2` therefore has
`Re s < 2`. By reflection, `Λ_f` and `Λ(·,χ)` have all their zeros in `−1 < Re s < 2`.

**Counting `N_f`.** `Λ_f` is entire: the poles of the Gamma factor at `s = −1, −3, …` are
cancelled by the trivial zeros. `f` is real and positive on `[1/2, 2]` (checked on a ball grid,
with minimum `f(1/2) = 0.825383`). By the functional equation `Λ_f > 0` on `[−1, 2]`.

Apply the argument principle on the rectangle `[−1, 2] × [0, T]`. The bottom edge contributes
nothing. The reflection `s ↦ 1 − s̄` maps the right half of the boundary, `2 → 2+iT → 1/2+iT`,
onto the left half, and `Λ_f(1 − s̄)` is the complex conjugate of `Λ_f(s)`. So the left half
contributes the same argument change as the right half. Along the right half, the Gamma factor
changes argument by exactly `ϑ(T)`. That gives

    N_f(T) = (ϑ(T) + arg_c f(1/2+iT))/π,

where `arg_c` is the principal argument at `2+iT`, continued along the horizontal segment.
`N_f(T)` counts every zero with `0 < Im < T`, including both members `ρ` and `1 − ρ̄` of each
off-line pair. It is an exact integer when `Z_f(T) ≠ 0`, because `Λ_f(1/2+iT)` is real. Hence,
in a window with `n_f` on-line roots,

    K = (ΔN_f − n_f)/2 = number of zeros with Re s > 1/2 in the window.

**Counting `N_χ`.** `Λ(σ,χ)` is not real on the real axis. Use the relation
`Λ(s,χ) = ε · conj Λ(1−s̄, χ)`. The same reflection argument applies to the path
`P = 1/2 → 2 → 2+iT → 1/2+iT`, and the left half is now included through the reflection. So
`N_χ(T) = Δ_P arg Λ(·,χ)/π`, which is

    N_χ(T) = (ϑ(T) + D + [Arg L(2+iT,χ) − Arg L(2,χ)] + Δ_hor)/π.

Here `D` is the continuous change of `arg L(σ,χ)` on `σ ∈ [1/2, 2]`; it equals `−0.12610390`
(computed once, 152 points, never at the pole `s = 1` of the individual Hurwitz values).
`Δ_hor` is the change along the horizontal segment. For `χ̄`, `D` and `Arg L(2)` change sign.
`N_χ(T)` is integral because the phases at both ends of `P` are `θ mod π`.

**Parity checks**, run at every count:
* `N_f(T)` is odd iff `Z_f(T) < 0`.
* `N_χ(T)` is odd iff `Z_χ(T) < 0` xor `e^{−iθ}L(1/2,χ) < 0`, and likewise for `χ̄`. Here
  `e^{−iθ}L(1/2,χ) = 0.793968 > 0`, with imaginary part `8e−18`.

## 3. Method, per checkpoint window

The nominal ends are `t0, t0+dt, …, t1`. A remainder shorter than `dt/2` joins the last window,
and `dt ≥ 2`.

1. **Sampling.** The spec step is `h(t) = 2π/(16 log(5t/2π))`, capped at `0.1` where that
   formula exceeds 0.1, which is `t < 64` (it fails below `t ≈ 1.3`). The grid of a nominal
   window `[a, b]` is `b − j·h_b`, where `h_b = 0.5/⌈0.5/h(b)⌉ ≤ h(b) ≤ h(t)`, plus the point
   `a`. That is 16.7 to 17.4 samples per mean spacing.

   Each sample yields the three `Z` values. If any of their balls contains 0, the point is
   re-evaluated at `2·prec` (106 bits).

2. **Window ends.** The shift is **downward only**, by at most 0.5: the candidates are
   `b − j·h_b` for `j = 0..J`, tiling `[b − 0.5, b]`. They are ranked by
   `min_k |Z_k|/rms_k`, with the rms taken over the candidates. The end is the best-ranked
   candidate whose counts track cleanly, meaning integral and parity-consistent; this is the
   maximiser itself unless tracking fails there.

   Two reasons for downward-only shifts:
   * A run on `[t0, t1]` never counts above `t1`.
   * The choice depends only on the nominal value `b`. So two runs sharing a nominal end, such
     as `[1, 200]` and `[200, 10000]` or any parallel split, pick the identical shifted end and
     tile the line exactly. A census started at 200 begins at `T0 = 199.5` with
     `N = (129, 129, 129)`, exactly where the validation ended (checked).

3. **Counts at the ends** come from phase tracking along `σ: 2 → 1/2`. The step is adaptive,
   every increment of all three phases must be below 0.25 rad, and the step is halved and
   retried otherwise. If an `N` is not within 0.05 of an integer, tracking is redone with
   0.05-rad increments. A step below 1e−9 raises `TrackingError`, and the next-ranked end is
   tried.

4. **On-line roots.** Every sign change between consecutive samples is refined by Brent's
   method with `xtol = 2e−10`, so the final bracket is ≤ 2.1e−10 < 1e−9. A Brent point whose
   sign is uncertain even at 106 bits is a root to about 1e−26 and is returned.

   **Close pairs.** At an interior same-sign local minimum of `|Z|` with
   `|Z| < 0.3 × (larger neighbour)`, the instrument does three things in turn:
   * It probes the vertex of the parabola through the three samples. A crossing found there
     ends the search.
   * Otherwise it runs a golden-section minimisation of `sign·Z` on `[t_{i−1}, t_{i+1}]`.
   * It stops early when `min g > 8·a·w²`, where `a` is the sample-parabola curvature and `w`
     the bracket width. Under a parabola of curvature ≤ 8a, a crossing is then impossible. For
     a hidden pair, `g_min ≤ a·w²`, so the rule never stops it early.

   A negative value adds the two roots, each found by Brent on the tightest bracket.

   Why 0.3 suffices: for a pair hidden between two samples, the parabola model gives a ratio
   ≤ 1/4.

5. **Accounting.**
   * `ΔN_χ = #roots(Z_χ)` and `ΔN_χ̄ = #roots(Z_χ̄)`.
   * `ΔN_f − n_f` must be even and ≥ 0.

   If a check fails, the window is **localised by bisection**: split points are samples in the
   middle half with all three `|Z|` large, and counts are tracked there. Recursion continues
   until a sub-window holds ≤ 16 samples. That sub-window is re-sampled with local step `h/16`,
   then `h/256`, and detection is redone. Whatever stays inconsistent is flagged.

   Refined roots are cached, so re-detection runs Brent only for roots not already found.

6. **Off-line zeros.** If `K > 0`, the instrument locates exactly `K` zeros with
   `1/2 + 1e−7 < Re < 2` and height inside the window.

   * **Starts.** Same-sign local minima of `|Z_f|` (the wrong-sign extrema), deepest first. For
     each, Newton starts at `1/2 + d + i·t_ext` for `d ∈ (d_est, 0.01, 0.03, 0.08, 0.2, 0.35)`.
     Here `d_est = √(min/curvature)`, since `Z_f ∝ (t−γ)² + β²` near a pair at
     `1/2 ± β + iγ`.
   * **Newton.** Stage 1 runs at `prec`, with a central-difference derivative (`h = 1e−5`), steps
     capped at 0.2, and stops at `|step| < 1e−8` or when `f`'s ball contains 0. It then polishes
     at `2·prec` on **acb points** with a central difference (`h = 2^{−40}`). The acb points are
     needed because a double cannot hold a zero at `t ≈ 10⁴` closely enough for
     `|f| < 1e−12`. A result with `Re < 1/2` is mirrored to `1 − ρ̄`.
   * **Acceptance:** `|f(ρ)| < 1e−12` at `2·prec`, `Re ρ > 1/2 + 1e−7`, height in the window,
     and distance > 1e−6 from the others.
   * **Fallback.** Bisection with intermediate counts narrows the search to the sub-windows
     (length ≤ 1) where zeros are missing. Each such sub-window is re-sampled at `h/16`, which
     reveals any hidden on-line pair and lowers its `K`. Then Newton runs from the local minima
     of `|f|` on the grids `σ ∈ [0.505, 1.3]` and `σ ∈ [1.3, 1.99]` (step 0.01) × `t` (step
     0.05), smallest first.

   Missing zeros raise the flag `offline_missing` and surplus ones raise `offline_excess`.

7. **Output.** One JSON line per window, written with `flush` + `fsync`. A rerun validates the
   file's parameters and contiguity, truncates a torn trailing line, recomputes the carried
   samples, and resumes. The records are identical bitwise on all science fields to an
   uninterrupted run.

**Pre-registration guard.** The evaluator raises `HeightCeiling` for any height above the run's
`t1`. Newton iterates that stray there are abandoned. Window ends, splits and grids never
exceed the window's end, which is ≤ `t1`.

### Record format (one line per window)

Required fields:
* `T0`, `T1`: the shifted ends, shared with the neighbouring windows.
* `Nf0`, `Nf1`, `Nchi0`, `Nchi1`, `Nchib0`, `Nchib1`: each is `[raw float, rounded int]`.
* `roots_f`, `roots_chi`, `roots_chibar`: on-line roots in `(T0, T1)`.
* `offline`: `[[σ, t, |f|], …]`, mirrors not stored.
* `K`: `−1` if the counts are inconsistent.
* `flags`, `seconds`.

Extra fields:
* `format`, `k`, `params` (`t0`, `t1`, `dt`, `prec`, `theta_sign`), `T0_nom`, `T1_nom`.
* `offline_hp`: σ and t as 25-digit strings.
* `n_samples`, `evals` (per precision).
* `selftest`: window maxima of the two self-test ratios.
* `diag`: Brent, golden and close-pair counts, repairs, splits, re-sampled points, grid points,
  Newton starts, and the minimum tracking step.
* `startup`, in the first record written by each process: self-test report, real-axis data,
  κ, θ.

Possible flags:
* `count_f`, `count_chi`, `count_chibar`
* `offline_missing`, `offline_excess`
* `selftest_im`, `selftest_id`
* `end_counts_unclean`
* `uncertain_sample`
* `near_double_root_*`, `double_root_suspect_*`

## 4. Self-tests

* **Start-up (`--selftest`, and before every census).** The instrument evaluates
  `t = 7.3, 51.1, 133.7` with each sign of θ.
  * `θ_sign = +1` passes. `max |Im R|/(1e−8(1+|R|)) = 2.8e−7` and
    `max |Z_f − (Z_χ+Z_χ̄)/(2cos θ)|/(1e−10(1+|Z_f|)) = 1.4e−6`.
  * `θ_sign = −1` fails, with ratios `4.4e7` and `1.2e9`.

  So the stated convention is right: `ε(χ) = e^{+2iθ}` for `χ(2) = i`. Two more start-up checks:
  * `L(s,χ)` from the Hurwitz values agrees with flint's independent `acb.dirichlet_l` to a
    relative `8.1e−14`.
  * The real-axis data come out as listed in §2.
* **Every critical-line evaluation** updates the two ratios above. A window flags if either
  reaches 1. Maxima over the whole `[1, 200]` census: `7.2e−6` and `3.2e−6`.
* **Every count** must be integral to 0.05 and parity-consistent.
* **At large heights** (accuracy only, via `--timing`; no counting), at `t = 10⁴`:
  * ball radius ≤ `2.0e−10`;
  * `|Z(53 bits) − Z(106 bits)| ≤ 2.3e−12`;
  * `Im` ratio ≤ `9.9e−4`, identity ratio ≤ `1.7e−6`.

## 5. Validation (all at t ≤ 200; `bash validate.sh` reproduces it)

**Reference census.**
`python3 dh_census.py --t0 1 --t1 200 --out val_1_200.jsonl` runs 8 windows over
`[1.0, 199.5]` in 3.1 s, with 4230 evaluations at 53 bits and 168 at 106 bits.

* `N_f = N_χ = N_χ̄ = 129` at `T = 199.5`.
* On-line roots: 121 for f, 129 for χ, 129 for χ̄.
* The accounting is exact in every window and in total (`129 = 121 + 2·4`). There are no flags
  and no continuity problems.
* The first roots are:
  * f: 5.094160, 8.939914, 12.133545, 14.404003, …
  * χ: 6.183578, 8.457229, …
  * χ̄: 4.132904, 9.442931, …

The four zeros with `Re > 1/2` (one each in windows 4, 5, 7 and 8; each found by the first
Newton start, `d_est`):

| σ | t | \|f\| (106 bits) | reference |
|---|---|---|---|
| 0.8085171824566373855533520 | 85.69934848537759217192927 | 1.6e−30 | 0.808517 + 85.699348i |
| 0.6508300806097370824037606 | 114.1633427307569809041644 | 2.4e−30 | 0.650830 + 114.163343i |
| 0.5743560504508059907214821 | 166.4793059131681558764777 | 5.3e−30 | 0.574356 + 166.479306i |
| 0.7242576946268097802111861 | 176.7024612428558250544739 | 3.0e−30 | 0.724258 + 176.702461i |

All agree with the references to their 6 decimals; the largest difference is `4.9e−7`.

**Independent checks.**

* **Argument principle for f around a rectangle.** This uses no on-line root count. Around
  `[0.501, 2] × [1, 200]` it gives `4.0000000000000195` zeros, and around
  `[0.55, 2] × [1, 200]` it gives `4.0`.
* **The strip `(199.5, 200]`** (the last end's shift). `N_f(200) = 130`, there is one f root
  (199.876185) and `K = 0`. The channels are consistent: χ has 130 = 129 + 1 and χ̄ has 129.
  So **exactly four zeros with Re s > 1/2 have 0 < t ≤ 200.**
* **flint's `acb.dirichlet_l` at every root.** `max |L(1/2+iγ,χ)| = 2.1e−10`,
  `max |L(1/2+iγ,χ̄)| = 2.8e−10`, and `max |f(1/2+iγ)| = 2.4e−10`. This is consistent with the
  Brent tolerance.

**Sabotage and variants** (`val_extra.py run …`). Each run gives the same 121/129/129 roots
(to < 1e−10) and the same four off-line zeros, with no flags:

| variant | what it forces | path exercised |
|---|---|---|
| `fine` | 64 samples per spacing | nothing missed at 16/spacing |
| `coarse` | 2 per spacing | 4 golden sections |
| `harsh` | 0.75 per spacing, ends may shift by 2 | 14 golden sections, 11 close pairs found, 2 repairs |
| `harsh_nogolden` | as `harsh`, close-pair detection off | 11 count repairs; f's missing roots first look like off-line zeros and are resolved by localisation (16 splits) + re-sampling |
| `nodips` | Newton from dips disabled | the four zeros found by bisection (25 splits) + \|f\| grids (5832 points) |
| `dt 10`, `dt 50` | different windowing | same roots and zeros |
| resume | kill mid-run, append a torn line, rerun | torn line truncated; records bitwise identical on all science fields |

## 6. Timing and cost of a census of [200, 10000] (estimates; not run)

`python3 dh_census.py --timing --heights 200,1000,3000,5000,10000 --reps 40` times one evaluator
call (four Hurwitz values, ϑ and the three rotated values). The 4-core Xeon at 2.8 GHz had a
load average of about 1.4 from unrelated jobs.

| t | 200 | 1000 | 3000 | 5000 | 10000 |
|---|---|---|---|---|---|
| median ms | 0.72 | 1.98 | 4.92 | 8.15 | 14.99 |

The cost is close to linear in `t`. flint's Hurwitz ζ uses Euler–Maclaurin. A single
`acb.dirichlet_l` call costs about the same as the four Hurwitz values.

**Cost model** (`--plan`). The validation windows above `t = 64` used 33.5 evaluations per
zero per channel, cost-weighted:
* about 17.4 samples;
* 3 × about 5 Brent evaluations;
* tracking and Newton, which are negligible.

At `t = 10⁴` the grid still gives 16.8 samples per zero, so `E = 34` is used. Over
`[200, 10000]` each channel has about 12,574 zeros.

* **One core: about 60 min** (53 to 71 min for `E = 30..40`).
* **Three cores: about 20 min wall** (18 to 24 min). The balanced split is `[200, 5825]`,
  `[5825, 8200]`, `[8200, 10000]`. The split points 5825 and 8200 lie on the common nominal grid
  `200 + 25k`, so neighbouring processes choose identical shared ends:

```
python3 dh_census.py --t0 200  --t1 5825  --out census_0200_5825.jsonl  &
python3 dh_census.py --t0 5825 --t1 8200  --out census_5825_8200.jsonl  &
python3 dh_census.py --t0 8200 --t1 10000 --out census_8200_10000.jsonl &
wait; python3 dh_census.py --summary census_*.jsonl     # continuity, accounting, flags, zeros
```

Any interrupted process resumes when rerun with the same command line.

## 7. Limitations (what is and is not rigorous)

* **Values are rigorous; detection is not.** Every value is a certified ball, and every sign
  used for counting is certified (or escalated). But detecting on-line roots from samples is
  not a proof. A missed root is caught only by the count consistency, and the counts rely on
  adaptive phase tracking (0.25-rad increments) rather than certified winding numbers.
  Integrality, parity and the cross-channel accounting are the safeguards.
* **Positivity of f on [1/2, 2]** is checked on a 152-point ball grid, not on the continuum.
  It is needed for the bottom edge of the rectangle.
* **Zeros extremely close to the line.** An off-line zero with `Re ρ − 1/2 ≤ 1e−7` cannot be
  accepted; its window is flagged `offline_missing`. An on-line double zero, or a pair closer
  than about 1e−9, is flagged rather than resolved.
* **GRH for χ₅ is never used in a computation.** It only motivates reading a channel mismatch
  as a missed close pair. The mismatch is repaired or flagged either way.
* **The low `t` range.** Below `t ≈ 64` the sampling step is the 0.1 cap. That is denser than
  16 samples per spacing, so it costs time but nothing else.
