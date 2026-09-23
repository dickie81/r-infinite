# Lean pilot: Theorems 1bt and 1ca of `riemann-indistinguishability.md` (b2014d8)

The toolchain is Lean 4.35.0-rc2 (`lean-toolchain`) with Mathlib at the commit in `MATHLIB_REV`. Point `MATHLIB` at a built Mathlib checkout (`lake exe cache get` then `lake build`), or place it at `./mathlib4`.

Re-run with `./build.sh`, which takes about 2 minutes.

- `T1ca.lean` → `Osc.lean` → `Split.lean` import each other through oleans written to `build/`.
- `Zeta.lean` imports `T1bt.lean`, `Split.lean` and `Exterior.lean`; `Roadmap.lean` imports `T1bt.lean` and `Exterior.lean`; `Limit.lean` imports `Roadmap.lean`; `HadamardApply.lean` imports `Hadamard.lean` and `Limit.lean`; `XiBounds.lean` imports `HadamardApply.lean`; `Curvature.lean` imports `XiBounds.lean`; `GroundState.lean` imports `Curvature.lean`; `Existence.lean` imports `GroundState.lean`; `Compactness.lean` imports `Existence.lean`; `GroundStateExists.lean` imports `Compactness.lean`; `Uniqueness.lean` imports `GroundStateExists.lean`.

Every file ends with `#print axioms`. All 152 checked theorems depend only on `propext`, `Classical.choice` and `Quot.sound`: there is no `sorry` and no added axiom. The build prints no warnings.

| File | Lines | Content |
|---|---|---|
| `T1bt.lean` | 543 | Theorem 1bt |
| `T1ca.lean` | 1500 | 1ca(ii) |
| `Osc.lean` | 926 | 1ca(iii) |
| `Split.lean` | 305 | 1ca(i), and (i)–(iii) assembled |
| `Exterior.lean` | 677 | 1ca(iv) |
| `Zeta.lean` | 142 | the 1ca zero family, linked to Mathlib's `riemannZeta` |
| `Roadmap.lean` | 341 | §11 item 1: the target stated prime-side, and its reduction to `RiemannHypothesis` |
| `Limit.lean` | 321 | 1bu(ii)'s convergence to `Ξ` from D, and the chain to `RiemannHypothesis` |
| `Hadamard.lean` | 776 | Hadamard's factorisation in genus zero, proved from Mathlib |
| `HadamardApply.lean` | 198 | Hadamard for even functions; applied to `ĝ` and `Ξ`; the chain to RH |
| `XiBounds.lean` | 403 | `XiGrowth` and `Ξ(0) ≠ 0`, proved; the chain to RH with no `Ξ` inputs |
| `Curvature.lean` | 506 | dodging D and the curvature sum rule; the chain to RH in its final form |
| `GroundState.lean` | 167 | ground states of Weil's form: the lower bound, the finite prime sum, the chain for ground states |
| `Existence.lean` | 485 | existence of the ground state, stage 1: the archimedean energy controls the Fourier tails |
| `Compactness.lean` | 234 | existence, stage 2: bounded-energy probes are precompact in `L²` |
| `GroundStateExists.lean` | 456 | existence, stage 3: **a ground state of Weil's form exists at every support** |
| `Uniqueness.lean` | 391 | the ground-state space; the uniqueness criterion |

## T1bt.lean: Theorem 1bt(i), "the pole-free form is indefinite for every a ≥ 0.2"

`pole_free_form_negative_zeta` is stated over the **nontrivial zeros of Mathlib's `riemannZeta`, counted with multiplicity** (`zetaZeroFamily`). For `a ≥ 1/5` it proves:

- `‖Q‖ < 2(a + sinh a)²`;
- `Re(Q − 2ĝ_a(i/2)²) < 0`, i.e. `Q₀(g_a) < 0`.

Round 2 discharged the strip hypothesis:

- `IsNontrivialZero s` means `ζ s = 0` and `s ≠ −2(n+1)`, the same predicate as Mathlib's `RiemannHypothesis`.
- `IsNontrivialZero.mem_strip` proves `0 < Re s < 1` from Mathlib:
  - `Re s < 1`: `ζ ≠ 0` on `Re s ≥ 1`.
  - `Re s > 0`: in the functional equation `ζ(s) = 2(2π)^{−(1−s)} Γ(1−s) cos(π(1−s)/2) ζ(1−s)`, every factor except the cosine is nonzero when `Re s ≤ 0`. The cosine vanishes only at `s = −2k`. For `k = 0` that is `ζ(0) = −1/2 ≠ 0`; for `k ≥ 1` it is a trivial zero.
- `zeroMult_pos`: every nontrivial zero has analytic order in `[1, ∞)`, so the family lists each zero at least once. Finiteness uses analyticity of ζ on the connected set `ℂ∖{1}`.

Three classical inputs remain. Each is now a statement about ζ itself.

| Hypothesis | Classical fact |
|---|---|
| `h_height` | every nontrivial zero has `|Im ρ| ≥ 14` |
| `h_hadamard` | `Σ_ρ 1/(ρ(1−ρ)) = 2 + γ_E − log 4π` |
| `h_explicit` | Weil's explicit formula for the witness: `Q(g_a) = Σ_ρ ĝ_a(t_ρ)²` |

The general form `pole_free_form_negative` is kept: it works for any family of zeros with the strip, height, Hadamard and explicit-formula properties. The round-1 lemmas are unchanged:

| Lemma | Content |
|---|---|
| `ghat_bound` | integration by parts, with the exact `V(a) = 4cosh(a/2) − 2` |
| `ghat_pole` | `ĝ_a(i/2) = a + sinh a` |
| `re_inv_zero_term_ge` | `Re 1/(ρ(1−ρ)) ≥ 1/(γ² + 5/4)` |
| `hadamard_const_lt` | `K < 0.0572` |
| `final_ineq` | `V(a)²eᵃK′ < 2(a + sinh a)²` for all `a ≥ 0.2`; this replaces the paper's interval evaluation on `[0.2, 1]` |

## T1ca.lean: Theorem 1ca(ii), uniqueness of the smooth wall, with no computed input

**`smooth_wall_unique`.** Assume:

- `γ₁ ∈ [14, 2πe]`;
- any horizon `T₀ > 0`;
- any finite hole set in `[0, L]`, with `L ≥ γ₁` (the domain is `T > L`).

Then all of the following hold:

1. `R(T) < 1` on all of `(γ₁, ∞)`.
2. `T·G` is strictly decreasing on `(L, ∞)`.
3. `F_k^s′` has derivative `F″`, and `T·F″ = 1 − T·G`.
4. `F_k^s′` is strictly quasiconvex on `(L, ∞)`: `F′(T₂) < max(F′(T₁), F′(T₃))` for `T₁ < T₂ < T₃`.
5. Any local minimum of `F_k^s′` is its strict global minimum, so the minimum is unique.
6. `F_k^s′` has at most two zeros.

**`hasDerivAt_Fs`.** The paper's own smooth functional, transcribed from 1ca(i),

`F_k^s(T) = T[ln(T/2π) − 1 − ln 2] − 2aT + 4Σ_h arccosh(T/h) + (7/2)arccosh(T/γ₁) − ∫₀^{γ₁} N₀(r)·4/(r√(1 − r²/T²)) dr`,

has derivative `Fp`, with `T₀ = 2πe^{2a}` (`I′ − 2a = ln(T/2T₀)`). `Fp` is exactly the paper's stationarity expression

`ln(T/2T₀) + 4Σ_h(T²−h²)^{−1/2} + (7/2)(T²−γ₁²)^{−1/2} + 4∫₀^{γ₁} N₀ r (T²−r²)^{−3/2}`.

So the chain starts from the paper's definition, not from a restatement.

Machinery added in round 2:

| Lemma | Content |
|---|---|
| `hasDerivAt_integral_param` | differentiation under the integral sign on `[0, G]` for an integrable weight and a kernel with a bounded T-derivative, via Mathlib's dominated-derivative lemma |
| `hasDerivAt_JA`, `hasDerivAt_JB`, `hasDerivAt_int_N0_wT` | the three parametric integrals, including the log-singular `N₀/r` weight of the `w_T` term |
| `T_mul_Fpp` | `T·F″ = 1 − T·G` |
| `TGp_eq` | `(T·G)′ = −4Σ_h T(T²+2h²)(T²−h²)^{−5/2} − T·fall + T·rise` |
| `TG_strictAntiOn` | `T·G` strictly decreasing wherever `R < 1` |
| `Fp_quasiconvex`, `Fp_localMin_unique`, `Fp_at_most_two_zeros` | the uniqueness consequences listed above |
| **`R_lt_one_low`** | `R < 1` on `(γ₁, 1.51γ₁]`, the part the paper says is *"computed and gated"* (see below) |

How `R_lt_one_low` works:

- Split the rise at `r₁ = 0.85γ₁`.
- Below `r₁`, use `|N₀| ≤ 1`.
- Above `r₁`, use `|N₀| ≤ |N₀(11.9)| ≤ 0.701`. This holds because `N₀` is nondecreasing and nonpositive on `[2π, 2πe]` (`N0_mono`, `N0_119_ge`).
- That gives `rise < K(r₁) + 0.701(K(γ₁) − K(r₁))`.
- For `T² ≤ 2.2801γ₁²`, `0.299K(r₁) ≤ 0.174K(γ₁)` by a squared rational comparison.
- The result is `R ≤ 0.983` in the worst case, at `T = 1.51γ₁`. There the true `R` is 0.678, and its maximum is 0.6866 at `1.39γ₁`, matching the paper's 0.69.

The round-1 lemmas (`integral_kern`, `R_lt_one` for `T ≥ 1.51γ₁`, `p_pos`, `p_crossing`, `log_deriv_identity`, `hasDerivAt_fall`, `hasDerivAt_rise`) are unchanged.

### Round 3: the limits, one minimum, and exactly two zeros

The hypotheses are bundled as `Endpoint`:

- `γ₁ ∈ [14, 2πe]` and `T₀ > 0`;
- every hole lies in `[0, L]`;
- `L = γ₁` or `L ∈ H`, so that `L = max(γ₁, h_max)` is the domain's actual left endpoint.

| Lemma | Content |
|---|---|
| `JA_lower` | cusp estimate `JA(T) ≥ −0.701(T²−γ₁²)^{−1/2} − 0.299(T²−r₁²)^{−1/2}`, from the same split at `r₁ = 0.85γ₁` |
| `Fp_lower` | `F′(T) ≥ ln(T/2T₀) + 4Σ_h(T²−h²)^{−1/2} + 0.696(T²−γ₁²)^{−1/2} − 1.196(γ₁²−r₁²)^{−1/2}` on the whole domain; the count constant's 7/2 beats the cusp's `4·0.701 = 2.804` (the true cusp coefficient `7/2 + 4N₀(γ₁)` is 1.797) |
| `Fp_tendsto_atTop` | `F′ → +∞` as `T → ∞`, through `ln(T/2T₀)` |
| `Fp_tendsto_left` | `F′ → +∞` as `T → L⁺`, through the hole's own term if a hole sits at `L`, or the constant's cusp if `L = γ₁` |
| `Fp_exists_min`, `Fp_unique_min` | **"F_k^s′ has one minimum"**: exactly one global minimizer on `(L, ∞)`, by compactness plus the round-2 uniqueness |
| `Fp_exactly_two_zeros` | **"where that minimum is negative F_k^s′ has exactly two zeros"**: if `F′(T_m) < 0` for some `T_m > L`, there are zeros `T₁ < T_m < T₂`, every zero in the domain is one of them, and `F′` is `+` on `(L, T₁)`, `−` on `(T₁, T₂)`, `+` on `(T₂, ∞)` |
| `Fs_max_then_min` | the same for the paper's `F_k^s` (with `T₀ = 2πe^{2a}` and positive holes): strictly increasing on `(L, T₁]`, strictly decreasing on `[T₁, T₂]`, strictly increasing on `[T₂, ∞)`, so a local maximum at `T₁` ("a maximum just above that cusp") and a local minimum at `T₂` (the smooth wall `T^s`) |

Still not formalized in 1ca(ii):

- **Quantitative parts of the sentence**: "just above that cusp", "far above the minimum in value", the wall's location in `(2T₀/e, 2T₀)`, and the closed form of the minimum's value.
- **Whether the minimum is negative at the paper's states.** The theorem takes it as its hypothesis, exactly as the paper's "where"; the paper computes it (−0.35 or less at the 45 states).
- **The numerical claims**: the 45-state minima and the 40-rung statistics.

## Round 4: 1ca(i), (iii) and (iv)

### Split.lean: 1ca(i), the split, with no inputs

The zeros are modelled as a family `γ : ι → ℝ` of ordinates, counted with multiplicity:

- locally finite: `{i | γ i < T}` is finite;
- every ordinate is `≥ γ₁`.

In this model:

- `Fk` is Theorem 1by's `F_k(T) = 4Σ_{γ<T} arccosh(T/γ) − 2aT + 4Σ_h arccosh(T/h)`;
- `Ncnt` is the count `N`;
- `Sz` is 1bs's `S = N − N₀ − 7/8`.

| Lemma | Content |
|---|---|
| `I_closed` | `∫₀^T N₀ w_T = T[ln(T/2π) − 1 − ln 2]`, and `N₀w_T` is integrable on `[0, T]`. Proved by `r = T sin θ` and Mathlib's `∫₀^{π/2} ln sin = −(π/2)ln 2`. The one-dimensional Jacobian formula is used because the integrand is singular at both ends. |
| `integral_wT` | `∫_b^T w_T = 4 arccosh(T/b)`, an improper integral at `T` |
| `integral_Ncnt_wT` | the Stieltjes step `∫_{γ₁}^T N w_T = 4Σ_{γ<T} arccosh(T/γ)` |
| **`split`** | **`F_k(T) = F_k^s(T) + Osc(T)` for every `T > γ₁`**, the paper's "(an identity)", with `F_k^s` exactly T1ca's `Fs` |
| `oscS_Sz` | `S` is measurable, locally integrable, and continuous off the countable set of `N`'s jumps (the standing hypotheses of (iii)) |
| **`wall_law_zeros`** | (i) + (ii) + (iii) assembled for the zero-sum functional itself; see below |

`wall_law_zeros` takes:

- `γ₁ ∈ [14, 2πe]` and any holes in `(0, L]`;
- von Mangoldt's `|S(t)| ≤ C ln t` and Littlewood's `|S₁(t)| ≤ C ln t` on `[γ₁, ∞)`;
- a window `J = [lo, hi]` with `lo > L`, `lo ≥ γ₁ + 2Δ` and `T·G(lo) < 1`;
- the smooth wall `T^s ∈ J` (`F_k^s′(T^s) = 0`);
- `T_u ∈ J` minimizing `F_k` on `J`.

It proves:

- `Osc_∞` exists;
- `|F_k(T_u) − (F_k^s(T^s) + Osc_∞)| ≤ K ln(hi)/√lo`;
- `(T_u − T^s)² ≤ 4K ln(hi)/√lo · hi/(1 − T·G(lo))`, with `K = 8C√Δ + 16C/√Δ + 12C`.

With `lo, hi ~ T` this is the paper's `|T_u − T^s| = O(T^{1/4}(ln T)^{1/2})`.

### Osc.lean: 1ca(iii)

| Lemma | Content |
|---|---|
| `osc_bound` | the paper's displayed bound `|Osc(T) − Osc_∞| ≤ 4 sup|S|·[arccosh(T/(T−Δ)) − ln(T/(T−Δ))] + 8 sup_{[γ₁,T]}|S₁|·D_T(T−Δ) + 8 sup_{[T,∞)}|S₁|/T`, for every `Δ ∈ (0, T − γ₁)`. The proof integrates by parts against `S₁` off the countable jump set of `S`. |
| `integral_DT`, `near_term_le`, `DT_le` | `∫_{T−Δ}^T D_T = arccosh(T/(T−Δ)) − ln(T/(T−Δ)) ≤ 2√(Δ/T)`, and `D_T(T−Δ) ≤ 2/√(ΔT)` for `T ≥ 2Δ` |
| **`osc_log`** | **`Osc(T) = Osc_∞ + O(ln T/√T)`** from the two named inputs: `Osc_∞` converges, and `|Osc(T) − Osc_∞| ≤ (8C√Δ + 16C/√Δ + 12C) ln T/√T` for `T ≥ max(γ₁ + 2Δ, 3)` |
| `wall_value` | the minimum's value: `|min F − (F^s(T^s) + Osc_∞)| ≤ ε`, and `F^s(T_u) − F^s(T^s) ≤ Osc(T^s) − Osc(T_u) ≤ 2ε` |
| `convex_quadratic_lower`, `wall_stability` | `F^s″ ≥ κ` gives `(T_u − T^s)² ≤ 4ε/κ` |
| `wall_stability_Fs` | the same for the paper's `F_k^s`, with `κ = (1 − T·G(lo))/hi`, from `T·F″ = 1 − T·G` and `T·G` decreasing (round 2) |
| `wall_law_Fs` | `osc_log` + `wall_stability_Fs` |

### Exterior.lean: 1ca(iv)

| Lemma | Content |
|---|---|
| **`exterior_identity`** | from Weil's explicit formula for an even `h` real on `ℝ`: **`Σ_ρ h(t_ρ) = (1/π)∫₀^∞ h ln(r/2π) + E_arch + 2h(i/2) − 2Σ_n Λ(n)n^{−1/2} f_χ(ln n)`**, with `t_ρ = (ρ − ½)/i` |
| `exterior_identity_probe` | the same for `h = ĝ²χ` with an even probe, where `E_pole = 2ĝ(i/2)²χ(i/2)` literally |
| `binet_remainder_le` | from Binet's formula, `|Re ψ(¼ + ir/2) − ln(r/2)| ≤ 3/(2r²)` for `r ≥ 8`. The pieces are `(1/2)ln(1 + 1/4r²)`, `Re 1/(2z)`, and the Binet integral `≤ 8/(π²r²) + 4e^{−πr/4}/(π²r)`. |
| `Earch_bound` | `|E_arch| ≤ (3/2)/(T² ln(T/2π)) · (1/π)∫_T^∞ h ln(r/2π) + (3/2π)∫_{(8,T]} h/r² + (1/π)∫_{(0,8]} |h(Re ψ − ln(r/2))|` for `h ≥ 0` and `T ≥ 8` |
| `norm_Phi_le`, `norm_chi_le` | `|Φ(z)| ≤ e^{(Im² − Re²)/2}/2` for `Re z ≤ 0`, with `Φ` extended to `ℂ`; `|χ(±i/2)| ≤ 2e^{−(T² − 1/4)/(2Δ²)}` for the mirrored four-term cut |
| `norm_ghat_half_le`, `norm_Epole_le` | `|ĝ(i/2)| ≤ √(2a)e^{a/2}` for `‖g‖₂ = 1`, via a pointwise AM–GM; `|E_pole| ≤ 8a eᵃ e^{−(T² − 1/4)/(2Δ²)}` |
| `psiRe_even`, `gh_eq_fchi` | `Re ψ(¼ − ir/2) = Re ψ(¼ + ir/2)`, from `Γ(z̄) = Γ(z)‾`; `g_h = f_χ` for even `h` |

The two named inputs are stated as `Prop`s:

- `WeilExplicit ρ h hR`: `h|ℝ = hR`, and the Guinand–Weil formula over a family of zeros counted with multiplicity.
- `BinetFormula`: `ψ(z) = ln z − 1/(2z) − 2∫₀^∞ t dt/((t² + z²)(e^{2πt} − 1))` for `Re z > 0`.

Mathlib has `Complex.digamma` but neither formula.

### What formalizing (iii)–(iv) found

All four are novel under Check 4 and minor. None changes a conclusion.

1. **(iii), the third term of the displayed bound.**
   - `8 sup_{[T,∞)}|S₁|/T` is a correct bound, but the named input `S₁ = O(ln t)` does not make that supremum finite, since `ln t` is unbounded.
   - The `O(ln T/√T)` conclusion needs the integrated tail instead: `|S₁(T)|/T + ∫_T^∞ |S₁|/r² ≤ C(2 ln T + 1)/T`. `osc_log` uses this and the conclusion holds.
   - The paper's "bound reads 1.66, 1.42, 1.21, 1.00, 0.77 nats" uses the list's supremum below height 6990 in place of `sup_{[T,∞)}|S₁|`.
2. **(iii), the consequences are argued globally but proved locally.**
   - *"F_k(T_u) ≥ F_k^s(T^s) + Osc(T_u)"* needs `T^s` to be `F_k^s`'s *global* minimizer. Round 3 proves only that it is the unique interior local minimum.
   - The comparison with the left end is easy: with no holes `F_k^s(γ₁⁺) = −2aγ₁`, against `F_k^s(T^s) ≈ −2T₀`. But it is not written.
   - Placing the global `T_u` inside the convex window also needs a global `O(1)` bound on `Osc` together with that gap.
   - The *"(1 + o(1))"* in `F_k^s″ ≥ (1 + o(1))/T` is `1 − T·G(T^s) ≈ 1 − ln(2T₀/T^s)`. The paper computes it as `≥ 0.2` at the rungs (*"T·F_k^s″ ≥ 0.2 at the 40 rungs (gated)"*).
   - The Lean statements are local: `T_u` minimizes `F_k` on `J`, and `1 − T·G(lo)` is carried explicitly.
3. **(iv), the zero side.** The identity is written *"2Σ_{γ>0} ĝ(γ)²χ(γ) = …"*, a sum over real ordinates. Unconditionally, Weil's formula sums `h(t_ρ)` with `t_ρ = (ρ − ½)/i`. The two agree only if every zero is on the line. The cell computations use listed zeros on the line and are unaffected. The Lean statement uses `t_ρ`.
4. **(iv), the `E_arch` bound.**
   - *"≤ (3/2)/(T² ln(T/2π)) times the smooth count's integral up to the cut's Gaussian tail"* holds pointwise only for `r ≥ T`.
   - Since `χ(T) = ½`, the shoulder just below `T` is not Gaussian-small. The factor there is `1 + O(Δ/T)`.
   - The Binet bound covers only `r ≥ 8`.
   - `Earch_bound` keeps `(0, 8]`, `(8, T]` and `(T, ∞)` as explicit terms.

These checked out as stated:

- the Binet constant `3/(2r²)`;
- `|ĝ(i/2)| ≤ √(2a)e^{a/2}`;
- `|χ(±i/2)| ≤ 2e^{−(T² − 1/4)/(2Δ²)}`;
- the `E_pole` bound;
- the identity's algebra from Weil's formula.

The remainder's leading term `−1/(24r²)`, which the paper quotes, agrees with Stirling's series. This was checked by hand, not in Lean.

### Still not formalized

- **The four named classical inputs**: von Mangoldt's and Littlewood's bounds, Weil's explicit formula, and Binet's formula.
- **Localizing the global unlocking height into the window**, and `T·G(lo) < 1` at the paper's states. Both are computed in the paper.
- **All computed, gated numerics.**

## Round 5: the zero family is `riemannZeta`'s (Zeta.lean)

1ca's zero family is no longer an abstract hypothesis. It is the positive-ordinate part of T1bt's `zetaZeroFamily`: the nontrivial zeros of Mathlib's `riemannZeta`, each repeated by its analytic order.

| Lemma | Content |
|---|---|
| `finite_zeros_below` | **finitely many nontrivial zeros have `0 < Im ρ < T`**, proved from Mathlib. Such zeros lie in a compact ball, by the strip. An accumulation point other than `1` would force `ζ ≡ 0` on the connected set `ℂ ∖ {1}` by the identity theorem, contradicting `ζ(2) ≠ 0`. An accumulation point at `1` is ruled out by `(s − 1)ζ(s) → 1`. |
| `zetaOrd_finite` | the same with multiplicity: `{p : γ_p < T}` is finite for the family `zetaOrd` of positive ordinates. This discharges the `hfin` hypothesis of `split` and `wall_law_zeros`. |
| `split_zeta` | **1ca(i) for ζ's own zeros**: `F_k = F_k^s + Osc` with `S = N − N₀ − 7/8`, where `N` is ζ's zero count |
| **`wall_law_zeta`** | **1ca(i)–(iii) for ζ's own zeros** |
| `exterior_identity_zeta` | **1ca(iv)** with the zero side summed over Mathlib's nontrivial zeros, with multiplicity |
| `zetaOrd_ge_of_height`, `fourteen_le_two_pi_e` | T1bt's `h_height` (`14 ≤ |Im ρ|`) gives `G = 14`, and `14 ≤ 2πe` |

`wall_law_zeta` still takes these named inputs:

- the first-zero height, `G ≤ γ` for every zero with `G ∈ [14, 2πe]` (`G = 14` from T1bt's `h_height`);
- von Mangoldt's and Littlewood's bounds, now on ζ's own `S`.

`exterior_identity_zeta` takes Weil's explicit formula (for the ζ family) as its named input.

## Round 6: §11 roadmap item 1, stated and reduced (Roadmap.lean)

### (i) The target, stated with no zero of ζ

| Definition | Content |
|---|---|
| `weilQ a g` | Theorem 1bn(i)'s true form `Q(g) = 2ĝ(i/2)² + (ψ(¼) − log π)‖g‖² + ∫₀^∞ [f(0) − f(u)] e^{u/2}/sinh u du − 2Σ Λ(n)n^{−1/2} f(log n)`, with `f` the autocorrelation and support `δ = 2a`. Only primes, `ψ(¼)` and `π` enter. |
| `Probe a g` | real, even, supported in `[−a, a]`, in `L²`, with the archimedean integral convergent |
| `IsGroundState a g` | a normalized probe minimizing `Q` among probes |
| `xi`, `Xi` | Riemann's `ξ(s) = (s(s−1)Λ₀(s) + 1)/2` from Mathlib's `completedRiemannZeta₀`, and `Ξ(t) = ξ(½ + it)` |
| `HypD a g T_D` | item 1(a), Hypothesis D of 1bu(ii): `ĝ` and `Ξ` have equal analytic orders at every point of `|z| < T_D` |
| `RealRooted a g` | item 1(b): every zero of `ĝ` is real |

`ghatC_I_div_two` checks that `ĝ(i/2)` in `Q` is the transform at `i/2`.

### (ii) The reductions, proved (no named inputs)

| Theorem | Content |
|---|---|
| `xi_eq_zero_of_nontrivial` | every nontrivial zero of `riemannZeta` is a zero of `ξ`; `ξ(2) ≠ 0` |
| **`zeros_on_line_below`** / `finite_advance` | **item 5's finite advance**: D at one support plus real-rootedness there puts every nontrivial zero with `|t_ρ| < T_D` on `Re s = ½`. Only one direction of D is used: every zero of `Ξ` below `T_D` is a zero of `ĝ`. The ground-state property plays no role; the reduction is about `ĝ` alone. |
| **`hurwitz_real`** | Hurwitz's theorem in the form needed, proved from the maximum modulus principle: locally uniform limits of entire functions with only real zeros have only real zeros (unless identically zero) |
| `ghatC_differentiable` | `ĝ` is entire, by differentiation under the integral |
| **`rh_of_realRooted_limit`** / **`rh_of_ground_states`** | **item 6's step**: real-rooted ground states `g_n` with nonzero `c_n` such that `c_n ĝ_n → Ξ` locally uniformly give Mathlib's `RiemannHypothesis` |

So the roadmap's claim that "(a) and (b) everywhere put Ξ's zeros on the line" is machine-checked in both forms.

- **Finite form:** exact D at a support. By the paper's own 1bu(ii) cell data ("not exactly", displacements up to 0.043), exact D is expected to fail.
- **Limit form:** real-rootedness with convergence to `Ξ`. 1bu(ii) derives the convergence from D and `ε(δ) → 0`; Round 7 formalizes that derivation.

What remains open is exactly the mathematics: proving `HypD` / convergence and `RealRooted` for `IsGroundState` from `weilQ`.

## Round 7: 1bu(ii)'s convergence to Ξ, and the chain to RH (Limit.lean)

Hadamard's factorisations are written in the variable `w = τ⁻²`. `HadamardW f w` states `f(0) ≠ 0`, `Σ‖w_i‖ < ∞` and `f(z) = f(0)Π(1 − z²w_i)`; a padding entry `w_i = 0` is the factor `1`. This is the only named input, taken once for each `ĝ_n` and once for `Ξ`.

| Theorem | Content |
|---|---|
| `norm_tprod_sub_tprod_le` | `‖Π(1 + x_i) − Π(1 + y_i)‖ ≤ exp(Σ‖x‖ + Σ‖y‖)·Σ‖x_i − y_i‖` for infinite products, via a finite-product induction and a limit |
| `hadamard_compare` | for two factorisations over one pairing, `‖f(z)/f(0) − g(z)/g(0)‖ ≤ ‖z‖²·exp(‖z‖²(Σ‖w‖ + Σ‖v‖))·Σ‖w_i − v_i‖` |
| **`tendstoLocallyUniformly_of_pairing`** | **1bu(ii)'s limit shape**: if `Σ‖w_n‖` is bounded and the pairing error `θ_n = Σ‖w_{n,i} − v_{n,i}‖ → 0`, then `ĝ_n/ĝ_n(0) → Ξ/Ξ(0)` locally uniformly |
| `rh_of_pairing_and_realRooted` | adding real-rootedness at every support gives Mathlib's `RiemannHypothesis` (via `hurwitz_real`) |
| `pairing_of_D` | **exact Hypothesis D is a special case**: the zeros below `T_D` matched by D, plus padding for the tails, give a pairing with `θ ≤ ε(δ) = Σ_{|τ|≥T_D}|τ|⁻² + Σ_{|γ|≥T_D}|γ|⁻²` |
| **`rh_of_D_and_realRooted`** | **the paper's statement end to end**. Suppose ground states at supports `δ_n` have real-rooted transforms, D holds exactly below `T_D(δ_n)`, `Σ_τ τ⁻²` is bounded, and `ε(δ_n) → 0`. Then Mathlib's `RiemannHypothesis` follows. |

What this adds:

- **The paper's route is checked.** Once Hadamard's factorisations are granted, the route from "(a) and (b) everywhere" to RH is machine-checked as the paper states it: D exact, `ε → 0`, real-rootedness, Hurwitz.
- **Exact D is more than the argument needs.** The pairing form requires only `θ_n → 0`: zeros matched within a summable displacement that vanishes in the limit. This is the "dodging tolerance" situation that 1bu(ii)'s cell data reports. The limit route therefore does not depend on exact D, which that data indicates fails.

Still open is the mathematics:

- real-rootedness of the minimizer of `weilQ`;
- `θ_n → 0` for it;
- the bound on `Σ_τ τ⁻²` for it.

The named inputs still to formalize are Hadamard's factorisation for `ĝ_n` (Cartwright class) and for `Ξ`.

## Round 8: Hadamard's factorisation, proved (Hadamard.lean, HadamardApply.lean)

Mathlib has no Hadamard factorisation. It is now proved here from Mathlib's complex analysis, using only circle averages.

**`hadamard_genus0`.** Let `F` be entire with `F(0) ≠ 0` and `‖F(w)‖ ≤ C·exp(A‖w‖^α)` for some `α < 1`. Then:

- `Σ 1/|u| < ∞` over the zeros, with multiplicity;
- `F(w) = F(0)·Π(1 − w/u)` for every `w`, as an unconditional `HasProd`.

| Step | Lemma | Mathlib inputs |
|---|---|---|
| A | `disc_estimate`: if `G` is zero-free on `|w| ≤ R` with `G(0) = 1`, then on `|w| ≤ r < R/2`, `‖G − 1‖ ≤ 12Mr/(R/2 − r)`, where `M` bounds the circle average of `log⁺|G|` | Poisson formula for harmonic functions and its kernel bounds; harmonic conjugate on a disc; maximum modulus; Borel–Carathéodory |
| B | `zero_count`, `summable_ord_div`: `n(R) ≤ log C + A(eR)^α − log‖F(0)‖`, then `Σ ord(u)/|u| < ∞` via dyadic shells | Jensen's inequality (`sum_divisor_le`) |
| C | `disc_factor`: `F = F(0)·Π_{|u|≤R}(1 − w/u)^{ord u}·G_R` on `|w| ≤ R`. `avg_posLog_G_le`: the circle average of `log⁺|G_R|` is `O(R^α)`, since each zero contributes at most `log 2` (`circleAverage_negLog_le`). | `extract_zeros_poles`; circle averages of `log‖· − u‖` |
| limit | `G_R(w) → 1` as `R → ∞`, and the partial products converge to the unconditional product | `multipliable_one_add_of_summable` |

**`hadamardW_even`.** An even entire `f` of order `< 2` satisfies `HadamardW f (u⁻¹)`, the product taken over `f`'s own zero pairs.

- Write `f(z) = F(z²)` with `F(w) = f(√w)`.
- `F` is entire: principal square root on the slit plane, the branch `i√(−w)` across the negative axis, and a removable singularity at `0`.
- `F` has order `< 1`, so `hadamard_genus0` applies to it.

The two applications:

- **`hadamardW_ghat`:** the transform of an even integrable probe with `ĝ(0) ≠ 0`. It is of exponential type, `‖ĝ(z)‖ ≤ (1 + ‖g‖₁)e^{a|z|}`. **No named input.**
- **`hadamardW_Xi`:** `Ξ`. Its evenness is proved from `Λ₀(1 − s) = Λ₀(s)` in Mathlib. Two named inputs remain:
  - `XiGrowth`: `‖Ξ(t)‖ ≤ C·exp(A‖t‖^{3/2})`, i.e. the order of `ξ` (true with order 1);
  - `Ξ(0) ≠ 0`: `Ξ(0) = 0.497…`, equivalently `ζ(½) ≠ 0`.

**`rh_of_D_and_realRooted_proved`.** This is roadmap item 1 ⇒ `RiemannHypothesis`, with Hadamard proved and the zero lists being the functions' own. Its hypotheses are:

- the ground states are even and integrable, with `ĝ_n(0) ≠ 0`;
- `ĝ_n` is real-rooted;
- Hypothesis D holds against `Ξ`'s zero list, with `Σ τ⁻²` bounded and `ε(δ_n) → 0`;
- the named inputs `XiGrowth` and `Ξ(0) ≠ 0`.

Both remaining named inputs are classical facts about `ζ`, not about the cascade. Round 9 proves both.

## Round 9: the two `Ξ` inputs, proved (XiBounds.lean)

Both are derived from Mathlib's Mellin representation `Λ₀(s) = ½·M[f_modif](s/2)`, where `f_modif` is the theta kernel `θ(x) − 1` for `x > 1` and its functional-equation image for `x < 1` (definitional in Mathlib).

| Step | Lemma | Content |
|---|---|---|
| kernel | `evenKernel_sub_one_le` | for `t ≥ 1`: `0 ≤ θ(t) − 1 ≤ 3e^{−πt}`, from `θ(t) − 1 = 2Σ_{n≥1} e^{−πn²t}` (`hasSum_int_evenKernel₀`) and `e^{−π} ≤ 1/10` |
| small `x` | `fmodif_lt_one` | for `0 < x < 1`: `‖f_modif(x)‖ ≤ 3x^{−1/2}e^{−π/x}`, via `evenKernel_functional_equation` |
| Mellin | `norm_completedZeta₀_le` | `‖Λ₀(s)‖ ≤ (3m₁!/π^{m₁} + 3m₂!/(π − 1))/2` whenever `m₁ ≥ 3/2 − Re(s/2)` and `m₂ ≥ Re(s/2) − 1`: both halves of the Mellin integral are bounded by Gamma integrals |
| `Ξ(0) ≠ 0` | `Xi_zero_ne_zero` | `Ξ(0) = (1 − ¼Λ₀(½))/2`; the Mellin bound at `m₁ = 2`, `m₂ = 0` gives `(6/π² + 3/(π − 1))/2 < 4`, so `‖Λ₀(½)‖ < 4`, ruling out the value `Λ₀(½) = 4` that `Ξ(0) = 0` requires |
| order | `xiGrowth` | `‖Ξ(t)‖ ≤ 3e^{144}·exp(18‖t‖^{3/2})`: at `s = ½ + it` take `m₁ = m₂ = N = ⌈‖t‖⌉ + 2`, so `‖Ξ(t)‖ ≤ 3N²·N! ≤ 3N^{N+2} ≤ 3exp(6N√N)`, using `log N ≤ 2√N` |

The constants are crude, since only the order `< 2` matters for `hadamardW_even`.

**`rh_of_D_and_realRooted_final`.** Roadmap item 1 ⇒ `RiemannHypothesis`, with no hypothesis about `Ξ` or `ζ`. What remains is exactly the cascade-side content:

- the ground states `g_n` are even and integrable, with `ĝ_n(0) ≠ 0`;
- `ĝ_n` is real-rooted;
- Hypothesis D holds against `Ξ`'s own zero list, with `Σ τ⁻²` bounded uniformly and `ε(δ_n) → 0`.

These are the open content of roadmap item 1. The classical analysis around them (the Hadamard products, the growth of `Ξ`, `Ξ(0) ≠ 0`, the limit argument, the link to Mathlib's `riemannZeta`) is now all machine-checked.

## Round 10: dodging D and the curvature sum rule (Curvature.lean)

Two changes to the hypotheses of the round-9 chain.

**Approximate D.** `DFamW` asked for an *exact* match between the zeros of `ĝ_n` and of `Ξ` below `T_D`. Theorem 1bu(ii)'s own census says: "D holds to the dodging tolerance, not exactly: the dodging zeros are displaced from the zeta zeros by at most 0.033, 0.024, 0.025, 0.004, 0.028, 0.036, 0.043". So the round-9 theorem assumed something the computed ground states do not satisfy. The replacement is *dodging D*:

- every zero of `Ξ` below `T_D(n)` is matched with its own zero of `ĝ_n`, with total displacement `Σ|τ⁻² − γ⁻²| ≤ η_n` and `η_n → 0`;
- `T_D(n) → ∞`;
- nothing is assumed about the other zeros of `ĝ_n`.

`pairing_of_matching` turns any such matching into a pairing whose error is the matched displacement plus the two unmatched sums. `pairing_of_D` is the special case of an exact match.

**The curvature sum rule.** `ghat_sum_rule`: for even integrable `g` with `∫g ≠ 0`, `Σ_τ τ⁻² = ∫u²g / (2∫g)`, summed over the zero pairs of `ĝ`. It is proved by comparing two second-order expansions at small real `x`:

| Lemma | Content |
|---|---|
| `HadamardW.expansion` | `‖f(z)/f(0) − (1 − z²Σw)‖ ≤ (‖z‖²Σ‖w‖)²`, from `‖Π(1 + x) − 1 − Σx‖ ≤ e^S − 1 − S` |
| `ghat_expansion` | `‖ĝ(x) − ∫g + (x²/2)∫u²g‖ ≤ |x|³a³∫|g|`; the odd moment vanishes by evenness, and the rest is Mathlib's `Complex.exp_bound` |
| `ghat_curvature` | real-rooted case: each term `τ⁻²` is a positive real, so `Σ‖τ⁻²‖ = ∫u²g / (2∫g)` |
| `xi_expansion` | `Ξ(z)/Ξ(0) = 1 − z²Σ_jγ_j⁻² + O(‖z‖⁴)`, so the target `Σ_jγ_j⁻²` is `Ξ`'s curvature, `−Ξ″(0)/(2Ξ(0)) = 0.023105` in the paper |

**`rh_of_dodging_and_curvature_final`.** Roadmap item 1 ⇒ `RiemannHypothesis`, with hypotheses:

- `g_n` even and integrable on `[−a_n, a_n]`, with `∫g_n ≠ 0`;
- `ĝ_n` real-rooted;
- dodging D with `η_n → 0` and `T_D(n) → ∞`;
- the curvature `κ_n = ∫u²g_n / (2∫g_n)` converges to `Re Σ_jγ_j⁻²`.

Compared with round 9:

- The uniform bound `Σ τ⁻² ≤ B` is gone, since a convergent `κ_n` is bounded.
- The tail condition `ε → 0` is gone. It follows from the curvature condition and dodging D, because `ĝ_n`'s unmatched zeros carry curvature `κ_n − Σ_matched ≥ 0`, and that tends to `0`.
- "No other zero of `ĝ_n` below `T_D`" is no longer assumed; it is a consequence in the limit.
- The target is `Re Σ_j γ_j⁻²`, the `z²` coefficient of `Ξ(z)/Ξ(0)`. It is known unconditionally, so no RH content is hidden in it. The proof shows `Re Σ ≤ Σ‖·‖` with equality forced by the hypotheses.

What remains open is unchanged in substance: real-rootedness and dodging D at every support are the wall (§11 items 5–6). The curvature condition is a statement about the second moment of the ground states, with no zero locations in it. *(Corrected in round 11: this section first said the ground states are "not yet defined in Lean". They are: `Roadmap.lean` defines `weilQ`, `Probe` and `IsGroundState` from Theorem 1bn(i). Round 11 connects them to this chain.)*

## Round 11: ground states of Weil's form (GroundState.lean)

`Roadmap.lean` (round 6) already states Theorem 1bn(i)'s form verbatim:

`Q(g) = 2ĝ(i/2)² + (ψ(¼) − log π)‖g‖² + ∫₀^∞ [f(0) − f(u)] e^{u/2}/sinh u du − 2Σ Λ(n)n^{−1/2} f(log n)`

It also defines the admissible class `Probe` (real, even, supported in `[−a, a]`, in `L²`, archimedean integral convergent) and `IsGroundState` (a normalised probe minimising `Q`). Round 11 proves what those definitions give:

| Theorem | Content |
|---|---|
| `abs_autocorr_le` | `|f(u)| ≤ f(0) = ‖g‖²`, from `|g(t)g(t+u)| ≤ (g(t)² + g(t+u)²)/2`, so the archimedean integrand is non-negative |
| `autocorr_eq_zero` | `f(u) = 0` for `|u| > 2a` |
| `prime_sum_eq` | the prime sum is the finite sum over `n ≤ e^{2a} = e^δ`, as Theorem 1bn(i) says |
| `weilQ_ge` | `Q(g) ≥ (ψ(¼) − log π − 2Σ_{n ≤ e^δ} Λ(n)/√n)‖g‖²` on probes |
| `groundState_energy_ge` | the ground energy `λ₁(δ)` is finite: `λ₁(δ) ≥ ψ(¼) − log π − 2Σ_{n ≤ e^δ} Λ(n)/√n` |
| `Probe.intervalIntegrable` | a probe is integrable on `[−a, a]` (from `L²` on a finite interval) |
| `rh_of_groundStates_dodging` | round 10's chain for ground states: evenness and integrability are now consequences of the definition |

The lower bound is weak: about `−6.35` at `δ = 1`, against the certified `λ₁ ≤ e^{−13.88}` (Theorem 1bn(ii)). Its role is only to show the minimisation problem is bounded below.

**Not proved in this round: existence.** *(Proved in rounds 12–14: `exists_groundState`.)* `IsGroundState` defines the minimiser; nothing in this round proves one exists. If none existed, `rh_of_groundStates_dodging` would be vacuous. Existence needs compactness. On the Fourier side the archimedean term weights `|ĝ(r)|²` by `Re ψ(¼ + ir/2) − ψ(¼)`, which grows like `log|r|`. Together with the support in `[−a, a]`, that makes bounded-energy sets precompact in `L²`, and the prime term is a bounded perturbation. Mathlib has the `L²` Fourier transform (`Analysis/Fourier/LpSpace.lean`) but no Kolmogorov–Riesz compactness criterion, so this is a foundations project of its own.

## Round 12: existence of the ground state, stage 1 (Existence.lean)

This round starts the proof that a ground state exists, i.e. that the minimum in `IsGroundState` is attained. There are three stages:

1. the energy controls the Fourier tails (this round);
2. compactness of bounded-energy probes;
3. lower semicontinuity and assembly.

Stage 1 expands a probe `g` (half-support `a > 0`) in the Fourier series of `[−2a, 2a]`, with period `4a` and `c_n = (4a)⁻¹∫e^{−2πint/4a}g(t)dt`.

| Theorem | Content |
|---|---|
| `normSq_sub_shift` | `‖g − g(· + s)‖² = 2(f(0) − f(s))` |
| `hasSum_cf_sq` | Parseval on `[−2a, 2a]`, from Mathlib's `hasSum_sq_fourierCoeffOn` |
| `cf_shift` | for `|s| < a`, a shift multiplies `c_n` by `e^{2πins/4a}` (the shifted probe stays inside the period) |
| `hasSum_shift` | `Σ_n |c_n|²(2 − 2cos(2πns/4a)) = (4a)⁻¹·2(f(0) − f(s))` |
| `archK_ge` | `e^{s/2}/sinh s ≥ 1/(2s)` on `(0, 1]` |
| `weight_ge` | `J(k) = ∫₀^b (2 − 2cos ks)/s ds ≥ 2 log(kb) − 6` for `kb ≥ 1`, by parts on `[1/k, b]` |
| `weighted_le_archE` | `a Σ_{n∈S} |c_n|² J_n ≤ E(g)` for every finite set `S`, where `E` is the archimedean integral, `0 < b ≤ 1` and `b < a` |
| `tail_le` | **`Σ_{|n|≥N} |c_n|² ≤ E(g) / (a(2 log(2πNb/4a) − 6))`**, uniformly over probes |

So probes of bounded archimedean energy have uniformly small high-frequency tails. The rate is logarithmic, as the `log|r|` growth of the archimedean weight predicts.

## Round 13: existence of the ground state, stage 2 (Compactness.lean)

**`exists_convergent_subseq`.** Probes at half-support `a > 0` with `‖g_j‖² ≤ B` and archimedean energy `E(g_j) ≤ C` have a subsequence converging in `L²` to some `G ∈ L²`. The proof:

- The coefficients satisfy `|c_n|² ≤ (4a)⁻¹‖g‖²` (Parseval), so the coefficient vectors lie in a product of closed discs. That product is compact (Tychonoff) and `ℤ → ℂ` is first countable, so a subsequence converges coordinatewise.
- Parseval for the difference of two probes (`hasSum_sub`) splits `‖g_i − g_j‖²/4a` into:
  - frequencies `|n| < N`: a finite sum, small once the coordinates converge;
  - frequencies `|n| ≥ N`: at most `2·tail_i + 2·tail_j`, uniformly small by `tail_le` once `N` is large (`exists_cut`).
- A `normSq`-Cauchy sequence converges in `L²` (`exists_limit_of_cauchy`, through Mathlib's complete `Lp ℝ 2`).

What remains is stage 3: the limit of a minimising sequence is a ground state.

## Round 14: existence of the ground state, stage 3 (GroundStateExists.lean)

**`exists_groundState`: for every `a > 0` there is a `g` with `IsGroundState a g`.** The minimum of `Q(g)/‖g‖²` over the even sector of `L²(−a, a)` is attained. `exists_groundStates` gives ground states for every term of a sequence of supports, so `rh_of_groundStates_dodging` is no longer vacuous.

The proof is the direct method:

| Step | Theorem | Content |
|---|---|---|
| non-empty | `box_probe`, `normSq_box` | `c·1_{[−a,a]}`, `c = (2a)^{−1/2}`, is a probe with `‖·‖² = 1`. Its archimedean integral converges because `f(0) − f(u) ≤ c²u` (the shifted box differs on two intervals of length `u`) and `u·e^{u/2}/sinh u ≤ 16e^{−u/4}`. |
| bounded below | `weilQ_ge` (round 11) | the infimum `λ` is finite |
| minimising sequence | Mathlib `exists_seq_tendsto_sInf` | `Q(h_j) → λ`, and the archimedean energies are uniformly bounded |
| compactness | `exists_convergent_subseq` (round 13) | a subsequence converges in `L²` to some `G` |
| a probe again | `symCut`, `normSq_sub_symCut_le` | `S f = 1_{|u|≤a}(f(u) + f(−u))/2` fixes probes and does not increase `‖·‖²`, so `S G` is even, supported in `[−a, a]` and still the `L²` limit |
| continuity | `tendsto_integral_mul` | `‖g‖²`, `ĝ(i/2)` and every `f(u)` are `L²` inner products, so they converge; hence the pole, constant and prime terms converge (the prime sum is finite) |
| semicontinuity | `fatou_real` | the archimedean integrands converge pointwise, so by Fatou the limit's integral converges and is at most the limit of the energies |
| conclusion | `exists_groundState` | `Q(S G) ≤ λ` and `‖S G‖² = 1`, so `S G` is a ground state |

**Scope.** This proves that *a* minimiser exists, not that it is unique up to sign *(round 15 reduces uniqueness to a criterion; it is not proved)*. The hypotheses of `rh_of_groundStates_dodging` (`∫g_n ≠ 0`, real-rootedness, dodging D, curvature convergence) concern whichever ground states are chosen. The paper's numerics suggest a simple lowest eigenvalue, but that is not proved here.

## Round 15: the ground-state space and the uniqueness criterion (Uniqueness.lean)

**Uniqueness is not proved, because it is not known to hold at every support.** Nothing in the paper claims `λ₁` is simple. Theorem 1br's ladder separates the rungs numerically, but 1br(i) certifies only upper bounds: "the upper end of flint's certified enclosure of that eigenvalue is a rigorous upper bound on λ_k". The standard Perron–Frobenius argument also fails here. Replacing `g` by `|g|` never increases the archimedean term, since `(|g(t)| − |g(t+u)|)² ≤ (g(t) − g(t+u))²`, nor the prime term, since `f_{|g|} ≥ f_g` and the term enters with a minus sign. But it can increase the pole term `2(∫g e^{−u/2})²`. This round proves the two things that are true.

**1. The ground states are the unit sphere of a linear space.**

| Theorem | Content |
|---|---|
| `weilQ_add_sub` | the parallelogram law `Q(g + h) + Q(g − h) = 2Q(g) + 2Q(h)` on probes, term by term (pole, constant, archimedean, primes) |
| `weilQ_smul` | `Q(cg) = c²Q(g)` |
| `probe_add_sub`, `probe_smul`, `probe_zero` | probes are closed under sums and multiples. Convergence of the archimedean integral for `g ± h` follows from `A_{g+h} + A_{g−h} = 2A_g + 2A_h` with all four non-negative. |
| `lam_mul_le` | `Q(g) ≥ λ₁‖g‖²` on probes, where `λ₁ = lam a` is the infimum |
| `groundSpace` | the submodule `{g : probe, Q(g) = λ₁‖g‖²}`. It is closed under addition because `R = Q − λ₁‖·‖² ≥ 0` satisfies the parallelogram law. |
| `isGroundState_iff` | `IsGroundState a g ↔ g ∈ groundSpace a ∧ ‖g‖² = 1` |

**2. The uniqueness criterion.** Let `w = 1_{[−a,a]}e^{−u/2}`, so `ĝ(i/2) = ⟨g, w⟩`.

| Theorem | Content |
|---|---|
| `exists_perp_of_not_unique` | if two ground states `g, h` are not equal up to sign a.e., then `ĥ(i/2)·g − ĝ(i/2)·h`, normalised, is a ground state orthogonal to `w`. When it vanishes a.e., the norms force `h = ±g`. |
| `groundState_unique` | **if no ground state is orthogonal to `w`, every two ground states agree up to sign a.e.** |
| `groundState_unique_of_gap` | the same under a gap `λ₁ < λ_⊥`, where `λ_⊥` is the infimum of `Q` over probes with `ĝ(i/2) = 0`. On those probes `Q` equals the pole-free `Q₀`. |

So uniqueness can fail only if the constrained minimum `λ_⊥` of the pole-free form, orthogonally to `w`, equals `λ₁` exactly. Equivalently, a ground state `v ⊥ w` would satisfy the weak eigen-equation of `Q₀` at `λ₁`, because the pole term's first variation `4ĝ(i/2)⟨h, w⟩` vanishes at `v` (an informal remark, not formalised). Deciding `λ₁ < λ_⊥` at a given support needs a certified lower bound on `λ_⊥`, which neither this pilot nor the paper has.

For the chain, `rh_of_groundStates_dodging` holds for any choice of ground states. Its hypotheses are unchanged by `g ↦ cg`, so uniqueness is not needed there.
