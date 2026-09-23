# Lean pilot: Theorems 1bt and 1ca of `riemann-indistinguishability.md` (b2014d8)

The toolchain is Lean 4.35.0-rc2 (`lean-toolchain`) with Mathlib at the commit in `MATHLIB_REV`. Point `MATHLIB` at a built Mathlib checkout (`lake exe cache get` then `lake build`), or place it at `./mathlib4`.

Re-run with `./build.sh`, which takes about 2 minutes.

- `T1ca.lean` → `Osc.lean` → `Split.lean` import each other through oleans written to `build/`.
- `Zeta.lean` imports `T1bt.lean`, `Split.lean` and `Exterior.lean`; `Roadmap.lean` imports `T1bt.lean` and `Exterior.lean`; `Limit.lean` imports `Roadmap.lean`; `HadamardApply.lean` imports `Hadamard.lean` and `Limit.lean`; `XiBounds.lean` imports `HadamardApply.lean`; `Curvature.lean` imports `XiBounds.lean`; `GroundState.lean` imports `Curvature.lean`; `Existence.lean` imports `GroundState.lean`; `Compactness.lean` imports `Existence.lean`; `GroundStateExists.lean` imports `Compactness.lean`; `Uniqueness.lean` imports `GroundStateExists.lean`; `Positivity.lean` imports `Uniqueness.lean`; `StrictPositivity.lean` imports `Positivity.lean`; `UniquenessQ.lean` imports `StrictPositivity.lean`; `SpectralGap.lean` imports `UniquenessQ.lean`; `FourierGap.lean` imports `SpectralGap.lean`; `ParabolaGap.lean` imports `FourierGap.lean`; `Polya.lean` imports `Roadmap.lean`; `Concave.lean` imports `Polya.lean`; `PrimeSide.lean` imports `Positivity.lean` and `Concave.lean`; `Saturation.lean` imports only Mathlib; `Unconditional.lean` imports `Concave.lean` and `Saturation.lean`.

Every file ends with `#print axioms`. All 246 checked theorems depend only on `propext`, `Classical.choice` and `Quot.sound`: there is no `sorry` and no added axiom. The build prints no warnings.

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
| `Positivity.lean` | 550 | the pole-free form `Q₀`: a unique, one-signed ground state |
| `StrictPositivity.lean` | 730 | the ground state of `Q₀` is strictly positive on `[−a, a]` |
| `UniquenessQ.lean` | 158 | the full form `Q`: strict gap `λ₀ < λ₁`, and the sharp uniqueness dichotomy |
| `SpectralGap.lean` | 658 | a certified lower bound `λ_⊥ ≥ λ₁ + 1/40` for `0 < a ≤ 1/40`; `Q`'s ground state is unique there |
| `FourierGap.lean` | 3154 | `λ_⊥ ≥ λ₁ + 1/40` for **every `0 < a ≤ 0.35`** (past the first prime); `Q`'s ground state is unique there |
| `ParabolaGap.lean` | 658 | the parabola trial; `λ_⊥ ≥ λ₁ + 1/50` and a unique ground state for **every `0 < a ≤ 0.36`** |
| `Polya.lean` | 356 | Pólya's theorem: every even probe concave on `(−a, a)` has a real-rooted transform |
| `Concave.lean` | 525 | Pólya's theorem stated for every even, concave `g ≥ 0` directly, with no representation hypothesis |
| `Saturation.lean` | 98 | saturation reduced to an envelope bound: a small value plus a steep slope forces a nearby zero |
| `Unconditional.lean` | 342 | saturation without RH: verified zeros, a counting bound, the decay of `ĝ` for monotone `g` |
| `PrimeSide.lean` | 108 | §11 item 1 restated with no zero of `ζ` in any hypothesis; `(a) + (b) ⇒ RiemannHypothesis` |

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

So uniqueness can fail only if the constrained minimum `λ_⊥` of the pole-free form, orthogonally to `w`, equals `λ₁` exactly. Equivalently, a ground state `v ⊥ w` would satisfy the weak eigen-equation of `Q₀` at `λ₁`, because the pole term's first variation `4ĝ(i/2)⟨h, w⟩` vanishes at `v` (an informal remark here; proved in round 18 as `euler_lagrange_perp`). Deciding `λ₁ < λ_⊥` at a given support needs a certified lower bound on `λ_⊥`, which neither this pilot nor the paper has.

For the chain, `rh_of_groundStates_dodging` holds for any choice of ground states. Its hypotheses are unchanged by `g ↦ cg`, so uniqueness is not needed there.

## Round 16: the pole-free form has a unique, one-signed ground state (Positivity.lean)

`Q₀ = Q − 2ĝ(i/2)² = (ψ(¼) − log π)‖g‖² + E(g) − 2S(g)` is Theorem 1bn(i)'s form without the pole term; its minimum is negative (Theorem 1bt). Round 15 showed that the full form `Q` is `Q₀` plus a positive rank-one term, and that `Q`'s ground state is unique unless `Q₀` has a `λ₁`-level direction orthogonal to `w`. This round proves what the Perron–Frobenius picture gives for `Q₀` itself.

| Theorem | Content |
|---|---|
| `exists_groundState0`, `isGroundState0_iff` | existence and the ground-state space, as in rounds 14–15 with the pole term removed |
| `weilQ0_abs_le` | **Beurling–Deny**: `|g|` is a probe and `Q₀(|g|) ≤ Q₀(g)`. Here `‖|g|‖ = ‖g‖`; `f_{|g|}(u) ≥ f_g(u)`, so the archimedean integrand does not increase; and the prime weights `Λ(n)/√n ≥ 0`, so the subtracted prime term does not decrease. |
| `one_sign_of_autocorr` | if `f_{|g|}(u) = f_g(u)` for a.e. `u > 0`, then `g ≥ 0` a.e. or `g ≤ 0` a.e. With `g = g⁺ − g⁻`, `f_{|g|}(u) − f_g(u) = 2(X(u) + X(−u))` where `X(u) = ∫g⁺(t)g⁻(t+u)dt ≥ 0`; so `X = 0` a.e., and by Tonelli `(∫g⁺)(∫g⁻) = ∫X = 0`. |
| `groundState0_one_sign` | **every ground state of `Q₀` has one sign.** At a ground state `Q₀(|g|) = Q₀(g)`, so the archimedean integrals agree, and since the integrands are ordered they agree a.e. on `(0, ∞)`. |
| `groundState0_unique` | **the ground state of `Q₀` is unique up to sign.** For two ground states, `(∫h)g − (∫g)h` lies in the ground-state space with integral `0`. If non-zero, its normalisation is a one-signed ground state with integral `0`, which is impossible. |
| `exists_unique_groundState0` | **`Q₀` has a ground state `φ ≥ 0` a.e., and every ground state is `±φ` a.e.** |

**Not proved in this round: strict positivity** (`φ > 0` a.e. on `[−a, a]`). *(Proved in round 17, `exists_positive_groundState0`, by truncated test functions; see below.)* The standard argument uses the Euler–Lagrange equation tested against a function supported on `{φ = 0}`. The natural test function, the indicator of that set, need not have finite archimedean energy, and the usual fix, the semigroup being positivity improving, is operator machinery the pilot does not have.

**What this says about `Q`.** Nothing new for the full form `Q`: its pole term is exactly what breaks the Beurling–Deny step, so round 15's criterion stands as the reduction of `Q`'s uniqueness.

## Round 17: the ground state of `Q₀` is strictly positive (StrictPositivity.lean)

**`exists_positive_groundState0`.** For every `a > 0` there is a ground state `φ` of `Q₀` with `φ ≥ 0` everywhere and `φ > 0` a.e. on `[−a, a]`, and every ground state is `±φ` a.e.

Round 16's note said the Euler–Lagrange route fails because the indicator of `{φ = 0}` need not have finite archimedean energy. The fix is to test against truncations of `φ`, which always do.

| Step | Theorem | Content |
|---|---|---|
| quadratic expansion | `weilQ0_add_smul` | `Q₀(φ + sψ) = Q₀(φ) + 2sB(φ, ψ) + s²Q₀(ψ)`. The cross archimedean integrand is integrable as `(A_{φ+ψ} − A_{φ−ψ})/4`. |
| Euler–Lagrange | `euler_lagrange0` | at a ground state, `B(φ, ψ) = λ₀⟨φ, ψ⟩` for every probe `ψ`, since `R(φ + sψ) = 2s·b + s²c ≥ 0` for all `s` forces `b = 0` |
| cross term | `xcorr_sub_eq` | `x(0) − x(u) = ½∫(φ(t) − φ(t+u))(ψ(t) − ψ(t+u))dt` |
| test functions | `trunc_probe`, `etaF_probe` | `min(φ, ε)` is a probe (a contraction: `A_{min(φ,ε)} ≤ A_φ`), so `η_ε = (1 − φ/ε)⁺·1_{[−a,a]} = c⁻¹·box − ε⁻¹·min(φ, ε)` is a probe |
| lower bound | `archX_eta_ge` | the Euler–Lagrange equation with `ψ = η_ε`, the prime cross term `≥ 0` and `⟨φ, η_ε⟩ ≤ aε/2` give `∫_{u>0} archX(φ, η_ε) ≥ −|λ₀ − C|(a/2)ε` |
| pairwise bound | `pair_le` | `(φ(t) − φ(t+u))(η(t) − η(t+u)) ≤ (ε/4)·1_{strips}(t)`. Inside `[−a, a]` the product is `≤ 0` because `η` decreases in `φ`; across the boundary it is `φ·η ≤ ε/4`, on two strips of width `u`. |
| exact gap | `integral_gapH` | the non-negative gap `H_ε = (ε/4)·1_{strips} − (pair)` has `K(u)∫H_ε = εuK(u)/2 − 2archX(u)`, so `∫_{u>0}K∫H_ε ≤ ε(M/2 + 2κ) → 0`, with `M = ∫uK < ∞` |
| limit | `eta_tendsto`, `gapH_tendsto` | `η_ε → 1_Z` pointwise, `Z = {φ = 0} ∩ [−a, a]`; `H_ε → 1_Z(t)φ(t+u) + φ(t)1_Z(t+u)` |
| Fatou | `gapInf_zero` | Fatou in `t` and then in `u` (lintegral form): `∫1_Z(t)φ(t+u)dt = ∫φ(t)1_Z(t+u)dt = 0` for a.e. `u > 0` |
| Tonelli | `tonelli_zero` | `(∫⁻ 1_Z)(∫⁻ φ) = 0`, splitting `u` at `0` and reflecting the negative half |
| conclusion | `groundState0_pos_of_nonneg`, `exists_positive_groundState0` | `∫φ > 0`, so `|Z| = 0`; the positive representative is `symCut` of the absolute value of a measurable version of the round-16 ground state |

So the pole-free form's ground state is simple (round 16) and strictly positive. This is the Perron–Frobenius picture, proved here without operator theory. The full form `Q` is not covered, as round 15 explains: its pole term breaks the `|g|` step. Round 18 narrows what can go wrong for `Q`.

## Round 18: uniqueness for the full form `Q` (UniquenessQ.lean)

**Uniqueness for `Q` is still not proved, and the structure of `Q` cannot prove it.** This round uses the `Q₀` results of rounds 16–17 to narrow round 15's criterion as far as it goes. What remains is a precise spectral coincidence that nothing in `Q` excludes.

| Theorem | Content |
|---|---|
| `quad_zero` | if `2sb + s²c ≥ 0` for all real `s`, then `b = 0` |
| `bil0_comm` | the bilinear form `B` of `Q₀` is symmetric |
| `lam0_le_lam` | `λ₀ ≤ λ₁`, since `Q₀ = Q − 2ĝ(i/2)² ≤ Q` |
| `poleR_pos` | `ĝ(i/2) = ⟨φ, w⟩ > 0` when `φ ≥ 0` and `φ > 0` a.e. on `[−a, a]` |
| `lam0_lt_lam` | **strict gap `λ₀ < λ₁`.** If `λ₀ = λ₁`, then a ground state `g` of `Q` has `λ₀ ≤ Q₀(g) = λ₁ − 2ĝ(i/2)²`, so `ĝ(i/2) = 0`, and `g` is a ground state of `Q₀`. By round 17, `g = ±φ₀`, and then `ĝ(i/2) = ±⟨φ₀, w⟩ ≠ 0`. |
| `euler_lagrange_perp` | **a ground state `v` of `Q` with `ĝ(i/2) = 0` solves `Q₀`'s weak eigen-equation at level `λ₁`**: `B(v, ψ) = λ₁⟨v, ψ⟩` for every probe `ψ`. Here `Q(v + sψ) − λ₁‖v + sψ‖² = 2s(B(v,ψ) − λ₁⟨v,ψ⟩) + s²(…) ≥ 0`, because the pole term of `v + sψ` is `2s²ĥ(i/2)²`. |
| `perp_groundState0` | **such a `v` is orthogonal to `φ₀`.** Testing the two Euler–Lagrange equations against each other gives `(λ₁ − λ₀)⟨v, φ₀⟩ = 0`. |
| `groundState_unique_or_excited` | **the dichotomy.** `λ₀ < λ₁`, and `Q₀` has a ground state `φ₀ > 0` a.e. on `[−a, a]` with `⟨φ₀, w⟩ > 0`. Either every two ground states of `Q` agree up to sign a.e., or there is a normalised probe `v` with `v ⊥ w`, `v ⊥ φ₀`, `Q₀(v) = λ₁` that solves `Q₀`'s eigen-equation at `λ₁`. |

**Why this is as far as structure goes.** The second branch says `Q₀` has an excited eigenvalue exactly equal to `λ₁`, with an eigenfunction orthogonal to both `w` and `φ₀`. By min–max, `Q = Q₀ + 2⟨·, w⟩²` is a rank-one positive perturbation of `Q₀`, and its lowest eigenvalue lies between `Q₀`'s first two eigenvalues: `λ₀ < λ₁ ≤ μ₁(Q₀)`. The second branch is the boundary case `λ₁ = μ₁(Q₀)`. For a general rank-one perturbation this happens exactly when `w` is orthogonal to the whole `μ₁`-eigenspace of `Q₀`, and nothing about `Q₀` or `w` forbids that. Evenness does not help, since every probe is even. The paper does not claim `λ₁` is simple (round 15). Deciding the second branch at a given support needs a certified lower bound on `Q₀`'s second eigenvalue on `w^⊥`, which neither the pilot nor the paper has. The min–max remark is an explanation and is not formalised.

For the chain, uniqueness is still not needed (round 15, last paragraph).

## Round 19: a certified lower bound orthogonally to `w`, at small support (SpectralGap.lean)

**`weilQ0_perp_ge`.** For `0 < a ≤ 1/40`, every normalised probe `g` with `ĝ(i/2) = ⟨g, w⟩ = 0` has `Q₀(g) = Q(g) ≥ Q(box) + 1/40 ≥ λ₁ + 1/40`. So `λ_⊥ ≥ λ₁ + 1/40`: round 18's second branch cannot occur, and **`groundState_unique_small`** gives a unique ground state of `Q`, up to sign, at every support `0 < a ≤ 1/40`.

The bound is analytic. Nothing is computed, and the only numbers used are `log 2 > 0.6931471803` (Mathlib) and elementary exponential bounds.

| Step | Theorem | Content |
|---|---|---|
| no primes | `primeS_eq_zero` | for `2a < log 2`, every `f(log n)` with `Λ(n) ≠ 0` vanishes |
| kernel | `kerK_ge`, `kerK_ge'`, `kerK_le` | `1/(u cosh(u/2)) ≤ K(u) ≤ e^{u/2}/u`, from `1 − u ≤ e^{−u}` and `u ≤ sinh u` |
| far field | `archIntegrand_eq_kerK`, `archE_split` | `A_g(u) = K(u)` for `u > 2a` at every normalised probe, so the far field cancels in `Q(g) − Q(box)` |
| edge mass | `edge`, `edge_reflect`, `autocorr_le_edge` | `m(u) = ∫_{t>a−u} g²` satisfies `m(u) + m(2a−u) = 1` (evenness) and `f(u) ≤ 1 − m(u)` (AM–GM on the overlap, which lies in `t ∈ [−a, a−u]`) |
| Fubini | `integral_autocorr`, `integral_autocorr_Ioc` | `∫f = (∫g)²`, via the shear `(t, u) ↦ (t, t+u)`; so `∫_{(0,2a]} f = (∫g)²/2` |
| near field | `integral_edge_ellK`, `integral_edge`, `nearField_ge` | with `A_g = mK + (1 − m − f)K`: reflection gives `∫₀^{2a} m/(u cosh a) ≥ log 2/cosh a` and `∫₀^{2a} m = a`, so `∫_{(0,2a]} A_g ≥ log 2/cosh a + (a − (∫g)²/2)/(2a cosh a)` |
| the box | `nearField_box_le`, `poleR_box_sq_le` | `∫_{(0,2a]} A_box ≤ e^a` and `2ĝ_box(i/2)² ≤ 4ae^a` |
| orthogonality | `integral_sq_le_of_perp` | `g ⊥ w` gives `∫g = ∫g(1 − e^{−t/2})`, so `(∫g)² ≤ a²(1+2a)²/4` |
| the gap | `weilQ_perp_ge_meas`, `weilQ0_perp_ge` | `Q(g) − Q(box) ≥ (log 2 + ½)/cosh a − a(1+2a)²/16 − e^a(1 + 4a) ≥ 1/40`. Non-measurable probes are reduced to a measurable `symCut` version, as in round 17. |
| uniqueness | `groundState_unique_small` | a ground state `v ⊥ w` would have `Q(v) ≥ Q(box) + 1/40 > Q(box) ≥ Q(v)` |

**Scope.** The margin at `a = 1/40` is `0.0357` with the bounds as formalised, or `0.063` with exact `cosh` and `exp`. The method stops near `a ≈ 0.037`, for two reasons: the near-field estimate replaces `K(|t − s|)` by its minimum `K(2a)`, which keeps only `½ + log 2 ≈ 1.19` of the kinetic energy against the box's `1`; and the pole penalty `2ĝ_box(i/2)² ≈ 4a` grows linearly. **The paper's certified cells are far beyond this.** Theorems 1bj, 1bl and 1br work at `δ = 2a ∈ [log 2, 1.3828125]`, i.e. `a ≈ 0.35–0.69`, where prime terms enter and the relevant gaps are about `10⁻²` (the paper records `λ₂` of the pole-free even section `≈ 0.012` at `δ = 1.0`). There the lower bounds come from Kato–Temple ratios and Birman–Schwinger counts on flint interval enclosures. Formalising those needs certified numerical linear algebra in Lean (interval arithmetic for `ψ(¼)`, the kernel integrals and the Gram entries, plus eigenvalue enclosures), which the pilot does not have. Uniqueness of `Q`'s ground state at those supports stays open in the pilot, and the paper does not claim it. *(Round 20 replaces this method and reaches `a = 0.35`; see below.)*

## Round 20: the certified gap for every `0 < a ≤ 0.35` (FourierGap.lean)

**`weilQ0_perp_ge_035`.** For every `0 < a ≤ 0.35`, every normalised probe `g` with `ĝ(i/2) = ⟨g, w⟩ = 0` has `Q₀(g) = Q(g) ≥ λ₁ + 1/40`. When `2a < log 2`, `weilQ0_perp_ge_fourier` gives `λ₁ + 1/10`. So `λ_⊥ ≥ λ₁ + 1/40` on the whole range, and **`groundState_unique_035`** gives a ground state of the full form `Q` that is unique up to sign at every support `0 < a ≤ 0.35`, i.e. `δ = 2a ≤ 0.7`. The range goes past the first prime, `δ = log 2`.

**Why round 19 stopped at `a ≈ 0.037`.** Numerically (a discretisation that reproduces the paper's `λ₁ ≈ 1.3×10⁻³` at `δ = log 2`), the true gap `λ_⊥ − λ₁` is large throughout: `1.59` at `a = 0.025`, falling to `0.54` at `a = 0.35`. Round 19's position-space bound captured only `1.51` of the true `2.93` for the near-field energy at `a = 0.35`. It replaced `K(|t − s|)` by its minimum on interior pairs. So the barrier was the method, not the truth.

**The method: an exact Fourier representation.** View `g` on a circle of length `8a`. For `0 ≤ u ≤ 2a` the circular and true autocorrelations agree, so `1 − f(u) = Σ_n p_n(1 − cos(πnu/4a))` exactly, with `Σ p_n = 1` (Parseval). The near-field energy is then a positive combination of mode energies `ψ_n`, which grow like `log n`. Truncating at `|n| ≤ 5` loses almost nothing.

| Step | Theorems | Content |
|---|---|---|
| A. representation | `cf_shift'`, `hasSum_shift'`, `hasSum_pm`, `hasSum_one_sub_autocorr` | round 12's shift identity, generalised to support `r` and any shift with `r + |s| < 2A`; the mode masses `p_n = 8a|c_n|²` |
| B. truncation | `sum_modeE_le`, `energy_ge_trunc` | `∫_{(0,2a]} A_g ≥ τ + Σ_{|n|≤5}(ψ_n − τ)p_n` whenever `ψ_n ≥ τ` for every `|n| ≥ 6`; the limit uses `Σ p_n = 1` |
| C. kernel | `kerK_eq`, `kerK_le'`, `sinh_le_taylor`, `cosh_le_taylor`, `kerK_ge_taylor`, `modeE_ge` | `K(u) = ½csch(u/2) + ½sech(u/2) ∈ [1/u + ½ − r(u), 1/u + ½]` from Mathlib's Taylor bound for `exp`; so `ψ_n ≥ Cin(πn/2) + a(1 − 2sin(πn/2)/(πn)) − err(a)` |
| D. `Cin` values | `Fk_deriv`, `cin_step`, `cin_quarter`, `piece1`–`piece11`, `pieceH6`–`pieceH60`, `cin_val1`–`cin_val6`, `cinH11`, `cinH21`, `cinH61` | `Cin(x) = ∫₀ˣ (1 − cos s)/s` via a Taylor piece on `[0, π/4]` and tangent-line pieces `1/s ≥ 2/c − s/c²` with exact antiderivatives; trig values at multiples of `π/4` by recursion; `π`, `√2` from Mathlib's bounds. Certified: `Cin(π/2) ≥ 0.5408`, …, `Cin(3π) ≥ 2.7801`, `Cin(61π/2) ≥ 5.098` |
| E. mode masses | `cs_supp`, `cf_even`, `pm_even`, `integral_sq_perp`, `integral_cos_sub_sq`, `pm_le`, `cval1`–`cval5` | for even `g`, `p_n = (∫ g cos(πnt/4a))²/(8a)`. Orthogonality to `w` gives `∫ g cosh(t/2) = 0`, so `(∫ g)² ≤ ∫(1 − cosh(t/2))² ≤ a⁵/30`. Cauchy–Schwarz against `cos − β_n` then gives `p_1 ≤ 0.0031`, `p_2 ≤ 0.0254`, `p_3 ≤ 0.0799`, `p_4 ≤ 0.1313`, `p_5 ≤ 0.1395` |
| F–G. no primes | `nearField_box_le'`, `pole_box_le`, `tail_ok`, `nearField_fourier`, `weilQ_perp_ge_fourier` | box: near field `≤ 1 + a/2`, pole `≤ 4a(1 + a²/24 + a⁴/1600)²`. For `2a < log 2`: `Q(g) ≥ Q(box) + 1/10` |
| H–J. the prime `n = 2` | `primeS_eq_two`, `autocorr_two_a`, `hasSum_autocorr`, `primeD_le`, `energy_prime_trunc`, `tailB_all`, `termB1`–`termB5`, `weilQ_perp_ge_sliver` | for `log 2 ≤ 2a ≤ 0.7` only `n = 2` enters: `−√2 log 2·f(log 2)`. Since `f(2a) = 0`, `f(log 2) = Σ p_n(cos(ω_n log 2) − cos(ω_n 2a))`, and each defect is `≤ min(ω_n(2a − log 2), 2) ≤ min(0.0155|n|, 2)`. It is absorbed mode by mode, with tail levels `n ∈ [6,10], [11,20], [21,60], [61,∞)` |

**Scope and honesty.**
* The constants are proved, not computed. Every numerical input is a Lean theorem from Mathlib's bounds on `π`, `√2` (via `Real.sqrt`), `log 2` and `e`; there are no floating-point certificates.
* The margins are thin but positive: `1/10` below `log 2`, `1/40` on the prime sliver. The modelled worst cases were `0.19` and `0.056`.
* **The paper's certified cells lie beyond this.** They start at `δ = log 2` and run to `δ = 1.3828125`, i.e. `a` up to `0.69`. `a = 0.35` is only the first sliver past `log 2`. Extending further needs more modes (the diagonal Cauchy–Schwarz bound degrades past about `N = 6`, so an eigenvalue bound for the low block would be needed) and more primes (`n = 3` at `δ = log 3`).
* Check 7: no semiclassical procedure is used. The kernel is the explicit formula's archimedean kernel, handled by Parseval on a circle and elementary calculus. There is no sphere Laplacian, loop integral or effective potential.

## Round 21: to the limit of the method, `a = 0.36`, and the frontier map (ParabolaGap.lean)

*(Corrected in round 23. The frontier map below was first computed in double precision, which cannot resolve eigenvalues below about `10⁻⁵`. Its `λ₁` row was wrong from `δ = 0.9` on, and its gap row and "near-degenerate" reading were wrong from `δ ≈ 1.2` on. The table and the text below now carry the values recomputed at 500–700 bits in the paper's Gram (`frontier/gap_hp.py`). The Lean results of this round are unaffected.)*

**`groundState_unique_036`.** For every `0 < a ≤ 0.36` (i.e. `δ = 2a ≤ 0.72`), `λ_⊥ ≥ λ₁ + 1/50` (`weilQ0_perp_ge_036`), so the ground state of the full form `Q` is unique up to sign.

**What changed.** The trial side. The box overshoots `λ₁` by about `0.19` near `a = 0.35`. The parabola `g = C(1 − t²/a²)` is within about `0.01` of `λ₁` numerically. Its autocorrelation is the explicit polynomial `f(u) = (2a − u)³(4a² + 6au + u²)/(32a⁵)` on `[0, 2a]` (`autocorr_par`, proved by exact polynomial integration). So `K ≤ 1/u + ½` gives the rational bound `∫_{(0,2a]} A_par ≤ 31/30 + 7a/12` (`nearField_par_le`), and cosh's Taylor bound gives `2ĝ_par(i/2)² ≤ (10/3)a(1 + a²/40 + a⁴/3584)²` (`pole_par_le`). On `0.35 ≤ a ≤ 0.36` the round-20 lower bound applies with a larger prime defect `≤ 0.06026|n|`, tail level `τ = 2.7`, and six certified `Cin` levels at `k = 6, 7, 11, 18, 25, 30`; the tightest has slack `0.0011`. It beats the parabola by `1/50`, against a modelled `0.039`.

### The frontier map

Recomputed at high precision in the paper's own Gram (`tools/research/weil_prime_gram.py`, even cosine basis, `K = 100–160`, 500–700 bits; `frontier/gap_hp.py`), with `⟨g, w⟩ = 0` imposed exactly for `λ_⊥`:

| `δ = 2a` | 0.70 | 0.80 | 0.90 | 1.00 | 1.10 | 1.20 | 1.38 | 2.00 |
|---|---|---|---|---|---|---|---|---|
| `λ₁` | `1.19×10⁻³` | `1.81×10⁻⁴` | `1.62×10⁻⁵` | `9.35×10⁻⁷` | `5.31×10⁻⁸` | `1.61×10⁻⁹` | `8.8×10⁻¹³` | `6.3×10⁻³⁰` |
| `λ_⊥` | `0.533` | `0.225` | `0.0661` | `0.0119` | `9.2×10⁻⁴` | `6.6×10⁻⁵` | `1.1×10⁻⁷` | `1.5×10⁻²³` |
| `λ_⊥/λ₁` | `450` | `1.2×10³` | `4.1×10³` | `1.3×10⁴` | `1.7×10⁴` | `4.1×10⁴` | `1.3×10⁵` | `2.3×10⁶` |

The `δ = 1.0` value `0.0119` reproduces the paper's "λ₂ of the pole-free even section ≈ 0.012". The absolute gap collapses fast, together with the eigenvalues themselves: every low eigenvalue tends to `0` as `δ` grows, because the ground state's transform dodges more and more zeta zeros (round 23). But `λ_⊥/λ₁` grows. **The ground state stays well separated, with no near-degeneracy at any tested support.** (The first version of this table, from a double-precision discretisation, showed a false floor of about `10⁻⁵–10⁻⁴` from `δ ≈ 1` on, and read it as near-degeneracy.) What the collapse does mean for certification is that a gap bound past `δ ≈ 1` must resolve `10⁻⁴` at `δ = 1.2`, `10⁻⁷` at `δ = 1.38` and `10⁻²³` at `δ = 2`, i.e. high-precision arithmetic throughout.

**Three barriers beyond `0.36`.**
1. **The prime tail.** Past `log 2`, the `n = 2` prime adds `−√2 log 2·(cos(ω_k log 2) − cos(ω_k 2a))` to every mode `k`. Bounded without evaluating the cosines, it reaches `≈ 1.96` in modes `k ≈ 10–40` and pulls the tail level `τ` down. The cos-free method stops at `a ≈ 0.363` (`frontier/reach.py`). Going on needs certified `cos(πk log 2/(4a))` over `a`-subintervals, i.e. interval trigonometry in Lean.
2. **The low block.** With exact cosines, the ceiling of the Fourier method needs `N ≈ 15–25` low modes (`frontier/ceil_lib.py`, `frontier/lp.py`): `2.75` at `N = 20` against `λ₁`'s `2.57` at `a = 0.4`; `2.78` against `2.73` at `a = 0.45`; `2.882` against `2.875` at `a = 0.5`. Per-mode Cauchy–Schwarz, even with the Parseval budget, plateaus near `2.4–2.5`. A certified top eigenvalue of a `16×16`–`25×25` block is required. The Gram part is `a`-independent in scaled variables, but the prime coefficients are not, so one certificate is needed per `a`-subinterval.
3. **The precision.** Near `a = 0.5` the whole budget is `0.007`, so every constant (`Cin` values, kernel remainders, the trial energy) must be certified to about `10⁻³`, and beyond `a ≈ 0.6` to the size of the absolute gap above (`10⁻⁴` down to `10⁻²³`). This is the regime of the paper's own Kato–Temple and Birman–Schwinger certificates, rebuilt in Lean.

So with elementary means the pilot's certified frontier is `a = 0.36`. The Fourier method's ceiling is about `a ≈ 0.45–0.5`, and it needs interval trigonometry plus matrix certificates. Beyond that the gap remains, in the ratio `λ_⊥/λ₁ ≥ 10⁴`, but its absolute size falls below `10⁻³` by `a ≈ 0.55` and far below after. Certifying it there is the paper's own high-precision regime, not a limit of the mathematics.

## Round 22: testing the chain's hypotheses on ground states (numerical, `frontier/hrr_test.py`, `frontier/hrr2.py`)

*(**Retracted in round 23.** The states tested here were not the ground states. The double-precision step-function discretisation misses the true ground state by up to 23 orders of magnitude in energy. The "`hκ` fails" conclusion is withdrawn. See round 23.)*

`rh_of_groundStates_dodging` derives RH from ground states `g_n` of `Q` at supports `a_n → ∞`, assuming `hRR` (every `ĝ_n` is real-rooted), `hD` (the zeros of `ĝ_n` below `T_D(n)` pair off with `Ξ`'s, total mismatch `η_n → 0`) and `hκ` (the curvature `κ_n = ∫u²g_n/(2∫g_n)` tends to `Re Σ_j γ_j⁻² = 0.023105`). This round tests all three numerically, before any further investment. Method:
* the even-sector ground state of the full `Q`, with every prime power, discretised piecewise-constant on `n` cells;
* `hRR`: all zeros of `ĝ` in `|z| < 60` by the argument principle, compared with the sign changes on the real axis;
* `hD`: the nearest zero of `ĝ` to each `γ_j < 55`, from the repo's 6700-zero list;
* `hκ`: the curvature from the ground state directly.

| `a` | `n` | all zeros in `|z|<60` real | zeros of `ĝ` in `(0,60)` | max `|τ − γ_j|`, `γ_j < 55` | `η` (11 zeros) | `κ` | `κ / 0.023105` |
|---|---|---|---|---|---|---|---|
| 0.5 | 400 | yes | 9 | 1.9 (too few zeros) | 3.5e-4 | 0.0150 | 0.65 |
| 0.7 | 560 | yes | 12 | 1.7 | 2.5e-4 | 0.0358 | 1.55 |
| 1.0 | 800 / 1600 | yes / yes | 18 | 0.029 / 0.059 | 1.4e-6 / 2.8e-6 | 0.0889 / 0.0883 | 3.8 |
| 1.5 | 1200 | yes | 27 | 0.012 | 9.7e-7 | 0.198 | 8.6 |
| 2.0 | 1600 / 3200 | yes / yes | 37 | 0.0059 / 0.0033 | 8.2e-7 / 2.5e-7 | 0.389 / 0.369 | 16 |
| 2.5 | 2000 | yes | 47 | 0.0015 | 2.0e-7 | 0.591 | 26 |
| 3.0 | 2400 | yes | 56 | 0.0014 | 3.9e-7 | 0.848 | 37 |

**Findings (as first written; the states were not the ground states, see round 23).**
1. `hRR` held on these states.
2. `hD` held on these states in the weak sense (every `γ_j` near some zero), but with extra zeros. The true ground states have none below `T_D` (round 23).
3. ~~`hκ` fails, decisively: `κ ≈ 0.088·a²`.~~ **Retracted.** The `a²` growth was a property of the wrong states: a high-energy, box-like state spread over `[−a, a]`. The true ground states have `κ = 0.0148 → 0.0221`, rising toward `0.023105` (round 23).

~~**What this means for the chain.** `rh_of_groundStates_dodging` cannot fire … refuted numerically at `hκ`.~~ **Retracted.** On the paper's ground states all three hypotheses are numerically consistent at every tested cell (round 23).

## Round 23: the test rerun on the paper's ground states, and two corrections (numerical, `frontier/rerun_paper.py`, `frontier/arbiter.py`, `frontier/verify_d3.py`, `frontier/gap_hp.py`)

**What went wrong in round 22.** Theorem 1bu(ii) states Hypothesis D as exact coincidence below `T_D`: "every zero of ĝ₁ with |τ| < T_D is a zero of ζ, every zero of ζ with |γ| < T_D is a zero of ĝ₁ … (the probe dodges every zero below T_D and has no other zero there)". The extra zeros belong to the excited states ("the ground state none"). The paper's curvature at the cells is "0.0148, 0.0177, 0.0203, 0.0210, 0.0216, 0.0221, 0.0225 rising toward Σ_γ γ⁻² = 0.0231". Round 22 agreed with this at `δ = 1` (`κ = 0.0150`) and disagreed from `δ = 1.38` on. The reason is precision. The true ground-state energies are `λ₁ = 9.4×10⁻⁷, 8.8×10⁻¹³, 6.3×10⁻³⁰, 2.1×10⁻⁴³, 4.3×10⁻⁹⁷` at `δ = 1, 1.38, 2, 2.3, 3`, far below what a double-precision dense eigensolver can resolve. Projected into the paper's cosine basis, round 22's state at `δ = 2` has true Rayleigh quotient `1.66×10⁻⁷`, against the ground state's `6.3×10⁻³⁰` (`frontier/arbiter.py`). It was a different state.

**The rerun.** The ground state is computed with the paper's own Gram (`tools/research/weil_prime_gram.py`: even cosine basis, every prime power, 600–1100 bits). `ĝ` is evaluated in the same precision. `hRR` is checked by the argument principle against the real-axis census; `hD` by the nearest zero to each `γ_j < 55`; `hκ` exactly from the coefficients.

| `δ` | `K` | `λ₁` | zeros in `|r| < 60`: all real? | zeros of `ĝ` in `(0, 55)` not at a zeta zero | max distance, dodged `γ_j` | `κ` (paper) |
|---|---|---|---|---|---|---|
| 1.0 | 120 | 9.4e-7 | yes (18/18) | above `T_D` only | (only 2 zeros dodged) | 0.01478 (0.0148) |
| 1.38 | 140 | 8.8e-13 | yes (22/22) | above `T_D` only (≈ 40) | 1e-5 for `γ ≤ 37.6` | 0.01770 (0.0177) |
| 2.0 | 160 | 6.3e-30 | yes (26/26) | **none** | 2.6e-8 | 0.02030 (0.0203) |
| 2.3 | 260 | 2.1e-43 | yes (26/26) | **none** | 6.0e-7 | 0.02105 (0.0210) |
| 3.0 | 400 | 4.3e-97 | yes: 13 of 13 roots of `M` in `|s| < 3600` are real positive (full precision) | **none** | 2.4e-6 | 0.02210 (0.0221) |

At `δ = 3` a first pass with coefficients rounded to double reported spurious non-real zeros. With the exact coefficients the count is 13 real of 13, and rounding alone produces 9 spurious roots (`frontier/verify_d3.py`). That is the same precision trap as round 22.

**Findings.** On the paper's ground states, all three hypotheses of `rh_of_groundStates_dodging` are numerically consistent at every cell tested.
* `hRR`: every zero in `|r| < 60` is real.
* `hD`: for `δ ≥ 2` every zero of `ĝ` below 55 is a zeta zero to `10⁻⁶–10⁻⁸`, with no other zeros.
* `hκ`: `κ` rises monotonically toward `0.023105` (0.0148 → 0.0221), matching the paper's values to 3 digits.

**What it does and does not mean.** This reproduces Theorem 1bu(ii)'s computed facts independently. It is not progress on RH. The ground state's transform vanishing at the zeta zeros is what the explicit formula's zero side `Σ_γ |ĝ(γ)|²` rewards: under RH that side is a sum of squares, which the minimiser drives to `≈ 0` by dodging every zero below `T_D`. §11's own words: "it is the direction RH ⇒ shadow, the shadow's description and not its cause". The open step is still roadmap item 1: derive (a) dodging and (b) real-rootedness from the prime side, with no zero entering. What the test does settle is that the chain's instance is not refuted: it has a numerically viable family. The chain also needs `δ → ∞`; the rate at which `κ → Σγ⁻²` (the paper's `ε(δ) ~ ln T_D/T_D`) is not proved.

**Correction to round 21.** Recomputed at high precision in the paper's Gram with `⟨g, w⟩ = 0` imposed (`frontier/gap_hp.py`), `λ_⊥ = 0.0119, 1.1×10⁻⁷, 1.5×10⁻²³` against `λ₁ = 9.4×10⁻⁷, 8.8×10⁻¹³, 6.3×10⁻³⁰` at `δ = 1, 1.38, 2`. The absolute gap collapses together with the eigenvalues. That is why a Lean certificate past `δ ≈ 1` needs high-precision arithmetic, as round 21 said. But `λ_⊥/λ₁` grows from `10⁴` to `10⁶`, so the ground state is numerically unique at every cell, and there is no near-degeneracy.


## Round 24: the chain with prime-side hypotheses only, and real-rootedness from concavity (PrimeSide.lean, Polya.lean, `frontier/polya_shape.py`)

**Step 1: the reduction, restated without zeros (`PrimeSide.lean`).** Before this round the pilot's chain to RH went through Hypothesis D (`DFamW`, `HypD`). D says the zeros of `ĝ_n` below `T_D` *are* the zeros of `ζ`. It presupposes the zeros it is meant to locate, which is §11's "RH ⇒ shadow" direction. `rh_of_prime_side` removes it:

* **(a) `HypConv a g`**: `ĝ_n(z)/ĝ_n(0) → Ξ(z)/Ξ(0)` locally uniformly. `Ξ` is one explicit entire function, built from Mathlib's `completedRiemannZeta₀`. No zero, and no zero count, enters.
* **(b) `RealRooted (a n) (g n)`**, required only eventually in `n`.

For ground states `g n` of Weil's form at supports `2a n`, (a) + (b) give Mathlib's `RiemannHypothesis`. No other input is needed:
* `ĝ_n(0) ≠ 0` eventually is derived from (a) at `z = 0`.
* `Ξ(0) ≠ 0` is `Xi_zero_ne_zero`.
* Integrability comes from `Probe`.

`hypConv_of_D` shows the old route is a special case: Hadamard factorisations, D and tails `ε → 0` imply (a). The open problem is exactly (a) and (b), and D is one sufficient condition for (a), a zero-dependent one.

**Step 2: (b) at small support (`Polya.lean`).** Pólya's class at half-support `a`:
* The functions are `g(t) = β + ∫ (a − max(|t|, c)) dμ(c)` on `[−a, a]`, with `β ≥ 0` and `μ` a measure on `[0, a)` with `∫ (a − c) dμ < ∞`.
* Each `a − max(|t|, c)` is a trapezoid. The class is exactly the even functions concave on `(−a, a)`: `μ` is `−g''` plus an atom `−g'(0+)` at `0`, and `β = g(a−)`.
* That converse representation is not formalised. Round 25 makes it unnecessary: `Concave.lean` proves the theorem for concave functions directly.

`realRooted_polya`: every nonzero member has a real-rooted transform. This is Pólya's 1918 theorem, specialised to even concave `f`. The proof is short and, as far as I know, not the textbook one:
* `integral_trap`, `ghatC_polya` (Fubini): `z²ĝ(z)/2 = βz sin(za) + ∫ (cos zc − cos za) dμ(c)`.
* `trap_ratio_im_pos`: for `Im z > 0` and `|c| < a`, `(cos zc − cos za)/sin za = 2/(cot A + cot B)` with `A = z(a+c)/2` and `B = z(a−c)/2`.
* `im_cot_neg`: `Im cot w = −sinh(2 Im w)/(2|sin w|²) < 0` in the upper half-plane. So every trapezoid's ratio has imaginary part of the sign of `Im z`, and so does `βz`.
* Divide the transform by `sin za` (nonzero off the real axis). The imaginary part is then a strictly signed integral, so it cannot vanish.

`realRooted_of_polya_shape`: any probe equal a.e. on `[−a, a]` to a nonzero member of the class is `RealRooted`. So (b) at a support reduces to one shape statement about the ground state: **concavity**. It involves no zero, no prime (for `δ < log 2`), and no limit.

**Does the ground state have that shape? (numerical, `frontier/polya_shape.py`, `polya_shape_results.jsonl`)** The ground state of `Q` is computed in the paper's Gram (cosine basis, 256 bits, `K = 160`–`240`). It is tested by second differences at step `a/40`, which is coarse against the Gibbs ripple of the truncated series.

| `δ` | 0.2 | 0.4 | 0.6 | 0.62 | 0.64 | 0.69 | 0.8 | 0.9 | 1.0 | 1.2 |
|---|---|---|---|---|---|---|---|---|---|---|
| concave? | yes | yes | yes | no | no | no | no | no | no | no |
| max second difference / `g(0)` | −7e-4 | −8e-4 | −1.3e-4 | +3e-5 | +2e-4 | +9e-4 | +5e-3 | +2e-3 | +2.5e-3 | +3e-3 |
| first zero of `ĝ` | 37.1 | 19.7 | 14.92 | 14.72 | 14.57 | 14.35 | 14.18 | 14.141 | 14.135 | 14.1347 |
| `2π/a` | 62.8 | 31.4 | 20.9 | 20.3 | 19.6 | 18.2 | 15.7 | **13.96** | **12.6** | **10.5** |

What the table shows:
* **The ground state is numerically concave for `δ ≲ 0.61` and not beyond.** The threshold is stable in `K` (160 → 240 at `δ = 0.6` and `0.69`).
* So for `δ ≲ 0.61`, (b) follows from `realRooted_of_polya_shape` once concavity is proved. That is a statement about the minimiser of an explicit, prime-free variational problem.
* Proving that concavity is **open**. It is the analogue of the known concavity of the first eigenfunction of the Cauchy process on an interval (Bañuelos–Kulczycki), for the kernel `e^{u/2}/sinh u`. That identification is from memory and not checked here.

**Where the mechanism stops (a structural fact, not just numerics).** For every member of Pólya's class, `Φ(x) = βx sin(xa) + ∫ (cos xc − cos xa) dμ` is positive for small `x > 0` and `≤ 0` at `x = 2π/a`. So `ĝ` has a real zero in `(0, 2π/a]`.
* The ground state's first zero is pinned near `γ₁ = 14.1347` from `δ ≈ 0.8` on (the dodging of round 23).
* Once `2π/a < 14.13`, i.e. `δ > 0.889`, the ground state **cannot** be concave.
* So concavity is at best a small-support mechanism. It covers exactly the regime where real-rootedness carries no information about `ζ`. The ground state's first zero is already at 14.35 at `δ = 0.69`, still with no prime in the form: the dodging of `γ₁` begins before any prime term is present.

**Status of §11 item 1 after this round.**

| | proved in Lean | open |
|---|---|---|
| (a) + (b) ⇒ RH | yes, with no zero in any hypothesis (`rh_of_prime_side`) | — |
| (b) at `δ ≲ 0.61` | modulo the ground state's concavity (`realRooted_of_polya_shape`; from round 25 `realRooted_of_ae_concaveOn`) | the concavity (numerically true) |
| (b) at `δ ≳ 0.61` | — | needs a mechanism other than concavity; provably so for `δ > 0.889` |
| (a) | only from D (`hypConv_of_D`), which is zero-dependent | a prime-side proof |

This is not RH progress. The small-support real-rootedness says nothing about `ζ`. What it provides is the first mechanism for (b) that is proved rather than observed, and a proof that this mechanism cannot reach the regime that matters. Candidates for the large-`δ` mechanism, none tried: Laguerre–Pólya closure (products of real-rooted transforms, i.e. convolutions of concave pieces); total positivity of the Gram pencil; interlacing of the ground-state transforms across `δ`.

## Round 25: Pólya's theorem for concave probes, with the named input removed (Concave.lean)

Round 24's `realRooted_polya` was stated for Pólya's class through its representation, a mixture of trapezoids with a measure `μ`. The converse, that every even concave function has such a representation, was a named classical input. Round 25 removes it. The theorem is now proved for concave functions directly, and no measure `−g''` is built.

**`realRooted_of_concaveOn`.** Let `g` be even, concave and `≥ 0` on `(−a, a)`, with `g(0) > 0`. Then `ĝ(z) = ∫_{−a}^{a} g(u) e^{izu} du` has only real zeros. Nothing is assumed at `±a`, where a concave function may jump or have infinite slope. `realRooted_of_ae_concaveOn` states the same for any probe equal to such a `g` a.e. on `[−a, a]`, which is the form the ground state enters in.

**The proof.**
* **The derivative.** `h = −g'₊` is the right derivative of the convex function `−g`. Mathlib gives it as a one-sided derivative at every interior point, together with its monotonicity (`hasDerivWithinAt_rightDeriv_of_mem_interior`, `monotoneOn_rightDeriv`). `h(0) ≥ 0` because `0` is the maximum (`negRD_zero_nonneg`).
* **Support `b < a` (`realRooted_concave_lt`).**
  * `ghatC_byParts`: evenness and integration by parts with right derivatives (`integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`) give `zĝ_b(z)/2 = g(b) sin(zb) + ∫₀^b h(t) sin(zt) dt`.
  * Dividing by `sin(zb)/z` and taking `Im z · Im(·)` gives `g(b)(Im z)² + ∫₀^b h w`, where `∫_c^b w = Im z · Im[(cos zc − cos zb)/sin zb]` (`tail_W`). By round 24's `trap_ratio_mul_pos`, every tail `∫_c^b w` is `≥ 0`.
  * `layer_nonneg`: for `h ≥ 0` nondecreasing, nonnegative tails give `∫₀^b h w ≥ 0`. The proof writes `h(s) = ∫₀^H 1[λ < h(s)] dλ` and applies Fubini. For each `λ`, the set `{h > λ}` is a final segment `(c, b]` of `[0, b]` up to one point, and its layer contributes the tail `∫_c^b w`.
  * `g(b) > 0` for `b < a` (`concave_pos`), so the sum is strictly positive and `ĝ_b` has no non-real zero.
* **The limit (`realRooted_of_concaveOn`).**
  * `‖ĝ_a(z) − ĝ_b(z)‖ ≤ 2g(0)e^{‖z‖a}(a − b)`, so `ĝ_{b_n} → ĝ_a` locally uniformly for `b_n = a(n+1)/(n+2)`.
  * `ĝ_a(0) = ∫g > 0`.
  * The pilot's `hurwitz_real` then carries real-rootedness to the limit.

**What changes.** Item 1(b) at a support now reduces, with nothing classical in between, to one hypothesis about the ground state: that it agrees a.e. with an even concave nonnegative function (it is already known to be one-signed and even). The numerical picture of round 24 is unchanged:
* concave for `δ ≲ 0.61`;
* not concave beyond that;
* provably not concave for `δ > 0.889`.

The open step at small support is proving that concavity. That is a statement about the minimiser of Weil's form, with no zero and, for `δ < log 2`, no prime.

## Round 26: the de Branges test (numerical, `frontier/debranges.py`, `frontier/locate.py`)

**The question.** Pólya's theorem (rounds 24–25) proves real-rootedness through a Hermite–Biehler structure, and that structure needs concavity. Does it survive past the concavity threshold `δ ≈ 0.61`? If it held at every `δ`, it would be the mechanism behind item 1(b).

**Which function.** For `g` decreasing on `[0, a]`, the obvious `E = 2∫₀^a g e^{−izt}` has its zeros in the upper half-plane (Kakeya), so it is never Hermite–Biehler. Pólya's structure sits one derivative down:
* `Ẽ(z) = g(0) − (iz/2)E(z) = βe^{−iza} + ∫₀^a h(t)e^{−izt} dt`, with `h = −g'` and `β = g(a)`.
* Its real and imaginary parts are `Ã = g(0) − zB/2` and `B̃ = zA/2 = zĝ/2`.
* When `h` is nondecreasing (`g` concave), Kakeya puts every zero of `Ẽ` in the lower half-plane. Then `Ẽ` is Hermite–Biehler and `ĝ` is real-rooted, with zeros interlacing those of `Ã`.

A caveat on what this tests. *Some* Hermite–Biehler `E` with `ĝ` as a component exists whenever `ĝ` is real-rooted (for example one built from `ĝ` and `ĝ'`). So the only informative test is on a function built from `g` without its zeros, and `Ẽ` is Pólya's.

**The tests** (the paper's Gram, 200–900 bits, coefficients at full precision):
* **(T1)** Zeros of `Ẽ` in the upper half-disc `|z| < 60`, by the argument principle.
* **(T2)** The phase derivative `W/|Ẽ|² = (ÃB̃' − Ã'B̃)/|Ẽ|²` on the real grid `(0, 60]`, step `0.01`. Hermite–Biehler requires it to be positive.
* `frontier/locate.py` finds the offending zeros.

| `δ` | 0.2 | 0.4 | 0.6 | 0.7 | 0.8 | **0.82** | 0.85 | 0.87 | 0.9 | 1.0 | 1.2 | 1.38 | 2.0 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| zeros of `Ẽ`, upper half-disc | 0 | 0 | 0 | 0 | 0 | **2** | 2 | 4 | 6 | 8 | 10 | 10 | 12 |
| grid points with `W < 0` (of 6000) | 0 | 0 | 0 | 0 | 0 | 205 | 331 | 580 | 1081 | 1931 | 2339 | 2342 | 2330 |

The results are stable in `K`: 100 → 160 at `δ = 0.8` and `0.9` changes nothing.

Offending zeros with `Re z > 0` (each has a mirror image `−z̄`):
* `δ = 0.82`: `21.62 + 0.26i`.
* `δ = 0.9`: `20.86 + 1.38i`, `32.25 + 0.80i`, `45.26 + 0.80i`.
* `δ = 1.0`: four zeros, at heights `2.1`–`2.7`.
* `δ = 1.38`: five zeros, at heights `3.6`–`9.5`.
* `δ = 2`: zeros at heights `4.4`–`13`.

**Findings.**
* **Pólya's Hermite–Biehler structure outlives concavity, but not by much.** It holds numerically for `δ ≤ 0.80`, past the concavity threshold `0.61`. It breaks between `0.80` and `0.82`.
* **The break is where dodging begins.** The first zero to cross into the upper half-plane appears near `Re z ≈ 21.6`, at `γ₂ = 21.02`. That is where the ground state's second zero is being pulled onto the zeta zero. From then on the zeros move deep into the upper half-plane.
* **So above `δ ≈ 0.81`, `ĝ`'s real-rootedness (round 23: every zero real at `δ = 1–3`) is not explained by this mechanism.**
* For the same reason as round 24's concavity bound, both mechanisms depend only on the *shape* of `g`. From about `δ ≈ 0.8` on, the ground state is shaped by the zeta zeros it dodges, and neither shape condition survives that.

**Status of item 1(b).**

| `δ` | mechanism | status |
|---|---|---|
| `≲ 0.61` | concavity ⇒ Pólya (proved in Lean, `realRooted_of_ae_concaveOn`) | concavity of the ground state open, numerically true |
| `0.61–0.80` | Pólya's Hermite–Biehler function `Ẽ` (numerical) | no proof route beyond the numerics |
| `≳ 0.81` | none known | `ĝ` numerically real-rooted, but neither natural structure holds |

The regime that matters for RH is the last row. What remains there is a mechanism tied to the Weil form itself rather than to the shape of `g`: for example, a positivity or interlacing property of the Gram pencil in `δ`, or a variational argument that a non-real zero would lower `Q`. None of these has been tested.

## Round 27: the zero flow in `δ`, and realification (numerical, `frontier/flow.py`, `frontier/flow4.py`, `frontier/realify.py`)

### Test A: the zeros of `ĝ_δ` flow monotonically, at every `δ` tested

**The test.** Ground states at `δ − h`, `δ`, `δ + h` (the paper's Gram, 200–900 bits, full-precision coefficients).
* Every real zero `x_j < 60` of `ĝ_δ` is refined by Newton at the working precision.
* Its velocity `v_j = dx_j/dδ` is taken by central difference, with `h = 10⁻³` and `10⁻⁴`; the two agree to 3–4 digits.
* The Wronskian `W = ĝ ∂_x∂_δĝ − ∂_δĝ ∂_xĝ` is evaluated on 6000 real points. It does not depend on how the ground state is normalised.
* The chain function `E_δ = ĝ + i ∂_δĝ` is tested for Hermite–Biehler.

`E_δ` is even in `z`, so the right variable is `s = z²`, and Hermite–Biehler means no zeros in the first quadrant of `z`. Near a real zero `x_j`, `E_δ` has a zero at `x_j + i v_j`. So the first quadrant is split in two:
* the strip `0 < Im z < η`, which is decided by the signs of the `v_j`;
* the rest, counted by the argument principle on a contour lifted to `Im z = η` (`η = 10⁻³` and `0.05`).

A first pass counted along the real axis itself and reported 1 and 12 spurious zeros at `δ = 1.38` and `2`. The pinned zeros' partners lie within `|v_j| ≈ 10⁻¹¹–10⁻²⁴` of that contour, where the phase unwrapping is unreliable.

| `δ` | zeros `< 60` | all `v_j < 0`? | `v_j` range | `W < 0` on the grid | zeros of `E_δ` off the axis |
|---|---|---|---|---|---|
| 0.4 | 3 | yes | `−41` … `−120` | 6000/6000 | 0 |
| 0.9 | 8 | yes | `−0.16` … `−52` | 6000/6000 | 0 |
| 1.0 | 9 | yes | `−0.013` … `−51` | 6000/6000 | 0 |
| 1.2 | 10 | yes | `−6×10⁻⁵` … `−50` | 6000/6000 | 0 (both `η`) |
| 1.38 | 11 | yes | `−6.7×10⁻⁸` … `−17` | 6000/6000 | 0 |
| 2.0 | 13 | yes | `−2.4×10⁻²⁴` (at `γ₁`) … `−2.4×10⁻⁵` | 6000/6000 | 0 (both `η`) |

**Findings.**
* **As `δ` grows, every zero of the ground state's transform moves toward the origin, at every `δ` tested from 0.4 to 2.** The zeros below `T_D` come down onto the zeta zeros from above and freeze there: at `δ = 2` the velocity is `10⁻²⁴` at `γ₁` and `10⁻¹¹` at `γ₈`. The zeros above `T_D` keep moving down, and they are the next ones to be captured.
* **`ĝ_δ` and `∂_δĝ_δ` interlace strictly.** Equivalently, `E_δ` is Hermite–Biehler in `s = z²` at every `δ` tested.
* This is the first structure that holds across the whole range, both inside and beyond the dodging regime. The two shape mechanisms fail: Pólya from `δ ≈ 0.61`, and its Hermite–Biehler function `Ẽ` from `0.81`.

**What it would give, and what it does not.**
* **Why it would matter.** Suppose one could prove that the zeros always move one way. Two real zeros could then never collide. A collision is the only way a pair of real zeros can leave the axis, apart from zeros arriving from infinity. So real-rootedness at small `δ` (Pólya, rounds 24–25) would carry over to every `δ`. That would be a candidate prime-side route to item 1(b).
* **Why it is not a mechanism yet.** It is an observation about the ground states, and Hermite–Biehler of `E_δ` contains the real-rootedness of `ĝ_δ`. A proof would need a formula for `∂_δ` of the minimiser, for example a Hadamard-type variational formula for moving the endpoint of the support, with a sign that forces interlacing.
* **Not examined:** zeros above 60, and `δ > 2`.

### Test B: realification does not lower the energy

**The test.** Probes `g = Σ_{k<K} c_k cos(kπt/a)` with `g(±a) = 0`. Their non-real zeros are the non-real roots of a polynomial `P(s)`, with `s = (ra/π)²`. Three maps replace each complex pair `σ, σ̄` of roots by real roots:
* `R1`: `(s − Re σ)²`;
* `R2`: `(s − Re σ ∓ |Im σ|)`, which is pointwise smaller in modulus on the real line;
* `R3`: `(s − |σ|)²`.

Every map also flips negative roots, which are imaginary zeros. Each keeps the degree, so the result is again a probe on `[−a, a]` (Paley–Wiener).

`Q/‖g‖²` is computed on the Fourier side, as `Q = 2ĝ(i/2)² + (1/π)∫₀^∞|ĝ|²Φ` with `Φ = Re ψ(¼ + ir/2) − log π − 2ΣΛ(n)n^{−½}cos(r log n)`. This matches the Gram to `10⁻⁵`–`10⁻⁸`.

| probes | `δ` | `K` | `R1` lowers | `R2` lowers | `R3` lowers |
|---|---|---|---|---|---|
| random (800) | 0.5 | 14 | 208/648 | 186/648 | 441/648 |
| random | 1.0 | 14 | 208/648 | 186/648 | 418/648 |
| random | 2.0 | 14 | 164/648 | 148/648 | 335/648 |
| ground state + 0.05·noise | 1.0 | 14 | 408/800 | 380/800 | **799/800** |
| ground state + 0.05·noise | 2.0 | 14 | 45/800 | 172/800 | 279/800 |
| ground state + 0.3·noise | 1.0 | 14 | 264/798 | 256/798 | 648/798 |
| ground state + 0.3·noise | 2.0 | 14 | 173/799 | 177/799 | 339/799 |

`K = 10` gives the same picture.

**Findings.**
* No realification map lowers the Rayleigh quotient consistently. `R1` and `R2` raise it more often than they lower it.
* `R3`, which moves each complex zero to its modulus on the real axis, lowers it almost always near the ground state at `δ = 1` (799/800). But it does so only in a minority of cases at `δ = 2`.
* So no simple "a non-real zero costs energy" argument is visible. Real-rootedness of the minimiser is not enforced by any of these local moves.
* **Caveat:** this is a `K = 14` space. At `K = 10` its constrained ground state is not even real-rooted, a truncation effect.

**Status of item 1(b) after round 27.** Of the four mechanisms tested, only the monotone zero flow (Test A) holds at every `δ` tested:
* concavity fails from `δ ≈ 0.61`;
* Pólya's `Ẽ` fails from `0.81`;
* realification fails at `δ = 2`.

Proving the flow is the concrete open step it points to: a sign for `∂_δ` of the ground state's transform at its zeros.

## Round 28: the pinned zeros sit above the zeta zeros (numerical, `frontier/pinned.py`)

**Why this test.** Rescale `g_a(t) = φ(t/a)`. The flow of round 27 is then `d log ρ_j/d log a < 1` for the rescaled zeros `ρ_j = a x_j`. With a pure `log|r|` symbol the ground state is scale-invariant, and the flow holds with room to spare (`d log ρ_j/d log a = 0`).

At the zeros pinned onto zeta zeros, though, the inequality holds only by exponentially small margins. There the flow is the statement that `x_j` decreases onto `γ_j`, i.e. `ε_j = x_j − γ_j > 0`. This round measures the sign of `ε_j` directly:
* zeros refined by Newton at the working precision;
* `γ_j` from `mpmath.zetazero` at 60 digits;
* each cell repeated at two values of `K`.

| `δ` | pinned zeros | `ε_j = x_j − γ_j` (`K` = first / second value) | all `> 0` |
|---|---|---|---|
| 1.0 | `γ₁` | `5.63e-4` / `5.62e-4` | yes |
| 1.2 | `γ₁–γ₃` | `1.79e-6, 2.70e-4, 3.41e-3` / `1.79e-6, 2.69e-4, 3.40e-3` | yes |
| 1.38 | `γ₁–γ₅` | `1.52e-9 … 3.26e-3` / `1.51e-9 … 3.24e-3` | yes |
| 1.6 | `γ₁–γ₈` | `4.32e-14 … 1.18e-3` / `4.28e-14 … 1.17e-3` | yes |
| 2.0 | `γ₁–γ₁₃` | `2.80e-26, 2.83e-23, 1.66e-21, … , 3.82e-7` / `2.71e-26, 2.74e-23, 1.60e-21, … , 3.72e-7` | yes |

**Finding.** Every pinned zero of the ground state's transform lies strictly above its zeta zero. That holds for all 52 zero–cell pairs, and the signs are stable in `K`. The `ε_j` shrink roughly exponentially in `δ` and grow with `j`. So the flow is not contradicted where it is most delicate. The picture is that the ground state's zeros descend monotonically and come to rest on the zeta zeros from above.

**What it means for a proof.** At a pinned zero the flow is equivalent to the sign of an exponentially small displacement `x_j − γ_j` of the minimiser's zeros relative to the zeta zeros. A prime-side proof of the flow must therefore produce that sign. That needs quantitative control of how the ground state locks onto `γ_j`, which is what item 1(a) asks for. So as far as this analysis goes, the flow is not an easier route to 1(b) than 1(a) itself. What it does supply is a sharp and falsifiable target: `x_j(δ) ↓ γ_j`, observed without exception at `δ ≤ 2`.

**Not tested:** `δ = 3` (it needs `K = 400`), and zeros above 60.

## Round 29: a law for the offsets `ε_j = x_j − γ_j` (numerical, `frontier/law.py`)

**The sign, restated.** Put `c_j = ĝ(γ_j)`. To first order, `ε_j = −c_j/ĝ'(γ_j)`, and this reproduces round 28's measured `ε_j` to 3–4 digits at every pinned zero. The pinned zeros are consecutive simple zeros, so `ĝ'(γ_j)` alternates in sign. Therefore **`ε_j > 0` for all `j` is equivalent to the values `ĝ(γ_j)` alternating in sign along the zeta zeros.** They do:

| `δ` | alternation of `sgn ĝ(γ_k)` holds for `k ≤` | pinned zeros |
|---|---|---|
| 1.0 | 6 | 1 |
| 1.38 | 12 | 5 |
| 2.0 | 29 | 19 (`|ε| < 10⁻²`) |

The alternation extends past the pinned zeros and then breaks: overall only 17–33% of consecutive pairs up to `γ₆₇₀₀` alternate.

**Where the energy sits (a check using the explicit formula, so conditional on RH).**
* Under RH, `Q(g) = 2Σ_{γ>0} ĝ(γ)²`. The first 6700 zeros give `0.9955 λ₁`, `0.990 λ₁` and `0.980 λ₁` at `δ = 1, 1.38, 2`, consistent with a tail above `γ₆₇₀₀`.
* The pinned zeros carry almost none of it. Each carries at most `5×10⁻⁴` of `λ₁`, and at `δ = 2` the zeros below 50 carry `< 10⁻²⁶`.
* The energy sits at the unpinned zeros: 35% in `50–100`, 55% in `100–500` (`δ = 2`).
* Only this interpretation uses the explicit formula. `ĝ(γ_k)`, `ĝ'(γ_k)` and `ε_j` are computed unconditionally.

**The magnitudes.** A least-squares fit of `log ε_j` against `γ_j` gives slopes `0.70, 0.78, 0.83, 0.97` at `δ = 1.2, 1.38, 1.6, 2`, i.e. `1.16a, 1.13a, 1.04a, 0.97a`. With `λ₁` factored out:

  **`ε_j ≈ C(δ) · λ₁ · e^{aγ_j}`**, with `log₁₀ C = −0.29, −0.36, −0.54, −1.04, −2.49` at `δ = 1, 1.2, 1.38, 1.6, 2`.

The per-zero scatter is `0.2–0.33` in `log₁₀`, about a factor of 2. Separately, `|ĝ'(γ_j)|` decays like `e^{−0.45γ_j}` to `e^{−0.59aγ_j}`, and `|c_j|` grows correspondingly.

**What the law does and does not say.**
* It locates the offsets. They are proportional to the ground-state energy and grow like `e^{aγ_j}` up the pinned range, until they reach `10⁻²–10⁻³`, where zeros stop being pinned.
* It does not explain the sign. `ε_j > 0` is the same statement as the alternation of `ĝ(γ_j)`, and that alternation is observed, not derived. The Euler–Lagrange equation says each pinned `c_j ≈ −(1/2a) Σ_{k≠j} c_k (S(γ_k − γ_j) + S(γ_k + γ_j))`, with `S(u) = 2 sin(au)/u`. So the alternation would have to come from how the sinc kernel carries the energy-bearing values at the unpinned zeros back onto the pinned range. That is a statement about the zeta zeros themselves.
* The fit is empirical: two parameters per `δ`, 1–13 points, factor-2 scatter. `C(δ)` has no model yet.

## Round 30: the universality test (numerical, `frontier/universality.py`)

**The question.** Is the zero flow of round 27 a general property of minimisers of truncated forms `Q(g) = (1/π)∫₀^∞|ĝ|²Φ [+ 2ĝ(i/2)²]` over growing supports? If so, it is a candidate for a general theorem. Or is it specific to `ζ`'s symbol `Φ = Re ψ(¼ + ir/2) − log π − 2ΣΛ(n)n^{−½}cos(r log n)` with the pole term?

**The method.**
* Gram matrices by Fourier quadrature on `(0, 3000]` with an analytic tail, cosine basis `K = 60`, in double precision.
* The control (`ζ` at `δ = 0.6, 0.9, 1.0`) reproduces the high-precision results: zeros to 4–5 digits, velocities to 3.
* For each symbol and `δ`: velocities of all zeros below 60, and the sign of `W = ĝ ∂_x∂_δĝ − ∂_δĝ ∂_xĝ` on 6000 points.
* Double precision is adequate here because every non-`ζ` ground energy is `|λ| ≥ 10⁻⁵`, apart from the `ζ`-identical `all_n` cells.

| symbol | pole | `δ` = 0.6, 0.9, 1.2, 1.6, 2.0: flow holds? (all `v < 0` and `W < 0` everywhere) |
|---|---|---|
| `ζ` (control, and high precision to `δ = 2`, round 27) | yes | yes at every `δ` |
| `log(1 + r)` | no | yes, yes, yes, yes, yes |
| `|r|` | no | yes, yes, yes, yes, yes |
| prolate: `1_{|r| > 12}` | no | yes, yes, yes, yes, yes |
| archimedean `Re ψ − log π`, no primes | no | yes, yes, yes, yes, yes |
| archimedean, no primes | **yes** | yes (`= ζ` there), **no** (`W > 0` at 898 points), **no**, **no**, **no** (one zero moving up) |
| `Λ(n)` replaced by `log n` (differs from `ζ` only for `δ ≥ log 4`) | yes | yes, yes, yes, yes, yes |
| primes' frequencies `log n` jittered by ±4% (1 draw) | yes | yes, yes, yes, **no** (2 zeros up), **no** |
| prime weights multiplied by `U(0.5, 1.5)` (1 draw) | yes | yes, **no**, **no**, **no**, **no** |

Robustness over 6 random draws each at `δ = 1.2, 1.6, 2.0`:

| perturbation | flow broken in |
|---|---|
| `log n` jittered by only **±1%** | 16 of 18 cells (4/6 at `δ = 1.2`, 6/6 at `1.6`, 6/6 at `2.0`) |
| prime weights jittered by **±10%** | 12 of 18 cells (1/6, 6/6, 5/6) |

**Findings.**
1. **For monotone symbols without the pole term, the flow looks general.** It holds for `log`, `|r|`, the prolate step and the bare archimedean term at every `δ`. For these, a general theorem (monotone symbol ⇒ zeros of the truncated minimiser flow inward) is a plausible target. The scale-invariant symbols are the easy case of round 28's analysis.
2. **The pole term alone breaks it.** Adding `2ĝ(i/2)²` to the archimedean symbol destroys the flow from `δ = 0.9` on.
3. **The true primes restore it, and it is fragile.** With the actual `Λ(n)` at the actual frequencies `log n`, the flow holds through `δ = 2` (at high precision in round 27). A ±1% jitter of the frequencies breaks it in most draws, and so does a ±10% jitter of the weights. The one exception tested is `all_n` (`Λ(4) = log 2` replaced by `log 4`), which keeps it at `δ = 1.6` and `2`. So the flow is not strictly arithmetic, but it is not generic either.
4. **Consequence for a proof.** For `ζ`'s form the flow depends on the fine structure of the prime sum balancing the pole term. That is the same balance that makes Weil's form nonnegative (`λ₁ > 0` for `ζ`, versus `λ < 0` in every perturbed cell). It fits rounds 28–29: the flow at pinned zeros is the statement `x_j ↓ γ_j`, a property of the zeta zeros. A general "monotone symbol" theorem cannot reach `ζ`'s case, because `ζ`'s symbol is not monotone and carries the pole term. So as far as these tests go, a proof of the flow for `ζ` is not easier than item 1(a).

**Not established.** Negativity of `λ` does not predict failure: the pole-free archimedean term and `all_n` have `λ < 0` and keep the flow. Each "no" in the first table is a single random draw; the robustness table covers 6 draws per perturbation.

## Round 31: is there a commuting Sturm–Liouville operator? (numerical, `frontier/prolate_test.py`, `frontier/prolate_wide.py`)

**The idea imported.** Slepian's "lucky accident": band-limiting to `|r| < W` on `[−a, a]` commutes with `L = −d/dt((a² − t²)d/dt) + W²t²`. So its eigenfunctions are Sturm–Liouville eigenfunctions, whose zeros are controlled by ODE theory: real, simple, counted, and moving monotonically. If the truncated Weil form commuted with such an `L`, even approximately, real-rootedness could come from ODE theory rather than from positivity. That is the one import found that is not automatically circular.

**The test.** Gram `G` for each symbol (round 30's quadrature, `K = 60`), in `N`-orthonormal coordinates.
* **Family 1:** `L = −(p g')' + q g` with `p = a² − t²` and `q = Σ_{m=1..4} q_m t^{2m}`.
* **Family 2:** `p = (a² − t²)(1 + Σ_{m=1..3} p_m t^{2m})` and `q = Σ_{m=1..8} q_m t^{2m}`.

In both families the commutator is linear in the coefficients, so the best `L` is a least-squares fit on the first 30 modes. Three measures:
* `‖[G, L]‖/‖[G, L₀]‖`;
* the off-diagonal fraction of `G` in `L`'s eigenbasis (0 means they commute);
* the ground state's best overlap with a single eigenfunction of `L`.

**The control.** For `Φ = 1_{|r|>12}` the fit recovers `q₁ = 143.9` (exact: `W² = 144`), with off-diagonal fraction `5×10⁻⁴`–`1.2×10⁻³` and overlap `1 − 10⁻⁸`. That is the truncation floor.

| symbol | residual (family 1 / 2) | off-diagonal fraction | ground-state overlap |
|---|---|---|---|
| control (band-limit) | 0.002–0.004 | 0.0005–0.0012 | 1.000000 |
| `log(1 + r)` | 0.95 / 0.87 | 0.42–0.44 | 0.79–0.89 |
| `|r|` | 0.61 / – | 0.85 | 0.70 |
| archimedean, no pole | 0.97 / 0.89 | 0.42 | 0.86–0.94 |
| archimedean + pole | 0.93–0.98 / – | 0.42–0.58 | 0.90–0.98 |
| **`ζ`** | 0.62–0.93 / **0.15–0.31** | **0.42–0.76** | **0.65–0.93** |

Ranges are over `δ = 0.6, 1.0, 1.6, 2.0` (family 1) and `δ = 1.0, 2.0` (family 2).

**Findings.**
* **No second-order operator in either family comes close to commuting with `ζ`'s truncated form.** The wider family lowers the fitted residual to 0.15–0.31, but the form stays 46–64% off-diagonal in the operator's eigenbasis, and the ground state is not an eigenfunction of it (overlap 0.78–0.83). The lower residual is fitting, not commutation.
* **The same holds for the simple monotone symbols** (`log`, `|r|`, bare archimedean), for which the zero flow does hold (round 30). So the flow is not produced by a hidden Slepian structure either.
* **This is consistent with the bispectral picture (from memory, unchecked here).** Time–frequency limiting admits a commuting differential operator essentially only for bispectral kernels (Duistermaat–Grünbaum), and a log-type symbol with a prime sum is not expected to be one.
* **Not excluded:** operators of order higher than 2; non-polynomial coefficients; differential operators acting in the frequency variable `r` instead of `t`; the semilocal prolate operators of Connes–Consani–Moscovici, which act on a different space. The test covers only the natural Slepian-type families.

## Round 32: a counting law for the pinning front (numerical, `frontier/front.py`)

**The import.** A function in the Paley–Wiener space of type `a` has about `aT/π` zeros below `T`, while `ζ` has `N(T) ≈ (T/2π)log(T/2πe) + 7/8`. The ground state can pin its zeros onto every `γ` only while its zero budget covers theirs. The budget runs out at the root `T_B(a)` of `(T/2π)log(T/2πe) + 7/8 = aT/π`. At leading order that is `T_B ≈ 2πe^{2a+1} = 2πe^{δ+1}`.

**The measurement.** Ground states from the paper's Gram (`K = 160`–`260`, 600–1100 bits). Zeros of `ĝ` below `R = 250`, each matched to its nearest zeta zero. The front `T_pin(τ)` is the largest `γ_k` such that every `γ_j ≤ γ_k` has a zero of `ĝ` within `τ`.

| `δ` | `λ₁` | `T_pin(10⁻⁶)` | `T_pin(10⁻³)` | `T_pin(10⁻¹)` | `T_B` (refined) | `T_pin(10⁻¹)/T_B` |
|---|---|---|---|---|---|---|
| 1.0 | 9.3e-7 | – | 14.1 | 21.0 | 40.5 | 0.52 |
| 1.2 | 1.6e-9 | – | 21.0 | 30.4 | 50.9 | 0.60 |
| 1.38 | 8.8e-13 | 21.0 | 30.4 | 37.6 | 62.3 | 0.60 |
| 1.6 | 1.7e-17 | 32.9 | 40.9 | 53.0 | 78.9 | 0.67 |
| 1.8 | 4.2e-23 | 43.3 | 56.4 | 65.1 | 97.7 | 0.67 |
| 2.0 | 6.1e-30 | 60.8 | 72.1 | 82.9 | 120.6 | 0.69 |
| 2.3 | 2.1e-43 | 92.5 | 101.3 | 111.0 | 164.8 | 0.67 |

**Findings.**
* **The front grows at the rate the counting law predicts.** From `δ = 1.6` to `2.3`, `ln T_pin(10⁻¹)` rises by `0.74` over `Δδ = 0.7`, a slope of `1.06`; the law predicts `≈ 1`.
* **The prefactor settles.** `T_pin(10⁻¹) ≈ 0.68 · T_B(a)` from `δ = 1.6` on. The tighter fronts `10⁻³` and `10⁻⁶` sit lower, and their ratios rise with `δ`: 0.35 → 0.61 and 0.34 → 0.56.
* **The ground state does not use its full budget at low heights.** At `δ = 2` it has 13 zeros below 60, all pinned, whereas `aT/π = 19`. The zero-count deficit `N_ζ(T) − N_ĝ(T)` becomes positive near 79 at `δ = 2` and near 104 at `δ = 2.3`, and then grows linearly. So pinning stops at about two-thirds of the height where the count alone would force it to stop.
* **The alternation front of round 29** (`37.6, 56.4, 98.8` at `δ = 1, 1.38, 2`) lies between `T_pin(10⁻¹)` and `T_B`. This round's own alternation values at `δ = 1.8`, `2` are not reliable: `|ĝ(γ)|` is below the rounding error of double-precision `γ` there. Round 29 used 60-digit `γ` and is the one to trust.

**What it gives item 1(a).** An empirical rate. The dodging reach grows like `T_D(δ) ≈ 0.68 · T_B ~ e^{δ}`. With the paper's tail estimate `ε(δ) ~ ln T_D/T_D`, the pairing error would decay like `δ e^{−δ}`. That would be the quantitative form of hypothesis D's `ε(δ) → 0` that `rh_of_D_and_realRooted` needs, if it could be proved. This is an observation over `δ ≤ 2.3` with a fitted constant, not a theorem. The counting side is standard (Riemann–von Mangoldt, Paley–Wiener zero density). The missing piece is why the ground state spends its zero budget on the zeta zeros at all, which is the dodging itself.

## Round 33: deriving the front, via constrained equilibrium (model, `frontier/edge_model.py`)

**The import: Rakhmanov's constrained equilibrium problem (also Dragnev–Saff, Kuijlaars–Rakhmanov; from memory).** Polynomials orthogonal on a discrete node set cannot have zeros denser than the nodes. Where the unconstrained zero density would exceed the node density, the zeros saturate: they sit within exponentially small distance of the nodes. Elsewhere they are free. That is the picture of rounds 27–32:
* the zeta zeros play the nodes, with density `σ(t) = (1/2π)log(t/2π)`;
* `ĝ` has type `a`, so its zeros want density `a/π`, which is larger than `σ` at low heights;
* the pinned zeros sit above `γ_j` within `e^{−cγ}`.

**The model.** The zero density `μ` of `ĝ` satisfies:
* `μ = σ` on the saturated region `(−T, T)`;
* on the free region `|x| > T`, the smoothed envelope `log|ĝ|` is flat, i.e. the Hilbert transform of `μ` vanishes there (round 29: the energy sits at the unpinned zeros);
* `μ → a/π` at infinity (exponential type `a`).

**The derivation.** Put `f = μ − a/π` and let `G` be its Cauchy transform, so `Re G = 0` outside and `Im G = πf` inside on the upper boundary. Then `Λ = G/√(z² − T²)` has `Re Λ = 0` outside and `Re Λ = πf/√(T² − t²)` inside. So `Λ` is a Schwarz integral, and `G = O(1/z)` (density exactly `a/π` at infinity) holds if and only if

  `∫₀^T σ(t)/√(T² − t²) dt = a/2`.

Compare the budget condition of round 32, `∫₀^T σ dt = aT/π`: the same density with a different weight. Using `∫₀^{π/2} log sin θ dθ = −(π/2)log 2`, the left side is `(1/4)log(T/4π)` for large `T`, so

  **`T_edge = 4πe^{2a}`, and `T_edge/T_B → 4πe^{2a}/(2πe^{2a+1}) = 2/e ≈ 0.7358`.**

The exact integral (smoothed Riemann–von Mangoldt density, no fitted parameter) gives ratios `0.7514, 0.7478, 0.7454, 0.7432, 0.7417, 0.7405, 0.7392` at the measured `δ`, and `0.7374, 0.7360, 0.7358` at `δ = 3, 5, 10`.

**Against the measurements.**

| `δ` | `T_edge` | `T_edge/T_B` | measured `T_pin(10⁻¹)` | `T_pin(10⁻¹)/T_edge` | alternation front (round 29) |
|---|---|---|---|---|---|
| 1.0 | 30.5 | 0.751 | 21.0 | 0.69 | 37.6 |
| 1.2 | 38.1 | 0.748 | 30.4 | 0.80 | – |
| 1.38 | 46.5 | 0.745 | 37.6 | 0.81 | 56.4 |
| 1.6 | 58.6 | 0.743 | 53.0 | 0.90 | – |
| 1.8 | 72.4 | 0.742 | 65.1 | 0.90 | – |
| 2.0 | 89.3 | 0.740 | 82.9 | 0.93 | 98.8 |
| 2.3 | 121.8 | 0.739 | 111.0 | 0.91 | – |

**Findings.**
* **The ground state stops saturating where the `1/√(T² − t²)`-weighted density of zeta zeros reaches `a/2`, not where the plain counts cross.** That puts the edge at a fixed fraction of the budget root, tending to `2/e`, and explains why the pinning stops well short of where the count alone would stop it.
* **The measured fronts bracket the edge.** The strict fronts lie inside it: `T_pin(10⁻¹) ≈ 0.90–0.93 T_edge` from `δ = 1.6` on. The alternation front lies just outside it (`98.8` against `89.3` at `δ = 2`). This is the expected transition zone between the saturated and free regions.
* **So round 32's `0.68 ≈ (2/e) × 0.92`.** The `2/e` is derived. The `0.92` is where a `10⁻¹`-tolerance criterion sits inside the transition zone, and it is not derived. In discrete orthogonal polynomials that zone has its own local scaling (from memory), which was not modelled here.

**Status.** This is a heuristic model:
* the flat envelope on the free region and the saturation below `T` are assumed, not proved from Weil's form;
* the solvability step is the standard Schwarz-integral argument, sketched here rather than formalised.

It gives a parameter-free prediction for the dodging reach, `T_D(δ) ≈ 4πe^{δ}` (`2a = δ`), which is what hypothesis D's `ε(δ) → 0` needs. Proving it would need the constrained-equilibrium asymptotics for this `PW_a`-type extremal problem, a strong-asymptotics result in the style of discrete orthogonal polynomials. Whether that can be done without assuming RH is open. The model uses the zeta-zero density `σ` as input, but not RH.

## Round 34: the transition zone, derived from the same model (`frontier/transition.py`)

**The mechanism.** In the round-33 model the smoothed envelope inside the saturated region is fixed by the same boundary problem:

  `U'(x) = √(T² − x²) · p.v.∫_{−T}^{T} f(t) dt / (√(T² − t²)(x − t))`, with `f = σ − a/π`.

Round 29 showed `ĝ(γ_j) ∝ λ₁e^{−U}` and `|ĝ'(γ_j)| ∝ e^{U}`. So the offsets follow

  `ε(x) ≈ A e^{−2Δ(x)}`, with `Δ(x) = U(x) − U(T_edge)`.

`A` is fixed without fitting: at the edge a zero is free, so its offset is about half a zero spacing, `A = 1/(2σ(T_edge))`. The front `T_pin(τ)` is the root of `2Δ(x) = log(A/τ)`.

**Checks on the envelope.**
* **Slope.** `log ε_j` against `−2Δ(γ_j)`, over all pinned zeros, has slope `0.79, 0.86, 0.89, 0.93` at `δ = 1.2, 1.38, 1.6, 2`, tending to 1.
* **Depth.** The model's `2Δ(0)` is `17.8, 24.7, 32.4, 43.8, 72.9` against `−log λ₁ = 13.9, 20.2, 27.8, 38.6, 67.3` at `δ = 1, 1.2, 1.38, 1.6, 2`. This is a near-constant offset of 4–5.6 on depths up to 73, so the model also predicts the ground-state energy to within a factor of about `e^5`.

**The fronts, predicted with no fitted parameter** (`T_pin/T_edge`; brackets: `A = 1/(πσ)`):

| `δ` | `τ = 10⁻¹` predicted | measured | `τ = 10⁻³` predicted | measured | `τ = 10⁻⁶` predicted | measured |
|---|---|---|---|---|---|---|
| 1.0 | 0.76 [0.78] | 0.69 | 0.55 [0.57] | 0.46 | 0.31 [0.32] | –* |
| 1.2 | 0.80 [0.82] | 0.80 | 0.63 [0.64] | 0.55 | 0.42 [0.43] | –* |
| 1.38 | 0.83 [0.85] | 0.81 | 0.68 [0.69] | 0.65 | 0.50 [0.51] | 0.45 |
| 1.6 | 0.86 [0.88] | 0.90 | 0.73 [0.74] | 0.70 | 0.58 [0.59] | 0.56 |
| 1.8 | 0.88 [0.90] | 0.90 | 0.77 [0.78] | 0.78 | 0.64 [0.65] | 0.60 |
| 2.0 | 0.90 [0.91] | 0.93 | 0.80 [0.81] | 0.81 | 0.69 [0.70] | 0.68 |
| 2.3 | 0.92 [0.93] | 0.91 | 0.84 [0.85] | 0.83 | 0.75 [0.76] | 0.76 |

\* At `δ = 1` the predicted `10⁻⁶`-front (9.5) lies below `γ₁ = 14.13`, so no zero is pinned at that level; measured `ε₁ = 5.6×10⁻⁴`, consistent. At `δ = 1.2` the prediction (16.0) is just above `γ₁`, while the measured `ε₁ = 1.8×10⁻⁶` is just above `10⁻⁶`: a marginal miss.

**Findings.**
* **The transition factor is derived.** All three fronts, at every `δ`, are reproduced to within `0.01–0.09` (mostly `≤ 0.04`) by one model with no fitted parameter. The fronts barely depend on the choice of `A`: `1/(2σ)` against `1/(πσ)` moves them by `0.01–0.02`.
* **The "0.92" is not a constant.** It is the `10⁻¹`-front of a transition zone that narrows relative to `T_edge` as `δ` grows (0.76 → 0.92). Round 32's plateau `T_pin/T_B ≈ 0.68` was the product of this rising factor and the slowly falling edge ratio (0.743 → 0.739). Predicted products are `0.64, 0.65, 0.67, 0.68` at `δ = 1.6, 1.8, 2, 2.3`, against measured `0.67, 0.67, 0.69, 0.67`.
* **Asymptotically every fixed-tolerance front tends to `T_edge`.** The pinning reach is `T_D(δ) ~ 4πe^{δ}`, and every `T_pin(τ)/T_B → 2/e`.

**Status.** Rounds 32–34 together give a parameter-free heuristic account of the dodging reach, the transition zone, the offset law of round 29 (`ε ∝ λ₁e^{−2U}`), and the order of magnitude of `λ₁`. It rests on the constrained-equilibrium model (saturation below `T`, flat envelope above), which is assumed, not derived from Weil's form. Turning it into a theorem needs strong asymptotics for this extremal problem. That would be the rigorous content of hypothesis D's `ε(δ) → 0`, and whether it can be proved without RH is open. The model uses the zeta-zero density `σ` as input, but not RH.

## Round 35: saturation, reduced to an envelope bound (Saturation.lean)

**What can and cannot be proved.** The saturation assumption of rounds 33–34 says that below the edge, every zeta zero has a zero of the ground state's transform `ĝ` exponentially close to it. That is a statement about the zeta zeros, so a proof must pass through the explicit formula `Q(g) = Σ_ρ ĝ(t_ρ)²`. Off the critical line those terms are complex and cannot be bounded one at a time. So full saturation from the prime side alone is as hard as Hypothesis D (item 1(a)), and it is not claimed.

**The reduction, proved** (named input: the explicit formula with the zeros on the line, `Q = 2Σ_{γ>0} ĝ(γ)²`):
* `sq_le_of_explicit`: `|ĝ(γ_j)| ≤ √(λ/2)` for every `j`, since each term is at most the sum.
* `zero_near_of_deriv_ge`, `zero_near_of_deriv_le`: a function at most `η` in size at `γ`, with `|F'| ≥ m` of fixed sign on `[γ − r, γ + r]` and `η/m ≤ r`, vanishes within `η/m` of `γ`. The proof uses the mean value theorem and the intermediate value theorem.
* `pinned_of_explicit`: a zero of `ĝ` lies within `√(λ/2)/m` of every `γ_j` near which `|ĝ'| ≥ m`.

So **saturation holds wherever the envelope `|ĝ'|` exceeds `√λ₁`**. That is the model's saturated region, since the band level of round 33 is `C_b ≈ ½ log λ₁`. The proved rate is `e^{−Δ}`; the model's is `e^{−2Δ}`. The model's assumption is thereby reduced to a lower bound on the envelope. That bound, and the explicit-formula input, are what remain open.

**Against the data** (`frontier/saturation_check.txt`). The bound `√(λ₁/2)/|ĝ'(γ_j)|` holds at all 25 pinned zeros (`δ = 1, 1.38, 2`). It is loose by `e^{Δ}`: from `1.5×10¹³` at `γ₁` down to `47` near the edge, with `bound² ≈ ε_j` up to a factor of 6–20, as the two rates predict. At `δ = 2` it certifies saturation at the `10⁻¹` level through `γ₁₈ ≈ 72.1`, against the measured front `83` and the model edge `89`. These values use the computed `ĝ'`, not a certified envelope bound, and the window condition `√(λ/2)/m ≤ r` is not checked near the edge.

**Unconditional variant (a remark, not formalised).** RH is verified numerically up to height `H ≈ 3×10¹²`. The terms of the explicit formula above `H` can be bounded by `|ĝ(t)| ≤ e^{a/2}‖g‖₁` times a decay factor. That replaces `λ` by `λ + O(log H/H)` in `sq_le_of_explicit`, which is usable where `λ₁` is not smaller than about `10⁻¹¹` (`δ ≲ 1.3`). Making it rigorous needs a decay bound for `ĝ` off the axis, which in turn needs bounded variation of the ground state; that is not proved.

## Round 36: out-of-sample test of the model (pre-registered; `frontier/predict.py`, `frontier/envelope.py`)

**Protocol.** The model's predictions for `δ = 2.6` and `3.0` (`frontier/predictions_round36.jsonl`) were committed in `4b79a57` before any ground state at those supports was computed. The fronts use no fitted parameter. The `λ₁` prediction carries one additive offset, extrapolated linearly from its values at `δ ≤ 2`.

| | `δ = 2.6` predicted | measured | error | `δ = 3.0` predicted | measured | error |
|---|---|---|---|---|---|---|
| `T_pin(10⁻¹)` | 155.7 | 156.1 | 0.3% | 237.9 | 241.0 | 1.3% |
| `T_pin(10⁻³)` | 144.8 | 146.0 | 0.8% | 225.3 | 227.4 | 0.9% |
| `T_pin(10⁻⁶)` | 132.5 | 131.1 | 1.1% | 211.3 | 211.7 | 0.2% |
| `−log λ₁` | 140.42 | 140.70 | 0.28 | 221.58 | 222.17 | 0.59 |

The measurements used `K = 300` / `400` at 1000 / 1100 bits, with zeros of `ĝ` tracked to 250 / 300. This round's `T_alt` values are not reliable, because double-precision `γ` was used (see round 32).

**The envelope, a second independent check (round 36b).** A sine-like function has `|ĝ'| ≈ e^{U}·πσ` at its zeros, so `log|ĝ'(γ_j)| − log(πσ(γ_j)) − log ĝ(0)` measures the envelope `U(γ_j)`. It follows the model's `U` (rounds 33–34, nothing fitted) over 36 e-folds:
* slope `0.979` at `δ = 2` and `0.943` at `δ = 1.38`;
* a near-constant offset of `0.5–0.9` deep inside;
* the offset rises to about `1.5` in the transition zone near the edge.

**Finding.** The constrained-equilibrium model predicts the pinning fronts at two unseen supports to `0.2–1.3%`, and `λ₁` to within `0.3–0.6` in `log` over depths of 140–222. Together with the envelope check, it is a quantitatively accurate description of the ground states: of how far they dodge the zeta zeros (`T_D ≈ 4πe^{δ}`), of the transition zone, and of the energy.

**Its assumptions are unchanged** (see the summary under round 35):
* saturation, which `Saturation.lean` reduces to RH (the explicit formula with the zeros on the line) plus a lower bound on `|ĝ'|`;
* a flat envelope above the edge;
* smoothed densities;
* the half-spacing normalisation `A`;
* one extrapolated offset, for `λ₁` only.

Because saturation currently enters through RH, the model describes item 1(a) quantitatively but does not prove it.

## Round 37: saturation without RH (Unconditional.lean, `frontier/unconditional.py`)

**What replaces RH.** `Saturation.lean` (round 35) took the explicit formula with every zero on the line, i.e. RH, as input. Here the inputs are theorems, plus one property of the ground state that is observed numerically:
* **`hQ`: the unconditional explicit formula** `Q = Σ_ρ ĝ(t_ρ)²`, over all nontrivial zeros with multiplicity. For even `g`, the transform of the autocorrelation is `ĝ²`.
* **`hRH`: verified RH up to `H`.** Zeros with `|Re t| ≤ H` are real. Platt–Trudgian give `H = 3·10¹²`; this is cited from memory and should be checked against the source.
* **`hstrip`: the critical strip,** `|Im t| ≤ ½`.
* **`hS`: a zero-counting bound,** `Σ_{|Re t| > H} (Re t)⁻² ≤ S`. With Trudgian's explicit `N(T)` bound (from memory: `N(T) ≤ (T/2π)log(T/2πe) + 7/8 + 0.112 log T + 0.278 log log T + 2.51`), `S_H = 4∫_H^∞ N⁺(t)/t³ dt = 5.7×10⁻¹²`.
* **The ground state is even, `≥ 0` and non-increasing on `[0, a]`.** Observed at every support tested (below). Not proved.

**Proved (four theorems, standard axioms only):**
* `norm_ghatC_le_of_antitone`: for `g` even, `≥ 0` and non-increasing on `[0, a]`, `‖ĝ(z)‖ ≤ 2g(0)cosh(a|Im z|)/‖z‖`. The proof is a layer cake: each level set is a symmetric interval, whose transform is `2 sin(zr)/z`, and `|sin w| ≤ cosh(Im w)`.
* `sq_le_of_explicit_tail`: every verified zero `t_j` has `‖ĝ(t_j)‖² ≤ Q + B²S`. The low terms are nonnegative squares of real numbers, and each high term is `≥ −B²/(Re t)²`.
* `ghatC_im_eq_zero`: `ĝ` is real on the real line for even `g`.
* `pinned_unconditional`: with `B = 2g(0)cosh(a/2)`, `ĝ` has a zero within `√(Q + B²S)/m` of every verified zeta zero near which `|ĝ'| ≥ m`, with fixed sign.

**Numbers** (normalised ground states; `B ≈ 3.5–4.1`, `B²S_H ≈ 7–10×10⁻¹¹`; the bounds use the computed `|ĝ'(γ_j)|`):

| `δ` | `λ₁` | non-increasing on `[0, a]`? | `B²S_H` | Lean bound at `γ₁` | at `γ₂` | at `γ₃` |
|---|---|---|---|---|---|---|
| 0.60 | 7.6e-03 | yes (largest step -1e-04) | 7.5e-11 | 2.5e+00 | 9.4e+00 | 9.7e+00 |
| 1.00 | 9.4e-07 | yes (largest step -1e-04) | 7.0e-11 | 7.9e-02 | 6.5e-01 | 1.5e+00 |
| 1.20 | 1.6e-09 | yes (largest step -1e-04) | 7.0e-11 | 4.7e-03 | 6.8e-02 | 2.5e-01 |
| 1.38 | 8.8e-13 | yes (largest step -5e-06) | 7.1e-11 | 1.2e-03 | 2.5e-02 | 1.2e-01 |
| 2.00 | 6.3e-30 | yes (largest step -5e-13) | 7.6e-11 | 2.1e-03 | 8.2e-02 | 6.9e-01 |
| 3.00 | 4.3e-97 | yes, up to rounding (largest step 4e-16) | 9.7e-11 | 3.3e-03 | 2.0e-01 | 2.4e+00 |

**Findings.**
* Where `λ₁ ≫ B²S_H` (`δ ≲ 1.2`), the bound without RH equals the RH-conditional one.
* Beyond that the tail dominates, but the lowest zeta zeros are still certified. At `δ = 2` the ground state has a zero within `2×10⁻³` of `γ₁` and `0.08` of `γ₂`. At `δ = 3`: `3×10⁻³` and `0.2`.
* The RH-conditional bound of round 35 reaches much further (`10⁻¹³` at `γ₁`, `δ = 2`), because there the tail `B²S_H ≈ 7×10⁻¹¹` is replaced by `λ₁ = 6×10⁻³⁰`.

**What is still assumed.**
* **Monotonicity of the ground state**, which gives the decay constant `B`. It is numerically true; for `δ < log 2` a rearrangement argument should prove it (the kernel `e^{u/2}/sinh u` is decreasing and the pole weight `cosh(u/2)` is increasing). With primes present, it is open.
* **The slope bound** `|ĝ'| ≥ m` on each window. The table uses computed values, not a certified enclosure of the true ground state.
* **The three external inputs** (the explicit formula, the verified height `H`, the `N(T)` bound). These are published theorems, but they are named inputs, not formalised.

Of these, only monotonicity and the slope bound concern the ground state itself. Neither involves RH.

## Round 38: comparison with Zhu (arXiv 2608.24827) (`frontier/certify_gamma1.py`, `frontier/predict_zhu_results.jsonl`)

Zhu (Sept 2026) studies the same Weil quadratic form on `[−L, L]`; his `L` is our `a = δ/2`. His paper has:
* certified Weil positivity on `[−0.8, 0.8]` (`λ₁ ≥ 8.9×10⁻¹⁸`);
* at `L = 0.8` (Theorem 6.2), a certified simple, even ground state, with `λ₁ ∈ [8.9×10⁻¹⁸, 2.523×10⁻¹⁶]`, `λ₂^even ≥ 2.085×10⁻¹²` and `λ₁^odd ≥ 8.206×10⁻¹⁵`;
* certified upper bounds on `λ*` to `L = 2` (Table 3);
* a fitted law, `−ln λ* ≈ 2π²·N(T*)/ln N(T*)` with `T* = 2πe^{2L}`;
* a conditional theorem, `λ* ≤ exp(−Le^L)`.

Numbers quoted from his paper are named inputs, not re-derived here.

**1. Cross-validation.** Our `λ₁` (ball Gram, `tools/research/weil_prime_gram.py`) matches his Table 1 to 3 digits at `δ = 1, 1.2, 2`. At `δ = 1.6` our Rayleigh value `1.673×10⁻¹⁷` lies inside his certified interval.

**2. Our depth model against his certified `−ln λ*`.** The model is the round-36 model (`predict.py`), unchanged. The comparison was run after reading his table, so it is out of sample but not pre-registered. `δ = 2.0` is in-sample for the offset fit.

| `δ` (`L`) | ours | Zhu, certified | difference | his `2π²N/lnN` law |
|---|---|---|---|---|
| 2.0 (1.0) | 67.22 | 66.99 | +0.23 | 77.24 |
| 2.4 (1.2) | 110.79 | 110.53 | +0.26 | 115.31 |
| 2.8 (1.4) | 176.86 | 176.65 | +0.21 | 176.05 |
| 3.2 (1.6) | 276.37 | 276.46 | −0.09 | 270.35 |
| 3.6 (1.8) | 426.06 | 426.22 | −0.16 | 415.27 |
| 4.0 (2.0) | 649.99 | 650.47 | −0.48 | 636.85 |

The law column uses the smooth `N(T)`. The constrained-equilibrium model tracks the certified values to `≤ 0.5` across the whole range. The one-constant law is off by up to 10 near `δ = 2` and drifts by 13 at `δ = 4`.

**3. Where the dodging happens.** Zhu's `T* = 2πe^{2L}` is a density-crossing heuristic. Our edge is `T_edge ≈ 4πe^{2a}` (round 33), about `2T*` (89.3 vs 46.4 at `L = 1`). The measured pinning fronts (round 36; 82.9 at tolerance 0.1, `δ = 2`) lie well beyond `T*`. So `T*` sets the scale but underestimates how far the zeros of `ĝ` are pinned.

**4. What we took from him: a certified slope at `γ₁`.** His certified gap at `L = 0.8` closes one of the two ground-state gaps left open in round 37, at `δ = 1.6` and `γ₁` only. `certify_gamma1.py` proceeds in five steps:
* `φ` is the computed ground state (`K = 160`, 800 bits). Its Rayleigh quotient `ρ` is a ball value.
* Davis–Kahan gives `‖φ − g‖² ≤ 2(ρ − λ₁^lo)/(λ₂^lo − ρ)`, so `‖φ − g‖ ≤ 2.74×10⁻³`.
* This gives `|ĝ' − φ̂'| ≤ √(2a³/3)·‖φ − g‖ = 1.60×10⁻³`.
* Ball arithmetic encloses `φ̂'` on `γ₁ ± 5×10⁻³` in `[−5.70, −5.31]×10⁻³`. So the true ground state has `|ĝ'| ≥ 3.71×10⁻³`, with fixed sign, on that window.
* With the round-37 bound, `ĝ` has a zero within `2.75×10⁻³` of `γ₁`, which is inside the window.

The pinning claim assumes the ground state is non-increasing on `[0, a]` with `g(0) ≤ 2` (computed: 1.65). `L²` closeness does not control `g(0)`, so this remains an assumption. It also relies on the round-37 named inputs.

At `γ₂` the slope is `~2×10⁻⁴`, below the enclosure error, so it is **not** certified. Going further needs a certified gap at larger `δ`, or a pointwise (not `L²`) closeness bound.

**What stays ours.** None of the following appears in Zhu:
* the edge law and the `2/e` ratio;
* the transition-zone derivation;
* the depth model in item 2;
* the monotone zero flow;
* the Lean pieces (prime-side reduction, the concave Pólya theorem, the saturation reductions).

**What he has that we don't:**
* certified positivity;
* parity and gap theorems;
* the barrier `T₁ = 2πe^{A_L}`;
* the conditional theorem.

## Round 39: a certified gap at `L = 1` (support 2) (`frontier/gap_L1/`, `frontier/certify_gamma1_delta2.py`)

Zhu certified the gap at `L = 0.8`. Here the same method is carried out at `L = 1` (`δ = 2`), in both parity sectors.

**Theorem (computer-assisted).** Let `λ₁, λ₂` be the first two min–max values of `Q(f)/‖f‖²` over real `f` with `supp f ⊆ [−1, 1]`, taken separately in each parity sector. Then:

| sector | `λ₁` | `λ₂` |
|---|---|---|
| even | `5.192×10⁻³⁰ ≤ λ₁ ≤ 6.040×10⁻³⁰` | `≥ 1.885×10⁻²³` |
| odd | `≥ 1.309×10⁻²⁶` | `≥ 1.962×10⁻²⁰` |

Consequences:
* The ground state is simple and even. The odd sector clears it by a factor of at least 2100; the second even value clears it by at least 3×10⁶.
* By Zhu's parity splitting (his Lemma 6.1), `Q(f) ≥ 5.19×10⁻³⁰‖f‖²` for every complex `f` supported in `[−1, 1]`. So Weil's functional is positive on all `g = f ⋆ f̃*` with `supp g ⊆ [−2, 2]`. **Correction (round 40):** positivity at this support is not new. Liu ("Certified Weil positivity beyond the unit window", 14 Sept 2026) certified coercivity `2⁻¹⁵¹` at `L = 1` and `2⁻⁴⁹¹⁶²` at `L = 17/16`. What is new here is the sharp constant (`5.19×10⁻³⁰` against a true value of about `5.9×10⁻³⁰`), the gap `λ₂`, and the parity and simplicity statement.
* The lower bounds are about 12% below Zhu's converged (uncertified) values `5.88×10⁻³⁰` and `2.18×10⁻²³`, as they must be. The upper bound is a ball Rayleigh quotient of `Q` itself (cosine basis, `K = 240`).

**Method.** Zhu's one-stroke reduction (his Theorem 1.1). Before relying on it I rechecked its envelope lemma line by line: Binet's second formula at `5/4 + it/2`, `t ≥ 15/4`.
* `T♯ = 2496 > T₁ = 2187`, so `β* = log(T♯/2π) − 1/T♯ − A₁ = 0.13170`.
* The reduced form `R ≤ Q` is assembled in 1850 Legendre modes per sector.
* Entry errors: per entry `≤ 4.0×10⁻⁶⁰`. The Legendre tail beyond order 3700 gives `ε_D ≤ 6×10⁻²⁷⁹` and coupling `ε_B ≤ 5×10⁻¹³⁴`.

The steps, all in arb ball arithmetic except where noted:
* **Quadrature** (`nodes.py`). 46 Gauss–Legendre panels, 6147 nodes. Each panel's error is bounded by Trefethen's Bernstein-ellipse bound, with `M` from:
  * `|j_n(z)| ≤ e^{|Im z|}`;
  * `|cos(z log n)| ≤ cosh(b log n)`;
  * a ball covering of the ellipse boundary for the digamma part. The poles at `±i(2k+½)` are kept outside.
* **Legendre transforms** (`assemble.py`). `F_n(t) = i^n √(2(2n+1)) j_n(t)`. The two top orders come from the power series with an alternating-tail bound; the rest follow from the downward three-term recurrence. Working precision is up to 4300 bits, because ball radii grow like `2^{1.44t}` on the recurrence. Nodes are carried to 4400 bits for the same reason. `C = Vᵀ diag(h) V` is formed by `arb_mat` products (4 workers, about 4 minutes).
* **Certificate** (`la.py`). This is a Schur-complement inertia count, not a large Cholesky:
  * The block of Legendre orders `≥ 32` has `λ_min ≥ μ = 0.0658`. This is certified by a float64 Cholesky with a Higham `γ_n` residual bound.
  * `X ≈ D⁻¹B` is refined in arb to residual `‖R‖² ≈ 10⁻¹¹³`.
  * Congruence plus Haynsworth: the number of eigenvalues of `M` below `s` equals the number of negative pivots in a 16×16 ball `LDLᵀ` of the Schur complement, whose entries are widened by `‖R‖²/μ`.
  * Bisection on `s` gives the table. The certified bracket for `R` is tight: `λ₁(R) ∈ [5.192, 5.202]×10⁻³⁰` and `λ₂(R) ∈ [1.8854, 1.8875]×10⁻²³`.
  * The lift to the full space is Zhu's two-block bound: `λ_k(Q) ≥ λ_k(R) ≥ min(λ_k(M), β* − ε_D) − ε_B`.
* The `L = 1` runs took `τ = β*/2` for the high-block Cholesky shift. The committed `la.py` takes half the float64 estimate of `λ_min` instead, because the `L = 0.8` block has an eigenvalue below `β*/2`. Both are certified by the same residual bound.
* **Validation** (`validation_L08.txt`). The same code at Zhu's parameters (`L = 0.8`, `T♯ = 200`, `N = 200`) gives:
  * `β* = 0.5134667749`, his value;
  * `λ₁(R₂₀₀) ∈ [1.00, 1.05]×10⁻¹⁷`, consistent with his certified `8.9×10⁻¹⁸`.

**What the result rests on:**
* Zhu's reduction. Its two lemmas are elementary and were rechecked here.
* Trefethen's Gauss error bound (a published theorem, cited from memory).
* The correctness of arb and FLINT, including `legendre_p_root` weights and `acb_digamma` enclosures.
* IEEE float64 for the well-conditioned high block, covered by the `γ_n` bound.

No zeta zeros and no RH are used.

**Use: `γ₁` pinned at `δ = 2` from our own gap** (`certify_gamma1_delta2.py`, with the sharper Davis–Kahan bound `sin²θ ≤ (ρ − λ₁^lo)/(λ₂^lo − λ₁^lo)`):
* `‖φ − g‖ ≤ 3.0×10⁻⁴`, where `φ` is the cosine ground state with `K = 240`, `ρ = 6.039×10⁻³⁰`.
* So `|ĝ' − φ̂'| ≤ 2.45×10⁻⁴`, and `|ĝ'| ≥ 3.81×10⁻³` with fixed sign on `γ₁ ± 5×10⁻³`.
* Hence a zero of `ĝ` lies within `2.83×10⁻³` of `γ₁`.

This still assumes monotonicity with `g(0) ≤ 2` (computed 1.62), plus the round-37 inputs.

`γ₂` is not reached: its slope `~1×10⁻⁴` is below the error. Closing that would need `ρ − λ₁^lo ≲ 10⁻³¹`. But `R` itself already sits 12% below `Q`, so a larger `T♯` or a pointwise closeness bound would be needed.

**Reproduce:**
```
cd frontier/gap_L1
python3 nodes.py
for k in 0 1 2 3; do python3 assemble.py $k 4 [1] & done; wait
python3 la.py bisect x 16 [1]
```
The optional `1` selects the odd sector. `GAPCFG=L08` selects the validation run.

## Round 40: work on (a), convergence of the ground state to `Ξ` (`frontier/xi_conv/`)

`(a)` (`HypConv`, `PrimeSide.lean`) says `ĝ_a(z)/ĝ_a(0) → Ξ(z)/Ξ(0)` locally uniformly as the support grows. Throughout, `a` is the half-width, Zhu's `L`.

**Status first.**
* **Close to a known conjecture.** Connes–Consani–Moscovici (*Zeta Spectral Triples*, arXiv 2511.22755) conjecture the analogous convergence of regularised determinants to `Ξ`. They note that a proof would establish RH.
* **Our own (a) also looks RH-strength.** If RH fails, `λ₁(a) < 0` for all large `a`. The ground state is then driven by the off-line zero, and nothing suggests its transform tends to `Ξ`. This is a heuristic, not a theorem.
* **Where RH enters the natural proof.** Showing that a limit of `ĝ_a/ĝ_a(0)` vanishes at every zeta zero uses `Q = Σ_γ |ĝ(γ)|²`, a sum of squares, which is RH. So (a) is not "pure analysis", which corrects what I said before round 40.

What follows is what could be established.

**1. Theorem A (unconditional).** Let `Φ` be Riemann's kernel (`Ξ = ∫ Φ e^{izu}`, up to a constant) and `Φ_a = Φ·1_{[−a,a]}`. Then
`λ*(a) ≤ Q(Φ_a)/‖Φ_a‖² ≤ S·e₁(a)²/‖Φ_a‖² = exp(−2πe^{2a} + O(a))`.

The terms are:
* `e₁(a) = 2[Φ(a)cosh(a/2) + ∫_a^∞ |Φ'| cosh(u/2)]`;
* `S = 2·(197/196)·B = 0.0464`, where `B = Σ_ρ Re(1/ρ) = 1 + γ_E/2 − ½log 4π`.

The proof takes four lines:
* By the explicit formula, `Q(Φ_a) = Σ_ρ E_a(z_ρ)²`, with `E_a = Ξ − Φ̂_a` (`Ξ` vanishes at every zero, on the line or not).
* `|E_a(z)| ≤ e₁/|z|` on `|Im z| ≤ ½` (integration by parts, `|sin(zu)| ≤ cosh(u/2)`).
* `Σ_ρ 1/γ² ≤ S`, by pairing `ρ` with `1 − ρ̄`.
* No RH is needed.

Values (`thmA_results.jsonl`):

| `a` | `−ln` of bound | Zhu's certified `−ln λ*` | Zhu Theorem 1.3 (assumes RH): `a·e^a` |
|---|---|---|---|
| 1.0 | 29.1 | 66.99 | 2.7 |
| 2.0 | 316.0 | 650.47 | 14.8 |

It has the true double-exponential rate `e^{2a}`, with coefficient `2π` against the conjectured `2π²`. Zhu's RH-conditional Theorem 1.3 reaches only `e^{a}`, and he describes `e^{2a}` as out of reach of his construction. We have not found Theorem A in the literature, but a search is not proof that it is new.

**2. What (a) means, concretely.**
* **Moment identity (exact).** `ĝ_a(z)/ĝ_a(0) = (Ξ(z)/Ξ(0))(1 + κ(a)z² + O(z⁴))` with `κ(a) = (M₂(Φ) − m₂(g_a))/2`. Here `m₂` is the normalised second moment, and `M₂/2 = Σ_{γ>0} 1/γ² = 0.0231050`. Checked numerically: the moment formula gives `5.3194×10⁻³` against a direct fit of `5.3230×10⁻³` at `δ = 1.4`.
* **Probabilistic form.** The ground state is positive in every run (`moments.py`; the minimum is at the edge). So `μ_a = g_a/∫g_a` is a probability density, and (a) becomes a limit theorem: `μ_a → Φ/∫Φ` in distribution, with uniformly bounded exponential moments. This follows from Lévy continuity plus Vitali. It is standard, but not formalised here.
* **Proof skeleton**, with its weak points marked:
  * (L1) `g_a ≥ 0`: observed, not proved.
  * (L2) tightness and exponential moments: plausible.
  * (L3) every limit's transform vanishes at all zeta zeros: **needs RH**, via the sum of squares.
  * (L4) `κ(a) ≥ 0`: observed at every `δ`.
  * (L5) no extra zeros of `ĝ_a` inside fixed discs: the D-route again.
  * Given (L3), the limit is `Ξ·H` with `H` even and of order ≤ 1. (L4) excludes real extra zeros of `H` but not imaginary ones. Excluding those is where (b)-type information enters.

**3. Measurements.**
* **L² convergence.** The angle between `g_a` and `Φ_a` shrinks steadily, like `e^{−2.2a}`: `sin θ` = 0.135, 0.082, 0.052, 0.033, 0.022, 0.014 at `δ` = 1.0, 1.4, 1.8, 2.2, 2.6, 3.0. So the ground state converges to Riemann's kernel in `L²`, but only exponentially, not double-exponentially. It still beats `Φ_a` by a factor of about 2 in `−ln λ`: `Φ_a` is not the ground state, only its limit.
* **The error in (a) is `κ(a)z²` to leading order, and `κ` has a derived law.** The Hadamard tails give `κ = Σ_{γ>T} 1/γ² − Σ_{unpinned w} 1/w² ≈ (log(T/2π) + 1 − 2a)/(2πT)`. At the round-33 edge `T = 4πe^{2a}` this is `κ = (1 + log 2)/(8π²)·e^{−2a}`.
* The prediction was registered at 18:28 UTC, before the `δ = 2.6, 3.0` runs (`predictions_kappa_registered_1828UTC.txt`):

  | `δ` | `κ` measured | `κ` predicted | ratio |
  |---|---|---|---|
  | 1.0 | 8.337e-3 | 7.889e-3 | 1.057 |
  | 1.4 | 5.323e-3 | 5.288e-3 | 1.007 |
  | 1.8 | 3.466e-3 | 3.545e-3 | 0.978 |
  | 2.2 | 2.282e-3 | 2.376e-3 | 0.960 |
  | 2.6 (registered) | 1.513e-3 | 1.593e-3 | 0.950 |
  | 3.0 (registered) | 1.006e-3 | 1.068e-3 | 0.942 |

  The law holds to 6% out of sample, but there is a systematic drift. `κe^{2a}` falls from 0.0227 to 0.0202 and appears to settle near 0.0200, about 7% below `(1+log 2)/(8π²) = 0.0214`. That corresponds to an effective edge near `14.7e^{2a}` rather than `4πe^{2a} = 12.6e^{2a}`, consistent with the transition zone of round 34. So the constant is leading order, not exact.

**What this gives (a).**
* A precise target: `κ(a) → 0`, at rate `e^{−2a}`, with a derived constant.
* An unconditional witness `Φ_a` whose transform satisfies (a) exactly.
* A located obstruction: step (L3) is RH.

It does not give a proof. Since (a) looks RH-strength, it is not the easier half of the chain it was meant to be. The honest summary: (a) and (b) together are a reformulation, and both halves carry RH content.

## Round 41: two tests of (b) suggested by Paper 0 (`frontier/lp_tests/`)

Paper 0's ball slices `(1 − x²)^{d/2}` have Bessel transforms `J_ν(t)/t^ν` with `ν = (d+1)/2`, which have only real zeros. Products of real-rooted transforms are real-rooted. Two tests follow: whether the ground states pass the classical criterion for real-rootedness, and whether they are convolutions of ball slices.

**A. Pólya–Schur / Jensen test** (`jensen_test.py`).
* **The criterion.** Write `ĝ_a(z)/ĝ_a(0) = φ(−z²)` with `φ(w) = Σ γ_j w^j/j!` and `γ_j = j!·μ_{2j}/(2j)!`, where `μ_{2j}` are the normalised moments of `g_a`. If `ĝ_a` is real-rooted, then every Jensen polynomial `Σ_i C(d,i) γ_{n+i} w^i` has only real roots. A non-real root proves a non-real zero of `ĝ_a`.
* **Controls:**
  * `Ξ` itself (moments of Riemann's `Φ`) passes all 364 polynomials (`d ≤ 14`).
  * The positive, decreasing probe `1_{[−1,1]} + 2·1_{[−1/3,1/3]}`, whose transform has non-real zeros, fails 11, from degree 4 on.
* **Ground states** at `δ` = 0.6, 1.0, 1.4, 1.8, 2.2, 2.6, 3.0 pass all 364.
* **The pass carries little information.** A sensitivity test inserted one non-real pair at `±(T + iη)` into the `δ = 1.4` transform (`sens.py`):
  * with `d ≤ 14`, only a pair below the first zero (`T = 8`, `η = 2`) is detected;
  * with 90 moments and `d ≤ 44`, `T = 16` is detected from degree 27 on, and `T = 30` is still missed.

  The criterion's reach grows very slowly with the degree. Counting zeros directly (round 23: all real at `δ = 1–3`) is far stronger evidence. Jensen polynomials are not a useful instrument for (b) here.

**B. Is the ground state a convolution of ball slices?** (`conv_test.py`)
* **The test.** If `g_a = s ⋆ h` with `s = (1 − u²/r²)^{ν−1/2}` on `[−r, r]`, then every zero `j_{ν,k}/r` of `ŝ` is a zero of `ĝ_a`. Compute the real zeros of `ĝ_a` to high precision, then try every radius that puts the first slice zero on one of them, for `ν = 0, ½, …, 10`.
* **δ = 2** (`T_max = 180`): `ĝ` has 55 real zeros, the first six equal to the zeta zeros to 7 digits. No candidate survives the check of its second zero. Any slice factor must have `r < j_{ν,2}/180`, i.e. 3–10% of the half-width `a = 1`.
* **δ = 3** (`T_max = 250`): `ĝ` has 107 real zeros, which equals zeta's count there. No survivors; `r` is at most 1.5–5% of `a = 1.5`.
* **Why this must happen.** Below the dodging edge the zeros of `ĝ` are the zeta zeros. A slice factor would force an almost-arithmetic progression `j_{ν,k}/r` into that set, and zeta zeros contain none. So geometric factors can only live beyond the edge, with support of order `e^{−2a}`. A Gaussian factor is impossible outright, since `g_a` has compact support.
* **Consequence.** The closure of Paper 0's slices under convolution (the "Laguerre–Pólya closure" candidate of round 24) cannot explain (b). The factor that carries the zeta-pinned zeros is not geometric.
