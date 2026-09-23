# Lean pilot: Theorems 1bt and 1ca of `riemann-indistinguishability.md` (b2014d8)

The toolchain is Lean 4.35.0-rc2 (`lean-toolchain`) with Mathlib at the commit in `MATHLIB_REV`. Point `MATHLIB` at a built Mathlib checkout (`lake exe cache get` then `lake build`), or place it at `./mathlib4`.

Re-run with `./build.sh`, which takes about 2 minutes.

- `T1ca.lean` → `Osc.lean` → `Split.lean` import each other through oleans written to `build/`.
- `Zeta.lean` imports `T1bt.lean`, `Split.lean` and `Exterior.lean`; `Roadmap.lean` imports `T1bt.lean` and `Exterior.lean`; `Limit.lean` imports `Roadmap.lean`; `HadamardApply.lean` imports `Hadamard.lean` and `Limit.lean`; `XiBounds.lean` imports `HadamardApply.lean`; `Curvature.lean` imports `XiBounds.lean`; `GroundState.lean` imports `Curvature.lean`; `Existence.lean` imports `GroundState.lean`; `Compactness.lean` imports `Existence.lean`; `GroundStateExists.lean` imports `Compactness.lean`; `Uniqueness.lean` imports `GroundStateExists.lean`; `Positivity.lean` imports `Uniqueness.lean`; `StrictPositivity.lean` imports `Positivity.lean`; `UniquenessQ.lean` imports `StrictPositivity.lean`; `SpectralGap.lean` imports `UniquenessQ.lean`; `FourierGap.lean` imports `SpectralGap.lean`; `ParabolaGap.lean` imports `FourierGap.lean`; `Polya.lean` imports `Roadmap.lean`; `Concave.lean` imports `Polya.lean`; `PrimeSide.lean` imports `Positivity.lean` and `Concave.lean`.

Every file ends with `#print axioms`. All 238 checked theorems depend only on `propext`, `Classical.choice` and `Quot.sound`: there is no `sorry` and no added axiom. The build prints no warnings.

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
