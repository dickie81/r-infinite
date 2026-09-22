# Lean pilot: Theorems 1bt and 1ca of `riemann-indistinguishability.md` (b2014d8)

The toolchain is Lean 4.35.0-rc2 (`lean-toolchain`) with Mathlib at the commit in `MATHLIB_REV`. Point `MATHLIB` at a built Mathlib checkout (`lake exe cache get` then `lake build`), or place it at `./mathlib4`.

Re-run with `./build.sh`, which takes about 85 s.

- `T1bt.lean` and `Exterior.lean` stand alone.
- `T1ca.lean` → `Osc.lean` → `Split.lean` import each other through oleans written to `build/`.

Every file ends with `#print axioms`. All 68 checked theorems depend only on `propext`, `Classical.choice` and `Quot.sound`: there is no `sorry` and no added axiom. The build prints no warnings.

| File | Lines | Content |
|---|---|---|
| `T1bt.lean` | 543 | Theorem 1bt |
| `T1ca.lean` | 1500 | 1ca(ii) |
| `Osc.lean` | 926 | 1ca(iii) |
| `Split.lean` | 305 | 1ca(i), and (i)–(iii) assembled |
| `Exterior.lean` | 677 | 1ca(iv) |

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
- **The zero family's link to Mathlib's `riemannZeta`**: the positive-ordinate subfamily and its local finiteness. T1bt's `zetaZeroFamily` is the starting point.
- **All computed, gated numerics.**
