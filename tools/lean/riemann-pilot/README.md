# Lean pilot: Theorems 1bt and 1ca of `riemann-indistinguishability.md` (b2014d8)

The toolchain is Lean 4.35.0-rc2 (`lean-toolchain`) with Mathlib at the commit in `MATHLIB_REV`. Point `MATHLIB` at a built Mathlib checkout (`lake exe cache get` then `lake build`), or place it at `./mathlib4`.

Re-run with `./build.sh`, which takes about 9 minutes.

- `T1ca.lean` → `Osc.lean` → `Split.lean` import each other through oleans written to `build/`.
- `Zeta.lean` imports `T1bt.lean`, `Split.lean` and `Exterior.lean`; `Roadmap.lean` imports `T1bt.lean` and `Exterior.lean`; `Limit.lean` imports `Roadmap.lean`; `RiemannKernel.lean` imports `Roadmap.lean`; `HadamardApply.lean` imports `Hadamard.lean` and `Limit.lean`; `XiBounds.lean` imports `HadamardApply.lean` and `RiemannKernel.lean`; `Curvature.lean` imports `XiBounds.lean`; `GroundState.lean` imports `Curvature.lean`; `Existence.lean` imports `GroundState.lean`; `Compactness.lean` imports `Existence.lean`; `GroundStateExists.lean` imports `Compactness.lean`; `Uniqueness.lean` imports `GroundStateExists.lean`; `Positivity.lean` imports `Uniqueness.lean`; `StrictPositivity.lean` imports `Positivity.lean`; `UniquenessQ.lean` imports `StrictPositivity.lean`; `FourierGap.lean` imports `UniquenessQ.lean`; `ParabolaGap.lean` imports `FourierGap.lean`; `Polya.lean` imports `Roadmap.lean`; `Concave.lean` imports `Polya.lean`; `PrimeSide.lean` imports `Positivity.lean` and `Concave.lean`; `Saturation.lean` imports only Mathlib; `Unconditional.lean` imports `Concave.lean` and `Saturation.lean`; `ZeroSwap.lean` imports `UniquenessQ.lean`; `HurwitzCross.lean` imports `PrimeSide.lean` and `ZeroSwap.lean`; `SwapRealize.lean` imports `HurwitzCross.lean`; `SimpleCover.lean` imports `SwapRealize.lean` and `ParabolaGap.lean`; `SimpleStructure.lean` imports `SimpleCover.lean`; `GapCriterion.lean` imports `SimpleStructure.lean`; `Commute.lean` imports `GapCriterion.lean`; `DegenerateFlat.lean` imports `Commute.lean`; `StructureD.lean` imports `DegenerateFlat.lean`; `Mollify.lean` imports `StructureD.lean`; `TheoremC.lean` imports `Mollify.lean`; `GapBound.lean` imports `TheoremC.lean`; `CosTrunc.lean` imports `GapBound.lean`; `StripConv.lean` imports `GapBound.lean`; `KernelChain.lean` imports `StripConv.lean`; `ZeroCount.lean` imports `StructureD.lean`; `SixteenPi.lean` imports `Curvature.lean`.

Every file ends with `#print axioms`. All 391 checked theorems depend only on `propext`, `Classical.choice` and `Quot.sound`: there is no `sorry` and no added axiom. The build prints no warnings.

| File | Lines | Content |
|---|---|---|
| `T1bt.lean` | 543 | Theorem 1bt |
| `T1ca.lean` | 1500 | 1ca(ii) |
| `Osc.lean` | 926 | 1ca(iii) |
| `Split.lean` | 305 | 1ca(i), and (i)–(iii) assembled |
| `Exterior.lean` | 677 | 1ca(iv) |
| `Zeta.lean` | 136 | the 1ca zero family, linked to Mathlib's `riemannZeta` |
| `Roadmap.lean` | 352 | §11 item 1: the target stated prime-side, and its reduction to `RiemannHypothesis`; Hurwitz's theorem for open and closed target sets |
| `Limit.lean` | 321 | 1bu(ii)'s convergence to `Ξ` from D, and the chain to `RiemannHypothesis` |
| `Hadamard.lean` | 776 | Hadamard's factorisation in genus zero, proved from Mathlib |
| `HadamardApply.lean` | 198 | Hadamard for even functions; applied to `ĝ` and `Ξ`; the chain to RH |
| `XiBounds.lean` | 378 | `XiGrowth`, proved; the chain to RH with no `Ξ` inputs (`Ξ(0) ≠ 0` now comes from `Φ > 0`) |
| `Curvature.lean` | 443 | **dodging D and real-rootedness alone give RH** (`rh_of_dodging`); the curvature sum rule |
| `GroundState.lean` | 167 | ground states of Weil's form: the lower bound, the finite prime sum, the chain for ground states |
| `Existence.lean` | 494 | existence of the ground state, stage 1: the archimedean energy controls the Fourier tails |
| `Compactness.lean` | 234 | existence, stage 2: bounded-energy probes are precompact in `L²` |
| `GroundStateExists.lean` | 453 | existence, stage 3: **a ground state of Weil's form exists at every support** |
| `Uniqueness.lean` | 391 | the ground-state space; the uniqueness criterion |
| `Positivity.lean` | 538 | the pole-free form `Q₀`: a unique, one-signed ground state |
| `StrictPositivity.lean` | 726 | the ground state of `Q₀` is strictly positive on `[−a, a]` |
| `UniquenessQ.lean` | 144 | the full form `Q`: strict gap `λ₀ < λ₁`, and the sharp uniqueness dichotomy |
| `FourierGap.lean` | 1985 | `λ_⊥ ≥ λ₁ + 1/40` for **every `0 < a ≤ 0.35`** (past the first prime); `Q`'s ground state is unique there; the `Cin` chain in closed form, checked by kernel evaluation |
| `ParabolaGap.lean` | 531 | the parabola trial; `λ_⊥ ≥ λ₁ + 1/50` and a unique ground state for **every `0 < a ≤ 0.36`** |
| `Polya.lean` | 356 | Pólya's theorem: every even probe concave on `(−a, a)` has a real-rooted transform |
| `Concave.lean` | 514 | Pólya's theorem stated for every even, concave `g ≥ 0` directly, with no representation hypothesis |
| `Saturation.lean` | 98 | saturation reduced to an envelope bound: a small value plus a steep slope forces a nearby zero |
| `Unconditional.lean` | 342 | saturation without RH: verified zeros, a counting bound, the decay of `ĝ` for monotone `g` |
| `ZeroSwap.lean` | 231 | the zero-swap lemma: a simple ground state admits no zero `w` with `w²` non-real, given the swap's realisation by probes |
| `HurwitzCross.lean` | 116 | the chain with zeros on `ℝ ∪ iℝ`, and with the zero-swap lemma plugged in |
| `SwapRealize.lean` | 487 | the swap realisation, proved for every probe (no Paley–Wiener); the chain `(a) + eventual simplicity ⇒ RiemannHypothesis` |
| `SimpleCover.lean` | 245 | simplicity: every support `a ≤ 0.36` (proved); monotone covering `λ₁(a₀) < s ≤ λ₂(a₁)` ⇒ simple on `[a₀, a₁]`; every `δ ≤ 2.07` given round 47's certificates |
| `SimpleStructure.lean` | 108 | swap closure of the ground space: an off-cross zero of a ground state yields the Green solution `(∂² + w²)⁻¹g` in the ground space |
| `GapCriterion.lean` | 170 | Euler–Lagrange for `Q`; the pole-overlap identity; interlacing `λ₁(Q) ≤ μ₂(Q₀)`; energy gap ⇒ simple; non-simple ⇒ `λ₁ = μ₂` attained; the Jacobi eigenvector lemma |
| `Commute.lean` | 165 | round 48's Theorem B: Weil's form commutes with `∂²` (cross-correlation, pole, full bilinear form) |
| `DegenerateFlat.lean` | 742 | **degenerate ⇒ edge-flat**: a non-simple ground space contains a nonzero pole-free `w` and its compactly supported Green solution `G w` (`(Gw)'' − Gw/4 = w`); **simple ⇔ no such pair** |
| `StructureD.lean` | 722 | **round 48's Theorem D**: the ground space is finite-dimensional; a Green chain `w, Gw, …, G^{m−1}w` lies in it, is independent and spans it; `offcross_root`, the one swap computation: every off-cross zero of a ground-space transform is a root of its polynomial `P_v`; the top element's transform vanishes only on `ℝ ∪ iℝ`. **The RH chain without simplicity**: (a) for the top-of-chain ground states alone gives `RiemannHypothesis` |
| `Mollify.lean` | 1026 | smoothing inside `[−a, a]`: translation and dilation are continuous in `L²`; box averages contract `L²` and archimedean energy and converge to the identity in both; dilation towards `1` converges in archimedean energy (a Pratt/Scheffé limit lemma) |
| `TheoremC.lean` | 810 | **round 48's Theorem C in `H²` form**: an `H²`-flat ground-space element has `h''` in the ground space; Green solutions are `H²`-flat; **simple ⇔ no nonzero `H²`-flat ground-space element**; the smooth form `simple_not_flat` as a corollary |
| `ZeroCount.lean` | 333 | off-line zeros counted by `dim V`: at most `2⌊(m − 1)/2⌋` off-cross values of `ω²` per ground state (none for `m ≤ 2`); Hurwitz attraction; **under (a) with eventually `dim V ≤ M`, `ζ` has at most `2⌊(M − 1)/2⌋` zeros with `Re s > ½`**; `M ≤ 2` gives RH |
| `SixteenPi.lean` | 1251 | the strip note's §3.4 derivation of `1/(16π)`; **the balayage identity proved (Fubini), so the reduced problem gives `e^{−δ}/(16π)` with no hypothesis**; the wall maximiser `X* = 2`; **the balayage density in closed form, positive at the wall**; `P`, `Q`, `J(X) = (π/(2X))(1 + ln(X/2))`, the wall at `X = 2`, `τ = e^{−δ}/(16π)`; the multiplier's `z²` coefficient is the curvature defect; exact and tolerant D cancel the matched zeros |
| `GapBound.lean` | 443 | **the pole-overlap gap bound** `λ₂ − λ₁ ≥ c₂²(μ₂ − μ₁)/(c₁² + c₂²)` at operator level, hence simplicity from a nonzero overlap `⟨c, ψ₂⟩`; **the Galerkin transfer**: dense truncations with a uniform truncated gap give simplicity |
| `CosTrunc.lean` | 653 | **`TruncDense` for the paper's cosine basis** `span{1_{[−a,a]}cos(kπt/a) : k < K}`: `C²` approximant, its cosine series by Mathlib's Fourier theorem, Hölder tails, energy of a truncated Hölder function; round 60's transfer for this basis with no density hypothesis |
| `StripConv.lean` | 544 | **(a) is needed only on the strip `|{Im z}| < ½`**: RH from strip convergence; strip convergence from `L²` closeness of the ground state to a kernel at rate `o(e^{−a/2}/√a)` (`rh_of_close_top`); the min–max angle bound and `rh_of_relgap`; every moment condition (`k = 2`: `κ → 0`) as a corollary |
| `RiemannKernel.lean` | 901 | **Riemann's kernel formula** `∫ Φ(u)e^{izu}du = Ξ(z)/2` on all of `ℂ`, from Mathlib's theta kernel and completed zeta: termwise Gamma integrals on a half-plane, evenness of `Φ` from the theta functional equation, decay, the identity theorem. **`Φ > 0`, hence `ξ(σ) ≠ 0` for real `σ`**: `Ξ(0) ≠ 0` and `ζ(σ) ≠ 0` on `(0, 1)` |
| `KernelChain.lean` | 41 | Riemann's formula discharges `KernelApprox` (`kernelApprox_RPhi`); RH from `L²` closeness to `Φ` (`rh_of_close_RPhi`) |
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

`pairing_of_matching` *(removed in round 66, no longer needed)* turns any such matching into a pairing whose error is the matched displacement plus the two unmatched sums. `pairing_of_D` is the special case of an exact match.

**The curvature sum rule.** `ghat_sum_rule`: for even integrable `g` with `∫g ≠ 0`, `Σ_τ τ⁻² = ∫u²g / (2∫g)`, summed over the zero pairs of `ĝ`. It is proved by comparing two second-order expansions at small real `x`:

| Lemma | Content |
|---|---|
| `HadamardW.expansion` | `‖f(z)/f(0) − (1 − z²Σw)‖ ≤ (‖z‖²Σ‖w‖)²`, from `‖Π(1 + x) − 1 − Σx‖ ≤ e^S − 1 − S` |
| `ghat_expansion` | `‖ĝ(x) − ∫g + (x²/2)∫u²g‖ ≤ |x|³a³∫|g|`; the odd moment vanishes by evenness, and the rest is Mathlib's `Complex.exp_bound` |
| `ghat_curvature` | real-rooted case: each term `τ⁻²` is a positive real, so `Σ‖τ⁻²‖ = ∫u²g / (2∫g)` |
| `xi_expansion` | `Ξ(z)/Ξ(0) = 1 − z²Σ_jγ_j⁻² + O(‖z‖⁴)`, so the target `Σ_jγ_j⁻²` is `Ξ`'s curvature, `−Ξ″(0)/(2Ξ(0)) = 0.023105` in the paper |

**`rh_of_dodging_and_curvature_final`.** *(Round 66: removed. `rh_of_dodging_final` proves the same conclusion without the curvature hypothesis.)* Roadmap item 1 ⇒ `RiemannHypothesis`, with hypotheses:

- `g_n` even and integrable on `[−a_n, a_n]`, with `∫g_n ≠ 0`;
- `ĝ_n` real-rooted;
- dodging D with `η_n → 0` and `T_D(n) → ∞`;
- the curvature `κ_n = ∫u²g_n / (2∫g_n)` converges to `Re Σ_jγ_j⁻²`.

Compared with round 9:

- The uniform bound `Σ τ⁻² ≤ B` is gone, since a convergent `κ_n` is bounded.
- The tail condition `ε → 0` is gone. It follows from the curvature condition and dodging D, because `ĝ_n`'s unmatched zeros carry curvature `κ_n − Σ_matched ≥ 0`, and that tends to `0`.
- "No other zero of `ĝ_n` below `T_D`" is no longer assumed; it is a consequence in the limit.
- The target is `Re Σ_j γ_j⁻²`, the `z²` coefficient of `Ξ(z)/Ξ(0)`. It is known unconditionally, so no RH content is hidden in it. The proof shows `Re Σ ≤ Σ‖·‖` with equality forced by the hypotheses.

What remains open is unchanged in substance: real-rootedness and dodging D at every support are the wall (§11 items 5–6). The curvature condition is a statement about the second moment of the ground states, with no zero locations in it. *(Corrected in round 65: alone it is, but `rh_of_dodging_and_curvature` works because dodging D and the curvature limit together force `Re Σ v = Σ‖v‖`, which holds only under RH. The pair of hypotheses encodes RH.)* *(Corrected in round 11: this section first said the ground states are "not yet defined in Lean". They are: `Roadmap.lean` defines `weilQ`, `Probe` and `IsGroundState` from Theorem 1bn(i). Round 11 connects them to this chain.)*

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

*(Round 65: superseded by round 20's `a ≤ 0.35` and removed; the helpers still used moved to FourierGap.lean.)*

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

*(Round 66: `hκ` is no longer a hypothesis of `rh_of_groundStates_dodging`. The curvature numbers below and in round 23 remain evidence about the ground states, not about the chain.)*

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

## Round 42: (b) from spectral simplicity, and what the zero flow is really tracking (`frontier/simplicity/`)

**Known result that settles the mechanism.** Connes and van Suijlekom (*Quadratic Forms, Real Zeros and Echoes of the Spectral Action*, arXiv 2511.23257) prove the following for quadratic forms given by a real even distribution on `[−L, L]`, which includes Weil's form. If the lowest spectral value is a simple, isolated eigenvalue with an even eigenfunction `ξ`, then every zero of `ξ̂` is real. Their proof is a continuous Carathéodory–Fejér argument.
* So (b) is a spectral non-degeneracy statement, not a statement about the shape of `g`. That explains why every shape mechanism failed (rounds 24–29, 41).
* It is rigorous at two supports:
  * at `δ = 1.6` from Zhu's Theorem 6.2;
  * at `δ = 2` from round 39 (even `λ₁ ≤ 6.04×10⁻³⁰` against odd `λ₁ ≥ 1.31×10⁻²⁶` and even `λ₂ ≥ 1.885×10⁻²³`).

  At both, the true ground state's transform has only real zeros.

**1. Zero-swap lemma (proved here; a short even-sector variant of Carathéodory–Fejér).** Let `g` be an even ground state on `[−a, a]` that is simple within the even sector. Then every zero `w` of `ĝ` has `w²` real, i.e. `w` is real or purely imaginary.

*Proof.*
1. Suppose `ĝ(w) = 0` with `σ = w² ∉ ℝ`. Set `F₂(z) = ĝ(z)·(z² − σ̄)/(z² − σ)`.
2. `F₂` is entire, even, of exponential type `a`, and `|F₂| = |ĝ|` on `ℝ`, since `t²` is real. So by Paley–Wiener `F₂ = f̂₂` for a complex even `f₂ ∈ L²[−a, a]`.
3. At the pole point `z = i/2`, `z² = −¼` is also real, so `|F₂(i/2)| = |ĝ(i/2)|`.
4. On complex even functions `Q(f) = 2|f̂(i/2)|² + (1/π)∫₀^∞ |f̂|²Φ = Q(Re f) + Q(Im f)`. Hence `Q(f₂) = Q(g)` and `‖f₂‖ = ‖g‖`.
5. Since `Q(u) ≥ λ₁‖u‖²` for every even `u`, `Re f₂` and `Im f₂` are ground states (or zero). By simplicity `f₂ = c·g`, so `(z² − σ̄)/(z² − σ)` is constant, which forces `σ ∈ ℝ`. Contradiction. ∎

The odd sector would not work this way: there the pole enters with the other sign.

**2. The flow picture this gives.** While the even ground state stays simple, its zeros are confined to the cross `ℝ ∪ iℝ`. A zero can leave the real axis only through the origin (`ĝ(0) = ∫g = 0`) or through imaginary infinity. For `g(a) ≠ 0`, `ĝ(iy) ~ g(a)e^{ay}/y`, so a pair enters from infinity only when `g(a)` changes sign. So (b) holds along the whole `δ`-flow if:
* the even ground state is simple for all `δ`;
* `∫g_δ ≠ 0` and `g_δ(a) ≠ 0` for all `δ`;
* the start is real-rooted (concave regime, round 24).

Zero collisions in the flow correspond to eigenvalue crossings at the bottom of the spectrum.

**3. Tested against round 30's "universality" failures** (`jitter_real.py`, `where.py`, `track.py`). With primes jittered by ±1% in frequency or ±10% in weight, the ground states are still simple (gap ratio O(1)–10²). Wherever non-real zeros occur, they are **purely imaginary**, stable from `K = 60` to `K = 90`, and occur only where `g` changes sign. Every one of the 18 cells fits the lemma.

In the tracked cell (seed 1, ±1% frequencies):
* `g(a)` changes sign between `δ = 0.95` and `1.0`;
* one imaginary pair appears at `δ = 1.05`.

That is the predicted entry from imaginary infinity. So round 30's jitter broke the flow's *monotonicity*, not the realness mechanism. The realness failures are exactly the sign changes of `g` at the edge. For `ζ`, `g_δ(a) > 0` at every `δ` tested (`g(a)/g(0)` = 1.6e-3, 2e-11, 1.2e-30 at `δ` = 1, 1.8, 2.6), and `ĝ(0)/‖g‖ ≈ 0.8–0.87`.

**4. A Perron–Frobenius route to simplicity** (`simple_test.py`). Split `Q = Q₀ + 2⟨c, g⟩²`, with `c = cosh(t/2)` (the pole) and `Q₀` = archimedean Dirichlet form − prime shifts.
* **`Q₀` is Perron–Frobenius.** Its off-diagonal kernel is `≤ 0`: the archimedean kernel `e^{u/2}/sinh u > 0` enters with a minus sign, and so do the prime shifts. So `Q₀(|g|) ≤ Q₀(g)` (the Beurling–Deny criterion). The kernel is positive on the whole window, so the semigroup should be positivity-improving, giving a simple, strictly positive ground state. This is a standard argument, but not formalised here.
* **Rank-one step.** If `λ₁(Q) < λ₂(Q₀)`, then `λ₁(Q)` is a root of the secular equation and is simple. This uses `⟨c, φ₁(Q₀)⟩ ≠ 0`, which holds automatically because both are positive.
* **Measured:**

  | `δ` | `λ₁(Q)` | `λ₂(Q)` | `λ₁(Q₀)` | `λ₂(Q₀)` | margin `λ₂(Q₀)/λ₁(Q)` | `φ₁(Q₀)` min/centre |
  |---|---|---|---|---|---|---|
  | 1.0 | 9.4081e-7 | 0.018075 | -1.9874 | 0.011939 | 1.3e+04 | 0.58 |
  | 1.4 | 4.2886e-13 | 8.765e-8 | -2.8671 | 5.6064e-8 | 1.3e+05 | 0.65 |
  | 1.8 | 4.4732e-23 | 7.7004e-17 | -3.8232 | 4.9228e-17 | 1.1e+06 | 0.78 |
  | 2.2 | 2.0513e-38 | 1.5772e-31 | -4.8362 | 1.0091e-31 | 4.9e+06 | 0.85 |
  | 2.6 | 8.2926e-62 | 4.1933e-54 | -5.9636 | 2.6845e-54 | 3.2e+07 | 0.95 |
  | 3.0 | 4.8634e-97 | 1.3171e-88 | -7.2314 | 8.4362e-89 | 1.7e+08 | 0.95 |

* **Findings:**
  * `Q₀`'s ground state is positive and simple at every `δ`, as Perron–Frobenius predicts.
  * `λ₂(Q₀)` tracks `λ₂(Q)`: `λ₂(Q₀) ≈ 0.64·λ₂(Q)`, so `Q`'s second eigenvector is almost orthogonal to the pole.
  * The simplicity margin grows from about `10⁴` to about `3×10⁷` and beyond.
* **What remains.** Simplicity for all `δ` needs `λ₁(Q) < λ₂(Q₀)` for all `δ`. Theorem A's `Φ_a` bound (round 40) is too weak for this: at `a = 1` it gives `e^{−29}`, against `λ₂(Q₀) ≈ e^{−52}`. So it is a per-`δ` certificate question (as in round 39), not yet an asymptotic proof.

**What this changes.**
* (b) is no longer a mystery about shapes. It reduces to:
  * simplicity of the even ground state (an eigenvalue non-crossing statement);
  * two sign conditions, `∫g ≠ 0` and `g(a) ≠ 0`.

  All three look RH-independent in kind, which the jittered cells support: those violate Weil positivity, yet the lemma's conclusion still holds.
* **The zero flow's role.** It is the continuous path along which simplicity and the sign conditions must be maintained. Monotonicity of the zeros is not needed.
* **RH is untouched.** The RH content sits in (a), as round 40 found. A proof of (b) for all `δ` along these lines would reduce the pilot's chain to "(a) ⇒ RH", with (a) carrying everything.

## Round 43: the zero-swap lemma in Lean (ZeroSwap.lean)

Round 42's lemma, formalised. It depends on the standard axioms only, with no `sorry` and no warnings. It is built on the existing ground-state machinery (`groundSpace`, `lam_mul_le`, `isGroundState_iff`, from rounds 14–15).

**Definitions.**
* `SimpleGround a g`: `g` is a ground state, and every element of `groundSpace a` is an a.e. multiple of `g`.
* `SwapRealization a g σ` is the **named analytic input**. It asks for probes `u, v` such that:
  * `û(z) + i·v̂(z) = ĝ(z)·(z² − σ̄)/(z² − σ)` whenever `z² ≠ σ`;
  * `autocorr u + autocorr v = autocorr g` pointwise.

  When `ĝ(w) = 0` and `σ = w²`, this is supplied by Paley–Wiener (the swapped function is entire of type `a` and `L²` on `ℝ`), by evenness, and by Fourier uniqueness for autocorrelations. None of these is in Mathlib; all are standard. Admissibility of `u, v` (the archimedean integral) is part of the input.

**Proved.**

| theorem | statement |
|---|---|
| `exists_real_ghatC_ne` | a normalised probe has `ĝ(t) ≠ 0` at some real `t` (Fourier coefficients on `[−2a, 2a]` are values of `ĝ`, and Parseval) |
| `poleR_swap` | the swap preserves the pole value: `poleR(u)² + poleR(v)² = poleR(g)²`, because `(i/2)² = −¼` is real, so the multiplier has modulus 1 there |
| `zero_swap_false` | **the core.** Under `SimpleGround` and a realised swap with `Im σ ≠ 0`: `Q(u) + Q(v) = Q(g)` and `‖u‖² + ‖v‖² = ‖g‖²`. So `u`, `v` are in `groundSpace` and hence `αg`, `βg`. So the multiplier is the constant `α + iβ` at every real `t` with `ĝ(t) ≠ 0`. Two such `t` with different squares exist (continuity), which forces `σ = σ̄`: a contradiction. |
| `zeros_real_or_imag` | under `SimpleGround`, and the realisation for every zero off the cross, every zero `w` of `ĝ` has `w.re = 0 ∨ w.im = 0` |

**How this fits the chain.** `rh_of_prime_side` needs (a) and `RealRooted`. This round gives the weaker conclusion "real or purely imaginary" from simplicity. Connecting it takes two steps not done here:
* **a Hurwitz variant.** The cross `ℝ ∪ iℝ` is closed, so zeros of the limit `Ξ` lie on it too.
* **`Ξ(iy) ≠ 0` for real `y ≠ 0`.** This is `ξ(σ) ≠ 0` on the real line, i.e. `ζ(σ) ≠ 0` for `0 < σ < 1`. It is classical, but not in Mathlib as far as I know.

With both in place, the chain would read: (a) + simplicity at every large support + `SwapRealization` ⇒ RH. `groundState_unique_or_excited` (UniquenessQ.lean) already reduces simplicity to excluding an excited state of the pole-free form `Q₀` at energy exactly `λ₁`. Round 42's margins `λ₂(Q₀)/λ₁(Q)` = 10⁴–10⁸ measure how far that is from happening. Proving the exclusion for every support is still open.

## Round 44: Hurwitz for closed sets, and the chain through the zero-swap lemma (HurwitzCross.lean)

**Proved** (standard axioms only, no warnings):

| theorem | statement |
|---|---|
| `hurwitz_closed` | if entire `F n → f` locally uniformly, `f ≢ 0`, and every zero of every `F n` lies in a closed set `S`, then every zero of `f` lies in `S`. `hurwitz_real` is the case `S = ℝ`. The proof is the same maximum-modulus argument, with the disc chosen inside `Sᶜ`. |
| `isClosed_crossSet` | `ℝ ∪ iℝ` is closed |
| `rh_of_prime_side_cross` | `rh_of_prime_side` with (b) weakened to "every zero of `ĝ_n` is real or purely imaginary". A zero of `Ξ` on the imaginary axis is a real zero of `ζ` in `(0, 1)`, which the named input excludes. |
| `rh_of_simple_ground_states` | the chain with round 43's zero-swap lemma plugged in |

**`rh_of_simple_ground_states`, stated.** It concludes Mathlib's `RiemannHypothesis` from these hypotheses:
* supports `a n > 0`, with ground states `g n`;
* **(a)** `HypConv`;
* eventually, every ground state is **simple**;
* eventually, `SwapRealization` holds for every zero off the cross (named: Paley–Wiener and Fourier uniqueness);
* `ZetaNoZeroInUnitInterval` (named: `ζ(σ) ≠ 0` for `0 < σ < 1`). This is classical, via `(1 − 2^{1−σ})ζ(σ) = Σ(−1)^{n+1}n^{−σ} > 0`. Mathlib has only `Re s > 1`.

**What is left, and where.**
* **(a)** is the RH-strength core (round 40).
* **Simplicity at every large support** is reduced in `UniquenessQ.lean` (round 15) to excluding one coincidence: an excited state of the pole-free form at energy exactly `λ₁`. It is certified at `δ = 1.6` (Zhu) and `δ = 2` (round 39). The margins measured at `δ = 1–3` are 10⁴–10⁸ (round 42). No proof covers every support.
* **The two named inputs** are classical analysis and carry no RH content.

## Round 45: `ζ(σ) ≠ 0` on `(0, 1)`, proved (ZetaUnitInterval.lean)

*(Round 65: replaced by a short proof from `Φ > 0` in RiemannKernel.lean; ZetaUnitInterval.lean is removed.)*

Round 44's named input `ZetaNoZeroInUnitInterval` is discharged. `ZetaUnitInterval.riemannZeta_ne_zero_of_mem_Ioo` imports only Mathlib, uses the standard axioms only, and builds with no warnings. `HurwitzCross.lean` now proves:
* `zetaNoZeroInUnitInterval`;
* `rh_of_simple_ground_states'`: (a), positive supports, and eventually simple ground states with the swap realised give Mathlib's `RiemannHypothesis`. No assumption about `ζ` remains.

**The proof.** Mathlib defines `ζ` through the FE-pair of the theta kernel `θ(x) = Σ_{n∈ℤ} e^{−πn²x}`: `Λ(s) = P.Λ(s/2)/2` with `P.Λ(t) = ∫₀^∞ x^{t−1} h(x) dx − 1/t − 1/(½ − t)`. Here `h` is Mathlib's `f_modif`: `θ − 1` on `(1, ∞)` and `θ − x^{−½}` on `(0, 1)`.
* **Mellin identification** (`f_modif_eq`, `Lambda0_eq`, `integrable_F`). The Mellin integral is the real integral `∫ x^{t−1}h`. Integrability comes from Mathlib's strong FE-pair `hasMellin`.
* **Comparison integrals** (`integral_G`). For `0 < t < ½`, `1/t + 1/(½ − t) = ∫₀^∞ x^{t−1}m`, with `m = 1` on `(0, 1)` and `m = x^{−½}` on `(1, ∞)`: `integral_rpow` and `integral_Ioi_rpow_of_lt`.
* **Pointwise sign** (`upper_piece`, `lower_piece`). `h ≤ m`, strictly on `(1, ∞)`.
  * On `(1, ∞)` this is `θ − 1 < x^{−½}`.
  * On `(0, 1)`, Mathlib's functional equation gives `θ(x) − x^{−½} = x^{−½}(θ(1/x) − 1)`.

  Both reduce to one bound, `theta_bound`: `√y (θ(y) − 1) < 1` for `y ≥ 1`. It follows from `θ(y) − 1 ≤ 2q/(1 − q)`, `q = e^{−πy}` (termwise, since `n² ≥ |n|`), and from `√y q ≤ e^{(1−π)y} ≤ e^{−2} < 1/7`, with `q < 1/2`.
* **Strictness** (`integral_F_lt`). `integral_pos_iff_support_of_nonneg_ae`; the support contains `(1, ∞)`.

So `Λ(σ)` is a negative real (`completedRiemannZeta_re_neg`), and `ζ(σ) = Λ(σ)/Γ_ℝ(σ) ≠ 0`.

**What the chain now rests on.**
* (a) (`HypConv`), the RH-strength core.
* Eventual simplicity of the ground states. It is reduced in UniquenessQ.lean, and certified at `δ = 1.6` and `2`.
* `SwapRealization`: Paley–Wiener and Fourier uniqueness. This is the one remaining named analytic input, and it carries no RH content.

## Round 46: the swap realisation, proved (SwapRealize.lean)

The last named analytic input, `SwapRealization`, is now a theorem. `swapRealization_of_zero` proves it for **every** probe `g` and every zero `w` of `ĝ` with `w²` non-real. It uses the standard axioms only, and the build prints no warnings. No Paley–Wiener theorem is needed, because the swapped function can be written down explicitly.

**The construction.** Let `σ = w²`. `g` is even, so `ĝ(−w) = ĝ(w) = 0` (`ghatC_neg_of_even`). Let `h` be the Green solution of `h'' + σh = g` started at `−a`:

  `h(x) = ∫_{−a}^{x} sin(w(x − y))/w · g(y) dy = (e^{iwx}P_{−w}(x) − e^{−iwx}P_w(x))/(2iw)`,

where `P_c(x) = ∫_{−a}^{x} g(y)e^{icy} dy`. Put `f₂ = g + (σ̄ − σ)h`, `u = Re f₂` and `v = Im f₂`.

| theorem | statement |
|---|---|
| `hSw_supp` | `h` vanishes for `|x| > a`. For `x ≥ a`, `P_{±w}(x) = ĝ(±w) = 0`. `P_{−c}(−x) = ĝ(c) − P_c(x)` (`Pc_neg`) makes `h` even (`hSw_even`), which covers `x ≤ −a`. |
| `triangle_swap` | `∫_α^β e(x)∫_α^x f(y) dy dx = ∫_α^β f(y)∫_y^β e(x) dx dy`, for continuous `e` and integrable `f` (Fubini on the product with an indicator) |
| `hSw_hat` | `ĥ(z) = −ĝ(z)/(z² − w²)` for `z² ≠ w²`: `triangle_swap`, then `∫_y^a e^{i(z±w)x}dx` in closed form; the boundary terms carry `ĝ(±w) = 0` |
| `swap_hat` | **R1:** `û(z) + iv̂(z) = ĝ(z)(z² − σ̄)/(z² − σ)` |
| `swap_autocorr` | **R2:** `A_u(s) + A_v(s) = A_g(s)` for every `s`. On `[−6a, 6a]` the Fourier coefficients are `ĝ`-values at real points (`cf_eq_ghatC`). There `ĝ_u` and `ĝ_v` are real (`ghatC_im_zero`: even real functions), and the multiplier has modulus 1 (`norm_swapB`). So `|c_n(u)|² + |c_n(v)|² = |c_n(g)|²` (`swap_cf`). Parseval for `g − g(·+s)` (`hasSum_shift'`, which needs only `L²` and the support) gives R2 for `|s| < 3a`. For `|s| > 2a` all three sides vanish (`autocorr_eq_zero_far`). |
| `arch_dom` | `u` and `v` are admissible: `0 ≤ E_u(x) ≤ E_g(x)` pointwise, from R2 and `archIntegrand_nonneg` |
| `swapRealization_of_zero` | `SwapRealization a g (w²)`: `u` and `v` are probes (even, supported in `[−a, a]`, in `L²` since `h` is continuous with compact support, archimedean-integrable), with R1 and R2 |
| `zeros_real_or_imag'` | **every zero of a simple ground state is real or purely imaginary**, with no further input |
| `rh_of_eventually_simple` | `(a) + eventual simplicity ⇒ RiemannHypothesis` |

**`rh_of_eventually_simple`, stated.** It concludes Mathlib's `RiemannHypothesis` from exactly these hypotheses:
* supports `a n > 0`, with `g n` a ground state of Weil's form at support `a n`;
* eventually, `g n` is simple (`SimpleGround`);
* **(a)** `HypConv a g`: the rescaled transforms converge to `Ξ` locally uniformly.

No named analytic input remains, and no hypothesis mentions a zero of `ζ`.

**What this does and does not change.**
* The formal chain is now **RH ⇐ (a) + eventual simplicity**. Both remaining inputs are genuine open problems. (a) is RH-strength (round 40). Simplicity is certified at `δ = 1.6` (Zhu) and `δ = 2` (round 39), and its margins at `δ = 1–3` are 10⁴–10⁸ (round 42); no proof covers every support.
* `zeros_real_or_imag'` is unconditional in the analytic sense: any simple ground state, at any support, has all its transform zeros on `ℝ ∪ iℝ`. This agrees with round 42's numerics, where every non-real zero found was purely imaginary.
* This is weaker than Connes–van Suijlekom (arXiv 2511.23257), who get all zeros real under their simplicity hypothesis. Here, purely imaginary zeros of `ĝ_n` are allowed. They are excluded only in the limit, through Hurwitz and `ζ(σ) ≠ 0` on `(0, 1)`.

## Round 47: simplicity, support by support (SimpleCover.lean, `frontier/simplicity_cover/`)

Round 46 reduced the chain to **RH ⇐ (a) + eventual simplicity**. This round works on simplicity.

**State of the art (checked).** Suzuki (*Weil's quadratic form via the screw function*, arXiv 2606.09096, Thm 1.4) proves the lowest eigenvalue simple, with an even eigenfunction, **for sufficiently small support** (Dirichlet-form positivity improvement plus perturbation in `a`). Simplicity at every support is open. Connes–van Suijlekom assume it.

**1. Monotone covering (proved, SimpleCover.lean).** Enlarging the support enlarges the probe class. So `λ₁(a)` (`lam_antitone`) and every lower bound `λ₂(a) ≥ s` (`Lam2Ge.mono`) are nonincreasing in `a`. Hence:

* `simpleGround_of_lam2`: `λ₁(a) < s ≤ λ₂(a)` ⇒ every ground state at `a` is simple. It Gram–Schmidts a second ground-space direction against `g`, and every unit combination then has `Q = λ₁ < s`.
* `simpleGround_of_cover`: **`λ₁(a₀) < s ≤ λ₂(a₁)` ⇒ simplicity at every `a ∈ [a₀, a₁]`**.
* `simpleGround_of_chain`: finitely many such cells cover an interval.
* `simpleGround_036`: **every support `0 < a ≤ 0.36` has simple ground states**, fully in Lean (ParabolaGap's gap, plus `simpleGround_of_unique`).

So point certificates, which were all that was available before (Zhu at `δ = 1.6`, round 39 at `δ = 2`), now cover intervals.

**2. The certified cells (computer-assisted).** Nodes in `δ = 2a`: `0.72, 1.02, 1.28, 1.50, 1.70, 1.87, 2.02, 2.07`.

| cell `δ` | `λ₁` upper at left | `s` (Lean) | `λ₂(M)` ≥ at right | `L`, `T♯`, `N` | `ε_B` | ratio |
|---|---|---|---|---|---|---|
| `[0.72, 1.02]` | `8.500e-04` | `0.01` | `1.0478e-02` | `51/100`, `120`, `67` | `1e-24` | 12.3 |
| `[1.02, 1.28]` | `5.638e-07` | `6e-06` | `6.4067e-06` | `64/100`, `240`, `137` | `1e-28` | 11.4 |
| `[1.28, 1.50]` | `9.093e-11` | `1e-09` | `1.0555e-09` | `75/100`, `400`, `248` | `4e-38` | 11.6 |
| `[1.50, 1.70]` | `3.741e-15` | `2.7e-14` | `2.7991e-14` | `85/100`, `1000`, `666` | `1e-77` | 7.5 |
| `[1.70, 1.87]` | `4.482e-20` | `4.9e-19` | `4.9193e-19` | `935/1000`, `1000`, `731` | `3e-84` | 11.0 |
| `[1.87, 2.02]` | `2.681e-25` | `3e-24` | `3.3489e-24` | `101/100`, `2496`, `1936` | `4e-200` | 12.5 |
| `[2.02, 2.07]` | `1.097e-30` | `4e-26` | `4.4407e-26` | `1035/1000`, `2496`, `1983` | `2e-204` | 40496.9 |

Full record: `results/cover_certificate.json`; per-node logs in `results/n*/`; reproduce with `run_all.sh`.

* Upper bounds: `weil_prime_gram.certify` (cosine basis, `K = 120`, 400 bits), a ball Rayleigh quotient of `Q` at `δ − 10⁻⁹` (valid at the node by monotonicity).
* Lower bounds: Zhu's one-stroke reduction (arXiv 2608.24827, Thm 1.1, valid for every `L > 0` with `β* > 0`). Round 39's pipeline, generalised to any rational `L`, with `T♯` and `N` per node (`params.py`) and a new `la.py lam2` mode. `λ₂(Q) ≥ s − ε_B`; every `ε_B < 10⁻³⁷` is far below the thresholds.
* Validation: at Zhu's `L = 0.8`, `T♯ = 200`, the generalised code reproduces `β* = 0.5134667749`, `ε_D ≤ 4.6×10⁻²¹²` and `ε_B ≤ 3.9×10⁻¹⁰²`.
* **Bug found and fixed** in the inherited `assemble.py`. `x = L·t` was formed at 400 bits before the working precision was raised. That is exact for `L = 1`, where round 39 ran, so round 39 is unaffected. For other `L`, the Bessel recurrence amplifies the rounding by about `2^{1.44x}`. Ball arithmetic turned this into a failed certificate at `δ = 1.5` (entry radii `~10¹⁹`), not a false one.

`simpleGround_le_1035`: given `Round47Certs` (the fourteen inequalities, as a named hypothesis), **every ground state at every support `0 < δ ≤ 2.07` is simple**. Lean checks the logic; the numerics are the computer-assisted part.

**3. Why this does not reach every support.** Zhu's reduction needs `T♯ > T₁ = 2π·exp(A_δ)`, with `A_δ = Σ_{log n<δ} 2Λ(n)/√n ~ 4e^{δ/2}`. That is doubly exponential in `δ`. The cost grows like `(L·T♯)³`:

| `δ` | 2.0 | 2.2 | 2.5 | 3.0 | 4.0 | 5.0 |
|---|---|---|---|---|---|---|
| `T₁` | 2.2e3 | 7.4e3 | 3.2e4 | 2.8e6 | 2.4e11 | 1.9e19 |

`δ ≈ 2.5` is a heavy computation, and `δ = 3` is out of reach. Cell widths also shrink: `λ₁` and `λ₂` fall super-exponentially, while `log₁₀(λ₂/λ₁)` grows only about linearly, from 2.7 at `δ = 0.7` to 6.6 at `δ = 2.1` (round 42: 8.4 at `δ = 3`). Certification cannot give "every support".

**4. Structural routes, tested.**
* **Exact criterion.** Rank-one interlacing with `Q = Q₀ + 2cc^T` (`c = cosh(t/2)`) and UniquenessQ's dichotomy show that simplicity fails only if `λ₁(Q) = μ₂(Q₀)` and `⟨c, ψ⟩ = 0` for an eigenfunction `ψ` of `Q₀` at `μ₂`. If the second even eigenfunction of `Q₀` has nonzero pole overlap, the secular function has a pole at `μ₂`, and simplicity follows with no quantitative margin. Failure requires two independent real conditions at once (codimension 2), so a one-parameter family generically never meets it. That is a heuristic, not a proof.
* **Nodal/rearrangement route: fails as stated** (`nodal_test.py`). The hoped-for argument: `φ₀` radially decreasing (so `c/φ₀` increasing), and `ψ₂` with one sign change, force `⟨c, ψ₂⟩ ≠ 0`. `ψ₂(Q₀)` does have exactly one sign change at `δ = 1` (`K = 60, 90`). But `φ₀` is **not** monotone. It jumps up at `|u| = log 2 − a`, where the prime shift `log 2` couples the two edge regions. Riesz rearrangement does not apply to the translation kernels `δ_{log n}`. The weaker crossing condition also fails at `δ = 1` (`K = 90`). It needs `c/φ₀` below its value at `ψ₂`'s sign change `r` for `|u| < r`, and above it for `|u| > r`. But `r ≈ 0.218` sits just past the jump at `0.193`, where `c/φ₀ ≈ 0.93`, below the central values of about `1.01`. The overlap `⟨c, ψ₂⟩ = 0.0043` is nonzero, but not for this reason.

**What this round changes.**
* Simplicity is now proved (Lean) for `δ ≤ 0.72`, and certified (computer-assisted, Lean-checked logic) on the **whole interval** `δ ≤ 2.07`. Before, it was known at small `δ` and at two isolated points.
* Simplicity for **every** support remains open. So does "eventual simplicity", which the RH chain needs as `δ → ∞`. No finite certificate reaches it, and the natural structural argument (Perron–Frobenius / rearrangement) is blocked by the pole term and the prime translations.

## Round 48: simplicity at every support, reduced to one edge lemma (SimpleStructure.lean)

The target is simplicity of the even ground state at **every** support, with no further numerical cells. **It is not proved.** This round finds an exact reformulation that holds at every support at once, proves part of it in Lean, and isolates the one missing lemma.

Notation:
* `V` is the ground space (`groundSpace a`), and `V_ℂ` its complexification.
* `B_λ(f, k)` is the bilinear form of `Q − λ₁‖·‖²`, whose kernel on probes is `V`.
* **`D`** ("edge-flat") is the set of even `h` supported in `[−a, a]` with `h ∈ H²(ℝ)` (so `h` and `h'` vanish at `±a`) and `h''` a probe.

**Theorem A (swap closure; Lean, `green_mem_groundSpace`).** Let `g ∈ V` with `ĝ(w) = 0` and `w²` non-real. Then both real parts of the compactly supported Green solution `h = (∂² + w²)⁻¹g` lie in `V` (`ĥ = −ĝ/(z² − w²)`, SwapRealize.lean). The proof: the swapped pair `u, v` satisfies `Q(u) + Q(v) = Q(g)` and `‖u‖² + ‖v‖² = ‖g‖²`, with `Q ≥ λ₁‖·‖²` on each (`swap_pair_mem`); then `Im h = (u − g)/(2 Im σ)` and `Re h = −v/(2 Im σ)`.

**Theorem B (commutation; paper-level).** For `f ∈ H²(ℝ)` supported in `[−a, a]` and `k ∈ C_c^∞(−a, a)`: `B(f'', k) = B(f, k'')`.
* Each translation-invariant piece (norm, archimedean, primes) is a functional of the cross-correlation, and `xcorr(f'', k) = xcorr(f, k'')` by two integrations by parts.
* The pole term: `poleR(f'') = ∫f''e^{−u/2} = ¼·poleR(f)`, and likewise for `k`. This holds because `(i/2)² = −¼` is real, the same fact behind the swap.

**Theorem C (flat ⇒ degenerate; paper-level).** Let `h ∈ V ∩ D` with `h ≠ 0`. Then `h'' ∈ V`, so `dim V ≥ 2`.
* By Theorem B, `B_λ(h'', k) = B_λ(h, k'') = 0` for `k ∈ C_c^∞(−a, a)`.
* By density of `C_c^∞(−a, a)` in the form domain, and continuity of `B_λ(h'', ·)` (Cauchy–Schwarz for the nonnegative `Q_λ`), `Q_λ(h'') = 0`.
* `h''` is not a multiple of `h`, since `h'' = μh` has no compactly supported solution.

**Theorem D (degenerate ⇒ flat: the structure theorem; paper-level).** Let `dim V = m ≥ 2`. Then there is a real even `h`, supported in `[−a, a]`, with `h ∈ H^{2m−2}(ℝ)` and

  `V = span{h, h'', …, h^{(2m−2)}}`,  equivalently `V_ℂ = ĥ·{polynomials of degree ≤ m−1 in z²}`.

Moreover every zero of `ĥ` lies on `ℝ ∪ iℝ`. In particular `h ∈ V ∩ D`.

*Proof.*
1. `V` is finite-dimensional: its unit sphere has bounded energy, hence is precompact (Compactness.lean).
2. Choose off-cross points `z₁, …, z_{m−1}` with distinct non-real squares `σ_j`. Pick `G ∈ V_ℂ`, `G ≠ 0`, with `Ĝ(z_j) = 0`; these are `m − 1` linear conditions.
3. Theorem A, extended complex-linearly, gives the chain `H_k = (∂² + σ_k)⁻¹H_{k−1} ∈ V_ℂ`. The extension works because the complex form `Q(Re f) + Q(Im f) = 2|F(i/2)|² + ∫Φ|F|²` sees only `|F|` on `ℝ` and at `i/2`.
4. The `m` transforms `±Ĝ/∏_{j≤k}(z² − σ_j)` are independent (their polynomial cofactors have distinct degrees). So they span `V_ℂ`, which gives the form stated, with `ĥ` the last one.
5. `ĥ` can be taken real, because `V_ℂ` is closed under `F ↦ F̄(z̄)`.
6. An off-cross zero of `ĥ` would add an `(m+1)`-th independent element. ∎

**Corollary (exact reformulation, every support at once).** *The even ground state at support `2a` is simple if and only if no nonzero ground state is edge-flat (`V ∩ D = {0}`).*

**Why the swap symmetry cannot finish the job.**
* The degenerate structure `V_ℂ = ĥ·P_{m−1}(z²)` is closed under every zero-swap. Swapping at a root `σ` of the polynomial factor returns `ĥ·p/(z² − σ)`, which again lies in `V_ℂ`.
* It is also closed under the commutation with `∂²`.

So a hypothetical degenerate ground space is fully self-consistent under all the Fourier-side symmetries used so far (rounds 43–48). Any proof must use information about the **edge** `±a`.

**The missing lemma (edge non-flatness).** *No nonzero ground state of Weil's form at support `2a` lies in `D`.* This is a Hopf-lemma / boundary-unique-continuation statement for the Euler–Lagrange operator `A₀ + 2|c⟩⟨c| − λ₁`. Here `A₀` is a logarithmic-Laplacian-type operator (kernel `e^{u/2}/sinh u ~ 1/u`) plus attractive prime shifts, and `c = cosh(t/2)`.

Hopf-type lemmas are known for the logarithmic Laplacian, but only for **nonnegative** solutions (e.g. *Hopf's lemma and radial symmetry for the Logarithmic Laplacian problem*, FCAA 2024; *Optimal boundary regularity and a Hopf-type lemma … logarithmic Laplacian*, DCDS 2024). They do not apply here, for two reasons:
1. In a degenerate `V`, the pole-free element `v = h/4 − h''` is orthogonal to `Q₀`'s positive ground state, so it changes sign.
2. For `h`, the equation reads `(A₀ − λ₁)h = −2·poleR(h)·c` with `λ₁ = μ₂(Q₀) > μ₁(Q₀)`. That is above the principal eigenvalue, where the maximum principle fails.

The rank-one pole term is, once again, what breaks Perron–Frobenius.

**Evidence and caution.** The computed ground states are not flat: `g(a) ≠ 0` at every `δ` tested (round 42). But `g(a)/g(0)` falls to about `10⁻³⁰` by `δ = 2.6`, while the simplicity margins grow over the same range. So smallness of the edge value is not the right measure of nearness to degeneracy. A cosine basis also cannot tell a small jump from the logarithmic edge decay expected for such operators.

**What this round changes.**
* Simplicity at every support is **equivalent** to the edge lemma (Theorems C and D).
* The swap-closure step is formal (Lean). The commutation, density, compactness and complex-extension steps are standard analysis, written out above but not formalised.
* The RH chain `rh_of_eventually_simple` now needs, besides (a), only the edge lemma at all large supports.
* **Nothing here proves simplicity.** The edge lemma for sign-changing solutions is open, and I did not find it in the literature.

## Round 49: attempts on the edge lemma (not proved)

The edge lemma of round 48 (*no nonzero ground state is `H²`-flat at `±a`*) is **not proved**. This section records what the attempt established, so that the same routes are not retried blindly.

**1. The edge lemma is not a strengthening. It is simplicity itself.** Theorems C and D make it exactly equivalent to simplicity. Degeneracy is also equivalent to a coincidence of two conditions, using round 42's rank-one interlacing. Here `ψ₂` is the second even eigenfunction of the pole-free form `Q₀` and `c = cosh(t/2)` is the pole:
* (i) `⟨c, ψ₂⟩ = 0`;
* (ii) `λ₁(Q) = μ₂(Q₀)`.

Given (i), `h = (¼ − ∂²)⁻¹ψ₂` is automatically compactly supported and in `H²`: its transform is `ψ̂₂/(z² + ¼)`, entire because `ψ̂₂(±i/2) = ⟨c, ψ₂⟩ = 0`. It is a ground state exactly when (ii) holds. So "edge-flat ground state" is (i) ∧ (ii) in other words.

**2. Local, boundary-only arguments cannot work.**
* Hopf-type lemmas for logarithmic-Laplacian operators need **nonnegative** solutions. A degenerate ground space contains the sign-changing `ψ₂` (orthogonal to `Q₀`'s positive ground state).
* For `h`, the operator sits at `μ₂ > μ₁`, above the principal eigenvalue, where maximum principles fail.
* The degenerate configuration (`V = span{h, h''}`) satisfies every edge matching condition that the `∂²`-commutation produces. Theorem C derives `h'' ∈ V` from exactly those identities, without contradiction.

A proof must be global.

**3. The orthogonality route (exclude (i)) has no robust margin. Exact identity:**

  `2·poleR(g)·⟨c, ψ₂⟩ = (λ₁(Q) − μ₂(Q₀))·⟨g, ψ₂⟩`   for the `Q`-ground state `g`.

Proof: subtract `Q₀`'s eigen-equation for `ψ₂` (tested against `g`) from `Q`'s Euler–Lagrange equation for `g` (tested against `ψ₂`).

So `⟨c, ψ₂⟩` is of the size of the tiny eigenvalue `μ₂`, not of order one. Round 42's data confirm this: `⟨c, ψ₂⟩/μ₂ = 0.361, 0.353, 0.348, 0.345, 0.343` at `δ = 1.4, 1.8, 2.2, 2.6, 3.0`, with `μ₂` falling from `5.6×10⁻⁸` to `8.4×10⁻⁸⁹`. The overlap vanishes super-exponentially in absolute terms. A structural sign argument for `⟨c, ψ₂⟩ ≠ 0` would have to track that `μ₂ > λ₁`, which is condition (ii) again.

**4. The robust margin is the energy gap (ii).** `λ₂(Q)/λ₁(Q)` runs from `10⁴` to `10⁸` over `δ = 1–3` and grows. Proving `λ₁(Q) < μ₂(Q₀)` at every support needs the large-support asymptotics of the two smallest eigenvalues of Weil's form. That is the prolate / semiclassical regime of Connes–Consani–Moscovici, and it is open.

Exact positivity does not help without RH:
* Under RH, `λ₁(Q) > 0` at every support, since `Q(f) = Σ|f̂(γ)|²` and `f̂` cannot vanish at all zeta zeros.
* Using it would make the chain circular.

**Status.** Simplicity is:
* proved for `δ ≤ 0.72` (Lean);
* certified for `δ ≤ 2.07` (round 47);
* equivalent to the edge lemma, or to `λ₁(Q) < μ₂(Q₀)`, at every support.

It is open beyond `δ = 2.07`.

## Round 50: rotating the problem so the ground state is positive (`frontier/simplicity/jacobi_rotation.py`, `gauge_test.py`)

Perron–Frobenius proves simplicity whenever some orthonormal basis makes the form irreducible with nonpositive off-diagonal entries. Such a basis exists **iff** `λ₁` is simple. So the task is to find a *structural* rotation, one that works at every support.

**1. Position space fails at `δ ≈ 0.28`.** For even `g`, `Q(g) = ∫∫g(x)g(y)M(x − y)` with off-diagonal kernel

  `M(u) = 2cosh(u/2) − ½·e^{u/2}/sinh(u) − Σ_n Λ(n)n^{−½}δ(|u| − log n)`.

The pole's `2cosh(u/2)` overtakes the archimedean attraction for `|u| > 0.28`, where `M > 0`. This is why Suzuki's Perron–Frobenius proof (arXiv 2606.09096) holds only at small support.

**2. Frequency bases with sign gauges fail.** In the cosine basis, even after the best `±1` gauge taken from row 0, 256–406 of the 435 off-diagonal pairs have the wrong sign at `δ = 0.2–2` (`gauge_test_results.txt`).

**3. The canonical rotation: the Jacobi basis generated by the pole.** Take the Lanczos basis of the pole-free operator `A₀` seeded at the pole vector `c`. In it:
* `A₀` is tridiagonal with off-diagonals `b_k ≥ 0`;
* `Q = A₀ + 2|c⟩⟨c|` differs only in the `(0, 0)` entry;
* after the gauge `(−1)^k`, `Q` is a Jacobi matrix with nonpositive off-diagonals.

**Theorem (rotation; standard linear algebra).** Let `H_c` be the closed `A₀`-cyclic subspace of `c`.
* `H_c` reduces `Q`, and `Q = A₀` on `H_c^⊥`.
* On `H_c`, `Q` is an irreducible Jacobi matrix. Every eigenvalue there is simple, and the ground state is one-signed in the Jacobi basis.
* `H_c^⊥` is spanned by the `A₀`-eigenvectors orthogonal to `c`, and lies in `[μ₂, ∞)`.

Hence:
* **If `c` is cyclic for `A₀`**, every eigenvalue of `Q` is simple, not just `λ₁`.
* **In general**, `λ₁(Q)` fails to be simple only if an `A₀`-eigenvector orthogonal to `c` sits at exactly `λ₁(Q|H_c)`. This is round 49's pair (i) ∧ (ii).

**Measured** (`K = 60`, 320 bits):

| `δ` | smallest `b_k` | Jacobi ground state | `λ₁(Q)` Jacobi = direct | smallest overlap `\|⟨c, ψ_k⟩\|` | `⟨c, ψ₂⟩` |
|---|---|---|---|---|---|
| 0.5 | 0.056 | all components > 0 | 0.033379 | 1.9e-3 | 9.6e-2 |
| 1.0 | 0.013 | all components > 0 | 9.4081e-7 | 7.2e-5 | 4.4e-3 |
| 1.4 | 0.109 | all components > 0 | 4.4787e-13 | 2.1e-8 | 2.1e-8 |

So the rotation does make the solution positive, and Lanczos never breaks down in the truncation. But the pole's weakest overlap, `2.1×10⁻⁸` at `δ = 1.4`, is exactly the `ψ₂` overlap. Round 49's identity says it has the size of `μ₂`, so it falls super-exponentially with `δ`.

**Status.** The rotation reduces simplicity to **cyclicity of the pole vector for the pole-free Weil operator**, needed only at the one energy `λ₁`. That is the same open condition in a sharper form. The rotation theorem is standard and rigorous; cyclicity at every support is not proved.

## Round 51: the pole overlap `⟨c, ψ₂⟩`, tracked (`frontier/simplicity/overlap_track.py`), not proved nonzero

The request was to prove `⟨c, ψ₂(Q₀)⟩ ≠ 0` at every support. **It is not proved.** What was found:

**1. It is strictly stronger than the energy gap.** Round 49's identity is

  `2·poleR(g)·⟨c, ψ₂⟩ = (λ₁(Q) − μ₂(Q₀))·⟨g, ψ₂⟩`,

and `poleR(g) ≠ 0` (UniquenessQ's dichotomy). So `⟨c, ψ₂⟩ ≠ 0` ⇔ `λ₁ < μ₂` **and** `⟨g, ψ₂⟩ ≠ 0`. Proving it includes proving the gap of round 49, plus a second non-vanishing. Each is one real condition in a one-parameter family, so neither is excluded by counting.

**2. Numerically it never vanishes, and it follows a clean law.** With `ψ₂` sign-fixed by `ψ₂(0) > 0`, tracked at 43 supports `δ = 0.10, 0.15, …, 2.05`:
* `⟨c, ψ₂⟩ < 0` at every support; no sign change.
* The ratio `⟨c, ψ₂⟩/μ₂` runs `−0.018` (`δ = 0.1`), `−0.20` (`0.7`), `−0.365` (`1.0`), `−0.369` (`1.05`, its extreme), `−0.361` (`1.4`), `−0.353` (`1.8`), `−0.350` (`2.05`). It is smooth and slowly drifting.
* Meanwhile `μ₂` falls from `2.5` to `2×10⁻²⁵`.
* The kink near `δ ≈ 0.7` is where `log 2` enters the prime sum.

So the overlap is `≈ −κ(δ)·μ₂` with `κ ≈ 0.35` stable. By the identity, `κ ≈ ⟨g, ψ₂⟩/(2·poleR(g))`: the `Q`-ground state keeps a fixed-size projection on `Q₀`'s second eigenfunction.

**3. What a proof would need.** An asymptotic theorem `κ(δ) → κ_∞ > 0`, meaning the limiting shapes of `g` and `ψ₂` at large support, together with a finite certified range. That is the same large-support spectral asymptotics as in round 49, and it is open. The stability of `κ` is a genuine, unexplained regularity. It is the most concrete target this line of work has produced.

## Round 52: formalising rounds 48–50 (GapCriterion.lean, Commute.lean)

Everything below uses the standard axioms only and builds with no warnings. **Simplicity at every support remains unproved.** This round makes the reductions of rounds 48–50 machine-checked, so the open part is exactly the named statement.

**GapCriterion.lean**

| theorem | statement |
|---|---|
| `euler_lagrange_Q` | a ground state `g` of `Q` satisfies `B₀(g, ψ) + 2ĝ(i/2)ψ̂(i/2) = λ₁⟨g, ψ⟩` for every probe `ψ` |
| `pole_overlap_identity` | round 49's identity: `2ĝ(i/2)ψ̂(i/2) = (λ₁ − μ)⟨g, ψ⟩` for any weak `Q₀`-eigenfunction `ψ` at level `μ` |
| `lam_le_of_perp` | **interlacing**: `λ₁(Q) ≤ Q₀(ψ)` for every normalised probe `ψ ⊥ φ₀`, i.e. `λ₁(Q) ≤ μ₂(Q₀)` |
| `simpleGround_of_gap` | the strict **energy gap** (`EnergyGap a`) ⇒ every ground state is simple |
| `not_simple_gap` | without simplicity, `λ₁(Q)` is attained by `Q₀` on `φ₀^⊥`, so `λ₁(Q) = μ₂(Q₀)` exactly |
| `jacobi_eigvec_unique` | the eigen-solutions of a Jacobi recurrence with nonzero off-diagonals form a line: round 50's rotation fact |

So "simple ⇔ energy gap" is formal, up to one direction's standard attainment argument: the gap implies simplicity, and non-simplicity forces the gap closed.

**Commute.lean** (round 48's Theorems B and C, for `C²`/`C⁴` functions supported in `[−a, a]`)

| theorem | statement |
|---|---|
| `xcorr_deriv2` | `xcorr(f'', k)(u) = xcorr(f, k'')(u)` at every shift (integration by parts twice, `ibp2_line`) |
| `bil0_deriv2` | the pole-free bilinear form commutes with `∂²` |
| `poleR_deriv2` | `poleR(f'') = ¼·poleR(f)`: `(i/2)² = −¼` is real |
| `bilQ_deriv2` | the full bilinear form: `B(f'', k) = B(f, k'')` |
| `deriv2_mem_groundSpace` | an edge-flat ground state `h` has `h''` in the ground space |
| `eq_zero_of_deriv2_eq` | ODE uniqueness (Mathlib's `ODE_solution_unique_univ`): a compactly supported `C²` solution of `h'' = c·h` vanishes |
| `simple_not_flat` | **a simple ground state is never edge-flat** |

**Still not formal:**
* the converse direction of round 48 (degenerate ⇒ an edge-flat element: the complex swap chain and finite-dimensionality);
* the density step that extends `Commute.lean` from smooth to `H²` functions;
* **the open statement itself**: the energy gap, equivalently simplicity, equivalently `⟨c, ψ₂⟩ ≠ 0` with `λ₁ < μ₂`, at every support.

## Round 53: degenerate ⇒ edge-flat, formal (DegenerateFlat.lean)

Round 48's converse direction (Theorem D) is now machine-checked, by a route that needs neither complex swaps nor finite-dimensionality of the ground space. It uses the standard axioms only, with no `sorry` and no warnings.

**The Green operator of the pole.** `G w (x) = ∫_{−a}^{x} 2 sinh((x − y)/2) w(y) dy` solves `h'' − h/4 = w`.
* `hSw_half_eq`: it is round 46's `hSw` at `w = i/2`.
* For a pole-free probe `w` (`ŵ(i/2) = poleR w = 0`), `G w` is even, continuous and supported in `[−a, a]`, with `Ĝw(z) = −ŵ(z)/(z² + ¼)` (`Gpole_hat`).

| theorem | statement |
|---|---|
| `Gpole_lip` | `G w` is Lipschitz on `[−R, R]` with constant `cosh R·∫_{−R}^{R}|w|` (mean value theorem on the `sinh` kernel) |
| `Gpole_autocorr_le`, `Gpole_probe` | its autocorrelation defect is `O(u)`, so the archimedean integral converges: **`G w` is a probe** |
| `triangle_swap_int` | Fubini on a triangle with merely integrable weights |
| `kernel_zero` | a pole-free even probe annihilates `2 sinh((s − c)/2)` |
| `shift_swap`, `xcorr_G_swap` | **`xcorr(G v, m) = xcorr(v, G m)`** at every shift, for pole-free `m` |
| `Gpole_annihilates` | for pole-free `v` in the ground space, `Q − λ₁` pairs `G v` with every pole-free probe to zero (Euler–Lagrange for `v` tested on `G m`) |
| `G_mem_pole_free`, `G_mem_partner` | hence `G v` is in the ground space: directly if `G v` is pole-free; otherwise by a rank-one argument with any ground-space element of nonzero pole value (`Q_λ(Gv) + Q_λ(f) = 0` with both `≥ 0`) |
| `degenerate_flat` | **if a ground state is not simple, the ground space contains a nonzero pole-free `w` and `G w`** |
| `degenerate_flat_fourier` | the same, with `G w` supported in `[−a, a]` and `Ĝw = −ŵ/(z² + ¼)`: `G w` is `H²`-flat at `±a`, and both `G w` and `(G w)'' = w + (G w)/4` are ground states |
| `not_simple_of_green_pair` | conversely, such a pair rules out simplicity: `G w = c·w` would force `ŵ ≡ 0` |
| `simple_iff_no_green_pair` | **simple ⇔ the ground space contains no nonzero pole-free `w` together with `G w`** |

**What this closes, and what it does not.**
* Round 48's reduction is now formal in both directions:
  * `simple_iff_no_green_pair` (the Green/Fourier form of edge-flatness);
  * `simple_not_flat` (Commute.lean, the smooth `C⁴` form).
* `simpleGround_of_gap` and `not_simple_gap` (GapCriterion.lean) make "simple ⇔ strict energy gap" formal.
* **Simplicity itself is not proved.** The open statement is still `EnergyGap a` at every support, equivalently the absence of a Green pair in the ground space.

## Round 54: Theorem D, formal (StructureD.lean)

The rest of round 48's Theorem D is now machine-checked. The file uses the standard axioms only, with no `sorry` and no warnings. It holds at every support `a > 0` and every dimension `m ≥ 1`. For `m = 1` it is the zero-swap statement for a simple ground state.

| theorem | statement |
|---|---|
| `finiteDimensional_groundL2` | **the ground space is finite-dimensional** (its image in `L²`). A Riesz-separated sequence in an infinite-dimensional image would be a bounded-energy family (`archE_le_of_mem`) with no convergent subsequence, against `exists_convergent_subseq` (Compactness.lean) |
| `chain_step` | **one step of a filtration.** The chains of length `j` (`chainSpace`: `f, …, G^j f` in the ground space, all but the last pole-free) form a subspace. One linear condition carries a chain of length `j` to one of length `j + 1`: `(G^j f)^(i/2) = 0` if some ground-space element has a pole (`G_mem_partner`), and `(G^{j+1} f)^(i/2) = 0` if none does (`G_mem_pole_free`) |
| `finrank_map_le_succ`, `finrank_chain` | each step costs at most one dimension, so `dim(chains of length j) ≥ m − j` |
| `exists_long_chain` | **a nonzero `w` with a chain of full length `m − 1`** (`gdim_pos`: `m ≥ 1`, from `exists_groundState`) |
| `Gi_hat` | `(G^i w)^(t) = q(t)^i ŵ(t)`, with `q = −1/(t² + ¼)` |
| `chain_linearIndependent` | **the chain is independent**. A relation `Σ cᵢ G^i w = 0` gives a polynomial in `q` that vanishes on the image of an interval where `ŵ ≠ 0` (`exists_interval_ghat`), so it is zero |
| `chain_span_ae`, `chain_span_hat` | **the chain spans the ground space**, since `m` independent vectors fill an `m`-dimensional space. Every `v` in it is a.e. `Σ cᵢ G^i w`, i.e. `v̂ = P(q)·ŵ` with `deg P < m`. With `ĥ = q^{m−1}ŵ` this is `V_ℂ = ĥ·{polynomials of degree < m in z²}` |
| `chain_top_zeros` | **zeros on the cross.** Suppose `ĥ(ω) = 0` with `ω² ∉ ℝ`, where `h = G^{m−1}w`. Then both parts of the Green solution `(∂² + ω²)⁻¹h` lie in the ground space (`green_mem_groundSpace`). Spanning then forces `P(q)(1 + (¼ + ω²)q) = q^m` for a polynomial `P` of degree `< m` (`no_poly`), which is impossible |
| `theoremD` | the package: chain, independence, spanning, zeros on `ℝ ∪ iℝ` |

**How it differs from the paper proof.**
* The paper chains Green solutions at `m − 1` distinct off-cross points. The formal proof chains the single pole operator `G = (∂² − ¼)⁻¹` instead, with the filtration dimension count replacing the choice of points. It lands on the same structure: one `ĥ`, and the cofactors are the polynomials of degree `< m` in `z²`.
* The Sobolev regularity `h ∈ H^{2m−2}` is not stated as such. Its content is `h = G^{m−1}w` with `w` in the ground space.

**Consequence for the RH chain: simplicity drops out as a separate input.** Round 46's chain needs, at each support, a ground state whose transform vanishes only on `ℝ ∪ iℝ`. Simplicity was used only to supply one, through the zero-swap lemma. Theorem D supplies one at every support unconditionally: the normalised top of the chain.

| theorem | statement |
|---|---|
| `topGS`, `topGS_isGroundState` | `G^{m−1}w`, normalised, is a ground state at every support (it is nonzero because the chain is independent) |
| `topGS_cross` | **every zero of its transform lies on `ℝ ∪ iℝ`**, with no simplicity assumption |
| `rh_of_hypConv_top` | **`HypConv` for the ground states `topGS (a n)` alone gives Mathlib's `RiemannHypothesis`** |
| `hypConv_top_of_simple` | the new hypothesis is implied by the old pair: eventual simplicity plus (a) for any ground states gives (a) for `topGS` |

So the open input is now the single statement "(a) for the top-of-chain ground states". It is no stronger than the previous pair "(a) + eventual simplicity", and it is identical to it wherever the ground space is simple.

**What this does not do.**
* It does not prove simplicity; `EnergyGap a` is still open at large support.
* It does not prove (a). Where the ground space is degenerate, (a) is now asserted for one particular ground state, `ĥ = q^{m−1}ŵ`. Nothing here shows that this choice, rather than some other element of the ground space, converges to `Ξ`.
* The remaining gap is therefore exactly `HypConv a (topGS ∘ a)`: a convergence statement about one explicit family, with no zero of `ζ` in it.

## Round 55: Theorem C, formal in `H²` form (Mollify.lean, TheoremC.lean)

Round 52 formalised Theorem C (flat ⇒ degenerate) only for `C⁴` functions. Round 55 formalises it at the paper's regularity. `D` is now formal as `FlatH2 a h h₁ h₂`: `h' = h₁` everywhere, `h₁` is the primitive from `−a` of an `L²` function `h₂`, `h` and `h₁` vanish outside `[−a, a]`, and `h₂` is a probe. Both files use the standard axioms only, with no `sorry` and no warnings.

**The argument (Green form).**
1. **Flat functions are Green solutions** (`flat_green`). Let `f = h₂ − h/4`. Then `∫_{−a}^x f e^{∓y/2} = e^{∓x/2}(h₁ ± h/2)`, by integrating by parts twice. The first integration uses only that `h₁` is a primitive, through Fubini on a triangle. Hence `poleR f = 0` and `G f = h`.
2. **The cross term vanishes** (`Qlam_green_add`). For every pole-free probe `m`, `Q_λ(G m + r f) = Q_λ(G m) + r² Q_λ(f)`. This is round 53's swap `B(G m, f) = B(m, G f)` plus Euler–Lagrange for `G f = h ∈ V`. With `r = −1`: `Q_λ(f) ≤ Q_λ(G m − f)`.
3. **`Q_λ` is controlled by norm and energy** (`Qlam_le`, `poleR_sq_le`).
4. **Density** (`green_dense`). For every probe `f` and `ε > 0` there is a pole-free probe `m` with `‖G m − f‖² ≤ ε` and `E_arch(G m − f) ≤ ε`. Construction:
   * dilate: `ψ(x) = f(x/l)`, supported in `[−la, la]`;
   * smooth with three box averages `A₃ = Av_δ³ψ`, which fit inside `[−a, a]`;
   * `A₃` is `C²` with `A₃'' = δ⁻²(A₁(x + δ) − 2A₁(x) + A₁(x − δ))`, a probe;
   * so `A₃ = G(A₃'' − A₃/4)` by step 1 (`exists_smooth_green`).
   The analytic input is in Mollify.lean:

| theorem | statement |
|---|---|
| `tendsto_normSq_shift`, `tendsto_normSq_dil` | translation and dilation are continuous in `L²` (by approximation with continuous compactly supported functions) |
| `normSq_avg_le`, `normSq_Av_le`, `normSq_Av_sub_le`, `tendsto_Av` | box averages: `L²` contraction and convergence to the identity (Jensen plus Fubini over the shift) |
| `archIntegrand_Av_le`, `probe_Av`, `tendsto_archE_Av` | box averages contract the archimedean energy density `½‖g − g(· + u)‖²K(u)`, preserve probes, and converge in energy (dominated convergence) |
| `kerK_anti`, `kerK_half_le`, `kerK_far`, `integrableOn_Fsh_half` | the kernel `K(u) = e^{u/2}/sinh u` is decreasing; `F_g(v)K(v/2)` is integrable for a probe |
| `probe_dil`, `tendsto_integral_pratt`, `tendsto_archE_dil` | dilations of probes are probes; dilation converges in energy, via a dominated-convergence lemma with moving dominators (Pratt/Scheffé) |

5. **Conclusion** (`mem_of_green_dense`, `mem_of_green_mem`). `Q_λ(f) = 0`, so `f ∈ V` and `h₂ = f + h/4 ∈ V`.

| theorem | statement |
|---|---|
| `theoremC` | **if `h ∈ V` is `H²`-flat, then `h'' = h₂ ∈ V`** |
| `theoremC_not_simple` | a nonzero such `h` rules out simplicity: `h'' = c·h` a.e. would make `h` solve `h'' = ch` with zero edge data, hence `h = 0` |
| `green_flat` | conversely, for a pole-free probe `w`, `G w` is `H²`-flat, with `(G w)' = ½(e^{x/2}I₁ + e^{−x/2}I₂)` and `(G w)'' = w + G w/4` |
| `simple_iff_no_flat` | **round 48's corollary, formal: the ground state is simple iff no nonzero ground-space element is `H²`-flat at the edges** |

**What this closes, and what it does not.**
* Round 48's structure theory is now machine-checked at the paper's regularity:
  * Theorem A (`green_mem_groundSpace`);
  * Theorem B (Commute.lean);
  * Theorem C (`theoremC`);
  * Theorem D (StructureD.lean);
  * the corollary (`simple_iff_no_flat`).
* The density step in the paper's proof of C ("density of `C_c^∞(−a, a)` in the form domain") is now proved, not cited.
* Simplicity itself is still open, and so is `HypConv` for the top-of-chain ground states, the single remaining input of `rh_of_hypConv_top`.

## Round 56: dimension two already puts the zeros on the cross (DimTwo.lean)

The zero-swap lemma (rounds 43–46) puts every zero of a **simple** ground state on `ℝ ∪ iℝ`. This round extends that to ground spaces of dimension two, using Theorems A and D. It uses the standard axioms only, with no `sorry` and no warnings.

| theorem | statement |
|---|---|
| `zeros_cross_of_dim_le_two` | if `dim V ≤ 2`, every nonzero `v ∈ V` has `v̂(ω) = 0 ⇒ ω² ∈ ℝ` |
| `gdim_le_one_of_simple` | a simple ground state has `dim V ≤ 1` |
| `rh_of_dim_le_two` | **(a) for any family of ground states, with eventually `dim V ≤ 2`, gives Mathlib's `RiemannHypothesis`** |
| `rh_of_eventually_simple'` | round 46's chain as the special case `m = 1` |

**Proof.**
1. Let `ω` be an off-cross zero of `v̂`. By Theorem A (`green_mem_groundSpace`), both parts of `(∂² + ω²)⁻¹v` lie in `V`.
2. By Theorem D's spanning statement (`chain_span_hat`), the transforms of `v` and of those two parts are `P(q)·ŵ` on the real line, with `deg P < m` and `q = −1/(t² + ¼)`.
3. The transform identity of the Green solution then becomes `P(X)(1 + βX) = X·P_v(X)`. Here `β = ¼ + ω²`, and `P_v` is **real** because `v` is real.
4. For `m ≤ 2`, compare coefficients: `P(0) = 0`, `P'(0) = P_v(0) =: A`, and `β·A = P_v'(0) =: B`.
   * If `A ≠ 0`, then `β = B/A` is real, so `ω²` is real. Contradiction.
   * If `A = 0`, then `P_v = 0`, so `v̂ ≡ 0` on the real line. Contradiction.

**What this changes.**
* The RH chain's second input can be weakened from "eventually simple" to "eventually `dim V ≤ 2`". In this form, (a) may be for **any** ground-state family.
* This is an alternative to `rh_of_hypConv_top`, not a strengthening of it. That theorem needs no dimension bound, but asks (a) of one specific family.
* For `m ≥ 3` the argument leaves room for off-cross zeros. They are the roots of the real polynomial `P_v` of degree `≤ m − 1` in `X`, which come in conjugate pairs. Hurwitz with multiplicities would then bound the off-line zeros of `Ξ` by the eventual dimension. That counting version is not formalised.
* Nothing here bounds `dim V`, and (a) is still open.

## Round 57: counting off-line zeros by the dimension of the ground space (HurwitzCount.lean)

Round 56 handled `dim V ≤ 2`. For larger `m`, off-cross zeros can exist, but only finitely many, and Hurwitz carries the count to `ζ`. The file uses the standard axioms only, with no `sorry` and no warnings.

| theorem | statement |
|---|---|
| `offcross_root` | for `v` in the ground space, every off-cross zero `ω` of `v̂` makes `−1/(¼ + ω²)` a root of `P_v`. `P_v` is the fixed real polynomial of degree `< m` with `v̂ = P_v(q)·ŵ` (Theorem D) |
| `card_offcross_le` | a nonzero ground-space element has **at most `m − 1` distinct off-cross values of `ω²`**, because `P_v ≠ 0` and `σ ↦ −1/(¼ + σ)` is injective |
| `hurwitz_attract` | Hurwitz: if entire `F_n → f` locally uniformly and `f(z₀) = 0` with `f ≢ 0`, then eventually `F_n` has a zero within any `ρ > 0` of `z₀`. It follows from `hurwitz_closed` applied to a subsequence |
| `xi_offcross_card_le` | if (a) holds for ground states with eventually `dim V ≤ M`, then **`Ξ` has at most `M − 1` distinct off-cross values of `z²`** |
| `zeta_offline_card_le` | the same hypotheses give: **`ζ` has at most `M − 1` nontrivial zeros with `Re s > ½`** |

**Proof of the limit step.**
* Take distinct off-cross values `σ₁, …, σ_k` of `z²` at zeros of `Ξ`, and let `η` be their mutual separation and their distance from `ℝ`.
* Hurwitz places a zero `ζ_j` of `ĝ_n` near each root, close enough that `|ζ_j² − σ_j| < η/2`.
* The values `ζ_j²` are then off the real axis and pairwise distinct. So `k ≤ dim V_n − 1 ≤ M − 1` by `card_offcross_le`.
* For `ζ`: a nontrivial zero with `Re s > ½` has `Im s ≠ 0`, because `ζ ≠ 0` on `(0, 1)`. So `((s − ½)/i)²` is an off-cross value of `Ξ`. The map `s ↦ ((s − ½)/i)²` is injective on `Re s > ½`.

**What this gives.**
* Eventually `dim V ≤ M` bounds the zeros of `ζ` right of the critical line by `M − 1`. `M ≤ 2` gives at most one such zero. Conjugate symmetry `ζ(s̄) = conj ζ(s)` pairs every zero right of the line with a distinct one, since `Im s ≠ 0`, so one zero is impossible. That recovers RH, as in round 56. The conjugate pairing is not formalised here.
* The bound is about finitely many exceptions. It needs (a) and a uniform dimension bound, and neither is proved.

## Round 58: conjugate parity (HurwitzCount.lean)

Off-cross zeros of a real even transform come in conjugate pairs, and none of their squares is real. So every count in round 57 is even.

| theorem | statement |
|---|---|
| `ghatC_conj` | `ĝ(z̄) = conj ĝ(z)` for real even square-integrable `g` |
| `card_even_of_conj` | a finite set of non-real numbers closed under conjugation has even cardinality |
| `card_offcross_le_even` | a nonzero ground-space element has at most **`2⌊(m − 1)/2⌋`** off-cross values of `ω²` |
| `zeros_cross_of_dim_le_two'` | round 56's `dim V ≤ 2` theorem, re-derived as the case `2⌊(m − 1)/2⌋ = 0` |
| `xi_offcross_card_le`, `zeta_offline_card_le` | now sharpened: under (a) with eventually `dim V ≤ M`, `Ξ` has at most `2⌊(M − 1)/2⌋` off-cross values of `z²`, and `ζ` has at most `2⌊(M − 1)/2⌋` nontrivial zeros with `Re s > ½` |

Reading the bound by `M`:
* `M ≤ 2`: no zeros right of the line (round 56).
* `M ∈ {3, 4}`: at most one conjugate pair `s, s̄`.
* In general, at most `⌊(M − 1)/2⌋` conjugate pairs.

(a) and a uniform dimension bound remain the open inputs. The file uses the standard axioms only, with no `sorry` and no warnings.

## Round 59: consolidation

No mathematical content changes; the pilot is shorter and each fact has one proof. The full build passes with the standard axioms only, no `sorry`, no warnings.

* **One swap computation.** Before, the identity `P(X)(1 + (¼ + ω²)X) = X·P_v(X)` was derived three times: in `chain_top_zeros`, in round 56's `zeros_cross_of_dim_le_two`, and in `offcross_root`. It now lives only in `offcross_root` (StructureD.lean). Both earlier results are short corollaries:
  * `chain_top_zeros`: the top element has `P_h = X^{m−1}`, which has no root at `−1/(¼ + ω²) ≠ 0`;
  * `zeros_cross_of_dim_le_two`: the parity count `2⌊(m − 1)/2⌋` is `0` for `m ≤ 2`.
  `no_poly` is no longer needed.
* **DimTwo.lean + HurwitzCount.lean → ZeroCount.lean** (507 → 355 lines). Theorem names are kept, except that `zeros_cross_of_dim_le_two'` is now `zeros_cross_of_dim_le_two`, with the parity proof.
* **Theorem C in one place.** Round 52's smooth `C⁴` form (`deriv2_mem_groundSpace`, `deriv2_multiple_of_simple`, `simple_not_flat`) is removed from Commute.lean. `simple_not_flat` is now a corollary of the `H²` theorem in TheoremC.lean (`flatH2_of_C2`, `theoremC_not_simple`). It needs only `h ∈ C²` with `h''` a probe; the old hypotheses on the third and fourth derivatives are gone. Commute.lean keeps Theorem B and the ODE step.

Earlier rounds' sections still name the old locations. The theorems they describe are all still proved, at the places listed in this round.

## Round 60: the pole-overlap gap bound and the Galerkin transfer (GapBound.lean)

Round 50's rotation reduced simplicity to the pole overlap `⟨c, ψ₂⟩`. This round proves the resulting gap bound at operator level, and the transfer from truncations. The file uses the standard axioms only, with no `sorry` and no warnings.

**1. The gap bound, with no spectral decomposition.** Let:
* `φ₀` be the ground state of `Q₀`, with `μ₁ = λ₀`;
* `ψ` be a normalised probe `⊥ φ₀` attaining `μ₂ = inf {Q₀(χ)/‖χ‖² : χ ⊥ φ₀}`;
* `c₁ = φ̂₀(i/2)` and `c₂ = ψ̂(i/2)` be the pole overlaps.

| theorem | statement |
|---|---|
| `lam_le_trial` | the trial function `ψ − (c₂/c₁)φ₀` has zero pole term, so `λ₁(c₁² + c₂²) ≤ μ₂c₁² + μ₁c₂²` |
| `lam2Ge_of_Q0` | interlacing in min–max form: every two-dimensional span has a unit vector `⊥ φ₀`, where `Q ≥ Q₀ ≥ μ₂`. So `λ₂(Q) ≥ μ₂` (`Lam2Ge`) |
| `lam2Ge_gap` | **`λ₂(Q) ≥ λ₁(Q) + c₂²(μ₂ − μ₁)/(c₁² + c₂²)`** |
| `simple_of_pole_overlap` | `c₂ ≠ 0` and `μ₂ > μ₁` imply every ground state is simple, with the explicit gap above |

The overlap can come from any minimiser `ψ` on `φ₀^⊥`; `μ₂` itself need not be simple. The bound is sharper than the secular-equation bound `c₂²(λ₁ − μ₁)/c₁²` sketched earlier, because `μ₂ − μ₁ ≥ λ₁ − μ₁`.

**2. The Galerkin transfer.**
* `TruncDense a T`: every probe is a limit, in `L²` plus archimedean energy, of vectors from the truncation spaces `T K`.
* `Lam2GeT a S s`: `λ₂(Q|S) ≥ s` in min–max form. Every span of two vectors of `S` contains a vector with `Q ≥ s‖·‖²`, so no orthonormalisation is needed.

| theorem | statement |
|---|---|
| `Qlam_add_le`, `normSq_add_le_t` | `Q_λ(x + y) ≤ (1 + t)Q_λ(x) + (1 + 1/t)Q_λ(y)`, from Cauchy–Schwarz for the nonnegative `Q_λ`; the same for `‖·‖²` |
| `Qlam_le_d` | `Q_λ ≤ C·(‖·‖² + E_arch)` on probes |
| `lam2Ge_of_trunc` | if `T` is dense and eventually `λ₂(T K) ≥ s_K → s₀`, then `λ₂(Q) ≥ s₀ − ε` for every `ε > 0` |
| `simple_of_trunc_gap` | **if `T` is dense and eventually `λ₂(T K) ≥ λ₁(T K) + γ`, with `γ > 0` uniform, then every ground state is simple** |

**What this gives, and what it does not.**
* Simplicity at a support now follows from either of two checkable statements:
  * a nonzero pole overlap of a second `Q₀`-minimiser, together with `μ₂ > μ₁`;
  * a uniform gap in dense truncations.
* Neither is proved at every support.
* Round 50 measured the overlap `⟨c, ψ₂⟩ ≈ 2×10⁻⁸` at `δ = 1.4`, which falls super-exponentially with `δ`. The gap bound is correspondingly tiny.
* `TruncDense` for the cosine truncations used in rounds 47–50 is a hypothesis here. *(Proved in round 61.)*
* The converse direction (simple ⇒ truncated gaps bounded below) needs attainment of `λ₂` by compactness, and is not formalised.

## Round 61: `TruncDense` for the cosine truncations (CosTrunc.lean)

Round 60's Galerkin transfer assumed `TruncDense`. This round proves it for the basis of the paper's Gram code (`tools/research/weil_prime_gram.py`: `phi_k(t) = cos(omega_k t) 1_{[-a,a]}`, `omega_k = k pi / a`), so the transfer for that basis has no density hypothesis left. The file uses the standard axioms only, with no `sorry` and no warnings.

**The statement.** `cosTrunc a K = span{1_{[−a,a]}·cos(kπt/a) : k < K}`. For every `a > 0` and every probe `f` there are `F_K ∈ cosTrunc a K` with `‖F_K − f‖² + E_arch(F_K − f) → 0` (`cosTrunc_dense`).

**The proof.**

| step | theorems | content |
|---|---|---|
| smooth approximant | `av3_C2`, `av3_dense` (TheoremC.lean) | round 55's density, refactored. `f` is approximated by `h = Av_δ³ψ`, which is `C²`, with `h, h', h''` vanishing outside `[−a, a]`. `green_dense` is now a corollary |
| cosine series | `fco_norm_le`, `fco_deriv`, `cos_series` | two integrations by parts with Mathlib's `fourierCoeffOn_of_hasDerivAt`; the edge terms vanish because `h(±a) = h'(±a) = 0`. So `|ĉ_n| ≤ (a/π)² sup|h''|/n²`. Mathlib's `has_pointwise_sum_fourier_series_of_summable`, on the circle of length `2a` via `AddCircle.liftIco`, gives `h(t) + r = Σ_n d_n cos(nπt/a)` on `[−a, a]`, with `|d_n| ≤ C/n²`. Averaging `t` and `−t` removes the sines |
| tails | `abs_cos_sub_cos_le_sqrt`, `trunc_error` | the error `S_K − h` of the partial sums is `≤ μ_K = Σ_{n≥K}|d_n|` and `½`-Hölder with constant `ν_K = Σ_{n≥K}|d_n|√(2nπ/a)`, from `|cos x − cos y| ≤ √(2|x − y|)`. Since `|d_n|√n = O(n^{−3/2})`, `μ_K, ν_K → 0` |
| energy | `ind_autocorr_le`, `ind_energy` | if `φ² ≤ M` and `(φ(t) − φ(s))² ≤ D|t − s|` on `[−a, a]`, then `f(0) − f(u) ≤ (aD + M)u` for `1_{[−a,a]}φ`. The interior costs `D·u·2a` and the two edge jumps cost `M·2u`. With `u·K(u) ≤ 16e^{−u/4}` this gives `E_arch ≤ (aD + M)E₀` and `‖·‖² ≤ 2aM` |
| basis | `cosB_probe`, `probe_of_mem_cosTrunc`, `cosTrunc_mono`, `cosSum_mem` | each `1_{[−a,a]}cos(kπt/a)` is a probe (by `ind_energy`, despite the jump at `±a`), so is every element of the span; the spaces increase in `K`; the truncated partial sum lies in `cosTrunc a K` |
| diagonal | `truncDense_of_approx`, `cos_approx` | every accuracy is reached in some `cosTrunc a K`; with increasing spaces, `Nat.findGreatest` picks one sequence |
| corollaries | `cosTrunc_dense`, `simple_of_cos_gap`, `lam2Ge_of_cos` | round 60's `simple_of_trunc_gap` and `lam2Ge_of_trunc` for this basis |

**What this gives, and what it does not.**
* The Galerkin transfer is now unconditional for the paper's cosine basis. A uniform gap `λ₂(T_K) ≥ λ₁(T_K) + γ` in these truncations, for all large `K`, implies simplicity at support `2a`. Likewise, truncated `λ₂` lower bounds that converge give `λ₂(Q)` lower bounds.
* The hypothesis that remains is the truncated gap itself, uniformly in `K`. The numerics of rounds 47–50 compute it at finite `K` in high precision. They are not a certificate, and they do not give uniformity in `K`.
* Only density is proved. No rate is given, and no bound relates a finite-`K` eigenvalue to `λ₁(Q)`. A certified gap would need a quantitative version: an explicit `K` and an explicit error.
* Simplicity at every support, (a) `HypConv`, and uniform dimension bounds remain open, as in rounds 54–60.

## Round 62: the second-moment condition, and (a) on the strip (StripConv.lean, `frontier/strip/`)

The target was the second-moment condition `κ(a) → 0`, i.e. `m₂(g_a) → M₂(Φ)`, the first necessary condition for (a).

**1. A direct proof is blocked at the same place as round 40's (L3).**
* By Hadamard (round 18), `m₂/2 = Σ_w 1/w²` over the zeros of `ĝ_a` and `M₂/2 = Σ_γ 1/γ²`. So `κ → 0` is a statement about `ĝ_a`'s zeros tracking ζ's.
* The only handle on `ĝ_a` at the zeta zeros is `Q = Σ_ρ ĝ(γ_ρ)²`, and splitting that sum term by term needs RH.
* The Euler–Lagrange equation says `Σ_ρ ĝ(γ_ρ)φ̂(γ_ρ) = λ₁⟨g, φ⟩` for every `φ` on `[−a, a]`. It fixes the values `ĝ(γ_ρ)` only modulo the annihilator of `PW_a` on the zero set, which is large because the zeros are denser than `PW_a`'s Beurling density. So it does not fix the moments.
* I found no unconditional route to `κ → 0` alone.

**2. What does work: (a) is needed only on the strip `|Im z| < ½`, and there it is an `L²` statement.**

| theorem | statement |
|---|---|
| `hurwitz_closed_on`, `rh_of_strip_cross`, `rh_of_hypConvStrip_top` | Hurwitz on an open set. Every zero of `Ξ` lies in `|Im z| < ½`, so **locally uniform convergence on that strip alone** gives RH for the top-of-chain ground states |
| `norm_ghatC_sub_le` | `|ĝ(z) − φ̂(z)| ≤ √(2a) e^{a|Im z|} ‖g − φ‖` (Cauchy–Schwarz on `[−a, a]`) |
| `tendstoLocallyUniformlyOn_of_close`, `tendstoLocallyUniformlyOn_ratio`, `hypConvStrip_of_close` | if `φ̂_n → cΞ` on the strip (`KernelApprox`) and `√(2a_n) e^{b a_n}‖g_n − φ_n‖ → 0` for every `b < ½`, then (a) holds on the strip |
| `rh_of_close_top` | **RH ⇐ `‖σ_n·topGS(a_n) − φ_n‖ = o(e^{−b a_n}/√a_n)` for every `b < ½`**, with signs `σ_n ≠ 0` |
| `normSq_sub_le_of_gap`, `rh_of_relgap` | min–max: `‖g − φ‖² ≤ 2(Q(φ) − λ₁)/(λ₂ − λ₁)`; hence RH from a relative spectral gap |
| `tendstoLocallyUniformlyOn_iteratedDeriv`, `moments_of_hypConvStrip` | (a) on the strip makes every Taylor coefficient at `0` converge; `k = 2` is `κ → 0` |

* **The one unformalised input is `KernelApprox`.** For `φ_n = Φ·1_{[−a_n, a_n]}` it is Riemann's formula `Ξ(t) = 2∫₀^∞ Φ(u) cos(ut) du` (Titchmarsh §2.16) together with `Φ`'s decay `exp(−πe^{2|u|})`. *(Formalised in round 63.)*
* **The threshold `½` is the half-width of the critical strip.** Round 40 had required convergence on all of `ℂ`, which is much more than the chain uses.

**3. Measurements** (`angle_gap.py`, paper's Gram, 400–1400 bits; `angle_gap_results.jsonl`)

| `δ` | `λ₁` | `λ₂` | `Q(Φ_a)/‖Φ_a‖²` | `sin θ(g_a, Φ_a)` | `sin θ/κ` | `sin θ·√a·e^{a/2}` |
|---|---|---|---|---|---|---|
| 1.0 | 9.4e-7 | 1.8e-2 | 7.0e-4 | 0.1351 | 16.21 | 0.123 |
| 1.4 | 4.3e-13 | 8.8e-8 | 1.3e-6 | 0.0824 | 15.48 | 0.098 |
| 1.8 | 4.5e-23 | 7.7e-17 | 2.4e-11 | 0.0517 | 14.91 | 0.077 |
| 2.2 | 2.1e-38 | 1.6e-31 | 9.1e-19 | 0.0333 | 14.58 | 0.060 |
| 2.6 | 8.3e-62 | 4.2e-54 | 3.4e-30 | 0.0217 | 14.37 | 0.047 |
| 3.0 | 4.9e-97 | 1.3e-88 | 1.4e-47 | 0.0143 | 14.24 | 0.037 |
| 3.4 (registered) | 4.3e-150 | 6.7e-141 | 7.0e-74 | 0.00949 | – | 0.029 |

* **The angle falls like `e^{−2a}`.** The local rate goes `2.47, 2.33, 2.20, 2.13, 2.09, 2.06`, against the threshold `½` that `rh_of_close_top` needs. The criterion's quantity `sin θ·√a·e^{a/2}` falls steadily.
* **The angle and the second moment are one parameter.** The moment identity `ĝ/ĝ(0) ≈ (Ξ/Ξ(0))(1 + κz²)` means `g_a ≈ Φ − κΦ''`, so `sin θ ≈ |κ|·‖(Φ'')^⊥‖/‖Φ‖ = 13.98|κ|` (`phi_pp.py`). The measured ratio falls `16.2 → 14.2` towards `13.98`.
* **Pre-registered test.** The `δ = 3.4` prediction (`prediction_delta3.4_registered.txt`, committed before the run finished) was `sin θ = 9.33×10⁻³`, band `[9.0, 9.7]×10⁻³`. Measured: `9.49×10⁻³`.
* **The gap route fails for `Φ_a`.** `λ₂` is itself double-exponentially small, and far below `Q(Φ_a)`. So `(Q(Φ_a) − λ₁)/(λ₂ − λ₁)` grows from `0.04` to `10⁶⁷`. `rh_of_relgap` is proved, but its hypothesis is false for this trial. A usable trial would need `Q(φ) ≪ λ₂`.

**What this gives, and what it does not.**
* (a) is replaced by a sharper, purely Hilbert-space target: the ground state approaches Riemann's kernel in `L²` faster than `e^{−a/2}/√a`. Numerically the rate is `e^{−2a}`, four times the threshold.
* The second-moment condition follows as the `k = 2` case (`moments_of_hypConvStrip`). Numerically it is the same small parameter as the angle.
* Nothing here proves the angle bound. It is presumably RH-strength: `rh_of_close_top` derives RH from it with no other open input, apart from the classical `KernelApprox` (proved in round 63).
* The measurements stop at `a = 1.7`. The asymptotic rate is inferred, not certified.
* Whether the reduction is in the literature was not checked. Connes–Consani–Moscovici's related conjecture (round 40) is about determinants on all of `ℂ`.

## Round 63: Riemann's kernel formula, formal (RiemannKernel.lean)

Round 62 left one classical input unformalised: `KernelApprox`, Riemann's formula for `Ξ` as the Fourier transform of his kernel. It is now proved from Mathlib's definitions, so **`rh_of_close_RPhi` derives Mathlib's `RiemannHypothesis` from one hypothesis only**: the `L²` closeness of the top-of-chain ground states to `Φ`. The file uses the standard axioms only, with no `sorry` and no warnings.

**The statement** (`RPhiHat_eq`). With `Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u/2} − 3πn²e^{5u/2}) e^{−πn²e^{2u}}` (`RPhi`) and `Ξ(z) = ξ(½ + iz)` built from Mathlib's `completedRiemannZeta₀`:

  `∫_ℝ Φ(u) e^{izu} du = Ξ(z)/2`   for `|Im z| < 1`.

**The proof.**

| step | theorems | content |
|---|---|---|
| Euler's integral on the line | `integral_exp_theta_term`, `integrable_exp_theta_term` | `∫_ℝ e^{αu} e^{−ce^{2u}} du = ½(1/c)^{α/2}Γ(α/2)` for `Re α > 0`, via `x = e^{2u}` (`integral_comp_exp`) and `integral_cpow_mul_exp_neg_mul_Ioi` |
| one term | `phiT_split`, `integral_phiT` | `∫ φ_n(u)e^{izu} du = (s(s−1)/4)(πn²)^{−s/2}Γ(s/2)`, with `s = ½ + iz` and `Im z < −½`; the functional equation of `Γ` combines the two pieces |
| the sum | `summable_integral_norm_phiT`, `integral_RPhi_halfplane` | the norm integrals are `O(n^{−Re s})`, so the sum integrates termwise (`hasSum_integral_of_summable_integral_norm`). Mathlib's `completedZeta_eq_tsum_of_one_lt_re` gives `ξ(s)/2` for `Im z < −½` |
| derivatives | `hasDerivAt_thF`, `hasDerivAt_thF1`, `th_all_le`, `hasDerivAt_thG`, `hasDerivAt_thG1` | termwise differentiation of `Σ e^{u/2 − πn²e^{2u}}` twice, with one majorant `K(n⁴ + 1)e^{−rn}` on `|u| ≤ R` |
| theta kernel | `theta_eq_sum`, `theta_even` | `e^{u/2}θ(e^{2u}) = 2Σ_{n≥0} e^{u/2−πn²e^{2u}} − e^{u/2}` (`hasSum_int_evenKernel`); it is even by `evenKernel_functional_equation` |
| evenness | `thFF1_odd`, `thFF2_even`, `RPhi_eq`, `RPhi_even` | `4Φ = F'' − F/4` with `F` even, so `Φ` is even |
| decay, continuity | `RPhi_decay`, `continuous_RPhi`, `memLp_RPhi` | `|Φ(u)| ≤ Ce^{−2|u|}` |
| continuation | `norm_RPhiHat_sub_le`, `tendstoUniformlyOn_ghatC_RPhi`, `differentiableOn_RPhiHat`, `RPhiHat_eq` | truncations converge uniformly on `|Im z| ≤ 1` (tail `≤ De^{−a/2}`), so `Φ̂` is holomorphic on `|Im z| < 1`. It equals `Ξ/2` on `−1 < Im z < −½`, hence on the whole strip (identity theorem) |
| conclusion | `kernelApprox_RPhi`, `rh_of_close_RPhi` | `KernelApprox a (fun _ => Φ)` for every `a_n → ∞`; RH from closeness to `Φ` |

**What this gives, and what it does not.**
* The reduction of rounds 54–62 now rests on Mathlib's definitions and one hypothesis: `√(2a_n) e^{b a_n}‖σ_n·topGS(a_n) − Φ‖ → 0` for every `b < ½`. That hypothesis is round 62's `L²` angle condition, measured to decay like `e^{−2a}`, with threshold `e^{−a/2}`. It is not proved.
* The formula is proved on `|Im z| < 1`, which is all the chain needs. *(Extended to all of `ℂ` in round 64.)*

## Round 64: Riemann's formula on all of `ℂ` (RiemannKernel.lean)

`RPhiHat_eq` now reads `∫_ℝ Φ(u) e^{izu} du = Ξ(z)/2` for **every** `z ∈ ℂ`. The file uses the standard axioms only, with no `sorry` and no warnings.

| theorem | change |
|---|---|
| `RPhi_decay_gen` | `|Φ(u)| ≤ C_B e^{−B|u|}` for every real `B`, from `X^m e^{−πX/2} ≤ m!(2/π)^m` with `m = ⌈B/2⌉ + 3` and `X = e^{2u}`; evenness for `u < 0`. `RPhi_decay` is the case `B = 2` |
| `norm_RPhi_exp_le`, `integrable_RPhi_exp`, `norm_RPhiHat_sub_le`, `tendstoUniformlyOn_ghatC_RPhi` | now on every strip `|Im z| ≤ M`, using the decay rate `M + 1` |
| `differentiable_RPhiHat` | `Φ̂` is entire: each `z` lies in an open strip where the truncations converge uniformly |
| `RPhiHat_eq` | the identity theorem on `ℂ` (preconnected), from agreement on `Im z < −½` |

`kernelApprox_RPhi` and `rh_of_close_RPhi` are unchanged in statement and now use the entire version.

## Round 65: consolidation (no new hypotheses, fewer lines)

A pass over all 45 files for duplicated proofs, dead code, and shorter routes. No hypothesis was added. Statements changed only where a lemma was generalised: `triangle_swap` and `primeS_eq_two` take weaker hypotheses, and `log_three_gt` has a stronger conclusion. The pilot now has 44 files and 362 `#print axioms` checks (round 65's count), all on the standard axioms, with no `sorry` and no warnings.

**One new result: `Φ > 0`, hence `ξ(σ) ≠ 0` on the real axis (RiemannKernel.lean).** For `u ≥ 0` and `n ≥ 1`, `c_n e^{2u} ≥ π > 3/2`, so each term of Riemann's kernel `φ_n(u) = c_n e^{2u}(2c_n e^{2u} − 3)e^{u/2 − c_n e^{2u}}` is `≥ 0` and the `n = 1` term is `> 0`. Evenness covers `u < 0`. Then `Ξ(it) = 2∫Φ(u)e^{−tu}du > 0` for every real `t`.

| theorem | content |
|---|---|
| `phiT_pos`, `RPhi_pos` | `Φ(u) > 0` for every real `u` |
| `integral_RPhi_exp_pos`, `Xi_I_mul_ne_zero` | `Ξ(it) = 2∫Φ(u)e^{−tu}du > 0` |
| `xi_real_ne_zero` | `ξ(σ) ≠ 0` for every real `σ` |
| `Xi_zero_ne_zero` | the case `σ = ½`. It replaces XiBounds' proof via `‖Λ₀(½)‖ < 4` |
| `riemannZeta_ne_zero_of_mem_Ioo` | `ζ(σ) ≠ 0` on `(0, 1)`: such a zero would be nontrivial, hence a zero of `ξ(σ)`. It replaces ZetaUnitInterval.lean (295 lines), which is deleted |

To make this possible, RiemannKernel.lean now imports only `Roadmap.lean` and builds to an olean before `XiBounds.lean`. `kernelApprox_RPhi` and `rh_of_close_RPhi`, which need `StripConv.lean`, moved unchanged to the new `KernelChain.lean`.

**Shorter routes.**

| theorem | new proof |
|---|---|
| `theoremC_not_simple` (TheoremC) | `f = h'' − h/4` and `G f = h` form a green pair in the ground space, so `not_simple_of_green_pair` applies. `normSq f > 0` because `f = 0` a.e. would make `h = G f = 0`. The ODE lemma `eq_zero_of_deriv2_eq` (Commute) is no longer needed and is deleted |
| `hurwitz_real` (Roadmap) | a corollary of `hurwitz_closed_on`, which moved here from StripConv. `hurwitz_closed` moved here from HurwitzCross, also as a corollary |
| `tail_ok` (FourierGap) | from `modeE_tail_base` and `Cin` monotonicity |
| `ghatC_im_zero` (SwapRealize) | from `ghatC_conj`, which moved here from ZeroCount |

**Duplicates merged.**

| kept | replaces |
|---|---|
| `euler_lagrange_mem` (moved to UniquenessQ) | the bodies of `euler_lagrange_Q` (GapCriterion) and `euler_lagrange_perp` (UniquenessQ), now one-line corollaries |
| `quad_zero` (moved to StrictPositivity) | the inline copy of the same argument in `euler_lagrange0` |
| `lam_le_perp_trial` (new, GapCriterion) | the shared pole-free-trial argument of `lam_le_of_perp` and `lam_le_trial` (GapBound) |
| `cf_shift'`, `hasSum_shift'` (general support `r`, moved to Existence) | FourierGap's copies. `cf_shift` and `hasSum_shift` are corollaries, and SwapRealize's `hasSum_shift_memLp` is deleted |
| `integrable_mul_shift₂` (moved to Existence) | the body of `integrable_mul_shift`, now its diagonal case |
| `memLp_intervalIntegrable` (moved to GroundState) | the body of `Probe.intervalIntegrable` |
| `triangle_swap` over any `RCLike` field, integrable weights (SwapRealize) | the continuous complex version and DegenerateFlat's `triangle_swap_int` |
| `primeS_eq_two`, `log_three_gt` at `2a ≤ 0.72` (FourierGap) | ParabolaGap's primed copies |

**The `Cin` chain in closed form (FourierGap).** On `[mπ/2, (m+1)π/2]` with `c = (2m+1)π/4`, the tangent-line gain is `F_c(β) − F_c(α) = 2/(2m+1) + 8((m+1)s_m − m s_{m+1})/((2m+1)²π) + 16(c_{m+1} − c_m)/((2m+1)²π²)`, where `(s_m, c_m) = (sin, cos)(mπ/2)` comes from the integer recursion `scQ`. The identity is `piece_eq`. `cin_chain` proves `Cin(Nπ/2) ≥ 2.780109 + Σ_{6 ≤ m < N} gain(m)` by induction. `lowP_le` bounds the sum below by a rational, using `0.3183097 < 1/π < 0.31831`. For each of the seven needed `N`, `decide +kernel` checks that rational inequality. This adds no axiom: `decide +kernel` is kernel evaluation, not `native_decide`. `cinH7`, `cinH11`, `cinH18`, `cinH21`, `cinH25`, `cinH30` and `cinH61` keep their statements. They replace `sc14`–`sc122`, `pieceH6`–`pieceH60` and `cinH7`–`cinH61`, about 1150 lines. The exact sums exceed the old step-by-step bounds (by `2·10⁻⁶` at `N = 7` up to `1.4·10⁻⁴` at `N = 61`).

**Removed.**

* **SpectralGap.lean.** Round 19's `a ≤ 1/40` bound (`weilQ0_perp_ge`, `groundState_unique_small`, and the edge-mass and near-field lemmas behind them) is superseded by FourierGap's `a ≤ 0.35`. Nothing used it. Its five live helpers (`kerK_le`, `primeS_eq_zero`, `box_sq`, `archIntegrand_eq_kerK`, `archE_split`) moved to the top of FourierGap.lean, which now imports `UniquenessQ.lean`.
* **Dead lemmas**, used nowhere:
  * `C2Fun.cont0`, `C2Supp.zero_ge` (Commute)
  * `concave_ge_end`, `negRD_nonneg` (Concave)
  * `modeE_nonneg` (FourierGap)
  * `normSq_neg` (GroundStateExists)
  * `Av_add` (Mollify)
  * `gapInf_nonneg` (StrictPositivity)
  * `mem_chainSpace`, `rr_val` (StructureD)
  * `sq_half` (TheoremC)
  * `zetaOrd_ge_of_height` (Zeta)
  * `rh_of_eventually_simple'` (ZeroCount). Its content is `gdim_le_one_of_simple` plus the `M = 1` case of the zero count.

**A correction to round 10.** Round 10 said the curvature condition is "a statement about the second moment of the ground states, with no zero locations in it." Alone, that is true. But `rh_of_dodging_and_curvature` proves RH by showing that dodging D (`hD`) and the curvature limit (`hκ`) **together** force `Re Σ_j v_j ≥ Σ_j ‖v_j‖` (the step `hge` in Curvature.lean). Since `Re Σ v ≤ Σ‖v‖` always, this is equality, and equality holds only if every `v_j` (the `γ_j⁻²` of `Ξ`'s zeros) is a positive real, i.e. every `γ_j` is real. So the pair of hypotheses cannot hold unless RH does. The round-10 text is annotated.

## Round 66: dodging D alone gives RH (Curvature.lean)

Round 65's analysis found that the curvature hypothesis `hκ` of round 10's chain does no work toward RH. It is now removed from the chain. `rh_of_groundStates_dodging` concludes `RiemannHypothesis` from real-rootedness (`hRR`) and dodging D (`hD`, `η_n → 0`, `T_D(n) → ∞`) alone. The new proofs use the standard axioms only, with no `sorry` and no warnings.

| theorem | content |
|---|---|
| `hasProd_eq_zero_of_eq_zero` | a product with a zero factor is zero |
| `HadamardW.nonneg_real` | **real roots give real parameters.** If every zero of `f` is real, every parameter `w_i` of `f(z)/f(0) = ∏(1 − z²w_i)` is a non-negative real: `w_i ≠ 0` puts a zero at `z = w_i^{−1/2}` |
| `rh_of_Xi_params` | **RH from real parameters.** If every parameter `v_j` of a factorisation of `Ξ` is a non-negative real, every zero of `Ξ` is real. The product converges absolutely, so by Mathlib's `tprod_one_add_ne_zero_of_summable` it vanishes only at a vanishing factor, and `z²v_j = 1` with `v_j > 0` forces `z` real |
| `rh_of_dodging` | **dodging D and real-rootedness give RH.** Fix `j` with `v_j ≠ 0`. Since `T_D(n) → ∞`, `v_j` is matched for all large `n`, within `η_n`, to a parameter of the real-rooted `ĝ_n`, which is a non-negative real. The non-negative reals are closed, so `v_j` is one too |
| `rh_of_dodging_final` | the same for the explicit factorisations of `ĝ_n` and `Ξ` (`hadamardW_ghat`, `hadamardW_Xi`) |
| `rh_of_groundStates_dodging` (GroundState) | statement **strengthened**: the hypothesis `hκ` is dropped |

Removed:
* `rh_of_dodging_and_curvature` and `rh_of_dodging_and_curvature_final`, which became special cases with an unused hypothesis;
* `pairing_of_matching` and `tendsto_tsum_above`, which only served them.

The curvature sum rule (`ghat_sum_rule`, `ghat_curvature`, `xi_expansion`) stays as a result about ground states.

**What this means.** The proof never uses the unmatched zeros of `ĝ_n`, the convergence `ĝ_n → Ξ`, or Hurwitz's theorem. It uses only that each zero of `Ξ` is eventually matched to a real zero of some `ĝ_n`, with error tending to `0`. So, given real-rootedness, dodging D says that every zero of `Ξ` is a limit of real numbers, and that is already RH. Round 10's text reads curvature as the extra ingredient that closes the chain. It is not: the chain was closed by D itself. This sharpens round 65's correction and the paper's own verdict that these chains are "presumably a reformulation, not a proof". The open content of roadmap item 1 is (a) dodging and (b) real-rootedness. The Lean chain now shows that proving (a) and (b) for the ground states *is* proving RH, with nothing left to add.

## Round 67: the gap numerics, parametrised (FourierGap.lean, ParabolaGap.lean)

The certified gaps (round 20's `a ≤ 0.3466` and `log 2 ≤ 2a ≤ 0.7`, round 21's `0.35 ≤ a ≤ 0.36`) each carried the same per-mode argument written out five times, with only the constants changing. Four generic lemmas now carry the argument. Each instance keeps its exact statement and is left with one closed numeric check. No certified constant changed. The two files shrink by 223 lines (FourierGap 2103 → 1985, ParabolaGap 636 → 531).

| lemma | replaces |
|---|---|
| `pm_le_of` | the proofs of `pm_le1`–`pm_le5`, `pm_leB1`–`pm_leB5` and `pm_leC1`–`pm_leC5`. From `cval_k ≤ C` and `a ≤ A ≤ ½`, `p_k ≤ (1.05·C + 21β²A⁴/30)/8`. Each stated bound is this value rounded up, checked by `norm_num` |
| `term_mode` | the proofs of `term1`–`term5`, `termB1`–`termB5` and `termC1`–`termC5`. It is `modeE_ge` plus `term_ge` with a generic subtracted prime term `Y ≤ X`. The side condition `ψ̲ ≤ τ` now needs only `err(a) ≥ 0` (`errK_nonneg`): every `C_v + a_max·D ≤ τ`, so the old lower bounds on `a` and `err(a)` were not needed |
| `tail_branch` | the six-way and four-way case splits of `tailC_pos` and `tailB_pos`: one `Cin` value at `Mπ/2` and a bound `D_n ≤ B` give one branch. The tightest branch is `tailC_pos` at `n ≤ 6`: `2.7011 ≥ 2.7` |
| `sum_lowS_even` | the three unrolled 11-term expansions of `Σ_{|n| ≤ 5}` in the gap assemblies |

**On kernel evaluation.** Round 65's `decide +kernel` applied because the `Cin` chain reduces to closed rational sums. These files' numerics do not: they are inequalities in a real parameter `a` with `π`, `log 2` and `√2`. The rational leftovers after parametrising are single `norm_num` or `linarith` steps, so kernel evaluation would add cast plumbing and no reduction. The reduction here comes from parametrising.

## Round 68: is Riemann's kernel a near-ground-state? (numerical, `frontier/nullvec/`)

After round 66, the chain's one open input is `HypConvStrip` for the top ground states: their transforms converge to `Ξ` on the strip. The proved lemma `rh_of_relgap` offers an energy route to it: RH follows if `R_n = (Q(φ_n) − λ₁)/(λ₂ − λ₁)` tends to `0` faster than `a_n⁻¹e^{−2ba_n}` for every `b < ½`, where `φ_n` is the normalised truncation of Riemann's `Φ` to `[−a_n, a_n]`. The idea behind it: `Φ̂ = Ξ/2` vanishes at every zeta zero, so by the explicit formula `Φ` should be a zero-energy vector of Weil's form. This round tests that numerically.

**Method** (`nullvec.py`). Weil's Gram in the cosine basis comes from `tools/research/weil_prime_gram.py`, unconditional: arithmetic side only, arb balls. `Φ`'s cosine coefficients use 9216-point Gauss–Legendre on 96 panels. The outputs are the enclosure of `Q(φ_a)/‖φ_a‖²`, the two lowest generalised eigenvalues, `R`, and `sin²θ`, where `θ` is the angle between `φ_a` and the ground state (the quantity in `rh_of_close_top`). The results are stable in `K`: at `δ = 1.4`, `K = 120` and `160` give `R = 14.76` and `14.81`; at `δ = 2.0`, `K = 120` and `180` give `4.8e8` and `5.1e8`. `λ₁` reproduces round 23 (`6.3e-30` at `δ = 2`, `4.3e-97` at `δ = 3`). Data: `frontier/nullvec/results.jsonl`.

| `δ` | `K` | `λ₁` | `λ₂` | `Q(φ_a)` | `Q(Φ1_a)/Φ(a)²` | `R` | `sin²θ` | local rate of `sin²θ` in `a` |
|---|---|---|---|---|---|---|---|---|
| 0.7 | 120 | 1.19e-3 | 0.649 | 2.42e-2 | 0.11 | 0.0355 | 2.78e-2 | |
| 1.0 | 120 | 9.35e-7 | 1.80e-2 | 7.04e-4 | 0.06 | 0.039 | 1.83e-2 | 2.80 |
| 1.2 | 120 | 1.61e-9 | 1.03e-4 | 5.52e-5 | 0.08 | 0.535 | 1.10e-2 | 5.02 |
| 1.4 | 120 | 4.22e-13 | 8.68e-8 | 1.28e-6 | 0.07 | 14.8 | 6.79e-3 | 4.87 |
| 1.6 | 120 | 1.71e-17 | 8.55e-12 | 8.86e-9 | 0.05 | 1.04e3 | 4.21e-3 | 4.77 |
| 1.8 | 120 | 4.47e-23 | 7.70e-17 | 2.38e-11 | 0.06 | 3.09e5 | 2.67e-3 | 4.56 |
| 2.0 | 120 | 6.44e-30 | 2.42e-23 | 1.17e-14 | 0.05 | 4.83e8 | 1.71e-3 | 4.44 |
| 2.2 | 120 | 2.17e-38 | 1.61e-31 | 9.08e-19 | 0.04 | 5.64e12 | 1.11e-3 | 4.37 |
| 2.4 | 220 | 7.21e-49 | 1.36e-41 | 6.98e-24 | 0.04 | 5.13e17 | 7.19e-4 | 4.32 |
| 2.6 | 280 | 7.94e-62 | 4.00e-54 | 3.34e-30 | 0.03 | 8.36e23 | 4.72e-4 | 4.20 |
| 2.8 | 340 | 1.26e-77 | 1.42e-69 | 5.03e-38 | 0.03 | 3.54e31 | 3.10e-4 | 4.21 |
| 3.0 | 400 | 4.27e-97 | 1.15e-88 | 1.33e-47 | 0.03 | 1.16e41 | 2.05e-4 | 4.14 |

**Findings.**

1. **`Φ` behaves as a null vector of Weil's form.** The energy of its truncation is the truncation defect and nothing more: `Q(Φ1_{[−a,a]}) ≈ (0.03–0.11)·Φ(a)²`, down to `10⁻⁴⁷` at `δ = 3`, even though the individual terms of `Q` are of order `1`. This is computed from the arithmetic side alone, so it is unconditional numerical evidence for `Q(Φ) = 0`. That is what the explicit formula predicts, because `Φ̂ = Ξ/2` vanishes at every zero, RH or not. Not proved: the explicit formula for `Φ` is not formalised.
2. **The energy route is dead.** `R` grows from `0.04` to `10⁴¹`, and faster than exponentially in `e^δ`: `ln R / e^δ` is `2.7` at `δ = 2` and `4.7` at `δ = 3`. The reason is that `λ₂` falls faster than the truncation defect: `ln λ₂ / e^δ` goes from `−7.0` at `δ = 2` to `−10.1` at `δ = 3`, against about `−2π ≈ −6.3` for `Φ(a)²`. The spectral gap collapses faster than any truncation of `Φ` can approach the ground energy. `rh_of_relgap` stays a correct theorem, but it cannot be applied along `a_n → ∞`, as far as these data reach and on this trend.
3. **The L² route survives.** `sin²θ` falls steadily, from `2.8e-2` to `2.1e-4`. Its local decay rate in `a` is `4.1–5.0`, and `rh_of_close_top` needs a rate above `1`. The rate is drifting down slowly (about `0.5` per unit `a` over `δ ∈ [2, 3]`). If that drift stays linear it would cross `1` only near `δ ≈ 14`. If it levels off, as the last three steps suggest (`4.20, 4.21, 4.14`), closeness holds with room to spare. The data cannot tell these apart.
4. **The two measures disagree, and that explains finding 2.** `R ≥ sin²θ` always holds. At `δ = 3`, `R = 10⁴¹` while `sin²θ = 2·10⁻⁴`. So `φ_a` differs from the ground state by a piece that is tiny in `L²` but carries enormous energy: the edge defect of the truncation, which lives on the high modes. Variational (energy and gap) arguments cannot see this kind of closeness.

**What this means for the chain.** The one open input can only be reached through `L²` closeness (`rh_of_close_RPhi`). Its proof would need a structural reason why the minimiser tracks the null vector `Φ` away from the edges, not a spectral-gap estimate. The observed rate, `sin θ ~ e^{−2.1a}`, has a large margin over the needed `e^{−a/2}`. It is inferred from supports up to `δ = 3` and is not certified.

## Round 69: the ground state is Φ plus a vanishing Φ″ correction (numerical, `frontier/nullvec/`)

**Faster pipeline** (`nullvec_fast.py`). Cosine coefficients in arb via the Chebyshev recurrence, and inverse iteration for `λ₁`, `λ₂` and the ground vector instead of a full eigensolve. It reproduces `nullvec.py` digit for digit at `δ = 2.0` and `3.0`, 20–30× faster. Data: `results_fast.jsonl`.

**The angle to `Φ`, pushed to `δ = 4.5`.** sin²θ is stable in `K` to about 2·10⁻⁴ relative at the two sizes tested.

| `δ` | `K` | `λ₁` | `R` | `sin²θ` | local rate in `a` | `sin²θ·e^{2δ}` |
|---|---|---|---|---|---|---|
| 3.0 | 400 | 4.27e-97 | 1.2e41 | 2.049e-4 | 4.14 | 0.0827 |
| 3.5 | 550 / 700 | 3.3e-167 | 3.3e75 | 7.340e-5 | 4.11 | 0.0805 |
| 4.0 | 700 / 900 | 2.2e-283 | 1.1e133 | 2.659e-5 | 4.06 | 0.0793 |
| 4.5 | 900 | 1.9e-475 | 2.5e228 | 9.688e-6 | 4.04 | 0.0785 |

Over `δ ∈ [2, 4.5]`, `sin²θ·e^{2δ}` runs `0.093, 0.090, 0.087, 0.086, 0.084, 0.083, 0.081, 0.079, 0.0785`, with shrinking steps. So **`sin²θ ≈ C·e^{−4a}` with `C → ≈ 0.077`**. The local rate levels off near 4, four times the rate of 1 that `rh_of_close_top` needs.

**The deviation is `Φ″`** (`defect_fit.py`). The unit component of the ground state orthogonal to `Φ` has a fixed profile, the same at `δ = 2` and `3`. It is positive at `t = 0`, crosses zero near `0.17`, is negative around `0.3–0.5`, and vanishes by `0.9`. So it lives where `Φ` lives, not at the edges. Gram–Schmidt against `Φ, Φ″, Φ⁗, Φ⁽⁶⁾`:

| `δ` | `sin²θ` | share of the deviation along `Φ″` | share within `Φ″, Φ⁗, Φ⁽⁶⁾` | `sin²` outside `span{Φ, …, Φ⁽⁶⁾}` |
|---|---|---|---|---|
| 1.0 | 1.8e-2 | 0.99480 | 0.9999919 | 1.5e-7 |
| 2.0 | 1.7e-3 | 0.99802 | 0.99999996 | 6.7e-11 |
| 3.0 | 2.0e-4 | 0.99976 | 0.99999999994 | 1.2e-14 |

**The coefficients** (`beta_fit.py`, least squares `g ≈ c₀(Φ + βΦ″ + γΦ⁗)`). So `ĝ ≈ c₀(Ξ/2)(1 − βz² + γz⁴)`.

| `δ` | `β` | `β·e^{δ}` | `γ` | `γ/(β²/2)` |
|---|---|---|---|---|
| 1.0 | −7.66e-3 | −0.02082 | 5.64e-5 | 1.92 |
| 1.5 | −4.65e-3 | −0.02085 | 1.44e-5 | 1.33 |
| 2.0 | −2.79e-3 | −0.02064 | 4.52e-6 | 1.16 |
| 2.5 | −1.67e-3 | −0.02037 | 1.52e-6 | 1.09 |
| 3.0 | −1.00e-3 | −0.02018 | 5.30e-7 | 1.05 |

**Findings.**

1. **The ground state is `Φ + βΦ″ + O(β²)`, with `β ≈ −0.020·e^{−δ}`.** The part outside the span of `Φ`'s even derivatives is extremely small: `sin² ≈ 10⁻¹⁴` at `δ = 3`, falling much faster than the deviation itself.
2. **To second order the multiplier is Gaussian.** `γ/(β²/2) → 1`, so `1 − βz² + γz⁴ ≈ e^{τz²}` with `τ = −β ≈ 0.020·e^{−δ}`. Conjecture: for `|z| ≪ τ^{−1/2}`, `ĝ_a(z) ≈ c·Ξ(z)·e^{τ_a z²}`. That multiplier has no zeros, which fits the observed dodging (round 23: no zeros other than zeta zeros below `T_D`). It can only be local: `ĝ_a` is bounded on `ℝ`, while `Ξ·e^{τz²}` is not.
3. **Consequence for the chain.** The family `φ_n = Φ + β_nΦ″ + γ_nΦ⁗` has transforms `(Ξ/2)(1 − β_nz² + γ_nz⁴) → Ξ/2` on the strip, because `β_n, γ_n → 0`. The ground states are closer to this family than to `Φ` by about ten orders at `δ = 3`. Taken as the kernel family in `rh_of_close_top`, the numerical margin of the one remaining hypothesis becomes very large. That substitution is not formalised: it needs `Φ″`, `Φ⁗` and their transforms in Lean.

**Status.** All of this is numerical, on supports up to `δ = 4.5`. The laws `sin²θ ~ e^{−4a}` and `β ~ e^{−δ}` are inferred, not proved. Proving that the minimiser has this structure for every `a` would prove RH (through `rh_of_close_top`), so these are targets, not results. `Φ`'s even derivatives are, like `Φ`, null directions of Weil's form (their transforms vanish at every zero), so a structural explanation plausibly starts there.

## Round 70: the correction is a backward heat flow of `Φ` with time `e^{−δ}/(16π)` (numerical, `frontier/nullvec/`)

Round 69 found the ground state `g_a ≈ c(Φ + βΦ″ + γΦ⁗)` with `γ ≈ β²/2`. So to second order `g_a ≈ c·e^{−τ∂²}Φ` and `ĝ_a ≈ c(Ξ/2)e^{τz²}`, with `τ = −β > 0`. This round pins down `τ` and tests the multiplier away from `z = 0`.

**The law** (`beta_fit.py`, now to `δ = 4.0`).

| `δ` | `β·e^δ` | `(β·e^δ + 1/16π)·e^δ` | `γ·e^{2δ}` | `γ/(β²/2)` |
|---|---|---|---|---|
| 1.0 | −0.020821 | −0.0025 | 4.17e-4 | 1.923 |
| 1.5 | −0.020853 | −0.0043 | 2.89e-4 | 1.330 |
| 2.0 | −0.020636 | −0.0055 | 2.47e-4 | 1.159 |
| 2.5 | −0.020368 | −0.0058 | 2.26e-4 | 1.087 |
| 3.0 | −0.020179 | −0.0057 | 2.14e-4 | 1.050 |
| 3.5 | −0.020070 | −0.0058 | 2.07e-4 | 1.029 |
| 4.0 | −0.020004 | −0.0060 | 2.04e-4 | 1.017 |

With the constant set to `1/(16π) = 0.019894`, the remainder `(β·e^δ + 1/16π)·e^δ` is steady at about `−0.0058` for `δ ≥ 2.5`: a clean leading term plus an `e^{−2δ}` correction. Aitken extrapolation of `β·e^δ` without assuming the constant gives `0.01991`, within `0.08%`. `γ·e^{2δ} → (1/16π)²/2 = 1.98e-4` and `γ/(β²/2) → 1`. **Conjecture:**

  `g_a ≈ c·e^{−τ_a∂²}Φ` with `τ_a = e^{−δ}/(16π) = 1/(16π e^{2a})`.

**What the time `τ_a` means.** On `Φ`'s tail, `Φ ≈ C x^{9/4}e^{−πx}` in the variable `x = e^{2t}`, so `Φ⁽²ᵏ⁾ ≈ (2πx)^{2k}Φ` to leading order. The backward heat flow then multiplies the tail by `exp(−τ(2πx)²) = exp(−(π/4)·x²/e^{2a})`. At the edge `x = e^{2a}` this damping is exactly **one quarter of `Φ`'s own decay exponent `πe^{2a}`**. The minimiser sharpens `Φ`, making it fall faster towards the edge of the window, by a precise fraction.

**The multiplier away from `0`** (`explain.py`, `δ = 2`, `explain_results_d2.json`), with `M = (ĝ/ĝ(0))/(Ξ/Ξ(0))`:
* On the real axis, `M(x) = e^{τx²}` to `0.1–4%` for `x ≤ 29`, where `e^{τx²} = 10.5`.
* On the imaginary axis, `log M(iy) = −τy²` to `1%` for `y ≲ 38`. Beyond that `ĝ(iy)` grows like `e^{ay}`, the Paley–Wiener maximum, because the edge of the support takes over.

**Heuristic explanations tried.**
* A Paley–Wiener argument balances `log Ξ(iy) ≈ (y/2)log(y/2πe)` against the type bound `ay` with a Gaussian `M(iy) = e^{−τy²}`. It gives `τ ≥ e^{−δ}/(4πe²) = 0.0108·e^{−δ}`: the right scaling, but the constant is off by a factor of 2.
* Balancing the truncation cost (`≈ Φ(a)²e^{−2κX²}`) against the failure of `Ξe^{τz²}` beyond `|z| ≈ π/(8τ)` gives `τ ≈ 0.034·e^{−δ}`: also the right scaling, constant again off.

Both explain why `τ ∝ e^{−δ}`. Neither produces `1/(16π)`, and **a derivation of the quarter-exponent rule is open.**

**The angle at `δ = 5`** (`K = 1100`, `4000` bits): `sin²θ = 3.18e-6`, so `sin²θ·e^{2δ} = 0.070`. That breaks the smooth trend (`0.0793, 0.0785` at `δ = 4.0, 4.5`). It is not yet checked in `K`: `K = 1100` may be too small at `δ = 5`. Until it is, the `C → 0.077` limit of round 69 stands on `δ ≤ 4.5`.

**Status.** All numerical. If the conjecture holds for every `a`, `ĝ_a/ĝ_a(0) → Ξ/Ξ(0)` on the strip follows (`τ_a → 0`), and with it RH through `rh_of_hypConvStrip_top`. So the conjecture is RH-strength. Its value is that it names the exact asymptotic form a proof would have to establish.

## Round 71: not a harmonic oscillator, but classical free motion with a caustic (numerical, `frontier/nullvec/`)

Round 70's heuristic: on `Φ`'s tail, `e^{−τ∂²}Φ ≈ Φ·exp(−τ(2πx)²)` with `x = e^{2t}`. With `τ = 1/(16πX)`, `X = e^{δ}`, this is a Gaussian in `x` (a harmonic-oscillator ground state). This round tests that pointwise. `oscillator.py` evaluates the ground state on `[0, a]` from its cosine coefficients. `Φ`, projected on the same basis, shows where values can be trusted: relative error `10⁻¹¹` (`δ = 2`) to `10⁻²⁷` (`δ = 3`) in the bulk, degrading only in the last `~0.1` before the edge. `hj.py` gives the Hamilton–Jacobi prediction. Data: `oscillator_results_d*.json`, `hj_results_d*.txt`.

**1. The ground state is `e^{−τ∂²}Φ` pointwise, not only in `L²`.** Here `τ` is round 70's fitted value and the heat flow is `Σ_k (−τ)^kΦ⁽²ᵏ⁾/k!` with exact derivatives. `log(g/Φ)` and `log(e^{−τ∂²}Φ/Φ)` agree:
* `δ = 2`: to `0.001–0.005` up to `t = 0.7` (the ratio reaches `−1.57`);
* `δ = 3`: to 3 decimals up to `t = 0.9`, and to `1%` at `t = 1.1`;
* `δ = 4`: to 4 decimals up to `t = 1.0`, and to `0.4%` at `t = 1.5` (the ratio reaches `−6.6`).

**2. The Gaussian in `x` is only the leading term.** It is off by `10–30%` in `log(g/Φ)` at intermediate `x`. The first correction to `−τS′²` (`S = log Φ`) has relative size `4πτx = x/(4X)`, which does not vanish at fixed `x/X`. So the harmonic-oscillator picture is not the large-`X` limit.

**3. The correct limit is Hamilton–Jacobi: classical free motion.** Write `g = e^{W}`. Backward heat flow `W_τ = −(W_t² + W_tt)` becomes, dropping `W_tt` (relative size `~1/(πx)`), the Hamilton–Jacobi equation for `H = p²`. Its characteristics start at `t₀` with momentum `p = S′(t₀) ≈ −2πe^{2t₀}`, reach `t = t₀ + 2pτ`, and carry `W = S(t₀) + τp²`. Their error against the ground state shrinks as `δ` grows: about `20%` at `δ = 2`, `6–11%` at `δ = 3`, `2–3%` at `δ = 4`. At `δ = 4` they keep tracking `g` beyond `t ≈ 1.6`, where the heat series has already diverged, down to `log(g/Φ) ≈ −30`.

**4. The characteristics fold into a caustic just inside the edge.** `dt/dt₀ = 1 + 2τS″(t₀) = 0` at `e^{2t₀} ≈ 1/(8πτ) = 2X`. With `τ = 1/(16πX)` this puts the caustic at `a − t_c = ½·log(e/2) = 0.1534`. Measured, with exact `S` and fitted `τ`: `0.1462, 0.1514, 0.1529` at `δ = 2, 3, 4`. In every run, the ground state leaves the heat flow at the caustic. So **the window has a bulk, where the ground state is `Φ` transported by classical free motion, and an edge layer of width `→ 0.153` beyond the caustic**, where it falls much faster.

**What this means for the constant `1/(16π)`.** With `τ = c/X`, the caustic distance is `½·log(8πec)`. So fixing `1/(16π)` is the same as fixing where the caustic sits relative to the edge. Equivalent readings, none derived:
* the caustic is fed by the characteristic that starts at `x₀ = 2X`, i.e. `t₀ = a + ½·log 2`, just outside the window;
* the characteristic starting at the edge `t₀ = a` lands at `a − ¼`.

(That the caustic's source sits at `a + ½·log 2` is a tempting link to the prime `2`. It is untested and may be a coincidence.) The natural derivation route is standard boundary-layer asymptotics: resolve the edge layer by the uniform (Airy-type) expansion at the caustic, impose the window's boundary condition at `t = a`, and read off `c`.

**Status.** Numerical, `δ ≤ 4`. The bulk description (backward heat flow of `Φ`, i.e. classical free transport of its phase) is now established pointwise at these supports. The edge layer and the value of `c` are open.

## Round 72: the edge condition behind `1/(16π)`: partly derived, partly open (`frontier/nullvec/edge_principles.py`)

**Derived (leading order).** Backward heat flow `e^{−τ∂²}Φ` is, in the Hamilton–Jacobi limit (round 71), free classical transport of `S = log Φ ≈ −πe^{2t}`. Along the characteristics, `W = S(t₀) + τp²` with `p = S′(t₀) ≈ −2πx₀`. The caustic sits at `x₀ = 1/(8πτ)`, where `W_c = −1/(16τ)`. So for `τ = c·e^{−δ}` the following conditions are **all equivalent at leading order**, and each selects `c = 1/(16π)`:
* P1: the amplitude at the caustic equals `Φ` at the window's edge, `W_c = log Φ(a) ≈ −πe^{δ}`;
* P2: the caustic is fed from `x₀ = 2e^{δ}`, i.e. `t₀ = a + ½·log 2`;
* P3: the characteristic from the edge `t₀ = a` lands at `a − ¼`;
* P4: the caustic sits at `a − ½·log(e/2)`.

So the constant is one matching condition between the bulk (transported `Φ`) and the window's edge.

**Discriminating at finite `δ`.** Each condition, evaluated with the exact `S`, predicts its own finite-`δ` correction to `τe^{δ}`:

| `δ` | measured | P1 | P2 | P3 | P4 |
|---|---|---|---|---|---|
| 2.0 | 0.020636 | 0.020516 | 0.019880 | 0.022102 | 0.020953 |
| 3.0 | 0.020179 | 0.020116 | 0.019892 | 0.020638 | 0.020261 |
| 4.0 | 0.020004 | 0.019975 | 0.019894 | 0.020160 | 0.020026 |

P2 (almost no correction) and P3 (correction 2.5× too large) are excluded. P1 and P4 bracket the measurement, each off by about `25%` in the correction. That is the size of the dropped `W_tt` term in Hamilton–Jacobi, so this test cannot separate them. P4 is also only a restatement of the constant. P1 is the candidate with physical content.

**P1 tested directly on the ground state** (pointwise, `g` normalised to `Φ` in the bulk, at the measured caustic): `log g(t_c)` against `log Φ(a)`:

| `δ` | `log g(t_c)` | `log Φ(a)` | relative gap |
|---|---|---|---|
| 2 | −14.79 | −15.80 | 6.4% |
| 3 | −51.15 | −53.39 | 4.2% |
| 4 | −154.42 | −159.55 | 3.2% |

It holds at leading order, with a shrinking relative gap, as a leading-order law with subleading corrections should.

**Not derived.** Why the minimiser of Weil's form selects P1 (or whichever exact condition is right) remains open. That needs a model of the form's cost in the edge layer, where the heat-flow representation ends. A controlled next step: a reduced variational problem, with a transported-`Φ` bulk (parameter `τ`) plus an edge-layer ansatz, energy evaluated on the certified Gram, minimised over `τ`. If it reproduces `1/(16π)`, the edge-layer energetics is the explanation.

**Also this round.** The `δ = 4.5` angle is now checked in `K`: `K = 900` and `1100` give `sin²θ = 9.6877e-6` and `9.6893e-6`.

## Round 73: a reduced variational model: the heat family alone does not fix the constant (`frontier/nullvec/`)

**Rayleigh–Ritz on `span{Φ, Φ″, …, Φ⁽²ᵐ⁾}`** (`ritz.py`, `δ = 2`). Each `Φ⁽²ᵏ⁾` is a null direction on `ℝ`, so the restricted energy is pure edge cost. The Ritz minimiser moves toward the ground state as `m` grows: `c₁/c₀·e^δ = −0.0043, −0.0077, −0.0103, −0.0124` for `m = 1–4`, against the ground state's `−0.0206`, with `λ_Ritz = 2.6e-17 → 3.5e-22` against `λ₁ = 6.3e-30`.

**One-parameter heat family** (`heat_family.py`, fast version `heat_family_fast.py`, which computes all derivative orders per node in one pass and reproduces the slow one exactly, 7–10× faster). Take `h_τ = Σ_{k≤m}(−τ)^kΦ⁽²ᵏ⁾/k!` on `[−a, a]`, with no edge freedom. Minimise `Q(h_τ)/‖h_τ‖²` over `c = τe^δ`.

| `m` | 2 | 4 | 8 | 12 | 16 | 20 | 24 | 28 | 32 |
|---|---|---|---|---|---|---|---|---|---|
| `δ = 2`: `c_opt` | 0.00555 | 0.01169 | 0.01628 | 0.01961 | 0.021957 | 0.0219594 | 0.0219596 | 0.0219596 | 0.0219596 |
| `δ = 3`: `c_opt` | | | | 0.00856 | 0.01159 | 0.01357 | 0.01516 | (running) | |

At `δ = 2` the optimum converges, from `m = 16` on, to **`c = 0.021960`**. The ground state has `0.02064`, and `1/(16π) = 0.01989`. The optimal energy is `2.8e-24`, about `10⁶` times the true `λ₁ = 6.3e-30`. At `δ = 3` the series needs more terms: the number of significant terms scales like `τ(2πX)² ≈ 16`, against `≈ 6` at `δ = 2`. A run to `m = 64` is under way.

**Reading.** The least-edge-cost member of `Φ`'s backward-heat family is not the ground state: at `δ = 2` its time is `6%` too large, and its energy is `10⁶` too high. The edge layer, which this family cannot represent, carries most of the energetics and shifts the optimal `τ`. So "minimise the truncation cost of transported `Φ`" is not by itself the principle behind `1/(16π)`. Any derivation must include the edge layer. Whether `c_opt/c_ground → 1` as `δ` grows (the edge layer becoming relatively cheaper) is what the `δ = 3` run will show.

**Also this round.** The `δ = 5` angle is not converged in `K`: `K = 1100` and `1300` give `sin²θ = 3.18e-6` and `3.48e-6`, and `λ₁` moves by 22 orders. The `δ = 5` row of round 70 is therefore unreliable. The `K = 1300` value gives `sin²θ·e^{2δ} = 0.077`, back in line with the trend. Confirming it needs `K ≳ 1500`.

## Round 74: the strip note's `1/(16π)` derivation, formal except for the balayage (SixteenPi.lean)

The owner's working note (`riemann-strip-target-note.md` §3.4) derives this pilot's multiplier time `τ_a = e^{−δ}/(16π)` (rounds 70–73) from the zero side, within the paper's Theorem 1bm(iv) reduced problem. Round 74 formalises every step of that derivation that is ordinary analysis. It uses only the standard axioms and adds no hypothesis beyond the ones listed here.

- **(3.1) The time is the curvature defect** (`multiplier_expansion`). Take Hadamard products `f(z)/f(0) = Π(1 − z²w_i)` and `F(z)/F(0) = Π(1 − z²v_k)`. Then `f(z)/f(0) = (F(z)/F(0))(1 + τz²) + E`, with `τ = Σv − Σw` and `‖E‖ ≤ 3‖z‖⁴(Σ‖w‖ + Σ‖v‖)²` once `‖z‖²(Σ‖w‖ + Σ‖v‖) ≤ 1`. Applied to `ĝ_a` and `Ξ` this gives `τ = Σγ⁻² − Στ⁻² = κ_Ξ − κ(a)`, for any ground state.
- **(3.2) Under D, only the tails remain** (`defect_sub_tail`, `defect_eq_tail_of_D`, `defect_sub_tail_le`). If the first `N` zeros agree, the defect equals the tails' defect exactly. The paper verifies D only within a tolerance. If the first `N` zeros agree within `Δ_n ≤ γ_n/2`, the defect is within `Σ_{n<N} 10Δ_n/γ_n³` of the tails' defect, via `inv_sq_sub_le`: `|γ⁻² − t⁻²| ≤ Δ(2γ + Δ)/(γ²(γ − Δ)²)`. This is the note's "at most `2Δ/γ³(1 + O(Δ/γ))`".
- **(iv) The closed forms.**
  - `∫_X^∞ x⁻² ln x dx = (1 + ln X)/X` for `X ≥ 1` (`integral_log_div_sq_Ioi`).
  - `P = ∫₀¹ (1 − √(1 − s²))/s² ds = π/2 − 1` (`P_eq`).
  - `Q = ∫₀¹ ln s·(1 − √(1 − s²))/s² ds = π/2 − 1 − (π/2) ln 2` (`Q_eq`).
  - `P` and `Q` both use the substitution `s = sin θ` (`integral_subst_sin`, valid for any integrand). `Q` also needs the antiderivative `sin θ ln sin θ/(1 + cos θ) − θ + tan(θ/2)` of `ln sin θ/(1 + cos θ)`, and Mathlib's `∫₀^{π/2} ln sin = −(π/2) ln 2`.
  - The rescaling `t = Xs`: `∫₀^X (−ln t)h_X(t) dt = (−P ln X − Q)/X` (`balayageSide_eq`).
  - Hence `J(X) = (π/(2X))(1 + ln(X/2))` (`J_eq`), and `J(2) = π/4`.
- **(v) The wall and the constant.**
  - `(1 + ln(X/2))/X ≤ 1/2`, with equality only at `X = 2` (`wall_le`, `wall_eq_iff`), and the deficit is quadratic: at most `(y − 1)²/(2y²)` with `y = X/2` (`wall_quadratic`).
  - `J(X)/(2πT₀) = (1 + ln(X/2))/(4XT₀)` (`J_div_eq_tauWall`), which equals `e^{−δ}/(16π)` at `X = 2`, `T₀ = 2πe^δ` (`tau_at_wall`).
  - Assembled: given the balayage identity at the wall, `(∫_2^∞ x⁻²[ln x − τ(x)] dx)/(2πT₀) = e^{−δ}/(16π)` (`sixteenPi_of_balayage`).

**Not formalised.**
- **The balayage identity** `∫_X^∞ x⁻²τ(x) dx = ∫₀^X (−ln t)h_X(t) dt`: harmonic measure on the doubly slit plane, the hypothesis `hbal` of `exteriorMoment_eq` and `sixteenPi_of_balayage`.
- **The note's four inputs (vii)(a)–(d).** None of these is touched:
  - (a) Hypothesis D at the wall, which is RH-strength at every δ;
  - (b) the reduction's five lemmas;
  - (c) that the ground state's wall sits at the reduced problem's maximiser `X = 2`;
  - (d) the continuum density in place of the discrete zeros.
- Also, `defect_*` take the zeros as enumerated sequences; the bridge to the `ZeroIdx` families of `HadamardApply` is not built.

So the formal status of `1/(16π)` is:

**(balayage identity) ∧ D at the wall ∧ (b)–(d) ⇒ τ_a = e^{−δ}/(16π)**

Every arithmetic and calculus step in between is now checked. Nothing here bears on RH.

**Also this round (numerical).** At `δ = 5`:
- `K = 1300` gives `sin²θ = 3.4781e-6` at both 3200 and 4000 bits.
- `K = 1500` gives `3.5426e-6`, a change of `1.9%`, so `K = 1500` is still not converged.
- `sin²θ·e^{10} = 0.0766` at `K = 1300` and `0.0780` at `K = 1500`, against the note's prediction `(13.98/16π)² = 0.0774`.
- `K = 1700` is running.

## Round 75: the reduced problem's `1/(16π)`, with no hypothesis (SixteenPi.lean)

Round 74 kept one hypothesis inside the reduced problem: the balayage identity `hbal`. Round 75 proves it. With it proved, every statement *about the reduced problem* is unconditional.

**The balayage identity** (`balayage_identity`).
- Take the paper's explicit density (Theorem 1bm(iv)), `τ(x) = −I(x)/(π√(x² − X²))` with `I(x) = ∫_{−X}^{X} √(X² − t²) ln|t|/(x − t) dt`.
- For every `X > 0`: `x⁻²τ` is integrable on `(X, ∞)`, and `∫_X^∞ x⁻²τ = ∫₀^X (−ln t) h_X(t) dt`.
- **Method.**
  1. Write `x⁻²τ(x) = ∫ (−ln|t|) k(t, x) dt`, with the kernel `k(t, x) = √(X² − t²)/(π x² √(x² − X²)(x − t)) ≥ 0`, and exchange the two integrals (`integral_integral_swap`).
  2. Integrability on the product follows from the bound `0 ≤ ∫_X^∞ k(t, x) dx ≤ 1/X²` (`Abal_bounds`) and the integrability of `ln` near 0.
  3. The paired kernel `k(t, ·) + k(−t, ·)` splits by partial fractions into two arctan kernels, `x/((x² − X² + c²)√(x² − X²))` with `c = √(X² − t²)` and `c = X` (`kBal_pair`).
  4. Each arctan kernel integrates to `π/(2c)` (`integral_gAt`). So `∫_X^∞ [k(t, x) + k(−t, x)] dx = h_X(t)` (`kBal_integrals`).
  5. Folding `t < 0` onto `t > 0` finishes the proof.
- Harmonic measure is never used.

**Consequences, with no hypothesis.**
- `∫_X^∞ x⁻²[ln x − τ(x)] dx = (π/(2X))(1 + ln(X/2))` for `X ≥ 1` (`exteriorMoment_reduced`).
- At the wall, `(∫_2^∞ x⁻²[ln x − τ]) / (2πT₀) = e^{−δ}/(16π)` with `T₀ = 2πe^δ` (`sixteenPi_reduced`).
- The paper's reduced exponent `f(X) = 2πX(1 + ln 2 − ln X)` satisfies `f ≤ 4π`, with equality only at `X = 2` (`fBalExp_le`). This proves the paper's `X* = 2` and `f_∞ = 4π`.

**Admissibility at the wall: a closed form, proved on paper.** The paper states that the positivity of `τ` on the whole exterior at `X = 2` "is checked to 10⁶X, not proved". The density has a closed form, which proves it.
- **The closed form.** With `s = √(x² − X²)`, `τ_X(x) = ln(Xx/(x + s)) − x·ln(X/2)/s`.
- **Proof.**
  1. Rewrite `√(X² − t²)/(x² − t²)` as `[1 − s²/(x² − t²)]/√(X² − t²)` and substitute `t = X sin θ`. This leaves `L = ∫₀^{π/2} ln sin θ/(x² − X² sin²θ) dθ`.
  2. Use `ln sin θ = −ln 2 − Σ_k cos(2kθ)/k` together with the classical `∫₀^π cos kφ/(a + b cos φ) dφ = (π/√(a² − b²))·((√(a² − b²) − a)/b)^k`, here with `a = x² − X²/2` and `b = X²/2`. The ratio becomes `−q`, where `q = (x − s)/(x + s)`.
  3. Summing the series gives `L = (π/(2xs)) ln(x/(x + s))`.
- **At `X = 2`.** `τ(x) = ln(2x/(x + √(x² − 4)))`. This is strictly positive for `x > 2`, equals `ln 2` at the edge (the paper's edge value) and tends to 0 at infinity.
- **Numerical checks (`scratchpad`, 30 digits).** The closed form matches the paper's `−I/(π√)` at `X = 0.7, 1.5, 2, 3`. At `X = 2` its moment matches `(ln 2 − π/2 + 1)/2 = 0.0611754…`. Its mass matches `2(1 − ln 2)` to quadrature accuracy.
- **Not formalised.** This needs the Fourier series of `ln sin`, which is not in Mathlib.

**What remains conditional, and why it cannot be removed here.** These are the note's inputs (vii)(a)–(d), the link from the reduced problem to ζ's actual ground state:
- (a) Hypothesis D at the wall. At every δ with `T → ∞` it is the strip target itself, so removing it is RH-strength.
- (b) The five reduction lemmas: the paper's "the reduction is not a theorem".
- (c) That the *ground state's* wall is the reduced problem's maximiser. Round 75 proves the maximiser inside the reduced problem, not the transfer to the ground state.
- (d) The continuum limit. This is an approximation whose error is the pilot's measured `−0.0058e^{−δ}` term, not a hypothesis that could be discharged.

So `1/(16π)` is now a theorem about the paper's reduced problem, and a conjecture about ζ's ground state exactly to the extent of (a)–(d).

## Round 76: the balayage density in closed form, and its positivity at the wall (SixteenPi.lean)

Round 75 recorded a closed form for the paper's balayage density, proved on paper using the Fourier series of `ln sin`, which Mathlib lacks. Round 76 proves it in Lean by a route that avoids that series.

**The theorem** (`tauBal_closed`). For `x > X > 0`, with `s = √(x² − X²)`:

`τ_X(x) = −I(x)/(πs) = ln(Xx/(x + s)) − x·ln(X/2)/s`.

Equivalently (`Ibal_closed`): `I(x) = πx ln X − πx ln 2 − πs ln x + (πs/2)(ln(x + s) − ln(x − s))`.

**Route.** Every step is elementary.
1. **The logarithm as an integral** (`integral_logRep`): `ln c = ∫₀^∞ (1/(1 + v) − 1/(c + v)) dv`, with `∫|·| = |ln c|`. So `ln|t| = ½∫₀^∞ (1/(1 + v) − 1/(t² + v)) dv`.
2. **Fubini** on `(−X, X) × (0, ∞)`. The product integrand is integrable because `√(X² − t²)/(x − t) ≤ X/(x − X)` and `∫|·| dv = 2|ln|t||`.
3. **For fixed `v`, the `t`-integral** (`integral_Cv`). Partial fractions `1/((x − t)(t² + v)) = [1/(x − t) + (x + t)/(t² + v)]/(x² + v)` reduce it to three pieces:
   - `C₀ = ∫√(X² − t²)/(x − t) = π(x − s)` (`integral_C0`), by the antiderivative `x·arcsin(t/X) − √(X² − t²) + s·arcsin((X² − xt)/(X(x − t)))`;
   - `D(v) = ∫√(X² − t²)/(t² + v) = π(√(X² + v) − √v)/√v` (`integral_Dv`), by the antiderivative `(√(X² + v)/√v)·arcsin(t√(X² + v)/(X√(t² + v))) − arcsin(t/X)`;
   - an odd part, which vanishes (`integral_Ev`).
   Both arcsin antiderivatives are continuous on the closed interval, so no improper integrals are needed.
4. **The `v`-integral** (`integral_Qv`). Its antiderivative is `2π[ln(√v + √(X² + v)) − ½ln(x² + v) − (s/(2x))(ln(x√(X² + v) + s√v) − ln(x√(X² + v) − s√v))]`:
   - its derivative is checked with one polynomial identity (`hasDerivAt_Qprim`);
   - its limit at `∞` comes from rescaling to `2πΨ(1/v)` with `Ψ` continuous at 0 (`Qprim_eq_Psi`, `tendsto_Qprim`).
5. **Assembly.** Combine the pieces, then use `(x + s)(x − s) = X²` to reach the stated form.

**Admissibility at the wall, proved** (`tauBal_two`). For every `x > 2`, `τ(x) = ln(2x/(x + √(x² − 4))) > 0`. The paper's Theorem 1bm(iv) states that "positivity on the whole exterior at X = 2 is checked to 10⁶X, not proved". The closed form proves it for every `x > 2`: the balayage at the wall is a positive density on the whole exterior, as the paper's "admissibility threshold is the maximiser" needs.

**Status of the reduced problem.** Every statement of the note's §3.4 inside the paper's reduced problem is now a Lean theorem with no hypothesis:
- the balayage identity;
- the exterior moment and `e^{−δ}/(16π)`;
- the wall `X* = 2` with `f_∞ = 4π`;
- the density's closed form and its positivity at the wall.

What stays conditional is only the transfer to ζ's ground state, the note's (vii)(a)–(d); (a) is RH-strength (round 75).

## Round 77: the whole multiplier in closed form (numerical, `frontier/nullvec/multiplier_closed.py`)

**What round 76 implies.** Write `x = 2 cosh u` and `s = 2 sinh u`. At the wall, the closed form `τ(x) = ln(2x/(x + s))` becomes `ln(1 + e^{−2u})`. The exterior zero deficit is therefore exactly

`ln x − τ(x) = u = arccosh(x/2)`,

the Green's function of the band `[−2, 2]` with its pole at infinity. For a general wall the deficit is `arccosh(x/X) + (x/s)·ln(X/2)`. `X = 2` is the only wall where the second term, whose edge singularity is the admissibility issue, vanishes identically.

**The multiplier.** Summing `ln(1 − z²/r²)` against this deficit, not just its `r⁻²` moment, gives the whole multiplier:

`ln M(z) = −(1/2π)∫_{2T₀}^∞ ln(1 − z²/r²)·arccosh(r/(2T₀)) dr = T₀[w·arcsin w + √(1 − w²) − 1]`,

with `w = z/(2T₀)` and `T₀ = 2πe^δ`.
- Proof sketch: expand the log. The moments are `∫₁^∞ y^{−2k} arccosh y dy = (√π/2)Γ(k − ½)/((2k − 1)Γ(k))`. The resulting series has second derivative `1/√(1 − w²)`.
- The formula was checked against direct quadrature at `w = 0.3` and `0.8` to 10⁻¹⁰.
- Its small-`w` expansion is `z²/(8T₀) + z⁴/(384T₀³) + …`. So the Gaussian `e^{τz²}` with `τ = e^{−δ}/(16π)` is just the first term, and round 69's `γ/(β²/2) → 1` is automatic from scaling: the quartic cumulant is `O(e^{−3δ})`.
- On the imaginary axis, `ln M(iy) = −T₀[η·arsinh η − √(1 + η²) + 1]`, with `η = y/(2T₀)`. For large `y` this is `≈ −(y/2) ln(y/T₀) + y/2`. That is exactly the factor turning `Ξ`'s growth `(y/2) ln(y/2πe)` into the exponential type `a = δ/2` that a probe supported on `[−a, a]` must have.

**Measured against the ground state** (`explain.py` at `δ = 2` and `δ = 3`; ratio = measured `ln M` / closed form; no fitted parameter):

| `y/y₀` | 0.05 | 0.3 | 1.0 | 2.0 | 5.0 |
|---|---|---|---|---|---|
| `δ = 2` | 1.0430 | 1.0407 | 1.0287 | 1.0183 | 1.0083 |
| `δ = 3` | 1.0149 | 1.0142 | 1.0102 | 1.0066 | 1.0030 |

At `y = 5y₀` the Gaussian is off by a factor of 2: −1112 against a measured −557 at `δ = 2`, and −2956 against −1506 at `δ = 3`. The closed form is within 0.8% and 0.3% there.
- The small-`y` ratio is the known offset of `τ` itself: `τ_fit·16πe^δ = 1.037` and `1.014`. Round 70's "remainder `≈ −0.0058e^{−δ}`" fits this.
- The ratio falls with `δ` roughly like `e^{−δ}` at every `y`, and the real axis agrees: 1.043 at `δ = 2` and 1.015 at `δ = 3` for small `x`.

**Reading.**
- Within the paper's reduced problem, the ground state's transform is `ĝ_a(z)/ĝ_a(0) ≈ (Ξ(z)/Ξ(0))·exp{T₀[w·arcsin w + √(1 − w²) − 1]}`, uniformly over the range tested (up to five times the Paley–Wiener scale `y₀`), with a relative error of order `e^{−δ}`.
- The heat-flow picture of rounds 70–73 is this formula's small-`w` limit.
- The edge layer and caustic of round 71 are where `w` stops being small.
- The formula's inputs remain those of the note's §3.4 (vii): the transfer from the reduced problem to the actual ground state. It is a prediction of the reduced problem that the data confirm. It is not a theorem about ζ, and nothing about RH follows.

## Round 78: the pole overlap at large support, and δ = 5 confirmed (numerical)

**The pole overlap of the second pole-free mode** (`frontier/simplicity/overlap_big.py`).
- **Method.** Block inverse iteration in arb. `Q₀` has exactly one negative eigenvalue (≈ −4.3), so `ψ₂` belongs to the smallest nonnegative eigenvalue `μ₂`.
- **Results.** `κ = ⟨c, ψ₂⟩/μ₂`, with `ψ₂(0) > 0`:

| `δ` | 2.0 | 2.5 | 3.0 | 3.5 | 4.0 |
|---|---|---|---|---|---|
| `κ` | −0.35022 | −0.34543 | −0.34269 | −0.34108 | −0.34013 |
| `μ₂` | 1.5e-23 | 1.0e-47 | 7.4e-89 | 5.1e-158 | 2.7e-273 |

- `κ` is stable in `K` to 6 digits (`K = 120/180` at `δ = 2`, `300/400` at `δ = 3`). It continues round 51's trend and settles near `−0.34`, but it is not proved.
- The overlap itself, `κμ₂`, collapses super-exponentially. So the gap bound `simple_of_pole_overlap` certifies simplicity window by window, but with a gap of size `μ₂²`.
- Simplicity is not an input of the RH chain since `StructureD.lean` (`topGS`, "simplicity is no longer a separate input"). The overlap's role is only to identify `topGS` with the computed ground state.

**The closeness hypothesis of `rh_of_close_top`, measured.** Distance `‖Φ‖ sin θ` against the threshold `e^{−a/2}/√(2a)`:
- the ratio is `2.7e-2, 1.5e-2, 7.9e-3, 4.2e-3` at `δ = 2, 3, 4, 5`, decreasing like `e^{−3a/2}√a`;
- the hypothesis is satisfied with a growing margin at every computed window;
- no finite computation discharges it, because it is a limit statement.

**`δ = 5` converged.** `K = 1700` (3600 bits) gives `sin²θ = 3.5437e-6`, against `3.5426e-6` at `K = 1500`: stable to 3 parts in `10⁴`. So `sin²θ·e^{2δ} = 0.0806, 0.0793, 0.0785, 0.0781` at `δ = 3.5, 4, 4.5, 5`.
- The excess over the note's prediction `(13.98/16π)² = 0.0774` is `0.0019, 0.0011, 0.0007` at `δ = 4, 4.5, 5`. It shrinks by `≈ 0.6 = e^{−1/2}` per half-unit of `δ`, i.e. like `e^{−δ}` (`≈ 0.10e^{−δ}`), the same order as round 77's corrections.
- So the data converge to `0.0774`.

**The heat family at `δ = 3`, converged** (`m = 64`). `c_opt = 0.0197318`, against the ground state's `0.020179` and `1/(16π) = 0.019894`. The ratio `c_opt/c_ground` is `1.064` at `δ = 2` and `0.978` at `δ = 3`. The least-edge-cost heat member crosses the ground state's time rather than converging to it. This confirms round 73: the family alone does not fix the constant.

## Round 79: the functor, and what the pilot has been computing (`frontier/nullvec/repkernel.py`)

**The functor.**
- The windows `a > 0`, ordered by inclusion, map to the spaces `PW_a = {ĝ : g ∈ L²[−a, a]}` carrying Weil's form `Q`. Inclusion of windows is an isometric embedding, since `Q_b` restricted to `PW_a` is `Q_a`.
- This is a functor into quadratic spaces, with no hypothesis.
- It lands in Hilbert spaces up to window `a` iff `Q_a ≥ 0`. For every `a` that is Weil's criterion, i.e. RH.
- Where it is positive, it is a de Branges chain. Suzuki shows that the Hilbert space built from Weil's distribution is a de Branges space, and that RH is equivalent to the existence of a Krein canonical system (a Hamiltonian `H(t)` on all of `[0, ∞)`) generating it ([arXiv 2301.00421](https://arxiv.org/abs/2301.00421), [arXiv 1204.1827](https://arxiv.org/abs/1204.1827)).
- Positivity is proved for small windows. In this pilot that is FourierGap/ParabolaGap (`2a < log 2`) and the certified simplicity cells.

**What the pilot has been computing.** The ground state of `Q_a` is, up to normalisation, the chain's reproducing kernel at `z = 0`: `k₀ = Q_a⁻¹ ev₀` with `ev₀(g) = ĝ(0)`.

| `δ` | `K` | `sin²∠(k₀, g₁)` | `λ₁/λ₂` | `ln K_a(0, 0)` | `−ln λ₁` |
|---|---|---|---|---|---|
| 2 | 180 | 4.0e-14 | 2.7e-7 | 66.23 | 67.24 |
| 3 | 400 | 7.4e-18 | 3.7e-9 | 220.52 | 221.90 |

The two agree to relative order `(λ₁/λ₂)²` times an overlap ratio, and the agreement improves with `δ`.
- **The open hypothesis, restated.** Rounds 62–78 ask whether the chain's normalised kernels `K_a(z, 0)/K_a(0, 0)` converge to `Ξ(z)/Ξ(0)` fast enough.
- **Round 77's multiplier, restated.** It is a prediction for the asymptotics of these kernels.
- **Round 27, restated.** Round 27 found `ĝ_δ` and `∂_δĝ_δ` interlacing at every `δ` tested. That is the Hermite–Biehler property of the chain's structure function, which the canonical system `∂_t(A, B) = zJH(t)(A, B)` provides wherever the chain exists. This is a plausible explanation, not checked here.
- **Status.** Nothing here removes the open input. The chain exists for all `a` iff RH. The reformulation turns global positivity into positivity of a Hamiltonian that is local in `t`.

## Round 80: the window chain's Hamiltonian, and the law behind `1/(16π)` (`frontier/nullvec/kchain*.py`)

**Setting.** On the even functions, the window chain `a ↦ (PW_a, Q)` of round 79 is a diagonal canonical system (a Krein string) `H = diag(h₁, h₂)`. It is determined by two functionals:
- `ℓ₀(F) = F(0) = ∫g`;
- `ℓ₂(F) = −[z²]F = ½∫t²g`.

Their kernel matrix is `𝒦(a) = L Q_a⁻¹ Lᵀ = ∫₀^a h₁[1 c; c c²]`, with `c = ∫ h₂ 𝒦₀₀`. Hence, in the window variable `a = δ/2`:
- `h₁ = d𝒦₀₀/da`;
- `h₂ = (dc/da)/𝒦₀₀`;
- `c = r + r′/ℓ′`, where `ℓ = ln 𝒦₀₀` and `r = 𝒦₀₂/𝒦₀₀`.

`kchain.py` computes `𝒦` at `δ = 0.3, 0.35, …, 3.2`, with `K = 20e^δ + 40` and `30e^δ + 40` at `300 + 40e^δ` bits.

**1. `det H = 1` in the window variable.**
- `det H = h₁h₂ = 4ℓ′c′` (derivatives in `δ`) comes out as `1.004 ± 0.013` over `δ ≥ 1.5` at both `K`. It is within `±0.08` down to `δ = 0.4`.
- This is the Krein–de Branges type formula: exponential type `= ∫√det H`, and the space at window `a` has type exactly `a`. So it is a check on the extraction, not a discovery.
- It says the chain is a Dirac system in `a`, with `H = diag(e^{2φ}, e^{−2φ})`, `φ = ½ ln(d𝒦₀₀/da)`, and potential `q = φ′`. Asymptotically `q ≈ 4πe^{2a} − 4.5`, with structure where prime powers enter at `a = ½ log pᵏ`. This is visible as dips in `ℓ′`, not resolved at step 0.05.

**2. The two clues are one law.** `det H = 1` gives `c′ = 1/(4ℓ′)`. If the kernels converge, `c → κ_Ξ = 0.02310499`, so the multiplier time `τ = κ_Ξ − r` satisfies

`τ(δ) = ∫_δ^∞ du/(4ℓ′(u)) + r′/ℓ′`.

Measured against predicted (data up to `δ = 3.15`, then a tail with `ℓ′ ≈ 4πe^u − 4.5`): the ratio `τ_meas/τ_pred` is `1.001–1.007` at every window from `δ = 0.5` to `3.1`, at both `K`. Consequences:
- The paper's exponent law `ln 𝒦₀₀ ≈ −ln λ₁ ≈ 4πe^δ` (`f_∞ = 4π`) forces `τ ≈ e^{−δ}/(16π)`. The constant is `1/(4·4π)`, so round 70's quarter-exponent rule `τ = 1/(4T)` is this identity.
- The `O(1)` offset `ℓ′ − 4πe^δ ≈ −4.5` produces the `e^{−2δ}` correction. Predicted: `≈ 0.0053–0.0057`. Measured: `0.0058–0.0062`, consistent with round 70's `≈ 0.0058`. The remaining gap is the tail extrapolation.
- So the whole multiplier time follows from the growth of one number, the reproducing kernel at 0.

**Status.** The Hamiltonian of the window chain is explicit in terms of `K_a(0, 0)`: it is diagonal, has determinant 1, and has potential `½ d/da ln(dK_a(0, 0)/da)`. Its asymptotics are fixed by the reduced problem's `4π`. RH is equivalent to this chain existing for every `a`. Our numbers describe it where it provably or numerically exists. Nothing here shows it exists for all `a`.

## Round 81: the prime structure of the chain's potential (`frontier/nullvec/kprime*.py`, `kedge.py`)

**Method.** Each prime power `n` enters the form through `−2(Λ(n)/√n)·f(log n)`, where `f` is the probe's autocorrelation, when the window passes `δ = log n`. `kprime.py` computes `Δℓ(ε)`: the value of `ℓ = ln K_a(0, 0)` at `δ = log n + ε` with the term of `n` on, minus its value with the term off. Both use the same basis, so the truncation ripple that spoils fixed-`K` scans (`kfine.py`: slope noise `±2–3` at step `0.0025`) cancels exactly.

**1. In every truncation, the potential jumps, with an exact first-order law.** `ℓ′` jumps at `log n` by

`J_n = 2·(Λ(n)/√n)·E(log n)`, where `E = k(a)²/K(0, 0)` is the reproducing kernel's edge weight.

Measured by Richardson extrapolation in `ε`, the ratio `J/(2wE)` is `0.9993, 0.9996, 0.9998, 0.9997, 0.9991, 0.9987, 0.9957` for `n = 2, 3, 4, 5, 7, 8, 9`, at `K = 25e^δ + 60`. At `K = 50e^δ + 60` it is `0.998` (n = 3) and `0.996` (n = 7). For `n ≥ 11` the `ε`-steps are not small against the edge scale: the ratio is `0.97 → 0.50`.

**2. But `E` is a truncation artefact: the continuum kernel vanishes at the edge.** At `δ = log 3`, `E = 6.25, 5.36, 4.83, 4.37, 3.98` for `K = 135, 210, 300, 450, 700`, falling like `K^{−0.27}`. The profile just inside the edge (`k(a − h)²/K(0, 0)` at `h = 0.005–0.05`) is `K`-converged. So in the true chain `J_n = 0`: no prime power makes the potential jump.

**3. The continuum onset is a soft, non-universal kink.** `Δℓ(ε)` at `ε ≥ 0.002`, where the basis resolves it (at `n = 3`, `K = 450` and `690` agree to 0.5%):

| `n` | 3 | 5 | 7 | 8 | 9 |
|---|---|---|---|---|---|
| local exponent, `ε` = .002 → .004 | 1.43 | 1.59 | 1.34 | 1.84 | 1.12 |
| `Δℓ(.002)/(w·.002^{3/2})` | 297 | 740 | 1531 | 2720 | 3423 |

At `n = 3` the exponent is `1.41 → 1.53` over `ε = 0.002–0.016`, i.e. `Δℓ ∝ ε^{≈3/2}`, a kernel edge exponent of about `¼`. It varies from prime to prime (`1.1–1.8`), and the amplitude per unit weight does not follow a smooth function of `δ`. For example, `7 → 8` grows ×1.78 in `Δδ = 0.13`, but `8 → 9` only ×1.26 in `Δδ = 0.12`.

**Reading.** The hypothesis "potential = archimedean part + Σ(Λ(n)/√n) × one universal profile" fails in this simple form. Each prime's imprint depends on the kernel's near-edge profile at that window, and that profile is itself reshaped by the prime powers that entered just before. The chain has memory. Two things survive:
- the exact first-order identity, whose content is `J_n ∝ (Λ(n)/√n)·(edge weight)` in any regularisation;
- a measured continuum onset exponent near `3/2` at `n = 3`.

Neither is derived.

## Round 82: the Hamiltonian, tabulated and validated (`frontier/nullvec/kham.py`, `zdirect.py`, `ktable.py`, `hamiltonian_*`)

**The object.** The window chain's Hamiltonian is `H(a) = diag(e^{2φ(a)}, e^{−2φ(a)})`, from its diagonal form (round 80) and `det H = 1`. Here `e^{2φ} = h(a) = dK_a(0, 0)/da` and `K_a(0, 0) = sup (∫g)²/Q(g)` over `g` supported in `[−a, a]`. So the Hamiltonian is determined by the one function `L(a) = d ln K_a(0, 0)/da`. With `b = B/K_a(0, 0)` the canonical system becomes

`A′ = −(z/L)·b`,  `b′ = L·(zA − b)`,  `K_a(z, 0)/K_a(0, 0) = b/z`.

**Validation: the Hamiltonian generates the chain.**
- **Method.** `L` comes from `ln K_a(0, 0)` on a grid (`kchain.py`, `K = 30e^δ + 40`), smoothed by local cubic fits of half-width `0.02` in `δ`. The system is integrated from `δ = 0.5` (exact initial data from the direct kernel at `δ = 0.49, 0.5, 0.51`) to `δ = 2`, and the result compared with `K_a(z, 0)/K_a(0, 0)` computed directly from the Gram (`zdirect.py`).
- **Results.** Relative errors:

| grid step in `δ` | `z = 1` | `5` | `10` | `18` | `40i` | at `γ₁ = 14.1347` (absolute) |
|---|---|---|---|---|---|---|
| 0.01 | 5.1e-6 | 1.4e-4 | 6.2e-4 | 5.1e-3 | 1.6e-3 | 9.6e-7 |
| 0.0025 | **2.8e-7** | **4.5e-6** | **2.0e-5** | **1.2e-3** | **3.1e-3** | **1.1e-7** |

- **Convergence.** The error falls with the grid step. Doubling `K` does not change it (`K = 60e^δ + 40`: `1.2e-5` at `z = 1` on the 0.01 grid), so it is set by how well the grid resolves `L`'s fine structure, not by the basis.
- **Coarse errors.** Starting instead at `δ = 0.02` with first-order data gives `2.4e-5·z²`. Using unsmoothed secant slopes gives `2.2e-5` at `z = 1`.

**The tabulated Hamiltonian.**
- `hamiltonian_table.json`: `a, ln K_a(0, 0), L, φ, q = φ′` at 616 windows, `a ∈ [0.24, 1.01]`.
- `hamiltonian.png`: the Dirac potential `q` against `4πe^{2a}`.
- Smooth part: `ln K_a(0, 0) ≈ 4πe^δ − 5.18δ − 15.65` (rms residual `0.10` on `δ ∈ [0.5, 2]`), so `q ≈ 4πe^{2a} − 5`.

**Two findings about the fine structure.**
- **The smooth model is not enough.** The closed-form `L = 2(4πe^δ − 5.18)` reproduces the chain to `4e-4` at `z = 1` and `6e-2` at `z = 10`. But it misses the zeta zeros: the kernel at `γ₁` comes out `1.4e-3` instead of `≈ 0` (the tabulated `L` gives `1e-7`). The positions of the zeros the chain dodges live in the fine structure of the potential.
- **The fine structure is not explained.** The potential has about 37 extrema on `a ∈ [0.25, 1]`: features at `a = ½ log n` for the prime powers `n = 2, 3, 4, 5, 7`, and more between them, growing denser with `a`.
  - A hypothesis that the extra features are zeta zeros crossing a horizon `c·e^{2a}` fits well: `c = 5.65`, mean distance `0.0018`.
  - But it fails a fair null test. Surrogate zero sequences with `c` optimised the same way fit equally well: median `0.00175`, and 53% of surrogates do at least as well. So it is not supported.

**Status.** We have the Hamiltonian as a computed object. It is exactly defined, tabulated on `a ∈ [0.24, 1.01]`, and shown to generate the chain's kernels to `3e-7` (at `z = 1`) to `3e-3` (at `z = 40i`). We do not have a closed form. Its existence for every `a` is equivalent to RH.

## Round 83: the Hamiltonian pushed to `a = 1.5`; its fine structure is real, and multi-scale (`kcompare.py`, `kcount.py`)

**1. The fine structure is not a numerical artefact.** The potential `q − 4πe^{2a}` was recomputed on `δ ∈ [1.5, 2.0]` (step 0.0025) with a different basis size (`K = 45e^δ + 40` instead of `30e^δ + 40`):
- the two residual curves correlate at `0.9997`, with rms difference `0.16` against a signal rms of `7.1`;
- all 18 extrema coincide (mean shift `0.0001` in `δ`).

**2. Extension and validation to `δ = 3` (`a = 1.5`).** `ln K_a(0, 0)` is now tabulated on `δ ∈ [0.46, 3.0]` at step `0.0025` (`hamiltonian_grid_to3.jsonl`, 1020 windows). Integrating the canonical system from `δ = 0.5` to `δ = 3` (`K_a(0, 0)` grows by `≈ e²⁰⁰`) reproduces the directly computed kernel at `δ = 3` to:

| `z = 1` | `5` | `10` | `18` | `30` | `40i` | `γ₁` (absolute) |
|---|---|---|---|---|---|---|
| 2.2e-6 | 5.8e-5 | 2.7e-4 | 2.0e-3 | 2.9e-4 | 7.1e-4 | 7.5e-8 |

`hamiltonian_table.json` and `hamiltonian.png` now cover `a ∈ [0.24, 1.49]`.

**3. No spacing law, but a growth law for the density of features.**
- **Counting against models.** Counting prominent maxima of `q − 4πe^δ` with a smoothing window `∝ e^{−δ}`, the count fits `A·e^δ` (rms 0.46–0.59) much better than the zero-count shapes `A·e^δ·δ` or `A·N_ζ(c·T₀)` (rms 1.0–1.5). So the features are not zeta-zero crossings, independently of round 82's null test.
- **At fixed resolution.** Per 0.25 in `δ`, with `hw = 0.008`, the counts are `2, 1, 2, 4, 5, 7, 10, 12, 12, 12`. They grow by about `×1.3 ≈ e^{1/4}` per bin until the grid's resolution caps them, and they keep rising as the resolution improves.
- **No clean coefficient.** `N ≈ πe^δ` appears at one smoothing choice, but `dN/d ln K_a(0, 0)` runs `0.35 → 0.25 → 0.19` as the smoothing factor goes `0.10 → 0.15 → 0.25`.
- **Amplitude.** The residual's rms is `≈ 6–11` in `q` units across the range, against `q ≈ 250` at `δ = 3`, so its relative size falls like `e^{−δ}`.

**Reading.** The Hamiltonian's potential is `q ≈ 4πe^{2a} − 5` plus a fine structure that is real, of roughly constant absolute amplitude, and multi-scale. The density of its features grows with the window at every resolution tested, with no regular spacing and no scale-free constant. It is not a zero-crossing pattern. Round 81 showed it is not a sum of independent prime-power pieces either. Together these rule out the natural closed forms. The Hamiltonian is tabulated and validated to `a = 1.5`. It has no closed form, and its existence for all `a` is equivalent to RH.

## Round 84: the fine structure is quasi-periodic in `x = e^{2a}` (`frontier/nullvec/kspectrum.py`)

**Question** (the owner's "a higher-dimensional shadow?"). A quasi-periodic function, meaning a sum of a few incommensurate frequencies, is the restriction of a periodic function on a torus to a line. Bohr's view of ζ and the Kurasov–Sarnak Fourier quasicrystals are of this kind. Does the Hamiltonian's fine structure have a discrete spectrum?

**Method.** Take the residual of `ln K_a(0, 0)` on `δ ∈ [0.5, 3]` after the smooth fit. The fitted leading coefficient is `12.5666 = 4π` to five digits, which confirms the reduced problem's exponent. Resample the residual uniformly in `x = e^δ = e^{2a}`, detrend it, apply a Hann window, and take its spectrum (`kspectrum_results.txt`).

**Findings.**
- **Discrete.** Over `x ∈ [1.65, 20.1]`, the eight main lines hold `0.48` of the power in their centre bins alone, and `≈ 0.9` including each line's ±2-bin Hann main lobe, against `≈ 0.03` for a flat spectrum. The ±2-bin sums double-count slightly where lines are within 4 bins: `kspectrum_results.txt` prints values up to `1.04`.
- **Stable in `x`.** The lines appear independently in both halves of the range, at the same positions within resolution:

| `x ∈ [1.65, 10]` (res 0.75) | 5.27 | 9.78 | 12.79 | 16.56 | 23.33 |
|---|---|---|---|---|---|
| `x ∈ [10, 20.1]` (res 0.62) | 4.99 | 9.37 | 13.11 | 16.86 | 23.72 |

  The dominant line, `ω ≈ 9.5`, carries 24–30%.
- **Not stable in `δ`.** The lines drift between halves, so the structure is not log-periodic. That argues against frequencies set by zeta zeros, which would enter as `e^{iγ·a}`.
- **Not prime powers on the integers.** Prime powers enter at `x = n`, so an arithmetic event train would give lines periodic in `ω` with period `2π`. They are not. The residual does not correlate with `Σ_{n≤x} Λ(n)/√n`: corr `−0.02`, best over lag `0.155`, inside the null band from random integer positions (95% point `0.20`).

**Reading.** In the variable `x = e^{2a} = T₀/(2π)`, the natural horizon scale, the fine structure of the chain's Hamiltonian is quasi-periodic with a handful of stable frequencies. That is the signature of a shadow of a low-dimensional torus flow. What remains open:
- The number of independent frequencies, i.e. the torus dimension, is undetermined at this resolution (`Δω ≈ 0.34` over `x ≤ 20`).
- The frequencies are unidentified: not prime-lattice, not zero-driven, and not harmonics of `π` within resolution.
- Sharper lines need larger windows (`x` up to `e⁴` would give `3×` resolution, at `K ≈ 1650`).

## Round 85: larger windows (to `a = 2`, `x = e^{2a} = 55`); the main line sits at `3π` (`kspectrum2.py`)

**Data.** 289 new windows at uniform step `0.12` in `x = e^δ ∈ [20, 54.6]`, i.e. `δ ∈ [3, 4]` (`hamiltonian_grid_x20_55.jsonl`). The basis is `K = 15x + 40` at `300 + 24x` bits: about 4 minutes per window at `x = 55`, where `ln K_a(0, 0) = 650.5`. `K = 15` was validated against `K = 30` on `δ ∈ [1.5, 2]`: the residual of `ln K_a(0, 0)` correlates at `0.9976`, with rms difference 7% of the signal. The joint smooth fit over `x ∈ [1.65, 54.6]` (with a step term at the `K`-factor junction `x = 20`) again gives the leading coefficient `12.565 ≈ 4π`.

**The spectrum in `x`** (`kspectrum2_results.txt`; resolution `0.119` over the combined range, `≈ 0.18–0.37` per segment):
- **The dominant line persists** in every segment, including the new ones, and does not drift. Its refined centre (zero-padded peak) is `9.436, 9.390, 9.472, 9.437` on `x ∈ [1.65, 12], [12, 25], [25, 40], [40, 54.6]`, and `9.417` combined. The mean over segments is `9.434 ± 0.017`, against `3π = 9.4248`.
- **The next strongest lines** are `5.246` (`5π/3 = 5.236`) and `16.741` (`16π/3 = 16.755`).
- **Weaker lines do not fit a `π/3` lattice**: `2.04, 4.30, 6.69, 13.19` sit at ratios `1.95, 4.10, 6.39, 12.59` to `π/3`.

**Caveats.**
- The `π/3` lattice was chosen after seeing the data, from a handful of natural candidates.
- The chance that three given lines fall within their observed deviations (0.008, 0.010, 0.014) of a lattice of spacing `1.047` is about `1e-5`. Choosing the lattice and the three lines afterwards costs perhaps two orders of magnitude, so this is suggestive, not established.
- No mechanism is known. An oscillation `cos(3πx)` in `ln K_a(0, 0)` is `cos(3T₀/2)` in the horizon `T₀ = 2πx`, or `cos(¾·4πx)` against the smooth part `4πx`.
- Rounds 82–84 exclude a zero-crossing origin (not log-periodic) and a prime-lattice origin (not `2π`-periodic in `ω`; no correlation with `Σ Λ(n)/√n`).

**Reading.** In the variable `x = e^{2a}`, the Hamiltonian's fine structure is quasi-periodic and stable out to `a = 2`, `x = 55`. Its dominant frequency is `3π` to `0.2%`. Its identity and the torus it would be a shadow of are open.

## Round 86: the cascade tower through the window chain, a pre-registered test (`PREREG_tower_layers.md`, `ztower*.py`)

**Primes-off control.** With the prime terms removed (Γ-archimedean part and pole only), the chain collapses: `ln K_a(0, 0) = 0.18` at `δ = 1.5`, against `≈ 29` with primes, and the 2×2 kernel matrix is indefinite. So the trend `4πe^δ` is not "the Gamma part". It is the balance between Γ and the primes.

**The dictionary.** The owner's paper, Theorem 1, defines the tower as `Γ_ℝ(d+1)` with `Ω(d) = |S^d|`. Its Theorem 1b evaluates the explicit formula at `z = d+½`. By the functional equation, `Ξ(i(d+½)) = ξ(d+1) = ½(d+1)d·Γ_ℝ(d+1)ζ(d+1)`, checked to 20 digits. So the chain's kernel at `z = i(d+½)` is, in the limit, the tower times `ζ(d+1)`. Round 77's multiplier gives each layer at a finite window, with a dimension horizon at `d* ≈ 4πe^δ`.

**Pre-registered prediction P1** (committed in `b53b470` before any computation):

`ln[K_a(i(d+½),0)/K_a(0,0)] = ln[ξ(d+1)/ξ(½)] + T₀[√(1+η²) − 1 − η·arsinh η]`,  `η = (d+½)/(2T₀)`.

It passes if `|ratio − 1| ≤ 3e^{−δ}` for `d = 0…60`.

**Result** (`tower_results/score.txt`, `K = 15e^δ + 40`):

| `δ` | tolerance | P1: max `\|ratio − 1\|` | verdict | Gaussian null |
|---|---|---|---|---|
| 2.0 | 0.41 | 9.9e-3 | PASS | 6.4e-3 (passes too) |
| 3.0 | 0.15 | 1.25e-3 | PASS | 9.0e-4 (passes too) |
| **4.3 (fresh)** | 0.041 | **9.0e-5** | **PASS** | 8.3e-5 (passes too) |

**Honest scoring.**
- P1 passes at every window, including the fresh one, with large margins. The registered tolerance was loose.
- The registered null did not fail. At layers `d ≤ 60`, the `ξ(d+1)` term dominates and the closed-form multiplier and the Gaussian differ by less than the residual. The pre-registration's statement that the null "must fail beyond `d ≈ √T₀`" was wrong for this range.
- So the test confirms the dictionary (the chain at the tower points is the tower times `ζ(d+1)`, up to the multiplier). It does not discriminate the multiplier's shape.

**The residual is fully accounted for.** It is `∝ −z²` with coefficient `−9.9e-5, −1.46e-5, −1.12e-6` at `δ = 2, 3, 4.3`. That matches the known `e^{−2δ}` correction of `τ` (rounds 70 and 80), `0.0058·e^{−2δ} = 1.06e-4, 1.44e-5, 1.07e-6`.

**Reading.** Each window of the Weil chain carries the cascade's ball tower `Γ_ℝ(d+1)ζ(d+1)` at the imaginary half-integers, to `≈ 1e-4` relative at `δ = 4.3`. The only deviation is the known finite-window correction. That is the precise sense in which "the Gamma and the arithmetic are one object" shows up in the chain. It is the explicit formula's identity seen through the window chain, not new physics. No prediction for the wiggle frequencies was registered, and none is claimed.

## Round 87: the tower up to the dimension horizon, a second pre-registered test (`PREREG_tower_horizon.md`, `ztower_score2.py`)

**The test.** It was registered in `1367192` before any computation. Round 86's test could not separate the closed-form multiplier from the Gaussian at `d ≤ 60`, so this one goes to the dimension horizon. The window is `δ = 3.5` (`T₀ = 208`, `2T₀ = 416`), with layers `d = 0, 25, …, 500` (`1.2 × 2T₀`). Two bases are used: `K = 536` (top frequency ≈ 968) and `K = 867` (≈ 1558).

**Result** (`tower_results/score_horizon.txt`). Every registered criterion passes:

| criterion | registered | measured | verdict |
|---|---|---|---|
| validity: the bases agree | `≤ 1e-3` | `≤ 2.3e-5` at every `d` | valid |
| (A) P1 holds | `\|m/P1 − 1\| ≤ 3e-3`, `d ≤ 500` | max `1.23e-3` (at `d = 500`) | **PASS** |
| (B) the Gaussian null fails | `\|m/N − 1\| > 3e-3`, `300 ≤ d ≤ 500` | `4.3e-3` (d = 300) rising to `1.74e-2` (d = 500) | **PASS** |
| (C) the residual is the known correction | `c` within ±30% of `5.29e-6` | `3.86e-6` (ratio `0.73`) | **PASS, narrowly** |

**The residual's shape**, recorded honestly. `(m − P1)/z²` is `−5.29e-6` at `d = 50`, equal to `0.0058·e^{−2δ}` to three digits. It then shrinks steadily: `−5.20e-6, −4.87e-6, −4.43e-6, −3.97e-6, −3.54e-6` at `d = 100, 200, 300, 400, 500`. So the finite-window correction is not a pure `Δτ·z²`. It has its own shape in `η = z/(2T₀)`, like a correction `T₀·Δ(η)` to the multiplier. Its small-`z` limit is the known `τ` correction. Criterion (C) passed only because of the ±30% band. Its shape is not derived.

**Reading.** Through the dimension horizon and 20% beyond it, the Weil window chain at `z = i(d+½)` carries the cascade tower `Γ_ℝ(d+1)ζ(d+1)`, shaped by the closed-form multiplier `exp{T₀[w·arcsin w + √(1−w²) − 1]}`. The agreement is `1.2e-3`, and the Gaussian is excluded beyond `d ≈ 300`. The ball-tower layers are seen through each window up to `d ≈ 4πe^δ`, with a suppression law now tested and distinguished from the naive one. As in round 86, this is the explicit formula seen through the chain, not a derivation of the cascade hypothesis. The wiggles remain unexplained.


## Round 88: the wiggles against the discrete zeros, a third pre-registered test (`PREREG_wiggles_balayage.md`, `kbalayage_model.py`)

**Pre-registered in `eb7bc7a` before any evaluation.** Prediction P3: the fine structure of `ln K_a(0,0)` is the discreteness structure of `−F(δ)`, where `F(δ) = min_T [4Σ_{γ<T} ln((1 + √(1 − γ²/T²))T/γ) − δT]` (Theorem 1bm(v); the first 6700 ζ zeros; no free parameter). The test uses the 1290 measured points, `x = e^δ ∈ [1.65, 54.6]`. **Evaluation.** Between consecutive zeros, `dF/dT` decreases from `+∞`. So `F` is concave on each gap and the minimum is attained exactly at a zero or at an end of `[1.2T₀, 2.8T₀]`; no grid search is needed. The minimiser sits at `T*/T₀ ∈ [1.30, 2.05]`. The null replaces the zeros by the density `(1/2π)ln(γ/2π)`.

**Result: P3 FAILS, as stated in advance.**
- **(i)** fails. The measured dominant line is `9.38` (power share 0.214), but the model's dominant line is `5.11` (0.152), well outside `9.42 ± 0.2`. The model has no line near 9.4; its nearest line is `8.67` (0.018).
- **(ii)** fails. The residual correlation is `0.277` at the grid points and `0.180` uniformly resampled in `x`, below `0.5`.
- **The null holds.** The continuum model's residual has `0.13%` of the discrete model's variance (a single smooth 0.36 line from detrending). So the model's structure is purely discreteness.
- `kbalayage_results.json` holds the numbers; `kbalayage_model_series.npz` holds the series.

**Reading.** The paper's discrete-balayage mechanism produces wiggles of the right *size* (rms `0.057` vs measured `0.071`). Its smooth part also has the right leading coefficient (`12.5676` vs `4π = 12.5664`). But its *spectrum is not the measured one*: the `3π` line of rounds 82–85 is not the zero-hopping of the balayage minimum. This agrees with rounds 82–84, which found the wiggles not tied to zero crossings. The origin of the `≈ 3π` line remains open.

**Post hoc, not registered, and not evidence.**
- The model's strongest line `5.11` lies near the measured second line `5.22` (0.071).
- The uniform-`x` correlation `0.18` sits at about the 97th percentile of a circular-shift null (sd 0.064, 95th percentile of `|c|` 0.115, max 0.204 over 186 shifts).
- Both are weak hints that part of the measured residual is zero-discreteness. Neither may be claimed without a new pre-registration.

## Round 89: topological depths in the wiggles, a fourth pre-registered test (`PREREG_topology.md`, `ktopology.py`)

**Registered in `8d8870e` before any statistic was computed.** The depth map is derived, not fitted: the multiplier's branch point `z = 2T₀ = 4πx` reaches cascade layer `D` (tower index `d = D − 1`, sphere `S^{D−1}`) at `x_D = (D − ½)/4π`. A feature recurring with period `P` in `D` gives a line at `8π²/P` in `x`. The accessible layers are `D ∈ [21, 687]`, so `d_V, d₀, d₁` and the Adams/Hopf dimensions are below range.

**Result: every test fails. Hypothesis T is not supported.**

| Test | Target | Power / flank 95th percentile | Flank rank | Verdict |
|---|---|---|---|---|
| H2: hairy ball / Lefschetz parity (P = 2), blind | 39.48 | 0.23 | 0.79 | fail |
| H3: Bott fermion layers `D ≡ 5 mod 8` (P = 8), not blind | 9.87 | 0.076 | 0.60 | fail, as expected |
| H4: Bott half-period (P = 4), not blind | 19.74 | 0.035 | 0.57 | fail |
| H1: threshold `d₂ = 217` at `x = 17.23`, blind | — | — | jump 0.42, rms 0.15 (needs 0.975) | fail |

**Positive control (post hoc).** The same line test at the known 9.38 gives power 14.6 times the flank 95th percentile, rank 1.0. So the method detects a real line of this data's size, and the topology lines are absent, not merely undetected. The strongest lines in `(26, 62)` on `[1.65, 20]` are 30.2 and 36.7, with none at 39.5.

**Reading.** Under the derived depth map, the wiggles carry no parity comb (hairy ball), no period-8 comb (Bott / fermion layers), no period-4 comb, and no event at `d₂ = 217`. Two readings remain, and this test cannot separate them:
- the wiggles of `ln K_a(0,0)` at `z = 0` do not see the layer structure;
- the horizon is not the depth probe for them. The multiplier's transition is smooth, with an arccosh deficit, not a sharp edge.

The recorded caveat stands: a period-8 comb gives exactly `3π` only if the slope is 12 instead of the derived 4π, and that slope is not available without a fit. The `3π` line's origin remains open after rounds 82–89.

## Round 90: digging the Bott, a fifth pre-registered test (`PREREG_bott.md`, `kbott.py`)

**Registered in `14cc729` before the data existed.** The depth slope `s` is left free, since round 89 excluded `4π`. Bott periodicity (period 8 on the integer layers) then predicts two things whatever `s` and whichever 8-periodic pattern:
- **B1:** harmonics at `3ω₁` or `4ω₁`, because a pattern on integer layers is not a pure sinusoid;
- **B2:** the lattice line at `8ω₁ = 2πs`.

**New data.** 426 new windows (`kchain_list.py`, same basis `K = 15x + 40`, reproducing existing points exactly), merged into a uniform step of 0.03 on `x ∈ [20, 37.04]`. This gives 569 points with Nyquist 104.7, where previously no line above 26 had been observed. The file is `hamiltonian_grid_x20_37_fine.jsonl`.

**Result: B1 and B2 both fail. Bott is not visible as a lattice pattern.**

The fundamental is `ω₁ = 9.586` (power 15.0 times its flank 95th percentile, the positive control). So the implied slope would be `s = 8ω₁/2π = 12.2`.

| `k` | `kω₁` | Power / flank q95 | Verdict |
|---|---|---|---|
| 2 (not blind) | 19.17 | 0.025 | — |
| **3** | 28.76 | 0.087 | fail |
| **4** | 38.34 | 0.80 | fail |
| 5, 6, 7 | 47.9, 57.5, 67.1 | 0.76, 0.31, 0.52 | — |
| **8 (lattice)** | 76.69 | 0.15 | fail |

The strongest line in `[50, 100]` is at 50.1, which is `5.23ω₁`, not an integer multiple.

**Quantitative bound.** Relative to the fundamental, the harmonic amplitudes are:
- `|c₃/c₁| < 0.061`;
- `|c₄/c₁| < 0.042`;
- `|c₈/c₁| < 0.0049`.

The 3π line is therefore sinusoidal to about 5% in amplitude. An equal-weight comb on integer layers (the fermion layers `D ≡ 5 mod 8`) would need each layer's feature smeared over a Gaussian width of at least `1.06` layers (from `k = 3`) to hide its harmonics.

**Reading.** Rounds 89–90 give two results:
- At the derived slope `4π`, there is no line at `π²`.
- At a free slope, the line that exists has no harmonics and no lattice line.

So the wiggles show no trace of the integer layer structure. Bott could still be present only if every layer's feature is spread over more than about one layer. In that case a period-8 pattern cannot be told apart from any other smooth oscillation of that frequency in this data, and the Bott reading is not testable here. The `≈ 3π` line (9.4–9.6 depending on range and detrending, resolution 0.37 here) is a clean single-frequency oscillation of unknown origin.

## Round 91: the one remaining route, geometric resonance, is closed; the 3π line is arithmetic (`PREREG_resonance.md`, `kzeroside.py`, `kresonance.py`)

**Two structural facts, found on the way.**
- **The prime side cannot be dissected.** At `x = 12` (`kchain_variant.py`), `ln K00` is `122.5` with the full prime side. It becomes:
  - `1.9` with every `Λ(n)` scaled by 0.9;
  - indefinite with the weights scaled by 1.1;
  - `0.09` with `n ≤ 5` dropped;
  - `100.4` with `n = 11` alone dropped.

  The `e^{4πx}` growth is an exact Γ–prime cancellation that exists only at prime weight 1.
- **The zero side is exact and robust.** By Weil's explicit formula (zeros on the line), `K_a(0,0) = sup ĝ(0)²/Σ_γ |ĝ(γ)|²`. `kzeroside.py` evaluates this in the cosine basis on the first 6700 zeros. It reproduces the prime-side chain up to a near-constant offset: `0.667` and `0.664` nats at `x = 5` and `8`, close to `ln 2` less the truncation. Its residual correlates with the measured one at **`0.985`**. Any point set gives a positive form, so the zeros can be replaced safely.

**The test (registered in `56f642c`).** Route R said the line is a geometric resonance between the window and the *mean* zero spacing. The test replaces the 6700 zeros by their fluctuation-free quantiles, `θ(γ̃_k) = (k − 3/2)π`, and recomputes on `x ∈ [3, 12]` (451 windows, step 0.02).

| | True zeros | Smooth quantiles | Measured (prime side) |
|---|---|---|---|
| Line at 9.075 (power / flank q95) | **5.07** | **0.074** | 5.12 |
| Residual rms | 0.074 | 0.010 | — |
| Top lines | 9.07, 4.89, 16.75, 13.26, 23.73 | none (a detrending remnant at 1.4) | 9.07, 4.89, 16.75, 13.26, 23.73 |

The quantile residual correlates with the true one at `0.08`.

**Result: V passes, R fails, A holds.**
- With the zeros at their mean positions, the chain has *no* wiggles: it keeps 14% of the rms, and that remnant has no structure.
- The whole fine structure, including the 3π line, its companions at 4.9 and 16.75, and their relative powers, is carried by the **fluctuations of the zeta zeros about their mean positions**.
- The line position is 9.075 here (resolution 0.70 on this range) against 9.4 on the larger ranges.

**Reading.** The route is closed, and the question now has a precise answer. The trend is Γ, and the wiggles are arithmetic: they are the zeros' deviations `S(t) = (1/π)arg ζ(½ + it)` read through the window's extremal problem. This fits every earlier negative:
- not the mean density (round 88's continuum null, and now Z1);
- not the individual zero crossings (rounds 82–83, 88);
- not the layer topology (rounds 89–90).

The zero side makes the next step possible, because it can be dissected where the prime side could not. Replacing the zeros by quantiles *in height bands* will localise which zeros carry the 3π line: those near the edge `2T₀ = 4πx`, or the low zeros.

## Round 92: the discretised d-ball has a consistent arithmetic only for d = 1, 2 (`PREREG_latticeball.md`, `klatticeball.py`)

**Registered in `052cdfb`.** The owner's claim was that "the arithmetic is forced by discretising the unit ball". It was made operational as follows:
- sum the Gaussian `e^{−π|t|²x}` over the integer lattice ℤ^d instead of integrating it over ℝ^d;
- take the Mellin transform, which gives the completed Epstein zeta `Λ_d(s) = π^{−s}Γ(s)Σ'_{m∈ℤ^d}|m|^{−2s}`.

The discretised d-ball has a window chain only if every zero of `Ξ_d = s(s − d/2)Λ_d` lies on `Re s = d/4`. `Λ_d` is computed from its theta integral, which matches the closed forms at `d = 1, 2, 4, 8` to `1e-31`–`1e-47`. The test compares zeros on the line (sign changes) with all zeros (argument principle) up to `T = 40`.

| `d` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| all zeros, `0 < Im < 40` | 21 | 20 | 20 | 20 | 20 | 21 | 21 | 21 |
| on `Re s = d/4` | 21 | 20 | 10 | 8 | 8 | 9 | 9 | 9 |
| off-line | 0 | 0 | **10** | **12** | **12** | **12** | **12** | **12** |
| consistent (chain exists) | yes | yes | no | no | no | no | no | no |

**Cross-checks.**
- `d = 1` is `ζ(2s)`: its line zeros are `γ/2` (7.07, 10.51, …), 21 of them.
- `d = 2` is `ζ(s)L(s, χ₋₄)`, the Gaussian integers: 6 ζ-zeros plus 14 `L`-zeros.
- `d = 4` is exact: 8 line zeros from `1 − 4^{1−s}` at `t = 2πk/ln 4 = 4.53k`, and 12 off-line zeros (6 ζ-zeros at `Re s = ½` and their mirrors at `3/2`).
- `d = 8` is exact: 9 line zeros from `1 − 2^{1−s} + 2^{4−2s}` (whose roots have `|2^{−s}| = ¼`, so they lie on the line) plus 12 off-line zeros.

**Result: H fails, as expected.** The literal lattice discretisation of the d-ball gives a consistent arithmetic, zeros all on the centre line, **only for d = 1 and d = 2**. It fails for every `d = 3, …, 8` computed. The two exact cases, `d = 4` and `d = 8`, fail because their Epstein zetas factor into ζ's *shifted off* the centre. `d = 3, 5, 6, 7`, which have no Euler product, fail with 10–12 off-line zeros below height 40.

**Reading.**
- **Supported.** In one dimension, discretising the Gaussian on a lattice through the origin forces ζ uniquely: every such lattice is `λℤ`, and `Λ_{λℤ} = λ^{−2s}Λ_1` has the same zeros. `d = 2` (ℤ[i]) gives `ζ·L(χ₋₄)`, which contains ζ. So "the arithmetic is the 1-D lattice sampling of the Gaussian, with Γ as its continuum" holds exactly (Riemann 1859). The measured chain is its window chain.
- **Not supported.** "The arithmetic is forced by discretising the *higher-dimensional* ball." From `d = 3` on, the ball's own lattice discretisation gives an arithmetic *without* a consistent window chain.
  - In the distinguished dimensions 4 and 8 (quaternions, octonions), it gives ζ back, but shifted off-centre.
  - The higher balls' lattices do not carry the chain. Only the lowest dimensions do.

## Round 93: the octonion ball and the shift (`ke8ball.py`)

**The question** (owner): could the octonions be responsible for the phase shift?

**The octonion lattice.** The integral octonions (Coxeter's octavians) form the `E₈` lattice. Its theta function is `½(θ₂⁸ + θ₃⁸ + θ₄⁸)`, which equals the weight-4 Eisenstein series. Its Epstein zeta is therefore *exactly*

`Σ'_{v∈E₈} |v|^{−2s} = 240·2^{−s} ζ(s) ζ(s − 3)`.

It contains nothing but Riemann's ζ, with no extra 2-adic factor as ℤ⁸ has. `ke8ball.py` is round 92's code with the `E₈` theta:
- it matches the closed form to `1e-32`–`1e-46`;
- up to `T = 30` it finds **6 zeros, none on the centre `Re s = 2`**. These are ζ's first three zeros (14.13, 21.02, 25.01), each appearing twice, at `Re s = ½` and at `Re s = 7/2`, i.e. at `2 ∓ 3/2`.

**What the shift is.** For a lattice whose theta is an Eisenstein series of weight `k = d/2`, the zeta is `ζ(s)ζ(s − k + 1)`. Its two copies of ζ's zeros sit at `k/2 ∓ (k − 1)/2`, a displacement of `(d/2 − 1)/2` from the centre. That is `½` for `d = 4` and `3/2` for `d = 8`. It is fixed by the modular weight, i.e. by the dimension. The octonions supply the lattice (`E₈`) whose zeta is *purely* ζ.

**Is it a shift seen in the chain? No, on three counts.**
- **Positivity.** A zero displaced by `β` from the centre contributes `ĥ(γ − iβ)`, weighted by `e^{βu}` across the window, i.e. an amplitude `x^{±β}`, not a phase. It also makes the zero-side form indefinite (round 91). The measured chain is positive out to `x = 55`, so it contains no displaced zeros.
- **The Hamiltonian–wiggle lead** (the figure from round 90) is derived: `2φ = ln K00 + ln(2 d ln K00/dδ)` adds the derivative, a quarter-cycle lead. No further cause is needed.
- **The `3/2` coincidence**, checked because the 3π line is `cos(3T₀/2)`: a real-part displacement of `3/2` changes the Γ-phase by a *constant*, `arg Γ(σ + 3/2 + it) − arg Γ(σ + it) → 3π/4`. It does not change the frequency. So it cannot make a line at `1.5·T₀`, and the match is numerical only.

**Reading.**
- The octonion 8-ball, discretised on its own lattice, carries *exactly* Riemann's zeros, twice, displaced by `±3/2` from its centre.
- Undoing that displacement (the factor `ζ(s)`) returns the ζ chain.
- So "the octonion ball contains the arithmetic, shifted" is a theorem, not a hypothesis.
- What the chain sees is the unshifted copy. The displacement itself does not appear in it.

## Round 94: the octonion superposition (`PREREG_superposition.md`, `ksuperpose_zeros.py`, `ksuperpose_score.py`)

**The idea** (owner), made exact and registered in `3c41236`. The chain's arithmetic is a *superposition* of the octonion ball's two displaced copies of Riemann's function, `G(t) = Ξ(t + 3i/2) + Ξ(t − 3i/2) = 2 Re ξ(2 + it)`.

**Theorem** (de Bruijn 1950). If `F` is real entire of order `< 2` with its zeros in `|Im z| ≤ Δ`, then `F(z+ib) + F(z−ib)` has only real zeros for `b ≥ Δ`. For `Ξ`, `Δ ≤ ½` unconditionally, so every zero of the octonionic superposition lies on the critical line, **unconditionally**.

**The zeros.** `ksuperpose_zeros.py` finds `G`'s zeros as the points where `arg ξ(2 + it) ≡ π/2 (mod π)`. `ζ(2 + it)` comes from its absolutely convergent series and matches mpmath to `1e-13`–`7e-11`.
- There are 6700 zeros up to `t = 6996.5`, against ζ's `6996.9`, and the phase is monotone.
- The first ones are 12.77, 19.39, 23.94, 28.70, … They are not Riemann's zeros.
- They sit a near-constant ≈ 3/8 of a spacing from ζ's smooth quantiles. This is the constant Γ-phase `3π/4` of round 93, halved by `Γ(s/2)`. On top of that there is a ripple from `arg ζ(2+it)`, i.e. prime weights `Λ(n)/n²`.

**Result: S fails as registered.**

| Measure | Superposed zeros | True zeros | Smooth quantiles (round 91) |
|---|---|---|---|
| Correlation with measured wiggles (needs ≥ 0.9) | **0.47** | 0.985 | ~0.08 |
| Residual rms | 0.022 (29%) | 0.074 | 0.010 |
| Dominant line | **9.77**, 41× threshold | 9.075 | none |
| Other lines | 16.75, 23.73, 4.89 (weak) | 4.89, 16.75, 13.26, 23.73 | — |

The registered line test at 9.075 technically finds power within `±res`. But it finds it at the bin edge (9.773, resolution 0.70), and the correlation criterion fails, so S fails.

**Post hoc, not evidence.** The superposition does far more than the smooth quantiles:
- its residual correlates with the true-zero wiggles at 0.54;
- it carries a strong single line one resolution bin above the measured one;
- it shares the 16.75 and 23.73 lines exactly.

Its only arithmetic is `arg ζ(2 + it)`, which is dominated by the smallest primes (weights `Λ(n)/n²`). This suggests that the *line positions* of the wiggle family are set by low primes, while the full wiggle, including its amplitude and the 4.89 line, needs the critical-line fluctuations. That is a hypothesis for a new registration, not a result.

## Round 95: the wiggles are the small primes (`PREREG_lowprimes.md`, `kprimezeros.py`, `kzeroside2.py`, `klowprimes_score.py`)

**Faster protocol.** `kzeroside2.py` keeps the zeros below `H = 1000` individually and replaces the zeros above by their smooth density, with `sin²(ta)` replaced by its mean. Together with a step of 0.04 (226 windows, Nyquist 78), a variant costs about 1/10 of round 91's. **Validation V: correlation `0.9999`** with round 91's full kernel on the true zeros.

**Construction** (registered in `5e9051c`). The zero sets solve `θ(t)/π + 1 + S_P(t) = k − ½`, where `S_P` is the Euler product truncated at the prime `P`. Their mean deviation from the true zeros (below 1000) falls from 0.306 (`P = 0`) through 0.222, 0.158, 0.121, 0.096, 0.077 and 0.060 to 0.041 (`P = 101`).

| `P` | 0 | **2** | 3 | 5 | **7** | 13 | 31 | 101 | 1009 |
|---|---|---|---|---|---|---|---|---|---|
| Correlation with true-zero wiggles | 0.08 | **0.45** | 0.69 | 0.71 | **0.90** | 0.92 | 0.96 | 0.95 | −0.09 |
| rms ratio | 0.14 | 0.83 | 0.93 | 1.13 | 1.10 | 1.29 | 1.14 | 1.20 | 3.88 |
| Line test at `ω₀ = 9.075` (power / q95) | 0.38 | **13.3** | 3.6 | 4.8 | 4.5 | 4.8 | 2.9 | 4.1 | 0.13 |
| Where the line peaks | — | 9.77 | 9.77 | 9.77 | 9.77 | **9.075** | 9.075 | 9.075 | — |

**Result: LP passes as registered.**
- (i): the line test passes for every `P` from 2 to 101.
- (ii): the correlation at `P = 3` is 0.69 ≥ 0.5.

**Honest qualifications.**
1. For `P ≤ 7` the line sits one resolution bin (0.70) above `ω₀`, at 9.77. It moves onto `ω₀` from `P = 13`. At this resolution the two are adjacent bins and cannot be separated.
2. `P = 1009` breaks down: the truncated Euler product does not converge on the critical line, and the zero set becomes misaligned (mean deviation 13.8). This is an expected artefact of the construction, not evidence against LP.

**Reading.**
- **The prime 2 alone** turns the featureless smooth-quantile chain into one with the dominant line at 13× the threshold and 83% of the true rms.
- **The primes up to 7** reproduce the true chain's wiggles at correlation 0.90.
- So the wiggle family is set by the smallest primes, overwhelmingly by `p = 2`, with 3, 5 and 7 shaping it. Larger primes refine it.

**Next.** The next step is a single-prime dictionary (only `p = 3`, only `p = 5`, …) to identify which line each prime creates. Deriving the frequencies from `ln p` needs the *reading height* of the window: `4π ln 2 = 8.71` with the edge at `2T₀`, against the measured 9.1–9.4. That derivation is open.

## Round 96: one prime at a time, one prime removed (`PREREG_primeablation.md`, `kprimezeros2.py`, `kablation_score.py`)

**Registered in `a34af8f`.** The zero sets come from `S_Q` over a prime set `Q`: only-`p` (`Q = {p}`), or minus-`p` (the primes up to 101 without `p`), for `p = 2, 3, 5, 7, 11, 13`. They use round 95's fast kernel and grid. The baseline is `P = 101`, with correlation `0.945`.

**Deviation, stated.** The zero scan starts at `t = 1`. For the minus-`p` sets it produced a pair of crossings near `t ≈ 1.1–1.5`, where the smooth count is below ½ and no zero can exist. Crossings with `t < 10` were therefore dropped from every set; round 95's sets had none there. Elsewhere "all crossings" was kept as registered. In only-11 this gives a triple crossing at 47.05/47.19/47.25, and in only-13 an extra pair at 13.95/14.85.

| `p` | 2 | 3 | 5 | 7 | 11 | 13 |
|---|---|---|---|---|---|---|
| minus-`p`: correlation (drop) | 0.931 (0.014) | 0.916 (**0.029**) | 0.942 (0.003) | 0.958 (**−0.013**) | 0.949 (−0.004) | 0.962 (−0.017) |
| minus-`p`: line at 9.075 (× q95) | **2.2** | 5.3 | 4.6 | 3.9 | 5.5 | 3.6 |
| only-`p`: correlation | 0.45 | 0.31 | 0.40 | 0.29 | −0.09* | −0.03* |
| only-`p`: strongest lines | **9.77**, 2.79, 4.89 | 3.49, **16.75**, 5.58 | 3.49, 6.28, 8.38 | 2.79, 5.58, 11.87 | 2.09* | 2.09* |
| only-`p`: line at 9.075 (× q95) | **13.3** | 0.29 | 0.34 | 0.52 | 0.03 | 0.02 |

\* Only-11 and only-13 are dominated by their close crossing pairs (rms 9× and 6× the true value). These are artefacts of the construction and are not interpreted.

**Result: D7 fails, F fails.**
- **D7.** The drop ranking is 3, 2, 5, 11, 7, 13. Removing 7 slightly *raises* the correlation (−0.013). No single prime is essential once the others are present: the largest drop is 0.029. The owner's reading that 7 is special is not supported. The Weil-weight maximum at `e² ≈ 7.39` does not show up either.
- **F.** The single-prime lines do not scale with `ln p`: predicted 15.5, 22.7 and 27.4 for 3, 5 and 7, against observed strongest lines of 3.49, 3.49 and 2.79.

**What the dictionary does show** (descriptive):
- **The main line (≈ 9.1–9.8) belongs to `p = 2`.** Only-2 carries it at 13×. Removing 2 is the only removal that weakens it, to 2.2×, after which the 4.89 line becomes the strongest.
- **The 16.75 line belongs to `p = 3`.** It is only-3's second line, at 12% of the power.
- The other single primes contribute low-frequency structure (2.8–8.4). The full pattern is the non-additive combination: correlation 0.45 for 2 alone, and 0.94–0.96 for the full set.
